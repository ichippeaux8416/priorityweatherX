#!/usr/bin/env python3
"""PriorityWeather / OneWeather automated NOAA/NWS -> X worker."""

from __future__ import annotations

import hashlib
import html
import io
import logging
import math
import os
import re
import signal
import sqlite3
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Any, Callable, Iterable, Optional

import requests
from bs4 import BeautifulSoup
from PIL import Image, ImageDraw, ImageFont, ImageOps
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# =============================================================================
# Configuration
# =============================================================================

BOT_NAME = os.getenv("BOT_NAME", "OneWeather").strip() or "OneWeather"
BUILD_ID = "2026-08-26-auth-wpc-v4-hsd"
CONTACT_EMAIL = os.getenv("CONTACT_EMAIL", "").strip()

X_CLIENT_ID = os.getenv("X_CLIENT_ID", "").strip()
X_CLIENT_SECRET = os.getenv("X_CLIENT_SECRET", "").strip()
X_ACCESS_TOKEN = os.getenv("X_ACCESS_TOKEN", "").strip()
X_REFRESH_TOKEN = os.getenv("X_REFRESH_TOKEN", "").strip()

DB_PATH = os.getenv("DB_PATH", "/var/data/oneweather.sqlite3").strip()
DRY_RUN = os.getenv("DRY_RUN", "false").lower() in {"1", "true", "yes", "on"}
INCLUDE_SOURCE_URLS = os.getenv("INCLUDE_SOURCE_URLS", "false").lower() in {"1", "true", "yes", "on"}
POST_TEXT_LIMIT = max(180, min(270, int(os.getenv("POST_TEXT_LIMIT", "265"))))

NWS_POLL_SECONDS = max(30, int(os.getenv("NWS_POLL_SECONDS", "30")))
SPC_POLL_SECONDS = max(30, int(os.getenv("SPC_POLL_SECONDS", "60")))
NHC_POLL_SECONDS = max(30, int(os.getenv("NHC_POLL_SECONDS", "60")))
NHC_FULL_SWEEP_SECONDS = max(300, int(os.getenv("NHC_FULL_SWEEP_SECONDS", "600")))
WPC_ERO_POLL_SECONDS = max(60, int(os.getenv("WPC_ERO_POLL_SECONDS", "120")))
WPC_WINTER_POLL_SECONDS = max(60, int(os.getenv("WPC_WINTER_POLL_SECONDS", "300")))

TORNADO_MAX_POST_AGE_MINUTES = max(5, int(os.getenv("TORNADO_MAX_POST_AGE_MINUTES", "30")))
WINTER_ALERT_MAX_POST_AGE_MINUTES = max(30, int(os.getenv("WINTER_ALERT_MAX_POST_AGE_MINUTES", "360")))
NWS_QUERY_BACKFILL_MAX_MINUTES = max(15, min(10080, int(os.getenv("NWS_QUERY_BACKFILL_MAX_MINUTES", "360"))))
WPC_HSD_MAX_AGE_HOURS = max(12, int(os.getenv("WPC_HSD_MAX_AGE_HOURS", "36")))

ENABLE_SPC_FIRE = os.getenv("ENABLE_SPC_FIRE", "true").lower() in {"1", "true", "yes", "on"}
ENABLE_NHC_DISCUSSIONS = os.getenv("ENABLE_NHC_DISCUSSIONS", "true").lower() in {"1", "true", "yes", "on"}
ENABLE_NHC_FORECAST_ADVISORIES = os.getenv("ENABLE_NHC_FORECAST_ADVISORIES", "false").lower() in {"1", "true", "yes", "on"}
ENABLE_WPC_DAY4_DAY5_ERO = os.getenv("ENABLE_WPC_DAY4_DAY5_ERO", "true").lower() in {"1", "true", "yes", "on"}
ENABLE_WPC_HEAVY_SNOW_DISCUSSION = os.getenv("ENABLE_WPC_HEAVY_SNOW_DISCUSSION", "true").lower() in {"1", "true", "yes", "on"}
ENABLE_WPC_WINTER_PACKAGES = os.getenv("ENABLE_WPC_WINTER_PACKAGES", "true").lower() in {"1", "true", "yes", "on"}
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

# X API
X_TOKEN_URL = "https://api.x.com/2/oauth2/token"
X_ME_URL = "https://api.x.com/2/users/me"
X_POST_URL = "https://api.x.com/2/tweets"
X_MEDIA_URL = "https://api.x.com/2/media/upload"

# NOAA / NWS / NCEP
NWS_ALERTS_URL = "https://api.weather.gov/alerts"
NWS_PRODUCTS_URL = "https://api.weather.gov/products"

SPC_FEEDS = {
    "spc_md": ("https://www.spc.noaa.gov/products/spcmdrss.xml", "md"),
    "spc_convective": ("https://www.spc.noaa.gov/products/spcacrss.xml", "convective"),
    "spc_watches": ("https://www.spc.noaa.gov/products/spcwwrss.xml", "watch"),
}
if ENABLE_SPC_FIRE:
    SPC_FEEDS["spc_fire"] = ("https://www.spc.noaa.gov/products/spcfwrss.xml", "fire")

NHC_TWO_FEEDS = {
    "nhc_two_atlantic": "https://www.nhc.noaa.gov/xml/TWOAT.xml",
    "nhc_two_epac": "https://www.nhc.noaa.gov/xml/TWOEP.xml",
    "nhc_two_cpac": "https://www.nhc.noaa.gov/xml/TWOCP.xml",
}
NHC_BASIN_INDEX_FEEDS = {
    "atlantic": "https://www.nhc.noaa.gov/index-at.xml",
    "epac": "https://www.nhc.noaa.gov/index-ep.xml",
    "cpac": "https://www.nhc.noaa.gov/index-cp.xml",
}
NHC_BASIN_CODES = {"atlantic": "AT", "epac": "EP", "cpac": "CP"}

RADAR_EXPORT_URL = (
    "https://mapservices.weather.noaa.gov/eventdriven/rest/services/"
    "radar/radar_base_reflectivity/MapServer/export"
)
REFERENCE_EXPORT_URL = (
    "https://mapservices.weather.noaa.gov/static/rest/services/"
    "nws_reference_maps/nws_reference_map/MapServer/export"
)
WPC_ERO_MAPSERVER = (
    "https://mapservices.weather.noaa.gov/vector/rest/services/"
    "hazards/wpc_precip_hazards/MapServer"
)
WPC_WINTER_MAPSERVER = (
    "https://mapservices.weather.noaa.gov/vector/rest/services/"
    "precip/wpc_prob_winter_precip/MapServer"
)

# QPFHSD = AWIPS identifier. In api.weather.gov, product type is HSD and location is WBC.
# We deliberately do NOT use /latest because that endpoint can return a server-side 500
# when there is no current seasonal product. The NWS TGFTP raw feed is an official fallback.
WPC_HSD_TYPE = "HSD"
WPC_HSD_LOCATION = "WBC"
WPC_HSD_RAW_URL = "https://tgftp.nws.noaa.gov/data/raw/fo/fous11.kwbc.qpf.hsd.txt"
WPC_HSD_PUBLIC_URL = "https://www.wpc.ncep.noaa.gov/discussions/qpfhsd.html"
WPC_ERO_PUBLIC_URL = "https://www.wpc.ncep.noaa.gov/qpf/excessive_rainfall_outlook_ero.php"
WPC_WINTER_PUBLIC_URL = "https://www.wpc.ncep.noaa.gov/wwd/winter_wx.shtml"

WINTER_ALERT_EVENTS = {
    "Winter Storm Warning", "Winter Storm Watch", "Winter Weather Advisory",
    "Blizzard Warning", "Blizzard Watch", "Ice Storm Warning",
    "Lake Effect Snow Warning", "Lake Effect Snow Watch", "Lake Effect Snow Advisory",
    "Snow Squall Warning", "Extreme Cold Warning", "Extreme Cold Watch",
    "Cold Weather Advisory", "Wind Chill Warning", "Wind Chill Watch",
    "Wind Chill Advisory", "Heavy Snow Warning", "Freezing Rain Advisory",
}

# =============================================================================
# Logging / lifecycle
# =============================================================================

logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)sZ %(levelname)s %(message)s",
    datefmt="%Y-%m-%dT%H:%M:%S",
)
logging.Formatter.converter = time.gmtime
log = logging.getLogger("oneweather")
STOP_REQUESTED = False


def _request_stop(signum: int, _frame: Any) -> None:
    global STOP_REQUESTED
    STOP_REQUESTED = True
    log.info("Received signal %s; stopping after current work", signum)


signal.signal(signal.SIGTERM, _request_stop)
signal.signal(signal.SIGINT, _request_stop)

# =============================================================================
# Helpers
# =============================================================================


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def iso_z(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8", errors="replace")).hexdigest()


def squish(value: Optional[str]) -> str:
    if not value:
        return ""
    return re.sub(r"\s+", " ", html.unescape(value)).strip()


def html_to_text(value: Optional[str], preserve_lines: bool = False) -> str:
    if not value:
        return ""
    soup = BeautifulSoup(value, "html.parser")
    text = soup.get_text("\n" if preserve_lines else " ", strip=True)
    if preserve_lines:
        lines = [re.sub(r"[ \t]+", " ", line).strip() for line in text.splitlines()]
        return "\n".join(line for line in lines if line)
    return squish(text)


def truncate(value: str, limit: int) -> str:
    value = squish(value)
    if len(value) <= limit:
        return value
    if limit <= 1:
        return "…"[:limit]
    cut = value[: limit - 1].rstrip()
    if " " in cut and len(cut.rsplit(" ", 1)[0]) >= int(limit * 0.72):
        cut = cut.rsplit(" ", 1)[0]
    return cut + "…"


def fit_post(parts: Iterable[str], url: str = "") -> str:
    clean = [p.strip() for p in parts if p and p.strip()]
    suffix = "\n\n" + url.strip() if INCLUDE_SOURCE_URLS and url else ""
    budget = POST_TEXT_LIMIT - len(suffix)
    if budget < 80:
        suffix = ""
        budget = POST_TEXT_LIMIT
    text = "\n".join(clean)
    return truncate(text, budget) + suffix if len(text) > budget else text + suffix


def parse_any_datetime(value: Optional[str]) -> Optional[datetime]:
    if not value:
        return None
    value = value.strip()
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        pass
    try:
        dt = parsedate_to_datetime(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        return None


def age_minutes(value: Optional[str]) -> Optional[float]:
    dt = parse_any_datetime(value)
    if not dt:
        return None
    return max(0.0, (utcnow() - dt).total_seconds() / 60.0)


def format_offset_time(value: Optional[str]) -> str:
    if not value:
        return ""
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except Exception:
        return ""
    offset = dt.utcoffset() or timedelta(0)
    total = int(offset.total_seconds() // 60)
    sign = "+" if total >= 0 else "−"
    hh, mm = divmod(abs(total), 60)
    hour = dt.strftime("%I").lstrip("0") or "0"
    return f"{hour}:{dt.strftime('%M %p')} UTC{sign}{hh:02d}:{mm:02d}"


def first_parameter(parameters: dict[str, Any], *names: str) -> str:
    lowered = {str(k).lower(): v for k, v in (parameters or {}).items()}
    for name in names:
        value = lowered.get(name.lower())
        if isinstance(value, list) and value:
            return squish(str(value[0]))
        if value is not None:
            return squish(str(value))
    return ""


def all_parameter_values(parameters: dict[str, Any], name: str) -> list[str]:
    for key, value in (parameters or {}).items():
        if str(key).lower() == name.lower():
            if isinstance(value, list):
                return [str(v) for v in value]
            return [str(value)] if value is not None else []
    return []


def validate_environment() -> None:
    missing = []
    if not CONTACT_EMAIL:
        missing.append("CONTACT_EMAIL")
    if not DRY_RUN:
        for name, value in (
            ("X_CLIENT_ID", X_CLIENT_ID),
            ("X_CLIENT_SECRET", X_CLIENT_SECRET),
            ("X_ACCESS_TOKEN", X_ACCESS_TOKEN),
            ("X_REFRESH_TOKEN", X_REFRESH_TOKEN),
        ):
            if not value:
                missing.append(name)
    if missing:
        raise SystemExit("Missing required environment variables: " + ", ".join(missing))
    parent = Path(DB_PATH).expanduser().resolve().parent
    try:
        parent.mkdir(parents=True, exist_ok=True)
    except Exception as exc:
        raise SystemExit(f"Cannot create DB directory {parent}: {exc}") from exc


# =============================================================================
# HTTP client
# =============================================================================


def build_http_session() -> requests.Session:
    session = requests.Session()
    session.headers.update({
        "User-Agent": f"{BOT_NAME}/1.0 ({CONTACT_EMAIL})",
        "Accept-Encoding": "gzip, deflate",
    })
    retry = Retry(
        total=3,
        connect=3,
        read=3,
        status=3,
        backoff_factor=0.8,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset({"GET", "HEAD"}),
        respect_retry_after_header=True,
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=10, pool_maxsize=20)
    session.mount("https://", adapter)
    return session


HTTP = build_http_session()


def http_get(
    url: str,
    *,
    params: Optional[dict[str, Any]] = None,
    headers: Optional[dict[str, str]] = None,
    timeout: tuple[int, int] = (8, 30),
) -> requests.Response:
    response = HTTP.get(url, params=params, headers=headers, timeout=timeout)
    response.raise_for_status()
    return response


# =============================================================================
# SQLite state
# =============================================================================


class StateDB:
    def __init__(self, path: str):
        self.conn = sqlite3.connect(path, timeout=30, isolation_level=None)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA synchronous=FULL")
        self.conn.execute("PRAGMA busy_timeout=30000")
        self.conn.executescript("""
            CREATE TABLE IF NOT EXISTS items (
                source TEXT NOT NULL,
                item_key TEXT NOT NULL,
                first_seen_utc TEXT NOT NULL,
                status TEXT NOT NULL,
                tweet_id TEXT,
                last_error TEXT,
                updated_utc TEXT NOT NULL,
                PRIMARY KEY (source, item_key)
            );
            CREATE TABLE IF NOT EXISTS meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
        """)

    def close(self) -> None:
        self.conn.close()

    def get_meta(self, key: str, default: str = "") -> str:
        row = self.conn.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def set_meta(self, key: str, value: str) -> None:
        self.conn.execute(
            "INSERT INTO meta(key,value) VALUES(?,?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )

    def source_primed(self, source: str) -> bool:
        return self.get_meta(f"primed:{source}") == "1"

    def mark_source_primed(self, source: str) -> None:
        self.set_meta(f"primed:{source}", "1")

    def exists(self, source: str, item_key: str) -> bool:
        return bool(self.conn.execute(
            "SELECT 1 FROM items WHERE source=? AND item_key=?", (source, item_key)
        ).fetchone())

    def mark_seen_without_post(self, source: str, item_key: str, status: str = "primed") -> None:
        now = iso_z(utcnow())
        self.conn.execute(
            "INSERT OR IGNORE INTO items(source,item_key,first_seen_utc,status,updated_utc) VALUES(?,?,?,?,?)",
            (source, item_key, now, status, now),
        )

    def claim(self, source: str, item_key: str) -> bool:
        now = iso_z(utcnow())
        try:
            self.conn.execute(
                "INSERT INTO items(source,item_key,first_seen_utc,status,updated_utc) VALUES(?,?,?,?,?)",
                (source, item_key, now, "posting", now),
            )
            return True
        except sqlite3.IntegrityError:
            return False

    def set_status(self, source: str, item_key: str, status: str, *, tweet_id: str = "", error: str = "") -> None:
        self.conn.execute(
            "UPDATE items SET status=?,tweet_id=?,last_error=?,updated_utc=? WHERE source=? AND item_key=?",
            (status, tweet_id or None, error or None, iso_z(utcnow()), source, item_key),
        )

    def delete_item(self, source: str, item_key: str) -> None:
        self.conn.execute("DELETE FROM items WHERE source=? AND item_key=?", (source, item_key))

    def count_by_status(self) -> dict[str, int]:
        rows = self.conn.execute("SELECT status,COUNT(*) FROM items GROUP BY status").fetchall()
        return {str(k): int(v) for k, v in rows}


# =============================================================================
# X OAuth2 / posting
# =============================================================================


class XError(RuntimeError):
    pass


class XRejectedError(XError):
    pass


class XRetryableError(XError):
    pass


class XAmbiguousError(XError):
    pass


class XOAuth2:
    def __init__(self, db: StateDB):
        self.db = db
        self.client_id = X_CLIENT_ID
        self.client_secret = X_CLIENT_SECRET
        self.env_access_token = X_ACCESS_TOKEN
        self.env_refresh_token = X_REFRESH_TOKEN
        self.db_access_token = db.get_meta("x:access_token")
        self.db_refresh_token = db.get_meta("x:refresh_token")
        self.access_token = self.env_access_token or self.db_access_token
        self.refresh_token_value = self.db_refresh_token or self.env_refresh_token
        self.expires_at = 0.0

    def _token_auth(self) -> Optional[tuple[str, str]]:
        return (self.client_id, self.client_secret) if self.client_secret else None

    def _store_tokens(self, payload: dict[str, Any]) -> None:
        access = str(payload.get("access_token") or "").strip()
        refresh = str(payload.get("refresh_token") or "").strip()
        if not access:
            raise XRejectedError(f"X token response had no access_token: {payload!r}")

        self.access_token = access
        self.db_access_token = access
        self.db.set_meta("x:access_token", access)

        if refresh:
            self.refresh_token_value = refresh
            self.db_refresh_token = refresh
            self.db.set_meta("x:refresh_token", refresh)

        try:
            self.expires_at = time.time() + max(60, int(payload.get("expires_in"))) - 60
        except Exception:
            self.expires_at = 0.0

    def refresh(self) -> None:
        candidates: list[str] = []

        for token in (
            self.db_refresh_token,
            self.refresh_token_value,
            self.env_refresh_token,
        ):
            token = (token or "").strip()
            if token and token not in candidates:
                candidates.append(token)

        if not candidates:
            raise XRejectedError("No X OAuth2 refresh token is available")

        auth = self._token_auth()
        last_rejection = ""

        for refresh in candidates:
            data = {
                "grant_type": "refresh_token",
                "refresh_token": refresh,
            }

            if not auth:
                data["client_id"] = self.client_id

            try:
                response = requests.post(
                    X_TOKEN_URL,
                    data=data,
                    auth=auth,
                    headers={"Content-Type": "application/x-www-form-urlencoded"},
                    timeout=(8, 30),
                )
            except requests.RequestException as exc:
                raise XRetryableError(f"X token refresh network failure: {exc}") from exc

            if 200 <= response.status_code < 300:
                self._store_tokens(response.json())
                return

            if response.status_code == 429 or 500 <= response.status_code < 600:
                raise XRetryableError(
                    f"X token refresh temporary failure HTTP "
                    f"{response.status_code}: {response.text[:500]}"
                )

            last_rejection = (
                f"HTTP {response.status_code}: {response.text[:500]}"
            )

        raise XRejectedError(
            f"All available X refresh tokens were rejected; "
            f"last response {last_rejection}"
        )

    def bearer(self, *, force_refresh: bool = False) -> str:
        if (
            force_refresh
            or not self.access_token
            or (
                self.expires_at
                and time.time() >= self.expires_at
            )
        ):
            self.refresh()

        return self.access_token

    def request(
        self,
        method: str,
        url: str,
        *,
        retry_auth: bool = True,
        ambiguous_if_sent: bool = False,
        **kwargs: Any,
    ) -> requests.Response:
        token = self.bearer()

        caller_headers = dict(kwargs.pop("headers", {}) or {})
        headers = dict(caller_headers)
        headers["Authorization"] = f"Bearer {token}"
        headers.setdefault("User-Agent", f"{BOT_NAME}/1.0")

        try:
            response = requests.request(
                method,
                url,
                headers=headers,
                timeout=kwargs.pop("timeout", (8, 45)),
                **kwargs,
            )
        except requests.RequestException as exc:
            if ambiguous_if_sent:
                raise XAmbiguousError(
                    f"X create-post network failure: {exc}"
                ) from exc

            raise XRetryableError(
                f"X API network failure: {exc}"
            ) from exc

        if response.status_code == 401 and retry_auth:
            self.refresh()

            return self.request(
                method,
                url,
                retry_auth=False,
                ambiguous_if_sent=ambiguous_if_sent,
                headers=caller_headers,
                **kwargs,
            )

        return response


class XPublisher:
    def __init__(self, db: StateDB):
        self.dry_run = DRY_RUN
        self.oauth = None if self.dry_run else XOAuth2(db)

    @staticmethod
    def _raise_prepost(
        response: requests.Response,
        operation: str,
    ) -> None:
        if 200 <= response.status_code < 300:
            return

        msg = (
            f"{operation} HTTP {response.status_code}: "
            f"{response.text[:500]}"
        )

        if response.status_code == 429 or 500 <= response.status_code < 600:
            raise XRetryableError(msg)

        raise XRejectedError(msg)

    def upload_image(self, path: str) -> str:
        if self.dry_run:
            return "dry-run-media"

        assert self.oauth is not None

        media_type = (
            "image/png"
            if Path(path).suffix.lower() == ".png"
            else "image/jpeg"
        )

        size = os.path.getsize(path)

        if size <= 0 or size > 5 * 1024 * 1024:
            raise XRejectedError(
                f"Invalid X image size: {size} bytes"
            )

        with open(path, "rb") as fh:
            response = self.oauth.request(
                "POST",
                X_MEDIA_URL,
                data={"media_category": "tweet_image"},
                files={
                    "media": (
                        Path(path).name,
                        fh,
                        media_type,
                    )
                },
            )

        self._raise_prepost(
            response,
            "X media upload",
        )

        data = response.json().get("data") or {}
        media_id = str(data.get("id") or "")

        if not media_id:
            raise XRetryableError(
                f"X media upload returned no id: "
                f"{response.text[:300]}"
            )

        processing = data.get("processing_info") or {}
        checks = 0

        while (
            processing
            and processing.get("state") not in {"succeeded", "failed"}
            and checks < 20
        ):
            time.sleep(
                max(
                    1,
                    min(
                        10,
                        int(
                            processing.get("check_after_secs")
                            or 1
                        ),
                    ),
                )
            )

            status = self.oauth.request(
                "GET",
                X_MEDIA_URL,
                params={
                    "command": "STATUS",
                    "media_id": media_id,
                },
            )

            self._raise_prepost(
                status,
                "X media STATUS",
            )

            processing = (
                (status.json().get("data") or {})
                .get("processing_info")
                or {}
            )

            checks += 1

        if processing.get("state") == "failed":
            raise XRejectedError(
                f"X media processing failed: {processing!r}"
            )

        if processing and processing.get("state") != "succeeded":
            raise XRetryableError(
                f"X media processing did not finish: {processing!r}"
            )

        return media_id

    def create_post(
        self,
        text: str,
        image_path: str = "",
    ) -> str:
        text = truncate(
            text.strip(),
            POST_TEXT_LIMIT,
        )

        if self.dry_run:
            log.info(
                "[DRY RUN POST]\n%s%s",
                text,
                (
                    f"\n[image={image_path}]"
                    if image_path
                    else ""
                ),
            )
            return "dry-run-post"

        assert self.oauth is not None

        payload: dict[str, Any] = {
            "text": text
        }

        if image_path:
            payload["media"] = {
                "media_ids": [
                    self.upload_image(image_path)
                ]
            }

        response = self.oauth.request(
            "POST",
            X_POST_URL,
            json=payload,
            headers={
                "Content-Type": "application/json"
            },
            ambiguous_if_sent=True,
        )

        if response.status_code == 429:
            raise XRetryableError(
                f"X create-post rate limited: "
                f"{response.text[:500]}"
            )

        if 500 <= response.status_code < 600:
            raise XAmbiguousError(
                f"X create-post server error HTTP "
                f"{response.status_code}; outcome unknown: "
                f"{response.text[:500]}"
            )

        if not 200 <= response.status_code < 300:
            raise XRejectedError(
                f"X create-post rejected HTTP "
                f"{response.status_code}: "
                f"{response.text[:500]}"
            )

        tweet_id = str(
            (response.json().get("data") or {}).get("id")
            or ""
        )

        if not tweet_id:
            raise XAmbiguousError(
                f"X returned success but no post id: "
                f"{response.text[:500]}"
            )

        return tweet_id

    def verify(self) -> str:
        if self.dry_run:
            return "dry-run"

        assert self.oauth is not None

        response = self.oauth.request(
            "GET",
            X_ME_URL,
        )

        if not 200 <= response.status_code < 300:
            raise XRejectedError(
                f"X authenticated-user lookup failed HTTP "
                f"{response.status_code}: "
                f"{response.text[:500]}"
            )

        data = response.json().get("data") or {}

        if (
            self.oauth.access_token
            == self.oauth.env_access_token
            and self.oauth.env_access_token
        ):
            self.oauth.db.set_meta(
                "x:access_token",
                self.oauth.env_access_token,
            )

            if self.oauth.env_refresh_token:
                self.oauth.db.set_meta(
                    "x:refresh_token",
                    self.oauth.env_refresh_token,
                )

                self.oauth.db_refresh_token = (
                    self.oauth.env_refresh_token
                )

                self.oauth.refresh_token_value = (
                    self.oauth.env_refresh_token
                )

        return str(
            data.get("username")
            or data.get("name")
            or data.get("id")
            or "unknown"
        )


def publish_once(
    db: StateDB,
    x: XPublisher,
    source: str,
    item_key: str,
    text: str,
    image_path: str = "",
) -> bool:
    if not db.claim(
        source,
        item_key,
    ):
        return False

    try:
        tweet_id = x.create_post(
            text,
            image_path=image_path,
        )

        db.set_status(
            source,
            item_key,
            "posted",
            tweet_id=tweet_id,
        )

        log.info(
            "Posted %s %s -> X id %s",
            source,
            item_key[:16],
            tweet_id,
        )

        return True

    except XRetryableError as exc:
        db.delete_item(
            source,
            item_key,
        )

        log.warning(
            "Retryable X failure for %s %s: %s",
            source,
            item_key[:16],
            exc,
        )

    except XRejectedError as exc:
        db.set_status(
            source,
            item_key,
            "rejected",
            error=repr(exc),
        )

        log.error(
            "X rejected %s %s: %s",
            source,
            item_key[:16],
            exc,
        )

    except XAmbiguousError as exc:
        db.set_status(
            source,
            item_key,
            "ambiguous",
            error=repr(exc),
        )

        log.error(
            "Ambiguous X result for %s %s; "
            "will not auto-retry: %s",
            source,
            item_key[:16],
            exc,
        )

    except Exception as exc:
        db.set_status(
            source,
            item_key,
            "ambiguous",
            error=repr(exc),
        )

        log.exception(
            "Unexpected X publish failure for %s %s",
            source,
            item_key[:16],
        )

    return False


# =============================================================================
# RSS / SPC / NHC
# =============================================================================


@dataclass(frozen=True)
class RSSItem:
    title: str
    link: str
    guid: str
    pub_date: str
    description_html: str

    @property
    def text(self) -> str:
        return html_to_text(
            self.description_html
        )

    @property
    def multiline_text(self) -> str:
        return html_to_text(
            self.description_html,
            preserve_lines=True,
        )

    @property
    def key(self) -> str:
        return sha256_text(
            "\x1f".join(
                [
                    self.guid,
                    self.pub_date,
                    self.title,
                    self.link,
                    self.description_html,
                ]
            )
        )

    @property
    def published(self) -> Optional[datetime]:
        return parse_any_datetime(
            self.pub_date
        )


def _child_text(
    node: ET.Element,
    local_name: str,
) -> str:
    for child in list(node):
        if (
            child.tag
            .rsplit("}", 1)[-1]
            .lower()
            == local_name.lower()
        ):
            return "".join(
                child.itertext()
            ).strip()

    return ""


def fetch_rss(
    url: str,
) -> list[RSSItem]:
    response = http_get(
        url,
        headers={
            "Accept":
                "application/rss+xml,"
                "application/xml,"
                "text/xml,*/*"
        },
    )

    root = ET.fromstring(
        response.content
    )

    items: list[RSSItem] = []

    for node in root.iter():
        if (
            node.tag
            .rsplit("}", 1)[-1]
            .lower()
            != "item"
        ):
            continue

        items.append(
            RSSItem(
                title=squish(
                    _child_text(
                        node,
                        "title",
                    )
                ),
                link=_child_text(
                    node,
                    "link",
                ).strip(),
                guid=_child_text(
                    node,
                    "guid",
                ).strip(),
                pub_date=_child_text(
                    node,
                    "pubDate",
                ).strip(),
                description_html=_child_text(
                    node,
                    "description",
                ),
            )
        )

    items.sort(
        key=lambda item:
            item.published
            or datetime(
                1970,
                1,
                1,
                tzinfo=timezone.utc,
            )
    )

    return items


def process_rss_source(
    db: StateDB,
    x: XPublisher,
    *,
    source: str,
    url: str,
    formatter: Callable[
        [RSSItem],
        Optional[str],
    ],
    item_filter: Optional[
        Callable[
            [RSSItem],
            bool,
        ]
    ] = None,
) -> None:
    accepted = [
        item
        for item in fetch_rss(url)
        if (
            item_filter is None
            or item_filter(item)
        )
    ]

    if not db.source_primed(source):
        for item in accepted:
            db.mark_seen_without_post(
                source,
                item.key,
            )

        db.mark_source_primed(
            source
        )

        log.info(
            "Primed %s with %d existing RSS item(s)",
            source,
            len(accepted),
        )

        return

    for item in accepted:
        if db.exists(
            source,
            item.key,
        ):
            continue

        text = formatter(item)

        if not text:
            db.mark_seen_without_post(
                source,
                item.key,
                status="ignored",
            )
            continue

        publish_once(
            db,
            x,
            source,
            item.key,
            text,
        )


def first_useful_summary(
    item: RSSItem,
    max_len: int = 150,
) -> str:
    summary = item.text

    if (
        item.title
        and summary.lower().startswith(
            item.title.lower()
        )
    ):
        summary = summary[
            len(item.title):
        ].lstrip(" :-–—")

    return truncate(
        summary,
        max_len,
    )


def spc_item_is_real(
    item: RSSItem,
    kind: str,
) -> bool:
    combined = (
        f"{item.title} "
        f"{item.text}"
    ).lower()

    if any(
        marker in combined
        for marker in (
            "no mesoscale discussions",
            "no watches are",
            "no watches in effect",
            "no severe thunderstorm watches",
            "no tornado watches",
            "no fire weather",
        )
    ):
        return False

    if kind == "watch":
        return (
            "status report" not in combined
            and "watch" in combined
            and (
                "tornado" in combined
                or "severe thunderstorm" in combined
            )
        )

    if kind == "md":
        return (
            "mesoscale discussion"
            in combined
        )

    if kind == "convective":
        return "outlook" in combined

    if kind == "fire":
        return (
            "fire" in combined
            and "outlook" in combined
        )

    return True


def format_spc(
    item: RSSItem,
    kind: str,
) -> str:
    if kind == "md":
        heading = (
            "⚡ SPC MESOSCALE DISCUSSION"
        )

    elif kind == "convective":
        heading = (
            "⛈️ SPC CONVECTIVE OUTLOOK"
        )

    elif kind == "fire":
        heading = (
            "🔥 SPC FIRE WEATHER OUTLOOK"
        )

    else:
        heading = (
            "🌪️ SPC TORNADO WATCH"
            if "tornado"
            in f"{item.title} {item.text}".lower()
            else
            "⚠️ SPC SEVERE THUNDERSTORM WATCH"
        )

    return fit_post(
        [
            heading,
            item.title,
            first_useful_summary(
                item,
                155,
            ),
            "Source: NOAA/NWS SPC",
        ],
        item.link,
    )


def poll_spc(
    db: StateDB,
    x: XPublisher,
) -> None:
    for source, (url, kind) in SPC_FEEDS.items():
        try:
            process_rss_source(
                db,
                x,
                source=source,
                url=url,
                item_filter=lambda item, k=kind:
                    spc_item_is_real(
                        item,
                        k,
                    ),
                formatter=lambda item, k=kind:
                    format_spc(
                        item,
                        k,
                    ),
            )
        except Exception:
            log.exception(
                "SPC source failed: %s",
                source,
            )


def build_nhc_basin_sources(
    basin: str,
) -> list[
    tuple[
        str,
        str,
        str,
    ]
]:
    code = NHC_BASIN_CODES[
        basin
    ]

    out: list[
        tuple[
            str,
            str,
            str,
        ]
    ] = []

    for wallet in range(
        1,
        6,
    ):
        out.append(
            (
                f"nhc_tcp_{basin}_{wallet}",
                f"https://www.nhc.noaa.gov/xml/"
                f"TCP{code}{wallet}.xml",
                "tcp",
            )
        )

        out.append(
            (
                f"nhc_tcu_{basin}_{wallet}",
                f"https://www.nhc.noaa.gov/xml/"
                f"TCU{code}{wallet}.xml",
                "tcu",
            )
        )

        if ENABLE_NHC_DISCUSSIONS:
            out.append(
                (
                    f"nhc_tcd_{basin}_{wallet}",
                    f"https://www.nhc.noaa.gov/xml/"
                    f"TCD{code}{wallet}.xml",
                    "tcd",
                )
            )

        if ENABLE_NHC_FORECAST_ADVISORIES:
            out.append(
                (
                    f"nhc_tcm_{basin}_{wallet}",
                    f"https://www.nhc.noaa.gov/xml/"
                    f"TCM{code}{wallet}.xml",
                    "tcm",
                )
            )

    return out


NHC_BASIN_SOURCES = {
    basin:
        build_nhc_basin_sources(
            basin
        )
    for basin in NHC_BASIN_CODES
}


def nhc_item_is_real(
    item: RSSItem,
) -> bool:
    combined = (
        f"{item.title} "
        f"{item.text}"
    ).lower()

    if (
        "tropical weather outlook"
        in combined
    ):
        return True

    return not any(
        marker in combined
        for marker in (
            "no tropical cyclones",
            "there are no tropical cyclones",
            "no active tropical cyclones",
            "no tropical cyclone updates",
        )
    )


def _find_nhc_field(
    text: str,
    field: str,
) -> str:
    match = re.search(
        rf"(?im)^\s*"
        rf"{re.escape(field)}"
        rf"\s*\.{{2,}}\s*"
        rf"(.+?)\s*$",
        text,
    )

    return (
        squish(
            match.group(1)
        )
        if match
        else ""
    )


def format_nhc(
    item: RSSItem,
    kind: str,
) -> str:
    if kind == "two":
        return fit_post(
            [
                "🌀 NHC TROPICAL WEATHER OUTLOOK",
                item.title,
                first_useful_summary(
                    item,
                    155,
                ),
                "Source: NOAA/NHC",
            ],
            item.link,
        )

    if kind == "tcp":
        raw = item.multiline_text

        details = " | ".join(
            value
            for value in (
                _find_nhc_field(
                    raw,
                    "MAXIMUM SUSTAINED WINDS",
                ),
                _find_nhc_field(
                    raw,
                    "PRESENT MOVEMENT",
                ),
                _find_nhc_field(
                    raw,
                    "MINIMUM CENTRAL PRESSURE",
                ),
            )
            if value
        ) or first_useful_summary(
            item,
            135,
        )

        return fit_post(
            [
                "🌀 NHC PUBLIC ADVISORY",
                item.title,
                _find_nhc_field(
                    raw,
                    "LOCATION",
                ),
                details,
                "Source: NOAA/NHC",
            ],
            item.link,
        )

    heading = {
        "tcu":
            "🚨 NHC TROPICAL CYCLONE UPDATE",
        "tcd":
            "🌀 NHC FORECAST DISCUSSION",
        "tcm":
            "🌀 NHC FORECAST ADVISORY",
    }.get(
        kind,
        "🌀 NHC TROPICAL UPDATE",
    )

    return fit_post(
        [
            heading,
            item.title,
            first_useful_summary(
                item,
                145,
            ),
            "Source: NOAA/NHC",
        ],
        item.link,
    )


def _poll_nhc_product_source(
    db: StateDB,
    x: XPublisher,
    source: str,
    url: str,
    kind: str,
) -> None:
    try:
        process_rss_source(
            db,
            x,
            source=source,
            url=url,
            item_filter=nhc_item_is_real,
            formatter=lambda item, k=kind:
                format_nhc(
                    item,
                    k,
                ),
        )

    except requests.HTTPError as exc:
        if getattr(
            exc.response,
            "status_code",
            None,
        ) in {
            404,
            410,
        }:
            if not db.source_primed(source):
                db.mark_source_primed(
                    source
                )
            return

        raise


def _nhc_index_fingerprint(
    url: str,
) -> str:
    return hashlib.sha256(
        http_get(
            url,
            headers={
                "Accept":
                    "application/xml,"
                    "text/xml,*/*"
            },
        ).content
    ).hexdigest()


def _nhc_sweep_basin(
    db: StateDB,
    x: XPublisher,
    basin: str,
) -> bool:
    ok = True

    for (
        source,
        url,
        kind,
    ) in NHC_BASIN_SOURCES[
        basin
    ]:
        try:
            _poll_nhc_product_source(
                db,
                x,
                source,
                url,
                kind,
            )

        except Exception:
            ok = False

            log.exception(
                "NHC product source failed: %s",
                source,
            )

    return ok


def poll_nhc(
    db: StateDB,
    x: XPublisher,
) -> None:
    for (
        source,
        url,
    ) in NHC_TWO_FEEDS.items():
        try:
            process_rss_source(
                db,
                x,
                source=source,
                url=url,
                item_filter=nhc_item_is_real,
                formatter=lambda item:
                    format_nhc(
                        item,
                        "two",
                    ),
            )

        except Exception:
            log.exception(
                "NHC Tropical Weather Outlook "
                "source failed: %s",
                source,
            )

    now_ts = int(
        time.time()
    )

    for (
        basin,
        index_url,
    ) in NHC_BASIN_INDEX_FEEDS.items():
        fp_key = (
            f"nhc:index-fingerprint:{basin}"
        )

        sweep_key = (
            f"nhc:last-full-sweep:{basin}"
        )

        try:
            fingerprint = (
                _nhc_index_fingerprint(
                    index_url
                )
            )

            old_fingerprint = (
                db.get_meta(
                    fp_key
                )
            )

            try:
                last_sweep = int(
                    db.get_meta(
                        sweep_key,
                        "0",
                    )
                    or "0"
                )

            except ValueError:
                last_sweep = 0

            changed = (
                not old_fingerprint
                or fingerprint
                != old_fingerprint
            )

            due = (
                now_ts
                - last_sweep
                >= NHC_FULL_SWEEP_SECONDS
            )

            if changed or due:
                log.info(
                    "NHC %s product sweep (%s)",
                    basin,
                    (
                        "index changed"
                        if changed
                        else "safety sweep"
                    ),
                )

                if _nhc_sweep_basin(
                    db,
                    x,
                    basin,
                ):
                    db.set_meta(
                        sweep_key,
                        str(now_ts),
                    )

                    db.set_meta(
                        fp_key,
                        fingerprint,
                    )

                else:
                    log.warning(
                        "NHC %s sweep incomplete; "
                        "retrying next cycle",
                        basin,
                    )

            else:
                db.set_meta(
                    fp_key,
                    fingerprint,
                )

        except Exception:
            log.exception(
                "NHC basin index/sweep failed: %s",
                basin,
            )


# =============================================================================
# NWS alerts + tornado radar graphic
# =============================================================================


def fetch_nws_alerts_since(
    start: datetime,
) -> list[
    dict[
        str,
        Any,
    ]
]:
    params: Optional[
        dict[
            str,
            Any,
        ]
    ] = {
        "start":
            iso_z(start),
        "status":
            "actual",
        "limit":
            500,
    }

    url = NWS_ALERTS_URL

    features: list[
        dict[
            str,
            Any,
        ]
    ] = []

    pages = 0

    while (
        url
        and pages < 25
    ):
        response = http_get(
            url,
            params=params,
            headers={
                "Accept":
                    "application/geo+json"
            },
            timeout=(
                8,
                45,
            ),
        )

        data = response.json()

        if isinstance(
            data.get("features"),
            list,
        ):
            features.extend(
                data["features"]
            )

        pagination = (
            data.get("pagination")
            or {}
        )

        next_url = (
            pagination.get("next")
            if isinstance(
                pagination,
                dict,
            )
            else None
        )

        url = (
            str(next_url)
            if next_url
            else ""
        )

        params = None
        pages += 1

    return features


def alert_vtec_actions(
    props: dict[
        str,
        Any,
    ],
) -> set[str]:
    actions: set[str] = set()

    for value in all_parameter_values(
        props.get("parameters") or {},
        "VTEC",
    ):
        actions.update(
            re.findall(
                r"/[A-Z]\."
                r"(NEW|CON|EXT|EXA|EXB|"
                r"UPG|CAN|EXP|COR)"
                r"\.",
                value.upper(),
            )
        )

    return actions


def is_new_alert_message(
    props: dict[
        str,
        Any,
    ],
) -> bool:
    actions = alert_vtec_actions(
        props
    )

    return (
        "NEW" in actions
        if actions
        else str(
            props.get(
                "messageType",
                "",
            )
        ).lower()
        == "alert"
    )


def nws_alert_key(
    feature: dict[
        str,
        Any,
    ],
) -> str:
    props = (
        feature.get("properties")
        or {}
    )

    raw = (
        props.get("id")
        or feature.get("id")
        or props.get("@id")
    )

    if raw:
        return sha256_text(
            str(raw)
        )

    return sha256_text(
        "\x1f".join(
            str(
                props.get(key)
                or ""
            )
            for key in (
                "event",
                "sent",
                "headline",
                "areaDesc",
                "expires",
            )
        )
    )


def format_tornado_warning(
    feature: dict[
        str,
        Any,
    ],
) -> str:
    props = (
        feature.get("properties")
        or {}
    )

    params = (
        props.get("parameters")
        or {}
    )

    headline = squish(
        props.get("headline")
    )

    nws_headline = (
        first_parameter(
            params,
            "NWSheadline",
        )
    )

    emergency = (
        "TORNADO EMERGENCY"
        in (
            nws_headline
            or headline
        ).upper()
    )

    heading = (
        "🚨🚨 TORNADO EMERGENCY"
        if emergency
        else "🚨 TORNADO WARNING"
    )

    details = []

    detection = first_parameter(
        params,
        "tornadoDetection",
    )

    damage = first_parameter(
        params,
        "tornadoDamageThreat",
    )

    if detection:
        details.append(
            detection.title()
        )

    if (
        damage
        and damage.lower()
        not in {
            "base",
            "none",
        }
    ):
        details.append(
            f"Damage threat: "
            f"{damage.title()}"
        )

    official = (
        nws_headline
        or headline
    )

    if official.upper().startswith(
        "TORNADO WARNING"
    ):
        official = ""

    sender = squish(
        props.get("senderName")
    )

    expires = format_offset_time(
        props.get("expires")
    )

    return fit_post(
        [
            heading,
            truncate(
                squish(
                    props.get("areaDesc")
                ),
                100,
            ),
            (
                f"Until {expires}"
                if expires
                else ""
            ),
            " | ".join(details),
            truncate(
                official,
                105,
            ),
            (
                f"Issued by {sender}"
                if sender
                else "Source: NWS"
            ),
        ]
    )


def format_winter_alert(
    feature: dict[
        str,
        Any,
    ],
) -> str:
    props = (
        feature.get("properties")
        or {}
    )

    event = (
        squish(
            props.get("event")
        )
        or "Winter Weather Alert"
    )

    lower = event.lower()

    icon = (
        "🧊"
        if (
            "ice" in lower
            or "freezing" in lower
        )
        else "🌨️"
        if "blizzard" in lower
        else "🥶"
        if (
            "cold" in lower
            or "wind chill" in lower
        )
        else "❄️"
    )

    expires = format_offset_time(
        props.get("expires")
    )

    sender = squish(
        props.get("senderName")
    )

    return fit_post(
        [
            f"{icon} {event.upper()}",
            truncate(
                squish(
                    props.get("areaDesc")
                ),
                105,
            ),
            (
                f"Until {expires}"
                if expires
                else ""
            ),
            truncate(
                squish(
                    props.get("headline")
                ),
                110,
            ),
            (
                f"Issued by {sender}"
                if sender
                else "Source: NWS"
            ),
        ]
    )


def lonlat_to_web_mercator(
    lon: float,
    lat: float,
) -> tuple[
    float,
    float,
]:
    lat = max(
        min(
            lat,
            85.05112878,
        ),
        -85.05112878,
    )

    radius = 6378137.0

    return (
        radius
        * math.radians(lon),
        radius
        * math.log(
            math.tan(
                math.pi / 4
                + math.radians(lat) / 2
            )
        ),
    )


def warning_rings(
    geometry: Optional[
        dict[
            str,
            Any,
        ]
    ],
) -> list[
    list[
        list[
            float
        ]
    ]
]:
    if (
        not geometry
        or not isinstance(
            geometry.get("coordinates"),
            list,
        )
    ):
        return []

    coords = geometry[
        "coordinates"
    ]

    if (
        geometry.get("type")
        == "Polygon"
        and coords
    ):
        return (
            [coords[0]]
            if isinstance(
                coords[0],
                list,
            )
            else []
        )

    if (
        geometry.get("type")
        == "MultiPolygon"
    ):
        return [
            polygon[0]
            for polygon in coords
            if (
                isinstance(
                    polygon,
                    list,
                )
                and polygon
                and isinstance(
                    polygon[0],
                    list,
                )
            )
        ]

    return []


def map_bbox_for_rings(
    rings: list[
        list[
            list[
                float
            ]
        ]
    ],
    width: int,
    height: int,
) -> tuple[
    float,
    float,
    float,
    float,
]:
    points = [
        lonlat_to_web_mercator(
            float(coord[0]),
            float(coord[1]),
        )
        for ring in rings
        for coord in ring
        if (
            isinstance(
                coord,
                (
                    list,
                    tuple,
                ),
            )
            and len(coord) >= 2
        )
    ]

    if not points:
        raise ValueError(
            "Warning geometry has "
            "no usable coordinates"
        )

    xs = [
        point[0]
        for point in points
    ]

    ys = [
        point[1]
        for point in points
    ]

    minx = min(xs)
    maxx = max(xs)
    miny = min(ys)
    maxy = max(ys)

    cx = (
        minx + maxx
    ) / 2

    cy = (
        miny + maxy
    ) / 2

    raw_w = max(
        maxx - minx,
        120000.0,
    ) * 1.65

    raw_h = max(
        maxy - miny,
        90000.0,
    ) * 1.65

    aspect = width / height

    if raw_w / raw_h < aspect:
        raw_w = raw_h * aspect
    else:
        raw_h = raw_w / aspect

    return (
        cx - raw_w / 2,
        cy - raw_h / 2,
        cx + raw_w / 2,
        cy + raw_h / 2,
    )


def export_map_image(
    url: str,
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
    *,
    layers: str = "",
) -> Image.Image:
    params: dict[
        str,
        Any,
    ] = {
        "bbox":
            ",".join(
                f"{value:.3f}"
                for value in bbox
            ),
        "bboxSR":
            "3857",
        "imageSR":
            "3857",
        "size":
            f"{width},{height}",
        "format":
            "png32",
        "transparent":
            "true",
        "f":
            "image",
    }

    if layers:
        params[
            "layers"
        ] = layers

    response = http_get(
        url,
        params=params,
        headers={
            "Accept":
                "image/png,*/*"
        },
        timeout=(
            8,
            45,
        ),
    )

    return Image.open(
        io.BytesIO(
            response.content
        )
    ).convert(
        "RGBA"
    )


def map_ring_to_pixels(
    ring: list[
        list[
            float
        ]
    ],
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
) -> list[
    tuple[
        int,
        int,
    ]
]:
    (
        minx,
        miny,
        maxx,
        maxy,
    ) = bbox

    out = []

    for coord in ring:
        if (
            not isinstance(
                coord,
                (
                    list,
                    tuple,
                ),
            )
            or len(coord) < 2
        ):
            continue

        mx, my = (
            lonlat_to_web_mercator(
                float(coord[0]),
                float(coord[1]),
            )
        )

        out.append(
            (
                int(
                    round(
                        (
                            mx - minx
                        )
                        / (
                            maxx - minx
                        )
                        * (
                            width - 1
                        )
                    )
                ),
                int(
                    round(
                        (
                            maxy - my
                        )
                        / (
                            maxy - miny
                        )
                        * (
                            height - 1
                        )
                    )
                ),
            )
        )

    return out


def load_font(
    size: int,
    bold: bool = False,
) -> ImageFont.ImageFont:
    names = [
        (
            "/usr/share/fonts/truetype/dejavu/"
            "DejaVuSans-Bold.ttf"
            if bold
            else
            "/usr/share/fonts/truetype/dejavu/"
            "DejaVuSans.ttf"
        ),
        (
            "/usr/share/fonts/truetype/liberation2/"
            "LiberationSans-Bold.ttf"
            if bold
            else
            "/usr/share/fonts/truetype/liberation2/"
            "LiberationSans-Regular.ttf"
        ),
    ]

    for name in names:
        try:
            return ImageFont.truetype(
                name,
                size=size,
            )
        except Exception:
            pass

    return ImageFont.load_default()


def build_tornado_warning_image(
    feature: dict[
        str,
        Any,
    ],
) -> str:
    rings = warning_rings(
        feature.get("geometry")
    )

    if not rings:
        raise ValueError(
            "Tornado Warning has "
            "no polygon geometry"
        )

    map_w = 1200
    map_h = 760
    header_h = 190

    bbox = map_bbox_for_rings(
        rings,
        map_w,
        map_h,
    )

    radar = export_map_image(
        RADAR_EXPORT_URL,
        bbox,
        map_w,
        map_h,
    )

    refs = export_map_image(
        REFERENCE_EXPORT_URL,
        bbox,
        map_w,
        map_h,
        layers="show:2,3",
    )

    alpha = refs.getchannel("A")

    refs = ImageOps.invert(
        refs.convert("RGB")
    ).convert("RGBA")

    refs.putalpha(alpha)

    base = Image.new(
        "RGBA",
        (
            map_w,
            map_h,
        ),
        (
            18,
            20,
            23,
            255,
        ),
    )

    base.alpha_composite(radar)
    base.alpha_composite(refs)

    draw = ImageDraw.Draw(
        base,
        "RGBA",
    )

    for ring in rings:
        points = map_ring_to_pixels(
            ring,
            bbox,
            map_w,
            map_h,
        )

        if len(points) >= 3:
            draw.polygon(
                points,
                fill=(
                    255,
                    28,
                    28,
                    58,
                ),
            )

            draw.line(
                points + [points[0]],
                fill=(
                    255,
                    255,
                    255,
                    240,
                ),
                width=10,
                joint="curve",
            )

            draw.line(
                points + [points[0]],
                fill=(
                    235,
                    32,
                    32,
                    255,
                ),
                width=6,
                joint="curve",
            )

    props = (
        feature.get("properties")
        or {}
    )

    params = (
        props.get("parameters")
        or {}
    )

    headline = (
        first_parameter(
            params,
            "NWSheadline",
        )
        or squish(
            props.get("headline")
        )
    )

    emergency = (
        "TORNADO EMERGENCY"
        in headline.upper()
    )

    canvas = Image.new(
        "RGBA",
        (
            map_w,
            header_h + map_h,
        ),
        (
            12,
            13,
            15,
            255,
        ),
    )

    canvas.alpha_composite(
        base,
        dest=(
            0,
            header_h,
        ),
    )

    draw = ImageDraw.Draw(
        canvas,
        "RGBA",
    )

    draw.text(
        (
            30,
            20,
        ),
        (
            "TORNADO EMERGENCY"
            if emergency
            else "TORNADO WARNING"
        ),
        font=load_font(
            48,
            True,
        ),
        fill=(
            255,
            77,
            77,
            255,
        ),
    )

    draw.text(
        (
            30,
            82,
        ),
        truncate(
            squish(
                props.get("areaDesc")
            ),
            92,
        ),
        font=load_font(26),
        fill=(
            245,
            245,
            245,
            255,
        ),
    )

    details = []

    expires = format_offset_time(
        props.get("expires")
    )

    if expires:
        details.append(
            f"Until {expires}"
        )

    detection = first_parameter(
        params,
        "tornadoDetection",
    )

    if detection:
        details.append(
            detection.title()
        )

    damage = first_parameter(
        params,
        "tornadoDamageThreat",
    )

    if (
        damage
        and damage.lower()
        not in {
            "base",
            "none",
        }
    ):
        details.append(
            f"Damage threat: "
            f"{damage.title()}"
        )

    draw.text(
        (
            30,
            126,
        ),
        "  •  ".join(details),
        font=load_font(26),
        fill=(
            220,
            225,
            230,
            255,
        ),
    )

    tmp = tempfile.NamedTemporaryFile(
        prefix="oneweather_tor_",
        suffix=".jpg",
        delete=False,
    )

    tmp.close()

    canvas.convert("RGB").save(
        tmp.name,
        format="JPEG",
        quality=90,
        optimize=True,
    )

    return tmp.name


def poll_nws_alerts(
    db: StateDB,
    x: XPublisher,
) -> None:
    source = "nws_alerts"
    now = utcnow()

    previous = parse_any_datetime(
        db.get_meta(
            "nws:last_success"
        )
    )

    if previous is None:
        start = (
            now
            - timedelta(
                minutes=15
            )
        )

    else:
        floor = (
            now
            - timedelta(
                minutes=
                    NWS_QUERY_BACKFILL_MAX_MINUTES
            )
        )

        start = max(
            previous
            - timedelta(
                seconds=90
            ),
            floor,
        )

    features = fetch_nws_alerts_since(
        start
    )

    relevant: list[
        tuple[
            dict[
                str,
                Any,
            ],
            str,
        ]
    ] = []

    for feature in features:
        event = squish(
            (
                feature.get("properties")
                or {}
            ).get("event")
        )

        if event == "Tornado Warning":
            relevant.append(
                (
                    feature,
                    "tornado",
                )
            )

        elif event in WINTER_ALERT_EVENTS:
            relevant.append(
                (
                    feature,
                    "winter",
                )
            )

    relevant.sort(
        key=lambda pair:
            parse_any_datetime(
                (
                    pair[0]
                    .get("properties")
                    or {}
                ).get("sent")
            )
            or datetime(
                1970,
                1,
                1,
                tzinfo=timezone.utc,
            )
    )

    if not db.source_primed(source):
        for feature, _kind in relevant:
            db.mark_seen_without_post(
                source,
                nws_alert_key(
                    feature
                ),
            )

        db.mark_source_primed(
            source
        )

        log.info(
            "Primed %s with %d recent relevant alert(s)",
            source,
            len(relevant),
        )

        db.set_meta(
            "nws:last_success",
            iso_z(now),
        )

        return

    for feature, kind in relevant:
        props = (
            feature.get("properties")
            or {}
        )

        key = nws_alert_key(
            feature
        )

        if db.exists(
            source,
            key,
        ):
            continue

        if not is_new_alert_message(
            props
        ):
            db.mark_seen_without_post(
                source,
                key,
                status="non_new_vtec",
            )
            continue

        age = age_minutes(
            props.get("sent")
        )

        max_age = (
            TORNADO_MAX_POST_AGE_MINUTES
            if kind == "tornado"
            else
            WINTER_ALERT_MAX_POST_AGE_MINUTES
        )

        if (
            age is not None
            and age > max_age
        ):
            db.mark_seen_without_post(
                source,
                key,
                status="stale",
            )
            continue

        image_path = ""

        try:
            if kind == "tornado":
                text = format_tornado_warning(
                    feature
                )

                try:
                    image_path = (
                        build_tornado_warning_image(
                            feature
                        )
                    )

                except Exception:
                    log.exception(
                        "Could not build tornado-warning "
                        "radar image; posting text only"
                    )

            else:
                text = format_winter_alert(
                    feature
                )

            publish_once(
                db,
                x,
                source,
                key,
                text,
                image_path=image_path,
            )

        finally:
            if image_path:
                try:
                    os.unlink(
                        image_path
                    )
                except OSError:
                    pass

    db.set_meta(
        "nws:last_success",
        iso_z(now),
    )


# =============================================================================
# WPC Excessive Rainfall Outlooks
# =============================================================================


def _arcgis_features(
    mapserver: str,
    layer: int,
    out_fields: str,
) -> list[
    dict[
        str,
        Any,
    ]
]:
    response = http_get(
        f"{mapserver}/{layer}/query",
        params={
            "where":
                "1=1",
            "outFields":
                out_fields,
            "returnGeometry":
                "false",
            "f":
                "json",
        },
        headers={
            "Accept":
                "application/json"
        },
        timeout=(
            8,
            35,
        ),
    )

    payload = response.json()

    if payload.get("error"):
        raise RuntimeError(
            f"NOAA ArcGIS error layer "
            f"{layer}: "
            f"{payload['error']!r}"
        )

    return [
        dict(
            feature.get("attributes")
            or {}
        )
        for feature
        in payload.get("features")
        or []
    ]


def _first_nonempty(
    values: Iterable[Any],
) -> str:
    for value in values:
        text = squish(
            str(
                value
                or ""
            )
        )

        if text:
            return text

    return ""


@dataclass(frozen=True)
class EROProduct:
    day: int
    issued: str
    valid: str
    headline: str

    @property
    def key(self) -> str:
        return sha256_text(
            f"{self.day}|"
            f"{self.issued}|"
            f"{self.valid}|"
            f"{self.headline}"
        )


def parse_wpc_ero(
    day: int,
) -> EROProduct:
    attrs = _arcgis_features(
        WPC_ERO_MAPSERVER,
        day - 1,
        (
            "product,"
            "valid_time,"
            "outlook,"
            "issue_time,"
            "start_time,"
            "end_time,"
            "dn,"
            "idp_ingestdate"
        ),
    )

    if not attrs:
        raise ValueError(
            f"WPC ERO Day {day} "
            f"returned no features"
        )

    issued = _first_nonempty(
        attribute.get("issue_time")
        for attribute in attrs
    )

    valid = _first_nonempty(
        attribute.get("valid_time")
        for attribute in attrs
    )

    if not valid:
        valid = " to ".join(
            value
            for value in (
                _first_nonempty(
                    attribute.get("start_time")
                    for attribute in attrs
                ),
                _first_nonempty(
                    attribute.get("end_time")
                    for attribute in attrs
                ),
            )
            if value
        )

    if not issued:
        raw = max(
            (
                attribute.get("idp_ingestdate")
                or 0
                for attribute in attrs
            ),
            default=0,
        )

        if raw:
            issued = iso_z(
                datetime.fromtimestamp(
                    float(raw) / 1000.0,
                    tz=timezone.utc,
                )
            )

    if not issued:
        raise ValueError(
            f"WPC ERO Day {day} "
            f"had no issue time"
        )

    ranks = {
        "marginal": 1,
        "slight": 2,
        "moderate": 3,
        "high": 4,
    }

    best_name = ""
    best_rank = -1

    for attribute in attrs:
        outlook = squish(
            str(
                attribute.get("outlook")
                or ""
            )
        )

        try:
            rank = int(
                float(
                    attribute.get("dn")
                )
            )

        except Exception:
            rank = max(
                (
                    value
                    for key, value
                    in ranks.items()
                    if key in outlook.lower()
                ),
                default=0,
            )

        if rank > best_rank:
            best_name = outlook
            best_rank = rank

    return EROProduct(
        day,
        issued,
        valid,
        (
            f"Highest risk: {best_name}"
            if best_name
            else
            "Official WPC outlook updated"
        ),
    )


def format_ero(
    product: EROProduct,
) -> str:
    return fit_post(
        [
            f"🌧️ WPC DAY {product.day} "
            f"EXCESSIVE RAINFALL OUTLOOK",
            truncate(
                product.headline,
                135,
            ),
            (
                f"Valid: "
                f"{truncate(product.valid, 90)}"
                if product.valid
                else ""
            ),
            (
                f"Issued/updated: "
                f"{truncate(product.issued, 65)}"
            ),
            "Source: NOAA/NWS WPC",
        ],
        WPC_ERO_PUBLIC_URL,
    )


def poll_wpc_ero(
    db: StateDB,
    x: XPublisher,
) -> None:
    days = (
        [1, 2, 3]
        + (
            [4, 5]
            if ENABLE_WPC_DAY4_DAY5_ERO
            else []
        )
    )

    for day in days:
        source = (
            f"wpc_ero_day{day}"
        )

        try:
            product = parse_wpc_ero(
                day
            )

            if not db.source_primed(
                source
            ):
                db.mark_seen_without_post(
                    source,
                    product.key,
                )

                db.mark_source_primed(
                    source
                )

                log.info(
                    "Primed %s: %s",
                    source,
                    product.issued,
                )

            elif not db.exists(
                source,
                product.key,
            ):
                publish_once(
                    db,
                    x,
                    source,
                    product.key,
                    format_ero(product),
                )

        except Exception:
            log.exception(
                "WPC ERO Day %d poll failed",
                day,
            )


# =============================================================================
# WPC heavy snow/ice discussion + winter probability packages
# =============================================================================


@dataclass(frozen=True)
class WPCWinterDiscussion:
    identity: str
    issued_line: str
    valid_line: str
    headline: str

    @property
    def key(self) -> str:
        return sha256_text(
            self.identity
        )


def _parse_wmo_ddhhmm_from_text(
    product_text: str,
) -> Optional[datetime]:
    match = re.search(
        r"(?m)^FOUS11\s+KWBC\s+(\d{6})\b",
        product_text,
    )

    if not match:
        return None

    stamp = match.group(1)

    day = int(stamp[:2])
    hour = int(stamp[2:4])
    minute = int(stamp[4:6])

    now = utcnow()

    candidates: list[datetime] = []

    for offset in (
        -1,
        0,
        1,
    ):
        year = now.year
        month = now.month + offset

        if month < 1:
            month = 12
            year -= 1

        elif month > 12:
            month = 1
            year += 1

        try:
            candidates.append(
                datetime(
                    year,
                    month,
                    day,
                    hour,
                    minute,
                    tzinfo=timezone.utc,
                )
            )

        except ValueError:
            pass

    plausible = [
        date
        for date in candidates
        if (
            date
            <= now + timedelta(hours=6)
        )
    ]

    if plausible:
        return max(plausible)

    return (
        min(
            candidates,
            key=lambda date:
                abs(
                    (
                        date - now
                    ).total_seconds()
                ),
        )
        if candidates
        else None
    )


def _wpc_hsd_from_products_api(
) -> tuple[
    str,
    str,
    str,
]:
    response = http_get(
        NWS_PRODUCTS_URL,
        params={
            "type":
                WPC_HSD_TYPE,
            "location":
                WPC_HSD_LOCATION,
            "limit":
                10,
        },
        headers={
            "Accept":
                "application/ld+json,"
                "application/json"
        },
        timeout=(
            8,
            35,
        ),
    )

    payload = response.json()

    graph = (
        payload.get("@graph")
        or payload.get("products")
        or payload.get("features")
        or []
    )

    if (
        not isinstance(
            graph,
            list,
        )
        or not graph
    ):
        return (
            "",
            "",
            "",
        )

    candidates: list[
        tuple[
            datetime,
            dict[
                str,
                Any,
            ],
        ]
    ] = []

    for item in graph:
        if not isinstance(
            item,
            dict,
        ):
            continue

        issued = parse_any_datetime(
            str(
                item.get("issuanceTime")
                or item.get("issuance_time")
                or ""
            )
        )

        candidates.append(
            (
                issued
                or datetime(
                    1970,
                    1,
                    1,
                    tzinfo=timezone.utc,
                ),
                item,
            )
        )

    if not candidates:
        return (
            "",
            "",
            "",
        )

    candidates.sort(
        key=lambda pair:
            pair[0],
        reverse=True,
    )

    issued_dt, newest = (
        candidates[0]
    )

    if (
        issued_dt.year > 1970
        and max(
            0.0,
            (
                utcnow()
                - issued_dt
            ).total_seconds()
            / 3600.0,
        )
        > WPC_HSD_MAX_AGE_HOURS
    ):
        return (
            "",
            "",
            "",
        )

    ref = str(
        newest.get("@id")
        or newest.get("id")
        or ""
    ).strip()

    if not ref:
        return (
            "",
            "",
            "",
        )

    url = (
        ref
        if ref.startswith(
            (
                "http://",
                "https://",
            )
        )
        else
        f"https://api.weather.gov/"
        f"products/{ref}"
    )

    detail = http_get(
        url,
        headers={
            "Accept":
                "application/ld+json,"
                "application/json"
        },
        timeout=(
            8,
            35,
        ),
    ).json()

    text = str(
        detail.get("productText")
        or detail.get("product_text")
        or ""
    )

    issuance = squish(
        str(
            detail.get("issuanceTime")
            or detail.get("issuance_time")
            or newest.get("issuanceTime")
            or ""
        )
    )

    identity = squish(
        str(
            detail.get("id")
            or detail.get("@id")
            or ref
        )
    )

    return (
        text,
        issuance,
        identity,
    )


def _wpc_hsd_from_tgftp(
) -> tuple[
    str,
    str,
    str,
]:
    response = http_get(
        WPC_HSD_RAW_URL,
        headers={
            "Accept":
                "text/plain,*/*"
        },
        timeout=(
            8,
            35,
        ),
    )

    text = (
        response.text
        or ""
    )

    if not text.strip():
        return (
            "",
            "",
            "",
        )

    issued_dt = (
        _parse_wmo_ddhhmm_from_text(
            text
        )
    )

    if issued_dt is not None:
        age_hours = max(
            0.0,
            (
                utcnow()
                - issued_dt
            ).total_seconds()
            / 3600.0,
        )

        if (
            age_hours
            > WPC_HSD_MAX_AGE_HOURS
        ):
            return (
                "",
                "",
                "",
            )

        issuance = iso_z(
            issued_dt
        )

    else:
        issuance = ""

    return (
        text,
        issuance,
        sha256_text(text),
    )


def parse_wpc_heavy_snow_discussion(
) -> Optional[
    WPCWinterDiscussion
]:
    text = ""
    issuance = ""
    identity = ""

    api_error: Optional[
        Exception
    ] = None

    try:
        (
            text,
            issuance,
            identity,
        ) = (
            _wpc_hsd_from_products_api()
        )

    except Exception as exc:
        api_error = exc

        log.warning(
            "NWS Products API QPFHSD lookup failed; "
            "trying TGFTP fallback: %s",
            exc,
        )

    if not text:
        try:
            (
                fallback_text,
                fallback_issuance,
                fallback_identity,
            ) = (
                _wpc_hsd_from_tgftp()
            )

            text = fallback_text

            issuance = (
                issuance
                or fallback_issuance
            )

            identity = (
                identity
                or fallback_identity
            )

        except requests.HTTPError as exc:
            status = getattr(
                exc.response,
                "status_code",
                None,
            )

            if status not in {
                404,
                410,
            }:
                if api_error is not None:
                    raise RuntimeError(
                        "Both NWS QPFHSD sources failed: "
                        f"API={api_error!r}; "
                        f"TGFTP={exc!r}"
                    ) from exc

                raise

        except Exception as exc:
            if api_error is not None:
                raise RuntimeError(
                    "Both NWS QPFHSD sources failed: "
                    f"API={api_error!r}; "
                    f"TGFTP={exc!r}"
                ) from exc

            raise

    if not text:
        return None

    upper = text.upper()

    if (
        "QPFHSD" not in upper
        and "HEAVY SNOW" not in upper
        and "PROBABILISTIC HEAVY SNOW"
        not in upper
    ):
        raise ValueError(
            "Retrieved FOUS11/HSD product "
            "was not the WPC heavy snow/"
            "icing discussion"
        )

    lines = [
        line.strip()
        for line in text.splitlines()
        if line.strip()
    ]

    valid_line = next(
        (
            squish(
                line[5:]
            )
            for line in lines
            if line.lower().startswith(
                "valid "
            )
        ),
        "",
    )

    compact = re.sub(
        r"\s+",
        " ",
        text,
    )

    headline_match = re.search(
        r"\.\.\.\s*(.*?)\s*\.\.\.",
        compact,
    )

    headline = (
        squish(
            headline_match.group(1)
        )
        if headline_match
        else ""
    )

    if not issuance:
        issued_dt = (
            _parse_wmo_ddhhmm_from_text(
                text
            )
        )

        if issued_dt:
            issuance = iso_z(
                issued_dt
            )

        else:
            for index, line in enumerate(
                lines
            ):
                if (
                    "Weather Prediction Center"
                    in line
                    and index + 1
                    < len(lines)
                ):
                    issuance = squish(
                        lines[
                            index + 1
                        ]
                    )
                    break

    identity = (
        identity
        or
        f"{issuance}|"
        f"{valid_line}|"
        f"{headline}|"
        f"{sha256_text(text)}"
    )

    return WPCWinterDiscussion(
        identity,
        issuance,
        valid_line,
        headline,
    )


def format_wpc_heavy_snow(
    disc: WPCWinterDiscussion,
) -> str:
    return fit_post(
        [
            "❄️ WPC PROBABILISTIC "
            "HEAVY SNOW & ICE DISCUSSION",
            truncate(
                disc.headline,
                125,
            ),
            (
                f"Valid: "
                f"{truncate(disc.valid_line, 90)}"
                if disc.valid_line
                else ""
            ),
            (
                f"Issued: "
                f"{truncate(disc.issued_line, 70)}"
                if disc.issued_line
                else ""
            ),
            "Source: NOAA/NWS WPC",
        ],
        WPC_HSD_PUBLIC_URL,
    )


def parse_wpc_winter_package_updates(
) -> list[
    tuple[
        int,
        str,
    ]
]:
    day_layers = {
        1: (
            1,
            2,
            3,
            4,
        ),
        2: (
            6,
            7,
            8,
            9,
        ),
        3: (
            11,
            12,
            13,
            14,
        ),
    }

    out: list[
        tuple[
            int,
            str,
        ]
    ] = []

    for day, layers in day_layers.items():
        attrs: list[
            dict[
                str,
                Any,
            ]
        ] = []

        for layer in layers:
            attrs.extend(
                _arcgis_features(
                    WPC_WINTER_MAPSERVER,
                    layer,
                    (
                        "product,"
                        "valid_time,"
                        "outlook,"
                        "issue_time,"
                        "start_time,"
                        "end_time,"
                        "dn,"
                        "idp_ingestdate"
                    ),
                )
            )

        if not attrs:
            continue

        issue = _first_nonempty(
            attribute.get("issue_time")
            for attribute in attrs
        )

        valid = _first_nonempty(
            attribute.get("valid_time")
            for attribute in attrs
        )

        if not issue:
            raw = max(
                (
                    attribute.get(
                        "idp_ingestdate"
                    )
                    or 0
                    for attribute in attrs
                ),
                default=0,
            )

            if raw:
                issue = iso_z(
                    datetime.fromtimestamp(
                        float(raw) / 1000.0,
                        tz=timezone.utc,
                    )
                )

        if issue:
            out.append(
                (
                    day,
                    (
                        issue
                        + (
                            f" | Valid {valid}"
                            if valid
                            else ""
                        )
                    ),
                )
            )

    return out


def poll_wpc_winter(
    db: StateDB,
    x: XPublisher,
) -> None:
    if ENABLE_WPC_HEAVY_SNOW_DISCUSSION:
        source = (
            "wpc_heavy_snow_discussion"
        )

        try:
            disc = (
                parse_wpc_heavy_snow_discussion()
            )

            if disc is None:
                if (
                    db.get_meta(
                        "wpc_hsd:no_current_logged"
                    )
                    != "1"
                ):
                    log.info(
                        "No current WPC heavy snow/ice "
                        "discussion "
                        "(normal outside the routine "
                        "winter season)"
                    )

                    db.set_meta(
                        "wpc_hsd:no_current_logged",
                        "1",
                    )

            else:
                db.set_meta(
                    "wpc_hsd:no_current_logged",
                    "0",
                )

                if not db.source_primed(
                    source
                ):
                    db.mark_seen_without_post(
                        source,
                        disc.key,
                    )

                    db.mark_source_primed(
                        source
                    )

                    log.info(
                        "Primed %s",
                        source,
                    )

                elif not db.exists(
                    source,
                    disc.key,
                ):
                    publish_once(
                        db,
                        x,
                        source,
                        disc.key,
                        format_wpc_heavy_snow(
                            disc
                        ),
                    )

        except Exception:
            log.exception(
                "WPC heavy snow/ice discussion "
                "poll failed"
            )

    if ENABLE_WPC_WINTER_PACKAGES:
        source = (
            "wpc_winter_packages"
        )

        try:
            updates = (
                parse_wpc_winter_package_updates()
            )

            keyed = [
                (
                    day,
                    update,
                    sha256_text(
                        f"day{day}|{update}"
                    ),
                )
                for day, update in updates
            ]

            if not db.source_primed(
                source
            ):
                for (
                    _day,
                    _update,
                    key,
                ) in keyed:
                    db.mark_seen_without_post(
                        source,
                        key,
                    )

                db.mark_source_primed(
                    source
                )

                log.info(
                    "Primed %s with %d active "
                    "package timestamp(s)",
                    source,
                    len(keyed),
                )

            else:
                for (
                    day,
                    update,
                    key,
                ) in keyed:
                    if db.exists(
                        source,
                        key,
                    ):
                        continue

                    text = fit_post(
                        [
                            f"❄️ WPC DAY {day} "
                            f"WINTER WEATHER "
                            f"FORECAST UPDATED",
                            update,
                            "Probabilistic snow and "
                            "freezing-rain guidance.",
                            "Source: NOAA/NWS WPC",
                        ],
                        WPC_WINTER_PUBLIC_URL,
                    )

                    publish_once(
                        db,
                        x,
                        source,
                        key,
                        text,
                    )

        except Exception:
            log.exception(
                "WPC winter-package poll failed"
            )


# =============================================================================
# Scheduler
# =============================================================================


@dataclass
class Job:
    name: str
    interval: int
    func: Callable[
        [
            StateDB,
            XPublisher,
        ],
        None,
    ]
    next_due: float = 0.0


def verify_x_credentials(
    x: XPublisher,
) -> None:
    if DRY_RUN:
        log.info(
            "DRY_RUN=true: skipping "
            "X credential verification"
        )
        return

    log.info(
        "Authenticated to X as @%s",
        x.verify(),
    )


def main() -> int:
    validate_environment()

    db = StateDB(
        DB_PATH
    )

    x = XPublisher(
        db
    )

    log.info(
        "Starting %s worker",
        BOT_NAME,
    )

    log.info(
        "BUILD=%s",
        BUILD_ID,
    )

    log.info(
        "DB=%s "
        "DRY_RUN=%s "
        "INCLUDE_SOURCE_URLS=%s",
        DB_PATH,
        DRY_RUN,
        INCLUDE_SOURCE_URLS,
    )

    log.info(
        "Intervals: "
        "NWS=%ss "
        "SPC=%ss "
        "NHC=%ss "
        "WPC_ERO=%ss "
        "WPC_WINTER=%ss",
        NWS_POLL_SECONDS,
        SPC_POLL_SECONDS,
        NHC_POLL_SECONDS,
        WPC_ERO_POLL_SECONDS,
        WPC_WINTER_POLL_SECONDS,
    )

    while not STOP_REQUESTED:
        try:
            verify_x_credentials(
                x
            )

            break

        except XRetryableError as exc:
            log.warning(
                "Temporary X startup/auth failure: %s",
                exc,
            )

            time.sleep(
                30
            )

        except Exception:
            db.close()

            log.exception(
                "X credential verification failed; "
                "refusing to run"
            )

            return 2

    if STOP_REQUESTED:
        db.close()
        return 0

    jobs = [
        Job(
            "nws",
            NWS_POLL_SECONDS,
            poll_nws_alerts,
        ),
        Job(
            "spc",
            SPC_POLL_SECONDS,
            poll_spc,
        ),
        Job(
            "nhc",
            NHC_POLL_SECONDS,
            poll_nhc,
        ),
        Job(
            "wpc_ero",
            WPC_ERO_POLL_SECONDS,
            poll_wpc_ero,
        ),
        Job(
            "wpc_winter",
            WPC_WINTER_POLL_SECONDS,
            poll_wpc_winter,
        ),
    ]

    base = time.monotonic()

    for index, job in enumerate(
        jobs
    ):
        job.next_due = (
            base
            + index * 0.8
        )

    try:
        while not STOP_REQUESTED:
            now = time.monotonic()

            for job in jobs:
                if STOP_REQUESTED:
                    break

                if now < job.next_due:
                    continue

                try:
                    job.func(
                        db,
                        x,
                    )

                except Exception:
                    log.exception(
                        "Unhandled failure in job %s",
                        job.name,
                    )

                job.next_due = (
                    time.monotonic()
                    + job.interval
                )

            time.sleep(
                0.5
            )

    finally:
        log.info(
            "Stopping. DB status counts: %s",
            db.count_by_status(),
        )

        db.close()

    return 0


if __name__ == "__main__":
    sys.exit(
        main()
    )
