#!/usr/bin/env python3
"""
OneWeather production weather-to-X worker
==========================================

Continuously monitors official NOAA/NWS/NCEP products and posts new items to X.
Designed for a single Render Background Worker with a persistent disk.

Sources monitored by default:
  - SPC: mesoscale discussions, convective outlooks, tornado/severe thunderstorm
    watches, and fire-weather outlooks (official SPC RSS feeds)
  - NWS: newly issued Tornado Warnings and newly issued winter-weather
    watches/warnings/advisories from api.weather.gov
  - NHC/CPHC: Tropical Weather Outlooks, Public Advisories, Forecast Discussions,
    and Tropical Cyclone Updates (official RSS feeds, Atlantic/E Pacific/C Pacific)
  - WPC: Day 1-5 Excessive Rainfall Outlooks, the Probabilistic Heavy Snow and
    Icing Discussion, and Day 1-3 winter forecast-package update notices

Tornado Warning posts include a generated image using:
  - official NOAA/NWS MRMS base reflectivity
  - official NWS state/county reference boundaries
  - the exact warning polygon from the NWS CAP/GeoJSON alert

Important deployment behavior:
  - Each source is independently "primed" on its first successful poll. Existing
    products are recorded but NOT posted. Only later products are posted.
  - SQLite provides durable de-duplication. Put DB_PATH on a Render persistent disk.
  - X posting is deliberately at-most-once across ambiguous network failures. If an
    X request times out after it may have reached X, the item is marked ambiguous
    instead of blindly retrying and risking a duplicate post.

Required runtime environment variables:
  X_CLIENT_ID
  X_CLIENT_SECRET
  X_REFRESH_TOKEN
  X_ACCESS_TOKEN
  CONTACT_EMAIL

Recommended Render environment variables:
  DB_PATH=/var/data/oneweather2.sqlite3
  DRY_RUN=false
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import html
import io
import logging
import math
import os
import re
import secrets
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
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import parse_qs, urlencode, urlparse
import webbrowser
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
BUILD_ID = "2026-08-26-auth-wpc-v3"
CONTACT_EMAIL = os.getenv("CONTACT_EMAIL", "").strip()

X_CLIENT_ID = os.getenv("X_CLIENT_ID", "").strip()
X_CLIENT_SECRET = os.getenv("X_CLIENT_SECRET", "").strip()
X_ACCESS_TOKEN = os.getenv("X_ACCESS_TOKEN", "").strip()
X_REFRESH_TOKEN = os.getenv("X_REFRESH_TOKEN", "").strip()
X_REDIRECT_URI = os.getenv(
    "X_REDIRECT_URI", "http://127.0.0.1:8765/callback"
).strip()

DB_PATH = os.getenv("DB_PATH", "/var/data/oneweather.sqlite3").strip()

DRY_RUN = os.getenv("DRY_RUN", "false").lower() in {
    "1",
    "true",
    "yes",
    "on",
}

INCLUDE_SOURCE_URLS = os.getenv(
    "INCLUDE_SOURCE_URLS", "false"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

NWS_POLL_SECONDS = max(
    30, int(os.getenv("NWS_POLL_SECONDS", "30"))
)

SPC_POLL_SECONDS = max(
    30, int(os.getenv("SPC_POLL_SECONDS", "60"))
)

NHC_POLL_SECONDS = max(
    30, int(os.getenv("NHC_POLL_SECONDS", "60"))
)

NHC_FULL_SWEEP_SECONDS = max(
    300, int(os.getenv("NHC_FULL_SWEEP_SECONDS", "600"))
)

WPC_ERO_POLL_SECONDS = max(
    60, int(os.getenv("WPC_ERO_POLL_SECONDS", "120"))
)

WPC_WINTER_POLL_SECONDS = max(
    60, int(os.getenv("WPC_WINTER_POLL_SECONDS", "300"))
)

TORNADO_MAX_POST_AGE_MINUTES = max(
    5,
    int(os.getenv("TORNADO_MAX_POST_AGE_MINUTES", "30")),
)

WINTER_ALERT_MAX_POST_AGE_MINUTES = max(
    30,
    int(os.getenv("WINTER_ALERT_MAX_POST_AGE_MINUTES", "360")),
)

NWS_QUERY_BACKFILL_MAX_MINUTES = max(
    15,
    min(
        10080,
        int(os.getenv("NWS_QUERY_BACKFILL_MAX_MINUTES", "360")),
    ),
)

POST_TEXT_LIMIT = max(
    180,
    min(
        270,
        int(os.getenv("POST_TEXT_LIMIT", "265")),
    ),
)

ENABLE_SPC_FIRE = os.getenv(
    "ENABLE_SPC_FIRE", "true"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

ENABLE_NHC_DISCUSSIONS = os.getenv(
    "ENABLE_NHC_DISCUSSIONS", "true"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

ENABLE_NHC_FORECAST_ADVISORIES = os.getenv(
    "ENABLE_NHC_FORECAST_ADVISORIES", "false"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

ENABLE_WPC_DAY4_DAY5_ERO = os.getenv(
    "ENABLE_WPC_DAY4_DAY5_ERO", "true"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

ENABLE_WPC_HEAVY_SNOW_DISCUSSION = os.getenv(
    "ENABLE_WPC_HEAVY_SNOW_DISCUSSION", "true"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

ENABLE_WPC_WINTER_PACKAGES = os.getenv(
    "ENABLE_WPC_WINTER_PACKAGES", "true"
).lower() in {
    "1",
    "true",
    "yes",
    "on",
}

LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()


# =============================================================================
# Official endpoints
# =============================================================================

NWS_ALERTS_URL = "https://api.weather.gov/alerts"

X_AUTHORIZE_URL = "https://x.com/i/oauth2/authorize"
X_TOKEN_URL = "https://api.x.com/2/oauth2/token"
X_ME_URL = "https://api.x.com/2/users/me"
X_POST_URL = "https://api.x.com/2/tweets"
X_MEDIA_URL = "https://api.x.com/2/media/upload"

X_SCOPES = [
    "tweet.read",
    "tweet.write",
    "users.read",
    "media.write",
    "offline.access",
]

SPC_FEEDS = {
    "spc_md": (
        "https://www.spc.noaa.gov/products/spcmdrss.xml",
        "md",
    ),
    "spc_convective": (
        "https://www.spc.noaa.gov/products/spcacrss.xml",
        "convective",
    ),
    "spc_watches": (
        "https://www.spc.noaa.gov/products/spcwwrss.xml",
        "watch",
    ),
}

if ENABLE_SPC_FIRE:
    SPC_FEEDS["spc_fire"] = (
        "https://www.spc.noaa.gov/products/spcfwrss.xml",
        "fire",
    )

NHC_TWO_FEEDS = {
    "nhc_two_atlantic":
        "https://www.nhc.noaa.gov/xml/TWOAT.xml",
    "nhc_two_epac":
        "https://www.nhc.noaa.gov/xml/TWOEP.xml",
    "nhc_two_cpac":
        "https://www.nhc.noaa.gov/xml/TWOCP.xml",
}

NHC_BASIN_INDEX_FEEDS = {
    "atlantic":
        "https://www.nhc.noaa.gov/index-at.xml",
    "epac":
        "https://www.nhc.noaa.gov/index-ep.xml",
    "cpac":
        "https://www.nhc.noaa.gov/index-cp.xml",
}

NHC_BASIN_CODES = {
    "atlantic": "AT",
    "epac": "EP",
    "cpac": "CP",
}

RADAR_EXPORT_URL = (
    "https://mapservices.weather.noaa.gov/"
    "eventdriven/rest/services/"
    "radar/radar_base_reflectivity/MapServer/export"
)

REFERENCE_EXPORT_URL = (
    "https://mapservices.weather.noaa.gov/"
    "static/rest/services/"
    "nws_reference_maps/nws_reference_map/MapServer/export"
)

# IMPORTANT:
# Do not scrape WPC's PHP/HTML pages from Render.
# They can reject cloud-hosted requests with HTTP 403.
#
# These are official NOAA machine-facing services.

WPC_ERO_MAPSERVER = (
    "https://mapservices.weather.noaa.gov/vector/"
    "rest/services/hazards/"
    "wpc_precip_hazards/MapServer"
)

WPC_WINTER_MAPSERVER = (
    "https://mapservices.weather.noaa.gov/vector/"
    "rest/services/precip/"
    "wpc_prob_winter_precip/MapServer"
)

WPC_HSD_API_URL = (
    "https://api.weather.gov/"
    "products/types/QPF/locations/HSD/latest"
)

WPC_HSD_PUBLIC_URL = (
    "https://www.wpc.ncep.noaa.gov/"
    "discussions/qpfhsd.html"
)

WPC_ERO_PUBLIC_URL = (
    "https://www.wpc.ncep.noaa.gov/"
    "qpf/excessive_rainfall_outlook_ero.php"
)

WPC_WINTER_PUBLIC_URL = (
    "https://www.wpc.ncep.noaa.gov/"
    "wwd/winter_wx.shtml"
)

WINTER_ALERT_EVENTS = {
    "Winter Storm Warning",
    "Winter Storm Watch",
    "Winter Weather Advisory",
    "Blizzard Warning",
    "Blizzard Watch",
    "Ice Storm Warning",
    "Lake Effect Snow Warning",
    "Lake Effect Snow Watch",
    "Lake Effect Snow Advisory",
    "Snow Squall Warning",
    "Extreme Cold Warning",
    "Extreme Cold Watch",
    "Cold Weather Advisory",
    "Wind Chill Warning",
    "Wind Chill Watch",
    "Wind Chill Advisory",
    "Heavy Snow Warning",
    "Freezing Rain Advisory",
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


def _request_stop(
    signum: int,
    _frame: Any,
) -> None:
    global STOP_REQUESTED
    STOP_REQUESTED = True

    log.info(
        "Received signal %s; finishing current work and stopping.",
        signum,
    )


signal.signal(
    signal.SIGTERM,
    _request_stop,
)

signal.signal(
    signal.SIGINT,
    _request_stop,
)


# =============================================================================
# General helpers
# =============================================================================


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def iso_z(
    dt: datetime,
) -> str:
    return (
        dt.astimezone(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def sha256_text(
    value: str,
) -> str:
    return hashlib.sha256(
        value.encode(
            "utf-8",
            errors="replace",
        )
    ).hexdigest()


def squish(
    value: Optional[str],
) -> str:
    if not value:
        return ""

    return re.sub(
        r"\s+",
        " ",
        html.unescape(value),
    ).strip()


def html_to_text(
    value: Optional[str],
    preserve_lines: bool = False,
) -> str:
    if not value:
        return ""

    soup = BeautifulSoup(
        value,
        "html.parser",
    )

    sep = "\n" if preserve_lines else " "

    text = soup.get_text(
        sep,
        strip=True,
    )

    if preserve_lines:
        lines = [
            re.sub(
                r"[ \t]+",
                " ",
                line,
            ).strip()
            for line in text.splitlines()
        ]

        return "\n".join(
            line
            for line in lines
            if line
        )

    return squish(text)


def truncate(
    value: str,
    limit: int,
) -> str:
    value = squish(value)

    if len(value) <= limit:
        return value

    if limit <= 1:
        return "…"[:limit]

    cut = value[
        : limit - 1
    ].rstrip()

    if (
        " " in cut
        and
        len(
            cut.rsplit(
                " ",
                1,
            )[0]
        )
        >= int(limit * 0.72)
    ):
        cut = cut.rsplit(
            " ",
            1,
        )[0]

    return cut + "…"


def fit_post(
    parts: Iterable[str],
    url: str = "",
) -> str:
    clean_parts = [
        part.strip()
        for part in parts
        if part
        and part.strip()
    ]

    suffix = ""

    if (
        INCLUDE_SOURCE_URLS
        and
        url
    ):
        suffix = "\n\n" + url.strip()

    budget = (
        POST_TEXT_LIMIT
        -
        len(suffix)
    )

    if budget < 80:
        budget = POST_TEXT_LIMIT
        suffix = ""

    text = "\n".join(
        clean_parts
    )

    if len(text) > budget:
        text = truncate(
            text,
            budget,
        )

    return text + suffix


def parse_any_datetime(
    value: Optional[str],
) -> Optional[datetime]:
    if not value:
        return None

    value = value.strip()

    try:
        dt = datetime.fromisoformat(
            value.replace(
                "Z",
                "+00:00",
            )
        )

        if dt.tzinfo is None:
            dt = dt.replace(
                tzinfo=timezone.utc
            )

        return dt.astimezone(
            timezone.utc
        )

    except Exception:
        pass

    try:
        dt = parsedate_to_datetime(
            value
        )

        if dt.tzinfo is None:
            dt = dt.replace(
                tzinfo=timezone.utc
            )

        return dt.astimezone(
            timezone.utc
        )

    except Exception:
        return None


def age_minutes(
    value: Optional[str],
) -> Optional[float]:
    dt = parse_any_datetime(
        value
    )

    if not dt:
        return None

    return max(
        0.0,
        (
            utcnow()
            -
            dt
        ).total_seconds()
        /
        60.0,
    )


def format_offset_time(
    value: Optional[str],
) -> str:
    if not value:
        return ""

    try:
        dt = datetime.fromisoformat(
            value.replace(
                "Z",
                "+00:00",
            )
        )

    except Exception:
        return ""

    offset = (
        dt.utcoffset()
        or
        timedelta(0)
    )

    total_minutes = int(
        offset.total_seconds()
        //
        60
    )

    sign = (
        "+"
        if total_minutes >= 0
        else "−"
    )

    total_minutes = abs(
        total_minutes
    )

    hh, mm = divmod(
        total_minutes,
        60,
    )

    hour = (
        dt.strftime("%I")
        .lstrip("0")
        or
        "0"
    )

    return (
        f"{hour}:"
        f"{dt.strftime('%M %p')} "
        f"UTC{sign}"
        f"{hh:02d}:"
        f"{mm:02d}"
    )


def first_parameter(
    parameters: dict[str, Any],
    *names: str,
) -> str:
    if not parameters:
        return ""

    lowered = {
        str(key).lower(): value
        for key, value
        in parameters.items()
    }

    for name in names:
        value = lowered.get(
            name.lower()
        )

        if isinstance(
            value,
            list,
        ):
            if value:
                return squish(
                    str(
                        value[0]
                    )
                )

        elif value is not None:
            return squish(
                str(value)
            )

    return ""


def all_parameter_values(
    parameters: dict[str, Any],
    name: str,
) -> list[str]:
    if not parameters:
        return []

    for key, value in parameters.items():

        if (
            str(key).lower()
            ==
            name.lower()
        ):
            if isinstance(
                value,
                list,
            ):
                return [
                    str(v)
                    for v in value
                ]

            if value is not None:
                return [
                    str(value)
                ]

    return []


def validate_environment() -> None:
    missing = []

    if not CONTACT_EMAIL:
        missing.append(
            "CONTACT_EMAIL"
        )

    if not DRY_RUN:

        for name, value in [
            (
                "X_CLIENT_ID",
                X_CLIENT_ID,
            ),
            (
                "X_CLIENT_SECRET",
                X_CLIENT_SECRET,
            ),
        ]:
            if not value:
                missing.append(
                    name
                )

        if not X_REFRESH_TOKEN:
            missing.append(
                "X_REFRESH_TOKEN"
            )

    if missing:
        raise SystemExit(
            "Missing required environment variables: "
            +
            ", ".join(missing)
        )

    db_parent = (
        Path(DB_PATH)
        .expanduser()
        .resolve()
        .parent
    )

    try:
        db_parent.mkdir(
            parents=True,
            exist_ok=True,
        )

    except Exception as exc:
        raise SystemExit(
            f"Cannot create DB directory "
            f"{db_parent}: {exc}"
        ) from exc


# =============================================================================
# HTTP
# =============================================================================


def build_http_session() -> requests.Session:
    session = requests.Session()

    session.headers.update(
        {
            "User-Agent":
                f"{BOT_NAME}/1.0 "
                f"({CONTACT_EMAIL})",

            "Accept-Encoding":
                "gzip, deflate",
        }
    )

    retry = Retry(
        total=3,
        connect=3,
        read=3,
        status=3,
        backoff_factor=0.8,
        status_forcelist=(
            429,
            500,
            502,
            503,
            504,
        ),
        allowed_methods=frozenset(
            {
                "GET",
                "HEAD",
            }
        ),
        respect_retry_after_header=True,
        raise_on_status=False,
    )

    adapter = HTTPAdapter(
        max_retries=retry,
        pool_connections=10,
        pool_maxsize=20,
    )

    session.mount(
        "https://",
        adapter,
    )

    return session


HTTP = build_http_session()


def http_get(
    url: str,
    *,
    params: Optional[
        dict[str, Any]
    ] = None,
    headers: Optional[
        dict[str, str]
    ] = None,
    timeout: tuple[
        int,
        int,
    ] = (
        8,
        30,
    ),
) -> requests.Response:

    response = HTTP.get(
        url,
        params=params,
        headers=headers,
        timeout=timeout,
    )

    response.raise_for_status()

    return response


# =============================================================================
# Durable SQLite state
# =============================================================================


class StateDB:

    def __init__(
        self,
        path: str,
    ):
        self.path = path

        self.conn = sqlite3.connect(
            path,
            timeout=30,
            isolation_level=None,
        )

        self.conn.execute(
            "PRAGMA journal_mode=WAL"
        )

        self.conn.execute(
            "PRAGMA synchronous=FULL"
        )

        self.conn.execute(
            "PRAGMA busy_timeout=30000"
        )

        self.conn.executescript(
            """
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
            """
        )

    def close(
        self,
    ) -> None:
        self.conn.close()

    def get_meta(
        self,
        key: str,
        default: str = "",
    ) -> str:

        row = self.conn.execute(
            "SELECT value "
            "FROM meta "
            "WHERE key=?",
            (
                key,
            ),
        ).fetchone()

        return (
            row[0]
            if row
            else default
        )

    def set_meta(
        self,
        key: str,
        value: str,
    ) -> None:

        self.conn.execute(
            "INSERT INTO meta(key,value) "
            "VALUES(?,?) "
            "ON CONFLICT(key) "
            "DO UPDATE SET "
            "value=excluded.value",
            (
                key,
                value,
            ),
        )

    def source_primed(
        self,
        source: str,
    ) -> bool:

        return (
            self.get_meta(
                f"primed:{source}"
            )
            ==
            "1"
        )

    def mark_source_primed(
        self,
        source: str,
    ) -> None:

        self.set_meta(
            f"primed:{source}",
            "1",
        )

    def exists(
        self,
        source: str,
        item_key: str,
    ) -> bool:

        row = self.conn.execute(
            "SELECT 1 "
            "FROM items "
            "WHERE source=? "
            "AND item_key=?",
            (
                source,
                item_key,
            ),
        ).fetchone()

        return bool(row)

    def mark_seen_without_post(
        self,
        source: str,
        item_key: str,
        status: str = "primed",
    ) -> None:

        now = iso_z(
            utcnow()
        )

        self.conn.execute(
            "INSERT OR IGNORE INTO items"
            "(source,item_key,first_seen_utc,"
            "status,updated_utc) "
            "VALUES(?,?,?,?,?)",
            (
                source,
                item_key,
                now,
                status,
                now,
            ),
        )

    def claim(
        self,
        source: str,
        item_key: str,
    ) -> bool:

        now = iso_z(
            utcnow()
        )

        try:
            self.conn.execute(
                "INSERT INTO items"
                "(source,item_key,first_seen_utc,"
                "status,updated_utc) "
                "VALUES(?,?,?,?,?)",
                (
                    source,
                    item_key,
                    now,
                    "posting",
                    now,
                ),
            )

            return True

        except sqlite3.IntegrityError:
            return False

    def set_status(
        self,
        source: str,
        item_key: str,
        status: str,
        *,
        tweet_id: str = "",
        error: str = "",
    ) -> None:

        self.conn.execute(
            "UPDATE items "
            "SET status=?, "
            "tweet_id=?, "
            "last_error=?, "
            "updated_utc=? "
            "WHERE source=? "
            "AND item_key=?",
            (
                status,
                tweet_id or None,
                error or None,
                iso_z(
                    utcnow()
                ),
                source,
                item_key,
            ),
        )

    def delete_item(
        self,
        source: str,
        item_key: str,
    ) -> None:

        self.conn.execute(
            "DELETE FROM items "
            "WHERE source=? "
            "AND item_key=?",
            (
                source,
                item_key,
            ),
        )

    def count_by_status(
        self,
    ) -> dict[str, int]:

        rows = self.conn.execute(
            "SELECT status, COUNT(*) "
            "FROM items "
            "GROUP BY status"
        ).fetchall()

        return {
            str(key): int(value)
            for key, value in rows
        }


# =============================================================================
# X OAuth 2.0
# =============================================================================


class XError(
    RuntimeError
):
    pass


class XRejectedError(
    XError
):
    pass


class XRetryableError(
    XError
):
    pass


class XAmbiguousError(
    XError
):
    pass


class XOAuth2:

    def __init__(
        self,
        db: StateDB,
    ):
        self.db = db

        self.client_id = (
            X_CLIENT_ID
        )

        self.client_secret = (
            X_CLIENT_SECRET
        )

        # Tokens already rotated by a running worker may exist in SQLite.
        self.db_access_token = (
            db.get_meta(
                "x:access_token"
            )
        )

        self.db_refresh_token = (
            db.get_meta(
                "x:refresh_token"
            )
        )

        # Tokens generated in the X Developer Console live in Render.
        self.env_access_token = (
            X_ACCESS_TOKEN
        )

        self.env_refresh_token = (
            X_REFRESH_TOKEN
        )

        # IMPORTANT:
        # Prefer the current Render access token on startup.
        #
        # The old version did the opposite and immediately forced a refresh,
        # which caused the exact refresh-token failure seen on Render.
        self.access_token = (
            self.env_access_token
            or
            self.db_access_token
        )

        self.refresh_token_value = (
            self.db_refresh_token
            or
            self.env_refresh_token
        )

        self.expires_at = 0.0

    def _token_auth(
        self,
    ) -> Optional[
        tuple[
            str,
            str,
        ]
    ]:

        if self.client_secret:
            return (
                self.client_id,
                self.client_secret,
            )

        return None

    def _store_tokens(
        self,
        payload: dict[
            str,
            Any,
        ],
    ) -> None:

        access = str(
            payload.get(
                "access_token"
            )
            or
            ""
        ).strip()

        refresh = str(
            payload.get(
                "refresh_token"
            )
            or
            ""
        ).strip()

        if not access:
            raise XRejectedError(
                "X token response had "
                "no access_token: "
                f"{payload!r}"
            )

        self.access_token = access

        self.db.set_meta(
            "x:access_token",
            access,
        )

        if refresh:
            self.refresh_token_value = (
                refresh
            )

            self.db.set_meta(
                "x:refresh_token",
                refresh,
            )

        expires_in = payload.get(
            "expires_in"
        )

        try:
            self.expires_at = (
                time.time()
                +
                max(
                    60,
                    int(expires_in),
                )
                -
                60
            )

        except Exception:
            self.expires_at = 0.0

    def refresh(
        self,
    ) -> None:

        # Refresh tokens can rotate.
        #
        # Try each known candidate once:
        # 1. SQLite's durable token
        # 2. current in-memory token
        # 3. Render's environment token
        #
        # This allows recovery if a token was regenerated in X while SQLite
        # still contains an older token.

        candidates: list[str] = []

        for token in (
            self.db_refresh_token,
            self.refresh_token_value,
            self.env_refresh_token,
        ):
            token = (
                token
                or
                ""
            ).strip()

            if (
                token
                and
                token not in candidates
            ):
                candidates.append(
                    token
                )

        if not candidates:
            raise XRejectedError(
                "No X OAuth2 refresh token "
                "is available."
            )

        auth = self._token_auth()

        last_rejection = ""

        for refresh in candidates:

            data = {
                "grant_type":
                    "refresh_token",

                "refresh_token":
                    refresh,
            }

            if not auth:
                data[
                    "client_id"
                ] = self.client_id

            try:
                response = requests.post(
                    X_TOKEN_URL,
                    data=data,
                    auth=auth,
                    headers={
                        "Content-Type":
                            "application/"
                            "x-www-form-urlencoded"
                    },
                    timeout=(
                        8,
                        30,
                    ),
                )

            except requests.RequestException as exc:
                raise XRetryableError(
                    "X token refresh "
                    "network failure: "
                    f"{exc}"
                ) from exc

            if (
                200
                <=
                response.status_code
                <
                300
            ):
                self._store_tokens(
                    response.json()
                )

                self.db_access_token = (
                    self.access_token
                )

                self.db_refresh_token = (
                    self.refresh_token_value
                )

                return

            if (
                response.status_code
                ==
                429
                or
                500
                <=
                response.status_code
                <
                600
            ):
                raise XRetryableError(
                    "X token refresh "
                    "temporary failure "
                    f"HTTP "
                    f"{response.status_code}: "
                    f"{response.text[:500]}"
                )

            last_rejection = (
                f"HTTP "
                f"{response.status_code}: "
                f"{response.text[:500]}"
            )

        raise XRejectedError(
            "All available X refresh tokens "
            "were rejected; last response "
            f"{last_rejection}"
        )

    def bearer(
        self,
        *,
        force_refresh: bool = False,
    ) -> str:

        if (
            force_refresh
            or
            not self.access_token
            or
            (
                self.expires_at
                and
                time.time()
                >=
                self.expires_at
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

        caller_headers = dict(
            kwargs.pop(
                "headers",
                {},
            )
            or
            {}
        )

        headers = dict(
            caller_headers
        )

        headers[
            "Authorization"
        ] = (
            f"Bearer {token}"
        )

        headers.setdefault(
            "User-Agent",
            f"{BOT_NAME}/1.0",
        )

        try:
            response = requests.request(
                method,
                url,
                headers=headers,
                timeout=kwargs.pop(
                    "timeout",
                    (
                        8,
                        45,
                    ),
                ),
                **kwargs,
            )

        except requests.RequestException as exc:

            if ambiguous_if_sent:
                raise XAmbiguousError(
                    "X create-post "
                    "network failure: "
                    f"{exc}"
                ) from exc

            raise XRetryableError(
                "X API network failure "
                "before post creation: "
                f"{exc}"
            ) from exc

        if (
            response.status_code
            ==
            401
            and
            retry_auth
        ):
            # Only refresh if X actually says the access token is unauthorized.
            self.refresh()

            return self.request(
                method,
                url,
                retry_auth=False,
                ambiguous_if_sent=
                    ambiguous_if_sent,
                headers=
                    caller_headers,
                **kwargs,
            )

        return response


class XPublisher:

    def __init__(
        self,
        db: StateDB,
    ):
        self.dry_run = (
            DRY_RUN
        )

        self.oauth = (
            None
            if self.dry_run
            else XOAuth2(db)
        )

    @staticmethod
    def _raise_for_prepost_response(
        response: requests.Response,
        operation: str,
    ) -> None:

        if (
            200
            <=
            response.status_code
            <
            300
        ):
            return

        msg = (
            f"{operation} "
            f"HTTP "
            f"{response.status_code}: "
            f"{response.text[:500]}"
        )

        if (
            response.status_code
            ==
            429
            or
            500
            <=
            response.status_code
            <
            600
        ):
            raise XRetryableError(
                msg
            )

        raise XRejectedError(
            msg
        )

    def upload_image(
        self,
        path: str,
    ) -> str:

        if self.dry_run:
            return "dry-run-media"

        assert self.oauth is not None

        suffix = (
            Path(path)
            .suffix
            .lower()
        )

        media_type = (
            "image/png"
            if suffix == ".png"
            else "image/jpeg"
        )

        total_bytes = (
            os.path.getsize(path)
        )

        if total_bytes <= 0:
            raise XRejectedError(
                "Generated tornado-warning "
                "image is empty"
            )

        if (
            total_bytes
            >
            5
            *
            1024
            *
            1024
        ):
            raise XRejectedError(
                "Generated tornado-warning "
                f"image is {total_bytes} bytes; "
                "X allows <= 5 MB"
            )

        filename = (
            Path(path).name
            or
            (
                "oneweather.png"
                if media_type == "image/png"
                else "oneweather.jpg"
            )
        )

        with open(
            path,
            "rb",
        ) as fh:

            response = self.oauth.request(
                "POST",
                X_MEDIA_URL,
                data={
                    "media_category":
                        "tweet_image"
                },
                files={
                    "media": (
                        filename,
                        fh,
                        media_type,
                    )
                },
            )

        self._raise_for_prepost_response(
            response,
            "X media upload",
        )

        try:
            data = (
                response.json()
                .get(
                    "data"
                )
                or
                {}
            )

            media_id = str(
                data.get(
                    "id"
                )
                or
                ""
            )

        except Exception as exc:
            raise XRetryableError(
                "Could not decode "
                "X media upload response: "
                f"{response.text[:300]}"
            ) from exc

        if not media_id:
            raise XRetryableError(
                "X media upload returned "
                "no id: "
                f"{response.text[:300]}"
            )

        processing = (
            data.get(
                "processing_info"
            )
            or
            {}
        )

        checks = 0

        while (
            processing
            and
            processing.get(
                "state"
            )
            not in {
                "succeeded",
                "failed",
            }
            and
            checks < 20
        ):

            wait = max(
                1,
                min(
                    10,
                    int(
                        processing.get(
                            "check_after_secs"
                        )
                        or
                        1
                    ),
                ),
            )

            time.sleep(
                wait
            )

            status = self.oauth.request(
                "GET",
                X_MEDIA_URL,
                params={
                    "command":
                        "STATUS",

                    "media_id":
                        media_id,
                },
            )

            self._raise_for_prepost_response(
                status,
                "X media STATUS",
            )

            try:
                processing = (
                    status.json()
                    .get(
                        "data"
                    )
                    or
                    {}
                ).get(
                    "processing_info"
                ) or {}

            except Exception as exc:
                raise XRetryableError(
                    "Could not decode "
                    "X media STATUS response: "
                    f"{status.text[:300]}"
                ) from exc

            checks += 1

        if (
            processing.get(
                "state"
            )
            ==
            "failed"
        ):
            raise XRejectedError(
                "X media processing "
                "failed: "
                f"{processing!r}"
            )

        if (
            processing
            and
            processing.get(
                "state"
            )
            !=
            "succeeded"
        ):
            raise XRetryableError(
                "X media processing "
                "did not finish: "
                f"{processing!r}"
            )

        return media_id

    def create_post(
        self,
        text: str,
        image_path: str = "",
    ) -> str:

        text = text.strip()

        if (
            len(text)
            >
            POST_TEXT_LIMIT
        ):
            text = truncate(
                text,
                POST_TEXT_LIMIT,
            )

        if self.dry_run:
            log.info(
                "[DRY RUN POST]\n"
                "%s%s",
                text,
                (
                    f"\n[image={image_path}]"
                    if image_path
                    else ""
                ),
            )

            return "dry-run-post"

        assert self.oauth is not None

        payload: dict[
            str,
            Any,
        ] = {
            "text":
                text
        }

        if image_path:
            payload[
                "media"
            ] = {
                "media_ids": [
                    self.upload_image(
                        image_path
                    )
                ]
            }

        response = self.oauth.request(
            "POST",
            X_POST_URL,
            json=payload,
            headers={
                "Content-Type":
                    "application/json"
            },
            ambiguous_if_sent=True,
        )

        if (
            response.status_code
            ==
            429
        ):
            raise XRetryableError(
                "X create-post "
                "rate limited: "
                f"{response.text[:500]}"
            )

        if (
            500
            <=
            response.status_code
            <
            600
        ):
            raise XAmbiguousError(
                "X create-post server error "
                f"HTTP {response.status_code}; "
                "outcome unknown: "
                f"{response.text[:500]}"
            )

        if not (
            200
            <=
            response.status_code
            <
            300
        ):
            raise XRejectedError(
                "X create-post rejected "
                f"HTTP "
                f"{response.status_code}: "
                f"{response.text[:500]}"
            )

        try:
            tweet_id = str(
                (
                    response.json()
                    .get(
                        "data"
                    )
                    or
                    {}
                ).get(
                    "id"
                )
                or
                ""
            )

        except Exception as exc:
            raise XAmbiguousError(
                "X returned success but "
                "its post response was "
                "unreadable: "
                f"{response.text[:500]}"
            ) from exc

        if not tweet_id:
            raise XAmbiguousError(
                "X returned success "
                "but no post id: "
                f"{response.text[:500]}"
            )

        return tweet_id

    def verify(
        self,
    ) -> str:

        if self.dry_run:
            return "dry-run"

        assert self.oauth is not None

        # IMPORTANT FIX:
        #
        # OLD VERSION:
        #     self.oauth.refresh()
        #
        # NEW VERSION:
        # Test the existing access token first.
        #
        # If X returns 401, XOAuth2.request() will refresh once automatically.
        response = self.oauth.request(
            "GET",
            X_ME_URL,
        )

        if not (
            200
            <=
            response.status_code
            <
            300
        ):
            raise XRejectedError(
                "X authenticated-user lookup "
                "failed HTTP "
                f"{response.status_code}: "
                f"{response.text[:500]}"
            )

        data = (
            response.json()
            .get(
                "data"
            )
            or
            {}
        )

        # If Render's environment access token worked, persist the matching
        # Render refresh token as the new durable SQLite baseline.
        if (
            self.oauth.access_token
            ==
            self.oauth.env_access_token
            and
            self.oauth.env_access_token
        ):
            self.oauth.db.set_meta(
                "x:access_token",
                self.oauth.env_access_token,
            )

            if (
                self.oauth.env_refresh_token
            ):
                self.oauth.db.set_meta(
                    "x:refresh_token",
                    self.oauth.env_refresh_token,
                )

                self.oauth.db_refresh_token = (
                    self.oauth.env_refresh_token
                )

        return str(
            data.get(
                "username"
            )
            or
            data.get(
                "name"
            )
            or
            data.get(
                "id"
            )
            or
            "unknown"
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
            "Retryable X failure "
            "for %s %s: %s",
            source,
            item_key[:16],
            exc,
        )

        return False

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

        return False

    except XAmbiguousError as exc:

        db.set_status(
            source,
            item_key,
            "ambiguous",
            error=repr(exc),
        )

        log.error(
            "Ambiguous X create result "
            "for %s %s; will NOT "
            "auto-retry: %s",
            source,
            item_key[:16],
            exc,
        )

        return False

    except Exception as exc:

        db.set_status(
            source,
            item_key,
            "ambiguous",
            error=repr(exc),
        )

        log.exception(
            "Unexpected X publish failure "
            "for %s %s; "
            "will NOT auto-retry",
            source,
            item_key[:16],
        )

        return False


# =============================================================================
# RSS parsing
# =============================================================================


@dataclass(
    frozen=True
)
class RSSItem:
    title: str
    link: str
    guid: str
    pub_date: str
    description_html: str

    @property
    def text(
        self,
    ) -> str:
        return html_to_text(
            self.description_html,
            preserve_lines=False,
        )

    @property
    def multiline_text(
        self,
    ) -> str:
        return html_to_text(
            self.description_html,
            preserve_lines=True,
        )

    @property
    def key(
        self,
    ) -> str:

        material = "\x1f".join(
            [
                self.guid,
                self.pub_date,
                self.title,
                self.link,
                self.description_html,
            ]
        )

        return sha256_text(
            material
        )

    @property
    def published(
        self,
    ) -> Optional[
        datetime
    ]:
        return parse_any_datetime(
            self.pub_date
        )


def _child_text_by_localname(
    node: ET.Element,
    local_name: str,
) -> str:

    for child in list(
        node
    ):
        tag = (
            child.tag
            .rsplit(
                "}",
                1,
            )[-1]
            .lower()
        )

        if (
            tag
            ==
            local_name.lower()
        ):
            return (
                "".join(
                    child.itertext()
                )
                .strip()
            )

    return ""


def fetch_rss(
    url: str,
) -> list[RSSItem]:

    response = http_get(
        url,
        headers={
            "Accept":
                "application/rss+xml, "
                "application/xml, "
                "text/xml, */*"
        },
    )

    root = ET.fromstring(
        response.content
    )

    items: list[
        RSSItem
    ] = []

    for node in root.iter():

        if (
            node.tag
            .rsplit(
                "}",
                1,
            )[-1]
            .lower()
            !=
            "item"
        ):
            continue

        title = (
            _child_text_by_localname(
                node,
                "title",
            )
        )

        link = (
            _child_text_by_localname(
                node,
                "link",
            )
        )

        guid = (
            _child_text_by_localname(
                node,
                "guid",
            )
        )

        pub_date = (
            _child_text_by_localname(
                node,
                "pubDate",
            )
        )

        description = (
            _child_text_by_localname(
                node,
                "description",
            )
        )

        items.append(
            RSSItem(
                title=squish(
                    title
                ),
                link=link.strip(),
                guid=guid.strip(),
                pub_date=
                    pub_date.strip(),
                description_html=
                    description,
            )
        )

    def sort_key(
        item: RSSItem,
    ) -> datetime:

        return (
            item.published
            or
            datetime(
                1970,
                1,
                1,
                tzinfo=timezone.utc,
            )
        )

    items.sort(
        key=sort_key
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

    items = fetch_rss(
        url
    )

    accepted = [
        item
        for item in items
        if (
            item_filter is None
            or
            item_filter(item)
        )
    ]

    if not db.source_primed(
        source
    ):

        for item in accepted:
            db.mark_seen_without_post(
                source,
                item.key,
            )

        db.mark_source_primed(
            source
        )

        log.info(
            "Primed %s with %d "
            "existing RSS item(s)",
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

        text = formatter(
            item
        )

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


# =============================================================================
# SPC
# =============================================================================


def spc_item_is_real(
    item: RSSItem,
    kind: str,
) -> bool:

    title = (
        item.title.lower()
    )

    description = (
        item.text.lower()
    )

    combined = (
        f"{title} "
        f"{description}"
    )

    negative_markers = (
        "no mesoscale discussions",
        "no watches are",
        "no watches in effect",
        "no severe thunderstorm watches",
        "no tornado watches",
        "no fire weather",
    )

    if any(
        marker in combined
        for marker
        in negative_markers
    ):
        return False

    if kind == "watch":

        if (
            "status report"
            in combined
        ):
            return False

        return (
            "watch"
            in combined
            and
            (
                "tornado"
                in combined
                or
                "severe thunderstorm"
                in combined
            )
        )

    if kind == "md":
        return (
            "mesoscale discussion"
            in combined
        )

    if kind == "convective":
        return (
            "outlook"
            in combined
        )

    if kind == "fire":
        return (
            "fire"
            in combined
            and
            "outlook"
            in combined
        )

    return True


def first_useful_summary(
    item: RSSItem,
    max_len: int = 150,
) -> str:

    summary = item.text

    if not summary:
        return ""

    if (
        item.title
        and
        summary.lower().startswith(
            item.title.lower()
        )
    ):
        summary = summary[
            len(item.title):
        ].lstrip(
            " :-–—"
        )

    return truncate(
        summary,
        max_len,
    )


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
        lower = (
            f"{item.title} "
            f"{item.text}"
        ).lower()

        heading = (
            "🌪️ SPC TORNADO WATCH"
            if
            "tornado" in lower
            else
            "⚠️ SPC SEVERE "
            "THUNDERSTORM WATCH"
        )

    summary = first_useful_summary(
        item,
        155,
    )

    return fit_post(
        [
            heading,
            item.title,
            summary,
            "Source: NOAA/NWS SPC",
        ],
        item.link,
    )


def poll_spc(
    db: StateDB,
    x: XPublisher,
) -> None:

    for (
        source,
        (
            url,
            kind,
        ),
    ) in SPC_FEEDS.items():

        try:
            process_rss_source(
                db,
                x,
                source=source,
                url=url,
                item_filter=(
                    lambda item, k=kind:
                        spc_item_is_real(
                            item,
                            k,
                        )
                ),
                formatter=(
                    lambda item, k=kind:
                        format_spc(
                            item,
                            k,
                        )
                ),
            )

        except Exception:
            log.exception(
                "SPC source failed: %s",
                source,
            )


# =============================================================================
# NHC / CPHC
# =============================================================================


def build_nhc_basin_sources(
    basin_name: str,
) -> list[
    tuple[
        str,
        str,
        str,
    ]
]:

    basin_code = (
        NHC_BASIN_CODES[
            basin_name
        ]
    )

    sources: list[
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
        sources.append(
            (
                f"nhc_tcp_"
                f"{basin_name}_"
                f"{wallet}",

                "https://"
                "www.nhc.noaa.gov/"
                f"xml/TCP"
                f"{basin_code}"
                f"{wallet}.xml",

                "tcp",
            )
        )

        sources.append(
            (
                f"nhc_tcu_"
                f"{basin_name}_"
                f"{wallet}",

                "https://"
                "www.nhc.noaa.gov/"
                f"xml/TCU"
                f"{basin_code}"
                f"{wallet}.xml",

                "tcu",
            )
        )

        if ENABLE_NHC_DISCUSSIONS:

            sources.append(
                (
                    f"nhc_tcd_"
                    f"{basin_name}_"
                    f"{wallet}",

                    "https://"
                    "www.nhc.noaa.gov/"
                    f"xml/TCD"
                    f"{basin_code}"
                    f"{wallet}.xml",

                    "tcd",
                )
            )

        if ENABLE_NHC_FORECAST_ADVISORIES:

            sources.append(
                (
                    f"nhc_tcm_"
                    f"{basin_name}_"
                    f"{wallet}",

                    "https://"
                    "www.nhc.noaa.gov/"
                    f"xml/TCM"
                    f"{basin_code}"
                    f"{wallet}.xml",

                    "tcm",
                )
            )

    return sources


NHC_BASIN_SOURCES = {
    basin:
        build_nhc_basin_sources(
            basin
        )
    for basin
    in NHC_BASIN_CODES
}


def nhc_item_is_real(
    item: RSSItem,
) -> bool:

    combined = (
        f"{item.title} "
        f"{item.text}"
    ).lower()

    empty_markers = (
        "no tropical cyclones",
        "there are no tropical cyclones",
        "no active tropical cyclones",
        "no tropical cyclone updates",
    )

    if (
        "tropical weather outlook"
        in combined
    ):
        return True

    return not any(
        marker in combined
        for marker
        in empty_markers
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

        heading = (
            "🌀 NHC TROPICAL "
            "WEATHER OUTLOOK"
        )

        summary = first_useful_summary(
            item,
            155,
        )

        return fit_post(
            [
                heading,
                item.title,
                summary,
                "Source: NOAA/NHC",
            ],
            item.link,
        )

    if kind == "tcp":

        heading = (
            "🌀 NHC PUBLIC ADVISORY"
        )

        raw = (
            item.multiline_text
        )

        location = _find_nhc_field(
            raw,
            "LOCATION",
        )

        winds = _find_nhc_field(
            raw,
            "MAXIMUM SUSTAINED WINDS",
        )

        movement = _find_nhc_field(
            raw,
            "PRESENT MOVEMENT",
        )

        pressure = _find_nhc_field(
            raw,
            "MINIMUM CENTRAL PRESSURE",
        )

        details = " | ".join(
            value
            for value in [
                winds,
                movement,
                pressure,
            ]
            if value
        )

        if not details:
            details = first_useful_summary(
                item,
                135,
            )

        return fit_post(
            [
                heading,
                item.title,
                location,
                details,
                "Source: NOAA/NHC",
            ],
            item.link,
        )

    if kind == "tcu":
        heading = (
            "🚨 NHC TROPICAL "
            "CYCLONE UPDATE"
        )

    elif kind == "tcd":
        heading = (
            "🌀 NHC FORECAST "
            "DISCUSSION"
        )

    else:
        heading = (
            "🌀 NHC FORECAST "
            "ADVISORY"
        )

    summary = first_useful_summary(
        item,
        145,
    )

    return fit_post(
        [
            heading,
            item.title,
            summary,
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
            item_filter=
                nhc_item_is_real,
            formatter=(
                lambda item, k=kind:
                    format_nhc(
                        item,
                        k,
                    )
            ),
        )

    except requests.HTTPError as exc:

        status = getattr(
            exc.response,
            "status_code",
            None,
        )

        if status in {
            404,
            410,
        }:

            if not db.source_primed(
                source
            ):
                db.mark_source_primed(
                    source
                )

            log.debug(
                "NHC wallet "
                "unavailable (%s): %s",
                status,
                url,
            )

            return

        raise


def _nhc_index_fingerprint(
    url: str,
) -> str:

    response = http_get(
        url,
        headers={
            "Accept":
                "application/rss+xml, "
                "application/xml, "
                "text/xml, */*"
        },
    )

    return hashlib.sha256(
        response.content
    ).hexdigest()


def _nhc_sweep_basin(
    db: StateDB,
    x: XPublisher,
    basin: str,
) -> bool:

    all_ok = True

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
            all_ok = False

            log.exception(
                "NHC product source "
                "failed: %s",
                source,
            )

    return all_ok


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
                item_filter=
                    nhc_item_is_real,
                formatter=(
                    lambda item:
                        format_nhc(
                            item,
                            "two",
                        )
                ),
            )

        except Exception:
            log.exception(
                "NHC Tropical "
                "Weather Outlook "
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
            f"nhc:index-fingerprint:"
            f"{basin}"
        )

        sweep_key = (
            f"nhc:last-full-sweep:"
            f"{basin}"
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
                    or
                    "0"
                )

            except ValueError:
                last_sweep = 0

            trigger_changed = (
                not old_fingerprint
                or
                fingerprint
                !=
                old_fingerprint
            )

            safety_sweep_due = (
                now_ts
                -
                last_sweep
                >=
                NHC_FULL_SWEEP_SECONDS
            )

            if (
                trigger_changed
                or
                safety_sweep_due
            ):

                reason = (
                    "index changed"
                    if
                    trigger_changed
                    else
                    "safety sweep"
                )

                log.info(
                    "NHC %s product "
                    "sweep (%s)",
                    basin,
                    reason,
                )

                sweep_ok = (
                    _nhc_sweep_basin(
                        db,
                        x,
                        basin,
                    )
                )

                if sweep_ok:
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
                        "NHC %s sweep "
                        "incomplete; "
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
                "NHC basin index/"
                "sweep failed: %s",
                basin,
            )


# =============================================================================
# NWS alerts
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
        and
        pages < 25
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

        page_features = (
            data.get(
                "features"
            )
            or
            []
        )

        if isinstance(
            page_features,
            list,
        ):
            features.extend(
                page_features
            )

        pagination = (
            data.get(
                "pagination"
            )
            or
            {}
        )

        next_url = (
            pagination.get(
                "next"
            )
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

    if (
        pages >= 25
        and
        url
    ):
        log.error(
            "NWS alerts pagination "
            "exceeded safety cap; "
            "results may be incomplete"
        )

    return features


def alert_vtec_actions(
    props: dict[
        str,
        Any,
    ],
) -> set[str]:

    parameters = (
        props.get(
            "parameters"
        )
        or
        {}
    )

    actions: set[str] = (
        set()
    )

    for value in all_parameter_values(
        parameters,
        "VTEC",
    ):

        actions.update(
            re.findall(
                r"/[A-Z]\."
                r"(NEW|CON|EXT|EXA|"
                r"EXB|UPG|CAN|EXP|COR)"
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

    if actions:
        return (
            "NEW"
            in actions
        )

    return (
        str(
            props.get(
                "messageType",
                "",
            )
        ).lower()
        ==
        "alert"
    )


def nws_alert_key(
    feature: dict[
        str,
        Any,
    ],
) -> str:

    props = (
        feature.get(
            "properties"
        )
        or
        {}
    )

    raw_id = (
        props.get(
            "id"
        )
        or
        feature.get(
            "id"
        )
        or
        props.get(
            "@id"
        )
    )

    if raw_id:
        return sha256_text(
            str(raw_id)
        )

    material = "\x1f".join(
        str(
            props.get(key)
            or
            ""
        )
        for key in (
            "event",
            "sent",
            "headline",
            "areaDesc",
            "expires",
        )
    )

    return sha256_text(
        material
    )


def format_tornado_warning(
    feature: dict[
        str,
        Any,
    ],
) -> str:

    props = (
        feature.get(
            "properties"
        )
        or
        {}
    )

    params = (
        props.get(
            "parameters"
        )
        or
        {}
    )

    headline = squish(
        props.get(
            "headline"
        )
    )

    nws_headline = (
        first_parameter(
            params,
            "NWSheadline",
        )
    )

    area = truncate(
        squish(
            props.get(
                "areaDesc"
            )
        ),
        100,
    )

    expires = format_offset_time(
        props.get(
            "expires"
        )
    )

    sender = squish(
        props.get(
            "senderName"
        )
    )

    detection = (
        first_parameter(
            params,
            "tornadoDetection",
        )
    )

    damage = (
        first_parameter(
            params,
            "tornadoDamageThreat",
        )
    )

    emergency = (
        "TORNADO EMERGENCY"
        in
        (
            nws_headline
            or
            headline
        ).upper()
    )

    heading = (
        "🚨🚨 TORNADO EMERGENCY"
        if emergency
        else
        "🚨 TORNADO WARNING"
    )

    details = []

    if detection:
        details.append(
            detection.title()
        )

    if (
        damage
        and
        damage.lower()
        not in {
            "base",
            "none",
        }
    ):
        details.append(
            "Damage threat: "
            f"{damage.title()}"
        )

    official_headline = (
        nws_headline
        or
        headline
    )

    if official_headline.upper().startswith(
        "TORNADO WARNING"
    ):
        official_headline = ""

    return fit_post(
        [
            heading,
            area,
            (
                f"Until {expires}"
                if expires
                else ""
            ),
            " | ".join(
                details
            ),
            truncate(
                official_headline,
                105,
            ),
            (
                f"Issued by {sender}"
                if sender
                else
                "Source: NWS"
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
        feature.get(
            "properties"
        )
        or
        {}
    )

    event = (
        squish(
            props.get(
                "event"
            )
        )
        or
        "Winter Weather Alert"
    )

    area = truncate(
        squish(
            props.get(
                "areaDesc"
            )
        ),
        105,
    )

    expires = format_offset_time(
        props.get(
            "expires"
        )
    )

    headline = squish(
        props.get(
            "headline"
        )
    )

    sender = squish(
        props.get(
            "senderName"
        )
    )

    icon = "❄️"

    if (
        "ice"
        in event.lower()
        or
        "freezing"
        in event.lower()
    ):
        icon = "🧊"

    elif (
        "blizzard"
        in event.lower()
    ):
        icon = "🌨️"

    elif (
        "cold"
        in event.lower()
        or
        "wind chill"
        in event.lower()
    ):
        icon = "🥶"

    return fit_post(
        [
            f"{icon} "
            f"{event.upper()}",
            area,
            (
                f"Until {expires}"
                if expires
                else ""
            ),
            truncate(
                headline,
                110,
            ),
            (
                f"Issued by {sender}"
                if sender
                else
                "Source: NWS"
            ),
        ]
    )


# =============================================================================
# Tornado-warning radar image
# =============================================================================


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

    radius = (
        6378137.0
    )

    x = (
        radius
        *
        math.radians(
            lon
        )
    )

    y = (
        radius
        *
        math.log(
            math.tan(
                math.pi
                /
                4.0
                +
                math.radians(
                    lat
                )
                /
                2.0
            )
        )
    )

    return (
        x,
        y,
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

    if not geometry:
        return []

    gtype = (
        geometry.get(
            "type"
        )
    )

    coords = (
        geometry.get(
            "coordinates"
        )
    )

    if not isinstance(
        coords,
        list,
    ):
        return []

    if (
        gtype == "Polygon"
        and
        coords
    ):
        return (
            [
                coords[0]
            ]
            if isinstance(
                coords[0],
                list,
            )
            else
            []
        )

    if (
        gtype
        ==
        "MultiPolygon"
    ):
        rings = []

        for polygon in coords:

            if (
                isinstance(
                    polygon,
                    list,
                )
                and
                polygon
                and
                isinstance(
                    polygon[0],
                    list,
                )
            ):
                rings.append(
                    polygon[0]
                )

        return rings

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

    points: list[
        tuple[
            float,
            float,
        ]
    ] = []

    for ring in rings:

        for coord in ring:

            if (
                not isinstance(
                    coord,
                    (
                        list,
                        tuple,
                    ),
                )
                or
                len(coord) < 2
            ):
                continue

            lon = float(
                coord[0]
            )

            lat = float(
                coord[1]
            )

            points.append(
                lonlat_to_web_mercator(
                    lon,
                    lat,
                )
            )

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
        minx
        +
        maxx
    ) / 2.0

    cy = (
        miny
        +
        maxy
    ) / 2.0

    raw_w = max(
        maxx - minx,
        120_000.0,
    )

    raw_h = max(
        maxy - miny,
        90_000.0,
    )

    raw_w *= 1.65
    raw_h *= 1.65

    target_aspect = (
        width
        /
        height
    )

    if (
        raw_w / raw_h
        <
        target_aspect
    ):
        raw_w = (
            raw_h
            *
            target_aspect
        )

    else:
        raw_h = (
            raw_w
            /
            target_aspect
        )

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
                for value
                in bbox
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

    ctype = (
        response.headers.get(
            "Content-Type",
            "",
        )
    )

    if (
        "image"
        not in ctype.lower()
        and
        not response.content.startswith(
            b"\x89PNG"
        )
    ):
        raise RuntimeError(
            "Map export did not "
            "return an image "
            f"({ctype}): "
            f"{response.text[:200]}"
        )

    return (
        Image.open(
            io.BytesIO(
                response.content
            )
        )
        .convert(
            "RGBA"
        )
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

    points: list[
        tuple[
            int,
            int,
        ]
    ] = []

    for coord in ring:

        if (
            not isinstance(
                coord,
                (
                    list,
                    tuple,
                ),
            )
            or
            len(coord) < 2
        ):
            continue

        mx, my = (
            lonlat_to_web_mercator(
                float(
                    coord[0]
                ),
                float(
                    coord[1]
                ),
            )
        )

        px = int(
            round(
                (
                    mx - minx
                )
                /
                (
                    maxx - minx
                )
                *
                (
                    width - 1
                )
            )
        )

        py = int(
            round(
                (
                    maxy - my
                )
                /
                (
                    maxy - miny
                )
                *
                (
                    height - 1
                )
            )
        )

        points.append(
            (
                px,
                py,
            )
        )

    return points


def load_font(
    size: int,
    bold: bool = False,
) -> ImageFont.ImageFont:

    candidates = []

    if bold:
        candidates.extend(
            [
                "/usr/share/fonts/"
                "truetype/dejavu/"
                "DejaVuSans-Bold.ttf",

                "/usr/share/fonts/"
                "truetype/liberation2/"
                "LiberationSans-Bold.ttf",

                "/System/Library/Fonts/"
                "Supplemental/"
                "Arial Bold.ttf",
            ]
        )

    else:
        candidates.extend(
            [
                "/usr/share/fonts/"
                "truetype/dejavu/"
                "DejaVuSans.ttf",

                "/usr/share/fonts/"
                "truetype/liberation2/"
                "LiberationSans-Regular.ttf",

                "/System/Library/Fonts/"
                "Supplemental/"
                "Arial.ttf",
            ]
        )

    for path in candidates:

        try:
            return ImageFont.truetype(
                path,
                size=size,
            )

        except Exception:
            continue

    try:
        return ImageFont.load_default(
            size=size
        )

    except TypeError:
        return (
            ImageFont.load_default()
        )


def invert_visible_reference_layer(
    layer: Image.Image,
) -> Image.Image:

    layer = layer.convert(
        "RGBA"
    )

    alpha = layer.getchannel(
        "A"
    )

    inverted = ImageOps.invert(
        layer.convert(
            "RGB"
        )
    )

    inverted.putalpha(
        alpha
    )

    return inverted


def build_tornado_warning_image(
    feature: dict[
        str,
        Any,
    ],
) -> str:

    rings = warning_rings(
        feature.get(
            "geometry"
        )
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

    references = export_map_image(
        REFERENCE_EXPORT_URL,
        bbox,
        map_w,
        map_h,
        layers="show:2,3",
    )

    references = (
        invert_visible_reference_layer(
            references
        )
    )

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

    base.alpha_composite(
        radar
    )

    base.alpha_composite(
        references
    )

    overlay = Image.new(
        "RGBA",
        base.size,
        (
            0,
            0,
            0,
            0,
        ),
    )

    od = ImageDraw.Draw(
        overlay,
        "RGBA",
    )

    for ring in rings:

        pts = map_ring_to_pixels(
            ring,
            bbox,
            map_w,
            map_h,
        )

        if len(pts) >= 3:

            od.polygon(
                pts,
                fill=(
                    255,
                    28,
                    28,
                    58,
                ),
            )

            od.line(
                pts
                +
                [
                    pts[0]
                ],
                fill=(
                    255,
                    255,
                    255,
                    240,
                ),
                width=10,
                joint="curve",
            )

            od.line(
                pts
                +
                [
                    pts[0]
                ],
                fill=(
                    235,
                    32,
                    32,
                    255,
                ),
                width=6,
                joint="curve",
            )

    base.alpha_composite(
        overlay
    )

    props = (
        feature.get(
            "properties"
        )
        or
        {}
    )

    params = (
        props.get(
            "parameters"
        )
        or
        {}
    )

    headline = (
        first_parameter(
            params,
            "NWSheadline",
        )
        or
        squish(
            props.get(
                "headline"
            )
        )
    )

    area = squish(
        props.get(
            "areaDesc"
        )
    )

    expires = format_offset_time(
        props.get(
            "expires"
        )
    )

    detection = first_parameter(
        params,
        "tornadoDetection",
    )

    damage = first_parameter(
        params,
        "tornadoDamageThreat",
    )

    sender = squish(
        props.get(
            "senderName"
        )
    )

    emergency = (
        "TORNADO EMERGENCY"
        in
        headline.upper()
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

    title_font = load_font(
        48,
        bold=True,
    )

    body_font = load_font(
        26,
        bold=False,
    )

    small_font = load_font(
        20,
        bold=False,
    )

    title = (
        "TORNADO EMERGENCY"
        if emergency
        else
        "TORNADO WARNING"
    )

    draw.text(
        (
            30,
            20,
        ),
        title,
        font=title_font,
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
            area,
            92,
        ),
        font=body_font,
        fill=(
            245,
            245,
            245,
            255,
        ),
    )

    detail_bits = []

    if expires:
        detail_bits.append(
            f"Until {expires}"
        )

    if detection:
        detail_bits.append(
            detection.title()
        )

    if (
        damage
        and
        damage.lower()
        not in {
            "base",
            "none",
        }
    ):
        detail_bits.append(
            "Damage threat: "
            f"{damage.title()}"
        )

    draw.text(
        (
            30,
            126,
        ),
        "  •  ".join(
            detail_bits
        ),
        font=body_font,
        fill=(
            220,
            225,
            230,
            255,
        ),
    )

    footer = (
        "NOAA/NWS MRMS radar "
        "• NWS warning polygon"
        +
        (
            f" • {sender}"
            if sender
            else ""
        )
    )

    draw.rectangle(
        (
            0,
            canvas.height - 36,
            map_w,
            canvas.height,
        ),
        fill=(
            8,
            9,
            10,
            210,
        ),
    )

    draw.text(
        (
            20,
            canvas.height - 30,
        ),
        truncate(
            footer,
            110,
        ),
        font=small_font,
        fill=(
            238,
            238,
            238,
            255,
        ),
    )

    tmp = tempfile.NamedTemporaryFile(
        prefix="oneweather_tor_",
        suffix=".jpg",
        delete=False,
    )

    tmp.close()

    canvas.convert(
        "RGB"
    ).save(
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

    source = (
        "nws_alerts"
    )

    now = utcnow()

    previous = parse_any_datetime(
        db.get_meta(
            "nws:last_success"
        )
    )

    if previous is None:

        start = (
            now
            -
            timedelta(
                minutes=15
            )
        )

    else:

        floor = (
            now
            -
            timedelta(
                minutes=
                    NWS_QUERY_BACKFILL_MAX_MINUTES
            )
        )

        start = max(
            previous
            -
            timedelta(
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

        props = (
            feature.get(
                "properties"
            )
            or
            {}
        )

        event = squish(
            props.get(
                "event"
            )
        )

        if (
            event
            ==
            "Tornado Warning"
        ):
            relevant.append(
                (
                    feature,
                    "tornado",
                )
            )

        elif (
            event
            in
            WINTER_ALERT_EVENTS
        ):
            relevant.append(
                (
                    feature,
                    "winter",
                )
            )

    relevant.sort(
        key=lambda pair:
            (
                parse_any_datetime(
                    (
                        pair[0]
                        .get(
                            "properties"
                        )
                        or
                        {}
                    ).get(
                        "sent"
                    )
                )
                or
                datetime(
                    1970,
                    1,
                    1,
                    tzinfo=
                        timezone.utc,
                )
            )
    )

    if not db.source_primed(
        source
    ):

        for (
            feature,
            _kind,
        ) in relevant:

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
            "Primed %s with %d "
            "recent relevant alert(s)",
            source,
            len(relevant),
        )

        return

    for (
        feature,
        kind,
    ) in relevant:

        props = (
            feature.get(
                "properties"
            )
            or
            {}
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

        sent = props.get(
            "sent"
        )

        age = age_minutes(
            sent
        )

        max_age = (
            TORNADO_MAX_POST_AGE_MINUTES
            if kind == "tornado"
            else
            WINTER_ALERT_MAX_POST_AGE_MINUTES
        )

        if (
            age is not None
            and
            age > max_age
        ):
            db.mark_seen_without_post(
                source,
                key,
                status="stale",
            )

            log.info(
                "Skipping stale %s "
                "alert (%.1f minutes old)",
                kind,
                age,
            )

            continue

        image_path = ""

        try:

            if kind == "tornado":

                text = (
                    format_tornado_warning(
                        feature
                    )
                )

                try:
                    image_path = (
                        build_tornado_warning_image(
                            feature
                        )
                    )

                except Exception:
                    log.exception(
                        "Could not build "
                        "tornado-warning radar "
                        "image; posting text only"
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
# WPC ERO — official NOAA ArcGIS service
# =============================================================================


@dataclass(
    frozen=True
)
class EROProduct:
    day: int
    issued: str
    valid: str
    headline: str
    url: str

    @property
    def key(
        self,
    ) -> str:

        return sha256_text(
            f"{self.day}|"
            f"{self.issued}|"
            f"{self.valid}|"
            f"{self.headline}"
        )


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

    url = (
        f"{mapserver}/"
        f"{layer}/query"
    )

    response = http_get(
        url,
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

    if payload.get(
        "error"
    ):
        raise RuntimeError(
            "NOAA ArcGIS query "
            f"error for layer {layer}: "
            f"{payload['error']!r}"
        )

    features = (
        payload.get(
            "features"
        )
        or
        []
    )

    return [
        dict(
            feature.get(
                "attributes"
            )
            or
            {}
        )
        for feature
        in features
    ]


def _first_nonempty(
    values: Iterable[Any],
) -> str:

    for value in values:

        text = squish(
            str(
                value
                or
                ""
            )
        )

        if text:
            return text

    return ""


def parse_wpc_ero(
    day: int,
) -> EROProduct:

    if day not in (
        1,
        2,
        3,
        4,
        5,
    ):
        raise ValueError(
            "Invalid WPC ERO day "
            f"{day}"
        )

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
            "NOAA WPC ERO Day "
            f"{day} GIS layer "
            "returned no features"
        )

    issued = _first_nonempty(
        attribute.get(
            "issue_time"
        )
        for attribute
        in attrs
    )

    valid = _first_nonempty(
        attribute.get(
            "valid_time"
        )
        for attribute
        in attrs
    )

    if not valid:

        start = _first_nonempty(
            attribute.get(
                "start_time"
            )
            for attribute
            in attrs
        )

        end = _first_nonempty(
            attribute.get(
                "end_time"
            )
            for attribute
            in attrs
        )

        valid = " to ".join(
            value
            for value in (
                start,
                end,
            )
            if value
        )

    if not issued:

        raw = max(
            (
                attribute.get(
                    "idp_ingestdate"
                )
                or
                0
                for attribute
                in attrs
            ),
            default=0,
        )

        if raw:

            try:
                issued = iso_z(
                    datetime.fromtimestamp(
                        float(raw)
                        /
                        1000.0,
                        tz=timezone.utc,
                    )
                )

            except Exception:
                issued = str(raw)

    if not issued:
        raise ValueError(
            "NOAA WPC ERO Day "
            f"{day} GIS layer "
            "had no issue timestamp"
        )

    best_name = ""
    best_rank = -1

    ranks = {
        "marginal": 1,
        "slight": 2,
        "moderate": 3,
        "high": 4,
    }

    for attribute in attrs:

        outlook = squish(
            str(
                attribute.get(
                    "outlook"
                )
                or
                ""
            )
        )

        dn = attribute.get(
            "dn"
        )

        try:
            rank = int(
                float(dn)
            )

        except Exception:

            lower = outlook.lower()

            rank = max(
                (
                    rank_value
                    for (
                        rank_name,
                        rank_value,
                    )
                    in ranks.items()
                    if
                    rank_name
                    in lower
                ),
                default=0,
            )

        if rank > best_rank:
            best_rank = rank
            best_name = outlook

    headline = (
        f"Highest risk: {best_name}"
        if best_name
        else
        "Official WPC "
        "excessive-rainfall "
        "outlook updated."
    )

    return EROProduct(
        day=day,
        issued=issued,
        valid=valid,
        headline=headline,
        url=WPC_ERO_PUBLIC_URL,
    )


def format_ero(
    product: EROProduct,
) -> str:

    return fit_post(
        [
            "🌧️ WPC DAY "
            f"{product.day} "
            "EXCESSIVE RAINFALL "
            "OUTLOOK",

            truncate(
                product.headline,
                135,
            ),

            (
                "Valid: "
                f"{truncate(product.valid, 90)}"
                if product.valid
                else ""
            ),

            "Issued/updated: "
            f"{truncate(product.issued, 65)}",

            "Source: NOAA/NWS WPC",
        ],
        product.url,
    )


def poll_wpc_ero(
    db: StateDB,
    x: XPublisher,
) -> None:

    days = [
        1,
        2,
        3,
    ]

    if ENABLE_WPC_DAY4_DAY5_ERO:
        days += [
            4,
            5,
        ]

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

                continue

            if not db.exists(
                source,
                product.key,
            ):
                publish_once(
                    db,
                    x,
                    source,
                    product.key,
                    format_ero(
                        product
                    ),
                )

        except Exception:
            log.exception(
                "WPC ERO Day %d "
                "poll failed",
                day,
            )


# =============================================================================
# WPC winter — api.weather.gov + NOAA GIS
# =============================================================================


@dataclass(
    frozen=True
)
class WPCWinterDiscussion:
    identity: str
    issued_line: str
    valid_line: str
    headline: str

    @property
    def key(
        self,
    ) -> str:
        return sha256_text(
            self.identity
        )


def parse_wpc_heavy_snow_discussion(
) -> WPCWinterDiscussion:

    response = http_get(
        WPC_HSD_API_URL,
        headers={
            "Accept":
                "application/geo+json,"
                "application/ld+json,"
                "application/json"
        },
        timeout=(
            8,
            35,
        ),
    )

    data = response.json()

    product_text = str(
        data.get(
            "productText"
        )
        or
        data.get(
            "product_text"
        )
        or
        ""
    )

    if not product_text:
        raise ValueError(
            "api.weather.gov "
            "returned no QPFHSD "
            "productText"
        )

    if (
        "QPFHSD"
        not in product_text
        and
        "Heavy Snow"
        not in product_text
        and
        "heavy snow"
        not in product_text
    ):
        raise ValueError(
            "Latest QPF/HSD product "
            "did not identify as the "
            "heavy snow/icing discussion"
        )

    issuance = squish(
        str(
            data.get(
                "issuanceTime"
            )
            or
            data.get(
                "issuance_time"
            )
            or
            ""
        )
    )

    lines = [
        line.strip()
        for line
        in product_text.splitlines()
        if line.strip()
    ]

    valid_line = next(
        (
            squish(
                line[5:]
            )
            for line in lines
            if
            line.lower().startswith(
                "valid "
            )
        ),
        "",
    )

    headline = ""

    compact = re.sub(
        r"\s+",
        " ",
        product_text,
    )

    hm = re.search(
        r"\.\.\.\s*"
        r"(.*?)"
        r"\s*\.\.\.",
        compact,
    )

    if hm:
        headline = squish(
            hm.group(1)
        )

    if not issuance:

        for (
            index,
            line,
        ) in enumerate(
            lines
        ):
            if (
                "Weather Prediction Center"
                in line
                and
                index + 1
                <
                len(lines)
            ):
                issuance = squish(
                    lines[
                        index + 1
                    ]
                )

                break

    product_id = squish(
        str(
            data.get(
                "id"
            )
            or
            data.get(
                "@id"
            )
            or
            ""
        )
    )

    identity = (
        product_id
        or
        (
            f"{issuance}|"
            f"{valid_line}|"
            f"{headline}|"
            f"{sha256_text(product_text)}"
        )
    )

    return WPCWinterDiscussion(
        identity=identity,
        issued_line=issuance,
        valid_line=valid_line,
        headline=headline,
    )


def format_wpc_heavy_snow(
    disc: WPCWinterDiscussion,
) -> str:

    return fit_post(
        [
            "❄️ WPC PROBABILISTIC "
            "HEAVY SNOW & ICE "
            "DISCUSSION",

            truncate(
                disc.headline,
                125,
            ),

            (
                "Valid: "
                f"{truncate(disc.valid_line, 90)}"
                if disc.valid_line
                else ""
            ),

            (
                "Issued: "
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

    # Layer IDs in NOAA's official WPC probabilistic-winter service:
    #
    # Day 1:
    # 1 >= 4" snow
    # 2 >= 8" snow
    # 3 >= 12" snow
    # 4 >= .25" ice
    #
    # Day 2:
    # 6,7,8,9
    #
    # Day 3:
    # 11,12,13,14

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

    for (
        day,
        layers,
    ) in day_layers.items():

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
            attribute.get(
                "issue_time"
            )
            for attribute
            in attrs
        )

        valid = _first_nonempty(
            attribute.get(
                "valid_time"
            )
            for attribute
            in attrs
        )

        if not issue:

            raw = max(
                (
                    attribute.get(
                        "idp_ingestdate"
                    )
                    or
                    0
                    for attribute
                    in attrs
                ),
                default=0,
            )

            if raw:

                try:
                    issue = iso_z(
                        datetime.fromtimestamp(
                            float(raw)
                            /
                            1000.0,
                            tz=timezone.utc,
                        )
                    )

                except Exception:
                    issue = str(raw)

        if issue:

            update = (
                issue
                +
                (
                    f" | Valid {valid}"
                    if valid
                    else ""
                )
            )

            out.append(
                (
                    day,
                    update,
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

        except requests.HTTPError as exc:

            if (
                getattr(
                    exc.response,
                    "status_code",
                    None,
                )
                ==
                404
            ):
                log.info(
                    "No current WPC heavy "
                    "snow/ice discussion"
                )

            else:
                log.exception(
                    "WPC heavy snow/ice "
                    "discussion poll failed"
                )

        except Exception:
            log.exception(
                "WPC heavy snow/ice "
                "discussion poll failed"
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
                        f"day{day}|"
                        f"{update}"
                    ),
                )
                for (
                    day,
                    update,
                )
                in updates
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
                    "Primed %s with %d "
                    "active package "
                    "timestamp(s)",
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
                            "❄️ WPC DAY "
                            f"{day} "
                            "WINTER WEATHER "
                            "FORECAST UPDATED",

                            update,

                            "Probabilistic snow "
                            "and freezing-rain "
                            "guidance.",

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
                "WPC winter-package "
                "poll failed"
            )


# =============================================================================
# Local X OAuth authorization helper
# =============================================================================


def _pkce_verifier_and_challenge(
) -> tuple[
    str,
    str,
]:

    verifier = (
        base64.urlsafe_b64encode(
            secrets.token_bytes(
                64
            )
        )
        .decode(
            "ascii"
        )
        .rstrip("=")
    )

    digest = hashlib.sha256(
        verifier.encode(
            "ascii"
        )
    ).digest()

    challenge = (
        base64.urlsafe_b64encode(
            digest
        )
        .decode(
            "ascii"
        )
        .rstrip("=")
    )

    return (
        verifier,
        challenge,
    )


def _oauth_token_exchange(
    data: dict[
        str,
        str,
    ],
) -> dict[
    str,
    Any,
]:

    if not X_CLIENT_ID:
        raise SystemExit(
            "Set X_CLIENT_ID before "
            "running --authorize"
        )

    auth: Optional[
        tuple[
            str,
            str,
        ]
    ] = None

    payload = dict(
        data
    )

    if X_CLIENT_SECRET:
        auth = (
            X_CLIENT_ID,
            X_CLIENT_SECRET,
        )

    else:
        payload[
            "client_id"
        ] = X_CLIENT_ID

    response = requests.post(
        X_TOKEN_URL,
        data=payload,
        auth=auth,
        headers={
            "Content-Type":
                "application/"
                "x-www-form-urlencoded"
        },
        timeout=(
            8,
            30,
        ),
    )

    if not (
        200
        <=
        response.status_code
        <
        300
    ):
        raise SystemExit(
            "X OAuth token exchange "
            "failed HTTP "
            f"{response.status_code}: "
            f"{response.text[:1000]}"
        )

    return response.json()


def authorize_x_interactively(
) -> int:

    if not X_CLIENT_ID:
        raise SystemExit(
            "Set X_CLIENT_ID first. "
            "For an Automated App/Bot "
            "also set X_CLIENT_SECRET."
        )

    verifier, challenge = (
        _pkce_verifier_and_challenge()
    )

    state = secrets.token_urlsafe(
        32
    )

    query = urlencode(
        {
            "response_type":
                "code",

            "client_id":
                X_CLIENT_ID,

            "redirect_uri":
                X_REDIRECT_URI,

            "scope":
                " ".join(
                    X_SCOPES
                ),

            "state":
                state,

            "code_challenge":
                challenge,

            "code_challenge_method":
                "S256",
        }
    )

    auth_url = (
        f"{X_AUTHORIZE_URL}?"
        f"{query}"
    )

    parsed_redirect = urlparse(
        X_REDIRECT_URI
    )

    code = ""

    print(
        "\nOpen this X authorization "
        "URL in a browser while "
        "logged into the account "
        "OneWeather will post from:\n"
    )

    print(
        auth_url
    )

    print()

    if (
        parsed_redirect.hostname
        in {
            "127.0.0.1",
            "localhost",
        }
        and
        parsed_redirect.scheme
        ==
        "http"
    ):

        port = (
            parsed_redirect.port
            or
            80
        )

        callback_path = (
            parsed_redirect.path
            or
            "/"
        )

        result: dict[
            str,
            str,
        ] = {}

        class CallbackHandler(
            BaseHTTPRequestHandler
        ):

            def do_GET(
                self,
            ) -> None:

                parsed = urlparse(
                    self.path
                )

                params = parse_qs(
                    parsed.query
                )

                if (
                    parsed.path
                    !=
                    callback_path
                ):
                    self.send_response(
                        404
                    )

                    self.end_headers()

                    return

                result[
                    "state"
                ] = (
                    params.get(
                        "state"
                    )
                    or
                    [
                        ""
                    ]
                )[0]

                result[
                    "code"
                ] = (
                    params.get(
                        "code"
                    )
                    or
                    [
                        ""
                    ]
                )[0]

                result[
                    "error"
                ] = (
                    params.get(
                        "error"
                    )
                    or
                    [
                        ""
                    ]
                )[0]

                ok = bool(
                    result[
                        "code"
                    ]
                    and
                    result[
                        "state"
                    ]
                    ==
                    state
                )

                self.send_response(
                    200
                    if ok
                    else
                    400
                )

                self.send_header(
                    "Content-Type",
                    "text/plain; "
                    "charset=utf-8",
                )

                self.end_headers()

                if ok:
                    self.wfile.write(
                        b"OneWeather authorization "
                        b"received. You can return "
                        b"to Terminal."
                    )

                else:
                    self.wfile.write(
                        b"Authorization failed or "
                        b"state did not match. "
                        b"Return to Terminal."
                    )

            def log_message(
                self,
                _format: str,
                *_args: Any,
            ) -> None:
                return

        server = HTTPServer(
            (
                parsed_redirect.hostname,
                port,
            ),
            CallbackHandler,
        )

        server.timeout = 180

        try:

            try:
                webbrowser.open(
                    auth_url
                )

            except Exception:
                pass

            server.handle_request()

        finally:
            server.server_close()

        if result.get(
            "error"
        ):
            raise SystemExit(
                "X authorization "
                "returned error: "
                f"{result['error']}"
            )

        if (
            result.get(
                "state"
            )
            !=
            state
        ):
            raise SystemExit(
                "X OAuth state mismatch "
                "or callback was not received"
            )

        code = result.get(
            "code",
            "",
        )

    else:

        try:
            webbrowser.open(
                auth_url
            )

        except Exception:
            pass

        callback = input(
            "After authorizing, paste "
            "the FULL callback URL here: "
        ).strip()

        params = parse_qs(
            urlparse(
                callback
            ).query
        )

        if (
            (
                params.get(
                    "state"
                )
                or
                [
                    ""
                ]
            )[0]
            !=
            state
        ):
            raise SystemExit(
                "X OAuth state mismatch"
            )

        code = (
            params.get(
                "code"
            )
            or
            [
                ""
            ]
        )[0]

    if not code:
        raise SystemExit(
            "No authorization code "
            "was received"
        )

    tokens = _oauth_token_exchange(
        {
            "grant_type":
                "authorization_code",

            "code":
                code,

            "redirect_uri":
                X_REDIRECT_URI,

            "code_verifier":
                verifier,
        }
    )

    access = str(
        tokens.get(
            "access_token"
        )
        or
        ""
    )

    refresh = str(
        tokens.get(
            "refresh_token"
        )
        or
        ""
    )

    if (
        not access
        or
        not refresh
    ):
        raise SystemExit(
            "Authorization succeeded "
            "but X did not return both "
            "access and refresh tokens. "
            "Make sure offline.access "
            "was granted."
        )

    verify = requests.get(
        X_ME_URL,
        headers={
            "Authorization":
                f"Bearer {access}"
        },
        timeout=(
            8,
            30,
        ),
    )

    if not (
        200
        <=
        verify.status_code
        <
        300
    ):
        raise SystemExit(
            "Tokens were issued, but "
            "/2/users/me verification "
            "failed HTTP "
            f"{verify.status_code}: "
            f"{verify.text[:500]}"
        )

    me = (
        verify.json()
        .get(
            "data"
        )
        or
        {}
    )

    username = (
        me.get(
            "username"
        )
        or
        me.get(
            "name"
        )
        or
        me.get(
            "id"
        )
        or
        "unknown"
    )

    print(
        "\nAuthorized successfully "
        f"as @{username}.\n"
    )

    print(
        "Put these values in Render "
        "Environment Variables "
        "(never commit them to Git):\n"
    )

    print(
        f"X_CLIENT_ID="
        f"{X_CLIENT_ID}"
    )

    if X_CLIENT_SECRET:
        print(
            "X_CLIENT_SECRET="
            "<the same client secret "
            "you used locally>"
        )

    print(
        f"X_ACCESS_TOKEN="
        f"{access}"
    )

    print(
        f"X_REFRESH_TOKEN="
        f"{refresh}"
    )

    print(
        "\nThe worker stores future "
        "rotated refresh tokens on "
        "its persistent disk."
    )

    return 0


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

    username = x.verify()

    log.info(
        "Authenticated to X as @%s",
        username,
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

    # This line lets us conclusively verify that Render has deployed THIS file.
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
                "Temporary X startup/"
                "auth failure: %s",
                exc,
            )

            time.sleep(
                30
            )

        except Exception:

            db.close()

            log.exception(
                "X credential verification "
                "failed; refusing to run"
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

    for (
        index,
        job,
    ) in enumerate(
        jobs
    ):
        job.next_due = (
            base
            +
            index * 0.8
        )

    try:

        while not STOP_REQUESTED:

            now_mono = (
                time.monotonic()
            )

            for job in jobs:

                if STOP_REQUESTED:
                    break

                if (
                    now_mono
                    <
                    job.next_due
                ):
                    continue

                started = (
                    time.monotonic()
                )

                try:
                    job.func(
                        db,
                        x,
                    )

                except Exception:
                    log.exception(
                        "Unhandled failure "
                        "in job %s",
                        job.name,
                    )

                elapsed = (
                    time.monotonic()
                    -
                    started
                )

                job.next_due = (
                    time.monotonic()
                    +
                    job.interval
                )

                log.debug(
                    "Job %s finished "
                    "in %.2fs",
                    job.name,
                    elapsed,
                )

            time.sleep(
                0.5
            )

    finally:

        counts = (
            db.count_by_status()
        )

        log.info(
            "Stopping. "
            "DB status counts: %s",
            counts,
        )

        db.close()

    return 0


if __name__ == "__main__":

    parser = argparse.ArgumentParser(
        description=(
            "OneWeather automated "
            "NOAA/NWS -> X worker"
        )
    )

    parser.add_argument(
        "--authorize",
        action="store_true",
        help=(
            "run the one-time local "
            "X OAuth2 PKCE "
            "authorization flow "
            "and exit"
        ),
    )

    args = parser.parse_args()

    if args.authorize:
        sys.exit(
            authorize_x_interactively()
        )

    sys.exit(
        main()
    )
