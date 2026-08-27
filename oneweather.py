#!/usr/bin/env python3
"""PriorityWeather automated official-weather -> X worker."""
from __future__ import annotations
import base64
import hashlib
import html
import io
import json
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
from urllib.parse import urljoin
import requests
from bs4 import BeautifulSoup
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageOps
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

BOT_NAME = os.getenv('BOT_NAME', 'PriorityWeather').strip() or 'PriorityWeather'
BUILD_ID = '2026-08-27-nhc-operational-maps-v8.5'
CONTACT_EMAIL = os.getenv('CONTACT_EMAIL', '').strip()
MAPBOX_API_KEY = os.getenv('MAPBOX_API_KEY', '').strip()
MAPBOX_STYLE = os.getenv('MAPBOX_STYLE', 'mapbox/light-v11').strip() or 'mapbox/light-v11'
X_CLIENT_ID = os.getenv('X_CLIENT_ID', '').strip()
X_CLIENT_SECRET = os.getenv('X_CLIENT_SECRET', '').strip()
X_ACCESS_TOKEN = os.getenv('X_ACCESS_TOKEN', '').strip()
X_REFRESH_TOKEN = os.getenv('X_REFRESH_TOKEN', '').strip()
DB_PATH = os.getenv('DB_PATH', '/var/data/oneweather.sqlite3').strip()
DRY_RUN = os.getenv('DRY_RUN', 'false').lower() in {'1', 'true', 'yes', 'on'}
INCLUDE_SOURCE_URLS = os.getenv('INCLUDE_SOURCE_URLS', 'false').lower() in {'1', 'true', 'yes', 'on'}
POST_TEXT_LIMIT = max(1000, min(25000, int(os.getenv('POST_TEXT_LIMIT', '25000'))))
NWS_POLL_SECONDS = max(30, int(os.getenv('NWS_POLL_SECONDS', '30')))
SPC_POLL_SECONDS = max(30, int(os.getenv('SPC_POLL_SECONDS', '60')))
NHC_POLL_SECONDS = max(30, int(os.getenv('NHC_POLL_SECONDS', '60')))
NHC_FULL_SWEEP_SECONDS = max(300, int(os.getenv('NHC_FULL_SWEEP_SECONDS', '600')))
WPC_ERO_POLL_SECONDS = max(60, int(os.getenv('WPC_ERO_POLL_SECONDS', '120')))
WPC_WINTER_POLL_SECONDS = max(60, int(os.getenv('WPC_WINTER_POLL_SECONDS', '300')))
TORNADO_MAX_POST_AGE_MINUTES = max(5, int(os.getenv('TORNADO_MAX_POST_AGE_MINUTES', '30')))
WINTER_ALERT_MAX_POST_AGE_MINUTES = max(30, int(os.getenv('WINTER_ALERT_MAX_POST_AGE_MINUTES', '360')))
NWS_QUERY_BACKFILL_MAX_MINUTES = max(
    15,
    min(
        10080,
        int(os.getenv('NWS_QUERY_BACKFILL_MAX_MINUTES', '360')),
    ),
)
WPC_HSD_MAX_AGE_HOURS = max(12, int(os.getenv('WPC_HSD_MAX_AGE_HOURS', '36')))
ENABLE_SPC_FIRE = os.getenv('ENABLE_SPC_FIRE', 'true').lower() in {'1', 'true', 'yes', 'on'}
ENABLE_NHC_DISCUSSIONS = os.getenv('ENABLE_NHC_DISCUSSIONS', 'true').lower() in {'1', 'true', 'yes', 'on'}
ENABLE_NHC_FORECAST_ADVISORIES = os.getenv('ENABLE_NHC_FORECAST_ADVISORIES', 'false').lower() in {'1', 'true', 'yes', 'on'}
ENABLE_WPC_DAY4_DAY5_ERO = os.getenv('ENABLE_WPC_DAY4_DAY5_ERO', 'true').lower() in {'1', 'true', 'yes', 'on'}
ENABLE_WPC_HEAVY_SNOW_DISCUSSION = os.getenv('ENABLE_WPC_HEAVY_SNOW_DISCUSSION', 'true').lower() in {'1', 'true', 'yes', 'on'}
ENABLE_WPC_WINTER_PACKAGES = os.getenv('ENABLE_WPC_WINTER_PACKAGES', 'true').lower() in {'1', 'true', 'yes', 'on'}
LOG_LEVEL = os.getenv('LOG_LEVEL', 'INFO').upper()

X_TOKEN_URL = 'https://api.x.com/2/oauth2/token'
X_ME_URL = 'https://api.x.com/2/users/me'
X_POST_URL = 'https://api.x.com/2/tweets'
X_MEDIA_URL = 'https://api.x.com/2/media/upload'
X_MEDIA_INIT_URL = 'https://api.x.com/2/media/upload/initialize'

NWS_ALERTS_URL = 'https://api.weather.gov/alerts'
NWS_PRODUCTS_URL = 'https://api.weather.gov/products'

SPC_FEEDS = {
    'spc_md': (
        'https://www.spc.noaa.gov/products/spcmdrss.xml',
        'md',
    ),
    'spc_convective': (
        'https://www.spc.noaa.gov/products/spcacrss.xml',
        'convective',
    ),
    'spc_watches': (
        'https://www.spc.noaa.gov/products/spcwwrss.xml',
        'watch',
    ),
}

if ENABLE_SPC_FIRE:
    SPC_FEEDS['spc_fire'] = (
        'https://www.spc.noaa.gov/products/spcfwrss.xml',
        'fire',
    )

NHC_TWO_FEEDS = {
    'nhc_two_atlantic': 'https://www.nhc.noaa.gov/xml/TWOAT.xml',
    'nhc_two_epac': 'https://www.nhc.noaa.gov/xml/TWOEP.xml',
    'nhc_two_cpac': 'https://www.nhc.noaa.gov/xml/TWOCP.xml',
}

NHC_TWO_IMAGES = {
    'nhc_two_atlantic': 'https://www.nhc.noaa.gov/xgtwo/two_atl_7d0.png',
    'nhc_two_epac': 'https://www.nhc.noaa.gov/xgtwo/two_pac_7d0.png',
    'nhc_two_cpac': 'https://www.nhc.noaa.gov/xgtwo/two_cpac_7d0.png',
}

NHC_BASIN_INDEX_FEEDS = {
    'atlantic': 'https://www.nhc.noaa.gov/index-at.xml',
    'epac': 'https://www.nhc.noaa.gov/index-ep.xml',
    'cpac': 'https://www.nhc.noaa.gov/index-cp.xml',
}

NHC_BASIN_CODES = {
    'atlantic': 'AT',
    'epac': 'EP',
    'cpac': 'CP',
}

NHC_BASIN_LABELS = {
    'atlantic': 'Atlantic Basin',
    'epac': 'Eastern Pacific',
    'cpac': 'Central Pacific',
}

NHC_TROPICAL_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'tropical/rest/services/tropical/'
    'NHC_tropical_weather_summary/'
    'MapServer'
)

NHC_TWO_CURRENT_LAYER = 2
NHC_TWO_REGION_LAYER = 3
NHC_FORECAST_POINTS_LAYER = 5
NHC_FORECAST_TRACK_LAYER = 6
NHC_FORECAST_CONE_LAYER = 7
NHC_WATCH_WARNING_LAYER = 8
NHC_TWO_MOTION_LAYER = 33
NHC_ATCF_BTK_INDEX_URL = 'https://ftp.nhc.noaa.gov/atcf/btk/'

RADAR_EXPORT_URL = (
    'https://mapservices.weather.noaa.gov/'
    'eventdriven/rest/services/'
    'radar/radar_base_reflectivity/'
    'MapServer/export'
)

REFERENCE_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'static/rest/services/'
    'nws_reference_maps/'
    'nws_reference_map/'
    'MapServer'
)

REFERENCE_EXPORT_URL = REFERENCE_MAPSERVER + '/export'

WPC_ERO_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'vector/rest/services/'
    'hazards/wpc_precip_hazards/'
    'MapServer'
)

WPC_WINTER_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'vector/rest/services/'
    'precip/wpc_prob_winter_precip/'
    'MapServer'
)

WPC_HSD_TYPE = 'HSD'
WPC_HSD_LOCATION = 'WBC'

WPC_HSD_RAW_URL = (
    'https://tgftp.nws.noaa.gov/'
    'data/raw/fo/'
    'fous11.kwbc.qpf.hsd.txt'
)

WINTER_ALERT_EVENTS = {
    'Winter Storm Warning',
    'Winter Storm Watch',
    'Winter Weather Advisory',
    'Blizzard Warning',
    'Blizzard Watch',
    'Ice Storm Warning',
    'Lake Effect Snow Warning',
    'Lake Effect Snow Watch',
    'Lake Effect Snow Advisory',
    'Snow Squall Warning',
    'Extreme Cold Warning',
    'Extreme Cold Watch',
    'Cold Weather Advisory',
    'Wind Chill Warning',
    'Wind Chill Watch',
    'Wind Chill Advisory',
    'Heavy Snow Warning',
    'Freezing Rain Advisory',
}

logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format='%(asctime)sZ %(levelname)s %(message)s',
    datefmt='%Y-%m-%dT%H:%M:%S',
)

logging.Formatter.converter = time.gmtime
log = logging.getLogger('priorityweather')

STOP_REQUESTED = False


def request_stop(
    signum: int,
    _frame: Any,
) -> None:
    global STOP_REQUESTED
    STOP_REQUESTED = True

    log.info(
        'Received signal %s; stopping after current work',
        signum,
    )


signal.signal(signal.SIGTERM, request_stop)
signal.signal(signal.SIGINT, request_stop)


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def iso_z(
    dt: datetime,
) -> str:
    return (
        dt.astimezone(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace('+00:00', 'Z')
    )


def sha256_text(
    value: str,
) -> str:
    return hashlib.sha256(
        value.encode(
            'utf-8',
            errors='replace',
        )
    ).hexdigest()


def squish(
    value: Optional[str],
) -> str:
    if not value:
        return ''

    return re.sub(
        r'\s+',
        ' ',
        html.unescape(value),
    ).strip()


def remove_emojis(
    value: str,
) -> str:
    out: list[str] = []

    for ch in value:
        cp = ord(ch)

        if (
            0x1F000 <= cp <= 0x1FAFF
            or
            0x2600 <= cp <= 0x26FF
            or
            0x2700 <= cp <= 0x27BF
            or
            0xFE00 <= cp <= 0xFE0F
            or
            0x1F1E6 <= cp <= 0x1F1FF
        ):
            continue

        out.append(ch)

    return ''.join(out)


def html_to_text(
    value: Optional[str],
    preserve_lines: bool = False,
) -> str:
    if not value:
        return ''

    soup = BeautifulSoup(
        value,
        'html.parser',
    )

    text = soup.get_text(
        '\n'
        if preserve_lines
        else ' ',
        strip=True,
    )

    if preserve_lines:
        lines = [
            re.sub(
                r'[ \t]+',
                ' ',
                line,
            ).strip()
            for line
            in text.splitlines()
        ]

        return '\n'.join(
            line
            for line
            in lines
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
        return value[:limit]

    cut = value[:limit - 1].rstrip()

    if (
        ' ' in cut
        and
        len(
            cut.rsplit(
                ' ',
                1,
            )[0]
        )
        >=
        int(
            limit
            *
            0.72
        )
    ):
        cut = cut.rsplit(
            ' ',
            1,
        )[0]

    return cut + '...'


def fit_post(
    parts: Iterable[str],
    url: str = '',
) -> str:
    clean = [
        remove_emojis(
            part.strip()
        )
        for part
        in parts
        if part
        and
        part.strip()
    ]

    suffix = (
        '\n\n'
        +
        url.strip()
        if
        INCLUDE_SOURCE_URLS
        and
        url
        else
        ''
    )

    budget = (
        POST_TEXT_LIMIT
        -
        len(suffix)
    )

    if budget < 80:
        suffix = ''
        budget = POST_TEXT_LIMIT

    text = '\n'.join(clean)

    if len(text) > budget:
        text = truncate(
            text,
            budget,
        )

    return remove_emojis(
        text
        +
        suffix
    )


def parse_any_datetime(
    value: Optional[str],
) -> Optional[datetime]:
    if not value:
        return None

    value = value.strip()

    try:
        dt = datetime.fromisoformat(
            value.replace(
                'Z',
                '+00:00',
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
    dt = parse_any_datetime(value)

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


def format_utc_clock(
    value: str,
) -> str:
    dt = parse_any_datetime(value)

    if not dt:
        return squish(value)

    return dt.strftime(
        '%-I:%M %p UTC'
    )


def first_parameter(
    parameters: dict[str, Any],
    *names: str,
) -> str:
    lowered = {
        str(key).lower():
            value
        for key, value
        in (
            parameters
            or
            {}
        ).items()
    }

    for name in names:
        value = lowered.get(
            name.lower()
        )

        if (
            isinstance(
                value,
                list,
            )
            and
            value
        ):
            return squish(
                str(value[0])
            )

        if value is not None:
            return squish(
                str(value)
            )

    return ''


def all_parameter_values(
    parameters: dict[str, Any],
    name: str,
) -> list[str]:
    for key, value in (
        parameters
        or
        {}
    ).items():

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
                    str(item)
                    for item
                    in value
                ]

            if value is not None:
                return [
                    str(value)
                ]

            return []

    return []


def extract_hazards(
    text: str,
    product_name: str = '',
) -> list[str]:
    lower = (
        f'{product_name} '
        f'{text}'
    ).lower()

    hazards: list[str] = []

    def add(
        label: str,
        condition: bool,
    ) -> None:
        if (
            condition
            and
            label not in hazards
        ):
            hazards.append(label)

    add(
        'Tornadoes',
        'tornado'
        in lower,
    )

    add(
        'Damaging winds',
        any(
            phrase
            in lower
            for phrase
            in (
                'damaging wind',
                'damaging gust',
                'severe wind',
            )
        ),
    )

    add(
        'Large hail',
        any(
            phrase
            in lower
            for phrase
            in (
                'large hail',
                'severe hail',
                'inch hail',
            )
        ),
    )

    add(
        'Flash flooding',
        any(
            phrase
            in lower
            for phrase
            in (
                'flash flood',
                'excessive rainfall',
            )
        ),
    )

    add(
        'Heavy snow',
        any(
            phrase
            in lower
            for phrase
            in (
                'heavy snow',
                'blizzard',
            )
        ),
    )

    add(
        'Icing',
        any(
            phrase
            in lower
            for phrase
            in (
                'freezing rain',
                'significant icing',
                'ice accumulation',
            )
        ),
    )

    return hazards[:3]


def validate_environment() -> None:
    missing: list[str] = []

    if not CONTACT_EMAIL:
        missing.append(
            'CONTACT_EMAIL'
        )

    if not DRY_RUN:
        for name, value in (
            (
                'X_CLIENT_ID',
                X_CLIENT_ID,
            ),
            (
                'X_CLIENT_SECRET',
                X_CLIENT_SECRET,
            ),
            (
                'X_ACCESS_TOKEN',
                X_ACCESS_TOKEN,
            ),
            (
                'X_REFRESH_TOKEN',
                X_REFRESH_TOKEN,
            ),
        ):
            if not value:
                missing.append(
                    name
                )

    if missing:
        raise SystemExit(
            'Missing required environment variables: '
            +
            ', '.join(missing)
        )

    parent = (
        Path(DB_PATH)
        .expanduser()
        .resolve()
        .parent
    )

    parent.mkdir(
        parents=True,
        exist_ok=True,
    )


def build_http_session() -> requests.Session:
    session = requests.Session()

    session.headers.update(
        {
            'User-Agent':
                f'{BOT_NAME}/1.0 '
                f'({CONTACT_EMAIL})',

            'Accept-Encoding':
                'gzip, deflate',
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
        allowed_methods=
            frozenset(
                {
                    'GET',
                    'HEAD',
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
        'https://',
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


class StateDB:

    def __init__(
        self,
        path: str,
    ):
        self.conn = sqlite3.connect(
            path,
            timeout=30,
            isolation_level=None,
        )

        self.conn.execute(
            'PRAGMA journal_mode=WAL'
        )

        self.conn.execute(
            'PRAGMA synchronous=FULL'
        )

        self.conn.execute(
            'PRAGMA busy_timeout=30000'
        )

        self.conn.executescript(
            '''
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
            '''
        )

    def close(
        self,
    ) -> None:
        self.conn.close()

    def get_meta(
        self,
        key: str,
        default: str = '',
    ) -> str:
        row = self.conn.execute(
            'SELECT value '
            'FROM meta '
            'WHERE key=?',
            (
                key,
            ),
        ).fetchone()

        return (
            row[0]
            if row
            else
            default
        )

    def set_meta(
        self,
        key: str,
        value: str,
    ) -> None:
        self.conn.execute(
            'INSERT INTO meta'
            '(key,value) '
            'VALUES(?,?) '
            'ON CONFLICT(key) '
            'DO UPDATE SET '
            'value=excluded.value',
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
                f'primed:{source}'
            )
            ==
            '1'
        )

    def mark_source_primed(
        self,
        source: str,
    ) -> None:
        self.set_meta(
            f'primed:{source}',
            '1',
        )

    def status(
        self,
        source: str,
        item_key: str,
    ) -> str:
        row = self.conn.execute(
            'SELECT status '
            'FROM items '
            'WHERE source=? '
            'AND item_key=?',
            (
                source,
                item_key,
            ),
        ).fetchone()

        return (
            str(row[0])
            if row
            else
            ''
        )

    def exists(
        self,
        source: str,
        item_key: str,
    ) -> bool:
        return bool(
            self.status(
                source,
                item_key,
            )
        )

    def mark_seen_without_post(
        self,
        source: str,
        item_key: str,
        status: str = 'primed',
    ) -> None:
        now = iso_z(
            utcnow()
        )

        self.conn.execute(
            'INSERT OR IGNORE INTO items'
            '(source,item_key,'
            'first_seen_utc,status,'
            'updated_utc) '
            'VALUES(?,?,?,?,?)',
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
        existing = self.status(
            source,
            item_key,
        )

        if existing == 'rejected':
            self.conn.execute(
                'DELETE FROM items '
                'WHERE source=? '
                'AND item_key=?',
                (
                    source,
                    item_key,
                ),
            )

        elif existing:
            return False

        now = iso_z(
            utcnow()
        )

        try:
            self.conn.execute(
                'INSERT INTO items'
                '(source,item_key,'
                'first_seen_utc,status,'
                'updated_utc) '
                'VALUES(?,?,?,?,?)',
                (
                    source,
                    item_key,
                    now,
                    'posting',
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
        tweet_id: str = '',
        error: str = '',
    ) -> None:
        self.conn.execute(
            'UPDATE items '
            'SET status=?,'
            'tweet_id=?,'
            'last_error=?,'
            'updated_utc=? '
            'WHERE source=? '
            'AND item_key=?',
            (
                status,
                tweet_id
                or
                None,
                error
                or
                None,
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
            'DELETE FROM items '
            'WHERE source=? '
            'AND item_key=?',
            (
                source,
                item_key,
            ),
        )

    def count_by_status(
        self,
    ) -> dict[str, int]:
        rows = self.conn.execute(
            'SELECT status,COUNT(*) '
            'FROM items '
            'GROUP BY status'
        ).fetchall()

        return {
            str(key):
                int(value)
            for key, value
            in rows
        }


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
        self.client_id = X_CLIENT_ID
        self.client_secret = X_CLIENT_SECRET
        self.env_access_token = X_ACCESS_TOKEN
        self.env_refresh_token = X_REFRESH_TOKEN

        self.db_access_token = db.get_meta(
            'x:access_token'
        )

        self.db_refresh_token = db.get_meta(
            'x:refresh_token'
        )

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
                'access_token'
            )
            or
            ''
        ).strip()

        refresh = str(
            payload.get(
                'refresh_token'
            )
            or
            ''
        ).strip()

        if not access:
            raise XRejectedError(
                'X token response had '
                'no access_token: '
                f'{payload!r}'
            )

        self.access_token = access
        self.db_access_token = access

        self.db.set_meta(
            'x:access_token',
            access,
        )

        if refresh:
            self.refresh_token_value = refresh
            self.db_refresh_token = refresh

            self.db.set_meta(
                'x:refresh_token',
                refresh,
            )

        try:
            self.expires_at = (
                time.time()
                +
                max(
                    60,
                    int(
                        payload.get(
                            'expires_in'
                        )
                    ),
                )
                -
                60
            )

        except Exception:
            self.expires_at = 0.0

    def refresh(
        self,
    ) -> None:
        candidates: list[str] = []

        for token in (
            self.db_refresh_token,
            self.refresh_token_value,
            self.env_refresh_token,
        ):
            token = (
                token
                or
                ''
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
                'No X OAuth2 refresh token '
                'is available'
            )

        auth = self._token_auth()
        last_rejection = ''

        for refresh in candidates:
            data = {
                'grant_type':
                    'refresh_token',

                'refresh_token':
                    refresh,
            }

            if not auth:
                data[
                    'client_id'
                ] = self.client_id

            try:
                response = requests.post(
                    X_TOKEN_URL,
                    data=data,
                    auth=auth,
                    headers={
                        'Content-Type':
                            'application/'
                            'x-www-form-urlencoded'
                    },
                    timeout=(
                        8,
                        30,
                    ),
                )

            except requests.RequestException as exc:
                raise XRetryableError(
                    'X token refresh '
                    'network failure: '
                    f'{exc}'
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
                    'X token refresh '
                    'temporary failure HTTP '
                    f'{response.status_code}: '
                    f'{response.text[:500]}'
                )

            last_rejection = (
                f'HTTP '
                f'{response.status_code}: '
                f'{response.text[:500]}'
            )

        raise XRejectedError(
            'All available X refresh '
            'tokens were rejected; '
            'last response '
            +
            last_rejection
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
                'headers',
                {},
            )
            or
            {}
        )

        headers = dict(
            caller_headers
        )

        headers[
            'Authorization'
        ] = (
            f'Bearer {token}'
        )

        headers.setdefault(
            'User-Agent',
            f'{BOT_NAME}/1.0',
        )

        try:
            response = requests.request(
                method,
                url,
                headers=headers,
                timeout=
                    kwargs.pop(
                        'timeout',
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
                    'X create-post '
                    'network failure: '
                    f'{exc}'
                ) from exc

            raise XRetryableError(
                'X API network failure: '
                f'{exc}'
            ) from exc

        if (
            response.status_code
            ==
            401
            and
            retry_auth
        ):
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
        self.dry_run = DRY_RUN

        self.oauth = (
            None
            if self.dry_run
            else
            XOAuth2(db)
        )

    @staticmethod
    def _raise_prepost(
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

        message = (
            f'{operation} '
            f'HTTP '
            f'{response.status_code}: '
            f'{response.text[:500]}'
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
                message
            )

        raise XRejectedError(
            message
        )

    def _upload_image_json(
        self,
        raw: bytes,
        media_type: str,
    ) -> requests.Response:
        assert self.oauth is not None

        payload = {
            'media':
                base64.b64encode(
                    raw
                ).decode(
                    'ascii'
                ),

            'media_category':
                'tweet_image',

            'media_type':
                media_type,

            'shared':
                False,
        }

        return self.oauth.request(
            'POST',
            X_MEDIA_URL,
            json=payload,
            headers={
                'Content-Type':
                    'application/json'
            },
            timeout=(
                10,
                90,
            ),
        )

    def _upload_image_chunked(
        self,
        raw: bytes,
        media_type: str,
    ) -> requests.Response:
        assert self.oauth is not None

        init = self.oauth.request(
            'POST',
            X_MEDIA_INIT_URL,
            json={
                'media_type':
                    media_type,

                'media_category':
                    'tweet_image',

                'total_bytes':
                    len(raw),

                'shared':
                    False,
            },
            headers={
                'Content-Type':
                    'application/json'
            },
            timeout=(
                10,
                45,
            ),
        )

        self._raise_prepost(
            init,
            'X media initialize',
        )

        init_data = (
            init.json()
            .get(
                'data'
            )
            or
            {}
        )

        media_id = str(
            init_data.get(
                'id'
            )
            or
            ''
        )

        if not media_id:
            raise XRetryableError(
                'X media initialize '
                'returned no id: '
                f'{init.text[:300]}'
            )

        append = self.oauth.request(
            'POST',
            f'{X_MEDIA_URL}/'
            f'{media_id}/append',
            json={
                'media':
                    base64.b64encode(
                        raw
                    ).decode(
                        'ascii'
                    ),

                'segment_index':
                    0,
            },
            headers={
                'Content-Type':
                    'application/json'
            },
            timeout=(
                10,
                90,
            ),
        )

        self._raise_prepost(
            append,
            'X media append',
        )

        finalize = self.oauth.request(
            'POST',
            f'{X_MEDIA_URL}/'
            f'{media_id}/finalize',
            headers={
                'Content-Type':
                    'application/json'
            },
            timeout=(
                10,
                45,
            ),
        )

        self._raise_prepost(
            finalize,
            'X media finalize',
        )

        return finalize

    def upload_image(
        self,
        path: str,
    ) -> str:
        if self.dry_run:
            return 'dry-run-media'

        assert self.oauth is not None

        suffix = (
            Path(path)
            .suffix
            .lower()
        )

        media_type = (
            'image/png'
            if
            suffix
            ==
            '.png'
            else
            'image/jpeg'
        )

        size = os.path.getsize(
            path
        )

        if (
            size <= 0
            or
            size
            >
            5
            *
            1024
            *
            1024
        ):
            raise XRejectedError(
                'Invalid X image size: '
                f'{size} bytes'
            )

        with open(
            path,
            'rb',
        ) as file_handle:
            raw = file_handle.read()

        response = self._upload_image_json(
            raw,
            media_type,
        )

        if not (
            200
            <=
            response.status_code
            <
            300
        ):
            simple_status = response.status_code
            simple_body = response.text[:500]

            log.warning(
                'X simple media upload '
                'failed HTTP %s; '
                'trying v2 chunked fallback',
                simple_status,
            )

            try:
                response = self._upload_image_chunked(
                    raw,
                    media_type,
                )

            except XError as exc:
                raise XRejectedError(
                    'X media upload failed. '
                    'Simple upload HTTP '
                    f'{simple_status}: '
                    f'{simple_body}; '
                    f'fallback: {exc}'
                ) from exc

        data = (
            response.json()
            .get(
                'data'
            )
            or
            {}
        )

        media_id = str(
            data.get(
                'id'
            )
            or
            ''
        )

        if not media_id:
            raise XRetryableError(
                'X media upload returned '
                'no id: '
                f'{response.text[:300]}'
            )

        processing = (
            data.get(
                'processing_info'
            )
            or
            {}
        )

        checks = 0

        while (
            processing
            and
            processing.get(
                'state'
            )
            not in {
                'succeeded',
                'failed',
            }
            and
            checks
            <
            20
        ):
            time.sleep(
                max(
                    1,
                    min(
                        10,
                        int(
                            processing.get(
                                'check_after_secs'
                            )
                            or
                            1
                        ),
                    ),
                )
            )

            status = self.oauth.request(
                'GET',
                X_MEDIA_URL,
                params={
                    'media_id':
                        media_id
                },
                timeout=(
                    8,
                    30,
                ),
            )

            self._raise_prepost(
                status,
                'X media STATUS',
            )

            processing = (
                (
                    status.json()
                    .get(
                        'data'
                    )
                    or
                    {}
                )
                .get(
                    'processing_info'
                )
                or
                {}
            )

            checks += 1

        if (
            processing.get(
                'state'
            )
            ==
            'failed'
        ):
            raise XRejectedError(
                'X media processing '
                'failed: '
                f'{processing!r}'
            )

        if (
            processing
            and
            processing.get(
                'state'
            )
            !=
            'succeeded'
        ):
            raise XRetryableError(
                'X media processing '
                'did not finish: '
                f'{processing!r}'
            )

        return media_id

    def create_post(
        self,
        text: str,
        image_path: str = '',
    ) -> str:
        text = remove_emojis(
            truncate(
                text.strip(),
                POST_TEXT_LIMIT,
            )
        )

        if self.dry_run:
            log.info(
                '[DRY RUN POST]\n'
                '%s%s',
                text,
                (
                    f'\n[image={image_path}]'
                    if image_path
                    else
                    ''
                ),
            )

            return 'dry-run-post'

        assert self.oauth is not None

        payload: dict[
            str,
            Any,
        ] = {
            'text':
                text
        }

        if image_path:
            payload[
                'media'
            ] = {
                'media_ids': [
                    self.upload_image(
                        image_path
                    )
                ]
            }

        response = self.oauth.request(
            'POST',
            X_POST_URL,
            json=payload,
            headers={
                'Content-Type':
                    'application/json'
            },
            ambiguous_if_sent=True,
        )

        if response.status_code == 429:
            raise XRetryableError(
                'X create-post '
                'rate limited: '
                f'{response.text[:500]}'
            )

        if (
            500
            <=
            response.status_code
            <
            600
        ):
            raise XAmbiguousError(
                'X create-post server '
                'error HTTP '
                f'{response.status_code}; '
                'outcome unknown: '
                f'{response.text[:500]}'
            )

        if not (
            200
            <=
            response.status_code
            <
            300
        ):
            raise XRejectedError(
                'X create-post rejected '
                f'HTTP '
                f'{response.status_code}: '
                f'{response.text[:500]}'
            )

        tweet_id = str(
            (
                response.json()
                .get(
                    'data'
                )
                or
                {}
            )
            .get(
                'id'
            )
            or
            ''
        )

        if not tweet_id:
            raise XAmbiguousError(
                'X returned success '
                'but no post id: '
                f'{response.text[:500]}'
            )

        return tweet_id

    def verify(
        self,
    ) -> str:
        if self.dry_run:
            return 'dry-run'

        assert self.oauth is not None

        response = self.oauth.request(
            'GET',
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
                'X authenticated-user '
                'lookup failed HTTP '
                f'{response.status_code}: '
                f'{response.text[:500]}'
            )

        data = (
            response.json()
            .get(
                'data'
            )
            or
            {}
        )

        if (
            self.oauth.access_token
            ==
            self.oauth.env_access_token
            and
            self.oauth.env_access_token
        ):
            self.oauth.db.set_meta(
                'x:access_token',
                self.oauth.env_access_token,
            )

            if self.oauth.env_refresh_token:
                self.oauth.db.set_meta(
                    'x:refresh_token',
                    self.oauth.env_refresh_token,
                )

                self.oauth.db_refresh_token = (
                    self.oauth.env_refresh_token
                )

                self.oauth.refresh_token_value = (
                    self.oauth.env_refresh_token
                )

        return str(
            data.get(
                'username'
            )
            or
            data.get(
                'name'
            )
            or
            data.get(
                'id'
            )
            or
            'unknown'
        )


@dataclass
class RenderedPost:
    text: str
    image_path: str = ''


def publish_once(
    db: StateDB,
    x: XPublisher,
    source: str,
    item_key: str,
    post: RenderedPost,
) -> bool:
    if not db.claim(
        source,
        item_key,
    ):
        return False

    try:
        tweet_id = x.create_post(
            post.text,
            image_path=
                post.image_path,
        )

        db.set_status(
            source,
            item_key,
            'posted',
            tweet_id=
                tweet_id,
        )

        log.info(
            'Posted %s %s -> '
            'X id %s',
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
            'Retryable X failure '
            'for %s %s: %s',
            source,
            item_key[:16],
            exc,
        )

    except XRejectedError as exc:
        db.set_status(
            source,
            item_key,
            'rejected',
            error=
                repr(
                    exc
                ),
        )

        log.error(
            'X rejected %s %s: %s',
            source,
            item_key[:16],
            exc,
        )

    except XAmbiguousError as exc:
        db.set_status(
            source,
            item_key,
            'ambiguous',
            error=
                repr(
                    exc
                ),
        )

        log.error(
            'Ambiguous X result '
            'for %s %s; '
            'not auto-retrying: %s',
            source,
            item_key[:16],
            exc,
        )

    except Exception as exc:
        db.set_status(
            source,
            item_key,
            'ambiguous',
            error=
                repr(
                    exc
                ),
        )

        log.exception(
            'Unexpected X publish '
            'failure for %s %s',
            source,
            item_key[:16],
        )

    return False


def cleanup_post(
    post: Optional[
        RenderedPost
    ],
) -> None:
    if (
        post
        and
        post.image_path
    ):
        try:
            os.unlink(
                post.image_path
            )

        except OSError:
            pass


def image_bytes_to_temp(
    content: bytes,
    prefix: str = 'priorityweather_',
) -> str:
    image = Image.open(
        io.BytesIO(
            content
        )
    )

    try:
        image.seek(
            0
        )

    except Exception:
        pass

    image = image.convert(
        'RGB'
    )

    max_side = 1800

    if (
        max(
            image.size
        )
        >
        max_side
    ):
        scale = (
            max_side
            /
            max(
                image.size
            )
        )

        image = image.resize(
            (
                max(
                    1,
                    int(
                        image.width
                        *
                        scale
                    ),
                ),
                max(
                    1,
                    int(
                        image.height
                        *
                        scale
                    ),
                ),
            ),
            Image.Resampling.LANCZOS,
        )

    tmp = (
        tempfile.NamedTemporaryFile(
            prefix=prefix,
            suffix='.jpg',
            delete=False,
        )
    )

    tmp.close()

    quality = 91

    image.save(
        tmp.name,
        'JPEG',
        quality=quality,
        optimize=True,
    )

    while (
        os.path.getsize(
            tmp.name
        )
        >
        4_700_000
        and
        quality
        >
        55
    ):
        quality -= 8

        image.save(
            tmp.name,
            'JPEG',
            quality=quality,
            optimize=True,
        )

    return tmp.name


def download_image_to_temp(
    url: str,
    prefix: str = 'priorityweather_',
) -> str:
    response = http_get(
        url,
        headers={
            'Accept':
                'image/png,'
                'image/jpeg,'
                'image/gif,'
                'image/webp,'
                '*/*'
        },
        timeout=(
            8,
            45,
        ),
    )

    return image_bytes_to_temp(
        response.content,
        prefix=prefix,
    )


def nhc_browser_headers(
    *,
    referer: str = 'https://www.nhc.noaa.gov/',
    image: bool = False,
) -> dict[str, str]:
    return {
        'User-Agent': (
            'Mozilla/5.0 '
            '(X11; Linux x86_64) '
            'AppleWebKit/537.36 '
            '(KHTML, like Gecko) '
            'Chrome/127.0.0.0 '
            'Safari/537.36'
        ),
        'Accept': (
            'image/avif,'
            'image/webp,'
            'image/apng,'
            'image/svg+xml,'
            'image/*,*/*;q=0.8'
            if image
            else
            'text/html,'
            'application/xhtml+xml,'
            'application/xml;q=0.9,'
            '*/*;q=0.8'
        ),
        'Referer': referer,
        'Accept-Language':
            'en-US,en;q=0.9',
        'Cache-Control':
            'no-cache',
        'Pragma':
            'no-cache',
        'Sec-Fetch-Dest':
            'image'
            if image
            else
            'document',
        'Sec-Fetch-Mode':
            'no-cors'
            if image
            else
            'navigate',
        'Sec-Fetch-Site':
            'same-origin',
    }


def download_nhc_image_to_temp(
    url: str,
    prefix: str = 'nhc_',
    *,
    referer: str = 'https://www.nhc.noaa.gov/',
) -> str:
    if not url:
        return ''

    headers = nhc_browser_headers(
        referer=referer,
        image=True,
    )

    try:
        HTTP.get(
            'https://www.nhc.noaa.gov/',
            headers=nhc_browser_headers(),
            timeout=(
                8,
                20,
            ),
        )

    except Exception:
        pass

    attempts = [
        url,
    ]

    if '?' not in url:
        attempts.append(
            url
            +
            f'?v={int(time.time())}'
        )

    last_error: Optional[Exception] = None

    for candidate in attempts:
        try:
            response = http_get(
                candidate,
                headers=headers,
                timeout=(
                    8,
                    45,
                ),
            )

            return image_bytes_to_temp(
                response.content,
                prefix=prefix,
            )

        except Exception as exc:
            last_error = exc

    if last_error is not None:
        raise last_error

    return ''


def fetch_nhc_product_page(
    url: str,
) -> tuple[
    str,
    BeautifulSoup,
]:
    response = http_get(
        url,
        headers=nhc_browser_headers(
            referer='https://www.nhc.noaa.gov/',
            image=False,
        ),
        timeout=(
            8,
            35,
        ),
    )

    soup = BeautifulSoup(
        response.text,
        'html.parser',
    )

    pre = soup.find(
        'pre'
    )

    page_text = (
        pre.get_text(
            '\n',
            strip=True,
        )
        if pre
        else
        soup.get_text(
            '\n',
            strip=True,
        )
    )

    return (
        page_text,
        soup,
    )


def fetch_product_page(
    url: str,
) -> tuple[
    str,
    BeautifulSoup,
]:
    headers = {
        'Accept':
            'text/html,'
            'application/xhtml+xml'
    }

    if (
        'spc.noaa.gov'
        in
        url.lower()
    ):
        headers.update(
            {
                'User-Agent': (
                    'Mozilla/5.0 '
                    '(X11; Linux x86_64) '
                    'AppleWebKit/537.36 '
                    '(KHTML, like Gecko) '
                    'Chrome/127.0.0.0 '
                    'Safari/537.36'
                ),
                'Referer':
                    'https://www.spc.noaa.gov/',
                'Accept-Language':
                    'en-US,en;q=0.9',
                'Cache-Control':
                    'no-cache',
                'Pragma':
                    'no-cache',
            }
        )

    response = http_get(
        url,
        headers=headers,
        timeout=(
            8,
            35,
        ),
    )

    soup = BeautifulSoup(
        response.text,
        'html.parser',
    )

    pre = soup.find(
        'pre'
    )

    text = (
        pre.get_text(
            '\n',
            strip=True,
        )
        if pre
        else
        soup.get_text(
            '\n',
            strip=True,
        )
    )

    return (
        text,
        soup,
    )


def page_product_image(
    page_url: str,
    soup: BeautifulSoup,
    kind: str,
    product_number: str = '',
) -> str:
    candidates: list[
        tuple[
            int,
            str,
        ]
    ] = []

    for image_tag in soup.find_all(
        'img'
    ):
        src = str(
            image_tag.get(
                'src'
            )
            or
            ''
        ).strip()

        if not src:
            continue

        descriptor = ' '.join(
            (
                str(
                    image_tag.get(
                        'alt'
                    )
                    or
                    ''
                ),
                str(
                    image_tag.get(
                        'title'
                    )
                    or
                    ''
                ),
                src,
            )
        ).lower()

        if any(
            bad
            in
            descriptor
            for bad
            in (
                'logo',
                'legend',
                'banner',
                'rss',
                'spc-logo',
            )
        ):
            continue

        score = 0

        if (
            'graphic'
            in
            descriptor
        ):
            score += 8

        if (
            kind
            ==
            'md'
            and
            any(
                value
                in
                descriptor
                for value
                in (
                    'mcd',
                    'mesoscale',
                    'md',
                )
            )
        ):
            score += 25

        elif (
            kind
            ==
            'watch'
            and
            any(
                value
                in
                descriptor
                for value
                in (
                    'watch',
                    'ww',
                )
            )
        ):
            score += 25

        elif (
            kind
            ==
            'convective'
        ):
            if (
                'categorical'
                in
                descriptor
            ):
                score += 30

            if any(
                value
                in
                descriptor
                for value
                in (
                    'day1otlk',
                    'day2otlk',
                    'day3otlk',
                    'outlook',
                )
            ):
                score += 20

        elif (
            kind
            ==
            'fire'
            and
            'fire'
            in
            descriptor
        ):
            score += 25

        if (
            product_number
            and
            product_number.lstrip(
                '0'
            )
            in
            descriptor
        ):
            score += 15

        if any(
            extension
            in
            src.lower()
            for extension
            in (
                '.png',
                '.gif',
                '.jpg',
                '.jpeg',
            )
        ):
            score += 3

        if score:
            candidates.append(
                (
                    score,
                    urljoin(
                        page_url,
                        src,
                    ),
                )
            )

    for (
        _score,
        image_url,
    ) in sorted(
        candidates,
        reverse=True,
    ):
        try:
            path = (
                download_image_to_temp(
                    image_url,
                    prefix=
                        f'spc_{kind}_',
                )
            )

            with Image.open(
                path
            ) as image:
                if (
                    image.width
                    >=
                    400
                    and
                    image.height
                    >=
                    250
                ):
                    return path

            os.unlink(
                path
            )

        except Exception:
            continue

    return ''


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
        *
        math.radians(
            lon
        ),

        radius
        *
        math.log(
            math.tan(
                math.pi
                /
                4
                +
                math.radians(
                    lat
                )
                /
                2
            )
        ),
    )


def mercator_bbox_from_lonlat(
    west: float,
    south: float,
    east: float,
    north: float,
) -> tuple[
    float,
    float,
    float,
    float,
]:
    minx, miny = (
        lonlat_to_web_mercator(
            west,
            south,
        )
    )

    maxx, maxy = (
        lonlat_to_web_mercator(
            east,
            north,
        )
    )

    return (
        minx,
        miny,
        maxx,
        maxy,
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
    layers: str = '',
) -> Image.Image:
    params: dict[
        str,
        Any,
    ] = {
        'bbox':
            ','.join(
                f'{value:.3f}'
                for value
                in bbox
            ),

        'bboxSR':
            '3857',

        'imageSR':
            '3857',

        'size':
            f'{width},{height}',

        'format':
            'png32',

        'transparent':
            'true',

        'f':
            'image',
    }

    if layers:
        params[
            'layers'
        ] = layers

    response = http_get(
        url,
        params=params,
        headers={
            'Accept':
                'image/png,*/*'
        },
        timeout=(
            8,
            45,
        ),
    )

    return (
        Image.open(
            io.BytesIO(
                response.content
            )
        )
        .convert(
            'RGBA'
        )
    )


def build_service_map(
    mapserver: str,
    layers: str,
    *,
    bbox_lonlat: tuple[
        float,
        float,
        float,
        float,
    ] = (
        -128,
        22,
        -65,
        52,
    ),
    prefix: str = 'product_map_',
) -> str:
    width = 1200
    height = 760

    bbox = (
        mercator_bbox_from_lonlat(
            *bbox_lonlat
        )
    )

    product = export_map_image(
        f'{mapserver}/export',
        bbox,
        width,
        height,
        layers=layers,
    )

    refs = export_map_image(
        REFERENCE_EXPORT_URL,
        bbox,
        width,
        height,
        layers='show:2,3',
    )

    base = Image.new(
        'RGBA',
        (
            width,
            height,
        ),
        (
            245,
            246,
            247,
            255,
        ),
    )

    base.alpha_composite(
        product
    )

    base.alpha_composite(
        refs
    )

    tmp = (
        tempfile.NamedTemporaryFile(
            prefix=prefix,
            suffix='.jpg',
            delete=False,
        )
    )

    tmp.close()

    base.convert(
        'RGB'
    ).save(
        tmp.name,
        'JPEG',
        quality=91,
        optimize=True,
    )

    return tmp.name


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
        or
        not isinstance(
            geometry.get(
                'coordinates'
            ),
            list,
        )
    ):
        return []

    coords = (
        geometry[
            'coordinates'
        ]
    )

    if (
        geometry.get(
            'type'
        )
        ==
        'Polygon'
        and
        coords
    ):
        return (
            [
                coords[0]
            ]
            if
            isinstance(
                coords[0],
                list,
            )
            else
            []
        )

    if (
        geometry.get(
            'type'
        )
        ==
        'MultiPolygon'
    ):
        return [
            polygon[0]
            for polygon
            in coords
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
            float(
                coordinate[0]
            ),
            float(
                coordinate[1]
            ),
        )
        for ring
        in rings
        for coordinate
        in ring
        if (
            isinstance(
                coordinate,
                (
                    list,
                    tuple,
                ),
            )
            and
            len(
                coordinate
            )
            >=
            2
        )
    ]

    if not points:
        raise ValueError(
            'Warning geometry has '
            'no usable coordinates'
        )

    xs = [
        point[0]
        for point
        in points
    ]

    ys = [
        point[1]
        for point
        in points
    ]

    minx = min(
        xs
    )

    maxx = max(
        xs
    )

    miny = min(
        ys
    )

    maxy = max(
        ys
    )

    cx = (
        minx
        +
        maxx
    ) / 2

    cy = (
        miny
        +
        maxy
    ) / 2

    raw_w = max(
        maxx
        -
        minx,
        120000.0,
    ) * 1.65

    raw_h = max(
        maxy
        -
        miny,
        90000.0,
    ) * 1.65

    aspect = (
        width
        /
        height
    )

    if (
        raw_w
        /
        raw_h
        <
        aspect
    ):
        raw_w = (
            raw_h
            *
            aspect
        )

    else:
        raw_h = (
            raw_w
            /
            aspect
        )

    return (
        cx
        -
        raw_w
        /
        2,

        cy
        -
        raw_h
        /
        2,

        cx
        +
        raw_w
        /
        2,

        cy
        +
        raw_h
        /
        2,
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
    minx, miny, maxx, maxy = bbox

    out: list[
        tuple[
            int,
            int,
        ]
    ] = []

    for coordinate in ring:
        if (
            not isinstance(
                coordinate,
                (
                    list,
                    tuple,
                ),
            )
            or
            len(
                coordinate
            )
            <
            2
        ):
            continue

        mx, my = (
            lonlat_to_web_mercator(
                float(
                    coordinate[0]
                ),
                float(
                    coordinate[1]
                ),
            )
        )

        px = int(
            round(
                (
                    mx
                    -
                    minx
                )
                /
                (
                    maxx
                    -
                    minx
                )
                *
                (
                    width
                    -
                    1
                )
            )
        )

        py = int(
            round(
                (
                    maxy
                    -
                    my
                )
                /
                (
                    maxy
                    -
                    miny
                )
                *
                (
                    height
                    -
                    1
                )
            )
        )

        out.append(
            (
                px,
                py,
            )
        )

    return out


def load_font(
    size: int,
    bold: bool = False,
) -> ImageFont.ImageFont:
    names = [
        (
            '/usr/share/fonts/'
            'truetype/dejavu/'
            'DejaVuSans-Bold.ttf'
            if bold
            else
            '/usr/share/fonts/'
            'truetype/dejavu/'
            'DejaVuSans.ttf'
        ),
        (
            '/usr/share/fonts/'
            'truetype/liberation2/'
            'LiberationSans-Bold.ttf'
            if bold
            else
            '/usr/share/fonts/'
            'truetype/liberation2/'
            'LiberationSans-Regular.ttf'
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


def build_alert_polygon_image(
    feature: dict[
        str,
        Any,
    ],
    title: str,
    *,
    radar: bool,
) -> str:
    rings = warning_rings(
        feature.get(
            'geometry'
        )
    )

    if not rings:
        return ''

    map_w = 1200
    map_h = 760
    header_h = 120

    bbox = map_bbox_for_rings(
        rings,
        map_w,
        map_h,
    )

    base = Image.new(
        'RGBA',
        (
            map_w,
            map_h,
        ),
        (
            245,
            246,
            247,
            255,
        ),
    )

    if radar:
        radar_image = export_map_image(
            RADAR_EXPORT_URL,
            bbox,
            map_w,
            map_h,
        )

        base.alpha_composite(
            radar_image
        )

    refs = export_map_image(
        REFERENCE_EXPORT_URL,
        bbox,
        map_w,
        map_h,
        layers='show:2,3',
    )

    if radar:
        alpha = refs.getchannel(
            'A'
        )

        refs = (
            ImageOps.invert(
                refs.convert(
                    'RGB'
                )
            )
            .convert(
                'RGBA'
            )
        )

        refs.putalpha(
            alpha
        )

    base.alpha_composite(
        refs
    )

    draw = ImageDraw.Draw(
        base,
        'RGBA',
    )

    for ring in rings:
        points = map_ring_to_pixels(
            ring,
            bbox,
            map_w,
            map_h,
        )

        if len(points) < 3:
            continue

        fill = (
            (
                230,
                30,
                30,
                58,
            )
            if radar
            else
            (
                30,
                80,
                210,
                52,
            )
        )

        line = (
            (
                225,
                25,
                25,
                255,
            )
            if radar
            else
            (
                30,
                70,
                190,
                255,
            )
        )

        draw.polygon(
            points,
            fill=fill,
        )

        draw.line(
            points
            +
            [
                points[0]
            ],
            fill=(
                255,
                255,
                255,
                245,
            ),
            width=10,
            joint='curve',
        )

        draw.line(
            points
            +
            [
                points[0]
            ],
            fill=line,
            width=6,
            joint='curve',
        )

    canvas = Image.new(
        'RGBA',
        (
            map_w,
            header_h
            +
            map_h,
        ),
        (
            18,
            20,
            23,
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
        canvas
    )

    draw.text(
        (
            30,
            27,
        ),
        remove_emojis(
            title
        ),
        font=
            load_font(
                44,
                True,
            ),
        fill=(
            245,
            245,
            245,
            255,
        ),
    )

    tmp = tempfile.NamedTemporaryFile(
        prefix='warning_map_',
        suffix='.jpg',
        delete=False,
    )

    tmp.close()

    canvas.convert(
        'RGB'
    ).save(
        tmp.name,
        'JPEG',
        quality=91,
        optimize=True,
    )

    return tmp.name


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
            self.description_html
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
        return sha256_text(
            '\x1f'.join(
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
    def published(
        self,
    ) -> Optional[
        datetime
    ]:
        return parse_any_datetime(
            self.pub_date
        )


def child_text(
    node: ET.Element,
    local_name: str,
) -> str:
    for child in list(
        node
    ):
        if (
            child.tag
            .rsplit(
                '}',
                1,
            )[-1]
            .lower()
            ==
            local_name.lower()
        ):
            return ''.join(
                child.itertext()
            ).strip()

    return ''


def fetch_rss(
    url: str,
) -> list[
    RSSItem
]:
    response = http_get(
        url,
        headers={
            'Accept':
                'application/rss+xml,'
                'application/xml,'
                'text/xml,*/*'
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
                '}',
                1,
            )[-1]
            .lower()
            !=
            'item'
        ):
            continue

        items.append(
            RSSItem(
                title=
                    squish(
                        child_text(
                            node,
                            'title',
                        )
                    ),

                link=
                    child_text(
                        node,
                        'link',
                    ).strip(),

                guid=
                    child_text(
                        node,
                        'guid',
                    ).strip(),

                pub_date=
                    child_text(
                        node,
                        'pubDate',
                    ).strip(),

                description_html=
                    child_text(
                        node,
                        'description',
                    ),
            )
        )

    items.sort(
        key=lambda item:
            item.published
            or
            datetime(
                1970,
                1,
                1,
                tzinfo=
                    timezone.utc,
            )
    )

    return items


def process_rss_source(
    db: StateDB,
    x: XPublisher,
    *,
    source: str,
    url: str,
    renderer: Callable[
        [
            RSSItem
        ],
        Optional[
            RenderedPost
        ],
    ],
    item_filter: Optional[
        Callable[
            [
                RSSItem
            ],
            bool,
        ]
    ] = None,
) -> None:
    accepted = [
        item
        for item
        in fetch_rss(
            url
        )
        if (
            item_filter is None
            or
            item_filter(
                item
            )
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
            'Primed %s with %d '
            'existing RSS item(s)',
            source,
            len(accepted),
        )

        return

    for item in accepted:
        current_status = db.status(
            source,
            item.key,
        )

        if (
            current_status
            and
            current_status
            !=
            'rejected'
        ):
            continue

        post: Optional[
            RenderedPost
        ] = None

        try:
            try:
                post = renderer(
                    item
                )

            except RetryableSourceDataError as exc:
                log.info(
                    'Deferred %s %s: %s',
                    source,
                    item.key[:16],
                    exc,
                )

                continue

            if not post:
                db.mark_seen_without_post(
                    source,
                    item.key,
                    status='ignored',
                )

                continue

            publish_once(
                db,
                x,
                source,
                item.key,
                post,
            )

        finally:
            cleanup_post(
                post
            )


class RetryableSourceDataError(
    RuntimeError
):
    pass


SPC_OUTLOOK_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'vector/rest/services/'
    'outlooks/SPC_wx_outlks/'
    'MapServer'
)

SPC_MCD_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'vector/rest/services/'
    'outlooks/spc_mesoscale_discussion/'
    'MapServer'
)

WWA_MAPSERVER = (
    'https://mapservices.weather.noaa.gov/'
    'eventdriven/rest/services/'
    'WWA/watch_warn_adv/'
    'MapServer'
)

SPC_OUTLOOK_LAYER_IDS = {
    1: {
        'categorical': 1,
        'tornado': 3,
        'hail': 5,
        'wind': 7,
    },
    2: {
        'categorical': 9,
        'tornado': 11,
        'hail': 13,
        'wind': 15,
    },
    3: {
        'categorical': 17,
        'severe': 19,
    },
    4: {
        'probability': 21,
    },
    5: {
        'probability': 22,
    },
    6: {
        'probability': 23,
    },
    7: {
        'probability': 24,
    },
    8: {
        'probability': 25,
    },
}


@dataclass(
    frozen=True
)
class SPCConvectiveSnapshot:
    day: int
    category: str
    tornado_risk: str
    wind_risk: str
    hail_risk: str
    severe_risk: str
    image_path: str
    issued: str
    valid: str


@dataclass(
    frozen=True
)
class SPCGeometryMatch:
    attributes: dict[
        str,
        Any,
    ]
    geometry: dict[
        str,
        Any,
    ]


def arcgis_query_features(
    mapserver: str,
    layer: int,
    *,
    where: str = '1=1',
    out_fields: str = '*',
    return_geometry: bool = False,
    order_by: str = '',
    out_sr: Optional[int] = None,
) -> list[
    dict[
        str,
        Any,
    ]
]:
    params: dict[
        str,
        Any,
    ] = {
        'where':
            where,

        'outFields':
            out_fields,

        'returnGeometry':
            (
                'true'
                if
                return_geometry
                else
                'false'
            ),

        'f':
            'json',
    }

    if order_by:
        params[
            'orderByFields'
        ] = order_by

    if out_sr is not None:
        params[
            'outSR'
        ] = str(
            out_sr
        )

    features: list[
        dict[
            str,
            Any,
        ]
    ] = []

    offset = 0

    while True:
        page_params = dict(
            params
        )

        page_params[
            'resultOffset'
        ] = offset

        page_params[
            'resultRecordCount'
        ] = 2000

        response = http_get(
            f'{mapserver}/'
            f'{layer}/query',
            params=page_params,
            headers={
                'Accept':
                    'application/json'
            },
            timeout=(
                8,
                40,
            ),
        )

        payload = response.json()

        if payload.get(
            'error'
        ):
            raise RuntimeError(
                'ArcGIS query error '
                f'for {mapserver}/{layer}: '
                f'{payload["error"]!r}'
            )

        page = (
            payload.get(
                'features'
            )
            or
            []
        )

        features.extend(
            page
        )

        if (
            not
            payload.get(
                'exceededTransferLimit'
            )
            or
            not page
        ):
            break

        offset += len(
            page
        )

    return features


def arcgis_query_features_in_bbox(
    mapserver: str,
    layer: int,
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    *,
    out_fields: str = '*',
    return_geometry: bool = False,
    out_sr: int = 3857,
) -> list[
    dict[
        str,
        Any,
    ]
]:
    minx, miny, maxx, maxy = bbox

    params: dict[
        str,
        Any,
    ] = {
        'where':
            '1=1',

        'geometry':
            json.dumps(
                {
                    'xmin':
                        minx,

                    'ymin':
                        miny,

                    'xmax':
                        maxx,

                    'ymax':
                        maxy,

                    'spatialReference': {
                        'wkid':
                            3857
                    },
                }
            ),

        'geometryType':
            'esriGeometryEnvelope',

        'inSR':
            '3857',

        'spatialRel':
            'esriSpatialRelIntersects',

        'outFields':
            out_fields,

        'returnGeometry':
            (
                'true'
                if
                return_geometry
                else
                'false'
            ),

        'outSR':
            str(
                out_sr
            ),

        'f':
            'json',

        'resultRecordCount':
            2000,
    }

    response = http_get(
        f'{mapserver}/'
        f'{layer}/query',
        params=params,
        headers={
            'Accept':
                'application/json'
        },
        timeout=(
            8,
            40,
        ),
    )

    payload = response.json()

    if payload.get(
        'error'
    ):
        raise RuntimeError(
            'ArcGIS bbox query error '
            f'for {mapserver}/{layer}: '
            f'{payload["error"]!r}'
        )

    return (
        payload.get(
            'features'
        )
        or
        []
    )


def sql_quote(
    value: str,
) -> str:
    return (
        "'"
        +
        value.replace(
            "'",
            "''",
        )
        +
        "'"
    )


def digits_only(
    value: Any,
) -> str:
    return re.sub(
        r'\D+',
        '',
        str(
            value
            or
            ''
        ),
    )


def clean_spc_location(
    value: str,
) -> str:
    cleaned = squish(
        value
    )

    cleaned = re.sub(
        r'^(?:portions|parts) of\s+',
        '',
        cleaned,
        flags=re.I,
    )

    cleaned = re.sub(
        r'^(?:the )',
        '',
        cleaned,
        flags=re.I,
    )

    return truncate(
        cleaned,
        110,
    )


def spc_item_is_real(
    item: RSSItem,
    kind: str,
) -> bool:
    combined = (
        f'{item.title} '
        f'{item.text}'
    ).lower()

    if any(
        marker
        in
        combined
        for marker
        in (
            'no mesoscale discussions',
            'no watches are',
            'no watches in effect',
            'no severe thunderstorm watches',
            'no tornado watches',
            'no fire weather',
        )
    ):
        return False

    if kind == 'watch':
        return (
            'status report'
            not in combined
            and
            'watch'
            in combined
            and
            (
                'tornado'
                in combined
                or
                'severe thunderstorm'
                in combined
            )
        )

    if kind == 'md':
        return (
            'mesoscale discussion'
            in combined
        )

    if kind == 'convective':
        return (
            'outlook'
            in combined
        )

    if kind == 'fire':
        return (
            'fire'
            in combined
            and
            'outlook'
            in combined
        )

    return True


def spc_field(
    text: str,
    label: str,
) -> str:
    match = re.search(
        rf'(?is)'
        rf'{re.escape(label)}'
        rf'\s*\.{{3}}\s*'
        rf'(.*?)'
        rf'(?='
        rf'\n\s*'
        rf'(?:'
        rf'Areas affected|'
        rf'Concerning|'
        rf'Valid|'
        rf'Probability of Watch Issuance|'
        rf'Summary|'
        rf'Discussion'
        rf')'
        rf'\s*\.{{3}}'
        rf'|$'
        rf')',
        text,
    )

    return (
        squish(
            match.group(
                1
            )
        )
        if match
        else
        ''
    )


SPC_DAY_WORDS = {
    1: 'One',
    2: 'Two',
    3: 'Three',
    4: 'Four',
    5: 'Five',
    6: 'Six',
    7: 'Seven',
    8: 'Eight',
}


def spc_product_name(
    item: RSSItem,
    kind: str,
) -> tuple[
    str,
    str,
]:
    combined = (
        f'{item.title} '
        f'{item.text}'
    )

    if kind == 'watch':
        match = re.search(
            r'\b'
            r'(Tornado Watch|'
            r'Severe Thunderstorm Watch)'
            r'\s*#?\s*'
            r'(\d+)\b',
            combined,
            re.I,
        )

        if match:
            return (
                f'{match.group(1).title()} '
                f'{int(match.group(2))}',
                match.group(
                    2
                ),
            )

        return (
            (
                'Tornado Watch'
                if
                'tornado'
                in
                combined.lower()
                else
                'Severe Thunderstorm Watch'
            ),
            '',
        )

    if kind == 'md':
        match = re.search(
            r'Mesoscale Discussion'
            r'\s*#?\s*'
            r'(\d+)',
            combined,
            re.I,
        )

        if match:
            return (
                f'Mesoscale Discussion '
                f'{int(match.group(1))}',
                match.group(
                    1
                ),
            )

        return (
            'Mesoscale Discussion',
            '',
        )

    if kind == 'convective':
        match = re.search(
            r'Day\s*([1-8])',
            combined,
            re.I,
        )

        if match:
            day = int(
                match.group(
                    1
                )
            )

            return (
                f'Day '
                f'{SPC_DAY_WORDS.get(day, str(day))} '
                'Convective Outlook',
                '',
            )

        return (
            'Convective Outlook',
            '',
        )

    if kind == 'fire':
        match = re.search(
            r'Day\s*([1-8])',
            combined,
            re.I,
        )

        if match:
            day = int(
                match.group(
                    1
                )
            )

            return (
                f'Day '
                f'{SPC_DAY_WORDS.get(day, str(day))} '
                'Fire Weather Outlook',
                '',
            )

        return (
            'Fire Weather Outlook',
            '',
        )

    return (
        item.title,
        '',
    )


def spc_location(
    text: str,
    kind: str,
) -> str:
    area = spc_field(
        text,
        'Areas affected',
    )

    if area:
        return clean_spc_location(
            area
        )

    if kind == 'watch':
        match = re.search(
            r'(?is)'
            r'watch\s+for\s+'
            r'portions\s+of\s+'
            r'(.*?)'
            r'(?='
            r'\s+effective\b|'
            r'\s+primary threats\b|'
            r'\n\s*\*'
            r')',
            text,
        )

        if match:
            return clean_spc_location(
                match.group(
                    1
                )
            )

    if kind == 'convective':
        match = re.search(
            r'(?is)'
            r'THERE IS '
            r'(?:AN?|A) '
            r'.*? '
            r'RISK OF '
            r'SEVERE THUNDERSTORMS '
            r'(?:ACROSS|FOR) '
            r'(.*?)'
            r'(?:\.|\n)',
            text,
        )

        if match:
            return clean_spc_location(
                match.group(
                    1
                )
            )

    if kind == 'fire':
        match = re.search(
            r'(?is)'
            r'(?:CRITICAL|ELEVATED) '
            r'FIRE WEATHER AREA'
            r'(?:S)? '
            r'(?:FOR|ACROSS) '
            r'(.*?)'
            r'(?:\.|\n)',
            text,
        )

        if match:
            return clean_spc_location(
                match.group(
                    1
                )
            )

    return 'United States'


def smart_title_region(
    value: str,
) -> str:
    value = squish(
        value
    ).strip(
        ' .;:-'
    )

    value = re.sub(
        r'^(?:THE\s+)',
        '',
        value,
        flags=re.I,
    )

    value = re.sub(
        r'^(?:PARTS?|PORTIONS?)\s+OF\s+(?:THE\s+)?',
        '',
        value,
        flags=re.I,
    )

    value = re.sub(
        r'\s+AND\s+PORTIONS?\s+OF\s+(?:THE\s+)?',
        ' and ',
        value,
        flags=re.I,
    )

    value = re.sub(
        r'\s+AND\s+PARTS?\s+OF\s+(?:THE\s+)?',
        ' and ',
        value,
        flags=re.I,
    )

    if value.upper() == value:
        value = value.title()

    for word in (
        ' And ',
        ' Of ',
        ' The ',
        ' In ',
        ' Across ',
        ' Near ',
    ):
        value = value.replace(
            word,
            word.lower(),
        )

    return value.strip()


def spc_convective_risk_location(
    text: str,
    category: str,
) -> str:
    flat = squish(
        text
    )

    category_word = re.sub(
        r'\s+Risk\s*$',
        '',
        squish(
            category
        ),
        flags=re.I,
    )

    category_pattern = (
        re.escape(
            category_word
        )
        if
        category_word
        else
        r'(?:Marginal|Slight|Enhanced|Moderate|High)'
    )

    patterns = [
        (
            rf'THERE IS (?:AN?|A)\s+'
            rf'{category_pattern}\s+'
            r'RISK OF SEVERE THUNDERSTORMS\s+'
            r'(?:ACROSS|FOR)\s+'
            r'(.+?)'
            r'(?=\.\.\.|\.(?:\s|$)|$)'
        ),
        (
            rf'{category_pattern}\s+'
            r'RISK OF SEVERE THUNDERSTORMS\s+'
            r'(?:ACROSS|FOR)\s+'
            r'(.+?)'
            r'(?=\.\.\.|\.(?:\s|$)|$)'
        ),
    ]

    for pattern in patterns:
        match = re.search(
            pattern,
            flat,
            re.I,
        )

        if not match:
            continue

        region = smart_title_region(
            match.group(
                1
            )
        )

        if (
            region
            and
            region.lower()
            not in {
                'the',
                'parts',
                'portions',
            }
        ):
            return truncate(
                region,
                220,
            )

    return ''


def format_spc_issue_z(
    value: Any,
    fallback: Optional[
        datetime
    ] = None,
) -> str:
    dt = arcgis_datetime(
        value
    )

    if (
        dt is None
        and
        fallback is not None
    ):
        dt = fallback.astimezone(
            timezone.utc
        )

    if dt is None:
        return ''

    return (
        dt.astimezone(
            timezone.utc
        )
        .strftime(
            '%H%MZ'
        )
        .lower()
    )


def find_local_issue_clock(
    text: str,
) -> str:
    match = re.search(
        r'\b(\d{1,4})\s+'
        r'(AM|PM)\s+'
        r'([A-Z]{2,5})\s+'
        r'(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun)\b',
        text,
        re.I,
    )

    if not match:
        return ''

    digits, ampm, zone = match.groups()
    digits = digits.strip()

    if len(digits) <= 2:
        hour = int(
            digits
        )

        minute = 0

    elif len(digits) == 3:
        hour = int(
            digits[0]
        )

        minute = int(
            digits[1:]
        )

    else:
        hour = int(
            digits[:-2]
        )

        minute = int(
            digits[-2:]
        )

    return (
        f'{hour}:'
        f'{minute:02d} '
        f'{ampm.upper()} '
        f'{zone.upper()}'
    )


def find_spc_expiry_text(
    text: str,
) -> str:
    match = re.search(
        r'Expires:\s*'
        r'('
        r'[A-Za-z]{3}\s+'
        r'\d{1,2},\s*'
        r'\d{4}\s+'
        r'at\s+'
        r'\d{4}\s+UTC'
        r')',
        text,
        re.I,
    )

    if match:
        return match.group(
            1
        )

    valid = re.search(
        r'\bValid\s+'
        r'\d{6}Z\s*-\s*'
        r'(\d{6})Z\b',
        text,
        re.I,
    )

    if valid:
        return (
            f'{valid.group(1)}Z'
        )

    return ''


def spc_day_number(
    item: RSSItem,
) -> int:
    match = re.search(
        r'Day\s*([1-8])',
        f'{item.title} '
        f'{item.text}',
        re.I,
    )

    if not match:
        raise RetryableSourceDataError(
            'SPC convective item '
            'is missing a day number'
        )

    return int(
        match.group(
            1
        )
    )


def spc_percent_string(
    value: Any,
) -> str:
    text = squish(
        str(
            value
            or
            ''
        )
    )

    if not text:
        return ''

    if '%' in text:
        return text

    digits = digits_only(
        text
    )

    if digits:
        return (
            f'{int(digits)}%'
        )

    return text


def spc_max_label(
    features: list[
        dict[
            str,
            Any,
        ]
    ],
    *,
    categorical: bool = False,
) -> str:
    ranked: list[
        tuple[
            int,
            str,
        ]
    ] = []

    for feature in features:
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        label = first_nonempty(
            [
                attrs.get(
                    'label2'
                ),
                attrs.get(
                    'label'
                ),
            ]
        )

        dn_value = (
            attrs.get(
                'dn'
            )
        )

        if categorical:
            try:
                score = int(
                    dn_value
                )

            except Exception:
                label_digits = digits_only(
                    label
                )

                score = (
                    int(
                        label_digits
                    )
                    if
                    label_digits
                    else
                    0
                )

            if label:
                ranked.append(
                    (
                        score,
                        label,
                    )
                )

            continue

        score_text = (
            spc_percent_string(
                label
            )
            or
            spc_percent_string(
                dn_value
            )
        )

        digits = digits_only(
            score_text
        )

        if digits:
            ranked.append(
                (
                    int(
                        digits
                    ),
                    f'{int(digits)}%',
                )
            )

    if not ranked:
        return ''

    ranked.sort(
        key=lambda item:
            item[0]
    )

    return (
        ranked[-1][1]
    )


def default_spc_map_extent_for_day(
    day: int,
) -> tuple[
    float,
    float,
    float,
    float,
]:
    return (
        -128,
        22,
        -65,
        52,
    )


def web_mercator_to_lonlat(
    x: float,
    y: float,
) -> tuple[
    float,
    float,
]:
    radius = 6378137.0

    lon = math.degrees(
        x
        /
        radius
    )

    lat = math.degrees(
        2.0
        *
        math.atan(
            math.exp(
                y
                /
                radius
            )
        )
        -
        math.pi
        /
        2.0
    )

    return (
        lon,
        lat,
    )


def mapbox_camera_for_mercator_bbox(
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
) -> tuple[
    float,
    float,
    float,
]:
    minx, miny, maxx, maxy = bbox

    span_x = max(
        maxx
        -
        minx,
        1.0,
    )

    span_y = max(
        maxy
        -
        miny,
        1.0,
    )

    center_x = (
        minx
        +
        maxx
    ) / 2.0

    center_y = (
        miny
        +
        maxy
    ) / 2.0

    lon, lat = (
        web_mercator_to_lonlat(
            center_x,
            center_y,
        )
    )

    world_m = (
        2.0
        *
        math.pi
        *
        6378137.0
    )

    tile_size = 512.0

    zoom_x = math.log2(
        max(
            1.0,
            float(
                width
            )
            *
            world_m
            /
            (
                tile_size
                *
                span_x
            ),
        )
    )

    zoom_y = math.log2(
        max(
            1.0,
            float(
                height
            )
            *
            world_m
            /
            (
                tile_size
                *
                span_y
            ),
        )
    )

    zoom = min(
        zoom_x,
        zoom_y,
    )

    zoom = max(
        1.0,
        min(
            14.0,
            zoom,
        ),
    )

    return (
        lon,
        lat,
        zoom,
    )


def fetch_mapbox_light_base(
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
) -> Image.Image:
    if not MAPBOX_API_KEY:
        log.warning(
            'MAPBOX_API_KEY is not set; '
            'using plain fallback base map'
        )

        return Image.new(
            'RGBA',
            (
                width,
                height,
            ),
            (
                246,
                247,
                248,
                255,
            ),
        )

    lon, lat, zoom = (
        mapbox_camera_for_mercator_bbox(
            bbox,
            width,
            height,
        )
    )

    style = (
        MAPBOX_STYLE
        .strip(
            '/'
        )
    )

    if '/' not in style:
        style = (
            'mapbox/light-v11'
        )

    owner, style_id = (
        style.split(
            '/',
            1,
        )
    )

    url = (
        'https://api.mapbox.com/'
        'styles/v1/'
        f'{owner}/'
        f'{style_id}/'
        'static/'
        f'{lon:.6f},'
        f'{lat:.6f},'
        f'{zoom:.3f},0/'
        f'{width}x{height}'
    )

    base_params = {
        'access_token':
            MAPBOX_API_KEY
    }

    filtered_params = dict(
        base_params
    )

    filtered_params[
        'layer_id'
    ] = (
        'state-label'
    )

    filtered_params[
        'setfilter'
    ] = json.dumps(
        [
            '==',
            'name_en',
            '__PRIORITYWEATHER_HIDE_STATES__',
        ]
    )

    headers = {
        'Accept':
            'image/png,'
            'image/jpeg,*/*',

        'User-Agent':
            f'{BOT_NAME}/1.0 '
            f'({CONTACT_EMAIL})',
    }

    try:
        response = requests.get(
            url,
            params=filtered_params,
            headers=headers,
            timeout=(
                8,
                45,
            ),
        )

        if (
            response.status_code
            ==
            422
        ):
            log.warning(
                'Mapbox style has no usable '
                'state-label filter; '
                'requesting base style '
                'without filter'
            )

            response = requests.get(
                url,
                params=base_params,
                headers=headers,
                timeout=(
                    8,
                    45,
                ),
            )

        response.raise_for_status()

        return (
            Image.open(
                io.BytesIO(
                    response.content
                )
            )
            .convert(
                'RGBA'
            )
        )

    except Exception as exc:
        log.warning(
            'Mapbox static map failed; '
            'using fallback base map: %s',
            exc,
        )

        return Image.new(
            'RGBA',
            (
                width,
                height,
            ),
            (
                246,
                247,
                248,
                255,
            ),
        )


def scale_overlay_alpha(
    image: Image.Image,
    factor: float,
) -> Image.Image:
    factor = max(
        0.0,
        min(
            1.0,
            factor,
        ),
    )

    image = (
        image.copy()
        .convert(
            'RGBA'
        )
    )

    alpha = (
        image.getchannel(
            'A'
        )
        .point(
            lambda value:
                int(
                    value
                    *
                    factor
                )
        )
    )

    image.putalpha(
        alpha
    )

    return image


def add_reference_boundaries(
    base: Image.Image,
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    *,
    counties: bool,
    states: bool = True,
) -> Image.Image:
    width, height = (
        base.size
    )

    out = (
        base.copy()
        .convert(
            'RGBA'
        )
    )

    if counties:
        try:
            county_layer = (
                export_map_image(
                    REFERENCE_EXPORT_URL,
                    bbox,
                    width,
                    height,
                    layers='show:2',
                )
            )

            county_layer = (
                scale_overlay_alpha(
                    county_layer,
                    0.62,
                )
            )

            out.alpha_composite(
                county_layer
            )

        except Exception:
            log.exception(
                'Could not render '
                'NOAA county boundaries/names'
            )

    if states:
        try:
            state_features = (
                arcgis_query_features_in_bbox(
                    REFERENCE_MAPSERVER,
                    3,
                    bbox,
                    out_fields=
                        'objectid,state,name',
                    return_geometry=True,
                    out_sr=3857,
                )
            )

            draw = ImageDraw.Draw(
                out,
                'RGBA',
            )

            for feature in state_features:
                geometry = (
                    feature.get(
                        'geometry'
                    )
                    or
                    {}
                )

                for ring in (
                    arcgis_geometry_rings_mercator(
                        geometry,
                        default_wkid=3857,
                    )
                ):
                    pixels = (
                        mercator_ring_to_pixels(
                            ring,
                            bbox,
                            width,
                            height,
                        )
                    )

                    if len(
                        pixels
                    ) < 2:
                        continue

                    closed = (
                        pixels
                        +
                        [
                            pixels[0]
                        ]
                    )

                    draw.line(
                        closed,
                        fill=(
                            255,
                            255,
                            255,
                            235,
                        ),
                        width=7,
                        joint='curve',
                    )

                    draw.line(
                        closed,
                        fill=(
                            0,
                            0,
                            0,
                            255,
                        ),
                        width=5,
                        joint='curve',
                    )

        except Exception:
            log.exception(
                'Could not render custom '
                'NOAA state boundaries'
            )

    return out


def arcgis_geometry_rings_mercator(
    geometry: dict[
        str,
        Any,
    ],
    *,
    default_wkid: int,
) -> list[
    list[
        tuple[
            float,
            float,
        ]
    ]
]:
    spatial_reference = (
        geometry.get(
            'spatialReference'
        )
        or
        {}
    )

    wkid = int(
        spatial_reference.get(
            'latestWkid'
        )
        or
        spatial_reference.get(
            'wkid'
        )
        or
        default_wkid
    )

    rings_out: list[
        list[
            tuple[
                float,
                float,
            ]
        ]
    ] = []

    for ring in (
        geometry.get(
            'rings'
        )
        or
        []
    ):
        converted: list[
            tuple[
                float,
                float,
            ]
        ] = []

        for coordinate in ring:
            if (
                not isinstance(
                    coordinate,
                    (
                        list,
                        tuple,
                    ),
                )
                or
                len(
                    coordinate
                )
                <
                2
            ):
                continue

            x = float(
                coordinate[0]
            )

            y = float(
                coordinate[1]
            )

            if wkid in (
                4326,
                4269,
            ):
                converted.append(
                    lonlat_to_web_mercator(
                        x,
                        y,
                    )
                )

            else:
                converted.append(
                    (
                        x,
                        y,
                    )
                )

        if len(
            converted
        ) >= 3:
            rings_out.append(
                converted
            )

    return rings_out


def mercator_points_from_arcgis_geometry(
    geometry: dict[
        str,
        Any,
    ],
    *,
    default_wkid: int,
) -> list[
    tuple[
        float,
        float,
    ]
]:
    return [
        point
        for ring
        in
        arcgis_geometry_rings_mercator(
            geometry,
            default_wkid=
                default_wkid,
        )
        for point
        in ring
    ]


def mercator_bbox_from_points(
    points: list[
        tuple[
            float,
            float,
        ]
    ],
    width: int,
    height: int,
    *,
    padding_factor: float = 1.75,
    min_width_m: float = 120000.0,
    min_height_m: float = 90000.0,
) -> tuple[
    float,
    float,
    float,
    float,
]:
    if not points:
        raise RetryableSourceDataError(
            'No polygon coordinates '
            'were available'
        )

    xs = [
        point[0]
        for point
        in points
    ]

    ys = [
        point[1]
        for point
        in points
    ]

    minx = min(
        xs
    )

    maxx = max(
        xs
    )

    miny = min(
        ys
    )

    maxy = max(
        ys
    )

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

    raw_w = (
        max(
            maxx
            -
            minx,
            min_width_m,
        )
        *
        padding_factor
    )

    raw_h = (
        max(
            maxy
            -
            miny,
            min_height_m,
        )
        *
        padding_factor
    )

    aspect = (
        width
        /
        height
    )

    if (
        raw_w
        /
        raw_h
        <
        aspect
    ):
        raw_w = (
            raw_h
            *
            aspect
        )

    else:
        raw_h = (
            raw_w
            /
            aspect
        )

    return (
        cx
        -
        raw_w
        /
        2.0,

        cy
        -
        raw_h
        /
        2.0,

        cx
        +
        raw_w
        /
        2.0,

        cy
        +
        raw_h
        /
        2.0,
    )


def mercator_ring_to_pixels(
    ring: list[
        tuple[
            float,
            float,
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
    minx, miny, maxx, maxy = bbox

    span_x = max(
        maxx
        -
        minx,
        1.0,
    )

    span_y = max(
        maxy
        -
        miny,
        1.0,
    )

    result: list[
        tuple[
            int,
            int,
        ]
    ] = []

    for x, y in ring:
        px = int(
            round(
                (
                    x
                    -
                    minx
                )
                /
                span_x
                *
                (
                    width
                    -
                    1
                )
            )
        )

        py = int(
            round(
                (
                    maxy
                    -
                    y
                )
                /
                span_y
                *
                (
                    height
                    -
                    1
                )
            )
        )

        result.append(
            (
                px,
                py,
            )
        )

    return result


def draw_red_outline_geometry(
    base: Image.Image,
    geometry: dict[
        str,
        Any,
    ],
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    *,
    default_wkid: int,
    line_width: int = 7,
) -> Image.Image:
    out = (
        base.copy()
        .convert(
            'RGBA'
        )
    )

    draw = ImageDraw.Draw(
        out,
        'RGBA',
    )

    width, height = (
        out.size
    )

    rings = (
        arcgis_geometry_rings_mercator(
            geometry,
            default_wkid=
                default_wkid,
        )
    )

    if not rings:
        raise RetryableSourceDataError(
            'Product geometry contained '
            'no drawable rings'
        )

    for ring in rings:
        pixels = (
            mercator_ring_to_pixels(
                ring,
                bbox,
                width,
                height,
            )
        )

        if len(
            pixels
        ) < 3:
            continue

        closed = (
            pixels
            +
            [
                pixels[0]
            ]
        )

        draw.line(
            closed,
            fill=(
                255,
                255,
                255,
                245,
            ),
            width=
                line_width
                +
                4,
            joint='curve',
        )

        draw.line(
            closed,
            fill=(
                214,
                0,
                0,
                255,
            ),
            width=
                line_width,
            joint='curve',
        )

    return out


def draw_union_red_outline_geometry(
    base: Image.Image,
    geometry: dict[
        str,
        Any,
    ],
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    *,
    default_wkid: int,
    line_width: int = 7,
) -> Image.Image:
    out = (
        base.copy()
        .convert(
            'RGBA'
        )
    )

    width, height = (
        out.size
    )

    rings = (
        arcgis_geometry_rings_mercator(
            geometry,
            default_wkid=
                default_wkid,
        )
    )

    if not rings:
        raise RetryableSourceDataError(
            'Product geometry contained '
            'no drawable rings'
        )

    mask = Image.new(
        'L',
        (
            width,
            height,
        ),
        0,
    )

    mask_draw = ImageDraw.Draw(
        mask
    )

    for ring in rings:
        pixels = (
            mercator_ring_to_pixels(
                ring,
                bbox,
                width,
                height,
            )
        )

        if len(
            pixels
        ) >= 3:
            mask_draw.polygon(
                pixels,
                fill=255,
            )

    mask = (
        mask
        .filter(
            ImageFilter.MaxFilter(
                3
            )
        )
        .filter(
            ImageFilter.MinFilter(
                3
            )
        )
    )

    red_radius = max(
        2,
        line_width
        //
        2,
    )

    halo_radius = (
        red_radius
        +
        3
    )

    red_outer = mask.filter(
        ImageFilter.MaxFilter(
            red_radius
            *
            2
            +
            1
        )
    )

    red_inner = mask.filter(
        ImageFilter.MinFilter(
            red_radius
            *
            2
            +
            1
        )
    )

    red_mask = ImageChops.subtract(
        red_outer,
        red_inner,
    )

    halo_outer = mask.filter(
        ImageFilter.MaxFilter(
            halo_radius
            *
            2
            +
            1
        )
    )

    halo_inner = mask.filter(
        ImageFilter.MinFilter(
            halo_radius
            *
            2
            +
            1
        )
    )

    halo_mask = ImageChops.subtract(
        halo_outer,
        halo_inner,
    )

    white = Image.new(
        'RGBA',
        (
            width,
            height,
        ),
        (
            255,
            255,
            255,
            245,
        ),
    )

    red = Image.new(
        'RGBA',
        (
            width,
            height,
        ),
        (
            214,
            0,
            0,
            255,
        ),
    )

    out.alpha_composite(
        Image.composite(
            white,
            Image.new(
                'RGBA',
                (
                    width,
                    height,
                ),
                (
                    0,
                    0,
                    0,
                    0,
                ),
            ),
            halo_mask,
        )
    )

    out.alpha_composite(
        Image.composite(
            red,
            Image.new(
                'RGBA',
                (
                    width,
                    height,
                ),
                (
                    0,
                    0,
                    0,
                    0,
                ),
            ),
            red_mask,
        )
    )

    return out


def save_map_image(
    image: Image.Image,
    *,
    prefix: str,
) -> str:
    tmp = (
        tempfile.NamedTemporaryFile(
            prefix=prefix,
            suffix='.jpg',
            delete=False,
        )
    )

    tmp.close()

    image.convert(
        'RGB'
    ).save(
        tmp.name,
        'JPEG',
        quality=92,
        optimize=True,
    )

    return tmp.name


def build_mapbox_product_outline_map(
    geometry: dict[
        str,
        Any,
    ],
    *,
    default_wkid: int,
    padding_factor: float,
    min_width_m: float,
    min_height_m: float,
    prefix: str,
    show_counties: bool,
    line_width: int,
) -> str:
    width = 1200
    height = 760

    points = (
        mercator_points_from_arcgis_geometry(
            geometry,
            default_wkid=
                default_wkid,
        )
    )

    bbox = mercator_bbox_from_points(
        points,
        width,
        height,
        padding_factor=
            padding_factor,
        min_width_m=
            min_width_m,
        min_height_m=
            min_height_m,
    )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    base = add_reference_boundaries(
        base,
        bbox,
        counties=
            show_counties,
        states=True,
    )

    base = draw_red_outline_geometry(
        base,
        geometry,
        bbox,
        default_wkid=
            default_wkid,
        line_width=
            line_width,
    )

    return save_map_image(
        base,
        prefix=prefix,
    )


def build_mapbox_watch_outline_map(
    geometry: dict[
        str,
        Any,
    ],
) -> str:
    width = 1200
    height = 760

    points = (
        mercator_points_from_arcgis_geometry(
            geometry,
            default_wkid=3857,
        )
    )

    bbox = mercator_bbox_from_points(
        points,
        width,
        height,
        padding_factor=1.48,
        min_width_m=900000.0,
        min_height_m=560000.0,
    )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    base = add_reference_boundaries(
        base,
        bbox,
        counties=True,
        states=True,
    )

    base = (
        draw_union_red_outline_geometry(
            base,
            geometry,
            bbox,
            default_wkid=3857,
            line_width=7,
        )
    )

    return save_map_image(
        base,
        prefix='spc_watch_',
    )


def build_mapbox_spc_outlook_map(
    day: int,
    image_layer: int,
    primary_features: list[
        dict[
            str,
            Any,
        ]
    ],
) -> str:
    width = 1200
    height = 760

    all_points: list[
        tuple[
            float,
            float,
        ]
    ] = []

    for feature in primary_features:
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if geometry:
            all_points.extend(
                mercator_points_from_arcgis_geometry(
                    geometry,
                    default_wkid=3857,
                )
            )

    if all_points:
        if day <= 2:
            padding_factor = 1.42
            min_width_m = 3000000.0
            min_height_m = 1800000.0

        elif day == 3:
            padding_factor = 1.35
            min_width_m = 3600000.0
            min_height_m = 2100000.0

        else:
            padding_factor = 1.30
            min_width_m = 4200000.0
            min_height_m = 2400000.0

        bbox = mercator_bbox_from_points(
            all_points,
            width,
            height,
            padding_factor=
                padding_factor,
            min_width_m=
                min_width_m,
            min_height_m=
                min_height_m,
        )

    else:
        bbox = mercator_bbox_from_lonlat(
            *default_spc_map_extent_for_day(
                day
            )
        )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    product = export_map_image(
        f'{SPC_OUTLOOK_MAPSERVER}/export',
        bbox,
        width,
        height,
        layers=
            f'show:{image_layer}',
    )

    base.alpha_composite(
        product
    )

    base = add_reference_boundaries(
        base,
        bbox,
        counties=False,
        states=True,
    )

    return save_map_image(
        base,
        prefix=
            f'spc_day{day}_',
    )


def build_mapbox_wpc_ero_map(
    day: int,
) -> str:
    width = 1200
    height = 760
    layer = day - 1

    features = arcgis_query_features(
        WPC_ERO_MAPSERVER,
        layer,
        out_fields='*',
        return_geometry=True,
        out_sr=3857,
    )

    all_points: list[
        tuple[
            float,
            float,
        ]
    ] = []

    for feature in features:
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if geometry:
            all_points.extend(
                mercator_points_from_arcgis_geometry(
                    geometry,
                    default_wkid=3857,
                )
            )

    if all_points:
        bbox = mercator_bbox_from_points(
            all_points,
            width,
            height,
            padding_factor=1.42,
            min_width_m=3200000.0,
            min_height_m=1900000.0,
        )

    else:
        bbox = mercator_bbox_from_lonlat(
            -128,
            22,
            -65,
            52,
        )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    product = export_map_image(
        f'{WPC_ERO_MAPSERVER}/export',
        bbox,
        width,
        height,
        layers=
            f'show:{layer}',
    )

    base.alpha_composite(
        product
    )

    base = add_reference_boundaries(
        base,
        bbox,
        counties=False,
        states=True,
    )

    return save_map_image(
        base,
        prefix=
            f'wpc_ero_d{day}_',
    )


def find_matching_mcd_feature(
    number: str,
) -> Optional[
    SPCGeometryMatch
]:
    features = arcgis_query_features(
        SPC_MCD_MAPSERVER,
        0,
        out_fields=(
            'objectid,name,folderpath,'
            'popupinfo,idp_filedate,'
            'idp_ingestdate'
        ),
        return_geometry=True,
    )

    target = digits_only(
        number
    )

    candidates: list[
        SPCGeometryMatch
    ] = []

    for feature in features:
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        feature_number = (
            digits_only(
                attrs.get(
                    'name'
                )
            )
        )

        if (
            target
            and
            feature_number
            !=
            target
        ):
            continue

        name_text = str(
            attrs.get(
                'name'
            )
            or
            ''
        )

        if (
            name_text
            and
            'noarea'
            in
            name_text.lower()
        ):
            continue

        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if not geometry.get(
            'rings'
        ):
            continue

        candidates.append(
            SPCGeometryMatch(
                dict(
                    attrs
                ),
                dict(
                    geometry
                ),
            )
        )

    if not candidates:
        return None

    candidates.sort(
        key=lambda match:
            str(
                match.attributes.get(
                    'idp_ingestdate'
                )
                or
                match.attributes.get(
                    'idp_filedate'
                )
                or
                ''
            )
    )

    return candidates[-1]


def find_matching_watch_feature(
    product_name: str,
    number: str,
) -> Optional[
    SPCGeometryMatch
]:
    prod_type = (
        'Tornado Watch'
        if
        'tornado'
        in
        product_name.lower()
        else
        'Severe Thunderstorm Watch'
    )

    features = arcgis_query_features(
        WWA_MAPSERVER,
        1,
        where=(
            'prod_type = '
            +
            sql_quote(
                prod_type
            )
        ),
        out_fields=(
            'prod_type,msg_type,phenom,'
            'url,expiration,onset,ends,'
            'issuance,event,sig,wfo,'
            'idp_filedate,idp_ingestdate,'
            'cap_id'
        ),
        return_geometry=True,
        out_sr=3857,
    )

    target = digits_only(
        number
    ).lstrip(
        '0'
    )

    candidates: list[
        SPCGeometryMatch
    ] = []

    for feature in features:
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        if (
            squish(
                str(
                    attrs.get(
                        'prod_type'
                    )
                    or
                    ''
                )
            )
            !=
            prod_type
        ):
            continue

        feature_number = digits_only(
            attrs.get(
                'event'
            )
        ).lstrip(
            '0'
        )

        if (
            target
            and
            feature_number
            !=
            target
        ):
            continue

        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if not geometry.get(
            'rings'
        ):
            continue

        candidates.append(
            SPCGeometryMatch(
                dict(
                    attrs
                ),
                dict(
                    geometry
                ),
            )
        )

    if not candidates:
        return None

    candidates.sort(
        key=lambda match:
            str(
                match.attributes.get(
                    'idp_ingestdate'
                )
                or
                match.attributes.get(
                    'idp_filedate'
                )
                or
                ''
            )
    )

    merged_rings: list[
        Any
    ] = []

    for candidate in candidates:
        merged_rings.extend(
            candidate.geometry.get(
                'rings'
            )
            or
            []
        )

    latest = (
        candidates[-1]
    )

    merged_attrs = dict(
        latest.attributes
    )

    merged_attrs[
        '_piece_count'
    ] = len(
        candidates
    )

    merged_geometry = {
        'rings':
            merged_rings,

        'spatialReference':
            (
                latest.geometry.get(
                    'spatialReference'
                )
                or
                {
                    'wkid':
                        3857
                }
            ),
    }

    return SPCGeometryMatch(
        merged_attrs,
        merged_geometry,
    )


def build_mcd_image(
    feature: SPCGeometryMatch,
) -> str:
    return (
        build_mapbox_product_outline_map(
            feature.geometry,
            default_wkid=4326,
            padding_factor=2.35,
            min_width_m=280000.0,
            min_height_m=190000.0,
            prefix='spc_md_',
            show_counties=True,
            line_width=7,
        )
    )


def build_watch_image(
    feature: SPCGeometryMatch,
) -> str:
    return (
        build_mapbox_watch_outline_map(
            feature.geometry
        )
    )


@dataclass(
    frozen=True
)
class WatchProbabilities:
    tornadoes: str
    strong_tornadoes: str
    severe_wind: str
    significant_wind: str
    severe_hail: str
    significant_hail: str
    combined: str


def normalize_watch_probability(
    value: str,
) -> str:
    value = (
        squish(
            value
        )
        .replace(
            ' ',
            ''
        )
    )

    match = re.match(
        r'([<>]?)(\d+)',
        value,
    )

    if not match:
        return ''

    prefix, digits = (
        match.groups()
    )

    return (
        f'{prefix}'
        f'{int(digits)}%'
    )


def watch_probability_level(
    value: str,
) -> str:
    normalized = (
        normalize_watch_probability(
            value
        )
    )

    digits = digits_only(
        normalized
    )

    if not digits:
        return ''

    probability = int(
        digits
    )

    if probability <= 5:
        return 'Very Low'

    if probability <= 20:
        return 'Low'

    if probability <= 60:
        return 'Moderate'

    return 'High'


def parse_watch_probabilities(
    text: str,
) -> Optional[
    WatchProbabilities
]:
    def grab(
        pattern: str,
    ) -> str:
        match = re.search(
            pattern
            +
            r'\s*:\s*'
            r'([<>]?\s*\d+)'
            r'\s*%',
            text,
            re.I,
        )

        return (
            normalize_watch_probability(
                match.group(
                    1
                )
            )
            if match
            else
            ''
        )

    values = WatchProbabilities(
        tornadoes=
            grab(
                r'PROB OF 2 OR MORE '
                r'TORNADOES'
            ),

        strong_tornadoes=
            grab(
                r'PROB OF 1 OR MORE STRONG'
                r'\s*/?EF2-EF5/?\s*'
                r'TORNADOES'
            ),

        severe_wind=
            grab(
                r'PROB OF 10 OR MORE '
                r'SEVERE WIND EVENTS'
            ),

        significant_wind=
            grab(
                r'PROB OF 1 OR MORE '
                r'WIND EVENTS\s*'
                r'(?:>=|>)\s*'
                r'(?:65\s*KNOTS|75\s*MPH)'
            ),

        severe_hail=
            grab(
                r'PROB OF 10 OR MORE '
                r'SEVERE HAIL EVENTS'
            ),

        significant_hail=
            grab(
                r'PROB OF 1 OR MORE '
                r'(?:HAIL EVENTS|HAILSTONES)'
                r'\s*(?:>=|>)\s*'
                r'2\s*INCH(?:ES)?'
            ),

        combined=
            grab(
                r'PROB OF 6 OR MORE '
                r'COMBINED SEVERE '
                r'HAIL/WIND EVENTS'
            ),
    )

    return (
        values
        if
        any(
            values.__dict__.values()
        )
        else
        None
    )


def fetch_watch_probabilities(
    number: str,
) -> WatchProbabilities:
    target = digits_only(
        number
    ).lstrip(
        '0'
    )

    if not target:
        raise RetryableSourceDataError(
            'Watch number was unavailable '
            'for probability lookup'
        )

    response = http_get(
        NWS_PRODUCTS_URL,
        params={
            'type':
                'WWP',

            'limit':
                50,
        },
        headers={
            'Accept':
                'application/ld+json,'
                'application/json'
        },
        timeout=(
            8,
            35,
        ),
    )

    payload = response.json()

    graph = (
        payload.get(
            '@graph'
        )
        or
        payload.get(
            'products'
        )
        or
        payload.get(
            'features'
        )
        or
        []
    )

    if not isinstance(
        graph,
        list,
    ):
        graph = []

    def issuance(
        item: dict[
            str,
            Any,
        ],
    ) -> datetime:
        return (
            parse_any_datetime(
                str(
                    item.get(
                        'issuanceTime'
                    )
                    or
                    item.get(
                        'issuance_time'
                    )
                    or
                    ''
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

    graph = [
        item
        for item
        in graph
        if isinstance(
            item,
            dict,
        )
    ]

    graph.sort(
        key=issuance,
        reverse=True,
    )

    for item in graph:
        issued = issuance(
            item
        )

        if (
            issued.year
            >
            1970
            and
            utcnow()
            -
            issued
            >
            timedelta(
                hours=30
            )
        ):
            continue

        reference = str(
            item.get(
                '@id'
            )
            or
            item.get(
                'id'
            )
            or
            ''
        ).strip()

        if not reference:
            continue

        detail_url = (
            reference
            if
            reference.startswith(
                (
                    'http://',
                    'https://',
                )
            )
            else
            f'https://api.weather.gov/'
            f'products/{reference}'
        )

        try:
            detail = (
                http_get(
                    detail_url,
                    headers={
                        'Accept':
                            'application/ld+json,'
                            'application/json'
                    },
                    timeout=(
                        8,
                        35,
                    ),
                )
                .json()
            )

        except Exception:
            continue

        text = str(
            detail.get(
                'productText'
            )
            or
            detail.get(
                'product_text'
            )
            or
            ''
        )

        watch_match = re.search(
            r'\b(?:WT|WS|WATCH)\s+'
            r'0*(\d{1,4})\b',
            text,
            re.I,
        )

        if (
            not watch_match
            or
            watch_match.group(
                1
            ).lstrip(
                '0'
            )
            !=
            target
        ):
            continue

        parsed = (
            parse_watch_probabilities(
                text
            )
        )

        if parsed:
            return parsed

    raise RetryableSourceDataError(
        f'Watch {number} '
        'hazard probability product '
        'was not ready yet'
    )


def watch_probability_summary(
    probabilities: WatchProbabilities,
) -> str:
    parts = [
        f'Tornadoes '
        f'{watch_probability_level(probabilities.tornadoes)}',

        f'EF2+ '
        f'{watch_probability_level(probabilities.strong_tornadoes)}',

        f'Severe wind '
        f'{watch_probability_level(probabilities.severe_wind)}',

        f'65+ kt wind '
        f'{watch_probability_level(probabilities.significant_wind)}',

        f'Severe hail '
        f'{watch_probability_level(probabilities.severe_hail)}',

        f'2+ in hail '
        f'{watch_probability_level(probabilities.significant_hail)}',
    ]

    return (
        'Likelihoods: '
        +
        ' | '.join(
            part
            for part
            in parts
            if not part.endswith(
                ' '
            )
        )
    )


def arcgis_datetime(
    value: Any,
) -> Optional[
    datetime
]:
    if (
        value is None
        or
        value == ''
    ):
        return None

    if (
        isinstance(
            value,
            (
                int,
                float,
            ),
        )
        or
        re.fullmatch(
            r'\d{10,13}(?:\.\d+)?',
            str(value).strip(),
        )
    ):
        raw = float(
            value
        )

        if raw > 100000000000:
            raw /= 1000.0

        try:
            return datetime.fromtimestamp(
                raw,
                tz=timezone.utc,
            )

        except Exception:
            return None

    return parse_any_datetime(
        str(
            value
        )
    )


def format_datetime_in_abbrev(
    value: Any,
    abbreviation: str,
) -> str:
    dt = arcgis_datetime(
        value
    )

    if not dt:
        return ''

    offsets = {
        'EDT': -4,
        'EST': -5,

        'CDT': -5,
        'CST': -6,

        'MDT': -6,
        'MST': -7,

        'PDT': -7,
        'PST': -8,

        'AKDT': -8,
        'AKST': -9,

        'HST': -10,
    }

    abbreviation = (
        abbreviation
        .upper()
        .strip()
    )

    offset = offsets.get(
        abbreviation
    )

    if offset is None:
        return dt.strftime(
            '%-I:%M %p UTC'
        )

    local_tz = timezone(
        timedelta(
            hours=offset
        ),
        name=
            abbreviation,
    )

    return (
        dt.astimezone(
            local_tz
        )
        .strftime(
            f'%-I:%M %p '
            f'{abbreviation}'
        )
    )


def load_convective_snapshot(
    day: int,
) -> SPCConvectiveSnapshot:
    layer_ids = (
        SPC_OUTLOOK_LAYER_IDS.get(
            day
        )
    )

    if not layer_ids:
        raise RetryableSourceDataError(
            f'No SPC outlook layer '
            f'mapping exists for day {day}'
        )

    primary_layer = (
        layer_ids.get(
            'categorical'
        )
        or
        layer_ids.get(
            'probability'
        )
    )

    if primary_layer is None:
        raise RetryableSourceDataError(
            f'SPC Day {day} has no '
            'usable GIS layer mapping'
        )

    category_features = (
        arcgis_query_features(
            SPC_OUTLOOK_MAPSERVER,
            primary_layer,
            out_fields=(
                'objectid,dn,valid,expire,'
                'idp_source,idp_filedate,'
                'idp_ingestdate,issue,'
                'label,label2,stroke,fill'
            ),
            return_geometry=True,
            out_sr=3857,
        )
    )

    if not category_features:
        raise RetryableSourceDataError(
            f'SPC Day {day} GIS data '
            'was not ready yet'
        )

    category = (
        spc_max_label(
            category_features,
            categorical=True,
        )
        if
        'categorical'
        in
        layer_ids
        else
        ''
    )

    issued = first_nonempty(
        [
            (
                feature.get(
                    'attributes'
                )
                or
                {}
            ).get(
                'issue'
            )
            for feature
            in category_features
        ]
    )

    valid = first_nonempty(
        [
            (
                feature.get(
                    'attributes'
                )
                or
                {}
            ).get(
                'valid'
            )
            for feature
            in category_features
        ]
    )

    tornado_risk = ''
    hail_risk = ''
    wind_risk = ''
    severe_risk = ''

    if day in (
        1,
        2,
    ):
        tornado_risk = spc_max_label(
            arcgis_query_features(
                SPC_OUTLOOK_MAPSERVER,
                layer_ids[
                    'tornado'
                ],
                out_fields=(
                    'objectid,dn,label,'
                    'label2,issue,valid,'
                    'idp_ingestdate'
                ),
                return_geometry=False,
            )
        )

        hail_risk = spc_max_label(
            arcgis_query_features(
                SPC_OUTLOOK_MAPSERVER,
                layer_ids[
                    'hail'
                ],
                out_fields=(
                    'objectid,dn,label,'
                    'label2,issue,valid,'
                    'idp_ingestdate'
                ),
                return_geometry=False,
            )
        )

        wind_risk = spc_max_label(
            arcgis_query_features(
                SPC_OUTLOOK_MAPSERVER,
                layer_ids[
                    'wind'
                ],
                out_fields=(
                    'objectid,dn,label,'
                    'label2,issue,valid,'
                    'idp_ingestdate'
                ),
                return_geometry=False,
            )
        )

        if not any(
            (
                tornado_risk,
                hail_risk,
                wind_risk,
            )
        ):
            raise RetryableSourceDataError(
                f'SPC Day {day} '
                'probability layers '
                'were not ready yet'
            )

    elif day == 3:
        severe_risk = spc_max_label(
            arcgis_query_features(
                SPC_OUTLOOK_MAPSERVER,
                layer_ids[
                    'severe'
                ],
                out_fields=(
                    'objectid,dn,label,'
                    'label2,issue,valid,'
                    'idp_ingestdate'
                ),
                return_geometry=False,
            )
        )

        if not severe_risk:
            raise RetryableSourceDataError(
                'SPC Day 3 severe '
                'probability layer '
                'was not ready yet'
            )

    image_layer = (
        layer_ids.get(
            'categorical'
        )
        or
        layer_ids.get(
            'probability'
        )
    )

    image_path = (
        build_mapbox_spc_outlook_map(
            day,
            image_layer,
            category_features,
        )
    )

    if not image_path:
        raise RetryableSourceDataError(
            f'Could not render '
            f'SPC Day {day} outlook image'
        )

    return SPCConvectiveSnapshot(
        day=day,
        category=category,
        tornado_risk=
            tornado_risk,
        wind_risk=
            wind_risk,
        hail_risk=
            hail_risk,
        severe_risk=
            severe_risk,
        image_path=
            image_path,
        issued=
            issued,
        valid=
            valid,
    )


def render_spc(
    item: RSSItem,
    kind: str,
) -> Optional[
    RenderedPost
]:
    product_name, number = (
        spc_product_name(
            item,
            kind,
        )
    )

    page_text = (
        item.multiline_text
    )

    soup: Optional[
        BeautifulSoup
    ] = None

    if item.link:
        try:
            page_text, soup = (
                fetch_product_page(
                    item.link
                )
            )

        except Exception:
            log.exception(
                'Could not fetch SPC '
                'product page: %s',
                item.link,
            )

    location = spc_location(
        page_text,
        kind,
    )

    issued = find_local_issue_clock(
        page_text
    )

    expires = find_spc_expiry_text(
        page_text
    )

    time_line = ''

    if (
        issued
        and
        expires
    ):
        time_line = (
            f'Issued {issued} '
            f'Expires {expires}'
        )

    elif issued:
        time_line = (
            f'Issued {issued}'
        )

    elif item.published:
        time_line = (
            'Issued '
            +
            item.published.strftime(
                '%-I:%M %p UTC'
            )
        )

    details: list[str] = []
    image_path = ''

    if kind == 'convective':
        day = spc_day_number(
            item
        )

        snapshot = (
            load_convective_snapshot(
                day
            )
        )

        image_path = (
            snapshot.image_path
        )

        issue_z = format_spc_issue_z(
            snapshot.issued,
            item.published,
        )

        risk_region = spc_convective_risk_location(
            page_text,
            snapshot.category,
        )

        category_name = re.sub(
            r'\s+Risk\s*$',
            '',
            squish(
                snapshot.category
            ),
            flags=re.I,
        ).title()

        post_lines: list[str] = [
            product_name,
            (
                f'Issued at {issue_z}'
                if issue_z
                else
                time_line
            ),
        ]

        if (
            category_name
            and
            risk_region
        ):
            post_lines.append(
                f'{category_name} risks in '
                f'{risk_region}'
            )

        elif snapshot.category:
            post_lines.append(
                snapshot.category
            )

        if day in (
            1,
            2,
        ):
            post_lines.append(
                'Max Hazard Probabilities: '
                f'Tornado '
                f'{snapshot.tornado_risk or "N/A"} | '
                f'Wind '
                f'{snapshot.wind_risk or "N/A"} | '
                f'Hail '
                f'{snapshot.hail_risk or "N/A"}'
            )

        elif day == 3:
            post_lines.append(
                'Max Severe Probability: '
                +
                (
                    snapshot.severe_risk
                    or
                    'N/A'
                )
            )

        elif day >= 4:
            probability_layer = (
                SPC_OUTLOOK_LAYER_IDS[
                    day
                ][
                    'probability'
                ]
            )

            probability_risk = (
                spc_max_label(
                    arcgis_query_features(
                        SPC_OUTLOOK_MAPSERVER,
                        probability_layer,
                        out_fields=(
                            'objectid,dn,label,'
                            'label2,issue,valid,'
                            'idp_ingestdate'
                        ),
                        return_geometry=False,
                    )
                )
            )

            if probability_risk:
                post_lines.append(
                    'Max Severe Probability: '
                    +
                    probability_risk
                )

        if not image_path:
            raise RetryableSourceDataError(
                f'SPC Day {day} image '
                'was not ready yet'
            )

        return RenderedPost(
            fit_post(
                post_lines,
                item.link,
            ),
            image_path,
        )

    if kind == 'md':
        concerning = spc_field(
            page_text,
            'Concerning',
        )

        if concerning:
            details.append(
                'Concerning: '
                +
                truncate(
                    concerning,
                    140,
                )
            )

        probability = re.search(
            r'Probability of Watch Issuance'
            r'\s*\.{3}\s*'
            r'(\d+)\s*percent',
            page_text,
            re.I,
        )

        if probability:
            details.append(
                f'Watch probability: '
                f'{probability.group(1)}%'
            )

        match = (
            find_matching_mcd_feature(
                number
            )
        )

        if not match:
            raise RetryableSourceDataError(
                f'MCD '
                f'{number or product_name} '
                'polygon GIS data '
                'was not ready yet'
            )

        image_path = (
            build_mcd_image(
                match
            )
        )

        if not image_path:
            raise RetryableSourceDataError(
                f'MCD '
                f'{number or product_name} '
                'image could not be rendered'
            )

    elif kind == 'watch':
        match = (
            find_matching_watch_feature(
                product_name,
                number,
            )
        )

        if not match:
            raise RetryableSourceDataError(
                f'Watch '
                f'{number or product_name} '
                'polygon GIS data '
                'was not ready yet'
            )

        probabilities = (
            fetch_watch_probabilities(
                number
            )
        )

        details.append(
            watch_probability_summary(
                probabilities
            )
        )

        zone_match = re.search(
            r'\b([ECMPAH][DS]T)\b',
            issued
            or
            '',
        )

        zone = (
            zone_match.group(
                1
            )
            if
            zone_match
            else
            'UTC'
        )

        if not issued:
            issued_from_gis = (
                format_datetime_in_abbrev(
                    match.attributes.get(
                        'issuance'
                    ),
                    zone,
                )
            )

            if issued_from_gis:
                issued = (
                    issued_from_gis
                )

        if not expires:
            expires_from_gis = (
                format_datetime_in_abbrev(
                    match.attributes.get(
                        'expiration'
                    )
                    or
                    match.attributes.get(
                        'ends'
                    ),
                    zone,
                )
            )

            if expires_from_gis:
                expires = (
                    expires_from_gis
                )

        if (
            issued
            and
            expires
        ):
            time_line = (
                f'Issued {issued} '
                f'Expires {expires}'
            )

        elif issued:
            time_line = (
                f'Issued {issued}'
            )

        image_path = (
            build_watch_image(
                match
            )
        )

        if not image_path:
            raise RetryableSourceDataError(
                f'Watch '
                f'{number or product_name} '
                'image could not be rendered'
            )

    elif (
        soup
        is not None
        and
        item.link
    ):
        try:
            image_path = (
                page_product_image(
                    item.link,
                    soup,
                    kind,
                    number,
                )
            )

        except Exception:
            log.exception(
                'Could not obtain '
                'SPC image for %s',
                product_name,
            )

    hazards = extract_hazards(
        page_text,
        product_name,
    )

    if (
        hazards
        and
        kind
        not in (
            'convective',
            'watch',
        )
    ):
        details.append(
            'Hazards: '
            +
            ', '.join(
                hazards
            )
        )

    return RenderedPost(
        fit_post(
            [
                product_name,
                location,
                time_line,
                *details,
            ],
            item.link,
        ),
        image_path,
    )


def poll_spc(
    db: StateDB,
    x: XPublisher,
) -> None:
    for source, (
        url,
        kind,
    ) in SPC_FEEDS.items():
        try:
            process_rss_source(
                db,
                x,
                source=source,
                url=url,
                item_filter=
                    lambda item, k=kind:
                        spc_item_is_real(
                            item,
                            k,
                        ),
                renderer=
                    lambda item, k=kind:
                        render_spc(
                            item,
                            k,
                        ),
            )

        except Exception:
            log.exception(
                'SPC source failed: %s',
                source,
            )


def build_nhc_basin_sources(
    basin: str,
) -> list[
    tuple[
        str,
        str,
        str,
        str,
    ]
]:
    code = (
        NHC_BASIN_CODES[
            basin
        ]
    )

    out: list[
        tuple[
            str,
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
                f'nhc_tcp_'
                f'{basin}_'
                f'{wallet}',

                'https://'
                'www.nhc.noaa.gov/'
                f'xml/TCP'
                f'{code}'
                f'{wallet}.xml',

                'tcp',

                basin,
            )
        )

        out.append(
            (
                f'nhc_tcu_'
                f'{basin}_'
                f'{wallet}',

                'https://'
                'www.nhc.noaa.gov/'
                f'xml/TCU'
                f'{code}'
                f'{wallet}.xml',

                'tcu',

                basin,
            )
        )

        if ENABLE_NHC_DISCUSSIONS:
            out.append(
                (
                    f'nhc_tcd_'
                    f'{basin}_'
                    f'{wallet}',

                    'https://'
                    'www.nhc.noaa.gov/'
                    f'xml/TCD'
                    f'{code}'
                    f'{wallet}.xml',

                    'tcd',

                    basin,
                )
            )

        if ENABLE_NHC_FORECAST_ADVISORIES:
            out.append(
                (
                    f'nhc_tcm_'
                    f'{basin}_'
                    f'{wallet}',

                    'https://'
                    'www.nhc.noaa.gov/'
                    f'xml/TCM'
                    f'{code}'
                    f'{wallet}.xml',

                    'tcm',

                    basin,
                )
            )

    return out


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
        f'{item.title} '
        f'{item.text}'
    ).lower()

    if (
        'tropical weather outlook'
        in
        combined
    ):
        return True

    return not any(
        marker
        in
        combined
        for marker
        in (
            'no tropical cyclones',
            'there are no tropical cyclones',
            'no active tropical cyclones',
            'no tropical cyclone updates',
        )
    )


def find_nhc_field(
    text: str,
    field: str,
) -> str:
    match = re.search(
        rf'(?im)^'
        rf'\s*'
        rf'{re.escape(field)}'
        rf'\s*'
        rf'\.{{2,}}'
        rf'\s*'
        rf'(.+?)'
        rf'\s*$',
        text,
    )

    return (
        squish(
            match.group(
                1
            )
        )
        if match
        else
        ''
    )


def nhc_center_location(
    text: str,
) -> str:
    location = find_nhc_field(
        text,
        'LOCATION',
    )

    if location:
        return location

    match = re.search(
        r'(?i)'
        r'center '
        r'(?:was |is )?'
        r'located near\s+'
        r'('
        r'[0-9.]+[NS]\s+'
        r'[0-9.]+[EW]'
        r')',
        text,
    )

    return (
        squish(
            match.group(
                1
            )
        )
        if match
        else
        ''
    )


def nhc_coordinate_value(
    token: str,
) -> Optional[float]:
    match = re.fullmatch(
        r'\s*'
        r'([0-9]+(?:\.[0-9]+)?)'
        r'\s*'
        r'([NSEW])'
        r'\s*',
        token,
        re.I,
    )

    if not match:
        return None

    value = float(
        match.group(
            1
        )
    )

    hemisphere = (
        match.group(
            2
        )
        .upper()
    )

    if hemisphere in {
        'S',
        'W',
    }:
        value *= -1.0

    return value


def nhc_lonlat_from_text(
    text: str,
) -> tuple[
    Optional[float],
    Optional[float],
]:
    candidates = [
        nhc_center_location(
            text
        ),
        text,
    ]

    for candidate in candidates:
        if not candidate:
            continue

        match = re.search(
            r'('
            r'[0-9]+(?:\.[0-9]+)?'
            r'\s*[NS]'
            r')'
            r'[^0-9A-Z]+'
            r'('
            r'[0-9]+(?:\.[0-9]+)?'
            r'\s*[EW]'
            r')',
            candidate,
            re.I,
        )

        if not match:
            continue

        lat = nhc_coordinate_value(
            match.group(
                1
            )
        )

        lon = nhc_coordinate_value(
            match.group(
                2
            )
        )

        if (
            lat is not None
            and
            lon is not None
        ):
            return (
                lon,
                lat,
            )

    return (
        None,
        None,
    )


def nhc_storm_identity(
    item: RSSItem,
) -> tuple[
    str,
    str,
]:
    storm_type_pattern = (
        r'(?:Major\s+Hurricane|'
        r'Hurricane|'
        r'Tropical\s+Storm|'
        r'Tropical\s+Depression|'
        r'Subtropical\s+Storm|'
        r'Subtropical\s+Depression|'
        r'Potential\s+Tropical\s+Cyclone|'
        r'Post-Tropical\s+Cyclone)'
    )

    product_tail = (
        r'(?:'
        r'Advisory|'
        r'Intermediate\s+Advisory|'
        r'Special\s+Advisory|'
        r'Forecast/Advisory|'
        r'Forecast\s+Advisory|'
        r'Forecast\s+Discussion|'
        r'Tropical\s+Cyclone\s+Update|'
        r'Public\s+Advisory|'
        r'Update'
        r')'
    )

    candidates = [
        item.title,
        *item.multiline_text.splitlines()[:80],
    ]

    for candidate in candidates:
        candidate = squish(
            candidate
        )

        if not candidate:
            continue

        match = re.search(
            rf'(?i)^\s*'
            rf'({storm_type_pattern})'
            rf'\s+'
            rf'([A-Z0-9][A-Z0-9-]{{1,24}})'
            rf'(?:\s+{product_tail}\b|\s+NUMBER\b|$)',
            candidate,
        )

        if not match:
            continue

        storm_type = squish(
            match.group(
                1
            )
        ).title()

        storm_name = squish(
            match.group(
                2
            )
        ).title()

        if storm_name.upper() in {
            'CENTER',
            'CENTRE',
            'WARNING',
            'WATCH',
        }:
            continue

        return (
            storm_type,
            storm_name,
        )

    return (
        '',
        '',
    )


def nhc_storm_name(
    item: RSSItem,
) -> str:
    storm_type, storm_name = (
        nhc_storm_identity(
            item
        )
    )

    return squish(
        ' '.join(
            part
            for part
            in (
                storm_type,
                storm_name,
            )
            if part
        )
    )


def nhc_atcf_id(
    text: str,
) -> str:
    match = re.search(
        r'\b'
        r'((?:AL|EP|CP)\d{6})'
        r'\b',
        text,
        re.I,
    )

    return (
        match.group(
            1
        ).upper()
        if match
        else
        ''
    )


def nhc_invest_ids(
    text: str,
) -> list[str]:
    found: list[str] = []

    def add(
        value: str,
    ) -> None:
        value = value.upper()

        if (
            re.fullmatch(
                r'9\d[LEC]',
                value,
            )
            and
            value not in found
        ):
            found.append(
                value
            )

    for match in re.finditer(
        r'(?i)\bINVEST\s+(9\d[LEC])\b',
        text,
    ):
        add(
            match.group(
                1
            )
        )

    for match in re.finditer(
        r'(?i)\b(9\d[LEC])\b',
        text,
    ):
        add(
            match.group(
                1
            )
        )

    basin_suffix = {
        'AL': 'L',
        'EP': 'E',
        'CP': 'C',
    }

    for match in re.finditer(
        r'(?i)\b(AL|EP|CP)(9\d)(?:\d{4})?\b',
        text,
    ):
        prefix = match.group(
            1
        ).upper()

        number = match.group(
            2
        )

        add(
            number
            +
            basin_suffix[
                prefix
            ]
        )

    return found


@dataclass(frozen=True)
class NHCInvestFix:
    invest_id: str
    lon: float
    lat: float
    valid: datetime


def nhc_atcf_coordinate(
    value: str,
) -> Optional[float]:
    match = re.fullmatch(
        r'\s*'
        r'(\d{1,4})'
        r'([NSEW])'
        r'\s*',
        value,
        re.I,
    )

    if not match:
        return None

    number = int(
        match.group(
            1
        )
    )

    coordinate = (
        number
        /
        10.0
    )

    hemisphere = (
        match.group(
            2
        )
        .upper()
    )

    if hemisphere in {
        'S',
        'W',
    }:
        coordinate *= -1.0

    return coordinate


def nhc_parse_atcf_invest_fix(
    text: str,
    invest_id: str,
) -> Optional[NHCInvestFix]:
    latest: Optional[NHCInvestFix] = None

    for raw_line in text.splitlines():
        fields = [
            field.strip()
            for field
            in raw_line.split(',')
        ]

        if len(fields) < 9:
            continue

        if fields[4].upper() != 'BEST':
            continue

        stamp = fields[2]

        if not re.fullmatch(
            r'\d{10}',
            stamp,
        ):
            continue

        try:
            valid = datetime.strptime(
                stamp,
                '%Y%m%d%H',
            ).replace(
                tzinfo=timezone.utc
            )
        except Exception:
            continue

        lat = nhc_atcf_coordinate(
            fields[6]
        )

        lon = nhc_atcf_coordinate(
            fields[7]
        )

        if (
            lat is None
            or
            lon is None
        ):
            continue

        candidate = NHCInvestFix(
            invest_id=
                invest_id,
            lon=lon,
            lat=lat,
            valid=valid,
        )

        if (
            latest is None
            or
            candidate.valid
            >
            latest.valid
        ):
            latest = candidate

    return latest


def nhc_active_atcf_invests(
    basin: str,
) -> list[NHCInvestFix]:
    prefix = {
        'atlantic': 'al',
        'epac': 'ep',
        'cpac': 'cp',
    }.get(
        basin,
        '',
    )

    suffix = {
        'atlantic': 'L',
        'epac': 'E',
        'cpac': 'C',
    }.get(
        basin,
        '',
    )

    if not prefix:
        return []

    year = utcnow().year

    try:
        response = http_get(
            NHC_ATCF_BTK_INDEX_URL,
            headers={
                'Accept':
                    'text/html,text/plain,*/*'
            },
            timeout=(
                8,
                30,
            ),
        )
    except Exception:
        log.exception(
            'Could not read NHC ATCF best-track index'
        )
        return []

    file_pattern = re.compile(
        rf'\bb{prefix}(9\d){year}\.dat\b',
        re.I,
    )

    file_names: list[str] = []

    for match in file_pattern.finditer(
        response.text
    ):
        file_name = match.group(
            0
        ).lower()

        if file_name not in file_names:
            file_names.append(
                file_name
            )

    fixes: list[NHCInvestFix] = []

    for file_name in file_names:
        number_match = re.search(
            rf'b{prefix}(9\d){year}\.dat',
            file_name,
            re.I,
        )

        if not number_match:
            continue

        invest_id = (
            number_match.group(
                1
            )
            +
            suffix
        )

        try:
            data = http_get(
                urljoin(
                    NHC_ATCF_BTK_INDEX_URL,
                    file_name,
                ),
                headers={
                    'Accept':
                        'text/plain,*/*'
                },
                timeout=(
                    8,
                    30,
                ),
            ).text
        except Exception:
            continue

        fix = nhc_parse_atcf_invest_fix(
            data,
            invest_id,
        )

        if not fix:
            continue

        if (
            utcnow()
            -
            fix.valid
            >
            timedelta(
                hours=42
            )
        ):
            continue

        fixes.append(
            fix
        )

    return fixes


def nhc_gtwo_point_lonlat(
    feature: dict[str, Any],
) -> tuple[
    Optional[float],
    Optional[float],
]:
    geometry = (
        feature.get(
            'geometry'
        )
        or
        {}
    )

    try:
        x = float(
            geometry[
                'x'
            ]
        )
        y = float(
            geometry[
                'y'
            ]
        )
    except Exception:
        return (
            None,
            None,
        )

    spatial_reference = (
        geometry.get(
            'spatialReference'
        )
        or
        {}
    )

    wkid = int(
        spatial_reference.get(
            'latestWkid'
        )
        or
        spatial_reference.get(
            'wkid'
        )
        or
        3857
    )

    if wkid in {
        4326,
        4269,
    }:
        return (
            x,
            y,
        )

    return web_mercator_to_lonlat(
        x,
        y,
    )


def nhc_distance_km(
    lon1: float,
    lat1: float,
    lon2: float,
    lat2: float,
) -> float:
    radius_km = 6371.0

    lat1_r = math.radians(
        lat1
    )
    lat2_r = math.radians(
        lat2
    )

    delta_lat = math.radians(
        lat2
        -
        lat1
    )

    delta_lon = math.radians(
        lon2
        -
        lon1
    )

    value = (
        math.sin(
            delta_lat
            /
            2.0
        )
        **
        2
        +
        math.cos(
            lat1_r
        )
        *
        math.cos(
            lat2_r
        )
        *
        math.sin(
            delta_lon
            /
            2.0
        )
        **
        2
    )

    return (
        2.0
        *
        radius_km
        *
        math.asin(
            min(
                1.0,
                math.sqrt(
                    value
                ),
            )
        )
    )


def nhc_match_invest_ids_to_outlook(
    basin: str,
    point_features: list[dict[str, Any]],
) -> list[str]:
    if not point_features:
        return []

    active_invests = nhc_active_atcf_invests(
        basin
    )

    if not active_invests:
        return []

    candidates: list[
        tuple[
            float,
            str,
            int,
        ]
    ] = []

    for point_index, feature in enumerate(
        point_features
    ):
        point_lon, point_lat = (
            nhc_gtwo_point_lonlat(
                feature
            )
        )

        if (
            point_lon is None
            or
            point_lat is None
        ):
            continue

        for invest in active_invests:
            distance = nhc_distance_km(
                point_lon,
                point_lat,
                invest.lon,
                invest.lat,
            )

            if distance <= 650.0:
                candidates.append(
                    (
                        distance,
                        invest.invest_id,
                        point_index,
                    )
                )

    candidates.sort(
        key=lambda item:
            item[0]
    )

    used_points: set[int] = set()
    used_invests: set[str] = set()
    matched: list[str] = []

    for (
        _distance,
        invest_id,
        point_index,
    ) in candidates:
        if (
            point_index in used_points
            or
            invest_id in used_invests
        ):
            continue

        used_points.add(
            point_index
        )
        used_invests.add(
            invest_id
        )
        matched.append(
            invest_id
        )

    return matched


def nhc_wind_mph(
    text: str,
) -> Optional[int]:
    winds = (
        find_nhc_field(
            text,
            'MAXIMUM SUSTAINED WINDS',
        )
        or
        find_nhc_field(
            text,
            'MAX SUSTAINED WINDS',
        )
    )

    match = re.search(
        r'\b(\d+)\s*MPH\b',
        winds,
        re.I,
    )

    if match:
        return int(
            match.group(
                1
            )
        )

    match = re.search(
        r'(?i)'
        r'maximum sustained winds '
        r'(?:are|near|now estimated to be)\s+'
        r'(\d+)\s*mph',
        text,
    )

    if not match:
        return None

    return int(
        match.group(
            1
        )
    )


def nhc_basin_matches(
    value: Any,
    basin: str,
) -> bool:
    text = squish(
        str(
            value
            or
            ''
        )
    ).lower()

    if not text:
        return True

    if basin == 'atlantic':
        return (
            'atlantic'
            in
            text
            or
            text in {
                'atl',
                'al',
            }
        )

    if basin == 'epac':
        return (
            (
                'east'
                in
                text
                or
                'eastern'
                in
                text
            )
            and
            'pac'
            in
            text
        ) or text in {
            'epac',
            'ep',
        }

    if basin == 'cpac':
        return (
            'central'
            in
            text
            and
            'pac'
            in
            text
        ) or text in {
            'cpac',
            'cp',
        }

    return True


def nhc_two_basin_extent(
    basin: str,
) -> tuple[
    float,
    float,
    float,
    float,
]:
    extents = {
        'atlantic': (
            -100.0,
            5.0,
            -10.0,
            45.0,
        ),
        'epac': (
            -145.0,
            5.0,
            -75.0,
            35.0,
        ),
        'cpac': (
            -180.0,
            5.0,
            -140.0,
            35.0,
        ),
    }

    return extents.get(
        basin,
        (
            -180.0,
            0.0,
            -10.0,
            50.0,
        ),
    )


def nhc_arcgis_geometry_points(
    geometry: dict[str, Any],
) -> list[
    tuple[
        float,
        float,
    ]
]:
    points: list[
        tuple[
            float,
            float,
        ]
    ] = []

    if (
        'x'
        in
        geometry
        and
        'y'
        in
        geometry
    ):
        try:
            points.append(
                (
                    float(
                        geometry[
                            'x'
                        ]
                    ),
                    float(
                        geometry[
                            'y'
                        ]
                    ),
                )
            )
        except Exception:
            pass

    for collection_name in (
        'rings',
        'paths',
        'points',
    ):
        collection = (
            geometry.get(
                collection_name
            )
            or
            []
        )

        for part in collection:
            if (
                isinstance(
                    part,
                    (list, tuple),
                )
                and
                len(
                    part
                )
                >=
                2
                and
                isinstance(
                    part[0],
                    (int, float),
                )
            ):
                try:
                    points.append(
                        (
                            float(
                                part[0]
                            ),
                            float(
                                part[1]
                            ),
                        )
                    )
                except Exception:
                    pass

                continue

            if not isinstance(
                part,
                (list, tuple),
            ):
                continue

            for coordinate in part:
                if (
                    not isinstance(
                        coordinate,
                        (list, tuple),
                    )
                    or
                    len(
                        coordinate
                    )
                    <
                    2
                ):
                    continue

                try:
                    points.append(
                        (
                            float(
                                coordinate[0]
                            ),
                            float(
                                coordinate[1]
                            ),
                        )
                    )
                except Exception:
                    pass

    return points


def nhc_export_summary_overlay(
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
    layers: Iterable[int],
    *,
    layer_where: str = '',
) -> Image.Image:
    layer_ids = [
        int(
            layer
        )
        for layer
        in layers
    ]

    params: dict[str, Any] = {
        'bbox':
            ','.join(
                f'{value:.3f}'
                for value
                in bbox
            ),
        'bboxSR':
            '3857',
        'imageSR':
            '3857',
        'size':
            f'{width},{height}',
        'format':
            'png32',
        'transparent':
            'true',
        'layers':
            'show:'
            +
            ','.join(
                str(
                    layer
                )
                for layer
                in layer_ids
            ),
        'f':
            'image',
    }

    if layer_where:
        params[
            'layerDefs'
        ] = json.dumps(
            {
                str(
                    layer
                ):
                    layer_where
                for layer
                in layer_ids
            },
            separators=(
                ',',
                ':',
            ),
        )

    try:
        response = http_get(
            f'{NHC_TROPICAL_MAPSERVER}/export',
            params=params,
            headers={
                'Accept':
                    'image/png,*/*'
            },
            timeout=(
                8,
                45,
            ),
        )

    except requests.HTTPError:
        if not layer_where:
            raise

        params.pop(
            'layerDefs',
            None,
        )

        response = http_get(
            f'{NHC_TROPICAL_MAPSERVER}/export',
            params=params,
            headers={
                'Accept':
                    'image/png,*/*'
            },
            timeout=(
                8,
                45,
            ),
        )

    return (
        Image.open(
            io.BytesIO(
                response.content
            )
        )
        .convert(
            'RGBA'
        )
    )


def nhc_probability_features(
    basin: str,
) -> tuple[
    list[dict[str, Any]],
    list[dict[str, Any]],
]:
    point_features = arcgis_query_features(
        NHC_TROPICAL_MAPSERVER,
        NHC_TWO_CURRENT_LAYER,
        out_fields=(
            'objectid,basin,prob2day,risk2day,'
            'prob7day,risk7day,idp_source,'
            'idp_filedate,idp_ingestdate'
        ),
        return_geometry=True,
        out_sr=3857,
    )

    region_features = arcgis_query_features(
        NHC_TROPICAL_MAPSERVER,
        NHC_TWO_REGION_LAYER,
        out_fields=(
            'objectid,basin,prob2day,risk2day,'
            'prob7day,risk7day,idp_source,'
            'idp_filedate,idp_ingestdate'
        ),
        return_geometry=True,
        out_sr=3857,
    )

    point_features = [
        feature
        for feature
        in point_features
        if nhc_basin_matches(
            (
                feature.get(
                    'attributes'
                )
                or
                {}
            ).get(
                'basin'
            ),
            basin,
        )
    ]

    region_features = [
        feature
        for feature
        in region_features
        if nhc_basin_matches(
            (
                feature.get(
                    'attributes'
                )
                or
                {}
            ).get(
                'basin'
            ),
            basin,
        )
    ]

    return (
        point_features,
        region_features,
    )


def nhc_point_pixel_from_mercator(
    x: float,
    y: float,
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    width: int,
    height: int,
) -> tuple[
    int,
    int,
]:
    minx, miny, maxx, maxy = bbox

    px = int(
        round(
            (
                x
                -
                minx
            )
            /
            max(
                maxx
                -
                minx,
                1.0,
            )
            *
            (
                width
                -
                1
            )
        )
    )

    py = int(
        round(
            (
                maxy
                -
                y
            )
            /
            max(
                maxy
                -
                miny,
                1.0,
            )
            *
            (
                height
                -
                1
            )
        )
    )

    return (
        px,
        py,
    )


def nhc_draw_probability_labels(
    image: Image.Image,
    point_features: list[dict[str, Any]],
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
) -> Image.Image:
    out = image.copy().convert(
        'RGBA'
    )

    draw = ImageDraw.Draw(
        out,
        'RGBA',
    )

    font = load_font(
        22,
        True,
    )

    width, height = out.size

    for index, feature in enumerate(
        point_features
    ):
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        try:
            x = float(
                geometry[
                    'x'
                ]
            )

            y = float(
                geometry[
                    'y'
                ]
            )

        except Exception:
            continue

        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        probability_2 = squish(
            str(
                attrs.get(
                    'prob2day'
                )
                or
                ''
            )
        )

        probability_7 = squish(
            str(
                attrs.get(
                    'prob7day'
                )
                or
                ''
            )
        )

        if not any(
            (
                probability_2,
                probability_7,
            )
        ):
            continue

        if (
            probability_2
            and
            probability_7
        ):
            label = (
                f'2d {probability_2}  '
                f'7d {probability_7}'
            )

        elif probability_7:
            label = (
                f'7d {probability_7}'
            )

        else:
            label = (
                f'2d {probability_2}'
            )

        px, py = (
            nhc_point_pixel_from_mercator(
                x,
                y,
                bbox,
                width,
                height,
            )
        )

        text_box = draw.textbbox(
            (
                0,
                0,
            ),
            label,
            font=font,
            stroke_width=2,
        )

        text_width = (
            text_box[2]
            -
            text_box[0]
        )

        text_height = (
            text_box[3]
            -
            text_box[1]
        )

        label_x = min(
            max(
                8,
                px + 18,
            ),
            width
            -
            text_width
            -
            10,
        )

        vertical_offset = (
            -26
            if
            index % 2 == 0
            else
            12
        )

        label_y = min(
            max(
                8,
                py
                +
                vertical_offset,
            ),
            height
            -
            text_height
            -
            8,
        )

        draw.text(
            (
                label_x,
                label_y,
            ),
            label,
            font=font,
            fill=(
                16,
                22,
                29,
                255,
            ),
            stroke_width=3,
            stroke_fill=(
                255,
                255,
                255,
                245,
            ),
        )

    return out


def build_mapbox_nhc_invest_map(
    basin: str,
) -> str:
    width = 1200
    height = 760

    point_features, region_features = (
        nhc_probability_features(
            basin
        )
    )

    if (
        not point_features
        and
        not region_features
    ):
        return ''

    bbox = mercator_bbox_from_lonlat(
        *nhc_two_basin_extent(
            basin
        )
    )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    exact_basin_value = first_nonempty(
        (
            (
                feature.get(
                    'attributes'
                )
                or
                {}
            ).get(
                'basin'
            )
            for feature
            in (
                point_features
                +
                region_features
            )
        )
    )

    layer_where = (
        'basin = '
        +
        sql_quote(
            exact_basin_value
        )
        if
        exact_basin_value
        else
        ''
    )

    overlay = nhc_export_summary_overlay(
        bbox,
        width,
        height,
        (
            NHC_TWO_CURRENT_LAYER,
            NHC_TWO_REGION_LAYER,
        ),
        layer_where=
            layer_where,
    )

    base.alpha_composite(
        overlay
    )

    base = nhc_draw_probability_labels(
        base,
        point_features,
        bbox,
    )

    return save_map_image(
        base,
        prefix='nhc_invest_',
    )


def nhc_normalized_storm_token(
    value: Any,
) -> str:
    return re.sub(
        r'[^A-Z0-9]+',
        '',
        str(
            value
            or
            ''
        ).upper(),
    )


def nhc_feature_distance_score(
    features: list[dict[str, Any]],
    current_lon: Optional[float],
    current_lat: Optional[float],
) -> float:
    if (
        current_lon is None
        or
        current_lat is None
    ):
        return 0.0

    current_x, current_y = (
        lonlat_to_web_mercator(
            current_lon,
            current_lat,
        )
    )

    distances: list[float] = []

    for feature in features:
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if (
            'x'
            not in
            geometry
            or
            'y'
            not in
            geometry
        ):
            continue

        try:
            dx = (
                float(
                    geometry[
                        'x'
                    ]
                )
                -
                current_x
            )

            dy = (
                float(
                    geometry[
                        'y'
                    ]
                )
                -
                current_y
            )

        except Exception:
            continue

        distances.append(
            math.hypot(
                dx,
                dy,
            )
        )

    if not distances:
        return 0.0

    distance_km = (
        min(
            distances
        )
        /
        1000.0
    )

    return max(
        0.0,
        40.0
        -
        min(
            40.0,
            distance_km
            /
            75.0,
        ),
    )


def nhc_select_forecast_group(
    item: RSSItem,
    basin: str,
) -> tuple[
    list[dict[str, Any]],
    str,
    str,
]:
    _storm_type, storm_name = (
        nhc_storm_identity(
            item
        )
    )

    if not storm_name:
        return (
            [],
            '',
            '',
        )

    features = arcgis_query_features(
        NHC_TROPICAL_MAPSERVER,
        NHC_FORECAST_POINTS_LAYER,
        out_fields='*',
        return_geometry=True,
        out_sr=3857,
    )

    groups: dict[
        str,
        list[dict[str, Any]],
    ] = {}

    for feature in features:
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        if not nhc_basin_matches(
            attrs.get(
                'basin'
            ),
            basin,
        ):
            continue

        group_key = squish(
            str(
                attrs.get(
                    'idp_source'
                )
                or
                attrs.get(
                    'stormname'
                )
                or
                ''
            )
        )

        if not group_key:
            continue

        groups.setdefault(
            group_key,
            [],
        ).append(
            feature
        )

    if not groups:
        return (
            [],
            '',
            '',
        )

    current_lon, current_lat = (
        nhc_lonlat_from_text(
            item.multiline_text
        )
    )

    wanted_name = (
        nhc_normalized_storm_token(
            storm_name
        )
    )

    ranked: list[
        tuple[
            int,
            float,
            float,
            str,
        ]
    ] = []

    for group_key, group in groups.items():
        attrs = (
            group[0].get(
                'attributes'
            )
            or
            {}
        )

        candidate_name = (
            nhc_normalized_storm_token(
                attrs.get(
                    'stormname'
                )
            )
        )

        if (
            not candidate_name
            or
            not wanted_name
        ):
            name_rank = 0
        elif candidate_name == wanted_name:
            name_rank = 2
        elif (
            candidate_name in wanted_name
            or
            wanted_name in candidate_name
        ):
            name_rank = 1
        else:
            name_rank = 0

        if name_rank == 0:
            continue

        latest_ingest = 0.0

        for feature in group:
            feature_attrs = (
                feature.get(
                    'attributes'
                )
                or
                {}
            )

            for key in (
                'idp_ingestdate',
                'idp_filedate',
            ):
                value = feature_attrs.get(
                    key
                )

                if value in (
                    None,
                    '',
                ):
                    continue

                try:
                    numeric = float(
                        value
                    )
                except Exception:
                    dt = arcgis_datetime(
                        value
                    )
                    numeric = (
                        dt.timestamp()
                        *
                        1000.0
                        if dt
                        else
                        0.0
                    )

                latest_ingest = max(
                    latest_ingest,
                    numeric,
                )

        distance_score = (
            nhc_feature_distance_score(
                group,
                current_lon,
                current_lat,
            )
        )

        ranked.append(
            (
                name_rank,
                latest_ingest,
                distance_score,
                group_key,
            )
        )

    if not ranked:
        return (
            [],
            '',
            '',
        )

    ranked.sort(
        reverse=True
    )

    best_key = ranked[0][3]
    selected = groups.get(
        best_key,
        [],
    )

    if not selected:
        return (
            [],
            '',
            '',
        )

    selected_attrs = (
        selected[0].get(
            'attributes'
        )
        or
        {}
    )

    selected_storm_name = squish(
        str(
            selected_attrs.get(
                'stormname'
            )
            or
            storm_name
        )
    )

    selected_source = squish(
        str(
            selected_attrs.get(
                'idp_source'
            )
            or
            best_key
        )
    )

    def forecast_tau(
        feature: dict[str, Any],
    ) -> float:
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        try:
            return float(
                attrs.get(
                    'tau'
                )
                if attrs.get(
                    'tau'
                ) is not None
                else
                attrs.get(
                    'fcstprd'
                )
                or
                0.0
            )
        except Exception:
            return 0.0

    selected.sort(
        key=forecast_tau
    )

    return (
        selected,
        selected_storm_name,
        selected_source,
    )


def nhc_knots_to_mph(
    value: Any,
) -> Optional[int]:
    try:
        knots = float(
            value
        )
    except Exception:
        return None

    if knots < 0:
        return None

    mph = (
        knots
        *
        1.15078
    )

    return int(
        round(
            mph
            /
            5.0
        )
        *
        5
    )


def nhc_draw_named_wind_labels(
    image: Image.Image,
    forecast_points: list[dict[str, Any]],
    bbox: tuple[
        float,
        float,
        float,
        float,
    ],
    *,
    current_lon: Optional[float],
    current_lat: Optional[float],
    current_wind_mph: Optional[int],
) -> Image.Image:
    out = image.copy().convert(
        'RGBA'
    )

    draw = ImageDraw.Draw(
        out,
        'RGBA',
    )

    font = load_font(
        19,
        True,
    )

    width, height = out.size

    selected_points: list[
        tuple[
            int,
            dict[str, Any],
        ]
    ] = []

    for index, feature in enumerate(
        forecast_points
    ):
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        try:
            tau = int(
                round(
                    float(
                        attrs.get(
                            'tau'
                        )
                        if attrs.get(
                            'tau'
                        ) is not None
                        else
                        attrs.get(
                            'fcstprd'
                        )
                        or
                        0.0
                    )
                )
            )
        except Exception:
            tau = index

        if (
            tau == 0
            or
            tau in {
                12,
                24,
                36,
                48,
                60,
                72,
                96,
                120,
            }
        ):
            selected_points.append(
                (
                    tau,
                    feature,
                )
            )

    if not selected_points:
        return out

    for point_index, (
        tau,
        feature,
    ) in enumerate(
        selected_points
    ):
        attrs = (
            feature.get(
                'attributes'
            )
            or
            {}
        )

        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        if (
            tau == 0
            and
            current_lon is not None
            and
            current_lat is not None
        ):
            point_x, point_y = (
                lonlat_to_web_mercator(
                    current_lon,
                    current_lat,
                )
            )
        else:
            try:
                point_x = float(
                    geometry[
                        'x'
                    ]
                )
                point_y = float(
                    geometry[
                        'y'
                    ]
                )
            except Exception:
                continue

        px, py = (
            nhc_point_pixel_from_mercator(
                point_x,
                point_y,
                bbox,
                width,
                height,
            )
        )

        if (
            tau == 0
            and
            current_wind_mph is not None
        ):
            wind_mph = current_wind_mph
        else:
            wind_mph = nhc_knots_to_mph(
                attrs.get(
                    'maxwind'
                )
            )

        if wind_mph is None:
            continue

        label = (
            f'{wind_mph} mph'
        )

        text_box = draw.textbbox(
            (
                0,
                0,
            ),
            label,
            font=font,
            stroke_width=2,
        )

        text_width = (
            text_box[2]
            -
            text_box[0]
        )

        text_height = (
            text_box[3]
            -
            text_box[1]
        )

        label_x = (
            px
            +
            13
        )

        if (
            label_x
            +
            text_width
            >
            width
            -
            8
        ):
            label_x = (
                px
                -
                text_width
                -
                13
            )

        label_y = (
            py
            -
            text_height
            -
            10
            if point_index % 2 == 0
            else
            py
            +
            10
        )

        label_y = min(
            max(
                8,
                label_y,
            ),
            height
            -
            text_height
            -
            8,
        )

        draw.text(
            (
                label_x,
                label_y,
            ),
            label,
            font=font,
            fill=(
                0,
                0,
                0,
                255,
            ),
            stroke_width=3,
            stroke_fill=(
                255,
                255,
                255,
                248,
            ),
        )

        if (
            tau == 0
            and
            current_lon is not None
            and
            current_lat is not None
        ):
            draw.ellipse(
                (
                    px - 6,
                    py - 6,
                    px + 6,
                    py + 6,
                ),
                fill=(
                    0,
                    0,
                    0,
                    255,
                ),
                outline=(
                    255,
                    255,
                    255,
                    255,
                ),
                width=2,
            )

    return out


def build_mapbox_nhc_storm_map(
    item: RSSItem,
    kind: str,
    basin: str,
) -> str:
    _storm_type, parsed_storm_name = (
        nhc_storm_identity(
            item
        )
    )

    if not parsed_storm_name:
        return ''

    forecast_points, gis_storm_name, _gis_source = (
        nhc_select_forecast_group(
            item,
            basin,
        )
    )

    if not forecast_points:
        return ''

    first_attrs = (
        forecast_points[0].get(
            'attributes'
        )
        or
        {}
    )

    where_value = (
        gis_storm_name
        or
        parsed_storm_name
    )

    where_parts = [
        'stormname = '
        +
        sql_quote(
            where_value
        )
    ]

    advisory_number = squish(
        str(
            first_attrs.get(
                'advisnum'
            )
            or
            ''
        )
    )

    if advisory_number:
        where_parts.append(
            'advisnum = '
            +
            sql_quote(
                advisory_number
            )
        )

    layer_where = (
        ' AND '.join(
            where_parts
        )
    )

    cone_features = arcgis_query_features(
        NHC_TROPICAL_MAPSERVER,
        NHC_FORECAST_CONE_LAYER,
        where=layer_where,
        out_fields='*',
        return_geometry=True,
        out_sr=3857,
    )

    if not cone_features:
        cone_features = arcgis_query_features(
            NHC_TROPICAL_MAPSERVER,
            NHC_FORECAST_CONE_LAYER,
            where=(
                'stormname = '
                +
                sql_quote(
                    where_value
                )
            ),
            out_fields='*',
            return_geometry=True,
            out_sr=3857,
        )

        if cone_features:
            latest_advisory = squish(
                str(
                    (
                        cone_features[-1].get(
                            'attributes'
                        )
                        or
                        {}
                    ).get(
                        'advisnum'
                    )
                    or
                    ''
                )
            )

            if latest_advisory:
                layer_where = (
                    'stormname = '
                    +
                    sql_quote(
                        where_value
                    )
                    +
                    ' AND advisnum = '
                    +
                    sql_quote(
                        latest_advisory
                    )
                )

                cone_features = [
                    feature
                    for feature
                    in cone_features
                    if squish(
                        str(
                            (
                                feature.get(
                                    'attributes'
                                )
                                or
                                {}
                            ).get(
                                'advisnum'
                            )
                            or
                            ''
                        )
                    )
                    ==
                    latest_advisory
                ]

    map_points: list[
        tuple[
            float,
            float,
        ]
    ] = []

    for feature in forecast_points:
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        map_points.extend(
            nhc_arcgis_geometry_points(
                geometry
            )
        )

    for feature in cone_features:
        geometry = (
            feature.get(
                'geometry'
            )
            or
            {}
        )

        map_points.extend(
            nhc_arcgis_geometry_points(
                geometry
            )
        )

    current_lon, current_lat = (
        nhc_lonlat_from_text(
            item.multiline_text
        )
    )

    if (
        current_lon is not None
        and
        current_lat is not None
    ):
        map_points.append(
            lonlat_to_web_mercator(
                current_lon,
                current_lat,
            )
        )

    if not map_points:
        return ''

    width = 1200
    height = 760

    bbox = mercator_bbox_from_points(
        map_points,
        width,
        height,
        padding_factor=1.35,
        min_width_m=1500000.0,
        min_height_m=900000.0,
    )

    base = fetch_mapbox_light_base(
        bbox,
        width,
        height,
    )

    overlay = nhc_export_summary_overlay(
        bbox,
        width,
        height,
        (
            NHC_FORECAST_TRACK_LAYER,
            NHC_FORECAST_CONE_LAYER,
            NHC_WATCH_WARNING_LAYER,
            NHC_FORECAST_POINTS_LAYER,
        ),
        layer_where=
            layer_where,
    )

    base.alpha_composite(
        overlay
    )

    base = nhc_draw_named_wind_labels(
        base,
        forecast_points,
        bbox,
        current_lon=
            current_lon,
        current_lat=
            current_lat,
        current_wind_mph=
            nhc_wind_mph(
                item.multiline_text
            ),
    )

    return save_map_image(
        base,
        prefix='nhc_storm_',
    )


def nhc_page_image(
    page_url: str,
) -> str:
    if not page_url:
        return ''

    try:
        _text, soup = (
            fetch_nhc_product_page(
                page_url
            )
        )

    except Exception:
        return ''

    candidates: list[
        tuple[
            int,
            str,
        ]
    ] = []

    for image_tag in soup.find_all(
        'img'
    ):
        src = str(
            image_tag.get(
                'src'
            )
            or
            ''
        ).strip()

        if not src:
            continue

        descriptor = ' '.join(
            (
                str(
                    image_tag.get(
                        'alt'
                    )
                    or
                    ''
                ),
                str(
                    image_tag.get(
                        'title'
                    )
                    or
                    ''
                ),
                src,
            )
        ).lower()

        if any(
            bad
            in
            descriptor
            for bad
            in (
                'logo',
                'banner',
                'social',
                'icon',
            )
        ):
            continue

        score = 0

        if 'cone' in descriptor:
            score += 50

        if '5day' in descriptor:
            score += 35

        if 'forecast' in descriptor:
            score += 25

        if 'track' in descriptor:
            score += 20

        if 'graphic' in descriptor:
            score += 10

        if 'outlook' in descriptor:
            score += 10

        if (
            'gtwo'
            in
            descriptor
            or
            '7d0'
            in
            descriptor
        ):
            score += 18

        if score:
            candidates.append(
                (
                    score,
                    urljoin(
                        page_url,
                        src,
                    ),
                )
            )

    for (
        _score,
        image_url,
    ) in sorted(
        candidates,
        reverse=True,
    ):
        try:
            path = (
                download_nhc_image_to_temp(
                    image_url,
                    prefix='nhc_storm_',
                    referer=page_url,
                )
            )

            with Image.open(
                path
            ) as image:
                if (
                    image.width
                    >=
                    400
                    and
                    image.height
                    >=
                    250
                ):
                    return path

            os.unlink(
                path
            )

        except Exception:
            continue

    return ''


def nhc_probability_values(
    raw: str,
    horizon: str,
) -> list[int]:
    if horizon == '2':
        label_pattern = (
            r'(?:48\s*hours|2\s*days?)'
        )
    else:
        label_pattern = (
            r'7\s*days?'
        )

    values: list[int] = []

    patterns = [
        rf'Formation chance through\s*'
        rf'{label_pattern}'
        rf'[^\n]*?'
        rf'(\d+)\s*(?:percent|%)',
        rf'{label_pattern}\s*formation chance'
        rf'[^\n]*?'
        rf'(\d+)\s*(?:percent|%)',
    ]

    for pattern in patterns:
        for value in re.findall(
            pattern,
            raw,
            re.I,
        ):
            try:
                values.append(
                    int(
                        value
                    )
                )
            except Exception:
                pass

    return values


def render_nhc_two(
    item: RSSItem,
    source: str,
) -> RenderedPost:
    basin_key = (
        'atlantic'
        if
        source.endswith(
            'atlantic'
        )
        else
        'epac'
        if
        source.endswith(
            'epac'
        )
        else
        'cpac'
    )

    basin = NHC_BASIN_LABELS[
        basin_key
    ]

    raw = (
        item.multiline_text
    )

    issued = (
        find_local_issue_clock(
            raw
        )
    )

    probabilities_48 = (
        nhc_probability_values(
            raw,
            '2',
        )
    )

    probabilities_7 = (
        nhc_probability_values(
            raw,
            '7',
        )
    )

    invests = nhc_invest_ids(
        raw
    )

    try:
        point_features, _region_features = (
            nhc_probability_features(
                basin_key
            )
        )

        for invest_id in nhc_match_invest_ids_to_outlook(
            basin_key,
            point_features,
        ):
            if invest_id not in invests:
                invests.append(
                    invest_id
                )

    except Exception:
        log.exception(
            'Could not resolve NHC outlook disturbances to ATCF invest identifiers'
        )

    details: list[str] = []

    if probabilities_48:
        details.append(
            'Highest 2-day formation '
            'chance: '
            f'{max(probabilities_48)}%'
        )

    if probabilities_7:
        details.append(
            'Highest 7-day formation '
            'chance: '
            f'{max(probabilities_7)}%'
        )

    image_path = ''

    try:
        image_path = (
            build_mapbox_nhc_invest_map(
                basin_key
            )
        )

    except Exception:
        log.exception(
            'Could not build clean '
            'NHC tropical outlook map '
            'for %s',
            source,
        )

    if not image_path:
        image_url = (
            NHC_TWO_IMAGES.get(
                source,
                '',
            )
        )

        if image_url:
            try:
                image_path = (
                    download_nhc_image_to_temp(
                        image_url,
                        prefix='nhc_two_',
                        referer=(
                            item.link
                            or
                            'https://www.nhc.noaa.gov/'
                        ),
                    )
                )

            except Exception:
                log.exception(
                    'Could not download '
                    'fallback NHC graphical '
                    'outlook image for %s',
                    source,
                )

    if (
        not image_path
        and
        item.link
    ):
        try:
            image_path = (
                nhc_page_image(
                    item.link
                )
            )

        except Exception:
            log.exception(
                'Could not obtain '
                'fallback NHC outlook '
                'image for %s',
                source,
            )

    if len(
        invests
    ) == 1:
        first_line = (
            f'Invest {invests[0]}'
        )

    elif invests:
        first_line = (
            'Invests '
            +
            ', '.join(
                invests
            )
        )

    else:
        first_line = (
            'Tropical Weather Outlook'
        )

    post_lines = [
        first_line,
    ]

    if first_line != 'Tropical Weather Outlook':
        post_lines.append(
            'Tropical Weather Outlook'
        )

    post_lines.extend(
        [
            basin,
            (
                f'Issued {issued}'
                if issued
                else
                (
                    'Issued '
                    +
                    item.published.strftime(
                        '%-I:%M %p UTC'
                    )
                    if
                    item.published
                    else
                    ''
                )
            ),
            *details,
        ]
    )

    return RenderedPost(
        fit_post(
            post_lines,
            item.link,
        ),
        image_path,
    )


def render_nhc_storm(
    item: RSSItem,
    kind: str,
    basin: str,
) -> Optional[RenderedPost]:
    raw = (
        item.multiline_text
    )

    storm_label = nhc_storm_name(
        item
    )

    if not storm_label:
        log.info(
            'Ignoring NHC %s item without '
            'an advisory-bearing cyclone identity: %s',
            kind,
            item.title,
        )

        return None

    names = {
        'tcp':
            'Tropical Cyclone Public Advisory',
        'tcu':
            'Tropical Cyclone Update',
        'tcd':
            'Tropical Cyclone Forecast Discussion',
        'tcm':
            'Tropical Cyclone Forecast Advisory',
    }

    product = names.get(
        kind,
        'Tropical Cyclone Update',
    )

    location = (
        nhc_center_location(
            raw
        )
        or
        NHC_BASIN_LABELS[
            basin
        ]
    )

    issued = (
        find_local_issue_clock(
            raw
        )
    )

    details: list[str] = []

    winds = (
        find_nhc_field(
            raw,
            'MAXIMUM SUSTAINED WINDS',
        )
        or
        find_nhc_field(
            raw,
            'MAX SUSTAINED WINDS',
        )
    )

    movement = find_nhc_field(
        raw,
        'PRESENT MOVEMENT',
    )

    pressure = find_nhc_field(
        raw,
        'MINIMUM CENTRAL PRESSURE',
    )

    if winds:
        details.append(
            'Maximum winds: '
            +
            truncate(
                winds,
                70,
            )
        )

    if movement:
        details.append(
            'Movement: '
            +
            truncate(
                movement,
                70,
            )
        )

    if (
        pressure
        and
        len(
            details
        ) < 2
    ):
        details.append(
            'Pressure: '
            +
            truncate(
                pressure,
                70,
            )
        )

    image_path = ''

    try:
        image_path = (
            build_mapbox_nhc_storm_map(
                item,
                kind,
                basin,
            )
        )

    except Exception:
        log.exception(
            'Could not build clean '
            'NHC storm cone map for %s',
            storm_label,
        )

    if not image_path:
        try:
            image_path = (
                nhc_page_image(
                    item.link
                )
            )

        except Exception:
            log.exception(
                'Could not obtain '
                'official NHC storm image '
                'for %s',
                storm_label,
            )

    return RenderedPost(
        fit_post(
            [
                storm_label,
                product,
                location,
                (
                    f'Issued {issued}'
                    if issued
                    else
                    (
                        'Issued '
                        +
                        item.published.strftime(
                            '%-I:%M %p UTC'
                        )
                        if
                        item.published
                        else
                        ''
                    )
                ),
                *details,
            ],
            item.link,
        ),
        image_path,
    )


def poll_nhc_product_source(
    db: StateDB,
    x: XPublisher,
    source: str,
    url: str,
    kind: str,
    basin: str,
) -> None:
    try:
        process_rss_source(
            db,
            x,
            source=source,
            url=url,
            item_filter=
                nhc_item_is_real,
            renderer=
                lambda item, k=kind, b=basin:
                    render_nhc_storm(
                        item,
                        k,
                        b,
                    ),
        )

    except requests.HTTPError as exc:
        if getattr(
            exc.response,
            'status_code',
            None,
        ) in {
            404,
            410,
        }:
            if not db.source_primed(
                source
            ):
                db.mark_source_primed(
                    source
                )

            return

        raise


def nhc_index_fingerprint(
    url: str,
) -> str:
    return hashlib.sha256(
        http_get(
            url,
            headers={
                'Accept':
                    'application/xml,'
                    'text/xml,*/*'
            },
        ).content
    ).hexdigest()


def nhc_sweep_basin(
    db: StateDB,
    x: XPublisher,
    basin: str,
) -> bool:
    okay = True

    for (
        source,
        url,
        kind,
        source_basin,
    ) in NHC_BASIN_SOURCES[
        basin
    ]:
        try:
            poll_nhc_product_source(
                db,
                x,
                source,
                url,
                kind,
                source_basin,
            )

        except Exception:
            okay = False

            log.exception(
                'NHC product source '
                'failed: %s',
                source,
            )

    return okay


def poll_nhc(
    db: StateDB,
    x: XPublisher,
) -> None:
    for source, url in (
        NHC_TWO_FEEDS.items()
    ):
        try:
            process_rss_source(
                db,
                x,
                source=source,
                url=url,
                item_filter=
                    nhc_item_is_real,
                renderer=
                    lambda item, s=source:
                        render_nhc_two(
                            item,
                            s,
                        ),
            )

        except Exception:
            log.exception(
                'NHC Tropical Weather '
                'Outlook source failed: %s',
                source,
            )

    now_ts = int(
        time.time()
    )

    for basin, index_url in (
        NHC_BASIN_INDEX_FEEDS.items()
    ):
        fp_key = (
            f'nhc:index-fingerprint:'
            f'{basin}'
        )

        sweep_key = (
            f'nhc:last-full-sweep:'
            f'{basin}'
        )

        try:
            fingerprint = (
                nhc_index_fingerprint(
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
                        '0',
                    )
                    or
                    '0'
                )

            except ValueError:
                last_sweep = 0

            changed = (
                not
                old_fingerprint
                or
                fingerprint
                !=
                old_fingerprint
            )

            due = (
                now_ts
                -
                last_sweep
                >=
                NHC_FULL_SWEEP_SECONDS
            )

            if (
                changed
                or
                due
            ):
                log.info(
                    'NHC %s product '
                    'sweep (%s)',
                    basin,
                    (
                        'index changed'
                        if changed
                        else
                        'safety sweep'
                    ),
                )

                if nhc_sweep_basin(
                    db,
                    x,
                    basin,
                ):
                    db.set_meta(
                        sweep_key,
                        str(
                            now_ts
                        ),
                    )

                    db.set_meta(
                        fp_key,
                        fingerprint,
                    )

                else:
                    log.warning(
                        'NHC %s sweep '
                        'incomplete; '
                        'retrying next cycle',
                        basin,
                    )

            else:
                db.set_meta(
                    fp_key,
                    fingerprint,
                )

        except Exception:
            log.exception(
                'NHC basin index/'
                'sweep failed: %s',
                basin,
            )


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
        'start':
            iso_z(
                start
            ),

        'status':
            'actual',

        'limit':
            500,
    }

    url = (
        NWS_ALERTS_URL
    )

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
        pages
        <
        25
    ):
        response = http_get(
            url,
            params=params,
            headers={
                'Accept':
                    'application/geo+json'
            },
            timeout=(
                8,
                45,
            ),
        )

        data = response.json()

        page_features = (
            data.get(
                'features'
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
                'pagination'
            )
            or
            {}
        )

        next_url = (
            pagination.get(
                'next'
            )
            if
            isinstance(
                pagination,
                dict,
            )
            else
            None
        )

        url = (
            str(
                next_url
            )
            if
            next_url
            else
            ''
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
        props.get(
            'parameters'
        )
        or
        {},
        'VTEC',
    ):
        actions.update(
            re.findall(
                r'/[A-Z]\.'
                r'(NEW|CON|EXT|'
                r'EXA|EXB|UPG|'
                r'CAN|EXP|COR)'
                r'\.',
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
    actions = (
        alert_vtec_actions(
            props
        )
    )

    if actions:
        return (
            'NEW'
            in
            actions
        )

    return (
        str(
            props.get(
                'messageType',
                '',
            )
        ).lower()
        ==
        'alert'
    )


def nws_alert_key(
    feature: dict[
        str,
        Any,
    ],
) -> str:
    props = (
        feature.get(
            'properties'
        )
        or
        {}
    )

    raw = (
        props.get(
            'id'
        )
        or
        feature.get(
            'id'
        )
        or
        props.get(
            '@id'
        )
    )

    if raw:
        return sha256_text(
            str(
                raw
            )
        )

    return sha256_text(
        '\x1f'.join(
            str(
                props.get(
                    key
                )
                or
                ''
            )
            for key
            in (
                'event',
                'sent',
                'headline',
                'areaDesc',
                'expires',
            )
        )
    )


def format_cap_time(
    value: str,
) -> str:
    if not value:
        return ''

    try:
        dt = datetime.fromisoformat(
            value.replace(
                'Z',
                '+00:00',
            )
        )

    except Exception:
        return ''

    clock = dt.strftime(
        '%-I:%M %p'
    )

    offset = (
        dt.utcoffset()
        or
        timedelta(
            0
        )
    )

    hours = int(
        offset.total_seconds()
        //
        3600
    )

    zone = {
        -4:
            'EDT',

        -5:
            'EST/CDT',

        -6:
            'CST/MDT',

        -7:
            'MST/PDT',

        -8:
            'PST/AKDT',

        -9:
            'AKST',

        -10:
            'HST',
    }.get(
        hours,
        f'UTC{hours:+d}',
    )

    return (
        f'{clock} '
        f'{zone}'
    )


def render_nws_alert(
    feature: dict[
        str,
        Any,
    ],
    kind: str,
) -> RenderedPost:
    props = (
        feature.get(
            'properties'
        )
        or
        {}
    )

    parameters = (
        props.get(
            'parameters'
        )
        or
        {}
    )

    product = (
        'Tornado Warning'
        if
        kind
        ==
        'tornado'
        else
        squish(
            props.get(
                'event'
            )
        )
        or
        'Winter Weather Alert'
    )

    location = truncate(
        squish(
            props.get(
                'areaDesc'
            )
        ),
        110,
    )

    issued = format_cap_time(
        str(
            props.get(
                'sent'
            )
            or
            ''
        )
    )

    expires = format_cap_time(
        str(
            props.get(
                'expires'
            )
            or
            ''
        )
    )

    time_line = ' '.join(
        part
        for part
        in (
            (
                f'Issued {issued}'
                if issued
                else
                ''
            ),
            (
                f'Expires {expires}'
                if expires
                else
                ''
            ),
        )
        if part
    )

    hazards = (
        [
            'Tornado'
        ]
        if
        kind
        ==
        'tornado'
        else
        extract_hazards(
            f'{product} '
            f'{props.get("headline") or ""} '
            f'{props.get("description") or ""}',
            product,
        )
    )

    if kind == 'tornado':
        damage = first_parameter(
            parameters,
            'tornadoDamageThreat',
        )

        detection = first_parameter(
            parameters,
            'tornadoDetection',
        )

        if (
            damage
            and
            damage.lower()
            not in {
                'base',
                'none',
            }
        ):
            hazards.append(
                f'{damage.title()} '
                'damage threat'
            )

        if detection:
            hazards.append(
                detection.title()
            )

    image_path = ''

    try:
        image_path = (
            build_alert_polygon_image(
                feature,
                product,
                radar=(
                    kind
                    ==
                    'tornado'
                ),
            )
        )

    except Exception:
        log.exception(
            'Could not build %s '
            'map image',
            product,
        )

    return RenderedPost(
        fit_post(
            [
                product,
                location,
                time_line,
                (
                    'Hazards: '
                    +
                    ', '.join(
                        hazards[:3]
                    )
                    if hazards
                    else
                    ''
                ),
            ]
        ),
        image_path,
    )


def poll_nws_alerts(
    db: StateDB,
    x: XPublisher,
) -> None:
    source = (
        'nws_alerts'
    )

    now = (
        utcnow()
    )

    previous = parse_any_datetime(
        db.get_meta(
            'nws:last_success'
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
        event = squish(
            (
                feature.get(
                    'properties'
                )
                or
                {}
            ).get(
                'event'
            )
        )

        if event == 'Tornado Warning':
            relevant.append(
                (
                    feature,
                    'tornado',
                )
            )

        elif event in WINTER_ALERT_EVENTS:
            relevant.append(
                (
                    feature,
                    'winter',
                )
            )

    relevant.sort(
        key=lambda pair:
            parse_any_datetime(
                (
                    pair[0]
                    .get(
                        'properties'
                    )
                    or
                    {}
                )
                .get(
                    'sent'
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

    if not db.source_primed(
        source
    ):
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

        db.set_meta(
            'nws:last_success',
            iso_z(
                now
            ),
        )

        log.info(
            'Primed %s with %d '
            'recent relevant alert(s)',
            source,
            len(
                relevant
            ),
        )

        return

    for feature, kind in relevant:
        props = (
            feature.get(
                'properties'
            )
            or
            {}
        )

        key = (
            nws_alert_key(
                feature
            )
        )

        current_status = db.status(
            source,
            key,
        )

        if (
            current_status
            and
            current_status
            !=
            'rejected'
        ):
            continue

        if not is_new_alert_message(
            props
        ):
            db.mark_seen_without_post(
                source,
                key,
                status=
                    'non_new_vtec',
            )

            continue

        age = age_minutes(
            props.get(
                'sent'
            )
        )

        max_age = (
            TORNADO_MAX_POST_AGE_MINUTES
            if
            kind
            ==
            'tornado'
            else
            WINTER_ALERT_MAX_POST_AGE_MINUTES
        )

        if (
            age
            is not None
            and
            age
            >
            max_age
        ):
            db.mark_seen_without_post(
                source,
                key,
                status=
                    'stale',
            )

            continue

        post: Optional[
            RenderedPost
        ] = None

        try:
            post = render_nws_alert(
                feature,
                kind,
            )

            publish_once(
                db,
                x,
                source,
                key,
                post,
            )

        finally:
            cleanup_post(
                post
            )

    db.set_meta(
        'nws:last_success',
        iso_z(
            now
        ),
    )


def arcgis_features(
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
        f'{mapserver}/'
        f'{layer}/query',
        params={
            'where':
                '1=1',

            'outFields':
                out_fields,

            'returnGeometry':
                'false',

            'f':
                'json',
        },
        headers={
            'Accept':
                'application/json'
        },
        timeout=(
            8,
            35,
        ),
    )

    payload = (
        response.json()
    )

    if payload.get(
        'error'
    ):
        raise RuntimeError(
            'NOAA ArcGIS error '
            f'layer {layer}: '
            f'{payload["error"]!r}'
        )

    return [
        dict(
            feature.get(
                'attributes'
            )
            or
            {}
        )
        for feature
        in (
            payload.get(
                'features'
            )
            or
            []
        )
    ]


def first_nonempty(
    values: Iterable[Any],
) -> str:
    for value in values:
        text = squish(
            str(
                value
                or
                ''
            )
        )

        if text:
            return text

    return ''


@dataclass(
    frozen=True
)
class EROProduct:
    day: int
    issued: str
    valid: str
    highest_risk: str

    @property
    def key(
        self,
    ) -> str:
        return sha256_text(
            f'{self.day}|'
            f'{self.issued}|'
            f'{self.valid}|'
            f'{self.highest_risk}'
        )


def parse_wpc_ero(
    day: int,
) -> EROProduct:
    attrs = arcgis_features(
        WPC_ERO_MAPSERVER,
        day - 1,
        (
            'product,valid_time,outlook,'
            'issue_time,start_time,end_time,'
            'dn,idp_ingestdate'
        ),
    )

    if not attrs:
        raise ValueError(
            f'WPC ERO Day {day} '
            'returned no features'
        )

    issued = first_nonempty(
        attribute.get(
            'issue_time'
        )
        for attribute
        in attrs
    )

    valid = first_nonempty(
        attribute.get(
            'valid_time'
        )
        for attribute
        in attrs
    )

    if not valid:
        valid = ' to '.join(
            value
            for value
            in (
                first_nonempty(
                    attribute.get(
                        'start_time'
                    )
                    for attribute
                    in attrs
                ),
                first_nonempty(
                    attribute.get(
                        'end_time'
                    )
                    for attribute
                    in attrs
                ),
            )
            if value
        )

    if not issued:
        raw = max(
            (
                attribute.get(
                    'idp_ingestdate'
                )
                or
                0
                for attribute
                in attrs
            ),
            default=0,
        )

        if raw:
            issued = iso_z(
                datetime.fromtimestamp(
                    float(
                        raw
                    )
                    /
                    1000.0,
                    tz=
                        timezone.utc,
                )
            )

    ranks = {
        'marginal': 1,
        'slight': 2,
        'moderate': 3,
        'high': 4,
    }

    best_name = ''
    best_rank = -1

    for attribute in attrs:
        outlook = squish(
            str(
                attribute.get(
                    'outlook'
                )
                or
                ''
            )
        )

        try:
            rank = int(
                float(
                    attribute.get(
                        'dn'
                    )
                )
            )

        except Exception:
            rank = max(
                (
                    value
                    for key, value
                    in ranks.items()
                    if
                    key
                    in
                    outlook.lower()
                ),
                default=0,
            )

        if (
            rank
            >
            best_rank
        ):
            best_name = (
                outlook
            )

            best_rank = (
                rank
            )

    return EROProduct(
        day,
        issued,
        valid,
        best_name,
    )


def render_ero(
    product: EROProduct,
) -> RenderedPost:
    image_path = ''

    try:
        image_path = (
            build_mapbox_wpc_ero_map(
                product.day
            )
        )

    except Exception:
        log.exception(
            'Could not build WPC '
            'ERO Day %d Mapbox image',
            product.day,
        )

    day_name = SPC_DAY_WORDS.get(
        product.day,
        str(
            product.day
        ),
    )

    issue_z = format_spc_issue_z(
        product.issued
    )

    return RenderedPost(
        fit_post(
            [
                f'Day {day_name} '
                'Excessive Rainfall Outlook',

                (
                    f'Issued at {issue_z}'
                    if issue_z
                    else
                    f'Issued '
                    f'{format_utc_clock(product.issued)}'
                ),

                (
                    f'Highest Risk: '
                    f'{truncate(product.highest_risk, 90)}'
                    if
                    product.highest_risk
                    else
                    ''
                ),

                'Hazards: Excessive rainfall | '
                'Flash flooding',
            ]
        ),
        image_path,
    )


def poll_wpc_ero(
    db: StateDB,
    x: XPublisher,
) -> None:
    days = (
        [
            1,
            2,
            3,
        ]
        +
        (
            [
                4,
                5,
            ]
            if
            ENABLE_WPC_DAY4_DAY5_ERO
            else
            []
        )
    )

    for day in days:
        source = (
            f'wpc_ero_day'
            f'{day}'
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
                    'Primed %s: %s',
                    source,
                    product.issued,
                )

                continue

            current_status = db.status(
                source,
                product.key,
            )

            if (
                current_status
                and
                current_status
                !=
                'rejected'
            ):
                continue

            post: Optional[
                RenderedPost
            ] = None

            try:
                post = render_ero(
                    product
                )

                publish_once(
                    db,
                    x,
                    source,
                    product.key,
                    post,
                )

            finally:
                cleanup_post(
                    post
                )

        except Exception:
            log.exception(
                'WPC ERO Day %d '
                'poll failed',
                day,
            )


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


def parse_wmo_ddhhmm_from_text(
    product_text: str,
) -> Optional[
    datetime
]:
    match = re.search(
        r'(?m)^'
        r'FOUS11\s+KWBC\s+'
        r'(\d{6})\b',
        product_text,
    )

    if not match:
        return None

    stamp = (
        match.group(
            1
        )
    )

    day = int(
        stamp[:2]
    )

    hour = int(
        stamp[2:4]
    )

    minute = int(
        stamp[4:6]
    )

    now = utcnow()

    candidates: list[
        datetime
    ] = []

    for offset in (
        -1,
        0,
        1,
    ):
        year = now.year
        month = (
            now.month
            +
            offset
        )

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
                    tzinfo=
                        timezone.utc,
                )
            )

        except ValueError:
            pass

    plausible = [
        date
        for date
        in candidates
        if
        date
        <=
        now
        +
        timedelta(
            hours=6
        )
    ]

    if plausible:
        return max(
            plausible
        )

    if candidates:
        return min(
            candidates,
            key=lambda date:
                abs(
                    (
                        date
                        -
                        now
                    ).total_seconds()
                ),
        )

    return None


def wpc_hsd_from_products_api(
) -> tuple[
    str,
    str,
    str,
]:
    response = http_get(
        NWS_PRODUCTS_URL,
        params={
            'type':
                WPC_HSD_TYPE,

            'location':
                WPC_HSD_LOCATION,

            'limit':
                10,
        },
        headers={
            'Accept':
                'application/ld+json,'
                'application/json'
        },
        timeout=(
            8,
            35,
        ),
    )

    payload = response.json()

    graph = (
        payload.get(
            '@graph'
        )
        or
        payload.get(
            'products'
        )
        or
        payload.get(
            'features'
        )
        or
        []
    )

    if (
        not isinstance(
            graph,
            list,
        )
        or
        not graph
    ):
        return (
            '',
            '',
            '',
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
                item.get(
                    'issuanceTime'
                )
                or
                item.get(
                    'issuance_time'
                )
                or
                ''
            )
        )

        candidates.append(
            (
                issued
                or
                datetime(
                    1970,
                    1,
                    1,
                    tzinfo=
                        timezone.utc,
                ),
                item,
            )
        )

    if not candidates:
        return (
            '',
            '',
            '',
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
        issued_dt.year
        >
        1970
        and
        max(
            0.0,
            (
                utcnow()
                -
                issued_dt
            ).total_seconds()
            /
            3600.0,
        )
        >
        WPC_HSD_MAX_AGE_HOURS
    ):
        return (
            '',
            '',
            '',
        )

    reference = str(
        newest.get(
            '@id'
        )
        or
        newest.get(
            'id'
        )
        or
        ''
    ).strip()

    if not reference:
        return (
            '',
            '',
            '',
        )

    detail_url = (
        reference
        if
        reference.startswith(
            (
                'http://',
                'https://',
            )
        )
        else
        'https://'
        'api.weather.gov/'
        f'products/{reference}'
    )

    detail = (
        http_get(
            detail_url,
            headers={
                'Accept':
                    'application/ld+json,'
                    'application/json'
            },
            timeout=(
                8,
                35,
            ),
        )
        .json()
    )

    text = str(
        detail.get(
            'productText'
        )
        or
        detail.get(
            'product_text'
        )
        or
        ''
    )

    issuance = squish(
        str(
            detail.get(
                'issuanceTime'
            )
            or
            detail.get(
                'issuance_time'
            )
            or
            newest.get(
                'issuanceTime'
            )
            or
            ''
        )
    )

    identity = squish(
        str(
            detail.get(
                'id'
            )
            or
            detail.get(
                '@id'
            )
            or
            reference
        )
    )

    return (
        text,
        issuance,
        identity,
    )


def wpc_hsd_from_tgftp(
) -> tuple[
    str,
    str,
    str,
]:
    response = http_get(
        WPC_HSD_RAW_URL,
        headers={
            'Accept':
                'text/plain,*/*'
        },
        timeout=(
            8,
            35,
        ),
    )

    text = (
        response.text
        or
        ''
    )

    if not text.strip():
        return (
            '',
            '',
            '',
        )

    issued_dt = (
        parse_wmo_ddhhmm_from_text(
            text
        )
    )

    if issued_dt is not None:
        if (
            max(
                0.0,
                (
                    utcnow()
                    -
                    issued_dt
                ).total_seconds()
                /
                3600.0,
            )
            >
            WPC_HSD_MAX_AGE_HOURS
        ):
            return (
                '',
                '',
                '',
            )

        issuance = iso_z(
            issued_dt
        )

    else:
        issuance = ''

    return (
        text,
        issuance,
        sha256_text(
            text
        ),
    )


def parse_wpc_heavy_snow_discussion(
) -> Optional[
    WPCWinterDiscussion
]:
    text = ''
    issuance = ''
    identity = ''

    api_error: Optional[
        Exception
    ] = None

    try:
        text, issuance, identity = (
            wpc_hsd_from_products_api()
        )

    except Exception as exc:
        api_error = (
            exc
        )

        log.warning(
            'NWS Products API HSD '
            'lookup failed; trying '
            'TGFTP fallback: %s',
            exc,
        )

    if not text:
        try:
            (
                fallback_text,
                fallback_issuance,
                fallback_identity,
            ) = (
                wpc_hsd_from_tgftp()
            )

            text = (
                fallback_text
            )

            issuance = (
                issuance
                or
                fallback_issuance
            )

            identity = (
                identity
                or
                fallback_identity
            )

        except Exception as exc:
            if api_error is not None:
                raise RuntimeError(
                    'Both NWS HSD '
                    'sources failed: '
                    f'API={api_error!r}; '
                    f'TGFTP={exc!r}'
                ) from exc

            raise

    if not text:
        return None

    upper = (
        text.upper()
    )

    if (
        'QPFHSD'
        not in upper
        and
        'HEAVY SNOW'
        not in upper
        and
        'PROBABILISTIC HEAVY SNOW'
        not in upper
    ):
        raise ValueError(
            'Retrieved HSD product '
            'was not the WPC heavy '
            'snow/icing discussion'
        )

    lines = [
        line.strip()
        for line
        in text.splitlines()
        if
        line.strip()
    ]

    valid_line = next(
        (
            squish(
                line[5:]
            )
            for line
            in lines
            if
            line.lower()
            .startswith(
                'valid '
            )
        ),
        '',
    )

    compact = re.sub(
        r'\s+',
        ' ',
        text,
    )

    headline_match = re.search(
        r'\.\.\.\s*'
        r'(.*?)'
        r'\s*\.\.\.',
        compact,
    )

    headline = (
        squish(
            headline_match.group(
                1
            )
        )
        if
        headline_match
        else
        ''
    )

    if not issuance:
        issued_dt = (
            parse_wmo_ddhhmm_from_text(
                text
            )
        )

        issuance = (
            iso_z(
                issued_dt
            )
            if
            issued_dt
            else
            ''
        )

    identity = (
        identity
        or
        f'{issuance}|'
        f'{valid_line}|'
        f'{headline}|'
        f'{sha256_text(text)}'
    )

    return WPCWinterDiscussion(
        identity,
        issuance,
        valid_line,
        headline,
    )


def parse_wpc_winter_package_updates(
) -> list[
    tuple[
        int,
        str,
        str,
    ]
]:
    day_layers = {
        1:
            (
                1,
                2,
                3,
                4,
            ),

        2:
            (
                6,
                7,
                8,
                9,
            ),

        3:
            (
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
                arcgis_features(
                    WPC_WINTER_MAPSERVER,
                    layer,
                    (
                        'product,valid_time,'
                        'outlook,issue_time,'
                        'start_time,end_time,'
                        'dn,idp_ingestdate'
                    ),
                )
            )

        if not attrs:
            continue

        issue = first_nonempty(
            attribute.get(
                'issue_time'
            )
            for attribute
            in attrs
        )

        valid = first_nonempty(
            attribute.get(
                'valid_time'
            )
            for attribute
            in attrs
        )

        if not issue:
            raw = max(
                (
                    attribute.get(
                        'idp_ingestdate'
                    )
                    or
                    0
                    for attribute
                    in attrs
                ),
                default=0,
            )

            if raw:
                issue = iso_z(
                    datetime.fromtimestamp(
                        float(
                            raw
                        )
                        /
                        1000.0,
                        tz=
                            timezone.utc,
                    )
                )

        if issue:
            out.append(
                (
                    day,
                    issue,
                    valid,
                )
            )

    return out


def render_wpc_hsd(
    disc: WPCWinterDiscussion,
) -> RenderedPost:
    image_path = ''

    try:
        image_path = (
            build_service_map(
                WPC_WINTER_MAPSERVER,
                'show:1,2,3,4',
                prefix='wpc_hsd_',
            )
        )

    except Exception:
        log.exception(
            'Could not build WPC '
            'heavy snow/ice image'
        )

    return RenderedPost(
        fit_post(
            [
                'Probabilistic Heavy Snow '
                'and Icing Discussion',

                'United States',

                (
                    f'Issued '
                    f'{format_utc_clock(disc.issued_line)}'
                    +
                    (
                        f' Valid '
                        f'{truncate(disc.valid_line, 60)}'
                        if
                        disc.valid_line
                        else
                        ''
                    )
                ),

                'Hazards: Heavy snow, icing',

                truncate(
                    disc.headline,
                    90,
                ),
            ]
        ),
        image_path,
    )


def render_wpc_winter_day(
    day: int,
    issue: str,
    valid: str,
) -> RenderedPost:
    layers = {
        1:
            'show:1,2,3,4',

        2:
            'show:6,7,8,9',

        3:
            'show:11,12,13,14',
    }[
        day
    ]

    image_path = ''

    try:
        image_path = (
            build_service_map(
                WPC_WINTER_MAPSERVER,
                layers,
                prefix=
                    f'wpc_winter_d'
                    f'{day}_',
            )
        )

    except Exception:
        log.exception(
            'Could not build WPC '
            'Day %d winter map',
            day,
        )

    return RenderedPost(
        fit_post(
            [
                f'Day {day} '
                'Winter Weather Outlook',

                'United States',

                (
                    f'Issued '
                    f'{format_utc_clock(issue)}'
                    +
                    (
                        f' Valid '
                        f'{truncate(valid, 60)}'
                        if
                        valid
                        else
                        ''
                    )
                ),

                'Hazards: Heavy snow, '
                'freezing rain',
            ]
        ),
        image_path,
    )


def poll_wpc_winter(
    db: StateDB,
    x: XPublisher,
) -> None:
    if ENABLE_WPC_HEAVY_SNOW_DISCUSSION:
        source = (
            'wpc_heavy_snow_discussion'
        )

        try:
            disc = (
                parse_wpc_heavy_snow_discussion()
            )

            if disc is None:
                if (
                    db.get_meta(
                        'wpc_hsd:'
                        'no_current_logged'
                    )
                    !=
                    '1'
                ):
                    log.info(
                        'No current WPC '
                        'heavy snow/ice '
                        'discussion'
                    )

                    db.set_meta(
                        'wpc_hsd:'
                        'no_current_logged',
                        '1',
                    )

            else:
                db.set_meta(
                    'wpc_hsd:'
                    'no_current_logged',
                    '0',
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
                        'Primed %s',
                        source,
                    )

                else:
                    current_status = db.status(
                        source,
                        disc.key,
                    )

                    if (
                        not
                        current_status
                        or
                        current_status
                        ==
                        'rejected'
                    ):
                        post: Optional[
                            RenderedPost
                        ] = None

                        try:
                            post = (
                                render_wpc_hsd(
                                    disc
                                )
                            )

                            publish_once(
                                db,
                                x,
                                source,
                                disc.key,
                                post,
                            )

                        finally:
                            cleanup_post(
                                post
                            )

        except Exception:
            log.exception(
                'WPC heavy snow/ice '
                'discussion poll failed'
            )

    if ENABLE_WPC_WINTER_PACKAGES:
        source = (
            'wpc_winter_packages'
        )

        try:
            updates = (
                parse_wpc_winter_package_updates()
            )

            keyed = [
                (
                    day,
                    issue,
                    valid,
                    sha256_text(
                        f'day{day}|'
                        f'{issue}|'
                        f'{valid}'
                    ),
                )
                for day, issue, valid
                in updates
            ]

            if not db.source_primed(
                source
            ):
                for (
                    _day,
                    _issue,
                    _valid,
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
                    'Primed %s with %d '
                    'active package '
                    'timestamp(s)',
                    source,
                    len(
                        keyed
                    ),
                )

            else:
                for (
                    day,
                    issue,
                    valid,
                    key,
                ) in keyed:
                    current_status = db.status(
                        source,
                        key,
                    )

                    if (
                        current_status
                        and
                        current_status
                        !=
                        'rejected'
                    ):
                        continue

                    post: Optional[
                        RenderedPost
                    ] = None

                    try:
                        post = (
                            render_wpc_winter_day(
                                day,
                                issue,
                                valid,
                            )
                        )

                        publish_once(
                            db,
                            x,
                            source,
                            key,
                            post,
                        )

                    finally:
                        cleanup_post(
                            post
                        )

        except Exception:
            log.exception(
                'WPC winter-package '
                'poll failed'
            )


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
            'DRY_RUN=true: '
            'skipping X credential '
            'verification'
        )

        return

    log.info(
        'Authenticated to X as @%s',
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
        'Starting %s worker',
        BOT_NAME,
    )

    log.info(
        'BUILD=%s',
        BUILD_ID,
    )

    log.info(
        'DB=%s '
        'DRY_RUN=%s '
        'INCLUDE_SOURCE_URLS=%s',
        DB_PATH,
        DRY_RUN,
        INCLUDE_SOURCE_URLS,
    )

    log.info(
        'Mapbox basemap: %s',
        (
            'enabled'
            if
            MAPBOX_API_KEY
            else
            'fallback '
            '(MAPBOX_API_KEY not set)'
        ),
    )

    log.info(
        'Intervals: '
        'NWS=%ss '
        'SPC=%ss '
        'NHC=%ss '
        'WPC_ERO=%ss '
        'WPC_WINTER=%ss',
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
                'Temporary X startup/'
                'auth failure: %s',
                exc,
            )

            time.sleep(
                30
            )

        except Exception:
            db.close()

            log.exception(
                'X credential verification '
                'failed; refusing to run'
            )

            return 2

    if STOP_REQUESTED:
        db.close()

        return 0

    jobs = [
        Job(
            'nws',
            NWS_POLL_SECONDS,
            poll_nws_alerts,
        ),
        Job(
            'spc',
            SPC_POLL_SECONDS,
            poll_spc,
        ),
        Job(
            'nhc',
            NHC_POLL_SECONDS,
            poll_nhc,
        ),
        Job(
            'wpc_ero',
            WPC_ERO_POLL_SECONDS,
            poll_wpc_ero,
        ),
        Job(
            'wpc_winter',
            WPC_WINTER_POLL_SECONDS,
            poll_wpc_winter,
        ),
    ]

    base = (
        time.monotonic()
    )

    for index, job in enumerate(
        jobs
    ):
        job.next_due = (
            base
            +
            index
            *
            0.8
        )

    try:
        while not STOP_REQUESTED:
            now = (
                time.monotonic()
            )

            for job in jobs:
                if STOP_REQUESTED:
                    break

                if (
                    now
                    <
                    job.next_due
                ):
                    continue

                try:
                    job.func(
                        db,
                        x,
                    )

                except Exception:
                    log.exception(
                        'Unhandled failure '
                        'in job %s',
                        job.name,
                    )

                job.next_due = (
                    time.monotonic()
                    +
                    job.interval
                )

            time.sleep(
                0.5
            )

    finally:
        log.info(
            'Stopping. '
            'DB status counts: %s',
            db.count_by_status(),
        )

        db.close()

    return 0


if __name__ == '__main__':
    sys.exit(
        main()
    )
