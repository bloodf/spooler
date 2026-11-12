# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.21.0"
# ///

import asyncio
import base64
import csv
import datetime
import ftplib
import hashlib
import json
import logging
import math
import os
import platform
import re
import shutil
import socket
import ssl
import struct
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
import zipfile
import zlib
from logging.handlers import RotatingFileHandler
from pathlib import Path

import orca

try:
    import orca.pages  # noqa: F401
    _PAGES = True
except (ImportError, AttributeError):
    _PAGES = False

_SLICING = hasattr(getattr(orca, "slicing", None), "SlicingPipelineCapabilityBase")

PLUGIN_NAME = "Spooler"
PLUGIN_VERSION = "0.21.0"
# Stamped per operating system by scripts/build.py.
BUILD_TARGET = "any"

DEFAULT_SPOOLMAN_URL = "http://raspberrypi:7912"
LOW_DEFAULT = 100  # grams

FEEDBACK_URL = "https://github.com/bloodf/spooler/issues"
RELEASE_API = "https://api.github.com/repos/bloodf/spooler/releases/latest"

# webbrowser can only open a URL; it can't use the browser's default search engine.
SEARCH_URL = "https://www.google.com/search?q={query}"

SETTINGS_FILENAME = "spooler_settings.json"
LOG_FILENAME = "spooler.log"
LOG_MAX = 256 * 1024

TIMEOUT = 5  # seconds
MAX_QUERY = 200
REFRESH_SECS = 60
DEFAULT_MARGIN = 10  # percent
TAIL_BYTES = 192 * 1024
CACHE_SECS = 120
REPEAT_SECS = 120
COLOUR_TOLERANCE = 40
NOTICE_MAX = 400
NOTICE_DELAY = 0.4  # seconds, so the slicing thread has returned before any UI call
MAIN_SIZE = (380, 600)
SETTINGS_SIZE = (560, 820)

PLUGIN_DIR = Path(__file__).resolve().parent


def _config_root() -> Path:
    if sys.platform == "win32":
        return Path(os.environ.get("APPDATA") or Path.home() / "AppData" / "Roaming")
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Application Support"
    return Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config")


def _data_dir() -> Path:
    """Settings, log and tab-icon folder, inside OrcaSlicer's data folder.

    Not the plugin folder: updates would reset it, and OrcaSlicer expects that folder to
    hold only the plugin file.
    """
    for parent in PLUGIN_DIR.parents:
        if parent.name == "OrcaSlicer":
            return parent / "spooler"
    return _config_root() / "OrcaSlicer" / "spooler"


DATA_DIR = _data_dir()
SETTINGS_FILE = DATA_DIR / SETTINGS_FILENAME
LOG_FILE = DATA_DIR / LOG_FILENAME
# Where earlier builds kept settings when OrcaSlicer's data folder wasn't found.
OLD_SETTINGS = PLUGIN_DIR / SETTINGS_FILENAME

log = logging.getLogger("spooler")
log.setLevel(logging.INFO)
log.propagate = False
log.addHandler(logging.NullHandler())

# The log is what users attach to bug reports, so nothing secret may reach it. Messages from the
# pages are never logged whole (see message_summary); this filter is the second line: it masks the
# user:password part of URLs, secret-looking query values and secret-looking JSON/form fields in
# every record, whatever the message or exception text holds.
_SECRET_NAMES = r"(?:pass(?:word|wd)?|access[_-]?token|refresh[_-]?token|token|secret|api[_-]?key|key|code|tfa[_-]?(?:key|code)|auth(?:orization)?|cookie|session)"
_REDACTIONS = (
    (re.compile(r"(?i)\b([a-z][a-z0-9+.-]*://)[^/\s@]+@"), r"\1***@"),
    (re.compile(r"(?i)([?&;]" + _SECRET_NAMES + r"=)[^&;\s#'\"]+"), r"\1***"),
    (re.compile(r"(?i)(['\"]" + _SECRET_NAMES + r"['\"]\s*:\s*)(['\"])(?:\\.|(?!\2).)*\2"), r"\1\2***\2"),
    (re.compile(r"(?i)(\bBearer\s+)[A-Za-z0-9._~+/=-]+"), r"\1***"),
)


def redact(text: object) -> str:
    out = str(text)
    for pattern, repl in _REDACTIONS:
        out = pattern.sub(repl, out)
    return out


class _Redact(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        try:
            message = record.getMessage()
        except Exception:
            message = str(record.msg)
        if record.exc_info and not record.exc_text:
            record.exc_text = logging.Formatter().formatException(record.exc_info)
        record.msg, record.args = redact(message), ()
        if record.exc_text:
            record.exc_text = redact(record.exc_text)
        return True


log.addFilter(_Redact())

_SAFE_FIELDS = ("view", "type", "action", "act", "mode", "period", "source")


def message_summary(data: object) -> str:
    """What a page message was, for the log, without its values: the routing fields (short
    identifiers only) and the names of the other keys. Never the password, code or URL it holds."""
    if isinstance(data, str):
        try:
            data = json.loads(data)
        except ValueError:
            return f"unparsed text of {len(data)} characters"
    if not isinstance(data, dict):
        return type(data).__name__
    shown = [f"{key}={data[key]}" for key in _SAFE_FIELDS
             if isinstance(data.get(key), str) and re.fullmatch(r"[A-Za-z0-9_-]{1,32}", data[key])]
    rest = sorted(str(key)[:32] for key in data if key not in _SAFE_FIELDS)
    return ", ".join(shown + ([f"keys: {', '.join(rest)}"] if rest else [])) or "empty message"


def setup_log(path: Path | None = None) -> None:
    if any(isinstance(h, RotatingFileHandler) for h in log.handlers):
        return
    path = path or LOG_FILE
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        handler = RotatingFileHandler(path, maxBytes=LOG_MAX, backupCount=1, encoding="utf-8")
    except OSError:
        return
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    log.addHandler(handler)


# Started at import so anything that goes wrong while the plugin loads is captured.
setup_log()
log.info(
    "%s %s (%s build) imported; orca.pages %s",
    PLUGIN_NAME,
    PLUGIN_VERSION,
    BUILD_TARGET,
    "available" if _PAGES else "not available",
)


_reported = {}
_spool_cache = {"url": "", "time": 0.0, "spools": []}


def _report(key: str, error: str | None, exc_info: bool = False) -> None:
    """Log a failure once, then its recovery, so the periodic refresh can't flood the log."""
    if error is None:
        if _reported.pop(key, None) is not None:
            log.info("%s recovered", key)
    elif _reported.get(key) != error:
        _reported[key] = error
        log.warning("%s failed: %s", key, error, exc_info=exc_info)


def get_settings() -> dict:
    defaults = {
        "spoolman_url": "",
        "spool_source": "spoolman",
        "low_stock_grams": LOW_DEFAULT,
        "plate_check": True,
        "plate_margin_percent": DEFAULT_MARGIN,
        "weight_display": "both",
        "show_cart": False,
        "spool_columns": 1,
        "progress": {},
        "stats": {},
        "auto_send": True,
        "send_saved_copies": True,
    }
    for path in (SETTINGS_FILE, OLD_SETTINGS):
        try:
            return {**defaults, **json.loads(path.read_text(encoding="utf-8"))}
        except (OSError, ValueError):
            continue
    return defaults


def parse_low(value: object) -> float:
    try:
        grams = float(value)
    except (TypeError, ValueError):
        return LOW_DEFAULT
    if grams < 0:
        return LOW_DEFAULT
    return int(grams) if grams == int(grams) else grams


def parse_margin(value: object) -> int:
    try:
        return min(50, max(0, round(float(value))))
    except (TypeError, ValueError, OverflowError):
        return DEFAULT_MARGIN


def parse_flag(value: object, default: bool = True) -> bool:
    if value is None:
        return default
    if isinstance(value, str):
        return value.strip().lower() in ("1", "true", "on", "yes")
    return bool(value)


def parse_weights(value: object) -> str:
    return value if value in ("grams", "percent", "both") else "both"


def weight_mode() -> str:
    return parse_weights(get_settings().get("weight_display"))


def cart_on() -> bool:
    return parse_flag(get_settings().get("show_cart"), default=False)


def parse_columns(value: object) -> int:
    return 2 if value in (2, "2") else 1


def spool_columns() -> int:
    return parse_columns(get_settings().get("spool_columns"))


def parse_progress(value: object) -> dict:
    v = value if isinstance(value, dict) else {}
    return {"on": parse_flag(v.get("on")), "finish": parse_flag(v.get("finish")),
            "slot": parse_flag(v.get("slot")), "idle": "hide" if v.get("idle") == "hide" else "line"}


def progress_settings() -> dict:
    return parse_progress(get_settings().get("progress"))


# What the Spools and Printer tabs show, each switched in Settings > Display: {key: default}.
DISPLAY_DEFAULTS = {
    # Spools tab
    "group_same": True,     # spools of one filament fold into one row
    "in_use": True,         # which printer slot a spool is loaded in
    "vendor": True,         # the manufacturer tag
    "material": True,
    "colour_code": False,   # #RRGGBB; off by default since the Vue page (review S04): noise on every row
    "diameter": False,
    "rfid": True,
    "bar": True,            # the remaining-weight bar
    "location": True,       # the Spoolman location
    "spool_id": False,
    "comment": True,        # the spool's Spoolman comment, on a muted line under the details
    "lot_nr": False,
    "extra_fields": False,  # your own Spoolman extra fields, as name: value
    "exact_weight": True,   # 2,380 g instead of 2.38 kg
    "archived": False,      # also list archived spools (fetched only while this is on)
    "dried": True,          # "Dried 12 d ago" chip, amber once past the material's reminder days
    "use_first": True,      # "Use First" chip on the opened spool to finish before others of its filament
    "low_notice": True,     # an OrcaSlicer notification when a spool drops below the low-stock grams
    # Printer tab: each slot's card
    "head_vendor": True,
    "head_material": True,
    "head_colour_code": True,
    "head_weight": True,    # grams left of the spool's weight
    "head_bar": True,
    "head_spool": True,     # spool id and location
    "head_preset": True,    # the OrcaSlicer preset, on the card instead of only on hover
    "head_rfid": True,
}


def parse_display(value: object) -> dict:
    value = value if isinstance(value, dict) else {}
    return {key: parse_flag(value.get(key), default) for key, default in DISPLAY_DEFAULTS.items()}


def display_settings() -> dict:
    return parse_display(get_settings().get("display"))


def save_display(value: object) -> None:
    """Save Settings > Display on its own, so it never depends on the connection check."""
    if isinstance(value, dict):
        save_settings({**get_settings(), "display": parse_display(value)})


# Drying reminders: days a spool of a material may go since it was dried, 0 = never remind.
DRYING_DEFAULTS = {"PETG": 30, "TPU": 14, "PA": 7, "PVA": 7, "PC": 14, "ABS": 0, "ASA": 0, "PLA": 0}
DRYING_MAX_DAYS = 3650
DRIED_FIELD = "dried"  # Spoolman spool extra field (datetime) holding the day a spool was dried


def parse_drying(value: object) -> dict:
    """{MATERIAL: days}. Not a dict means the defaults; a dict is the whole table as saved."""
    if not isinstance(value, dict):
        return dict(DRYING_DEFAULTS)
    table = {}
    for key, days in value.items():
        name = " ".join(str(key).split()).upper()[:24]
        if not name or isinstance(days, bool):
            continue
        try:
            number = int(float(days))
        except (TypeError, ValueError):
            number = 0
        table[name] = min(max(number, 0), DRYING_MAX_DAYS)
    return table


def drying_settings() -> dict:
    return parse_drying(get_settings().get("drying"))


def save_drying(value: object) -> None:
    """Save Settings > Drying on its own, like the display flags."""
    if isinstance(value, dict):
        save_settings({**get_settings(), "drying": parse_drying(value)})


def drying_days(material: object, table: dict | None = None) -> int:
    """Reminder days for a filament material; the longest table name it starts with wins
    ("PA-CF" uses PA, "PETG HF" uses PETG), case-insensitively. 0 when none or switched off."""
    table = drying_settings() if table is None else table
    name = _norm(material)
    best = max((k for k in table if name.startswith(_norm(k)) and _norm(k)), key=lambda k: len(_norm(k)), default=None)
    return table[best] if best else 0


def dried_date(spool: dict) -> datetime.date | None:
    """The day a spool was marked dried (its extra field, stored as JSON text), or None."""
    raw = (spool.get("extra") or {}).get(DRIED_FIELD) if isinstance(spool, dict) else None
    try:
        raw = json.loads(raw) if isinstance(raw, str) else raw
        return datetime.date.fromisoformat(raw[:10]) if isinstance(raw, str) else None
    except ValueError:
        return None


def wizard_pending() -> bool:
    """The first-run setup guide opens by itself until it is finished or skipped, and never for
    someone who already has a source set up."""
    return not get_settings().get("wizard_done") and not configured()


def save_wizard_done() -> None:
    save_settings({**get_settings(), "wizard_done": True})


CURRENCIES = ("spoolman", "gbp", "eur", "usd")


def parse_stats(value: object) -> dict:
    v = value if isinstance(value, dict) else {}
    return {"on": parse_flag(v.get("on")), "cur": v.get("cur") if v.get("cur") in CURRENCIES else "spoolman"}


def stats_settings() -> dict:
    return parse_stats(get_settings().get("stats"))


def plate_settings() -> tuple[bool, int]:
    settings = get_settings()
    return (parse_flag(settings.get("plate_check")),
            parse_margin(settings.get("plate_margin_percent")))


def save_settings(settings: dict) -> bool:
    try:
        _write_json(SETTINGS_FILE, settings)  # in one step: a crash never leaves half a file
        return True
    except OSError:
        log.exception("Could not write %s", SETTINGS_FILE)
        return False


# The settings shown in OrcaSlicer's plugin manager (Plugins > Spooler > Config). Spooler's own
# settings file stays the source; the plugin manager holds a copy, and a change made there is
# taken back into the file. Each value goes through the same check as the Settings page.
CONFIG_KEYS = {
    "spoolman_url": lambda v: clean_url(str(v)),
    "spool_source": lambda v: parse_source(v),
    "low_stock_grams": lambda v: parse_low(v),
    "plate_check": lambda v: parse_flag(v),
    "plate_margin_percent": lambda v: parse_margin(v),
    "weight_display": lambda v: parse_weights(v),
    "show_cart": lambda v: parse_flag(v, default=False),
    "spool_columns": lambda v: parse_columns(v),
    "auto_send": lambda v: parse_flag(v),
    "send_saved_copies": lambda v: parse_flag(v),
}
_config: dict = {"last": None}


def config_view(settings: dict) -> dict:
    return {key: settings[key] for key in CONFIG_KEYS if key in settings}


def sync_config(capability) -> None:
    """Keep the plugin manager's copy and the settings file the same. A change made in the
    plugin manager since the last sync wins; otherwise the file is copied there. Never raises."""
    if not (callable(getattr(capability, "get_config", None)) and callable(getattr(capability, "save_config", None))):
        return
    try:
        raw = json.loads(capability.get_config() or "{}")
        stored = config_view(raw) if isinstance(raw, dict) else {}
        settings = get_settings()
        if stored and stored != _config["last"] and stored != config_view(settings):
            changed = {}
            for key, value in stored.items():
                try:
                    if value is not None:
                        changed[key] = CONFIG_KEYS[key](value)
                except Exception:
                    log.warning("Ignored %s=%r from OrcaSlicer's plugin manager", key, value)
            if changed:
                settings = {**settings, **changed}
                save_settings(settings)
                log.info("Took %s from OrcaSlicer's plugin manager", ", ".join(sorted(changed)))
        current = config_view(settings)
        if current != stored and not capability.save_config(json.dumps(current)):
            log.warning("OrcaSlicer did not store Spooler's settings in the plugin manager")
        _config["last"] = current
    except Exception:
        log.exception("Could not sync the plugin manager's settings")


def default_config() -> dict:
    """What the plugin manager's Restore defaults puts back."""
    settings = dict(get_settings())
    defaults = {**settings, "low_stock_grams": LOW_DEFAULT, "plate_check": True,
                "plate_margin_percent": DEFAULT_MARGIN, "weight_display": "both", "show_cart": False,
                "spool_columns": 1, "auto_send": True, "send_saved_copies": True}
    return config_view(defaults)  # The Spoolman address and source stay: they are yours.


def get_spools(spoolman_url: str) -> dict:
    """Return ``{"ok": True, "spools": [...]}`` or ``{"ok": False, "error": "..."}``."""
    path = "spool?allow_archived=true" if display_settings()["archived"] else "spool"
    try:
        data = _spoolman_open(spoolman_url, path)
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
        _report("Spool list", error)
        return {"ok": False, "error": error}
    except Exception as exc:
        _report("Spool list", str(exc), exc_info=True)
        return {"ok": False, "error": str(exc)}
    _report("Spool list", None)
    pinned = getattr(_op, "origin", None)
    if pinned is not None and not origin_live(pinned):
        return {"ok": True, "spools": data}  # read from a source the settings left: don't cache it
    # Archived spools are only for the Spools tab: everything else reads the cache.
    _spool_cache.update(url=spoolman_url, time=time.monotonic(), spools=active_spools(data))
    publish_stock(spoolman_url, data)   # for u1control, only while it shows the stock
    notices = low_stock_crossed(spoolman_url, _spool_cache["spools"])
    if notices:
        threading.Thread(target=lambda: [push_notice("warning", text) for text in notices], daemon=True).start()
    return {"ok": True, "spools": data}


_low_seen: dict = {"url": None, "ids": set()}
_low_lock = threading.Lock()


def low_stock_crossed(url: str, spools: list[dict]) -> list[str]:
    """Notice texts for spools that just dropped below the low-stock grams. The first list for an
    address only seeds the set, so nothing fires at start-up; a refilled spool re-arms."""
    limit = parse_low(get_settings().get("low_stock_grams"))
    low = {str(s.get("id")): s for s in spools
           if limit > 0 and isinstance(s.get("remaining_weight"), (int, float)) and s["remaining_weight"] < limit}
    with _low_lock:
        seeded = _low_seen["url"] == url
        fresh = [s for key, s in low.items() if key not in _low_seen["ids"]]
        _low_seen.update(url=url, ids=set(low))
    if not seeded or not display_settings()["low_notice"]:
        return []
    return [f"Spooler: {_spool_label(s)} is down to {s['remaining_weight']:.0f} g" for s in fresh]


def use_first_id(spools: list[dict]) -> dict:
    """{filament id: spool id}: of 2+ live spools of a filament, the opened one to finish first,
    by first used, else registered, else lowest id."""
    groups: dict = {}
    for s in spools:
        fid = (s.get("filament") or {}).get("id")
        if fid is not None and not s.get("archived"):
            groups.setdefault(fid, []).append(s)
    pick = {}
    for fid, group in groups.items():
        opened = [s for s in group if s.get("first_used") or (s.get("used_weight") or 0) > 0]
        if len(group) > 1 and opened:
            pick[fid] = min(opened, key=lambda s: (s.get("first_used") or s.get("registered") or "\uffff", s.get("id") or 0))["id"]
    return pick


def active_spools(spools: list) -> list:
    return [s for s in spools if isinstance(s, dict) and not s.get("archived")]


def _spoolman_open(base: str, path: str, method: str = "GET", body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors."""
    data = None if body is None else json.dumps(body).encode("utf-8")
    request = urllib.request.Request(f"{base.rstrip('/')}/api/v1/{path}", data=data, method=method,
                                     headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8") or "null")


def clean_url(url: str | None) -> str:
    return (url or "").strip().rstrip("/")


def ping(spoolman_url: str) -> dict:
    """Ask Spoolman for its version, which doubles as a connection test.

    Returns ``{"ok": True, "version": "..."}`` or ``{"ok": False, "error": "..."}``.
    """
    if not spoolman_url:
        return {"ok": False, "error": "No Spoolman URL configured yet"}
    try:
        data = _spoolman_open(spoolman_url, "info")
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
        log.warning("Connection test failed: %s", error)
        return {"ok": False, "error": error}
    except Exception as exc:
        log.exception("Connection test failed")
        return {"ok": False, "error": str(exc)}
    version = data.get("version", "unknown")
    log.info("Connected to Spoolman %s at %s", version, spoolman_url)
    return {"ok": True, "version": version}


BAMBU_HOSTS = {"global": "https://api.bambulab.com", "china": "https://api.bambulab.cn"}
BAMBU_REGIONS = {"global": "Global", "china": "China"}
BAMBU_PATH = "/v1/design-user-service/my/filament/v2"
BAMBU_PAGE = 100
BAMBU_PAGES = 50
BAMBU_TIMEOUT = 10
BAMBU_KEY = "bambu"
BAMBU_UA = f"BBL-Slicer/v02.08.01.51 (OrcaSlicer; {PLUGIN_NAME}/{PLUGIN_VERSION})"
AUTH_FILE = DATA_DIR / "bambu_auth.json"
TFA_HOSTS = {"global": "https://bambulab.com", "china": "https://bambulab.cn"}
LOGIN_PATH = "/v1/user-service/user/login"
CODE_PATH = "/v1/user-service/user/sendemail/code"
SIGN_IN = "Open Settings and sign in to Bambu Cloud."
_pending: dict = {}
_ams_logged: list = []


def parse_source(value: object) -> str:
    return value if value in ("spoolman", "bambu") else "spoolman"


def source() -> str:
    return parse_source(get_settings().get("spool_source"))


def source_name() -> str:
    return "Bambu Cloud" if source() == "bambu" else "Spoolman"


def spool_key() -> str:
    return BAMBU_KEY if source() == "bambu" else get_settings().get("spoolman_url", "")


def configured() -> bool:
    return bool(spool_key())


def parse_region(value: object) -> str:
    return value if value in BAMBU_HOSTS else "global"


def jwt_expiry(token: str) -> float | None:
    try:
        part = token.split(".")[1]
        payload = json.loads(base64.urlsafe_b64decode(part + "=" * (-len(part) % 4)))
        return float(payload["exp"])
    except (IndexError, KeyError, ValueError, TypeError):
        return None


def account_text(auth: dict) -> str:
    who = f"Signed in as {auth['user']}" if auth.get("user") else "Signed in"
    return f"{who} ({BAMBU_REGIONS.get(auth.get('region'), 'Global')})"


def read_auth() -> dict:
    """Sign-in result: ``{"ok": True, token, ...}`` or ``{"ok": False, "error", ...}``."""
    try:
        data = json.loads(AUTH_FILE.read_text(encoding="utf-8"))
        token = data["access_token"]
    except FileNotFoundError:
        return {"ok": False, "account": "Signed out", "signin": True, "error": "Signed out"}
    except (OSError, ValueError, KeyError, TypeError):
        log.exception("Could not read %s", AUTH_FILE)
        return {"ok": False, "account": "Signed out", "signin": True,
                "error": "Your saved Bambu sign-in is unreadable"}
    auth = {"token": token, "region": parse_region(data.get("region")),
            "user": str(data.get("account") or "")}
    auth["account"] = account_text(auth)
    expiry = jwt_expiry(token)
    if expiry is not None and expiry < time.time():
        return {**auth, "ok": False, "account": "Sign-in expired", "signin": True,
                "error": "Your Bambu sign-in has expired"}
    return {**auth, "ok": True}


class BambuError(Exception):
    pass


def _bambu_message(code: int, raw: str) -> str:
    try:
        text = str(json.loads(raw).get("message") or "")
    except (ValueError, AttributeError):
        text = ""
    if text and text.lower() != "success":
        return text
    return "Bambu blocked the request (HTTP 403)" if code == 403 else f"Bambu Cloud returned an error (HTTP {code})"


def _bambu_post(region: str, path: str, body: dict, host: str = "") -> tuple[dict, list[str]]:
    request = urllib.request.Request(
        (host or BAMBU_HOSTS[region]) + path, data=json.dumps(body).encode("utf-8"), method="POST",
        headers={"Content-Type": "application/json", "Accept": "application/json",
                 "User-Agent": BAMBU_UA})
    try:
        with urllib.request.urlopen(request, timeout=BAMBU_TIMEOUT) as resp:
            raw, cookies = resp.read().decode("utf-8", "replace"), resp.headers.get_all("Set-Cookie") or []
    except urllib.error.HTTPError as exc:
        raw = exc.read(2000).decode("utf-8", "replace")
        log.warning("Bambu Cloud %s answered HTTP %s: %s", path, exc.code, raw[:200])
        raise BambuError(_bambu_message(exc.code, raw)) from None
    except urllib.error.URLError as exc:
        raise BambuError(f"Could not reach Bambu Cloud ({exc.reason})") from None
    try:
        data = json.loads(raw) if raw.strip() else {}
    except ValueError:
        raise BambuError("Bambu Cloud sent a reply Spooler doesn't understand") from None
    return (data if isinstance(data, dict) else {}), cookies


def _send_code(region: str, account: str) -> None:
    _bambu_post(region, CODE_PATH, {"email": account, "type": "codeLogin"})


def _after_login(region: str, account: str, reply: dict, cookies: list[str]) -> dict:
    token = str(reply.get("accessToken") or "")
    for cookie in cookies:
        if not token and cookie.startswith("token="):
            token = cookie[6:].split(";")[0]
    if token:
        _pending.clear()
        AUTH_FILE.write_text(json.dumps({"access_token": token, "region": region, "account": account}),
                             encoding="utf-8")
        try:
            os.chmod(AUTH_FILE, 0o600)
        except OSError:
            pass
        _spool_cache.update(url="", time=0.0, spools=[])
        log.info("Signed in to Bambu Cloud (%s)", region)
        return {"ok": True, "step": "done"}
    _pending.update(region=region, account=account)
    if reply.get("loginType") == "verifyCode":
        _send_code(region, account)
        return {"ok": True, "step": "code"}
    if reply.get("loginType") == "tfa" or reply.get("tfaKey"):
        _pending["tfa_key"] = str(reply.get("tfaKey") or "")
        return {"ok": True, "step": "tfa"}
    raise BambuError("Bambu Cloud didn't sign you in")


def bambu_sign_in(data: dict) -> dict:
    """One sign-in step: password, then the 2FA code if asked."""
    action = data.get("action")
    try:
        if action == "sign_out":
            AUTH_FILE.unlink(missing_ok=True)
            _pending.clear()
            _spool_cache.update(url="", time=0.0, spools=[])
            return {"ok": True, "step": "out"}
        if action == "password":
            region = parse_region(data.get("region"))
            account = str(data.get("account") or "").strip()
            password = str(data.get("password") or "")
            if not account or not password:
                raise BambuError("Enter your Bambu email and password")
            reply, cookies = _bambu_post(region, LOGIN_PATH, {"account": account, "password": password})
            return _after_login(region, account, reply, cookies)
        if not _pending:
            raise BambuError("Your sign-in timed out. Enter your email and password again")
        region, account = _pending["region"], _pending["account"]
        if action == "resend":
            _send_code(region, account)
            return {"ok": True, "step": "code"}
        code = str(data.get("code") or "").strip()
        if not code:
            raise BambuError("Enter your Bambu Lab verification code")
        if action == "tfa":
            reply, cookies = _bambu_post(region, "/api/sign-in/tfa",
                                         {"tfaKey": _pending.get("tfa_key", ""), "tfaCode": code},
                                         TFA_HOSTS[region])
        else:
            reply, cookies = _bambu_post(region, LOGIN_PATH, {"account": account, "code": code})
        return _after_login(region, account, reply, cookies)
    except BambuError as exc:
        return {"ok": False, "error": str(exc)}


def _bambu_page(auth: dict, offset: int) -> dict:
    url = f"{BAMBU_HOSTS[auth['region']]}{BAMBU_PATH}?offset={offset}&limit={BAMBU_PAGE}"
    request = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {auth['token']}",
        "Accept": "application/json",
        "User-Agent": BAMBU_UA,
    })
    with urllib.request.urlopen(request, timeout=BAMBU_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if isinstance(data, dict) and "hits" not in data and isinstance(data.get("data"), dict):
        data = data["data"]
    if not isinstance(data, dict) or not isinstance(data.get("hits"), list):
        raise ValueError("Bambu Cloud sent a reply Spooler doesn't understand")
    return data


def fetch_bambu(auth: dict) -> list[dict]:
    hits: list[dict] = []
    for _ in range(BAMBU_PAGES):
        data = _bambu_page(auth, len(hits))
        page = [item for item in data["hits"] if isinstance(item, dict)]
        hits += page
        total = data.get("total")
        if not page or not isinstance(total, int) or len(hits) >= total:
            break
    return hits


def _hex6(value: object) -> str:
    text = str(value or "").lstrip("#")
    return text[:6].upper() if re.fullmatch(r"[0-9A-Fa-f]{6}([0-9A-Fa-f]{2})?", text) else ""


def _grams(value: object) -> float | None:
    """A weight read from Spoolman, Bambu Cloud or a printer: any finite number, 0 included (an
    empty spool is still a spool); None for text, booleans, missing and non-finite values. Card
    actions check what the user typed with _action_grams instead."""
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) else None


def map_bambu(item: dict) -> dict | None:
    """A Bambu Cloud spool in Spoolman's shape."""
    remaining = _grams(item.get("netWeight"))
    if remaining is None:
        return None
    total = _grams(item.get("totalNetWeight"))
    colour = item.get("color")
    if not colour and isinstance(item.get("colors"), list) and item["colors"]:
        colour = item["colors"][0]
    colour = _hex6(colour)
    material = str(item.get("filamentType") or "").strip()
    name = str(item.get("filamentName") or "").strip() or material
    rfid = str(item.get("RFID") or "").strip()
    where = ""
    if item.get("inPrinter"):
        where = " ".join(part for part in (
            str(item.get("deviceName") or "").strip(),
            f"AMS {item['amsId']}" if item.get("amsId") not in (None, "") else "",
            f"slot {item['slotId']}" if item.get("slotId") not in (None, "") else "",
        ) if part)
    spool = {
        "id": item.get("id"),
        "remaining_weight": remaining,
        "archived": str(item.get("status") or "").lower() == "archived",
        "location": where or None,
        "tags": [rfid] if rfid.strip("0") else [],
        "filament": {
            "id": f"{item.get('filamentId') or name}|{colour}",
            "name": name,
            "material": material,
            "color_hex": colour,
            "diameter": 1.75,
            "vendor": {"name": str(item.get("filamentVendor") or "").strip()},
        },
    }
    if item.get("inPrinter") and item.get("slotId") not in (None, ""):
        spool["ams"] = {"printer": str(item.get("deviceName") or "").strip(),
                        "unit": item.get("amsId"), "slot": item.get("slotId")}
    if total is not None and total > 0:
        spool["initial_weight"] = total
        spool["used_weight"] = max(0.0, total - remaining)
        spool["filament"]["weight"] = total
    return spool


def bambu_fetch() -> dict:
    """``{"ok": True, "auth", "spools"}`` or ``{"ok": False, "error", "account"}``."""
    auth = read_auth()
    if not auth["ok"]:
        return auth
    try:
        hits = fetch_bambu(auth)
    except urllib.error.HTTPError as exc:
        body = ""
        try:
            body = exc.read(200).decode("utf-8", "replace")
        except Exception:
            pass
        log.warning("Bambu Cloud answered HTTP %s: %s", exc.code, body)
        if exc.code == 401:
            return {"ok": False, "error": "Bambu Cloud didn't accept your sign-in",
                    "account": auth["account"], "signin": True}
        return {"ok": False, "error": f"Bambu Cloud returned an error (HTTP {exc.code})",
                "account": auth["account"]}
    except urllib.error.URLError as exc:
        return {"ok": False, "error": f"Could not reach Bambu Cloud ({exc.reason})",
                "account": auth["account"]}
    except Exception as exc:
        log.exception("Bambu Cloud request failed")
        return {"ok": False, "error": str(exc), "account": auth["account"]}
    spools = [spool for spool in map(map_bambu, hits) if spool]
    seen = sorted({(sp["ams"]["printer"], str(sp["ams"]["unit"]), str(sp["ams"]["slot"]))
                   for sp in spools if "ams" in sp})
    if seen != _ams_logged:
        _ams_logged[:] = seen
        log.info("Spools in printers (printer, ams, slot): %s", seen)
    if len(spools) != len(hits):
        log.info("Skipped %d Bambu Cloud spools with no remaining weight", len(hits) - len(spools))
    if hits and not spools:
        log.warning("No Bambu Cloud spool had a netWeight (keys: %s)", ", ".join(sorted(hits[0])))
    return {"ok": True, "auth": auth, "spools": spools}


def get_bambu_spools() -> dict:
    result = bambu_fetch()
    if not result["ok"]:
        error = f"{result['error']}. {SIGN_IN}" if result.get("signin") else result["error"]
        _report("Spool list", error)
        return {"ok": False, "error": error}
    _report("Spool list", None)
    _spool_cache.update(url=BAMBU_KEY, time=time.monotonic(), spools=result["spools"])
    return {"ok": True, "spools": result["spools"]}


def bambu_ping() -> dict:
    """Bambu Cloud connection test result."""
    result = bambu_fetch()
    if not result["ok"]:
        log.warning("Bambu Cloud test failed: %s", result["error"])
        return {"ok": False, "error": result["error"], "account": result.get("account", ""),
                "signin": bool(result.get("signin"))}
    log.info("Connected to Bambu Cloud, %d spools", len(result["spools"]))
    return {"ok": True, "count": len(result["spools"]), "account": result["auth"]["account"]}


def load_spools() -> dict:
    with pinned_origin() as origin:
        if origin[0] != BAMBU_KEY:
            ensure_fields()
        result = get_bambu_spools() if origin[0] == BAMBU_KEY else get_spools(origin[0])
    for sp in result.get("spools") or []:
        sp["rfid_tags"] = sorted(spool_tags(sp))
        sp["u1_bound"] = u1_bound(sp.get("location"))
    first = use_first_id(result.get("spools") or [])
    for sp in result.get("spools") or []:
        sp["use_first"] = first.get((sp.get("filament") or {}).get("id")) == sp.get("id")
    table = drying_settings()
    for sp in result.get("spools") or []:
        sp["dry_days"] = drying_days((sp.get("filament") or {}).get("material"), table)
    return result

# --- Filament profiles -------------------------------------------------------------------
# For each of your printers, one OrcaSlicer filament preset per Spoolman filament, written as a
# local preset bundle and hot-reloaded. Each one inherits the closest preset OrcaSlicer already
# has for that printer (so the printer's own tuning is kept), is limited to that printer, and
# carries the filament's colour, vendor, temperatures, density, diameter and cost. It shows up
# under "User presets" in the sidebar's filament dropdown.
#
# OrcaSlicer refuses the whole bundle when any preset in it has an unknown key or a parent it
# can't find, so only keys checked against PrintConfig.cpp are written, and only parents read
# from the live preset list are used.

PROFILE_BUNDLE = "spooler"
PROFILE_STATE = ".spooler-profiles.json"
PROFILE_PREFIX = f"_local/{PROFILE_BUNDLE}/"
# Spoolman material spellings to the material names OrcaSlicer's presets use.
MATERIAL_ALIASES = {
    "PLA+": "PLA", "PLAPLUS": "PLA", "PLAPRO": "PLA", "HSPLA": "PLA", "PLAHS": "PLA",
    "SILKPLA": "PLA", "PLASILK": "PLA", "MATTEPLA": "PLA", "PLAMATTE": "PLA", "PETG+": "PETG",
    "HSPETG": "PETG", "PETGHS": "PETG", "PETGHF": "PETG", "ABS+": "ABS", "NYLON": "PA",
}
# Every bed plate type, so the Spoolman bed temperature holds whichever plate is picked.
BED_TEMP_KEYS = tuple(f"{plate}_plate_temp{layer}"
                      for plate in ("cool", "eng", "hot", "supertack", "textured_cool", "textured")
                      for layer in ("", "_initial_layer"))
# Calibrated settings from the filament's "orca_settings" extra field in Spoolman: a JSON object
# of OrcaSlicer filament keys, either flat (every printer) or in sections, "*" for every printer
# plus one per printer named by a part of its preset name, e.g.
#   {"*": {"filament_ironing_flow": "15%"}, "Snapmaker U1": {"filament_max_volumetric_speed": 20}}
# Only these keys, checked against PrintConfig.cpp, are used; any other is ignored.
ORCA_SETTINGS_FIELD = "orca_settings"
ORCA_SETTINGS_KEYS = frozenset({
    *BED_TEMP_KEYS, "nozzle_temperature", "nozzle_temperature_initial_layer",
    "filament_flow_ratio", "filament_max_volumetric_speed", "pressure_advance",
    "enable_pressure_advance", "filament_retraction_length", "filament_retraction_speed",
    "filament_deretraction_speed", "filament_z_hop", "filament_ironing_flow",
    "filament_ironing_speed", "filament_ironing_spacing", "filament_ironing_inset",
    "fan_min_speed", "fan_max_speed", "slow_down_layer_time", "slow_down_min_speed",
    "filament_shrink", "temperature_vitrification", "filament_density", "filament_diameter",
    "filament_cost", "filament_shrinkage_compensation_z", "filament_notes",
    "nozzle_temperature_range_low", "nozzle_temperature_range_high", "chamber_temperature",
    "overhang_fan_speed", "close_fan_the_first_x_layers", "full_fan_speed_layer",
    "additional_cooling_fan_speed", "filament_minimal_purge_on_wipe_tower",
})
_ignored_keys: set = set()  # orca_settings keys already reported as not used, so the log says it once
# The one listed setting OrcaSlicer holds as text; every other is a number, a percentage or on/off.
TEXT_KEYS = frozenset({"filament_notes"})
# Spoolman extra fields Spooler adds to every filament for the calibration values people set most,
# so they can be filled in Spoolman's own form: {field key: (OrcaSlicer key, label, unit)}. They
# apply to every printer; a value in orca_settings (for every printer or for one) wins over them.
CALIBRATION_FIELDS = {
    "orca_flow_ratio": ("filament_flow_ratio", "Flow ratio", ""),
    "orca_pressure_advance": ("pressure_advance", "Pressure advance", ""),
    "orca_max_volumetric_speed": ("filament_max_volumetric_speed", "Max volumetric speed", "mm³/s"),
}
# OrcaSlicer settings that come from Spoolman's own filament fields. Sending one of them changes
# that field, so a later edit in Spoolman still reaches the preset.
NATIVE_KEYS = {"filament_density": "density", "filament_diameter": "diameter", "filament_cost": "price"}
PROFILE_RETRY = 300  # seconds before a refused set of presets is offered again
_profiles: dict = {"names": {}, "error": "", "count": 0, "failed": ("", 0.0), "gen": None}
_profile_lock = threading.Lock()
_ui_snap: dict = {}
_parent_cache: dict = {"key": None, "parents": []}


def _material_key(material: object) -> str:
    return re.sub(r"[^A-Z0-9+]", "", str(material or "").upper())


def _words(text: object) -> set[str]:
    return {w for w in re.split(r"[^a-z0-9+]+", str(text or "").lower()) if w}


def _first(value: object) -> str:
    items = split_list(value)
    return items[0] if items else ""


def _parent_ok(name: str) -> bool:
    """Instantiable presets only: not a template, base or internal root."""
    low = name.lower()
    return not (low.startswith("fdm_") or "@base" in low or low.endswith(" base") or "template" in low)


def parent_candidates(filaments) -> list[dict]:
    """The system filament presets a generated profile may inherit from."""
    found = []
    for index in range(filaments.size()):
        preset = filaments.preset(index)
        if not preset.is_system or preset.is_default or not _parent_ok(preset.name):
            continue
        printers = [p for p in split_list(preset.config_value("compatible_printers")) if p]
        condition = str(preset.config_value("compatible_printers_condition") or "").strip()
        if not printers and condition:
            continue  # Can't evaluate the condition here, so don't guess.
        found.append({"name": preset.name, "vendor": _first(preset.config_value("filament_vendor")),
                      "type": _first(preset.config_value("filament_type")), "printers": printers})
    return found


def _type_score(candidate: str, material: str) -> int:
    want = {_material_key(material), _material_key(MATERIAL_ALIASES.get(_material_key(material), material))}
    have = _material_key(candidate)
    if have in want:
        return 6
    return 1 if have and any(w.startswith(have) or have.startswith(w) for w in want if w) else -1


def parent_score(candidate: dict, filament: dict, target: str) -> int | None:
    """How well a system preset fits a filament on one printer; None when it can't be used."""
    specific = target in candidate["printers"]
    if candidate["printers"] and not specific:
        return None
    material = str(filament.get("material") or "")
    score = _type_score(candidate["type"], material)
    if score < 0:
        return None
    vendor = _norm((filament.get("vendor") or {}).get("name"))
    theirs = _norm(candidate["vendor"])
    if vendor and theirs == vendor:
        score += 5
    elif theirs == "generic":
        score += 1
    elif theirs:
        score -= 2
    base = candidate["name"].split("@")[0]
    extra = _words(base) - _words(candidate["vendor"]) - _words(candidate["type"]) - {"generic"}
    named = _words(filament.get("name")) | _words(material)
    score += sum(2 if w in named else -3 for w in extra)
    return score + (3 if specific else 0)


def best_parent(filament: dict, target: str, parents: list[dict]) -> str:
    """The best-fitting system preset for a filament on one printer, or ''."""
    best = None
    for candidate in parents:
        score = parent_score(candidate, filament, target)
        if score is not None and (best is None or (score, -len(candidate["name"])) > best[0]):
            best = ((score, -len(candidate["name"])), candidate["name"])
    return best[1] if best else ""


WINDOWS_RESERVED = re.compile(r"(CON|PRN|AUX|NUL|COM\d|LPT\d)(\..*)?", re.I)
# OrcaSlicer blocks any plugin write to a path containing these words, and a preset's name is its
# file name, so they are split with an invisible zero-width space ("Con\u200bfetti").
DENIED_WORDS = re.compile(r"(?i)secret|cert|conf")
NAME_MAX = 60  # with " #id @printer" (LABEL_MAX) it stays under Windows' 260-character path limit
LABEL_MAX = 30


def _safe_name(text: str) -> str:
    name = re.sub(r'[\x00-\x1f\u200b\\/:*?"<>|;@]', " ", unicodedata.normalize("NFC", text))
    name = re.sub(r"\s+", " ", name).strip(" .")[:NAME_MAX].strip(" .")
    name = f"_{name}" if WINDOWS_RESERVED.fullmatch(name) else name
    return DENIED_WORDS.sub(lambda m: m.group(0)[0] + "\u200b" + m.group(0)[1:], name)


def profile_name(filament: dict) -> str:
    vendor = str((filament.get("vendor") or {}).get("name") or "").strip()
    name = str(filament.get("name") or "").strip()
    material = str(filament.get("material") or "").strip()
    if material and _norm(material) not in _norm(name):
        name = f"{material} {name}".strip()
    if vendor and _norm(vendor) not in _norm(name):
        name = f"{vendor} {name}"
    return _safe_name(name) or f"Spoolman filament {filament.get('id')}"


def _num(value: object) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or value <= 0:
        return None
    return value


def _fmt(value: float) -> str:
    return str(int(value)) if float(value).is_integer() else f"{value:.4g}"


def profile_colour(filament: dict) -> str:
    multi = str(filament.get("multi_color_hexes") or "").split(",")
    return _hex6(filament.get("color_hex")) or _hex6(multi[0].strip()) or "FFFFFF"


def profile_preset(filament: dict, name: str, parent: str, target: str) -> dict:
    """The preset JSON for one Spoolman filament on one printer. Values are lists of strings,
    as OrcaSlicer stores them; one value applies to every nozzle variant of the parent."""
    vendor = str((filament.get("vendor") or {}).get("name") or "").strip()
    preset = {
        "type": "filament", "name": name, "from": "User", "instantiation": "true",
        "inherits": parent, "version": "1.0.0",
        "compatible_printers": [target], "compatible_printers_condition": "",
        "filament_settings_id": [name],
        # The colour OrcaSlicer gives a filament slot when this preset is picked for it.
        "default_filament_colour": ["#" + profile_colour(filament)],
    }
    if vendor:
        preset["filament_vendor"] = [vendor]
    extruder, bed = _num(filament.get("settings_extruder_temp")), _num(filament.get("settings_bed_temp"))
    if extruder:
        preset["nozzle_temperature"] = [_fmt(extruder)]
        preset["nozzle_temperature_initial_layer"] = [_fmt(extruder)]
    if bed:
        for key in BED_TEMP_KEYS:
            preset[key] = [_fmt(bed)]
    for key, field in (("filament_density", "density"), ("filament_diameter", "diameter")):
        value = _num(filament.get(field))
        if value:
            preset[key] = [_fmt(value)]
    price, weight = _num(filament.get("price")), _num(filament.get("weight"))
    if price and weight:
        preset["filament_cost"] = [_fmt(round(price / weight * 1000, 2))]
    for field, (key, _label, _unit) in CALIBRATION_FIELDS.items():
        value = extra_number(filament, field)
        if value is not None:
            preset[key] = [_fmt(value)]
            if key == "pressure_advance":
                preset["enable_pressure_advance"] = ["1"]
    preset.update(orca_settings(filament, target))
    return preset


def extra_number(filament: dict, field: str) -> float | None:
    """A number extra field of a Spoolman filament (stored as JSON text), or None when unset."""
    raw = (filament.get("extra") or {}).get(field)
    try:
        value = json.loads(raw) if isinstance(raw, str) else raw
    except ValueError:
        return None
    if isinstance(value, str):
        value = _number(value)
    return float(value) if isinstance(value, (int, float)) and not isinstance(value, bool) else None


_fields_ready: set = set()
_fields_failed: dict = {}  # Spoolman address: when adding the fields last failed, to retry later


def ensure_fields() -> None:
    """Add Spooler's calibration fields to Spoolman's filament form, once per Spoolman address.
    Never raises: a Spoolman that refuses them only means the fields can't be filled in there."""
    pinned = getattr(_op, "origin", None)
    url = pinned[0] if pinned else clean_url(get_settings().get("spoolman_url"))
    if not url or url == BAMBU_KEY or url in _fields_ready or time.monotonic() - _fields_failed.get(url, -PROFILE_RETRY) < PROFILE_RETRY:
        return
    try:
        have = {field.get("key") for field in spoolman_call("GET", "field/filament") or []}
        for order, (field, (_key, label, unit)) in enumerate(CALIBRATION_FIELDS.items(), start=100):
            if field not in have:
                body = {"name": label, "field_type": "float", "order": order}
                if unit:
                    body["unit"] = unit
                spoolman_call("POST", f"field/filament/{field}", body)
                log.info("Added the %s field to Spoolman", field)
        if DRIED_FIELD not in {field.get("key") for field in spoolman_call("GET", "field/spool") or []}:
            spoolman_call("POST", f"field/spool/{DRIED_FIELD}", {"name": "Dried", "field_type": "datetime", "order": 100})
            log.info("Added the %s field to Spoolman", DRIED_FIELD)
        _fields_ready.add(url)
    except Exception as exc:
        log.warning("Could not add Spooler's fields to Spoolman: %s", exc)
        _fields_failed[url] = time.monotonic()


def orca_settings_data(filament: dict) -> dict | None:
    """The filament's orca_settings field as {section: settings}, a flat object being the "*"
    section; {} when the field is empty, None when it isn't a JSON object."""
    raw = (filament.get("extra") or {}).get(ORCA_SETTINGS_FIELD)
    try:
        data = json.loads(raw) if isinstance(raw, str) else raw
        data = json.loads(data) if isinstance(data, str) and data.strip() else data  # Spoolman stores text as JSON
    except ValueError:
        return None
    if data is None or (isinstance(data, str) and not data.strip()):
        return {}
    if not isinstance(data, dict):
        return None
    return data if any(isinstance(v, dict) for v in data.values()) else {"*": data}


def _number(text: str) -> float | None:
    try:
        return float(text.rstrip("%"))
    except ValueError:
        return None


def _one_value(key: str, value: object) -> bool:
    """A value OrcaSlicer can take for the setting: text holding one number, percentage or "nil"
    for a number setting, since "0,95" would reach it as the two values 0 and 95."""
    if isinstance(value, bool) or not isinstance(value, (str, int, float)):
        return False
    return key in TEXT_KEYS or not isinstance(value, str) or value == "nil" or _number(value) is not None


def orca_settings(filament: dict, target: str) -> dict:
    """The allowed keys of the filament's orca_settings extra field that apply to one printer,
    as preset values. A field that isn't a JSON object is ignored."""
    data = orca_settings_data(filament)
    if not data:
        return {}
    low = target.lower()
    sections = [data.get("*")] + [v for k, v in data.items() if k != "*" and k.lower() in low]
    out = {}
    for section in sections:
        for key, value in (section.items() if isinstance(section, dict) else ()):
            values = value if isinstance(value, list) else [value]
            if key in ORCA_SETTINGS_KEYS and values and all(_one_value(key, v) for v in values):
                out[key] = [v if isinstance(v, str) else _fmt(v) for v in values]
            elif key not in ORCA_SETTINGS_KEYS and key not in _ignored_keys:
                _ignored_keys.add(key)
                log.warning("orca_settings of filament %s: %s is not a setting Spooler applies; ignored",
                            filament.get("id"), key)
    return out


def stocked_filaments(spools: list[dict]) -> list[dict]:
    """Each filament that has at least one spool not archived, in Spoolman id order."""
    seen: dict = {}
    for spool in spools or []:
        filament = spool.get("filament") if isinstance(spool, dict) else None
        if spool.get("archived") or not isinstance(filament, dict) or filament.get("id") is None:
            continue
        seen.setdefault(filament["id"], filament)
    return [seen[key] for key in sorted(seen, key=lambda k: str(k).zfill(12))]


def profile_names(spools: list[dict], printers: list[dict]) -> dict:
    """{(filament id, printer preset): preset name}, unique ignoring case."""
    by_key: dict = {}
    taken: set[str] = set()
    for printer in printers:
        label = _safe_name(printer["label"])[:LABEL_MAX].strip()
        for filament in stocked_filaments(spools):
            name = f"{profile_name(filament)} @{label}"
            if name.casefold() in taken:
                name = f"{profile_name(filament)} #{filament['id']} @{label}"
            taken.add(name.casefold())
            by_key[(filament["id"], printer["target"])] = name
    return by_key


def profile_files(spools: list[dict], snapshot: dict) -> tuple[dict, dict]:
    """({file name: preset dict}, {(filament id, printer preset): preset name}). A filament with
    no usable parent on a printer is left out for that printer."""
    files: dict = {}
    by_key: dict = {}
    filaments = {f["id"]: f for f in stocked_filaments(spools)}
    printers = {p["target"]: p for p in snapshot.get("printers") or []}
    for (fid, target), name in profile_names(spools, list(printers.values())).items():
        parent = best_parent(filaments[fid], target, snapshot.get("parents") or [])
        if not parent:
            continue
        files[f"{name}.json"] = profile_preset(filaments[fid], name, parent, target)
        by_key[(fid, target)] = name
    return files, by_key


def _orca_data_dir() -> Path | None:
    for parent in PLUGIN_DIR.parents:
        if parent.name == "orca_plugins":
            return parent.parent
    return DATA_DIR.parent if DATA_DIR.parent.name == "OrcaSlicer" else None


def profile_user_folder(bundle, root: Path | None) -> str:
    """The account's preset folder, from where a user preset is stored; "" when none is."""
    for collection in (bundle.filaments, bundle.prints, bundle.printers):
        for index in range(collection.size()):
            path = Path(collection.preset(index).file or "")
            try:
                parts = path.relative_to(root / "user").parts if root else ()
            except ValueError:
                continue
            if len(parts) > 1:
                return parts[0]
    return ""


def _root_printer(printers, preset) -> str:
    """The system printer preset a printer preset comes from."""
    seen = set()
    while preset is not None and not preset.is_system and preset.name not in seen:
        seen.add(preset.name)
        parent = str(preset.config_value("inherits") or "").strip()
        preset = printers.find_preset(parent) if parent else None
    return preset.name if preset is not None and preset.is_system else ""


def target_printers(bundle) -> list[dict]:
    """Your printers: the system presets behind every printer preset with a host address, and
    behind the selected printer, each with a short label and the hosts that point at it."""
    printers = bundle.printers
    found: dict = {}

    def add(preset, host: str = "") -> None:
        target = _root_printer(printers, preset)
        if not target:
            return
        entry = found.setdefault(target, {"target": target, "hosts": []})
        if host and host not in entry["hosts"]:
            entry["hosts"].append(host)
        root = printers.find_preset(target)
        entry["model"] = str(root.config_value("printer_model") or "").strip() if root else ""
        # Numbers serialize comma-separated ("0.4,0.4"), strings semicolon-separated.
        nozzle = str(root.config_value("nozzle_diameter") or "") if root else ""
        entry["nozzle"] = re.split(r"[,;]", nozzle)[0].strip()

    for index in range(printers.size()):
        preset = printers.preset(index)
        host = moon_base(preset.config_value("print_host"))
        if host and preset.is_visible:
            add(preset, host)
    add(printers.selected_preset())
    models = [e.get("model") for e in found.values()]
    for entry in found.values():
        model = entry.get("model") or entry["target"]
        clash = models.count(entry.get("model")) > 1 and entry.get("nozzle")
        entry["label"] = _safe_name(f"{model} {entry['nozzle']}" if clash else model) or "Printer"
    return list(found.values())


_project: dict = {"n": 0}  # counts projects opened or started, so a run can tell one changed


def profile_snapshot() -> dict | None:
    """What profile_sync and the Load action need from OrcaSlicer. Call it on the UI thread."""
    try:
        bundle = orca.host.preset_bundle()
        filaments = bundle.filaments
        key = (filaments.size(), bundle.printers.size())
        if _parent_cache["key"] != key:
            _parent_cache.update(key=key, parents=parent_candidates(filaments))
        printers = target_printers(bundle)
        selected = _root_printer(bundle.printers, bundle.printers.selected_preset())
        current = bundle.current_filament_preset_names()
        snap = {"names": set(filaments.preset_names()), "parents": _parent_cache["parents"],
                "printers": printers, "selected": selected,
                "folder": profile_user_folder(bundle, _orca_data_dir()),
                "host": moon_base(bundle.full_config_value("print_host")),
                "slots": len(current),
                # Each slot's preset and whether it is a system one, as OrcaSlicer's own sync picks.
                "current": [(name, bool(getattr(filaments.find_preset(name), "is_system", False)))
                            for name in current],
                "gen": _ui_snap.get("gen", 0) + 1, "project": _project["n"]}
    except Exception:
        log.exception("Could not read the presets")
        return None
    # Key by key, never empty in between: worker threads read it while this runs.
    _ui_snap.update(snap)
    for key in set(_ui_snap) - set(snap):
        _ui_snap.pop(key, None)
    return snap


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{threading.get_ident()}.tmp")
    try:
        tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding="utf-8")
        os.replace(tmp, path)
    except OSError:
        tmp.unlink(missing_ok=True)
        raise


def profile_digest(files: dict) -> str:
    return hashlib.sha256(json.dumps(files, sort_keys=True).encode("utf-8")).hexdigest()


def synced_digest(target: Path) -> str:
    try:
        return str(json.loads((target / PROFILE_STATE).read_text(encoding="utf-8")).get("hash") or "")
    except (OSError, ValueError, AttributeError):
        return ""


def bundle_files(target: Path) -> dict | None:
    """Every file of an installed bundle as {path relative to it: bytes}; None when there is none."""
    if not target.is_dir():
        return None
    return {path.relative_to(target).as_posix(): path.read_bytes()
            for path in target.rglob("*") if path.is_file()}


def restore_bundle(target: Path, saved: dict | None) -> None:
    """Put a bundle back as bundle_files() read it (none: remove it), each file in one step."""
    if saved is None:
        shutil.rmtree(target, ignore_errors=True)
        return
    for path in [p for p in target.rglob("*") if p.is_file()]:
        if path.relative_to(target).as_posix() not in saved:
            path.unlink(missing_ok=True)
    for rel, raw in saved.items():
        path = target / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_name(f".{path.name}.{threading.get_ident()}.tmp")
        try:
            tmp.write_bytes(raw)
            os.replace(tmp, path)
        except OSError:
            tmp.unlink(missing_ok=True)
            raise
    log.info("Put back the last filament presets OrcaSlicer accepted")


def write_profiles(target: Path, files: dict) -> None:
    """Make target/filament hold exactly these presets."""
    for preset in files.values():
        json.dumps(preset)  # every one must be writable before any file is replaced
    folder = target / "filament"
    for name, preset in files.items():
        _write_json(folder / name, preset)
    for old in folder.glob("*.json"):
        if old.name in files:
            continue
        # On a case-insensitive disk "a.json" and "A.json" are one file: keep it.
        same = [folder / n for n in files if n.casefold() == old.name.casefold()]
        if not any(p.exists() and os.path.samefile(p, old) for p in same):
            old.unlink()
    _write_json(target / "bundle_metadata.json",
                {"id": PROFILE_BUNDLE, "name": f"{PLUGIN_NAME} (Spoolman)", "version": PLUGIN_VERSION})


def profile_folders(root: Path, snapshot: dict) -> list[str]:
    """Account folders to try: the one a user preset showed, else each one under user/."""
    if snapshot.get("folder"):
        return [snapshot["folder"]]
    try:
        found = sorted(p.name for p in (root / "user").iterdir() if p.is_dir() and p.name != "default")
    except OSError:
        found = []
    return found + ["default"]


def offered_bundles() -> object:
    """The local bundle ids OrcaSlicer offers for reload, for the log; None when it can't say."""
    list_ids = getattr(orca.host.preset.bundles, "list_ids", None)
    try:
        return list(list_ids()) if callable(list_ids) else None
    except Exception:
        return None


def _install_profiles(root: Path, snapshot: dict, files: dict, digest: str, force: bool = False) -> None:
    """Write the bundle where OrcaSlicer reads it and reload it. Raises when it is refused."""
    last = None
    for folder in profile_folders(root, snapshot):
        target = root / "user" / folder / "_local" / PROFILE_BUNDLE
        if not force and synced_digest(target) == digest:
            return
        saved = bundle_files(target)  # the last bundle OrcaSlicer took, to put back if this fails
        try:
            write_profiles(target, files)
            orca.host.preset.bundles.reload_local(PROFILE_BUNDLE)
        except Exception as exc:
            restore_bundle(target, saved)
            if not isinstance(exc, RuntimeError):
                raise
            last = exc
            log.info("OrcaSlicer did not take the bundle in %s: %s (bundles it offers: %s)",
                     folder, exc, offered_bundles())
            if "does not exist" not in str(exc):
                raise
            continue  # Not the signed-in account's folder.
        # Only after OrcaSlicer accepted the bundle, so a refused one is tried again.
        _write_json(target / PROFILE_STATE, {"hash": digest})
        log.info("Synced %d filament profiles from Spoolman into %s", len(files), folder)
        return
    raise last or RuntimeError("No OrcaSlicer user folder accepted the presets")


# --- Files shared with u1control --------------------------------------------------------
# u1control (github.com/bloodf/u1control) runs the Snapmaker U1 from OrcaSlicer and reads these
# from <OrcaSlicer data folder>/spooler/, so both plugins pick the same preset for a spool and
# only one of them changes the plate's slots:
#   profiles.json:   {"version": 1, "updated": <unix s>,
#                     "filaments": {"<filament id>": {"<printer label>": "_local/spooler/<preset>"}}}
#   keep_slots.json: {"active": true, "printer": "<label>", "ts": <unix s>} while Keep Slots Synced
#                    runs, refreshed every pass; {"active": false, "ts": ...} once it stops.
BRIDGE_PROFILES = "profiles.json"
BRIDGE_KEEP = "keep_slots.json"
_bridge: dict = {"profiles": None}


def bridge_dir() -> Path:
    """<OrcaSlicer data folder>/spooler, where u1control looks for these files."""
    root = _orca_data_dir()
    return root / PROFILE_BUNDLE if root else DATA_DIR


def profile_map(by_key: dict, printers: list[dict]) -> dict:
    """{"<filament id>": {"<printer label>": "_local/spooler/<preset>"}} for every generated preset."""
    labels = {p["target"]: p["label"] for p in printers}
    out: dict = {}
    for (fid, target), name in sorted(by_key.items(), key=lambda item: (str(item[0][0]), item[0][1])):
        if target in labels:
            out.setdefault(str(fid), {})[labels[target]] = PROFILE_PREFIX + name
    return out


def publish_profiles(by_key: dict, printers: list[dict]) -> None:
    """Write profiles.json when the presets changed (or it is missing). Never raises."""
    filaments = profile_map(by_key, printers)
    path = bridge_dir() / BRIDGE_PROFILES
    if filaments == _bridge["profiles"] and path.exists():
        return
    try:
        _write_json(path, {"version": 1, "updated": int(time.time()), "filaments": filaments})
        _bridge["profiles"] = filaments
    except OSError as exc:
        log.warning("Could not write %s: %s", path, exc)


def mark_keep_slots(active: bool, printer: str = "") -> None:
    """Tell u1control whether Keep Slots Synced owns the plate's slots. Never raises."""
    marker = {"active": True, "printer": printer, "ts": int(time.time())} if active else \
        {"active": False, "ts": int(time.time())}
    try:
        _write_json(bridge_dir() / BRIDGE_KEEP, marker)
    except OSError as exc:
        log.warning("Could not write %s: %s", BRIDGE_KEEP, exc)


def label_for_target(target: str) -> str:
    """Spooler's label for a printer ("Snapmaker U1"), from the last snapshot; "" when unknown."""
    return next((p["label"] for p in _ui_snap.get("printers") or [] if p["target"] == target), "")


# --- Presence and stock for u1control -------------------------------------------------------
# OrcaSlicer's plugin API can't list the loaded plugins, pass messages between them or hide a tab;
# its data folder is shared and writable by every plugin. So each plugin writes
# <data folder>/<plugin>/presence.json every PEER_BEAT seconds while it is loaded:
#   {"schema": "orca-plugin-presence", "version": 1, "plugin": "spooler", "plugin_version": ...,
#    "session": <random per load>, "pid": <process>, "started", "ts": <unix s>, "state": "active"|"stopped", ...}
# A peer counts as running only when its file is "active", fresh (PEER_FRESH s) and of this process.
# While u1control runs and its tab shows the stock (its presence "wants" it), Spooler writes
# <data folder>/spooler/stock.json from its Spoolman reads; nothing is written to Spoolman or a
# printer for it. u1control links spools with its own commands; filament use stays with u1control.
PEER_SCHEMA = "orca-plugin-presence"
PEER_VERSION = 1
STOCK_SCHEMA = "spooler-stock"
STOCK_VERSION = 1
PEER_BEAT = 5.0
PEER_FRESH = 20.0
STOCK_EVERY = 30.0      # seconds between stock re-reads while u1control shows the stock
STOCK_ROWS = 2000
PEER_FILE = "presence.json"
STOCK_FILE = "stock.json"
U1CONTROL = "u1control"
_peer: dict = {"session": "", "started": 0.0, "users": 0, "stop": None, "thread": None,
               "seq": 0, "stock_at": 0.0, "served": None}
_peer_lock = threading.Lock()


def public_url(url: str) -> str:
    """A Spoolman address without user name or password, for files other plugins read."""
    try:
        parts = urllib.parse.urlsplit(clean_url(url))
    except ValueError:
        return ""
    if not parts.hostname:
        return clean_url(url)
    host = f"[{parts.hostname}]" if ":" in parts.hostname else parts.hostname
    try:
        port = f":{parts.port}" if parts.port else ""
    except ValueError:
        return ""
    return urllib.parse.urlunsplit((parts.scheme, host + port, parts.path, "", ""))


def peer_alive(doc: object, plugin: str, now: float | None = None) -> bool:
    """Whether a presence file is of `plugin`, running now in this OrcaSlicer process."""
    now = time.time() if now is None else now
    if not isinstance(doc, dict) or doc.get("schema") != PEER_SCHEMA or doc.get("version") != PEER_VERSION:
        return False
    ts = doc.get("ts")
    return (doc.get("plugin") == plugin and doc.get("state") == "active" and doc.get("pid") == os.getpid()
            and isinstance(doc.get("session"), str) and bool(doc["session"])
            and isinstance(ts, (int, float)) and not isinstance(ts, bool) and -5 <= now - ts <= PEER_FRESH)


def _read_peer(plugin: str) -> dict | None:
    root = _orca_data_dir()
    if root is None:
        return None
    try:
        data = json.loads((root / plugin / PEER_FILE).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return data if isinstance(data, dict) else None


def presence_doc(state: str = "active") -> dict:
    settings = get_settings()
    src = parse_source(settings.get("spool_source"))
    return {"schema": PEER_SCHEMA, "version": PEER_VERSION, "plugin": PROFILE_BUNDLE, "plugin_version": PLUGIN_VERSION,
            "session": _peer["session"], "pid": os.getpid(), "started": int(_peer["started"]), "ts": time.time(),
            "state": state, "provides": {"stock": STOCK_VERSION},
            "spoolman": {"source": src, "origin": public_url(settings.get("spoolman_url")) if src == "spoolman" else ""}}


def publish_presence(state: str = "active") -> bool:
    if _orca_data_dir() is None or not _peer["session"]:
        return False
    try:
        _write_json(bridge_dir() / PEER_FILE, presence_doc(state))
        return True
    except OSError as exc:
        log.warning("Could not write %s: %s", PEER_FILE, exc)
        return False


def u1control_wants() -> dict | None:
    """u1control's stock request while it runs and its tab shows the stock; else None."""
    doc = _read_peer(U1CONTROL)
    if not peer_alive(doc, U1CONTROL):
        return None
    wants = doc.get("wants") if isinstance(doc.get("wants"), dict) else {}
    until = wants.get("stock_until")
    if not isinstance(until, (int, float)) or isinstance(until, bool) or until < time.time():
        return None
    request = wants.get("stock_request")
    return {"request": request if isinstance(request, int) and not isinstance(request, bool) else 0}


def peer_context() -> dict:
    """For the page: whether U1 Control runs in this OrcaSlicer now (its tab holds the printer and spool links).
    Read-only; never sends anything to a printer. Never raises."""
    try:
        return {"peers": {"u1control": peer_alive(_read_peer(U1CONTROL), U1CONTROL)}}
    except Exception:  # noqa: BLE001 - a hint for the page, never worth failing the spool list
        return {"peers": {"u1control": False}}


def spools_message_extras(result: dict) -> dict:
    """Fields every "spools" message carries besides the list: the peer hint and, on a failed read, a stable
    error code ("read_failed") the page can word in its own language; the English "error" text stays."""
    extras = peer_context()
    if not result.get("ok", True) and "error_code" not in result:
        extras["error_code"] = "read_failed"
    return extras


def stock_row(spool: dict, limit: float, first: dict) -> dict:
    filament = spool.get("filament") if isinstance(spool.get("filament"), dict) else {}
    vendor = filament.get("vendor") if isinstance(filament.get("vendor"), dict) else {}
    remaining = spool.get("remaining_weight")
    multi = filament.get("multi_color_hexes")
    return {"id": spool.get("id"), "filament_id": filament.get("id"), "name": filament.get("name") or "",
            "vendor": vendor.get("name") or "", "material": filament.get("material") or "",
            "colour": filament.get("color_hex") or "", "colours": multi.split(",") if isinstance(multi, str) else [],
            "remaining": remaining, "initial": spool.get("initial_weight"), "location": spool.get("location") or "",
            "low": limit > 0 and isinstance(remaining, (int, float)) and remaining < limit,
            "use_first": first.get(filament.get("id")) == spool.get("id"), "u1_bound": u1_bound(spool.get("location"))}


def publish_stock(url: str, spools: list | None, error: str = "", request: int | None = None) -> bool:
    """Write stock.json for u1control, only while it runs and asks for it. Never raises."""
    origin = current_origin()
    wants = u1control_wants()
    if wants is None or _orca_data_dir() is None or not _peer["session"] or origin[0] != clean_url(url):
        return False
    live = active_spools(spools or [])
    limit = parse_low(get_settings().get("low_stock_grams"))
    first = use_first_id(live)
    with _peer_lock:
        _peer["seq"] += 1
        seq = _peer["seq"]
    doc = {"schema": STOCK_SCHEMA, "version": STOCK_VERSION, "session": _peer["session"], "seq": seq, "ts": time.time(),
           "origin": {"url": public_url(url), "gen": origin[1], "source": source()},
           "request": wants["request"] if request is None else request,
           "low_stock_grams": limit, "spools": [stock_row(s, limit, first) for s in live[:STOCK_ROWS]]}
    if error:
        doc["error"] = error[:200]
    try:
        _write_json(bridge_dir() / STOCK_FILE, doc)
    except OSError as exc:
        log.warning("Could not write %s: %s", STOCK_FILE, exc)
        return False
    _peer["stock_at"] = time.monotonic()
    return True


def refresh_stock(wants: dict) -> None:
    """Read Spoolman (read only: no fields are created) and publish the list for u1control."""
    _peer["served"] = wants["request"]
    with pinned_origin() as origin:
        if origin[0] in ("", BAMBU_KEY):
            # Not Spoolman: say so, so u1control can explain why there is no stock to show.
            if _orca_data_dir() is not None and _peer["session"]:
                try:
                    _write_json(bridge_dir() / STOCK_FILE, {
                        "schema": STOCK_SCHEMA, "version": STOCK_VERSION, "session": _peer["session"], "seq": 0,
                        "ts": time.time(), "origin": {"url": "", "gen": origin[1], "source": source() if origin[0] else ""},
                        "request": wants["request"], "spools": []})
                except OSError as exc:
                    log.warning("Could not write %s: %s", STOCK_FILE, exc)
            _peer["stock_at"] = time.monotonic()
            return
        result = get_spools(origin[0])   # publishes through its hook when the read succeeds
        if not result.get("ok"):
            publish_stock(origin[0], [], result.get("error") or "Spoolman could not be read", wants["request"])


def peer_tick() -> None:
    """One heartbeat: say Spooler runs, and refresh the stock when u1control shows it. Never raises."""
    try:
        publish_presence()
        wants = u1control_wants()
        if wants is None:
            return
        due = time.monotonic() - _peer["stock_at"] >= STOCK_EVERY
        if due or wants["request"] != _peer["served"]:
            refresh_stock(wants)
    except Exception:
        log.exception("Presence for u1control failed")


def start_presence() -> None:
    """Called from each Spooler capability's on_load (OrcaSlicer calls it whether or not the tab is
    enabled); the heartbeat runs until the last of them unloads."""
    with _peer_lock:
        _peer["users"] += 1
        if _peer["thread"] is not None:
            return
        _peer.update(session=os.urandom(8).hex(), started=time.time(), stop=threading.Event(), seq=0,
                     stock_at=0.0, served=None)
        stop = _peer["stop"]

        def beat():
            while not stop.wait(PEER_BEAT):
                peer_tick()
        publish_presence()   # visible from load on, not only after the first beat
        _peer["thread"] = threading.Thread(target=beat, name="spooler-presence", daemon=True)
        _peer["thread"].start()


def stop_presence() -> None:
    with _peer_lock:
        _peer["users"] = max(0, _peer["users"] - 1)
        if _peer["users"] or _peer["thread"] is None:
            return
        thread, stop = _peer["thread"], _peer["stop"]
        _peer.update(thread=None, stop=None)
    stop.set()
    if thread is not threading.current_thread():
        thread.join(2.0)
    publish_presence("stopped")
    _peer["session"] = ""


def location_names(target: str) -> tuple:
    """The printer names a u1control location may start with for this printer: Spooler's label,
    the printer model (the label without the nozzle Spooler adds when two presets share a model)."""
    printer = next((p for p in _ui_snap.get("printers") or [] if p["target"] == target), {})
    return tuple(name for name in dict.fromkeys((printer.get("label"), printer.get("model"))) if name)


def profile_sync(spools: list[dict], snapshot: dict | None, force: bool = False) -> dict:
    """Write and hot-reload the Spoolman filament presets. Never raises. force (Sync Presets)
    rewrites and reloads them even when nothing changed or a refused set is backing off."""
    if not snapshot:
        return dict(_profiles)
    with _profile_lock:
        root = _orca_data_dir()
        files, by_key = profile_files(spools, snapshot)
        digest = profile_digest(files)
        failed, when = _profiles["failed"]
        if not force and digest == failed and time.monotonic() - when < PROFILE_RETRY:
            return dict(_profiles)
        try:
            if root is None:
                raise RuntimeError("OrcaSlicer's data folder was not found")
            _install_profiles(root, snapshot, files, digest, force)
            pinned = getattr(_op, "origin", None)
            if pinned is not None and not origin_live(pinned):
                # Built from a source the settings left: its names must not map ids of the new one,
                # nor reach profiles.json. The next refresh builds them from the new source.
                raise OriginChanged()
            _profiles.update(names=by_key, count=len(files), error="", failed=("", 0.0),
                             gen=pinned[1] if pinned else None)
            publish_profiles(by_key, snapshot.get("printers") or [])
            _report("Profile sync", None)
        except Exception as exc:
            _profiles.update(error=str(exc), failed=(digest, time.monotonic()))
            _report("Profile sync", str(exc), exc_info=True)
        return dict(_profiles)


def load_spools_synced(snapshot: dict | None, force: bool = False) -> dict:
    """The spool list, after syncing the filament profiles from it. For worker threads."""
    with pinned_origin():
        result = load_spools()
        if result.get("ok") and snapshot:
            state = profile_sync(active_spools(result["spools"]), snapshot, force)
            result["profiles"] = {"count": state["count"], "error": state["error"]}
    return result


def fresh_spools(snapshot: dict | None, force: bool = False) -> dict:
    """load_spools_synced for a page: read again when the source changed while it ran, so a list
    from the old source never reaches a page that now shows the new one."""
    for _ in range(3):
        with pinned_origin() as origin:
            result = load_spools_synced(snapshot, force)
        if origin_live(origin):
            # The page sends it back with card actions and bookings: ids picked from this list
            # are only written while this source is still the one in Settings.
            return {**result, "origin": origin[1]}
    return {"ok": False, "error": "The spool source kept changing while loading; refresh to try again."}


def start_preset_sync(post) -> None:
    """Sync Presets: read Spoolman now and rebuild every Spooler filament preset, even when nothing
    changed. Call it on the UI thread; post() gets {"type": "sent", "ok": ..., "text": ...}."""
    if source() != "spoolman":
        post({"type": "sent", "ok": False, "text": "Syncing presets needs Spoolman as the source."})
        return
    snapshot = refresh_snapshot()
    if snapshot is None:
        post({"type": "sent", "ok": False, "text": "Could not read OrcaSlicer's presets."})
        return

    def worker():
        result = fresh_spools(snapshot, force=True)
        state = result.get("profiles") or {}
        if not result.get("ok"):
            ok, text = False, result.get("error") or "Could not read Spoolman."
        elif state.get("error"):
            ok, text = False, "The filament presets were not rebuilt: " + state["error"]
        else:
            ok, text = True, f"Synced {state.get('count', 0)} filament presets from Spoolman."
        post({"type": "sent", "ok": ok, "text": text})

    threading.Thread(target=worker, daemon=True).start()


def target_for_host(host: str) -> str:
    """The system printer preset a printer address belongs to, from the last snapshot."""
    for printer in _ui_snap.get("printers") or []:
        if host in printer["hosts"]:
            return printer["target"]
    return ""


def profile_for_spool(spool: dict | None, target: str) -> str:
    """The preset name OrcaSlicer knows a spool's filament by on one printer, or ''."""
    filament = (spool or {}).get("filament") or {}
    name = _profiles["names"].get((filament.get("id"), target))
    return PROFILE_PREFIX + name if name else ""

# --- Sending preset edits to Spoolman ----------------------------------------------------
# OrcaSlicer won't save over a plugin's preset (Save makes a separate user copy that stops
# following Spoolman), so edits made in its filament settings are sent from the Spooler tab
# instead: each changed setting goes into the filament's orca_settings field, in the section for
# the preset's printer, then the presets are rebuilt. The reload keeps the unsaved edits, which
# now match the preset, so none are left.


# --- Which server an operation belongs to ----------------------------------------------------
# Spoolman ids are only unique inside one server. An operation (a send, a card action, a booking,
# a refresh) pins the server it started on: every request it makes goes to that address, and once
# the source or address in the settings changes, its generation is stale and it stops before the
# next request, so ids and data read from server A are never written to server B, and an old
# answer doesn't update a page that now shows B.


class NotSent(RuntimeError):
    """Raised before a request left Spooler: Spoolman has certainly not applied it."""


class OriginChanged(NotSent):
    def __init__(self):
        super().__init__("The spool source changed in Settings while this ran, so Spooler stopped "
                         "before writing anything more. Try again.")


_origin: dict = {"key": None, "gen": 0}
_origin_lock = threading.Lock()
_op = threading.local()


def _origin_key(settings: dict) -> str:
    if parse_source(settings.get("spool_source")) == "bambu":
        return BAMBU_KEY
    return clean_url(settings.get("spoolman_url"))


def current_origin() -> tuple[str, int]:
    """(source key, generation): the Spoolman address (or "bambu") in the settings now, and a
    number that changes whenever it does. A change also drops what was read from the old one."""
    key = _origin_key(get_settings())
    with _origin_lock:
        if key != _origin["key"]:
            if _origin["key"] is not None:
                log.info("The spool source changed; dropping what was read from the old one")
                _spool_cache.update(url="", time=0.0, spools=[])
                _profiles.update(names={}, gen=None)
                _auto.update(seen=None, sent=None, kept={})
            _origin.update(key=key, gen=_origin["gen"] + 1)
        return key, _origin["gen"]


def origin_live(origin: tuple | None) -> bool:
    return origin is not None and current_origin()[1] == origin[1]


class pinned_origin:
    """`with pinned_origin() as origin:` every spoolman_call in the block, on this thread, goes to
    the address the block started with and raises OriginChanged once the settings moved on.
    Nested blocks share the outer pin."""

    def __enter__(self) -> tuple[str, int]:
        self.outer = getattr(_op, "origin", None)
        if self.outer is None:
            _op.origin = current_origin()
        return _op.origin

    def __exit__(self, *exc) -> None:
        if self.outer is None:
            _op.origin = None


def spoolman_call(method: str, path: str, body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors, and
    OriginChanged inside a pinned_origin block whose server is no longer the one in Settings."""
    pinned = getattr(_op, "origin", None)
    if pinned is None:
        return _spoolman_open(clean_url(get_settings().get("spoolman_url")), path, method, body)
    if not origin_live(pinned):
        raise OriginChanged()
    if pinned[0] in ("", BAMBU_KEY):
        raise NotSent("Spoolman is not the spool source.")
    return _spoolman_open(pinned[0], path, method, body)


def orca_items(text: str, key: str) -> list[str]:
    """A setting's values as config_value() writes them: numbers comma separated, text semicolon
    separated and, when it holds spaces or special characters, quoted with C escapes."""
    if key not in TEXT_KEYS:
        return [item.strip() for item in text.split(",")]
    items = []
    for quoted, plain in re.findall(r'"((?:[^"\\]|\\.)*)"|([^;]+)', text):
        unescape = {"n": "\n", "r": "\r"}
        items.append(re.sub(r"\\(.)", lambda m: unescape.get(m.group(1), m.group(1)), quoted)
                     if quoted or not plain else plain.strip())
    return items or [""]


def _same(first: list[str], second: list[str]) -> bool:
    """The same values, as text or as numbers ("99.5" and "99.5%"); one value stands for every
    nozzle variant, as in the presets."""
    if len(first) == 1:
        first = first * len(second)
    if len(second) == 1:
        second = second * len(first)
    return len(first) == len(second) and all(
        a == b or (_six_digits(a) is not None and _six_digits(a) == _six_digits(b)) for a, b in zip(first, second))


def _six_digits(text: str) -> str | None:
    """A number as OrcaSlicer keeps it, 6 significant digits ("0.03256789" is kept as 0.0325679)."""
    number = _number(text)
    return None if number is None else f"{number:.6g}"


def edited_changes() -> tuple[str, dict]:
    """(preset name, {setting: (edited text, saved text)}) for the Spooler preset open in
    OrcaSlicer's filament settings. Call it on the UI thread; raises RuntimeError saying what to do."""
    filaments = orca.host.preset_bundle().filaments
    edited = filaments.get_edited_preset()
    saved = filaments.find_preset(edited.name)
    if saved is None or not edited.name.startswith(PROFILE_PREFIX):
        raise RuntimeError("Open a Spooler preset in OrcaSlicer's filament settings and change it first.")
    name = edited.name[len(PROFILE_PREFIX):]
    changes = {key: (edited.config_value(key), saved.config_value(key)) for key in edited.config_keys()
               if edited.config_value(key) != saved.config_value(key)}
    if not changes:
        raise RuntimeError(f"{name} has no unsaved changes to send.")
    return name, changes


# Spoolman versions whose behaviour a write depends on, read from Spoolman's own source:
# from 0.26.0 a PATCH's extra map is merged key by key (before, it replaced the whole map), and
# since at least 0.18.0 PUT spool/<id>/use adds use_weight to used_weight in one SQL UPDATE,
# clamped at 0, whatever its sign.
SPOOLMAN_EXTRA_MERGE = (0, 26, 0)
SPOOLMAN_ATOMIC_USE = (0, 18, 0)
_versions: dict = {}


def spoolman_version() -> tuple | None:
    """The pinned (or configured) Spoolman's version as (major, minor, patch); None when it can't
    be read. Cached per address and source generation."""
    pinned = getattr(_op, "origin", None) or current_origin()
    if pinned in _versions:
        return _versions[pinned]
    try:
        info = spoolman_call("GET", "info")
    except OriginChanged:
        raise
    except Exception as exc:
        log.info("Could not read Spoolman's version: %s", exc)
        return None
    found = re.match(r"v?(\d+)\.(\d+)\.(\d+)", str((info or {}).get("version") or "") if isinstance(info, dict) else "")
    version = tuple(int(part) for part in found.groups()) if found else None
    _versions[pinned] = version
    return version


def spoolman_at_least(minimum: tuple) -> bool:
    version = spoolman_version()
    return version is not None and version >= minimum


_MISSING = object()


def merge_settings(base: dict, local: dict, remote: dict, target: str) -> tuple[dict, set]:
    """Three-way merge of orca_settings objects ({section: {setting: value}}): the changes from
    base (what this send read first) to local (what it wants) applied to remote (what Spoolman
    holds now), removals included. A setting Spoolman changed meanwhile to something else is
    left as Spoolman has it and returned as a conflict. target's section stays last."""
    merged = json.loads(json.dumps(remote))
    conflicts: set = set()
    for name in dict.fromkeys([*base, *local]):
        old, new, now = base.get(name, _MISSING), local.get(name, _MISSING), remote.get(name, _MISSING)
        if old == new:
            continue
        if all(isinstance(v, dict) or v is _MISSING for v in (old, new, now)):
            old, new = ({} if old is _MISSING else old), ({} if new is _MISSING else new)
            section = dict({} if now is _MISSING else now)
            for key in dict.fromkeys([*old, *new]):
                was, want = old.get(key, _MISSING), new.get(key, _MISSING)
                if was == want:
                    continue
                has = section.get(key, _MISSING)
                if has != was and has != want:
                    conflicts.add(key)
                elif want is _MISSING:
                    section.pop(key, None)
                else:
                    section[key] = want
            if section or now is not _MISSING:
                merged[name] = section
        elif now == old or now == new:
            if new is _MISSING:
                merged.pop(name, None)
            else:
                merged[name] = new
        else:
            conflicts.update(new if isinstance(new, dict) else [name])
    if target in merged:
        merged[target] = merged.pop(target)
    return merged, conflicts


def send_changes(name: str, changes: dict, snapshot: dict) -> str:
    """Write a Spooler preset's changed settings into its filament's orca_settings field, in the
    section for the preset's printer, and rebuild the presets. Returns what happened, for the user.
    Runs on a worker thread. Every request goes to the Spoolman the presets were built from."""
    with pinned_origin() as origin:
        if _profiles.get("gen") not in (None, origin[1]):
            raise OriginChanged()
        return _send_changes(name, changes, snapshot)


def _send_changes(name: str, changes: dict, snapshot: dict) -> str:
    fid, target = next((key for key, known in _profiles["names"].items() if known == name), (None, ""))
    if fid is None:
        raise RuntimeError(f"{name} is no longer a Spooler preset. Refresh, then send it again.")
    filament = spoolman_call("GET", f"filament/{int(fid)}")
    base = orca_settings_data(filament)
    data = orca_settings_data(filament)
    if data is None:  # Never overwrite what can't be read back.
        raise RuntimeError(f"The {ORCA_SETTINGS_FIELD} field of {name}'s filament isn't a JSON object; "
                           "fix it in Spoolman, then send again.")
    # What Spoolman gives this printer now; a setting that differs from what the preset was made
    # from was changed in Spoolman meanwhile, and Spoolman's value is kept.
    now = profile_preset(filament, name, "", target)
    section, native, sent, kept, other = {}, {}, [], [], []
    for key, (text, saved) in sorted(changes.items()):
        if key not in ORCA_SETTINGS_KEYS:
            other.append(key)
        elif key in now and not _same(now[key], orca_items(saved or "", key)):
            kept.append(key)
        elif key in NATIVE_KEYS and native_value(key, text, filament) is not None:
            native[NATIVE_KEYS[key]] = native_value(key, text, filament)
            sent.append(key)
        else:
            items = orca_items(text, key)
            section[key] = items[0] if len(items) == 1 else items
            sent.append(key)
    patch = dict(native)
    if native:
        # A copy in orca_settings would hide the Spoolman field from this printer's preset.
        low = target.lower()
        for name_, values in data.items():
            if isinstance(values, dict) and (name_ == "*" or name_.lower() in low):
                for key in NATIVE_KEYS:
                    if NATIVE_KEYS[key] in native:
                        values.pop(key, None)
    if section or (native and orca_settings_data(filament) != data):
        if ORCA_SETTINGS_FIELD not in {field["key"] for field in spoolman_call("GET", "field/filament")}:
            spoolman_call("POST", f"field/filament/{ORCA_SETTINGS_FIELD}",
                          {"name": "Orca settings", "field_type": "text"})
        if section:  # Last, so it beats any other section that matches the printer.
            data[target] = {**data.pop(target, {}), **section}
        # Read again just before writing and merge: a setting or field changed in Spoolman since
        # the first read is kept. This narrows the window but isn't atomic: Spoolman has no
        # precondition for a PATCH, so a change landing between this read and the PATCH can
        # still be overwritten (only orca_settings itself on a Spoolman that merges extra).
        fresh = spoolman_call("GET", f"filament/{int(fid)}")
        remote = orca_settings_data(fresh) if isinstance(fresh, dict) else None
        if remote is None:
            raise RuntimeError(f"The {ORCA_SETTINGS_FIELD} field of {name}'s filament changed in Spoolman "
                               "and isn't a JSON object now; fix it in Spoolman, then send again.")
        data, clashes = merge_settings(base, data, remote, target)
        for key in clashes:
            if key in sent:
                sent.remove(key)
                kept.append(key)
                native.pop(NATIVE_KEYS.get(key), None)
                patch.pop(NATIVE_KEYS.get(key), None)
        kept.sort()
        value = json.dumps(json.dumps(data))
        if spoolman_at_least(SPOOLMAN_EXTRA_MERGE):
            # Spoolman merges extra key by key: send only the one field this changes.
            patch["extra"] = {ORCA_SETTINGS_FIELD: value}
        else:
            # Older Spoolman replaces the whole extra map, so every field goes back, as just read.
            patch["extra"] = {**(fresh.get("extra") or {}), ORCA_SETTINGS_FIELD: value}
    if patch:
        spoolman_call("PATCH", f"filament/{int(fid)}", patch)
    # Always, so the presets also take the values Spoolman kept. OrcaSlicer's reload keeps every
    # unsaved edit, so a kept setting's edit stays unsaved for the user to send again or discard.
    _auto["kept"][name] = set(kept)
    result = load_spools_synced(snapshot) or {}
    rebuild_error = (result.get("profiles") or {}).get("error") if result.get("ok") else result.get("error")
    notes = []
    if sent:
        notes.append(f"Sent {', '.join(sent)} to Spoolman for {name}.")
    if kept:
        notes.append(f"Kept Spoolman's newer value for {', '.join(kept)}: the preset now has it, and your "
                     "change stays unsaved; send again to use yours, or discard it.")
    if other:
        notes.append(f"Not sent: {', '.join(other)}. Spoolman's {ORCA_SETTINGS_FIELD} field holds only "
                     "calibration settings; colour, vendor, material and name come from its own fields.")
    if rebuild_error:
        notes.append(f"The presets were not rebuilt: {rebuild_error}")
    return " ".join(notes)


def native_value(key: str, text: str, filament: dict) -> float | None:
    """The Spoolman field value for an OrcaSlicer setting kept in one: cost is per kg in
    OrcaSlicer and per spool in Spoolman."""
    items = orca_items(text, key)
    number = _number(items[0]) if len(set(items)) == 1 else None
    if number is None or number <= 0:
        return None
    if key != "filament_cost":
        return number
    weight = _num(filament.get("weight"))
    return round(number * weight / 1000, 6) if weight else None


# Edits made in OrcaSlicer reach Spoolman by themselves: every tick the open Spooler preset's
# unsaved calibration changes are read, and once they have stayed the same for a tick (so a value
# being typed isn't sent half done) they are sent. The same changes are never sent twice, so a
# setting Spoolman kept its own value for doesn't loop. "auto_send": false in the settings file
# turns it off; Send to Spoolman still works.
_auto: dict = {"seen": None, "sent": None, "busy": False, "kept": {}}


def auto_send(post) -> None:
    """Send settled preset edits to Spoolman. Call it on the UI thread."""
    if _auto["busy"] or source() != "spoolman" or not parse_flag(get_settings().get("auto_send"), True):
        return
    try:
        name, changes = edited_changes()
    except Exception:
        _auto["seen"] = None
        return
    # A setting Spoolman kept its own value for is only sent again by hand.
    kept = _auto["kept"].get(name, set())
    changes = {key: value for key, value in changes.items() if key in ORCA_SETTINGS_KEYS and key not in kept}
    mark = (name, tuple(sorted((key, value[0]) for key, value in changes.items())))
    if not changes or mark == _auto["sent"] or mark != _auto["seen"]:
        _auto["seen"] = mark
        return
    _auto["sent"] = mark
    log.info("Sending %s's edits to Spoolman", name)
    start_send(post, (name, changes), auto=True)


# Save on a Spooler preset makes a separate user copy (OrcaSlicer can't save over a plugin's
# preset). When that copy was made from a Spooler preset, its changed calibration settings are
# sent to Spoolman too, so the next rebuild of the Spooler preset has them. "send_saved_copies":
# false in the settings turns this off. The copy itself is left as it is.
_recent_filaments: list = []  # the filament presets picked last, newest last


def note_filament_selected(name: str) -> None:
    if name:
        _recent_filaments[:] = [n for n in _recent_filaments if n != name][-4:] + [name]


def saved_copy_changes(name: str) -> tuple[str, dict] | None:
    """(Spooler preset name, {setting: (copy's text, Spooler preset's text)}) for a user preset
    just saved from a Spooler preset, or None when it wasn't one or nothing calibrated changed.
    Call it on the UI thread."""
    if not name or name.startswith(PROFILE_PREFIX):
        return None
    filaments = orca.host.preset_bundle().filaments
    copy = filaments.find_preset(name)
    # The filament picked just before the save, not counting the copy (OrcaSlicer picks it
    # after saving): the preset that was being edited. Only a Spooler preset counts.
    before = [n for n in _recent_filaments if n != name]
    origin = before[-1] if before and before[-1].startswith(PROFILE_PREFIX) else ""
    spooler = filaments.find_preset(origin) if origin else None
    if copy is None or spooler is None:
        return None
    # A copy keeps what the Spooler preset inherits from, and the filament it was made for:
    # its vendor and colour, which Spooler sets from Spoolman. Another filament's preset
    # tweaked after picking this one doesn't pass.
    for key in ("inherits", "filament_vendor", "default_filament_colour"):
        if copy.config_value(key) != spooler.config_value(key) and not (
                key == "inherits" and copy.config_value(key) == origin):
            return None
    changes = {}
    for key in sorted(ORCA_SETTINGS_KEYS):
        mine, theirs = copy.config_value(key), spooler.config_value(key)
        if mine is not None and mine != theirs:
            changes[key] = (mine, theirs or "")
    return (origin[len(PROFILE_PREFIX):], changes) if changes else None


def send_saved_copy(name: str) -> None:
    """On PresetSaved: send a saved copy's calibration changes to Spoolman. Never raises."""
    try:
        if source() != "spoolman" or not parse_flag(get_settings().get("send_saved_copies"), True):
            return
        edits = saved_copy_changes(name)
        if edits is None:
            return
        log.info("%s was saved from %s; sending its changes to Spoolman", name, edits[0])

        def done(result: dict) -> None:
            push_notice("info" if result.get("ok") else "warning", f"Spooler: {result.get('text')}")

        start_send(done, edits)
    except Exception:
        log.exception("Could not send the saved copy %s to Spoolman", name)


def start_send(post, edits: tuple | None = None, auto: bool = False) -> None:
    """Send the unsaved changes of the Spooler preset open in OrcaSlicer to Spoolman. Call it on the
    UI thread; post() gets {"type": "sent", "ok": ..., "text": ...} when it is done."""
    try:
        if _auto["busy"]:
            raise RuntimeError("Already sending to Spoolman; try again in a moment.")
        if source() != "spoolman":
            raise RuntimeError("Sending needs Spoolman as the source.")
        snapshot = refresh_snapshot()
        if snapshot is None:
            raise RuntimeError("Could not read OrcaSlicer's presets.")
        name, changes = edits or edited_changes()
    except Exception as exc:
        log.warning("Send to Spoolman: %s", exc)
        if auto:
            _auto["sent"] = None  # so the next tick tries again
        post({"type": "sent", "ok": False, "text": str(exc)})
        return
    if not auto:
        _auto["kept"].pop(name, None)

    def worker():
        try:
            text, ok = send_changes(name, changes, snapshot), True
        except Exception as exc:
            log.exception("Sending %s to Spoolman failed", name)
            text, ok = _spoolman_error(exc), False
            if auto:
                _auto["sent"] = None
        finally:
            _auto["busy"] = False
        post({"type": "sent", "ok": ok, "text": text})

    _auto["busy"] = True

    threading.Thread(target=worker, daemon=True).start()


PRINTER_SLOTS = {"ams": 4, "ht": 1, "ext": 1}


def parse_printers(value: object) -> list[dict]:
    """Cleaned printers; a spool sits in at most one slot."""
    if not isinstance(value, list):
        return []
    seen: set[str] = set()
    printers = []
    for item in value[:8]:
        if not isinstance(item, dict) or item.get("auto"):
            continue
        units = []
        for unit in (item.get("units") if isinstance(item.get("units"), list) else [])[:8]:
            kind = unit.get("kind") if isinstance(unit, dict) else None
            if kind not in PRINTER_SLOTS or (kind == "ext" and any(u["kind"] == "ext" for u in units)):
                continue
            raw = unit.get("slots") if isinstance(unit.get("slots"), list) else []
            slots: list[str | None] = []
            for index in range(PRINTER_SLOTS[kind]):
                spool = str(raw[index])[:64] if index < len(raw) and raw[index] not in (None, "") else None
                if spool in seen:
                    spool = None
                if spool:
                    seen.add(spool)
                slots.append(spool)
            units.append({"kind": kind, "slots": slots})
        name = str(item.get("name") or "").strip()[:40] or "Printer"
        ip = str(item.get("ip") or "").strip()[:64]
        serial = re.sub(r"[^A-Za-z0-9]", "", str(item.get("serial") or ""))[:32]
        printers.append({"id": str(item.get("id") or f"p{len(printers) + 1}")[:32], "name": name, "units": units,
                         "ip": ip if re.fullmatch(r"[A-Za-z0-9.\-]+", ip) else "", "serial": serial})
    return printers


def printers_cfg() -> list[dict]:
    """Saved printers, then the Moonraker printers found in OrcaSlicer's printer presets."""
    saved = get_settings().get("printers")
    printers = parse_printers(saved.get(source())) if isinstance(saved, dict) else []
    return printers + list(_auto_printers)


def save_printers(value: object) -> None:
    settings = get_settings()
    saved = settings.get("printers") if isinstance(settings.get("printers"), dict) else {}
    saved[source()] = parse_printers(value)
    settings["printers"] = saved
    save_settings(settings)
    prune_codes()
    _local_sync()


def printer_state() -> dict:
    codes = read_codes()
    printers = [dict(p, has_code=p.get("kind") == "moonraker" or bool(codes.get(_code_key(p["id"]))))
                for p in printers_cfg() if _live["links"].get(p["id"]) != "none"]
    live = any(p["ip"] and p["has_code"] for p in printers)
    return {"printers": printers, "live_ok": live, "usage": usage_state(), "progress": progress_settings(),
            "stats": stats_settings()}


LOCAL_PORT = 8883
LIVE_IDLE = 90.0
LIVE_PING = 15.0
LIVE_DEAD = 35.0
LIVE_JUMP = 10.0
LIVE_RETRY = (2.0, 5.0, 15.0)
_live: dict = {"seen": 0.0, "printers": {}, "links": {}, "keep": False}
_local: dict = {}
_live_lock = threading.Lock()


def _mqtt_len(size: int) -> bytes:
    out = bytearray()
    while True:
        digit, size = size % 128, size // 128
        out.append(digit | (128 if size else 0))
        if not size:
            return bytes(out)


def _mqtt_str(text: str) -> bytes:
    raw = text.encode("utf-8")
    return struct.pack("!H", len(raw)) + raw


def _mqtt_packet(first: int, body: bytes) -> bytes:
    return bytes([first]) + _mqtt_len(len(body)) + body


def _mqtt_connect(user: str, password: str) -> bytes:
    body = _mqtt_str("MQTT") + b"\x04\xc2" + struct.pack("!H", 60)
    body += _mqtt_str("spooler-" + os.urandom(4).hex()) + _mqtt_str(user) + _mqtt_str(password)
    return _mqtt_packet(0x10, body)


def _mqtt_subscribe(topic: str, packet_id: int) -> bytes:
    return _mqtt_packet(0x82, struct.pack("!H", packet_id) + _mqtt_str(topic) + b"\x00")


def _mqtt_publish(topic: str, payload: str) -> bytes:
    return _mqtt_packet(0x30, _mqtt_str(topic) + payload.encode("utf-8"))


MQTT_MAX = 1 << 20     # largest MQTT packet accepted, in bytes; status reports are a few dozen KB
PACKET_SECS = 15.0     # the whole of one packet must arrive within this, however it is split


def _mqtt_exact(sock, size: int, who: str = "The printer", deadline: float | None = None,
                alive=None) -> bytes:
    """Exactly size bytes. Raises TimeoutError once the deadline (absolute, monotonic) passes,
    checked between chunks too, so a sender trickling bytes can't hold it; ConnectionError when
    alive() turns false (the link was stopped) or the peer closes."""
    data = bytearray()
    deadline = time.monotonic() + PACKET_SECS if deadline is None else deadline
    while len(data) < size:
        if time.monotonic() > deadline:
            raise TimeoutError(f"{who} sent a message too slowly")
        if alive is not None and not alive():
            raise ConnectionError("The connection was stopped")
        try:
            chunk = sock.recv(min(size - len(data), 65536))
        except socket.timeout:
            continue
        if not chunk:
            raise ConnectionError(f"{who} closed the connection")
        data += chunk
    return bytes(data)


def _mqtt_read(sock, alive=None) -> tuple[int, bytes] | None:
    """Next packet as (type byte, body), or None on timeout. The size is checked against MQTT_MAX
    before any of the body is read; a length of more than four bytes is refused."""
    try:
        first = sock.recv(1)
    except socket.timeout:
        return None
    if not first:
        raise ConnectionError("The printer closed the connection")
    deadline = time.monotonic() + PACKET_SECS
    size = 0
    for shift in (0, 7, 14, 21):
        digit = _mqtt_exact(sock, 1, deadline=deadline, alive=alive)[0]
        size += (digit & 127) << shift
        if not digit & 128:
            break
    else:
        raise ConnectionError("The printer sent a malformed packet")
    if size > MQTT_MAX:
        raise ConnectionError(f"The printer sent a {size} byte packet, more than Spooler accepts")
    return first[0], _mqtt_exact(sock, size, deadline=deadline, alive=alive) if size else b""


def _mqtt_message(packet: tuple[int, bytes]) -> tuple[str, bytes] | None:
    """(topic, payload) of a PUBLISH packet, or None when it is malformed."""
    first, body = packet
    if len(body) < 2:
        return None
    size = struct.unpack("!H", body[:2])[0]
    start = 2 + size + (2 if first & 0x06 else 0)  # QoS 1 and 2 carry a packet id after the topic
    if len(body) < start:
        return None
    return body[2:2 + size].decode("utf-8", "replace"), body[start:]


# --- Live spool updates -------------------------------------------------------------------
# Spoolman pushes every spool change over a WebSocket. A small RFC 6455 client listens on one
# daemon thread and tells the open page to refresh, so a change made in Spoolman shows within a
# second. The 60 s poll stays for when the socket can't connect (some reverse proxies drop the
# upgrade headers).

WS_GUID = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
WS_MAX = 1 << 20     # largest frame or message accepted, in bytes
WS_KEEP = 30.0       # seconds between keepalive frames; Spoolman answers each one
WS_DEAD = 75.0       # silence after which the socket is taken as dead
WS_DEBOUNCE = 1.0    # a burst of changes within this many seconds refreshes once
WS_KEY = "Live spool updates"
_ws: dict = {"url": "", "stop": None, "post": None}


def ws_url(spoolman_url: object) -> str:
    """ws(s)://host[:port][/prefix]/api/v1/spool for a Spoolman address, or '' when unusable."""
    parts = urllib.parse.urlsplit(clean_url(str(spoolman_url or "")))
    if parts.scheme not in ("http", "https") or not parts.hostname:
        return ""
    scheme = "wss" if parts.scheme == "https" else "ws"
    return urllib.parse.urlunsplit((scheme, parts.netloc, parts.path.rstrip("/") + "/api/v1/spool", "", ""))


def _ws_frame(opcode: int, payload: bytes) -> bytes:
    """One final client frame, masked as the protocol requires."""
    size = len(payload)
    if size < 126:
        head = bytes([0x80 | opcode, 0x80 | size])
    elif size < 65536:
        head = bytes([0x80 | opcode, 0xFE]) + struct.pack("!H", size)
    else:
        head = bytes([0x80 | opcode, 0xFF]) + struct.pack("!Q", size)
    mask = os.urandom(4)
    return head + mask + bytes(b ^ mask[i % 4] for i, b in enumerate(payload))


def _ws_read(sock) -> tuple[bool, int, bytes] | None:
    """Next frame as (final, opcode, payload), or None on timeout."""
    try:
        first = sock.recv(1)
    except socket.timeout:
        return None
    if not first:
        raise ConnectionError("Spoolman closed the connection")
    second = _mqtt_exact(sock, 1, "Spoolman")[0]
    size = second & 127
    if size == 126:
        size = struct.unpack("!H", _mqtt_exact(sock, 2, "Spoolman"))[0]
    elif size == 127:
        size = struct.unpack("!Q", _mqtt_exact(sock, 8, "Spoolman"))[0]
    if size > WS_MAX:
        raise ConnectionError(f"Spoolman sent a {size} byte frame")
    mask = _mqtt_exact(sock, 4, "Spoolman") if second & 128 else b""
    data = _mqtt_exact(sock, size, "Spoolman") if size else b""
    if mask:
        data = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
    return bool(first[0] & 0x80), first[0] & 15, data


def _ws_handshake(sock, url: str) -> None:
    """Ask for the upgrade and check Spoolman's Sec-WebSocket-Accept; raises ConnectionError."""
    parts = urllib.parse.urlsplit(url)
    key = base64.b64encode(os.urandom(16)).decode("ascii")
    sock.sendall((f"GET {parts.path or '/'} HTTP/1.1\r\nHost: {parts.netloc.rpartition('@')[2]}\r\n"
                  "Upgrade: websocket\r\nConnection: Upgrade\r\n"
                  f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n"
                  f"User-Agent: {PLUGIN_NAME}/{PLUGIN_VERSION}\r\n\r\n").encode("ascii"))
    head = b""
    while not head.endswith(b"\r\n\r\n"):  # byte by byte, so no frame is read with the headers
        head += _mqtt_exact(sock, 1, "Spoolman")
        if len(head) > 16384:
            raise ConnectionError("Spoolman's upgrade answer is too long")
    lines = head.decode("latin-1").split("\r\n")
    if lines[0].split(" ")[1:2] != ["101"]:
        raise ConnectionError(f"Spoolman refused the WebSocket ({lines[0].strip()})")
    headers = {k.strip().lower(): v.strip() for k, _, v in (line.partition(":") for line in lines[1:]) if k}
    want = base64.b64encode(hashlib.sha1(key.encode("ascii") + WS_GUID).digest()).decode("ascii")
    if headers.get("sec-websocket-accept") != want:
        raise ConnectionError("Spoolman's WebSocket answer has the wrong key")


def _ws_change(text: bytes) -> bool:
    """True for a spool added, updated or deleted event."""
    try:
        doc = json.loads(text.decode("utf-8"))
    except ValueError:
        return False
    return (isinstance(doc, dict) and doc.get("resource") == "spool"
            and doc.get("type") in ("added", "updated", "deleted"))


def _ws_notify() -> None:
    post = _ws["post"]
    if post is None:
        return
    try:
        post({"type": "spool_changed"})
    except Exception as exc:  # the window was closed meanwhile
        log.debug("Could not tell the page about a spool change: %s", exc)


def _ws_listen(sock, stop: threading.Event) -> None:
    """Read frames until stop, a close frame or silence. Expects a 1 s socket timeout."""
    heard = sent = time.monotonic()
    due = 0.0
    parts: list[bytes] = []
    while not stop.is_set():
        now = time.monotonic()
        if due and now >= due:
            due = 0.0
            _ws_notify()
        if now - heard > WS_DEAD:
            raise ConnectionError("Spoolman stopped answering")
        if now - sent >= WS_KEEP:
            sock.sendall(_ws_frame(1, b"ping"))
            sent = now
        frame = _ws_read(sock)
        if frame is None:
            continue
        heard = time.monotonic()
        final, opcode, data = frame
        if opcode == 9:
            sock.sendall(_ws_frame(10, data))
        elif opcode == 8:
            sock.sendall(_ws_frame(8, data[:2]))
            return
        elif opcode in (0, 1, 2):
            parts = [data] if opcode else parts + [data]
            if sum(map(len, parts)) > WS_MAX:
                raise ConnectionError("Spoolman sent a message too large")
            if final:
                text, parts = b"".join(parts), []
                if _ws_change(text):
                    _spool_cache["time"] = 0.0
                    due = due or time.monotonic() + WS_DEBOUNCE


def _ws_session(url: str, stop: threading.Event) -> None:
    parts = urllib.parse.urlsplit(url)
    secure = parts.scheme == "wss"
    with socket.create_connection((parts.hostname, parts.port or (443 if secure else 80)), timeout=8) as raw:
        sock = ssl.create_default_context().wrap_socket(raw, server_hostname=parts.hostname) if secure else raw
        with sock:
            _ws_handshake(sock, url)
            _report(WS_KEY, None)
            sock.settimeout(1.0)
            _ws_listen(sock, stop)


def _ws_run(url: str, stop: threading.Event) -> None:
    """Keep the socket open until stop, reconnecting with backoff; each failure is logged once."""
    fails = 0
    while not stop.is_set():
        start = time.monotonic()
        try:
            _ws_session(url, stop)
        except Exception as exc:
            _report(WS_KEY, str(exc) or type(exc).__name__)
        fails = 0 if time.monotonic() - start > WS_DEAD else fails + 1
        stop.wait(LIVE_RETRY[min(fails, len(LIVE_RETRY) - 1)])


def ws_sync(post) -> None:
    """Match the live-updates socket to the settings; post tells the open page about changes.
    None stops it (the window closed). Called on the UI thread with every refresh."""
    _ws["post"] = post
    url = ws_url(get_settings().get("spoolman_url")) if post is not None and source() == "spoolman" else ""
    if url == _ws["url"]:
        return
    if _ws["stop"] is not None:
        _ws["stop"].set()
    _ws.update(url=url, stop=None)
    if url:
        stop = threading.Event()
        _ws["stop"] = stop
        threading.Thread(target=_ws_run, args=(url, stop), daemon=True).start()


def _int(value: object, default: int = -1) -> int:
    try:
        return int(str(value))
    except ValueError:
        return default


def live_apply(dev_id: str, name: str, doc: object, link: str = "", full: bool = False) -> None:
    """Merge a printer report into the live state. A Bambu report is a delta: units, slots and the
    external spool it doesn't mention stay. full (Moonraker and Anycubic, which report everything
    each time) replaces them, so a unit or lane that is gone, or a switch between the external
    spool and an MMU, shows at once."""
    report = doc.get("print") if isinstance(doc, dict) else None
    if not isinstance(report, dict):
        return
    with _live_lock:
        state = _live["printers"].setdefault(dev_id, {"name": name, "units": {}, "ext": {}, "time": 0.0, "link": link})
        state["time"] = time.time()
        if full:
            state["units"], state["ext"] = {}, {}
        ams = report.get("ams")
        for unit in (ams.get("ams") if isinstance(ams, dict) else None) or []:
            if not isinstance(unit, dict) or _int(unit.get("id")) < 0:
                continue
            slots = state["units"].setdefault(_int(unit["id"]), {})
            for tray in unit.get("tray") or []:
                if not isinstance(tray, dict) or _int(tray.get("id")) < 0:
                    continue
                if set(tray) <= {"id"}:
                    slots.pop(_int(tray["id"]), None)
                else:
                    slots.setdefault(_int(tray["id"]), {}).update(tray)
        ext = report.get("vt_tray")
        if isinstance(ext, dict):
            if set(ext) <= {"id"}:
                state["ext"].clear()
            else:
                state["ext"].update(ext)
        job = {k: report[k] for k in ("gcode_state", "mc_percent", "subtask_name", "gcode_file") + JOB_KEYS
               if k in report}
        prog = state.setdefault("prog", {})
        was = str(prog.get("gcode_state") or "").upper()
        prog.update({k: report[k] for k in PROG_KEYS if k in report})
        if isinstance(ams, dict) and "tray_now" in ams:
            prog["tray_now"] = ams["tray_now"]
        dev = report.get("device")
        ex = dev.get("extruder") if isinstance(dev, dict) else None
        if isinstance(ex, dict):
            if "state" in ex:
                prog["ex_now"] = (_int(ex["state"], 0) >> 4) & 0xF
            for e in ex.get("info") or []:
                if isinstance(e, dict) and "snow" in e:
                    prog.setdefault("snow", {})[_int(e.get("id"), 0)] = _int(e["snow"])
        key = tray_key(prog)
        if key != prog.get("key"):
            prog["key"] = key
            log.info("Active tray: %s (tray_now %s, extruder %s, snow %s)", key, prog.get("tray_now"),
                     prog.get("ex_now"), prog.get("snow"))
        events = _note_tray(dev_id, state)
        if "gcode_state" in report:
            gs = str(report["gcode_state"]).upper()
            if gs in ("FINISH", "FAILED"):
                if was in LIVE_STATES:
                    prog["end"] = time.time()
            else:
                prog.pop("end", None)
        if job:
            state.setdefault("job", {}).update(job)
            events += usage_track(dev_id, state, "gcode_state" in report)
    for event in events:
        usage_event(*event)


def _live_tray(slot: int, tray: dict) -> dict:
    kind = str(tray.get("tray_type") or "").strip()
    colour = _hex6(tray.get("tray_color"))
    remain = tray.get("remain")
    uid = str(tray.get("tray_uuid") or tray.get("tag_uid") or "")
    return {
        "slot": slot,
        "empty": not kind and not colour,
        "type": kind,
        "name": str(tray.get("tray_sub_brands") or kind).strip(),
        "colour": colour,
        "remain": remain if isinstance(remain, (int, float)) and 0 <= remain <= 100 else None,
        "rfid": bool(uid.strip("0")),
        "spool": tray.get("spool_id"),
        "profile": tray.get("profile") or "",
        "linked": tray.get("linked") or "",
    }


PROG_KEYS = ("gcode_state", "mc_percent", "mc_remaining_time", "layer_num", "total_layer_num",
             "subtask_name", "gcode_file", "stg_cur", "gcode_start_time")
STAGES = {
    1: "Auto Bed Levelling", 2: "Heating Bed", 3: "Sweeping XY Mech Mode", 4: "Changing Filament",
    5: "Paused", 6: "Paused: Filament Runout", 7: "Heating Nozzle", 8: "Calibrating Extrusion",
    9: "Scanning Bed Surface", 10: "Inspecting First Layer", 11: "Identifying Build Plate",
    12: "Calibrating Micro Lidar", 13: "Homing Toolhead", 14: "Cleaning Nozzle Tip",
    15: "Checking Extruder Temperature", 16: "Paused by User", 17: "Paused: Front Cover Removed",
    18: "Calibrating Micro Lidar", 19: "Calibrating Extrusion Flow", 20: "Paused: Nozzle Temperature Fault",
    21: "Paused: Bed Temperature Fault", 22: "Unloading Filament", 23: "Paused: Skipped Step",
    24: "Loading Filament", 25: "Calibrating Motor Noise", 26: "Paused: AMS Lost",
    27: "Paused: Heat Break Fan", 28: "Paused: Chamber Temperature Fault", 29: "Cooling Chamber",
    30: "Paused by G-code", 31: "Motor Noise Showoff", 32: "Paused: Nozzle Covered",
    33: "Paused: Cutter Error", 34: "Paused: First Layer Error", 35: "Paused: Nozzle Clog",
}


def tray_key(p: dict) -> int:
    """Printer tray number feeding now: AMS unit*4+slot, AMS HT unit id, 254 external, -1 none.

    H2 printers report it per extruder as snow = ams_id << 8 | slot; others only have tray_now.
    """
    snow = p.get("snow") or {}
    if snow:
        n = snow.get(p.get("ex_now", 0), snow[min(snow)] if len(snow) == 1 else -1)
        unit, slot = n >> 8, n & 0xFF
        if n < 0 or unit == 255:
            return -1
        return 254 if unit == 254 else unit if unit >= 128 else unit * 4 + slot
    t = _int(p.get("tray_now"))
    return t if 0 <= t <= 254 else -1


def _live_prog(state: dict) -> dict | None:
    p = state.get("prog") or {}
    gs = str(p.get("gcode_state") or "").upper()
    if not gs:
        return None
    def num(key: str) -> int | None:
        value = _int(p.get(key))
        return value if value >= 0 else None

    tray = None
    t = tray_key(p)
    if 0 <= t < 128:
        tray = {"unit": t // 4, "slot": t % 4}
    elif 128 <= t < 254:
        tray = {"unit": t, "slot": 0}
    elif t == 254:
        tray = {"unit": "ext", "slot": 0}
    name = str(p.get("subtask_name") or "").strip() or Path(str(p.get("gcode_file") or "")).name
    start, end = num("gcode_start_time"), p.get("end")
    return {"state": gs, "pct": num("mc_percent"), "left": num("mc_remaining_time"), "layer": num("layer_num"),
            "layers": num("total_layer_num"), "name": name[:80], "stage": STAGES.get(_int(p.get("stg_cur"))),
            "tray": tray, "took": round((end - start) / 60) if end and start and end > start else None,
            "end": end}


def live_snapshot() -> dict:
    with _live_lock:
        printers = []
        for dev_id, state in _live["printers"].items():
            units = []
            for unit_id in sorted(state["units"]):
                slots = state["units"][unit_id]
                size = 1 if unit_id >= 128 else 4
                units.append({"id": unit_id, "kind": "ht" if unit_id >= 128 else "ams",
                              "trays": [_live_tray(i, slots.get(i, {})) for i in range(size)]})
            ext = _live_tray(0, state["ext"]) if state["ext"] else None
            printers.append({"id": dev_id, "link": state.get("link", ""), "name": state["name"], "age": round(time.time() - state["time"]),
                             "units": units, "ext": ext, "job": _live_prog(state),
                             "heads": bool(state.get("heads")), "unit_label": state.get("unit_label", ""),
                             "spool_set": bool(state.get("spool_set"))})
        return {"links": dict(_live["links"]), "printers": printers}


CODES_FILE = DATA_DIR / "printer_codes.json"


def _code_key(pid: str) -> str:
    return f"{source()}:{pid}"


def read_codes() -> dict:
    try:
        data = json.loads(CODES_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except (OSError, ValueError):
        log.exception("Could not read %s", CODES_FILE)
        return {}
    return {str(k): str(v) for k, v in data.items()} if isinstance(data, dict) else {}


def write_codes(codes: dict) -> None:
    try:
        CODES_FILE.write_text(json.dumps(codes), encoding="utf-8")
        os.chmod(CODES_FILE, 0o600)
    except OSError:
        log.exception("Could not write %s", CODES_FILE)


def save_printer_code(pid: object, code: object) -> None:
    """Store a printer access code privately; never sent back to the page."""
    pid = str(pid or "")[:32]
    if pid not in {p["id"] for p in printers_cfg()}:
        return
    codes = read_codes()
    code = re.sub(r"\s", "", str(code or ""))[:32]
    if code:
        codes[_code_key(pid)] = code
    else:
        codes.pop(_code_key(pid), None)
    write_codes(codes)


def prune_codes() -> None:
    mine = {_code_key(p["id"]) for p in printers_cfg() if p.get("ip")}
    codes = read_codes()
    kept = {k: v for k, v in codes.items() if not k.startswith(f"{source()}:") or k in mine}
    if kept != codes:
        write_codes(kept)


class AuthError(Exception):
    pass


class TopicError(Exception):
    pass


PUSHALL = '{"pushing": {"sequence_id": "0", "command": "pushall"}}'


def _mqtt_run(sock, user: str, password: str, topics: list[str], push: list[tuple[str, str]], on_report, keep) -> None:
    """One MQTT session: connect, subscribe, request status, feed reports to on_report."""
    sock.settimeout(5)
    sock.sendall(_mqtt_connect(user, password))
    packet = _mqtt_read(sock)
    if not packet or packet[0] >> 4 != 2 or len(packet[1]) < 2:
        raise ConnectionError("The printer didn't accept the live connection")
    if packet[1][1] in (4, 5):
        raise AuthError("Wrong access code")
    if packet[1][1] != 0:
        raise ConnectionError("The live connection was refused")
    for number, topic in enumerate(topics, 1):
        sock.sendall(_mqtt_subscribe(topic, number))
    for topic, payload in push:
        sock.sendall(_mqtt_publish(topic, payload))
    ping = heard = mark = time.monotonic()
    wall = time.time()
    while keep():
        packet = _mqtt_read(sock, keep)
        now, clock = time.monotonic(), time.time()
        if (clock - wall) - (now - mark) > LIVE_JUMP:
            raise ConnectionError("The computer woke from sleep")
        mark, wall = now, clock
        if packet:
            heard = now
        elif now - heard > LIVE_DEAD:
            raise ConnectionError("The printer stopped answering")
        if packet and packet[0] >> 4 == 9 and 128 in packet[1][2:]:
            raise TopicError("The printer refused the status topic")
        message = _mqtt_message(packet) if packet and packet[0] >> 4 == 3 else None
        if message:
            topic, payload = message
            dev_id = topic.split("/")[1] if topic.count("/") >= 2 else ""
            try:
                doc = json.loads(payload)
            except ValueError:
                continue
            for reply_topic, payload in on_report(dev_id, doc) or []:
                sock.sendall(_mqtt_publish(reply_topic, payload))
        if time.monotonic() - ping > LIVE_PING:
            sock.sendall(b"\xc0\x00")
            ping = time.monotonic()


def _live_active() -> bool:
    return time.monotonic() - _live["seen"] < LIVE_IDLE or _live["keep"]


def _cert_serial(sock) -> str:
    """Serial from the printer certificate's subject CN."""
    found = ""
    for part in (sock.getpeercert(binary_form=True) or b"").split(b"\x06\x03\x55\x04\x03")[1:]:
        if len(part) > 2 and part[1] < 128:
            val = part[2:2 + part[1]].decode("ascii", "ignore")
            if re.fullmatch(r"[A-Za-z0-9]{8,32}", val):
                found = val
    return found


def _local_session(pid: str, link: dict, stop: threading.Event) -> None:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    with socket.create_connection((link["ip"], LOCAL_PORT), timeout=8) as raw:
        with context.wrap_socket(raw, server_hostname=link["ip"]) as sock:
            serial = link["serial"]
            if not serial:
                try:
                    serial = _cert_serial(sock)
                except (OSError, ValueError):
                    serial = ""
                log.info("Printer serial %s", "read from its certificate" if serial else "not found, listening for any")
            topics = [f"device/{serial or '+'}/report"]
            push = [(f"device/{serial}/request", PUSHALL)] if serial else []
            asked: set[str] = set()

            def on_report(dev_id: str, doc: object):
                _live["links"][pid] = "live"
                live_apply(pid, link["name"], doc, link=pid)
                if not serial and dev_id and dev_id not in asked:
                    asked.add(dev_id)
                    return [(f"device/{dev_id}/request", PUSHALL)]
                return None

            _live["links"][pid] = "waiting"
            with _live_lock:
                if pid in _live["printers"]:
                    _live["printers"][pid]["fresh"] = True
            log.info("Live link to a printer on the local network connected")
            _mqtt_run(sock, "bblp", link["code"], topics, push, on_report,
                      lambda: _live_active() and not stop.is_set())


def _local_run(pid: str, link: dict, stop: threading.Event) -> None:
    fails = 0
    while _live_active() and not stop.is_set():
        _live["links"][pid] = "connecting"
        start = time.monotonic()
        try:
            _local_session(pid, link, stop)
        except AuthError:
            _live["links"][pid] = "auth"
            log.warning("A printer refused the access code")
            return
        except TopicError:
            _live["links"][pid] = "serial"
            log.warning("A printer refused the status topic")
            return
        except Exception as exc:
            fails = 0 if time.monotonic() - start > LIVE_DEAD else fails + 1
            _live["links"][pid] = "unreachable" if fails else "connecting"
            log.warning("Live link to a printer stopped: %s", exc)
            stop.wait(LIVE_RETRY[min(fails, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


def _local_sync() -> bool:
    """Match the local connections to the saved printers."""
    codes = read_codes()
    wanted = {}
    for printer in printers_cfg():
        if printer.get("kind") == "moonraker":
            wanted[printer["id"]] = {"ip": printer["ip"], "name": printer["name"], "kind": "moonraker"}
            continue
        code = codes.get(_code_key(printer["id"]))
        if printer.get("ip") and code:
            wanted[printer["id"]] = {"ip": printer["ip"], "serial": printer["serial"], "code": code,
                                     "name": printer["name"]}
    for pid in list(_local):
        entry = _local[pid]
        if wanted.get(pid) != entry["link"]:
            entry["stop"].set()
            del _local[pid]
            _live["links"].pop(pid, None)
            with _live_lock:
                _live["printers"].pop(pid, None)
    for pid, link in wanted.items():
        entry = _local.get(pid)
        if entry and (entry["thread"].is_alive() or _live["links"].get(pid) in ("auth", "none", "serial")):
            continue
        stop = threading.Event()
        run = _moon_run if link.get("kind") == "moonraker" else _local_run
        thread = threading.Thread(target=run, args=(pid, link, stop), daemon=True)
        _local[pid] = {"link": link, "stop": stop, "thread": thread}
        thread.start()
    bambu = any(link.get("kind") != "moonraker" for link in wanted.values())
    _live["keep"] = bambu and usage_mode() != "off" and source() == "spoolman"
    return bool(wanted)


def stop_workers() -> None:
    """Stop every thread Spooler started for live links and the Spoolman socket (plugin unload).
    Only Spooler's own: each loop ends at its stop event, and nothing posts to a page after."""
    _live.update(keep=False, seen=0.0)
    for pid in list(_local):
        entry = _local.pop(pid, None)
        if entry:
            entry["stop"].set()
    ws_sync(None)


def live_poll() -> dict:
    """Keep live links alive while the Printer tab is open; never blocks."""
    _live["seen"] = time.monotonic()
    _local_sync()
    return live_snapshot()


# --- Moonraker printers ------------------------------------------------------------------
# Klipper printers (Snapmaker U1, Sovol SV06 ACE, ...) found from the host address saved in
# OrcaSlicer's printer presets, so they need no setup here. Their slots are read over plain
# HTTP and fed into the same live state as a Bambu Live Link.

MOON_POLL = 5.0  # seconds
MOON_EXT = 254
_auto_printers: list = []


def moon_base(host: object) -> str:
    """http://host[:port] from a print_host value, or '' when it isn't a usable address."""
    text = str(host or "").strip()
    if not text:
        return ""
    if "://" not in text:
        text = "http://" + text
    parts = urllib.parse.urlsplit(text)
    if parts.scheme not in ("http", "https") or not re.fullmatch(r"[A-Za-z0-9.\-]+(:\d{1,5})?", parts.netloc):
        return ""
    return f"{parts.scheme}://{parts.netloc}"


def _slug(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")[:24] or "printer"


def auto_printers(snapshot: dict) -> list[dict]:
    """One Printer tab entry per host address found on your printer presets."""
    found: dict = {}
    for printer in snapshot.get("printers") or []:
        for host in printer["hosts"]:
            found.setdefault(host, {"id": "auto-" + _slug(urllib.parse.urlsplit(host).netloc),
                                    "name": printer["label"][:40], "units": [], "ip": host, "serial": "",
                                    "kind": "moonraker", "auto": True})
    return list(found.values())


def refresh_snapshot() -> dict | None:
    """Read OrcaSlicer's presets and refresh the auto-detected printers. Call it on the UI thread."""
    snapshot = profile_snapshot()
    if snapshot is not None:
        _auto_printers[:] = auto_printers(snapshot)
    return snapshot


def _moon_get(base: str, path: str) -> dict:
    with urllib.request.urlopen(base + path, timeout=TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("result") or {} if isinstance(data, dict) else {}


def _moon_post(base: str, path: str, body: dict) -> dict:
    req = urllib.request.Request(base + path, data=json.dumps(body).encode("utf-8"), method="POST",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("result") or {} if isinstance(data, dict) else {}


def _spool_remain(spool: dict) -> float | None:
    filament = spool.get("filament") or {}
    left = _grams(spool.get("remaining_weight"))
    full = _grams(spool.get("initial_weight")) or _grams(filament.get("weight"))
    return None if left is None or not full else max(0.0, min(100.0, left / full * 100))


def _spool_tray(slot: int, spool: dict, target: str, **extra) -> dict:
    filament = spool.get("filament") or {}
    colour = profile_colour(filament)
    return {"id": str(slot), "tray_type": str(filament.get("material") or ""),
            "tray_color": colour + "FF", "tray_sub_brands": str(filament.get("name") or _spool_label(spool)),
            "remain": _spool_remain(spool), "spool_id": spool.get("id"), "filament_id": filament.get("id"),
            "profile": profile_for_spool(spool, target), **extra}


def _list_at(value: object, index: int) -> object:
    return value[index] if isinstance(value, list) and index < len(value) else None


def _card_uid(info: object) -> str:
    uid = info.get("CARD_UID") if isinstance(info, dict) else None
    if isinstance(uid, list):
        uid = "".join(f"{int(b) & 255:02X}" for b in uid if isinstance(b, int))
    return "" if str(uid or "").upper() in ("", "NONE", "0") else str(uid)


def _spool_by_id(spool_id: object, spools: list[dict]) -> dict | None:
    if isinstance(spool_id, bool) or spool_id in (None, "", 0, "0"):
        return None
    return next((s for s in spools if str(s.get("id")) == str(spool_id) and not s.get("archived")), None)


def _location_key(text: object) -> str:
    return " ".join(str(text or "").split()).casefold()


def _bound_here(location: object, names: tuple, number: int) -> int:
    """How surely a location is u1control's binding of toolhead T<number> on this printer:
    2 for "<name> T<n>" with one of its names, 1 for any name ending in the word "U1"
    (u1control's printer name is "Snapmaker U1" unless renamed, e.g. "Workshop U1"; the oldest
    form is "U1 T<n>"), 0 for no binding."""
    key = _location_key(location)
    suffix = f" t{number}"
    if not key.endswith(suffix):
        return 0
    name = key[:-len(suffix)].strip()
    if name in {_location_key(n) for n in names}:
        return 2
    return 1 if re.fullmatch(r"(?:.*\s)?u1", name) else 0


def spool_at_location(spools: list[dict], printer: str | tuple, number: int) -> dict | None:
    """The spool u1control bound to toolhead T<number> on stock U1 firmware, where the binding is
    the spool's Spoolman location "<printer name> T<n>". Spooler never writes locations on its
    own; only the card's Move action does, after a second click when it unlinks a toolhead. A location naming this printer exactly beats one that only ends in "U1"; two
    spools equally sure: the last used wins. Limit: two U1s on one system preset share their
    names here, so a spool left at the other U1's location can still match."""
    names = (printer,) if isinstance(printer, str) else tuple(printer)
    scored = [(_bound_here(s.get("location"), names, number), s) for s in spools if not s.get("archived")]
    best = max((score for score, _ in scored), default=0)
    found = [s for score, s in scored if score and score == best]
    if len(found) > 1:
        found.sort(key=lambda s: str(s.get("last_used") or ""), reverse=True)
        log.warning("Spools %s all have the location of %s T%d; using %s, the last used",
                    ", ".join(str(s.get("id")) for s in found), (names or ("U1",))[0], number,
                    found[0].get("id"))
    return found[0] if found else None


def slot_tray(slot: int, spool_id: object, uid: str, vendor: str, kind: str, rgba: str, label: str,
              spools: list[dict], target: str, location: tuple | None = None, sub: str = "") -> dict:
    """A Bambu-shaped tray for one printer slot, matched to a Spoolman spool: by the spool id the
    printer reports, else (location = (printer label, toolhead number)) by the Spoolman location
    u1control binds it with, else by RFID tag, else by vendor, material and colour, with the
    printer's filament sub type breaking a tie."""
    spool, linked = _spool_by_id(spool_id, spools), ""
    if spool is None and location:
        spool = spool_at_location(spools, *location)
        linked = "u1control" if spool is not None else ""
    if spool is None and uid:
        spool = match_spool({"tag_uid": uid}, spools)
    if spool is None and kind and rgba:
        found = match_spools({"preset": "", "vendor": vendor, "material": kind, "colour": rgba[:6],
                              "sub_type": sub}, spools)
        spool = found[0] if found else None
    if spool is not None:
        tray = _spool_tray(slot, spool, target, tag_uid=uid, **({"linked": linked} if linked else {}))
        return dict(tray, tray_color=rgba) if rgba else tray
    return {"id": str(slot), "tray_type": kind, "tray_color": rgba, "tray_sub_brands": label,
            "tag_uid": uid, "remain": None, "spool_id": None, "profile": ""}


def head_tray(index: int, config: dict, detect: dict, spools: list[dict], target: str = "") -> dict:
    """A Bambu-shaped tray for one Snapmaker U1 toolhead."""
    if not _list_at(config.get("filament_exist"), index):
        return {"id": str(index)}
    kind = str(_list_at(config.get("filament_type"), index) or "").strip()
    sub = str(_list_at(config.get("filament_sub_type"), index) or "").strip()
    vendor = str(_list_at(config.get("filament_vendor"), index) or "").strip()
    rgba = str(_list_at(config.get("filament_color_rgba"), index) or "").lstrip("#").upper()
    uid = _card_uid(_list_at((detect or {}).get("info"), index))
    label = " ".join(part for part in (vendor, kind, "" if sub.upper() in ("", "NONE", "BASIC") else sub) if part)
    return slot_tray(index, _list_at(config.get("filament_spool_id"), index), uid, vendor, kind, rgba,
                     label, spools, target, location=(location_names(target), index + 1), sub=sub)


LANE_MAX = 64  # more lanes than any filament changer has; a bad number can't build a huge list


def lane_units(lanes: dict, spools: list[dict], target: str) -> list[dict]:
    """Moonraker lane_data, as AFC, Happy Hare and other MMU integrations write it, as Bambu-shaped
    units of four trays. Each entry's "lane" is its 0-based slot; an empty material is an empty lane."""
    trays: dict = {}
    for entry in lanes.values():
        index = _int(entry.get("lane")) if isinstance(entry, dict) else -1
        if not 0 <= index < LANE_MAX:
            continue
        trays[index] = {"id": str(index % 4)}
        kind = str(entry.get("material") or "").strip()
        if kind:
            colour = _hex6(entry.get("color"))
            vendor = str(entry.get("vendor_name") or "").strip()
            label = " ".join(part for part in (vendor, str(entry.get("name") or "").strip() or kind) if part)
            trays[index] = slot_tray(index % 4, entry.get("spool_id"), "", vendor, kind,
                                     colour + "FF" if colour else "", label, spools, target)
    return [{"id": str(unit), "tray": [trays.get(unit * 4 + i, {"id": str(i)}) for i in range(4)]}
            for unit in range(max(trays, default=-1) // 4 + 1)]


def moon_report(status: dict, active_spool: object, spools: list[dict], target: str = "",
                lanes: dict | None = None) -> tuple[dict, bool]:
    """(Bambu-shaped report, has toolheads) from Moonraker's answers."""
    config = status.get("print_task_config")
    if isinstance(config, dict) and isinstance(config.get("filament_exist"), list):
        detect = status.get("filament_detect") if isinstance(status.get("filament_detect"), dict) else {}
        heads = len(config["filament_exist"])
        trays = [head_tray(i, config, detect, spools, target) for i in range(heads)]
        return {"print": {"ams": {"ams": [{"id": "0", "tray": trays}]}}}, True
    if lanes:
        return {"print": {"ams": {"ams": lane_units(lanes, spools, target)}}}, False
    spool = _spool_by_id(active_spool, spools)
    ext = _spool_tray(MOON_EXT, spool, target) if spool else {"id": str(MOON_EXT)}
    return {"print": {"vt_tray": ext}}, False


def moon_lanes(base: str) -> dict:
    """The lanes an MMU integration wrote to Moonraker's lane_data namespace, or {}."""
    try:
        lanes = _moon_get(base, "/server/database/item?namespace=lane_data").get("value")
    except urllib.error.HTTPError:
        return {}  # No lane_data namespace: nothing on the printer writes it.
    # The format isn't standard across tools: an entry without a lane number can't be placed.
    return {key: entry for key, entry in (lanes.items() if isinstance(lanes, dict) else ())
            if isinstance(entry, dict) and _int(entry.get("lane")) >= 0}


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect").get("status") or {}
    active = lanes = None
    # Moonraker answers {} for an object the printer doesn't have (only the U1 has this one).
    if not status.get("print_task_config"):
        lanes = moon_lanes(base)
        if not lanes:
            try:
                active = _moon_get(base, "/server/spoolman/spool_id").get("spool_id")
            except urllib.error.HTTPError:
                active = None  # Moonraker without its Spoolman integration
    return moon_report(status, active, _spool_cache["spools"] or [], target_for_host(base), lanes)


def moon_mark(pid: str, doc: dict, heads: bool) -> None:
    """Note what a Moonraker poll found: toolheads (U1), and whether the card is the single-extruder
    one fed by Moonraker's active spool, the only kind whose spool Spooler may change. Call it
    with _live_lock held."""
    if pid in _live["printers"]:
        _live["printers"][pid]["heads"] = heads
        _live["printers"][pid]["spool_set"] = "vt_tray" in doc["print"]


def moon_set_spool(pid: object, spool_id: object) -> dict:
    """Set the spool Moonraker books a single-extruder printer's usage to, or clear it (None).
    Refused for the Snapmaker U1 (u1control binds its toolheads through Spoolman locations) and
    for AFC / Happy Hare lanes (they manage their own spools), checked here against the printer
    itself, not only hidden on the page."""
    if source() != "spoolman":
        return {"ok": False, "text": "Setting a printer's spool needs Spoolman as the spool source."}
    if spool_id is not None:
        number = spool_id if isinstance(spool_id, int) and not isinstance(spool_id, bool) else -1
        if number <= 0 or _spool_by_id(number, _spool_cache["spools"] or []) is None:
            return {"ok": False, "text": "That spool isn't in Spoolman, or it is archived."}
    entry = _local.get(str(pid))
    link = entry["link"] if entry else None
    with _live_lock:
        state = _live["printers"].get(str(pid)) or {}
        single = bool(state.get("spool_set"))
    if not link or link.get("kind") != "moonraker" or not single:
        return {"ok": False, "text": "Spooler can only set the spool on a single-extruder Klipper printer."}
    base = link["ip"]
    try:
        doc, heads = moon_poll(base)  # read again: the printer decides, not the page
        if heads or "vt_tray" not in doc["print"]:
            with _live_lock:
                moon_mark(str(pid), doc, heads)
            return {"ok": False, "text": f"{link['name']} manages its own spools; Spooler only reads them."}
        # Body per https://moonraker.readthedocs.io/en/latest/external_api/integrations/#set-active-spool
        # {"spool_id": <id>} sets the active spool; {"spool_id": null} clears it and stops tracking.
        _moon_post(base, "/server/spoolman/spool_id", {"spool_id": spool_id})
        doc, heads = moon_poll(base)
    except (urllib.error.URLError, OSError, ValueError) as exc:
        log.warning("Could not set the spool on %s: %s", link["name"], exc)
        return {"ok": False, "text": f"Could not set the spool on {link['name']}: {exc}"}
    live_apply(str(pid), link["name"], doc, link=str(pid), full=True)
    with _live_lock:
        moon_mark(str(pid), doc, heads)
    if spool_id is None:
        return {"ok": True, "text": f"{link['name']}: no active spool, Moonraker stopped booking usage."}
    return {"ok": True, "text": f"{link['name']} now books its usage to spool #{spool_id}."}


def start_moon_spool(data: object, post) -> None:
    """Run moon_set_spool off the UI thread, then post the result and the refreshed live state."""
    data = data if isinstance(data, dict) else {}

    def work():
        result = {"ok": False, "text": STALE_LIST} if data.get("spool") is not None and stale_list(data) \
            else moon_set_spool(data.get("id"), data.get("spool"))
        post({"type": "moon_spool", "id": data.get("id"), **result})
        post({"type": "live", "live": live_snapshot(), "usage": usage_state()})
    threading.Thread(target=work, daemon=True).start()


def is_moonraker(base: str) -> bool:
    """True when the host answers like Moonraker. Raises URLError when it can't be reached."""
    try:
        info = _moon_get(base, "/server/info")
    except (urllib.error.HTTPError, ValueError):
        return False
    return "klippy_state" in info or "moonraker_version" in info

# --- Anycubic printers (Kobra X, Kobra S1) -----------------------------------------------
# LAN mode: the printer hands out MQTT credentials over HTTP on port 18910 (AES-encrypted
# with half of the token it gives), then reports its multi-colour box over MQTT/TLS on 9883.
# Only the standard library is available to a plugin, so AES-128 decryption is done here.

KX_INFO_PORT = 18910
KX_MQTT_PORT = 9883
KX_TOPIC = "anycubic/anycubicCloud/v1"
KX_REQUEST_SECS = 20.0


def _xtime(a: int) -> int:
    return ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else a << 1


def _gmul(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        a, b = _xtime(a), b >> 1
    return out


def _aes_tables() -> tuple[list[int], list[int]]:
    sbox = [0] * 256
    p = q = 1
    while True:
        p = (p ^ _xtime(p)) & 0xFF
        q ^= (q << 1) & 0xFF
        q ^= (q << 2) & 0xFF
        q ^= (q << 4) & 0xFF
        q = (q ^ 0x09) & 0xFF if q & 0x80 else q

        def rotl(x: int, n: int) -> int:
            return ((x << n) | (x >> (8 - n))) & 0xFF

        sbox[p] = q ^ rotl(q, 1) ^ rotl(q, 2) ^ rotl(q, 3) ^ rotl(q, 4) ^ 0x63
        if p == 1:
            break
    sbox[0] = 0x63
    inverse = [0] * 256
    for i, v in enumerate(sbox):
        inverse[v] = i
    return sbox, inverse


_SBOX, _INV_SBOX = _aes_tables()


def _round_keys(key: bytes) -> list[list[int]]:
    words = [list(key[i:i + 4]) for i in range(0, 16, 4)]
    rcon = 1
    for i in range(4, 44):
        word = list(words[i - 1])
        if i % 4 == 0:
            word = [_SBOX[b] for b in word[1:] + word[:1]]
            word[0] ^= rcon
            rcon = _xtime(rcon)
        words.append([a ^ b for a, b in zip(word, words[i - 4])])
    return [sum(words[r * 4:r * 4 + 4], []) for r in range(11)]


def aes128_decrypt_block(keys: list[list[int]], block: bytes) -> bytes:
    s = [b ^ k for b, k in zip(block, keys[10])]
    for rnd in range(9, -1, -1):
        s = [s[r + 4 * ((c - r) % 4)] for c in range(4) for r in range(4)]  # inverse shift rows
        s = [_INV_SBOX[b] ^ k for b, k in zip(s, keys[rnd])]
        if rnd:
            mixed = []
            for c in range(4):
                a0, a1, a2, a3 = s[4 * c:4 * c + 4]
                mixed += [_gmul(a0, 14) ^ _gmul(a1, 11) ^ _gmul(a2, 13) ^ _gmul(a3, 9),
                          _gmul(a0, 9) ^ _gmul(a1, 14) ^ _gmul(a2, 11) ^ _gmul(a3, 13),
                          _gmul(a0, 13) ^ _gmul(a1, 9) ^ _gmul(a2, 14) ^ _gmul(a3, 11),
                          _gmul(a0, 11) ^ _gmul(a1, 13) ^ _gmul(a2, 9) ^ _gmul(a3, 14)]
            s = mixed
    return bytes(s)


def aes128_cbc_decrypt(key: bytes, iv: bytes, data: bytes) -> bytes:
    """AES-128-CBC with PKCS#7 padding. Raises ValueError on bad input or padding."""
    if len(key) != 16 or len(iv) != 16 or not data or len(data) % 16:
        raise ValueError("bad AES input")
    keys = _round_keys(key)
    out = bytearray()
    previous = iv
    for i in range(0, len(data), 16):
        block = data[i:i + 16]
        out += bytes(a ^ b for a, b in zip(aes128_decrypt_block(keys, block), previous))
        previous = block
    pad = out[-1]
    if not 1 <= pad <= 16 or out[-pad:] != bytes([pad]) * pad:
        raise ValueError("bad AES padding")
    return bytes(out[:-pad])


def _host(base: str) -> str:
    return urllib.parse.urlsplit(base).hostname or ""


def kx_info(base: str) -> dict:
    """The printer's LAN-mode details, or raises."""
    with urllib.request.urlopen(f"http://{_host(base)}:{KX_INFO_PORT}/info", timeout=TIMEOUT) as resp:
        info = json.loads(resp.read().decode("utf-8"))
    if not isinstance(info, dict) or len(str(info.get("token") or "")) < 32 or not info.get("ctrlInfoUrl"):
        raise ValueError("not an Anycubic LAN-mode printer")
    return info


def kx_signed_params(token: str, now_ms: int, nonce: str, did: str) -> dict:
    def md5(text: str) -> str:
        return hashlib.md5(text.encode("utf-8")).hexdigest()

    return {"ts": str(now_ms), "nonce": nonce, "sign": md5(md5(token[:16]) + str(now_ms) + nonce), "did": did}


def kx_decrypt_bundle(reply: dict, token: str) -> dict:
    """The MQTT credentials from the printer's encrypted reply."""
    data = reply.get("data") if isinstance(reply, dict) and reply.get("code") == 200 else None
    if not isinstance(data, dict) or not data.get("info") or not data.get("token"):
        raise ValueError("The printer refused the LAN credentials request")
    plain = aes128_cbc_decrypt(token[16:32].encode("utf-8"), str(data["token"]).encode("utf-8"),
                               base64.b64decode(data["info"]))
    bundle = json.loads(plain.decode("utf-8"))
    for key in ("deviceId", "username", "password", "devicecrt", "devicepk"):
        if not bundle.get(key):
            raise ValueError(f"The printer's credentials have no {key}")
    if not (bundle.get("modelId") or bundle.get("modeId")):
        raise ValueError("The printer's credentials have no model id")
    return bundle


def kx_credentials(base: str) -> dict:
    info = kx_info(base)
    alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    nonce = "".join(alphabet[b % len(alphabet)] for b in os.urandom(6))
    params = kx_signed_params(info["token"], int(time.time() * 1000), nonce, os.urandom(16).hex().upper())
    url = str(info["ctrlInfoUrl"])
    url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    with urllib.request.urlopen(urllib.request.Request(url, method="POST"), timeout=TIMEOUT) as resp:
        reply = json.loads(resp.read().decode("utf-8"))
    return kx_decrypt_bundle(reply, info["token"])


def kx_request(kind: str, action: str = "getInfo") -> str:
    return json.dumps({"type": kind, "action": action, "timestamp": int(time.time() * 1000),
                       "msgid": os.urandom(16).hex(), "data": None})


# Debug capture for booking Anycubic prints (docs/kobra-booking.md): with "kx_capture": true in
# the settings file, each MQTT message type is logged once per session, with secrets stripped.
KX_CAPTURE_CHARS = 3000
_KX_SECRET_KEY = re.compile(r"(?i)serial|token|passw|pwd|secret|key|cert|crt|sign|auth|cookie|session|"
                            r"user|email|url|host|addr|device_?id|(^|_)(sn|ip|mac|cn|did|uid|pk)$")
_KX_IP = re.compile(r"\b\d{1,3}(?:\.\d{1,3}){3}\b")
_KX_LONG_ID = re.compile(r"\b[A-Za-z0-9_-]{16,}\b")


def kx_redact(value: object) -> object:
    """A copy with anything that looks like a serial, token, address or credential replaced."""
    if isinstance(value, dict):
        return {k: "<redacted>" if _KX_SECRET_KEY.search(str(k)) else kx_redact(v) for k, v in value.items()}
    if isinstance(value, list):
        return [kx_redact(v) for v in value]
    if isinstance(value, str):
        return _KX_LONG_ID.sub("<id>", _KX_IP.sub("<ip>", value))
    return value


def kx_capture(doc: object, seen: set, topic: str = "") -> None:
    """Log one MQTT message per type (once per session): its keys and a redacted sample."""
    kind = str(doc.get("type") or "?") if isinstance(doc, dict) else "?"
    if kind.lower() in seen:
        return
    seen.add(kind.lower())
    data = doc.get("data") if isinstance(doc, dict) else None
    # The topic ends in .../<model>/<device>/<kind>/report: keep only the parts after the device.
    log.info("Kobra capture: type=%s topic=%s keys=%s data keys=%s sample=%s", kind,
             "/".join(topic.split("/")[7:]), sorted(doc) if isinstance(doc, dict) else [],
             sorted(data) if isinstance(data, dict) else type(data).__name__,
             json.dumps(kx_redact(doc))[:KX_CAPTURE_CHARS])


def _kx_colour(value: object) -> str:
    if isinstance(value, list) and len(value) >= 3 and all(isinstance(v, int) for v in value[:3]):
        return "".join(f"{max(0, min(255, v)):02X}" for v in value[:3])
    return ""


def kx_tray(slot: int, item: object, spools: list[dict], target: str) -> dict:
    """A Bambu-shaped tray for one Anycubic slot, matched to a Spoolman spool by material and colour."""
    item = item if isinstance(item, dict) else {}
    kind = str(item.get("type") or "").strip()
    colour = _kx_colour(item.get("color"))
    if not kind or item.get("status") == 0:
        return {"id": str(slot)}
    found = match_spools({"preset": "", "vendor": "", "material": kind, "colour": colour}, spools) if colour else []
    if found:
        return dict(_spool_tray(slot, found[0], target), tray_color=colour + "FF")
    percent = item.get("consumables_percent")
    return {"id": str(slot), "tray_type": kind, "tray_color": colour + "FF" if colour else "",
            "tray_sub_brands": kind, "remain": percent if isinstance(percent, (int, float)) else None,
            "spool_id": None, "profile": ""}


def kx_report(boxes: object, external: object, spools: list[dict], target: str = "") -> dict:
    """A Bambu-shaped report from multiColorBox and extfilbox replies."""
    units = []
    for number, box in enumerate(boxes if isinstance(boxes, list) else []):
        if isinstance(box, dict) and isinstance(box.get("slots"), list):
            units.append({"id": str(number), "tray": [kx_tray(i, s, spools, target)
                                                      for i, s in enumerate(box["slots"][:4])]})
    report: dict = {"ams": {"ams": units}}
    if isinstance(external, dict):
        report["vt_tray"] = dict(kx_tray(MOON_EXT, external, spools, target), id=str(MOON_EXT))
    return {"print": report}


def _kx_socket(host: str, bundle: dict, files: tuple[Path, Path]):
    """A TLS socket authenticated with the printer's client key pair."""
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE  # The printer's certificate is self-signed.
    try:
        for path, text in zip(files, (bundle["devicecrt"], bundle["devicepk"])):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text if text.endswith("\n") else text + "\n", encoding="utf-8")
            os.chmod(path, 0o600)
        context.load_cert_chain(str(files[0]), str(files[1]))
    finally:
        for path in files:
            try:
                path.unlink()
            except OSError:
                pass
    raw = socket.create_connection((host, KX_MQTT_PORT), timeout=8)
    return context.wrap_socket(raw, server_hostname=host)


def _kx_session(pid: str, link: dict, stop: threading.Event) -> None:
    """One MQTT session with an Anycubic printer, until stopped or the link drops."""
    base, host = link["ip"], _host(link["ip"])
    bundle = kx_credentials(base)
    model = str(bundle.get("modelId") or bundle.get("modeId"))
    device = str(bundle["deviceId"])
    # Not named after the key material: OrcaSlicer blocks plugin paths containing "cert".
    files = (DATA_DIR / f".kx-{_slug(pid)}-1.pem", DATA_DIR / f".kx-{_slug(pid)}-2.pem")
    state = {"boxes": None, "external": None}
    command = f"{KX_TOPIC}/web/printer/{model}/{device}"
    capture, seen = get_settings().get("kx_capture") is True, set()
    with _kx_socket(host, bundle, files) as sock:
        sock.settimeout(5)
        sock.sendall(_mqtt_connect(bundle["username"], bundle["password"]))
        packet = _mqtt_read(sock)
        if not packet or packet[0] >> 4 != 2 or len(packet[1]) < 2 or packet[1][1] != 0:
            raise ConnectionError("The printer refused the live connection")
        for number, topic in enumerate((f"{KX_TOPIC}/printer/+/{model}/{device}/#",
                                        f"{KX_TOPIC}/printer/public/{model}/{device}/#"), 1):
            sock.sendall(_mqtt_subscribe(topic, number))
        # monotonic() counts from boot, so "never" must be -inf, not 0.
        asked = ping = float("-inf")
        # Silence counts from the connection: a printer that never reports is dropped and tried
        # again (with the usual backoff) like one that stops reporting.
        heard = time.monotonic()
        _live["links"][pid] = "waiting"
        alive = lambda: _live_active() and not stop.is_set()  # noqa: E731
        while alive():
            now = time.monotonic()
            if now - asked > KX_REQUEST_SECS:
                sock.sendall(_mqtt_publish(f"{command}/multiColorBox", kx_request("multiColorBox")))
                sock.sendall(_mqtt_publish(f"{command}/extfilbox", kx_request("extfilbox")))
                if capture:
                    # A read-only status query ({"type": "info", "action": "query"}, answered with the
                    # print "project" state and progress), as sent by
                    # https://github.com/HughKantsime/runsodin backend/modules/printers/adapters/anycubic_lan.py
                    sock.sendall(_mqtt_publish(f"{command}/info", kx_request("info", "query")))
                asked = now
            if now - ping > LIVE_PING:
                sock.sendall(b"\xc0\x00")
                ping = now
            packet = _mqtt_read(sock, alive)
            if packet:
                heard = time.monotonic()
            elif time.monotonic() - heard > LIVE_DEAD:
                raise ConnectionError("The printer stopped answering")
            message = _mqtt_message(packet) if packet and packet[0] >> 4 == 3 else None
            if not message:
                continue
            try:
                doc = json.loads(message[1])
            except ValueError:
                continue
            if capture:
                kx_capture(doc, seen, message[0])
            data = doc.get("data") if isinstance(doc, dict) else None
            kind = str(doc.get("type") or "").lower() if isinstance(doc, dict) else ""
            if kind == "multicolorbox" and isinstance(data, dict) and "multi_color_box" in data:
                state["boxes"] = data["multi_color_box"]
            elif kind == "extfilbox" and isinstance(data, dict):
                state["external"] = data
            else:
                continue
            # Every slot is in each report (empty ones as {"id": n}), so nothing goes stale.
            report = kx_report(state["boxes"] or [], state["external"], _spool_cache["spools"] or [],
                               target_for_host(base))
            live_apply(pid, link["name"], report, link=pid, full=True)
            with _live_lock:
                if pid in _live["printers"]:
                    _live["printers"][pid]["unit_label"] = "ACE"
            _live["links"][pid] = "live"


def printer_kind(base: str) -> str:
    """'moonraker', 'anycubic' or 'none'. Raises URLError when nothing answers at all."""
    try:
        if is_moonraker(base):
            return "moonraker"
        moonraker_down = None
    except (urllib.error.URLError, OSError) as exc:
        moonraker_down = exc
    try:
        kx_info(base)
        return "anycubic"
    except (urllib.error.URLError, OSError) as exc:
        if moonraker_down is not None:
            raise exc
    except ValueError:
        pass
    return "none"


def _moon_run(pid: str, link: dict, stop: threading.Event) -> None:
    """Read a printer found from a preset's host address: Moonraker, or Anycubic LAN mode."""
    fails = 0
    kind = None
    while _live_active() and not stop.is_set():
        try:
            if kind is None:
                kind = printer_kind(link["ip"])
                if kind == "none":
                    _live["links"][pid] = "none"
                    log.info("%s is neither a Moonraker nor an Anycubic printer, not reading it", link["name"])
                    return
            if kind == "anycubic":
                _kx_session(pid, link, stop)
                continue
            # Every slot is reported each time (empty ones as {"id": n}), so nothing goes stale.
            doc, heads = moon_poll(link["ip"])
            if stop.is_set():
                break
            live_apply(pid, link["name"], doc, link=pid, full=True)
            with _live_lock:
                if stop.is_set():
                    # Removed while this poll ran: don't leave it behind.
                    _live["printers"].pop(pid, None)
                else:
                    moon_mark(pid, doc, heads)
            _live["links"][pid] = "live"
            fails = 0
            _report(f"Printer {link['name']}", None)
        except Exception as exc:
            fails += 1
            _live["links"][pid] = "unreachable"
            # One message per kind of failure, so an offline printer logs once, not every retry.
            reason = "not reachable" if isinstance(exc, (urllib.error.URLError, OSError)) else str(exc)
            _report(f"Printer {link['name']}", reason)
        stop.wait(MOON_POLL if not fails else LIVE_RETRY[min(fails - 1, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


USAGE_FILE = DATA_DIR / "usage.json"
USAGE_MODES = ("ask", "auto", "off")
USAGE_PRINTS = 5
_usage: dict = {"plan": None}
_usage_lock = threading.RLock()


def usage_mode() -> str:
    value = get_settings().get("book_usage")
    return value if value in USAGE_MODES else "ask"


def usage_load() -> dict:
    try:
        data = json.loads(USAGE_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        data = {}
    except (OSError, ValueError):
        log.exception("Could not read %s", USAGE_FILE)
        data = {}
    data = data if isinstance(data, dict) else {}
    if "prints" not in data and isinstance(data.get("pending"), list):
        data["prints"] = [dict(e, state="pending") for e in data["pending"] if isinstance(e, dict)][:USAGE_PRINTS]
    out = {key: data.get(key) if isinstance(data.get(key), kind) else kind()
           for key, kind in (("prints", list), ("active", dict), ("last", dict), ("done", list))}
    # A row saved as "sending" was on its way to Spoolman when Spooler stopped (or couldn't save
    # the answer): whether Spoolman applied it is unknown, so it is never sent again by itself.
    # Every reader holds _usage_lock, and booking holds it throughout, so none is mid-send here.
    for entry in out["prints"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("rows"), list):
            continue
        for row in entry["rows"]:
            if isinstance(row, dict) and row.get("state") == "sending":
                row.update(state="unknown", error=row.get("error") or UNKNOWN_TEXT)
        if any(isinstance(r, dict) and r.get("state") == "unknown" for r in entry["rows"]):
            entry["state"] = "unknown"
    return out


UNKNOWN_TEXT = "Spooler can't tell whether Spoolman applied this. Check the spool in Spoolman, then say which."


def usage_save(data: dict) -> None:
    """Write usage.json in one step (a crash leaves the old or the new file, never half of one).
    Raises OSError: a booking must not go on when its state can't be kept."""
    _write_json(USAGE_FILE, data)


def usage_state() -> dict:
    enabled = source() == "spoolman"
    with _usage_lock:
        data = usage_load()
    return {"enabled": enabled, "mode": usage_mode(), "prints": data["prints"] if enabled else []}


def usage_plan(slots: list[dict]) -> None:
    """Store the latest slice plan for booking the print that follows."""
    if source() != "spoolman":
        return
    used = [{key: slot[key] for key in ("n", "grams", "preset", "colour", "material")}
            for slot in slots if slot["grams"] > 0]
    _usage["plan"] = {"slots": used, "time": time.time()} if used else None
    _local_sync()


def _tag_ids(value: object) -> set[str]:
    out = set()
    items = value if isinstance(value, list) else [value]
    for item in items:
        if isinstance(item, dict):
            item = item.get("uid") or item.get("id")
        text = str(item or "").strip()
        if text.startswith('"'):
            try:
                text = str(json.loads(text))
            except ValueError:
                pass
        text = re.sub(r"[\s:\-\"]", "", text).upper()
        if len(text) >= 8 and re.fullmatch(r"[0-9A-F]+", text) and text.strip("0"):
            out.add(text)
    return out


def spool_tags(spool: dict) -> set[str]:
    extra = spool.get("extra")
    first = _tag_ids(extra.get("tag") if isinstance(extra, dict) else None)
    if first:
        return first
    tags = _tag_ids(spool.get("tags"))
    filament = spool.get("filament")
    for holder in (spool, filament if isinstance(filament, dict) else {}):
        extra = holder.get("extra")
        for value in (extra.values() if isinstance(extra, dict) else []):
            tags |= _tag_ids(value)
    return tags


def match_spool(tray: dict | None, spools: list[dict]) -> dict | None:
    """The one spool whose RFID tag matches the tray, else None."""
    if not tray:
        return None
    uids = _tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")])
    found = [sp for sp in spools if not sp.get("archived") and uids & spool_tags(sp)]
    return found[0] if len(found) == 1 else None


def _loaded(state: dict) -> list[dict]:
    """Trays in slicer slot order, each with its printer tray number as key."""
    trays = []
    for unit_id in sorted(state["units"], key=lambda u: (u >= 128, u)):
        slots = state["units"][unit_id]
        trays += [dict(slots.get(i, {}), key=unit_id if unit_id >= 128 else unit_id * 4 + i)
                  for i in range(1 if unit_id >= 128 else 4)]
    if state["ext"]:
        trays.append(dict(state["ext"], key=254, spare=bool(trays)))
    return trays


def _note_tray(dev_id: str, state: dict) -> list[tuple]:
    """Remember each tray that feeds the running print. Holds _live_lock."""
    run, p = state.get("run"), state.get("prog") or {}
    t = tray_key(p)
    if not run or not 0 <= t <= 254 or str(p.get("gcode_state") or "").upper() != "RUNNING":
        return []
    if _int(p.get("layer_num"), 0) < 1 or t in run.setdefault("used", []):
        return []
    run["used"].append(t)
    if t not in [tr.get("key") for tr in run["trays"]]:
        run["trays"] = _loaded(state)
    log.info("Print is using printer tray %d", t)
    return [("save", dev_id, dict(run))]


def _fits(item: dict, tray: dict) -> bool:
    if not _same_mat(item.get("material"), tray.get("tray_type")):
        return False
    gap = colour_diff(item.get("colour") or "", _hex6(tray.get("tray_color")))
    return gap is None or gap <= COLOUR_TOLERANCE


def run_tray(run: dict, item: dict, count: int) -> dict | None:
    """The tray a filament slot printed from: the trays seen feeding the print come first."""
    trays = run.get("trays") or []
    keyed = {tr["key"]: tr for tr in trays if "key" in tr}
    used = [keyed[k] for k in run.get("used") or [] if k in keyed]
    if count == 1 and len(used) == 1:
        return used[0]
    slots = [tr for tr in trays if not tr.get("spare")]
    pos = slots[item["n"] - 1] if 0 < item["n"] <= len(slots) else None
    pool = used or trays
    fit = [tr for tr in pool if _fits(item, tr)]
    if len(fit) == 1:
        return fit[0]
    if pos is not None and (not used or pos in used) and (not fit or pos in fit):
        return pos
    return None


JOB_KEYS = ("task_id", "subtask_id", "gcode_start_time")
USAGE_DONE = 40
LIVE_STATES = ("PREPARE", "RUNNING", "PAUSE")


def job_ident(job: dict) -> dict:
    out = {k: str(job.get(k) or "") for k in JOB_KEYS}
    out.update(name=str(job.get("subtask_name") or ""), file=str(job.get("gcode_file") or ""))
    return out


def same_job(a: dict | None, b: dict | None) -> bool:
    """Same print, judged by name and file plus whichever ids both sides know."""
    if not a or not b or (a.get("name"), a.get("file")) != (b.get("name"), b.get("file")):
        return False
    known = [k for k in JOB_KEYS if a.get(k) not in ("", "0") and b.get(k) not in ("", "0")]
    return all(a[k] == b[k] for k in known)


def _ended(run: dict, printer: str, result: str, pct: int) -> dict:
    return {**run, "printer": printer, "result": result, "pct": 100 if result == "finished" else pct}


def usage_track(dev_id: str, state: dict, has_state: bool) -> list[tuple]:
    """Track a printer through a print; returns events to handle outside the lock. Holds _live_lock.

    The run is saved to disk while it lasts, so a dropped link or a restart picks it up again.
    """
    # Only Bambu Live Link prints are booked here. Printers found from a preset's host address
    # ("auto-..." ids: Moonraker, Anycubic) are not: on the Snapmaker U1 the u1control plugin
    # books each toolhead's use to Spoolman, and Moonraker's own Spoolman integration books
    # other Klipper printers, so booking them here too would count the filament twice.
    if str(dev_id).startswith("auto-"):
        return []
    job = state.get("job") or {}
    gcode = job.get("gcode_state")
    if not gcode or source() != "spoolman" or not state.get("link") or usage_mode() == "off":
        return []
    events: list[tuple] = []
    if not state.get("loaded"):
        state["loaded"] = True
        state["fresh"] = True
        with _usage_lock:
            store = usage_load()
        state["run"] = store["active"].get(dev_id)
        state["last"] = store["last"].get(dev_id)
        if state["run"] and not state["run"].get("file"):
            events.append(("fetch", dev_id, state["run"]))
    fresh = has_state and state.pop("fresh", False)
    pct = max(0, min(100, _int(job.get("mc_percent"), 0)))
    ident = job_ident(job)
    run = state.get("run")
    if fresh and run and not same_job(run["job"], ident):
        # The tracked print ended while the link was down and another one has run since.
        events.append(("end", dev_id, _ended(run, state["name"], "unknown", run["pct"])))
        state["run"] = run = None
    if run is None:
        if fresh and gcode in ("FINISH", "FAILED") and state.get("last") and not same_job(state["last"], ident):
            events.append(("missed", dev_id, {"job": ident, "printer": state["name"],
                                              "result": "finished" if gcode == "FINISH" else "cancelled",
                                              "pct": pct, "link": state["link"]}))
        if gcode in ("IDLE", "FINISH", "FAILED"):
            state["idle_seen"] = True
        elif gcode in ("PREPARE", "RUNNING") and (state.get("idle_seen") or pct <= 2 or fresh):
            new = state.get("idle_seen") or pct <= 2
            plan = _usage["plan"]["slots"] if new and _usage["plan"] else None
            state["run"] = {"id": f"{dev_id}-{int(time.time())}", "plan": plan, "file": None, "job": ident,
                            "name": str(job.get("subtask_name") or job.get("gcode_file") or "Print")[:80],
                            "trays": _loaded(state), "pct": pct, "late": not new}
            state["idle_seen"] = False
            events.append(("start", dev_id, dict(state["run"])))
        if not same_job(state.get("last"), ident) and (ident["name"] or ident["file"]):
            state["last"] = ident
            events.append(("last", dev_id, ident))
        return events
    if gcode in LIVE_STATES:
        step = pct // 5 != run["pct"] // 5 or run["job"] != ident
        run["pct"] = max(run["pct"], pct)
        run["job"] = ident
        if step:
            events.append(("save", dev_id, dict(run)))
        return events
    if gcode not in ("FINISH", "FAILED", "IDLE"):
        return events
    state["run"] = None
    state["idle_seen"] = True
    state["last"] = ident if ident["name"] or ident["file"] else state.get("last")
    result = "finished" if gcode == "FINISH" else "cancelled"
    events.append(("end", dev_id, _ended(run, state["name"], result, max(run["pct"], pct))))
    return events


FTP_PORT = 990
JOB_DIRS = ("/", "/cache", "/model", "/sdcard", "/sdcard/cache", "/sdcard/model")
JOB_MAX = 1024 * 1024 * 1024
JOB_TRIES = 6
JOB_RETRY = 30.0


class _Ftps(ftplib.FTP_TLS):
    """Implicit FTPS; data connections reuse the control TLS session, which Bambu printers require."""

    def connect(self, host="", port=0, timeout=-999, source_address=None):
        self.host, self.port, self.timeout = host, port, timeout
        raw = socket.create_connection((host, port), timeout=timeout)
        self.af = raw.family
        self.sock = self.context.wrap_socket(raw, server_hostname=host)
        self.file = self.sock.makefile("r", encoding=self.encoding)
        self.welcome = self.getresp()
        return self.welcome

    def ntransfercmd(self, cmd, rest=None):
        conn, size = ftplib.FTP.ntransfercmd(self, cmd, rest)
        if self._prot_p:
            conn = self.context.wrap_socket(conn, server_hostname=self.host, session=self.sock.session)
        return conn, size

    def pull(self, cmd: str, out, limit: int) -> None:
        # No TLS unwrap after the transfer: some printers never answer it.
        self.voidcmd("TYPE I")
        got = 0
        with self.transfercmd(cmd) as conn:
            while chunk := conn.recv(65536):
                got += len(chunk)
                if got > limit:
                    raise ValueError("The job file is too large")
                out.write(chunk)
        self.voidresp()


def _ftp_open(link: dict) -> _Ftps:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    ftp = _Ftps(context=context, timeout=15)
    ftp.connect(link["ip"], FTP_PORT, 15)
    ftp.login("bblp", link["code"])
    ftp.prot_p()
    return ftp


def job_names(job: dict) -> list[str]:
    file, name = job.get("file") or "", job.get("name") or ""
    names = [file.rsplit("/", 1)[-1]] if file.lower().endswith(".3mf") else []
    names += [f"{name}.gcode.3mf", f"{name}.3mf"] if name else []
    return [n.lower() for n in names if n.strip(".")]


def _find_job(ftp: _Ftps, job: dict) -> str | None:
    wanted = job_names(job)
    if not wanted:
        return None
    for folder in JOB_DIRS:
        out = tempfile.SpooledTemporaryFile()
        try:
            ftp.pull(f"NLST {folder}", out, 4 * 1024 * 1024)
        except (ftplib.Error, OSError, ValueError):
            continue
        out.seek(0)
        found = {line.rsplit("/", 1)[-1].lower(): line.rsplit("/", 1)[-1]
                 for line in out.read().decode("utf-8", "replace").splitlines() if line.strip()}
        for name in wanted:
            if name in found:
                return folder.rstrip("/") + "/" + found[name]
        jobs = sorted(n for n in found.values() if n.lower().endswith(".3mf"))
        if jobs:
            log.info("Job files in %s: %s", folder, ", ".join(jobs[:20]))
    return None


def parse_slice(data: bytes, file: str = "") -> list[dict] | None:
    """Grams per filament slot for the printed plate, from Metadata/slice_info.config."""
    plates = []
    for plate in ET.fromstring(data).iter("plate"):
        meta = {m.get("key"): m.get("value") for m in plate.findall("metadata")}
        rows = []
        for item in plate.findall("filament"):
            try:
                grams = float(item.get("used_g") or 0)
            except ValueError:
                grams = 0.0
            n = _int(item.get("id"), 0)
            if n > 0 and grams > 0:
                rows.append({"n": n, "grams": round(grams, 2), "preset": str(item.get("tray_info_idx") or ""),
                             "colour": _hex6(item.get("color")), "material": str(item.get("type") or "")})
        if rows:
            plates.append((_int(meta.get("index"), 0), rows))
    hint = re.search(r"plate_(\d+)", file)
    if hint:
        match = [rows for index, rows in plates if index == int(hint.group(1))]
        if match:
            return match[0]
    return plates[0][1] if len(plates) == 1 else None


WASTE_SUPPORT = ("support",)
WASTE_PURGE = ("prime tower", "wipe tower", "flush", "purge")


def parse_waste(lines) -> dict[int, tuple[float, float]]:
    """Support and purge share of each filament (1-based), from the plate G-code."""
    tool, kind, flush, rel, last = 0, "model", False, False, 0.0
    sums: dict[int, list[float]] = {}
    for raw in lines:
        line = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
        if line.startswith(";"):
            low = line.lower()
            if low.startswith((";type:", "; feature:")):
                name = low.split(":", 1)[1].strip()
                kind = ("support" if any(w in name for w in WASTE_SUPPORT)
                        else "purge" if any(w in name for w in WASTE_PURGE) else "model")
            elif "flush_start" in low:
                flush = True
            elif "flush_end" in low:
                flush = False
            continue
        cmd = line.split(";", 1)[0].strip()
        if not cmd:
            continue
        head = cmd.split(None, 1)[0].upper()
        if head == "M83":
            rel = True
        elif head == "M82":
            rel = False
        elif re.fullmatch(r"T\d+", head) and int(head[1:]) < 255:
            tool = int(head[1:])
        elif head in ("G1", "G0", "G2", "G3", "G92"):
            m = re.search(r"\bE(-?\d*\.?\d+)", cmd, re.I)
            if not m:
                continue
            e = float(m.group(1))
            if head == "G92":
                last = e
                continue
            d = e if rel else e - last
            last = last if rel else e
            if d > 0:
                k = "purge" if flush else kind
                acc = sums.setdefault(tool + 1, [0.0, 0.0, 0.0])
                acc[(k == "support") + 2 * (k == "purge")] += d
    out = {}
    for n, (model, sup, pur) in sums.items():
        total = model + sup + pur
        if total > 0:
            out[n] = (round(sup / total, 4), round(pur / total, 4))
    return out


def _plate_gcode(box: zipfile.ZipFile, file: str) -> str | None:
    names = [n for n in box.namelist() if re.fullmatch(r"Metadata/plate_\d+\.gcode", n)]
    hint = re.search(r"plate_(\d+)", file)
    if hint and f"Metadata/plate_{hint.group(1)}.gcode" in names:
        return f"Metadata/plate_{hint.group(1)}.gcode"
    return names[0] if len(names) == 1 else None


def add_waste(items: list[dict], box: zipfile.ZipFile, file: str) -> None:
    name = _plate_gcode(box, file)
    if not name:
        return
    try:
        with box.open(name) as fh:
            waste = parse_waste(fh)
    except (OSError, ValueError, zipfile.BadZipFile) as exc:
        log.info("Could not read waste from the job G-code: %s", exc)
        return
    for item in items:
        if item["n"] in waste:
            item["ws"], item["wp"] = waste[item["n"]]
    log.info("Waste from %s: %s", name, {n: waste[n] for n in sorted(waste)})


def fetch_job(link: dict, job: dict) -> list[dict] | None:
    """Download the printing job's file over FTPS and read its filament use."""
    ftp = _ftp_open(link)
    try:
        path = _find_job(ftp, job)
        if not path:
            log.info("The job file wasn't found on the printer (looked for %s in %s)",
                     ", ".join(job_names(job)) or "nothing", ", ".join(JOB_DIRS))
            return None
        log.info("Found the job file at %s", path)
        with tempfile.TemporaryFile() as out:
            ftp.pull(f"RETR {path}", out, JOB_MAX)
            out.seek(0)
            with zipfile.ZipFile(out) as box:
                info = box.getinfo("Metadata/slice_info.config")
                if info.file_size > 4 * 1024 * 1024:
                    return None
                items = parse_slice(box.read(info), job.get("file") or "")
                if items:
                    add_waste(items, box, job.get("file") or "")
    finally:
        try:
            ftp.quit()
        except (ftplib.Error, OSError):
            ftp.close()
    return items


def _try_fetch(dev_id: str, job: dict) -> list[dict] | None:
    link = (_local.get(dev_id) or {}).get("link")
    if not link:
        return None
    try:
        return fetch_job(link, job)
    except (ftplib.Error, OSError, ValueError, KeyError, zipfile.BadZipFile, ET.ParseError) as exc:
        log.warning("Could not read the job file from a printer: %s", exc)
        return None


def _store(change) -> None:
    with _usage_lock:
        data = usage_load()
        change(data)
        try:
            usage_save(data)
        except OSError:
            log.exception("Could not write %s", USAGE_FILE)


def _job_fetch(dev_id: str, run_id: str) -> None:
    """Fetch the job file while the print runs, retrying through link drops."""
    for _ in range(JOB_TRIES):
        with _live_lock:
            run = (_live["printers"].get(dev_id) or {}).get("run")
            job = dict(run["job"]) if run and run["id"] == run_id else None
        if job is None:
            return
        items = _try_fetch(dev_id, job)
        if items:
            with _live_lock:
                run = (_live["printers"].get(dev_id) or {}).get("run")
                if run and run["id"] == run_id:
                    run["file"] = items
                    saved = dict(run)
                else:
                    saved = None
            if saved:
                _store(lambda d: d["active"].__setitem__(dev_id, saved))
            log.info("Read the job file: %d slots", len(items))
            return
        time.sleep(JOB_RETRY)


def _missed(dev_id: str, info: dict) -> None:
    ident = info["job"]
    run_id = f"{dev_id}-" + re.sub(r"[^A-Za-z0-9]", "", "-".join(ident.values()))[:60]
    with _usage_lock:
        if run_id in usage_load()["done"]:
            return
    items = _try_fetch(dev_id, ident)
    if not items:
        log.info("A print ended while Spooler was away and its job file couldn't be read")
        return
    with _live_lock:
        state = _live["printers"].get(dev_id)
        trays = _loaded(state) if state else []
    run = {"id": run_id, "plan": None, "file": items, "job": ident, "trays": trays, "late": True,
           "name": (ident["name"] or ident["file"] or "Print")[:80], "pct": info["pct"]}
    usage_finish(_ended(run, info["printer"], info["result"], info["pct"]), dev_id)


def _end(dev_id: str, run: dict) -> None:
    # Finish first: if Orca closes in between, the saved run is picked up and finished again.
    usage_finish(run, dev_id)

    def drop(d):
        if (d["active"].get(dev_id) or {}).get("id") == run["id"]:
            d["active"].pop(dev_id)
        if run["result"] != "unknown":
            d["last"][dev_id] = run["job"]
    _store(drop)


def usage_event(kind: str, dev_id: str, data: dict) -> None:
    if kind in ("start", "save"):
        _store(lambda d: d["active"].__setitem__(dev_id, data))
    if kind in ("start", "fetch"):
        threading.Thread(target=_job_fetch, args=(dev_id, data["id"]), daemon=True).start()
    elif kind == "last":
        _store(lambda d: d["last"].__setitem__(dev_id, data))
    elif kind == "end":
        threading.Thread(target=_end, args=(dev_id, data), daemon=True).start()
    elif kind == "missed":
        threading.Thread(target=_missed, args=(dev_id, data), daemon=True).start()


def _spool_label(spool: dict) -> str:
    filament = spool.get("filament") or {}
    vendor = (filament.get("vendor") or {}).get("name") or ""
    return " ".join(part for part in (vendor, filament.get("name") or f"Spool {spool.get('id')}") if part)


def usage_finish(run: dict, dev_id: str = "") -> None:
    """Work out each slot's spool and grams, then ask or book. Each run is booked once."""
    with _usage_lock:
        if run["id"] in usage_load()["done"]:
            return
    items = run.get("file") or (_try_fetch(dev_id, run["job"]) if dev_id and run.get("job") else None)
    src = "file" if items else "slice"
    items = items or run.get("plan")
    if not items:
        log.info("A print ended but its filament use is unknown")
        return
    url = current_origin()[0]
    spools = (plate_spools(url) if url and url != BAMBU_KEY else None) or []
    by_id = {sp.get("id"): sp for sp in spools}
    share = run["pct"] / 100 if run["result"] == "cancelled" else 1.0
    rows = []
    for item in items:
        tray = run_tray(run, item, len(items))
        spool = match_spool(tray, spools)
        grams = round(item["grams"] * share, 1)
        if grams <= 0:
            continue
        rows.append({"slot": item["n"], "grams": grams, "preset": item["preset"], "material": item["material"],
                     "colour": item["colour"], "spool": spool["id"] if spool else None,
                     "how": "rfid" if spool else "", "label": _spool_label(by_id[spool["id"]]) if spool else "",
                     "state": "open", "error": "", **{k: item[k] for k in ("ws", "wp") if k in item}})
    late = bool(run.get("late")) or run["result"] == "unknown"
    entry = {"id": run["id"], "printer": run["printer"], "name": run["name"], "result": run["result"],
             "pct": run["pct"], "time": time.time(), "rows": rows, "late": late, "src": src, "state": "pending",
             "origin": url}  # the Spoolman these spool ids belong to; it is only booked there
    with _usage_lock:
        data = usage_load()
        if run["id"] in data["done"]:
            return
        data["done"] = [run["id"]] + data["done"][:USAGE_DONE - 1]
        if rows:
            data["prints"] = ([entry] + [e for e in data["prints"] if e.get("id") != entry["id"]])[:USAGE_PRINTS]
        try:
            usage_save(data)
        except OSError:
            log.exception("Could not write %s; the print is not booked", USAGE_FILE)
            return
    if not rows:
        return
    log.info("A print ended (%s, %d%%, grams from the %s): %d slots to book", run["result"], run["pct"],
             "job file" if src == "file" else "last slice", len(rows))
    if usage_mode() == "auto" and run["result"] == "finished" and not late:
        notice = usage_book(entry["id"], None)
        if notice:
            log.warning("Booking %s: %s", entry["id"], notice)


def spoolman_use(spool_id: int, grams: float) -> None:
    spoolman_call("PUT", f"spool/{int(spool_id)}/use", {"use_weight": round(grams, 1)})
    _spool_cache["time"] = 0.0


def spoolman_unuse(spool_id: int, grams: float) -> None:
    """Add grams back in one step on Spoolman's side (used_weight + -grams, clamped at 0), so use
    booked meanwhile by anything else isn't lost. Only for SPOOLMAN_ATOMIC_USE and newer."""
    spoolman_call("PUT", f"spool/{int(spool_id)}/use", {"use_weight": -round(grams, 1)})
    _spool_cache["time"] = 0.0


def maybe_applied(exc: Exception) -> bool:
    """Whether a failed Spoolman write may still have been applied: a timeout or dropped
    connection after sending, or a server error. A refusal (4xx), a refused connection, an
    unknown host or a check before sending means it certainly wasn't."""
    if isinstance(exc, NotSent):
        return False
    if isinstance(exc, urllib.error.HTTPError):
        return exc.code >= 500
    if isinstance(exc, urllib.error.URLError):
        return not isinstance(exc.reason, (ConnectionRefusedError, socket.gaierror))
    return True


def _spoolman_error(exc: Exception) -> str:
    if isinstance(exc, urllib.error.HTTPError):
        return f"Spoolman refused it (HTTP {exc.code})"
    if isinstance(exc, urllib.error.URLError):
        return f"Could not reach Spoolman ({exc.reason})"
    return str(exc)


def u1_bound(location: object) -> bool:
    """Whether a Spoolman location is a u1control toolhead binding ("<printer name> T<n>")."""
    found = re.search(r"\st(\d+)\s*$", str(location or ""), re.I)
    if not found:
        return False
    names = tuple(n for p in _ui_snap.get("printers") or [] for n in location_names(p["target"]))
    return _bound_here(location, names, int(found.group(1))) > 0


# --- Card actions on the Spools tab --------------------------------------------------------
# One message from either UI host: {"type": "spool_action", "action": ..., "id": ...}. The page is
# untrusted input, so everything is checked here before it reaches Spoolman.
SPOOL_ACTIONS = ("weigh", "use", "archive", "unarchive", "move", "add", "open", "dried", "clear_dried")
MAX_GRAMS = 100000.0
LOCATION_MAX = 64  # Spoolman's own limit


def _action_grams(value: object) -> float | None:
    """A positive, finite gram count up to MAX_GRAMS, from a number or numeric text; else None."""
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return None
    try:
        grams = float(value)
    except ValueError:
        return None
    return grams if math.isfinite(grams) and 0 < grams <= MAX_GRAMS else None


def _pos_int(value: object) -> int | None:
    return value if isinstance(value, int) and not isinstance(value, bool) and value > 0 else None


def today() -> datetime.date:
    return datetime.date.today()


DRIED_NO_VERSION = ("Spooler couldn't read Spoolman's version, so it can't tell whether changing the dried date "
                    "would erase this spool's other extra fields. Nothing was written; check the connection and try again.")
DRIED_NO_EXTRA = ("Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them "
                  "on a change. Nothing was written.")


def _dried_extra(sid: int, value: str | None) -> dict | str:
    """The extra map to PATCH for the dried date, or why nothing may be written.

    From Spoolman 0.26.0 the map is merged key by key: only the dried key is sent (null removes it).
    Before, a PATCH replaced the whole map, so the spool's extra fields are read again and sent back
    whole, with only the dried key changed. A change made by someone else between that read and the
    PATCH can still be lost there: Spoolman's PATCH has no precondition.
    """
    version = spoolman_version()
    if version is None:
        return DRIED_NO_VERSION
    if version >= SPOOLMAN_EXTRA_MERGE:
        return {DRIED_FIELD: value}
    spool = spoolman_call("GET", f"spool/{sid}")
    extra = spool.get("extra") if isinstance(spool, dict) else None
    if not isinstance(extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in extra.items()):
        return DRIED_NO_EXTRA
    kept = {k: v for k, v in extra.items() if k != DRIED_FIELD}
    return {**kept, DRIED_FIELD: value} if value is not None else kept


def _spool_write(action: str, sid: int, data: dict) -> dict:
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    if action in ("weigh", "use"):
        grams = _action_grams(data.get("grams"))
        if grams is None:
            return no(f"Enter a weight between 0 and {MAX_GRAMS:,.0f} g.")
        if action == "use":
            spoolman_use(sid, grams)
            return {"ok": True, "text": f"Used {grams:,.1f} g of spool #{sid}."}
        spoolman_call("PUT", f"spool/{sid}/measure", {"weight": round(grams, 1)})
        return {"ok": True, "text": f"Spool #{sid} set from a scale weight of {grams:,.1f} g."}
    if action in ("archive", "unarchive"):
        spoolman_call("PATCH", f"spool/{sid}", {"archived": action == "archive"})
        return {"ok": True, "text": f"Spool #{sid} {action}d."}
    if action == "move":
        location = data.get("location")
        if not isinstance(location, str) or len(location.strip()) > LOCATION_MAX:
            return no(f"A location is text of at most {LOCATION_MAX} characters.")
        location = " ".join(location.split())
        spoolman_call("PATCH", f"spool/{sid}", {"location": location or None})
        return {"ok": True, "text": f"Spool #{sid} moved to {location}." if location else f"Spool #{sid} has no location now."}
    if action in ("dried", "clear_dried"):
        ensure_fields()
        value = json.dumps(f"{today().isoformat()}T00:00:00+00:00") if action == "dried" else None
        extra = _dried_extra(sid, value)
        if isinstance(extra, str):
            return no(extra)
        spoolman_call("PATCH", f"spool/{sid}", {"extra": extra})
        return {"ok": True, "text": f"Spool #{sid} marked as dried today." if action == "dried"
                else f"Spool #{sid} has no dried date now."}
    if action == "add":
        fid = _pos_int(data.get("filament"))
        if fid is None:
            return no("That spool has no filament to copy.")
        made = spoolman_call("POST", "spool", {"filament_id": fid}) or {}
        return {"ok": True, "text": f"Added spool #{made.get('id', '?')} of the same filament."}
    url = getattr(_op, "origin", None)[0] if getattr(_op, "origin", None) else clean_url(get_settings().get("spoolman_url"))
    if open_url(f"{url}/spool/show/{sid}"):
        return {"ok": True, "text": f"Opened spool #{sid} in Spoolman."}
    return no(f"Could not open {url}/spool/show/{sid}.")


STALE_LIST = "The spool source changed since this list was read; nothing was written. Refresh and try again."


def stale_list(data: dict) -> bool:
    """Whether a page message carries the origin of a list read from a source the settings left.
    No origin (null) means the page has no list yet, so nothing in it was picked from an old one."""
    origin = data.get("origin")
    return isinstance(origin, int) and not isinstance(origin, bool) and origin != current_origin()[1]


def spool_action(data: object) -> dict:
    """Run one card action; {"ok": bool, "text": str} (plus "locations" for that action). Never raises."""
    data = data if isinstance(data, dict) else {}
    action = data.get("action")
    if action == "show_archived":
        save_display({**display_settings(), "archived": data.get("on") is True})
        return {"ok": True, "text": ""}
    if action != "locations" and action not in SPOOL_ACTIONS:
        return {"ok": False, "text": "Unknown spool action."}
    if source() != "spoolman":
        return {"ok": False, "text": "Spool actions need Spoolman as the source."}
    sid = _pos_int(data.get("id"))
    if sid is None and action != "locations":
        return {"ok": False, "text": "No spool chosen."}
    if action != "locations" and stale_list(data):
        return {"ok": False, "text": STALE_LIST}
    try:
        with pinned_origin():
            if action == "locations":
                found = spoolman_call("GET", "location")
                return {"ok": True, "text": "",
                        "locations": [x for x in found if isinstance(x, str)] if isinstance(found, list) else []}
            return _spool_write(action, sid, data)
    except Exception as exc:
        detail = ""
        if isinstance(exc, urllib.error.HTTPError):
            try:
                detail = json.loads(exc.read().decode("utf-8")).get("message") or ""
            except Exception:
                detail = ""
        log.warning("Spool action %s on #%s failed: %s", action, sid, exc)
        return {"ok": False, "text": _spoolman_error(exc) + (f": {detail}" if isinstance(detail, str) and detail else "")}


def start_spool_action(data: object, post) -> None:
    """Run a card action off the UI thread and post {"type": "action_result", ...}. The page asks
    for a refresh when it gets it, so the list is re-read on the UI thread."""
    action = data.get("action") if isinstance(data, dict) else None

    def work():
        result = spool_action(data)
        if action != "locations":
            _spool_cache["time"] = 0.0
        post({"type": "action_result", "action": action, **result})
    threading.Thread(target=work, daemon=True).start()


ORIGIN_TEXT = ("This print was recorded for another spool source, or before Spooler noted which Spoolman "
               "it belongs to, so Spooler won't book it here. If it is still owed, book it in Spoolman by hand.")


def _book_state(entry: dict, done: str, partial: str) -> str:
    """The print's state after booking or undoing: unknown while a row's result is unknown."""
    rows = entry["rows"]
    if any(row["state"] in ("unknown", "sending") for row in rows):
        return "unknown"
    if done == "booked":
        return "booked" if all(row["state"] == "booked" for row in rows) else partial
    return "undone" if not any(row["state"] == "booked" for row in rows) else partial


def _send_row(data: dict, row: dict, op: str, request) -> bool:
    """One row's write with its intent saved first: "sending" is on disk before the request, and
    the outcome after it. A request that may have been applied leaves the row unknown, never
    retried by itself. Returns whether it was applied. Raises OSError when state can't be saved."""
    before = {key: row.get(key) for key in ("state", "error", "op")}
    row.update(state="sending", op=op, error="")
    try:
        usage_save(data)
    except OSError:
        row.update(before)
        raise
    try:
        request()
    except Exception as exc:
        if maybe_applied(exc):
            row.update(state="unknown", error=f"{UNKNOWN_TEXT} ({_spoolman_error(exc)})")
        else:
            row.update(state=before["state"], error=_spoolman_error(exc))
        log.warning("Usage %s for spool %s failed: %s", op, row.get("spool"), exc)
        usage_save(data)
        return False
    return True


def usage_book(entry_id: str, chosen: list | None) -> str:
    """Book the open rows to their spools; chosen holds manual picks. Returns a notice for the
    page, "" when there is none. Raises OSError when the booking state can't be saved."""
    wanted = {}
    for item in chosen if isinstance(chosen, list) else []:
        if isinstance(item, dict):
            wanted[_int(item.get("slot"))] = item
    with pinned_origin() as origin:
        url = origin[0]
        by_id = {sp.get("id"): sp for sp in (plate_spools(url) if url and url != BAMBU_KEY else None) or []}
        with _usage_lock:
            data = usage_load()
            entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
            if entry is None or entry.get("state") == "unknown":
                return ""
            if not url or entry.get("origin") != url:
                return ORIGIN_TEXT
            for row in entry["rows"]:
                if row["state"] in ("booked", "unknown", "sending"):
                    continue
                pick = wanted.get(row["slot"], {})
                spool = _int(pick.get("spool")) if pick.get("spool") not in (None, "") else row["spool"]
                try:
                    grams = float(pick["grams"]) if "grams" in pick else row["grams"]
                except (TypeError, ValueError):
                    grams = 0.0
                if spool in (None, -1) or not (math.isfinite(grams) and 0 < grams <= 5000):
                    continue
                row.update(spool=spool, grams=round(grams, 1))
                if not _send_row(data, row, "book", lambda: spoolman_use(spool, grams)):
                    continue
                label = _spool_label(by_id[spool]) if spool in by_id else row.get("label") or f"spool {spool}"
                row.update(state="booked", error="", label=label)
                log.info("Booked %.1f g to Spoolman spool %s", grams, spool)
                usage_save(data)
            entry["state"] = _book_state(entry, "booked", "pending")
            usage_save(data)
            return _hist_after(entry, by_id)


def _hist_after(entry: dict, by_id: dict) -> str:
    try:
        hist_note(entry, by_id)
    except OSError:
        log.exception("Could not write %s", HISTORY_FILE)
        return "Spoolman has the change, but Spooler could not update its history file."
    return ""


def usage_undo(entry_id: str) -> str:
    """Add a booked print's grams back to its spools. Returns a notice, "" when there is none."""
    with pinned_origin() as origin:
        with _usage_lock:
            entry = next((e for e in usage_load()["prints"] if e.get("id") == entry_id), None)
        if entry is None or entry.get("state") != "booked":
            return ""
        if entry.get("origin") != origin[0]:
            return ORIGIN_TEXT
        if not spoolman_at_least(SPOOLMAN_ATOMIC_USE):
            return ("Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use "
                    "booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; "
                    "adjust the spools in Spoolman by hand.")
        with _usage_lock:
            data = usage_load()
            entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
            if entry is None or entry.get("state") != "booked":
                return ""
            for row in entry["rows"]:
                if row["state"] != "booked":
                    continue
                if not _send_row(data, row, "undo", lambda: spoolman_unuse(row["spool"], row["grams"])):
                    continue
                row.update(state="undone", error="")
                log.info("Added %.1f g back to Spoolman spool %s", row["grams"], row["spool"])
                usage_save(data)
            entry["state"] = _book_state(entry, "undone", "booked")
            usage_save(data)
            return _hist_after(entry, {})


def usage_resolve(entry_id: str, slot: object, outcome: object) -> str:
    """The user checked Spoolman for a row whose result was unknown: "applied" or "not_applied"."""
    if outcome not in ("applied", "not_applied"):
        return ""
    with _usage_lock:
        data = usage_load()
        entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
        row = next((r for r in (entry or {}).get("rows") or [] if r.get("slot") == _int(slot)), None)
        if row is None or row.get("state") != "unknown":
            return ""
        undo = row.get("op") == "undo"
        applied = outcome == "applied"
        row.update(state=("undone" if applied else "booked") if undo else ("booked" if applied else "open"), error="")
        entry["state"] = _book_state(entry, "undone" if undo else "booked", "booked" if undo else "pending")
        usage_save(data)
        return _hist_after(entry, {})


def usage_action(data: dict) -> dict:
    kind = data.get("type")
    if kind == "usage_mode":
        settings = get_settings()
        settings["book_usage"] = data.get("mode") if data.get("mode") in USAGE_MODES else "ask"
        save_settings(settings)
        _local_sync()
    notice = ""
    try:
        if kind == "usage_book" and stale_list(data):
            notice = STALE_LIST
        elif kind == "usage_book":
            notice = usage_book(str(data.get("run") or ""), data.get("rows"))
        elif kind == "usage_undo":
            notice = usage_undo(str(data.get("run") or ""))
        elif kind == "usage_resolve":
            notice = usage_resolve(str(data.get("run") or ""), data.get("slot"), data.get("outcome"))
    except OSError:
        log.exception("Could not write %s", USAGE_FILE)
        notice = (f"Spooler could not save its booking state ({USAGE_FILE.name}), so it stopped. Rows it "
                  "was sending are marked for you to check in Spoolman.")
    except NotSent as exc:
        notice = str(exc)
    return {**usage_state(), "notice": notice}


HISTORY_FILE = DATA_DIR / "history.json"
CUR_SIGNS = {"GBP": "£", "EUR": "€", "USD": "$"}
PERIODS = {"30": 30, "90": 90, "year": 0, "all": -1}
_cur = {"url": "", "code": "", "time": 0.0}


def hist_load() -> list[dict]:
    try:
        data = json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return []
    except (OSError, ValueError):
        log.exception("Could not read %s", HISTORY_FILE)
        return []
    return [e for e in data if isinstance(e, dict)] if isinstance(data, list) else []


def _hex(sp: dict) -> str:
    f = sp.get("filament") or {}
    cs = [c for c in (_hex6(x) for x in str(f.get("multi_color_hexes") or "").split(",")) if c]
    return (cs[0] if len(cs) > 1 else _hex6(f.get("color_hex"))) or ""


def _cost(sp: dict, grams: float) -> float | None:
    f = sp.get("filament") or {}
    price = sp.get("price") if isinstance(sp.get("price"), (int, float)) else f.get("price")
    wt = sp.get("initial_weight") or f.get("weight")
    if not isinstance(price, (int, float)) or not isinstance(wt, (int, float)) or wt <= 0:
        return None
    return round(price / wt * grams, 4)


def hist_note(entry: dict, by_id: dict) -> None:
    """Keep the uncapped history in step with a print's booked rows. Holds _usage_lock."""
    hist = hist_load()
    old = next((e for e in hist if e.get("id") == entry["id"]), None)
    prev = {r.get("spool"): r for r in (old or {}).get("rows") or []}
    rows = []
    for row in entry["rows"]:
        if row["state"] != "booked":
            continue
        sp, p = by_id.get(row["spool"]), prev.get(row["spool"]) or {}
        if sp:
            f = sp.get("filament") or {}
            p = {"label": row.get("label") or _spool_label(sp), "material": f.get("material") or row.get("material") or "",
                 "colour": _hex(sp) or _hex6(row.get("colour")), "cost": _cost(sp, row["grams"])}
        rows.append({"spool": row["spool"], "grams": row["grams"], "label": p.get("label") or row.get("label") or "",
                     "material": p.get("material") or row.get("material") or "",
                     "colour": p.get("colour") or _hex6(row.get("colour")), "cost": p.get("cost"),
                     **{k: row[k] for k in ("ws", "wp") if isinstance(row.get(k), (int, float))}})
    hist = [e for e in hist if e.get("id") != entry["id"]]
    if rows:
        hist.append({"id": entry["id"], "time": entry.get("time") or time.time(), "name": entry.get("name") or "",
                     "printer": entry.get("printer") or "", "result": entry.get("result") or "",
                     "pct": entry.get("pct"), "rows": rows})
        hist.sort(key=lambda e: e.get("time") or 0)
    elif old is None:
        return
    _write_json(HISTORY_FILE, hist)  # one step; raises OSError for the caller to report


def spoolman_currency(url: str) -> str:
    """Spoolman's own currency setting, cached; EUR is Spoolman's default."""
    if _cur["url"] == url and time.monotonic() - _cur["time"] < CACHE_SECS * 5:
        return _cur["code"]
    code = "EUR"
    try:
        val = _spoolman_open(url, "setting/currency").get("value")
        val = json.loads(val) if isinstance(val, str) and val.startswith('"') else val
        if isinstance(val, str) and re.fullmatch(r"[A-Za-z]{3}", val.strip()):
            code = val.strip().upper()
    except Exception as exc:
        log.info("Could not read the currency from Spoolman: %s", exc)
    _cur.update(url=url, code=code, time=time.monotonic())
    return code


def stats_currency() -> str:
    cfg = stats_settings()
    url = clean_url(get_settings().get("spoolman_url"))
    if cfg["cur"] == "spoolman":
        return spoolman_currency(url) if url else "EUR"
    return cfg["cur"].upper()


def period_start(period: object, now: float) -> float:
    days = PERIODS.get(str(period), 30)
    if days > 0:
        return now - days * 86400
    if days == 0:
        return time.mktime((time.localtime(now).tm_year, 1, 1, 0, 0, 0, 0, 0, -1))
    return 0.0


def weekly_rates(hist: list[dict], now: float) -> dict:
    """Grams per week each spool used over the last 4 weeks, by spool id."""
    rate: dict = {}
    for e in hist:
        if (e.get("time") or 0) >= now - 28 * 86400:
            for r in e["rows"]:
                rate[r["spool"]] = rate.get(r["spool"], 0) + r["grams"] / 4
    return rate


def spool_detail(spool_id: object) -> dict:
    """Prints that used one spool, what they booked, the weekly rate and the weeks left."""
    try:
        sid = int(spool_id)
    except (TypeError, ValueError):
        return {"id": spool_id, "prints": [], "grams": 0.0, "cost": None, "rate": None, "weeks": None, "code": "", "sign": ""}
    url = clean_url(get_settings().get("spoolman_url"))
    code = stats_currency()
    with _usage_lock:
        hist = hist_load()
    prints = []
    for e in reversed(hist):
        for r in e["rows"]:
            if r["spool"] == sid:
                prints.append({"time": e.get("time"), "name": e.get("name") or "", "grams": r["grams"], "cost": r.get("cost")})
    costs = [p["cost"] for p in prints if isinstance(p["cost"], (int, float))]
    rate = weekly_rates(hist, time.time()).get(sid)
    left = next((sp.get("remaining_weight") for sp in (plate_spools(url) if url else None) or [] if sp.get("id") == sid), None)
    weeks = left / rate if rate and isinstance(left, (int, float)) else None
    return {"id": sid, "prints": prints, "grams": round(sum(p["grams"] for p in prints), 1),
            "cost": round(sum(costs), 2) if costs else None, "rate": round(rate, 1) if rate else None,
            "weeks": round(weeks, 1) if weeks is not None else None, "code": code, "sign": CUR_SIGNS.get(code, code + " ")}


def csv_cell(value: object) -> object:
    """Text that starts like a spreadsheet formula gets an apostrophe in front."""
    return "'" + value if isinstance(value, str) and value[:1] in ("=", "+", "-", "@", "\t", "\r") else value


def export_history(period: object) -> dict:
    """Write the period's print history to DATA_DIR/exports and open that folder."""
    now = time.time()
    start = period_start(period, now)
    with _usage_lock:
        hist = [e for e in hist_load() if (e.get("time") or 0) >= start]
    folder = DATA_DIR / "exports"
    path = folder / time.strftime("history-%Y%m%d-%H%M.csv", time.localtime(now))
    try:
        folder.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8-sig", newline="") as fh:
            out = csv.writer(fh)
            out.writerow(["Date", "Print", "Printer", "Result", "Progress %", "Spool ID", "Spool", "Material", "Colour",
                          "Grams", "Cost", "Waste Support g", "Waste Purge g"])
            for e in hist:
                when = time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(e.get("time") or 0))
                for r in e["rows"]:
                    ws, wp = r.get("ws"), r.get("wp")
                    out.writerow([csv_cell(c) for c in (
                        when, e.get("name") or "", e.get("printer") or "", e.get("result") or "",
                        "" if e.get("pct") is None else e["pct"], r["spool"], r.get("label") or "",
                        r.get("material") or "", r.get("colour") or "", r["grams"],
                        "" if r.get("cost") is None else r["cost"],
                        round(r["grams"] * ws, 2) if isinstance(ws, (int, float)) else "",
                        round(r["grams"] * wp, 2) if isinstance(wp, (int, float)) else "")])
    except OSError as exc:
        log.exception("Could not write %s", path)
        return {"ok": False, "text": f"Could not write the export: {exc}"}
    open_url(folder.as_uri())
    return {"ok": True, "text": f"Saved {path}", "path": str(path)}


def stats_data(period: object) -> dict:
    url = clean_url(get_settings().get("spoolman_url"))
    code = stats_currency()
    with _usage_lock:
        hist = hist_load()
    now = time.time()
    lt = time.localtime(now)
    sel = [e for e in hist if (e.get("time") or 0) >= period_start(period, now)]
    total = sum(r["grams"] for e in sel for r in e["rows"])
    costs = [r["cost"] for e in sel for r in e["rows"] if isinstance(r.get("cost"), (int, float))]
    mats: dict = {}
    top: dict = {}
    for e in sel:
        for r in e["rows"]:
            m = (r.get("material") or "Other").strip() or "Other"
            mats[m] = mats.get(m, 0) + r["grams"]
            t = top.setdefault(r["spool"], {"label": r["label"], "colour": r["colour"], "g": 0})
            t["g"] += r["grams"]
    week0 = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday - lt.tm_wday, 0, 0, 0, 0, 0, -1))
    weeks = []
    for i in range(7, -1, -1):
        a = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday - lt.tm_wday - 7 * i, 0, 0, 0, 0, 0, -1))
        b = time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday - lt.tm_wday - 7 * i + 7, 0, 0, 0, 0, 0, -1))
        parts: dict = {}
        for e in hist:
            if a <= (e.get("time") or 0) < b:
                for r in e["rows"]:
                    k = parts.setdefault(r["spool"], {"label": r["label"], "colour": r["colour"], "g": 0})
                    k["g"] += r["grams"]
        weeks.append({"start": a, "now": a == week0,
                      "parts": sorted(parts.values(), key=lambda x: -x["g"])})
    low = parse_low(get_settings().get("low_stock_grams"))
    rate = weekly_rates(hist, now)
    out, nlow = [], 0
    shelf = {"g": 0.0, "value": 0.0, "unpriced": 0, "mats": {}}
    for sp in (plate_spools(url) if url else None) or []:
        left = sp.get("remaining_weight")
        if sp.get("archived") or not isinstance(left, (int, float)):
            continue
        worth = _cost(sp, left)
        m = (str((sp.get("filament") or {}).get("material") or "").strip()) or "Other"
        sm = shelf["mats"].setdefault(m, {"name": m, "g": 0.0, "value": 0.0})
        shelf["g"] += left
        sm["g"] += left
        if worth is None:
            shelf["unpriced"] += 1
        else:
            shelf["value"] += worth
            sm["value"] += worth
        is_low = left < low
        nlow += is_low
        wk = left / rate[sp.get("id")] if rate.get(sp.get("id")) else None
        if is_low or (wk is not None and wk <= 8):
            f = sp.get("filament") or {}
            full = sp.get("initial_weight") or f.get("weight") or 0
            out.append({"label": _spool_label(sp), "colour": _hex(sp), "left": left, "low": is_low,
                        "weeks": round(wk, 1) if wk is not None else None,
                        "pct": max(0, min(100, left / full * 100)) if full else None})
    out.sort(key=lambda x: (not x["low"], x["weeks"] if x["weeks"] is not None else 99, x["left"]))
    ws = {"model": 0.0, "support": 0.0, "purge": 0.0, "cost": 0.0, "mcost": 0.0, "scost": 0.0, "pcost": 0.0, "prints": 0}
    worst = []
    for e in sel:
        rows = [r for r in e["rows"] if "ws" in r]
        if not rows:
            continue
        ws["prints"] += 1
        g = c = sg = pg = 0.0
        for r in rows:
            s_, p_ = r["grams"] * r["ws"], r["grams"] * r["wp"]
            ws["support"] += s_
            ws["purge"] += p_
            ws["model"] += r["grams"] - s_ - p_
            sg, pg = sg + s_, pg + p_
            g += s_ + p_
            if isinstance(r.get("cost"), (int, float)):
                ws["scost"] += r["cost"] * r["ws"]
                ws["pcost"] += r["cost"] * r["wp"]
                ws["mcost"] += r["cost"] * (1 - r["ws"] - r["wp"])
                c += r["cost"] * (r["ws"] + r["wp"])
        if g > 0:
            worst.append({"name": e["name"], "g": round(g, 1), "cost": round(c, 2), "kind": "support" if sg >= pg else "purge"})
    ws["cost"] = ws["scost"] + ws["pcost"]
    lost = [e for e in sel if e.get("result") in ("cancelled", "failed")]
    lost_costs = [r["cost"] for e in lost for r in e["rows"] if isinstance(r.get("cost"), (int, float))]
    failed = {"prints": len(lost), "g": round(sum(r["grams"] for e in lost for r in e["rows"]), 1),
              "cost": round(sum(lost_costs), 2) if lost_costs else None}
    shelf_out = {"g": round(shelf["g"], 1), "value": round(shelf["value"], 2), "unpriced": shelf["unpriced"],
                 "mats": sorted(({"name": k, "g": round(v["g"], 1), "value": round(v["value"], 2)} for k, v in shelf["mats"].items()),
                                key=lambda x: -x["g"])} if shelf["mats"] else None
    ws = {k: round(v, 2) if isinstance(v, float) else v for k, v in ws.items()}
    return {"period": str(period), "since": hist[0]["time"] if hist else None, "code": code,
            "sign": CUR_SIGNS.get(code, code + " "), "grams": round(total, 1), "prints": len(sel),
            "cost": round(sum(costs), 2) if costs else None, "low": nlow,
            "mats": sorted(({"name": k, "g": round(v, 1)} for k, v in mats.items()), key=lambda x: -x["g"]),
            "top": sorted(top.values(), key=lambda x: -x["g"])[:5], "weeks": weeks, "soon": out[:5],
            "waste": ws if ws["prints"] else None, "failed": failed, "shelf": shelf_out, "worst": sorted(worst, key=lambda x: -x["g"])[:3],
            "history": [{"time": e["time"], "name": e["name"], "printer": e["printer"], "result": e["result"],
                         "pct": e.get("pct"), "rows": e["rows"]} for e in reversed(sel)]}


def is_newer(latest: str, current: str) -> bool:
    def parts(version):
        return tuple(int(n) for n in re.findall(r"\d+", version)[:3])

    return parts(latest) > parts(current)


def get_release() -> dict:
    """Return ``{"ok": True, "version": ..., "url": ...}`` or ``{"ok": False, "error": ...}``."""
    request = urllib.request.Request(
        RELEASE_API,
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": f"Spooler/{PLUGIN_VERSION}",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            error = "No published release found yet"
        else:
            error = f"GitHub returned HTTP {exc.code}"
    except urllib.error.URLError as exc:
        error = f"Could not reach GitHub ({exc.reason})"
    except Exception as exc:
        log.exception("Update check failed")
        return {"ok": False, "error": str(exc)}
    else:
        version = str(data.get("tag_name", "")).lstrip("v")
        log.info("Latest release is %s", version)
        return {"ok": True, "version": version, "url": data.get("html_url", "")}
    log.warning("Update check failed: %s", error)
    return {"ok": False, "error": error}


def open_url(url: str) -> bool:
    log.info("Opening %s", url)
    try:
        if sys.platform == "win32":
            # What OrcaSlicer itself does (ShellExecute): inside its Python, webbrowser.open can
            # report success on Windows without opening anything.
            try:
                os.startfile(url)
                return True
            except OSError:
                log.warning("os.startfile could not open %s, trying webbrowser", url)
        if webbrowser.open(url):
            return True
        # webbrowser reports "no browser available" (common on Linux) by returning
        # False rather than raising.
        log.warning("No web browser could be launched for %s", url)
        message = f"No web browser could be launched. Open this address yourself:\n{url}"
    except Exception as exc:
        log.exception("Could not open the browser")
        message = f"Could not open the browser: {exc}"
    orca.host.ui.message(message, title=PLUGIN_NAME, icon="error")
    return False


def open_search(query: object) -> None:
    if isinstance(query, str) and query.strip():
        terms = urllib.parse.quote_plus(query.strip()[:MAX_QUERY])
        open_url(SEARCH_URL.format(query=terms))


def read_tail(path: str) -> list[str]:
    size = os.path.getsize(path)
    with open(path, "rb") as handle:
        handle.seek(max(0, size - TAIL_BYTES))
        return handle.read().decode("utf-8", "replace").splitlines()


def parse_usage(lines: list[str]) -> list[float]:
    """Grams per filament slot, from the last ``; filament used [g] = ...`` footer line."""
    for line in reversed(lines):
        if line.startswith("; filament used [g] ="):
            return [float(n) for n in re.findall(r"-?\d+(?:\.\d+)?", line.split("=", 1)[1])]
    return []


def split_list(value: object) -> list[str]:
    """Split a slicer list such as ``"a";"b"`` or ``#000;#fff`` into its items."""
    text = "" if value is None else str(value)
    if '"' in text:
        return [quoted or plain.strip() for quoted, plain in re.findall(r'"([^"]*)"|([^;]+)', text)]
    return [item.strip() for item in text.split(";")]


def plate_slots(ctx, grams: list[float]) -> list[dict]:
    """Every filament slot the slicer reports, with how much of it this plate uses."""
    names = split_list(ctx.config_value("filament_settings_id"))
    colours = split_list(ctx.config_value("filament_colour"))
    materials = split_list(ctx.config_value("filament_type"))
    vendors = split_list(ctx.config_value("filament_vendor"))
    ams = "bambu" in str(ctx.config_value("printer_model") or "").lower()

    def at(items: list[str], i: int) -> str:
        return items[i] if i < len(items) else ""

    return [
        {"n": i + 1, "grams": used, "preset": at(names, i), "colour": at(colours, i),
         "material": at(materials, i), "vendor": at(vendors, i), "ams": ams}
        for i, used in enumerate(grams)
    ]


def colour_diff(first: str, second: str) -> float | None:
    def rgb(value):
        digits = (value or "").strip().lstrip("#")[:6]
        if not re.fullmatch(r"[0-9a-fA-F]{6}", digits):
            return None
        return tuple(int(digits[i:i + 2], 16) for i in (0, 2, 4))

    a, b = rgb(first), rgb(second)
    return None if a is None or b is None else sum((x - y) ** 2 for x, y in zip(a, b)) ** 0.5


def _norm(text: object) -> str:
    return re.sub(r"[^a-z0-9+]", "", str(text or "").lower())


def _same_mat(slicer: object, spool: object) -> bool:
    """Equal, or one is a variant of the other ("PLA" and "PLA Matte" or "PLA+")."""
    first, second = _norm(slicer), _norm(spool)
    return bool(first) and bool(second) and (first.startswith(second) or second.startswith(first))


def match_spools(slot: dict, spools: list[dict]) -> list[dict]:
    """Spools that could be what is loaded in a slot: same vendor and material, close colour."""
    wants_support = "support" in slot["preset"].lower()
    vendor = _norm(slot["vendor"])
    found = []
    for spool in spools:
        filament = spool.get("filament") or {}
        if spool.get("archived") or not isinstance(spool.get("remaining_weight"), (int, float)):
            continue
        if ("support" in str(filament.get("name", "")).lower()) != wants_support:
            continue
        if vendor and vendor != "generic":
            theirs = _norm((filament.get("vendor") or {}).get("name"))
            if not theirs or (vendor not in theirs and theirs not in vendor):
                continue
        if not _same_mat(slot["material"], filament.get("material")):
            continue
        distance = colour_diff(slot["colour"], filament.get("color_hex"))
        if distance is not None and distance <= COLOUR_TOLERANCE:
            exact = _norm(slot["material"]) == _norm(filament.get("material"))
            found.append((distance, exact, spool))
    # An exact colour beats a near one, and an exact material beats a variant.
    pool = [item for item in found if item[0] <= 1] or found
    spools_left = [spool for *_, spool in [item for item in pool if item[1]] or pool]
    return sub_type_pick(spools_left, slot.get("sub_type"))


def _sub_key(text: object) -> str:
    """A filament name as the U1's sub type field holds it: u1control writes the Spoolman name
    with spaces (and ; = quotes) as "_", cut to 32 characters. "_" and spaces count as one."""
    return re.sub(r"[\s_;=\"']+", " ", str(text or "")).strip().casefold()


def sub_type_pick(spools: list[dict], sub: object) -> list[dict]:
    """The tied spools whose filament name is the printer's sub type, else all of them."""
    key = _sub_key(sub)
    if len(spools) < 2 or not key:
        return spools
    same = [s for s in spools if _sub_key(re.sub(r"[\s;=\"']+", "_",
                                                 str((s.get("filament") or {}).get("name") or "").strip())[:32]) == key]
    return same or spools


def group_slots(slots: list[dict]) -> list[dict]:
    """The groups of slots holding the same filament that this plate uses.

    The AMS moves on to another spool of the same filament when one runs out, so a group is
    one supply: its use is added together and compared with its spools' combined weight.
    """
    groups: dict[tuple, dict] = {}
    for slot in slots:
        key = (_norm(slot["preset"]), _norm(slot["vendor"]), _norm(slot["material"]),
               slot["colour"].lstrip("#").upper()[:6])
        group = groups.setdefault(key, {"slot": slot, "pool": 0, "used": []})
        group["pool"] += 1
        if slot["grams"] > 0:
            group["used"].append(slot)
    return [group for group in groups.values() if group["used"]]


def check_group(group: dict, spools: list[dict], margin: int) -> dict:
    """ok, mixed (depends which spools are loaded), barely, short, or unknown (no spool)."""
    slot, pool = group["slot"], group["pool"]
    matches = match_spools(slot, spools)
    need = sum(used["grams"] for used in group["used"])
    result = {"slot": slot, "slots": [used["n"] for used in group["used"]], "need": need,
              "margin": margin, "pool": pool, "matches": len(matches), "status": "unknown",
              "ams": bool(slot.get("ams")), "ids": [spool.get("id") for spool in matches]}
    if not matches:
        return result
    padded = need * (1 + margin / 100)
    weights = sorted((spool["remaining_weight"] for spool in matches), reverse=True)
    best, worst = sum(weights[:pool]), sum(weights[-pool:])
    if worst >= padded:
        status = "ok"
    elif best >= padded:
        status = "mixed"
    elif best >= need:
        status = "barely"
    else:
        status = "short"
    ranked = sorted(matches, key=lambda spool: spool["remaining_weight"], reverse=True)
    fullest = ranked[0]
    name = (fullest.get("filament") or {}).get("name") or ""
    total = sum(spool.get("initial_weight") or (spool.get("filament") or {}).get("weight") or 0
                for spool in ranked[:pool])
    result = {**result, "status": status, "have": best, "worst": worst, "padded": padded, "cost": _cost(fullest, need),
              "name": name, "total": total, "spool_colour": (fullest.get("filament") or {}).get("color_hex")}
    if status == "short":
        result["swap"] = swap_spool(matches, spools, padded)
    result["dry"] = dry_check(fullest)
    return result


def dry_check(spool: dict) -> dict | None:
    """Set when a moisture-sensitive spool was dried too long ago or never: {"days": age or None}."""
    limit = drying_days((spool.get("filament") or {}).get("material"))
    if limit <= 0:
        return None
    dried = dried_date(spool)
    age = (today() - dried).days if dried else None
    return {"days": age} if age is None or age > limit else None


def loaded_spool_ids() -> set[str]:
    """Spools sitting in a printer slot: the live trays and the slots saved in Settings."""
    ids = {str(p_slot) for p in printers_cfg() for u in p["units"] for p_slot in u["slots"] if p_slot}
    snap = live_snapshot()
    for printer in snap["printers"]:
        for tray in [t for u in printer["units"] for t in u["trays"]] + [printer["ext"] or {}]:
            if tray.get("spool") is not None:
                ids.add(str(tray["spool"]))
    return ids


def swap_spool(matches: list[dict], spools: list[dict], padded: float) -> dict | None:
    """An unloaded spool of the same filament that covers the plate on its own: the use-first one,
    else the one with the least left that still suffices."""
    fids = {(m.get("filament") or {}).get("id") for m in matches} - {None}
    loaded = loaded_spool_ids()
    options = [s for s in spools if (s.get("filament") or {}).get("id") in fids and not s.get("archived")
               and str(s.get("id")) not in loaded and isinstance(s.get("remaining_weight"), (int, float))
               and s["remaining_weight"] >= padded]
    first = use_first_id(spools)
    return min(options, key=lambda s: (first.get((s.get("filament") or {}).get("id")) != s.get("id"),
                                       s["remaining_weight"], s.get("id") or 0), default=None)


def fmt_grams(grams: float) -> str:
    # The epsilon makes a half such as 296.15 round up, matching the slicer's own figure.
    grams += 1e-9
    return f"{grams / 1000:.2f} kg" if grams >= 1000 else f"{grams:.1f} g"


def _join(items: list[str]) -> str:
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def slot_label(result: dict) -> str:
    slot, numbers = result["slot"], result["slots"]
    preset = slot["preset"].split("@")[0].strip()
    named = preset or " ".join(part for part in (slot["vendor"], slot["material"]) if part)
    name = result.get("name") or " ".join(part for part in (named, slot["colour"]) if part)
    which = "slot " if len(numbers) == 1 else "slots "
    return f"{which}{_join([str(n) for n in numbers])} ({name})"


def _sentence(text: str) -> str:
    return text[:1].upper() + text[1:] + "."


def _need(result: dict) -> str:
    grams = fmt_grams(result["need"])
    if len(result["slots"]) == 1:
        return f"needs {grams} of filament"
    return f"need {grams} of filament together"


def _supply(result: dict) -> str:
    count, have = min(result["pool"], result["matches"]), fmt_grams(result["have"])
    if count == 1:
        return f"the spool has {have}"
    return f"the {count} spools have {have} between them"


def _tracked(result: dict) -> str:
    if result["matches"] >= result["pool"]:
        return ""
    return f" (only {result['matches']} of {result['pool']} matching spools are in {source_name()})"


def plate_notice(results: list[dict], cost: str = "") -> tuple[str, str] | None:
    """The one notification for a slice: ``("warning" | "info", text)``."""
    label, grams = slot_label, fmt_grams
    where = " in the AMS" if any(r["ams"] for r in results) else ""
    short = [r for r in results if r["status"] == "short"]
    mixed = [r for r in results if r["status"] == "mixed"]
    barely = [r for r in results if r["status"] == "barely"]

    def short_part(r: dict) -> str:
        text = _sentence(f"{label(r)} {_need(r)} but {_supply(r)}{_tracked(r)}")
        swap = r.get("swap")
        if swap:
            where = f"{swap['location']}, " if swap.get("location") else ""
            text += f" Swap in spool #{swap['id']} ({where}{swap['remaining_weight']:.0f} g)."
        return text

    def mixed_part(r: dict, prefix: str = "") -> str:
        count = min(r["pool"], r["matches"])
        if count == 1:
            body = (f"of {r['matches']} matching spools the fullest has {grams(r['have'])} and "
                    f"the smallest has {grams(r['worst'])}, so make sure the right one is loaded")
        else:
            body = (f"the {count} fullest of {r['matches']} matching spools hold "
                    f"{grams(r['have'])} and the {count} smallest hold {grams(r['worst'])}, "
                    "so make sure the right ones are loaded")
        return _sentence(f"{prefix}{label(r)} {_need(r)}; {body}")

    def barely_part(r: dict, prefix: str = "") -> str:
        return _sentence(f"{prefix}{label(r)} {_need(r)} ({grams(r['padded'])} with the "
                         f"{r['margin']}% margin) and {_supply(r)}{_tracked(r)}")

    if short:
        kind, parts = "warning", [f"not enough filament loaded{where}."]
        parts += [short_part(r) for r in short]
        parts += [mixed_part(r, "also check: ") for r in mixed]
        parts += [barely_part(r, "also barely enough: ") for r in barely]
    elif mixed:
        kind, parts = "warning", [f"not enough filament may be loaded{where}."]
        parts += [mixed_part(r) for r in mixed]
        parts += [barely_part(r, "also barely enough: ") for r in barely]
    elif barely:
        kind, parts = "warning", ["barely enough filament."] + [barely_part(r) for r in barely]
    else:
        kind, parts = "info", []
        fine = [r for r in results if r["status"] == "ok"]
        unknown = [r for r in results if r["status"] == "unknown"]
        if len(fine) > 3:
            numbers = sorted(n for r in fine for n in r["slots"])
            parts.append(f"quantity OK for slots {_join([str(n) for n in numbers])}.")
        elif fine:
            parts.append("quantity OK.")
            parts += [_sentence(f"{label(r)} {_need(r)}, {_supply(r)}") for r in fine]
        if unknown:
            many = sum(len(r["slots"]) for r in unknown) > 1
            outcome = "so they weren't checked" if many else "so it wasn't checked"
            names = _join([label(r) for r in unknown])
            sentence = _sentence(f"no spool found for {names}, {outcome}")
            parts.append(sentence if parts else sentence[:1].lower() + sentence[1:])
        if not parts:
            return None
    parts += [dry_part(r) for r in results if r.get("dry")]  # after the stock sentences, before the cost
    if cost:
        parts.append(cost)  # last, so fit_text drops it first
    return kind, "Spooler: " + " ".join(parts)


def dry_part(r: dict) -> str:
    slot = r["slot"]
    name = r.get("name") or " ".join(p for p in (slot["preset"].split("@")[0].strip() or slot["material"], slot["colour"]) if p)
    which = f"slot {r['slots'][0]}" if len(r["slots"]) == 1 else f"slots {_join([str(n) for n in r['slots']])}"
    days = r["dry"]["days"]
    if days is None:
        return f"{name} ({which}) has no drying date."
    return f"{name} ({which}) was last dried {days} day{'' if days == 1 else 's'} ago."


def cost_sentence(results: list[dict], code: str) -> str:
    """"About €1.23 of filament." from the matched spools' prices, or "" when none is known."""
    costs = [r["cost"] for r in results if isinstance(r.get("cost"), (int, float))]
    if not costs:
        return ""
    return f"About {CUR_SIGNS.get(code, code + ' ')}{sum(costs):.2f} of filament."


def fit_text(text: str, limit: int = NOTICE_MAX) -> str:
    """Whole sentences only: what doesn't fit is dropped and counted, never cut mid-sentence."""
    if len(text) <= limit:
        return text
    sentences = re.split(r"(?<=\.) ", text)
    for keep in range(len(sentences) - 1, 0, -1):
        note = f" (+{len(sentences) - keep} more, see the log)"
        shown = " ".join(sentences[:keep])
        if len(shown) + len(note) <= limit:
            return shown + note
    return text[:limit - 1] + "\u2026"


_recent: dict[str, float] = {}
_plate: dict = {"payload": None, "slots": [], "margin": DEFAULT_MARGIN, "page": None}


def is_repeat(text: str) -> bool:
    """True if this exact notice was shown moments ago, so re-slicing doesn't stack warnings."""
    now = time.monotonic()
    expired = [key for key, shown in _recent.items() if now - shown > REPEAT_SECS]
    for old in expired:
        del _recent[old]
    if text in _recent:
        return True
    _recent[text] = now
    return False


def push_notice(kind: str, text: str) -> bool:
    text = fit_text(text)
    ui = orca.host.ui
    push = getattr(ui, "push_notification", None)
    level_name = "WarningNotificationLevel" if kind == "warning" else "RegularNotificationLevel"
    # OrcaSlicer 2.5 has the levels on ui.NotificationLevel; older builds had them on ui itself.
    level = getattr(getattr(ui, "NotificationLevel", None), level_name, None) or getattr(ui, level_name, None)
    if push is None or level is None:
        log.info("Notifications are not available in this build: %s", text)
        return False
    for call in (lambda: push(level, text), lambda: push(text, level)):
        try:
            call()
            return True
        except TypeError:
            continue
        except Exception:
            log.exception("push_notification failed")
            return False
    log.warning("push_notification accepted neither (level, text) nor (text, level)")
    return False


def plate_spools(url: str) -> list[dict] | None:
    """The spool list, from the cache when it is fresh; None if Spoolman can't be reached."""
    age = time.monotonic() - _spool_cache["time"]
    if _spool_cache["url"] == url and age < CACHE_SECS:
        return _spool_cache["spools"]
    result = load_spools()
    return active_spools(result["spools"]) if result["ok"] else None


def plate_rows(results: list[dict]) -> list[dict]:
    rows = []
    for r in results:
        slot, numbers, status = r["slot"], r["slots"], r["status"]
        many = len(numbers) > 1
        preset = slot["preset"].split("@")[0].strip()
        name = r.get("name") or preset or " ".join(p for p in (slot["vendor"], slot["material"]) if p)
        need, have, count = fmt_grams(r["need"]), r.get("have", 0), min(r["pool"], r["matches"])
        total = r.get("total") or max(have, r["need"])
        if status == "unknown":
            headline, detail = "Not checked", f"no spool found for {'these slots' if many else 'this slot'}"
        else:
            headline = {"ok": "Quantity OK", "barely": "Barely enough", "short": "Not enough",
                        "mixed": "Check the spool" + ("s" if count > 1 else "")}[status]
            if status == "mixed":
                detail = f"{need} needed \u00b7 matching spools hold {fmt_grams(r['worst'])} to {fmt_grams(have)}"
            elif count > 1:
                detail = f"{need} needed \u00b7 {fmt_grams(have)} across {count} spools"
            elif status == "ok" and r["matches"] == 1:
                detail = f"{need} needed \u00b7 leaves {fmt_grams(have - r['need'])}"
            elif status == "ok":
                detail = f"{need} needed \u00b7 every matching spool has at least {fmt_grams(r['worst'])}"
            else:
                detail = f"{need} needed \u00b7 {fmt_grams(have)} left"
        rows.append({
            "slots": ("Slots " if many else "Slot ") + " + ".join(str(n) for n in numbers),
            "first": min(numbers), "name": name,
            "meta": " \u00b7 ".join(p for p in (slot["vendor"], f"{len(numbers)} slots, pooled" if many else "") if p),
            "colour": slot["colour"], "status": status, "headline": headline, "detail": detail,
            "fill": round(min(1.0, have / total), 3), "need_pct": round(min(1.0, r["need"] / total), 3),
            "spool_colour": r.get("spool_colour") or slot["colour"],
            "ids": r["ids"],
        })
    return rows


def send_plate(payload: dict | None) -> None:
    page = _plate["page"]
    if page is None:
        return
    try:
        page.post_message(payload or {"type": "plate_clear"})
    except Exception:
        log.exception("Could not update the plate panel")


def show_plate(slots: list[dict], margin: int, results: list[dict] | None) -> None:
    payload = ({"type": "plate", "time": time.strftime("%H:%M"), "rows": plate_rows(results)}
               if results else None)
    _plate.update(payload=payload, slots=slots, margin=margin)
    send_plate(payload)


def clear_plate() -> None:
    _plate["payload"] = None
    send_plate(None)


def recheck() -> None:
    slots, margin = _plate["slots"], _plate["margin"]
    if not slots:
        return
    try:
        show_plate(slots, margin, check_plate(slots, margin, fresh=True)[1])
    except Exception:
        log.exception("Plate re-check failed")


def check_plate(slots: list[dict], margin: int, fresh: bool = False) -> tuple[tuple | None, list | None]:
    """The notice for a plate and its per-group results (None when the spool source couldn't be checked)."""
    key = spool_key()
    if fresh:
        _spool_cache["time"] = float("-inf")
    spools = plate_spools(key) if key else None
    if not key:
        return ("info", "Spooler: no Spoolman address is set up yet, "
                        "so the filament quantity wasn't checked."), None
    if spools is None:
        return ("info", f"Spooler: couldn't reach {source_name()}, "
                        "so the filament quantity wasn't checked."), None
    results = [check_group(group, spools, margin) for group in group_slots(slots)]
    log.info("Plate check: %s", ", ".join(
        f"slot {'+'.join(str(n) for n in r['slots'])} {r['status']}" for r in results))
    cost = cost_sentence(results, stats_currency()) if any(r.get("cost") for r in results) else ""
    return plate_notice(results, cost), results


def run_check(slots: list[dict], margin: int) -> None:
    time.sleep(NOTICE_DELAY)
    try:
        notice, results = check_plate(slots, margin)
        show_plate(slots, margin, results)
        if notice and not is_repeat(notice[1]):
            log.info("Plate notice (%s): %s", *notice)
            push_notice(*notice)
    except Exception:
        log.exception("Plate check failed")


LOGO_DATA_URI = (
    "data:image/svg+xml;base64,"
    "PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNTYg"
    "MjU2Ij4KPHJlY3QgeD0iMCIgeT0iMCIgd2lkdGg9IjI1NiIgaGVpZ2h0PSIyNTYiIHJ4PSI1NiIg"
    "ZmlsbD0iIzE0MTgxRiIvPjxnIGZpbGw9Im5vbmUiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ry"
    "b2tlLWxpbmVqb2luPSJyb3VuZCI+CjxwYXRoIGQ9Ik0xODguMzYgMTA3LjY2QTc3IDc3IDAgMSAx"
    "IDExNiA1N0gyMTZNMjAxIDQyTDIxNiA1N0wyMDEgNzIiIHN0cm9rZT0iI0E5OUJGRiIgc3Ryb2tl"
    "LXdpZHRoPSIxNiIvPgo8cGF0aCBkPSJNODUuNTkgMTAzLjU5QTQzIDQzIDAgMCAxIDE0Ni40MSAx"
    "MDMuNTkiIHN0cm9rZT0iIzc4Q0ZENSIgc3Ryb2tlLXdpZHRoPSIxNCIvPgo8cGF0aCBkPSJNMTU3"
    "LjUzIDEyMi44N0E0MyA0MyAwIDAgMSAxMjcuMTMgMTc1LjUzIiBzdHJva2U9IiNGNENGNzgiIHN0"
    "cm9rZS13aWR0aD0iMTQiLz4KPHBhdGggZD0iTTEwNC44NyAxNzUuNTNBNDMgNDMgMCAwIDEgNzQu"
    "NDcgMTIyLjg3IiBzdHJva2U9IiNGRjk5N0QiIHN0cm9rZS13aWR0aD0iMTQiLz4KPGNpcmNsZSBj"
    "eD0iMTE2IiBjeT0iMTM0IiByPSIxNCIgc3Ryb2tlPSIjRjZGN0ZCIiBzdHJva2Utd2lkdGg9IjEw"
    "Ii8+CjwvZz4KPC9zdmc+Cg=="
)

# White line-art tab icon: the Spooler symbol (spool rim flowing into an arrow). get_icon() must return the
# path of an image file; SVG markup or a data: URI shows no icon.
TAB_ICON_SVG = (
    '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" '
    'fill="none" stroke="#FFFFFF" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">'
    '<path d="M18.05 10.43A7.5 7.5 0 1 1 11 5.5H21"/>'
    '<path d="M18.5 3L21 5.5L18.5 8"/>'
    '<circle cx="11" cy="13" r="2.75"/>'
    '</svg>'
)
TAB_ICON_FILE = DATA_DIR / "spooler_tab.svg"


def icon_path() -> str:
    try:
        if not TAB_ICON_FILE.exists() or TAB_ICON_FILE.read_text(encoding="utf-8") != TAB_ICON_SVG:
            TAB_ICON_FILE.parent.mkdir(parents=True, exist_ok=True)
            TAB_ICON_FILE.write_text(TAB_ICON_SVG, encoding="utf-8")
    except OSError:
        log.exception("Could not write the tab icon to %s", TAB_ICON_FILE)
        return ""
    return str(TAB_ICON_FILE)


# The UI: one compiled Vue 3 + PrimeVue page (ui/, shared Orca UI foundation), embedded at the end of this file
# by scripts/embed_ui.py. The native tab, the separate spool window and the separate Settings window all serve
# it; the boot JSON says which surface it is and carries the saved settings.
UI_LANGUAGES = ("auto", "en", "pt-BR")


def ui_page() -> str:
    return zlib.decompress(base64.b64decode(UI_PAGE_Z64)).decode("utf-8")


def _json_for_html(data: object) -> str:
    """JSON safe inside a <script> block: no literal <, > or & can end it or open a tag."""
    return json.dumps(data).replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")


def host_language() -> str | None:
    """OrcaSlicer's UI language (`orca.host.app_language()`, e.g. "pt_BR"), or None when the host doesn't offer it.
    The page maps it to a language it has, then falls back to the browser's; an explicit choice wins."""
    try:
        attr = orca.host.app_language
        lang = attr() if callable(attr) else attr
    except Exception:  # noqa: BLE001 - an optional host call; the page has its own fallback
        return None
    return lang if isinstance(lang, str) and lang else None


def ui_language() -> str:
    value = get_settings().get("ui_language")
    return value if value in UI_LANGUAGES else "auto"


def save_ui_language(value: object) -> None:
    """The page's language choice ("auto", "en", "pt-BR"); anything else is ignored."""
    if value in UI_LANGUAGES:
        save_settings({**get_settings(), "ui_language": value})


def settings_boot(current_url: str, low_stock_grams: float, plate_check: bool = True,
                  plate_margin: int = DEFAULT_MARGIN, weight: str = "both", cart: bool = False,
                  source: str = "spoolman", progress: dict | None = None, columns: int = 1,
                  stats: dict | None = None, wizard: bool = False, verified_url: str = "") -> dict:
    return {
        "url": current_url or "", "verified_url": verified_url, "default_url": DEFAULT_SPOOLMAN_URL,
        "source": parse_source(source), "low_stock": low_stock_grams, "plate_check": bool(plate_check),
        "plate_margin": plate_margin, "weight_display": parse_weights(weight), "show_cart": bool(cart),
        "spool_columns": parse_columns(columns), "progress": parse_progress(progress), "stats": parse_stats(stats),
        "display": display_settings(), "drying": drying_settings(), "cur_code": _cur["code"] or "EUR",
        "wizard": bool(wizard), "log_path": str(LOG_FILE),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None) -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window)."""
    boot = {
        "mode": mode, "view": view, "version": PLUGIN_VERSION, "lang": host_language(), "pref": ui_language(),
        "low_stock_default": LOW_DEFAULT, "refresh_ms": REFRESH_SECS * 1000, "display_defaults": DISPLAY_DEFAULTS,
        "own_fields": ["tag", ORCA_SETTINGS_FIELD, DRIED_FIELD, *CALIBRATION_FIELDS], "logo": LOGO_DATA_URI,
        "settings": settings or settings_boot(get_settings().get("spoolman_url", ""), parse_low(get_settings().get("low_stock_grams"))),
    }
    return ui_page().replace("__BOOT__", _json_for_html(boot), 1)


def main_html() -> str:
    return page_html("main")


def settings_html(current_url: str, spoolman_info: dict, low_stock_grams: float,
                  plate_check: bool = True, plate_margin: int = DEFAULT_MARGIN,
                  weight: str = "both", cart: bool = False, source: str = "spoolman",
                  progress: dict | None = None, columns: int = 1, stats: dict | None = None,
                  wizard: bool = False) -> str:
    """``spoolman_info`` describes the saved URL, not whatever is typed in the field."""
    verified_url = clean_url(current_url) if spoolman_info.get("ok") else ""
    return page_html("settings", "settings", settings_boot(
        current_url, low_stock_grams, plate_check, plate_margin, weight, cart, source, progress, columns, stats,
        wizard, verified_url))


def tab_html(initial_view: str, current_url: str, low_stock_grams: float,
             plate_check: bool = True, plate_margin: int = DEFAULT_MARGIN,
             weight: str = "both", cart: bool = False, source: str = "spoolman",
             progress: dict | None = None, columns: int = 1, stats: dict | None = None,
             wizard: bool = False) -> str:
    """The spool views and Settings as two views of one page (the native tab)."""
    return page_html("tab", "main" if initial_view == "main" else "settings", settings_boot(
        current_url, low_stock_grams, plate_check, plate_margin, weight, cart, source, progress, columns, stats, wizard))


class SpoolerWindow(orca.script.ScriptPluginCapabilityBase):
    def __init__(self):
        super().__init__()
        self._panel = None
        self._settings_window = None
        self._verified_url = ""
        self._verified_bambu = False
        self._release_url = ""
        self._refreshing = False
        self._testing = False
        self._checking_update = False

    def get_name(self):
        return PLUGIN_NAME

    def _spoolman_url(self):
        return get_settings().get("spoolman_url", "")

    def _save_settings(self, url, low_stock, plate_check=True,
                       plate_margin=DEFAULT_MARGIN, weight="both", cart=False, src="spoolman",
                       progress=None, columns=None, stats=None):
        sync_config(self)  # take a pending plugin-manager edit first, so this save wins over it
        settings = get_settings()
        settings["spool_source"] = parse_source(src)
        if settings["spool_source"] == "spoolman":
            settings["spoolman_url"] = url
        settings["low_stock_grams"] = parse_low(low_stock)
        settings["plate_check"] = parse_flag(plate_check)
        settings["plate_margin_percent"] = parse_margin(plate_margin)
        settings["weight_display"] = parse_weights(weight)
        settings["show_cart"] = parse_flag(cart, default=False)
        if columns is not None:
            settings["spool_columns"] = parse_columns(columns)
        if progress is not None:
            settings["progress"] = parse_progress(progress)
        if stats is not None:
            settings["stats"] = parse_stats(stats)
        if save_settings(settings):
            log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                     url, settings["low_stock_grams"], settings["plate_check"],
                     settings["plate_margin_percent"])
            sync_config(self)
            return True
        orca.host.ui.message(
            f"Could not write settings to {SETTINGS_FILE}. Check that this folder is writable.",
            title=PLUGIN_NAME,
            icon="error",
        )
        return False

    def _after_save(self):
        self._open_panel()
        self._push_data()

    def _open_settings(self):
        if self._settings_window is not None and self._settings_window.is_open():
            return
        saved_url = self._spoolman_url()
        self._settings_window = orca.host.ui.create_window(
            html=settings_html(
                saved_url,
                spoolman_info={"ok": False, "pending": True},
                source=source(),
                low_stock_grams=parse_low(get_settings().get("low_stock_grams")),
                plate_check=plate_settings()[0],
                plate_margin=plate_settings()[1],
                weight=weight_mode(),
                cart=cart_on(),
                progress=progress_settings(),
                columns=spool_columns(),
                stats=stats_settings(),
                wizard=wizard_pending(),
            ),
            title=f"{PLUGIN_NAME} - Settings & About",
            width=SETTINGS_SIZE[0],
            height=SETTINGS_SIZE[1],
            on_message=self._on_settings,
            on_close=self._on_settings_close,
        )

    def _check_connection(self, url, window, src=None):
        if self._testing:
            return
        self._testing = True
        src = parse_source(src or source())

        def worker():
            info = bambu_ping() if src == "bambu" else ping(url)
            self._testing = False
            if src == "bambu":
                self._verified_bambu = bool(info.get("ok"))
            elif info.get("ok"):
                self._verified_url = clean_url(url)
            if window.is_open():
                window.post({"type": "test_result", "source": src, "url": url, **info})

        threading.Thread(target=worker, daemon=True).start()

    def _bambu_sign_in(self, data, window):
        if data.get("action") == "sign_out":
            self._verified_bambu = False

        def worker():
            result = bambu_sign_in(data)
            if window.is_open():
                window.post({"type": "bambu_auth_result", **result})

        threading.Thread(target=worker, daemon=True).start()

    def _on_settings(self, data):
        msg_type = data.get("type") if isinstance(data, dict) else None
        if msg_type == "ready":
            # Only check the connection once the page confirms its message
            # listener is registered, so the result can never arrive too early.
            if self._settings_window is not None:
                self._check_connection(self._spoolman_url(), self._settings_window)
        elif msg_type == "test":
            url = (data.get("url") or "").strip()
            if self._settings_window is not None:
                self._check_connection(url, self._settings_window, data.get("source"))
        elif msg_type == "save":
            save_display(data.get("display"))
            save_drying(data.get("drying"))
            # The page already gates Save; enforce it here too.
            url = (data.get("url") or "").strip()
            src = parse_source(data.get("source"))
            verified = self._verified_bambu if src == "bambu" else clean_url(url) == self._verified_url
            if not verified:
                if self._settings_window is not None:
                    self._settings_window.post({
                        "type": "test_result",
                        "source": src,
                        "ok": False,
                        "url": url,
                        "error": "Test the connection successfully before saving.",
                    })
                return
            saved = self._save_settings(url, data.get("low_stock"), data.get("plate_check"),
                                        data.get("plate_margin"), data.get("weight_display"),
                                        data.get("show_cart"), src, data.get("progress"),
                                        data.get("spool_columns"), data.get("stats"))
            if saved:
                self._after_save()
                if self._settings_window is not None:
                    self._settings_window.close()
        elif msg_type == "wizard":
            if data.get("done"):
                save_wizard_done()
        elif msg_type == "bambu_auth":
            if self._settings_window is not None:
                self._bambu_sign_in(data, self._settings_window)
        elif msg_type == "feedback":
            open_url(FEEDBACK_URL)
        elif msg_type == "check_update":
            if self._checking_update or self._settings_window is None:
                return
            self._checking_update = True
            window = self._settings_window

            def worker():
                result = get_release()
                self._checking_update = False
                if result["ok"]:
                    self._release_url = result["url"]
                    result["newer"] = is_newer(result["version"], PLUGIN_VERSION)
                if window.is_open():
                    window.post({"type": "update_result", **result})

            threading.Thread(target=worker, daemon=True).start()
        elif msg_type == "release" and self._release_url.startswith("https://"):
            open_url(self._release_url)
        elif msg_type == "cancel" and self._settings_window is not None:
            self._settings_window.close()
        elif msg_type == "ui_language":
            save_ui_language(data.get("value"))

    def _on_settings_close(self):
        self._settings_window = None

    def on_unload(self):
        # Without this, open windows would outlive OrcaSlicer's shutdown.
        log.info("Unloading")
        stop_workers()
        stop_presence()
        if self._panel is not None and self._panel.is_open():
            self._panel.close()
        if self._settings_window is not None and self._settings_window.is_open():
            self._settings_window.close()

    def on_message(self, data):
        msg_type = data.get("type") if isinstance(data, dict) else None
        if msg_type in ("ready", "refresh"):
            sync_config(self)
            self._push_data()
        elif msg_type == "settings":
            self._open_settings()
        elif msg_type == "order":
            open_search(data.get("query"))
        elif msg_type == "printers":
            save_printers(data.get("printers"))
        elif msg_type == "live":
            self._panel.post({"type": "live", "live": live_poll(), "usage": usage_state()})
        elif msg_type == "printer_code":
            save_printer_code(data.get("id"), data.get("code"))
        elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
            threading.Thread(target=lambda: self._panel.post({"type": "usage", "usage": usage_action(data)}), daemon=True).start()
        elif msg_type == "stats":
            threading.Thread(target=lambda: self._panel.post({"type": "stats", "stats": stats_data(data.get("period"))}), daemon=True).start()
        elif msg_type == "stats_export":
            threading.Thread(target=lambda: self._panel.post({"type": "stats_export", **export_history(data.get("period"))}), daemon=True).start()
        elif msg_type == "spool_detail":
            threading.Thread(target=lambda: self._panel.post({"type": "spool_detail", "detail": spool_detail(data.get("id"))}), daemon=True).start()
        elif msg_type == "send":
            start_send(self._panel.post)
        elif msg_type == "sync_presets":
            start_preset_sync(self._panel.post)
        elif msg_type == "spool_action":
            start_spool_action(data, self._panel.post)
        elif msg_type == "moon_spool":
            start_moon_spool(data, self._panel.post)
        elif msg_type == "tick":
            auto_send(self._panel.post)
        elif msg_type == "ui_language":
            save_ui_language(data.get("value"))

    def _push_data(self):
        if self._panel is None or not self._panel.is_open():
            return
        ws_sync(self._panel.post)
        url = self._spoolman_url()
        if source() == "spoolman" and not url:
            self._panel.post({
                "type": "spools",
                "ok": False,
                "error": "No Spoolman URL configured yet - click Settings to set one.",
                "error_code": "no_url", **peer_context(),
            })
            return
        if self._refreshing:
            return
        self._refreshing = True
        snapshot = refresh_snapshot()
        _local_sync()
        panel = self._panel
        low_stock_grams = parse_low(get_settings().get("low_stock_grams"))

        snapshot = snapshot if source() == "spoolman" else None

        def worker():
            result = fresh_spools(snapshot)
            self._refreshing = False
            if panel.is_open():
                panel.post({"type": "spools", "low_stock_grams": low_stock_grams,
                            "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                            "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            **spools_message_extras(result), **result})

        threading.Thread(target=worker, daemon=True).start()

    def _on_panel_close(self):
        self._panel = None
        ws_sync(None)

    def _open_panel(self):
        if self._panel is not None and self._panel.is_open():
            self._push_data()
            return
        self._panel = orca.host.ui.create_window(
            html=main_html(),
            title=PLUGIN_NAME,
            width=MAIN_SIZE[0],
            height=MAIN_SIZE[1],
            on_message=self.on_message,
            on_close=self._on_panel_close,
        )

    def _open(self):
        if not configured():
            self._open_settings()
            return
        self._open_panel()

    def get_default_config(self):
        return default_config()

    def on_load(self):
        log.info(
            "%s %s loaded (Python %s, %s)",
            PLUGIN_NAME,
            PLUGIN_VERSION,
            platform.python_version(),
            platform.platform(),
        )
        sync_config(self)
        start_presence()
        self._open()

    def execute(self):
        self._open()
        return orca.ExecutionResult.success(f"Opened {PLUGIN_NAME}")



class _SettingsView:
    """Stands in for a settings window when Settings is a view inside the tab.

    Same post / is_open / close calls as a host window, so the settings code is shared.
    """

    def __init__(self, page):
        self._page = page

    def post(self, data):
        self._page.post_message({**data, "view": "settings"})

    def is_open(self):
        return True

    def close(self):
        self._page.post_message({"type": "show_view", "view": "main"})


if _PAGES:

    class SpoolerPage(orca.pages.PagesPluginCapabilityBase):
        """The Spooler tab, with Settings as a second view inside it.

        Used instead of SpoolerWindow when orca.pages exists. Its settings methods duplicate
        SpoolerWindow's rather than share a mixin, to avoid multiple inheritance with a
        pybind11 base class.
        """

        def __init__(self):
            super().__init__()
            self._settings_window = _SettingsView(self)
            self._verified_url = ""
            self._verified_bambu = False
            self._release_url = ""
            self._refreshing = False
            self._testing = False
            self._checking_update = False
            _plate["page"] = self

        def get_name(self):
            return PLUGIN_NAME

        def get_type(self):
            return orca.PluginType.Pages

        def get_icon(self):
            return icon_path()

        def get_ui(self):
            try:
                url = self._spoolman_url()
                return tab_html(
                    source=source(),
                    initial_view="main" if configured() else "settings",
                    current_url=url,
                    low_stock_grams=parse_low(get_settings().get("low_stock_grams")),
                    plate_check=plate_settings()[0],
                    plate_margin=plate_settings()[1],
                    weight=weight_mode(),
                    cart=cart_on(),
                    progress=progress_settings(),
                    columns=spool_columns(),
                    stats=stats_settings(),
                    wizard=wizard_pending(),
                )
            except Exception:
                log.exception("get_ui() raised")
                raise

        def on_message(self, arg0):
            # The base class hints "arg0: str", but a parsed dict arrives (as with
            # create_window). A string is still accepted in case that changes.
            try:
                data = json.loads(arg0) if isinstance(arg0, str) else arg0
                if not isinstance(data, dict):
                    return
                if data.get("view") == "settings":
                    self._on_settings(data)
                    return
                msg_type = data.get("type")
                if msg_type in ("ready", "refresh"):
                    sync_config(self)
                    self._push_data()
                    if msg_type == "ready" and _plate["payload"]:
                        send_plate(_plate["payload"])
                elif msg_type == "settings":
                    self._open_settings()
                elif msg_type == "order":
                    open_search(data.get("query"))
                elif msg_type == "printers":
                    save_printers(data.get("printers"))
                elif msg_type == "live":
                    self.post_message({"type": "live", "live": live_poll(), "usage": usage_state()})
                elif msg_type == "printer_code":
                    save_printer_code(data.get("id"), data.get("code"))
                elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
                    threading.Thread(target=lambda: self.post_message({"type": "usage", "usage": usage_action(data)}), daemon=True).start()
                elif msg_type == "stats":
                    threading.Thread(target=lambda: self.post_message({"type": "stats", "stats": stats_data(data.get("period"))}), daemon=True).start()
                elif msg_type == "stats_export":
                    threading.Thread(target=lambda: self.post_message({"type": "stats_export", **export_history(data.get("period"))}), daemon=True).start()
                elif msg_type == "spool_detail":
                    threading.Thread(target=lambda: self.post_message({"type": "spool_detail", "detail": spool_detail(data.get("id"))}), daemon=True).start()
                elif msg_type == "plate_recheck":
                    threading.Thread(target=recheck, daemon=True).start()
                elif msg_type == "plate_dismiss":
                    _plate.update(payload=None, slots=[])
                elif msg_type == "send":
                    start_send(self.post_message)
                elif msg_type == "sync_presets":
                    start_preset_sync(self.post_message)
                elif msg_type == "spool_action":
                    start_spool_action(data, self.post_message)
                elif msg_type == "moon_spool":
                    start_moon_spool(data, self.post_message)
                elif msg_type == "tick":
                    auto_send(self.post_message)
                elif msg_type == "ui_language":
                    save_ui_language(data.get("value"))
            except Exception:
                log.exception("on_message() raised (%s)", message_summary(arg0))

        def _spoolman_url(self):
            return get_settings().get("spoolman_url", "")

        def _push_data(self):
            ws_sync(self.post_message)
            url = self._spoolman_url()
            if source() == "spoolman" and not url:
                self.post_message({
                    "type": "spools",
                    "ok": False,
                    "error": "No Spoolman URL configured yet - click Settings to set one.",
                "error_code": "no_url", **peer_context(),
                })
                return
            if self._refreshing:
                return
            self._refreshing = True
            snapshot = refresh_snapshot()
            _local_sync()
            low_stock_grams = parse_low(get_settings().get("low_stock_grams"))

            snapshot = snapshot if source() == "spoolman" else None

            def worker():
                result = fresh_spools(snapshot)
                self._refreshing = False
                self.post_message({"type": "spools", "low_stock_grams": low_stock_grams,
                                   "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                                   "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            **spools_message_extras(result), **result})

            threading.Thread(target=worker, daemon=True).start()

        def _save_settings(self, url, low_stock, plate_check=True,
                           plate_margin=DEFAULT_MARGIN, weight="both", cart=False, src="spoolman",
                           progress=None, columns=None, stats=None):
            sync_config(self)  # take a pending plugin-manager edit first, so this save wins over it
            settings = get_settings()
            settings["spool_source"] = parse_source(src)
            if settings["spool_source"] == "spoolman":
                settings["spoolman_url"] = url
            settings["low_stock_grams"] = parse_low(low_stock)
            settings["plate_check"] = parse_flag(plate_check)
            settings["plate_margin_percent"] = parse_margin(plate_margin)
            settings["weight_display"] = parse_weights(weight)
            settings["show_cart"] = parse_flag(cart, default=False)
            if columns is not None:
                settings["spool_columns"] = parse_columns(columns)
            if progress is not None:
                settings["progress"] = parse_progress(progress)
            if stats is not None:
                settings["stats"] = parse_stats(stats)
            if save_settings(settings):
                log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                         url, settings["low_stock_grams"], settings["plate_check"],
                         settings["plate_margin_percent"])
                sync_config(self)
                return True
            orca.host.ui.message(
                f"Could not write settings to {SETTINGS_FILE}. Check that this folder is writable.",
                title=PLUGIN_NAME,
                icon="error",
            )
            return False

        def _after_save(self):
            self._push_data()

        def _open_settings(self):
            saved_url = self._spoolman_url()
            self.post_message({
                "type": "show_view",
                "view": "settings",
                "source": source(),
                "url": saved_url,
                "low_stock": parse_low(get_settings().get("low_stock_grams")),
                "plate_check": plate_settings()[0],
                "plate_margin": plate_settings()[1],
                "weight_display": weight_mode(),
                "show_cart": cart_on(),
                "spool_columns": spool_columns(),
                "display": display_settings(),
                "drying": drying_settings(),
                "progress": progress_settings(),
                "stats": stats_settings(),
                "cur_code": _cur["code"] or "EUR",
                "wizard": wizard_pending(),
            })
            self._check_connection(saved_url, self._settings_window)

        def _check_connection(self, url, window, src=None):
            if self._testing:
                return
            self._testing = True
            src = parse_source(src or source())

            def worker():
                info = bambu_ping() if src == "bambu" else ping(url)
                self._testing = False
                if src == "bambu":
                    self._verified_bambu = bool(info.get("ok"))
                elif info.get("ok"):
                    self._verified_url = clean_url(url)
                if window.is_open():
                    window.post({"type": "test_result", "source": src, "url": url, **info})

            threading.Thread(target=worker, daemon=True).start()

        def _bambu_sign_in(self, data, window):
            if data.get("action") == "sign_out":
                self._verified_bambu = False

            def worker():
                result = bambu_sign_in(data)
                if window.is_open():
                    window.post({"type": "bambu_auth_result", **result})

            threading.Thread(target=worker, daemon=True).start()

        def _on_settings(self, data):
            msg_type = data.get("type")
            if msg_type == "ready":
                self._check_connection(self._spoolman_url(), self._settings_window)
            elif msg_type == "test":
                url = (data.get("url") or "").strip()
                self._check_connection(url, self._settings_window, data.get("source"))
            elif msg_type == "save":
                save_display(data.get("display"))
                save_drying(data.get("drying"))
                url = (data.get("url") or "").strip()
                src = parse_source(data.get("source"))
                verified = (self._verified_bambu if src == "bambu"
                            else clean_url(url) == self._verified_url)
                if not verified:
                    self._settings_window.post({
                        "type": "test_result",
                        "source": src,
                        "ok": False,
                        "url": url,
                        "error": "Test the connection successfully before saving.",
                    })
                    return
                saved = self._save_settings(url, data.get("low_stock"), data.get("plate_check"),
                                            data.get("plate_margin"), data.get("weight_display"),
                                            data.get("show_cart"), src, data.get("progress"),
                                            data.get("spool_columns"), data.get("stats"))
                if saved:
                    self._after_save()
                    self._settings_window.close()
            elif msg_type == "wizard":
                if data.get("done"):
                    save_wizard_done()
            elif msg_type == "bambu_auth":
                if self._settings_window is not None:
                    self._bambu_sign_in(data, self._settings_window)
            elif msg_type == "feedback":
                open_url(FEEDBACK_URL)
            elif msg_type == "check_update":
                if self._checking_update:
                    return
                self._checking_update = True
                window = self._settings_window

                def worker():
                    result = get_release()
                    self._checking_update = False
                    if result["ok"]:
                        self._release_url = result["url"]
                        result["newer"] = is_newer(result["version"], PLUGIN_VERSION)
                    window.post({"type": "update_result", **result})

                threading.Thread(target=worker, daemon=True).start()
            elif msg_type == "release" and self._release_url.startswith("https://"):
                open_url(self._release_url)
            elif msg_type == "cancel":
                self._settings_window.close()
            elif msg_type == "ui_language":
                save_ui_language(data.get("value"))

        def get_default_config(self):
            return default_config()

        def on_load(self):
            log.info(
                "%s %s loaded as a native tab (Python %s, %s)",
                PLUGIN_NAME,
                PLUGIN_VERSION,
                platform.python_version(),
                platform.platform(),
            )
            sync_config(self)
            start_presence()   # called on load even when the tab is disabled in the Plugins dialog

        def on_unload(self):
            log.info("Unloading")
            stop_workers()
            stop_presence()


if _SLICING:

    class SpoolerFilamentCheck(orca.slicing.SlicingPipelineCapabilityBase):
        """After each slice, checks the plate's filament against the spools in Spoolman."""

        def get_name(self):
            return "Spooler Filament Check"

        def execute(self, ctx):
            try:
                if ctx.step == getattr(orca.slicing.Step, "posSlice", None):
                    if _plate["payload"]:
                        threading.Thread(target=clear_plate, daemon=True).start()
                    return orca.ExecutionResult.success()
                if ctx.step != orca.slicing.Step.psGCodePostProcess:
                    return orca.ExecutionResult.success()
                enabled, margin = plate_settings()
                slots = plate_slots(ctx, parse_usage(read_tail(ctx.gcode_path)))
                usage_plan(slots)
                if enabled:
                    if any(slot["grams"] > 0 for slot in slots):
                        # Off the slicing thread: it may fetch the spool list, and UI calls from
                        # here can deadlock while the GUI waits for slicing to finish.
                        threading.Thread(target=run_check, args=(slots, margin),
                                         daemon=True).start()
            except Exception:
                log.exception("Filament check failed")
            return orca.ExecutionResult.success()


def printer_trays(base: str) -> list[dict]:
    """The printer's slots in slicer order, each with its matched profile."""
    report = moon_poll(base)[0]["print"]
    units = (report.get("ams") or {}).get("ams")
    return [tray for unit in units for tray in unit["tray"]] if units else [report["vt_tray"]]


def slot_plan(trays: list[dict], slots: int, names: set[str]) -> tuple[list, list]:
    """([(slot, preset name)], [slots with no profile]) for the plate's filament slots."""
    plan, missing = [], []
    for slot, tray in enumerate(trays[:slots], 1):
        name = tray.get("profile") or ""
        short = name[len(PROFILE_PREFIX):] if name.startswith(PROFILE_PREFIX) else name
        found = next((n for n in (name, short) if n and n in names), "")
        if found:
            plan.append((slot, found))
        elif tray.get("tray_type"):
            missing.append(slot)
    return plan, missing


def sync_for(snap: dict) -> set[str]:
    """Sync the presets from Spoolman for the selected printer and return every preset name a slot
    can take. Raises RuntimeError saying what is missing. Runs on the Script worker."""
    if not snap:
        raise RuntimeError(f"Open the {PLUGIN_NAME} tab once, then run this again.")
    if not snap.get("host"):
        raise RuntimeError("The selected printer preset has no host address.")
    with pinned_origin() as origin:
        result = get_spools("" if origin[0] == BAMBU_KEY else origin[0])
        if not result["ok"]:
            raise RuntimeError(result["error"])
        state = profile_sync(result["spools"], snap)
    if state["error"]:
        raise RuntimeError("The filament presets could not be updated: " + state["error"])
    return snap["names"] | {PROFILE_PREFIX + n for n in state["names"].values()}


def load_printer_filaments(snap: dict) -> str:
    """Select the matching profile for each plate slot. Runs on the Script worker."""
    names = sync_for(snap)
    plan, missing = slot_plan(printer_trays(snap["host"]), snap["slots"], names)
    done, failed = 0, []
    for slot, name in plan:
        try:
            orca.host.preset.filament.begin_update(slot, name).commit()
            done += 1
        except Exception as exc:
            log.warning("Could not load %s into slot %d: %s", name, slot, exc)
            failed.append(slot)
    text = (f"Loaded {done} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot "
            "colours, so a slot keeps its old colour until you pick its filament in the dropdown.")
    if missing:
        text += " No Spoolman filament matched slot(s) " + ", ".join(map(str, missing)) + "."
    if failed:
        text += " Could not change slot(s) " + ", ".join(map(str, failed)) + "."
    return text


def keep_plan(trays: list[dict], slots: int, names: set[str], current: list, gen: int,
              seen: dict) -> list[tuple[int, str]]:
    """The slots Keep Slots Synced (re)assigns: those whose lane's spool changed since the last pass,
    and those holding a system preset (what OrcaSlicer's own Sync filaments picks) in a snapshot
    newer than the last pass. User presets are left alone. Updates seen: {slot: (spool, gen)}."""
    plan, _ = slot_plan(trays, slots, names)
    changes = []
    for slot, name in plan:
        spool = trays[slot - 1].get("spool_id")
        held, system = current[slot - 1] if slot <= len(current) else ("", False)
        last = seen.get(slot)
        if held != name and (last is None or last[0] != spool or (system and gen > last[1])) and \
                not same_filament(held, trays[slot - 1].get("filament_id")):
            changes.append((slot, name))
        seen[slot] = (spool, gen)
    return changes


def same_filament(held: str, filament_id: object) -> bool:
    """A slot holds a Spooler preset of this filament, for some printer: what u1control may have
    picked for the same spool. Keep Slots leaves it, so the two plugins never take turns."""
    short = held[len(PROFILE_PREFIX):] if held.startswith(PROFILE_PREFIX) else ""
    return bool(short) and filament_id is not None and any(
        name == short and fid == filament_id for (fid, _target), name in _profiles["names"].items())


SNAPSHOT_EVENTS = ("PresetSelected", "PresetSaved", "ProjectOpened", "NewProject")


class SpoolerLoadFilaments(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: put the filament each printer slot holds into the plate's filament slots."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Load Printer Filaments"

    def on_lifecycle_event(self, event, ctx):
        # Preset and project events arrive on the UI thread, where the presets may be read;
        # execute() runs on a worker thread, so it uses this snapshot.
        events = getattr(orca, "LifecycleEvent", None)
        try:
            if event == getattr(events, "PresetSelected", None) and getattr(ctx, "msg", "") == "filament":
                note_filament_selected(str(getattr(ctx, "name", "") or ""))
            if any(event == getattr(events, name, None) for name in ("ProjectOpened", "NewProject")):
                _project["n"] += 1
            if any(event == getattr(events, name, None) for name in SNAPSHOT_EVENTS):
                refresh_snapshot()
            if event == getattr(events, "PresetSaved", None) and getattr(ctx, "msg", "") == "new":
                send_saved_copy(str(getattr(ctx, "name", "") or ""))
        except Exception:
            log.exception("Snapshot on %s failed", event)

    def execute(self):
        try:
            text = load_printer_filaments(dict(_ui_snap))
            log.info(text)
            return orca.ExecutionResult.success(text)
        except Exception as exc:
            log.exception("Load printer filaments failed")
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))


_keep: dict = {"run": None}
_keep_lock = threading.Lock()


def keep_context(snap: dict) -> tuple:
    """What a Keep Slots pass was planned for: printer address, printer preset, slot count, project.
    Not the snapshot's gen, which the pass's own selections advance."""
    return (snap.get("host"), snap.get("selected"), snap.get("slots"), snap.get("project"))


def stop_keep_slots() -> None:
    """Stop the running Keep Slots Synced (cancel, unload) and drop its marker."""
    with _keep_lock:
        if _keep["run"] is None:
            return
        _keep["run"] = None
        mark_keep_slots(False)


class SpoolerKeepSlots(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: keep the plate's filament slots on what each printer lane holds, until run
    again. OrcaSlicer only lets a running Plugins > Run action change slots, so this one stays."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Keep Slots Synced"

    async def execute(self):
        if _keep["run"] is not None:
            stop_keep_slots()
            return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")
        try:
            names = sync_for(dict(_ui_snap))
        except Exception as exc:
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))
        run = object()
        with _keep_lock:
            if _keep["run"] is not None:  # another run started while this one synced
                return orca.ExecutionResult.success("Keep Slots Synced is already running.")
            _keep["run"] = run
        seen, synced = {}, time.monotonic()

        def live() -> bool:
            # Checked after every read and before every selection: a cancel, an unload or a newer
            # run while this one waited on the network ends it before it touches a slot.
            return _keep["run"] is run

        def mark(printer: str) -> None:
            with _keep_lock:
                if live():  # never after a cancel or unload marked it stopped
                    mark_keep_slots(True, printer)

        try:
            while live():
                snap = dict(_ui_snap)
                context = keep_context(snap)
                printer = label_for_target(snap.get("selected") or "")
                mark(printer)
                try:
                    if time.monotonic() - synced > REFRESH_SECS:
                        names, synced = sync_for(snap), time.monotonic()
                        mark(printer)  # the sync can take seconds: keep the marker fresh
                    trays = printer_trays(snap["host"])
                    if not live():
                        break
                    if keep_context(_ui_snap) != context:
                        continue  # the printer, its slots or the project changed: plan again
                    for slot, name in keep_plan(trays, snap["slots"], names, snap.get("current") or [],
                                                snap.get("gen", 0), seen):
                        if not live() or keep_context(_ui_snap) != context:
                            break
                        try:
                            orca.host.preset.filament.begin_update(slot, name).commit()
                            # The selection refreshed the snapshot before the slot changed, so it
                            # still shows the old preset: only a later snapshot may count.
                            seen[slot] = (seen[slot][0], _ui_snap.get("gen", 0))
                        except Exception as exc:
                            log.warning("Could not load %s into slot %d: %s", name, slot, exc)
                    _report("Keep Slots Synced", None)
                except Exception as exc:
                    _report("Keep Slots Synced", str(exc))
                if live():
                    await asyncio.sleep(MOON_POLL)
        finally:
            with _keep_lock:
                # Only this run's own marker: a newer run's stays, and a cancel already wrote its own.
                if _keep["run"] is run:
                    _keep["run"] = None
                    mark_keep_slots(False)
        return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")

    def on_unload(self):
        stop_keep_slots()

    def on_cancelled(self):
        """OrcaSlicer's cancel for a running action (Speed Dial or Plugins > Run)."""
        stop_keep_slots()


def permission_targets() -> dict:
    """What Spooler declares to OrcaSlicer up front: its data folder, its worker threads and the
    fixed addresses it calls. Spoolman, Moonraker and printer addresses are the user's own, so
    OrcaSlicer asks for them on first use."""
    urls = [RELEASE_API]
    for region in BAMBU_HOSTS:
        urls += [BAMBU_HOSTS[region] + LOGIN_PATH, BAMBU_HOSTS[region] + CODE_PATH,
                 TFA_HOSTS[region] + LOGIN_PATH]
    return {"fs_readwrite": [str(DATA_DIR)], "network_http": urls, "threading": True}


def request_permissions() -> None:
    """Declare Spooler's access while the plugin registers; OrcaSlicer builds without the call
    just prompt on first use."""
    request = getattr(orca, "request_permissions", None)
    if request is None:
        return
    try:
        request(**permission_targets())
    except Exception:
        log.exception("Could not declare permissions")


@orca.plugin
class SpoolerPlugin(orca.base):
    def register_capabilities(self):
        request_permissions()
        if _PAGES:
            orca.register_capability(SpoolerPage)
        else:
            orca.register_capability(SpoolerWindow)
        if _SLICING:
            orca.register_capability(SpoolerFilamentCheck)
        orca.register_capability(SpoolerLoadFilaments)
        orca.register_capability(SpoolerKeepSlots)


# --- BEGIN GENERATED UI: scripts/embed_ui.py from ui/ (npm run build); do not edit ---
UI_PAGE_SHA256 = "bb999052f90593386b424fc6cfacb5c2e6818c497c044c530cca6b62f63d5b1e"
UI_PAGE_BYTES = 722242
UI_PAGE_Z64 = (
    "eNq0vXlz28ayB/r//RRmnosXOB4xkpKT6wsaRjmKkzhekmM5zqLokhA5lBCTAAOAWkLyu7/+dc8Gis7JeVXPVRaBmcGsPT3dPb08"
    "6U2rSXu31A+u2sX86X89wc+DeV5epp/o8hMk6HxKPwvd5g8mV3nd6Db9ZNXODh5/YpPLfKHTT64LfbOs6vaTB5OqbHVJxW6KaXuV"
    "TvV1MdEH/KIeFGXRFvn8oJnkc50eoZK2aOf66emyqua6fvKpvP7Xk2ZSF8v2AXqXfpIvl/NikrdFVX76e1OVnzwopuknjXxzcFFV"
    "7SdPR6Mvv//+3Wj05FP59Ol/PXjQrWVRTVdz/cnT2aqcoKoHOtLxeq4pP/3+4nc9aQeTWuetjsrVfB4PZ1UdIbd8UM0e6EFDfWij"
    "sRrHcXtWnqdHw1q3q5qqSZ9qGtmDdnud11TXeqvK9Oxc1WkUp0/preCH3pHKU5QdYCZPqql+1kaHcZqmR0dH/X4n+UiSD/v9qJN+"
    "HD89Oj7ebHYSn/zv/8SqksqbNq/b5qeivYrGVfnjckoDSsaxauwY86YpLks1SSOtWnSQx5jqQVFO9e33s6iNh+XTA+4Sxjyh+VBH"
    "8VbNbQ3LumorzOngKm++vyl/qKulrts7tbJ1zge0wHN+UdP0WV3nd4Oi4V81Qz9vaeppiOOziqt88Dpfno/Vcl/WqW4pa7Ev6ysa"
    "G+VdIQ/9wTpRtl3gsbrcyWnauigvx2q0m363uKjmY3W9ky7tjPv9Xk+rO2RG19SHzeaK/sb9Pv0M2itdmkcC0clVrC7uT1RbnXLT"
    "6haVXJjpidWpHdag4Zl+rA6OYqX1vtFKpTTeE+ReUi4tUY8KvMnfUBf12eE53g7oeTx+tMRufVG2tAhHDGW0GFQtAfAHfadqPcP/"
    "EcE4/yKtKt+XBFFfakrUr6tV2dokftHTbgkBLZsmb7tFykVYjXnVUwLHkof4F7tPNldU0nrQbttsIt50lBvHBIu1Tj89+O3m00t1"
    "k5a0jwH5tV7Oc5rDWivZCTyjRzFN/o9LAtCTvNERfa0K+vi3L6OzZwe/nsdURa7v1VFoNT54eDTGx6+qG/exqnxZbEHewt0GHvmW"
    "ade54hntxofrCjhnO07GNAUTbbdLz0xA0ciWmXPOYDDg/enwUHo4LJ/owVyXl+3VsHz0KNY0JxGX26qVVKdKQjy9I3xoap3qWVFq"
    "u0m5zJqw9Ky4XNX5xVwnvUOly9VCm7cjdVMXLT/X6jqfr3RSbqmBabhkDF5fz6ucAMwu1oOiIVAk/JHppN2qWVge4Jq9WS0udE1P"
    "CZXb/9FSKzpPgC+XerNJzV68nFcX+fzdVdE8Ga/GmX9NTIFGz2echQebeEMYrbrhZHlMOtUFVSXr7dAdC+9wLBSzaIo9brqP/I8v"
    "AxeqU6wGIfvLqI6za4LDOHlHf4ZUVRHbr/mkKOgE0edpQX+2ZhbaLRW7ZNwCDBPbs4XPlCsC2GGU9c7+Lzr/x28xYPaSkpLo7P/O"
    "H8WfqhG9fBJlydn/ffLbb+eb336j9Pgfn2z+m9P+O0j7b3nY/Pbpb/+g339kv/3jt08/vfSDvw4ORRq07YbbGCO7uYJj5tN/jONs"
    "PE6AxfiQvKInGvDzfHIF2MdkmkpxzkiZSwKb0kziUzpssL8Jgw0ITS6i+Dwtz47sS7zdxqrduj4+910cj4dm3uI21UM9b2iCzdL9"
    "+wWjimjJCHzR/KO0fjR+MI63tpLrTiVYN80bTgqXXNhOUGu66jt5pw0Y9bRdTCC2IVW2nszpEE5a1bR3c2wu6rmth46aS9oMcvCj"
    "GHWyJURScgp/kL4DElQCGheM04tWL5oJbXBF50p1M6OGiPTRulTTosFOXhYTql8XpXmw6bVeVC2W9u4in3xQNNpFWdGeLxi3F80i"
    "X6qyEspJBTn4oinKOSEWwsX5tCrndzQbbvS3PHoZFJ2dRLHgJBv76TnVgqx4iuza0PHVmkczZ72joSxV79BtwILWk1as8Eta0JLS"
    "alKVZ8W5avGndEtT+0ZPuo02xZ+am8TDboNCtMzqakHzT7u61DcPfizK9jFnRLXtp+tWy2SigJZOD45cRk79zZ/YD4Y5dRZgUZzl"
    "BErU6VbV9Ei9itc6zYcXNJ8fgA30k0PfKeCK9Mhgi96hH9ONG5P0G1uNustkHFVSbzYFHZ51upT0JUaDRIdiMJWZm5kEbc0ic3QQ"
    "WdCAOHHLE6a38b21skOuZbesZbl26URCikQKt/dTGVXSDsg3mx794ocXtcai1jxFtimLN4WsEkrJPLfBLnyn7ZkYr0s6T86wjK8B"
    "1PJ7jtU+K1ROCIdbR6cYC+f81LppKgaXupV2aJPm/NYyXTUsBg2ycHLn/NgqQm4Ye5XWZl7daUfHMeVge1Bh80wfVgF660Ap2rOj"
    "PjSwuZC1BGQ6KKclzXgpNbr2rlgQKYJv/RstbUKAMJKPRxYQMm4COVPJmbocrs9N4am2VVxLwWtXsFdjxTLKdaVvqPTexQH9Bsz1"
    "FZMHvV6kwWmMRtejonmrZ1S0dxirryyNS2QBdRCoE0fM1J2QjA8tWU0fXVAProKkOM6+wixnX1EiUzFx8t3p928GwgMUM1BC32t1"
    "HHST3i1J9hVWJfueR2M/x57K1mdjgpvo4VrQxjYenydnIMEGxPXWhW7o8KLTcrqiw5I+PqO5IFaQaiQ4/sCbPaaTI306JogjMFFr"
    "Iq2SpamZeJ19NXP7XDHhY5yoHzAy+g6LmKHWOLnmU6M3lR/N3XdzTmfNBxkaIWHqC2AgG58y10MNagJEYZUJ/rKspaYTrZ5p9btO"
    "+RACvUjztpq0tME1yMt1S9QXfdbSGa+nYC7wPsoJhK+pwKF5r+jwlUc9mxHmaMAY8/tkrvNytfQJtPw/5KuGKiMKVFJu8rr8vny7"
    "Kn2FBCbNh2KJhB4BzjP6Hz3TA2k3i7gQ0aaQQDwznWK+NkUpPiIbQofumVqP48Fy1VzxpzFxX0nUHcqezhBlv70EZucikT3oHoQf"
    "bpcYTMSbOEw3MxeMVnY1dXZoi0rfLMUUJBnOQg4djalNLQ011E/aoaazpaSTYmAa3/py4SLsfhLmhV8Tkm1Wiz2D6Pe7g7g/qKP/"
    "HwZle7MNqrAj+o/r2Nar0lBo3eURwvKZHrb1nV3YZ5pbUzylRUlE1t0aadvttippeh49cuCepkzMMhzW+voUQwQomiribTWbhRNa"
    "lU8P+/2Dg6CCQ85+xngZn5hPfX1M5xpCgzqKMQ/10FA1vlXz+TpM26lIiA3CxD5tu93p/HVVTB8cbrdNWy33ztjOfuGVJ7TH/Wpp"
    "Lcq9wNc+KYftLvC15wNuRhZyz2e8tK5Ki0T21mkzqdIodmC484lFTyF06o9CpzStd5vTrt90dA3Dj20joOd6HZRptpDgKmDsTtuS"
    "bGtZ8oxoEfcg30FYWOzMY7tzQshGoJf61Hgboke7rAHn+zrAZc+Ev3ij1Q+aid+fCFLofFJf7z0TDBTMSnsUTDXhdmnDJ7zLi3kn"
    "cTbPL5v0n/JS6tu2k2vWqpPWYPKIG6lt6s4RQE8WYjxaT3xj/fTgOHbI2adv0i8+9/guKP/F53a27fdf/JPmRMhDVE7ZP2hHyiFF"
    "ekqH7+WlriFy2pZVC4qjU/ExrXpY8WfHRNoE7483mz9NhYyshJsMvzhy1KmZ/MhAnxnRsfqX7dG35kHQcvoGpMB3evjGILbvcGaH"
    "GM9V6PDdj7Yq+kbjg1Z1ZuUzgyE8grCddBIsA9yABMJXwDpY8q/0Mn4JgmboAWcvxPyrM71VeUrNmW0kL1Hc7dIx4TK7CN0lzWjF"
    "8uk0hA4HWFn3NTL5tAQvZl8V4FR4PdzL+idtAcEWjIQ+mJoCZk5tue1WvcAZ9Uqrt9rvvj+Z2GTiStsVfKzaLJJpSt+ieEp0qE2g"
    "718hwbMOXwJ2X9Bh55Pem+P74OCFfmoZSmDDtw7jvJUj5K1F9XyWyDEoLQ11Z29qN8H/q/gQ5GrkGHrlv30lSa9cte3Qnf5SLQCl"
    "u+uDmlsHPwDL1m+nLYvZiapds4RwS0f9lvllQvt1dfNA+8F/y2IIx6GnWmCvHbamC4A9oq913VBxYtpVywffM8Ylr4ryQwr56dIg"
    "FySo3YQ0kEz96KVnfE5YCFZ1KsfhsB7aWa+5JerAsHYdSKkLGTFYxPAQVqEaYvUSgkT1B/4SIKa1qnfbr3e6rHYT7OzWqd5qs7+U"
    "7xxNnxvAT39nwnjZ0AnTbZahmGfCYJw1qRbLVYtjLvpGR9202Bba833seV0nPRqMeCP5Xn5jZWsWEj8HKrUvR19QA5EH0qP/ocGK"
    "nPe9m+eHWgp10x9q4ioGRXN6+hZMqanv+DGNoidTgZPa9IcYTp6u2PZ56Lbt8TCYPoIEQre1Qbc6wLUMnkMrFyVsS1ULrzmM2gAo"
    "DjcbvoVz2cL9msaofy6HeEr3IREmZqvw6YytEeQp7TD7G3xGvaoVw2+wvwmnu0l/6dETZJg0sKRUTCWuLpJaATjwVECaCcETdbEe"
    "mNS0UIbCpGeBxlgVVKJwqbXSrrQtUQ6a1UUDGQt2g7zUqkdVlx6Y4rV/cR3/59CfOUH2R04eRWTbtgcq7OCAmpmgfuK0zY892kuI"
    "vQJk+4fd7GuzkYnLNrWKTLcF4WAbArdvd7wfII/LprbKdcuWYBqMAUb9oolZ9afFz8Drv2ghcr6jVUOpI9+7X5EvE4BSTEF+B5FL"
    "aurebAJE+S83FkNzJa1ZR32PCrPVvmF4trgdODqgFgDpRFui+w9x1ul2H9WIyuS0pVX3hKMlLewOcGDr6USeL8unuBcLQJ6DCV/u"
    "YUQ6iNv2L6hZCze2a7Y/hhTN72FYO5Yu5Usw1HknMNohadP74g2iXPLJB3uH8IaOut539OeNZev8BjDIRzDOTsf4iA2WvEXvCN++"
    "ocNytyxT+bqN3shoQejxhsmi1s3ym+BMC579koSpaRsn5jXtJKsSslN3W9N2zj/eNG7lg2lX/gRyvJJNGfq95Tqr3BNXaZ5dV2nL"
    "7B9Xu7MJ/85A7ZtIhyP7RrSZu9+z9IsFLo+JHxLBZiBb2ATtGAYqDJqOt9cOFQ0wM7jMQHqskWgriVmBg95x0to0tz/fswwk4P2g"
    "KWDOVHzQTHBE8PfmiPUkYXiWM4DxochfUZ9oeO4YPAzQcLsP+3KrW3sC2iqGIAk0n3F2E5cGV9odrnED5j4ArgGqqVvHqkLIX7Sp"
    "kXHivj3vvFXhm5+Gpg2E799RH944kVDdmiuAYbvZ0IsR+qfmKiE2wnkpBYk/lBa4FK7kUaqFvJzRQUu/QAMlEmSnx8FZO2nttYUq"
    "VC4dqIIOACVU8RqAY8gknsOGL9xZnu6pZRQGDCnggTGQeT2OK3c/28RemlTIFUCe0tF8giHIfQz25VgkGWOH/OUqv46HvqoI80Yd"
    "iMIPNhu8VTRlvVEERZnyaQrpPe5WtuaytbkpQKZEWHaLqSpmsM0xyOUrM7HUQf9a4XKUTpFJ3ugxcXTjpMiCbNdt4ppsWoFPZpEO"
    "Ks1xLSHCsCHXJEc+VUZr+J98R6s9Trpl8Nl2y/vNre+89VfYv4YaFFgjjTZxiYRr3TqnbhCwxuoXlIuzNvkOD9kf/Le1NwK6jB5y"
    "AWISJK20Tw/DC7FV6y9mGdil/Z22AspgKjdb9hNpnFqT9h+2fLsQJ/zAe3DWpuvRiFWfRqMEFzfqTHbaQNqo6nPPEy9b5onVTgko"
    "GUxNFm46FB3PRMtC18V3fy4F4kGQaecDgJzxNCf8vbuc2W14bHLGaDLSZ0fnqWuYXmJpXhO2vutMxKX7Hln0Ne1Xc17k9eVqQdUS"
    "p69mxbzV9f4vJU8+ZaUK23c/8J26yunHaiqnrh7/+b2vX0AM+PEqOPsvhlJOX+VN+/Hvkft3uoFy/6YrrsjHu2MVTPZWIZkf/bgo"
    "J/PVlOChA1DX9nObTd9zYVGM/FhZzpWiv1dFGe2BUJO+VXM7ro/WF5SQOhkq9g2SMj46QCb47Rd39gtKHSMTPEOndV+CsqRZc4dp"
    "9NBswZEtKNncviv8tri8av/NF1zGftZcFbN2Tz85HT1tqoXeP3jkfHT0Rm91/xAlUwbZVm+xfxs9je4vWpiJoqdVTRTPvuUN8rgg"
    "tzD9CLbayd+qVSnzsL+7Jlf6a2+C72ExyRjv4s2AwFu2XUURPglUkdZn7TmOfNFJFSWMWuivnpw5IIVyi8Pt/fq7/PIcxzyrwzx4"
    "YfC2ow+6Kp3mjY7DH6xKLMF/HsdewYzFgND7W9Cxym9EshB5VFBXrlrqY7+/T58ROF0rMx3JGgeu7UI+MJyRPVv3aAhnenABrJrT"
    "MQFuEFKS3Vo48e9XssXxmQ9GPCAZicp3hjdy47P8Qe5P3EUXwxKVW5WahVUi4mmdQoNVArtqjbqSUzj2y365l5SUxW/SKlxoNUkr"
    "mmgAwMTOuqVSJgMo4eMIzN2iNfb4Z+JznpZDU13UZPPU9oBVHuxgSoEyhk9DWVDHCLITpwt4TN//ja9b+S4WsntFHeS8Ss3pA9dD"
    "KLAU0SpOVn5+R63XCRKqV2aD9kBnNipiOhrcZ5rkKM+iJrV6XBDLUZGwn6rwlBUmgXUHUjNMSLPC3nNyTfDNo/DD/4y+/Gi1uxNQ"
    "BFMwSQvcdFbAvsEMZNzQJE4mfgaud1CBkKB0stddOnAo0wMMAeTktJiigjn1zQa/vSMidn8mwvzs8DzO+AcV8qvyn8ZJEShHmg5A"
    "/WINSZZiLjfoDW5ULcR57SlQ0QqSLVWL9mML7UdHbSqnRURPRfN+pYnRuxUODao1Hg0Femdv8gXhEMFu8cDSa0SOQZneHSpjo2uP"
    "+SeaLba0mnx3ps/dp6M4YCdPmdweRSJtTp2mUTx0xL9cy3mKnOh+4nyA7tU9FTktJPZJ+xG1HCOftcoYb41mplPPKZrTK9YQTdvt"
    "pQ5ZXWYOrfhp7NSPnUTKMrc7NdP5sVPzMKyMC7KAyVbZq+8XMNqjVpNtp4Cp1+UXnfw69zlgNKM6K7L3bfJlS4zgn23yto0N07zZ"
    "7D+FWDttf1YJ7TMj4BRNzqnlvg3uYBFpDklFOmN06WbO9bK7hK6zp4I1q5SgdW7a5vVoS9F6E/Y7YhWv29ZoIyYXwLgApnqzYVJ8"
    "TN+NgUa9RmfFbZdR5eRkOfh5qqdKKjk6hl75E8p02TfCKdnT6Jq+zWqkVnHyI/+t6Hi8MXD3gE4vXU4bAsQ9mmHNikYaETAStDb6"
    "HrLVQm9MmUk+MWqqvR0osh0ndrOQAr+0LD3ofSe/hIJ+RR7hkF9FKNCjQdKgCxSi39IvBc1WYc5OIih6h2bic2uP0MZOlThZyZnU"
    "uGXxI7AL45ErZLHUeg1uH2g741sa9IAFOCwN4E8LQr+cAgkF7zlqYitChtAww96Pml7UMlmF68yeL5xiab9f2naN9MLTxjhntqzZ"
    "6tuwddpkW9GINQgdxFkwY5xEfSq31U35UvSCQzlCcHIw720lL0lBH9m2/KcETe/+E2g6DKDJKZYf7p1Cl7lVzwX337TqK3l616rv"
    "bRqUddSHls3m1DP+DfZiF0V4jP67w5pm8O6o5nPXALmT5hN+ImAXUKVjnWhEorJYGd7KHUQ3fkf+0e8TISPloGs9xvuKDUakGTVN"
    "y+xDm7SZLpOHrb0rbQkQib4M1mKe5S0vQRN1SfJVrNZChfK1j9j5aAVaE3c/K0OCO7o32y2SmIRJdkYLzqf9lOUn8Tmr6dpyRBAH"
    "ks3XofwpnLqA4MWoDQhDpVh7uWUm8MwKGUGlb9oQsNciJlyHJ5ZZiUK2q6wIIVigBt6zecwzVxh0SmgieMvluF7TFiA0mD7jxWzS"
    "FgugzQIQiqqEOCu8mvqDJqqt0LJTIr9XgnkhIjBoG9tPtgo6JFAFjiwVHg7GrrnmnoOQCKV4WHKjR6xkI4eKl3Y+apkHmRePAsy0"
    "tIzKhCy02z94K2KRKRdZaU+n0iENeSoCOU1wBDD9CpbT9qNC+/m9Se2MsNoZXe7lzqKybYjjWjXM20RyJm6dEVODG/RsTSg4IShk"
    "VAwDvZbfgKoJZBnqOMEAIG1XQB4nGdk5QT5Uh5xFk6XhaDaf+dlkhoLvlJmbkJOL8GKR+MMXcySdBgTyJb9mUOzkaMkp7ucUIARK"
    "VmQCXsFFg5wwOSCMab6tEqRJ+6HdbPgQ3Wy+k5/Inp2e8JaBMKQXAL8kZ3ivgbyshADGDdVmkzrZcZAhVTXE9/qybrS2J8oclI0c"
    "lLU5KCmLkhJJ4WFwYRmFs5pYdwln6WvJfa25r2KtYxgltF+EfQ0yYkPT1VntEw25R8NtvaVGcMZOmEC3B6x2widYcAioOMmB6yLu"
    "zIytkaiPmnKB0Zec2wJgts7ODw7ebazO5Djw8h4vvt6VsbvtUadP1+VZfZ7+jpllwRtqc9jzhw72NLjUcnoiNUifFntI+qynk2IP"
    "JZ91ki39nrU+FVR7Vich6bsylFMB06E6KxNpmfmdr1tG6gn1lMjKHozRX3STDinpVZB0KKXedu8D/+y+ftl9fd959Sf+t3xkmTsq"
    "ba6a5DAdJ/zCwpdxYpbzSK6CqA6TfaptQVN38MZ55sPj4VTP8tW8tQmHwRn3Y3hwmluY5CUWi8b/vFVftzTa4KLnp7C8Lfd9SxNH"
    "0xCU++Z+uUOilmg2aX6Cci8DOZLoJIglvLZInLVZQ1Meox5ui4CL3Gy8qfNzUH1NcTHXob2r2ZNFcNOZ28zc2FTRgpwyD40jlfXl"
    "O183vIxEv92CIESBY4K10ARLEFEDGtxr89yfXyTZ0cXJrqWSGZ6v4bs2tHncKcw7Iyj8y0cLWw7Il/057JrOWCNOepV0NH6CS0VX"
    "nycUiITjQz4J1X7CXoDpCEQATt66s1T9/kp3SmL3GUHkQ6aimaP8UThKpUuXZJhMv7PasjOwXSuwzui+D4qWJYNzMEWc4klIx0MT"
    "INSSJfoB5V9qIUH1SO7pvTqOdCe0P/JCFGcbRLP8XmSz1KgcNJJx7VIfBqmdSlgS84AL7lgSQbvB6AaE1YENMuV1lzC03VABmeca"
    "4tNfy+lPG4t4YdfXidyxWD13PxzdGUbZHYZ0z+q4h1cNH4K1MksxMNwDL0MuRHpiOKn0aUecQ618iHalIswxu0/YoC6QJwx9Y57/"
    "zzzXDxBN7nP0dafXVQiNf7QegiwqyUuBouYjUMREVtcKgtqi89jqs5l53LGKMCAX6rbfB7z/xJzi6At529VtPTj6iJ2FGEwIWd5p"
    "34gPe6b/rBiblt6aoaPpv0HDHfuExzH0Z4zNikXSxqaBsQYx6SHwd20ELOzbxf3Gqv+LZlBHRSzQJv6LvRIsidHVlxeWR3hAmJRG"
    "Om10XR/QkWc7AQogq1MNM1i2tFWwb6ZqYjYpboRiMoAyL+EMaFV2yIxpaXUmXYOz0qjWUptTkceWdmevSqtPRPQ7vYg+UQvJOfTX"
    "cJOrQwZ7ibpKyGWFsS8WCz0t4AQoJyJaL5NKVeVEJ41yFg7JXOWrS4i5v6sukpUCMZzMtmkhDnkq2gYGdVQs75ffw2yBpo7iBL+x"
    "WqhLNVLX6g7juEjFjlx2f3TJV18GCVAJuVdMZJOZXDZQv4PxL4sPsugCwH+H2eVL4PTpH9IJ+VjZOo0gfm1b87JrkXRSOn9o05eG"
    "rLgK0mbZLGJTYGjpUMcuU17nMptlaMRmJuzQib4dya0Fq+WNAq26X1mrThZuWg5pqRehUY0085k6uz5HU9f+QyrZbrdQo+73K7sR"
    "LmmZecYPs6NPD5NqKEPGdONEEL252xRWW+pUnE0tjPmcuu33bwfWWHMS3VqjKLUQjbCm3y9tO+WwTCPrbSborjauZWwnT1llkL/R"
    "6UUmjhCs5JTvP+bRvIyTeSkuijBTC6tET3t2MTB68+ZO2cH4QmxmWN2YgGuzoTLRRdbKyhv2ng8prVnInrB0QkPdyYyBZtuvSL9P"
    "i6J49iX3DIVpJuellSBdEIEEoZUknp0nmni586GGWROWqaRlImKlNHf0wTppJassqmum617KsCL6KDqh7cCb/msdXdJzYLU2Z4ia"
    "RycgYJITcTk1E4KGFkeNaDbEmklWVAZgsMBC5ohnbxYDmD43arQ7XigguaNvDAe7gLi1zPLsBDJPGqqd8WSeUU/k9po1tQQp05aW"
    "fHUqtsBUnn+l5ALpYiqHivghyAEEpqfqNLjRFvxGQGxvm57ApqHDQQh7EMFJg/XREJXu6uYwfpq23cuV0ntdaA8ORDofoyWDZdjr"
    "wl6HMDUciHjvIfWjR/wdu5kIP1py05jvWHf82SzMAUG4whXWzMasdzxgdOr1ebRGe+8ihYeH/Cq+50Jsacq8aJ47Z03WzRpuIMKm"
    "ts59kFuDq9JfxAR7vM60SJQZ9TlzkZEboa/hMqjB4k9DgwWVB7KSOybGioGplSbOVmtlG+DbcTXR8bZUsJ1Dx3mK7jhPkVMP3YHf"
    "FGnWtxv0eCRnIZ3IOEpyd55XRMqWg2v4JBMFxbWu66r+Ni+nOA4b0QP5sbzihOlzZL7AIk1XXHEy2cJAq8QN9Qn8Hd62A/Gotdmw"
    "KNhhttJY27JIagk6khjS8VXbLpvk00+vV/r3ZlDVl59y+we1nmkqPdGf/j+0/dpioQ8eruvtWEzHQvM5PeFmQOoSVeYcq8FOKWct"
    "f1gEG/wfhwZdhzBadvbL4oqmxCW9JrKliuU+36gUw+ZLuo8FasxNPa11o3jWjg7VGX92LpfyVhV5e415r1VFeZOASbsuvYOyQ6zJ"
    "EQNSYe32hqCnK4Jqng172X3HzhQv2Drvlp9PS/YHok5giXFTprQwi6KBjyr6Gv4Y1Dsp4Sms56Xnld4RjrlxWkGajhm48GPa0mry"
    "iFmohmqLq+KroIqL8hFotTs3k7JAT8qhu3Z4VD59+vSIRnkH2RsB39fgTQDLm00uJk2FNQTO2rR+dJSUae3NBTzja90UBBZuzi/Z"
    "10x6oSdnrjMHR+fDHo3Rlz+GaepTFCauiMoZqjGhR6MpR4MjPIpLNuXtytSHsqOVjtc1Zi+9KWXOXpTB8j5zHeW9fFpCBlFMxajx"
    "1DV1grlDS4kbDuH9W9eroAO7ZxtDrw6h130GsmDI/fU3dR7csF6yCwjx+1WrrSuwUlbJ7KnSTRvbQyChmEIHaLAqprS7nJY6RF7I"
    "47MJjk+LkghOP6s1Uce4xM3qg6PkolSlN1eMysAcXeGodZks0w9s1cPbM8uZiIuIWzsSSwXdYrCHTHjDmVSAR+E0q3jiPmCXWWtB"
    "sLflWXE+jPJB4QyFMrn9zeOkR8lwhlRg7E8IfKg0Tdt5mifG9iw3FC+hbSj6GFUbHZ8T9Va3lnpjQD34GmDGNIzrSVrTfg5NxA+H"
    "+knhfHdQN0/NGuP20+EYlCc8UDASGJ6UT07d0E6chzednpZnJ+X5MLATDQxDj72p42MiQ6LQ8vF4G2IZsS55A47Q45QfjMyJRvOG"
    "RhAgQIOl/XQaotNOzi2IDGoOFYrpHMGqM69Tr91LqQLym5uXnnxdirNX7C52jeR2ekaQBmYBeb6rL3hrWiOiC0zZRRlshItgymgn"
    "XGDKQpPax4HB6f1J5NOfGsT/7OifydHnfiY/75jiHkNOZMfD2/FvdKPz/VYOAvcNnQCvGQcalK8il7XZ+P3R7/MUyOy9MkXf7p4S"
    "fwYo/pU7IV6B5qeyYlcDUmw04vP1BSEDrijA1s+Y0n1VGkK31zJ9W3Yl1HUqOnFEEdWDEZ3aH/Lo4Miq2/3JuDhP3+Wm96piGKlS"
    "LZ91ZlBmy5Ud6qf5UB8cxF/lBI9/4sxRro0jRxhWW38tN2L3SvQ7Mb9T/g28CpRygUjjeQUdK3bQujOgpqK8mIUhxOQ1cLV2Puxu"
    "6jLc1Jjls5xIhEZN0hbuHvX5EIpUQCjQtUzXhqZJcrUS57JJvhWnabDoW0C/SRlacE1tUrmibNocwg3rt7RS1XzKoszEa4kTfbeo"
    "psWs0HVDlFy8j1p+X95TW2K9aMgpL7yD3DExBiPuZ+B8MigkXnHHjm6jY9iUH4o522hO+U3L7lpMRaX3QMk1OZ+5zv7OfDT0bbt6"
    "LBJhBalW2dacObG9XcEa4Y4THcKzW6oJLdXkiYOmid2Q8zQ/m5wPq2w+sFOaVpRi5Lqdnvb7vlBwVkbztInWW0Xk9s6qeC3eOXqD"
    "k5jY6IjJTSLzV7QOj4nUHOg5fVyo1tCbIW3yrUfGL3M73y9z0NzXxVQ3dC7izXjbcY8uf+idLgRf7aix19DihSPGNryYuyctTP/I"
    "I+t88VlhAehZkT0raJMZfsE2keD62bjk4Z212dSDCZEMwp8ELAYu/3fTgmp2R2QVF8WGz/idtUwSdhuu1qx6q3PE6nQp4dG6hYGZ"
    "XOSjceZfQBMzFv2ptEpLgJ3x9UEzuR3H6puS5RY0Kz+VgdrUy3JHbeoPx2H6K7h/L7qczWm7JxMRYc4holwJUBWsEiU+I6EHB13d"
    "ZQVzpBkG+jBn0Jik7Oy7nDg7hW8gd5phB41uwKZqwwUKBnM7sTe1H4hPd2+3wNIOOC8wAhE8isyEnoQyWhJIDVc8kam78mBueimC"
    "ARRagLbg/nG3s1UgM2KrTiLPlmqS46t+H2avzVKXDVTnebA8KgjZgLzDj62b9zaDD0jmJgiNrgZe5Mv1l6FLCTrAF+H7MdqMmN5Y"
    "ghBU3BvagNz1q9QInVeOC38IVD7LZoKer+JkCnii7XMV3JeWXS10Y6cPHrkQf9FwYWXstMaDcZz9UrJGCYthawLhxLBrNRQc8yED"
    "bA5fluJdlLl53IVZZ5w/5+YGoUkJ1go6S+TzOFAxr6LOtfAvZagc0dooAAPn+tcJ6XAE7D/wCMmKm70UPo71ub+ukp30c/eC4NfS"
    "WSaPrlkF6V+G3INS+zs914i0oB5KIq+L8eY7BbFhn9nhLhFidVAM8gUugwdToK0Dp/en7795PteAC3jHFrQhZ2onU5XhR6/z9ur1"
    "K5MVGsbsfN8pp+p6NwIB01eVnZxLMKtthqsPFtIkJe3yOl0j4EQyttMwVuGkwJU5QdBEN01o9SJkhpoLWllMkpVaTpKpWl5Mkpmq"
    "kjV1UtPXS/XHStd3pxr3hFWdLJQg/neEaZMr83JSLdD/5FIJwn0DKdJou03n6jp9WLKngWoJzaTpHfW1mJxcFfMplUzutnQkX3gU"
    "QHu6ucqX+mvaZP2jLyA4hld5KS16w7bv8VbdQokpmK6HZaRtU7iLagmZ6zata5sMaXKezmtW+rlSS/FzXTGyuL6kxWlhv51V8ppw"
    "xoKWaDGnvLJmteaocmnssKUYFM3Jc3bcMiF4bM28v+O2G1a03pNuDTDimHXVsN8g4GchERTXarnOh6HtaeAz3t62/FwGvndjk+Ld"
    "6AYTYWmkUQRiAWqIwwuebjozy8lVVdvGiBS6lVu/nwM5MmHXFjpHQ3G8y3Su8zSh5+kVew6g88nUJglDERUzsaiW0P/EA/TKTa+I"
    "f4bHYELX06K8/LLGx/H61Ctcbq9pRi8i0RRHD1v0MFa3kdCCa24dQ3I+BkwH7LjoGHSzhP6s4vXK+xDrTFfYbmug5hTe3B0M8dtQ"
    "Ti5bwmWqK5f2zPYhfFWXHcgcpZdZSRvrgn7r5Mqq7DDIbTYEgUsPgZJjwI3WDpm7MHiXReyioru11J0a2c1CR1fOa44pTCabDdtM"
    "U/6F204Ea+o6vszMAgHvmAeTQmiI5T32xTgQkZcgPU7yOhI0M1dH/jIgau9XGFONkd5pEenOIZiDGNq5zPj6yVfcjha561zRyIQ0"
    "uSTAQs6SNjj3gIHnGvc9cO1+bb0xr1cLYooI00lqUlABIZPXDgUReWWRD7FIAldEagUwkcxVuNSERuUVqBT9xqUxkScAgBluwECM"
    "Uc+6oHkFJm8/bBINB9QSzWmTEQizo4cimsSqh4+WtJQEDhUcfHUP2maXsyRyG45shzXtRgx/oXq9YhdoMEk8GXmtru6m0CxOqjrQ"
    "A8hrO3v+iKjpG5o9QqzH8RpyXInRE0wSUcrdBMb2yieafcKp5c7uEUVzPae1MAvQKL9AE79AczPjK8z4NEVPjjG7UzRfSeW9n0vj"
    "zhz3AkQc0LqssKMm96dwHk4hrQDNHg/9OB5ylc0OrW41XswBixli1yzFxZxwHHU/OBybnWN1osxkzsPzdUXLQVS2V4oQoYMgvMB7"
    "nvgWqwfghN7dsZvbx5I6IGYbEzG2x88DjlLxQGZyHHexXe0Z9vsf2k/WO7gO1P1ovsx3cCBBZdTuLKS41t3WaRXVHQUNo3BmUfg0"
    "qlilStTWrZ3uVniCNjjWLXKg/XAVEhpY9oVM1CRdcPc2m8VgRmx9y7A+bHfojOgqi6Qbij5Fhd3ObzZENSyoSytCKo0cvItM7srg"
    "ScX1nXv+b6uAYcgEU4RStBftGGNz1l0ZZAZCebenpps7B9VOY9yPIBZHHiyKOfdFcatOizrQ86lD2p5Ir/bW3QCsWq/6w55/M1b4"
    "0XMWcZlKRQko3OrFvf0MWIVdxzDugOwRQJgIj2dtWxcXK0J/YwDhwfVBdVPCKUgJPguUnXGiJxtriJ51LmXmwUYMKBYPoTJlpTg9"
    "2j27OdlOXH72a3meVqxfVUc5HTcQHhI20WzrUfEcrmrPncx1fq1PLmA4EaTSttc1UgMFJ68Vvy4aE04KkYaK5hXVAYzBL+Yi07zP"
    "Jes9kEiTGK0Ax3q/r6NIiGhXI9ymxeqnIMNXKHmif7is07OvTd8Uq7Gcq0UNiSNhKxOoK18uYffxJWLM5aVaQrmsQa9tSlVKkKvn"
    "GG6ypNO1DB6fzehxN+sEjNCceDNJk+8xAVoSgkf+fjdr7/fPpKPyVfiMGu5nhnVs1ZVjqL7MG/2OSNOmkNBpcrwsamhdrrAL1828"
    "apuk3doNAykXwefMWzJEXiuT3TRAl73fP6kj9xaxeol4mLKXPNklHdOwHWpWF+9qrbMvozgQXvXy0MNdZew4ZK2abcrGrvXAAZIV"
    "YF0QBFvD+Ft+Rl2T+9nz9K6OJkQX1pACTFjCTxv2hGiPU2TMrWzSdbDfpwrdm9DbxLyFX/Ze59GKsGK/fxMWdZcbNeWaFunrU7yy"
    "PwbEnFu1BwV456ArzjbajxNiHkJEDkwct9Qpc6RwQ/l7deEuckTzyqiD+YvOQLjVKQ9LLhG/w5UYxD6lEhkSo+wgU6i4B2GfiCsx"
    "Al4l880DLMoDGmN3gBk70M7vzFAchyzAdA0edkVTdWYM6FfsivM8pVk7W9Xn0m8Al7waKbjp0Vyq1tPdPnUzzOCj+N99t03cI88B"
    "rb3V6HTOPEJ10ss60Ms/OzwfBhGPngbesSXOJCtkBCu/JtztaAkrNgISGxH7GRxm1/4wW+8gTpCIhOolZA1XHYaNoTNsT/w9JWyx"
    "FId+TXghdFd3bkfWBlcWijdlHiDLCiDYxZSNQ5STLp6c30eTqx0sOfNIsosjF/dR5NUuhrz0CHK0gx+v96BHI62xLhsY4tQtYJHj"
    "tpw66RXhg0tRePlfdmqk9Y5gqz07Oh+emmiYItc0/sQg1BNAeJLCjQZU8oIUTtiqE3MydSZWXfg5tdadddowliv9kWg0bOr0crNp"
    "hOK1vD+2ClFc+OG4BUYb4Ozi3Dg1eJ2zOaL3hKPnKDyUoGYGom94Y2u5SpICW0jyqOOntGuhl8He16SXuPmnBqD/EmL1Op1AVEX0"
    "yeqjAxhtNih0TZQllbvbbFad4YjlT+9o2J5NCQVAigR5VAM8SXOfVTR96Iw66WxrOp4671Cs5QrsjRn3b5pyYqgoSbx2nWnNQ1TT"
    "cygtw70X19H6a8MO+LBiBirCtE9l2lXZIVMcpqdD9TSacZfNyvDYgN5KGhuR+FHO97TQ0ozK7Ir2AI+vDVHg7VlxLspGBqkhwQyK"
    "iEEU3RkUf0FMPMa2xNgqGluFsU3mVelMToo0QALesmr3PDoJUjDV/g01FvuR/kmQnIUvNkZZGXzcwd7/bm3pK6+pe+IR2kVtVJfe"
    "1KEGefoqF4Uky3aL3kBwT3xbOw+94Zf/ggSMEa0E9pWvQej4N1hCiX/larGkmS1br7nukizlMOxKalovCCiNn2ajWAvO3l7hmbOm"
    "7X92jNuX0hJhrpulJ8sCjuK0dlepoYD6Cx6K6+saPkYtuZi2zov5/a5TfTQfpZ0P0E6QzAJXOuXZkO07fhzEijS3XIFSJRx6F823"
    "LLChDZOVXcEq0ZGi9iivkKPJgAYWfk2zVHlzIsGqOyOx5Xw2IKBpvs7ncwRJ/Fhhmx+OKiyqBCJoN76h3RgCgh3uqyKU/2Mzltx5"
    "nqogimHtrEUs2j+Dk5DDv1KaNXqvrDHbEAYRtaEKaMnGPyvjR+aJk02RPKkEd1Wu+xkVWOKy1K4X0fKPHjGrajxxUher8CajiVls"
    "AK+unrLhK2VcDza2Nwntt0qt0acGehnA/EQhdSVVdSipqiVclelLenC8J+rjTe08G9/bajd1tAdkRcvejdcedZ1F6/fvL5cztLyp"
    "OSSbEImurg4pHyCRd13/oGx60kTCl+kBfraI2cuMWKK3HQvO556zZq0Dp9Ua6fvayYNi+kOtZ8XtZjO+HsePxgfjR7jUbQhTmIej"
    "80ePkjBQ51c8e5yZnu0UPqbCqEQdqsPzQGM1lKu4MA5RVKZ7ld6/MrHnjCkm7PfKQRigWIQ3H+r95tnPaqPknavKqhSLMrne9RAh"
    "Rft9yi/jDGrPCSSz+NKJj7Bcr2tWQoKL5TzATP88OsY9jlEBy3Hj/lZUjqdIvwdGPqXf973cB24dGiZs8vOsqaLgkzjJWQsmrTK+"
    "E23UuiCqmDh8EPkL0Uqv1SidDWih2R15Zh7X20Se1DXlMjCdtojlegeW+hphy6+5fJEgLiMt4kixtW90B3r31gWrhpU35xpVzkWP"
    "t2+/Tw/pkuf/d+B4dRkt4nh0tjiXY/OCXmnur21C4AC+RElnjXQbLQhZfojZZMhYcDJPQomUNiIw/GCq4MAvV7gnuiqJXJmpo2N1"
    "Nlej88CrNYJPLyFqp2aWQoPR8WPJGMs2E7C4W/7sAtdS12fL82SEP7f0utn0qNlsaRSepBN8nRVP2SPVhD1aBBYnhNhLr8DQsFMU"
    "wXfByGM0kJ415wpt8vTQOxI7I6ACNC1LOy1L6wpyZ05wTnDVbRZxxfNOtRDeAvz31LQ7u/NYrkHncecylojND7W/sNkOW+iEHBwh"
    "tXuNWptz8PeaXYREHT3m3wOW+EPt3KrzlZe7GQobircIy0Xg+8dKN+2L6ZwYPTluFWdMmG0L04fAGa9riTGqO5v2VZVPda3eiGaE"
    "zSqal1ovn82JdAh0fA0qe1Gz966xCl0ifN3JnO7kvjD0cWr10WrRMppO4I/Ea42U3rqDYyEUzVfiWyAPgjsEphjOOE8W6G3NPiJx"
    "l+TpIylqAgPyZaMkxG9YO0AUxViXDOcYpCsg5EHqpjY7WK1X9a4y5Fu5jayNMI9ex6vFWGFUk4gdyhasU5M7i2Rf21s/LxKpPjAF"
    "LFgPFArw0LKDiSvk2DRp+gqTxoZKNHE/W2eRBVR6SpS6LPkeVofciPUVmXtl16wYWG+7eZwUVoOdivAZ8yeDRGRWjVqCHhP7fWyW"
    "482Guy4WgelT468Xt2Lqyzr9k+bgYjGO1Xt5xuO3JnlFzz/KMx5/ssko841Jx/NLeaa2YvWHPNftJb18Z18moVT9FyEEAV9YAT0x"
    "bpVZp6hOx+7UaMbqV3qfFrVm0rgZ+0r+1SU+yiL6GfoisDuHbZ64dah3VP3Kaacjuggs51lzy1VzhEoSvdk8DCiyNixPRX9lV67e"
    "mUNhNSoPDYTIWr8qN5uXOSs0WlRd8O41+hrpz9YrYzqpIiHJxIBDwiiLp7Ub9k+Fp0pHNxKQ2HbF6MfWBRsbEMLma1AqjpSAnpJk"
    "S9oQjMBhTR5smbro+vBFF2hbULtnaJIfbPPnoc3Kzk4jyMaRDguiyjmfrDabS2ctV6ZVv88GzjxX4rEWSJ7efjFeftnjA+3tlVhO"
    "F+mO6a5jHEr2aesYh/JJNYRKfnFW0tkS1VmTmTgDlBCz039+SvDXW/VB2wXJjhEKnCaX7HJxbHhmfiGM94JmVWKj0MQ8OYzZBJCP"
    "P9fXTiepZzrsGZtj3WvetX9tvVjre5EI4iKM9E67W4tDCqbWdioMTuQy7UZIH9p+lvfmtOY59TZHNKe1Z8jE7AjemTCX1TnfCnCD"
    "9bkzMubp8Iq5EXtzKmA46QCnMADXnaTWraRtsYYOItMt0MOKu6ZVdWhapc+AyJn9OGcXwINZaSRuDM21zcIcZBYr2lgpiGbGSYGT"
    "q4inSz6IVbtNUGqf9v3rrstqnA9ZBlcKr4gxIFzyqnSa3ESquzecZfaZyjm5paVPy4CtZaXhUnjNHP6XaVfsDXr/1En1Yff1iRGY"
    "fMJaH5gA0GA/0CHzInoj2jlnbwmDzyt2aIbL34h2uCqyg+Pki8/jrWXD2/Mh7dtqMJpAwYltLo7sdZU35vjBnHNzNgARLEif5UVU"
    "sc9T4uTR3c0m32z4Ro1ehvMUfeGRwcy/NyKCM2uS8ejhut0S1xf14GQwG49mF2Ni9SAUwy1AhkiXOHIL9h2EO+rsi88T2Nw4s+D9"
    "BicTb3DiIjAaC5XdMR7a5UYf5gNjRgPbgAHm7FTeidN0ecRfNmPq1dyDRx4eH949RO/3nBFIz7PuJzm0Xb3YpZcXHcFLbJQaAr2W"
    "ouNKcjvcMegmprHf//Ts2cGv558OYHIBFcpxVSZsqJs0MBI4T2GI7TasqB4UTGxm/8qZu4fCQtIUjhgTFVc1KdJdP53C+awfJuym"
    "9KGe84MxBCBW8CHUBiQNT+qhXNxyguiLPMzbtjYp/KgeylUup/CjegjGUBKYRXwo3UJK2EsqV1U+FS+UdlU1rXw7QQ8XhXnDk3pY"
    "cVR5rnxUsL4mTenEmMZIwZmliHGzaG4UCSwfQvHhXTH5IKVgePq8FHG1NsYI6iFr7aPAdzYL6u3zIjWYnN3PSNRG+EJiScMpmF9W"
    "twXdvCrEZeh6lOitsXMq97nDlkjt60l7m5hrcWagk0LxGuTmzrxS+QQayCeI8wxjcgK/ZKI89QDDBZFonh2eg7h86MwRGoOcvd1M"
    "3HU89+AocTYcVJSTjhOnwGGTPrdJtUv6zCZVlOSOxnnRdViK8/RIcd22SC4zuIry3YLHKg8LrqJqt8RnqgpL1Laqerfg56p2BWeI"
    "DMmpxmJpmk7QI2Lvl3xyhQ6/xwLeY/YRagFc/LZC48XSTNEsnRAETJrmdQW7CA7bPEtnfK5b9yzDv9NFaPumcytREx9LPhiFWhFv"
    "7T9cYq7ZBaeBLntlyhBThFCUKwBWBdCwEUMKnvIswiynzGwlhe1ewTmFz1k5vW8Wr4tvEwItnHsSw/woLth/3FESVe47cQ9LvZMu"
    "6bBLZQeSa+5gEQKyB3kG8ma7VRNjL+blfvXZBPSudHziQF7234T6SuMs+QEAJL+F+Z3Yh/yjE458mJbtru6cmo3hODSIFnK3Y4TE"
    "d+KGIoADSnGrOY69dyj5wLgUYVycECYZBPNCRzlReN5D957mQm2AaXh4mdtgE2rHCNiYUzA3TYT5Wd7LgbXgxSKI51J4GYog1jLV"
    "zn5GtNnwCWIay13xCZ8o/f5VEXWTiFIZX4Cjc5BJwGgC/NHaLnR7VU0bQmWCbCfK2Jglc1WUOKzgNIprmiYzFdhHJktlrTgXKjSJ"
    "TC6dUedIOWlHckfL5d8uzCdf0TFbV3fJra1CbkuTUyrNOVRWa7WyXjCSE0Wn1VTXCQ1Nnt7BlRjllD6BHddRUk3Dh7+Jk3xJa0IJ"
    "N7QF6mtdQ1SuMd6CStwuq4b2qKYBX+m6YL09gnutPJNNh7/yLHZCZ6FEhGiSud6mrVETWhTRCh7C+Fhv/N0GyIvGricrL1+xI3bm"
    "RNPW3NLKpUhuy+XWE3AZD6+luJAB6Y8cJwCFGWxU1W2psjVUYGXz9NuIHfIZkz9pCzetlIAtgkT6CTL4AEx60scriXOIUo0rRWW2"
    "8XBfzJ472t5arbVzYwOznVDgj3f2D0i7ITd7D81p95rqLQ9u0h3WJL4sogmGVLA8K5Bg6vSKHrO5mbE4mQ/ve6V3FwYtESPfQqTE"
    "jiWorRlvmxl2Skf0sTLhqaYyc8H3iHptFy1O4Bk16q4iffplrZZEgOjofQ1rHXr4tlaX/PBjrUb88EOt7vjh61pd8MMvtbrhh+8Q"
    "dpmf/qgJrvnpp1qd8sM3tTrhh5fERsEde5TbWE664zYCth0C31OisIjkzbvejvYvIeR/a7tILCfBCrXyjNvOcHW3LtRjt6lty9JJ"
    "2ZJ0XDFnaV9bxODRlnmD9WGw9dIKkg0xa/NbMG3Ym6WxibNbMZ1AAk2pfJcVuKWycqYa68da8jo9LViX2CtlMdlvBbigQgpi9q+Z"
    "7DfM4Jg9Fv9YRjVLEXC3XdubdT6awyx5ixW7qsw+Nrfl390eRXd7FH57JGD009Ad0lVhj7/LMjJHjw0fafzeGLI6TnYSdrT/L4td"
    "iXB931QTuQY6RGkoFFq1guFwcfKyZGLGkaTsWIoTtdsvw3uinOk9t1xBpwJJDYy0tDUGxYjNo8NS1BObhh7VtkcskwydSQXnrfCU"
    "ar0obosS7sdNCAu4IG9dcqEM7yP0U24WMVlL8mtdX+rTFnYnl0TIIMJKGl7aKlwFss4ewbSP5zRJm6RXONNSWDv3akoleJhARuKz"
    "inB2rgkx0patxLKM31pceyo5N3JR94MifxgoqvAem0zcdzc2O+QcZ1ve73NZolf5TqAIW2+5dakIrXunNNhcbcy+jWjrs3twQQ/j"
    "2G65u+KsgCQWUtCCGASoJ0FWgQfVQpspwV8vRWKfUcTSMR1zURgK9R11mNhRfrD0zE3hqRx6Dimi5KRwFM1J0SFpTgpH07gcQ9TQ"
    "u6VqXJYlXnxZQ71Qgidf8GUZVOuJIC7Wee1SKyfFLrlyUoRECQ0sIEroTWi454Uj4miODBV3WwSE6kVXhN1mOnPxOnzkF96tmQ7j"
    "konvLBW6Dwgy2nibtKEGw223nZsiYhSs6C8oGK+WVBg1Du8prg0FNEYsHEo8aWsTDjxntO1tru/LG092pPVZ6Mno7NxqtbB2wnno"
    "E+xm98P90huUCT97t/uZnD5MQ3SahgSVo2kiqMr+upmfwN82y9bwXRq087xwmlw9q2/5oJV4S10HLuVH5E467grA2phlz5gw9jUI"
    "KbUXdHmlkcKBCJSDjXDLYL+ieZMDGt/ll4RG6MSjFhbstoV4lV32LiGMth9dUkbHa58R1t/kdbmThN1Q0Pv3RhK1huGfoLGz83Cv"
    "UJXBXqE350tj39x0kHtowM8Y534y4597yXLx+D2rbzlHa134cNuO44izic+VDeAhcmyoZ1tCqXctltumqLknxYrgMsk0TNClKqiN"
    "TcAgzlO+3ErXo1UxTb6HMtfITQudbiPBobVi7yU5kSq1LKn1ZkLrOHLOdzjHOGNOZhVHsZG193ijMOw8y0ZsLm3vrVo192LO5saK"
    "Ea6kwGyAEqS2aHBZlA8kFotyidFcvgbzwjSdL+KyIE4WEAiY8WIgQOEpGTTpUq17uvnWg8wOhoT1u4MmIYPnuGXuJAYwdv9zD37B"
    "553ErZw+kdg6r8WoZW2954wmmrX+N5u3UaiZuwroirRgQ5PeYdYYw2t+PeKQlTbaSNXvw/fCSiGoKX5gWM0OouYDDwVprnJ4b13p"
    "EdU/GqVz1VTRKtBXoq1WlebIw1xXzmW1PfAIKHA/QCRphbotGKmjL7BiYvAcNBmYZ/jEsA+x27ad6S2cYxwzs1tVr8qfivbKTIun"
    "7p4Vw2dFOh92XCF7r1uUh6hWTkonO/iZWN+p3wurKNWKTyTqLvs6grm7SzkQQRMIcLy+dv6o9NkY1zQuYcxXxZSGq+I9ybneSfdY"
    "5HXBl5gSlow1nAJPoaH2PaRFcp/A+5z6SZii5ktLNqBtMEvRWEibZMxxY/v931lybESL/0NUHcc8RUSABfvvqi1vYVy5ICPiaOyq"
    "Gcg1MJfLudwUvpzl/gvo6IyoXFp8XJSb5xuwAefD3hwW4PAlZdJzzRm0L9kMY06H7RcqtzZbVOjR+HsCp/G5cYvAZyFfTWAW3BMo"
    "Ca+3axIhQTTzFKZhF7BbKmnKOAcs9qsn/lDccw9VZm+KpB348wBRmAML+cIL/13MS1FMkF7Acxdhyonxsd7znnhr5z2jTE3DsOzA"
    "nTHv3UYk9NshuIbWYjbnpcYmuMhBQKuGzhezdvOCdCkL9v3eV1uvGNGbZMyzGXPXyAhRjSg1QuCqLA/5FAik5ORK0NscDEr4eUW4"
    "KdTB6hyVPUJ8vRxkFITcUJoS8DxGECbefQwLWUvTX+vlPKe8T5H08FO+LeC4i2eH54O2elXdwBKJICx+1DoBOsuiic3REoVT4jSG"
    "Sl+WSVyzQLxVxsmwYjaaTtAb2kocTyIxnIklSlgxm6/lGiUXdhOmGJK5FWauzIOQEM7lglw+LUO5/YIl9VddWeUlNERHKfs4hJt+"
    "Rm/iR9urm1pZWbHZ1IhbNbxO3+bRysXHUlM1Uwu4m4jhrH+ydXy2Ji6QC3vTtkxHM7W2g7GDk0FBqk25YlFONRlj9mySvIXHh625"
    "c6aVdTfN6aEasUgOXlWpqejEmMlfpNfYB3eEAHqp22e6c59/F6vQfmKbXgy1B/z+/wAVAZb5MrkC2XCX/llEdxxI7QKGIBfqTkmo"
    "KaeyULLvPPhukQLGiIY54AvOS+Unkx/LSMh3MHnlX8Ki3lCANf7/VUYXgb3EBYHaRacUJuBC0VqO6CnQ1CvENODQKl//hetcJ9KS"
    "iN+/59AHEQNSp6zOvuis7QvtnuuDYjY2CnsGMcJp8TY0xOpce78tvD+fXZmaXLJyJBV4e2GvMO3dHAcllPqwBtDUJVQXQ5LFmkae"
    "i1N/Fjtmdvcv6yumhGuze/8X118tKxfWckUfsC4eYX9ZBG7J1pbydfY2AXMN0YdWa3sFFjhPcRYJ8BROtAZs54C4zWZnHWTjJzM0"
    "PvH3zOKGYPLUOPqd9I8Ojz/vZE8CS586e19E8Lc9R5iqSrIfe9dFxvEJuKrm34JE6UDi2yISG2VC44Rn5/5eE8FVw0WPCF/wjWqP"
    "RtRrBg+JboDiftY7ZNeQFfBxnfWqzabbU1NdEOfpfdH1ChduYokVbLWUeul+jR0/TV3nx/Ue38c1ZEo4Qxmr0zajMQPD5GbMpQ/V"
    "SWO+39tvd3orAmLRsQovqQWwEWwZEHkN0W/vOYwHizhh9xCBP8kiWsupoY0TFTpGrB0UnKDVxpN16A/e2loJPjeF+ebXPHeMosQi"
    "MCjp1EmI5KM/teJIySWbacLrmNEVljyviywUkxgniz/8fY24uo0Xjp8KUC/fiOp9l7H+qYjVS0YZfxGr+6fCb9Y/7gkoH3DtefoN"
    "MbxDQ9F+JbL4Zq+h8y9SBTTN/N5g/DEID2gEuOVkKEsVuKE1JJpthMi6OiuSnxAdNjFa5XKmFUmujGZCmgf+D7tCdINHCnP654Z0"
    "WHtcwgJiIr4lmjAI0W4XCc8IRQjHo9XTQ8BwxO6SGIlU/cCwThZlL2KQ8Bj3naRbZcVZBKKrg9AgSHb+z63BbMVlJ9w2lEeoDLyo"
    "55SB05Z+0im6fNixdLih03fI8/szZNTwOzQVRWKDcT5Sh0FI62A5mU2wls21t46Tq1YoJK7Y3xvbwBNJR1sddUMxAfYLSJ9kom+Z"
    "nzuaHLoVtX+VK9rcdTe3WqNaHJAZbhVFJJohfblz7ZvHrbTJIg7zQY4rNRnZXOKDWt2Wxui2BE4qCxvnwvlVvgcb0AtWEjUi7oC5"
    "MRxlirazhoQMoMk/Heai/DNl1emYsXiv8lKSaZzVZ9PzdJ5EE3Nc89t9KIEmteyhfn+OyMGsEi27aY4eHvLFaBVE1kXk8nSCsBrd"
    "c6u6d24RU8qR4M4aXgvcRDSqgGUNrQQ0Sho4DLZy6yC6YtHVNrUamqLqU/U6bgChoeKu/ax2ee0cvdtilb3+k6jPhp6yLmdgWTaA"
    "YtnXOfxh3bFMKw6QgMVXIDAKXjIBE4JSqyS1dh5NC6JiOD01UnhxSU5sUmS3TA11s8GEQ07APWPDWHXJEqJtRZhNqN+ezoBGk+rs"
    "6JwFiHAQSiQg/QqXLVrlAQFcM0L/9SOs778K9opQONScp0X2a5HUAy8hJVY2D1jfypI0ldGFtTpNc2D1GSSWy/tsL0edXC9TUdA7"
    "o8U8T03j2P5NxPNB82780YoX9SHrwe4ywfUuO9t2mOD2bzLBLUNyb0KzurRjEkY293GQS9HDnsQ7Jq6Te/7sStp7E45/8LDgS9No"
    "zprv/tb0niaEw6cysw/5OsVUxioSdTrHxpuyKBkC5UyY1nKbGKkyyyX4pjNnPx6pkJ5Tgrn4IwEbHj1yYjQorhANISoiLStLD61q"
    "pXGiNIYPParUkBDIERPkMbt9BNLn8eVUi8QSYpXroALa74fnaa5qgtm0UlEOprwO9mjsVr01gSoW6dlczRx91l2VRawWHjc87Gga"
    "B6prPTF/A/TrnDV7WWF0LIYl4xHx3/bZ0MJj1XLB4N79bR4nZ+CYY5qnPHCAwOyBDxrQGh8ZzyJne5RHxvwodF0sLvyPVE00Yr7j"
    "RIeNz1glbEexASiM2a0O7i8cAsTEx6xKUOYI0QyhsoW5ooscW0ZGXJZD89GRrIp81xkKxDNDo3ds0SSXJ9I2D7u9c/GE0GA9zVyq"
    "2B8Q+LORhKr2DZbrFyqQRXpC8HhRx2fHnj8aDXUW5XlknTJyiFsCotHYnuJ1aNJIp3WRS1BZ1XDbPiCpId0LI+5gDrFi0ZtogBV7"
    "u1ByF2rCI6x2D8hPqD+5Eh0Kei8tT0VLK1wJlP+NEyaQILmglCZd2yDSR1uDUneIDUwiQJ4F4ebSKCA6tmqSp7e5R+PzPNgEq7yj"
    "QoNXQ3XQJoUp5hAXAu9/fD4aGXRsPWdWxiOpZY9xAsGjJdPixin0jkfIHY/LU8i4OGeGJ/MNJyxDf5MLFbqivEJZY1iQXBL/Iv2B"
    "pKyYGA8PyQjrdC1gZB3p4boMP5X8uPCrE3kn2qzX3vMpaoyJ2VOxFR2LOzATYbdIT9kNL9/+5KKPoayBcxv4MkjTg2OhYKHBudOO"
    "K7+TThCEw+h+6m4SrtQg+GSrnN3KJRLC/XSJOfqRmiylLYcIhJUzrJiTuc2gJ2KU2VdGmf00T+7snBuPmaKsfpInF3szbvJEZ9kt"
    "27yCpAvz3iSNth8FTr9NEbstZv2j7GRPMcr4IpvsqyCJKOvzzWbGvkng6S30Md4pq25od0ztVWyePaujqTI6bjMqBBtE1WuJLbA7"
    "z2bab+AogAsL7AkC2qq7NIx8HPinho9L4q2JffB2LeKUJzBW8/6jfSl2cDxxEIKQl0EVhLovOk1q66RD2psG7W02kJ0zqnINbY3D"
    "APu5RO+wnjPP2UN3x9U5PKsGJdgVeARPuNp6wm23ncDP3roZmuXDuOCYrUT1Gk/cmkjnKjJhntkp105t7kzaramUmhoxmiyHEDzB"
    "C9d9l/LusDYmRnyd6vxZ+2S4rx7veLK2C1jqaLfWcOkwKwARjbvR5v1KnzyH/7A5X7OzDJ8lL6MLfVmUP7DQHMqOlgm27uPt5aUU"
    "JvLVFMUZXeru0Bq1snMDcb8RTCyCvXylvNAyucSFdsMolKlD7nI6N1ZYVN+i318MCvZHf9V/nC2xJQI3SFfs6fUmBIipQD+6MxUn"
    "ZNwpNer3OTKPyR0bFS2azVqjVjjqEUxP5QkGFoHJGg6/RczG3HL5aqk4uG6YWt/aC9aHxvYxpfCVlDAJppzRu6SeRTMO2foeB/+X"
    "XlGM6n2fRzPRI9zteCeGEFNc1+mSyCd1GQ+vs8tB6NxtGieX1NfLgfP+Bg8mZxc5LiIB8FMhW2DjwlNt+mIdqG0215vNCMPMxTEq"
    "xwELeqeu+/3LgTaN3ZtkF4DIARHouhgexgO4MVuB4OtSKJH6r4xLUaZm32Zda+5AjonrOkItd7l3HQWJpXXKJAbdZeB4ic9cx3wI"
    "wUekMXexdXDRdgwNEUBKTNuwEW72bPH0MKRF5+lkOPdC87nlz4hRPZufp032J4ErPcXJW/MwvBaGfNKtGAi20KmV25hEs+uMGJYR"
    "YiD/W6ndiBJT2Xp0tJbD1YZ9Nzi3TF+YsDLBrf6VBCGVl8uheNKege6FR/zoMr3qwrGoNQogX+ImAMAyY/BgVwtqJ8yVctUdiiv3"
    "3j26g6OP7BAQTpw/9eHaolV6KDKrqaF1IsIhZanrb9+9ftXvX/kXGzZpMYAahwEPlAheDa7t95fRXOzCslzviSMwVQ7rgMhWVZzQ"
    "ZL3jZZp3kJJk88StnsotzQqi1gpaRgt1xaEtvGlc/xg7ky+7aKBX8gS8Qt2RKzCp3eSg8hUi7XEBuT1AGGk8UBn55TKPPQ/x/+Ga"
    "h0jdBa4sqvQK/B5HBynMZZyzhUIfwPlVjBi32xWieeuQkCgDQgIzXAaEBKagR0N1FE93hqIQ7ASQgLJmAb66/AsANPq2bMVM//Od"
    "o6wKN29DU9F4m/gm3LwNhK0tflbphPYdIc0c/sqnKSKRTZwNMfGgRMuDKtxsJqHXuv99HGcLImyTknY8KMHgDDNkPnShwi1vUSZN"
    "oGjo4Kndlc72WDQLUT4n1LwgPEasnzAqIJI7n9UfE+pWbMoP3pFN0CGM7vfb8FCUyhtebZpSfwzWkueOQXMC1u4k3EKbb5eUwFRZ"
    "YsLQoUK/rNgj+SyIZZJZ4s/kBahveQ/1LVSIx5MrcBdXrOcyySb2ov2KqAtHaWURjkqmDSuoHuDhpkPGnsGJxSzoeJwsnx4SSBP5"
    "T9v3b3JWRlshJarAOLiO9uKahQnwwx79xTdCz6CygtYE8nHnIYxaD4KavDNzHHaV2Hb9EQq1e+SljZuQtuvcLCtgNDiwyuaGLIVJ"
    "ZrLqEqkT3GtwY4hMtNq36WTDBcY56Te5iIP5zGd3mawwhiZFsUXX6Q1I7ipCiBZo+jQDdtj0lRa3YmxVUBOhS0RQTYlUbgaTBkKE"
    "PQ74Y73g2nkTJZHhRWS2ItNJdCBC8eeqmsPKqAazInKUmaYKtQ+8xNaj90RLbTCkYHgYlFMdMHoUtvOw0Bh0/MXFPqQPmP6gP53e"
    "qaU2QinrIk6iAaTEdnrP2yKU+lv1mQiCKfFSs4+vmveJFrjhBWuPtpNWXaySUq2S2t5PN+aucgIWwJwul7kRPJc0VpYmUP+AWTEm"
    "bWxPSjdFEk86cItlXPh3XJELAHTcfWbsbKyIkzniQQ6N+7D088fKZGx9WHJRCWzVdDjLJeKUarO9HUvadAIx4BzXHiqapvfi+XyU"
    "TprylSXtaGnD3D7OUtYMU0v2aSo0rntKZ+qandctoqU9epY0O6cafus0HxWKuzlDN1epPUl/BLwhjSmvSc76BH/VXXu+urM17HAR"
    "e22uSoFZboyOGSuxrC8WCZ3biJ0mqz5V7AxiJrbfxgHh69poabgpnvM0Uhd7C+aAJ3D8/jF2qaJjs/Vzp2gIz3XcBQk7azKjz3nT"
    "2kSeLfEMOFwgTKJx+SbuYnW2myAbntbbRtqa8TXZjK/JrvLm9CqfVjdvaZxRbJPFWIbR+CnoMHamJ3OSOedqPCdWQ8BcKXZ7bhmD"
    "SoQfwSpXQEliLTxBGIFi79zZjenE2EO/pphGzSsahTj++J9fbDZTdpozde7fpvdE41SM/Rbn3D79ogfdMBuqTctULAy2CAvA3NUA"
    "lkHu3k4iDPDN4NeafR7aUrOZdWuTWm8ftAHrlXHgQaC4SnnnS+qL2VdF3d7ZzOFqUBCoreB4kCOyq0kY7RI6JQhz5GFoDr/PyxCR"
    "d1D40N4YBCrQQ23xJI2bES4vlWhsmBtJ9rnX5OJa2J7plMRRa39nLctf2eX0u31cJe0Mx+zpkJrG2LNgNZJDhf3ssgOiaBZIZBbG"
    "wnxmeBGRVa4vQWtPd8VL3tPpjBd7ffVXxbaL/uOMmZt+/xYFGVKhhjEHtU9MEyFMZGcL/NnbZGI/ZHtYquyxfAoyb2HkP7vfwDWF"
    "TvfIY4EFNpu0hDQ1LY2mt+VweLbM4yxFyMnBooCy9hTYV3TChssns+HSc0ItO8cE744n5t35gbaopl/ulyG0bR+2q6fT7NbL8EGw"
    "zOLkJtoVCM9oGJcfG4Z0/bDbZzuSgyPq8PTgSLq8epIS40N/l0PPwK1E2Wzler+yvV+JaOU139nF8bVc3e2OIlDgGq4ePdp+vKWZ"
    "tPSRefrPWpodHKjlwQGjuKczYZ2fwHOsILIlnLml+sk0g5EwWIXCTQF1yaDNj42auUTfrsKw3CX56ukydmOkqmj9MIf2GobKetHr"
    "Il2pK/p/mZrIQ9yJVXol/Vj5UPUfXQDtaXpI2PiGGUlqJYrLI3VHi3+RLg+uaMy3kHacUgKdEOJM7iI2bR5SmxfcpEaHDRiv0oUM"
    "ZBUy9Su+tr17ml7EaxpgaUc3tHzgVsTnrCro+hcX6SXrYZTi7VsIYmpkRAMeYcAjuNsjmlCfjQ6uziXyHS96ezY6B8Wbjsw9fuH0"
    "YbKwAwm+LfDtikZbPE1Ps9O0SG5xnFxzPcX5fcBRd9Qud/kkvc2uCN9q8NjStRO/VVbpBW2V1VPM1cGB8/nwaKXE2Byc5pl+dAQF"
    "Evoh6JpZWov2bTGUiaVRZQbAsOmX4S3QLbzjPjncbFbQjaZBZyOMDqWO42REjUKGOArJaplaczNMgJxbZ1CB+HzuFYdXAUKfWnF6"
    "/4t4pPd5KbfBF5zHYUb53mf+gOM/3iv0xefxZBCEhiSWy+VOxN15FeXCdHSVPFahWgr1aWWDBFL9VeRCkbahMT9qvMnjU3P4djxB"
    "HRPxAVHSXNglTH48D6XcvRwBKjLbnSSadwTjEMCZLGVon7kRY+cgfvw9CkfEgQcjH0sCipY+fswE4XtXlsIESxrYSmUNnMXapogp"
    "9O57ERVl5OItbTY96fIwTIUzRxNjRXWHp7NVFCcItcYV0osChRfBW8awyKDEhnOLQ4vIjPpOXHs4A94oPEUhF7DeNRMuYhsPZJN7"
    "opR5AHarQHfdSpdpcom+ekEs+i0c+uhFBXKDoTOa8j31ZgMq394EyzU3aP/Gee9gqugZ4kiazSW0GSgknMtG7sFTz9RQe9tjAX/U"
    "DgKrF5w/1kJxBdIFHA5Wy5vI+ygcJjY5SytnhMZ7r9kV9YhdUWAvp+ydsMvJyZoLMzJC4GA09EV80dmBwf2qiH1BagUbz1o2BhaY"
    "26vwVqV1knMpOeZWPs+M2nAndOsNfBonMOydB5f2UCN9Q8Q8xFO8pzOmsNjFwpFg29yEmuh/9vhzgkzinVlAzUTcxAQlJfYK+hxy"
    "AeUcuZv1GO6ZJm9AuNlcEfYMxLSjcNJ2h+u8G4z5uikSZXNm1Bicn1s7EWs4hRtOe1dbh/iyAKOZszXXGxOoqFfE6zvdmW5zgUSo"
    "Z61Z36JAsXD3FZ3QNEUnNE3okL9K84xDSCSa6HYeaZ4tWAnPtJk0kBL8Rw2w626e10CETIW6dcQB7tIh7mq3KbG5zCgq4Xk0u1Ab"
    "crx0Oq5qoBWDhYFP1N1OUCpz5/1XF94XO7Kv9QUHEWYmjrAn8WeEZMxZRGiGMhu1gKND8W84Yvk5/RXpxFyzLu+gaaslTNFhuu1c"
    "vdOUVMqIzpKKvYUGoVMsa+aTOh9ASEAwCPViwwvshn+UyJDDlfNGrpivxiBv76NRAq7OnR8BwLDyNygVHX5MOFbn7u5zq041A/Bu"
    "zByrwneq/yLOSDf2jfdratEJGFDDMbfszSY3IVZZ5gn6BvGkfg1MTrIr9myzVSfhGv5gBGxe/Dviie33QSeYF4Of2ZKNsMi1y9hs"
    "xCUdanNF5A/kFlIo1Vuou9jXTJB1ojuxg7JwKuBx4KccwjvCdOl6mVwDkq41gdKIMF/yXC3aZEWvk+RGLSfJO7W8mMARW5mcalXB"
    "qeI7rZ47p4nwHXnGKedpEd1AQ3JtDChPtIvzTAVEd+DZcpl8KCLKeqfDIDvTPBJMpM052m5Dv4FW10M09sZA5cVlKeYl1pjNaHqY"
    "InlZVlA5q8qDW06VgGnlpJoyjeCfA09KVy1URewsBg42ZtQ9EbBQB7ETpXslwr6YXfXZsXLBFD4H8W3kqOnBZ5/ZHHr5Z6DNt8xD"
    "Y9oI1rSaXad2Q9dz33utx1OBS638nrVzINooAkGGdUENtyf31InrewrQbVqLpzpoFQ/zLtrs5ffvZSLCL46UeZIS2Z53lOs+O2bf"
    "EFxfSqwbfgkt4VhqeVvBRDr4pCf6eIucTUZQ0lwJnubsY6KjuHfUqVqKu4pz752Yuw79nsjnhw678tDllFgxYr+fHZ53hEkON2EW"
    "xXxn4u12JuKOGMR4LzUGhQi0UDrm6VzBm9KTSbxu2bO4MoFK6oBpRNV5x5U5sVv5k2oYN2n+qHr69IgqKc+ac6ony9Pm0VFSpc1w"
    "8gSp+TmbGIBYibgJSqJmaSywnOHw2Fy9rRqtcIlhfnDw9JBOKJSrEL8YZkX3Hc5cdmdqN/4O65PEPj60v5dpu/cyWZtcQkE5cPuV"
    "2+hR8V9cqWv2j26Os8B/lvs4vIXxKD5IHNrO7+801RQcG/fCo3nn8F0jvOwa6jNhiniaFi9ZorkujpFNTeoi95Gcp3qm61pPmd0K"
    "vR7eGkTBOKx7H8P67a2R/jbO3kKzbmCYSCnPSqtE/2YnwMTsEjTxab6T3N4i+WQ3ebJA8s1ucoNwGepdDquR56LMG/hliDQjqXe5"
    "dIcKaImpdBYGZIBXcy7DVAsVepefOYt0AlA5FcWHT54eBT58chOlLV5/nz8iklU/Ieh/njPypNZCtVnf3LO849p8VwH3e9pC2fOc"
    "GhUvO+id+p73FWp+njsvNYF3q6+79k2mcmrpVUcuzXY93pFBoNkVfPI2+KT7we+dnmeAqmsoLEIjm73NJKHd7Ou86wHLokS5OAG1"
    "wK76U74VFwjJ04h92msobuqM10r9gFQwuPDrOhshv+UnAgE6L+FN937wCfbzOB4/0l41gBf+kh3+tCX/sF+zdZG8osFS7R+o3lnS"
    "65XbRAcbgadQLgdMcEiEe3D64xIu7zBh2xmJzWFx8jqYHzh0tM7G8dwlPBSPqt9/A8TE3Dy9/MAvRqkteVt2tSFE48yFiAxM1kWV"
    "3VkT85tVqbOvVqFO3lkGIGycZ8KEFBQlVMulSRmOLh8+c/z5MOFZULwxWvhwiHcYiCHyQAxRq1CxCd7Wd+QX0gnvlVpG397S2m29"
    "38ToS+jtIFiQhCwkuhp+x+bFnxoWWBwYK9Do2aSIiJg9TuCHSLZYr5JtRsVc756CsOiDq550aAWE3LTbkX0qsjeE9OvAruLr/K+B"
    "x4RGMnrJDxGqWSOAoOKtZsmrV04vJDgEvszZfbntd276XYesCeGRM+phAbEOm1bTQZzYLnPA505gRVWDp55X1k8qb/DJ5Ptl28R8"
    "FKQv2LKHPeRDhQ2uxHE9igilLRtBXMq3rai4pc85GM21mLP93PJvT2KphY7NWtF2S9+x31xhyNil0FFyx8EUaDUTBFyNEa4C1lzZ"
    "5+z6KztOXOyOENVVguwCXNdFXT+3JgAjsTJx8rLwb2dFBb9LcbIbNeKVJ3sDV5nWoBtbNgTojquIYFNBfQJaaNl7+FOgBtuYvl79"
    "DVQhmtbS3pzxxZzxxdzhC4jRZjBmzjPjc8eoSDEiiZOzXPHTecI/4OwNbglUqkMUo7t6tOGIBAVQp/ihgwZsIr918YHNktcOZtCD"
    "4C3AEgHrHEwvXC1bk9s3WcX0eHb0RVJt8KeLTLom8Pcwy32lrQDNdHy1MpZkp8PdJQ1QbyhAdBjY03ABHg5iz/b7gK0wFm2An8Ow"
    "s66gi0OrAuoy6aoBwRACsqPcTr0R3QNpsvBVTdC1iQ5FvzAvti8Or076/Zpd1qzUxATDXdGmXfm98ScO2wdjwnSHbpO9jU5zZcUJ"
    "wU78kg9mQzZ5v3gSX+fEfkLg+jZ4C0LLdTayFSoHBMCFsRrNWC8sYVr1rQ3c4zisOGEMy7rcaMr21cbyDsmeP7sEm5475Rzd5R2P"
    "IK6B7DzTyauuEd2XeRhz5jB0VFQbObtVYJbjIggySXu3TI++GO6E2qLy40qkEXK50v/in95biDVOZ98GEp6nNCGIFHemjFg5K8g5"
    "9AFS1yWdbkOrDDca9ggAei8LcfcKG9P0VcleXz5DPCaq4VVprD0lqBAVSuGdi36OVTBLm5Sd3ARxu67YZNl1n7vmzBtbr9nVeqPH"
    "Vo3Mya/QTaMbZ8Owg36CnD3CnBGYnf0JlEdnf/p4GET5htZHQAgEfOZ74WX+lvfZwCXMsGOFUsfGRNBofsetUwyvrWJ4cEqemUdl"
    "Ms8Dd9jaO5eJ/UF5Zh7pC/499x/kOz64YeINiUpBnCN0v6FnLGdwELu0iGO+i0/LzHvDxW1/UiSFhffSPvQMjcBfFNbvO1SMxzYV"
    "TTonAoHD2ve5E8aKYfFlyQn/o84o7Vx4xW9z8Wb6Yx76TIUM0e7DHwMvK6x1Gjgqt1ZJaVRm5eAj6ByOgBBOeA3p5I/5o0fKeuTh"
    "87awKnBlNxgK68MJPefoUCsgFxQjIjt+Nu4UxWlkdWFKs3AdCge/a74wNKJLzhQfclKRONEPX37wud7JnP1OvNhixB9xaZu7jFgV"
    "UymK37OxRHfuRIIRWjVwRtd1o2vZButI13bCO7v7F3xHEiUbegdJfggSzcDE5WJQgfOM0Xad2xWd4AB8jrXiGK91bJT41WmNZTaz"
    "ifzq/eaZlw4f4U7q2j0SUVRntZV70NuhshIlw4uEIiV4NXaqc/LiriXkNYj3ioSLieFg5OdiIb/mB7q3DD7mxyWbh2lu+mBWqb20"
    "D6Y+bX4b6aw7ySuc+0RrJtVWVRzaKwUQMExXlILFSF8Xxm8+ay5CK3Aisn04zVMV78+Xxm76j5wvYl7mCNinvsvVL/nQXJrDUJzQ"
    "bxQqVpt+ROKSTpzycCQcWB2bSPHQ3qbytXcxWIde5jm8ZQKPEDhft8Pv8rSNxmKO/uLN6btnb06ej06fv3v3/O3pCMb96F2qY+qZ"
    "L3h6+nanzEOUkaiquXdnl77M7dR9l4sHYq8Fqayuqtd4pBlgFxTqV5mX9UtiyV7mu0WM8qp3otIlMHZ1NT+XAK3gFoN4rJWRPRlB"
    "PFGRvzjm7L5Hu629YSOsyM0N/xDnKTm7kWETf1USIWU1WfOs5RZsiPsgxiO1AyqiCoK9ViF1I+h3qMMISnvdcplQRqx8xbgsEsJ0"
    "VcgweKeCPuKbBELvLigwC0aDfZwG4FJx4D0GT44drOEU+4qAjgjRQ3XmImgRyFXpHTFKqJyDCOPEQeRVqhsBtUWZwIQUoZ3AcVVE"
    "if3XnJYYPLFzX83JJS05ZocYdbbaFUPl1ltVytRtt4hm3ZoYNMbh5aF1KsXOAojIr99KjBTrajga/3b72UnvgP49HUPnXTshd5ob"
    "LxEVKytalzG1LEsQdbeyruzYc7+Li02NvSjnRamlySxsHqemjdaSuABEHqOmtBdaiBJ4sEFjdRX6zSs8WEhtm01auMd6aDYcr9eQ"
    "1xkzyAGw3OzxIrVs0IwdUVRWjE0rXEmAv1DiiGBxQZg4trYBaQ6ME4brYoBxruz5BAkhUlxy5TBVkZCKJp6iBEGUCIgmdlTLCMEc"
    "3FBtWW/D8CJN1WUkpFxmn7hBqLu6xmlq/yXeiLgk7jk5WIiNYCheU+zONN5cOHVS2GQOq8fOuNnDeuiNnN3DGHddk2ILf62yI32X"
    "J5XzNmq+MsEgpkVD3Obdm3yBG0T22ZPID1XI0UVHePE1zcPBi9v2sRMvwfZMwnp8a+F9ImThwzyMxORACsDxIY8OTEDVOs3ryxVc"
    "hTTOp51xmEOrfpwJ3PY4+sLv7Dz4rVVcwUGUvBVU5xLpOaqffpaVJnLw0jooFP5RnHC5JqEbaJih33Mr3IIrU/XWGgs5GKZOHxl3"
    "0rP/l71vbWzaWBr+fn6F05fDYzeK8TVOnBofCKGl5XYIlLYhRbIsJyqK5EoySZr4v78zs3ddbCcECj08fU6w9jo7uzs7OzuXaGC3"
    "6916p2tb00i4HjmJBvyCdwqncHT6nT0Dnpr9rqfxDB9jX0IB8jB6EtVom0SDk4jT1ucRQHhetd+jAd8FS0MTWgqwOeeBXi8IgONo"
    "MIUNMbg7FZWxIKnBYCDSI4DvOE2n/Tt3Tk9P66ftehQf3Wk1Go07+C5uvS3Mb25vb91BnWz68+SxDXRNjGgcuYQxHNNQfDBSfY4I"
    "uH37vYCEe36p2ql3AguNTI9HsMm5pxld0Z8lMeUunED2XkPG6+SMRh3nwnQDpWw7XGKGRUj0Q3vEdFWje7dgRCyVHiCykD7drx5F"
    "KE1MNcWAolJvqVSYy8KLr5/gi0Y/nyUlv+w26GFQM5vkMnH9BLhlfxrIMFo+Umdkkv3RDM5aW+TbliqLgaV1PzwYPUh0igmIITz1"
    "TO88eimeRkpF3GWP0D5CsfvYI4/4aIWW8eOjSunG21BOc+/DQtvKb8PZDwsUqxKsP2defL5PKEFBF8FopHEYuSCT0UDPRFJqsSjJ"
    "eb9BRZ4D2SXLe+9Hs0SAldbh4s5MhnaYHWMVlaQxarMOLVOD2MmsWp/J1QjreP6jrhnzUwmNmPV3uFbieaSZxx9HzJUfrUz7O/jn"
    "7q0Lb/4dbtS7NhEnuSTt7/AXz6efdt8TMUSgVZeNe4fr61KbzEOgdGwiPIjXJ34sxsyUzfSUGkUcgROeby8tD3iu7NbLYsSSYcMP"
    "omGkowBQrVqylswFnPTWGRAqJbC1rf0IdXX8E4d97kbqOfw9vSefAqGhE43JlJhEgP92k6TP1Ia4fzpLyKXWGnNrPIup1f4BL/6U"
    "3iMtxv4eWqS6/DCOTnbp/YQXotR7dJXOp7+MjDREqZNvgiUXtMEyMo2QvmGuDUotaILSzRbm1suIvd+cxICumrUXDdC1f9XgDAb2"
    "Sw3twonuSySANQyFesHv6fiIC2f729h6h1wC+tu3HkTECeDVEIgFd6mnBRHwqjwEDF5O2e+59SxiIbh5cRE2XPmrRxZH/O7r9ynq"
    "uEDmx0OC4z+nEeoqKz/lpPMBy4EiqxiO/NjiCQf2e5utnVgtDD+7BpyBfesinG9Q8gaGELTzCyIyCjFlD9tcH65RJI3s3FIJMJZL"
    "bp3MBlFmkYwHbnaFTHjjlMyBzC2XqVFIAGmsnhOjCACJ72HHg3sRujs+Ghzfvn2Mmk9v2a/moXURhfeVPUD/vRWF7Ne5+LWLoWSC"
    "gILJRiFTnj0Tv1TmviVaukeD7XveAFvjX7uDc/mhKsH1ZoSGsZr7JHZ0vfWMrgex9ZR40+G479bE71k/Ik+DYVV50uHVpeUA3uCp"
    "+IRXO+H/TmEboC9SVJrERa0LUuAyNdxFDDCnih5dIMPazgNAIzC0VgSs5/OIaYI+RQdZ3jDow331CftNMD5DlF9ePorInO0ITeFr"
    "6ikdEk3M4+6A5t9bpEP3JGIem+hfNKI3ccsLe55WOuD/zqg0m8NTJkgQc3BKZx+fOXFM66hq8Ms/Dox5/antPOHIy83JsPqE4/F+"
    "REKjKv1r8VSFIc8w5KiK2XjCZwMQdcYQhfKSt8TNI3mqnsHoUIwwz61EHH/okXG0fquHOiPCyDy/1FSVRqZK6sk65pJm9ykcEpTa"
    "Z4XmuqJRJDTT+MuSUB7A5yURZ5MfsX+gcQ/hr2bRb9qgtUNxL8c0wYPCAsMLtFIL0m92E89493rCJUNpHQ4FP63eeZOs3zFi8NJl"
    "kR49HvtJSnG8kPxXvYNdfIln/w54uLxajRdQPTy9ag/c8iKtSVES9sAfypiTTHxECuuJ/5cnAeAmKVrHz/mwgdVM0nuCnXgYA+ln"
    "66o4y8N9hrevh5H+tvEoyoZbpQU9fjQerK8/jCwuUESWUmRguB5mZRCuGROM/Lh/4kWzlILLK4+NkZWydG72z57e3fngMUMi+VyW"
    "/pljacIdrdvQo20xO1a+aRge997DqkG8esCLVtEW1nKQZk0GKV3O2IM/CxSwvj67i/btaOu0owHJLKO+4zlWst7E7QwTnW9c08cw"
    "ZI78fgxd7fJwn8xuHzYHBUyqYshicmLIl4ltVWxyflyFA+ksmj9AywsbRYUyhZ/YNsoJX0Ts4SJh2fuqgqtSVIUAK5DTlxkTlI8B"
    "cxPUKQVMnAE/S2qyM/gJORHkCHVDdn3cj4YBL7GPJWDkA1eWqI65zbNzhvHUsI/x3Qa0GQzPov5+xC7Uk8FsOGO9icb7oo0+d1gw"
    "HbASt2/feTOqDvvEJGOoxkuMvAcJ1uWt2h24pyVpVaBFRDAGTKYRf3OVD8fCMahYZmNtmU1QAPVS9NCfahTkBZ9LfodgQCovTjWP"
    "dGZZgE55E5Y4QN6PnC3zI/IvoJm1dfhLbJrxkh+ZygNwDZgBDzJs9BmbXhX6AQ1ro1mT4aNsC/6r27Xat02vrb3pa61VUR0yOoVl"
    "+kCINYR8o1YfReNzlP7Dkv/B84+O9dfQKBtcBGkRRk3Dp5MhkFqM7XbYP6B/avU/Ij+s2rB0SZ5Jeo1iJ2o3fv7m3A+HmWuu8EOW"
    "Ih9Mv4lNT5noTb8HRWjF9UpPSY4h5bW4GdnJcXRq61FzkZ8nN1FoqHChKxLO4Rw/+IHiFdBbtbgi4ASEcO2FO6ndz+Qh35TC1W5k"
    "sCD977lIW8TnXdhpSIq4IbcXpXiEzDmKVsuKgjFJKjDsit5ADA2spWsDtBGoxsN0WI0zwFgEDL3gyi5q/ZgdnZBDZI2VaQLRF7CT"
    "2ZVmGKgPoXYhBqjJp3nSRRZ76ZCw2mc4tLyDV4DiNTaXP6mZg1n7Mxrcgd38++VO7U3yLa8Pv/p3VC8/Zlci1y/wSUmSdBV5yCI0"
    "xSO99QsK+J1qlh0V1EsRFHbHrmUtGxoUw5NpI9p9yOchA3fQVdlw+EtErpBQFCON06VKBcal9UQhj0XH0INMo0wcVxQfnk32GWvS"
    "NQuFlo74nqE2fGyjjzFAUdP5iPmwH6KJuogqGwHfx4tGms4KHz86xROikPjgJ9i3FAxnfQAjR8XjGC+HL8mzCKDvz4jR0VA0lDKv"
    "wJmtyxU9dn6I6OaJAiDmKCwkVgR3kTOMxRro4+zSxJPqp1gZbEXUGJ/xK0w+zPWafzKN4tQJ01varP8iZ51UjYC3DSXrFA7uymyl"
    "XRIOh6S/ZcSN3NiA3n6VI2RkR491L2nprxE9xtgSGpyCbGkjtvstzpuUNu+Q2eGSLsgihcndf4sGB/Zrb/TOx5ehJ9Ff8PcksQ+t"
    "/0Z09ZeRAQwO478RD5klffaH/OnhVAStQv2XiR+kpH/O45PxslR7EO/EgwihzegU/RbllIr8wW8RHF/rMQkTC9ryC3RrvEQxkUrt"
    "3jl6yiMqvNz75eW9F3v3SEkHE079cXosopYe09mE3iCPyGgLLdxY9I80KZH0b985C/zwna2QFia6wHQwIkb7IkZZu75gqBoQgGFY"
    "doo93a+miSXCMm5aghuo8fWSLYjOA0KhD4hWV2ceWyrZLZZmG0BrLzyB3mJ5ztFgY/pbZqLbSnDDY1vKXwUGNYG2DcePtIwnHYdM"
    "leFxxHrRDZEx/CefL+EfVzptRHNw+/mLZ9+/2Nvft8msTFkRbthSW9yhGJjPXz569hSDzx4Z5z93+ImcMGCBeXX0B2oShDdr99hz"
    "342iMziagaEFMtOXiNlBUbCPr3fSbSRdk1hrAx+24rAQ7XhFZ2VC0/ianyw8Fg0HRgxHqHZS4J+BruAZDmiK+1IrjYmrWXAR1P8D"
    "MoVxGdjjnGYZEpKNG+qH4+MZTU4o3sWiIqrso2KEWg2+ts0K7incH7ks7hjFi65NvAZutSjRWC7P1y2ykiTrdYTHZPAOooRdleFf"
    "DM6EEXc4tYKdF9UiPjexpKsHoQVFZxRvLx7SgOCQQkycJMzFXMKstB2WhZ6LWT6/CDNS6ibAWKCJ0+Vz4CX9997lrjOFmfVqt+5Y"
    "AWT+DpzUEFiPkjLa024i5a8Wt1yvopbHCelJuAlGBFkLEnYEwCWgxsJGWp7BW3CbrfCgeSjIhQVjxU8j3Cu61RbSDO+ghU5hYJEP"
    "RVPtWp/ceYrIsjUUeOB4xwne45IBnD0nfoKTSQpg1Zo1ZS4VxwmAVZ0kytchVqlZD4DtrIfRKV6VlCVtYqjNMNvyNdwlaVJj/wxU"
    "RS12MeZ8NwhRNQGVa4xIz/GAe20V1rdKLQft8h+dnHhjH9+J4fh0jujCulOexS77IXvwJgWot1h0ys3t2UkVS7tVZ4CKpubh5su4"
    "S2uqtjrogGJQwCsK7Yzru0tuZmmwRyHxg10m25LGL3w1e5bCwGCaoNkse9ZOmM2je+zEu9EY9nG1gUEFm03u01gmN1lyI5Pcqt3d"
    "3sylfddsta2jRPf0Jr15uwNfPJXRFZ/fs4Y/M6Ghy1+FGXM3/FEEMOiTKgJeVy8vtd0NW6+KIYqxSh0omQpy3KxZTWiL5/2ezQNS"
    "91ZErHBrNbiy8C+cOH6umIcGEDbdMTB9EO33xuKTPTbDN5Bm2Tg6lFQV6UwWoQuAaLxnCxsVQ9DAVDhkfBw5Y4oIfufg3sZvh1yw"
    "gOXWkOMAgAneU9Lhxh4QD3SuxjNPhVN/i5/sdTlmeJ04sFo2xCBwg1AKLwPrQkOKxuC91QgzKZjx4J9rKxzvXG0Glu1xQjcH1Fys"
    "yUM7mXpBQIgUlcexc3REUaJEa3jXJM0GnoCyCDeKY+ZfgDXjhGM8hcncRfFxjx6+uPdkTxRCcYr4HcCRkiv99Pmrl7JXOE6zBSRb"
    "KBDQlOMoZBDlpS7Lqjx68r0o+/OjB3vPxMfuvac/39sXX/vPXr3Y3VOdCUaWI5Js8taafYZfzdDapJZsZTFXjkg2QwW8xpYLs1bS"
    "4vET5nMN2g/l2+ApizgKm1GPNBvW8gWYQXUClwc3jQO4NCTH/gSvEE6Af0+81IFLxCgZXCCRY3oK+Esjp3hQxN57rkvh1fkHV3mu"
    "oppCMGFZTHDKIrjMYtSEeMlsrbBzLLKGypJx8JN3bhEgPI1+YyJAxZPgFyYggDwFf2JS4LF6NrA5KTB6bEV7dfaJrgSsE388DryF"
    "hZpWjAtjYZmW5Z05rtT+OE8YfuGO6R3QkyCAYx+Stb4kUPjSYp0l8t2MTkdpWS8VQd+iLvyTiI5e4AjQYoWJyeq2MpiE+58IC12t"
    "hiRV0x3AMJ8Uac4nRTwYJQdozyCYqRi92IlnE7FyPdHiHCHehxXgJW7fhj8O7DYrmcK1tI8GUrNp33biODrdmE1thn3+jb9tjkee"
    "RB+2NY5OQ5GEv22LPVL0bTQBo7btubWbZIKwcbwAWlfGS8hxXLVhD9gkUjE5CwwRyXwHUkQc+byO2+Pycp9FG4OdUlN4YSg5TVBZ"
    "QMUEO0rm1iiqWS8TRY33EmXd8RJhDpzqacJ23QMYnQiMx6kPFq9LBy8s07ogiRozR5WuIChNKnXHg3cJd1u9FuvDQ88lb5VnhmN6"
    "HlUqqn5daKKhk2r5AcyPPCdQ5IOaTy/ZJapJMhldycnmgWCcQUgBOaxnCZ57UlcRKB5ckoFVhgsPV5miNnJSovcbbhA57zAcR0bA"
    "iwYRG+83nOmUtF6BJZtbaEYl0fwsEa+Cem/7P3/PO+QoYbyMsjZjyny8DB46vD08S/SGjHKiLa43pGg5TYGYbLL0FdLynOZWn+mF"
    "3pORnYHs+6EnpD/WHzIDiOOz01BksFtUYj2R+UqJE/0yqJLW04IiU575KNmDi6MXU1y+54lytcSOp+E9xkNceLIUmuy6UTjxj2by"
    "+zT2U/H7PZc21/rs5mk9VFsXyRGOlmn2ski7TxLGfacUpf05u4+lQgPlDxZomFUC/P+Bh2jtaXkdsTU1PuhRUmRT6fH7uHl2euQ2"
    "WsY/aADvZq6kB8xNumaRyY0Ub98uDOWOjWivepwlk9Fm8dE3G26PhShF10VrqbL9XJM9ybRUT6ModuT3gf2SVBw4hpCelT3xuiyC"
    "cWZGDtduMwn4VPLPw88GJhqKlJ/iaE06/VV9MTc4Ebq9wQN2By0F13DcB84hzBH8CTXIZGB6JmD0TS7HHeRwj9bl2TTuGCgw+DsX"
    "vXJKKeERe46F694gVR/C8bLe4AvvaO9siv6M86nY7mxtMDY6mt2+PVYdqUdDcgUiv7gPfXONkAu9wUTDp1Egra2G3SUEQOyVCQbw"
    "XtxUMsBCFpuvBOcrKZkv9bhpat2zFa4/Suq7T9s2GoW1EUDOU9lA2oNz2+SNX6km1mg3a6+UvHu5Yww1EBSAqVBBiO5XVTmcipSK"
    "QXrh5qVm/9L2UkVEeU7VOw+wG2SgL9cA9iQNlfljUd2ml3rdHS06zpAM2XcpizvMtFJz6izxID7A56FDFbZ6ruVrD66JePCQjvQI"
    "QyHCeD8hitl/kZ2jHxQSpZo16Y8LNCh9QSQ7uFJ+Zq1KkjWX1x01a0nWuMLYaAzjzK0epMYzPBEHYgegCP/ysnBWyAWY6uY1ZCED"
    "iIqN4vr0kPu+EMdBZleJJ6BYKpzFOwAtvo1hiGZ+80X4MWWIb2uD1+yLfDzX+pSEP+collFvmQm3rpb0IPbGM9erynM1JAfNaf81"
    "Q7l1oas0/WTcATeabMF6NbKCQJ4XWIPxYydJyYMB6gmxBYxZgUiGNYnP6d5hHW9fMcoDqR6u4nne79if2CfplwqgaccOudJpX9uG"
    "P+YmVNvPiYx6jRFCyVZaG9mvOhX4kXUgX7TuVDcu39buHCFHZwoy9d5/Yb3bNhyfYqbjwa80odouI3kdXhKlD9SKP3xFPUILONqD"
    "zKoi5AD/TDCi8J/eDw7Ju6y6UuDG4V4M/0wytmC/5RCT5yoILcUr+L86cl5R6TU/eeo8NSjdrYRcS2QKaswKuhFcEyLlO2/2Lyt3"
    "tOqeK/d4qvwoCHmzvE3IZQQEKizY1KlrrnCx4jUrPFdnt9h7A5/nN3fefFsd9qvDtTffvrlTO3iTvNk/rH2LH5cHb+I34Zv0cJ2v"
    "A1mpctGy5phYMVKrBxf9+WGtgjm3mnpW9WDHKsyorGHamp7Up2J9W7zUa29irrhI3L595+DN2W5j483Zw4dvZo1mA37CP709IePz"
    "pCbAxb2+LLzbZYXpb4v+dg6hu3t7rMwmfuyy3z3K3qS/W/T3Hv3dxTIPqMwD1tAe/m02MJ23s4V93adk6qXZob/UWJMaa97D4t9j"
    "cfzapb/UUIsabbUw/wee36L6LQLvEetiF7ugsbeowRZB16KGWtRQmyB69CNvo00tyi8a90/ii1p+LL626S/B335Af6mjThNLPWVD"
    "b1JKm/4SVjuEsA6N6xkr0wIYH2zC/wjCDsHWIdi6BNuzPd5jl2B7Ib5otF3CVncLc/ZFDg2ySw11qaFNauglz98kbG9S/U0a0ysG"
    "yTZCQtU2CZZNamiTpVBDPUJ7jwB5zZvrEZJ+ZU0QInoEVI+A+k2UInT1CF29B5jjUI09XHF7bMURthqErUaXinisDAHpst9sxbG/"
    "1GaD2mxQm2PeW4OmoklTwdvA1bbHVhv10KQ+m9RQkxpq3sfiR2K10VCabPEQZK025vusOVxZeyyTKreo6RZValF6m3r3/xDrhWrL"
    "LxrfO/HVs+gfwlggEgn7bcJ+m7DfIex3CPshgfGQLTCayg5hvcNWEQ1lysrs4e+I/cbF9hAW20NWjMDtELhdAjfyxCIicGPxRcjq"
    "ErK625iTiBwad5ca6lJDm9RQKhYbIXuT6m/2MGfGIMHF9pAtLULgJjW0SQ1tUkM9GlyPADkVy4jwds6aeCAIW48a/kuUIcT1dgWt"
    "O8rYjaSkuChIKV6/lVGTzr37bubsR4WxoXfQwFfLV9OpOOzXPfnUo5/7jruQdWCMw4Z5ADgbfx3WqvQMU2PnwMat1iLmInKrMgop"
    "j5XCVT7R/ltXGyMLZSXTGkq/Dv0YjWItUr6o0qNUeuwncwv9IixqAW0ckX8ByGN5qwhrd+/ebVhN0QiaYRe3gtU1u6ELJpScW26A"
    "lgr4JM9/Gaba4hQnr7D87Do4XNUXEBMuGlE5faHJwDR6NFWFy0tf00+opdIxr9Q3G+iuntgkmPxTXBseMJDj2qF4yPBCaN9DCSPT"
    "jj0A9gaNqdKhCluWSmHFMJUqtnWmxITYAn4JQ+XJy1SqNFAFQ6AZi7umx8+hpnav/yYTQwduOqiLwwQHVbv6+2WlZq+n63a1cnmr"
    "Zlv2kY+dEPugdFVrho/RQPFs6JJcsm0wzRwY0kwphoLJenRF2HX0YrYOt4Yd7us3pasBIYNb+9UMGzTBVyM6pNpcTcfJzFVSba6k"
    "TvLi1/iwtiGlnuIHF5xybWEqpDksp42ev1IMAQ2yJVQ2tuCib083IrjdTILodOPYH4+90EYP4WvSddl7J/ZRJokDv33bqM8VTXUl"
    "O7O8hcNat6dnqOue63yoMFoMh8ZFTspnsGzepAGHocOs/ZaETltbb96McHXpE8ZW8qUNA6lCtlp0xEnf4BqYls3b5OPMG0NQydTV"
    "rMkHTdgJDUZFItbM+rkWGb8Eyj4IqP1jz0sTuqebspIhasm+mAVeUjMaDYesIjlSE5oCXJrCVNBTIUrnwz5Sy5Ve/vHeK2gUl2MV"
    "ioSOXc30kx68+w2LvXX3G2Rfw7LJP9ngQKhhv/cTf+TD1J9bGc1s9LhG4NyPZuQ/ajfwAREvgChXKUZipv7A5njONjSwR0HkvkNt"
    "W4Jr4LN/8aKsUQjIZuBCPvuhCjCDg1zDsVUARligUnqkzn1GvuAaL2bWIkeDJuWiZ8YjafGf3D9/yZQEqjauNbsGXI3gHBiuPY0g"
    "omzeJWTxz1j/FJPCa/zAhyqqiO/Y+Nb24Vvj4j0kAxJnlKCilxtHQfDYmwBR0US379Xgyyi1cGnFafvUOfJ+eUaYv7yk/mobdAAh"
    "QNj+5aUu2Di/Vge/ig4E4C+jqdYNfJm9jMxxFxhJ1bkrt4iUMOM0sI1j9swVvm8bOkeEXBZbZc9ZaFQ5o/rilJNmWMD0adeRMIoV"
    "QMsrtroxBIC5epOBcSJaLltjRdvLCgaIVGs2wMmzxgNcwNbEmlonAzuNpvaOC0zudD1a9++OedfDKppXYWqw4WO5UZSmaOE8QX/u"
    "kIlRwieDaJ0XsqZkjTVJ1x1og2AeSmukhsXzZuvJhlPriy+LZmEoth06O0iZ06W9cDyY0mHaL8glN7o8X25aAGMwySQJy6pnsX/k"
    "h4MTtKCpitwTJ4ZEWBmDE6ZDSwMc4sOCW711AUT9zgZzELtxNEvhrLt1pzZkenbDod2CjuaVbysbzZrdX1LW1k++fX66ox2D5rZU"
    "nH8COmEnkWZZV3KhpI7V6kGKBrdMsQYq0vupfjjtatyELkrH13nxJi31I7QVtaOEfumgYH8Agz+YOnHiPQwiYAhSjk8iGOsFGS9w"
    "WWnCZP5DIy2naksByeTsuLa3/A/fW052G0ULtk3CNgqGM50NYphH2it0j8EQVrjunXVxvNxN5M5xBxvNb0U6VJV7h9VxaQdRIUqA"
    "jeQOHNik/CSDltj+iWibfLvR7LNf69kCVTN9g6fXsErD2BiuuTFyeylYvHFm4hKZDhYt9Z381poVba00u38wwdbvmi+lILVW5KdI"
    "Od4zHlxV2Gp8hzqOEnoRGrCfcCsu5nX2tKNgbU1nK1FxhbGUBI8eH8PNP1DyzUSOnLwCtZV+0fs/XCZFT0pFRhSUACj6oEB4huck"
    "YEiZ+TINEcgzuRMjq1pD8rGDPtqm6fmQ/4tyDaFREwQvnPDIS0gIj7/IVPUuKQRDS5RJ6sNkWSz3C6oecS8iDc1eQLRmXIrf0Uan"
    "BxkYAOFSkCASgsBFh5zZccWgKvp2qN8ip3M16dEJreMOZPqwDt+H/QPBSB3E8qKiXtNirjEXr2m2AisLIbwVhBB+XggR0pAWCCCI"
    "emu60GiNwWJpNWpD+9aFd2Uh1byP2oM22rpKqQa6JuJSDWk47OekGt5cyeJQ53wne/iYB098WIJR8aD0O6y4+nrtTm3HHxaYhfg5"
    "KwREFeFiuoEeV4V+7PQ+fgxp4cToiG6gq5Tj0yX3hlANpUFvXKsd5kQzhtJ5KGwLoSwvuaNKxhawCmx1DcQPOnuJh2DfZMFWs3LG"
    "U3GN/E5ojifEksdn09DkGCWbW+bgDIYd47tvzJ1HVakNK9YdTphyJtpTQ7YW0TMNAGwokd1D5Q6Mf3Co+aUoaoI/DdLUo5/IjC5a"
    "WsuEhHiquBs5LOb1hg9rbcACv08gNzG8VjxXjIpBEjL2WkoKyp47QzKYYwrxIgYdqbrbWno/7K+HGroeuvxdWHRC+OOauv0wSmF1"
    "OyMSrFYGlW82mt/g+z0mw20RxQZj8U0L6NvBN8L6FM1MZWF2hz2swZE3t/5V0f7v4Dj2JocLe7pmy34IbNqnGAIzgvgUPaG+KBz+"
    "zieZGGie3rLV5Dz6iL1xz3LemClDfqROSZHoQPfHj9KkWvGtl9pa4wbTt28XFVICkjUpqME3BR6GSz5TaMFmXF1LhW0/pXEtOYdh"
    "eNA4zEaZKeAFDR4+LLyeCOZsQ7+lhMBFjpHRR/HAelHGfeJVM3mjKB6jV7EpXTEKM1k9lq84TV3nbWUMaBEKM6j4qwAVZTI14X0k"
    "mvZTuncUiktKpe1SiqKVYfJUlYGRvVFfP2XXkDKBT1kfNTMXW6+RlGauwc7ckQi7APytkfH72t02e4lli+Oat9js8hDpfHUsusX+"
    "7AoffRwgujvsaCFUWRTaPhQMLfnCRH5ZNO0613hj0wf4s8tc+NypIjou2XzU7qCAFd0Lce3FtNz/D/nzVZuUC5LzsmJbyLztWg1F"
    "iEvL/bJqwV9RfM7kz1JbaJ6lTnI+zcuRV0d9fphgvhITzoskzBHBhTD4FD6NbM2zADYciyLE74T0GuqTcb98ZZzPVafAr2xjAU8V"
    "8GrzAqnwqwX3MfOxy7yP6fq+aJ4qtkNRA4WZRhOaimMp2WRykutQzZxwR+Yw6U4RYcQ65WST6i2gmt+rt0JY7+E4hutM7Y7P3V44"
    "7/0jB+a+Pku8+N4R0hRNMVJVRfPFUgfSAqm5BJMf11r+U3GPJczyJ+ckD3T5vvgivB5+CiC+Mp1fmc4802k8mPyYEbMhJdeluVyC"
    "oKn/qv1rA8DRzD0mdymo5892Ktz2JAU4cc5eYpHncI1PE4xPqeUlTzK5moawKzWEaxe0jSkklBABZu71IbO9+801vOL810Ut2+nM"
    "f+uP3yqiwGUnzLCi+ptroaEN/IsmgcA60Y/1dQtFPPNbF/Q51wR8t9RD2MEhDxsDx/729raw+HMGPveTgd4tmAx2veqIILLDRj+u"
    "rTd3VNxlPL0uWLRY9k4coWMMjBlGygUDXc2FOy9ZQxsjtJTk9lg+/SvdpHCgGpBTrEAOLYXDtUZfhrZFAaQOQjy3WEDm27fpfHiE"
    "og8uR/6LFqTVbCBfKDhajLLooPPyPncZgN4YyFOlXknGPmP+Q9GUnus3kfN7ckvFwoJZZm+kg27h2chMjLF4zJyaMQcfXjDAqbHS"
    "oMT8LizO8L3EioNiy7wHHjAz/hTZGMsPFlvvOcFS670oWNF6Lwly1ntp8MHWe26w0HrPCXRLvCQwrff8wLTe80lSFZXXUQLLQPYb"
    "YoGYalozBQ01KnxZ4wf3SCUgQuEisnlCoy6u0VsNmQKjuyzm4FqKoBWkMYcUzS4ytSOjbb0teYlQlGQclGjKU3CMYIAqh9Y0GNy5"
    "qB78Pj/8toZK7ifwXX0zXn+TrB+8WX+zgarxh/ABSSgjPoZsqP4GatQO199AkurvKFikJ8lcUhxZItwOmaF4fbtur3um2HaBluRb"
    "vQuyqUC6ai7Yqn2Le80ozCMHDQgZK6W3/j6ompYzBDqKN+9UskYBB7+/OT3kip+avkEgom9q/Bw0C2RZ6J3evv0jWkGhBioR6w27"
    "jxQbjzhNo6CgHXtj49bFecAspzTSfhYYZhnVqrTAuLhzBLQOLo9cBrCusuaZrNq/W2u6neh+oGxd4A8KfLhnLppYzUUF8y8IGWeB"
    "UiCipe3CMKdBTZw7qY7QaYBRwWxYStVbFzDa0EItW4Xei8s5x7iyrNEfGGJmHA8nDTcrqQmhO3rqqgFCX1V9wLBVuXXhz9HB1rym"
    "rPI9va/jwLIbdg1Wfk0+KnpQGqZFXsxgOGQjU8srF+8GwuBNzCvFLcXT0cZppeeTHX1yT4OMGietgwsszCBVL5eBEkkoe78xoCNj"
    "8af5h9MFQzhpgwYcieSpi4WsQ6fI6P3J/06qpu6IgOpoX4ZTV3VR2P2NfXlJP/6P//jG/gYHd+BvNA/RvurNG3xfigYYH9hl8d/d"
    "moUhvlkDVchOgCmhjxp+bGxYLMviD2ICBKTD9EglVosjVpZn+LWjsWNECsQvRw+wi/yyTScwjdZfX2cujlwAlD1bobOt9QEAiHl5"
    "M7RYu9uiDhWiIRVoSAUaUg0NnhKtacbTFalEbonoSeFAuL/NPzfgWcfeuWCyHF2umqI7Y6UCna6vk6oenoro7oaczLCeUitdb9co"
    "FdHD44/jI/X6oKXcWvGaOBGOFBEqfE+jKaDb0czGMdQNNcU0m3EXrPmmRXBFWZTG8lFwA9jEuwB9vLHBFPscKzoc+HBOoaYRPThJ"
    "51/OehuDIKK3cN3VmFNbT6Q6frTe1NT68fTaC7Qggk8CMqg+9igkYjh4FpC/fu5j1BbKmXL78+gRQ0ELNzYO3pxuoN1XbVjH6Aii"
    "Rj/k7EiuRTpe5nPrAbAD3G0GlDEBYR4zniHDQNahgr2UQsQL2Y9vRTyApzPH4fCIJ/RCaF1M4U7un6FzcencOZnjKzavdHnpUEHY"
    "v5zkDtO+zemJHqeLA355+SghGVUi3qfd1B5y4KN3Xii0O/twCrhi1JF14Ne9M3IdM/7JO3/hHcEVUxlcAN3Son0EWZtOQ4mB3hKH"
    "uH21B3WGHm89XEcjyRRXy8U47T8I5jVSeyKnow+CGrN+FFnaq2ggFQHYptMQKTV0JTZRqsd+WkLo1/dR0sc/rOxQ+w7kZhMxdkWE"
    "OzfBP+7g4ILHuJ066THcRthu3nENQmuUSecDl2+9TEwUoaaENh3BADgfH7XuPBT0OrXhOZ62ffyLJyd3jQUcEZy3Lr+bUTcB62Y2"
    "5z5f4bhKLDhwZzULZjewZlZskVn+DqMDMxRhGjQ3XsczFd+p5f4U0SBhX8KVjwsy1eG9gUc3+vOez+fMwX3CD2e1B9nGSqwUF1yC"
    "MeU9N3CYg/cEoMYwQHBQ+lbAb0p/BANYSzgRFzFqM/cv6Gm+j15vgCsI+3d+f1MnnQZkNGlHf4teEoULQRWCkHyoi4d9OfmexeRt"
    "4z4avNR5q8I+gh1GOCCKgWv0elCtf1t7c7igL6yidWX3MSIsHvpWH7WJ8Je9avfkQ1Dv/z+UUkEgFoBAha4z3OQ8Sb0TvUOWsqAv"
    "VkAfsIARdxxc6DfcKIjijcRFUtmvjJ34XW1lBLizJI0AoNKJpfzCoa41MF6kDjc7QQzrfOydVpjOcJI9OW+ZadtAoiqK/hOlv0up"
    "LCSK0Q8MlFFXPSuJhhD0joHMqRbrrDO9BkD+No1+5pTM9HpBxE/QtnTISducCx+ik5MorLJzj90rCPGkQjKFTXeSwFGHQpBYBNtK"
    "+j6jo9hmQkIScURFSPQSpslojVH1l3kJcGqkyCjOqDV1toiG/BMflTcoRvSJE6a+C916Z6kXjvsn84FjHaMXbjzyaH3ss+VxNB8c"
    "W28Hs6B6bB3YWo59WLPeD07yNc7ng/fWCGu8z9c4GxyxGrjq+vvzwZnleVj2DMpiGhbaHZxrhVJvPtjFGEVQalcrFXuDV6jKQrNm"
    "TI0+2DnwN/0LjDL0qvq2sLDExltR1seWPa+wdMBUUj1R1sGy+4VF+RB5wQgLjhZDMBKFEywcLoIglBC4hAevHIRUFj2AI3jmHQ4O"
    "Yq+uU3w84QGfdXYcHFoHY8+aYLnTfLFTXgrvr1ByCvsbS/oFLfqeWfaldYxFnYKiTqbokWe9xbJRQdkoU/a9Z+1B0aSgaJIpeu5Z"
    "I2zWLSjrGmV3gFdGfModtbu/j3GePMsOmOc6xdoCd0ZOhd3BDB0U4cWzoCokj1HWMMXjprSReWnll1iNFn9BLYxeo+vO4e8JMYEn"
    "9BcQXzu0xgtgO0LY3ntz43AQUF4d2vNMSxzwcvgnOfjfEuR7+GdE4E8HwHw6qE+vGFB++Kgdf4G8i+Rs3LmidpQTiJwZEOcgGjkB"
    "Sx+L9AnUQBkyhnCx6N0bKbBOvjlNJvotyHIoKHlMlNxXlNxRR2HEmWMi34xso0vQsJxskxGKDNSywe1YMO4csuMzOAoM0jsW9HxC"
    "HNx0PphZJ0g3ZxlKbNmsIPyAgkhNjweTKxP/sUalTaovaPSK5P5V9aSQfMEtpO/CLSigUIw16y2cqCFRsrScmhqVRjXoUNYKsdb5"
    "8lrnwJ7LSkAsrVOgGbt5krFrUhffAzoGJdMC6pJmKFHkwbqAsmFB2TBLiQp3bYzbLMZd65dQlBCDFGBsj+LqAEJ+P8o6Nl6oMjvy"
    "FPeiQ9syoR0Z4I6c5najuQX5fgr0/bR7s/zQwBnWpXNL1CD3DqX+A448t4/FJk5UQ4v61iB/cD3IKfhB6U4W44okOAmOyx1EmXE5"
    "h5eXkCars7SFY3XEWF3V+OKxkg+2B7AydtWON2TzuGqewP1WKA+vDaSOYWHmWpNzwrK5ZwSJGbAdgS/pmrPmeAFVPHmuJwxV2him"
    "QjKTy+/nqwwXFCedaoT7sXPuxc9Qx0VofotAdrjSKRcQp5yy+kP7PwGmVm5dwP7w66QfQ6GSuQ0ynFbezMeHaiZzVveEfWlOvGyd"
    "kXPofjwgdtE8cuYilLNYEOYdRDRnrgKzAUt6DdXsHJS4SJmqKVn74BsUtn9DLz/WgR7OK+OHTbQYMfu3fKsXTJqC74Pmy3vIzisZ"
    "DSR0qyHyA2hqSTBsCEqW2DsCtu+I/pBtz+Ab1AW5AzW+qZAvWZqJ9zNvg8ps+GMchD//BmYumd8F+opRpjHrrq0JQbXR8Rfmm522"
    "1efJQu+qutN7RVj4ptEIF1wCzKRdSKqRiTqQmpuf7mR4ddx72hTiLLg4CzDNSU3NBO0YHs2dzhgp42WvZXj1kJJIZyBklHLzkkYn"
    "qhgqxAmpx7F8ZEKvhFHg1U+dGEa168fuLMDnYRSheKHrVcZeSpEDKk5a4QcsNoAa2gYTJUSNogB9JlJpggl45zv8FUUBYqVELgaq"
    "YlpHzSU/PKLHd+7GlbJlSAxhhioTddd804Drc8rcmjTzkUlc2CPPqmlgaX4S9dcVNMEktoLmgD9erTnFCKSJqoRRWpmgijMGP6sQ"
    "XtgTYc2y37599fTF3v6zxz/vPXj71uaBzRw6/2YsrB0Fzyp0sReR+EM+nrSGjB3aQJpevXURobchGt7cwq+m+KrZ/UhZ92ZAmGM0"
    "oBOOND/7ZKneK31sRkasegSrSUwUQMXcmVdkkhUygfOVFkmsbfEMkDXhkSIG/oqiivOXjsx+9nR7L2A+D1V0D/aIK6X0OTl7bRj2"
    "wyH5sa/DRRHf6eHYon+BA4wxJ8YcYEP7HnrSTDDsB91yav2qf+CiE3b8Z3DBhoXSej6rfWNXMtKPRQkLiebdUCwrlYlzKheHmcwu"
    "nZaGdKbvAaRK8io19XTW2Im/y3W6Ewu3R85Aaz2mZe7wLvARVUBmLlWt63kOdCGc9LQqEugD8ZN8787hLNYqsscFWiyBJcT44rau"
    "rRJtcdXZzaDG94RdWo4uA1CM/hWBF+VEOYKh99HpvQpYI8K9WD6dhNoblhFx0fAmk9EnII0A03gwXLAca8otZw0fWtFKcbWRpyuN"
    "nL+5YbgfmO6htshqWZ85OChJkrTX2+bQkSSn76iTlM4pFcYgc3+P5zJ4WIVi+s1QNyN38wYiJuJUWVJ9PIrRzUwuQl6ojCu5RR09"
    "hwxPA5I+DLnKYop00ZtXSBWmT5aZpCgBf9Cim55M2HMJWWPOrYzERwTuQokohdO64OKNDJvszge+jCbIo0EKDRXJq2ZvCRifcicd"
    "EPQ0Q0P95ZI9PIRKzBLPAcHQOSlpeesDnXgeALiHMNOxuouxJAzHIyAwEIqheigohuXRIyjiJcmiJKXneVe8ffIgspLNJ/5ffc+R"
    "RrqkQsaOeLgkuPTLkpwfjgkGUrNe8ULkQ3YAnau7BcuYY/cWXIApGW3ME1GlpnRo5DPx3HoSDC4kC6mewcX7hT3NPZaJYeZeZe/8"
    "XpWSt0shaLtUN9ZLdVG9lGzdJS1nRrMuaWNe4qxiNbikXGKHl0kKzF1yyaRUl8jh37pz5Ct5mw5s7ponn8DkskOjFOstY6f57n6r"
    "0NXnMg5IwxhOzISiIAeoOWVpyZwkXojgu7TD2ZrnzPt84O2Q8wImc6JDIxCCJvQALYYkpU9UUr6d82xkB8XPOXMLWOe9D/4I6gY3"
    "zLgI4vDNxng90p19nBkqvu8hNamkTIPCuJYzuFk+azhTgPKHvFO81rGyHOLiwlKBQpRmw8l1TansbCkAjUOWiFz0RYbpfD74NACn"
    "Z02COvlRtFmSe4zuDGBR69KdTONsPNQ6zxfN52ZSwqKkOd6yifKuMj0KfiHPkQMoG5oGFI3xWeF08HmgUYoSKw1TrFw5zqWQy7V+"
    "ZdAfK+ImoEeJJANSbeVDGoVWWA5EleHRMFizOWDNxZclCHPLT+QXq6y7DymswyNzMMjMPA28bCUBJLs/rF6PlaeqJdNRVlM4Cs1y"
    "cXJ4f+SUlNT1z8quZf3tmwlDMu0Uy6TktAuhR6rEHUYHJAu50Ig45RqTTyw4AUkuHDhA7GiSMOkn9seHYsdAgZDChAy4B+Kw/IyA"
    "eyCA2yWNCEEFCT4pBq34g4xcPZUntU5iFF+hvZd9PNiBX8/Ib4lZ1bXDWXFTwKsDTMNKJGeoU6F5bsGbPDFH0UA5JtE6zbHPMTKZ"
    "Rs8rj71842lSSQkOsicF+zAvwFyw3JgMM7zRnanDWgzo3wsiR9ETdKHEiL4io5IxlFSbl35FTMiqpcV5wm8B6by4VuL/5UmG0szi"
    "xD/NHaukC49l6cxdK282U4+qkPLTU7g17L+89+Ll/tvXj17+AEy2VFK0rd1nT1/ee/R0v28L58e29fTZy7cqPYwoThzL2nv6QLQC"
    "7D1vY++/r+49hpLenzMn4PVFGtTe48mPnvZtP7Stx3v7+29f/nAPPjFApfx8++wFq/b25TPMgp33/Yu9ey/3XvDSR6mZYlY4wgr3"
    "916+3tuDsiMvPfXQdekDKP72EUCC8/kokQlvAUqR+DRKefr9vYfPXuyx9PsebHOPZ9x7CL2y9HuT1It1rd3n3NyAWTZxQS6zFGNG"
    "zt4B+6r7UBOtIQ8vL70D+z//Ed/2IY8VipfvbAgSjIM4eEh2TRjvm+zsvEFY2yGjp0EDLu9SUF67EPT0Iun7VtjXcoRG813lW/ti"
    "DEcqqvf1+a8ml0x5B/H6+iEsHk+1QFshjk7xGWXS9+dz9oUG+ntxHMVV+1EItX2Uq2MYQrwWVNgIvUoYhRv0G+6RUqW5/q9HYYWu"
    "2Fh05FVECYvKO4iACvPtlVRO4BirHDvvvYpTyeGzWquceOlxNK7bzE7LoUjqVjKQsa8AIRoywoEMHj030UTmhZAbwhVWhaLB6GmI"
    "IhThmDhJsB9nQEjRmkEfEBE6gWUNiOh14hu9BPghAHCOU57UGC6due6A72Gge9ZQbwTa04CQYD5iRXeEcZ30RiAGycX/W2RcoUuY"
    "ngkveEY4J4pGb6QwuYRFdZ44UyGTgru0bfi4orj3A/tefET2+yi8uvN7ddh/5V8+qgH3NuxvXTY3L9utGvzcDZyTKWpwUgu3eFSW"
    "sDbk4xFvLJoPG46Taiowmt7VjGGqynF8TRoYhgP0ZSlC4+2E36XkGD8+CA+ZW3zpKgdLPwZyyWSEff39iYnJ2PJwuDsQFfXVIcxH"
    "g+ckWk92hD/pqA78xs5aNRlE9RBN9HAN7bBW3EH++cfVppZmHMk9gwYF2FUX1TxqtQtuq+LWdoQzfxaanBoOEAw4SWYSjICDMRsE"
    "OTDGgxm3JJ5goDHXGrNAaZmeJ7meR3AhfjfnPqxJKbhOtxexroP6hIIXqAKRWSCiAgKDsH9Yb/0LdUBlpoDhRM48RYI0gi96Rgw2"
    "2PuMRsZuVY/pxywlYWd4SnCt3qdiJtNeXFha3AidforFPLfEKfr5Aq4sY9fQFg6onzrgvwSoBwxqwX58SpDRLfQq0Ep1EgW2JY28"
    "5ILh6GdcU24YQjBhDoWs+Ln3orVmX8bHRINp/nNoBM3Uo2b2VwJ+sBouaN3sXQ32poK9sRT2tWvAvrYq7H5oAJ1ZNZotn1o72mmC"
    "R4geYkWEVSRbeFVDulWyODea6TOHpoPGofrdPNRwVTDlQyyuEPTdQMMd9xMrcrAxDZVY8TvyAMmy5laQLgTtiqvuO33evO9SbN+7"
    "0Q4GZg8D6OLoRodw1+jgLrV/o0O4aw7hLg6BXUaWLBLp+aBaGMORhUF6QA8atZqVd25OPJIsQ69jsEfwQ8W/pQC4elJNAAc3pb8d"
    "vrVS+NiN7W8AsHDpc6Douvh3wnTXgAnNuI7Q928WJoPh8w5hQc6tF8HAJrdF3zLvRf3+iFAsvhwcW+VCejYaRWcbif8XgNSvMN9i"
    "G5C0Q/nzf9E/9SlasQXONPHhoreBLpDiDeadVmvICf0T0qvuV6Yb7MMz651NnRCuBvVWUvGAqm9Es3RHVhc+7voV5gxpEQSBB3fK"
    "a0DAf3vXguE/77zzSYzSqsXjU/Dg7Ur7xP87iv3xBt60A6wN98ekX2lMYgXCXP6C6/Xyus183VXBlci4MsDNDwC4UQowzLHwmWVl"
    "Eyrfak27sziJ4n6FyxdVc1P0UgVL00Nn2dAX6tSoXPR1t8H9oGlZC3qXT+t9CYeCIpo6rp+eAxhp9f9Efp2n/l8t07ivYxk4d9xy"
    "Hqvrw/2D5IG5ShuYpVVkYRuKK+H/8RAOy1rFVR445xsnTvJOJwSO++4oRn3BfgWdlWxsTM+ozIbKsahtTKyrxP+raTCQukFfFaNv"
    "HchplPhsj078M2+8oy2fKSwP9U2uS/UEPvxmo/Hv/JhVavFAr0S18hXVgOgxgUZQH8+YIcn/1VDD8tSJx8lCEK5CtvIVrwVCIRUo"
    "GN5CGqCvDOqbhZRYiQbczKoShGK1ITF0rTykDwVr6bgX4EytFBYbxBvLoVxlwRZXrrQbjZME6OXIdzdG3l++F1frzW2radVbLauZ"
    "Iwy5Vq6yYIsrXwmEwpktGdrC2ZW0WaMeNEvSq0glwQtmtVHfbteucoCWjPKifCF8KCy2erT4i5x2ffOfkTPygjvHXjAFvq+ywQOp"
    "fCNEGH8F5oMGOvbnTdgySEpGGo98KaXYQ11Qngk9P+8XZHqZNs3uDIE0XFNYGaYazGGQvvaGAgYZ8mVu0Zg1z9XGu40ZXB5FRYs8"
    "ALJa8UIvgdgMKpDFg1honcohp1kPlWW+CJmrR+UIEDULmcUBM7mq4lN+gV+mnwMRDxEBTQfNnfQ7RwjldedIfPgyj9wd0TX2Yt7X"
    "U3fSf7eGgDMGMIrD1hpKNV0f2Q/ct9cBej+SYVdKvS0OSzw1QiPLqqIHl74OUzFAhT4iCcZl2CcF0nlRdOQfAlPcBTewV+TKjTw4"
    "lvfIXbiE1srOHZVTR637VzS/bG5fIyjy3UBtXYBG24tpP13XvaS9Vs9LtDHWZBydy0v1suHxNyX5hplGz4XiKD2ChNJTmNgT4mUN"
    "H6RY47HWuGg43sm9H/7nP1rj7MFPvA5UpLZqhRm7SKuuaqqFCxoyiUCfOQ6rGdv9ew1j2Z1wt3n7tlrr5KaNjWmop8Jc7PzpoHgN"
    "/+r2nT+jk7J+OkRhzh4SNHpK+ilAr3HSY/WH90/WFs+qa030Pf+MBSp8ViV5tuUM0Nn2MOM/WyjNRlpITCsh13Oig35EgQv9E3I2"
    "k6IjBFdmX166aK1eP3HCmRNY48FMcww3syYDZutkTQcT1SRTnHl762J9/adgbvcn1gl2MLaOKcwfL8WtX06sI2wf+7beDo5y+UfW"
    "e+wkCl3POh+8z+Wj8XoK9DVOUutsMNLAG1n7GGou5JofaMC+n6u+b+1SIa7wgfbpu7lC5MUES6GiB/ovCb1cmdCzTgfk7HWaoCOS"
    "U1UCCOkp+hvRn+nRrYhOoti74rXXxQ69Il+wV0ig/T+T0qeP4fbQvUXEDVinMLkRzMTl5TFMa8TQenl5vuNzo7MkE1yITeVBudmf"
    "O//m0K5dXiZadNX754/G1YASzXBKwnDA4t3V/WQ3CkOyxru8rMYcCAwhar1zq7wUNxSwhRWibfnjfsA9Or21aAzoqcs6G2IAQGeM"
    "2r8Uo4k3UOvzdBa6affYD1Se9YvqyC4ep225NR2eSA0gClHRZlDAysTesC41glxURPIwxa0xExmofHk5qMKq+CmsxpbegGgbx7vL"
    "3IQPgJiy2nPrQu5UOhuYU2RB9IEbWhvfvg20LkJFX0DUsUUQTC0v6PvkXSK2ZgS1rq6QoDcL6hb9PaIdz54cL7q8Y/hjAeUy+OP1"
    "BmtNgRXuRdyiTiLP8hOmINX/Ho9o7TX/x9WY0B//SUwojZmOh18D65fA+i2w/huoU+KW6eXUn5EGUDzjUeNT8cOb6YEm8OtiFX2c"
    "scdAn8WfVidHQsoHsIpSSzj7Zym18PHklVp4xkdSalGuWmf6fUc8VpH/2esrrYUi6iDxfswHiXDrCGxsgApYqIaCppeDqqZ2VSMN"
    "KwuD0TXIonNnreoO4LLksBIhV1NBBHDryViQHHE8kmP8HeyotqPpoWDH/sCTiia8/zUXiRx/lRUPLtFAqWTx20A1wjemSLzk6opa"
    "AVfU8mX0mUSbR9qsRSp8Bf6Pndk/+PIZzT7K5RNwtvzymcw+6eVTh+nTXT7FILXLpzv7dJdPd6auMsGs6PL545LLZ6COgR8/5uXz"
    "x8/k8jmbmS+/wPtJr82C7sBh43l/edXyFXkRO6d9PodmnRR13Rlb8VpYsY6cxCNTSoPJYbPm1cfC6439r/p0g71Rbjiu6yX0pMcl"
    "j+wVVwoc3cCf9ito7FJtVOg/LmWUTydT/tzLYrX1KxsyJSu8LH4g5bGsZKnydzj1+OOMkiiYpTz99BhOqI0EevOw+GnsTHkGf/NB"
    "gOb/+hd/UUEQ+PD5mBcCthGzgd66wOsMRT8bOTEL+g3LAlu2hSO6F4FFBtwe2Zn6PNY32aFecO44PzMfIhqo5iq39Mqtwsqtw0Im"
    "eF6rvguqvwIzMoDFe2Cjvys0Ya/JPf4KmZo/4aRGR8oW0Hxu/YCKBGTfTE7m0UYUh7q7v59Xs87B29DhbRTC26D7rm64h80zhVV0"
    "iOPxmwdhOt8llrPS6/dshdedItsugZpWC1DnDKzxdYFUHT3JGCylXA7gMakN+f+4dQHz/Et2ntHBVc1whEtWukVL5YluFShnX5jn"
    "SsO95fW5gV+uCWlet6QJZYaXa4LZlWXrG+qKHAzdWk5rhopmjNKoucy6Nhoz7ddka1m7qRvbFxT65INkSGIXCc7sz0RtLOEs8PKS"
    "nDXBtoeF85uxcPjaQSqBoslc4HLu/MHUPGI93UKf7C0UbGL8WagdAlSZuFm0XrmjL3JfNS/2X4UuJK7hwkpRrm/IuZHpRgydV0ln"
    "DJltUTSXH07Rdwo2mGZLZ6zOmrKz/zjAoJ+fJ1lzPhOEQ7mCCGWCislCyCsRUzK0mQdXhn3ArI57nggrAJbXf7N0SSxIRjPFkkTx"
    "N6zHLLlDiw2My/bpFyLz6x1e15FdTCswwhXoFDiyCzUfdsJxbJ4owomMhzIzM61Z5CMWmEH+IsBYFC6LQDI5t8YzCm6lhFGT2Ury"
    "ucnsHySfozErxn36T76nn3yce/p0lXv68ae9p0//lnv6cf6efvQJ7+lH2j39beE9fTJbfE9/q+7ptDE+1j0dGv877+kI0/vZ4AIm"
    "dBqQHSxF02VXCAoARt/kdjpMWUpAdiWGtZq9T7/hpol20dIWzFYG1Lqxlf00SivK7FpaNNl78Iu3wa2DbGFErYxuqLYnkx8yk0VI"
    "rbCfNlp12I/hOg/XDSe0yQhDfVeimNWuYGj3Iyj6PT3Vxbw02jsYSWYFbqtgo8J5xU9szT5ApKHPSFvXy5cZI25ZrdTjZRZplNs8"
    "SKi9i//YzK1x376H//B4J/eCoG8/wV8V+CkSw3OZGEJJuLGjJzCoOR5X8BfGSsAXLJb6gn7zDJR8TAH4X70ES+EqRGQCKMdRlEDp"
    "XfrXtmZTurjbr6bMKt/FVxMAZpf+ZW730JZ/jNPOf9oWvjvimrOfsx82Wjt6+/5fFOA86R/Y94HB+Qn/PME/3+Ofl/jnOf7Zwz+/"
    "4Z9f79uHgLhz5v3gwN6fhfCF1SL+4+XMS9iv1944FL9fHs9i/vNh7LMf+w7sDfypWtw/juKUNcvaZA2yxlgzrAVWXav5xA+pHlWj"
    "WlSJ6lAVqgEVgIlNjwX4P6JeQUxQeaOY/3zixC7WuQf7OaBvTP1xhl4N4R9cBPa92dEMPZvZ+zBtHm5k+P0Mznz26ynMLE984Lns"
    "p961GOePuNaxb9Yt61TvkvXIOmS9sX5YH6x5aJmtkl/ZqqXflV9p7bKMJ9ixzKEvkYUrX+bgB8UpeA/NOmPIgJvoez+aJRWWgD7m"
    "z1KR+RR+ywysxQCQdRgIWINlUHmWiKU5VLI4hwvL8yyqwJOxxg/RTG8fP1l5lkHFWSK174ezVB8DS+A98EzWBc/AWvse0MSxVosl"
    "sFoik2qJDOekbzsnUBv+ncK/aQSLsm+/jGiZn3reux88hxz5vX6HGy9O0gfO+bPJa8jpAyd8HJ3SGIkWEabgAEDi9BDuEQ7QgZOT"
    "O+PxnXNqzHkHzcBfmxQQZtDlE/rXBo46jnCL79O/AI6TJKdRPIaT/QRJyx4pm8IpxdOBukP6OSPXT4AwO0ceEfDYS9DXCXO4iz79"
    "cD/IAheNuSzhxF7Fee/4AYsBwCwS4Nw2CgPLfZLwqO2e6HU/VxQ6FmWoiixo9J4HDwkZLN/EM3vFZHEyZfOhEcyuuJTMO9Jz5ZiE"
    "IzqY5BjjdwFf7z3G2whMb4x0aQLnn0h5iL+hSzideQqekfty4HhS9+1mBf9lX3CC0fk9pzQZ14xOF/iTQ90sLCwgkrGIG7DjIqDT"
    "YsoXsVrObB2zFQy/WYB0FGPbT+VvgIMkyy+jKSwn+lmB37DkgKxR4hM8uWTSK5Hyiic8iE5DnoQ/WeL9KMUIYCyZfYgWXwIP76U8"
    "K40q7Fvk7sOOdj2Vy75Z7j2E0qiOaMk0QYWMVngh0dIUJp5P2XP4WbnAhDnfq89V5kP8rmAC8DOOkfXYkTmIYC2HaAXLwenQciSJ"
    "YbloVfTci7UCLyClAmx5ZUoF/pidTF9GmP8AuPUxYJaX+xEycDwEvMjTyz9C9rGoMGWIdQfdUZ/amhVLS2a90tYasxKTWXv0SYuQ"
    "22PJrF2egLsAyJ2gOeEM1hd8c56xgim2deyPPb3ED/BtlmA31WdTdpfHeaFMkSAK7NJNHNjbVBZRSQD+2Ffj2oMPAM557+EvAAvV"
    "SlgiY7FYMmOzeEbgJ+nPvgctPIZfFfwJnCuwNyzxe/jFE5PAxwNzH//hX4z9RwKgvmDJ/RVFJ49OiBD9Bj8r9JsnhyItZAnPZilP"
    "eYaTGEfo/PQFPRDBmPCj8oIFd2FZj9EMSeTgBxsCXxfMhWMFh4LeXhkKiZ1FJ6nPhANVlB/1D54Gdc2pkwWfwmUT/tZdOOG39NtE"
    "H+SbSRRjX4cWXTR9l1ouKoFf0leT8aH7YcIM3UdT9lsve0hnLHXInTJZ6if6Z5KfzC2T/CRnTIdz669H6F6hf3ECB33QbzYbDYub"
    "UvSbXhvOZ1i8+CONoiD1p1RibhnOZGF74R1vjCf+VGrLTlOJbUDKkbfPjsoE79yU8JyclKFpv5tM+xdMBVHo9VjnMy5p0mVpI0OQ"
    "dMGu8v1XKT7dKukiS64z8aiSctRvCTEhXvBRgPUe1mz1fGaFNWt/Vq1Zu9g8fIR0lz2bUUhkGZYc1cMmgXAUaZ3N8hIQTb42rFfR"
    "VS01okXsNiVhXAtZe7pA4S8fwJB5ddPCy6w9Cep5D5w2cx2McUHo4cMKB6/rpmh9yAQFr2sUj4rFn+W3fItFnmXOi1ECzPGGQbu5"
    "gDgZ8MmpogIvA64mtKwoNCtMIE8QmrweU4ud77xmb3QxC7RxIh44bQmAFrRkbiW1msVr+NkaAsiyCk62ApePFxcnLFZzhZncHAui"
    "hirgu8BtqUT4fL4DCwLmLeO+VZeIaXqqK6xMUYI5nk1JL5Up7/mo4yqwb5ky9/GMu63jG0LAcRF6pz8zX2RWFIzZz3Se1X+1xp43"
    "ZXqwDvaSf4kT/daZbGe+pH8uAbo+GNESMLjbYw0KX8M0mzXhENmStQSduryMq4bKbRZ+czYLwffLwG9S9KDF4AtAjBGEtYs18nSh"
    "j/H2bQQ1C58kuAtBDBdgeAeoFz2r+ETI6KejfkbqZ8IEe6ezwQWptwLTbk4+o8lu9f2MJLhz6+VMBiYfB+yXtYdywShK8fIhbGUf"
    "cFNZ4B4KDGjnNoYNCuFMv2D6M69J88RGhZnm9KzSsC2WTh7zoQ2XaXnXWSqzc8ZGjtm1lYUawL7g6K+fYEQDUcY6xhNvV88XOczU"
    "ckHWD6VVhRKO3aw3W90Y74JoaP6aKfnYmw05ghcO3H3hdiMTxFBXG6KlmbZqZWSiGOD9pcXYkFYt98NqjU4id5a8QExcMOUh+4KS"
    "6qSFTElzm7+kGVmUNCc+nEavZYmRR5MJ+jK1UUEKmXJnjJyw0Qil4TpIo6OjwHsEMH7ytTBndzBY/NH0vjHl2SmNKX2eWwhzuqnh"
    "VsAb54pt8OksqNJA3phXy+6vG1t07sJdAbuY74v8D4TugaQYRk/4Kl2f+F4wNjsTDh/ulxSWDiHMtekHC+qw3KIa+aWfr0YLqajy"
    "Q1ydSyqzFWxUNmdFx4M5MWyvlxXmUJlVqLfSKhwWs4rPzCJKK/H8bDU3X1JkiRkqaExOnlxFGLzkGE66wr613Cy8zxdWFEAXNaAR"
    "F1leEBexqn/JwMFS62eqxK/FJc7n2bOgYILlvi6kqJnpKiGuRaXydLaoVJbklhRj2SX4KqbLRQyBVqmENxCXVJM88NQ6E+8s2kDZ"
    "khnqZk5GcWE5IW5xm7mlk8lXOEABRv9C0sYL/BaLAxo4cqYiEX7S6Olq3WcnnUFLqBTLLqIiQu5VWkcUKK72cGF/sm5BxwJHenmD"
    "/uwWFGDtSDzy5otKyq6zhR+WtZ0BNndAGYXVXGRWhl4osyzELH0PKJhm1qleDROny5HFiimUKVayoBhm108pv3RMrKQc2dwac5mr"
    "JCutOuNbkxOVRMezFSja02YpN3M8ZQoLDma10h9IQW+YJ71YQhXzpBBYsmN/KvgxOQ4D+HpyglNlPPZcLFmzc0sPs3ZBQaeAB6a+"
    "8gQkmcUTOP7qrUYjuzVF1hZm6etlVNRAkxrIXz3MDgruHKJAmwq4mc43VbNZuHpai8Uwzyle1vLB98oHv8rQt5YMvbds6JuFQ2+X"
    "D721YOhNNnQY/DPJVOvb2eKGJ/wLaQcqVcDNlb6LOf1ivk5kl2zJkpvK3PLpWpaoXufWESebxZcRnVrKW2Cj3usW0yc5xHZ2iJzE"
    "GQDUuwYI6pbJ7yZngWy9Y7TeybTeyrXdKmmZdwmNv1MXn0V04GRs3qYa9W6mc4EN46zoodjhxA/5bU8MXwxADn2MACS8HZ6Gx4De"
    "/CYXa+jNtbLttbQZ0Stv9fKVe9nKYjoR4dllqSoWLOJikodSVifO8ow8NbeWVXoIPGii3eYT0pnIt2RSvkLCBZVnZB+WqXoUe15Y"
    "7xZWpGp+OImy3b07X1QDQw9n2eMY5YWLKo2xQJypFgOXtKCOQFAJNra7ZTUFNf5U87JVTlUXz0vHqMjSaFil82LWwBRevnxWzCo8"
    "kdcqnRazEqbwGksmpQgRrCbSoHtAg+QDTYYQ4VuQR3KiM6BKLRK8nQDpwx8n0MUm/oDdbm/hD9i5dhMLIc/ixU4w7l90G337/3nu"
    "ZDzp2hbsFfgaNyeOB18t+nJ6k/YYOmjT16bn9UY92+rQV7szbm9v21aXvpqN0fZW07Y26avR3d7chLwe++r0trpQb4t9bXYnnU3b"
    "2uZfHa89gi+CpdFqua0WkWX0MM4AnDQAwI4E0J24Xk8AOBpNegrArU0P8CcA7Dhjb6shAISWu11PANjcdNodRwDY7G412mMBYHNz"
    "s9vuCACbnW67NZYAdltec5MuikjOGHy9iYcQMfgAna47EvCNtyfb22MB38ibtDY7Aj6n7W22uwK+rY7rQsscvs2u026MBXydcc9t"
    "TAR87clmq9kS8LUB2GZHwNd0Wl6ja6NfZDG/E+h00hLgAagtryXAm3iu4zoCvInrdJ2uAG+y1Wv2mgI8b9KB/xPgjd3WZmtTgDfa"
    "brpNV4C3vd0cNUcCvN6kOW5K9HW6Dafh4IWMNpWAcDLpoS4Hh3DijcddBeG45ygIxyOnJxE4GW232q6AcLLdaysEeg7MqSsgdFud"
    "ZkNBCHOvENhzW2P6YhACMhs9gNAhfQoJ4AiVKgUKJ21XrsDJ2Nvc0lA4hn2hABxNWh0JYHfba4wkCrd7vYZCIayyxrYEsAX1PQng"
    "VruLsy9Q2HQabQDw3AvQrFdOsuttaRBuu22FwklDg3DswX6UEDqw6uQa9JxRu7ElIHSdLafRERA6zc1WQ27irW5nrEHYbE80FLag"
    "X9wjqecE+h52BHyuOxlNmgK+7e3JptcR8HU9zxnLKW6Nx53RRBKZzmjLkVPcGG93trYkkZn0Njc9uYebXa+7Lfdwu+Phbud7uAP7"
    "AZ+W3XMnVETQm0wkfJOJM/EkEexO2hNXEsGetzXZlvC1xm3PE/A1NkebY7lJGluwE1oSPq/X2W5I+IAW9boSPiCCm20J31a7DVsN"
    "DsJ35wp92wo8rwE7WoI3crzNiSQxvfGYgOU0ems0nmxJ8GBTeNsSvBaQnJ4Er7257TQlje51t7ckeA234yBqBXitSWcbBQ34tsnR"
    "N5lsKvjGI09D3wg2LX4x+LbbbnciN8hmA5DrCPjaI2haTm+ru9nGTcdJ9Ljjjbck+rxOw5lI9HltZ0tOb7PX6nY7xBCM/aNIQIhU"
    "UMOg18MvBqHbG7cUhE531FEY3GpuuQqDm+3NzYk85TpwjuFZyYl0u72FtJQT6V674bQlkW62PDwdOYRec9QZAYTv/SjACIBsjnGZ"
    "KQjH3rbC4Xg83lQQup2RhkOntzVSONwadV2Fw57bdjx5jGyOW1tjSWS6o1ZzJM/hjtscb3cFhHDIwTGND7+zGBUIOIQOwCghnLRh"
    "I0gcettjymMQjrcAh56A0G1sEUYZhM5WtzvpCQi32+22Jw/ingfHtNzEmwChsyUg7G413a2egLA9avQ2cZYnM/c4QWVaBiJwChqI"
    "jg7ipDtuKCROGs5ITbO31dueSGYGCAtwEpIONlqb47akg62m68izeGuzub0lF2Kv0XR6EokdoJ4dpDNTP3yn4GtNFJ0GTmai6PQI"
    "iNCWhG/b2VJ0cNLptXCyOJ12O1vbciOPR61eT27kkdfc6kpeZnvc7OF5xODbaje3OpLOQFu9FqIwRh1fedI1NWZh4gFh0piFMeJB"
    "nCNOB/EgTrpec0ueI5NOe6J4La8Jm3dLg48ObQ4fnBttSae3tprttpzijtvoNpHQJOglXwC4BavQlQA2YUVuyzUIm2wimUF3NO56"
    "TQHgdscB8iL3cafX2ZJHcafX7SpuFYgvUGdFaVrbbcnNNCZAXdRB0mpsNnvErTqSUm8DfIpVaMNylAj0gOYjReN7pDnujkcSPtdp"
    "O/Kg2xz1Wsi6cvhGAJ9cgO0ewCcpNczWNqGMH3vNrZZEYKPd6DWRm/7LD121hx11EAN0nYnktWCyO8jIcvg68N+WpDJN+E9SGeQM"
    "e46Ar9uC/ySlbuOgNwV8rV6LYYzBB+S0qbj9bfgP6WDozeCKFBSD2MX/NBR2keRqIGr8NP4nQWzjfwaI8izuNPA/CeImY2Y5iDQ2"
    "CaLDGdYkxcuWBuC2AWBHAtgDACUzMwbCMZZrEA6p1rZkFnrAX2+6EsAe3Dk8CWCn01CbpLUNsKsLidvc1gB0AcBtvMELrbxizR6M"
    "61Ekbmf6Gky+nkSBPy663pvy9Jau4kEKkXP5ZvyMu8VBoRSTt+mSIuYj/PtZSlZy1I6UOOBoLvjNtE6CCkKvTGKinJaRxmStbSON"
    "iWY7Rhq7m3cbZheYtmmkMWFvz0hjEuItI42JL7aNtG2WZgyDSwDw/eMhPn/IB4JfNKGgepBuaK88RRI6vbIQ+em1271CEZ9Se9Ib"
    "2CroflPICJcLPPMrqSHXEa0JsYw0F/9qCTVyC+gq2miZR9oGE21WGkLmSa+0tLqEyplWlum3aOUrXMwtXnKzZeVErfAaZLwzljaU"
    "1T7LqwAtwPzcwrgLZZu82UXlWs0O52JlZAHDnHonHzJ+1paSUs9GqLTO7AGugA1R8ZEmrZfrda4pHPCQNSuI58Via1Q607PKJvwP"
    "FdUq8dHIqTasCv//erMGfyuADCq20SosggxdNEUgrvYwIMZ7w7Awc4HFkJwFphpkKwtJqwHNt7rYUbcUli3IaWLBjc0yYPSFd7Pj"
    "LH5H4ALT/gXnXScTYqHIDAZ4Rv0cYQn6KcJS9DOEpegnCEvRzw/RsDo9WIp+drAU/eRgKfq5wVL0U4OnsDNDnovZ01iI/5lQmT/H"
    "ybEbT5KiymbBk6TI6zGZ+zHgk+O0UPTfla+w94uyzXcWo23z7VZk8YdrRsr0Hvnc03/1Ti0vG281smdqqVi9UBUx86qe1zsUBbqN"
    "BVqGBYUelr5hUyHz+bTgIfl+YYGOwqFZIMudFeoB5h8mzIfvrKqfgrhRrNxnFijX5cOO2bKbBJHDbMKK21D5D4sWSraRe4UP69mm"
    "uK/oK2oWIrtajH9FyxqV/9eA/7Mqxk8kbEi5Gox2NbesCv6v1Uby1ejWSBh6lqrdbE5DoSIBIxakE108XKr1pCifP3AqpqJsh5Qr"
    "RrAdXbxoW8aKMrSK80rbTM9VvgzmD+8y2K7at34s31yb4ni9sRYF+1quOGhOQaGeoCTXqyoHqgoLNAKNmTTIdn4mczqAqoeFin9Z"
    "QPS9l98enXLtny5XIypV7TMuHuV2BnOTa2E88LJJWaAw1CzfHMtQWmDXYBa4HpJKlJEEAk02/ToYNBn2mwVPaCaUc3oo3NIZPfrW"
    "+TxK0Nk8StC5PErQmTzepuLxKEFn8ShB5/AoQWfwKEHn71jCEvauU8TeKcWA/HEhKrYXMHmthUwegbBx4p9V/bCSwAFmVQxwLD1M"
    "X2Wr8+9aASt4tUZ6m/9WrB0dma1u1xL/g7tezVwxxUWW8o+b1+cfma7MQg6yt4yD3GqswkLqpcp5yK0F5/HmMiay+8FMZLtM6aiU"
    "hewsYyE7K7CQnSUsZGcVFlKS3yVMZOdLZSJLWchSBrKzhIFsr8JAbi/RrV20ZHsfnYXcvlbvy5jI67a6iI28ZpurM5JbXxnJbjkT"
    "0vl7GMmtZYzk1idnJJchqYRT63wiRvLDwCN1yj/KVLrL9OHn1hNZRQlQF2jj69tBF4df6YGDrZ1r2UavNi5uyKbWK3oyPmE2bZnF"
    "kS1D4dML4SgsaWzO+Wdr75N4sDzJ+9NKA4caT8uW0gJrJ1oY3tg0AW+pZxixVm7CihXBfRYG56/zFmTqadCwoT1hxmr44FJqSQuF"
    "loOhFSqCpOiNUq8eHK0ACBRaDohWqAAQbi8XMHqlP0N16RkqdvzEG+9Lrq2N7x9lbxQt+YyhsXD6G0anJni8bnGBVu0GzOEW7YE5"
    "kKzxkac/yF/T5LfoKYbTyJUMCPI8oyhRdI4VFmRZGbJXxvkXXI0WdlhYMtPjMiOI4lt6rlTxhT1XTFsYZeoZ5oP6qrYxH2wVWMy3"
    "NpddSY3WFzyN3KTRYREWzXazOFxo61OAunfmY1sus1eEskyDuczNclTJJt0F74Ay0UCNTC1CigQpt6iW2kzlscJyS/HCsoswk2+2"
    "ILscO3rDN4sfHbAshpYZe+Xxw7NLEcTzizBU0HJRfjmOjLZvFkkGbFksYfSN7CFBqsalWOLZpVji+UVYKmi5KL8cS0bbN4slA7Ys"
    "lpbYAOaRpJ5dCzCEmUXoyTaYyyxHjGryZrGiQMqiZCUTx/JDbXu1W3fxoaY3Xlxg6aG2VSpHLRXgFR9oS44zBmoGeXMrmqUYtm+s"
    "MWrlvFi3sZgFK3oiNl4cyjRJDd7keLFuxdKXtlUeYM03JXWIlZ1V3YVHVbP0qGoVWKfyPhknUcwydBdwDM0SjqGVM2vlHbHzp/SU"
    "6S4+ZJrlh0yryCqWd8rIeSnR7i6m2c1ymp1ZRxqxVNSxmAx2F1DBZgkVbOVseLuNjA3vx1muvUa5GTC+ofjhp90oPS7SY+8NN0Yr"
    "PgU9+Jh7/iPs7I+0gz/eNv04e/Gj7rmPu6/K9k5AVl/uIpFEmbyiTCggZI9MJeKrxOULk7jckDOi0QLOcgFz2lvKnN68r6NFLGr7"
    "KhKXzgKJS3uRxKVVwj91Fklc2gslLq1ijyIZFMnkDHpkeoncpXNluUtnodylvVju0iplZjuL5S7tJXKXVpmnFhNPeoaJKT2nVAbT"
    "uaIMprNYBtNeIoNplbPHnSUymPYyGUyr1OuMiTEjx0SZkVUukulcUSTTWSySaS8RybTK2fvOEpFMe5lIpvB+UIA0IydzAuhZ5RKa"
    "ztUkNJ0FEpr2IglNq+Ru0lkkoWkvlNC0il0TmRhSySZ6VHqJnKZzHTnNKsrnCw7C1oKDcMkx2Fx6DLbKmcbiY7CQzht5C47Ba8tp"
    "FmlcMg7F1LncJp3LPFKv2g5TAC1m/3rXv+blVDwb9UanEOCCks3N2tWu1p1lt8IirKgj5/qYLWujCKsFDxj6sVd69SzqV7AW14e8"
    "uIUiuHPPUoqxKb3dFvWoHVfXB7u0kSLIi55DjFOz9A5duIvUyfEBW7GskcJ9WPBQYRxgC27qRZ0L+n598ItbKII995agTpfVhAFL"
    "Nep6C06NBV4Vl8oJPqjjzUa5U8Zl4re/9wj4MGneikj7Qgj3502eP38y/EXQ2s+eoH5cwvlRiWMxAfx4MlRo/HlxYJtCVd7l7hXK"
    "HG8rqw/U/WsX6/7VdPuPEjcJ5JZlfK7rIRs+PKTfDdfhFgFmcuqn6MlN9wtTEA2rKzxw8OIL9d0fXiuYmLQq4fAJpzPor89FHdzH"
    "psuSZsEYZdkSB+pCk3ZFdejPNgxBgaKlNvRR+d24fEOWi2tK3hmWddhb0uHmyh1Cl4++Rpv6Gm3qa7Spr9GmCg+Pv8F84e+wVJgv"
    "CAFUMF2GZcr/dDwu6yQa+YGHkbQxSnvGs9vXGF2fb4yujNWZXtKwOCsdfd7azMq7jqOQ4aZ1Ydk+mluPV4v/Qp7vTpeEXbFW4maA"
    "0XPfZZZbLvgGK/PDigodn4pB+tvYlCynwVG4UDvFwOEKSiq8/MPlDhR4yQcC6ytCfU22aiFz8nneaT7g3Bd7zNxguTBTZZGUzNhW"
    "ygHqAt6Uz+ZSXSF9PS0tfBWGF4edGDGk2FD1+FwwsBcllKpJIWBW8jl7fVvlE4p8d7ogAlRBTDH4C8h6lM34LBbtQr51kfHjFUJQ"
    "cf+HxXb4PFPHkbswiN6C7rcWBLIqbHlp1yI00V/XiyQfe+9973TZbv0HhJCcOiHaFed4XO5gRBHqEpZalNOzy4xveV+jK1u0cDm7"
    "E451YV9haLAFXSz1YLKkC+jkPqymXHi+3P2B3Kioq44pSRRBAX8uFiHl8Lr8CmROQU6akS225I6UaU0u4OUr5Ih7TEfvu7blxHF0"
    "+oyvTBXXTyJDMeXZBjMXp2YBec7cMkuGiI4cIgTposhvAQq7S/u+Tg7O6g9XltbnQlXeZKTM/Kxp/iLkxH2AV3Pd/0ThrTebzwNS"
    "l/mdybqzKLh1Fohos7W4SnbhZTVbtvDKVgxG8aNNSef5y2e2YOkFNFvwI7lFWTjigovq4mFTBXPsyttO/6JQ5FHgQl1vl2ezprn0"
    "qmBkRrFlgzMKrzg+o05miLpPllU2NODk1bVYEhEk4Kp0Zeyk8B/w61ejLNz7SIO/+DXyPuJZRAJi/rUsFt2hIp/A8B5gvJFV5Fkg"
    "xrTrBcEq48q/3YhiBa8ZV/Ej9oEIMx54TZBW9x5WckIZqP4UPORGU4+bUnw5/pAph/5mJ+FL9cprBlWIMVbg37gUPuocfybzx17o"
    "+a5bbel/hL3PWLNV9/4HbtGPAD9byA85g5lfyYL1/CfRa3zueR75YVqq7SLw8sLD81rpPcj2Y8p4lFOMoGVbrqsXxal5z1/J3Rzb"
    "oGaprLjdCiIHR/soH3UdiNHL6Ogo8O7DzSYq1B9agez8UFqp3Cvlqn70jD7KpL3izlQYIKfb+PfnK5yY+AHtIT9EO4Pv9SOS32f2"
    "i5yrfqGviDzjeaFr15uTC1zx3r9MjLBcLrDyTV8RiVngrchOo0AhAZYZiNLjq73C6lW/vrre/KvrVS9GN/hMS3LNIz/E3l9G05XZ"
    "nJKjVGvtfgQnwcmHN7hAPL8SrohPhsXrTxfEBdIZPblcCx8Gm0WC+nID7hX6374aANvC/a31OvNKtFsQoM9Ea3ZlGLzPlW7Oi1ms"
    "JZK6K/JhWZjL/JhfH9CFKNMwVADK6szrzaGM0IX/XQFli3b51aZp6R6/2hBgIX9/vZenggeMz0d6fJ2z/fqiqysOSpPrNyoifqNS"
    "KTckLHll8lJVNu1Rv5V7xm/rkUg/VK8kU7jI+re89Jf/FOmH01m6mtoTZ0qewCweX/Fa9gESnoLwpFfR3xdQ/+o58RcE9BGPNbDK"
    "1mQ89gJSMHbOf6aHdTj1gdyqOKuMalqnnvfugXOeDwWb37JlSMFOMBD7h8sIsxdpsvra/3ukiaWKOgZQ5bLHcs2XIoFAEfY/T6Jx"
    "giRg4ZI6YUQiJ/NafQecw4Zd2MU57egP6GFEAqaRUxAEmrNEq10LUv/Ee+6777wPa8h8jWDAfW+aQRVdYNQR+jFded+kr23AWDR2"
    "zhfaKLmF2ijirrRkzDfkTOsmvV0tHvMCO0cY80+LlVaY4ssKoilecLHCiqFGUya2MloqZ1xZMSVry4Vcz5Qsk0ytZp7IXgDyqi6a"
    "wonZzVXTtSvaR2jcHPPc+rP4Sr5IJHfVi6wZh+o4iv2/oDgGoxIkt8nYeZ3Lb3IloDyaFewwwtR39YZEvRx9LGxKXiOgrR8LV790"
    "9FJRf8gS1lz7xcUwnEamsxXMeIX+zIrXuFwH7EWg/Tkf7HPr17+P1twc+SikGJ8JwSgtOrd+AdynURQQR3JD1/ZVeSHe76PrR5da"
    "bFT/TzI9s8peO+Qon13XquwGnhluUKB/lTPlE0jGYIv8dtOanisS8xWkX816k131cz+uqOvpHXnh+Mb1cT7gVrwijrJC2UWC8dxR"
    "L97JS+WFSKw/2/twSgoLN6MrUXgiYSf//cy0nD9Uj7I88mNud6mdZAxsFsLsrPAwlfGBItAr5TWL7fZW3OO62vzER+6jyEtJMz+K"
    "sulhLqIytwJsmT25m4OaxtFR7CUJ8Q7K04kQHIycxHdzjd2SK6rI0B+DHdcpAl7xEVRSdpF6b0mVjPK2XxpcWa8k7B5FraLlCAhI"
    "YAIjlr7IFwMvssAZQ04SyqDWmUxJxfSynQbtXqZdIuqk0RS1BpWSFzpKIlG8XDb4uCbZVp7GH8nKYJxbRvtlpQCYcInh8lkyVwNc"
    "yT7ZuAc2xbjmljc2r7Gl58MHntBXoUah814ol612pyz3SJq7V7rl0e6KvNHql0JhyiMVkmPvfXaeUFAMAyDnf0U5n+sJCSh/lLcl"
    "gpPzeHYyCh0/ALKyMq9pqkoqKicbe6omWDcZWzUAbmYePluuIzfcR3lrWunxK7fSNQ9i3dKFa55hOUdcxQr02bJiLsqttFdwAfUl"
    "qVD6yJg8MlG1BP/ZSqsTqM7qBGpzsdNko+w2wuQGUeKZW6mYVn10OtpdSEa/oLWhobSQIha98RQRtmUu0q/6YlOwX6/vQ06+1FwN"
    "8gV+XUvnflW4V3JFR+8t6VjYGy93BBOOPzoL/Teww4vYR2sVftf6cF52bsXjD/Ii4BftrhMneZdZIJhULCuhHDXXUjYrMAj705vA"
    "kJ1ZGtlWrJ9nhEFx2WMDpVJwFQtm0PYW8b9LPNeXvmaoMq1aueBFkMN2Q3P10bfrRY5B8VQo3JslcF2NPOsnB06LKZP/cog3rGtY"
    "k8JfAV9aXcQuDZ0Ni6F7ydy2F56GZrkimUdep20lYQghd/XddGPzUDKyD5oKR5IHJfIupCWVMjK36n3AfIymu1delbHAk02xi9Zs"
    "EKsiT85AJGhPmZ6cu3nP+FTQVJmgJDNmOazISgf+t4WqsvC/BV0W+p8uCTJV7gt9FdDLY0FdHXgVdbEQ+nzQp3wjF+deEESnK4HO"
    "i5qw88SrAy87LoHei+Osg90y79+rAF8c9ufqYIt4jMXrZUm8u6vHHb06gHr8hkIglwWMXhrvufAUvA6I291iEJWf5StQjRUiapTW"
    "7uVqbxru42UXfytxueYIVdCcRUPUIrh+ahq0gBasOERef9kYtW7+Rlp1zTGKaDCLBpiPEv/RSdrWlYM4tz85SSuHcEE43JulaPj8"
    "8Kk4ty/Jz2XJdXbsJ1PSm7nSa//yV310EzT+jP3pf3WJ/ze4xP/q0f5z8mgP1PzYn67gYrr4pskq51XQFrPZpvfQZW0sVlx3gcDA"
    "5OdEsmUUZtXNu0Qse4VVllPSPfHD14YlIkYaupYccmQ+erWu7LxUKFE/X3xGlsz+qEAWbmjc3HCI1b/F/PIKLwXdBRYam8aa/wDM"
    "XSva3+eOufYCzLXko8lMbpJsNCZ6CLi6eS/Ox/hrwJ+v3M3XgD9f2aP/6YA/c2tyDQ7ks1WAgP01y2oV5sxFyMC6TBcsa39LLzIL"
    "oxFOP8VJMvq4ET1uiG4uJGKrE6Br3miuGrQpb/NFmSzZsJ76Gsnp84/kJGbpe+7dogxr5P1iObJYMYUy9SRbUIyI8ynll46JldTs"
    "uSh6ywm7Ci+YLaYNt586MTqDVZ4IWPoejk8mzi3vZJqeP/GShKKjLMFu8e1OLPalzsjEpWaVCsod2Mn48zKzMtRMxb34WexDGUZ6"
    "Ptw3vrJ+Lm53kaHS1SS6IyfxHl3Lkrjcmf1X3/7/K779pR2t4Uvus9ilK4W9MPeNjFTwwfuXt/QYlSFLmhMRBZjCpGrXODhKy5vn"
    "x6hkt5h1lu0Xs7Tys/U/GKGBh+eUKrx5tbWMR+UP9kl9pQe1z1Yh8Xj8NfbNR459c4MH3T/m7Jr/wyjulePJHH3OLHIp1/qVT/3K"
    "p37iGFQfSLk/MW+70vFVEFbLUP/+0pi1r9zap+LW3o5L4oav7lTlKiS83LVaob+Vsig1m62iODUivaJHUVfWEftG6N6M7wTz6UaP"
    "C3Nkeu1qtooiNCuvGyoKcjMXAlkLG6Sbscrosr1seNmPGKtl0aoRAOZDHusxnrcKgjxr6IlmKYZrGffLvC3gLvdPpizQaqGDmX+M"
    "uYo533nKQXWZlos2sQsACqPQM5FcULhgpEyxRMN7Lu/LtqxZhmhWuRTTRTCVo1ovXTTeEmTrmV+2JdAybPPapeguBKsc30bxwlGX"
    "YNzI/RLNl5YhGquWYjkPTTmKVdn8GEuQq7K+CCOrZag0wSlAZzFk5Sg19f2Kx94tRq2Z/QWYh62K3K1lyO1eDbdsdAtGXo5blv0/"
    "Yde2ZHaKXZ800BVPGVPSvQpT0i1jSroLmJLudZmSL88i70anpwjCZZxMt5ST6S7iZLpX4GS+dHvCG52jQhiXsj/dcvanu5D96V6H"
    "/fmSLCJvdHLy0C3mmrolXFO3nGvqrsg1fQZ2nKse7L1lB3v7ilxTZ8HYO4u5ps5qXNPfboG6Km6by3C7fUWuqXzkC/HKdbLm1vur"
    "yg51j7QnXurFyUoKtTJYs5A3sQc+U3GDEp8AD4fKmUUVClwRUjpzhid0uIzowkoF63sF+dw6/2oF8tUK5KsVyFcrkP9tK5DyWJlL"
    "4zb+g2JvfLUg+N+2IMjoj35x5gSr2vMHnhOvGJX1auYEc2tkWuqqR0TGukdBkgsUcKaqSL+/19AoCqOxd+OBTZIrhAb9IAXIZGm4"
    "z6sFhtWDbLMAIsjaPC8qUOFv2YUhucuDOiG+X1LLhZ5xPxz3V8LnlaJJJV+oh1DcQyEsExT5uDeikSTDxnbYI/6+3Iv8qqn4AVQP"
    "yXWqzRfeInfzvpe4TkhTVwhpXSWUqnX9iPU3ELZhiW+GGyIdH6zAlKwcLbhu6qW0vsBNMItxOp7DifTCm0bxYvNc64/ZyfRlhKUf"
    "/X/23m05juRIFHyfr0i2Wpyqo0QRF5JNFgRBuJBNqnmBCLJbEofLyqqMArJZlVmdF4BosI7NR6zZ2p6no12zlUlmepKNrdk8Lv5k"
    "vmT9EtfMyCqAze5m63TPiMiK8Lh5RLh7eHi4s7eIafS24YXl9OMydP++YhotphbtQY7mFg95UBd5tS2XxeytEInLAyIuCHzkDYq6"
    "CH4ePvf6CrkSLZhFKSqlPqhxqG1ltzzgmw7sfjVSOU7ywhsMp8xmu5dceZOoaImng57Gdy8bTO/jeBLhN1y/vM10G6J/iLcPeIFt"
    "GQHXXm59f2a+0IN7sIdIqXs5ne4VhY2eMja8XByEJRqGWTZbJjs2QC+lY6hBtyoZFFzzPFqHMMusoYlQIEYVoSllPcBc046yKIEn"
    "HMFOPT8V0ZuGNRFfZ00F9H/qZEbTITQpb8bgcJYeeQzsbjn+q5Y0dXNxUzcXN3VTvxHfv/ox8mm8MLjwd18my+b9isto6RLQYXDW"
    "yOd/lOfZ6VMpN2nzYw9DbV92gKU3SwSd77SxTa8u5YZF3v2MGqER+Y7PUZYsiAlym2Pg7cDIfJvDCqDyNBXOlqDE56eZa9XCqcew"
    "ImvWFJRxP6s89/C8ObxN3fQ2dbOtqZttTZnN8bWeQ21tvl63Nl9vRk5qvdQiPxS1g0o9PpaEad5IKUBXE/FD3ZP9aLdVddogUbgw"
    "1qeDQy+ki0QJf7/ZkZaa9xXWv19fQQvvqH5KXpEvdf3THlfO8Su41qtvQd/bEk3A5IztLaN99ppZCnwlT03T5tX6kXunDn1/XD9M"
    "XTnm9McbRq/xIOayWpj67lscnH4ePlnImTyh++j/MBJSjbMsD/tD/OHg/VzKRtrY4m4zzJPnIuEj1pJ6PNZG+SI7duOftRXujua/"
    "93+2GfnZZuRnm5GfbUZ+thn52WbkZ5uRn71O/rTMRK5g/fEReKichw/bTJPb+ZBfBuRK3k88qEni71sJVPPoipbWi8ayIIZylMIx"
    "BHG5JAbozcudMtx3FhTqe2EDLvxNeTJ59l4nE0gevfmgCksZMhZtHrzOoBuqShWVVTE60sjqO/TV5nmJbtAv0+N2m4KGfCoVvZ6G"
    "FlRiExylqrht955/2W8gVnu35AsI/F89nPzqnW5IGWvyfz6gNZzxn9QBUc2wQXPLAxPzvvRyRdSjVCj27Xe+mp6Hu1enhiF1SakF"
    "VQEKjQGrPylEfKhmP9iQk7qy7pnVdZz5AHPwf6u+WUcALH/LD7BO1ObLH8ra4ipURt62XM4rvBulmaynwlZTjZ90PDmYrgfvRbVt"
    "r0+XIG8e/2t1PRv8OEow0nyA/7emPAdJar5O1Lwoxaxhfea+VkKQphHLTz3sX831LYzxOdvgLNBqLlRchs0o1Fjrkwpvci+zcz0z"
    "+v473BeA6OomoYsHLNeRvmDUbqJubvgdTfk8k12ej96+DB9d70q8k01S4SztO8qFlmsM5SyCS5syLbdJQk2VbY8yD1/8AISBLYke"
    "JembSz9N/EnsUBqVewH+AXYo1vrzDv3Bd+g8/Or9TjbRkLVHrgGmlKE+mO91ZY13ecNmJ7e5TDzijafvl1kKniuBK6yvxj34+7wG"
    "WLzkjEmtY2jasEBxpJMViQJHzP9oL0Jhbbj6oA+HvrlePECQ9InTmJP2BytrddnZc4P6+ce9u6ChnzfXP//m4qW6ZDfBWviAMpeS"
    "8RaYvP/4dCVJ4XfQgo+WdzWLEXKlJVa7fPpoVsIHoHxeTZWFUUeWQSEF/7mlxZSGIva2pey9VDU+Fyiemav5VVz9pdT3fvG+dJsd"
    "eXxY+vzx0kHq4cF3pBo/wFb7ya/Hb/R69PiHdrjOZ8h1PO9xbr3/O0avFrZmV/V2Mh/4LQb9uJcLqeX6wnV6pFI/k66WLuXf0+sp"
    "s8WFn+OR1/UrJ9tsemQ8L97U+4kpEr7phu48o/uaWhGZKEvF+KN+ADZuVW23XbLEMmect1oD0cvF650H32JVk9Dmja0+WRuXm6w7"
    "7a7DPpi/RXdGN9pm1Os1683yESPMRtu0+yqVk76sXgm20b42ruoxz15AG5daQK2+x4gq/e5q9oTDK0Zh9xi0aXnkTu1hnNcALGiz"
    "HLvCffwsz6azuhkx4m06jdL4mShmGUiR+DiXBX26YML99cefjS1/Nrb82djyZ2PL/9XDtP/h51h833csvp9jgP0UY4B5Amb9rxnl"
    "dB7+CWiEOCFbpGmSPlA3YYwS4wG1z0B7jafDpIYlsUv5UG0FXQ3ULTABuN5a6+5HXKs4W6W93tCBfReC1m4hpw7TyjR1kdotJIXm"
    "4fdyT6iweUk3TpZpyzz8ff3d7xX9KH2naF/eCFlXe35eD2tO0bzqIZunfI5u3OTWon7BSU6UUTJZCGnFtfqJBulaaPw7wefha7g0"
    "L30Q/0CxtBj3fv/lH3ucrR8lKNaHQtiPFDDrxwht9aFQ9uOFvfpBo1N9KHT94JGrvr9IUx8KJT9qFKrvK1KUHzk/pRhS9WcrzA5X"
    "r84Nf6DQTx8G4x9BUKiPOYLTh0HyRxHb6WOOwvRh0PyRxGf6GMMofRgE/+gBlr6/gEgfln/9KKGSvqdwRn7M/MRCHRF7/9TnTvpq"
    "So+akWBNVfB+t4XxMjdbi4td5mLrPa/V/umcb13lase+V77qFY1VVqm6rjBdXrfG2mTosystWOnwy9Y+rqkHlz7d47qle2wFutll"
    "dLb2jjHWnn3lR+iSQHk8C7oQy+jGVcjfLVNjCydxna65JyivCz/XSZSZ5kUDW503XNt+kB4ueKZfP/At6B1DtKN9afjd0B/Wzzuo"
    "jUWDWop0Ge33Uki/s7oA7d+hh8SHxLiuePc7+6vt8Q3yC+DaCv4UfSf6fIFb8+V57NCa7ZtvH8CDxdW8J3t8Tz4ENQlTAKaysF6A"
    "t941Ldff+9axFG7fSy5p39Q3W6nxd/PzaqGhTX699FDaHWL4CMaS/AeLK3kfC+5Wj53LHXW6OLsEGf+sfRW4ysJ2ZN3+cab85vKe"
    "313S842looPDsNun+q7/kNTODO74mMF3mGh8DjT+wFY7lxUjW4x7/AERLDkv1R02cVLWFL8zAbrq7KzViXk9EFCbPLzEXfqVCalf"
    "d7B6lf3XEiw3zK8wp0ufeFmBkcgWwnlj/x4B0FrfLFzWl/sPEuNoWXSjy8c1+kiee4U1w2acjPd4VPtesZ28sdhaxRJt9PA+E/3g"
    "co6mPtiYHyzyu/yxPqieZBFuQduYY10GM0om5GPI8WQj6SI9GRz/bOz+s7H7z8buPxu7/+xZ+GfPwrBKhGj3LHxVT6rfS4BgwPj4"
    "fd54++IbXuZUhChBvx7iaq8Zmg40/LFyVcf2xGTyEQUTvvKoLxEseLlovfCsKCO6fjTeFqBQNU2ft8WdzKHojzmf3+tEfTSTMMzi"
    "M7l1Lrd+W1aVaxTOIUAvuyW/485powu8vu7LaKTNBabilH50BI07/kwgm871AtHIzSnjYRonI35qcuoJVNrwV1Fkefmhjrd1U/32"
    "41PzmPvRHGKvdHCtncR/QrGXZxGcW3GdPM9ml3Sp0rJerbp22SHOd6xugX7wUk5iDO3SdN3rBmbNdxfrvb+Ud5KXrfiuDjBUgEiF"
    "u4BVBcWb7+bPxX27s65Ce43GW0+HX6PAGYtxkooDkLlFXp6FE39GIoqw0llHonx6mqoy+6IY5ckM5rII4xaYw7PpMJsU4Vjnz/Ks"
    "zMqzmegdR4UFGc48IDOZ+bC4l1ZTkSPJDKfjrY4IyzDtbv2mDJI0ENujMaWcCw3Vv7aKd8jj5KjSv0/zpFTfHKsynXf74mX5aisN"
    "j8dbk3Gng/VAvSj6dk6iPEixgfLdu63zeXc87o2iyaSDTV+/PsU207B8mb7qbibjTjzumkLZOIjHnbLbnbWXyUVZ5dD7ebdzPg93"
    "qi5gugPzPJ1lKcx00T+PRiNYNChS36vCqCozzJyIUvT34fdJVEZ5/2kVDqMYjgJv4GOSjd5USf9r+MxBpB3l1XTYfwy/mHI+qcJR"
    "lMf9A/qbVbA0+/fxuxjBuuOF2n9Y8W3HMHvbf1Tx+eFZxUttlozwwd+3FeM2n8ZJNMmO+rs6YZbNqln/y4ov8N+W9FrzQQUbp4wY"
    "+S/4x0kiTvtf0beQ1X4Ov7i+L/DrJMG98A18wqj6v4O/eXQKKX+sQhEnyLb+UIV0OkHK9if8nohqhnuo/3v4BR8lRxv9tALhYjIR"
    "eRL1RUw7g8r1S/gxLiOGSuHHFA9VufxAbEe56CfwO53AppjKU1eECaQ66Wf0WZWIpqJfyF8Uf6M/kr9S9s06kT+zctav5Dc9h4vj"
    "8E2aDfvjmJ5DI+JncTgVRxFhb4rf8PeY/2KwsiP85L68xk8QQrjJE/hVTcpEzuVZHBLVoVfWQ/xxFKXJt3QgGx1j5I63sTo98yo6"
    "jA2J7u/FMir6qfygfjzHH0VxCjX378E3TB7Vvw/ffI/Tfxqj748jEDMK7O4b87OYJWkKEDtxiKfPTK7Mr/FniazvMXwlM1jl/Sdx"
    "CAQmm0y4Dwex5LP9++pLFn4Iv99AAn4/ivnqPu8/g6+ZEDEuqf63+GOSqBK78icKb1/G7DMZPh/wZ9F/EaNzLhrtV/RZ9D+nv7Rq"
    "v8DPo/438EfkU8DVpP+7mF42wmqJ+n+E70TkIqbyf8BfU4HLp/8n+M7Q8vP3+IEijezPp+p3cZrAUuqLMfzOJoi7kj9L2IXpmJUD"
    "Of+V2Ij4F2+ubByeJHlZRRNGHQyqGM/n3W54hOxFhcUzfOUX41vj2+M7IAMw/8IU+m/ATzUHv1hfXf9sY20QEnuB37fWb699tqZ4"
    "MiSMRvFGPBqoIM27Kv2z6M7duxHIqNJN0uAXq6u3P7s11CkkLlHyzfHN2yCjADNQoKoT0nXP4BfDm+sba3dUgip6Z7w2XNvAovsK"
    "0C25e8RJq0IMyLSepOVf3Fm9tYG2oDJFQd2O7w70Owfo2PD2cCPSKQQl7o5vQ10mdKCFy7U7a6P1dRuX6+vrdxB5EpciHq+Nbxlc"
    "Dm+PVkexhctbt28Dtpu4BEzeie7YuPzsbnxn9FkDl9G6+CweurhcW1u/u75h4XI8jqLoZh2X4/Ho1mjNweXGrbVba+sOLm+urt/B"
    "ygwuxxuj0Wc1XG7cWRdrsY3Lz8bxMBq6uFyLAW4EgsnmuEpHSJSC18Ahu+fMGo2DLZZzUB6gBG1CvSfT9WhtIV2D0wCd5/hulnqV"
    "rFrBX25FlEKTplLoBwM9bqRb5mvW+hA9uS4aCgfbtYRzUlTnw3Bx1/Agmk/vE0vzt+i5NHIabVwPeXIfLOq1/8LHdMAdlbO8m/c4"
    "ZqIb9zUmy3MvI3q8UF10udctauoaFysqo+3+RFeO4oNbxDVjN+poSaH9U7J0nueanb53BdMsjibvXRz+0/vyhCXsdEuE+ZbZoXbN"
    "bo2yqrKx2NPmfKf2ki6bHllSj4vO1NnQZfOtQd54XaAHc2YTGfnWQJIaHKdeYjZhcUlG13riQkWsrSCXncG0LtpVJJiKyOWEjeyr"
    "T4sidzXxJGhNN0P9HXpTu/yCjAppkhzq79Cb2uXHk61DcdLUaGClVyUKNnG/nVQPvZt3IQVszL/jekd78xu523LoIwTNdhQr87Wi"
    "8pwHTA4tWU7G3mtMigO1YvG74KttLN/DHLwnuu29OaS9CcJ8UG7Jw3hHNWM7cKnNRW2zq9P1OT/yK+3tppqVG6XsePeG2X5lx7vj"
    "5JbB3MYmsckDAjCbcCDmc9QUvB1vPa86x+MQeMU0Sstk5L9RW+2t3Sp8GkIyH5MqwSIDvtWqv9UqwA1bpy9ZliU/mCvdNarc3N7e"
    "aUa84zByzg21U+oP8nG2Vctteqv9QUay3hzJvM0h0BqHivIoDEHkPBr36LvLUj2n4GeXKjQaGXle8wZjI1ywKqF5VeBt+azR8pnT"
    "sjrjO801TfLtDnjbGTbaGTrtSK2Ld1QSb434teursrWmjyjMCmS+uiHxZ8N/XSP7HzpsmZUA19bCkocyywVO+tuxjL0Ks4H9f5zF"
    "4pDkLFwqvSwfRSuYDqunKB5FZ9D4tTUYY6/XE1tbW4NZubL7bLB9PslGEd4aRrCdZzBLe6y/ivJBmAtUQ/YHX8KxG3+PjrOsgFVJ"
    "zUDLmCb1TIN76UlCMFE6gokf7NFfTHHu6QdPRHpcTQN0bRaIlM8vcSah7pOFWB0WxltBB+IsQI9ggShKUQRoTJZnhSx4KKJ8dNxe"
    "0G6pcGHPV+cGsLAgC3WfASN1oKHvaREUCgmx1Ys6uD1aqwDZhQkkE8/PZqLovxzsDsLBF/jPY/znc/znOf5zgP/cw3/+hP/8cXfw"
    "Chbu2ZNoSsXibAqLCeobFOIIqGm0MhZJDif1AeDx4i/m5zdVlJf2zyS1fhaosjG/Lv48xE6alg6Ps7zk5rgpboDr5eq4FlnaKvo4"
    "SaHgPmQc4pjgf7+X/zuk/70C2Twtj9WAvo5S6AUOaCyAhcpvWI0Xf8GPaJgnE0pI8OfXVXrMfyf0NzrKipKxARgfUlkQzSr+SoEp"
    "y8RYfMufdvNqlNAHbp9b5ma5UW6TW+T2uDFuh9vg6gkFpbgP/CSCLRTHN6bTG2dnOPN5Ue5HZ0/HXwnxpr8aRqiNPaf3xP3BfYHq"
    "SNRmiJMkQ7qzA3QlTzJIS0l3cpBf/ONtMs1kTQewzjiS1gAldJzCYHbxZ9RcIhF2AC7+x6QEBmLysUanAqraAsBu2ACcHkS6T7xD"
    "niHfMVQhAFn4GEpXqZW9LwpA5kjnAsnrn9sCzx6drLrnolcVonNahYd0cWAATglgKwaOOcUbIPVxbyLwT/e87I1gxAWGT+ixGrEz"
    "sOggkT367IZQOiojmDkilC+S50hb4UxX8h1iz2IeW2IT7zNAEnuZhvmrbBzI6xloM09EAQzkpXjV7aqiUKm6y+kMVlayKln59Dzt"
    "5YJO2p0bL3dW/vTqBshYW78ZrAx+BVJT9ig7BQEOutOB8QLd7ZJM9Hy8dU7a7NcFLE+8rEnS14AburYRaQx0Hr5geaE+f8IXPZOs"
    "yl+P0BYeGAawM1KJ43c+TmIEQVUq/EGqTxIVfBezLJu8xuw1ckmNbIxAytcplYVVkkev+YaBf4MQ+5pDbyMk0lOQaamCGFBCDUFH"
    "X9MK5bpOX6cZSHXUeeShr80I6Kc9DEpwxiLTTJP0U46FvmkQ+pfkkeqnHLylXrs37rBwLcx6OhJqKe2ePYw7A6pS5CtDYN2D7jZJ"
    "t9IVJPyAzdbpbm8PBnjndU28ewczjzHAi6+S8rgzeP160O1KFj7fLPMzyc+D3x0+fdIDRgaTLbpzmIXRsWL1c5aF98db2L3wKcz/"
    "FIc/KFFhSCp3JEJAf4A0FiQPx0ilJiDI99NqMiE8AwUcvXkdi3EEPK2/troKfHwM+Dh+PS36t8VN1APBUjxTIEX/OYgSp6ma4JfQ"
    "HBJ43BivAYt4G1EgUcOZBbIGAsT+OFQZ/fMqB8pAXUqghvi1/C1r55/HZTnr37hBssYx0Oj+Z3dRnVrADKN6mDA9RbKrB0Adh26W"
    "4jXdwuFc8k9pPr62GvJyeC3H0x8Ms/IY5WCoY4R3OrAceW2zFUjRX9PXL/1zXvvjJE2KY9oFsN5pj+HzrgGe5imIZFRq2BG6WNJd"
    "nSs89s8BI8/HaLd5RnL8HCF54Q7uvXiGMXq+xdtG6A5Il69nEYqtA8ZjT+FxexunP3wDc/4JbkK0MiQR6hMlSw1CnYG8AtPxr0mG"
    "/kyTooCMff4yWUcZHjgh5/MswLOXyZH2JpD1iL/+69//H5ObYZmnX5gEWKn5GaQ9z8+C6IjWosoqohPs1CH8MYlV+iaFtXUPT5+Q"
    "+YJ/BnQaBShgLT0+IWK3z9N5UATEVCkHZBs4L6oc+GXlRSUkR2VwjpdKQDM/OT0WKZBSkDuwe/i3lneGgmPO+X9U3wYmjU56dGjB"
    "MfDOB5GNqEUhs2nuC5WvUuFQhuzwE2LAKYlFDI1rB4Hxr0qTs43JemdRTlQiXYHGPkGpUcSAB5UiIYClpIem/FP4GViVYHNosyKO"
    "uBIpg1pZhPQDIAbJW8inKembXDlTOv8ZycSBTLYA02wnLU5pwOcR4WcePMlAJsDEYJxn00DhLxoDOoKN1aDYDGgXcw5sn2AogKmK"
    "oKQ9w0upZ9o4jRIcF3JyaAYOPgHhPsD71eA4KtL/+vf/swyiPEe2E5yhAPYJ9wVQnMoFfchfQZnpZnlxzwS+0VOT+WIt2GP9VZAU"
    "QV6lqPcga4dj+P0UqODhBBhX3g+wH4dpNJtGb2BYL9ZCEOyLAG8lkcvAjKUxCjdvsDxXj23jsQ26KrhKEVjtAV0Pg9PjZHQcRJMi"
    "C5B0FdwuEcGe6qxZY97e9oORqrHWRd2nWle9fekFz7Fp+JI9OT2GHaYmEw0pCt2j0+MzMjeFLn11fBaUpxmWK7at/N0sxr1mMBiM"
    "oA48vGWpoFZASApmkwrIORztjgR19gimtJCpRZBmwSnsUkDjcRIDAKOsyMwSgyLWKGD9AGEqdH8QuxMRIGegOYAFEjyvSLXFuJLV"
    "UPPZeIyIMR2GVVYEB7IrrBwANEwz7GEpURVSF06B6QOKVX1UUG3OUC5eXqDwMxesKA1iufqhAlz4sLiTEeRXsO0nwVlWBSQxQLVI"
    "s7HvgF0yb3cIFe0KlTPKoPRrQDBuT5xF2J0gsq5xH2pQgIHchSMSrKgbW9yTKFXIKtcs7OAZHC0zyoBhGiVU9VBne6l6Q/cjmLDY"
    "XTcyC1YDEKQZnqvifsAqzbkqLoUcolz0VctgmvBMRLGae0NSmCzY0NQDg13VqoGKYu7oDhKovayaxEyTMKdWe6OrxVk6wurhT3Dg"
    "IgGzHojJTHbV0EsgwrROcjGskkkc4On4TC/fGk7dVWzXLSkjf2m80up1aSSXAAoqCansaHAvZkKiwW1Y2XOCt0D6AcoGBaEFzoQR"
    "0mxB9cCKc3Yht4GczrMR9SAVFwUYaAXr0WhSMD27Wy47kI2I+kCsccud+nQ8VtOEqKdhEREZj/voXi4qgPeZPVmXpNoXWZq9yCe9"
    "UtJP3flE8jXsXjWTbM0qMGSCeg9ZAZKH3Iw7imMUaxFriuxQn2eU+hzEnZ7GMnQrpR4VXIlkVbBZRc9tsECNyCeoUm62ZG14sxv0"
    "mOo7wmrIU0q1YxDGJwNga7qaoaCaVGlSuOnmQP6Qo7CQxiASabr/ID0gV2HwXrATx8yhEXMSJmQUMe4kNenVao2mwwqq3cW/AQji"
    "FW7NGQwD1rZV/R5JPTgutGEEomvP0MJ20uwxng09Q5xiOhYtRMBvaot6ITnovWO84uF1SFrPIAMmjO+bKE0Wxk1QCCFJCjVitk8Z"
    "eeezJpJ1JIXrwioDXqIWP+URvJbUN5GdTYFJw3xmVUkGokBZsUHZHam6gUbv68G5WU9MHrSczrsWBI8T8QV0IAyUngO/yjCQ6g1E"
    "wy/YGpF3pVv6keSu3IZZtgqKVRMGYHgWcJIFE03ICWGVo4i5M5lICLsapfJAYV1+uhWoVFWFKmBXwmoUqiKtxkC4qlzU+vElgZhK"
    "DJxdEWma1Mg/xx/NgePDBwVyCN9NiKhAzrZTjJjYWjmxoCw0lm7mJblkHfzAASQ4CXQj9sErhRN24xgZo/xtzxGejen0sMdfzSmS"
    "IIppSdlbWDJQIEFYjAd5j+voOZXAktlTC2KP9panJUjW2ePGsibc91IWsQj3/YCu8eogajkbMJXSALVWlwSdNhcZg+o1pAG9Swln"
    "v5fCtpKzD32EH3UAq10G8jRLgLpVBdbeKMjccD6UbJygdUrASqB6iarg1UHA+KMFjjSUrx1oSqIydWBUp7uwmOIFJVWVBsvkYZJS"
    "STlCy2g4YaXM7kSpZCj5KCcdxefwxyTCOabkw1ZiV5FTZ55RB2QSh3wkARo/TAZ7ASbtB37YDQrBSwr+2t2rBPWusiqZVfmMiPMB"
    "fVgZcMjEZPhjVZHDwQLrwL8mmUyzkWbhX71beDHaBxhzanHyrHOFJkBqCz0yOwQ4prU7GECqMx6bRapUUtYydUC/VMvUADoLFTgk"
    "HNST9EUhdK+Bx1ekmXMyrW5rAF6VvQwFTTx+lRkw3LnJmIgx0rDz03mAn1gl8WdmXtYp5RfnCT6EkdnA7EgOBa4LnyYdFeG4Xu4/"
    "3AcJtoyOCpMHvFXILl78H9jJ/+//DbBdlW5VjosI/mUlhU4Hdo46uck0g01BYpJpl0+81CdZrK9FEnpSEIyBJ59/Y7ojZfD7hPsd"
    "/sFASHUMnJymR4yoZ5ouyHQNNxuVEuYcPue/NCTEDCA9kNv2qb1hCRGoHi5sBEexiB+mUtoH+gJTen6KMrQBonkHiIc024xPFwKS"
    "7yO5weVF0lxelI1MyaBQ4Qft8J1KwIpr7iWqU5Q+DfgXLTTFweiElZjDk66d1PnPpb50H38EpD11AXaOMp2NayKWKlgL5Okk1iCT"
    "DE2KEAZajVjHdA6VFlASZD5AOXp4yt0K5PgeIS2dYiStOOC7Br0UDLvfMZyeQoe5ihDaBErPokBoJ7HCVTIBVlIWaPeggCqaKJ4D"
    "jSjKQW0PkqrsRAOzj2lStPOXypAdNf3U1acm64X61qViGhkcRCIpU3smjRtGtJCsl79hHOk5o3ySM/YlEAsbDBUz3yEgPF0r/bF1"
    "6NEYNQT0kaGelEUY08jOeHopMcSajixkxszApoXijpRxhClyuik3DFZRFp/C0u0F1jlY6VsC1NyTJgy1Bj2nnodsn6wPxFHARBGx"
    "d1SvXHdtbRetzpAKqIHOST+q1K40NBD3ItQqKn3pJlRyQlphVIgr8KjUAD3ibWQ401wEkmIFHVqeXRvp28HDEgi71o6wrkmr/wpb"
    "uFVnSrspa+Wk4tSsHtmi3ZJVjIdwRRz0gsdLcEBK2CStRLOtP9ItDu4h0kpwIkDxTlKSLzBsUnQXwTDL3tDitnsER/ueKcOQmuXS"
    "z2auxXM5yW70GRN7aBbJs1SJk0h3EyiFeGMB5wx6fjQPjgAvmBugjeeCIhM41aOJB/JKPOATQZRFJS+XkFQQmZMcTTTEk/HaElA5"
    "NAbGAVJeDR75F7EX51hOicH6qtT4klIfE7Wy4bktrXKWvo7SKE8b11QNSAv9CO0BphvG31do8lmeBXTVyBm5oBsj0mKgDkXdNjq5"
    "kpZYEPwvjM5onKQySZf13ZM6ObLWB3jjwJsRsYbGMkGB6kgNX1RDRC2mxVK/gVy+KPNkBilbNGgR44UFUCr4jZODEESoC0VC3Zr5"
    "qqcHBAz39uNDK+245KTgwXMrFUqLPCVh9p781HJzHeZQatoUoAWiL4foGC6/rXyUgJ6inHpepUkJovcko3VXA0HljCcLxnnP9BNH"
    "Ldr6Ki0HnvBJ01yqevKfGIBae0gAlapCQcjjqgLJhTzMPqMPI1jqKSiK5CglXnaObIxvSFhEp+HD6pcgdqk4fgEIUoQ5DXDCgA+5"
    "4yWlG9qLuCV3aNZ/FbjzDhkPSpXuTj5kAV4pr3Xy+cqKpWMkwbMGShlCdltC8TRbQLRoD/loIWGMGpBFqua8p1l5X3JcFhvwDmeM"
    "KR4gufEesobwGNgiyLUgAMT4qBU2FGDRUvW408Tooc8GAhhCLQcJFJmJIOmeZ1cWcZZBVWZPMqL/1EvkFERdnBsqXmLyRqUX3ItG"
    "x81rCRRtkMcL5IEx3tAW1vWW5EAF0J1hVLvzUE7BwiCaoEb1DKHxBsOopFR/8YAaTWSPd1AtjfWneMEICEUzIjxznfUDvEmSwrCe"
    "SLoTgKaRU8u13cNeBo+w8CO8SQaEaR2wGjf0REzGPWdOHZ6Oulpk4KRwJ+zJZKkEZ9tia0GhPwPEIU5Nz13wPNVx7FnI0nDggaRj"
    "X/FPOjfa3aUhoLbevRaX5gFuXbjiL18XkQVlQ8MiUPvmImFIlZL4xtkueFL0Ytxu1HagDQJUhQp2SZ3yEmibFPzpmx4b8qOwr+ZX"
    "5UxYiH3EJxVKUrcBT8w9LKFjA41zFBBsFzxufZVneLVNj0QCNIbSlSjNy3MLiSxLULcpW8ryfbxuYokTd0ujj1Wa4yLBZ41sJ6Vu"
    "KGDhnCezeR83nD1ZwHEj3sGPdp4EaF2nMSGnmy47KEIxMu7TZZOuSo+4jFOBND7BjqjLP4BMiMQdqIs0Fy1au25jwQU5OKbTG0pR"
    "0aTPtDRAGjWNKGj15Mz0KSYS0JwD/EZDrVgabMV9PoUEw0nEO/yNEDMbmlpFITJVUovZfARUZzITa5qOpXIfSpmB00RY68O2kZF1"
    "EwlMRXmawXm30LdmdF2t5o9MOtTVJva6UNdtumKlfsUHLFUpjUaQBLJNi6GAaufLfpMXmYY2MuAsLmXd/zUKNdSUy0umGY3Euu6T"
    "ZWyQJXQ9tOm61UoPz5ojYEZxMh4rSy2y8EFZ//is4MUTsGoLcVDm0Rnfd6LEKBV6lAidkAYVT/hLllL5lp5RM2PKYFbns+7oAwmb"
    "KzAe64u1T8gSE3E2PLPMfOpgz2lPHdqzU4efZjrGvNQnngjdNcocHUu9ubw1dTPtGxwnUVlB7elr1ciqfNuFFSSqPYaEnAy0YGUa"
    "wl2U2YyPvkRxFOfHsykdxnk9GO2AZJmo/dP2c9SWYb2RZ5yYKwUt05GEjWtU4xWaDlqtOqOQNE5+NobMpI7A5ZY11o5yDKQIkcyW"
    "XN6Ya1t+yWP0+jLfDEltJTxJYQeJwfVsSLoC996YoyqB6rfgSxh/+gCmQNt12hJWJNkokCbED8tuLI6wIbE+MhNHDlSyDYEWxUjy"
    "44mwk9OMilgykjLncwqjDlkK3QREawO3LmqSbcjjKRKb43kArG86lxxZ51JmM3mCD8NI+XrGR6jAuYVw4Yy2hX768i2ax0k2EKkq"
    "cPexyiJ2W5DK+VjfdOismJvdp5VOr0aN2a6Zh4xUCXByfVOvmnXl0lbrvvwR2MbDGhT34ExCHvI3Ak4UemzYYcRGv/zTqN3c+lBP"
    "8OzFkycPn3yuVkltihnm4Nm9g51n9whGzGhrNYEOHz3cUxW1Ah3svDikeiKpe63l33/45OHhAwsVHpCdh4/u7SMIGegAAFEEvdjv"
    "G+IU0RUjZ6O2dp8n6ysU6iO5ruUEFBoQGTecyt7QaexNMNX3F5IA1QBBuMFLRJzauqBjgWVkrgXtkxAIDILuphggFyORsvyNH6od"
    "0yPU4T2R65tuIpRC0cmWy5sAHJ2iRE+GfdS7BMgTttPItjZJHUQtVXd21BjQIlteQzYstDVYyxLmWy8NxRpWiVXUXh3NdR5sMB7C"
    "C/rQ6a5Czro44GwgkLuq1ieSmVjdx1plnU4vZB+cNGYau/zFjEIOjinhoVE0SNywwEGkn7k/yh5WzzP5ZIJ5ZmSzKhuErxtZkkCZ"
    "v6g3BIN8iDFK6K2LHGiiEzQYXUDcl0YV6hqkoSSxYJ+QphDlLLbCQiA+FFF20NF3Gd3aXunpimBD7TJClTxs2c/J8yNzQVXUsk/T"
    "p+6aFVwRnbGUeBzN6Aayb7f3gid1QXv83lkZMX/HFk+jQi8xkGbhZ32VQVJa1mCkAWEDcCeO2dePqS3CJPVExqqxCSqfIDThleWH"
    "RMkkI9sjENNHJZ9c7HNkXEkZCmVwTCPj9pHGEU9+24SLAt9zlsI+TIN4L2eAaQlVaKpCSQbOAKokL0k8d2sO4GxYJd3iPDtLZ9sF"
    "Y8FWXjvRWgeCYs5lp8lkoo7yZMtuzXrfqekLOME5w0GLflKN1Sg3jYvEYHxNgqwB6uYrAJyB3NoWsZo51BlR8679sgZDhxcaEucF"
    "gZlI0Gue3gyfvcZar0y/apm9jVXFITZW8da7qAPc1QB3/QBnfNagS5gzPm84+cD6pDEfyi86t0jSETFnnFJ5kaYmQF6oEQjeyJds"
    "hEDl0GUVWTLQSyU8eNCujNzShaW1c+yme7qipgU0pdsIlFfDlvwgLARS3UpKsrY2Z4+yorTL4m+r7VPbukSnw04tqcmv6MOxg+BG"
    "R+UO4VOahYAYB/htwuFG+V02VPj9OhsijCia6hA5G8diMlamJEDs8KdBQwrgIxFrUQEJAwrFJDGNhAfQEhragIlfqGnR78ishS5H"
    "ol5YPMrYtJETjDBjz8aTxg1rLdd3w6pXq7z/fIEEAR/74BVlPX8nT6L6ktDaX/lAgG5Y7+gbVjncDIsXfIDSx2W50u3bXFnQLFQk"
    "ZLJrtMmcbuEPqTwnJT6I+QHdQU+QeJ0py2mrs3QNjsV6AXmsQvGCXw4q0+qkNI1PLatebeHrbgQNInGDZljRKM/glEEvIS074FoB"
    "M12WPVsTxpq0ZmVN5Y6NU2RUTIZ0AVXdU2UmxkjOWMVQ1HZ5kZG++Zl8aMeWiKrlw0yZ7smjO/Kr3IBaxMZcr/9a3pU7U6gOq//d"
    "nye7/N/1xbm7cXfPalsXZ76BUsp5IlUTfBtu7nyURhg9FyDblwPCEPPqbR/XQr6N6CUiaV34Zy1XNnJYzVDpLN92VDmqqdBGpJqR"
    "tFoj+n7tJilVFfnquYSSDlJkkI5/a3kFN251owZAHWLTUPmYDx0WoR7p1FoXBKtup+qSiO4n9bK3MR3rrtYIba3nhxld5boaDIWQ"
    "Y3yBYCqSF1j1GiT7fIqKYVlwGsVCMk16vER3HrQmSccr7DoytuOjBU8VjqtJnSQCycIcXuEE1LqpIK3M6K01a5bk7xpjeyKpA/+y"
    "2nmgizesatpaHKFBHkuT+2z5YdJnUlV14DABzPG8YnD3OwKx3R1yYWWFbeVJjBBmnBzJ8PdsPu/vyNi8xWONhTnxorkFyeBku2Oo"
    "IQjU6vkAfusM8XamTCToUg8Wy97hl5gtSvfJFuww+/01ZI+BBgxZgKTHYuo3Ht3kHWEUDKsjCc52KeZUyiYrylgFIY6qhK5woB3Y"
    "4vTLzpFit37YVeVpYV/lWlI2v5Vb8AyTX6GaZ7/EftUxhY6j6ASUmSi6TYGT2eeyd2RKyI+M6t1MNBBK9PpVF2nlmbirx3618qod"
    "YzmsBQSZJAHQ04N+BxLgr4DvNIkiSljJPVaI8hrlMpaH5ENMtaXHQHq/Czp0aOoaUKk43xVo/lyy7IArOjQqBaBb9dcJKD9Iy1Yo"
    "J4+5tqG0Gi25/RGnrN/DLzf9CfBHtWSYu+hrAYnaEjc7wcp35XIlnOLBPCjz5IjscxVeau3ek3fKyqBS9T6Vh0dTe63gnueaDK04"
    "6dZWb7wGfPOGDFdEa6kn9UuAhdCPeYf/ikUmucUhmwel3TjIQRZurr6HPaZ5Fs0pzaSZCS45ZPxF36mBtTpK/eNmAeGV2sgD/mId"
    "qgWB79VJAYYOTXjtRWesPHeefJscp8PK9js1r2v5Wb/ppZQnYEAT3JDoH0XRuFPU6Dw/zWRy4bSjTHRQuZtGeQ6tnSZwbsdVbYrA"
    "kQLOUOqoHSELNe3gwR0VBQW/1kdWTCGAZDvSrQqb5+GXm65N/ohkEqmyBhnRS2V5R4/v/5Gi1Wo+dN14BORdx22CrUesivrGGMWF"
    "lYIM3xlC+7PZ5My1Wg7V+/6zxkW07hj5ASArenIIoOzkCydfjnwf9SFq26Od1FEmHW1gi0hmUBNCdt+94ADPP3g+CZEHpfjEU1Ki"
    "kE0PySmTLI8miHRqxxaKjDuOUGzcj6EdDCXrBY/IYiDSYjGTMiK7aabH0At2DAR5uRjhGYmNPU7Q+Rk6lAwOdlT6wc7K3n2NGegK"
    "jFlpSWQKK1afyRZIh8JPQ6ZzCZVmKpcJhv3ygLgK2ig8jmyLHF0WsG0ojT4eKfNjhIBEsodQAk9IrYu3EUYlCR48PDg0gGpjauEI"
    "N0QcSwD44l6gaso+X6h+0Ooie3815VEhjfq16k4+ePDs945m/2gZ0FX9V4p8o0rBBDvzaapoydiBoQUzTthqvNCjRI9MZEoyFiWe"
    "k/B30Pll1wGQ6/erCKWUU3k/RA9sWNE95QcskTHNw7faeBlIi5dZGJupGINq2k+ywQKjlKgxss70sGTxYJc1qLQnpdWlHqu8/LVk"
    "I1qm2DieFCrGKnuhCjgwBaJaSV0aiazZVsaBszwbyXfy0myFORUdkovgN8Gh3G0HyYyiYkhHI4azNt0KcTrrac0MzZybZ7UKLOKl"
    "pFPSB9tMTZ29Yv2cSOoTUTjlm5YHKt4eFUDzU5IFzQs3FPLiib7yS9VdtuWdxgJDkw2ERTVvveMnSZEMJ3alvWOWHckSe1a/YCem"
    "lJwIfXXiXsHDnv+mSnIkypbxonUqZ988SsbtFN1eDcXQbExvZWoVw9COKQsd5jiY5sUlHWrYVo5abq57hdJpZj5pD5Mq1szdqMpz"
    "kY7OmrsyK8hytG8Ae4VRAd7XNn9IBNCBdCzm3VqliqVSVcCbRM0mlNWMznGiF7g1w2Lgk4eqM5BuSIx3DZCL0XpM7QfgTcnoDbu/"
    "4RdrZJE1koyUGqegWeQxIM5Eoe+VgE2Usk8OWuXdgWsMlguKHUWOP6xztHQMhM3gvOkpVdcKOeuu5Vmfo00FydjxypNZVw26E3rR"
    "PLen0V4zznmeVIslqty5o1KlIPB9NPn4w+XHLpJkQnB+MrfJ14uZPLQz/UFOxHoKtbxSwd66vjTlsdXoBE7KFCyHbcdyAbRV7+lJ"
    "xnp8MkQSaJwVUdQ9ypROXOheiN25yGlTiDCu4ILr/IjeSE0oL6trpX3+yQiXdWzXQOUZV3k1QbJsFklEtjnSbQr2hMUSnG70mCPr"
    "oOU07bkVW827vcd1g25uWCQjSiX4J76rAbGvZ7xy1nwlKH01ZtlXCFSKvXeqHUwvQTWnQ7twZUFHwG1+HSjT7zmCsiy3mbSlJ4RZ"
    "Nv0kAOUUlIbPnyrLttqjKFgqgy1dzNvaYaTLWM8FNTGwXl0TjHIwat4AKLNW2WVyykHdndoIYw+k8iGzW8Z2ScrPWfIo4J+WnTPf"
    "esgCxmcpFaDrWD7sBZ31cOPOanAUkpHXem/jTvDmqKuKtnmbMHoEAtMOT+VDUnq7y0Kzeiqp3htIbque+/K8yGeblqzdIcHWqB+5"
    "/KkSALsGT8q7Kuvsk/GZ6z5JSVtcAbDlQqrdqbjljrVlvTkeWj2Lru6w1b/yLBeu2iyCzPjUppGWhgZ4wbozTl9rq4o93tVWoOUU"
    "1md76oD5doFmWkRxpQGk/GS2p8UKedupCpBzn+f8Bu9AO2PCRWAu+S2ZRN70F0TCenZF+GSPG37OX4vbHSkbdtuevW8Y9sm5ZCdz"
    "u5S+GtwzXRorEzANheK6HBKReDSS5wMYCPRokAmdo1Ha7r0s31G9emW70ptSozY0/MbabDdLZsg938y47FCbD2m4avY822eIP9JL"
    "F9QhzXBClB+iIh/1vqkQyUTWviJCXRzT8cO+WnG8ZyHR2ZaFq5wcSzx7hAhgIDEZr6DjW2G5dCtEfsJiPZSRzzQRbZBC7qV60mVU"
    "zc2UTNVQVkkLNzobzWOfsuYIXz2Rm3Ir62GqeDFlJ6kluy5qFfckvTjEvzpVxUMk60P+1HnaM+kz+qj1wnTANIGC8x6TE8vnGfcK"
    "jtUBuxzmna4oDRelnDOWeeDD6oPt0o4fTTsFFzzjsLDBS8p0HwM2qxGw81APhJkEBIF5sGG4Y66jOtM9G5KHxpBfqm8pQNVAGbPa"
    "oaKaYL2hDZSITe/wnZ21SLyEpIYPDQxcaM+CR+O4kSE+56fHZ3MNq2nNyENr5Ap4i3dUKBLI163mZ59P/nTuoJ7QAaNKszGsCFSz"
    "jGjZ4h4DQq+8rHKf0WKIRT68JorSMzr3GmslVpOheC6U1YtczPQyBArqi6BH8KNi9S2lK38U6DQ/mNQypR3rjjJhxfMYHZdKOpIR"
    "DB0d7qVHk4Q9WGIaherASrO8rI6qi7+BxLKbR0Uy0cXkCxtT9ThDHz9F3Yei6pK8g+BTFpClKeb2gj+yHJ6hThAPJiTbG++QshJN"
    "S9FPTfJtT1GpwxJE5YYNOUIUb/iFBvxhWzR5RYR58sJsl23oMCVlkf8J/JEpRnXBRwr+rcE1O8Ii6F0gG71BRYiUm+wzP1JJnE2h"
    "e09T2Vuly8kJnX5L7V7WAVlru6kzIOus08dH5FI/ZvI2mOPklt9Tk3nTZLK+wMm9ZTMrllcwc/VD3f2Fl738YwfBNHsBPpyAU+SQ"
    "LZHYV7fC6Zoj7fSCpfOCjB6qf5JZrjEkrh0uhN1s4VPKwWLHphpd1aP1moaveKPNKi2eDkJEIZ/k86Mz1DvmCfos1i97QXCVrzAq"
    "NGrkd2Y0pugkS2LUOMwEKdVmIBPMymKTPfKcJmh4PINEWMKEYCTv6jEcVqD6ukF+tFg4nKq70cZLYM8LYtJH5bR18a3EzJ5qaY7B"
    "T26lYv9MkgmzUtgHpDuZNyOjhGSFCL851EoiFGxsD6S24ktfL3fMYyNsfSc9G1XDZNTtyenTr4TlqpCv/LTirqnW1P0bah1JEfzX"
    "v/9n8KxK6a+c2H6A5oi6pNLXwpRW8I++1yHSpjzQSlOTSWTQcCvSJjrSBrUvDSNpy6i3DmwRli14yUyVDbW9Jd0uSW1QKPV55FLa"
    "NVjUJUfmZqyv3oCZTaudd2t4aSrKsnjB1ivjKieVG60jyyNpL3gmMr7N1/tc8UeeEN9df28wD3faAxfQoa0WukDFufHGLoAmCjtT"
    "Ry9QgaiawQv2IuCjR4C27JLxC5A6wPjxBuwk8wQxmJzYDdXCGODfAD1TZikcMpI4a4QyOL74M/uRbIQyUDn8EEuHMrj4n0VLLIMH"
    "2ddiQSiDpykGl/KHMRAXf7n4D6Bdsc3QnEgGu9kwSaNmKIOHUzq4ZhgQyolmcA8/Lv6OnsojT1SDna+rgjWP9aAGwA5GSREhymFT"
    "pdCz/zvzRzbYGeZJHpiampENUtyF6cLQBksjG2BYMHsKl0Q4eGqkQ+g4RgybwVSLKgDkywAH9OAhCmxfySlyDuSVznJrDXQQ0b0+"
    "4WjIExNESRpH3CYwp6Os8kU6oOBraKEfLQ518NR2lQ9rCJZiDqsMS6a4pJxoB1Et1kFRoeYVltbFX+BDwDhPLv6ejqpJ5vQ3gA2P"
    "RuSjaBpgqKhhZDUaBnCwBho1HV78dRqg/YsM6Ib/ZJDniXjQ3mkd9kDUOhvgc2jsmqj1utGhXoALmhJlbzLqogkwMLn4my/oAcji"
    "BBhj/VDcG/kgcGIfJFFQTbktCmQ3imIdagtRKCMhCJ7tbCzw0RpMqYmGUE2Dr0VSEsKzES7iXFUZBrDEsJzqtxPcYcSeuWBKYLnq"
    "LkORb9DzEjSGNAIoPio9MOzaFBbiEUa26wX7osBv0u2ovppW4BeGbJtEJkyCI2nyRTvWywMX5IMZ10iIjcpNHuKldqSIlVpMIdkp"
    "4eVLTt9AXWHbQ2GEFjYdsnoEgOXFX/EyIzm6+PPKJGrETHhU22KLIicA1JqEWxw6IWa3wbUq67ETQCADdo7AiqtneGHadNXvC6FA"
    "hYvLF9bn/gNZ0JkYWmNAgqJJ8i1O9IJ4CjsSKvdGVHgkiPA0KFdLTIVHDQKn+hC1BFd4gj0dZ0kwy4ri4u8nYhJQ4I9Gi61xFoAU"
    "5FmKI5BI9ERbeIQXkBblPsqQMuH6g32L/j4wOGRWeGfB3g/Z4sALuiuINFkXbohsQfgFDq2Jd1CGncuVFC2MwyALRnYkhqM8Oolo"
    "A+nqaCkUKPHYVVuDgo2T02KD2eIN2xi/vbIyK2uU5YpVAjnXlcpnQ7UIDZqNLRlqa6QGa6JFoNBWEFmMmYzxSm8P3WDkyMVL2o3g"
    "8NRaOIZf45oloeCo4sijnlgOD1OMOIz8RuBpDrgUobMAwcKcyaaKTsKoRpME2Q6k4ck6ypFAz5B0WxyLuk2MT2+yb6qkLbYDhyh1"
    "mtdNxwI1LabvnkgPLdvTbn5BxIe0bXNneYK0Pm7WUov8QN2PJBCj3xsAwpojahSlZllzL9gD8gPcX6xwcAiDegvfmgy2hILYcTQV"
    "1EZCs5tVVkNSSIz4SWjb3DbbaoSDcMdNTNUNjOuNCPG4oihKw6oYAY4rWCvTmUC6JouxZEKOLTPEvUF/IyTEpemyHR3iMQlZ9vaa"
    "JLBfzOlnE2UDqDJmoQFl5sKwiNYwETxif5gIHFZ7mIhMhYmYUIwIFlBQlvpznmSIol+kF/85FXm2LFJEHuXWUvXGikCQGYbgyFpD"
    "RTxXaB+h9vl9o0U8V+xKlkq8ISPuYzjdER5S2gJG6HrGGrQ1ZsTOUV7NvDiww0Y8zYETeKE4dMReTgEfnC7p0BEjX6aOHbEzIf+H"
    "FGaMwW7E3iLWhT6vR3QrCBTyBKmAP4YEvr2P6I02h8htDSPBFeIEWvKgWxa5J658mOH2SBKPYGNG9ZWivBDJzHFj4TuBJOSE9AMm"
    "8YuCSWhQ2giLYkloyOXRJDTo2LfO7GgSclFg0IuFASU03NKYEhqyvW07qIQGn4mCDvelr4R8vOwCVwXz9vawEgaeAzRjmWxRbAld"
    "4OI/MWCzF14FmDCoozWFMYajZoSJg1yUWSPCxF6Sfhs1Q0zsAoEeZfUYE18KkFMozHYj0MQj4Bnp15En0sTONIKTWNYMNQG1xaIR"
    "amLn22riCTXxLHubNQJNPMuKqBlo4jE+SZguiDTRFmhCH/LaIk0YguUJNXGIJ2a5ddoCTWgD8Jri0B9twtDmOrwv4AQ0z2ukLeCE"
    "BrADTuChdUHACbUNCl/UCVYctoWdEB8g7gTIYdS5WtwJqSgKhlHyNqvFnvgGhE4RnETfJpEn9MQ9u2SfZSC0Ol0h6+vZwvgTRjex"
    "JPwEo6wxZ20hKOoYNiEonpj9vCQAhTyzxCRNtsWguEcLYGkMiijXVKotDsUOngYjDdYHSTqfIgZZycMqT2ByMCW5dQSJSc2nT4b+"
    "OBSHgpRix9nXwheHQmVLFXrsC0RhwRDXBTl/pnR6EzEd5oKmR4elSKLCG47i4n8g7cXXLXC0JW01lpI6KH9oCilC1GNT6MWjpXW1"
    "a5z4FPt01sqZq8xQCh5Gkyi9+EtUD1IR5Q4e62Eqcn+cigk74GoEqqBe575IFfsgeteyVcSBZITuR5UY55nceryKEQkz04wwaKa4"
    "GbZCyjZxxGcIg3A7eAVfEaTZsugVk3roCkm2UoPcEHeNL3RFVBBvj4q26BURR5ioaJ31AuuAefFXS7WGmgvSruRt8Sv2kyPgvKjd"
    "lUcNHPhRo4WFMSxY3x3xJlSHYVIOS+U3Lr8XaxTJ4uJvKxOas3H0LRRAkik1+W1xLHgR1ANZpPZt/T2osogSbIYPdqSHPclGF3+T"
    "qvWctLxa0PYFslDLCvudZieRWV+qbbvNJSEtLokSCmyxACUqrEWUL4prgRonKC7bzJuxLeR5PeGLNSQnvP5QW+T0EDUY7XEuTPmF"
    "wS4U2H8IX8SLQxYHAqTLLGPCx03Ya4DVqC3qBTJIhlhazvLNASs2I76Jg5fFLfm6JQLGSADBYO37ZcrIgetSdPPKnXJ4bD0ohqWN"
    "KDAcBjEMdhWomL0nOMY9W9BuC44x8193LoqQIYtM/WWsQBkxeqXwh8qA1SmQNJqLbW+8jBoYqY9adG6emBn6ft4XNeOpvJei7Z+p"
    "Qy86GSoTzR3s8Bn3MQOmwMTPQPqBGlMKoIHmNaSLCYPi4h9AMDFZTSpF20CTrbS1pe8STkNyC5myPJxGSzSNPXn9+D0F09Cko9lP"
    "N5SGc6nfEk3DwCwIqIFKMySeia9CO6wGwEX5ZQJrmKOICqxR5smwuvh7nBUtsTWIVxDXpAAbVWCpQyUm5D0r9ALQn3+4SBut66Lm"
    "BD1vw1AjIEC+ONzG84TYp2aH2ZJQG0rMQTYjUrolZ8G0JeLGQUZGCjnGnoASb0cTRD1piCNLrPVF3KB5SnJzgG4JuqHgbGW9CrwR"
    "i2WBN+7pQdA1lLmFMwh2r6FYp++5pKNLGnwoPCJNu7kcrYqKdb4YvhkDjmR57ZoLhcYcGqJHf6gv/hoOGSldtShlnjcGx+HFP2jY"
    "J0nBtiOW4/aoD9IRfMasw7cOTHhkYfGJ90JScSCOzDKKo/XNWnckfzO0MTAY8YXjcMUQRBsLHIHeUDgaKxvPdSOgZVFgS2Mkw7eH"
    "5lBynHf512J07ByBaBXLOwGrYb48YalRGXAsDNCxtKLssuE51G5kUwOJfqMCoL1nr9nl8Tlyy8/7okqzqwfo2MlgYZ1k9RgdKOOp"
    "QwgfX/FI7IvUsXfxjzg5okNHhNwW763o3rbMGjE7dmzEahknsw8uxcVf4SiHkTvkgoKOLAnc4blKiiYjEo9zGcfDXZNkBUT3ubRA"
    "0ZQIOvFo54k/mocYoblXGERLVkhbMA8sz4V8sTzu6avThwf+aB5P6tjxRvQYyYgemmBnlrfrqbzDsAN7NCbOH95jcpL1ASZ5y6qx"
    "jKnGNLKjd+gQHywS44zW2LsvyEeuT0m1SB9PrfvkhwdkLDZqrDJpI+ZaFeQirokWoTSQUFMsTZN6lkkeT6vVCFuzsZsVgMXDGQiP"
    "aMsV1AmkN9CHJHTyNIdmWqiPuWSwD0XAdeliQXEr4od7o6tLN0J/LGQnoWYn9TZ7AXH5OJGiPyvFeCuNpAqRpgfk56wR/uNLXDme"
    "8B/EuFTpWviPXXM3Lb1xuzFADrSliW136A8D4kxFtjQWyK5nArNFEUFkAcJhIyLI8zwbRZaI44QEYYWVNyaI1GUZgQdr94YEeRoY"
    "83ibs/BejYVUFqAOLS0qOOTgCd6SpIyuhbk1WjOh/rURE6RmLmEP1woMYneHhUimuNQJpITebniihBAGmHTaTXpjhLAC1AFeEChk"
    "l9X31kHVjRSiOJ7ajcAt8TkX4VMy39wfNsRrWSFtJloCh+xaMhsKhdLoiLAjfbmTvR3LndOWACKckFnkTyoAapFEngKnKKKWWCJN"
    "PRMKAiDimROxJ7QIgidTQn6MxkIfLLDIXjTF7Xee2me8BZFFRgS/JLQIA3lji+xpHVBreBFbI1SPMfKc7jIiUnad4GsD7nVLsJFH"
    "4gROSIuijXB9AOTY93vDjRxgaBNkuyONsvZoI5lzFdUabuShntblAUciL1Q94ogfyg45Upu+WswRoL/ycLkw6sjkmCzd3agje5Lo"
    "xO5VQyP2CGrJ8EDnbgO+pop8MUiAER1VZKGvLfYlvfUGInkkaXFTOmtEIyEyFKEgEqXHVnU6HgnXRUMxqkdvVBJ1IeWQBl90EgnI"
    "FiiuItgbpoQPkbXxemKVeOGsgCXO1C4KWVJ/euENXcLbAW80WwKXMOZQcegLXbIvijGayjeDlyjdZ5otCWFi6eizehSTfbopEHk9"
    "ksmjGnpMMJNHindeIZyJijTCLwWAJPmDmtxTLN+wrbbIJrs+BVJLZBOyYLR60BbcRF+Ueat1o5vsKb2BrSDnqy4KccJXXd3GPvQF"
    "Oak9yUGRRBxVSaVCj7Dxr6qCtphtgCn5u2vuCacH9QQkwlMYbMjKF/DkEm3j0ICFVHT4/o4N23FP7sM5ubEs3bAn+jztg7NDmWBd"
    "1MuTpF6ZDabra8IqMySNjxla9lRs3lqqmwVbS1flpLknmcrQMvN+KirUgmhfBFbgkx2bxqeG0GeVfhJjaiQg3CWyAhBF+WSgOFHm"
    "D3+itntjQS0Og4LCAYZBMdg5iRQShUOBvEFQnKGpJzykTvExDT3cGARQm1brW56YLMV9gVH2PV3yB0aRkJqOtcRFufh7poyVapFR"
    "mDtBvzE6ijS+aERH0UB3/UAyQso9nI0ozfwBUtB4NaD3A25vVJyUfVgQFnvU97EFLwk1ZcCp4vaYKTv1p0hKxqf1LG37tWU+tcC2"
    "8XbL6eJoKtajBKetBYFVjF1iLbTKQ9+A6yFW9qqibIhZdpyVe3UjLDfWiukFIA8JQqKokD/mCl4+8GQ1GzRxV/YzZT7AN8pwvB2i"
    "oNhQVbkBWJ6gohImbyISK7cRgaUQGDQHNVaLg6944OpxV54JwI39nKgZeuUAkRLT2WwMY4jaw6444l577BVXzmsGYMms+/slEVjk"
    "2sG+keCB9DK2b/zvWDf+jVAs/JzE3JooFuQaDegqvEFZ6Ia91lcrLAsJEXwVc/FXoA/AkBKl4hnXBpGqisgXMl2fTDMMqVpkw5xu"
    "D0u8G5dKUbIDyRbGaklY2smKhdFaUG41wVWSDxmpJfFGakGUGFQTm1KEzxOopZJ2406kFs/QZKyWnRHstNTawCZQi6ssYTVRJMFb"
    "g7V4ptYK1+LPtQO21JefCdnibHZa8guDtsidSjZBkPKWGa39HC8wz1jE1H6lXIvdAgdzaM1c52hzXE8Ilyzn9z4YLyUyDCOtcYXG"
    "O2SUryUBdOhfXNdpt0Z0yRaFdKFuLQjpglctJd4LkUiGD4e+jbxRXV54BCzVbwrp4ii4XPLdHtbFMhGwsQRC0XE09eJF3Y62BHpB"
    "PTqJqXTtateJJ0c2WaXXUs41WjPii81ScfGQFZFkfBd/HyWZL/wLk0kbqnXXmkgwGNTl4h/AkzLr6tsh+W5UGIf7Fv7oMEvs0nwd"
    "cgPFRN5AMQ+bbKs9WowtGzjhYg5EkXmDxez70GvHjEEJphE0xtMpJ3IMap2MygGNi+Rpxhs7Rr0dmtokuRY+Bu2pcRU2Q8ioZ3+O"
    "b45aEBn5hLWojqRCGbqXCzhykYkkHlqGE0GPkZxwMvf0hT1bdNWCyXxeJXyHr96mKkOzelwZc2xBK7mC7khtCwXbpAKlIv/TaOtp"
    "sHCdLKB6XgkZfP3doAS1SDNs95uh25n2IZiYM08L7SGC+iUN3CQy+VkzSd/++poxaJ5JdwQN2dgEolGrYpjJd8d0PQZEStIj5dFA"
    "X12oGwZXoHYj0+ycJKzydeA4PE3kiU+zw/mx3MAYy8E8a7IM0UF8Ivt2utGZZrJaIU+KnGYeVWS+MDUXfz1JokVhatD5H3FYZV5o"
    "OKp+bAptJGZdzUScAGWYaly1hKkxdtNkM4923HzM1/WSWQx2cGG8Gld4Uai7XNwaLRyoNbWg9BPvHdwlmnVC2fC7ikYwGySVNdNN"
    "TzwbtToz96Ub3cLjAlZMLFsQzSZqD2eTqXA2U288m53pMCvqAW08/jiaYW0eGwtyTX3Yo8iuls7c0DYvSKabVGnkxLXZJ38wlO4N"
    "bHOPLzSlUxOBj8JBFgjZaYosF5yAcMlwaFVAq43oyFQUWk9DTlTEEVqzJEUzts29t8kwsamWG95GkXCpEZT+WvRYA8tMk0nqtC3I"
    "zY7BkT/KDQKY6vqGHHsD3ewUwbSKSULA8C0TvFxU7xsCoWw6auYXjTg3j+RDnKL2pqYR6yaRl6rWfqG34dhOrsgU/GYqFtlPTPjA"
    "h6QtKYgAVpARpFU6ikiXKYsgZYyIvEazi3+gHwVjP6wMg0KyYCnExH4DRGdP3D8jskbZJwObamqC3VjGNkovqV8g9YIXFuSIzqKk"
    "FpIRcYQKiYMZ3og4SdSMiEPoQuFcvXOixlui4tCbRQnYGhYn98fFYenVhPVRbxb8wXFmFBxHTGeAvyXBcSJlNhblzQg5yqpwUZyc"
    "2mKxnxzNyDOVcTM0iZQ/KLWvOgUdCezzXyNmDt8fXfwtHSV+MUCHz9E0C1cX0avRkrI6kA4MRLJKvFbIWW3YEk8HZYMIOai68+Q3"
    "g9b9Ch9IsvpGQg8YsCnQMgwXXcBPNaRRED18U32AVRj54+rsKBW9ZWTdCKxji4DK95fqHrryygMXNX008apEW4SdmsWYDLST0UMu"
    "1mxcJbqOYxTfCLBj8Uu/eYZaQo1qtMtaU8VxlrOFMR+O2dqqvPgrXVe4YXf2mbBgKWUYigbp5p2vCbuD+7jF2sMXeecx2f05A0JD"
    "MjS69ETeUa85LHBf5J2nVm3iLYh5rkrFDr8D3esUXUvOXxR4x6mX5CRye5ZhUDEX62oByl1uq9ghtxF+p+7G0A3Do3cuNeKDteLx"
    "KOARHjlrxx8jlNTi8uxnl43Kg2cYrvnk4m+wHbNCqp8LW9pzrhACu3Y4XaN73kzEkXLnE7lbKFO243YV9xwzMpJzSrSCwwV58XeM"
    "y5Nt6rtPDMgjVLd8IXnMSVJfY6E7R/X6KiP/p1KzwTeGiHh2cWdf47lXLSxsyOg8OOnKYF75frNuvJrxeXaak2uvsQiv7ZxuyY4X"
    "5PBMdT/OmvF6MNAOnf0y5dOvLWTPAaC0opVmVEz/0Qjcs0Ohf7BGDN3DfUSpLEtp2/bpqGNdSjohfHaMYgwSWgP5kPOUqOkRrB7R"
    "R8l5yn+rL6iPwJ+lfO9p1euP7PNUuwEEWggrPGrpSS84jODwz57ZYtkGvtWsteIJ82M6ZMF5o/3ot54U8kfqvJsxf2q+bnCmQfaf"
    "uvdXbtAfzQZS9sBkH/6UAW3UiP7juOi5YuwfZXAdSS8yzfA/F/8XfOdZLf7PIcq50tLECv+zSxcuZKJtnmLWQgDRm+vaJXI9BJA2"
    "hrfMRptxgJQHpkYsIF08I3dNLQGB9qLpDGgcpTqKqpZ4QHh6RvAICW0HIwBxOCBcfhgcqCUekFH2SD9rthuhRlQgQqzjY4EeoqvH"
    "UNJATRqh1eMCHdZOH5040SpqOiOqivBswxKvP0AQyYs1T4W2+GhWZkIqFHP344kW1Fyf7xMryLtSm+GC7Ne8zeVjRQxqXapO1CC1"
    "kgS7bmmpcaG1ui9wkL19fHGDvpRRS9jQWclIC8IG7dVc/mn1VsKnYEvQ0hYzxuFASwChxc3Xgn7w+5nLRw/aMT0aK1NOf/QgYify"
    "WQ4enp+T5mAopitFNRJ0RR5nfueEC6II1WqtXe45ryKCcZXSsTLVnLwlnpDk1cbyxRNR6Etpgl/yw0DFtu135Z4IQ/uCuYJtc0JB"
    "Tl03is3wQtJTJAU5wVcutr2BG1OIeHU9qtAeuSD0xXFxSmrs+WIKAUtuiSd0Ly05dmKgXki2taZjCa20BRM6FOlx5I8kVO/Xw1S2"
    "bQ3ZjiQklcbOgyS1l6Sbl8jEGGqJKIT7rhlUSF7XoB8PelTPDbTGFlKvyi7+52ViC9GQ9OLzRRZCLUzWFlRI+1at9W5haCFJpbzA"
    "teBCnid8wp0EO87QPln/MllpizTEuTXstEUaOmSDK1qmrYGGIg9ZukSgITxBZbzJiAShEvEE7+vZTTeHG1KLhj2cax+WqCtFCg38"
    "dUKmBtNMGqJaFqSkkpTUquATxnHUCDX0ME4yuutzAg1xamA8ifuCDV38GZ2ffU/hhmTlqKjCbZXIDtUu/mLlpRZpVoIRh/DNsX5b"
    "fPFXZlmsfXMOpxJN9WBDqNzNmu9KrGhDB+iIRV4WurGGdBwJK9rQgXQf0Yw4JI88IzJvT/Jm1CFVFEcxSYaC3k9KiSqjkENCXi7y"
    "4kPCFuXN+EO7WVSsnKAutdDujj0xiDzXu94IRPKQ40YgOhRVYbxguwGIDmtKk0YMoucVKQsyPt+oEEQ/8jVxQFagdIM7EbiC1Asg"
    "1FBj2I3Mjkq01/CfvGj2bIoh5QQogcTGcnwkp8MWKgQRP+Z+dd63ID6RjYSZfJNiZDrLITcqPImu0HPZrGK33sq9ORmbg/SkIKUj"
    "PX40Kr4NxEmCHmxkAxywCL3KFJtIemCwYRBxmKIRO1w4sUUwWYsdrEiiYIUv033OE0K/r4Ve8AAmFy9ws9xWmznPf5GcYqQp9YrG"
    "Mc+SYRTciaaIRTvOWmbTb+MLQxr5OpIlxTFqdS9hBTASdviih1YjPMMF7/VRydopx2NDQ13cGsXo3lsxqlD8ukwoIzxQkXLOhBgw"
    "+yWVdwJOJCPLhlwSJ3xb1Vc2yua2wNItk0V72uoHQgc22qkr1vqWJi1U+kzhmD858Y3M7WhfswjuETVownXYUY6IOiXqZTkL3fJa"
    "3bjZxghHcGaVUUeIasi9Dif3ghSUALvQzKQ3mG8iNaDAZV+PO6J7now75dlMZONAXNsaQMcwWPS7d9dEDz6nnW43FxQ0PK0mk03Y"
    "HUG5pbJASsPJEZ3B60E4WBl0e2X2KDsFeTUqRKe7KUuWW1tbg1kJlZIeMy+Lr5LyuANJUGR7QDx70CcokTagREpQkNPHLsx19x9D"
    "98MyTLvnsh2haxDcIta7LfowzrK7vZ32ptGs8/W4iwwy7oit31y7JiAdi5han1Ctus5yW+hR3vi3886/nf6q+2/zG0chQKXdrd9Q"
    "CKpy+5DQ1ilfpq+6/cH5p8Db54NuX8yRsh2MAa9SEkARZBDeH2+di7T/Zhx+IiWWnfE8fDje6kCV59YUPaIpggxhevhs3Ome40SI"
    "radjPG2PN2EOvYNXcyc0BIpWKpl/bJb5mayOdAmHQP/o8ZMoH4Ko0zkY64lsQzBXNB/hK+Rzu+45jf/b8dbTDva6G+7iJ05jN/xy"
    "vPWgg+OFefx23DuJJpWAfPmRRifJUQRd6amwj8X29stm6iuo9IFVE7f7XvUYrL8grKs6bNx/RTnf6hyYM0ggFBr0bjt45Itphcq+"
    "k1doHIeiK/E3N6197ixFWJn3xy+/lG2/eilebW+/GdMfBLOK1TfG5x0M1/cwLSc9oNJ5NHlWAVfqqKq6PWR7oxJ2CY4ByP9ge/Dp"
    "uZijldGgLz/RcGgQnqf9Muz1eum8S3P7Baxkdq3bx0a3VnFPqMaeUMZ9FKpK3Vp4Po1AZqmm93P2U0un2gKqBUboS5/DhuUqRDck"
    "Y54+7F1AN66j7cF2cER9fL9WV03tj6PyuJejZyloqEuGTMMzILuSSMoG1d4ZSFpIU/TeY7bHpnfZb9bEXZwASLwBn+EadObz3UEf"
    "M26bjNuU8XiXRs9JG+EqJL3ZHcxDfKuGLbm9B7qeFPcBz6XAQcqx/Ne//+9qOISE8STLcqhw4/bqajdMncRfYuKN26uqu52SeoQv"
    "7KEjg+6vcCr4ST10IirFcxAXccI0hvZlYgNHCH1Ynk2AoFCMjUGIj86dFIMvrA5r6oj/BuMGKlBeup2r1BodZbSuMREO7qedLqK5"
    "fUFIZMF0d1ZDa0WVK4BuNcPpr2+vbn8OtMrE3cOdNe/2018jelWejLxHu86qK0X0A7CEigBRNKb+F+Me/oWZhd1pcZFviGop3j1F"
    "MtO58fLf4t6rX904Ur26ViLnnYj0qDz+9Yb5/s3WzevXeVUDf9t4hTRidRtH3u+t373733TW6qvur3q37nxmUtYwZW3tpklZf2XR"
    "qd8ZRhZno4oiRY5yjD96byLwV2cQJyeD7ia+robp6o1Qr/y2BM6TFQlW0Y+GRTYBHG2eJAWIXZOkPOsf0y3pJp6XjwhhfSBUnZWV"
    "DA4oK8OjkI96+HIhLbuDUDeNYUZ60WwGcvXecTJBKiA3BeAPuOEe2YSJmJYOZPZMCxj6IDcbWNL8DixKSaUI549FnESdQQdZtsiL"
    "FfLpvlKMjmGwfTgZ5m+6IEIRKF44YgJsqQneIoB49Ou19Tu1RIPKP1ozjGv4xbNHh+Rt5CBCgtlR91zSB0kXuXtngDFaxQB3OHYy"
    "zFn8wFryLRLHqDVYCvjNTW6XfZy2zfwajOz69U66lYen407eDcV2D/5055t5h/GWbF1+1JsJ+Sg8gXlAm0qRwmoZsA+bQZhzfRGN"
    "7HFV0kieDjkGPbS5GfUy/tXRk6k+5EoKz6OSHKegddq11VD/uk+BCfovB7TCQIodTaICdtwAnTivMIJezbkD2dYpqilPiW3jIQbo"
    "SScPN4AeKGKI+Evk9LeOJozogpdVgLBIyOeMrjDrstT0B+Csr9lVOq049HJZ9BEFh6IMYf4e1fPUaugY6RWOLr1GJfMwKfQvrsWU"
    "FUsK944j5IjzsGj0wKmkpTTMMpWO8aAt3qMCLkh1EN4WYaGlCirXcSjkn8YaacC/ovyIFk+hSODq9es6DegcrH0Mlxysbtup/cFs"
    "NJh/en4vt09GJyuwmAY6YWcy6Qww6fWgOx/QRP9+vPUVeWUF0k7PrzGsPIZuBb5kevgp7fBPfjtE5ekNVGJiwOGVgM9unyja8+l4"
    "S57mDs/Q0gU2rqpicP26k9VL0KAAJFGAKShlsO1bBvJwOPetEVGr021OoF4cTpTViFrZYhhIv6a+0WyqzLCKbdWHvm4wpDEbIidm"
    "VssF/gDSxH8S/pPPOhY85VnnW27y14MKu/ayhgSYVBaQxMvBb3+rUgcyWR2kdnL014Xvep2epTNHUpd9yziVe0cfbv/wF6zRPDsN"
    "nkMPKUJvZyB9qwfoaHk6KwN+iUxIrHK0dk9XqHfDiYCzJ96GjkTvXx6mAT30QPAhZEiIkODxSvksyIZfA71BG+iiDI4xGH0UNLDQ"
    "6QZTUR5ncW9g9VQOgKQeR2OwpTUGCkMRg27iyk63zue9MuPDcQ/OPRNkmwUqCTt3wpU1IxAhg3lK/asvG+IxTgq580WmBWUeRzPg"
    "T/QJVHGw7cxPn9J31BYFwBv/W2e7/yJ597ALwsV2/867tdvvNta78Lk3iaYzEXe5hk9v0DViJ+1uy/H0ecNbhzOZcd4plWhd/kZI"
    "gtGFXqOoJX9tgnTZYYSsApelJuCwtZn+utxMf/Wrbv4yfbUl4B+Fj9w0IxfRORdXpx4Svy61rBsLGlUBqVzVVGseJmEUZmGx9fJV"
    "ONoC7jjZurZGZ1oAjbYA/6mavC5dOaBYAyc9zOZJA0ShPCDXwCZUsjYXkwKjreedzWud0VYn34q4khQqQUc3iKOiN6uK404uz6Gh"
    "IrhQGaAH+9Ld5GMxiTfYtwSP40kKNZ2dyy5eG12/TuGxUYqlgUHV2ZZKAg4re5lhLzN17NHVQBWTLu/DZD5Xe9ia6kIREl5eScEz"
    "qA9QgaUhGDnzxQ333ogzZJqbGmEofz3FuM4ZkPHyjCetkPOxtQiG1A0wvnwr73FUpY6my4YCeWvAm8s8mZV4jIMu9gQc3JlMzOGk"
    "k9JcoAA8OeukIKYoTKRmcF8gHtRiLrdgkfy6zis3S1jQcvSGO5av5MI9n/ft1M3yl+vbgDK9jEKYcjyM3Ytgzu2BTWas1IBCePZZ"
    "MsBiWwKQ2aiQAAke5sNlRXGF9u0++Tvka+CM+rgM+SkgH09ozcWjBqnmEYhINYPGuhhbebu9xXPaP/00NFOKUq7W/crfp3lSym9A"
    "ocBZgSKm+YrWOc9tjF3RxN2IF6Qk0vJC2S9/NbDOIbFhFMS8r20NmO2QRtmoIyU1U9SqRB+A0wStthR9khKW2hKKAiFr4cpzq3JV"
    "cb7ZYKe//a1VOfM+xanIlI3TCX/I8jTeDWeTyt0+H2K7yPixT+PZlpTWdqNC4OEQiFoKZ3EQaWZF/3xW9s+RQsulGkpn9YqRhLPy"
    "6YzCNC0Gq1I6mcQSahfVyFHaAIsXtwYif4rp/fNP+eD7UEoO/fMG5CnS2/55UrzQTSfTKZ7iSlpFcI6J8T7HFgfHE3QaJ0+UfXXU"
    "MfL3Hr27gMoKOCi+e9fx5eBxmZKpkj2qQx+fvFWBCE8DX9I9Q46xls1FfaW0wxFsrVg1jSdbq3nOfE5w3G3RbS+81TyTpe31zJci"
    "wNe/bp/zqtRfL2AJTmuUTCn3JnKuwzzLSvOrSmL1+Smejw9JKZzlKpFfz+yRgsY+ZZGJAVKtUEsS4SichBWhuzcrt3toRzyDRblV"
    "bXeESu4quQmSRA/tAZAff0mSgOQW3DJSKizyaQ9XOIl/r2SnNkE46UClZbNSSJJihVtZ6alMFX73LjYVoNhznGVvCpOEdChLdy1E"
    "6LxcSTdE28ZbnYS79CnZy55UgpyoHZm6kq3E9Fd1LlGomm2Nt0H2cqswhSOUpmoVYlqjwshFrEYbSGTQQNbaQLaVNRrAtEYDGSO5"
    "3yla6yq2CrcuVVbifGZAR1uj5vQ42fUpmUBSy5RMeEpGcn86i3oLT/ycDut+ywCgp1oQ5RsFzIkeTvnhYHbyOonxDB+yxjJu6h2w"
    "o51BlnKvYoTlLfQYzYAa8LwZtx6POvsj3u2fikl3W3311cd2jym40mwNXn563uzu/NVADo/rxQOJ+QWzNNr6Qmob6vgOnc3vqVqi"
    "c0aqxW7XIvM1Qq4wsGuGjViY4scijD1mAIMxNmRtL7BrQWGpir4WtMCgdgvp1Dsr9SYYjNpIW8fB+j+iwYpKG6S0kuka0l6o+gll"
    "dCYHUYGyHdaLByCekIzliR7agqCmS4lyst1CHDyXbAREU/UNtKa+AFRPUIClKol0hAPaeT28DSSdsa52nyUIu/bWcpvADWCoKf4L"
    "bOk1SKtHJMsWzqC44y97vZ4+LbySigOjNfgWeea2kEcWyaXgqP5lPQXaQZzbE/WHca+hBO0MhiDJDYAidb4iF3Z7h4dyJ5IgJOU1"
    "e8F/PsmGeJ0rZxBqbapFVbV2OZc/h9bm8esvLykbqaqMjNRg1JvXvEO3hrnNiwAohmTVnNxVR2teJJD9+/FyLOlFSXnXr1uACwv7"
    "MWmXpk6qAdvz0BiyWakM1rpQjygbr5kGLo3bfNFBhPCqAIFSkU5ZYqBIojMG1TdrrpuzgbuXe2PkbcV+aK7xIIJ+4WH90FZ/PPEt"
    "XKkw7sqdg7LYVkdJRXL+LMGGDqd7VIZ6V+PL8rAF5853787h6LCV9/RRKYy20JM9huBIRmEGPxgHYYHp2NCmRFOyjZg0uNJVrJCj"
    "ADiHFi2IC2UNUa0G1eylK8hqFXBXL1ucL/rqhfmiyFswhP+H+fGRADVB89Y5vPIO5LkmSTuMQ5A4QTzyzjeKSPL+ko6ovinXshJP"
    "OYifhLkp/OVJ7VTeyitG9MzgWEkjZpfOlyO8E3trj33z4Gtg0aRM2yalQU3aJ2dAnvxXSMWudtlxeBS+3uoc+5F+tHWMSH+E5TDQ"
    "eU5YB3JXQ7zUix931bZ5bVBpNxrSSzzU3Pgx2LLunH7jQdB/+GwyX0lCltCQA3phtoiGhGKBhEqLrUsrLdlyNgChIm+uKqeGFc9S"
    "aFlhm5TonILh/CUmgJAWgaxJq9VudGpxT7H2gfPdO2MIAM14OHeTU73nzaNVz3wTWKf3ZhRkCFR9pHXNB+odvCKrXe1VFDzLYBdD"
    "+FQc0EFYbA9ArtV6K99l5LZfDgYR0ZJugaG2gfW1WGA31RG9mtKs228kaUUcydYgz/Jxu+Va/aV4JZl8ozFM7W73AILrsgQUX21/"
    "QI12Y9Ws2atmzbtq1l71B4NmyXW75Lq35PqrPmxaOdLntZ59x4UMrKfcev/hpFvvPSCgdo2yG3bZDW/ZjVd9upS60btxxHeGJfDt"
    "a9fSl2WvmE2SsjPoDbowtFeh1OY4CwSNoCWNwnOHT2ME530FQqw524p6dGo6FITyAiSvbEt17d27LBwpCDpXhcD+dc+vXx+F1Va+"
    "nWwvkIkPnu+hEQwLxXgb0V901GtCy3NXvJVonZsBBuJN5qktxb9APj+HWkL495xFrn6FA8c7qrGFwufovxOYT4E3qerS7t27a8X1"
    "6/H2RI7PoKEjxaRuH5ugRqpuiLSIU+A3/VDrGvv5YZf1ktPslx3rnC5PsJgSvrTP7BJzn5K88grVaqMI15zWLvhLf/qadFsHz+0i"
    "eqwKkx9svLAVyy02oZqNVnBf0jkGlU+D69dfdLRi+KUGKng1D14ZMzqofEC2eom0J5HzZNeFSZMZppIVKqJlEP6x6KTbi9po6Lzw"
    "/vP6dasitsehqpqwtDgNcFMwIZOfOthcNY+VCgv9ZgO0HV1dPmBPr0a7RtvvCjI++RMpR87JnK0v5vD/sjWPnoVqSr8D3fXQznWX"
    "wEqakGzVW08u36ybjAfR7RzNPATQRJxyOH/h31LuDmWTl1y/jvSx0CpxWBLZq+72djS3lpo6WR1HhXVr2xmwPn4AqOQvYP1SRe8q"
    "1pNO/Q4jPNEZLBbO8RsvuFHoxH3q3FGhwK1Q4hMb8MEJ3srTU47l/eWqoi3V3R+MuXgQEW8ZJCiUV1umWKy/1RzBIo672zH+rbrb"
    "VX8pYddEnIh6P1aX6wldq9l8rob0mrmjpSU9kgVChuNaNAO8dDWxKqHrmZXTD0tp33Pjnuv1b3EYFkuUalgohuyow8h+AYeRfCTj"
    "AOIl2adkdPh0LKsQ6XIkU7oGNgZnagOljQ2UxAPUvKS9JN7elkeFBESDlEac/ROIuq2zzgLYubIqJC5Jsti1NbzoevsxrlqjNm0I"
    "mxbLdHQ9xBNFsXBxFx/HYOFs8V0mGi01lQXNUrQkKbpZ5EN8G25SvYVeeuv7/fiy1YT5K1RHjeSjiv75UYM+2zKQZ8122hhaKIUN"
    "j13cNyAehGaBiznaYYVxk6h/D22LJvZDwbJKyHKtuVN99456Wk/Gzlp2OS0G/8pkyHBVf2+1aZFTah4CuWurun5FXiUEn9Zu8BT2"
    "bPNHKUafpFkstntkJEXav03XZBFtd9FfDNrqySQhf6pRQMmuz/aRbXzSGSBuDY/cWrrbhkU5mlSxQCFxjtub71ZaR1nHFEFDKcKQ"
    "pxQtcklWtKhr7QOVVr+FnIfyDqyZeFhvCjZLZ4HKiDWpUk3ru3vrqv4rs7OGfpMHc56iA4a+vnpos19BdeeomNVNdXpUHDpbK7gU"
    "19vSRgRKptGCuamr7ZRgaw5o2DZtmAXHKR8CNY2CBaeQ4fBCadpnrcOQor/KFDxmkvFEYVlNQCGqsG9RHVkPDNmpBX9bdeBP+kI6"
    "qQ/wHrx4twmB86KobxVzqKB3C7RXtmsv8/sD2Ci9XMQV4MdnSkfbbB3I+FYKxeFglwK/2rQeAcw6udKA9fEwrBUe275q+fQjbbjR"
    "MhUvv8hAFahYLhnfytp2grrHEHOAMMLHPCRdZF3s+zBY4tOxQZJ6KdkplfhYNtF2JbxpEvUyf0UYVCOCKZ/NGu+CymhYDEKmQoN/"
    "CeC/3mwFE4Nz+oX/SZ/3/WA8EW83dTL+WomTnM91fYoHME05f/4vVl2TpCiXV6dfYHJQl+REmDz0vT6eZKfoOYOeYuoc601mEJed"
    "f8Wu92Sb1nPKf+229GsFI0pgbBqrg6q1lbd9imrc7MfKWbMnxSjPJpOVoTiOTpIs7wfFNMvK4zrAMMpXTpO4PO7jQ5raGBt1kKuc"
    "JLW60T6Cfn/lVAzfJOWKbsmHddNqsyr4u1KbrUXT0jKTQ7oc5BtUQEM2SeJGJr3Z9E0ZZZPz1lxNmlVMYq6tGGW3zzWFkk3t0dEa"
    "hiUCK2utrVQanawMq7LMUqtgNEFfaGkhSt8KVo+Ig2vJlAIfpWVt3xTHeZK+6QerJj3B2laGk2z0ZoVogJP77QqGKoAVuW7Sjskf"
    "KHR9dfWXS2clmiRH9NALuFhAzhdzk4nuYJLxmcJQE8C7zwAzPcaMZ6vhf/VZtgo0Zrg+tRasM634n9Hh9nWabs9aHRqsp5wX/Gs3"
    "dEoAbUehauXqJYcZzmIUZ6dLitmLWBXxj5Pz7BJO9/r2O3MLyVVeYOYsS8ycLVrG/XE2qtC3WpHgk7/z5hpbu3yfqa4ePcdr7f7S"
    "knKClzaAFGU5WGNpKSxm4zFssaW9YbB2MmJh8pijglxmwROo27dm1RjiqElsmDKw+F8jDZ7eAYNfUoXAXbx6iT70gb138nIil76/"
    "FQ1kNad93wHbyFAU7azdWY3FkW/gdXLsIY3eJY7/VQUyGrokqfPTRYxrIYc6PQYiuQLbDARrqPM0j2Ym8yiaueynBynOHm8RSFoo"
    "ZDtf8/K0xRy0lXv6YBtAMw5tXQOTqTbgGJjEyqnkPQ4w5sgoV5ch1wYlV6S8BgFXKviRswcOZFNDKSdehSc4m6ufZmUHPkEoQHO5"
    "uPvdiT9P9JWofq1Ig9zXq6zT+Vr+5Ql8reACyq4QhSIwelQ6wdfeddzVyX3rZmdiv3DL+/akLHaFXbyMq8ixXKbPDHn1TqtyV+i1"
    "LNLe7RlGnCsu0WsCvKT0qcEvR/oY1kP/9PpebTtMUdHWnda2q7jBq2+tRjnf/mpW7tlkDaAr7bRG6WWCFC+DFfeg6qND+khDp6NF"
    "Jy7/cUo4y0YvdNxqIMFM7QEe1/maBX3c4GzeZWnX712YFj8M1m+tTjGo0TAZwbn/20TkndXexq0wWIX/763Dx5rG3yBUGuFzNFbx"
    "WO+9HEjtzWxlZN4Pn3/CqVIxgMTsk75gjXnPpM3x/qQbTvUz5OekHGKFEbRp3ia7GeOZeqHM9gn8bPglP3IO+ZHzq8b74kn07VnL"
    "E+Rra/i8VHVrEdBxdvpEeV4s2gDRwDka8qpiEO6ThlhF30MoQz5N7+PqbW9xLlVlMxrySRJ7tMrnn85GiCBW8NatOukGlF5PH4s8"
    "KXdIMXttLRRTdN/3csAPzfqEycEr9HcXeZqIXzOqSedIn+aZ9UnDspOtBl4r35PW4y9u7cuFJa5tbQn12E9XIu8DsNcdt88hvaFJ"
    "ii/RPcIomrSp3bM8QafPmIPWVycSfDC3vSgdzzrWQ2BdwUGnG95nX27hlx1lktQbve2wFVcX77jQmkD97oYvH6PVLTrnLcKBnNFB"
    "91W4drs7n856Ofk+3jqe0WPbo6aiFF9cJSO0tRpBW4N/ATKGPyXh0gRKnrAsOqUGtkIKGCBhUBHCcG79xANEUtYMJ5BEVa8Ue1FK"
    "YeSRbthA6wXG5iQfjAFWHckT0hXAod3fqlbeiLNxjvbdQbMnq7+0SLUq0DztWWc9/3HQOQziv6jDulTVG7fuLqvcAZnT2P75xuT4"
    "8no9u5Qvr9ezfyJfXjRm4yjk5J/ZTc7Z7Hvxk3NyGT85wx/WT87Jj+InZ9j0k/P2B/ST89byk3Po9ZPzerbYT86h8ZNDG+P78pMD"
    "lf/YfnL2HD85D4kpN2VRigkjJTkpitZFUOQBy2W9oyWyHnZgkaxnpK1Z6TFvfChvjqm/erphw5+Rnfe1mk3a9etS3EFRnwUSFO81"
    "T/uEZUL8BHmeHz2AJI22ANKgYpBMjwbhJ/iAckUGzhGOpRslSoBjGSBU8A3yqUb93rE4ybP0kRiX7gzszSz57bntYPENOzF8yn/2"
    "+c89x4Hhvcs6MCxmuYjiH8d34f7lfRfu/JP5Ltxp81349AfzjPlmmeu8HVcu2PlhvCp+vfCkUpwc0UmF9fyDtZuDUCoa6Buv8Hez"
    "t/3BarAarN0MMA1kjEmfH+qHb6eTFA4dx2U569+4cXp62jvdgAPU0Y311dXVG1g5H3gSjIgAew5dZ797t/XyUWeAAW6BRMT9weO7"
    "vdtr63dvB2sbe3d7t1bv3v0MPntQw63gbu/m6md314O19d7dO6s34ffG2vod+nlz9S6Ar699dvsz+r26htlrG2sbd/H3nf+fuzdd"
    "b9tYFkX/76eQvbx9iBiCMZEEKTM8tuIkTjytOHGcaGsLMAlJiEmQBiHJjsTnOv/vk92q6gGNkaBkO1lZK5/Fnqurq2todFe5jgNp"
    "szswqXm/b1pPHcNzoMJO3+i6rtXbd4ye13NcSDuDvuXtQNp0PA/S1qA/6Mp0zxhAN/Z+lu57tjvYEe17RtdzbKzP+u8ZrtOzvady"
    "fIDTdAhes9/DtNm3YFo4PYBjx4T+e10AHFBh9m0XK5imZUMDDxpSA9PpW6C5ww/XwrTXRTyZhuX2+ziAPegO9iFtDwAAy3D6jm1j"
    "OfwA1BrdXm/gsXQf+wN8mF2s73gm5BuDPgKOabPr7tiG1Rv0qL4FDSHtWJ7df9o13IELS8UR8lSUW5bR6wGCsL3l9DHtmQOC1xn0"
    "aAFM03PVtG31rH0l7doOg4/a20bPdiw5Pl9ArG8O3K5cYMKH5ygEMLBoHpJAPMszLYV++laXSE3QlyC93wVl8+hr5OgcyJf8hQMT"
    "PNTIJL+QJvkfzCR/VpQ8P+H2aRA9z1XR85QJmyfsz7fsz8uc6Hn5nyB6vm0ven76h4men+pEz5MvJnqebhI9P+VFz09fRvT8+bcR"
    "Pc/rRI8L7K+P/M/Zdw3bc+knYw2uARzPdCTrcIHl9gaWZC0OsECr70nWA2mzm3EmIQoE5xKiQnA2IUoE51PSxBmVNHFO2Z5zVtk/"
    "47xPPZCcXbMvObMo55wb+xu4ICoFZ4c0SKCM80Patr2+lAyY7iGn5ZLDMQBPJDmYZIH+uzbCwyUPooM4K5dMiL5BP5NcgGk2HBNs"
    "rtEddGF6UvK5Bsh5NxONLmDZykSnlDRctEpJI0SvkCRCNGdpJrpFWoh20V6IftE/Vw2eyvH5+rmGBwuQra+L4ziZ6uHC+pDk5uSB"
    "E7QtWyEfd2CafYW8BOW1lDzPpOT5c5lJk0ftDtge/ZMO2B7ludnrvEv6H5kQ/U54ov9F/Pg+J1a//49xSf9Le9n66z9Mtv5aJ1t/"
    "/TIS7Lu/pUv6W+iS/p/hb/7HLfzNv/8nH6T/8HkO0t+3OUj/7csepL//Sw7SfysfpL/5ggfpb5SD9N8rD9IfbThI/z0TA48+50H6"
    "o7/+IP396BJfrj0Lq+4YHPyy6hR3xoOR9KegPkgGod+ypv5+1dmi33HLisNyPatczzrUuAus4gPCjN/piXDykQU4JNkstJCSU7rM"
    "PTW5CM8ce6fGJP2gevpOkDXt4wuLD2k+v+gXO5FOMLNtXxg4UQbWspeORQdfb1aNXrWq3pG3djYQ38C9QnLdN+i+r0fX9asF4wbl"
    "tq7a1q1s69K7+cWo9PHmfY0nnfdbudFZjZDaUgPvKME2rXcAmL2JlU5W8JXpJh8sk9Gq4INlNpooPljQycpK9cEyHZ0pPljO9ONR"
    "MH5fdNelp5knEtBQFnj8IF11LUfvpc8S/b144w5ig7vSoeogjH+gj1xRzjnXsXDONR+9L3nm0rOoiBh7FBSl5XiKwCn+W1J0y6Uv"
    "9bk2ZEOwUY41fallmeiUFJOfzWfVjf1xZP6uJA0JyFPFY9VvwiFUnHmr4m4AuMsopYbqMkr12FXhxOnTuhKp9N6UlLw3gZwcx8wH"
    "U0S+l+RyJ2PjIDocj5PMydLdu1yhYC5XUNy39a6U1HlXShTvSon09VPlyeHTkkUeiRw/WyCyzBPzzE/6yyozwDyn4xWDKp9RiGLc"
    "5swRSBH9qV5wFrUApiacRYWbuNRqtChwKeBbCpdCrrVQudTZaKZwqRlwraCTFhf1mDLznqKmiqeo4ypPUcfa+Fh6jJoAmwH77Hh8"
    "VmAzofD/J3clc/53LNRiGLneydNfyFyqZfcXIiyxCFI+yLPrerf1n0dXqdxxWzieY8KJETPZm7BnuK+LSBHhUYNTi733pZhFqR5o"
    "+vuyU381vxzrQZRWBopINZS7GWorYgjVDLjGPisjBKj9tQgS8EUWj3zfVwcjqPKD3uQEPdnLAjaASU/qfMFjdaJWqIkukHcG3sJ9"
    "P+6FG2Aq2QZTHcVnWXbBqKORxZPRb8yc1ZQoWJyFXSeeAB3GgdYbQe9FR+AB7JjGYAL8GC7inuVRbmTBBCaQksEEUGDwYAJnmK8G"
    "E1gxT/7IuJuiCSSZ7/9JsUVl9AClwazYoCJaQFIIDlCqLBzRA3s5u0EwgLi0A9IM95nzkWwHcBVaP4VlmlYs0/Foisv0DXMAwnlO"
    "YaWO2UpN+UqhB3tEyBH85TEAluWelwx5JwreQHGtd/+PGOzMy/3MK7Fa6krB71EdfuMbOPU/1z/qb0ed8woUfhydt/Lo/5Gh8Vx6"
    "9H+r4KbGpX/yCT34f1GFF98lYQiADp2SxciWc65wlfN8jCaQjMISXjG8SGMogYghNAG9A0MJhE1xBPbCgpP/TpiPKRDkCDUsRxQI"
    "S+EE0HlROFv/x/vwvyFZ1ARODHO6RT45kl7xC2Gr1AsQZHpgzMCRv4jvXEYT1MN9kAY5jQ01ThAL8di4Iw73wISQaulZdmyRKAHr"
    "ksoDmQW5NtX09/WxqiYY4+p4VDxGOQOwsrB2s1zAQQxzNxX8tXgAiC7/N463HF2Gs2Gs85OlYaKTt7xhpKOXh9f0O1jvTccGALIE"
    "+PiPmjhatStevZlrPJTb14q3xS55fbpjCtIrZW8y1CTrleJN7iXGkSQNDEakpJA90CeAszxRIf0BFeXqUmwGPH/Cu95gUmaHOKCX"
    "jw1+PVwjP6SFdiPVtMQjMubJLtTvoLM6WM47YmUj/c58MY2OI9yiEfQqEvod7jV6zChXx9B/U4z7Byrs1ZWIz8nuuuNYn9/rYDrm"
    "DgRLLv3OCoFCO4j2O8tpbk8cyACOWdhHtVW1983M0GGb+qzOuSZ9B5AeOnPxaWo3Y4zRNWpdafLwN/LLQlqij3yQ0Tulg+Da0KPS"
    "yaaWnWOcKY44Aez6sfCbd3kszK0aK1YcepacXdIU9+Snpw3zq/QAmc2JO8dkesD1R9kCi9O00on2DYyx6u8U2zokfp/zplycr/5J"
    "cbBECSrO47Vq39R/yeeialRu65t6Aypx8lGdW2oqvAElBDemhKqVzqw21XoXC1pSDTqbeYGqRytht7h364hTR1Dtzvov2iy3zCr0"
    "bksd0bgCXxt3VxW+0ry/6jhDWhYQ/VjTk0zrHJX39WTUmY2UKtpBnI09YdbLTKosenLg36FoqIdqI9QOKfZrmEXSpoGX06urEZ4W"
    "4c+clkE5FCuKqRtc25COZouQosxTvuFkX9HJPEuL81qMgrFBbgr01agiQBzYcnF4wRRZNOwWsyklxCotFPQvqiNApww5AQttASbA"
    "TYc58Nk4RhKBThr6h40D7gXGHZogaF77ATrhnLwbXbIehiv9dq6v28MJBsjItmApQnYsOg/GJampT8/IbuOdC+sJLKaFcpGgFn4Z"
    "YBw6VyznYIN0jng/xeFZroRigspQmTBKJFHG1h6Y/B3sGw3DwtxigR+9UKEwelyetL55ZHFfRzCFy1Ig7lRYmGm2iVKxicRmySmw"
    "/550/CUFXEZU8bjduuinJn53KkyR97kg2GKksbyMQp1gz0o32LvY6vT9qRRUWs5iY/dkIkP3Im50CfBiGO2Q1dAuJUw8hLYuSipC"
    "aW8PD++iAp5i0G2sQKiM8CtI7QeS0lAKVkWEbl30VRmpO80dPux1FiPRaT7cfeEeEc+tCQCJRfkAkAsZAJLwEJdXBsRL0VQWZvvr"
    "ZYdJObzxVXFTBb1Ip6MQ72nhzbbM+zYKh0/QaZLr9L3wsJLq6i2NmGJ5C6MYzzHX9BVKVo4p599lFy1sr+9KI63k1zqK31V5RN7C"
    "qVTR3xMbstlnWhJMo7NV0Uuv4uFjBWw47JiqPzLm53I3PEcUVvtshsmUnbspHl8YaDum4a5yTmF4D4pHFF4z66Xgt4T8fi2DSZR+"
    "zHnlrJyGbXSViaxrPFf5BL+P7qbu4FUhsZBswf69VH2bhPNWTy/C+T/o6UWYf3iWzpWRgzndI4vYn4T9iefqowtM/e3fMibz1u8t"
    "FvN/1nsLPp/yewta1C/yljGYb3gRUKjPQf7cL0FW89L18cn8y10fn8yzc+XZvOr6eDhvvj4+U6h6/hmvj0Pnf/X18bP56M5SsG4u"
    "fX39kruhK5o6Kg8Nx8znCVOIf6IaPH4GnmvzaDN4dvWYJGC5jH7j1010oBe9BSHd4bclp7sCkltmvjJ9gxMhHEY+c23il6sIBWDk"
    "C8/RvjZkIHDlqwYcVloPESkuFbqjcLjHe8dPbymYYIsz4aomcyGT4SSPUCOYsnx5QweV9lU4XVyIKS7iZ5jzDeQQalmQGtJma3tl"
    "EF23Y3V5a4KE4nfaJ/E7ehNE9vZDMJhWywD6BlYA/zHnNT6dBXN3gX7BNw3s69sM06hUFNNcSbqNThbZpeuiS50O8C9GjtJ/oL6I"
    "HwpV6nHM41nl85SpimBkuY8QPvQCag7W8rOYgcIfIX7WBF0Zds7+aTSbdiQhhbMRGm0M8S2QJjwzVtN4I3XzQnX5OxjpqXrVpWoZ"
    "ygnlEZK17ODiK1RRHyAWZDB7jPszGAwh2DC5+cXE6UBas+tAFNaN3edI6NWuZnAd/pa8gkQ3kCrW93gCbXyVIHw8CqtiIGod3T8O"
    "Ziuse+sp9ICBuH/FvyKs6rMgPTXmwYfO/gRvgT3Cf0FUcFSzd/aj6J6//ODrIpce4vPMNQup+ie1XuDdh+AkfLMbgCg9Tu9NFxPS"
    "Moy3i+lH7qj158Vyl0C4b+sr3uA3aJAulpX10UHT7lPWQAIGlUerPFQ44GjB8qoQOLsuAkHBwqrUJedqI7yWwX521C90QMu30k+8"
    "cECJrmkh4y1s6RL35cDdvUv3JAR8apGm15BWkYyL8BbK20O/1tlWqLFAoF/kHtDzGE0EmcLYU8CcKhq9nKBSI94V0HMBusDHJdQ6"
    "00nBNJvOFU/AyAnqnAHnyzIfbMKFWkXUqRk1KVmFWQmPROOXw/eUQx/56OAXgVCri2BGvs6w+ihI1OLM+bRPlyEesWAWfnUwjqro"
    "H76O74TL7dQIHJXtELeb3AfTbLbyIBzFqAkOD3zuf7jee3C0eikn/Dgm3/bUweq5nI/Mxs8VIHujP8MXb1dhApIluxjwDlBazOXa"
    "X8Ezc175k9rdT7mOO9pQEUjFsjVfRvZ84/J4drY6BawvcIFPg3g6y9+cYj3ROeETArSjaJVPcqB36NCspJXlAnZWc6ywOEJY3b1u"
    "dYUumkeMkN6sG4b6V+TvVYG2iImqM1Q+4WLvdZ3XnpcKxFUugaovlOcodVQYhURPmcW2BU+nS4Cof/CLUh1SKDKq3Qdz/11NMMY7"
    "SXi8Mjiz0DON6TVzxM86+BWFMF5+i0cgTUNtF3UPkuawczqhIjy13fgrw9MVWZ/opranVhm9xS7Gu9ZX0TBCQLN99CUBvccBFZnU"
    "dDfWAw56FNOdtxrQg2Gw1surXrMfuL2i1hzF4cVOgWTK92/CSnLkpJXv0FiwHx0FW8hKpcmyAdI9EXE03608SwdQ4rohquCRdw/L"
    "9N+Eper9sqeo83lCiEfPJviU6kCV0qPbIEduH/I8LrwgE5Sr24e+Rh/NmG6SG2e7NRFsTCxHvi+5HHFmNG7AglyBfE/KCoACD/OO"
    "0UtB5aAS5yqETfsJvzUoqMSH2+9AxtN3XoyBQIcrUn3fHtE8VCtJWCPzct/Rxp04r/aDMRBpTKGOFb37T8zGX7t/olZOijtW0oay"
    "A2Yh7Jfbk5LOOsCfvAeyFaiLtcCTsrs2IgvpXY8VrOFZkzQ2MA6ryk+Am4j09zRPHf2UsEgfrMJKpnmFScavYpVf6bPRwa9k+TzF"
    "fw/xQR9+JprCH+uwCdNcCy9pMaMEfbZwOiprM6M0B9jXIxBBoFytgKxSOk0bBbtTcdRT1f2kXfeEh69HC6X3CfYe7Z4xjb6Cw29c"
    "pkxH5RcYxOiwXmYuoHhJxUhGnXSswnZ1ZWr3OnEpDyyrXAR1/E4wAxpa1cdaZsvDAivkVbQNTXgoiVIQjw3N8rXXiur+MImCp+T0"
    "eVNgaH6LwJgt8JOVgYdJ4401aAGixdlKuo/OluBzD40jyWGRM72sGGg16VwqUVPyWMuCvGh8hSk2DGhrBUfOw4ulXvSwOXy2hGHl"
    "3Vew1tiR3tkc7zLNRwfcoASLY4mpzLU02v889AoUznNVT2VVJRQI5J80dKFEPJhX3PkfpZE8iJYn9oVgIbChhr5ifebihoiDw9vD"
    "wCA8VwQSCUobLKpiFuNHcafDxxb2Igz/Lvw4NHUCIiNdsF/RCbmspwKm1NLyXrsDo4L4s1A3gVx9kaULfZQ7aSzTUGCUtOy7dysy"
    "+Xf+QPnOv+aoKkB8eVtIV/xAvtzl/gduD/1YYNAHfeOAUPWkE0adwJBsh+05oMCrq5LDcQ2xmT8IZmdNOThYVY05+bN6GkV8ASrF"
    "hTxYHB5qw0cdn30qeFqgES4O86shMvGEmFs5KQirWmSyOgyH7HcV6urIThkP4C0CyGJ3q9DxUxA8IaNTc3macru4z24r5KFkA55P"
    "Ifknhp2eZZiU/dbF0UHksVN7ARxTu/LgyXMYCWDTsX5hNZXG2XLSap7O2d/5XNOrN2dJVDdsTottzoy5N21OpVZpc1aIh5ab066n"
    "p4JlyQirkNm4OXMQ32xzYlf5zZn5ZN68O7F19e48qdidVHA819bTuXDPeTQnG+p8XhXUvilUGrO8MpdO/NHhYrnay0VRk4HT5Cek"
    "lMd2029nUSFvD2ND/OYR1D6q56Z1Z6Y3jZ8mxmwIjxasCn2x7+dZX/6jX37++cVzH6vSd6jN0TDO5xuPLm94bKn72QkoKg3ZsRIL"
    "zlY8q5I6jhrCTXzRowuhDzOtlB0klU5lmir/GH6cFj9irS4icukIytoUkhNYUv9hkiwuaAf48nuhzIJO8HPd2yQM3u1l1VGa5Wtj"
    "Trny94t5KOtholzlcTyVNeB3ucLL4IS+xslaIqO66i/LXMVfllVDpmHiD+k3kOkymKo5rzCCsgISlLAu2LcYFTV13znxKwYyN1jf"
    "4jcWsMTHyqrRoodTqog3a0qoqjlSVHHeBAXqP9eGQi5HDRAcyqbxv8WH3dgvP4GoHK+mezZ8U+9Pg2t3rhBRxXkvaTxP4tdReNEp"
    "j9bUJ9Fb2x4z7NTjgJFfucfKXa8Q3k1enOazx+GQ2e2PZyHmvYpAO4tPpO0+fknHUfzkSfB3HyMVKAUTIaXZhzsmkFDVGpe2DFBg"
    "/QmXrw1R7LK5cvL+xHMVFvPnnq/YnO3nKwimzl7PYTETMiiS+GktRXoldwt8diQ/UVVhI3AibxpAgl0/AOgwFf2XSLZWJirxPTtZ"
    "rFDZRbbFC74wn0/kjZT8jtNEZFaWUSaYvVB5PBPK1ukCq8uD31RcZruky9eoboO2APJeHk+wAyi22hVIfL1S0bYai+MkPTfLaFpu"
    "6t+5zLe8E03XR4DtI17AjqVQJwLtFd11wgxWW/RDYZDLnZG+UzERNo9gRQoRAz+wrI9KUjl/EBkvgySY0x0r3rCOzgL0oCbUvPFl"
    "3pKRKiSL7SqUWKliSjiqviHzVtE0M2rYiLRk4xwZyhq7VmaZCnuP6W2oSCvtedmEo1+UKSui31Y3+W3RZYGb3M7PTZZLjV4ZUiiY"
    "XGpTQtH/eDZPrvGBLFuGCuxMmJdXScDKMKgDNx3hVbTAPVFz/JYdiL1tfSAWGlzbH1fZ8jq3ghmM/DyCG72PO+phmcaPe6ESx2BG"
    "MIFCxELfRlOVfq3BruP2NxmVCJCWHY61OJar6BNMf9pjYNUKs+Vh+VtXTRhgMNqOhs4ajcwDn8b3hfyBH3wI/1DapeuP0gx9y8zQ"
    "D6rN95LC19dZfsXSVvdllrxR1Y0ZXtbmWgkbeysLTaGxV/PrhWOuOu3ZLkTzB4nvVwzf+5VmP2GidZh0Xptb+ZSSjCE7HhC7kNn2"
    "F6V1blzmm1r5m034b568bmO/66dhAOgjHYj/Zq45lIx9Wjglg7l/UTIeEiKVbH4+qXTFc5S+eI7SSgoeDqig+/15OwK+8cWov0bD"
    "qNEMxOkgIOTtxxspLBt0jG3UiuuIfgmhPNOUwp5vNeWIlGaryPUMBVWSXbSvF983EciqHP15XulMak8ewopZ8vPj51xgrvWDdoL1"
    "BqIUBGd+VOAQB7c6ncVIgiW9QizAePjzI7rmFyrZdjL3kwtUJj1/XeidVQW4KwJ3fMuUKMgf//Zcjf87rEeuCarShZQUPzNJ8Vhy"
    "7FfLKI7DpCFo4DfqQ7s/2NO6h+zPO/bnRe6h3Yv/hId279o/tHv2D3to96zuod3DL/bQ7o9ND+2e5es/+zIP7Z7P/y5BA2HPVQcN"
    "xJByfQwq6u53DQ/DxWFUt8GAgtjZA4w/6xh9y+th0DzbxCBwjmF5jr1vQzaFQbWNnouxAw3PpWB08KPvUBhXs9ensKYD23P3TaPb"
    "63YpbunAc8zuDgap67q2u+MZ3qBrY+RY07UcD+PY9bsDb7C/Czme3WNBWnu223WwTt+x7O5O13D7PbOPb68HXcvGIHuu5fZhmIHV"
    "tyyMZ+t0HQyrisHruvaODeUUQ9CFnjDqbK9v9jGWoOPY9gCD9zmm7WKwP6cPP7BjywEU4Ehet0/g9ux+dx9AMS2rv0PQwQ+ADgDu"
    "mTADzOraZtfp4qR6FgUFtLuWReFvBz0HZ92FSfcpSN+gT0ECAXqbh5ntIt4w9mJ3H9IDqwvwmpY7oNiIg36PRbN1rIGSdqx+39vP"
    "0m7fxii5onkPlsGWvcOqOVi337UtTHhdk8VdBFBtw7O9PkHSAxxiuuv1XKzedXuIOs/zaIFdwNAOBgt0PILEGTiOSGN1B1ZWLbdd"
    "01WaW71BV+3dHHh9dXTTcXsZcCYGHRwwyAdImkRrlg205UGe7WKgRrsHlEMBEG0b01bP6/dgqXA5KJBjv2d1iaZND9Mu0KrLAkX2"
    "sW/btrpI010gAZz5AIgKiaRv9zwMkGjZFJjRcHqOS8RnwYLvUwRIk2Iomx70g1NxYE09A+NLIu0BxfS7FOp5YPf2cfFskwI6drsU"
    "qNIyae9gZEoLac8e9FmgTcsznX0kvYFLgRn7sCFgHMRZlwVi9GAYq+9atAX7VrcP2IHqPWruug7Fhez1cRo0D4q32bUwriXkw17f"
    "h3pOz7MwcjDUp/iOHtKWZ8AkPJ62Aa374hcA4HZtFpR64GJw6N6gN7BZJEjHowiWQFr7yCQsByNWwvQY04AVwm0MiOtR5Ej44Yo0"
    "1u/2LVst71u07WV7zx5Yav8DB4hJju9moLkIL3EVYDgWG5qFj+6xaM4Dl1HlwB309ym72+PVaN92CRfuTsYbW4a1fCzVoudMLXpZ"
    "NqDfBtOTstcMyq3ym8H8XO0ez8IPtU4v0EkGdWCwAoMVqG4yQFU6Ia0IFPedSYgfarLCP0DdiY4/irc/5QrLYEr+L5WReFbOFUfB"
    "bwevmETzIPlY475jgoisqk4Fas1jAG4X71irtTHTwMxSzQsmSYt1WbZaex7Fu0wCK3Uhk10QVmuelro8zfWWuQ2h0t3pIlVWtDQG"
    "FJdArwSmqmIZlqpaBTrpqr5R5Jqa1dBPomSSc1hSbNA0QLGzVQi0NYV1VfqrJhdZsy3BZA1yJFOC4GwyCVerzeOzeq1H59Ubx47i"
    "48XGgbFS21GpbuOQFwHomZuGxEpth6S6jUNO8WNXsnFQVq3tsLx248D0/SJYpRuHFhXbDi7rN1PWXBm4kkut5tWMqnK3Q+WW3Adq"
    "NjOg2ckmyGYnW0AGlVtCBjWbIfsw2wTZh9kWkEHllpBBzSJkbW6x0aGyroYoVG6xMdm93JUXvtlpt8pGbw9/kQGS7t5l1r7M4JYm"
    "WOKWflsRHreHT1ZKq1sxP5AREeGyyqs5XptDVJFDkXkww2O8jAzU0hneqVFKP8zU0g/FYmQ1VCE8x/Pej1gJ85QqnAcWa/FspSLy"
    "kGItzFOqsP1erMRy1SEF0y8NKgqUymIbF+uKfJ9/dfhWnmHhx4VHTE+73pcFdglCDMYr87qFOkj39eXi0P7lhkN7grbxxD47f3vS"
    "ztfXk3+Sr68n+fOfp2UPSD99QQ9IPykekP6s9ID0ZIMHpD+z48Ynn9MD0pO/3gPSI2Vb5rbkt/PSV6jsk1PD139YfPjvknHmYfZ1"
    "R5ySC/acfYJSOTQeNn9UWo14K+a1Is+huc8awQfyKXH1BxhA9kujZ/Kv1Tc82cb9vvk4UTwNuN6Lm+oD/7Ve/hjxZ+cbGb5Rt/Az"
    "BF0cfz3X1o+kAfw9M4B/mY8yG5d5a2hr5IKpvUJ9jPtpzArOVmBysAstqtfGm5u5wqXPcIddp69yVym8VVWrjTTDehu2pJbm6zd5"
    "uBzuWMsPO6sFfvKoasoM/9KIecudt2F5xsf/o1Vlf6ixuq0knBcKjoN5NKP1o21YLA0DoBcU1mkKHa8q6pFnS4bZnMfLDBMqhFlt"
    "YwrMFn/8H03PNSQEbNmGG7HXabo4S4lyrzfsh93VaTAFNrqpYfPJD2tYe/STg3HIUM5UhKzOSbDMdQbpCtWdOWER9wqUjSy2Kucb"
    "1Q138RnLboLKt9JUEPfGNjBu0knSmVZuvFvTehgv0k7W1zl/3KwV+i9Uy4bUGsZsBPjtAn7Py43spkaLePax5ryILQrWMrBW2dDh"
    "e3eXM1LQ/JI0d1BTqIBOhtViWn9zE3RZFm3NHAk0HTXlzLDGuTRgJsujmw3K0Of40DuakefcIuPmWNw4teEwOE5zpxdSStz+nw8P"
    "zdt7n2K4xqMChpi6s4IqRg51a3i5UvKhFrcATR4T1wKuotttCRtatKWHys6b6LKC9rYYrvEEhfVWd4RStWBQt2bBlJIPTdBsuWBV"
    "wFV0u+2CQYv2GLz5gm0xnODxKmZAqxT+ylGDAzl4No/rwC3wlvK3BA4S1qv6pFDq8Xh2Fk3L2MwclVe3+ETCoVIkShGuDU9R5206"
    "OM2rmVT9Jnoq76BGW61XpVm7unPYyqmV/LZvmBurf5PJiR62nh1v2Dy9Y7wqv3vOvJrkJK/QIyv7pmYGXS9itSp0w1xDpQEnpZpS"
    "Opkq2BDlQUtoEPooc4tSNzQrrUNG1SfT4skwV4vZUXnT57OmigRpq9qlbZwE0aqgIlUuFKtXWJxyb5s0LrVHVrfaJCiL1Dbf5rjk"
    "3PBxrnGXKI1bb5DNH/cKc7gmf8vGuTaHK3VxjUm24HL1U23L77Lhrs/xyn1cY7ZtuJ4y3Tr+V7BvK4dq4kc127Ky8YZN2uIjM++8"
    "8StzM+pF0/YY3/CNOgf7dTcQH+P62yffwdaTa7V1qqfYeuPwoW6wbQo9bD3LdluGT/MaG4YPc53tUm66YbNsuhXB9dr6axGNqGbt"
    "WiO48UZFBu81dwf1fu2tobbebkJtNkXVtNruCBrk+tsh13y7mbXaCDS17XcBDXCNLVBst4H+N13RYZ023NFpxC1r1xqpjdd7Mniv"
    "Sf/U+7XpX2293YTa0H/VtNrSPw1yffrPNd9uZq3on6a2Pf3TANeg/2K7DfSPFw82oxhrXQe3rF1rpFL1ZmxilWvSP/V+bfpXW283"
    "oTb0XzWttvRPg1yf/nPNt5tZK/qnqW1P/zTANei/2G4D/W++L8m6bbww2Yhf0bI1ajfctlThvuZO4CNcey/k2287sTb7oXp6bXcE"
    "H+j6e6LQwbYzbLUv+BS33xl8kGvsjXLLDbujzaVe1vWGW72N2M7atkb0xkvBefivuU/kKNfeKcUetp9gm91SN822+0UOdv0dU+pi"
    "+5m22jVyqtvvGznQNXZOVdsNe4cDMq1Bf+UNEPUSTG580dnGq0YtmjYjWFS/5pYpjbZ56/wtp9t265SGa7GF/hYT3vDpYSOg1/mQ"
    "UNH42sDelD63+djwn4SHrQl3qy8Rf0dMlI/7N4O69fF9qek1wbwx2bY+4v/PmP/25Nr+/P9vhoHiUftGGLc8Pc+3uw50NyXOlifs"
    "f+s5b02QbY/f/zazLh55b4Ruy1PsfLvrQHdTOmx50v23nvPWdNj2GPxvM+vi0fNG6LY8Tc63uw50N6XDlifOf+s5b02HbY+j/zaz"
    "Lh8Bb4Rv6zPdYsvrwXhTemx97vsfMPet6bL9ofDfavZVR7AbobzGiWq57XUhvSmVbnHq+h+Dg62pdZsj2b8dFpazINpOxaQW1zr0"
    "oobXAvDGJ5w09A3PN/8G897+qJPGvulB5+ecOTrAvf65e2WVMkQ4SMtDV3LIez1yy43Snti+zBzakk5umC0I5/PMov2t+09MLG0P"
    "OWuAvAkFXee4+y+c2laEda0T7C8wucZ76J+atFodSlYCeCOy2vo4+i+a1HYEtf0Z8+eeVsM97U9MSS3OFMug3YSGtjw1/uJz2Yp0"
    "tj0N/qyzabjc/ImJpsUBYBm0mxDNlke8X3wuWxHNtke3n3U2DTeCPzHRtDitK4N2E6LZ8jz2i89lK6LZ9pz1s86m8RrtJyabVgdp"
    "VeDdhHS2Pjr9S2a0FQFtfyD6mee04bbpJyajlqdb1SDehJSucb75l81rK4K6zpnlZ59Z6SzyM54FtTyZ+jTnkMqQn+lY6NNMZ7sz"
    "om2PFj/1hGZR/O6zUwsO0gKObQjjEwPX5tZ5PYj1nnxwHXan4WTBnOoNd9BHRoIHu1sM0khRnxgR1ZfS/cwd6K/t/Pj++k/y4/tr"
    "3o/vd2U/vj9+QT++Pyp+fN9X+vH9dYMf3/eZH99fP6cf31//ej++P1TEQuExkpmP61/mLTyxC//r5IydPHKrntiZc6CcK3Ygkbr/"
    "yEt7wckWOgk/DVYYvo5crhMboV/k8ke/XXI1dnvYYe63Xi4oDnS6oIBrahbzB+lrd+/yDpVuZosA3b7dHkIR+6kWAiOgEviLfZ5j"
    "EMeYkI1Z/lqXs969cxlL38JrX48VR8N+wSkRlrJfuTLmNogK2U+1FPknFuHfAihUpNYVX8ywvvhdaCOrqO1Wc4I758deLZ+dqOXM"
    "Vb1aTmIWq9APtYR8qvk6re23+Fs7XOsc37jWQ7+4IEQSvk4OQmtDApRoj7dC4lLXhsjrzmUqiGKNoBAlEBz4Q4UA0xRp+Le8S3q+"
    "Xco+6VkPDW7maRobygGu6ir+LDxOfVaJhZxtDpfLuqT90jQmVdiyv1eNLvUV9/9ydRui9arrX9lf+wDBPPh7mxjBpFfUF7cJGsD2"
    "bkMnfP821GCBWmuL5eOkBkCbIxfofLM3VWFae/0QtGtrynPhEX7YFB6BudBrFx/hTTu96s0/Sa96k9erfi/rVf/+gnrVvxW96k6l"
    "XvVmg151J9Or3nxOverN30CvkiKiIB5+m9dF6cYt8S3bW4XtxCLbArs7CdOXP79YIjJXFeTYIQlMwQPGMtD1UPwC2PQsGrQMRE7F"
    "IgXiDcZTAjaIWuWYDSyyAsVJls2vrqpyESifF3HuvhYc46GIf103AgnRcfbzHgsBQXJn7O/497Lk0Pe1oQqADK691rn2WDcKClEB"
    "PAsWgTmb44qvlKjihSDj6lrJiA4oimqCi+/wHhFbXHCNGZOVGnnNmmUSsSF0uRJ/nAcPL65AKfi4GFaEHhcD3s6PL8uFkOTlUu0l"
    "7DPKLs/6CQ82T1JFG9+6JeKpswZZGZBMffQQYI0N/12uK6N66L40MHgc+MzGyAhOJIjEoA2nYN6CpyBfKLO8H6bP6r7U36kgU+GF"
    "zs+yhdqf6eiUn6npPLRJpabOjACqweyAYmVhCpB1wuEm26VYkSpARWFF+XpHbo+cIVXMzWypDHFI7bhkiNHGZRPLw/vLJerisVDP"
    "RLatuv4EKy8YI1mwwIuVkOrDx3OdxXp6NAfImFfrc7KYo+USJOrZHBqHp0r8GBi1MppMfJqPJoOyZDH6N4gqNYS7pq8oj8Xe0fTJ"
    "KMWoMTRYJo4x0D3pveP6uPEWs+6HjztqaBpNYSVBxthALXgUdzoY2uZJJ4w6OICGwW0oAr3eKsQNdIddaboUcg875Wg27ePehGIL"
    "5ibJ85jdVwDwgEGo2BkAKMuj+mj8USCeQh2taXSsMu4Ug/5sNaye66wWCIpua/U0bcgXYiFGslpPUF8BMYG43DCGfuBTj/6hhgGF"
    "hiqGc6gtjFxEY9SAv6gt4iSS8Af/Q3bqYZHKiOGUBhdzCk8BdY86vq/fMnFWiHbSMSqBsHNUzc4AtAxtLK1fFiBgjAn6xphMjBnq"
    "Vh/2vDK0HnIlhi/jim1IR2faOi9VtmdmmWuZPcqzhQWun8Vke02hQPzUl+mQw8tD0uEMCB0erDAN5+t8pUGp513BT9ED/FymSAQq"
    "3hB1R0NnrdKJLjkaBq86mBweausfRPCp+JQU+wQZ3yqZAA+MTkc/J53LoyOmKj9dnCx8mFp6tlR1WlDqR1+/67w41mB/nCzkOkXz"
    "E87ETB36G2ZV9ACtf19njsd92/N17i2cfjOUwjrvYmVf4iJRlwcPeoLTER/+chamaJIYR0fnkwlodaurq3DvGEwIKDgI9eQQLLZU"
    "A4I+HCWC/4L+uDgdBaed6BSQ4R8drSZglT2ZCjSd7wbHE8fr2YEPiNJXp8Jm+DmahySOMrNhf6nYwpNTxQQ9xsTV1ZT9OWN/Zqcd"
    "xXDE1GXJ9nkSw9KD4gj8GMOn7aSLndUyCYMphu/aJeMYXemIs13jv57ELGQO1nwLBbyGTvWDJAk+7jCLa8UsqdMAbKdg56Bgbh92"
    "tB1m0aBJJYE8O5XGYUj/Cjs4s7WEIbdkVbmdeLkGC5FZYdwM1IzVLJqEHQ+jgMvVQD2FGclF0/zu3Q6urZJj4EIAz8A2zwI6Osaf"
    "r0KwrB7iTI3jZIEm7JDyHyYnYFmDWgAV7/9vZzz8Jbp6osUp/PKurN6VY2vwE/bufAlqHuvhzn3Q1lZpJ9bGfD5Cj89wQouq4IJh"
    "8oF/hjMo4ZWFygPCPAC7VuT6PFvgLgd9NtKxGImVRyv6C3kqzpX6HORLtIXZqOnXIY/IB1pgBw9jeYq2CVsqU09GrGNYvfhBuhff"
    "u6clB/EhGPvxoVipJBtmftoYXO/8hBg13+eWm+1z/H0ehRePFh+GvrljYuR4zGMB4zE+na9/mM/AjPZP03Q5vH//4uLCuHCMRXJy"
    "3zZN8z52zhh91AFuBnsuPTAPr65GB0+BkQbpKTCf6dB/5hmmZXm9nb5hmgPHeWrZht3fsY1+17J6+5ByXAuSPa+LQeshOfAwaXZt"
    "F5Ou0+9Cumv1ehbWdvu9AaRduw/1MD3wbEg7ju2w5ACLbadrD7A6dNqDtOV4MCiWew52b7rWgJJuH0YxBl1r4FLvlgVAGF7PGlB1"
    "pwt/jL5nMmBsz8PqfYDcweq2hUAYPdcxbSyHYSDZ9bwBAWO6HvbW7dpdAAaHYWmrZ3d3LBoGu4cpuJjs91xMdk1AGFbv9fosbcEU"
    "Id3t25i0HbOHSZgKAtOFzrpY3Rm4BIxpm9SdY3Ux2fUQRsuwXQ+L+/Zg0H/aMwYDs9ff6RoDz7Pcp7AcDsLEivcBb4Nu12G9wSiI"
    "GFgIHM2xPUSobfctmqvTg1WEqTqIeEwP3B7DIALXs2AdWLe4ukYflq+/D9UGvR5273kmTgYmZdKydL1elzBEi267Xc/F2paLa+w6"
    "jukQfp0e0YhFq4jL4ViCop7ClHqICUlvvBxR0Ot3sbs+wx/rjDDr9Xrid7/vWfv8N/RE+dgAVhcmL4dj1IBz8dxenxGTjZgyHdOl"
    "1acZ2IzOuvuIQsfxREF30Gckwxox7LMu5eJ42FfXfioXTwwJa+uxMbA1wt/jHSP83YHLhiSKMwe8BKnT7clGtAtlj5Bpdp1skrhR"
    "LCdDQZZm6MnSDHWiPccq65wh/GmBAfwumMzkLMEj7X28KiCUDJBHIOlBe1+vToVeNGd60elp6UssaAGrAIOrsvN0GbOT51cF7TxJ"
    "oqkSQQ5SuyjdZ0Ea7oL8Xw13rOOkMXIh73xz6EIlrEuhTSkSnmjC5sG8BRYvePA+RCDQ3YskWC5z91swloyI+mJuaF6Fm3wk08ao"
    "pLk4YWJ2vGsRE0ydoAzVWKxbGbNRwFqMFoYxsVanCX6KapjgbLEKG8K2bjHLjbFXqyCilQiSkyguBDYMztLFTcO2VtAUzdcQ3qyb"
    "gslXtsgHlt9A87mWtRtg4/WilgFUxahbRVDdolE5DuoWjQuBULcZdhlMwH7cMQ1ntV3AU15WCkgrd6NZ9j6aDzW8bXjiuu3VHMcv"
    "Ty4U5K0YoqqWkCtr11NxqXozQ9joBnXTBivHGavl4m364NHImuOMbeqkLuqYZKPNMUtE9w1BSyqcxOZbbX6Wnqu/0Y1srnad49jc"
    "/K674LUg1iB7O9Br1/0mU9p04bkegrqLz9UAKMkK57x1iFPcYdTE0NvYsoqcNoK4ikCNC1sAyCpu6n1zVCzRaXNYrIZJb+FTsdik"
    "NRWKBpsITkz3E24jCetNd9Kmjm46t7b7qRKO9ltKNN92V4l219pYpcbt9lYZ1jbbSxJbqx22IZSQ6LQhllDDvNt65svVb02RVHsT"
    "2dH8PuF+YiDedDM19nKjKbXdRmUI2u8harvtBqJG19o9+Zbttk4BxDb7hpFTq00T4reJFkimettvG96s/b5hDVpTH6u+iczYJD/h"
    "1uFQ3nTvNHdzs1m13T0VMLTfPqzxtvuHtbrWBio0bbeDilC22UKcsNqpdi1iB0uRtiF4cJPo3ca/e7lRe/VINtmoCMmJf0o1L4P4"
    "xorexq5uPsPWyl41LFuoe7KDrRU+2fJ6Kl+5eUulrwLiVmpfRoCt9l+LKEnqMXFDmKQGLGzjyLHUpjXFyhabCFPO+RPuvAzcm268"
    "jT3deHptt101JO13nWy/7aaTDa+158qt2225CnDb7LiM7FptuIJ7x5rTWnrzjWWl41dqcFFxBps1uch9Rtj8KacahLZHxa0PiVsc"
    "D6/mzZ/HGj91rebFr12bBthiLaDz0nJs6n4bPM/bo3q+Bbbn2yH8mt8T5tt+Uphv/VVh00RmJzegnNnJZsrJD7AF5UDnLSgn3/0W"
    "lAPdt6Wciqq1lFOouxHh16OcdsA3N9hAORsncp1Ydw1fqIpCJ/dlqmIDFiVM67GbPk6qukXTB0Q++vY7R8q6ylsGDUhu1En0FvC1"
    "VWRKeKmwbfGz627JI0cQR3Pu4WO5yxJhvg19Lt4JgxVNDOg8uQiS6WrThYKKTRQG5+GWEFAbgMDqchCieFsI/u+78ONxEkCPtTNU"
    "dnGymCtJ5at57ht33RUeU73Cs86uHSzq+rQ292mV+2wzM4a5djO7HhTNMytgi11MuS4S1//lt3B2UfQxIG5jKQ4udjJy9O+l8iWc"
    "jr4titsXfVtUPezSbxf3bKEmy8zXm2OdvKsGtXx2opYzVw3rQ3zXRDznV3blaujX3sbyRdWKOtwtg58XuT571O7n5TzieSF8J+T6"
    "UngRr/RkUlWF+sZL+ienqjeGZ+LKXNkdQ/Mbfh+/nfprGpJeQTf5CjgWxezVb2u3DuKhZjavzdUYjl6yOVBtukmYH/Lmz/7Fo/3T"
    "0+ZH+xzBLV/tH522erV/dPoPerV/lL8pf35aerX/8fTLvdr/eJrxrrenVa/2j06bX+2/zR5m0NQ+16t96PyvfrX/QfKSEh85OS29"
    "2w9hoNUQ3z7BNvXxee0xivopvu6M5iFwcr5VgzSo2Ez8LAwXbq3PQcNK8+/sEaBwhFtqjz/ZPQbCXYXpz6xz9dlkaPDeRgiXcQdB"
    "62QAaWtddqEp/gQI8twOYS+Cs77Ya2zWHZ9nmHcRQLkbn/HfwXUJz89ocwEBG7MFLH5IT/THG2sw40PyxYaH4LDb4L9L6Sml9t20"
    "zsRnqQKXquLdsJDcuVTdo+S6t7+5d8PycddwdaqyylftWOWrfxKrfJVnlfuc0zBOwlkjaJ8rqIUcguechOmLi1gwSzbOSjCVpjrY"
    "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"
    "kzzNYgueUwf6J2ujPgmJOp72OJJKsc5zeK7x+ZwEpywaBU+ACKX3G1mm2AknEsF8UfmhF5AC5N69ZKVRgYb4usMat0LBhiRJp0Zz"
    "EUhPUQcDLDbnSlOkhKFNCXk78TNczO2NGDg2Yvb/N+LWG3Gmb4TBbM7HQuS8clLS6zAJzMzjkmw7WWR7afUUXcl8uZxq37tqaETb"
    "FaKmmSGeZ4V/xga+IQU678MrngRecurKdR6sZAL5C5xQkM5xLm9DJqKgRpEFrDYOJKnb5FebqX/ZIH1jzt2m/VCDg38V4/XYrQzC"
    "r89RqbKcIme1XCRFrVn4Lphi0EiMRZKJrT1SnEpXSFEiNOtMmyvV6Ye8hFac5fJqnKlseXbkUNupMo3buqvlqWMvyD+E68ycKogM"
    "2EXBNDwPQPKS0LP1aekaWuZP1EpnqM/qpHPDfPH//j//R3sdrZGtqNBFVOMy8iFFJXR7U1nKb/DrvYyLk0y/XU02i4XFcIZAJvzv"
    "hJY/QMRmpNloox7QjYlTP3kzzEZn+MxFz/V8cDVIfiM3XJiE3+vhluv20+ZzyQ2G0ehMY/DTI8lPW47dy+Slx1m8dGz2wix3LO1U"
    "c5yjndJDm2Vt8I4ucWsNLHlbNx66lY7qT8cijmcpNdWrsa6mem024lZINyipjGhtWct9nF4uD/jlWi8fWGPp21xpta24+A9tB493"
    "6ayma2qs3rhWn3FheJ5zYegEwCSC94lUCwo1r2NLfh7Nkgz8fJmFn+/G1v1kpNRbmv40F0O5WVYlzN6yXWPLVAOXDlWaed1Oj2ov"
    "hHVioikzhkBTg6XufGgtQjc7idu6GuznteDATM0yYbHnhAVrZGOwZrmmSb3Zc89ixbqTioLZRxNmwjtFwYut+tNaq0aruWwNetW5"
    "aGzjWjJZ4P0NC/7JXDANY3o5/GrWQEs9607zl0u3wuP1tYfkJfB1Wha5Ohw8G6I1J0SxjQVRsjbU1SyicplWJzQtdwBySgmTBXd2"
    "y1ETWaWArF12fjEuOzDqb2OxO79bapjRefA6CHpBz8FVP6+thrGXa/rxvCXFYb0mtIF6eIt2K4jHZ8fRwAfKCaKzN3QY1dpchVin"
    "F5UvRY2WNtQKFBUk0Kry7uPr1y9e/8TnBI03RWP4vZX1Ws3sCdubj3+QmkiAU9D0NI9bORDcB1EUW84ata069+va3MUHx4dttGZq"
    "P0w3CfrELRtW+RAF12Gj7k0b7eoWvk67YMk4iiPuDYjbGQP22AMHep832rVao46d0+YyZb/Q/XtpTnKYjmziGIcOOKp/3IeBFjOQ"
    "tNvNV+8LaDbQqDsHS4n2f7hPm5/pVTzrmSFpZhzCs6bJlsge1jqCo2beEyZZkuWcvzXjbU9Ud52+bPBbHb0jx/TNcxeDkpiVmJlB"
    "98pirmHTpQrof8M3Eml0lw2rzTSs0JDPUl4vIutxhGqWu2gkJN9FbKYqIP+NOKo2CevxJG6ab29sE7ruTTDVrajuduzor0Hg1HY3"
    "b8VmBQD0B8C+wa04wEPy3nvYbhTaVmChOU7O528sD+ECW6lV25xnbnM+2Yn4dOSDjiSkadNro65yPgROcwaS9axX2Zz2kU3sbVU2"
    "CwPBMLQhKtXdtuWPCfPuOaCUzwGGWRxgoLoig63EjNXDnGub+vXq3Gox0Z6BZEAYWz36pV+S8V3mUmvwlVFeuEW5aRVClujZJKbe"
    "iD71KWVWlk6Kz1a/Wl1ZKx+6b1WdprjJX5r7xMOjYshUHppMBkw14P2+qXRWa3vFy8uYDKOO1rYYVHlcbLZKFLZYM4T56DSE4U3M"
    "iFWsPQtGvGbIEdInYgO+VtnBSjc6q22nrM6iYBL4McV3dzjqN0wm/IyBt6mFIFObddG0LDfQRA0NxeyocPDlDMtXJfPdlEUwaHsf"
    "mhjo5I3m9stGPzIHWMzQuL9nO/4C9F6kmrZYU/hgVQZGsvO3RiLgsWh4eHY73hsrlTs0dYWhMSMNaEwIg+qboXWet3Qk/LNVcio2"
    "pE+EORkWpF8h7KdWrkrNjbs039ZxflCXrcf+1m5vb5vcp8eGZ0kMJI4uK82m04d6Llyo/2y6XKhfodcPN/jzXpsdo+PZG6OIwtqv"
    "vOfNA90ppDmfpyKnuGzt9z9FRZBD0aR51fg8KHI/EIyjgon4GvjlM6aFYgkEUdR68ODel4Ewv5XfhCIGvn4mk7M3rOCD3zlk7+Rx"
    "u0G1cVoNoN6jAfLRkvSbsJtdX4thlDPES17ypHp9/U583f91xjvAw9ujQCM4JYLMgwd/DTC5hzJU94ul5ReV1EFAYqXZ8oa2Le8Y"
    "iFlGKzpuKsNHR3BCxPTpvCSTWKaU3fyECqX17EzquQ1XUFf0RM2guNnUFD1/NoVBcXgibn7SrpiFN8U2LLrpuPi5JCMtcyhxsx7F"
    "qXtTyaq125t/7nzygHJxoKfnjAC5mkqACGwQdOt37suyvDhMOEasvZ6L+EtsORbKyWVcqWUIg3OOqcb4yq0zfwJK34jOLHj6jnTA"
    "mYK+DrkeKoj0NyDsDQ1zZizurq61e62OCKsWu+rtAotIB4kwT48vg5IDCDUZcJfdmowt4F6NN+yAuuulx814iNKDcAF+rh00J42n"
    "aUGidrs3GFqCjC1uHR28vNxJZlowIKdEoa346awIi2HZRd4QGc7OeKQxBLtaHkZqc+I41r1IE4ir4vByTby/yMR7V7dPP6yBRRcZ"
    "WOTqcNHKRg/A4O1aHY/VT6Fjj09PzbAn4v7O5C9xgmEijkMAfYons93CAVwjyL2HUSyzTNiyaYsf+fvSnQjf/Cu0hy/RDNXv9Yrt"
    "MOr65cUI8OcjebChVF/yfu8XS5Ty7kXzoBUXnzdL+8/6xRdwe8P7FX152Tx40aywNMYVFnmc5z0eBZhzFAPMncNZ8a5JFh0vZV30"
    "oZwEKzzpfuvTCScnKH5wpyeaDJwkdlvq8F0THZze9+Hg5cWHh0tM+7kcTadBb4SnEyUfgFlO0dy32P7eB0mitP/jI5S95smT7wqF"
    "H8n2qgAy98F9+gniTpDcL3SjMI7DaDQYzZ4Mk+kErvyYjt2fjiZXjfgqToIpQM0rYzLEoMwKvKdApuNXfvc9/fkcWnjvg0EYFD6+"
    "8GJ/FpdjjL64T11hmtJGbWt+uaJd4duw7JLtF8C3WC6jmIVCvfd9vVp/vFkr7aMzyoAsfbUqqtD7vr/d3+nvlvZ5pp3qSnbsd9GF"
    "sqz3P8cAAFDzipWW9rt+FNhVcALiO/3GCGwR8qNy2O+j+FOpB9N9HTw8t7K1zn1qw71iapWtbTm3wj88+bPB3ty0Ah8DAC074SV2"
    "hWI0M5LD9POqhxPmEnMq8+ygX8290XQeRok/S1TFxgXMLSiyMEMsSTsw3QlmZsfVAQD8Eu21WEWq6bDmDevecNObl5YMzOUOhuVH"
    "5V2UaCAvDGtLBQKMPscgwux4GzvbVQskdQ0kMIT6van1U9ux+6na/Wxq/fjLvB3XFtdgUICTObPFLIn8WCJDChdzOmeQIwskPM0Q"
    "6BVEXWYiwwBe5rl9y5QmfdRtQPXFxI/w7zhrA333FnrxYoozAUGXJ4EFDsk8Y3jkqSU/VBv1+WUhDiejXiGDKHhFge2b88vUZDLQ"
    "CLhMOJmUdSRp7FapvbxALZ0kHS+ivt+F24DEdVjttFGz5krUTzXgSjAJLssXkT9v4P/s+5PRYFYeARuKG12KXLs/gG81WO7+HBg/"
    "EhL+USB8ElSDneizQxTWWAnyIzjNO360XG+4XWffJDustfDcFXPYYPiJRWytbEdAmR6dlzgXXOcU9oG56FXlvAbRqKfVfUJy0dKi"
    "MFYBoySkOPQUc4CXdGZXF4PTp4wGrAZLu3Qz/u+HIBf20WeHYO7PrgjztFHruzfzF33ME5IWRzMRd/gAfQlPcyfLNakurldHBm+U"
    "YxpHLGVNg+k8uVr+uYiTUf+K4wm1TGMldZXeHOrhyT9sdESWQjCBD5d8b2vV6g8SYA308eVdoNt9uQebOJosL4YwizKI7d2gMY9Y"
    "H7lQ5ocbwiSchdTQk7/s7f8nSSCFoprUYzwASkuNuDyNGHSSNAkNrhFlAaOV7Bdm3A8iDNvWW3SDHkyJUleyP3GU9U9WzqU6wdA/"
    "H8HeI7zUybkPPH8Wj6h380zd92fAJ0lN3VtE9KNRqdamsbMKAJvVYcGAGzXtcJargvnhYggH4wam4zzXF/P3sf4hUMiEwgqs4FqO"
    "QVDCExFYsN/d3N2p+6fE8ggG+2xHieI4ceFvaOqLVrXu472gXu0rgYRhcuwjwXTH6Xo2u7yhPkwkKTaIKJQYwk+JHTYXfI1Lj2Mx"
    "bkGSeLqjCzxhMyBDchEEs9xTxOTrcU8OtdXrbm92dk4l17WW1CvM03UVWcdd8XWvX/M3e9XHp8t1ToN1zlH9rNDPAkl+VTwRiQbj"
    "bkVEaUnPJwQo4S29JjpmHhw9H24PuMQuxYpMt5PAcx1EHJDdcnwBFJBuzDZDbhRxT5OjaluUZqLUcSZo6w7QksQXTjiIvRTMbbBu"
    "A9tli9rcUaSxydCxW8bQMunxBeirhS1xgEk2ap5foh+8WKf7IeqsybVnn/TQQxLOs8DrFGFyd4v0YA4UyThK2DT1HgXq2/ellAgC"
    "g/UWjplz8kdrkYZ9O9jiDXlMnknoQAH7zMeYThgQxTkD3hHw0Js7YiEm3P2MALvSPdjsiG8Ex6q6hlW6yMB6hJNKMUoNwZ13ZqcM"
    "uan6RzhKEYJdLtUghVF6GIGlKHsIHCFJiFHeonMzuIQkuZZobYuzFuWkmcqig0fkuohKbeCMCdaeti5QzUKaOukLJBSDyWQ0j0ex"
    "E+HrGfAm8SiLayEh5x4KkoAZhVD1qkIcVZBiESwXeOzmM9ru2GechHcmj6pXq+bWUXVMEJgxWMcHoDHE0k5JuZObO9uPu53uJpwu"
    "MHk89PEQn3FowJ+xVyvtZ4gX6V5IsKCAEyXVIZOhYxYuOT3wVx/PmtzuUoAxDiL1SoRWRBYN5Hn73UUUQ5t5SDph11nvPHdTh769"
    "iYl2YKYW+60OTCVVkseGSeju0zS1iUymdkw1F+huSJsz3Nvb0/lsYSd9RuvM/TEx98Q4otV01j+iE/2IVh2srWXADvRjWXWx9rHM"
    "OtGPlBvgutaRYpwMDoaX2AeMGjTvgEn0A0Y1WVNVAc0Jplm4ziSL+hp8VvBValBLoeq6t1eYkB9ptxc1Ies2Cte1+YSYUmFYF7Uf"
    "17c7XSjSLxVQCzlhuop5QmhcAZUnCFcS7Ik+TRxlPTo6RJ4J0OT+PjwjPcKiANg19S+LVa9W2epHJfE3qgS9mlYgKqx1/ZKz6YVJ"
    "eja3VqMpGb6mcR0me8MgF8MwNYhHsAgcwM0gtmzCh446fuRYxvoEt63Nmo76kONLFMCOwHUuTXVsVEVzalzZ2O8A+IB69lFiqO7z"
    "mzbgCCJ6VXZBuQ9ypx8F88BPiEbgbuNH5QHOG/a2uLXdCwZeweLHGC8M09YQ4s99jA6GBciIS/viGlrZ3nZonHa2mMbpqzC1j3r8"
    "jG3J3njqmvXYqCORzgpcLaPUKjvVvl/vnC7N05vqztO1OH3i5KoFZM7nok79cbe297jPabnmOB/P9dmr6qbWhFSVUNU4SlXl9BXm"
    "vMyiasaZPSOu7PJu/3J0SdLgbloaxElMHL3KSjX2ikAV547J5pyTmqQloDSa0TWbn5zn5VnmggjbuSwIY2scR1XN4ThfJx7xmW9p"
    "9C33DGZS8ScOmGmUB6OPuorcvg+2t3a36Mm0t1f1ve+3dvzH27ve95vBzmYPytn3Eg1g3EJMhLOuF7su9Jv6SXf4rUGlVgYEYUFu"
    "R+701lbOnfmcEmAQd86gprprOdgoGxjO6hjgxdHEyYEYiyzWPYMLmachab9cWvYdxvPuMKzJ82jmpF5Nt896xnCunvooDDdT3Xjq"
    "6zyL4vgukWPsLSA+0K9pa+Hb/xvXtHUfLW1pH1aMlqLpFa+vhEvD0HlmZCk52DIjJDPH/Wav6twl43bh5Fnf+HYhxlSijho173qh"
    "2lXwpWTNKceLbjeI45LZwXTUW7O9UEOa7TUN5g3tufYRJIqBaLFb3+x1FXdLb8t8UP4z7Lir77hq63inqmfp1KABviGnGyhyT7Tn"
    "j8f97s43IdwslUg1RyViEVnSrRjs0J6d8QRCvafPjiT1tiH6+Mq3jcR827Dg9m3fNtLPfon9tiHGv+XbRmK/bYh+NMXJZq7iJLHe"
    "NkQH+a98bh0K9KUjt+rs5lsdm4ipjpd78u3U8YlDHS+GyWFn0Axhn26ToS650fSCaVHmcrGdx7WOXw38TMJN2RjdiXp3tFMxLQbM"
    "x+rOoSakTnCqoUtyqhKKUwLBd2weaRtWQC9IoJlrr97ChukbCBWmVJxzEXJBjiF+1ooaQ1z68gYbzBJ1oF2NbsSGfGVM6gKksZ/a"
    "LkO8smOwu4o+0BuOluoQLvtjJajqyCJOrslCfK0G3b3ezs5elog6WZTR8ztdXbtIOV9AoSH24Bgn7yaBiIqX9Ym4UdATDL9VZM6w"
    "G6gLpRrIdVC5zyTeRYWZsaR6KgAfEkdnrlEuWb4O/R5Q3GgWBwmFWq8WEIuy7C750E8qPNNUehniQIiDSZ9fprDVLF1zLR2yc6d0"
    "NFL9aUTAZIX1LPuEQOGUUDjmynX2q9XO3l53N1vMm9tKY9nEw4/6wac6c71bMsXoHE+UcbrF3awY10HmJAuXsy9Lcuk4V+12Yy5d"
    "f4jU4Kgp9GqPyjXtJRLa6MRsg0sQM1XUidfqfH3ird9EvDCQTrxqoPWJF3Eg3f6OtACd+XEMQ2chiCk759pAsGdgAKsQjARopyMY"
    "YjbIxcHbEFwuoRmWAWkCAfJXtOjX9/aqtWrmWWBhhar+jbFiYmGFMa8tV3XjvqPqf3uALqQOuVrtPu7s+NVMzrWINaalaivIL2Kg"
    "uMFAvX2qSmuIV/nilBTp1pCrtlBTb0lWMDdd4lxjsZSIL13/jnzVEpqzR6zAivXTyxrYMveDRvqBoWpnqQGggfYio4HB/SKzpV5k"
    "ajhnSkNfMh9pCli2jhm+XKfO6K0puBk9tNHE2q/YDO2N0dLm228S/MYGI5Mb4boQvqMJVQpZ48AxpGrBLXkMu3NqN0i1KpCtsrh+"
    "4Sa6HuyqTHl9d/QQD3aZAPPc00s/2MnntaDWqW7Wgr3M57V5Soutmuj2SrLHzl69Gjzu1rIf7JLzcjKaqIdFrcWtDoXatkM2co+V"
    "Hurv8E9JSbHZEyqgEVd6VmubdPBeOukubnY2Mb3W9DlNtVe2O0+qgppdB8DTlyFLDZycG7LC7dBCSsyblqiQgYH4Sztr1WACqeES"
    "tiuWBQQcZExLY6a8bhCMb4vau3mPYcGsJ/mZVChWnYvCsdNDa0oVwR6NyaDpDKl7CjA4O2l0YzUYv6Cx1bpugYEaDLdlqjmpgqZw"
    "uQmvHI8wLhFcmO5EgLRsIMOVIoV4nFCRnW4xMwN2jvRGEXN8arBNKWNI6CgO+B7QFRq3gL9AagpHbO4y8uIzqcwUl1ezuatjYk3g"
    "IkguyjhbI/v1HAQdxqyiz0J8Pkj3y880ZLVy27erxmQKlW7NMSFMgOeSRtlGbrttC1WX9Ru7TPGhTTGtSTBwQ0i3T7ytSRjvuDAZ"
    "pfu+hemi6KRQYSEmsziQYY4BrdKY7TFcu7gJ5VHRntIz6mQs2XfkwtgMuaSebfK2I03ebhJbBew3jeuEBm8HAWUZtOPxs+Y57z7D"
    "NWl1d55B2UlhtMYYKWLOte6kXitR0Ftz9vLlkx1NX3le1nfXOi8vRpqVg3W2kPUaBtxvLDBVbtcH7jkJkgSvUmjDBhtcqW4F0/0M"
    "jq8duWkLZD68ptHKwvPH1m3DtACzadG9v8NhJgtc0y7CumPbLxpZd+47OHhXHbxlOMwValilvj+a5LOdHQF3B3tynM8Zs9U2IZJk"
    "lSEvmGZqOLKT0rJumlXLLtR90yQIOTHJtunrTQZl3aHGr9d39vzNrdOUZzH2r2Mww1ls3x2Go6665qgulGGZfInb5JfNW51J9mOd"
    "GjQ9pq12JHxjOlL9ehvLG0W/v9nvPe76mYZInfIimqRrM7vHnbTdYwcdb9X7t9b/bdhVTWNXLinZOVFD622O61aGXHyREKxu9ra2"
    "d3ezwHDxRbNnlXX1nlCtEqerZOiBpeZC82lK20TxXhWJqH5vY0wt6WfXOPq0/ivKjS9niPQbFYisJ1bwwdMb31bdArmuDwckPR/a"
    "bC8wHZfUeF/K5CHe2FZm4gDz7viK2Xmzprorr2oqT0JdL69UQbVq1YpHYSMdZj0Muo6Ob7BOrGxrgpRSe2cezWwcjemroVI3WVF3"
    "M7MuSXWpU3hLa/2kNzpPN896etnNdwSCLimirANVNNeUPC1M1sA7btOnLNcVNRUndL6plJOWb+TY8+xNZNV0/bqJrPU7XWl4l9qd"
    "RvV6F6siQhIfQ45k4cg6dyTZyRNdSyZ7asySIT58T3rFeolf63iri1ymw3M4Ztt+aVIEV43xlJFumLvRCOvrlsk30T4qXeC/qnHB"
    "uepbKOIRyYXSGaaYNh43DExoWAyrHK8748xXui3zKrFjByBSQOpFV4VkmB4w7YjBKqdqmir3Lblb/TgTclUnS3IQTXq683kObW5J"
    "rxUkp3CQrph5Z8UJh+G6R6VtMnaTf/T6UZzyY0aljk/hIJVnon/XA7DPxYd1TobqupAwPMLrtitjdbXCIIAeigIeRhFcmiLHDxTE"
    "bw3TMBFP+WZJx5ZpqC1KMWsILTz88joM1bxV8YZm2C8WKndpyupUVqhQbN9lzvta1jgYHlVxZgopm28FvqZkmnWvw3DTHvunHM4m"
    "V8vuZDRvoBxZZPZUVademXMPjSPqLoXSKzCtKWCxrJfZ8mrK5NqheBVhVhmY2e+lpR/Q/Xnm9Hj9t7xcZU1ZjvpkWL9FUDjrOpxe"
    "uECPu8SYg+YXw6u1X6VIybrGq1gaPdhQgKDLnEerOcYdywqNshImeusc3g78XN+HP0cDo8zUd/PN1OvVHIrGVVRYlNG17Brz41KK"
    "Dgm6N7wM7md+yOMo5c5AG6cDjDVjGBHFJqs8RwVrjhGOs4YQrjL7mR/yPGzkKBQNTxtj4s/joCF+mGocXhtkLE/7QwJhDWttW3F5"
    "jqF/u/6El02BFU4C3c7aGPWuxnSyi0q0tF2vcsLuCYZsBtrjR5sdZoWR4qay/L9k+rPVd4/+sXEONLTRqP3j0Y+P6Nr05LsfH+G5"
    "DP+iEFCg+MoH93nQuvtQDBfiwqh3cB/khvtPfnwEf2IbrExtQbB48t3/BUXFdKY="
)
# --- END GENERATED UI ---
