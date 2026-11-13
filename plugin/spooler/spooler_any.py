# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.22.1"
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
PLUGIN_VERSION = "0.22.1"
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
# carries the filament's colour, vendor, temperatures, density, diameter and cost (the filament's
# price, else its spools' prices). It shows up under "User presets" in the sidebar's filament
# dropdown.
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


def spool_cost_per_kg(filament_id: object, spools: list[dict]) -> float | None:
    """The mean price per kg of a filament's spools not archived that have a price, each spool's
    price over its initial weight (else the filament's weight); None when none has one."""
    rates = []
    for spool in spools or []:
        filament = spool.get("filament") if isinstance(spool, dict) else None
        if spool.get("archived") or not isinstance(filament, dict) or filament.get("id") != filament_id:
            continue
        price, weight = _num(spool.get("price")), _num(spool.get("initial_weight")) or _num(filament.get("weight"))
        if price and weight:
            rates.append(price / weight * 1000)
    return sum(rates) / len(rates) if rates else None


def profile_preset(filament: dict, name: str, parent: str, target: str,
                   spool_cost: float | None = None) -> dict:
    """The preset JSON for one Spoolman filament on one printer. Values are lists of strings,
    as OrcaSlicer stores them; one value applies to every nozzle variant of the parent.
    spool_cost is the price per kg from the filament's spools, used when the filament has none."""
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
    elif spool_cost:
        preset["filament_cost"] = [_fmt(round(spool_cost, 2))]
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
        files[f"{name}.json"] = profile_preset(filaments[fid], name, parent, target,
                                               spool_cost_per_kg(fid, spools))
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
            "remaining": remaining, "initial": _num(spool.get("initial_weight")) or _num(filament.get("weight")), "location": spool.get("location") or "",
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
            sys.platform + "-" + platform.machine(),  # platform.platform() opens files Orca's audit blocks
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
                sys.platform + "-" + platform.machine(),  # platform.platform() opens files Orca's audit blocks
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
UI_PAGE_SHA256 = "f91df9abc9512d21fe2f9d4241cc045e8399d7dda7f205c808198d67fe65e629"
UI_PAGE_BYTES = 825739
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
    "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"
    "1bwM4lsremu7uv0MGyt71bBsoO7JDjZW+GTLm6l85eYNlb4KiBupfRkBNtp/DaIkqcfEK8IkrcDCJo4cS20aU6xssY4w5Zw/4c7L"
    "wL3txlvb062n13TbVUPSfNfJ9ptuOtnwRnuu3LrZlqsAt8mOy8iu0YYruHesOa2lN99YVjp+pQaXFWewWZPL3GeE9Z9yqkFoelTc"
    "+JC4wfHwYrr689jKT12LafFr17oBNlgL6Ly0HOu63wTP0+aonm6A7elmCL/h94Tppp8Upht/VVg3kcnpLShncrqecvIDbEA50HkD"
    "ysl3vwHlQPdNKaeiai3lFOquRfjNKKcZ8KsbrKGctRO5Say7FV+oikIn92WqYgMWJUzjsVd9nFR1i1UfEPnom+8cKesqbxmsQPJK"
    "nURvAF9TRaaElwrbFj+77pQ8cgRxNOUePuY7LBHm29Dn4q0wWNDEgM6TyyAZL9ZdKKjYRGFwEW4IAbUBCKw2ByGKN4Xg/3kXfjxJ"
    "AuixdobKLk5mUyWpfDXPfeOuu8Jjqld4ltm1g1ldn9b6Pq1yn01mxjDXbGY3g2L1zArYYhdTborE5f/4DZxdFH0MiNtYioOLrYwc"
    "/e1UvoTT0bdFcfuib4uqh1363eKeLdRkmfl6U6yTd9Wglk9O1XLmqmF5hO+aiOe8Zleu+n7tbSxfVK2ow90y+HmR67NH7X5eziOe"
    "Z8J3Qq4vhRfxSvujqirUN17SPz1TvTE8E1fmyu4YVr/h9/Hbqb+kIekV9CpfASeimL36bezWQTzUzOa1vhrD0Us2B6pNNwnzQ97+"
    "2b94tH92tvrRPkdww1f7x2eNXu0fn/2LXu0f52/KX5yVXu1/PPtyr/Y/nmW86+1Z1av947PVr/bfZg8zaGqf69U+dP5Xv9r/IHlJ"
    "iY+cnpXe7Ycw0KKPb59gm/r4vPYERf0YX3dG0xA4Od+qQRpUbCZ+FoYLt9SnoGGl+Xf2CFA4wC21y5/sngDhLsL0Z9a5+mwyNHhv"
    "A4TLuIegtTKAtKUuu9AUfwIEeW6HsBfBWV/sNTbrjs8zzLsIoNy1z/jv4bqEF+e0uYCAjckMFj+kJ/rDtTWY8SH54oqH4LDb4L8r"
    "6Sml9t20zsRnqQKXquLdsJDcuVTdo+S6t7+5d8PycVd/caayylfNWOWrfxOrfJVnlXuc0zBOwlkjaJ8LqIUcguechumLy1gwSzbO"
    "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"
    "XD4VyuNCKnLpi+VaLr9KUGKxkD1vOUBY1xzDD5X4oX5cZfvoKuN5ES6+cRGinGfvughpRjvoIqQ01mLphhhbzthxqN+olfLnQ6g7"
    "Klymh/QxWSlzCnR6lD7etHh8GWdWWrY2nZcaVX69u3SmtBaKz+qZZPF2VDNKfHgQJb5WGBYj8/hBWc8zkcOa61aVuJatiEP5GMvE"
    "r5WqeErFu8lUCGwX6Wp8yNDcSg0V9+vV6XhTlNtB0SLdVajTTk5OU6W8B2l7Shl3Z8eJMGSimniLqgD9Qr+fjGayaU7hdgWFPkSF"
    "wagwqPcr52SWXe7jyewmFcrE2wlNWOfWuUIhx5c2dbFyzdLJony5HLuhY6I6Xpdz/UJvs9ow6eVhfYmsVonjIBQ7rEfr5lq4Mccu"
    "xdLLVfy0vG6mVCOU7+T6zXpyqFajsSgXmiq1WnlTqR2p3qHDbkLT+VTWIiwnS+tRjssNc7NCqHkZt1dUNJOOtvh5r5TrzRuR5RDQ"
    "/fqiKeVcOkJf5td5v5CdZJf7aaN77GQjkXRyTxcALy+vtUF9WW/KWaEmMdyKEzvspFRcRW9jccN1lOKtvEy0SqNDt7ncbsv9Tjo9"
    "bR7VEBeN9SYsNZkVUukT3S9PloqY7p3X7FBKNY9KqTy/XUaSoLQTTOuUk/tsYzLV9uCMPojIiV4xV2nVTnEqsc/tjnFtc8iNCqtK"
    "/3q+gtnIVYebojzdnYVlYXCtAwH7IpaoS5w7c/1khy7mdulDfZCrx4pcV7lcqs1mpVae7Xo5dpPd9GB7gpxYLuP55Lnb6xQn2Qin"
    "lvPd1ajVb0T5FR8tMZV8dspR+6ocBaecVZWd87VNcdbOhNRirRUBKBnW1t3B8iS38m16NW6lE8suEBDAOikA/BaGVJaOHnpchWFF"
    "pVS/1gqlOTeMlJJatCG2y1JZ3R+raXnQyLCVbDs/3ChVrjQs9Iql4kiczeftdqqcbJZHpWw9NawIQveqZUb8ZqyV8qV9PnptFQqd"
    "c7zAV7eRVKKWvsXLowRfWE2ylfQhLQEs58C+XGTVaacuFnPFS0kpx8VDVYoVutsdP091I1Iq10xI81Wutq7thNChoOxT/K2SOQvd"
    "yLxWSEyakjpPt9KT2bx3jK+VUnq7rCfkGZfOiolmK786UfMxnYpxKuAvJakQ4hPx9ajFjbf1yopqTMqX03VcpboFuspne9NDijqW"
    "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"
    "59RnP45t48vXn/n7H/lp+/T44Mvh1afpYfnb98kv62jv4r7z0bz/ZTwW5o/VS+/wrD/46GrfPpTyFxqwzn516I3Pt64GVe3b2S9t"
    "y7H3+q3HxfvZ6feTo+9fpr9Ozvfzv05mp+P7o4+V9uyw/yOvfbNKvnP5fnp8dbC4nx4PjkDg/nRtuteWf/atZV/P8mefHhfDo88X"
    "J/6x2z37MLTqM1C5KsBYdtonO9bHXtX4+elqx5r5J1/Ge44/2euO519dFEh+VXY+lttnnfEhCM077bPB+Bi4+WG/Pjx4XFRPzfff"
    "rtzzz3uls08aIM8YnxoP3/vdrbPDnwPnvgKAuZ67M7YL+cnXDxXr4bxWHO//yNs7tVa7X51ca/ZDff5hZ8vu9neq1ufP2sj51t+Z"
    "9QZfe2c/F+aee96xaoeVxU7l8Gh0361dfZ8Wikcz9+dJ8ddepVx88Gpnn+u9h+PW+Ljz0cmPf/0szPPml5Pj66Mrf+fw49X3wfv3"
    "5X73wih/174Z5eqpMzFG1taHaslYfL8/Liz2Ph/O7B3r+tOXS69zNDS/XO2Mzz/0Z6U90EorC+3SaH3/9e0SpJT2z4sPB7OF/Sn/"
    "TfsxmZwUL1t9q3tynD+wdpzi9NDc6n3tvR/55R/tzw/7oAp8aA86X799+37VP/yyOKjMtC8HVe9qqn09fH/a/2FdffqpLTr5y6lT"
    "rf7oP5wf/DD7tdn13vy6U9mZzEBrvr8eDi/ef33sfzmb5WcfT086v2bzj+fG/uHO4vLRHR8/HPgfrzrjC/P+fPHY9ofu/YfHr1eH"
    "/bH55fCsdfLt8VPrB0z9pakZP/z3X+0f+P6A1n9/cHbgTb+cfBkdWt3hwuu3fn4vnPQKH0tno4PTdvf9xfXA7j2W7nfM89rOB+Nr"
    "3rA6e9aP6Wn7s/fhvD359pCve65bPe74R+eP2sns60c7f3m2/3Hsfm91/S3zU8VZLOqH+55z8amg1btXo0+d++N7zT6yvriecTI1"
    "PtaLx+fH5xc7xsGnh/7VYuvgbP98uvejddor1vd/zMtfzh10wj86mU1HHw7vfxx/MEv79yc/W9Xe5Mfh18qXReVDof/5rFb19goH"
    "+7VPJ8e174/axeF45IM26lQ/W197lYfO8ODjtN7f/3Lf6V1+ne6f7mgfSoP3F7PHo8M8EO+iN7UeZ4cfr3ceP1z9+lSpXB18riwu"
    "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"
)
# --- END GENERATED UI ---
