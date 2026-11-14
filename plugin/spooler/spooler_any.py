# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.24.0"
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
PLUGIN_VERSION = "0.24.0"
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
        "auto_keep_slots": False,
    }
    for path in (SETTINGS_FILE, OLD_SETTINGS):
        try:
            saved = json.loads(path.read_text(encoding="utf-8"))
        except ValueError:
            if path == SETTINGS_FILE:
                _keep_unreadable(path)
            continue
        except OSError:
            continue
        if isinstance(saved, dict):
            return {**defaults, **saved}
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
    "auto_keep_slots": lambda v: parse_flag(v, default=False),
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
                auto_keep_check()
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
                "spool_columns": 1, "auto_send": True, "send_saved_copies": True,
                "auto_keep_slots": False}
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
        spawn(lambda: [push_notice("warning", text) for text in notices])
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


def _keep_unreadable(path: Path) -> Path | None:
    """Move a file that is not valid JSON aside as <name>.bad (or <name>.<time>.bad when one is
    already kept), so the next save starts clean without erasing what it held: a half-written
    history can still be merged back by hand. Returns where it went, or None."""
    bad = path.with_name(path.name + ".bad")
    if bad.exists():
        bad = path.with_name(f"{path.name}.{int(time.time())}.bad")
    try:
        os.replace(path, bad)
    except OSError:
        log.exception("Could not read %s, and could not keep it aside", path)
        return None
    log.warning("Could not read %s; kept it as %s and started a new one", path.name, bad.name)
    return bad


def spawn(fn, *args, name: str = "") -> threading.Thread:
    """Run fn(*args) on a daemon thread; an exception goes to spooler.log instead of a stderr nobody sees."""
    name = name or f"spooler-{getattr(fn, '__name__', 'task')}"

    def run():
        try:
            fn(*args)
        except Exception:
            log.exception("Background task %s failed", name)
    thread = threading.Thread(target=run, name=name, daemon=True)
    thread.start()
    return thread


def _write_json(path: Path, value: object, mode: int | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{threading.get_ident()}.tmp")
    try:
        tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding="utf-8")
        if mode is not None:
            os.chmod(tmp, mode)  # before it takes the real name: never readable by others, even briefly
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

    spawn(worker)


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

    spawn(worker)


PRINTER_SLOTS = {"ams": 4, "ht": 1, "ext": 1, "tool": 1}
# Manual printers: Bambu (Live Link over MQTT, the default) or a network printer read over HTTP.
NET_KINDS = ("prusalink", "octoprint")
PRINTER_TYPES = ("bambu",) + NET_KINDS
# Printers whose prints are always asked before booking, never booked automatically: their report
# can't say which toolhead printed, and some already book to Spoolman themselves.
ASK_ONLY = NET_KINDS + ("moonraker",)


def clean_host(value: object, port: bool = False) -> str:
    """A printer address as typed: host, or host:port (and an https:// prefix kept) when port is
    allowed; '' when it isn't a usable address. http:// is dropped, it is the default."""
    text = str(value or "").strip()[:96]
    if not port:
        return text[:64] if re.fullmatch(r"[A-Za-z0-9.\-]+", text[:64]) else ""
    scheme = ""
    low = text.lower()
    if low.startswith("https://"):
        scheme, text = "https://", text[8:]
    elif low.startswith("http://"):
        text = text[7:]
    text = text.rstrip("/")
    return scheme + text if re.fullmatch(r"[A-Za-z0-9.\-]+(:\d{1,5})?", text) else ""


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
        kind = item.get("type") if item.get("type") in PRINTER_TYPES else "bambu"
        net = kind in NET_KINDS
        serial = "" if net else re.sub(r"[^A-Za-z0-9]", "", str(item.get("serial") or ""))[:32]
        user = re.sub(r"[\x00-\x1f]", "", str(item.get("user") or "")).strip()[:64] if kind == "prusalink" else ""
        printers.append({"id": str(item.get("id") or f"p{len(printers) + 1}")[:32], "name": name, "units": units,
                         "ip": clean_host(item.get("ip"), port=net), "serial": serial, "type": kind, "user": user,
                         "slice_fill": item.get("slice_fill") is not False})
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


_printers_rev = {"n": 0}  # bumped when Spooler itself changes the saved printers (slice fill)


def printer_state() -> dict:
    codes = read_codes()
    printers = [dict(p, has_code=p.get("kind") == "moonraker" or bool(codes.get(_code_key(p["id"]))))
                for p in printers_cfg() if _live["links"].get(p["id"]) != "none"]
    live = any(p["ip"] and p["has_code"] for p in printers)
    return {"printers": printers, "live_ok": live, "usage": usage_state(), "progress": progress_settings(),
            "stats": stats_settings(), "printers_rev": _printers_rev["n"]}


def live_message() -> dict:
    """The Printer tab's poll reply: live state, the booking list, and the saved printers when
    Spooler changed them itself (a slice filled the toolheads), so the page doesn't save over it."""
    msg = {"type": "live", "live": live_poll(), "usage": usage_state(), "printers_rev": _printers_rev["n"]}
    if _printers_rev["n"]:
        msg["printers"] = printer_state()["printers"]
    return msg


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
        spawn(_ws_run, url, stop)


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
                # Toolheads (U1, network printers) are one unit with as many slots as the printer has.
                size = 1 if unit_id >= 128 else (state.get("head_count") or max(4, max(slots, default=-1) + 1)
                                                 if state.get("heads") else 4)
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
    except ValueError:
        _keep_unreadable(CODES_FILE)
        return {}
    except OSError:
        log.exception("Could not read %s", CODES_FILE)
        return {}
    return {str(k): str(v) for k, v in data.items()} if isinstance(data, dict) else {}


def write_codes(codes: dict) -> None:
    try:
        _write_json(CODES_FILE, codes, mode=0o600)
    except OSError:
        log.exception("Could not write %s", CODES_FILE)


def save_printer_code(pid: object, code: object) -> None:
    """Store a printer access code privately; never sent back to the page."""
    pid = str(pid or "")[:32]
    if pid not in {p["id"] for p in printers_cfg()}:
        return
    codes = read_codes()
    kind = next((p.get("type") for p in printers_cfg() if p["id"] == pid), "bambu")
    # A Bambu access code is 8 characters; a PrusaLink password or an OctoPrint API key is longer.
    code = str(code or "").strip()[:128] if kind in NET_KINDS else re.sub(r"\s", "", str(code or ""))[:32]
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


_local_lock = threading.Lock()


def _local_sync() -> bool:
    """Match the local connections to the saved printers. Called from the UI thread and from workers at
    once; the lock keeps two callers from each starting a connection to the same printer (two Bambu MQTT
    sessions with one access code knock each other off)."""
    with _local_lock:
        return _local_sync_locked()


def _local_sync_locked() -> bool:
    codes = read_codes()
    wanted = {}
    for printer in printers_cfg():
        if printer.get("kind") == "moonraker":
            wanted[printer["id"]] = {"ip": printer["ip"], "name": printer["name"], "kind": "moonraker"}
            continue
        code = codes.get(_code_key(printer["id"]))
        if printer.get("type") in NET_KINDS:
            if printer.get("ip") and code:
                wanted[printer["id"]] = {"kind": printer["type"], "ip": printer["ip"], "user": printer.get("user", ""),
                                         "code": code, "name": printer["name"]}
            continue
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
        run = {"moonraker": _moon_run, "prusalink": _net_run, "octoprint": _net_run}.get(link.get("kind"), _local_run)
        thread = threading.Thread(target=run, args=(pid, link, stop), daemon=True)
        _local[pid] = {"link": link, "stop": stop, "thread": thread}
        thread.start()
    # Keep the links up while the tab is closed when a print on them may be booked: Bambu and network
    # printers, and Klipper printers once a poll showed Spooler may book them (see usage_track).
    booking = any(link.get("kind") != "moonraker" or (_live["printers"].get(pid) or {}).get("book_ok")
                  for pid, link in wanted.items())
    _live["keep"] = booking and usage_mode() != "off" and source() == "spoolman"
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
        auto_keep_check()  # the first snapshot is what the automatic Keep Slots Synced waits for
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


MOON_STATES = {"standby": "IDLE", "printing": "RUNNING", "paused": "PAUSE", "complete": "FINISH",
               "cancelled": "FAILED", "error": "FAILED"}
MOON_IDLE = 15.0  # seconds between polls while nothing prints


def moon_progress(status: dict) -> dict:
    """Bambu-shaped job fields from Moonraker's print_stats and virtual_sdcard; {} without them."""
    stats = status.get("print_stats")
    if not isinstance(stats, dict) or not stats:
        return {}
    state = MOON_STATES.get(str(stats.get("state") or "").lower(), "IDLE")
    sd = status.get("virtual_sdcard") if isinstance(status.get("virtual_sdcard"), dict) else {}
    frac = sd.get("progress")
    frac = float(frac) if isinstance(frac, (int, float)) and not isinstance(frac, bool) and 0 <= frac <= 1 else None
    file = str(stats.get("filename") or "")
    out = {"gcode_state": state, "gcode_file": file, "subtask_name": Path(file).stem if file else "",
           "mc_percent": round(frac * 100) if frac is not None else 0}
    took = stats.get("print_duration")
    if state in ("RUNNING", "PAUSE") and frac and frac > 0.01 and isinstance(took, (int, float)) and took > 0:
        out["mc_remaining_time"] = round(took * (1 - frac) / frac / 60)
    return out


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect&print_stats&virtual_sdcard"
                       ).get("status") or {}
    active = lanes = None
    # Moonraker answers {} for an object the printer doesn't have (only the U1 has this one).
    if not status.get("print_task_config"):
        lanes = moon_lanes(base)
        if not lanes:
            try:
                active = _moon_get(base, "/server/spoolman/spool_id").get("spool_id")
            except urllib.error.HTTPError:
                active = None  # Moonraker without its Spoolman integration
    doc, heads = moon_report(status, active, _spool_cache["spools"] or [], target_for_host(base), lanes)
    doc["print"].update(moon_progress(status))
    return doc, heads


def moon_spoolman_connected(base: str) -> bool:
    """Whether Moonraker's own Spoolman integration is set up and connected: it then books the
    printer's filament use itself, and Spooler must not book it a second time."""
    try:
        return bool(_moon_get(base, "/server/spoolman/status").get("spoolman_connected"))
    except urllib.error.HTTPError:
        return False  # no [spoolman] section in moonraker.conf


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
    spawn(work)


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
    checked = 0.0
    while _live_active() and not stop.is_set():
        busy = False
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
            busy = doc["print"].get("gcode_state") in LIVE_STATES
            if time.monotonic() - checked > 60 and not busy:
                # Re-checked while idle only, so a booking rule can't change in the middle of a print.
                checked = time.monotonic()
                try:
                    connected = moon_spoolman_connected(link["ip"])
                except (urllib.error.URLError, OSError, ValueError):
                    connected = True  # unknown: assume it books, never count twice
                with _live_lock:
                    state = _live["printers"].setdefault(pid, {"name": link["name"], "units": {}, "ext": {},
                                                               "time": 0.0, "link": pid})
                    # The Snapmaker U1 (toolheads) is booked by u1control; a Moonraker with Spoolman books itself.
                    state["book_ok"] = not heads and not connected
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
        stop.wait((MOON_POLL if busy else MOON_IDLE) if not fails else LIVE_RETRY[min(fails - 1, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


# --- Network printers: PrusaLink and OctoPrint -------------------------------------------
# Added by hand on the Printer tab (address and password or API key), read over plain HTTP and fed
# into the same live state as a Bambu Live Link: progress, and the spool assigned to each toolhead.
# Neither reports which toolhead is printing, so their prints are always asked before booking.
# APIs: PrusaLink v1 (https://github.com/prusa3d/Prusa-Link-Web/blob/master/spec/openapi.yaml) and
# OctoPrint's REST API (https://docs.octoprint.org/en/master/api/job.html).

NET_POLL = 3.0      # seconds between polls while a print runs
NET_IDLE = 15.0     # seconds between polls otherwise
NET_TAIL = 512 * 1024          # bytes read from the end of a job's G-code: the footer and settings block
NET_STREAM_MAX = 512 * 1024 * 1024  # a server that ignores Range is read through at most this far
PL_STATES = {"PRINTING": "RUNNING", "PAUSED": "PAUSE", "ATTENTION": "PAUSE", "BUSY": "PREPARE",
             "FINISHED": "FINISH", "STOPPED": "FAILED", "ERROR": "FAILED", "IDLE": "IDLE", "READY": "IDLE"}


class NetAuthError(Exception):
    """The printer refused the password or API key."""


def net_base(link: dict) -> str:
    return moon_base(link.get("ip"))


def _net_request(link: dict, path: str, headers: dict | None = None, timeout: float = TIMEOUT):
    """Open path on the printer, authenticated: PrusaLink with HTTP digest (username and password),
    or an X-Api-Key header (OctoPrint, and PrusaLink without a username). Only paths on the printer
    itself are opened: a reference the printer hands back can't point Spooler at another host."""
    base = net_base(link)
    if not base or not path.startswith("/") or path.startswith("//"):
        raise ValueError(f"not a path on the printer: {path[:80]}")
    url = base + urllib.parse.quote(path, safe="/?&=%:@!$'()*+,;~-._")
    req = urllib.request.Request(url, headers=dict(headers or {}))
    handlers = []
    if link.get("kind") == "prusalink" and link.get("user"):
        mgr = urllib.request.HTTPPasswordMgrWithDefaultRealm()
        mgr.add_password(None, base, link["user"], link.get("code") or "")
        handlers.append(urllib.request.HTTPDigestAuthHandler(mgr))
    else:
        req.add_header("X-Api-Key", link.get("code") or "")
    try:
        return urllib.request.build_opener(*handlers).open(req, timeout=timeout)
    except urllib.error.HTTPError as exc:
        if exc.code in (401, 403):
            raise NetAuthError(f"the printer refused the {'password' if handlers else 'API key'}") from exc
        raise


def net_json(link: dict, path: str) -> dict:
    """A JSON answer as a dict; {} for 204 No Content (PrusaLink's /job while nothing prints)."""
    with _net_request(link, path, {"Accept": "application/json"}) as resp:
        if getattr(resp, "status", 200) == 204:
            return {}
        raw = resp.read(4 * 1024 * 1024 + 1)
    if len(raw) > 4 * 1024 * 1024:
        raise ValueError("answer too large")
    data = json.loads(raw.decode("utf-8") or "{}")
    return data if isinstance(data, dict) else {}


def _pos_num(value: object) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
        return None
    return float(value)


def prusalink_job(status: dict, job: dict) -> dict:
    """Bambu-shaped job fields from PrusaLink's /api/v1/status and /api/v1/job answers."""
    printer = status.get("printer") if isinstance(status.get("printer"), dict) else {}
    job = job if isinstance(job, dict) else {}
    brief = status.get("job") if isinstance(status.get("job"), dict) else {}
    file = job.get("file") if isinstance(job.get("file"), dict) else {}
    raw = str(printer.get("state") or "").upper()
    state = PL_STATES.get(raw, "IDLE")
    if state == "PREPARE" and not (job or brief):
        state = "IDLE"  # BUSY with no job: homing or a menu action, not a print starting
    name = str(file.get("display_name") or file.get("name") or "")
    folder = str(file.get("path") or "").rstrip("/")
    pct = _pos_num(job.get("progress", brief.get("progress")))
    left = _pos_num(job.get("time_remaining", brief.get("time_remaining")))
    out = {"gcode_state": state, "mc_percent": round(min(pct, 100)) if pct is not None else 0,
           "subtask_name": Path(name).stem if name else "",
           "gcode_file": f"{folder}/{file['name']}" if file.get("name") else "",
           "task_id": str(job.get("id", brief.get("id")) or "")}
    if left is not None and state in LIVE_STATES:
        out["mc_remaining_time"] = round(left / 60)
    ref = (file.get("refs") or {}).get("download") if isinstance(file.get("refs"), dict) else None
    if isinstance(ref, str):
        out["download"] = ref
    return out


def octoprint_state(text: object, completion: float | None, has_file: bool) -> str:
    """OctoPrint's state text as a Bambu gcode_state."""
    s = str(text or "").strip().lower()
    if s.startswith("printing") or s in ("finishing", "resuming"):
        return "RUNNING"
    if s.startswith(("starting", "sending file")):
        return "PREPARE"
    if s in ("pausing", "paused"):
        return "PAUSE"
    if s.startswith(("cancelling", "error")) or "after error" in s:
        return "FAILED"
    if s.startswith("operational") and has_file and completion is not None and completion >= 100:
        return "FINISH"
    if s.startswith("operational"):
        return "IDLE"
    # Offline, Closed, Opening serial connection, Connecting...: OctoPrint lost the printer's serial link.
    # That says nothing about the print, so it is not read as the print ending (it would book as cancelled).
    return ""


def octoprint_job(answer: dict) -> dict:
    """Bambu-shaped job fields from OctoPrint's /api/job answer."""
    job = answer.get("job") if isinstance(answer.get("job"), dict) else {}
    prog = answer.get("progress") if isinstance(answer.get("progress"), dict) else {}
    file = job.get("file") if isinstance(job.get("file"), dict) else {}
    path = str(file.get("path") or file.get("name") or "")
    pct = _pos_num(prog.get("completion"))
    state = octoprint_state(answer.get("state"), pct, bool(path))
    name = str(file.get("display") or file.get("name") or "")
    out = {**({"gcode_state": state} if state else {}), "mc_percent": round(min(pct, 100)) if pct is not None else 0,
           "subtask_name": Path(name).stem if name else "", "gcode_file": path,
           # The file's upload time tells two uploads of one name apart, and stays the same for a whole print.
           "task_id": f"{path}@{file.get('date')}" if path and file.get("date") else path}
    left = _pos_num(prog.get("printTimeLeft"))
    if left is not None and state in LIVE_STATES:
        out["mc_remaining_time"] = round(left / 60)
    if path and str(file.get("origin") or "local") == "local":
        out["download"] = "/downloads/files/local/" + path.lstrip("/")
    return out


def net_trays(printer: dict, spools: list[dict], target: str) -> tuple[list[dict], dict | None]:
    """(toolhead trays, external spool tray) from the spools assigned on the Printer tab."""
    heads, ext = [], None
    for unit in printer.get("units") or []:
        for spool_id in unit["slots"]:
            spool = _spool_by_id(spool_id, spools)
            if unit["kind"] == "ext":
                ext = _spool_tray(MOON_EXT, spool, target) if spool else {"id": str(MOON_EXT)}
                continue
            slot = len(heads)
            heads.append(_spool_tray(slot, spool, target) if spool else {"id": str(slot)})
    return heads, ext


def net_doc(job: dict, printer: dict, spools: list[dict], target: str = "") -> tuple[dict, bool]:
    """(Bambu-shaped report, has toolheads) for a network printer."""
    heads, ext = net_trays(printer, spools, target)
    report = {k: v for k, v in job.items() if k != "download"}
    if heads:
        report["ams"] = {"ams": [{"id": "0", "tray": heads}]}
        if len(heads) == 1:
            report["ams"]["tray_now"] = "0"  # one toolhead: it is the one printing
    elif ext is not None:
        report["ams"] = {"tray_now": "254"}
    report["vt_tray"] = ext if ext is not None else {"id": str(MOON_EXT)}
    return {"print": report}, bool(heads)


def net_poll(link: dict) -> dict:
    """The printer's current job fields (with 'download', the job file's path, when known)."""
    if link.get("kind") == "prusalink":
        status = net_json(link, "/api/v1/status")
        job = net_json(link, "/api/v1/job") if isinstance(status.get("job"), dict) and status["job"] else {}
        return prusalink_job(status, job)
    return octoprint_job(net_json(link, "/api/job"))


def _net_run(pid: str, link: dict, stop: threading.Event) -> None:
    """Poll a PrusaLink or OctoPrint printer while the Printer tab is open or a print may be booked."""
    fails = 0
    who = f"Printer {link['name']}"
    while _live_active() and not stop.is_set():
        busy = False
        try:
            job = net_poll(link)
            if stop.is_set():
                break
            busy = job.get("gcode_state") in LIVE_STATES
            printer = next((p for p in printers_cfg() if p["id"] == pid), {"units": []})
            doc, heads = net_doc(job, printer, _spool_cache["spools"] or [], target_for_host(net_base(link)))
            with _live_lock:
                state = _live["printers"].setdefault(pid, {"name": link["name"], "units": {}, "ext": {},
                                                           "time": 0.0, "link": pid})
                state["download"] = job.get("download") or ""
            live_apply(pid, link["name"], doc, link=pid, full=True)
            with _live_lock:
                if stop.is_set():
                    _live["printers"].pop(pid, None)
                elif pid in _live["printers"]:
                    _live["printers"][pid]["heads"] = heads
                    _live["printers"][pid]["head_count"] = len(doc["print"]["ams"]["ams"][0]["tray"]) if heads else 0
            _live["links"][pid] = "live"
            fails = 0
            _report(who, None)
        except NetAuthError as exc:
            _live["links"][pid] = "auth"
            _report(who, str(exc))
            return  # wrong password or key: wait for it to be changed (_local_sync starts a new link)
        except Exception as exc:
            fails += 1
            _live["links"][pid] = "unreachable"
            reason = "not reachable" if isinstance(exc, (urllib.error.URLError, OSError)) else str(exc)
            _report(who, reason)
        stop.wait((NET_POLL if busy else NET_IDLE) if not fails else LIVE_RETRY[min(fails - 1, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


def read_http_tail(resp, size: int = NET_TAIL, cap: int = NET_STREAM_MAX) -> bytes | None:
    """The last size bytes of an answer to a Range request. A 206 is the tail already; a server that
    ignored Range sends everything (200), which is read through keeping only the end. None past cap."""
    if getattr(resp, "status", 200) == 206:
        return resp.read(size + 1)[-size:]
    buf = bytearray()
    total = 0
    while True:
        chunk = resp.read(256 * 1024)
        if not chunk:
            return bytes(buf[-size:])
        total += len(chunk)
        if total > cap:
            return None
        buf += chunk
        if len(buf) > 2 * size:
            del buf[:-size]


def parse_gcode_tail(lines) -> list[dict] | None:
    """Grams per filament slot from an OrcaSlicer G-code's footer and settings block, in the shape
    parse_slice returns; None when the file doesn't say (another slicer, or a binary .bgcode)."""
    found: dict = {}
    keys = {"filament used [g]": "grams", "filament_type": "material", "filament_colour": "colour",
            "filament_settings_id": "preset"}
    for raw in lines:
        line = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
        if not line.startswith(";") or "=" not in line:
            continue
        key, value = (part.strip() for part in line[1:].split("=", 1))
        if key in keys:
            found[keys[key]] = value
    if "grams" not in found:
        return None
    grams = [float(n) for n in re.findall(r"-?\d+(?:\.\d+)?", found["grams"])]
    lists = {k: split_list(found.get(k, "")) for k in ("material", "colour", "preset")}

    def at(name: str, i: int) -> str:
        return lists[name][i] if i < len(lists[name]) else ""
    items = [{"n": i + 1, "grams": round(g, 2), "preset": at("preset", i), "colour": _hex6(at("colour", i)),
              "material": at("material", i)} for i, g in enumerate(grams) if g > 0]
    return items or None


def _gcode_tail_items(link: dict, path: str, opener) -> list[dict] | None:
    if path.lower().endswith((".bgcode", ".bgc")):
        return None  # Prusa binary G-code: its metadata is compressed; the slice plan is used instead
    with opener(link, path, {"Range": f"bytes=-{NET_TAIL}"}) as resp:
        tail = read_http_tail(resp)
    if tail is None or tail.startswith(b"GCDE"):
        return None
    return parse_gcode_tail(tail.decode("utf-8", "replace").splitlines())


def net_fetch_job(link: dict, job: dict, pid: str = "") -> list[dict] | None:
    """Grams per slot of a PrusaLink or OctoPrint print, from the end of its G-code file."""
    with _live_lock:
        path = (_live["printers"].get(pid) or {}).get("download") or ""
    if not path:
        file = str(job.get("file") or "")
        if link.get("kind") != "octoprint" or not file:
            return None
        path = "/downloads/files/local/" + file.lstrip("/")
    return _gcode_tail_items(link, path, _net_request)


def _moon_open(link: dict, path: str, headers: dict | None = None):
    req = urllib.request.Request(moon_base(link.get("ip")) + urllib.parse.quote(path, safe="/?&=%"),
                                 headers=dict(headers or {}))
    return urllib.request.urlopen(req, timeout=TIMEOUT)


def moon_items(meta: dict) -> list[dict] | None:
    """Grams per slot from Moonraker's file metadata (filament_weights, as OrcaSlicer's G-code states it)."""
    weights = meta.get("filament_weights")
    if not isinstance(weights, list):
        total = _pos_num(meta.get("filament_weight_total"))
        weights = [total] if total else []
    types = split_list(meta.get("filament_type") or "")
    colours = meta.get("filament_colors") if isinstance(meta.get("filament_colors"), list) else []
    names = split_list(meta.get("filament_name") or "")
    items = []
    for i, g in enumerate(weights):
        g = _pos_num(g)
        if g:
            items.append({"n": i + 1, "grams": round(g, 2), "preset": names[i] if i < len(names) else "",
                          "colour": _hex6(colours[i]) if i < len(colours) else "",
                          "material": types[i] if i < len(types) else ""})
    return items or None


def moon_fetch_job(link: dict, job: dict) -> list[dict] | None:
    """Grams per slot of a Klipper print: Moonraker's file metadata, else the end of the G-code."""
    file = str(job.get("file") or "").lstrip("/")
    if not file:
        return None
    base = moon_base(link.get("ip"))
    try:
        items = moon_items(_moon_get(base, "/server/files/metadata?filename=" + urllib.parse.quote(file)))
    except (urllib.error.HTTPError, ValueError):
        items = None
    return items or _gcode_tail_items(link, "/server/files/gcodes/" + file, _moon_open)


def _same_host(a: str, b: str) -> bool:
    ha, hb = urllib.parse.urlsplit(moon_base(a)).hostname, urllib.parse.urlsplit(moon_base(b)).hostname
    return bool(ha) and ha == hb


def slice_fill(slots: list[dict], host: str, spools: list[dict] | None = None) -> bool:
    """After a slice for a PrusaLink or OctoPrint printer, put the matching spool on each toolhead the
    plate uses: filament n goes on that printer's n-th toolhead. Only a single match is set (and moved
    off any other slot); several or none leave the toolhead as it is. Bambu printers are never touched:
    they report their own trays. Returns whether the saved printers changed. Runs off the UI thread."""
    used = [s for s in slots if s.get("grams", 0) > 0]
    if not used or not host or source() != "spoolman":
        return False
    saved = get_settings().get("printers")
    printers = parse_printers(saved.get(source())) if isinstance(saved, dict) else []
    printer = next((p for p in printers if p["type"] in NET_KINDS and p["slice_fill"] and p["ip"]
                    and _same_host(p["ip"], host)), None)
    if printer is None:
        return False
    tools = [u for u in printer["units"] if u["kind"] == "tool"]
    if max(s["n"] for s in used) > len(tools):
        log.info("Slice uses filament %d but %s has %d toolheads; not filling them",
                 max(s["n"] for s in used), printer["name"], len(tools))
        return False
    if spools is None:
        url = current_origin()[0]
        spools = (plate_spools(url) if url and url != BAMBU_KEY else None) or []
    changed = False
    for slot in used:
        found = match_spools({"vendor": "", "sub_type": "", **slot}, spools)
        if len(found) != 1:
            if found:
                log.info("Filament %d matches %d spools; leaving %s T%d as it is", slot["n"], len(found),
                         printer["name"], slot["n"])
            continue
        spool_id = str(found[0]["id"])
        unit = tools[slot["n"] - 1]
        if unit["slots"][0] == spool_id:
            continue
        for other in printers:  # a spool sits in at most one slot
            for u in other["units"]:
                u["slots"] = [None if v == spool_id else v for v in u["slots"]]
        unit["slots"][0] = spool_id
        changed = True
        log.info("Slice: put spool %s on %s T%d", spool_id, printer["name"], slot["n"])
    if changed:
        save_printers(printers)
        _printers_rev["n"] += 1
    return changed


def slice_fill_ctx(ctx, slots: list[dict]) -> None:
    """slice_fill for the printer preset being sliced for, off the slicing thread."""
    try:
        host = moon_base(ctx.config_value("print_host")) or _ui_snap.get("host") or ""
    except Exception:
        host = _ui_snap.get("host") or ""
    if host and any(s.get("grams", 0) > 0 for s in slots):
        spawn(slice_fill, slots, host, name="spooler-slice-fill")


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
    except ValueError:
        _keep_unreadable(USAGE_FILE)
        data = {}
    except OSError:
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


_usage_seen: dict = {"prints": []}


def usage_state() -> dict:
    """The booking list for the page. Called on OrcaSlicer's UI thread, so it never waits: while a booking
    holds _usage_lock (it does so across Spoolman requests, which can take long when Spoolman is slow or
    offline) it answers with the list as last read, and the booking's own reply brings the new one."""
    enabled = source() == "spoolman"
    if _usage_lock.acquire(blocking=False):
        try:
            _usage_seen["prints"] = usage_load()["prints"]
        finally:
            _usage_lock.release()
    return {"enabled": enabled, "mode": usage_mode(), "prints": _usage_seen["prints"] if enabled else []}


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
    # Klipper lanes and network printers' toolheads name their Spoolman spool directly.
    if tray.get("spool_id") not in (None, ""):
        spool = _spool_by_id(tray["spool_id"], spools)
        if spool is not None and not spool.get("archived"):
            return spool
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
    # Printers found from a preset's host address ("auto-..." ids) are booked only when nothing else
    # does it: the Snapmaker U1's toolheads are booked by u1control, a Moonraker with its Spoolman
    # integration connected books its own use, and Anycubic printers have no job file to read. _moon_run
    # sets book_ok for a Klipper printer that is none of these; anything else would count twice.
    if str(dev_id).startswith("auto-") and not state.get("book_ok"):
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
                            "trays": _loaded(state), "pct": pct, "late": not new,
                            "ask": _link_kind(dev_id) in ASK_ONLY}
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
    """Support and purge share of each filament (1-based), from the plate G-code.

    A flush is only the bare "; FLUSH_START" / "; FLUSH_END" comment line. The same words also appear
    inside the printer's custom G-code templates that OrcaSlicer copies into the settings block
    (CONFIG_BLOCK, at the top or the end of the file); read as markers, they left the flush open and
    counted a whole single-colour print as purge. The settings block is skipped entirely."""
    tool, kind, flush, rel, last, config = 0, "model", False, False, 0.0, False
    sums: dict[int, list[float]] = {}
    for raw in lines:
        line = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
        if line.startswith(";"):
            low = line.lower()
            marker = low[1:].strip()
            if marker == "config_block_start":
                config = True
            elif marker == "config_block_end":
                config = False
            elif config:
                pass
            elif low.startswith((";type:", "; feature:")):
                name = low.split(":", 1)[1].strip()
                kind = ("support" if any(w in name for w in WASTE_SUPPORT)
                        else "purge" if any(w in name for w in WASTE_PURGE) else "model")
            elif marker == "flush_start":
                flush = True
            elif marker == "flush_end":
                flush = False
            continue
        if config:
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


def _link_kind(dev_id: str) -> str:
    """'bambu', 'moonraker', 'prusalink' or 'octoprint' for a live printer id."""
    link = (_local.get(dev_id) or {}).get("link") or {}
    return link.get("kind") or ("moonraker" if str(dev_id).startswith("auto-") else "bambu")


def _try_fetch(dev_id: str, job: dict) -> list[dict] | None:
    link = (_local.get(dev_id) or {}).get("link")
    if not link:
        return None
    try:
        if link.get("kind") in NET_KINDS:
            return net_fetch_job(link, job, dev_id)
        if link.get("kind") == "moonraker":
            return moon_fetch_job(link, job)
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
        spawn(_job_fetch, dev_id, data["id"])
    elif kind == "last":
        _store(lambda d: d["last"].__setitem__(dev_id, data))
    elif kind == "end":
        spawn(_end, dev_id, data)
    elif kind == "missed":
        spawn(_missed, dev_id, data)


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
    ask_only = bool(run.get("ask")) or (bool(dev_id) and _link_kind(dev_id) in ASK_ONLY)
    if usage_mode() == "auto" and run["result"] == "finished" and not late and not ask_only:
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
    spawn(work)


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
    except ValueError:
        _keep_unreadable(HISTORY_FILE)
        return []
    except OSError:
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
                          "Grams", "Cost", "Waste Support g", "Waste Purge g", "Calibration"])
            for e in hist:
                when = time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(e.get("time") or 0))
                cal = "yes" if is_calibration(e.get("name")) else ""
                for r in e["rows"]:
                    ws, wp = (None, None) if cal else (r.get("ws"), r.get("wp"))
                    out.writerow([csv_cell(c) for c in (
                        when, e.get("name") or "", e.get("printer") or "", e.get("result") or "",
                        "" if e.get("pct") is None else e["pct"], r["spool"], r.get("label") or "",
                        r.get("material") or "", r.get("colour") or "", r["grams"],
                        "" if r.get("cost") is None else r["cost"],
                        round(r["grams"] * ws, 2) if isinstance(ws, (int, float)) else "",
                        round(r["grams"] * wp, 2) if isinstance(wp, (int, float)) else "", cal)])
    except OSError as exc:
        log.exception("Could not write %s", path)
        return {"ok": False, "text": f"Could not write the export: {exc}"}
    open_url(folder.as_uri())
    return {"ok": True, "text": f"Saved {path}", "path": str(path)}


# OrcaSlicer's Calibration menu names its test prints after the test; so do the common hand-made towers.
CALIBRATION_NAME = re.compile(
    r"calib|flow[\s_-]*rate|pressure[\s_-]*advance|\bpa[\s_-]*(line|pattern|tower|test)\b|temp(erature)?[\s_-]*tower"
    r"|retraction[\s_-]*(test|tower)|max[\s_-]*volumetric|\bmvs\b|\bvfa\b|input[\s_-]*shap|junction[\s_-]*deviation"
    r"|cornering[\s_-]*test", re.I)


def is_calibration(name: object) -> bool:
    """A calibration test print (flow, pressure advance, temperature, retraction, max volumetric speed, VFA,
    input shaping), told from its print name. Its prime tower and flushes are part of the test, not waste."""
    return isinstance(name, str) and bool(CALIBRATION_NAME.search(name))


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
    ws = {"model": 0.0, "support": 0.0, "purge": 0.0, "calibration": 0.0, "cost": 0.0, "mcost": 0.0, "scost": 0.0,
          "pcost": 0.0, "ccost": 0.0, "prints": 0}
    worst = []
    for e in sel:
        if is_calibration(e.get("name")):
            # a whole calibration print is its own slice: never support/purge waste, never "most wasteful"
            ws["prints"] += 1
            ws["calibration"] += sum(r["grams"] for r in e["rows"])
            ws["ccost"] += sum(r["cost"] for r in e["rows"] if isinstance(r.get("cost"), (int, float)))
            continue
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
                         "pct": e.get("pct"), "rows": e["rows"], "cal": is_calibration(e.get("name"))} for e in reversed(sel)]}


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
    def cached():
        if _spool_cache["url"] == url and time.monotonic() - _spool_cache["time"] < CACHE_SECS:
            return _spool_cache["spools"]
        return None
    hit = cached()
    if hit is not None:
        return hit
    # One read at a time: after a slice the plate check, the slot sync and the page each want the list, and
    # without this each asked Spoolman for it. Whoever waited reuses the read that just finished.
    with _plate_read_lock:
        hit = cached()
        if hit is not None:
            return hit
        result = load_spools()
    return active_spools(result["spools"]) if result["ok"] else None


_plate_read_lock = threading.Lock()


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
        "wizard": bool(wizard), "log_path": str(LOG_FILE), "auto_keep_slots": auto_keep_on(),
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

        spawn(worker)

    def _bambu_sign_in(self, data, window):
        if data.get("action") == "sign_out":
            self._verified_bambu = False

        def worker():
            result = bambu_sign_in(data)
            if window.is_open():
                window.post({"type": "bambu_auth_result", **result})

        spawn(worker)

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
            save_auto_keep(data.get("auto_keep_slots"))
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

            spawn(worker)
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
            self._panel.post(live_message())
        elif msg_type == "printer_code":
            save_printer_code(data.get("id"), data.get("code"))
        elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
            spawn(lambda: self._panel.post({"type": "usage", "usage": usage_action(data)}), name="spooler-usage")
        elif msg_type == "stats":
            spawn(lambda: self._panel.post({"type": "stats", "stats": stats_data(data.get("period"))}), name="spooler-stats")
        elif msg_type == "stats_export":
            spawn(lambda: self._panel.post({"type": "stats_export", **export_history(data.get("period"))}), name="spooler-export")
        elif msg_type == "spool_detail":
            spawn(lambda: self._panel.post({"type": "spool_detail", "detail": spool_detail(data.get("id"))}), name="spooler-detail")
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
            try:
                result = fresh_spools(snapshot)
            except Exception as exc:  # never leave _refreshing set: the list would stop refreshing for good
                log.exception("Reading the spool list failed")
                result = {"ok": False, "error": f"Could not read the spool list: {exc}"}
            finally:
                self._refreshing = False
            if panel.is_open():
                panel.post({"type": "spools", "low_stock_grams": low_stock_grams,
                            "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                            "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            **spools_message_extras(result), **result})

        spawn(worker, name="spooler-refresh")

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
                    self.post_message(live_message())
                elif msg_type == "printer_code":
                    save_printer_code(data.get("id"), data.get("code"))
                elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
                    spawn(lambda: self.post_message({"type": "usage", "usage": usage_action(data)}))
                elif msg_type == "stats":
                    spawn(lambda: self.post_message({"type": "stats", "stats": stats_data(data.get("period"))}))
                elif msg_type == "stats_export":
                    spawn(lambda: self.post_message({"type": "stats_export", **export_history(data.get("period"))}))
                elif msg_type == "spool_detail":
                    spawn(lambda: self.post_message({"type": "spool_detail", "detail": spool_detail(data.get("id"))}))
                elif msg_type == "plate_recheck":
                    spawn(recheck)
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
                try:
                    result = fresh_spools(snapshot)
                except Exception as exc:  # never leave _refreshing set: the list would stop refreshing for good
                    log.exception("Reading the spool list failed")
                    result = {"ok": False, "error": f"Could not read the spool list: {exc}"}
                finally:
                    self._refreshing = False
                self.post_message({"type": "spools", "low_stock_grams": low_stock_grams,
                                   "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                                   "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            **spools_message_extras(result), **result})

            spawn(worker, name="spooler-refresh")

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
                "auto_keep_slots": auto_keep_on(),
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

            spawn(worker)

        def _bambu_sign_in(self, data, window):
            if data.get("action") == "sign_out":
                self._verified_bambu = False

            def worker():
                result = bambu_sign_in(data)
                if window.is_open():
                    window.post({"type": "bambu_auth_result", **result})

            spawn(worker)

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
                save_auto_keep(data.get("auto_keep_slots"))
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

                spawn(worker)
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
                        spawn(clear_plate)
                    return orca.ExecutionResult.success()
                if ctx.step != orca.slicing.Step.psGCodePostProcess:
                    return orca.ExecutionResult.success()
                enabled, margin = plate_settings()
                slots = plate_slots(ctx, parse_usage(read_tail(ctx.gcode_path)))
                usage_plan(slots)
                slice_fill_ctx(ctx, slots)
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


_keep: dict = {"run": None, "auto_off": False, "unloaded": False}
_keep_lock = threading.Lock()


def keep_context(snap: dict) -> tuple:
    """What a Keep Slots pass was planned for: printer address, printer preset, slot count, project.
    Not the snapshot's gen, which the pass's own selections advance."""
    return (snap.get("host"), snap.get("selected"), snap.get("slots"), snap.get("project"))


def stop_keep_slots() -> None:
    """Stop the running Keep Slots Synced (cancel, unload) and drop its marker."""
    with _keep_lock:
        run = _keep["run"]
        if run is None:
            return
        _keep["run"] = None
        run.wake.set()
        mark_keep_slots(False)


# What an error from begin_update could say if OrcaSlicer refused a slot change from a thread other
# than the Plugins > Run worker. OrcaSlicer 2.5 has no such check today, so the wording is a guess.
_WORKER_ONLY = re.compile(r"(?i)script worker|worker thread|ui thread|main thread|wrong thread|"
                          r"not (?:allowed|permitted|supported) (?:from|on|in) (?:this|a|the)")
AUTO_KEEP_REFUSED = (f"OrcaSlicer refused a filament slot change from {PLUGIN_NAME}'s background thread, so "
                     "keeping the slots synced automatically is off. Use Plugins > Run > "
                     f"{PLUGIN_NAME}: Keep Slots Synced instead.")


class KeepRun:
    """One Keep Slots Synced loop; _keep["run"] holds the one running. The Plugins > Run action
    (async) and the automatic thread drive the same passes and differ only in how they wait."""

    def __init__(self, names: set[str], synced: float, auto: bool = False):
        self.names, self.synced, self.seen, self.auto = names, synced, {}, auto
        self.wake = threading.Event()  # set when stopped: the automatic thread's wait ends at once

    def live(self) -> bool:
        # Checked after every read and before every selection: a cancel, an unload or a newer
        # run while this one waited on the network ends it before it touches a slot.
        return _keep["run"] is self

    def mark(self, printer: str) -> None:
        with _keep_lock:
            if self.live():  # never after a cancel or unload marked it stopped
                mark_keep_slots(True, printer)

    def step(self) -> bool:
        """One pass. False when the next one should start at once: the plan went stale."""
        snap = dict(_ui_snap)
        context = keep_context(snap)
        printer = label_for_target(snap.get("selected") or "")
        self.mark(printer)
        try:
            if time.monotonic() - self.synced > REFRESH_SECS:
                self.names, self.synced = sync_for(snap), time.monotonic()
                self.mark(printer)  # the sync can take seconds: keep the marker fresh
            trays = printer_trays(snap["host"])
            if not self.live():
                return True
            if keep_context(_ui_snap) != context:
                return False  # the printer, its slots or the project changed: plan again
            for slot, name in keep_plan(trays, snap["slots"], self.names, snap.get("current") or [],
                                        snap.get("gen", 0), self.seen):
                if not self.live() or keep_context(_ui_snap) != context:
                    break
                try:
                    orca.host.preset.filament.begin_update(slot, name).commit()
                    # The selection refreshed the snapshot before the slot changed, so it
                    # still shows the old preset: only a later snapshot may count.
                    self.seen[slot] = (self.seen[slot][0], _ui_snap.get("gen", 0))
                    if self.auto:
                        _report(f"Keep Slots Synced slot {slot}", None)
                except Exception as exc:
                    if not self.auto:
                        log.warning("Could not load %s into slot %d: %s", name, slot, exc)
                        continue
                    _report(f"Keep Slots Synced slot {slot}", f"could not load {name}: {exc}")
                    if _WORKER_ONLY.search(str(exc)):
                        self.refused()
                        return True
            _report("Keep Slots Synced", None)
        except Exception as exc:
            _report("Keep Slots Synced", str(exc))
        return True

    def refused(self) -> None:
        """OrcaSlicer won't take slot changes from this thread: stop for the session and say so."""
        _keep["auto_off"] = True
        stop_keep_slots()
        log.warning(AUTO_KEEP_REFUSED)
        push_notice("warning", AUTO_KEEP_REFUSED)

    def end(self) -> None:
        with _keep_lock:
            # Only this run's own marker: a newer run's stays, and a cancel already wrote its own.
            if _keep["run"] is self:
                _keep["run"] = None
                mark_keep_slots(False)

    def run_auto(self) -> None:
        """The automatic loop, on its own daemon thread. Idles while no printer with a host is selected."""
        try:
            while self.live():
                ready = _ui_snap.get("host") and _ui_snap.get("slots")
                if ready and not self.step():
                    continue
                if self.live():
                    self.wake.wait(MOON_POLL)
        finally:
            self.end()
            log.info("Stopped keeping the filament slots synced automatically")


def auto_keep_on() -> bool:
    return parse_flag(get_settings().get("auto_keep_slots"), default=False)


def save_auto_keep(value: object) -> None:
    """Save Settings > Keep slots synced automatically on its own, like the display flags, and apply it."""
    if isinstance(value, bool):
        save_settings({**get_settings(), "auto_keep_slots": value})
        auto_keep_check()


def auto_keep_check() -> None:
    """Start or stop the automatic Keep Slots Synced to match its setting. Never blocks: the loop runs
    on its own thread, and only once a snapshot of the presets exists. Never raises."""
    try:
        on = auto_keep_on()
        start = stop = None
        with _keep_lock:
            run = _keep["run"]
            if not on:
                _keep["auto_off"] = False  # so turning it on again starts it
                stop = run if run is not None and run.auto else None
            elif run is None and _ui_snap and not (_keep["auto_off"] or _keep["unloaded"]):
                start = _keep["run"] = KeepRun(set(), float("-inf"), auto=True)
        if stop is not None:
            stop_keep_slots()
        if start is not None:
            log.info("Keeping the filament slots synced automatically")
            spawn(start.run_auto, name="spooler-keep-slots")
    except Exception:
        log.exception("Could not start or stop keeping the slots synced automatically")


class SpoolerKeepSlots(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: keep the plate's filament slots on what each printer lane holds, until run
    again. Settings can also start the same loop by itself (auto_keep_slots); this action stops it."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Keep Slots Synced"

    async def execute(self):
        running = _keep["run"]
        if running is not None:
            _keep["auto_off"] = True  # stopped by hand: the setting doesn't start it again this session
            stop_keep_slots()
            if running.auto:
                return orca.ExecutionResult.success(
                    "Stopped keeping the filament slots synced automatically until OrcaSlicer restarts. "
                    "Run this again to keep them synced, or turn the setting off and on to restart it.")
            return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")
        try:
            names = sync_for(dict(_ui_snap))
        except Exception as exc:
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))
        run = KeepRun(names, time.monotonic())
        with _keep_lock:
            if _keep["run"] is not None:  # another run started while this one synced
                return orca.ExecutionResult.success("Keep Slots Synced is already running.")
            _keep["run"] = run
        try:
            while run.live():
                if run.step() and run.live():
                    await asyncio.sleep(MOON_POLL)
        finally:
            run.end()
        return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")

    def on_load(self):
        _keep["unloaded"] = False

    def on_unload(self):
        _keep["unloaded"] = True
        stop_keep_slots()

    def on_cancelled(self):
        """OrcaSlicer's cancel for a running action (Speed Dial or Plugins > Run)."""
        _keep["auto_off"] = True
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
UI_PAGE_SHA256 = "f12e72bf8e4ea07f7c5fd26db2fcd725224b06edd74523cd7b5391bb80f6429f"
UI_PAGE_BYTES = 880553
UI_PAGE_Z64 = (
    "eNq0vXtz20ayB/r/+RRmrosHWI8Yyclms6BhlK3YiRPHTizlqeiQEDmUEJMAA4B6hOR3v/3rnhdIOZu9VddVFoGZwTx7erp7+vGk"
    "N60m7d1SP7hqF/On//MEPw/meXmZfqTLj5Cg8yn9LHSbP5hc5XWj2/SjVTs7+Pwjm1zmC51+dF3om2VVtx89mFRlq0sqdlNM26t0"
    "qq+LiT7gF/WgKIu2yOcHzSSf6/QIlbRFO9dPT5ZVNdf1k4/l9X+eNJO6WLYP0Lv0o3y5nBeTvC2q8uPfm6r86EExTT9q5JuDi6pq"
    "P3o6Gj1/+/Z0NHrysXz69H8ePOjWsqimq7n+6OlsVU5Q1QMd6Xg915Sfvr34XU/awaTWeaujcjWfx8NZVUfILR9Uswd60FAf2mis"
    "xnHcnpXn6dGw1u2qpmrSp5pG9qDdXuc11bXeqjI9O1d1GsXpU3or+KF3pPIUZQeYyeNqqp+10WGcpunR0VG/30k+kuTDfj/qpD+O"
    "nx49frzZ7CQ++fe/YlVJ5U2b123zU9FeReOq/GE5pQEl41g1dox50xSXpZqkkVYtOshjTPWgKKf69u0sauNh+fSAu4QxT2g+1FG8"
    "VXNbw7Ku2gpzOrjKm7c35Xd1tdR1e6dWts75gBZ4zi9qmj6r6/xuUDT8q2bo5y1NPQ1xfFZxlQ++zZfnY7W8L+tEt5S1uC/rCxob"
    "5V0hD/3BOlG2XeCxutzJadq6KC/HarSbfre4qOZjdb2TLu2M+/1eT6s7ZEbX1IfN5or+xv0+/QzaK12aRwLRyVWsLvYnqq1OuGl1"
    "i0ouzPTE6sQOa9DwTH+uDo5idXzfYKVOGq7WyL6kbFqiHpV4k7+hLuqzw3O8HdDzePxoid36qmxpEY4Yymgx6EMC4Pf6TtV6hv8j"
    "gnH+RVpV/lgSRD3XlKi/rVZla5P4RU+7JQS0bJq87RYpF2E15lVPCRxLHsRf7D7ZXFFJ60G7bbOJeNNRbhwTLNY6/fjgt5uPL9VN"
    "WtI+BuTXejnPaQ5rrWQn8IwexTT5PywJQI/zRkf0tSro49+eR2fPDn49j6mK070qCq3GBw+Pxvj2dXXjvlW5dmWxA3kHd+t/5Bum"
    "PemKZ7QZH65zoJztOBljQ2q7W3pm/EUjO2bCOYPBgLenQ0Pp4bB8ogdzXV62V8Py0aNY05REXI52p1SnSsI7vSN8aGqd6llRartH"
    "ucyakPSsuFzV+cVcJ71DpcvVQpu3I3VTFy0/1+o6n690Um6pgVW4YgxdL+dVTvBl1+pB0RAkEvrIdNJu1TQsD2jN3qwWF7qmp4TK"
    "3f/RTCtC1UCXM73ZpGYrXs6ri3x+elU0T8arceZfE1Og0fMZZ+HBJt4QQqtuOFkek051QVXJejt0p8ILnArFLJpii5vuI//Dy8CF"
    "6hSrQbj+MqrjbERgGCcv6M+Qqipi+zUfFAUdIPo8LejP1sxCu6Vil4xagGBie7TwkUIH7MfDKOud/V90/o/fYoDsFSUl0dn/nT+K"
    "P1aX9PJRlCVn//fRb7+db377jdLjf3y0+V9O+98g7X/lYfPbx7/9g37/kf32j98+/vjSD34UnIk0aNsNtzEu7d4KTpmP/zGOs/E4"
    "ARLjM3JBTzTgF/nkCrCPyTSV4piRMlcENqWZxKd01mB7EwIbEJZcRPF5Wp4d2Zd4u41Vu3V9/MJ3cTwemnmL21QP9byhCTZL958X"
    "jCqiJSPwRfOP0vrR+ME43tpKrjuVYN00bzgpXHJhO0Gt6arv5LU2YNTTdjGB14ZU2XoypzM4aVXT3s2xuajnth46aS5pM8i5j2LU"
    "yZYQSckp/EH6AjhQCWjcMUovWr1oJrTBFR0r1c2MGiLKR+tSTYsGO3lZTKh+XZTmwabXelG1WNq7i3zyXtFoF2VFe75g1F40i3yp"
    "ykoIJxXk4IumKOeEWAgV59OqnN/RbLjRX/DoZVB0dBLBgpNs7KfnVguy4imya0OnV2sezZz1joayVL1DtwELWk9ascIvaUFLWqen"
    "VOVZca5a/Cnd0tS+0ZNuo03xp+Ym8bDboNAss7pa0PzTri71zYMfirL9nDOi2vbTdatlKlFAS6cHRy4jp/7mT+wHw5w6C7AoznIC"
    "Jep0q2p6pF7Fa53mwwuaz/fABvrJoe8UcEV6ZLBF79CP6diNSfqNrUbdZSqOKqk3m4LOzjpdSvoSo0GiQzGYyszNTIK2ZpE5Oogq"
    "aECbuOUJ09t4b63skGvZLWtZrl0ykZAiUcLtfiqjStoB+WbTo1/88KLWWNSap8g2ZfGmUFVCKZnnNtiFN9qeifG6pPPkDMv4LYBa"
    "fs+x2meFygnhcOvoFGPhnJ9aN03F4FK30g5t0pzfWiarhsWgQRZO7pwfW0XIDWOv0trMqzvt6DimHGwPKmye6cPK9/m0A6Voz476"
    "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"
    "Ry6Y/1M/UHbxC/S46vTFlDTdGOgwGPN5KzjVITJek/mJTVKQy8TNcD+MRip6Bru9cEiLdxyAI+AAHAeV2Bfj8MfzmvAY17bmQX6S"
    "nj1XAfvzuoToOR8eMU1yEq5Op4AELK6+SB4j7S+qUQc0XJoIugYy9ui81NXHYv8zne0nUYiQjn0M1kDS7yEN1mk89Fi8L25MBzi0"
    "bHwu+0zTqTfFBDmJspi8PHJoUxBNMKj8uz7fe+5w9NcDjMIeeqoYHvIkkT1Ugtyp4CGnFb9pdlg5VIgI1t1iru3twhzXul19r1EX"
    "Iici2Oqm2+aAz5BphF+nu0TJMBwd16yKPlA3bxZyhObOB90et+OfedLYEfBanu8crQaDY6mQXu3BOIaJ+BbXHt4NxJjsMEvNSHI+"
    "xVUfxHidhngqPqP/sjxyvrQbfxEG+Y4bLtQ0qttnE1C/lXfjjWayEba+3DbNGHSTf2lvYe746+yLASUa0OcGvEt/m32RbODbdCP5"
    "Qt5LEC26ptVVbaXGbCTBrBKxfhInzTwYtyjwusxB8wI5Wuc7cjPcmHVmgTYK9tmw2CfbtR0283zUtCKEaHP8k2YreMqh3YM3TeWy"
    "2B58aLL/ZwuPbNGhRz23gncv6R4tIrMHfVlR/dZBsHW3NT8dtTOCQuqej+gm0JHmWoOT6DRLE2LGfSTYEJZpOMIl4n7q4y5zFmbD"
    "Pl2dhm7NMAa4HL8FfUp1ABR5OupcfJiMk7zTPymKaefLL8/Oztpnt9ppNvpye3Nz80tI0g+Yb29vBsKV4ddpHJ09SD90+psgj2zj"
    "f3ilczzu8IXVeYBnsNCyd30Eue4HF8NO/9nWVvv+3ftfNW63b8OfW3tb2+3tu9t34Xnrq7v3bjfg+atbX902z7fam7c2b5n0t9q3"
    "tm9tw/NXkG27oZ7vtLdvfXXrnk5/p33n1ub2vaf32nfubt6509jafKo+bXFZuqgtLksXtUVlmaq3qCxqKjUNnu9ROmm6fpauSfqn"
    "d+kR8m9y/rvtu9ylTS5fPd+Xrqj097mrT0tD9Sc1ugIbSBH6+wHFw43yrwZbd/rzgwOLWD/oWKPqhIdclXVoKiuMIuOdUIzCPw+/"
    "aP65Df+2eioQIawPQkyZfhDolD4tvP1Rt/kOlsOBhNin0LwJQqlk824BPANhf9KsCZ8oGdRVOrfKWq343QtcgAfdQp+3ITyFKSvG"
    "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"
    "6RfFHes0tqYfGnmKEZ98WdkcUKnR1eclD79rn/+m5Xv9YZEuzklXVMY5MRms63RyCjjGQ+sEIjNDYRdlUreHwILxx29agZORRmDN"
    "PKLbXiZrOiuIdC9X7YcNRgVYmnGxQYgz1lqEnDZ2eMhZcDBpRuHUKQyePRI933hXh+/WSlZrVRiHP+MG+hVvZEgCVlZF3UvzQL1Z"
    "MyvGrWrmjZrcnSQtmqasUwS/hu2tVSq/lMxU2VpQ58IGH6Xwe1LNtL0oU5qMz2vMSDwpmKqNqar6jyzeDeGkIA9mhWO/KSXA2I/2"
    "Z5r/zWWtM69oaToksMgCdVLlCjV9WTAy5h1xFKvqU7zUFo8poGGZc8soLu1apxMeF45RQ28T1//8YXfz+s7nqG6hBYEHps6E4OPk"
    "kLaGmVtfPtSOLbTGHYlLNc5T7LqEDTlWpQdv4Yvo0kN7a1S30LAi+9to9QmDtDUTZn35sKg1a06Yr3GeYtedMMix+ghefcLWqE7x"
    "eHtkQKxUYWRRhIN9cDZJ6ppb4i1rSzWVEo/Hs3hYHU0TP9af4zNtDt4tUW/hrc4JCr2L7KmunEnJryKoSgE14mq9LM356syz3q5V"
    "wuku6Runv0rnVAlr904yLu7eMTowbpzyDW5n51VypLdsytam8KqcyiMblqR7nUFIqeYr2atKSkS10sowKHmUr4DXVc1f6wbDd5Ja"
    "NhiLWMwW9EWnaosSUktXSl1ZxlkY5yURyTtRnK40OdXSlklcdomc1q8SVLfUVY7sZOdccma3cJVYmVdeIMvP/Ep9uCR/M/VcmsNV"
    "irhEJ1fgcvVdXZXfmeouz/GqZVyit6twPau7dfyvpN96q1rEj2qWpTfzkkW6wtmzFL7w8Hnx0Kusq4/4kqNrp+2XXUBSx+WXj1vA"
    "2p1baen4u7jywpGqrrBsSiWs3cvVlox08xILRqq5zHKpZl2yWJY5S4hcW+8tsXCoOd/KA7zQ0cK095Krg0q/9NKwc6/XoVUWha9b"
    "q64IquTyy8HJvl7PVloI1LX1VwFVcIklUM63hP6Xee5woQtcdxaOLedbeVAXev2Y9l6S/qn0S9O/nXu9Dq1C/75urUr/VMnl6d/J"
    "vl7PVqJ/6tr69E8VXIL+y/mW0D+6IywfYkx1mbHlfCsPKiVfPJqY5JL0T6Vfmv7t3Ot1aBX693VrVfqnSi5P/0729Xq2Ev1T19an"
    "f6rgEvRfzreE/pe7UXKxC/0oF46vyrny0C5xwrTbfcmVIDVcei24+dft2Crrwd+9VVeEVHT5NVEqYN0errQupIvrrwyp5BJro5pz"
    "yepYxdeXi17i7LtwtE3elQd6qa+w2/5LrhNdy6VXSrmE9Tu4ymqp6+aq60VXdvkVUyli/Z6utGp0V9dfN7qiS6wcX94la0caMqwZ"
    "fq8HiO0E49SvClvqa7RC1sUDrJJfcslUalu+dH6V3V116VSqW2EJ/So6vOToYWlDL3OQ4Ml86cZelT7XOWz47zQOaxPuWicRv8aR"
    "qJr7lzd1bfN9Jeslm3llsl3ZxP/fo//rk+vq9v9f2QiUTe1L27im9dzNd5nWXZU4V7Sw/6r7vDZBrmp+/9X0umzyXtq6Na3Ybr7L"
    "tO6qdLiipftX3ee16XBVM/ivptdl0/PS1q1pTXbzXaZ1V6XDFS3Ov+o+r02Hq5qjfzW9rpqAl7ZvbZtuOefl2nhVelzZ7vvfoO9r"
    "0+XqRuFfVe99JtilrbyERbWa97ItvSqVrmF1/W8zBmtT6zom2V/dKEzHYbyeiEk5LmX0ooyXauCVLZxU9RXtm7+Cfq9v6qS6r2ro"
    "/Cl7jpESL2939yaptggrWdHoSpEbL0duTi2rE9vP04dVScepZg3C+Wl6sbrX/WcmllWNnDWNvAoFXcbc/Qt2bS3CupQF+2fo3EI/"
    "9M9NWisZJb0NvBJZrW2O/oU6tR5BrW9j/qm7tcBP+zNT0go2xWrTrkJDa1qNf/a+rEU661qDf9LeLHBu/sxEs4IBsNq0qxDNmibe"
    "/5+7d1ts20gWRd/XV0gejzYQgTQpybYMmeZ2FHviGd9WHGcy0dIWIBKSMKYABoQkKxK/67yfLzt16SvQAEnZSc6eSSYi+lpdXV1d"
    "XV1d9YePZSWiWVV1+7uOpsUi+CsTzRLaujpoX0I0K+pj//CxrEQ0q+pZf9fRtJrRfmWyWUqR5gLvS0hnZdXpnzKilQhodYXo7zym"
    "BdamX5mMltRuuUH8ElK6g37zTxvXSgR1F53l7z6ymi7yd9QFLamZ+jp6SKPL30kt9HWGs5qOaFXV4tce0CTNPv3u1IKdLAHHKoTx"
    "lYFbxuq8GcRmTz44D51xMsrZqV64hj4yClTsrtBJK0V9ZUS4jdIj7Q/0ajnvvlf/Sd59r2zvvj/Wvfu++AO9+74wvPt+5/Tue7XA"
    "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"
    "+BU/75Mc5a+3FD3J7KP7o+9DwB2+C1r4pib7HpLhvwZS+CVg3Ef8tqc9ND9JweMI3fIRL+x16uET2tZXIvcNCNdnuGPd8gof9noW"
    "72V31qdCv4fy9hE67U3Aty+A0744jfeKhrZZ4OVz0DP/81+fQrd6+R5M2Cui1zNI2PMGo+9hc30LwfVxk/PrBudXaK6Pm+A+Tun4"
    "n6Z03urhx676r7jxE9LJNxvqP8M6+fwU/9Mp6edD0Z/wt542Huaf4ey8gus8n4P9tI/pi+NIzxm+BNj5dMr8M0id122rLze1PWTZ"
    "/yTXHxn90+d/hrrzm/hYbyFtvQGI9fuRcL6LlfX/L7yoF3/lN+GinmlesN6ent/eyvk1976M+qfDBt3y3VOKD555QwCekj/y/9ds"
    "+eYhgk+Tee/eatLHl2+X+vlm6lf0jW+Y7ksn8RtR++rEdv5y5OJZtb/W9caG9Y8V/OVrLJIvTxfkLyc/vvm4L2FjPv+u3wLa+PYD"
    "Xuvv397c/19d/2d7cp/2zfrL89/85W+1vPt1WF730dbLU6jdbxHZc6M+9NGH37HpfLNgW5bPe/NDPeZ/fGy/3d4VL+/gN96Nn6r6"
    "LDV6MzX5rFnNH5/BMX9932ypfVg/aci62BLKrxOyLxNeW9Ftr9Lvv/rPT7VtPdL8sRrLLXV6M/X+G18fLD+v//mj+uMvr5tfraau"
    "C357mW8VvsxeR08/f/rlMSP62abYx1rFY4ni5//4bI6kepoo+vCXHx8TeI9sf9kcibR63KjwDthlf3p+v5lR5N1PH/6v/+1/f9x3"
    "tZXwuORjXw3Fn/iNCx9QS7vNhduCgo8Xzb8+vOxz/1OxaaOP6vWXh+f6PDv8oYyj/PHZ75783q2IR9GPUn+M/zsco+8+bt4d3uev"
    "m3dfjXO/PI5/vLT79eFPTZd/uhDsq+NjjwMjmz5qPmy88v74I/Ojnr3bCvs84wOl6K2S3r0DPvzwf/4fP3wAHvl22buPffNKnnZ+"
    "2b+HnwjTV9Lq0/uw7ofH6aYn3bo1Idqa/zj78pGge7jhz87+X5gf208tq2rz4Y69++mL1O7JRfsl/Un1h+xPT2vOX5b1dMMe/O79"
    "F4l/eK7gMZn1kjrH8a1/SX7juN35x4/f/WWW/wF/2crHZndne/HUzs879olaiZPNFXmrqU+v3z019aujbc+H/Z+Fc5PYp7EbHvgh"
    "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"
    "kjqwrBZOJ/1t14GFtVu1DqY94Gy4AmvE4ijdYS5WbTZk+UNc5/Vqixd0t43rHg4udUxDQ62SSrewoUZJlae/9SF/b4tynqjXFWlq"
    "ti0LHwKXaHjIrfBrrY3L2+u2ibnUaP3CaqjVG5q8BQybxTQhdDWqXV3oQrlDE7oaDUPoanstQ+hqYVoTujzuUgldHa8rhK4GC111"
    "U+ZqNE2Zi1dsJnOxdJLJXJ22KXQJKUkKXZ2WKXQ1a6bQVe+aQpcUqqTQJaV4KXR1aqbQVe+YQle7ZQpd7Y5V6Go0G2KB10noatMG"
    "AkIXwFnD+SDh0GyC+RB88JhX4J4J6SqdpjrAjkgYqkou0e22SAjrVD3sEnY2Pu60GZMeSG18/PFEmmW5JiEeu22wLNdhTNRrQoZr"
    "8UgbbZbhgA5ZRiNZoUOCP+DXIxkKZrXFiG816rQNtruEyDp0RCKZmJhmrUkyGZBXjee5XieZrNVA6Bsei2CdKjXfaFcbCC3grUOi"
    "OwCDxWvVNq4WIkYSyao0fyAEdEj0aXTadaRSIH/AO4hkMMoaUjHCiyJZHecBBZRGF7dZILYqru56pwUiD6wnOBZ1DyU3oFUOCwxX"
    "fdtjJlAneQeTxCPoVG/wjo+vm0TlLRT5kN+DyNfy8ATSxuVJ9bvNLu2MXhUlRlprsM13cK3XGtAdyLt1HD7sz4A1kLe8Ds1li8gb"
    "JDMQQTENxE/D67QaTSwPsk2V8htw+sQ0rNUmSXJVElq60G2NxLmG12Txptomea5VF9JPo8HyHB91Mnmu2TTkuRoLFEKeQ+akCXQN"
    "U5xr1ZU4JxgRy3RA2526yqvhJJBk1/WQAutAU8ghcXKqsEnipCMtwGTC0Rslg0YTJcI6EEcThZF2t0qnxTqMDjoGEmGw6MDegjmo"
    "MuOqeVWUbqB2DfdoqE3Ceh35WYcoonaYm0KUahh0TZ/TYH2Ox+ocoGoU6T0+DMMKNpU5DVOZ0+DjQksctZs5XU4jO23QSb0ulDms"
    "zcE+DW1OIzvMkCKgLQ47XaEoaJvKnJqXnZVIz9A2lTk5XY46igm1RT2nyunmVDkdcdITWpF2LafK6eRUOZ01qpyOqcoRvIx6ZSqq"
    "qgYySYoBYIYt1C4NpuxqSwAk5HyvKsYjtgcGX+h4iMsjrnjzqjfqApddzm/V61S84RFXb1RrrMPxuHMgSAK72RGHjBo33xQiJzA9"
    "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"
    "3Cq1T+4muE/uKLub9d2TGA98d/G9sDwerI9lqLsOlvOQ3BHLMM5dsOyovhLLVv3lP7jdMUybiySO4WgUmV1Db0HpUDHc/zTN0PJE"
    "b/vJGshfQ5+0TYPdDHb6ZBZP0ZTsLx44tyy+beY//Qdq+z5oqv2G5fxkw9oPZ92fsZ/nKpv8gbO0+lDG4ZY/sS+T0VOXvIjlnqOr"
    "f/9Bbr/MGL8nmzn8jSAi8rARf3L3ILf6Rhu8M1BtxgHGuVmeLv0OPq7JEWzbZ8dL23HmwLcuBtjJ0xZGs/CHoxa3rT4P0lDDS9tn"
    "pte0+dO1T0vXXGhBxTvRNEiumzzJmJ+EICVOx9dN5pMlisVNxEZ9qbIOsyrMaVnWYI/3CeI3PV6FJeVyVaHcx7zWCa/GMu2duqqz"
    "IBusOqtm1cI1/Uk+dl81vKy5otKSm6YnI0TcBd6p5dIeL0wqbOKzM/8hs4e84buGCpfLpYrkMxjh7nrwzw5C8HgYjmdhkpYqPBPb"
    "AxEuYTASoeE/XE868RhplXfRfvTI+FSNsjAJsjhB0qSS9oG+k81Ub+Gy6fgYWn2aw6GjBkwomXdplBarA+Ub4jdyhizGLg4EDE05"
    "oE9z1mIAjUTGNH59m7UuRuXM8yKMj8HTLcJygJrwDqg2TDKWYk0Qrx/Skz1xVdvFm+bBXP59mUQZ/730mujL24ImaviLkeJv1wgK"
    "ejDRTbpCPkCjYTNrZpvttpbxjSZASfFoahutdkxQt29uNkIRoCOklNJTDK1i4Pbb9hxDkgM/PeHIy+J3STSJ8GrjFDrjKR4ZjElr"
    "iu5MY5a2j42YaCOK0ZL9bIgh1T7CUK8wLEK5/c9/ah2XJvM0K/HKQWkmy5l7QlvepRNf5Bg5YHuD73QPVxFh6kiO4+Q2wxHs2SFe"
    "eB1mWZLiDXo4wfytJ+3uEO9X236bXer67c54nrRPoT5OprlwMPamjOfA0AJ7cxJmwxgGWgzC7N3HYx4mI0/WZWK9eLTBGsJGxPTi"
    "UVP8gun4CzLwX8HIQpGkr+KMkre9VCr+Wi4pNvkLmosxLEbRMapifF78WzBXQXdUyBjwwYY+JBuJB97Cn84DsOBDFUk/pGtPzF3s"
    "sc6sQp+1xhUpy/WAhcUpvaabVH1GemW+ZiHN/jksXF5g8Kf7egtaXRwTqAoInj6hUe01npBelfXiMU+rm5uMEfqUQYPSBAZqhFXG"
    "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"
    "sHj2j/8fa7KrVw=="
)
# --- END GENERATED UI ---
