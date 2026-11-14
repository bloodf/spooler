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
UI_PAGE_SHA256 = "1b22e464c5b3a4b0f283d4b2ec6d08b6c3c5428615cef586dd79ffb59f43f614"
UI_PAGE_BYTES = 834646
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
    "EvHQcHPa1fSUsywZYeUyazdnBuLrbU7sKrs5U5/Mm3cnti7fncclu5MKjubaejIX7jkP52RDnc3LgtrXhUpjllfq0ok/OlwsV7uZ"
    "KGoycJr8hJTw2G76zTQq5M1BZIjfPILaR/XctOrM9Lrx08SYNeHRglWuL/b9PO3Lv//rq1fPnvpYlb5DbY6GcTbfeHR5zWNL3U9P"
    "QFFpSI+VWHC2/FmV1HHUEG7iix5dCL2XaqXsIKlwKlNX+Zfw4yT/EWt1PiWXjqCsTSA5hiX178Xx4px2gC+/F8os6AQ/172Nw+Dd"
    "blodpVm2NuYUK/+8mIeyHiaKVR5EE1kDfhcrPA+O6WucrCUyyqv+usxU/HVZNmQSxv6AfgOZLoOJmvMSIygrIEEJ64J9i1FRU/Wd"
    "E79iIHOD9c1/YwFLfKSsGi16OKGKeLOmgKqKI0UV53VQoP5zZSjkclQAwaGsG/8hPuzGfvkJROl4Fd2z4et6fxxcuXOFiErOe0nj"
    "eRS9nobn7eJodX0SvTXtMcVONQ4Y+RV7LN31CuFd58VpNnsUDpjd/mAWYt7LKWhn0bG03UfP6TiKnzwJ/u5jpAKlYCykNPtwxwQS"
    "qlqjwpYBCqw+4fK1AYpdNldO3p95rsJi/tLzFZuz+XwFwVTZ6xkspkIGRRI/raVIr+Rugc+O5CeqKmwETuR1A0iwqwcAHaak/wLJ"
    "VspEJb5nO40VKrtIt3jOF+bTsbyRkt1xmojMyjKKBLMbKo9nQtk6WWB1efCbiMtsF3T5GtVt0BZA3svjCXYAxVa7BImvVyraViNx"
    "nKRnZjmdFJv6ty6yLW9NJ+tDwPYhL2DHUqgTgfaK7jphBqst+qEwyMXOSN8pmQibR7AihYiBH1jWRyWpnD+IjOdBHMzpjhVvWEVn"
    "AXpQE2re6CJryUgVksV2FUqsVDElHGXfkHmr6SQ1atiItGSjDBnKGjtWapkKe4/pbahIK+152ZijX5QpK6LfVDf5TdFljpvczM5N"
    "lkuNXhlSKJhcalNC0f94Nk+u8YEsW4YS7IyZl1dJwMowqAPXHeGVtMA9UXH8lh6IvW18IBYaXNsfldnyOreCGYz8PIIbvQ/a6mGZ"
    "xo97oRLHYEowgULEQt9GU5V+rcGu4/Y3GZUIkJYejjU4livpE0x/2mNg1Qqz5V7xW1dFGGAw2g4HzhqNzH2fxveF/IEffAj/QNql"
    "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"
    "B4838YMXWX7w4uvwg09/G37wNMMPlgF6x7iYDPwnruF1rX6/ZVlGp+96e67R83pWj6VtpwVpy+l2Kd1zO5Duup0+S7t2F+p3ep7N"
    "0pbZg/KO1etRf263Y0Pa7Xo29eeafeuxafQ6Tt/rtHpGF8Zz9kyj6zlWt4cZrte3WpBhOz2zCxkdr9fBjI5nmn0bM6yO3YEmHafr"
    "9jzIcF0bgIcME/q0IMPpwvCUYds2Zti9Xs+CJm4f4Ia01cfpYIWu1cFBLNPrUwuna7qYYTqm6eIg3U7f6bS6Rr9jWQSX5TgAaNfw"
    "PEz13B70CCnbNj2o34OxAYau0eu6Fg7hmX0s79lmv4PJvuk6Xcjo9jsEUr9n9nsOZvRwZHRFBmuB6a4DGLIMy+l3qUGv63T2LMO2"
    "HYvqe56H9R3TpnIYAZfMcHq2Telur29Dfde1PEx7MFMsd/t9Ar9HrTuu5Vpsev3eY0kIpmF3TOexZRtdB6rbiDlYJ0j3XNfFtA0r"
    "14K01/X6kAYgcXTb6PcdG8tNIJQ9yzEsq0f1LQ9mCWnbcR1M93BcSDs2oMs2Op2eSfVdq4P9dWEAD8sBv1i/1+lCv5juOx6kvR5g"
    "Det3LCBQxzBNx+pQOaAF0pbdZ9XtntXCUXtd73EHZtWRZLgHSVh/T5Jpx7BcWBRJxh3D7HmmJckc0hYMo2wDICNP2SWZXfRHqVgt"
    "yNAnUoZ+YjL0vipDz+JF9OPiPKqRpK9VSfoTk52/sT+/sj8/ZyTpz/8NkvTX5pL0l29Mkv5SJUl/+2qS9KdNkvSXrCT95etI0vd/"
    "G0n6ukqSguAAfuciAwUBtwd81QJGyZMoRjwQNJQEyQU82rKRa0HS6fWhNsgO5IrAffs9ZNIdu4diF9IO8XC345pU3wLp8phkA4lb"
    "z+1bwA1BajkgM12UqqYL0gbGRAHooqBDWQJcEhiUazhWv+NhfRsGgLTloAyB/sxuH7kplAKXBVkDMqwLaRDebm8PZQuIA0h3+90O"
    "9tfpOCayV+D9LrBbEA4mKzddE2VPHwUvpDt9s4tSwbJwHlDuOh6m7W7HcyHdA/7qPhbI84DpO333MTDSXrcvivcg2bc86h6ERR+F"
    "DYhOGh1nDUmAEnl/F3i/hbLKBfzRaB0Q4SjLkD07KClRFqEs62N9z3VsD+ujUMHZA1Q2yTJQMBA7tueyNKwmYs/s4OwcBBfLXc/q"
    "snLPRWR3WcoDLOLaWD2aG+gvnkNr59j2Xg+1lT5bW8tGTcgFyUiEAzjDNCxJh8od28H6tt1HYQNplLigstiuyykL2mUJr6HsuS9l"
    "z3sme/4tZc/LEJ2k14id31Wxc4sJmv+wP3+wP28yYufNf4PY+aO52AnPvi2xw+dTFDv/+Wpi59YmsYMwKvU5yF9a7CRnfxex83uZ"
    "2GHnNPHpDN8Qh2dhtJjgrY3xbLos5KKIstGSMG1UU8Fy6OwBf+x2SakFiwL5FbB0i5ira6FlYIJh0xXpPbQjLLcvy3uo6zqkBHte"
    "B3m3Y7vI50A4eMBVPWCqJsosEB6gevdR8JlU3eyAmdKH4Rw0HNACZAZHH3m+hTLHtYjJAv+jNKnikO57lO7bLin8Vo+y+x0wXNG+"
    "IGgcFH3MvABjynJB8pnUyjVBYFouWRo9sMiUIjANOkrLrsOyRcc9Uv3TcQFMS4UL4HVVuPtoJmI9C+xATPf7HhuGWSYiDRCRISPS"
    "0Jz6Ee1JYRDdE3o6jxm6eoQ+FF2ITYeQ2+s5HNcOrIXX7fdsthYAPK1Nx95ja9Vja4eLQWvpko1oWX0lDWvf6e6JNNCG3fc4paCa"
    "0AVB3OeEhEZZt9fpQfcoojqoDnS9TtcFsEB690kdAX0F4BE0AvY40EifZJsL+SYshd01ETQYGuxDr7UD4hJUEIsI0+06aIFbYMh6"
    "XaTbnuditw6sJNmMACwa5SD9HVBjUHtwkJbwr4PGORR0+x6r6fSoJYxPCknPsxzWNwh5Nphp7bHhmb1tgu7iMRhhHiSiAWzXYtPo"
    "AC0J/OJEwe7ssZkDBggTfabodV0CVd2CfzwBOu10QEMDRFsdPH+xXBeFP1qzXWaI2qjiGKi5KJuSpRGBfdpFvNwD+9UhBQ4UzB6t"
    "AKhIaIZ3LVSkAAyLNCMwnk3SMTzLw1n3HDw7EGkYxgSDeC9N9zugqGJ5Bw3fHtK+RzqJaQIaPSCIfs/bg+E8tOr7iBio50G/QKZU"
    "r+fg6QrQBdOKXSBy1JI94jmm0WOHE4CFDukyXt+l6YOCS3CB3ofHTaAmO9S+g5sR9gxXpUzAK87SBsLH7dDv9lxUQzu9HoFhd5B3"
    "gOplkgrl9SwTV8exkI4BDNCagdwN1Cc9mn4fNx+sMxIWgAGKJNJ1x/N6SJFW1+P9W16PwEB13jZgdj366+IpRHZxG6pm/5aqWXLG"
    "dIwzec8IdAS6jlP6eryk9GhZ9VqF7g9Q3fxrFVGi3JZcLvjLilYczgL8ip3ez+S+0gYtutVZegMTuyztLXi7WsxOE6W3ZLEctDri"
    "Uib+bx7Ex9NohwpAvxq3d6zWd602XQOFfvkl09bdlq1VXDIWE6I46sWL7nTLnQtu9YLzpx3yYC7zlElJFKkzHJB/yJ3xyTSDO1Bg"
    "w4TfXkW3HjG/S49XqwwGV90N1vKhMPBT/UihuJd91XHozli0SNrqvPhbk9IG5zE+IYmLbareQGVv9grc0Bq3qyGHxbe11p1WjgC2"
    "mlGKPq0aHsLgZ4dmgK5GjdxtX61qq+SuWCswVF0O5xebG9YWZN+wes1erGyt7sxm+JgdXwEfVXfOy/FRVbsCH1XVm+Ej2zqLj/yl"
    "c19Bjb/5grXg+LUXrPMXURVTPq41cMjxChg4xUuQzDKRl0zBQNl/0g6NW+QUVxdPYX3tgCRadCYkWswk2vQsc3M2e9aQf3+ZLa2W"
    "aIJcylAqyzhK8b0tmxV7Obv5GjtCsRWWldu6eAM3AJYS79GQRb8DzIdCesWUpbHyQeaCfFBvj5KTH7legZEdN79mYD/SzdST6WQS"
    "RmArJvEputuqXcqpXMqALeXibLgYw/gruaTPF3ESzHyBZhQK0eTVgr9K3ufPktlRyIF8nuy/XaA/swb+YSq9sswxyh651Ic6IpG/"
    "FsXzh7+M25p6o5o/L6l4ICyg4q+UxZzojng4O/IzqzQuXyWMiIJjjMrQy+504aX8qQBxxD0arWJWiOEDB5Ece125TuhvKVmgv6LB"
    "/bbvo2/K9Uqu25it2+xsmN9BZ9M4OQ1m7N4XXoUbo2+tf+AztGwJZ8hVWiG+cDvCCA2t4DRZsDxOioMWnqWN+RNQehOKjJI/D0XH"
    "nH+0Tc4cz/Fwg/kBgWY09I4Ykg8k3kWa/MUqyJcitDt0AT5KClBntU9i4ib7PQuPEpmYA4eX6qF8L4S5hUdEGZDl7Krggv06LkFm"
    "Q7AkSMsPYnAGjUjL8Xe412dAE2+7XJCzvR08HUpWg1rskQfqIpQrdAr4cQOMBQRl8Vg34M48WL3jo0oT42gW8skFs+kxnRLPAXwM"
    "8xjGrODPU4Ds6KNY9LSwfLATwM0npM1Z64fWRtrJAVLeJdvlrS0IEV26TccV/bUqUARMlHekbCNcyNaN6RzdwgbipbVKwJIAytaR"
    "GRBkxwlt3FRLsoq6iQAXzMda8il7N5prwDyeYwjh1bvND0jrGle8wqzA5U69plkxkKLyl6qc2zRTdc+m7WABQGCfnqlOK16zti8l"
    "G1dUJy6TpR+RUkcjbEXpVCLVkXisStaMDtFzrbD8ZerCZJ89lmLuY1Mxb0L3BNjPaeRknvMboU2EWIV9Qi4KygH1QcQA4YKagccn"
    "81foXRWEx+SRAiQHIAvlJMT9W1oBQItDRO6P1XUsqDQLPn2s8V7XwMEdW80fN1cUoYmqsc6pt6YPdI37kiRNVSWTVXpMUNX0lARv"
    "2YlIFfq4DlUDSxIuK1szxeZZNKvDLmoUCpWVqoeMfmdn9Vp9bpvU6fb62xDYa/iEojkXHD3Nzmh77r18CYrUAlulDpO4M5s9eqyT"
    "9Zk0Xi0LDpOo+VpTlcnJWaNHWZOzb+hR1iT7se/oTPE4N+TPjkAjXvGYqjznOEwUf0xsnJV401NXB7tBD/tgngoHtXLKaUDb0h5+"
    "DIF3TZcwTQJReaaFUXIiCt7E3+VF+MZKfAxW3svS+opvlMnQ2k2+z7/w2U3E4zDl9Q++3WXkc7EeqLm7yb/sEeCMAdyONDQApPNj"
    "dWZzbqhgUDiwPDbMcFX6/BhDSof6pqYAhTZQYSoHqPp98ybsR4B9LQ2frjw0E5NUXlSfnH29F9UnZ+k7t+Ozsnduk7P6d27HZ/Jm"
    "Am2ML/XODTr/q19UH0pFplKJOT0rHLTkXOMW9AGMr8SfUvEf7GRfOpn0UaSTIugfFA4X2AMv5oFxdX+RoE92LkXokHsQ8ogVSBsz"
    "+LOGX3jAXFqwxOB/ZQUANQH7KHo9Dc8pOlFVxwwpzxcrrIG2F2Sj1UUVJodFfYj5WMxnQ1WhPbAnYCzBtRNQNjDkH7NRyUMbugXl"
    "FoxIg2jkT8m4usiNLkpkQVUUPR5+jWUxlSuTxYU50wdNkeQKo0zvsbFytXiurDxdvcA1Zr5CKdoirjWqOuRxEOfEIBBP5FSonr1d"
    "hfGZyOPeFiGf+uHOe4vYLnEFW6iETnkF8rNuVdlSAIzcbWvGeytvkvpY5RnowVUo6EX/sdQtuomVUXzbLJIuz0BXjMzB6DQRLwTx"
    "NPsUz2PucYWrjSH5uHdiRdnPH69t6GOdUe3zjTMUk91yBULP2RFbw6HaHNs2rj5dxDs/j5TW28xIl0svyXNYzCK/xDpjdZnxb0jQ"
    "OZFyR7IpSNAsqgKcvRZ9kdkKYhJKn0PUwaUfC9G12tv/z917brmNNImC/+cpJJ2+PeRHVNFbdXUNvfeeuroiSIIkSBAgAdBKdc6+"
    "wz7M/t9H2SfZdAASjlWlVvcYzXxdRGaki4yMjIyMjKhYHvhqtKpw2trMCx7dZzCEYN6Cc4b2n41m7WloackEgsniqXYPhuYgem3m"
    "XjlxFb1S+wB0LAXMD23JVDih+AXxFdt8GApnHX00InQMNfcoeo6WDsEwx9aWLK8MyFHZTbdNrUi4Q1Mna14p6eqxN5Y29GmoPCT1"
    "N5ZEIXu1ddmT7GzUjEvy9ajBQxFCL4xCgjo4cEJnvJ9+QT+Fh88pI5vXMcNr3wayPEigkp+5Rxg84OpxOkH9+RCEAiP4g3vHEhfX"
    "UKZgpCd6kIzyJOkD3TPzJ8XwMx9IKYygZ9cAM2GOTwKdDzbUJzPRNIis4fE6SAVLDLzS12uL6ArBUPdkqIT7M7snm6Bkw22Axm3A"
    "EbeBr6mAHhH8jyePfX7ME0HEWDA2sI2un+idjnJawf1L9YkvzOrX9RFM/U+Sjj48imC/I84P+gy2AZmZcWv2xEtA1oB+yr89yQ7C"
    "3wlGdLuC/3yWnz0oogwA2Hk40DlmAf7jxbAwJQhTgtDp88qz9nyDylCF2cPk5SNs18vAVBRibQ+LL8F5YQ+OrNcn+74Fs8C45uTy"
    "y5wHKwOZR9A5XB/4YNGPHz9wsygB/vCmQKdB55gFWDTPqF/MXu/P3JtaeY6MlujeHVCfh38+puZe2CasXePAJlnv6cRctc0HLaqn"
    "b3DnxujHUraTR3vMIxwmOkRPdMhxokMaj4Crn1TIW7gF68Yt+HdxC0lfpR10rcct0NjhRSxgBpiJzMGvEzlMAB7x65aB+peXgei8"
    "DFRjGchwGRyf0KFRlfCdwxRyMpIA46MhP2DoYMx753jQiPIeFPTnT7gwngWPlgVp8F8mBgbXg8dUMui1QIBVlaIreFDQnz9h2d9/"
    "Fzym2u3FQQN0/fbKcQQ7MAQC9gCqxhO0fNLTrNV+ZsGwlkzAmxI8AWYJ6FqrZaGjA64ZGht/PMH2fMH3IcTnghBUO4UPWHsQ1G5D"
    "ie8voQQZasHKfYTu9zpSfI5I2WtI2UOXYRgtlDcTIhqA9Q7jQVtXj/3Yb2YQhHjrrLp+XAoSVPr5PeqPH9A/GaPS+zd07qT5jdFk"
    "T8270+vCg8YktO1fAgzU2P4V/Qvu9nArUMlWwHkkxoZNvCdwHoWxTgOMz0RKksnWFAUWTQTeJ1A9ZFLdAGEm4FPw/QVgaErK0h/4"
    "pEV1K6wpiohahcIm0qboGwGj8bSUBokBRKiOsMk4r6hytGmzTIBoEXTkO0IRb5qsZ5N0in0joxPGg/yIj3qW2XUqgA8aoAQ+Ikp3"
    "6HDO8QJNhsqTw/ZBQ4ag2cuTpluSPCwjGmQieXjwCUkD/FSf+RTI1dVdDiqqOeOibXLQecB7j+cvCli/KOwrA38hseBrCvz0eunZ"
    "I8ca58kz5ozMoUgvPdlV2AUzJTvQHZgP2UEOppCObHm07dy29YXprS9sbH3mZF2+hURUA/TqAdKpz6P+IT+HUmHvv2SGR7On6hMj"
    "4mXH4z8sPUkilud4/IeFLBUa+cAcZHL0WV8sT2TZ24f9xDOu2inWKWiPg17VrQLtNKrfKmqCmK5bBOOknoJ9x6hM4bG+eB937N5j"
    "PzY6lsAsBzAdp9wXr5ehNGotkMkr3KPMKZJwAtLSo7rmRLolzqKA0XS8j/Dq8lk1C+V4GoBknhIxC0LrbMeLHgKP/4ATGodYifKs"
    "a9wCyISSINhQPzOW9uGVBmNThzgvCzzp2gWpFq6EUhq+PnoUeFdTaxhOj411xlkZpYySNBUDkGT18tjlPMQGUZs45GDVCzlXW/M1"
    "G5WnqWZeBmH0cz+CIWZlT/hJHbYtffoynHs4Q+VTo7++gtXOwwOPBP4Ev36GfBMF77bWjIw4ntg/OJPS6Zn1TfeXKaQHQ38IY1/S"
    "QAjEy8CqZaeqsaHHk2TUjTH0LJkrx6lU7TiBVP8ziL6H5DvIhVazSFqCfCv1954jnE76ptBEeCHpK0191pRxyFSCnFEREOSY1IpL"
    "UcWNVIbzQmWyfWd3cgFoWhrcEyqEDUjRjYhVLfi0Z2WFK4AFCENtk1cDUGjz+nD/2YvHBIJOwrBTAbjYnEp34Ay7FZdRJikvO5YH"
    "AqRbaXjiJmV5x7KAC6jSzq34DOfiGjSRAUk8YE/Gtj6aqgNBpnjmkgJ7IHNNyT7+5YUuESAlAgwWgEiJACgRYKCZ7AtDFKIurNBR"
    "9nYRG2wczSSQYYOQPJHEiaxnWvzT3767yXyAAdCfL2DhatKfeYk716HlyqZvVItZOjH0BOYljG6jXz5DHvfskTxTzHlAH7wM+EIs"
    "bgrkDm/KlEewq+uRX5HC4IKiFB6iBcuyI5b5OwI1+1clr2c6lVItPlK3mU/7kwf8/3e4DVPJXmaHEuGEvEwZj0hflP0LECrmvt6X"
    "zwCjrIE11XbwAtLZFYxFR7OFS0GZzXYu5h8vYDLkZ9dS5iIIPuXeC9QFPJuuzM2kG/9sYXSaEGGYZr1vjjkgAdlOc6zzaYb7l/pC"
    "k/Vf3l3EX6Cspe+7DYoxp8OAyboF7lQ3ZA8vPL9958BiZT789l1EfwNeGM0cGWN4wcHLQ+R327mcgVlI6red5rFyBKEGiOke3nK+"
    "/iw/S+CkH4ArOsAoyG26JOqqUzT3WD/qfjuieZ5n3qWrcFzJLgdXQBZ/qs/cA5Cr0UXue9Qsc4u63/LIgvvjiYfH1mfxQX7gwf7C"
    "P0CDS7oQKcJIjMLMscz7x5OkmbsE8OuIJ32TA2h85v4Qn+UU9yCluD/xr9C/JC9UT+qnOQHUpdGN8Ofx+fjApgSowXRq2UsmUAT8"
    "JPQvVmdQfz6xQF5UfE+sLwgj1muVg9MovH1/gic/QxHEoi2bWVLJ6P6HJRr1veMlws5QqTNreKGwctCxo+sr3MtvLjcCfzwtmNOT"
    "y43AH09LWIWVe5iez8AEMNpvP36cvLipK9FGKZ6Fmx5L8Syd9FgzUnLuuVILx1AyGrfx1KebosvtVAuZ+jfSD9iQsXgNdSfVkPHp"
    "oihzbwhsBSfAKPZkVII2qtk/MzhBG9zsbx4j0loAisTDPGrD3P/SYZFBHbVB7X/tINAQ1k977fLLMjk/fuxMOfp4fvzYa9djFvzC"
    "InSO3kntcGO65wLrF1mSLLAlyZJovdGCugBmuAQ5XYd1+sfT5Y1LtEu2Yu5J8VysG87+SfBwHDOH/6E2eYPHuCDWFadM1/vrKto9"
    "HWHH9n+hGi+cXNMkgfmhp8ZtVi4vZoX2HuuIdlabtDW5k4RWcitqv767Tz867+oerGI3VKF4zGDntvYPbNuPCs3uee1ikXSXqLTk"
    "F10otIuRHomeqyfRQPOT7GQAZdYrOtpiSiaFHcFsi9U7Dm2Hye5JXxQgdZuhFCASCSyXuRYgGCj3Lx2S8TjqArwPOoTXptIzmnGp"
    "Xr+QQjo/mXFu4uWzx27UhfEHiEqnMAcY2B0EAn94CW7sGkTF62RIptCSoJv0b5+cqR4hAj2ceaYjIRCbzd9/nwscK5MvBwD9dp6e"
    "RagXsykoXZTGrqRuoWmCNYh+R8rxeu2Gk7qllqnLT4DUtQHRllmP5rUJV5tqGoC59x9VNAugX5pxrW6Xg7pC9yPIQF3DisMiJU1Z"
    "6HJRnwIvOCCasKJ3Bc4vti67px822ds6zZ0JgCDHlOaCHMAlKrSm1VV/bCiLifbYcmh8h/oW3oWCJWFWv0K7BzoRa03AsnsGG+gc"
    "nK6VlAgGjjWzjra5DrdB5iYAI7NU/yQZKVa7QkOlboMxLApNQNgYEh7dKfSjZ2lQ1rVZEb4+3xqkZk5oTtV2FFwrMlNEYF7mDH5K"
    "Z4fQKriCKeNQ251SlMmfxu8dK6ASNRvsJ5E7f+iYksz3Nlr3Pd4XxwoeJfzDrBhERrH3MerQw99/f/KQQTpGbnkLdhwLvhVByKWi"
    "0yhhz5wGv+AVQF8ifHxDSiOdt+2eVd8QqB2SVoExFtXPs0Xc9XGUqsfHaXpg/G5QBJI4fEKnMkTEAOyQvJWAP9WHIANfpKfE/xWC"
    "GdJiAX9+fIL6XngURnzV3mWz7ZZxx6i9niKna6i7wf3gSD9E0g/O6Af8KWr94Ix+cLgfjIrxRvHnlNt9O1ZdeDzcM4Ukr89NzvxX"
    "xOs3hIwfP4LYepfawJxaona8j/q2j9uDu4kmp1q2FHOX8AtQyj7bbntLeNMTR/ZY8v3jR91sYM1Mv+BYdvMHhUNVPH0isJ++Ircx"
    "GK7DLV0NfOHbCFLGEUzviyki4qs+Vqa2p99Tys8KitLq/JL/E7k4Qh+MAxi0XP6wR38ecKJWRNv4Pt11PLCnPqwV0Hvjy1cdMW8f"
    "pOZ0YOo4QiJ+fEqZxSLYEl5G72gIF3Bvh/h0+JTChIodl5DVqje4uGO0Y78GtF1yPzswJwRJXPJazrbPgdR9XYrFEoFSYWpKefhc"
    "j1TOmWvmaJUJZ5zioa2Cw+wSkVWvVu966l2jMAbgTX3RsdqB+hU33zZm5Jkfpz+bWSqo0ngsRiZLayNLHqs73puirHdYYMFDJ2Q2"
    "XseeElxZuspZOguvASzdp3ujzdqzRf1CI1OrkjXlIey+0D0jVRKOhAI/K6nv3T0PtlwZuY7K70Dm6fT0Zao9o6dDk14tLoPwSbwN"
    "JAKqDuPJqBFdFDsJKngaxEeQm1cghk41WAImMGKdwmAjQvKh+R5gH03T+wJk8FgEHEI8FidhyH8RIwOOzT4aXJ5x9kVl+BKAtw34"
    "J3m3z+GrS+OwejcIKobBUVDxb+cwqHfdlRn4QE1nqS5rvJa8rmNpwoeCAPyhSSTsoyFR6a/7eINq7TIMKmFKMl7WcZT1IZwXrekO"
    "scV0mhx639T7D2eBfsbJ0/ed5hedvOlii9GeAoG6TMc2Y7tCOabzG9wFUSpe3S+Mfe+oGUQjWzs6d8K94tA5MqUeffLgpAKahAd6"
    "uBzQk82NxzxhjnfmNCVAlBNfXCKaCiCrSg7T6xGhZZaXCYYSXuwZ7SsMb/poONt4dl4feHxTN2dQU32s1BzpQyUwXj2YL+Xhi/nI"
    "Wfgh9MNAqyMoSnTsXFBHPrX1622T3R1iWUMXbMC0iz9T+Cf+zMAU8Ab/fX0CdCECT4HkulA8ImNQ2e+/Q+PULDJ0xrK1s2GyMWcG"
    "3qytA/RgL4LfnWi345EgvhTAlVPTqft00l6FpiYkglTMzI1Z/PqCacjoFfwEuwU4AnzTHbddseO2md1xmwL4LYzwZ3HFhJMpn0a6"
    "+yriyMlwp4XcKh1lBfpVIs7BPr/J++9RgbSLGtLciLk5esJQLj6dZii0A/Je9kGRYFwIugjKtHvuRXftuGt6mrlluhYD+nFxlNEZ"
    "+9+JP1uTZ6l3lsGde/iZosR/3cPPNXt5UNbsQjq/WtCK5QcZUOFRSTmgGOfQRUx9JE7tsE0UXa3WF1OdOMnugYuQC/TEC740Scab"
    "WkPHgbSnMAqzpooRoCNVvNoI+L2U5kflLc0gQFficxk0LoSigZjHb3JY6FwA2fz8u9etOri6XXNt/dMmDpuOuTWJc93QB92lQR+h"
    "ovoAPZdzizt+3LS6EZzDKn+17jcQxN0mCVX8goadiORu04RS3tI0T8LevIH+COibCJ3qPlU1CeFqcmvuMhKt9BtG8YAuDawO87BH"
    "RugN1eyQ0eKxjzSHqnBxyO7sx1zrpyztwaoStcXi0kUNzGn3M297rp4k73qT1N0EgroAGwBraas7S7Ri2ZFn2lGij8yGEMqh4F0s"
    "UNSE3ktC5L2L2ZPCsNh7itqwL0BnZU6op2IEoIGtAd6x6AulB+hBnmJguhtZ7KHYjHRA0+D/DAeztLtRKnoAMV02jUFz3341M1Ob"
    "d3wkYgBJ68HoCScI/F7hlTdITQ40b9tCXiMSTSoKWEQrm+NbB6+VQZnb3Zse8AnmZM6tJcHsoNPecQruVS6k8befb01je+9pVed9"
    "7jTosOA0lne3dlzRA4xRdqVZqyt16kw3YKoQ+SC/0z1CR0Rj49IX2CpYSO8JpkExJZNv3jt7AWnldferFngHGemOVK+34ipguQmr"
    "lpJOfMxRNtPK2QUzR2/Ozk6Uifcxmus4O312nMA1Z3GH68SgBF4BQi6C1LiSK3Vih4VUhbZh2Amah9EvNH2cI00bfNVOguj8/QDp"
    "Yu9Av2aOjAMkmGjOacC4zkdUp3XE9+iULvZmYqUL2YgOMdAz5YnXqRSK5oCB3LkGQDKFnnuIoFconBok6D8g/6YW9u5KLA44W7F7"
    "OxxIpGFcRCIk1Cx4Gd/gpT5gbeNdenCgBNuOaMKtCNYIK7xRFLingXBnxD8j8N2hTie6dNmfXanu/SLAf3cdxzv0FH9FOfKmbQPP"
    "wdtEWAysHQ3NvA9/wRPqz58cSWfcTo53qQgXui+1/Fz/33rk/md679rxN3dQK/DePurl/lI3300NesGfQqyltKXr4D/OO/lMYMWt"
    "zf29w7nWTRSYr7m5rYJ7LNvt0EzCKdljpWkHKNgQANo+rmA0L/kRgTgEZHLRHdjKc69h1ihxnxDQ6eBhxykKu+Jeke4Q7COBfV2+"
    "E44mbZHLpva61Kfs7hyOLNEONAWuSxgwLVAaOs1bS1Cn688uodXcilxcsWDqvK7bIXHEfnocdr3KW+Kk3QG1S4GrdyPdLdaYO9JB"
    "ifcinSpyeVvn3430NwRkewXSAelOoEa/l/ApOj6u8+K9M5IJlw6M5i46cSErb7EVscd2sxtZQktfHGkA2Uaj6BzIKBpGhNGMJ6Gt"
    "FbnK2z/o5iUfzFEXsdmVto9/Som6dgManxGVyqeU+vgb+Y1s0kxqcJRLkqCTNZw6hYBoQ/mUkvHOotVptE7XgH/aISxVoFft+Dw+"
    "4BUeBnL/RG0sMCDZHQDEFXFz8BeVAziFJbgiRAakF+R+HJw5hCkFDmjcEnuQBhfgQ9gpMk6DVPXGGbTNG175eIoordan1EfxkVtg"
    "//HIPzMEgwaotO6L7qyhibKU/ahqN/HI6zp6XKDVBrqBiuBOoMcI8Nez4Q46gE0LoUoe2SpNHTT9U0bjAFS2ljRlqJtzKt90C65X"
    "YGlDSyZQZM4pAE3pRVE/jLSOopVMLZqVKbOfF9Byp7Lw+gedBEfgrKb3oLtpUohgOEv2lJgiFKECgO4bpQ0xwdQQwTgDavRAZPT3"
    "8gX4sJ7IfAwLfpIVhQ0j7MSHITH1OcupcCHxSpd8eXjv77+Lj2vAfAXIgJsiznFiBLhN5FMP0BHLmHgQrBQDaCYpoGpIabh5FwyZ"
    "cJOF8peFXmxSpwacgYKsM7Ah404ZtBjqWPyiIE0iHIoTeTGFVeoSIwstEMH8mxZNSTNSwfF56MFpwQ4LZIa/ktwBCi3hlqsHBnID"
    "oAjsLkgWRriVOdEByuQ83TnEUjAic7vpC4NXjx5qB3+2DAalFcQZNWnOCpw5rQ5d5delBefSEll6it4Yiml6L+yRxvn0XlEM815o"
    "K2icXoWWRSgawVo6ZyGDuxNvCG0N5bvhshAIthm8H+KSAicBFBA4BrPGdYKze79dBPL2dhH4q+3uWfE9lRLW/Gq1BO7tFaN+vFrt"
    "O2OLvh4sy9gDHRGP3+69mHeyu5CYnl+HoyzD7gPKnMKpeIdriiV+cS/clgn2NUo/mSOuaCaq97B/VCUMVoC7wStRu3A/XoPEzLj5"
    "ao1o/wEIgIR1J66ZbRO7A6uf9e81i/kZ2TzuxdBDrQHUvAEW7Tzd9xYovLUrpv3uDtyr4d3g0QDvOndq0YHABja73oHU4rTNXonT"
    "RubtXuhlw46++7Zoad3/SdHSuuZoadkT1XIOfvz4kcd/evjP+eSh4OHXd1uIpzK5xmdVFdLPB1X6oOxlIGLDm44HhBOw/X7QxNTH"
    "fyuLH5BeHULOQAaBYBA8C7fwDziwlIIDRq3ZE/eB/fDFguWvHu8HHF8ERo7SO9kzYmBx+FkJGb4RUkp7KdLEoCQc1veXR1XC5Eei"
    "XXnJu48E8xDUH1SgCBSYyVlnBJylxCdTyiMUCuFrZlCmzu7BkQr97HLqlHZqynnRq8ZpWnuHAAD9/8fznOrzP8peUQW/Ej+CsR/h"
    "kBf8BFvjbs8tvLiG3/yPKoe8CjyT8WgbgIETNKkULjAm/5ge4QhseP1IYg9yX6b/8R9a6pQke+0OVmmSymkt4XxeQX9BGo1zCp50"
    "+TsM+YVbVf/kyHETPXx/0r8+a5HvxCcYXgFXDGZP/EP9LPp8XvmL+PWJA//RZko2mtn+T44LmP574gJu3xIXcPPPxgXc/qfEBdzY"
    "4wLW/8G4gHUqLmDDMS5g95W4gA2DJ3b/zriA3f/8uIAt/SRuPYVf3MMB6tH9kKwI/s6Eowz/oGCuD/D0Z3ytgfwBwwPiRPJF9Ebg"
    "TH1UFZCUBRvH1hwojpyjScw1KnacGYyc1WzFd+hkDE6zbNN4+W8G0fRhuB6omUK/LOI66Q0Q8edrUzA9nIQVDjiMnQJP4gJKocLi"
    "WcMeEgFsDvuMIYjKh/pJaX9SD0EiHFNNmdW3sODhyMlXaqiaKEiC6e30ntljstm7/QSldsnuKV73g91HjstRubtR22ywjB6uq2ab"
    "ODq3fm/6UMA1e5w27GvDhBndW41tiJpPHCpojRbRRlxoCjtqGjxe3duOA7qCWiTjPo4D5xIFrulA7dqo78WJw3nuGMP5r+CM9sZD"
    "lpXu08KUCngzYBrS1WPyhkEQC4twArYy99AZuvMLPYid/qjPGjSMckVJAumZVpzx7DgFY5Ihd0SwBsqvRs12aWCKf2bAPGfgZmlN"
    "9cLwVnpllmXhWBmCsVWGUs2V4bAnUBPmNF7iJAnryqjqSAp5vm4eJpQGfdNvU5+KHWT06JexVped5r7Dp3Eygzw4ALau6VNTHKN5"
    "DdH01NqzeV1TDaRwjSvhVeGklTZ3Fi8TKBYYkdpJtRZdNdh7XpALDnP6K1Ogk4V1FnK6jQ3SK5Ja8X3C/SoNdS88mlBp8BNdKFAz"
    "S+mGHWq1dsqA9lrr0JXHb61GK4BrSss825KUMnzL4eZvjKY2a3+ge1i86hCLJJREzm7Qa7tNJKdw92hCL5xJzX9NivP6gjjevd2z"
    "CHF9RgsIZrZC+DXYeBg3enOnw4fgs77bUGqzZ52fI98sBVtRD1lvms77+SGYur8HuC0GBuw0DeKw5TeZWxKYMtRIQyeWJh2M1S2w"
    "yQ+aGVNIXIKu0Kxogk7NiASBPxwQ8wDTKSkFRiJQH21qTnSlSUkY+NyqjchhOJ+d3ZSJcFsOIGdpWMdoD9drCb1J+qxPunXv9vy3"
    "JAU3ucIGqUkUZMqJMI18McMrt6Pstrqd8Y9OIww4PBh4fRdhaJSHZHnA/z3ikwf6uYQ29+jayPuIu+XVdA/kOCMz0EVeMIDnHmxj"
    "OXiX/YofdN0wEl7CQp9Qag7rMD3EETcALM6B1KWceSDWIC9uC1DVnFW4aYadb5FB81Tz2KengOY1DqrNpffzTObY7WdUNA+tkqcp"
    "9BuchfbsIsfN+R0r6FUhCFSNVlDTrjp0FfPFF3ISfASyD9zHYWSRuSoL4Odnp/6nwanuDLGkN6qnmBo2gPt7M2h//9pAERj0Wk0G"
    "i75RkAtzTRDktbpK0s5ANfx4HcsLCp+L18ChBy0TOrQEOzZgDoUM/GkH65qoo/tzlEFSXOkCF1Pm7N5oCn/awXrsTIcBv+0Af4Gm"
    "u2t+qVJTjb7JVJsp+KP4+++/AREDKvMMR6GOZya4SYMTwEdTs1oe4h2avwiOwfVpDmvhTqI5URWB3NkD25TZ2SfZU/ANHtxUzHuN"
    "kQ6YEpCfAEck/sS0DQ+5XM2TTiFIR1sP7G4fW+58pnquc72PjsMxYms7Mk/t0EWda2EZxhmZfY/uUhajFHY9a/jsAUO6t1PqbpZ4"
    "cQXZChmSyq4a7A6ZUpUbrX5vSuVBGVFVZX52VDnP1OI1buqFZdDxDRltUOXmgqRA1biTpzkNHvqa07Zv/URIf2nuiCCR4Xqt8AQz"
    "eEuGAg70bJIyEAS+tFjc2nzjnQXds7ogzDwZZieOlptaI3StReRBkgsUD0rouYtdiGlAZ6LI6Jpb9NDYtEOQVUh6Ls9NY2am6EEA"
    "QewDfk+DbX7gPD99UuUj9+mrd0oQ4SBDwtPgL+la52/oGl4g5ELRyX/kTwb9/WgE+zRTjynmp/kkDy85HGgC+vYkpKoR3YvR9boE"
    "1nkdtGHpvcEFyJW45kwOaX4c5EiOUQkhQepy9TTuxJtoglQZd/5jlhqJBd53/IqSFZDfU3DEx8p09UXjSy5KFjIeS64lqGuAGpKT"
    "fAe93UN/wzBml6QATuX9e6UeMHd/TdSxVOAi31igHIUaG8w/LkS8GHNjPjTQ1GulIaNM/z2KVPTCr4lz8E7W1OyPrGxZOj1iCiUV"
    "PSBu7kCoeCEQ5sIJL3S1TsSGaQruYgRr2gZkQhushCYvG706MRVa8HGSe+6t+vu6YyO4kPqG0yvZ+CynVqfj5+snWgjSAFIYneV2"
    "IP38Bt5mPwTpqEbL04HZvTlalDkZeaoEJAfXLDTE9rp0+yNEnE4E9FakzYtZ1fXFpZ6vXsad8tGeAR3ROZ9WKS/J75tZuKm7zBrM"
    "uj+vLdCXXzKvopv0Sq8Ih5nXp56wVtPk/+S035e9YYuEQ1uX9E+2Z2zJ86MMjaCw/PQZ+vjj0aieobZE1e3IUGQEqCnV9nDdJK0L"
    "37vAIN2O8FpABJeBGRHV38Jm7BzhDVP42Xnx4s3sb0YnWswaRr1OGHLBJ0OEJN2whV5wpqzPTrWKkLjvbITvxLttvf482nXdhf04"
    "Y1IfBhyXHmPSkrxShZPCH+MMHmfdqEK1XmQ5igbPnn+IL2tiO1xgrwjHNtHSbZCaZsg0yI8/TfuGKGLIeQiXmmTyGjItJxSHXkNf"
    "qKq0h5Yz7IrFEhtsAsuDv4IBO5/XtZ6xSkE7G5LYrYrH++yx3H5YjtEUdFOT7ZwG5z61/9wmT53FvEQXTynifs0O9yrLoGRgREpu"
    "6nROgCxPF7KnDEHGb9AqiDsdkXnlkl893tDojcv67hzg7bv+lnyq+TiaosDA08BUi/VhFvkdbje0WwxWVWU8I9C0k4P9MtRQdhBm"
    "OvUybtGALGbt8Amfple8oyhkVAfjFCZIIzO9BCUsGCUL8TUDDZiPz8dOOc6GG1rIJ3ThSXWjxrEnznVO9QjiyM0LOicpJBA78y5r"
    "Eufu3rM0sSOe1uk6KoN/kY7XhDDt3pNaJU/kvYtpJu141G1TIOOladdum0SeuCAjOU5YTp/PFs2YdiTV4kJp+k4TlDUUfFZjhKAc"
    "CmnMXNyqJSGHnObxXuAhJ5s5nWc75D3RBp+a3IQefALW2GKhm2dAc1ZmxBnj/Sg+8uJcOC6g5SnquTVNYyuwGD4pvTALQEAoYLY9"
    "WhFRBbj2GGpV9PhBr6HHtRZoqqR3wjEo0Fv6oZk12dfTvTkyGVT9+IFiLGW/0Vuk/iqWMQdbsk0DwaeT/ZYjT9Lw5t5ZJ0Mwh8qd"
    "ecjfEibrLgo+juceE2X9VOys/4R4VBTl2G33XHCmq6boJ+g4NIa1Bm3T0Gkc2YBq+ysMXQhKfFlK8tOn374bdZQXL/AWBxrgV+Ye"
    "467L3gA9LeiCwUH3/9rydug2VBu4WTQ6xThxGzn3syPn0Mg5RFOv8gWH1l/wnN61t3xteu/aJ2szawB5ph4qghl0ASerMsur3ilR"
    "7ljtf7UbhLvtmNedVbnrWK/TdNPx1O6PS5/5N+Pu9Up1I1ZbV53n9u29dcYAEkS0te10HHIIB1T42Ts37WARMAwb8xd2riL83TGZ"
    "5JUBfGWGSyBSJ2+ZnA1MjXcCZCewQTw/qhJ+gV6TzpycZRXTSQlnecmdI3XL/qZixuCQxkcZ8ur6v9rQsEss1DXPTw0SjZLqutMA"
    "+2g8Hz1udrN6RGSzEaZRtfn24T04tBkAwzq1T6eKBooW8hXp4Binq1gtxi13OIL2VHifAwPXOOgv3xCYzKK/grVgHZxjFDHzEFX4"
    "VIlxUODdb7eqOKnOmHc1aLl8cbcD5f64p6Z7djfa5XxBrxM6zHa75hl/8aYegvojzT9B/aIP1ANt2R1uFu50+s/AszOWKIti5me7"
    "pHXH4VLt7yIYc1PUPLrcszn3w/0qUI809kfg7v0eZ5Dr39So/eqJe2FMtlCuoUDtxlQ2nvjjx3Tq9amfsZ3GQ5Dhnz7qs9u3gXvR"
    "c9A3TptBReKj07aIiImRn7DO8K/Va+xIqFZQLVFFengU41pr5d7dn9GHuxe2Rt2vXUfImomU6V2aY8BwGsCpkEvQadFqKidaimF1"
    "TDQAUMBDFw/OfXU1p7Eqd9V75t7uWkeTV4t3qYe/Mh9RIFi6VudlxTjcYJs0ugFH86XAV8jO3FVkZDXhy2GLr6nyIjX9DYjkv/GL"
    "l2/gCPMyBXRWh0cw+E6RmQr8F34BDzciPtHIz7KOHlWCQ/n9d2uK5zt2cDgVwTxy0PEWcV+oJ8DntG52QtBO0JIFj0/37YZcBocI"
    "AzNWi77W8QEhZcf/6puA+8vLlWRszZBIqtjlnjNdoWPAe24eIMFpDxctozUWB3zdzBE7NoYza0W1o4u7rRfYMwT2Tuxp+nEQh6NP"
    "y9ziCLZpqivoGRmHXtJ7vtPO2UQGvYmCj7DxAzL5BXuD4J/UR+c3Th5R33t4GCjP6Q26vgOjFiFdMGAjAn3TvRs5RivW9MIAFi4K"
    "M4yOT5j1BD7xQ0KbMx7Hmi0wlnjI5tl2ZRnOb68wbRhzRD/RUjQ9M/6C06NbP1K2gRrnqAnaQy2VZuvYwxdjLUUn6F7DGPspxbC3"
    "tD5joy0uqS6Cff2L4UPCcYJxQc6NRNR7L85oNTOgjM8yxYF5TDHpE/z/7zCEOAwtuMG/iRsTp3d01Kt4x/wUilapTJksfKAPLwE1"
    "CwJq4njKt4QmdCJ9gNsRzHwCI6zF5v/ynfIcZVpEOWoDspfJNaXjs1In1sXBRcfRdvW2N+M/2z1yTIRi4Tu7Y5wd3ZBJv9GFbDlF"
    "P6rVZFri+s6lCto9HiBr64vhr5qHqg6nHAWVOH3qwVe19gr7ToPxPtMr0CgPGDCaubQgeKbfAy9Txv0UqD1Ss3mpghVZfGi59M3e"
    "CaJTsN0YC4ghEK6iw06nTl6y7jVmh36lReK1y9Ts6wUsLej9fGsP39GUqRGrP7J7DVlhX0W9FVwfVfcdrToWeNscOLWvvRl/Q8uE"
    "yT07Dt6Z+KfBKU3lTuN8YayyshuZu1hiIhYxJTcDmojtXOBlih2vdTkVxY7+CaWDi3sjZDBPq/FU4y01VL1lNYeJmpMPN5rSfG0S"
    "KZXwWex+ShNkF7q1/0f6QZFNHLI/xde76yQZkUG+MPplZg7w3JZDV5W5B+7LxEU2MfbWHGab3QXo7rXRbJie2TLIJzUpjf1Tk0CT"
    "OMnuY5vcYsB7OeMXPPahjfF+b2GHae+njtYPmi9o6xaMHV4iP0XmaXIbre541dSKc/+ZKVocU8b5qtDqsJrup81ntZ5Je62GGKJd"
    "cb4yra5YJjL6q8Wn8D6LFR6mPpNphls6ukIkYZROyAs8v98D1B13WFBHnqxBMpJgEIPafWMGFr8+305MC9WeUk4MgkQ+QnnwMYeP"
    "I4AkkBJPDNR3KChHWTPZNXeSATo0D6WZb0x3z4sicUSa3zF430JflW+M4WW5/o0xvCifv4H+F05PX6b8ArA8fA00/cqUYRJ0xwQS"
    "UQ6aQvCXIizwpfmThEUJ+YCfkPY1H8/UB/IWqaVwlz0LSurgcN0CdCjaN4sQCoTtOcAzC72B43SyUum+1qx9pXr1z3QFfVII0LvW"
    "gV3Tv24Ez1+ZjP5roOPe3lVtf3NogeSr+M4ff6IHTyANfJNnZNhvu/YFryD1ztGVkxTC2owEvb2vhvfN0klz8MLwDIv3HumpLXum"
    "FPlBezqUppM9SJljKJ0qQZJgAJGUI07RyB6kLFCKTr4gZYlSdBoGKXuUYllWIH2H0vHaAp/rJ5X3TPEKNXywtTwwmj2g39MUhn2X"
    "wTl8SjmKB1weab9IHHggnlxAHZIEhwRfgsLXRuqXYOjrjx9Pdr7CPlqf2P7+uz2NuAlkGV1nBzjWJzwLn1Lso3lTI6Hmea0bXuYL"
    "Z7iL8JDxIB/UaERbcFwJMGhchsHElEHO1jjk6BIPklgmQP0acYmNzq6pKXTZQwJdpL5gBGA6hYazhmtshns0/FV/Ja5fvxAI5OdZ"
    "g0AfX4myiH20H/NMvr45026mu7Dl9B0LusiAJvs4w9jWDAik3YP8WOBUMCBpuZwygEo4ONO7mTSTAK/4ZCzAT6Co7uSWzkB8w5SL"
    "UggIOHLvpf0RTNkUKnuoWjUW8ynF2wJemHiOHeAZUZ9v+g2FKCAuQkkpK2eCpckqfmZtelxTUT1cCKcFY/3xgwBoXlPULwF3oiba"
    "Sf2nIwkT5yEqMuV2qQhC4HrgL5dqwOEZhaVQv9xZZ+SJHq6MfLjUhx/qq1/C7rWZ3vTjOk1Jr61ZQ6wj61VfNNgciwnGwC4L7czJ"
    "glUAiejrNfhz6/XXr9HXl9tb19GPHx7WRfh7xpSnYc37Dy850wr7W5fWJ9M+/onmUMaqi/yqVRf9Zasu9gtW3RvXxpc6NO9D5wZd"
    "6iT+WDndwsN1e3hhbL38cvPk3Clv+r8v6cBU69PzMznPeJmg9+uL9ytcpTWwShn20X4Qfqa7ajiyYNAKDpHFmPfg1aiHHYCDRB9Z"
    "VhBg+L8UEgh0lxJOQ0A8ouzheFiZVtHzlJ+mpvqpAPRZF1/0tswcgeoDQ1X0VRdkrD0hk0OX+/7J4pPjU4oa+4vB3L5MUdtI/kTV"
    "Tb96IU5TGQ/0dxLwMjVD6qKFKz3ikFfvgJGEhB2iNDDhn4pORGYgYJkBKv7CFB4J7WjWa0bodWTMAQuPpesEpyP+QQFi8JQx1fRV"
    "Y1bIug7gCxrVTQ3SN/VLw5+2M5Q9krEp0GgyNw2bTU2nP9OSPlNkfmisaoin0Bq0oJU+nbvglSZfGvwZ4zY1tZxmMSmbEG1uhTHX"
    "44xgmuPYVAg20nJDinGa82ocwct0PDvmux6ZhNPVAS/Md83BUdpjx0PHk0eTif0c7x9Ycb6WZG7xoD+aIu/10EKkX13B183GgyEq"
    "10iFflnQIxQqFyVoZW25RqqODSPwLsTF3cHYBFWP5SRlnDvYR+P61Lx+tIGjJ3h6XBpGN723yilGzBgDhkgq1GHsjtxKe4nAexad"
    "8upGGAy+WrVpQzSnvbYv0koqfUp0FAHWV6O4ERYQ3/C8UTvq7KEHImI67MwoyNxMdUNgdj7nFDS7H+zGwVNDOKQPDfE74oult0SS"
    "saQ6YUnHBu6EYVmBB0ztS/auf4JmAp9cLJw/IeftOtNlaOanhZuziR+aQ2rWomOH9gJEz+6yGmgGTqo3djktAUx0x3Nkvh9FRPdQ"
    "1td+Mnvk/A9Ca0HwdFUCrOkV9qMwGtnoj96mpkM+Hilvuq8H8o4oLbg68ayNp4xy2KIBaP5b7ADmDUPrOByoWZCzxR1jiB4dWgPh"
    "X4wTUjB94/tBdARwOO5jegeL8M0Cv03MpziBMUaytDWp28iAn/pR00jGjpgc5hFqtiR5l8XHktR3UUJnB4BASKIvmEQTYF/SVLHm"
    "eTESCNanjL6DmZW2BJPgl4ZATYMIsXNH66kPH/3OYFf7ZISwFRXskWBrFN5KuXDLfTv10isTEwoRSpwlOSMq131BjobUV6KR5CiR"
    "zZkr59GEMudCVCkoNQDO8C0VfkHzR2EdoexuJmNi+ZjOAQuH/lnJIRnMEuDfe0ng1bscfGrjoYYVwav8E3QRHqJcLA/AaSmOJaPX"
    "pXtTgE4ouOIAcJ927OUBRwP+hPiqiyP2R1NUw+nU2BksFSMmutc2SluNQBKBJZ2vEZnvyOzGxt+1zpKoxebOUNG1HoKGEtJ1LNSC"
    "OFk11wDdPO/B7tJF03IQjQgeqDNYXpJgQA8MDEUsBXyiETBz8GvFqZSjdkYwYLEgdSTQ8FpZCy0KJu8o6GKGgzUU+0hM3Txgg4Av"
    "NBYWrmo+JsEkLyNrkpxAWLamszFNIpo7sNIgERU8DbyQNh7qsQPtXh6v7QY+m7CPdvf3AJq1+oaXmTk8qXxhLTffoldnFgJPsQpq"
    "dFOfY20W0jg+H9GTaz2mH70EKEMviBSECRLB9QVt0N/ARoDi1WkiIF3AoiLBeSQ4reZXX6SNyYiJpGO3nXgnzXFcul3D2ppXe1vT"
    "tDqQeTj4r/eYOurFfISoXTJQOZoRPQ4TEnzLhNi7TuHHbLjhgptXJ9U0dWbFJ2u1KhM1raYRkZelnznp+YZ2kLU/vKJqQXd/EIiy"
    "CiGZ2k0g6Qbtp9/jvBYY6sbQebnbbNlFdDTSbxbvl9K9WoKCbqvROMAl4BHiotBCAFisU+htBm6JnyxXmGCDAtOshXaEhwoLXs0X"
    "nJQq1xLb2JGOPlluQ13mxbIWUF2mCBmAD80ZWVuwRJOl91rjO4SRBQhzoobxTISPhfNpwhJM+f7ipMAc1UCaoLN0Vj1ZYjHfb4sC"
    "c1Y5MbEILTfYmRu9bvU4IdZJ/qVM7g38zZm1aWvdxMkGUIH85cv661c8WMBYgqEESDOds6ATbOXHD3AoVmgDGOcNie4ybQlo309I"
    "py1Ar0p7pj0GFdb9u7rr2J3NMSldOpjnj5xhs63/NIKe0GN/dmT9/wlDf33QrsPVyBoRwu1EhP3QC1z8xDoKamU5+ZloBfHXlFmK"
    "tNhH+UshePrscCzSyurhykV89ICIg46UyMYFWGgwEAmARUisy6donzMb8eCjiU0nspQk9b06kZ+Zcutt6K88+eTfSRAusxy3nHb+"
    "nmNa12zk+tb+OtjGoi4zNhWiwP5X0yAm3TWIFs/jWIFoSXyD/lB/y/qL1YdolXdO9LrXDvdo0yPqfaQ2MTT36BPp4Y0M/GlRDmjX"
    "DGRlMoWT96V1epTRUeepdEJPoPp6IMU6Lx7x1aAeSzG7pyIpD+kwwhUcOPiA/1Txn6IpjHDxv0MY4erbwwiP/4eFER67hRE+/GNh"
    "hCuvhREem8MIj/+ZMMIji9Wi2fRPOa0QOzxDt2mpaTAyZciJD/0+8dw5I13ADvoh8CEY+QDToFF3ijjCu+wEsO9N16q6T/n95/P5"
    "8Rx+lOSVPxQIBPywcsx9ePjwE6w5YlcFRdA9q67BXroAazUYfgyBfx/ij3HwL1EKoL/xRDbwGI0HI8mElvMh8BiOh2OxOEiIJaOJ"
    "CEgIheKJQAwkRCPJJCwSSASTkQisLRKIBEOg4/HHUCAWSqJfoF+BYDbwIfYYT4K6PhjwscdoMpo0aow9RqKBQDirtxl7DIMK4x/0"
    "XsVQt2EduL9aQokMKAv+RkKJqA4IvmOhWFivCXzH46GQ3hT4TgYTQa0rAOFaN8FPre/oJx6QBq8NVatPQ4bWnoYtrT8aOi2In2iT"
    "S5wGZyUBUD9RvwM+AIWnmPelr7PdEWa7k9PT8BGzWe2CFx3u0H0E1iNM/+0D+Pe4f9AyPnxHKfCf7v/yA4qdAaSFz3oekMr20G/g"
    "B/xM+mEpcBcjF5xjZXIUTkEWShU8wSDNgJc9IIdKqQ8zSVWlnZGPCf7DQvX8u9alR5T2714DiCwFMxRO1MBe/s06sgdkUEaND2BT"
    "AceoD8SVpFE93NNYGe4M1t4bKNFcghp5SL3xgJ6RPyB3OKkPAWsuwZY9mww7GAj8L/swzal7dgEtJkzFwXF9xYumJGnPznn1akq7"
    "PWDJ5kOQgjuq6KE7WIXmsc7Qjghg95cPYKyAf6Ob+D0LSdAK9iCzCx5ISuYpwXmPOO/OzJjpTqctM1FtwMbLL68Pmgb6w5yzTBuk"
    "qAesJrdlvrubzihwKjeHy9FUjJ1vofZTXFgb0jNo8F9F8vCfYSyR0tPMXTLXYMA/Lo4ykqL/3cuYiqLhvbsUwffPFr48KGt2AaS6"
    "9xYl5Pzmhm0LAZdMuRG71jHLTODEe8wHkC1F40ZfHrS+pN7VW9JLUxHYhp0al2C9PEDFrBM0TH+NFh0BHenRBmlHBPLt9mioLr2p"
    "Nat4bGw6tYY2Jt47XIImMOuygGUdV6fDxKAf3OLnWiKF388J9II2jvDGLlroyZ0cSENvRMOvm57XRk4myZEjvgHjPzPHf2Fw70U3"
    "7t4r/Xprf9DR/oHosH5yTaA63OnUja/hYugAamZxJtHBrQjZxdyrhDLonXxbPzUeLS2XMMCza0Gc/+so4lfMgEYa7jNh7yf4Sez1"
    "P/z5c62S4m9vj5jiPOA3wj+zwnHJd7G2X9Luz/BUW8P/+QzQcVa07lAN6AJ+8C3lfqKjWtmfZ9JGDW+lPtf+/gwz1pt/bX9QdoxD"
    "2h2cOYlJyu6NUjsAfPWsamndMuL7It3uHVLd7j2C3e4V2e5BWDEOae/Eo7B6Ix4B4Kt4tLT+HjyC6t+MRwdYdzxagF/+jVxRoLf6"
    "kuQcrVfTVUOvoo97Wdrrt21TSnkDfmov/KfM9092fvcppWqrk/lEGxAYqwWm6+/F1Mff9vMsqQRZxDzbk3RnFRBc81vxycpZUWV2"
    "JxTMJzPZ7zGDXcK31uAb9gxiCwWi2LGCYC4A5tdUQFjRBQQYMmv68vWFgdLW1EyG0MUf5ORTK28HGdAPwdRCN9OXFy/T1m8yMqzC"
    "ZXVtmnaZMf/GoMlJkctIpKKb8SIrX1MZSRI4VkRmASon70CqyqW+I1tnLU+PRR18YeDtFfYwhWFQXTpA4IVZsoJyBwJUAe88JFG4"
    "3mlF5g5HXoa+29w7ot2IYZDGcTfjZB0C+7okzz0JCL6zcAJBxoEE6gsBw1cXX53Au9jaCYFjMAuU+QnmveZ1yDtAL0QtOjnBaTzx"
    "CwfPMt8p8kf+SJjfsJqgTJYoSnx5oW61fkNXEJ/+Ywab9685Yc/JyoeHD/ju45N2O/Db6cl0GwIXCaliqjvytlyNwGWBUqbPTn6E"
    "yUXTi5MpFGep09yc6dIILCYMA9I/ar8hG1IlWMWz1oeU3iDzm/lWBUdpZ0StdY8KxupRvV4e5D3jqX0EcwGkexi9i5NVXEBbRwwn"
    "Hnf4Vg5efmKHTEf9G3qGJL+ho84v6tcnUMRoHtamMVMR1qxfvBnIB72hsKmmVN90atSASuFLPDS0j09TfCU4/fHjI6fdJXHk5k6/"
    "wlKllszveKg9Rw4LRd0bqmE1i6/24LUfrlymKtcqlj/bbjn/4z+oyvG9pHYt/WGvp+MYgFPNIR9yO6p7+MNrgKxor2nC5CtFKsoV"
    "3b1K+A+L//BX+iYWfv2Xv4llr2++iZ1f/2fdxJLx2G9i0aT+IzexyvWVm9j51QRPuvw33cRCaOGqbef2rbx9AlvQmgOMBUZqU8BO"
    "yEBPs0rqi+5rFjtDAH9n+OEJdl+bMm3w06+gGkgQqe9WuSmlPy7RJoWBNh0OW87im1lowAEJ6CRQ9gw9l6a+myFt/lstVT0Rp1S4"
    "62U6C4Ww3ZEnVlbfw87wxIHvm8HxEgXyALJMdXLNq/njhSsA+ZYh/jzVHZ/SfnlhtD50LXQBWNZUO8RNOJZ1HdBnQYSL67EXHHLb"
    "NVa9OXCN1ZWcJn/R7uEdJGqnVM2KLWWKI0FczGKJ8tlpHDjRkB1pNBAvm4bYeAeWeD+z1i66u6P9OFDgesWu1WDAAvH5y1fI8Oas"
    "6gHbiehlsOtQBPDVm6K/Pju1pvlns9Lsx6DJ9bPjsmOcSmpurt84BZS/aZnhiOtFS6KjE2ot8DyyHrMtQQJMmAdn+MewkRcjfqZL"
    "YDYD2gSsz6NH1JZ3yDGVl3jO8OrMEu9UImrBYQHaFimOYMVj7zIea5KZ3zw5otfkCxo9AGlA7urmAfNts2DUQ3wbghHDT+hYHy91"
    "Zw+8f2GdmZxWWpfAx2CKXoSc5uDQWEclLeYHWrMQ/Qt3J39AMnZx/ejIydz8Qf6cq0ezS0CTRz7dVC/VP8HQVFfdb5ymTDDcslmW"
    "ns1bG+V/bnHVvMtpj0aJnzyjUmcXfhovRT/xmdXdgZ7JaZ3mFe8rs7xSzu+M89n+6uZBjnbyhv3HGRaMbu7a7F7Z9LcX2rsLzVub"
    "buKpq2dYQz3jhFv4UMRCj4YnH9urEMqXD+14Ar3lx0/3DZdsyPBW038sUlaHa4bhkOkVHS5gduikvagzuXDSbLPxkkAyF2usbJ3U"
    "jeFTXp7uulHTVRycvtsaOg2Yhn++3X+Tq7u1/17+yYjEctc9GYYh7v/Qb2dDZSv1klk33s4srq6PayHNOCwAlKzTv4ksadt+8p7a"
    "Th5mgc62KCzv+3ny1gezYa0th/cTegPPVk835gcuPHljZMOM2SMRPa57XlzsA9DaV5xfmfzq9inbcGTGvbziv8er90W4anaF+ys6"
    "Du/AqYkY1SuL6RseQrwwa1CExuJUOvIPQPpnQd6K5AUd8r4ZTVGpJ8fUK9Wt/QNSB4HUGUhV5hLiYZIAEi7WhK45QesFtLDMumed"
    "jdbkD6A98bgDqT3H1Pyd0eeuT+za05M93799w0fR7l6ShBzI5UGLRJu8QJ+p71BDCSgVxrX7LnAqvBqANwJPf1KKDBFpc6bPHqhQ"
    "g8WewW6/Ep+fYcyp6vIR54MdL+RNTf+//+v/huFzQA0wCm9ZVIXHHCA/6MKrAOQsILnrcUS1H+QpxqMAGIbOAb9D8RJra6c7bsHD"
    "cXuRcAqqgFXDWj3cv4Jc2KttnB6V4b1Pf5rckuyu8BkS6bf243Ev80Z8Icu7RPhwCdotTwGxMDnP1lNcekFldEHo/MqpJq/XN/3w"
    "//4/H6Y+WK669Oq40cBXMrtTmCACXGmgopE/lxQVvqxD7A904QS6D99g6QAylJWxRP4Mumb0TJQ6UFbypkypMpKfvq9SdVZdP6I7"
    "V3NdKMpW0MuYEj8+EYfmeuqZ47YKSXZ4x3nz6OM2F/kjaO6lwCnKEGTgflKIRdA1bgmkBaeuomwv6qrlMSX2H4FXJ1iyaO5U6GZm"
    "ijkU+pbpj/UULGI8s6B9yGdggGgBMjZuqiMfgl2cwNCMm+G6TnBndGFnBsw6AcI5x2BftdHMpMVV67LdTYCV+LTYfyEAhjRcxhqA"
    "I0ezpGKqVjW05DyQKlWwLI0OGnnYB+ePH3RXreMG0Gc8HBOhmyh8SgH3IDAkdZ3Gv6IJhc9E0cCd19SfIePFHFgQeQODGkmxKgqw"
    "9V1MOdeAKZx+p4gIiKp0ZasUPXsg5SjAtQEIzjk7ePmK/c0R2K/wCAQfwk6/fUN8vqyfVU4PwchiHg3PYtOvYLDN6xNKT/E7dsX5"
    "z9xs/3nGKlwswvS3QrFzWHXT6cyo06+0B0I6MkxLafCvDf8jnvH/2v1Lu5sONEBSJlFeJrfXUsV/Sg5usUsynhPis8YxNFsY/zsu"
    "ZvV45Xa8Sfwh5pObXH6SH8j+yCDQSQvFkMzKzejg0uuIpVOmk6z42suZP9GoiKHVYBQSN6XRaMnN5KAQvay7vg7HB+O5iRAUwqFb"
    "OBwqijd1stwXG9lVf5O/BIdyKbxcdkq+uhgMHYJgjsaloC86KR+by8iumDzuhiHuWAyGI+PwYKcGQ0pSHDZ93LG7TQ4nh+ulzUba"
    "yXl0dg1fxGannhgWjt117LRZb/z7yXI3LNXYZGQ5nAdvk7VwFNVWPhdIzg5CMnHaTvadTTTARxaleai5HIq1WGTZmwzDUqw2kmPr"
    "ZFDhc+P2Ouk/hcTzONBYnM7XeTwb7nGx3JqP7jZC4BKOqfxe7Qbjl2qgr2ZWx8by2ORCxdFgsFiO51VlkUze/LFNqVNUls1SJjEq"
    "Xvq9WvS4bkxE+dbwsX4ulD9XWqVN1N8OLYI9eXxajw/Dcn54PnBFuVPY9dolIVHKHveJtNIVSmKyms+GtsXOLe0vnwbDmD8Y3EaH"
    "vmPFl5jFpG4h2Ag1o3Vfby6rHV4+XU+jcVbmc9F0cltt+eqrQJsd+I4BoRrmk0H/bS5kz9lsWEwnomo+MWLBmEo9uTnnt1U1Uqyd"
    "O5sxn2jM1u2i2GMrq3YsPojF0j0xJ80Po5zANxPz4FoOtOLh2Zw9DorlRHjDZxRpH92EgsfMSVmEt7K42ib5s3jhtjOuU5SXWaUp"
    "ZrObyq5bqA5CYrQsLcOLiG8Wlw/FdX+X4/fpcSg0jtXr3ctglOweZ71llA8NpeJByXeGkZ3Q5ifqsFetLeuCJF+2Uia86AXaC46t"
    "n5axLD84dPwNlctNgul6fFbq5xqFG3tM3E614mIQ7Ja6G38mx63ViLIVItH6QejPhVAx5EtGevttubisZbeDY7UlLvz94209S66l"
    "yLw9zh/barS/bWRG8t7XuLDRUaHRmgc7ylptT5RkbZ+ptxZCIhzLduOAuQzS9Xp5lxlxQeHoy0wG8kZtBpMzQam3T77dOpNeloPV"
    "4SYfGB1Og0XruI+w/cRmxPeEmZjfHNRKPtJp1LlkJX8YnSZ5UZAr8VAgNvAV0ot8Ntvhhrex0OtFO8vaVT116r5g+RgR+t10pywE"
    "du1yI5PPsKFDe3lrhLnT7JgdjOeh4fyST0c2vWDfX91sbydlcMhtz7XKUlEik3a6tRTkfmwSH9b780F3NEj2pUInKrXLZT7e2Ibr"
    "vYxfaAi3Fncd9IOdULGQGY4qizgntxf7dfxUDhfObK4khGOHdp07l/KHfq93qdySw2r9sJLK2V1IqO5qmUNfHS8L17Mk+qpZpTrM"
    "xRr8dhO7lobd3ny32nTlczp+EIVY/dg/5fLhcvdUGNU713IgIOQzyex1P29WR+liY5grL4ReI5fI1k6VbK3eLG5qyWKhuspd+4dS"
    "9Hxe+0Lha7N+mqnp0u7IhSVJynQL+SovcbHKsS7P9oVLs62MxXRjm+bW1/zGt+hz11qoGS7MCsd1k+vJNTC16cF27r9UD52Nb7M8"
    "H2PhRWW7GnZi20uselTjldFpLeave741GbPBhtCuLNhRozkEJBaOxgBJ7eOl/Tnc6zYXp96+WNzNkqt4Jy6fe9FcNS+WuuX6Lnri"
    "CgE5N8xUK9vCiivz/ba0O4aAEFvrnkZb9naorZRdmi3kj/Vasx0KD6VdrVuc78rtdc03Ow/Lm+BpUm9cpPYsNIjWBdXfq5z7NX87"
    "n2ynQ+V2K3bOzarlwCmXUbPi2L/2b7hJb7jI9pR89yS0LpN6oh+99tnivOyL1AZq9whOhr3m+Jo+lFpqJn3xpfuNTCnQPlW4biWS"
    "WfWCo0XrnLktK+E1W+n1O7X4fh6ZFfmLMPDNV7XhLpu97srZVaOZrg/H5dG2XD4fs/xRPm0mp8s4sU5vlFquuMwdyi21HCr5/Ov4"
    "aD+brc/H1Wxd57J1/3pSLU4GvlVjtPbv/OfWfhweS+fZNtEoLBolqVDzn7b12WHmr2R2Uo2TxV6mzZX4/GDRaAGWHvfX/AX/fLJP"
    "RLKZynmhKq1AxXeubIRwEayfYWe2aXNsbcTWK8qiWzmE1aiSXeWT5fl11y6xY7FQ7m2H7T2f2E3U2zw853ppQVx0smo/fWNVoXBr"
    "xTfs7Koo2faGXV1GharSyLdXYek6Pjcb8/w8E2bzvpjoz6/Kh9w5P+uk/e10Ji3NY+xeGOz5aiu7j4uNpLA+7Tb+USNTj4riJb+p"
    "dA4xf2vdj4aPE99lUayUgFyc6WQ358auHAgOmsIiMhyxgeglulsc1Hy2UM7k68tiJCeMR4XkBazobdS/UE63Zi5ZLPGjoXTYZLcn"
    "+dS8xns+sKEmQ+nxsJJoNhY+Pn/t9Xm+PAvuC+JpmBbKcma5ilXn+3FM6Y9nfL96kDZ8h/eVxrN5rhwfLduDQWeWHwa6N3EeKY5P"
    "+8DwEAlmBuXjsC7Opcy1M7luq9JWrCi5EMdmVmuJzwzbuVy0sB73M9XurHLpd6LJ5aBfbAeEgloetQtCtqxOVLWZ3x028uqQCDQz"
    "5ZKUyB5mjWYhmvWBzTObKI6r8eC8vwU7eLlTr1f3A3U+y9f3YqXmn1zZtpz2FTOLrphjeVnojtO7ZbyROLcltt3PjufD7GCT7KdP"
    "ebHYFuLNjVQsHHqD+rDD1xaLoAI25O1K5OTQaBurtIsK1yzXJqtYsDPvB6VOcxEbSfHevB4dBysVsPTKpWxvlo0EZ4H5Ph2ph2HZ"
    "CVvkG9XzIlHjkrt95dDthYb9cV6Zc8VzSK1sSu3ELhE/FW9sOTYqKUPlEkmf08FWYy9vpXB3UD1EjoH9iT2H8sP1KdsY3WYZQPHt"
    "8/CSlfoHdn9u9LeR/Xx4S8fPSmtTLRZV/li9TRqlXnCS3V27fCZYChxzoQXvuy33y1I+uewK5/NEKfojChu83erDiXAVl9VRV6zW"
    "FkWhnu2LGykfaW8GY39t4+8l4i0+wvnz6cRG3VYvUX4xDmXU5b4czI6OEXamZsaKdCj2FvXD7jqqK7lwWx1GB8fxcR/on0SxVNz6"
    "g7tDAvSmWqjvLy1/4+BbhocKv+Z7/v4wHczPdsnVeRld++aB1vmWFwqdC9vvibHjQDz3/AWlv810j+HbRcpUyvXB6TKK7XwRPtds"
    "L86AJWd3m/XoMj9z1WpFPJx7gVMv2cqeT2N+OGjUO9vhJrjiu8Fcczbvnerh0PxWWpe63flwKyYio/Y+dIjK2cKxxC4S811+l86z"
    "yWw60emEk/14JrFrTZqFyqVVkbb5yrwtdWNKs129DntzX00J+tXRuRIOXM+sD6w6IHw36pe2XAn0Z/31Jlxq3iqtTlKppesbab3M"
    "tNsDdtDOd/fDIXdu5eTqaXReJ2pgS69ux4G0UM9fOvWZ1K+WinWxUR+cl8P8VuhVB5HFTmKDzUDelyuVKqPCqVe7tteDbiEybrC9"
    "kXDt74fFZimQT+cz2eL6WB8W1vXJ/FrdxLeBXp3LdVrpXrzXWRYmZ+547c7LvcyiGJxE/Y3wcXjIXLhL3N8YXiudldiYBBrdqLS8"
    "ZZYHYbwU2/XQJdkrbfla69yt14SjoAq+IX8QlxEhF1pe2JVQ268PzcOpM2l2xH4oc90MS00huTjl2pHS8FivXOVCsBgLRQqByTXh"
    "bwY2pcEwLNZqnU16Im7m7Eqs3PbteLMszrKNw/7a2AoBoZ5o9VZCNZJYt2eH6qwaWBcrFXF7CXRyitCtH7uTUrMdF9hSu9sr1UKV"
    "/cAf36/6chks9lFWXY3AkpnDOazFK77cstKNp4vRzLHbLRcT/sSlOQwkc91Qrp5jT2wjwkXlfq0lzc6+FTglnDbj7q61P+03itoN"
    "jK65qzQP8uezWuMDuejGXxcqwVNgcJYFSQykh7nmKJE89QLhqK9e6HLd4eTcADJoNJkYXgOSlPVH5pVxYT0ZJjuZ1VjNC3tfj01c"
    "2VpyXL61a1m1CbaFcKy4Gd0AY7zKld6hGeoPwc/5ZVutZkbNXjV8HLV9wzGrZI+79GLXzsqtZXCrVGNCPXmpypPjtjdLs8FDZlPb"
    "DYPCdhhIFI69jJJN5IuReGQzyvb8NSC1BhKiL9Oq7SfldLYlCUWpXBskAvP+7XjYiquGEImPhhnpsFvXu1KnmAViXXU+u/kT7LYr"
    "h46h5GrVzDcH7XQsUghW21GwtqLV6Cg0Dp9W6aq4GN/yu+3mNh4W0v59kItO8o3jns1MTp14Us4URuXOppHh82N1Foi0/dWZ3I1u"
    "fKV6P1jdr6/b1S6WvfTGPVFKBofXZHMtnDaLSkeNS8VrK1TdRZVgobm73g4qN591i9FZdFMY8mCP4XfVwmrREEOXw2VS5VYlubW6"
    "dDv1YFWaFIGs3AyMTsLoGh0Fjo0qmLvYciL40/7hbtMcS9JqnFZusXH2JOblWfNar56Pyfw5ec4MG2wFnCCW7UhxcRAHdb86iO5r"
    "h0gaHDPFQ3fZj/ly2eylOpyUh938OLvOBILZOFdeX3qHxUTxnedcK71cZ8vhXalSbaxi/db+Ei62/Pl4dcHvJ9XgbHk5NsaRBFtd"
    "ZLZFPq3Ow5twLnDe+go+gYtLXHmxnoyjs+N6W+9ds2p61S1P2tfKuiKVJnJ7GQ9GyrPsoRRvFTKFebc5OnMsXwgGb4s2V6g3g8fQ"
    "+HpqS+Il2I5tTofVOjjic7H9MBYAiJTGzWYeyPS97nJeliJAipS26cOt0ek1lFOiJvkO9ZyPmx+B5Jo48rmbvLkGT0fO58vJo8AC"
    "rNTqvBXodeYdOTo6LwML5RbMVDN879hrT5acPz6rX1rDqtA4lkqFhJ8dV6OZXL+gxkcBuF1cbtGKPBNb3WBkFm4C4hN3i9Fsrhwm"
    "k1YldNpXlr39MOxvba8hX9QXmdR66kWOz3alYbWtLlvN/Pk0O3QqNz9XAZgJClG+EjoGVDY+8yVCy9lk2Kn5fcPbOVpREvtYI1gK"
    "1zrjoY+t76PVIr9PVldCuiiPapNOtB65XQR1ISZv0fY+2clOZmsgQoQi59no1GPjl0acPRQ6/rWYTMzDs5sakX3gnFlVWrvRaLQp"
    "LZfzuX+xaATVw1GIT/yhQS2zygz7udVqke6n0430IV0JZKqHNNTM+Gbda6fDtnlpson3Vpl0RukGVmA9Fm+FkOSLbpTk4ji/1Ity"
    "uLtctZd5bpXxbfdq0Bcul9NS/zxunGKnRKauyPHz4TofZhKsH5zz+vPAjd2p/W0sHSndxMa8DvbHZHIT4OtRXkhfwsvTOjZfxDql"
    "zSTcLfvOW7V14fObTbxQqwncodZoRxYrv1ru128lf2mVj23awzHfD1+ivdiqOVNW+22pWNldz8p1Mx7NotlwzV/Zppt7br485TPg"
    "zDHpLXyRXmewWFeS+UQnm+l2QtlS/7wtlCKX+S1c20fV4im9618T+3Epc6wO6uX8+DDcVGKxgTLpJeTVYJbP8UpzkOluCtFANX/Z"
    "3Q5ZHxBZguWMf3jwJU6B6roY2KzmrFoMJZRinuMy/uWulsjvJtnyVR22o0d/vJQMVFYd4XxNHqW+GAyOSmp2VDvP5W4kMowtVulc"
    "qyzvtzOhzl7bgX56L2VO1+Alx0VbQN5UMvtDLnHdAsYbPm2CvfZmexzv1PGgeGFHYoaL19PpnM9fDSzDgcBEUstJIegPxxuBTqCV"
    "P9xYrh/mi7F+ZtVub9brXiY25keF6KnWaIX3SkYMJ+T4Tcgq5xE4VeZykfEhct0EjrdBAuw4hVPjli1dF4Xtsdxqj8SA2L+sTuCs"
    "WbzUhvIhGqmeC205UzktJmFOjRbaK1A8JpTnfGddOfeCkWhSWapHPq7cLsl0u7Xvds8nIdJiJbAxLIarSOzIZtajZrU0SwhzRQlf"
    "QyGle+rtJvsMX0puk0InVg10+UBPaYNdJT8++zOJ2a0xV2aDW7sZzdYXhWupnx7M5FJlvCgVcq1DrHXa9YblW3cSKS0L89EsUw+n"
    "w/5ieVWYSGBFz87gtLlojhqJZXBXnywv12bvOpmELypbbPVYNlQvqOFSSODXaWk15IeHZLJQ6qz507JcLKm74GTPFwS12PHVRuN2"
    "pr+e1I6d+mKc72/lUjmZqNyWq8pkIWQvQ7A/rhrF4a3eqbUnvU603AodmuNks5jscSWJzZcaUmDSHCr9c3OVjA8jQibErud+cXMY"
    "zSWZTZcTl/CmlajeEtvxaLcP1aqd874ajV+zq2AwqYzisWJkpOb33dZZzleLyd2lujiWj6Eem0s2D5HF/KKelXV+mz+vcr1rKdfh"
    "zrHiOTOPnMrbXqQbVSftwiISV4RKoigvstEgX+Tjt2xgMeyI/mCvMZlt15NsbdNfjcKd4TKx8N1my2AyE0weyrnh7OK/9fo5LtTq"
    "tROnbkIpDdfNpi9Sn5VWJ9/suJQaxejiUsvw+1EpJoUypU0ssp3F1iP/XFREv58b7w634TyrJkunxJxtFdbCzpfrqUXRn8vVyny1"
    "IYP10N+2Ze7SYn370pwPzCZCIrnP+KKH7mU0ufTqg/TxEKpFE7uqmr8EsoGcP7Rbrm+VyEpkS7tqcbzOrwDbbVxLt3Ku3stf5zF/"
    "mB/Lg10snOlWg43xqCVJvfxlWej706fBXs4ArlNL+677EVuJVi7lcaIr9da9tm/C1U6nurxe1Ie+TCgTqh9ilewgoMihznrjE9fJ"
    "UWPfqylAUCpwg110GZ4scmxXqh3PrXQntgZN7WKT4uZ4qkdO3EwJl7eiGo2kZyG5Ep6VZ8pIgtYEMSWbj/j9a7BVtJNbteuLJVrL"
    "WLUnrNjBvpAppqOZ/cp3XfmU4bnHLrfNyMI35veLmr/fG8faaucwClyjpyzHrYJNZaM04nFAOZP9MrE99vhEpsKzxX5luyt0Afue"
    "5JTNMdvy+4PVXLkn1EpyrRBITrZ5vl+P9psRsdHtF6vrQ21ebraWuaKPO8Mly6frjVGz3S32WkogWj5L8/GwVmxeOmC4y2BNbtbY"
    "fCiwXFTzkWwscJLagUlL9UXacXZZDPVa5/6soLY78fa8ppaGy/Sps+/0gkfpKF/2I74ZmHG1ARdJb8Kr+XGcjp96CYEX6rnzzh/3"
    "xYbqan64Vo+hfc2XWPrZmy+eLIn5qDBSbvlINZcYRyOX8HVQKUZz62o2nhSOoWq0MEuuA3xj7t+PhVzLN0hLw6E/Po7VK5t2bHCK"
    "LPaFU7YwyMb8l45YKKczy0hQzGWT5w0HCOuanvM9OXyoHJfJDrrKeJoy21cuQuTz+E0XIbVAE12E5AdqKF4VQ7PxYuDrVMv5zPng"
    "a/Wzl9EhfowWC5wMnR7Fjzc1HJ6F50s1WR5N8tUSv9pemiNW9YXHlUQ0dzsqCTncO4gSX872cv5J+CCvJgn/YcW1SnJYTRbF3v4Y"
    "SoSvxZJ4ioVb0ZgPbBfxUrg3Z7ml4svtVsvT8SbLt4Os+ltLX7MRHZ5GcmEH0nZBedAaH4dCbx5QxVtAAegXOp1oIJGMczK3zcrs"
    "ISB0+9lupVM8R5OL2S4cTa5jvkS4EVGFVXqVzmbTfH5dEYvXJBvN7S+XY8t3jJQGq0K6k22vl+t5fHZYXfzLZeTY9YUOq/6qthJu"
    "82MruGBny/Bpdl2PglVfppnu1CrRnlIKhAKcbySXy4V1sXwMtg/Nxdo3moz2qn/B7aVVP82le+lx1le7DBrLYCARD9T5STufbk+q"
    "/lkP0P3qosqFdNzPXibXSSebHCZnu1G1dWwm/f54dMdmAS8vrNRuZVap7ZNCWZpzS05sLob53DJwG4hrrinnboVZpJ7vH1q12WZT"
    "6DTj8VHtqPi4QKg9XASH42wsfmI7heFMFuPt82rRk2K1o5wvTG6XviTIjci8fkrvO4vqcKTuwBm9699H2rl0sV4+hYORXXp7DKvr"
    "Q7qfXRY71/MVzEa61Fvn9qPtWZhlu9cKELAvYj54CXNnrhNtsrn0Nn6odNOVUI5ryZdLqVYrlgvjbTu9WCfXbVifsI/MZuFM9Nxq"
    "N3PDpJ9TCpnWsl/vVAP8kg/k58VMcsQFd6V9AJxylqXFhC+vc+NGwqfkynU/QEmvvGp1Z6d9PdNgl4N6PDJrAQEBrJMswG+2F0yy"
    "gUObK84XopyvXMvZ/ITr+fNRNVAVGwWpoOyOpfi+W00sislGpreWS1y+l23n8rm+OJ5MGo1YIVor9PPJSqxXFITWVU30+fVAzWfy"
    "u0zgWs9mm+dwli9t/LFIOX4LF/oRPrscJovxQ1wCWE6DfTm3UEbNiphL5y55uRAWDyUplG1ttvwk1vJLsXQtIk2W6fKqvBV8h6y8"
    "i/G3YuIstPyTcjYyrEnKJF6PD8eT9jG8kvPxzawS2Y+5eFKM1OqZ5Sk4GbCxEKcA/pKXsj4+El7169xgUykug9Vh4XK6DkrBVpYt"
    "8cn26BALHvOjxkDuzseJwXHOJkptlg8sd7FlLrjJN2Nq9JSWF8lhhW9ws1I62Kr4i9Vz4zZoKbPOpHrc5zNdJauGcrndOhvaJVqN"
    "9cAfbM+Tc4HfnCbc9dzNbYu5/iK2z8Xl+boCeEuyMGgluHzgJLTKvUSgVWvUznwkqXaiYlu8rstbwJbyWyF5GTZ8glRNAvIJBzeH"
    "7rqQ4Cv5nL8xuyT4wCKy3EeyNSXZCoKTURccfFZKZtbL7s/bVWcVvoiqb8KWWkLItxzFdrWs0toCFnQM1Urg4C9v/eluugWOWpNI"
    "vNhvxaP9im+2bvbP123FPxo0QqWdkK0uFvX54DY/34Kl4JENgyUpnCv5XaeZjEY359FEUXh2MwjcwuIqHTuNRlz6yiUyt3avlpE2"
    "yUl+nz/HW9VJZXX8/xk5jx2HgeyKfhANMActvGCSmHNemTnnzK83ezADwwtjvOiNoJbIV6/uvUdVRWF38Z1F1KnYl3QwBTqyDMv4"
    "mD/kqydJyvPO77gWwwOemP8s30paAC7YmNXU3wioi+jlKDN8esYnpmCLyTTtGfIZ6yJe/81CrKkYQa28PxzqQTo7MDidmceG9vaE"
    "lU7Vg8GiSqj50/yK5UpMXW3sKieXR8KF46aYlm41l921X68PV1rTB/wTU0YtMsEuc8q4NVefkVO0RLGtpQN1KF8F7VUyadMkDCVz"
    "DNbnbkGqoDwKJLBgiUxs3/59s5/wAkVzHUBlKc1GVJqGSzXYfsPA4Vh8OXpcX53uK2eKYUxY4U49QYMEoTGehC9jGoBTchzDUSdF"
    "+MFP0UyuV7wdYKIFpD7pxEGDiWveTPleefQYAU8FFs2K7N8fyzAJt0KG9wJqpMVJ0pPaiGLnigdoU1bhnSFnBJ51zflFc1+cHJ2X"
    "fGivLmXxI4UqmDnEV2/WwTc4t/IKbgJTrld/CSnYkvHtqy1WPI54RnqFHWR901wJHPpM9Tb0CiXCUszeS31H5WAEs5Z4aturTxk1"
    "hi8RTYQ3mW3hE+bkupwRF/2yx36SqnOqSGh6epaNG2MUej6s21WK+EkFD/uTydtX2yESg6TZOZ4uuIDUjRA4xMe1UIDxacnKgkdA"
    "OhwJGLl5hjeXzKfDURf/MdI34pmAiwNZmX76Ux4Kbfw+GrzS3Q4Ug+xdy12yWfEbSfEKv6wwYelMx+7qOR0E7Df2bNnnt34hWHO2"
    "pEAazq2tLEhTHuVHmqG5BJzVbW2k5zDRetqQJ4XpJYgtxWClClVqYQExyYpEPn6n2jAJC//Dk6j3htce0w/N12xYtpgivzafa0W6"
    "EqjwgMgYrpxQyYVtVRqFqs8a1CbpCEsMGNSbG5pWMNF9f1YdvolTExFyArOeKBkk8LszwZtXoSYuybRlolZ8eplc2CokGJyWgjAQ"
    "d8lobdTEppbgEbKL3/Vl12/ogZPH7F6/qHMqAgUHamvZBIyYWdPTZhit+qR9NBcVKHT6+aGzj8lAPS3RDXnH9h2YIdjiLI4UfVMS"
    "tmKpM4V0xSNdqfilWF2kRkQ76Zb27rjPRlBy69pRrTUAv1Xz0b8vvCD7Sb0gvojQ0EeyQ7QS3YPNaYnCPQxAmRgOpgedjobOKEkO"
    "AES91eMm/7ONBsy4RloRUcTWwdKRENNpilNUUkv460Vylx9s6fVgtFv1w0GGbga4CqwOznwgOOZV1ysI6Adg4cG+g/qaDJc+/BUm"
    "XdvnNIkkiecSMc9FGhVFznqTm6I+WkOvdfDWti9k4+Zb9P1YBO0jiOejH95nHZEwoyJqvzNNhSG6FmARGcH8m+9bB/eBeUuWMFB5"
    "Z0T18HH5Ulj1mn988jnokukj/Sb71wd2/+nZ0Xoo8gWXpDPNj6SpvycsG+t851CvbHwJfH78wzlA4PYufbXT4EFACsVOtTdsGPUT"
    "GO62JUmvSawJdDTGV6setwzl6f4E9OBoMwWrcErZDE/XHEtbtxE2heoJ5l6XQZI5zPhE4YO9SD4fd457NkO3pU3bWOw/dIX7r8Pz"
    "o0FlQ9k+4HJsxMtCrfxTKtFcfjT2c18BmQdioyQNKjSv3YSmsvDF/NxRS8jWTpfnzzZZKRR27kHPjuUHkkjv9ccZS5QILty0/Xlm"
    "u1SVctlWPyKAGO8F9pvq9xtCftYHQaZfcA3auCaFXk1W+l4SABVL8cuQyWB0L6FJqX1E83NNlcrBQCsMjeTpT0xi4PNoE1+pVBLa"
    "EwFaqs7rgS9dIwXBqcDrbHFNpQyCLn/XCA1Gy9UMaAC0TLbKyPTRUuZnsi+9RAclr/GoU2nELoBqwfx3R4YWvTwDlS3IKBBN6lcZ"
    "sGaknRN6bU074By0wR+v/GTb7qotJbDk8caIwqANEQ5HqaPRp2WwK55NuHiVcmBre3N3lIKUtvAKaOQk2kgPdqAHrZPpt1y3HSs7"
    "ipSj4hpN2ht7lhI30/wI+sPWJQjN+kv0xHyvhkcxblMr8GtIhLnTPa2WbckC+0PTmnbe+F4YSnd0YZvp9fylE+CU6ME8GnHTPprv"
    "j7Rl0Se9o3bCf9Vw/UAmD2/kfTyBMvfKnPRdfzJSaSwuoZzqMFO0QV88910Njp+f3Nh6OCUKJzyxfWtrO1Jokiq6SQ9RpSk5lv3b"
    "7hXUVOdkCP+js00A3sljyMnJx8In7M/PE/SUWdC0JJU8C7FA8FKn5r2NqTQ9ySscygyTSP/+fnlIHWMxxcz+ShtQWPvwJijxy1o0"
    "N1qwyi1tWrIpux9xHNb4UsQM82ax74mQhdD9hJaHQ1pSuaRIPfw3yu0y3TGLalaA2UnKSPk24cHgLdr3dKWJJJ7GL9QeFdLtmwJZ"
    "Bwsq7RLm4VvV5ujJ7dK8WbTgKC1UOSbYL3mKow3BNw7W4Cwgi9UriirCfS4vrweFp8PgA/qEFnH2CV0kEmxjly7XRs9BpRIe34/O"
    "9XD1fRXe5ufgY9H2Z5Nptb/jLnrjPFL6p3DYfSLwYicXcjAiyFL3QyDVS00xoTZAUxhCVXPPWEXT2FAjz5qOANAheTRAx4qwQQI7"
    "v+odhptgfJyaShBH8y+pLqZsKozRzpWNFJnByoCEz3v9uIEs3Dni4k6oAG31QWX0rCnu2X7FHI9wBSEkPhc9Lo5aegSae4LGzH6s"
    "gYCvpKjK9s2o01uiy3rChwbqhH+8z1R40imv2rJ8D8b2yKdx3xxXY1JtfvjR0WdsxWdrm17Ph0AW/oFPOztAfKOjVbzDKaWDsi3N"
    "L7DZ8YCTYx6wrbyJtodvrYD+FtmpIl1Kkn3Ceg6gJBQ+QX9fj38xL5VwDoQSak0OrJlxAxy9wUxVzx3NhPbQv1MU0SWaY6+m8pb2"
    "OhV+j3xHYOjufM7+vW6ozX/ET9XCrLD4uAMFwI5Qt7DHG1AfCcSbNhJp2gizTgldC4VstVY+EdnsZ30U/oa6J28gbh3kX0gsDwL/"
    "cVZfxsn19sJwlWGxU9iLnxyAf+IvQysUPXLL54Tu9TlGuuWMhFg/PvoZjWJSQ8g99xu1KrriefZ8eQD+Jh73+UD6C5Q6O4HfgthE"
    "NHtcj1pt+DvRNG2/Tc4HNFes3z7hj3iyPydaKigqRFqYR3bXvzS2v58o2ywjvBE/FHqrLWSWtk8Newo9GbNSPgcvj+5mGOHnu7+J"
    "ImlK7LkIAGGVSNtPUx0IgAbzJ97LqZbqy6fFmq5Zh2cDGLGlEk8SV4OWQmCkmuuIfR9g6PwW/qKV32D2TPuN5hKVKA9JV89dj1re"
    "f8uaG8qXnvSFk70sWQOF1ni79hkXvOnCh+2KG2rBRMwfBGNJ9nXRHwLA0Ph+tW/YTEkjEuhZUfN6W1rRK428/THehg82bO29bMDT"
    "S5Rp8jk/4oMDbdSZC+4twtXXH8osWUuR3NYJ1b0Rb0l98q+xyTsMbGIIXR+9aF16+rK223byi/SWFGl182uxT/TrZJzMn8I2IDwd"
    "abdax86cJdcBYKbqHANCXCwOi0V5IW8F3PfCyppFa8nkjyTzr8J/viSCn5Xyomdr8j5B7RoLwuGTA3ivefz+s+maJyjwjw4uE4w/"
    "eJwpGmk6z8jaNtnMDy+CEXZPfZM0NwJnRwRl/WcjZ3+WLLlz+UpgqnmX3zdd0X4xEo6TpCaQwkD2mwfi5wMEC+PXG5G+OW5I0hSg"
    "n1Ng4BBOyAUukdQInmVoiAfEwMgA8/xosnwH9fx6rNdBssPtfQ8CE/3mBxMDtuP7XCCA/mshDXmjJK3Q8P9aSHNY16rNRqz56dM8"
    "9N/oxSZy6iIdipxBC/gA0oz2Az/Zhy3qC0gojaBOjERS8BCEn0kfWRWhFA4rkhUAr58X5ADOBpJ97gbk8m0Bz9wrPvsL2mSfnzBw"
    "srrv7Bw5SKlOGjjHvu4uSG4GAPHhFRvWmwZVlYNs9Qylco223vgJwLTXW1T7ayaTGBa6IwMaSuqfbhrknkaZ0fPJANk89GFBXEF0"
    "QovQcQ2nKjCclJw0Ir5FiZlyhD2EBSkuBEHnDLTvH4xHYwZ9QFDvgwnxB4pol+uFTClq+EAYV8VDPdKKvXGI1NGmNr1Qx9bjUHvD"
    "3vRA/qYJ/NVpECMOcf3mCtDp30txNTzFXFHzCkoqE4NgJvXyO3koRtEunkO31Idq/CWoxXjv/SpTlW9kWvJrf82O7rzZedQEVSzv"
    "G+E8nGQZRGa/GYUODT6roATUjtAl/74NiShwN2dMMpNwONWrJu6pZ7JPqbFlF0+t4jgcx8OE7oRTKLAeWyAUEGBXBZJC5fOZS7I4"
    "y1IRQ7KOO+i/tvJ8fs5BTtkQkMqZz65iF1YrVKaC7AGcWIDEv8JNvI2g/xbv4HRYACZsl24xeB8LpSCT0Xa1QKTY56KYQZsI3lSe"
    "HteFgxfOSs46cpXYUcnU+0o/ZMmho1TPFblr7sEwKN5L3zzbqIuQJtXvw3UHEJC4mq91I+HjDRFfWiGlx8+mLQ4gJbRtCxzv7kX2"
    "QV0mAlhz6lT0adu0FazlitzGUoPeWGkBh099mYTsCuSN43yCK6BCnau2+Un9JhB/SO37fHGzFlTqc8poKNGWcgReGdITeq31XSvs"
    "l+QtOcHryrx3A5y+jC9A6g8JBY8kk0/QpHBd4/5MEb7FfVr8dR1pZGTlmj7xOpJh9QqH9lPOu/pyCgDD9yOs5o7kc9V9asnG3ubp"
    "b2MGBD2Qw2xwVt45ZNzJkU8Za7H+VS1ca/R4/JrVlHJkJehUVM8d6lvXEdT0L3PFh8mhl35g31x1IBD16iHSyPnUfODUyePRLYYQ"
    "uY+3rHdacEBFKwkT0EYDjG+igxqHVgvEaj3fKl10Vtd+OVaZqMQ6YJGEG9No7EaDR5vL93AmvuCl514ADy3IaQqlLWAqxBb+MC98"
    "ZiOkvvFTwsnSjUMJvyxk0o5YPhB2/LE4t7bxxc7z1aQ5LtS9lmU26sg1/mb4lsYEN0sMCVvXszscGIdzazuGEKlXkHfe7JLwv4Rh"
    "UM8y5i8mvzbwHV3G6IKIwsuw47rPuQPqq6055zz3AuObuf3Uu78JM5ELX2q4+7neQFcx3/uUdnGrmqeCYhCToUPA2MtoSM9kPBNs"
    "x+29zk8Xbj2wNLxl82zq+tYPWExMIWIZaF2zgzgvox+glZEr8eXPR6Bxizm6OhdpYCZ6kjsLIeTGj666Oc1qveuDiubDT/OEWIcd"
    "MEkNUcFlmCF+NWYqvziyNqw9tJJP7ZP1MSNYsv1a3KIqIpp1MzaT0Vb7a/iDWGlCG8/IbYvcFtOJe84NUKSpytUqJFlgO2yDVfOj"
    "zCi2ayt/24JEzBVyEF49KBYj3q6oOPTWXtS3Y/Y7IsMQlY1iYvvmzILaU6fO7p1Gm0qi4mlS64mriJaX2ipG/d7ttSPcjRqkFdMN"
    "g9GFBolCU6OTDFh/stXbDIWZw8A4QapxADOgaIXYAcCUVhSKyzpp07Z7FsX+FfZl1OZUCIFsl4dhvGykitHGywc0QIXyysrvkHcu"
    "oc6vm/v2T1G+NdF2gmw0M2lkEZ3hZoY4kvuT4kdnxQgSFps1BNP7Yu2XWAki7SJKcEJoEKdkAwgV043ydI/2k40VMcm7+6pULs4b"
    "DSagvL7YYoB3pZNBLJ2De2JgbK9ZovaMGWz4IpAfd0/DjY3Yt/Nn6/vFh4v8dRWJZdVnaYP0IzwpYQBNGOQgGit0wxTK6yMbixJG"
    "Vm+gkUEGtOaGOhrJtpaBTgkbJmGunBLVtVYuu/xeGzqzmvkcohv8VDXi0QMhOgyyw6n/Pt0dPU3KxiGJBI5VFd8cVoiOSnPTHfPr"
    "nMCBIlmJml91f0qG93GX0QlP73lwrPxrKe7wyyKUGRPR/ZB++L3k7oBpl3sxkbv5miMgxt81Pt1XflXBq9wn81gtCbzjIcT0KhCG"
    "MlxNH7/C3eZ0g1mCO5z1AWMzec+f2SeBfjD30bOTe3E6d7Ac3ZxrzAvtNCCSboJwLIos2TPL+XDnPgOgmPNqWq4W/puHQsfuXfKy"
    "5B1TeYuiA1H8avwYP8WQYNWPHE7br6LtHIv2hywLCVfFDyPYz1ZNpXawsALcEND25L0s3AunHyErZ1mPioQT+hSQCn3zOqxjJ/J2"
    "r0tSCS2WdgK5ap2gR6n89MsUQa7UOgCYsTI+/Eb8GyectyI3zIPifSZhkbneT0eIEgBWYVLICX2INoAbTU9AtV5Pks1p5gB0F8jO"
    "6PmpcdfP0RY8vi02Hk66Va6nF3d0t8NazmurU8TF6NV8lXdoDfqLyBGvMjjrpD9M2VTXoUUhw/3+agdfMi+tWm6j/Bx8K4mhQETg"
    "Zwadb+ypx95m8RNHDC5Wn6qIr7ofeUM7BekrgBKnMfa3myEDfnAECcgZy0tUGavPI1LTye/2M8RUkn8tfYO+3xCOp22AMIvoAhnD"
    "CrUJDWoWgyOYjaEw3jcpZ6tzBY1jGbL7UinI1BkuukNajCJnUgJ/sMPGfyhZRjhpMqJous/YqOUkefPzJleCeRwbqKpaNsnuVLyZ"
    "ZH0OopiOdzAlkEez/i6e3yi1FxsLtWSLkF8dpDabQytCXiLEIcKixQ4T29i88tLzl6w/DIWiLiEuJ9yZWj9nvwF1L++eNHURcWJ/"
    "A7x/TQR8wh/7AcI1h4NgCctQrGo90drAVzTtIyar9QXutUdKlW5tTl71F0ORxY76tOkfQvZZQ+Gqj6DlD/W1sxs1lD7fGJ0DaVIE"
    "Av3KDWWAHpgCyCsH9FnzKCAJm1PVIRu8ObN5x8mGsS7k8vnNc9o8DCpGhq/plWP/UDdYml0Vqy6HWqOA6dKPv8Qxkz7dAqdoBKOA"
    "1s4n4Z4KgnN9xHKIYIW2pNWPwJSOGLG/3qItkGUvr3Q87o6DBcPx9COWv1DVaPGu4RhDU+s4fMQifXlU+FVTIvqC+LybX4vPWlzP"
    "Ycm7vwyFvA1B3zkm/BzbiLJP+gyEWBZqQk9gxOj2przi6ExfBOTo4cUyqAKBD1hWrkaS0ARUSXse4vXSlPgZvVw7CvhnST9hsyuR"
    "C1KUPGHdt8lhODP0UaKIxUj0JAHNuRoD0QbzctzVzTYE42irC8OTlzAkw1BC6xioIMzhAXMdgZOHThUTq4y+FPoaj2gZ7/Sg4tUf"
    "lvIDdrA+QzRfaZHKI/fDw5tmPQ7ALl/x+7fU6EqO8G9Dpa/IPgP9jz0S//lf/0H/m00SPfb/Oy2qrurfJgmB9qbfw27FpyV/L6bT"
    "czN3YHwWjtgi6RjnGL4hZPQ/f/CTFEYCLZywz+Ej5hMxN2qjzspCybdY2pPoadIo1HP1SuQ+6oFWiNzPRrnaBpU8OnXsYwopjPMM"
    "bwpccku/dklbJj2C937dYjYAwac8dkYIAIF+gkA+Adyvq3e4h9U5GaRZrnd1P4iIBqMIHEAaNjRBMyFQ+w96XJsRLCDkj+8Ecsob"
    "JwEjMI5jIc6r2HVjLxsruUeEeOQHPyCoq3mWhzW+tR3wKHfWlx9YIVGj0U8l3JNIcSNEPcnjeZ30QIPMehM+cXSkIz1t8HNLWHow"
    "QNAsP95r+CAz6u2aEYMQRgWoT7BQg6Yz3gbsd8rQ3zX3T8bWlgJ9wlkxfPL4liyN4n2oV98b1j5LnhnmIFHISrn87LX30WtXbBE7"
    "nA0i0pzvVAKPFoDrTcmXjFywNOt2rGHJOvflWlwMp8lGAwCSX6lN0Rq4xFLBfOfHS9egJjc7n3BExxfdp/wnKrpMHkM791s+UCBk"
    "jhP6DrXHUqHNUY/wla3J7ADIdCy+v7N0Wj75BrMrCHXrcwGGLTsCYgHla1O6CoQcdQrF0tHlthPCMOzwSbEN83JByBrQPcvfMHxZ"
    "Wnkr6+sIpXlkD6Wg9wVcfcXHjBypkn5Urty/DiIEfuqVByqUszTaERUbZIT/hMrLXEdzsrtkd+yDkovn6tpCfy2hwUUBz9eBQvz6"
    "3JEJ2GiaHVdnKcFG75crIusD+mkUPLE+fT2jAQoc/wBEscLHaxfEqJlmEnwuixJ93KIFtTqPwd587cgmvcTpiqP6kzxlmqirorV3"
    "4Sklq6UzG2AdPKTirbuNpHGTuXxK+suHQpnAfP1VDe8dCayjIhiESkEaa5rLRUZHmD6ZrKCzcoQ6cJIGGiZB2AszdMsKR1E+5sOY"
    "5G4G1gy5WFBBBJfvVB4TnjgNdSDjsNcsMz/7UPN+7CHt2Upvq93uRMU3HrKJkenAyaKg9RaNsmMlv6E+wldDLGGaxGyF82gMlL8C"
    "RSdU02QppOGJLWPRPBHphZzmXvY26BRkm4ITHTokxHXSLlG0kY39K/1r7T44B9bG6yxETF4S0o7UAWS2brfP5+j6RNAGR2ULiNoN"
    "nIvq9DiTlrQToMqlxW9nQcUQnA+NlwghJOqxIIq7ped932C6EvBA9k51ETmQ2UWLd0RmSSLeosHiIozVmqekWID7Lq7HNG4Mmic5"
    "TGCOz4MURJjsgg51I18BGuMOC9RkslxWkv3mKHf1JNNb3gfTbrzvNpo7l/OJXk7dD5ri4rDUg1iaK/3jClZt9dZV/5ZM58917jpI"
    "K3HO+WjzFcKu4UDX64qhXr6+kNfqGWeLfqiacEI/W3CSh39bjIJhG/kR79fZe9Oanl9lHhwiLbcyOUqyVqADVVdhdZ+72N7RyYK0"
    "iMzJZpUanLO9YVGdtiI/1x/tYUeWKW4DMzOkqzqa8yWB507mV31sNCqvVc0RCtrXij0iWre9/wkKO0DVMEbpwr458FMzoyD87Lgy"
    "jUJDPInnJbz4qIDdF/cuy8K99IHKCiFs8IQwM7nuTYkAfeXvltUETO7mmWHbqjwoz5TfCFNSdrqZtWFQCUBdm+ToYHbAFaG/1Dfg"
    "zDEwr1zvTnHwqmx8A4t8mPXnGngDodUn9EZ9wRm1vtLu6rhXCF8cKmSDn8mb4hy2kWCZc3XMnee24s+mZRNO/HzThmgduiAV9aFb"
    "XrgtiBW0jvNeMv+kOfV2aLLiCd0JaYnn7ThI60r630GdZ+BU7coByZmSwXW5Y78Ys92m+CjofvkLfOFq9JUe1d+CWkvVTA6ua0tp"
    "ljaDTLXc9rnuvP423f8QXeV0eDOlFFe4JXqryvRnuzAkZxYoJ3w9bP24sJ72NddgqoxwoYrPKYhK1YtSt4A7lp8perLxAtG3YS/c"
    "WZ55TPDpdM47huPsyDlody66DGlIPlG15Ygrtk59Zst9xDxOx3MC0h1Q1TlETwhwJSEzotdKvdwwWrZlJbR4gLDgejkNiJcJT1ed"
    "SC5CiJXVccQgqAjDYloBUwRiUsJ4zCNLibq2qtJ3Z9+5lk1bYOCANusoGkC0bJ84fBYgp+EcVlfs4KnZxX+TJF20MwCda7psdDQi"
    "mNZjh5KTUq3HzqvS8numtZqx+3DEtmjLotH0G1yR1xgs5tLHjFdR1/QreIP4SeslzzxWuD5xXbeiqzfefXSlbOm6PSNrZbH6jiEd"
    "R00Rh0vcRHernzJugww+8jvKb3jtuJnz6iSUblar+DGqRmV9hf58MYWEldO19PWw6xkCO0PE8XNV5ADAN88hLyPjuOfXLLpq3J7p"
    "vKPBNsRnDVpgDSRHnwdm9siJzFPxrcgiiLHmxLLRUc4A4+cYPWIjxI1l4HTJff7z3acZy+7GVytIccyNlqp0Z95aBhzgUkoIi0IH"
    "h5SGPFz0DXrMATPBU/2YQLZN/XbSzVchbF5Lpo35k7DRrYCd4V837Jitrcs+sqi6hu33S855EYND2zLmE2iVqpOl6h7l9soD/zOZ"
    "L56QkcVa0AZDJTD4rCta3UlApssDuDvGJwRvNPzxhc6jw3HwaUliKGhGspRUrvK770HOavD1JubeeT4ifdFfoTnQgsWbsAhE0nRa"
    "WhsNV75h4tFOECzw0VUZjeQG9709P8L+TiiDut7gGdNVNdKUO7JfP+Ow6o8mndHsQG+fvMQpGvTBxA/VMEoofHAaNpGpC9qT3fMy"
    "mVJurYTquTBJynsXYE/vWRMHSvK25r5SzDE4CVrJRN3HNEVAnD34Tuue4f/8lu8WtuNA2xXp1JkHLX1+oFbOlKK1GfOZu89RuG5A"
    "eqwmj9CczxKH+UXurkNEHE4AkH7adheR0Soj7S4jIUL8/GKAMeOm1SEs13JevZQF5f3fFwojvtTbUPRiXQtjFihjssRKNLF20TU+"
    "FrYuDsKMU6KQBljzOScc9/bhwMlDGdnNy4zukxUlRdrOT56iKV7tz+zOn6ei2SbO5DHIMOeh0m16VRh31RjCf0z3vobn9eQG+7HO"
    "XPsJ7XFvlxNEqHPPF/wnFV8Uv/UoZsEKcFRHLzR7rHY4WqwX1Zp5/CYRa0WvwVIbBXr3OGXTpVHckv09QDGV/LH/dElNChj5Um8g"
    "foLP5hGWlsS4kX+nsK7312WHorfsi5A7qdkQivieLfzxNKH5Enf4HIgn8Kuh6swWnL9C23tzKdZNditIw96y5+2n0ugSb9LFzjac"
    "2624WyGwH6sN1Oc1ca0JXE8sj7Jy9eRQK2QP0LSfm9nT4dj9h9TMRxvVhAuu3p193AzrT16GSRtb7GQEvJtkhOqREqmr9lBD9rRo"
    "Nhi5F/Jc6Bsc4NI+EGed4nguSq4mKVHFA9kOOfzg3WyH4hTBKUBW/PLSoutI50M9JRfcKKi8mo9EjaFThUcLSUX3UNZlIng0ui0n"
    "8cC9n+v5/Gb1cNHO/NgV4dT883V2FXKnrSk/hVXI1gN1YUFcR8fAixKkZSXW8gIrOP+FEh2OY0H9BtHG0ubg85YKqUHdDrAggz8c"
    "vAAf9q09PgKIZ/eNV488n1D9EbOSK6pXf3QMZvTPj5GiLQLJCisak8Kumyk/7WBplafmn/deltZVBELk1Q91MxlUmnakhbsWtQv3"
    "yXtcK2GU3JX6YABgXNeE+faXPsk5w+P94qGd4jerFC7s1+IetJOFthDEHajrp0au3ZajJuqwn9eyG762aREFhmrAHKZkp/RB+azN"
    "L/TExugYVecitOreRTKqJiOMl+rvKTKNX5RmFhElO3JxYV0jGXzYQU3UH5okIAY+HjzdJVMfUQReRemKjpQ3f/u6V0BEZWKrRyPM"
    "cHgQqz6/GIfDPEe7Uth14R/JQTZJja9FVqnD0ACA7oeme5THJAWekd/f6v8aoRx9v2QoR6+J2T36UEJm3HoWPE5Pwz4/11eaj1Je"
    "DokCnbN68lTjXUyDUQn/5uyrnuz2kUbEVYgAxnjPPT3Fyb5IoBQ+cCaUQC1V6Zz4dUg4+72RB39t0ZNJnFMGQcv17Yd5eZUBjJcD"
    "FwLJwwuwVyMgTc/88s7eliNJe9S6W7S13QE52CpN4IjHkZDaOMWrabtD59b8qLTPQjR+y1HRR9qzQ6buBUvQAC1yVe0CpZBqFIYM"
    "50at4aLmQRhcdD70FSyOWzF39KH7nRCXrebAHLhfv9CnEQE+w68IFKPhuyiPi7qmwWn6IpeUd3giA5+cjrcwktRGWY6jSoqiAJDJ"
    "p8A4Bt2fWnWRD/iVb/bEaselMFi/+l7o+BvHZen58CfwGO2JYjAi5tPWQ0dWheFI7Hb0aD5lR/Ls4wztNRCj7OvgHiPhM+OCP9bo"
    "zRWNYdVP+oIhCT5xUDwM4bQg8sTAEYIK+gEQ0OPCBFzhEC2kRAg4Ko7z4hXHPX7sBaSAmP7nYnTxd6pT+r9OdVYk01j/ONVZcS/v"
    "2SQy77iycZ9zl7BKzoXLV2yAGlV6sHpBjeisAcDpQHZdQFPiW1h2BxIUrV9AE/ZFbddCw/AkxRUMqPpivcbfg3AfiHMtj+WCIqyK"
    "TKK2YpY1wKSleO2Oqt1rVeYezRXG9LS5+G8BABzSVUzBumGIhUDIeNWkblog2a9tT9PjUixcBINHMKBO28kelJV4ttZB1Ies2Pp6"
    "0CVPAAN1YLvz5j1TVRKC2/YEoeqwmbWuoU+PTy7LdoNBaqan67rLgrLhiFGM4G5p3TAWIc0DcB8qPU88ih2rP/ZLJbRAsELmfzXP"
    "lct7gkwW+sgHCFTAUAtHgFUC+EuMm/t6121xvjSVQ/SNRTjT7yWbKZ6oEqIqSdJgpx78fek0jtKky9yx21z43G+EIM/hynwVHfH+"
    "VJ3dMkfGeKUGEvZ3ANhfe80r5CM0TYOb8KvAqHDxDWrkcl8wU+TJysY/bFgKFSDZy9kU9m+LqpjYGpIOg0rdmePML1GEhR2sE0Ir"
    "Dd6/QBgyhng5Lu7gPvAsL2DKvJFav/pE7z5vGVgALMjPS4sG0Dj0xdFCLkDJTUem5pRv/fmN2LqSd7mCkrnq5/xUPMbAhdylWt6w"
    "rKD0JKJJuP6ImyRuAVyCQesCa4ZRBclUmWBpoqT1x2OPn67YPRAK5E+zCQvwWdSb+HLHkV2i/rL4o02WF6NFGv5MdlaabSmc7/LY"
    "H6C0YlCz4uvGz5HOsCs93tbQ/Pjb/F7cp2xuJrMhSSVUT+TrJKhdvAU6AZu8FDmZaONZRjfKke/QcHUDKECvovvhqa5hcUXD/zJT"
    "NF/e17iWerTa+OtRo17+zCFEOPIG1U0yePC0BSpG4HuzBEjjhtCC3/kA2vE9GCaKbZN8S9Udmy9/v8IJk/wVXOxXHGY9MqZ7S/VH"
    "KpNjngC3BvLw+ZLbOx8M6yHiDxXYZ9k7g0gZwgKDy/MjASdpAubFboOKsDV9swZp31XRf0LAFz04/hiBxz4KXApZ5qjMq50LRLdN"
    "9V2n7hVYmDk75068zNh+h/4M8JJ3bpt8DBQRTxhTxjDqerIaX/DB46/KsnF2nn3qP6DG+UE5K7Xmzmcm/uTtYlJQbqpMOUBDiTOk"
    "+IQrxyzH/GpgvQ7D3j7FPr+fxQBcgGi7qcMqOBpexMg6uJmYgEQhh0XfH2mF8fq2NMSEd/DSkfm0EH5q0dfKP10or9qDrKiltwUX"
    "+PM75Wy3xyhjN7aPB/kjeA5rCqY0vxV+LtZR/HjDCapmM52sP8whvg6GDTyqnUG59EIETAS3dpUiGyg0xrt8Y8Qy6pzOTX/J4zqQ"
    "6YjCxSmUN5zrpt6B5CXKC8O1AXnghI643Wgpm3ORUokcDB9+sH1F74rRb3oyRrDv96gRXy2XqsrykJPxMvkrK1T/QMjiCVDrcYBG"
    "SYJvi1hdvpyg9/41YPOVlzCPzR9lBlwb/XJVgfm+WHxlzz5NfIUJ3g4PLvYmpc/ugFvz9Oks0GJJZzTM5zuCg5zSm2WA4AMiwdHK"
    "jm0/OeWDpRvUhy8vhQmMSmt/uZX+IoNrypIhxqhVKQqdkg3CkrOowPVvpnXH3hoDlq03E3w4AgomZ5zL02jRbcuSDAXz33c75cMA"
    "CYA4zuSBIWhVRZsgKxE0m6Uo9sIJCUko3vxtnl+wV2XyMOklwBJWBIMMpiuNnAqNORq2S4hYs8XifNYOsvPnyzNTwJAND3FEG/hs"
    "AIntc+fgWRogRTsyTjDg9oEXQpYJHmPSb0i0Wwasie5EJ94CCDlH6snHO2lYuY016gWVvKS5dqBSNm4VsfBaQtBSXhyBZs3QVd2u"
    "hHUuBsRzM9L7Idd+P7t/4qoIUTRb3avG2EVUWNIXMMd/LV40/2bxovt/nvCU/nnCU03AAelJsKCOxEguOyWkxLMs1I7glrwsifS2"
    "4xskW48mW+UHa4Q0kp7yOU4auQeHKgHAn24kjyLWa7o9wZvCI+iS7JRsG72zwSmv190ojZACP5S8LCR53N2xv/YF6ABBUkB0CA9J"
    "DrcHsvFIJsdt1DBVHASNk/g1Cn4QUf6LKeRg+TmgDiQSi6P1hb+j8kOD58KtFTOWdVNVSaFQsX5KeuV4ZgPOc8WEAqPy3/63hYY5"
    "VPzxfc4uWq27NmZwjkBZQIXlmRkOaH+xUu83IrDkkQanbdScG4rg0glbFlsWxYAOZV6clHsk1m8GFNO94NmcZ3iFRwYyjT9QOLhA"
    "c4PWhyAOTg43Z5pqj0eEpWSDJa14vo/29fNsBO6FV/NrLd9Iug9l9yRjkldJM+ViBik2AGHPa4W/D3Ow18OvsTxanSmI2BVH7a7M"
    "tZkl8c8OiCDJ1wdWf9GBR/d8zMcYxXsMkG6SE6cfzaFBnTdPhYDBj95wbdPrCncu2pABEJFvJ34qtjtTMkSJRXa8pqHpriL7Xh6Y"
    "Y6QLrl9zySkkm4lUYa9cL0sh3SnbJ51NLN+Zk3sJ6EN8Q4h7bYs+TN8U0H2+VzzHLeZMz1wA95X2GRAL5LSG8jEyHRO3loZQZUMb"
    "MmHkfwnnzD9FPJtqzOYa0sGpCx9TIOkYpAxvbpBA/5WvC8DZXdbrJ+C21w5K1DNqcbyqMSl80EnMWCkI2P1lxiNBXaHzaHJn61YQ"
    "f89AZUXh9PvNg7spfaU1MyplzINkRCYOPgUI1ARVWIbIFZmH899/YpB6JiEmzSBy5MOWy2MICT+BwbatSYt9G7LQrm1T4+9lRUTG"
    "Yo7UvIigxiDeGklQ05oMBC9TwfTlr2FU3s4+zR6UovkjZe8YtqY2P9Cv37aEGX5I0NEnDqiHZeemVOWJettk5/weOLdkRIvMHzag"
    "08R1w5fmOczol+1+EP/iqWz9OFd+85LwoKa/Bp61DY+F/fyj/SyFHxiS87tsPPppyUjbqq34/cFEzjZy3S0wepBkDfnEjFxsVGc+"
    "hcbyGsbShmR3eXR3J9Olfa417g/X8Lx6bSwzHZE9a4n5wR04aEKunCP74dGJX0q0TjctO3aVB8eGdYtUAGGXOys6nxXoYUZz/3pv"
    "b5M7erWEYVLlN8jd6ye4Fia3CnPau2ZWS7ffQRDN6FVgd26VirX9focLO2XGo7JUle5R34nmIVm/PUMbNm5h01RNasnknGwDJXvn"
    "l4HW7NaQ9PuVW8JE8+PTbVdSMm4Ijq/U1vrqc+aabuxbKAxDER8Fa5MuTUuy+tOklWrNxw8SmM1L5wrBLFFk4zix3RlbPaZJc7cm"
    "3UC2hVP9UNWytDeYMMqk81NAGVvVvppziWE/Ng2/Yiz2pM7+ESErzeN1do1ZvDc3ixolDaGZ5y2TDjVD9H/xs9xB/tgxhSLzbzdI"
    "qq2fDdkr8SxTGq6019TO9EEeuIY5oep+cl+lrcQCqOa1wNPJ1qa4fsrloSRmoPRM+OhNlXaQPJDd2GkniudScjs77xt/d3JLPcXl"
    "dWrC5C/wCw9G+Sd7pEiYyevVJREdDfz8yFf/AJKr7XgAKpmcCDNGmNWqqdtK0aZCl6Ximw2yOuoA56IDp0BO3TxZCDfORBIedTNo"
    "VqFj8RIz40/t5BjWwYzKwF/cTgAJ2o8f/LTgb+cf6G8fbpgjzD0dSZ0Pv5sYeUTafimU54gOIjRcD0mm4Bw7ox3I819V9poCWQhi"
    "YuaWUmToyk/873cwHfUtmm4N37JTXSW+qRwKtU70nOOjShOfmZ/5UzyDt0SvNXeHrVe520Jsh8uLAgg5nbG7Nv+h1LAiTCG17ISE"
    "s3yXTOYEChraCpj98e7JVdbCUVN+Z+1WvVGj9dt4Wyvmix9nSnU+4uxEc3AJ9JEg4juyEk33PB5dg+dmV3ehJB9PCIrkJkzvzqZ/"
    "zcqOhymdte9GwayCGyCZSB6cOC+HJW3jRHZLKyyL/vZXYzG7xDkqGeY4H84V4nC/ncBTMoMzUdC5H4/QK70MELw97+eFHKM4uDfD"
    "SaPnx0zShrj79by1w/TlICLAb0PUPTzAG2rC0ZTf9po1ygLBzofOdFR12M7rd58ocuqLpzJNUaW/y2J6dAPvpx83mfaQLPDxL83v"
    "RgD204Cch4jijmfSx8oL+8wk4QFoqTeMkJ7rykwNn3qTDSNou6itl831Bk9DsogPh8hEzcUkMU8DQy5+rH69vcWBEmfUTmzp9uNe"
    "IhEzcA3NED4L9GC6LZ1oI67Frz6zimWq0r2dfYEhkiXU2ITIfSxLB2qvoEPXtGbw2bXe5jn6B+Ns/OUlHWnQjFS1Jd38fi8eu4Aw"
    "y4L0Nt80pm/Rk7XFZ0Q4F4Zm2tpmxPKFacxydRZKXOGrX64XOFqvWVABJMAUnmXTRCxefowXGXZ5KyfeEsvC2IfpQHCLwk+hfV9Q"
    "+/Vn6TPonO4nHbbY5kVeZ+M1biNAI3hDeG/MgpiSRxpz/1v65q3hS5wtZDBd85vm7GkBPcJS8/uz6gloeJ5+mI+9ct/lJ35r9OO4"
    "RoMKdOkypj4STsZZGdwwn77s4e8J643/mcpXH18zN+HgIBze9IOPeIZJcBFDITXBJ3oqoxybShPgXpdcsEAaRuuGMpNxgPhYq6Gp"
    "jMjwxzJPh9jUV8gFR40BgOVqNgSMGxW9E7H9UU6ltnWmytGBCxzw89C3R6fjHYqEK+cjBF8IwddzR2/LsQqPcPojLqIQ40ORWgat"
    "Q1ePe7JvNz+aq9NfI5x/zaeNaPnNEQDEOC03nbPE/C1YKTZApr9zWl3st8ZfewJ9t5kJZkLtkL8QlNwFnmevXzshPYE38PQGYTbf"
    "il2QO+xV44B28t1hN+MB+5BhlaY3PB2KUYQPSjNkVnqMRUrsHGyi5dqZqMUJ40X32Vs1vn0yblOi0AyP0fzfQxtoTn8TgzLIs8vS"
    "L4ommx79ijKuHg1lJ65ChUiV2tKi3Rr3BpUXCdMYh7mTGuebKdPgawY6BtKiYinEwxY2Y1JOpvOXg8G9ptnh+DzR9JRQaDTM4G5o"
    "r9hf6aRTWmI6mtB7G1IxjVH1ElTmTi6UwS31o2wwlhokfDY+6vdkJCDASRe4hCWg21/Is8Bao4mrZ1JZ0yX7pO+YfIpNpSCTFYEf"
    "qb9f7/nXFIHxJ6Ws9YZvgTZl5TaTnd7tL+8HODG5XROlUVzc85QqKsod8NPFhoCnoNGn8hvjD6NHMjfql9Chf1bZfchqmz6KeBP4"
    "ts2OORuLpU3HnBXdkADft35MxAk3pPXPM1ayDQXeNLpNR5a0Mht5X4jg772dhDUYphmMWV0P395qzspdv3uzRW+YJVfqmHpryljR"
    "HeIy3+DYPDn0DiDXdSA77E1FxSVu3/ZGLwFDYytbF2My6Dff12YkpvQ49g4PZl8lhJ6g8TcNlSTwOLhuC9Aa1ojMwuk79ZheXz47"
    "bX3oUmyIn2gvP+KrrLrtRrZCJfMaRgQ8sAJzfFZCRhI/50NTFKuzhK+PP9JvO72KHoeU7OQfiV48cuPGRbwViLYtmplr9+9g1X2f"
    "DM0vXG77snpDH3hYwkLAI2uZAQFmbUfnNKJVINBbytF+Ch12gHFljsS0Vr2GGnw1KVA2DYujWUtOELnltBF641QbwaO+t7x8v3jF"
    "qgQ+a9CxtjQDVB/621Lw0N0R8oFblU7F/ceU4ZHVAv02S5Dgu4bS/fIzGHuKAkGulCTBeo7eN53rr8DBkCCz9Tt04oQ0WfvD+9Gl"
    "qp1tIpHYcZIHwFT+uMP6kzBrnvPOq9ToK6PVbyq+e9UFbFEcKyJuqORag0Qaiu5LktnSalSdBCa9qc9PHWKldsSxVE3/Of/N2Hkr"
    "SahsWfSDMNDKRGtVaDy0ptAUfP3QN+5MxFjvGe10RQNNZp69VpFJimNLBQIWDY0x7EaONQFRnNEHgzOTr58qTTTu8Iqgn3ybo5hV"
    "DGj/gLIzURhXWkZ6m42nosZtYg9wZvpuxEZGbJlvJBRVcBy5LvcEmibGC+2noYxN9ftxlVPgPzZ7LwbJMokTwjfoUj8hzlI1VI46"
    "dZUf4W5SfClBRT9SGT4kEeVG7V1WnFMc9o38LQMQXt9fJvUbkDLIO5AjK0FgN+RNxc2Or94frT8UlYxMx6fJc9xT87U8nUD7fF8O"
    "pPpPMr058OViGiWrp3il882+l/N3P5tNmatTDElOySqiBbTfpEvBkaP/3toHeFSEhharMUHQrlSKgfZGiP1fTYieQKZKByeO+2Wl"
    "lnLbXUZ4BYx+fknD4h39UtLdyWDLhwM/tpcpPWfgRN9kuLwvRfJQe3vp7jHY4UP79jmRTaUg55ykUAExkR109l2lM0dO8q38lGjo"
    "goXhkoDXvVZ5XNXqHSRxxD91C+rUjv7eRw/3xKjZGf5yT7iZSRoqx7UXMUf1Lr5sO/ptXxhQ9qHOkFQKvwD08eR7yXMFjrNtwg40"
    "EP+Wk5h8BKP4pWa6A8dlNsC9x9I6PCgfNgqZPUl54hZt8R6XaWbwMhfVvUHH2thiE0Zr6Pno8qDZApNzyPbBSuWj7W9jxiNMLqyz"
    "XJTgewVtwabgUS3P5TwHtE9/+0uAhNr92svoGW3eEM1qm18fQpDJyt0fI13+y9ehdoHhmIjPZGA7Omg/InLkg/Ongc2D/IcULLZc"
    "/KMBHUUYo0stY/FLYh+vNE+dOm68HYootcobqJ8k6NIlHFwr/S1L9jO4XNIeAw5kKrpKLKjHV7dSiQBDxgEov64H9Gqlf14JWib1"
    "jfBNBqWz1GpNGaoiIR6yiFew1FY7GekEV5QDbQdpW56cPHeMdQQ3eeAdi63KRoJgsob757Dtb8c/p6Dcc7XWCf9l/l77U2dkacX+"
    "glTkrH4sb+jGhEei9KSQnGBYTO8ulH8+3/KHd8uZgCSRVtMrphm0GxkWt1/vOpUAM1spsJNvhARIyiKIFaYonqIWo11wrRC3vO8Y"
    "giguuu8HQHcLFa0yI2KCCD9RCVe11K4KTGMkFkXoOUHdM+gjXaTqrXIpgYpAvT/VhRhaSAfRMBQIanerX50VsA4v//6IPX+2FD9+"
    "6Qq/ihGAQqiE8JqUZ60nyA2CCS5PclECr9r95ibXQBMca4H5+35OUetXD7jLqLmCcZea0RjGHqFrEPJeWZRGE0UDURizDfs3hmKF"
    "40Hqy4HGzzRsWqYZsDkBkzJJZsMGxAVPWbod62/RpkwS8Ou1+ts7/I48wdO2IwKJABh3ToSsjLJlgYNQPHJCT0MvSGaGESNgQzPq"
    "fvvg5uTbzZqz5xLgEwUa/3HCbEYNXVnjoIhRPUIPfmAocFAGmNzJMEMYw8EowULoTjv6XDE/XO2R0t2x8D3vI5ILjI5UOM42JcIJ"
    "iM79lFY/uw48cmH6my7IVAODbCYhQWREJALtwTgUO12J1IV0kxwpwwLeOK/YCfD6cqdu4u3Y9SM/Fn+zQPi544iSR7h2OhPgvauS"
    "I8IIZ33wH0DlVSPcM9J+Ht4DgUIj1EuLutpgQRXibUjmYoGF3kia3J+Ot1LPfjG8Mz/+k8etGo0ag9yyZ8AV1VB5yjNAZaDf7WHD"
    "iOIXrDBVW3sPtm29HMsKvf6SgVjReekwYsR2kTvORil+qLEfF/qTct87Y46ZBBq4mPWGurBOLLM5FAKEQfK41x69L/7UHPQ5fqVC"
    "eoLQhFEEQ078g/4ewEUqJgrZjeGsPLIiha/BefPXZzqoUk5QXfZ0hj6a4+VxP1Zr543N3dFbmx5EzVe5T9fTDW2ySbTa8UwyO5W/"
    "RwPBFotNK56KRL6KU2hxaFF9SF7AM6tCHcS5cpNXHP3+qIE5aAGxzdFZt6qHhU3snQhI5i9xHzHsLUnGHRXumBB5AwP9pVL2LANX"
    "+LlSqaJKr63VpwlwMckcr5UHj70tUJrPDmISaioOwb878WjLT6kxBvmFlIrhf7yatunB/JBluJ01B0NHvN+7KhomA6Hfstp6GoLZ"
    "SVxeSzh8wNWnWsthsMqiFI8J69VjPhCeZAuJp6hiKifbi7pkmiw4pZL7yzOX/MKQFAEpN0UMuS9L9eJhjUP6/UhyXDGBphAGbF11"
    "hdY07LTUUK22oUy+xtHr6cyWsHTtvzZ5xQbuetlealfRODhpWjdKt+sL9Fj0vbakPca1fEzqWJ5H6kJwTIEA68YBSNN7T8gXqYR3"
    "YF0TkY+YgH0C51qfD2gpVAgJgWGuAI4BI/yYHTDgRr1q3p0Enu//SN9ZJ0WOrNdu9qvBHPIn72wpjkaNEjCnzIn1nZn6K8ty5Lb1"
    "rSu+f2ziI6JpH2HvuHxd4lZgYBSbWbaO5Ozkp2JTovaxr6sfgjObPQq3UUuhm4nXYPlDA10FrsjHR4Rp12hG+uS40b2rZQqljCzi"
    "/DbNjSohXQMn4mCbnu64X99TG1bcvJ/yHmp2P4rh14eyd8abaUGXsk0cJI7DqaOGkN9VAr1XzFUlXpkHfzUT8GjqA+AZIeVZlpqP"
    "oM/Zk9N3s8UrwIpDFjZ19ZjXPk0fiDrdMS98Alp+9aZKGKuNzGWQwaN/OxDbldDDUH2Fwl8fF7+Lx3QQau+BphfnNdwSXv1NIYCF"
    "lUmeq+KJNNMWvhp1qs3VK8rCwb7n7+53u3w+ACMrAIyFpubQGeMdfToIN8SNnayVhvy4oNqWoY8yEhqC4EY1jFPUXgehcd+FBSLU"
    "MP59Iiqj1zp/xYqjkJRzJkDXospVJapo6VxHi9mafQpNjzee3gYhg077ZliLqp84dCU65Vh6G4i32HyydAVJrZ72qKhdRBpBqGc2"
    "UoJsftbIH7A5B/t7BC4gTqncmx6oB0lw33w7LetZe7sZG2ijWP258No4dVEFwvCG4tiyo2ecZoeB11af0l53XoYgPL89KphikKFo"
    "z/UzNiBjcklBhnrqlKYikQL984WEzZ3AsuW/OTp+Z5sfMM8L4fW/ebdui0+k+uyYDH8NRlUK7xMTmhnTJMvh4VNoZVnsmdLlVUsj"
    "u3P8+p+A0tgj2zDVOzIWxib/6dddLsDkHQF6lmM9XGcfVcjoHX5IXHRMx9R6maH5jxSxT0ByLzZi81z2amSi+/eNf0+r1d36zS/y"
    "7ZdT3I6hP36P2Yn7cwC9y0NM+mL2wydOtw/D2Bc3/xIJaYHyBQ2lHby2wzyGJSmHHi8ztw/0eEJrrGiltUGRd2xP8OHIwjUZYcjE"
    "xr8p9NSeEhIsFDUX+/TEeztrt2Ca/rGEVJ3hzLjAygtlDdwbsiwJmpK46qakg03FwLHSrxbGXqfPt6/fgqYYW6ZbUq7aWHiLmopt"
    "YGN+SqdUtngoB9xbRZmStnrHHvbme9/QqYrnE5ZLtfnDtN+qaxQhKKe0cGTgMyuxQjn8vU5i2Cz2HF51zMqvEvUg4pd+HRNV0386"
    "b5Gz1KghOr9cLaPYVzgTlNHqfNvKq8+plCmmR9oCA5h2OWu7ngEQ2pbJYY9J4TWCIbSJwhC1tRv2FkKxMxer0iPcFsZnx/hE4RAp"
    "R12uegVuPmQ9ef/gwGcn95XwiLjDACk3+UZesTsmCcb2SXXVj7GFYVit+HOqY7nT98K4D5+kAdGm6v6aC3NmOGC8Vhcf8Chauev8"
    "iawH+rQEVOqciXWXlKpCwLZLhDwZ8zx97FKAmPCtSwNeK9RnK4trVoK0bD5LS8wrZkMq/4veFoCkKfJO2iub3zXyUQjYDlHzVlU8"
    "5ek1C/+1DAi0hI5WJ7wK9m4A8mqcX3bxhIbjS4Om5oGAA2XNGiJaqxqqlcfzs5/JoV8P8OpnuTVWvuvCDJQ0Y6w0KqLdAy+JwI4z"
    "oZX4izVlrw1vfel/yeGmZT7OykcZVEUZqbHoHjlpom+G2PYLPD80vu/H5vtV1ZrRZgE603vgK7id4PMHoXkBsZBHftTYh5qd0ArI"
    "IaKG/Lm0zWmsRfKHMKSNa6VKDt+c1awEczvWZi+ZfJCyr47Dt//jcdMoE0lsXU53R/fjbXhftIsY11eAWdzziePMzsoBpkZR+fwo"
    "4k6ehrvPW7KTGptT1QJwk4ApP58IyIAPCNZSHPxkmM9SIaLgr6xkWYxKlhB/+k0F5voRDFPdIKivsK0BApx2oFNNznCKxmPFnoQT"
    "MP8Bl+KQQwPY3eq0/HRQbIcxfoWs/tChn1h4kwAXx1+n7Xbgc2pUcd/qWxSphHNy4B1yI0QnhP4J/bdH+Uo6wwHQNTj367vsC9mZ"
    "/qCpOPher4K+NXVBQ3MA38yO70lBRKRtEaIUqMkxGolHNSZx+KmxTXj69jwu3AmWmUFK6zPuKG79xPGSzSdgaL/ix+yN2jQgATHA"
    "vyFH4o7e16VOq1e9eyF4AwBNAK07/NJzP4xMIoL8AsDnSGGdYb8XgOZA/MsG2m2PGfp6+LmIULuGuxQDYCfY9MnBsHCy67KI9fIB"
    "eRAEMUVpAWhVRn1RaRbIDLgTdCIZ3P77G7j4wziUH/jZMvzkD70eivLvJAXjP0xSaGPvv5qkIBn/7Me5KdX+tx9ncAbYGe3b3yrK"
    "Eg22/11RKYEFRn5QOxGygIJ+MsgpbUqRQfQTGj/R+2OEJPbBGcG86F79tLhz3CB2RPMwRpFUZlNWFanli83uARDR+SbtRcH0QBEi"
    "ny4Ovq1FzWuJ7BCVgdRBmApeHQBE4QXAcASAP0jnv4NKr9YkLw6qSKnHSxbxvAmpkIpfIXrNh29Vb/oUReVdd0F86Ot7XzhtzFGF"
    "r7n06tiD9qV1JzTwBpUG+lCguruZgmCAFpbv7v6uA4BLguVT/ngZPLoa1V1UST48gBHWmwBV5cfzF1YUKm2BUgxKUKZ3s5knMg4e"
    "CQyM7mOV+e4h1+3w/AqphGjcrcoGPgoQmEiX7fBM1dw5TKKKfD8BmSMHBN5cxIO47CZ+neMrXMu8rDzczgOpoIhUDV6B1QmJ1NCH"
    "eKt3QrV3M0sg3smLGWqqyBLV+tIiJkdeTpOVPyr+0J3HOFYMUhjfReDwU5W/UDGQUhaS1U+MK1T0F5KjyoGSPcVwXpFjlEr6HNEW"
    "gDGROIL8SxlQ26upv2OHq1NFTo5ZfGRT10jGpzP7EqdZVXg3cSUAm3U52uzX+ziFodgUFl3CaHGr0deX93pjPWNniDAQc+LTUnrI"
    "gxbB/cLOVR5muZ1Q+nZB37kagoN8YXS4mzqriXBQA8TUn0V0vPbyoJhb4Xe+dE7M0SGnt+7yKSbPZq6XEpUh5zVUc7wUv/bKQ/aJ"
    "HKSfeMySfwNmN4SF/uLRSV5BBBCPMvgonacUlbzwzsZTz/C+Q42wnJxaYI+Be9tuEZ60vLBi1wswB68h9jN85lIovZaGFdXRkKZq"
    "4LMSlmVzbVaHJSsyvahdjA0EuT7YfQHIPaKVHLB/Plgvd0EbZmKqN8/9HAM9Xweo/0QFmWPR/MI1HdocXknNaMbpgnzRxcCSng1k"
    "/8bt9Njg/DoNz5rt/satXWY14yv5uA3u00f94o9Tl4ROHP3hiBRcYxLrN4e/Jx9VxN0nPCDb37XDCmLz7iLZ4IstCc4Hjqpn6OUK"
    "AP9eFjAgLwlFDGkHR5gnGf+3VEi/5ZgKteTvJRykf1rzIuTRU9PKg1t+2VP1ZrGx4Ctld+JrvIxqlxPeuBbGs3WB9mPvmu0k1z0/"
    "b3pR4rkuuN5FT+X/WIEJb7phOJFirU+lGYEvvn3OxlfsGM7tM0dFe5mtzyZLm9pMFhGGlZsF6ZxRtZDAXPVZYidqHYAL0re7RfCE"
    "+z10CNH9Aq5jZ41KMSz8EgzOuVC5Diw3on9sFZhq1jnL1q2nOHaFmaJGfO9DGSdG+OvWDX6ntH4UJ/SymMpItNOm/Y9IlAiQXKTR"
    "rl9T/y6wWM2bTkrOUnb/Kd4OoIhW0ly48P1bPLkq4aSgnuFWO0gpbCnJciEKenlJlB6fFKW0S0Wqkv2k7uBmW4QORf/VXFUFHPBR"
    "zQMclNvhKnVRoHzA+/MFjjHd5eU+HxG4XUjD/JaIdl8UieV8Uk1pCl4UI78YlbVAIP8IJPDTsC/wO1ymCj8gh6CUGEmzcd7BIgkm"
    "Ri0MFtm/1ZXUajjx8Tv4W787nHIpuXBbFDUEcHXTHvtFxk8Ml+RSYLJoyryyQEhZFeKCuqiNfF6fb249ygSe9EcNynZBTPxmQMar"
    "7DGPzWBD0KyXNj+XbDPAIn9NV+9pF1XdHkO17jtKFC6yi+MJmp2HKwNr1ysoyjFkav6dhMOKY8lowNGjWLPII3/JhqpVqJpF5Ao5"
    "RSMM//YAJRhAWOcP100YUQgrj5FAHRJ8dHFVKQmyWDNrsnVNt+g5Q/p02PvqndacDeEQataXKXfTjXfM8jv4h41w9XwGwULk+I50"
    "8/tBZVZlPyisdzMIrc2jOIHi4olCXl0hkguOZFZGMS2R9HWE9UugHHBgD5jaVXqnSe4yfNbMtBnkXvEdtTAkXYPp2ngj+zpxD5lm"
    "B0IEph58PR7hR5/CSK9rcR971m47cQqfNMBrS92/NtSvNy42Xx1uvE8TVOU5M1T97QmhUfGlyTxGa/Ttp01r+ZsuqVn0TnCZfHep"
    "1nWViOW5YP6iBUhLIPwWq93cUlb5+LXsEqlJf25AB2dRhy5dZD6C1IDVi1Rl5+CaZWf3ZsxCf63lqzPg7mnw9mI1Ls5Qd0oXFLm1"
    "xC/qKrF7r4Qao6uWKumbTesqHML+/uh8OuH1V/8aBsNIl+fMjfb1+zcj2A0DovhvbeZkzjZzxhvElSVEKJBUpK3G+jLbxqEFxj97"
    "SxSHur42sfhbzZIjKKKy4LMdBzQXoBkUs7vcEJiQlqidH/yTGu6v61Xvs5GO1MdY8/HbSE3CX062kU/1hOdd3odV3dpdaMdbb2b4"
    "KQiYlN4G7ApzfvGW6XAh0hdFHp/szvviACFWEnjDgTRBhc/gEQY5pCdp4PfYyMNA5pd57g5ukHSAPoLFI/Ce27sxrYixq/ErpGSJ"
    "avtdeLkOKb6djMOoiVmfp5TxuWIfIaXbYb/Sk7p+4yvnQO14lTO+yht6ySZyIEI9GuWio6sHxkdPXWC6tSj9MjFNl3gFi+tL6GJv"
    "uw0+77MPcy7+G8UaDlooD95MBlYPc3CG1SCdMQpruDjOAhlHJoTZq0mK1IXogWsZqvHm+2OV9lYp/K6naVFGcgBvNrANZzkhrhGA"
    "SXuZ5mPyP0YjzC4BsfOZrwC6vJ+O5V9ISZ+Khx6vrd3vWDfMy/KPAXImM/oufvGkyZTJ2rSNt2xmE4j6EQ7YbDJ3BgWfHrmazm1T"
    "U55EFsRAAg6P5SDqQl3y39GqS+3JLGxpBar+AhQd9b6469/v8O9Mi2lvtfCZE3JYfv+mGOzpPQ9MCGzlKE51sPX2i2f9/Vf1thQU"
    "6xIjwx7NVLQHxRjiO/v6mwt+0AzH5YMevgRn1jgi7f7Xc69Hn53+AZ7Ppf69h+ppEVJhkaMf7gl7ni9V86IPwcm104VuK7uEz6sK"
    "aRWwrx/Y8iY1bQPSqp0+un1WUKVv68vMZAqqwUkDK5BFP3HqbtT7Xiy7Cb3BYcaR1n2gx1A5kGjBwvh8iwNpPKL8JF5QW23S2Ngp"
    "Lk5rLEwjzBlSoPJpNYltjoF6T9P3o4yAIA5um6dokzDj5LPYNDK44p+8PKOKEe6OItl3V1bp7s4EJrQe3D9Cvtiq96ploza8j8+g"
    "KWwtu5JcMYoVtFmmPsdGHX/4dQHNrXfk1jqCe9lqwXvxTa5RbJd9w/vovyDeozexutnsjTDXLWypBfazAymgq5JVZhCzeOagCGgy"
    "hF3KKQuOnbwQDMWyajET5LPg1o/TOTlK5sEYZlNOUD9lb0QGMNIubT5EeojzC7g352u8l2c1Of5k9CB8V3Qp2xM6UwxdsMW0VQ2/"
    "POKJIdFhlwv3yPjyjY0kAhDojpIf4dZyczsDdChq0ql+n4TCtEGaMohnY0W6ZaQidtqfVP6gpL4xDPzX8vGs1N52hmHwDYEaG+1o"
    "wBRRgiXS1Kh83Np0yD+G+NMZb8fygn58b6iFyeKCadmO5StJLEj+ou3A54WFPDyDtnEGceJ6S25DEMoOfBkh+/Z2pa/ErHmrl2m9"
    "vPOXeNrnwDp5fao/AknmtALCWW0Ugm94tRlZoOH4i3RF5SRH6FuHqG8AQbpp1xxPJW+zKbsQR5JInpffTPoLUwRxUtWdIj7QzsFj"
    "oG8TviU22zVsvTC7Mg9VCH/qEbZ0EcSWGRboCK5aXkVryeYXzzo2zSFqZmH27XwXyQSkVzPGTOWCoE+RRuJjJxD3/FseNxp3qMk6"
    "8okeb4l120Ki0mKWeSxh4Y1aEy4MfxnQ1uLV5ULP5v5ndP39BnApMLZR8sLy5Zq7I/gMdkpG2jMg3Q8dHjPdD3j2NeQ+fGbDefyP"
    "agqct1Og61OCmZNX/p6cLZGvedZ0tORurQW/MLriANW7u3gEob9zVqZ6bgneDBljpELPY5Xdm/Tj3zImGLUJjWjFolvVkhYPXRbs"
    "Q/L5RUt5kUuYM8n3EI02Z3fk5aHhDmphb5aFXnRmMN0dZQXEFAxAxKnSlPbPqbDp4apIZrtfboe95stsAfQp3sZqv4diU8aJNiF7"
    "3IrcmjJexjlnnaHCtwXFJJ1acJidae7GBxsYwccR21CH8uuv4nBelN8wekmrHhl45e+bRr5NdQSO83HhwjccJOVvmp8OO1LSFj5h"
    "WsF+cGSqIuXSC1VWOAHddCXMqQBPfcx4HvLz8CkoRa2yM6qFf5S+WA1WrkiaqUjJCI458387I7FF0Cxl54en1Ps/iZl8epcbA06q"
    "Nj3A+yHkJIlw3+hkGUaiIY5PYn9N7KIQIU47/UOVFrtFk4tSK/NzLu/WgMNCzGCcE6v2T885KkBCSd8/ZF2fFA5sf2aFTs/Gp0dJ"
    "HhjK4GJGfjD0Atc5WZyghvDPYFb2Xuw+GdMbh0dTiZGf554Ke9J5SVBlp9P6ojKfMxVW3MfmxajQtMyPfVN3HvleK4nKy+NQAHi4"
    "vIkTPxpcH3oQHhi3SPhDz1rp4tw0oR/IJhMdEleSIH5LDHTV2xP7PresR7y9kR2ynwLT5fSoYRANGpPovc/v3Yv4FNnOl/DhB7Os"
    "LAVw5ySDykLjOkfRPwc4CmjltcTh2dCgEa+bEkSiWslyVsWJF65F26+GIxT+kCS5orLab8YyeuBwQwnzqpXFcTnrMMzGXczkCMuX"
    "4WqGx3ddFd/qqTWjvJadwEg/3WU7hjGRcreK35myZJ90E4/6nalkFw9pj9qSo4EO1uKbFUju4UX0kA2pEQicC1Zdw2i2YOX96MWx"
    "JJmtO8gVc+S8MXMYJ4JSfWFvqROkfPQE6jUSOzmc8vuTtWx5RoNcDMgVFHvaOpa8GxCTSHjqRlPPXdEbud+mzGGtHUnv87Trtaqs"
    "X0w6zG/1K7FdeBj63DSa/5rF7yQuby55B+KwCqSKhf24p3QGgRvJAalgcNbUE7+IFhehOS6kYzOvT3J3vOGmlQtdiSl6zUpIvW3j"
    "DfVlvzIeMYT+uPQv89OzWxZUjxI5+3ub2u8JooBQ9XaHN/swLNRYCbwFWSRsJ1WPyQzl4dFMtsbZmG8BPs8W1ZrtMuY3Zm3R5XHx"
    "MmLy2wwxC27Gqpw6t+I3kJa7nBTcc/UP8aW7mSI/E17dfKVRJ+Qe0+1mnPVloeqH5eGB7wPdebz66ov50h1jk9T6maofUsMRY38T"
    "Tz5je4sDXqvB26i7M3sAG7g5gnSrbRIVALkugy44T5f4QTrNjRc2sDryk8n8sYi6d5CRiSKbkYurmwz0wrBrfBiNfgQdPbTTxwUD"
    "0y9Oc95sKoki2BOXIeiipXMrfkFU53Rcnj4jGptpvAzLP58fmbuyBzEdfdAIbpfdwuVGwH1arPLxeqLaitw0HXb24xJlE70QV8Y5"
    "5aRhJRPbAnSSgbU9NTat8fHGwrM8RcSVsRF0EIP4zf35pBn/GtHHLitja5/156hLDGWRP8umW7/s0vvI1HE6wezCr6ivIGhZV00g"
    "EUY1whc/ndsrbfVRJKQSbUWDPGwp9Uo4m2ARd9/RyI4RtG7H+3SRmaU+6q4AUGK2H/rNwIox+05AQPAK49HJrtsD4ZcJZ7WyspL6"
    "2yukmlIMnYlwF2wo6IZVj2vJBU5d6eZgRw9hEypyPnoy1F1s+c0YesOZM8bZ/dzfsI9drH9U27OFCwEkMBCjKfx9Nb2eGpVsNNvq"
    "ntKJksqAyrACPiJRC1IRJnNMrWI4B1nzgKF7RtUq4SIxw+0G/OpcOa00Wk2478KXE62DPeJGFwbNcV2suAk+NFdWrhH3Ii1NnIYw"
    "8YjwlgFb4P2xY9xR7YvmSh9VkfPnsJ2OMsgcLVEWd46258vBW/dJue7PSb2ftWJtmCoCV+VPS4/AS1XgQ8AGZv40VoWAwLVmYLg2"
    "NzjG3/jtiu/xQ37+RsBR74YgiQ8m2EV9guRi37gyaBBGtw6WxXvF5OffPsDFT5+FtlFZKcFQy37lIkD2Og57hw6Oy+GVGDAP25Nt"
    "OBt+p7fjoaHBv40kpiipHtOuaVDxHLWnmWcGchOGM2ZgYGKgdN/e2RCUOt5kGhU8zJHuYgXodIIZa3lm8M3fyohBxraG6ftl7iLN"
    "CLIQubNq2Zx8hJNAJwA8xYAwG5H1YlOSpHXS6l72epDp39uO56Wp6/cesicAl0gVJgrJgmZoiKLGVE/IUQuQOpMlOo+nh5aOyhlU"
    "xyn6fIFfuOSRAde8NYUmNb82UfJA/mMNl8XF936G6t+GL3Ty0n+cfe97aSlzWOYnnkCH/AZZBYIkn9jczn1EgF4gjNPArdQAi4+6"
    "4Ve/fGCC2TeH3j6139nm9rXhfdVZBtqXxE3xttWWil9MfuY9ioUEYsY7NhZqjhu5rD9iwmRSDF9xCAJXLvOyrXEw/mxVfn7P5NeF"
    "bmEGTegbmiD5VyOejm603vRlI0rGiK/TIkvByHkYdXB7eBWpkuqdIgqJtRnT8jmexwz2cX2iwmgQ51D+mUvaysED4gaFwNysYYFR"
    "wptAJShiKtDf5U/fJZWCbHtbc8O+J5wnAKWEiEgbtUZn5XkHQNcpDrtUoMX3WBWMIpEgjOjV9nQoqNL7Fpi4KBg0d9eQPSxDiZWS"
    "QXOCiM0qPpnIPKhR/+4bav6nVaVM9F89sJGF/1tVeiI9Cp7A3tMGlnrfGSVDc4tRFNH/fWiDIxb+IMjj//ZZGFPRGAh7r9ZrINe9"
    "qhIAdY5zpD6GI4/gA1pB5M1W5MbbSVafHMGinMCqQotsiPx5M3Qn5RdkCZDKu6FKy+gb00R6Jlf77AJ+LC2d42GAErx3zOcSORiO"
    "E4MKPYsAiQvD02Ui2nHp67f0JgrwYwd713EUIdyR/3aOM/Y7I4/nio2JRHrqYsxYCFFUngRtYCboTW0AXuUgNIgCZ7CS+cmO9QnM"
    "RycjcMduApOOzV/D4+zYzQ+n+DB3G9nCr9cKmfMw+T40nwEgIKqwJrPu4mb0LICbQSDVPJt6fiS2qspYB44RMua1RtFnSG4oZOZP"
    "tPxc+qEXEu09EADv8vWDgQLz7EToe3NYTNCj0Ex/BywF0/7MApK1cPwFLDykj2hMDSO0y4r4TEI53UPXNKIwEbUUydIUza98WfLW"
    "emIqPK44QGUM/X7LA9IkOnxC+0Lez6Pmw03L/MF9/KvE6kGsvEM76oXkJt3x4tjQoPWw5atbNGKorYFScAETDTodQD3yPUH/PTQU"
    "wS3Drt+HQtPVa6DJ7aDvxkZ4EK4gMNa4osHM2U9Kk2EpH3SeFdAT6O9sE0Q7beh1HToZ+E2zt9ewoaCbI+Ys8mzGHMQA0c0ZaUZu"
    "EBiKsUSHdW1zgToFXqenxn4qtqcXNe2f98Cwtv5xJdtYVqocqT1/yo0Tg2Ch6a2GE2nPo4b4WsnuFBwNUXmcU62vexaa/2yeYVqw"
    "y0O9i9KOcHAAOmyLy5CBsYDz7/wJQkNP0B1M3DPn0sJ5eosVvzsQaO5OcOO2yJPn0MWXrXkd/2o6QARr/OXn2ndix2XooM8Ivvto"
    "shUpK5mL0Wx/Ze/xWgx1iLSYUmQXn9H9cOx3jUOY0W5YqKrVMdDUgKHt/hp4RMEZs9cMav9gz4Jez0kXhD4s6RszHAnAYpMd+WJt"
    "E+A6l2AQa3aGsA6j0ZIiWRgqrwhxZq1bUWA9z99sPgWIVMNLrN9T5qMbLjPlTL+cccN5YxWGilICjz7aG1Wrj3wYrKLkls40KEyM"
    "tdf9kFGzPUu8Qb+jJ5h8Q7rU4VlrA0/xq7PGRhmXvQhA5O8bwvFNxLr8ovEm01bb8GdE+KzA3OKGPciyRj04XtsNgqng2TeoJMjL"
    "He3PNxGWnTrRhMs3C/2JXMjOsH+Wpn0hGGFBqlcZQaTNJGXen1ffjcTHm0tJGCCDI0zD40OjAAcqYMPQ+tiSWDvXvyB9apLyUFBn"
    "Xt/4bJL++hsLqcZwsPse52lq70tVETbYOotD/O9WxoxqplQzRE9h1VvZAiN/Wb6O2bs1htp/G4LjewjFxoOcVtlpHZbhXJbt7HA8"
    "bDN6q85HKZS9TGK7PD+lNb5xdaNW0Clxf51+y+RwqSd+Qqvfiy2R+ltg1kL7nIenktf4zg0bQ2ZWsmGtlFaUxCm4wgO+4IhVmeZJ"
    "qItrTO/ErALN+Fvtnoul5Z+x2EWWZBggX3YPjG8NUHlnhPlMvEAhsy2d0D5j+pY6AQfd3gEkxLnRKl+pj9Az3OefFe0kiLhGuVNE"
    "zRKopXQu+hn7BxAGrs9G6TnP93qF/vuSfZLe3BZwSd+sD6MdWvKyWHZ8VkArkbKL9Owurl3V1DG26LxHz/1HQC2RpNXgVU9Arsvc"
    "UQO2E3QrMJzyik26SZGOC3dE4KnS02mm9Yh7fLTuwcA8l2sgcWyg5Tlp+H0Z8qhK1mOHBiQgQIGKBbq0lAIqZHevKJ+RbDGOMhq7"
    "reElWhwndHF/wGXv3d8EE/RTaCwWknuSx4GegpHgMAKuBWkpm+6t2HnSn+DRKQyvHDDqwRa61nwuLeGaqdMB05im5LuUpp8vfV3v"
    "1bsa8mxQPGSTq9GbGlHHmAYzqbgm4NdlUInhSayy1wZnOLcw+mG2T6SL0bgmi/8J3KmdAtCuHrNLwWPck2NKY+LH9gCIz8f3o8zk"
    "mWt8mWm1O+CVlpoKCnxSBleEaNChgV2sGnNNeXUgydd+WDniZPr7IZDNB2LxoaZP9FXKtcEcKmTJymWgiYU+wYxE0BJEKtAyEYXz"
    "1NALsud9MO/mr5ODpkTMvFkjG/kbtY3+UN1sby5/bzoNJLSz/oCcGcnkZ8AeVB6y9ZbqeSyuGqNU1kX7G1ydZbJmpgwjs9CuqDW7"
    "ytw6O9jO+PNlyqyndgHK4lOzHeir78BrBiZ8VoX1EI/CJArbMww3H9shdNBnGzMTwXyiaScOpKHTfvotADfn8IdniQfp0M1f8K31"
    "HL1s7x2qFCUwcs0JuZSvhfJbCXSBdoT3397UrIG0atMvdJTYUzlBetu+IR2to34Oo9pAdIJj3zJ8sYfSvIBtBfV/tV4nENJX4emu"
    "41y2pZkxGDcHNj/t5woaHc7SmCc5pOAc3Ivi3NWZkT1mgI+J5FA54L5Tu4o6+gOFZE02A7LDKY55IGy2+684/tC182H9mhih/rof"
    "cFZ8yaHoXOHDxzFMjvJz4XW5JD7EeSE6QnVYf+BUpum/Z8g7SKLVtxCVBsF6R2nPWnmEpueD9GwMouSqQHaSc9t+F2CuIa3oPmq6"
    "3/9ce0mnnVqLjhj5T/NHxhSUicDD8LMqIDZEG3w0Gm1as3zEmxzBzsUWZdYefiD9+WG8X8hTwfq1LaDx09xZj4NqwT0p5DjtXplU"
    "Z2b+aVyYokho3+6QFpwvw7En9uW+cLK9QVzz7Ot0apy/RXlwYzQ4CnKeXPqt109cGD3zUY8127mhwFX8WdzZLuUkdt+UjeMPp/JS"
    "rRjlnZrtnS8Z8As+DqX5b3kpGEcR+uAVg2wuO2St3uItRTfEujG1WaM7dqLcTum2Rx+eZnTZr5lCQddmnSnMNdiacxqSLscrqU30"
    "az+36X20YsEs33FVSw6EiNlHLF+ia/vbvphCCRfCKWRndtZE7rL6TgTYOkrNxMxLQd5eYokmf9cJbMZCHEwA00DLyqZ41qfn8/zt"
    "4dQyKh9dQl2KjxgChj5RnfhbOnYAKOIKyIu2gnJg+x+s1pxLCSlkkyf2mWO5k1KRI5cNSXPi3Cez6gHymK5aLeuDpRdKZqekEgJZ"
    "2yHTyD3gN8WOXc2KopRXuDZyPKs9wCwsdRLYTA1587KAoQicJC5XOPIM6qyggZi1D6CE/RIao1r25yKTjKg1HpwELfXQUrQBPWJ+"
    "UjzNY9dlLNHlvaqg8pCGrSrZ2c633IerkVO8MW9rc6YG6/AtAUbsnyiQLuyTWcGOmO618xG1j+1bLxuXZ37rC1iW/CSPq4N6cBZJ"
    "Zoxmb0Xj0iiOWP9cQuvrjZCZKSrkrpxl7vw4+JVFVZQs0xo+OPG2wXt7WZXhGysul1JkxSSX0tktJaJ6eia299321L4bn8h5o5DV"
    "EQbVvj+QnJqHBg905f2fhnzdkL/mSzmBUD95EV1thoV8dx2mcDHvqtohahL0AtyPrEKXGPWoK5R7+cDsbo/a77f81fKwk8SictsR"
    "udpNGwIRFcPeGDEA8/3Dks5b9341+zqZueDVqCreC1jOHtDpSs917SQQmRbjfMwaxGw1W9sfujb0DSw49mJz+hiRtidRTnf7R7xO"
    "DUntOVAY1oqQrcfEUDNZTAsomI98EKKiGiDWIlPd1yB9lmJl3q/vS5xsMmnyE81FxyUzlfwcChx8ykyhFCKDPrH0pmWsOIyslfEU"
    "2GVaD3q1MNO2feBHe0jk7ifQ+Fxa7x2o5XEzCtfzgmqKyRA50WU+g9nkMeCR+37yUcbx1cvJ906j2FVPZ/Ycf7v2BRY9qgGRzUHm"
    "Z8QaCr6tps8ohZbV6JnKvxx6cgLYRsHI8DapXy9DYYLt3YO+XeFXr1WE46lFPLJTFPpXvBS+Chs4JNXKsDfYIPkvG69wNf6GzhzO"
    "VjC3dt7vj4voV3dpzHHuWmUW8ldOQVKdbEhn7Zne460MV7IeffSo3wrU+uWlTtbGpvJt7w2+bQMYFbHyXXlzvBNHzcxH4YyaV0hv"
    "qgznZawYxgLgjrTQ1sg7UpiaP7CpDp6ro5Zu448b4hlp3zmheDvE474RLPZ2Tv5+K9VBZ0s2esWPEKOr3vGjw7tY+toJ3wtAkfxE"
    "0i1L4qv19vv8IplU5nkPBvzQKY2aA2qR4PzIPIXctKAjRFM4ZRZq1OCwmzKbPsFtFUWMe7nufqWshox0YhQKh7NwAL538ATlutNY"
    "9yPS53VZ8UC6yKr4r5gxKwxyweujfASgJuZf+TyprLxuDt9fwW2UT6AdLuoAH4ONObge8W9W/e330bQbVWGV2WCtWc8XPQl0YedD"
    "jp2/AaJe4TgY4cmBQ46scYnjYPKKzJ26UHgPzIPSYjzmHVzJbULDxvDxPqNJakqi6kfsqBP2LmfCVsT8ij5BFBXK59ZQfHpGZQB1"
    "G7DXaELg5h5DOjgrqJEuRvr5NRKRRJ5ZuTDkKaZNApsdJI6G5OrxEmaaQoCcfSZT8jzEaz5XqCFiNhdCf8xCTQQcRlXbLWnMz1T7"
    "HIapGMzwAT1N85/IdV/m/EhN8dnUA/AO0GLsB9j9gFsR6yyfUuFguFaY8QbVlLrjDL7yHfE8yODAuZyoJ5sjFGzq3R0R5P41E8cw"
    "h3GY1W7OXp+jFR04RAWB0/A5tAPEcsWZj9ZIf6Ygp8/ZgrxoJBe+FPyKryGo0NZ+vvmCwWHjVdyGWlXJNfflMQv2hcrQziYnva0j"
    "4EYAgFlvhjxqJ2WmTG+YgoeF2egqGqv71+LokqzW/ShwAmCrqjLMN9YgEdU+hzUbYP7FvsFxP9C3OxCy8X+cvGxxx0RD2xrksJ9f"
    "/blLgA/aLw2S59rTFOS8wkPJXQFacCeZNngtw8WYw28epmSY8qKif4FOksBVeYOyER8hb08MsGJU+XQkTDXxAS7brv+GoQq7/Xmo"
    "owTB8bSuNUFapaUQt7Rez3+AkKbzQliSMSjhEWUAPkStksfuH0lSBiDSdPWadbqcm0dZwOMfBUDgGKxgA/03l8UGb1/798EY9jYH"
    "I3DU/3swZswfWeUM8OuOz42dFx8P729GiHd37C3gNZNpLPKrcO96nYvJyU+0sz9tBVCMCkBQKXzJl8DbFkNqoGuPFsq9QK9zAWut"
    "bFXgYilJekBCTCS7uAag0I/mGKcMBI04fy4jMr+WubJgs1ZMrENceLloWiHnMRjKWk+oNFa/Evyb3/hhfCFbpte78XUWpu/bfPr8"
    "lbdjl1EKmmFukOSvZFzR3sVhjrJeg/jSNOd5WIGXglEf+mdqPq7v2Hh9kMrDPLS5Bn7+gFS0zZiT6FlWYifxvGeKIh02VcOocyP0"
    "YWEc8LpjSQT2FRRisrLMRnuGwR5WNFe98Nd0tBfBoSB0yP32gKiWl/1Odg42B930jdZQvp5/JPsJxubv+OKGxh8ZNqcVB+jgaV4M"
    "qsy31LIhcayc7xFk8ihqPuCfj6lDMFO1kQj3e4wBeaWwsYab2Hi7EOA/yyQFZhifs/KlEzw8ctdhI8E6/naArMHn9t2sbBLJCHdX"
    "46MwPaPgcv7Zi3NkAtzDO2ZufgN1sXEsXr8HZtqJiAiVAEkJ9g/gLloYB5WKS8jfh1jgb2S8TvWUBa5bePUxuC//8qoooHsUI+WY"
    "A7/Q4sQvZ0EBcklMLlS2tzOuBDl6Lnio88VVLuzXoXPCCfLXGvlJyQZK/US9A5HeDU4P84HEWq3nW9xSV7NaTBgNKXnjRFHqHHEC"
    "LB+CAtnNoAQn64W1+autGfX3uQVuGZVsFRUxhUczjFAFNcVHftDMMb6EJz20PRJTdm8l87odeb4A9SishM5kJO62LvUUgQE+x0cK"
    "DoPOwGvIdmoelTQkhIhECzRBt1pQmPMBrMbb+A7v8u0LwXWKNsJfjhDaLBYFMn9OHoEPH+DJ3tu3HtpuqbPN+OHWmcyV1l7Z8use"
    "RE768ppPa/7lUr3Err9mDh0OarfjO/OKEMAAgTRnJiU2nJnn5sRQduNs0WMomppOxalj7XFo3aLpd0B26HlwMg5aBTxr4JuJvEve"
    "aE7MGfeqDdJoaqB/vuzz5Pi63lDvLz6AWBWpjPlk02dncHePPzJyRjdAP+hgPUkjL78S5ezYCsfi7efq9kQDJiSqCY7R4oKApYYL"
    "1+OFo3ynrxopcYFGgF7QZpjuZpZFPNwaDMTIV4did/Oa41nNr6xQNu+ucj7iLTCc9puLY3um73D3/oex89iRncm28wNRAL0b0puk"
    "Z9KORJP03pNPL9bfVxKkwe0u4IzqIJGMiL3WtyoYsakuxWMajztAs7Ic5Vypur/Gaa5+ekAi6SldwZ7wSsfeZ0o35qXauLQ32sCT"
    "7dd0sb13EKLOCH+XTypBaGEl43Mq2uObvk2ttFsCCUKShwBZCNYcaSyjRSYxB6PgyGSGwT1OPb22c6g+CexF/ZLhPhyMfgAF2pet"
    "Bt1c2iYExMU9GjKFVDC8S8Z18rGCx4ZxWwwoo4YDpOIlG+ezIfuwEcUKpldXUKU5UaSN6kSDRcBadvuvzryzSOIUpOkpLkEQYkFv"
    "E77Mt43N3JKT8BoTIjyfbJ9L19cGUhMzUt7lRuDFUHJadREkZC5/wZcSwco/nR8v8FKVMuYXBl8EvLMQIieZ4a14avNdsgwVokoh"
    "8oLk5AD6EtC5uSTo6K/+7C1CP2D1tZWQo0wFOiN//imjpqE7Oz4xF6LnKX17sy0q6p8zKMZjnSUx6PHYxSgpkD2MmG2aEdAcbFfo"
    "TXQsrMW8c0KZIx+p/wRADFx6oqHHx7an0nwi2gp+8OGfVxHsu+4QCGB0+Qg5s3AJgRnsTtjq4QFeXbpT7fQy63K8HEU+87Pyhej8"
    "nlsuj6DxSG0zQCJwZrKmWjiOUdn87L7K0aZd+1PeRcJaUQbRjfbAtMNQkUJYKWaCsWGUL+k30qr90VN7F8gvHsR/3ZHTVKXjB7xu"
    "qMj4Ou8m1VtR/QsAfuHdGYC3hECnI/9c294DW4XFptn+THrp9byf9Y31OFMjKzxYN5TO9LoSDBx6OA0E5AHKZIQ8UYBz7HlnTCXt"
    "h4cpUnkx6uwaZjCr+cTejJpGXhQnaVzQrArWa/xZnq8yS2TuTOfghIbBGNZOfncTy5rcN5Vj/2lYEfO3q+KKLaDuyo47qmviiFOS"
    "bG7xM2aHH5DN487AkYmYtjg59Z0TGNAwXuVZTYnOq+fRocRD2qUKmUovGkkny91jqZnXp+mhKDVPQuWDKrRKROy/4oxubPBpZyGL"
    "FJ3VImYBJfmm5WTJAihvW4sby3hAGduVJTnJZgx69ksm35y9iD3efIz3YaVCCY3TYv4WdYiG6KE5To3R6344k1Aztu54wFGRwYWT"
    "aIn9zPSbfaweyiXrr2OJD2gN4pY9x3NP5ZbDHoBycG1icYLdG4nOhNG9AKdHsWGfhsWG59g6ZqEJnv2cvj4oa5S+mWy1M1FODRpZ"
    "SjBeHwDGzxfRjHAa92swviK5cLEMMbXoAUQqV6PG1zxOIRhmLtASAYqYx1AoKpGr1fzXnh0ZJxEJA1oIBZWHIyIUGJkvjfZU7mSS"
    "fVjK1v2ubZokkxSLzsznPOABfs1G0ix5enYcgky6c3DbV+tHi3QjRhfYm+o+Vb+r4/x+mS3dRNWfZB6+MEZk+OJbPLfZSuP7wJgt"
    "ySTqj2D5NeXzTE7P0TyPEMlRUDCVDavRda5zyOpnlA/xS9/byNWKLUdiLhvQWdJEs4fr19gB+fmEdy78PvnBzlOTE65QXe0Vki0t"
    "7ebgYgM4vd85bsPK94w+GZImnHzhRktjuiT4lckfR3J40eu7w0pW+aG+kcpbJ7IWXOZhzMcT8KAg0AArLwjGnnLSIdmIN744iOIb"
    "QSRVdDf7DUxSaEbp4Ei0QEIk2s9tsvUk577m9Ps6Q5GaCP4LkY5SSYylyn+625v0m9UMUSE/BppLM1nwnfF+pa7Jgq9pJd8EK8Ps"
    "9y5ksC5kXjPf+anY4cedu4NjuTxJzpU2aUd2spoP2TjmUnC4yS6YKvBFlTA8nRKmHJSjH3lOko8DzLfxVUE9bPmeNYWUrR2U1Mz0"
    "Y23Sh8E0uxuYH+SiXtksdo2Kepo1CgrfXD5jrLCd+GHV+rRkycK/fP4//4f1bzbPS+Y/O+3IQcZ/108SfPTWjWbkldPnn+uY//e/"
    "pkfS1N2QmZznsSpwy2id46lFEtSvHC4EW2Tb3UUe52EYRfPexeWWIMRdGNpWLQoa0YHWWU+qucE4InsqVO+oRiflcxvgkxxHR7Gz"
    "Pw3EOgmg+piUh3Rti21doRhGN0A/Dw0oz9jrijrWcrIEmB8w+PJ3aBc0fxM9+LOmN3TPQLzZ6x4B4kMSaEk110gCZLSGaYMj9SlB"
    "y9EtA4iy2GKbxqccbSZn460jKzjqBmCm0+Ma/Tbbt8/Ac9p3XpzjIiyMR6UHoD6XDht54rXpOFqmxuBWrgSgwaH03jmjJ1f8+DTU"
    "EZ7GgDtrWDYRVEbKW2bIW8DoJpA3RMXoVwdiphdJli4vNt008cS54xJEMJ4NKmI/xkl3cShPgeepMZBHojDb0KFN/Cd/BUTivyQy"
    "WoZi+mZrN2gHo6gfxI4ym5JKiKse/DWqy6mt+ijfg1rWz+VEu5YwzVcjEO80IjmYoW4UflHTvsDy0OtSRtQPLN+JV0BJjSC62n9+"
    "hAf4b1omhM8w1E+Yr1KprLDMd/LBNjN0epO1jzsi1CcoucA09FlJjqFquS8NG2QoLx6XfRhGTFymXBTxnvOPQJnl9BiSQTIfMR6T"
    "ZJ9X0FdD0f12gASiUVZIFsZI79wmMJHy7SrZOXYXQVvUGLa/ypeME3GnLJNQ/RB0Z3mIkAGMCJNR/qWAYgYiQjK5LAO/js99DiXj"
    "CR5D8+NzEIP/m+OvTx78KLcX/yl9jmCC9BqgJutOGnaF7aONykVlnUoY03CFZYW7rrc3sbd+R5PDA/+YfIdKMvw8x0l414u1lG/Z"
    "+qdS+9H8XevkbEvf1kgpt7xfZELKpNwilitEjkhLP+SUEchF6UWl/a2oULo2c1uLDJc6ZUp+VjoaSngJ4fSBZuJ73qjlK92oVILe"
    "nt3vWBI9FKmd9goaCk2LGAghwPnp5+616ck+cT6Oc8ziD+3Pi5rUdF4yytvUqiRVNt6d/XT3Q2tmpRofIZwhvuolinTlrfnWZPgd"
    "/fzeQFeritOz2NmsXrYT/lY52BN5rEnQl3ShFcWRcMQDxbZxZfjJTTvrihLDWLQAPkUdCeELSOjN7UmA/S6izKVWFwbU6kYH2Iuh"
    "G/EjIha/Pe+Kw+8bHmD1J66L+nAoyGtVbspHYZq0vEoNxuE93Zd3cNzO65DY+AJVg8tsfHbAsjv0CZr3tt/CqTj1bUmc3yq/2UA4"
    "Ov6cuYe03eDiSgOIyTNXPR2xxAMpOeQgx1T70vXgwxHxwBI3Pi98mArwdDVlC0y9B/fsqTrGbJFbwppkAo3526dFerxjGpCVVfnL"
    "pl/uIn561ID3ns92erA5bFsQD7pNQc/wrFDePlBP+QZE6gzKTMe0CsxrzFCKKHNaoA3JbbhLO03EXiDwGA6z5MwSEmfgnzCvJfvF"
    "bumbr+jFde131EWgknucdJgvMY2wNCoyVIh00avmu0zto6QT2AjcrjmRX2eJrkQQ11ov2GExy9gnx7WqwzWtOeoWZwa9sgFWBNJr"
    "af7jG61QCn2L0fD08fkIw+nA+cH6WRpSmqyO7VxnyZc3VioY2D8W0odR3KhXGMRZjykxPPy2ciiPSm/bENSOH0bIajxohavQ5B4O"
    "xH53y1vBFPAJzrE0ftM0mugJRazl2tq3speZs5smmLxLZe9CMxRjmGgakKOA5zcRL8phCLVipxmWt7HGc3zTRRv+lt4uPXgZ+LTu"
    "aUldRKl3YIoVjMc8WWF66bCgXl4GEV70LdjV5TrBfAbFgB8/fn/WKVNL3jz1YWvgTCka0iWmuqpiYD6d2nvLhSQjJh1gTOo3hmPf"
    "xV09JEZhYnpGeEGTHpG/nHrR6YmmhKZiPKUyv218vRPdnAvzp3hM9fFHvVF8DLSPaWC/VudoqJPajf64+FqmRuSFebzh2eR+X5IT"
    "e3dq5D0plp/cPpKOpj/Q9Lq2EhupvOz1Y9K/1gcgVlINrk4u8NjeZ2SJqnuYKK8hatzx1zvq0l7MvAzPxFRo7ib93svjz/RWvk0l"
    "QFP4Xde1iaF/4W8necko43iNwQ7eOwXc7fV42os4ndmeSMqIXC2K9EBq5O02VFXqYaaR6IuvCmmt1z+C2t68UZUuGce40VITo5lP"
    "1i2AYJctfYnglIkx/ncWf/zN2KE8ts1BS6sdFuD2oFBW1pRhIhG+9X1zV8rDldq2PGp1uEWm0vpxwRGSHOhW3KEA9xTvuV0i+UPr"
    "UONRRdMBSkB8x0J2j1EIb+xEx9IttB7DZ4KFtCq6hTfQyfysv5L5aN0aOZqkK4JHi9cndQQmMxY00j+4xa8ecCPKWIlpRJmHBGi5"
    "RKYwHp58W1lbtdillOGIIURJlRp1BP+9aKZRyRqdSBB5yMj1hHy63zVFJHZjjqDaQgh79Z91UbD4xPWWwXqOfvxP3LsH+XqNZCCh"
    "I/qzMtviGAwqScgfW8+EjDV1CejokLHFUDAvsLW2YxvsZ1BRyjdJGloE8twuSRTp8MDnWrhDsZZYLCXFxiWa4Nyxc2UmYzz96vJj"
    "h4opdhnPl1yKNy4L96sgRkTGEuANrcGs5zfFVb9Jn9JiOzzu2ZNYqiSodVcSgXxhhgSOEXPXiyJ+uSNKUkQbGCO7MRZ+1cVIJP9U"
    "2+/BveVQ75fH6CgnsskyVroR2tt4gCjqFJzwVMbc7nwXKJ/WfFa2nGy4JsqCMwNMykCn2+o8a8LQVBeWM8HFBC0k78Ufvwuv1f/e"
    "rD8ydGYzGSqll0PoIIDGJV+oqwXpJ3ZErmour9mA+OqV+guchtNI+6JmjPI+ct8gYjkFbUIH7GRsPZLc9ib2fJf4EzP2XcquM1DD"
    "5GpGuTpGjprht343cXmNExll1HRejfKjRuYUxaZiQvNDwaMonGMP8HS0CjaO/Hx7uVMAHPQZQ4wgW3fzB43FZJWRlSE3PsRWBcxB"
    "K/6qb/93HIfCqzKAp2lwtV+JYNQqdd/Od8xbfmVj6mEMrIexO3k+Dwl3+MEjq8P2L0YnLjLiWz6432Lq9u3ueX0gbYiqSkVw/rkK"
    "Ln47fkTUWiMf/p2e3fGJ0aTCgl5sn0ugSGNk+e72BHNkKCZacVNvNvMRLmkZZ/TFmUoreseivooiDI3I91xFyZGMD9jnQ96//IIF"
    "Cz/73vxs1q9LcLOZg4ETBSlxTbG71vBHPTDV87OllVZ+vX5S0sY8gfAsWGPTBj/hwA5w169bF0L8dykJqQUpL5z2m+RtPuS+BJLY"
    "vObKtz1/hbhomAbDiW8K+mGaKZD93buRFvOvDLJfONBrdq1pNwWRyJ8pWEmuOkb7H9vOb6yzxdwDCuGk5UZV59sr7I/0gfg5ycP2"
    "8HZuw6ZISArYKVkaO48cW4Fc4uSzLhy1nH7+dfVNmuiP2LyZnLa+fp9Lobp/Cas78/jZ6f787rhVq6SIHtA7+lRXvyH6kmEMWR9U"
    "wxc/XXELnNTw9w62djQ51hrUzwyJp//bOonhJh8jCK8DB2lTzzwpD2Rt4JN4IUo/JVqIUdY1TLHbajHPJpPKuLfquDSgOfLmSZHu"
    "zOKYIMHOxAYT4A/pGNy1HcS8QL3q13ZwEjLeTo677RjecIL+0SOdCZhf9zjCdaVRYjoyc5iiKcNlFdZQeBIUh0lWJLv8L2I1w33N"
    "x456olnAX6ZIHw175m7iDNqqCkM6PxficLVFEEpDf8Ip/XothanN+FnGzVMSo9Iutky/jDiEqJnmhDCNdW/eBp4KXFF3ElbimNJe"
    "oFjajtQm1gJPhi8sqg10bbgK6Tkvl8JZfA6gQaYWh3bC18YfpVeXjOwJdd9gvgYlVUe6V22uO6y3JuEwQyYRbFWjju5ZAdQI36Me"
    "Jd91h308VCoYXHS8VGf7rCwQhJMpgJd9761xdxc0pG+1OVVxV1ksI7/4R24FL7KfM+yMhBlyqcRU4Jmfvxb3wklS6xK9ZdgMUe2v"
    "+V8jCHN5OYpvHQ4svMx26Xr6PXPJEgUulIPvro7tfFAn72rK9cCPGSilf98PnMN47WlUXyuE6WKzUGs6tv3Oqx8YZ1UA4bfTyyMM"
    "7u9mBEuRrEucVA7YqaHTXBqcZwIh8+h0FPPsA7X/sG/Qlq60EjQ/CDU7VgOSt3cfRG4nT5tSB1t5spzgfNd4SxY0xm96ZHOhZi7u"
    "JnbA1yioSp1/p9fzjexDGjk4Xq3ROJ2IgUJMBkjYfydqyPgX/raUKP1o8lB9Km+GmVztATpP/4ZcAPVXxPNWvwdeZEyhFy/BQcFg"
    "8oIKLmb8cr/4xtWdiDh6YxEMlFIAzTXZnC8Wjvr9JDDmiz59FqnaRTy/2f5C/gRhm52REWn5KktEkOkimFP2Ll3gGPPm+gW7HloC"
    "Lc0n0F+2ZoZ9t/0NFZYh9dVoFuHq9qLAHFE7vBg3Ho977290CXwxMaZrdEPygKlCzjf4qyI5jbDY7FF3VVVZl1FKB+AnStm7/HcZ"
    "7Nd5I9F1HeHtvB5Hose0dm9G8psFa3Nw2Iikaxst9R5rJjIjFA+K8tJQ+o6/olgJHMdvjLxTmqJCMPZ05r82Y9e/U4rQ/7cZ+39O"
    "KerL/v3XKUXBZDSMYXdPXIqEo5/sbj/G0B5MAmh6EbK93Mzrod3gjTekvgUKqOslODpGEw7xQhnxl35OIeD2dc5+kvGsxMe9uhNV"
    "tGcFIQIBy3QdG4nB2q9YdUSfyTHcXjFYuQ5Ns2ZyxqwF+Y8rxhbh6FLUItyXxIUe9bY+CfI6DxGzK2I2rJF8J9rv2Z2vd7Vul+Z3"
    "NXPoO4yfQkUiktG4BD5+BCHlvhy5omhWa9ZFjDpeCmAZ1htjW2gIPjEp4ZKBm+FAngvO4AXv9qm2sm+ZEuwbPz57/ymWlxZHp8uF"
    "uIo5msgAMov6HX8GYXWXYnTA8RbASfm7PlAT9meDp8KAAV2dFB/JM39/n5oLSp3UNZHQUl4vFhnuTA8HMawFNwCh5VdALt7z5p96"
    "5jau+X5cxEuyCj44yi1iMq7wS9utFC5vBZhXQDNqLSsOAGk8IrgPKDfKQ3UlHGGglI3J/bn7v7bSIN2OE/pmRyYe3iTnf9Ggd9yI"
    "YXgAyhIZyETGWm8/2cInZR04UfqPgFwoTF8WMuzluEPieQgx4X3r5PgYJxFPUwc7YYc6fGKFOAc3ti3cOWIAMp690YDp1qfk5utY"
    "ItZgDL51M8ZFCB5rbgqUnSZChxV4xsV3whku1/BrXNR14L8kodPvcTm/QwaOEZhggUzRFfd49sEoBnPds0GPnUiC090mX9ZgypIB"
    "m4oOlvvu7ivHHXUmyla0p2PtMRdG3xht9ZuU6flzpgNsdibOEu1HqW+SuZmL0uhHm1vKgH1tQACSX8OLIjT7vNqgkCoCTJaGYLxz"
    "AH695ieFvv4U1vJ1CNtlj/MmXFOjLKUZyNScui6Mz0+iM4o7B6afOWgXXRVjO46j2g9pcsNhPogBQSxc7bkyn2w5XH7+c9ihcFJ2"
    "7603oc6dE+j2TMt+4oswoTETXklVb1tvveLuiKdhvZewNSSobbcsZ/+qQZIs019giaxtGacbUzIgzxe/TKQ+3CleN8ps/e/E8+VB"
    "LWrclA/suzW91tXiHaOahOZ1llF37gSbqzvb6LI0VRlq6u4EzBVfiVDcNuOTHAxtv3UJl+3k/tr9dH4d5YbyJ3Rb0VBj/psRwqVf"
    "TjPhVu7PSNMJBSkXM7kmtpDLuEyLAtY0cbIDGnDPIv8dMPz8DPlfC+hZVdNa+yW7FO19d5jNbpAne9K/yR0qxdKOBPIycB5k9VAg"
    "/9aSbWabCjy3fBfLAjuf7Fh7k6wZMIPqPQTMgDELA0GV8do/suAyEgdwH77+emX68h7Cnej6iasuefCG6gkLiTKQymOO/Pkx8XdZ"
    "VqSL3DugoVdvlXtACLD1VGphFu5ZJTCvooarCnoEsA05vxss2noZzHpHIxVxxyMJ6/lVuv52mG4Oh8SVf6AP+NGs+m3F00Hb2kmf"
    "WDK12NYo5Mfjj3UdhKgA7DaC+l1fZ5/lVVWfvjynJigNUM9nS9G0W9cLCFtbML8+CFqcPhCqLtyNJqePWTqgY9TdVnBjx0ORVX24"
    "cz1+X/8SOZD1KWJKF9SuwnxiGw5FEgWivLXvXJsnGDUBKopV1gABAUenArCYfp75d2B1uYGJhuIE+/gvRdYgQkdiVf+uRRTsFPGz"
    "Bo+L2WjkiLDjF4qxM4dr6x5zKpZpXkFoJiAuU2E+w/XxK2TyzUFa2JP7fE3NDysxi9Dvd3kQjxGOwlXVUQQa4w6vi5HKdiiZq/jK"
    "Bd5SFhQ2vWQHORjiaqNIxfKz4TlsIwGqDH9T1h9zPA1S833w4H3Z3fb62cikXvMxD+qTNfGyBe1JRdLj20tl/vLs7TtTRU8HYLgp"
    "9ffHpgBLT9TjCL4oWHHUaOE0Z5d3NgFstDUxqLTKCuJDJZv5ae3+W8mlPLtfTsCVMsinwvU06Wj4la8Q2NVfL/XmHUEi4BucrNM/"
    "ntSo+P7r2R5YEHuZc22znqIA/tl8Ef/dVZOM/x9tvhiM/rf5ciopONyfaQumPkahcF1q0kRFS+EwOz9pEzXQnP2iA9NkbzCVsB9C"
    "ZqGT1u/kVflvQWcQ0JZ52QmH3JFLdwSCBxAKmV/IKFw2C+JyfHrv7MXM7waYTg5BXxINRPtvYRayxh7W4MO5bw1VJdIEgDRGzYrS"
    "1/1ENOSF8qEjKb1qslPLlmp10pgB0xDLEaMVEZauijNiC1ogmvnzRl9G0/s1GfPY8+JLgqeP61HyQaoxk6Q7m0GCcmmzi2a/0O71"
    "IJ1OjlUclz7XkwZEvhgbdQbAT8Ky7+9IEGcbsVIZX/kMWuu3FOpCnVqgoQt4dLpVEF3l8zYdXkDsoAutJfbFKC3x9Uyb+TBw+Q5u"
    "2kzJzy8MJqgEackHuqhGvfrRENcVm/aciD9LlQYGnDrGlU92HvkR2JLnUHY27uYhfkIHzGo9VwHGqGzL2YU1KGaQHnPProx8H1Do"
    "zDphNfehs6eHGmxDlK5Lk9olAklqBhLF8OkWWzrnmEd6KhXo01PwUK0colh4ZoyuRyG542EYuaUxLraehLyseMUyw1XLF7njDKCj"
    "hcPELYngF+Xj62KK08fwOyXwAUfis1EhlflLMgLN68HjkE5Zd44lZdgsPmG+Bae65JfF3KAS/Uo/7OMu4atrqLVN5kTRjxNMmV1+"
    "uj+Rk0Sa0O5sFt0wyTTgs4tniZFQVOSGz2XrjBtzwkHHSTiDJxLsou1XP8w2md5AP/DP1Fp7WCh8Lc5LYAx2sfwY85+z4u5bB6SS"
    "h1AjeXOJLqufIzThob9qotgsKQ51SonH1H7dzIm8jaAyUyrKWlAnLl/4hwQDzD4LS9QWcTQMIrnt3/ubrbZ1jYL0YXi4u/59QJdK"
    "49F8fuZTZrRYjqoF2eytoR/6jL6jQkm4vs+Zyh57nR35d42kshqXL8Sk1VLR8RuoNE9SeADl7IDRodGFwYjMbCEwTeZI4ZhAnUL6"
    "LBR2b8CtpHzX63Z+bCFWcnb9rrXi51O6SsIzsk2f8PIEg+EVB4DeIKBqHEsL8UAeWFgoxpg0oCHH3UQ2EDsx9Pb3rnjIsK2BnmrG"
    "WIFjXjP4knHaE4SxGx1hX7gK18gr5MeCwxMygsL2a2XOHugRu1aB+zy55YrfDrk+HCu0dpQhBeqZowes0emuXTNACCT8fh9v8I5+"
    "0zmFd27rrnU29NmNMeWE192/+9lcjql2w+x+X2+EPqRDfeOXLyAYo0SpmxbeRrTdm/HlDrN4Q9g6maiHCrJEM7HwqeEYgxhInJbA"
    "/HvRl8itK5MJgjRUaUFhN/pRvaqy0nIs58mIgAfgbyjnUfnF7EA9uubbzNXEuLjb2uSrnTWqGeTXBeBCOeWn6H9/t4sMLJu2vXqg"
    "NZTCBQZAUO4aniujiyMy4IbnaniUUaU7NswCZFU7xHGvY+a/koO1jTEfzusIHzU8KVItDUmY4LgffWvFv7bDoGLfnjuF/MCx7Aqb"
    "bBh41ydXYgfOqRcy1uJdmPpudy+/syPx8zskzS6ZlogqN6FeqgZiJvZI4OjljfzuE2g8U3xuDNQepJ1ZFFK3oTt4vy3MJfw38Nu1"
    "EXir/T4rbXxFS92N6JTqY2JMp+qKO4DBXLF36YuVDIuPXKgmIDUW07el+V09AUEBxDhHv3W903Mn7l/I8g6OOPWWw4+VuEEfkUD7"
    "pCeRLDwnX9/J0lVTcjXFbpfslgof7KBh+UDbkWiuH17m8IHL8PkppRTqexmu2XnQUkPWVfmCHQA1uWlLpaxbNNp0OFargmTv6STv"
    "uYm2JzsB1rLPeQkVMMZkJrJT7kaHHkv6mtNdaKkHtaK0mlZX0987AO/AJOzuW/d8VDxT9oz3bAtvuZhoswqjFhtEoqX3sGqkUr8j"
    "wiC2JJlvo6SvmhsdWOtMxMk4hDm6bCxAZOoG5exE30SEK8S1eOS3H8J7lu09dW4vL5+bVqgKqJCRXMbCZiaDMeN7cY1g/0FRIwPz"
    "2kbtbp8gUiH2kdadLX2KRwu1YJsUDnoaIu1TRtspzyHI+5QFDGxrmKiIivt2daRhheHV+Uh9Bkd26Li6Gygf71U1zfgYg61E0nmY"
    "5FVgGPLrxAF57aL814uxL0IVKc93CCKO+7ny6Niryvbk2bMjK42khQShtCZVjirzr84WQxFYepiPM4mkVGUEF0N1ZKgZppdCGoNT"
    "6lBfA+wZW5Xa5l06apGkso7izCne/nr2QvcC/JUgZVCV7hjw2rBH819/t6kzGlsv7F0NgE9ZsUKTuq8n6sOOz+DY27nOf67KuI0a"
    "wzuHxhgnTlxFZV0aHn06CK2Z24jEzYYYgXs/5LEpidPhXldDMG48cjxHYPovtMW3iQR1pQGrY8g+aHkMo+6VYH1XPAZxT1K5UkOo"
    "eGdWpXR1hdXZUXAdtY1EzewHalQVoUU5xWTeqDkqq6P/2GVZ63hvDYXhIjbCxyxXmYDROEfJlkKsVUbE2mvPt61yuLIw2jqvM8iU"
    "mIYLMwaz50KI7P7ao70Ig7/rMsMb0ULSXSvGYcsPq+4LodrqZ7BuHJqPv/s3LFUwX8c1gV1X7Yax7ZXeKrKmglNpGyd1KIeZvBT8"
    "TOz0ObANL9eYYT5n6aRutV/TMn7woraZID8fvl02KiaCHtBCasXAr8sqestIiSKThZoTirLgaiHaaZKv1kMDl70L7xCkYcSJ/GDy"
    "1+XpVwTJM1kHQ3OOxb60IcCEDmejP/xerKxi6F1yEc6BOsrrRQk9fyiBcmtRba+6KD8A9ouexlqoEgq7/IMoFi8KM7evmPU3VeA/"
    "IbjPlkoDHlORkv6ZDO8xbmaSASx8P3g0PXAAMD5DBMsWa46hy2Hxx4j80FQoL3wn4AViMsBPk4G+FoH9/UpfnbqZdIHA4UDIB66E"
    "d+6+b+Vz9qTkMWwgVVrZnCJ03x9q4vcBxBkwKif7gd4KinK9WqYE441rZ1QGKj6dcpF8AXSTPDniG/1PRznbEU3kjPJ/zkxPcfS1"
    "UEisZ+kCMSkIYT6OldvDPAUq0whVMLn7/cbHTto5Bbav7p8kSgm6An/7OlfIorcYu7f5inUeASdFgww+nJqmdef/Xag+2wITzz/I"
    "7XgiRD686i1aRUGUb7Ww4a6AlYh25cGd0jf0vLIf69UKM5jRFEIZtzlKx9Z6EsaAzxZU4b36xhJqJx3KHeZNA6FVk4YBXXy73e15"
    "JJ8wjPYzKWWB6I9XIyCYa6sjNuGXXfgd1XlZpDC3rWy2VGyZsV2FVNv8Jf6QoRQPCDco4IbHwBfdHQk88c18UNNLvQUTRwLEYRge"
    "v7EWaJ+AVnga+Xq3hn2pj2TzI8d22AG3u7mcwyqqAGFGc9GR5bfQrnp227RfT+dD4EAISiLkBK+K7tF0L+dNSwDK451Nr4NaekYQ"
    "+7nsslSnOrGaIVBrAi+CRocS/7wZTsDn3HTb/zrmqrzle883N49wlgLqSMrydpQlgMpJdq8XrjXqclN5dcGJEM17+2ZE6SVuB1ls"
    "WflAATIi22bWPAjD94Su5lcHFW4q0uxkuWoPh6J+XV1Ky225CjLh60ckqlaE3bkIigDvF3J0pHxVQruZOSpkXbEwsivy5k6usvoC"
    "UiTRJlCh+fNHC9dcRcl3QCb3wHaQbmcz/lh9mzuWCikfgsL5DZI28HGVExihcSuWy2SguPVLQo+OLKiPHBu3Ei6++A9wzFCGS5pG"
    "2m+r8ytSVunBcVfyIy8vZnfi6X1AxsvBl5dTqAyTvWpbhBZ+yFdmpzMSTyQMnyvv6NgBVhVcVw6ycifac26A6uAFwTmY3+7cH7qH"
    "Zj98yCe5gCxK9pdHUl9jQNXn4B21zrtkCsMwcF9u6LVVy+LOhT7S/SF68ZE5RLgm4KoZtb9Lt9t5uOKcAuwQ+TX63IsvYb8r7u/C"
    "EfrVkOq3GfHSb+u5fCZ0B7Fd5bXyfGRfSjBUuTfMX1zh2OAvnh9ZJ7QRj9TpQV72K7gaHHVH/7HlSBeGDs1GVcb0nQ/qjblGZrug"
    "3Fm+gbloHq/IOL25JuD9JnCnt6k0A0V5P56qjkNL2RRN2G8OrfgI0L6Im1tcRe5JY1mG/opj29TqSUZ6hEvnMD2rJwCCrhPDAFq1"
    "FcMeAUSxhuF3Qeh0bGl6lbJRBgD0FgSjmiR08zqM+CPma6MNzgRw/8GB/eOz2EF878kOmi9lenySAC5hV/NiC+l2Pb1b/WbQIEE4"
    "AxDJTqkn/lThvOTJGTHMEO+Igfj0uafbt7lMyBmnPqBglStYC89WYDUVuiKZzGMmBgybgv06NxZaYN8gJy7m8XM9AghXIyq1fKrU"
    "uA8QR9NFqzN9DABGFmkcZ2VXYfi6vQ4tUh9pL8HRgy+NuLJHfakt7D4PofyOAnzmE58JmgJ1UuIzNIxwLNos9LhuKKYX4ykCnkEq"
    "8wh3hMB5gpgCP/DlR7q7fLunrdl9fwj397Mt7C5QDrDS5FvAIQFx//Qp5Ma/e3pO7f/tU3h33q9VbqVSv7pW/t8+hXor3Rc9F0BC"
    "6aCGU2c30EAbaSvddcXrdyQt4tOLkMBE6RaZgxtopwQcAh2uWktRfoq9Il+nlaWPZCzv2tR/df4m1Vviao7+7NDaKhGgaX1vW1D4"
    "LfyCWuBIEBH4ZOwKGqA2REefGEeAALlLoPI9MtmpW7ZuyfQQKttcG3QoISz6h+nj7MCVvXAuBViNLBT+I4kLfeg5J8SVNjAHfLAj"
    "ZlH8zJwjdYSwEoHSnRFqZUGyOGwdPZYn4YITpjmwmlc7mKVx+dEUD75JBhgT72EuYBX3Enn8eXFcD2fFz1raoPhRDjgUn12NblG3"
    "lrpKbEqqI3rvaAb1timfY5Tli1zBqHSl6D6i2q1OGU4znrL5buJ5E0hV2QoPEmZLUGPY93Ry6eIpXtgniKojq9FcoeY43GQyB1Iu"
    "1+LXKLRnDZli5y/ncMclmXFFwbarQniR4p4aqPN34XrHC6TCcvEV8T3/1XewFPNGf/aecHeklGEV+pbI5tAkO0tfSjiNG+C/uA4K"
    "Vme/0MNO8uiV2ifx7gjUnE0IyFpq+NaktNOa0on9QcDp5p9xUyL1o/VD/Mrllerc2RpH1CrSF+9+nEVKj3Ufj1Nzq0psKUULuNjk"
    "H8quCn7f6otQP51+9qDtuHxw51RY/9AmYY9dKWRDU6QCMskQzMpNkPztMN7U8lTA/UNDNCWc9Pa51LeEixp1HqJU55F21n6CIpbW"
    "I5pABATsD+wfNFu2gIZlFWB4QvJNI5UUW14DSzrrlSZphYZn3tEF9OkU9quai69C2IaxlbKS/93OxnzhKNS6XXUrmUDE38Yf+FMS"
    "l+UsAWM2LPAUAyJtEOyxLUvnOtsyyYDq9Lf5pE6Bf53f2njC9TIPrfw1N1yd1OhjhRCi/Fe5C21s+HIqh+zSqrPylHzecVd/pxZ/"
    "LWCxdXkvGxsWy8gyKfblxOAM06eSfEzoZskXYqX6yDd2eK25MZzHd3exr23ed6hiHMHuVQpygz849Ybw63wWs2hl0VXMBguWkgD6"
    "magNllHdoZ8ZYG7TaPaRvL5joH0xizvPXaECOcPsitlDLI58WggHRz1xJj6/wubL8enHOQR68jVsEZ78eLV+4HiOp24DKeaLQidX"
    "syP8azTvHXMqZHK9hf1GUbUUWUu3HeG2on/lQfNAq+SHC3y0SfzbFTYg0aItV/QgN2dIUk6KjeR59QMoONaLnznGdz58+uKASWx4"
    "fsYyaL4o2EvOMmjuuzCkNCEcyN/Zw9Jj3yUQwm4iKBBdLnWqTm1xgkPleUkmDo9cqMC8ANoTBMDBKvWSn7PdnTZIpz0mR2UVAQX7"
    "g8DwtxDY1R+QGax9r7xaub4hf4W+WDGxpNw1OtUffGkXxLTswOgrmYP3c3wrOgPcHc+LOI73ZHGv3EN8kT4c8TJap6835iMvZu41"
    "vuh0ZmVPVVNbEjaf4yvwqMavFd/V15MlkUK4nprPGsNprXLeYC4UGtN2LG6r1IPfGC19p3BwpEp+HJB+8hWZnXTPV0wvyCsrFVeU"
    "62c3smTuMpCAJYRYjSUCSeNrSMrABU6f4qzzKTbkUwbKylweLwxNxzUefZDnymo6B7WXrWE0L7LPDKTHZGRrBOnAdqXJxTNj4yxq"
    "YYI8R0GVWL/s/wFg9FUn+uGO1E3yMQajhL7WOisebwc1b6N+X0eCOmdsBDxcPGmd8AzXn551l6igGCmlBbFYfix8VZ/HxFAgTnXM"
    "7/WVKzzJvZnIjmzLtV7XGIQpcFw5fWJUEU+TqZOndI1RaeBqwEdEKSnb/ZEDrjt0op2LnKUqqihgnYSY/lkZngB+xNQS2p0fcdk9"
    "HKabfmhtbL4LZ8mVpUKnF6WGKWV4iWmTLy7cmPoxmvVeO9NDQuz3xO3URZAN0hBzSHuf0D+rcP3tzBucgKyVb1sPuuyNPD9IBkRk"
    "nCywCo6CjC06AqmIeswIaJwYKP+G8+a3IaysU2xz88t1o/Kl1s13DQoREQ0KJrSaWRM/Wi4BrGvhYw1r7vb9H9mF7wuWEBUrKorR"
    "fTUr2VUc2WgI+Qz4E/Hm5VZjNtjSqyy0FbPmdzKvZy99P8AlYmYPfmjA4odiuKNr/d4YGlWYbIVjRV+oRDGim5No/n6F66U9t16e"
    "A22EKV61QQ3jRVn7c5PzhGI+2nROoWvdJqhIlQbY42p3fEetr10wqN37OfELPpPQnJCNXt/vzGiaElHrREd1SAtBYB1HIPzIx+ri"
    "zsqmydm6wUPK7uqqlbGWR+Yl00aHe5sDxP62E+dwH+NnuRuv3tAPp/tivNbOb1dTKHs/GwWQIMp0sSjoJaIcB4uB+MidLtWtw0Bf"
    "G51GWl1tL4K8+RiP2Zh32mAR7lHXnAJdQQ6i2po1qHQkzEEERP44Wdb+FByoyF9J7QN8zTLGLEXQfqDB4LKn2b/LV6LvOkMf+B2m"
    "gcTk2bL1Oq1/322XvcYGa8tJXK9ZHZr1HgeKlDjjG+wSrN+WxN91fzi+qMeEfHhan9i7em1faQir+9mT2cGDMyQsBjfSRg1MkMBi"
    "P7dI4qAEYb2FkTkiOHzZyvLI2yUZY3yymgMWCv/qwccUl8MF4c14yXj0P+3FennMpDNuE7+PxJvqo5hoBR0tSds/now+DpW1IFHB"
    "JTPHKjFX1Zt+Te6jJChrJbHV0FoGYAKO6IM+Opb4PLNHm4WH+fwO8Q8rae0gikxf+IcIeWGG1xmrQHliTMB54444YZGN2kqDQGz1"
    "13b8cWfdKAwA/A7yEDwzr8IO+NnTe1clkf92r/8cXJOohA/NzH/9/PWvU/7NpuJcfv/D61D/mxNdxFk8SosUALio7Y+OCbhB/nWi"
    "69o18YVAJM23RXqMhaRepyLHepyJ5dPotT5vBcittaxV26t7s3kUOtIPA7JBoSmNjfsWskeTKrBfXviCg9J+OFXvNoX2uE3lkF/J"
    "xfpNneBJHfkXQs3iyxFnZB7WByry4uj5zXkjSw7TFUYgCILKHCwP3s//IDeJBgeY99jBQ1Jj7MH3QAl4tIhKk/ICnIhUBl0LBoks"
    "fL6D1j8SVQBUEeU4gEauF/JDCRgBq3wVj8lseDzPXwSm9L1fnYMR4SFYKWgmhP6miPMz2Uv98+lsg4LNsVA2pUgLbltRwBcY+yT+"
    "V5I16cxgBI0cCAj2MJrTcKuXpkeTJabTWyk59w4TZWJPVGvzDxrPF5WlrX+TtRHN8SpTIvrbsv19TsfmDDTX18yrPX1bCDh7tZe6"
    "hFMUJoo1H7MJT+STi9AUCJPdtZAOpv7rKexJc7o7E4a/DQDgrkd23HX307D3gwE1IlP873Yo/4wqRa3INJPHps4HzVB652vcy7k1"
    "E3I1jBSUvclAEEB6Ii49lZV2shPACP3y3UyWSmOrXNPwrM6ELqLF90ckwOuDKUWL1KSc6m5rXyXoqCg0VwiJGm92ou2Sax1Fetms"
    "A9ZgF2G9SM7PzLbCm5BxeQMT6zN/0KCd7nmB5qzwShEyJXZrqpYNcVD2tTnR7wAIafu4QmI+7JXZMIJIA9P0DRhsP6JJYdRB0MJW"
    "0fM5yTzXXdebKIT4oOL50zBmZQOXSIofU3cEamMP4k4S5MTe2jhw3z/BpfI4fuwqw8X3dUbF4dNi1D7pyea/04bxoz8IM/5JcmVd"
    "EUl4jLW5MGTPFZIxLRGPVUXIvNeslQBmsn6h0+6ipEerTIYTRfPS5QjeHa+0uSiUcSycwYtZZJLO1TMQJ5YtMAYgp9Pa0h9a3sBl"
    "BJ74OQtc8hg65Yj0Sz3TeiUKtXRSpMXoXJfK8npO+z3Fd01ooZDk6G3hwsqUi+8p2OFyn6rUTqWKC4H5DdrBuTPeIUnGDsxcshDj"
    "PsI2qAavmc7V4q8lu0D7iAyMUN8akRGg5VcyVr5PuGk9UNYmT1x4GOyCQ5jc5v0qGq42oxtKzWhRTCAjMC8XOeDVtctYj/dO0F6G"
    "sPAAaIneDCk7GSZ5acN63/CIzQ8xzRMjqxHsV4QD8IKSUXiWnM0lbi/2/+hm/4yZTWL3zUjZePm5SjjEvPwwSwTOsGv42G6TAPyJ"
    "73BUg9S1Beow8kSLMkcYtPelU5gKTr8M3S6ELJNcsgjxbg9QQKrGfsbKy+XZoZxXQOXnd9mN5F35O/PjounwUc/Z5yT9Sdm79aMB"
    "68d7lDXtRs6gZU+IObsQR+NK+nWV8iigxf44bnr7IEK53Oo/TQ77RTVXieKGVnJWm7VuDpdOnxYB28Eza2DPHx6/PhVFOi8NQSOm"
    "n3dSjvSCDxsVIJ81tc3X2XNtzHgr3XPWEaMZ4g9KlBr9PX4JsW/bkJeu+rVpoxwZaYETyUjikp8YHdfvGDsTvIdYEYDncj2zEFaR"
    "CkKvbaKtLzF7+5RafKv5J+XwdFbHnfFZFa0lb61JHwpLrIZlYMA6d7+VJu0qSIhu8+kZdjNPIvUrU/QNQy8sjqdpBE0riFRghhdZ"
    "aUP5O3M086XDNvObI23DpuCzNpj8l9lhiYiTfMRg3RmRrT0AzU7i6n+wmzziBryf/8XYebU4zLQH9AcpoN4u1Xu36lXUe6/2r4/2"
    "TfhIIJCw7LIsXmssPeUcjzVDPb5GvheHCjbDJ2Nehcw339tjeZ66p+84lsXKo1mrnK2HJAH0u61rwCQcFdn85DbOjYcdBjZOfrUv"
    "WdAW3e/N2GHYKRNzwdRvTGjZ1mFj0doME0F3pOjCeal2SEspvaZdvcyyom6KpDMhQvNDVm52Fu+t8F2blI2bGaBm+C2kuXiCzS+f"
    "wr+tot1Q8RIbEW8EkVPqQ/cl7GR37BlmjDX3Cf4kb1mk17c2VIsLE+ivgkddQw0ZZZC+y17MsPeUsn75lBcBrH5DpZrIQzxFs/DQ"
    "x8RZ8fgSCx9QCXxNH7Bz3B27c1D7gWRSjLrlBGyiPCCNRHCeOPhhJfk5avd7dUZ7Hd06gFdRZYIh0iYdvgznSNsT+aS/2xHyQ1Qx"
    "SQ/Vza7sjNz3x4khKSDqUz4EbRUjRwlpjblcsnqLW5SQhZ3gicUSl7GWJhzbLI7nPZEcAEWYs8uDvgdd0IZ8OGz725IVDxfIc0Lh"
    "PM8f4TybLBNj37VkWb11wqtoQfoWbUN2IlneApF5uOWFX4VnKPx3YUL67atlbl5q2R5/GNLX4lPREDaCt6CpOUNGY9uiMmuD2Zup"
    "uiPIqmuo+z36iLbwh1qdi/6W3xTJfPgjCzodbhIU5/6D3Vglu2DuvuZaMWaZKTP/6ptXu3Y6eZ/9mPdswjM043oYxAoYPD3o88H4"
    "2CxvBSjdJUz4oMLy40jeU6ftMQzj1jfydGiv9OS6Hh5IQzu6u4aZMSJnwtoDBoXEgUyMcATbADITdHVQLvjNPrK1DP/ebjSq35cO"
    "auMuyWGiEyF2igwHX9fGIVSFgAjAlUHr3xzF8AbkyBSPwRWalF3YfgRRFL9BLNSoz6vy5dVqREM0SLJlMh2RO3Be+nxrUltGCBSp"
    "aXIHBJ3CFYM0mZZhfuEUCD+pQYN15DD7mhYbv04aUMeblkOrwu5+9yd/BnYnLjuzu0rgQ2S+fpX4eXRpvFmxbVjZ63Xc7Wz/ikP/"
    "A1bgQxk6l5jUL1bC4FNPElZDJr7zoF2NWQ/mbEkSeyJ9eVrJMd0xQX1yFvDi2CwU+44sh2sRPZRcsZ1mv8QLAXZWOrRv5CV2nBxk"
    "IqCgAQSyYwY1GjCjJ+84EznxvKTS8ZQAqbRCBVEtnLeIff3twagF5uM32sTzxtaaMeVv/gjfM/IpyZASvpiIWOpxa0NE92bHrAGn"
    "AL3gYoCspEMcIwx+Q3zAnxKchy8PfvQxAAExg7hSofOXUvzs0wGxIv86HL/4WQC+T7BLKlw4+Qnw1UPN4xb+yKqR+INLOwaeue/p"
    "BFDTD73pVocwO9Z0z2TZE4B89cGC+2T+rHBbD17W+K8Eee4a3XAwMtakz+4nIC4+f405Xdl169RgBtFq40FSAt9H+SPP7iiyDWOl"
    "QHKzmBmU6dDCxxHJakp3UI4mL/i9OrUg4ZVl3jIkgMUnZb/h943vnEaguVG0tSFZsavRQJj5sQ9dFQS3OzcfPMPmSVHTjswbSYeh"
    "stXc34/lNdSqHeeGtCaoYRFrxi8kQTfnb7UmNLz+nN/PcF+swZUwwLseMLmAjFPK0ViseKLTGHG7AUmEmbU14n/G4ragv0kQ88YV"
    "Mt59De8d+1t7x/l8R5WgQpdyclrTQksAyrCKnHGZw89OM80JpR+0cBkxKV32rQRKDzzG/bwGPZfSNibMcLbBaLjyax87jXXN7AhP"
    "rwSfhW7rOdn2JNN2h5oGIKN2208evSziLjflU20f+EeOP2sd9u6H0XVl/IqloGDPv5OLFjcbE2hiw96Ij2bbzwV8tjLcuH9zJpmq"
    "zz+Lq3ImVw+x2fEDagBpnzwAcbYVMq8vTN+xOy1ZpQ5gG29jGrN3X8s+mCtMZdTx6dC4QT8fmqpMyrtaIryZ670+Ae7L34LUby3p"
    "6oGqrmfD4Lc2/7HIKn7TaDfd8oebM8OSq1+6XxbjIcbx+PR3EvtvFuZ2nMtj+GmpH7/dMCkXpP+YKXlnCo4rJsngooPsD3hFeplr"
    "uBN6lKjisR09eYtqAd3M26/9NumI3cr8+5HJWWHUUIePdLbT4MPnUhyyxBSYaSoXZBgKk1xig+/594t/fD4zvgifwqxQ4xDtGrhg"
    "dHMmE6AtTKZlvGPT8yz9JeLgwRq6aQ3jPfnYtu6ZRdpImmj6/cmja06BmKQyP6TWaPM8Rvs/HyqLX1xTvRVV0T4RwQ5rLSuiWPB2"
    "cyPYLRWAin4HJPJLzn7YUcn2myqeJTuogE9+oyj7CIWNheZ45PoncVFK/oxGt6eKVvFuarVeqd1dbaxd03rNsnZ4T3Mu/8EbG+oq"
    "Z+rs+wYwUu20vRvBl86Sp1wUaySNLuM/ZTfSzaFZEx+e/YfgpboJy7WczBLBu6OavKr+cRmEus2BTz1lT1xZCUPj/tyJCzY7CL4S"
    "VOyCj2u8FqpZoF8UPf4Kn2ddubeUrifo5dBJRsJFXja5rJuHHi673GBO6xd+5gWQXygXcGEhbZoeo9PpoT44KpoINHShoBh3GQaO"
    "YCQCBkusSKVNWlc5hO8OGrT0iLXh7hoU0plBayiVH9OSDrg8orS5JTsHHo1LmIPyGaage/+j04Q8JV8PE2g6589JBgsi1/sgmqJ2"
    "d6LXwttArk9zLdCXvUW9TdjKE52UyqnjVA6GShaci2nuBmhy77EWiTjMIgG69rNXhnLwhdBTy/Hc7/X4mHhDI8ojTPw07p5ABpM3"
    "75/e4lHbr7mEFTcA1hdgm82dpMERjhDUzrJq/gIgCE5y9gPxgzbRcAusOdKClEp6r+StcPKi4S6r4HKhiQG1T3lqcny9dRn0vsX1"
    "9x6WM8ttoCQNgMPLupMZ8HZC8RcYPpB2fvLh09mkUQ5RT5fpDwl1u2LaZoWaZbze9rkYrBHCg+EHSRcvzak/LlvxlGHHnxi+22Rj"
    "1Q/424ZsKUcAfwhhmKbpM3fj7v8qempvgflnspRlJIbhHd35H5Oldw+VvbJKjTZwhvWfk6WMWCgPlp3s+KnxMDwPUe5PcAU6muHp"
    "rP/0snExKrC5OZOBAMB5n8bXw2+e+D/3wn7v68JoHiCDzFHmCJxB27WDhLU64yP9luiNCqYzEBchr+jWf3pJXj8G9RYndYVi3azi"
    "9eDc+VaKSs+rWgIBpucPzsiSqSsNEa6yi7Je9Pn7iEk+gvpumFV/x1pzBKsV8ZVRGo7wygY+tPELWcoE3pMQEX8fEUCL80qL1KVh"
    "68eL1rZmshrSYYtlGAN22sOczB2kYUhcSy8EPtwt7I5HOj0dI8qCiNXX7PB4pvF1HD9wz0M65MYJo0sV2aGdue2S+6JdscL/Za8R"
    "obZmffNeoidQVq6xyphPewTKo8RDiq6puOe0zN41EQrjyJu69rQuk4fMB/RbF5XXbNgFtD42K1oha3SlOR44/WCAn07Vk/nweq8x"
    "Dt2ygtdUbl7ub8GCK6Aps0RjBKS9cLkyKLaMJIphwAtC8hkQTAAqIUZ1+4AmWCZB4S5LTtZEXHIFJ7a8wEeJmACSEuyXurEGGh5t"
    "ns65jIMK9f1UrPUZDcLEsCOL3Qt9idVUyPYBgVVCMuXGzAsM3QK99ceHENEFqfr4SWAV/kl/i2L/AGSNaqG8sIfFalwCVZDYyY5i"
    "7KKL/YHZBJmholF6qm0pPz0TL9P561tw8cnfW8gNGbGeQiE6B86I4mDIxz+Dsuy2I675bbDRII36kuu/N5vchyHcNLaZZa5ng6pd"
    "lmad9hkbN4WU7YJhngg6Iqvhu7UIx4s6keqroZ++sY2ZBmUqXGUmW/6wMKNVJaeZ97iGu98aB0k0GvJtaP8izU9LEB7jEzjky1bi"
    "RTVkz+5PT3bFe0/tloknbWSQ27XTZYcg74L2ZmTbQsnHAbnJe85lyzb5j365wXRzRQNWd1MLwyFtxvX4/Kz/TuTIWZLqROkry8lQ"
    "rSjzFvgTywEITeKMuorcs3cEgePGfpAh3X6b63zeFAUdN1MLtfrkv+UYoik14mdq8qn5PXZH2aVmj0U3SyYoc7ubltCM8AiGETZK"
    "JZZr6WFvIT7JX0/Q8/wHld/hbDU3/BIHaDJpiBYY65WFFUo8oNMGblP4oKX3gtNIKLowYMWTJCoAhGPMWKJR4br+VQbU81WkufDT"
    "HczlqI05bv/07a13wZMREtFIn3t3xVF3FDFUIYyWeHXT1HMzT5C8+hMCpMqdyDL12KKICR772x2KfuLeQNqUXLe0/HwR/4t9OxTn"
    "fPU+T+n1ny9Wzy2+KkqjsCVO5+UEYkv3cJWQkNt4mT5lFBJs4uS9K9SiIVUq0I1BZfBvgiMgcZuPkKUnCql4aWHOHtzxIAh5CJt5"
    "Hp7SpfY6Z8LuF1zaa+HSJ/TOjTLaWF6CSy4zF0clvY4XoJmScpx4BzgqlpOxbrFUuLGrLGpA9BV3G4vJSgP5y+LNicZhBRSDHGlb"
    "IqV1lMKru5Rq+OzJX1boK3uWfbMgP3ppMs4ivIQxDgBmQ8r0udJgN38WDDd+u4b29g2v/9jL1WmadvAk+nksGpYNPDJuiERlSCs3"
    "GXTKv11JvmsqVNhNzzG8kQQIEoAINSB4vN3UWPOGtn/QSW7QvuPjGdZvE0SSDLCNeYfUyYELTSVPo2RvKasGA+NzCX4QF4O8s62z"
    "BT3s6IrKQOZlcUERGq8dtjvEkCqfLqER6vi7v6JmkwyXL+1ZjJL69oQNWPXbecm2tk7xRcBZXXWW294A0jipZHMc6S3oZ5solnkq"
    "uhDaRqlV7hhHWMIt+3rz2Z9ulkVR9SMWvCha/s21HbtegEu/mCK5XM1PVnIkQwgBukSRgCteCzLonQ3iQs2TeKmeHMj0der4C+qo"
    "HQ/mOo7uXF8WtDfGa79jGV6nyT6WeEw0a9ui35lEEAPrSNnYN4hdYrJmRPo7WQf+hcu2jB/ikUy7a3MbouMiB1vMugnN1UD741t3"
    "706SEn38VIQyRh3V4D6wPlBP36Y5Sll3+bDlZoBUwVtxlhy+OOL0+lxQEfYZn4vqkc7f+ubBUQuBBE3Ygk1jDqNArvA7+azUpX0R"
    "tedP51X9qobJp/4+HP13x5r+f0wubfH/c7lAzPjXXntfAQcvoCAbfBD5c0P4rLqj9XeM0PYZs/CfZQJPeI53Wuoh2S54pMLRsPl1"
    "Q2AH4S+g/9lnbwXpZy9LjwF/nViA9LcUsflbUcZ6edZ3grkxShQiokQ4uoIdHJpCJ7vZzd4MUlCQjgHejM5xP1PzkVRogeSuQK/d"
    "MCyENBNP2kC+MHn/M8hDVpzMpJEyGtkLtqOZ9oIWmAOpG4V6B4RNankPHkeP+CXraAev9Sldxr5PC3bw5IG86rMIibLqweWoR2wB"
    "Ec4PLn939uZWbxcpaBr6XQ7doPmp+/ccFAwsvo8vq9ADhG0vjllTSjE5o++cnyjV1Z1XJL5uo+iGZdM7rOK9Zs36sBb5mClQES+h"
    "8BjD4e72/eaKDQWCaXlNIHUrIgkPXI0tN8sFdXP0rlSfn3KrCjOtuGPzHpG0abnuASE3xDQxsuUT6RpKBt4Div5g04Z7pnnTxDs8"
    "ffYvLtZDGZnJXP5RqlfRqtOeGTQSsn7yddQCagXAgV9NzwE32i/kchBS8KIbEkh0vlsY3lvZE6+LU0lKhQ3X2mq25QMmKdlTxsZC"
    "f5YGX2UkP7IGESC7HsZJ2wvTtuYHbaFb3O5TgdH0TXEd55O5l8v2Q0NHzq8P/z4Zu6dTIt2qZ9M5svXbuRWxgUnVqFsBofk2vi3+"
    "Qt5+4xRPJgpnoU/rGhz2vlxg8qSDwRLyBf/ikU4YRzGtSLWUySjFgrMgluwpAvVUlhG5kDxjhjE/bw8PDKcJivO94LXNsZ8j+gyV"
    "mcsxI6xmbu7ib1K+fVVgbRCl4PulpB/PVAAeAT8kvhFo2uKQnjW7FCIfxzWBj+AZF0lncXr33gen5JduFxrWgfRgRYC4fF4Pq4TW"
    "MtUIVOrHzE1dc2Vb7BOLdPiQs293oMiwSlfFYbxeLtJnLryC3JvaJmj/ZmEubH9f+hSHBYq49AfjUHr9YoeKAAkjZ0onHZZ5e97p"
    "vQWbUiWHl1XwXvTfqpil4alrk1WAHamMR0RppY/fsXYN1+QhwdtuzKR6zg7w70ba/LGEHTbE82n9rQoK7lG1nvyJtnzGuHxJl3pR"
    "p7vach63sb8eOomwZDd0+QofQd0wlPii+FWF50S7G1QXuiP3q3k7MOkCDQeE46IYazhwR1Wptdf7BJy9ggcd4kFpQIatdhwN0/ra"
    "LfhVzn3jrnzHyILYGVQm9nZKt4EsedgMPhwBVo7KCB+nUzLX5n3HAMRbqZl0it07MKIt4Qv7fQKlHrJHYx5ht5efz9wn0OG/abnI"
    "VVjkleZPpNvMRWdzjM7C6CgB2Ic50KWV3TEXRZD52+6t6nsP6pGt4EeVIvP2NiGxKdoiLoUEtRj/GqrQp5+ZEPMmoG8qo9r9CgSx"
    "OKdy1NrGj+UfXKA5m/jUwl3gRP529Rd7+0MWZI8Z7Jch7qR3iDGUk3M5WfxH7DIpKj8qbL8C68sDDWZJWxkfkEDytfg8knNwA1x9"
    "R2IZeZJ+KS/rswRTsXLfAtWkwUrh2eFLumF5YEk7rsD5S9G4uvzv90nRbmIVmm/aMJ3cD9vHw0FT+j7iYtNiUK95+nZ2q989U1qh"
    "6YilvXSUc0URhndZ3TaMpfBZUklwAC2KFC3cnXQYyE9xSbC1k6cHrV4bkVG28rspMjt18V6c88c4eqIFvJACTSQkuTCodDO2IK/f"
    "LcywNeuYbyU1ZczBXByQ26l3dyay4XPk9/kwz0tKzLRQe6zQM4Yh4Dmh8/LgCxzLO/vYfBVyNGDpItxRZwi8LCvL8ea4750xg8ka"
    "Q7n7kcJIxbLRVkpIfjvy6KY2hRuTL2RMc2Awm2HZzglCyu0X2oJCekPQm0BcITs1RB7TTTIJ04PMIwfAs6ZgmRUXv43joe9HcSm3"
    "VMo3MrDr3TnswfcDmCHTekId/2FM+E69N0PI2INso+vLhqRUo2TsWul55vc18uGop4zTF/cakeTIkI3L66L1updvQtYQZweeT/yo"
    "bU8RRozYAlraR70MxBkAGISp3fkNiDO4Ep0zWPm1XfUKbfTpeYUAB9dnggh6gtqw1xn/XbnCpkw1M2aDBMeGzBw1RD9Pa3VB4Zs3"
    "lRC1JNHRQ+swGLNztgTQrFduGlf4qx+3zd59i6LN30IBqvU1u55oneO0kbF5iaSf/DomXHj73ueAxe0OehSRXtpefpelwSCkZmIM"
    "52eWXWP7e6z1x/n0DVTPLzmcLqs20DrV5qf4KUCL+n6h8AFxoWXTicsCqg7LiqQOQNoPjpqymWT4WieF9RzdcPfr4hnh5yLlQTsg"
    "92Vff1jmFulzRmVGz8meDmVbwWhfMc9pMTVdILvnyCYLN4S4ratIo8/iEL1np1YdcicSa+Oq/sRT15dHe7HBQkOlT+OwypsjWUF8"
    "DyTZOeMt+grXvzFQPQkmUgHrmVNIYYBhRfxGvmnOAjIkypblAZigVJ4Ms/ThqOHfehUKLClH1KIjulhzrNxMzj28hFxscdQGRC6N"
    "3Mu2hqKa1I7jD+9UpheYG8CQEcHfZqcw8opMUFYHOj39oM1Yt9lNYfX1fI4xN6hSTwJyfOmrvBntK4HoJzIZPUPnYEL8bQakHqXg"
    "nl/X8Ujy9TOzodj+tfd8Q3kieeFchOlZ2d5zsXkF79erjS+VoX0jArH16TtrdiIF58IwQj191fLQcwMRHFeVWqYqhuSZyJq6CYaR"
    "ylb3+6s6PhizCFTID/JToS7tcU5Bs3ShqygAfT7MAhdmAKF1L1Nc/+Hco0Z4XQsrru+4lc/zVd24x2hBU2ixF1uzujh13Rhl1nFU"
    "YVuav9VLfNOM2FpgZKjmVFO8G12t1lpICznA23BOdWjlGcZiDLV5pt2evWtRpoQI1mdpDtqePj0ubYcvvw5gqX+vTEA1mVlLceb6"
    "bVtXn4+4+0M75k4uoh71fL5bp0GoqsARdvK6WCyCnN8llZCe6ewUaJMwGAFZQmAVz+Riu76F7Cvy7MLUeHKG/LheXCMtNn8u0igv"
    "ypdhsCU+38e//LziASYwnpd71aCGtMy6N3Vdp2yjA7Ole1+ou+gmzI0aFU/N6YlcspxMQZ7VXHs26zfGm2JbsZWOUDhOU5XW7p7m"
    "orH/GEmkjNlv+v1mJrLGotciKvx9Xdq2Cub6UGH49qrqaiLPGscdwculZw2DK/IBRvIxi1KFJ+4gsdZiF4pr7BHyfaY1HVEdYPmN"
    "91h5BA1ulzP67btKijbkBW0mI/1ua/0Mirgk4meNTuEuHwJIPSR0W9JlaqeWfxVcygJv3CVuD6PWxDYK6Vj9iEyym+a34AnQ0+43"
    "/Y72c4nM4ZSLpTwkGn84uSJCPkcPTZVZOdN+D3ToGQ71Epg+/oddXMyc88Umg4/S5tfKKTxUO8gUZhs1o1Dvy0Da7uOZ+PSeIA3h"
    "5sCtrj8313yq/+hwOCIfnd4E19NdUIrszsMV+RG9E6PEN1J4LQSn8U4CaFFwj4rm7ADU1vvstDEWbcB+N1CsVRmpLzZXqNGKLGn6"
    "HQXDqIRJQZ7mM2TlseZJOjmXYnCY/y6UPFMkZdjWkLBSgMqe5D+m2TOUxgxcqWNEkOLgSpdoWi5zYTO8MrELl0+xVJeh/qbAt9Ba"
    "7U2rqzrDT5sBegvkP2qnkyb+WzRDaUBTD2EJwekjrBZAe49K0hsYpImigD0oUALgwbFsqQKPbeYUAci3uEyFSoLIJcOErtgovnpq"
    "wKa9J0MnOMAkFKgoBdYCtZmzDmY4yvHNKSkEKuSSHWyxg4tYkjIkjkm41exGuoHJCe7biPzPged2O+Q4vxxO161AOt4zJY4v7mLf"
    "Gia0Hi54lmBXx+ZQpakSLMKsPVy2J3JFfF9KDS9tL4I1WSHjntlvj8HRsUSAA1ffq1yZT/BUyYn7J9TD/kWym0E9fElKNLH+anDx"
    "U6gGcnnk++dmfEGwHjMEi1LbMV1dX0iXTuaQnK/kAE4Dq2dDJIVt7tmx1BVQPJUPgXBqnDFtbU0222HqlOSl6pmpfVIST1Hgxlxo"
    "ZARNz8epUkqhZt44mD9YCWKuH4qchN6bS66LvdGL3wsDV3w+cbW+frxfXLkeTM3yUIrbVKHK2RMcZpJGpimvbYrkNqhHIICsu9B5"
    "b0S9xRWdtHPVfuUegnqWkTRFn3h0geANdhf6O8GXdduhPQ7DJhIqRlEYPueCDtZSk0VvyXabKI4JvrECWaLeBEDnbBlwTbZ14iWZ"
    "/MBIhwxyNLk44uMnCFPgP5MVkiIzDHdrzP9yZ9eqNGphZfu/7uyKbhadGWvZwXlKUXCqviIFVPoqAhBDikmUGxHwIQZjusC6VCe6"
    "BaFq6uhUBwOqB+HnFkDUp1uejngPNWn1zIhPnBMC+qDmoCzbbdiDaTgpJZ5K8y3A0sb3qwtgoORrbda0tprs95Atse6QkF3qVHiD"
    "0HgWwg/okOzRaFO5VeyGhmQtVx2/t5ZqnygAMWfXP30vZwmzfF3UWSzyuFV+bvmOlrtJuqVAWl8hHGcBEG7QMb6mYaB5HJocetry"
    "wMGO7P1ke0rnA6K6ttqLFgRgPGh/nXdP4P5G4EYtPkjuebk4AJe8SAPAY1ZksM1Xia6lwxip4jjZkQHvybeIp3R/QPshldWHmpaT"
    "gETDnpZhExvwMvFnLYsrrqUSMNXfnuPGjwGqX3SDuHCC3S4bprHuN2+0f/d8M2+F/MbMuvlR22BbQ8oDBccXVnRFYrUBNPWfKDZt"
    "9D46NsHV5lUd8fspfxXnJJAIipBYpcV3AqzIiStAxajLeFyHzJKC4xKfVBg+1X3YTr/OmuXScwTjUIR8yO+H8qSCWHokGw3O1MTk"
    "qJtf6pnnRoDpyaJmyM3LKTg3aNdbnAi10wnd5/pWP359K7etRrZxktkhgBiAf9CdyGSImnaVmnHNi6qnhITTIc8BvkhT3E5xVyQP"
    "qPc9Ibq5ry03ALIFAUgOnw8WdfxnCXAHbNPnse3YoqOtTsL04hXc+bULMmqft3bh7Q8OlJAE+m/1dd2SskLp+RlSt5hSB7Szu+2F"
    "d+38NwMd5FdM0E7PyPQ148tqVnLzMVDDRRJdZEYC873my1v3RPfEjmfmatOhu+Hz2Q2Rmv0KrI15bEhNiseuVb6qZTi++PHriRO+"
    "auBxixoJr61LwTR1UOEqsG/6yBeSWG1E4o/v7I7hLON15JswodQtFOElQxNt/HKScbDBCSCFwkAwR0vKrBLlW8xncp4MO8te/nwv"
    "br9xS3cRonTsJ0jAvVf754hmpvwxJHsiM1rGQq68Ds5MctrxaU4vEEAX1c6AKJ/GVSZ2qv5twkVlfm3xKJmAJ/PFLehVQlHMus/H"
    "Bjdbc/HBuUJmoDuI/UjfpRr06m9f0OmFEsevk4epK5fw4aDrlo18bAfcAezEHWHYW7S6tUpAsDhCPCAEKozawNObdlp/eWWYKz4/"
    "EMKL5ZLvLXAvq+7zoWJ//OZQHZajrzVYiCfSOf30IZAtNhGREUgRHiIuGGmSeBnMWWGS8J4gi0lY72e726PhuOcouYHb8GmV023G"
    "KVYwBV/RP+eLdW0NlWfbLtVLDRkBHcVMh/ehQRzAMMSkdj6f1pJnByYDdp0zUG/N40AeYIIlM5t67M/wBxgGxO/Wd1+OwC/B3CXr"
    "BelV/1OeC6nja8F+y9ktR7Q5UF98DrE2uhKBxBV3V/vOTMMmRTDP226wO76qU/niVzhrK+g4wM0bTKGSnTBROe1XvSNUJJ/pNc35"
    "3LoWqGI1xPZIbYb3t93QOk9ol6hXqzdcRuf+105LyAMS4DZ/R1D+UpS3NoIDAPQhW5hY2RLE8R8y6yclW7TXftMnquKXoi7sdt5a"
    "Fk9c7enhQjeioP1YGIblEArFo5yE9ApXMZUHx1bME+a+QcV0hQGnMr+PITV/Jk7TXPIFaDR4JrsoUMWYBUy0OL1zrjnqOScrjp/+"
    "IJwS4VLZq6dAa1O48pR6DCebIRaLMRehOtMwn6M5+BHPbabLkK9h80RZLT+I9B/7m7Tly+fw+mkgD47G9cODpsb8SEYr59RtQIOq"
    "W9Kg15473ktgg28+m+8PUoakjX/LSXwuFxHVEDJ5VHEmmJE0kksWr6HnqM/27/FydPkNn4A74khmnIyyGHlX0mXzUZtmJGFHCBEt"
    "T+5304PJHsQ56p8MTkjZ/26iVAKQ/csCJeVZmIZ+CSRx7FA2pCG48AAHPawvK0BFroWEJ4XiyERyQAXE+G9FYVkhEmQUJjDp2CIz"
    "XF2zKmPGwPT2mizcyUIaXIv+tQT7zboFRXsHPEQ7ips2UFEoar0oPGfMacS3X7rOEL1NHgcWjcUEE67T4lMyEUKJcwmL4PrmADRG"
    "OJzm91T1oq5+z8F+tChKWa9gFxAKtgpJlFpYeXzhHlkFgdK3u+V1aClaAkh863xkPLKpolod/vRmE3mOYcwl/O3c8TLQ5we8jh4S"
    "0e+z4rdgPHsj6jDMVPMdMEfXKP00r6qmVIu0WUDHW4zLpQAf2K7rvicCdu18tQ4Q2bddxAyBrmdUlSyEwqVvn4BEJKRy92pPBYXd"
    "Vd6BTtEN5ez0+UtWf3xwJpLQzvykd1M1nE6OqN/laqBE227+bLFgNRx+kDdfW0xbWy3AtQ/jT2XkMgFVvngrSowFnpPbcj4yDSVf"
    "VMjC3K0PIMdoA77amffFTQKjzSa5GN3jm4QfPDKYcj3DToNDcwdxYC3uIVUpV41NNrBv/XDyyfYTg1SnJ5+B9ycMcO3d++jSHfCS"
    "Ci/XJ9eMM2pRyPpV3zbA74wrZNriQZoRTREPAKi+tB9538d/3c707//m/l93M83e/2vCSb3/mXDahSw7xp5Epr/1YZMD+W/fFkQm"
    "27x+vvtB0sQX/iAXqp8gSQWF4KjusSLrj3Hf7q7eejrqJJtH4A3bcqEc12XSj4r/3XJDbD8avaJXnGHZOM799/1+b+iLOwU/rGMI"
    "oEr5I/EsemwuYC3pQuEWKA+bQkBWQz86CeqnA1A0GP4ti0DjFMij2waSIhKOxSNMr0gAKCuMrsJ9knY17bTAnmIxnfJJw21ErJHo"
    "QPLc1nmNPWs4Z660YYwoF8EqwvM1SdpwxbmAZtIPQJ4uX6CjwyelT62JYqQRWAWOihA4kclER/3Nk+f6mNH8gSCml3iG35CsGM8A"
    "QUlxYbFPM2bC5Z2wwcUguZSCyyaxsbrPQZHuxD0YXFKq46Gte0W6VhgffDtQoV+/Onsq+pf0GvtTZk59H8hPx7ZqwoNo22yBrVfj"
    "9lzggqaPkdMGpgsyQ/IFfcB2ZUe0cTOCHsg5XJr9GFMoihcC58gXgAGCm2pkkJwC2f78z+SUzv5hUlgqjHiQfzj4OUED5q/Hli0p"
    "/rJM8xQ2yAQGynVmaSdP0TajQ99zigFYvLwVOEdgc1wzYcWDHOmnZ/d//KfKwu+mAhUDcgxrP0vnJfW3O3T3ewR87NX2kAMjV4EQ"
    "wOf6RS+KxMQKS0MUkZVj2NN58xWYkOFskXFjsjJ/WgpCiX5xCkcb7LRMyfjbD6fWZcNXLIE5FKP1+XMzPftjN2b0kREiaS6Vt5/h"
    "ib7QBOf8387AShhoEoOIRIpTr80lddA76i+O4Vpt5c009TGhDVqEt/EXs2C4MPIPhhYvueYnRyhTb+o5yTxEqOn0Y0qSLeuOj2CY"
    "zOExVn/EF66beRRVosTnPEnWqK/9m+HX2vV3iZjrrB7n+IJ8i38DD81Mll1Vc/yqXtCG1YozJfmUFf48TkRY1qbYmlGndks6i4qp"
    "Qf6nTjlIGtBej1zqvgLX8zcmJu/TSa7oc+m5IYSa0OYh5CLCH7zDCNCK1PmmRtQdXB/c7simb+ChbULvE2LEiTRsr20GeZ6GeP20"
    "GOoLqdXPxjAmYwer8qdNZ6aAQ6kBzbMQismSKfhxGC+EUlM25vyGjVjZZZIavuxSa5Jy4AWlILP75AxgznOJtO8QQunA9tewUfeT"
    "lsQaabFQR3EXnkcW1JxqC7XavwT0NdJXvfPbXtdcmwGZFQPcNdkYz2yMQKTvZgphi6xch9ZzO4yC0Xzbd/SAFZPELmBWWyCdOOF4"
    "LxlfhlxFIrOVpzh3icMFzmb8RUMZ6Eh6zptQPLGs30CPqMoqM8MpDeLEdTDk5S9+c4JdTELgXSRzJ5E5KAJTJSfT9zbBH2RuWW6o"
    "TbLALEldKJunqqRNV4PYuFkJHLvYM4cgcY3JvbJucN0eg/F0nNwWLscAff1gdyS28YGA9bH/mcThtsgLhHgctAaSxPiX6L6r1HbQ"
    "sQBGQWEbRJhHZpj0HbNIyilybXW/c/sOCx/NEpiEoPVGdl5IMH4EC7lJoDaScgm58F0N5X1HgTZDJJsodPt2PVZ5HVNBAvxczUqZ"
    "oEOU9XHNa3k9WZYFkkNLS/1vcUBa364t7LQtFTfFYLGQii4kQT2OTv18/sYrn646Q3debubiMhD5dgnyZq8MvL8wdW5T8goxPGBa"
    "IzgfNZ9/VwVf/UkbjwYvjA/ZsDyAaVd8LlU0siOqjB42gFFBwOdviTIoLm4DMXb3lWQ4/0qAfg4DbJruU92Q5yq1t5WGkir3A9xc"
    "s3psgwvLWSw/H9JqMlAFKGcRixQM76nQGrCjYuLa2FXd4nu8OS8gqTkNVMgoeOpdKAI4mXYu4QPWBPrhZMZGlbv/+fT18WiyJ1zu"
    "WATFRwURh2KswMdQZJiftOnXN+Hq/W/THKfstgTMsxaAnMIjWmkQfGGr90BXXaxOygGEPqI5Q44GbHqpM4lYm2NGzC2wPr8mKeDn"
    "3uRVP+7RdOYPNxQkEm163T+36R3dbsF8zNTZ5X3dG6ggcmbfeNlTQT1aY3uL5PlRIIEVmZukB7ZHs4k9f7V1sFBS4xVlo40RmAVu"
    "uf7w/c4xl3s8cxSE9eqCrZ+61gmK3gOJGiOFRsL5uDYVPwPMGTMl841lZWFpL9Y/SUCc76B+NjhkIY/0LaSwguX8NFTIMI3+mG9v"
    "SNARVyYpuc1ZDbGXNzQQdVSmDj+b9v0G6uHshprrJtWrTMRcR3odhPUBGt4lU7yXS/H3qqa5uV+8Nx0zv+QzlMa1rr/zr3qjJvfM"
    "9YY0VrtXQ2mXxX+EuAsu96uy5mq6fJTfSXFbKHDpXGRHhz8IDdM199jbgxZR5JnE+4kPlGj5i9ijztkSNTAWmT6OhneEVPUevN7V"
    "Ux/AAw/LxG5P81QZBVE4x5OnKahCiL2ek+7hLvn91DhWY7mQxQALQ+LznemVdwzFZ5iPzvLy6n7QyiXncBPeCq0lHj/zeFZ/WRxd"
    "LfSoEJjM7jAtO35hNFXafkK7YoJ0GHGOT/ImljiU+gGsbepiqB/XcH3BAVPbHNueBLI3MZrY4O8MYlOeY3+PsONU8Z3BEIIMTUlY"
    "QQwIAC12BrBKvgN1UAh8ZmbDk527+rLu5ovEXppH1Rgn41U/nyxfwlqa0kARkkBzgkIskDtyaHLU6iaNTc94TEQRoV87RU+pA7q9"
    "FH7v6FI+Ops58rE0K/Z8+huEFq7k8CsS6AwBFNRg9HeXtCDo8f3CrPCVKUNDmkyn8nrEMQ31eFxqSCXvKLOGX5Aqh3RiKeP6hh6X"
    "CLaNFb4+g5A6vPmKKIBe7QIshsvH8D6gFWFen+PK3ZB19ELv4PNOk8/IqgE/ENiyg+nNsCD60BVyNjfv4qNaQQN8DWVOxOp18yaU"
    "qsThgRCzAKXob3vj5a0BBVyjBuQj2a7Wc5gBtCEb9v7hycTMJa+JQfKS1srndJhPMaweKHzZFZt/iNblmTYcIRcK1ZfkQU5sl5rZ"
    "Xl5etZgKDC9ABkIyEIw71qrotLnfiMrGvuGKWxrkLZgxMk7L6cGOQnFf0QQEtLY42D9ECVz/gZObGd66bdjz96oZvWVSkRHHqgWD"
    "+9uDSeJ7Y5ajsMKwck8sqTQzrg8xgXN9XFzZC1+g0uVHayU2XMhnhLbEk9OZU6fvl9M86YP3/RFohUzZSexXGgCRK6M510Bhg6UL"
    "UgOliL926DGqvsJHhFB7rd88zOCgR15+EYWCLkafGf9LDx98+fAU3SET9pJVO8xE5r92nlctxER+s65W3yGxtgzdL0OYZDGeY35P"
    "QFwDBa+obGSAzctOd+XiTJL7P4kvOkoa9BvI1YVu2o25tVNXIHXbuNqqpNBDmyXp9tx7AkLEmK8c3Gy8UBIwTU/8OlkNy21ELKWf"
    "MWGoPXR4xatFzjqv9faVe5S7tircW/dHIbhp3R+ltULtUvohw3k/EoRAlr4lm/ujpwwrmyKOhi0+9VIOxpP9C9G+a6DW/pk/QC9Z"
    "SSdtidN7k2l/HbYW413YmURJ+PT7C9oCayexmDywsYL0xqD7Zq1DbjSCDRZC/rkH0xjUhwuVYzu828oVcf6KtARXqGdOapx3Zywy"
    "av7SsJGX/eemvOHnnzc17Or+FfJmUSAoEFZqsY0azB5KiL9hCaMqxOuKNDxHJtmKLDP4QHqSggCQqFvUJDy2SjCJarBJ+xaCCP/C"
    "rZDZ3g0cA3dz7R5KgngiEUELOEa99UmIqWmrtOWUwtzK3hrKXOfRYqdwWAWzHVebJDR1r1aTbpxELiHgpoTok5eb7TVPsCRnG4WL"
    "exJoR6XL/1Y4A2OmZTTOGNAr2xMLCIlJqUXuNZ3GvPpb8q3W5hNp00j2LZjB1cdA69tWOsFvrN+76LFvn29Qf3RlnUH0pnkPBinS"
    "PY8zc5Jv45w7IsGzlAhh8Tf7wydCz/VVYqB3vWojDGuqWIQ66/dXDMvnpUsJfZgZrT3F+kFj3qu5IZWtA6BD08KuJTthtlaYL7h0"
    "JT0IagmmmT1m5RfFdZ2NJWF6YGq+zbywc1QxAILhKuSNqSFYsA8Z2yl80eRAb761+mqRAhf6uHQddOtlyiaWSQFJ5q/0KS52fedq"
    "Vq8kJikSesa/vTj8Oy7suYWGKLwO4KURormjcxP7QBrMHyYZBvn14FO2u0gV6j5IB/KxGPJYDt4vSgKddjh9qp4vBjN/igQLetAB"
    "cOJ5FdY+0dHFcRDPejn7PSSNByPZMfMITnFdQMyxwl9IJ+l2ySiOmDwl4+iCBFXgSr4of03W1GMB03FkTAOc/RB6BblDt29BkMB+"
    "8znSXPqgzazeTcit/tbZv4OUqgDoq0vFi61f37+app+qNAhiMdWp6CdKB+hvumy5e3hKL7k6bBL29xLiCIDAqoQkdT3xJhvSQQwc"
    "7yX0+bommLcZ68zJqBCrrczfOyBA9tF8d3U6yxtnqn8+CoOoqdPcDLf0CmUiFDZZikKA4cV/0brrs0TrhnwQ2V3gYfTTC1/xyH/X"
    "sz6l9KAqfBFnzyU78nuBgI7lb4hpgATWJZJ+e6yVgJ8/cTuWFr5bamwNo9VAS8vtOq7ECEARBNYC3tbW/W3awJTDXRHMoDDqoKIi"
    "joLbjJggMw/x1xZbtAJ/DoNafEMmX/3CCS65f2Yg6wOVPysou80vG4iX6T5nSAeP+R1wpVwHIeSeCbBgu2IuQ1PrXgj5lyYKNo9v"
    "soRdsWvsAGJWbx8UMM44oAkeVqn33+6m7RcU79UEIwbmV43kArm1/hZE7KrTZbpyguIBK46tDxwviyIAPPIEH3D72/ugBXqWSk/t"
    "ECYLvAN0jttE6ywXBANJeqK7naYoeM0MGJBcfEbmoTGwjm/l44Rb03aRYeCaEKIygCP7R24yZfE57uR+5C1W+A4enUzR2QqfG00u"
    "aotjCfkEPzQX819ZcjGarRy7+dM/SxxqRlWGKXdQnxCq1diAoXqHnu9DpfqYnXwXIgl+iQGvfGb+ZxktmQQ/GmkQ4YUOi56qg7LI"
    "nP5SebmVByPMh/vrjX2+hIF8EfvzAFnUATQ8WfmVs0KdHwBYJXLurdUHY64kqCPLmPS8CrIro7/ZZ9uVjm66lu41gEfHO/IZ7PNx"
    "fzvHujiqLWkD8L+PlLLg822+Xc11eup+gaBfP2PL7zvCQQkAloCNHMPGagQz/WLzjE75pc/qQeXYpKtLN8wLO/x8auhVGxxjvzeQ"
    "msfvKW6WEfFa3RHGEOrzLbKxeiPDNysz7/r9Oudlsn7XrtiyF8Nutjw4bUCoVuJI0BqSP8H6dl90h37qB+/mD86qn2kPOAiCGRfH"
    "aCYaD3zGQg6E6SEFqhARj9Ymf+3qu7OncavMPeDbCe18AUnET9rhA2ujKLow7QLsJ6z1IzSnbv698sg4JbBaN99ZdJEefZaBU/C8"
    "Re4g4A5nedfRWpE0OF2ad8PCgfi+yy8zG4+B5D3zoW+8b+dpDkGgXF5eSHK6IjoooU5XVsXoBVA9rG98Mne7Tg/CA5XJh08jBhhN"
    "Vjw0rw4/3EbJsqgGoTJ//53jnZK/Lw1TlNJJyH8wdh5LEgJJtv0gFmi1RGut2aEhEQmJ5uuH6pkem35mz7qXZZVVGTjhfu8hAg9l"
    "crywcDSvPCbeM3bx2hNyop9y0r2V8SaA+b6RHgNR+/RWZv80fXTs40ENwu3bUMkaLlJXqOL7kbJw3oBgkRmZr1t48XVHaMcuRkwx"
    "ZBVopteGQJWaKdHd8jL7SjMmFmjwAGRCjMy96QbwLZpmWsOpNRlCWjQTX4HJQO5HmImjxbcDba4qz3XnTbzx2UO8vIRLqXK4vBrX"
    "4jAZNfUpPBTO2C49VxuIDLBgpq/JX/uF54Q7tdtebR/Wz5swFyhUXcyV/RIIbKBREk0lDztg/gHCH/XMoOYDaR/65zeu15jEzA/p"
    "wO902+sI5Mwmrz0tsn8ttV8kQAA3JjFqFdZ0ON7aJH5hpopwEskyEXhpWYNRM/Sfmoq3SyTfGWbjpv3SMUeKAwI9xukbkfT3NEtf"
    "YBkve1dhvl/dt5aSpAU72+g3cuC3cJf11G7yszI++iz22KAoZN4fZSQbjSU91BqciFQc0sZ5AbGFMxtlqOg9ylmkv+Nipt/c35iO"
    "/NwUmzyUhjf6144epeN1fvN74a9yBv0eCtSwmHu1nKUrOdv3z5YOcsCGCbj+oMuTuBrsviHugiB4PIv16lDPDioDXdBd7FSMgQoq"
    "AerPhPhqi4fxK3PWW+qwik+tWFCvUBFTPp/qXhbg3ke7NN+jvgaRCEabMjSrDnuwWwvF9IaSqk3l66qcXIRyPuROAJHbt2hKZXL4"
    "iPqMPBrZ+peUkeIie811us5xI/ubOfCWzMvP7cLUlkixJ8ufFFFcGXKWKyOnqPzw/pGlHxY4eje/rJWm5eW5WS4dOK88E0qMr2RD"
    "vwv/SAktzJrzuizV3e9jSza+MppTrl1eegqWbF1aBAYQBNCbt7RFijD9Y6pY+nM8xn4LA3Nr5hO3ZkfNh3Otd3+JAyTFZv1WBV35"
    "tG8K6Mk/W7s9/+68qMT8jxZDmF75x9s3SrmNt6iCBy1+S/jzWh2EzMP/XRCp4OOz5QWe9XiMx6hMQeXoikkthjFJdWun9jyNvrdZ"
    "bFGdxL34cF3bsnyNhUG6WCmkyz07zcjKJa90cD13bHukytf6WG0q80yiBPBEYsBvtVaOb8boYWsCZBtUzFaolTGs7sCv8YAWoNbg"
    "CwEA+vD4jX6ODwzdAVDwx2t2pr2+NlTWioETGc2PhL479lCqh1nOYppaODWRi+7shuu94oQRuIS9iztfgID5SYX38os7oHiQvVev"
    "YKBk9KTdp64qAVn3PJUiIUc//65yHNdW3QIt6akXu2nEY/TLiVFfM3kIEHFFAstVWW6z9Z23yEpEYj7Gg5vgCCX67alk+PX6Bi/L"
    "tv0Zv3n0OHksUMFj0lCngyh6kVaQHNqatCLJaZoteYNi/45bcEjaHo7qHmFa7Dfz0N8IEvtC8uUYZe5MF7/qIX+m1jI2+giGbf0K"
    "ZwiyWlQ/T+SpHLPEEynYgnwFRc2Huvv4POKT6qhi9eDn4B5eSs+9E+xrbGQLszlMm3LD5sfmG8FxR05a2GUZehvcMI7IfeL3q/EN"
    "t865AvdFkMqvI9OJIn2q/iGd78d58l0IfnAlvOLgW/fxWCYg5uzFQ2UZqVtviVNo4mdGz7LTHTqfKIciVCuMm+ae/2aP48H5i4F3"
    "KGEarHV2G+bEOHdi18LeTIpz/FTvd0oMzyissFbzoOBU/7ju0MAuPEs8jGz4XrSsHBczfDKscPLLPo5zkCP1PGYOqBMm1/bkLyQB"
    "2frbDLGLX/71xD2Citq0m0+qN/Z97edSFlSH0mT5BJZDCV+Obfu6W0IVv+hA894ZxuIx5+mAdf/Ghyfxfqtz9u+sGR+O5g/wnL/k"
    "xUlNuXE+yV3TsBn2jSZZmIP6I2ojLBM4GlFdSkUWZgSbcathPMxBEONYfR3DCdBZG7d6gNbLmpKMwVR+hua+Os3ACiDaB6bJDVRO"
    "lgK/7C9MkyRDaa4jSRjiMslrCU/3OnixiWP0t91pOEYxk+NhSWuYCv3ZkogzOfBV5IyaiXB7VloLhF7wmrqkXqewIF6L7vG8c2yk"
    "Jo5cLzdh2nK4CXL/YYv5pwvPQvMmgsChb3LVWU4cLumbRuTFx+VWFHerPiReAv2AF+F+yF+hM+w3fIL2qPRYR1UJytBh10CMd0QF"
    "6lUQvQEamWho4M0Aqu6sI5eQQz6fKuVti4jjrwhaRRCu+LPV3nXSNEOV5BFztLpA5J4p0q3n4fd3vgr7k6TnKTiPNkcAN4Dl9TEk"
    "+hvtX/5dcz73sDCL0XBBbZxs2cWV6xv8pvsdmIY1PBBAwLFYrwPNhwkGhpQhRhMujh78faW8k1BxsAOd/Bb56ysZXF3P6Xf/FvJb"
    "Fag0abX1MZjtVSA/t90tw77A0DQPkBbE18yJ7XJWI9pR5FBmALW9Rvby0DMlULFrzUp7gSLirhccdsMIP8fCp/jCMTqN10IHdDww"
    "La0y+P7+b3NPq8gKtPmX1cq3zL9I77jMEYvsuEb1IrMi+WNvIM7PxV0aK2rbcekfG3mO7s2saHq9hmlAHqv0zACdICUWLnRvEHLR"
    "QLOZ/cRqUNZ938DF6jl8+VQ5e9oxPdo2xyQ8DGdk6mZ3fItIVefBQE3/9c2NUBWQq+mr9HYPPBDvtWs5sLTAo8dCDWl2Ds5+N1CH"
    "Wv4RZc2WBRxpc9/FAi2uDEgydITf/pxLlwAEocdpoPSxjUsO7zUQtlQGj3wTluWYvzlqKb9pQ9uKSTqW6b/cSs5BqYkxtn65kHwS"
    "gQk4BpzMYFs4BEjR29tp9GJK/TcDuRm4LyMg41tpuFY4q56PBfIqkBytBPw2NpqfZgi1bTlZSuG31aeqeD1PZLidQUQ9rOshY4tw"
    "BJtcQG5h25jCx9xm9QRiOzZEx/mG0J3PSH3yiplf0NRIcfg7A5IzB2cNYvrG+72yUEL5p8IibdqQdo+1b7HTQ84IHpcY3BiX+4JZ"
    "DKrRVCqNv6kMdHyetx9snFm1Rz/Thl5/M5rJXsAdndv8+b2qOXBsgcLL1wZNfkttENQzjqL08t7lroKnOiSdAv238WkXex401oTG"
    "buI7fEuyviGGYAzlHqsSGf3HaxAQHG/AL6lQmtn8u+Mu5dU9TR1xxjCnU1PX30abQVoFjwqUDodzRoTw2B8xTCRadTwZQxdtCXTp"
    "8GQxe+90XcO8xqzlWHd/9lvHN0UvpJ5OTxcSMCZWcRgy3IhSab3mh2SbhnNl+4+LyR03oKGJOKpt31rG8zoSZaRXLeZNOXD/YVhV"
    "4jEeyNB7cTssjoyVhjK+0siIglbR7VMyFirJb4noS2FrplQY/Eu1TC1+6YB8/SxlZayb1MP/sIYCCs20bKc9uOUNpz/YdCDfGBAE"
    "as7tDLjqB8HBXg76SqKvUCrCtk8qoE0tpTIfRGcRlZU9rJqvs0IIUmoPj4UvT+zwpz1ruwEC6MAZb95lFd+AojHZCc4Rm/vUeFqh"
    "JNMAA94DtlyDeep+0xau21M9tYpFu3Nwi9vVL3CgV1/VkDPLS+dvr+IpmErl47ymRQT511LEp7S88l8P0Khm4GO+pYCAWDu4NYQM"
    "Za5Q6nkDajzeSn6ta/syqia3Ww82roOg7J8T+4Y292SqAA7tC+eqHifwBWBjsUApHALjzajButUCpK/rlH7SMj5slM6jN8mjQfWC"
    "Q6+KpygQeBhQRf6oC7CC2aaOn2yPwuxOsNYqgMyYntePqaAVv3SxrZs/5kODLs71KgGOEApr58fQUs3+BX4vT9BowbD/eOhFN6+t"
    "FZn6Xx96eaHHOR+lEz7Ub02av4deEUnV8jowyzABKT2jgEZpBD1d5ESSYhpMxO+xMDk+8WOVgRdu5J8NEmBf1TbQscDu+pDRpJ9I"
    "q7SSBWCScozrG59ud8BlKhviY/bMWxWiWpEx3G+r+GL9L2FfcYPhB4vNrjIWBdynN94xqdmz4K+q/IUH8bKr3R8WVhYKfOlokNk9"
    "tlii86eCsXcCsBG8sCCsW9X49VMMH3A0BzrqzyCO1o77W8UtnHQwNt3sxlgzhqivDE7s/AuDXh2G6w4ea+Lgv2Uup9vI2hQHSZLf"
    "whNFwEpFkBqQiZ/oZ7ct7VtYzJXudyAGzz3+2nvm74HSJb+GoTNk0kvx365ijjr6KJBYuy3WyyHGawUEtzkVPo9amj9N9tmTM+xN"
    "EWVUs5kbPAjn8nm0nQpO4ZKXEQSbl6vtuNlh6/n8tfAd9nRljs/sLMl3zOxI4XYRD/T+ZJDj3BseiNHBpwZrpthsaK6GehIGPLfq"
    "c1aEh/oYU5X+8Alv6xMoNQA3qz+GKnlR9kVJKARtnA5tZZ3Ga9IyjcAD/pHLKdllUfNBYEB7fgUiJR6qRF8ZryYooFg+xpzv+gVg"
    "Gs4s76NNEdxZSyflZ7fYZQN47qf+zpeibx86ZSgSyu2r3pZ3MN2gZATEuN/WPsHABtX73DFswvZ1v5jpe4Ww+tVwBFZOTcezGJ6e"
    "vp91p93IYS6/ErSh1Rdnk4c8hZ/2nMJqKhbHvB5FaoBFFHwpsYZihirqO0GFBSsSlb64JllhwtAEA/l94PBF7fztHZnziCF2F83s"
    "cqUbKp7n5zADVqXgbcwQYMehcekAxr43NnPO+HgLAwACEAmClOJH0DtBe9B82RKYlsBqXUmV1r9Ofy8ZO2nvO9vCcAp4IgkaeMzo"
    "pY4wPcmROLzqtOLyCAHLeQ3+o3arLhwtBzMjdg0mXrcvdLD8B51i7L4U0zGw1Sx9/+rQ6b0LEH+G2CqJhlOUZ8nkg/csjqYKM21+"
    "24e2y6H12G7rtTd+TvXLStyCk8/5Aal7CQEnmqMmqLZQVOFKIYfTSM4u+nutKLlFX+AwneMHQBrB8fxqh1VEyOYytG1DhMDb6lnK"
    "wHE5wAfUoQVGD36O/3aJh9UoWCZ2ISiBkuwX7bkgiMrng0YsD2lbZfWweBOKx2zTya18C2K0qD4a31RN5xNjzf3eMkqQpGcP9keJ"
    "5etIpaxQO/6jfgb/21pYjHsINX5y9EIX8hYSK/XjVxp/EHDW7RPZJCMS3sWp95tcDt75TXIoIXyOFRU/k8FFdkEKhX1SUK7K7Z1B"
    "sFAHWvqLz0J0vsr7wxp7cm2TnwgXt0xWftQ5eUJqiqqGr+RvcaAos9wKlFV/vCDJu/JKIOasIHGA7GhM/ZZrsbw2Dg6i/TcdsasX"
    "YN4SulRx8JwBo5jLrjLpAHYshhknbitTdXaqsL/h4NamcpyFou1oVeh8AL/wmfp6WaxBxWBhtJ80baI5HNQ2jsRK8c9Pkyrol5HO"
    "FPp3ztWsFCaoMOsyh4TmhvReyi3hmcoMuVe3nHNrTbmEipmTe64q8YsnIJL3AsIJkJqyZNz6x6J51yh+HNodtKv4wyHm0WciDKIZ"
    "WhuEk2D5nNiHAp0qLnGWo84jPdtJJh6SLaGK/ZYtJt38ysL8vZ4YAdyUwICfWgIA2p5/7un3yLWTTRAiY7bZP2Fl1eUiSet/d6+y"
    "/+aBzab8Z7tXdcH4//fiz87aV3qk+LnIh0DyckfyFHjQ0c63EamvOqIz+kDI9baQEHHHAvRlt3elMiTpsBQs1ek1ZJHas6z2k+4+"
    "ds+7p1y0DQw+h/pbY/dmb6ZT9c7Ehc4zx80Yn2EIFYSW8Q/Y4rWX//ayPJAGONOypkg2Iv1y5NoFjawcreuqooDS3LdM7MWLpMwd"
    "RD4B9fsakdFAofHgREXyFoIVyJPgxDeL6+sGCzPKzGyPH/cH05EVk/QQufb2iecFU6q1UIWe22tkpaBJhMQd1eo7KmAijdUYRj97"
    "rlHkIEpuBE48ba5BMXkgtRQKztEJp/cdSxcTdPygPm2WF2ihehr4Q5ZVdTfQPE8nGtTJ3tl79aADfFDa4qxVjvXIBwZMvXK+Q9fQ"
    "VO30WM7aE4N9OvKlkfL8zeDGEh/UHAlXV2hrr4lBSnJZBqmVyQja68yofNHLYNe6OMace1KFN+vBUuYXvKC6MfyGO8OuZ+kQ3Pvy"
    "2A5xtB4Xqd2cBVGibhDrB0vfwlw3lB313Pf3FqLPNMAr5gGSURS/NeWgHFWYHnblFMLxquwSH+FT3nTPdWTaiu0w0v1rVuw3kqcU"
    "XMxn9YEvxliZXKKDE9xyLckZ0vJ4YlltoKEDsLzFuSsyLjJzqSXmAWFhvcyFnd9ct7PJG89cy9jYQLJN/M0XA/Mn/2z41VhQVflw"
    "X9YiEZfhHCbslIrBXmndXr1xjgL9hknIcrLjOGZCFPsWLC9nNIvCrG7DFQ3wyfxk2Wwv9l+qf1MDdsdU6RS3mJkIxKtqKTIAehPU"
    "9OyvE2RsqkZRfw3BwGl0C8sk0eIKL12/qPrwq+OhpU4FMqbUd6Lcr3e7Z9AU2XB+fng1Xvs0hL9EMDo5sfFQagfGOLxqyCrYXXxU"
    "/cQBgwxFSLt2pkT5BFr3Y+6TA66QAMhhO42dnzOfRvwxd4SKnrVVxMoQXQ7GN9owjk98AsNBgZ1MZ1cDQEzEnX1AHT54Dq9peyMZ"
    "ihJlsv6UzY9mOo1/uZtMjQKhF8wuMMwAz5PkxVZ0auUKfDd7R7su1GGpX1FhAodjX2u+ejl0nwrl699gGqZgNfAdR7jOYpRN28hR"
    "6POAe9XAuNox1R3E/dooojwqWMqr7W879l3dCKLq1+HArZiIh4RL7fW5uxqPhVFEh2xvayC+oqTbIAaw5C0sh4s/LPMN8fhKtGfD"
    "WlKuELsMr0kiY2ldeUC31UTVqt4x+uQ7DOQHVAhOFfRvw0TYt4QD9SpRrtuuPseg0iSXK2fvqT96w6eWXSWXLa3xPUE+R3Oxqmsz"
    "ys+OpLO6TaK7HuyX7Hj/OzYWxii/jJLZjiFnwYH4xXfQ8zS3rUMAKNLGnbH5yOOvYfoibuLtvLe3A6vhuZB1DBzfhs6HHSpYsf5U"
    "VZSq0jEpsYaKvf04sCPGkJZQyBUOYLGJ3g607gtHmDmCaQvuiZQ34KuX4+TXcJrdN8iDSJfOw8EXJ0dWQVLn63ESpxmLZc47xZJz"
    "m1f/am6gCMIJ6zZe2wnzpKv8FGMa0KHZ3s94pQQqQ3lpLI0OkJFi+suImiLJdqL/QcgPdWtYhipw4d2CBszUdluSJ7vul86DYxIw"
    "nHYoYNlCWfvxsynj+prcfUA4uht1QGDZx1ErJ+8uI8xXP90QhcZR9xDgM93oyDsLhD3u5qvh2BrSWJyw0IwDvWaz5pq/nUF5sZRQ"
    "Z+DcZBpPQKv7DoTnCVyGYjG9CSs1BJ+otgiykK3s+hadkCA3CtRFkHWcDVnm4JhGZjCTe61PpeM/l7ibUdlHHqWdBnOuMuRDYsIq"
    "Ui+xZ/x17vhtitt/kvlU2e128FTJGkxT59g2Gh5EGepadfZgYhaB1HLb84SQwJAk4a+XfAMkf7OF/UwjVe9K6BY19F2nGhDVl+bb"
    "Cb/rv6PZnUexBPABcnE1t839LIbtTbO2v3BYZpkm+2z/w+DhoaOoicN91pefFFIvs7mSbx1fiTpc03calzmHo+ip3z5GjZtcipo9"
    "I9ka3PTJXMHQQlQYGVdhu5xCh2V/ePtW+uS0HD7pKMORlCOR9OKkRWGrYRa4TMylly1WjUp0SWfATTWT4+Kp2I5+pWQOmjEQkQ1+"
    "y/mzfREQPz3dvL34dpiOeT9DdjqXCcRa/x43+EmMRXn7Ue0O0i5012juNtrtH8Yr1e5bJg4INYlUsv0rEvkF7vlVVVRa9ZFcAHl1"
    "OhfybnB1PbU2TufReTHdUAwRR3f2J/XX48Onoi4m94EPDUwTZc0e26iZnkx9rjjk6WT1WOwi65moyh1lKTCU0HCzVd+yMj+8ELan"
    "d6Omxd6mT8fX+Rp/8kzmMkEnxUhIBVV/LQY2kiQtzEgi4jkZ/gp534C/RBmhnJ7xjd3CtJyCu/arrJpPjcT0EDwHt9dJbyKIFmjT"
    "NHI2Mv09cos6DJQKBJesGlvlIpTarECFQh3fySscASTfv95v/FDk5hp7Ufv6j+sQ+FXPdA/su9YPW5iBGRC0ThYtj5R0O3ZNk54U"
    "urVf7PYT9N5JFMk/5wP+4o2EsRVAIlM/Z8pryw8ak66og3LDIgnlN/3AVrZgMQchGhxqv9NJdnGIkRjBNHlOwc/QYvEGA6kvAlED"
    "GfdOobGSACNm3U6NtM2bKMkRogePDheiAbZD4oON6SeNGf4Oj0haT018OxkFikY6SvXZosqeDdyV3kqE0XLKURbD4CVOKehLjxsj"
    "8u6/3xXt9dNaJ0ffhqihRdtGTHl3uYohgq+KR/jdyTjGIkbA/xxjG9eZq3zp+ZBDVEPQVXGV0S4FDHWjAzAbO/lETLOKDdHMfQcL"
    "qctet/ERJ9c/Vb9j8uZeRPngYDdDMgBjF7H70qRAbimVlMWOuaZyt7/2Jyf+erO5opI2Iel4taapo3YPi8GKSE1n5mBPY6gyfV8V"
    "wK9EguLPg4F3gjHxonRTd2oxZklgfzNiO1eBrNHixM2F1Ly5kBWciO+IYilC/vpndf1S5TdN0STWwLM4m8Xtz1OHk1nx8K2LWlzQ"
    "eo9QKwWmwW0Tuw2JHEi45exwOPb3uY2njL8AiuqLtKYCq6hFYhnqaHubc5qk4xTQ8LORhT4/NDmV4oe+QgHp7ZH6EClm9u1yDTvh"
    "EdpmH6yaSbk8yWPyOjOUZBzwu0Xd3PzGS882K8cEDVKf13uHp+/XSuym2pqao3DWmbQLXGJloISZYDnl2qBBuQltgEfND8is3Xo0"
    "xtTaw9h3n4E6ssD4XmzWzXXXEp65XgRF0nk51jp5G0DCGYTu89pFCQapjcaeBe05tuB6XuJIMfVfA7sd020nWs3BndeqJosCuGim"
    "zLVEnmiqL6xX8BFrzwm1EE/oM1L9B+GkhyKLrPZng/6qFeD3jC6o/kcY5Kf8LJdzhk+hjY696rJ81zzeQgsv2zDSCTYnNQYnHTuC"
    "z/HevxFZp/3LIEX1hjgcKV3OlK/c36UKEbaj70epNQbbchrOLVxkvFVT+AWXhtctfKs2JXDcsoglTvDenUoYkoUywo6+S+Go5zcq"
    "LuRTQ9ngd3LnccN71eodU+BOl+JmdVlfeU5TXeuZreG8qUlZ9qdp8Jc3Z1LetpKbunEmlYu7udeBU4k4vgNSOCYiq7zPUmXMWhyg"
    "ECYQmPxqmnmq04MXO8bX+E/Qo/T8LE3DqK0FKn7qjFydTfK+hFd6QyiTK/r1zYX+VWkJPymwuJbI2KPoEKdM0zAl41Y5jkdGawAj"
    "W071TPZO6PJQgX+kqzLBGNDZwZ4QPwCJGytU0f21XTLuvuk43Sfm9L6vYfoU31hIE9GZBwCeidHgmlsNq6McVaZovpn93RSJJ60w"
    "vJbg65nYZE+I45F4I43I0dks8RbIOBqIgAmt9WRP0kBaCbkao/st6uQKE4qq0Y+fguBGrsXhi+f4stWPCokiIFLYr6ny6IezW1wn"
    "JAbgqyFYBLtoInrIMTaZw6rMpzM55zBqF6+SJycVVX6HL5YXnFfBnW+inOsrKC94i720zRQ6uROpSNaqSQmmqhERCkeZBCnzr3BF"
    "pOjBwau/k9+UQOgO+AfBo0eINmokP64gWOkFVKtjywk88kMaAYT58uXvGLn4l7+gu6PFe1l6hVUEbDYDK7TDa5NqHMXo1wXI5xx5"
    "+k0SyZ6TarUDBUXjgwldJE1d5siKeXH8MF0VrNXgDFc/WqSAjXtifm6qt4i0PMyNA4RiHvUFEjdZHjbqb990U9h1jOgbFyyPA7VV"
    "z5GS9QugtG2ww3HdGzf5xewRzgfqM5DgsQR7rWJJeSJOiJZPJQYCcnpRH3RHFJLHkQDs0rSzCf8du4sZpKgegcdrPlPAV9ibOTkz"
    "FTD+vHHuxjxlD13ELozWmwry83v+axqw/FB7raq6COEQxwFIT8rH/j+96O2vyDCso5//0t5l7/vorxd9HB3JS4S5sCkOxrCG8fPX"
    "jaAhS8W6vDZvtAovcrIZADC1NLtGxGmdT1WDMQjucPAah+EWO3HwAIgqbL95MlRLQyeTPTJKkL8DiHrnc3yzUs17tuM0ODiNYDyn"
    "V462LgsAJT2V9mnHYpuTH8K9cuh9uyxMicHsMRsbmqvVQW2jKnzVy3A9AG3L7uTznTJQc2/AuW6NTLgrWH1bUWGNo22TgoK/yqPr"
    "Yq5x4JVX31XPzDTo/w74ZoRZFlmIvh3PwfE2nOzsBuXI3NkpkQEyYAc35Kwv/ik/ouR0ZMyh7ZRovcyAtF4Zjd/86CWJtj6CBtOW"
    "+gfirjGhcX6h1gMML2X1id3g16mJPJGDOppPV1wfdqZCfZlCdhuFv6UAMwLC0MXittYU6li0ubmLw6g41YWNVX2mR9E95Z6yuSEI"
    "ip5KBSgpZHPggjfAGsfaNFEVtuykAqZkE8gM5mAo7hOjOHOhWeHppiXq6DWqPmC8Iz+7blJ9/ceChCwhIKxG0OpAN/rM5bEakG+k"
    "O+uzWRmkOJI3wXl/7Tn74flhhjEM2/v9nPSIWlug9xtpqRCLHiwMsvVLKjCxdsvxwkx9jLe/fLHl28F3Lx7+DIvmVtuQXLwh1UXy"
    "hP2uE0hW0UKKCP1P18iFIh8t/aWp4s5RDPtgbjxnLu88rn+zrfQx5ZQ24gmyGxrnxBjAX3qnKKgGh+khgQ5UPu2aszMY/rzfjrVg"
    "ZG8pjq/ZErlX/Ln9S6dB4PtDXNCtDcFGaBuAi9JXVJvd8fnDygQwULT0scIDvHMFnR7mIjAGFjuiGdxmALFFh/HfNCrIXWu+mpKI"
    "/roWbm80ge1m8fexM5PsDGUOYGNOlWQXmZIAyKFxCOJYf17twFOKnYfSOqFN3sNmUFtPfFqe2Q+SJw1vROVu57+4wiZRIUiRcB6N"
    "56wmnUtULueP0mpnkOSMy81XDP8mZY8A+Ck+Wxr1qaBigvRdmIDYxDAT2tdfFpUGvmJUs74rfFz3zAk7GDEJ+oDuWtFXi8VgIMSf"
    "dnS+b53vzYJEjkTEReynt2F2WxrQ4zG7yIsaZ1jccbAJ+XCx8ako++EdoBvci7XueOhxWo8Ch59J4xnQ7esjMUA4T8wCSseSbx8F"
    "4w6e7LCLUQ2DkAfEvXgHUUnROptQVyWX+2i14HUN6Its/YS2K1IMjQ0TXG6IKHjKaCTe56YJiZphOMo3jtDJz45BYLGA89fTGKU4"
    "2vYDi/cQnOXrulQzMHhrwQvYg+dQPF8knH4shsF2TZpRyAjZwSnd8WJa0H159qy3natLScyq1wC4VTi3qE6d7c6n03BQlTyAzAmV"
    "Utz72mWUs6i4mAePBpniW7Z+pNUqU35srFgzL1jXiWLNeQeghMyCLzqP+1i9+6VAQbB1sxWuQXJIBfxjmuLLDBo1oGf7Ug7zm7I7"
    "PfTeog+ocQLXQfBr+wp25a39UYA3ZeL2sR5ats6A6uxwhJ9cyAZP1uXgAjMlnQt1Xxo7fwvmJW1eoc5/vUSbGrZOudQ+/KqsLlY/"
    "UO9/99mkAZiWDzApGzPt4TupeacaYnrPx3eArGx/w4XiFnRc9oN5jtU/0w4eX291x2tF7Fs3GM/GWbiZGXVyNpaHpSaVb9W+EPn4"
    "SS4/a9eYnpAO/8AGQsnp9zcj+eogdvhrPJudoN6OQID5Hhnl6GIUJjCW6rAIguASuKQKPuEn/85UoX+QV3sExhGMfCAIT/TzI3u0"
    "eOPSSoQr+EFmo5nXEDCaBfDsnSI1ZGvHPjpad3dBtdMzSP0hiW/Iy/h+mrr4oPRL3GXQb2Xwdv01MObMb7kIMtu5+CQGzuCdcApo"
    "Kiw2WWLeUZ7cmV3+1owt+PgYN27CEOgPy7Hz92CcUjS0HYGcb/Za+A1A5Zy8tD7T9seKKL4XRrsZg2H41MpKVvroY9SF/h2epoJH"
    "DYJNyX8+wtoZm1xyp3VHkopWZ3+lrDtfmz1Tlt3OGHv9RIbOLTTIPs9bYeP03pfTOEdF5fA1+Pmc5xa/kEnlkKaUo4XO4YPm3dwG"
    "HHqBE/jPBZTw3yygfE7xP1pAsSnubwHly/jqNk75uNXIiiA5SuYXYu//vWhSrsiEwKVCYWlCkZL9K8hxp8WL8RP+oA8Q8a1OhvWB"
    "myqakMPXVAVqfIwdGLgl4qvQMWp8IEfkSCyfY+19jwF+sDug6Pvd4mIbsIzGbd8LEhB2jwo3jtkjZ+n7plFNp8P4MFwn+DdChYLJ"
    "9WX7ImNWB1+eKXLN8fIF4yL20gDa9UZqgFrKpkzBzr+t4BzyqLXl0VBczD92yEP4S3o5/YRhRr7IOOH5r3vkbeYh3jVNuNLQZnSo"
    "4PZ1XIAtQFcvdV9Dv9P3B88G/LcykV6hdz7reiJjS7/EHQ71z2OmHY0pEF+acBQrXlN/kHsu+RFiBbmciFiDGaTL01yJjstgNgh1"
    "5xq4Gfm6XiizMi5xYryei6lnOrW+02LAzYYnWi/9EV7BGp8wH/BvLewTvh9ugXEsvncYH3Z1lwyQlPZd/V33QHfeu+6wZblgg8DT"
    "MZGrsl3ImJeO0iVSdOmPFOdx+WeLB5PhId03ISS3KkbaXg8fa2KjAzVCl+yCI81reAlTBWfH/FrQEus/eho1WIf9gmW4+hccbHR2"
    "oPvSJ+yaLy4GR8RcffXgtUj2HyymYcjKPdexr2AODhu8nhN26uGGdaie+WbezX4Nd161tNkWxzcGEgvobDJ0wo/pOWriaJ0q1/RY"
    "uuDysIaxgWm8czwg5hUfEg6cKNuPFmD3JPKiKWuVpUid4/o3w1/zGZlKKrve0z8wFeLbuG5M5sS8WPaQomEw9Ku4hgOyb9OpLihm"
    "dIAsb4boFzB6di9D7/0qa+jHWNweC/IK2RFALx8OuSwgVZpuD8qjIwMfQLGYtdum9TikulC/vOLjKHt1m4n+lsQNiyMS8SHrFOt9"
    "esmYfI4dtb71g34NL6QvDynwdVLfSTccHhIxFC5U2fxJj+/GbMYRwJQN3389mX5gxbdsTEjiuJ1+ih5lKabD+fQwzAoMpwfFN9ly"
    "GETZY6HRRT7KyYPVG37KOP6oPxgfUD340FDYexqxXKmc1wpQvTmg8yC9hdz/7BwSG4VheMb9f3YOxZ7ndN9OaEOmZ/5n51BbeBIU"
    "ghAMMCTTnGr4MVCqkSGSZA6PoXmbThgcbQeqWQpkR7/4tuBe7tKzI7VKrJT932/5REkQ8XoSUIgqJ7T4Pj0BadL6mZt605CeITqf"
    "KxwEIrHKrukEtV38es8wrWjn/APi6W0yQmz+NiLnWX+EEVo2z+avbyIY1wwvbETzLVUgKo8gwLLefwiQ6H5eOuE0Y6RY/RY8N1fI"
    "va7nj+Ao9fB0CwuxoWwQ+z5tkU/gKO5JT7TGLJigeVDw9G0dNFugphTKZ6Prk8D/zINdAu5VBh7KZucuZn2p1brN6G5w4uV3K7MT"
    "CwRNpZqxw7UdAqkVBskduWyV5DM7NH7A1+eVgtRpF5K5ENwdG61Rhr9juXurmugNpJKmVHeqwdikpA5y//5gNl8H81fQo1N8jHY9"
    "jS1Vvl/ZupUJvHTU8jzBRmlSlnIWVO2gSYKQSQisjlcdSwPpaI8AA2cN15Dm0FFX+gTc2pxjo12JdZQJvuEkcNRfxa0WEGgM6VBs"
    "u0+51cnJzjcZl+b4tq6hmotc+qf4E8skWVoruaJbrxWXlzM/8+2XY++8KR21Ekta0mshcLLv4Mct9ybXPJh+CoGy/AHEuF4+8aZa"
    "HLZI/MpeFWyIEtUL4nNWTVcePL3AIwslYZQortkF44A3EBtPLoweOQgU50CQpgL7LZo4zD9fC5H/jUjOyX/YI8v57x5ZSvqP10LC"
    "Tzbu+b/2yELI3E2eQLJDJMyh13oisTATn7KBKZcJJA/Xc5PhmESRfijfnJZOfQAZxqQn5yHzW9WlrV4tcpMgd2/g7WTIUpUJIA3D"
    "QI+9P45v/XBMc8taGqXvkvlrNHn47YPTkTX9eBm2byNcCRolzNiubfcDk5x7njVI2wSfAgAWaZXymaIdJDKSGODNJyCGYmLpkKcO"
    "+8Kwv5kUQKNk7AJadMiVVVX62dCQHR/nIUAFma60uWRfspI0jX4OnKL9h/T2akVs5iFOglo4R+DNfI9lDS+m8JrjXa9ITnZEotfU"
    "vngojIAzAo/HrcJKoQg6bfPnid0oPFAuCCcz3IU5SZnYwqQfinjgO9Bi/ihbgIXLRQ2PcqeMyNbm7gv6l9T0M3/S+QXdSCLXw1XF"
    "JNtcJ/jbo+fRx3fmIZv4TJ6x5Ddelvd10pAz5QtTADcYk/61z1aV/dik1uF02ugJtmfZEIZRATnK/qBWYK1CJhZyjC/UhHzJLzUr"
    "o53F8e1YKcm+RTbVarbtyxksLynk8c9iTkIhU8iREwuDprRY2euj6j777Zz3nk0yS3goVEzVtGfbsHZJxbPl81bn0o59nrcDj79c"
    "vAuDLAlc1ods4HZeBwi7SIiyfsdRikJ5djcIWV0goDGpd1ScGfcjnfyabp816uKDyQsSvEXavyEVbnV4eSHL0DYsWqd0N9sm3J7R"
    "vJXxPFAAqUZv/XXTM37MhKtRS3hr6y1awHgOwoN+9HLhreCiFrMA7YaneOoYv8S43nuXts2EJLvK6p0uzdpFZB9nsILWXaKVC4lv"
    "NnnboPxSFBXxfsa01p0F73jM5uX3TjZF8+8k+8BO+LCH+XdgTKozlyAxK7fteUCyG0cRK4w3kxE2EIikOOfK9LZCS7Q9DW96oPp5"
    "jjKcGOPV9M/+YUCufkbXdAADx4vNaxbD+zlKm1SfJF9VCz+Q7iCbt8znH5o109RdNJdeDIDI9AaMCAdvPVbd+eHx9wF8Sidis7f2"
    "2a19E4Nrr5yHtplloU+y3Z3615Jvu8cPFkQIBqT5lPYciozQ/gqW6vReesbBnhXLfAkjM7+wfDKiZ6/mXeGRbTPbCHmCWBDBJQNG"
    "nfPl+JGv2/kK2PpYquBW3eE6F3jXlgKTXwmHBqH/vn/0GjPdllDjzJZL/HQ/hIIwnFvqzvl4UF+YmIAUuvo7+D0UXdiu2uBkT8fh"
    "oBjaM0L8hS2yiDZ7kN08Q0eRcW3u68yYS7lo5NMtFQ53gwUgzSMQEDcy3UuzKO0yMh4vpD+m85oq92MiLOLaCW94KkWe+7zJ4hTc"
    "gb+J2hi/t8y+RhTbmt4klG/41iEfHwGLbssMi1286Oz5/mrTmoO2AcIqHh5Gc/pa0ehggKvhDIZkmEn9GGpTGy5MBcj3xHoFlrHF"
    "eRNmy0lWTpmgnR+qJbSXG4yA+BiWkjp3gqHroZ7t4b3A6JiOOl7z+nvSDFXqyZdhIw7l8kK4y4eCa908/8dZ7xUXBjh4vPJe1DJL"
    "lML5bwLeiy2eAXw1FC3SgTK389yjAytJNjaLbDbm5LNvBHLm9EdxmfCQI1yaI2mwCL+seUz3KN7wOOch8vilKTB6bBamfIOKA3aB"
    "ipfDswGkW/MTySwACn+NvlBY9E/IiZuXu8VBfNq0kmNClLsu5XRJOpWt/wxDDC4Vdzn7UE9saapJyLCQLv0WfBgbCsIRhSHTRpwd"
    "f04Lw/PuwKIjoqn3H0jwAb07umC3/aVo1aP+aIuxJbyovjJ4qTyDg7dCsCb3u3zfa4D81aiPpQNTHq2otz8d3Qnf21GDr+3E+xOy"
    "QlFz7pTE1IH0BM9Cfoe4TgILMs6Yt14oZfDZqitWQ16MRzPHeNRzBkpLJXuA+Va6adlxKirULnHGD1pTS4F3+hA41OSZXLS58DyF"
    "PC+PlYZRKqfX3ZJwI6MTPA48wv07d6pE9rzahcuuHc7rXmnBaloI+gwtFJUf4y5/e0Y6krK5UlxQDaucr2JYkKz6Sl2YF3dksM25"
    "kNDymS+Mn328kJkm8jniGU1dhHYlQhOHOMZjnSNk9LzWy8Z40wB8LZAAdewnuRxdrJmMj9JmTTuWxnEEm2Ocrw05lLDujb9zzlNB"
    "0+8U+TSRRNnL96GqRTD6ZEu1KDs3pbpFpIjZjhVwCiYU6TnDa0X7MYiIMMkMqhcTTqzJycqjgsBkgjFm3KU0cT1aiu1gGQ+Gc13T"
    "ULOKSrDtDBd/yLI5j9qDH+wrjnq4GbAlFcM7Is62a1TTsLmXdWmDYPNZBD5U3HPJn/TltouKJMtAuEdphYGeHsXkXkNULWMdkDxu"
    "fB42YPxv6ZgdzCw8F8A/IBzH/uVk9/rkqNsK6pcivrqYNa2OkkY3/rLp3hurZcnunKTClTiZ/8HCGLGSDfKy/XvT/TtUshDrY0tO"
    "esvwnWhLm5PgjyN3QEEYU4DDr8kw3+g7s0+tu5QJYlmghDvR2Nf6BofsQusngtHbeRQ6e2v5reOnc91CoFjjuEno0cgPeA372eSp"
    "vTWbNxnrQdHHqTu1CC0dmDSPW9bOHn9RJUy8xdJMzbm+VeAjjt+MoqHwH1H+63iHnDt35MVp3NPExdSjY4U94WokaL4f1r6hl/s9"
    "4YXiKLN/B2IvlPu5qN0JmyJrjq0kTMXr8/g5sSJmMHicuY+8fqTfnZ+gXw/dyxQ2e2eckVWJJ9w9Jnid+HcSaMpmMBCmY2J5OgWJ"
    "3yJkvA5PmQiSVmz3jbl9tYUU7D6JGVZDJcwoxK/fnqySEfDjdr+ItLrK1XjyyhqWc60fI1zvBYyX9NRrJEa7wxrWJRoOKXt5hyNJ"
    "y5boIil2x/LNz9ucoDNy8YzWqEd97bdO1KBik+k6zbjVP1lmRkGYsh38jYoUbJCQSA3OGtyHzQTAZc9u9OMKHKxcyOUAJ94BZjzP"
    "MrB/dAXWKJK09YUGSlMap8OBSUkwGUXtpTbxBV2uRSFWjtfxm6zwHjgVtv86lO1Ctqjf5A22DSivmbdm9LQM5hPh4TvWzqlUsie+"
    "B1f24RiBTnkH7l18gUxjvyJNtK1wSUV2aOfMgY+B7MyWxdKSmplwe11F8NwA+D95T3NMJEg3QQJWIYOuG2iBrnhjW07aOvzmRfV2"
    "F1xPCXldOzzwGcrOwj+Xrm5jYao8KwpYa0kGc5UuysvKKN1o51yBZHSBw0uFxFVfU/JnxO+edE1s27SUb+a01p/LFPsb5E1/VI1S"
    "rXtxl+66oJc4gYjY1k+/fC1SVnxGUFMiFhXhfsWyCxYpUzC4dTT62Dt7mwOubOtdZRuIYM66xx7xFLi71mbV+rv3wU9JRpHzKNoE"
    "DYjy1t74DSwFCOnJHZs8YW9NCpq9/cYqNHyzFAVD51CAX2IqGb8EYnODwMedfEhlN4gwl6+gvBFRZ9GT5nxVrCj7eWVz3FCT1cJL"
    "vLBXuF2i9TWaLank6bUFKf7JhprvhXAV97AD5wa0JeW+t1KvoUUaGwmYe73pKoXPWYF40sfTD3paxhhou8ZTnqq+u5S4fM2U/Wgl"
    "AtcpaE1dsBkkOKZ+IXruyXCFNkmPsM8yCOqymBJRtV9TRZQ2H58s4iMP7SC5zmcSmREWIws/sXlzlgziE4mR1PrFDJi0T7lA8XVJ"
    "JWNy2Bjy5rLcJ86Hk764tqGNjhmytPoNHHMyVcF3W11qmzL6L/bebbl1HUkUfO+vkFetcktlWhZ1l1Z5q2z5frflu8NtUhIl0ZZI"
    "maQsyba+YN7Pb5yIExMx8zBxHuZT+ksmMwGQIEVf9q6qPmc6elf3sohLIpFIJDITCaBlbK1cNrb0YTtjtZaudnMbufPb6ye9bZ9u"
    "OXvH7ZdmHgSVurW/e6Nvb10sXXcs0202N3vtotfJXux0y7trp0+ly6O9teeVxorTu1p5vO0+Xl3lbjultR1v57Ci10vl/Xp2v9nd"
    "uFzxiqZ9XbCn63Z2yZ2se4f7T2ulUqmc6R9undWf9/svJ9f9wdXjy2Omcmibj/lJzjDOj9VbHVS219L4pnPYvlwZ16dHZ4/NcnfF"
    "3X+8Kp9eW73n4uHOvpU98Zp5s398/GQclsAcLbRu3ULXcMY3w6eyt3Ny8Fgpe1N90lRP8sbKhtnO3Vw/9Yxe5mDn5OW14A4e98qH"
    "lUp7sz228r2bTrmvlo6u9GHduW4/rfWfl15vXiqvzlO32y48uvbLbbncNG9fRqPu4HgdpNFJf7RyeOHutVvD0/V+dpAdTQc709bl"
    "jtU/LnXqS6Xi8fnW836rPRyPM64x3GicbOZPdq/7ZXPa36pbprG+n8m9lk5Whhvt8nXB7TW2nPxrYcnTvdvRlrHVbC4dbBvTxqS4"
    "s5O7XjrYemr3T7rlwvX6un6rPj52MoDM0nBLrZTyuKPneVb/8unpoFJ4tVaemsN6JbuiV0bZ/uvrxVN7K69v9zvN3eGxN9ILV8/X"
    "I8N+uR6DWbv/UjaO8TXGyUB1jNv1wcHS9PZCPbh+Mc5K2e7rKLOvrpwcZzqHub3Hw2fPXNq5OjoeWoPt88PJSsnoP75MdreebztT"
    "e6eQh7VPHYKaMt6Yep47Lb6+enqp1LQOJubLceZ2p9Ip3T5R9MARbg5snB6sRaMHbugl+wPrxCn6j8Pc7K7tAHOZ+dJjtvx6dXp7"
    "fnBVmXa6Z1euetwyd1e2OxuT8t6oUbCL9anVL9RznenKZXHj7GR36VbvDpvntwWYOp166fmoc3vac3qVy2LlfH86uuleOPpoXNi+"
    "GRqlrd7oZv+sPe7nrKXC8bR9tT0+fFkrrZjlwn77aFCw+pOz6/XC5bXueINra8+xTw7qvUr+4EJ92T7f7eYunNz581KjtX+9sn9Z"
    "P94fX+dejYpX8CbPgNRRf1jaXW9W1jJ7L+5tpu68rqgvk7VyrtSflE52HnePTkenl61saZCbHDb33cpFd+m6cZ657a+Vixc3Byen"
    "7cdmyS5c2e713qC7vrm53bSaE8/MGzBNzu1m08ptn17vF/OX55OWfnm1tJfJt/TD9uh6Xd+/2Fl7moI6eOVsH22MV9rd8/HT6Ny5"
    "PXnc6gARsvmdzZu8dTXIXDyPu5NxZeDsDyr100HeOLgc75bW84/W1lK5UT/bvjhpVlrDxvH+oZGt5Ma747NS+fjkamXl2T45PtzT"
    "r9cvL0HWHx2fF2x9q334eNpdOymdTZ72yttro7XOWqXpla8Hub2Vk/Lhwf7ryUWleVi/Or88eL08rzQz/aXibTe7Vnw5L3eblc3n"
    "/NHAq19kl9oXdfX8UjVXhnrvNbOznzGt3OCycoQXUeb6KzeXz/tb5nQy3W3vn67sZtut8mnlpLQ92Lk+2F8Cc+N0WlkZmR13cNXM"
    "FCd2cXwy6D32G9nrSdcwniedg2xvP/uydTJ+fekfj65XrryLK7W1cdOq98u5G6s8zVTU9Zf943pu72brFCYS8Nrm2sprc9IfqNtn"
    "3ZvK43Gn4q6BtIR1Za28v3Jy0Lvqne85l3nv7MBUj6+ya+VWc/2ldWrvbl2DzbB5vH7cAmHsnemX+6fGtL7hdm9GTqO39rqxmxlY"
    "k8n+y165n9vp6C9rB4eW2d7p9VaeNk4yxk3ufLK01Fm5vADVfK91dnCzXt/bfMpeGJddx3MGl9dPh7m2a7Yuy5snA/v50XztDkuD"
    "rLp9MNkv73QKu63H3V3r/ApE1mi3BEbuuPB6W+5c1G8qrl0Z3+5b+unZY+bpNjNqHO5vnW5f7o22C1c3w2dzd+38qbljPD3rr9nJ"
    "a+nC3T7udHcc9WojnzlXQXR2Sj13cLJ02S2pV8fP6pJtrXXqr9P18eHNwe7N6ej54GQz83wwPhw87e4UG+Ptzm1GvTLznn2xPtq/"
    "3Jo+jfa7u6Bw710bzrXpHV/Vretx5njvddrbPTo/8Pad1vFGz6yMweQqgmBZaRysmDvtkv64d7lijr2D08Ga7Q3XWoPJmYMKyXNx"
    "ZafQOG4OtkFpXmkcdwf7IM23O5Xe1uu0dGisX106J0dr+eM9FYinDw71l5tOa+l4+7FrPxUBMcd1VgZWNjM82yiaLyfl3GDzNmOt"
    "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"
    "/Li/P2d/btmf64WlXFHj113OWT330VzykgSRVUrCUjyLfG9UmobTMsXCOB/7JREVvfKnl9NSGI38CEueQwYv4VB5DzlEibnIj5nr"
    "+yvv2i95pZNMdI1Tyy6xKIzoA18CiZBzb/48Ght3s5Y6xxee99+xotyx/92ykoRsxXC//eJRcgeldvHADa8CXGaflY3EgTY7fS2F"
    "X5lSHWDs7v09/XznA0ErvNAH1Zl5v+C+R6Hg43+3Br33wf1Le5rAr859rXUPyjz83B97kxm64qMWHj1msf1gNfDxyGjtEic0qQou"
    "GCa/cuc4ghxet8jw4P7eP3H/9jeR6vJkgTsN+rSnG9ETyw9i+ouP3BWcK+U5yHf4MJb1mjwVdvI2xSeUX09EDI9pvwo8nzUMszf9"
    "Knky3d21o5Ppad+Hf8RMRcoL3IUev0APRBBfX5LzUBETrek6V+QWgf2+DvzF8/Cm51ZL1VKtWcI0MpJz6VGQczMZT4GHXSXJrPf4"
    "8WKxqCwalTC6fFyvVquPsXHmfjRA3y6w5rhxAvKdGWx++KiGDuWiOTogdvFWKBzBMt8egsSYSwWl53UbYHhRq1U6+7V6pdFp7BFY"
    "9Uq32aiVao1Ku9Wp49/G3l5L/N2X6aIcVZG1obUP9Up9H39XWrXWXj1tqVLda3WbssVqpdVsNlp7+6KpaqXeqLU7e7LBKrVXqr6g"
    "FnlzVdmQLC9aSptMmxJlS2l9aO1De79aaldqe91aA2pVW406QNyuNGq1NjZca++1Gy1IaNab9RY21+nU9zqQsNdotbtQotmsdtrw"
    "TePAv1CoTc2xtC62VJcVAA5sSbZYq9QoXXRZq9QlPPSbYbGCaOs2mu0O/G1UoS0cR6faxFLNbr3TFX/303RRTtSr44jxr5zsKs1L"
    "hWaxUeu20kr1yl61XUsbrVcAe0qn9UonbRk/EJmiWUpibYt6on3RLvu7r6SLcqJeh006/nrR3m9VOoRoymgBFJ06le7AjMH3HswT"
    "o1n4AYWbOJFIYdVOpwH5RG31ZrUrfjf3+Y89QHVJqdCGaUgbbFQ69WZjX3bYgCG3EAAODdAK/PPL626l3e5U92haa936frfSga20"
    "QdMOzQBlNWuYu9dtdzr4TRQBci5QfRWWQUfL3Kt2u2nVVr0u24XPdqNZQ3KpdpGs4bvbIYrpNKk0AtfFhj8ArEhjWKdTbbVK8F3d"
    "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"
    "kp9QBwpjXcJYPPrX/wG9SJ37"
)
# --- END GENERATED UI ---
