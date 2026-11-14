# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.25.1"
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
PLUGIN_VERSION = "0.25.1"
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
UI_PAGE_SHA256 = "fc613dcc8df5743558812c60440497be065962d87e4d472541a07b32cca9bed7"
UI_PAGE_BYTES = 880718
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
    "2hhHx0XLr2FGtV1NQaibeDQzXwX0qVXVSH0Fnzhywfyf+oGyi1+gx1WnL6ak6cZAh8GYz1vBqQ6R8ZrMT2ySglwmbob7YTRS0TPY"
    "7YVDWrznABwBB+A4qMS+GIc/nNeEx7i2NQ/yk/TsuQrYn9clRM/58IhpkpNwdToFJGBx9UXyGGl/UY06oOHSRNA1kLFH56WuPhb7"
    "n+lsP4lChHTsY7AGkn4PabBO46HH4n1xYzrAoWXjc9lnmk69KSbISZTF5OWRQ5uCaIJB5d/3+d5zh6O/HmAU9tBTxfCQJ4nsoRLk"
    "TgUPOa34TbPDyqFCRLDuFnNtbxfmuNbt6nuNuhA5EcFWN902B3yGTCP8Ot0lSobh6LhmVfSBunmzkCM0dz7o9rgd/8yTxo6A1/J8"
    "52g1GBxLhfRqD8YxTMS3uPbwbiDGZIdZakaS8ymu+iDG6zTEU/EZ/ZflkfOl3fiLMMh33HChplHdPpuA+q28G280k42w9eW2acag"
    "m/xLewtzx19nXwwo0YA+N+Bd+tvsi2QD36YbyRfyXoJo0TWtrmorNWYjCWaViPWTOGnmwbhFgddlDpoXyNE678jNcGPWmQXaKNhn"
    "w2KfbNd22MzzUdOKEKLN8U+areAph3YP3jSVy2J78LHJ/p8tPLJFhx713Arev6R7tIjMHvRlRfVbB8HW3db8dNTOCAqpez6im0BH"
    "mmsNTqLTLE2IGfeRYENYpuEIl4j7qY+7zFmYDft0dRq6NcMY4HL8FvQp1QFQ5Omoc/FxMk7yTv+kKKadL788Oztrn91qp9noy+3N"
    "zc0vIUk/YL69vRkIV4Zfp3F09iD92Olvgjyyjf/hlc7xuMMXVucBnsFCy973EeS6H1wMO/1nW1vt+3fvf9W43b4Nf27tbW23t+9u"
    "34Xnra/u3rvdgOevbn112zzfam/e2rxl0t9q39q+tQ3PX0G27YZ6vtPevvXVrXs6/Z32nVub2/ee3mvfubt5505ja/Op+rTFZemi"
    "trgsXdQWlWWq3qKyqKnUNHi+R+mk6fpZuibpn96lR8i/yfnvtu9ylza5fPV8X7qi0t/nrj4tDdWf1OgKbCBF6O8HFA83yr8abN3p"
    "zw8OLGL9qGONqhMeclXWoamsMIqMd0IxCv88/KL55zb82+qpQISwPggxZfpRoFP6tPD2R93me1gOBxJin0LzJgilks27BfAMhP1J"
    "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"
    "B25R5v7VUOX+tUWR+08DwESq5/9iqOf/5/hWf27B54PTFDDK+r1VCWj1CKsUEqppLgckuw2LSgrMUnMfaWF8PZHARn6oSwYHJIIc"
    "9g+6wWawvfDhWLX7pN/pbnfh9Jc86G12HsOp0kvWO10o8qBHf777brOzrWaxs9nbfPhdtt551NvZ/K6Ako82N79LZ3qaO2jXdc1t"
    "d7oP/UE0igs4UZoZcNCE9DHuS5G80vib0Brj4sAVPCkupjFFAUD1jEzNh2U+gWNGGQX/uOzflMhEe0EMnGI7AGGzhyaGYW8W/CYz"
    "u5TZw8xNytyaBX9H04afPrx58/LN32CPf/fT83fPfnoOv96/erkv0p59eP88Ogz+Be2IkmidN0WvzexXNpoFomIlY1IkE8gUbbkz"
    "qXmRhR5TZDb9ngUvXr55+f5HkZ9/krk5Rnd78ezlq+c/iLzjeCQz8adlBlc72lzAup9ah0Lcd+ikhj/wBAv8IRsln9/CYvTXe/oK"
    "SBSMEKXRAN1xxiM4IYc6B7Ac0b1DB37haktnkZENEz0wDsNUEGQ6UQ5/I4F8Lg0bNkPCJlZWABNTUkNK7nILEDXenwHvZ6U6QjXV"
    "JQhIYDuCuRigGGXKPRbaW9BDY0NhnssciRAMsoZawb2BWQDvSMzv29tUoia2sDyL9hQ4eFHu5QECbRi8zdneWfRB3iO3eLET4h0r"
    "sAqUNFalHp32WHVSpzw/QNU57eQz1JPD3KAGfQ9wRiOkltWtbAGSWoEORK8rGR7aAwHa4O9HPPUUQRyA0Jv5aAdQ4nwBNB79CDJ7"
    "+mCwptakpIa9xNV9CRt8h+02Kh3T2PO+nmg0xhhUerJJEiM72qStVk2Y8WSohCAmSlpbWy3o2ChwmPp+Basp4TMx8ZkjPg0p0bC1"
    "q5zY3ielDpYhB0jEKMjTTLLRIC/V6T5czjCa+CH6icUm18hi6T6CteDpCVruSV0QkfppEg3Kp73dblga2h+08DMuSwIhJhQxCH14"
    "pSQkm2iC4nqZi963HvrrVO5knMP8wulh8/FD38rXmMiulYJp9R+XB+Uhsn1zhT3t78J8yYnV62+anyf2emUrHGXmJ7THeJfPVQIW"
    "uMuAEBjydQH1STqzsUeKspkt8f8Ggg71cLgBP5luDuWUsqEANR5mM0J2cd3fSraD9Lq/m2wFH/sfSg+wNEzwhI0G77T0UPAVhyY+"
    "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"
    "b/vix8/HjRfPov42dub/Azn7AsDxaxF4BUp8EcL4FT/vkxzlr7cUPcnso/uj70PAHb4LWvimJvsekuG/BlL4JWDcR/y2pz00P0vB"
    "4wjd8hEv7HXq4RPa1lci9w0I12e4Y93yCh/2ehbvZXfWp0K/h/L2ETrtTcC3L4DTvjiN94qGtlng5XPQM//zX59Ct3r5HkzYK6LX"
    "M0jY8waj72FzfQvB9XGT8+sG51doro+b4D5O6fifpnTe6uHHrvqvuPET0sk3G+o/wzr5/BT/0ynp50PRn/C3njYe5p/h7LyC6zyf"
    "g/20j+mL40jPGb4E2Pl0yvwzSJ3XbasvN7U9ZNn/JNcfGf3T53+GuvOb+FhvIW29AYj1+5FwvouV9f8vvKgXf+U34aKeaV6w3p6e"
    "397K+TX3voz6p8MG3fLdU4oPnnlDAJ6SP/L/12z55iGCT5N5795q0seXb5f6+WbqV/SNb5juSyfxG1H76sR2/nLk4lm1v9b1xob1"
    "jxX85Wsski9PF+QvJz+++bgvYWM+/67fAtr49gNe6+/f3tz/X13/Z3tyn/bN+svz3/zlb7W8+3VYXvfR1stTqN1vEdlzoz700Yff"
    "sel8s2Bbls9780M95j89tt9u74qXd/Ab78ZPVX2WGr2ZmnzWrOanZ3DMX983W2of1k8asi62hPLrhOzLhNdWdNur9Puv/vNTbVuP"
    "ND9VY7mlTm+m3n/j64Plz+t//qj++Mvr5lerqeuC317mW4Uvs9fR08+ff3nMiH62KfaxVvFYovjzf3w2R1I9TRR9+MuPjwm8R7a/"
    "bI5EWj1uVHgH7LI/Pr/fzCjy7ucP/9f/9r8/7rvaSnhc8rGvhuKP/MaFD6il3ebCbUHBx4vmXx9e9rn/sdi00Uf1+svDc32eHf5Q"
    "xlH++Ox3T37vVsSj6EepP8b/HY7Rdx837w7v89fNu6/GuV8exz9e2v368Memyz9dCPbV8bHHgZFNHzUfNl55f/yR+VHP3m2FfZ7x"
    "gVL0Vknv3gEffvg//48fPgCPfLvs3ce+eSVPO7/s38NPhOkrafXpfVj3w+N005Nu3ZoQbc1/nH35SNA93PBnZ/8vzI/tp5ZVtflw"
    "x979/EVq9+Si/ZL+rPpD9senNecvy3q6YQ9+9/6LxD88V/CYzHpJneP41r8kv3Hc7vzjx+/+Msv/gL9s5WOzu7O9eGrn5x37RK3E"
    "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"
    "Ub5d/Obo+n8vISfzmryiZfCalrMFvjnwbc/pdQbpX1iP4CXNfhVow890zZpleYG6QdqVfXjJPfzXSXlPiGfeGq39kjy/6XFf04H+"
    "K3Q02fwLDdltGv4bYnA6tb3mNvKa22eI23qveHH47z//5fw7/8L8dc9U4+F7KtHXVDZg339N63+HR2FkBq8H77we/ATwX96fl9zX"
    "33Bb1VvrfnIHjOoSnjzXxF6bmv2LqXlbSvs2I9KF26L4+tYA3A7EP6/tNrUBhuhNbffupfKtLlN4+tbm6pbXia1v7flV+Vf6KSmA"
    "RedfNTX5a9DKvGo9179NXjWe6t/Y123n+rflq1Y1bnz026nY4yvQ15mzn23y1ddTlZzyrlYtPVXJjd9VyaXnKjn59bybUrjVqzY3"
    "Nf26qGv0rqir5ueroq4GtC7qqg9/m7tkNQgIxn51x2J/Vxcnxs+VXQ2Cr/C3X9RysfUFiwbm/lVB16nG61+r5zpnTh7OtRN/VYnx"
    "BrwuenDflgVcdA7o8Bjevft8VRF2s3bj0uFUgt54Rw26X5RuvAW/1HB4f3+Cz6UcN2ZXo7pUon29VcHWlEFdVuC5Xuw15MNJYn5R"
    "O3bp/BelY7xzd8oInM6SgKo6ycL5RO8evNdy96WGawTvklc7td/fqqR6nUP8xaUb83xd4DqVXYcztYa9uMR1Eur6ahXY10l9Ueya"
    "whbynL9v6Ku/X3bIKRY/V3VcgpPL68tmdEzVuHH0cJbuZ8X8fBh1/vL5kgn8eZVLnT8fv17pkVMu+U+PY5HTuQiGvztwbWzLX5/n"
    "vpGyV+e6b769nO/20b84332eF9/k7d/IBnJ/DcJc55Qn4qtzBvbmQWv6dw9a/9ah6usi0utk3us6UvNFI55KSV9PY1nP9LyyX57+"
    "83/9v2C7/uf/+n+e3sIdX8+QrLtdn+uqp2Oj+ixEv5nzVuoe+s2TEPWUu6r7ejf7juu+3q2+3y6HHcTd9v6sA/7iuCO9Pu54Iys3"
    "jz1+cQbx9qThRKpck5q9kPqtSR9wIhDr4O5yHrESb2Upziv1nKQAHqZ4Tk/U94pO5c5m+3c3uOz9p+ukwbkq/yptgSFo7d/I4SWq"
    "+VZTg3SBQ/Onvo/ZUXud7qDxfWa3ateBwf4Qea+yqp5paBWgKPI+OU+vc+lRc1Lys3248gmazOKHGrjWRj/bU/CtTuo03X+2N7+q"
    "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"
)
# --- END GENERATED UI ---
