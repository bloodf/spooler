# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.26.0"
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
PLUGIN_VERSION = "0.26.0"
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
        if not isinstance(data, list):
            raise ValueError("Spoolman sent a spool list Spooler doesn't understand")
        data = [spool for spool in data if isinstance(spool, dict)]
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


def split_auth(url: str) -> tuple[str, dict]:
    """(address without user name and password, {"Authorization": ...} for them or {}): urllib can't
    open an address that holds them, so they go as HTTP basic auth."""
    parts = urllib.parse.urlsplit(url)
    if parts.username is None:
        return url, {}
    pair = f"{urllib.parse.unquote(parts.username)}:{urllib.parse.unquote(parts.password or '')}"
    netloc = parts.netloc.rpartition("@")[2]
    return (urllib.parse.urlunsplit(parts._replace(netloc=netloc)),
            {"Authorization": "Basic " + base64.b64encode(pair.encode("utf-8")).decode("ascii")})


def _spoolman_open(base: str, path: str, method: str = "GET", body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors. Only http(s):
    urllib would also read file:// and ftp:// addresses typed or synced in as Spoolman's."""
    url, auth = split_auth(f"{base.rstrip('/')}/api/v1/{path}")
    if urllib.parse.urlsplit(url).scheme not in ("http", "https"):
        raise urllib.error.URLError("the address must start with http:// or https://")
    data = None if body is None else json.dumps(body).encode("utf-8")
    request = urllib.request.Request(url, data=data, method=method,
                                     headers={"Content-Type": "application/json", **auth})
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
        if not isinstance(data, dict):
            raise ValueError("not a JSON object")
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
        log.warning("Connection test failed: %s", error)
        return {"ok": False, "error": error}
    except ValueError:
        # Not JSON, or not an object: a web page or another service at that address. Raising here
        # would leave the page's Test Connection waiting, and every later test ignored.
        error = f"{spoolman_url} answered, but not like Spoolman does"
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
TFA_PATH = "/api/sign-in/tfa"
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
        try:
            # Private before it takes its name, and in one step: never readable by others, even briefly.
            _write_json(AUTH_FILE, {"access_token": token, "region": region, "account": account}, mode=0o600)
        except OSError as exc:
            log.warning("Could not save the Bambu sign-in: %s", exc)
            raise BambuError(f"Signed in, but Spooler could not save the sign-in to {AUTH_FILE.parent}") from None
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
            reply, cookies = _bambu_post(region, TFA_PATH,
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


def spoolman_version(fresh: bool = False) -> tuple | None:
    """The pinned (or configured) Spoolman's version as (major, minor, patch); None when it can't
    be read. Cached per address and source generation; fresh reads it again, for a write whose
    shape depends on it (Spoolman can be up- or downgraded while OrcaSlicer runs)."""
    pinned = getattr(_op, "origin", None) or current_origin()
    if pinned in _versions and not fresh:
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


def spoolman_at_least(minimum: tuple, fresh: bool = False) -> bool:
    version = spoolman_version(fresh)
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
        if spoolman_at_least(SPOOLMAN_EXTRA_MERGE, fresh=True):
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
    auth = "".join(f"{k}: {v}\r\n" for k, v in split_auth(url)[1].items())
    sock.sendall((f"GET {parts.path or '/'} HTTP/1.1\r\nHost: {parts.netloc.rpartition('@')[2]}\r\n"
                  f"{auth}Upgrade: websocket\r\nConnection: Upgrade\r\n"
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


def _link_done(pid: str, stop: threading.Event) -> None:
    """A link thread ending: drop its status unless a newer thread for the printer has taken over
    (_local_sync restarted the link with a new stop event), whose status it would hide."""
    entry = _local.get(pid)
    if entry is None or entry["stop"] is stop:
        _live["links"].pop(pid, None)


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
    _link_done(pid, stop)


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


def _moon_result(data: object) -> dict:
    """Moonraker's "result" object; {} for anything else, so callers can always .get() from it."""
    result = data.get("result") if isinstance(data, dict) else None
    return result if isinstance(result, dict) else {}


def _moon_get(base: str, path: str) -> dict:
    with urllib.request.urlopen(base + path, timeout=TIMEOUT) as resp:
        return _moon_result(json.loads(resp.read().decode("utf-8")))


def _moon_post(base: str, path: str, body: dict) -> dict:
    req = urllib.request.Request(base + path, data=json.dumps(body).encode("utf-8"), method="POST",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
        return _moon_result(json.loads(resp.read().decode("utf-8")))


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
                       ).get("status")
    status = status if isinstance(status, dict) else {}
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


def moon_set_spool(pid: object, spool_id: object, confirmed: bool = False) -> dict:
    """Set the spool Moonraker books a single-extruder printer's usage to, or clear it (None).
    Refused for the Snapmaker U1 (u1control binds its toolheads through Spoolman locations) and
    for AFC / Happy Hare lanes (they manage their own spools), checked here against the printer
    itself, not only hidden on the page. While the printer prints (or is paused) the rest of that
    print would be booked to the new spool, so it is only changed once the page confirmed that
    ({"confirm": true} in the answer asks for it)."""
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
        busy = str(doc["print"].get("gcode_state") or "").upper()
        if busy in LIVE_STATES and not confirmed:
            return {"ok": False, "confirm": True, "state": busy,
                    "text": f"{link['name']} is {'paused in' if busy == 'PAUSE' else 'running'} a print: "
                            "Moonraker would book the rest of this print to the new spool. Confirm to change it anyway."}
        # Body per https://moonraker.readthedocs.io/en/latest/external_api/integrations/#set-active-spool
        # {"spool_id": <id>} sets the active spool; {"spool_id": null} clears it and stops tracking.
        _moon_post(base, "/server/spoolman/spool_id", {"spool_id": spool_id})
        doc, heads = moon_poll(base)
    except Exception as exc:  # the page waits for an answer: any failure is one
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
            else moon_set_spool(data.get("id"), data.get("spool"), data.get("confirm") is True)
        post({"type": "moon_spool", "id": data.get("id"), "spool": data.get("spool"), **result})
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
    if urllib.parse.urlsplit(url).scheme not in ("http", "https"):
        raise ValueError("The printer's LAN credentials address isn't http")
    url +=("&" if "?" in url else "?") + urllib.parse.urlencode(params)
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
    # Slots only: no gcode_state or job keys, so live_apply never books an Anycubic print (Kobra Control
    # books it; tests/test_kobra.py NoKobraBookingTest). If Spooler ever books Anycubic prints, publish
    # "books": ["anycubic"] under "provides" in presence.json in the same change: Kobra Control then stops
    # booking in that Spoolman.
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
            path.unlink(missing_ok=True)  # O_CREAT's mode only applies to a new file
            # Created private: the key is never readable by others, even before a chmod.
            with os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600), "w", encoding="utf-8") as fh:
                fh.write(text if text.endswith("\n") else text + "\n")
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
    _link_done(pid, stop)


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


class _SameHostRedirect(urllib.request.HTTPRedirectHandler):
    """urllib copies every header onto a redirect, X-Api-Key included: follow one only on the host it
    started on."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).netloc.lower() != urllib.parse.urlsplit(req.full_url).netloc.lower():
            raise urllib.error.HTTPError(req.full_url, code, "the printer redirected to another host", headers, fp)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


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
        return urllib.request.build_opener(*handlers, _SameHostRedirect).open(req, timeout=timeout)
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
    _link_done(pid, stop)


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
SPOOL_ACTIONS = ("weigh", "use", "archive", "unarchive", "move", "add", "open", "dried", "clear_dried",
                 "comment", "remaining")
MAX_GRAMS = 100000.0
LOCATION_MAX = 64  # Spoolman's own limit
COMMENT_MAX = 1024  # Spoolman's own limit
ADD_MAX = 20  # spools added in one go (a multi-pack); more is a typo


def _action_grams(value: object, zero: bool = False) -> float | None:
    """A positive (or, with zero, not negative), finite gram count up to MAX_GRAMS, from a number or
    numeric text (a decimal comma too); else None."""
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return None
    try:
        grams = float(value.strip().replace(",", ".") if isinstance(value, str) else value)
    except ValueError:
        return None
    low_ok = grams >= 0 if zero else grams > 0
    return grams if math.isfinite(grams) and low_ok and grams <= MAX_GRAMS else None


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
    version = spoolman_version(fresh=True)
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
    if action == "remaining":
        grams = _action_grams(data.get("grams"), zero=True)
        if grams is None:
            return no(f"Enter the grams left, from 0 to {MAX_GRAMS:,.0f} g.")
        spoolman_call("PATCH", f"spool/{sid}", {"remaining_weight": round(grams, 1)})
        return {"ok": True, "text": f"Spool #{sid} now has {grams:,.1f} g left."}
    if action == "comment":
        text = data.get("comment")
        if not isinstance(text, str) or len(text.strip()) > COMMENT_MAX:
            return no(f"A note is text of at most {COMMENT_MAX} characters.")
        text = text.strip()
        spoolman_call("PATCH", f"spool/{sid}", {"comment": text or None})
        return {"ok": True, "text": f"Saved the note on spool #{sid}." if text else f"Spool #{sid} has no note now."}
    if action == "add":
        fid = _pos_int(data.get("filament"))
        if fid is None:
            return no("That spool has no filament to copy.")
        count = data.get("count", 1)
        if _pos_int(count) is None or count > ADD_MAX:
            return no(f"Add 1 to {ADD_MAX} spools at a time.")
        made: list[str] = []
        for _ in range(count):
            try:
                made.append(f"#{(spoolman_call('POST', 'spool', {'filament_id': fid}) or {}).get('id', '?')}")
            except Exception as exc:
                if not made:
                    raise
                # Each POST is its own spool: say which ones exist, so none is added twice by a retry.
                log.warning("Adding spool %d of %d failed: %s", len(made) + 1, count, exc)
                return no(f"Added spool {_join(made)}, then Spoolman refused the next one: {_spoolman_error(exc)}")
        if count == 1:
            return {"ok": True, "text": f"Added spool {made[0]} of the same filament."}
        return {"ok": True, "text": f"Added {count} spools of the same filament: {_join(made)}."}
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
                if not (math.isfinite(grams) and 0 <= grams <= 5000):
                    continue
                if grams == 0:
                    # Set to 0 g on the page: nothing was used from this slot, so nothing is sent.
                    row.update(grams=0.0, state="booked", error="")
                    usage_save(data)
                    continue
                if spool in (None, -1):
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
                if not row.get("grams"):   # 0 g: nothing was booked, nothing to add back
                    row.update(state="undone", error="")
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


def hist_here(hist: list[dict]) -> list[dict]:
    """The history of the Spoolman in Settings: spool ids are only unique inside one server. Entries
    booked before Spooler noted the Spoolman (no "origin") can't be told apart and stay in."""
    here = clean_url(get_settings().get("spoolman_url"))
    return [e for e in hist if not e.get("origin") or clean_url(e["origin"]) == here]


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
        if row["state"] != "booked" or not row.get("grams"):
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
                     "pct": entry.get("pct"), "rows": rows,
                     **({"origin": entry["origin"]} if entry.get("origin") else {})})
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
    """Grams per week each spool used over the last 4 weeks, by spool id. A history younger than
    that is divided by the weeks it covers (at least one), not by 4: 40 g in the first 3 days is
    40 g a week, not 10."""
    first = min((e.get("time") or now for e in hist), default=now)
    weeks = min(4.0, max(1.0, (now - first) / (7 * 86400)))
    rate: dict = {}
    for e in hist:
        if (e.get("time") or 0) >= now - 28 * 86400:
            for r in e["rows"]:
                rate[r["spool"]] = rate.get(r["spool"], 0) + r["grams"] / weeks
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
        hist = hist_here(hist_load())
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
        hist = [e for e in hist_here(hist_load()) if (e.get("time") or 0) >= start]
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
        hist = hist_here(hist_load())
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
        if not isinstance(data, dict):
            raise ValueError("GitHub sent an answer Spooler doesn't understand")
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

    def _post(self, data):
        """Post to the window if it is still open. Workers answer after their work is done, and the
        window may have closed meanwhile: the work (a booking, say) has still happened."""
        panel = self._panel
        try:
            if panel is not None and panel.is_open():
                panel.post(data)
        except Exception as exc:  # closed between the check and the post
            log.debug("Could not post to the closed window: %s", exc)

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
            self._post(live_message())
        elif msg_type == "printer_code":
            save_printer_code(data.get("id"), data.get("code"))
        elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
            spawn(lambda: self._post({"type": "usage", "usage": usage_action(data)}), name="spooler-usage")
        elif msg_type == "stats":
            spawn(lambda: self._post({"type": "stats", "stats": stats_data(data.get("period"))}), name="spooler-stats")
        elif msg_type == "stats_export":
            spawn(lambda: self._post({"type": "stats_export", **export_history(data.get("period"))}), name="spooler-export")
        elif msg_type == "spool_detail":
            spawn(lambda: self._post({"type": "spool_detail", "detail": spool_detail(data.get("id"))}), name="spooler-detail")
        elif msg_type == "send":
            start_send(self._post)
        elif msg_type == "sync_presets":
            start_preset_sync(self._post)
        elif msg_type == "spool_action":
            start_spool_action(data, self._post)
        elif msg_type == "moon_spool":
            start_moon_spool(data, self._post)
        elif msg_type == "tick":
            auto_send(self._post)
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
                 BAMBU_HOSTS[region] + BAMBU_PATH, TFA_HOSTS[region] + TFA_PATH]
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
UI_PAGE_SHA256 = "7d6c0f60bde030f794421589ffd5675fe7cd4b6c700c1e01c08be504f7ba40ff"
UI_PAGE_BYTES = 884293
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
    "yVRaMB/gSbO6fk63du2SfGndcXKarqwYE61bK6VdWuV5CIzVqiox0bpVUtqlVQ5R15itrJSTrVutpF5aMamPwrxYWbVKuG7lOv3y"
    "lTW1KvZSqXzqJ1Te3Q6J16Q+kHI5AZqMVrVsMrpGyyDxmi2DlMtbdjFZ1bKLyTVaBonXbBmkLLdsHRsCkuQDG6TPsiHgs3u2oa3Y"
    "WMVgk1EQqyYarOf2bZbt9Qu5dOl2u1vBTev0uNn5w8DKdSMRzlyhk5nE+RStFnCsyHl7Gk5QsjPrwP46wStN6+vFxP56Uf6MtIYS"
    "RGfIPl1iInxnJREiWE4lr62ESETKqfCdlYQ3fDkRv7WrVFS/Uqn6YCVW+7icVr3vi65npCUYVOk8ZEbt0/Q5fAmlKpPEkraUBhd+"
    "/Xelxxmv0ONQa5cqcYw8fny8VrCV4+N/oGAr1GcTweHsuBKC4vL45wtBcXlsqMvJsS8ExfHx8hAUlItDUFDXftYQFFDjLx2C4sLa"
    "q84+HR1XJD2jmlxyJQMrAv67YnrdMVpApUNRNNuoKm2yjbF2Lq1cXcnFvr8u2ZagAIo4uE/qPhaogvnVIh/AQ9vC2ezm/aVKem2f"
    "+WmmyHXqoKqq6m3zpcYXDLZQSUXGfIfHrcWFVhXts6ro/LhrJF/2jF1X9AXJP0cuTaJnmQ/zHAQRvmW0Y2l9vvCrYiZ0Gmzi6Asi"
    "psKF+JlJ6mG9ZFthVt30y+KOdRpbs4tGnmLEJ19WVgdUanTlecnD79qXv2r5Xl8sk8U56ZrCOCcmhXWdTE4Bx3honUBkZijsokzq"
    "9hBIMP74VStwMtIIXDOPyLafkjWdF7R0P63aiw1GBViZcblCiDPWaoScNnZ4yJlxMGlG4cwpDJ49HD17vKvLd2snq70qhMOfcQPt"
    "ijcyXAJWVrW6V+aBerNmVkxa1cwbNbk7SVo0TVlnCH4Nx1urVH4pmamytaTOpQ0+SeH3tJppe1mmNJlc1qiReFIwVRtTVeUf2bwb"
    "QkmBH8wKR39TSoCxH+3PNP+bq1pnXtHWdJbAMg3UuEoVavqyZGTMO6IoVtVn6NQWTyigYZlyyyiu7FqnE54WjlJDHxM3/3ixt3lz"
    "96eobqkGgQemToXgo+SQtoaYW18uascWWuOOxCc1zlPsdRc25Fh3PXgLX7YuPWvvGtUtVazI+TZaf8Igbc2EWV8ulrXmmhPma5yn"
    "2OtOGORYfwQ/f8KuUZ2i8fbIAFupwsgiCwfn4Hya1DW3RFuuzdVUSjydzONhdTRN/Fh/jp/ocPAeifoIb3XGyPQu06e6fCYl/xxG"
    "VQqoYVfreWnOV6ee9XatEk53Rd84/ed0TpVw7d5JxuXdO0UDxo0z9uB2Tl7FR3rLpmxtCq/KqTy8YYm71xlkKdV8JX1VSYioVloZ"
    "BsWPsgt4XdX8tW4wfDepZYWxsMWsQV92q7YsIbV0rdSVbZyFcV5ikbwTxelKk1MtbRXHZZfIaf0iQfVIXefKTk7OFXd2S3eJlXnt"
    "DbL6zq/Uh0+kb6aeT6ZwlSI+oZNrULn6rq5L70x1n07xqmV8Qm/XoXpWd+voX0m+9Va1jB7VbEtv5hWbdI27Zyl86eXz8qFXWdcf"
    "8RVX107bP3UDSR2fvn3cAq7dubW2jr+La2+c/4+7N12M20YWRv9/TyF5PLpkRLW7JdmWKbf7cxR74om34yWTiY6OSHVTEuMW2WFT"
    "shWpn+v+v092awFAgASXlpfkzCQTNbEWCoVCoVCoEl19xrIptbD0KLstGTHMGywY0c1Nlku1astiaTOWEHJtvbVEI6q5XmcENxpa"
    "FPDecHVQ6zdeGnrt5QbUZVHYhtV1RVAnN18ORvXlRtZpIdDQll8F1MENlkC5Xgv9t1nucKMNpjuNuOV6nZHaaPVTwHtD+qfWb0z/"
    "eu3lBtSF/m3D6kr/1MnN6d+ovtzIOtE/DW15+qcObkD/5Xot9I/mCO0oxlI3wS3X64xUKt6MTSxyQ/qn1m9M/3rt5QbUhf5tw+pK"
    "/9TJzenfqL7cyDrRPw1tefqnDm5A/+V6LfTfbkbJzTbaUTbiV9bsjNoWI0wd7huuBNHDjdeCWX/ZgXVZD/bhdV0RoqObr4lSA8uO"
    "sNO6EENcfmWITm6wNqo1W1ZHF1tfbrrF2LcR20XdzohutRU24b/hOlG93HillFtYfoBdVkvdMLuuF9XZzVdMpYnlR9pp1aihLr9u"
    "VEc3WDm2ui1rRwAyqUG/1QJEN4Ix+peNtdoadajajGBZ/IZLptJb+9L5Sw6369KpdNdhCf0lBtxy9dAK6E0uEiyVbwzs59LnMpcN"
    "/5vwsDThLnUT8VfERFXd3w7q0ur7StUbgvnZZNtZxf+/Y/zLk2t3/f9fDANlVXsrjEtqz816N4Huc4mzo4b9Lz3mpQmyq/r9LzPq"
    "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"
    "LBmCkwZEsm77KEoa+4Wa75TkC/vmwE/LTJIkumljW5WBBArPK3j10QF3rO5dVaV7GSOdlWLY4glpZkoz+GUSJKjCVrQETO72WWDb"
    "qj0oz9RCgmk5+7uZtWNQBUB9l+ToaPbAFaEFSog4e4rsqzSHU/4GTTG9gUU97PZzfXkLofUnDiZzwRm9vfLhGrhXCF8cqlSLn8mb"
    "4jy2U2CV803Mn+e+4c+uZzNO/gh5R/QeXZGa/tA9L90OxErGwAUvmX/yknorNFvxjB6kvMbLfvoq60qGwlefZ+DU3cYDyZlSwXW5"
    "07Cait2l+CQaxPIFvni1xsZMWqGi1lq3s4Mb+lqZlc0ic6N0Q244r79D9yJi6pwJb7aS4xq3JO+oMuPZLwzJ2RXKSUKArR8fNvOx"
    "5TpMVxEu1vE5B1GleVHqlnDPCQvNzDZeIsY+HqW7KIuAiT6DyQXH9zgHco76nUsuS/lmn6TZSsSXe689i+U+Uh6n0zkD6QFo2hKi"
    "fwhwZTEzoddKvdwwOa7jZLR8gLDkByUNyJcN/642U3yEkBtn4IivpCMMixkVTBGITUnTMU8sJZvGqivCzr5rrfhtkYUDxmyiaATR"
    "qnvi8FmBnIFzWNuw30AvLl7Isnwxzgj0rt/lopOVwLSZepSa1Xo7DUGT18KZt3rB7t8jdWVXla1u3OCGvKZosZcxZYKGun5ixVuE"
    "qKyXOvNY5YfEdd2aqd/48DG1uqfb/kyclcXaO4VMHLVlHK5xG92d8VdwG2TxSThQYccbx82c16CgdLc6lcjoBlWMDSqGcg5JK2ca"
    "+eth1/ON3AKRp8/VkF8AvnkOeRkZx4OwZdHV4PbC5D0DdiG+6NAK6yA1+TwwsydeYp9a6CQOQUwtJ9ediXIWmD7HFBAbIW8sA+dL"
    "GfIfYf/NWHF3od5AmmdvtNLkO/OOZcQBPqXFsCwNcEwZyMMlQjRiHlhIgR6mBLJtujAoN9/EsH0thTGVT8YmtwYOVnjdsGf3rqmG"
    "yKKbBrbfLzmXVQp++56xn8hodJOsdf+ot1ceeNFmBDwjE4d1oA2GauAbsr7sDCcB2T4P4P6UnhC80fAnlIaAjqdvSCsKQ0EzUuSk"
    "dtXCvkcla8DXm5hH7/nI9EULUnegFYt3cRXJpO31tDFZvnrDxGOcIFjhk68zBsl9/ffxwgT761AGTbPDC2ZoWqSrd2S/ROtw2o+h"
    "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"
)
# --- END GENERATED UI ---
