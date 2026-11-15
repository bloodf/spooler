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
UI_PAGE_SHA256 = "e7bd23ac822395ea42ee3c95d58bd9f4e269edc965e7a3454eaf3b3947eec4b0"
UI_PAGE_BYTES = 882026
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
    "r3vn7uadO62tzafq0xaXpYva4rJ0UVtUlql6i8qiplLT4PkepZOm62fpmqR/epceIf8m57/bvctd2uTy1fN96YpKf5+7+rQ0VH9Q"
    "oyuwgRShfxhQPNwo/2q0dWe4PDiwiPWDjjWqTnjIVVmHprLCKDLeCcUo/OP4i/Yfu/BvZ6ACEcL6IMSU+QeBThnSwtuf9NvvYDkc"
    "SIh9Cs2bIJRKtuwXwDMQ9ifN2vCJkkFdpXOrrNOJ373ABXjQL/R5G8JTmLJiPBLbm/QjieNf9C9I+5fdSbZE3qSqGzFL4pxWNrJy"
    "knwOqm/tpqgcny6ejEAyeyaHV3w2q44ENwjjYI74S7DoT8Jst2hvInLUm/lcIUd9Eekzw073+xT4EUyEOoOFbbxYzNsS0z/vJcuO"
    "YBYwChAbNgaD7U1kxfyufQGDA1PM3zo3b15cJ4EqhnaSfeR6z3xd4kgWLFRDSh4VeabrFKGUCmuVSkCuwUXBfKv7fniPJU5u3lSf"
    "8Gl4oA4bZfA6NnIAzOWQ2Ac2FkbgdCKMRIIuKm6iHq/jvcwNPpy73hsWGe6ciM0jAkYs6ZjDhrLHB3iED6yGJmF/gjG39NCiADDp"
    "q3kb7jGTfEo8sixsHB76mCzPDWNRMBUUy/7epH2kcUYEOKuN28Cr9i7eQjmN2o9D5PA0oei2j7GlgblT215X+HnGkS28DF2+DWEt"
    "CUNHgykyc/kAXR1F0fiXYOeKZzGP2t77iljitrDvW62vkGUCW1bP95Clbt9T6TVPvi/5FQ++X2Lvimdqnsw89akqT/FoVZ/iyao9"
    "6lnz5DslnnzH5clqT9DpucHIk2/fuk/bifrEO81Xuii1E6nn2yX2Ll1vYuej5M7m7Tmx8+BRlXpf8byvIl8hjzr6fX1l+jVbzMP1"
    "4kI//EeKC/3QjQv9wo2+/JyjLz9TQZd31Y/3TvTl9/9toi/vrh99+ft/sOjL39dFX/7+54m+/OzvMvryNYy+/I8RWvn5JUIrv/xH"
    "Dq38ePI3ia38cp3Yyk9+3tjKL3+R2MpPqrGVn/6MsZWfWrGVX3ljKz9cEVv5ldkGHv7ssZUf/vKxlX80gB6w2wTf9S/Q8/ZZ5LND"
    "vgun7fLq+bqvr/vZV0EQRGK9lMECCl2/3MGaCXvVdFvVdFsHnQMV0IKhWXoef9Ag0wKlFTcMr5FIsIxyqDBzv4ZC9pgIW6CaFh/s"
    "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"
    "deyHPLn/9Lp29kMYfzVsD4766XmB75vIf7qab3fBW+nChw74Ipkf3h7rNlX0dUEfIz4nf0r/FeVjIfzbjP+rhOPx36dN4J8/hn1Z"
    "+S9z+ET/x2jsnmzr//7u/ZdJn/v4qdr/QuLlpz7zo3r+p5O+sPDvLvgb5v/pZQi+w+CvFfuqT58Df1PhRJuqG7Y6/T/I3G+Vu+Xy"
    "/jdqs03VvxWdf1bdtzjuiTcfS1D/kOvepEy2Jv70CPw9xJ/G76fX8fv5d4/wt13zBHn5x0+LPO9+ftzK/2aS+Dl7bNa/+w0d9Tmr"
    "fy1qj7Rv6oY3hurpI47+tZJeEv/zeuhjwn9SH70k+52N+q/r7H/Ujpcuf7M1v6P/vj9iv6s7npP/g075vZ3x5Fn89OI7/4sc+JTH"
    "97nie/rsOdnjiu1Xqu0LM+F7SV7moe9n+bA3fyP+m3q+6uY6STbT6fsFP8f/17Hjf8UIvLLG90fi23puny+HhX/4j3+t1Jfkv7+8"
    "l0MEPz1fHP1XJPA55Rui9/1x+C8p9/sa7J8o+P99BfXmqLxW57MCPhrz8O9J9y9U9DXtv65EP+Xwz+rRjyn/0bzSl+/fCPuN5r5l"
    "vfTl7zSZN8J/6FJ+VfrbhtfXRL9th32X+nOz7LdtqPIbM+r7Zlz5z1hyXxK/0R/FGw0q0n9yhIr0d47QRvgPR+ir0t8eoa+JfnuE"
    "vkv9u0doq/jvHqE3aL8/Ql8R//rfXtZln+5k1/XwBs7e44rK8ztPT5C9TVc3HzcVPny2LrR9vt7k/vD+l3/7Vr0+NkxfPt//2+f7"
    "qNVnO9jNp7sxwx//vQm5l0yejgn85dugj4AJD/JX7IR/+1qRP2X2LRDC+3/7Uq6aZ32ePC7Hbr8fNXv01tPTQaVfFF8m2Ib5iwRF"
    "+nmC4vHaw4df//br+4dx9+FLBn8s9r0wxRdRH0MfBI+Z5cPXc80W8Vj6+/AVy354LOc5H1d0Wb+PuY8rec8rfP3Pyv390+j9/LIp"
    "87QWGOSV391/fkHsetoy3VzHcgsd4p9/eTpU+hr3elTvD/Cv7x9n7Z+Bsp5pnvL6SAD9+j7xi/43KOBfP905/X4pH2+K/kZFXjcI"
    "nkm0sQzi7iPFM6DHy727F5JnlJi3SJ6OVL1Q/fWF7Bhc43D421vk1vOBkCfyZ7KvqL68ufZbxX+k/A2iX1+WZE/BYxinPHoDTuWX"
    "z+TjCdni/b8/L1e8vtX2FPjrr79+umsuBg9Z/7f/GTyKB7O4aOKu/+GnH55xAf/t9UK3GPz5BSnQupdBXTyk6CWLDx9fN3iOepwp"
    "6x5c/JCbp5APf3kL3/sFePDXtw6NxF/l+WVxT8hF/caD4VMpf36m2cL/8Pr90FND/cjiL691+Pljge+f2vzrxy44vFy3fy39x+HP"
    "bfDA68u3ivzleWj/uI3F5m08XoOMu+H+lOBVjt7H1VjGz+gjf4DeP6MqjR9/P3BQX74fSLd/Hf725y3Jp+Lb4JO2lR9VeQVdfPep"
    "838c3n3Wm8PPA/Dhw6ccnlI9ww4+Ne0Pf/5QP9X6w9///of4FeAwfkYwfIJO/Lxv/8eHcevTHzft/teXzhtqvcvL/LGk/7d3HzGG"
    "X+ELN892U4ZPJf7pucTusxJfS+v+NGRdPf9gb0UJXfd4muh//s/PMv6hHPvhh9etux+aj+HP6CYfXiGrn8B8P8JQPgvGi5i/+2IU"
    "L8Fn/PPvwdNDFMbzH+/5jxv8+Bn949cv39Rx/+Ji+cPw2Lf9Yah/6JuHqnqsfv/0xNmPzcrXOfGP/21f/fBk0D4ogy3iheL9E73/"
    "QHH54bln+ucWZ/7WRv+Hv34lK3/78d0PZTxkdfRo+sdKep9G9hni8pWJP/XJx+F9fkX8Babyl1+3UXzurZfhevfy6AD1/if4E4D+"
    "o3OfOfxruXpmic9Dnm4sv3v/lEb1m425nj6tePjwgr2UdHW5lfTzUzjzur26EYL/249/+fmU/33/rhq2L+rvMPF3FHm3fW5Kt2w2"
    "3+o5h38H/zjE/QNE9S8v7Xk9YPepT54G9Ze3uTj+pl//8PrC0183/nsN/fAS/Np3X9T+U0n//lrSl6g88bvP+/wz+pcq//Lg2edS"
    "h//4+JjyAxroz5+eVk42bnseKuh99+cXuJ93f6r+x/CnCgDedX+t/rYJZPURmqt7QtAcltc5/tv53Qm+2UN8gC0/tnNf4Zafr6dv"
    "f4Pno/zPCM4/fzHrf/jbls2DIX7+5Wtr6+ePx/VfB+X9Y9/7jXko+s8vLYmXp8c+C9rSzg8Y3p9/+ZLyG2zhr7L68wtk0XPV959H"
    "Pb2SXr5ccPnmHa036V8wrH83+bOIbkbC0yGwt9CpX/diHxLwBCXyjGD3wBb5+fXr3eOJ1qel/GXr5df1pxcc/2cL+Y3u+6ojvoNs"
    "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"
    "S26T+Cdc7eJ/LgDc+Yr6zLOLublw5Z2tAQIJRrX2oj2YJ0oWd9l1KdZLdiJOzgU8J4ynYqS2KuOZeFlqrzcQFG9LwfBu9coUXQ/u"
    "pSDodDjePaWZdsoLmV7W1jOaj89MeuuDA1X+w3Ftb5XO4/7byuJUhfJKW2B/Q1u8tycvKexrVuzWMjAvhuWcwUWoFuTPM2BvXKb3"
    "BOEHYw/mGp3n+okUfr6h4pT5ml5k7f7xbc/ZDp+o+NLtofcvs5xM0vKUYvoXmH+a4ZzivuX84DXnLwDvsf9fn7V4YxuGr+c8df/v"
    "nfGSAX2ZEn895TlF+XbzT1fX/3sJOZvX7BUtxGtaLhb43Ynf95xeZ5D+hf2IXtLsN4E2/EzX/LQtL1DvkHZjH15yD/91Un4kJLDe"
    "m637kjx/1+O+pQP9V+g4ZfOvNBTv0/DfEIPzre0tt5HX3L5AvK/3qheH//7TX66/9y+s3wgsLR39SCX6msoT2Nef0/rf4VGcWNHr"
    "yXuvJz8D/JfP5zX39TfcVu29fT+7A2ZzDU+ea2JvTY3/YmreltK+zYj04a4kvf5qAO5G0p/Xdls6gSHGqbZ7/1L51pYpPH3p8m3L"
    "68TWl+7ipvwr/5hVwKILr5pO+WvQyr5qvdS/TV81nuvfuNdtl/q31atWLT356O+nYo+vQF9nzr53qVe95yo59YdatfxcJTf5oUou"
    "v1TJKa/XfSqFW79q83IrbIu6xj8UdbX8fFXUdQJti7ray9/Tt2QtCAjGfvaNhX/XFiemz5VdJwS/w19+UsvFtR9YnGDuXxV0nWu8"
    "/rV6rkvm5OFSO/FXlRhvwNuiB+9tWcBV54ABj/HdD903FWHv1m5cB5xL0E/e0QndT0o33oJfaziCv7/A51KOd1bXorpWov3+XgXb"
    "qQzqugPP9WKvIR/OEvOT2rHr4L8oHRPcu3NG4HyXBFTVWRYuN3r34L2Vu88t3Enwrnm1c/v9e5VUr3OIP/noxrp8LnCbym7DmVbD"
    "Xl3iNgl1+2kVONdZ+6HYLYUd5Dl/f6Kv7b+ekHMsfqnquAYn19eXw+hamvnO1cNFup8V8/Nl1KXn0zUT+P0ml7p4vn690SPnXPKf"
    "Xsci53sRDP/hwvVkW/76PveNlL26133T93K/O0T/4n73eV3CKW//RjaQ+1sQ9janPJVe3TNw71605n/3ovVvXaq+LiK9Tea9riO1"
    "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"
    "k7R+SePCHyKT31BmHoXjKQbzXF8EqGkUXU4n43ULQq5ZYFOvxluL6It/XdxWrbgeWtgakVY3+z673dS9Krmp0Dz6eRHPo/F6hMgQ"
    "p6+3hDjV+PbGOKe5o9Dbh7lhvv13csN8a7phvjDcMC1OZsrDTI7s9P4+Ogn+9jeZDk7RpWwnIV+2p/N5eOvFKf2Fju7vnWTwnl5f"
    "ur+HbhL0Zx8k1X32S6u5se4WsZIhX9N+7CYWJ985hkJg98mDO1hH5KDXF798l537opP5kyen6DJRiKyEvm1oG92PV6uSp9srFpMr"
    "YZZFwBLwkQMeYYQqpT36ja+1SdnF+69XCWvOsOhZVJElXCofIgIq7GCXsuPcJb6iEFZK+HSqFQ7xiR50iJfQnWKYlxQE8BwhGjIS"
    "5c9XXZlo4lgDCT3w6ignNgytgShyoyJOUuwnpFhYhqP9/PZuiscBbkBG/ZFpkJvO4wQAuMUpT6uMyxCWVk5Xr/6d3XuPfh/33lcP"
    "ce/97o917331L3Hv/a7s3vvLH+je+4vm3vvM6t77dot777PcvfftH+7e+/Zf696rkPDhUNvVvj6k7eCf/Oc9/3l56GjlMXX3EMac"
    "zlCM+kP5sgLyfT6zEb8nLrbWHCcS4d9wUZ7kwd0KZpGxJbm3l07iUeR03T1fUVaCyGUKL+72TBL6F3r2EXgW1nkd4ssd9PNdlAUH"
    "vBXje0HQU5++P5UcBwp+9T+cg/77+P5VNcngV/feb9836lX4CQLj1SwaV7mFx195GQY0S6oHYjzyQJHjhCb1zk7FZflBBh8pSBH8"
    "WeLOgD7v6WvZU1HQ0HGulRcg3yHNipAnf5USBD4BmSl5opqHQwSxZD7ghmH2kr9k+wnw8vlJcgoLMjmVMzWnzfpnpTuw6g2+PVwb"
    "Vl/oiwLp5HM2WQAaoDjOfR8l2heoderfGQIz7PjUxQtWQ5C18EfmdhOREqdhkSJFkvgNh6lF+g5vEjmtTrqcFEdjToiTNCfYRo1+"
    "U3vDS/JyduP03Qx6Cyf0QQS1v5KXDh+YGxe+vqOruuLXw2TM37jfvD0GKk9n8ZUKU2+P9S90k3x2WKJqAXD4kbeGu/iKQldmtBHw"
    "Q2nzspJqX8VCBmhST+n01OPJmF94TZlOKTLOTqEeFhVBsoSR4uDHEfR2wIb//eCMnx1dKa2J+egxx36jEO9DufzfYsgylmGKepTP"
    "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"
)
# --- END GENERATED UI ---
