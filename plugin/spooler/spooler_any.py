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
UI_PAGE_SHA256 = "214fcc52b35eb0c230a951a8c7359ee202a4d04dfa1bc59a5a5319383614c244"
UI_PAGE_BYTES = 882111
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
    "0MDmQtYSkOmgnJY046XU6NppsSBSBN/6N1rahABhJB+PLCBk3ARyppIzdTlcn5vCW22ruJaC165gr8aKZZTrSh9T6XsXB+QbMNcL"
    "Jg96vUiD0RiNrkdF807PqGjvMFZvLYlLZAF1EKgTR8zUnZCMDy1VTR9dUA+ugqQ4zl5glrO3lMhUTJx8ffL2zUBYgGIGSugLrR4H"
    "3aR3S5K9wKpkX/Bo7OfYU9n6bExwEz1cC9rYxuPz5Awk2ICY3rrQDR1edFpOV3RY0sdnNBfECVKNBMdvebPHdHKkT8cEcQQmak2k"
    "VbI0NROrc1/N3D5XTPgYJ+pbjIy+wyJmqDVOrvnU6E3l5xgZbsrpqHkrIyMcTF0BCGTjE+Z5qD1NcCiMMoFflrXUcqKJS1DPdMpn"
    "EMhFmrbVpKX9rUFdrlsivuizlo54PQVrgfdRThB8TQUOzXtFZ6886tmMEEcDtpjfJ3Odl6ulT6DV/y5fNVQZEaCScpPX5dvy3ar0"
    "FRKUNO+LJRJ6BDfv6X/0Xg+k3SziQkSaQv7w3nSKudoUpfiEbAgbumdqPY4Hy1VzxZ/GxHslUXco93SGCPvtJRA7F4nsOfcg/HC7"
    "xGAi3sNhupm5YLSyqamzQ1tU+mYJpiDJMBZy5mhMbWpJqKF+0g41HS0lHRQD0/jWlwsXYfeTMC/8mnBss1rcM4h+vzuI/UEd/f8w"
    "KNubbVCFHdF/Xce2XpWGQOsuj9CV7/Wwre/swr7X3JriKS1KorHu1kjbbrdVSdPz6JED9zRlWpbhsNbXJxgiQNFUEW+r2Syc0Kp8"
    "etjvHxwEFRxy9ntGy/jEfOrrYzLX0BnUUYx5qIeGqPGtms/XYdpORUJrECL2advtTuevq2L64HC7bdpqee+M7ewXXnnCetyvltai"
    "vBf42iflsN0FvvZ8wM3IQt7zGS+tq9IikXvrtJlUaRQ7MNz5xKKnEDr1B6FTmta7zWnXbzq5huHHthGQc70OyjRbSHAVIWzdaVuS"
    "bS1LnhEtwh7kOwgLi515bHdOCNmI81KfGm9D9GiXNWB8fw9w2XvtCZJv+RRktL+DcN9rP6GMRemUhJiED/g3Wn2nmW7+iaCMjjb1"
    "8t7zxEDQrLTHyFTTuSD98wmneTHvJM7m+WWT/lNeSn3bdnJNtzppDSaeGJnapu6PxkKbPxIS31g/PXgcO8Tu0zfpZ596XBmU/+xT"
    "u1L2+8/+SXMilCUqp+zvtKMCkSI9pYP78lLXEFZty6oFsdKp+DFBTFjxJ4+JKgreP99s/jQVMqITRjT84sgRtmbyIwO5ZkSP1fe2"
    "R1+ZB0Hp6RvAwtd6+MYgxa9x3ofY0lXocOUPtir6RuODVnVm5RODXTxysZ10wi+zMQAJhOuAsbDkX+hl/A1ooaEHnHsh5vvO9Fbl"
    "CTVntqC8RHG3S48JD9pF6C5pRiuWT6chdDjAyrqvkcmnJXg1+6IAk8Pr4V7WP2kLCLZgJLTF1BQwc2rLbbfqFc6311q9037n/ul3"
    "qLYr+Llqs0imKX2H4iltTptA379Ggt/kzwG7r+ig9Ek/mqP/4OCVfmp5UWDSdw5bvZPj5509JvgckiNUWhrqzt7UboL/rfgA5Wrk"
    "CHvtv30tSa9dte3QUQ5SLQClu+uDmlsHPwDL1m+nLQvoiSJes3BxS2TCllltOjLq6uZBgPS+YgmGY+5TLbDXDlvTBcAekea6bqg4"
    "8fuq5UPzGeOS10X5PoXodWmQCxLUbkIaCLV+8II3PmMsBKs6laN0WA/trNfcEnVgWLsOpNSFjHgz4pUIq1ANsfoGMkj1B/4SIKa1"
    "qnfbr3e6rHYT7OzWqd5qs7+U7xxNnxvAT39nwnjZ0AnTbRa/mGfCYJw1qRbLVYsjMvpSR9202Ba65/vYs8lO8DQY8UbyvfzSiuUs"
    "JH4KVGpfjj6jBiIPpEf/osGKiPhHN88PtRTqpj/UxJEMiubk5B34WVPf489pFD2ZCpzypj/Eq/J0xbbPQ7dtHw+D6SNIIHRbG3Sr"
    "A1zL4Dm0IlXCtlS1sKnDqA2A4nCzaXB/57KFcTaNUf9cDrGj7kMiasxW4dMZWyPIU9ph9jf4jHpVK4bfYH8TTneT/o1HTxB/0sCS"
    "UjGFubpIagXgwFMBQShkVtTFemBS00IZ6pSeBRpjVVCJwqXWSrvStkQ5aFYXDcQz2A3yUqseVV16YIrX/sV1/J9Df+YE2R84eRSR"
    "fNseKLiDA2pmgvqJSTc/9mgvITELkO0fdrOvzUYmDt3UKuLgFoSDbQiCArvj/QB5XDa1Va5btgTTYAww6hdNjK4/LX4GXv9FC5Hz"
    "Na0aSh353v2KfJkAlGLq82tIa1JT92YTIMrv3VgMzZW0Zh31HhVmq33D8GxxO3B0QC0A0okuRfcf4qzT7X1UIyqT05ZW3ROOlrSw"
    "O8CBracTeb4sj+NeLAB57id82cOIdBC37V9QsxZubNdsfwwpmu9hWDuWLuVLMNR5JzDaIWnTfdEIUS755L29fnhDR13va/rzxrKE"
    "fgMY5CMYZ6djfMQGS96id4Rv39BhuVuWqXzdRm9ktCD0eMNkUetm+U1wpgXPfknC1LSNE/OadpJVCbGru+hpO+cfbxq38sG0K38C"
    "OT7Lpgz93nKdVe6JqzTPrqu0Ze4fV7uzCf/OQO2bCJYj+0a0mbsatPSLBS6PiR8SwWYgW9gE7RgGKgyajrfXDhUNMDO4zEB6rJFo"
    "K4lZ9YPecdLaNLc/f2T5ScA3QsfAnKn4oJngiODvzRHrScLwLGcA40ORv6I+0fDcMXgYoOH2PuzLrW7tCWirGIIk0HzG2U1cGlxp"
    "d7jG5Zn7ALgGqKZuHauK+4GiTY18FFf1eeetCt/8NDRtILf/mvrwxomT6tbcHgzbzYZezH1Bam4hYiPXl1K4LIC6A5fCbT5KtRC1"
    "Mzpo6RdooESC7PQ4OGsnrb3xUIXKpQNV0AGghCpeA3AMmcRz2PBdPYviPbWMwoAhBTwwBjKvx3Hlrnab2EuiCrk9yFM6mjWUNMxd"
    "DjbmWMQgY4f9RQ2gjoe+rggTRz2Iwg82G7xVNGe9UQQdm/JpCsk/7mW25qK2uSlAp0RYd4uqKuawzTnI5Sszs9RD/1rhYpWOkUne"
    "6DGxdOOkyIJs121im2xagU9mkQ4qzXGlIZK0IdckZz5VRov433xHyz1OumXw2XbLG84t8Lz119+/htoXWCSNNnEBhSvhOqduELTG"
    "6heUi7M2+RoP2R/8t7W3CbqMHnIB4hIkrbRPD8PLtFXrL3UZ2qX9nbYC0mAqt2L2E2mcWpP2H7Z8NREn/MCbcNam69GItaZGowSX"
    "PupMttpA2qjqc88UL1tmitVOCSgoTE0WbkkUnc9EzEJPxnd/LgXiQZBp5wOQnPE0J/y9u9jZbXhscsZoMtJnR+epa5heYmleE7q+"
    "60zEpfseWfQ1bVhzYOT15WpB1RKrr2bFvNX1/V9KnnzKChm2737gO3WV0w/VVE5dPf7zva9fQYb44So4+y+GUk5f50374e+R+3e6"
    "gXL/oSuuyIe7Y5VT7q1CMj/4cVFO5qspwUMHoK7t5zabvufColP5obKcK0V/r4oyugdCTfpWze24PlhfUELqZKi4b5CU8cEBMsVv"
    "v7izX1DqGJlgGjqt+xKUJc2a+0+jw2YLjmxByeb2XeF3xeVV+x++4DL2s+aqmLX39JPT0dOmWuj7B4+cD47eqLzeP0TJlEG21Tvs"
    "30ZPo/1FCzNR9KSqieS5b3mDPC7ILUw/gK128rdqVco83N9dkyv9tbfIe1hMMsa7eDOg8JZtV8mETwJVpPVZe44zX9RZRYGjFgKs"
    "J2cOaKHc4nB7N3+aX57jmGdVmgevDN529EFXG9S80XH4ndWmJfjP49grp7EcEDqDCzpW+Y1oFqKPCurKVUt97Pfv04UETtfKTEey"
    "xoFru5APDGtkz9Z7lIszPbgAVs3pmAA7CDHJbi2c+Pcr2eL4zAcjHpCMROU7wxu58VkGIfcn7qKLYYnMrUrN0iqR8bROGcIqkF21"
    "RtXJ6Sr7Zb+8l5aUxW/SKlxoNUkrmmgAwMTOuqVSJgPo7+MIzN2iNfb4Z+pznpZDU13UZPPU9oDVJexgSoEyhk9DWVDHCLITp0f4"
    "mL7/G1+38l0sdPeKOsh5lZrTB66HUH4polWcrPz8jlqvTyRkr8wG7YHObFTEdTS4DDXJUZ5FTWp1wCCXoyJhP1XhKStMAisepGaY"
    "EGeFvefkmuCbR+GH/wl9+cFqdyegCKZgkha4Jq2AfYMZyLihSZxMAr3GHVQgJCid7HWXDhzK9ABDADk5DaioYFZ9s8Fv74iI3Z+J"
    "MD87PI8z/kGF/Kr8p3FS+A7cmQ5Ad2MNUZZiNjfoDa5jLcR5zStQ0QqiLVUz4F+00Jx01KZyGkj0VDQ/rjRxerfCokEtx6OhQGft"
    "Tb4gHCLYLR5Yeo3IMejhu0NlbNT0Mf9Es8WWVpPvzvS5+3QUB/zkCZPbo0jEzanTUoqHjviXezlPkRPdT5wP0L3aU6/TQmIftx/Q"
    "6TECWqvJ8c5odTrdnqI5uWLt0rTdXuqQ12Xu0Mqfxk512YmkLHe7UzOdHzs1D8PKuCBLmGyVvXq/gNE8tVpwOwVMvS6/6OTXuc8B"
    "oxnVWZH92CbPW2IE/2yTd21suObN5v5TiDXb7s8qoblmJJyiBTq17LfBHSwjzSGqSGeMLt3MuV52l9B19kSwZpUStM5N27webSka"
    "c8J+R6wedtsaTcbkAhgXwFRvNkyKj+m7MdCo1watuO0yqpygLGeGniqqkkrOjqHXHIUmXvalsEr2OLqmj7MaqVWc/MB/Kzofbwzg"
    "PaDjS5fThiDxHr2yZkVDjQgaCVwbvYdttRAcU7F90UbJtbcDR7brxHAWUuCXluUHva/ll5DQr8gjLPKriAV6NEwadoFC9Fv6xaD5"
    "KszpSSRF79BMfW6tGdrYKSInKzmVGrcwfgh2aTx6hTiWWq/B7wNxZ3xRgx6wDIflAfxpQQiYUyCj4F1HTWxFzBCaddgrUtOLWmar"
    "cJ255wunltrvl7ZdI7/w1DFOmi3rxfo2bJ022VY0Yv1DB3MW0BgrUZ/KbXVTfiNaxaEkITg7mPu2spekoI9sW/5TAqfT/wacDgNw"
    "cmrph/dOocvcqheC/W9a9YU8nbbqrU2Dro9637LNnXrGv8Fu7CKJQMXG4U0zeHdY88lroNwJ9AlDEbQLqNLBTlQi0VmsSm8lD6JZ"
    "vyMB6feJlJFy0NQe433F5ibSjJqmZfa+TdpMl8nD1l6XtgSIRGEGazHP8paXoIm6RPkqVmuhQ/nmR6yEtAK1ieuflSHCHeWb7RZJ"
    "TMIkO6MF5/N+yhKU+JyVfG05IokD4ea3oQQqnLqA5MWoDQhDIVl70WUm8Mw6GUGlb9oQsNciKFyHZ5ZZiUK2q6wIoVgWtmHP5jHP"
    "XGEQKqGJ4C2XA3tNW4DwYPqMF7NJWyyANgtAKKoS8qzwSu4Pmqi2YstOiXyvBHNDRGLQNrafbBXUSKBIHFk6PByMXXPNPQcpEcrx"
    "sORGC1nJRg71Nu181DIPMi8eBZhpaRmVCWFot3/wVsQiVi6y0p5PpUMa8lQEkprgDGAKFkyn7UeF9vO9Se2MsNoZXe4lz6Lwbcjj"
    "WjXM3URyKm6dCVSDS/RsTSg4IShkVAwTvpbfgKoJZBnqOMEAIG1XQB4nGfE5QT60h5w9lKXiaDaf+dlkloKvlZmfkJOL8GKR+NMX"
    "cySdBgTyPb9mUOzkaMkp9nMKkAIl6zIBr+CuQU6YHBDGVN9WCdKk/dBuNnyIbjZfy09kz05PestAGNILgF+SM7zXQF5WRgDTiGqz"
    "SZ30OMiQqhrifH1ZN1rbE2UOykYOytoclJRFSYmk8DC4sIzC2Vysu6Sz9LXkvtbcV7H1MawS2i/CvgYZsaHq6qz2iYbgo+G23s4j"
    "OGMnTKLbA1Y78RPsPwRUnOzAdRHXZsZSSbRPTbnAZEzObQEwW2fnBwfvNlZnchx4iY8XYO9K2d32qNOn6/KsPk9/x8yy6A21Oez5"
    "XQd7GlxqeT2RG6RPi3uI+qynk+IeWj7rJFsKPmt9Kuj2rE5C4ndlKKcChkd1VibSMnM8L1tG6gn1lOjKHizZX3WTDinpdZB0KKXe"
    "da8E/+y+Pu++/th59Sf+V3xkmVsqbS6b5DAdJ/zC4pdxYpbzSC6DqA6TfaJtQVN38MZ55sPHw6me5at5axMOgzPuh/DgNPcwyTdY"
    "LBr/i1a9bGm0wVXPT2F5W+5tSxNH0xCU+3K/3CFRSzSbND9BuW8CSZKoJYgZvbZInBVaQ0Mgo11ui4CP3Gy8ofQLUH1NcTHXobWs"
    "2ZNFcNmZ28zcWGTRgpwwF40jldXtO183vIxEv92CIESBxwRroQGXIKIGNLhX6NmfXyTZ0cXJrp2TGZ6v4es2tJjcKcw7Iyj8ywcL"
    "Ww7Il/057JrOWClOepV0lH6Ca0VXnycUiITjQz4JNX/CXoDpCIQATuK6s1T9Pn6Ckth9RhT5kKloZil/EJZS6dIlGS7T76y27Axs"
    "14asM7r3QdGyZHAOpohTPAnpuGgChFqyREWg/EtFJGgfyVW918iR7oTmS16M4kyLaJZ/FOksNSoHjWRcu9SHQWqnEpbFPOCCO4ZI"
    "UHAw6gFhdWCDTHndJQxtN1RA5rmG+PTXcvrTxiJe2PW1kVsWq+ruh6M7wyi7w5DuWTX38LLhWbBWZikGhnvgZciFSE8MJ5U+7Qh0"
    "qJVn0a5chDlm9wmb4wUChaFvzPP/mef6AaLJPkdfd3pdhdD4R+shyKKSvBQoaj4ARUxkdQ0hqC06j61Km5nHHcMIA3Khevs+4P03"
    "FhVHn8nbrnrrwdEHTC3EZkLI8k77RoDYM/1n3di09AYNHWX/DRrumCh8HkOFxpi8WCRtzBoYaxCTHgJ/10zAwr5d3C+tBYAoB3W0"
    "xAKF4r/YK8GSGHV9eWF5hAeESWnk00bd9QEdebYToACyOtUwomU7XQXraKomZoPkRigmAyjzEp6EVmWHzJiWVm3SNTgrjXYttTkV"
    "iWxpd/aqtCpFRL/Ti6gUtZCdQ4VNTHYCOmGJukpIZoWxLxYLPS3gQSgnIlovk0pV5UQnjXJGDslc5atLCLq/ri6SlQIxnMy2aSHe"
    "fCraBgZ1VCzxl9/DbIGmjuIEv7FaqEs1UtfqDuO4SMUKXXZ/dMmXXwYJUAm5WUxkk5lcNm+/g+kwiw+y6ALAf4fZ5Wvg9Okf0gn5"
    "WNk6jSh+bVvz0msRdVI6f2jTl4asuArSZtksYkNi6OlQxy5TXucym2XsyMRkJuwNir4dyb0Fa+aNAsW6X1mxThZuWg5pqRehXY00"
    "84k6uz5HU9f+QyrZbrfQpO73K7sRLmmZecYPs6OPD5NqKEPGdONEENW52xRGX+pEPFUtjPWduu33bwfW1nMS3Vq7KLUQpbCm3y9t"
    "O+WwTCPrqyborjaOaWwnT1hrEN8cpxeZeFGwglO+AJlH8zJO5qXxb4SZWlg9etqzi4FRnTe3yg7GF2I2wxrHBFybDZWJLrJWVt6w"
    "93xIHbOUPWHhxHHsJNw01349+n1aEsVzL7lnVJamcV5a8dFFv3+MiypOOztPjtX1+fCYsDQWqKQFIjKlNPfzwQppJesramum016+"
    "sOr3iYTCTuD9/lJHl/Qc2KzNGZjmVAbES0I/7KxqJtQMrYwa0VSINZMsp/TfoICFTBBP3SwGJH1q1Gh3HFhAbEffGPZ1AVlrmeWZ"
    "1pB4Jsd2upN5hr7I7TVraglKpg0tBdSJGBLTB/wrJRdIF1s51MQPQQ7gLz1RJ8GNtmA3AmF72/QERg0d/kGYgwgOHqx/h6h0VzeH"
    "8dO07V6ulN5jQ3twILL5GC0ZHMMeG+51JlPD+Yj3PFI/esTfsYuK8KMlN40Jj3XHF87CHA+EKVzhY9aU2HGe0anW59Ea3XsVKQw8"
    "hFfxnvOxpSnzqnnh/DxZB224fgib2jrPQ24Jrkp/DRNs8DrTIk5mvOfMRUZugL6Gy6AGizwNARZUHghK7pgSKwamVpo3W60VbIBp"
    "x71Ex1FTwXYOHb8ruuN3RY48dAcuV6RZ327Q45EchHQc4xzJ3WFeER1bDq7hzUz0E9e6rqv6q7yc4ixsRA3kh/KKE6YvkPkKizRd"
    "ccXJZAsDrRIX1MfwlHjbDsQZ12bDcmCH1kpjqcvyqCWISOJGx1dtu2ySjz++Xunfm0FVX37M7R/Ueqap9ER//P/Q7muLhT54uK63"
    "YzEdC83n9ISbAZ1LJJlzyQY7pZy1/GFNbJB/HBp0HcLg2dk+ixebEnf0mmiWKpbrfKNSDJsv6T4WqDEX9bTWjeJZOzpUZ/zZudzJ"
    "W1Xk7TXmvVYV5U1Cb0ql9212iDU5YkAqrN3eEMR0RVDNs2Hvuu/YDeMFW+fd8vNJya5E1DEsMW7KlBZmUTRwb0Vfw5eDOpUSgTuw"
    "0jNKp4RibpxSkKYzBs7/mLC0ijxiFqqh2eIdVgVVXJSPQKjduZmUBXpSDt2dw6Py6dOnRzTKOwjeCPhegjEBLG82uZg0FdYQOGvT"
    "+tFRUqa1Nxdw7b61Lg4CCzfn0uwl013oyZnrzMHR+bBHY/TlH8M09SkKE0tE5ayVNz0aRTkaHKFR3LApb1em3pcdrXS8rjF76U0p"
    "c/aqDJb3meso7+WTEgKIYipGjSeuqWPMHVpK3HAI7d+6XgUd2D3bGHp1CL3uMxAFQ+6vv6bz4Ib1kl1AeN+vWm29iJWySmZPlW7a"
    "2B4CCcUUKkCDVTGl3eWU1CHvQh4fTXCZWpREbfpZrYk0xg1uVh8cJRelKr25YlQG5ugKJ63LZIF+YKseXp1ZtkTcS9zakVgi6BaD"
    "PWSqG36oAjwKf1vFE/cBe9taC4K9Lc+K82GUDwpnKJTJ1W8eJz1Khh+lAmN/QuBDpWnaztM8MbZnuSF3CW1Dz8do2uj4nEi3urWk"
    "GwPqwUuAGdMwridpTfs5NBE/HOonhfP7Qd08MWuMq0+HY1Ce8EDBSGB4XD45cUM7ds7hdHpSnh2X58PATjQwDH3sTR0/JyokCi0f"
    "H29DLCPWJW/ADnqc8p0RONFo3tAIAgRosLSfTkN02sm5BY1BzaFCMZ0jWHXmdepb91KqgPbm5qUnL0txE4vdxV6V3E7PCNLAKSDP"
    "d/UVb01rRHSBKbsog41wEUwZ7YQLTFloUvt5YHC6P4l8+lOD+J8d/TM5+tTP5KcdU9zHEBLZ8fB2/Bvd6Hy/lYPAfUMnwLeMAw3K"
    "V5HL2mz8/uj3eQpk9l6bou92T4k/AxT/2p0Qr0H2U1mxqwEpNhrx+fqKkAFXFGDr35nQfV0aOrfXMnlbdsXTdSoqcUQR1YMRndpv"
    "8+jgyGrb/cm4OE9vctN7VTGMVKmWzzozKLPlyg7103yoDw7iFznB4584c5Rr48gRhtXW38mN2DUT/U7M75R/A68Cpdwe0nheQ8WK"
    "XbvuDKiqKC9mSQhxeA28tJ0Pu5u6DDc1ZvksJxKhUZO0hadIfT6EHhUQClQt07WhaZJcrcQtbZJvxd8aLPoWUG9ShhZcU5tUriib"
    "Nodkw7o8rVQ1n7IcM/FK4kTfLappMSt03RAlF99HLf9Y7iktsVo0hJQX3rXumPiCEfcz8FsZFBJ/umNHt9ExbMoPxZxtNKf8pmVX"
    "L6ai0juv5Jqct11nf2c+Gvq2XT0WibB2VKtsa86c2F6tYI1wwYkO4dkt1YSWavLEQdPEbsh5mp9NzodVNh/YKU0rSjFC3U5P+31f"
    "KDgro3naROutInJ7Z1W8Eu8cvcFJTJx0xOQmkfkrWofPidQc6Dl9XKjW0JshbfKVR8Zf5na+v8xBc18XU93QuYg346nHPbr8oXe6"
    "EHy1o8VeQ4kXPhzb8FZuT1SYfpNH1m/j+8IC0Psie1/QJjP8gm0iwd2zcefDO2uzqQcTIhmEPwlYDNz876YF1eyOyOotigmfcVlr"
    "mSTsNtyrWe1W58PVqVLCF3YL+zK5xUfjzL+AJmYs+lNpNZYAO+Prg2ZyO47VlyXLLWhWfioDnalvyh2dqT8ch+nv3/6z3HI2p+2e"
    "TER+OYd8ciVAVbA+lLibhBIcVHWXFayRZhjo9zmDxiRlN+HlxJkpfAmh0ww7aHQDNlUbLlAwmNuJvan9QLzBe7MFFnbAeYGRh+BR"
    "RCb0JJTRkkBquOKJTN19B3PTSxEMoNACtAX3j7udrQKpEVt1Enm2VE2Or/p9mL02S1020JznwfKoIGED8g4/tg7i2wzuI5mbIDS6"
    "Gnh5L9dfhi4l6ABfhO+P0WbE9MYShKDi3tAG5K5fpUbivHJc+PdA5bNsJuj5Kk6mgCfaPlfBZWnZVUI3dvrgkQtxNQ33V8ZMazwY"
    "x9kvJauTsAy2JhBODLtWQ7sxHzLA5nCDKY5JmZvHRZj14/lLbq4PmpRgraCzRD6PAw3zKurcCf9ShpoRrY0fMHBeg52QDkfA/Qce"
    "IVlx0ZfCPbI+93dVspN+7t4O/Fo6y+TRNesffW/IPei0n+q5RowG9VASeV2MI+ApiA37zL56iRCrg2KQL3AZPJgCbR24yz/58csX"
    "cw24gGNtQRtypnYyVRl+9G3eXn372mSFdjE733fKqbrejV3A9FVlJ+cSzGqb4d6DhTRJSbu8TtcIVZGM7TSMVTgp8IJOEDTRTRMa"
    "vQiZoeaCVhaTZKWWk2SqlheTZKaqZE2d1PT1Uv2x0vXdicYlYVUnCyWI/5QwbXJlXo6rBfqfXCpBuG8gRRptt+lcXacPS/Y0UC2h"
    "ljS9o74Wk+OrYj6lksndlo7kC48CaE83V/lSv6RN1j/6jGXHg4kpLUrDtu/xVt1CgymYrodlpG1TuIhqCZnrNq1rmwxpcp7Oa9b4"
    "uVJLcZFdMbK4vqTFaWG+nVXymnDGgpZoMae8smad5qhyaeywpRgUzfELdtwyIXhszbyfctsNa1nfk27tL+KYFdWw3yDdZyERtNZq"
    "ucuHne1J4G7eXrX8XAZue2OT4j3wBhNhaaRRBGIBOojDC55uOjPLyVVV28aIFLqVK7+fAzEyYdcWCkdD8dnLdK7zNKHn6RV7DqDz"
    "ydQmCUORFDOxqJZQ/sQDlMpNr4h/hrNhQtfTorx8XuPjeH3itS231zSjF5GoiaOHLXoYq9tIaME1t44hOR8DpgN2XHQMullCf1bx"
    "euV9iHWmK2y3NVBzAkfwDob4bSgnly3hMtWVS3tm+xC+qssOZI7Sy6ykjXVBv3VyZfV1GOQ2G4LApYdAyTHgRmuHzF0YvMsidlHR"
    "3VrqTo3sZqE1yHnNMYXJZLNhk2nKv3DbiWBNXceXmVkg4B3zYFIIDbG8x74YByLyEqTHSV5Hgmbm6sjfBUTtfoUx1RjpnRaR7hyC"
    "OYihncuMr598xe1okbvOFY1MSJNLAizkLGmDcw8YeK5x3wOv8NfWkfN6tSCmiDCdpCYFFRAyee1QEJFXFvkQiyRwRaRWABPJXIVL"
    "TWhUXoFK0W/cGBN5AgCY4Q4MxBj1rAuaV2Dy7odNouGAWqI5bTICYfbzUESTWPXw0ZKWksChgoOv7kHb7HKWRG7DCe6wpt2I4S9U"
    "r1fsAg0miScjr9XV3RRqxUlVB0oAeW1nzx8RNX1Ds0eI9XG8hhxXovsEk0SUcjeBsb3yiWafcGq5s3tEy1zPaS3MAjTKL9DEL9Dc"
    "zPgKMz5N0ZPHmN0pmq+k8t7PpfGEjnsBIg5oXVbYUZP9KZyHU0grQLPHQ38cD7nKZodWt+ou5oDFDLFrluJiTjiOuh8cjs3OsTpR"
    "ZjLn4fm6ouUgKttrRIjQQRBe4D1PfIvVA3BCp3fsIvdzSR0Qs42JGNvj5wEHuHggMzmOu9iu9gz7/of2k/UOrgN1P5ov8x0cSFAZ"
    "tTsLKW55t3VaRXVHO8Nom1kUPo0q1qcSnXVrprsVnqANjnWLHGg/XIWEBpZ9IRM1SRfcvc1mMZgRW98yrA/bHTojusoi6YaiT1Fh"
    "t/ObDVENC+rSipBKIwfvIpO7MjhScX3nnv/HKmAVMsEUoRTtRTvG2Jx1VwaZgVDe7anp5s5BtdMY9yMI45EHi2LOfdHaqtOiDpR8"
    "6pC2J9KrvXU3AKvW6/2w1+CMtX30nEVcplLRAAq3erG3nwGrMOoYxh2QPQIIE+HxrG3r4mJF6G8MIDy4PqhuSvgEKcFngbIzTvRk"
    "Yw3Rs86lzDzYiAHF4iFUpqwUp0e7Zzcn24nLz34tz9OKlavqKKfjBsJDwiaaDT0qnsNV7bmTuc6v9fEFrCaCVNr2ukZqoN3kVeLX"
    "RWMCUSFIUdG8pjqAMfjFXGSa97lk/Qgk0iRGKcCx3s/rKBIi2tUIt2mx+iHI8BVKnigfLuv07KXpm2IllnO1qCFxJGxlQnzlyyWM"
    "Pp4jOl1eqiU0yxr02qZUpYTHeoHhJks6Xcvg8dmMHnezjsEIzYk3kzT5HhOgJSF45O93s+79/pl0VL4Kn1HDfmZYx1ZdOYbqed7o"
    "UyJNm0KCrsnxsqihcrnCLlw386ptknZrNwykXASfM2/GEHmVTPbSAEX2fv+4jtxbxNol4mHKXvJkl3RMw3CoWV2c1lpnX0VxILzq"
    "5aGHu8oYcchaNduUbV3rgQMkK8C6IAi2dvG3/Iy6JvvZ8/SujiZEF9aQAkxYwk8b9oRojxNkzK1s0nWw36cK3ZvQ28S8hV/2fs+j"
    "FWHFfv8mLOouN2rKNS3S1yd4ZXcMiFa3ag8K8M5BV5xptB8nxDyEiByYOG6pU+ZI4Yby9+rCXeSI2pXRBfMXnYFwq1MeZlwifocr"
    "MYh9SiUyJEbZQaZQcQ/CPhFXYgS8SuabB1iUBzTG7gAzdqCd35mhOA5ZgOkaPOyKpurM2M+v2BXneUqzdraqz6XfAC55NVJw06O5"
    "VK2nu33qZpjBR/F/+m6buEeeA1p7q87pfHmEuqSXdaCUf3Z4PgyCJT0NvGNLhEpWyAhWfk2429ESVmwEJDYi9jM4zK79YbbeQZwg"
    "EQnVS7QbrjqMOENn2D2R+5SwxVIc+jXhhdBd3bkdWRtcWSjelHmALCuAYBdTNg5RTrp4cr6PJlc7WHLmkWQXRy72UeTVLoa89Ahy"
    "tIMfr+9Bj0ZaYz02MMSpW8Aih3w5cdIrwgeXovDyb/ZpdLwj12rPjs6HJyaMpog1jTcxyPQEDp6kcKIBjbwghRO20KRc70+suvBz"
    "ak0767RhLFf6I9Fo2NTp5WbTCMVreX9sFaK48MMxD4w2wNnFufFp8HvOtojeEY6eo/BQ4qEZiL7hja3lKkkKbCHJo56f0K6FXgY7"
    "X5Ne4uafGoD+S4jV63QCURXRJ6sPDmC02aDQNVGWVO5us1l1hiNmP72jYXs2JRQAKRLkUQ3wJE1+VtH0oTM0nZ19DQ8EnQTo1XIV"
    "9s6MezhNOTHUlCRuu86OeYxqeg6VZQ7giCpaf2/YgR/WzEA9mPepzLsqO3SKQ/V0qp5EM+6zWRoeHPBbSYMjGj/K+aIWWppRmV3R"
    "JuABtiEOvD0rzkXbyGA1JJgxETWIojtj4i+Ii6ehLTG0ioZWYWiTeVU6e5MiDZCAN6vaPY90eBzwVPtX1Fncj/Z1eBxknTcb4qwM"
    "Pu9g8P+8vvSdV9nVwa3vRW00mL6tQy3y9FUuekmW+xb1geDDW/thr/Pl9xCEMb6VyMDyNegd/wZrKHGzXC2WNMFl67XXXZIlIIZd"
    "gU3r5QGlcdds1GvB4NubPHPktP1PHuMSprS0mOtm6amzgLE4qd2Naiin/oyH4vq6hqtRSzWmrXNmvt91qo/mo7TzARIKAlqgTMuI"
    "d+Thjz8Pok2ay65AtxJ+vYvmK5bb0LbJyq58lchJ0X6UV4jTZEADC8amWaq8OZZo152R2HI+GxDQNC/z+RxhFj9U2OaHowqLKoEI"
    "2pMvaU+GgGCH+6oIrwGwJUvuPE9VEDOwdhYjFvufwVHI4V/pzhr1V1acbQiPiPZQBeRkI6iV8SPzxMmmSJ5UgsEq1/2MCixxZ2rX"
    "i0j6R4+YYzX+OKmLVXih0cQsPYBvV0/g8M0ybgkb25uE9lul1uhTA/UMHABEKHUFVnUosKol4pXpS3rw+J64kTe1c3C8t9Vu6uge"
    "kBVlezdee+J1Fq3f318uZ2x5U3NQN6EVXV0dij6M0NOxX2TrkyYS7kwP8LNF0F9mxxK97Rhxnnr+mnUPnG5rpPd1lAfF9Ltaz4rb"
    "zWZ8PY4fjQ/Gj3C12xCiMA9H548eJWGkzxc8eZyZnu0UfkyFUYk6VIfngb5sKF1xwRyiqEzvVX3/wkSvM9aYMOErB2GEYxHhvK3v"
    "t9B+XxtV71xVVrFYVMr1rpMIKdrvU34ZZ1B+TiCfxZdOiITV+r1mVSQ4Ws4DxPTPo8e4zTGKYDnu3d+J4vEU6XtQ5FP6fd/L+6Ct"
    "Q8mETX6aVVUUfBInOevCpFXGN6ONWhdEGxOfD1J/IbrptRqlswEtNDslz8zjepvIk7qmXAamkxbBYO/AWF8j7Pk1ly8SBHakRRwp"
    "oOtVdAeq99ZFu4ahN+cahc5Fj3dvv08P6ZLn/xlQvLqMFnE8Olucy6l5Qa8099c2IXADX6KkM0i6jRaEK9/HbDVkjDiZM6FEShsR"
    "GL43VXD4lyvcFl2VRLTM1NFjdTZXo/PAtzWiVy8hcKdmlkKI0eljiRnLPBOwuLv+7AKXU9dny/NkhD+39LrZ9KjZbGnUnqQTfKkV"
    "T9kp1YSdWgRmJ4TXS6/G0LBfFEF3wchjNJCeNecKbfL00DsSOyOgAjQtSzstS+sPcmdOcExw1W0WccXzTrUQ4QL876lpd3bnsVyG"
    "zuPOlSxRnG9rf22zHbbQDDk4Qmr3MrU2x+Czmr2ERB1t5mcBY/y2ds7V+eLL3Q+FDcXbJZFvBL5/rHTTvprOid2T01ZxxoSZtzB9"
    "CJzxey1BSnVn076u8qmu1beiH2GziuYbrZfP5kQ5eOTyxqCylzU78Bqr0CvCd53M6U7uS0Mlp1YrrRZdo+kELkm87kjpbTw4IkLR"
    "fCHuBfIgxENgkOHs82SBXtfsKBI3Sp48kqImtCBfOUpC/C3rCIi6GGuU4RiDjAXkPCjd1GYHq/Wq3lWJfC13krUR6dHreLUYK4xq"
    "ErFX2YI1a3JnlOxre+3nRULdB9aABWuDQg0eunawcoU0myZNX2HS2FyJJu5n6zGygGJPiVKXJd/G6pAnsQ4jc6/ymhUD63I3j5PC"
    "6rFTET5j3jFIRGbVqCVoM7Hzx2Y53my462IamD41TntxN6b+rNN3NAcXi3GsnsszHn80ySt6/kqe8fiDTUaZn0w6nr+UZ2orVt/I"
    "c91e0ssf9mUSyta/FjoQ8IUV0BPjWxkj+aVOx+7UaMbqZ3qfFrVmyrgZ+0p+7Xoob4voF2iNwPQcBnpc2ff1jsJfOe105GEdGM+z"
    "/par5giVJHqz+T4gyHQR+ggoop/Zn6v3DFFYvcpDAyEG6srN5suc1Rotqi549xqtjfQX65oxbapIKDIx45A4zOJs7YZdVOEp19GN"
    "RDS27JDRki0LNjkghM2XocDclBLQU5JsSRuCEfisyYMtUxZdR77oAm0LavcMTfKDbf48GPqbnZ1GkI0jHXZElfNAWW02l85mrkyr"
    "fp9tnHmuxG0tkDy9/WJc/bLTB9rbKzGeLtId813HN5Ts2NbxDeWTagjF/OKspLMlqrMmM8EGKCFmz//8lOCvt+2DzguSHR8UeE4u"
    "2evi2MS24RfCeK9oViVCCk3Mk8OYDQH5+HN97XSSeqbDnrFR1l7zrv1r68pa74UjiIswVDztbi0+KZha26kwOJHLtBtifWj7We7N"
    "ac1z6i2PaE5rz4+J8REcNGEuq3O+G+AG63NnbczT4dVzI3boVMB80gFObQCuO0mtW0nbYg1NRKZboI0Vdw2s6tDASp8BkTP7cc5+"
    "gAez0sjdGJprm4U5yCxWtBFTENOMkwI/VxFPl3wQq3aboNR9Ovjfdf1W43zIMnhTeE2MAeGS16XT5yZS3b3RWeaeqZyTXlr6tAy4"
    "WlYdLoXVzOGEmXZFd0mtnN7J9mH99ZGRl3zEuh+YANBgr+iQeRe9FB2ds+eEwecV+zTDFXBEO1wV2cHj5LNP463lwtvzIe3bajCa"
    "QM2JLS+O7KWVN+l4Zc65OZuBCBakz4oiqtjtKTHy6O5mk282fK9GL8N5ir7wyGDp3xsRwZk1yXj0cN1uieuLevAzmI1Hs4sxsXoQ"
    "iuEuIEO8Sxy5BbsPwk119tmnCSxvnHHw/WYnE2924uIwGjuV3TEe2uVGH+YDY0wDC4EB5uxE3onTdHnEXzZj6tXcg0cRHh/eQ0Tv"
    "Wc4IpOc595McOq9e6tIrio7cJTaqDb7uvOh4k9wOd8y6iWns9z8+e3bw6/nHAxheQJFyXJUJm+smFUwFzlOYY7sNy0doVTCxmf2K"
    "PoKp03FSFY4YE0VX1RTprqtO4XzWDxP2VPpQz/nBmAMQK/gQygOShif1UK5vOUG0Rh7mbVubFH5UD+VCl1P4UT0EYygJzCI+lG4h"
    "Jewllasqn4oXSruqmla+naCHi8K84Uk9rDguPVd+WbDWJk3pxBjISMGZpYhxv2juFQksH0L94bSYvJdSMD99UYrMWhuTBPWQdfdR"
    "4GubBSX3SZEaTM4eaCR2I9whsaThBMwvK92Cbp4X4jV0PUr01lg7lff5xJZY7+tJe5uYy3FmoJNC8Rrk5ua8UvkEesjHiBQNk3IC"
    "v2SiPPUA8wURaJ4dnoO4fOiMEhqDnL31TNz1PffgKHGWHFSUkx4nTo3DJn1qk2qX9IlNqijJHY2TouuzFOfpkeK6bZFcZnAV5bsF"
    "H6s8LLiKqt0Sn6gqLFHbqurdgp+q2hWcIj4kpxq7pWnaoEfE3i/55Aq9fo8FvMfsJtQCuLhuhd6LpZmiWTohCJg0zbcVrCM4ePMs"
    "nfG5bj20DP9OF6Hzm86tRE3cLPmIFGpFvLX/cIm5Zi+cBrrsxSlDTBFCUa4AWBVAw3xMa4MpzyLMcsrMVlLY7hWcU/icldP+Zum6"
    "uDgh0MK5J1HQj+KCXcgdJVHlvhMPsdQ76ZIOu1R2ILnmDhYhIHuQZyBvtls1MVZjXu5Xn01A70rHJw7kZf9NqK80zpIfAEDyW5jf"
    "xj7kH5xw5MPAbHd159RsDN+hQciQux1TJL4ZNxQBfFCKZ81x7B1EyQfGrwjj4oQwySCYFzrKicLzTrrvaS7UCViFh5e5FDbxdoyA"
    "jTkFc9FEmJ/lvThCpvBlEWhWFV6GIoi1TLWzohGdNnyCyMZyY3zMJ0q/vyiibhJRKuMLcHQOMgkYTZg/WtuFbq+qaUOoTJDtRBlL"
    "s2SuihKHFfxGcU3TZKYCK8lkqawt50KFhpHJpTPtHCkn7UjuaLn824X55As6ZuvqLrm1VciVaXJCpTmHyh6rlXWFAd86dFpNdZ20"
    "9ukU3sQoq/QJ7LuOkmoaPrxOHOdLWhNKuKEtUF/rGqJyjfEWVOJ2WTU6OaXxXum6YOW9Jsm18jw2nf3Kc9hJo00AsCaZ6G3aGl2h"
    "ZRGt4COMT/XG32yAumjscrIG8xW7YmdGNG3NTa1cieS2XG59AZfx8FqKCxWQ/sCxAti7CntAqbotVbaGCpxsnv4UsUs+Y/cnbeGq"
    "lRKwQ5BIP0EGn39JT/p4JcEOUapxpajMNh7eF7fnjna3VmvtfNnAdieU9+OdPQTSZsjN1kNz2r2mesuDm3SHNYmvimiCIRUszgoE"
    "mDq9osdsbmYsTubDfb/07r6gJVrkK0iU2LsEtTXjXTPDRulIPuYmRNVUZi74HqGv7aLFCXyjRt1VpE//rNWS6A8dPa9hskMPP9bq"
    "kh++qtWIH97U6o4fvqvVBT98XasbfvgDsZf56ZuawJqffqjVCT/8VCstSV8SGwWP7NGpMMGnHdcRsO8Q6J4SfUUE72nH39H9Cwjh"
    "39ouEQtJsD6tPOOmM1zbrQv22G1p27JoUvYjnVXMVtrXFi60teXcYIAYbLw0R4wesWzzGzCt2JulMYuzGzFtIH6mVL7ICpSxrZCp"
    "xuqxorxObwtWJ/Z6WUzzW+ktSJCCOP1rpvkNJzhmj8U/lFHNIgTca9f2Vp3P5TBL3mLFriqzD81t+Xc3R9HdHIXfHAm4/DT0iLQo"
    "7Nl3WUbm3LEBJI3rG0NTx8lOwo4BwFWxKw6u9601kWugQ/SGQolVK/gNtybflEzJOHqUfUtxona7Zbgnx5nuOeYKOhWIaWCnpa09"
    "KEZsHh2Oop7YNPSotj1igWToASs4bIWhVOtFcVuUcD9uQljABXnrkgtlGB8hnnKziMlakr/V9aU+aWF6cklUDEKspOGNrcI9IKvt"
    "ETPjIzpN0ibpFc66FAbPvZpSCR4mEJD4rCKcnRGhRdqylRiX8VuLO08lp0YuGn/Q5Q9CRY0K77TJhH53Y7NDznGy5f0+lyVilS8E"
    "irD1lluXitC690uDzdXG7N6Itj67Bxf0MI7tlrsuzgqIYSECLYg7gIISBBV4UC30mRL89SIk0EnXxM8xEXNXGPL0hjpMvCg/WGLm"
    "uPAkDj2H5FByUjhy5qTo0DMnhSNoXI6haOjdkjQuy1IuvqwlXYqAdsGXZVCtp4C4WOe1S6qcFLu0ykkRkiQ0sIAkoTch4E4LR8HR"
    "HBkS7qIIqNS7rvy6zXTm4nX4yC+8WzMdRiYT91kq9CAQZLTxNmlD9YWLbjvHRcQoWNFf0C9ezaowKhzeWVwbSmeMTDgUd9LWJhx4"
    "zmjbm13vCxtPdkT1WejM6OzcarSwasJ56BbsePfD+0U3KBN+drP7mZw+TEF0mob4lONpIqjK/XUzM4G/bZat4bs0aOe0cFpcPaty"
    "+aCVeEtdHy7lB4ROOu5Kv9qYBc+YMHY3CBG1l3J5jZHCgQj0g0WyZbFf0bzJAY2n+SWhETrxqIUFe24hRmWXt0sIo92PLimj47jP"
    "SOpv8rrcScJuKOj9rRFDrWH7J2js7DzcK1RlsFfozbnTuG9uOsg9tOFnjLOfzPhnL1luHb9g1S3n9a0LH27bcShxtvK5sgE8RIgN"
    "DW1LKPWuxXjbFDWXpFgR3CSZhgm6VAWVsQm4w3nKN1vperQqpskXUOQauWmh020kOLRW7MAkJ1KlliW1Dk1oHUfO/w7nGGfMyari"
    "KDay9h5vFIaXZ8GIzaXtvVWrZi/qbG4MGeFNCqwGKEFqiwaXRflAYrEolxjN5WuwLkzT+SIuC7JkAYGAEy8GAhSekkGTLtV6qJtv"
    "PcjsYEgYwDtoEjJ4jivmTmIAY/ufe/ALPu8kbuX0icTceS12LWvrQGc00az4v9k8j0Ll3FVAV6QF25r0DrPG2F7z6xEHrbTRRqp+"
    "H+4XVgphTfED22r2ETUfeChIc5XDf+tKj6j+0Qha3FW0CpSVaKtVpTnyMNeVc1ltDzwCClwOEElaoW4LRuroM6yY2DwHTQYWGj4x"
    "7EPstm1negvnG8fM7FbVq/Knor0y0+Kpu/fF8H2RzocdV8je8RblIaqVndq57OD3YoCnnhVWS6oVt0jUXXZ3BIt3l3IgUiYQ4Hj9"
    "1rmk0mdj3NG4hDHfE1Ma7onvST7dSQ4ClRV8gSlRyVi7KfAVGurfQ1Ikdwm8zambhChqvrBkE9oGkxSNhbJJxhw4tt9/xlJjI1b8"
    "FxF1HPQUAQEW7MGrtqyFceaCjIjDsatmIFfAXC7ncghna+6+gI3OJsTJEYqjUZrnG3AB58PeHDbg8CZl0k85nXYl22HM6aj9TOXW"
    "aIvKPBq/JWAanxu/CHwS8q0EJsE9gY7wGrsmEcJDM01hGvYA+6WSpmT1vy3u10x8U+z5hyqzb4ukHfjTAFGYAxP5wsv9XcxL0UmQ"
    "XsB1F+HJifGw3vOueGvnPqNMTcMw7cB1Me/cRoTz2yF4htbiNeemxia4uEFAqobKF7t284J0KQvmfe+rrdeJ6E0y5tiMvWtk5KdG"
    "ihohbFWWh1wKhFFybiXobQ72JPy8IswUql91Dsoeob1eDiIK8m3oSwl0PkYIJt57DAtZS9Nf6+U8p7yPkfTwY74o4KiLZ4fng7Z6"
    "Xd3AFInOovhR62TnLIbW6lSCcEqQxlDdy3KIaxaFt8o4GVbMQ9PxeUMbiYNJJIYtsRQJa2TzhVyj5KpuwuRCMrdizJV5EPrBuVyQ"
    "a6dlKLFfsIz+qiumvIRu6ChlH4fw0c+4Tdxoe0VTKyYrNpsaQauG1+nrPFq54FhqqmZqAXcTMTz1T7aOydbEAnJhb9qW6Wim1nYw"
    "dnAyKMizKVcsyqkmY8yeTZLX8PiwNbfNtLDujjk9VCOWxsGr6nX6PDoxZvIX6TW2wR3t/17qtpnu3OTfxSo0nNimF0Pt4b7/LyAi"
    "gDJfI1egGe7Sd0V0x1HULmABcqHulMSZcsoKJfvOg+8WKWBsaJj9veC8VH4y+bFchHwHk1f+JRzqLQRY1f/7MroIDCUuCNQuOqUw"
    "AReK1nJET4GOXiE2AYdW7fovXOc6eZYE/H6WQxNEDEidljr7orNGL7R5rg+K2dio6hm8CKfF29AQq3Ph/brw/nx2BWpyvcphVODt"
    "hb3CtHdznJJQ58MaQEeXMF0MMRbrGHkWTr0rduzs9q/pKyaDa7N5/42Lr5bVCmu5nA/4lsAJaBG4JVtbstcZ2gScNeQeWq3t5Vfg"
    "PMWZIsBTOBEasJ0D3jabnbWPjZ/M0OrE3zCLG4LJU+Pod9I/Onz8aSd7Epj41NnzIoK/7TliVFWS/bl3XWQcn4Clav4jSJQOJH4s"
    "IrFRJixOaHbubzQRWTVc9IjwBd+l9mhEvWbwkKgGqOxnvUN2DVkBHddZryKitNNTU10Q5Ol50fUKF25iCRRs9ZN66f26On6aus6P"
    "63t8H9cQKOEIXbGp42ZDYwaGyc2YSx+nk8a839sfd3or0mHRrgqvpwWwEWoZEHkNuW/vFA6iizhh9xCBJ8siWsupoY0TFTpGrAEU"
    "nKDVxpN16A/eGlkJPjeF+c7XPHesocQgMCjpFEmI4KM/teIwySWbacLrmNESljyvhSwEkxgniz/8+xpxdRsvHD8UIF5+EqX7Llf9"
    "QxGrLxll/EWo7h+KwK3knnTyAdeepz8Rtzs09OwXIohv7jV0/lqqgI6Z3xuMPwbhAY3otpwMNakCd7OGQrONEFVXZ0XyE0LDJkaf"
    "XM60IsmV0UlI88DdZVeCbvBIYU7/3JAOa49LWDpMpLeEEgYd2u0i4RkhCOF4tHp6CBiO2F0SI5GqH1jUyaLcixgkOsa+k3SrpjiL"
    "QHN1EBqkyM7/uTWXrbjshNuG2giVgRf1nDJw2tJPOkWXDzs2Djd0+g55fn+BgBp+h6aiQmwwzgfqMAhpHSwnMwnWsrn2ZnFyywpV"
    "xBX7e2Mb+FPE30XV0EiA4QKSJ5koWubnjiKHUkXtX+VyNne9za26qBb/Y4ZTRRGJZEhf7lz45nErbbJ4w3yQ4zpNBjaX2KBWqaUx"
    "Si2BI83ChrlwbpX3QAMKwUqCRsQdKDcGo4jC3l1CwgVQ4Z8Oc9H6mbLOdMxIvFd5Cck0zuqz6Xk6T6KJOa35bR9IoEItW6jfnyNq"
    "MOtCy2aao4eHfCVaBVF1EbU8nSCqRvfYqvaOLeJIOQrcWcNrgVuIRhUwqaGVgCpJA3/BVmYdOPgsumqmVjVTdHyqXscLIFRT3JWf"
    "VSuvnZ93W6yyV38S8dmQU9bjDEzKBtAoe5nDHdYdy7PiAAdYdAX6ouAlEzCpU6dotXYOTQsiYjg9NRJ48UhOTFJkd0wNPbPBhCNO"
    "wDtjw0h1ydKhbUWITYjfns6ARZPq7OichYfwD0oUIP2eGnoMgTs8+VuL99IP8L2/FuwToXCIOU+L7OciqQdeOEp8bB7wvZUlaCqj"
    "A2t1mebA6TMIK5f7PC8HnFwvU1HMO6O1PE9N49j8TcTTQdNuvNGKD/Uh67/ucsD1Li/bdjjg9m9ywC0Dcm9Ck7q0YxIuNvchkEvR"
    "v57EO5atkz1vdiVtvQlHP/i+4PvSaM4a7/7CdE8FwmFTmdnv+SbFVMa6EXU6x76bshQZsuRMWNZymxiBMgsl+JIzZy8eqRCeUwK5"
    "+APhGh49chI0aKwQBSG6IS0rSQ+tSqVxoTSGBz2q1BAQyBHL4zE7fQTK5/HlVItEEmJV66AC2u6H52muagLZtFJRDpa8DrZo7Fa9"
    "NWEqFunZXM0cddZdlUWsFkFo1I6GcaCy1hOzNw53Khq9rCg6FoOS8Yi4b/tsKOGx0jkKBlfur/M4OQO/HJ+rNg+cHzBz4EMGtMZD"
    "xu+R1a7XeWTMjkLHxeLA/0jVtHb5jgsdNjqDKtiuTgO19RAg1UX9hcN/mPiYtQjaHNGZIU+2MFd0caNmXMRlOSrfFj4o810fv5DN"
    "DI2+scWSXB7efcNu79w5IS5Yj7paMx7SbCrBxhEqv2+wXL/QgCzPE3LHCzo+eey5o9FQZ1GRR9YlI0e3JSAaje0hXoamjHDwmEs8"
    "WVVx2z4WqSHcCyPsYP6wYrmbqH4V93ah5C7UhEdY3R6Qn1B/ciXqE/ReWo6KllZ4Eij9GxdMwMu5oJQmXdv40Udbg1J3aA1MIkCe"
    "ZeDmviigObaqydOLPHCSlwebYJ53tGfwaogO2qQwwRziLuDHH16MRgYdW7+ZlfFHapljHEDwZ8mUuHEJveMPcsff8hQSLs6Z4cl8"
    "wwnL0NvkQoWOKK9Q1hgUJJfEvUh/ICcrJsaxQzLCOl0LGFk3ergpw08lPy7y6kTeiTTrtXseRY0RMfsptnJjcQZmgusW6S074R1p"
    "1pSoJHCyMWxuAxcGaXrwWOhXaG7utOPK76QTBOEw2k/dTcJtGqSebI2zW7nEQdhPl3CjH6jJ0tlyiEBUOcOKOYnbDCoiRol9ZZTY"
    "b/Pkzs658ZcpSuoneXJxb8Zxnugsu2VbV1B0Yd5LmF2YjwKX36aI3Raz/hGiIO6Xo5zPsubenIiyPt1sZuyTBI7eQhfjnbLqmLbH"
    "1F7D5tn7Opoqo982o0IwPlS9ltgCu/Vspv0GHgK4sACfYKCtukvDqMeBe2q4uCTWmtgHb9AiPnkCKzXvPtqXYv/GEwciCHoZVEG4"
    "+6LTpLbOOaS9adDeZgPJOeMq19DWeAqwn0vwDus485wddHc8ncOxalCCPYFHcISrrSPcdtsJ+uzNmqFSPowLjtdKVK9xxK2JdK4i"
    "E+IZPrl2KnNn0m5FpVTUiLFkOYTYiZ1w7XuUd6e1sS3iq1Tnztonw3v1eMeRtV3AUke7tYZLh1kBiGjcizY/rvTxC/gPm/MVO4vw"
    "WfAyutCXRfkdy8yh6Gh5YOs93l5cSmGiX01RHNLlztAatbKTA2m/kUssgs18pbzMMrnEZXbDOJTJQ+5yOjfmV1Tfot9fDAp2R3/V"
    "/zxbYksE7o+u2NHrTQgQU4F+dGclPsi4U2rU73NgHpM7NupZNJu1Rq1w0COonsoTDCwCWzWcfouYrbjl4tWScfDZMLWutResCY3t"
    "Y0rhKylhEkw5o3NJPYtmHLH1R5z8z72SGNX7PI9mokO42/FOCCEmua7TGdFP6jIeXmeXg9C32zROLqmvlwPn/A2uS87uclxDAuCn"
    "QrfAuIWn2vTF+k/bbK43mxFO/Fz8onIYsKB36rrfvxxo09jeJLv4Qw6Itgi3AgfjAdyYrUDwdSmkSP1XVqUoU7Nns64ZdyDGxGUd"
    "oZbr3LuMgsDSOmMSS+4ycLjEh67jPoTiI9qYu9g6uGg7FoaIHyU2bdgIN/ds8fQwJEbn6WQ49zLzuWXQiFM9m5+nTfaOwJWe4uS1"
    "eRheC0M+6VYMBFvo1MptTKLZdUYKywgxEP+t1G5AialsPTpby+Fqw04bnDumz0xUmeBK/0pikMrL5VAcaU9B+MIhfnSZXnXhWFQa"
    "BZAvcREAYJkxeLCPBbUT5Uq56g7Fk3tvj/Dg4CM7FIST5k99tLZolR6KzGpqiJ2IcEhZ6vqr029f9/tX/sVGTVoMoMJhwAMlgleD"
    "a/v9ZTQXg7Ds9J4oAlPlkA6IbFXFCc3VC16leQcnSTbP2+qp3NGsIGjNoWC0UFcc2MKbxPUfY2PyVReN80qegFaoN3IBJrWbHFS+"
    "Qpw9LiB3BwgjjQcqI79c5nPPQ/x/uOQhUneBC4sqvQK/x7FBCnMV52yg0AdwfhXjxe12hUDeOqQjyoCOwASXAR2BKejRUB3B052h"
    "KIQ6gSNgrFmAri7/Av6Mqi1bL9P/050NHG7dhmai8abwTbh1G4haW/ys0gntOsKXOZyVT1OEIZs402FiQYmUB0242UxCX3X//jzO"
    "FkTXJiXtd9CBwQlmqHwEXAg3vEWYNH+inIOndlc222PBLOT4nFDzevAYsXzCp4BG7nxWf0ikW7EFP1hHtjyHKLrfb8MjUSpveLFp"
    "Rv0hWEueOwTN+Ve7cxBaXnuEBKbKkhKGChXqZcXuyGdBIJPMkn4mL0B8yz3Et1AhFk+uwFxcsY7LJJvYW/Yroi0cnZVFOCiZMqyg"
    "d4CHmw4RewbfFbOg43GyfHpIEE3EP+3ev8lYGVWFlGgC4906ug/TLExwH/bmLx4RegaPFbQkEI47v2DUhSCgyQszxWFPoUL5AfK0"
    "e96ljZuPtuvSLCtgKjiwWuaGJoUhZjLvUqiUspJTdcL+Tu/Zc7LfAquc9KdchMF84LOPTFYVQ5Oi1KLr9BhW4XmE8CxQ8mkG7Kbp"
    "Cy3OxNicoCYqlyigmhKp3BS2DIQGexzsx3rAtfMmCiLDi8jsRCaS6DSEzs9VNYd5UQ1OxdwqaapQ+6BLUE7Ue4KlNhhSMDwMyqkN"
    "GB0K23mYZgw6XuJiH84HLH/Qn07v1EwbkZR1DCeRAFLiOb3XbRFJ/a36TPTAtIU57AdXzXtCC1zwgrFH20mrLlZJqVZJbe+mG3NP"
    "OQH9b86Wq9yInUsaK8sSqH9ArBiTNkYnpZsiiSUdOMMy7vs7bsgFADo+PjN2MVYQhCIW5NA4DUs//VyZjK0PSS7agK2aDqe5RJtS"
    "bXZvx5I2nUAIOIH2oYqm6V4snw8SSVO+rsTBkUuQKca6s5S1wtSSHZkKgeue0pm6Zpd1i2hpT54lQj9peKvTfFIo7uYM3Vyl9hz9"
    "CvCGNCa7mpx1Cf6qu/Z0dSdr2OEi9ppclQKr3Bj9MlZgWV8sEjq1ETdNVn2q2AXETCy+jdvB32ujoeGmeM7TSF3sLZj9ncDp+4d4"
    "pYpOzdbPnaIhnOq4CxJ21mRGT3nT2kSeLfEHOFwgRKJx9CY+YnW2myAbntbbRtma8R3ZjO/IrvLm5CqfVjfvaJxRbJPFSobR+Amo"
    "MHahJ3OSOZdqPCdWO8DcJ3Z7brmCSiQfwSpXQEliJNwghEBx79zZjemE2EO/pphGzSsahTj+8T8/22ym7Cpn6py+TfcE41SMnRXn"
    "3D79ogfdEBuqTctUTAu2CAnArNUAJkHu1k6iC/C94EvNng5tqdnMOrNJrY8P2oD1yrjtIFBcpbzzJfXV7Iuibu9s5nA1KAjUVnA3"
    "yNHY1SSMdAl9EoQ48jA0h7fnWYjIOyh8aO8LAuXnobZ4ksbNCJeXSrQ1zH0ke9qrcvEnbM90SuKItb+zhuWv7Gj6xX0sJe0Mx+np"
    "kJbG2LNgNZJDhf3ssgOaaBaIYxbGsHxmOBERVK6vQGlPd2VL3r/pjBd7vfirYttF//OMWZt+/wIFGVKhgjEHrU8sEyFMZGcL/Lm3"
    "ycR+yIawVNnn8imovIUR/ux+Q1O30Ok9wlhggc0mLSFKTUuj5G35G54t8zhLEW5ysCigpz0F9hV9sOHyyWy49HxQyy4xwbjjiRl3"
    "fqAtqumX+2XobNuH7erpNLvwEnwQLLM4uYl2pcEz+NX40DCk64fdPtuRHBxRh6cHR9Ll1ZOU2B76uxx69m0limYr1/uV7f1K5Cq/"
    "841dHF/Lxd3uKALlreHq0aPth1uaSUsfmKf/rqXZwYFaHhwwins6E8b5CfzFCiJbwoVbqp9MM1gHg1Mo3BRQlwza/NComUf07SoM"
    "y12Rr54uYzfGYYwbGMyhvYShsl7uukhX6or+X6Ym6hB3YpVeST9WPkz9BxdAe5oe4jW+X0aSWonS8kjd0eJfpMuDKxrzLUQdJ5Rw"
    "bDzIXcSmyUNq8oJbPEZThyZ5IcNYhQz9iq9s756mF/GahlfasQ0tE7gVyTkrCbrexUV6yToYpTj45vlCIyMa7gjDHcHF3iw6Phsd"
    "XJ1LyDte8fZsdA5yNx2ZK/zCacJkYfsJfVrg0xWNtHianmQnaZHc4ii55mqK832gUXfUKneYDs3bbJFHx2CvpWM62Cer9IL2yeop"
    "ZurgwPl5eLRSYmIOLvNMPzqC7gj9EGjNLKFFm7YY8rTSoDIDXNjwy/D65xb+cJ8cbjYr3JloGnR2idGh2OM4GVGjkB5ehjS1zKy5"
    "FCYozq3/p0BwPvcaw6sAm0+tIL3/WXyp7/NLbqMuOCfDjO+9l/wBB37cK/TZp/FkEMSEJH7L5U7EwXkV5cJxdPU7VqFGCvVpZaMD"
    "Uv1V5GKQtqEJP2o8zuMTc/J2nD89JsoDUqS58EqY/Xgeyrd7OQJTZLY7STTviMQhezNZyhA+cyPAzkH5+BsUDoUDp0U+gAQ0LH3g"
    "mAni9q4seQl+NDCRyhr4h7VNEdvkPfYiHMrIBVrabHrS5WGYCv+NJriK6g5PZ6soThBjjSukFwXyLoKPjGGRQX0NhxaHFJEZ9Z0Y"
    "eTgD0ig8OSF3r94bE+5gGw9kkz0xyjwAu1WgtG7lymoCJa1XxJ/fwoePXlSgNRg6oylfUW82c3jwM5fAcsMNwr9xPjuYJHqPAJJm"
    "dwlhBvIIh7IRevDUMynU3vZYtB+1g8DcBYePtUtcgW4Be4PV8obxPu6GCUrOgsoZ4fDe7+x9esQOKLCZU3ZI2GXjZM2FExkhYjAa"
    "+iy+6+zA4GZVJL6gs4KNZ+0ZA7vL7VV4n9I6mbmUHHMrn2ZGX7gTs/UYbowTmPPOg/t6KJC+JEoeoine0xmTV+xY4UiwbW6CS/Q/"
    "+fxTgkxinFk2zRTcxEQj7fe/gCqHXD053+1mPYb3TJO3G9xsrjab60BCOwonbXe4zqfBmC+aItEyZy6NwfkLayBiLaZwt2mvaesQ"
    "XxbgMnO24nppIhT1inh9rTvTba6OCPWsj9nnOEqFm6/oRKQpOgFpQhf8VZpnHDMi0USz80DzbMHqd6bJpIGE4L9qgJ1187QG0mMq"
    "1K0jDlCXDlFXu02JxWUmUQm/o9lp2pDjpNNxVQOrGCQMdKJMWJ3d2+6/uuq+25F7rS84eDAzcIQ8iTcjHGOOIsIylNmoBVwbikfD"
    "Sxad01+RTEw0K/EOmrZawv4c9trOuTtRCZUyYrOkYv+gQawUy5b5pM4HEBA0kBe21thzN+yjRIQcrpz/ccU8NQZ5sY9FCbY6l30E"
    "AMPK351UdPYx0Vidu0vPrbrVDL+7QXKs8t6t/ovAIt1gN96TqcUmYD4Nt9yyC5vchFZleSfIG4SR+jUwNcmu2J3NVp2Ea/idEa55"
    "0e+IJ7bfH8EdlbwY9MwWbIRErl3GZiNO6FCbKyJ/ILOQQqneQs/FvmaCqxPdCRaUhVMBNwM/5BDcEaJL18vkGpA00gRKl4T4ki/U"
    "ok3m9DpJbtRykrxQy4tJcqrK5FarCl4Ub7Q6dV4S4SzyjFPO0yI6hmrk2thNnmgX3pkKiM7As+UyeVtElHWjw6A6qzwSPKTNKdpu"
    "Q0eBVsdDVPXGQOTFZSlWJdaGzWh4mCJ5WVbQNavKg1tOlThp5aSaMoXgnwPvSVctVETsJAZONabUPZGtUAexEaV7JeK8mE31yWPl"
    "oid8SoeByeinB598YnPo5Z+BGt8sD01oI9jQavaV2o1Yz33vtR5NBW608j0b50CqUQQyDOtzGq5O9vSI6z3N5zatxTcd1ImHeRdr"
    "9vL9G5mI0IsjZJ6kRLXnHa26Tx6zPwiuLyWuDb+ElXAotbyrYBgdfNITRbxlzpYiKGkuA29z9ivR0dg76lQtxV3FuXdHzF2HXk/k"
    "80MnXXnoZkqMF7Hdzw7PO3Ikh5owi2K1M/HmOhPxPwxSvJcaO0JEVigd63Su4EHpySRet+xKXJnIJHXAMaLqvOO7nJit/Ek1jJs0"
    "f1Q9fXpElZRnzTnVk+Vp8+goqdJmOHmC1PycTQtAqkTcBCVRszQWWMxwVGyu3laNVrjEMD84eHpIBxTKVQhbDGuifSczV92Z2g24"
    "w3oksQ8L7a9k2u6VTNYmV9BMDlx95TZaVPwXd+maHaKb0yzwmeU+Di9gPIYPEoe28/d3mmoKTo29cGjeG3zX9i4bQW0mTBHX0uIZ"
    "K5eIJ+wJ2dSk7nIfwHmqZ7qu9ZSZrdDP4YVBFIzDulcxrNjeGsFv4wwtNOsEhomU8qy02vMvdyJKzC5BEd/mO8ntLZJPdpMnCyQf"
    "7yY3iI+hbnKYi5yKFq8fwqtIM5K6yaU7VEBLEKWzMAID3JhzGSZaqNBNfuYM0QlA5VAUvz15ehT47clNVLZ4/UX+iAhW/YSg/zRn"
    "5Emthfqyvrn3eceX+a7m7Re0hbLTnBoVzzronfqC9xVqPs2dZ5rAo9Xrrl2TqZxa+rMjkmaDHvfRu0CjK/jkefBJ94NnnZ5ngKpr"
    "KCpCFZs9zCShuezvedfrlUWJcmcCYoF986d8IS5eNfI0Yif2GhqbOuO1Um+QCvYWjlxnI+S3/EQgQOcl3OfuR5tg347j8SPtlQJ4"
    "4S/ZyU9b8g/7MlsXyWsaLNX+nuqdJb1euU10sBF4CuVewASDRHwHpzgu4fEOEzaakWAcFievg/mBE0frXRzPXcJD8aj6/W+BmJiX"
    "p5c3/GKU2ZJ3ZVcPQjTNXEjIwFJddNidETG/WVU6+2oV6eSdJQDCxHkWTChBUT61PJqU4aDy4TOHnQ8TngXFG6N+Dyd4h4EQIg+E"
    "ELUKNZrgXn1HeiGd8G6oZfTtLa3d1vtKjP6Exg6iA0mIQiKr4WtsXvypYXrFkbACXZ5NigiI2ecJfA/JFutVss2omOvdUxAWffDU"
    "kw6tgBCbdjuyH0XA8PP0u8Cg4rv8r4HHxEIyCsnfI0KzRsBAxVvNklevnEpIcAj8mbO/ctvv3PS7DjkTwiNn1MMCQh22qKaDOLFd"
    "5jjPnUCKqmYPu5X1jcobfDJ5u2ybmI+C9CWb9LBLfOiuwXc4bkYRkbRl64dL+bYV3bb0C44+cy12bD+3/NuT4GmhM7NW1NzSF+wp"
    "V/gx9iN0lFxz9ARazQQBVmPEp4AZV/Ypu/vKHicuWEeI6ipBdoGvli7q+rk1EReJk4mTLwv/dlZX8LUUJ7thIl55sjdwj2ntuLFl"
    "Q4DueIgINhU0J6B/lv0ANwrUYBvT16u/gSpEw1ramzO+mDO+mDt8ASHaDEbMeWY87RjlKEYkcXKWK346T/gHjL3BLYEqdYhidFd/"
    "NhyRoADqFD900IBN5LcuPrBZ8trBDHoQvAVYIuCcg+mFc2VnaptVTI9nR58l1QZ/usika/m+h1n29bUCNNPxz8pYkh0Nd5c0QL2h"
    "+NBhYE/DBXg4iDXb7wO2wtizAX4Ow8y6gi7urAqoy6SrAQQLCIiOcjv1RnAPpMmiVzVB1yY6FPzCrNi+OLw66fdr9lSzUhMT/HZF"
    "m3YVeMbAYftgTJju0G2y59Ftrqw0IdiJX/HBbMgm7wtPAuqc2E8IXJ8HbwGl09nIVqQcEAAXxlw0Y5WwhGnV5zZSj+OwiDBlxAId"
    "bjRl+2ojeHfopC7BpudOL0d3eccjSGsgOc908qprPfdnHgaZOQz9E9VGym4Vl+W4CKJK0t4t06PPhjuxtaj8uBJphFyt9D/7p3cS"
    "Yo3S2aeBxOMpTcwhxZ0pI9bLCnIOfUTUdUmn29DqwY2GPQKA3peFuHiFcWn6umRnL58gABPV8Lo0Zp4SRYgKpfDJRT+PVTBLm5R9"
    "2wSBuq7YVtl1n7vm7Bpbr9TVemvHVo3Mya/QTaMWZ4Ovg36ClD3CnBGYnf0IlEdnf/r5MIjqDYWPgBAI+MwfhJf5Wx5nA08ww471"
    "SR0b20Cj8h23TiO8thrhwSl5Zh6VyTwPXGBr71Mm9gflmXmkL/j33H+Q7/jdhm03JCoFcY5Q+oaGsZzBQbDSIo75Gj4tM+8BFxf9"
    "SZEUFt5L+9AzNAJ/UVhf71AuHttUNOm8BwROap/nThYrFsWXJSf8S51R2rnwij/m4sH0qzz0kwoRot2HXwXOVVjhNHBObq2R0qjM"
    "ysEH0Dn8/yB+8BrCya/yR4+UdcTD521htd/KbvQTVoUTes7RoVY+LihGRHb8bHwo8jMkeFKaZevQNXim+brQiC45U1zHSUXiOD98"
    "+c7net9y9jvxXIsRf8CNbe4yYlVMpSh+z8YSzrkT+kVo1cAHXdd1rmUbrPNc2wnv4+5XOIwkSjb0CpK8CRLNwMTRYlCB84jRdn3a"
    "FZ2AAHyOteIPr3VslLjTaY1JNrOJ/Ord5ZmXDh/hTuraPRJRVGe1lXvQ26GyEiXDi4QiJXgydlpz8uJuJeQ1CPCKhIuJ4WDk52Ih"
    "v+YHarcMPubHJZuHaW76YFapvbQPpj5tfhvprDvJK5z7RGsm1VZVHMsrBRAwTFeUgsVIfy+Mr3xWWoRC4ERE+/CVpyren18ag+lv"
    "cr6H+TJHhD71R66+zodWuwdyzDaNQp1q049IPNGJLx4OfQNzYxMZHorbVL72ngXr0LM8x7NM4AoC5+t2+EeettFY7NBfvTk5ffbm"
    "+MXo5MXp6Yt3JyNY9aN3qY6pZ77gycm7nTLfo4yEUc29F7v0y9xO3R+5eB32CpDKqql6ZUeaAfY9oX6WeVl/SSzZl/luEaO36r2n"
    "dAmMXTXNTyUiK7jFIACrlT0ZQTxRkV875mzfkd3WXrARVuTmht+I15Qcarg52/arkggpq8SaZ7piksUotwZBHakdUBFVEN21Cqkb"
    "Qb9DHYZMutcbl4ldxHpXjMsiIUznhQyDdyroI75JIPTuogCzYDTYx2kALjlH2mPw5GDBCCuSXhHQESF6qM5cyCwCuSq9I0YJlXPU"
    "YJw4CLVKdSOCtqgSmDAitBNApeSiv/5zTksMnti5rObkkpYcs0OMOgwvWzFQbr01pUzddovw1a2JOmP8XB5aZ1LsJYCI/PqdxEWx"
    "7oWj8W+3nxz3Dujf0zHU3bUTcqe5IYIq1lO0vmJKWZYgzG5lPdixt34XCJsae1XOi1JLk1nYPE5NG6ElcSGHPEZNaS+0ICV5sEFj"
    "ZRW6yys8WEhtm01auMd6aDYcr9eQ15lNVwumos3s8SK1bMiMHVFXVoxNS1dJRL9Q4ojocEFcOGgK1CDNgXHC+FwMMM59PZ8gIUSK"
    "K64CVioSQ9EEUJSohxLy0ASLahkhmIMbii3rbRhSpKq6jISUy+wTNwhNV9c4Te334oaIS+KekwOE2JCF4i7F7kzjxoVTm8IFskPA"
    "OHbAzV7VQw/k7BfGuOlqii3ctMqO9F1uKudk1HxlAkBMi4a4zbs3+QI3iOysJ5EfqpDDiY7w4muahIMXV+1jJ16C1ZmE8vjJwvtE"
    "yMLv8zD2kgMpAMfbPDowEVTrNK8vV/AR0jhXdsZTDq3640zgtscRF56xy+DnVm0FB1HyXFCdS6TnqH76SVaaUMHL/5e9b21oG0kW"
    "/Xz3V5hcDmvFbfDb2EZ4M4RkMpPXBDIvY5CwBGhiJI8kBwj2/vZbj+5WSzYkO7vn3Pvhnj0T5H53dXV1dXU9lF9Cvj+y8y3dJWoG"
    "ysvQM1cJt9CDqfhO2QlpHIZB16UT6XlkO83t9nar7YiLSPkcmUW2vODdwCkc3ew5c+Cp+Xs7jef4GHsMBcix6CyyaJtE9iyStPV9"
    "BCO8Kzuf0XTvntPQdJYiai5lZNd7GsB1ZF/AhrD3L1RlLEhaMBh59ArGd5Wms/7Ozs3NzfZNczuKL3catVptB9/FxeXa/Hqvt7uD"
    "6tj0z5vXjjjTM/KiCUEM5zRUP2QAgcg+i7a2ztRIpMuXspP614BoZHJ8B5tcupgxdfw5iVW7cAH5vYaM1skLTXacK6sNlLINpMQM"
    "i5Doh/ZI3keN6dWCiViqPT8UR/r2qHwVoTQxNRQD1pW6pFLhShZefIMEXzT6q1la8su3QR/DmDkkl4m3r4FbDmZTHTorQOqMTHJw"
    "Poez1lH5jsjKYiRp0wEPRgxSnWICQghPvbxbHrOUTCOdIumrRykfodjd88kLPhqgFRz4ZKVMo20oZ/j14Vi2+nfOyw9Hhs0SxJ9z"
    "P747IpCgoIvGmEuTY5SCTKaBfh5IqeCwyKsOg9Z5DORLlv85iOaJGla6DRd3thYasAljGVWkMUyzOVpWgxgUsDZguRpBHc9/VDVj"
    "/5TQSL7+QOokfo4Ms/jriF34EWY6e/Bnf/PeX+7hRt13iDhplHT28Evm06fT91XcEGh1wvMeSG1dapM9A2qHJspx+PZFEKs5s66Z"
    "mWJRlBE44eX2MvKA5ypuvSJEhI4TPoqGkQkCAHXWkvjKWozRuw0Qqkxg64jbCHV1gmuXfx5F2XP4Z3pPPgBCQycay5RYIiC/J0nS"
    "Z7Uh6ZhOKLnURm0pvHlMrfZHsjgHvBfM/o4FKS6/iKPrA3o/kYUo9RldpVfTj6NcGoLUXW2Ck9e0wRmFRkjdcKUNSl3TBKXnW1iK"
    "m4jfb65jAJcljiMbHfqXc5yB7RwbYFe+c2+QAFoY+/Re3tPxERfO9jOAE3IJ6GZfHEbECeDVEIiF9KVnhA7wyzLsC15O+Xspnkcc"
    "c1sWV3HCMzf1yOKo7755n6KO18j8ZAxw/HMQoaZy5p6cdD4AHSiaSs6DHyNPaDufHcadOEOMoIgDru1s3ofLKiVXMWygs4oQUa4Q"
    "K3s4efyY5IqkkbOCKlOM37KCJ3M7KiCJZ0+KGHIhG6dkOcgVdJnlCqlB5rDnOlcEBonvYVf2pwi9HF/aV1tbV6j5dMZf9bG4j8Lv"
    "MmuA/mcRhfx1p74OMHzMdErRY6OQdWdv1VeWeSRUS89osv0DGxuTP3zfvtO/skpwvTlHm1jDbRIfXWd+rms7Fm+INx16/Ymlvuf9"
    "iFwMhuXMg46sru0G8AZPxS9ktWv5dwbbAJ2QWuirBneWIUgJ0HTQRxCwO0WfbpChNTgEOAJHKyLgPd9GrAn6Bj1j+cNpHy6sf/A3"
    "DfI5wnyxeBGRKdslmsFb2Vs6JOZBj9sDmv8sSInuj4hdNdFfNKDPA1cWPjAKT+XfORXmNbxhQYJahBs6++TKqWPaBFVNXv5xXuzt"
    "xxr8IYG3sibD8h8Sjl8iEhqV6a+QqRmA/JwZR1mtxh9yNQBOtwwnlJecETeP5Kl8C7NDMcJyBRNx+qFPdtHmrR7qnBNElquollWp"
    "Faqkvq6TR2m+T+GUoNQRF1qaikaR0kyTL0tKeQCfl1RsTXnEPkPTHoKfJeibNqg1VvdyTFM8KOAXXqAztSDzZkdso6EEJCVD6TYc"
    "CkFa3jlJKju5qLt0WaRHj9dBklLsLiT/ZX90hC/x/NeWIfIsSxbIenjzr/Yg7S5SS4uSsAf5UMbeMfERKdxOgi++HoA0SDE6fiun"
    "Daxmkj5T7MSLGEg/49X6LB+3Gd6+3kfm28aLqBhilRDae+XZlcr7SEiBIrKUKgOD9LCRQbiRW2Dkx4NrP5qnFE0+c9UYiZTTpcU/"
    "P71PlvYrBiI5W9aOmWNtvR1VHOjREWzCKjcNw/HwM2ANwtUHXrSMZrDCJTtsO6XLGT/4c3yASmW+j6btaOk0MAbJdlF7MkcklTpu"
    "Z1jo1cYNfYyczFHej6GrAxnik032YXNQmKQyhikm54USTRxRcsjrcRkOpPNo+RwNLxwUFeoUeWI7KCd8HfHDRcLZt1mFSZaSVZhi"
    "BfL3MmdBuQeQu0CdUoDEOfCzpCY7h0/IiSBHqRvy9fE2Gk5liVssATO3J7pE2ZPmzu4txlDDPrz9GrQ5HZ5H/duIL9QX9nw4595U"
    "433VRl/6KpjZXGJra+fkvDzsE5OM4RkXGG0PEsRi09qBe1qSlhVYVNRigGQayTdX/XCsPIIqNPMMNLtAAdSx6qE/MyjIa7mW8g7B"
    "g8z8N1k+6cxyUE59E9YwQN6PvCzLI/ID0EyrAv8Sm5Z7yY/yygNwDZgDDzKs9ZlNLyv9gJqo1i0dNMoR8L9tx7Ke1v2m8aZvtFZG"
    "dcjoBtD0uRJrKPmGtX0eeXco/QeU/94PLq/M19CoGFMEaRGGSsOnkyGQWgzoNu6P6I+1/UcUhGUHUJfkmaTXqHaiceOXb879cFi4"
    "5ioHZCnywfRNbHrKj67mPShCG67vzZTkClI+qpuRk1xFN44ZKRf5eXIQhYYK96Yi4RLO8dHPFKeA3qrVFQEXIIRrL9xJnX4hD/mm"
    "FK525zkOpP+LFGmrmLyPdhqSIm4orUUpBiH7RTFqiWjqkaQCo62YDcTQwEa6YW+Qz+VhOizHhcEIGgy94OourH7MRyfkEFnjMnUg"
    "+mrsZJBkmAWaU7Du1QQN+bRMui9CLx0SVPsMQ+GPvgcQb/BavsxWDlbtx8jegd18uhhYJ8lTWR+++jtZL38WMVHqFwSkJEm6ijJS"
    "ERrikd76PQX5Tg3LjhLqpSgKO3CsomVDjeJ2sjai04d8GSdwgE7KhsPfIvKChKIYbZmuVSowFq2vCvkcFcMMLI0yccQoOT2H7DM2"
    "tFcWCicdyT1DbQTYRn8zorevjUt2Xj9EC3UVSTYCvk8WjQydFTl/9IanRCHx6CXsW4qBU7Fh5qh4HOPl8JicigD4foyYjoaqoZS9"
    "ARe2rlT0GPwc0c0TBUDsIywkVgR3kTuMFQ70cXVp4Un1U2EGY4TFfMYPsPiw1hvB9SyKUzdMN41V/02vOqkaAW8batYptPd1dqZd"
    "Eg6HpL+VCxZZrUJvP+gZMtkx49trWvpDRI8xjh6Ng6SoUDoXz/0nyZs82PwxGh1+pQcySGGx+6+RPXJ+8c8/Bfgw9Cb6Av9eJ85Y"
    "/B7RzV9HBMgxGL9HMlCW9tUfypeHGxWqCtVfLoJpSurnMiqZLEu17Rijd6CJZEGl6NdoRacosH+N4PSqxCRLXNNWsEa1ZtPgITOt"
    "e/fyrYykcHz46/GzD4fPSEcHE24CL71SgUqv6GhCL5CXZLOFBm4c9cNPHhD093Zup0H4ycmAliamvNS+Iz77PkZRu4kvVA32/zB8"
    "6BB7e1T2E6FiMXaEYgYsiS7Fgug5IFTqgGh0de4zphR3WFpsAI298AA6w/KSocHGzKfMxDSVkFbHjha/Kgga8mwHTh9tFk8qDoUq"
    "w+uIezHNkDHmp1wv5RZXe2tEW3Dn/Yd3Lz8cHh05ZFWWGRFWHa0s7lLgy/fHr969xXizl7njXzr6REYYoMDuHAM7WwTlxHpy5U8+"
    "nUe3cDIDPwtUpq8BM0BJcICPd9pfJN2SuDU7gK04XAt2vKFzmTBvei0PFhmCRg5GTUdpdlK8H9vU7wxtWuK+VkpjaTUHFUH1P6BS"
    "GI+B3+YMw5CQTNxQPRzfzmhxQvUsFq0jygHqRWTYECfZNltzTZFuyHXxIFd83a1J1sCt5iYGx+UHpkFWlBRdjshYDP7ITfimDH8x"
    "JhNG2pHUCnZeZEVybWJNVkehgKJTirIXD2lCcEYhJGYJO5dL2EY74Cx0WMz58h7MpDRJgK9AC6fFe2Alg8/+4sCdwcr61uaOmEDm"
    "KTBSQ+A8HihjvOwmWvwqpN16GZU8rklNIkkwEsjGJOETAO4AFgeLFH6OtZAmW+GoPlbkQsBc8Wcuxit601bCDH/UQJcwgORD1VTT"
    "6h/rq0ADWe0xP9gmeP9NbDh5roME15LUv8qWuGBfivMERlX2kszJIVZBG40U38Ru8KKU2dEmOaUZNizfwE2SJhb/sbOKRrxizNmz"
    "Q1RMQNWaXHDn2JbeWpXtbaaUg0b5r66vfS/AV2I4PN1Luq4OHs7iq37Iz92k/nSGRWfS1p4Pqlhbrbo2qpnmz7ZAh1vayGpn5xwQ"
    "DApzReGcEb3b5F6WJnsZEjfYZsmWNn2RyOyLDAL2RYJGs/yonbDF4+TKjQ8iD7ZxuYaRBOt16cpYJ9c5uVZIblj7vc5K2l690RRX"
    "ieniTfvwntiBeiijC768ZQ2/Y5HhRL4JM2s3/FOFLeiTIgJeVhcLY3PDzitjWGKssg2ELAtsXLdEHdqSeafFPKB0lypOxcSygATK"
    "X7hw8ljJnxlA10yHwPSDSL/vqZ/81Ay/oaxuHD1JZhXpSFYBC9CXCCM2qoWgeanyxPg6cj0KAr4zelb9fSzFClhuAxkOGDCN94Y0"
    "uLEHhAMdq/HczwKon+FPfluOGa4XLmBLVU0CNwilyDKwew2gGPzdpUGXSb1MRvzc+IbTXSrNANpeJ3RvQL1FS5/ZycyfTgmQqrIX"
    "u5eXFBxKtYY3TdJrkAkoiZhEcczeBbgZN/TwECZjl4yNe/Xiw7M3h6oQClPU9xROlJXSb99/PNa9wmlaLKC5QgWAup7HWv5QX+mK"
    "nMqrNy9V2Z9fPT98p34cPHv787Mj9evo3ccPB4dZZ4qPlYAki7yNep/ha5hZ56klYxb7cESyGWaDN7hy2TTr8AQJe1uD9kP9MnjD"
    "YUZhM5rhZUNrtQCbUydwd5ik8RTuDMlVcIE3CHeK/177qQt3iLvEvkcix1oK+GWQU6BR+FItNSn8bflDKjyXUUlhesFZLDbluC3z"
    "GPUgjtnSCjvHIhuoKhlPf/TvBA1EptE3JsKoZBJ8YQIOUKbgJyZNfa7nAJeTAp/HGO1v8090JCCuA8+b+o8WqosYEePRMg3h37oT"
    "rfvxOWH4wg3TH9GDIAzHGZOtviZQIUlKEv1qRqejtqvXaqBnqAn/JvISZgjQXoWFZNtOZi4J1z8VC7pcDkmmZnp/YY8U6YpHiti+"
    "S0ZozaB4qRhd2KlHE4W5vmpxiSO+BQzwk0nfgX9c2G0imcGttI/mUfNZ33HjOLqpzmcOQ1/+xm9HwlEm0Q9HeNFNqJLw2xH8RNF3"
    "0ACM2naW4igpxl5juABYvxkuoYRx2YE94JBAJc9ZHCuvgRQGR7+t4+5YLG45xhhsFCsDC0PkIEFNgSwS2FWyFHeRJW6SjBgfJ5lp"
    "xw0OeeKWDxLedIcwORUOTxIfLL6tvbtwprgncRrbomo/EJSmNbpj+10i3VVvxObs0G3JWeaW4YqeRjP91GBbqaGhc2r9A3gffUyg"
    "vAfVno75ClUngYyp4eTI6C+uHVIUDvE8wWNPKyoCwYMrMjDKcN2R+lLUxoqI6HN1Mo3cTxiDoyDdRWuI6ueqO5uRyitwZEuBNlQa"
    "zM8T9SRo9nb080vZoQQJszKZqRlr8skyeObI9vAoMRvKlVNtSaWhjJTTEqjFJjNfJSpfUdvqs1LoJx3NGah+EPpK9COe6Qygje9u"
    "QpXBd6hE/KHzMw1OdMqQlRRv1hSZycxXySFcG/2YovG9TTI3S3w6DT8xC3Hv61JorzuJwovgcq5/38RBqr4/S1Gz1ed7p3if7Vyk"
    "RjhbVuvl8Lp/JMx8pxSZ/S3fxlKlfvKMowtzJYD/MzxDrTcP11FbcyleGLORCsd4pymXZXwfuozSvsFLMlBj9lCFhpGsuo54RCYY"
    "IsoVS6+AVK0tJxlzD7bYMFYCA6tfvE2pDL5Eob/6QQJE2yZLrukdy9Clvyx8iX+V2MRvl2Sw1tIhEMsYSN7rRIfrLKkQnX9THyex"
    "+vpfjvjAJXWgZ0DrfdupIXrv2U7PkG99SbI3dXUXphmXEIivgK3+zvVKkvSzilCupcwvTO5+Um3tqrKuLHvxYNndrir7TJZ98WDZ"
    "dnvw8PDYYQFS18zT5Ro7jUKAmU5LusNxnn138PzwxcvvX/3w4+s3b9+9/+nD0fHHn3/59bff3fMJ7NTLq+CPT9PrMJr9GSfp/PPN"
    "7d2XGtyjWu1Od7dXPXNgC4wzYu0vrbJBq37WoJbn8n+1gKxKaNMal51XIeAKLMI5XOs7rXk8LXFRR3lSo0fCi2kEhTtPVUM7u+hh"
    "CSHyMQjTXWYL8dZBrhlqwpWedx8LqhPZ38GJhxMgL39FbHhwfLg8wAmRr53Yjvf2OotIBBW7g85yd1HiUrV30WdSpTK24/39YKvR"
    "blOE4QBfhOOtcn1vL7CqXwUEXDACVIYsnQdpYhz5tOjfa6J3Efv+Fx+O5zi49udB35EfwLcoX+s6rQp0sa+THYGnm+8FqHWbK4Lp"
    "Vc5wBE44TfIFOA1YmcC9jN3rfKZMdMTMu/gc+DfFAUByldNhBG7y6TxyY68wAEiuUrpDFoKXcVAooVIdcemGaUoDypeg9CplOOIi"
    "gDPNDd3L4mAwoypzHCBGH8nz4C+J3Wm3mx3xkuVCjGEfE2sbyk9hX2ZY/mMm+LJfkhTD9gseeT8mbLhbI8aUjXT/65cEShrYHe78"
    "kuhF5jfAPxNu8YfEhl7qlvgtv9Uxc4ChjnGw9a6B8nVA+Xpbe72iybT1Nh3V22O72eh2uqKwZX/NXdI4jvuAh67m2Nx9Gg5CY4Ox"
    "mOhjUrSnrrBzLHOOMc4RXZDBzqimTwEEKbkTVjGlU0Ol4KU5EoZ/s2HAX0UcJk9q0HucvbwoV2oBu1IrLgatArDMFVwH+lMJnqZk"
    "YA13BCRSTSXbKpKRZiMjIDEFZqr4A391iiG9FlV9mCIaEEnAq7khwmTtwoBWHZVVPyaopUp/KwByCgBGS1kbqOF8wwI8Dv2llixK"
    "AezHDAMBE0KKxL4smw8pv5usHy6RqSv2Uw57CHVjY5xAmQcBjjNQ40TRdwDjxH/wba1Sdvdthl8wtt1qjIM0B4TvhMZz2V/rr4r9"
    "VWV/ezXVW2Wlt2q+O39izB36/jPJzT6d5NcV9x/6OU/RzzmegrB6+78laK4kRR0UoR2T93LJSqKyUTMesCYZlTHRaNXvYG2wFt/V"
    "awygeQX37wpesM1/NUQg/JqU1zgWb2xtwRwxIngm/H0cC5FnrcLc4F/cJpVyjOAmDWzYdrQ5NMFD8fTKmQ47fvDA9m08hfHC0bpF"
    "HhLod6U+pgnu7+/iobvGBWFsgJFAugZgsMephwW1NTC8iRrrEUxylnjQrkRGAyHcSU7iVegm5V7s35NyaK0ZamQMlXYdDBU3HLSa"
    "CnzTiOEnuYcO4CMUv9NlFFifl2UoEog2+lYH1p5+uqIOgCf1N/pN/0Sigdq6lsqbcF4i2hjPR2uEfanX+7H40mjX+lndCVSCUhNL"
    "FjYId6IGTjVTrgl3eprQQJMOaCTEQabMxU6wd9hheNA16p1OG10GZz87FvyeTnLH3xpcocOw0a4XjsJmPTsKETH8URNQpVmXpPQH"
    "PIqhp0bxWAFUwGMlT1B2iZ5QVHvk7vARok7v8bwcuE65NU3zR+w8hxUvCW+274S/fWsJ+E7hO4VvXt+fjMyfzExcc8qeTMRkQu8D"
    "6IUrZQSgal8g8QsmfkE02EzY21iCXxQnaGL/JL+m+BVnscvub2Gl6cXwDj4ovsMX+CB1yJSych5QPZMu0vRMsniRmy80/WeiqdVd"
    "/4fsxxfzR2oUW5K7LoOsZ/EkBgFS2AAorMp17e7AxUQXEmN6LIbxhayQHMCKuXrF4mFozyd0zPXLNDSArTE2gLYxOICjMToAdW54"
    "mesdcw/PJoUbEDmdy6lxSx5Ao/E2mmbwbi+niKb7+10e8YB+2vVGd4u+pFBv9TQgtnAtWZa2L42n4XhBf4Bi7gFCZ0SYNWGAzGdi"
    "QD3MwCYaAxgGKBQAV4p4BZjzEpEwsCgB6QuUioiuTPhHQj+mhLEuYlVhyPdEIdJ1FAIpHWIT1ZxYGZADpEPQ9pTadtETBXYwBRoB"
    "m6OQaQ2BPmNA2ZB9SJY3yvWtf4aYBvTCQjUwQIep7WOKJQARprD8cREjsXmUEWfOWa/zBAmWO8SugZS0FPUCOmbxw9KGn7/xjf4h"
    "7yE72EOY6GvIuHToAZWq9+gyWJpFgBylC7gM+l4pRa2yIA3grpj4jvXAzfvKODsA+/n/fQN8MQ4TsJ2oAwAGIMa05QtT48tJkbqO"
    "Gs2uaNTrotFqi15DNDqi1xP1XbG7C8ktUW93IKsr6h3Ia8B/rR7/rYnH/1fvjI2RnxWYKKTcRSZq73KyjonazyVrJqrO7z6TB+/L"
    "7/Hj46vcfflo/R0ZdQEPC9fig+JV+Pma6+/75y9KP69eeY/hs/Rd8Zr7HL5erlxtX+J34SL7An6U3mSX17uJkkV+RWgqFQJQKy/z"
    "F2yS8btJ+fMEdt7w8wSYoAxIGW27LRT/Hrnh4ff4iiC1L7OyR3QG2LoV6z65CaRscQI47khTs76UOG/ep8uS3BWlIClx9rYzoMIA"
    "3cnDZQMgDmlSokIlmGwQedulDz6icxKRC43SJ9+fleYJylbSK6jyGX2kR6Fq37+dBbHvre/Bi/ykFEZpaRJBtXx92Y2bliRy4fth"
    "7ItSFJfw6QfG5KGPj5KrqpRif+pDn14JH3tg6HfRPC6xknMi/QeoYaXuNUznoXElwWXoolYOw4CESarmTRyFlyjt8OaTVFd/vX5G"
    "2KqqeB0kCCVd5W2k+/vk35WUnByGDzs2V1OO4MFVunan+O7t6zECqujWHqzFo1TFoKqy3F0LkRTgkZTm4acQYL/tsMbTwcQejer1"
    "eqfZbrRqu6LZqfW6nW6rvTsWo/pur9dqdVutuujUGru9erfRhuRmrdVrNpqtbl00e51Wa7fV7PUwvdcALrjX7jaBBHabjV673cJm"
    "ep16b7cLXQjoAQjibqvbwNbbtd1et9brNUWz1m7uNluNDjYPFLUJw+m2gJL2mjCYeruLzTd2u7Vup9loQLedTgsG2u7UsNtOo9Xc"
    "rdd2a6LRbbZ2d5vNXgvT67V2b7dVqwuYXqvX67Rb2G2n1m002o3urqjDJDp1aBNL16H33V0cqGi2ezWcI7VS78Fp3N1tAl1v1Tq7"
    "9d0GjBRHAxOB9EYNCX+9CQ3VKblThxHAaJqi02zu1prNehfH0mjtAvlvwxgBbr0uTK6DoIG22s1eDQfZAK6+U28y5Fs1KA3nR7cl"
    "cAVggZoEgk4LqkO3AsBfb3Qa3W6TptTahWk0ILkGmbAGTUzudmtwbvZ2m6Le6rV7vVqvVscZwVkEsK/DaVTfbUOL9UazTevRbuP6"
    "wGkGg2436rsAIIJAr1MDAO7CiQbw6UGhJs4J2m41GrXdXSjf6/W6deiV1wmqNmGgPdHtdLq4Ah1M7rUb0NIuIFmjDReaXmuXlrUJ"
    "SNOsNzuITQ2AV7ML64rpANN2F1AQ1q/WbLXaMBtKb++22oALdPZ2OtCMnBaAqNEhbOq2d5uNDq8TLEKjBa204WSFSt1eExsBUDcB"
    "D2qQWofV6sLAWgSxJg6yDpBpA4JBn03CgUav1YXvLqY3Grs1wGuCGKA/IESjh6sHOIh9YZ8AwzaAoFur4TpBk11YY4LkLq5xrY1T"
    "qrdweXdrhEu4VIDzcPwDQnXbvTqhKuyEDiI5sBoAgFoXlpgA3wXs3G3DboPivdpup9mijQCAB7yF2QIk6wilVoPQo9lo96AK4AWg"
    "NuyJNuwzQkpANkD+bheH04FB1GqEk+06rHcboILUoAOJ0Dnts1oN5rJbA+6m1WwALYABEa72oJ06oBekd7qwmG3aOY0uDAD6aInd"
    "NuzAHoAbS8MIEW1bMEZoGtioNk61XcOV7NQ7sCthj0PvPYQwoAmMoA3MFJSD7QfojDOCPQ4It9uFEXZ3YUpAnLDtHlRrAv2B+TcB"
    "/rVui+AFaNzA3QfcGdAJGHizVaNlauMSAcCbuG+agGQ96rTebUHbzW63hwAAmHZ2ib7BkGAkuDEBDbq4oWAT4UQR5rAidcQm3HGN"
    "XgMB2aCJAhYB2wfkD7Z5s0Y7AYjFLpDbRku0YIRdQDSCVwsoYxPWoyVglp2eBDuAsQPgqiNh6sK80OEo7xsgG806UBMgk4D2bRgT"
    "IzxQTSBwPZotDKbGUIDNCUwpICxAHsYH2Arj5+UGhOjCCAVsSwAk7Cwi5rBvd2FsAHrAJFieNu0FwC5AuBoWb9UAerj1iUoAja3v"
    "4uDrgL31JixVi2EJ0GgBqgIuAubDXmBU7SFxxHUF+MLoawQZwOMmDL7Tw2Sgr4BKiAS7bSCBMHfR3u22gITQFgYIwi7pEfLudrow"
    "pTaRgRrgMRwJOP0OjAGxjIbXAPStIQFu4J7FQ65DW3sXiTQQVZhmrQejrvPRBwQS9wocQi184Kvh1qWtDfCB3mCt6Uzrtjp8UsL0"
    "ARiIv0CVkN706uOxuKHjFTAJ+oBh4QHYA2rLWwEWDwCFGIBXA0S5NuNfrY5nAkAN+obVANJDZIW2DRF6wD9Ac6ThhJdQD+BZryMm"
    "QOlOu84EGvduA8EvuniBggJYHIknUIxmG1qHLQBDbdEuabfqLUCXRhuAD2OFFeiNx4ZGy0RZ1hgiwGZjOKotUlFbAJsb7uFPf39/"
    "P1yke/CjGoqUfvn8a9wf0e9qs4FJnRYU8FVCygljI47FSo9ZBysN13RLRgvPJ0Uj5DLWq1mVckx/tdJ0JayUgx3AJ8CvbqPXWdSs"
    "BVzHFoHR2ruJKWKWUV9youN0B1gXYFPgBEGBFQIBuxGBDXj2lApO/GBaLqeVetfawchZwi1eLQMLYwX55ImIVNShmLL5gpJ4HcK7"
    "U9ndPp9fXPgYxhKLYwvNRjmo7lJ851xSC2PMYROJfTMh01Lf3h+hdFD4I8BTlE1w54DfRRFzMPArNgULzD/+1DskRZyMGk9hkBFq"
    "rMgO/cru0xTaxBwUQq/kVVpmJ+gKem+3ZgZOwqplv1pvW2OAcPYLI6GOYhGM7eMJmRnULTFyRaR/A0BHiZiO7UP+3UVr4vjUPU2E"
    "Zwen0SmZHnN7DQvDquof1Pa1uKK2LsQMCBk0dinOdEIHe/ss7qh1SrDEuX19enn6WdzaV6dnp3didCQOxjYgnhp0B3rJvrETjI45"
    "0OXgr8rvZkW7WNISuVLn4paB6o/tI/5A6B7gu9UIJju2E1xRhk+CzkYANFP8RAINveInEhIYOn621HyTEZIdmmkyQipHc0xG3XEB"
    "FYxFGkVocaEg1YKhwvCyhF01dpnQQhN4345Oz0+PROrbyent6QG6IbnYuj7958XWJfoTmW1dnf5ztnUmRjci8GneMBKBQWN9gJhO"
    "xA+oC1UsUUg9wPs5QoE/CIb5EgxADT7aF6Nj4foah3BXjiJfJFlSEyc48cXUSELsmGOEQ2r7+DTyT6GE658m/ukUhrwVn6Zb7mm8"
    "5YpwKzgNt6anwdbUGny2L8WdfSYu7Wv0CyOu7QtxZc/kskBTsFICh4qo65K1vGvHYmoHSFLQVkbwaqsZ0SCsJS4+puFfhAD9rY9l"
    "pFn44sy6zKxTJtvGoMkIZTZkZoMyXRR1I8pwZlNmNimTApMjEnFmS2a2KPMC3ZQgWnFmW2a2KRNwDjM7MrMjMzuUCViImV2Z2ZWZ"
    "XcoEbOBwGtMi0ey0yDWBSR+nmj4WkJhweG4QyN2nsNiMN3QqiEJmpcXZ9bF5aJRY6PlpYu92Wn5bPJuwecvH44MysIRtFOZZ4g8t"
    "aUNrocuwvM5x7P0kur6eh0F6x/p219d+PAncKbrgssSbyVpvs2+BtzDO5/fG6eQ4jzl5Tyt2Ga5gC3InkDk9AOqkbS8Gq8aYL+RZ"
    "ilp86kB+n5TvSbDRZ+cDLLaSemgslxIsd+j74tpPEvfS77P0iyOoZt4vJjlXomngk5GbhoshaXudf2t8kZRR6sR+LlWhp+UscoAU"
    "9Lx2z/2poQPqb2jjOrTskE60gFveXSw2TLsSdJSg+pqUtShHOiJhy3I2EN9mDbk4e91oPFJzFAgMJCci8gwbrXm5qAlpscQu9vQq"
    "bm29TkjGi3ZjlQq+uIQ6juf8HGZFJsrSYozMuvNKcx9D/3ZGZjClNPrkhzBuQApVYwk0ppypXktkGgzYUnRf8z4rjaZ+fB2E6JCg"
    "JCGrQTSCcY61C74nTmZ0jGl76AEi3xpqGceRoV9GTl1Vq8o8+eQEDVMrdlwIE686lHLVQMpVnzh9+gvV+GPH6UPtgEPAs+TtnJKc"
    "k3PHTL2QqRe51JBT/5ZLjGXROJeacur/yiXOnb5UDfgiF3Rvr95Y8A88nPb2dtWvBv5qqV/NMS1ZS0CjvH/ppexAKkuiTTZrEekg"
    "Ew9rTS6XcMBEjEDRPpCBfNnjKCp5vj8DsIdlxUb60h4zeUht1EAxdLVjqcLOPawYrI1EjHv291O2WJsH8pcaN6CUiE3cU8U2GIXy"
    "HR6q7lDbH4FTkUMNylnnZ2f0BHB2Bnv+m94E0HxtjUIs91EYUv/BIU2iKbrRIeqDkxoB6+SWI/QLZDYgHP2osw4SDzRO8nQou0RS"
    "sFQzHeXAPBoXwTx+GMzScT0P8NERjv+FEY6LI3ySq2yuUupkLpvIWs6xBD9sUfaFmU2mcZhf1/mhmY/HAmQrH2FUoAqr/wEfYmW5"
    "skHt0oExvypaDcLg1O+ag/RWx1Df+CB37RoMkebZzHwMPuTotdHDNgMUO/kPtEZnr/w+zFpWq1dB9Wr5jTD4d3qVEC74GSJrInp8"
    "/dqBg2r2LmouSrxk27C1B8ux0vzVZ4Gh/xsty6sH52isFZlM5sfQBlSn0R5dbNPV2LF0jGC0Wiq2b9d7ra2teM9uNJpWYDfrWzEQ"
    "TYyRiLdzZcsM5RoNWQ7uB3Dtb1O5BpRDziLDHCraqnHRVqsIfaX+/PH4RXUXCYfdpYaa0BBp4uKqhxV3/wGQFevnb+5uprWZGsAo"
    "13uNrRT4BYTJ18YToKZ3p7mVkir3XrRYBPv1er0F/+Gn3W430Oo42LNRiN78Wnv7PK0hqouzqrFcE2oHGtyv10S702zUFvVao7kV"
    "WBiclUoEfCWITa53xQDObtV6HStee1hKOwx2lC4R2RfA9WOVTEdgWf6Zwgopl+PrObsluZzTEbyiDR3UarHI221Gj7KViR1hlORv"
    "fLqmx2bjrRlui/fAlWO76PdKssD4Wz17wo4DHhtT8C/+RE9n+BNNai0RuFQc/qBHntsZ/oA/Djvok7ObKuba5KV1HsezyzI2mFgA"
    "AF6g0oYPNzRo0VqbAf1aRlOBZzY0pfuBYd2SjYczjD5rUOyPyYhzMESLHjMSSWUcsLU1VXcOyc08sjR4P78gpn1uA0q4FtzREbFJ"
    "HQIDogNBtDg0uo/Y+Si6kLv7HO+PCLRzOqpVe2714ln1xfjp5o7yE7HeSOLKv83ZYUiFzod1R/lSmOYuhagLNXPjxH+FLryUs4in"
    "oUC9qIYlgC80FKMcz/W7bb/TOe9dtHvn/vnFbtdrnZ83ehO30+q1Lppdz59MLiaTxnm92Tjv7fp+vd3zoVKt3ew2z52vwIXd+cGp"
    "jgCa2XeBP/UMjfGcXPjBKyCCsliHacV7VIKrAMtWoXuz+kpRlfDNRCrMb9TQNQwgUR3/KpQIpNVjvmFpdW9otnVai0W4RtFNmnQH"
    "Wk252RCdFutEnU2QwuTKuaRHxdnuYnE1wdjsuRKRobIOvYgEa0RcI6EaSaHGZFV8UtEOiQYTkj5HAhVa6TOkZvk7pbGyDGb14H0U"
    "5ww9xRCVmEJUYloXcM7UO5ZsWaPdIZuECjCZI6npTCHX9vd3yW3aIMawtgjA1Bo8pI4NbRbVsS8n69WxsUN/GVdtX8QYBRtj1Fum"
    "fnaMEXjF3L5A7eLrid4cF6hEmQhInqKuHWvflT17bm3figvUPn1ZvoBPT6uavSx723dZ1h1nDVC4BIRmKfHrXdbFW+X3cp9i9rIB"
    "dQnQ9u2EDebL1ljAt2RqBCG0TdiMYWTxz1L5QSu4Gfhr+4zrKip8OY3O3ekxlKS4GNnPviyAbgEoi/wDrEQHGfKnPMqs4fYkvpul"
    "0RBlG+nU59hJSBZ4G/GQ4fQg/2g/+ndlJ3ZvgIgI6dlRqg86SzRSHjmf/Ti4uHMy61HVAGeUV2oFHPHTJFfol1gCxwzMwiPGU4d8"
    "jUEZOivWkDqtvYTDnLl308j1+tMlsw8z6xtKDorEzRCfZSdcCoMpb+SdlZn2Xg65NdGneHYiYrI8ZZ1MIAlUu4xMkqyQ42DyalXF"
    "0eJaXdt1v/mUTn1xZfgCEpfmI1r5unpl7XyaWOJsDYUpnJSrkdKt3M0k4ykw6jL0zpEAH5QDktOuNRrJNFg6Hg2dXN3FW/ctur4h"
    "bVoy3dAn5YZy5pXu288mQw4Osyyj12bSdMN2aSnPdBDWjVekd7v2XBT3nnuXfIQ7yvQQ1fLu+hhFOIcTZ7rLs/1rsxWlx/dNrfAY"
    "EMJX+9eVZu0prMdfbesqPw4pF/5azaVRRbne/2od0zduTtH+mxVAh3jHLcaIY0wJDXds4YpS55ecWFqKxYHgPCj/Npzm5m0ClGuo"
    "e0mQUsP/4aMkOLBviYVx7XP6G9nx0EQ0Ihmaj/liYparbh0SbHD3oC9ND1g6ow5WJpmv8aDDNwB1vwiEKWzH6KJZ5xijUfoUIov4"
    "wKPAdAQdJDJ58qHtv5dZ0OYcfaKwQA8SteFrtMn5F4fWB4gkw6J6qNb6REdeMuqYXiuC90A5WkK1+Y0NCUHpiyobb/jIeGHXbxTg"
    "raLC/Tzh+MlZwGmJLf+aDn3sX6J7vliqufZRhJmUVMgv1CZF9+4B6ZFq8gV9I24au+qj0fnPE0WUz01LhaL/g5WtkFduNfdFISe1"
    "MjLw80Sdz/kQgL9MypZhAPXGnYnUvofzIed5HqPMZUd1MAwUb9QPbOCNhC/53AD4v6XAwJbrqrOrXBUrSPn9ja2BT9GyCSVnUnxQ"
    "N2IFU2i9Mrm+NtwRU+Q7a0Ahr4w4MPd+OUQzDMS1yRRjT6CbRfm1XOZNol9OHnAk8uPkcUcif06+6kjkh8k3OhL5bbLiSOTl5N92"
    "JPLr5FFHIn9OTKcgv03yjkR+nOQdifyI+9T64eE6mtwYUUwn6yKz+9KtZ16Wg9H/1PUGLSOR68p5kqFzHkhYxq5IqdDWlumoy7eM"
    "RgxL4onh1dhntg5xzmeimOaMPzZ86D3NYsibEigVaj1Lyy4AoQzV+IvvfoJtpN0vUhhK9eQmPZNuMxXM+o3xrktKS3gpk61ggAsR"
    "ywgX8tJbhBscVvkkOrd4JsHWllu8VetrKvlZzXnVjvUNcxBXq2ylj/BA6OEmT/EfoPP3VJWfxzIf2BieLGtU7dLiGorATotp6jUy"
    "MMbE7rUwhTY6RoYoo9+1NPv1YD8f/Etgboo9cerX+spCGFBn2c/M32bewdGMXf+ZKUzdVwoCrhUL0gkefPFpXfBjdVVIGwnRkJYi"
    "JcSJUeb3E96bCRzk7vqBZcn7dfLTwmgRw9aMFpILo8WC3zBaphbmWNcNTLneym1cjL2h0E/ik1kgtVYQ1/DEEAx8E2O/iVsFthAd"
    "ieaGhy+4hu1ngGafhrsKGOLIZdEWbYoAN0WwuikMJw3RYhEbUWSMIMmbeT2MnyaFk9mfGvTTIHyGsy0HJyK96zkkhXfyXhJTo42N"
    "3/OsSDg1+CAkeSvXNrQyV3ICn9xT0L1vmsUJgr6ko2TIKHhMlMtF9GeaEbuSooZp5vkfWCYbOQA9AuxKK6Bk2iEYu8UUcwGrEuo3"
    "ir10UKnwrTZeE+AohrXDgAHjpX6QWBr5hlH/tKg2OyRQhTjGkE+//mZxtYIMmjrwJkUUVWDI7ZAU0TTmVvUhkJkYZjb/02K43dw+"
    "ZYiTb9oIUuM5ukmz1cZBub5+ps8fj+TJhDigaKpiKZVHxvO+cIwWHWSr5VZyTPPKZKqEt7kzS3msn2A8QFhscwiBeUID2x7Ko5D4"
    "e5KPBsot3oY6JhV34eLJyaehKNAGxQC6Ug1jSlXdnMfCyHZFYqejaDwAuCbQpYqpgGCGZGsYwL82d5ugW1CkrvAxhInCVBJ205tw"
    "afWT2uKaD1SgvGQJZzVOICMGgRENecpOCzMZFHDwc+CEJQ/HkMYA0sLgMSxxb17Z5RVcbpxqPdutuItRgAw8rvfaTdJXuPPKWihH"
    "smWVDBsSo8v44210R4oSG4vq4RZerhqlz7FTCreoxz6laIscg7FvUCNvBZsNsiYlA4y0eMZQQA9t9m8SQ4870BEedsrVxZm1c4k+"
    "DvOOvc3eZ9y740gdPGnvjqTJJDHkwJqFwNl9BxHEWmVah9Amzn9U2GQELoyjPGVvsQF52MdzAtg57XUT6QhLQfrzaSFY+vUKqFYZ"
    "ZgJUbkNnFtu5s2NKxTdYzmYeAZeQg3AulDQ48TrerJXb9Z2To0Vpx6h/ZnajyV55dVUzbjoTNObSzoPLIEwLadKzv9Hh54zKUog3"
    "jbS2CgWYapfw2uWnUUiEa4jsXWHvqb2YlTjPbSypGJFW61V8hyGdEPwmtZGTE2dghZWKdt/wXw2AomHnnANZhsKjk/gkPEnHFYnG"
    "OqN03xBLTCzlUsuj+/5ybJUwZ7NuZpVHA7E2o7SBaRtmUp+K9U0QH03VI2rBua7cOvCP8oo0iIu6IYazLATGDinMxKhlD7+eGr6i"
    "9dH/dAfaqzTQ+V1KPMBQNdlPK43sesEaT4sFffydlLNsgGVo0ZDkiQE98cBcQ9cT4yCgyk6wWNA6wqEwsFxYIWhBPfzFgqOHwc50"
    "K3UdOYDcpkACDwM1HWGsSnennFZoACpmUQbCA9xWQKlTc29JEuGHUNonKpFR+BEcE2MjqPiQTI+30RGy0w/18TcFTn9oxD47mJJ3"
    "TnS3LjU5hL8UozGf7DdTG7Dq9qBWPbl98eJkXqvX4BP+dA/HO+J4at8/6+sCB20uQP826N/WGHDj2SGX6eCPA/7uUnaH/t2lf5/R"
    "vwdY5jmVec4NHeK/9Rqmy3Z2sa/vKJl6qbfoX2qsTo3Vn2Hxl1gcfx3Qv9RQgxptNDD/e5nfoPoNGt4r7uIAu6D5NqjBBo2uQQ01"
    "qKEmjejVD7KNJrWof9G8f1S/qOXX6leP/qXxN5/Tv9RRq46l3vLU65TSpH8Jqi0CWIvm9Y7LNGCMzzvwH42wRWNr0djaNLZ3h7LH"
    "No3tg/pFs20TtNq7mHOkcmiSbWqoTQ11qKFjmd8haHeofofm9JFH0sORULUOjaVDDXU4hRrqEti7NJBfZHNdAtJv3AQBokuD6tKg"
    "flelCFxdAlf3Oea4VOMQMe6QMY6gVSNo1dpUxOcyNMgJfzPG8b/UZo3arFGbnuytRktRp6WQbSC2HTK2UQ916rNODdWpofp3WPxS"
    "YRtNpc7IQyNrNDE/4OYQsw45kyo3qOkGVWpQepN6D/5Q+EK19S+a3yf1i0bRJIBNVRoBv0nAbxLwWwT8FgE/pFG8YPyilWwR0FuM"
    "RDSTGZc5xO+IvxHXXgCuveBiNNoWjbZNo418hUM02lj9Ili1aZTtHuYkKoem3aaG2tRQhxpKFa4RrDtUv9PFnDmPBHHtBWMWwa9D"
    "DXWooQ411KXJdWkgNwqLCGx33MRzRcu61PAXVYYA1z1Q5O3SkEMeqgMNGP2bqdYE0ip9eAc4nlJMSXUuHk/RP2JqiDUzk8giI4rB"
    "/IZoCgic58fZTHGeFV8bg5hM6LvH+VjmYqv549ytfhlbZQqSYfGpXt1sPMbpfnq0E462cSnkzYJcZg79PnCkFT/f5iNdPFM8k1IY"
    "fcxgxlRSYU/rSk1U+Vpnpi/WjINmGwMjVJOVqZnm2AIliZVyijyjDCfmiAcbW+N+4RCOLY4TOgJQ4PmbAhyk1sQgs1EdpjrY6DbH"
    "c0PeHthi1KHMVFqyWJyKIcBT+I+peDNlR9fZCmw/rQxPN++XZWsxOhmfnOByAOe4uWXGd3o7VQ6tZrF/Edz2U4FalxhGfuYIdDrT"
    "R8X0pb1OKO7DTFQ9Xz+IqoZY7B0OU6XuyA3LRo2X1ffTvNoX8SV/27z38Z9QzvhvwD46gz+mw6F6QpLL+sdUiiflw6l0mqlENkOn"
    "PNzYvH+DN7BltTzsY5O4Hm+mKrDpwkFt6OHGycmNZWHcMRHZupaD46hiic17d+nA3Z4TU0wcBPY9qUr3WfBbdsqni5OTBMpGy837"
    "ZFke2ryzHOFcwmXMi1Jd9ORk+6FirvKu3985GZ0kT8nVOPwtj/65ON18Oh7aGFITJvOkPDp9Mn5qPVn8Hb7+Dl9/X8DHSfLk7yfj"
    "ccWCrRzIV5uvjHCxKTtfCoAoCl73UW0JvuWrFiUjoIEZVOhoyBZeZDd06f52yndzoRAiZgQIGAHcpU24p95lw8ViIx6G/Syk4nti"
    "PIGT3iYQI0navI9pLTKLtOzOpLoJuZuYuwlUNyQshj50JMWUIlTjgrgGvCMJrWRpQ/8ce49VfLOtlfBQQsIAvTFVriucbZmp0yJh"
    "hPKTHDig6HAYD4fBcEgYF2rVpGGmpYQhAuEi0odbiT4mVkOPqVDLVRXS8WnDqkQVVEKsRKbs5vU0r4M0NEKUm99IilI3CFHqZSJO"
    "yXIqacUplyS2BEiG6KjL4vpaffPa+8GQWAJB0AZ/AAQ5GArjt34ULIUzgwZX0Kt+BXbyAM7O7YspkEtLkcvv+CZvme+02uoPCaYO"
    "MWqZeh1fpkYQEHZeReE1fsEwRFUdJEJ9yDgTMrIyFTJ0RIiarkomhgAG3RIGZhb+YuHMqui86mIa3VSvAs9Dg4t+JtdF/Ys4wJdX"
    "nPjWVq6+DMprBiTNlxc4rYozuwVqstr5MIPo+nEYOPPzwyv40LrpYPe5eM/Gt94YOaJ0jthlLpgmz4BykJ0hHckp/oM48P1D6/bz"
    "f8+6MYAeWDpL/PxvLdjHaV7tTjW178zzSnMZc4pRPDJHnrpvGuzRle+nyWIxGrOEN/fEYNRKMfDwh/nUl2WVsjG3MmBh2oOVLYtf"
    "kA0pmq8i78pBs8pnKAk0PUoqCFLUNXwOkjwR/B/LnLWl0NpHmF+mmcriPYUd69cERxzr18iEgrNJcmKPVCjsz0ESnAeAUujkNhcd"
    "eyykIsp30Tz0AIMOpgEA8gOwS/i4u1LfduT6FRuynfNpNPmEEY9pXHbAf1EWa1AeyObhQj5/ZAU46PtKw7FYM4xwTVzfl1Ots8Nk"
    "UaS2wgyBItACRaRgTzB1+TP57u6YQ7WVHcRhB92WKhaRYe0bhBY1EyYELPkzNn+qRZE1vpdTVVXU7zj329jfP+bkoUMSw7nn6HA4"
    "mcTRdPravwBiZehy/JlN/qETQM6lLM+MmXvp//qOIL9YUH9WlQ42HBC2v1iYsvMf/lIHv6kO1MCPo5nRDfzK9/Jbft6wOgfR9Qz4"
    "HO8IUQDlg16Awf8w7CaQvTidOrnj+1fJmtMbgd4PpMTBWPbexTBxQ72iJnLqRTMRctmnXUcvIFwAHWcwdgMXlD60e8S92Uo/EUZP"
    "/QncT8TUTobDSDU6tyf4i9v1bIS3uLBxXcXMRtxGDxfi0nbSaOYMIuAxZ5VpJdifyQaG5WubU71qgOXOozSNrh1xTYYG17YHF7Nr"
    "e1qRhcSVjdzXRVpxoQ3qlvHs2r0FXk3mXVTmVdfqq1/iN3lv5h0JDJcP5G8ahP5h6NlXdH731+QeoY6izNf7GYZhXxeSMN4j+qx8"
    "F+PTh30pQopVybnXbgyJgDT2Jcc4pgkO8b1/Ut68h3Nkp+qGk6sorl7OUzheN3esIcdJAp61AR0tS09L1Trcmb5S1pGhe3+f2jv+"
    "LTDqCToShSvMSXkxj6f0Af+M/v5kPOSLzR/uZxdQPJili8/n/GH1F/9g84GTpPJ40QU6prX6O4H4CXpc1wMW6MON6YkFdya8JG2a"
    "T9RXcJXAYIvxBP7lsOEyyWWtCEERMOWPsSX8uVk7TTEUGv5JMEijC7xJBB+pTxEcrzHxgopccAmg9efYSjq3d05pZME17PaTHZjd"
    "LLxcXAYXiz9m/iX8c7m48c9ni/Pr2cL9HFxYA469I/AOV6v2Kjv2STKubO4E2RU/nBfU8DNd+lzwzd8zsZXWGPtpuvL6JQOspPZP"
    "aCNA8SVYHyady+CqFPmYDmJT92zlRSyer/eFwso9Sh8kH1pq4O/ZzTor+NUb3cVi5yTZUXwC3CTQQYa15jAL5ubbGvVM51VO9ERW"
    "zjn93/+Nlhf5pJ3VpO11aesSh44BEOnqLFTPnqcsg1MLuV0FxAQMhl2EDpKGhaFmSrIU6BVwxhmy2w5EWjgK8dPAXFRrnKu7mlyc"
    "vj8nJYTA6pthO9x57pKotBHN1/NN1nwoSvLw+XdeTnOu9KN5wewlV0UOGE4+R+td5nra2YPdypsaLgBAM24qkGAvsk3fp81O4Z9O"
    "dq7S6+lOoIL8GvEd5rkHUXNRqnBRH/p9/18Whhp6FXPD607IAhODzgJfjFan+E4HDJu6gaSZN4PsobIvHVbs1fJRMFN96ddMLqoe"
    "KoP+Sl2lsugTEG+e2SjKd0vYYzsbADymoW6YbipIBfjOH9hBBoJiOVZ64H6hJZ2FZsdr7qIst8lpjcz/Y4/b83nRh4BAs3IMojbI"
    "tOpqxvPswM0CqOE77SAeYuw0WKMNGpdrkekgzLEf8cvvYhHxW/AwtiNOhO0bVCr8bcG3bZzuARyCnDNAmwfWOipLSXLmdsGlQBtu"
    "xVA7LxTBsO+GKouJV6u7Y0h4B+BIScuj/DjmFaTShjpTmTyVyWi3odKhBgwqxmKVaqoUvuVhbIoZmvG3YVPwdWxK5hydO6DIrpm2"
    "jkQpP1MGMYEjgXdPMCEfXX1OQv0ms53ZPBNwmHpvGF9VRRXVAW4NrlNeaRkR17DWg7DCttovppEL5EjyW3TXqKzJ+IBsp6H8JD8M"
    "ynw919w4oLx8QzDY8uDfZ8vdRzhw5M7NOsOhq7jthFnqiZiiJ0fg+IirJlq0teUShxxV1B11P9E89sSu1p8GGc+uuWyuMyFemwpR"
    "ApxZEztCL3vMYUNLzGm7xFA/rdb7/FUpFijn06sy3cIqtRwLPcmz0Ctc9/RxFnuu3jFS+zGmeLDKhM/XMeFpkdPGBGdp3G2vFHtn"
    "uD2d0fK/Ba5Jy6eLqtZXLlwqP0QRqY9eRQkpctr8iURorcDk0jhGNzZMmRcGIWZ5F43HVN+ar2oYy21FdsT+mhDE/XWvTRsbvuop"
    "C3esCuoBZBTAUOiaG5YZyk5wI6fkvFE27Ad1l3Bbcq7c0Jv6hxgzfV18ap9usmczFHz6oR9jGGk4lVwz+k8M+Kqt6mO0qo+rVSsY"
    "xejMEE0A8PjFX6TCFA6hcq1fVmJC6lo1j6qrXBJIpzJkikUd46S4JEp3Pa9YAwk2HzRM6Y3VuZuzBwYpZICtz4GQIS8v/clllS0k"
    "ooDD/vUsvRvKv/h4qwJHT6cf3PDST3DFYvw6wJDY+V8YWpSkZVT0WZr/Bdw+/sooEEbflhb1VLHQU9kU6J7TitO5ida2hJKKhg+3"
    "N/G9JwESaoYvD+xQoTNqcA9Zj7s/UkIrQ9isdKrYmopOTa6qyLDCpW97ag4fe2ouGuOEFoYxxvO+cKCH6plZHuY+9ws0BtVdQzjQ"
    "KWwlaX3967xuX6qJ6ddcfLsOVt6ug8ferpd4giPbCjAj1iUuywGSQyrYM/7gW7kUE954LqlLFODmdsXaIT44smjjR3QfNWcjDIiz"
    "h5nqOSA5KobSr+/wh0U4VCzJ47UCZIJciUi2+iDNafUDDeQKfJj2LOXOCXeAy+QPRVJCUk90SNbvDFFBWkkVAFSciqXHK1oA/fAb"
    "RhOyBWUWuh27XqKXBENzVG0caQdpyvy0oJI9nEpabWjBAsRiwdZks5kfemVqQ5hv/UfGaVBm0VCGjHsnO2UCGElknL2Tkx1ULjV0"
    "Hs2zRHKjvtHAFiLwlns9G5jNPqHUP+dRmkveo+RpPnGfEi8xMev2Zk6qlkUty0wRW6H8zim/ve/t79gohdECFdqagPekOGA/2bzH"
    "maCftuUTs6Pj/GWZ6NbQDLGWj1X/bEomL0CjDH/s65qQutW0oeiumw95n8rwYJn+EcEZJXbsac88dzdsu5dxGkivgYlAVmMo7fPZ"
    "7mZoHtQ92Fm5hLq2wkm32W+AxKYh+WcY+JK7ldFeEVPWPWcNpWa7SrOAvVrXHN02Af7hcDvRjI+lLWjydeDyia9Wulwhd9U44V12"
    "ESHAsc2nD5RrMk9yYohP2VUjfyYhHI19mcXl034iQrnTyWZB69nDaVAJ+yS7JxeMTOWlv8Vhlt4PjT34bC5tFFT3hHYOdJ1G0FiU"
    "Aql1z0kmUbJLT6r1J2OLk70gwVdKT/2mzfrUfiIflyAx9HVhftoaW4jy4m8l4/9GKJIaP9rTX2w5COEK9j8xhYT2zv9ETyjYAnbe"
    "/R9ZGGieZL3Z4rz6b+wNX2dhS2GkOmzvv6lTsugzdAd9FDCHj13cU/VaCncEbBZlk8Zz6YZ+tkVLKxbgWJnBn95nf+RkXrzrsp2t"
    "edkhehIoEOA3ay51uWfdcO3AFU2tmoKHEK6DHl7m8bGwsi7jO7p0FvLOo9jzY6hDUoO1mVyP87MroyGwePvNEAj1BakIivdrQPHQ"
    "C7t8XoZrPAY7jWaVtY+nD+r06DdVowxrbWQZNUugIKGfsjzhoeffh/qw8rnYukVvtktj7I47xwcj6oe/Der9whBXFeVSjBx/UTBV"
    "RA+VLrHjMcHUKz5RRmM1IBICmGGocU3h7gAFQ6FvC6P8XfR1TrA7MCf4Sr7Y7JQRHAteD2sH1S3gQqDMh1PjrlqYNPniydyAyReC"
    "VR0SR2nWOJaFCgVfLffrtxb8zSk4Jd2oL5driRKuZ17K4W/jGwcssMTERHJuCT0WKP48VIpOwnAmS89psSpyKO806IqABLVa23m5"
    "zLN4WMDPCvimW71Mu+8R6UFepS4vPTBdHkB1vR3WNbA2M9eEoctnYBDwjCZ3amXsqSESy/OkKO2JEhLzpMoLWKbb9yBJZrHqX6HI"
    "K7JgncPC4HVEF+s8TJKp3iMU+ed52RDgrXj129qS66WgvpKQv/wZsP8+4yofuHv8v8Vh/od6+v8c5//nOFc5zpwS1ceC1BzpuflM"
    "I2VZhl5itkkdGHA0n1zRizUSJt6OcM9zPweXLpwB+AR5jEXeY8ztBB2sGnnJm0KuoeA316bq2Y0ULpqmaG2tjgRK2UhsuKMe/Kx7"
    "krTFyiGxlbncXKpwIlJydr/GTx+9y4W5p7p10nhPHV664YfkaGvlXJk2oLEezpPN+zWCpNGTnL2MaUEdnsQnF2T+Z+9jNmpBmyoq"
    "uVg9S9RTfuKQ8tOfc/QamGkAolDJmc2Ds8A7W7HgZV8y5T/nAl0CwF/0pwu8J31UKoLMUjbv6efSeOr4ba71CkdjWN0yO87o9XqZ"
    "3UHAifig5/JrVKXsojQLnyKGtX5sVeqZtQEd//eQ20+l6m20RBczQuqA26a9ks/tkburZSZgD+gv52HcGh5UDXLWO4GAlsLhRq3v"
    "q1Hhe4M5hJikxdDf1pbpDpuErV9oL4t6DRlrdSWAs7nvCsCKPqFajNBAXbgwV0m9cKOHLHxjRT/y7N+tT07fsELZRcGNyPdGfiQE"
    "MgDzGLc0Fo/ZbI81336d27g04vf5A77gflqfEfiJ2JyvdxP33GcNGOADhe897kou9b7qSi70vtGVXOytuJL7ff5vu5ILvEddyaWe"
    "6RYu9vKu5Hwv70rOJ0ci4cN1tM2lcHW/P+EkNlHZAPA7Gw01SltX9kBRjnw9IgAI8cmZq0F6tQ7RnTM6KuAB6qfSbKSxHCm6TinU"
    "DnNtm23pW5hIPBv9KoqJZ+/cl0en98vxUwudOEwhoTzsny5OnlvlE6+C6pKVpzvVMXzAT3zlmUMRGMJJGcqVhxv0aY1OrbFVOYH8"
    "jEp53n+7leeF2YXLzkG+0ROss0lo5PwrNTh0AsyC6+actxgj2RmdntxUx1qEb067VHSfgWXH0qjWbPDaI9cnebYYegHqrax64VhD"
    "BEX7Xmlq2EfCjkyE8ca/ph2nWt28xw7QQ5RxAlx60t2KCiXyDTaz5gmGB+wGalc2YcvQR5uC0Ojr3381NuwaEbUzjw3jtPraSSx9"
    "bCGLk6VeyNS8mh36IhkuTi4Qbn9zLPGZW6OAtazh2ZOKnjWl8Cn/NsUdl923W7vQFYYvgUMSA9Za+3avCzuGvvegakOcq7L1xi43"
    "0GrL9vHv19toNLL9cOupW6Axv5pjbRiexaSf9tQ+w8JkKyHj0MKZh2pqpB0Ap69Ug4v2Qu0MPx1FMtCLb6vQaRTxyw7zrSu/+QN/"
    "r7O1deeh/U22iBG6H4kwqhBGQhp+Xs3e2opQmw2KoLZB5spPuUDxpQsUI+TU6iBiY7zI5PkWx01TPB8OP5KxmEoq8W9KPfUk1l8X"
    "mSpyfihlnr+b01TGlcnPp9qwLESUXV62QmaTMuuttZktzoQF3zgvgqnaRkDBHKttisf0vx3z1z+0NXiklgJYiiKsfVwKXAaUygG3"
    "xnHRsB3+RjczBpD9dUDOtQf7VgG4Vc8ADv0iI/6NAym2uEGN6X61o0LspdniZWr2+G8L9mO8Z+/yLwwlhKGXOKISKmfHrJydWzJM"
    "6zX0DBeLwtBomxfnrR0ArcFwNRv0lTOIh2smC5saMNzHaGaR7WdBoygWUqWy3+hl/cV7sM/zmDdizFspaUPZ+qJQ2FI7ZixrVatQ"
    "aFGub8UA2kpZ5Rnt7O8Xe9xh7Mq5MfJN7WB0Y4Th3og87BnggvlJN0bK96wzUCO6Vx9L9bFn6P2vonwd5ZllpFCZyC/Ie7o98jIn"
    "Z+SpCa4aAc2bOIScN9j9ut82NaZQbJapKl96mc9GQmI8CyeelU1eHRcTjy5ccOyUN+/hPAwFernITpP7xVKeypmbNVMZBe6m0bWP"
    "b/DSvZel7EvhzAY2H47caTmAQ1iUNu+DJboBWFqZfTfR/eFns8u5JzDWHLBbllbX86FOX7l3WGZ1U0srziD6XeW9W2b6DZ5SVFNM"
    "AR6kdAMjzQHSwsmrJngFi25iIu6xMM8Bz+ljTxx69sgJJmitkh1mz73MOWeqlF+cnFPiLEZTwVFXaO+czqqmGADm6MxOTqqoX6Tk"
    "ADAGVMFNkn5sGNkHS/vYGw6ziH4++Vsg5wyH3lqvDILD1kh7YRkfDCOInOycPB2dJCdH46dDaODk6cnOYtNaPIHv0Snc4uV9fXFy"
    "wqWsp0+Gi79T7t/X5f59qH8siIlG3g5mNbZG84/jUfxhPJq+HiPjjFrNoyd/HxPf/PTEGi7KJ9uzKsJf+3OwIA0dOIwmB1Rv5D4b"
    "j5Ij+g+T/3n6dGxLVw6j0kk6fjqrPj7yXKmHZjCrWtKbg8JfhLdNC5EaC7EepGVbzmzInVk8KTTisjLTk2wjxOzdICbfJsr5QT8e"
    "ZhrggbohEBZL7wh900zknWe+FBrMlQdbmW0ics5b/SxmJgcQJAZsoLjeOhni5hoRYaWJ+s1GssWJ0pubbEG6BSZP8XuuRWEvV9oK"
    "sJqit9UqXXzkUVzsgdT9kYXh8XMh+Ww8CoU7Rg6x2L6qtKG8FefnLZUCdRBjM4BT/EAAp5Er0O0oucfB6Ela1LG9vf3J0yYIbqUp"
    "Iovo41LZjWhWNYtOqL0oY5BCN/NxF4kYrvPoGr8SoHujyKbf9XEmUnK116LIVI3JIQAcKMwrUwgN1+gehxLtZU7EI3WNwXC3EYe7"
    "VSxWwvwVfzxxnmDcTTjglJUJHHOBjUdbwkFhEktsBMAjJsx4bm25sPYJH+/wo1oVnCWkeYh24AeZhACZFr5y+Bdpu5xQes/L2R4R"
    "cg8B9wOYev+ZhzY7MHE445drnKA+84y3J7SmRlY4VQx7qixX8AMmi0fHKIvmRXrGVsGHSF0ARkpyroKEZrZlSsMIxTTkZcjTkTK2"
    "0ezQyU6SN7nVS4fZuXz6j6l758dAUXbyd+YBJG3uGKYgUtMsNDwH6OdM0p+ju6a0XSPrPbVnci5RDA+zFBWcmeX9WqZwprSmK3UB"
    "NSzh8BBLeHDx2SPQu4QjI1aOfBGOFSuRaq9BwnD+Qj4Ts2ZiqNzn2A9vPfteOXfQvpLQtZJ6wu0DpYyiVPTp5VH4txTR3PvRvwPC"
    "7N/2d07LCPMAVdAWiX/tAhc7WUyi61kUopn9Qhpwf/aTheooWWAs4ziZXPnX/mJKxvGeG3/CatdRuMAOFxjnA0r6t6kfegs4GazN"
    "nctgKaIZrmiSGyxWfgMM4pEedHKXpP61I6Dea5w1Rg6B75/VCFDEl0yimY8xRZZL8d6QGcrgXalIcXx9WFP8K2Zu7F4n/VDIaNgJ"
    "5KhPgZFRohBSzvirbJEw955Ajnr/WBpSXuvf2+ckSbaWwkNjlzMvXVrihQdsC0qt4HQ+G49QwoNI+IpEBNKttg5Y6Utdu7VBqDZe"
    "eFq7U8Z3wXdkFeNF7pPbcYnUdt8TLEup+8lPSoBWGB5XlLzgMoC5lZ6cPcHgy0+qT7ZRjPyaI1VSxXvDQzb5KLkKEg0V+60nKOGM"
    "ICgHLpMyyCjTZJURuZ58oX4oG6ZI+cU8csSUkNdR+s0rfIyp7930Shc33KdnUun3SjQHOxOrwwHKMC6K7gYP1co51NOeyQsSb5oT"
    "yVRJldpwMP6N0cQpdBO+OKwV1Mts4QKx9tD99ldE83zXKEjGlxbGXgYIJn78GWiR7S9xOwaTEjRTUsub+SV66y3P6LnhlZclUgOf"
    "/Lsht6TWk/GeAKxuHHrP3C91saLbN/L3ZuAqe4Bb2tS4pAlIdFWnQ2LIoAi5qCJ/aGQikOnY8FXkH0gOUaY5n3kuRnhTbrHvefen"
    "S9s3FJZ8O1CAzaG6GgJa0KrPwStPuY7iMVu53aBXCH2QKaoGF7Q8Lv/uSY0GwmIO3LWNHgoU0qsRyHqUc+CSQgMwxLhe1F1hXXgM"
    "lM2NFfIpeyg7Qk19KipHub6szNSFeQIr/VLqEhD7KL85TSustZuXTbotbLtQNesEn+vW1x4vXc8z6mWsykZ9kPf8jZ6Lcx6aJNtA"
    "HiUHjwyOTfzX56OvsNBib+a4xkt6tlszkQfqq9hNGPllzXryciYqU1FiidQSlzVyyW29TSGlHM6cXKGZkiMYwu/XIQVjwzLR2aqb"
    "FYzWQ2L3engUfhWz/a/j87rRy+az4X99isbwcK7v1mK1RGecrSoA08UtPfyWPW1CYGVz05DpBHtsZqraX53aai+8WoRKrwunrBoC"
    "Z+qzuSybybfw0PgfwGkEstnkymbNeIHxMsckZRiWFaGtBNNbGelqSWPTrM43T22KXMcySPQPrrtCoIpVFIFKVnozplGsIyfD8TC+"
    "vZqMn6HBsDq7ByqadASXiLVAs6nBrsxnMUbRFhXFLbpklcJrjKRK73+FZmTeez7vKQKuqsPXg/XVmLocrNZ7ru4Sj9V7vqa/eZJG"
    "14poUVVhxOYztqxmRbKXbP12C3s+uAzhLnyvL0dorg31Qqm8GcD9YTgM6T5y9HAZwWeAOeiyphzZ4GMro56pvvfkGR6+dgQiKB6n"
    "CbNxeuu9Q+3Lg6OjfKwLHkJWQBFh1T7dhGSfhU28LOKCtjRXvZArAGVBGZt95ouibA4VH3IdGxcnSfRW7k7EQxaGIXJ3DL2YGaIe"
    "aZ+B2RgB6vFazDUKr1mflNcnmuGlULK//Xg4lCe44oflKpgdP9Trf6w/OfQ3aMbMlGvN5UnRHln4I/EK31hYkUQZHjtdrq+Efnrx"
    "gromK4sA9OChRk8KWCs7+9a0v1g82ADVRU+a5cSzxAd1xxfs/4Vv1EY0w7zXqVI6HPoFYsjxOydezhHkxsRTLww5572lCGVEyi9O"
    "LtCXpi5HXjn3hmR63TFkYBhbKtcAydZi1lpAp8SqG6AZcGON8uOQTh/z88iezqTtg0PvSkCX5BaKBUZ1c2GHfTEBl+nplU3zdJQR"
    "52KUGS6zUBfA38uClCmRaGAjU4zx5wb5ADWp8vsD/HRs000txkgg+O4VGKZMFoU1FhyzkE4oYivPJsSVbON68tW3HFkDuJms5iHp"
    "jUSifHazsHGiDOQDM+zlRiCm9mRrK2BVKRxUuFyg1+2FfJHTCQ659yOSWZ6qay65GynPN7II79AYMw1TS/sjjUbuGO5dSMGFh5JK"
    "pXCILhWJx7Sl0Rf6C3wgn0RqDhxFnpg9VAbPKCqC47rY2pptbV3A2GZqIB9wd19InUhXrj2AmtJnhfTBnCzDI0Qj6ryKzZdJwxk9"
    "eVsOPyXPuXr5YjicKVcjWSMS6nNTjnXrleeIBnPlT0YQ1HDdpmKucYFEJcUbpWsNYX8597gksCYSr0OBITznVn++FN+RYO1nr/za"
    "QxLzs2cXcTq7bwny/P5Raump1hwl1ERYOs5S+cFmuhgrw/9qlYR5lZ1LdJhWG5NTbS14jaW64ZrGSX1suRTfGwLKjzTe1545OM4T"
    "H7kYHi56t6Kc1yXsU5obMlYQ7ht9cCaIKOr4ncBSaqe/5LlymwUxw2GkS6k0QPayi0VMAWu+oJljKQ9OrnY/Iaep13Id0f19Qn7A"
    "NuY69DgDayom20WpNBAFmqCngyqYetox7OXVOspW+0evvJqJe83b2oL1ny5ParjP8d+YVpy+Mo/otb7Rp/SkMaz3G4CAM9sjm5/y"
    "hSa/MzuT525ALlKDC1SpnNmAup/RxfvEs4DEIxaHBhZPxWh1mGOkhjDOssce8u1f4IenPeR7tG0uxAzIjZgtxS+e3ar1OuKlZ8bs"
    "FT+ytJnJwEtPxe5VR8pi8dKTUXpTTTcx4vWfgHsUD4PeUb/3+IfcFZleuVdwxM94rC/hudv1YF3AR3pbHD73yvgoawSQYrVpvxJW"
    "MB4dBeq999L+996SBmHhWw4MkpyRQW0KN6cK5OLO/eZp7yx6iFrQp3eFjhsAR7PcCNm9AE9++WP1zQSjPxQT0UNshO+KCf4zsUf3"
    "aPrVx2eH9KofL+U78iQXaixXJl3ak+1ZNCsXjOvy3iDUyYtarahpDJubsAxo5TV5s8d/UXcl5JcpF7VOrIlUs6f+Au5vujSiD/v2"
    "lQfHGEDtCF8Lp8g9uHiuG/itDlXT38yBVybW1uRCULdUPvpN0RIw56QyrqBCDOoca+ZKvfVW6qgYLX3WZA95VdS72SY2kF7MgJrJ"
    "JzItDL6XQRUEcxH9SHg+YGHs8pVrik9H/RuamNKXz3DddIPikwueN/IxcDhER+NjuOjZ95Lv6MuuzP3GrIiZtMSLHSDKfYz+yvv3"
    "tCP69wD21I/D/s7pyTY5xkH1Zn4ksjZ3oE4STT8bl3myZekrxywaOX3BFm8e36xkqwXnmwAsUsTI9Toqbz+1TsaP9IVVVh4PUc4O"
    "bMDOaflkNDo9GY+fnoytzP2I6nLo0COjUlPiX6TZAWTvG4d87XuBa475H5RSwoE/Mmwq9FdAxO+MZoec8khf6mkyA5IaI1IRP06q"
    "9DpaZVatX0JOyvpmAExI1AGYw72joUdZ4QFlrZ0lygqWS3PITP1zAWZJ8ocIaSqu0SOkbFk/g2dFibmX4j5fO6hSxZTbGbwCqZ4t"
    "g1uVw7PkHZda3ObOzBow8rM0yt52JQ9HZFw/ICluBWh9JpliLo0FAfzcg5yTfulFyUucvfcGGehcJXqJ8Pk2WerHKpJFa2HNFMn6"
    "XHgCDl126C3D0U4sVUO+nfdToV7PoWN+9e6fAUkXn1EdFUZ1T2hxxFhxt7Q/i3M7Ah5BjBwjB/0039pnqzWOlvatOMAat6s1fN++"
    "4yqIbf3UX9o+HKg+FoePEd8WoGDs20dGwZulHfsioHKxWe64wEinU9IxlPJ/vVTle8AKOLmArvbvVYSmUbhtkl9ilUN5wRsv4Vzx"
    "ReSP7eOyo6GHskAxSnwx4QwFSkecQzoc1nNO54sRTAxSPbjecCoNWqSYOPPFYaGFA0i+9sVVroUAC1/64sxs4YbuQSQvzQu4YMSq"
    "YnZfoEMygNtPBJyZHcFoKLLUmuqQnKDRxRRI4eMNLR9swKO6PM71VZE//RWYXwQWQMYS14+MZ4bjufaXOVKlRvbXRnhZaE2O9fEh"
    "X+GQD2FxYCVgY9vM103wwkG8HWAPsXfT/KPNUscCU9uPdA/nigHwltlupJwLlQNn8+U0OnennH6t0q+WLJLrXy7J0E6KdQ0CoyS5"
    "SGEUfQgVrYmJ1gQZrXEzWhMpWpOsE/NOkAABL0bXvDlfe5DcSEKDQcXLcHsOH7iEzRcLSYvI0EZxTU5V6+04xDdP7DRPT+aKSF0T"
    "d3SFpOoS6cCkQF6EwwUxnDrwIUAczuzrVfr0eWmfiTts4GyVPp3bc4PqALN8Lo6w6LlBcg7sz0YZH0jYAexpLHVglAKaBlC5XE+L"
    "4nFfP+9fWuLOWuJdAQW1VOvo67WOLKQjqtoN1rr9eq1bpMCq1sBbv+9i3CShv0IbYUfFa1LX7sOQd45I1u/DWNyskt7VHWi04gDV"
    "gh0YagFcrL9u5AcGtOBteUVbciq3ZLh+SyIyeWpXXchNNeNNxciv/cLpKNjDbX4v39pSWuDOCD2SVKm2hw7t/OWTsQMrQk8xH+aw"
    "swHn5BmFcaM42nCJ2M0+cO6pKspPCJmfa7lT4Lqe4tUk97YDB7e+J2sBPnoYHGZPRnH+dUi1QBa91rKfFaTlyY0XRzEcZjdLq9iU"
    "+RPmtK6BfCH0gS6MF7f/GX7IngC8tIbgcBt4AJR1ykemlUXO/OKoInniqijrPOvmkSHLcZrA4SX25FFMwzeg8vw/DJXS5DE6q2A2"
    "1ZOZI8w8e1qA2WS8WEBapl5JaSgTXg/HiZg/DseJgqOXdf1X4HiRh6M7m03vngPOHWQk3fRRU9Td1GPcsLV3s406WuyzAXvWCouM"
    "8sEgcDQP9CjvEHix1peHjRrpSRfHMNRKXCtZ/TWlHylOzi/FyhurlM/yLtE6qgGsdBY5I9PXBdIZbJP7nMUi2A5lkDXW4ETvGGxJ"
    "I9Y9W34Fdfk1Mca0b+I/1KsjR5xUnAcu5VzjXf5qpbrNY9JXO+KWAe1v5higVvuTHawPJE/cQS6YvOGM10Vh1jdaYIfMpGiO6GiK"
    "YQsSVAaVdk57BAPyFG4/QVc0O5D9pCSPUwkg7dsjKU9kNFat/IySKCjuLfc3749wdsu9Haq272TPGRTBXoup+PD7v7Kq/4FlFPgm"
    "sR2EJPBMciRPbkqD1s6tfj7pAJIsYl6Btj2ADd7wry2Lv7osF3JZYOE9y1ga2mErzaB4haLbVGk7fp77zHJUA0950UX/KiKv6EYK"
    "yso2kSKDSNzkYmXyb6MCBSuptHqBNcLE5G0PC8Yd/G7s2ob+zijg0NPKWrmE2sfR1N++cWMAKA2vFEZp6QKdF8K/cYkkvWxxaAnn"
    "7Ozj2w+HR+9e/3z4/OxMPSK5dDChWzHpuAU7yXsFj9CeW4ppgeI2tGEyhgznV0B8+qzLH1rsTx5f0A1zoefCKyOJF1N8ZZQVoyy2"
    "V6EmHknRGqDmTeaN1qVvgKKBE0nqlfkK3I6kLfBkL5FGXlP7gfbEhAA05Wbvg3yIFbiMKevmQgbwQSwWn9t15Acq9TrsiCq78R94"
    "e8nW1ny/NshOVsNs1mNJfKs2nFcqffqsD+fVKn+2oCY78ruQ3hHKF7YH1LdSQSMvfLKuLRYX6wc81QPGfmca/3h8Oo7Ktc64qMDw"
    "q7mIQGn2aC0Nhfh1WnYVmYrvWdHhDK/ftHy5lwjXKG5WnekbEXkXyv1IH6x1rS5AXCn7HihAMJI+hJLWcmJ72lDZIOlJDguJIyAP"
    "lRTlS1NLJe69stZv2oMgnsyn6K0FZcd+OPFLnp8CMfG9kpsq+ocN4A7O3bjVu5EqQD8T7cNIKucry7BsICIlHsTOKqakkBWEl+QL"
    "R3kFwGzezoaajU7MXoF0VAKdp5AmsYMH9iRZQMK2M/LvZSqZ2KFUQzLbydBczkC+lPdJmyNXm7VpJn0TEyay+GCa1/mZ53/G9lTq"
    "AE2L9teZ8fUUXzWm2nLu90lZww3drJA+VEknwU2NHvP+pTUznp51iLI4m2SBFjK81MN3jK8HduZ+qsBi+WaoAx/tQuWRE9lssa5f"
    "Rldfz1FFifVltoHxIT0yp09/YRHi4SgWvooZsI2Gt/Lh0bWsSRkFDdPc/r7n50c5ZWA8pPTRYDEMkG0rZRi53x8sJxVieIf3+eoh"
    "1MmWvQ0GcHbbgTTlTDFGBunnSy+k2ThTHmfSRw9og1SfkTY+bZSVAiDueOPophqkFpEdlnVteQKHJRkIFxSBhmg/xmmZ8bM+kl1A"
    "JIVSMRntomNRfbmy8kpawYqSlgv9+jRZN+tYW2rmz36zI03xtGmkLqlGK8KR+kTNBbSnTy2BsIXLHsZ9UNOZSKwUAXHCpuIyuyMw"
    "KI5S8GJConQXpJJgPpOVGOK88heGy8FaKZ1MgaGuFZN2RqbkF8jAdeHDmE8xqQy1uCTn6JsgHq1AHDkhgLibozCu8uCbd1u1WEjU"
    "S9kceqIft7G7qemdY82eYIr3QBneD7ZJItTekCfn3PZHE2Yp51JnTcGGKsQEYaXNpFRyMt2SuYESmpfPM474aMQPgvhMiCIQPUDy"
    "5yP5PHzeo4+luCDmygIGppwnG556vMHT3pNvNtbgwvZNHYVMkUfOOcsdpv0sm32VPHLuay1FCYQLS1zwPU7ekzAWeaZWaeftbF1L"
    "BrtT0VZk5AR6X5ceMbQLY4/8sGlVT8a3HVEe2tTaSdnasXKKCTkjb+7RGo7oQlQi/Ytxf1TO+tva2jml0a1/v6cAwcTatdFpQiUV"
    "Zkt6YWGY7jAnfaQIMgGgtpk4zuyX+0H2bZAUmi/8kw6HAZENsaJPziDF+DIopgaO+169hhRELtOlHQwKLkBTFFenIsib+UyUh7wJ"
    "C5spHpn8xnZNVMtEIUVhVYCisdjUrhtqcS5cVvI4gAGjJ1k+sPCh5o2HpuYTP/CHhv7REu2YyWMMhlusEJ+kDr0RQGkMC57F05RJ"
    "Ah2epNkFPIepAelpoqr+BN1LkjZVn9Z0iEF1lrTr5GsvCw0yERXJrrLfywEc7lNS4mFOcg4/6UtocQNOKF5ivMmpLGURxKHHTDDG"
    "GUt6/QXcymwGVBUj1q7SfFwaPk5/ynTR1EkzVSmk5rPp2fdHx88+HB+d/fLq+Pu+k20cRxy8e3v87NXboz5a8aZuECaOePvu+CxL"
    "h7v0gc46fPtcteKHnmzj8KePz15DSf/PuTuV9VUa1D6Uya/e9p0gdMTrw6Ojs+Pvn8HPaWr8PHv3gaudHb/DLOBcXn44fHZ8+EGW"
    "vkzzKfkKl1jhu8PjXw4Poey5n974PvT2HIqfvTpCsp/6rxKdcAajVIlvo1Smf3f44t2HQ07/zofd6MuMZy+gV05/dpH6sWOsgE/+"
    "yp/849w996c7V/505sdJqSoD8T3R/MyF0uRkh6F2LjheLms7gC7QuTBuaEpxhtlFqxjpz1/212T6hTbz3SEno622YUNyGbYVl2PQ"
    "QsahGoMOGbgUNOdM2zC9YBE2+/HM9csuz/1RYWZjdBTi/OMf6rczltq99yuCF/LOG9ohGacDE2SRV1nfhhsNufgkJyYaApbWwbhH"
    "EX/YN3LUcbavpR7Dew84SNQd6suvuuTJ/VFcqYzhPuHnoMtuCPCMBgK1XHFK8CqE2gFeW1OM11dKoxLP0C8Bq1qlbyCYWhV0+2+v"
    "whKRFix67pdUCUHlXQRAibV+k9L1PElLV+5nv+SWVuBZtkrXfnoVeejfgNSlgXFDDxGZcTAAxAAGKh9Kd/3LPJiwNoYFD/3bLOIH"
    "a1oDiIRfhEmC/QBTj0AxmsGQERHG5+YGdNBb+RuDCgTh/2Hv3dbbNpZGwfv1FMhh5Rf3DzE8iBRFL8W/j7ETn2LJOX7ZJkgAIiIS"
    "YADQsiLz+/ZbzDdzt29mP8BczP2sN9lPMlXVB3QDDRCkZEdOZCUSgD5VV1dXV1dXVwEA5zjkCXfw4KzUwJuhrwbiUOKrHxZuusQs"
    "6y3hSlb6iBad5Ov7gPyxKGEzRs+FUbU2Kcg8U/vC2LFNZUAKEeLMkZeOtABiDRYs6k58Qt78Ue758r/v3B6+Ct49boQpPA3etfvv"
    "up0GPN6bOfMFmodRDZ/LQOu3eX+ECkOJ6c5xspMKjKZfKW5ydtLMaY50p8sCOAtx9Fb4r5R8k6KnokM0oZUOBRjl+IcXzDpumFcy"
    "og86ysKjh2QuyxzCPOwVcKjs5BaOPjYfNROgoU92ksOoidfYiIZusVpQ0pfalcmh6A8wlwkF4ZJRGgPmzoLb7CW/ALlP8AgfRCGH"
    "7R0mDcX7IIkx2MAMwYGFdSnBmXFwloezAjguSPNMkesfhjNowWWavVzLfqFlpjtcsdAjdDDYpHutgr5nTR8dGSgZIj1DRBkEJmEe"
    "sdaGF9lanRsKhhNJAUhwoyzwPfNQSDp46YaQ8coHM9p/ibgezGcwzBAv25FlF6sezCj+fHXm7N6WIDuM+72yhUBxfQHP/EGTEgm4"
    "YCbrfAxQHzKohST2IUGGFbcWtPIoOAPbloF6JcFw9DMBstANIe3oXSHf9dzk/pP2kF24CTA6cioeb8uPO4irNHsb1gL+sB4uiG4e"
    "bAI7bbwZ5K21kH+yBeSf1IU8CDWQczSTKfBaGeUoawouJKqva9yEkh6Vok7JEtLtsM3F8lybBSRRyGbx3P5VwZVhwG9j9gxB/zpU"
    "cMfDHYsUrExBJRb8F8WRZEkre5ZWgrYhzf1LHTfvX2ginHpX2sCh3gLZl1xpF77SGviK6r/SLnyld+Er7ALbla0hEunt3yATsu2B"
    "d2bdJ3dIuAPnRzdanjTLk1K4iTTCFzFniGXonxoCONgy/unwfVIKH9u6/gkAGkmfA0X75j8Tpq80mOh+EsZvz8OkiXseqfHtCCTi"
    "gh+SoXDcZnDNYth1lvhosQtOWky7+WpvLXbRXUtu01rlt8U2Om6pU0HmwcU2unDRdoPVvlygD756gzNTr0x8sZiSfAKSR+KLMxHY"
    "fzSLTm5Sduc+kNGH8QI+PxCR37izarWXLBizCJwtaJI2VEHC6uY250KxnrL9ArIKWN7QH/pO8O4dwMeOZYLsbmnAVei/AC7EHaIG"
    "Cxae95iDDl9o8+Ifjv7B9YSqT1DrggJuDc+mXuztDINkhxsKoxr3V9tib4vJbsIC+cFSbG9cYjgcExPZpqSDM51Dif/G0dvdJPgD"
    "JujQYiH0duHTLUpf/UNtgEev27hLv5DN1H+w4v/x69YVkLXWJcony/E8qFuBgiGM5e7EqBACDFEnbmXYcyanJzFaM7FLdUOLjgoW"
    "FNfMmC2YOydQEZ6NKulMgW21rCSaBW4+YTd23GCZQHqWwuMkat9YvFLtkw9bpqEVhICIINU/7/qeA7PJg16nsDc/Scry0UkC4qUq"
    "J3PquQtdnxBYhQwcP4XvaEu368yCk7AsUZ6+5NE2WcYJ1rnA2G5eXEG0IpTdpmMvWuBmiKYWWADEjYmShzPcuJwMTrhxyWiRIg0u"
    "LkP/ObK9of7LUn+EJdLzodU20dZGg60MGbDK4A/A8xuMoAYbS1PdNdcLOsCbRjNXWzXyYCtdZHfs5sFbmBlWdDpzxjZOIyQJSrJ6"
    "rX/aKqE0LgHd7pk3Pg3S3SAMCf1BuMtmvH2JyqJlqlemdHxKEaaHFoZhvgK4E5hZk+mu600idiVKaUrkMc+/SzWLIj/e19nFQKBK"
    "kyKyJ9DpLAi9XX/mvb3q5nb9wJu5ye5ZjB1TiSo/qXNt7s6jP3aXAYw1HeNsOidI0Jk6bnRWjsblbAu2ukWZuRcuN4V/BvshZvyd"
    "558GxleNShaEcGP8ETOGOTxzFolHE52ebhmylK/0qGpEpmwEbOKQFcMWq+J0izIbk1ClqEKLxRlnD4XU6gGZtjcHf9rZokx3izJ7"
    "W5TpbVGmv3mZxeZFKCCnt3m58SyanP6+jNItyrpbsAh3Y+okAmTr/obEmWMgOm1uLHyUTX+xGtAsyla8MkZRmkMHj60m3haS9Mw7"
    "wevlW7FBg7C6MRcO5idbbBvebFHoTeB60ebFJg6stMnm5QI/Rh3VxuW8+bjmDk1fgOkgetNxlKIOTexszITILPj8PHDdmXdl41d/"
    "KBRY587b3bPAxZtS7Vbrn5cAhsdqJ0awNWi5SjaQjqfxpl0XNbbWb6W49JFGC4mshVF6TZZzmKznW1MMSWJB6s1NlbuBM4tOroyr"
    "1NzoKhSSlw3f7gocbrV5N2HbJJj70WSZoJ5/067Dbgv3GjrRrP4xspeoYsXX/8bJVNd6bqPJbC525R33/MrpO/NgBqPrpjv/kZ4v"
    "ohPYn0zPm5jWZGn/0dhchUDbKDEAuaoxrcnS/qNRhJOk6wAk9V0PtVu7Dl1pVRUzYTDnC+Ril714erm3Cyd0rVazk1iek3i4s1VU"
    "D8Dq/Bluh6bA47ywCoKZ57zxtoBA7BG2guG/Tr1zWkqS6v4pAxlHc+UV/53EgbuL9n4zLB1HZ6hI8uMMhFUmdkQ1yraLZeuCK5Gx"
    "McDtSwDcKgUYxljoRe38B+u/rdOCEndiitdd7w3a0uU5zDJBNQrTcxa33KbW5eSUCluTzgmnkUhv8q+FCRSYJWMsi2FAyX9pcdZh"
    "klKQs1QMurq7u3hLyVSRna9IYQ1itm9WClUtu8kUOOhpXl7kcJFGyqQfUidhlhHmWxD6QQgLFXEhRyGDDYsIAhctqoRugqz1zxxd"
    "StE/0+THEcZf22m53omCBaLqdZmyCYDSUO2mur2DOo0VspVP8r9Z34EOkV+DDLQ7d5JTdemVsoRC9phnN0thxI8fm9lHbQpwUUNm"
    "o3d10V1EScCo1g/eeoqUBDKfJg7NPF+XGQvSszpRCzJ1rqMbrb/FglmHCOHUg6a7ZHvb/2igG4QzJ3aTShA2WYCLBbcCwbieGbpX"
    "uZqplGGULytWs6uhKkHC9brE0FW7S5cFa22/K3CWUYoTTqYgGLuyK5sQrLmw1W215gms/ONgsjv2/gi8eKfZPrDbdrPTsduFhbNQ"
    "yyYEay5cD4RqMaSKlEs6Xjn2UgZplbLSBA05d1rNg25jE0GxBAcX5WRyWVgUn+luvVtS7l/plpSr35LytVtSuk9zNMg2hrlk7STc"
    "+umwKg+F9uPWTty7sexyZmxXJ5hmMwulifcXmfsM5pRsJ1SusSqRkxc0vsI4OD1s30r/5YgrMGoka959mfZLKgx8L1ZD9eut9J+d"
    "275ACxqdf9LKHDioPZtzEzEo1Fg1hmt6mNw2RR0l/xDrIo1ifMTGUIXJDJA5rCnCuA77IcX7UpxoSQTPfd2ofCc9nOLllgbIht7t"
    "8haFt3ZbC4+K1zPonEK8n8VBKkOnDj0cFSiSNT/1pYnc4QmCIi9gZVMXoFHmYjpM/3M0ymo4yS5z0cTQAtN4mXMiog/F34p6jxDv"
    "ZImrb2n0Qri+/bUhfRyIiSIut9nMCYLLrnnIK0XiwtOtwhW+//ovpWJ2505czLGkr12LeV+Q3s6Y+x+OkdvMHHfIwn03NB7wWkFj"
    "fnp81f7ii2wCtH+VfbqtfsXBCg+/dZjboVDYM4aKa8UvvvgkbAYJD50lMPJJW78nyc3yY+IYUCmZxd66G+8EDfsV/X6Bv1nUm/Q2"
    "XT5A3knGiW/8w5Z97mv3Lu2xf1jiSWxkv9XMO+0jH+8lSrTck8R95CPf/X3pxefi7vYdGEd2sf2Xzy/G/urw84tvl+gt4ldb+frf"
    "2WfyVPdfMDC/jgxzU+Ke7IKlE7Sdsc+uegHKwy++eOtzy1qOuluAoDNf+huOm8uQrDnRgDP25rCcogUrQ8yZn/Xq+PKDTS6VTnc+"
    "ofhZp3i1LoA/dG/Hdg6/X+40bp8FoRudNd1oQsX4jUFy2yG+2clhlPmAcIYR+kJuBnNy2p9idJyJ4hViYi8P0a99uHRmtnu4VOJ1"
    "L9E5J7vmvjj0syrZ8Lz+/OI///ONvxoNfXuODbj29HBecEcxt0+wfmzbfn14Ukg/sd9gI1E48ezzwzeFdPQajx414iS13x6OFfDQ"
    "pXLajEJO+fa9w6NC6SP0FI+ZeLA4dLDseUWfGeQ7HvOhfS56Tw6LmUIP/SM3yVkhupA/y3LAYnZmHyMSkmhG4qjteIfHhSqO7cg7"
    "PPdtcvx+qJuis5US0r9lF4ou5IgRl771G11xeapYMctVPkJg8Z401U4+cmdK9am4xrk1WZKLKlZLdAiLP/wHtIo+5R30tB1xH58L"
    "oK0ICOHduylQVcRG9d27c3LG43FPYcyImkF+K+a+tVKcaOw6ZuIdTmyMkmKrE9nxmOcKsqxGJ1cXRBLDtzyCxmubGhsuMWStd7u5"
    "M8GIlbw1YHjZNVEXo+PIsN3cEfIT1540bt+e3Dry3707dAERExvYFPrTctGem1WT6KxK8KkSf4rEoVziTej1BljQg5mHSL17/hh9"
    "veBH5kCRf98RDj2Af1I/ebvobps/AoHdi8KQ3KWh3XuGPs8eL2UBHkBDuJUc2YE7nBkw9fZ20px6jouhJhZe6IoKGkP+HU2qQvfe"
    "NJhlafbXWUNjH/GjtBxloEYhXgA4NAjiMQ6Q8J0xQXK9RyMmBwzGYAfowC3SATPbF01gB/ESJyAPhgxdnBhSDgFkdMSR8fRUxa5K"
    "L+jReiW9OM0wxBXU6Xi3Z7ggwnI+w6soF4DNqU3AL2xvNgzIoXxsL6nDhcv1txJcsKktmqI7MGu82zuSovnFisRT6LXdGO7seCrM"
    "Hl+HMNuJxHeDIvLhSLGlKTdSWX2ShpmvTmAQCOrMs8Vlh+HXKOEqV88f1NvDPfgr7eGoz7Sy3/ft57596tt3lCX+t7/ynu7p+9nT"
    "/VZnT/fsw+7pfvtT9nTPinu6Fx9wT/dCkU8fGvd0D9bs6R5me7oHH3xP9+Ca7Oke+/ptRliqhDexVkNQhx973h/eTjmZXsTOmQit"
    "ppdJcXPBeNAT/9C0l3HFtbXRP5qLXXbOvetMJl5Cx8JcqyctQJiibjILFkML3VjvtCz64Ro8eWghbFuENciu/JJXDJoP2fOWJeVK"
    "1OzYxRmDvAxbMvb9bAoLBN15IJNkNOjmCYr5zeof/+BnGQgC7z7vcyVguzHrKGwZQdCaxNFsNnbiJtUNZIA1j1b2Sx+9sP1Bv+/6"
    "BuFlxHalzFm2WZLEGJLkRntlfytci+FdvhHJCU9EjJClb5PDNi8ZvvRtZiHPwkQP//BtXZS4kp3lTqFwRy3cMRbu/GpchtH1ZROI"
    "+LY33FG2PeT3/N27b9zGzn2UpGG2/IIhWShmVxZFGn2kNW7Djhnd1TdsWHp4WG68N0ou0pCLAtRMTrl3dFR0WVToTEvtTMvYmRZh"
    "gt3xlBCnqiPSlDl4x1aZLxj04+7ZJjGFiW/kwQ8XLVM5LmehSz5yuvjBeiFhmfmI3ae0XwOBEMMNCV93HKZdEfAeOBIuHca+3tZ6"
    "O/RWvGdEr8Vecc/X23cu3JbQyUW9QpBFjGT+9WFtzUEebAvySIRR3on5ULx798Rt6NGKUr5N9phOheKXf36BJeSkeZ6fNBgsQwS9"
    "YYEqKICyYU7ubIkxBDOLgiFnIBEv+84Uje+vXVZ/sen7IuzCe2pa1l9smoVyyLerSW+Ftrtq211j292s2xQUksezUZqnJnIBWAiM"
    "HA8sA6IeuXIgsiaIPAUU+fAdV8a1MPzH5ZRQgrWKTchylnFbERr53TtiArC0fOPunGoTis8pXIrsAINzpIbgHLA4xY2KAB13fRVV"
    "FGuiGBkFw29ID576cF4JYvXP9uUEg6fujnf7N1cok1mA6zLiQN10OebCNZgbkYuDXRJOR4S9mGMvzAcvYdOQLVJVOANgtl5oip2o"
    "hj6/ajZYBDYZgmXmqzFY8lzb1IvLS3YC+2zYChGVdOZiWNwrhFi+8LxH4DGGBAP8ykD+VTIKyiP2k7JS3OiROH57xCJj8rEciiiG"
    "JIAKsSg4BC5yJ78sC77D5AjBefCU5ghByUcpDDDQd2HWpBgxAHWDawI13cWtLxJaxAnNMYVgCpVQHTzSpQFzUhhE8Jk8iJsSPvPZ"
    "xoR7ocS1UPF8+72/o3rlFKdNbFv/iXjNq7lHi13cG4eJt8vcdotZKwvkVOBu8GaEwasC9zBfFj2oIIDI7Y+hi4cjGPghmpcGzuyW"
    "3FUyW75xlGJc6XYfNo1s50ePf9CF0bfDTntvf2/Q7e/t38ptVGmfOroldttOmjqT6RFd9N25mGM8+dFkFiWeO1rBEDbppvij46dP"
    "Dkf/Atgt2FfC8Dkz2Op/ahG4h5+KrXG7tXhrtfcADMUk67ODg/a4Pb7FrBU/833/FrkZ6LdaVru7ePtlu9mxWAzu3WVg4/XtGeyS"
    "6YOdAJntJl4c+Ld05wbYV+WGcsvaw6Y78Cs+GTs7LZt+mp3GrU+/En5sUWnivXpsPWFI/9eX0J+vRrYcqXHknmsnAh4PLv/IP/xh"
    "stPIaOVVPd3xq7+S7viVbv/zw19ZV/z1+9EV/1BHV/zth9UV//Cn6Iq/LeqKf/+AuuLfFV3xN0Zd8as1uuJvMl3xqw+uK3715+qK"
    "Eaaf/MNRp9Xp77bbu+3OyP7RP7yAUV/MyOs4+fih4MrA6HE62Hyh4y/kvFNzCDw6omfrjLzwS3e7o8xdv+rPdvQsSq3Myb90Gjt6"
    "AE+8Du6AdSRc9md+Tam0Jz8/ZN6h4avFHkfoOnP0xEsSK5064Yg8XWbvVhSz0lYajdBF5ehrWuJjnhudSmqf9ALcIeQIvfpZQTJS"
    "nDCKbxjzb6Q6P5QJY+7HP/NBKJPoet+I+a4DvOGfEQv2OhzdwT8je44em++ATDF6ik8WPIqP4bn8GEJOWNAxyASUdF0Ln2DHSQew"
    "7OtLeuYJqJpfAPA/eQnmosvFgEwAZRqBHAGw0N+RvVyQ0nf0iv5COvpoAWDu0V8W2wmPil0cdv44snE5RgIcvWAPI3Qo7R0Ff3hI"
    "58nwl9FdEFq/xV9P8dfX+OsYf73AXw/w18/466e7o18BcefMm98voyOQTpxzLBbxh+Oll7CnHzw3FM/H02XMHx/GAXs4wouM+JjV"
    "eDSN4pRVy+pkFbLKWDWsBlZcKfk0CKkcFaNSVIjKUBEqAQVg45NOBfjfoElTTFB545g/PkX3OPD3DkzuGb3j12+WGDoL/iARjO4s"
    "T5YobY6OYNjwDjnW/xykAvb0DEaWf7zvTdij2rTo5zdI69g2a5Y1qjbJWmQNstZYO6wNVj3UzKjkJ0a19Gz9RLTLEp5iwzKF3kQS"
    "Ur5MwZcRRkx+A9U6KMXC5vpNEC0Ti32AqQ4ytUh8Bs8yAUsxAGQZBgKWYAmUn33E3BwqmZ3Dhfl5EhXgn7HEo2ip1o+vLD9LoOzs"
    "I9UfhMtU7QP7wFvgiawJnoCljjzgia5Sin1gpUQilRIJznw4cuZQGv4u4G8aAVEOR8cRkfmZ550+8hyKFfPDKU68OEnvO+fP/R8g"
    "ZQj7qWl0Rn0kXkSYAu6PzOkh7A0d4APz+Zeu++U5VeacQjXwe0SWOkto8in9HcG+LI5wih/RXwDHSZIzkPdh7Z8ja3lANw1gyeLf"
    "gbvD93PGrp8CY0YvacjAYy/B6LcsYCrUS+6iZIaL1krmcGLPct44wQzlhBGP1AMru5YZL60nFkvzRKtHhazQsMhDRWRGrfUieMjI"
    "gHwTT28VP4uVKZ8OlWCyNaHPvCE1VfbJ4iGwYZBhHR5egOTvPcH9CgxvjHzJh/VPfHmIz9AkrM78C66RR7LjuFIPR20L/7I3WMFo"
    "/V7Rt0RgkFYX+FVAHVr3GDKIz5iFtp24dNFqseBEnJEzo2NGwfDsvAlO2NWY0TP5DHDQ0edxtAByokcLnoHkgK3Rx6e4cslPr8SX"
    "V/zD/egs5J/wkX28yzbb7DN7ETUeg5TvpTwpjSz2LlKPYEZPvCyVvbPUOwilVhzRkquCMmm18EyipgUMPB+yF/BoXeCHFZ+rL7LE"
    "h/hu4QeQZxwt6YkjUxDBSgrxCpaCw6GkSBbDUvHq9AsvVjK8hC8W+itbUIbflvPFcYTp90Gehy17yPN9AwnYHwJepKn5H6MsacpM"
    "CYLuoDlqU6FZQVoy6ZVCa+wqvEx6QK9EhPzSuUy6xz/gLAB2J3hOuAT6gncuM1r4ZWRPA9dTczyCdz0Hj0UyEqIme3++YLt/8d0S"
    "H0SGe7R3B3E3lVmyT9AdN8j6+QBeAFjnjYdPACZejGIfmcjFPjOxiyegj47vAw9qeAJPFj6CJAviDvv4NTzxj8kswAX0CP/wN7Y3"
    "QIaQvQEJ/hFF88fkwHL0Mzxa9Mw/h+JbyD48X6b8y3McVHa/9iXptaBP+GK9ZEEOWdITvLEqUvCFdYHTCQvuZmFXRisRgYTE26eR"
    "y0O/JcASkZ388rnbVEKK2fAqAobhsxpADN9l1DB6ochgIht7+9WmrWkwoZpNOfBNRgrTXtQoYJigRgjLv6t5f6U1lxrkIcHs7BGj"
    "g8lXFhRMvlIosF9X9h8U1nKI+j9nNmy3Wy2b36sbtr2uTf738CGNolkaLCjHiseg57pVmG6oDXRRApDHCPQirfgXqUQ9YOjEO2Lr"
    "aIJbdvqAe314a6/sSbIYXjBDXhE0yP7Z54oqVRX3naaH4rcJbqVNvuH84otHk50L7nF6KD+vGvaryU4WEO8iBs7gcJHyJ3/VwEPu"
    "ULtqIWxNvSZpE23+9927HT0A9C9czfgrnpw052xpxljPqGBurEScrwumsxi+oqsXb1DFGUgrVVIYZIf8/PCeYhTt7ATq+b90AR4I"
    "TQJqrUbCWjvLOGr82mjk9QOfMmC/X3q/WqMsq5U6px5udrlqwIp8a4S76sciy05jxK57jv5LNPXlBHamX2aVND9t3Iqz9lWgKTwm"
    "Rb5tMv3tyyhKv/jiE/XV3B2WjkEZsT+V3cmqKu/PkcxT2iGlReqRDCIqix4qvcx8qWfp/ACHLtiwQW+yc5lMWdf8XDR6GEOuRRyh"
    "c6mdn32MsatU/+6dhxGo0wVh0GYRrj73KYitjOAHOS4SVzijtz/3jTeHhIbqdnMHLcOpEiUG3kKfVezKjnr/IzhULUFs5xCdwsdv"
    "YHrdvp24doTJ7MTh3btHvhpcnZ2ycFTwOmT4Y6CCwOAFfzShYz95vIKXxpr64SNH87c8uq0dNN69w4Cjh2FTaroArBDAnDthGkwA"
    "ppCPhD3B73TWNTvkbGcHL8wwIKWR+g5Of2BNOc/5Hr/fI7EzjFe3vmXmOA5Zv9hfCxOwkQRmV0QcTaRxkj1rNGxeMMoXFHCvKZfk"
    "y/FDwMpShO+dQhl2RogZ7Ql3+5938C9HZrW65TRheEdsVZhMnRBX+6JNBxAGHk++exf5jaYx1AJRZGVlQJqfyDsHn+zESiAEL0X/"
    "WCcUZ3X9fBM5qJ3DVLlRI1j1BC8sCUqw9TtNUdObYyhpzssFmBehd/Y9C7xoRzOXPaZ42KxderJdz1swm7QZNmIIsyHAY6rVVXXz"
    "XP+6PRTLNVAQkjQgYrkuvntH5EFTEW/2yUJCLnj3DsZVvbGRg14faSPwcRnwbQDeXQO8gEODH5bWTyiaj9rDL75ASHPgSfGmEsKw"
    "Ar236HJqEyQN7dpQOaSEMU6FPvBTIO4U5aPP/Vu+CNdn86eZfFrKJ5ep6sPF4QWF6ISdt04/JDudz3Z+9OmgZmXHi0MRbvfwqywY"
    "rx1AFbgEohZB+EO5z92hgNhvcJKyAq4BWyoQxi/Ywe0PZOM8QtPs9uKt1RrZ7DuFZIY6JuwyU5N9Zb5ssJIp0z9dTHg+lNmbc4xR"
    "LvLYUxRV76npIoW506hIelRaVJxpj9rNdqcXo1IHj61/YObko35L9uAlO5EeyQ+iq/W6aCtn5Uoe+VF08O7abKxLdfM9qlcp+Sl8"
    "iZi4YGbqowv61KRwpPRpNeKGFVoSfVrRhpp6rySJnke+j55oR2iKj7trOsrXK6FvSAdpdHIy8x4DjB+cFlZMmQLEHy3uakOeH1Jm"
    "nLAqEMKKVC44FVB1VLMOPpyGIlghEiMegiCsOe+L6CsNoeYV52fglZHlpHLewDznM6f4gJtyR/IUrSU0KmqSk2K9MeHA7m5JZung"
    "TqfeYFZRhqWaShQnR7EYkZqp8EOk3zWFGY1rhfVRUfGgDwzjBmWZOVR6EWqttAiHRS/CowaUFuLp+WKTYk6RJEbIUJkcPElFWRQN"
    "Q3YlNQ/vi8qCAmhTBQr7kfkF+xFU/WMODva1+TbL8ZM5x/kqv1oYBljOfCPPzQ1XCfs15SpyYlOuPFMuycaSS/Bl5twmkUEpVCI9"
    "CP2Tzh741ybT5FZNoHzOHHfTB8OcWQ7IxFxngXRy6RkOUDc5vJC88QLfBXFABSfOQnyER+o9C+zA1kKNl1AulmziIkLFXVpGZDAX"
    "e1jZnixraFjgSM2v8Z97hgysHolHXr0pp2w6n/lhWd05YAsLlJY5G4scZaiZivM0Ewhz3YK1koUP4Nn4Ul3IJNZq9u1rijelU7xa"
    "hOJRrUc7y5YhvwRKlk2H1YwdljPDUUmPlApFv1x+oiM5WafJhOlknn0iicCeZeyuy75czYqYyyzEqnq5L8m0r1hQvljDiA3cV6Ul"
    "ZtnvOvHpzkWyjH1YBJukyLfk6wBeG4Ydh6loRy+6z4oWdyGmsl29bJ+V5SgwFejrBboKnPfKS+3rpToqiBXFBnqxNhUDgXoaLIQ0"
    "LUlCo4NmMpfi1lbYUzllDcgYXJoRwMUaBocRYKXorc5Am1+V5m/ZHG/Tu3k/YJb+RHLJLCrb8WicKr+rESxqZQe0CUwy2Fb2CWec"
    "5o2Nyi/lnrPV3O+ZGY9ERDePCM67NACaPQ2EbE/L9zlvZ7L2Pa32vVztnULdnZKaeZMYZzbbRFVR5dzVd2atZi/XuMCGNgb7qOSY"
    "ByHfOYruiw7IrrsIQMLr4d+Qv6vV97kSRa2uk6+vo4yIWniwXyy8ny8shhMRniferKCB1Fc2aoMxwoW+8vKvBerOvocguyaKniAh"
    "s6pCTfX57qYMEJpckmeE8gZPYs8Lmz1Wmr3srW1MyXzQYw0FoR9VdOv0XLSBjzVbwKyifjw9La8/ilHrKprgbzVb4blFQy6+xeVN"
    "xSAy8nbwsWYjmFW0IAhjPRVgiRw7X480pWwDOcwEmIA8VcpxAjzM8kjp8xbYQof0bHPgPfgwB6D6+ADTbTTAB5g6I7xEQ2uKFzsz"
    "d3jRaw1Hn3kT3/V7IxuoFt7ctu948NahN2ff77rQQJfe+p63P94f2Xv01t1zuwcHI7tHb+3W+GDQHtl9emv1Dvp9SNtnb3v7gx6U"
    "G7C3fs/f64/sA/6253XH8EawtDqdSadDfBHokwPotwDAPQngxJ94+wLA8djfzwAc9D1AnwBwz3G9QUsACDX3ep4AsN13unuOALDd"
    "G7S6rgCw3e/3unsCwPZer9txJYC9jtfu065v7gn49n0PIWLwATonk7GAzz3wDw5cAd/Y8zv9PQGf0/X63Z6Ab7A3mUDNHL5+z+m2"
    "XAHfnrs/afkCvq7f76BdPoOvC8C29wR8bafjtXojDBovxteHRv2OAA9A7XgdAZ7vTZyJI8DzJ07P6Qnw/MF+e78twPP8PfgnwHMn"
    "nX6nL8AbH7Qn7YkAj90JE+Dt+223LdG312s5LQf3RDRvBYS+v482WBxC33PdXgahu+9kELpjZ18i0B8fdLoTAaF/sN/NEOg5MKYT"
    "AeGks9duZRDC2GcI3J90XHpjEAIyW/sAoUN2TxLAMRpDCxT63YmkQN/1+gMFhS7MiwzAsd/ZkwD2DrzWWKLwYH+/laEQqKx1IAHs"
    "QHlPAjjo9nD0BQrbTqsLAJ57M/QXIwd54g0UCA8m3QyFfkuB0PVgPkoIHaA6SYOeM+62BgLCiTNwWnsCQqfd77TkJB709lwFwnbX"
    "V1DYgXZxjqSeM1PnsCPgm0z8sd8W8B0c+H1vT8DX8zzHlUPccd29sS+ZzN544MghbrkHe4OBZDL+fr/vyTnc7nm9AzmHu3seznY+"
    "h/dgPuDR9+TcCTMm6Pm+hM/3Hd+TTLDnd/2JZIL73sA/kPB13K7nCfha/XHflZOkNYCZ0JHweft7By0JH/Ci/Z6ED5hgvyvhG3S7"
    "MNVg/T89z9B3kIHntWBGS/DGjtf3JYvZd10ClvPowdj1BxI8mBTegQSvAyxnX4LX7R84bcmj93sHAwlea7LnIGoFeB1/7wC3n3gq"
    "ytHn+/0MPnfsKegbw6TFNwbfQXfS8+UE6bcAuY6ArzuGquXwdnr9Lk46zqLdPc8dSPR5ey3Hl+jzus5ADm97v9Pr7ZFU4wYnkYAQ"
    "uaCCQW8f3xiEk323k0Ho9MZ7GQYH7cEkw2C/2+/7cpXbg3UM10rOpLvdAfJSzqT3uy2nK5l0u+Ph6sgh9NrjvTFA+CaIZiD28zFG"
    "MssgdL2DDIeu6/YzCCd7YwWHzv5gnOFwMO5NMhzuT7qOJ5eRvtsZuJLJ9Mad9liuw3uTtnvQExDCIgfLNErPyxjtDjiEDsAoIfS7"
    "MBEkDr0Dl9IYhO4AcOgJCCetAWGUQegMej1/X0B40O12PbkQ73uwTMtJ3AcInYGAsDdoTwb7AsLuuLXfx1H2l5NpgkbwDESQFBQQ"
    "HRVEv+e2MiT6LWecDbM32D/wpTADjAUkCckHW52+25V8sNOeOHItHvTbBwNJiPuttrMvkbgH3HMP+cwCAxlJ+Dp+xqdBkvEzPj0G"
    "JjSQ8B04g4wP+nv7HRwszqcne4MDOZHdcWd/X07ksdce9KQsc+C293E9YvANuu3BnuQzUNd+B1EYo22+XOnairDge8CYFGHBRTyI"
    "dcTZQzyIlW6/PZDriL/X9TNZy2vD5B0o8NGizeGDdaMr+fRg0O525RDvTVq9NjKaBEN4CQAHQIUTCWAbKPJA0iBMMl8Kg5Ox2/Pa"
    "AsCDPQfYi5zHeINeLsV7+71eJq0C8wXunHGazkFXSjMtH7hLtpB0Wv32PkmrjuTUBwBfJip0gRwlAj3g+cjR+Bxpuz13LOGbOF1H"
    "LnT98X4HRVcO3xjgkwTY3Qf4JKeG0ToglPFlrz3oSAS2uq39NkrTfwThJJvDTrYQA3R7vpS1YLD3UJDl8O3Bz0BymTb8SC6DkuG+"
    "I+DrdeBHcuoudrov4OvsdxjGGHzATtuZtH8AP8gHQ28Jm6qZGcQe/igo7CHLVUBU5Gn8kSB28UcDUa7Fey38kSD2mTDLQaS+SRAd"
    "LrAmKW62FAAPNAD3JID7AKAUZlxgHK6kQVikOgdSWNgH+bo/kQDuw57DkwDu7bWySdI5ANizDcmkfaAAOAEAD3CrKGwIzYY8GHTQ"
    "pMhm5hlMc03xNk26EF1T3VEtOsiycyUPgJ9zf4uoFWIKL1VVwwK7fL1M6ZoE1SPVM9ibC74zhT36iqNXfkKlCkey/Nahb13tW5e+"
    "7Wnf9uhbr6U3gd/62rc+fdvXvu3Tt4H2bUDfDrRvB+yb1o0D6odh0y9Qy3UR4lXqI5iOoagrRv4M/1RNQbWyXNTc1xvqrlGWi3z7"
    "erEOV0zhUclDPCmRGukfFTVjdlzeUg6ETDo/tbBQIqqlu/tGpWFmtqVWMDA03xdax/Uq1OLUaMmJQUQuxlEJQ5XNiVZhRtS3plt7"
    "jmNQDRltZjY4iijYzpjK9kxqzBIjmg3LP6xzjGIsr50D1D9+Kp4jmsru6WV7ysGNfqqY540mk5q84nEvUzx21yoe94uHQXkrGzPK"
    "tGKcoRRNbuqXLTW+yXevX9Cr+rPIYde2Nm41K/qw5NSshLOxAdFquLPuSHAdCNzJ0IZGR7j4iSJq1RmnQIPZz1rwz7a0RzSiRXdH"
    "LebwqD2wLfy/04XEZqvXqHmaVseOMGe80mLHNFZLnN+Q9Qot1MJYV8nL7P6U/BY/shMWLvm8com4onNW80GL0UxmCsWpirq2MVmB"
    "CoMYzTxSs4ShFGawV2YCk7VQafeSB0SlL2kvuyEz23QyrK6K4ozLYitRu17rnFizqSkls6JVtzLC2jpeYXa8fhYVzHGr5IzNFvsN"
    "TDbMk2HtcmkWEIwEXjTA1gh8ZWOQz7LtRzcp7bvm1m2vYet+3voNBR4Vatw4Zo4CLmqzspWN/gkuxZ2oruykfWtWVc+gpvI8eTMe"
    "ZLCU1zN8SK6y3ljHXIyZI1zI4OG0kNHt8IsrWxhL+BQeyo/xyjS7jf6nsx4BzmPFtCTbCl3rYVwpdsCM+9dhn5nshF4h+/A/3jAR"
    "HMPi/zXbDRSkUIjCbLsdY5btmPEVctSVvYgWiITNbHwEjf3FcMEcFFRj4u1Mv7/VyWOig35KOz3saK8UFwN0KIoZd/vXFRnqynal"
    "44yaQgbA8IJr/H2fFM85oFHpzrfgqD9uMr0DKeWK+fgSRRmZSSVT1RVzdpSc3Gaza87ZVXLyDfOeOeeekpPzpF6rpD9qhyhn35yz"
    "r+TkOoR9c859JScf04E550DJyVfxA3POAyUnJ68D8wgdKEMkjJTklqHcSinTQEJporrdefB2JwitBIgmp5O01djr1mDvn43GGrFH"
    "lGZ0sVn9+/1/NhqValOGcSLuTq9ni/9h3WtULGKi9KCqNFotvE0rJSCTamadsbLBttemtX7jxZZaerqmaIlBYSZEoLgceo+4gBKi"
    "R7cZkzceOvMA/UoG4dSL0X2QKsmoGRXFPpqrzsrMVUssgqHIUhbJOHqFPbK6AdcE8E0uLjPRf6tbpjUtndmFn4x/o/vnObv7o0vX"
    "hTwk0BrhMObMXbBhcqIxpxAWr+k9BpPsnu8H5SkX4yuyy0164gGDIU9ctUYASrhlNF1xV4Qo1HP1W72dbAcqiPYqrh0iuM/D2fkP"
    "xfs3Cm7US49zTRljhgEyrQdDyWSCxHRsoxafndQABDKtB0TJZACE3zYyUBhwVzR9cILEc4+kgNVFybBMeupIAUvRzqrS1V5DqG97"
    "5gydxhVcJqqaaXgpyD3x1EPXre5o1jSbL3ovEDlMagdjRpaUY7JlxyyG22CVDRpz5lpcZ/qvc+LSXLpmpTSbMvpl5+z6QeIV3Dz4"
    "k258rd0PVUG73V7KMOx/kRtqBsKpD2ieora571FNRKfyIA4fu7WI51TaF+BjZx3RVEBVVaYUrKpCRbgmVbYY8qpLGUkY85YRgjHz"
    "muE3IqfASLa/T1Q5+ixnXy1WiwJY1n213DoqWAdhdbkKEKsLmmCsogj1etV6mtByr6cKLXs1XZSjK08b21/RqiQNnrWvFaxFHDzv"
    "vlZyHXmsh3NNySpA1xQ1QlpFJNrdtfVUomdfTyZ6/mo6qcJbnlIwJFKFXokMxqVhG3urQyk8a18rWItSeN59reQ6SlkP55qSVYCu"
    "KWqEtIpSeM66lKJnX08pev5qSqnCW55StruNWUklOUOjWvSBGfezMusoowqqqjKlYFUVKsJVRQfZRdT1RKDkXU8BSubq4TcjJz/w"
    "l7skW2u7cmAUkuttVwZGuXztdqUc1rUlq4BdV9gM7WY3idduVUxl1m5UTIXqbVNMqMwTkVlxpHvWWaI/WLzpKtUV1WtM3UMPthXX"
    "jyUO2LHEmrWo9rmHqQl+slK+aCl22EpVuYPEnD5BUyBMa9vtFs5HWs3WXmNDmxVDJe1+49JnpRvYrck9T40dTClZZJLzFiTBCpcT"
    "RFnl64gh24zISsqxVLoREMqAtdv7UuSIDecWqMGi5YgxV7wOLWLPziuoIBzTnllshOpsakoxosjPWyCFly7HS2n161CjbE2yasoR"
    "VLEpELuAOhJ9ObPNhMdtOC0rXcFoy6pfy2UzuTyrphxNFRJxJgKvFWpLsZTdHNgYRVi0HD/mitchR0iqvIJytBglRVU0nG59hWQr"
    "q8n9mlLevtEwbjNZZoU3LoLw2vaxs6n+22DysBKWEn8p0etqZairHNS/oejzd5Bj/k6Cyd9Pxvi7iAsfz/r/US3kG6/IM/I0Mqmy"
    "nigzrSizXxC2UL7Zp7/ROm+9CXeZN9HM1BmtaLpmK5qGekmyxBSa7ny756ppoXYRSDqznDj8sqL+OQ1S9HujXjo3hAphRkTJcsyz"
    "17rLYY46Un7ZDYhwqxgt8lIa75m4C49+kSZoB/dEvzHVNmBH5i3xJyus2Wp7gf0oHSmblVG1eILZ1KTCHiqbcfObKBo3UTRuomjc"
    "RNEwW2h+eCvfP8OgN3fzPH8SZLIFLzstKo1XYBh2zRD8bx2vxJ5H42DmYRBhDFCd8/BwE8PkGscw0W+bqDm1myalvS+9ZSJvGK/M"
    "fhtKupmfr1cUX4XijOrR48pm8sqe1vOqT7f8z9Y4s7dryWWTqTc5zRF8wf08y/Oopjn9hxL1/jSBKy8zcRRW3g3QcFjjigDP/3C9"
    "cyee877Aek2otxQQK8Wsa7qB2l6CEXNMn2CF4B1l8Sn0iCEFzwcmKZuP5tqbGio9rc28ieiO3U60yBysq4l+ofKkhFO1ya9/Lb97"
    "W96StK88wIXp+uv2kXRg0OcUDuesIu5HIZLMhvChC/05jP3jQj3XYQ5Wbyg27emWzlMyMWBlv94ujHDsvQm8s3XT/KMP1SUDJhfE"
    "c+4AJOPwJbsBkU9NrjFTc8Nd11PFgXnaTZ3QVdWcGRVhF99srCFeF6a2nlJRTvxB5u/T4K2OORO1zMLb1kCiinSxTE0ttS6h9K1a"
    "wDZW/Rjc/EnPqhRfTEnqCLdZpTp63JFHaQ657we3K/t8U68CkkbXg8B5OvMIlum5Reyv/c26soXuu1Pue7kyvhl3YrYuXrbBTRZg"
    "dIwh4/OByApaBfLFk424fpTAxbO5iEpXdphzVc64VvZbM2spMMf1Khidjxa0svlsa3Q0udrkWK9n8yfcCTa6IRrZThxHZ8/58Gax"
    "0iTaM6VAvsKc4qZtEH5yWq6SLmbT2uSmAE/kStveJuXD0s/RVS9Nl4yGWKAPxRGFJJFNBKm8Uk+pz6jfy6fz0MTMO0pRqZf3k2HQ"
    "rxmOtPKl+MV7o1oun9eonDKDYT7BLmm8qGbLZyxVteUzvifHL5U9NqjkqrtNBXJ9r+Mq5kP5ZGHuC4cXRi2zwbmhWitPVgE30ZOW"
    "bR2Wtcw1Ea2V0XGteZ2pJ0+WOJg0NcgwqsduNo2Wnr/OgBlKcASPS2a4XmLdHNdzZ/LevcXh6B8W/JsFzcWus0yjSTRfzLzU22Wq"
    "X5tS3eANJE+cZAJiPtMw8/RdjlY7qwUZ3Dh6q1VACfPlLA200kpi2XdTbQycNPa83TByPQMMrpPCz3jm7frBDFZZzJIALw9ELjWP"
    "9rKboh2L9ZWVxjIntiRzypdCTgYW4nkXJ6AOFoc58GLPrcxCn96mlXkwcezEFeknTmUFtD2mHGznVp2nWEs61XAmKvFmMyU9w5Qh"
    "Hb7oaMcvhEz8NTXgXpRRBgC/fJXGX6VT64IKUN1yyR5aeLntFqWs/jGyz7ZQmpRv3o0MpaCmy/bGm4pCEjebCUPcE1OL22y1ip5M"
    "mdt40osadtFNRUWq2SrJ7eZK9OkejGedfhXdFolsBpMV44nl+0CXZp6nA1R2ApmvokR019D8ITRku201RpD5zOAyww3tLefhcWaj"
    "p7laruE2OcbImR+CUEriDlwhDRTDCFybEU7jYLFpmBnhwxTXMj6f602rK+cq2YCuu4/b1u/jHgiPTRXbVy5N1SBVti2vy9ouyYPe"
    "A2tmc/UhVy5sM1mFYuKvtGChMdKLKAjTUnNtgbmXHuIhM8CV9ceU8LhgoUszs/wiUxSnj9epDssiPZgUjIoxyCxysLeP8+pF4rfH"
    "0cnJzLu7TNPIZFBfh7M+Ki1UHp2lrndXrY0yS4C8blhTEPRa/7y+509s2zG8CEL0mPC1KidwHdSR8MH/F7Bx4wkvpHf996M13lAr"
    "vE7JvF5rXFsPnDGJJR2G1NI8ZHvSJ5vZCKpFb2wCr94mcGMd0tUZEdLR9UkQYuvH0aK2NFaylCq13Y1gJZhfvsJJAl0o6FB2MRYR"
    "fODzhF6VPfnu7uItfdtVWIOVj0mkey7pNWwtMFG30ZBb+ZV9nDupvGeIFqn3IT8MmqCx0T69Wp6pdcpeW+jJw6wGv7oaQCtRpmDI"
    "AEp9SfHqUEbowp8NUFY1pTYbprUTarMuwHR/sJ0lD7NvuabHa9sspNsryjbslHLE2rJEHKnsCmIu1ph++bDO9qn03oNif9kpWFx2"
    "1cC5lzUBzmU2eecuz/2xG3/ZH5XX7mvtBZtbW9Uz9ufi1lOYC9MNN5yXUM8ZAhBueEV28xnOOvqT58R/7X6esHiftbgt26NUcHfX"
    "Of+ebE9hhw8raBbCjy2E9pnnnd53zoshJQ2wV1mwrOPOTuptqQ6pvFJCrjSO/hyVdKmZvAZUuQK73K7bpHIxjc+1XAeuLDjlHFla"
    "JfHOGdMrWnzade0oz4GbVDZxTuzmEi2MSRU4dgxBpbk8XW+zmwZz70UwOfUuV5F+eMaA+1r1nGC/bzs1O41cp0aUj419Yx4YnYXc"
    "rzaqZCagNZRjPGO1QaVmUFqmONNqKpfmWbZsXhWMvXM5y3Rj9Xx89FstoymmYhCpN7Ppd6NF9ZVVrvd5ZT836ymqlIKb7u71SJbT"
    "KA7+gOwY21OwkjY3MVf6K+7oFNGcwQ49TIOJWpEoV5j3xqrk3grqOjVSv1T7WNkvHhFUxZY5G0Z3yjVWwxeOsLqsKTcVGmBnEt1r"
    "vPABtu/8ebzm6tiHkWNcE4ZRmnVl/wa4T6NoRivtB72agysatft4+6iL1X6p/kquGeyy8xbZy+fbel24goOOKzxS2GRN+QDqQpgi"
    "T/+kq2s1VILi4ljxYcMbAt6JB526aqOnS+waa+Ior6muOi0oLPXipL5UicptUK7tfnHtjgGNKq7GnsO4ZuHseHbNbs9sQvYmHb5G"
    "MiahVY0wL+aa1rFlCONX4zwv52pQoFdqPKr9TtTkAurFLz9A+cTk0q9d7EXZ8DBPurl9A9bMzAL0Ti1iIEwvSUi6yNwCChu6sZME"
    "k3wZrOuZM887TLzy/TS2Q1nWOWbc9tb7CzkzTK7DZpGT6jcc9MW2JG/VrZOSIrkLPtyzyJpCwv+IKGWaVjCQCRBixL5XeXfjWSrc"
    "uxW0pgxqVZyW/FrNu9dqjeqFgyFbH1FrGi3QTDUzuUM/rvplbTx9lSI8/8ZPUct6sbK1+styATDhGhdDb5NVhoJanoS0PXFb9Gtl"
    "P8xt6UvXyktKK5vw3dB5I0z96u2vC1JH+R47734Az4Zya5zimUDbIItrt9JGPvbe5McJlcrQAXJub0q5riZ+gPLHxXu/ICNMl/Nx"
    "6AQzYDy15W7dcDXj57KyZ9kAqxfJa5JSfhyuqQRW6wx2Y9/NfZO//k3PUdlxaHE4Cv5qFBfHhZmouEzulU4sXZoo+A823znJ5xW0"
    "Uu7vqYZT3I/H4PaDuxRGVANcj/WxWTPg+UL1OfZefY7dNxokmPMekIv4WZR4Om8xM+/3vrD0KteVj8j6W0GpaYlY2Y9BhEB0oq1Q"
    "bnlQL+aYPesM9nM7kqryBucx0uNMebmcHKMaiUgFull+7SZcZlNWKuEnyDSEeRrYy4SLuybwBtXCh/D+9nzhTIL0HC1chT+4iH3a"
    "SLDKefaQQqCd3a3Wh88YkEQzsVHDOey1/tkQAtOHxJKg7ZZs8wpQItdGkdjLecpTjnbH5UDnNvVNDSlc1O6iqG0wgVPZu9nszRyG"
    "4WjizNhWs7eZ2C37fM9w+tWRx1/2E+kFaL3L1Jfvf5P7J2xYq7Zvdq0d6eX3kiv7j8u5zQtM8j6ated4OBnDG/W2lJKNtTwnEhgc"
    "Xsw8H7qMrhhGdqzKa4RBoVZiHaVcIPzMllD3gPafpoVXiQZaerKa5ek0ypXAYlp2W4pTzOGoaYr0IRaBcoFAh2szaUAVVHBY9PPB"
    "j0dWWNl3gSaFFzVOWj3J31i3GLrXjG23UvjS85m0q0V+WkvtSsjdYPm4qnEo6dmlhuJ7yR6y4zcjL7HK2Fzd/bhuGEO6j2Kgm6C4"
    "t2S64pLdjkn4AN7Ar3yrgkfvnw1z2CmefdMwlVSsUxrMipL3C7X2S6NZUQG+b5cgKUGrYT5Ye/D/AG9SwP8bdAVjc6nR+jbApRK7"
    "rxYy1eh524YaLq93E3yyEn01jt8WGC3rD0cpi5hXG58X595sFp1tgE9ZYFOE8oLlGOUZNkEpL8JxqoC2IVJLO8Wx6sVxFG9EpjJg"
    "XS2kZoHjtotLW1bnJrjE/P0seN0WWDT3Qsz1LJjodndDrj58uvluxyY91qORGnqdhf5b12mDvWoNn8U9w4WR6rCpRb8jW/X4oGfu"
    "8cp+9KHW748pLkDJpsYNkgVZcm1kf7LezgSG4dV1jqR2EwztTwiGdhPL7DrFMoO1YRos6oTk2T5oxKZBEVb2DxtaygPrd+r7KU9g"
    "OnhxbbPvvHrTzu3QzXZKn/n0z6StVBc62PjxZa5lCKbaGmDAVUho8/9Nmdp4IrTdrluDrVMwWpB9iJYp+q5RM/JPlVb5tAln+Z6r"
    "DtQ5rdKKPTn/Og7cYmADdgCqLhoSmlTYFmVKaxjUMyedTNedM1QYon4NNAdcJK/FL12q6q4Ca7S8G7Crwv2DeRD+oN8rv6qIfSv7"
    "263Uo2P9rLmzcRARcc/kRbXQplOGZlW4jeHARgGjzTzuGtzWrzgZulcli5u2H2svifdNd8uBbn6XdJMPZ0wq+839IECd39yE472R"
    "QEtjet3Ik9cpNm4+4rnpgl05CmGy/3Qz2W8m+03s7Rv+chN7u1JGryfrA0P9cRtX99fVnA7m6TJvtF+4mUq+TspMrfMuLOjAdc0l"
    "lQofBSEg3pkhaD/nJd+uYr9SeV2meD8D4TDeya1j1AawfPchFtHx+43G+yHkw/q8d0vt2qYh34s34imRfdbult/Egf8I4sBv54ff"
    "4MT+MnHat40UL2jsa+77q2zMyTfY+qFm2Yx3/4rZ9D6aR4Tl1GMwGTChVCjj1mOAaVgzTjPObyJKZvV+lDoxhl3IGDr7/gARkY/n"
    "+VRE1ltDRDCBP79mN9+12yRCD/c8DiAPt26+dJC7zCGNud6qu+ObHWmOncR7vJVzl/KodDdB+m6C9H3gIH3Sx4rmfPlasItagTT1"
    "CSxDDl6akXzgSH3vMfLeplEA/6ahGVmQSnlLrmh2nIsPcukIKxuZwlxbg3JvfhN99z1H373CFfqvs+hevzi3f8+lYssIuNdjbUE7"
    "kfk13iOVbltuNio3G5W/azTxSy7FH3hzU0seMQRI1+5jfWzS9434/aHE73Cu27Fu4XFxk7Wk3O+y0RljWRBNaVOphdEU3y3VC1t2"
    "XfEou5pYPM7SD23VsJUnukvfzIWA0bUAVaRdgsQKEu10bpVzYyLc3ggUSM837zOUZBXVCAAL7oKU3uVQVPSwwM1q3WGZ+zGc5cF8"
    "MSMPfEbfkjf3R6/k/qhObZXWp1QNMz01G0y3eo2GRn1b9Afj3OsUskEl1aNSLKASWe0yNzdur/zG7QZEyOq5LBWu71MtOiyvZs34"
    "GIpU0mJ5qZvLyu/jsvIGBMkruixF1ulXLZqsqmjdSJkKVdJlVbmbC9+XvvC9ARliLZelweq+1KI+cxWVY1HIXklx5hJ/z5vxG5BH"
    "dSeqyaJef2qRR8mtnb2aQ2AsVkku1SX/fq4FtiAZYzzNmiRT2Z2NKCaHya3QX5taTOUA0HhTfYjqYH/upV6c1DLrtcUuWuyhmRJU"
    "t0agj08BbLS3NBUw+POl78zBq7CQ+lpVqWQGTl8rkFOp44Jnp8s42Ift+/zmnszNPZmbezI392Ru7slcwT2Z8ljta4Nd/4UCod1c"
    "WPibX1goROtac7Wg5iWFmxsIhRsItbzu4FGR58SPa/mL3vgGgjMv+EhTjgH1I0MlqhS3V9nC8qJSzC+xuNjEEKE8PPwVmKVcwpqm"
    "pi3LlqY3RgEhX9B8ZAwTbK7dWlTcHNHOPpolhXhkSVZEhoXYwvIpjFzvyoMiGteKLMz91Rm85hl71sYGcRiVaccDOXD33hhaECX6"
    "F6YMFj/qttqbxP3Z7BZq1d70msZgAnI6JsSZYqlcAWltRC4bBdpNPk6H5ZqNhmoVAp9DmBx4dDG5EjMtYbPR2WOWDRPJgbjqKxPa"
    "0Wam0KgyjKiGmpnWPWVGaUte7WCptYO051nJFQR3q/aAdVUM89JWXeuZZm7vJQf+o5sbVxZJc7KMcVhfgEz30ltEcXqlITVLm/1t"
    "OV8cR9jqY+a5a+681Z3NwURaXq/rJe8r5mw19yoPQrtSVvJHxeBN3VzwJi3IfS5K8noyMQS9rwhda4oGVZl/Zbtzk2e3jbjXwglR"
    "D3+lNr6qseT6oN4iEs+GzN0P4sQY5DONFndr0ubMSUrihGIEl7t1/VRej6tK5osQl98J/q3uJGFQXMWoPHf95r1erPFhMtOBWr3z"
    "tA3ltKYwXq0X6GqNBnURLdZJ44WstXSoudylSlSRr6hvy+fI6L2gaRVZMhFBsuzcLekUlqoTYA8XZ55zWmWu0svMOLgBwNyDLszL"
    "yjjzMQDAS7EXXg7ajMKTapPBnmo8JywHiIaOc1bgl9pgAnEuNtdJzM2SyNWR0Dqa2JDE1pKHDLnZpoBPThxHZ8KJsjR1N6z65SQJ"
    "WJqukdcuNekzqGo56eKsdlKIxsfsSQyXHo0B4VA+gp6dzLVIec9hS1hjulDe47PIYLfcU+yWtdxToP+a04OVeBgtzUZ/Pc3oT1rU"
    "vJZdkVcXOvmrC6bYiWUn/+TsJrfBy8c+5HmKx/Yio663+lDGBH/akX5+8nMUVsaP1HBozKkjked/WASkpOb7Auvv1+9a5UH+xxTt"
    "pNYZeXlUbM0XdbuZn4Kmi0qSQ/ERu7eOuak0szbzRl7v5kWbphPdmAm9Kea3dJuHgL2u6uBCwLza2itzXNiSVGjp3LioKvyeB2yg"
    "n2a7oRgYq/EKifeP/6T77tfW3WfgnTGdV1FHA5LyBGRBFjS1VOEDg3UShApti1nR2Vx9IQJ/1HIsymLB+o7LY1XstZju+u18q8AK"
    "jjRSPCjGYC2N13L9OPVWtuWAtqMbc8cbc8cbc8cbc8cbc8cbc8cbc8cbc8crMXe8sXB8fxaOGxguXgt/zPfKLidVLL3biT1453y+"
    "SYTDa7s/A54aLWvc/TM5OF8Vman0PSPOF/vlp9WlWfPHKnK76CSB65mq2OBguuyE2Z9FIIqEJ3dr7rd59iNxMZGiO3bwWiJqB3Za"
    "Fv58ya4dA3wnjD2YQKekvHfDVubGR7Gh2fDMu+iwp9y+tqhU4ZDdmbBlMI3EfTg7ZuWzWoX9W3d/IwDfyynxVgfrZd7ACgfMeGCG"
    "576VzkgxizDyMlguqHbZJTbT64Z8nQe8rW2uax2W1zJD2HQINvYvuLGZ9Uam3Djoz8PZuTSZ4gNxFqRTNiW4aS+tWjL5zzV/YKSn"
    "zdhskZWzVvaEK8b/LrP2ruOiILEGLdkBgciRRWktw1VWm8bAO/lbOBV8ePxhjJgZJo6WY8mZ7s6iyamyzNr6qmszC5enXAvbVr7l"
    "bdup3ZmzSIKx4m3RkHYcLZ5Kra5oR0m/a0auhL3AWyvMlm647HXnsn8qu3SCcDvhNxMYtykchCCdrytp8hyRnYZsFh8786BRLaiu"
    "7OONXV7WcrhS4pOnjz55nDCY0xDdrTh/04/b9hqlVe6xk7gHWx3TwGfghldpXcPoEOPGm+PaFexqxCGVUOuR+ZBkVa3i4RFZ0deB"
    "uPxeQWH94DswQ0MVlahsQEgXfRV69qY6c2k1e9yVC/7PD1ot/l+zNYBhxoQ2/9+Uqb3XWE+Ehrm0ur5uZ+9f2lJ7ZT/fQhtCCBT2"
    "KaJAh4lJTpB4brbd7fIR2e0YhqSDw0ZMRjKa/JBhBizfM2fo0Bw+/VDXEzZhEdyur94hspjMjAvQ9Se79Kj74z7rX9l3tmK5qi/r"
    "GrzJIJbkDT7kIklrW1sulXwQiBUnqbcoXB/T/RVhluKtj498mPIRnaCPx+zSSoV5TaUFTXEvU+O2C7b7bIkWzHXmtmHMt+cBvLJL"
    "XgatRgmntNz2rw2Mr1uy/TN4ZK+/TPbrLJOdBsc76UoTjfgHwmeAfntII5NLq1jVOaTfm1jZv30A1sGu3jwJwtPasu1HMYepV7ox"
    "9qXnMKv1ZoZ+8Bm6sp9ut3FxxuwoXL/TyKWsKws6KK6v1b+7rKUWycQgABlgr0MKBjupDeirYLK9jR+AapLLLCC1m5mF2xCa/LLL"
    "UZDz63NNbXaBNvQT46tD30oSDzAkuaHM7l8OR7vtvHRtMPZ9dr1nFzR0M7n++pOLkep6BwRrpGigliuUyoQUWHGL/M/nPKQ5tcpc"
    "yJida1QjZCMizNnaXRdaEamK6kuIInj90OpJeaOgLxWSiZ7X5FjZgMWcm/oW+ohfz6hba7n0i225NHPte7Xc+PpyPYLwxSU5wIeY"
    "NteKPlf2Q0le685m93HJMNhw9Lb3M2RUsuYugLydFd0ziUNQTgPlx1aCSNqlIR5EjtLQEQbP4KIMCw0hX7vCA/1low9s6nZ/fRAi"
    "LVLOFhGGSqPQ7Ks3hQU0ldG4LpLTqvHA1E3AwPwcCHwUIFTGwbmI6PSpAgqeYRNAeBEOC38T4Lj4Vh79RAnYsXFok5KwGPvZBXEB"
    "xAbhDQz+9SuI0nSitLIfb3bLqe4doIprNnKFHeRcuRivpVhl91k2ua1yRR6qFnE0X+SvruKIzedO6L70kkUEwh46rmISO50lIZKf"
    "3Fwlu7lKdnOV7OYq2c1Vsqu4SrayX14vN4D1ojpvsjPM3xLbKrT1TVT2m6jsf5afOUMI85y3uY8zlPnGkcxX9h/ArLw3ZJ42D8JH"
    "4oyOoSSL3zRkme4VHGyRgpjkSBEBqjRryxLn05RBjzWV9zWqm+OpyvZO4VziMpy13DRPaAqkkXqVkQwpUo/eywmmwGZNH9KKWc7K"
    "vpt3nrWhE+dLxF+3x7Ol9Nf2UbjFkRQotkg0MPizoWu5nEUBiwqfsxRazpnaqcLch/Ml10udYFaZU4mP/pEGe//bx19no1wRe3Df"
    "EC/yLx60/SYy+gejjo80nPpNtPIsGPd7p5GPOMT53zl2+Huni48s4PhHFNv7vQ/dRxgQ/COJsb126P5+gbkxKFU8d2ZXrhfVjCM0"
    "xJvsKtb7Gq9GXdV98iKyTDvWPF5W9vemEEyb7dULoSq1veJ2p3buOhfL1cXqHDBtebz1l3O8vMkRi3q+u+lRiR68cqPFj89qgwP1"
    "+oVrMSJz0bWMuwTcKqalFeBe6lW7qxprLl+ldBfXdRcjkyf1+l1be2QlFFybTMjrjC9jXKe8J6C6jlcYAKrOVt7lN2lsO4rGtjQT"
    "Xp5O5hXQsQlbkVxzdpm9Aj8qqHvNftpzOOqSjlY3v/sY3d6bgkkpE8tg/F+abJqYpgyPqqvZcnXbchmBmrysAAxlsv4qf9cor5vE"
    "BbX0GhFAqbDfqs/393RY+q2y9eaSATsU1+Vlxz7twpHP2lm4tz3qGFxFxya1sFbBXTfziaIVfbRx0welG6WCEF7S03slRQuFBqY1"
    "pJIoKmOPAOd89SdFGigz7TAHlJPLxMr+QQKcRaJsC3afBaLOc/PSPU8+9GvZcroukpOGPpWrZH3NqGdz80c1ru7XG4zZ2vs6Sqhb"
    "OmDWrlRvEci71Mq9bhipDxK1dl282vqRaq/L3Z2c+SsOxhZ3KLeK1msMul26wMgz2W0G+lE9t0FX1udHVRFhrq033sjBKaieNXe4"
    "+9xgRk5nNNcmnO+hDJ7AWP3Dgn/NxW4ae94uRi+BZ8786NW6oBz4b3d38Za+7SqMyKp2udVr2FognG6jcYsqXP1jRHT0xGATVcog"
    "t3S3XcOufGV/e2MffmMffmMffmMffmMffhNq5OpCjeC6Wh5qZNN4BbDZCxYFR0TFOGAbBWJY2b9vcXO6XFFt3CoW9XgyEMCmW1FE"
    "KfrW8Da7QFB0YpHfcHLDXQ7YPW9W6wzvvW1hLtlrTfTVQaq/36ncoDN8XZc9EWrNZ8t5yD3TFXx41LhcGEPlf+aIv9ehvDbDNI7c"
    "cz656lF4Cd1ptCnRXMaV9Avu8lU4Zq7afygL3xoCYgFL6nKOS07wMvbFpsFDHjtlm3kg4q5cO87MuvbSQ0BjScfS3DymhMehG0zY"
    "7ZAz5ZBkUuYOI4ni9KqUJ3k79fLNeVGJcm1UJBupRXJ6nvdhav+eFCcL5yQIkU6Oo0VNjy0l9KrUdZe5q7lkdQXVDM2qD6yfWdnf"
    "gFyIFMyUSMnp5Vy96PdQOiIc9U/zw+fj31Bqdj0/CL0XsHHw4vTc/tGcEHiJ/bNMOvHS52ehKHPfSyZxsIBxSOzvSvIcnc/H0Syx"
    "P5fpizhKI+CFXnPqJEpO25sWsyx44uPkQbicezEOjJ1OD3fgtx02Dr9KrSC0vNs/zenLhSdzDT9p4cG+H5ws5ftZHKTi+Y0zW3rD"
    "cNUYer+kvx6Gdjg9/HG+s4P1QL0ov++8cWIrxAbSd+8OL1aNz+fNiTOb7WDTX3yRTiFvaKe/hL82bgX+znfzRlYo8q3v5jtpo+FN"
    "S8vEXrqMAfpVY+cCqHDRAEyjQD9fRCGMdDK8cCYTIFrcFwQL21mmESbOvNQbOvD+xkmdeBgt7DGFTUngASOFLIPhDB5jkKsn8XI+"
    "Hi7hjXE9d2FPnNgd+vQ3WgLPGS7wOZkA3TEONJwv2CnXOHo7nC7YJuhkwUhtEUzwft3rhfABQXcf39Arnk8PzxcM6/HcDZxZdDIc"
    "yw+LaLFcDN8umL3F25SKHi1sF7rBhuWMvWBE6uExPXu8wQfwxuq7j09vApwlz+ERI6Ocwt/YOYMvdxa25wa4GP22sGnzhfzqKT7P"
    "vOUCZ9fw2YIFhmD3Q18sQLKZzbw4cIYPxfP58PGCpg9VMXwCL37qsAIv4WWO28c/+IPo+V14D2cwc+Z8f/k9fiBl0/ARPS5TxGUy"
    "fCXeaPL+wN9Y/LGv+VvI/Lp+y1+jdDH8nT+nzkky/Ea84D2wnxb2aRiNhz8u+K3Xnxd0nxpH8LuFPfdOHEL25wsWG8ub018MeJ3i"
    "I4M3xEeQRBggMbwtZ2nAiSKY29l9UarEmdvEUOnidoQvJ04Y/EEZJlOMH5jMhXaBEehknnHu4WzOI8It+QNV6uJLkpxFSKTwDKNP"
    "9S/gmR0ODudzdEtyAtJHgh2YZq/JIghDyHEyt3F3HnGif42vGAdk+AaeggVMoOH5nEc2h5FzhmPxxiB6O+eL8fBIPPGq7sE7kB62"
    "ewaPp5CGn4/nzE4C6BSeFp7nIrEO7+PLLBCFn/NXFPZO58xhM9Ise0yGv83RVxih4Sk9JsNn9Jfmwwt8PBk+hD9ePAckzoaP53QN"
    "kLrwBJ4DL/bYhHyJb3MPqXH4BzxHaNl8Fx9QBOLwfC/ek7MAKHP4CN8jivX+ij2mMPN/mDOtytfsL0fMt+yNTdvf5/abIE6Xzoxh"
    "ETr1zZwtq/cWqwYselNY2Ugo1pa0z/ye3/cHIDowXQV+oX8jdr1x9Fmn1dnvtkc2rWzw3uv02/ttsZTDh8nE7boTducWmr4rvu87"
    "g4MDZyQ9cY0+a7X6+72x/EJSFn3e8/f6INrAOiSyCiC4d6TRZ+O9Trc9EB9E0YHfHre7WPS+yKiXvHvCPrU8b0R3ikjI/mzQ6nVx"
    "a8C/iFx992Ak76YBYOP+uOvIL5TLO/D7UBf6bYpz4sFn7UF70umouOx0OgNEHsel5/ptv5fhctyftCaugstevw/YLuISMDlwBiou"
    "9w/cwWS/gEun4+27Yx2X7XbnoNNVcOn7juPs5XHp+5PepK3hsttr99odDZd7rc4AK8tw6Xcnk/0cLruDjtd2VVzu++7YGeu4bLuQ"
    "bwIy0S1/GVI4NiuAxblxwVblC+nDjXFpFEXog7wpcI9/l71VZXuZnTqoXbzXk8RNXtEKvukV0RcaNPGFXlimp4XvijmjQh9ek9NF"
    "QZ2ierPQNphiW2lXg4b713j+kBZKc4uGwzut0cIxnSH1URXU5oO3DAC9Vxp5F8/TsoEunJtlSYbzMa/JCFVHl37sJYaucMAlEsrO"
    "sWTlKJToRXS7/0ydzxm1eUjWjvNKLrdbVzCP3Ny1jE2Kwz85L50pE/cPPTs+zGaoWrNeI68qLRB7WBzvUCXptOgEJjQ4Dg21CZ0W"
    "b2jEhesYsjORymT49QzOarCfksRUxqKzjIZy14yKKFOBk12GaVm0IVgwFeHkhI3cF48KR25I5km5Jd+05bNt/NpgV2epkGTJtny2"
    "jV8b7Jp+aVe0b6I3QOnLFOUbd1jOqsfGyVvJAQvjr3n7kQ4TJ/q0HJsYQbEdsZSZWhFp2k1CjZesZ2Nb9UmsQKVYvAy+yvryHsZg"
    "S3SrczOhuQkyvZUecj3AjmhGNULMjUVusouN/QW7Hpyq0000yydKumOcG9n0S3eMM45PGUwtTBKVPWAGtkxoOVYrVFJMpofxYiec"
    "2rBWwFY+DSZDRUfNdNkPnXkwO0ef3lPYIqcjG6eccOgjPppP+VvNdi8x6SPJFJIrIJMIlrtSbbFUOHbVgw6+0iliR3Yi36bKs8P3"
    "QTEWHwtwpxkYaKV+FP5lslr6FI/qSnrSKfZkVeYxqM3iYFEVR5OpN/eGfBsFkmo8bdJzg20G2Bd8bFCFmQ6J7/aMkeYIFwZHWXh0"
    "sTK2HBVajrSWhTJBa654e0IFwNhOUmgn0drh2iBjrzjepvnAYBSZ0Xjdx8Iki6eL8xhzMvxr2LPp4cg7/2bx873H/ce/vZz/9MOD"
    "1rM/vg+eHJ92n/32NH12/+HsadAOnt8/+ePJ8TenPx+7vz09frz3tPPdH8/uPU4eh3fPx52X7Z+63wXPg2/OJvNZ+vOP3y8eB0BZ"
    "X89mkwDqnT97M/6h3R7PZy3vCMu87E2+foX5T3/+8afgyb1vFj/9COV/e9B9fvxd5+nxq7fP/riTPJ5/vzcBuJ4en5w/++1B++nx"
    "g+7TR63m/JX7ZvrD8ru79+fB8d0Hv3/TcX7rf//9i2Sw+/re/uNnRz/u/hQ9bB9/t9v9efr7wdtnbx79uDjoHTvxsnen9fs4fXHS"
    "H+99PW09P5gNvn15dveBO7t3Msq2T0tNsmF6lk/awDEmHjqJnU3tlI3wIvZwLkymNjO5ACLFYX0aud4RSa04g5pRPHFIkz5CTcIT"
    "5xzG5JM2DH2z2fQODw9Hi3T37svR7YtZNHHwDNoB5rgA4r3H1I1OPLJjD/XJw9H30SzF98k0igCUETUDLeM3rhYcPQjfBJTHCScw"
    "H0b36C9+0axGRs+8cLqcW+gQzvJCtht0I57rIRmB5vNCf5cAgBtZ6EnN8pLUSyy0F42jhBc88px4Mi0vqLaU6HkvWqssY6LkTMSh"
    "EvRUyw2wh4mVCCS4ChT57GpvlQJk7egh9zw+X3jJ8JfR3ZE9+hZ/PcVfX+OvY/z1An89wF8/46+f7o5+hfl8/syZUzE3msMcg/pG"
    "iXcCa5Oz63tB7MA74PHf/yt7/X3pxKn6GoTKa4J6sOzt3/9zjEBmLR1NozhlzbGmWAOsXlYdq4WXVoo+DUIoeB8SjrBP8P93/P8j"
    "+v9X2OmE6VR06DcnBCiwQ74HAgl/Bmr89//CB2ccBzP6EODrb8twyv7O6K9zEiUpwwZgfExlQdBdsqcQRBz+0fX+YI9q86KXAANr"
    "n7XMmmWNsjZZi6w91hhrh7XBqicUpN5DvF4PU8h1v5zPvzw/x5GPk/S+c/7c/8HzToct20Hl+QVdcB+OHnqo/EXdkPcmiJAd3wF2"
    "GwcRfAtJE/Ui/vf/8zaYR7ymF0BnzC55hPsdHEJr8e//iXpiXJu0DP/+v2YprKtZOtaoVUBVKxkQDDUD+245EiY2Q17icpxxBQvE"
    "nCmUXoZK8n0vAWROZCqsBMOLFZOl3OnhxRxkKxC1dhoXgb+TToOk+Tnnb80QRucTYFnHLPzF6N27Eep3R3i0RBljz08ajHXeQvnT"
    "O8y+3zIe2IF8+inW8al9kT/mUg/B2vYJsNodkGTZlgEWvlVDVXr5tLluXHjNZeLthAsb2HjaaIDAOA/eBuGOO21kAvKCMh+6IAnN"
    "8SxSPDyYefincZE2JzBkCXayyZTLOyOFkRPfpseGDaWd1AHSI07/KjjGxQG2+Ck7iW4qQsGhdwtP1gAxv4R2/GvkWxwl0GYceAkI"
    "Br94vzYaoihUKtE02t2NlsHu5xdhM/ZI8bLz5S93dn/+9UsQuQ+/Gu2O/hOE6OhJdAbyPICz02hgBIgGDeschpWOQ14nMIKI2yB8"
    "DXiiA0QvdGGhgieYH3h+NGNHjrNoGb+e4H0dQD6IKXSmgs+xH7iYBRXs8AeXLZKU4TlZRNHsNSa36WANxRPKkr4OqSyQeey8Zida"
    "7B32NK+Z/SfmxAUBtjhUgQsooYYA0Nc0xVhdZ6/DCIR8Ah5lo9dZD+hV7QZ90PrCv2VN0ivvCz1TJ+QbX+TFK++8QnjT6Q7ba3kZ"
    "PQGtclK6e/7Y3RlRlV68OwaRbNS4TZsd7gMUXoBb7DRu3x6N8PT1E+/dOxh5WObT5Icgne6MXr8eNficuljdSuNzLptY3xw9f9aE"
    "lRgG22usYBQmUyG28Ol8Mj1E8OzXNK2h+zhdRzYdxCAXBQYKvD2hfY6LbHYG+7phuJzNCM/Awienr2G+OrAoD9utFggiPuBj+nqe"
    "DPveHqoFgRTPRZZkOAdZ6CwUA/wLNIcrFE6M14BFPLxKkCvjyAJfBgnoZGqLhOHFMgbWRiAFUIP7mr/z2tnrNE0Xwy+/JGFpCovM"
    "cP8AtesJjDCeFhCm57huyA4Q4ABm6r2m82AcS/bKr7i0WzYjh9e8P8PROEqnuL+BOiZ4BAjkyGib2RIlw7Y8rRteMNoHphYkU5oF"
    "QO80x/Aa7Qh3mhTX1Ell3gl6/5SgrgQehxeAkfkUzaDPaX+2wpyMcEcPXr3EoFB/4Lk3iqPRyeuFg9uREZ2ovz71PJje0DRNLEJt"
    "U6D29m2kCPsNkMGnOC/RjpfEwk+FfDiyZQKuf/gd/2afAcR5kCSQcJ89ZUknEaokIOXryMLdeZbCDZkg6Ql7+t//4//OUiMs8/zb"
    "7AMQb3wO347jc8s5IfIUSYnzBoE6gj/Zx2V4GgK5PUD9BCS+Yq8W6SsgFyyXTaZDQLAvwpWVWCQoUArIa0uQX3kKvClpTgqfndS6"
    "wNNHYKOfnk29ELgryFIIHv7NpZ2jMByz9J/Ec5YndN4wr8vYB8YMQAwlBpLwZCKHRKSLr7D/xiX+UxIqQhL1WG4kJ8yMf8U3Ptr4"
    "WU42SnFSZDXQ2KcoCXsu4EF84TlglQmPsvLP4dVSKsHm0BjKO2GVcLlaSSKkvwD+ELyFdBqSYZbKR0qmvyQ53+KflYxhdCdMzqjD"
    "Fw7hZ2U9i0DOwY+WH0dzS+DP8QEdVrdlJbcsmtgsBWaUNfZgnfWslKYRI6Vm1saZE2C/cHGHZmAzZxHuLTyht6ZOEv7v//F/ppYT"
    "x7gSWecoVH7KYAEUh5ygj9iTlUayWUbcCw+vDovBfNW27jENpxUkVrwMUTNmcXnJeg6M8Qg3lvHQQjiOQmcxd06hW6/aNmxWEguP"
    "r3HhgRELXRTYTrE8qx7bxq0ogOqxKj1LaQ9YvW2dTYPJ1HJmSWQhN0tYu8QXmwLYjMaM0A6tiagxB6KEKQeqEZamdYxNwxOH5GwK"
    "M0wMJlr5JBKis+k5GWQDSD9Mz630LMJyyW0l/W7k4lzLMGhNoA7ckEahR62A3GQtZkvg8LBdPfEI2BMY0oR/Tawwss5glgIap4EL"
    "GRjKkigjMSii9ALoBxhTIuFB7M48CxcLGgMgEOt4ScpPhiteDTUf+T4iJgMYqCyxXnBQmB4I0DCPEMKUo8omEM5ADgAUi/qooJic"
    "NideRqDwGntMlW65nPqhAiR8IO5gAukg3Acz6zxaWiREQLXIsxF2wC5dINEYFc0KkTLBrcFrQDBOTxxFmJ0gxbYZDLlcgIFYz0cs"
    "WHA3dqeFpKuEV9lWsIN6BbT2SS2Wp1BCVA91lpfKN/TQgQFzdbrhSUANwJAWuFd0hxZTeq9EcS73EOeip1wC4wkvPccVY5+xFMYW"
    "1NwEQYZd0WqWy3EZoHeQQd2LljOX8SRMydVeADU5DydYPfyxXuhIwKRH3mzBQc34JTBhopPYGy+DmWvhjv9ckm8OpzoVq3Vzzsie"
    "JF6JenUeyUoAB+WMlANqPXAZI5HZ1bwccsqvZBlaKBskhBbY5zrIsz2qByhOm4WsDVzpDBNRdlKsopAHWsF6JJpEnqYKlr4c8Ea8"
    "fEeUfvOZ+tz3xTAh6qlbxER8f4guOp0E1r5sTuYlqXIiC6NX8ayZcv4pgQ/4uobgLRd8WVMKjBlDfYBLAbKHOOu347oo6SLWBNsh"
    "mBf09RjEnabEMoAVEkQJq4QvVTBZvabeYIJank/x9KDYkjLhs9kg+5SfEUpDhlKinQxhbLMAy5qsZuxRTaI0KRFlcyB/8F4oSGNZ"
    "ONIk/CA94KrCsjetO67LVmjEHM9jMxQx3HFu0szV6szHS6j2Lv61QBBf4tRcQDeAtpXq75HUg/1CA1tguuoIVbYTRk9xu2jo4hy/"
    "Y9HEs5grgCRfiHf63hQPARkdkibXimARxhuE9I0XxkmQeB5nKdRINn1SxzieOZFsh3O4BlAZrCWC+CmN8ktJ/RYuZ3NYpGE8o2WK"
    "HAA5KzbIweHaHGj0oeycnvQsS4OWQ7znI3OwfiK+gA/YllB94FOKbopJ44Fo+IzZvbJZqZd+wldX1kZGtiIX01ZkGcbnFvuk5HFm"
    "5MRzGaOIeWc24znUaoQWBIV1/qhXIL6KKkQBtRKmWaEqwqUPjGsZezk4vqcsWSVZPrUiUj6Jnn+NL8WO440akeUInos5nARXtjvJ"
    "hDFbJcX1KAkt+YtpQcyXDnZzBiQ4nulL15Rf6KAQjCkujPxdHSPcG9Pu4R57Kg4RzyIWLS57e4oMZPEsTIwHeY/V0dQqAZK5Jwji"
    "Hs0tQ0vwWSb7BbIm3DdDJmIR7ocWndjmswhyzrKJL4WsCnXxrPMikbGskoZkRiMp4eiTfpmPPsAIL/kMSrssk6FZyihbFdnKGwWZ"
    "G/aHfBmn3PKLxfRC+RLLhFEHZcaXknyktHyt5aZPVCafGY8I9Lz4xZiVtFcyW8Q3k/SVlCNERuMZU8rcnQmVDH0+iUlH8TX8yT7C"
    "PiZlm61ArSImYF4SAPwTC7xKAjQ+ZAnMxTxpP/BBbdDzGEnBXxW8pUfQLZVKFst4Qcz5BT0oCbDJxM/wR6kiho0F1oF/s89k7o88"
    "C//K2cKIUd3AZLsWLU3ZV0gGJKbQk2yGwIqpzA6WgasznmZEKlRSCplqWb8XZJpl1AgVVkjYqAfhq8STUMMavyTNnJaogC0zMKps"
    "Riho4vYrjWDBXWUJM89HHnZxtrLwEauk9ZktXsou5bOLAG9p8WRY7EgOhVUXHrPvqBtHenn4+D5IsHi9I0uDtdXjIP77/0Ag/7//"
    "18J2xXelciQi+M2UFPI7LOeok5vNI5gUJCZl7bIdL8HEiw2lSEJXWSwf1uSL3zNwuAz+kHB/h72wTMh1snx8mJ4wRL2UfIF/l/kW"
    "k5TnuYDH1T8zFpJ1IHzBp+1zdcISIkhtqyLYcT33ccilfeAvMKQXZyhDZ5lo3CHHYxpthk89B3x+iOwGyYukuThJC4l8gUKFH7TD"
    "jlkspstmUKI6RejTYP0iQhMrGO2wgmzzJGsnDf8x15fexxeLtKd6hjsnkUxGmnC5ClbJ8nzmyiyzCI3OMA+06jAd0wVUmkBJkPkA"
    "5eiYLtYr4P17grx0jlHVXIsdP0hSyJb7O9lKT2HkdEUITQKhZxFZaCYxhStfBJiSMkFbDpFpSQPFxkAiilJQ24OsKnojMzMf7aRo"
    "Z08igQOawSmrD7OkV+JZlnKpZ7ARcbhMbRg01jCihWS9+JThSI4ZpZOccZ9nYsIGy+WydYcy4e5a6I+VTY/EaMZAn2Tck5IIYxLZ"
    "ERte+mhjTScKMl22gM0TsTpSwgl+4cNNqbY1Z1QLtNJqWspOWGhcLNTdky4M9QZNrabHzIZdbokdi7FFxB9lsJwxDBs6NwZpFmQ4"
    "PGZqtVqylmX7LlopIk8Q3V6RtlQoYamjUNBBHaPQnt4CoN+QjhjV4yK7k8oMTVrpyDSoSBKcf1k7RKwNdQhuW49TYPNSV8I0T1IZ"
    "mKiirthhqk0pdBR6Zxkt8RbVlpRirAsb4qBpPV2DA1LJBuHSK7b1E53p4IwiHQX7CLnYvBJyMCzfpPZOrHEUnRKpqxDBRr+ZlWE5"
    "5QJMr8VUZQVmn9RGXzLWD80is+YKchLw9oBveKdK5phlvThZWSeAF0y10Ca4osgM9vhoxIIrJ273ieR5Ub6y85xUEJcq3hugYdgn"
    "t9dk5V1jmbGDlJbLj6sZLTbaJp0+Wp0W1/+Sih8/StXDsSq7siR5OCVRHhYOrQo5FfRjbkNmOm/8bokmwum5RQePLCH26PyIdBqo"
    "URFnj1oq5yxKDvYbepfpn7hqSZY1nZpqKbzWR3j+wCYjYg3NgawElZMyf7IcI2rxm8u1HbjmJ2kcLODLIXXac/H4ArgWvOPgYA5i"
    "24lgqHrN7OCnCcwM5/bTI+XbNGWfrEfHylco7cUhibYP+KOUovN5jrjeTWRUssijItqU82clHeWh5yi1XizDIAVBfBYR3eWyoKrG"
    "kAT9fJDBib32ymDlpgXP2L4zO2I1pD/LMuTaQwYoFBciB9+8iiyxx7e2L+khEzPlECRJcBLSynaBixo7L2ECO3UfqJ9nUUu57itA"
    "kGDMoYUDBlKs3l9SwaFBiV7yDo36f1r6uEPCo1R81wcfkgCvlFY6+OwAi8nKyIIXBZSyHBxsnosNs5KJiPaIbTR4nkwpyASs4riH"
    "UfqQr7hMiMATHR+/GDLxifeY6QunsCyClAvCgIt3oWFCARYVxY8+TAw99FhAAMshyIFncrKBIFmfjS4vopHBMo2eRcT/CUpcKYi7"
    "aOdVjMT4+UrTeuBMpsVDChRzcI33cA108bw2UQ67+ArEb4HrJyDCCZ9tOTPUr55jbjzPyBRUAl7crjozDvEdVFJj/SEeNwJC0c4I"
    "d2DnQwvPlbhoLAeSTgigaVypOW03EUrrCRZ+gufKgDCpERb9Bki8md/UxlRb01Fziws4qd8Je/wzV4kz62mFoND1BuIQh6apEzwb"
    "atc1EDI3I3jE+dgP7JV2kSq41AXU3euH5NxYQK8LKb5+XcQWhEUNE4HKJxcJQ6IUxzeOdsIGRRLj7UJtL6R5gKhQ5F1TJz8Suk3q"
    "/vC0iZ5QFBaJr2rSXe3UA2aQtfPkzjML7dYaIh8/H2IMD59EAvDMmO2xYs566bNwwoDN8kdZ1SL41sPt6Z0Xj61T7zxf5MWUizKh"
    "WDvFKLDp9CJeJs4TJlsqFVKxh9j955M0or7S7LqzWMwCJgFbkE0CTmvxw2DGjwTY+p+ZUmQzhq/ZVGgKzIva59tKOgJiCLFRwCQc"
    "sCM63huS70t6Is/0vrKeeSnkPoUn2b2mhWaIeOwkKrZZHaJmFJqRbTgJrUAMm9YOXfvNqmlkR4RoqZbodQgdJl74Wabc8gI5BzMM"
    "ydAgJoyKCUQ07VtP0YYDG8fjXYH9YifzQyHP6SyaWrQnzIqLc1M0G8bkAWz4fFpjHfRhY7UPOs12f9BsN3utYQ83gIaOIlC1+ijb"
    "lT2EJWEKw0KScjZyseeT4lnHYmzliHkZxsjZ0Iaa1XHPkedswPAugsVqiAOoEkVEGziFB6KERnxQiGoq6/VSzv1fsO2U1Ebz2vBI"
    "25mdOecowOBGi+uScNuF1wVBIsW9Dd+F4fo3h5FBV0OwasD+z428RIDMhwctmsQM4e3AwnHHZ7t0mig0QkEKK1i2rNEOko43YQdM"
    "hsezc9Ju8UUAYF6mDH5tq/nYz01ludRy6yKxSmIfEq33NoDPD5ghDbuDGjqs27YieUzKwCP1M9oWAfjqInQ6C9C/Csfyt+xNbF4d"
    "jklAHdW8o6GatHkNRmNE1U+jKIzReIv6gQwhU4pAYyfsziOiIvJ9m+n6zgLOYCSkZ3hcy+Dl4FrHecuwQG6sx+eKCZWkanabD9VA"
    "Yq0XKTOm0HjCdFiMR/Jz4meZhQ4NcBfNNtV5gktnHKHRE10wtdByVlYidPLqNGL7SlrCKJnreIbITZn2AXlHAUZlWtWdU2ytDC2x"
    "pMlVkS/9dAwehuQ6z7bO1gkAovSEldEq4GaJCIgwC4GcAYm7L8Q6oaNFnruqWNCz0ML2nC6COLMhk6v1+ZrB5JI4WBwDfEYTXpeb"
    "8qKnOY9E75nDpD1kmWru0lVYZMpvOGbKME35sS+UyjpOA6HQh2o9yeum2RHypTCR9hRkyCTGj4z9ioxerXjbRY2c3xXOqSyWxEop"
    "liGFQoUDrPUlw4h6ohiC8DJqljUyvq3K+EorTdQ7ToDDuIHvCxtesv1EPjk9TxjxWOzQA3GQxs45s4RB7QE/6qGPAAQ3tXvGnngp"
    "ka6cQMmNGSWwbY/J7m8I4uxKZGN9fdX+lMz2C9wrn+2Y5tSROjr5/HPguE12b5+fNL3xJGiUOJnyE1VuT6Mnqmf72kdhH3tPGtw4"
    "SuW39bwebdsl90fKzIT4JI0WiViPMy6PekpSzDJ6yDTFfPuEK6e0rKa2xstEmu1m1YvVkJ2FZRnzMLFVhdZJ7E2MakNxVEEVcHPn"
    "TPts0waff0Vw/n/u3qW7jexIF533r4B01TTQlUTxoSdYMJqiJJdsPWhRUrUs8xBJIAlmCchEZSZIsSj0Oj/iju7o9L2DXvZaHnn1"
    "pKf6J+eX3HjtV+ZOAKTKVT72KovIzP1+xI6IHREfEGzSc0RsMus0bD+UiwNN/t1RwFooSbuxtE3xF7ZlrzTlhdp0csWUXJzztYvO"
    "4Jh4QNFuEiP/hp4Fhl9F22F6FrO9q5r1GVrzW9PtLB85XORnZa3xGUPJhVYaBwS7XyLxUiBEY0nFDsPmql2+my4pGobqTGwgSZlt"
    "OyVZpXmN2Eg0wfKt9AX0P/kWZl27WthqjlBkWTgTcHxYgcLsGLv7aL01SwfqtZ0C/X7wrB2OI/t1wiykpahQFvZOZrzWFc2X2jdM"
    "M5HBs1OeTnCfnc4bwHNM5sIK6a/0sfp6jP7ndB96wXrMhmMY4KYzVx706PtuHTb8yk5E9wVI9vjeYOjWIPflQ218oD8NudpHRGIo"
    "1IfxpDHzkJI+/zVuzlLRfH0t5tNP5KFh+/PopEj8ppLygH9jwrEaHjvtcch+OPxo7r7c8lBZ/+rNixdPX/xGrZLSFHOa/VeP93df"
    "PaY00ZS2VjXRwbOne6qg2kT7u28OqJxQrkNL3588ffH04FtrKDxJdp8+e/wIk5DNLCQgiqAX+xNzKoRk9cOfUah4xJP1HcoXoaxr"
    "mYBcJ0SOqQ1CCalEPzQmUUkMLCWckUD/EKe2zGFayVKyoH4kEhaczGQuwgmyaBAlrATDH6oe0yK8SHsh65uMA9StnvNZljclcC72"
    "ZHhSbKPeJUCesJ7KZ2uTlJOoperOjuoDOkmJZVDFaUonq1nCbIiiU7E0JqOKV0ijuf4GG4y78IZ+6PfurZh1l8+fgUA+VKW+kMPE"
    "aj6WKmU6rZA2OO/40HjIv/igkM4xJTww2n4ZG+b0iPQz24VMn9XyVLwYmVkJ7aPKTsIWQMzCobCVlyuCTj5FtEPySJWOxvqFTkYW"
    "AU/EzlFZJlRuKqy0L+i6DhlcNozGRCyNsnFBcwM1BGjA0CrtlbYuCDbUQx5QJYhYJu2ixOVTUGW1TMa16rtkmJ6HF8yen4ZTMgrq"
    "2PW94UldUB9Hm1F+RV9Y43mY6yUGYgQ8llcZvEqKUhqjcnET7g6HHKDRlBbiK+W1apVYTSpegdX0yhhThmSckjkwyEeDgkVGW4Af"
    "zoSHUlwt+ZsN9Bjx5NdNOPCf8YSrM2zsMJYZYFpCBZqiSP+WNFROXpKo8NAngLNhFf+O8+wsnZ6bjLl3sf2gtQ4ExQjE56jJFh0K"
    "uZdZs95xSvodiM5Od9DJju6nSpSb+kXyBzp4ijqN7+FxBjJrWwzVzKFel6p3XYp0MoxSplPivGBiJhLkYNueYnSNob7cpafSx/b2"
    "hjohtjfQEC0vJ3igEzzwJ7hg7p4sIS5Y0HO+h3Q7gPb1yL/or3mcDCJ12yAKQTUBonyjJGgkV7BdIOXDOKNkXEjOwyjx0a4M3dy5"
    "dXXmuDK1dUFVpyR6bw+gCF0W/xBZA0hlG92x3rH8eZDmhZ0Xn626z22DT/0edmpBVX5HPxzTRK50UOzSeIqlJrBxML7VdLhRfpse"
    "q/H9Pj3GNFFe1UPJbJxG4xNl3QnEDh/NMCSQfBANNauAhAGZYuKYBpEnocU01CWm80JNi3bttha69EQ5PT5L2duAXxhmxp6NFxUz"
    "p9JXn5mTXq1ihPQGCQKqqdFOqPx9N4vD8pLQV7Dis0dmTve1mZN0N8XsOQtQWk8hK902qZKMZqEiIZOm0SZzmoUPol2nm/TjkMRj"
    "inGOjIWj+5ZLl7CgMtoNCjOK7AU78ytvp7gwlU8sRxvtdONuBJ1ExgYto8NBloKUQcEJLNecUgYzXZaJeTWNNWnVwqpaNXtM8aBi"
    "MqQzqOJeKsttHuSUVQx5aZfnKSn6X4nvOzsHqJoPUmVNL6I7nleZSWoRG2Pj9o0YrDlTqITVf/d/kyb/u7Zeczfuw4vS1sWZrwwp"
    "fXkhqgk2STM3KEoVD6uAjn3pEAyidrfnUuiWhYIDkNaFH0tfpZKD2RS1/eJuOctQP4iGmrMpcaslou9XK5M2W5GvtksoSZAiHzH8"
    "W/qWc+VWM0oJqEHsrSH+9RguEvVI59a64LQgv8XHmTL+3TNPhtyHY1FT7Tas1A0yIBReqUjHQ8PCIPfB6mW+Owv5KgcvC+gWkJVy"
    "8Jab4LZIGa2UeSM9cjRu7e3JiR68EukvFXiQkoWXq1NRU3SKboqmILFrKZcgB/pLvCOQjJNwGMkxTh7OdP1Fu2TAcbqsMlI29qct"
    "SAWezMZlIg1EFL/wnqNEtdsc3hUpBWRhXZc8l47aF0Kv+Mmq51udvWJsW1fjAK32mb99xAah5v1UlGf7zrGEXzyuji4FwkRsnI98"
    "gXLVsr7JiNDIOF+EBdmzOQ9/Q06Mwz7rUIwMjlaYJBWQSa+hz8DiKx9D/K0/RB+nynKSbrxhsewdvMXPUeH6dVt2DfL5BKjSMbO0"
    "5FGunlGYlAv0sHE8G0lyNlc1cjJbsiobVkwxmsV0mwf1ANGhJ/uLCALa+3uWJblt4RW7V8zpolgNHKrCxAYhhkAJTiQgYyx5PtYx"
    "3BrIir+R1pG/AXsil5sZ60QoY2jXb7qg4eNGRQQo5Vf1GPcizbLIK0mAEaK0s2gDnxp8vU00WtLKebZOZ4FRd2N+eH2Ab21+tiFB"
    "lBtNEuNaJqnQyIcR+kgVzM3gig6MkgPoVtmFETkacX+BfCJ4295UqrcU7zA6Z40j/nLfv4ATWy0ZPu/0DZEMbYGbndKKqYasBL5L"
    "KbJ4RE48alxK9T4WUzPlc6Fan4g4a0ovZdzz3Jiiowdd4OuNV0lfvSzFFVGb60X5WmJh6ue8w79iJk62eKTwjnWsJ+lk7n7VV/Kn"
    "NM9RdUpTsT7FJYesSN5xSmA9k1JIuZ+A8Ip+dJ9/sVbXSoFBbUglh4HQeO2FF6zOd+LCmC9Og5WDWGJCcHDsH9NK4XCgQ2PckBhX"
    "TdG4c9QxvT5P5XXu1KMsd1HdnIRZBrWdx8mQVrXJAkIOSHVK+A/xCDX1oCoBmYecQ/rgUUwAlFKPhGNjq3385b7XngBEMolUWZ0M"
    "KZyJmGtgkCCkaKWSD9xYXw2KyudWwUalVkEdY6PqphVGhu8Sof7pVJn7KMemQAUBqhqh6YZRsCBytaOoQcqZLne+S88fkYmRLD40"
    "nx6lEo0La0QyQ5Zb6BzWbuyjRIYSE5k8sbUXUyK2I+RgjpIf2TbSI2ANecoNx1TsAYi4Y4aStRvPyHgk1Iw6kzIiu0mq+9Bu7JoU"
    "FAprgFIbM4tnGPUVA4w39nfV+/3d9b0nemSgKdBnpbeRN6zqfSU1kFaH/Ucnc0mVpOorEwzbPZFOFTRXeR7ahro6L4y2oTRaYFNe"
    "SZgCXpJpjGJ4XJvEb5/uH5iEamNq5gg3xHAoCeAXtwKVZbbEo9pBq4ucAtWUA0fNnn+aExevSM9+b+rjH41EWqr96mrBKHfwhf3x"
    "ZaJoyYmThhbMidhv5rqXGMmRrIpOogIlN3xuNP+55SSQ9ftdiFzKudxYkRcuq96Nv6DqKgZ0wetJWrx8hLHFkvGzov0kFeYIoaf6"
    "yFrcg4LZg4es06U9Kc4Yuq9yHW3xRrRMsXKUFGY8qhy9ssEwZzjUiuvSg8i6duUzMM3SgQTTEQsmPqlIbEdD2APZbfvxlDDWJBqZ"
    "OVmrsQf5PWuOzQxNnbtwtQos4qW4U9JQ24eakr2G2udYNJzInPLdz7cKlJoyoFcK8YLGDR6ZvOFYX0Im6nbdCmFnJUPrHbKkjKJp"
    "ueFncR4fj+1C26fMO5KD1rR85U+HUnwW6csc1ygA9vwPszhDomz5NFh6ArEXkYFu5np74K2naMapnZQKF+qv7EhV5BaEgbeiqiWe"
    "XYoKQkJBZRtUIHkaNA447/GFOFWI7bNZhsga50xbHMtTDEXReBFx1DCMbAdFqDixWn2jYtv9uvEKVvCv1XLteFrANkixcki1WoA2"
    "N9jsdmnxwYQMydW4NOQw6af0iY1SrTXI207ikdluIbrsclBN/c6sdKJupDY3q3owy7IoGVxU6VWak6tNxyRs50Zd+0Q7SSB5RISW"
    "YTRvlQpVzAYVBad2VHKiYZWwI2i1G27JsE1YJlNlNiSKmwlOJtbAilLAqR0PPnD0QHb4J7PFgbAYVDkB4u64JtqwtOEALaRNzrDK"
    "anYtJrOIcGEpbpqlYZC4iuQJAfOmp1RdAWV8zyBaEEaSbcQnTlDD1LoW0o3Qi+a1PY32mnE0HaQGLvB6hBsqypYIw8tQ1GRcfmwD"
    "Li8al2dzm7C/mYo6gykz7iPW4KjllUQc7PStyY+1hmchLCKMfM4GllkEp46mduOU71zIWi9CC8aQ0LDpo8TAozs8joYn06YGwkTS"
    "baxxDCLDT6Ikoa4AH/EjD7iU0SslFelf+VbggWUWSUh2VBJ1DlvCDBtONwYclDJoOU3absFW9W7rcd1glEBmVomQRPyIjsjAELdN"
    "nPNSqCl1t4Cf7OseysXx0NUOpkAamgdARzplZkqJ68Ji0Ud/4C36ZAUipy09ppFl+2hKoMKsU/f5p/pkm7YSDK36wFZJJjTJcajz"
    "WNEWNDGwgtZQGhWy3ThNKttvaTLFNKPmTuwB45juEgfGzWMHeWf/3wzdMPDRcgzjGyrJYKLAUwa6OmcxuNHcCrbvbzRGrMzdam/f"
    "b3wYtVTWumBdRsNCyXQIeXGYotAnLE6oSBPKQVP4EBUthedFol5YUkiTWH6jmOX854o1bplxUvHq+X4lPrlwo08qPpQLgLMzlysS"
    "ym4FuK9Zb07Me8+iK4fA9688Kyi+NmEhk0u1acQq1CResO5MGP3SquKAwaUVaIXZ9xloO8l8u0AfWkRxxVhVfvKxpxkuuZlWGSg2"
    "4msOWrCvY1niIjAGGRa3JlYZOZGwtl0QXlFwxa/51+J6B8rRw3b66JgD++xSjpO5nUtf4+6ZJp0ocz2dCgUZ6RKRePQkYdE0JEcx"
    "bNxrbVsdVUJvtsuFKbfMSmnoHYGl2VEqTZfbvplxj0Nt6qXTzaav00ec4h25BqN2jYKrqDCOeTZo/zDDQSay9h0R6vyUBDP7GswJ"
    "PopEpyeZZxnF5Xr1DAeAEwHju45QApEVETePsjMWeCCPxLXAYYM3FJ2zLRE3S1E65a1OZeW0xkZ/RlPml6xTQzdxQq6xPj1N1FlM"
    "n+PE4l0X1Yp7kkI04F/91u8Ly990YPdX9KPUCtMAUwUyzntMTqyQscZ3l0EcxMtSKA1npS8XzPPAD6sNdkRgjjLjZFzg62SNBi8p"
    "03xIoXvAsdc9KcwkYBKYBzsNN8yN82uaZ6fkrnHKt+q3MFClpDyyOh61mmC9oU2qaGhah4EJrEXiJSSl8dCJ4RTas9KjIePAEJ/L"
    "89OLuU6rac3AQ2tkBXzE2ztkCSQciHnssE6E5A5qCQkYswQExXiACqgBLVvcY3RLy/cE3Ga07mKWDy/QwuSCNALGsowViMieR8pC"
    "SRYzuU9BRn1F9gweZqzYpvcqnBfiKDXGpY9ic7yrxGiUx0hcKkgkozQkOjxORuOYA4DjO0Jvw0LTrJiNZp//DBzLwyzM47HOJm5o"
    "puiTFEMk5uUQ1KpJcjvDUhaQpQl+bTfeMR+eorYUBRPi7U1wbSlE01IM8xf/2FZU6qAAVrli748p8g/sxgR/2G5QLs/wm1wlPmR7"
    "R3yTMMv/Av7IG6PUYZGCn3VyfRxhFgzHlA4+oIpI+CZbG0IX/TCbkW49TWV7g65txyT9Fjo6v5Nks+4O0yTZ4tsOjLojmkPzbZtP"
    "nMwKG28+3jYfWV/gfL1jH1bMr+DHjZ/qVjRY9VqU8RVo9hro5EIByshqjKFO1JhuOtwOqnGWzAse9KjuSa1YYjLWzimEzaw5p1R8"
    "6qZNNVqqRVsl3Wf+QZvAWmc6+W2z0xV7ZqJGNosR8kGHQgHGVTxmZmiAys6Y1KfwLI2HqHGYRqRunAJPMC3yHcvJOZzCS1jCNMBI"
    "3pXHKBag2rpNYUiZOZyoW+NK6BRPyBXSR2W0ddGvZWpPtZjOsMu4XHlcCJkwK4VDaLuTeTs06llWiLBjrlYSIWNjB3C3FV/64r1p"
    "HMOw9t3kYjA7jgettkyfDqsiq0JcYbVKs6rw1e071jqSvPG//+d/kyoQ/2plIJqO6pxKk02++Lm58SLSpgL4J0Ydqqq5E2pzKrEX"
    "7ogRK20Z5ZfC1nvpgtAvVNixto2lezfRBgWizyNEDte4VOccmDvDjnKUNJtWY5/o9GLWy7x4znY9J7OMVG60jqyA7u3GqyhlOwe9"
    "z9X5yBPis4Jo9+fBRT3uEwltJeQnBX3ohX5ChbD9UYM/KWzSKvbTXgjn6AiGLV0R/gmpA/Qf7wbPUg8G1PjMrqiEAoV/GxjYO01A"
    "yIiHaQUJ6vTzf3AY7goSlPrCTnMaCerz/8proKC+Tb+PFiBBvUwQb9SPAhV9/s/P/wW0a2gfaA4Q1MP0OE7CKhLU0wkJrilihDpg"
    "UI/xx+e/INBL6AGF2v1+lrPmsYwJBcfBIM5DHHLYVAm07P9L/cBQu8dZnDVMSVVgqAR3YbIQGWopMBQixdpTuAQg6qXhDqHheGUw"
    "hamOZg0YfMGHIueUsGFDTSR4cuBZ6Sy3WpyokCweaIyOeWIaYZwMQ64TDqdROvMBRREeL3pThIuRol7aSEOwhmApZrDKMGeCS8oB"
    "iwpLUFH5DDWvsLQ+/yf8iKCfZ5//kgxm49RpbwM2PF4gDcJJA9FDj0Or0qABgjXQqMnx5z9NGmgZJBi/+E8K3zyAUfWN1qhRUamx"
    "DYwZgE2LSq2uNKjdwAVNL6U1KTXR4DONP//ZhxkFvDglHGL5kN0LHNVwoKPisDGbcF2EbTwIhxp9FYdQQr1EPNvpSYQOhjClBkxq"
    "Nml8H8UFDXg6wEWcqSKDBiwxzKfa7WBjDTiUKUwJLFfdZMjyA4aqhMqQRgDFR6UHIvFOYCGOEOy43XgU5fibdDuqraYWeEIU33Fo"
    "UKZS92qNzA4iNcgRQVjgGgmwUtnkAQV2UsRKLaaALLjw8iWj30BdYdtDZkwd2XTIahEkLD7/CS8z4tHn/1gfhxXIqWelLbYIeApS"
    "bUq6xchTQ0ZdKBVZhp4ChgyOc0ysTvUUr5KrSEc+BCrKnK+eWcv9+5LRmRhaY0CCwnH8I070AjiqXUmVeQGpnkVEeCqUqwaS6lmF"
    "wKk2hDXYVC+wpSdp3Jimef75L2fRuEG4aZUaa2GqgBRkaYI9kEH0gFU9wwtIi3KPUqRMuP5g32JQHMQLT3PvLNj7IV2MW6WbgoMm"
    "ZeGGSBegVzHaOt5BmeNcVlK4EMZKMoY2kNUoC89C2kC6OFoKOXI8dtFWp2DjZLTYYLZ4w1b6b6+s1Po0SDN1VAI514WKi1cJ4Eof"
    "Y0u6Wgt0ZU101FDDlhNZHDIZ45Vej3xl+MjFS9oFwHppLRxzXuOa1XjTxCNWobCeJiCCTvC8iVCag1OKhjMHxsLIZBNFJ6FXg3GM"
    "xw68e01WC0igp0i6rROLmk0Hn95kP8ziOmgsRq13qtdVE452bNruAcqq2Z529QsAs5K6zZ1mMdL6YbWUEnAWNT+URDz8Xvwsa46o"
    "UuSapeR2Yw/ID5z+0Tpja5mht8Zbk8EaJK1dR1NBdcQ0u+nMqkiYxJDdd+vmtlpXBU3L7TcdqlQMorhkaR2g1vMZgVAez/IBjPEM"
    "1spkGiFdk2zMmVAk8BTH3gx/BVFrZbpsg2s9JybL3l7jGPaLkX52kDeAIofMNCDPnJsjohZli3vsR9nCbtWjbKUKZWtMEFvMoCAv"
    "9R9ZnOIQ/V/J5/+eRFm6DGgrCzNrqXqhtjDJFBHM0lqkrddq2Aeofb4u2NZrdVxJrtiLuPUkBElrgEJKHd6WLudEJ62F3NodZbOp"
    "dwxs1K2XGZwE3lSMvLWXEV6W0ySNvDXwfdTQW7tjChhNKK2c7OuhN4t1oc/rEUNIAoU8Qyrgh+DCOAkh+dN//uvHeBLWonBxgTiB"
    "Fj/o5sXTE1c+zHA9ENcz2JhheaWoUF3y8aSy8B0cLpmQToNJ/CIsLp2UNsIiKC6dcjkYl0564ltnNhiXLArEDFuIx6XTLYXk0inr"
    "67YxuXTyaZSnbA/oySGO5m7iWc5nez0ql0mPWuk4wzzpImguneHzf4+BKHrTK3wuM3S0puD1IKwCdO1nUZFWALr24uTHsIrQ9RAI"
    "9CAtQ3S9jYBPGZ+mHpyuZ3BmJN+HHqCu3UkIklhaReqC0oZRBalr98fZ2IPU9Sr9mFZwul6leVjF6XqOzhqTBUBddThdWsirA+oy"
    "BMuD1HWAErNsnTqcLm0aX1Ic+sG6DG0up/fhdUH1vEbq8Lp0AhuvC4XWBXhdahvkPtAuVhzWoXZFPwFsF/Bh1LgSbJcoihrHYfwx"
    "LUF3/QBMZ9Q4C3+MQw9y12M7Z4d5ILQ6XSe79OlC+C6jm1iC3sVDVpmzOgSv8ggbBK8XZj8vwe8SmWVI3GQdhNdjWgBLIbzCTFOp"
    "OhivXZQGQ52sA5x0NsERZCUPqzzhkIMpySwRZEhqPi0Z+mG8DiJSip2m30c+GC/1WVToQx+Ol5WGTl3g86dKpzeOJsdZRNOjUb3i"
    "MPeieX3+f5D2ot8PiLakrcZcooPyI3sJC1GG9tKLR3Pratc48F6PSNbK+FSZIhd8HI7D5PN/hmWMrzBzxrGM8pX5Yb7GHCytgvNF"
    "rc58QF+PgPUufVYQTfEAY/QqNs4zuWW4rwExM5OURtBMcRX1S3ibYcgyhBlwG/uLrwiSdBn417iM/CVkKzGDG+Cu8SF/hTmd7WFe"
    "B/4VIvoXLjFcXBvthiVhfv6TpVtD1QWpV7I69K9H8QiOXlTviqyBPR9xG8IBrsIhgYCRanNzY6O9FAOM1d8h70klG5OuWHThuBrf"
    "bBIS2Oc/r49pCk/CHyEDUlBR7NfhgPGaKAOBJfbl/WMoMg9jrIblPGr7WTr4/GfRtGek9NV8tw8ITK0ybHeSnoVmuam67TqXQIKt"
    "OCQEDLZgSBQsWJgtwgVDBRRklzqzKjaYiO8x37MhdeHliMojp4Wo0KjHCTP5F4KFqWT/FfkQww6YO2ggmWaWE37chq0HoxrWoYbh"
    "eckpluazwqrAik3pGMXOS3aL3a5BEBtEQD9YGb9KHum4zkUXsdwo58gtg4pZyokc4cRoc3OUR3X2e8DFHtt8dx242NR/+7kIYUyy"
    "TPx5LKCxIYbv8EONweqMkFKae24v3lgpGWmTalRwHswxfV3vQx17KddUtP1TJQNjfKgi1oeFDT/2BD/AFBj8MaQfqEAlADK0tiHV"
    "TNDIP/8VyCe+VpNKaGVowZXU1vQlcGRyeMib5XBkNWhke3Ib+TcCI9Oko9pOF4rMueOvQSMzaRYAkqEODYln7CvQhiWDdGG2CjCZ"
    "kUwUMFmRxcezz38ZpnkNNhmdFXSGEkDZrGFpR2Uk5NoVWgHDn/10SGW166IEHJDVjVAFUClbDFf2OqbjUx+H6RKoMsX14DETJXRp"
    "znxqDWLZfko2Cxlid0GOj4MxDj0pjEOLy/UhltE8xZmRp2tAy1Q6W3evgMuG0TLgsse6E3QrZS7lzAC7t1Ks4vfc2dGdDXpUD0jx"
    "bu5KZ/mMVcAJ8qzjqEiz0q0X8pAZVEQ+gKg+/h5kjoRuXpRuz4thdvD5r9TtszhnUxIL7CDsAHcEP4es0rfkJ2QymX3ivRDPGMgs"
    "tWzkaH2zEh7J3xRNDsyI+ODMXDYEh40ZjobeUNgb6zOKeQOgZWHD5saIpa+HNlN8nHf5lzDOdkfAWg3lisCqmO9SmGtU9hwLAc6W"
    "FpSuCm+mdiNbHsjwG40A7T17zS7HN8ssVIBFhaZ1AGev42nqrvclMGeTFAp7tvvCA3P2WF39VYDOeAd4gM4OYN2EFZSzPYI4hFbt"
    "7j/1Qp0xgzUk+cteU5OFSGePwiq0Ge1uhZjkwznbR0Xj4DRy1gv5J2UFcjolvsALeWZdygYNiyKQ2yaOgEgyeEdS6dGeuvmVOf11"
    "41UEQ+OgnjHjPRN+RhUKjFKEd9dMA9Duywxro6mzo6olHqWttmWbxktel8RGXRyHBVqJQgkwTWjS1CgThjLS2R6I4ywcUe2JNdzY"
    "u4VQZ08TODCwFRgLLGygjRGMt10Cn0RsbIRDxwkR9mxKIUaiyXSc+mDPPF2VBtZ3NV2IeLZrzxscAyAIzfQA0s+BZ1lXQM88t6Hh"
    "eEAiXSZ4Te4KIUM2MkkI67DQhFH0QqE9NRKdCIxW4XSugMQzJed1IkQhXSsqQYZlzSxoJLNkEGrRM7dCPODOiDp0G2vdZdNsjrXE"
    "jHXGEzyKxAoBT0jcVxmfRWTnBSyZOTXxGDNGITh/0cew4NpsZuAsjLmIEHKMtYyOewbFCDaVM3YK9uLCY5h71CgNTMBdGYdkrQ+M"
    "jDJFDHCmXbsVvJ0nS7mz6Ed2FvGjpTkTkeoQFo5IzwYYjaaekomeFpLqWrRWZZ+ECieNlY76IIdPxoTetRmS1aRsXKCfsHzJiLDc"
    "JSrI9Kqx69pNAunRaohpBFvwOrBquymwNmdpGVkNiZ1SinHXUEfrw1fb+/zXIVA2EnxR3sPFR2vGkGqNtOZsXy1lp7YiLf/8JyBm"
    "iLcmLA00ZAnc2pfs5gZVoM5bPwZbNEAiBSR/CY9SB8GG+TmTD4FNH+iNp/t+DLYX5dHx4rANBIdNiwxpmT6U4NgqE+cHZRufpR1I"
    "E3/ku5qUN/oktDHXNDCb8Aype8LWQLNlWk9Xwmd7aRk4Pd0n6+VBZZWJ0bJr5pbhqT10qQjvPjXFYivrOZxMJVc8iSvwbIoqsj6R"
    "d2e4KkSbEiF07nxBdgunzTUx0rkrgG0LBZpACzTlOtsNkjOHsSif+HDgrTSQO61UTpS0Atr2FleOB7SN2CaVuwTa9tAYSwmUh4vc"
    "tq9NH21DeD94mzMV6VIEt4eeCUwX4bhJBhrDCo7b6ywdhJaQ7QC58Q2KF8lNLleMyI2le4HcXlqHjS3b8F41LAQeK/kMuFRkZS1Z"
    "3mj7WV5E81q8EFyC5MazL2wFo7qU4dzslkkjYtxqmXX3Wjia9cS5PRAmIAl5uY2VRiid+cHcdu2iokmj3FiEdEPTtMYKDRuH12vM"
    "XmnimTNyrhMbkyifMHbZxIfrJlPvSVXSBRx7Fp6F72b3UrHxmuHCM8m7IDxgb9QgPsTsKr1Qb3w36iRegPf2kG/2LaW1C/imeA9F"
    "F4FvQU9vHlRRTPnR37xGl2JOWYP/9tDS3yBnKvbINDoCyUOm+KyDmtTgwPGL1DqI5DKgBAj3Es7sPKyBhKveOSFLBly40Y57EOLM"
    "ZoTagY39yfDh9kKUSvgmP1oBIG5A6ZcgxHEiL0Tcnr4PqkWJs2+HylBxr8nMgWRVoGxjvp6uxYx7Fp2BSLEINI7Lg0SO658XNW4f"
    "EeqQSAz0kNWDxqWOlUotatxTm8YuwY0LvanKwHH+VDZyXGn6StBxcBKKonkheNz4lJzgXPC4PSE6Q9cKoQIh93uWsUrbgC1YQh+U"
    "HLAEoxk575WFZy+e3DM5Fat8cgVUjshQiCxhmJxaxWlYOS6LumKuIb3gcspWxSENPpA5ScjGqe6lsBdtjhXKpf56IOe86SzcOWdq"
    "FyHPlb0yvQh0vB3oKPbjz/HI4SWiD4HuUZSfoBddFYNO3YMm6RIkOku4T8tgdI/IaiDKyoB0z0rDYzDpnqmz8wqodAowjp0IgST5"
    "sekeK+bLHFt1AHUPfZdJNQB1pBCyWlCHUadtaLzFuiB1e+oOwb4sFyMYRKqb0X18q7IPfVh1JW9dZEmi0SyeabVLxl6nY7PFbN8M"
    "Od9dTxCQ45R3aIjyMGzImQ+3boW6sWtwhMxIDfKFFdvwdU/SuLosXfQ6rdnwpbMR6bAsauVZXC7MTqbLq6ZVFsp6PKZo9DtjRVSh"
    "rAzsG7tZRnxyiX83rtVhrq2iaheBhV/ncO6JIfTpTHvLmhIpEe4SKQBYUZbR1EmU+lHs1HavLKjFaHbIHCCanRkd1HjyIEYOBfJi"
    "2TldU969pNjyHRq6u0OSVwyt1hYfQ1Lf+vDtHnma5Me3k5SajtXA233+S6rsmEsAd3w6QbsR5E7sMisgdzrRA38iAbp7jLMRJqkf"
    "5w79WhrkWui2RsHd4ZWTdTxailxaEmrK4KQa1kPf7Za9lBWPT+tZ3P600x4rrMltLnZVyotA8Sx/RaeuBfh4xmWhhJD31NfhMlLe"
    "3iwvKmyWDZf3uGyf7ULmmVbA4CFBiBUV8kPnoSECT1a1QgOf9yhVpoRsXVZk4TEyihWloYuj9wJVxjB54yi2vlaA9PIIsQ/lhnQB"
    "hp4nXRk+71UEY2N7GlcR9PZxUIYkm51AH8J69DyH3auH0HP5vCqOXmrZ8i0B0pO1g20jxgPp5dC2/rtvWf9VEPXY09TcSKgjyDUg"
    "1EV4sfXI2q7UVgtdj5gINsv4/CegD3AgxUrZdlLqRKIKIgAJuu+dpLBZGnl6nJElUYF2cqKeJpvQdCHkXszcTpovBN1DvtVg5MU/"
    "JeBe7AXcwyExQ03HlCJ8Hry9mbiUOYB7nq4J5N7uAHZaYm1gg7fnKktYTRRK8lrMPc/UWqh7/q827l55+RnkPWez05JfiL0nO5Wu"
    "wOHNRz5o3Vs3rUGKJnYAkxIEHwjmUJsx7dCeOh4kvjRjV2CEvQvNgZGUToVKiBLkr4UAOvRvWL5dqAXmSxch81GzFiDz4aVXgTd0"
    "xJKhT/GP4SrgfMqmtYzO98aVz8kaLWe/jYGVM6D4ICwqyiZHG0O20RbrCbqO1reogWLKJ/oA+vyXQZz6gfveeNhBNcqE2jcs65lr"
    "B9tC7rOMG+05BRbuNJx4Z1HZddVg+eH9CzHVZDBml4lyLvvekNu3c/1aBfWzGQBc6mT/bI+SD+GPibqdqpbGGLA/xO37/Fc4QW0j"
    "JueAcoH/HF4h9wMALrGo9zXIxQIMvViAT6uHbD0goM3JOIiA+1GeevEAH/mG14YFRH6rggvoaZQDDog6MqMgQbNokb288IDKCXpi"
    "HyAlhEB16VBFCVTxC5wgYyWcQInFkc9Gov6G5mURCIjk3IEi1vE4Iq9qBzHwsTY1ZFv0El7gb2YxWx9aplY8IiXoQCNkoX1/zoYs"
    "tm9a6kTbqInxYsU4idxoUXiZoFgiNtyrUIISmCA7MKUYP6++CwZW8GWuQ11Ru8Q0XwaT47OQrOAvrwoz+EriKlU4eYM1qFbFcSoB"
    "VOhaFYiU0CMVmklftKj7EJf9d8EHd89iVlA76RiBMPRAEO7y96Fs4JwM8cyFmuYugNkjR72h0HbOFolcy++Md2jqQyL8/KezOFyE"
    "RIhRjIkfUI4R5vzXUTOgjtisq2k0jIEyTPRY1SARGv8vcv5DhzRWSuhy6QTDBi6EJHRZLTV0q0ETalZGrakFuV94bwxXqNZBK2QH"
    "0QpeIZLKktOJB7JQrc7Uddkn6w1cwOoQSxcAFob1iIWpQiyceCELdyfHaV7GLPQEFqsiFz43vm+a+nBotIeal3TRC98QBzqeJaED"
    "XfiIAtvRey924WO+fpXobBFGtwFeIGDrL8nXOANWmNOhNQqtNqIjkyjXWiWKBheN0AoqzqvwhY8/xsexTbVcBENFwkV/KYHndF8b"
    "loMJk9RJHY7hrhkjP5AhJjDFdQw59mIZ7uaNyWxIHAIi9I3xKlT5aTYiZQtUMtupQBk+E4/ivOQcXIEzjOUK2NovFOQG68kUmYJn"
    "pmKh7SvL4imStjgnAjiDD2K5iZpXyYKUMSTyGk4//xUDQhkLZ2VQFpDlUx6NbWdmkpRx/wzIiukRGWbNJgbP0DLSUlpU7Urdbryx"
    "Ug5IciYlloAeRgr1ED94QQ/jsAp6SMOFooRy2KbKa4APKfiCJKxFPsz80IfMvRrkRuVt6cc/tI2Tl+AfhsrcMMyqIIjKH2IRFGJp"
    "sdi+01MKsWniJbJViU1DmjmJBLa0WoFF5Nuuz39OBrGfDdAIiZpm4eoiejVYkldjJUJH5KjES5CMlZw1kInIG2hrcew6Bz+wboNY"
    "IEnLGwlDecGmQItCMrlhJ1MxJiMPftUGWIWhHzpxV10oWO5hFexEmwVUQUxV8zAmadZwh6aDpoGzqA5EsWRpKFiKKXmksx7mKgCK"
    "jjtfBUPROi/9xiRqCVWK0bH3TRGnaSaeECQcs5Ve8flPdLniIis+YsKCuZRLC7rSmYAlBlkR93GNbYoPXPE52Ys6HUIDRDTW9YAr"
    "Kj9UK7kPXPGlVVr0Edg8VwFkIyxC85p5y+Lz/diKqpnibFTxIYOjlpCDJXIh+pJUjQc8SItPE8S5gP54kA7TH4lNN44XVuB7IJMB"
    "k1PT8lyZrWME/jPmmyVcItG8aTjMoPsdWeRXAF1MlVUVxWSNqc2Z06Ja0EVnKoi1pJC3KRqtuwtV7VkhjPYdCnauDL1YDmHtQjBq"
    "YkeV+NJaWIwq8QCl9NLcGj6uhMn4KF0VkRHFPi757POfgYKludwv5DaD7NwRNezSZznKzpM0GoYqlGPoUh3tX2AX8dix2CTWsEC7"
    "Q9zDn/+CmIzpjr7cRjDGSDXLB8dohG99T4mhvJWrfUqx70UZxFfCOPAc3ti+p3Xv0pg/E2RGnHTlHani/lpXmlVsxt3q5NprjIw5"
    "nWZJw3MKdquaP0yrWI0IskjisnZSqYNr3IchndFKM1q5/6qANu4S7COWiLCN4ucRo/MMUboOSYfWrbMD37hrdInwohbEkQLnhdVo"
    "sGU0R8Uaq9j9PkDHCB8LCe5hletHdXypQ0DD8QErPKxpSbtxEMaZROUdSh0YmKNUiwfi0TTISudFetSBPQjuUS41qniPpTiHONNs"
    "VGszQS7goz45E46+acvLylY9rCA/OuEZr4j7qHwbQokgWIV+/Pz/wu8sLWE/HqBoIKZEFvTjQ7pRI28IE3ejBP9I8XZKVgJl+Eft"
    "d2LZBVcxIFX0zQoOpM6eUqjOGjDIvXAyBRpHbx3dXg0WJCoccnJDw0ChiP7IUJC4/BAYsgYL0ujHJMauHUKygghJA+vE16IgRMrz"
    "XSwQxcqwjAl5UBLYmsNYa/VJrFYFoTjIQoIfHJJY7FKUapvjNiuTPDNDc7nnQYqsrs/r4ER6V2oVKtIO3VJdPhZaZO1SdRAj1UqK"
    "OGxfTYkLHUN8oJH29vFhRr4VxDq2ZFds5QLIyL1SuGetEYxZcWDxptokysSaqgGPXFx9CfCNXdVWR47cNS06Uba6fuRIOk7EAw71"
    "Da9J2XIcTdbzGfCOaAMxTP2BqRcgSJZKLd3eOg5IjZNZQpJ4ok/yGixJOauNaZMHTfKteLsUHAVCHdt2ECEPuuSjiE8F26joLKqE"
    "0K5CS0qUcAK4Q4cy26DExZOks7qMKMk3pD4MPyenHj0fniQcyTVYko+TQvxcVTiMuto0juR6HZCkijXgQZEst+tpInVbXbZRJEXP"
    "7vj+qb0kIf5Cgy9ZgyaJ+64KKCk3XBjCjSIocQW1uJLKgfPz/1oFV5K6pBefD1USFVdpHaCkjqtfat1CWEmhUt7EJWBJj7ds5E6C"
    "jTH5iMy7mazUoUzy19Lo1KFMHrBFHS3TWpDJ0EOWVgCZRAkq5U1GJAj1rmdokMEQLQw1qRZNoJ24SLWL6mWk0OgxT7Ykk1QsjS0T"
    "YdLiCrXKZxJ3oAIz+XQYp3Q96oBM8tuGQZHxAU1+/g8MfPs3gpqUwlG3h9sqlgaV7kqHCqEAaVaMaJMYYEYHkvn8Jz6yWGHpCKcy"
    "TGWgSdSHp1XHIQtpch+j7sn9qoszqTHELKTJfYkVVkWbFJFnQP4LcVZFnFRZyXU+Po7IVVkrXozVilp8SNjCrIo9+TAN8/UzVD/n"
    "GurCgz/puRH3ok+KkOOiTx5Es9wgoLjgkwclpUkFf/L1jJQFKcs3Cn7yF75Zb5CZL116jyNcQcrFC5X6CLmW2oiUexXsjEWzZ1MM"
    "4RMyDtliRbmU6bCZioiIH59+5bNvATalPQhTcToyPJ0FxoI6YqIr5JmezhjSRUHbkO0TcE8qpQRRZv/s6MdGdBZjuEKpgMEqMYRg"
    "viMxI4JGyBCVA46udWazYFKKDVQpQ7DO9ge+SFmBP7BWu/EtTC7eeaeZrTZzPO2RnCLKqHKTcuzvBELLnWhCq9x11jLb9pvAZ2LF"
    "7XCWhGFZG0vMAq+MbOjKp1YlPMM57/VBwdopJzxXRcNei2D5+GM0mCH7tQqMJQpUpJwz8FJmvyRyjeKgWFpOAkKc0Hmuo4zQzQWL"
    "pY4nl4WkNuiXBrXcLSvWOpYmLVD6zKhifaexLc2FckcfERI3JhzaUG02wiVRp1gFcWCmWywRDMQKoluCzCqIc0Q1ZK+D5J5LVJXF"
    "ljnt/nwHqQFFOzo+bUaty/ikiTG30pNGdKPbh4YBE9X/9OlG1Iafk2arlUUIzgtH/Xi8A7ujUXTVJ+DScHKiZv+oH/TX+612kT5L"
    "z4FfDfOo2dqRnEW32+1PCyiU9JhZkX8XF6dNeAVZen06s/sdShUllVRRQqngSwebMNfN/wjND4ogaV1KPZEuIeIasdxe1IF+Fq1e"
    "L2lPwmnz+LSFB+SwGXV/feNGBO8xiyn1gErVZRa9SPfy6z9eNv94/lXrj/OvRwGkSlrdXxP8aNE7oGFrFu+Tw1anf3kLzvZ5v9WJ"
    "5kjZ9k5hXIUTQBakH5yfdi+jpHN2GtwUjuXidB68Pu02ochLa4oe0xTBh8i08NFps3WJExF1j05R2j7ZgTn0dl7NXaRTIGulXvPD"
    "TpFdSHGkSzgA+kfebVHxFFid5t6pnsi6AeaC5gN0M7+0y55T/1+edj80sdWt4AP+xGlsBbun3e+a2F+Yx5en7bNwPIvgu/xIwrN4"
    "FEJT2gryO+/13lffHkKh31slcb3XKseM+nMadVWGPfYv6MtL/QXmDF7QEJrh7TnjyHf5aig7zrdcj3EQtWT85qa2H5ylCCvz/PT9"
    "rtR9+D467PXOTukPJjPZ9ssb44cmQjU/TYpxG6h0Fo5fzeBUaqqiWm089gYF7BLsA5D/fq9/6zKao2FWvyM/0daqH1wmnSJot9vJ"
    "vEVz+wRWMsMqdLDS7gbuCVXZC/rwBJmqQtcWXE5C4FlmkycZYxSQVJtDsXAQ+t7PYcNyEVErIPunDuxdGG5cR71+rzGiNl6v1g1T"
    "+vOwOG1nGEYUKmqR7dfxBZBdIZJSodo7faGFNEXX7rPdN73Lfr0ZPcAJgJdfw89gExrzm4f9Dn64az7cpQ/PH1Lv+dV2sAGvPjzs"
    "zwN0RsSa3NYDXY/zJzDORYSdlL787//5f6vu0CCcjNM0gwK3725stILEefnP+PLruxuquc2CWoQhFKAh/dZXOBUcMwEaERbRa2AX"
    "ccL0CD2Sl5UxwtQHxcUYCArhq/UDjCrgvDHjhcVhSc3oX6DfQAWKleu5SqnhKKV1jS9BcD9vtnCY6xeEDBZMd3MjsFZUsQ7DrWY4"
    "+ebuRu8HoFUGcxl31rzVSb7B4VXfBHWZdp1VVoLDD4klVQgDRX3qPEF8tQnOLOxO6xR5SlRLnd0TJDPNr9//cdg+/OrrkWrVjQJP"
    "3nGUjIrTb7bN7193b6+t8aqG8237EGnERg973mlvPXjwL/rTxmHrq/ad+/fMm018s7l527zZOrTo1DNzkA3TwYxQwgcZYs8/Hkf4"
    "1OwP47N+awfd52G62gPUK38s4ORJ8xiL6ITHeTqGMdo5i3Ngu8ZxcdE5pVvSHZSXRzRgHSBUzfX1FASU9eNRwKIeuqYkRasf6KoR"
    "Yq4dTqfAV++dxmOkArIpYPzgNNwjM7poSEsHPrZNDQh7lZkNLDS/CYtSqBSN+fNoGIfNfhOP7CjL1wnPZz0fnEJnOyAZZh9awEJR"
    "UrxwxBewpcZ4iwDs0TebW/dLL81QvrJmGNfwm1fPDiiczH6IBLOp7rkkyEwLT/dmv8Ca+7jDsZFBxuwHlpJ1iR2j2mAp4G+usld0"
    "cNp2shvQs7W1ZtLNgulpM2sFUa8Nf1rznazJ4xZ3V+/1TkwBqc9gHtAMNUpgtfQ5XFQ/yLi8kHr2fFZQT14eo1YLksHXsJ3yU1NP"
    "pvohKym4DAuKjIMGfTc2Av30hECpOu/7tMKAix2Mwxx2XB8BPNZ5gA7n3IC0e45qynM6tlGIAXrSzIJtoAeKGOL4xTL9tb0JQrrg"
    "ZRUgLBIKKqQLTFsWB/AjbhEhMLcuQ5B6SWZSW3NjbU2/g/0Hc3KWxsPGRs9+2+lPB/35rcvXmc2xn61DJ/v6xe543Ozjq6N+a24t"
    "rIe0sG7+6zHq7L5G3RnMYWO9wSLDTbXkH552RYg4uEADC1gvqoj+2przqR3jPTYwQJAmpzf9nkqLdSnGW2SSecfzMSqV6VYXoToW"
    "BJnZgGrpchp4f0P9RmudIsUieqoNHV1hQH02Q/BWJAIg+TeaIFYneAM1wLRFq1WcZul54zXkRdR2mOa9MElAbgUmD40oaTWRLUFD"
    "N9Aq+lspGk6fJnJTSXdjJ/lGUd6d5KuvWpf4HrYjSBY7WTsCXgtG73gcde0HONY3g6ytZT38Dqu8TwdeHySUDLZq1j7P4kK+tYKX"
    "x9/D8muTXU2EPn5RVlxAc76D3dz+EF20YKVaK/FNmaks1taw+WYooSO1hd7UqW4Gl6oZnRubc6Abpo7vaLFhh4vub7A+JY62zDoj"
    "JlUvnKJTfNW3lutvzFzRLIJEm1KTSKI14hAN9o4RfXlZfNOf9YmmRe9lnVBM1kmM18mHLb291KQk6PI3php3uMbMqlHVlu1UFsm/"
    "/qtVcGMC0n1DEjMwFb+n2WvDelECAAuZEXPevzvt6p0BK0iNQAQDdMlrqUIuNm1yseklF5uHHavU+Q4sfvReBvEkwL/tiOlpt+DH"
    "sZC3bqIaSevk/SUsoE7/GMjlwSBLx2NFBvsBdcqug8rJKRUuin06l/Pus1nTrhCkM9kjEeyR6Bt/LrVxItg4/hQgLnlOGk7Wd/sE"
    "qz/gfsySlXqCy8lbaeuna7v3aFnSfDSOz9KLurH39a5Zmm7iD0ozrl9VJ48UNXPg9ZqWVP2Do1khdpO0CLQ1e8C9jpuXyCTEH0EW"
    "RNOmzuPhPLAp8W+XlPC0rgQc+3enXSCS/+bsGpTbpbBNR31xY8Pmn/9g6BLwSlqUaiI3DYzUyylB7bWs94VQhpa87PFG68B7PBH2"
    "qZFIM24knz4lqhPC5yJ4ida67dx4d7q29m/ABwBlwj5sBHi6pWMMZgMcR/89EpLo7Sw6bLw+jRrEsjRSalLDqqxxE+Wymw2K6NBA"
    "n9LzKGv8K1nzzOKPX1PNwx05sTDMS97AIcQCGzen6zcbPLJAj6wZ+f2pfSr32lT7p0/PhibJLTsJpW/TfeQg6vXyIU1NNCLW7rso"
    "/PA8nJpxL0ZKelWnQjQiztUIy7AG4F2O74DZ/q5pTS7l0FJqN5LjESg0zghwENzaHswuNqsdw6ASa9lqdXi65ihWstTImqxk1P0d"
    "oeWAFEahcDp9tPyCQ31uLfRstBLPlI3+gXgm6rOZ9Hhk1TzEh0+fQv4z4D/5qGmlD0euKto+j/VhrAbh8IZstOg9nKTqbV9eq52z"
    "m2EUW4yx4rQsHTlKNWnbjN9y6+iH2z58uqwc44KA10AArMkUZC/29MRBnGXoy5esU+uAMmq2sf1PT6ER6MaKyY/hg6QIKD1af100"
    "mIPImTOg8P1hozIKzVZjEhWn6bBts5TSAdk1lnK/q5X7aoTGnJSZoe7lHLgdZjEU8WJEiub9YH3T6C6QWDGbV142zDrZbwhmCeVL"
    "yAM7uy+07iACQdKZnw6931VsCCT8+n80e5038aenraSAX/c/bd79tL3Vgp9743AyjYYtLuHW12Tx00xaPemP2rxmTOTDZbNQJLr4"
    "dSTnLZJVJA7ytGOx4iAQUxXAUSFXTux4Bnw4sIfIjMsuNtXIIhLuSykoSVOy0rKuLGg8IBJZ1cxyBnEQBmmQd98fBgM8C8ZwqJH6"
    "GZKGXRj/RJ88ZB2AGojuBi0EnjQYKBTdZQ3sQCGb82icRw3s+M6N5qDbzLohFwKUkKKH4hjl7eksR9GAVcaB4legMBgebEtrh49Q"
    "0kRg22LUnMcJlHRxKU28MVhbS9pyxgodbqZd9aqpJAiQgqHgVGkodTFQxFhkrniuWM7cmuqhIiS8vOKcZ1DrOhuWuHHizJeILsAx"
    "ocZ3Rw8YnfDniRJmeNJyJQIsSkM3Ayh4gazG4NfmeDIUyFsCGhll8bRAjSs00RL18ExKaC5QVzW+aCYop6nNafFKOA5qMRddWCTf"
    "lOWBnULJl5as8L44lIV7Oe/Yb3eKf97qwZDpZRTAlKPe9HEIc253bDpiUREyoZpySQfznk9ojFHvHizLiiu0Y7fJ36A6qbRYVgEM"
    "Lsj4cz2+1uJRnVTzCERkMoLKWjEyQvU1XjITngRmSjvM02nRHZ+NjAxcSCfCWUlsUXkyMkzR6cgnKmejxaLyqTko6PD+WUVlqPFv"
    "KSo3SS6QEZHL2Q4roVtKfh6NusLCPQzzCJW7QOkQjAn4nGneuZwWnUvssqzfQJAF1ekSTBXfvzjZLGHOWlI9xGvgMKkkGy6ubR7E"
    "Cb7vXN5ixfVTYSc6l5WU50iEO5dx/kZXHU8mqIUtaGmdhskQ7TFsHvEWi/ntW4YJxjC/oiLuKN0lpTnC8H175HsKpeetIEKRx/NF"
    "CZFHVAjHgNcCprcolFlxJJa2lxc+lrFzpabTu4MB7Mehaglqrq3W8MfXlI57EbXqM9vCpGLC68uZLx0PX/taHf42S/zlwqDNg5xe"
    "05vHY1kLwSweqp+3UON9QNe8aaZf6iHTb2jFfJvmaj0F7Ga8R9cynZJ0RQQw0ExJMAjGwYxmpT0tem30HprCUu7Oes1IvTZScgRc"
    "F1oB4tH+lpgKV1YGokfzSpBwxEkeSqN2gO40odCiWiiK3meewgpPYSrzp09DUwByUKdp+sES55F6pclDayD0t0wxSkQmT7rNmJt0"
    "i+Tqs1nEMGqmrLgbm/aqxsVqqKbdkx6wcW4RJnOIjFmpQHxXKTB0B1YPGzB3UEFaW0HaTSsV4LtKBSkPcqeZ15aVd3O3LJVXxnxq"
    "kg66g+r0OJ/LUzKGVzVTMuYpGciuNWu81NKeEfglpV773VJOkBdKWfPTcJiev0pT0YM626uLtzb8HnZg1yRAmANVlp3B3MpMB/2g"
    "Pz07iod4DxPwbeiworI7wuFo9tOE+z7EtLxRn6OJcTU9UQ6XKKsiHpp8WMwEf7hV0lbfUVvYDJMecoKARqYLE5TLf84F9tV8qEFc"
    "W3Of2YQ/joY9XlvAQtzY/PTp7UlTd479WepH46GVCvsyo18Lho+TWsP3Jpn4B7BUBSejOpLaEeOcrLElgq1IupmEWpoeLBxuRP6u"
    "Ge43qj00maQfAA6FPjsnKApjXAHrCvM2mpCS6tE6XYkw7b+W0wnYZPV7qha+2bGqJVojSrQn6NPWbaMREV0162IfMeNil16bbweO"
    "ExiUBP+F0+4IOOcR8dW5hy143263teRyKEoMo8GIUDruRSI+yTFXtDpvym+gHpydysRSF0Cwtt4PTpqRRTB67WPgKT99Sk+CPv7q"
    "BxU+4f3vKAzy3sEB5qRJVnrkIOIN+5txeoy2YrwiDvGuDLdLdEJX8WtrCyrVqTw1N7jmfZWkUv9ct8BlM3ZKZLFXem4TEwKtQCUA"
    "DGjRVEPIRfjJ0opcoirKcIt18wJrrNrn+rFSvac17JkndFipnyi9e+gDKsSktLo8MI3zHcW58CdLI41tQIXUFQY6aXWgtWp47DXj"
    "HyDae5ysduuN6DPa2/QV1SY7EqN2pz3ECwmEut8qbThn7M/tE1X1XCvmgvLaKl2iMV0y8otq/e+rnP6OunO7RasHzow+oiT15XCx"
    "KjqNooJ4+Ruo6T9Q9yxokx4Nm32C4lknvWy/pe96gqz7fNhU55Tsl973mqsuzaPFRJJO4RkW+hLLpDbAciixQiIVFwEah8loZmY0"
    "7UYF5ImN8lAWnqNWwDvEAdmUcqd0H0u9Q3GhPDBVKkqXU96hkhsPGSXi/7vNZuIfCeSd2XYK8lCFpSFQHHQgQwoj8enT5TwIkVFW"
    "8n2QwhOFRi7iQZDDAy+0YIDvsUY1emEPV60ZQl3EOgX0Oh6jOd3CEZSC0lJBqvarlpOXyuGGX7EUNjkrl8EmS96MwaBuKajZm9fN"
    "r1Vaj8910pDX0yteByD5BcPgBESYJnDn3rUw645lLbCqxbccZrwcxuXlMOlOaRxP4S9PeHPorWXIwz4xI37r0kpHLZ6vPPzNE28l"
    "J75Z8dWzaIpOa6aoXEpL7dcKm1jdtUoc99LKpp7Gwhp5EZpT5xLbuq/O87dqsND088Ymqf18yyGR4ytECwtpbPohSprTUfPSGQM+"
    "a2FuoawQuNlxVERLhyEok3ThS1j2TmHdAbXxLry4m+HC26dwCL5VF/Oqy4JICY2iXlMSmlqOIS/HFq3FvKvn3Jbm5uueldAHUuXs"
    "LCYyepXmC9fhjthZWDqe7qDXjsQA48j6gmPXzWHF1IgWHh2OFu2cClxFja1TQQnEWLj6GgDT6pIMR37BSIHptOnNSYyMhxOs8jLX"
    "NIZ0rJu8usOkrDpExZ1XjKs2ylPgTnQFTeripAsT+FSH0G5Y9zj4Wl/sswzo+QVBkJEs8Q72fl2yjuYi7aqQ9XWV1a1O5ZXhCWmD"
    "ptO3ro2SZdwAdbyPDkV/UqmMZOFeG1JwWRY/6yttincR1zSQ6/erObfsnFvenFuHHaAc0tPXb8u2WF+0qpG8dq/fHY+t4KodAha5"
    "knfbzrvtzbt92KEb4q/bX4/4Ar+Aw+DGjeR90c6n47ho9tv9FnTtMBB9qLNA0HlQqGO/VVbPsc6119ZJiINIu2Gb1AYHEQ050u+0"
    "q5oGoiBQaElBioUASKxuOQjbwayb9eLeAhFq//UeGk+xDIVXg51Fuo5qajljht1YH78mMZwuJ80oqMv+W+RD5lBKAP9eMoPYmWHH"
    "8cL4xBrC1wgVkKMwVLSAW4PBuZGvrQ17Y+maGYGm8HStDpZO5c9aAVAheQPP9ADMGd23ZWla9HtD2IRsPT8drMfD/mGvZ2lA3U9K"
    "MS2bcrK2Nl1bm9zodqunak9qnHIPb5pibiLrNZk3vGdxf97qTNWewzH8abfcElXTm6alRBP1Eikp3tsKNcV0EJdziErzQYj7QSsJ"
    "/blvHdGI7r+2s2j6omb5J+svkImiq2evz4aQMukgCoyb+t7HzHHOW61/aJRvKKKTA04slmcyr3Zh+Ip5RnItw3EB+ReExN6iOjoV"
    "hWQrSGBFmYLYco+KqqaldYWJnaXlWVIejT96UpgCpDbVMKwusmbG7Ns6BY17fNkzr2dED+hwTAZsE1LIXJL1Zieaw39SW821aZB8"
    "wXHhIflb7rkgpCzulmuPV6/WfQ3HQNbL0FQMtQG4GFpAwHEmZeMoS894bQ3Jeq7vwmCxpIetXi+cW4uQJRYx09CWje3TMLcMQZTN"
    "Qp+v5/owwPwL+Bi5sXPv2eJm+UpTbK7xA7PQc/yNpjPIouPGtiaIr1PVQPl4IPQ6R3sf8ue+bi+4grCrOvGznZ+e4Rl2zdCo6Zl1"
    "Tbah/q3mExb8sNUb4t9ZqzfrLD3A9GFFh1dnqIx5YrqRt4/y0lQ4rKdzEzKSDAGn41L0Gb9yMUOVQ5dzaxJmH7y8OqkKdpXbWtM+"
    "Rj0ESVQLJr2fZqEVy+SnPSGuSVUu9ea0TkZm9dR9U6SYHEcjTQZa2I3476QfQFnl2JcDGsNYpDOcZenJhMygjEXtlfZxEvRhylFx"
    "krTjYa+n7qqBE0toHNJ/AKGidi0wq3up1DN0PBPXe2MTr8s//j2uZXORoUjYD6feexdH5UUneZQvWPVBMWqWjC9wJwyS6iC4bKpq"
    "HTrk6J6BFB9Bx2sKzaOxT4pmhxxfjvzvYypAxvySZYi3S9oDc9mMxQlG9mdVTt20JXrbv/eWl4xWLSbIDvEiZyBO6Z3LUeUQs5lK"
    "z45q1p36StnpMVae4WWV2X7RHI1jg2H15Psb1B1VRx8vYEmVzCKEHiD06MCWll9jYy27SI/xHjvE8XfDevhbq007nVxwiOurwmoN"
    "5bvNshWMHglVBKrcN6DMuLa5ZdOiWYxtiJOSeYSaEdvOXaSgsyQdRlgnZCD19o5rm45OGhjDE42y5VUkj6r1kLPlM3Jn6/IUSESw"
    "ieqcHeMrFmNMwmGERtxzJBl8K1Hby/IIUeq5WCx6ctHGESqq5RFrb6l3ZROPeSBX99WXB+WqYAM2F6gj+apAbiMCV3vKL2mi3KuG"
    "alf67w2z9+/dm149x83DvhoLZZZcsUfi0i4TDLDX0fZFdZaKqPUf5NOyUWabsgfGcrSk757T+reLXDqjPbEThJx0F1KXvqx4VnKL"
    "keKxbtrqCyRr3zRp6grLWg2Tw2OIUbi12gOMESea71s4PxRTIrcUBpCJCuxY9FLKgS47peCzVQY+0i+k8FrN4xkX72ak5Lz0yhvS"
    "nNzkBkc7sleKydYBsQDDQgxnMD62JONs5i04gLoJMgwx/NnU+3o8asajZqZ0uB3Ui2i1WM9XLIu8Qh3R0QFYW/Z3ANKXyZG9vtmL"
    "UXse4Bd06Q1grkmbXmayf5pRYkWJGSQVI6dZmLvvyrBdadw0IXyfHdIIqh7hbW/VzbQIj/N+wLSu/08N+F97uo4vG5f0hP8TgLhO"
    "42QcfdzRr/FpfRhnLLZ3CDxvkvD3+T9ZZaFrt1Ucoo6djNNzDIBIEXWWVaSj8jA2anwWmW9WNJ7GsGj+CpveljqtQDq/allZyF6F"
    "r9A7DaAv8bDykYLJ+Eqkz4QqkXnKPI+HxWl9NvqsslWGaB3jcCIK1uVKPV80K9BpGN5N83YSJ+unhBvQaWzsVKZi/WOH0JU8X6CC"
    "wTiemi/slb9+HJ2GZzEOUj5J0+K0nOA41MOBllNuyZUyKBhsnFiNqB2eTmf9PDr+EBfruiLfWjWVVktKwrP141lRpImVE4TgTgOY"
    "rajwrTwVEKpxI54Q7m9SlMY8P83i5IMzvDGWtn48Tgcf1mlXO19/XEekPhj5LfNOzdHmxsY/L53qEBg58gSGc6lBgfQz8xFDe8Yn"
    "F3rUKgm8OwdGps0jU7N5yhvDylDZFOXdYKV1dgL+z6juO/qdrs/aUDpZWwWi+1UrcHIAtUZmbP3qOY9TnEU0wF+Szd73Kou/n/zN"
    "zuE0r2PHDLMGeZbl+HGaxmbOFi3jzkk6mGGc7DxGn/DL6hrbXL3NVFab/LVrm780p0zw0gqQCC9PVllaahTTkxPYYktbw8nqKa81"
    "kqcMirnKgqekbtuqRSPCb5XYMGVgsaFEGjytgyN7SRER7uKNFdrQgQO7mRVjWfr+WnQiqzodxxzR7pC5bG7e3xhGI1/HrWx1pNG7"
    "xPF/sxzPZhI/yifHQj5g0aF+fgpEch22GbDKUOZ5Flrn2Sicuid2G944e7yGxVjMXnhYAS8bsJjpqGU4fGkriabhEKEuSsnkrZ3w"
    "BA6J9XM5e5zE+EVAnisZ8vjHyJcc369C2834XZFMm9G6Usa/87OEQV9LA8ovr3KAODuxk6RFE34CB4GWlsPWl58UPM1XOiJKWSpn"
    "Q7nI8qFQ+r76aVDKuOAYUAMFP9cxlO4Zxg4pj135bKilDHwyLKQPvg0s2a6w5ZcdQdKXVdrMKa/eaJXvCq2WLPXNniI6e75Cqynh"
    "iqyqTr4aneS0HmKp1/dGnZBBWWt3Wt2u4gqvvrUq+Xz7q1q4Z5NVEl1pp1VyL+O6eBmsuwKcjw5p+YdEqUXi2ZJTW6/xus1pHVUs"
    "vjS27mxMEG72OB6AvPpjHGXNjfb2naCxAf+1t+DHZivw8HMrZdxZyBByeOHpR2ug1sfRSdHyS5hRbVdTYOomHsnMVwF9alUlUl/B"
    "pw5fMP+nfqD04pdocdXpiyppuj7QYTDm81ZwpkNkvCb1E6ukIJeJm+F+GI1U9Aw2e+GQFu85AEfAATgOK7EvxuGPFzXhMW5szoP8"
    "ND1/oQL253UJ0XI+POY1yUm4Op0CEjC7+jJ5gmt/UY06oOHSRNA14LFHF6WuPhH9n+lsP4lChHTsY7AG4n6PaLDO4qFH4315azrA"
    "oWXlc9lmmm69KSbIaZTFZOWRQ5uCaIJB5d/32e+5w9FfDzEKe+ipYnjEk0T6UAlyp4KHnFXsptlg5UghIli+xVzb24U5bnS72q9R"
    "FyI3ItjqptvmgO+QaYRfp7u0kmE4Oq5aFW2g1tYKuUJz54O8x+34Z540dgS8luc7R6vB4FgqpFd7MI5hIr7DvYe+gRiTHWapGUnO"
    "Z7jrgxjdaYim4jPaL8sj50u78VdhkO+44UJNo7p9VgH1W3k3Xm8m62Hr6y3TjEE3+Zf2JuaOv8m+GlCiAX1uwLv019lXyTq+TdeT"
    "r+S9BNEiN62uais1Zj0JZpWI9ZM4aebBuEWB12UOmpdI0TrvyMxwfdaZBVop2GfFYp9013bYzItR04oQotXxT5ut4BmHdg/eNJXJ"
    "Ynvwscn2ny28skWDHvXcCt7vkx8tIrMHfdlR/dZhsHm3NT8btTOCQupejMgT6FhTrcFpdJalCRHjPi7YELZpOMIt4n7q4ylzHmbD"
    "PrlOQ7dmGANcrt+CPqU6hBV5NupcfpyMk7zTPy2Kaefrr8/Pz9vn2+00G329tbGx8TUk6QdMt7c2AqHK8Ossjs4fph87/Q3gR7bw"
    "P3TpHI877LA6D/AOFlr2vo8g1/3gctjpP9/cbD+4++Be43b7NvzZ3tvcam/d3boLz5v37t6/3YDne9v3bpvn7fbG9sa2Sb/d3t7a"
    "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"
    "2jr+Lq68caSqL9g2pRKu3MvVtox08xobRqq5znapZl2yWZYZSwhfW28tsXCoOd/KA7zQ0MK095q7g0q/9tawc1+tQ6tsCl+3Vt0R"
    "VMn1t4OT/Wo9W2kjUNeuvguogmtsgXK+Jet/meUOF7rAdGfh2HK+lQd1odWPae811z+Vfu31b+e+WodWWf++bq26/qmS669/J/vV"
    "erbS+qeuXX39UwXXWP/lfEvWP5ojLB9iTHWdseV8Kw8qJV88mpjkmuufSr/2+rdzX61Dq6x/X7dWXf9UyfXXv5P9aj1baf1T166+"
    "/qmCa6z/cr4l63+5GSUXu9COcuH4qpwrD+0SI0y73dfcCVLDtfeCm/+qHVtlP/i7t+qOkIquvydKBVy1hyvtC+ni1XeGVHKNvVHN"
    "uWR3rGLry0UvMfZdONom78oDvdRW2G3/NfeJruXaO6VcwtU7uMpuqevmqvtFV3b9HVMp4uo9XWnX6K5efd/oiq6xc3x5l+wdaciw"
    "Zvi9FiC2EYxTvypsqa3RClkXD7BKfs0tU6lt+db5u+zuqlunUt0KW+jvosNLrh6WNvQ6FwmezNdu7Jeuz6tcNvyfNA5XXrj/P3f/"
    "2ti2jTQMw9/vX2Fns37ImlYk2U4cOoqexE222c1pk6btxpdvk5ZomxuZVCnajmvrdz3f31/2zgEAARKkKOfQvXbbrUUcB4PBYDAY"
    "zCx1E/GfiImqun8xqEur7ytVbwnmF5NtaxX//47xL0+u7fX//2EYKKvaF8K4pPbcrHcb6L6UOFtq2P+jx7w0QbZVv//HjLqs8l4I"
    "3ZJabLPebaD7Ujpsqen+jx7z0nTYVg3+HzPqsup5IXRLapPNereB7kvpsKXG+T96zEvTYVt19H/MqKsq4IXwLa3TLde8HYxfSo+t"
    "9b7/C8a+NF22Vwr/R43epoJdCOUtNKrVureF9EupdAmt6/8aHCxNrcuoZP/jsDCdhPFyIibVuJXSiyreCsAv1nBS11+o3/wPGPfy"
    "qk7q+0sVnd9y5Ogp8fZ6d2uRKkTYSUulK3luvB25Gb20J7bvM4a2pGN0swThfJtRtLe6/8rE0lbJWQPkl1DQbdTdf+LQliKsW2mw"
    "v8PgGu3QvzZptVJKWgH8IrJaWh39Jw1qOYJaXsf8rYfVYKf9lSmphU6xCtqX0NCSWuPvPpalSGdZbfA3HU2DcfNXJpoWCsAqaF9C"
    "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"
    "IR9iFzmOuYRuQgYca+HpNcJMsZW7qPToW41Dyi12l9nMBxwimlHbwfQNKPkgXFhZEb1SYyKRUu+iE6U07kQubpQsRsDcmskP6bhN"
    "qUrRHEpxf4c2UKzxOgb1p8weQ70omm5GLJRVUj/6h5nY+iPGmtxVNuU1mP/TOAm3zPE393Lr8rk6/QLd/IyhvGhoBnGwjc6oXBDZ"
    "zLMwuDcU8zu+Tzw9FRSZLf3zts+gOrx8Uhkl0z2FG4MDaahOa0YFqnOvlOrPq4yjalGG/MnYbH41/qRlIMQID7jEJaQ6IeIYYG0+"
    "qWfkctVQFfNk75x8y00jIYuRAIEw3tv7wTXFYPLNSHu94VukLEW9rXSndofnghDDJ69v4yxOynueMlX7sAf89IkpYhloDpny2vjD"
    "HJDci4clcinBrvovUW/TV5VuHNu22bVmc7H16Zjzsv+lAP+OHx2z4g3pw/OMteJAoT+NXtsTFaXOZjGUEii8j5MyJk23P3PW1iNw"
    "toa1Cy/oX28xmFbFVgaq3bo61lSPeDQfHpuvRP4BFIYB5IezaR9pSbo3vD+XiH4SO18XczKp1983Vixl1DgOLgfmvBpBT9gGm/6R"
    "ZfA42H4LPw2s47mNUXfm04OxfHfK/lKV1OKC5CwCzqur4Xixo5LpvEYxDv8YkT6+K64gaVBwkSVJ9VnB1zcYqTec3oqeRKTiFl+Z"
    "WnxiY8dFulWIcmyKnhvvr7Hqvk+a4ha2cAJFu6Ev/FuiUsRie5kBEWYc12B1vFMh0F+q0XlKA3aBcaWP1LJXo4FabLVIULFMm6UY"
    "W0kRpWP1EXrtVBfDo7F3nHK/eMVoODbr0LF2FA3UX4rvSPjX3zHyhTuNyqRdoKvoyBuReoMlTLFd/1DDIpi0M8WhqNRqmqIDS+2b"
    "wQ5X6KJImDvGHblJSliM8+WC+NK03rGQWOpZ2Qdgsni83yrIqD3PRe/XWswrn1qYSn6v+5Apy2NFpO0je/ZPJkzVCGTZ6igtrk8c"
    "lV/XF2QuvpI74tqabgguPzSkz6FhX2v9pmVo7eP5EdoonOps9ZRJrDC7m/vdzzMZklp4/+vtUHrEEuUI8/BdJ+0pyWH90Ts4UV07"
    "oAPFN9QYcnnp73umih3+SWLtNe2HJg11eV1MaeXYRafvP4OkqcBwwSt0iRfjRyFrMkMeqswOcPuTPCH+8F4oU2xAINL9MTdRsg6+"
    "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"
    "28jbdHHzR4N8r+Mwy5BTIOuAta1Ua3Vxm+O+tniUu26oU+9xP9e5j+WzrmMua9pQi5rraCTpzbUA/XHgmC9dYaldPMdQl11A376F"
    "CNjKgIfVB7ge3g5OnHV0DHlI8UXSZlzPI1qjB5QqSkWr6DvquadvI56rIJ4+Eogua40k6q03EtNC2EARnAL5FrZxiG9ttvkwWZbg"
    "Zlu6ubi2/Bd5YpfSbqlM9b9vbe0ye2vx0cSMO82dhjxqdgTVObeKtlaP1qXO2nJt8cohXfjrnEaa4HWHY0wKbCBnddbfqGvd/tg3"
    "LtaRkRch5h3cnutyaGoDwnG4Nti6zR80XQSd+IHU7MPxOJqlUerk9AhzzgaARIAW/CJ5t8J1skKZV55cjGqoek3RtyrInY0B3cak"
    "N54UtmFU4rvwcG7ULNGPMdT5uEDAq8ABFKVMMNRMq0pBCreC3a3tx6cLBB4txWj5nXJswJ+pX/f2C2zS+V64RjQLp57qkM4B+gvI"
    "kL3Wxo6b9X6CnVD1PDyMcuH07LPrKKxK1zP5qn9Zf9HstC4vD3b8KTsHEiaTFJGT7MNhk0KbWUyOTy5l6C5i/AqlySKXArR8XQWI"
    "xkkv8si3b0NIKRCm0e2bjXdFHT9BblhoWNUtx0XNM/K/kbpXdWdnnxtV0yDDm6qwXN3b8UwLFBFrzghFo9CFVR4BGjnwtV1hUlKr"
    "TeKbTW2aRq2pmzVu27lR875Rkmk4REa3saqCVRkCKuzszQylwSKAulQNVygNma402Dt9DQ+FNLNEcBOIvyCCZ7pcofV6W2E704Rt"
    "2Y2P5Zo8ovpfV9guaL6GsJ2ZqpVqu75qdaNGlelK9Qqu/J9Dh850ceouS0FUVTRdthiNNaQKIUWw+6Hc9ejasinwnkS74NX4Us72"
    "NxvTSVEaNkTtR42dTheK9HtXqIXHc76KKQ9pdj3cCYhXsmkZd6ts47MeHR0aMgGPfEi4KAEBToLLcs2vV7f7iSf+Rh8tv64ViApr"
    "3VBLaDR6VdDc2q9JI8ZdjRjJxAKDXAzj3CA+4SJ0ILdgPxZzU+ioEySOaTgdUd0TsLbQGhdrbNRSlB93zZsd2QXlA10JfvGF1rZ9"
    "n8W4B52S5m0W5/faXc7OjsMFaHebqaR/iVL7qEMXLEvxwlPXrMdmAzcp8EbmuaI8T3Zr/aDROV2YkibVneVr8f2JwIHkADzrXNZ5"
    "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"
)
# --- END GENERATED UI ---
