# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.27.1"
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
PLUGIN_VERSION = "0.27.1"
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

# White tab icon: the Spooler mark (a spool seen from the side, its filament leaving it), as on the page's
# app bar. get_icon() must return the path of an image file; SVG markup or a data: URI shows no icon.
TAB_ICON_SVG = (
    '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" '
    'fill="none" stroke="#FFFFFF" stroke-linecap="round">'
    '<circle cx="11" cy="13" r="6.1" stroke-width="4.4"/>'
    '<circle cx="11" cy="13" r="1.5" fill="#FFFFFF" stroke="none"/>'
    '<path d="M13.6 7.3C16.6 7.7 20.3 6.6 21.5 3.5" stroke-width="2.2"/>'
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
UI_PAGE_SHA256 = "5f249f5b1c3b3cf2d8f1449e9b41e509a6ee7eb8e0b6bea651d910c7d712b7ec"
UI_PAGE_BYTES = 1109706
UI_PAGE_Z64 = (
    "eNq0vXtz20ayB/r/+RRmrosHWI8YSclms6BhlC07iRMncSznqeiQEDkUEZMAA4B6mOR3v/3rnhcoOZu9VddVFoGZwTx7erp7+vG4"
    "N60m7e1KP5i3y8WT/3mMnweLvLxMP9LlR0jQ+ZR+lrrNH0zmed3oNv1o3c4OPv/IJpf5UqcfXRX6elXV7UcPJlXZ6pKKXRfTdp5O"
    "9VUx0Qf8oh4UZdEW+eKgmeQLnR6hkrZoF/rJ6aqqFrp+/LG8/s/jZlIXq/YBepd+lK9Wi2KSt0VVfvxHU5UfPSim6UeNfHNwUVXt"
    "R09Go2fff/92NHr8sXz65H8ePOjWsqym64X+6MlsXU5Q1QMd6Xiz0JSffn/xh560g0mt81ZH5XqxiIezqo6QWz6oZg/0oKE+tNFY"
    "jeO4PSvP06Nhrdt1TdWkTzSN7EG7u8prqmuzU2V6dq7qNIrTJ/RW8EPvSOUpyg4wkyfVVD9to8M4TdOjo6N+v5N8JMmH/X7UST+O"
    "nxwdH2+3e4mP//2vWFVSedPmddv8XLTzaFyVP66mNKBkHKvGjjFvmuKyVJM00qpFB3mMqR4U5VTffD+L2nhYPjngLmHME5oPdRTv"
    "1MLWsKqrtsKcDuZ58/11+bquVrpub9Xa1rkY0AIv+EVN06d1nd8OioZ/1Qz9vKGppyGOzyqu8sG3+ep8rFb3ZZ3qlrKW92U9p7FR"
    "3hx56A/WibLtAo/V5V5O09ZFeTlWo/302+VFtRirq710aWfc7/d6Wt0iM7qiPmy3c/ob9/v0M2jnujSPBKKTeawu7k5UW51y0+oG"
    "lVyY6YnVqR3WoOGZ/lwdHMVK6/tGK5XSeE+Qe0m5tEQ9KvBd/h11UZ8dnuPtgJ7H40cr7NaXZUuLcMRQRotB1RIAv9O3qtYz/B8R"
    "jPMv0qryp5Ig6pmmRP1ttS5bm8QvetotIaBl0+Rtv0i5DKsxr3pK4FjyEP9i98nmikpaD9pt223Em45y45hgsdbpxwe/X398qa7T"
    "kvYxIL/Wq0VOc1hrJTuBZ/Qopsn/cUUAepI3OqKvVUEf//4sOnt68Nt5TFXk+k4dhVbjg4dHY3z8qrp2H6vKl8UW5C3cbeCRb5l2"
    "nSue0W58uKmAc3bjZExTMNF2u/TMBBSNbJkF5wwGA96fDg+lh8PysR4sdHnZzoflo0expjmJuNxOraU6VRLi6R3hQ1PrVM+KUttN"
    "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"
    "ihLcylxPUVxGuHmj325DzjL2ilXXTw0OdmvfKCLOODYAJSv8L6Ol8wmBVuV5riGpTHerpim19LxRQTqbRaxstdJz7UQ8uGDCLvty"
    "mKurDvplPyT224JEvPuoTM52GWPOa56XjeoEZP9Tt2n/t+7fsMglq9nLXf57Jv4e73qzk11pRXvIVrQXuz1qI0jG0XG8eh4fTjYP"
    "o2l8f8P/+GX0w4fTX3948uTp5w8ff/zp0+jJxs9Psifw30/4z/vz5/T/P328+Gnn3ZtDSPrwNF3NVrvF542z1aPTydPtR8fP1w+/"
    "/HTxYeeP5Kd3L45/eNL5efen87dnv+/8kkQ//Jj9fBI/+nH7l+n4Y34yGD1/92z3Q/b61cc3qzuvs52fpr/+9mRyfrrzZPzHkzdb"
    "D99kOx9/+f3L5PmX7ae7w8sfo2L8cK3785uHq+uvht388OPDs7cPXt7b+P3V1uDZ6qPV1dUV+Pfe7tHPR0f3Dk+3X64cr65++nV9"
    "fTD9+UXeOYy2ftv++Wjw8P3P2WnnxQ/x9ujT8PzwaPdhdyU6XD0fH/0w/v3BT+urnz/fe7vz8u3q2uqDZ9GLwVkRf3jy/NdXydZh"
    "9Obk6HTt4/MPv79+cvlk68Pup87p863f0pXk9fnF861n7x79+vvKz93t7eej4yd/nL4YfFpJt1+ONs5ejop74276erB9Pvzyw5tx"
    "8vPPD0/W3/88vZhOX/z4NP7xyegiu7/+5W2eJIeff1kdj15t/Tp8+NNJ8vn18+nwXdHNtx+8+fTDm6Onh09fXJ5kz5/tnnajeK27"
    "crH+27vRxun5cOPXi8mPv549+Pzx/Dx7n3z48MO7bQBx8qqb5+e/b2892BltfXryYeN8+/Nvzz59/un9+8nO06MnL9beDN4OL179"
    "fO/Fm1FnmBeP3n5M3r04j3df/ZG+G//w/v1g8GT04dejF3nRKe4nR92dQbT6R3d9NX892X2TXma/PzwZX4wPT9OLl+uPigcXnUH8"
    "W/7TYOXo6NHR6qB4+MPHPw7Xuw9/TMfj1fjZ7sYvP8Qr99c+n73+dLj+drsDw3obDQ6L9Hj10aPOID2eHD579/oyev/bs872z6+f"
    "Zw8f5pO1dO3Lr+Ps/HLnt8Ha22L088fT1x8vHk6zs0fPu89/2PqQb388/+H+w7M/Ll5Oj8/H6et7fwBqPrq3ffzozcVPP/5/bJ3H"
    "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"
    "hXvQMe+p6Z3dKXLBQyhPCidypC8HEE0ApjvgeHiZ/kZpsNhRpMEeJFy/lppwUkqXpEISxF/csQWniEspzytyyz4Cbj/QnYHlgow4"
    "YlqdwJEwLaa673+WLEl88pP+THEdPidEp8acCaaYda/w7B8yCvjH87MrjBGEXQFU/FRyDmclrbwLCkVz+q61/g380+IY9DJtDBPa"
    "41PgRe+1aYXtOal6OZkd2Kf3vV1IHTxXm+vcEXSXuquuWMeYBKGCkmDj95xrQzmwaJPxK+7ILf4/9t60S3EcWRj+Pr8iu07fvskL"
    "Cd6XrMmpYU1I1mSHOvU2BgwYjG1ss1blf3+02MaAWTKrevo+9zw9cyqRHAqFQhGhkBSSRjuW7axrHUEqa7PXZWMojwq1eZiLV0aj"
    "QWtF7fozLr6KSQlhk95mw3aqu5Hq81QmPnylZ1vxdTqm4nZCDDfK2e5gXW5z211Wjz+vh+EVudCTWk1QwVwzE9a6s9aClpnZaLfo"
    "vCy5cYltyVo4u0zmC1QlP53HK+VJsyW9jpLVMUdJuWy6q2ZHxjRGap2qvXiNracTjt/l9edwLq7YmwGr9Ber0iI9bpfrsRq9qxVH"
    "ubSp7mKdTbpbqHXlwqsZp+18NvGi1YmsMdR4tUlYWyozW8r0Ij5oDSeWQDWnaabTjdPPja447WbWLLuolYovMJ66nGDrsYnSMtb1"
    "TVoaTcRVvZ/ZbHhT7TPTptlZyfawkNoOuGG5MKSY2ktymih3q6nWjOfV13GjNYzX4pNOJ6YoYaMmjrfdHDmhrPF8qeXSXWDG9Xqr"
    "FU9xakdY6EXrRa7W1suqXRNX2myYS9rZLtPdUJN2lrDG2mIzNhcze0wZq+fXhDUVFl2j3k2HSZXTEua8Mo1PTW1VyewoYVNIstOm"
    "UC0Ric7LZDbPcmHgzy2YjbIRgFtSTZXBdLDO5JS01CI31Tmb7lB5upzW6LmqmdNpvGw3qitgMOONbE0Zbc3uy1KxtzRH5Nn1M/1M"
    "m5vlpJ9+SbP5UiyTmVU7Wn5VtpbJ7PPYKhlEnV4Rs3S1uCVmFlld1VbsOtd8YXa7WYywNdY2KHsOLDlTsczinN1s5mo6vcvx61gz"
    "3ikMm/E+udA2owndrtpGv56fVyRyukx2E8arVM5SsdWKnA2NRVtVbfI1t7IMTstNi0plm1W0AVNRTHIHbGaXWvA5amlVBpuyasg2"
    "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"
    "/XC+FusNQrl0JFQb9fu307EYud0FBjXp7hSfxJ9rndZz85h5ek4XKrlCRmjGQolduPpY3a3r9ez+efc8Sa3EVEsMtcZzn1Iure7m"
    "jVJqXCp0RvVyatTspnL92t1T+bUw0p/2jVQzMjumwu1TtJmb3smJ7ih9O+30e8VjINrfz0KFZbe4LtYzpWMpJ06eg8d8tVat5ffh"
    "WCAWvJM7+qS9Ew6btvC8FJa+eGNbWZZT+0qqXGtlUqfHupJWg6V84hAZTaTD+FnbH4XuU+Yxsp0EYvPRsZ15DdTKaLJq41k58pyQ"
    "0rFI7XURiOjtYKAZb9aeU9Jrc74qF9Pr2+b8sdWu3h5Wwlx4PJV3kXh/emhkU0qnlO6ni5V2UczmUqtU5bjfZrf11GS/3Qv1Rvf1"
    "+ZjvVZa3pcbytjeIrTqlSTOmt0fbUHn11JAV9bidlOfjXub2NbTs9qJoHySCuj6KDPZdeZPvVdOZQT/W7YuVcaIReZQDx/Em19y9"
    "7l/lZiVe7R7T/d4k1Fv1+vNcGnW0nqmDUngzLld808B4fRdbdqR9N75/DR0eI8fTuqkFVLR+ibrP50sEnlbr13lm+4h2W7X8nG2W"
    "tU7+KbA/KHf6XfBYy3R9r9PpITutFBKF6F27l5/f7k4ZMRQsVFuzeTYvRJvqYlCL+OZ3hWlgUIjF1NVxFxbWmZJUXRyzgUY+sKuU"
    "srNpdZYDB/z9aN+YTdNyenlKJ/Khu7g41ncjKaQHiuNcWjk+Rp9O+qiaTrWyx3zpNhp/GgjpV724OgQm6VtNzvtG4X39NRbdVov7"
    "ppJO5WP6Ro6E40K1OGsKqeaklevvTtterF7IPd1GSpMnKfXcyrcbT5Pj7WxcljuleaS0f0XsT3CbEHrTzmIXDfZKzafFepILnZS7"
    "dPxZEu9apcfirv401Se3k+J2oG8DwdH2uH0dHEbx2GRyDD1nMt3qLi37VoHsLr1KhUad1TEa9/WL/X1mUKoWl02lWc4dY5lNZtGK"
    "aq3KMiM9NtXyprruV5ZtvbGblfPSvKl2BXXcRDyRrjcLPUGZBEUxKB1vY00hvcs8ZxBGFaJ6apFaCcXNYVe6WwWzFUT0crNcdTYr"
    "tTM7dRqq74KRTE8pNxupfL1dyOWWz9FcO/bab6Vr2WKhPDjO0o+P5WU/M2vE8rVUqYv+3JaOyqi51iJdNf2aEWulJkKQp/m2cpfv"
    "546PHanba91GteghmBokZsVoOlUqlQvVhZqfTgL5aara0hOZQ+OYWs5X2WxGai9SgcHTLn0q5tLN3qo8PXTFbtOXbrXarWxu9SSp"
    "3ao+P/Zjz6+nbXiyEAtCLxZ6Cm/Xy+1+O5V8G3TgPI/1WGlVKycqYWmdqTUb63bukLjLZIJKNTuYP+02jadaa1+vaLH1U+gQfFpX"
    "VqHQYKzUIv3O5Fh9OhbjcV1T2sd8rdF6kqub7QBNWEaIHLWe9FhLNeep/iyXms2U52O91Vk2U4d9JtVudvWqLyuW0tlSKZOb6bFl"
    "+Uma6zNyJoqHdFaulAZHJX9stu5i5Vkmj/5Upe5rvrycHJpt3647zi/VdjZS3jR2T5v8tNSIa5klohu7aj9fmz+eToER62tSUBpy"
    "aoym9BFNqaSdIplWapqarVRpO8A9ItJyV6p2luFtp6zrg0R7XItIS62yFpbSfqXH93ogsSpspqv2XWmfLaWVaCM7WqUii0O0MVlU"
    "tlKhHLvL5A7hitatJDK1xmh019WjkU28EbqT4qF2Ky+Ha61RPi/Gl9PK/lBWpEW6Nk7E263GUcu1463onbaa9Q+BdnZ+l663G/F9"
    "P7yaRTrPzbhUkXvR3GPpVG4I8fBTrjWKLuVXTZn0Fqd5ZqI9Ledz4aDMar7YKvBYCccrgi8jS5XmQOzVnsqrfrxZiLUDr7FefTs7"
    "PS1j2fagohRi+dUukmnPt6dwTT1WpVx4OT9USu27ja84CSiJjPjc2w4mk9rx2fc83pcS6rIppvv5yVM6U1sffYFtuZy9U/J5TZxk"
    "ZoewFpyUdL1SupOnu8mgEgktBpl+b1nT13e3hZza6x12t9WWqEjHdWKXDQXUdL672QQH9UpGmWzv+vVWLBpX93pm5+s/dyNqpVNv"
    "H6qr3UbqCuVEdtWovGr6XXx2N7+tFKYlX7ycX65CvW0iEwgvdr5wJKb1hZM8V2tPi0OlkO4dw0ElnJ2o4efRKbJpNp7baymxFxKN"
    "UGGn1mKNZWCajvtawjEYzdYCzVMnHZ1rkcqxWGlGR5lCo7g5JkKLUXp0J8QqwYyiDDadu54SS/tyj63jIbO73VQGYiQYOk0r8dJ+"
    "+roONmKrrbp8ur3Nxm7VhV4XptnEbhdIpMr5U7Aemk1n1XZOCR06hUxupfbXr8eeMmsWm/N2t1LVG8+r/GAbOYV9gcZkVZlNFnfV"
    "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"
    "khWcSLZwU972OkhJRmuChNHbw6ZxNhdntMsea0V+NIDXtnI6cjzo/cHx0GCJXMESC1ZXPc9ktXZuALtASXINq3XCavT5LElnytoN"
    "i43VYD7tJSvYdDrOIk1LZ4onDjtvl4uh3tGGTOFc35REdcmY69xwle+fjVFOmLXO9VppKw4LVtsSjDN6VodDIssuFamAZNny0dKO"
    "xvCYmagG36REtNti1ElWmsmDxWheILcCYhVFBVdGkkmrtW19hI2Z0qk1tg6ZRkco4+i01zOs03yP1VaH5mg93BRP+y5Ndfs0Cczq"
    "pDRlq3Tp1GCOXO0w3prLRplQCEnoTvjTlO2S2ZrE9+l5ZTnqLWZiu5LsTJvLGrrnOi0UbVjLc7O3W5EdplpSm7WWPq4hp+K6UFmb"
    "O80qEAtjdOpt0JE1LCTX8z63G7fMc43I7gb9dZ8xenw9tzwu52e8SI6sXSHJ6oCnJFPciSWrpmdmrIXUrXKfYyqTOVarYao1kfBs"
    "bZeVt1hzhahloatnD5tJv8UXFsv2Pjk2stxwSc5LIput7/hGJk8fsdr6MKsuCQnbyNjJxGmiUZ3uFXRCDQ4CJ2/o3bnV2eML1tgs"
    "m1Osn8eRoiUouWXV7B3rJUUVkmJ3UJKRnrgrioeccsgLmUxmOKzlNo15tyUB27LLsGL51J/TtYVgaXrRPJNolkb3k+Xi2G2bU6G6"
    "zKzVwnayKR6XwOAtMfixXTuih1FBq5amudJxlOORRrWvHzaLddkoE9kqi5gr+Tyabfl9v9fBkWZF3ZOmjJlmJZtFFDS/nWyHaoUr"
    "n6ajKk8sRWMybomK0FfzuWa+sxUmJ7Wqs9Mx0MHqyK5LnPO1MbkoF+bWoGPRh3Z132RmSI5KbmuW3pamElvW8LG14QtCj89YSm6i"
    "rHNWp3HkVmcEb806U1ovTysd2tz22gSx6ktAoPWPjFxATYY50mp9liwv56ctg236e3Sl9lrtusUuCGnWbx5Rns63lvO1NR9jdG4/"
    "VbgsUZw2zs1uDwPGLjatna1VkkG3i0ahXFviydM6py9LLQTsjyOhTfSzowK6LGWIJi82TXyZZKvzFb0psHgn268u4Ro0CSY7nU/4"
    "DN4dHw5A7aca2fwpyfarxLCCFktnfcWxg1PSGM5bmDUbnWDesuMB3e/6fJ9fny1xMdHrM91sF/M5E+nQJ7QrFvnD2NoX6xpV21Rm"
    "ydV8I9cWZg1XcYyoCwre0uaqXJ6skPVBmuaKYFcrj1F9VyQOx3J9LCDUXNxsslWRtZjsfn0+q331tG0bS43VCpQiFVfLCrKstmcm"
    "op/ZyWhCVzPDWZnhmzp1QEYzA1gMVuZ4GsntFqcCoxZdoEshX8rjo+OkwBgttVZcdTA8c9atRRbVlV5TVOdipmfmq7V6o1MeF2Yn"
    "87Ax5jW1eOittD1WPI3nulLfZfqNhtyc9Eir0O0fBuU+QY3oznBWqJ7bi2EDk6anjSUQZOGk5k4aMe0aFkHvhuttAUzPns9p6xPN"
    "Y9Qgj02qu30vlx2LzWSuUmOSWq13GFeIIaFMRkSpQWT7RJOocc3pxOQkrpaVtr1J7kTQuYw1UIoq1xd5K7np5oryFBv2sY6JcXN8"
    "Xs+u62Mlz/X1/EFnqPpW0HraFChDpaqGjUzaGtaADEuWtWEJqyzzhcy8jvWa3BjpGmrN3FDJmsWXUTbZgymv5EGxQmzAXtCprSdG"
    "VVfWO7ZUx05iSTYyha5RoQ98cmeYjVyfUS2C7WJ6b41swO6lzienJZVTRIlkh8SuXsKTM1o9JS2lW62Lkmz1F+tZ3uriq3PTEI7o"
    "2Mxs8QI8A2fPh964KIkbfd7FZ/NDm+yytRmbYbFlAymojaPWynHGgauMR/0SpRP8HusemsMzw26EI1LdHPPWYl/ajxXzaDSqnVFx"
    "XMZng8UEpk/MEkSu2J6ze4k6cMa6OZmhfK+wOw8FsAKGpS6DU8K6UKo096dsn8rNj+vz1Dose71cfzLLkfpgmMkQ0qC0Ig0CZyV2"
    "1jr0werWuo0tlW9MhyOuRhOUPJV0dlCXVL0yYven8bmptkri9gSM5eKycMB6pSXLrjYysjJ6BVrhM4PSJmPJGUqpU2d0MyV6gqKI"
    "qlAY8C2+Z7QM8qCjA8NK7oBdWzIK+S6RWeqNblPr0y1tuhUq/HKjrjhd6BnVHHmklEO2d5KJVWurnMZcuX8cSlSDPx8atQPahX6U"
    "EVnPLjfUZlCr5bgFMeD5cqN8GtBEC/R5eED4g7U9l+sCwpxn+lmr8b3kZFTJrbiigRynct0q1g/nqtDZl0uVHVhkjdGiV6K6uIFN"
    "2/3atLNlSJPaKb26PFp3tmT72OlWcsPkcUtb0sHIjBZJnqwecblKyCgq6OhU2ZwNvTMWmBy2a82w/HrW0Ixqx6yBLavUEefsnOlP"
    "53gOm6yZHtGdbnBkJ403J6LHZpeZo0awBr6ZKI0Wkdc7lVXe2K2ro8lknawwlfKCHxpDXZgX5uMuizatFjvYzi1FV2uF3Gg1n+Zy"
    "dJayDEY8rgWzt9QrGI0Osy1x2hgcpVMSG7YxadZr8dp0QXZ7CD+aHbqjamF8kAp7qbg95BtmIcsW+9XzVpvhdaFVrOfK1Ojc1SuL"
    "LFUbUVsspy7LQBAX82V0yzV75U5LQo/T9XZojCw5eTJ6bItdL1bH+XHSH7NCpmxxnKHSXWVYP6lInZeJlqHkEPJ4kvRRYTwfknKD"
    "FdiZwdcaHWJTAWrsiaoMd6t5YUWtZ+cCWTEWZw455GrjJk6Z0yMKBqW+H4vHRUk6UVR3IW6z+tlEMGK0XHLwTLtc64yrQ2FRy9M5"
    "bL3pVaZSk96KCFABxVZ51elJ7WmOmbROfYM21hJRWYjr3PqQbODMal47NsgFOpuUinQFZ8olEsXGY/E0qA7nB2LYJKzutncU2G3X"
    "REwMp1r9dkXMywdJkhV8ZGmVVkuQGsMu15b40rjSzTKTjsbVSFZhcuKAt7JiTamx00Vnmp0ApbXRMOgZ6AVVW801gx+fSGK6XU31"
    "I9JdtepkZ1Iej2sywDEQxsRcHIwq1rhYQnSCPbebps6t+9RhlEFLSXQ15w+i0Kx1hPxpcT6aCpUlS+f9cL3pUIIpNOb74k6trwZ0"
    "VxYRup3s7s7AvmVFutTYcWh+xNb4rYkUirOiLgC1ma7ilcGcz+cl/tAV970KIw5nPXN6Qo9sh8lJ88KW63Q6xQ3O7tT5sZrv6t3V"
    "eNjEe8JiOWrVuPNuR9Ra5aMhS23L1DNsh1SSONIqEzO0s55iRwblVGxUq4ujDnUsVwa11obAMs0c1qfZvElsxiOjIvV29Km+1SY4"
    "v9p1D9vSqF3aN3u6kd+cj6Vz9dAtqkpX7ZbKRDLJFDal4ba4bi37UlE3DuMsRRwPpRq3KpVaTRbt4N384cxxYqNWZ/FppYFVdjmw"
    "exVbR6OrmHonqcv0HmhC5Qy1RA77OdcvWcMM1jn11PU5WR2URstKH1n02ud8aVnjwQJcF8/W4jwf77uTKlEpa9KgeB5bBUvvz5pM"
    "KZMZm/gUXVkri1R32cU4W5PzU6w5YzV9WCYWS7SFLpSZscIaRmtqKhOy1OZquflQ61sGyazPilrIr3piJrNtVSRmsEGNvdxTkzkE"
    "O+4bUp5czrRF7jjclMtCXVBnS3pO9xfNgjlf4Cta4031UJYy4gxPortua6kNV6O1WDjpu/HmILZojs6dNS7b6y5mhk62umVmXc3X"
    "afSsmbmVueN5Qh2r2G6qblGqg7WmQ3khLYu503hFKmh2U02eZqNqp8Kq0z0O/tfQRwdV6eBNdN7uFU4az61U/kjPpf16Nx0t+33u"
    "rA8bs+RgPpFPHWO2zamzQVI6AgXotFekzayriA0DQaZGfyRiRWZSOs5rZYWfaTgh7lr7Zl3ctrl1oTrJN89jbDkxltNZp1osba2q"
    "iBzytd5+VjzzhgQGZrPYk6UCOynu0FlVGJDd8qBfO0qKdaSxXm6SWZ1zWwptt1GpQe9G21NWmO9Ic67uNqUFVsy3pbGQ7Ux7bGOc"
    "bA/V4qC/WyFbuj9Q1JEmteoSLp9yal8ctjPNcV0DNuu2PRkccwoPFlY+Y2GingSmWuHYJwedXkZWtyNhqLW2td4W3zQPw3bNauZR"
    "YjA8StX9DltLbLs4HJQErjqfIsSkxC+NwbintImabNGGUtuStRXVr6631fpxf+Rm6+ZMOcjcwljprepp0rCmeKlU7LRrk35nUpuu"
    "Fu1RUuV5MObwtDTfGzQac9Y4VmvkQlmUp3qRyyxK5xEQ0MdZudstFklrLi/Ec08+UXuOmk4stLKYoGujCfZLYaF0OtR5MhEXRKVm"
    "GJJ5LFROyGRK7hoC2h1PRpvjoj+U0MqBOq/nhzm6Q6yRRHUyg2W2fJTW+mnOABu7a7X5jZEfK5ODuMIErls+Ip3dQd9RgwWxJldq"
    "htdPBJUfEnlgARjTLipXgGoLNEByva6QJGa2WsZaO5cpQdhVSG0ttdt5YTxHG8uZxZw7Zrsrr0h8kpzmG8AUL+wUipxb8w7aUjLS"
    "rD1Ex8Zfb6yqy6T5/Zv94t+3tw/7fcADI3C8+Y4jSCKPIM43+8nNdwVWl5wvtGBo8M1B40Bqv3hTlgKPC+5J/fvtIU4XsPNcblY7"
    "/rKfOnXfNr1QKtCofC3s18A/4CO8nA5f+fIV3T6+fcikzgnKO/LrCshPgKDw8ClhH+IggrQMQJAUxYDiMAHwSVRSP719UKTO3Bc7"
    "9NlAACGMLgkKkwYDaDDm+w+MkT/ACG5EwUw7uGVVNXn4SjipmAIpCaTB0E5rnYHNYZGqmYIMiJQYTtgIkmCePmyovDMV6A/82svE"
    "n6nrn+8bBswg4/tAsiajXzbqEfYZQt6oOsCRBl9uEP7DCzTNKD8v3hwqqsL8P0HWVN0ERN4qvh/AIDLfN5ZpqkpKUDTLTBmASMq0"
    "X2UGo0O+2aPuDfddUx5N8ViKz6Z4PKWlaClF0ylLSqlSihU4S2feLnfTeGvqwI6cPYl7+5AYE3Q2DZ9ShT1N/0AQAoy+n4dzBBIa"
    "yOw9HkjfA1SQUR7D9E0OeYljJh/ed2cMBVW5q60qN+6LXAER4JxumPBd8pRqmXCSfsCqiiVf/9gweuqHlran0Pnp/O32ew+fOwb/"
    "BkVgGql3AMySSB3+NuLYgYxmiJRhyZDC1H8AEAEw+PHn2zurAj08vRcMARB5AUTCAXyHz5QaqiTQiYi151byFhaoe0dIDEMalK5K"
    "UtphrPRGUinxvYDY7QEC+03n+Nk+GneM9cNmK7vUfoEVCs13S9MYQI3BfISnULZMJswySBQbwrqMScbTYshvcdDvGdAru0S3cGoY"
    "pq4q3CVEm9taVdQYGQ6L/DL8RxFnZKeVqVtgYzGZi00xfIiWldTDOyNJgmYIxseBF0zGHkq4fRx0UvuQwawcBNrk35GPawNHJDkw"
    "GV1X9TQNxkaQLn4Ams6kbRBeM/sXEKwnmyE+XqP+fpTdwdEvFKA6rZGANEEBXPedQP54i+qCQz58r9mbA/CnphoCXNTv5AZwNRj1"
    "6N5pJMdcOED2jQ4j+/ahkTQNuS3w1bcwDDzwKwd2L0ngFPvVY7CJvRuA+80PT6JzukB/wCISMIr+7uHNCIrNOXAcPI4AUiaCnCjg"
    "/onzI3Ig6erh4rQCwyUb73BrZfSPEGgMzITEHJ2Ju2MHDyqs4tIHh12/wA/vaAJNuMxKC3uBhjtdpJZg73lAgNr/BmB9k+TbbkDN"
    "A+DTaBj2/HsgvHeqb8XOB5dxgJpAG+6zzfbf6ftOB79ca4ECMICAEWXQb8BlYPFasmK864zGAMWMtEw1zQpmKgFGSSaP3ymJlLXv"
    "GPFHIp2IApdKfA9/xlNFBEi/N9ACRQA/J/5MFIvFVMIBBTj8dVBYCsejQNk/QAOU1d/eIliDFRiJDjMZ+vaEoexWn0/k9QMZGSnl"
    "7G3S5j6geRxd7JD+22KFg/7L3WL+A1/FToPtjvn55s4w/HGP7FaWNlTWDLCKYIRqABnhGwhLh29zv/264frLUUx/RmO8bpHxON0q"
    "9ud4zD5lw4/cZEgpBjUseoQXlj9HakPxYzTEUwxCUPIIHyh+jg7C8GOj1A0pxQ2uU/gIp1PjOVoXkh/zXlCBbhGD2Sl8hNmp8Ryz"
    "C8mPWQbCH2wGMajd0ke43SrPkXuw/NglQWZiUMOiR3hh+XOkNhQ/RhUoalwcTqfwEVanxnO8LqQAL1tg7RpGHD87pQ952qmS3nCP"
    "udoE+0UA84HUlRi0sAgoF4/QulW+jpaGQ6DHIHYKH+F1anwdraCwagxSWPQIJSx/EeEP9+eGVOjLbdsJ1oWFHjB7O4gvduVtfIWb"
    "TA64Pe4gOH36H9b+D8Z8+DUf7zOOffi3oGvt4odPx3n/HwRBsh+ebFOAhSCF4GyyHxF2qkNUjJtGoYNjl/BtpKlAgbMrC8AsjF6r"
    "weG5TWe46/ezGEHFDdkrHbqiuFmeAWjR9vBTuzcdhzsGDbDbHRRpgwETRIPZ/xL5RU+LdRq5n4n86+iA2WN+fwcaGlSe6Ld3HupK"
    "D2jwo3uJRhx7nZjbJ7gS/do7kkBCXQWsjTyF7Eggx2nGkzTQAAEg8F/onoicJPALTLwaYTX5FdoIgw5/ZlDYfq17TRhi8y2gaIvl"
    "ujQgkmtX7DWecDoE7J+EPTBpWTh+F5SEoXObVCII4i2BI3+kEranQyN1sJd7Vg4vaC8YeOjTPkKV3bXIMGBNfHzNFwMdrBEWeYwN"
    "EDlSnkb+YJjujUlvOpFEzqPZ593x5sy1r2/2Kxw1/9TdOZPhkH/8dyc0Gz+hDmm2Ey6aNsD3D8gLUAa9yL7F5q2vS8Rshc4Zgu6s"
    "gt/Vd1umPkPQbenQEqyQ9lVIgZl5iwB1lWQpf5n38UJZugHGAci8NCkBg5Ch7zyPnisVsin0qzo+SIeCt8vD3sABd4xQx9YH25EJ"
    "9oYv+RxjAJo8Q9Kfpv5p8pdz2t6D3tGoxXL1VBmmQImnD1PV/A54AFTTVU4HWuiG1NN7UrKYS3BR46FemSrHSYwzvKGfgM8YSgTq"
    "h2B89438bcDfHnnB47oKT5BAV98l0jAhJ0ug4/TletoBEMueJH4CArYD2xkYCWC72vLtXRZoWmLuXex8yqTffL712GIGaIv25Dnw"
    "wM8bMJP3IESyA5xDewOzPW+pcDPG2bqeNLtsLTC17OnqwLN9bgEy7AkgJZVzBw16x+688a7wC041QCuAQQf/TsM/Lh6nI8gf4YpR"
    "az9iC4mSnv8nM4C+xHdNZ1hGN9I6Q1sUQ6dl1eZc5+fb5SvHYu7BwIbhSWAi67aj53bs9WEvNGddBA/EPkgFMCMsSNOWbv8BFigq"
    "G5FVQM+cOmDwLTD0qO9k7dorQB/sjM34xjtJmcLe35n/3kkLD+ZKgvP1y9kEBMAhjncV9vk6E/apya3G0x3s102zfuIy/fidXeZG"
    "IKCOYh5yz01tguR4Gxxr/ube64AiNQ2IwptURaJl6EdAiYQrylZBEaC1pJAEEJoJFPd9xEMuegfLvZPe+f7Iw44ETwpsRdRdlwQG"
    "zyau2kuw3r3D3cUl0HGoUKizheHHwgEMKl5eUHodWZ1Fbkcq9t/hKXtgdF7NiwcscuMNH3kJuDMZey4lyNzbxSEE8xFi/x2xMFwQ"
    "Cinfbd9pIB6i9VRfIERYj8x7PmoXMHRBWMZrZyp+w+Ohr9xeSUgCir4AcgIJnr5En10FKPv0DpDA36kg7wR+kvZRt3GTMgFYQHYZ"
    "rmSGP51O2Ev9tuhjhgC7nuekvSUDz6lCQxPZq/TRcfOHKPF0P00VbCweK2IRrHjlt4hZ9m0lN171LT0WaC1vKUd3D3/+iLRo35GQ"
    "WWWzT8zA5AIrHsXCBgvxwGC5DYZr5kd5FMJV/wPjB1wtmKH/MnUrYqN4Ye0G4Nrb5+XG2VCVfmws+lQudzTuic8WQgNZDAwWAX5F"
    "6O8+bjahQgVjNxyqCjdBAf+88yJko200wGjQFKvYHHBnoPnp9tcMkU4gf3zErqqoOUncj+9ve/ZCq/tlMeXfNqJWry2aAvvJ/113"
    "ycQNceK7Pf7//iufg0eSl/BGGTxljhKs4TNlv0ByGcK1JCIOsEFDJOGcG9rLk4jsSzp310mghNuff70gMX3DhcMmThswB4rtr3q6"
    "qT5zK/jh40Hm/Sf8RuGT/nhplbCVCm8Vwg+FSKXC6brj+HNmgfC0kZDbzYn7cachewPufoezkNXuoX66ETL3c4bH7dZua/8u5+uz"
    "J45f4/QfrhOeFXQ5De3Ty/0aig5HvNdwGFkzT5dgHIc76p51+Gi1Roek5EIhKREi18dU9vqIocyZxNs27p3F4zjFx7Z5QZu8qpK4"
    "T5XEI/bvVzyEL6mSNmmfrxpAcGH6uyTAA9OLutlCBxIrgDlyhJ0XY4T7+uH8iFBFbVCOqUOpMtBETFfU+3E4AIncDR5xlUN2vURc"
    "jNiV1x1whiYontfgalletybYwu9/j9iz3K75KHG0Gc+Gfv9RNBJwoQAxL4DFoIAZsEW/aelKbI/9HhcnYOmFmKrQWnDa3S+F6Cgd"
    "uIC9yBwkBaNfEjet8smc2KwcbfW44S+qLr8WU4W+xVt/eMEnWAOCJNQmuodu51AY9pPCYAev3c2CX1FROw7ZrrvWNhhDEvpJm893"
    "IP08p150qKJX3z2ujPV2ffzz8Wgh1J8PHcKhkFv4UyMN4wAWxJu7f+XC+1cwKimI1A6M/FoslHcAH/RGBlWYABLXYQLDAhn65+Uh"
    "Wzg8/6B54vXpsldeWNWDLa+KHo7dFD1vcXyVvFdoiBjysGT55YVyKkxM/KAX1fXKgZ9/+r9yJuVXwZw2DkUuS9OC7kSZvzvjEsHN"
    "dnVnylhBkn76fbl+KYL4qtuu5i+r+/bO5ckhPNAbKItCX7KvjFsi8qNtMv9Xj9OwXFjPjRlY92jn5scIRRxGbrFOSzsw/PWQ6psp"
    "8zy62kHwutmGvn1Feb2xyKfvbMYOILjH/hahZwf4wg/TVoefH7DbQ3Hbhf0cLlkG//MzDPJq+0cvic8oErxlEQoa9VVlVdV8bZG8"
    "sjm7iwH6mB8c04R3sujdy7hePfG7nmFJyPHsj5rwNXSOGK5HCzfXg69OmmYM6vJKSLt/w8tjFH8PCkhh4/PP5J+X1wbBAbBVNynv"
    "D8fkexKtca+UwJZ3ou6qWbwG7TbyEJrJAzXgEnZrAlWBdbnjVlWgfe6Jm7PzKcGua8O7++J4L3DNR4Ttrn54r+oLYicowMJ3XKLl"
    "DyTCvdvxG1HdNxjOBbJ4GNmjFHVHDMaP3KbgUQ9+FIkwtk8ASAk7+5FI+fgDKXiX0Zw7M3d30zyJb7Mo+dJdBt/xu9/pGDvOAKxD"
    "crC5dzny4Q2zD78u4HNo2wyY+IF7FlqUPeridsQoPDID4wWYF+hoPx16XMMH+8Nn9NkLCaxpJoFC6DeKGNIA265nCAaZ3bhf16Fr"
    "Mk+FIgTlbYdPrYPI5lFWXqzgwd6etnu8RmX6OYRni8NeG4HVioZgwpiznzbtSFTJZ6iTvxvtFqvERSG11Yhgl98e9Pnm3vgKGHvw"
    "g8LOvvUcc+fMu+zrRHbCOzXv2Efgh1cDap2qLkBrw4s3ubKTr04UxYmgoAiMqt+LgkV3OJY/AbDrKo9u+nm3RF7Y1UOAwDqVmDuO"
    "eeR4iwSQiBBrUTCCQczPYLlcE7Pb/J/InFgdcISRuIqnC/LH5RaUZf8Frc/vafsa1C9TjSzNYrDQIUbcXzzH90tOGKAhuXZq0NsU"
    "oQSIe/v0wytwmxleYYI2H14QhTXoSwyr+9QPr7Yn4SHD//z7ojgEMOHvkqcERfU52Ar08R+83xu5Z9+hjPFUScw+zkMQvbNnA2qe"
    "ffDsrtBc2PUbve3bGB+sjusNlId4fTLF78P3bfE2Hv8dH/Xw8wFa7wZKdGMKaCNQHj6C4Hqy7gBYigjUUSUQFe1cn4THPY6OkuZg"
    "N8FC+I5mCZrhUvd2g3NUGzDs7bNbMOzxOB1y/WkUIu4bPJuR4OG3DkwOYFtdoi7gvmYHuBBcBgUQ7KN4GCQYcS31Rb92ALITNGY3"
    "BQvzHc3AviWwOHvmnp7PADTD2jjAHPTvWBCZHX76YgBaoM0T7ScyYufRxfJYQwclIjoK8f5lyK4Me5GwiLQWMZkD7nFJ3NdwYTGj"
    "QHhX++9R3HTCq2YVU+lLlDyw1IJ9R4IDDZahYN5bYzEHfZFGGhoy0nJxRlocNybuCXLw3zKi/MYohZ2CL3CWjdrXk0LkNAoK1ALB"
    "kDGRyGOGLibXDQpHKxQp8QP1Z8CxG9IMpbpRs1cYCZo0eC8PzhcqpE1eoEQFbGDQBxQ1OD717pW+XbMM6GJcGOxtn3XDan1t7P3l"
    "Ah2FTkN4eCoydzGmzmdXZkMJ7n6ArSmwnOwtwf9xqwqK89WPDEb9OsheufWBh93ULnG3bcqBClYCx5hf7AR66wScKVLXwXBhiawf"
    "MK26UKMhRZ2WBHH8ILSjD2ACnme83H+C+CP80XH/v4VB+qeTNKJp9vcLDtLlrg8hsyOiK/cDlk3gH9dxd1Ewph19GPLPep8jMni4"
    "JS8n4Ei8crTt7v4FHOhEqO/ctwgkfwrqB28RB993Bz73ysmVWud8+MvBrY+jX3x5Qzw8ztL2jvts5cR3zHetpvFA14+JEI/cEG7D"
    "Dn3EDzoKFMVHcL+mn7ymiFxx25tC5MaHvbjvXUF5B6cvHRj51bk0lkmjDwP6PBzXk17Cd9Ibmsh7XTvA/7/BzLewjad04UgEXS8e"
    "Q/siQ+7G1D9cKByt2Os7VwDQuDHuZYT9OVJG2CX25YhL1IWB185qovuJIQVgKAU9E8GacOMy3r8p5D4Bz9C+fYPHYwn4f98CMRr3"
    "SYxC9AMIzmhBiO/g14cXYRLIfBR1OSN39XBdoYFREl8TQc9iznyCzw42+1sB4L7QbSTirmlYZwpoLK4E9J/dBbsbqwbFNom57v0g"
    "TePNixcL1IlOdmObf/6tPHiPQYdwsxLJRWnoURUi8mfEnYRHkeHpoybzlx1F8oCUGC/HtWpUKCg8crzFE+AFxB/kehe27DkX7XUD"
    "wb2YeMpd1eBf36EnyE0AlXIyPX1p6UKk3sU292w3nKsvZpnaZ+ne1Svi4zd0nMC0vVOkRH1Po4k/g/LtxaP4V6J9vnhQf5sZ2NXg"
    "jZWwKHOnNnTVLG0HUedud8tQNmI3s4fzupsVgrusf4N4vp3FCvhv324S/luU9L5TFh7G2kfeDIobICAPqegrPkEZeLsz4an1KtiF"
    "49KIPbocabeEKxms2hcsk5CNkMCwgI3isdHVQvoSsDwSbfDdLDYfzUE/ZuK+MxG2StbfZzASgnJRoXpqnt5/EP4yhuYijOLHNhvc"
    "TRLEV7qQ5q1N2FYLGZL/PE4w2EwYaeSBU8AF7B/ZVFxxRHeul3Hc7riLG0dicdzoc+vmvVmTVPPy2Lby37/IhUP0Pn73vslvZdt4"
    "NYAR9sphZecO9c9LDJpgMpeQ9nAFYodmB2DYDOzFOtlWvOuZil+I4dS1acf4D17ru2H+vAXHwZ9pg4QOurfrFaSAruG72ecPmru6"
    "Y30Q7kJc7dPs9IYxDwyjfPzTai/UC34/sNJeiffX4G6acPR9IF93/85hkP/Mx87vkkp8SfLiRIhwe/nkrydHNpkbEkrFV0bUdRP6"
    "bhZi+KOrjzBD9Re0c5+yErqr+PvzdH9P5jZ1+fubU/F39m9D5TnZVSnSPIAFb/Ft/vqGfotNlKRK6MOm2KOm2MOm2UdNsw+b4o+a"
    "4v6mtlHhv359+cem0odFhhv8czHxNPTRBua6HZ7fBbFr2zE4zyNrnoTkRAXcxDGir030uXp4k0iEqH0hCS2B+MR+mpTt+7dwVMKX"
    "jgMZB0JD4zRL+G9pxZ0kRh4l2UBADZ2M0AbicEZHx/l0d2jwBEvCt2puFl5M5LjLyS4E+0dcml2nNDqNrnu5DNiu3sb34HrNVb5i"
    "j+QrjEZ9IeXYlao4uWuXhzdVFI2/x08ErqYXwZK+l6Z3zxHEX+13CHCY2M34/5etxl/vfdhTE92vmLwEXjdu2mPMgbUfueMUUcWf"
    "cbMdSpMaNd/XHJ3BOlAfDt1Xv0LzEwJzfviJ2VjG6WfK/0UDihXozzXv8x2R/jSjf5NCG9Qj8uzcrgHynIPOWOJCGV//Jn3B6J37"
    "qXT8W3G0BJPA/k1SAg6yoAHkCBD/ko5ZorBNKgTXETDPcstErN2oBRpYAf5Bc4+9YkLsozcepyE8TP2NrBAfUVkq4qZRoK9n59FY"
    "nXUfreP7DmvvAANJrEBTTuFeAO9kI7NNrSc3iz1B7o9W++I94ntabUlwR2UwTJ0nJTWBPYhRD8WNQnyXQGCorkJk31FY8vYrXB/C"
    "h2Gmd2od8jSXyJ074xf0CwHcd7AIz1voecEOpEnxMVGDdtnb3zXwCnd5Th5wbmgf83vdbGr+OYsPe2rxOdIhkQsPru1XyF4NPeeG"
    "zwv5T7+SjOD6FMUX/CeRCQ19Yxv2DbhKx2u5+aLllN33T0HmopIZPHSiQvsGhqJ/ORjgqb8++0LMsYs97ia3YKfjYKTrje1C/I3t"
    "LHY9vHChpt0cfVGJEJ+krvJMVA8SzCn5W/fZX7u8aZAp8E/0ezB3loFBOimhedL47kuC8vYWOp/3AL47yUhChZqdgvbFO6gv39L3"
    "wD7E+XlLaRy+cA+rgDHy5a913DG+UGwskFLPbmIn40zY/39xEnMCpKplAkPkyNAfYQTukYPLNjnvK9hivLRS9qU9+yNYKO5HFM3d"
    "vjKsVxfFC+5nlf1vP2HkO1SCZKiSe5z0+VfRDY4IU4chSBR1PuXE5ka/BRI60vnlH2E3a2soU5vvqPlWVYd/O3Tfs4EzAX/TveGw"
    "k0QnbhAj3bY+eMSb3YzUQcM94295PUvJYzcKX3OcgNq2E+LLEjQmbMAwnauvoXR4/qf+Hmdiuyati75qaYcXAaJtNoEU3geLwVLA"
    "+A8s44fTAtp+3hKcxgU92OOme7dLXnVg+G+hhJJeG/s093p+BJ8jItp/Gxjwu/Q2odmJyxvoCSqoqtyNFKDX5py4wHd7ywve/IFt"
    "4HYdlfcwmGXEm9lb8+KdZytOoPgSu/lW9sF+9Ssw+A8gEEg0hHtp4HLB/eoOCGonSuyHQTv5/5/PcfDNNuKJNgLgCnQMJ75jOPJY"
    "BNBPro3CoMLfut6QtYHDWxoP0k3e9cTn3oyNKStcIzOcVxpj9Tj0+ciR1DXSMeSMhK5zp8LvXPEFLaHB9lIWACwmju4lDJ++p9Kc"
    "GXc3TshtknYJpexxP0drOTQ8XYiPLQLlugUUlbjBd0cMqHhMzJhmY3kp+poegGYZMAnZ64eSj1ItRNJEvBTF+PRM81G4mZs/5tl0"
    "2l196qKHC/J+UwTTGjsvRGhRwOrPdXUAUTBMFRghL4RBZd/e/E1e1GhpOEBgtYeMO02ys3c8eO0Syhrj9ry0zz50iHcgXF5NyGZn"
    "177FKf3AfcG+uXD0r1fhkdV7peLAqymbGsa4POD8x2qa0z5wcHd/0dyu9vfyQVz1Z50BwwPUzHuL3cGREC73Kr+XydyJM7tVdUw+"
    "GMPynWRSpA7+R6U2FPhnJ6QocZOi9ymWTHGSmOKZlGil5LOSUnZqSlM2Kc1IGXTK4lKWnjoJwFCEql8A+j8D+KJ7CatcwD94cs88"
    "vgrrsVnQ6W4Zf4H2jBQ4FgAfZcj+MGFAPOCbu9wBHGhv8KoOw1Ljm1/ltNcFhWHo1/xbePh2q+N4c11cfq8X5t5t/biaHblwxCB8"
    "MfaqS+XcaEFvRb6y/thbJ66LJ3jTExTfbDNHLsFPCc9tElJxY19qf/weDwT5H1WDT55Hbx3oW9gvBXS/a6z8F+7LuMGRzwJjoXVn"
    "Bza+mNTIH2hjqwW208n9YMtxIIj3PHyXNetMqj8vle+VAWgZAYEbvCFga8Um72blSfio82HJ2k9ox3PI518omrt6AHzwnkWT5n0i"
    "2Y4uThE237xEVUTf7ZYu6sh7ALidSdkxFS7Bu0W+YQKFgVEKWhlwEG8dR/Brx82D+unCNi4PQ6yxVIBnXmIaACLpUe5yTsDP8Cgv"
    "VnwP/g16kC3+KN7ZSj50CftxoQhv2j1FzxJ02RakmzrxxZReoAGlauaXrerIo3AATLnEekWf+W+yDjmP9es99ORR/NW/d9ue74PI"
    "4HHAgyd4wsGFX1BfoRfA56XUuLQMo0O/oCQ/nRgAEx4aXv65JHYQZjjnXiAlrBMuCRBv1c2bn4PsLl7uNB2TsndJ4xKX6fdxRgUt"
    "yhse2d3XTmiuW9YjlOndxa9fa6Lz0pJP8DnugMClp3AuwutLTKLd5a9lI/xy/G/UqdY/6MSKdfZBpe2ur86VpdT998DzSG9PchCB"
    "Rl6a+cezZV8IjuQJUOy6ZqONBrvcvpPwUvr17NvXru3YukIq6ll2iJbc/DPvqgNYrCXdX2N0Ou84EbwzlmIO5ngEcyCrNLAoI5yI"
    "dino+4uJprwZBo2cV+e+vEm8Ig//i5z90JkAI0bgyg9OHvhKkTp9edH99HvJROM53kX/A3QFML499I9CIMP3Fe191eTBUHAOK7zu"
    "MH82Vte0mfYh7XOD3KM8bnGC8gj3A/aK+6FQeHRR/qnLAWCOWVOghDTEgIsQil/nCCnei//SOxwPzlQgDvj+5rMzcGfHArW5hH2O"
    "fvHWvUvogT/FXq+0K0CuepWzn3iPXGgJSfitKfzKhD0ynQnXLvK46WXT2ZvXlD2e4SRJNyEaPA/5oe3/i7brSxYgoMCA5yxfMf2w"
    "q+kHFGhzb7+lYbzch+AGKEneDogW43ZAiONLw/Tsamz2K1djIfbDdYgCC9wuYhgx6qji+lxG4famTOS9yYddKIRNzwjaAAGX+8dd"
    "gmChczfuEYz4R2ayj8+xIPJ9yvm3dHn4hN79wbPTPtZ76t1F8/JN/xF4eObxBaYXfLB2Gnu4uUdeX0vrDBDPRiDvs3e+4Q8kDb+n"
    "eO+8dfv4KfiTkWN/+/6VfRv1QXienV3Uxf0DpjX54l072NRgOH/K0XgehsswdJTkmu8OlIRwefgsdYjwYHJDB4oEaLl7Lu/JluK2"
    "i95SHmwSN9qd1gnvEeBXI8Mcow4CEL/W8XAocDhc1gH6JTUHiz9lgaFIj7dN/yMQUYtfitXG7F3hq8k0fdkzI9eR+RVG+lKWTEfE"
    "Xx6GBOR+d7PBCr7N5n4Q+cuDzSEQ6APq8q8p34GsGUHb54uRKDHPT0JiXjb87LnzBd3dpiWHXbmagg9ley9foVns9t1eef5IO4jb"
    "PsP8+4YIhCV/aeeC1nYMXjzyBcHoA9/AaNIS57yx5idE0538coBINx/yPk0XigUcZYo/nx8lb9KGTj1tZ0/PJq1qZnRVJ4hxk7Z0"
    "6b6CY9eEn0Wy60sqGIVXqP7SkrKNmQitDW7Nd92HNlkEBeH8Tc6EQbIPZ686SjAojmDZ58N8OCe0+1Z+mPBKgnFfJSaqO/QGoW34"
    "3++rLtSEcA/3CyL39rxb+MrJFf4PVXkRhU91YMwviAansv1oSPR5H+bVepCPJKSMhFiBMR3HTPAd4tA1uIeKhAsBahKPg2Li2cUV"
    "NwASPBy5LS3mmgPgJWEWLYwZ0z3EcoWQM6twA8JsU83Odh7RKdjoh3lQ4+xcVk+Af251ExEPVER6l5+96nR9JDFKEXY188RdWkeb"
    "DJ6hXHPr1ZzscfZmvMf1hujzOmW3bcTdIe4CoNxchbfGCecGWdSTp65Hz6nNeY/g3r8x51SA9wmC8ZouU6pcnAbGm7KUggcyqf8h"
    "Ne0SeunTOdbmGUkKlex572Ukjvn8j65KzF9gz7aPd376O/LkoV8vKyDEclKoxDVC37lUl7IL4K2qiCSBt7d97UTczgsQlEQaxs+3"
    "/3bIvEdw+EZB9FFg5PkjEpX0A/n161+ZP/93D+j833f0z8y/M7aw+fzXvzP2+1v/+redcsvu5V/fXJXvG/hMC/uEQP/1DQzKt89/"
    "Z8BP2MY+aINtwSR//uv/A/QWTJI="
)
# Third-party licences of the embedded page (Vue, PrimeVue, PrimeUIX, Lucide icons, Manrope font).
UI_LICENSES = (
    '===== Lucide.txt =====\n'
    'ISC License\n'
    '\n'
    'Copyright (c) 2026 Lucide Icons and Contributors\n'
    '\n'
    'Permission to use, copy, modify, and/or distribute this software for any\n'
    'purpose with or without fee is hereby granted, provided that the above\n'
    'copyright notice and this permission notice appear in all copies.\n'
    '\n'
    'THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES\n'
    'WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF\n'
    'MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR\n'
    'ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES\n'
    'WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN\n'
    'ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF\n'
    'OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.\n'
    '\n'
    '---\n'
    '\n'
    'The following Lucide icons are derived from the Feather project:\n'
    '\n'
    'airplay, alert-circle, alert-octagon, alert-triangle, aperture, arrow-down-circle, arrow-down-left, arrow-down-right, arrow-down, arrow-left-circle, arrow-left, arrow-right-circle, arrow-right, arrow-up-circle, arrow-up-left, arrow-up-right, arrow-up, at-sign, calendar, cast, check, chevron-down, chevron-left, chevron-right, chevron-up, chevrons-down, chevrons-left, chevrons-right, chevrons-up, circle, clipboard, clock, code, columns, command, compass, corner-down-left, corner-down-right, corner-left-down, corner-left-up, corner-right-down, corner-right-up, corner-up-left, corner-up-right, crosshair, database, divide-circle, divide-square, dollar-sign, download, external-link, feather, frown, hash, headphones, help-circle, info, italic, key, layout, life-buoy, link-2, link, loader, lock, log-in, log-out, maximize, meh, minimize, minimize-2, minus-circle, minus-square, minus, monitor, moon, more-horizontal, more-vertical, move, music, navigation-2, navigation, octagon, pause-circle, percent, plus-circle, plus-square, plus, power, radio, rss, search, server, share, shopping-bag, sidebar, smartphone, smile, square, table-2, tablet, target, terminal, trash-2, trash, triangle, tv, type, upload, x-circle, x-octagon, x-square, x, zoom-in, zoom-out\n'
    '\n'
    'The MIT License (MIT) (for the icons listed above)\n'
    '\n'
    'Copyright (c) 2013-present Cole Bemis\n'
    '\n'
    'Permission is hereby granted, free of charge, to any person obtaining a copy\n'
    'of this software and associated documentation files (the "Software"), to deal\n'
    'in the Software without restriction, including without limitation the rights\n'
    'to use, copy, modify, merge, publish, distribute, sublicense, and/or sell\n'
    'copies of the Software, and to permit persons to whom the Software is\n'
    'furnished to do so, subject to the following conditions:\n'
    '\n'
    'The above copyright notice and this permission notice shall be included in all\n'
    'copies or substantial portions of the Software.\n'
    '\n'
    'THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\n'
    'IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,\n'
    'FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE\n'
    'AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER\n'
    'LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,\n'
    'OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE\n'
    'SOFTWARE.\n'
    '\n'
    '===== Manrope.txt =====\n'
    'Copyright 2018 The Manrope Project Authors (https://github.com/googlefonts/manrope)\n'
    '\n'
    'This Font Software is licensed under the SIL Open Font License, Version 1.1.\n'
    'This license is copied below, and is also available with a FAQ at:\n'
    'http://scripts.sil.org/OFL\n'
    '\n'
    '\n'
    '-----------------------------------------------------------\n'
    'SIL OPEN FONT LICENSE Version 1.1 - 26 February 2007\n'
    '-----------------------------------------------------------\n'
    '\n'
    'PREAMBLE\n'
    'The goals of the Open Font License (OFL) are to stimulate worldwide\n'
    'development of collaborative font projects, to support the font creation\n'
    'efforts of academic and linguistic communities, and to provide a free and\n'
    'open framework in which fonts may be shared and improved in partnership\n'
    'with others.\n'
    '\n'
    'The OFL allows the licensed fonts to be used, studied, modified and\n'
    'redistributed freely as long as they are not sold by themselves. The\n'
    'fonts, including any derivative works, can be bundled, embedded, \n'
    'redistributed and/or sold with any software provided that any reserved\n'
    'names are not used by derivative works. The fonts and derivatives,\n'
    'however, cannot be released under any other type of license. The\n'
    'requirement for fonts to remain under this license does not apply\n'
    'to any document created using the fonts or their derivatives.\n'
    '\n'
    'DEFINITIONS\n'
    '"Font Software" refers to the set of files released by the Copyright\n'
    'Holder(s) under this license and clearly marked as such. This may\n'
    'include source files, build scripts and documentation.\n'
    '\n'
    '"Reserved Font Name" refers to any names specified as such after the\n'
    'copyright statement(s).\n'
    '\n'
    '"Original Version" refers to the collection of Font Software components as\n'
    'distributed by the Copyright Holder(s).\n'
    '\n'
    '"Modified Version" refers to any derivative made by adding to, deleting,\n'
    'or substituting -- in part or in whole -- any of the components of the\n'
    'Original Version, by changing formats or by porting the Font Software to a\n'
    'new environment.\n'
    '\n'
    '"Author" refers to any designer, engineer, programmer, technical\n'
    'writer or other person who contributed to the Font Software.\n'
    '\n'
    'PERMISSION & CONDITIONS\n'
    'Permission is hereby granted, free of charge, to any person obtaining\n'
    'a copy of the Font Software, to use, study, copy, merge, embed, modify,\n'
    'redistribute, and sell modified and unmodified copies of the Font\n'
    'Software, subject to the following conditions:\n'
    '\n'
    '1) Neither the Font Software nor any of its individual components,\n'
    'in Original or Modified Versions, may be sold by itself.\n'
    '\n'
    '2) Original or Modified Versions of the Font Software may be bundled,\n'
    'redistributed and/or sold with any software, provided that each copy\n'
    'contains the above copyright notice and this license. These can be\n'
    'included either as stand-alone text files, human-readable headers or\n'
    'in the appropriate machine-readable metadata fields within text or\n'
    'binary files as long as those fields can be easily viewed by the user.\n'
    '\n'
    '3) No Modified Version of the Font Software may use the Reserved Font\n'
    'Name(s) unless explicit written permission is granted by the corresponding\n'
    'Copyright Holder. This restriction only applies to the primary font name as\n'
    'presented to the users.\n'
    '\n'
    '4) The name(s) of the Copyright Holder(s) or the Author(s) of the Font\n'
    'Software shall not be used to promote, endorse or advertise any\n'
    'Modified Version, except to acknowledge the contribution(s) of the\n'
    'Copyright Holder(s) and the Author(s) or with their explicit written\n'
    'permission.\n'
    '\n'
    '5) The Font Software, modified or unmodified, in part or in whole,\n'
    'must be distributed entirely under this license, and must not be\n'
    'distributed under any other license. The requirement for fonts to\n'
    'remain under this license does not apply to any document created\n'
    'using the Font Software.\n'
    '\n'
    'TERMINATION\n'
    'This license becomes null and void if any of the above conditions are\n'
    'not met.\n'
    '\n'
    'DISCLAIMER\n'
    'THE FONT SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,\n'
    'EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OF\n'
    'MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT\n'
    'OF COPYRIGHT, PATENT, TRADEMARK, OR OTHER RIGHT. IN NO EVENT SHALL THE\n'
    'COPYRIGHT HOLDER BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,\n'
    'INCLUDING ANY GENERAL, SPECIAL, INDIRECT, INCIDENTAL, OR CONSEQUENTIAL\n'
    'DAMAGES, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING\n'
    'FROM, OUT OF THE USE OR INABILITY TO USE THE FONT SOFTWARE OR FROM\n'
    'OTHER DEALINGS IN THE FONT SOFTWARE.\n'
    '\n'
    '===== PrimeUIX.txt =====\n'
    '# PrimeUI License\n'
    '\n'
    'License: https://primeui.dev/licenses\n'
    '\n'
    'This package is part of **PrimeUI**, a family of commercial UI libraries by PrimeTek Informatics.\n'
    '\n'
    '## How PrimeUI May Be Used\n'
    '\n'
    'PrimeUI may be used under one of two licenses. You choose the one that applies to you based on eligibility.\n'
    '\n'
    '### Community License (Free)\n'
    '\n'
    'Free for organizations that meet all of the following criteria:\n'
    '\n'
    '- Less than $1,000,000 USD in annual gross revenue\n'
    '- Fewer than 5 developers\n'
    '- Fewer than 10 employees\n'
    '- Less than $3,000,000 USD in venture capital or outside funding\n'
    '\n'
    'Individuals, students, non-profits, and non-commercial open source projects also qualify.\n'
    '\n'
    'The Community License provides full access to the core libraries and supports up to 4 developers. It requires annual renewal by confirming continued eligibility.\n'
    '\n'
    '### Commercial License (Paid)\n'
    '\n'
    'For organizations that do not qualify for the Community License.\n'
    '\n'
    'Licensed per developer, perpetual, with one year of updates included. Renewal is optional and extends access to new versions. The Commercial Suite also includes PrimeBlocks, Theme Designer, all PrimeUI Pro components, and Premium Support.\n'
    '\n'
    '## License Key\n'
    '\n'
    'A valid license key is required to use this software. License verification is performed offline, with no telemetry and no remote connection. A missing, invalid, or expired key may cause the software to display a license notice.\n'
    '\n'
    '## Full Terms\n'
    '\n'
    'The complete license terms, eligibility details, and renewal information are available at:\n'
    '\n'
    '- Community License: <https://primeui.dev/licenses/community>\n'
    '- Commercial License: <https://primeui.dev/licenses/commercial>\n'
    '\n'
    '## Restrictions\n'
    '\n'
    'This software is distributed as a compiled package. You may not reverse-engineer, decompile, or extract its source code, redistribute it as a component library or development tool, or remove its license mechanisms. Redistributing the software so that third parties can develop with it requires a separate OEM License. See the full terms for details.\n'
    '\n'
    '---\n'
    '\n'
    '© 2026 PrimeTek Informatics. All rights reserved.\n'
    '\n'
    '===== PrimeVue.txt =====\n'
    '# PrimeUI License\n'
    '\n'
    'License: https://primeui.dev/licenses\n'
    '\n'
    'This package is part of **PrimeUI**, a family of commercial UI libraries by PrimeTek Informatics.\n'
    '\n'
    '## How PrimeUI May Be Used\n'
    '\n'
    'PrimeUI may be used under one of two licenses. You choose the one that applies to you based on eligibility.\n'
    '\n'
    '### Community License (Free)\n'
    '\n'
    'Free for organizations that meet all of the following criteria:\n'
    '\n'
    '- Less than $1,000,000 USD in annual gross revenue\n'
    '- Fewer than 5 developers\n'
    '- Fewer than 10 employees\n'
    '- Less than $3,000,000 USD in venture capital or outside funding\n'
    '\n'
    'Individuals, students, non-profits, and non-commercial open source projects also qualify.\n'
    '\n'
    'The Community License provides full access to the core libraries and supports up to 4 developers. It requires annual renewal by confirming continued eligibility.\n'
    '\n'
    '### Commercial License (Paid)\n'
    '\n'
    'For organizations that do not qualify for the Community License.\n'
    '\n'
    'Licensed per developer, perpetual, with one year of updates included. Renewal is optional and extends access to new versions. The Commercial Suite also includes PrimeBlocks, Theme Designer, all PrimeUI Pro components, and Premium Support.\n'
    '\n'
    '## License Key\n'
    '\n'
    'A valid license key is required to use this software. License verification is performed offline, with no telemetry and no remote connection. A missing, invalid, or expired key may cause the software to display a license notice.\n'
    '\n'
    '## Full Terms\n'
    '\n'
    'The complete license terms, eligibility details, and renewal information are available at:\n'
    '\n'
    '- Community License: https://primeui.dev/licenses/community\n'
    '- Commercial License: https://primeui.dev/licenses/commercial\n'
    '\n'
    '## Restrictions\n'
    '\n'
    'This software is distributed as a compiled package. You may not reverse-engineer, decompile, or extract its source code, redistribute it as a component library or development tool, or remove its license mechanisms. Redistributing the software so that third parties can develop with it requires a separate OEM License. See the full terms for details.\n'
    '\n'
    '---\n'
    '\n'
    '© 2026 PrimeTek Informatics. All rights reserved.\n'
    '\n'
    '===== Vue.txt =====\n'
    'The MIT License (MIT)\n'
    '\n'
    'Copyright (c) 2018-present, Yuxi (Evan) You\n'
    '\n'
    'Permission is hereby granted, free of charge, to any person obtaining a copy\n'
    'of this software and associated documentation files (the "Software"), to deal\n'
    'in the Software without restriction, including without limitation the rights\n'
    'to use, copy, modify, merge, publish, distribute, sublicense, and/or sell\n'
    'copies of the Software, and to permit persons to whom the Software is\n'
    'furnished to do so, subject to the following conditions:\n'
    '\n'
    'The above copyright notice and this permission notice shall be included in\n'
    'all copies or substantial portions of the Software.\n'
    '\n'
    'THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\n'
    'IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,\n'
    'FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE\n'
    'AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER\n'
    'LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,\n'
    'OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN\n'
    'THE SOFTWARE.\n'
)
# --- END GENERATED UI ---
