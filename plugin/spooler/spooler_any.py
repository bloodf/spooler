# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.27.0"
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
PLUGIN_VERSION = "0.27.0"
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
    '<path d="M16.2 6.6c2.6.5 4.3-.7 5.3-3.1" stroke-width="2.2"/>'
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
UI_PAGE_SHA256 = "6819952330994359d73e820cc470ee45174bdef274e96541907e06df215d92c7"
UI_PAGE_BYTES = 1108328
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
    "k86oXCCW+KuOcjDojd932F+jG4q/xPV+1KOBQSMr3sUpgm74Zp9CZLD14UiaP0JviWYkzuvOA30fDGftw1X3MNz6ChrdXZ0cwXEa"
    "UToHR0em3adXk0Knf09S6NSVQudHTsajM854tKsyHr1XP46P7IxH+Nf/PzIevT+6csajg7+zjEcHbRmPDn6ejEe7f5MZj65hxqO/"
    "j3RGZ5+Qzujl33M6o4d/mXRGL6+SzujBz5vO6OVfJZ3Rg6au+vxn1FWfW7rqW6+uenqJrvrWbAOnP7uuevrX11V3jnSWUNhtwneD"
    "C7y/eooYdk09qpx16qvnFwPtQ2c7VoBicEXKcDHrfEK5wysS9pt0W026rcPuoQoZ4Xyv6/MrJ1aYrrG3NCJzjbcKRcWZcNaqN67e"
    "2/GtBcqvXbzbeF+5z+v5VPCZuGBo2dCIhjUVc6/ql6MOUnHP7je9Mpek+GpPX79e/XtzRdsInpnO1kasfH4eafKM+3yvuuJzfXhG"
    "ozD93JgVilFufHvH/vaO99s75HeUDxp3z+9aPLzffZJ7dzno4KV9D0FkQFq0x+6Zu3rt0It33Jf5+44HZc3fdzYYW/6+6NBb2v6+"
    "8WBp+fsuw8kgGr6rh8KElfF5Be0px+OmDoNZDN5p79jwnfIPgi1NXLyJHBSFh+TKkzphLxMV9jIfvGvEvIQGTBYhm0GJWwxjbJzl"
    "K1xxOHM47/a5Cq5l0sWwE/2Qo1Dmf7lQix/tcGnCNFSXdcsrK8rigQpUyEx8hbhQSSiDRWGHMtiBJh4r90/rK+qNKigaUQWIJJBx"
    "bEBKMQEmicWw9yY9HA4L4/yvnWzZtfZT/PuLNv/+wvLvL7RXuc8L7qdlC3cQZXw+YSCbMtEVfjqOoykAXUmnoqV9UQs4xLjM2ZGy"
    "PvxVPTAhB6GmAhOSy6RUOchrUgrkliWlUGrltpRaDmaWlJqB1Io6VX1SJ/TQjUqIraiEiS8qYdIdTnR0whjEDJwdJ8NlTcwkKrxO"
    "r0oOrJsolR1qbg8n+CsKF//e/TMx1rbRZHh/0LbK9vRDfxldxbviPiEgijcnZmY6C2Owq+UwBwqDuOSl1o6eXsn3Llptv2uk6AQZ"
    "1g3fNbMo2M+b6cnUW29uswphAW6YUffkYmqpcIVlepNA2eWF0RUyQSkG+BHzG11xfrdpBmq5LxLJffFy0ulEVmKNyAJSqKfWwIRU"
    "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"
    "XR2hFx4rTebaPgLEqQ9Mll+3rvXr3er21all6Kz7igsgl1ovKlWbgp7Im6p+qxss5hzqkM4HLuSV8LN1J4+PRZlXyPuhk7BTS6tZ"
    "dudu+a+0QUWyBrqwLMMJnVEKxpg/HJBpYbrBjGNQmaJduWQg4wODcWayL6dUnc98e+FaG3JCrZNOswyx6cQqo5vmcqsVXsKo6j7o"
    "jQLqmJe3GNVI76XozQKKCg/LTGnzfyR21jHIlZKevV+FbExe/fHu/iyvIrGfbtuQ69bu4FbX5NY0SpoUgqTwGKM19ZoyjlyWj+m2"
    "2WvzIDylSWA1Tuqza1U4156h3Ut95IyVJnozxSBBeEyeYCwnOCF3QAyAhdrYeORpXkhjhnI7BTU8tPhAz4PFM77DaBrhHlA1BPww"
    "cirY8qDIR/BzezpLgJ0n96FDGNEgmsbhkzzPZjjYULqKVSl0OnvbR0Bbv2zrwh8ndtGPEz7GLRypVsNwA2Ggvylgkd0SFlnW1sts"
    "HKta+LGswvN0qMrD72XF0fWhBQ6ZUIUG5hjA4M9qMXLco0rR1/Ixo0KHgfX2bDyJhiJFzaMQzJNdbTqIJror/qwW24uOVBn4XS3w"
    "NBp8mVqjVinLRr57mhwXxlLTt1hqLqZuMdO7dy/hrEe81x6enbI3HtNA1FesbmUebWHpvCf2uT3paRyPEimmlyreSYH124Nzyz4Q"
    "xCHDF+p4ytiHj04HQgEEHQiSOIPkCcjOs5+LzqhoWcRZsVgWbcLFsVTYEG/bRaBWnFMu/JWut+BEaHWlTE8KD9I1EE/su2Eu5CYD"
    "9DSlHe10DeZa52veVKVtV1IUUXYTNfhCeiXgUEQnb6MxmVO+evv+415o5MH/oyY1OTor4mZY8iMaeliH+iUrLqPeYJRNUYXt8j0q"
    "y6P3UXkMK32E+SX9z02bst1yeQHLvuID0HNVoCEKX0p5IgDToZNjRwFrEYtQYnltEDYdUO84EcBUXvX3DwLbU3DJqEOHTC/xZ8zV"
    "IOvwkh4BVhmcV+iymh6NxENWIPeEr9kyS9d/embB0Q/pPZRYrBa/MmQjQgRFb7XIz+LVAy8UwK2yiD4K599kaD/8CUPjbSoMClxa"
    "gq+MNr/ScUWqv2FAWmJPXKTBjXgltKyI5yB3aGZGopsnDhYTAG9EHtOmfIEgozmdpKRAIbzEqxoHvifAhYuNLLckE2vXIG6us5Fd"
    "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"
    "fnX4Eay2YrIeI3EF27eOfmJueNORRqsiNhvu5EjvaoXmevqGw52FrrFcTrYcvrBu7gSn1k3W/yxXUYJbWegpissIN2/0223IWcZe"
    "ser6qcHhXu0bRcQZxwagZIX/ZbR0PiHQqjzPNSSV6W7VNKWWnjcqSGeziJWtVnqunYgHF0zYZV8Oc3XVQb/sh8R+W5CIdx+Vydku"
    "Y8x5LfKyUZ2A7H/qNu3/1v0bFrlkNXu5x3/Pxd+TPW9+uietaI/YivZir0dtBMk4OonXZ/HRZPsomsb3t/yPX0Y/fDj79YcnT55+"
    "/vDxx58/jZ5s/fIkewL//Yz/vJ89p///+ePFz7vv3hxB0oen6Xq23i0+b52vH59Nnr5+dPJ88+jLzxcfdv9Ifn734uSHJ51f9n6e"
    "vT3/ffefSfTDj9kvp/GjH1//czr+mJ8ORs/fPdv7kP306uOb9d2fst2fp7/+9mQyO9t9Mv7jyZudh2+y3Y///P3L5PmX10/3hpc/"
    "RsX44Ub3lzcP1zdfDbv50ceH528fvLy39furncGz9Ufr6+tr8O+9veNfjo/vHZ29frl2sr7+6dfNzcH0lxd55yja+e31L8eDh+9/"
    "yc46L36IX48+DWdHx3sPu2vR0fpsfPzD+PcHP2+uf/587+3uy7frG+sPnkUvBudF/OHJ819fJTtH0ZvT47ONj88//P7Tk8snOx/2"
    "PnXOnu/8lq4lP80unu88e/fo19/Xfum+fv18dPLkj7MXg09r6euXo63zl6Pi3rib/jR4PRt++eHNOPnll4enm+9/mV5Mpy9+fBr/"
    "+GR0kd3f/PI2T5Kjz/9cH49e7fw6fPjzafL5p+fT4buim79+8ObTD2+Onx49fXF5mj1/tnfWjeKN7trF5m/vRltns+HWrxeTH389"
    "f/D542yWvU8+fPjh3WsAcfKqm+ez31/vPNgd7Xx68mFr9vrzb88+ff75/fvJ7tPjJy823gzeDi9e/XLvxZtRZ5gXj95+TN69mMV7"
    "r/5I341/eP9+MHgy+vDr8Yu86BT3k+Pu7iBa/6O7uZ7/NNl7k15mvz88HV+Mj87Si5ebj4oHF51B/Fv+82Dt+PjR8fqgePjDxz+O"
    "NrsPf0zH4/X42d7WP3+I1+5vfD7/6dPR5tvXHRjW22hwVKQn648edQbpyeTo2bufLqP3vz3rvP7lp+fZw4f5ZCPd+PLrOJtd7v42"
    "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"
    "X6R3q8ZuwptSeteYjbdjo5DsZ5tmZWPkXzrr13VtYRbIktx8no8Uhp8sw9xzpUOxRqLFNGe1F6uoxpgMYKSRHnOVlpUj4hXZkgvP"
    "1Vqu1M4WlXytVo53iJfZWMmnXwrDdWedqfeLq0FMsECnjBWx8GqsRK65GTWK085Cbm4YdZHh2Ux2XgHaGh/Q81qO3azyVp6JD6eC"
    "vgZyVedft3KJeJXA8GtJrXL6hcrkaFYablJ8Lauog2mMpzrVhKLUxamoJzhroW8NkbfbVnbYz1rxxnJFWylDzLcyMbHb2a3tbLxa"
    "WQA1S6XCtfZK47OkKlHtl4qpD1/mVZktvwwXzHiyypR33bmRS0+ymWQ39zwebcILaRhmZ8m1vLC3tXVzsOjPpvN2vbJNFq2ywZQz"
    "8WZqLs7zcj6uxbbZDT+ak2ytxo+FWacdLnVSUpgtjFKSohmvzzaR6YKp53LBK2WhII4q20bJVlWD56Zms18Gg3O9yVIUkZotB6NC"
    "a1halPhps79czkYC8M7J1aJT3nWYiWjzpdfOUl3XLD6R04nXgca2waRf244HueV0Pt5MNIpcTNdSqq4WwlW2W6jzwzWdWFgttR6e"
    "8Qum/lxML2JE64Vq1FShnXiG1U6GrXFf3UkbU+XqDf3VoDO5wYImWslVpTRJWWpMaDwr8Dyctm0s40Y6KU4oSc20OLm8blRiqZxQ"
    "mlvPmfLzrrUd0h22HtZfOlpu0CDlafl1Hh++DrOFfHw8n/J6fiN0U+tYS6KsWmZhb3byi6GoC8Oq10XK5lrV50LJGAyyjVpR3tib"
    "QmNTXs2fx43KJNvo7EbjbGHeKsfKfY16HZnTtVlv7PqjFF9s02zDZLKv5o54ric6jfWiUh8k8oU0OX5m2is7ty3OwywTKy6KUzv9"
    "WtSp1gtbCs+UtrYk6U5WT3KGAmzfoNxNygl7vU4uBzatNezJ6zhJpl+2ueV6SnWndDuzqSw6AiVzU6uzowU6ZZbXA3sKXKC0+mpw"
    "Nq8WlDk7X5gv9IjhgAvyssx3jWcjyUstaUHn1rq6mSnFBr0uzpXJa38jtibGKlmlRkV53d5MVaMP6tyydbUZH44X7Qm3W9E2r3QK"
    "g9aMKVKTTr8ozV7aLVpcZbbmdFy1gRsqjl5fuRSd2AwG8FheRo5tX7J9U+HX01rHrpVkIV3rSh3+JadVZCLFxneiLpskJSTn8Xpl"
    "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"
    "OLIBChaZQfcljJLHD093sGb5oLWzHyigrlpFXweXJYrbF5KAubFHxQ5urGHBZhVxFOcRXDDJBqYu4KAEDVNOvQYTECReJ+FQDiW8"
    "T2peDqSjuTEUc3FMv/D06dkkuDxDVpE9h8VwSd/him26uKf07BOQHL+r5qN4m/nXAbz6Ca2MWFtgGhn9uz6wj0TFCW3x/7B8S/ff"
    "1wG0/xTu24KyWiIGzmNIFui+M1TqVnempSIDdSQ0TEoQIWqLO85kCrMT0wZoKjHw+ZIm3qp7n1ZxaHbQEC60BI+nMhUQPAI1qhK8"
    "aPCGqkUaGaG2hR0w1FqA0dfLwewMCVCYj6BMSiuSC3lHqhD/uchqb2vCcFhjxJc/Ed1cXfYySWe1UkUoMCQJDPLQRUvBHDZ9cu5M"
    "roLLvAVZGisvHorTAIcGY3usK7gtR7Ou3Zlpp+29WHsNDvT9KlOGBPpGlSlLAq9uyHNnyjzMgnkbyQwqclM6FPMebct/PSKDrOqL"
    "Yd3iMtONxL25ZY77Ss3eW6zVaVRpdWqvTezg3qgRa7hzNRTcoLvznZWx15bPBmmB8yQd1+CxwLsYEpWqjVQG7wwvcddaTjOkSa3D"
    "eGm7g7v2Kf4ipOiyNHy8/cYoNd9rcWdpOW6PvNG8agoxhaSl5Y3tsy6pKUQLVkvDMdu0I1lUgpLFlpa3tddKpKYIQ4Bbmk7IfnOQ"
    "ujHVUl+rEK/dR0MZLCm2ivBbeDSUIcTLViFeU46GMuxJ8Vtt1H6OMuzS8bSGr7faLQlraxiKZChh8cq0ZOWlz10ailm4Nisy9rLq"
    "Og3lLFyhrmS+9LtRQ1G77YvSMv3S51INhd1fojAh2S8r7tVQTqtVW+meqRaHQh60LqSwl63Vp63N1sXYXaoq2aGwhevY646NBS6l"
    "i2fdO/tPKF82pYAnxo8ZPsnmaT29zdPZDJvJovkMjCyOy0J18XBTioVSfJO2CKjyRQYr1EK/b7A1HndSg2lxeBRTAezYCDQZJNSy"
    "CpZJg4cNsBXpftuaWv3/PIy6W3tCpfnTQTj/i9Je/pu1l39V2ktDx7pQfSmUasLk6nr4m814cUVbgbQvyKQlmW0vML5GUc1gaiaU"
    "mlGDxE6oB1XDK3f/0oBQE5YzDKR2bcC1yAdQxhbMBaJYBeUCsQa8XyDWKDtYEjo5w0pOx5M0A2Y+CLIFBSMYe3PBWccqM2TQs9YI"
    "cnk9glxeQZDTc4NrAdHj8tCaMmuaXeGunikl39NJUMvAlyhxziPfSvM5hvsWq/9tPEnfZU9FFrI2ZEcwIajfjMr+T1pYHw2PffFc"
    "+3fK/CK5c8KC7iDp/w6fhOswZUXydDKNy6BkBcPxEJZlgqcuztMG8mpwoG2GUr9iCPco4zPK9yQbS1E/gpFdatD2vy/TNEat/x1v"
    "+mbTcm/TmCVu0Tiyn+5n3Ly5JW21oxZX18Rxda6YzJIvheW2LqSU1ovfVX4yfTnhHayjJ9fgoVTrE1LPqIrRNiz4lce53V5cg+My"
    "SirjdNLD5JO56WP+j3Y+5v/4lnzM/2H7mP/9W/Yx/+eX8TH/exsf87/dro/537+Kj/nfqj7md2/Rx/yu4WOeHPp8zP+xwMecvmIf"
    "83/cuo/5P76+j3l5aHhtR8pjQDmFW+eXqXHJDm2Ni6NcYQtLqSexzwLlwGafSWa8+ci1kJWaMW5oqJweKiH/+P08gq3/zyXi1ZuH"
    "l+HxcrOR4k8Ny1Z/2E1lFCocVu0wwWYQTTEhphVu7DlOjTC1ltOn7X7K30kj2cqY2a/DCONw+aqCO9x910u9PAznf1V3uexQr6D8"
    "8MuHokoP/wxF9f+3UFTpYetQVPHhtxWKSvSnGopKvPhCoahI235oGZcLYrGcfIYkSvW2jbbls0+KM8fyPqRjj8nF5d2c8MgZRpQp"
    "Fmn67spirVdM/IqmMAG6jF6WfFx59i7ghg3R2gDOBKcoJxOnDsne4W0CY568zkhyVBH2mDV1RpMkzqUJoFODfPlZyPk0BzXw+Vpu"
    "42THF9CoGxD38OCIA8XUH0vBxytcWcJ4QoptLQOVekELtdWWtvCK84H2m5nLermL1X+N3e++bJbBUD5LBMO1V0UzRrojn7HfKCEN"
    "m11Y88n8Op+CYk6Tm5bXZf55gC0IQ1rOGUTTEXXpl145F3aDoNrhpZJyiUTvLVoOX6LHK/EO0FO9kWumydyCA2xM4I58VJkK5dlq"
    "1CFJgU8i4NnQXBUcnkZhpkznLC6qeIx8EK92HXBAalQILzYZRL8GOhCYMhuMNVNgrKUAYwVerQLGilcbYoH2PXK9PFIc4tVVbnDI"
    "eYXxvaQGVtBZSxudtTTRWZGvcujCV7aQcw3YtL6i99cDU/xUHLYSPxWH35D4ifqsGZPR4TcsfpocfhHxE4zZYvHTxeGtip/MNt2e"
    "+El20hA/jQ9vT/w0PtTc0alX/FQcNoufTvVdhTbGrYqfoMavLX6aHSpz3g1NQ0050/mhx7KX0QJNyqqHPO6oY1H7EOPxUoPcxu8k"
    "WB2QciPNsfudR5l5mg5gf8N/l9rIl6uJXT7VFjcJDluJonqLvtbiKD1EdxA+I6k/tKb96YJDa2oaZKpA9DoEPTfHlG1xp11L4C5a"
    "AlP3NB8Fo27gr2QV6aB26c4sr200xQYWKKeohO7oKhZMie+Is0W4FRpJqCf0gsIYjROMFWxKByDGgYb5HMQXwqmzX0pU5YEUjfUU"
    "5pkt6SuFHULmMdkWIj/p/y1NsyVegjKfUA89L2Kjx0veGtm2qDrZTQ5a9nmD1jBYdYPE0snZoSGvnE8PpZzy3JBTnrXj0s6+JS7t"
    "zObS3n3LXNqbL8OlvWvDpX24XS7t3Vfh0j5UubRPt8ilfTK4tLdeLu1sAZf2VnNpZ7fOpZ19fS7tdyXb5fPzKW3R9tghvKU11IZ4"
    "pl0JjzjlSA11hnO8+J9Px4kBz0H0LE6zciMej+2EPDmffjAKJjkoImRjBcLQX+Fr0JnTBAhAb/wQACg8gGNznBazSfypqRA0AWsC"
    "RAD+hjq5CJ0AyzkU49MUwfkM7U+h12zluSDnIxyXVjl/lm0sFhU5Hi8sUHVYimnqgRPO498fq/kt/GaZW+hljPMtnLVFLgnmUcEF"
    "waxsrvpKGMa2+YL5xmW+oHlY5gOajmU+QLvgpSoYj5f95CVtqWW/oq4v+1EjkITIcgTLP1mcD3ecCRri3VI66wL0EDHY2ezCAryo"
    "zVmF1KhVYomHGt0Suq8Affk1LVI617qyDLUdrZIVfRA6MPE550HgV/aLgmLOJX7rK2BXklLg+nJ2ikf4PC2Aeidc1AK9lO+7tbV+"
    "8PZjZ3p6GgzFe+VoVfcNIzeHVgY4L0/HQp9lpstc2SE//5iOkwB1AR6jaymJFktI6FHE07F4gLPgxLJI9LzfTzryiBqIULbOdCid"
    "L5Gr482TjqJ1kfmBnKm+LjHs+Uusa4wueW6jdHhstDXLDjzuzRtpz5FDaWvWnNWbNWctzJqzWzNrhlYwf6MPIF8AblejcJa+O5ug"
    "uTJ6tYh6ycVXTalyNk5YVRKSpgCXONdXVeK8IfGHuRLC/cRaDHpd2unGaiQvi1ESdGEYvd/2fSs0qi0PVndfcuZIJDQb413IwJI7"
    "baNv+4w761/ZfW9JoRU01GL1/K9U/EffW2Y+xaszIiPziBKrs2F+bvKUkWAmdSciY6B6dVt43r5BKMqsNMchbHQ2+mgYvbAIGZnE"
    "KP2oWjwyShtX9cMkzt4HFYrGa7bnzysWtI5mBw2HtV9tu7lTPUOjI8aZ5dfSQlFtZGX3SkuU2UvFFgiFJfDrPAgVUsjm1VVSgV3B"
    "fCoD7ErysKwAppiHlTi/RfxbOxFFb3mCx+ABL/NAAMvr+B2+4MrFx5RUojA5sCEuR3GRDJ9keBnr0W9gkWfx2Ew5msWjZMhrUbcZ"
    "BS6kZd3nIopRPJO53NYjagv7BMud6InCytdrH8Eqa/Z4Ym2C6o2vurc0pUnmjTu+bL/B7I75hlxYF3dKYpn2fTMA62P6keIY9YyQ"
    "qIjQ8wucDRjYlQyo0M6qw3dV5RgX6IhOBKMav+XYnMNNOBc7p9PRRREwyqizWszpo/pfz7j2XNf+Ar6RtecLa8/t2vOm2ucCQ6hy"
    "uNWaNjSyMv0+GgICVyco0mcsMHWqJUuskIoEorr4ZBa99pybtMC48a457Btuu/odZLNqbhez2sO4vLEtJSPYXqt78Xis2aVWjExU"
    "LsVF7NfzNxRe2JlQV1rUdFDrLjfzD0sNCG8035g0reUISMciPi6JugKPrtpXKQhr7G7Wjngu1V1x/Y8nk7fx6H0d71T9SlNIL81F"
    "Y2Ibik85fw2eX6CSyNFbstsg12OMXQJ3HDIYH/goc4+0R3QLEpWxP7l4eIw2StxYSVC9jfVjB95Ygw1i7mnwJHbbe+aYwfrPdj3X"
    "SJ94qtfWnklXxjw5BWYM3dDvJhMdWifj6DhVzkdJG9C6+y165xN5tSUBl9M8fYemXCQGAMrDR6vFfSgqpAvsGtWrQDSVHpotoCNF"
    "SBwyixG1UBP3jT2oxEJra28vLNFD5MsVRqeIMqD7OJSeh3dR4p58IMwC1Fd0/sORBJQgA4pPosuZdJwdxm8LuJESIAVcbuEEhiFI"
    "fU1wJoUT8RQ/vCgLmHTqvRSuBMZ7duj3vXmZoC+0+8YnrOlbUw58ulkp3W15MtH9orQmA1YPSoayJQRDxvw9OkVBb+a7Ju9LCz45"
    "tLblHnExsK1mKj3pxBfl9ClzN0YdFMinumVsWZPbJucj1CRKwVViZv7Rtx0vskXzxjn888Pv/LMqxoKv2ctL5OrnnwWX4pWLRGpV"
    "nSCPaC8PL90cTaYF+i9In2lFG/t3ZnGWTO6cRCvVV6IWdqYW0b/55siyTbUgJTCCkiyuWnsKYd7i8+QXYDLIach6JxzUUD8d4tUU"
    "e2QVX8vu6k2KfHd123qrdbKYtcPmqVkpNaHBuR+e/LgxjXeKklZ3eInBzB2Rcf8lnmKJOA5qK7EKYb62UtRgYJS1X62JJUTOkQWz"
    "kGiygnfyCglCCNAgqR51CPFXvgKiDA02w6olziGDlGoMxIHOVeAerfUPbLUBdNU0juSS11COtQk9Q4jfE1ROm4mvLQWGQrWBucMb"
    "6Y63qDY9aq6E57x+VenX3sVS4RjEtrFJZNOGYZO4H+NsPMGd0kefnaN3vg0cWSvIXaSJFDBYYN2iXO9hLGe6vq3VgiTUrVW4/1Tg"
    "gbDPkaaByK2ckmbYqf3GIVidjoPQGInoIzRg+tGzE7hUsXDsKvQOqG+65zNUQ4nqvCu1qUbWRll+FjZ7XAsYLHJJgi+sBFZF1DRB"
    "41EAiUlvWUFOsgEeuWfjupLvphiXSHKYhiK9qJlC82NX6y7PGpc/FZytk/tYNRoFDTOPWdblBO3iENnRLXEyHcUTtMcR3rHlfE6y"
    "2iPbsKCm0+5AycVufSwS9YDMlaDG4wsikE5Ei/3DwI3mEh8BTeGmvzntPPrlYB61/zT7pD89fDk/mUfZlIXUz6mIuqn2FzporFGW"
    "rHRYPMZKL9ywYGWeeu2okqjpoV1CoG98TQmmVccSpRhX46ur47psJ2yLom0X6quwmyIE+993peDm5YWUwt/8bOka1HwBTfySNYri"
    "neXxqE5m564RZdvTYpGoLPYA1ySLcX8oNrFp8yNUo19qSKhwPf5azvUFRh8LV1WNDAs6rvFRnsaVWk23Ne2h5q1Ahc5MKJjgwCPo"
    "WdBA+IpO6adKuNFb/AGuDOMD2T9eHJKsePv22SNq1+FUjSv9S1Zr7BnDZIANy55qK6gXcR6fe2icaTGA9u080qa6NCDDAGWGgKO7"
    "uDDHZMincYxHaP+p6jMqsx0WWZXT++ljJPidv0YvpnkZT3ovPkX81dEkLs56Pz0Rj/B30vtNPvV+fBK9yjHD359ELyYXRe+vT9Bm"
    "Mk+oAWiCKUUyvV8+mf6QR+0s7Y++JUv7I9vS/vG3bGn/8ctY2j9uY2n/6nYt7R9/FUv7V1VL+ye3aGn/xLC0P/Ba2h8tsLQ/0Jb2"
    "R7duaX/09S3tD9EfMkXzdjxjN86n43gyPIneY/I0eyyiaZJtiAiWqRT4hs/ko8OaaChM0NHZEZ+Y0MPTCJ+YxsPTpJ+k6BMmaHQl"
    "cMo4/cDhUw0nSiYlHugo+YLcCMWNWMYRV+6ZssSqc6Zl4P1YwoVhPUBLPpICNeu4drqhvxHVUpwArVa2UCpRM6FBFfdjuGROepni"
    "gcXbE1cDGnfsBMM1jZ3epLMCFaieZHYZ3dWG97LlEDpejML0wkg2Q5RQDaM7tIDouqpxy7xsp8gKLMFsOruYoetnfpHIEiSo851e"
    "6jIUnGEkgldXMwzijhZt8M6zJnc2elxpFaw/Hzi4WPuV8BD6lI5t6ybUvOggCN3aj7wmV/i9scKc1eRtNrvtuhwbnYsV43CRgjhz"
    "0jb8fVAVU1RWpmlYf3UVxCYXNxhqVmzYEw+47Z4ET+PAux+wmVgk7QNaneQWOQ+jN+jU292FtaoXkSRJcj3IZzn96JFDiLBG9CAL"
    "ne6HYMS1NHb6h+AVrWdyN0o6s1EGA74RZ6OzaZ6MN6QMLERMetIGxh1bxwsvDF2h8VanQhbW2hlvKUF+W3mrUyurAUhkxirc4aIJ"
    "reyPH7PATwI5IpVWsmGgcmMziZ1Hp4NnX7KH7ziNJ9N3Mmj5sUlPD9UoZh3HceLE3je0246KamdW+MaIMbzxX8H3xZFizmAHHg8T"
    "tis8CY0N7IS/sPaiaVyARdsp3koQzF+HKnGiY/gKV0oHqwKV6quk5lRTw+g7RmxPo69/mkT1x+/FpPH01RdelJHXnvFuthpXfC2q"
    "1RqUrOKBP5ykGiKgQwSosWXD6FJbkKGBk1xvNUS/as0qg5lZJ8exGwuovhTj6Ihgw7w19swSVR8PhaUl7hnYP2TIewKsgGTzenjH"
    "3BwMN4fChciCTFgwMdYpVXFvCAg/4SAQ441gnsB4Kq/56D9qVppm4kiZLi1eKEZefQK1rGdo0pTt2kky/CsCd2rvXWNqRUClhhl2"
    "aqyb0cWTJYBWLbUBIawKxjCwcBe6hKBgC/5bM9jyg9o50xmgEz8gAsNUqFfijqNwidDkdPIrXSj1S5cfrRETira9CiSH+NTKhxGU"
    "6N4DzeAGsJRvKFgUTuO6h7SngI2dZq8pUkFPN+xOJaqVPfu2HTJNfE3ImgpvWNdgg2SLoUM/Z9UiyU5JXqvCSwkkC/dS8J+m+xiK"
    "Qhtpts5QQ61dgX0Taoq1yvLI3xxsymKSxTlDvaK1xm/ggoDohWgcLcYaLA1fPP/q0v271vryLWxLCF2zBGvWnsdOPMCwHssuQV+v"
    "Fi9Cue6sxehpvjdIqFqVFq8BTNTFcNBwz+a7az1/VC5ihyy/rbhjPC3LKAnMAHF9Oqlev7Vu0Utct6LFa5tttJmQ0l2HMU/fiouk"
    "fUN+anyjVYRw+DnLzqu2bOaCXBP1oGaNORvWd6GdTWd4BzFaEV3Wr8xqb+bLXoWr7ulXV0NSOsDQcEjfulmobwXZ9tRehWt2hpTJ"
    "LSDUFjATPUSStll6WHtVPQmkaKdmMSnVrCPVar2yHpmaZ4unul97PlrOHkHdomlaJ0Ih3bRInIYtvUIczANYHqiKGvoFIjWV8oIw"
    "VkT0azBcGa4jW1ZV2cPk1iyZzzrEuYa3cT1zZuSAqV+VI2DhUGA4AgckpCI/3IwWrxfje2u17LXlwJdeK/R900qxmrRonfwaUPAC"
    "x7Sg/dQpEDK90qxxbnGctbnuG4N2vbu+470zsC8LW/PoWG0UE32kekxbr2+od59xQBszsNS6NcbCWrcP6qmcbuT1aBx+30jhzCa1"
    "W7euncoS65YQ8JzziNOiypzbmDd/DE1IdHiI1O14cnJi9MLqO8qM6Uxm/2f8pYW+9PicY/oOTTkvXca5GHFK/65gAB8dkqbxXwr/"
    "iqV6MhZuewQs4VynQKgoNC5G5iYYFxWnG58MgJjozKquNbDOQmAQH6T/TQdulF3kwvlBd1VayNLTEtERy3oYkbIFjEh5azAiGDG5"
    "4sRsuW1Kp1zXG04O3Ko5cnMH+d1aGNc1dzLsxUQ1LQzFOIjuo8mkhY0YUCGVW8YksWyNqAe98cdIdqV39sq0CPq5TpOttqClncZD"
    "4dK4+2dq4b2FEc4/oRGD3m1q/bmXqZrR1XNKigP62fpS7lAOFIMgd2kSe3X6AC2t3/nmEV2fS4eQEqspUUNhCEHwlykUEFmUHMC8"
    "ACtaixktQYAcRs/lSKL3ucfR/F+Kxv7MNPYXRWOfGvqTdkF+NZV1Ao7fHvKgF2rw86MOR3AKIqCygleoQdeDaaFA2A3vG0ELBR7w"
    "DQKymdGzm9DYjMDaItsxAwKK3PKEO7kFcLY/Yzy7bAKGVzPySpMoHK39L89CuLGfv0U+4c8oyv+doigjkLyQrmNTxCHVGFEZLqFn"
    "xlmmFqietrknurJpRLAoBPMJRxiqtKsSeLlF4OSmdqjQzDWBmb0hlz+nwJNKKB2bi+r96zA6eGVaY/V+PzTZxxftDMpffEsG5S9s"
    "g/Kn37JB+bMvY1D+tI1B+fPbNSh/+lUMyp9XDcpf3qJB+UvDoPw/XoPyFwsMyv+jDcpf3LpB+Yuvb1D+gxFgpzaW8691t2yX4ErL"
    "cZvoagQOOyywDOCBI9gx7wPo1ltcvOVjEUOidoxbALx0ogtzkBAdyLg8M4xZZIjp+hNQhZuuP7znEVCSZ4ftw0UbJ/q1wkXbb1hI"
    "kqIp4zhhnu0cLiXpDA5BraVxLvRZx7kbmpINugxqeYVrNl0aURKVOMq5O2NUUCf+dJ2ww429oqQIhmRABWRpNBtoE0SbptAxA5Ea"
    "idjDazyVQWa8y4p1B/YrnE3cnPBW3prpgqxR/Z35s1wh4Ssbl36Jbvlh6pcogBemH7t+iWI4IpAX0H6JUlh15wO5X6IQ1qN4gO+X"
    "KAMlbTVY+Mu0ZDw2CvIg5C9RFguOjOKq0PnLDrRRWKH1MrbAJrOwgatClKozjUd84tF6AakRpFUSnO4iglOBHZyrQmit9Fzb2/oy"
    "HBhCDe3vIwfqrdqnOmpAXX55A7OicdTRAG0rWQnLUf3E1qe7wTmq+W09phOio5YqqSyyDhWtw1ODfAd5KxE7vAPkZKLvrPAd9lf2"
    "S9LGOrivrkGvZ+YrkltePz9L8a0q6d6ikqoS31ICHYo2woj0hN1v4wnqyIndYphgVCxPm0uSAmYujGbfb6DjKcaCKr/ucc7nJKGx"
    "KP8z24LP6/Dg1ST7DCZ8ZgYefye/VU+tNVinhqhK8meRwQrNq3XZUrTDdZuxsFRcQxvXGMPBsLExNip4PQ4uhjwB5ITBXA0JGhYm"
    "vIPGX5aKP/rBCnD3i9K6/Mpalx9dzfZy+hZqilxh8tFAFJNJ4zx+x+I3KwntJOyUiVDQq6TpTD8xUJMq5+spe9qEmboB3Q/1Fwdf"
    "hg2vV+5cV4tSTPOyXkMzLOAJ5l6XfwT5nxoBtI5blL9s/sMcFmLTuNDdCFvyc1LGDUGkbk53xhN+sDjs141HNHpsLiNf0/JkiuPV"
    "bpn8qTS7DaUZyatQmnKryjHaO7ECf7HYOvGGRQsSic6fg4qRBjppwR08ojS4cCuS1NPQecbSi5BA94JS4hXVBCeG9wuCE5cdLIl4"
    "1b/k6Ri1MkUvCLIFBWf9bEHBfPiqMsOrK4xv0VqtmNerFfMWasX8Ns2P/AjdisU0j+6qDZJHSSW85yoBMkQsDFxabGmHCMsyxQxI"
    "YqZzWBLChxxd5DhhDOTZySAD8h6Y6dWPw7W15xeBkydSEcPFqpUizVBh7V67k55YF9rJuNJ1T2UG99N6VA+A8yGl46LCDT5qqcLR"
    "U7lN2cyQLVV0Ff+6pmzB2i1RuEOIveUif9i6SMYQbTXSFq8piP3PJt9BaO5t4DfNjwjIn770KclKtqDFYCg+SSWQ7ZoMistC4TI1"
    "9Yd4/C5hGzhvEzve7gSh1XSDqRQkyEiBRlhJijOELf39RneQ9JL1LkINqmqSWnxTyYVagm+L6rmnlGyPvxdQP9Zsnl1tqhbc7kC9"
    "EP0J7ATZc/8ULcxqTFYoT1ljjDR386dNyB/VJgRblvZlk5xIHJ6YJTAjKQ913P9N9yXcT5Ug9zg+gXZbz00N7rtt9WeLFhdIk7Oo"
    "OMpEsITTzNYILjRydi7piW3HPJJua8vY0IRmKA7e5IM2BjRVxvisrX2NamfFpqYSdq9Ng4T8ua5Byi6mX2cZs9/ClEdGInEMcqLk"
    "hO/ZR3S3qHQFY8IQy7wvCYmHRoaiy7dCJaE9iSbKLB7Y3EcaseJrojpBpNVH44GXwWFBxGx1U463dWQfZycdumFLrfuluCAlhrCi"
    "nM/V9Yvn30UfNpaJGnvsV4dLizLxk8rTMYOAzmbfbw6ygx7+erg5SA7o1t3725N5hMbW2MxFR4M+Nq/bDq57OE6KEZACNDfoiZYN"
    "Y500zKZZMpwbNqKO/RZxJb2zN1ErQ64I+/ZoUkJf+SfJD17PMCk7MJKILU8OTMOv1+0Mv15/S4Zfr23Dr9++ZcOvv3wZw6/f2hh+"
    "/XS7hl+/fRXDr5+qhl//vkXDr38bhl9/9Rp+vV5g+PVXbfj1+tYNv15/fcOvf6DhlwIHJR1KMYtRJwMtEL/IWwep/bBWpKJeKFFf"
    "5Q2fHPpZakecbLb1mVGukl97LNP+XotkikeJNkermKmNGszUVmw7skKZCpg8nrIas1lUDcQV15yxCptL4PBxLmHrFolpcL6WkxNG"
    "YnKc93LKJOwH1obmZZIDqHXEtwHwDFi9Bjw9Df/3oL4sIQjk0sRDG3y+zfoiHWC+RkQ+IXyia84CTEElXONi1WNDsSgGWwAmKKVq"
    "utBD5fTtLZPEX1jodnOhJE/TpdJjbbHTGZZ4r6nE6UwWNp35sQ3hLP3L55s+OoTjTu3+iO7UUJQ7vayqULhjERkstaKTuOOjO3eU"
    "lRLnjpYy0TTa6FInbqWrc5sTvrHb+rW1VX/5ypSVCbEXmY2/Y5FlTlYy5kZq2EeGlJOn3khohW7p1GzgnyyELBmZlrWMrOmBLfHm"
    "ohFsYfHG68/0gvXn0B6wttWLaagqzhsb5ql6H6+bsK5nwl6lJaOcefss3jKyn68iAvirbY5xytgNUkBBW5WK6Xx3oa5bjDN+hyaF"
    "aDdbvdsSypK4Ccf6Kimvkfpq7L6kVGvcMJVxiL1tTxmiWC5CmDbFcKjyTIflKmy2I191LKq3K6hwmFHwF6HXl9vIIII8URYtdIfy"
    "SRM6LM6BLRyaS07gc8yQ52IEuYbl12QYjnNm2SWsWriuyjT6XoPFuOXQ7hPsVW3KGyAplti+Ui5INqufa2Vu+JkbBuf1DW1tjW4N"
    "r4Ky8/RqsZ36iCdj54vbqVMT/zRU/9NQ/U9D9T8N1f80VP/TUP1PQ/U/DdX/+IbqbK3+j8Nw/qOyUf8726j/U9mokyX6j0KS9qeR"
    "+k0ZqZNfbr0p8MgyK/Zk+NJQP0vYwd+cyfc3bRn/NezZlzRUz4vS39PNL2XGDnviQzr2AKZc3kX5u4AsfMMXF1xl0V25NaxXUiRY"
    "axhvltHDCPPP3kmo5pcIwwW3ObsoJxOnDgkS8G1yCuP+OiNFeMUc3qyJMWUDYebi1CBfLjKHj0rTID6hw1oJR4gI+G3hLUt45wN8"
    "Ac26AZN4Hh6pailG+XQyIS3jzVikq/KaDMapT7bVONPXzGM6bmbO6u3HrXFKIGd11GmYGm3JKZ9lVMm1V03MjXTHztx+o4zNoS2w"
    "wqyZZ90xK0fF3Cc37fuQ+ecBNisMaYnjDz8dk3390muvj91A3j+Bl8paXyR6LTrk8CV6vBLvAHk8Rb7iGCnPhXKxc0PZwrnBGq/H"
    "jY407YdsIdJW0g5qK/EAbCVRK4itJFoSZMttUm2NddhXZOog0K+wxh/1UVGzvU0iP8B5CdwdG1W2sBTLhEYd8rDxWTV5jgyuKokS"
    "ozDTtBOWCqnl5Y28Jri5DmFt0utkAb1O+skCep1Y9LoOSAzWSe9HtD1zQUd7v1hAYn9rZ0/2t2/Jnuxvtj3Z3W/Znix5/0Xsye62"
    "sScr39+qPdndr2JPJjtp2JNl72/Pnix7r+3J8vc+e7K/LbAno6/Ynuxvt25P9revb0+WvtdAYpqymrZa8XuPrZZjoMXm+8I4qwL0"
    "XDXQgncVGwNODQXyF9B5I41NrmBM6FqOilfz2BvgNn+Ppi4J8ziiAoqKaB5WttWLuNcoi5jeoq8Nqxg1Und6wbT20IITbdqfLjjR"
    "psaJJg1URhsFK4gxajM1Z27YUXCnjbhuMpbQLxwAR/MWMN6KAsD0uZHdylzZPKR6jIdOZCh3dBVboqyI6JYAFfBIQj11cedcpgSW"
    "f1MDRc8s8X0uRXI/JZ8qWtU80s4I6Tw6XnXf3gx2na4mVEd1rvilVb3n3KB2kiMnuTz+VNFzW0j3TXmnlO1jmmWIt9uyHENQSpd9"
    "Q4Zndd0jCMuqzoFarJYpnw1DFJZppxBD4JUZhiO2hCuzfTUq4r+qxQOL/UyAPMuPCQbm/rWQ8urUmVLG5hgTfDVl594NaDu7D5ZV"
    "d3oUZ1ubN6Y52+relOpsa+vGdGdb2zejPNu6t7T2rKX9jDSBMTax8aS2rLCzIgukyPDLss2vrH2I6gZ730EK7TillyjUL7Ej9Bva"
    "BOpRr3mVZKzwRgseCm9kxdyTD72gerBtWgeb7wjznFTypC3+m59O9QcQi5HSykG0eUPn0PWOIVmUaQS+1bIoQ8/nFiUMv7eXKInV"
    "g25B0tr73hIlCbWiXRRZeO+0LgU1kTdxTHuUNT6z56pqzmPCLTvzUmtG29kWVPWp2LU/PAfxLTEQrIfDN/BvlZ24CW7iJpiJ7s0x"
    "E90bYya6N8dMdG+Imeh+cWZCupstZiqq1IQSbeLxR2c+aF8syYR4LYu14bbNlWz9yZUo42kPV7IsubbhvP8wNqhbOzdhhLp7E9ey"
    "+zd3Ldu7sWvZgxujpNubN0NJt7tLU1IPq7C9dS1e4Zo0uT1Z/JJ3MAegNn0fzv+pTP7i9yRAn6KwOfl9FkPi2JQxF+9b6eGK99+Q"
    "Ho76rBURI62ISFhALNQBl3NWPqD8vT95r5QHixVz8ULFHGrG8v7mfv4wltqwfH09zPrxcX4SlYxAeXgaZOijhIAql3NS6WMxz4on"
    "Sncj1RoZHhLpcXbST+CPUhilupuTRd3sww+psMtXUI0UQl6o9ywujE7IGnOBjKWaigoVaGqI+uc0u0j2M+gKNCc/8egHL95/w8rP"
    "8ZdRfsKYLVZ+nt6u8tNs0+0pP0+rys/ZLSo/Z4by89yr/CzeNys/z/VmJGp0q8pPqPFrKj/VIJy9t+wfP+BAXF294dSrqyP54937"
    "wPgKny4rLX2WQSugz3FZ4hm8Uk5XxgmfERd5spJNsw06l2BWV6QNWOd/PMtW6M6E2d/CC5Ejovwx2vmu8CAV3PmzGLobrxw7J91J"
    "EK6wmSeOgmrpG4vGCaI7ILQpz3QmlVKvrpJjmAL5DMc2TF62yrSbpxYVwxHqhI9PohEibk36q0Bt8k+4suI+4ffy3MPuRCC9qITV"
    "sRkibdpfDUZ9IJAx58D9O55mCR4kBRG5IO/Q1IaRJFrwLSwhrCjcn4+Q2cSNMMGK0z5sEMQMnXy6FPWvjtBvTUSyolZD0dO+TIKb"
    "iCAdU1yy01AsRFUMFDEJeabTuaQCxVwPMK0YzEYm2Z20oH+xr1WS8cmajOuP/2rmrZGwknHFhojGFl5mBIGWhfu8A3F8DHstaUJ4"
    "WcCVK/PYoeXf9xMx5oNLnBUkRT3xqyt8pOFoXV/HkI4uXCCOGPA5pz0YtjY7hXt4u7uE2KRoikunwDWrBsQYDGP1ziMP+ltGS1qD"
    "rKI9AA4R0GpnTAqsJ+7ToJg23bBQp3h95gKk7YBeoeZaLMRajNH6Ta2rt+8NvvUjk7DH/M8R//O7Rb5+b0u+ilkO1/uvQ7mODF6R"
    "uTzBPGvCLrfYK8EXSxYSjiIm+XLmOgXc2JJgLwLWUE5UhicEb36Xn+dzzUzpoK8SMF74zc/xDMUdBHidlMMBb8PTfHoONfUo/ZFk"
    "myDjd/87GPRep1fPwqyEX3tX3d2r7a0Qfj6exOezZBxyCXe/65RwWgANHIj+SLNZPSaP39tj0Uw7VsVScijIqsl4r1it1zV9XETW"
    "XtkXGNHkSzx4udbye0k9CMFb0ZJQMfiMA8sFw+xlD8v9DBjSXN4g5EzltFGfvJceYx7XsPwgSrOzBHimR2WZF0if2FWM4RjERVuE"
    "C+iRgE8+oBtIZxbrt0ogaSaQVFIm2PDP+Frw9yggY+kA/Rq/nfCDLEgiP9BbfqKfcNXmB5FRmM+Sw5/1jXiBeADWhxuwzo1C6VH/"
    "lN23tC+I/6pTaCNTCfK3aIq8sJO3CTdhMolnRUIP/NaTl8SE9AFJBa2vOMX+VHpGku07tpBcI/mpQLSkUQL9SMYpwtempfGIJsCT"
    "pDRzjJA+TVSrIAlogeqALkQ9UQ3qyf4c7vDx5GUyglEpTF/HJtcix4VICm7vGhZczktOa3IvYq2NwKRFxc34jfZgwl+QoFVmNhir"
    "eCVwTS3QVXiF+/XIfm0lQRZbv1YFVB3AEVRNDXvAEo7fKLmwVtCRp9YbtR9+gku3TOTxECo+TtIzaGYUqewVBwP3Rkp+2TB+Aocw"
    "y1KLwEDyLUJVR60LVmTPijfbX9gWEc3jYfBfTS9GZ8kY6Q4snrMpyvEZTJ5B43D72Unj6YiOCFON+jwtgJypfntyPMnGdqZJXJT8"
    "6keSm/1dVEhJ/KUCAsEXBgwUXomgvSYw1M/TD9wJSHzJdAD9l39Lx+WZ+t548WOCiOOiuXn87l0yFrFtqklWM8QbZ0jgmjxzE2Fw"
    "Uff+Dltr9ICaVDDaMSXTZZlSjUQz70umKdQ9wliZviTx5OMYZo6zf8TbRO+Sd1oF/VpsQWTgcstzQ2fAdHyv96Enk4ZITkwP0Jqc"
    "9BJz2rvUk9vKgF/Ym9bzhZWBWiM3ZO8yPT+HDYYjCVwrHB/jibdWGEjYk3Y0HnNXB4QNbpDgzyn5iUUHuGjlzDpOkllziZJA9KsE"
    "gooyKf1z4lVqIdB9ZwPDoNfFQ0p5sZ5eTAIV0UQcc/RC+nBW4ebMrI+NBR1IdHscXYmTjSow8YkawVXRfZuMNo2sKlZMWrjIJ/Ui"
    "QwBNi1Jh2I5CeaaiHGT6ifyjBCHQTqsj21018hyM2pW1LkiUPb58xsGpbo3trQzU8r620+xF7MDts1yP4o6IxQrdf6IPPGSB9UgJ"
    "uiT4AosWEWewb0Cmj+BGVybP4/98ej6NxzRLKKfOiAV+jJMLH6nfEaeLpMizBYSy3GxJ6MuH7RiabbNzYfHaXfYu3qlfAeccmNMs"
    "85osPRSJOolRUhTJGEclnBumVtIP0A2apIeXsNGtUDNwJZGc8r4HeD2PKtDraT/rlBzEKO7X5H9qoeR7NeMUUQLJUoHXQBkSQzkD"
    "9O/wV3y05xgWQ9zF9oPnF0FaH0AJlvvq5tWVmUmVyvhznLMkHMMWGQXcmwB5bPxAgf1xLjusxnW+WbaE6oi6A6TDjAAFaDEBfIq8"
    "JV2p+CobB3IJoFNAcHAhN6cvFE1QYQT6/XggyPz59AO2DU9lSZ40H/B/bXRlXAWBc6AOfKtUZgGYL3Lrost/r1Jyf6Pbqxbhrapa"
    "Zuzd8oZlj/tFbX5h/eM2RB+OSYnEMpBhdmqiDMF0AB1Gqo6StFGZT+hn4GV8fIkVhZ3p6ywDNsVzeQTH47GCo6QOBv4hcYyafDWH"
    "9oeM5F1LurPwRkhmKGJdHNESrTuKFDlsOI1axZfS68D2Rbbn5fjy1HeXnXpusYKuuit1HplFGOvPLMRYZvMTY9eK1YSnI5+fJGaF"
    "4wGvgz/Hsyjtf3qPatCYlB0o1Uo7wPHsrwZxP+3A+LMyY18inMesytjPO7CKg2mUTuBPZWfAVCitRtpJSMomBcCd04Cl1kX/94mW"
    "ObMlrLFWtVZy5edJkLNTNzSdfuAha3Y6KujZuj6gdUcmzHLFONzYopCbsCIWkJPo7EQWG9YvJif/8eYJb9DQChVTzbW/WteQhjb2"
    "M7b0g/JXVf2VXJxBF+Os67rPTlDkDJMfSGlKhTTw7Oe8FJV8tGH6S5bIqOWFL6NNnN5cXBB9d1UTxCIlpa1vCDM50LATIFe5KFds"
    "LVq0mkkHDTO+0f1eRFyqdAGat94Ne5s9XN1RWlsx7fIojnw3ZAQmdql2zRr3HA7tIv7Nw/3y+/5m09lut7kUbW466L0tQrnkKIE5"
    "6Kqz3S25L2hhYhO/2gbMvTlYK+styiW+oXde+nWLm1ArHo1QnS+u5Z7pEHYVcPTlZCESds7jWVDNR3r9LdTYoFcLEG30SkFalXe0"
    "LWAh+XcrsfHoJwq+yjqOuWDZebl+vykOs+MsGr8PxuQ0i4Dlc8Qs0XCU6Tw8mcs4V7lVoC4gP5mHTe1Q5hVztZ/EyKAm54kYHe2C"
    "0EC8pWTDT7/37Whb1vQ4YtUcLpHvJtO38YRsnvgTen6qoZAL6wZUVGZP7SEfyIq+RFVeiziZWrmUojlC3N/cjx9KzdN+LM2dlMoX"
    "DRa66psJWpxloTb9UiZ8XvuzLJoAsz9BQ2ju5zC8RLsEGrOL/iQCZvv4glbduCMtbLkBp8g6jK2lGM0UG3Eq2IhZ/7TCRpz3Z4KN"
    "gGKnPMrJ78noAjjD6UiOdXARJcfxSXQeRrpqoChvTjuHL9fWpldXbvKjXw7gIjMN3wKT+d5gQU5tFuSUWBBevwtrH9MGUYVig9Ea"
    "Qy6S1WJtLQ/l4J/BXJ09zOVcncm5etfPj89oEIv+0alcbseyGI1YeXX17rTz+PCXV4+e/XJ0EuC5hY14hwe2yEsDZwYapEajcYlo"
    "Ilb4Rmyt/Td9+eFgNBjBqK2tFb2ih7+iN2trKZNCrCScKzIgyTYbJHHa1ZVpXJiFKusmWUz2BYf5oV5Co3b5B9HwZEyY9P3Uuizw"
    "u2H0wb5D2Nx/Cuc1ymQr01bDAGRi2FDMYQ/20atHL18dvfnt2asfYasRCwBjOTWnKVVa3GkQR7ln7CmGLyKW+oU0rnQm67+QwTbz"
    "5LTovJ2OP71MTsV5aqVxaNEyV/d+EkzTzT+ffpTX/mMZ/Kd/Z5NijZKBzTgo1YVexd8Tw6mUvCjyFRcGE9NfDlxCksUo7ZvCsfWE"
    "jVUV3ywCGQCHfWQWQlLMTnGWnpZaDG7rloQiXwsbLDWTXBrctJf4CrXsKgqruPemynQc4RiAMEp9olBpiZrFbVo1UTXfbpKs1G3J"
    "lMek6Jf6Xl7KezmWBTx3oQcaGkUXUWdEQp/QQGYZkobE6OBIBvAUvNqzTBWHXZ307ZmrHreGrLZc7Y+QmWusfxLO3WUi9fOVeNYl"
    "K3q10wvrFskjKORQuZ83GHloB9OsXWY8Mxd9KedWZVxdHZ/sX8AxatxKLsLoOD/xS2903RfVgbjWMMztcKBmu82wpfEgaLEwopuZ"
    "m7AXLBr46CY670xfpfNGQFTcPjyL4+Ylf7rkkh8vXPKnNzWsOjr0zGnk4LhyLVbveDX24M+Cds5uZlLQ6k7OiCaRyEdmwhGBzwyC"
    "0UNLpPQtHLGBX0gNBZTTd7CCORiOkOUzjwe08SJHOfcrUZ6SSi86zoaoy4FUprzDje4wOgcm49xI2xyKqM9AoA/eTlqevPvmmSi4"
    "eGM4pa0TqUG57JdoHFAtXfD/ysJJysud+kRVndPp6ELrOu0Z9tlJQQPo3K3OuGE8ZbSSJvFJVtUomhO8KTKLoHiOQk8YV3v0SIIB"
    "EGc+MEk+ufS+d5PLm4pULOwXH1PkydEPFN+O4iIZPsrRPgIRFPgOPs1UChQMN5QpSkfCfeJu9/Unr2f2B69nddl/nJ4nKi8+1GWE"
    "IVT54Hd9NuRQe/T7l4vzGXC4nKI+hSf+GN1bzU+PZvFIt4WeVEanllfxW5URfnM2VZrEiEZTdhpN3I6Q59FwbS0Wx+CC81IYEZiG"
    "JAEZlBWLSGYRzq1KH2OluBpmeYLr5oAbF4g9as6nw6BHuZRfKKr/C6zvI0UXYMEG7G6Ril7RZkJu+4z5QbwMJIrLDE3G0Opazl0D"
    "/jBb737flyK6gZbV9eDFvhhxyc4HDm1NmLbGx9MTQV6nSPmrPY/MZbm41y/g+y/c643uw/7mYLMHP26yl2JDLe7iU7w72H1s0UVB"
    "YNC8uXVvFyzfWNhSb5IItq5fTAAWd+t5/MfqVRbJFd3QNSZQldtyu2VRRhLDGbviq0ASNs/oyYPCIJNcubGcXTZeyhbNofeu8rh6"
    "DmnRpjiMxhMnBwpXU4zYW33jLWqji/n34SB82J8OCtgaxObG1e8xG1/jYqCU2QDItZikn+PyrHOeZkGMPeen+Hd6giW5YKZHIZFV"
    "PhS85/gSwoW8/8sFrJk2TBlKWhXZx+NpbS2H/5wRTlG64SkQeBBVFHARL1rVWpVsDILU4gMjOO1iWCCw34LY5hrxopOjLs3OD5kx"
    "FVp+XJ6gnBc1Bs6HZJXnOYu8PCaqrYUxx1H6dgJXOikwKgfPL4JSm7VYfRRWLQNlEe0/+1TECM8h4W0Obsh0elHcTJN8B5PRpCpR"
    "97hh2eIuythmwXENFfpadWD65XrlyyFJBslxoje37J1FuJ1tljj3k9JeY88uSHHBdyMo47e0PHsZj9Opd8KwmfuuJKsMb1gk4PL2"
    "FimX3L24KWJT2TqojbigbH0zvX4bnMGUiBX142mInvSQWvTRK2Io0TpiORFDtlDEkH+ZaZIYHJbsIXVlD1WJQ+/4ZD+1hWJw/qGn"
    "+wKhWPolJtrshTHLRe0020f8o8lEsgeWzZHrOYTXZS1Y9QnlMWAAhW6FFQAjlA2kBpCjY5OywiPJMd6GkUy0jZOEPttKrBlJbHGt"
    "QGcuS/IsJP+H80VTmuOge8WzdWEd6mSYWIz3vtm6ICUPpBZJ6KQaXBN7kZtG0NK6wHLN8SYeG4Yh/G14otTSvdVuz65F+Y1OT9nn"
    "cFBPR5Lw+w3xffLvixiRNCJ3G3JAqerHtZEutM1GpTCjJC9HCHc+3DeokBGXAwWswfgppYmfIreYbjoKKdGTON8X2lUF1xF5XCa8"
    "+9UZ/P7lPKp4ZorN+YnM1DKlTS6FNhkod0WbrLR7+94pZi9aVKXm9kyHJ/2uoSQubSVxaSiJF5SbeMqNfKb27qgkeP2Ts+G12+8L"
    "UJnPHBG70BscEqe1zDjxovE7DAjB6TlaQKsVQ3ZwQ/5sOEBSUPZiGle7edK556XDkKloXvtVxd33Hg3fQIbdspMjwRdY3wuCa6U9"
    "bCrTyimLtPOGvcbMdv08BJP4P/JWPIuRwLOLd7lhKWajzH7WpiTiJLNPIGFfUu7HD/uZaVmSH8fAIbBtwLT9mc+n1NRWNyziKNBk"
    "KiPchMdHv9ZeZuFIHv6//+f/Ge6XHBSt2hnaTKrkw2wC1Llf1Qb23DObHLvLNue6PHzNF6axDjpOkrGOZR1UtdsxX+NAu+4U0wgh"
    "xpSDBhxIq10rDprMJUyG0P5ikK+Lcgu4rcHuogDLKdoIwZvhneF6UFuNCFzqceyYymj1NS8lHuI6VAAzjYdLBboIjzBowf8Y7msg"
    "JxipFEYqfZi5w5TKYUI1gxyjlBFbzMpj7xi5WWT7Lkscn8wenFKaOU3ZPrTu4/1pfyowZ4ZDBGykemU4zIGbEFyKXXAqcH+9pc5D"
    "EdcS9lcnT2aTeJQE39357l00vHMH44XwpE1xZOfzuV5mwuJrc3/kXWYjOX4Te5mNTvZHQFc3UdxBs1EN8DVptexULg5MTKuv8K++"
    "omn1VcqpLjDIctr40lp9Cmgh4nKr1OSvExkhTtEbeiEc67g1KQwk4mRQdFd21PBEr2Rvtc22zmRzB2v6iLCmq1fXf0s5RjJBA6vT"
    "cl/7U9qe0P1E6hZtXyJjmKSDNM6Cm8xe0riUxOnieGALZ7m/b5TrskEiyMtzaBV/VOct6Xa2fT89DVRDjFgQVXW0uv2QcAc1o0MU"
    "/FxgALtVcf1/LTAg19be6mqjyzsXRZKLo+xOb5gB+zRUtyWSI+XGiHSojM4ZOYv3VZump6cFRoTB1PXh7Pfhgu/L6aw/3FycD8ek"
    "eQ7a1CZAZfvDt5Pp6P3QnRhHYYw2Y/5pCBf4x+prddLPjakd+BfXRl2reTSxd73FWTb8hUeSs6ruGTRo+GF6kY1hUzyepAmir47K"
    "IOx8RF9k4L5gKxXJs6wMakvgcT1P2X356qq7E3U3SWK0Tsas+UMBWLWBuvMs9G08vuuepuXQ0mf4qqsKlpv7sJHs5993d9bWUvpr"
    "lEtYMxjLqiDEZdsqydc+hjYZWkopQ7wqJoKGYT3hxTjtmzsdGatEDBg1rp84w9ePw7kS01WbGUbTilRX7uoPaV7CbeGItgPhVePb"
    "saXXbqf+GJmZmbP7wfOJ9QY/3J8GqFUNUBdjngIVfBpgkxMBG1E3z9E4mQDLkCwkP2pDE7WKKuUZ7pJILRgmuA3R9FHLQFMdTDke"
    "GgRzeNIfShZikd98s1f7XIRRN6beewn47aJ2V4Ysr/MrAZB/rXrBUvKdk5XvV8oc/5wNQz/nKr2T2Ey6efeF88VIAWwYbb/ZZyow"
    "HML1QXvsIhfSp2hq1JU7J3cFeoMUQvH1eZrPoQOeHuJHaC0Upxl6Wq+Iz2t2DrK2Q6Mcrl1kLkTmOydDrIyKrqkRsuzn1aHMtfXs"
    "lDShSQ9uC/RzvTsoeznswyENYg8aWsxnv6+spufEjGbl/sp5/PtG3dsh3BmAoV3x/O/uZUztbbkGehlQUIqBFty9nK53YTobi0Uy"
    "4ikWk41ix8sWizyvp1hMbi525dJbLpc9mntfVlM1E5QW00mspauFsWj7Tg5kzmR0QFrctBXhoOlVPu2kGSzIH1/9/LyfziM/6ahq"
    "+DSMRBPokPKObshjoZonDq+MMgSbSSI9niwPfaSphbKwYEjxfwQa+6KqpQHgAlSkpl4Y2UwgzGo/gqRyDehGbuegtCBs0b+L2bBV"
    "y0PCgF88pwtHam2tH6hG8THmtEu+bTPspqZ0QQ9upGJzRLhuF86DIk05Vphhk2KKsTzECejGJ6ne0jNPGBN1pVcmsJ0MmL1fkNID"
    "w/fslxevXw3RpcHz8tWTv7969PLJI4azkFmiNgAfA8cOuEO4WdisPipY6l9uVkYNQbTqrs6LRs3eDIOyYrbUU7ywixrWf21xFmJg"
    "nwEXMEI5x+uZZvMruGL9H9t9a8GM9TNPokV5yTCDLv48MtqqGf3g0TIqj7PiNCE3ffKCHIrL8Vs0bvGM6+EHr4dl/bBKNXl9Uwze"
    "vmbF+jpINkWrngXNLDhJ8yqTJ1goU64AzBQ85roVvsrQFEhDG+CteyOlf6JCPK/n5lXnu639xtk0rvkx/oXS8G9Quz42uqHnJm8X"
    "i3TCX7BqnCWBYLHB98UgaNNWEjVM7W5ukEHaKEkntZviu62lGn4jtSC43otpkRKl6SqzlDb9+1I9+rw+wOxHbfrgCHJattAV/8x9"
    "+/45BQRc7DlxnY0cVDfqct01rrnte0sfeWichWG2FH5WVtMNX6+lTEfeV715gDbJ9xXyqUGYomk/xSBU++x0HMQbKZzFXTXkxkLC"
    "gCFXV5xhoyZHNyTY+FVYc+oyVoO3YXumW5G3SocqGy8HDR+iTrf+y16NM7znK6k/kYIbqf/wwFno+ztZMNhTgZf1yZJFEKTMhSVr"
    "IO/cG5ExXLSVMeyzl9wFtbfGKA0GbjRHZ7mLRcZrlG9mG4OdKvv4CcZxG59ERiIkCXM3uCwYWI507SsCYGgmD0c1K3BtbbK+Hk2+"
    "H9WtYciwsRH9a2LKJYtoFEnunXUsLytkKLCV1DYkdEVRnRF2K9vKjAiylX9PlLr6i9OnegJi8ccNfKCBjGbzjka6MbpkmiGsiA1y"
    "UzFJsdn+H4c6hopW3ya20mlf3xVW+SPWqbuqqXBfWdyW3BJu8g+fqmbsjnWMAbe+n2kwjExqO3MGW/djHTpkqAm/EN+rOC7KxIms"
    "Wsgrwn9vgytRoq5Efj9JvWLz6UeGd+W7VI0eb4liBknDHarX8LIr/SeXvFax77/0L5TIxkpX5+Ai42Vm4ZXEaMkSFxEbhMBoi82V"
    "aKyBvgKEcO6dUcqXBWSq0SKGWOh/4AG8/ldM/24LLgR5nWV9/HA6CHK/glIJcCmU8myK4fveTstyeo4h6+JJ4VdV/kPZZs1GWTBs"
    "LEeJlWzsaRh4uAIU12hWrQL1t0lQtG8Vel+0r73EENGNVS8eECwjpIqv2fPGCfnv0PWalbDejfIbXghLLM8wKj2eoXrL199B7E2K"
    "to41WzAjvMwbnvBsuS7ecO3lMvt/2cX2mTXzajOm0LIlSLT3uT4dujWng8WuzNw3rY4v52anBT5WgWbAL4mJZzfme99nA19iz9vi"
    "PrnX+l5tdKOs7/cN2P+XWmhOc9Yt085yvR6f2oh54rPKVMyurxaD/y1FQKxM8sH2Dg0kUpA565jo8wFVfhxNl24ZbAXu2xQ9dPo+"
    "JKQBghzQLjzS/vdSWeultmHwfixhvHSglwGj11XSQwy0kQ3QtRn5o3GCgVdW8FG6cVaLkjNnl3N8guXwtS0Ne3G/AXF3tZS29CnC"
    "NngdhszSh1EcRkLxZkyysMqAm2ivigzB0WnIpUMPP2HPt+SnaNgJLTOrYJ6GEgOqEiDHNzr8hhyNBIGRiU9EJowRFaT9dAFCYO53"
    "YKlU5fNNsqP2NDrVBMLYOf/c2uQE1deFvi3uYHjJFxclfB65XsHXVgdaTKp2RjBnbt+0va/GN5JxZ0v0WBF3HiSu2m6j1oEH38P+"
    "WxWG/0CgMT6zYzIpMD/0FyKPgP+YIITasCcjv0Frph87lCjyMRpGARQT70FORpEss0pUDA4Mx0HhKhWvD1fSYiWblivxCoeLI7K3"
    "ApdMtBVYobwrBWeOVoqLGZoaJCJbsQIXtZU71MI7KzCWK3dEI+5g7Ld5pIxb/Frsjh4llFqgh4ecccuynyMh2Ob9jM7Rr0YgMMCX"
    "8VuOrOa+WbWiP6MHiQI/92Cbd1wE9QqSuQN+SkUuRiUXH5/FhYDgFJ01wpooOM6maCI4zFYokVLlrwqpAylGtDpkJIXVg4K+MhOq"
    "B0P1K7lP7U85tYZ+uvB7PDXyyXFhiIxX5HLj802SAUEZq7EMlY8Ri1D+enT4S4fDD6anHLZO4kC/QXvKIxjZMa1gNuFLymdlch5Y"
    "W16FuXC+kKpL6YWpgp8NKQgxGXupeDHtNghJRKstQFzc7/7v8eW9+Qb83RJ/X9HfnvG3A3+35//8Lsr7fhmo2Cw6JCP6EVAYwzIc"
    "IE76ARqqlXDiAk3kmLA8hGQuCswynLfkMnWJuFqr6dVVgf60KAqTkYETYUrg6YUJZgikoEoHuHmpIAf9YUYRgIcamJtfpGbklBbh"
    "TWIPfQkjVRvRGU9llM6vW0ZIias0y6jHiB+hh78aXMLIuHSUhriZzpktYerg6bZ+aWRcOv5D3EhTbV/I1AlDVwfE7uS7bsAGaNu1"
    "SDcudUWv+3rJI7SsSBbe2eaCrQthlTqk313H9M5YySJvbB8fxpuaA0TvKjO6WnUJVuK09e0voGarAP9HxiLTEd6qlTnR3/pm7ig2"
    "P/VlDxtOP3dlmeeenhbzgLTyqF7WH560DKyT0VkL5jtnQTRdgpxCoSXWgey+djtaPWsXVqoYfN9BHXsOdW9GGg/tnO0MhotrhC5U"
    "1gd0iNd9hC8re8pmCpzcSHhaMA0LPDVNyEqjwL71onr4iwMfL7SCOTa5Ns/N9MuoV8vWJtyJs6c7/5qmWTCMhg3eHOLaR/ySsVF/"
    "r5qksy0IB26oaE89GJN19uIl2otn34S9eOKZN42zps3Ck0az8MQ1Cy9Ns/C7l9m1TcFz22ZbFnUd8++aoq5j8p17TL7vXqbaoJt/"
    "3aQ5d9lszl0q7t6/w7Voo3pEmvx/5a2MWAxbcH/xFvSdjorsGx5MpmuS75uo5gvlvuQ9hqMcg7VLrHOfhUTCug90dUF4iGdZWtbG"
    "6LQjRkvEV/npYxE2usXnMsJ0pQiKE92mAMpoYM56227I1o2IklpCaESZJNmgJMpVsNtq4GsvzlRlbETLjvwaJV9DoBUy8oyDscIC"
    "Uai1e/228d3XaptnzL9W6+xZNSKnVEDPbHQtEheTzQSZyjGcE0ruRa1R3DfE71acazRrixHtGjEyw9UpGaVhQp8d58V3IfvPF7BM"
    "gIJNubKC10umgcW1W5HM0SxPRqwu6Sw/kN/0C60GyE/m1Tb343nkiy1T8WmQ0Vk1Y2aWcolxPT2hMTx4PxUljhE6XUoD/z/23m27"
    "jSNZEH2fryDVMqeqVYRxIwgWDaMpSrJki5JalGy3uLhZIFAkQQIFGCiQokGsdZ7m/axz1jqfMu9z/mR/yYlb3qoKICW7956Z0263"
    "icprZGRmZERkZIQJnc5ydZAJnW7HisuETrdDpxXERc/IfYETlVyLV0DGQBT8wQqPs0xRfKbExQfFpLGrBDosDS5Q7qVgbWYky9gU"
    "3huPB7d//AX/F8mjWY8tmcgmyyOk4PKw5OGC7Tdf7BofWPlAUkUMMCv9VDCpSYv9ncKfChBg3Hd9HUanPVe/QpMYOJGfnChTSyIf"
    "8RbGa66FbOc+vY1UXpHy9nvFmsCAhAHXRjM7wCTP4S81M727i4utSc3LTUcKTtVutfnvHKi7GeZJPd9yGCz9pogbVLx8RIWUZOHw"
    "Vbg9WmQi9W13Cots2ss3G6AxYRfOF09Yp8fjSX8YX89inwVEgCUmU+bkrH+eSZuOJaEt/s7Q9g9a8wPvsfWO4u5Ow45csl/qjMdx"
    "0tsnNjQHEb0myz9/zW1Auw6+ucqPnzWmnn5AZfv7LTqXxKzPuVxXLs8cparjAxJ3qb6zV3S1lTyxySrIIHbn+7D+4qjPpK2d80VM"
    "2eRCVLxAo8ZwNumSWytWi5Eit5XgB2rPW/gIRRZxH7VVQHt35dm99uk8ca/xcj225txLmMpRkQTYdjgJuMEQjrDOwphfghj8syva"
    "vY/PltFvZoIzoiBRf3L0PKGpLvJaR8wwnBPIfs7QmZ9EFF+y4a1A6hjlE5PY67D2ZbDs/YGjjtKKBGBTbq+8IoXVRDtSS8SRGjpN"
    "yzpSw6h6HDiqYx47WUarQFLRETT6PSLa07EDnyau97SEvKdJdDxtbZ2iaXW8gmlJ9f1s7H9XXmD4THUAIFpNePllc5cJQq/xCtPH"
    "kcVN7pJnt67rNtNWO2OBnloxBi0yC1QKaRlbsIo7KWSE2LfPf2z34k8Iuzda7IdyLXybZl9Qas/Xytc7p8sZOetyZDquvggc0pQb"
    "rHJcQuuN4hYpyxHDTax7itBn9uLbMTY19ddFLRhTBRRDjcNHxZO6N6/2jSu6ODPBg40PiKIA4KmJgsy+Q730nnDWVg0dlzj1yXQO"
    "7VXSzuB93IX9PX1N4BbpDWhQ9hTZ1XYtOuKeAsbNs6AiLAN7Mhynt0vIUFH19RjZBx0gD1rQJ8qH0XjZGnKu8pwEZZmP94RiyKeO"
    "sGyRFhe5QCZYZz6lOn+sXzTje0invByWUxgtZxSHPy4OFKs3DxxMgwHFEM65fHUIwVK/v3mnspC5a+ki/ikOfHfNGZf6WYe02UuX"
    "jLdW3JXxdTy5LSZfxvX0dDSMi5jdWJmTJSAqL/B/gTL5KYgEnDHbKdrOTnzycFl05/bqaNHiOZ2JPBOZp+TBGylxEZ2VILMS4HU+"
    "RZz0YVtGU9RF9zqTWxCXgAUO0ZMcau1hcayXFws7BqPVA0eq7SeDfhKT5EFC+x9vt8RN+sF4NB7h+wRsu9PrvZ8B22O13k/ORqZh"
    "cn4WTYfomBlVo8jPZmv0UJSdLKvTIeF17ibKmEazFGHq5WotHYQAT4tlwqqoB80OobSfPhyNdMvzBcVZC/UF06TsbtwRwLCW3FYU"
    "jO3vXW/VQXp3x+cuX2VgIyyBvCto6tXAO7uSf+emQphpIHh0Nog/b5qER9kSiohQgvgPQKYFqkUyqzjT5pcfRINRB6+yRKsgX5BO"
    "x5uk0m9f8eHA3qIkP3/24Z2i+eHp8+DZB/LAJM/CPr1VCejzKvzhmfpkd43hCPMzAkR4dRPoUE/hhw+BxD8Kn30IDsd0TxAOzxeL"
    "XYXCtWfo1Hj+6G+nndN48O0Fubqarm2KTc4jRWGfXbXkBv3wdng6GrQcQzYnq9RPVUTgaEopUbuIq+Y68WKZd/Hl3cUZ7o7LQPq6"
    "+m3UW20FQ6g7DGjMC42Ct1e2lyub04xJ9JEUYNstPRn3M1WPmVaVwWZSCmY9yUkZ5sgpbOFZDCuxP4ZhEoilOJkNWfgCMSRISOQp"
    "EYki+dR4BNeDu6L5NQ8HK7vpd53JOWkTtMvSVD3iS1o6D0O9s25ivgjt1N30m2obcMYAw4EYrJcL1F4wsr0rjiuEYQ0WfnjPCKdt"
    "KdCLQaqIpQBp1YL7qgIU0L4FUzFARR1w7KP7sJ+Q7Zwl+GkEq0GqiQQm+5I8FfeR3V3e41wM/QMzp0hjWU800983QI3lN6AwxlmB"
    "Kqb7yyujgDlAUJRNi2+2LkBj7cU0TJ9EkWnh4Eq/96SNsa5tHoACx+bxKa0P4gDtnfldNEPJImnFR7L10tG7SX/Yxwjvx7525W/c"
    "opOCGXvc5R4nVo/64ecumw9/gK7YhDj629+shteGs2m6JoU7a2OdzvGytS9aj6i3YKTN7n7DN2Ra5iMNQJjeXLWO+LUOU/2pXNJP"
    "I/UENDoO3ulC8GWo54srFVUr6Acd9Tri0ouE2EYY0wo+LUIPSV1Osoh9hC/hTSIS/AjfuZsk5aM36HFihvCb6X7l+cFrL+r1r6Pg"
    "I7JfnekUn6B+xjunEfoZfFQ02EdQZgxfXlSy3xvdTFDXONG1xo/CDmm+3i3wzUk67Ktm/eDonReXHk8Ho3QKmGMzcKj41PswCuZo"
    "nYBd8IMmZIIGndvNYWd6hdLNXFmNX3m5wx3jAvGZ2vYygwMiHcKWsYaoGiTY1CeApgDTTdmw6gMc+CxerepP2Q+lzxcB9VZZ5NvC"
    "wKsM2nvvwCvK9QMH1A8eAyslXlHgVgCanls1g6OIikXHQNP02F/pTmD8fT36ijR5VNBiEI37m1NYiBjL1Mo51uhxAeD+Kw1fBv3e"
    "G6luqgG2E0aRg2yn+j2N2qM6Dhp1/C919dKDVuEEwTvGk7C2IATgaoGSgUYmyzMPWADKWboGRyVk1qdKzkARdEq2TkFN61Rmny/8"
    "+kotzWrevnkcYOlCwk4pr1FB3UH8up9cHaK4wN6F1Sew2cPxgO6NLRgkjTp+F0/QGbYwyFAsnxjIWz1Meh+jIc4H0+rSvMy6HHcN"
    "tQrmY9FGhKSrQL4DmH18YJIelY/v7loF7FunxEWQxAadwU3ndnp4MboBEMyH7iKYycNHyFY/FbXBV46P8BgcYzwjmk8bOJSi+t78"
    "JKza21IjT9tStZn8RDohCs4Sm9ZoNsxZI/mGAB1yCyy23qTgT+kOQS6D2TB7TAii+aXf+yA6pZJAv/VKmEoq/XZXUOqsIF5tiNZ9"
    "OEFPO90rBYWdRhBlCmWTAnwrmCmTTQrQ8XGmTDYJR8w3wVahXFrAwZ8ybeUTF0QCcJtF5WgRCgXOz+oU/SSoGaWP7GyunkyuYjqr"
    "rOosTnqqK3Ik/CUdYQXTTXVVNzSNuAoGsAroPJFOcxlfuHIL6s/VZodJwF++hfjaKiBxiRTBmE3/QhDz1VdBWF8FIS7QIgiz6V8I"
    "Yb76Kgi3VkGIW7EIwmz6F0KYr74KwsYqCC9nQ5B4sDF8ldwb3SQ2nMW5XwjtskZWwby9CmYkucClLgN6SfYXQr20lVVgNzXYwM1U"
    "yrUqMDf8QicSG5fIpvER9adZAsyVIxp+5k97SFx6pmMeMVxBZA5d+FBHLHaVEo+peZ/fi8WGlC971REIIg3dNcOBOy3KnQ87n1lz"
    "BizQMtvl2FGxAWO5OF4mYeS7AFbuqddDMCfxWRhl+oiwXrFOMZj3AZ/ImrmBi9SNeEf7u+IhxsWKQGWtMedYFJlii8AZ2rI2okq5"
    "/E2k1nRPqUmXoixAvtrSp8KciZYdvZbP0hGxlPB7CvPMNgHhesVinLJoQoubOXI2aBxyVXDDcfS7oD7SqJZPaCHWH44AIpFrArHB"
    "38e8Y7NgKJFMFYKkNDWGCyCSXF15V2y0xKXkNsFeAuTkA5cdjJDl5qli0LtawrIuszul3P26nmod2giZGMqiOInEU+vPwHrDDVnW"
    "V8FVT6eUSwvy1hLYQy4xyL6PolJuUu6GrlPKpMh9aoeVzYG6Y8IVKD8t88T+EtvE/grDxP5Sq8S+sb1Tafh+FPt2k5+xCzadLt9B"
    "7qpET17uDkvKvkrGs5SLqsZMUk4yU54oKaY6SC6VFZKL7bOSY7DHli9L8j+GxB9aqT6wFe2zTFpyjCixsJ2QsZs02fSt4UDnH8TK"
    "Ahy1B8Kh3Yw5I8JUulJLj+pf0BB6Ccu1MyA/QunR1hc0pDyb2C2NxtBI48GNoMvKXNQjhZ3te5uxQkKpdiTqrcxRetRc2khxuFxq"
    "p0iyFYJsa3sMeYqUseSUz3tNieDToj7W16F5d5v3N06tZOgI8QMO3Yj0VVWkCIX8VA1bT2qjzFPWSJvgRvbG15+ywfW3tZF1mtm3"
    "FlvkbgorgbbBakYmdswN5IgYaB0OnmRONJlIvO449QL+jf5z1ssF50aWxIgnnDBWPnECbUMQWvYEgfPkj+mt81LQiclr1yQKDovi"
    "JW1WOqnoZ0CH+GeYkGQW0t2Y+rJzDi1gipK/8hwscJESxkWOU0hZIFyl+olph8JpqZ+BMuAPY23LH+TDldIosomBdfUb2/e+1vtQ"
    "1EuGcSmTEigfNVaRbJLdytRtYhrkXqC6BQQH1ouQMLYfmQRuGFdaFm6SVg9iTRFOMrfvIT30zxgVBP3pz0uu5GFZ04sYms8PRMZC"
    "i54xw0Ql1LG5s4KUqmKefmnz7HTQVedteXVNKJqp/B7ZZV29sro6Fc408GE0617ESS+UMvT9POlxLqCUDnHJhE88ny0Xo3auPr+N"
    "tzV1uFSq9wwsc+RKkpy3ldr9ta1zVlLUIVup31/bPlwlCXEClbfur8zOxWwnb1CvcV89fRgT0mlVQbXt+w9QVa3T64/0wVt5wMmL"
    "By/VWnZ6V3Ye1ohzemceCAK7t2oR22W9JY8EoYnKA5pQ5b3Ch4LQSPUhjVBpL/9YEOrfs+oyw7Df80Hl+v2VD50158K+dX91C3Tr"
    "7ZZNE0n4KHoth63kUh/Eh0V8dWw8kcOZrk5y2xrQPqvds1kfyPb5WnjWOoerfZwWHZz6tNRHpD4XC45A69TLnnG5A805wQrcklnn"
    "U8k9jEr6MMpagJWyJ0rJIcYlm/iWXGpbsia3aBr13MG0RepBcolcvWrO7ymyecTgnbqsXcd5r+HRFEx9ffElLsIJz34Bs+eK1v9i"
    "/f7F+v2vwPplVH77rOzjCskKxnC5EvIL+cVq42sZxur2H2IYq81/FsO4vE3hISmQx+LLOcnqzh/hJGvlP8JJ1ip/gJOsVb+Ok6zV"
    "voqTrNW/kpOsbf0JnGSt8WdwkrXtP8xJ1pp/AidZ2/ljnGS9/Ac4yXrlD3GS9er/5Jwk8WyKnyTG4V9c5ddylStOstLSc+w/gxcN"
    "OiX3Ta7nXHT52oSNvBRFxsDOvnHNjJZb0xev6tox6nYGXe/x3OmgxJmLtU10bURcrlh5/zVBy/whXhMuxp99fKVSfDOourMNAi0G"
    "exbM3Uu23CvSAv754Vpv0uWSVR5bBFYWbD1IN7dOSX64D3+t+1W02ZXZt9sK3l05pn38ci9j3Vf9/7d1n7yAdAz86rV/uoUfd/sv"
    "I79/Gfn9y8jvX0Z+/zLy+5eR37+M/P6ZRn4ascy2FT6pqDncqHjsME8qVELmSYVKzj6psMwKSTPLkclf0lNT90GJ7VRSB3A0fK/E"
    "bww5fqPhX5dUM/xrUGR0pUcO3HOih14PBMZs4EkXUpim9/kiGlLDVXVOp9AdztQy6Jc0BcjNvymCsgJZX5WdjXGB3t1F+t0vasSz"
    "c/BwBGwVI4Aavg8F3PufhAQZygPRoHaqQgShMPfGCEWBN1f+4vlVaUIXAa0XV/Sw8dVVS3Y4YAMdvI6n0SJ4ja/+0n4KYsZx8B6K"
    "2JsjGs36VDISXhaE1fgRDLbbhb0KtX83bWLRdDJDnxcw6uCp3e7PS4u91I8OUwpYqqt8tOv/InBt5+BaBD9ctfaAdT5hEnk4Ho0G"
    "+zQ29IQznobzKSZhOKZTkNLDOT7tDJ9CUtxJ0FU0UEpUwc0HcYoOvoKk9Yvn+a3v0SMmlEJfdpww2Ac5l/Uek3gIbDRIyyc3JJIF"
    "v5YGoxsfoxdx2d8PvV8pFmsQ9ZOTGQZBa7/al9roHInfaeoG+z2YwiiikM3UwHtVmFcDVrHLBqN8R71JH6ih3/7pUBX1yVMGvs/M"
    "FQaGCsv+aJU9OsZnm1zySHV21h908FV0u3QNi2k0aZcQz4HKBuBOksndXb44Fru7+wl3HmCxxLEOkFrP+73QDAWOGPVgXObEF0/Y"
    "a7gxBgLPelrC2dvY+LXUBa5XP51fNiF2dIVlZb7jSZNHpfRct/W9Sy9eXQVH4ptLCdJvvetD/daRfI+HUoI8qc/SqB3F+Jw3CqOb"
    "ziSJnJefhNufvWfQzE++l6vIuMLfofwGCBEPFf9YFAWoV6Bu3SNvkIXyR1/Zgi33d4GW1JZPj8CiDiSNPOpM+p3NAbpNeBQSxAKV"
    "iQL3W9jlntFbBu7WB5QTUhJP00eo4MGeRtpqlbStp1Mvbn3/+tDj3RpJK7/N4smt1RBiYjQGRKDvELzVEgQ/hfH/w5e0t97o1udx"
    "VuqWcoZ4nmMHr2a4hhDZSFYrCfYz60s2Nt56vx/60N2vvmwsnRf5GxvrqkZnAtTqOu5lziNHL3YPsVVvmkeDfu8RTh1/YwX4hG43"
    "lUfR3DRA5gvMQ34EeRxZfplcXGc7cB64T0WtZaXBfg/b4nf18ftVpr1R8o75tjnRrrCj5ouXsdV6v7B14VFySMmPi54L9F5hnZsL"
    "oC5hX3W1sAD8OQtgP/lIgdoydQg8WAdPHQyM9B4lRxEqPSyAeWv1RL71foOlIitCteu3mUoomcDZG0zR9cALq9sDo/Jv0Zx13gNG"
    "WZPZ3uT2BBPQQUW2uFkTZqTlfKsfRtBAVFB/73wE3SXhyKBxB051+DNVZwS7QS5AWOMhk0wnVTBPO+fTUDUpsRLWIvIylN3vj6/V"
    "fq/m93sghvE/e9H7F6+eRcEmz/rHq6KdvmTf/pJdUqoc02qLG0N/OH7wqfVL6tHBh9DgSxbyp3SBt6aUNESLgIgMOfBPL047/QH7"
    "ufJ3f9kH6YJSogDI4jze2PhED0TQexoeohsb3qcSl2hR2EftvOEncp0hHjoA1f3zxPtER3CswFhYbmJ+u/KKS1twVzLA2vV/pO6o"
    "0+DtviBnGlkl/kElBPx1AB9gz3XIiIlXYiWIlRfCX43nU+5w2EEPOub0oMQThUEcOwZI1CD9Sg4uWsB95YdOEMQEQIp9krfB0XVc"
    "0H5HIpjw35AiDrJwa2PoE3c2X1hIkBgr9zQYI+RSJ2C/3eGvEl4zKJVKCN8l4Bzd5pKnB+C9OurqjZP8gJvelKZ1BLfMgK25Zf8h"
    "f0dmnE5HdddFxup0ZgN7/tiSLK43z8mzAYg9ew7TP0Rb+kWQ7jllTzv4mC3JF13DH8DDoU+zPVtwoRFAaj+fugmUYhF09izJYbRX"
    "KHlQ6+g/GLACMsBewfAcZsCMtWt1iwEPZiQHDfZajqMGdxiWvDOzqnc3p7NTik6/CHo20GfSWsXiyJIOinxQcrznSEzHwTCbcGG3"
    "db63TPQ6sYtdFw4AnemuQeejMyh/m4VKF4HM072cFPaB386JFEaXCnPxH0i/puqV1xxl5GEfWAVibQHN8vYD4BLxLJhjAdyDJKcl"
    "IKdNWmmRuBV/hsUtHD7dVbaAZMalK5Ci2U8Ott+O6Z5wCtwmWlIhtCBRQcEOuTcXIebuDqHEZDSVWC3RUEUUZ0CEKupwtO9Jn344"
    "H8cTZOnCXw69WEuZSjrRTrxKiodeJtq0lxVhcq18+4cfTTftNvtOHDCQAohibvA/oU79tlIuB7PC0URRONj3lnUv0nDQw7pnWE6X"
    "CHTrUOiGjN+E/wrSc2FpgjOsJ9noP1RqkFc03ZKOTWVCDEtSG6aIASnBugXOAfWS4UtEgiqZ73SB4ncwtnrWnkmXdStgqV6jx3Od"
    "tvgmwuaG2JwoFnAJBUkL1wks3aPUkac3NqwVzBkgnKsyJd5U0bF2MZudjyOg/5Ogc+7xvikxWQpkxanAnAFJLr02lqOKihPmdMTA"
    "UmH8f/x3YLZC7oeinI4mJxfxZwdwTJ1NTrr4uAr42r9ET6ySgMLxoNONvW//7S/fBnDYltLRR/S7tN+Zxh5hX8XIhOZgwKkbI9FW"
    "dEg2dvJ4boov1oZDwrtVlo9S0nVEf0FrAdijVAadZ68e7SK4sObPwjkdQCDcxSWKktR+bSt2RkwIWPWivUqjJ1aalO8rbU1B0hFU"
    "uCDxOAklP7jBlSoXpkuWKRDRzK4kiNo/6H0eyPBfXpSAWzjh+CPIO/5kRCdYH3P4LzFDiJAToaViUEFer4t6Ubu+j4nKrAdf2sQY"
    "yyHBncGrjpzKUguZor6QIT+4xnF480dwxFz0e704QRdd/Ct4xErKQQ/TsrgX1FMhxXsXl3P5c6DPt4S7dnZYcxGv8etRaAa5CGOd"
    "h3uGeolvF3BqGTb7FJna3K6ceOo4oyp+iIyxbtj4bwsSpXhCxc3zK185zmP7CJEJoQUQCeG/GaXNI21KtYnMG5QRb7uWgfaJrKNH"
    "FMIdT+9H4bXFXMgzd8rmCOPclJhYTdsRcCriTkpLqlwQIdw8RdD4yEYLhzkZpo9uQm8uRlx4cre+v/V4REfibv5YGb2x8idh5Q9M"
    "z6kK1sR2ERn9GYp7+x8ASwyRSIuD/pTIDSOYPK4hGFiJQ/7ECMKRuqmZ7LHc+PizH3yEv719n/YuNHs2EZZ74HUpZcq2Lrzba9Ww"
    "DkKT5fRLlUc7HbzsOjb3Qf09UkSM9eUas3LDWEm6FKjLUlaM9kCynFKvFSTYmSWlxNBTshuLlB6SxQaVmBGqFSe9BvwqYkzp9RSv"
    "i9OMO7dQ3UfHBFt9Eplyj5SATiYag691eKdTL219n138trLODLe7F0T/7/8TPXnmZc+qCtphWWI9w9iG/XGNWohnq2R8lOene86l"
    "SBPEAj8YAqR3d+eeZaMGUzPYsyCa4QQM1QQ4RS3NhWaTgYlPRqmeznOaTm6gzecIqvVhfOfU5A4w+q56wL6/ypAkt98zgJIOlyGw"
    "7zBRgwLlo8qKVgO9TD/1/JD3gO6C9UJOCgxhvOday/1wFcgli1A3a0Z4KMfOSI99V+0qhAWS7h3Qe7X1eTwOAVBhEUwdi8Ld9Hsx"
    "SjLdTciOltAGZ6T/TAwO3UVQgAoLwTmkKM1CIVIqLlKGaElrKmQwMmGUQP4ylNyzKDM+H3G+qbVg/khLh4+QNVBcBwOyOFa3Bdmc"
    "uzs+XsgOzs0yg/2HXgCi8ftFU4Nanhq41/QM9znu8nzf0b//H/93xHrgCqyuL5ml+w4lurIpXpGc90UT8J42nVxC2VtP3QogExOp"
    "hnO78Z5h3TeYQXyWmrHo44WWEmbdc/RaRyEVd5XeIrrL+jjqyRl8xn9X3Bba5wqNmD5Zx8MJzzxpjWi7tJhZ0de4MqC5J2emqDXN"
    "48JKt3CMEbEHQj8uqldE21D1Ze3gX079/NmSTugIzXEkSG9gVmbAtMwogU7tEDOzQr1z1ZNcJSAQvKb5c7Ts425KqcEcfjntLGyv"
    "rRarI/f1rCE7zhy2J3vFK4sS2chVOEsxbaIvKcbmTLJ0UrV0NMtTyOygLnEZc8M9AdNJP46Z2VHcSkysivCuUiR3p1DcRgEzUnDB"
    "aIjO46uiJZlvm1BKSzRRdxVWK/Ee3T10zv2ctJ9tiDLU7bFuILXZnQQ+8D66VwAHyaBT338S0cI+W1EEgR0vz2+7HoaRuv/sWTtm"
    "ZcPsStfeSk/VdrH2xdImilYvcSCQ9PcrbC5jqmsM3EhoQq7exCePXBFJG5/hLc/nPbrmue5P++TNvCI0LDLX7ZN4Ohpcc+A2CUhB"
    "jliwcB9dxPAXat6Dw73WPObrDgKRNXf7e613k9GwPyX3WdgYYPZmr4WSEYiknelt0l3TgumHPe34/POeqrCx8XwPP63+/WD9cK8E"
    "q460HbEJJIgIu1bR8nYFpJjgARm6OxhNgWp7Eh/8DGpNUVA9BsKG2pC9NJ30YafGXuQWiJQmUnmb79x0+una/l6QxDdrMkAvgSG5"
    "NxSf94L5bTxVMmgy0s7lKMKJRmOouIg4MPNRNuh3cJ/aqMcws/DRlqvpNl1wWRc4gDptLGRQumt+EtWFtVCSflsAE0yaPS7UKsGU"
    "xajd/tAfxqNZCtPUKJcpQmS7hEJEZiKf7XGAqhv4GzCy3ibuT9Pl3Z0BR9zN7wLEZurSRetwb7dwge2Kfp30ONP9UZKQzqYNaGrr"
    "VUGGGCrSe272W48ez/cPD0vxtNsZY/StxSNYEKwQ85I2csLdi3iqSHqwRhgP1nibBWudYO0o7ZyyigBWShJCpUyXD6sKq5CgApTa"
    "wTBgCjmkk8xj8Wrf2ChOX2+ZCsjmtIuL8XgFxymj/Q/umHhBt3FXe6gjoa29DnR3z3yyVu0yeyF0YF069fiS7I2TJDd27wqu4SB3"
    "OjuFzBdOjc5Qbr5eYWf9zIXZcfDabYojoC6C91j6bASsQPC7VDwOnuIvprXHwc+5u6+eXFeiteLLglySvxfBR7dHBmQR/OKAPZt2"
    "zrHwD8WFf1p6C6YcQiJLPUNIflt1G/ajZFYzPDJk/SODY6nxawFAiPsLyPtkDyEDiFLawLoD3nk8GvQJGX9fdh8JeY8LIee8+LLw"
    "zvbSuilMLpc3PbnM3QI+k2v3jDHmlxheZo0L8V7OmFoqywdjO7niNpAu+fAqSFk2WddOykpSrPIebsFozCZ/MeaUxnbxo504+wJj"
    "0p4yflz/lUydKEoIXo9xcqHdg893WOoO0bos9JS1VQlPUjzY/CejcxkWRW0OSfwNhtL+3MRBWQbqum5ejhlRXHddoym6V5S0YIbP"
    "qqNvogDICjI6eOAcwTwct0ZLUeKr56cg5uHFL0M1UL3oMRbe/I28gX17ou5krGs+c8EoQKo7PXc4GdAfz+PF2uN5iv+ZLKISEO4h"
    "HDOhUt5z8ZQKH02C/LVipjNoUJk20vXhPbdTsAUu1Ewx0yYTjDFndFAbFYIHz3gGn6H/CZ8UDIejREXNgBYpBm5p0knVxN3fBm+9"
    "UjJ6T+oN5h7SlsnppO/ZFvA8POikFyWKrya9oKWSvtG8ieOracvFe67HdBFKye8qqlD03Vol4lJ4sSn9UqEIxRKpJ6WtFc9lAt1g"
    "eWPDAZGS/1op+99Uyu1KCML/kk6kqOoKJubcnRgOztgky4KBBw2lrV8BZzffVuLaLsatIp5rDZa03qPjCYY+b7ePjplATlrbmwTd"
    "2WAEFbx0MymlwDr63zbK9SZwjruT71swgsl3zY0NLz6aHD9pJSAJdYZTE9GJIqkDdbCHSVHJ1d3fTzapunYHofYmQNYFvnhif+5m"
    "Ap7ZF7fLNuvGhiR9X27H38rvvwJGlIHXrdu/c8s6MbbwVqT6WN+xxqqRU2XQPmcNyU95laisNW3RLirKwNSQ6RYDe6lwUkDjTiwT"
    "SlMvFdtJa+WgNSZZTp4o0pTvjjCru7su6A4oxti7Vi2sfbt2hdZMuYbwcl+3k6HomJc3LDkypNgqoA12MaS4ciU21QYQY89OfYA1"
    "AQu0OXD5aYKAaz1QsKw+AyBcZLuIhm+3smeOci1N4QR/IUyDbrH4+v1Wg86X8CNPpdAhgiLgcXh0fAxilqyoHzRkwRygEI4DiSoy"
    "/wjbQ2/fQdTHMxslxFdJOig9A9qIYuGL0WSIwbvPVTfA07Nn8RAWca+P/CQFgcNSWBsrerSHoM04bs3RVDHMLPiAJlNSQULDiz2Y"
    "ZEmgtSLGSJLEH6/ZEg6ZbUnHn6+Fcd5XBMSL46NPJVSNHAOLYZpEnWWsObahCtyMppR3dyaBeHk/SFRRNDjBkR3Cnj8iLGuzyoA+"
    "2cJUETazfVHBk1t96OPX89HWSrGasQqEHe97n/B3YGDhcSPkNznACc62Iib4xXbUYWZsbb2NKienSHB1nVnlKX7TMmCQ8yQI91BI"
    "YKEZFJqcTARgaCYHaNuerlcJlIN9JHNFB4FK88P7atNg7Ko8OiAAcWuSeCxmdmKAaffHxEJNQFoLeUozt3QTcduD4nHg9dUAsgI9"
    "CfJGYvcwGDLQGV1cXBdMvWJpG+Our1fg6FvaQU5JAfXDx/NOTNoJ069tPj2KPaUR4wHu/nrl4TOttzzqL+4t21lOz4O2UIK4KxCl"
    "WIGo1oxYsUQ+6xOJh0vO+pOhzpEgdGInH2QElQBVZ/nGgJQadvB89BSvHAANGxufYLCmZSV+hROrySz8XYMxHsVefhS9XtEIer0M"
    "9Fl4e71/xNNl4IraL3PKQx1yUqGJPzpJWFBUxgyPK4zrG8UbMjPv765zSqkPuyeNzyl6/d1d+l0F/vN9tdxGi2t+7hVkO9XbDagC"
    "IpIGWIBEMt4GnmXeZd8aaFqUR+wgJi8N6gD2srQIu5DDB2/Y5Bgi4rGwyZLa7lhei1nIn+M25/LaVC8K4H8YaTJP17z1LGW7u1u2"
    "bKlGfsZnGNrjajUBVCvArbNqHShFcBkOVl7B1L3Vi8bJlSDxvsFrSy3riSDe2N3gFUT+wcpyRYG6ru7fyg1e5m0Xsy2P7DrBXJRf"
    "yvjpbNlDv/IXPPTjXWJZCOB1VuRnn+HBifrW+3QFhTh/9TO7F9cPfGaXvzKkGx0cyMOHUGCsJFwfqVgj9zliJst9ZUV5m5ynUfDW"
    "++3qngGP/8C7QutJARbNWLhlbsrJsKK3CbzqiIy58IcysRglm/gy9lG43hOyeew7RimS3I6SeJZOOoNI343k7N8mShVmLtZWaHLI"
    "PpzHX6kWG8RZlnAHZG9nTIUU70yPsqMiI4WADefekEWcgqyikt+J/d7poR889150MkOwPSPg/aZ6xus+Y1aJyjZHmSCr9LwhMmpp"
    "srna7niihQgxeiYj6Fzq/abQqwUnc6FLmH0hmPh0apZmqijMLPvEmOljZGfgG2P1DFFTJJtEZA0/+CwdKowa3ZhKwg/ShqgE+C3b"
    "dwCHzRQkqlgtzOCRWCUUPTR2DBYK7USyOy9jmBDoS1yECe9yZ6fkV43knsjpGtdcjrx+Os0aG/1+raj39OrWRZSQGfRiM9V4usjj"
    "6SKLp4uvwJNVJ4+Erxr9PZfs99EC2yhF7VexS3FrfpVJinna+wBrlGO24Lrcy8yocgKjZrRHVjbjThIPNvF1gD53UQY+OyHLAMql"
    "77Afu7dS6jJGzEcKziSWvXkycuwA+cKUOEscZOFw6vHbd1h4PjEnGxsohMBg0b0U7sxj/OCrVTam1UX1EFElkDNU7W1iMp0fNzGe"
    "oKPkcHaKr6qgx0Hs9MCmVISp12wtooYAbRDK+kkGX2jnuK9mfSd4v4cWTwKYxTaqbdX97GcmIdciPf+UK3pqCsXzR6Pk4xj1IKHJ"
    "faSCXSm8QUGQNYedz2xMHEaNOuxTIGLUETCC02xXPHM9QOukfxr3yJ4dil6g2GtvLrznNB3jgoNWaec4g2WWPD/Yyp8z2OrKwVbK"
    "1fpXj+jYRMa24K7+OXDX8nCT2MaPTntxtw+8Hcb8I8FJt5dVfnz9bEnLFKB7+fp8zXfvNLWZRVqwdhbkvQeZWLRvos7feIkCNTYu"
    "RUZjplXUYqzCMWl4n+6R0WC16ZNp0u97RfyxvA+mfesePSIHTTska+lYixbS6PAEovWILC/PRzaq1HGhHYseP5AnLwCBTWssaWIU"
    "53rS3N1cEEtzZ9kR2/YHnDd/BD9PO71HS9fF4pisrW8UFaoBImtV3/hqIIL2s7BLOLScHERMheY0tPqGvHCkIedaUlJdL+hfUUqS"
    "2qulhvT2C8Wk1RORG8LMknCyA5jZEo5EsDPgU82iqfoyAJTedAkMkm2B0XDBUPX/OCSieCiGg9UCBoptFwrOzmok7u6iPwZYooUB"
    "UtCI1hU9Mb/BMyPUKqQ3rAkvhp2fnBjYmy7snJ3p6g+DzqCpSzDT+Y6rKpACRT2drPKl8gBdRg6YLghHk2c5iCoZ7QUVO1kOmB8Y"
    "bdy9sFUeCBurORVQ3biwXxUeS9vj2tY37PJakenNyjK3JDZ01QdCN0uM/tdCXMVFnFVqNVE7/XLdTw70mgW6SKkByKwY/7eXPWoy"
    "Gmw1gmn8Z4OJ/wb1cvDKOY5VaDGYtouJO2lwxvDDmt7mZDaI7dlDYF6SkK6DGnOs5lM5vyyQyBM43jZmpBc4CF/a9tsf97Qnmsyl"
    "HBtlo+7js1GeOEq3jGQkxtlVi/n/Zc/81k8qLmpR8IPp1rpkfhdPfonjK+la2TKoW2HLsMQezm+5ppQ1CT+hsIr+uFdkQG9ZM9hd"
    "kd36OZmAqDByjh39P3L9Yi0muwpVVt8/meJZwxmC8zjjzgpX9s9GyJFHCx2MIkqlpqG61r3p94Btr2w3AnF6D8utQKlANiZ7wPhG"
    "8jxYt5Bxh6QXEZcqfqNBiMCZ/DWHBvKyTeYnMpFqBXwC9Gcnle1UMj6e3JUEyIsvzZsFY92APQSFDdHcyeuAt97o3FdGO6o0KewR"
    "7TjH5h2BY4Cg35BaL6ozvU2BasReOaiW/WJPeMB8ghQwAhKad+NX/EgK7TIpJAY+YI6Np1Ce5ahW/gZdgha+j8K9ik/4ya4n6/Pv"
    "vsdZpl8a26r3z/mTRrvFgQFzdf08j60glcoYn6twit2r9Ihyf3r5lVArG82sxWwGf9vN8eeVCHSWS2ahRF+NU1xQ98NWvQc2fOii"
    "l+by91GSKBbRfvEWwctHizwll/ltjIpSMm4pbGCRfaLGz2ysNh8XUOakiC7//V7amH/Do4ep7kNEcWldhKl3NX1jlDwekMMB9PJ0"
    "qYzcxRL6OBg55W4uUMKdFho0d52S+BBPdArKC0UEOwLP7oHbdYw9zwqb7BWmnjkG0eQX8R2rEzPmz8qkl1xet8lLAhn/WVbRou3V"
    "XjV43KTZpyN3gozbt//2l/ZReXMHZIbjeWPxbb+Eq8CLifun64g4f/2gyGCDbbKCfms+ugqx2QBwEw9uxZVpMOx/Rl6MP6YXo0ka"
    "qttv0eOGUb+HXI+xoeh4/lzGxU9jjJ8zSjzp9afD/pTcpOl71pFPwowv+HCvXOVEta73qFSJV5K+Zf1R6+m7o9POIPvOlJ2Lw27F"
    "qVI0/a33+76/wtXrapeudL4xLJ0Ug/eQvofatLc8bIRkqVPZiuoJsL/Cdax0M7qKMi1bWyxzc7xSzlt6Pcz9TOIuBvvK3Ko6eWwi"
    "ZJQ++go5O9+qrcU9MsXfv4xZNx5bv+I2OT9itSqLRix5mRF3CvRpCiS8WSLX8dYNLxDOnqHa3DLdz8yRAQjN8ieGADewcqFacF08"
    "Q73pZZEqUghHkHFwPOiLJjINHNqq/cwSdSFPOPRrYa5b53STGU48vtOcTYrmico4z19Hl8XPX8lLrMXwMYehOE+uO72korhVs89Z"
    "u5fkKkATQyFEUc5Vq/X4FCr3DQd0gTpTOcsvYk+Oc8cWHA23/1oplwHMbyLNZNcJDKulJEazj5UtYZGTcTctao1PSXtwg0tGO5EH"
    "Jgx9PVq0sCRqCxIFHF5JSjusv4w+YdysTg8lT00xgEOXp67KpbTpesYoV49rKvJktnNp1NTLz3Fb1sAjfGydowjf0D0X43hCgpd6"
    "JcSeeZ1XQo6zJN4bMXr7mFXQMnAyGli09NYcEkT/+8nZyHC01Dg9+0B2CO/0ZQdCeyWVpq4iKVG5Mc0cIJC1OasUYPt3xTChE3pZ"
    "9bPhkMiPLHur9ZuL2w98clnmDYXFnmI4NaEBedRncX7hciTkjWdteo3uwzI5qGM6ubT9cnZHY7xavy5KvL1c6qwTmt/E6T29bB25"
    "7wE/F70aY4eWh5DF14rX5MsLzYndLrjcjVWOnpBC2ofLlnmmrV6oPYeCdK0g5TYvHJ9INNxnGQjl+eLpbHoLLbx1+ycWRzGli+BK"
    "xrJlO0zHBeKuD7o/WgR7BhqYwqjg1dzlZcu+ZcuXI4gP8m/rpj/345scKwm7BE1UE2OpOzE/+yq7Qz+YoQ9G9GHMAfExXDalSymd"
    "aTfCp23Sygx/jOXGHhap+OCJ6PUadsq22/hozfoyzCGBnU5uVcw11LMPDkHg7pzTQ49XaYyulHC3wkbr4mxK0fXKYvFj4s3IIzK2"
    "4FSdStUcYEHchpbwub8vzeFWESNmYVOpyXW8eTc2MswtbmxoL9lT/aYMa4/YMfO6XVJKsEdmnBpyB2lbtMdZMx//WGzU9dOuoZe3"
    "cTdBFrRPIV/levr1GbM0/L7g/EGt2aZR97V40vrHIfsI9I7iY2iaL1GBCPYj/6hynHs9BEM+6Iz1a6cUXzspYJRT11/R86HzynOX"
    "/AlOMfpF4PHTn8S/u4OTs6KkhSP1DkxxcT8ZV1DA2+0Th4LEuzdKw5MAnSYLCkQORvtbGgxNhXeU0nAwxKWXChogMUgwWSEjNX0x"
    "C1TCh4DSSRKQxxCANUXr0WMYBiyRa1oi+gXNui3KqWUmuT7asUsiXtrw8lHvoY5411p+oCw/Wdp96PGy+bPQw+5D0CqdzFyt11IR"
    "+6graDewrYYjfi7CIaBO5AP1h+o3b4aHwILrXkAxt9fO1luX7UmQqlc4T9bX5e7midcx25Uw1C6HFf/JGhRRD0CDQ/2kVvHFYumt"
    "Q5jc3U3Uj776oapbhCtGc+xUz5G6mWEJd2J/mIlUQTrg5wIndN/dIi5ApXT0enSjbAKBXOtlKws1lYqdlrtn1Hu4RK20jiYT+FIr"
    "M0rMtvc9FMmOf2MD9mXHX9fLs71eCdchP90HdoyoW/9Mv7GV3h9DFTVeXr7THA2ImQZkVR4OicAruanvrU9lP97dxRwr8rup7DDY"
    "LFOiEAALZ+kngZ0WUtuOEFURgCb7+EMFUAjU294pNO3lCH5bSjuLHs9AKB+W0b30gh42xYUhfzY2dMwfhF5i/kgEH/3GyTOm6T8p"
    "lz4JTL5+oKimz2SLjHNgPN3xHOZK/Cy+hBf2q6fsPtELXEz69pUhl34kr8xZ6C2Uet7DNFufZb5ZeDxV7QSEB4rMnaLCo9PrwY8g"
    "sVRD/Zi903BLR8d6ZUxw6qeIegurNLATfNNHjwl88ocyybhH8+dJaTybXnCgrwm6ngywhDjVj8RbmvD07I0cfUztohTRT2bxgjej"
    "l/IL+egODXixlX7rzJrLmBa93Ves+mGvl3yzN2GvlvjArgcf+CdAW/qwb7oO+r6zI6SObzceASf4hB6LFAwGFjF6JkUHN7pR9eY3"
    "ofF01NTr92PqR+kM1vkBU2fhH3FWBGx23akmtmePn3LaR/j0EV8LBKw5xXcXx9h/CK3s60UzyvUvbn3OJqPhcxDf+vHU0yDJYXFE"
    "fSgjnZitKAN+JJNxQ8qunkLLyTpjeT0P8gLFJAmLFbsEuKNMpdDbMx37vNJT36K5614MHELe0TAm0jT4tDJ+VWGhgWxWgVQKpN9V"
    "hUAC0ySedjYrZtm3KruT71TZ3cmTJ7558QM9HE2Oj/nQxsAf9L1ZkRSgXsl35bs7UjZ0TgGdm6qhb6v+dzo5sZOR0QA5wWzd78pt"
    "gCxEFYPohNMjYHwC9U1fGBSym8HdJ2M6QUTEOq2UH2nyAo3lxPcTvcK6u1v/VMLAIvBD4V9dAqqH3fI2S2XDatPvzbP+cVPj11/c"
    "iDDzhZB29Vu9fo8hCP5xFcz7Q3xLi5oVfDNEfQ2yC+Nc28CTp7UMB6kCluw74BvnBnDETUawgjDmO0qSbXYd8T/++9rj+U/S8ngS"
    "wxk2fQESJr0cooJhtibs68hOJHjs5jSk0h7C6pbGFvBp3SzWdw6TuBuTNcmv3Mu+tmI9mU0GUVv9CC03JMSOOVjQYc+y6S5a2iwX"
    "Y3TEE5biwygejtPbCEOmyK1R0DPQWV1mWx6dk2rU+1UiQe2l6FGBA+mdxa7uuThIC07ciQ7eE6Crv4UVEW5qKUzpCvyC9HHDSxU8"
    "SkW4WSDIOZ1+Vg/F9ya2PpnmSszxZc5Jt6UHHZAuWLWdDZ7GNfOPxL5O1S93dzB6KOZbL6H+sf9nq+qdx08r9FgBYQNn6R0r5j50"
    "TnO2WWeXcnWCXE7R06nx5vmEgkg9Ir+r6YV+abe+3rWNR2lcdMd0NoCzF2VKy1cp63MKHJKjKUU1Cs6NNj/pXGutobZDuDnMmJxq"
    "2SfGJShmO4BpYNoeNJP3XmXw8qL43ZZJ8Ppb7+W+j1f4b/bxlpvz88sS0uWKo9DgWvRU7oKk4OJm5Xy6b+XMbr9w5WgL5Ye9pHuq"
    "zNgtO3V1I1Jspj7VF1dKvIvFeoenKYNuukq9GA3yfqiluF/0LKRw5rOoFGWoxopjym71m/G9xovtpxt30Mk9g1aWf4ketDNMNl6f"
    "qkdH0AwlqFGp6VHJ19ysUs0+wh28SWaYFLpwOdKgMyXVTFejznLz7eBNpy/D3EjHnP5SHPbvwaF6l9FfjcPrr8PhclSwCiqLCEld"
    "KNsnNEhRjw4cS6CTy9zd3rV2uQbcW2q2ArCdfrvUG4F09NY78Yvu+/CqaXV1GkO7nZt4rarTNxyMCYJcfmZAv86DHiN4ywCLLee6"
    "upFbvulK8hcrS9ZNfqV8DYlWpp0uHjjWwhuy2/msTv2wqIzeHsbX8cx5ICMXY1Mm1vKMzVki0uCmCvCg7Wj1Ux31THR9pmxUV1Hz"
    "11/KB7hB1+zrx7n7FiSFs/S0M9mUe7S1XJg4PNyv+X0IHnB4P+iyzsd+oa/E7J5hr5bPvFlsPZDFk//uzk7S3Gt7IKnEddaKX3C8"
    "TDzNl8gdj0yHbYTHQ1wzmfc9LsyuB2FgsmRrcg/ZUq9YJqvJ1vk/n/Szuuoewq/iY7kzJ6l/PtHv3IM99Yimsxp7t3820adlUcg5"
    "8IK5HxP3j310z9jVy53R6rGfft3YJVlxfOiqQTN/q3iq0SQt5qgg46vQ8jBRygHJvHgmdXH2sMNb1AzYyF1n2HCd1Z8II559Ts2N"
    "R//+3/5PEJ///b/9X1F+xIC/iU3Z1Tsn1UiuMQIkpA8LWYU+LDSWWEzLuyPNxEn4LMf1BZraPqK3n5sUzVpd/Qen/QQwS+GtaXrU"
    "otBxE/TbF3T4VF6yMs/i7DRvamta85j50MhremKcOL7FsUP2L+0X0Tf5RsTHs7HnYN9WgWOUEIlQweyJFcZAcvlMGai7mOgvTfon"
    "Klwg0uNLfiiZhOSPY4nQpk0iRskr8pk01c/H1P1UXEo7k/M4dZ6l1MvBh8sVgea/1v+MGQMcEfuKkzXrdScDXBQVvaQqmKfnS2fG"
    "wZMxbTqF4R0dfRwFwuscCz+ifP+7KgVA6wjHQkqF9GYE9NDVX35fsXgOm1CRdD1QFKqQJ9HGKMDT2YyIKMjgoC9Ktl6cn2YNV1WZ"
    "vJxvtG4ZF9cay0Yvk2GBSD2Y77QS9Iedc+zk84cCxUIy+jgZaGtdWiC53FMydXKpGakJN5PRJna7XOllLy7Uw+BNwGGcpjDGqaPW"
    "+vt9yonJ7Z+i1iJkWFSTQv5mscnK0wJkVtUMiqF1Dp2TuNNjvbHGaQHauPbDsPafogh8+DvU+yc1Z4d7j7MlJhhvmWDY6tfsQ43i"
    "ncD664K5q63eCFQvuxGcg/S0MzydKe7BqsPpfr6xVfsmiR84/7Kszibx9OI/RRH8oB1jRLA84uvqEUCiXa0p91dF9OgA21lBkTh/"
    "OW75fPlSRfzSU9DR1h4K86wDFsWr/TY4eBSPSFk0OncaV4Vm4+owy9qNG/c5qWv+GJH0eboXcKjvWEX6HqmGdKTYgou4UXKIF3io"
    "h1TaV7ltb914Z8qXBi7FH+iGe2qeKvd0uZ4uZ2GInguJ8cBUx/IRTBlLZvYX9OzSRKgiJbkKT8XG+yoylTHg3zM8Bi0Vmf63Z+h+"
    "HgjzlBYhNKRN94uCDVXreKHqMlaTSze+m8q3kK4NUlfFdwuqyJ3jULL28Aj/ZQZ+o/OXh1tkSfymwF74XeF7pxeuXfdkdA40ZLr6"
    "yRPyPm8TvN0bS/nSKGlzurLH1lZPsapRQkeQ03bpiH8ds57mOqagv5ejUz+0X09ZbaPFPBa+6GOYah1kIjVBJqQf9UbnfL/UT7qD"
    "GXDSHjXNwfz8cH39ZP/ISsEH/X03ZkX76DjMt1xQj8LUQ/NA99rtsv99pVnmYBWCLMv3e/xto6zvllN0KKzHdoF6sAvYmcNQGRt9"
    "A4VL404P9tck9aoBWb6iB2BTCysNQ3KtxdHu5Vo1ptvUoNuav//45s2rNz9g1LUpEK5375+/23v/HIUXCg9EfOXh61f7VMZOfLf3"
    "8fC5uvh88erNq8OX/K7sxd6r18+fKaZGAtJn0EKvLthQP4a1SqHoBxhYVeLU65JYhhuP2pVymR9cDDufvXLAP/uJhw7KuMq4m6IF"
    "qWXM17PCkGARWDZH/ArFsjSAns5jjONNXaKlL48BFpxY6kgZOECAu7+FRWvlUMLGxjrBbyOfMiQCOP1mYxb1NV2w33i3/DTSfaAT"
    "CQsLCiTdo0Bgd4lxeMd4W253iwQqcSNMaPycFeBHY8beHgKJT/3HZ+k6WYSgkYnYMtGp/Pu1Nv8kdFiDK3VO0U1haCc5TgdHHreM"
    "dtfWpj7rJ/3pheBXD5q72zfd2c322PSdm5166DsdYzJ4/hPu4a+NuE5kO80tMhxeOhpdZTq6Ku4ISzrwYwJF+ipsGCjwwwbAY7Zc"
    "+yP+oTb5f1/Yq9BdfpnWXxa3zutS+01+PFfrZO3bNf0xXaDlQ+L6x504UrA2I3V8BGTecmZv28fn2ceaAljxYxu8fH9jPaVTo0it"
    "ZzV5DmdyH4PDJ4vllGp8vgmrH0V++DUcTdCp2fdlYznw9JRekE9GIUbfLGMwgDG664FC4suxA/jnoNlMi5a+pQ/UIEKM7xk8Up+u"
    "JkGPlJ4wz3MNR2yYgmxC2KPQ1HOW7hXyOjq+dfFzV21gsvQdKqJILFgyL1GXv23tOmR+5StXQ7Nwfz6eWxUXVof5h2wFgl5+CSBh"
    "C1LLpbP29ikKGhYj0hL+kW2icq4dWwKl3oqsib7fKyfjzeZDnbGwn99IlpHluFOs8/WuMD+1ilY/oUcOULVfsAv6eUd1ZgdEfbQ6"
    "tXaBeo61BhuAH3rn3ifKA/CHTCqVdFaN0d69K9jPyeideJooei2aQaPzGhq52FfAsTJfGt8C9ujZ9xwO7Gl4xCnRNT2nAhGBX1cg"
    "nwKsC4qYsEin1+fh/PNwkOCL0TQdh99+e3NzU7qplUaT82+r5XL5WygSiTuXall5c4Ff2O7T0Wfg+9fKa1X8FySJPgZwEaE8GcHp"
    "GR4BhQF2BXDfC6ODSnmtVqpu7VdqpXK5UaWPcrm5VtkqVXZqO2v10k61vLOzVmmUtnYgHf6UazuV/cp2qbpTq6zhn53tNfhsVuqV"
    "tWapvFPdguLNUmVrpwrfjebWFjTfLNVqVczfaVYbDcyvQ287pSqmwtdWfacJn/XyTqWJpbd2atv4vbPd2ML8RnW7Dt9bjWa1Sd9b"
    "ZfxuVJqVBpZvNCo7+F2v7nD+doXyG9Ut+d7G9hvb8D8q3yxT+WZtm6CFdrG/xg4NHr/rDfqu1+pcfmuLvhu1Kuc3qP7OdrPB39uc"
    "v1OtvqbvJn5vlyuV7Z/xb7WytW+nV3lY2zs1+mxsY7drlfK+Sq2UEcPSGVSi7+2tzPfOz/S32XytgIDvGgxiXwFJ34xkGgR9A3LV"
    "IOl7a3tfIYG+dwQpZa5faVQ1EvEbZm1fIRm/azA5ahLwe2tbzxF+NnlOaQ7hu16rUD7NMXxvgWiq1wB+7zD4uELgE6aMoKEFVKmU"
    "ypXtml5g8F2r1Lf21QKE750ydiPrs1IF5JZrev3COq/vNGD9yvqGv2VsXpY/FNuu4+DL9HNrv1Ha2QH4+Qt2Q7PcqGypWjVar9u6"
    "Ueyr0dzRnVZLleYWfiugSs16uVkxQAPGtnkQPKjSVq3JOONBl+pbZUYp4wT6a+CgFM5Kte1qw8JpqQZwGJQDypoyQ1uUW21u7ZgJ"
    "g+9qtWEmFIDaqVTNhMOf7WrTLAj43qpXzYKhQVgLCr5rlYpZcPBdre+oBfkavytblTVZsD/LAqZ2ajzz1R3c7QBtfYfLbeNChynY"
    "oTnZV1mwY2A/1ddUVdxBNfnGLmTD/Swb8LUCRTbovgJVb2AZit7gMlRNAAQVTCB4qIgqJiBNjUpNYATVTICoPM0EEyg9UZp+yTwy"
    "fcNsnmemf3W9DjR9lHVC5BO3qKwjpq5bep0p6qvWIVPn5ppap0K81TJWtF2tcqb9SPN5D+DZsCYHxic8Oeq4Q7ZhbTZqW/SxtlXa"
    "BoTUoArsjwqkbcGuhX5gtOWd/Vppp1KBBpslPMjq2HEd0drE7bGFHVRq20RX67Ud2B+4KbfrRJdhVqoA9055q4F4g2GVK/DdhPHj"
    "itxXWbBoYCbXVE1a642mbhl3TqOMLXPPuPMAJWsKMvhuKqhhFyM+9tWYYJcjPtbUgIEIMD7oxz4Ur5drDfoiElIvVSsNUw3S6w0A"
    "RTULFKXcpB63d+SA3cK5F4jgu9mo1jTEFZyFqiK3SN/KO7U6jxc32Xap0timPSI5jKTtNVWRkFiu6oYVklXHPAmUj3DxHG1psNUc"
    "qmHJDKtR4+zT0cmrgpYHEVAaX71JH2WkLrSKsPUtJKSypvblBxXeWVOVMFWRY2JTqB6TcShONFnV4Y/yPv3lcttrqrxk0l+CrYmt"
    "7ZTKtdpWhT74P5zCv6Et+VvaaTRUHlFvbox+7HN2nb4IVsk2qTxA+sFtNHU2dkBYYYgANE3sXHrZQDpZBdpBdStlOi34GyZ6p9rY"
    "dogfkLvXpilo1uI8IA9P120gkVKXDnf65rbrLpPR2HlNrMnrTCufFH/ZnU0mcZLus5EBsfSns9HN+edocQw87WtS1zJT/BxZ4H5y"
    "gfcUGIV6isHUlSaX+GNbfzt/RYLRojU+915dWk8mEjtCTiqxOUBy62CTVlQOYsnf2yz55hREjIs8Y67SWWOLok7/mmKKRrMEWPWE"
    "/Xpz5PP/DEYdKFYDZ5P+bteAgm03qk38rgBhww1YJQpH300mYuWtuir/Grd5rdzg/byzjdu+Wa3V8Bsaaqzp7wY2VF/T5elvbZ/T"
    "t6VcRertyDc1u60KvwYiUa8gscLU6jbu7srONtGWKm1f2AzVWt1it4BeM5cmPFe9vGPzXMh2WDxXve7wXNuVhsNzNfDb4rkq3KXm"
    "uZqVHeG56sxz1VyWq77lsly8YQ3LxcyJYbma2y7PJUyS4rmaDZfn2qq6PFdtx+W5FE+leC7FxCueq1l1ea5a0+W5thsuz7XdLOS5"
    "6lt12d814rm26fwAngvgrOJ8EG/oNsFkCBIqTCrwyITvMglTTaBGxAuVFZHY2WkQD9YsV7BLONhY2tlmTFaAaWPppyLfzMptEeKx"
    "2zqzck3GRK0qLFyDR1rfZhYO1iGzaMQqNInvB/xWiIWCWW0w4hv1Gp2C2zuEyBp0RByZTMxWdYtYMlheVZ7nWo1YskYdoa9XmANr"
    "lqn5+na5jtAC3prEuQMwWLxa3sbdQouROLIyzR/wAE3ifOrN7RquUlj+gHfgyGCUVVzFCC9yZDWcB+RP6jt4ysJiK+PurjUbwPHA"
    "fgKpaOe1oga0y2GD4a7frjARqBG7g59EI0iod2jHp4MtWuUN5PiQ3APH16igALKN25Pq72zt0MFYKSPDSHsNTvkm7vVqHboDdreG"
    "w4fjGbAG7FalSXPZoOUNjBlwoPgNi5+G12zUt7A8sDZlyq+D8InfsFe3iJErE8+yA91WiZurV7aYuylvEzvXqAnzU68zO8eSjmHn"
    "trYcdq7K/ISwc0icLH6u7nJzjZrm5oQQMUsHa7tZ03lVnARi7HYquAJrsKaQQuLklOGMxEnHtQCTCZI3Mgb1LWQIa7A4tpAX2d4p"
    "k7BYg9FBx7BEGCyS1xswB2UmXNVKGZkbqF3FIxpqE69eQ3rWpBVRfZ2ZQmRqGHRLnVNndU6FtTmwqpGjr7AsDDvY1eXUXV1OnaWF"
    "hkjaWxlVTt0IGySo10SXw8oc7NNR5tSNLEN6gG2RdXZET7Dt6nKqFSMqkZph29XlZFQ5WhITrUUto8nZyWhymiLoiVJku5rR5DQz"
    "mpzmEk1O09XkCC2jXnkVlXUDhpFiAJhgi9alziu73BCAhM2vlGU8cjww+KLiISqPuOLDq1avCS53OL9Rq1HxeoWoer1cZRVOhTuH"
    "BUlgbzVFxqhy81vCcQLRI9zXK6yEAepDSpdqsy7brEHAAzZIf0FEbhumdotkgioSLZJEKvSNXCaxHLUtUrZUK01iLWqNOgsBtHtB"
    "pqjx1ixXUeSBnVqpyobaIg6gsVWn76robnbKOwQOQNPE9mvNLeK5a9T6dm2HBg8zS7wF0D4+SmEpkZy0xeoPIhUgQMlYK7RySKCq"
    "GYlqOyNRiVharohE1XAlqpoIVDURqGpa6iUObLuSkagaIlEpkWqHRaqKJkkkbMOuIVTVRZjY3mk2iENiMaaxhXiC753aFglLNJ2w"
    "6+HIQ+reBIpCleGsQbF8G5bPNh4uFTzjtlHhRywkgEH0ALBcxmNkq4KsIGz8OqwjPA2quPeauCrqWB7qN+lwrNSI+lqUlJUFWLW5"
    "Y4gC0JRqY4ewDbsAz0lYfyx/bNfp3NwGakgrqwrpMO4qn7NAY2ukAdghHgLo+7ZWkJFohkrH15nulPzTzMg/NZZ/WDkK3zs8+w1R"
    "jiqd1BZt2+yOfoAQVL/cua5WWAj63RWCDlnaWCEJKYFkmTz0/qvloaeXrf64FH9O46SnQBp3ptOb0UT7lYz+yxr8Uxpvqoy1OaXg"
    "P2ggP+jchmscYWDzbBB/3tW549G0T4/o1ibxoIPBkzlv8V9yTVq/N0fX8QQatboZ9pNNlp4A7eVvlrWySdERrXoiaK31Uu+/qkIl"
    "KlTirP/qG2hPO92rc/KaWVjBZDuVoEA82Zx0ev3ZtLgelShxCVV1Gex8m1YwAjNs/EdwUTYp6aSTKGRT7lpluhZ3pjFG0BrN0n8e"
    "xDdx58oCeCkWp+mE7uNLWKEAm0s74MjzX9QFV/mSTthJ7Bd1wlW+pBM0h7S6OBsl6ebN8iWKxUtYSHzV2+uO6tId8OqaWGQFXGeD"
    "Wb9wP5uNvLSWnUIPTqx2HrJZOYB2uDmcbmIcwM4gWFWE7FSLIEVFydI+8qRk3Onh44MM2qRcSXIfRBZUnWLCwG+Di2tQXp6KAL7G"
    "n9emowEgt7gn3pgF1T9vTi86vdHNkg4586F0K9PdvXQAn/3Ccbd6GdGihS98HcbvW8I19lhk8s874wwo0nQJclYAwM9RN4ed6dUm"
    "Gj5YkPQTODQ35XSK1RxiYMrSWT8e9NSMlz7fN3nYcB715ojrnMLMzdLYoskjGM6WTbeHnck50GPK6HYGXW+zsvZX/oV9URe8Y9e+"
    "Xav6fo7iZ0rtFp50uQJFc4bbKYusP2MwReOwEDubTBGz4xFZ2e7+efNkFc3PVB4BITroWrWG/JX0TaBxACYceMvBBuRU/bUnWQz9"
    "WSAWzmgerf90KA0c/xOi0ALuAej9Z8BfQ/gLd/xfzY6HkYhpYjwN55PRKA2VbSyy/9dwEqJlLMxuirEvhfk/iiyGGp9IDMdwNgJh"
    "HjPwN5MOBv0mc0InBZ+T0HvntPSYfwa5EhgQEAvQDy7g8gNcG38tQMYZd+mt5wd6jJnFYhQgkkmAiVaRcZuBUokY+OOLa3MVqU9r"
    "IFfdrIwokAPQyVechIVXaIqPJ7chTqNrJTjToywXKBn0YPwhsxotkRHQJpa+2/kS0RPJ09wqRrxHN/iYmJsUw51CEV7Phyj6Fa09"
    "Bmqujwp8MTEaT0u4TJLehxG9xo4HZ1E7UkJfJE9PFgsUOX/WV3BPQTx5p4VNFkKnYfJZOeWHP8Mxv6wP2akavzHQZpYoyuKYkNl/"
    "H5/Hn6XYkZSDtOefx8e6fPRvnue1W6W/HnU2fz/2+efe5qdj37/LZ5Q3d6wMKmZn0Me8ESx8jPpDssADYSiEwGqaGm5ywygsPRAD"
    "9xZjIO8tdhbHPeRppYy4CteF1suLQE12ZqzsY9MaKz1gWwS8NQ9gCy5rs7JAf54x7cpC0FQ8ML31V5ZCFyD3l7IIyb2t7SN5WAG9"
    "fj63vIjtiGQF+ifxbzNgkVe1RET0VW9VK1Rkn0xoV8+RVfyQg4tRcS5WVOodb04qRboktwx5klkNGxV5OGxU/F7YqNQ9sAkNXw2d"
    "FHo4fFLhXgil3D0w4kN82qID9KCwClBdcmWhWTqiI3vJcqJSC9H0Pb1E0ovhRA3J1xT/8biriHWYXvSnweNxB7Wcr+S4okSg8OaV"
    "08tLPDAe/e0UgfwWg2rHk+na5hoCMjp7pN7zvLxsccra4e3wdDSAA0Q1ge9T7Cx0tjrppKMJHjKUErXzh5N0sBYvCk6utTjTptsd"
    "RhiCAU1mXeqlxWUgfV39xvMuHWETbQVDqDsMaMzmIdPHS/LmnZhwMq1fLtGHeB8AUT6JYS7gxMV1EU/SW6ogftOSIE5mQxgykBb0"
    "tgywnfXPZ/r7ZtJP5ffCD9ElcAuqmO5/uTSMxQ8ICgZDItcLBvkAjYXNNEyfAKugW6BaKXm+pqGtt6IRQR3d3a3HxmMu9pGgg10H"
    "t99Fs4g8/sZHgrwULeqHfWQLjtHDO9NYhnHSwljugwH1uMs9TqweVW+T3fQCnwR8gK7o0bwX/e1vVsNrw9k0XVMu2dfGOp2fBUU6"
    "7FvKjnwJI23ePuEbCuTo4ywiTD9pbiXPqfx8mVPax9ATWhF1LzCeMAYqwL0Hf08HswnbDXUG/V50DDVxTCFuqxfINIfzzJakUI75"
    "bShU5Gc2P8I+mc9k1//J2Yi4O/oSVh3L8FFHvxeKX9jHoGjMnnB55g9yyZMYBZTX/SmMWnXEvkhedpLeQCUpppk+hujWDLqz4Efy"
    "UFIAtuiLGTz8Dug7Bxc5e+efnlWC+Cyf6+SAztWxeDN/EZzGIJrFHxOCMAffLDntJ733zog91ZM95o2NlpdPRZ9K0Nutx9csUlEw"
    "g1XOevzg3rMzpDBx5xcjWFjzUfKWs56jlsShYtACxh6IpC6sRu7kMS7z+Jpi0SKRKP3+KunFn00fpzPYV4Zvj5SKJwpQg4MvxAVc"
    "WKDnqn81dsTKIY00i5Xl+KIbp0N6/Y6+lDlt2JlcqRODXizpob6OO9fxkgkp7nrVZMmwW3L0qk72zlD0cntipPK0IET2+HPw5MWc"
    "w5kzmTL2SXyGqx34pdLjeOCHTpkSHbf4SvgXVOu1PksT2VpPovHnKOg/pAOAG18uHipxLy9YlvXL4sJtI2E7/XbaqoXFu9EqUg3V"
    "80og72kLQ14vtH8nu29qCY+pmDxlea6nJ/SwwMNBwulpsskL4wXxLbnWhKyhMy7+FnkFIaGhxami1QcxOdHH1N6JRGSxcSlUtEUh"
    "1i04hGozGE+BdOfxGSS7LjSVYmiyPeHL0LQFR6LUngxfoJbIL3FHPvu0Rwf+dBQmWRTxQcKQ/RTffhw7oOEBbENhtAoO2qV3Coup"
    "cKWWDt4Z40lMx0rQh1+kb9hVTVN6axK49LwfIOFhN+7Pp93OOI5kulwEABFcr8hKXBTk393BZHAYPmcS7Y0IkKw7c2rBRafPyqNm"
    "Nx5MY0JLvBIL7qJpxYIQ4GUEIVavaabLJFgxtML+ChfY9KafdgUUe3d7GIuk25nGa5VQxod6AjpIk9bc6HwwVdkdR7VaqVb7Jlrs"
    "nk4geZfqV1V93uz5Fjhdt9FolBqNTBs11QbTlHwbKgCntIGXgroFxfTkOYKEabewPfIUVjE7C6Y2xEzlKYRsFcVs0W7JHyP2kjLL"
    "YTd/qsPEUdCZ80IqHVjNxEWrfVHEPxSeqKiSWA1nESNS0HjxqclIcM/LVUhwGb+7O68gtbVy9OujnochP+ICMriA9ZD0RjcYp+f5"
    "NQiSGtCIu4iCgv58jaTl4yiohryXdDeJhwDMF/SouDMZwvv4LL/iFLsR47pERdcHUnkVsDPMh7fWnc8FOVtCd4TkcSlbyzo/ib7N"
    "FzbjlKkDIJ3elHgHCFibXXJ5FcxHk/55P+kMaPQhcI50KISyaQbQ7IJ8CMyQd5/TEkchKy+GrDngt9nRk2U6xIpLEkWW1NWKTTjq"
    "CvlXCq8YUzklsaxqz9KB3tMil1Tq0FVtWgrTe9rkkovA0K9lbVpK7XvaVMh8RzUWQX+6r24ulPS3DG6lsFRcN1/qwH7kU010lXpJ"
    "f0z6v83iV71l7T3u955EJ0riWNC1R6cPe+MZyKjvCmq9GnhzugqSpcXXQr7cP6yo9fHSmy8Cc7K29QVGYaJvtuW9jUbj0STtDPBu"
    "xGbkl6X7ai/QVQ/IZOY+q/s5eEd1wne3gTLgC3+/xN/h68vgA0znNDy9tXVhvz1MF/bb/066sN9cXdiPokoiVVFLdF9X8a2KbSYp"
    "QJDe3iRKG8b9TJWCaFUZbCaFwwaYU+X6Sg851UMubOEZ+awdp+jsCkAsGa0beylC7zW4Mga3wJBPrFhnenD/oPnFuFrMcFd20++A"
    "uM4wSKIKH7SbPnmihq/zUGfHYazmi9BO3U2/qbYBZwywl/joVgIFhucd4Antkf0qSkYMJIqu+1ePcFqodsR4aHFwX1WAwg9tmIoB"
    "Wq7XvA/7wDjDxtMItlSZv+Y1qZ/+AzWpnyxN6t8LNam/3aNJ/bvRpP72H65J/e0/X5P6GANgk4ulcXQcxAfwhby5SUoPrAKGciYH"
    "PPEBCKNBh8c3al16kSbIFD0aEojuUuBo+GAKbabHdjXz0RNPgkDhPgPzNxpRG3QHAme5SWKXUONHYafknnkLEHfH6bCvSvrolWaE"
    "DYNwECr/23D+xSW5rGPv252SZqrEwc0Rw2DZS0QY/c7c3x1rwMwlnbq+Yaf5sZJTlaOnx6hWeAO/bWfQA/bIHZfcGybXX7SVm4v1"
    "0c8w8bmgH9kCbc32050XHij2d6nfw+Cq+lIOP8wtHpY2X1JWLhfv7jqlLOvCy19guuhMx6PxbIwDUqoQ5/41Lllf5so1LqmfAbMv"
    "GK4S/loBgjX3FFxjVxQaUn4FInDSVNEv9tIUk4WPdRUXl/RvrTSDEfEvrfjClBdShnRQHdERseZnNqYE0gFZwjC3Q78Xah0RCoO5"
    "rGbEzmZMpi6IH3M5H4xxMLCss8txltASxIGpnwv9kCCAbVzCxV2iBS26TXuBksOkUmYlWt8lZ6GVnFVVcubTnjU9VTxFel7UbKg5"
    "IOQbhCs0K+QKTkuCU4O9Ug5bgBo9/qg0HQ9QxCrh5rexuLHRN4LRO3x5MR2MUgxtyj9KmIXNtSP1CyQntH5g4yOgIdzYPhBwssPA"
    "KTUypUs3lAUDEQ31cSzkyc72gxxvfCTPRIDA6qrtqB9Zr1J8QytXdqidBbuwFsKh1s1RRA07Ppl9AF12ctlyse/id/0eBHMmo9j8"
    "jjj44tcg2RiKRL7BrZ16D3ZNUY3fAtTaDQZ2pXvR64LyQARXLATDuZSTLm3cRnQ9onFnn57anA5PXtJh2Cg1Wg0NrFWhCG1PvWkO"
    "M1YVFxf3Nb8KFQYT1aJoDtYwx90ESOImRxze7HS78ZSdPxRHU9CgcIU9LC/FDQ3OtvWIOM/gmdfXamQ/qGyjl/puMNcGV7EWUB2H"
    "d0Vo/ED8iLAEMoRO0r0YAc1U5ozkbJ0vGRGd9q0jZPBFmZVBCZBhXaNZuSZVY8A8S8LZWAlwjnvwMiwb+4lE/kqf/u/jM2ay8kxE"
    "IZfgbmuDA6lD/FagW3PYryOdzByYVKEPsyZTjuWYV0NYaKKSGxvZFJEvO4EWAv2FzYDaeg4JnNHrdwaj82jJIgSRlP+dLwKbl/ID"
    "lw/z1WRpfCA7a2/+i7jTI9+sDkVQdq7QfH42fy9mtVUl32xXleIHyyqx2aypIt/3VFARmXj65nz50BcNkvwtyZVE5GDaKKncLqVF"
    "Q1XSA/Ti3jAxYIvgYB7KbYnTCnY7NYfhrm1Miy94ygTByXa2vkDHk7UFkzhx0ikbmn7RbqRfZnNGx6YeBVoSgkKuO6Ghx5f+4qdL"
    "YK+AGwNB8oAk0slBSzag7Zcd4NvsDCWEXf/AcdCOMfIWQUfVWwQj+VmxmxiiqhkNaA+KvLt3s72m3U20Tka3vIMiiKTeDEVJCZ0R"
    "9OyPswPbX/yHCWy+Dtr0iMkx0KvbEBY0XzehKhJd4cNf9LN/HbtGdDCnGIzhtSpLXy/7IBLM+QbTdj4fa9fwaQl7abfnVJ7J/sT1"
    "4o6XFCBs2vHNya84vTLz3EKWD3idI5EI0R+vrxjVb+EnMNGeT6lBJ9MjefJfGVBdOXjHgOqoDeRPp74PzFmsY1pJ2HU4YrRTfHwY"
    "htI6f/9+6KmAb1H8GVB8wg8dcWt0pcxg3+uo6A08YOhVygUYh/sGCg+k8JHdIlKtExW7D+mttAKY6SB9bUtgv7b2XRzkqpuYr+jE"
    "mkeKS6C4NAdAPcF7cLsCJ7ejv0RP3CQgPMdKVSlrync8ooPolQkMz/VRpbOe614hD/VJd3dKD5vD2norSkg1o9RAUSQB7z8eog5V"
    "TqyfvIjLsz/0YH4TvoT8/CRMBYhU4jX6T5TqKm3prtrRWvTENDnCcBXsdx4aLWhjQUHVF+hWvFewWmi8HHzCmtqjnzyOSFHiXimw"
    "PcnEjHW8gwjUB96y4JlFU6nmBT0PU6S3aFYRETRC7/m4YyXzYyXy7504jgivVqW4PNYNjScxUAeAbawi/NJwvwyKD/3xAwDxg7FA"
    "sb6umie6oz0GpCboPHoMGFJgW0VtVcwYsXlgcojS2GigSGJc4h+w9ccq7CIHqdE6JUMmVRBeGglHMVJhilTtjY0zFYNO2HOi1ZLL"
    "tEmNhDeuvTEDtWOLK1ARfjVo+rt/n4odpCx8Fd+03dakiTqplEF+gBIpdj/RcYM4IkG2JMd1J9dzlr9qiTknHqr5aFX50uK6shCa"
    "2fFbFJ88OQgkUkwffrlA5AOyKMuMzgGwIhO1faNvIozFEmQ7YLloZJVVDUcg0/J6e/LMm5kxWJwKBoX5/dDPbGF0I2/5g//F8tA/"
    "4dA2GUQy/iTtW4yxQcGW3nqzfd/rqp550WZqitN7og+z5CoZ3QB7hJEeQjtn3E1fM72DX6qJhe1aXUGG8Y3QSV9QEBTQ/Z31Cz92"
    "EfsiUCySTN30gOJDa37C2TXJKL2giweKMvDOSzWfKL0go9iom6BL0nwFmu+pnVU0F0KVfFRgSTHNaZz1exsbRZUwR82gWoPdA91T"
    "2wr9M8BR9YoWR/AgcOy2ChhJFZs5nYAwQu4ama4oCkvMtnS+Axyi3f8Xj1NCRnO4PAsKYHzGbsAvmjOuLa7rrehlj3X0smo+elkw"
    "ZWHyZy96/+LVsyjYrFDUyN7BkoW2ajHoKFOG7HmKct/dqY2jok9xTAMr+JQquip0A4XqeZgb/uTjND4cjNIviOBgwrBhvJa2xPGR"
    "SD8res1V5G3OQV/4N/CQDiAc2coK65AJoRUoLKvoWwpt8mkjzp4Sla2brLhRuSgEg454i7wN1yEJzjpSrQBrIvJpNjVQ4V0jfVrR"
    "qwM6kyKJrjVGgcgOOhwMzdUbGQoZLVlwYQSz8dUmynnnrqim99siOMkLcWuZItdFQuLtMlFuDboUR6inK8S9z45Qd4iT+g6gRxlY"
    "5Dotz8WfKXLQh85VnGSkuYV+vSFIoOCtgAKR5II55ofpgkW6BEQ6tPzst4CJYokKfiiBR/+cugx8UrIhaH/e934tdc/O/ZAsDOM0"
    "SFsqfA3IV0PPB17r9egmnux3prGnmXNLOCPeLwH+LtGCF0lh+Lxdy2ggsqEd3np6d3eUWBIQYiywE9RKchJtOQkyFOfslKF1d3IR"
    "fz5W/GeUgd2K2uT7PkXN9lQonDgDE0uubAi1j9FIJjFspIIy0A4s1NgrB1Xgvhb+7ssJofttQn+00Pc4HrCptufbgbi6YjQdoyGK"
    "bbuMMnSMVnLPmK54qCXDOFaoMuucd1jbFUw8WSU+mRWvUVNsVQet2b0TvVWdkH4GVZWSsAfE7OYZMCR43E2d8EVUrwAWp6k2wMGL"
    "VirDyYFzHqpTrF36bRZPbtVrDA+IdZqSUrat0RIUgJOF8SPIHKLQOCqVSsWt7w0GpoN2++j4GA3OYfp78ee3Z14P+sNZlCPl+SDG"
    "LzJTSL4ri0y6u2rQChRg3THsUbtolsP0qCgqWypo3awEyROvYMTtSgjnLJB9jZiFNnIwvtV00BpNGonQ3cQYoJmVsxQAMsper7MY"
    "RZeNPegu7ApT0P3sY/zGsxOOgsP2A6TrDkycccXLLAlCnhypUJZ9FVdbYn5PYw527sTEtu/D5YAmolmS0oWhpLNFzNHwWzaCFpXc"
    "lJLZ8Og/S0AiCwg87axDyWhVDV4wZCSjZWT1TKmLwpii+VhDsi5VwK2+GGbodNNsP42Hakw4mEdcXKv6W9/rXUc6MZnJ00Nf7EBO"
    "zlDMBLb+rdcD6cTQuLu7+QLDF0ncWuOTz9w+XbAcxx/nLA9kyZ8ttrgKD1Z1qGjwMt8n2MpRvIyuo9hLAzSqkftUC8QxaSivDyiA"
    "0stDv0hLxEw1RRtGJWBW4Qf56bnPbcIqGR6YEFIuPSyMKnp7YLh7OTfbznqViLpa1tPJSawijwZblSrSGOd8tvo4PTDxobh2ikVe"
    "cnwoV9jF2PXjA+a2Dg9av6TeHOug7kBUCYBy/ILyqM95OwZuBGOnmZNp/wCPJmIOYBu/PvSYWYlUfFJkbfhX+OPh2zclOCLhkKWf"
    "bIfVP7vFdyILtr66OWjJWQsNU6tAGcfINyBzACQwbqM9X5jYp+OHA88XvmV/3zAf0AISf2qFlxuraLhZmSYK7kcAKlsQNEh6QxEg"
    "7YJPKio4aK4wWZ4QR3aMge0PD0oKb4CRmIb1XA/rBs3EcJ/PATQBKFU8lOIR6mUfTzTMxO3xLFf7Zp8SYDkua5ghwtt5+Kv2h7jd"
    "TNZbrZRCOF4dIBnWqJZiKSr/+z0oBRMT7HEXaNl2Xzc4VZDdh3J9mKu0zYVIrkDzIrErGSt+CpmPpD0JY3+B/7fn9PJA2VHixE5a"
    "GsKkp+DD1QB8gei5JfI3Do3VZ/1WcneHsR1TevG1m4GclqkqOg4TVA5Bq2OZC+CmST2X4BM3LLRuoo5TSc5XpWfwKa1xYNbZtIM7"
    "Bs7+9aSdljBfyuJmook+IS+sacl8BMAMk1o+7LfXKyExx/R9d7cuw8BZ8/jn3V0f2LDclmO9Pt03B9IWAcy1SYXeaS3B5q6KOtxS"
    "P7Bnr9MGxKBuUMGDMUYxH9iDVhSpFzIggKBtI8is3uP9oIaMrp7PA5lPfFIjU5oqjZfAPxyNElGWM/Qc4JmeV4Wry6QBPxmBLcs/"
    "FruAl4TW34SNaCdDPOPCiR9c7sM2hiOFhE4NBOxtbJwf2JLiKlRJMC6O2otEBOSqgJJDOIf8xS/7XGif+4iCzvQ26a6ZAMX5eM0u"
    "zvFIVielfXWFvKi6GpFLL31JISmEmt3OTaefrl2BZMn6HAU16jk+sPw9l94JeIri/pMXmyCrFIwYlrWu9q6Db0Wj0GoIb4Lddm7j"
    "aZhksYdl9zlUuwPIvryYRQwmyEmMMLs7Gg6hwPnoaaeLoWB7WIh4EVjYsGJcfFC8Qp+ued8Y8XwwI5Z2imHSMfy2K7gzk7YIXrjJ"
    "3c6kh5ezr7S0zswwBwHNcIg4CBDvSS/wurj598XN/15c+mlx6Z8LL55RdeBCtwheOoqE17C+PiL9NWqEa7ocBvqz+opXDk0QNq4x"
    "fKiR2q2A4078caTgGxsxGr2iwnBjw40BzkGO25zJG9cOJA690Lo9AYCw2eloNunSCqTkYQdts/oubOY5OFY3xwxwBPSKGFNR8zkV"
    "gWw+CxM7bi+f1qilolKRvyABrgRMDt1cXWgr8+KamL/YjZ+0KrtCtRQcJwN+HGUV7gyn2pLbai5TheIOq7EwdwGQVOAcjB7PJ4u1"
    "x/N4ES3oTlHdfgNPIYxZu4TLcWPDpJTGeNTSfZvPodENUmCivqu34ycV0d/tMnXSVBnExvky+kGEkAmIJhp2ToYiYJ/MsBBlcMpG"
    "Sza8bHMGXt4vujoPM0x+Mm1Kx8aoPxhk5d035lKp+PbiohYBqdCcMoEqOkwtj1BLLw5QXDo7CNjmIsZh4rNfntnoeZS5RbTaY65d"
    "5V8AnnLZL+PBGBXuc9G5KnUsCmg/ougVX6PfllsUjeEU63UmtxnpmOGwmhXfBH7OLn59vaPEcqJupDbYBJwoEoeIDjGSMOJ3oYgg"
    "QGYXiLRgOTiqoBgPR9lb7/DA1/Pk3CDOxypaNB2Z9LBcS9hKS+wAqp5aaPBQxFZoN3r9H41avwhHtF6je3Eli3MJQijbxoga+rRg"
    "EDmgV92sdey1+d77fKAGs3w6RwnqisMuATGaxoB/pUZx8c+uRDLwZcDR1we4qHNae7Ng0dYKZV6QhhGaN3AI4r2T9am4GMSQLYa+"
    "OsgFQHbrja7a0egKeAy+IdHPFFDV0l9+VWI3kbI5WuF9iDPgZfeMy6M+A1GZGKIiVYQdAW4eGZInAPuTiSEnr5GcSBBsh4S8Pyjq"
    "CVtB7E8Db0ISk6yFM1kL/YAIzsRYNghNb0cfoide/0nFVwDhbzZ5GHl9Xxk8aEMKYzmARw4dFjgAk4ynOiT3rVUj66L4lscOKM24"
    "VToQtU9Js68BXkqBf7d0FXKEotOqSdIZZMjw03vJ8L2jjthvaHaIekxqLOaecr2fUXGvu3SIV/rPrPXSo3XHg4crzNFLZj7Cwky8"
    "YpzmlTN8H0rKmY/3mTW6HKtoqxbBL0XXWD8UXlGJgeNPq6wff8tfYNH1aO76SpkjspgCP4b96RQVSasME1faIlJL7YxqcpLJ/uXQ"
    "k59+yNdafWOep9tYap7XMRZcvxZq/4yJoGrsY67HqWXjp1pR1n1ttSRtjWbIJnqqrDHl06W1rRCU1KNQys+NDauySoTKUlCXu98E"
    "y1hadbOWVh+9+XIDqy80o+KVSsBhaRlOv6deBcpSyewjkL9eoFUp7CFVx7WuWqVl5lTUNYvbN4XQbFM6gw9Rlc2KcSnk43qe56ys"
    "llhUGUMqv9CS6r7xMocYTlcYXCko3YcI2sDqF1HRiw0VIQCp7hnp+hk1uS2hBkUH7s3BqBcrg0RLA27lonZsHIM0B7RIP9YfKUwo"
    "xYXOWdavpeNwTVh+QCKLtpmMpbx5Jiv0lTGMC+vCz9nxKLjxXDgdpRcAmmu39vWg/sSgwp4CaU6Mer6JlpiZWRcNf66NWf9/ERuz"
    "YlsgZQWkTKqW2ftkOMz+11rf9P+g9c1/nPFNvZw3vnG5d0NeCw1vVhjc/CiP3Y+Df2guIKN5+tVlKJTW7ZObTAEFIPnv2OAZzMBx"
    "8Li4RPzGmO2McQjohvtNAX+iKiQFFSZvCngWVaFfUKHzphCY0RsN7lSadKzm0AUBtHEGqx8ffZjSA7c9t9zsTd7ayOT2pKNasLzM"
    "WWHzyNZC5vhNoY5x+KZQx3ixqjvRcZ6/sbm8d3wgvcN3WZrRG9/Hro0Nc1aoAAeplWVGpEja7F2/xOi7dbHgtF06MiWP2237dcj6"
    "+kRx/dZWHpA6R/Ns4319hBs2TSlF7u5GimKqJx1o6nTQGXtZIyaA3X49QupISDtytNUxCUnqwQf5AtTQj+/u9Ie6UcF7IknCN+DK"
    "8wVp+KGyQCnJyq65Xeqcx+122f++0iy3hQjiZkWlv1LZIfJKnOYvQlUIRG+3BCNrsctq1zkAcRGOzIMAKoOJb9DYNbRTIn1ZpnsT"
    "DjaYJZO4070gjyXZxqy8N/TKAG/hNIoWpg+rYL7UQumHY3VYHLfzp4HdRDsanZ3h6yyjeyBEmAYMlrqjJMEoUHRThIWsNkV4i/SA"
    "VIKB3K6eA3xhXs3Ykir6devNurG6I42fpHJxylJoUPbNW5OHVcxy/VZD6u3HzEyOVmYDW3qeEBNN7pl76u0L8Vsz/SDEXrZ402g3"
    "0evhxYT9vMOFeDoaxkwLlD5eXhwOC4sz4N+3mn5wkSlAvdtdwzcqiSL/iTzpUTlXgz6GiuFMe1Vq1jtOJVOp6dxRDTvJrDPgIn5w"
    "bmwoT+inJZX4uz8mSn+vbAKsC8LYIX4bG96JrC67jYD182/RjO+8wIDMTZySbZuHDsfm/SG6kMN1jBdq5mr9WhTr2kohA4WdBWwb"
    "kKbnB54pEZwoIrpAWnFLZiNinET343idjqpXLbPS5XgU8W20e/tNkBkkKSOToAg94jyJ16V3G0hsAve5mwHBJrcGHK3zok/KIfD0"
    "QpuiC8liYI2+TCWBsICOM+Va/VSJ/uLMSQGjL5WIKCCgT9lYYaHcPlkGA0ql9Q5TXmOKKTXqpiNahbrU2+7/x96bbieuLP+C3/sp"
    "XPWvW8tcsJltYB9vNzOYeTRQt9oIECAGCUtidHmtXv0M/Qb3az/FfZT7JJ2Rg5QaoOw6+9/dH7r2OVUilcoxMjIyMuIXGAYJHFuR"
    "eHigDShdH11MER5J/Qb4YcLMZBZMMwkbqSQehwnGxyaY1lu0fPNDahFhMryJWAfzJdf6WS4DMXDO7yS4RkhCm6doW93mLnntOt/g"
    "6Emq9PjSHxkEQLbDI3xxFCAXjDAbhzk+jHNLSRev8VJidPvAP/PUCyzE/GVecsmALv62sKwvMFo4vgOgMl/acPhuu7xTRVP22hmy"
    "jc/CMn+IP325NF2wbqYCjKkRuFHMrRG/l4kBuSEhUAsKt1zMvsvi7GZeAl4u/wNmANf2K8CaZbCADdnGZe9+qWltyfBc56i8y11t"
    "fqRjwz/ry5LvC2WokshMur58MfMj+ZC78nW9A+Z5JfdqC/czlhQN7gBMIhZEbJqjOm9bk9ahRpmojKuC6Rnh2oaZtM1y+4f1Quzh"
    "K7tN45YB3K3BX/r7159DzsTbXB+KSNDoHETwycrJpvHB2mEWNGMWrLLJ4zA7TJhJ+AT+yK0+0Vxuxn0RXM+MxQfTJsj+vVXKMY8Z"
    "tnwewzZd9HiDCdM04u+H4Pfv+r8eIo9GNCgz0LbOK3P3I9NtdgPel8TBa7DzEOXRcI1OFDKYnDgh2eD8bBnAIXEOJSuM6jLIXaSr"
    "aGHqtrAVuYGTQmymYXUVTXvyGW9P/nLRnlw3LkJfDHtyy73vWjisKMZ3JDB0NRdnoh9qBAPkMI3ff+jkqrulXY80mJcdvsz7MaSm"
    "/3BD/WMoYraBHvUfIXvuoDM3ceD4iYGCMGya/iNMu4GLP2eJbrE951xkTU+/IFjGOSfLZ2pBsFYIPA0twqov7nuqYEcyXkm9sl5V"
    "u3jUrZhYBL9shlSENlgO4LjuWjg+h7uSjTmTOTvdB4XrlHPYdGoZ2TVir+KjFOq+S7OCAZhw6LNqoUB7hD7iHCgUubUdYV+rH0E8"
    "d2S+0Z5un/B3EwNmQNTxVFsHUKyJIQggjqXFbkYNoREko7ivUQGsJfRqj6aBWyNEjDm7RKKUtqi0gzJi540bCIjpVr9P2RCLlJGx"
    "9nACWzesAyx5Ryoa7giZWq4joQc3uAfniJq1BVz6SL1EqWoO1Dfe0UCsotFxCKHccGHMAe43OoiC/Rq9VDYcWSzDJ23ODt6dMXjS"
    "Bg0d75HiLj0G46Hb4F3sNngbDSSigUAASZB82hCjLAJsM9oQQLCfTj/keoIHxdFxRrV0qPQqN1Ry1UpI5NxjQASdHQ2S7+yI3Bsj"
    "QjLaRsVRIcj1/0afubsbV6HeNgIqPwKSbQTghHex65DhbMdjRschm63baPfE3pzchnMXcZtrl/WBm+U+HrYRYJxEqDo5CRySXDjJ"
    "wfQoV6qUfyzs/YZvz/Y7bvQbh0+x8g+XWs3wnF+Cvq9c0NuvcKh2GREL7KlINx1u2qCOlrAT4Qa4RXkSAT8dfoSt/H4VOVEnMPlo"
    "VWLING87lohpt39u1IIBc50YudHgjSRZUI8wEvwwwkvH5P2mZxYmSWjAtRgrE4C25FA2sqWMq0BgBl2taI/BxI765eFtzmpARw86"
    "moDVxk57M99FG0Zmn+dS4hhibhEBjIHVBYMWSzf+TOxSMcqPV6nBASw3VhtEB8ZCuwmaoArS5rJ1ITnJuTcdj6pxEuQaHqINB5kg"
    "4PmdWR65sN8Cw0qb8swHSBV9Nak6bKkMRSb1HAuHPBYsTXpjYlydfFGssl6hwgTK1c4wc8BW5RxtcV3awf0v8GPolkUxyzeY2cGR"
    "+7V3X/XacvzxoSOL0/RO5SSoadUwINuQTu9M6wwfXPrn0tRAAc1A/BOk8CGSPWtSel7V4d7Cd5NSEIWoIjpVu9iVckCg5hJdV91M"
    "CqmHFRgvcgaFr4ZBIWmsJmIXLWLCg6PbMSeaRwpCAbj3zPdC9zCbGWrB9eULWPe553QaMusuxn/u3/5zpr1sHhTEIloEe4sfaFTB"
    "0nNNUN9Joy+MObdePk8cFw6aWBlCbOfe5ITkxdGXODiWS/mc1sruqhUV/pI4s2Xc+WTFwyt1AK2eBg4iaC+cZQWHALM5MgSYiBMB"
    "hj+sccdTE/7DZhttIWrONpef/KDvc7bv1lsrF/N3ScR2ti6jd0Y3ZAzfhWkkn5bp7gurL2FTF1nz63Mxaxi42sqCr6vcNJ9RP/JW"
    "+bSz1gnmbcFppw1bfG7itwnVpyWk98vz3tt9cN4/aMvvsxIID/jsOLSzxjuM5L9S3+cb7Nn81b4ZO0iBms6j0RFwkaBaZ1b0KFEh"
    "9bjygbqJM4NBVuxm9Gj/cgfEYQY4lG1esJmeO2Gj5rCtzd3xyQzbKMsGS7R+ifM2Rpf0clZx4k9Z8IVlgquFy3vcPBtBu7G9ix/w"
    "K4BlNEWuiEVUNDrMSyyXCL66+3NG99NEAXj8txkaFikZOomDm11QYlnGh1wpGqMjXu58599b7bbVwSzifBcolWIGc4SqGdLo+qwD"
    "1z8jpwmTSZtIBxaeOpnckDXMifEmUWWs2ydVzLsdQ5gwbRfW/zP6kQTHQ77B0bMNxj6Kf3xe+0hjCrq1LXdn24KdK51NIfzRt3Ed"
    "wA+sqc80Nnuwtfb+bGspQLbzCGf3G9F/hAL/1qmDHTWVrQ6GSpNPHDu4zuwvL/bx8VOL/SdvkWriwJFYC0PbZRGzKH2pupqL7txt"
    "Fo/uNouj6gVItaobHneravWPBiRaasBos1m0gp4Rg7+/IDwafn2lTA0IM4ampoOXLwY2xtAQhhkgAOBK8lakbsIyM3i0OAhbUUOk"
    "B3IIUsHukdTtEx7oyUTGx2GwXhT+fkCSwiOmPxqt6lbScmC8K14LnkcBtukHCRelmEX9hUNMXyuGKBpIGEWDrInoFDWB5PFhdH14"
    "xJIQBccHnIxbUUZHNFG79vwkyB0/RJ/+E06XNGQDwz5BmXU+sxU37Ufgp9GOeDye8EKK5+Zad7yAFGyyD+YBxh2skQe9TSRV8CeZ"
    "qsr6+o3qWQ0MrbAPNYQ0Bsfs8xhOL7aR83iQlO1jQCRgroovXB02dD+CP0lcpIDHvFOlx2uHS58Vxsm4cCUYTtiai6EWGPCbNP38"
    "RSy+jKtdCzMqFIiT2zHx+VKvqc4En7zPXHm9nFEVUGWLMZ1uno6ix/TV24FMKp4515hee+DDbmOyeMO5+vbmFdGIDy1ufUfXxpFb"
    "azT7dhUGc6gXLbfxDD0QrtmpJgOvBdlD7qdtA8NeumrRRtbLAjTWskJ1COxqkUjfRinnRe5/ZkO9qMVgrSC4Xpd1RzYHBSeUJzmy"
    "nD+oEO3kwWWEmI7xp/1QxBQAdJfA7NmsAHaINGLgoMNH50NQcN+shg7LdPPVu29v3wvQy40AxvvtKkMLNeVRX9Z1e8i4Gfezqkhp"
    "NcNOnjaOQLqZlVIwt2WVIZKqW7Rv+pJmhSgTOISiTAtLogRJFUsSvY+vura2blQBXBvVkbN8ixPffUVrIp7Kd1/ZbevE4L/vvqbL"
    "UM4AtMS1pFTVxZO0ax9I9AH2WXAAltjdDmjGK+rPgLJ0XNwkUC5BA4Hh+YIIkK+egU2Bz/dzwPotuX3OhJFXS3+38kQxr/jffU/V"
    "cyiyfbcR6blO4cAij3Q0xNrdxRGwH77mDQxxbG31yMLzYKTRlq6oqARY+kVdXFNvLYjVriig9dGwOSSIaWMAk6Pffgm+vz+BcyeY"
    "IUGRlrK0s2X5xEdUFHAODy3vnZq7mg4eW+gR2vxxYLvv369N8Cj2DnMzw4A74OFdPCw5GARalPPHZW7YvGGUAV7EkJyYWbvp74HY"
    "gQbKGzh2AjOcToc/mbPGNTWpFU3jXNIM4DS3GIEFZBDOT+RLKc0GBYl06VsgFPQM7iKoPLTrgdhVlPXVLRE0coq6FvRrFinC94ak"
    "E2m9Xeeoy1xGmoHcFHzHsWkhKxc6RfyvwYDHj/7/fjVD2wIWTTDgv7ExI0EFX2le+/+3//D7hkOqpd9iiQlAtrAwo+wtXis6oMoZ"
    "Iwe9getUF7+BmYp2bZB4DEKcmEQKHc2gMqCVYhj2aa7l117jtfEAALvwQBvv8dwYr3T7K48/dhcRoyCPKbNbXQL/AAPRj8CoQniO"
    "uSijLyfgwf8GmRIqeCJgGB32+ihqqN/2LGySoFIAK3NME/ogMcQxeKUxEr6QVD/HEflUxGWNqdKJV4GKTQWnTHLUkJQBAztFAqY2"
    "R0P7aJCVkeRJ8Dmp7yWXkbzr0HSPSZgA6rsRJ0nmjgmx0vTHR/Ar3mATfNOQ3rqk8IK3HGn4mNYbj0fk3DAwmgdAPLkssF+/JiJc"
    "2F9tfug/KQ9YMwn9evOD+mU9oJagDPjBN2fv2evbH8QrBT1hIntgEYEfKdUlaE6Wj9LijDOfZIuAoC9/CHja7rPFTicYKddw3HLi"
    "S7tUgYENA4kgOr0YuNWf+/DXrw8BScuXgaQBX8/BzkBRQTjaeQRVZ92lS/CsJuKqe1yds2gJZpScy8ADcNbzvdBFZOVYlAy/8NwK"
    "pOkjIOjRA/mcRI+2xpGXeadz+e+HAPr7Xw9RMexwhEEneY25AH55AShSiuzMTHU/0CSYBbNBTlJ/fGP2uOSOiKT7CL3TQ/mcInqi"
    "o6tMHfrfyGnGoDKCM/EOvpeoG+Z+hEEEfXTVVxUd0Qc47pjIkPjFC+RGktlWJmQC/XIBTuSMr48MgtMYoOtPV4r4mbKCyABGvWQE"
    "QLc1VkC5/87be48Imiz+9uENo7fiZ2wNnBDfHeWvMdglfUtMtw+mR1bLXcgwXVAxv2PWUdT71CQQEdw7DoZC2tz1kYxj/nj4EnA0"
    "C16RPh+Yo5znnbJn80umfnjDgDmo0ANzAMM3soTFpmFlWKOcWQFQ7SsSbQqmpgIYnGq/k9ib2AKG5GsNB0KGS6fob1Q5UTOUEysJ"
    "Ll2mq602x0ZMvDUb/nToNAUwzZTS5hGS1AP7dcbAODbNW79imydmW4qxEkwpzXp0Zuaqyp+ZqzqN3bkDqbt118hum3VDC7OasNq0"
    "D2YnyJqxonbsqenV7gi2V3iomYsqnRzr1zycEb2CstgsWAGMHl3BxYPuyOKo/8Rqb+i4fGJ6LntgdfOczBQVJtQ7/ebhi87i3Fj1"
    "0bph8Zfdwc145tJVlM8Nz8QkJ1Uciwzt2sT9zhKqw3o0kg91FG7crYNEvhJ+a/VuyEXnYCW4inQlhXmvYLif89FkTMSnmK9d9Vj0"
    "URn7UuGgwH12eCrdLdJWrXoJ54xDnBdURFHYxdqAnCek0L7+ATM7xgEo34B1yThYPBMQSQq+FPjKVCEEhJ4z2kpWzedF1YJIU8Ga"
    "ReqDwM9YlbygmjAQuUFe8GauwQGG+zmBYBaII7FxdZ5xLs2jsrwYDYgMOy3H9zZLjK+3BLDcmEWs7wrBFZBzVB7PxwoaSpOV+IG6"
    "aUk2qrFURU8RzrpCrK7fIaDQusZzEdzWfhfuKPzRRcATrp6i8pKl9IuzxS76Ip+8PDcHDlzwJA0rJhiIEqVSnAeYFt6qnWZBkI7B"
    "H4k7hBlO4Q3thEkPaiHbrXGWy5dtq+Mnb9ZZoy9bTxlk8IUjA+P09sWNDNmQRs+MXtpjSHgEnfrRvg4IxoE9FQ30ShGAGFxLccwC"
    "lbZtk0FkVG6wd/gSwqHZplVZB8rNbA+NrdvtBwi/Pt0eJQXGhcrm5i4I6kkGWobefKU5uDAabyRS4wrjskMgRre5JgGv+EAUOcQG"
    "7atEY6Z+tBJqxmocK12MIbrXBiM085EAFZZraStjZAvXHZyRNLBYhXsO99Vpa4KJfAmKESbEcdBMGHDkgxifZ9guVRC4cV7aVd2K"
    "hMYhfbq1UL+dK3voGA57Z0PxKts3XhIbzw2j0WbYEaKU4SLBrkHeJ5evtKX4xOEuyc4s0/k5eZYcV0E0d3rlMEav4HhQbmZbfI4c"
    "CJ8cPXILQxPPysbyw9+Ovj7IvxWYL8TZgdXtqIiZrfB0hje6z1Ma2p6KEyQ1SlPJvkUZkQld1sIZp5EmleOzBwcNkHO+zUEVHcAD"
    "4DWUiIph31f0cMOQ1W4mWE/8FUkNX7eaeIPDNaGF+xX8arTtdCodEkNQEp+dR7xoHNMoyag9EM6A6EtIq8yQy4gFY2dc+0wSnR1T"
    "stjx/ZgjM9FFf4g0SIHnScNCArTRmBior/AZsjCtcpy8wOBvp6oTsZe8ScEbk+OY3BS1Gx/ILACwVQfU8adAjWmRTqZmsSk6J+6x"
    "zavA+7x1SM+UDZNEh5ZdXNCWHSwbJWyp+JhiHsI/BkHukK8Y6v256veClpygkySBSEjYXjEp0TxEPvx9NCgGUcRms8JrlKMZTghw"
    "3n3/J3dF1i90RtZ/1x3EeF4+3aWftmNjvcpjMDs2eRycb4US4f6H3DB84e8pPDw5P5NTF2S3dBUSbB0UNXTsEgwPI5NaXduA5T2+"
    "prx9j8WrrSqKE9Flqw0GfMsqZ5xgc83ogspkJ2kSYI19+cJcBBFXICBEcBdv2wNhOlmAAwiPiGHKvhDplWnoJqowm5EXcG47ooe3"
    "vTSBSyGI0xcNBTYH39VYWI2vg4HAbn91cxUObQ4eD1rsJgOk7YLYd8wj7A0UftbKHApARDPJKdrIC9IEdD+ZJNj5EJPZDxmZuHjX"
    "mcAkjNSt/YXLUnzWgDEz1TjMAY9vnxsIPiNabtXxJwtai5UZTYA+XJYPekHbaj1YsKbaj3HWs4MoXjg2uGnmWm7ak1KVwei66Jkw"
    "/ZAwGPhmv8XDdhFFASNDRKUeM9LdFrXl1VUvw4pwv3Tgb2151c1KMrQ2544m4qeOJk+MBzh2xj49tIyv0ww92IN1MV58Ahlfi2zP"
    "RGkPRNB2auv4r70iv8t6ePsjanLUq7oMfEkUN0xOc49tQBfdkITGxgIlW+WYmRpLy3YEtxgt8YWDvVLDxaL1arNDq/2bu62rWH9g"
    "xwK9fsEMRa67oG52JXF/xmbVuBEwL2/RIGKMeuOa02Mgcn750rvdkB3gj8w1zAsF1R5rpYHFn/XC97afi6oZh2z4zoXGNDWJmx2S"
    "YUGGe/uKHjU0/F+Zg8e7BSjjGy43t3A7wGM9OIT1M00tZ1VOcblJ8Kt/w9mc+XSrZrdVZcdYC/I/q8CE/tfPXqIEnWIdBhbAUDtw"
    "lzvGln7nLTzdPGCInvd8ZJgz5uyGMwO9jAFvBjYfBmusXbcrnn/Y78tiami8pXZ/5t2ERaXIKEis+z6+j/1/rbOQQXbbOnTcq+kC"
    "dsJB1SayhVhkB7Xuwk80HRiKVLfD/gJ0cZ3YS6IsNxuLraQGTgVK3c3+TDNT4TtdWolglTe2JuNl+e5b1S+Eh9jW7THZJ5BCJ9g3"
    "rbtHVkfnQ+jUzR76tXHJhF9i3GLXDswvtWnmaNNLnZlMUlRy1r6dtccrETTXR2vun75R3cWy73CpCS1buSgpbRtzMF51K7d9qdys"
    "s9yMWyG1S4Us7f1LOktdOFtbsX9Wdau5fqnmXN1mmomnWQJz1brrZll2TGXz3FSe3KYyZW9z163NBVca69SdTimYLiEq9POlbubt"
    "tZacA/zqHOAn+2d9t8b26i52zQOOC8yJJXLjbAtxJ4hZ87e6i62sDnLAzV4VwCpYzFnaSQCNkOiS41a5nDtvjavyGaWcA7jcbIuQ"
    "Y8bDNmNhJWeJMoOSNVc56N8zlt2gbUaZgFXbMBywmsrihHdi4mqYkkjwSDDHjTQFHgHrS4OHsaUx4880BuZQQTvdOcNdaMsK6rgH"
    "0GgCQwM+B/ie26dtNxtF1QGHZySsIBzPVp2hodtJqHCwWhdW0kilUWB0UcC48w8/qKoN7PLHigaW5T+GtCjwBjDScGmgmzVSuAJB"
    "qCbpP82+T1HfTYsYmFiITYkHnF30U1udzcOPn38VVOKFhX5AOFWaH0MAw10W+RDHraKWOAz//EH0GSHkiRIN28ihbdUoJ3sg/YHS"
    "WDwSdJKnN/EPbwo6Kd4qSwzkS3HAMQgdFPQOul/UF1RenjRxAwagWWE8xwI3mKuanV4DZepGwyii3cM9i6WCz8x//d7ymhImBDik"
    "9tbQBKOa+bVhj/XwhT58oFRGYYaDssOo26hhhmowhipgDBUWjGyz+iLS4XWd3BfDEBstKN8wDn8dIeKebwjatkvG2Lh0OhS8OfYO"
    "mwn+/RAUw4/Db2/KjJosXot+lITEqver5WyYsLzi7ao9xKL6aAHjBDuQIkXWHF4NTVvCfwUejaZhIBdEEwnD1JIZYuok/reRAnif"
    "7+++ETZ7oUFk+GgxBng/wBPgOAZerh+oD4nh//zf/8+h72CafVONeotrttMKm6X4VPOlDLwmh77to3G/BkkV/a6AUTP7QSy0PfAI"
    "9tDXwOmclte6+f7vB9XdBFt69ySs+W6wLfd5i2zp37XI9mFHP0sXsS+8JeXxDU0a0J1ZyrvDlFt6N1GnuQmSx+LjR1oIFuygGxwC"
    "5Drs20b5xlSoDCYTCsVzBqHAAa/a3fHwduYDvT9rlOHhGIBOm0S0F8Wl9vj446dhDAyqlY2gglsgaABEgj/1j9i924gOHV9E0npc"
    "H2vAEIfMhKX8nrj69savv9sZXoBWA2Df3uqHS/uGnWxFbFKtPTLrLOqa+tMwz4W3xlK84yyiSZR3OGlnW8y86B2rRCwf3XnODL3h"
    "dPCI3Umpjs/gTYo+BxxB3ywh0/O8LG51FTbXnxjbWnKQ0x7xGfGR0QH+dUs3XK81lWzgRMgQRNfRocUZ4S8eiVXkymuWScvxgvLP"
    "3LF//Qp4QN3hUwgkMRpl/N4ScuSM8bMRE2uvmRyNYxLUzlA/51LyX6919Cn6td940BDTMGuaFRv5XJ0gZny2VvjGrGgsclbm571e"
    "fCuab6Xs4cYELzEWOmsHelFxqoPpDX7xL+xyQogCnau1Z5QIsSNmLBHnGvosywCn8Wo12a5WU+umKkyq80iPQt1Qh/LbpB3T08X+"
    "gBluMhODl3/KWJZqIyzaGCbHuF8Drz9gPWtqnRXosg0VkvQdc9MhYcEGbuS7EccM5wFAxKJsXOpLDtvOo2ET6GJzKzGD1X8mSDO9"
    "h0ETD/K+oaaaXlZRNXafB2uwKbQtN2buwbFDnPpVo0o5UHPiCt10nIMRjg1JG6kfmWqTnUz4jpO5gFAyoNc8Xu+MHZGp/9/IoK1m"
    "oDrGdQbvTCWirWeEyH/bujeH2pUdkpxtI1pvNClEwmPNo25UZuNsE2Be0O4M64M/aWLSZl7vbCA+aLHmUb7IWmnljo+ja/4F9Q78"
    "T+/ClFEAqxxx0EdikmPujy4dw8H1bMOO0i412BJv8E/bbdLu2KBddmp2thJvuJh6JdEaT/HNNHt5TwBpswwWqkYH9VHCstEbhwG6"
    "78NccVNnJjJrZ5AYvRaaHetJYDHYJ5DbYlgD/NeCyAwug57/GgwEPHbuqCrrJ2WEj81nFp0PEGD/jcGdHH9H2dpcXE1hZA0pGRIe"
    "eS6BU5D86Enwo31ueMn3I9vXZE68ttStjJb4WJw8UkNKartPGRZ9OfS5f4SFeEtfZFGcaBiyYY32rv/EYa3vbKttKkhoR6YM65HB"
    "CF1ceeQTO0emBc2c5GsZG1JR1RwaSwO4cabphEeRJTNE7SLDPXLL5nEdN9uitw4fh4865javN/56zRCYiJTGLuX2O9vO5bzS00XX"
    "LTPIbZm84pQKfUS1Ka3dDfQsrUmi1xCtLAGOxYwBQCnsSLO75k929ATlAwdKN0sCSxG8sYBp6oytClTdZ2s2E3xwfKFfv2hAEc66"
    "bArSmNmWR0vD8JmWtxjg7n6hBghzi85Syh6Qb5Q9eI0Qs5q5eP02xw5sCb5wDtnHTPWz2cAMLRFAw/ZfhkZk2juu9k2dOJegfYgf"
    "c30uMUEdQjCRgaB2fjHfpG4aIaCf2zqzRFjbRW8YLxNj2WpyCB+s7B/IyjOmDA5Oxt3swHeBfplZsGZScMGgYKzgJahBe6v7l2sR"
    "mOx8b/uEXR7zGfGGyXGZFII2D0YQ9hWyd3U2+8060cTZx1bJnzfYdXnsnQ5QphENNuD5alzNfMWRzmWRI9TpSjyg1JmBX4l1Hhig"
    "ElQeO6LpYGJLMOR7sZLUrG4YAu3qH2zfytpAfkXyI7ocujTdkJ+OdW5xUGscN9+rERAu6QbnaWVV5fgt44+XIl6IxCbHhiLEr4q5"
    "c1WgBQluJZdXhYEgdGlx6MrGXBba8beMnXUCfcdI1w0Z6nC5zb7zHBgV7OPjMFndTXjuS6747cZbB9N466LRVqt+zmgrTfQHQD88"
    "aZgXSAZdE9NGfm5R638Eft7OYHotXDbi4Svfc/Rim/8/YnGagnFP6TSeDO6mLY8X5hC+ujSJbecktnBFv5tDKPj/kUnM2icxxWLB"
    "G1HgMfKHJQY8TjEjwNNj11iVdGmMNgMkveE2nQ3bzjcgAw1Ywdb/z8wjCMupozmVLesp1zmXXyxy9q9f1t88a+dtiWv2mcW5q6a3"
    "rKn7uDDL+NBAFM6PP36ek5p4ID9uxj/CjWvX2ZbH0EazGVnyTDlZP8OSF+6r2FKk61K+do4gXtLsRGhZ1mivqtQtS7taJyaf5ur2"
    "iWeheTlvtNG1yPs7273RPklaFgsSwHxw0hrWb3My0evOfqa3KCjx6foCM6EndJ4AcpxStlj/NyUa1lwin1gIcgLAjADLWJCvT5xk"
    "YqGlLQT3tIkklraj97x84lBlsItVIrHYP7WIL01EoT9+dBSfPdffgZ8Ae409pNAElk255lQ/0y8COEl6Zso0H1xA0Glj3aRchJlz"
    "vbSupa5B045uu4s79mwuehUm+/ic6ptfv6xp2ODid6vHWqX+88wy8kWDITo52OOXN86w18u94yeOHW8KdbcBpOcbfE2asemmyEn/"
    "X1ZV6aOjiJZC0NwTbl/TiOLWMmxKKlIK1vUzNT5be3jeGUppx9EDRdUYFIRROaRdEhOeXU5tmFn8Vk7ARX9OUPgg1eOwEibp53nS"
    "L5lbxq9fDo22nfZf3fcRo46L4iDuoLtAiNjEk3Xn6LvtHB8hfar0/O2+8dN6rqjb542wWE4K+LOthu4nTWM/MRRq7hA4zNjm3WcN"
    "jnrioFdcQVewPd/cibiinUNcMQwAjYuk+TvvVU6GwTAvMyRK42pJ+wzuCnD4Xt0eIZSDOzmjFqT6QI6zOi9/uPXJqwkvoOe7Mksb"
    "3fhcN3OLY7hRiFPVX7XpGX57Zc980x2e9zYRg2x+JB4oWiOsJDpPdvGWuENQlWZ26WHx4O2fMSuIFYscYrmE5K1PsQ+Mu9tCGuLc"
    "WZzl2N3T6naCff18VhtVbNI5vpkQVNS3kTI5QnlwIysAJhelkJYNpMVYhtQ5hy7AS9VTbnamEjagYs6CLmPRcZznjnhvfHSJpuuE"
    "zrVwZqpucwqjqLgCDhf/7iqU8Ls0DsKn56wOlCZIJAmIB1p6030Tw0wS1f0lhBlykX3J+52/BbBiS/76FfCBy50y8zDjNBItLMg8"
    "2SCSmOezCxV/xK0SG4KOBa2COnNYF4Kcs6AC2cLj/AldMdXiWdI6iyBi2+g5srHs9GsT7J2YRV1SD1D2G3BTE8C8iVaMSSqWWeaJ"
    "clUYGi8GByBqbTXneuT6+EAZyI6uHIDYq59lAK6UZLbvzxpEpLI/ao/CUy+2uLQSu0KbiFv450yL3tn/SQsti8Wtcou3IxcqlhOJ"
    "Gk5RtsBLA6YcLeXObUR/r84FNQp8EpeJqvIVlY9TYoLE0Xq8D6HAxVCZvksb5r8TdIm0jxo1m37HigU4igp5zPSZdWN22YJn8Vkn"
    "M9NX2Rm007ZRCTkHAgXNeKssHwF653OIFMJvo7HbIAgsp1AqUv50cQX86XFG/PusHyXd2gwEKOfWy1557J4lLmCJ1CGReuNppsPK"
    "ZDW7gf6Dn5zVjWUqiSvsKIeSccBdyIoD8oKDnGsJE4tLS1qRp5K6ziAWrsw4txbDAl+HX0hYySavD0kaEBfbzbHQLNRgsIZee25x"
    "1Sbtd01rNgaHQPLRXy6QCPAWD4kV7oCQO+rGVzLudvCDyEXwA/C1Fm/IAedmoyobdF65EAvjS8CHNS3iBB5dlGYsPDAOxOdxRVfQ"
    "PwGYwJY99F1WHh/dURJc28uPC41WzDGzkBFAKpv0XJMKLFN4IfaWNdwyGF0TMoInk1NBiUdRs7VZsbSX5CIWIKYlCLm6tXaAECOH"
    "ffKFI6su4QOqtL52g2Fj1VmhH5znHbTHkC5grzWzRw4XQDSOLdx7hjkx0q5FC6HzLfr+nR9k87UHvJZU1DYk3jOfcrQXajm8F2Jq"
    "p5zNtBjJ8Sa2KzMnLtV2H4NjxrOekJXv40KD25tzDgnJ2PfsH9jCyvMN4dItWB3nAoXb457jKNAfQEmwrlwHXgLHv0WDf5/hN4xB"
    "m1zmKyU6c4FfIOmvZPFY855fsYTULfR/jlVQPowmImxZs7DRujESJ1FDtG4nUbkPL1M3WfoOv7nuYbRHEvvNPuCwPU1z0MinVq0K"
    "djBIOMSPGsYHl6ZHfGe3yYGf4DR3XZiDF5gOQTxQcgNiBDhS1zkcOgAWMeCeddRVYmfJc8tevWxVRP/sV5tGL2JRjEBvyIGBenzf"
    "LOXCZiKMcdQqjEkn4Os/ZYYEELStiBv0KeIDewUAZvWpkGCueI6SfQB1vSJlkA/gWRVn2LVxtgLTXrSWAQ18CM2Yk/6NttqRL1QW"
    "9xgdD+WY5ZgP5wvJC/GWCNYPalfAAhefg22Zeh3YYhBgdmTG5Phvfu83HJXjHclbV8cc9eCwTVfD8+XhwZa2yRl3ZiP2WeNWQwfD"
    "MR8B/tutObZfUMMatzA/378bjyjvOnfLTazHd2DljXLMB3CYcCkbvBnY9IMtYwon41AUlvS2iDXr5gC1cqZzLrjfIHIzugNOS+L7"
    "Xzo0Dq01mEH66gFlQ8uGBqUgQXuvGz6cCjOIlxV8gB7xxMHzmiZb+3ip/4/cT0y+fHcw7C0RGVE2HMD5EyUTAdugfmM80rlrz9v5"
    "775/tzXp8dqlW/DCaBTUhFgvy8Z3Ae13mkamxMxuxO4wG7WHRrkVAMca6xCYy65puH1CLrRoMc0kiHcpWLn6UA8TuJ9MWOCqbEOV"
    "34waMZmhc7EsowknNX77aIWERPnCszkc8ebt3ajizeANRmVAU6hccALxwfOLstUdb2tbGDs0jKgR5kvymwziD/Hn46PxBs/Q8UwH"
    "8IJiVQEAm7liIToP10Fc2Avay+foIEctPLBfI9/LDO6l581YrqKPW7Lfv38xi//+Xf/+HYbc/LoGE4CWD/BBcOmdu0w/WwJkoxx6"
    "LMvNbC3O9rIlmfgWLqEOxllQg2bG4zV7hKrNkjQBwkLQiWX9ctAROoPvX9AhH4nWjVvj2YexjF5wY1A694u+WQsqRLVgr8hPH9Ff"
    "vUCwkpVwRG+tCT5tjioYC6oO7WHPJKbgy1hZbdeyBm/43z4kH81g6SWA46H66M93fE5lqfj53ccqJon0F0pWgYpYKv7xjoW7l6Uo"
    "bl4A0gvqtaWgzWuPaE7Zw2YNLp2I0IifoDneSAiJgJ+mOU1JmCZuOsnxBU2koB3l8ZWRbwH56F53NGdV2AuSfrVEh1ki1REKgq4A"
    "PDwD09NN/mq8wtFzfUjGs71AibLC0qB32YlEuQIV5b6gXfjxSzBxDW3HOFxGKys5GsIFnQhQf/Cag3nbAV4EftG7hecHkfwD7ynB"
    "Dx/NR8BiAlmE5PrC5/Lwo0nd9d7RRvcGhCqS3WxokLFIyRilmazRpGDxDAWLPAUTKAIce5UnXjNQErgzW6jcmvHdTuaijcxR40YK"
    "cBuT3EWT3FE9aJlaaV600jzKEnoMIXnfpH3EtNBXBFASnnCQF/QvQNzjKOTikHaJfvLr19u7sUbI1+Otyu8oODvOQPLi37QLj29m"
    "59gySryxPHgFoSxkWbEEMwOq6AVkxMc39pQwE3G2vXRCpIlEKzR2+NGxHEX7csTj9g63FuSL79+rwIPFlSZeITpEMjWcy4C2dGGE"
    "b3IcFGmjZMJkX8iFz9Bj8O+gwb+xek8kbBqEOZ6fbzdtHFkNRxyj2Bgl47hEMWSzWCnI8XooETA3SJEibCoalq2Hf7GemA00dy6j"
    "kbRFIDxDDoo9/+0WRhY2EtiXCGg9yQCbI7yHI8EDOxJ8u6WHBfjCLjfAnipOyF5t33WRaPSNFE1qgI+nwoNZHfoFJZLaxjh0kL18"
    "EW6V0vDqTPl05M0hNdtVlHPUncb4lKhdPS6jB4KNMW4w8xyj8YkOsRzEGzYsInvCvIeXLL7ABLAewvOvX19EKuA8DiV5mDAH2SQh"
    "u1CG49QZibKip410QPk7JpzdN/yIjK47dM+Me+IX11ZZ+AEOV4ybYgmUl3+tggrXFkaeBqGi6i8J3B8TsDkJm++o0QLWV/MrOsvv"
    "HIoKrP63lxyO3/vr13UteT2Ex5vZVsK0ZT3vvOR89OQZME6e3D5Xx/scLQ11gz4BpZh7OeE7Qx+Oz0J40ffvpkQGAhpXZA7al2td"
    "kyBT4kOxdV3JGU71ZqmqKEyOcFL+gyOX+xErce7Y4jyLEkHWxyskGHdlHNXCQX/9QqlOvkp4sQ8LRyJiyvhUXuSQrkaAPZZzooLh"
    "6L+aOsYQXk0XNKvRDXrLzD1VYSIpGKDd3UmelnNyLUfZwEVB6sK7LrtvQIMNKGY5ggEG6+GGXnGwaqUdmCZslJWEjTI6boBdxPzs"
    "OeeGhZbPuUD0jUhs33dfyf0+5NU9+Yk1G0/pDRzOIHque+Ye7RTJSxQ7eNAG/GyxhjTcC/nmOoj0G7H48OY+SnrxIdO65qHHMDWm"
    "Vgoopm3gYz+oDY6hdCLK+WGe/HxnNjrowCTJgvE6jX+9/7SClqEzLKcBe2Oqsm+3WN1l6rqAr5NHpvP6dkseMNtlL9G2SdHLAMUC"
    "b7NLEHe34zFabEMaPh2zrEf6r2nS5ghyb1peFHNMk17OmbfK6vj2dQu6A+ZHYejUmzkebJ/eUeayLoHdGh52/vuK1dw30oQuGFMe"
    "JHOCf9+QzEPqMc4Jje6adonTtGdynmvuAzhOuCNRAFLEjyC+zTEvBgglWxr27hsazr6+m6DFADL1Z50mzO9Sj2mOc90NWrtLc/+u"
    "r+FzfaVaF98QqwKv0itlO6F9RV9yPcFslw2Ge2gZWnjXSkHA0gzioVdFNl5lXg1JRF8/0q6vQZ7HF6H7HL4NQv+QNPsNkOXaBmqz"
    "XtigHqDEs+Np3umRjA+m/8foBv3GIKdIrlbsAVcKc4+5ddH7A1Cl4/MEXGpDQN0Ejk1NefdE1MaqNKJ7hoW5s5gctet0zvORCx8z"
    "TsbZO8bf4u3C7Ohkf7aYP+C0yyYP/U+DlsDllME+Cjl7MEQV/VrnPFjo8hj3SpACkom1ffzI8Tf/FhRRh3ciZxlau/7mIXI0ImrJ"
    "Hm6jw/O2Z5OYiTRMOThneW2PVojKNmR4/kvuePP7MBz8PJHP6Uxx4Mc5t3vbjwbHYBcmzoqgneQQxuqSfkTMWzTMZJn20+3KG64Q"
    "LSNMjiXGIFMeYEWPHd3Qw4vBChAPkN0ve/P2OSEHNKqiYvNCB6TEz6bFkYQeCmEf5mYEcxILA0E9IZv1ORYSNQaHZUVMxMkF3Jf1"
    "T97h4dVyVf1k76chSHBQUAuX5hqixLkW3/EtNmQL627FyXS+qYiYloAoAUxHSOzQm7WgLbH1yB/1tG/pac/eUyL62CGv7P0kuc72"
    "8p7vJcn7YCJk6f8+NpZDlP1ttwc5Ew/dyq3d1yG+1uDNNxiFUR36r19fLHN4OXAHZcOmFSG3FEMXliISICwWG8ADcLVYE/OG1Wz4"
    "N9ayuZlo0MY0frcYTQ3N5QUJFZ2d9xg/71g95ViOsngDFus3WFH0gXn79ol5I5dHznmDus7b27jFV/l05BeTYcetK9xUwbnZKOFM"
    "+lSwWXpbzUHPbxjkHs1SfTBg3TBYFjfbT0aVxmCLRbpF6/jm9ByWm0po0Cox0K/OiwUWi3JbQGYSYI63OqRkeQDEuzWEdFhZ+mDI"
    "GtTeHZty/PgxfHnRxspGLBoxPnc3k1g8FgmK8eFPiCpQdFFIWD1YpdMNETTefWrRdsbfnyCGQNEG+I1ThaLboV8pPlgXOc6r0dSw"
    "JXVMUyOW1BVNjVpSt2Zt+9PNRNENPcVcmkxEGYRJdQsrbEK/v3MBFp8WH+58G8cRHU7lz1Tx5Ron5SWHGdCXh4fgr18jwxxBtr5G"
    "EkiUs2RQrw0o5+/fr1l4h3oOTIMS9BPvQ5BTp0lE2wcv/g58/35zQ3+YBpuCx4hVYotWVbt+QSIsKPTOhKtC80wsp27Bixcy46KB"
    "e/D2mmYMq8A/b34JbdCWEnZocZqC3l00BbXRLJ4sF5sswTi3vmFPnTpiCl+CHwqDxaboEm/6sIRrdtW53HC6wcMETrFgtNbJvHzC"
    "D6ZHsLp6YsPHDTqwqYzl3nxG5oeGjhzhvBh9IJoOODswomaWlAl/KoiXbAHghNrJjZ8BgAZJMrnpNfc13c16HpqCc7pHHFN/J6P4"
    "XI3x5KIhK0BTCG8Ev2NzVLxB6m88LVI3JuuIWY95atE1/hcUHjCjT1lKCFpLkIogFOhF5mMtWJsYPFNKyFqKcr4doTMlhK0laOdL"
    "CJ8pIWItYXy+hIhgHqlc34/MKixlrkiZgBdg+HEDJoCjhChXg3uG0e8yjHnXcbdWRo1GGlLGtugEMZgWARjEAsvAIM7gJlu8CaKx"
    "49g0Ywkh093eSjA4DuAoZ4mNOLGSCWdvd9bh7Q8tec9LI8GoGIwEQmEsjazNXRztsxCTp+gawmVmyUdjfbwUXeKO0I19VyQq/5Wy"
    "v5mDx6QjqNHRWeSZi46RLecOK+b2Itb8H4rOAC8Qu6d4PppJ+kK799a6ViQMS9taCRJs5DHxjM0WXaK7ZC5UXivag+EsIWUKroC+"
    "pLV2TYBTCwTycaul4iipapZUL9rC0OTohKzPTEfRfeLLbhPfdB/zkzUvvhsENV3KbFbX/cvCmS875pfPrtJt/txIX5mtLbl++eoY"
    "vSezsj4dLNjFbsAa5Myg9dxGZ3CJXBvuA/DtAsWIZZeIYXrZrVNy2d4ptWx0Siqfr0Mo22M6oZbDsQ2JaWUX2tNcqx+frcHus7Uq"
    "u1xFkhHE/4ILFTpjGK3CN7bCTrzZz49Dl/ZPyg/W8wPWzdsCDOXVa7gf9/gGONKLeRu+lV5WgjzbCjPjLkZEYgTFy/8xxLe/L2g1"
    "YmAJ+WWrwcMOjQ843w0NT2PfkHj7vhAjFLTZoE9w3DoSjd43xDiZQwjqQpG6iAkWfgcnegzcht7rLzJkRKKUKrzgG1AN/xTG+gv1"
    "14Uo2iQiJHpELULZABQF1apKJMCwsn+RFV0a4+hOD8TD9MVoNf7FNR3/trYfJxnV4V+kA/gRN539gBt/0ciFe4uIzwgVgz2X4R5D"
    "VAk4HTFW44PFWALFiDo1b+PDxEiG5bzV9A0UzaSCx+FdJHA1GybcsrC6IdN/GSbgb3BgJ19ABChLQAZq3gkWZNb7r4ZhVJbg8tzq"
    "SmeDakgLmnjNDC7e8ql6Yvg//vvQl+00E8P/+X/8X0Nfp5VJDL8NidWxCH7eELSB1W3alNksIL70blVxLMJ0Q0BPcIbEZl6O+A7Q"
    "csMeEYJtsEgLZhh4VNq1+PdDwEM/fmNh49EZETa8xA9EL4nAO6V/IyYpjd6gG9EbIDYD2FiiNlIyMbHKv393vv2XCFeKqm6EZ3Dk"
    "uHF+xAX/QE3EgUDxKhehPQKsmEeKAlGiV8DU1xvbEtFPwKw24azu3QjWYI5BkIyBjoaAwQlhJ1IWKWxM54qa+qD60XrTrpmNL+86"
    "sbr2UGrSmO+t3aVE8/pnPghPZCMg0FCIV5J8xcr99cuo4oG3KfYhQsKBP1j4KCRC1mTcwgk6f8H4QOCc7EqEx9SxOEFCsHq8Ievq"
    "8RYf0iDmlan12FJtyxsUrYN1pfz+wOr7y2iFjM0RJg90Mt/ON09HxPB3gIL+SvJ1+C4a4CNn6B6IXfLumzJ+gbgBb2rLswVYa+ar"
    "N7oODTtPUCKgj2ejjWGd8T/++xVah0PyQtyqxgu0Hq/QwqRvttrEePPtCi3TIaAYb8wmkTt6EAm4JsG+cUvSwO5URWNsJH97k2kg"
    "HszBTOsRUbaXIMpD7v1Gv0k17VlIogcatebHnDI4i/U5HvUvX3Q0pnOjA3gPJZZNlhGlRggUYA99jEoynInALJn6ZmMV6fu7jxak"
    "ioqKzyOWwlgqLU05GvnJitOGblzegPfTzfyoG3DNaM1OE2nuws7IjUVGO6ngNJq3bealg2TLzVJp/iKXX3XkVamHCM5aMbMagWot"
    "2VkqzT8w89OoeNb5wGk0737HDQjcNVuJQqe2+Thvd4eIw7T0mdktfdZFcpPxesBqKBr3ZM4UObKwswEaosbQChyqudr1kR1tLSA1"
    "AebJb/jM2CS/C6A1qLqtDFLeZMijY/BICbXrA3eiJmq3bZn4aubskKCzH6HAP6Wgc9MoMt914m1hUyvaXchr14uPXtpbDDWAIMCn"
    "xnqnNMqZOBa16xn65WZnYkrMlqYRHx2zYcvcb0Ipi8dPolwYSj0T8MIWTNqp6MMkOqckmhl5fDzDog0RjhfDbFu4GRkKfJ/LvcaG"
    "usRt5Z+K/QPFgpo/T22ALWPNWQfTF3jDRYfKo+2tOR/V3xDK+eGb4eszdu/Aa55eTM0TtFdirSVLhq5jvWiGTb8Q8hvNrzm2jHC5"
    "GTN2Bjprii1QiH3KjD3DHSpkNnJZE+DUgsaaGLPNlf0NTnAvYN62XyODaZvhCeZ+lzzjLgH47DZTCbNu30iSEaGc9dp3N47yne0h"
    "EuJbIMOzXoImDQv1aJWg7cSak4GSuXU/e3DpvumydK77Qb77RnZb97lGIcEuQc3cgwHfV3QivcHnZrT4v2LX6+10Kh0SGBnKjVkZ"
    "msJzw2caYO6sxGz03+6mz5YOjNeQu9I/Fk2Q35Gh/z5YSwU7BuxwhvXPFCzokf57S48L/BJLu36fJTs/t87sgblMpTUrXH5kyItm"
    "OWly62Fk8b3NbDNpgquaX2GQTLesTKkOOvp90S1WAasJTkMGCGHUcyZ2ATpicfYd7eIZtOssvLDGzOPRwjggM6Ojf0f5Qc64DnIF"
    "sKfgRsj46ib6bleqOwIWtFzLqiotuoVQbNELnNDJ+wwpl4+eZuN3hsz7CX5Hv6HhAF1hKyyY1YZ97UUnhq8XajgffYYnAQ4cT7zd"
    "+ewG+qJO3RxMg2k7J7J5655jRxZjXZtyx8qT9nC2vd29M1NrqlkwpH4W6Xd3ztiWlcUFIPPZDaiNSt55ZP+4b1nkyRiVXSt+ku8b"
    "fMd1kimafNGBNTj8j6AA/2H4ix/BO4vgi/s5rJeTV2jt6eLVzVVqhW+Mb6yGrAtYERKzpgh6fh+F8DfLgR3iHPFsIOKDY2EYpzt3"
    "2Y28vrTVuW+k+LP/xJVjq8Bxtfgj6Av9pLeL/Hr5k9VidVM/t1jCFtHF4uVrXSsoVSOqIItfAiSbmvB/Y5mY5eN1gi/SOakZEJz5"
    "w+ZeIbCpVbyKDPz5yj+7hvjpxgGs4MoJ9/gNtcBlnOHmHvQu7vZNzvk2QrBQHFlC7UT6dSUES2gfY7zrRWMMQp9biL+T0Km2hK7K"
    "ti3KlH1ZMj2K+6rEbwsMw/fD8jt8VZOZcItd3WmzPiHE8xAR59ZChF8L3Ae2lcC34J8W5YkLv7WvNM0uy5PkT4vzFkCMcyMRdY4E"
    "RSFwGwrWQCLXr4VDIkrF+6gpy/+XoYuk7ybdrz8q2+esQhk/Hr8R7z+8GriTQNGpbzDkBLo6io54I/b1YWoO3VcIfX9uUllbykUj"
    "4EHTOgi0AOyQptnc8U4utiz65zcbvLx4IpjQbcFYCj4XTzfasB/iT4JvQSEIUerXxDkjbf3h7zVWX/OqJHMrsYaNNsrDChBHaW5b"
    "zsTcb8gIwudGuJC4L8XtLfhrGPCu64AXRGFiH++Cy3jL//94nx/vjn28IRSH63BzIRf/fGvDynq6dCuXxU1Di39m2eLXxqq16r9J"
    "P0q2fqiWPti1dM4D1ZgeqIz4OYZCfcbwF9mtuEg2D+Pq7sLmYAsP/3fgUSeRoi30xgriGDy+l7uguRl6ub4KR7ikOCMSw9scmBm8"
    "rcGUwuY/yXLJSlNEtZP7orPUO8HUa/hJshR2BU1DNhsxsmkK7rHnbDx6bgWQ7mF7CsNwxulx6VwL7n6Y9J7g9yrkMyOnimtlJ6Jj"
    "mjF2TnWpPQdTHaOhgbvby8r8zUeV+ZbhYIvPooWmEP/hELcZY1sj4wTsG1vDh7rF5cm7LCIjtMtZz2HDwMviNrg66yHMSUxG3JUz"
    "chJzkWM36iIsDtKBxDAUGfI2UjN8VHQn77Wg1+fn1wh6bZwZP+L1y9t1/bnjL6pYmEyAevgbJat9wmUC6u3+9DbIBaj2U7zduF2l"
    "LRkY/H0M+Awuopl583pGpSDtxKooTkiw7A+fXhjelXmAwfcALPlTRxj6za1yXnC/twju5gdudxFGG/7pQwxzCqCHGFTNDU36k96S"
    "T8/2OObaY/KR/bTCtYSTnvjbUuuonVttVk+ET4wMIIVZxgUn/MmowIdnxyTuOibwiduI4Db8vzMeAA/3n6NpYyW7qFwIGh06C07O"
    "6Fj+QNlmDBLUe/6iLOA6MfCNbWIgyaJtY5lvcMeYwu0P5sqhi7M6/NhldrMh79Zr4clK5ET3J6sa7vWzajiwiyqJ4oYtDsOc2qH2"
    "YDkvKT5cl44Nr+/8JFmuM+0of9Zp4prJncZclBo28/DfKzf6VlHH2uuP3l72uNvLgXF72bh0e2knI/cw7qgUsez7gQbrnt0e8AAX"
    "w4yoLV9q6kxAvFZUX+pYgxQcGsYzXKCSIYAaXrT2MRkYfHDb7FSrxWreavgDFxmxsxY8xBJ9GL7/LxxCD+qDXva51YMOmCA6vMlI"
    "bglRb7FwDEwdvLZgceYn4hSE7EnClj4HcXSeCPnWiWEgAjirbsNM9qTLQRFtBU/IdS34pyeGwWAiBIW7xJ7zOfeAj0TBo9IQzl+b"
    "ooq2MhKbh8lK6wpNo4yk+XPRSO1Xp9/s1EZaUsCq8Y/cnP5O1KOGcVTQ2xuCnqICfKyL2Q81mnMX8/Bbwok+IeXhr2wiHqnnM3Ym"
    "2EL8gnAXtNxssuxuoh0dk39YriNWq2NQX9qYMnvzO8Xln+/nZt2u983T/4z7ZsNk//yMhJ0zAm4AtquzrWq7aMY5b8Zblbtjtu/l"
    "bH7/oY2ca4TtIlot2y6i5fLF3eVP7tIsPeKtNISyM1wpCZmGmG3iamjDT1LAgpOGp0IZQpHbYADnQXMRp/x/pNJtyLDXNDYFrewb"
    "gqp2M0cs4qWlC/LkNryeAu+LR27DVzPGBbkqbgOxoc11FbVbKlvYGm64jaf9g7dwxKCXsriuMwwtz+N4a98PsjD8CWmkZWnj9PkF"
    "QQsD7ti1z9/mHgM/Z2MoUP4QReerWxMtdpNkbM6uUPNST5p5rsXzej7aZLv65I9WAkWjBYRaCgJn4NO6rY15zkMRl90i2F2yJsVf"
    "0WqMUjg9HxoAdpfHQ7quREETzcjN1ih7VgY6JoQ+z5nxbX5jAH2xwfja1IgxYBomQ/kgCXLGrbXfGRun/jSknkM5ad8CiXi4KtuM"
    "B2cQH1XQ53ZgP/TmBdLfHZK5zejFWh0zrEcZDIt6QlabIsOJmZruj9rmRpsT39CNm/sk52u8Lrt6IV9BETh+n83MG5ux0Vfvvrn1"
    "6w04O777ZiiVbNe6MAKwoJUr3BWuTxgRfEyQf16Mtn7ia6aNe/ftDM/Oz1ROZa+jxdkzudk4QGLcfOj+yqvXSEoGr5n3hLwHP9An"
    "4idFogn4MEIJfILDBnz//i0NAU+wExzDlendonbgUnFTvn//0k0TXghOefQd6yV628N2w3WS0BZGj0M6gAmc22N4SPYuRzKQmUmW"
    "ZHdHouWZbiGI5qi/HnMLkbBHj+HFRzXxbwSN1pYMOPnvNLu15UaNThcXqNLh4gKFnOjg/B349SuVZh5FYIEmYwGdfmskoA0J6v8J"
    "Dojocza2Zt12dxncWZu7DPuaowHA5ucKYcNqK8cAliZFqUcfapiqJd6sq4pmuxnp4A0Ftf30/GWLsyHgUI/W6ew5w1B8/95ANJa4"
    "dnn16xcJygEROwADNQ2bHJCiYlCMI8STBcg1YeLXgvOi6V/KeZIy/096ZueC99ChYSFSWegPbAtsBOJ8/wuH4sBYw2k61LLyglFf"
    "rSUT9daFMmWlo66A5MCqn5br8HF1kDAtHf1zvnhhs7kFtHMcBhsfrJUZDllOa4AA2f6gGAYHPcPVjYZVvdBgKJKEBTBbTVw9e66o"
    "uTSyGAuPZYDim66g/9sP4eb005v4b/7/5vdLPss7I/IYDs/2wHULgKVnCvQJ/WPrkq+HxnVPO/eXdUaUpWv3xMchqP9AYP72pr8P"
    "E/r7O+dSpthdyqZlctI6ok37jTrfQ5+BP6BVpyX0RxLfJCExmdEiVzKL4q+Q2Sobwpo0RENXOVBAgsRaUJemILFowVZMfM1Yqm5z"
    "F9uY+7912buZ6AffHTF42VUZ/uWu4WJZjPiSbqF2zfPLGlqk2aPzMosJm4/SFx0QkXseY8PAu5WLlulD7my/u5GmtD5VRXz1YzmR"
    "WF+ZQl81jVH/2AsL92TJnEDYT/9GIGzs/p0Lazfp8BOSLielIQ5vlXyJZwQke86OHX1tagG+ICkz7QEgNDxOFD7RMbDwHdG7uHv2"
    "7dz8+nALzZHt/W5kPx292jLCnJOf0zrAR4RptgNzRPoJ+LbfUadt2+YH0fbq/BbOjVfjd+Ol/kOmE+5OKR8Icf7RgcH3tRS4d+i0"
    "IOFesd4rhrubeaI0sr3/Zlzy/8YK/WlVqsA+4LBKMzcHoCwDF3RSNt0VXfh2Qb5GLJbEAJvjfUrbe3wklXhL4sTKwhLnXGYGRQ9M"
    "tv6JqbnnsUvEqCTLXviCi5PrtDhneUxGRgXymvxu2uMoa4fLUnJnyyJSL18S3wnnBvHTsSSxUMzq5QbzUycytsLotHNttTTByGdt"
    "MNA+4sWTHD0X/2UgVoyUyfEW894ycENhMrkeKupYuNlKEM1xBigpoCJC+87s2vMXRH4ZlR+y2vWx7PmrPr8elX0YZcHwEyZ5DuWH"
    "UfkWx+qd3ZIYH3VV2YiqLona7bcNIL3ukDjSKmM8hYORFxB7VuL7X+jEqM/wSdFoKnugCBu4WQ+iz/4tLrBVhpNJZY6EeZr8+IgO"
    "PLC61mtxIoF8gWP8oFau4Xx2PfwPJOmh1v/LTzSJf/8vV1f/wkidV6q4eviKH7W5KOpfr8aqommKKs0k+e+Eqij6280NjqCioIPe"
    "14ogQ1e/+q60o6aLazSUvqsbVPpKvCEpvqvUSpKXFWHcwr9z6Dvf1deWOFPEq04RvhRkDU26Kk3/IkVDdIQE/Rd71EP+3FUF/UTZ"
    "v6YFbYy2X4ElVER5pfiu0kieUdDk+q6M72h5wOBuDloiGNwc+CRtnQiGrEnrSSIYtiatZolg1Jp0WCUAxJRPCkFazJoWRmkRM58W"
    "TETMH6GEmVsL8w3RIongnfkrytel3SVCXCGxRNj8Dq5Gthr0KmJLS9zZM6FOxexpqLVcKxCd6WjR8hXQJKghxDVwLkzARAjWdSJw"
    "hcb4Cn1y9R/BWDASHgcjvqvAFWrQVZBLDUysHytoW4IQfQGSK0yyBoKxUCwUp1mngqYnboMhjf4eCZqIfsfYb9BTJsbbkTS+GYkn"
    "SVSvb0Oobvy/oOf9Fq90tOMt31zbDf/pKiLFjQB4Kx9oXwD/iQXe/1dYC6h9Y/GNPq2l1TFB18ZfmjpOoJPZNUgLCcjg3yvTaegv"
    "6MBdxDcJxPOVWTKVhD+5+jKZKuLHoAq/q3fJZCvVSp7/k19WRne5/XhZSPpbuUGqo1SU1Drp7wSbqW5ulpyn+7t2KltMK/l5tZhP"
    "5xeZ4yCZDSWlRkZK7ctzVHMqnczN27NCMbXr7I9dbR3pVUez8dq/DQriInlcVsR5Y6xmj9lk/Ll3OjxN/f5qJ1+t9E7FQj+9qTW9"
    "832+VWo9tfIdzXu8v1NeteikVip3q6WYPpn0G97lfXwUHgWTleQ+P8vsDiN5W9k27u4WmdDU24p2t/Vk7KA8F/TlUpR7cqugnhpp"
    "vbbztnaTqhTW4vVBV5knla70mvMGg6dQobVQG/N0pDgol1bVglA7tnv1UjG6PoXu5adwqpzNZJZaZtPK91P7xVppBKVm69jZLJV4"
    "Tqgto92dMLlTG97ooFUZn17nK7FSjdSEwthb8PrDC/UUGoRz1fQqe3xdLGetdLA2bw26k9yzEtjOy0oktttrlbBXaYflRvGU3a/v"
    "EJ/sbHKNTjO57xyyq0LysCxV7pRndVtVhVA+6s91xcO2vJv4Z6GDOo0U9PQq1Vols81M7v4khtXwfDwI63f1kxzuTibL0akRj3rX"
    "3lZFTdWOq3nuee2/j2zl+2l9I/dCuWq0OwhmU+FgddTr3U3HYvhu5x9UpftTbBLrV9vNfuOYfu6n8uVsPi00osH4LlR5quzWtVpm"
    "39/1J8mVmGyKweZ47lVKxdX9vF5Mjov59qhWSo4anWS2V71/Lr3mR/rzvp5shGfHZKh1ijSy03s53hml7qbtXrdw9Ed6+1kwv+wU"
    "1oVaungsZsVJP3DMVaqVam4fivqjgXu5rU9aO+GwaQn9pbD0xurb8rKU3JeTpWoznTw91ZSUGijm4ofwaCIdxn1tfxQ6z+mn8Hbi"
    "j85Hx1b61V8tocGqjmelcD8upaLh6uvCH9ZbAX8j1qj2k9JrY74qFVLru8b8qdmq3B1Wwlx4OpV24Vhveqhnkkq7mOqlCuVWQcxk"
    "k6tk+bjfZra15GS/3Qu1eue1f8x1y8u7Yn151x1EV+3ipBHVW6NtsLR6rsuKetxOSvNxN333Glx2uhG0DuIBXR+FB/uOvMl1K6n0"
    "oBft9MTyOF4PP8n+43iTbexe969yoxyrdI6pXncS7K66vXk2hSpaz9RBMbQZl8reqX+8vo8u29K+E9u/Bg9P4eNp3dD8Kpq/eM3r"
    "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"
    "jKK9Zm09FqOV6OJ01MI1ObQKzHpqaz6tNwbNXrp0EPq98qofjyqr5V18UtohBr0LiU8b/X4dCu+E+3x0F++FZm1hlIrresH7uhdH"
    "i3Z8k92uA+L9qOv1ohWVjw8a9fi0VV8Uj/WB2JdnofU0I06T9fF8O1mo8XSy3K5WjsfcqtAZpFa9vZxpbibHmtzRIsHgXit5qzFl"
    "vJssG8VlpawdG/N9QWpM0mo+9apWa5VgZ7Xs6kpnKjwf7gbzbjE3ftqU2xkxmRXa4361El13Cit9P8nk0ApprwbCXhsE5eYyeOq+"
    "tqe53vx46IdTUrsZ1paL1nFe6bRyS71fzucPh0xBfa3GZt5IL5V+noyX1ftyoZ8RQ4jtZzKp7Cx5F+g8B+VYc1daT5Nh/X6Urqq9"
    "V7k3as+8s3mrt2/LnfRoca9519FSK1PrNlK7ihI59rKh4qYdHcuh2X0nFHptC9FlsbPatYtjudXOrQN3k6dgtH3n7cwi41glmesF"
    "w/NO4XCIDFbhdrqaDVV73nqvP531CkX/YVZ43fgn6errPiokM+m1sD6G/fljW5w0S1JOX8h6L3ZfTYc7m0O3Ga+ERuJW6nXvpvt0"
    "W9/nt9tN5dgQRC2mN6pKySvK1dS0dijNjvnR8liNTPvPd83ToTGqLE6zV7W8U/PP1Vg/s5qfZtGdXNycSodW91XtzaqzSnKWbB7T"
    "s93zLFztrtpZ+dCU53tvIBhJRkLlfFa+KwtPld40WgnXW8HYeDwe3Ocjg9GkqMSK+cnRrwT7u3m2GqiNB414fbSfKyo6qpQq/V53"
    "JwmnlHcphjrj7mnSDjdPvdXpmGpPG83DYlOoVxrxUqu5Ee7H28BqPsqUAvtuufqaH7Ry3UGk/BqYpefVY/1OL3eDm6O+zS+etENt"
    "1qoUGqesvvQ2sqUq3tO781KwXXpudaX74lzpr8uZ56dJKzCvvnY7pUpLWGVnKSTDKUKmOWs3J5NMNp9J695pvJCdIs67jyyiJ6lc"
    "WC5Oz/I2fTc/lhaRwirzutiXIr1x4PhaQ2Jz5rSPKGIuvepOa/Fmd6odD095QWxHY1K6JKVy6MA02an1urr3y/lGdxyLrZR6Ixpv"
    "5FKIn9ai7cE81ii3FuWnY7Qfm/rRiWUgbYrz10YnlUGSzhyd09MN78gfHh8H7YIfydyB2WE33xwK7aK+kyO99nwR7bXT4il1OIWT"
    "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"
    "qUk4Jfb2kbcYkJ0Yb5GbdR2A3FUMItHFLQqUojvS5IW5fShA3w/2pupsrg/AOs8/yNe/K/x02LqCloKLo691hX6IaMw+GhGHIntw"
    "SY9drwRMDes7FHSmBOXoD6dHOOaD7c7eAFE5UyDysOfhS5ncXFauc9CvxZ/n2mR8LZNxvsKyvID7l6+tqtv78LKziVYBomJpoSkx"
    "G0hSQcsLtU8gtiT3K3LckDTnS4MBGcHMd5Ey34K3bpp4EtGgLI6RgLBj1CT7IuA2vJTVzhX7r+llo/lZ2qRvVbrN2dwnthQEO0Cn"
    "RjDphQ5EVn/FD8rJnv/vBqSCxUolzOI+JZrP8q+VR+tn5mS9ZD+8oY0+uc9O52THOO9fQg+/ATYMFqm85KfCycWciepbiTBAlOsS"
    "MqOoI0Q0A1zUjFO1IIsgPUkPeaAkZxqmdK7Lz4mtXAUqHx6uVRGLIkSG2bA8tD2hYoJAsajMMwjltXn6db5SkjCHXxvfWQFQRzjj"
    "Mr5nywUGHf4ggiQdZr8Z8lfaE8mixaPEjFVXSS9wqdLcb7WEqT8fFQ3nZp/sQzeXzEhwTJH/avvSLsVxZNHv8yt4dW+fU9lAYRub"
    "JXM6z2Xf95059cF4B2MbL6yn/vuTZBtsYwNZ3TMzPZ1YUoSWUCg2hWZMpgdOkM0CK0i5bW5AzHq1cmnUGp6U5oZr5fkSPcixk277"
    "wMpWtT9Q10y/vN/ImUqfG8V5Kb9pCcXFCNvOwU5dNnrFmqJtditVodvn7cZqlnrpOkv32NmqM1D3ipo/08eVeK7mDXl77MyPTaak"
    "rJi00gS0lhfItTWunnsEtmR6mXyDPaSOKT7PdA9KpdfdbJrgzGDG9bQ5S+1LBClMD8fcSl+1xfi5MNPIKkfvrQNNCgsFnD773lCw"
    "uPF8rNZT520GH/Q5jR4tzMy2rQjgsJC2ORFnjFZLXcymdHNYOg0XIr3OnjcrutqiOtnRdleq1pi50FcquZ5yoMjsLJMhUis9PebM"
    "ZgYH4ml3HC8z6fYxM1zVlyvaLKf7PN+atPupYevIjFhl3BsY0xHXyREib27otZY7N5T2sdpvqaU2Rip5gxxrWj6/7po8QZpWq9rE"
    "SXPUzHer2nkjxHv5vcZVa0DRbVH73imXqZmpzKS27eptCS9LhQqdKvBAgNcG8/Zxp9VKFavQmk/p2snSt9PBsr5uTQQqrmU1uaBl"
    "paXAjI5guchxn9AWWhPXu6mWeLaaRH9+sGpKfnSuzEtNhh1mVpN0eT6Y1ga5SY6lmz15mZ2VGudsq1Nck5uNBfi4HmeqonIedPj9"
    "LpsvMJQ+lfatOiETY7FTXQDZpshZRL0B5O2Ush7kx2OhT2eM5WyJzbEJ01gexe3+VOoK6tIaE6tRozEfKZVNWyhtrXadpIZNoY9L"
    "x+7ZHOzWWrqrETUgW8+oc9kssFSZGBSpzLG1qS5EpsiXDouMOKnNNaY3k/rp9EKhysv+SO7SpW2ZOQn8mennmc55saaP8+OouOH6"
    "Ay6LFaxud9BWhxtq3VstZucNHa/P0/P2utGrnao1Kl6exkul3pbfbwC55oo9Fqep06Fu7E7kBJfmA6t80lo9STnPdjLgRM22ZioG"
    "s5lKxJitn4s9IdM4U/tmpmvmes1mpUJWa/sxSZTMVc3MG1NpPaxu8BOjiEustZ0D8Xi5mCzjqkrNAWtfcpaR7tTqjbQo9SlWnPF8"
    "mpvQmK4b7NSw8oLAH7dCvac1lZI+H3f3QABpii2+V+qNLaNhjXbMzipte/hwnxekFU+zp3F+3mPocX45GKzNjjEbHHhNOojcPDUg"
    "a+tUyjwtczD0mjidmqO5kJ2V5XWvvpophfqmlJ3ESyQVb5Dmdt1pYYUtXpFkgl0fVrWzOTvjbf5YyYuDHry2ldGx40Hv9o6HGk9l"
    "ctYmZ7XV82SrVs41oBcocaFmNU5EhT2fZfnMWLt+vrboTcedeIkYj4dprG7pXP4kEOf1fNbXW1qfy52rq8JGnXPmMtNfZLtnY5CR"
    "Jo1ztVJYb/o5q2lJxhk/q/0+lebnipzD0nzxaGlHo39MjVRDrDMbvN3g1FFanmx7s8E0R68lzMpvFFIZyCarVtbVATHkCqfG0Dqk"
    "ai2pSOLjTsewTtM9UVkc6oNlf5U/7dss0+6yNFCr4/KYL7OFU407CpXDcG3Oa0VKoWSpPRJPY75Npyuy2GWnpfmgM5tsmqV4a1yf"
    "V/C90GrgeM2an+ud3YJuceWCWq809GEFO+WXudLS3GlWjpoZg1NnhQ+sfi6+nHaF3bBhnitUetfrLruc0RGrmflxPj2TeXpg7XJx"
    "Xgc0JZub3aZgVfTUhLewqlXsClxpNCUqFUK1RjKZruzS2zVRX2BqUWrr6cNq1G2Iudm8uY8PjbTQn9PTwoZPV3diLZVlj0RleZiU"
    "55RMrLbEySRZqlYe7xV8xPQOkrBdsbtzo7UnZ7yxmtfHRDdLYnlLUjLzstk5VguKKsU37V5hi3U2u/zmkFEOWSmVSvX7lcyqNm03"
    "ZKBbtjl+Uzx1p2xlJlmanjfPNJ5m8f1oPju2m+ZYKs9TSzW3Hq3yxzlQeAsceWxWjvhhkNPKhXGmcBxkRKxW7uqH1WxZNIpUusxj"
    "5mJ7HkzW4r7baZFYvaTuaXNLmGYpncYUPLserftqSSiexoOySM03xmjY2ChSV81m6tnWWhqd1LLOj4dABqtiuzZ1zlaG9KyYm1q9"
    "lsUemuV9nZtgGSa+rlh6Ux7LfFEjh9ZKzEkdMWUpmZGyzFit2lFYnDGyMWmNWb04LrVYc91pUtSiKwOG1j1y2xxuctyRVauTeHE+"
    "Pa05YtXd4wu102hWLX5GyZNu/YiLbLYxny6t6ZBgM/uxIqSp/Lh2rrc7BFB2iXHlbC3iHL6e1XLFypyMn5YZfV5oYOB8HEhNqpse"
    "5PB5IUXVxU3dJOdxvjxdsKscT7bS3fIc7kGT4tLj6UhMke3h4QDEfqaWzp7ifLdM9Ut4vnDWFwLfO8WN/rRBWJPBCeYtOx7w/a4r"
    "dsXl2drMRnp1opvNfDZjYi32hLc3efEwtPb5qsZUVqVJfDFdbSszs0KqJEFVJYVsaFN1WxwtsOVBHmfy4FQrDnF9l6cOx2J1KGHM"
    "dLNapcsb3uLS++X5rHbV07ppzDVeyzGKnF/MS9i83JyYmH7mR4MRW071J0VOrOvMARtMDKAxWKnjabBtNgQVKLX4DJ9L2UKWHBxH"
    "Oc5oqJX8okWQqbNuzdK4rnTqG3W6SXXMbLlSrbWKw9zkZB5WxrSi5g+dhbYn8qfhVFequ1S3VtvWRx3ayrW7h16xSzEDttWf5Mrn"
    "5qxfI+TxaWVJFJ07qZmTRo3bhkWxu/5ynQPLsxcz2vLEigTTyxKj8m7fyaSHm3o8U6pwca3SOQxLVJ9SRgOqUKPSXapOVYT6eGQK"
    "slBJy+vOKHOi2EzK6il5VehuRCu+amfy2zHR7xItkxCm5LSaXlaHSlbo6tmDzjHVtaR1tDEQhgpljRiYrNWvAB4WL2r9AlGaZ3Op"
    "aZXo1IUh1jbUirli4hVLLOJ8vANTXm17+RK1AmdBq7IcGWVdWe74QpU4bQpbI5VrGyX2IMZ3hlnLdDnVovg2oXeW2AqcXup0dJoz"
    "GWUj03yf2lULZHzCqqe4pbTL1Y28tbqz5SRrtcnFuW5IR3xoptZkDvrA+fOhM8zLm5U+bZOT6aFJt/nKhE/xxLyG5dTaUWtkBOMg"
    "lIaDboHRKXFPtA/1/pnjV9IRK6+OWWu2L+yHink0auXWID8skpPebATTJ6YpKpNvTvm9zBwEY1kfTXCxk9ud+xLYAf1CmyMZaZkr"
    "lOr7U7rLZKbH5XlsHeadTqY7mmRovddPpSi5V1jQBkXyMj9pHLpgd2vt2prJ1sb9gVBhKWY7lnW+V5VVvTTg96fhua42Cpv1CSjL"
    "+XnuQHQKc55frLbYwujkWEVM9QqrlLVNMUqVOeOrMdWRFGWjSrme2BA7RsOgDzreM6z4Dui1BSOXbVOpuV5r17Uu29DGa6kkzlfq"
    "QtCljlHO0EdGOaQ7py21aKyV01Aodo99mamJ50OtcsDb0I4yoKvp+YpZ9SqVjDCjeqJYrBVPPZZqgDH3D5h4sNbnYlXCuPNEP2sV"
    "sRMfDUqZhZA3sON4W7Xy1cO5LLX2xUJpBzZZbTDrFJg2aRDjZrcybq052mR2Sqe6HSxba7p5bLVLmX78uGYt+WCkBrO4SJeP5LZM"
    "bXFc0vGxsjobemsocRli15gQ2eWkphnlllkBR1ahtZnyU647npIZYrTkOlR7vCKxnTxcnagOn56njhrFG+RqpNQaVFZvlRZZY7cs"
    "D0ajZbzElYozsW/0dWmamw7bPF63GnxvPbUUXa3kMoPFdJzJsGnGMrjNcSmZnbleIli8n25sxrXeUT7FiX6TkCedhqiNZ3S7g4mD"
    "yaE9KOeGBzm3l/PrQ7Zm5tJ8vls+r7UJWZUa+WqmyAzObb00SzOVAbMmMuq8CBhxPlvE10K9U2w1ZPw4Xq77xsDaxk9Gh2/wy9ni"
    "OD2OukNeShUtQTBUtq30qycVq4pbqmEoGYw+nmR9kBtO+/S2xkv8xBArtRa1KgEx9sSU+rvFNLdglpNzji4Zs7OAHTKVYZ1kzPER"
    "B5NS3Q83x1lBPjFMe7ZZp/WziRHUYD4XoE+7WGkNy31pVsmyGWK56pTGcp1dbzAgAm4axUWrIzfHGW7UOHUN1ljKVGm2WWaWh3iN"
    "5BbTyrFGz/DJqJBnSyRXLNA4MRxuTr1yf3qg+nXKaq87R4lft03MJEim0W2WNtntQZa3CjmwtFKjIcm1fltoymJhWGqnuVFLEyo0"
    "r3CZTU+00puKUuHHs9Y4PQJCa61msBMwCqaymGqGODzR1Hi9GOtHrL1oVOnWqDgcVrYAR08aUtNNb1CyhvkCplP8uVk3dWHZZQ6D"
    "FF6I44upeNhI9UpLyp5m56OpMGm6cN73l6sWI5lSbbrP79Tqose2txuMbcbbuzPQb/kNW6jtBDw74Cvi2sRy+Ulel4DYzJbJUm8q"
    "ZrOyeGhv9p0St+lPOub4hB/5FpeRp7m10Gq18iuS36nTYznb1tuLYb9OdqTZfNCoCOfdjqo0ikdjKzctU0/xLVqJk1ijSE3w1nJM"
    "HDlcUIlBpboZtJhjsdSrNFYUkapniC7LZ01qNRwYJbmzY0/VtTYixcWufVgXBs3Cvt7RjezqfCycy4d2XlXaartQpOJxLrcq9Nf5"
    "ZWPelfO6cRimGep4KFSERaHQqPN4i2xnD2dB2NQqVZ4cl2pEaZcBp1e+cTTaiqm34vqW3QNJqJhi5thhPxW6BaufIlqnjro8x8u9"
    "wmBe6mKzTvOcLcwrItiAy/zZmp2nw317VKZKRU3u5c9DK2fp3UmdK6RSQ5Mc4wtrYdHqLj0bpivb7JioT3hN7xep2Rxv4DNlYiyI"
    "mtEYm8qILjSFSmba17qWQXPLs6LmsovOJpVaN0oy11vhxn7bUeMZjDjua3KWnk+0WebYXxWLUlVSJ3N2ynZn9Zw5nZELVhNN9VCU"
    "U5sJGcd37cZc6y8Gy03upO+Gq8OmwQps5qwJ6U57NjF0utEucstytsriZ83MLMydKFLqUCV2Y3WNMy2iMe5vZ/I8nzkNF7SCp1fl"
    "+GkyKLdKvDrek+B/NX1wUJUWWcenzU7upInCQhWP7FTeL3fjwbzbFc56vzaJ96aj7allTNYZddKLy0cgAJ32iryatJVNzcCwsdEd"
    "bIg8Nyocp5WiIk40ktrsGvt6dbNuCstceZStn4fEfGTMx5NWOV9YW+UNdshWOvtJ/iwaMpiY1WxPF3L8KL/DJ2WpR7eLvW7lKCvW"
    "kSU6mVFqcc6sGbzZxOUauxusT2lpuqPNqbpbFWZEPtuUh1K6Ne7wtWG82Vfzve5uga3Zbk9RB5rcqMrk9pRRu5t+M1UfVjWgs66b"
    "o94xo4hgY2VTFrHR40BVyx27dK/VSW3V9UDqa411pbMmV/VDv1mx6lmc6vWPcnm/I5Yy38z3ewVJKE/HGDUqiHOjN+woTaqytVhD"
    "qazpyoLplpfrcvW4PwqTZX2iHLbCzFjojfJpVLPGZKGQbzUro25rVBkvZs1BXBVFMOfQW5rt9Gq1KW8cyxV6psyKYz0vpGaF8wAw"
    "6OOk2G7n87Q13c425872xOwFZjyy8NJshC+NOjgvpZnSajHn0Wgzo0oVw5DNY650wkZjeleT8PZwNFgdZ92+jJcOzHk5PUzxHWYN"
    "ZKaV6s3TxaO81E9TDujYbasprozsUBkdNgtCEtrFI9baHfQd05tRS3qhpkT9RDHZPpUFGoAxbuPbEhBtgQRIL5clmibMRsNYauci"
    "I0m7Eq0t5WYzKw2neG0+sbhzy2y2twuaHMXH2RpQxXM7haGn1rSFN5SUPGn28aHx1xuv6lva/P4Nvfj37e0DvQ944CRBNN9JDItl"
    "Mcz+hp7cfFdgddn+wkqGBt8cNA609ks0t7LvccE9rX+/PcTpALafy01rx1/oqVPnbdMLowKJytMCvQb+AR/hFXT4ypen6Pbx7WNL"
    "64KkvGO/roC8HZAUET4l7EHsR5DcAhA0w3CgONgB+CQqrZ/ePhha5+6L7f4hIKAjnC5LCpcEE2hw5vsPgtt+gBlcbSQzaePeqqop"
    "wlfCacWUaFmiDY61W+scbA6LVM2UtqCTMidIK0mWzNMHgiraS4H/IK+jjP2ZuP75vuLACnKeDzRvcvplpR7hmCHklaoDHEnw5Qbh"
    "P6LEspzy8+KuoaIq3P+Ttpqqm6CTt4rvBzCJ3PeVZZqqkpAUzTITBugkY6JXmcHs0G9o1t3pvmsq4gmRSIjphEgmtAQrJ1g2YckJ"
    "VU7wkmDp3NvlbhlvTW3YoasnC28fMmeCwSbhU6pwpMkfGEaB2ffScIbCAhOZvscD+/cAFSSUxzA9i0NfoojJg/fdnkNJVe5qq8qN"
    "+kJ3QAg4exgmfJc8oVomXKQfsKpiba9/rDg98UNLoiW0f9p/O+Pew+eOwb9BEVhG5h0As2Rah7+NKHKgwwkiYVhb2MPEfwAQCRD4"
    "8efbO68COTy5lwwJdPICOgkn8B0+U2qossTGQvaeU8ndWKDuXUciCNJgdFWWkzZhJVeyymzecxhqDxCgN52jV/to3BHWD0RWqBS9"
    "wAqZ5rulaRzojcF9BJdwa5lckGSwMDKEdTmTju6LsX2Lgn5PgG7ZJbyFXcMwdVURLoG+Oa1VRY3g4bDIy8N/5Elua7cydQscLCZ3"
    "QT2GD9Hysnp452RZ0gzJ+DiIksmhqYTHx0GntY8tWJWDxJriO/ZxbWCzJBsmp+uqnmTB3EjyxQtA07kkAuE2Q78AYz0hgvh4rff3"
    "s+xMjn5hQK+TGg26JimA6r5T2B9vYUOwuw/fa3bXAPypqYYEN/U7vQJUDWY9fHQaLXAXAXT71g8j/fah0SwLqc331bMxDNL3KwNO"
    "L1kSFPTqMTjE3g1A/eaHy9EFXWI/YBENCEV/d/GmJAVRDpwHlyIAlwnpThhw78J5EdmQdPVwsVuB6doa7/Bo5fSPAGgCrITMHe2F"
    "uyMHFyqs4vQPTrt+gR/e8Rgec4iVlfYSC0+6UCkBnXmAgaJ/A7CeRfIcN6DmAdBpOAy0/i4I953qW7H9wSEcICawhvNsM/o7eT9o"
    "/5drLVAAJhAQ4haMG1AZ2LzWVjHedU7jgGBGW6aa5CUzEQOztKWP3xmZ3mrfCeqPWDIWBi4R+x78TCbyGOB+b6AFjgF6jv0Zy+fz"
    "iZgNClD466CIBEmGgUI/QAOc19/eQkiDlziZDRIZ/vaEoFCrzyf8+gGPDOVy6JhE1Ackj6ODHfb/tlnhpP9yjpj/wFexk+C4436+"
    "OSsMf9wju5UlDZU3faQiGYEagEd4JsLS4dvcb79uuP6yBdOf4RivR2Q0TqcK+hyN2SNseJGbHC1HoIZFj/DC8udIERQvRmNzikAI"
    "Sh7hA8XP0UEYXmyMuqLlqMm1Cx/htGs8R+tA8mLeSyqQLSIw24WPMNs1nmN2IHkxbwHzB4dBBGqn9BFup8pz5C4sL3ZZ2nIRqGHR"
    "I7yw/DlSBMWLUQWCmhCF0y58hNWu8RyvA8lHyxbYu4YRRc926UOatqskV8JjqjbBeeHDfKB1JQItLALCxSO0TpWvo2XhFOgRiO3C"
    "R3jtGl9HKym8GoEUFj1CCctfRPjD+bmiFfZyO3b8dWGhCwwdB9HFDr+NrnDjyT6zxx0Ee0z/w6P/ENyHV/JxP5PEh/cIutbOf3hk"
    "nPf/wTAs/eHyNgVoCHIAzir9EaKn2p2KMNMorH/uYp6DNOErsE9lCaiF4XvVPz235QwO/X4VQ3pxQ/bKgK4obpqnD1q4PvxU701G"
    "4Y5AA/R2G0XS4MACsWD1v9T9vCvF2o2cz1T2dXRA7TG/vwMJDQpP7Nu7CGWlB33wonupjyTxemdun+BO9ErvWAwLDBWQNvYUss2B"
    "bKOZSLNAAgSAwH+heSJ0kcAvsPBqiNbkFWhDFDrymUKB7Fr3kjDE5tlA4RrLdWtAJNehoD0eswcE9J8YmpjkVjp+l5SYoQurRMwP"
    "4i1GYn8kYsjSodE6OMtdLUeUtBcUPPzpGKHI7mhkBNAmPr5mi4EG1hCNPEIHCJ0pVyJ/ME33yqS7nFgs4/bZY91x18zRr2/6K5w1"
    "79LdGZPhlH/8dxc0Hb2gdteQES68b4DuH3TP1zNoRfZsNnd/XUJWK+Bn8Juzcl5T322behRBp6XdF3+FpKdCAqzMWwioKydLeMvc"
    "jxfG0g0wD4DnJWkZKIQce2d5dE2pkEyhXdW2Qdo9eLs8HA2ccFsJtXV9cByZ4Gz4ks0xAqApcjT7aeqfpng5J9EZ9I6HbZarpcow"
    "JWZz+jBVzWuAB0A1XRV0IIWuaD25p2WLu/g3NRkYlakKgszZ0xv4CeiMYzZA/JCM756Zv0342yMreNRQoQcJDPVdpg0TUrIMBs5e"
    "rt4OgHjrcuInIGA7cJyBmQC6K+Jv71uJZWXu3sQuJkz2zWNbjyzmgLSIFs+GB37egJmiCyGUHOAaogMMWd4SwWacfXQ9aXZZW2Bp"
    "+dPVgIdsbr5uoAWgZVVwJg1ax+6s8Q7z8y81QCuBSQf/TsI/Li6lY9gfwYphez/kCAnjnv+35UD/Yt81neM53UjqHGsxHJvcqohy"
    "7Z9vl6+4xRzHwIoTaaAi68jQc3N7faCNZu8Lv0Psg1YAMcKCJGvp6A+wQfGtEVoFjMyuAybfAlOPezxr11GB/sHBIMI33mnGlPbe"
    "wfz3PC0iWCsZrtcv+xCQAIXY1lU45utKIK/JrcbTE+zXTbJ+YjL9+J1T5tZB0DuGe0g9N7EJdsc94HjzN89eGxStaYAV3rgqFs5D"
    "P3xCJNxRSATFgNSSwGKAacZw0vORDJjobSz3Rnr7+yMLO+b3FCBB1NmXFAF9E1fpxV/v3uDu4JLYKFQ4lNmC8CPhAALdXF4Qem1e"
    "ncZuLhX0d3DJHiidV/XiAYncaMPTvRg8mYy9kJC2wtvF7gjh6Qj6O2RjOCAUent3fCcBewiXUz2BEEE5MuvaqB3A0ARhGa/5VLyK"
    "x0NbOdpJWAyyPh9yCvN7X8J9V76efboOJPB3wk87vp80cnUbNy7jgwV4l+FwZvjTHgTa6rdNHzEFxNWfk3S3DPRTBaYmdFTJo23m"
    "D/TElf00VUJYXFIkQkjxSm8hq+w5Sm606tl6PJBa3hK27B78/BGq0b5jAbUKkU/ExGR8Ox4nggoL9UBhuU2Go+aHWRSCVf8D4wcc"
    "KZhj/zJ1K+SgeGHv+uCi4/Nyo2woSj9WFj0ilzMb951P5wITmfdNFgV+hcjvHmo2oUAFYzfsXuVujAL+eWdFSIfraIDQoCpWQhRw"
    "p6B5++2tGeg6hf3xEbmrwtYkdj+/v23ZC+zul9mU99gI272INfnOk/+7npKxG+LYdzT///4rm4EuyUvwoPR7mcMYa9Cn7GVIDkE4"
    "mkSIAxs0xGK23xBtTyp0LMnM3SCBEI4+/3qBY3qmi4RN7DZgDRRkr3p6qD4zK3jhk37i/SfsRkFPfzS3iiGhwt2F8EMuVKiwh24b"
    "/uxVoFxpJGB2s+N+nGVI34A73+EqpLV7qJ9OhMz9mpFRp7XT2nvKecbssuPXKP2HY4TnJX2bhPrp5X4PhYcj3ks43FYzTxd/HIcz"
    "6652+Gi3hoekZAIhKSEs10NUaH9E9MxexNsx7vriSZIRI9u8IE1eRUnSI0qSIef3KxbCl0RJ1LXPVxUguDG9Q5Kgw/SirtbQgMRL"
    "YI1sZufGGJGecdg/QkRRBMpWdRh1CyQR02H1Xhw2QCpzg0dd+RCqF4uKEbvSug3O0CTFtRpcNcvr0QRbeO3vIWeWMzRPT2xpxtWh"
    "33/kjRjcKIDNS2AzKGAFEOs3LV2JHLHX4mIHLL0QUxXYC3a7+60QHqUDN7AbmYMlYPRL7CZVPlkTRMrhWo8T/qLq29diqvC3aO2P"
    "zHkYq4+RBNqEj9AZHA7DfhIEHOB1uGnwKyxqx+62Y65FCmOAQz9p8/kOuJ9r1AsPVXTrO+7KSGvXxz8fjxZA/fnQIBwIuYU/Ndow"
    "DmBDvDnnVyZ4fvmjkvxIUWDk12KhXAe83xrpF2F8SByDCQwL5Nifl4dkYdP8g+ax15cL7bygqAdbXgU9krgJeu7m+Gr3XulDyJQH"
    "OcsvN5RT4SLiB92orlccft7l/4pPyiuC2W3sHjkkzUq6HWX+bs9LCDWj6vaS8ZIs//Tacr1cBPNUR6bmL4v76ORy+RDpGw3kRYEv"
    "6VfmLRb6EanM/1V3GpEJyrkRE+u4dm52jEDEYegRa7dEgeGvh1TfVJnn0dU2gtfVNvztK8LrjUQ+Pb4ZFEBwj/0tRM720YUXJhKH"
    "nzvY0VTcTmEvhcuWIf78DIK86v7hW+IzrAvutggEjXqq8qpqvrZJXjmcnc0AbcwP3DTBkyz89DKuV0+8pmdYEjA8e6MmPA1tF8PV"
    "tXAzPXjqJFnOYC6vhLR7D7wswYj3oAAXNj7/jP95eW0SbABrdZVw/7BVvifRGvdCCWx5x+quksVr0G4zD6GZIhADLkGzJhAVeIc6"
    "blUl1mOeuBk7n3bYMW24d19s6wWpeTqBzNUP71V9ge34GVjwjks4/4GdcO52/EZU9w2GfYEsGkb6KIfdEYPxI7cleDSCH3kqiO0T"
    "AFKCxn4slD/+wHLuZTT7zszd3TSX4yMSpV+6y+Bxv3uNjpHzDMDaXfY3dy9HPrxh9uGVBTwGbUSAsR+kq6GF6aMObpuNQpcZmC9A"
    "vEBG+2n3x1F8iD88Sh/aSGBPczEcQr/1iKMNcOy6iqCf2I37fR24JvOUKUJQ7nH4VDsIbR6m5UUyHuLtabvHe3TLPofwbHOgveHb"
    "rXgAJow5+4n6joWVfAYG+bvRbpFCXBhSJEb4h/z2YMw388ZXwKDJ9zM7dOs54s6Ze9nXjuyEd2reiQ/fD7cGlDpVXYLahhtvciUn"
    "T52wHsf8jMI3q14rChE+4Ej6BMCuuzy86efdFnnhVA8AAvtU5u4o5pHhLRRALISthcHwBzE/g+VQTcRp838b7sTrgCKM2JU9XbA/"
    "LregLPQX1D6/J9E1qF+mGlqaJmCh3ZnN/uIavl8ywgAJydFT/damECFgs0feD7fAaWa4hTHWfHhBFNZgLxGk7hE/3Nouh4cE//Pv"
    "s+IAwJh3SK4QFDZmfyswxn/wfm/omX2HMsJSJXP7KAtB+Mme9ol5yPHs7NBM0PQbfuwjjA92x/UGykO8Hp7iteF7jniEx3vHRz38"
    "fIDWvYES3pgB0gjkh48gOJasOwCWsgHiqOKLiravT0J3jy2jJAU4TLARvuNpiuWExL3eYLtqfYo98t2CaY/GaXfXm0Yh5L7BsxXx"
    "O791oHIA3eoSdgH3NT3AgeAQKICAXPEwSDDkWuqLdm0fZDtoDDUFG/MdT8GxxYgofea+P58+aIa1soHZ6N8JPzIUfvpiAJqvzRPp"
    "JzRi59HF8khFB6dCBgrx/mVsHR72YsdC0lpEZA64xyULX8NFRMwC5V7tv0dxkwmvklVEpS/15IGm5h875p9osA0l814bi3D0hSpp"
    "eEBJy0QpaVHUGLvvkI3/lhHlN2YpaBR8gbIQas9IcqHLKClQCgRTxoUij5i6iFw3OJytQKTED9ybAQc1ZDlGdaJmrzBiLG2Ibh6c"
    "L1RImqLEbBRwgEEbUNjkeMS7V8Z2zTKgb6LCYG/nrBNW62mDzpcLNBTaDaHzdMPdxZjanx2eDTm48wG2ZsB2QkeC9+NalRT7qxcZ"
    "jPq1kb1y64MMmqmdzt2OKRsq2AkCZ35xEPhtEHClaF0H00XE0l7ArOpADYcU5i3x4/hBaUcPwBj0Z7w8for6I/jRNv+/BUF6l5M2"
    "wvvsHRecpMvdGAJqR8hQ7icsHSM/rvPuoOBMFH0YsM+6n0MyeDglLyfgiL3i2nZO/xwJZCLc4/fNA86fgPLBW4jj+87hcy+cXHtr"
    "+4e/HNz6OPrFkzfExWNvbdfdh4QTj5vvWk0TgawfESEeeiDcph3aiB8MFAiKj+B+TT55TRC54kaHQujBR7x47l1BuY7TlxxGXnEu"
    "SaSS+MOAPhfH1dNLeTy9gYW8l7V99P8bxHwL23jaLxIL6deLbmhPZMjdnHqnC4ezFXl95woAKjfGPY9An0N5BCpBlyMuYRcGXvPV"
    "hI+TwHJAUfJbJvw14cFlvH9T6H0M+tC+fYPusRj8v2++GI37JEaB/gMI9mxBiO/g14cbYeLLfBR2OSNztXBdoYFZ2rzGgp7FnHkY"
    "Hwo2+1sB4J7QbSzkrmlQZvJJLA4H9Pru/MONFIMim0Rc936QpvFmxYsEakcnO7HNP/9WHrzHoAO4eZkWwiT0sAoh+TOiPOFh3XDl"
    "UZP7C0WRPOhKhJXjWjUsFBS6HG/xBGQO8wa53oUtu8ZFtG8guBcTTzm7GvzrO7QEOQmgEnampy9tXYjUvdjm+HaDufoitinypbtX"
    "r6iP35BxfMv2ztAy8z2Jx/7087cXXfGvRPt80VF/Wxk4VP+NlSArc5Y2cNUsiYKoM7e7ZTgfcpqh6byeZjn/Kes9IJ4fZ5EM/tu3"
    "G4f/Fsa974SFh7H2oTeDoiYI8EMm/IqPnwfe7ky4Yr0KTuGoNGKPLkeilnAng137gmYS0BFiBOHTUVwyumpIXwKWxcIVvpvG5umz"
    "344Zux9MiK6S9o4ZzISkXFQonpqn9x+Ut4xjhRCl+LHOBk+TGPWVISRFaxXU1QKK5D+PE0w2F0Qa6nDymYC9M5uIKg4ZzvUyjjMc"
    "Z3OTWCSOW/+cull31WTVvDzWrbz3LzLBEL2P371v8lvZNl4NYISjsknZvkP98xKBxp/MJSA9XIGg0GwfDETAbqwT0uIdy1T0Rgym"
    "rk3ayr//Wt8N8+ctOA7+TBo0NNC9Xa8g+WQNz80+b9Dc1RzrgXAX4oq82ckVZx44Tvn4p8VeKBf8fmAl2on31+BuknD4fSDPcP+O"
    "M8jr80H5XRKxL3Fekgp0HG2f7NVzhLq5oiFXfGVGHTOh52YhQT66+ggzVH9BOvcIK4G7ir+/Tvf3ZG5Ll72/ORV9Z/82Va6RXZVD"
    "1QNY8Bbd5q9v+LfIREmqjD9sSjxqSjxsmn7UNP2wKfmoKeltipQK7/Xryz+2lB4sW3jAP2cTT0MfETDH7PD8LgiqjWJwnkfWPAnJ"
    "CQu4iSJET5twv3rwkIgFevtCEloK87D9JL1F92/hrAQvHfsyDgSmxm4W897SivIkhrqSEBBQQ6dDpIEonOHRcR7ZHSo8/pLgrZqb"
    "hhcROe5QsgMB/YhKs2uXhqfRdS6XAd3VPfgeXK+58lfiEX+F0agvpBy79iqK76Ly4KGK49H3+Cnf1fQ82NL33PTuOYLoq/12B2wi"
    "djL+/4XE+Ou9D7Q04eOKyEvgDuMmPUY4rL3IbaOIuvkZtdqBNKlh633N0emvA+XhwH31KzRvR2DOD29nVpZx+pnwftGAYAXGc837"
    "fNdJb5rRv9lDBOpR91BuV1/3bEdnZOcCGV//Zv/80Tv3S2nbt6L64k8C+ze74jOQ+RUgm4F4t3TEFoVtEgG4NoN5llsmZO+GbVDf"
    "DvBOmuP2igixDz947IbQmfobWSE+wrJURC2jxF595+FY7X0fLuN7nLV3gAEnVqAqpwgvgLezkSFV68nNYpeRe6PVvniP+L6viBPc"
    "9dIfpi7SshojHsSoB+JGIb6LLzBUVyGy7zgsefsVrA/hwzDTO7EOe5pL5M6c8QvahQDuO1iUay10rWAH2mTEiKhBVPb2dxW83F2e"
    "kweUGzjHvFY31Jt/TuMjnmp8NneIZYKTi+wK6auiZ9/weSH/6VeSEVyfoviC/SQ0oaFnboO2AUfoeC03XzifQmP/lLZCWDKDh0ZU"
    "qN/AUPQvBwM8tdenX4g5drBH3eSWUDoOTr7e2M5F39hOE1fnhQM16eToC0uE+CR1lauiupBgTsnfus/+2uVNg06Af8Lfg7nTDAza"
    "Tgkt0sZ3TxKUt7eAf94F+G4nIwkUaigF7Yt3UF++pe+CfYjz85bSOHjhHlYBc+TJX2ubYzyh2IQvpR5qgpJxxtD/X+zEnACpaplA"
    "ETly7EcQAVCuTTeBFLqehz6CLeF8xPHM9Ss6ltzvFHGrzfEuDJzMOZ9V/r/9iJHHrQS7ocqOQ+nzr7wTHhHsHUGQoYMhroP09doj"
    "tiA69eomAWfPL+/cO/lcAzncPE7oW1Ud/m2P555AbG/Q3zR82IQms7EbxFCDrgce9Yaa0TpouOe8La9elixx6+FrJhVQG5knvsxb"
    "IwIKDNO+FBtIlOd9BPBxjrZrOrvwS5go8Ah0GpEP7OF9GBksBRvlgc78cFlA289b6tOocAg0b7p77+RV04b3fkogHbaxTwqvZ07w"
    "mCjCLbu+Cb9LfBNYnaiMgi4Lg0LM3UyB/iLKiQqJR4eh/04QbAMP8rCMiP78I+7K3prn72xeUYzGk/LNs7MP6D0w3+Q/gEBh4RDu"
    "uYFDBb7JAQWs/QTA88X0P9tGPRFIAFyJjSC5d4LEHu919snNURhX+Fs3HNIIOLyo8SDj5N1IPBbOyLCy3DU4w36oMVKUw5/PHM1c"
    "gx0D9khoPbcr/M4tX9AS6mwvJQIgIkLpXsLw6XktzV5xDAmUiNpk7RLI2uN8Dhd0WOhgiA4vAuW6BWSVqMl3ZgxIeVzEnKYjaSn8"
    "ph6AZhkwD9nrfslH2RZC+0S9FMj41K35KOLMSSHzbDnRUJ9a6eGGvD/9wLJGrgsV2BSw+nNxHUCUDFMFesgLkVDptzdvkxeFWhZO"
    "ENjtAf1Ok1ECjwcPXkJeY9xemPaoiHbnbQiXV3OyoQTbt1ClH6Qn3jcTDAB2KzxSfK+9OIhqAvWGMy4PKP+xPGa39/nu7u+ao2p/"
    "LyXEVVDWOTA9QJ68V9ptHDHpci/zu8nM7VCzW1Vb64NhLN9pLkHr4H9MYsWAf3ZSgtmsEuw+wdMJQd4kRC6xsRLbs5JQdmpCU1YJ"
    "zUgYbMISEpaeOElAV4Qyng/6PwP4ors5qxzAP0R6zz2+DeuSmd/ubhl/gfac7PMMgI9bSP4wZ0A04JvF3Absa2+Iqg4jU6ObX/m0"
    "OwSF49jXTFxk8IKrbXtzrFxewxfhXG/9uOoXmWDQIHw09io0ZZyAQXdHvrL/+NsgrpvHf9kTFN+UMJsvwU8x13ISkGUjH2t//CQP"
    "BPkfVYOvnocfHfhb0DQFhL9ruPwXrsw48ZHPYmOhGodiG1/Ma+SNtUFiAbI7OR8QHweMeC/Cp1nT9qJ6U1N5HhqAKhBguP5LAkj8"
    "NUUnMU/M0zsPljR6RTuaQj7/wvHM1QTggfcsoDTrYckowDhBIbp5qVchY0ctHdShVwFIlEzZ1gku/utFnmkChb5Z8qsTcBJvA8fI"
    "68DNg/rpwDYuD6OsiYSPZl4iGgAi7vbcoRyfQeFRaqzoEfwbjCCd/5G/U4o86GLofaEQg9p9j57l6EKqopM98cWsXqABo2rml9Xn"
    "UG84AKZcIg2jzww1abs7j+XrPTTxMaKb6ciTpeU+jgx6BB68whOML/yC+ArVfY+hUhOSWxgg+gUh+enCAJjQb3j55/LYQZjBtHu+"
    "rLB2xCRAvFZXb14KQkO83Ek6JoNOSeMSlez3cVIFLcwgHjrc15w01yPrEcrk7uKVr7WN/diSh/HZ5gDfvadgOsLrY0wbNOSvJST8"
    "cghwmGPrH7RWRVr1oNB2N1b71lLi/rvvhaS3J2mIQCM30/zj1UJ3gkNpAhQ7NthwpQGVo2sJL2VgT7997eYOkhUSYS+zQ7T06p95"
    "Wh3A4i35/iajPXjbiOC6WfIZmOYRrMFWZYFGGWItRKVg7C/mmnJXGDSyH5778iHxCj/8L1L2Q2MCDBqBO9+/eOArQ+vs5UXz0+/l"
    "E42meAf9DzAUQPho6h9FQQavLKJz1RTBVAg2KbxuGX82V9fMmchP+1whd3setTlBeYj5gXjF/JDLPbor/9TkADBH7ClQQhsbn4kQ"
    "sl/bVxRtrn/pKY4HzhOIAz7B+cwNbp9YoLYQQ670i7vvnY4exFPkDUtUAVLVq5T9xHrkQIvJ0m8t4VcW7JHqTDl6kUtNL6vO7rom"
    "0HwG8yTdmKjf8fFD2/8XddeXNEDQAwM6VL6i+hFX1Q8I0OYePadhvDwG/wEoy+4JiOejTkCI40vT9Ox2bPort2Mh9sN1inwbHBVx"
    "3CbMVXF9MSN3e1Ym9OrkwyHkgqpnSN9ABy7377v4wULjbtQ7GNHvzKQf+7Eg8n3C/rd8efiK3r2H2W4fsJ4+DO5y5fFgyhifxT8k"
    "YR7KDwcPck/iM+itcLNZ/+F71gY5cuye/YA5QZ5ca4dVDU7w5ueMXm1IsAGni6Po2lBi0uXhG87egRHBTIA2FBn05e5tuSfM12kX"
    "znwfsNNb3+3WMffF3FfDqGz1BwLYfG3gwbjZYGypDfRLAgER7Y+AUTuPDxjviwlh20SOlFsQ//xq5klPqsk7JRoB/AohfSmlpM0M"
    "Lw+d55nfZctEzsOW7ydRvDxgo77YF1BXfE1M9aWY8GsJXwzOiHirEXbmZRUJrZ0nQu22LBniStUMfFX6GmiWJm7f0c7zBqtB3Mjb"
    "9/dFdghr+yUeD/XSCLxk6HN74a5R32yysmA/SObtiKbbydhAJ53kwfskm8vnSJzL/3zudF0lDZ152g4tzyqpamZ4VTtEbpW0dPm+"
    "gq0BBN8QQvVlFczCK73+0pZCYn+IfAOPvbvhQ+0lpAfBZEf2gsFuH85udZzicBIj0s+n+XCOafetvDBh/L5xXyUiBDrwYB9Ske/P"
    "VQdqTLqH+wWWe3sLLXg/4wr/h6q8iMIjOnDmF1iDXRm9sBHuGSPcWg+SdwSEkQApcKZtwvA/2hu4M/ZQkHAgQEnicfhINLk47AZA"
    "gm6E29birhfmX2Jm4cyYMx13j8OE7FWFBxCBlBqUGjxkULDRD/OgRmmEvB4D/9zqxkJecwi1wz57Aun6omDYrX3SlmtjdzkQUTdE"
    "jnEUk1cTmEdpZtG2yRuiz+uS3Y4R54S4CxVyEvvdGsfs61Zh74M6ti+7tuC+GHv/IJtdAQbf+0MYHaJUhSgJTDS3cgK6LhL/Q2va"
    "JfAspu0AFjlZDpTsRfcZIYH7/I+uytxf4MxGjpCf3oE8eRXXTaEHsZwUJnYNZ7dvoCVQAYrFvo9/BvWD0e/hPqtQRxkWlqAC+/Xr"
    "X6k//3cPFut/3/E/U/9Oob3++a9/p9BbUf/6N0oPxci0Yfz1zZG4voHPrLSPSexf38Dwvn3+OwV+wjbIIwTbgjn+/Nf/B5Afg0w="
)
# --- END GENERATED UI ---
