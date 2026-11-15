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
UI_PAGE_SHA256 = "393197ead3c4b2bd4acb62932bb74a6743edc8d8bbfc5bc9d6219eec70492061"
UI_PAGE_BYTES = 1109377
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
    "df3U4GC39o0i4oxjA1Cywv8yWjqfEGhVnucaksp0t2qaUkvPGxWks1nEylYrPddOxIMLJuyyL4e5uuqgX/ZDYr8tSMS7j8rkbJcx"
    "5rzmedmoTkD2P3Wb9n/r/g2LXLKavdzlv2fi7/GuNzvZlVa0h2xFe7HbozaCZBwdx6vn8eFk8zCaxvc3/I9fRj98OP31hydPnn7+"
    "8PHHnz6Nnmz8/CR7Av/9hP+8P39O///Tx4ufdt69OYSkD0/T1Wy1W3zeOFs9Op083X50/Hz98MtPFx92/kh+evfi+IcnnZ93fzp/"
    "e/b7zi9J9MOP2c8n8aMft3+Zjj/mJ4PR83fPdj9kr199fLO68zrb+Wn6629PJuenO0/Gfzx5s/XwTbbz8Zffv0yef9l+uju8/DEq"
    "xg/Xuj+/ebi6/mrYzQ8/Pjx7++DlvY3fX20Nnq0+Wl1dXYF/7+0e/Xx0dO/wdPvlyvHq6qdf19cH059f5J3DaOu37Z+PBg/f/5yd"
    "dl78EG+PPg3PD492H3ZXosPV8/HRD+PfH/y0vvr58723Oy/frq6tPngWvRicFfGHJ89/fZVsHUZvTo5O1z4+//D76yeXT7Y+7H7q"
    "nD7f+i1dSV6fXzzfevbu0a+/r/zc3d5+Pjp+8sfpi8GnlXT75Wjj7OWouDfupq8H2+fDLz+8GSc///zwZP39z9OL6fTFj0/jH5+M"
    "LrL761/e5kly+PmX1fHo1davw4c/nSSfXz+fDt8V3Xz7wZtPP7w5enr49MXlSfb82e5pN4rXuisX67+9G22cng83fr2Y/Pjr2YPP"
    "H8/Ps/fJhw8/vNsGECevunl+/vv21oOd0danJx82zrc///bs0+ef3r+f7Dw9evJi7c3g7fDi1c/3XrwZdYZ58ejtx+Tdi/N499Uf"
    "6bvxD+/fDwZPRh9+PXqRF53ifnLU3RlEq39011fz15PdN+ll9vvDk/HF+PA0vXi5/qh4cNEZxL/lPw1Wjo4eHa0Oioc/fPzjcL37"
    "8Md0PF6Nn+1u/PJDvHJ/7fPZ60+H62+3OzCst9HgsEiPVx896gzS48nhs3evL6P3vz3rbP/8+nn28GE+WUvXvvw6zs4vd34brL0t"
    "Rj9/PH398eLhNDt79Lz7/IetD/n2x/Mf7j88++Pi5fT4fJy+vvcHoOaje9vHj95c/PTjL8kv7y521++lyfDp+M3/x9Z5LLfKbFH4"
    "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"
    "Ksf6cgDxBGC6A46Hn+tvlAbLHUVa7EGi9WupKSdldEUqJEH8xR1bcMqkkoqiJrf8I+D2A905WC3IiCOm1QscCdNipgfBZ8nTNCA/"
    "mWeK6/A5IToz5lwwxbx/hWf/kHHIP36QX1GCIOwKoOKnlgs4r2jlXVAkmtN3bfRvGJwWx6CXaWOY0B2fEi9/fpfV2F6Qql+Q+YF9"
    "foG/C5mDF2p7nTuC7lJ/NTXrGJMg1FAabvxecF0khxZtMkHNHYXFlw+OR6cTkcl36Kz/2HvTLsVxZGH4+/yK7Dp9+yYvJHhfsian"
    "hjUhWZMd6tTbGDBgMLaxzVqV//3RYhsDZsms6un73PP0zKlEcigUCkWEQlJIWjaG8qhQm4e5eGU0GrRW1K4/4+KrmJQQNultNmyn"
    "uhupPk9l4sNXerYVX6djKm4nxHCjnO0O1uU2t91l9fjzehhekQs9qdUEFcw1M2GtO2staJmZjXaLzsuSG5fYlqyFs8tkvkBV8tN5"
    "vFKeNFvS6yhZHXOUlMumu2p2ZExjpNap2ovX2Ho64fhdXn8O5+KKvRmwSn+xKi3S43a5HqvRu1pxlEub6i7W2aS7hVpXLryacdrO"
    "ZxMvWp3IGkONV5uEtaUys6VML+KD1nBiCVRzmmY63Tj93OiK025mzbKLWqn4AuOpywm2HpsoLWNd36Sl0URc1fuZzYY31T4zbZqd"
    "lWwPC6ntgBuWC0OKqb0kp4lyt5pqzXhefR03WsN4LT7pdGKKEjZq4njbzZETyhrPl1ou3QVmXK+3WvEUp3aEhV60XuRqbb2s2jVx"
    "pc2GuaSd7TLdDTVpZwlrrC02Y3Mxs8eUsXp+TVhTYdE16t10mFQ5LWHOK9P41NRWlcyOEjaFJDttCtUSkei8TGbzLBcG/tyC2Sgb"
    "Abgl1VQZTAfrTE5JSy1yU52z6Q6Vp8tpjZ6rmjmdxst2o7oCBjPeyNaU0dbsviwVe0tzRJ5dP9PPtLlZTvrplzSbL8UymVm1o+VX"
    "ZWuZzD6PrZJB1OkVMUtXi1tiZpHVVW3FrnPNF2a3m8UIW2Ntg7LnwJIzFcssztnNZq6m07scv441453CsBnvkwttM5rQ7apt9Ov5"
    "eUUip8tkN2G8SuUsFVutyNnQWLRV1SZfcyvL4LTctKhUtllFGzAVxSR3wGZ2qQWfo5ZWZbApq4Zss3GpzZa5WWM3ZvMcU+n31e0s"
    "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"
    "eK7WcqV2tqjka7VyvEO8zMZKPv1SGK4760y9X1wNYoIFOmWsiIVXYyVyzc2oUZx2FnJzw6iLDM9msvMK0Nb4gJ7XcuxmlbfyTHw4"
    "FfQ1kKs6/7qVS8SrBIZfS2qV0y9UJkez0nCT4mtZRR1MYzzVqSYUpS5ORT3BWQt9a4i83bayw37WijeWK9pKGWK+lYmJ3c5ubWfj"
    "1coCqFkqFa61VxqfJVWJar9UTH34Mq/KbPlluGDGk1WmvOvOjVx6ks0ku7nn8WgTXkjDMDtLruWFva2tm4NFfzadt+uVbbJolQ2m"
    "nIk3U3NxnpfzcS22zW740ZxkazV+LMw67XCpk5LCbGGUkhTNeH22iUwXTD2XC14pCwVxVNk2SraqGjw3NZv9Mhic602WoojUbDkY"
    "FVrD0qLET5v95XI2EoB3Tq4WnfKuw0xEmy+9dpbqumbxiZxOvA40tg0m/dp2PMgtp/PxZqJR5GK6llJ1tRCust1CnR+u6cTCaqn1"
    "8IxfMPXnYnoRI1ovVKOmCu3EM6x2MmyN++pO2pgqV2/orwadyQ0WNNFKriqlScpSY0LjWYHn4bRtYxk30klxQklqpsXJ5XWjEkvl"
    "hNLces6Un3et7ZDusPWw/tLRcoMGKU/Lr/P48HWYLeTj4/mU1/MboZtax1oSZdUyC3uzk18MRV0YVr0uUjbXqj4XSsZgkG3UivLG"
    "3hQam/Jq/jxuVCbZRmc3GmcL81Y5Vu5r1OvInK7NemPXH6X4YptmGyaTfTV3xHM90WmsF5X6IJEvpMnxM9Ne2bltcR5mmVhxUZza"
    "6deiTrVe2FJ4prS1JUl3snqSMxRg+wblblJO2Ot1cjmwaa1hT17HSTL9ss0t11OqO6XbmU1l0REomZtanR0t0CmzvB7YU+ACpdVX"
    "g7N5taDM2fnCfKFHDAdckJdlvms8G0leakkLOrfW1c1MKTbodXGuTF77G7E1MVbJKjUqyuv2ZqoafVDnlq2rzfhwvGhPuN2Ktnml"
    "Uxi0ZkyRmnT6RWn20m7R4iqzNafjqg3cUHH0+sql6MRmMIDH8jJybPuS7ZsKv57WOnatJAvpWlfq8C85rSITKTa+E3XZJCkhOY/X"
    "K/OEJZLrhKV2Uslhlm+NiU5/XI0vjWpOzdfTqVh4IuXtilTN0vGsxNT7L2Asl8bCeNmxiqbM1u3BluwnUkQRWAcgdIzeJBJ9jd5m"
    "8vF1XV/nxPi8yo+JGFVQE3VaNGOvbTldFBrAwzcqtSWZUEorm26/jBaTUrLxoqfjHPU63/StojiNs8luVmdGK2nc5qn+C9xtz3ef"
    "n6nUeCZl7O4mt6hwehVMNvRV3LCaK9psDOR1v8M21Uycn5MbLtWoDCSZ2CWbrEybokYvXpeF6TNVqOyYbWycS6uUWXimlc4sX5pu"
    "wjGDSYkiMxuZ6SnXmYflWXM0GvVblSaRLAlMhia4Slcu7qo6+TxYhGuz4UguZdn+s9oaxrjWYlmo8jLHjCpMYkQWB9aaWs+KNS2p"
    "LZM1mSWX0/UqLhAvTWodbxRasTVPAXve5tLzOk+uh0txtn3hY6JZWteSFTM8X7f5fuYln3nOSt2dQk9Ax6Squ5RVzVLl1ZqrZZlR"
    "uZp7bqWY1rjaWPLJtCUSpbr4UggXheSs3xSzxXZqt5klXtcTOTNg87VMXGuZaYE21Pl8s2YSRH7WSa+reiofLzftwXD7HOPVkb5j"
    "VsRLahZLmrkUmdQII5upMPO4Ki8nuewm3HrVZ/lcxdrwY24Ti730X9RdNrYT50p/NVtsJT73/PpsToYU/yIlO2GTSw/WqRe2Ws8O"
    "wPRgIzTq5mt8KnTGryngUZRz6Re90x7u1G1sFV9XC5XcoGuJE64dS1L1ebNsz7l2ajhpdFfD0ixtTkiyOOIsQ6FnzGtd7A5GlCgn"
    "Z7pWrxXyteki+cLX5ELDWtlssvScs8KjNGPPkrnB1GiLtdqKytqTONsa8Z2YKM7tdXm2E8pddfRqzFU5W2WJ7LzZDTdaGZoNC2Qs"
    "vkjyS2ISD7/y442uDZSpuCwyRmdW1IopPT3qVtXtjLbntXxhJ7aeU9ZIoKjmdsmuZ43ythvOyMPNcCVYChV+TVXLJDHSh2EpNX2p"
    "5TuMWhkUrYY8ny/jrd3mOVyjql22q8obs5pbxEpaVsxZxq6obYqEVX0eSMN4fRqrz5Ttqv1ciKerSWqZ52c1Jt5oU9LQ1vMjtrRT"
    "m0oq3zKbllidLjOK2C28JJh4vK1O2UI2oRRGaelZruYrs1xuBWzAc6spdI3dZDNY8rNZpit02zV+Y5TpxQv9CtyJ7Ep54RL2mGTM"
    "Va1GNkX2ebQcC3020yivyJmdXBGbhpAcpFvNjTqrmJvdZGE1R3SfM2LAz8+kykV1SWY6hBaXeDUeVhthJky0E+QgLWbUSvaFSIzU"
    "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"
    "ToLVASk30hy733mUmafpAPY3/HeljXy5mtjlU21xk+CwlSiqt+hrLY7SQ3QH4TOS+kNr2p8uOLSmpkGmCkSvQ9Bzc0zZFnfatQTu"
    "oiUwdU/zUTDqBv5KVpEOapfuzPLaRlNsYIFyikrojq5iwZT4jjhbhFuhkYR6Qi8ojNE4wVjBpnQAYhxomE9BfCGcOvulRFUeSNFY"
    "T2Ge2ZK+UtghZB6TbSHyk/7f0jRb4iUo8wn10PMiNnq85K2RbYuqk93moGWfNmgNg1U3SCydnB0a8sr59FDKKS8MOeV5Oy7t/Fvi"
    "0s5tLu3tt8ylvfk8XNrbNlza+y/Lpb39Klza+yqX9vELcmkfDS7t1MulnS/g0k41l3b+xbm086/Ppf2uZLt8fj6lLdoeO4S3tIba"
    "EM+0K+ERpxypoc5wgRf/i+k4MeA5iJ7FaVZuxOOxnZAnF9P3RsEkB0WEbKxAGPorfA06c5oAAeiNHwIAhQdwbI7TYjaJPzYVgiZg"
    "TYAIwN9QJxehE2A5h2J8miI4n6P9KfSarTwX5HyE49Iq58+yjcWiIsfjhQWqDksxTT1wwkX8+2M1v4XfLHMLvYxxvoWztsglwTwq"
    "uCCYlc1VXwnD2DZfMN+4zBc0D8t8QNOxzAdoF7xUBePxsp+8pC217FfU9WU/agSSEFmOYPkni/PhjjNBQ7xbSmddgB4iBjubXVqA"
    "F7U5q5AatUos8VCjW0L3FaAvv6ZFSudaV5ahtqNVsqIPQgcmPuc8CPzKflFQzIXEb30F7EpSClxfzk7xCJ+nBVDvhItaoJfyfbe2"
    "1g9OP3SmZ2fBULxXjlZ13zByc2hlgPPybCz0WWa6zJUd8vOP6TgJUBfgMbqWkmixhIQeRTwdiwc4C04si0TP+/2kI4+ogQhl60yH"
    "0vkSuTrePOkoWheZH8iZ6usSw56/xLrG6JLnNkqHx0Zbs+zA496+kfYcOZS2Zs1ZvVlz1sKsOftiZs3QCuZv9AHkC8DtahTO07fn"
    "EzRXRq8WUS+5+KopVc7GCatKQtIU4BLn+qpKnDck/jBXQrifWItBr0s73ViN5GUxSoIuDKP3275vhUa15cHq7kvOHImEZmO8CxlY"
    "cqdt9G2fcWf9K7vvLSm0goZarJ7/lYr/6HvLzKd4dU5kZB5RYnU2zM9NnjISzKTuRGQMVK9uC8/bNwhFmZXmOISNzkYfDaMXFiEj"
    "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"
    "2kalttXYWmlWturVra2VWquysQXv4U+1sVXbrW1W6luN2gr+2dpcgcd2rVlbaVeqW/UNKN6u1Da26vDcam9sQPPtSqNRx+9b7Xqr"
    "hd+b0NtWpY5v4WmjudWGx2Z1q9bG0htbjU183tpsbeD3Vn2zCc8brXa9Tc8bVXxu1dq1FpZvtWpb+Nysb/H3zRp9b9U35HkT229t"
    "wv+ofLtK5duNTYIW2sX+Wls0eHxutui52Why+Y0Nem416vy9RfW3Ntstft7k71v1+mt6buPzZrVW2/wZ/9ZrG7v2+zoPa3OrQY+t"
    "Tex2pVbdVW9rVcSwdAaV6HlzI/e89TP9bbdfKyDguQGD2FVA0jMjmQZBz4BcNUh63tjcVUig5y1BSpXr11p1jUR8hlnbVUjG5wZM"
    "jpoEfN7Y1HOEj22eU5pDeG42avSd5hieN0BS1WsAn7cYfFwh8AhTRtDQAqrVKtXaZkMvMHhu1Jobu2oBwvNWFbuR9VmrA3KrDb1+"
    "YZ03t1qwfmV9w98qNi/LH4ptNnHwVfq5sduqbG0B/PwEu6FdbdU2VK0GrddN3Sj21Wpv6U7rlVp7A58VUJV2s9quGaABY5s8CB5U"
    "ZaPRZpzxoCvNjSqjlHEC/bVwUApnlcZmvWXhtNIAOAzKAWVtmaEN+lpvb2yZCYPner1lJhSA2qrVzYTDn8162ywIeN5o1s2CoUFY"
    "CwqeG7WaWXDwXG9uqQX5Gp9rG7UVWbA/ywKmdho88/Ut3O0AbXOLy23iQocp2KI52VWfYMfAfmquqKq4gxryjF3IhvtZNuBrBYps"
    "0F0Fqt7AMhS9wWWomgAIKphA8FARVUxA2hqVmsAIqpkAUXmaCSZQeqI0/ZJ5ZPqGn3memf419TrQ9FHWCZFP3KKyjpi6buh1pqiv"
    "WodMndsrap0K8VbLWNF2tcqZ9iPN5z2AZ8OKHBi/4cnRxB2yCWuz1digh5WNyiYgpAFVYH/U4N0G7FroB0Zb3dptVLZqNWiwXcGD"
    "rIkdNxGtbdweG9hBrbFJdLXZ2IL9gZtys0l0GWalDnBvVTdaiDcYVrUGz20YP67IXfUJFg3M5IqqSWu91dYt485pVbFl7hl3HqBk"
    "RUEGz20FNexixMeuGhPscsTHihowEAHGB/3YheLNaqNFT0RCmpV6rWWqwftmC0BRzQJFqbapx80tOWA3cO4FInhut+oNDXENZ6Gu"
    "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"
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
