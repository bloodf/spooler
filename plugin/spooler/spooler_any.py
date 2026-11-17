# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.28.0"
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
PLUGIN_VERSION = "0.28.0"
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
        "save_calibration": "ask",
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
            if "save_calibration" not in saved and not parse_flag(saved.get("send_saved_copies"), True):
                saved = {**saved, "save_calibration": "never"}  # the older on/off setting
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
    "save_calibration": lambda v: parse_calibration_mode(v),
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
        if isinstance(raw, dict) and "save_calibration" not in raw and "send_saved_copies" in raw \
                and not parse_flag(raw["send_saved_copies"], True):
            stored = {**stored, "save_calibration": "never"}  # an older config's "don't send saved copies"
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
                "spool_columns": 1, "auto_send": True, "save_calibration": "ask",
                "auto_keep_slots": False}
    return config_view(defaults)  # The Spoolman address and source stay: they are yours.


def get_spools(spoolman_url: str) -> dict:
    """Return ``{"ok": True, "spools": [...]}`` or ``{"ok": False, "error": "..."}``."""
    path = "spool?allow_archived=true" if display_settings()["archived"] else "spool"
    try:
        data = _spoolman_open(spoolman_url, path)
        if not isinstance(data, list):
            raise ValueError(tr("Spoolman sent a spool list Spooler doesn't understand"))
        data = [spool for spool in data if isinstance(spool, dict)]
    except urllib.error.URLError as exc:
        error = tr("Could not reach Spoolman at {url} ({reason})", url=spoolman_url, reason=exc.reason)
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
    return [tr("Spooler: {spool} is down to {grams} g", spool=_spool_label(s), grams=fmt_num(s["remaining_weight"]))
            for s in fresh]


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
        raise urllib.error.URLError(tr("the address must start with http:// or https://"))
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
        return {"ok": False, "error": tr("No Spoolman URL configured yet")}
    try:
        data = _spoolman_open(spoolman_url, "info")
        if not isinstance(data, dict):
            raise ValueError("not a JSON object")
    except urllib.error.URLError as exc:
        error = tr("Could not reach Spoolman at {url} ({reason})", url=spoolman_url, reason=exc.reason)
        log.warning("Connection test failed: %s", error)
        return {"ok": False, "error": error}
    except ValueError:
        # Not JSON, or not an object: a web page or another service at that address. Raising here
        # would leave the page's Test Connection waiting, and every later test ignored.
        error = tr("{url} answered, but not like Spoolman does", url=spoolman_url)
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
    region = BAMBU_REGIONS.get(auth.get("region"), "Global")
    region = tr(region)
    if auth.get("user"):
        return tr("Signed in as {user} ({region})", user=auth["user"], region=region)
    return tr("Signed in ({region})", region=region)


def read_auth() -> dict:
    """Sign-in result: ``{"ok": True, token, ...}`` or ``{"ok": False, "error", ...}``."""
    try:
        data = json.loads(AUTH_FILE.read_text(encoding="utf-8"))
        token = data["access_token"]
    except FileNotFoundError:
        return {"ok": False, "account": tr("Signed out"), "signin": True, "error": tr("Signed out")}
    except (OSError, ValueError, KeyError, TypeError):
        log.exception("Could not read %s", AUTH_FILE)
        return {"ok": False, "account": tr("Signed out"), "signin": True,
                "error": tr("Your saved Bambu sign-in is unreadable")}
    auth = {"token": token, "region": parse_region(data.get("region")),
            "user": str(data.get("account") or "")}
    auth["account"] = account_text(auth)
    expiry = jwt_expiry(token)
    if expiry is not None and expiry < time.time():
        return {**auth, "ok": False, "account": tr("Sign-in expired"), "signin": True,
                "error": tr("Your Bambu sign-in has expired")}
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
    return tr("Bambu blocked the request (HTTP 403)") if code == 403 else tr("Bambu Cloud returned an error (HTTP {code})", code=code)


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
        raise BambuError(tr("Could not reach Bambu Cloud ({reason})", reason=exc.reason)) from None
    try:
        data = json.loads(raw) if raw.strip() else {}
    except ValueError:
        raise BambuError(tr("Bambu Cloud sent a reply Spooler doesn't understand")) from None
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
            raise BambuError(tr("Signed in, but Spooler could not save the sign-in to {folder}", folder=AUTH_FILE.parent)) from None
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
    raise BambuError(tr("Bambu Cloud didn't sign you in"))


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
                raise BambuError(tr("Enter your Bambu email and password"))
            reply, cookies = _bambu_post(region, LOGIN_PATH, {"account": account, "password": password})
            return _after_login(region, account, reply, cookies)
        if not _pending:
            raise BambuError(tr("Your sign-in timed out. Enter your email and password again"))
        region, account = _pending["region"], _pending["account"]
        if action == "resend":
            _send_code(region, account)
            return {"ok": True, "step": "code"}
        code = str(data.get("code") or "").strip()
        if not code:
            raise BambuError(tr("Enter your Bambu Lab verification code"))
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
        raise ValueError(tr("Bambu Cloud sent a reply Spooler doesn't understand"))
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
            tr("slot {n}", n=item["slotId"]) if item.get("slotId") not in (None, "") else "",
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
            return {"ok": False, "error": tr("Bambu Cloud didn't accept your sign-in"),
                    "account": auth["account"], "signin": True}
        return {"ok": False, "error": tr("Bambu Cloud returned an error (HTTP {code})", code=exc.code),
                "account": auth["account"]}
    except urllib.error.URLError as exc:
        return {"ok": False, "error": tr("Could not reach Bambu Cloud ({reason})", reason=exc.reason),
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
        error = _sentences([result["error"] + tr("."), tr(SIGN_IN)]) if result.get("signin") else result["error"]
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
    raise last or RuntimeError(tr("No OrcaSlicer user folder accepted the presets"))


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
            publish_stock(origin[0], [], result.get("error") or tr("Spoolman could not be read"), wants["request"])


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
                raise RuntimeError(tr("OrcaSlicer's data folder was not found"))
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
    return {"ok": False, "error": tr("The spool source kept changing while loading; refresh to try again.")}


def start_preset_sync(post) -> None:
    """Sync Presets: read Spoolman now and rebuild every Spooler filament preset, even when nothing
    changed. Call it on the UI thread; post() gets {"type": "sent", "ok": ..., "text": ...}."""
    if source() != "spoolman":
        post({"type": "sent", "ok": False, "text": tr("Syncing presets needs Spoolman as the source.")})
        return
    snapshot = refresh_snapshot()
    if snapshot is None:
        post({"type": "sent", "ok": False, "text": tr("Could not read OrcaSlicer's presets.")})
        return

    def worker():
        result = fresh_spools(snapshot, force=True)
        state = result.get("profiles") or {}
        if not result.get("ok"):
            ok, text = False, result.get("error") or tr("Could not read Spoolman.")
        elif state.get("error"):
            ok, text = False, tr("The filament presets were not rebuilt: {error}", error=state["error"])
        else:
            ok, text = True, tr("Synced {count} filament presets from Spoolman.", count=state.get("count", 0))
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


class VersionUnknown(RuntimeError):
    """Spoolman's version couldn't be read, so how it stores extra fields is unknown."""


class OriginChanged(NotSent):
    def __init__(self):
        super().__init__(tr("The spool source changed in Settings while this ran, so Spooler stopped "
                            "before writing anything more. Try again."))


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
        raise NotSent(tr("Spoolman is not the spool source."))
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
        raise RuntimeError(tr("Open a Spooler preset in OrcaSlicer's filament settings and change it first."))
    name = edited.name[len(PROFILE_PREFIX):]
    changes = {key: (edited.config_value(key), saved.config_value(key)) for key in edited.config_keys()
               if edited.config_value(key) != saved.config_value(key)}
    if not changes:
        raise RuntimeError(tr("{name} has no unsaved changes to send.", name=name))
    return name, changes


# Spoolman versions whose behaviour a write depends on, read from Spoolman's own source:
# from 0.22.0 a PATCH's extra map is merged key by key (before, it replaced the whole map), from
# 0.26.0 a null value there empties a key (before, it was refused), and
# since at least 0.18.0 PUT spool/<id>/use adds use_weight to used_weight in one SQL UPDATE,
# clamped at 0, whatever its sign.
SPOOLMAN_EXTRA_MERGE = (0, 26, 0)  # merged, and null empties a key
SPOOLMAN_EXTRA_PARTIAL = (0, 22, 0)  # merged key by key
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
        raise RuntimeError(tr("{name} is no longer a Spooler preset. Refresh, then send it again.", name=name))
    filament = spoolman_call("GET", f"filament/{int(fid)}")
    base = orca_settings_data(filament)
    data = orca_settings_data(filament)
    if data is None:  # Never overwrite what can't be read back.
        raise RuntimeError(tr("The {field} field of {name}'s filament isn't a JSON object; "
                              "fix it in Spoolman, then send again.", field=ORCA_SETTINGS_FIELD, name=name))
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
            raise RuntimeError(tr("The {field} field of {name}'s filament changed in Spoolman "
                                  "and isn't a JSON object now; fix it in Spoolman, then send again.",
                                  field=ORCA_SETTINGS_FIELD, name=name))
        data, clashes = merge_settings(base, data, remote, target)
        for key in clashes:
            if key in sent:
                sent.remove(key)
                kept.append(key)
                native.pop(NATIVE_KEYS.get(key), None)
                patch.pop(NATIVE_KEYS.get(key), None)
        kept.sort()
        value = json.dumps(json.dumps(data))
        version = spoolman_version(fresh=True)
        if version is None:
            # Unknown, it could replace the whole map or merge it: write nothing rather than guess.
            raise VersionUnknown(tr(EDITOR_NO_VERSION))
        if version >= SPOOLMAN_EXTRA_PARTIAL:
            # Spoolman merges extra key by key (from 0.22): send only the one field this changes.
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
        notes.append(tr("Sent {settings} to Spoolman for {name}.", settings=", ".join(sent), name=name))
    if kept:
        notes.append(tr("Kept Spoolman's newer value for {settings}: the preset now has it, and your "
                        "change stays unsaved; send again to use yours, or discard it.", settings=", ".join(kept)))
    if other:
        notes.append(tr("Not sent: {settings}. Spoolman's {field} field holds only "
                        "calibration settings; colour, vendor, material and name come from its own fields.",
                        settings=", ".join(other), field=ORCA_SETTINGS_FIELD))
    if rebuild_error:
        notes.append(tr("The presets were not rebuilt: {error}", error=rebuild_error))
    return _sentences(notes)


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
    # Calibrated values follow "Save calibrated values to Spoolman": asked about (Ask), left
    # unsent (Never) or sent with the rest (Automatically). Sending only the other settings leaves
    # the calibrated ones in orca_settings as Spoolman has them: the send merges key by key.
    mode = calibration_mode()
    calibrated = {key: value for key, value in changes.items() if key in CALIBRATION_KEYS}
    if calibrated and mode != "auto":
        changes = {key: value for key, value in changes.items() if key not in CALIBRATION_KEYS}
        if mode == "ask":
            offer_calibration(name, calibrated)
    if not changes:
        return
    log.info("Sending %s's edits to Spoolman", name)
    start_send(post, (name, changes), auto=True)


# Save on a Spooler preset makes a separate user copy (OrcaSlicer can't save over a plugin's
# preset). When that copy was made from a Spooler preset, its changed calibration settings are
# offered for Spoolman too (or sent, or left, as "save_calibration" says), so the next rebuild of
# the Spooler preset has them. The copy itself is left as it is.
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


CALIBRATION_MODES = ("ask", "auto", "never")
# Units of the calibration values Spooler has its own Spoolman fields for, shown beside them.
# The calibrated values "Save calibrated values to Spoolman" holds back from unsaved edits.
# One read-modify-write of the waiting prompts and skips at a time: the UI thread adds prompts
# while a send's worker thread puts a failed one back.
_calib_lock = threading.Lock()
CALIBRATION_KEYS = frozenset(key for key, _label, _unit in CALIBRATION_FIELDS.values())
# Units shown beside the values in a prompt (OrcaSlicer's own units for these settings).
CALIBRATION_UNITS = {
    **{key: unit for key, _label, unit in CALIBRATION_FIELDS.values() if unit},
    **dict.fromkeys((*BED_TEMP_KEYS, "nozzle_temperature", "nozzle_temperature_initial_layer",
                     "nozzle_temperature_range_low", "nozzle_temperature_range_high", "chamber_temperature",
                     "temperature_vitrification"), "°C"),
    **dict.fromkeys(("filament_retraction_speed", "filament_deretraction_speed", "filament_ironing_speed",
                     "slow_down_min_speed"), "mm/s"),
    **dict.fromkeys(("filament_retraction_length", "filament_z_hop", "filament_ironing_spacing",
                     "filament_ironing_inset", "filament_diameter"), "mm"),
    **dict.fromkeys(("fan_min_speed", "fan_max_speed", "overhang_fan_speed", "additional_cooling_fan_speed"), "%"),
    "filament_density": "g/cm³", "slow_down_layer_time": "s", "filament_minimal_purge_on_wipe_tower": "mm³",
}


def parse_calibration_mode(value: object) -> str:
    return value if value in CALIBRATION_MODES else "ask"


def calibration_mode() -> str:
    """Save calibrated values to Spoolman: ask (the default), auto or never."""
    return parse_calibration_mode(get_settings().get("save_calibration"))


def save_calibration_mode(value: object) -> None:
    if value in CALIBRATION_MODES:
        save_settings({**get_settings(), "save_calibration": value})


def _asks() -> dict:
    """Change sets waiting for Save or Skip, kept in the settings file so a restart doesn't lose
    them: {Spooler preset name: {setting: (new, old)}}, oldest first."""
    saved = get_settings().get("calibration_asks")
    asks = {}
    for name, changes in (saved.items() if isinstance(saved, dict) else ()):
        if isinstance(changes, dict):
            asks[str(name)] = {str(key): (str(pair[0]), str(pair[1])) for key, pair in changes.items()
                               if isinstance(pair, (list, tuple)) and len(pair) == 2 and key in ORCA_SETTINGS_KEYS}
    return {name: changes for name, changes in asks.items() if changes}


def _save_asks(asks: dict) -> None:
    save_settings({**get_settings(), "calibration_asks": {
        name: {key: list(pair) for key, pair in changes.items()} for name, changes in asks.items()}})


def calibration_asks() -> list[dict]:
    """The change sets waiting on the page, oldest first."""
    return [{"name": name, "changes": [{"key": key, "old": old, "new": new, "unit": CALIBRATION_UNITS.get(key, "")}
                                       for key, (new, old) in sorted(changes.items())]}
            for name, changes in _asks().items()]


def _calib_mark(changes: dict) -> dict:
    return {key: new for key, (new, _old) in changes.items()}


def _post_asks() -> None:
    send_plate_message({"type": "calibration", "asks": calibration_asks()})


def offer_calibration(target: str, changes: dict) -> None:
    """Put a change set up for Save or Skip on the page, unless it was skipped or is already
    waiting as it is."""
    with _calib_lock:
        # Skipped values aren't asked about again until they change.
        if (get_settings().get("calibration_skipped") or {}).get(target) == _calib_mark(changes):
            return
        asks = _asks()
        if asks.get(target) == changes:
            return
        asks.pop(target, None)
        _save_asks({**asks, target: changes})
    push_notice("info", tr("Spooler: {name} has new calibrated values. Open Spooler to save them to "
                           "Spoolman or skip them.", name=target))
    _post_asks()


def send_saved_copy(name: str) -> None:
    """On PresetSaved: offer a saved copy's calibration changes for Spoolman, or send them when
    the setting says so. Never raises."""
    try:
        mode = calibration_mode()
        if source() != "spoolman" or mode == "never":
            return
        edits = saved_copy_changes(name)
        if edits is None:
            return
        if mode == "ask":
            log.info("%s was saved from %s; asking before sending its changes to Spoolman", name, edits[0])
            offer_calibration(*edits)
            return
        log.info("%s was saved from %s; sending its changes to Spoolman", name, edits[0])

        def done(result: dict) -> None:
            push_notice("info" if result.get("ok") else "warning", tr("Spooler: {text}", text=result.get("text")))

        start_send(done, edits)
    except Exception:
        log.exception("Could not send the saved copy %s to Spoolman", name)


def answer_calibration(data: dict, post) -> None:
    """The page's Save or Skip for one waiting change set. Save sends it the usual way (read again
    and merged just before writing); Skip remembers the values so the same ones aren't asked again."""
    name = str(data.get("name") or "")
    skip = data.get("type") == "calibration_skip"
    with _calib_lock:
        asks = _asks()
        changes = asks.pop(name, None)
        if changes is not None:
            _save_asks(asks)
            if skip:
                settings = get_settings()
                skipped = {**(settings.get("calibration_skipped") or {}), name: _calib_mark(changes)}
                save_settings({**settings, "calibration_skipped": skipped})
    if changes is None or skip:
        post({"type": "calibration", "asks": calibration_asks()})
        return

    def done(result: dict) -> None:
        # On the worker thread, while the UI thread may be adding a prompt: hence the lock.
        with _calib_lock:
            if not result.get("ok"):
                asks = _asks()
                if name not in asks:  # not written: still waiting, unless a newer set replaced it
                    _save_asks({**asks, name: changes})
            else:
                settings = get_settings()
                skipped = dict(settings.get("calibration_skipped") or {})
                if skipped.pop(name, None) is not None:
                    save_settings({**settings, "calibration_skipped": skipped})
        post(result)
        post({"type": "calibration", "asks": calibration_asks()})

    start_send(done, (name, changes))


def start_send(post, edits: tuple | None = None, auto: bool = False) -> None:
    """Send the unsaved changes of the Spooler preset open in OrcaSlicer to Spoolman. Call it on the
    UI thread; post() gets {"type": "sent", "ok": ..., "text": ...} when it is done."""
    try:
        if _auto["busy"]:
            raise RuntimeError(tr("Already sending to Spoolman; try again in a moment."))
        if source() != "spoolman":
            raise RuntimeError(tr("Sending needs Spoolman as the source."))
        snapshot = refresh_snapshot()
        if snapshot is None:
            raise RuntimeError(tr("Could not read OrcaSlicer's presets."))
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
            # The next tick tries again, but not after an unreadable version: that would fail and
            # report every 10 s. The same edits are then sent again only by hand or once they change.
            if auto and not isinstance(exc, VersionUnknown):
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


def stage_text(code: object) -> str | None:
    """A Bambu print stage (stg_cur) in the page's language; None for a code Spooler doesn't know."""
    stage = STAGES.get(_int(code))
    return tr(stage) if stage else None


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
            "layers": num("total_layer_num"), "name": name[:80], "stage": stage_text(p.get("stg_cur")),
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
        return {"ok": False, "text": tr("Setting a printer's spool needs Spoolman as the spool source.")}
    if spool_id is not None:
        number = spool_id if isinstance(spool_id, int) and not isinstance(spool_id, bool) else -1
        if number <= 0 or _spool_by_id(number, _spool_cache["spools"] or []) is None:
            return {"ok": False, "text": tr("That spool isn't in Spoolman, or it is archived.")}
    entry = _local.get(str(pid))
    link = entry["link"] if entry else None
    with _live_lock:
        state = _live["printers"].get(str(pid)) or {}
        single = bool(state.get("spool_set"))
    if not link or link.get("kind") != "moonraker" or not single:
        return {"ok": False, "text": tr("Spooler can only set the spool on a single-extruder Klipper printer.")}
    base = link["ip"]
    try:
        doc, heads = moon_poll(base)  # read again: the printer decides, not the page
        if heads or "vt_tray" not in doc["print"]:
            with _live_lock:
                moon_mark(str(pid), doc, heads)
            return {"ok": False, "text": tr("{printer} manages its own spools; Spooler only reads them.", printer=link["name"])}
        busy = str(doc["print"].get("gcode_state") or "").upper()
        if busy in LIVE_STATES and not confirmed:
            return {"ok": False, "confirm": True, "state": busy,
                    "text": tr("{printer} is paused in a print: Moonraker would book the rest of this print to the "
                               "new spool. Confirm to change it anyway." if busy == "PAUSE" else
                               "{printer} is running a print: Moonraker would book the rest of this print to the "
                               "new spool. Confirm to change it anyway.", printer=link["name"])}
        # Body per https://moonraker.readthedocs.io/en/latest/external_api/integrations/#set-active-spool
        # {"spool_id": <id>} sets the active spool; {"spool_id": null} clears it and stops tracking.
        _moon_post(base, "/server/spoolman/spool_id", {"spool_id": spool_id})
        doc, heads = moon_poll(base)
    except Exception as exc:  # the page waits for an answer: any failure is one
        log.warning("Could not set the spool on %s: %s", link["name"], exc)
        return {"ok": False, "text": tr("Could not set the spool on {printer}: {error}", printer=link["name"], error=exc)}
    live_apply(str(pid), link["name"], doc, link=str(pid), full=True)
    with _live_lock:
        moon_mark(str(pid), doc, heads)
    if spool_id is None:
        return {"ok": True, "text": tr("{printer}: no active spool, Moonraker stopped booking usage.", printer=link["name"])}
    return {"ok": True, "text": tr("{printer} now books its usage to spool #{id}.", printer=link["name"], id=spool_id)}


def start_moon_spool(data: object, post) -> None:
    """Run moon_set_spool off the UI thread, then post the result and the refreshed live state."""
    data = data if isinstance(data, dict) else {}

    def work():
        result = {"ok": False, "text": tr(STALE_LIST)} if data.get("spool") is not None and stale_list(data) \
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
                row.update(state="unknown", error=row.get("error") or tr(UNKNOWN_TEXT))
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
    return " ".join(part for part in (vendor, filament.get("name") or tr("Spool {id}", id=spool.get("id"))) if part)


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
        return tr("Spoolman refused it (HTTP {code})", code=exc.code)
    if isinstance(exc, urllib.error.URLError):
        return tr("Could not reach Spoolman ({reason})", reason=exc.reason)
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
DRIED_NO_CLEAR = ("This Spoolman can't remove a spool's dried date; Spoolman 0.26 or newer can. Nothing was written; "
                  "mark it dried again to change the date.")
DRIED_NO_EXTRA = ("Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them "
                  "on a change. Nothing was written.")


def _dried_extra(sid: int, value: str | None) -> dict | str:
    """The extra map to PATCH for the dried date, or why nothing may be written.

    From Spoolman 0.22.0 the map is merged key by key: only the dried key is sent. Only from 0.26.0
    does a null remove it, so on 0.22 to 0.25 the date can be set but not removed. Before 0.22 a
    PATCH replaced the whole map, so the spool's extra fields are read again and sent back whole,
    with only the dried key changed. A change made by someone else between that read and the PATCH
    can still be lost there: Spoolman's PATCH has no precondition.
    """
    version = spoolman_version(fresh=True)
    if version is None:
        return tr(DRIED_NO_VERSION)
    if version >= SPOOLMAN_EXTRA_MERGE or (version >= SPOOLMAN_EXTRA_PARTIAL and value is not None):
        return {DRIED_FIELD: value}
    if version >= SPOOLMAN_EXTRA_PARTIAL:
        return tr(DRIED_NO_CLEAR)
    spool = spoolman_call("GET", f"spool/{sid}")
    extra = spool.get("extra") if isinstance(spool, dict) else None
    if not isinstance(extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in extra.items()):
        return tr(DRIED_NO_EXTRA)
    kept = {k: v for k, v in extra.items() if k != DRIED_FIELD}
    return {**kept, DRIED_FIELD: value} if value is not None else kept


def _spool_write(action: str, sid: int, data: dict) -> dict:
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    if action in ("weigh", "use"):
        grams = _action_grams(data.get("grams"))
        if grams is None:
            return no(tr("Enter a weight between 0 and {max} g.", max=fmt_num(MAX_GRAMS, group=True)))
        if action == "use":
            spoolman_use(sid, grams)
            return {"ok": True, "text": tr("Used {grams} g of spool #{id}.", grams=fmt_num(grams, 1, group=True), id=sid)}
        spoolman_call("PUT", f"spool/{sid}/measure", {"weight": round(grams, 1)})
        return {"ok": True, "text": tr("Spool #{id} set from a scale weight of {grams} g.", id=sid, grams=fmt_num(grams, 1, group=True))}
    if action in ("archive", "unarchive"):
        spoolman_call("PATCH", f"spool/{sid}", {"archived": action == "archive"})
        return {"ok": True, "text": tr("Spool #{id} archived." if action == "archive" else "Spool #{id} unarchived.", id=sid)}
    if action == "move":
        location = data.get("location")
        if not isinstance(location, str) or len(location.strip()) > LOCATION_MAX:
            return no(tr("A location is text of at most {max} characters.", max=LOCATION_MAX))
        location = " ".join(location.split())
        spoolman_call("PATCH", f"spool/{sid}", {"location": location or None})
        return {"ok": True, "text": tr("Spool #{id} moved to {location}.", id=sid, location=location) if location
                else tr("Spool #{id} has no location now.", id=sid)}
    if action in ("dried", "clear_dried"):
        ensure_fields()
        value = json.dumps(f"{today().isoformat()}T00:00:00+00:00") if action == "dried" else None
        extra = _dried_extra(sid, value)
        if isinstance(extra, str):
            return no(extra)
        spoolman_call("PATCH", f"spool/{sid}", {"extra": extra})
        return {"ok": True, "text": tr("Spool #{id} marked as dried today." if action == "dried"
                                       else "Spool #{id} has no dried date now.", id=sid)}
    if action == "remaining":
        grams = _action_grams(data.get("grams"), zero=True)
        if grams is None:
            return no(tr("Enter the grams left, from 0 to {max} g.", max=fmt_num(MAX_GRAMS, group=True)))
        spoolman_call("PATCH", f"spool/{sid}", {"remaining_weight": round(grams, 1)})
        return {"ok": True, "text": tr("Spool #{id} now has {grams} g left.", id=sid, grams=fmt_num(grams, 1, group=True))}
    if action == "comment":
        text = data.get("comment")
        if not isinstance(text, str) or len(text.strip()) > COMMENT_MAX:
            return no(tr("A note is text of at most {max} characters.", max=COMMENT_MAX))
        text = text.strip()
        spoolman_call("PATCH", f"spool/{sid}", {"comment": text or None})
        return {"ok": True, "text": tr("Saved the note on spool #{id}." if text else "Spool #{id} has no note now.", id=sid)}
    if action == "add":
        fid = _pos_int(data.get("filament"))
        if fid is None:
            return no(tr("That spool has no filament to copy."))
        count = data.get("count", 1)
        if _pos_int(count) is None or count > ADD_MAX:
            return no(tr("Add 1 to {max} spools at a time.", max=ADD_MAX))
        made: list[str] = []
        for _ in range(count):
            try:
                made.append(f"#{(spoolman_call('POST', 'spool', {'filament_id': fid}) or {}).get('id', '?')}")
            except Exception as exc:
                if not made:
                    raise
                # Each POST is its own spool: say which ones exist, so none is added twice by a retry.
                log.warning("Adding spool %d of %d failed: %s", len(made) + 1, count, exc)
                return no(tr("Added spool {spools}, then Spoolman refused the next one: {error}",
                             spools=_join(made), error=_spoolman_error(exc)))
        if count == 1:
            return {"ok": True, "text": tr("Added spool {spool} of the same filament.", spool=made[0])}
        return {"ok": True, "text": tr("Added {count} spools of the same filament: {spools}.", count=count, spools=_join(made))}
    url = getattr(_op, "origin", None)[0] if getattr(_op, "origin", None) else clean_url(get_settings().get("spoolman_url"))
    if open_url(f"{url}/spool/show/{sid}"):
        return {"ok": True, "text": tr("Opened spool #{id} in Spoolman.", id=sid)}
    return no(tr("Could not open {url}.", url=f"{url}/spool/show/{sid}"))


# --- Spool editor: Add Spool and Edit Spool ----------------------------------------------------
# Every value from the page is checked against these tables of Spoolman's own fields before
# anything is sent. An edit sends only the fields the user changed, after reading Spoolman again:
# a field someone changed in Spoolman since the editor read it keeps Spoolman's value.
# kind, then (low, high) for numbers or the most characters for text. "pos" excludes the low end;
# "need" is "pos" that can't be cleared (Spoolman requires it), "grams" is "num" that can't be:
# Spoolman computes with a spool's weights and fails on an empty one.
SPOOL_FORM = {"initial_weight": ("grams", 0, MAX_GRAMS), "remaining_weight": ("grams", 0, MAX_GRAMS),
              "location": ("text", LOCATION_MAX), "lot_nr": ("text", 64), "price": ("num", 0, 1e7),
              "comment": ("text", COMMENT_MAX), "archived": ("bool",)}
FILAMENT_FORM = {"name": ("text", 64), "material": ("text", 64), "color_hex": ("hex",), "multi_color_hexes": ("hexes",),
                 "multi_color_direction": ("choice", "coaxial", "longitudinal"), "diameter": ("need", 0, 10),
                 "density": ("need", 0, 100), "settings_extruder_temp": ("int", 0, 600), "settings_bed_temp": ("int", 0, 300),
                 "weight": ("pos", 0, MAX_GRAMS), "spool_weight": ("num", 0, MAX_GRAMS), "vendor": ("text", 64)}
COLOUR_KEYS = ("color_hex", "multi_color_hexes", "multi_color_direction")
EDITOR_OWN = {"tag", ORCA_SETTINGS_FIELD, DRIED_FIELD, *CALIBRATION_FIELDS}  # Spooler's own fields: never from the editor
EDITOR_INVALID = "The value for {field} isn't valid; nothing was written."
EDITOR_NO_VERSION = ("Spooler couldn't read Spoolman's version, so it can't tell how this Spoolman saves extra fields. "
                     "Nothing was written; check the connection and try again.")
EDITOR_NO_CLEAR = "This Spoolman can't empty an extra field ({fields}); Spoolman 0.26 or newer can. Nothing was written."
EDITOR_NO_EXTRA = ("Spooler couldn't read the extra fields Spoolman holds, and this Spoolman version replaces all of them "
                   "on a change. Nothing was written.")
_BAD = object()


def _form_value(spec: tuple, value: object) -> object:
    """One form value checked against its spec: the value to send (None clears), or _BAD."""
    kind = spec[0]
    if kind == "bool":
        return value if isinstance(value, bool) else _BAD
    if value is None or (isinstance(value, str) and not value.strip()):
        return _BAD if kind in ("need", "grams") else None
    if kind == "text":
        if not isinstance(value, str) or len(value.strip()) > spec[1]:
            return _BAD
        # A note keeps its line breaks; a one-line field gets single spaces.
        return value.strip() if spec[1] == COMMENT_MAX else " ".join(value.split())
    if kind == "choice":
        return value if value in spec[1:] else _BAD
    if kind == "hex":
        text = str(value).strip().lstrip("#").upper() if isinstance(value, str) else ""
        return text if re.fullmatch(r"[0-9A-F]{6}([0-9A-F]{2})?", text) else _BAD
    if kind == "hexes":
        parts = [_form_value(("hex",), x) for x in value.split(",")] if isinstance(value, str) else [_BAD]
        return ",".join(parts) if len(parts) > 1 and all(isinstance(p, str) for p in parts) else _BAD
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return _BAD
    try:
        number = float(value.strip().replace(",", ".") if isinstance(value, str) else value)
    except ValueError:
        return _BAD
    low_ok = number > spec[1] if kind in ("pos", "need") else number >= spec[1]
    if not (math.isfinite(number) and low_ok and number <= spec[2]) or (kind == "int" and number != int(number)):
        return _BAD
    return int(number) if kind == "int" else round(number, 4)


def _extra_value(field: dict, value: object) -> object:
    """A typed extra-field value as the JSON text Spoolman keeps (None removes it), or _BAD."""
    kind, choices = field.get("field_type"), field.get("choices") or []
    if value is None or value == "" or value == []:
        return None
    whole = kind in ("integer", "integer_range")
    number = lambda x: (not isinstance(x, bool) and isinstance(x, (int, float)) and math.isfinite(x)  # noqa: E731
                        and (not whole or x == int(x)))
    as_int = lambda x: int(x) if whole and x is not None else x  # noqa: E731  Spoolman wants 3, not 3.0
    if kind == "boolean":
        ok = isinstance(value, bool)
    elif kind in ("integer", "float"):
        ok = number(value)
        value = as_int(value) if ok else value
    elif kind in ("integer_range", "float_range"):
        ok = (isinstance(value, list) and len(value) == 2
              and all(x is None or number(x) for x in value) and value != [None, None])
        value = [as_int(x) for x in value] if ok else value
    elif kind == "choice" and field.get("multi_choice"):
        ok = isinstance(value, list) and all(isinstance(x, str) and x in choices for x in value)
    elif kind == "choice":
        ok = isinstance(value, str) and value in choices
    elif kind == "datetime":
        try:
            ok = isinstance(value, str) and datetime.datetime.fromisoformat(value.strip()) is not None
        except ValueError:
            ok = False
    else:
        ok = isinstance(value, str) and len(value) <= COMMENT_MAX
    return json.dumps(value) if ok else _BAD


def _clean_form(form: dict, values: object, fields: list | None) -> dict | str:
    """The checked {field: value} of a page form ({"extra": {...}} inside), or the error text."""
    if not isinstance(values, dict):
        return tr(EDITOR_INVALID, field="form")
    known = {f.get("key"): f for f in fields or [] if isinstance(f, dict)}
    out: dict = {}
    for key, value in values.items():
        if key == "extra":
            if not isinstance(value, dict):
                return tr(EDITOR_INVALID, field=key)
            extra = {}
            for name, raw in value.items():
                text = _extra_value(known[name], raw) if name in known and name not in EDITOR_OWN else _BAD
                if text is _BAD:
                    return tr(EDITOR_INVALID, field=name)
                extra[name] = text
            out["extra"] = extra
            continue
        clean = _form_value(form[key], value) if key in form else _BAD
        if clean is _BAD:
            return tr(EDITOR_INVALID, field=key)
        out[key] = clean
    return out


def _vendor_id(name: str | None) -> int | None:
    """The Spoolman vendor of that name (case and spacing ignored), added when there is none."""
    if not name:
        return None
    for vendor in spoolman_call("GET", "vendor") or []:
        if isinstance(vendor, dict) and _norm(vendor.get("name")) == _norm(name) and _pos_int(vendor.get("id")):
            return vendor["id"]
    return spoolman_call("POST", "vendor", {"name": name})["id"]


def _for_spoolman(clean: dict, now: dict | None = None) -> dict:
    """A checked filament form as Spoolman's fields: the vendor by id, and the colour as one group.
    Spoolman checks the three colour fields together on every write (one colour and no direction,
    or several with one), so a change to any of them sends all three, the rest as Spoolman has them."""
    body = dict(clean)
    if "vendor" in body:
        body["vendor_id"] = _vendor_id(body.pop("vendor"))
    if any(key in body for key in COLOUR_KEYS):
        for key in COLOUR_KEYS:
            body.setdefault(key, (now or {}).get(key))
        if body["multi_color_hexes"]:
            body.update(color_hex=None, multi_color_direction=body["multi_color_direction"] or "coaxial")
        else:
            body.update(multi_color_hexes=None, multi_color_direction=None)
    return body


def _create_body(clean: dict) -> dict:
    """A create sends no empty field: Spoolman's defaults stand for them."""
    body = {k: v for k, v in clean.items() if v is not None}
    if body.get("extra"):
        body["extra"] = {k: v for k, v in body["extra"].items() if v is not None}
    return {k: v for k, v in body.items() if v != {}}


def _editor_fields() -> dict:
    return {kind: [f for f in spoolman_call("GET", f"field/{kind}") or [] if isinstance(f, dict)]
            for kind in ("spool", "filament")}


def _error_text(exc: Exception) -> str:
    """Spoolman's refusal with the reason it gives, when it gives one."""
    detail = ""
    if isinstance(exc, urllib.error.HTTPError):
        try:
            detail = json.loads(exc.read().decode("utf-8")).get("message") or ""
        except Exception:
            detail = ""
    error = _spoolman_error(exc)
    return tr("{text}: {detail}", text=error, detail=detail) if isinstance(detail, str) and detail else error


def editor_data(sid: int | None) -> dict:
    """What the editor needs: Spoolman's extra-field definitions, its filaments and vendors, and the
    spool being edited as Spoolman has it now."""
    filaments = [f for f in spoolman_call("GET", "filament") or [] if isinstance(f, dict)]
    vendors = sorted({str(v.get("name")) for v in spoolman_call("GET", "vendor") or [] if isinstance(v, dict) and v.get("name")},
                     key=str.casefold)
    spool = spoolman_call("GET", f"spool/{sid}") if sid else None
    return {"fields": _editor_fields(), "filaments": filaments, "vendors": vendors, "spool": spool}


def _merge_edit(changes: dict, was: dict, now: dict) -> tuple[dict, list, dict]:
    """The changed fields whose Spoolman value is still the one the editor read (the PATCH body,
    extra apart), the fields kept as Spoolman has them, and the changed extra keys."""
    patch, kept = {}, []
    for key, value in changes.items():
        if key == "extra":
            continue
        old = was.get(key)
        if value == old:
            continue  # sent along, not changed by the user (a starting weight's grams left)
        has = (now.get("vendor") or {}).get("name") if key == "vendor" else now.get(key)
        if has != old and has != value:
            kept.append(key)
        elif has != value:
            patch[key] = value
    now_extra, was_extra = now.get("extra") or {}, was.get("extra") or {}
    extra = {}
    for key, value in (changes.get("extra") or {}).items():
        if now_extra.get(key) != was_extra.get(key) and now_extra.get(key) != value:
            kept.append(key)
        elif now_extra.get(key) != value:
            extra[key] = value
    return patch, kept, extra


def _extra_patch(extra: dict, now: dict, version: tuple | None) -> dict:
    """The extra map to PATCH for these changed keys (None empties one), by Spoolman version, read
    from its source: from 0.26 the map is merged key by key and null empties a key; from 0.22 it
    is merged but takes no null; before, a PATCH replaces the whole map, so it goes back whole, as
    just read, with the changes on top. Raises RuntimeError with what to tell the user."""
    if version is None:
        raise RuntimeError(tr(EDITOR_NO_VERSION))
    if version >= SPOOLMAN_EXTRA_MERGE:
        return extra
    if version >= SPOOLMAN_EXTRA_PARTIAL:
        cleared = sorted(k for k, v in extra.items() if v is None)
        if cleared:
            raise RuntimeError(tr(EDITOR_NO_CLEAR, fields=", ".join(cleared)))
        return extra
    now_extra = now.get("extra") or {}
    if not isinstance(now_extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in now_extra.items()):
        raise RuntimeError(tr(EDITOR_NO_EXTRA))
    return {k: v for k, v in {**now_extra, **extra}.items() if v is not None}


def editor_save(sid: int, data: dict) -> dict:
    """Edit Spool: the spool's changed fields, and its filament's (shared by its other spools)."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    fields = _editor_fields()
    spool_changes = _clean_form(SPOOL_FORM, data.get("spool") or {}, fields["spool"])
    fil_changes = _clean_form(FILAMENT_FORM, data.get("filament") or {}, fields["filament"])
    for found in (spool_changes, fil_changes):
        if isinstance(found, str):
            return no(found)
    was = data.get("was") if isinstance(data.get("was"), dict) else {}
    was_spool = was.get("spool") if isinstance(was.get("spool"), dict) else {}
    was_fil = was.get("filament") if isinstance(was.get("filament"), dict) else {}
    now = spoolman_call("GET", f"spool/{sid}")
    now = now if isinstance(now, dict) else {}
    filament = now.get("filament") if isinstance(now.get("filament"), dict) else {}
    fid = _pos_int(filament.get("id"))
    s_patch, kept, s_extra = _merge_edit(spool_changes, was_spool, now)
    if fil_changes and (fid is None or fid != was_fil.get("id")):
        # The spool has another filament in Spoolman now: these changes were made to the old one.
        f_patch, f_extra = {}, {}
        kept += [key for key in fil_changes if key != "extra"] + list(fil_changes.get("extra") or {})
    else:
        f_patch, f_kept, f_extra = _merge_edit(fil_changes, was_fil, filament)
        kept += f_kept
    if "initial_weight" in s_patch and "remaining_weight" not in s_patch and now.get("remaining_weight") is not None:
        # Spoolman keeps the used grams and works out what is left, so a new starting weight alone would
        # move the grams left: they go along as Spoolman has them now, use booked meanwhile included.
        s_patch["remaining_weight"] = now["remaining_weight"]
    if s_extra or f_extra:
        version = spoolman_version(fresh=True)
        if s_extra:
            s_patch["extra"] = _extra_patch(s_extra, now, version)
        if f_extra:
            f_patch["extra"] = _extra_patch(f_extra, filament, version)
    if f_patch:
        spoolman_call("PATCH", f"filament/{fid}", _for_spoolman(f_patch, filament))
    if s_patch:
        try:
            spoolman_call("PATCH", f"spool/{sid}", s_patch)
        except Exception as exc:
            if not f_patch:
                raise
            log.warning("Saving spool #%s after its filament failed: %s", sid, exc)
            return no(tr("Saved the filament of spool #{id}, but Spoolman refused the spool: {error}", id=sid, error=_error_text(exc)))
    names = {f.get("key"): f.get("name") or f.get("key") for f in fields["spool"] + fields["filament"]}
    notes = []
    if f_patch:
        notes.append(tr("Saved spool #{id} and its filament.", id=sid))
    elif s_patch:
        notes.append(tr("Saved spool #{id}.", id=sid))
    elif not kept:
        notes.append(tr("Spool #{id} had no changes to save.", id=sid))
    if kept:
        notes.append(tr("Kept Spoolman's newer value for {fields}: it changed there while you were editing.",
                        fields=", ".join(str(names.get(key, key)) for key in kept)))
    return {"ok": True, "text": _sentences(notes)}


def editor_create(data: dict) -> dict:
    """Add Spool: a spool of an existing filament (stock), or of a new filament made first."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    fields = _editor_fields()
    spool = _clean_form(SPOOL_FORM, data.get("spool") or {}, fields["spool"])
    if isinstance(spool, str):
        return no(spool)
    first, left = spool.get("initial_weight"), spool.get("remaining_weight")
    if first is not None and left is not None and left > first:
        return no(tr(EDITOR_INVALID, field="remaining_weight"))
    fid, made = _pos_int(data.get("filament_id")), None
    if fid is None:
        new = _clean_form(FILAMENT_FORM, data.get("filament"), fields["filament"])
        if isinstance(new, str):
            return no(new)
        for key in ("density", "diameter"):  # Spoolman needs both for a filament
            if new.get(key) is None:
                return no(tr(EDITOR_INVALID, field=key))
        fid = made = spoolman_call("POST", "filament", _create_body(_for_spoolman(new)))["id"]
    try:
        added = spoolman_call("POST", "spool", {"filament_id": fid, **_create_body(spool)})
    except Exception as exc:
        if made is None:
            raise
        log.warning("Adding a spool of new filament #%s failed: %s", made, exc)
        # The filament exists now: the page offers it as the existing filament, so a retry adds no second one.
        return {**no(tr("Created filament #{filament}, but Spoolman refused the spool: {error}",
                        filament=made, error=_error_text(exc))), "filament": made}
    sid = (added or {}).get("id", "?") if isinstance(added, dict) else "?"
    if made is not None:
        return {"ok": True, "text": tr("Added spool #{id} with the new filament #{filament}.", id=sid, filament=made), "spool": sid}
    return {"ok": True, "text": tr("Added spool #{id}.", id=sid), "spool": sid}


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
    if action not in ("locations", "editor", "create", "save") and action not in SPOOL_ACTIONS:
        return {"ok": False, "text": tr("Unknown spool action.")}
    if source() != "spoolman":
        return {"ok": False, "text": tr("Spool actions need Spoolman as the source.")}
    sid = _pos_int(data.get("id"))
    if sid is None and action not in ("locations", "editor", "create"):
        return {"ok": False, "text": tr("No spool chosen.")}
    if action not in ("locations", "editor") and stale_list(data):
        return {"ok": False, "text": tr(STALE_LIST)}
    try:
        with pinned_origin():
            if action == "locations":
                found = spoolman_call("GET", "location")
                return {"ok": True, "text": "",
                        "locations": [x for x in found if isinstance(x, str)] if isinstance(found, list) else []}
            if action == "editor":
                return {"ok": True, "text": "", "editor": editor_data(sid)}
            if action == "create":
                return editor_create(data)
            if action == "save":
                return editor_save(sid, data)
            return _spool_write(action, sid, data)
    except Exception as exc:
        log.warning("Spool action %s on #%s failed: %s", action, sid, exc)
        return {"ok": False, "text": _error_text(exc)}


def start_spool_action(data: object, post) -> None:
    """Run a card action off the UI thread and post {"type": "action_result", ...}. The page asks
    for a refresh when it gets it, so the list is re-read on the UI thread."""
    action = data.get("action") if isinstance(data, dict) else None

    def work():
        result = spool_action(data)
        if action not in ("locations", "editor"):
            _spool_cache["time"] = 0.0
        ref = data.get("ref") if isinstance(data, dict) else None  # the editor's own count: its answer finds the right editor
        post({"type": "action_result", "action": action, **result,
              **({"ref": ref} if isinstance(ref, int) and not isinstance(ref, bool) else {})})
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
            row.update(state="unknown", error=tr("{text} ({detail})", text=tr(UNKNOWN_TEXT), detail=_spoolman_error(exc)))
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
                return tr(ORIGIN_TEXT)
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
                label = _spool_label(by_id[spool]) if spool in by_id else row.get("label") or tr("spool {id}", id=spool)
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
        return tr("Spoolman has the change, but Spooler could not update its history file.")
    return ""


def usage_undo(entry_id: str) -> str:
    """Add a booked print's grams back to its spools. Returns a notice, "" when there is none."""
    with pinned_origin() as origin:
        with _usage_lock:
            entry = next((e for e in usage_load()["prints"] if e.get("id") == entry_id), None)
        if entry is None or entry.get("state") != "booked":
            return ""
        if entry.get("origin") != origin[0]:
            return tr(ORIGIN_TEXT)
        if not spoolman_at_least(SPOOLMAN_ATOMIC_USE):
            return tr("Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use "
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
            notice = tr(STALE_LIST)
        elif kind == "usage_book":
            notice = usage_book(str(data.get("run") or ""), data.get("rows"))
        elif kind == "usage_undo":
            notice = usage_undo(str(data.get("run") or ""))
        elif kind == "usage_resolve":
            notice = usage_resolve(str(data.get("run") or ""), data.get("slot"), data.get("outcome"))
    except OSError:
        log.exception("Could not write %s", USAGE_FILE)
        notice = tr("Spooler could not save its booking state ({file}), so it stopped. Rows it "
                    "was sending are marked for you to check in Spoolman.", file=USAGE_FILE.name)
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
        return {"ok": False, "text": tr("Could not write the export: {error}", error=exc)}
    open_url(folder.as_uri())
    return {"ok": True, "text": tr("Saved {path}", path=path), "path": str(path)}


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
            m = (r.get("material") or "").strip() or tr("Other")
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
        m = (str((sp.get("filament") or {}).get("material") or "").strip()) or tr("Other")
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
            raise ValueError(tr("GitHub sent an answer Spooler doesn't understand"))
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            error = tr("No published release found yet")
        else:
            error = tr("GitHub returned HTTP {code}", code=exc.code)
    except urllib.error.URLError as exc:
        error = tr("Could not reach GitHub ({reason})", reason=exc.reason)
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
        message = tr("No web browser could be launched. Open this address yourself:\n{url}", url=url)
    except Exception as exc:
        log.exception("Could not open the browser")
        message = tr("Could not open the browser: {error}", error=exc)
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
    return f"{fmt_num(grams / 1000, 2)} kg" if grams >= 1000 else f"{fmt_num(grams, 1)} g"


def _join(items: list[str]) -> str:
    return items[0] if len(items) == 1 else tr(", ").join(items[:-1]) + tr(" and ") + items[-1]


def slot_label(result: dict) -> str:
    slot, numbers = result["slot"], result["slots"]
    preset = slot["preset"].split("@")[0].strip()
    named = preset or " ".join(part for part in (slot["vendor"], slot["material"]) if part)
    name = result.get("name") or " ".join(part for part in (named, slot["colour"]) if part)
    return tr("slot {n} ({name})" if len(numbers) == 1 else "slots {n} ({name})",
              n=_join([str(n) for n in numbers]), name=name)


def _sentence(text: str) -> str:
    return text[:1].upper() + text[1:] + tr(".")


def _need(result: dict) -> str:
    return tr("needs {grams} of filament" if len(result["slots"]) == 1 else "need {grams} of filament together",
              grams=fmt_grams(result["need"]))


def _supply(result: dict) -> str:
    count, have = min(result["pool"], result["matches"]), fmt_grams(result["have"])
    if count == 1:
        return tr("the spool has {have}", have=have)
    return tr("the {count} spools have {have} between them", count=count, have=have)


def _tracked(result: dict) -> str:
    if result["matches"] >= result["pool"]:
        return ""
    return tr(" (only {matches} of {pool} matching spools are in {source})",
              matches=result["matches"], pool=result["pool"], source=source_name())


def plate_notice(results: list[dict], cost: str = "") -> tuple[str, str] | None:
    """The one notification for a slice: ``("warning" | "info", text)``."""
    label, grams = slot_label, fmt_grams
    ams = any(r["ams"] for r in results)
    short = [r for r in results if r["status"] == "short"]
    mixed = [r for r in results if r["status"] == "mixed"]
    barely = [r for r in results if r["status"] == "barely"]

    def short_part(r: dict) -> str:
        text = _sentence(tr("{slot} {need} but {supply}{tracked}",
                            slot=label(r), need=_need(r), supply=_supply(r), tracked=_tracked(r)))
        swap = r.get("swap")
        if swap:
            grams, location = fmt_num(swap["remaining_weight"]), swap.get("location")
            text += (tr(" Swap in spool #{id} ({location}, {grams} g).", id=swap["id"], location=location, grams=grams)
                     if location else tr(" Swap in spool #{id} ({grams} g).", id=swap["id"], grams=grams))
        return text

    def mixed_part(r: dict, prefix: str = "") -> str:
        count = min(r["pool"], r["matches"])
        if count == 1:
            body = tr("of {matches} matching spools the fullest has {have} and "
                      "the smallest has {worst}, so make sure the right one is loaded",
                      matches=r["matches"], have=grams(r["have"]), worst=grams(r["worst"]))
        else:
            body = tr("the {count} fullest of {matches} matching spools hold "
                      "{have} and the {count} smallest hold {worst}, "
                      "so make sure the right ones are loaded",
                      count=count, matches=r["matches"], have=grams(r["have"]), worst=grams(r["worst"]))
        return _sentence(prefix + tr("{slot} {need}; {body}", slot=label(r), need=_need(r), body=body))

    def barely_part(r: dict, prefix: str = "") -> str:
        return _sentence(prefix + tr("{slot} {need} ({padded} with the {margin}% margin) and {supply}{tracked}",
                                     slot=label(r), need=_need(r), padded=grams(r["padded"]), margin=r["margin"],
                                     supply=_supply(r), tracked=_tracked(r)))

    if short:
        kind, parts = "warning", [tr("not enough filament loaded in the AMS." if ams else "not enough filament loaded.")]
        parts += [short_part(r) for r in short]
        parts += [mixed_part(r, tr("also check: ")) for r in mixed]
        parts += [barely_part(r, tr("also barely enough: ")) for r in barely]
    elif mixed:
        kind, parts = "warning", [tr("not enough filament may be loaded in the AMS." if ams else
                                     "not enough filament may be loaded.")]
        parts += [mixed_part(r) for r in mixed]
        parts += [barely_part(r, tr("also barely enough: ")) for r in barely]
    elif barely:
        kind, parts = "warning", [tr("barely enough filament.")] + [barely_part(r) for r in barely]
    else:
        kind, parts = "info", []
        fine = [r for r in results if r["status"] == "ok"]
        unknown = [r for r in results if r["status"] == "unknown"]
        if len(fine) > 3:
            numbers = sorted(n for r in fine for n in r["slots"])
            parts.append(tr("quantity OK for slots {slots}.", slots=_join([str(n) for n in numbers])))
        elif fine:
            parts.append(tr("quantity OK."))
            parts += [_sentence(tr("{slot} {need}, {supply}", slot=label(r), need=_need(r), supply=_supply(r)))
                      for r in fine]
        if unknown:
            many = sum(len(r["slots"]) for r in unknown) > 1
            sentence = _sentence(tr("no spool found for {slots}, so they weren't checked" if many else
                                    "no spool found for {slots}, so it wasn't checked",
                                    slots=_join([label(r) for r in unknown])))
            parts.append(sentence if parts else sentence[:1].lower() + sentence[1:])
        if not parts:
            return None
    parts += [dry_part(r) for r in results if r.get("dry")]  # after the stock sentences, before the cost
    if cost:
        parts.append(cost)  # last, so fit_text drops it first
    return kind, tr("Spooler: {text}", text=_sentences(parts))


def dry_part(r: dict) -> str:
    slot = r["slot"]
    name = r.get("name") or " ".join(p for p in (slot["preset"].split("@")[0].strip() or slot["material"], slot["colour"]) if p)
    which = tr("slot {n}" if len(r["slots"]) == 1 else "slots {n}", n=_join([str(n) for n in r["slots"]]))
    days = r["dry"]["days"]
    if days is None:
        return tr("{name} ({slots}) has no drying date.", name=name, slots=which)
    return tr("{name} ({slots}) was last dried {days} day ago." if days == 1 else
              "{name} ({slots}) was last dried {days} days ago.", name=name, slots=which, days=days)


def cost_sentence(results: list[dict], code: str) -> str:
    """"About €1.23 of filament." from the matched spools' prices, or "" when none is known."""
    costs = [r["cost"] for r in results if isinstance(r.get("cost"), (int, float))]
    if not costs:
        return ""
    return tr("About {cost} of filament.", cost=fmt_money(sum(costs), code))


def fit_text(text: str, limit: int = NOTICE_MAX) -> str:
    """Whole sentences only: what doesn't fit is dropped and counted, never cut mid-sentence."""
    if len(text) <= limit:
        return text
    # Chinese sentences end in "。" with no space after it.
    sentences = re.split(r"(?<=。)(?=.)" if text_language() == "zh-CN" else r"(?<=\.) ", text)
    for keep in range(len(sentences) - 1, 0, -1):
        note = tr(" (+{count} more, see the log)", count=len(sentences) - keep)
        shown = _sentences(sentences[:keep])
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
            headline = tr("Not checked")
            detail = tr("no spool found for these slots" if many else "no spool found for this slot")
        else:
            headline = {"ok": tr("Quantity OK"), "barely": tr("Barely enough"), "short": tr("Not enough"),
                        "mixed": tr("Check the spools" if count > 1 else "Check the spool")}[status]
            if status == "mixed":
                detail = tr("{need} needed \u00b7 matching spools hold {low} to {high}",
                            need=need, low=fmt_grams(r["worst"]), high=fmt_grams(have))
            elif count > 1:
                detail = tr("{need} needed \u00b7 {have} across {count} spools", need=need, have=fmt_grams(have), count=count)
            elif status == "ok" and r["matches"] == 1:
                detail = tr("{need} needed \u00b7 leaves {left}", need=need, left=fmt_grams(have - r["need"]))
            elif status == "ok":
                detail = tr("{need} needed \u00b7 every matching spool has at least {low}", need=need, low=fmt_grams(r["worst"]))
            else:
                detail = tr("{need} needed \u00b7 {have} left", need=need, have=fmt_grams(have))
        rows.append({
            "slots": tr("Slots {n}" if many else "Slot {n}", n=" + ".join(str(n) for n in numbers)),
            "first": min(numbers), "name": name,
            "meta": " \u00b7 ".join(p for p in (slot["vendor"], tr("{count} slots, pooled", count=len(numbers)) if many else "") if p),
            "colour": slot["colour"], "status": status, "headline": headline, "detail": detail,
            "fill": round(min(1.0, have / total), 3), "need_pct": round(min(1.0, r["need"] / total), 3),
            "spool_colour": r.get("spool_colour") or slot["colour"],
            "ids": r["ids"],
        })
    return rows


def send_plate(payload: dict | None) -> None:
    send_plate_message(payload or {"type": "plate_clear"})


def send_plate_message(payload: dict) -> None:
    """Post to the Spooler tab, when there is one. Never raises."""
    page = _plate["page"]
    if page is None:
        return
    try:
        page.post_message(payload)
    except Exception:
        log.exception("Could not post to the Spooler tab")


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
        return ("info", tr("Spooler: no Spoolman address is set up yet, "
                           "so the filament quantity wasn't checked.")), None
    if spools is None:
        return ("info", tr("Spooler: couldn't reach {source}, "
                           "so the filament quantity wasn't checked.", source=source_name())), None
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
UI_LANGUAGES = ("auto", "en", "pt-BR", "es", "de", "zh-CN")
# OrcaSlicer's language codes ("pt_BR", "es", "de", "zh_CN", "zh_TW") by their language part. Traditional
# Chinese takes the Simplified texts: closer to its reader than English. The page maps them the same way.
_LANGUAGE_OF = {"en": "en", "pt": "pt-BR", "es": "es", "de": "de", "zh": "zh-CN"}
_lang: dict = {"value": None}


def ui_page() -> str:
    return zlib.decompress(base64.b64decode(UI_PAGE_Z64)).decode("utf-8")


def _json_for_html(data: object) -> str:
    """JSON safe inside a <script> block: no literal <, > or & can end it or open a tag."""
    return json.dumps(data).replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")


def host_language() -> str | None:
    """OrcaSlicer's UI language (`orca.host.app_language()`, e.g. "pt_BR"), or None when the host doesn't offer it.
    The page and tr() map it to a language Spooler has, else English; an explicit choice wins."""
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
    """The page's language choice ("auto" or one of UI_LANGUAGES); anything else is ignored."""
    if value in UI_LANGUAGES:
        save_settings({**get_settings(), "ui_language": value})
        text_language(fresh=True)


def normalize_language(value: object) -> str | None:
    """A language code as one of Spooler's languages: "pt_BR" → "pt-BR", "es_ES" → "es", "de" → "de",
    "zh_CN" and "zh_TW" → "zh-CN", any English → "en"; None for the rest and for anything that isn't text."""
    if not isinstance(value, str):
        return None
    return _LANGUAGE_OF.get(re.split(r"[-_]", value.strip().lower())[0])


def text_language(fresh: bool = False) -> str:
    """The language of the texts worded in Python (notices, dialogs, action results, plate rows): the choice
    made on the page, else OrcaSlicer's language, else English. Kept after the first call, since worker
    threads word texts too; reading it again (fresh) happens on the UI thread: when a page is built and
    when the choice is saved."""
    if fresh or _lang["value"] is None:
        pref = ui_language()
        _lang["value"] = pref if pref != "auto" else normalize_language(host_language()) or "en"
    return _lang["value"]


def tr(text: str, /, **values: object) -> str:
    """text in the current language, with its {names} filled in. The English text is the key and what is
    shown when a language has no entry for it."""
    found = _TEXTS.get(text_language(), {}).get(text, text)
    return found.format(**values) if values else found


def _sentences(parts: list[str]) -> str:
    """Whole sentences in a row: a space between them, none in Chinese."""
    return ("" if text_language() == "zh-CN" else " ").join(parts)


def fmt_num(value: float, digits: int = 0, group: bool = False) -> str:
    """A number as the current language writes it: 1,234.5 in English and Chinese, 1.234,5 in German,
    Portuguese and Spanish (which groups only from 10,000 up, as the page's Intl.NumberFormat does)."""
    language = text_language()
    if group and not (language == "es" and abs(value) < 10000):
        text = f"{value:,.{digits}f}"
    else:
        text = f"{value:.{digits}f}"
    if language in ("pt-BR", "es", "de"):
        text = text.replace(",", "\0").replace(".", ",").replace("\0", ".")
    return text


def fmt_money(amount: float, code: str) -> str:
    """An amount with its currency sign where the language puts it: "€1.23", in German and Spanish "1,23 €"."""
    sign, text = CUR_SIGNS.get(code, code + " "), fmt_num(amount, 2)
    return f"{text}\u00a0{sign.strip()}" if text_language() in ("de", "es") else sign + text


# Python-worded texts in the page's other languages, by their English text: (pt-BR, es, de, zh-CN). Terms follow
# OrcaSlicer's own translations (Spanish "carrete", "ranura", "perfil"; German "Spule", "Slot", "Profil", formal "Sie";
# Chinese "料盘", "槽位", "预设", "耗材丝", full-width punctuation). Spoolman data (names, vendors, notes) is never translated.
_TEXT_LANGS = ("pt-BR", "es", "de", "zh-CN")
_TEXT_ROWS: dict[str, tuple[str, str, str, str]] = {
    "Signed in ({region})": (
        "Conectado ({region})",
        "Sesión iniciada ({region})",
        "Angemeldet ({region})",
        "已登录（{region}）",
    ),
    "Signed in as {user} ({region})": (
        "Conectado como {user} ({region})",
        "Sesión iniciada como {user} ({region})",
        "Angemeldet als {user} ({region})",
        "已登录为 {user}（{region}）",
    ),
    "Global": (
        "Global",
        "Global",
        "Global",
        "全球",
    ),
    "China": (
        "China",
        "China",
        "China",
        "中国",
    ),
    "slot {n} ({name})": (
        "slot {n} ({name})",
        "la ranura {n} ({name})",
        "Slot {n} ({name})",
        "槽位 {n}（{name}）",
    ),
    "slots {n} ({name})": (
        "slots {n} ({name})",
        "las ranuras {n} ({name})",
        "Slots {n} ({name})",
        "槽位 {n}（{name}）",
    ),
    "needs {grams} of filament": (
        "precisa de {grams} de filamento",
        "necesita {grams} de filamento",
        "braucht {grams} Filament",
        "需要 {grams} 耗材丝",
    ),
    "need {grams} of filament together": (
        "precisam de {grams} de filamento juntos",
        "necesitan {grams} de filamento en total",
        "brauchen zusammen {grams} Filament",
        "共需要 {grams} 耗材丝",
    ),
    "the spool has {have}": (
        "a bobina tem {have}",
        "el carrete tiene {have}",
        "die Spule hat {have}",
        "料盘有 {have}",
    ),
    "the {count} spools have {have} between them": (
        "as {count} bobinas têm {have} juntas",
        "los {count} carretes tienen {have} en total",
        "die {count} Spulen haben zusammen {have}",
        "这 {count} 个料盘共有 {have}",
    ),
    " (only {matches} of {pool} matching spools are in {source})": (
        " (só {matches} de {pool} bobinas compatíveis estão no {source})",
        " (solo {matches} de {pool} carretes compatibles están en {source})",
        " (nur {matches} von {pool} passenden Spulen sind in {source})",
        "（{pool} 个匹配料盘中只有 {matches} 个在 {source} 中）",
    ),
    "slot {n}": (
        "slot {n}",
        "ranura {n}",
        "Slot {n}",
        "槽位 {n}",
    ),
    "slots {n}": (
        "slots {n}",
        "ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
    ),
    "Slot {n}": (
        "Slot {n}",
        "Ranura {n}",
        "Slot {n}",
        "槽位 {n}",
    ),
    "Slots {n}": (
        "Slots {n}",
        "Ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
    ),
    "{name} ({slots}) has no drying date.": (
        "{name} ({slots}) não tem data de secagem.",
        "{name} ({slots}) no tiene fecha de secado.",
        "{name} ({slots}) hat kein Trocknungsdatum.",
        "{name}（{slots}）没有烘干日期。",
    ),
    "{name} ({slots}) was last dried {days} day ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dia.",
        "{name} ({slots}) se secó por última vez hace {days} día.",
        "{name} ({slots}) wurde zuletzt vor {days} Tag getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
    ),
    "{name} ({slots}) was last dried {days} days ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dias.",
        "{name} ({slots}) se secó por última vez hace {days} días.",
        "{name} ({slots}) wurde zuletzt vor {days} Tagen getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
    ),
    "About {cost} of filament.": (
        "Cerca de {cost} de filamento.",
        "Unos {cost} de filamento.",
        "Etwa {cost} an Filament.",
        "耗材丝成本约 {cost}。",
    ),
    "Loaded {count} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot colours, so a slot keeps its old colour until you pick its filament in the dropdown.": (
        "{count} slot(s) de filamento carregado(s) da impressora. O OrcaSlicer não deixa plugins definirem a cor dos slots, então um slot mantém a cor antiga até você escolher o filamento dele na lista.",
        "Se cargaron {count} ranura(s) de filamento desde la impresora. OrcaSlicer no deja que los plugins cambien el color de las ranuras, así que una ranura conserva su color anterior hasta que eliges su filamento en el desplegable.",
        "{count} Filament-Slot(s) vom Drucker geladen. OrcaSlicer lässt Plugins die Slotfarben nicht ändern, daher behält ein Slot seine alte Farbe, bis Sie sein Filament in der Auswahlliste wählen.",
        "已从打印机载入 {count} 个耗材丝槽位。OrcaSlicer 不允许插件设置槽位颜色，所以在您从下拉列表中选择该槽位的耗材丝之前，槽位会保留原来的颜色。",
    ),
    " No Spoolman filament matched slot(s) {slots}.": (
        " Nenhum filamento do Spoolman corresponde ao(s) slot(s) {slots}.",
        " Ningún filamento de Spoolman coincide con la(s) ranura(s) {slots}.",
        " Kein Spoolman-Filament passt zu Slot(s) {slots}.",
        "没有 Spoolman 耗材丝与槽位 {slots} 匹配。",
    ),
    " Could not change slot(s) {slots}.": (
        " Não foi possível alterar o(s) slot(s) {slots}.",
        " No se pudo cambiar la(s) ranura(s) {slots}.",
        " Slot(s) {slots} konnte(n) nicht geändert werden.",
        "无法更改槽位 {slots}。",
    ),
    "Spooler: {spool} is down to {grams} g": (
        "Spooler: {spool} está com apenas {grams} g",
        "Spooler: quedan {grams} g de {spool}",
        "Spooler: {spool} hat nur noch {grams} g",
        "Spooler：{spool} 只剩 {grams} g",
    ),
    "Bambu blocked the request (HTTP 403)": (
        "A Bambu bloqueou a solicitação (HTTP 403)",
        "Bambu bloqueó la solicitud (HTTP 403)",
        "Bambu hat die Anfrage blockiert (HTTP 403)",
        "Bambu 拦截了该请求（HTTP 403）",
    ),
    "Bambu Cloud returned an error (HTTP {code})": (
        "A Bambu Cloud retornou um erro (HTTP {code})",
        "Bambu Cloud devolvió un error (HTTP {code})",
        "Bambu Cloud hat einen Fehler gemeldet (HTTP {code})",
        "Bambu Cloud 返回错误（HTTP {code}）",
    ),
    "Bambu Cloud didn't sign you in": (
        "A Bambu Cloud não fez seu login",
        "Bambu Cloud no inició tu sesión",
        "Bambu Cloud hat Sie nicht angemeldet",
        "Bambu Cloud 登录失败",
    ),
    "Bambu Cloud didn't accept your sign-in": (
        "A Bambu Cloud não aceitou seu login",
        "Bambu Cloud no aceptó tu inicio de sesión",
        "Bambu Cloud hat Ihre Anmeldung nicht akzeptiert",
        "Bambu Cloud 不接受您的登录",
    ),
    "Bambu Cloud sent a reply Spooler doesn't understand": (
        "A Bambu Cloud enviou uma resposta que o Spooler não entende",
        "Bambu Cloud envió una respuesta que Spooler no entiende",
        "Bambu Cloud hat eine Antwort gesendet, die Spooler nicht versteht",
        "Bambu Cloud 返回了 Spooler 无法识别的回复",
    ),
    "Could not reach Bambu Cloud ({reason})": (
        "Não foi possível acessar a Bambu Cloud ({reason})",
        "No se pudo conectar con Bambu Cloud ({reason})",
        "Bambu Cloud ist nicht erreichbar ({reason})",
        "无法连接 Bambu Cloud（{reason}）",
    ),
    "Signed in, but Spooler could not save the sign-in to {folder}": (
        "Login feito, mas o Spooler não conseguiu salvá-lo em {folder}",
        "Sesión iniciada, pero Spooler no pudo guardarla en {folder}",
        "Angemeldet, aber Spooler konnte die Anmeldung nicht in {folder} speichern",
        "已登录，但 Spooler 无法将登录信息保存到 {folder}",
    ),
    "Enter your Bambu email and password": (
        "Digite seu e-mail e senha da Bambu",
        "Introduce tu correo y contraseña de Bambu",
        "Geben Sie Ihre Bambu-E-Mail-Adresse und Ihr Passwort ein",
        "请输入您的 Bambu 邮箱和密码",
    ),
    "Your sign-in timed out. Enter your email and password again": (
        "O login expirou. Digite seu e-mail e senha de novo",
        "El inicio de sesión caducó. Introduce de nuevo tu correo y contraseña",
        "Die Anmeldung ist abgelaufen. Geben Sie E-Mail-Adresse und Passwort erneut ein",
        "登录已超时。请重新输入邮箱和密码",
    ),
    "Enter your Bambu Lab verification code": (
        "Digite seu código de verificação da Bambu Lab",
        "Introduce tu código de verificación de Bambu Lab",
        "Geben Sie Ihren Bambu Lab-Bestätigungscode ein",
        "请输入您的 Bambu Lab 验证码",
    ),
    "Signed out": (
        "Desconectado",
        "Sesión cerrada",
        "Abgemeldet",
        "未登录",
    ),
    "Sign-in expired": (
        "Login expirado",
        "Sesión caducada",
        "Anmeldung abgelaufen",
        "登录已过期",
    ),
    "Your Bambu sign-in has expired": (
        "Seu login na Bambu expirou",
        "Tu sesión de Bambu caducó",
        "Ihre Bambu-Anmeldung ist abgelaufen",
        "您的 Bambu 登录已过期",
    ),
    "Your saved Bambu sign-in is unreadable": (
        "Não foi possível ler seu login salvo da Bambu",
        "No se puede leer tu sesión de Bambu guardada",
        "Ihre gespeicherte Bambu-Anmeldung ist nicht lesbar",
        "无法读取已保存的 Bambu 登录信息",
    ),
    "Open Settings and sign in to Bambu Cloud.": (
        "Abra os Ajustes e entre na Bambu Cloud.",
        "Abre Ajustes e inicia sesión en Bambu Cloud.",
        "Öffnen Sie die Einstellungen und melden Sie sich bei Bambu Cloud an.",
        "请打开设置并登录 Bambu Cloud。",
    ),
    "The spool source kept changing while loading; refresh to try again.": (
        "A origem das bobinas mudou durante o carregamento; atualize para tentar de novo.",
        "El origen de los carretes cambió mientras se cargaba; actualiza para intentarlo de nuevo.",
        "Die Spulenquelle hat sich beim Laden mehrmals geändert; aktualisieren Sie, um es erneut zu versuchen.",
        "加载时料盘来源一直在变化；请刷新后重试。",
    ),
    "{printer} now books its usage to spool #{id}.": (
        "{printer} agora registra o consumo na bobina #{id}.",
        "{printer} ahora registra su consumo en el carrete #{id}.",
        "{printer} bucht den Verbrauch jetzt auf Spule #{id}.",
        "{printer} 现在将用量记到料盘 #{id}。",
    ),
    "Spoolman refused it (HTTP {code})": (
        "O Spoolman recusou (HTTP {code})",
        "Spoolman lo rechazó (HTTP {code})",
        "Spoolman hat abgelehnt (HTTP {code})",
        "Spoolman 拒绝了该请求（HTTP {code}）",
    ),
    "Could not reach Spoolman ({reason})": (
        "Não foi possível acessar o Spoolman ({reason})",
        "No se pudo conectar con Spoolman ({reason})",
        "Spoolman ist nicht erreichbar ({reason})",
        "无法连接 Spoolman（{reason}）",
    ),
    "Could not reach Spoolman at {url} ({reason})": (
        "Não foi possível acessar o Spoolman em {url} ({reason})",
        "No se pudo conectar con Spoolman en {url} ({reason})",
        "Spoolman unter {url} ist nicht erreichbar ({reason})",
        "无法连接位于 {url} 的 Spoolman（{reason}）",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell whether changing the dried date would erase this spool's other extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe se alterar a data de secagem apagaria os outros campos extras desta bobina. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe si cambiar la fecha de secado borraría los demás campos extra de este carrete. No se escribió nada; revisa la conexión e inténtalo de nuevo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, ob das Ändern des Trocknungsdatums die anderen Zusatzfelder dieser Spule löschen würde. Es wurde nichts geschrieben; prüfen Sie die Verbindung und versuchen Sie es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法确定更改烘干日期是否会清除此料盘的其他额外字段。未写入任何内容；请检查连接后重试。",
    ),
    "Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras desta bobina, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra de este carrete, y esta versión de Spoolman los reemplaza todos en cada cambio. No se escribió nada.",
        "Spooler konnte die Zusatzfelder dieser Spule nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取此料盘的额外字段，而此版本的 Spoolman 每次更改都会替换全部字段。未写入任何内容。",
    ),
    "Could not open {url}.": (
        "Não foi possível abrir {url}.",
        "No se pudo abrir {url}.",
        "{url} konnte nicht geöffnet werden.",
        "无法打开 {url}。",
    ),
    "Saved {path}": (
        "Salvo em {path}",
        "Guardado en {path}",
        "Gespeichert: {path}",
        "已保存到 {path}",
    ),
    "No web browser could be launched. Open this address yourself:\n{url}": (
        "Nenhum navegador pôde ser aberto. Abra este endereço você mesmo:\n{url}",
        "No se pudo abrir ningún navegador. Abre esta dirección tú mismo:\n{url}",
        "Es konnte kein Webbrowser gestartet werden. Öffnen Sie diese Adresse selbst:\n{url}",
        "无法启动网页浏览器。请自行打开此地址：\n{url}",
    ),
    "Could not open the browser: {error}": (
        "Não foi possível abrir o navegador: {error}",
        "No se pudo abrir el navegador: {error}",
        "Der Browser konnte nicht geöffnet werden: {error}",
        "无法打开浏览器：{error}",
    ),
    ".": (
        ".",
        ".",
        ".",
        "。",
    ),
    ", ": (
        ", ",
        ", ",
        ", ",
        "、",
    ),
    " and ": (
        " e ",
        " y ",
        " und ",
        " 和 ",
    ),
    "Spooler: {text}": (
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler：{text}",
    ),
    " (+{count} more, see the log)": (
        " (+{count}, veja o log)",
        " (+{count} más, consulta el registro)",
        " (+{count} weitere, siehe Protokoll)",
        "（另有 {count} 条，见日志）",
    ),
    "the address must start with http:// or https://": (
        "o endereço deve começar com http:// ou https://",
        "la dirección debe empezar por http:// o https://",
        "die Adresse muss mit http:// oder https:// beginnen",
        "地址必须以 http:// 或 https:// 开头",
    ),
    "No Spoolman URL configured yet": (
        "Nenhuma URL do Spoolman configurada ainda",
        "Aún no hay una URL de Spoolman configurada",
        "Noch keine Spoolman-URL eingerichtet",
        "尚未配置 Spoolman URL",
    ),
    "No Spoolman URL configured yet - click Settings to set one.": (
        "Nenhuma URL do Spoolman configurada ainda: clique em Ajustes para definir uma.",
        "Aún no hay una URL de Spoolman configurada: pulsa Ajustes para añadirla.",
        "Noch keine Spoolman-URL eingerichtet: Klicken Sie auf Einstellungen, um eine festzulegen.",
        "尚未配置 Spoolman URL：请点击设置进行配置。",
    ),
    "{url} answered, but not like Spoolman does": (
        "{url} respondeu, mas não como o Spoolman responde",
        "{url} respondió, pero no como lo hace Spoolman",
        "{url} hat geantwortet, aber nicht wie Spoolman",
        "{url} 有响应，但不像 Spoolman 的响应",
    ),
    "No OrcaSlicer user folder accepted the presets": (
        "Nenhuma pasta de usuário do OrcaSlicer aceitou os perfis",
        "Ninguna carpeta de usuario de OrcaSlicer aceptó los perfiles",
        "Kein OrcaSlicer-Benutzerordner hat die Profile angenommen",
        "没有 OrcaSlicer 用户文件夹接受这些预设",
    ),
    "The spool source changed in Settings while this ran, so Spooler stopped before writing anything more. Try again.": (
        "A origem das bobinas mudou nos Ajustes durante a execução, então o Spooler parou antes de gravar mais nada. Tente de novo.",
        "El origen de los carretes cambió en Ajustes mientras esto se ejecutaba, así que Spooler se detuvo antes de escribir nada más. Inténtalo de nuevo.",
        "Die Spulenquelle wurde während des Vorgangs in den Einstellungen geändert, daher hat Spooler angehalten, bevor weiteres geschrieben wurde. Versuchen Sie es erneut.",
        "运行期间设置中的料盘来源发生了变化，Spooler 已停止，未再写入任何内容。请重试。",
    ),
    "Spoolman is not the spool source.": (
        "O Spoolman não é a origem das bobinas.",
        "Spoolman no es el origen de los carretes.",
        "Spoolman ist nicht die Spulenquelle.",
        "Spoolman 不是料盘来源。",
    ),
    "Open a Spooler preset in OrcaSlicer's filament settings and change it first.": (
        "Primeiro abra um perfil do Spooler nos ajustes de filamento do OrcaSlicer e altere-o.",
        "Primero abre un perfil de Spooler en los ajustes de filamento de OrcaSlicer y cámbialo.",
        "Öffnen Sie zuerst ein Spooler-Profil in den Filamenteinstellungen von OrcaSlicer und ändern Sie es.",
        "请先在 OrcaSlicer 的耗材丝设置中打开一个 Spooler 预设并修改它。",
    ),
    "{name} has no unsaved changes to send.": (
        "{name} não tem alterações não salvas para enviar.",
        "{name} no tiene cambios sin guardar que enviar.",
        "{name} hat keine ungespeicherten Änderungen zum Senden.",
        "{name} 没有可发送的未保存更改。",
    ),
    "{name} is no longer a Spooler preset. Refresh, then send it again.": (
        "{name} não é mais um perfil do Spooler. Atualize e envie de novo.",
        "{name} ya no es un perfil de Spooler. Actualiza y vuelve a enviarlo.",
        "{name} ist kein Spooler-Profil mehr. Aktualisieren Sie und senden Sie es erneut.",
        "{name} 已不再是 Spooler 预设。请刷新后重新发送。",
    ),
    "The {field} field of {name}'s filament isn't a JSON object; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} ist kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
    ),
    "The {field} field of {name}'s filament changed in Spoolman and isn't a JSON object now; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} mudou no Spoolman e agora não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} cambió en Spoolman y ahora no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} wurde in Spoolman geändert und ist jetzt kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段已在 Spoolman 中更改，现在不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
    ),
    "Spooler: {name} has new calibrated values. Open Spooler to save them to Spoolman or skip them.": (
        "Spooler: {name} tem novos valores de calibração. Abra o Spooler para salvá-los no Spoolman ou ignorá-los.",
        "Spooler: {name} tiene nuevos valores de calibración. Abre Spooler para guardarlos en Spoolman u omitirlos.",
        "Spooler: {name} hat neue Kalibrierungswerte. Öffnen Sie Spooler, um sie in Spoolman zu speichern oder zu überspringen.",
        "Spooler：{name} 有新的校准值。打开 Spooler 将其保存到 Spoolman，或跳过。",
    ),
    "Sent {settings} to Spoolman for {name}.": (
        "{settings} enviado(s) ao Spoolman para {name}.",
        "Se envió {settings} a Spoolman para {name}.",
        "{settings} für {name} an Spoolman gesendet.",
        "已将 {name} 的 {settings} 发送到 Spoolman。",
    ),
    "Kept Spoolman's newer value for {settings}: the preset now has it, and your change stays unsaved; send again to use yours, or discard it.": (
        "Mantido o valor mais recente do Spoolman para {settings}: o perfil agora tem esse valor e sua alteração continua não salva; envie de novo para usar a sua ou descarte-a.",
        "Se mantuvo el valor más reciente de Spoolman para {settings}: el perfil ya lo tiene y tu cambio sigue sin guardar; vuelve a enviarlo para usar el tuyo o descártalo.",
        "Der neuere Spoolman-Wert für {settings} wurde behalten: Das Profil hat ihn jetzt, und Ihre Änderung bleibt ungespeichert; senden Sie erneut, um Ihren Wert zu verwenden, oder verwerfen Sie ihn.",
        "已保留 Spoolman 中 {settings} 的较新值：预设现在使用该值，您的更改仍未保存；再次发送可使用您的值，或将其放弃。",
    ),
    "Not sent: {settings}. Spoolman's {field} field holds only calibration settings; colour, vendor, material and name come from its own fields.": (
        "Não enviado: {settings}. O campo {field} do Spoolman guarda só ajustes de calibração; cor, fabricante, material e nome vêm dos campos próprios dele.",
        "No enviado: {settings}. El campo {field} de Spoolman solo guarda ajustes de calibración; el color, el fabricante, el material y el nombre vienen de sus propios campos.",
        "Nicht gesendet: {settings}. Das Spoolman-Feld {field} enthält nur Kalibrierungseinstellungen; Farbe, Hersteller, Material und Name stammen aus eigenen Feldern.",
        "未发送：{settings}。Spoolman 的 {field} 字段只保存校准设置；颜色、供应商、材料和名称来自其各自的字段。",
    ),
    "The presets were not rebuilt: {error}": (
        "Os perfis não foram recriados: {error}",
        "Los perfiles no se reconstruyeron: {error}",
        "Die Profile wurden nicht neu erstellt: {error}",
        "预设未重建：{error}",
    ),
    "The filament presets were not rebuilt: {error}": (
        "Os perfis de filamento não foram recriados: {error}",
        "Los perfiles de filamento no se reconstruyeron: {error}",
        "Die Filamentprofile wurden nicht neu erstellt: {error}",
        "耗材丝预设未重建：{error}",
    ),
    "The filament presets could not be updated: {error}": (
        "Não foi possível atualizar os perfis de filamento: {error}",
        "No se pudieron actualizar los perfiles de filamento: {error}",
        "Die Filamentprofile konnten nicht aktualisiert werden: {error}",
        "无法更新耗材丝预设：{error}",
    ),
    "Synced {count} filament presets from Spoolman.": (
        "{count} perfis de filamento sincronizados do Spoolman.",
        "Se sincronizaron {count} perfiles de filamento desde Spoolman.",
        "{count} Filamentprofile aus Spoolman synchronisiert.",
        "已从 Spoolman 同步 {count} 个耗材丝预设。",
    ),
    "Setting a printer's spool needs Spoolman as the spool source.": (
        "Definir a bobina de uma impressora exige o Spoolman como origem das bobinas.",
        "Para asignar el carrete de una impresora, Spoolman debe ser el origen de los carretes.",
        "Zum Festlegen der Spule eines Druckers muss Spoolman die Spulenquelle sein.",
        "设置打印机的料盘需要以 Spoolman 作为料盘来源。",
    ),
    "Spooler can only set the spool on a single-extruder Klipper printer.": (
        "O Spooler só consegue definir a bobina em uma impressora Klipper de uma extrusora.",
        "Spooler solo puede asignar el carrete en una impresora Klipper de un extrusor.",
        "Spooler kann die Spule nur bei einem Klipper-Drucker mit einem Extruder festlegen.",
        "Spooler 只能为单挤出机的 Klipper 打印机设置料盘。",
    ),
    "{printer}: no active spool, Moonraker stopped booking usage.": (
        "{printer}: nenhuma bobina ativa, o Moonraker parou de registrar o consumo.",
        "{printer}: sin carrete activo, Moonraker dejó de registrar el consumo.",
        "{printer}: keine aktive Spule, Moonraker bucht keinen Verbrauch mehr.",
        "{printer}：没有活动料盘，Moonraker 已停止记录用量。",
    ),
    "{printer} manages its own spools; Spooler only reads them.": (
        "{printer} gerencia as próprias bobinas; o Spooler só as lê.",
        "{printer} gestiona sus propios carretes; Spooler solo los lee.",
        "{printer} verwaltet seine Spulen selbst; Spooler liest sie nur.",
        "{printer} 自行管理料盘；Spooler 只读取它们。",
    ),
    "{printer} is paused in a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está com uma impressão pausada: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} tiene una impresión en pausa: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} hat einen pausierten Druck: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 有一个已暂停的打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
    ),
    "{printer} is running a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está imprimindo: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} está imprimiendo: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} druckt gerade: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 正在打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
    ),
    "Could not set the spool on {printer}: {error}": (
        "Não foi possível definir a bobina em {printer}: {error}",
        "No se pudo asignar el carrete en {printer}: {error}",
        "Die Spule konnte auf {printer} nicht festgelegt werden: {error}",
        "无法为 {printer} 设置料盘：{error}",
    ),
    "That spool isn't in Spoolman, or it is archived.": (
        "Essa bobina não está no Spoolman ou está arquivada.",
        "Ese carrete no está en Spoolman o está archivado.",
        "Diese Spule ist nicht in Spoolman oder archiviert.",
        "该料盘不在 Spoolman 中，或已归档。",
    ),
    "Spool #{id} set from a scale weight of {grams} g.": (
        "Bobina #{id} ajustada pelo peso na balança de {grams} g.",
        "Carrete #{id} ajustado con un peso en báscula de {grams} g.",
        "Spule #{id} nach einem Waagengewicht von {grams} g gesetzt.",
        "已按称重 {grams} g 设置料盘 #{id}。",
    ),
    "Spool #{id} archived.": (
        "Bobina #{id} arquivada.",
        "Carrete #{id} archivado.",
        "Spule #{id} archiviert.",
        "料盘 #{id} 已归档。",
    ),
    "Spool #{id} unarchived.": (
        "Bobina #{id} desarquivada.",
        "Carrete #{id} desarchivado.",
        "Spule #{id} wiederhergestellt.",
        "料盘 #{id} 已取消归档。",
    ),
    "Spool #{id} marked as dried today.": (
        "Bobina #{id} marcada como secada hoje.",
        "Carrete #{id} marcado como secado hoy.",
        "Spule #{id} als heute getrocknet markiert.",
        "料盘 #{id} 已标记为今天烘干。",
    ),
    "Spool #{id} has no dried date now.": (
        "A bobina #{id} agora não tem data de secagem.",
        "El carrete #{id} ya no tiene fecha de secado.",
        "Spule #{id} hat jetzt kein Trocknungsdatum.",
        "料盘 #{id} 现在没有烘干日期。",
    ),
    "Spool #{id} now has {grams} g left.": (
        "A bobina #{id} agora tem {grams} g restantes.",
        "Al carrete #{id} ahora le quedan {grams} g.",
        "Spule #{id} hat jetzt noch {grams} g.",
        "料盘 #{id} 现在剩余 {grams} g。",
    ),
    "Spool #{id} moved to {location}.": (
        "Bobina #{id} movida para {location}.",
        "Carrete #{id} movido a {location}.",
        "Spule #{id} nach {location} verschoben.",
        "料盘 #{id} 已移至 {location}。",
    ),
    "Spool #{id} has no location now.": (
        "A bobina #{id} agora não tem local.",
        "El carrete #{id} ya no tiene ubicación.",
        "Spule #{id} hat jetzt keinen Lagerort.",
        "料盘 #{id} 现在没有位置。",
    ),
    "Saved the note on spool #{id}.": (
        "Nota da bobina #{id} salva.",
        "Nota del carrete #{id} guardada.",
        "Notiz zu Spule #{id} gespeichert.",
        "已保存料盘 #{id} 的备注。",
    ),
    "Spool #{id} has no note now.": (
        "A bobina #{id} agora não tem nota.",
        "El carrete #{id} ya no tiene nota.",
        "Spule #{id} hat jetzt keine Notiz.",
        "料盘 #{id} 现在没有备注。",
    ),
    "Added spool {spool} of the same filament.": (
        "Bobina {spool} do mesmo filamento adicionada.",
        "Se añadió el carrete {spool} del mismo filamento.",
        "Spule {spool} mit demselben Filament hinzugefügt.",
        "已添加相同耗材丝的料盘 {spool}。",
    ),
    "Added {count} spools of the same filament: {spools}.": (
        "{count} bobinas do mesmo filamento adicionadas: {spools}.",
        "Se añadieron {count} carretes del mismo filamento: {spools}.",
        "{count} Spulen mit demselben Filament hinzugefügt: {spools}.",
        "已添加 {count} 个相同耗材丝的料盘：{spools}。",
    ),
    "This Spoolman can't remove a spool's dried date; Spoolman 0.26 or newer can. Nothing was written; mark it dried again to change the date.": (
        "Este Spoolman não consegue remover a data de secagem de uma bobina; o Spoolman 0.26 ou mais recente consegue. Nada foi gravado; marque como secada de novo para mudar a data.",
        "Este Spoolman no puede quitar la fecha de secado de un carrete; Spoolman 0.26 o posterior sí puede. No se guardó nada; márcalo como secado de nuevo para cambiar la fecha.",
        "Dieses Spoolman kann das Trocknungsdatum einer Spule nicht entfernen; Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben; markiere sie erneut als getrocknet, um das Datum zu ändern.",
        "此 Spoolman 无法移除料盘的烘干日期；Spoolman 0.26 或更新版本可以。未写入任何内容；再次标记为已烘干即可更改日期。",
    ),
    "The value for {field} isn't valid; nothing was written.": (
        "O valor de {field} não é válido; nada foi gravado.",
        "El valor de {field} no es válido; no se guardó nada.",
        "Der Wert für {field} ist ungültig; es wurde nichts geschrieben.",
        "{field} 的值无效；未写入任何内容。",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell how this Spoolman saves extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe como este Spoolman salva campos extras. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe cómo guarda este Spoolman los campos extra. No se guardó nada; revisa la conexión y vuelve a intentarlo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, wie dieses Spoolman Zusatzfelder speichert. Es wurde nichts geschrieben; prüfe die Verbindung und versuche es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法判断此 Spoolman 如何保存额外字段。未写入任何内容；请检查连接后重试。",
    ),
    "This Spoolman can't empty an extra field ({fields}); Spoolman 0.26 or newer can. Nothing was written.": (
        "Este Spoolman não consegue esvaziar um campo extra ({fields}); o Spoolman 0.26 ou mais recente consegue. Nada foi gravado.",
        "Este Spoolman no puede vaciar un campo extra ({fields}); Spoolman 0.26 o posterior sí puede. No se guardó nada.",
        "Dieses Spoolman kann ein Zusatzfeld nicht leeren ({fields}); Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben.",
        "此 Spoolman 无法清空额外字段（{fields}）；Spoolman 0.26 或更新版本可以。未写入任何内容。",
    ),
    "Spooler couldn't read the extra fields Spoolman holds, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras que o Spoolman guarda, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra que guarda Spoolman, y esta versión de Spoolman los reemplaza todos en cada cambio. No se guardó nada.",
        "Spooler konnte die Zusatzfelder in Spoolman nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取 Spoolman 中的额外字段，而此 Spoolman 版本每次更改都会替换全部额外字段。未写入任何内容。",
    ),
    "Saved the filament of spool #{id}, but Spoolman refused the spool: {error}": (
        "O filamento da bobina #{id} foi salvo, mas o Spoolman recusou a bobina: {error}",
        "Se guardó el filamento del carrete #{id}, pero Spoolman rechazó el carrete: {error}",
        "Das Filament von Spule #{id} wurde gespeichert, aber Spoolman hat die Spule abgelehnt: {error}",
        "已保存料盘 #{id} 的耗材丝，但 Spoolman 拒绝了料盘：{error}",
    ),
    "Saved spool #{id} and its filament.": (
        "Bobina #{id} e seu filamento salvos.",
        "Se guardaron el carrete #{id} y su filamento.",
        "Spule #{id} und ihr Filament gespeichert.",
        "已保存料盘 #{id} 及其耗材丝。",
    ),
    "Saved spool #{id}.": (
        "Bobina #{id} salva.",
        "Carrete #{id} guardado.",
        "Spule #{id} gespeichert.",
        "已保存料盘 #{id}。",
    ),
    "Spool #{id} had no changes to save.": (
        "A bobina #{id} não tinha alterações para salvar.",
        "El carrete #{id} no tenía cambios que guardar.",
        "Spule #{id} hatte keine Änderungen zum Speichern.",
        "料盘 #{id} 没有需要保存的更改。",
    ),
    "Kept Spoolman's newer value for {fields}: it changed there while you were editing.": (
        "O valor mais recente do Spoolman foi mantido para {fields}: ele mudou lá enquanto você editava.",
        "Se mantuvo el valor más reciente de Spoolman para {fields}: cambió allí mientras editabas.",
        "Der neuere Wert aus Spoolman wurde für {fields} behalten: Er hat sich dort während deiner Bearbeitung geändert.",
        "已保留 Spoolman 中 {fields} 的较新值：你编辑期间它在那里被更改了。",
    ),
    "Created filament #{filament}, but Spoolman refused the spool: {error}": (
        "Filamento #{filament} criado, mas o Spoolman recusou a bobina: {error}",
        "Se creó el filamento #{filament}, pero Spoolman rechazó el carrete: {error}",
        "Filament #{filament} angelegt, aber Spoolman hat die Spule abgelehnt: {error}",
        "已创建耗材丝 #{filament}，但 Spoolman 拒绝了料盘：{error}",
    ),
    "Added spool #{id} with the new filament #{filament}.": (
        "Bobina #{id} adicionada com o novo filamento #{filament}.",
        "Se añadió el carrete #{id} con el nuevo filamento #{filament}.",
        "Spule #{id} mit dem neuen Filament #{filament} hinzugefügt.",
        "已添加料盘 #{id}，使用新耗材丝 #{filament}。",
    ),
    "Added spool #{id}.": (
        "Bobina #{id} adicionada.",
        "Se añadió el carrete #{id}.",
        "Spule #{id} hinzugefügt.",
        "已添加料盘 #{id}。",
    ),
    "Added spool {spools}, then Spoolman refused the next one: {error}": (
        "Bobina {spools} adicionada, depois o Spoolman recusou a próxima: {error}",
        "Se añadió el carrete {spools} y luego Spoolman rechazó el siguiente: {error}",
        "Spule {spools} hinzugefügt, dann hat Spoolman die nächste abgelehnt: {error}",
        "已添加料盘 {spools}，随后 Spoolman 拒绝了下一个：{error}",
    ),
    "Opened spool #{id} in Spoolman.": (
        "Bobina #{id} aberta no Spoolman.",
        "Carrete #{id} abierto en Spoolman.",
        "Spule #{id} in Spoolman geöffnet.",
        "已在 Spoolman 中打开料盘 #{id}。",
    ),
    "Unknown spool action.": (
        "Ação de bobina desconhecida.",
        "Acción de carrete desconocida.",
        "Unbekannte Spulenaktion.",
        "未知的料盘操作。",
    ),
    "Spool actions need Spoolman as the source.": (
        "As ações de bobina exigem o Spoolman como origem.",
        "Las acciones de carrete necesitan Spoolman como origen.",
        "Spulenaktionen erfordern Spoolman als Quelle.",
        "料盘操作需要以 Spoolman 作为来源。",
    ),
    "No spool chosen.": (
        "Nenhuma bobina escolhida.",
        "No se eligió ningún carrete.",
        "Keine Spule ausgewählt.",
        "未选择料盘。",
    ),
    "The spool source changed since this list was read; nothing was written. Refresh and try again.": (
        "A origem das bobinas mudou desde que esta lista foi lida; nada foi gravado. Atualize e tente de novo.",
        "El origen de los carretes cambió desde que se leyó esta lista; no se escribió nada. Actualiza e inténtalo de nuevo.",
        "Die Spulenquelle hat sich seit dem Lesen dieser Liste geändert; es wurde nichts geschrieben. Aktualisieren Sie und versuchen Sie es erneut.",
        "读取此列表后料盘来源已更改；未写入任何内容。请刷新后重试。",
    ),
    "Spoolman has the change, but Spooler could not update its history file.": (
        "O Spoolman tem a alteração, mas o Spooler não conseguiu atualizar seu arquivo de histórico.",
        "Spoolman tiene el cambio, pero Spooler no pudo actualizar su archivo de historial.",
        "Spoolman hat die Änderung, aber Spooler konnte seine Verlaufsdatei nicht aktualisieren.",
        "Spoolman 已有该更改，但 Spooler 无法更新其历史文件。",
    ),
    "This print was recorded for another spool source, or before Spooler noted which Spoolman it belongs to, so Spooler won't book it here. If it is still owed, book it in Spoolman by hand.": (
        "Esta impressão foi registrada para outra origem de bobinas, ou antes de o Spooler anotar a qual Spoolman ela pertence, então o Spooler não vai lançá-la aqui. Se ainda estiver pendente, lance-a à mão no Spoolman.",
        "Esta impresión se registró para otro origen de carretes, o antes de que Spooler anotara a qué Spoolman pertenece, así que Spooler no la registrará aquí. Si sigue pendiente, regístrala a mano en Spoolman.",
        "Dieser Druck wurde für eine andere Spulenquelle erfasst oder bevor Spooler vermerkt hat, zu welchem Spoolman er gehört, daher bucht Spooler ihn hier nicht. Falls er noch offen ist, buchen Sie ihn von Hand in Spoolman.",
        "此打印记录属于另一个料盘来源，或记录于 Spooler 标明其所属 Spoolman 之前，因此 Spooler 不会在此记账。如果仍需记录，请在 Spoolman 中手动记录。",
    ),
    "Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; adjust the spools in Spoolman by hand.": (
        "Desfazer exige o Spoolman 0.18 ou mais recente, que devolve os gramas em uma etapa sem perder o consumo registrado nesse meio-tempo. O Spooler não conseguiu confirmar a versão deste Spoolman, então nada mudou; ajuste as bobinas à mão no Spoolman.",
        "Deshacer necesita Spoolman 0.18 o posterior, que devuelve los gramos en un solo paso sin perder el consumo registrado mientras tanto. Spooler no pudo confirmar la versión de este Spoolman, así que no cambió nada; ajusta los carretes a mano en Spoolman.",
        "Rückgängig machen erfordert Spoolman 0.18 oder neuer, das Gramm in einem Schritt zurückbucht, ohne zwischenzeitlich gebuchten Verbrauch zu verlieren. Spooler konnte die Version dieses Spoolman nicht bestätigen, daher wurde nichts geändert; passen Sie die Spulen von Hand in Spoolman an.",
        "撤销需要 Spoolman 0.18 或更新版本，它能一步加回克数，且不会丢失期间记录的用量。Spooler 无法确认此 Spoolman 的版本，因此未做任何更改；请在 Spoolman 中手动调整料盘。",
    ),
    "Spooler could not save its booking state ({file}), so it stopped. Rows it was sending are marked for you to check in Spoolman.": (
        "O Spooler não conseguiu salvar seu estado de lançamentos ({file}), então parou. As linhas que ele estava enviando estão marcadas para você conferir no Spoolman.",
        "Spooler no pudo guardar su estado de registros ({file}), así que se detuvo. Las filas que estaba enviando quedan marcadas para que las revises en Spoolman.",
        "Spooler konnte seinen Buchungsstand ({file}) nicht speichern und hat daher angehalten. Zeilen, die gerade gesendet wurden, sind markiert, damit Sie sie in Spoolman prüfen.",
        "Spooler 无法保存其记账状态（{file}），因此已停止。正在发送的行已标记，请在 Spoolman 中核对。",
    ),
    "Spooler can't tell whether Spoolman applied this. Check the spool in Spoolman, then say which.": (
        "O Spooler não sabe se o Spoolman aplicou isto. Confira a bobina no Spoolman e diga o que aconteceu.",
        "Spooler no sabe si Spoolman aplicó esto. Revisa el carrete en Spoolman y di qué ocurrió.",
        "Spooler kann nicht erkennen, ob Spoolman dies übernommen hat. Prüfen Sie die Spule in Spoolman und geben Sie an, was zutrifft.",
        "Spooler 无法确定 Spoolman 是否已应用此操作。请在 Spoolman 中检查料盘，然后说明结果。",
    ),
    "Other": (
        "Outro",
        "Otro",
        "Sonstiges",
        "其他",
    ),
    "Could not reach GitHub ({reason})": (
        "Não foi possível acessar o GitHub ({reason})",
        "No se pudo conectar con GitHub ({reason})",
        "GitHub ist nicht erreichbar ({reason})",
        "无法连接 GitHub（{reason}）",
    ),
    "GitHub sent an answer Spooler doesn't understand": (
        "O GitHub enviou uma resposta que o Spooler não entende",
        "GitHub envió una respuesta que Spooler no entiende",
        "GitHub hat eine Antwort gesendet, die Spooler nicht versteht",
        "GitHub 返回了 Spooler 无法识别的回复",
    ),
    "No published release found yet": (
        "Nenhuma versão publicada ainda",
        "Aún no hay ninguna versión publicada",
        "Noch keine veröffentlichte Version gefunden",
        "尚未找到已发布的版本",
    ),
    "GitHub returned HTTP {code}": (
        "O GitHub retornou HTTP {code}",
        "GitHub devolvió HTTP {code}",
        "GitHub meldete HTTP {code}",
        "GitHub 返回 HTTP {code}",
    ),
    "{slot} {need} but {supply}{tracked}": (
        "{slot} {need}, mas {supply}{tracked}",
        "{slot} {need}, pero {supply}{tracked}",
        "{slot} {need}, aber {supply}{tracked}",
        "{slot}{need}，但{supply}{tracked}",
    ),
    " Swap in spool #{id} ({location}, {grams} g).": (
        " Troque pela bobina #{id} ({location}, {grams} g).",
        " Cambia al carrete #{id} ({location}, {grams} g).",
        " Wechseln Sie zu Spule #{id} ({location}, {grams} g).",
        "可换用料盘 #{id}（{location}，{grams} g）。",
    ),
    " Swap in spool #{id} ({grams} g).": (
        " Troque pela bobina #{id} ({grams} g).",
        " Cambia al carrete #{id} ({grams} g).",
        " Wechseln Sie zu Spule #{id} ({grams} g).",
        "可换用料盘 #{id}（{grams} g）。",
    ),
    "of {matches} matching spools the fullest has {have} and the smallest has {worst}, so make sure the right one is loaded": (
        "das {matches} bobinas compatíveis, a mais cheia tem {have} e a mais vazia tem {worst}, então confira se a certa está carregada",
        "de {matches} carretes compatibles, el más lleno tiene {have} y el más vacío {worst}, así que asegúrate de que esté cargado el correcto",
        "von {matches} passenden Spulen hat die vollste {have} und die leerste {worst}, also achten Sie darauf, dass die richtige geladen ist",
        "在 {matches} 个匹配料盘中，最满的有 {have}，最少的只有 {worst}，请确认装入的是正确的料盘",
    ),
    "the {count} fullest of {matches} matching spools hold {have} and the {count} smallest hold {worst}, so make sure the right ones are loaded": (
        "das {matches} bobinas compatíveis, as {count} mais cheias têm {have} e as {count} mais vazias têm {worst}, então confira se as certas estão carregadas",
        "de {matches} carretes compatibles, los {count} más llenos tienen {have} y los {count} más vacíos {worst}, así que asegúrate de que estén cargados los correctos",
        "von {matches} passenden Spulen haben die {count} vollsten {have} und die {count} leersten {worst}, also achten Sie darauf, dass die richtigen geladen sind",
        "在 {matches} 个匹配料盘中，最满的 {count} 个共有 {have}，最少的 {count} 个只有 {worst}，请确认装入的是正确的料盘",
    ),
    "{slot} {need}; {body}": (
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot}{need}；{body}",
    ),
    "{slot} {need} ({padded} with the {margin}% margin) and {supply}{tracked}": (
        "{slot} {need} ({padded} com a margem de {margin}%) e {supply}{tracked}",
        "{slot} {need} ({padded} con el margen del {margin} %) y {supply}{tracked}",
        "{slot} {need} ({padded} mit {margin} % Reserve) und {supply}{tracked}",
        "{slot}{need}（加上 {margin}% 余量为 {padded}），而{supply}{tracked}",
    ),
    "{slot} {need}, {supply}": (
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot}{need}，{supply}",
    ),
    "not enough filament loaded in the AMS.": (
        "filamento insuficiente carregado no AMS.",
        "no hay suficiente filamento cargado en el AMS.",
        "nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝不足。",
    ),
    "not enough filament loaded.": (
        "filamento insuficiente carregado.",
        "no hay suficiente filamento cargado.",
        "nicht genug Filament geladen.",
        "装入的耗材丝不足。",
    ),
    "not enough filament may be loaded in the AMS.": (
        "talvez não haja filamento suficiente carregado no AMS.",
        "puede que no haya suficiente filamento cargado en el AMS.",
        "möglicherweise ist nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝可能不足。",
    ),
    "not enough filament may be loaded.": (
        "talvez não haja filamento suficiente carregado.",
        "puede que no haya suficiente filamento cargado.",
        "möglicherweise ist nicht genug Filament geladen.",
        "装入的耗材丝可能不足。",
    ),
    "also check: ": (
        "confira também: ",
        "revisa también: ",
        "prüfen Sie auch: ",
        "另请检查：",
    ),
    "also barely enough: ": (
        "também no limite: ",
        "también muy justo: ",
        "ebenfalls knapp: ",
        "同样勉强够用：",
    ),
    "barely enough filament.": (
        "filamento no limite.",
        "filamento muy justo.",
        "Filament knapp.",
        "耗材丝勉强够用。",
    ),
    "quantity OK.": (
        "quantidade OK.",
        "cantidad correcta.",
        "Menge OK.",
        "用量充足。",
    ),
    "quantity OK for slots {slots}.": (
        "quantidade OK para os slots {slots}.",
        "cantidad correcta para las ranuras {slots}.",
        "Menge OK für Slots {slots}.",
        "槽位 {slots} 用量充足。",
    ),
    "no spool found for {slots}, so they weren't checked": (
        "nenhuma bobina encontrada para {slots}, então não foram conferidos",
        "no se encontró carrete para {slots}, así que no se comprobaron",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
    ),
    "no spool found for {slots}, so it wasn't checked": (
        "nenhuma bobina encontrada para {slots}, então não foi conferido",
        "no se encontró carrete para {slots}, así que no se comprobó",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
    ),
    "Not checked": (
        "Não conferido",
        "Sin comprobar",
        "Nicht geprüft",
        "未检查",
    ),
    "no spool found for these slots": (
        "nenhuma bobina encontrada para estes slots",
        "no se encontró carrete para estas ranuras",
        "keine Spule für diese Slots gefunden",
        "未找到这些槽位的料盘",
    ),
    "no spool found for this slot": (
        "nenhuma bobina encontrada para este slot",
        "no se encontró carrete para esta ranura",
        "keine Spule für diesen Slot gefunden",
        "未找到此槽位的料盘",
    ),
    "Quantity OK": (
        "Quantidade OK",
        "Cantidad correcta",
        "Menge OK",
        "用量充足",
    ),
    "Barely enough": (
        "No limite",
        "Muy justo",
        "Knapp",
        "勉强够用",
    ),
    "Not enough": (
        "Insuficiente",
        "Insuficiente",
        "Nicht genug",
        "不足",
    ),
    "Check the spools": (
        "Confira as bobinas",
        "Revisa los carretes",
        "Spulen prüfen",
        "检查料盘",
    ),
    "Check the spool": (
        "Confira a bobina",
        "Revisa el carrete",
        "Spule prüfen",
        "检查料盘",
    ),
    "{need} needed · matching spools hold {low} to {high}": (
        "{need} necessários · as bobinas compatíveis têm de {low} a {high}",
        "{need} necesarios · los carretes compatibles tienen de {low} a {high}",
        "{need} benötigt · passende Spulen haben {low} bis {high}",
        "需要 {need} · 匹配料盘有 {low} 至 {high}",
    ),
    "{need} needed · {have} across {count} spools": (
        "{need} necessários · {have} em {count} bobinas",
        "{need} necesarios · {have} en {count} carretes",
        "{need} benötigt · {have} auf {count} Spulen",
        "需要 {need} · {count} 个料盘共 {have}",
    ),
    "{need} needed · leaves {left}": (
        "{need} necessários · sobram {left}",
        "{need} necesarios · quedan {left}",
        "{need} benötigt · {left} bleiben übrig",
        "需要 {need} · 剩余 {left}",
    ),
    "{need} needed · every matching spool has at least {low}": (
        "{need} necessários · toda bobina compatível tem pelo menos {low}",
        "{need} necesarios · cada carrete compatible tiene al menos {low}",
        "{need} benötigt · jede passende Spule hat mindestens {low}",
        "需要 {need} · 每个匹配料盘至少有 {low}",
    ),
    "{need} needed · {have} left": (
        "{need} necessários · restam {have}",
        "{need} necesarios · quedan {have}",
        "{need} benötigt · {have} übrig",
        "需要 {need} · 剩余 {have}",
    ),
    "{count} slots, pooled": (
        "{count} slots, somados",
        "{count} ranuras, sumadas",
        "{count} Slots, zusammengefasst",
        "{count} 个槽位，合并计算",
    ),
    "Spooler: no Spoolman address is set up yet, so the filament quantity wasn't checked.": (
        "Spooler: nenhum endereço do Spoolman configurado ainda, então a quantidade de filamento não foi conferida.",
        "Spooler: aún no hay una dirección de Spoolman configurada, así que no se comprobó la cantidad de filamento.",
        "Spooler: Es ist noch keine Spoolman-Adresse eingerichtet, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：尚未设置 Spoolman 地址，因此未检查耗材丝用量。",
    ),
    "Spooler: couldn't reach {source}, so the filament quantity wasn't checked.": (
        "Spooler: não foi possível acessar {source}, então a quantidade de filamento não foi conferida.",
        "Spooler: no se pudo conectar con {source}, así que no se comprobó la cantidad de filamento.",
        "Spooler: {source} ist nicht erreichbar, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：无法连接 {source}，因此未检查耗材丝用量。",
    ),
    "Could not write settings to {file}. Check that this folder is writable.": (
        "Não foi possível gravar os ajustes em {file}. Verifique se a pasta permite gravação.",
        "No se pudieron guardar los ajustes en {file}. Comprueba que se pueda escribir en esa carpeta.",
        "Die Einstellungen konnten nicht in {file} geschrieben werden. Prüfen Sie, ob dieser Ordner beschreibbar ist.",
        "无法将设置写入 {file}。请检查该文件夹是否可写。",
    ),
    "{plugin} - Settings & About": (
        "{plugin} - Ajustes e Sobre",
        "{plugin} - Ajustes e información",
        "{plugin} - Einstellungen & Info",
        "{plugin} - 设置与关于",
    ),
    "Opened {plugin}": (
        "{plugin} aberto",
        "{plugin} abierto",
        "{plugin} geöffnet",
        "已打开 {plugin}",
    ),
    "Open the {plugin} tab once, then run this again.": (
        "Abra a aba {plugin} uma vez e rode isto de novo.",
        "Abre la pestaña {plugin} una vez y vuelve a ejecutar esto.",
        "Öffnen Sie einmal den Tab {plugin} und führen Sie dies dann erneut aus.",
        "请先打开一次 {plugin} 标签页，然后再次运行。",
    ),
    "The selected printer preset has no host address.": (
        "O perfil de impressora selecionado não tem endereço do host.",
        "El perfil de impresora seleccionado no tiene dirección de host.",
        "Das ausgewählte Druckerprofil hat keine Host-Adresse.",
        "所选打印机预设没有主机地址。",
    ),
    "OrcaSlicer refused a filament slot change from Spooler's background thread, so keeping the slots synced automatically is off. Use Plugins > Run > Spooler: Keep Slots Synced instead.": (
        "O OrcaSlicer recusou uma alteração de slot de filamento feita em segundo plano pelo Spooler, então a sincronização automática dos slots foi desligada. Use Plugins > Executar > Spooler: Keep Slots Synced.",
        "OrcaSlicer rechazó un cambio de ranura de filamento hecho en segundo plano por Spooler, así que la sincronización automática de ranuras quedó desactivada. Usa Plugins > Ejecutar > Spooler: Keep Slots Synced.",
        "OrcaSlicer hat eine Filament-Slot-Änderung aus dem Hintergrund-Thread von Spooler abgelehnt, daher ist das automatische Synchronisieren der Slots aus. Verwenden Sie stattdessen Plugins > Ausführen > Spooler: Keep Slots Synced.",
        "OrcaSlicer 拒绝了 Spooler 后台线程发起的耗材丝槽位更改，因此已关闭槽位自动同步。请改用 插件 > 运行 > Spooler: Keep Slots Synced。",
    ),
    "Stopped keeping the filament slots synced.": (
        "Os slots de filamento não estão mais sendo sincronizados.",
        "Se dejó de sincronizar las ranuras de filamento.",
        "Die Filament-Slots werden nicht mehr synchronisiert.",
        "已停止同步耗材丝槽位。",
    ),
    "Stopped keeping the filament slots synced automatically until OrcaSlicer restarts. Run this again to keep them synced, or turn the setting off and on to restart it.": (
        "A sincronização automática dos slots de filamento parou até o OrcaSlicer reiniciar. Rode isto de novo para mantê-los sincronizados, ou desligue e ligue o ajuste para reiniciá-la.",
        "Se dejó de sincronizar automáticamente las ranuras de filamento hasta que OrcaSlicer se reinicie. Vuelve a ejecutar esto para mantenerlas sincronizadas, o desactiva y activa el ajuste para reiniciarla.",
        "Die automatische Synchronisierung der Filament-Slots ist bis zum Neustart von OrcaSlicer beendet. Führen Sie dies erneut aus, um sie synchron zu halten, oder schalten Sie die Einstellung aus und wieder ein.",
        "已停止自动同步耗材丝槽位，直到 OrcaSlicer 重启。再次运行可继续同步，或将该设置关闭再打开以重新启动。",
    ),
    "Keep Slots Synced is already running.": (
        "Keep Slots Synced já está em execução.",
        "Keep Slots Synced ya se está ejecutando.",
        "Keep Slots Synced läuft bereits.",
        "Keep Slots Synced 已在运行。",
    ),
    "Spoolman sent a spool list Spooler doesn't understand": (
        "O Spoolman enviou uma lista de bobinas que o Spooler não entende",
        "Spoolman envió una lista de carretes que Spooler no entiende",
        "Spoolman hat eine Spulenliste gesendet, die Spooler nicht versteht",
        "Spoolman 返回了 Spooler 无法识别的料盘列表",
    ),
    "Syncing presets needs Spoolman as the source.": (
        "Sincronizar perfis exige o Spoolman como origem.",
        "Sincronizar perfiles necesita Spoolman como origen.",
        "Das Synchronisieren von Presets erfordert Spoolman als Quelle.",
        "同步预设需要以 Spoolman 作为来源。",
    ),
    "Could not read OrcaSlicer's presets.": (
        "Não foi possível ler os perfis do OrcaSlicer.",
        "No se pudieron leer los perfiles de OrcaSlicer.",
        "Die OrcaSlicer-Profile konnten nicht gelesen werden.",
        "无法读取 OrcaSlicer 的预设。",
    ),
    "Already sending to Spoolman; try again in a moment.": (
        "Já enviando ao Spoolman; tente de novo daqui a pouco.",
        "Ya se está enviando a Spoolman; inténtalo de nuevo en un momento.",
        "Es wird bereits an Spoolman gesendet; versuchen Sie es gleich erneut.",
        "正在发送到 Spoolman；请稍后重试。",
    ),
    "Sending needs Spoolman as the source.": (
        "O envio exige o Spoolman como origem.",
        "Enviar necesita Spoolman como origen.",
        "Senden erfordert Spoolman als Quelle.",
        "发送需要以 Spoolman 作为来源。",
    ),
    "Enter a weight between 0 and {max} g.": (
        "Digite um peso entre 0 e {max} g.",
        "Introduce un peso entre 0 y {max} g.",
        "Geben Sie ein Gewicht zwischen 0 und {max} g ein.",
        "请输入 0 到 {max} g 之间的重量。",
    ),
    "Used {grams} g of spool #{id}.": (
        "{grams} g da bobina #{id} usados.",
        "Se usaron {grams} g del carrete #{id}.",
        "{grams} g von Spule #{id} verbraucht.",
        "已使用料盘 #{id} 的 {grams} g。",
    ),
    "A location is text of at most {max} characters.": (
        "O local é um texto de no máximo {max} caracteres.",
        "La ubicación es un texto de {max} caracteres como máximo.",
        "Ein Lagerort ist Text mit höchstens {max} Zeichen.",
        "位置为最多 {max} 个字符的文本。",
    ),
    "Enter the grams left, from 0 to {max} g.": (
        "Digite os gramas restantes, de 0 a {max} g.",
        "Introduce los gramos restantes, de 0 a {max} g.",
        "Geben Sie die verbleibenden Gramm ein, von 0 bis {max} g.",
        "请输入剩余克数，0 到 {max} g。",
    ),
    "A note is text of at most {max} characters.": (
        "A nota é um texto de no máximo {max} caracteres.",
        "La nota es un texto de {max} caracteres como máximo.",
        "Eine Notiz ist Text mit höchstens {max} Zeichen.",
        "备注为最多 {max} 个字符的文本。",
    ),
    "That spool has no filament to copy.": (
        "Essa bobina não tem filamento para copiar.",
        "Ese carrete no tiene filamento que copiar.",
        "Diese Spule hat kein Filament zum Kopieren.",
        "该料盘没有可复制的耗材丝。",
    ),
    "Add 1 to {max} spools at a time.": (
        "Adicione de 1 a {max} bobinas por vez.",
        "Añade de 1 a {max} carretes a la vez.",
        "Fügen Sie 1 bis {max} Spulen auf einmal hinzu.",
        "每次可添加 1 到 {max} 个料盘。",
    ),
    "Could not write the export: {error}": (
        "Não foi possível gravar a exportação: {error}",
        "No se pudo escribir la exportación: {error}",
        "Der Export konnte nicht geschrieben werden: {error}",
        "无法写入导出文件：{error}",
    ),
    "Spoolman could not be read": (
        "Não foi possível ler o Spoolman",
        "No se pudo leer Spoolman",
        "Spoolman konnte nicht gelesen werden",
        "无法读取 Spoolman",
    ),
    "OrcaSlicer's data folder was not found": (
        "A pasta de dados do OrcaSlicer não foi encontrada",
        "No se encontró la carpeta de datos de OrcaSlicer",
        "Der Datenordner von OrcaSlicer wurde nicht gefunden",
        "未找到 OrcaSlicer 的数据文件夹",
    ),
    "Could not read Spoolman.": (
        "Não foi possível ler o Spoolman.",
        "No se pudo leer Spoolman.",
        "Spoolman konnte nicht gelesen werden.",
        "无法读取 Spoolman。",
    ),
    "{text}: {detail}": (
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}：{detail}",
    ),
    "{text} ({detail})": (
        "{text} ({detail})",
        "{text} ({detail})",
        "{text} ({detail})",
        "{text}（{detail}）",
    ),
    "Spool {id}": (
        "Bobina {id}",
        "Carrete {id}",
        "Spule {id}",
        "料盘 {id}",
    ),
    "spool {id}": (
        "bobina {id}",
        "carrete {id}",
        "Spule {id}",
        "料盘 {id}",
    ),
    "Could not read the spool list: {error}": (
        "Não foi possível ler a lista de bobinas: {error}",
        "No se pudo leer la lista de carretes: {error}",
        "Die Spulenliste konnte nicht gelesen werden: {error}",
        "无法读取料盘列表：{error}",
    ),
    "Test the connection successfully before saving.": (
        "Teste a conexão com sucesso antes de salvar.",
        "Prueba la conexión con éxito antes de guardar.",
        "Testen Sie die Verbindung erfolgreich, bevor Sie speichern.",
        "保存前请先成功测试连接。",
    ),
    "Auto Bed Levelling": (
        "Nivelamento automático da mesa",
        "Nivelación de cama automática",
        "Automatische Druckbettnivellierung",
        "自动热床调平",
    ),
    "Heating Bed": (
        "Aquecendo a mesa",
        "Precalentamiento de la cama",
        "Heizbett vorheizen",
        "预加热热床",
    ),
    "Sweeping XY Mech Mode": (
        "Varredura do modo mecânico XY",
        "Barrido del modo mecánico XY",
        "XY-Mechanik-Modus-Abtastung",
        "XY 机械模式扫描",
    ),
    "Changing Filament": (
        "Trocando o filamento",
        "Cambiando el filamento",
        "Filament wechseln",
        "换料",
    ),
    "Paused": (
        "Pausado",
        "En pausa",
        "Pausiert",
        "已暂停",
    ),
    "Paused: Filament Runout": (
        "Pausa (fim do filamento)",
        "Pausa (filamento agotado)",
        "Pause (Filament leer)",
        "暂停（耗材丝耗尽）",
    ),
    "Heating Nozzle": (
        "Aquecendo o bico",
        "Calentando la boquilla",
        "Düse wird erhitzt",
        "加热喷嘴",
    ),
    "Calibrating Extrusion": (
        "Calibrando a extrusão",
        "Calibrando la extrusión",
        "Extrusion wird kalibriert",
        "校准挤出",
    ),
    "Scanning Bed Surface": (
        "Digitalizando a superfície da mesa",
        "Escaneando la superficie de la cama",
        "Scan der Druckbettoberfläche",
        "扫描热床",
    ),
    "Inspecting First Layer": (
        "Inspecionando a primeira camada",
        "Inspeccionando la primera capa",
        "Überprüfung der ersten Schicht",
        "扫描首层",
    ),
    "Identifying Build Plate": (
        "Identificando o tipo de placa de impressão",
        "Identificando el tipo de cama de impresión",
        "Identifikation der Druckplatte",
        "识别打印板类型",
    ),
    "Calibrating Micro Lidar": (
        "Calibrando Micro Lidar",
        "Calibrando micro Lidar",
        "Kalibrierung des Mikro-Lidars",
        "校准 Micro Lidar",
    ),
    "Homing Toolhead": (
        "Reposicionando o cabeçote",
        "Homing del cabezal",
        "Referenzfahrt des Werkzeugkopfes",
        "工具头回原点",
    ),
    "Cleaning Nozzle Tip": (
        "Limpando a ponta do bico",
        "Limpiando la boquilla",
        "Reinigen der Düse",
        "清理喷嘴头",
    ),
    "Checking Extruder Temperature": (
        "Verificando a temperatura da extrusora",
        "Comprobando la temperatura del extrusor",
        "Überprüfen der Extrudertemperatur",
        "检查挤出温度",
    ),
    "Paused by User": (
        "Pausado pelo usuário",
        "Pausado por el usuario",
        "Vom Benutzer pausiert",
        "已被用户暂停",
    ),
    "Paused: Front Cover Removed": (
        "Pausa (tampa frontal removida)",
        "Pausa (se cayó la tapa delantera)",
        "Pause (Frontabdeckung abgefallen)",
        "暂停（前盖脱落）",
    ),
    "Calibrating Extrusion Flow": (
        "Calibrando o fluxo de extrusão",
        "Calibrando el flujo de extrusión",
        "Extrusionsfluss wird kalibriert",
        "校准挤出流量",
    ),
    "Paused: Nozzle Temperature Fault": (
        "Pausa (falha na temperatura do bico)",
        "Pausa (fallo en la temperatura de la boquilla)",
        "Pause (Düsentemperaturstörung)",
        "暂停（喷嘴温度故障）",
    ),
    "Paused: Bed Temperature Fault": (
        "Pausa (falha na temperatura da mesa)",
        "Pausa (fallo en la temperatura de la cama caliente)",
        "Pause (Heizbetttemperaturstörung)",
        "暂停（热床温度故障）",
    ),
    "Unloading Filament": (
        "Descarregando o filamento",
        "Descarga de filamento",
        "Entladen des Filaments",
        "耗材丝退料中",
    ),
    "Paused: Skipped Step": (
        "Pausa (perda de passos)",
        "Pausa (pasos perdidos)",
        "Pause (Schrittverlust)",
        "暂停（电机丢步）",
    ),
    "Loading Filament": (
        "Carregando o filamento",
        "Carga de filamento",
        "Laden des Filaments",
        "耗材丝进料中",
    ),
    "Calibrating Motor Noise": (
        "Calibrando o ruído do motor",
        "Calibrando el ruido del motor",
        "Motorgeräusch wird kalibriert",
        "电机噪音校准",
    ),
    "Paused: AMS Lost": (
        "Pausa (AMS desconectado)",
        "Pausa (AMS perdido)",
        "Pause (AMS getrennt)",
        "暂停（AMS 断开）",
    ),
    "Paused: Heat Break Fan": (
        "Pausa (ventoinha do heatbreak)",
        "Pausa (baja velocidad del ventilador del disipador térmico)",
        "Pause (zu kleine Geschwindigkeit des Heatbreak-Lüfters)",
        "暂停（散热风扇低速）",
    ),
    "Paused: Chamber Temperature Fault": (
        "Pausa (falha na temperatura da câmara)",
        "Pausa (problema con el control de temperatura de la recámara)",
        "Pause (Kammertemperaturregelungsproblem)",
        "暂停（腔体温度控制问题）",
    ),
    "Cooling Chamber": (
        "Resfriando a câmara",
        "Enfriando la recámara",
        "Kühlung der Kammer",
        "腔体降温中",
    ),
    "Paused by G-code": (
        "Pausado por G-code",
        "Pausa (G-code insertado por el usuario)",
        "Pause (vom Benutzer eingefügter G-Code)",
        "暂停（用户插入的 G-code）",
    ),
    "Motor Noise Showoff": (
        "Demonstração do ruído do motor",
        "Demostración del ruido del motor",
        "Motorgeräusch-Showoff",
        "电机噪音校准结果展示",
    ),
    "Paused: Nozzle Covered": (
        "Pausa (bico coberto de filamento)",
        "Pausa (boquilla cubierta de filamento)",
        "Pause (Düse mit Filament bedeckt)",
        "暂停（喷嘴被耗材丝包裹）",
    ),
    "Paused: Cutter Error": (
        "Pausa (erro do cortador)",
        "Pausa (error del cortador)",
        "Pause (Schneidfehler)",
        "暂停（切刀错误）",
    ),
    "Paused: First Layer Error": (
        "Pausa (erro na primeira camada)",
        "Pausa (error en la primera capa)",
        "Pause (Fehler in der ersten Schicht)",
        "暂停（首层错误）",
    ),
    "Paused: Nozzle Clog": (
        "Pausa (bico entupido)",
        "Pausa (boquilla obstruida)",
        "Pause (Düsenverstopfung)",
        "暂停（喷嘴堵塞）",
    ),
}
_TEXTS = {lang: {en: row[i] for en, row in _TEXT_ROWS.items()} for i, lang in enumerate(_TEXT_LANGS)}


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
        "save_calibration": calibration_mode(),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None) -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window)."""
    text_language(fresh=True)  # built on the UI thread: Python's own texts follow the same choice
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
            tr("Could not write settings to {file}. Check that this folder is writable.", file=SETTINGS_FILE),
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
            title=tr("{plugin} - Settings & About", plugin=PLUGIN_NAME),
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
            save_calibration_mode(data.get("save_calibration"))
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
                        "error": tr("Test the connection successfully before saving."),
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
        elif msg_type in ("calibration_save", "calibration_skip"):
            answer_calibration(data, self._post)
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
                "error": tr("No Spoolman URL configured yet - click Settings to set one."),
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
                result = {"ok": False, "error": tr("Could not read the spool list: {error}", error=exc)}
            finally:
                self._refreshing = False
            if panel.is_open():
                panel.post({"type": "spools", "low_stock_grams": low_stock_grams,
                            "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                            "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            "calibration": calibration_asks(),
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
        return orca.ExecutionResult.success(tr("Opened {plugin}", plugin=PLUGIN_NAME))



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
                elif msg_type in ("calibration_save", "calibration_skip"):
                    answer_calibration(data, self.post_message)
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
                    "error": tr("No Spoolman URL configured yet - click Settings to set one."),
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
                    result = {"ok": False, "error": tr("Could not read the spool list: {error}", error=exc)}
                finally:
                    self._refreshing = False
                self.post_message({"type": "spools", "low_stock_grams": low_stock_grams,
                                   "weight_display": weight_mode(), "show_cart": cart_on(), "display": display_settings(),
                                   "spool_columns": spool_columns(), "source": source(), **printer_state(),
                            "calibration": calibration_asks(),
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
                tr("Could not write settings to {file}. Check that this folder is writable.", file=SETTINGS_FILE),
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
                "save_calibration": calibration_mode(),
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
                save_calibration_mode(data.get("save_calibration"))
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
                        "error": tr("Test the connection successfully before saving."),
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
        raise RuntimeError(tr("Open the {plugin} tab once, then run this again.", plugin=PLUGIN_NAME))
    if not snap.get("host"):
        raise RuntimeError(tr("The selected printer preset has no host address."))
    with pinned_origin() as origin:
        result = get_spools("" if origin[0] == BAMBU_KEY else origin[0])
        if not result["ok"]:
            raise RuntimeError(result["error"])
        state = profile_sync(result["spools"], snap)
    if state["error"]:
        raise RuntimeError(tr("The filament presets could not be updated: {error}", error=state["error"]))
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
    text = tr("Loaded {count} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot "
              "colours, so a slot keeps its old colour until you pick its filament in the dropdown.", count=done)
    if missing:
        text += tr(" No Spoolman filament matched slot(s) {slots}.", slots=", ".join(map(str, missing)))
    if failed:
        text += tr(" Could not change slot(s) {slots}.", slots=", ".join(map(str, failed)))
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
AUTO_KEEP_REFUSED = ("OrcaSlicer refused a filament slot change from Spooler's background thread, so "
                     "keeping the slots synced automatically is off. Use Plugins > Run > "
                     "Spooler: Keep Slots Synced instead.")


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
        push_notice("warning", tr(AUTO_KEEP_REFUSED))

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
                return orca.ExecutionResult.success(tr(
                    "Stopped keeping the filament slots synced automatically until OrcaSlicer restarts. "
                    "Run this again to keep them synced, or turn the setting off and on to restart it."))
            return orca.ExecutionResult.success(tr("Stopped keeping the filament slots synced."))
        try:
            names = sync_for(dict(_ui_snap))
        except Exception as exc:
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))
        run = KeepRun(names, time.monotonic())
        with _keep_lock:
            if _keep["run"] is not None:  # another run started while this one synced
                return orca.ExecutionResult.success(tr("Keep Slots Synced is already running."))
            _keep["run"] = run
        try:
            while run.live():
                if run.step() and run.live():
                    await asyncio.sleep(MOON_POLL)
        finally:
            run.end()
        return orca.ExecutionResult.success(tr("Stopped keeping the filament slots synced."))

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
UI_PAGE_SHA256 = "287a0e7b34731cb6f9657114225ccc2ef86d02f293edb1cf2785abdc1248b828"
UI_PAGE_BYTES = 1287724
UI_PAGE_Z64 = (
    "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"
    "+MFmflxOiO7qIG2GuU2fIJdMU+tvcym62I7v2PGithen3IiijvlDQd2fBVLl6M1iYiz3GXN04YcTPVurNiVdXRwEWmUq8+NK2m+W"
    "hx63WhVWRLYk0qvCNkvQuZZ8NPo188hXOvMuCXaTA74kzatUr0JkplhqpReZTkPdyyKrTXu7847PbXnmsOQ39Dp9SIvjONPqKSts"
    "LiT33XSqNsCVbU/IVY+YXFV7QJBNUsdF8lLu4Lu0WFLaVJ1a1vnLYCHnershKTYBQTGzsW5t6hssfpzi5nxbS/HdQvFIbyoiv1gw"
    "reWhdlgP+2rmdM7UyptkqVVl23qHKWX3qyXYZi9y2RQ5vyST1d1IXDbpXamEpaec0FSBSjpsSEQnSVbAGrGqG4tjppVexy8i11+s"
    "L8XMZLRstvGF0Gy2j5pRNsl9XclNjNG6d+qc+IWmjdnpeHDa7fK1DV+6lLVqjskw42GtOcbTrQpO7yRlsZqMiuPNapTaNes9sbre"
    "LZLx4b7bIDSFZ9QtuS/r8W633RXAWrTj463TCGNqueZ6317V19tWhRv1q8futo2fhzy/yxOVw6pOTvq80Govze28NtCP/Hh3nLcM"
    "9UxPj0SmwydH5Ck5Ki/rl6GS5TL4Zj/ZgsUK67Sz/GbSZ3CsZZB9zewz+dQgWRooxCVTqrcwYa3KJ7A87npxWq5lm80pfikfFJka"
    "Fjus2uKVyqCI6QNzK57iA5LKJ6fTRm+6Ku7OlUq2z5ZA1+qk3OeqBqec8e05ri25xWXE7uj0uSLQ21ZOkYjjccyeytpaUOWzol3k"
    "zkA6SMPKpXiizVqLl2lqUZJYOTfqDua59bpKLSeiuZtW5ubmdGhfRK1ssnP+UjhuVHKbneYnx9GkuiuDRak+pIi+2Nz16uVS0egs"
    "D6tdPnXa7XGNlLvMOtnZpM1WpVdInkwjrS31vFni69PLopRl61Kz1OpKC1LpHsh0J5Nd5JWNxiYLYg3sz/OjRr5LH7U8rnG0mcQr"
    "zEZb82u9064dOwOwvwDjuzQxSSixLZncrle8eV7h5Wm+Cs1Jl2x6YbQmulhsSz3hLMoZeUnG2WXh0JqMqw1tIqzZIgFmw3RF6hch"
    "Ke6o1iIO9me80KPxUUamVBYvrA+HzaqXOs/HRzwZV1dSLdNp5uhKvtZpjCS9WMoPymbuNDwf9lKHEkq5ema+l9q9thKngfrVyK82"
    "PXXCmcvKpH2cqOqwu97h+X0em3YL50xjP603d6NjthSniA7YJfDjpbJcG22DzIJ9S63bW8aBuiWu5XZt2xLpdGeq44e6vK43CJHc"
    "roYrvVTEhqXaentUpPWloheWVI/YUK3ladgcmj1mUINByPNLom8UV8YhuQILJl3Id4XakCuUt6M2yfVX9cNioMyZ/uI02C6LArUg"
    "jZY+3B3K1JFrNfvrQa+xPEmTdVtp8LVuySR4adjAabydLkpquVM8b8VVhZpWylN+s2Wn8fRIZ7fpdWc+WRVlrlrJ54fLS2lT72YW"
    "0wwxr2kNYzRsbuvDpcxio8ayUc5o2g4zT8XyCq8OuClFMpWBTib1Ybp9FJfStMepeH6xNeVBFduU2+UUd6GBQJ6nwII53e3Xu2Zt"
    "esZPUvl8Gp3EwmVXOE7SB14d0s1iA0+XC8all2WLtZqK9djNFGN3xdIouzzpZ6OF8/Kyl8LnaqrD9+NDQZ+m03tcoTK0DnaO7aI4"
    "3mGjVkNkmkLluO3TnaZQyjTP/d1oN+4dKY3S81mgXRvjSQ3oeIa6Fmq5xVY65GVOyMSbp1J5MmIqy/mZ3Jy5/tasSC1ukM9VJ1pV"
    "nAN9uVI8avU2J/ZqZKWjd08HjeiW1JRcNrvl3XpUkPelFrlTtpNu71zjVGM4Geu9TWuL0fs1qed3GXkz6Vx0ajk8XUqlzULYpNTU"
    "TmziDUUctpoYJjcGk1yfUU2s19qxUjJ3SJeNFBCqhTa9XhaHjWO1lRHj00H+ZDT46nnTGDKNfHmhFjryqSrUy1lS747NbGFFqsVp"
    "Ri7nj3NVPMcHZ6m0wYziMVsxFvpWX2YkptpKtnbL/rxEN6ttDlekZfcsK0xmYu6kS5dLDcZbSd7oy0WvVtTz7ZbW3dcoihap4f7U"
    "ANvZZaHS0uebMy23CO2yWKv1Zq6pMpvSzigLnew5RVWWTH43Zgan6YEQd9V1+sjTuEYwdI/EqtRwuRLrtSqWHWELelU6n/dnOT1l"
    "ymlm2lhVd002VzI2F31Z6E8lmtqKZG3cyqnbWk0CQr7ZvtQLeHk/SW2kMpmZCvnKdESx3R55wiaTrNraC2S7Rvfrrf2kP4LmYUrp"
    "zGWm2VhS2tKoK7Vm19jRNWpUH4/E0vRE9Ke93GTCs5czwbTP8WSmlNbJVKEpTcf9Ir0p5jbSutDriHE5L+daGFh9j83G9NyrLSst"
    "sB3Xim1MkdSTtsRKnX6+UqTL81atP21WNqdpwRwmRbMeXxN7ui7i00uRk2iebR2483CSwWUpgxOVVI3cTIhsfbToJVfrXm0qXcCG"
    "f5+H9vGGasznSrpCqdTqQPWOmdyyManRqT6rYcvKrteQ5eQhWxth5Y00nlBj6UyJI5klU9VqX6+Uh4NJcTg/92vFS6bf1qf1tXZc"
    "GskG1lkx6UxjKzFFipqrTRVbdTbGGQi0Ua2qYPUiWO/rOCcxBhhsfn9stsRLvc7OC3JfILX5pChhaeo8IpdytjcpkJPN8ojl+vxO"
    "PG0ForRWzst4tUhvm+NRM42X4sxSHW27lMRhdUrBWmTh3BQGkx1Xna74PkHjPI6fqQmWHWz7CxUowOnusRXXmEymtz+vhwtyWE/N"
    "j5NNWgN6fieeM/bsOpcenJUqjvX5g7Zb7gSG2PXnLL7Jb4qtwl5li3hmxXRG1GTCMpm1lK2alyZTBwpTJrOog8m0b6xMHBezFz6V"
    "nmo59pSeJMurtHjZqdNdtTovV/kTUehL+fSC7YwGTHFwYtSOWKyvcsPMLsm2GhmjbIzEZpbNU/F8jRtkCXmj9hiOaDWY9I7PDqVN"
    "QRjVSsxm01xcpDHfxob1ltyjcq1Lvs4DtazHSKdiXSZM5txu0C0lP1Z4tjFZ9AdSTTrtmrnqyaBaW1JMcb39qc1cprvLONPE621t"
    "lW/rZea4L7Xb7WK/R2S6p02dZjr7FUkXlQ7Bbht6IVUvd2qqsi5I8fqCIpYZNlkyJ+POZS0vzEW8UO1y/GJ/qK3J+gnXMo3NkMyn"
    "+XqZ1EUFX67bOlAucFIdMUtCTktTYdmZtAU5zpTyxJxQSvnjoKpf+H6Pbh9lfs2cMy0+bWbi/WxRvZwy0qKwW00G+w1xBst1u9ts"
    "ceq0p85T2rS56AziUxNooe19ba8V6gOgp/WXW4a9GK3SsCjp+8tlYbbivUWyP5EOTGeY6SnJ/WI60o+ssTjtV5WqaXDtzfSo7HvU"
    "qZhqDHqLHD0hBJXr5JK5Ym1hnla0kdIyZoNmwB6Z3k7iZ4xhcwVukOaZxUIrTJKF1Tq5z8Wz8W1XrZtMUeMObPWw7uX4HdgBLPL4"
    "gb00yg1ZVCq5eL8fX2ynmemkddAwptdKVZVClu80VxLQr4Y66EAhT1ZZiiUmuVx7dWT4c7l4mRKpLVMraGnVaHQ1arkyMpVin1GU"
    "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"
    "X9D2XPsGzpc+n8vXZ7biM5zxtzk+0A5/ntOzNoDvynfUQ2/0z9qEvjwz+qJd8ItMiDf6F5mJr9r6KtOv1uRHitEi3Yg1z4rhs18p"
    "xqX6M7W4o+97SvFv/7xSdOxvT//Xh/XPp+qXyg7vGdzK5sPfH1X3P17cVpk9//ohyPzpb2/VD4/inlc9b3/94K5P6jefG5O+7eJg"
    "/uWRKrno/khw5/XL2NjVrx/u/35ucGw3vSdsLLxfP3jdT//zbUafPrf8z58/07t3+X5N+qh8T1WtW+49/fxXdC/V7ymdh2P2S2N7"
    "cd/+YQqPxk/Pje97hfcH+ZJ2rXql+P3/+oN8XyXz3ybnf3rGv6xOUvN+3rndrCS/xEUWF/4v/n3h7L4r/5zRSvpdNo9B/ozR+s3/"
    "+MfqYg3+v1G9xiffqg7i5pv1VeMP76a3qnN7B1pVxl9K+G3ZXmb+/+Xq9e0Kxedw6NcP933hc1M5+E2wOmK/fnj2iN9hvWzjuw/4"
    "64fGz+wuHvy/ol2FPXxyHrHsdxTtGfu/rrvVlxP5pgK+4/YHXczXVX7eEL/f6dH+vtPLxvn9Hs8E77sEq1R/Gf+s353q0/jtzvfM"
    "xX/W9U7zvuMathcv8n+r+1LyXzH83OGT1zf2/cv//PnjF30fIvzHu5V990DkP9ndKadf2shenbG/0vcvWtD3MPueMX0z1tu/fWUd"
    "3qq+Zw1+fWQ6/2WI23iNYL9jG/6U6G4p/pToYTf+lOpuRb4kemdTPkv4hyi7J/G9R8Kfnmnfi+plif9a9xel+mtD3YPov0j7Bw1/"
    "BV4ZBKu/8tcm90z7o/3nsb5F2f306XPy6Z9fK74ke7GZ9/bobii/u3x/YPc98sc6/mXqB8r+MvUDbt+mfg+Wv2K6H53+EU/pD32/"
    "WMzvLcP3Bf6PTvi13z8557fufzrtF3f8/Y7+Tc/xmezT4ykb/3589Ud8/2Bn+Vb/f3SL+S6P93vN95am/X/pUf7jfmHS3bPHV313"
    "r358ud++fOHZTd/e8JM+rz515fODPnp+Wmm/3Py/NeKz7npx81PTZT9/T1t/0P7Qzx+0PzTytf3dkzx2vqBs8tW3Kju7838Cia3n"
    "h29zffrb6wnch4K9h2n/+r+de253IPKzym/aD798uB9clsG//u31fI797bnmgzbnTpn99tvTK4un//E/vmj6tC7Z42JkpWkfNU//"
    "/nbg57+d+L308X//9RuN/lc8vxzOX7F+v3no3ccovz3TrPX/8vr9U7U+eHln8e+vc/j1bcCPj2f+/U0EzVr82K3h6MvoP3W/xewa"
    "kP4crxP597NzP0395PnBulfITbnKp5sfHf4+2Fm/2vqPftHnz6fkv/7L9uM6tyAO+7fyuIbKL99///lX/z+6//xt7fJ5+PixAvej"
    "1O43+z6Vp/Zxovz082fhr7N5J83u127z9PSZw6NX9/Pf4+Cnx6P9y29P5WPWT//n//yL//OrTB8JxYu/rVRfyPb/fupXmf5U/Ob/"
    "x4vwulJu4jy+++T/uTL77fk64HmOzW+rr2xn2WPEvz2P2Lwb8XW05m9d1Kw+2f32k22asvnp6X//73eMP+RrVPHhhdj+UL3VP4T6"
    "6enn398W4/7kzxL59+ez9pfbj5/vq3ifU8n+8c75TUueXk7aO/b5lvN+W/bW+AX2npfgruLPB+wfV5F8Sv35ZRn+4+n9wUO1+qt5"
    "tYYYRff0cUXQ3//1vWa+nPT/66//0n2K7HbX+Hb6CMnan37+/eN7Rr/829+L358+/pHs5/+8Xws9R1xP34hLn15btUcM+vTdGPiN"
    "kF23uKfvRLj346CHo/gHXfzisZ9t2tPH+9O++gD/+utnkb2c3Xx6bfv9P39/Zvw4A/ojp1/itf7p47P7+SdD34n+sZHvPf448L32"
    "ZdxnN/tPxr0T/WPj3nv8cdx77cu4z577n4x7J/rHxr33+OO499pXOd933q+kca96bvmmMjzevPjbN9dj7fI8v+84Wffp3ivEuEh/"
    "AVc1fvYV7jN98R2+guNz5ToZVy1H2W/klZpZx78ftH9J2lSrVF5a7vTCukXr5ffp75v/t+n5+36u33Hw9E1v4el+9tiybwfyRZj5"
    "v3hlv8r8l8dd5Fcn839sfwruC/Aswfut1HPl3ZFcP+5gjMu+/e84pidejojRT+T9YoYmXi5k0E/Y4+KGfD5F/1y8n0STb+TPJ9Xw"
    "B+wT9Oj2XMbXMr52A9/o8U/b+0WOiH1Cse399H4rvjaB0J0X8cYKhO+88DdWaxl/Psh/oUfuvB43P2s1dC/DbxcD96uqRxn88Ppk"
    "L/Qi8jzl14sGGnl5pNcrL+TtEZ/5vNK/HKKLX0nKktaJ3Sf+Jot1oLsQ3mS1lvH3sgPRx0Q+06PPE32V3XMZepPdK/2r7FZBbbHt"
    "Q3avTa+ye2X1KrtXVq+ye6N/kd3r1F5l9zx1/E12r4/2KruX+7c32b1dP26/vK97uy58oX+V3Vei+tHFw9yOTpE+Xzy47y8e7krF"
    "PHRKfGjPdy8g/qh937uJaNl/+iYi+7Y1aO7K+CNz8ELwbA9Wu+r6/v3i7rX6eZ95Wv320W68/w6D8Ax76A2l6AOd0AuK7+hdkQMT"
    "b2XsgU78lf5FrYnXpX9R6883yc9l7A065Ocr3seN8iu/V6iiXyL1dTqvSH2d7is58jKtV+S/Kz+U843+WXNE/BMJk8hDqV6bXvTt"
    "jRX28sSfy89T+EpSq0F4Qf2bgr9cer+K6vVS/F0ZfWcQ3rT6VXSvWv2mVa9a/ap1r1r9IrpXfm9a/nrpj7z1e34p4FXLX7X6lf6h"
    "xcRnq/G5/JDdG/2L7NZ6BCbRh0F6aXqV3WvXV9l9Lr8s35ei+pFBaAg/75/tQf9te6A+K89fMggvivY9i5D98xbB+8oifN8UfKXs"
    "f7QC/43qj3/CwffqT3zagp/VH7nvqsRn9b+XceK9+q/YgIg3DK+Ygj6h+NuLJA+9e5TfMPxC/4rhV36vmHwd7/Mu/zyf1/LrfF/p"
    "8U8I9F7/35UfGH6jf2AYvwMXI8g71sXXplcMv3Z9xfDn8jOGvxLVjzAc1nY3zc8gDr4G8V+C75/g1vvncVt9hdvvOrRfOq1f+7L/"
    "nU7s3dCB7w3vagjBLw0vSbw3vC+ge6N/AeWbdXorv1ivF/pnZNzfo4DBLfoAzRt+n/H0xurNZn4u41/g/bONfkztzUa/TP1d+fFo"
    "r57YG35fPLE3fL/o02v5Vd9e6V/0UfxKVD8CLVYGDeI8gzb/GrR/xQf7sfNV/fOQjd4ge/+pgPz5lOePvxboys7OVN8tG+877yc/"
    "v7b6/cbnM5Hvtb7Gttr9cPybROgz/5dQ9s/fqe78vMrs7pXbfzyfPX58PvX6/NuCp/19XvLL8B/kVf0+F16+tB9Oq0TeqkX7XQf1"
    "85xew+Wnt5j8Xqs+TvP1L2fzxSvQTz/9/R397x/K4MOzvO/F9vefn+7v8o723GpROX7/Fd3X12BL9sevwb6t84/fhA3fwEF//TBP"
    "H6Oy7U6Pxh+i5r6q9P1V1++u+7sH/yE2/klY/RCRfwnTX8Ho61eo/3Tp7gePedXfX/b9e/fFEdnn0/v7G72v49xvfzLb9X96+oLz"
    "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"
    "Lq4fLikfOacRZYlFJ30PJVjjEwu/VdE1AQmMYRR+3Pqf8xoj5qO3AawJKVCpQvzWJ3+H0xBoHv4ckeUoY+zRW6qPZ2GwlC6AqRbk"
    "xztlzqcxyEmfn9htUsXxAyB1D+YeJo5YUPTzY2n4eIucJZwnpNnWcFDJN7QQrqa1hTnOlrRfLxzn212M/ie5+9Mfi20wVM4wwXDr"
    "WdOM9j5lnzG/KCMNu10Y48n6Oq+CYkzD+7bXRfZxgCkIJI3XnEQzZepKPlrtXNgNStUOH5WVS7y07qIl+cKEXqGVQE+TiZwzTPoU"
    "3ENkamnKu5mhUJGtWhtSFNgsApYJzU3B4qkB0206F8Eqm4+RF+JtL5UckJBy4EODk+jnpA4EpcxMxhqpZKyxSMYKulomGStubUgF"
    "2rXY9Zau0hBvbpaahrzMKL7XhGAmO2tsZmeN9eysqFel5MI39pBLO7Al5xXDT0e6+elVNfPTqz+T+emVaX56+mc2Pz3/Muanp1XM"
    "Ty++rvnp6TcxP73Imp9ef0Xz02vN/PSH1fz0qsT89EeyV3n11c1Pr769+elJ4s67k8hQ3c70zubZy9kCdcmqZZWsq2UxiSHG5SUn"
    "cxt/k8nqQJRr71J+v2s30lfTPZjfz/myAuHky80EaT3VNDcJDVuZooZltRNzVEKiB5g+I8xftOajecmiNdcdMtVN9Mkd9IyObtvi"
    "Tqc9gT30BKbuJXoUUF3LvxJlrINJSHdkRG2jKzaoQEu6lTBNXaWCKfMdabaYboUoCe041qQwGnJCsYJJmUoQk0oNc5eML5Snzvwo"
    "syrvSdPYUOU8My19sfBDiCwu28LkJ+O/pWu2zJeg3CfUw9CasdESJW9QtmpWneg+iRbdjWgFxMojElsnn+hpDNY/KTvlO81O+aya"
    "lvbsz6SlPTO1tJ//zFraP7+MlvZzFS3tb19XS/v5m2hpf8tqaf/4ilraPzQt7XerlvasREv7PdHSnn11Le3Zt9fS/q5su7x+PqUp"
    "Wj13CE/pJNWGeKZZCY845CgNkwKXuPG/nE9CLT0HybNgGsU7wWRivliGl/MPGmCyg2KGbGxAOPqr/Bq05hQlBKAv9hQAaDyAZXMy"
    "XS1mweciIOgCVpQQAfQb6mRZdgKEcyToU3SD8wX6n0Kv2cuzpOSPSJdKJV9KHFdlICeTUoCqw9JMk5844TL4tK/Gd2V3y2xilDGO"
    "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"
    "wFeXY7tfFLYLZdwiR+PjJ91a1UarzIqY1rGCVD/JjdxaPa4r/V6ntFQo7kC0jh/dC7ta8Cesujjl9cmhdOiL2kmtV5u9Yr9Mjr4m"
    "A5g+MUtRueLneHUQlse1Ov8YjHCuXdhfujxYAd1SiyWX/LxQqnwcztnOMjc+zS9D/Thtt3OdwShHK1/dTIYSvkozWqXIlbAaNY4d"
    "sLrlVn2zzNeH3d66xlDL3VBQVl/vgqRUeqvDuX/5kBql7eYMlOXitHAk2qXpajVb7LCZ2i4wIpf5Ki0y+i6zFN+XF3wxpNq8KG4l"
    "vvDFNbi22lDpo4J/qfrTHui1JbWQb1GZqVJvfcgdpiEPN3yFmy6k2Vrh22o1R5+W4jHbPu+oWWMjnvvrcufUFZZ17nKs1454C9pR"
    "evR7drpYLr5qtdx6Qn1xXLlePn8xVAP0uXvEuKO+uZTfeYy9jJSLXOPaT4NeJTdbF1XsNNy968X346XKNw/lUmUPFlm9N2mXli1S"
    "JYafndqwuWFpbbkX2++73ry5oT9PzVYl1306bRhdOKqZ3uSJo6sncleldjjOK/hQXFxUpdnn2Ryxb4yI/HxUl9VqU6uBI6vU3I5X"
    "Y7YzHJM5YjBn21RruCCxvdBfnKn2KjvNnGRqpZKLgVhvUHmlWZnl1f282hsM5k8VtlKecF21q/DjwrjfWuEfemP1tRnroiLVCrne"
    "bDzM5ZjsUlfZ7WnOa+2pUiEYvJttbIf1r5NwfiK6n4Qwajc4eTihW22M642OrV610D8KhYNQ3Bzzda2QXRU71ctGHpHvfKP4nisv"
    "e5eWUplkl7XeckPkpGkZbMTFfBnfrD/a5WZDwE/D+aar9vTd01ltrxqr+WR2Gp8Gnf6Kz5T19VqVmJbYfT9L2Du3oxqqmMPo01lQ"
    "eoX+uEvv6it+NVK5Wr1JLSpAjD0vK939bFyYLeejS4GuqJPLGjvmav0PcqkNTzgYlPdDf3ualITzctmabDdZ5aJhBNWbTtfQp12u"
    "NfvVLj+p5ZkcMV+0K0Phg9lsMSACbhvlWbMtfA5z7KBx7qiMOheoymQ7z82PT3WSnY1rpzo9wUeDUpGpkGy5RONEv789f1W74yPV"
    "/aD01qZ94lebloZpBLlsdD4r2/zuKAg7kezpcqXR4IV6t7X+FLhSv9LKsoOmvK7RK5HNbb84PbutibXVcNIcZgdAaK3XVWYEerGs"
    "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"
    "7e2/GfATtkHORdgWcOPbf/4fFC3eaw=="
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
