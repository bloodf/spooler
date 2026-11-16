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
            raise RuntimeError(tr(EDITOR_NO_VERSION))
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
CALIBRATION_KEYS = frozenset(key for key, _label, _unit in CALIBRATION_FIELDS.values())
CALIBRATION_UNITS = {key: unit for key, _label, unit in CALIBRATION_FIELDS.values() if unit}


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
    asks = _asks()
    changes = asks.pop(name, None)
    if changes is None:
        post({"type": "calibration", "asks": calibration_asks()})
        return
    _save_asks(asks)
    if data.get("type") == "calibration_skip":
        settings = get_settings()
        skipped = {**(settings.get("calibration_skipped") or {}), name: _calib_mark(changes)}
        save_settings({**settings, "calibration_skipped": skipped})
        post({"type": "calibration", "asks": calibration_asks()})
        return

    def done(result: dict) -> None:
        if not result.get("ok"):
            _save_asks({**_asks(), name: changes})  # not written: still waiting for the user
        elif result.get("ok"):
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
UI_PAGE_SHA256 = "ccdb1d0afd68c000482ffaa1517b13651902f8aaff77980f3caaf4cf735b1d52"
UI_PAGE_BYTES = 1284535
UI_PAGE_Z64 = (
    "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"
    "PEQoUQpr4JmWVKot1oCsLb7DeCTf621SBay8dtP7fKjRpIZXPnrgfefs1Cv3PvO+Jm2JKd375iOvYDZqcYyutcU3c91GZDSysvjQ"
    "+15tdeiKfu8T7/NMpz3DZPvHb/0CTmC88sMJv5k2hxTtff6+932608qaiJRXPubvjKx+rH17KvPlSsxWhImTXe4gwTmzR4iLRb+w"
    "W2Ex6RYsCntgL1kUJiCNv5xPl2It6xHzfrM4wQPxB63BxPs7Qa71CW2Iwt8lwjGfhmDuEFmKItNTiTFpYVsJ7ji0ti1nxzW+EYM5"
    "zF1ni5TxLTLEWVhPXSFcwZEMd+k8Dvh/3w5IgnpIt43oROfzDDDlq7f+bIvYXx25j5tHUSZw/ZTr1saU0DX/Skztyr2HzNUEc39w"
    "/chG7NKLgM8Y2g8LNTOZ7fKXieKcuCHFe+SE5g4mhT5BD79UTy2sRTWy40Pu5fMjyKjPHYIFiRwQ7SrNQzaSWsoBAQnZIRbty/c/"
    "hJeNpQZ+ubmp4A125DgKxm++JtqTI8d5BZFPvLPA4uvu0dPwEW4zK+cj9Q4+1exZ4PbJ8n2fp4ZEQkmSeh9otJ4Y5AQYWKASmBdI"
    "brZ6+5PlOyeBdIrAH1bo1hFg8TAS4mxK9UnxcHbt6LvA9q19dNZvxQjFqI3ep8dWr99cvnOvOCzFEGhWgDLS+6oCCSiPvZJWwkDR"
    "+WHmbeWrK6jdY0GguSQ4uT3tYu/WcVhMu56mULKdrHy1yK93+ujy0PuD6sSqhFTlfjlnEOQnCu8lPlG/+6nQq/FXsItT3DmCI85j"
    "mwFm9oMAeue/gJU3YKiw5cen/1YigbNdUUczLcGkgnRSXgi01LyOwJLXmSE3Syi7hLh65K3e+zdNEcXCMPwflaCK8fIiihruvR0M"
    "A7/Fr/ve+VuocCR9Q+5p7xraGR8MW0S34GjwA9o0FLCyTVBx/fDw0PDwMImbqVfVErMaVizM9MIfNYMYPpgh7C7lJs+w5gCL4vVk"
    "rg6O49gCrRyKsbtnvxXm+uJ3q/e+/ev9Cyvf3BOO/PK3tCp+82UTV+OGVldPvdG98CPgCiwFCq1kBVRLgH7inM8oyO8jUxrVmiYP"
    "GryWVn96xy/GLDN2PQolTs6NIqc791ZvfCGzyeEcrgPVxim//xHMunv8o+7xTwFz/ZH+K9lZ8EDV561ivCmr9/5NdZBNsVur3o0z"
    "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"
    "t8CEeOTe3y+mluoch4gspsYTDQr7whsgK8jHoBr53keXZgJmmmAwaiMqpJjcvcCzISSwpUhPBqFQpjsryT0KCsn9XuJDg0kOArBQ"
    "KDulQXE1xg2wN3QOU2wek3NV064kmN68s9TejPw9lYyfzFiJifL5kuxxPJq6FTp3jL4AVe1TNlz02gvL7YM6AaJE+C9ouxOwnM/J"
    "rp4bzIKjSqWiVi7H6tyuNIznYwrRItZPQs3Fdu99NgXaoZt7RdslWvrjMzw1qgTGoHIKNuX9/eszx8NfnpOzE47GU3qN9eDtWyxK"
    "oyxd5U7AM/b78eQUY60wSxzjDjPOl+CMrofs7a1oVUEZmi6Jpt9ImBwCS4VC2tDYzwjGQea7QmYIoIF+ACBpbEkichVmwbShnSir"
    "SuzFopEBLst3uphYsvfExYaRmp+sGik1fygDfWKitqIyMI7LfWm7cJbmdUcc0Ce1BaFxE9SyJXl0pjETiGYfgxVOvnPKxktgnpTb"
    "dLnJ1rZaYRYJToJ13dWJdIlzUW+pa1XZd+Wdc7LclTmyx7IpWcNI/KO8tb8vT/jtEv/gHQm6JyP3Y5OGLoIgJnv+Ee5nvJW7SRiw"
    "LRhZ3ti/DWZlcs56ttrRcmb9XXHqMZl7g/8oyzozkpohSX6Fl1jpa6yTcACGyO0hk70SOxgJRdJzptFTR4tvQuKqaOZfo2/ASGSH"
    "AjNxt1QvM/3DRUOWNHlZSptwRmKJjQ9bbV07YZ+2rU20QAuaL/VBGWqwYPNanJJAWtzf3y0dH81lucp3JvA1Dy79KA6Hzhw+mNWc"
    "IaZji4p+/gBZVyOiqqR8hXcUTinAyEoayqom2aokBlvXNM/WxOhvWw9ficzVwnfqjEWdYRFLyFFcFo2zVtuAtTw5zItlF/MDrAOd"
    "kXMGCxoLbHUjTyz6Y8ET7HgxscWC2WKcZYvL/pRIeQF/eeCtkbGVEVP+UiP67p0GyFdjNh4B68zYyplxXEwNrRqki4JBytZiy5mb"
    "Mxvz81cuz41y01IDGWu0F4voSWrbXtuhn88PJbXw5Msjl9yAJoaIhDLz8WCSQHbyIYisW6BRigaseWF0oS5fHDdaSwYnK96FlcJr"
    "8QlwHsgdI+uF/Rmy3ht6NcDEdyHz3cwJ5CJSuNvkik0ypM8MaRM3zvtqzPXV3bJs4AQPhFZqbrGsSfh0vpIT98URb83p0x8OKoE4"
    "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"
    "m1SH19qtbAVh53u0IJ66nRrR4c2unC/0FzP6NGYKPLOu6n2DcU7M+rhymqfWuGkP+w37cF4T51aOKAoLymlZ5TmenSPD7iHXPFlD"
    "dsrVdyQ+Lq9AF+arEkZIytreD7dOXtp0UbqhNdvEAtkfho5J62i/zq7nqq2152R7tOkOrXq2sco6nc1UIurl7oTAmSPWyuNtotLq"
    "z+ZdrlFsskRxMeXkcofpD2eSky2hWpGi9gOtrBCLFX9gtTJRRzaH9Wjf7JTt7ZjkarqktzhtJeJHcqUPulplo+uLOdmtSbn0omI7"
    "i6o8z3e7k/ywtV4P9DF+PDTa8067lia7q9qBO+y22/lepeeciGMU3dxgJXqc74p5i1hs0nthsSHN3goMiCJPmkeemtvCRuZzoAmt"
    "NWtM7MJJ3Ch7tl1e7ecKpxdXi1y7KZ4XBWFW7FLj3ay7kfIig1aZeqHYPgvt0dZmcaJ8Xk+auVNzyBNVqTxr8DLTWMz3dXVTzpfb"
    "814na0t0od+adsYU1nDyWbTaQ3rr2mh9SPdkValsy2bXpEZFxci32s1zdqbsqyNVMpqFkjZcIbzRPtCrHHPqS4UNRdH5goQ41Xm1"
    "Wzv363Vxr42l6uHYW6OnjkSjhaKQ5Qvndm1e7ozVNr/IdWvT+q7c2UJmae47C2RqNccL66g07FkZG1e2Dt4mpZna387bxwVubAe2"
    "QW/SBJqmR/kqbqzySmFjcpX0dl5bzBnaGGCn3ZhZdxh6thKm/dUGI3KLgtIc1PT8pE2Lk16bEtNqf1S2nFb7gJS2u6lqN2oatzbW"
    "hdygsmFr5+ZudioW0r0F4GoNJyiV6Y/6qxk5aQEOG5zlfL47KAxr+AJpFXKjap6mjuN+Y8cy9ey4M2ueeqRizYuA/xoNeVvXC0ib"
    "oXtzekvvGh2ptmhpZnaj4as8zWSrKFcbEzS2qHZsrdebcuJGIGl0P1l3qVb9gFG7UUetnGbzyro0XrfrTLVzUPZCa8zaA5pCJ/j+"
    "qBxOWWtQnTi5/FFGxp0FWaSFEU6kVRyUt9JtjGIX5I6QOxM0vaBkNnusqMdecU2QZZ5ssLxdH3S4lT2m1yNtUEz3TAFvdQYNbaWX"
    "C/JJY0o1JV8hD+sCWDnFObev5/mjcjyyi/6u7sin6o5eL7B8b6hiY0eQUaSkFvH+pnVs1fpdEydna7G2PZ4anKQruDEmenR7WOZU"
    "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"
    "u/T6+b//+9+cd3eZXh4UT/86Un0m2//9XI8yfZt+dH6/Ca/KhCJIgrNP/sfI7OP1OODax+Lj6CsbcXxp8a/XFotXLd5bK/5a+cXo"
    "k51PP9miyIq3z//1X68Yv0nGqOLNjdh4kz/yL0J9//zu02MyziO/SuRv17322+nHu/MsnvuUsV+fOT+05Pm2016x11PO82nZo/Az"
    "7F2n4Kzi1w32p1Ek7yOnv03D78+vNx7y0V9N8jHESKvnpxFBf/7ltWbedvr/8uHfqve+Uc4Kx4guIVn59t2np9eMfvv3P9NPz09f"
    "k73743wsdI24nr8Rlz7fS6VLDPr83Rj4QciOS9zzdyLc83bQxVH8Shc/G/bVpj0/nUd79wH+8uFFZLe9m/f3sk9/fLoyvuwBfc3p"
    "t2DMf366up8/afpM9I+1fK7xdcPn3Fu7Vzf7J+2eif6xds81vm73nHtr9+q5/6TdM9E/1u65xtftnnPvcj6vvF9I45x1LfmmMlxu"
    "Xvz1m/MxVrn27ztO1rm75wwuSKPfwFGNr77Cuac33+ELOF4zx85YYtYKTiGM1MzY/nmj/XPSIh+lcis506/HJVrOvk9/Xvy/Tb86"
    "r+fyGQfP3/QWns97jyX72JBPvdj5zc7qUea/Xc4iv9iZ/7r82T1PwFWC51Opa+bZkRz/nMEYZHX5P7FNT9y2iNH35PlghiZuBzLo"
    "e+xycENed9FfkuedaPJBft2pht9g76FLtWsaH9P4WA180OPvp+eDHA57j2LT8+79lLsXgdCZF/FgBcJnXviD1ZjGrxv5N3rkzOty"
    "8jNmQ+c0/DgYOB9VXdLgm/vIbvQccu3y/aCBRm5Duh95IY8hXvnc6W+b6NwXktL5sWPnjj9kMTZ0FsJDVmMafy07EL105IUevXb0"
    "LrtrGnrI7k5/l90oqCk2vcjuXnSX3Z3VXXZ3VnfZPehvsrt37S67a9fxh+zuQ7vL7nb+9pDd4/hx+vl53eO48EZ/l90XovrRwUNf"
    "tmYaXQ8erNcHD2elYi46xV2057sHEF9r3/dOIkr2nz6JiL9tDYqzMv7IHNwIrvZgtKuW45wP7u7Z13XmefTbW6Ow/ycMwhX20AOl"
    "6AWd0A3FZ/SOyIGJRxq7oBO/09/UmrhP/U2tX06Sr2nsAR3y5Yj3cqJ853eHKvo5Uu/duSP13t07OXLr1h35r9IX5XzQXzWHw9+T"
    "MIlclOpedNO3ByvsNuKX9LULX0hqNAg31D8U/HbofRfV/VD8VRp9ZRAeWn0X3V2rH1p11+q71t21+ia6O7+Hlt8P/ZFHveulgLuW"
    "37X6Tn/RYuLFarykL7J70N9kN+YjMIleDNKt6C67e9W77F7St+n7XFQ/MggF4ST11R7U37YH4lV5fskg3BTtexYh/uctgv2FRfi+"
    "KfhC2b+2Av+D6o+/x8HX6k+8n4Iv6o+cV1XiRf3PaZx4rf4jNiDigeERU9B7FH9cJLno3SX9wPCN/o7hO787Ju/tvazy1/7c0/f+"
    "3unx9wj0Wv9fpS8YftBfMIyfgYsR5Bnr3L3ojuF71TuGX9JXDH8hqh9h2DsZVddfQex+CeJfgu9PcGv/87jNv8Dtdx3az53WL33Z"
    "/0kn9mzowNeGdzSE4OeGlyReG94b6B70N1A+rNMjfbNeN/orMs73KGBwil5A88DvFU8PVg+b+ZLGP8P7i42+dO1ho29df5W+DO3u"
    "iT3we/PEHvi+6dM9fde3O/1NH7kvRPUj0GKZWyDmFbTJl6D9FR/sx85X/s9D1n9A9vypgPCyy/P11wJVVhmx6FhZYX/nfvL12ur3"
    "C697It8rvce20nlz/JtE6JX/LZT9+Z3qykny2Kju3H6/7j0+XXe9Xr4teJ6f+yXcmn8jjOr3krj9KN9sR4k8sjnjVQXxpU/3cPn5"
    "EZOfc8XLbr78eW8+uwL9/PbPV/Sf3mTum6u8z8ny07vn813e1uhLyc/a71/RvV+DzdgfX4N9zPOPb8J6D3DQXw7m+cnPymp7Kfwh"
    "as6zSp+vun533l8N/IfY+Cdh9UNE/hKmv4DRl1eofzp1543HJK/Pl33/rD7bInvZvT/f6L23cz79iQ3Lefv8GefnpwvVq6x3ryhf"
    "NXkjfEj+NdlFVl9R/J/p3y4Zl9IJ+GH6usp5w2uswY+LxPskSN++orz8PAv4yu+1NN+9ZnEmuTd6/v1Vx2+V7jSfMRqR+HK+8vfb"
    "4cJT8RQ8GQ/5ne0d9/b5fKP/+ekwzsjlswTnvdW9vdvj53efnpz3eZW8ynn3xLw13p/n5N0TiL/75LHvr1eqP/6dvWzvNw8N+MxG"
    "/DL6v4DO/bumz+3Up7OL4GdnBHpOJch3w/atU57LtI1jcJ7+vGw3j2j6875n+eF6L/yLjcxP724AvGyuj218Ef5/sNhPT3ZQnD++"
    "aM67+UWQ56MNKZrXcu+/kPvlnOBjEbx9vpK/nK4o6du3t+m4Htd+NSHXTe93TxeR3IlGA/f+9ehfyP78y/mzr99y67fzSXH+W3n9"
    "TOQvl0MJ51793dPvt1WPf5s+VOm///ur3Y533+zOeTU9I+SbnbgWPlbOp9+fL/Wf/3j37o/LSvr0++/ZH3+8+9Q88NNf8WM+8PP1"
    "lurPQeQkQXV2Gi/bwJY/ugLO8x+vDevdWL0Y2bv1ukPivkjcBVLePze6Iy5L6Qvjz9B2BdK5+befNf7kvPvMmuWvluFXRm0Mut5e"
    "vmX4+PsfT9XH6V+r//25vflrNZm8G5WxLv23o30xnfhmVd+O1ufd0/UgsPr0wJTzBYTXsiBd78f18muUdt9Eafj2+VHhBadXsGRP"
    "fyajGxwfr2ePly4+ZbchGe9fDfCWy116+3zp9PMt71r5+dLt56e/ZOkht89K/8L5Lx+q36d//Pd/f/yGThvv73NwPoC7fTs4DuQC"
    "zm/txZ+h+Jjg9KHpT3V6Wf3tEdf3n0959eFm9L7N6emHymW/uDNZ8PbPv5+/QPv9RbvKy1l+lb0mPZ+M/O2G+dd5o3ecfojefuOU"
    "5htq+z3GozF4JZ7zr1FgF60kPlPK0Rpc/O7p86fbx1d/jAZ+CkMj1cukjKHWbabHX9fKT893aZ7v/d+EeA7JqpHvJ/Oh3t1VvaVv"
    "qPflBOTnuv2lv/+v0/XrZ7LfcPzsv1/4PFRxVKr2/PHVjf9XBuBK/9H59DNzcb4o8OD6H//x9rPaT983Jr+B7z63J5cjIqoIjKtN"
    "+I6f9O/n022nqS/3FtzAex9nlhE7742x4t9+SnGB1qupuir07RO9r8zMheTDsXttZegfWJnr7H9tZArH/fAcVvkNHa9sTnCT1A8U"
    "/3Godtb8v5wH8dtFQH8ZLdTnIvumXfi2QXoxO/+A4XjVk1eK95lK3RXppZufa9U3OvMtXZMeukZfda196Nrr4Ov/L57YZefqQ/0r"
    "rpj8L3TFLofiP/XEblT/Okfsuk/37lu9+Z4j9lL2C35Y+wCPfAUP+wDP6zD+/37wXGHj/gpsmH8hbC7b7T+FzY3qXwGb7wDmfjPk"
    "W4B5KfsFwLAPwDBXwOwegHnsAP3za7oVB1b0sppf3dvrhtWrlf3n+DlfSvsSQdUrBBkXAHxwPr5ajs/AecrS+yjoc1e+YPl6gb52"
    "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"
    "lXxFC8FqaluY4lxB+/XCSb7exRh/Grvf/lisg6FyhgqGe8+qZrR8Sz9jflFKGja7MOaT5XXeBcWcRvetr4vd8wBLEFCarDiIpqXq"
    "Sj869Vw4DArVDh+VlktkOk/REn1Riq/IiaCn6ULOmSZ9Ce4hMBUb835mKpRnq9aHZAUujYBjQXNXsHlqjek6nYtwmY3HyBvxdmAF"
    "BySgPPhQ4yD6OaEDQSgzg7HGKhhrIoKxgqyWCcaKRxsSgXYder2FryTEm5uFJiEvMoLvNQGYic6amNFZEz06K8pVFl/4yhZytgFb"
    "el/R/3ikq59erqd+evlnUj+9NNVPT//M6qfnn0f99HQd9dOLL6t+evpV1E8vsuqnV19Q/fRKUz/94VQ/vSxRP/2RnlVefnH108uv"
    "r356kprz7qQ8VNczvXVZ9nK0QJ2zalElq2pbTH2IcXvJidzG32SwOmDlWp5l97vyY3033YP1/ZwfKxBGvtxNaMupprpJSNhKFdUv"
    "q52qo1IUPcDwGVH+pjUbzEo2rZlukKleok/foGdwdN0WD9q2BA7QEpiGl8pRgHUt/kqc0Q6mLt2x4bWNptggAi3oVUIbu0oEU+o7"
    "kmwx3AphEvrxnEFhNOCEYAWL0goQY4WGuUvEF4pTZ36UUZX3pGqsr2KemZq+RNghxA6TbaHyk/7f0jRbxktQ5hMq0XdGbHR4yRuY"
    "XTeqTnyfSIvvhrQCZOUhibWTT/QwBqsflZ7yraanfLaelPbszySlPTOltJ/+zFLavz6PlPbTOlLa376slPbTV5HS/paV0v7xBaW0"
    "f2hS2u9OKe1ZiZT2eyqlPfviUtqzry+l/V3pdnn/fEpLdP3YIbyk01AbIk2rEpI45cgN0wKXePC/nI0jLTwH8bNwEic74XhsZiyi"
    "y9l7rWHSg2KEbOxAGPqr+Bq05xQFBKAv7hAAqDyAbXM8Wc6n4aeiRtAErCggAsg3NMiy6ATYzpHAT9ELzhdofwqjZivPkpLfI17W"
    "KvmDhHFZ1uR4XNqgGrBU0+QHTrgMP+6r+V26zTLr6GWM8y2ctUUpGcwjExcEi7K56hthGLtODZYbN6lB87BJBZqOTSqgXfBGHYzH"
    "m1Z5RUtq01o09E0rFQaSEEVeA/lH5eVwxelBQ5xLKi1aEj1EIDueXxkBL3JLZkNq5F5iiUTO3RK6rwB/eTtZTmhfC2QbajkaLSv+"
    "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"
    "g9rutulvnFqx8AjRAwbeiJSoKpKIQvyUDWsmtZFlyhopFdxIP/jqUxxw9a0dZJVWn1uNLDIPhZZAx2AxIZMY6gbiihgrHg7eZEY0"
    "mUh43THqBfwb/eds7jruDRvFCE84YSJ94gRKhyDU9AkCw+SP8a1hKWjE5NVrEgaHTfENHVa6qehnQJf4W1iQbBqSbEx+6TkHGjCu"
    "5Fvegw4XKWHicpxCzAJBVcqfmHYgKC35M5AK/GGidPmDZrhSGoWdGGii30SX+2r2ociXDJOOlRJIHzVaETtJb6U0myiDhgWqWUDM"
    "gWYREia6kUlghnGlbWEmKfYg1hSPE0v6HpKhv6VUEKTljy0iedjWZBFD63lIaCzU8BkTTFRCXptfLEClspinLG2enIyH8r7dXVwT"
    "ilqVXyK5rKp3F1enwlYDh/l0eJ5ko1CUoe+vshHnwpTSJS4y4RPvZ83FqJ6r7u/a25q8XLp7SwZmXbkiSdy33QfLa2v3rEiRl2z3"
    "4+W19ctVJOGcQOVPlldm52K6kzeo9+myeuoypkmnXQXVPlt+gcpq8SjN1cXbXeHmxYuXarXd3t0vVmvEuL0tA0Eg9xZtYr2s12Ik"
    "CE10V2hClvechoLQyN4qjVBpr2ksCPWX7DprGLo9H1T+eHnlA2PPmbB/sry6Brpmu6XjRHp8uKzlsJVG6kp0WMSi49oTOdzp8ibX"
    "tQH1u9q8m9WFrN+vzrvWuFz169R1carbUl2R6l50XIHarWffcY0LzbjBHG7JtPupY15GHXUZ2RpgHftG6RjIuKMj346JbTva4rqW"
    "Ua0dLFskDZI75OpVUX6PkMwjAu/EJO1iw17DoyUofSX4Ei7CaZ59B7FnPq0/kH4fSL//DqSfxfJ7zMw+rpAtIAzbmZBr0ot7n96W"
    "YNz77J0Ixr3P/yiCsb1NQUNSII/5+pTk3hfvQkk+2H0XSvJB9x0oyQd7t6MkHzy4FSX54ONbUpIPPrkDSvLBp3dBST747J0pyQef"
    "3wEl+eCLd6MkP959B0ry4+47UZIf7/2LU5JEs0l6kgiHD1TlbanKBTdZp/Ue+zNo0SDumDa5niHo8pUKG3kpimoFO13iao2WW1OC"
    "Vyl2jIbxeOjdmxkddDhzvrGDro2IyhVa3v+RoWb+FYoJ55O3PlqpuCWDsjtdIVAjsKfBzBSyNaxIHfTz6lxv4uWSVh5rBHbnrD1I"
    "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"
    "pdrJfnnKkiPz2BglpAKRIafqsJKerXtt2phNWzGDlzszbIFxq1Ty0K9nACsymnayBWJQ1ZsLvC+xK1M6JuXJZiRvNCHFHDfZ5Bgv"
    "TOWGJHRHLa6qrtOFzZZgynQCpyb0Wld3m5RBy+ud1jea9KY9knvKIAFwQLUwKFyGtWEM7OKWOLNpEbR7XOvnGGmauQqdLleG+zLW"
    "L/eYcitb2GSJZpngilwdn41jU6NBJtep9rmfUzb96pztxjqa0jVO8qbDV4vjk7xOUc1dJW1izU5XS8XEQVLolyedTidGq6lVWezI"
    "OwZcIOvTrCkVmLRp6so4e+RTG5NbVWr1mWCIMTNhnpKpESE2p/lJbmd0stRon56pOyFfTqSMVp2PYTE1VU7MV+tuDFzIxUwj00pN"
    "lLPCtNliVS+ziaMyLjb65mG7nhOZGqvMyP6KlNQ1QVQr4wG32wuZES/rczXVrizG+02qMkq1pP4uU621mtlcgW11L12xJ8+bJA/Q"
    "R6uGpw+xROIsjTMHij7Mk5cJm0yR890lLe2nqd5pzE/Y1mQsDKREjAEUXFFnOZreTqutcn7KFPJGOicXFg1jN+wofLXdxpn9JENN"
    "MeKSyY3XEr3rN5PDc3WqnLjyqdKsdUeJ6YJK1juZ9hlP0m3CTCXkNn9RzUNxkaXZ2KxX7NZOufGIqtPp5Lzca9Ur7cH5ODppAhju"
    "sTaYCTwYO5lKKr1aZ3cYKSzA+8Y51x808HpbpqkLTq1Ok3xlOkyOUwdqIoyNwbEIDlL1cKSMoiyeaoe83l6xO6bSaTM9c9cakxSg"
    "oTlSl2hsnuvWZrrQuZD7s6jWV3V5Xk/g1d5KlwaVQe3Q4pisJo47AkbgHWk8XinKxKxvZ9k9vluxi7nBE3hl1lzX60dioGQAlZZb"
    "kBjb4E7tvawQuUWnncxxNVbo9WLJskweARKdLBYTHJ+35+M6Qe7W8mBLsQ2qfexj68uok+FSfXx+yAo4edDTa7XMk+OhMRSkSqWa"
    "j4mcmS9ghcG8Xsm2Vgt9TLKAJDJMsnaSCZnPULupKh5NqQCouNUASwJgzOhCeiiIzLpdz03mTG7Gt87NKqXrDQ6r1irV7LScPUwH"
    "J05oE32cX4ETO5ZqTHG0bTZbl0O5286Ql6Fe4dJaWaOZYvNw0TrcrrwzVzViRIz1tDQj9VyzQox5vNbeNqoq1SrSeaEKKLMJ3+qu"
    "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"
    "SVvSnrTV4g6leo//eCiP7LemLWxfHzcv4jBXnF0t67bxqgyU+YNe6NlTqSy3pRtbLfbVSdFuPu8W40Ou0Bg2B4LxMKg1BWvZfuW4"
    "cUcBG1pnJ67LjCWKO0F7Gl49fI72S5GddjbMWGs3Xp/s+QenDDsvO0YSSo3P0cQe9VihuBmoizxXGTwfXlptFii77KB+sMdXIrP8"
    "eC4/1D8LV/tJ0fisNnLgfHyXX7lO/r3MfFZvuBdp9WIVPq/mj6OxMC3PC8185/ETrkGLE/ODUV+6KbR62y0Q+2fP+dL+at555Lo1"
    "plI9GOPF/G1/ZXZHDdYevu9h3rLdltl8daSONDnYq4++8TQ0rNdKqWjlmsKeaa0q0rZnbypP+qw+rQ2vxqPpuv5h1QtageWeZLXQ"
    "0Efa+qE/zk22yqBYAafaQ48xvircdvfw1JNzs9FqOs0/rua2mN9MDgeto+2Xr+anPtfLM1WpjD9ruc/H16GVMw7z/ntfeLzpDh9E"
    "6cWYbXPvQxNoDPbNbv++fm0sNKDUMh/Mp1yqlgrvu35ZNBtavTJusoWbg2F/5BlDbb+stNHqpm2VHutPz82HXnm4t7ZTc1TXKtv2"
    "WN+wlX1vZKhPXzed5+f1S7/N2+VWZ/v20OFm70KzOyw/Hl4/us+sMthPbZnjy3utuNe5Qcu0OeGrO1mWwfRspKI+2QsSO3srsf3H"
    "r027mO+tXq6Ktbp4pdfb216N63Jq/52rPnP5DvfC1Rcvg761UBb1vLJs94t7Tije2G9qRVt0VpJ9NW0VK+sB2+2wTYtdjAqjp/zk"
    "qaeWFh2jtDXE2dNS1tv6AAhD1UedfbcEu1sHe9jVg96tsrXPUvlm9MS2Xxa9XMvU6tZ0dlW3pQdmftWGKa/Wb5UaNwVnQbM+6ZuP"
    "hjr5mlef2P2qujZvyi2zJmylqy/Tei52RM3m5i3WaE9yU3B6aaP+/nNWVFcKP+9yX0/VwtVQ0PZXttp6fFopa7vzMRmW7FZhfHgx"
    "5R3Ts26WhTL0gc8P23avoqymxqhVGI62r3xrXh/Ob+bs53OurD3v9EZxYW4Xtd57pzozOGnDtrYv3YM4n8q73ON0V7I/NtVNT7V2"
    "5vNj873SeygM3z76MH1inuOKldfRfKPMtgtz8tIfMlK7/HXoymAFdKstsTCTJ+Vq7WWzz3dmxdFuchjY2892u9jpD4u88da9ueGU"
    "t+qYN7nCXJkPG9sOWN1663k5Kz0Puu+LusDN1gPFmL89KZpRe59v9r3Di9aorpZ7oCxXPstbtl39nM/H03VubLbLgirdvFWnN/b6"
    "ZqY+zQ7MdMC1ZVVdaXL5TWpIbbNh8luDeTPtqy+g11bNcqnF3Xwaz60XvSM09MFSrkmfU228MOS2+VjkdzN1m2/v19y4sVT3vcVD"
    "Z9dVZs/SYftc3zItaEd555/yn9PZ9K1eLy4+uDdJenh+2L8JXAP0ubvNSVt7eXh4knPiYWgc9LrUvuq/14rjRcXM7QbrJ7vytD08"
    "ys3NQ7X2BRbZ8/tHuzprFUx28NqpD5pLkbdmX2r7af0+aS75112zVSt2r3ZLwVa25s37x5XEP+4K60duzTCywQzU6cE0mj1ZLLJf"
    "jSFbmgyfdfOxadXBkVVtrkbzkdgZjApFtj8R21xrMC3kvpTedM+15/nPm53Ozc3CtK8+N7iS0ayNS+bX5PG9359c1cTaw4fUNbuG"
    "PCqPeq0582I35m/Lka0aWr1cfB+PBsWikJ/ZprjaTWSr/WnUWIHp5hurwfPbTtlfsd1XVhm2G5I++OBb7Zz0Pty23h/Lva1S3iiV"
    "5bb0bJXz80rn8bDUh4UnuVF5Kj7M3g8to/aRn9XfZ0u2qH0+gI24UnpglouX9kOzoTC7wWTZNd/t9dXebM8b88nHeDfa9Tu9uXzz"
    "YC8Wpia01O7TXss9SWuuYarFHL/bK8Z7uTfq8uvnuTwfmlL9uclNa0CM3c9q3a/xqDyeTYaHMl8zPw6L3LZY770UZtZgx4BBedr0"
    "VruPqrKfzVofq2XeOFg5lnv//FxAn/ZDvdl77Mof9ZJQZCfTdm2gvAjLVQ6IgKvGw7jZVl4HRbHf2HdMwZwoXO1jNSlOtlfPBXE8"
    "qu+e+Q9m2K9WhFpBfKjyDNvrrfZvj93Rluu+cHZr2d7J82XLyllsYdbovNZWpfVWUdZq4d3Wa42GrDx3W4tXRar2aq282G/qizo/"
    "V8Xi6k2y86u6Wp8PPpqDfB8Irc/PpjAEvZjVxyPdlHp7nhssxwNjl2uNG098s//Q69XXAMeb3ONGq7f3mt2rVHMGNz+8vljGYtKZ"
    "bd9vmOoVMx5J25X8Um/Kpf3HYWepszxfPWy6k2lzJlvy82hT+dKexm9Ca73KCa9Xra8D0G/nK6H6/LVgSu/zurS0cuXKsGLIQGwW"
    "Hgu1t5FUKinStrXatGviqjtsW4M9s5s3xaIyKi8XzWazMi3Mv7TR7rHUMlrjXvel0JY/Pt8b9cXh64urNx525lp5tS3jZt7k1atC"
    "rvHADZnmZMDuRGahse/1p9V7c7Z7qL3VG1OOvXkpsh1hXrK4ae/drCntL2H/tNT7BWn81douq++v1c1L2zBL08Ouenjctiqa2tJa"
    "1Qfu6kosT6vdZWXS+OwoFcPc9vIzbret1hfjarXxMmeahVZpe1gsVs/1p3lhUHtma19FcHpVGjuzpVpG88pYCxsgCT3czD5z281o"
    "0ana3Ru2uW9rk8PV41v1/bPWyX20Xw+l6mddAgtwUjnYH4dRb9PqP3K1B115qxx6dtk2OsMXsXpz07MKA2Zsj21e+8p/9PL1dWnA"
    "vgznutF94D4+mQbzoQ7NMftsNgaW2uerr4t6cdTVO7bJi5ODqpVL4/bq5mbZqCni25QxN+u2dlXMsbvNs1LiP4f6R3HXnT48yE+y"
    "NvwURkLn46VsjT4KY0GXLG37oNyshoUr5qvV+NS74/fJqrw3vnrT7aohLITiQV/k262PoWnwjdaDOHksPQnMQbeKY+tLkjitp7Ff"
    "A23JzJpsY9BdfyifleK+N+ZVJj99vNoP3x+btbk22BTA/56N962mNgsvzOi1Xd7r0mKsSTthpGwmX4P3z05ncTC6z8Ort1F/vW+a"
    "w2VRG75dKTsgAO03qjIdttTVs5nLDczO+4qtiP3qblR/UKWhXuBWX43Ny9Nq+bqYlB/7pZdDj/3sm5+DYfOxUl3aj6vctlRvb4aV"
    "g2QqYGCmHxu+Wp73K1/M8FF+41sPb536TlHtncC2i/2b8aG4nDGvr4zyLHy9L/d5efTFWyPta1r9YCulV6Un55uD9vy5d/Xa1Spv"
    "na9xbil03lTtXVcaT0phvS9qnVX39eal96QDnXX52n/bFVUJLKzSjc2ujCugqpV3Hf6t2b5Za8t3uas3lvX2sjB92XZf6/ZLieHe"
    "ujvlcfPFTpT5a6X7VpUXj6NBjutXpU/zrddWX7n62hZMtb7k6+NZ53GyfHzabXaL4eRlqG7Xiw9zbDQe9/1ne1CoVivN13q/0+zX"
    "B+OP1/crTZLAmENvaan99vw8mpu7xzr/oX48DIzK4uajengHG/Ru+NBqVSq8PVp/rA7t9X62WcwGfZupffSZifkCzkv5Q202Z4d+"
    "f/XB1eqmqVi7cm2f6w/4r2eZafX679PdR6erMLXt7DAZbUfMV85+V2bNm7fP/MNOmRj7kQh07Jb9Kk3NUk/tb1djVl60Hna55tfW"
    "+Jq9fXATfqzdSMaem5W6XAloAOagxaxrQLQFEiA/mdR4nrUaDXOiHx5msvxV4/WJ8vpaknsj5vlzaIuHpvXaWo/5Qv9qUHoGqnj5"
    "S53xI3vUZBrqjTJ87TI980d6rhlr3vr+Db349y19h94H3IryQrJuC7lcqpTL4W/oyc1bFVZX8BdBNnX45qC55fVfkrVWfI8Lbnjj"
    "u/cQpwMYv7eb13e/0CupzrOox5kGJCqiBXpO/A6+4rsw4CtfRJH3MX235o2FrN7mfp0AkQTIqgTfIiYQ+xFk1wAEP5uJoDhIAHxN"
    "lTf26bsZb4jhYkwfAgIIEQ1FVsUsGEBTtG6vWXF9B0ZwupKtLMa91jRLgs+M86ol84rMm6KAWxsibA6LNN2S14BIRVzIU1mRrf0d"
    "girhqWCuC6depv7MnP68nYpgBkXiAz+3ROM41XawzxDyVDMAjiz44kH4S5IFQVR/Ht05VDVV/D/yWtcMCxDpVbzdgkEUv09ty9LU"
    "jKzqtpUxAZEzCz3rDEaHT6NRd4c71FRiMhKbkfIZqZDRM4KSEYSMrWQ0JTOXF7Yhpo+hafSaYtjU2VMWafhQLehsFj6lCnuavc7l"
    "ODD6JA8XuVxgIPNhPJC+GFSQUeJhEpPDH6OYicB7i8dQ1tRQbU31uI+6AijgcDcs+LB5RrMtOEnXsKpqr09/TEUjc61n0RTin/hv"
    "p98b+C4v+DcoAtM4uwXAbIU34G8zih14OkNkTHsNKcz8BYDIgMF3P9O3cw3I4dmNbMqAyCMgEg7gLXym1NQUWUhR1p5TyV1YoG6I"
    "kAiGNGeGpihZzFjZqaLNVrflHGoPEKDnoKNne2eGGOsasRUqRS+wwk3z1tZ1EVBjinfBKVzblhhkmRyNDWFd0eKjaTHX6SjoYQZ0"
    "y470FriGaRmaujgGaHNaa6oWsYfDInIPv64UxDVuZRk2OFgs8Ygohg/RzhVteysqiqybsnm3lWRLREMJj4+twet3azArW1mwpNvc"
    "3akB3pIwTNEwNCMrgLGRlSMJQDfELALhNkO/wMa6Rwxxl4z68Cg7g2McZ4DqrM4D0mQVcN13LvdHmtYFTD58r9mdA/CnrpkyXNS3"
    "/BRwNRh1eu90fiEeF4Bsjw4zn77TeUGA3Ob7SiwMs+D7VQSnlyIvVPTqMTjEbk3A/dadu6MvDFm4g0U8YBTj1sV7I6uIc+A4uBwB"
    "dhkKOTTg5MSRiDAkQ9secSswXGvzFh6tonEXAM2CmVDEHZ64EDu4UGEVhz447MYRfrhlUkzKYVZB3sgCPOmoUgI688AGiv4NwBKT"
    "RBw3oOYW8CkdBpp/F4T7TrVXjD84jAPEBMF0nm1Gf2fDnfZ/OdUCBWAAASOuQb8Bl4HFa69V89YQdREIZrxtadm5bGVSYJTW/O77"
    "TOHX+neW+yOVTdHAZVLfg58LmUoO7H5p0ILJAX5O/ZmqVCqZFAYFODw5KDZTKNBAoR+gATM30mkKa8xlURGCTMakzzAUanV/Zr+O"
    "2SOpuxw6JhH3Aclj52CH9HuLFQ76L+eI+Qu+ip0Fx534M+3MMPwRRuaVZU1tbvlYRTYDNcAeQQyEbcC3udO/PFw/sGD6k47xdERG"
    "43SqoM/RmAlhg0RuibwSgRoWxeGF5eeRIigkRnO1j0AISuLwgeLz6CAMEttMm/JK1ODiwjicuMZ5tA4kEvNG1oBsEYEZF8ZhxjXO"
    "Y3YgkZjXYPMHh0EEaqc0DrdT5TxyFxaJXZHXYgRqWBSHF5afR4qgkBg1IKgtonDiwjisuMZ5vA4kHy/bYO2aZhQ/49JYnsZVstNF"
    "PFdb4LzwYd7yhhqBFhYB4SIOrVPlcrQCHAIjAjEujMOLa1yOVlbnWgRSWBSHEpYnRHjt/JzyqnD0jh1/XVjoAkPHQXSxs99GV/D2"
    "ZJ/ZIwQB9+l/5ug/rHhHSj7u5wJ7Rx5Bp9qVO0LGuf2fXC6Xv3P3NhVoCEoAzjR/R9FTMVERZhpV8I9dijhIM74CfCrLQC2kr1X/"
    "8HjTGex6eBYpVHjIknTohMLTPH3Q6PrwWb03G4U7Ag3Q2zGKrCmCCRLA7F9EfsWVYnEj5zNXSo4OqD3W91sgoUHhSUjfSlBWiqGB"
    "RJeIxgKbnBjvE1yJpPSeS+UCXQWsnTsLGe9A2Ggm8QKQAAEg8F9onqBOEvgFJl6jaE2kQEtR6ArnFApk1wpLwhAbsYDoGstpaUAk"
    "p66gNZ7CHQL6TwoNTHYt777Laso0FtNMyg8inSrk/sikkKVD5w1wlrtajiTrCRQ85mwfocjuaGQs0CbuLrPFQAMrRSOP0AGoI+VK"
    "5DHDFFYm3enMpYouzYR1x50zR7/29Fc4auTUhYzJcMjv/t0JzUdPKCYNGeHotAG+jyHPRxm0IhOLzV1fR8psBfwMfnNWmTT1ecuU"
    "UASdlpgWf4UsUSEDZiZNAXXayTJkmfvxOLMNE4wD2POyvAIUQlEIWR5dUypkU2hXxTZITEH6GNsbOOBYCcW6PjiOLHA2XGRzjABo"
    "SSIv3FvGvSUdD1l0Bt0ytMVyslSZljxb7e8sTScN8ACobmgLA0ihU97IbnjFFo/+RV0I9MrSFgtFxMMb+An4TJytgPghm9+JkfcG"
    "PB1nBY/qKvQgga7eKrxpQU5WQMeF48nbARCv3Z34DAjYDhxnYCSA7or2t9u1LAiKGDaxSxlLSBO29chiEUiLaPIwPPDTA2ZJLgQq"
    "O8A5RAcYsrxlgs1EfHSdaXZc2mBq5/uTAQ/Z3HxkoAngFW3hDBq0joWs8c7m559qgFYGgw7+nYV/HF1Oz+X+CFakrX3KEULbPf93"
    "LQL6Ut91Q5yLhpk1RMGeiUJ2rSHOxT/Tx0vcYo5jYCpKPFCRDWTo8dxed2ih4XXhd4jd8SpgRliQFWwD/QEWKLM2qVVAz3AdMPg2"
    "GHqG8KydegXog51BjG/e8jNL3pCd+fc8LRKYKwXO1y98CMiAQ7B1Ffb5NBPIa+LVOHuC/fIk6zMm07vfOWU8AgF1MzGWezyxCZLj"
    "HnBz6zfPXgyK13WwFXq7ao6+h975hEi4opAImgNSSyaXAptmiikQHwsBEz3GEjbS4+9xFvac31OABFFnXXIs9E2cpBd/vbDB3cEl"
    "C1GoGCizBeFHwgEMujomEHrxXp3PeS4V9HdwymKUzpN6EcMiHm8Q5KXgyWRuFhl5vUgfMSEsQQj6m7IwHBAqvw4d31mwPdDlVCIQ"
    "IihHllwbtQMYmiBsM5lPhVQ8Ym3laCXlUnDr8yHncn7vC9135aPs3nUggb8zft7x/eSRq9v0dhkfLLB3mc7ODH/iTqCl7i36iCFg"
    "T/6crLtkoJ8qMDTUXmV32MwfoMSV/XRNRlhcVmQprHjiN8osE0eJx6vE0psDqSWdwbJ78PMdVaO9zQXUKsQ+EQNT9K14hg0qLFyM"
    "wuINhqPm0ywKwap/wfgBRwoWhR+WYVMOigRr1wcXHZ9Hj7OhKB2vLBIilzMaYeLz5cBAVnyDxYFfFPmd4GYLClQwdgNTVfY2Cvhn"
    "yIqQp+togNGgKlZDHBBS0Ei6yZoB0rncH3eRq4o2J6nw+P62ZS+wuhNvU+SxQVu9aGvynSf/ezolUx7i1Hc0/v/9USpCl+QxeFD6"
    "vcy0jTXoUyY3JIchHE2C4sAGDXMp7DdEy5Oj9iVbDHUSCOHo868EOyYxXAXYBLcBc6Aie9XZQ/WcWYGEX/Az7z9hNwp6+qN3qxQS"
    "KtxVCD+UqUIF7jo2/OFZ4FxpJGB2w3E/zjTkPeDOdzgLeT0M9d6JkAnPWSHqtHZak6cc0Wd3O07G6deOEX4uG+ss1E+P4TVED0cM"
    "SzjiWrf2R38chzPqrnYYt1rpISnFQEgKZcslmAqtjwjK8CR6x7jriy8UZlJkmwTS5EmULBCiZIFyfiexECYSJRFp90kVILgwyS7J"
    "0GF61KZLaECay2CO8GbnxhgViH7gHxRRFIHCqs5MWwNJxHK2ehIHBsgVPXjcaR9C9VJRMWInXsfgTF1WXavBSbM8HU2wBWl/p5xZ"
    "TtcISrA04+rQt9cVMwUXCtjmZbAYVDADaOu3bEON7DFpccEBSwliqgJrAbcLLwV6lA5cwG5kTi4Do19SnlR5Zk4QK9O1Hif8RTPW"
    "yWKqmHS09lcoExurbyMJtKH30OkcA8N+Mizs4Km7efCLFrWDyXbMtUhhDOzQZ9rc34LdzzXq0UMV3fqOuzLS2nX3z8ejBVDfxxqE"
    "AyG38KfOm+YWLIi0c34Vg+eXPyrJjxQFRl4WC+U64P3WSL8I40PiGExgWKAo/DzGsgXm+ZjmqeTThVZeUNSDLU+CXoH1BD13cVxK"
    "XhIaKEMe3Fl+uaGcqhgRP+hGdSVx+JHTf4lPihTBcBtMkcPSgmzgKPNbPC4UbkbV8ZTNZUX5SdpyyV0kR1RHpuaLxX10crn7UMHX"
    "G7gXBb7kk4xbivoRqcz/qjuNLQbl3IiBdVw7nh0jEHFIPWJxSxQYnjyk2lNlzkdXYwTJ1TYmfYnw6rHIPeGbQQEEYexpipzt4wsS"
    "JhKHzzvY0VB4pzDJ4YptSj/vgyBPuj99SdzTSHCXRSBolKg61zQr2SJJcjg7iwHamGPcNMGTjH56maerJ6TpGZYEDM9k1ATRELsY"
    "Tq4Fz/RA1MkKojk7JglpJw+8EjuTwqDALmze/3n15zHZIGAAS22acf/AKt+ZaI2wUAJbhra6k2SRDJo38hCaJQEx4Bg0awJRYe5w"
    "h1dVFgjzhGfsPEuwY9pw775g60VBJ4hA5urYe1UXbDv+DSx4x4W+/0AinLsdvxHV7cHAF8iiYeR3Cu2OGIwf8aYgrgfXFS6I7R4A"
    "UoPG/hx1f7zOld3LaPjOTOhumrvjIxblE91lINzvpNExcpwBWEyyv7l7OTL2htkdKQsQBm3EgKnrgquh0fRRBzfeRqHLDIwXYF4g"
    "o/3E9DiKD/sHofShhQTWtJhiIHSPIpE3wbHrKoJ+ZjfD6zpwTebspghBucfhWe2A2pym5UVuPGz6bLv4NboWzkM4tzjQ2vCtViYA"
    "E8ac/US052gl94FO/m60W6QQR0OKxAh/l9MxffbMG5eAQYPv3+zQreeIO2fuZV8c2Qnv1Nyyd74fbg0odWqGDLUNN97kxE5EHRrF"
    "Kf9G4RtV0orC0jscyZ8A2GmV05veh5ZIglM9AAisU0UMcUyc4Y0KIEXZ1mgw/EHM52A5XBNx2vzvStzPDcARZuq0PR1zfxy9oCz0"
    "F9Q+v2fRNahflkYtzbOwEBOz2hxdw3ciIwyQkBw91W9toggBqw3yfrgFTjPTLUwJVuwFUVhDOEawOiF+uLXdHR4y/M+/vxUHAKbI"
    "LrlCEK3P/lagj//g/V7qmR1CGWGpUsRNlIWAfrLnfWIecjw7K7QYNP3Sj32EMWZ1nG6gxOIl9hTShk8c8QgPecdH2/6MQeveQKE3"
    "ngFpBO6HcRAcS1YIgK2ugDiq+qKi8fVJ6O7BMkp2AbsJFsJ3Js8J4iIT1huwq9an2CPfLRj2aJyYXDKNAuW+wbkZ8Tu/DaByAN3q"
    "SLuAm0wPcCA4DAogIFc8DBKkXEtNaNf2QcZBY6gpWJi3zA3sW4qN0mfC9Nz7oJn2FAPD6G9ZPzIUfpowAM3X5oz0Q43YibtYHqno"
    "MByloxDvD3Pt7GEJCaOktYjIHBDGpSwuw8VGjALnXu0Po/BkwpNkFVHpIkpiNDV/33P+gQbLULbC2liEo4+qpDEBJa0YpaRFcWMq"
    "TBDG72VE+Y1RChoFE3AWQk30pEydRlmFUiAYMpGKPGLoInLdMHC0ApES1wyZAQc1FMSZ5kTNnmCkBN6U3Dw4F1TIWpI8W6ngAIM2"
    "INrgEOJdkr6dsgwYq6gwWO+cdcJqiTbofDlCQyFuCJ2nKzEUY4o/O3s23MGdD7D1DCwndCSQH5earOKvJDIY9YuRJbn1UQiaqR3i"
    "vGMKQwUrYSFaF3aC8ToBZ4o3DDBcbCpPAhY0ByodEs1b4sdxzek7AmAK+jMS95/j/gh+xOb/dBAkOZ28SaeZ7BccpGOoDwG1g9KV"
    "8IDlU4W707g7KEQLRR8G7LPuZ0oGD6ckcQKOVBLXtnP6lwtAJmIIv28F7PwZKB+kKY7vkMMnLJycqMX+4YuDW+OjX4i8IS4evLRd"
    "dx8STgg336maLgFZPyJCnHogeMMObcQxHQWCYhzcy+STZILICTc6FKgHH5vw3DuBch2niRxGpDiXZW+yTGxAn4vj5OnlCE9vYCLD"
    "sraP/3+Dmb2wjbN0FXIUuhK6oYnIkNCYksPFwNGKvL5zAgCVGzO8R6DP1D0ClaDLEUfahYFkvhp6P9lcGShKfsuEvyY8uMzbbyq/"
    "SUEf2rdv0D2Wgv/3zRejEU5iFKAfQMCjBSHegl93boSJL/MR7XJG8WThOkEDo7RKtgWdizkjNj4UbPa3AsCJ0O0c5a5pUGbySSzO"
    "Dkj67vzdjRSDIptEXPeOSdPoWfEigeLoZCe2+effyoMXDzqAe67wC5qETqtAyZ8R5QmnkeHKo5b4A0WRxJASYeU4VaWFgkKXoxdP"
    "UCjnyCDXUNiya1xE6waCS5h4ylnV4F/foSXISQCVwZmeLlq6EKl7sc3x7QZz9UUsU+RLd69ecXe/IeP4pu12xiuz71km9ad/f0vo"
    "ik8S7XOho96bGdhV/42V4FbmTG3gqlkWBVEXvbtlzJxymqHhPJ1mZf8pSx4Q54+zyA3+2zdvh/9G271DwkJsrD31ZlDUAIH9cEa/"
    "4uPfA707E65Yr4FTOCqNWNzlSNQSrmSwahNoJgEdIcWyPh3FZaOThnQRsFKOrvB5GhtBs9+OmQp3hqKr5Mk+g5GQ1aMGxVNrf3vN"
    "kWWisKAoxfE6GzxNUtwlXchK9jSoqwUUyX8eJxhsMYiU6nDymYDJkc1EFVO6c7qM43THWdyFXCQOjz6nbsmdNUWzjvG6FXn/ohgM"
    "0bv73fsmv5VtI2kAI+wVZmV8h/rnMQKNP5lLQHo4AUGh2T4YiIHdWCekxTuWqeiFGExdm8XKv/9an4f53guOgz+zJg8NdOnTFSSf"
    "rEHc7COD5k7mWAJCKMQVebOzU9HaiqJ690+LvVAu+P3ASrQSw9fgPEmYfh+I6O7fcQaRPh+U3yWTumjnLXABwtHyKZ08R4jMKQ93"
    "xSQj6pgJiZuFbCHu6iPMUH2BdE4IK4G7ir8/T+F7Mt7UlcI3p6Lv7HtD5RrZNYWqHsCCdHSbH9+Yb5GJkjSFiW3KxjVlY5vm45rm"
    "Y5sW4poWyKZIqSCvXx//sakksKzhAX9+mzgb+oiAOWaH83dBUG0Ug3M+suZMSA4t4CaKEYk2dL968JBIBahNkISWyxHbfpZfo/u3"
    "cFSCl459GQcCQ4ObpchbWlGeRKorCQEBNQyeIg1E4aRHxxGyO1R4/CXBWzWehhcROe5wsgMB/YhKs4tL6Wl0nctlQHd1D76Y6zWn"
    "/ZWN219hNGqClGMnqqL2XVQePFQZJvoeP+e7ml4BSzq8m4aeI4i+2o8JwEzsZPz/gcT4070PNDX0fkXkJXC74UmPEQ5rEjk2imir"
    "n1GzHUiTSpvvU45Ofx0oDwfuq5+gkYTAnB8kMVPb3P/MkF90IFiB/pzyPoeIJNOM/k0KEag48lBuVx952NEZSVwg4+vfpM8fvROe"
    "SmzfiqLFnwT2b5LiM5D5FSC8gZBLOmKJwjaZAFy8wZzLLUNZu7QF6lsB5KA5bq+IEHv6wYMbQmfqb2SFuKNlqYiaRlk4+c7pWPG6"
    "p8v4hLM2BBjsxCpU5dRFAvA4GxlStc7cLHY3cjJa7cJ7xGFa0U4QotIfpi7xipZiY2LUA3GjEN/RFxhqaBDZdwaWpH8F60P4MMw0"
    "JNblzuYSCZkzfkG7EMAdgsW51kLXCrblrZkUETWIytJ/V8Erh/KcxHBu4BwjrW6Imn9O42PPanx4d0gVg4OL7Ar5k6KHb/gkyH96"
    "STKC01MUF9hPqAkNibEN2gYcoSNZbj76PoX6fi+vF7RkBrFGVKjfwFD0i4MBztrr8wlijh3sUTe5ZZSOQ1RON7bL0Te28+zJeeFA"
    "zTo5+miJEM+krnJVVBcSzCn5W/fZk13eNPkM+If+HkxIMzB5nBJa4s3vRBKUdDrgn3cB3uJkJP5CyJ4oCUhUuDnxgFPwaijUpFF7"
    "mAPz6CV9VnjdRFZf9McdeZH+VB3le8PJOmmXGfzZFFjf1Xns5PJlGY2/i+ghtQxs6COzG6QDSUIpWoYPBLyOCP7/mPTBE6Ip8r6B"
    "pgkCXDm3qaYIsRGBhA8a8ZYlga1rIeHGqrgNxzKaOso6nPDaceLEDC5YKpu5hfdeFutgjgVYBUwskbIYW+CI6HvWl0URNXFGFnEg"
    "zsUKkGq2BWZ4Jwp3QQSOl8nZKYruVyBVuJnE0D1N9BGwvPORYYreV3Hu1mUKZeezNv+3X60i/IiQDE1xPIj3PypOPEyQOjaXo1FH"
    "yKNoAyKVzoAX7xc5wk6i3kByPiK6wKtqwL8x3WE2wBPwNy1amJ0UIeVBpFrqCXhcGjXjDdBwI5ItT+6zEutRmMxWBmoju9PFh2ao"
    "O6IgWwmTKrGFgE06YnsIpFGMymgYm9bVsydQjcUO4ZcHp/jeRiKZyMLXvQO0k89bxmcfpHQrtCMDqtE6gVMUDpCEpWDlx1iDYicS"
    "tL33kvpGBfogxjHcG1VJjXbkzatAondzk10kzwlCGN/ok+Yb8NDZm5CzXOaB4nlopAC9aOlEnYVIzPPfdoNtoIhKy/XpP8LdmfWa"
    "V0LW3KgdlUhmSGxtW/TSnW/wYyBwOTqE8HbocEF4e/OdVDgy8toU8JsX5+fY/04hd0YCB3BlIYITwRaTi98DhTNXpWEg7W9d6ckj"
    "4GhnpKtSCYR3U0BXm2JytIaGgvAJRAZiltM+yTha+WHODz0/O4UHByz4hbRb4XfuxYOW0MqRKHUGGxF8mgjDPfG+IGYZR/SA7Kro"
    "x0CeK+czXU4UoEsuOiAPlBs2EPWiBt8ZMSDjixFjmo9kRvrdVgDNNmHmvuSe/Lj8JFSauEShv2cDAc6ftGenE3X1rF8LrujwqQqm"
    "NXJeuMCigNXPK7gAomxaGtDcE8QO5tNpsklCnUCAAwRWe8AiIqrwbQiHcyM3QDxsuO69P83ckXaAgbFf24olH2NDJQtnpgkU6fIs"
    "Ycw01Q8FIKA385KbMoDqFT8IJu053YiHcM3AE7im6IXEX5AP0YmBPBP/Sh7S4klpKjlhlyfUCe4OsPj9atBEN8SNDFRr+hMuqAra"
    "eZNnO7o7lwgKgDTFWYJnQs7uEoE1huBelNrJaQINv+jpkcAODg7wY4IYXgzHEnXi8Xk4tHLY8sXgyppu/Q2eBwDiTxY07eZvWfeC"
    "SwFCOiZ8YsWpnkJ7x1/WXoeOGgU68pxUvIRjJRz8ZK4zMD3BSe+hTVwwMu6CYwSK86S9xWP9s3u3iJ4rPv5+luPCb7AyVYollJ0Y"
    "KVY8m5Qrw1wzLGeI66TiLGbxi6RPMbsN5bBwwpNEEwUKWKIvGx7S+YJp1nUFJWyLeeAcitomjGHaK6LfJYCHA0M4Js3Bix5U8XbL"
    "6wJxv6sYvPDlVohzdJyo2EpaBlEjmscYuS3eTIPb+2K1wrmFULW/lwLsdB4YIhgeeUN5fB7jSMnHsMnPfbwGXy3wqmKLNQxb/s6L"
    "Gd4A/5tlpjPwz5ecma2mGWGTmfOZhbLKSGJmZWfWBzWjfmkZXZ1mdDNjChl7kbGNzF5Op4/Q8uGD/s8APhpujlIH8LXEb8T47Ccu"
    "m/njLGzzB2gvKr5IEPBxDYU3mCMqGrAXIYEB+9qbkmbAm0jRzU9ngdsFVRSFZC7NQjChCfa1Ol5N0tHJOulM7k5mx2LwkogOZXDX"
    "lFB0JBV3RSZZf3OvE6fF40/uAYo92yw+juCnlOspC1h4gqfm6VpY/BOMEORfmi6qPyOUMSYddEWaOlUWzP8jsiCy7qK7LAmFHTK2"
    "Gim1yM/ofEBaCDhWNlIqm2LyeFLJVKSkyKujZ9oCMh00ClmSk4gxRVBHYMkjqTOaQ+5/MEzx5AEg4J2TaUvElowulGU4xDeJqKL0"
    "HbV0UFOvfhbQ4xnYUnb0XycnhgkU+kbJb2SDg+h1PFc4ddzaavcObPMYe6uOzfh4JhHTABBXLuUO5/iMTnHycnQP/gt6kK9cV0Km"
    "QgId9jdSvGlhis4J7siA6mTLTirqbwCCpGI3IWfRBd1NVj1GOsLP+W/ymJx4GX4DPXkz6eTfixed/z9Jzfoiu4YXgi4w8ZydGAAT"
    "xokd/7m8xRBmMM2y7xUAfEMGIF5q0zTJQaiLx5CkY83QKWkeox53iE+ipdMCIKjdTRaUczqy4lBmv46kdUhf4cc1iY0PW8N9qnsw"
    "/fTp8c0V6vJlCagvvvJFC2T6B304kRYfKLSF+oodgZnwd9+LmOkzaSdBI4tiPwvPFsoBQ+UJUOy4ZulKAypH11AT6aKR4kfETW0k"
    "KzjHS4BqHUaf/k7S5bDFFcCa20o4cwXuPDaBuzEWlSJM6w3mYK0JYlY50oJcQCnoe8Lcou4Mg0b4oeGLD4kk++G/yNmxNhwYJEza"
    "tvDkga/IqJHQefJ7+eOjOd5Bfw26AhgfDX3crZf48CDQOLm/+NxYnTKlo7i88wq5S3nU4gTlFPMDm8T8UC7H5UY6a3IAmCPWFCjh"
    "zZXPwQW3XxxCEu3ETvT0WoxhHeKAT66fC3vEJxaovcCmxKO77h1Ct9I+MqMGqgC5Kilnn7EeOdBSivxbU3jJhMWpzpyjF7nclFh1"
    "duc1g8YzmBfT20T94QDX+uZf1F0TaYCAAhOGGVyi+rEn1Q8I0NYGPZ9mJu6D/wBUFPcEZCpRJyDEcdEwncuGkr8kGwrEvj0NkW+B"
    "oyJRXNEc7acX0sreM4LUVBmxXSgHVU8KbYCAY/g9Pz9YaNyNevcs+l3BfHwYB0S+yeB/0+SD2LirX/R2KGd7OD0arBtpaXVTFbjP"
    "kfzhe5cw/n57AnsteuUICgLU7AZZQwRbuel7FsT15JP3jILPbYcNvU4f72XyrRr2b1/PR8lKYm5voOTzDu5rmPXuwlQMsKkpLsiM"
    "9NH8DpdsIGjCUfUxlJR8jHlPPkS4P/c1hqIAWkKvKZ85fpx29OMn5kDxaMet8f0jGAeQ8OIAVgAhgNVlHQ/eFAvepsJALxKJ2GiP"
    "DAxbjj9iyTfCaBuFEim5oRPk0lzrRHJ16jqyLmGki5Ko4+PgGBs9V/zdgwkFDKQjt3rpGHOQ+GJiQV0pmaDuS6rm15MuDNqMeJ0c"
    "EpNYSURzRwToe9NSZE9cPcsKYFBdu0ue9b6jlUdG5UPcKFrnH3DSA1jri045qJlH4C1QH5hOEJQgKAt8+4YkRDdw+mFApPNcxiYr"
    "lCvlAiNWfp53vE+zpjE72w5NzxTGVNCr4gsP06xtKOEKWAcKvpqJ6isaGIUkVF+0pJDiQ5Hw4NEc6j7U3ygUBNN7emEn24NbneFE"
    "ppBj8+eHeXtI6eFWJEx4Y9UMV4m49Bd4ohoZCcLnqgM1JYfhXrDleq//Bm8kn+Bfa2pCFIToIFoXbA24Mgo8ovsGWbdWTLq6mHgz"
    "3BgZcbz3rfHsJBckHAhQkogP/4xmFzeww0LxS97SEk8pov5OTJPlOLycTQjPKjyAULxeBj2GQ+kUbHRtbbUonXhupMA/Xt0U5f0y"
    "qiX63KOfpze0aYKwI5mnQlm/ERmSOHNUs6RP9kTpptHWWQ/R/WnKvGPEOSFCob5OKmuvcQonGKDcknWtf7j2Akp09CeIcQV43dR/"
    "tcFhSm0RJYFJ1lrJQOdN5n94XT8GHoJHxTjk4yBlax03dQWSFL61edXQdPFbJvWtC4h9AtVS/Rr82ZZnhganMDXmX0QZfupoQP/s"
    "A0UkVXttOtW8b/h3X7ONmZh64VXiq7k3wdgB0SaTygISFcAb6Esm9QAt8m1+1ke/nwBNEIa40MTUsAFbAhhArzDkOXblS6KiBHq4"
    "kdwHQBfi/V+Gpog/gOyBXFo/yQkJ2lMAITDkI5j8GmLZq7PU6VYizh2RQQUweQAlFzYGBQUf9N4MfuhspvCm+TP9b18TdAkO3qKk"
    "uz+pPtccLbdd7tev/9z8+X83gM7/e8v8efPfG7Rp3v/nvzfomdn//BfdbUW9/PHNEV2/gc+CvEnJwo9vYFC+3f/3BvyEbZBzEbYF"
    "3Hj/n/8Ho9ASxQ=="
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
