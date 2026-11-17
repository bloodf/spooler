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
    msg = {"type": "live", "live": live_poll(), "usage": usage_state(), "printers_rev": _printers_rev["n"], "rfid": rfid_offers()}
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


# --- New RFID spools -------------------------------------------------------------------------------
# A Bambu RFID spool in an AMS slot or the external holder whose tag no Spoolman spool carries is
# offered on the Printer tab, built from the printer's own report (nothing is sent to the printer).
# Adding it stores the tag in the spool's "tag" field, the first place match_spool looks.
TAG_FIELD = "tag"
RFID_SKIP = "rfid_skip"  # settings: {printer id: [tag, ...]}, the RFID spools the user chose not to add
RFID_SKIP_MAX = 200


def tray_tag(tray: dict) -> str:
    """The tag Spooler stores for a printer tray: tray_uuid (one per spool, which both its chips
    share), else the chip's tag_uid; "" when the tray reports no RFID spool."""
    for key in ("tray_uuid", "tag_uid"):
        found = _tag_ids(tray.get(key))
        if found:
            return min(found)
    return ""


def _report_num(value: object, low: float, high: float) -> float | None:
    """A number from a printer report (Bambu sends most as text), inside (low, high]; else None."""
    if isinstance(value, bool):
        return None
    try:
        number = float(value) if isinstance(value, (int, float, str)) else None
    except ValueError:
        return None
    return number if number is not None and math.isfinite(number) and low < number <= high else None


def rfid_offer(tray: object, known: set) -> dict | None:
    """What the page offers to add for one Bambu tray, or None: an empty or non-RFID tray, a tray
    that names its spool itself, or a tag a Spoolman spool already carries."""
    # tray_uuid and tray_info_idx come only from Bambu reports; other printers' trays carry neither.
    if not isinstance(tray, dict) or not ("tray_uuid" in tray or "tray_info_idx" in tray):
        return None
    kind, tag = str(tray.get("tray_type") or "").strip(), tray_tag(tray)
    if not kind or not tag or tray.get("spool_id") not in (None, ""):
        return None
    if _tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")]) & known:
        return None
    cols = [c for c in (_hex6(x) for x in tray.get("cols") or [] if isinstance(x, str)) if c] if isinstance(tray.get("cols"), list) else []
    colour = _hex6(tray.get("tray_color"))
    remain = _report_num(tray.get("remain"), -1, 100)
    low, high = _report_num(tray.get("nozzle_temp_min"), 0, 600), _report_num(tray.get("nozzle_temp_max"), 0, 600)
    return {"tag": tag, "type": kind, "name": str(tray.get("tray_sub_brands") or kind).strip()[:64],
            "colours": cols if len(cols) > 1 else [colour] if colour else [],
            "remain": remain, "weight": _report_num(tray.get("tray_weight"), 0, MAX_GRAMS),
            "diameter": _report_num(tray.get("tray_diameter"), 0, 10),
            "nozzle": [int(low), int(high)] if low and high and low <= high else None}


def _rfid_skipped(settings: dict | None = None) -> dict:
    raw = (settings or get_settings()).get(RFID_SKIP)
    if not isinstance(raw, dict):
        return {}
    return {str(pid): [t for t in tags if isinstance(t, str)] for pid, tags in raw.items() if isinstance(tags, list)}


def rfid_skipped_count() -> int:
    return sum(len(tags) for tags in _rfid_skipped().values())


def rfid_skip(pid: object, tag: object) -> bool:
    """Stop offering this RFID spool in this printer. The newest RFID_SKIP_MAX tags per printer are kept."""
    tags = _tag_ids(tag) if isinstance(tag, str) else set()
    if not isinstance(pid, str) or not pid or len(pid) > 64 or len(tags) != 1:
        return False
    settings = get_settings()
    skipped = _rfid_skipped(settings)
    kept = [t for t in skipped.get(pid, []) if t not in tags] + sorted(tags)
    log.info("RFID spool %s in printer %s skipped", min(tags), pid)
    return save_settings({**settings, RFID_SKIP: {**skipped, pid: kept[-RFID_SKIP_MAX:]}})


def rfid_unskip() -> bool:
    """Offer every skipped RFID spool again (Settings)."""
    settings = get_settings()
    settings.pop(RFID_SKIP, None)
    return save_settings(settings)


def rfid_offers() -> list[dict]:
    """The new RFID spools in the printers Spooler reads, for the Printer tab. None until the spool
    list of the Spoolman in Settings was read after the last write, so a spool just added (whose tag
    that list doesn't hold yet) is never offered twice."""
    url = current_origin()[0]
    if source() != "spoolman" or not url or _spool_cache["url"] != url or not _spool_cache["time"]:
        return []
    known = set().union(*(spool_tags(s) for s in _spool_cache["spools"]))
    skipped, out, seen = _rfid_skipped(), [], set()
    with _live_lock:
        for pid, state in _live["printers"].items():
            trays = [(unit, slot, tray) for unit, slots in sorted(state["units"].items()) for slot, tray in sorted(slots.items())]
            trays += [("ext", 0, state["ext"])] if state["ext"] else []
            for unit, slot, tray in trays:
                offer = rfid_offer(tray, known)
                if offer and offer["tag"] not in seen and offer["tag"] not in skipped.get(pid, []):
                    seen.add(offer["tag"])
                    out.append({**offer, "printer": pid, "unit": unit, "slot": slot})
    return out


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


def _rfid_tag_extra(value: object, spool_fields: list) -> dict | str:
    """{"tag": <JSON text>} for a new spool's RFID tag, or why it can't be stored. Spoolman takes
    only extra fields it knows, so a missing text field "tag" is added first; a spool that already
    carries the tag stops it, as two would leave the tray matching neither."""
    tags = _tag_ids(value) if isinstance(value, str) else set()
    if len(tags) != 1:
        return tr(EDITOR_INVALID, field=TAG_FIELD)
    tag = min(tags)
    holder = next((s for s in spoolman_call("GET", "spool") or [] if isinstance(s, dict) and tag in spool_tags(s)), None)
    if holder is not None:
        return tr("Spool #{id} already carries this RFID tag; nothing was written.", id=holder.get("id", "?"))
    field = next((f for f in spool_fields if f.get("key") == TAG_FIELD), None)
    if field is None:
        spoolman_call("POST", f"field/spool/{TAG_FIELD}", {"name": "RFID tag", "field_type": "text", "order": 101})
        log.info("Added the %s field to Spoolman", TAG_FIELD)
    elif field.get("field_type") != "text":
        return tr("Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.")
    return {TAG_FIELD: json.dumps(tag)}


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
    if data.get("tag") is not None:  # a new RFID spool from the Printer tab
        tag = _rfid_tag_extra(data["tag"], fields["spool"])
        if isinstance(tag, str):
            return no(tag)
        spool["extra"] = {**(spool.get("extra") or {}), **tag}
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
    "Spool #{id} already carries this RFID tag; nothing was written.": (
        "A bobina #{id} já tem esta etiqueta RFID; nada foi gravado.",
        "El carrete #{id} ya tiene esta etiqueta RFID; no se escribió nada.",
        "Spule #{id} trägt dieses RFID-Tag bereits; es wurde nichts geschrieben.",
        "料盘 #{id} 已带有此 RFID 标签；未写入任何内容。",
    ),
    "Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.": (
        "O campo \"tag\" das bobinas no Spoolman não é um campo de texto, então a etiqueta RFID não pode ser guardada; nada foi gravado.",
        "El campo \"tag\" de los carretes en Spoolman no es un campo de texto, así que la etiqueta RFID no se puede guardar; no se escribió nada.",
        "Das Spulenfeld \"tag\" in Spoolman ist kein Textfeld, daher kann das RFID-Tag nicht gespeichert werden; es wurde nichts geschrieben.",
        "Spoolman 的料盘字段“tag”不是文本字段，无法保存 RFID 标签；未写入任何内容。",
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
        "rfid_skipped": rfid_skipped_count(),
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
        elif msg_type == "rfid_unskip":
            rfid_unskip()
            if self._settings_window is not None:
                self._settings_window.post({"type": "rfid_skipped", "count": rfid_skipped_count()})
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
        elif msg_type == "rfid_skip":
            rfid_skip(data.get("printer"), data.get("tag"))
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
                elif msg_type == "rfid_skip":
                    rfid_skip(data.get("printer"), data.get("tag"))
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
                "rfid_skipped": rfid_skipped_count(),
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
            elif msg_type == "rfid_unskip":
                rfid_unskip()
                self._settings_window.post({"type": "rfid_skipped", "count": rfid_skipped_count()})
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
UI_PAGE_SHA256 = "6a29c9c65f0a05facb13f4e65afc82e7f160bdd21193de680125903f03379d3a"
UI_PAGE_BYTES = 1296195
UI_PAGE_Z64 = (
    "eNq0vXtz20ayB/r/+RRmrosHWI8Yycnm5ICGUbZsJ87DTizHcaLVISFyKMEmAQYA9QjJ73771z0vkHI2e6tulS0CM4N59vR09/Tj"
    "UW9aTdrbpb532S7mj//rEX7uzfPyIv1Ml58hQedT+lnoNr83uczrRrfpZ6t2dvD1Zza5zBc6/eyq0NfLqm4/uzepylaXVOy6mLaX"
    "6VRfFRN9wC/qXlEWbZHPD5pJPtfpESppi3auH58sq2qu60efy+t/PWomdbFs76F36Wf5cjkvJnlbVOXnH5qq/OxeMU0/a+Sbg/Oq"
    "aj97PBo9ff367Wj06HP59PF/3bvXrWVRTVdz/dnj2aqcoKp7OtLxeq4pP319/kFP2sGk1nmro3I1n8fDWVVHyC3vVbN7etBQH9po"
    "rMZx3J6WZ+nRsNbtqqZq0seaRnav3V7lNdW13qoyPT1TdRrF6WN6K/ihd6TyFGUHmMnjaqqftNFhnKbp0dFRv99JPpLkw34/6qQ/"
    "jB8fPXy42ewkPvrf/4lVJZU3bV63za9FexmNq/KX5ZQGlIxj1dgx5k1TXJRqkkZateggjzHVg6Kc6pvXs6iNh+XjA+4Sxjyh+VBH"
    "8VbNbQ3LumorzOngMm9eX5c/1dVS1+2tWtk65wNa4Dm/qGn6pK7z20HR8K+aoZ83NPU0xPFpxVXe+zFfno3V8q6sE91S1uKurGc0"
    "Nsq7RB76g3WibLvAY3Wxk9O0dVFejNVoN/12cV7Nx+pqJ13aGff7vZ5Wt8iMrqgPm80l/Y37ffoZtJe6NI8EopPLWJ3vT1RbnXDT"
    "6gaVnJvpidWJHdag4Zn+Wh0cxer4rsFKnTRcrZF9Qdm0RD0q8Sp/RV3Up4dneDug5/H4wRK79WXZ0iIcMZTRYtCHBMAf9a2q9Qz/"
    "RwTj/Iu0qnxXEkQ91ZSof6xWZWuT+EVPuyUEtGyavO0WKRdhNeZVTwkcSx7EX+w+2VxRSetBu22ziXjTUW4cEyzWOv384F/Xn1+o"
    "67SkfQzIr/VyntMc1lrJTuAZPYpp8n9ZEoAe542O6GtV0Mf/ehqdPjn4/SymKnK9V0eh1fjg/tEYH/9QXbuPVeXLYgvyFu428MC3"
    "TLvOFc9oN95fV8A523EypimYaLtdemYCika2zJxzBoMB70+Hh9LDYflID+a6vGgvh+WDB7GmOYm43FatpDpVEuLpHeFDU+tUz4pS"
    "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"
    "Rqu2L5qdWq/b6bba+2Mxqu/3eq1Wt9Wqi06tsd+rdxttSG7WWr1mo9nq1kWz12m19lvNXg/Tew1gj3vtbhNIYLfZ6LXbLWym16n3"
    "9rvQhYAegCDut7oNbL1d2+91a71eUzRr7eZ+s9XoYPNAUZswnG4LKGmvCYOpt7vYfGO/W+t2mo0GdNvptGCg7U4Nu+00Ws39em2/"
    "JhrdZmt/v9nstTC9Xmv39lu1uoDptXq9TruF3XZq3Uaj3ejuizpMolOHNrF0HXrf38eBima7V8M5Uiv1HpzK3f0m0PVWrbNf32/A"
    "SHE0MBFIb9SQ8Neb0FCdkjt1GAGMpik6zeZ+rdmsd3EsjdY+kP82jBHg1uvC5DoIGmir3ezVcJANYPY79SZDvlWD0nB+dFsCVwAW"
    "qEkg6LSgOnQrAPz1RqfR7TZpSq19mEYDkmuQCWvQxORutwYHZ2+/KeqtXrvXq/VqdZwRnEUA+zqcRvX9NrRYbzTbtB7tNq4PnGYw"
    "6Hajvg8AIgj0OjUA4D6caACfHhRq4pyg7VajUdvfh/K9Xq9bh155naBqEwbaE91Op4sr0MHkXrsBLe0DkjXacM/ptfZpWZuANM16"
    "s4PY1AB4NbuwrpgOMG13AQVh/WrNVqsNs6H09n6rDbhAZ2+nA83IaQGIGh3Cpm57v9no8DrBIjRa0EobTlao1O01sREAdRPwoAap"
    "dVitLgysRRBr4iDrAJk2IBj02SQcaPRaXfjuYnqjsV8DvCaIAfoDQjR6uHqAg9gX9gkwbAMIurUarhM02YU1Jkju4xrX2jileguX"
    "d79GuIRLBTgPxz8gVLfdqxOqwk7oIJIDqwEAqHVhiQnwXcDO/TbsNijeq+13mi3aCAB4wFuYLUCyjlBqNQg9mo12D6oAXgBqw55o"
    "wz4jpARkA+TvdnE4HRhErUY42a7DercBKkgNOpAIndM+q9VgLvs14G5azQbQAhgQ4WoP2qkDekF6pwuL2aad0+jCAKCPlthvww7s"
    "AbixNIwQ0bYFY4SmgY1q41TbNVzJTr0DuxL2OPTeQwgDmsAI2sBMQTnYfoDOOCPY44Bw+10YYXcfpgTECdvuQbUm0B+YfxPgX+u2"
    "CF6Axg3cfcCdAZ2AgTdbNVqmNi4RALyJ+6YJSNajTuvdFrTd7HZ7CACAaWef6BsMCUaCGxPQoIsbCjYRThRhDitSR2zCHdfoNRCQ"
    "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"
    "gnx3K8bqPmTGMfoezJfJWaJo0nRymSjSNcbeWAz0s78MHNEzidMaLo1d53PJpRNw4Vr+5ruxJ/MKcCpo2CQtrCikcRcPlgcwuGGm"
    "vM5qOCq4KbD3AH6GU6BpLyZ/tCXT/ihEh9ql16es+nglevgOuYP5eotpZJ8sz69IOgdGpkc4l1VeXBj6p/qT83+HWiYM+I/TKWJO"
    "eufe6d88QZn/uEFydveO/nXtwlX/u8/D23twf+Xtz3xLrSUBQ6sP3up98Bff4ANa+lc/7V38snfq49X79zWJIYFQ9ODKpWur1y77"
    "H9tJh7w8146fXb3+tv9d9LHLDz7sXX3X/yzlOndgyXL81sUrKx99tvbWe6vXr2MudozuTICRJd0YMgYrX7zRO3lWmmbowmpT78Sx"
    "tTc+8q1stdewcAxcdnnBl5dO9S5/FYWNc/gytBmg/+6XAUAaHzQcIRNc+F7vzF1pzNR5pf/OeysfvCu/eoNp/+SbvbM3+hcdvBh/"
    "VpY+Wr12SX8UMRqP49qPK/evye8u5zPu68XF1c9f7v/1y/6r56SZ8r/7rvipe4tugIyy0HtJEBCm//J130DV4sfaQFJfwuFp6/92"
    "730PIEfkQFaW3uz/5SKfVACYtkbSjNX/8zFVVVpwe3XxS4wgw9M7drT/3aX+xZO9N8/27r71t3sfrF6/1Tt6ov/pYv+jzxw9/tu9"
    "M71jZxmJ/vfiK/4jkmAKE/O73e6duLB66cvejfdhUmuLL6/++COiAM2g4gU2weNzrwNI78QN9ylJdYGOg+4UTb4Z7ta/etnyLsBo"
    "rz44v3rpDGyATSn2v2Hoa0dW3n+1d+uz3tFbvcvfLy991jt3iue5fPs19zvCHP3r6stvrR25j7tjv/jx8ZWrP65d+gG+Avuw9sqn"
    "a8fPLN/5aPne+/13f1y5fHf1wXvLS/d7d9+Eq8SbQ7P32FaYvpssbvbgr/Vf+6J34maYJK135yZPNLcw+DBsiuvNM3PcyOr1JSBO"
    "sM3Y5djR3rU7ZqIgSqoqZPn23eWlxeU7JwAjlm9fXr59xY34t3sfmQ5bW9W5kBWC7YDe/evnsNO5N5aXbkKntQ8/6Z34oLd0d/n2"
    "YjjYGVjI8u23lm+f7R19efXabeny/vnVC+csWP/kIp3ZFbhmMKPVxaN4Quevr7z1JbQ6hH7jjN3E3o1v++9ezy0AVox7baYMm8Gf"
    "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"
    "3GvuGSGSPMaKWhQI1XSrulnlhvVTuRnng9NB6qzVufJlWx926qniUk63xXN5USsmsmp3rCfS66ycm8bFYuo0l/lLcHARCtuwljsl"
    "StpS3amruNApNyPN/ao/L1Qb5RZLScKqexGlTnyi74Vrl40OxjtB3KqrZa+SU1OtptI9VPL5Kp8fHs51sJ1dpUtNdb69VMUmrVyX"
    "G7nWSDbkzraw14qLduISzZdWndR+3Bmcp0ea35c3sRNXpRS6U+1lw+X8cLXma5VyODEKL6vrwuVyuIixaacY60zr6/K+wSQL2vaq"
    "rtL9qVDN7/hsZdxMyrtKRQBCvtG61tJU8TCJboViNj5dpErTUZ7p9rLn8GSSkJuHRbZVqfZrzcOkP4Lm4bzUnoudRn2VV1ZaTao0"
    "utq+WsmPauMRX5ie6f60l5xMOOZ6oTutSzASL8TUbDTdEKbjfq66zSW3wibda/NBMSUmm2Gw+p4a9emlV1mVmmA7ruRaYUmQz8oq"
    "XGj3U6VctThvVvrTRml7nqb1YYTXa8ENfajWeGp6zbFClWOaR/YynMQpUYhTdClayW4ndKI2WvYi602vMhWuYMN/SEH7eF3W5nMp"
    "VsrL+fUx3zvFk6v6pFKN9hklvCrte3VRjBwTlVG4uBXGk/xYuOT5kchko+VyXy0Vh4NJbji/9Cu5a7zfUqe1jXJaaZF6uL3uxOL1"
    "ndDJ5fNzuSGH1+2tdgECbVQpS+FaDqz3NYoVOhoYbO5wajT5a63GzNNif5FV5pOcEI7lL6PsSkz0JunsZLs6hZN9bs+fdwu6sJEu"
    "q2A5V901xqNGjCoEOyt5tOvmBTZcy0vhZjZ9aSwGkz1bnq65Pl2lOIq65CfhxGDXX8pAAY51T82g0onHe4fLZrjMDmvR+WmyjSlA"
    "z28Hk9qB2SRjg4tUpsJ97qjsV/tFh9735wy1TW1zzfRBZnJUfN1pj/KTCdOJb4REWb82OjWgMMXjyxqYTIf6WqcoPnHlorGpkmTO"
    "sUmkuI7x17083ZfL82KZO9PpvpCKLZn2aNDJDc4duc3nauvkML6PMM16XCtqI76RYFL5YKrCDhK0uJV7HZZu1juxPZcYCtv0YlQp"
    "dLbbxvIqjLlWeFhrir18snlN1TiglvU6wjlXE2m9c2nVq00pNZY4pj5Z9gdCRTjvG8nyWcs3d1k+yvYO51bnOt1fx/EGVWsp61RL"
    "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"
    "Yzvv4nrC9KeWN4Hi5LHAl2DfpP3VxyNwP51WMPUv2znMqek/fPsq9vQBHCuoO3zJXw8N0cwfqU9olXopGPOmQr+0rP/6r18r53Ao"
    "cPuqT3lo+t/eXOr49x+Z5GvX/FQS7+vo2/qbH//vj9Wm7l+P33zrR19fvFcNLu/F+qfaYa8ChN98+2+/sIKp/U0beDV/mNqP+p/V"
    "n/X/reOwvPmt2u7///p/HMRxsK+TQECcBI+DIqAz+dJ8EH/T3EPTUBR/PZMo+Kaxb5oIvU4aw+VPmkq8PZOfNZt4aQz6SbPB48AP"
    "jYF/0mzyTWUQ+pOlkG9kyFefLOmL5zdL+0gvv1si8j0BntEniNPvz4eev1nvJys+nvE3xXr7Qn/UtvfWz8r5ccxPz893tvK7OuOf"
    "1/im7fBPa3q3BvCL55fWQ5/p360J/bhn9KN1wR9lQnym/ygz+ZO1fpLpL87kjwxjQMYF698NI2J/YRiP9s/M4qV9v2cU//bfN4qR"
    "/fHD//jq+Pm+/a71klcFt6b/6m9vTa+fMBva0tt++Couo/Uvn5vfEMWrrno1/PBVcOw06n/qzKdhzOLtu7dSyfX4a4IXr++W3mt/"
    "+Or1908dvhcUr4KNdfjDV+H49b9/XtH3P/X8+zc/0Qcv+f6S9K3xS6r2CLmv8vO/oPvY/CWl/wbMvuu9MJuGXy3hrfP7984vRyWv"
    "jfyc9mj6RPH3//Er+X6SzP8xOf+3V/zdAZL6L9ddef1B8l1Wl1kdfRe9Ds6bxubPGR2kv8vmbZI/Y3R8i779dXN9JP+/0XzkJ7/V"
    "HGf9b7a3fTR/sbzDnIeXorVN9nMJfz62jyv///L0puFQxfd06IevXnHhp65mjvr4AGI/fPWOiL/Q9WbIXhjwh6/6qPTGbI7+Eeuq"
    "vfl7/y2X/R1De9f9H45o9fOF/KYBfsHtV7ZYHaf8HhB/f9Bb/5eDPgbO3x/xTvDlkPiQ6nfLn417UX2//PbgV+XiPxv6ovly4JG2"
    "1x/l/7nt55L/BcOfBnwfTr33+vLv33z7s7FvIvznhzXT+KaR/83hfrN+N6TeAcb+kbH/oAf9Us1+z5l+dtbnv/zCO3xu+j1v8MNb"
    "pfPv5mzIjgz2d3zDnxK9PMWfEr35jT+lenmRnxN94VN+kvAfatmriO8rE/7+nfZLUX084n9s+Eej+semeiXR/yDtryz8k+I1cXzg"
    "lX9sce+0fxR/3s63bsavv/+p+PQ3nxp+TvbRZ77605ej/N3j+xW73yN/O8d/mPpNy/5h6jd1+23qL5XlH3Hdb4P+GaT0q7E/O8zf"
    "O4bfF/g/u+BP4/6ba/48/E+X/RGOfxnRfxM5vpN9/7bLPnpdX/1av/8gsvzW+H82xPwujy9jze8dzfD/ElH+87gwH1/V49tpfDW/"
    "fXm9ffkZslt/O+DnU9V+PzbvG30b+f1B+/Pg/1szvttumPVf92P5ze9Z6x/0v9nnH/S/WeSn/i928hb54qavDmzVjN4YfQ0S5zBK"
    "Pq/1w18+3cB9VbOvNO1f/5f/qu0OpFHZRv3w1XdfvS4um/hf//Lpfo798b3lK2Or/Kb88ccPn1h8+J//82dd3x9H9vZi5KAZ3lo+"
    "/MfnC7/o843fxzHR33/4jc7oFzx/Pl106PrrzcMUvM3y4zvN0f4vn75/3x4bb14s/uPTGn74POG3b3v++2cR9Mfjt+ORjn6c/evx"
    "x4w9EtJvsmMh/3H3X7ep34dRfMQKtW8O+Yzb24C/zV45Hb7+26ieqvdb8h/+5fztsbY4S6bPz8uRKn/8/vdvfoj+c/zrj8eQn6bP"
    "3k7gdZU6/ui9lvJheLtR/vDNT8I/VvOFNMcfxtOHDz9xeBs1fvO3LP76bWv/8uOH5m3VH/73//6X6JtPMn0rKF7/5aD6mWz/rw/T"
    "IdOv6x+j//wovLFR+6zKXpj8rwezH99fB7yvsf/xwMpeWb7N+Jf3GfsvZvw0W/+XMe0PTPZ6+8n2fdN//eF//a8vGH9VHVnFVx+J"
    "va/az+1vQv3+wzd//3wYr52/S+Q/3u/aP779+OZ1iq81Neyv3zl/tpIPH2/aR/b9Lefrbdnnzp/p3vsRvEz8/YL920Mk3xfR9vEY"
    "/vPDlxcP7YFXq/ZIMerxw7eHBv3tX7+0zI83/f/6w7+M36fecOkjr3hLyYavv/n7t18y+u7f/lb//cO3vyb75q+v10LvGdeH38hL"
    "P3zqNd5y0A+/mwN/JmSPEPfhdzLc13XQG1D8lS3+bNvvPu3Dt6/dfsIA//rDTyL7eHfz/ae+v//17++M3+6Afs3pu+xo//DtO/z8"
    "k6lfRP/czK8Rv5741fpx3neY/Sfzvoj+uXlfI34976v147zvyP1P5n0R/XPzvkb8et5X6yc5vyLvL6Txanrv+U1jePuXF3/5zfM4"
    "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"
    "S+pyhS0s5T2JvRcoBzZ7TzKfnPfTFrLyZowB9ZTTQ+bVP/6+8mHpfzhe/8l6c/MyPF7u97H4c8Oy1f3ypjIKFQ6r9kvB5juaYkJM"
    "K9zIsZ0aL9VaTp+2+ynXk0ayGZzZnz0f3+FydQVnuE7aS/0YznIf1Vnut2NNQT8ef/mnqH49/s9TVP9/e4rq1+O1n6J6cfzneopK"
    "jCf7FJX48IWeosLSP9nG5YJZbKafIY1Svm2jbfns0uKssL3345HD5OLm4YLikXMYUeZYdNP3UDZrfWLmtyx6JkC30Z/GH7b+56LC"
    "gIVobQB7QqqpVCHODcne4SwGnMc/T0lzlFH2mD1Vh5M4WkgTwFQP8uNnRc6nOcgJn6/1Nqni+AGAugd1DyNHbCjm/bFUfLxByhLG"
    "E1Jtaxmo5CtaCFZb28IU5wrabxZO8vUu1vh17P70x2IdDJWzVDDce1Y1Y+Sn9DP2F6WkYbMLaz5ZXuddUMxpfN/6uql7HmAJAkqT"
    "FQfRTKm69EennguHQaHa4aPScolM5ylaoi/W+IqdCHqqF3LONJlLcA+BqaQx72emQnm2Gn1IVuDSCDgWNHcFm6fRmKnTuYyW2XiM"
    "vBFvB6nggASUBx9qHEQ/J3QgCGV2MNapCsaaiGCsIKtlgrHi0YZEoF2HXm/hKwnx9nZhSMiLjOB7QwBmorMmdnTWxIzOinJVii98"
    "Ywu5tAGbvq/ofzw21U8v11M/vfwzqZ9e2uqnp39m9dPzL6N+erqO+uno66qfnn4T9dNRVv306iuqn14Z6qc/nOqnlyXqpz/0WeXl"
    "V1c/vfz26qcn2px3R/NQU8/01mXZy9ECTc5qRJWsqm1R+xDj9pITuY2/yWB1wMqNvJTd78qfmrvpHqzv5/xYgTDy5W6itJxqq5uE"
    "hK1UUf2y2lodpVH0AMNnxPmb1mwwK9m0ZqZBpnqJXr9Bz+CYui0edNoSOEBLYBqelqMA60b8lWlGO6hduqeW1zaaYoMItKBXCdPY"
    "VSKYUt+RZIvhVgiT0I/nDApjACcEK1iUqQAxqdAwnxPxheLU2R9lVOU9qRrrq5hntqYvEXYIU4fJtlD5Sf9vaZot4yUo8wmV6Dsj"
    "Njq85C3MrhtVZ3qfSJt+HtIKkJWHJNZOPjHDGKx+UnrKt4ae8tl6UtqzP5OU9syW0n7+M0tp//wyUtrP60hpf/u6UtrP30RK+1tW"
    "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"
    "0J+o+Oe0oI3R+S2wBxVRXim+qzQSiBREF74r4ztaH3DIm4OWCAY3B/6Rtk4EQ9ZH60kiGLY+Ws0Swaj10WGVAMxl/lEInsWsz8Lo"
    "WcQspwUTEfOPUMIsrYX5jmiRRPDO/CvKt6XdJUJcJbFE2PwOLDJbDUYVsT1L3NkLoUHF7M9Qb7leIOrT0X7nG6CPoIUQ18G5MAFn"
    "MGAJicAVmuMr9MnVfwRjwUh4HIz4rgJXqENXQe5pYGL9WEHnGmQ9DZBSYVI0EIyFYqE4LToVND1xGwxp9O+RoIno7xj7G9SjifF2"
    "JI1vRuJJEtXr2xBqG/+/oOftFjMJdGQuX137Df+nq4gUNwKAN/1G/wL4f7HA2/8OewH1byy+0l9raXVM0L3xTVPHCXS1uwZxIwEF"
    "/HtlOg19gwHcRXyTQDxfmSVTSfhfrr5Mpor4Z1CFv6t3yWQr1Uqe/19+WRnd5fbjZSHpb+UGqY5SUVLrpL8TbKa6uVlynu7v2qls"
    "Ma3k59ViPp1fZI6DZDaUlBoZKbUvz1HLqXQyN2/PCsXUrrM/drV1pFcdzcZr/zYoiIvkcVkR542xmj1mk/Hn3unwNPX7q518tdI7"
    "FQv99KbW9M73+Vap9dTKdzTv8f5OedGik1qp3K2WYvpk0m94l/fxUXgUTFaS+/wsszuM5G1l27i7W2RCU28r2t3Wk7GD8lzQl0tR"
    "7smtgnpqpPXaztvaTapSWIvXB11lnlS60kvOGwyeQoXWQm3M05HioFxaVQtC7dju1UvF6PoUupefwqlyNpNZaplNK99P7RdrpRGU"
    "mq1jZ7NU4jmhtox2d8LkTm14o4NWZXx6ma/ESjVSEwpjb8HrDy/UU2gQzlXTq+zxZbGctdLB2rw16E5yz0pgOy8rkdhur1XCXqUd"
    "lhvFU3a/vkN8srPJNTrN5L5zyK4KycOyVLlTntVtVRVC+ag/1xUP2/Ju4p+FDuo0UtDTq1Rrlcw2M7n7kxhWw/PxIKzf1U9yuDuZ"
    "LEenRjzqXXtbFTVVO67muee1/z6yle+n9Y3cC+Wq0e4gmE2Fg9VRr3c3HYvhu51/UJXuT7FJrF9tN/uNY/q5n8qXs/m00IgG47tQ"
    "5amyW9dqmX1/158kV2KyKQab47lXKRVX9/N6MTku5tujWik5anSS2V71/rn0kh/pz/t6shGeHZOh1inSyE7v5XhnlLqbtnvdwtEf"
    "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"
    "RXdiKNkLPwvyIlxtFZZjLdQMNuvVSvykdmbyarb1pqK7dPDQmtz5C3tvObTrivmJUlsdN0KrE2jV1oOO6g114tFyaJWpzCbz8nNO"
    "3NzPM6f1NBZqV6u7YCoo154qrUNPaZeflMVMTK8L4V0kUu2N+vX4tlaYju536/lsGu0vlvIoNmrVX6LRxiaVbwYHddlfEKOzWraR"
    "6uel0mASkhbBUbpXaAc35U5UGq3Km9BLUIu+3A2C3miw4D95N6V5Y+rN9Pv3weLT7mmkjiOF0qxd7OYq+9ay3O7p/dz8KRcW9aA3"
    "fHxRtPpcS3eEzHggjTNHdKo/pSvKejVWB7FZK/CM5n/QEdbFYHPUXEipe2UWvuuvUn61mktm1VW/2F23RuVcoKRqmty9G5W66PgQ"
    "/PVK+3iaZw6jaK9ZW4/FaCW6OB21cE0OrQKzntqaT+uNQbOXLh2Efq+86sejymp5F5+UdohB70Li00a/X4fCO+E+H93Fe6FZWxil"
    "4rpe8L7sxdGiHd9kt+uAeD/qer1oR+Xjg0Y9Pm3VF8VjfSD25VloPc2I02R9PN9OFmo8nSy3q5XjMbcqdAapVW8vZ5qbybEmd7RI"
    "MLjXSt5qTBnvJstGcVkpa8fGfF+QGpO0mk+9qNVaJdhZLbu60pkKz4e7wbxbzI2fNuV2Rkxmhfa4X61E153CSt9PMjm0Q9qrgbDX"
    "BkG5uQyeui/taa43Px764ZTUboa15aJ1nFc6rdxS75fz+cMhU1BfqrGZN9JLpZ8n42X1vlzoZ8QQYvuZTCo7S94FOs9BOdbcldbT"
    "ZFi/H6Wrau9F7o3aM+9s3urt23InPVrca951tNTK1LqN1K6iRI69bKi4aUfHcmh23wmFXtpCdFnsrHbt4lhutXPrwN3kKRht33k7"
    "s8g4VknmesHwvFM4HCKDVbidrmZD1Z633utPZ71C0X+YFV42/km6+rKPCslMei2sj2F//tgWJ82SlNMXst6L3VfT4c7m0G3GK6GR"
    "uJV63bvpPt3W9/ntdlM5NgRRi+mNqlLyinI1Na0dSrNjfrQ8ViPT/vNd83RojCqL0+xFLe/U/HM11s+s5qdZdCcXN6fSodV9UXuz"
    "6qySnCWbx/Rs9zwLV7urdlY+NOX53hsIRpKRUDmfle/KwlOlN41WwvVWMDYejwf3+chgNCkqsWJ+cvQrwf5unq0GauNBI14f7eeK"
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
