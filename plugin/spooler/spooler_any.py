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
                # The printer presets, for the Printer tab's "which preset is which printer" choice.
                "preset": str(getattr(bundle.printers.selected_preset(), "name", "") or ""),
                # Your own presets first: they are the ones a printer is chosen for, and the list is capped.
                "presets": [str(p.name) for p in sorted((bundle.printers.preset(i) for i in range(bundle.printers.size())),
                                                        key=lambda p: bool(p.is_system)) if p.is_visible][:128],
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


def _slot_spool(value: object, seen: set) -> str | None:
    """A slot's spool id as saved, or None; a spool already in another slot is dropped here."""
    spool = str(value)[:64] if value not in (None, "") else None
    if spool in seen:
        return None
    if spool:
        seen.add(spool)
    return spool


def parse_printers(value: object, seen: set | None = None) -> list[dict]:
    """Cleaned printers; a spool sits in at most one slot."""
    if not isinstance(value, list):
        return []
    seen = set() if seen is None else seen
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
            slots = [_slot_spool(raw[index] if index < len(raw) else None, seen)
                     for index in range(PRINTER_SLOTS[kind])]
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


MOON_TOOLS = 8   # extruder, extruder1 ... extruder7
MOON_GATES = 16  # MMU gates assigned by hand
# What the last poll of each Klipper printer found: {"tools": extruders, "managed": True when the printer
# reports its own spools (Snapmaker U1, AFC / Happy Hare lane_data, Anycubic ACE), so nothing is set by hand}.
_moon_found: dict = {}


def parse_moon_slots(value: object, seen: set) -> dict:
    """Spools assigned by hand to Klipper printers found from the presets ("auto-..." ids), by printer:
    one per toolhead (2 to 8 extruders) or per MMU gate (up to 16), and the slice fill switch."""
    out: dict = {}
    for item in value if isinstance(value, list) else []:
        pid = str(item.get("id") or "")[:48] if isinstance(item, dict) else ""
        # A printer reporting its own spools (or not polled yet) shows no slots: what it had stays saved.
        if not pid.startswith("auto-") or pid in out or len(out) >= 16 or item.get("managed"):
            continue
        tools: list = []
        gates: list = []
        for unit in (item.get("units") if isinstance(item.get("units"), list) else [])[:MOON_TOOLS + 1]:
            if not isinstance(unit, dict):
                continue
            raw = unit.get("slots") if isinstance(unit.get("slots"), list) else []
            if unit.get("kind") == "tool" and len(tools) < MOON_TOOLS:
                tools.append(_slot_spool(raw[0] if raw else None, seen))
            elif unit.get("kind") == "gate" and not gates:
                gates = [_slot_spool(v, seen) for v in raw[:MOON_GATES]]
        out[pid] = {"tools": tools, "gates": gates, "slice_fill": item.get("slice_fill") is not False}
    return out


def moon_saved(settings: dict | None = None) -> dict:
    """The saved hand assignments of the Klipper printers (parse_moon_slots), for this spool source."""
    saved = (settings or get_settings()).get("moon_slots")
    mine = saved.get(source()) if isinstance(saved, dict) else None
    items = [dict(v, id=k, units=[{"kind": "tool", "slots": [s]} for s in v.get("tools") or []]
                  + [{"kind": "gate", "slots": v.get("gates") or []}])
             for k, v in (mine.items() if isinstance(mine, dict) else ()) if isinstance(v, dict)]
    return parse_moon_slots(items, set())


def moon_entry(printer: dict, saved: dict | None) -> dict:
    """A Klipper printer found from the presets, with the slots set by hand: one per toolhead when it has
    2 to 8 extruders, else its MMU gates; none on a printer that reports its own spools (managed)."""
    saved = saved or {}
    found = _moon_found.get(printer["id"]) or {}
    # Not polled yet: what the printer reports is unknown, so nothing is set by hand or filled until it is.
    entry = dict(printer, slice_fill=saved.get("slice_fill", True), managed=found.get("managed", True))
    if entry["managed"]:
        return entry
    count = found.get("tools", len(saved.get("tools") or []))
    tools = (list(saved.get("tools") or []) + [None] * MOON_TOOLS)[:count] if count >= 2 else []
    gates = [] if tools else list(saved.get("gates") or [])
    entry["units"] = [{"kind": "tool", "slots": [s]} for s in tools] + ([{"kind": "gate", "slots": gates}] if gates else [])
    return entry


def printers_cfg() -> list[dict]:
    """Saved printers, then the Moonraker printers found in OrcaSlicer's printer presets."""
    settings = get_settings()
    saved = settings.get("printers")
    printers = parse_printers(saved.get(source())) if isinstance(saved, dict) else []
    moon = moon_saved(settings)
    return printers + [moon_entry(p, moon.get(p["id"])) for p in _auto_printers]


def save_printers(value: object) -> None:
    """Save the printers from the page (or a slice fill): the ones added by hand, and the slots set by hand on
    Klipper printers found from the presets. A Klipper printer missing from value keeps what it had."""
    with _printers_lock:
        _save_printers(value)


def _save_printers(value: object) -> None:
    settings = get_settings()
    saved = settings.get("printers") if isinstance(settings.get("printers"), dict) else {}
    seen: set = set()
    saved[source()] = parse_printers(value, seen)
    settings["printers"] = saved
    moon = settings.get("moon_slots") if isinstance(settings.get("moon_slots"), dict) else {}
    old = moon_saved(settings)
    new = parse_moon_slots(value, seen)
    for pid, entry in new.items():
        # Slots the page didn't show stay: toolheads past the extruders found now, and the gates of a printer
        # showing toolheads. Only the gate count chosen on the page removes gates.
        before = old.get(pid) or {}
        tail = [_slot_spool(v, seen) for v in (before.get("tools") or [])[len(entry["tools"]):]]
        entry["tools"] = (entry["tools"] + tail)[:MOON_TOOLS]
        if len(entry["tools"]) >= 2 and not entry["gates"]:
            entry["gates"] = [_slot_spool(v, seen) for v in before.get("gates") or []]

    def free(ids: list) -> list:
        return [None if s in seen else s for s in ids]
    kept = {k: dict(v, tools=free(v["tools"]), gates=free(v["gates"])) for k, v in old.items()
            if k not in new}
    moon[source()] = {**kept, **new}
    settings["moon_slots"] = moon
    save_settings(settings)
    prune_codes()
    _local_sync()


_printers_rev = {"n": 0}  # bumped when Spooler itself changes the saved printers (slice fill)
# One writer of the saved printers at a time: the page, a slice fill and a pick answer run on different threads.
_printers_lock = threading.RLock()


def bump_printers_rev() -> None:
    with _printers_lock:
        _printers_rev["n"] += 1


def printer_state() -> dict:
    codes = read_codes()
    printers = [dict(p, has_code=p.get("kind") == "moonraker" or bool(codes.get(_code_key(p["id"]))))
                for p in printers_cfg() if _live["links"].get(p["id"]) != "none"]
    live = any(p["ip"] and p["has_code"] for p in printers)
    return {"printers": printers, "live_ok": live, "usage": usage_state(), "progress": progress_settings(),
            "stats": stats_settings(), "printers_rev": _printers_rev["n"], "slice_picks": list(_slice_picks),
            "slice_map": slice_map(), "printer_presets": list(_ui_snap.get("presets") or [])}


def live_message() -> dict:
    """The Printer tab's poll reply: live state, the booking list, and the saved printers when
    Spooler changed them itself (a slice filled the toolheads), so the page doesn't save over it."""
    msg = {"type": "live", "live": live_poll(), "usage": usage_state(), "printers_rev": _printers_rev["n"],
           "slice_picks": list(_slice_picks), "printer_presets": list(_ui_snap.get("presets") or [])}
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
                             "spool_set": bool(state.get("spool_set")), "hh": bool(state.get("hh"))})
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


MMU_KEYS = ("num_gates", "gate_status", "gate_material", "gate_color", "gate_spool_id", "gate_filament_name")


def mmu_units(mmu: dict, spools: list[dict], target: str) -> list[dict]:
    """Happy Hare's own gates (its "mmu" printer object) as Bambu-shaped units of four trays, read-only: the
    spool id it reports, else the gate's material and colour. A gate it reports empty (status 0) is empty."""
    def at(key: str, i: int) -> object:
        return _list_at(mmu.get(key), i)
    count = _int(mmu.get("num_gates"), 0)
    count = count if count > 0 else max((len(mmu[k]) for k in MMU_KEYS[1:] if isinstance(mmu.get(k), list)), default=0)
    trays = []
    for i in range(min(count, LANE_MAX)):
        kind = str(at("gate_material", i) or "").strip()
        if at("gate_status", i) == 0 or not (kind or _int(at("gate_spool_id", i), -1) > 0):
            trays.append({"id": str(i % 4)})
            continue
        colour = _hex6(at("gate_color", i))
        trays.append(slot_tray(i % 4, at("gate_spool_id", i), "", "", kind, colour + "FF" if colour else "",
                               str(at("gate_filament_name", i) or kind).strip(), spools, target))
    return [{"id": str(unit), "tray": trays[unit * 4:unit * 4 + 4]} for unit in range((len(trays) + 3) // 4)]


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
    if isinstance(status.get("mmu"), dict) and status["mmu"]:
        return {"print": {"ams": {"ams": mmu_units(status["mmu"], spools, target)}}}, False
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


MOON_EXTRUDERS = ("extruder",) + tuple(f"extruder{n}" for n in range(1, MOON_TOOLS))


def moon_tool_count(status: dict) -> int:
    """How many extruders (toolheads) Klipper has: extruder, extruder1 ... extruder7 that answered."""
    return sum(1 for name in MOON_EXTRUDERS if isinstance(status.get(name), dict) and status[name])


def moon_manual(doc: dict, units: list[dict], spools: list[dict], target: str = "") -> bool:
    """Put the spools set by hand on a Klipper printer into its report: its toolheads (one unit, like
    the U1's) or its MMU gates (units of four, like lane_data). They stand in for Moonraker's active
    spool. Returns whether the printer now shows toolheads."""
    tools = [u["slots"][0] if u["slots"] else None for u in units if u["kind"] == "tool"]
    gates = next((u["slots"] for u in units if u["kind"] == "gate"), [])
    if not tools and not gates:
        return False

    def tray(slot: int, spool_id: object) -> dict:
        spool = _spool_by_id(spool_id, spools)
        return _spool_tray(slot, spool, target) if spool else {"id": str(slot)}
    report = doc["print"]
    report.pop("vt_tray", None)
    if tools:
        report["ams"] = {"ams": [{"id": "0", "tray": [tray(i, s) for i, s in enumerate(tools)]}]}
        return True
    report["ams"] = {"ams": [{"id": str(unit), "tray": [tray(i, s) for i, s in enumerate(gates[unit * 4:unit * 4 + 4])]}
                             for unit in range((len(gates) + 3) // 4)]}
    return False


def moon_found(base: str, tools: int, managed: bool, u1: bool = False, hh: bool = False) -> dict | None:
    """Note what a poll found on the Klipper printer at base, and return its Printer tab entry (None when no
    preset has that address). A change is sent to the page, whose slots to set by hand follow it."""
    printer = next((p for p in _auto_printers if p["ip"] == base), None)
    if printer is None:
        return None
    # No extruder in the answer (an empty or partial status) says nothing about the printer: keep what the last
    # good poll found. Once a printer reported its own spools (U1, lane_data, ACE) it stays read-only, so one odd
    # answer can't offer slots to set, fill it from a slice, or book a U1 next to u1control.
    last = _moon_found.get(printer["id"]) or {}
    if not tools and last:
        managed = last["managed"]
    found = {"tools": tools or last.get("tools", 1), "managed": managed or bool(last.get("managed")),
             "u1": u1 or bool(last.get("u1")), "hh": hh or bool(last.get("hh"))}
    if _moon_found.get(printer["id"]) != found:
        _moon_found[printer["id"]] = found
        bump_printers_rev()
    return moon_entry(printer, moon_saved().get(printer["id"]))


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect&print_stats&virtual_sdcard&"
                       + "&".join(f"{name}=temperature" for name in MOON_EXTRUDERS) + "&mmu=" + ",".join(MMU_KEYS)
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
    spools, target = _spool_cache["spools"] or [], target_for_host(base)
    doc, heads = moon_report(status, active, spools, target, lanes)
    # The Snapmaker U1's toolheads are booked by u1control, so its prints never are here (_moon_run).
    # Happy Hare ("mmu" object) reports its gates and books them through its own Spoolman integration:
    # read-only even with no gate reported, never filled or booked here.
    doc["hh"] = isinstance(status.get("mmu"), dict) and bool(status["mmu"])
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"] or doc["hh"], heads, doc["hh"])
    found = (_moon_found.get(entry["id"]) or {}) if entry else {}
    doc["u1"] = heads or bool(found.get("u1"))
    doc["hh"] = doc["hh"] or bool(found.get("hh"))
    if entry is not None and not entry["managed"]:
        heads = moon_manual(doc, entry["units"], spools, target)
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
    """Note what a Moonraker poll found: toolheads (U1, or set by hand), and whether the card is the single-extruder
    one fed by Moonraker's active spool, the only kind whose spool Spooler may change. Call it
    with _live_lock held."""
    if pid in _live["printers"]:
        _live["printers"][pid]["heads"] = heads
        _live["printers"][pid]["head_count"] = len(doc["print"]["ams"]["ams"][0]["tray"]) if heads else 0
        _live["printers"][pid]["spool_set"] = "vt_tray" in doc["print"]
        _live["printers"][pid]["hh"] = bool(doc.get("hh"))
        if doc.get("hh"):
            _live["printers"][pid]["unit_label"] = "MMU"


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
        # A printer that once reported its own spools (U1, lane_data, Happy Hare) keeps them, even when one
        # answer comes back empty: never set Moonraker's active spool on it.
        if heads or "vt_tray" not in doc["print"] or (_moon_found.get(str(pid)) or {}).get("managed"):
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
                moon_found(link["ip"], 1, True)  # its ACE units report their own spools
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
                    state["book_ok"] = not doc.get("u1") and not doc.get("hh") and not connected
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


SLICE_MAP_MAX = 64
_slice_picks: list = []  # sliced filaments that matched several spools, until the page's answer
_slice_lock = threading.Lock()
_slice_count = {"n": 0}


def slice_map(value: object = None) -> dict:
    """{printer preset name: printer id}: which linked printer a slice for that preset fills, chosen on the
    Printer tab. The saved one when value is None, else value cleaned."""
    value = get_settings().get("slice_map") if value is None else value
    return {k[:128]: v[:48] for k, v in list(value.items())[:SLICE_MAP_MAX]
            if isinstance(k, str) and isinstance(v, str) and k and v} if isinstance(value, dict) else {}


def save_slice_map(value: object) -> None:
    with _printers_lock:
        settings = get_settings()
        settings["slice_map"] = slice_map(value)
        save_settings(settings)


def fill_printers(printers: list[dict]) -> list[dict]:
    """The printers a slice can fill: PrusaLink and OctoPrint printers with an address, and Klipper printers
    whose toolheads or gates are set by hand. Bambu printers and printers reporting their own spools never."""
    return [p for p in printers if (p.get("type") in NET_KINDS and p.get("ip"))
            or (p.get("auto") and p.get("kind") == "moonraker" and not p.get("managed"))]


def fill_places(printer: dict) -> list[tuple[int, int]]:
    """(unit, slot) that sliced filament n goes on, in order: the toolheads, else a Klipper printer's gates."""
    tools = [(i, 0) for i, u in enumerate(printer["units"]) if u["kind"] == "tool"]
    if tools or not printer.get("auto"):
        return tools
    return [(i, s) for i, u in enumerate(printer["units"]) if u["kind"] == "gate" for s in range(len(u["slots"]))]


def fill_target(printers: list[dict], host: str, preset: str = "") -> dict | None:
    """The printer a slice is for: the one chosen for its printer preset, else the one at its host address."""
    able = fill_printers(printers)
    chosen = slice_map().get(preset) if preset else None
    return (next((p for p in able if p["id"] == chosen), None) if chosen else None) or \
        next((p for p in able if host and _same_host(p["ip"], host)), None)


def place_spool(printers: list[dict], printer: dict, unit: int, slot: int, spool_id: str) -> None:
    """Put a spool on a slot, taking it off any other slot first: a spool sits in at most one."""
    for other in printers:
        for u in other["units"]:
            u["slots"] = [None if v == spool_id else v for v in u["slots"]]
    printer["units"][unit]["slots"][slot] = spool_id


def slice_fill(slots: list[dict], host: str, spools: list[dict] | None = None, preset: str = "") -> bool:
    """After a slice for a PrusaLink, OctoPrint or Klipper printer, put the matching spool on each slot the
    plate uses: filament n goes on that printer's n-th toolhead (on a Klipper printer without toolheads, its
    n-th gate). A single match is set (and moved off any other slot); several are left for the page to ask
    which one (_slice_picks), unless the slot already holds one of them; none leaves the slot as it is.
    Bambu printers and printers reporting their own spools are never filled. Returns whether the saved
    printers changed. Runs off the UI thread."""
    used = [s for s in slots if s.get("grams", 0) > 0]
    if not used or not (host or preset) or source() != "spoolman":
        return False
    with _printers_lock:
        return _slice_fill(used, host, spools, preset)


def _slice_fill(used: list[dict], host: str, spools: list[dict] | None, preset: str) -> bool:
    printers = printers_cfg()
    printer = fill_target(printers, host, preset)
    if printer is None:
        return False
    with _slice_lock:  # a new slice for this printer: the questions of the last one are void
        _slice_picks[:] = [p for p in _slice_picks if p["printer"] != printer["id"]]
    if not printer.get("slice_fill", True):
        return False
    places = fill_places(printer)
    if max(s["n"] for s in used) > len(places):
        log.info("Slice uses filament %d but %s has %d slots to fill; not filling them",
                 max(s["n"] for s in used), printer["name"], len(places))
        return False
    if spools is None:
        url = current_origin()[0]
        spools = (plate_spools(url) if url and url != BAMBU_KEY else None) or []
    changed, picks = False, []
    _slice_count["n"] += 1  # under _printers_lock: tells this slice's questions from an earlier one's
    token = _slice_count["n"]
    for slot in used:
        found = match_spools({"vendor": "", "sub_type": "", **slot}, spools)
        unit, index = places[slot["n"] - 1]
        here = printer["units"][unit]["slots"][index]
        ids = [str(s["id"]) for s in found]
        if len(found) > 1 and here not in ids:
            picks.append({"printer": printer["id"], "name": printer["name"], "n": slot["n"], "unit": unit, "slice": token,
                          "slot": index, "material": str(slot.get("material") or ""),
                          "colour": str(slot.get("colour") or ""), "spools": [s["id"] for s in found][:12]})
            log.info("Filament %d matches %d spools; asking which one goes on %s", slot["n"], len(found), printer["name"])
        if len(found) != 1 or here == ids[0]:
            continue
        place_spool(printers, printer, unit, index, ids[0])
        changed = True
        log.info("Slice: put spool %s on %s slot %d", ids[0], printer["name"], slot["n"])
    with _slice_lock:
        _slice_picks.extend(picks)
    if changed:
        save_printers(printers)
        bump_printers_rev()
    return changed


def take_pick(data: object) -> dict | None:
    """Take the pick the page answered ({"printer", "n", "slice"}) off the list; None when it is gone, or is
    from an earlier slice than the one asking now."""
    data = data if isinstance(data, dict) else {}
    with _slice_lock:
        pick = next((p for p in _slice_picks if p["printer"] == data.get("printer") and p["n"] == data.get("n")
                     and p["slice"] == data.get("slice")), None)
        if pick is not None:
            _slice_picks.remove(pick)
    return pick


def apply_pick(pick: dict | None, data: object) -> bool:
    """Put the answered spool (one of the pick's matches) on its slot; "spool": null leaves the slot as it is.
    Returns whether the saved printers changed."""
    spool = data.get("spool") if isinstance(data, dict) else None
    if pick is None or spool is None or str(spool) not in {str(s) for s in pick["spools"]}:
        return False
    with _printers_lock:
        printers = printers_cfg()
        printer = next((p for p in fill_printers(printers) if p["id"] == pick["printer"]), None)
        if printer is None or (pick["unit"], pick["slot"]) not in fill_places(printer):
            return False  # the printer or its slot is gone since the slice
        place_spool(printers, printer, pick["unit"], pick["slot"], str(spool))
        save_printers(printers)
        bump_printers_rev()
    return True


def slice_pick(data: object) -> bool:
    """The page's answer to a slice pick: {"printer", "n", "slice", "spool"}."""
    return apply_pick(take_pick(data), data)


def slice_fill_ctx(ctx, slots: list[dict]) -> None:
    """slice_fill for the printer preset being sliced for, off the slicing thread."""
    def value(key: str) -> object:
        try:
            return ctx.config_value(key)
        except Exception:
            return None
    host = moon_base(value("print_host")) or _ui_snap.get("host") or ""
    preset = str(value("printer_settings_id") or _ui_snap.get("preset") or "")
    if (host or preset) and any(s.get("grams", 0) > 0 for s in slots):
        spawn(slice_fill, slots, host, None, preset, name="spooler-slice-fill")


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
        elif msg_type == "slice_pick":
            pick = take_pick(data)  # off the list now, so no reply sent meanwhile asks it again
            spawn(lambda: (apply_pick(pick, data), self._post(live_message())), name="spooler-slice-pick")
        elif msg_type == "slice_map":
            save_slice_map(data.get("map"))
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
UI_PAGE_SHA256 = "1d0bad5c13c385a06861c3abacb939edac0ecd7c3af701f6d1da45ef34da9a16"
UI_PAGE_BYTES = 1353655
UI_PAGE_Z64 = (
    "eNq0vXlz28ayB/r//RRmnosXOB4xkpOT6wsaRtmynTiL7ViOs+jokhA5lBCTAAOAWkLyu7/+dc8GUs7JeVXPVRaBmcGsPT3dPb08"
    "7k2rSXu71Pcu28X8yX89xs+9eV5epJ/p8jMk6HxKPwvd5vcml3nd6Db9bNXODh59ZpPLfKHTz64Kfb2s6vaze5OqbHVJxa6LaXuZ"
    "TvVVMdEH/KLuFWXRFvn8oJnkc50eoZK2aOf6ycmyqua6fvy5vP7X42ZSF8v2HnqXfpYvl/NikrdFVX7+e1OVn90rpulnjXxzcF5V"
    "7WdPRqNnb968H40efy6fPvmve/e6tSyq6WquP3syW5UTVHVPRzpezzXlp2/Of9eTdjCpdd7qqFzN5/FwVtURcst71eyeHjTUhzYa"
    "q3Ect6flWXo0rHW7qqma9Immkd1rt1d5TXWtt6pMT89UnUZx+oTeCn7oHak8RdkBZvK4muqnbXQYp2l6dHTU73eSjyT5sN+POukP"
    "4ydHDx9uNjuJj//3f2JVSeVNm9dt83PRXkbjqvxpOaUBJeNYNXaMedMUF6WapJFWLTrIY0z1oCin+ubNLGrjYfnkgLuEMU9oPtRR"
    "vFVzW8OyrtoKczq4zJs31+Xbulrqur1VK1vnfEALPOcXNU2f1nV+Oyga/lUz9POGpp6GOD6tuMp7P+TLs7Fa3pV1olvKWtyV9ZzG"
    "RnmXyEN/sE6UbRd4rC52cpq2LsqLsRrtpt8uzqv5WF3tpEs7436/19PqFpnRFfVhs7mkv3G/Tz+D9lKX5pFAdHIZq/P9iWqrE25a"
    "3aCSczM9sTqxwxo0PNOP1MFRrI7vGqzUScO9Ru4F5dIK9ajA6/w19VCfHp7h7YCex+MHS2zWV2VLa3DEQKaV1qkm+P2ob1WtZ/g/"
    "IhDnX6RV5YeSAOqZpkT9Q7UqW5vEL3raLSGQZdPkbbdIuQirMa96StDYagziLzaf7K2opOWgzbbZRLznKDeOCRTfp58f/Ov68wtV"
    "6pQ+YcCv9XKe0xS+V7IPeD6PYpr6n5YEnsd5oyP6mMabfv6vZ9Hp04PfzmKqotivotZqfHD/aIyPv6+u3ccq92WxAXkDdxt44Fum"
    "LemKZ7QX769zYJztOBljP2q7WXpm/EUjG2bCOYPBgHenw0Lp4bB8rAdzXV60l8PywYNY05REXI42p1SnSkI7vSN8aGqd6llRartF"
    "ucyacPSsuFjV+flcJ71DpcvVQpu3I3VdFy0/1+oqn690Um6pgVW4YgxdL+dVTvBl1+pe0RAkEvbIdNJu1TQsD2jNXq8W57qmp4TK"
    "3f3RTCvC1MCWM73ZpGYnXsyr83z+/rJoHo9X48y/JqZAo+czzsKDTbwmfFZdc7I8Jp3qgqqS9XboDoUFnwrFLJpii5v+o8Cn14EL"
    "1SmWg3D9RVTH2RUBUZws8HdIdRWx/ZxPioJOEH2WFvRna+ah3VKxC8YtwDCxPVv4TLkkkB1GWe/0/6Kzf/wrBtReUFISnf7f2YP4"
    "czWil8+iLDn9v8/+9a+zzb/+RenxPz7b/Den/XeQ9t/ysPnX5//6B/3+I/vXP/71+ecXfvhXwaFIo7bdcFtjpNXeMfP5P8ZxNh4n"
    "wGJ8SF7SEw34RT65BPRjNk2lOGekzAUBTmlm8QkdNtjghMIGhCYXUXyWlqdH9iXebgljbF0fX/gujsdDM29xm+qhnjc0wWbt/v2K"
    "UUW0ZgTAaP5BWj8Y3xvHW1vJVacSrJvmLSeFSy5sJ6g1XfWdvLVw1NN2MYHZhlTZejKnQzhpVdPezrG9qOe2HjpqLmg7yMGPYtTJ"
    "llBJySn8QbpgNKgENs4ZqxetXjQT2uOKDpbqekYtEe2jdammRYPNvCwm1IAuSvNg02u9qFqs7e15PvmoaLiLsqJtXzB2L5pFvlRl"
    "JaSTCnLwRVOUc8IthFHzaVXOb2k63PBvePgyKjo8iWTBWTb283OiBV/xHNnFoQOsNY9m0npHQ1mr3qHbggUtKC1Z4de0oDWl5aQq"
    "T4sz1eJP6dam9o0edxttij81N4mH3QaFapnV1YIWgPZ1qa/v/VSU7SPOiGrbT9etlulEgS2dHhy5jJz6mz+2Hwxz6izgojjNCZao"
    "062q6ZF6Fa91mg/PaT4/Ah3ox4e+U0AW6ZFBF71DP6ZrNybpN/YadZfpOKqk3mwKOj7rdCnpS4wGiQ7HYCozNzMJ2ppF5vQgwqAB"
    "deKWJ0xv4721skOuZbusZbl2CUXCikQLt/upjCtpC+SbTY9+8cOLWmNRa54i25RFnEJXCa1knttgG77X9liM1yUdKadYxh8A1PJ7"
    "htU+LVROGIdbR6cYDef81LppKgYXupV2aJfm/NYyZTUsBg2ycHjn/Ngqwm4Ye5XWZl7dgUcnMuVge1Bh80wfVgF+60Ap2rOjPjSw"
    "uZC1BGQ6KKclzXgpNbr2viAswX31b7S0CQHCSD4eWUDIuAnkTCVn6nK4PjeFJ9pWcSUFr1zBXo0VyyjXlb6m0ncuDig4YK7nTCH0"
    "epEGqzEaXY2K5p2eUdHeYayeWyqXKAPqIHAnzpipOyIZIVq6mj46px5cBklxnD3HLGfPKZEJmTj59uTN64EwAcUMxNAbrR4G3aR3"
    "S5U9x6pkb3g09nPsqWx9Oia4ie6vBW1s4/FZcgoqbEBsb13ohk4vOi6nKzot6eNTmgviBalGguOPvNljOjrSJ2OCOAITtSbqKlma"
    "monZuatmbp8rJnyMI/UjRkbfYREz1BonV3xs9Kbyc4wMN+V01nyUkREOpq4ABLLxCXM91J4mOBRWmcAvy1pqOdHqqVa/65QPIVCM"
    "NG2rSUv7W4PAXLdEf9FnLZ3xekrcBb+PcoLgKypwaN4rOnzlUc9mhDgaMMb8PpnrvFwtfQKt/tt81VBlRINKynVel2/Kd6vSV0hQ"
    "0nwslkjoEdw8pf/RUz2QdrOICxF1CgnEU9Mp5mtTlOITsiFs6J6p9TgeLFfNJX8aE/eVRN2h3NEZou23F0DsXCSy59y98MPtEoOJ"
    "eA+H6WbmgtHKpqbODm1R6ZulmIIkw1vImaMxtamloYb6cTvUdLSUdFAMTONbXy5chN1Pwrzwa8KxzWpxxyD6/e4g9gd19P/DoGxv"
    "tkEVdkT/cR3belUaCq27PEJYPtXDtr61C/tUc2uKp7Qoica6XSNtu91WJU3PgwcO3NOUiVmGw1pfnWCIAEVTRbytZrNwQqvyyWG/"
    "f3AQVHDI2U8ZLeMT86mvj+lcQ2dQRzHmoR4aosa3aj5fh2k7FQmtQYjYp223O52/qorpvcPttmmr5Z0ztrNfeOUJ63G/WlqL8k7g"
    "ax+Xw3YX+NqzATcjC3nHZ7y0rkqLRO6s02ZSpVHswHDnE4ueQujUn4ROaVrvNqddv+nkGoYf20ZAzvU6KNNsIcFVhLB1p21JtrUs"
    "eUa0yHuQ7yAsLHbqsd0ZxD0G8fnUeBuiR7usAe/7Q4DLnmpPkLzmU5DR/g7Cfar9hDIWpVMSkhI+4N9q9VIz3fwzQRkdberVneeJ"
    "gaBZaY+RqaZzQfrnE97nxbyTOJvnF036T3kp9U3byTXd6qQ1mHhiZGqbuj8aC23+SEh8Y/304GHsELtP36RffelxZVD+qy/tStnv"
    "v/onzYlQlqicsl9qRwUiRXpKB/fFha4hsNqWVQtipVPxQ4KYsOIvHhJVFLw/2myemQoZ0QknGn5x5AhbM/mRgVwzoofqvu3RT+ZB"
    "UHr6FrDwqx6+NUjxV5z3IbZ0FTpc+bOtir7R+KBVnVn5wmAXj1xsJ538y2wMQALhOmAsLPlzvYz/AC009IBzJ8Tc70xvVZ5Qc2YL"
    "yksUd7v0kPCgXYTukma0Yvl0GkKHA6ys+xqZfFqCV7PnBZgcXg/3sv5aW0CwBSOhLaamgJlTW267Vd/jfHun1Z/a79xnfodqu4KP"
    "VJtFMk3pnyie0ua0CfT9OyT4Tf4BsPs9HZQ+6Rtz9B8cfK+fWF4UmPRPh63+lOPnT3tM8DkkR6i0NNSdvandBP+v4gOUq5Ej7J3/"
    "9p0kvXPVtkNHOUi1AJTurg9qbh38ACxbv522LKIninjN8sUtkQlbZrXpyKir63sB0vuJJRiOuU+1wF47bE0XAHtEmuu6oeLE76uW"
    "D82njEu+L8qPKaSvS4NckKB2E9JAqvWzl7zxGWMhWNWpHKXDemhnveaWqAPD2nUgpS5kxJsRr0RYhWqI1R+QP6pv8ZcAMa1Vvdt+"
    "vdNltZtgZ7dO9Vab/aV852j63AC+/jsTxsuGTphus/jFPBMG46xJtViuWhyR0Xc66qbFttAd38eeTXaCp8GIN5Lv5XdWLmch8Uug"
    "Uvty9BU1EHkgPfofGqxIiT+4edatFOqm0/FGzRXNyck78LOmvoePaBQ9mQqc8qY/xKvydMW2z0O3bR8Og+kjSCB0Wxt0qwNcy+A5"
    "tDJVwrZUtbCpw6gNgOJws2lwg+eyhXE2jVH/XA6xo+5DImrMVuHTGVsjyFPaYfa3+Ix6VSuG32B/E053k/6HR0+Qf9LAklIxhbk6"
    "T2oF4MBTAUkoZFbUxXpgUtNCGeqUngUaY1VQicKl1kq70rZEOWhW5w1WC7tBXmrVo6pLD0zx2r+4jv9z6M+cIPsTJ48ikm/bAwV3"
    "cEDNTFA/Menmxx7tJSRmAbL91m72tdnIxKGbWkUe3IJwsA1BUGB3vB8gj8umtsp1y5ZgGowBRv2iidH1p8VvwOu/aCFyfqVVQ6kj"
    "37sfkS8TgFJMff4KaU1q6t5sAkR5343F0FxJa9ZR71Fhttq3DM8WtwNHB9QCIJ3oUnRfg+Ju27uoRlQmpy2tuiccLWlhd4ADW08n"
    "8nxZHse9WADy3E/4socR6SAu27+gZi3c2K7Z/hhSNN/DsHYsXcqXYKjzTmC0Q9Km+6IRolzyyUd7//CWjrrer/TnrWUJ/QYwyEcw"
    "zk7H+IgNlrxF7wjfvqXDcrcsU/ltG72V0YLQ4w2TRa2b5bfBmRY8+yUJU9M2Tsxr2klWNcSu7qan7Zx/vGncygfTrvwJ5PgsmzL0"
    "e8t1VrknrtI8u67Slrl7XO3OJvw7A7VvIliO7BvRZu5u0NIvFrgCTEz8p4FsYRO0YxioMGg63l47VDTAzOAyA+mxRqKtJGblD3rH"
    "SWvT3P78huUnAd9Yt+5MxQfNBB3j780R60nC8CxnAONDkb+iPtHw3DF4GKDh9i7sy61u7QloqxiCJNB8xtlNXBpcaXe4xuWZ+wC4"
    "BqimaB2rivuBvE2NfBS39VXnrQnf/DRM2kBu/yv14a0TJxWtuT0YtpsNvZj7gtTcQsRGri+lcFkAjQcuhQt9lCohamd0QFuA0UCJ"
    "BNnpcXDWzlt746EKlUsHqqADQAkV0b8EOIZM4jls+LqeRfGeWkZhwJACHhgDmdfjuHJ3u03sJVGF3B7kKR3N1xiCXOVgX45FCjK2"
    "O88oAtTx0FcVYd6oA1H4wWaDt4amrDeKoGRTPkkh+Me1zNZc1DbXBciUCMtuMVXFDLY5Brl8ZSaWOuhfG1ys0ikyyRs9Jo5unBRZ"
    "kO26TVyTTcvxySzSQaUVbjREkDbkmuTIp8poDf+T72i1x0m3DD7bbnm/ufVdtf76+8dQ/wJrRFg+muD+CTfCdU7dIGCN1S8oF2dt"
    "8isesm/5b2svE1oiHksmRhNJa0v7pMug5Wnr73QZ2KX9nbYCymAml2L2E2mcWpP2qU3cTMQJP/AeXLbpejRitanRKMGdjzqVnTaQ"
    "Nqr6zPPEi5Z5YrVTAgoKM5OFSxJFxzPRstCU8d1fSYF4EGTa+QAgZzzNCX/v7nV2Gx6bnDGajPTp0VnqGqaXWJrXhK1vOxMxct8j"
    "i76m/WrOi7y+WC2oWuL01ayYt7q++0vJk09ZIcP0PRj4Tl3l9FM1lVNXj/987+tXECF+ugrO/ouhlNPv86b99PfI/TvdQLl/0xVX"
    "5NPdscopd1YhmZ/8uCgn89WU4KEDULf2c5tN33NhUar8VFnOlaK/V0UZ3QGhJn2r5nZcn6wvKCF1MlTcNUjK+OQAmeC3X5zbLyh1"
    "jEzwDJ3WfQnKkmbN9afRYrMFr2xByeb2XeF3xcVl+2++4DL2s+ayIDDZ7wWno6dNtdB3Dx45nxy90Xm9e4iSKYNsq3fYv42eRvuL"
    "Fmai6ElVE8Vz1/IGeVyQW5h+Alvt5G/VqpR5uLu7Jlf6ay+R97CYZIx38WaoFNd2dUz4JFBFWp+2ZzjyRZ9V9Ddqob96cuaAFMot"
    "DrdX8+/zizMc86xJc++VwduOPujqg5o3Og7fWnVagv88jr1yGosBoTVIEJTzG5EsRB4V1JWLlvrY79+lDQmcrpWZjmSNA9d2IR8Y"
    "zsierXdoF2d6cA6smtMxQdwgS0l2a+HEv1/JFsdnPhjxgGQkKt8Z3siNz/IHuT9xL7sYlqjcqtQsrBIRT+t0Iaz+2EVrNJ2csrJf"
    "9tGdpKQsfpNW4UKrSVrRRAMAJnbWLZUyGUCBH0dg7hatscc/E5/ztBya6qImm6e2B6wtYQdTCpQxfBrKgjpGkJ04PcKH9P3f+LqV"
    "72Ihu1fUQc6r1Jw+cD2E7ksRreJk5ef3qvXqRIbqbQ3Z25mNipiOBnehJjnKs6hJrQoYxHJUJOynKlxPcbvXsN5BaoYJaVbYe06u"
    "Cb55FH74X9CXn6x2dwKKYAomaYFb0grYN5iBjBuaxMkk0GvcQQVCghI1WHfpwKFMDzAEkJNTgIoK5tSJC4KizxERu78RYX56eBZn"
    "/IMK+VX5T+Ok8B04Nx2A6sYakizFXG7QG9zGWojzilegohUkW6pmwKc9paOxozaVU0Cip6L5sNLE6J0IhwatHI+GApW11/mCcIhg"
    "t3hg6TUix6CJ7w6VsVHUx/wTzRZbWk2+O9Vn7tNRHLCTx0xuj1jhiYo7JaV46Ih/uZbzFDnR/cT5AN2rPe06LST2dfsJlR4jn7WK"
    "HO+MUqdT7Smak0tWLk3b7YUOWV1mDq34aexUl51EyjK3OzXT+bFT8zCsjAuygMlW2av3CxjFU6sEt1PA1Ovyi05+nfscMJpRnRXZ"
    "N23yoSVG8Fmb/NnGhmnebO4+hVix7e6sEoprRsApSqBTy30b3MEi0hySinTJ6NLNnOtldwldZ48Fa1YpQevctC3rUYrCnLDf0UiU"
    "wIwiY3IDyRmAqd5sWFYxpu/GQKNeGbTCh1RN5eRkOfh5qqdKKjk6hl5vFHp42XfCKdnT6Iq+zWqkVnHyM/+t6Hh8b+DuHp1eupw2"
    "BIh3aJU1KxppRMBI0NroPWSrhd6YMpN8bTRceztQZDtO7GYhBX5pWXrQ+1V+CQX9iDzCIT+KUKBHg6RBFyhEv6VfCpqtwpydRFD0"
    "Ds3E59aaoY2dFnKykjOpccviR2AXxiNXyGKp9RrcPtB2xrc06AELcFgawJ8WcSIpkFDwnqMmtiJkCM067P2o6UUtk1W4ztzxhdNJ"
    "pdHbdo30wtPGOGe2rBTr27B12mRb0YiVDx3EWTBjnER9KrfVdfmdqBSHcoTg5GDe20pekpw+sm35TwmaXvwn0HQYQJPTST+8cwpd"
    "5lY9F9z/vlVv5OlFqz7aNCj6qKctm9yp3/k32ItdFBHo1zisaQbvjmo+dw2QO2k+4ScCdgFVOtaJRiQqi/XordxB1Op35B/9PhEy"
    "Ug5q2mO8r9jYRJpR07TMnrZJm7Vloi2JiyssWos8WIt5VrW8BE3UJclXsVoLFcrXPmIlpBVoTdz9rAwJ7ujebLdIYhIm2SktOJ/2"
    "U5afxGes4WvLEUEcSDZfh/KncOoCghejNiAMbWTt5ZaZwDMrZASVvm1DwF6LmHAdnlhmJQrZrrIihGCBGnjP5jHPXGHQKaGJ4C2X"
    "43pNW4DQYPo7L2aTtlgAbRaAUFQlxFnhNdzvNVFthZadEvleCeaFiMCgbWw/2SrokECLOLJUeDgYu+aaew5CIpTiYcmNCrKSjRwq"
    "bdr5qGUeZF48CjDT0jIqE7LQbv/grYhFplxkpT2dSoc05KkI5DTBEcD0K1hO248K7ed7k9oZYbUzutzLnUXb2xDHtWqYt4nkTNw6"
    "A6gGN+jZmlBwQlDIqBgmfC2/AVUTyDLUcYIBQBoxII+TjOycIB+qQ84aytJwNJu/+9lkhoLvlJmbkJOL8GKR+MMXcySdBgTyJb9m"
    "UOzkaMkp9nMKEAIlKzLR5M1x0SAnTA4IY5pvqwRp0n5oNxs+RDebX+UnsmenJ7xlIAzpBcAvyRneayAvKyGAXUS12aROdhxkSFUN"
    "8b2+rBut7YkyB2UjB2VtDkrKoqREUngYXFhG4Qwu1l3CWfpacl9r7qsY+hhGCe0XYV+DjNjQdHVW+0RD7tFwW2/kEZyxcybQ7QGr"
    "nfAJxh8CKk5y4LqIOzNjpiSqp6ZcYDAm57YAmK2z84ODdxurUzkOvLzHi693Zexue9Tpk3V5Wp+lP2BmWfCG2hz2fNnBngaXWk5P"
    "pAbpk+IOkj7r6aS4g5LPOsmWfs9anwqqPauTkPRdGcqpgNVRnZWJtMz8zquWkXpCPSWysgdD9u+7SYeU9C5IOpRSf3bvA591Xz90"
    "X7/pvPoT/yc+sswdlTZXTXKYjhN+YeHLODHLeSRXQVSHyT7RtqCpO3jjPPPhw+FUz/LVvLUJh8EZ93N4cAoq0ckfWCwa//NWvWpp"
    "tMFFz9dheVvuY0sTR9MQlPtuv9whUUs0mzQ/Qbk/AjmS6CSIFb22SJy1WUMrIKNabouAi9xsvKH0C1B9TXE+16GtrNmTRXDTmdvM"
    "3Jhj0YKcMA+NI5V17TtfN7yMRL/dgCBEgYcEa6H1liCiBjS41+bZn18k2dHFya6Rkxmer+HXNjSX3CnMOyMo/MsnC1sOyJf9Leya"
    "zlgjTnqVdDR+gktFV58nFIiE40M+CdV+wl6A6QhEAE7eurNUhKx0pyR2nxFE6hJUNHOUPwtHqVqfZJhMv7PKsjOwXQOyzujqsGxe"
    "MjwHc8QpnoZ0TDRBQiVZ3MGq/Es1JOgeyUW918eR/oTGS16K4gyLaJo/iHCWGpWTRjKuXCpfz95VCYti7nHBHTMkqDcY5YCwOvBB"
    "przuUoa2Gyqg81xDfPxrOf5pZxEz7PrayCWLVXT3w9GdYZTdYUj3rJJ7eNfwJlgrsxQDwz7wMjRCpSeGlUqfdOQ51MqbaE8sEgux"
    "5sQJxjGBCBSGvjEvAMg82w8YTfZZ+rrT60kIYuZ+OwlxSVMKFM3Lv1AauwNmpBOBIKlNd8GNp6PkERIZA41ZXni5WGBa3sy0TTHa"
    "8iP6LjV6cSO49qk/CU0WFu1nUdwFJFcHs+d+WlbhtKC789IKIqef2E5MbnbtQaheokysZl9nStTOZIRa/vuz+Z8Ylhx9JW+7Wr4H"
    "R5+wOBHTEWFQOu0bQWrP9J9VhNPS23V0bB42aLhjqfEohiaRsfyxx5Wx7mD82TvsrFvXWsIiAQvl31lDCNGR6ijLBXrVf4E0giUx"
    "VgvysrP0s9LI6Y3W7z06/G0nQAtldaphS8zmygpG4lRNzHbZU6EdzY5ZlnCptCg7BNdlafeEa/CiNErG1OalSKZLi+IWpdWsIk6G"
    "XkSzqsUdAjT5xHIpoJhGqKuEhFpEHMVioacFXCnlxE7oZVKpqpzopFHO1iOZq3x1AYH/t9V5slJgC5LZNi3ErVFF+MDg0IpvPuT3"
    "MLtCU0fEPDByXKgLNVJX6hbjOE/FGF/QYHTBl4AGG1IJuWFNBNuYXLbyv4UFNQtSsugcwH+L2eXr8PTJt9IJ+VjZOs2VxNq25qX4"
    "IvOldP7Qpi8NgXUZpM2yWcT21NBXoo5dpLzOZTbL2KWLyUzYLRZ9O5L7G1ZQHAX6hT+yfqEs3GU5pKVehOZF0swX6vTqDE1d+Q+p"
    "ZLvdQqG836/sRrigZeYZP8yOPj9MqqEMGdONo1E0CG9S2L6pE3HZtTBGiOqm378ZWJPXSXRjzcPUQnTjmn6/tO2UwzKNrNeeoLva"
    "uOixnTxh5Ul8c5yeZ+JMwoqQ+SJoHi3LOFmW4ugJE7Ww1gS0ZRcDY0BgLtc9iIvxEOtdE2xtNlQmOs9aWXgj5+DD+pgvGxKW0hzH"
    "TtBPU+2Xo9+nFVE89ZJ7SmVpFpellaOd9/vHuK/jtNOz5FhdnQ2PCUljfUpaH6LXSqOmECyQVrK8or1nOu0FLat+fxVd0z7g3f5K"
    "Rxf0HBjuzRmU5tE1SLjkWjx2XQhJR6uiRjQPYtAlSymdN9t/IbPD8zaLAUVfGk3iHR8eEF7SN4aJX0DiXGZ5dg2xb3JspzqZZ9QR"
    "OVRZV02QcZyYfHUiltRUnn+l5ALpYiyIivghyAHkpSfqJLhzFrxGwGvv2x7DqqPDQwmDFMHDhXVwEZXu8uowfpK23eul0rusaA8O"
    "5H4iRksGu7DLijvd6dTwvuJdr9QPHvB37KMj/GjJTWO6Y93xBnRlDgbCEa7wMeuK7HgP6VTr82iF7ryMFSEGBHjxnv+1pSnzqnnh"
    "fF1ZH3W4ggmb2jrfS/7Su/Q3UcHWrjMtInXGeM5e5sYNMLi1DmqwaNPQoEHlgbDolonRYmBqpXmz1VrhDgQXuJvp+Koq2NCj43hG"
    "dxzPyGGH7sDnjDTr2w16fCNHIB3EOEFyd4xXRMqXgyt4dBMNzbWu66r+Ji+nOAUbUYT5qbzkhOkLZL7CIk1XXHEy2cJCrcQV/TGc"
    "Rd60A3FIttmwWZ/DaKUxVWaZ3BJ0NHHk48u2XTbJ559frfTvzaCqLz7n9g9qPdNUeqI//39o97XFQh/cX9fbsdjOhfaDesLNEKkP"
    "BtW5pYOhVs5mDjCnNmg/Di3aDmHx7Yy/xY1PCS0FTdRKFYtCg9GphtGbdB8L1BhVBVrrRvGsHR2qU/7sTLQSrC729gTzXquK8iYB"
    "k3pSev9uh1iTIwakwhouDkFGVwTVPBuWyD5mT5TXbJ74np9flOxLRT2HKcqbMqWFWRQNHHzR13BmoT5KCU9YPS09r/iRUMwbpxal"
    "6XiB/0MmKa0qk9jFauj2uCp+D6q4Lh+ARDt2MykL9LgcunuXB+WTJ0+OaJTHED4S8P0J3gywvNnkYtNVWEvojPiWB0dJSdyLs5fw"
    "N27Wx0Ng4ue8uv3JFBd6cuo6c3B0NuzRGH35h7DNfYLCxBVSOWvmTo9GVfB3aDIp3DIqb1inXpcdtXy8rjF76ZtS5uxZqFv91nWU"
    "9/KLEkKYYipWnS9cU88xd2gpccMhtP/e9SrowO7JxtCrQ+h1n4EeGHJ/vWDXgxvWS3YB4X2/arX1o1bKKpk9VbppY4MQJBRTKEEN"
    "VsWUdpdT04fMD3l8NMFrbFESnelntSaiGLfYWX1wlFyXqvT2mlEZ2OMrnLQuky81AmP9YAVeWYZE/Gu8tyOx9M97DPaQdS/giCvA"
    "o3A4Vjx2H7C7sbUg2PflaXE2jPJB4SylMrn+zuOkR8lwJFVg7I8JfKg0TdtZmifG+C43hC6hbWg6GV0jHZ8R1Va3lmpjQD34s2TW"
    "Pex6WtN+Dm3kD4f6ceEcn1A3X5g1xvWvwzEoT3igYCQwfF4+fuGG9ty5x9Ppi/L0eXk2DAxlA8vYh97W8xFRIVFo+vlwG2IZMa/5"
    "HoygxynvjMyNRvM9jSBAgAZL++k09KadnPegMag5VCi2gwSrzr5QvXIvpQqobm5eevJnKZ5ysbvYrZTb6RlBGngE5AW29bw1rRXV"
    "Nabsugw2wnUwZbQTrjFloU3xo8Didn8S+fSnBvE/O/pncvSln8kvO7bIDyEns+Ph7fg3utH5fisHgfuGToBXjAMNyleRy9ps/P7o"
    "93kKZPY+mKLf7J4SPwUo/oM7IT6A4qeyYlgEUmw04vP1FSEDrijA1h+Z0P1QGjq31zJ5W3ZF9HUqSoFEEdWDEZ3ar/Po4MjqG/7E"
    "uDhPP+am96piGKlSLZ91ZlBmy5Ud6if5UB8cxL/nBI8/4cxRro0jRxhWW38vOWLfVPQ7Mb9T/g3uXkq5QYUlFZTM2L3tzoBmFeXF"
    "LAMh5q6Bm7qzYXdTl+Gmxiyf5kQiNGqStvCVqc+G0CQDQoGyabo2NE2Sq5W45k3yrTicg0njFRS8lKEF19QmlSvKps0h07BuXytV"
    "zacsyk28mjzRd4tqWswKXTdEycV3Uctfl3t6W6wYDjntuXcvPCa+YMT9DDx3BoXEp/DY0W10DJvyQ7HnG80pv2nZ142pqPTuO7km"
    "53HYGSCaj4a+bVePRSKsIdYq25qzp7bXS1gjXPKiQ3h2SzWhpZo8dtA0sRtynuank7Nhlc0HdkrTilKMXLvT037fFwrOymieNtF6"
    "q4jc3lkVr8Y8R29wEhMTHTG5SWT+itbhEZGaAz2njwvVGnozpE2+88j4l9zO9y85aO6rYqobOhfxZlwVuUeXP/ReJ4KvdvT4a6gx"
    "w4llGzoG2BMSpr/lkXVc+bqwAPS6yF4XtMkMv2CbSHD/bvwZ8c7abOrBhEgG4U8CFgPaD7tpQTW7I7Kam2LEaJz2WiYJuw13i1a/"
    "13mxdcqkcAfewsJONBnQOPMvoIkZi35bWq0twM746qCZ3Ixj9WvJUgualW/LQG/sl+4F1Y+MUpj1ms1pByfj5racjLfhtV+5o2n2"
    "o+NJ/Z3fv5dxSvUTkXXOIctcCRgWrEUmHjrpByr/42UFC64Zr13FwDRJ2bc69c3pZEJCNcOeG12DsdWGbxSc5/Zub2o/EBf63tSD"
    "xSPw92AkKHgUIQs9CS21JCAcrnjqU3dJxPz3UkQJKLQANcL9425nq0DGxIawRNAt1SzHV/0+LIWbpS4bWBvwYHlUEMcB3YcfW6/6"
    "bQaPm8x/EOJdDbxsmOsvQy8cdOQvwveHaDNiCmUJ0lFxb2jLctcvUyOdXnn9mIrKz7KZIPTLOJkCAmnDXQb3tWVXcd+4NgBXXYiD"
    "bngMM6Zt48GY3mtWwmF5bU1AnxgGr4ZOaD5kEM/hOVR8uTL/j9tD6/pUV+aqoUkJ1go6feTzONDKr6LOTbo1d7Ssugm6MHCelp1Q"
    "D4fG3UckoWXxapjCpbQ+cxd8Zu+1decmoaydMffoirW26loIRNgBvNdzjcAWqpBEXhfjO3kK8sQ+s3tjmCsGxSCR4DJ4MAWqOogx"
    "cPLh6xdzDbiAO3JBNHIKdzJVE370Q95e/vC9yQptiXa+75RTk3o34ANTZJWdnAuwt22GOxIW6yQlHTZ1ukZ8j2Rsp2GswkmB73iC"
    "oIlumtBQSAgTNRe0spgkK7WcJFO1PJ8kM1Ula+qkpq+X6o+Vrm9PNG5WqzpZKDkq3hNuTi7Ny3G1QP+TCyUo+jXkTqPtNp2rq7So"
    "2TlDtYQy1/SW+lpMji+L+ZRKJrdbOsTPPQqgPd1c5kv9kjZZ/+grCJrhxl9Ki6q17Xu8VTfQ+wqmi5rStilcWrWE/nWbTlwypM95"
    "uuA9oy7VUtyKV4wsri6ghQuT96yS14QzFrREiznlNTVrgkeVS2MfN8WgaI5fsK+bCcFja+b9PbfdsG76HenWZiWOWb0P+w1XASxW"
    "ymNaMVGAgG3ySeCk317LtHXg6Tg2Kd5pcTARlqoaRSAvoLk5POfpplO2nFxWtW2MiKcbuR5say94JuzaQk1rKG6OmTJ2zjn0PL1k"
    "Zwt0PpnaJGEosmUmL9USKrOMjjwkEMcN/8yErqdFefGsxsfx+sTrqG6vaEbPI1GuRw9b9DBWN5FQj2tuHUNybhlMB+y46Bh0s4T+"
    "rOL1KnC7Fk5X2G5roOYEzvMdDPHbUE4uW8JlqkuX9tT2IXxVFx3IHKUXWUkb65x+6+TSajkxyG02BIFLD4GSY8Bts2mQuQuDt1nE"
    "Xj26W0vdqpHdLDFxC7zmmMJkstmwmTnln7vtRLCmruKLzCwQ8I55MCmEhlhCZF+MzxV5CdLjZFVHgmbm6sjfHkTtfoUx1RjpnRaR"
    "bkFs4iCGdi6zyn7yFbdjiKy5opEJaXJBSAM5S9rg3AMGnivcD8GR/pX1fb1eLYiNIkwnqUlBBYSwXjsUROSVRT7EVAlcEakVwEQy"
    "V+FSExqVV6BS9Bu3y0SeAABmuDEDMbYEwISgeQm28G7YJBoOqCWa0yYjEGbfGEU0iVUPHy1pKQkcKvhE6x60zS4vSgQ6/AYPa9qN"
    "GP5C9XrFLtBgkngyVrW6vJ1CGTuZ1qGuSG1nzx8RNX1Ds0eI9WG8huRXQiIFk0S0dTeBsb3yiWafcGq5s3tEN1/PaS3MAjTKL9DE"
    "L9DczPgKMz5N0ZOHmN0pmq+k8l5bG+fxuEkg4oDWZYUdNdmfwnk4hbQCNHs89IfxkKtsdmj1ad05YDFD7M2mOJ8TjqPuB4djs3Os"
    "TpSZzHl4vq5oOYjK9uoaIqYQhBc4HBR3bPUAvNP7W/Yq/EhSB8SeYyLG9vi5x0FB7slMjuMutqs9i7//of1kvYPrQN2P5st8BwcS"
    "VEbtzkKKJ+NtnVZRHfK2xv+BQ+HTqGIlNNH0t6bNW+EJ2uBYt8iB9sNlSGhg2RcyUZN0wd3bbBaDWVE3LcP6sN2hM6LLLFqaIy9a"
    "oMJu5+nzmtJbtSKk0sjBu8jkdg3OZ1zfuef/tgrY0kwwRShFe9GOMTZn3aVBZiCUd3tqurlzUO00xv0IQp/kwaKYc58J7Vmdzmu/"
    "v5cd2p5Ir/bG3RmsWq8jxI6WM9YM0nMWiplKRVso3OrF3n4GrMIUZhh3QPYIIEyEx9O2rYvzFaG/MYDw4Oqgui7hR6UEnwXKzvgd"
    "lI01RM861ziLYCMGFIuHUJmyUrxG7Z7dnGwnLj8t67O0YkWsOsrpuIG4kbCJZvOYSkL/BNzJXOdX+vicKr4IUmnb6xqpgd2+NyRY"
    "F40J34XQTkXzPdUBjMEv5urTvM8l6wOQSJMYNQLHen9dR5EQ0a5GeJqL1bdBhq9Q8kRj86pOT1+avilWeDlTtzVklIStTFy0fLmE"
    "qcwzhPTLS7WEFlqDXtuUqpSgYi8w3OSKTtcyeHw6o8fdrGMwQnPizSRNvscEaEkIHvn73aw7v38qHZWvwmfUsJ8Z1rFV546hepY3"
    "+j2Rpk0hkerkeLmtocW5wi5cN/OqbZJ2azcM5GIEnyNv/BF5PVb2bAH1/37/TR25t4j1UcQpl70Wym7omIa5VbM6f19rnX0TxYG4"
    "q5eHTgErY/oia9VsU7YPrgcOkKzI6z1BsPUl8IKfUddkP3ueXtfRhOjCGlKACd8J0IZ9TrTHc2TMrTTTdbDfpwrdm9DbRIeFX/Ze"
    "5dGKsGK//zEsajcBtbiyLdLXz/HKLiwQ4m/VHhTgnYOuOHNyP06IeQgROTBx3FKnzJHCnebv1bm7+hEdLaM35q9GA+FWpzyM30Rg"
    "D+9rEPuUSmRIjLKDTKHi7oV9Iq7EiISVzDcPsCgPaIzdAWbsczy/NUNxHLIA0zF42BVN1anxObBi76VnKc3a6SXhLO43gEtejdzc"
    "9GguVevpbp+6GWbwUfzvvtsm7pHngNbeqn46/yeh3ulNHZgynB6eDYP4Uk8Ch+IS1pNVOIKVXxPudrSEFRsBiZ3U6XlwmB37w2y9"
    "gzhBIhKqlwBBXHUYpIfOsDviHSrRx5Li0MgJr5Cu6859ytrgykLxpswDZFkBBLuYsnGIctLFk/N9NLnawZIzhySXXRy52EeRl7sY"
    "8sIjyNEufrwDPRppjfVywRCnbgCLHCXnxEmvCB+ci4rM/7IfqOMduVZ7enQ2PDGxR0WsaTywQaYncPA4heMRqPAFKZywVdfmYOrM"
    "qzr3U2rtYeu0YSRX+hPRqOTU6QXx00LwWtYfO4UILvxwlAihGm5Oz8+MG4hXORtwet9Beo7CQwkhZ9VveF9ruXuSAlsI8qjjJ7Rp"
    "ocjB/uqkl/QpGoDCTIjU63RCRwKtf7r65ABGmw0KXW02KHe72aw6wxFbqd7RsD29IAwAIRLEUQ3QJM19VtH0oTPqurOr+/3uOxRw"
    "uQJ7xcb9m6acGCpWEqtdZ8c8QjU9g24zx7xEFa2/ZuwADytyoB7M+oXMuio7RIrD83SknkQz7rFZGB4akFtJQyMCP8r5XhdKnVGZ"
    "XdIO4OG1IQK8OS3ORDnJoDQkmDERKYiiO2PiL4iFp6EtMbSKhlZhaJN5VToLnSINMIC3RNs9jK6DFEy0f0ONxd0Y/zpIzsIXGw6u"
    "DD7uoO5/t7L0lVfrvQ4istVG0+n7OtQzTz/kor9keW5RMwiulV/YD3udL2tm9YFlJYiyfA0qx7/Bckz8UVeLJc1s2Xr9dpdkyYZh"
    "V0zTeilAafxaGzVcsPX2xs8cNG3/i4e4eiktBea6WXqaLGAnntfu5jWUTn/FQ3F9XcMnq6UV09Z5fd/vOtVX1+ZAi4VwglgWiNKy"
    "3x0p+MNHQVxOc8UV6GDCAXrRfMPSGtovWdmVqhIRKVqS8gohmgxoYOHXNEuVN8cSGLwzElvOZwMCmuZlPp8jHuWnCtv8cFRhUSUQ"
    "QZvxJW3GEBDscD8UofAfe7HkzvNU+fV5UzubEov0T+FU5fCvdGyNmiwr2DaEQETLqAJWsqHmyviBeeJkUyRPKkFdlet+RgWWuCm1"
    "60WE/IMHzKcaz6XUxSq8xmhilhnAC64na/gGGneDje1NQvutUmv0qYEaB/A+kUddMVUdiqlqCQ1m+pIePLwjwObH2nmC3ttqH+vo"
    "DpAVlXw3XnvQdRat399fLmeY+rHm6HdCIbq6OnR8gESedm7S2T6liYQn0wP8bBEgmZmwRG87Bq9PPVfNOgpOBzbS+7rMg2L6ttaz"
    "4mazGV+N4wfjg/EDXOg2hCjMw9HZgwdJGBL1d548zkxPdwo/pMKoRB2qw7NAvzWUqbioF1FUpneqyD83Yf6M4SpbOw7CaNAiuHld"
    "323N/rY2KuG5qqwCsqie612HGlK036f8Ms6gJJ1AKosvnegIq/WqZpUleKTOA8T0z6OHuMMxCmM5btvfiYLyFOl7UORT+n3fy7ug"
    "rUPAhE1+mc2qKPgkTnLWmUmrjO9DG7UuiCKukyUI/IXosNdqlM4GtNDsvT0zj+ttIk/qinIZmE5aRM29BTt9hQjxV1y+SBABkxZx"
    "pICuV9EtaN0bFxkcRvGcaxQ/Fz3evf0+PaRLnv+XQPHqIlrE8eh0cSan5jm90txf2QR/VVKWKOlMlm6iBeHKjzEbFhl7V+ZHKJHS"
    "RgSGH00VHCfnEndEtyVRKzN19FCdztXoLHACjkjfS4jZqZmlUGB0+lgqxrLMBCzuhj87x5XU1enyLBnhzw29bjY9ajZbGvUo6QRf"
    "ZcVTduA1YQcggXkK4fXSKy807ENG0F0QKSBGA+lpc6bQJk8PvSOxMwIqQNOytNOytJ4zd+YExwRX3WYRVzzvVAvBLcD/jpp2Z3ce"
    "yxXoPO5cxBKp+Tq4rNkOW+iDHBwhtXuFWptj8GXN97NRR+v5ZcAOv3YXQxJexN0KhQ3F2yVRbwS+f6x0076azonJk9NWccaEWbYw"
    "fch+NmqJ5qo7m/b7Kp/qWn1vNCpMVtF8p/Xy6Zwoh0Aj2KCyZzU7Oxur0IPEn53M6U7uM0Mep1Z7rRYNo+kE7lu8xkjpbUE4dETR"
    "PBdXDHkQCyMw3HAWfLJA39TsUhP3SJ48kqImBiNfNEpC/D1fy4paGWue4RiDZAV0PCjd1GYHq/Wh3lWd/EZuImsjyKPX8WoxVhjV"
    "JGL/uwXr0+TObDmI3+XnBWYjR6HBYMFao1CXh04e7GAhw6ZJ05eYNDZroon7zfrWLKDOU6LUecl3sDpkRqxrzdyrxmbFwDonzuOk"
    "sPruVITPmJ8YJCKzalDmrYybzGY53my462I9mD4x7o1xI6Z+rtOfaA7OF+NYfS3PePzOJK/o+Q95xuO3NhllfjXpeP5FnqmtWP0m"
    "z3V7QS8/2pdJKFG/L3Qg4AsroCfGCzU7rijSsTs14OmK3qdFrZkybsa+kt87tEdBJE2h2GUKnF6JqLwsdvQCy2mnHz8E5vSss+Vq"
    "OUIdiSbMF/hKrYugPBVt2emry8bHon15aOBDVvpDudn8krPyo0XUBe9do6mR6sJugCUBBdNjYuwh4arFLV2p2ZsXHnMd8Vvs2SGj"
    "TZsXbJpA3eYrUChvUEpAT0myJW1yImSzMsmDLZMXXZfH6ARtC2r4lNvkJ9eBs2D4r3f2GsE2DnVYHFXOW2e12Vw467oyJSBlO2ie"
    "L3HxCzRPb78Yt8jsIYN291QMrIt0x8TXcQ4lOwF2nEP5uBpChb84Lel0ieqsyUxgBkqIOUoCPyX4660AoeuCZMcJBV6mS/ZRORam"
    "WRxWEs57RfMqwWRoZh4fxmwyyAeg62unk9QzHfaMzbf2mnftX1m333ovdENsGhjM6mqB/a3FgQfTazsVBmdymXaj0Q9tP8u9Oa15"
    "Tr2NEs1p7TkyMVOCOytq8rQ64zsBbrA+cybJPB1ekTdi91cFDC0d4FQG5LqT1LqVtC3W0EBkygVaWHHXFKsOTbH0KVA5MyBn7DN5"
    "MCuNwI3hubZZmIPM4kVzrNUI/8ZJgVewiKdLPohVu01Q6i5t/bddH984IbIMHhc+EGtA+ORD6TS/iVh3bzjN7DOVc2JLS6GWAV/L"
    "KsOlMJs5HFbTruguqZXPO5k+7MQ+MxKTz1jnAxMAKuwVHTPvopeim3P6jHD4vGIPcLj6jWiHqyI7eJh89WW8tXx4ezakfVsNRhOo"
    "N7GNxpG9rPLGH6/MSTdngxHBhPRZU0QVO4klVh7dJQy12fB9Gr0M5yn6wiODN4DeiEjOrEnGo/vrdkt8X9SDV8ZsPJqdj4nZg1QM"
    "dwAZQoPi0C3Y2RJuqLOvvkxgo+PMiO82UJl4AxUXstJYtOyO8dAuN/owHxizG9gSDDBnJ/JOvKbLIw6zGVOv5h48mvAI8V4kei9z"
    "RiA9z7s/z6Hr6uUuvaboSF5io9Lg654UHd+b2+GOATixjf3+56dPD347+3wAEw0oUI6rMmHD3qSCUcFZCsNtt2HFx07B5GZWQlEB"
    "bJ2Ok3nhyDFRcFWrIt11bCq8z/p+wn5d7+s5PxjDAWIG70NpQNLwpO7LtS0niLbI/bxta5PCj+q+XORyCj+q+2ANJYGZxPvSLaSE"
    "vaRyVeVT8UJpl1XTyrcT9HBRmDc8qfvVEhPLlZ9j4dR9mtKJMaWRgjNLE+Ne0dwnEljeh9rD+2LyUUrBUPVpKeJqbYwX1H3W2UeB"
    "+zYLyu3TIjWYnL3USJhL+I5iWcMJ2F9WtgXlPCvEx+p6lOitsYsq7/If3mNvR+tJe5OYS3FmoZNC8Rrk5sa8UvkE+sfHCKoN43MC"
    "v2SiPP0AswURaZ4enoG8vO+MERqDnL2dTdz11HfvKHE2H1SUkx4mXn3DJH1pk2qX9IVNqijJHY3TouvhFefpkeK6bZFcZnAV5bsF"
    "H6o8LLiKqt0SX6gqLFHbqurdgl+q2hW8RChNTjUWTtN0hR4Rg7/kkyv0kD4W8B6zU1UL4OLoFvoulmaKZumEIGDSND9UsIrgONez"
    "dMbnuvXiMvw7XYSubzq3MjVxxeSjd6gVcdf+wyXmmn2WGuiyF6YMMUUIRbkCYFUADfMxrQ2mPIswyymzW0lhu1dwTuFzVk7rm+Xr"
    "4geFQAvnngSMP4oLdrh3lESV+0786VLvpEs67FLZgeSaO1iEgOxBnoG82W7VxNiXeclffToBwSsdnziQl/03ob7SOEt+AADJb2F+"
    "V/Yh/+SEIx+maLurO6dmY3haDcKr3O6YIPGNuKEI4LFT/JCOY+9ESj4wHkgYFyeESQbBvNBRzsGvrUvzO5oLdQGW4eFlLoNNbCIj"
    "YmNewVw1EebvSnwXHdaihziabUZ/20Q80MOXWqatIJ7OFSZ0uFH8RfA21uGCB43AT1XhJTKCpMtUO0sc0YvDJwgoLdfOx3w69ftX"
    "VGcniaie8TkYRAflBNgmuiLByUK3l9W0IbQoiHuijH1bMldFiYMPfqq4pmkyU4FtZrJU1oJ0oUJzzOTCGZSOlJOdJLe09P7t3Hzy"
    "nI7surpNbmwVcvOanFBpzqGyx2plHXAk14oOvqmuE63N03s4L6Oc1iewJztKeq/Y08VxvqTFofcSu6m+0jXk7hrDrWl+bpZVQ4eG"
    "pvFe6rpgBcAmybXyHDvREcrz60mjTeC1JpnobdoafaNREa3gk4wphMbfk4BSaexyshb0JTvBZ7Y2bc2Fr1yw5LZcbr0wl/HwSooL"
    "RZH+zDEaWNTKfleqbkuVraECX0zFI3b+Z6wNpS3c2lICdhsS6SfI4LM06UkfLyXGJEo1rhSV2cbDu+Il3UaQNKy186AD+5/w9gDv"
    "7JqRNlZutjGa0+411Vse3KQ7rEl8W0QTDKlg4VggDtXpJT1mczNjRMgN9yMCuNuHluia7yCfYp8WsIjkXTPDRukIUuYmNNhUZi74"
    "Hv4T7aLFCbzSRt1VpE9/rtWSqGQdfV3D7IcevqvVBT/8UasRP7yr1S0//Fmrc364j0jX/PRjrVp5+q1W7/nh21qd8MOvtbrmh19q"
    "gnkcqoVhqAvd8VgBIxGB7ykRa0Q9F10/S3cvIYSJa7tILHTBCrXyjJvTcHW3Lsxmt6mtZlGnbEk6+ZhJta8a7su15QNhxhhsvTRH"
    "dCSxj/NbMK3YkagxrrNbMW0gZ6FUvhgLnPNZsVWN9WN1e52+L1gp2Wt3MQdhpcEgaIphkV4xB2H4yjF7i/6jjGoWSOCevLa39HzK"
    "h1nyFiv2Epp9am7Lv7s9iu72KPz2SCAzSENPTFeFPUnPy8icYsZfn3W5Yyj0ONlJ2DEjuC12xcv1vs0ncg10iPpRKP9qBcPhFua3"
    "kukiR92yTytO1G6/DPekQtM9h2BBpwKhD6y9tLUqxYjNo8NS1BObhh7Vtkcc2iv0vBUct8KeqvWiuClKuH434UPgN7V1yYUybJSQ"
    "YrlZxGQtyT/o+kKftDBguSCaCNFt0vAGWOFekZX/YjXxsbQmaZP0CmejCrPpXk2pBA8TiFt8VhHOzg0hRtqylTFRw1uLO1Ql50Yu"
    "eoOwCAiCdN0U3lnUkTHDtGOzQ85xtuX9Ppcl0pcvGIqw9ZZbl4rQuveHg83VxuxWibY+u2YX9DCO7ZY7KU4LiHUhUC2I14CmE8Qe"
    "eFAtFKMS/PUCKVayJO6QyZjjwhC7b6jDxNnygyVnnheeyKHnkCBKXhSOoHlRdCiaF4UjaVyOoWno3RI1LsvSLr6sIV4owVMv+LIM"
    "qvU0EBfrvHbJlRfFLrnyogiJEhpYQJTQm5BwHwtHw9EcGSLuugho3uOuPJwI1szFSvEx5ni3ZjqMCSduu1TouSDIaONt0obE8XW3"
    "nedFxChYvRfC1+t7FUYlxDupa0NZj5Ewh8JT2tqEA88YbXvj7X3R5Ysd0X8WOlE6PbOEOas6nIXuyJ7vfni3IAhlws/e7H4WsAGd"
    "piGM5UimCGhzd92eS8iyNbylhn5wCqcV1rOam/daiXXV9R1TfkKEpeOuLK2NWYyNCWM3hxB4e5mZV3EpHIhAy1jkZBb7Fc3rHND4"
    "Pr8gNEInHrWwYI8xxKrscooJYbS70SVldBwGGrn/dV6XO0nYDQW9vzFCrTUsCAWNnZ6Fe4WqDPYKWDDrxuOuuekg99ATAGOc/WTG"
    "P3vJcov5O6uCudu5Lny4bccx3NlW6NIGTxGROPS8LaHUuxITcFPUXLpiRXAvZRom6FIVVNAm4A/nKd+UpevRqpgmv0MxbOSmhU63"
    "keDQWrHjlJxIlVqW1DpSoXUcOb8/nGPcPycXFUcQkrX3eKMwkgEWs9hc2t5btWr24v3mxhwSXqzAbIASpLZocFmUDyQOjnKJ0Vy+"
    "BvPCNJ0v4rIgmRYQCO81BwIUnpJBky7Vesabbz3I7GBImNE7aBIyeI4r605iAGP7n3vwCz7vJG7l9InEaHot1jFr67hnNNFsPrDZ"
    "PItCLd9VQFekBVus9A6zxlhw8+sRhwu1kV6qfh9OHFYKAWXxAwtt9k01H3goSHOVw2/sSo+o/tEonatZFa0C5SfaalVpjjzMdeWc"
    "ZNsDj4ACVw1Eklao24KROvoKKyaW00GTgZ2HTwz7ELtt270mdz55zMxuVb0qfy7aSzMtgXpLMXxdpPNhx/myd/hFeYgoZqd2Ljv4"
    "dbHjx+xtIepjxi0O7UG2vMIehP5DlRb826QvmXDC7K7KKIJszNzIzeEeQE1tQ7+UUei15DQ/GzYAaWb751RyAm9MsTKhg90JDd9j"
    "lJSJ0g5B1NwEZJJ+IZxsw9mSKCrOPaq6IfCDA7qVSAF5Y67c1TsjlhlhDrnVECnmMu31ohluO3FazDab3PxW/IuejgkehFy6vy63"
    "Y8kOE/O7EitJJOJxyZJDzaMlYhdYNRqvgho5qIr0FSCtOcwKrpEwoiltadwimAsGM0rWBYtpumGU3SBcnAuGunf5HPqDtteMNoqd"
    "hZbHD12ougcPsgaSvonEousdbZO1PB1SO4RLGHpeFlZXrxUnXgTk7JxrTN+6lAORdIJtw+sPzoGaPh3jntAljFlZgdJYWeGO9GI3"
    "3cPtK4FbiSTIWnaBb9tw7SFjDNaeOkrAXfO1ORtwN9hcbmnGHOq533/JdxdGuP0/tJ4cphiRJRbsca62LKlxJYQM2Nfg4nQgighc"
    "LudyCEBtbmBxip1O0gq7ioZpn/Eanw17c7ggwD4xGYVkED5nO6A5EWlfqdwaDVKhB+M3hIbGZ8YvB9NQDG2YBvcECtTrjptECLHN"
    "RIVpwJ7sSU2aMv4si7t1ZN8Vex7Nyuz7ImkHno5A5PTARUPh759cnFrRjpFewNkcnbATEw2g551H1859S5mahmFbBLUFxvmNXBJt"
    "h+A2W3siOjdJNsFF+8JxbPhD8atgXpAuZSH22ftq67VzepOMeX1jb20clcVGmh8h2FyWh/wtBJlC8STobQ7GNvy8IpQbKgLui+Rz"
    "kN+4Z4HmnsDnQwRO4/3HsJC1NP21Xs5zyvscSfc/5wsrjpV6eng2aKvvq2uYwhFiiR+07g6Hr0NovbREzpXYqqHmoRUurPlOplXG"
    "L7Zi8QtRXte0lzgETGI4WkvMsnEA3ww3Su6MJ0xpJnMrBF+ZByE9nc8Puf9chldHC74suuzKuC+gpjxK2S0nAkrwsSie373Os5Wx"
    "FptNjVhzw6v0mzxauZh2aqpmagF/JzHCSky2Tj6j01YKe9vKTEcztbaDsYOTQeFihXLFpQHVZLwpZJPkG7gc2Rq1B1pZp+yQHqob"
    "FuXCEfBV+ix6bvw0nKdX2Ae3/f5FL3X7THdUSm7pPA1seLbp+VB7wO//D3ARYJn1GSocOLfpT0V0y8EPz2GMdK5ulYSHc1ozJbt7"
    "BNEjBYwdF0tOzjkvlZ9MfiwDKt/B5pp/CY16YxW2Oqnr6Dyw2TknUDvvlMIEnCtayxE9BeqihZinHFoLgL/w9uxEoS2jxpc5VJLE"
    "gtkZTLD7RGt/Rbvn6qCYjY3WqEGM8LO9DU0BO5oX3xTeodSuLFbu+TnmD52O/NK0t3MclTlwOs0r1MUJ1cWQgLKym+f+1U/FjqHn"
    "vr5IxRxUbXbv/+IGtmUN11q0RAKW1yPsn4vAL97ackzO5isQykBkptXa3sIG3nucVQyc2xONCutNIG6z2VkR3rh2DQ2gvKqD+MGY"
    "PDG+qSf9o8OHX3ayJ4G1WZ19XURwET9HaLlKsh9531nG8w648ebfgkTpQOK7IhIjeULjhGfn/mqdaZ5g0SPCF3yp36MR9ZrBfSIc"
    "YD2S9Q7Zm2kFfFxnvWqz6fbUVBfEZvu66LolDDexxPe2inK99G6lMT9NXX/d9R3uumvIInGGrph232xozMAwuRlz6cPr0pj3e/vd"
    "Tm/lYkHU/EI9CQFsBEjn6BK4Mui9gE/zIk7YP0ngArWI1nJqaOPFh44Ra4sHL3y1cb4ehjCw9n6Cz01hVj4wzx3DPDFKDUo6jSai"
    "+ehPrTi6ecmGwnB7ZxTWJc8rxAvFJNbxEsLhrkZc3cYNzLcFqJdfxf6jK5D5tojVL4wyvLlSN3g21fpt4Tfrb3uC7Xtce57+WkTx"
    "0JC0z+UOp7nT0v6+VAFlR783GH8MwgMaQak5Gfp6BZQEDIlmGyGyrs6K5GtEdE6MaYOcaUWSK6Mck+aBv9Xu5YvBI4U5/XNDOqw9"
    "LuGLBTjP5KDRIES7XSQ8IxQhfOVWTw6Z6WN/XYxEqn5g3CmLcidikIAu+379rb7sLALR1UFouIBwLvutyXbFZSfcNvSXqAwc/+eU"
    "gdOWftIpunzYMbcpcfwOeYJ1HhHZQFM0FYV2g3I+UYnBSOtgPZlPsMb1tTfRlDt6KMWu2OMge2Egmo72OuqGcgysaJA+yUTnNz9z"
    "RDn0e2r/Knf7uetubjWXtbjAM2IOFJEQpPTljr5AHrfSJsvGzAc57mJlZHMJ6mv1qxqjXxX4ci1sbBbnC3wPOKCbriTSSdyBc1G6"
    "00zSdhaRsAHsSabDXBTQpqLCHzMe71VevjaNs/p0epbOk2hiDmx+24cTKPTLLqIhId43a+bLfpqji4d8pV4F8bBr6MxPEAume3JV"
    "eycX8aUcvvG04cXAHVajChh40VJAramBl2srTwmczOZdlWerJiz6ZlWv44kSalLuwtiaOdQuOoEtVtmLY4nVbigq6/UIBo4DaDe+"
    "zOGS7ZaloXGABizGAolR8JoJnNSpU/pbO6e6BdExnJ6a+xvxo0+MUmT3TA2dx8GE46TAQ2jDeHXJssVtRbhN6N+ezoBIk+r06IxF"
    "z/BRS0QgVkobmgzxZjwJXIsL3fxu5rfM2TFH4ZBznhYZcSv1wMvWiZnNA+a3skRNZRSyrUhqDrw+g6x7uc/4tkxmLlPREj2lxSQm"
    "UhrH/m9YvAb7U+MSWVz/D1kZe5cNrncZ2rbDBrd/kw1uGZJ7E5rVpR2TsLK5j15eijHAJN4xtJ7suVREuENWiaHFzvm+PZqz/YW/"
    "cN9TovEoVea2Bmtsq2P1mjqdY+tN+RoClxGZMK7lNjE3Eiyb4FvynJ3JpEJ+Tgnq4k/EGXnwwIlgofSE8It8N92yzv7QavgaT15j"
    "OHKkSg0ZgRwxhR+z71HgfR5gTrVICCzW/A8qoB1/eJbmqiaoTSsV5WDM62CXxm7dWxNfZZGeztXM0WjddVnEahHYTOWhwnugQdnT"
    "2oZVKnJWMGe95bGYOI1HxIPbZ0MPj1XOBQOdjW/yODkF1xyfqSoPHHEwi+BjXbTGU8vHyBp75LSY8hz6z5bIE0eq3qom3/HkxFaQ"
    "0CbcVYqBzIlZrg76LxwKxMTHrIZS5QitjgsJC3RFFz1SrwgdcVkOJMmi0XyHU0PXQTexSMAiSi4PJ9Nht3cuLRHQrlcwpypmMAT/"
    "bKujVncNlusXSpDFekL0eHHHFw89jzQa6iya55H1DMqhqQmIRmN7kDehbS20aXOJBa2m3LaPI2zI98KIPJhLrFj8JtqDxZ1dKLkL"
    "NWEStv4A5CdzOcWgf0PvpeWraGmFM4ENivEEBhFfLkilSdc2+PvR1iDVHXoDkwiQ50sUc+EY0B2EaPP0fR4ozoabYJF31K/waggP"
    "2qSwCR7iMunDTy9GI4OQrfvWyrjFtSwyziC4VWV63Hgm33FLuuP2ewo5F+fM8GS+4YRl6PR0oUJ/qJcoa+xbkgviYaQ/kJYVE+Np"
    "JBlhna4EjKw3R1zz4KeSHxcseCLvRJ712j3Htsaqnd1lW/Gx+KQzgbGL9IR9QfPNYS66PMpa2reBT400PXgoRCyUf3faceV30gmC"
    "cBztp+4m4ToWwk82DtutXAJ47KdLhNxP1GSJbTlEILCcYcWc3G0GHSNjU7EyNhUv8uTWzrlx2yo2E8/z5PzOjDd5orPsho2vQdSF"
    "eS9hBWQ+CjzPmyJ2W8z6R9n1HcUo46usuauCJKKsLzebGfvIgbvB0NF9p6y6pt0xtdf4efa2jqbK6EfOqBDMYVWvJc7A7jybab+B"
    "xwouLLAnCGirbtMwYHngJB2OVom/Jg7Cm1eJc6jAZtI7Mfel2Mv2xEEI4rQGVRDqPu80qa2zGGlvGrS32UB+zqjKNbQ1nivs5xJ0"
    "xrpvPWM38R1/+3DvG5Rgf/QR3DFr64653XbitXsze9wDDuOCIwwT3WvcwWsinqvIRGeHZ7idytyRtFtRKRU1YrpbDiF7giu4/bAG"
    "7qw2hm58E+98qvtkuFAf73hTt+vX6mi31nDlMCmAEI1r9ebDSh+/gBO7OWtosBifhS+jc31RlG9Zbg49WcsG2xAG9t5bChP9aori"
    "iG51d2iNWtm5gcTfyCYWwVa+VF5umVxAF6JhDMrEIXc5nRtbQKpv0e8vBgXHRLjsP8qW2BGBN65L9jbMzpwcQEwF+tGfS3GFx71S"
    "o37/axfwhg5oo95H0/ketcJflCB6Kk4gsAgMJ3H2LWJ2KiA3sJaIw7Xx1Pp3X7AqPXaPKYWvpIRJMOWMyi51LJpxmOEPOPefeR1D"
    "qvfrPJqJCupuvzuRr5jgukpHRD2pi3h4lV0MQg+D0zi5oL5eDJwLQnjSOb3OcRcJeJ8K1QJLK55q0xfrxW+zudpsRiCDc9E94Oh1"
    "Qe/UVb9/MdCmsb05dmGzHBBtEfNnq94HYGN2AoHXhdAh9V9ZOKNMzQ72um4FAkkmLuwIsRzn3oEZZJbWNZh4FigD91984jrWQ8i9"
    "4XvuYeugou0YuyLomZhXYhuU+o4dnh6GlOg8nQznXmw+t/wZMaqn87O0yX4iYKWnOPnGPAyvhCGfdCuWIAGpFdyYRKsyIoJYRoeB"
    "BHCldoOaTGXn0cFaDlcbdiHinIN9ZSIbBRf7lxI5V14uhuLM/QJUL4IyRBfpZReMRW9D4PgCdwGAlRlDB3v8UDux2ZSr7lCiCfT2"
    "qA4OgLNDPjiB/tTHGIxW6aEIraaG0okIhZSlrr95/8P3/f6lf7GxvhYDKAAZ8ECJ4NWg2n5/Gc3FODEr9B2hLKbK4RyQ2Koiwp9q"
    "1rxO8w5OknyeudUTuahZQdqaQ5tnoS45vIo30Ow/xM7k+y4a6aU8Aa9Qf+QWTGo3Oah8hfiQXEAuEBD6HA9URn65zCPPQvx/uOkh"
    "SneBW4sqvQS7xxFqCnMf5yzy0AcwfhUjxu12hdjzOqQjyoCOwBSXAR2BKejRUB3B052hKIQ7gSSgrFmAry7+AgKNqjbb0uP/7h4O"
    "d29DU9F4zwxNuHsbiFtb/KzSCW28zeYkh8/8aYr4eRNnyU4s6KucPVNvNpPQeeL/PoqzBdG1SUlbHoRgcIQZKh9xP8I9b3EmTaBo"
    "6eCp3ZXP9lg4C2k+J9S8IDxGrJ/wKaCRO5/VnxLrVuxQAqwjO0KAOLrfb8NDUSpveLVpSv0xWEueOwbNCVi7kxBqgnukBKbKEhOG"
    "DBX6ZcVe8WdBPJ3M0n4mL8B9yz3ct1AhJk8uwVxcsqrLJJvYu/ZLoi4cpZVFOCqZNKygfYAHyLQDMvYUvlRmQc/jZPnkkGCayH/a"
    "v3+TszIaCymRBcbLenQntlmYKFMcVkJcdPQMMitoUSB3da7q+v0wss7CxpYJ+wqFwE/QqN1jL23clLRdN3tZAYPTgbVUMIQpTIOT"
    "eZdMpZSVdGLCznfv2Hay5QLLrvRXIxHmY5/9trLaGJoU7RZdp9fwWlZFCBQEdZ9mwK7DnmtxcMcmKTWRukQG1ZQIZUDYwxAq7HHY"
    "KeuM2U6caIoMzyOzGZlSojMR2j+X1RwmajW4FXO7BE1C7cN/Qbak92RLbTCkYHgYlNMfMMoUtvMw7xl0PBfGPrAUuP6gP53eqZk2"
    "UinrrFBiUqTEd3r/7yKV+lv1mciXaQsD7U+umvfOF3iDBm+PtpNWna+SUq2S2l5SN+bCcgImwJwv57mRPJc0VhYnUP+AWzEmbQyX"
    "SjdFEgc9UI41gSQ6DvEFADp+ZzN2e1cQhEJzdmgc2aVfPlImw+mBivRX1HEvcol7ptrszo4lbTqBHHDC+r3RNN2LKvVJUmnK15a0"
    "paUNcwM5S5+JkQc71xUy1z2lM3XFbhQX0dIePkuanRMND4qaDwvF3Zyhm6vUnqV/AN6QxsTXLGelgr/qrj1h3ekadriIvUpXpcAu"
    "N0bRjDVZ1ueLhE5uRPCTVZ8qdkoyEx8ExhXmq9qoargpnvM0Uhd7C+aBJwg/8CmGqaKDs/Vzp2gIL3TcBQm3t3lGX/CmtYk8W+Kj"
    "crhAsE7jfFD8FutsN0E2PK23jfc245uyGd+UXebNyWU+ra7f0Tij2CaLpRXj8RNQYuzWUeYkc27+eE6smoC5ruv23PIGlUg/glWu"
    "gJLE1HyGYBbFnXNnN6aTYw/9mmIaNa9oFOL4h//8arOZsvOmqXNEON2TjVMxdqCdc/v0ix50g72oNi1TMU/ZIjgFc1gDmJW5qzuJ"
    "c8GXg680e9+0pWYz614ptV5naAPWK+NIZsJa3Nj5kvpq9ryo21ubOVwNCoRlgwtMzSFRJ2HMVZqAH0qixDwMzeGAfBYi8g4KH9or"
    "g0AReqgtnqRxM8LlpRK1DXMpyd4fp7n4uLaHOiVxtOWXrGr5I/s+X9zJWdLWcAyfDglqDD4LliM5VNjQLjugi2aBUGZh/BPMDDsi"
    "0sr1Bcjt6a6EyTvdnfFqry//qth20X+UMX/T79+gIIMqdDHmIPiJcSKMiexsgT93NpnYD9mamip7JJ+C0ltYEdDuR3CSotM7RLLA"
    "A5tNWkKgmpZG4dtyOTxd5nGWIvTpYFFAZ3sK/CuqYcPl49lw6bmhlh21goHHEzPw/ECbVNMv98sQ27YP29WTaXbjxfggWWbEAOho"
    "Vyg8o3FcfGoc0vfDbqftUA6OqMfTgyPp8+pxStwP/V0OPRe3EqWzlev+ynZ/JQKWV3xvF8dXcn23O4xAkWu4evBg++mWZtLSJybq"
    "P2tpdnCglgcHjOWezIR/fgw3xsaVJPwKpvrxNIOROfiFwk0Bdclgzk+NmllF367CsNxN+erJMnZjpKpoATGH9iqGynr56yJdqUv6"
    "f5GaEFjciVV6Kf1YWfjRn14A7el6iNn4lhlJaiUKzCN1S4t/ni4PLmnMN5B5nFDCsXFreB6bJg+pyXNu8RhNHZrkhQxjFfL1K764"
    "vX2SnsdrGl5pxza0rOBWBOisMOh6FxfpBetilOJ3nucLjYxouCMMdwS/j7Po+HR0cHkm8Rd5xdvT0Rko3nRkLvILpxKThe0n9GmB"
    "T1c00uJJepKdpEVyg9PkiqspzvaBRt1Sq9zh6/Qmu82jY/DY0q9rv0tW6TntktUTzNPBgXMX8mClxE8BOM1T/eAIGiT0Q4A1s5QW"
    "7dliyJNKQ8oMaGG/L8M7oBs4aX58uNnA7OiaRpyNMDSUehgnI2oTQsRRiOplWs29MIFwbj2SBdLzuVcdXgXIfGql6f2v4pG+y1e+"
    "DQHi/IkxuveRGwYcgnSv0FdfxpNBEJ2U+C2XOxGn+1WUC8fRVfFYhWop1KeVjVNJ9VeRi4bbhm4gUOObPD4xJ2/HHdlDojwgSZoL"
    "r4TJj+ehkLuXI0pKZruTRPOOXBzyN5OlDOEzN1LsHJSPv0bhoExwo+UjmkDV0ocwmiCC9MqSl+BHA3OprIHPYtsUsU2h8ViOWxkT"
    "8muz6UmXh2EqPIqaOD+qOzydraI4QbQ/rpBe1IRt2LZwMZ3BBxmOLI5vIzPqO3Hl4QwYo/DUhFy/ev9guIZtPJBN9iQp8wDsVoH2"
    "upUuqwk0tV4Rf34DT1B6UYHUYOiMpnxLvdlASdHeA8slNwj/xvl9YZLoLUKZms0lhBnIIxzJRurBU8+UUHvTYwF/1A4CuxecPNa2"
    "dQWyBewNVss7V/CxYJgmINwNEJsRAu+9Yo/oI2ZNsJdTdpHZZeNkzYUTGSF2NRr6Kj7v7MDgdlWkviCzgo1nbWID293tZXip0jrJ"
    "uZQccytfZkZxuBM9+BqutROYhM+DK3vokb4kSh7CKd7TGVNX7JzjSFBtbgKe9L949CUUZ+g0h3yaCbiJiYtLvBW0OeT+ycUTMOsx"
    "vGOavA3hZnO52VwFUtpROGm7w3V+McZ82xSJujlzaQzOL6yliDWdwgWnvaqtQ3xZgMvM2Z7rpQmW1Svi9a3uTLe5QCLUsz5mP/go"
    "FW6+ohMfqejERwrDQlRpnnEck0QTyc4DzbMFq+CZJpMGEoL/qAF2IM/TGgiQqVC3jjhAXTpEXe02JRaXmUQl/I5mN35DGHvTAzpV"
    "W6kQ0Im61V0lLHPj/VfX3ec7cq/1OYexZgaOkCfxZoRjzFFEWIYyG7WAs03xsXnD0nP6K5KJiWZV3kHTVkvYT8Pm3wUcoCmplBGb"
    "JRV7rA3i91i2zCd1PoCAgEAQ2sWGC9gNQCqxSYcr5xNfMU+NQd7sY1GCrc6VHwHAsPL3JxWdfUwxVmfu6nOrTjTD727gJqu/d6L/"
    "IthNNwCT961rsYlYJQ9FAHLpzllgS4h9Sg7/huixzuYku2SXSFt1HK7hOyNc86LfEU9svw8ywbwY9MymbIRErlzGZiNuEVGbKyJ/"
    "ILOQQqneQtfFvmaCqxPdCWCVhVMBVxXf5hDcEaJL18vkCpB0pQmURoT4khdq0SZzep3Apd9ykizo7/kEPvzK5ESrCq4932v1wrnu"
    "hAfTU045S4voGgqSa2NDeaxdrHEqIKoDT5fL5Icioqz3Ooz1dJlHgoq0OUjbbei90up6iMLeGLi8uCjFwsTasxlND1MkL8sKGmdV"
    "eXDDqRK1r5xUUyYS/HPghOuyhaqIncfAN8sFdU/EK9RB7EXpXonwQ2ZfffFQuaAeX9J5YDL66cEXX9gcevln6EstD+1pIxjUanbg"
    "2xG4xtz3XusxVeCdLN8zeA7kGkUgxbCO0OExZ0+buN7TgG7TWpwcQql4mHcRZy/fv5aJCMM4WuZxSnR73tGt++IhuxXh+lLi2vBL"
    "iAnnUssbC1bSwSc9Uce7ytloBCXNleCLnN2TdPT2jjpVS3FXce59ZHPXod8T+fwACG/z0FuZGDJix58ennUkSQ47YRbFgmfiTXcm"
    "4hQb1HgvNTaFCPhROubpTMER1+NJvG7Zv70yAXPqgGNE1XnHoT6xW/njahg3af6gevLkiCopT5szqifL0+bBUVKlzXDyGKn5GdsY"
    "gFqJuAlKomZpLLCd4RDtXL2tGq1wiWF+cPDkkM4olKsQQxuWRfu+is67M7UbB4oVSmIfo9zfyrTdW5msTc6hnxx4T8ttELP4L67U"
    "NXvpNwea//jEfRzewXgkHyQObefv7jTVFBwce1H6fIiCrh1edgL9mTBF/J2z4vqxKK6Le25Tk7rOfTTxqZ7putZT5rdCh5nvDaJg"
    "HNa9jWH19tbIfhtncKFZNTBMpJS3pdWhf7kT6WR2AaL4Rb6T3N4g+flu8mSB5De7yQ3CtqiPOcxGnuY7nl1eRZqR1MdcukMFtMT2"
    "Og3DgsC3PpdhuoUKfcxPnVE6AaicizyGH/L0yNf/OjfBAuP1D/kDoln1Y4L+pzkjT2ot1JoN4i907A329G9/oC2UPc2pUXHQhN6p"
    "H3hfoeanuXNwFDhG+75r4GQqp5b+7Ail2bDHe64IVLuCT54Fn3Q/eNnpeQaouoLCIhSy2VFREprOvsq7ztMsSpRrE9ALHDAi5Utx"
    "cbGRpxFHVtBQ3NQZr5V6h1RwuHAJPBshv+UnAgE6L+HTeT8ECrsIHY8faK8awAt/wb6iypJ/2CXeukg+0GCp9o9U7yzp9cptooON"
    "wFMoVwMmRimCjjj1cYnaeJiw6YxEiLE4eR3MD3yBWpf3eO4SHopH1e9/D8TE7Dy9vOMXo9aWfFN2tSFE5cxFKg2s1kWT3RkU85vV"
    "qbOvVqNO3lkIIHyc58KEGBQlVMumSZm8hlfT4PkEbmTChKdB8cYo4cOX4mEgh8gDOUStQsUm+PzfEWBIJ7xvdBl9e0Nrt/UuN6Of"
    "obeDoFUSOZMoa7ismxd/aphgcYC2QKNnkyIwZ/YogQsr2WK9SrYZFXO9ewLCog+2etKhFRD51W5HdscJGH6W/hmYVfyZ/zXwmBBd"
    "Ri+5hOmxRhxLxVvNklcfnFpIcAj8nLMTfdvv3PS7DpkTwiOn1MMCch22rqaDOLFd5qDjnfieqgZTvaisi13e4JPJm2XbxHwUpM/Y"
    "sIfjNECFDQ7tcTmKQLkt20BcyLetqLilLzgk0pWYs/3W8m9PYvqFPvFa0XZLF2yDaJhy9it0lBzn/PvwUYLAvzGipsCaK/uS3cZl"
    "DxMXQibEdZVgu8BxSxd3/daaSKDEzcTJL4V/O51UcL4UJ7vBSz54ujdws2qNurFnQ4juuIsIdhW0J6CGlv0EnwrUYBvT16u/gStE"
    "1VramzPCmDPCmDuEAUHaDPbMeWb87hgdKcYkcXKaK346S/gHzL1BLoFOdYhjdFeVNhyR4ADqFD908IBN5LcuQrBZ8tpBDXoQvAVo"
    "IuCeg+mFm25ndJtVTJBnR18l1QZ/utikawa/h1r2lbYCPNPx88tokh1Wd5c0wL2hCNGhYE/EBYg4iIHc7wO2wpjIAYIOwx+7gi4e"
    "sgrIy6SrBQRLCIiPcjv1RngPrMniVzVB1yY6FP7CwNi+OMQ66fdrdluzUhMTlHlFu3YV7A2ctvfGhOoO3SZ7Fr3IlZUoBDvxGz6Z"
    "Dd3kfSpKmKfn9hMC12fBW/B5ZyNbsXJAAZwbq9GM1cI4cgM9mvhRjsWKE0axrM2NpmxfbUj5kO75qUux6bnTzdFd5vEIEhtIzzOd"
    "fOga0f2ch6GPDkNnRbWRtFsVZjkvgmintHfL9Oir4U7ENyo/rkQcIdcr/a/+6T2GWPN0dm8gUaJKEwlLcWfKiHWzgpxDH6l3XdLx"
    "NrS6cKNhjwCg90shroJhY5p+KNnzyxcIC0Y1fCiNtafEtqJCKTx00c9DFczSJmVHN0H4uEs2WXbd564588bWK3a13uixVSNz9Ct0"
    "06jGpWbpQEBB0h5hzgjMTj8A5dHhnz4aBtHmofQRUAIBo/mTMDN/y3Nx4BZm2DFDqWNjImhUv+PWaYbXVjM8OCZPzaMymWeBK3Xt"
    "HczEwUl5ap7pE/4981/kOw7cYeMNmUpBvCO0v6FpLKdwEEW3iGO+iE/LzLtSxlV/UiSFBfjSPvQMlcBfFDZoAJSMxzYVTTo/AoG3"
    "46+dOwZjWXxecsL/qFNKOxNu8btcXOH+kYcOdyFHtBvxj8DVCmudBl7urV1SGpVZOfgEPoc3IAS2XkNC+Uf+4IGybnn4wC2sClzZ"
    "DcrD+nBC0TlK1ArJBceI0E5ijolTReHkqnNTmgXs0Db4XfOdoRFecqY4kpOKJAJD+PLW53pPc/Y7cYGMEX/CH3LuMmJVTKUofk/H"
    "Eme8E5FIqNXAI13XB7NlHKwXZtsJ7/GuhLET0bKhg5DkXeETzcDE72JQgXOO0XY93BWdyBJ8kLXiHa91jJQ412mNaTYzivzqneeZ"
    "lw4n4Y7q2j0SVVRntZV80NuhsjIlw42EQiW4xHaqc/LiribkNYg8jITzieFh5Od8Ib/mB7q3DD7mxyWbh2lu+mBWqb2wD6Y+bX4b"
    "6aw7yisc/ERsJtVWVRxiLgUQMExXlILFSF8VJugCay5CK3Ai8n247lEV789fjOH0bzlfxvySI3Ck+jFX9/Oh1e+BJLNNo1Cx2vQj"
    "Er904piHIzLB7LgWxgTa24gP7P0M1mGIAg6zmsAlBA7Y7fDHPG2jsdijv3p98v7p6+MXo5MX79+/eHcygnU/epciNF5Q8OTk3U6Z"
    "ukqNoEpX3qdd+ktup+7HXNxXey1IZXVVvcYjzQD7oFBtJZdUvxBT9ku+W8Qor3o/KlWHwtjV1fyS+1VDwOC/KSojfTKieCIj7zv2"
    "bN+t3dbessHkHc0N2bdWTYwSnZgrtvFXJVFSVpM1z3JuITYarkGsUWoHZEQVBOWtQvJG0O9Qh5G87vTNZcJgseYV47JIKNNZIcPg"
    "nQoCie8SCL278NQsGg32cRqAy4oDQDJ4chRrxKdJbwnoiBI9VKcuktsZvDvfEqeEyjmcNU4cRACmuhHaXfQJTDwa2gkgU3JRYm8r"
    "WmJwxc73OSeXtOSYHWLVYYJZiaVy6+0qZeq2W8RVb00AI+P18tA6lmJvAUTl1+8kwI71OByN/3XzxXHvgP49GUPnXTsxd/r/svel"
    "jW3jSKKf3/wKO8/rISPI1i1LMq1JHCed7lwdO32MrJi0RNnsyKSapHzE0v72VwcAgpTsZHpn970Pb2c7pnCjUCgUCnV4UnskIlVF"
    "5TQm4WUxItlGyp/dJccykxHaobPX4TQIfe6yb3aPp2asPnX0qoyiOqMQeThBnZnRZ5LIdJ4XZGjBrS0WTqA/454S7TNu4jojBCl4"
    "moYeLVJKJs24I0aREmTbYhpxoElT5ohBC41whaguMELeHCmOGTZubmw/6c/UxEh2yzVFUxUO7SnjenIwTo7EKQOPpUQQ5MGN2i33"
    "SzM2zSS/z2W5vvqiDlHZVXcOoN1ih0RU0pZew1MVSZPdpqidKd25UOo8UMkU3pE8uZN7ftOVPfmHkR675sESnbbyjsyGPIu0y1FZ"
    "S0YSGQcJXDfv3nlX+IZITnu6/AcapCi3Z/jD8CNiTp59/rtawITWZxwT5leF7xNmC+PIEMZeapRC5HjnWWUZ2Dd2vPhijr5CEu3Y"
    "TnrMgVWv9RlvNyl0x0vyIPxc6a7gQdR9zqROJ8K3FR/U+6GMYD1TXgr5Asl+uHSXqB4ob0MvPSXeQn+m4rkyFsrc0ntWVfqUvogc"
    "t77T3Gk0XXEWKd8j15Ejb3g3cApHN/vuHHhq/t5J4zk+x55AAXIzeh3ZCAmqLWnrhwhGeGe512jCd89paEVLgV6XMuDwPQ3gLnLO"
    "YEM4B2eqMhYkVRgMiHsO47tM01l3d/fm5mbnpr4TxRe7tUqlsosv4+J2bX6109nbRY1s+uftG1cc6xmNoxFBDOfUVz+YVB/CZo62"
    "t4/VSKTrF8tN/StANLI+voFNLl3NmIr+nMT6XbiA/GJjL5U3muw4V6YbKGbrSZEZFiHZD+2RvK8a070FE7FU+4AojvTdsXUeoTgx"
    "NVQD1pW6pVLhShbefIME3zS6q1la9svXQR8j4rkkmIl3roBbDmZTHYMtQOqMTHJwPoez1lX5rsjKYoBz0xEPwEh3igkIITz18u55"
    "zFIyjRSLpM8epYGEgvexT47x0Qqt4MgnK2Xab0M5w78Ph1jWv3PefjhgcZYg/pz78d0xgQQlXTTGXJoco5RkMg3080BKBUfrXnUc"
    "tM55IF+y/OsgmidqWOkO3NzZZKjHdowWKklj9HBztKwI0StgbcCCNYI6nv+ob8a+KqGRfP2eVEw8jAwL+buIvfkRZrr78Odg695f"
    "7uNGPXCJOGmUdPfxS+bTp9v1VQAaaHXE8+5JlV1qk50Eatcmyo34ziSI1ZxZ4cxMsSlcDZzwcnsZecBzFbdeESJCh68fRP3IBAGA"
    "OmtJfGMt4KQXJ0CoMomtK44i1NYJrjz++SLKHsSv6UX5PRAaOtFYqMQSAfk9SpIuKw5JB3VCCaY2K0sxnsfUancgi7+jF0nB7O9Q"
    "kPbyyzi6OqQXFFmIUp/RVXo1/STKpSFIvdUmOHlNG5xRaIR0DlfaoNQ1TVB6voWl+BLxC84dTA54o2dw4/ExwK7JGTjuiQF25Un3"
    "CxJAG0Py3st7Oj7jwtl+HIt3xK8jP/lHRJwAXg2BWEifekYkAd+S8YPwcsrfS/E24lDwsrgKX585rUcWR313zfsUdbxG6CdD0+Of"
    "9xGqK2fOyknrA9CBwvLkPPkx8oSOe+0y7sQZYgRFHPAcjACyLFNyGeNPuqsIEeUKsbqHm8ePUa5IGrkrqDLFQEAreDJ3ogKSjJ1R"
    "EUMmsnFKloNcQZdZrpAaZA57rnJFYJD4IHbpfEA3p+LCudzevkTdpzP+qg7FfRQ+z0wCutciCvnrTn0dYhyi6ZQCEUchK9Deqq8s"
    "81iolp7RZLuHDjYmf9w4d/pHVsf3nXO0izX8J/HJdebnenZi8YZY0/64O7LV97wbkafB0NKudGRtbTqA93cqPZG1ruTfGWwCdEZq"
    "k9ca3FiGHAXuUv0bBAAJGej0wqtX7w+AIvCzIgLO82PEyqBv0EGW3592PVu85m8a41uE+GLxPCJTtgu0hLezt3RIzAMeNwc0fy1I"
    "ie51xB6b6C/a0OdBKwsfGoWn8u+cCvMKhj7LEdQahHz2yZVTx7QJrIq8/OPMyPGP3XstobeyJn3rtQTkrxHJjCz6K2RqBiE/Z8ph"
    "qeV4LZcDAHXLgEJxyRkx80idrFuYHkoRliuIiPNHQwXU1Dcu9VDnnECyXEW1rEqlUMX3dZ08RmOVE5wRFDrmMktT0ShSmmnyYUkp"
    "D+DrkgrRKg/Yl2jdQ+CzBX3T9rSH6lb+Mso4UMAvvD5nakHmvY6YRkMJSMqF0h04EoLU2j1NSru58M10VaQ3jzdBklIIOCT+lj94"
    "gQ/x/NeRkRZtWxYwVJ/+1R6k6UVqa0ES9iDfydhHJr4hhTtJ8NXXA5A2Kab6lJw2MJpJ+kwxEy9jIPyMVuuzfNxmePf6GpkvG8+j"
    "YqRewufx67FTKn2NhCf9NaDXfZmBEXvYziDczC0wcuPBlR/NMfpcaDhsjETK6dLon1/eR0vnFwYiOV3WDppjbcAdlVzo0RVswir3"
    "DMPx6BqwBuHqAydqoRms8MgU20npasbv/RwroFSaH6B1Oxo79YxBsmnUvswRSamKuxkWerVx48k5J3GUt2Po6lBGimWrfQwoTcQT"
    "o12TD0OJJq7YcMn3sQXH0Um0fIG2Fy4KCnWKPK9dlBL+EPGzRcLZR1mFUZaSVZhiBfL5Mmcx+RggN0GdUoDECXCzpCY7h0/IiSBH"
    "qRvy5fEo6k9liSMsATN3RrqENZb2zt4thuLDPsYHFWhz2j+JukcRX6cnzrw/595U413VRle6K5g5XGJ7e/f03Op3iUXGKJ8LDNoI"
    "CWKxZe/CLS1JLQUWFfwaIJlG8slVvxsrv6AKzcYGmk1Q/HSieujODAryg1xLeYPgQWZenGyfdGY5tqu+B2sYIOdHvpblCfkJTjS7"
    "BP8Sk5Z7yI/yugNwCZgDB9KvdJlJt5R6QEWUq7aOIOUK+N+Oa9tPq37deNI3WrNQHTK6ATR9oYQaSrph75xH4zuU/QPK/+AHF5fm"
    "W2hUjC+CtAgjp+HDSR9ILcZ3G3YH9Mfe+SMKQssF1CVpJuk1qp1o3Pflk3M37BcuucoPWYpcMH0Tk57yk6t5C4rQjOtPMyW5hJQf"
    "1b3ITS6jG9cMuIzcPMfSg5v8valIuIRTfPATRSygl2p1QcAFCOHSCzdSt1vIQ7YphYvdeY4D6f4uBdoqtPOjnYakiBtKg1EKZcmu"
    "UYxaIpqOSU6BkVfMBmJoYDPddNBGwIr7ad+KC4MRNBh6v9Vd2N2Yj07IIbLGZapA9NXYyfDKsAw0p2Dfqwka0mmZdF+EXtonqHYZ"
    "hsIf/Akg3uS1/C1bOVi1f0bOLuzmz4uefZo8lfXhq7ub9fJzEROldkFASpKkqyijFqEtHumt31Os+NSw7NhAtRRFYXuuXbRsqFD4"
    "V9ZGdLuQL8MG9tBVWb/vJ+QICQUx2jJda1RgSGNfFfI5PoYZnxwl4ohRcnou2WdsascsFJU8UnsG2wiwjW6Q0MvX5gW7sO+jhboK"
    "SBwB2yeLRobKipw/amwqQUg8+A32LcXDKTkwc1Q8jvFqeEJ+RQB8/4yYjoaqoZSdAhe2rtTz6P1EgTixQeknLCRWBHeR148VDnRx"
    "dWnhSfVTYQZjhM18xhYsPqz1ZnA1i+LUC9MtY9X9RK06aRoBaxtq1imEa7PKznRLwn6f1LdysSPLZehtS8+QyY46KZAsa1q6FdFT"
    "jKtH4yIpKpQ2vOPGTsxvFr0Hmw/I8PAbXZBFCkvd08QZuL/6518CfBd6G32Ff68SdyjChC7+OjBAYnIYYSKjZmmX/aF8eKCgKT1p"
    "8e5OgmlKCugyRpkqjNWdGAN54HALOkXZo4VWKgqcNIHzqxSTLHFNW8Ea1ZogybjITO/eu3gnIyqcHP128uzj0TPS0cGEm2CcXqrY"
    "pZd0OKE7yAuy2kITN47/4SUPCPo7u7fTIPziZlCLElNe6pwTp30fo6jdxBiqBhSgHz50jL07trxEqNCMLaHYAVsiTLEgug8IlT4g"
    "ml3d+owrxT2WFhtAcy88gs6wvGRpsDHzKTMxjSWk6bGrxa8KgoY824XzR9vGk4pDoUr/LuJeTFtkDAEq10t5yNVeG9Eg3P3w8f2r"
    "j0fHxy7ZlWVmhGVXq4t7FAfzw8nr9+8wBO1FjgGQHj+RFQYosFvHwMkWQbmzHl36oy/n0S2czcDRAp3pasD0KFwMPt5pv5F0T+LW"
    "nAD2Yn8t2PGKzmXCvP21PFpkNBo5GDUdpdpJoX8cU8EzdGiJu1opjaXVHFwE9f+ATmFcBn6bM0xDQjJyQ/1wfDujxQnVs1i0jiwH"
    "qBeRYcPI2GZrLirSH7kuPs0VX3dvkjVwq80Tg+fyA9Mka5wU/Y7ImAz+YJ7wXRn+YngmjLkjyRXsvMiO5NrEmrAOQgFFryjmXtyn"
    "CcEpRWHPEvYwl7Ch9pSz0HexzOebMNPSSQKcBdo4LT4AMxlc+4tDbwYr69tbu2IGmZ+BleoD7/FAmWxyV4kWvwppvG6hkscVqUlM"
    "EowIsjlL+AyAW4DNoSOFn2MupNFWOKgOFbkQMFf8mQv5in61lTjDH9TQLQwgeV81VQe+wNe3gRpy20Oa72UCqHOROHD4XAUJLibp"
    "f1m2OGOPipcJDMu6SDJXh1gFDdpSfBS7wbtSZkqbO2Gkefkm7pI0sfmPk1U04hdjzr4TomYC6tbkwj3DgcSrrcxvM60cNM1/fXXl"
    "jwN8Jobz07ugG2vv4Sy+7Yf83k36T2dYdCYt7vmkirXhquegnmn+cAt05KXNrHZ20AHFoJBXFN4Z8btJfmbZj1RIDGGThVva+kVi"
    "sy8yCDhnGECdg5LeJWz0OLr04sNoDPvYqmBgwWpVOjXWyVVOrhSSa/ZBp7WStl+t1cV5Yvp50/68R06gXsroji8vWv1XLDQcyUdh"
    "5u76P6sABl3SRMD76mJh7G7YehaGKcYqO0DJskDHVVtUoS2Z97mYB6TuVkWsGNl231LxK3Dh5LmSPzSAsJmegekH0X5/rH7yWzP8"
    "Xiwi3Tj6k8wq0pmsYhcA0ThmxEa9ELQwVf4Y30TemMKC7w6elf85lJIFLLeJHAcMmMZLDBWCgbQw+GCN534WVf0Mf/LrcsyAnXiA"
    "LmU1C9whlCLLAD00oGKweLcGZSYFMxkBdPM7znepNgN4S5FLMcQb8snq1E5m/nRKkFSVx7F3cUFholRreNskzQaZgNKIURTH7GGA"
    "m/HCMR7DZO+SMXKvX3589vZIFUKBivqewpmyUvrdh08nulc4T4sFNF+oAFDV81jLIeprXZFXef32lSr7y+sXR+/Vj8Nn7355dqx+"
    "Hb//9PHwKOtMcbISkGSVt1ntMnwNU+s8uWTUYleOSDfDbPAmYy7bZjWeIGGXa9BBqB8HKX4a8rp21ww4G9prSrBVNd4gRmk8hZtD"
    "chlM8B7hTfHfKz/14CZxAzcJJHSsqoBfBkkFOoXP1VKdwt+RP6TWs4WaCtMJZ7H0lKO4zGNUhjhheyvsHItsor5kPP3JvxM0EJlG"
    "35gIo5JJ8IUJOECZgp+YNPW5ngusTgrMHiO1v8M/0Z+AuArG46n/aKGqiBE3Hi1TE/6tN9IKIIcJAxgvmgN6FYThuEMy2ddECl9b"
    "xEmiH8/ohNTm9VoX9AzV4d9G44S5ArRaYVnZjptZTcIlUIWHtqyQRGumHxh2TJGuOKaInRu4ccERpBiqGD3ZqbcThby+anGJIz4C"
    "DPCTUdeFfzzYcCKZwd20i0ZS81nX9eI4uinPZy5DX/7Gb1fCUSbRD1eMo5tQJeG3K/ilouuiGRi17S7Fi6QQiE3CBcD63XAJJYwt"
    "FzaBS3KVPHeBgSLZeyCFxdEv7Lg9FosjjjgGO8XO4MIgeZ+gvkAWF+w8WYqbyBZfkowgP0syA48vOOaZZ71PeNf9AbNTwfEkAcLi"
    "O9rLC2eKexKrsU2q9gdBaVqvO3beJdJz9WZsTg/dl5xl7hku6Yk001INdpQyGvqp1j+AAdJHBcp9UPnphC9SVRLMmHpOrowG4zkh"
    "heUQbxM8+7S6IhA9uCgDuwyXHqk1RW2siIquy6Np5H3BoBwFKS/aRJSvy95sRoqvwJYtBZpSaTC/TdTToNnb8S+vZIcSJMzPZBZn"
    "rM8ny+C5I9vD48RsKFdOtSVVhzJyTkugFpusfZXIfEV5q8uqoR90hGeg/EHoKxGQeKkzgDi+vwlVBt+kEvFa52d6nOicISsp3qwp"
    "MpOZr5MjuDz6McXm+5hkHpf4hOp/YDbi3tel0Gx3FIWT4GKuf9/EQaq+r6XI2e7y7VN8zbYukiOcLSv3crzd1wlz4ClFa//Id7JU"
    "KaG85HjDXAng/xLPUfvNw3XU1lyK58ZspNoxXmwsSwb8IekP7Ru8KgM5ZmdVaB/JCuyIR2SIIaJcsfQSaNXacpI7H8MW68dKbGB3"
    "i1cqlcE3KXRd30uAajtkzzW9Y1m6dJ2FD/K/JA4x3RsyeOvGEVDLGGjeD4kO3rmhAnb+TX2cxurrf7niE5fUoZ8BrQ8ct4Love+4"
    "HUPK9WuSva2rGzHNeAOB+Avw1s+98Yak/awolGsp8w+Tu6SUG3uqrCfLTh4su9dWZZ/Jsi8fLNts9h4eHu2tV0hdM6eXa6w1CvFm"
    "Wg3pFsd99vzwxdHLVz+8/vGnN2/fvf/w88fjk0+//Prb7//0zkewUy8ugz++TK/CaPZnnKTz65vbu68VuEw1mq32Xqd85sIWGGbE"
    "2l/alkGrftKglgfzfzSArEpo0xpb7usQcAUW4Rwu963GPJ5ucFFXOVWjx8LJNILCraeqod099LSEEPkUhOkec4Z48yAXDRXhSQ+8"
    "j8XYiZxXcOLhBMjhXxEbHhwfLg+wQuRzJ3bi/f3WIhJByWmh09w9FPuXnT30nVQqDZ344CDYrjWbFHE4wJfheNuq7u8HdvmbgIBL"
    "RoAqkRvnQZoYZz4t+p+a6E1i3//qw/EcB1f+POi68gMYF+V2XaeVgS52dbIr8HTzxwHq3uaKYHqZM1yBE06TfAFOA14m8C5i7yqf"
    "KRNdMRtPrgP/pjgASC5zOozAS76cR148LgwAksuU7pKd4EUcFEqoVFdceGGa0oDyJSi9TBmumARwpnmhd1EcDGaUZY4LxOhHckL4"
    "e+K0ms16S/zGwiHGsB8TewfKT2FfZlj+z0z85fxGogzHLzjn/TFh890KcaZsqvsfvyciNLE73P090YvMb4E/J9ziVuJAL6hbMcpt"
    "dczsYeBjHGy1baB8FVC+2tTer2gyTb1NB9Xm0KnX2q22KGzZdGRe1Diwe4+HruZY33sa9kJjg7Gs6MekaFZdYidZ5hxjnCO6IoOd"
    "UU6fAghS8iysIkynhmpBmBsKL0C9ZiyACkBMLtWg+zh7gFE+1QL2qVZcDVoGYJpLuBD0pxQ8TcnOGm4JSKXqSsJVpCP1WkZBYorT"
    "VPJ7/uocQ3o0KvswR7QjkpBXk0OMydqFAa16LCv/mKCyKv0tAcwpIBitZaWnhvMdK/A4+JdavijlsD8aKDiiu5IIl5b5nhKPDN6P"
    "1sjUGgtyi0bIGxsDBdrcC3CggRooisADGCj+g29sJcs7cBiAwdDxyjGO0hwRPhga1ot/rb8y9leW/e1XVG+lld7K+e4ic/LQ989J"
    "bvbJKL+wuAPR53mKPs/xHITlO/BHaLYkBR4UsR2T93PJSq6yWTGeLkYZnTHxaNUDYaW3FuHVqwzgeQl38ApisO1/OUQgwOzXeBmv"
    "bW/DHDFCeCYDfhwNkWstw9zwX9gnJStGcJMmNuw72h2a5KGUeuVUhy3fe2D/1p7CeOFw3SZPCfS7VB3SBA8O9vDYXeOMcGqAkUC6"
    "BmCwyamHBbXVM/yKGusxH+Us8qBdiYwGQoxz6Fk8FlLuxYEtFdprhjoxhhrLodKOG+Pi4NtGjL/JW3SAX7A7RuQdysNfUCoQTXS2"
    "jh4b6bcnqgB90objBP43EjVU3rVV7kjmJqKJQX60jtjXarUbi6+1ZqVrVh9BPSg3smVxg4jP1BSobirrLh2aWi+jItgWjjVllvaK"
    "RgC7DY+9WrXVaqIn8uxny4bfl/nDcA3e0NFYa1YLB2O9mh2MiCT+oA5oU69KurqFBzP0VCueMYAWeMbkicse0RaKeI+8Hr5LVOmN"
    "Xq4MLlpugdP8iXuRQ5GQsWjnTvg7t7AW0AZ8p/AtFzswcgMzlxGAClyNxNWI3g3QQVcq0YFqfoXUr5j6lV4aR+yJLMEvCiM0cgL5"
    "NcWvOAttdn+La06PiXf4RdEfvuIXaUumnJvzkHpmUsuL4lFxnZs4NP9zomnYXXcr+/HV/JEaxZbkzcsg9llcll6AdDcAuqtyPafd"
    "8zDRg8SYnpLPcFlIYTmAtfP02sX90Lng069r0dAAxMbYAOjG4ACWxugA3rnhZZ55zJ19NyrcjMgpXU7Nm3ExQ+gdNNxgGmCliLAH"
    "B20ecY9+OtVae5u+pLRv9YwgdnEtsZaWMbWn4XBBf4CO7gNqZ6SZ9WQSIi/FYQYOkR1AMw9JzlaCuBUQNgIqBjalEMWBchERmpH8"
    "ldCvqcRdD7GrMO57IhnpWpKBRBBxiuuO7AzWc2oPOphSBx76q6BepkA2bLGSbfen+APYdPY2aW1a1e3/HGEa0BAbFcbwRd2JMMUW"
    "gBJTQIS4iJvUAcqRMz+u53kqBSs/os6BwDQUTQPqZvMD1KafvxUO/iHvKrvYR5joq8pw42gMtKvaoQvjxiwCRNmYwIXRH2+kqIEW"
    "pAHcJxPftR+4nd8apwvsBP5/34DhlMYJqE/kAmAzV/TmK1Pp41GR6A5q9baoVaui1miKTk3UWqLTEdU9sbcHyQ1RbbYgqy2qLcir"
    "wX+NDv+tiMf/V20NjaEfFvgsJOhFPmv/eC2fdXC8ls+q0oRuRg9eqj/gx6fXuUv18fqLNCoOHhXuzofF+/KLNXfkDy9ebvyyei8+"
    "gc+N58W78Av4erVy/32F34Xb7kv4sfE2u+GejJTA8huSVak6gCp8GvRHJk0/GVk3I9iA/ZsR8EkZkDJC96JQ/E9kmPt/4lODVNXM"
    "yr6nA8HRrdj3yU0gBZAjQHJXWqV1pVh66z5dbshtsREkG5y94/aoMEB39HDZAK4qabJBhTZgskE03tn46CM6JxHeg6ONL74/25gn"
    "KIBJL6HKNTpUj0LVvn87C2J/vL6HceQnG2GUbowiqJavL7vx0g2JXPjKGPtiI4o38IEIxjT2cQCeqrIR+1Mf+hxv4JMQDP0umscb"
    "rBGdSFcDalipdwXTeWhcSXAReqjAwzAgiZOqeRNH4QWKRMbzUaqrv1k/I2xVVbwKEoSSrvIu0v198e82lDAdhg87NldTjuDBVbry"
    "pvhA7usxAqro1h6sxaNUxaCqMvJdC5EU4JFszMMvIcB+x2XlqC8jZzCoVquterPWqOyJeqvSabfajebeUAyqe51Oo9FuNKqiVant"
    "dartWhOS65VGp16rN9pVUe+0Go29Rr3TwfRODdjjTrNdBxLYrtc6zWYDm+m0qp29NnQhoAcgiHuNdg1bb1b2Ou1Kp1MX9Uqzvldv"
    "1FrYPFDUOgyn3QBK2qnDYKrNNjZf22tX2q16rQbdtloNGGizVcFuW7VGfa9a2auIWrve2Nur1zsNTK9Wmp29RqUqYHqNTqfVbGC3"
    "rUq7VmvW2nuiCpNoVaFNLF2F3vf2cKCi3uxUcI7USrUDp3J7rw50vVFp7VX3ajBSHA1MBNJrFST81To0VKXkVhVGAKOpi1a9vlep"
    "16ttHEutsQfkvwljBLh12jC5FoIG2mrWOxUcZA2Y/Va1zpBvVKA0nB/thsAVgAWqEwhaDagO3QoAf7XWqrXbdZpSYw+mUYPkCmTC"
    "GtQxud2uwMHZ2auLaqPT7HQqnUoVZwRnEcC+CqdRda8JLVZr9SatR7OJ6wOnGQy6WavuAYAIAp1WBQC4BycawKcDheo4J2i7UatV"
    "9vagfKfTaVehV14nqFqHgXZEu9Vq4wq0MLnTrEFLe4BktSbcczqNPVrWOiBNvVpvITbVAF71NqwrpgNMm21AQVi/Sr3RaMJsKL25"
    "12gCLtDZ22pBM3JaAKJai7Cp3dyr11q8TrAItQa00oSTFSq1O3VsBEBdBzyoQGoVVqsNA2sQxOo4yCpApgkIBn3WCQdqnUYbvtuY"
    "XqvtVQCvCWKA/oAQtQ6uHuAg9oV9AgybAIJ2pYLrBE22YY0Jknu4xpUmTqnawOXdqxAu4VIBzsPxDwjVbnaqhKqwE1qI5MBqAAAq"
    "bVhiAnwbsHOvCbsNincqe616gzYCAB7wFmYLkKwilBo1Qo96rdmBKoAXgNqwJ5qwzwgpAdkA+dttHE4LBlGpEE42q7DeTYAKUoMW"
    "JELntM8qFZjLXgW4m0a9BrQABkS42oF2qoBekN5qw2I2aefU2jAA6KMh9pqwAzsAbiwNI0S0bcAYoWlgo5o41WYFV7JVbcGuhD0O"
    "vXcQwoAmMIImMFNQDrYfoDPOCPY4INxeG0bY3oMpAXHCtjtQrQ70B+ZfB/hX2g2CF6BxDXcfcGdAJ2Dg9UaFlqmJSwQAr+O+qQOS"
    "dajTarsBbdfb7Q4CAGDa2iP6BkOCkeDGBDRo44aCTYQTRZjDilQRm3DH1To1BGSNJgpYBGwfkD/Y5vUK7QQgFntAbmsN0YARtgHR"
    "CF4NoIx1WI+GgFm2OhLsAMYWgKuKhKkN80LnpLxvgGzUq0BNgEwC2jdhTIzwQDWBwHVotjCYCkMBNicwpYCwAHkYH2ArjJ+XGxCi"
    "DSMUsC0BkLCziJjDvt2DsQHoAZNgeZq0FwC7AOEqWLxRAejh1icqATS2uoeDrwL2VuuwVA2GJUCjAagKuAiYD3uBUbWDxBHXFeAL"
    "o68QZACP6zD4VgeTgb4CKiES7DWBBMLcRXOv3QASQlsYIAi7pEPIu9dqw5SaRAYqgMdwJOD0WzAGxDIaXg3Qt4IEuIZ7Fg+5Fm3t"
    "PSTSQFRhmpUOjLrKRx8QSNwrcAg18BWwgluXtjbAB3qDtaYzrd1o8UkJ0wdgIP4CVUJ606kOh+IZHa+ASdAHDAsPwA5QW94KsHgA"
    "KMQAvBogyjUZ/ypVPBMAatA3rAaQHiIrtG2I0AP+AZojDSe8hHoAz2oVMQFKt5pVJtC4d2sIftHGGxQUwOJIPIFi1JvQOmwBGGqD"
    "dkmzUW0AutSaAHwYK6xAZzjM+OE/RsoMx5AS1mv9QWWRisoC2NxwH3/6BwcH4SLdhx/lUKT0y+dfw+6AfpfrNUxqNaCArxJSThhm"
    "bPLblR6zDlYaruiWjBbejYoWyxbWq9glK6a/Wr+6FJasYBfwCfCrXeu0FhV7AdexRWC09mFkSqFliJicdDndBdYF2BQ4QVCKhUDA"
    "bkTgAJ49pYIjP5haVlqqtu1djLSFIqv81TKwMbCQT06LSJsdiikDMSiJ1yG8O1nezvl8MvEx7CUWxxbqNSso76GgK5/UwJh02ETi"
    "PBuRHarvHAxQaCj8AeApiim4c8DvohQ66Pklh4IL5h+Iqi0SLo4GtacwyAjVWmSHfmnvaQptYg7KqVfySg2zE3Qbvb9XMaMsYVXL"
    "L1eb9hAgnP3CwKmDWARD5w8SOoqqLQaeiPRvAOggEdOh85Z/t9H0OP7sfU7E2Ak+R5/JTpnbq9kYhVX/oLavxCW1NREzIGTQ2IU4"
    "0wkt7O1a3FHrlGCLc+fq88Xna3HrXH4++3wnBsficOgA4qlBt6CX7Bs7wWiaPV0O/qr8dla0jSVtkSt1Lm4ZqP7QOeYPhO4hvm0N"
    "YLJDJ8EVZfgk6JcEQDPFTyTQ0Ct+IiGBoeNnQ803GSDZoZkmA6RyNMdk0B4WUMFYpEGExhkKUg0YKgwvS9hTY5cJDQDdjRN9Pv98"
    "LHzfST7ffj5EjyWT7avP/znZvhAnzmz78vN/zrbPxCDEMCo0bRiIuBEYa8hIpC+oLE5ssZL8BS/oCAb+ICAWyzAMNQRpawwCX3i+"
    "xiPcmYPIF0mWVMdJjnwxNZIQQ+YYFZFaD/zPkf95hA19TvzPUxjkdvw53fY+x9ueCLeDz+H29HOwPbV7186FuHPOxIVzhX5kxJUz"
    "EZfOTK4NtDXHyOU4WkRgjwzsPSdGYTUSFhSCC15zPSsah71EHMBE/ItwoL/VIYfaRKzgzKrMrFImW9OgkQll1mRmjTI9FIAj5nBm"
    "XWbWKZOimSMucWZDZjYoc4KeTRC7OLMpM5uUCaiHmS2Z2ZKZLcoEZMTMtsxsy8w2ZQJWcASOaZF2thrkzsAkk1NNJgu4TKg8N+jk"
    "3lNYb8YeOhxEIbPU4Ozq0Dw7Nlj6+XLk7LUaflO8HrE9zKeTQws4wybK9GzxRgvc0L7oIrTWuZq9H0VXV/MwSO9YN+/qyo9HgTdF"
    "p122+Dha65/2K7AYxjH93DikXPcxv/BpybHgJrYgFwSZowQgUtpYo7dqvvmLPFJR40+dy18T657kG112WMDSK6mzxuIpweKHri+u"
    "/CTxLvwuC8E48GrmZWGUcz6aBj6ZxWm4GAK3T/lXyeeJhcIn9oypCj21smADUt7zxjv3p4a+qL+pzfHQFES63QKmeW+x2DQNUdC5"
    "guwLYKAlOtJ5CVujs1H5DmvTxdmLR+2RmoNAYPA5EbE33jWvGRUhTZzYKZ9exe3tHxIS9aKlWamErzChDv85P4dZkVmztDEjU/C8"
    "gt2n0L+dkd3MRhp98UMYNyCFqrEEImNletoSmXo9ti090CzQSqOpH18FITox2JCQ1SAawDiH2mnfEzezU8a0ffQakW8NNZLjyNBF"
    "Q4GmblUZNJ+eoilryYkLoeVVh1K8Gkjx6hO3S3+hGn/sul2oHXDYeBbAnVOSe3rumqkTmTrJpYac+rdcYiyLxrnUlFP/Vy5x7nal"
    "EsGvckH396u1Bf/AA2p/f0/9quGvhvpVH9KSNQQ0yvuXXs8OpWIlWnGzxpGOS/GwhuVyCSdMxAgUHQAZyJc9iaKNse/PAOyhpbhJ"
    "X1pwJg+pmBoohu55bFXYvYcVg7WRiHHPPoIsmxV/IH+pcQNKidjEPVVsk1Eo3+GR6g5NAxA4JTnUwMo6Pzujl4CzM9jz3/U0gPZu"
    "a5RnuY/CkLoPDmkUTdH1DlEfnNQAOCjPitCXkNmAcPXbzjpIPNA4idWh7BJJwVLNdJAD82BYBPPwYTBLV/c8wEdHOPwXRjgsjvBJ"
    "rrK5SqmbuXki6zrXFvy+RdkTM5tM6TC/qvNDMx+PBchWfsWoQBlW/1NiJYquWwa1S3vG/MpoZgiDU78rLtJbHXp985PctWswRBp0"
    "M/PR+5Sj10YPOwxQ7OTf0BqdvfL7KGtZrV4JVbHlN8Lgv9KrhHDBNxGZHtEj7LcOHFTJ91DJUeIlG5KtPVhOlJawPgsMXeFoaa0e"
    "nIOhVnkymR9DcVCdRvt0v01X483SMYIRbqnYgVPtNLa3432nVqvbgVOvbsdANDGuIl7SlfEzlKvVZDm4IsDtv0nlalAOOYsMc6ho"
    "o8JFG40i9JWq9KeTl+U9JBxOmxqqQ0OktYurHpa8gwdAVqyfv8B7mYJnagDDqnZq2ynwCwiTb40nQK3wVn07JbXv/WixCA6q1WoD"
    "/sNPp9msoZlysO+gLL3+rfYOeFp9VC1ntWS5JtQONHhQrYhmq16rLKqVWn07sDGgK5UI+EoQm1zvirWc06h0Wna89rCUNhvsWl0i"
    "si+A68cqme3T0vqJAhEpJ+XrObsluanTQb+iTR0Ha7HIm3lGj7KViRNhZOXvfMGmN2fjyRmui/fAlWO76CtLssD4W71+wo4DHhtT"
    "8C/+RO9o+BNNcG0ReFQc/qAXn9sZ/oA/Ljv1k7ObKuba5KV1HofAyzI2mVgAAF6i8oYPNzRo0V6bAf3aRlPB2GxoSvcDwxImGw9n"
    "GH1WoNib0YBzMKiLHjMSSWVIsL09VXcOyc08sjR4Q58Q0z53ACU8Gy7piNikFYFB1IEg2hxO3UfsfBRdsJlJjvdHBNr9PKiUO155"
    "8qz8cvh0a1d5llhvUHHp3+ZsNnhjP6JlKh375C6FqB818+LEf41uv5R3iaehQF2pmi2ALzSUpdyx57ebfqt13pk0O+f++WSvPW6c"
    "n9c6I6/V6DQm9fbYH40mo1HtvFqvnXf2fL/a7PhQqdKst+vn7jfgwi4A4VRHAM2cu8Cfjg3l8px4+MErIIKyWIdpxXNUjCsBy1ai"
    "e7P6SlHL8ONI6tZvVtCZDCBRFf8qlAikhWS+YWmlb2i7tRqLRbhG+U2agAdaobleE60G60YdjpDC5Mp5qFAVcra3WNyOMJ57rkRk"
    "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"
    "VJNqSGf0OkYtW9M1x697mcggFVBRyVX6vr4GW/uUKvAwPvIVvNInSwobsD/LNbR0j2eq0/GGBlOpGPuwpre/gFipuYAoosQyF0qP"
    "a8W16WmqhsbzzaYihWr4jIODs8OjG8+ODl/98uDo/nCUrpqRdevJ46MbDx4fDtF+N3HDeTyyHj85epWmw0H6lvx05/FtUQuZ+7yO"
    "Oz89v/EQcpI/V+6UlxdpUPoOT37weDgK5yPr4Z3Dw1dH92/A6zRRXl89ecaKvTp6gp+Abbn37M6NozvPeO7jRE/RCxxjgZt3jn65"
    "cwfyjklyQjB0yG3I/urBIdL8hDyIZcIrgFIkPo4Snn7zzt0nz+6w9JsEliLhH27chVZZ+o0gIcvR2noL43rj8e3hyMX7wCfwNYLk"
    "dGIOqd/zL/8zdsdk+t2ETBdkGdf2efzTLwU9OQyEbidzH6o7V9c+NUJoGV0N4yqnKaPr6eErG2CVrIeGjyRTp94ccjfSjBtWKcvD"
    "jMc5DFLweF3AICO1ri3aZyV4dcDE2syrp9Yuc4BOXmR69hL9hoz+8x/xPnrJ9X3PcsIY6qt3fnBCrdWBMapTH7PkAE451OEn9Wki"
    "R6AudTPOUOw/HypfxBb3vZSEXD/zgatEbaIhf3I4n05eLL/99iX6WdBGl/klwH0bqNY656XgwRxKh3iUTTBMai2JaqyHpAbs6z59"
    "BioqlUMb/3gwr1GCg1nHpCZyWDS/iwNQY3rAcW22ipPaxH1Dam4tN5579dqMJJPIR4cHVIEamDl0GZFaC8OAKIOB6og8AsJaHyYs"
    "TXgomNQ3EdW9hiGySHZMYmwHGH0cFKUajMIRAR/QYBWIy3vxjnEawjkAcIpTHnOPD+5ajXd8EqhBVdJjuXoaF/eXLOs14VhWeowW"
    "neR7fp+6Z1FCoIyeCDVrbVFQhU0thVFpi5YBzkSwOIckGWlxG+ssRt+N5TH17Y+80Hf/tXd9+Dx8/6A+T+Cp/97pvm816/B4a+rO"
    "FqgwRmsQPMq8fp33R4g1lBDmfEz2EjGiyfeK15y9JPWhI53rzumZX7Co1+b/TqinUnRcdIBKtdLDAMWcO0DwmL7cMCt4RI90FLl4"
    "QJbUg5lLRz46QFIAB4drOPvYfNSIAYe+2IsPogYatlEcusZqQe5fSly8A9EfIC4ejX0og+OGzKSMa/HFLwDdPbzWB/7IZecJr674"
    "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"
    "AlpBOMYzlitUagqlRYIzraZibp5lS9dVTtk7k7NINlbNx0fXto2qmIpCpN7MtulGjeoLq1zv89r61SynKBMKbnu61yNZTqJl+A6y"
    "Y2xPQUocrmKu9FfY6OSHOYUdepiEnlqRKJdb98aq5NkK6vrdiP1S7FNLf/GIoOpombNhdKdMYxV84Qity4p8U64BdifRusQbH4z2"
    "T5+O1lwc+TBSjEtCMAqzrq2vYeyTKJrSnfajmubgjkbbfbB71MVyv1R/JdcMVtF9i+zlk129LlzARccFXilss6d8BHHhGq2gPo3p"
    "WgWRoDAcyz9saSFAjgl06qKVns5xaqw4RllJddltQW6rFzf1hUJUroNyac+LG08MqFRxMfocxj2L+vmdXS7rmW3Q3iTD11DGxLSq"
    "EebFWtM6tprD/FW4z8u4GhTDKyUe5X4nKlIB1fArCJE/Mbn0c/K9KJoe5kk3c27AmplagN6pxRIQk8Qx5S5St4BCh27sxqGXLYN1"
    "PXZnWYeJF36exnZolk2OGXe1ep/LlWFyHTaN3ES3cNA324K8ZVYnBUUyBj7cs8iGQsL/iChlWlYwkTEgYsTSy7y78Swl7t1yUlMG"
    "tcpOS3qt5m3b9qhaOBiq6yNqTaIFqqmmKnfox1U31sbbV8nC8zR+i1rUi7Wl1V+UC4CZb3Ax9DZep0NQyZOQdiZ2RL/W1nKmH+kL"
    "98pzcivb0N25+0ao+lU7X+e4juIzdtb9AN4NZfY4xTOBdkAWZrdSR35J3mTnCYXK0AHq3N705bKq+MGQP8jb/cL2PVnNxnM3nALh"
    "qcx364qrKT2XlT1OJ1g1JK+IStl5uKQcWKU72K19N3dN/vq3vUdl16H56cj5q1FcHOdWouIyuVO4sHRuIuc/2Gxzks0rcKXY31MF"
    "p7ifj8LtR3cpjEMNcD3Q52bDhGcLVafY7eoUu2tUSDDnHVAX8dMoJjptMRPvD76xdEr3lc9I+1sZUtMWgQ61Duiso65QZntQDXPM"
    "nnX6vcyJpKy8wXmM9DhTXC7Dx6hKIlKAbuZfWzHn2ZSdSvgJMk1hFgfaKXNx0wRev5z5EN7fnixcL0xOUcNV+IOLWNJWjFXGs4dk"
    "Aq3UtlqfPmNAEk3FRg3n0Lb/WRcM08ccJYHbtmzzAoZE7o3iYyfjKU+52h0XA5051De0QeGsdgtZbYMKnErezWpv5jAMh547ZUfN"
    "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"
    "8yzHTWONxijWq6zXXWmYvZxKtWm9VghUG4vCiTntd7vpQehMmVU23OyUt+FkZxhrrGJqfrYNHNjZtqq0FmBAeG5Uviyb0yO75ZZR"
    "0ITKmpZHx/h1teUPdC21OEx5RkosZtFaeXWbxdlJotEc7ieN7Sa2GoRyg2I8Ubuxtf7uSGfzqdt6VI5ey71lPrdJTUpLblCaTQ9F"
    "YZuKpWrTVj1y3HTi7cq4PmyGS+dYJJRrBVvrQn99CrQ4gU/vUkpDafYTvByr1Mq3yIQ/5PrCRi7Hk2JvEVzKtVNnER1c25v4ttns"
    "xOKb4Dk3zTUKt3axuDqIw03udGmtQ9f6phOKJ9jIMn6rFaap+lCoLWfRRmFc3KfqO8gs5UN9Fhyr5eFMvfCl4yQVHqZ352ytupkI"
    "7d20dpll5V33KHe2gXwo0OnHcll5EePjW4VJB3bTwmw66Mjd8HU/HKzrg85kwY7bi204H53F+XK3IMVGtc5q1Ko1VwGh3U+p50rt"
    "FEzu9mPhWCqIzFpex6Pd9JYu3Mr7yTURD7RmgKvFbL4pDNr99mJSHVUAh3VvXCzW6MZ7hewsWIlH+7lYp3kZtkt7elCMDOuT8rVV"
    "5dVpAvBfqcTtilI8WBt0WtPOrrMv1TeFWUVUIlsxu4h1BpFciCkM853wLFc/iq3WmFlt2WondBitG81K8RRu7vt1IX2dTNPr5HBd"
    "Kw5y9RN/YCtD+tjtNEOj7OHCn64RtZsbnaOxCxcc1mfVRIftZ/MBIQvKW0jHcJOeVfd5rj4KBWZNjo5c0sKllVjnq6lltUQvj8Vu"
    "nVkch511X+wmAi2FzVbq3ZK4kFJx7ioOkgU+lq6e1nGwcq6mzKEYW174y4WetffFM3fN7TvrWTjW6gnh4ZnlQsGkkMi2t5VLpdBu"
    "KNnqZL0q7C7XErOR+Kw8zLc6tV6KEfhuTa0PF1K5X68vJiXQG/qQ7SYS3K20KdeaNba1yNcSm75Y2UxK1ZgkLS7RSA1Mx8mZCdeU"
    "dC1YDHf5+nmZCww3s31fDDV7HJgHm2J+mR1nyxFhEeSnjfAg0GdCVzUsXfYK3z/lm51ZJ9SfjY/5nHo+jc4bNdGrb2b5ST6RLi27"
    "hU581Jan13RDGudHpRUfAUI2cOzJPfowOvfSTLgb74cC23qovcpXy6Pp+No+jKan0Gy4SZRiaqMk1MdghsRoMTcKHOVNepwstyZy"
    "OVUJK3U5vJ2u5OlgpEz6TfEsCeHtKDHJ1leTVlAqHkq7WVWaJRJZsbfMqt3ToNpc8b12shRWZuzmJvfqihBb5lqrzuR8OJbPVbHb"
    "XtY3QpPfltVZPxldDcVIY5NY0JvRsBPur7OdKDvaXNjsKJWQOLp4u+WnUvccYw65jVo999Uyv2icW4N9QqotxHHxStNcfNhL8P3z"
    "cVI8Zfn6elHKK8ddq94eDdrXQDQLeCMbnCzGs0mWu13BELUO9FAR4tsxf25mS1wqXSjScqzbTm2H2XWkHFpHttv6qLEJbXPb3XC0"
    "FtLKVBqczpvAYBMO87vG/hrjcpF6t19u7oScsmNz1VGztFJinV5/EzrWhqktI2aDh3QuV2p0EvtdpJ+vjsuslA3E4sFSl65cg9Hl"
    "ZFJclftx5RIdNhfHTqOVihQUaRqoxkFpeym6PAflrjhtTLnCJjDLlSaFSYVZitPDobjiAtHVppLim6lVYhofD7P9dLddE5Z5dauK"
    "t2IjKC5KjUqoEauP+H0jMMgvk53DOjfZp2vr6koodUvqdt0rN8PNbacp7hPt5nBZ5depMd9ppc7lw3ogV4qCQmeH/LnTDeyEbWUc"
    "LuTPp1WxmhszrHQGrFZicwU2kMtOsrHkeae0u+lDNn/aF4V1Yraui82W2k2kqtlRbN8dnMcjpaBUZ3Vl2FuOstWLUlP4fS5UDOzz"
    "Is+1rvmFvGfUUDlQj8z6iTb40K8Gd+Vui9lnaanebG02oU6NaXPNWbbZ29K9UoVtraN9NXnodm+zlBphc70OLxxjl/4wHooxndyh"
    "v+hMxf5yN+HX53IrXhueeqF1KXmWa5OiHF9VFtNgIlQrjXctLhS+pMbiqJM7FkJ8OnVpd+tCv1mvi9tON76P1ga1gBIutcsLVs33"
    "84l+uxhPJ6LVUiW05vjVOT9VytlcvC00q+H0OZlScimJKZYKoUi2U2BuXDGaTqmX1qahlru5anXB9ZnU7cCP6XM0zzLb4bXQEEZX"
    "LtsIlqRrs9bI7cdSJSXHZsmgFBrz4/omWjzGK1GxOUw308zu0OtUpHR6XDiLPSY1nu5bkXHonM/XwuFi7tSIxqpAq50pu+NZCi8v"
    "jby8DHERNly65BanEcNVcxLYEhxbkYZ0Khf7hX6jXam1o9tWLbtZ14LXI5uu5k+tY29XFLlCL84xkeOR33Xz4XhwwN7Y8H6fGxay"
    "IyaX3XRatZAkZmfSdZmrtrK5XLKyDFbAnmHdayxDx2oQ0F8KlXeXM9OsKr0t20vs1vI2eOhPmkOgGRQHjWDqcI4VE4BO1U05MM41"
    "SznpeOszUuoiV3fFXmF0luLx5USIXDv5VeMyXl4Hq9MuusoxsU6+11Hb/DJdbwYigDbt8CmaFG+5YGu5AiPUiualYX+8ouPZVLBQ"
    "UkfNcTU0ZdlSNBJvLTpJqar2h011lD0VSst9pNQZBrbJeiMfafbES/ooBLPDYpMH68ru1GLGQDdpTXedHXuILXvDYqNcqg7L13o0"
    "HwiJ5cg4P0yEeh0pfqm1O9t0a71dN1ORVLxRkuqD4PLUaCTPzD5+SbGr3WhbbUlXbq2MrrMb18rn8vw4vFqV6/3NKZmT0zS34y6p"
    "WyosZrkpv5lV8rXKlansh9VhMRyfluqtanZfOpynp2SktWb4RqwaD0+SO7W2K07l3Sk36JzCx+xYjC37o+tS2edD7eB+tKrXrt3D"
    "KSVs0k1muVsv6VCvNhwL53IHrr1HKVQ7FTvXTjPIjXqJ8SxaTcqJVkPhsikmP7gyPRHolnmpFS8Jw1pcmPDxVX/Qv2yWbK832SVC"
    "QDfj2VZ9V4lPwIpSkRNVaVeexvZplh1P9nSfrWbjg3a3OsyOpESh0mt2Q/KqJNR2kcF1oArdWiwixfZTaR0uyotx7dAYlcMtubo6"
    "76+9aqLbAlNfHe+ZmdqINfrJWGocq6indDwQnx1XkUVNlALhYGwvqkBTWxZOgTUbphO3k6pGR8nLTdknmVOkExyo40hEbYUl8CGS"
    "CDIrtSVfS5EqnVhNG7WyHI8qwUkiGT5Eq9vEQIpXB12p1hwfwUqbnQQGpXh1x/GC0MuyclBpsutuTF0kL7NWVKDpafZ0GreqvUoq"
    "cVE74Wio3Ok3uulZMhtQFoNbZXg+BUerVbchl0MtNkvL0ioSrZXyhfMkfE2llAI9viSCF3aVVmf0/nJY7HnumJAWu1L5mtiExXAr"
    "Uucu+Zm6kOXuurqlo5PmbB9dDqah6qAVaW2uZcBEC/kW61+anLrtyZNWojroh2ut7ZIbpm/l3K6X7o+PajmudPe3YaRVoDfh02HS"
    "T6wX4M2lN1aVRTO777UGU3ELvy9KiwWf6i2WojxTw1wkTkfFqzhODsa3BZdS2OKksmAv+V5xAf5XU3rlxZiLRVvXGle8TSN0BdR9"
    "W8i1XQ+Um9/HN7QK0+z5UwIoUcuC3Bh39kNJUo5SZd2atAfx9i0EWKQYa6fpS6J+A+I5nE/fpCLfreYG6aicYy6VVElKw2WonJjk"
    "4xOa3hRbHSCCgCI32rHMZXKp8kpWuPTbp1qjIF2Dq1NLGYQraSbYH53ZEst2k4tQsBISVpGkWt5sAq2VxB06wfGmF4yUtptxpX6Y"
    "Vjanfn6dHEcvx+XkUO0KCcCOhVYimK5G2ek0JGwj4Qrd3pSrzd14eO1EB8GoNGHCu/qQuQGBdbmCD82xMD62rt3qNXUUGtlqrDUb"
    "tZRgP1bmC8omvw6w9VCYTUzpVHa1S6SFrHhYJ5vNcjmYPbJAS6Gr8bS8bI+b+Vg2Hk2dlj2mvroygrjriu2akm9cq9lFc1I6HTvs"
    "cFSPRtVkbrMdBXNZsB4m07cSN0pPCmchd60318VNcXsR83Lndtl2z8U+cywNpQHb6q3YRJxdxdO5UPM2Yta3RigwqtKjVaW6zV6m"
    "bPJQ2xavhxSbyw8PldOtVWICqdSuGDofruphOJ1OU72SEGTU9TlQzrdKikLTcvGa5ZrZSysWKOXpbOF0anSLg9Ku2jr2azzYcaT2"
    "tUNwFwpHBtnSorBZVcNrft0qXBLLaTAnxxuD1PWcC+boVXLTjURHca6rdELjxXJ5kZendZZX0z2gHl2SspAsTmPHyzEm7xKBSTIV"
    "XZ4mHWa4W5zX03B3c+J2o+SuH86uOw2pv09Gq7lW4DCYrCpHdkaP8/lz6pQWj9dlVqSru9VUWR/j6vjGjKZyolJucLK4Oi2rYqe0"
    "OG+442596tGbTXoTThTY6ia9T4SrySZ/VvoV9cyU2otuFuwmh0yBW5TzvVI4PgtGN3Ku066LR54dSLPe4Xpgknumc1ozu+o2doqx"
    "k0Cn2RM2wcUycuzGopVhSNj3lsnyOciXxR4QZNPoeRW5FduhQ4wtCK18Lb+uMbfhik/2DqMs2wAEDar1bXNX2wUD51lIXewrUaab"
    "zp2ruxLLrFad5vpUOW1HfTF+ucYrxV2k0CwPWnK7U0gcN2uwzV4lE9Hs4haJlA9jdt2oHgqFYGxGLxsiUElHdS7cjmRLYI3Y1JTV"
    "Od6MbQM3lu6vtrdcfDpeN1qh1bLRaJ0lpahmjzUhOVXG296lfWFWkjQZzCbDy+GQquyYwq0olZOdeGcyqjQmoVizFKoeOGG1mY5z"
    "k91mHD00aj22vD2sIoHRsVsPSwLTEffZY1EOdLut7hKsRQcm0LyMg51KsrE9tja17b5Zosf98rm7b4WuI4Y5pMKl06aWnfaZZbO1"
    "VveLylA+M5PDedFUxGt1dg7H20xknL1ExsV17TYSEnQ8tDtO92CxCrZbCWY37XdCwaaS7Utqv5OKDiOFoRC+xQu1ZnC5FfkLWB4P"
    "vUCVryQajVnoVjwJfH6Uaw/EJiOUhrmgPFT37CUwzOZTkdms3pttcodrqZToDwqga7Us36fLCi1cQ/trQFrTq9t4cKjGrqVldd9M"
    "Clz4fJ4MLkVpuxT5qyDd+PaQO3Gj0i13qaqVJsNX86sCN+CT4+5wkdxuy/n1lFUPs9JC3V1OrRsrFdXBgrmlzzsxu0/MUtPzeFo+"
    "FMGiVBvlw322cejVioWc0l6fNodU9HI4hqQs3+1sI+1dTG2WeunIRVVi0lpOqQWmNrutColBjWsUml1ulRW6p2ysHU+sUsJOGkTS"
    "bAXsz1PjeqpbPUupkERX1Uio1NlJW2Yrt1uVc3sI9hdgfNdqkFsWBk0+u99uGPW6CRVnqTI0J90SsZXSnMpsrsX1lleWj/PrbGCw"
    "Tp+a00m5Lk2X20EuDGbDbJOVb8sIe8g3VwGwP2OWvWpoHOfz4iCU3p5Ou00vel1MzqFIQNxwlXi7kayWUpV2fczJuUJqWFSTl9H1"
    "dOTa+WUhWYsvjlyr1xICVaB+1VObXU+c0uq6NG2dp6I46m4PodQxFZx109d4/TirNQ7jc6IQyIfbYJfATNbCequ0lGwC7Fsq3d46"
    "ANQtdsu3KvsmW421Z3LoVOO3tXqYze43o41cyAVHhcp2fxa47a0kp9f5XniXb64vo8ZI7XWGFRiEPLUO95XcRjlFNmDBrKZT3WVl"
    "RKeL+3ErS/c3tdNqKCw6/dVluF/nlvlVVmnKo8OpmD/TzUZ/O+zV1xduum0JdabSLahhhhvVQ9VQK5bjxGI7d92zm1J+VirOmN1+"
    "MAvExvJgH9u2F9NNjqfLpVRqtL4VdrVufDWLhxcVqa6MR419bbTmB8FxfV0vxiXpEFQvueImVB7Ss3y2UxrK2Yg8irXO7Jqb9Wgx"
    "lFrtVX5YDu6KrWKUvlWBQF5EwYI5Oxy3h0Zldg1duOL1Mr6w6dshfZ7GTow4qjZy9VCsmFZuvcQgV6mIwd5gNwsODrnCOLG+yFel"
    "GWL4dS8aWojRNtMPjJbyLBY7hoR8vCqDnWMrx04OwXGzznYay9J536+2G8tCvHHtH8aHSe+cl/JyKgG0a2UyrQAdTxG3y0pytedO"
    "KZ5exgONS6E4HXdK68U1u7vS/b1a4pr0MJUsT6UyuwD6cil3lmotmu1VsqW23L2cpHC3IEb5ototHrbjNH8sNLMHYT/t9q4VWlRG"
    "04nc2zX3wepxm5VThzi/m7Zvcn49utwKhd1quYuK0QPbCNUFdtRsBIN8fThN9juiGuw1DwMukjzFikoUCNV0q7pd50b1c7kZZwOz"
    "Yeqi1JnydVcfdeqp4kpMt/lLeVkrJrJyd6Im0pusmJvF+WLqvBDZa2B45Qq7oJI7J0rKSt7L6zjXKTcjzcO6vyhUG+UWHRK4dffK"
    "C534VD1wty4dHU72HL+T16teJSenWk2pe6zk81U2Pzpe6mA7u06XmvJid63yzbB0W23FWiPZEDu7wkEpLtuJazRfWndSh0lneJmd"
    "wuyhvI2dmWpICneqvWywnB+tN2ytUg4mxsFVdVO4Xo9XPjbrFGOdWX1TPjQGyYKyu8nrdH/GVfN7NluZNJPivlLhgJBvtG61dKh4"
    "nEZ3XDEbny1Tpdk4P+j2spfgdJoQm8dltlWp9mvN47Q/hubhvNBe8J1GfZ2X1kpNqDS6yqFayY9rkzFbmF3C/VkvOZ0yg9s13Gld"
    "A5F4ISZno+kGN5v0c9VdLrnjtulemw3wKT7ZDILV99yoz669yrrUBNtxKdcKCpx4kdbBQrufKuWqxUWz0p81SrvLLK2OIqxaC2zD"
    "x2qNDc1uOZqrMoPmib6OpvEQz8VD4VK0kt1Nw4naeNWLbLa9yoy7gQ3/MQXt43VRWSyEWCkv5jenfO8cT67r00o12h9IwXXp0Kvz"
    "fOSUqIyDxR03meYn3DXPjvlBNlou9+VScTSc5kaLa7+Su8X7LXlW20rntRKpB9ubTixe33OdXD6/EBticNPeKVcg0MaVshCs5cB6"
    "XwvRXEcBg80cz40me6vVBos0319mpcU0xwVj+es4u+YTvWk6O92tz8Fknzmwl/0yXNgK13WgnKvuG5NxIxYqBDprcbzv5jk6WMsL"
    "wWY2fW0sh9MDXZ5tmH64GmJCoWt+GkwM9/2VCBTgWPfcDEideLx3vG5Hq+yoFl2cp7uYBPT8diCpHAfbZGx4FcqhYJ85SYf1YdkJ"
    "H/qLQWiX2uWa6aM4yIXim057nJ9OB534lkuU1VujUwMKUzy+qoHJdKxv1FCITdyYaGwmJQeX2DRS3MTY20GcHcrlRbHMXMLpPpeK"
    "rQbt8bCTG146YpvN1TbJUfwQGTTrcaWojNlGYpDKB1IVepgI8zux16HDzXondmASI26XXo4rhc5u11jduAnTCo5qTb6XTzZvqRoD"
    "1LJeh7vkanxY7Vxb9WpTSE0EZlCfrvpDrsJdDo1k+aLkm/ssG6V7x0urc5sdbpN4I1RrSZtUSy52zsdCq9XK9XvhePeyq1U77eMm"
    "W80J7fBgX5fT0VqxXRGFbZoL1Fb58Do+iBTU6aR92/IrdRVIl7s0szqeKtts7RKS4vXdKJuKMbViVmaF0HrbkoFyEcqK4846zMe4"
    "2XLdnraWfKBTSIUXYaGQOg/L8o3p96qtM89sO9d4k4mp8UA/kRNvlzi3Sh820+FxF76C5brVbTRpcdYTF1Fp1li1h4GZCrTQ1rFy"
    "lNK1IdDT+ut9Z3BTmoVRjpOPt9tKbQZ6q0h/yp067VG8J0SOq9lYPg+U1eW4KZVVhW7tZmfh2MtfctH6sLdKVqfhpUi3k5FkrrJS"
    "L5uqEpXiar3aAXvk6n4auAY7g2SaHsaYzmolpaeR9GYbOSYDicC+K9bUTk6iT4PyadtLMgewA1ilQqfBrV6s86xQSgb6/cBqP4vP"
    "ps2TFOz0mtGykE4w7caGA/rVSAYdSKey5UF+EJ4mk63NucNci7nbLBzddyppKSYq9a6UX2+UeCnX7whCSqjF97VjsdGcHjg6Ft3Q"
    "YnsVvyxGY/FY5lqlci4ZTG1it0M82y+lg8dBmxlJjVIgW1eP9cuFL6UWk/JhVAuUhsemKPU3QFtpcuezdF1v0+2hEGs3Qsdde1Yr"
    "btiZXCmUYrXJrBC69OlCKx6fhvK76EDalMOnXp0LBQqXVrx9ztPd6ZWthCIXuhdXp/+HuPfckR3J0gT/71PkjwGmG6xKalWDXoBa"
    "OOlO5U4xGExSa63ZmHdfxr2ZWVnVVZk9g8VuIG7QzezYodHsiO+EX49P9sCubh/gsaqG6hgjfWMqIaTKyNxBjfo2PjDUG3KpqiTV"
    "r/pRfDF3VAOZx5s0buhC11I8d3TqcVVfvsO7jFVPSbgaEve6Gfu8bz+gFa0AeJLZVApfrVMCD8BejLZIghvjeKmNRRuvyKbagw5P"
    "KK+YZpu5sOqpeHR1D7xkpAGbGxp+xvlFx1ZjfxAavMsdZJlotb0SB7wrhwSeHEJzS2OUcep+NCAdie0THKIFw44Hqyg/kx5RPYNu"
    "zojm+ZCzbHE66nMkWhKhbwevgESZBzxyPw9Dd5tNGxM/fH+Wdwgtk/MR28htnkvkxuGILIBoVwc7wkPktqeYIvT7zk2vGWCyIXMb"
    "zONEDt42CXkzPAjMIVnZqk8cw8btbt+vMw12bjbe/4jNfcL7m4Mfx7Zx0LuXb5NFz4uTjsRHHtG392Qylp9dWDo2D+YffdXQlzDr"
    "InNIRpWIUHUH+rrtJSQwlvQ9QzK8nJS5IqCId0gg52ts9iARJzKigNhdNXkHj+nK5rco/XpuUS8nKXgatan3Kyl1CykYEUyXd2UI"
    "zwIAKw25dht5Qy6dbtslibjNApNx8l9K9hkmi9lLYquwt5FW/ObfdfO4CB9xqvzcPzQijRbo/gZlkpaID7IlaPghAZidKmcAKjqk"
    "Jd0EJu9tArgvz296gp9w4m4ZRI+8e18R3+NzwwJiQzwpKN3yYvfLVzQpbEDWAVItZ8Kuydevi9JCSvjWSdpqgRlyqZRVIYT71gK5"
    "mCME94sfon6+wloRhwRkCZHntk/uqY2oRd4VrpBAK8z2FuTfV32z5AQQS7GvlHZ8EnJ4uxB6RzZEGVnRUrG2lz89qUf4SyhEK0Tt"
    "6nHn55GFwxBJ4uIwkpKtwXdF8sg7DBeag3KrqGkok/A3Rrju6l3ei036lCVkqQl9w4lXiqG0u5QMepLevf02YyX3i4Ev49Igzmfs"
    "8yo2uV7sd4f8hIWmWP2g3ljhYUsbPkltvqCb4r375S0dtV4nQ/A0y36flXbeM1bgRI3YoVm/a+fS9Lb94M3aPCQ5OdRKc8OUfz/P"
    "RXsxd9JUwThAlcO0GcUny7481NmAyi5lJIbeyaYH9MB3FCdNZHMSJU5NQGNDljsX1NqHeCdP/05PpXucoJv69dEpZbiFgIxMBmy6"
    "ABoEL4hjp4R47dtjAhps6bYFsZ0N6zLJSHCSrqQbKuMgSIMXyDE76775PEe5nmFErmBUiH3UDGsyAuDbp2WVZrkRQitKSEQxu+pf"
    "Uw+70vqBbI/hLxXEeMrO9gvb+Wi7U21u0Tz4AGsWRecNlAys607qAEx09exke6c9hWcoSdOgLuNMZvIQkaEXzBjwC3Q3GMu8C88N"
    "/AC7DRlpDIV6EO3uYUIF0w0cEKMjJ2B/ArdukE55ejcKFxxR4ACjCeNBxAEpdGbSnN03kC5B3qPVTZNBFWwKfAM8D1/IGdiDCiV5"
    "CpGxFewzjIcWkgJbcBTBZqNjEAWAEMFoZtufOJqhXhfQw+bLFJVxWK9k4wSltOogImHgyEnPhnKjxnEI3mH2D19VTBkatXBKc+Sn"
    "PC51p6o0eBTEWsU7+DwolHT1weeE6KLR6V7mV2AwcZLPioJxC8SAdjSRYL3qVLvATXQTg5cfBTmF5fBIm17yDhWf1gEwy4CCSpsL"
    "RNvsFeiwRBp0eaEuHKoAKTcuEsC9jnlZXC4KqmbrZRJ0yDm7zbEwKaip2QsAZ8cyoy6KdsI8ok7d4U7SSoNlzG3myQVwgc5liwtx"
    "LlZXrwPdp5PsDbPifMna17hiCNPIZGCKK5e8I18inq8UDPyqgcsAgpgHV0G5psjFoCYO1+KqtTjcW4m2DHYg5ako6R3opHRFc6x0"
    "TFEnPFochbbZysQ8Cu7pCgG2OWOW4QVyAAzhjENlvaoiZ4RLwDwL4uPjifRzFlTYwind8uhMrCfn6xp2eJrfU+JreSAiVjRm5ZNS"
    "lGfioAALfgTLP8e7Bu1i1mHKNzzxT98IhiG6wy+1mo9EIPkoQU05zuZVaiw4R/eJo0jCf3CNn74M9cXvoCUbnMJBjjneBosF77ze"
    "dRWfW1l/xgZNVTMmImZU+2BhwVZ7G7i3IxaanWlnkyF0aeaTIntrQPHsHNHjFImHNiGVMDfUzPSG4oXttDOjpYKEgk+7pNYXvQLb"
    "Re2epZcfTnCQcat3JgELs1SLhz5N2o2joud5A2cwL88zh9arLcHOi9/xh/rY7WneeuXhNaLPzq2CR1JAAznsuKzypIdI0BQZlxVK"
    "78SOXGe5Fj9g/clqfJ/O4FY6HucHeWUlM0+fmQTBJMzynu7Xg7t2S9TF52epm4eMpZLQpDZ6Oy+8zUiCMtrXO3CPIawepO0DezXu"
    "i8vjwJ0b6oePJ8XhhucQzrdvixCmx0/86p5GRA+GiGv2cpeTnNj3L56lFVCZA+I9f1xjLaT0489it3mG6RKfXnt63LIR2JRvPe3m"
    "mR9TOhPF2zPgq+oVjaxecyTuAK4o9l61Yzq1C48+uEOqwQLC05xjwkU/azvVFffRb/i+6NTIz8q0Q4w4I0FKGleoz4FrbIe293iS"
    "NGbz5gPQ7H0+q2PDhCMdN2XtaHUGNYQQlCa0Ba1Fia4Ry2UpkWlXwEMmfVHiOqSnxdZddx9MbG3NvMN42QwNS4U4xCoPMqMq5CHk"
    "bgxq66W4WfJqOixyFJL0HNGX0cpite2NhM5HP8OPtVK4lnLNRSzz1cqS/nm9VE+Ii+Ck8eJaKartnzwl0le2mxxKyxvPWAXvOfNg"
    "dsboC5vw8s0brfHkouS810Z1G+Hwu5oKM8ZuF82eDkV5NJV9+o/avV7jjUBv+OfAGi7jtFS/DnSSxDpyJzJIhAIVaKl5RsUHKDaS"
    "UB5X+kq3R9x3lseauS6YxAbIr3Kpw1VD4Us235kk+z5s87KbgKQHPSNz7RbcD2Mnh1lZYyckceltY+kEa8emsQaqtNV0bCqM4QHQ"
    "xRXmb74erey7ndqChGEpVsF0hH4DL45kHvEpC0uuBMtUHl4KRJ2t8Ke/xqNpCfILh9bwMIydYznMyiL1801bYhb49NBXv4icY+WC"
    "MCommfEVu5FUavxYI/V58tFy15+ufajaQg5xoarbbdRihIeuwBu3QVUDqrnI42Q1uiWffKgZN/Qjfccr5B6JfA1/jgAeDkgTM32o"
    "QTYReGFni4cFGj3FJ4wQjzmPcTcQtHr68KMmxiThU1DgK16a2iBY4PMOFp9vCktXRt09EUyMPKbozo36IA+wg4cTztoHtmKuSKNT"
    "tMNa5OOmXU505BhIPjzfG00OBO+au91L3ebK22z2oQV6oH2pzYRJHDahC2s3cjfcAQvBraeDnX4EsI0GcZEsFzJND7pmzE24h6ci"
    "ZMlDmsDKncEK86iSHxjDFgbGrKDCmgzegBgn7e033rML4nz4SJ4E9Cjb8WxD2UhyuPocvaFOLNrlVrIl+QZIJvdoPUbw6xoY/W4X"
    "+MdnfJt5nwcBMfEDhVKggOoBuC1LjPBIaTy9xl4+ienHR3fvZPeE3p/2rhDSGPXKVrYYURR43cygPLz8ZxUpPdakFExMqn/Wz/XB"
    "oVw0AnQbrDiuv/u9tEYuOxfygjNVOFZ5xskbawIa1GkMDLojfI0WD5agNFqcwqBQR1ZFRpuLlW6rljJ1SKCnjfIkN+6M2g5dKcn8"
    "PTkOYMKsAkgQS32mYuFs6qX1gydBUW8LDbQpfUxKN79YCRsvng/gTcbmDA1t2zVZ5HjAEQiJPPaadWsBPOYkTD3IXSARwmgyztSf"
    "clYnXLolRG1VY2iQbcw/9sATH2/6jtz884xYuMlmSOhinHdFU4+dmQAUITUeun9nrLI0kWyq5gyk8bDv46ZDdp9i7zopvSqiwKC9"
    "qmsSw1PIfKvx87nyyCv9pDmX+6dFGwNN8tXLL6mOvRDCXkKDv4SUQDCWzKogsm2bWkm0uJ7F21qJ3XzAjWmtk6mpKHHAOyW+UNJ7"
    "o22ssp6xd/M7UaR5qfMhLtEmC6FMA7ep1DZJoXfi3YsOgaRFngJ8Qnt7h39qxUKHjboaDmGJ5TBnuZ2n0I5p1TqvNVMVPNvS5kUa"
    "bHKWJP3mulcdkIr7kR8auy/Mjk59dJsNyuVx/eA6vn/48tY0SLo0YNUyfiJD5/wiK7E5QgXpnJ30dO1pO+Ajeo0+lCLTihOHjtvB"
    "XOTyylp0Hc7qyUv5W6hQC8q3GtgxJckUMExWhJspmeoxC8YmZ8EG+WNoxDYxLwBPPaQQN1k3ci9+DO9zBJWsTIKnV+CCfw3N7uSB"
    "9R7kAuzLILYYMy5b2iNDin4+tsfLWDYG5nFCE1+dhOuBVhzYQ8Q0+/Ta6wnkRpY2OGxfOFOURu9XPPpQOyWbEy/sPeW9zB/y6YMl"
    "rK4qz9vSWO0VZMpLSKR5tSXPhodRxuoeRaHbmvTJeT2Bmw9CzLT6pkablBRJVwMH7RSQFOqNIWzEYNY72T+n4fXWq3iAH6R48hXO"
    "w5w+nIhgXsFMNywrb8CEpx0kL0G3SyJjv4K09ssPS5xG/jZCE8HPa24b94FabCBlYeulBpaNFjSEDPKodvptOjhD8KD8McUUI0JJ"
    "O6NWfn6UnRPtG/DNpxMCCgasNpuEHQnKiE4/GqstJLFqHz0SQxcUnFrSQgfruQ/x8pqNAtADKrVKFR+gJxbPyJe5xSTtxXnC8o7Q"
    "sgrEGH1mtvKsw9cdr/VeUyhsq94lzJmlbYRGm5dvYYJkqdPypnxLY+2+4bM/FXuNeaHuSQjYOFqaEcmiF5kLcRY/iyITBF6TEewQ"
    "baR4zPPRIWo4Zoqrfw55ZZ5AaQKfbtY7wPpMQM/TcBlB49ghA7vzzl5useL36gaJW4nXqJTFpp6fj0i3FRpSC632ThFWTzTq8kJ0"
    "nZL1qEk91bmEkTleG+hSMNaPBcVZP4+S4+vrhTErtqc9E4N3cBHvUhQTbDNoGNQT45PTz9GTc7QP2vqGgHEPFLH9opXhVQPOPk6r"
    "pYbEubKMeHGZ6qzWVgEfqkjYctPtO96lucJ1ELrpreFPI+pJUdzUtrq9OFV6b1aXutYloE1zO0MYPn0pwVC7Jvs98EvpGa17Yr9K"
    "y01MxYIay7ezVVpDNhYuE1yCa7ghzstsZ8WW+ysltpyUhbSNcWB/YWoOZ693y8AsdtQK6RVNHaAnGkvXBV53MSfw7xfjzPVDh1Pj"
    "CkzWv4jtbdo9yBToir/8p19h/LMxirDOyrc7pSXQlVoDK9PGSfyleLLz4hrKKSdN9uYXMGtWJIklgQYbvhKr9L4UxfT0GyGpdkkQ"
    "0X7n0Ze1GSWr8mExQcVS3miTiM2e7JXruXp0yOxR1nKeqCnoHKKXmrc+QpqjHnuJU2HQuH6A5z1SFcBkPrEQLCKKna7EyEYzEiQG"
    "kDqP3D0IrS4UGPG78NSZ6o74F4rZQb0/QRu0adN90S6hElPnzaewhylnDQU6TfMjkYYU3C1gAWdwR2/fxFMjj3xBNDNdvZQ0Vh/u"
    "a3SmzmivRjtiFECaZl9K5oPRQ4eCa/108kZ3ZLtAz6rG7BFrstMux+BiTSSyfVBwWhPtUS67/FS3aUHZvj6tA6JYOpuMU/bQ9AGQ"
    "2pPdwFuH3t9lfOlz2K8Sk7B7ZZ5M+OhYNVPEkIih+eV7PcO/qGYQ5pcrcKH5ObWI0reSA1TOC73pzt3BErlwxeL+NNWPr09VVRfU"
    "04Kl6kwtdLblem5sVYpMhWC6byGFBrejt77+xlTeg4aDnci22JfFfe1kCQKg/Dgv7gjRPX8JbK3RjZdMYKHPUKDtLsryZVJSMKUf"
    "D/kjYGTkFwurbynPDn0pmW8BRR0BDU3ngstjV5ZI3mIHMQ1h38ZZuEs0EBzR6HLCPu3oUik/bpcl2tXNMWLVdUXdlg6RQ9fq7Ohd"
    "m4VgyqPlaXOGyMM3Pjx7GVrJV5BBSG3YMp+3SB0LEX1eaHwX4I0Kn1A/YAK9Kv0uI4DTEPNyqOpLbPfPoZTvUQdEZfXckLJgxeSZ"
    "cKwrpNrIB9QEXYOuIVqQzofYPnXQl5jwEHFly6kcFQuhtIQziaFQf9EU2mbBFdoMhbxFC2hObsAcdeEk9dMzd6i4c88DnHN/nIqo"
    "8dwUU1xWu4xpzgrERix8s1EiwjJ+m/iSeDsPOugoHCS2UfDk7Cw+GbCwL+bYt4V+mnCqPznGsM6+DwxH86nN09Dh9flsk6C4SFhy"
    "TzIM9HUj1O6oVvyR4bPzMc4IQ4NEvOSiNZ2ugWbiI73tangPPn2Hd/KgW3h+0If3PIQr1odGCHBe7mRtxKDHc6zYmTffeNZEYRzJ"
    "phehOu+mFxhHJgvSBCw8V2jJMAtAk1zHuWsGs8wVCXUmxORdVhTaHJrLlXCxrA04DLzkPIUVHcV150+C4ZNSrTxHeJZ0Vgh4AwdW"
    "E3z8O+ASYTnvuLePqqDzgNn5rQb3oU6SVjSp7fwC3wOf4EheucOkovhry4nnAzeAMVaaMuwCoZIeTpQR8DCYtFvCPvKxFgKA41gC"
    "NKzsppc/JJHtHsSUd0DMk/CZa+td2NEY5YjlcZdne4Pxo5d+Xvwr6psQBffXkk9QQqfxjXHgoJtrlnzpnCkdtUtNi0g/3SfxMYFq"
    "luaaLkOe32yR1dDciiov1l8O3BRREVptmFlkBBbSzsV4Wl2XxasfToB2lrt2NHQ/2iqIrL/pgzFsUx5ZJqIcKEMEFyWq4wOnQSvt"
    "MIWWUICwlkhaR7kQjDiYj6vPulF/N0tPhiVgCjgazdzyiTMiB3L4ThnI+KJaIHWJXCAaJPafSxFU77uAuKRBHVdiKUvfaGj6w65n"
    "p/vwjfA/cYD7LiVXca2Aw1Es1/QONFW1xPOByyd2CBnpD7bEuNSafnS6yqDnIyw7UEf6h8S93WH2NyZ7HC+KC5g4JB+jWESv7aQX"
    "VuAmAsKsEvFMiaploTHWgBuQ1IiSxmknEGPQu9IJU6cDcvnGSBEOYPW8C5/8cyqQkMv1ClOupK3t2wkeQI+7/r4+ecxGukvmOkV+"
    "yFWAcu5zG/ILEVRbrEEqlnJDV1O0fIzURif8sSpbssV94jpuoidHM7GUR8dPdnQDRn6995DxQNAAd99Q6BvWsxzd4bhD0N5sX4SM"
    "tN764YKXzfVbGUOLf6GVnD6bKMFexnzR3A11ASaqaMMMP0+GjOrXBshh5OUgbSaUivPxZ16ISd+W1mGx6ZPVT36UAdHEnsRWSKsc"
    "s5b12bbdolnnHfDOpcduzgLETiO1mj8dyzjGCtvKLSH7qUZgGDWAeW0bnkosUZVEXWy28QSMC869AYuQSYmq69PXbfumchqtiX3Y"
    "eX8wylnLnY02vVQtaMkbzM4u5sdGYUaej2n93L0SLjmqKppSJHpL6CO0GB3pkegX8R49WxAxIqs5RPXxM50m16zjT5iBpMZZBWIA"
    "L9JkinrUmgs9eijesWy7DIB8E/UoDK8+EvZHgVRJ0Vdl+Ty1WnKwIyYGMVe0kCXiGpn2MTSnIXa98YoqFd382yvSzrDo7HnDcrLs"
    "qgu/4wIE477zAhJ3D7iFpAxXcTg9VrAwREWlgLlJnpxIm95Zy2Yw29uFKtiBiToeSVlh27uCUE3v7oz6YE2xLVYTyzxuS3b2Lc4k"
    "Yj0zTwaSQUpsIPokjEy76eeGaVZkUB6ZTIPBfXDEU2oRPPknLGw55tCtV4i21HKXm1I7mB/PrS7UCW0Zh7yh66VwSV3EsSBs0Kbe"
    "ZfDzk5jRoN2P2nKdz2I0yKwjLaaXI/UQ2o8qdNjOczLrp31QiZ+CWz6hHORQQvBwYab054fLnLXYaQ+Np6wO1j+fCPIuvSSXIl7a"
    "x6BkPqCdWIvudHaFvXyX2IAqVucVwVGuRtrhgmkXXZ9w5/PGwt7vz2mock/LEZSib8eWIVgVhY2dTRdxssBiQkgiDxQr84PLG6YT"
    "H32VoSlNhCDUMXGJgTfsBftCogNiLKU0wJ7lVE5xqKe2HVdF0ryMTgQKzjuP6yxdPwN56tlj2l0Iq+hE530NwLAFBJeVJFR7eNKU"
    "KMOFbXrdoxHLcy38OXeI5p4Wh2m0ZjUvVz9M8mw/XXfYwnHXOBRHA50933mMfpkFNUGuA4hPQAkA2gEQadcRk9vnakFGIOZA44HV"
    "9o6WsjE74hrAB7y4d/4Bxu7VIj2/VbhnJdJcjnIrs/ducbNoqfAAzYqA4J9YAuvRgI2YRjuB4rtj8ojusBimgiourK0jERjo0ZhI"
    "Jp6f113IDrPCklEKF36inbNGyZ9xoRLijVNbIrx4NShJ7Gm72ruO3kT2ufixvna8+TQ4kGtIrkf0xfoZgCVzViG6tBFM7bJUm5SE"
    "/2GmxSH5jRXAyRSKJVP6BDsviv7Ul0fh7LvdFLZuomOjZf2krWHRk0+O7DdOo/f2QeIBpJZuzfKIq/auOKlOXnrcusJvQGmHEePE"
    "j+pu5Tp7H35Th8QBxjntWoxpwVX14xWstV7/4LWDusE5X0z19lN4pVGTRmBRDwTvunILzJjt5djjq3x5TB7U4ZXx0WzM1jMZZFN7"
    "T54y4XcNJnjFTr2fWfUCZyE+C6Olel/VFh0r7iTSmX5DLm1p5nUU+h9EeUt6/Jjj5M0XFbOv3sPIhS2I1m11H80KF9s4Vec7ShTp"
    "BT2CKHZUizeIcMA/j+EFPx6AdBVDCPW7o9FqRuKuybfxUDYL0a5RR0esavvPTZHI/g0aVyg/MWRASrvCCN5/wk+mhMPErFK2v2OS"
    "Ac7e2dJ3VK5sSpopqaxqxdz2c+ts93N5s4FR5iFZliad1rirDWeUdjY2Y3bctYTX7HFDV5Kv5bTvirPOHqH5TlqAP67NeePNK8Qq"
    "s2Jkew+SN2Q4Qwfv0tqorXrAsh8yzGHMkUbGro4D44V2GQaGMZW5u9NqDVnlotxkE/p4WM4jpVR1X9LuKqSSfnE6FWRMFflYHJFE"
    "4S8EZ12fT6ViIuzRORw8IWd72ru3vOLlQJxgHubCf2oaMFtzGqa0VDYrSQOglmGAlR02qOaqplLh2hpuhkuIej1rkqKlhXrQ5TiF"
    "1pZVW302+oIvN0oJic2ePLM3XoGzAJIAk/NcxwGYPMSafUoDP27nGosL2uQEeplNOwCx/2blVvv4Tqg9TjoxAKVfMfWN2k4VW8nC"
    "0I0qwnY9lUu5R5XWebgjNglhgHYQdpk7aDpxV/3y5IM3atp25NRgVPE/8eqY+AfaxjU2PnuzS7x3EeoVw5ES6NMGBAOA6TbYb59E"
    "v0tpMFtRpMIuxJ9f5iPi5ZjJKZUiiK9yxxLtLMzlNC2oJSFF3LqgMwHzCelxxDAbkadgRop11yWnJIpciozfhjR35A4x8XNMRENK"
    "mjvwrCQVeML1cZPDDxGEmwFUIgslhZOcUe8H8iVjeM2l/vLc3eRZ9DAsDBPrjczwrP3UcYGtKfX4pFSyYWTrflYxtvH0UR37iqCr"
    "3BxlwdnPQRQLKPIWYU352lc8kzFYt+C31BSyC8f93fap8NXV5vpO0kyzW4BgjCyL3Q25oppgNjBkqUM4ZWDhgyN0Wl5kEhOtT9qs"
    "coRZWBp4v+Qg3l8ecV5yz0h7Amzw2HOdTTV3rSkCXVC7I5pidXaNvroS+RN30w6QV+6hIcajahnjVXzc0Mw4KyeQUJGFoJGzoQLh"
    "zreW0QT3qiDI69FLgMKUyxHjZTRuz1HIvZcD2uhl65kiTM0F+ocQaHaQaubEoMtDZtXOgeQh6cjmA80nItZrio5M7CbFTCGfSsD8"
    "gEGld0BXgbjj+Gg/dfXr/1O/WNwBi9IdducQwqygNycSj4OcmgirPpO/pUui8WdMJC8tQTBb5Sr2FVi8W5NkY+ZvN2FspvB9sCyB"
    "wabzM1DgApnzdu0UIbjDeO+4LsMTjU+NvT6rqWXvq7XY9NbVicItcoAFB1J4MjTn3Xjk01gvOTJsksnOFTUGgxMIANwQHTu1RsVU"
    "U7cZ4oVQh8bh1YeynhDrq0XdygRw47kRO8qDumGJxb/uctDBlFIIXfiwWlzwkQf6Ejq0bbqpqpjX8ra2O2Ayb9kus3MK1LVcTpSA"
    "HvguoRI6HWsRCaqAP56gKNaW3z2217xyspTPzwFy0A2qBUs/oXqGrc3e8F35qNh11SC0dPgyIEt7R3LMmCe9xY+jbQThUsgd/DC+"
    "lnyYCB67IytQz1qGyHm0RghXKxewgxm+ZATcNrhOhtFrmgU2lW0eiE6p9NI45bKLMaOc4OuOmQEykgqyzkZ8vJohXXAm9PAXUb+v"
    "HH8QmBFFzVmz4DXY8ieNt+x93Lj5rp1AyCZWFd9kmjxRyKQxoBwgZHmJcPGsBp4QvLwVmRbyBoejNKV10oBq6w8TTmfHEHZli8BL"
    "0p+bKaYKVVGZRVP7VFDnLlC0vYnukOEdkBlV35BP0kFwtQBEm3jxD+g9wnioD56+hRycP2gXNzhjri1qpjZ0CgcHnZ0icNslzmA3"
    "sRZzfT2z8oylhQFNakr5oxGelRO0zTJDKouKgrWAbh0QVOrVxTITC7KBwY1/6QdkNb2EVt2DNkIhVCk7m8TqeOAQtUHlUzCe00it"
    "fDkIW4XQxQUFB9cSm3EW3qljw65vjsQzCtePkO9x/iu4NN+TTZ9z3GvlxLzJMSojk9VOWzerUSMmu3RXeBqEsZ55gxVlRxKGJm1G"
    "zmTmhlpI2Q9wHbNpvsQStCXP1csTPDPRfqPaSSkkbxjoJ6iEgmzDCTyMYqQGbbPGE8PfD0azdWcbGNZHCnAqsqs6PkqptppsYiWu"
    "qOjQYkfgmDPZPR+4I2R79/40tWt9PpzBge9QWJQLSz0T52SLi0aD8u+YPkFWvwR6Olgu6NJkA6Or9qIARuN5d0VMW8GQCJNO1lkd"
    "J48Jl5XXjjoCTV8/J3dNp8bVDiCjD4p9GlRTG+xEOhslghwKHnEIhfPLuzphaJ3oXsDnwoXVahsUlEC2o4ke1iC9UppGLomnMgsa"
    "LSz1OS7hyOzzpmxNh506q1lHt6MPTD/dC2wJjjAYPjdW7y43qztdc1SpiFzCTrPDWfhbyMdGwVy2ARiGZo2cMhboru+U1OqJfIxQ"
    "JuazlydSNs4e6IJHx/FqCdXan6AztGGzuEOQkMi1UChkFZ+PfvoHXwPm1ZgRPeQEfg7X0+VbWK/TfNYQQgpT6vnGRZSkmYpZ6OfF"
    "6+GLhV1qiwlFQNPKcJpKNxOwu96VpGeqkr/td1I5r+Qu3ljuSdzpiZyyKrCWTPvYWy0uCC0TM73F6O1a8sjYZ3gnqIduAZXisfly"
    "2HqoOOwDL8lnQ9h+UpJFRNFkebiSHYl3qlgV9RyUDQ58AVoezEP+eH6wOpPHoPZJS37md+lAORqeDU/8tovVrEa9FD2aD0LLO4A8"
    "G3fDWdlxvHFb0Jd+gK8i5BzGolA9g7OvfiekN4y9u70kuYSQHwHPJB/v89rmBnhA41uc8A0c3JAa4Y5iWiLeaoO3zTssvmafUJFn"
    "VFtJMII8FpsjLEDYy7wP64bcnweiFuJjk/SJSNrI+AjYS452V3DWXj/s1a9RT7pG6fNJrGJkQaN85Inx/uDzw5Ey9HywOV0b0ciM"
    "BMBvZdzflaGweNtxIymMPq9GpnLek5Y5SrzA1E49n923FvG7IrXgseF6OjEMv2NTBE8HlDxBfDv58sgB7t4IvHc+DFEsOvCGDZBZ"
    "Bjujo4V4lsrQxydUzQI2VBYCUhFyA7AaDt5XEJSP+OI3y/f0FpnfGt7acmcPQEJ62Hz6S+DK6sHnbnWdetG8tbyZTXqsMOs4PR9j"
    "YhErGarttJrK/SxsyzdMWku9oRGdUbQYdrhTi0rA5ACf5FOsveKQW54kBeZUgZa8vFxoMRwspy3Y6RGPBwPvVJQ5Bgt1dgpy4bB4"
    "1UE9sjRVaulRZuALgHitEA/uTrcbpvTNKBvTtrP7TlWvrBGf4RzIPC1sJU9s2EH0pjVZLuOoUlOcXFNSnn7kvWDH/B0fuBffJAXn"
    "TFL0ylCcVuNCy7qaxkYzTS0E5bazvEdCJQWSpH2Tx1Yja93Nh7B3zZK2Z9E8y0C8wfnizHW7iFMOZHfUCQcJHhpWpjdb/UTWAQoI"
    "V6MsyAOlTra77ZQSqEFqbp0YeWJpEWlfEXiai4SFI8Ibn1WOKWD/HixtbKYoA4fni9SfXAi/+soNFN1f7+cHnLadPY8tMd0rNx9C"
    "a7t4NlPS4PROFg+IYt9vWiWQZ8GEACP63ky4J+xFuBkiHGNBl7sGV/c+y3dfTDqrwpYhs6iEL7SK1W8DUe3hndg9FoQf83qchMfB"
    "oB+R6YvlkJegH+QzTR524t6Rokw+ZoAXHK+sLs4H3YY8Pza3dXI8XXPmqY8VA5oVwY+Id6pOR/MCZjw92LJVUsbrArsU6h9yyG+6"
    "Tp2aTUYeKr4RiNS8IxNu0Ke/aFRDJImm802XSxGpDFJ4nbud5Q5GyFH2vHw9VrxilZYxXqVic1YP/jwRG/rYV9nqpCbMYAtPEmG8"
    "tvo2PHAqsar3oydi1e+B6V4Im05q/kgwV8tExHtWqvE+ogo0BXIG61nkDwi3ts9lXiqpH088VmM5wkoEoWvhMxh40N/ugJFglBPJ"
    "7TTK48F/sjrNgLue7vuCAQ3c868OlR/J/kSyDgCfGNg3BLBWhx1bcXgRAYC/6vrd6cisFp3y4BJwFWiZFxB8btSAlqeRznCAfh9A"
    "t68C1hnZECCHvu8CTtZ5JIOwoIGXZytnffK9ak5KDGey0QYOm1EjpnfnDWrtLkHf2Yz04JuuzeH12MNdbgnrcFBj6wc2DS9ei1su"
    "CKwh6SPGDcuWDdiias5cM1ixqKsw8LhArwLqlAx74SeKb8ZoFMdZy3esd6GcpEEbkArYyOyIxdDaxDOASBrSTwNOwYbHk70RRr+g"
    "S+CxDbyJGqvmVxNRFoktaVlDGgVpIs9teHjYL0Ly+9li+hB08JZ4e+mdD7sPTOUbekOPz37Muc9uHdUcQjfnbB4X6mUY4PzwQJId"
    "o5hMZtSEJVvWnn35nAA9lfKujeGnXzpNUcOhNXkNW77cM9A/SmXW2ValHamT6BhucwFf2wIr1uvsdpu35OEGfBA75+C7fSgLZxG1"
    "9tZ7O9HiKp0wvn+RODESb8GjFjHg2gfAzNEmPqW61okufb63Emfr6Q0ljjzwdqZFCW+UBBWLti2KOYSePrDVhIN9QtbuLstDOPeY"
    "m+4O/5OupoKbVPTyIYcn7DZxBy5BgBkI2jpegfKP7DHDL5LK3Gj7mCyFky/+sp4LqeLNAr36lH7gJ6DYgfwE0RF5Ak8TeiAS3CFo"
    "6FYBFLzEd6ohNB3XC31+yvtnaV0pCd65RO/MYdB3MxAhjsWJqRONajO8B5FsZ4Pz2k6BWke8+mJZpWN0zKr0IJeiryiKGBhlxQeP"
    "wm3RHVSPRujnAWvddrzAA2NXn/WIq1pNpXkWFn3WAZZ353w51PWe8P61vSUKQJ/XbfiD/9qJvZ7GidSy1Hymp7Fx1zA2S8YoAt6P"
    "wrW9r4KcQuF61/mZDxoXyZ/JOIaH6u/mbo+TBj/Tj9RmJUYWK0BIho/gA+tin9pWZ70BMfHeyEHICcOdFYgx0jnVJMtWnp6slw/b"
    "fjE+pNZ5+RBULdn9XXQifYtBar4PJS9pzRw2mvgc2Vuv/DH9HFgziiQuyq1xeysTo62t4Mf2mB8Yk1RUv9925ZDmmT4hM7zT7xy6"
    "L0FFRAXFw+TgSVsum7gCScS32LJ06IruWWIe+3OgycWb5SSSZ+a9bujMD/TDFUE68K99kRnLGG8343nA9raOlOEmRDzVmPpEba0U"
    "f6nJiOXFJr6uoB0UoZBFLlCkPDuAMUwAvOb2dFxOe//EY1RXrecYJ6fPrwF7icyHb+n2kT6YDjzlg8xaGLdtMqdq3wOePh8CuJbx"
    "YdkNprRAYnCXnutIli9KozPjfD+XphlIopo+0etOzs4HRxCIr9c409zkOT7J6hOta51RNzqHt9F/XT5W0Av5NP212e2ZZJUeMuMO"
    "9+6ivzvzWFmrNj+KDoHHag95p9EACw80h0x2lB1nt3GAmhwxR9KFEYRcFXnbDeWx0tdti8TNo+YKj6khnHdvDqioxCMKudxmPAt+"
    "bkDqLZVfn4frzvfKDAJHF0jYiC6Rvva3AfIK9WxnSXxJl3smqI87QK/6nRK/4bR6mS2TmImsPZi8rcj+cVABv4NuiMy2OC7HlapD"
    "2YzD7Dg0shCuJWnPIY7lt62nx3Jo7+O1tVL+Ngr57V9ZLmut+wJfUYeY2VTtk/O+oowndQ/F3xMmm9MFSQ7rv/fRcGL2oQlwLmHe"
    "tiin3gI4BuqjXi2CqfeIq+JPoC69boVRX+45Yijv2Be/Ai5ll33n1nhBu/dSmDkHC+qprHuFBBXqiYcx+hSSEtXsXyiF8tNrj5fq"
    "hkBCYw7EQjZa2eLtOKlohhE3BFHXRzBIA0eGbjiiyt43R13qb3TX27Iwo4N2i2HjLCTT0907qmaI7nueuNN8mCQfvYK4NnQhS1+L"
    "3RrTkcKP9LBWPRelN/GcqtxabhhKZ6ZJ8Ch7xPHXx/LEFDxVOZpKcq9sf7GfKSXYQeiTqtIZKcTjzEX36QQjFNcyjtGyMw3v7Nz4"
    "PJfIpJtDfpRbzDpYSvNwBB4EivCxGKElo4wcYk6k3rk8zKl89Wd9SnFniU84YnlIv6PDbXRY/4HYqENP8cHsTr8rNNNaZA6BiNaw"
    "DkpPoOmlgk69b4Q/GPYKs+VzW1BPzcbiyb3VXmAIxGyPaNbpisG5QO6xbAtzj0Qi9evd9kcgSQif16G4BIcyGkRv3cVGvzHD/NnQ"
    "6R2ne+Tjn0ZkyBY+CP5txGEKXdwHT9GJ7tDRXLVKQjTjwk4wV4QGmTQJLf368awOABwwnqaxOpuEivBbIK0/WZZFrvGBuCeFiShE"
    "GEGqX1YPS/EI2HWSpU8Zj6TGTUDCHVfNIlMCywyMzWA9nndkr3W747qVs1McXqt9YyhI/SA789ZccCeRO557hNA6JLwnK12fKgnS"
    "03O3OWMC2t0jI1F9iJIcBleJFvfB8NbFz5aMvLadsGUse1mK5PKYm1vvleSEmYaeDq1qgE5xdfShZd3jr6Nmzb1IxRh/2CLTuZNA"
    "oUPTtseOsdCj9oXd6vkH8/oscXJKINlk/YVtkMrXIDcpPMx10CCLBtYyTboWinwArtnXD8WYDzInDhBUI7W5ZPCi2zLa6vEMSUUy"
    "palIEFINOR+YCCHeeRW3HDm+y4ODejuTyVSUn5v8jSheiqD2vpdczQluzG5phhIHM10QHsghTvt5LS3h8UnxDrbkWQtTAcN6RsxD"
    "idaY6dBBnCF0ytV959jaw65GTiXtVHvP24JzT0mZgUzAlppT4mrwaNveEHkpGNzNSB+k6XbZX/VFvYImM4e2SWULh+T2EwBvV0Rx"
    "gIJBZuTIFSoYwCTzo+/isqJXHRv8Wu90vheywGrOGl1a+6FdtCvxc0YhyOdc8b1+v84AENPkSDZqLhHA5K0XDGV9AoR8pdoPH2uM"
    "WJ/faduujHsdEmAjVoAHTXpMljKCz06mlXm49O7QodmS4jBhnAp06vLcPEljBItD1gdZ2xjz9pAwWfpHhj+v5lPyD3f6zLRVrWJJ"
    "B5rKYgzjNRWuyWypZUIopdbDqBVlu2OA5H6oYLiKI17JuhYDKvBs8hhe6Kii5g0n5K1UCXbJYWzabBv+0LiUrTkV4eL7tcH1wm3Q"
    "8aa4WHA/R1Mb03EV4/zJ0IgYwBvni/xLb1ZY9KGOCcmGAZo3gAGQx8KxQIuNIasQmzWJnuxWY66HzVfYMrfBnb7NxgM1sIVeUQ67"
    "dxK8gzcPuE0KD6iXJ9jlEb4T83xTCQfQZoVa5jsLICPllDDe3ZiCSPlOb1tJoTuDMQ68ZBlHsySZGsWsZY2RS+w5LBhh1DSxJlCi"
    "apnnaUBCaaijCKYdmDFqHgoh2w8T6r2sdD99Ug4rvkMP1p3d8/gkoAOsboOHPS0H0pOiEeZJJQrMjVuqpv45sf38UAbP4jcHxHiR"
    "tMnGQbmTPQRwHM5PX79UsI6JOaT3JD47fTJArDXw3cxAOlM22PPBImv7LZ5kdQijHPQuDQPRzOkd81mzVJ0PwogUMkZiuTNdcZo4"
    "frPO3pAG/oEcwINXOZYnH3NjZnTGCH5GKkmc/82HSf7tpz/9F+ff4uHH75Rh//IzlVjcN2vb/fS//vVPqfArvdj3vl/JxX7LLPp3"
    "Q8f//IVX9LuiR3r+I87P70yX37hS/45jU/yZg+DvWTbnflrE/w3570RP/zszvv50/xf53z+m3fzpi5/rp+/r+Ebg+M9pSIs0TNLp"
    "dx6775ffG59/wyX6D4bj3zCT/kMC0e/3t39fy3ch7o90RX1y/oGmL5E/1PP9mf9A03ehP9Q1F/0ufjtePe3Wf3YQ0G8FX8N3rr8/"
    "EObu3oldl6Xvfud8vySZL7aR35f8mwV8/VmnQu+TdP4DcSZJ/lBt9rcqf2Ge+z7hG3vg3+1YGx7cN+rGu0ZZ5n9Mj4v8r9uJ42ZN"
    "Uqnpoxvxf7vJ72zD91XI/zk7+q3wH1nBr0f7n9T6JfoHOue0Sb85/dd+/Z7G9BjCLvnd574D2xfLy++RDE/9/p8QsdJvZKG/x3n8"
    "q5AS/2oRf7fun9kX/zR9F/yKTd+D8u8Y0K1XSMrf8Yev4536K/09NwibMu/E30r9fchs0uwrZN57+gdBE/pFSP5t6PxnB/SVCX4b"
    "Qn/PNH7xkd+Nl2WS/N6T/hKR/8sfkS1/3/bfo1r+D6ScP7Nr/vef/sv3fDn/9D/+EWvlN2K4//Yvv3DD/Sz7K1le+mOYJD9z3n3R"
    "5XX/JyqS20eW9K9avpPb/APat58ZqJdf8UE43Qb156TfbyDQpkt4b2WYf1GN/nbgp69L04ffeNXSeEpv9PBz731p+j2dfvof91Zv"
    "+V/+/WibO579VCzL8BcQ3Pf9xx39sZ9yEIEgCLxFfvrTXiZL8RcE+tPPBPf3q61Md/aLYB36AfoB+fr+6Ruz3F9+6vouvQ2x+xZ/"
    "//t//2kIl+KnP/178pefdPiW+xHBORj6EYMx5FsDgtAf7jaJ3y2cwin45xb6gfEfYYrGtfuKETT11X9fSe5ukwRCfrVhkqB/gIkf"
    "EZTEftvG0e9av8sTP1IIinzTSyDED7+24Z/n/SIPf7tqt9z3Nvnt+rXa73Lk93n0NzW/bX/dBvtFXkO/tX/Vx6Ffy6KwX+/3a/vn"
    "9fwq//N60W/d6K/Pg/3t42FfWpFft0Ojv23i/Tjft+uDcr/0fNtQkr4X+LWx33b7h5+PIPjltOJ1+vKd25366ac/fZE9/QQvLTLe"
    "seR/3BbSCf/G/IJWmS8D47+Z0N971v/8n//ROOfbgIcvfsrb0v/9W0hd/te/Cfm/LMIvlHj/kv6p+9d/+79/Zpt6/cvyr386039h"
    "wy8OrvBL9V+5w74ICP/1T9PfecE6/EMf+Or+aR1+tv+y+9X+vw3cnrd9Y9v9/97+74O4D/brJDCYpOH7oCgEor8sHya/We5taThO"
    "frVpHP5msd8sEfk6aYLUfrFU6lub/tWyqS+LwX+xbPg+8Nti0L9aNv3NZDDuF0+hv4lhP/ziSb9pf/O0n+W1756I/UjBEP6BSe57"
    "+7bzb977ixffbfKbYX17wf1sbd97fzXOn+f8tf35rlb7bs7kr2v8Zu3oX9f03Rvg37S/rB75Vf67N+E/PzP+s3ehP+8J9av8z3um"
    "/eKtv+zp353J7znGjC07MX13jPLvHeM9/JFbfFnfP3OK6f/cKULh3376v364v34c/jyE+ReDWz/98O/fur6+knIemvD8yw9Zkx7/"
    "7dfub4jii1e9nf/yQ3w/aTr9dbBa56XMzj9/o0rulv8o8KXrz/sUDn/54evnXweiMK6/CBu75C8/JMu//NdfV/TjX0f+67/+VT7+"
    "2t+/F/3W+Vup4U65X/Tzfyf3c/dvJaNvwOzPU5iU6/wflvBt8Mfvg7+dlX89yN/K3l2/SPyv/+s/7O8vO/P/2z7/H6/4zzdImn67"
    "7jacbpE/l11Tdumf06+DC9el/2NFt+g/VfPtJn+k6H6V/uk/dnd38f8Puu/65B91Z+X0D/uHKd1+s7zbnecvQxv68m93+Ndj+3nl"
    "/2+e3jrfpvi9HPrLD1954a9D/ZZO2Q3E/vLDd0T8G1vv5/ILA/7lhyltwqXc0v+Md3Xh9mP0rZb9J4723fb/cmerv13IP3TA32j7"
    "D77Y3qf8PSH+80nfxn876efE+c9nfBf47ZTs3tU/738070vqx/0fT/5iLv6jqV8yv514l+3dz/v/a9/f7vzfKfzrhB+TdQq/XvzX"
    "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"
    "LgQhStPAwzYgHq4yNh8DpYj/MKmZzGLvO2TmAX84FZln2uHYY2BvriUGzAAKK9fTGOuoii3j2Hm4Cs+k6Aa6OveT2v1yEpmri7Vo"
    "KMYnPgWt1eCcYgLCoyPB3cBy9MaDQ74zHOQuGcV2an90optYcpjkXpXGQ9fqE3F3CnU/O9pEKltsyzi8dYA1tDrR6OP40k84PYan"
    "152IiK5IG4xgCVIm7vjslbNN+pxI56WwA5bLx07tfqToaADqgZ8g7MDGbWcGmBU1zBjccqnyM0JD25qGt7+02JvrE4fZ+6Q+550y"
    "2Rrud0IGWTdN5yXKmnJHOE7FhElfA52MaaeWEpIVyWtYqYxuRNYKK7ZELzLjADfC/eEqMy8aFQAOyMJWXBf+nigGjUVfsi+8IIf2"
    "bjrqa2YK8R62o0AiJnEQCMxEXdZVKOSJXhypCkikjAXCx3rf9mT8dmkj0l1/npqQMMM9eBcYriYlqkb8oz1iTVu4t5VF08VHKSCt"
    "LkACWmSo/Oyrp93JFzILvdNMN5yZnvszVaSPH5zTn6eqVTnLf9qzVHVbJpZn8dejeJZI2Wun/eHSJHBxsXX4HJJKxbbLFAhj+f3V"
    "1bKzh4tTjUnGx2bgKD5ccBSBgHBMMREHULckiZmR+I6eSXoXsr3kwby87jAaCc3iA4kdVe77T/a+k3iqdByzdBVd0VZJUHSDfXtx"
    "i31TiqvyvmFf1Ya0oYxwt85VZxD2z+4JNyK4kPExVSqOup4Ll+vnUX1hKB2e031jzb0wpErIqUOg0ljiXvIVXZDWtiru7FjBoEsx"
    "8FfVZIFjJ+LSIJzE13YnYLD8hrF50SpGuYiVvQjYkY3MSPb2koODSS8fpVs6j/rZav+nn3963Eh/Tvah3+chgYQbmmJwuaoIjXn8"
    "p8/jn19icqBLLykJlb4NMv3vLlvuIae6m1z6yCnd4tLHTuk2lz5xSjumt/PL1X5eaDnFyaDfTzMkJsdTPGGX/P2PgeQn65etH+NP"
    "JRYdufLfWPAVNBh91SEEtNxqNa6u3mhTiMx9DRTIE8uKYlyzzCRrko+qd4lWYU3+5EGrYevrlLQPXzxbW1lZXeUH44lRbRK5U3sF"
    "JCwK9CoSbMI+K1PIOobnwMrUNGIP2wzSZN1c+/6mjDiGyZcBeaqWzSp/XOjj4cEsbda1ppA7tR4gheXGjRJ3yhYtwk03pnDNVMvH"
    "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"
    "P85xTvDHm1L8Gdb1nCf31N2R/Etwemk7QaEhktn3Z8U8aRbzebQg5vlrNrt5C2z9jMNC4JwRTcDhmzSLtkr30+wKpelQo2KIfA8r"
    "uxQlHk1NUAapxxzIj9Pu+IshP37ZxQtcOUfqbKyef+NHQzW4pz9k2d9g/tMSiIkilJ7CcjGtK5V85w5VQbe4LUv8DUck3+j012Jo"
    "4TnVLRcYyPtzpK8ZuuMCsqkb+V9ep8hmWD8ap6QxcvgY95UhFd9vULBKeeEgUSm2yMjT82vIyKO/pOcO0ZS3oI8t2g4wvEsvK4cK"
    "LI4q145fG9nB8k5tch5h/D5aJ476WVpY/E5Ja8KuqGchR1QaoVnZk+tW9tXZLQl0Z4Utr9SyUUGsSHC5iC0gvUXUweug07u97UX0"
    "XlXf5NZ6XVy3XgffyeIi7MvisZX/L2nvtWs9jmYJ3s9TBKrnIgvKTHkX2dU1slvaMlveDQoouS3vvQr17qM/Ik1kZTdmBq1zcI5I"
    "USRFfmYtmY//OwPzy2PeP8eb/vd/fPHkN4f+Fm4W+gce+tdi//n/Mi7x/8a4/Nvf34r54Qf+4WW2vzmHH5L113C2Hvu372v/J3bb"
    "73/3mNhfl8R7/eqnjh+qbz1/fz32iwtTfjk0G89c4DDyI9jbe/h9/5e3kf7lL0D7336R6eCf/ys8fmr6O484/VLdqf65un+s7y+A"
    "+anwt08BhuOf/6Gu9y91Cdb/sq5fIfBva/rtRfyjm/i3f1DMXxDyX9r9zZD+/2Jzf9GzP0/+b/r6d134a7m/7/APDXimpbZ+TO1/"
    "jVB6W3/5xO4vsYH/9NeAK8mQXX/8xUCrP0xmnGW/+/dhTuM/bNUj2V3xI8jPj7tP//x7u/jdP//px6pGAfsv9fK7kP3nP1nl7wL2"
    "9/+e97+Elvr16/dfy0TsvwTsj3W0vlXxx1/XrzHmYczntcqXP/6f448oxvuDWUz2lygh0V/L/gg41eb/+aeHjH6LX0joX7v6l50/"
    "B4j5pVv/kv859M+vYrH+gbX+/V/l8gH6f67p56v4v/N/+9N/beDX2CTsLwuw/uu//sd//v7HzPy6NCf7xx/7vx75ZffH8f/8JchI"
    "1+VZ9QO//LL01XOB3Q8a+Lt//28Pknwu/L+Dv97f/B//x08//fdfAtj+NOftv/zTL7tLmefrP/2UzsOyDHNVVP3/+HkehvU//vCH"
    "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"
    "Dsl3hPPpMJQ+5k/CNNeS7L70Ct+vntRdz+WbK8dzPWui1vEYYngPLXy4HmptXhU1lN++k9JeF3gtRDZuQQEuHP7xP43/efveIhwB"
    "7D3p5fzH0eT7IlvjVikpe96wunfN4nvQPla+hBYZQA14u3ZrAlVBO1HHR1NTqbknPpydXw745No43305ei8wvzaIyl396b2qX2A7"
    "lwzs+o7Lff5TDuJ0t+NvZHV/wDheIHsMA83se3fEyvyRjy34bAa/U/g1tj8AIPfa2Q/d5Y+/Q+T5MtrxzszN3bQzx69IVPzWXYZa"
    "+L3udHy4zgDscciX3c+XIz+9YfazrgvUHNoVAT79jp0ttHv26An3kY2WITOwXoB4gY7253E8J8MH+WfN6KsOEjjT6hNcQv8YkSqG"
    "QOyeDcFLYg9vz/XVNZkvmWIJ6iwOv7QO7na/Z+U9ZDzI85f9Pj+jjvI1hK8OR3U2Lk4rfAWzzDn7sxo7dO/NH1eT/LvZbg+VuHtI"
    "KzXicsrPn8z5w73xK2Cqxb9kdtWt5wd3zs6XfY+ZneWdmh/Iz4sf5xal1ukFZmltnPNN3smp1ubeiJ8uGcXFqta9KMj9CT+kTwDs"
    "/ZTf7/rHzRH5hlS/AgTOqa3eUMxnjre7AJ7usLV7MC6TmL+CdaKaB9Lm/1lqrgWAIsKnd/b0Bv3z7SMpq/qrtD5/e62uQf0VeXff"
    "okj58jgYK3k7O76/5YQBGtLJTr30Nt1RAqykin6cX5y6heeXT0r06QXRsoXy9oDUa+rHufWZw5cE/+d/zoqvAD7Vp3RWgu7N+bIX"
    "mON/8X7vXZl9g/KBp8pWk0cegvuSHb1Q86rA8+mEEteu3/tiv8L4yel4v4HyKd4aT6n78GsivsJTv+PjpX9+gvZ8A+V+ZxloIyU/"
    "/AzCyZN1AyB2LaCOuhdZ0cfrk2W456ijvOrlNMFB+A1GcUXVX27thmOo9sKwr2K3YNkf4zwOt15G4c59g6925DL4HQCTA9hWb/cu"
    "4H7PDjhBOBEogFCF4sskwTvXUr/p176AfEwaq7qCg/kDbpZze0Ie2TO34/njAloYS0dgR/Q/kEtkVfrpNxPQLvp8of3czdj57GL5"
    "Q0MHxu9MtMT7r9A58bBvDuxOWYsHlQNucdn6r+FCHqwCfr7af4viQyd816weNPqlkXxiqV3OHbpcaHAMzejWGnsQ6LtrpMFXRhrx"
    "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"
    "gkkZLc4n8BPr0D0p1oXduDj4D0aGt6c="
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
