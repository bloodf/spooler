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
UI_PAGE_SHA256 = "d0f13f9920a19beac10991f343b0dddeb49ba90dc9e915c66a98e97166eeef45"
UI_PAGE_BYTES = 1284359
UI_PAGE_Z64 = (
    "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"
    "0A/fdnsUvX3tcftx9+njzb3uZru309uB763ezpMtDHn/ePPxlv7eoiDvuvxWe7O3iYHbO12ouKa/t5483nyiymPg9k7vyRsMuI7f"
    "0G/vSQfqd9o9bB++tzHG/NP24x1qR31vcXB5Lv9mWwSbF+3tbbd3HiNcsj/9zfDI8hLeHRpeT41nB4cH9eT3YwS390SWB3g5tvzT"
    "7TclVC0K6Z7vROdbKYd0H890SPcXSAxf0+w3RXM36aUpkPvJ7M6B3M9LFItvJGvoFZPDPGHaTMihNiUBJ2GS/Q+Q6tP2dm9nE/G/"
    "s/P46c7e0/aTXufpNk3d451tnKfe9jbmb21td3trktR4vnpvJCl2u+0eJCjShW8ovrNmfD998liTuiJVsRQkacqlor4FfUhSBdJ5"
    "2t7sdra33kiqkk1JqpNVJVXKb0m1srykagma8U2gq/I8tDdy1cihl1C3iHQnv/YuehmT7lmZdD+PlxEuUkkT2Z7fnWxPFdmi9+aX"
    "Q3649W02olsaw4tzyRzsHOhoJI51Ie0jIvoMuyVFAUwXqXOOrB6k8vfScqyqW+S6VtyoNjjwVf0tjW6Ht6rne3wnXe+MVrSFXWK6"
    "f112CXtd7vX+eIC3Do0Zr5J4NKzkNrpjHR6xECucb2oM6viS8rWunIJKUW94hAP9mpNejMejpBS5z5zAYRyP8Wkfx8bIq06XBEhB"
    "PC/N6YKS3n2EgEJuXSfn5BOpiJt6EVFOd4VfKYGzQIcnZUxqJzsYRjePT/FNel7ytCMe9BWeCFR735hy18WIoHMBnKKD/wx8GjrE"
    "Ejp3MYH72lo7SyFcF+ivTvuDB4MRR/VqLKI854jpWw8C7V1HzihFRiPQqjB1m7G2W8aRDjN7GheER/Z8aaPD5dfTJghViBBZJ3qF"
    "Gf5g8ZVqXKZR9abay3eV6x90yEc+H+y2vRoHsiZfVM4NRRGLTWKEaCABR7i8UyC67SzdoyKKUgQ15N51lienSRqNyCmDX4ijLHpu"
    "9jAQx7ssJQu9KsdA4y31IkpE7RiUPDTcx60rrnOGMBhZI4fe7ktmW42t6aWBMU0ZFUMzLEHaPFoDWCOGo2aFtqssgEynaW9ZAgav"
    "cYVB+mICKjVZyCbVE9YqtCJiJPeM/hY1D2vy37AAEbirST8SBrvpi6sAiwU1NG8UUW6ANSL7Zr4EVsGyEGQNiypfx3eqFLAEeYKK"
    "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"
    "KmGEpKzt/XDr5KVNF6UbWrNNLJD9YeiYtI726+x6rtpae062R5vu0KpnG6us09lMJaJe7k4InDlirTzeJiqt/mze5RrFJksUF1NO"
    "LneY/nAmOdkSqhUpaj/QygqxWPEHVisTdWRzWI/2zU7Z3o5JrqZLeovTViJ+JFf6oKtVNrq+mJPdmpRLLyq2s6jK83y3O8kPW+v1"
    "QB/jx0OjPe+0a2myu6oduMNuu53vVXrOiThG0c0NVqLH+a6Yt4jFJr0XFhvS7K3AgCjypHnkqbktbGQ+B5rQWrPGxC6cxI2yZ9vl"
    "1X6ucHpxtci1m+J5URBmxS413s26GykvMmiVqReK7bPQHm1tFifK5/WkmTs1hzxRlcqzBi8zjcV8X1c35Xy5Pe91srZEF/qtaWdM"
    "YQ0nn0WrPaS3ro3Wh3RPVpXKtmx2TWpUVIx8q908Z2fKvjpSJaNZKGnDFcIb7QO9yjGnvlTYUBSdL0iIU51Xu7Vzv14X99pYqh6O"
    "vTV66kg0WigKWb5wbtfm5c5YbfOLXLc2re/KnS1klua+s0CmVnO8sI5Kw56VsXFl6+BtUpqp/e28fVzgxnZgG/QmTaBpepSv4sYq"
    "rxQ2JldJb+e1xZyhjQF22o2ZdYehZyth2l9tMCK3KCjNQU3PT9q0OOm1KTGt9kdly2m1D0hpu5uqdqOmcWtjXcgNKhu2dm7uZqdi"
    "Id1bAK7WcIJSmf6ov5qRkxbgsMFZzue7g8Kwhi+QViE3quZp6jjuN3YsU8+OO7PmqUcq1rwI+K/RkLd1vYC0Gbo3p7f0rtGRaouW"
    "ZmY3Gr7K00y2inK1MUFji2rH1nq9KSduBJJG95N1l2rVDxi1G3XUymk2r6xL43W7zlQ7B2UvtMasPaApdILvj8rhlLUG1YmTyx9l"
    "ZNxZkEVaGOFEWsVBeSvdxih2Qe4IuTNB0wtKZrPHinrsFdcEWebJBsvb9UGHW9ljej3SBsV0zxTwVmfQ0FZ6uSCfNKZUU/IV8rAu"
    "gJVTnHP7ep4/Kscju+jv6o58qu7o9QLL94YqNnYEGUVKahHvb1rHVq3fNXFythZr2+OpwUm6ghtjoke3h2VOVQZtqzNe6c1Rp7Oa"
    "NUBv2D0+KBblc0Nqtqm20FsR7aI00lrSrEHmdX11zGXbYDrOHA5rm5U2UscGSsfhq+mxtNiNNJQaymAeSHWCx6d4M6uuEGXexZj0"
    "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"
    "hGtpoyGxYPHlwUmSmlKGbjGRIFFH9djpCnF1ArbpklyV+cCnHT8txYVl2JQcAnIU9I264ChWpKF6g0cSQh1UyLCrbOOi2yE+BsxG"
    "KY4lKYb1PCB1bj1DKEqNQ5RbzgLOZY2FI26EaLVqRh2wUI6Eng9+Z9V4FM11QlclvMt38GkN70d3YtkEa2xWeSBSNJIEHkl04dYe"
    "YaLzw64Bo4pupt2BoC1WOXZxJBTd4J/KowubWA6Mfv6c2fFxDc61aUoZeExN4sMEmUzVGWix5DwWluvpzI1t3m7FeF93EhMiVZno"
    "o/nexyrAAcl0Z3qgMhrBUXkzEyV2wBxWPRsZVEyTLYaJQ7abJK6/Drx2NoFOhByAaDr6FJjDpHySLFZkKlBChwYzSubExZI4zd1k"
    "JpxoWyoNn2JPHDePMBgLE2rbC1M2ENanOeCkgEutPYM1ZllewOpOdNpew5dGyKRwN1NKpe+ONiBPaiVGjYxc6ostQULUlrBXIH1q"
    "nLWj9cUsKzerXBWZRgYQZo5LeCzDdD/rWOCU98cs2q2ByMJKg2xtq0/5QgCQREDbvQuQ7qoBVQ3w3SRrrGK5zg3TA9SBQwDYlTN5"
    "v41mROTl7AnylwiOeHIxWI4ta3Fdqrmjax3UTTbMmp4x+KaM9y7pUqzm4ivb8j77mOTj85Mmf4zz99cnw97enhKzsrhO0udP757U"
    "l+fFrnmPx8Vevyz6RZH09/u7oteGNk7/rTc/ry9dXt5K/eKNzfntDYIvX9kss6Ka/wP014ee/pEa5/91//nxv28/u/l8fp/r+TqO"
    "ywOO33+G1HcM2yl+MO0sq35UXr56S/Qbxdarl0m/+YDotX/px61cieiftWVmdv+Tls4kP23nOueftHQl+mlbpZ+188vy8k5af28h"
    "pq8Jd/n1rb+fENNjbjGrqypLf7C+Z0rq/NrIjyk/G8D5f+vk85ntlD8hp2z7p826nzd5f3nuWuHyeuAXHEuMjr483TjuUary28/j"
    "Qp9GIbbi2nYWcWaOHv+lkx+w4TqK5a/h6DXxz1DwWNpfbPVM+pM2Syd2LkJ/5tePWnS63EjtH857VGznV15+9MhwkbW/QCI6l8dC"
    "f/Tm8YNoZT0Q8cW4b68vPhVXwrNuuirlHwBobJe1gx/Iw3l5i2xwfiQGRhx46fw11ZcqM3bcs8ocefoTpTm9Ey1fq87vLdDZErxW"
    "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"
    "ePv8X//1quE3ybireHMjNt7kj/wLU98/v/v0WIzzzK8c+ds11n47/Xh3XsXzmDL26zPnh5Q83yLtFXs95Tyflj0KP8PedQnOIn4N"
    "sD+NLHkfOf1tGX5/fh14yEd/NcnHLUZaPT+NCPrzL68l8xbp/8uHf6ve+0Y5KxwjumzJyrfvPj29bui3f/8z/fT89DXZuz/Ox0LX"
    "HdfzN/alz/dS6bIHff7uHvhByI4m7vk7O9xzOOjiKH4li59N+6rTnp/Os737AH/58MKyW+zm/b3s0x+frg1fYkBft/RbMOY/P13d"
    "z590fSb6x3o+1/i643Purd+rm/2Tfs9E/1i/5xpf93vOvfV79dx/0u+Z6B/r91zj637PuXc+ny3vF9w4Z11LvikMl5sXf/3meoxV"
    "ruP7jpN1Hu45gwvS6DdwFOOrr3Ae6c13+AKO18xxMJaYtYJTCCM1M/Z/DrR/TlrkI1duJWf69Wii5ez79Gfj/2361dmey2ccPH/T"
    "W3g+xx5L9hGQT73Y+c3O6pHnv13OIr+IzH9d/uyeF+DKwfOp1DXz7EiOf85gDLK6/J8I0xO3EDH6njwfzNDE7UAGfY9dDm7IaxT9"
    "JXmORJMP8mukGn6DvYcu1a5pfEzjYzXwQY+/n54PcjjsPYpNz9H7KXcvAqFzW8SjKRA+t4U/mhrT+DWQf6NHzm1dTn7GbOichh8H"
    "A+ejqksafHOf2Y2eQ65Dvh800MhtSvcjL+QxxWs7d/pbEJ37glM6Pw7sPPAHL8aOzkx48GpM4695B6KXgbzQo9eB3nl3TUMP3t3p"
    "77wbGTXFphfe3YvuvLs3defdvak77x70N97dh3bn3XXo+IN396ndeXc7f3vw7nH8OP38vO5xXHijv/PuC1b96OChL1szja4HD9br"
    "g4ezUDEXmeIu0vPdA4ivpe97JxEl+0+fRMTf1gbFWRh/pA5uBFd9MOpVy3HOB3f37KudeR799tYo7P8JhXCFPfRAKXpBJ3RD8Rm9"
    "I3Jg4pHGLujE7/Q3sSbuS38T65eT5Gsae0CHfDnivZwo39u7QxX9HKn34dyReh/unRy5DeuO/Ffpi3A+6K+Sw+HvSZhELkJ1L7rJ"
    "26Mp7Dbjl/R1CF9walQIN9Q/BPx26H1n1f1Q/FUafaUQHlJ9Z91dqh9SdZfqu9TdpfrGunt7Dym/H/ojj3rXSwF3Kb9L9Z3+IsXE"
    "i9Z4SV9496C/8W7MR2ASvSikW9Gdd/eqd969pG/L9zmrfqQQCsJJ6qs+qL+tD8Sr8PySQrgJ2vc0QvzPawT7C43wfVXwhbB/rQX+"
    "B8Uff4+Dr8WfeD8FX8QfOVtV4kX8z2mceC3+IzYg4oHhEVPQexR/XCS5yN0l/cDwjf6O4Xt7d0ze+3ux8tfx3NP38d7p8fcI9Fr+"
    "X6UvGH7QXzCMn4GLEeQZ69y96I7he9U7hl/SVwx/waofYdg7GVXXX0HsfgniX4LvT3Br//O4zb/A7Xcd2s+d1i992f9JJ/as6MDX"
    "indUhODnipckXiveG+ge9DdQPrTTI33TXjf6KzLO9yhgcIpeQPPA7xVPj6YeOvMljX+G9xcdfRnaQ0ffhv4qfZna3RN74PfmiT3w"
    "fZOne/oub3f6mzxyX7DqR6DFMrdAzCtoky9B+ys+2I+dr/yfh6z/gOz5UwHhJcrz9dcCVVYZsehYWWF/537y9drq9wuvMZHvld73"
    "ttI5OP5NIvTa/m0r+/M71ZWT5LFR3Vv7/Rp7fLpGvV6+LXien8cl3Lp/I4zi95K4/SjfbEeOPLI541UF8WVM9+3y82NPfs4VL9F8"
    "+fPRfHYF+vntn6/oP73J3DdXfp+T5ad3z+e7vK3Rl5Kftd+/onu/BpuxP74G+1jnH9+E9R7goL+czPOTn5XV9lL4Q9ScV5U+X3X9"
    "7rq/mvgPsfFPwuqHiPwlTH8Boy+vUP906c6BxySvz5d9/6w+C5G9RO/PN3rv/ZxPf2LDct4+f9by89OF6lXWu1eUr7q8ET44/5rs"
    "wquvKP7P9G+XjEvpBPwwfV3lHPAaa/CjkXifBOnbV5SXn2cGX9t7zc13r5s4k9w7Pf/+auC3SneazxoakfhyvvL32+HCU/EUPBkP"
    "/p31Hff2+Xyj//npMK7I5bME573Vvb3r4+d3n56c93mVvMp598S8Nd6f1+TdE4i/++Sx769Xqj/+nb2E95uHBHymI34Z/V9A5/5d"
    "0+d66tPZRfCzMwI9pxLku2L71inPZdnGOThPf17CzSOa/rzHLD9c74V/Ecj89O4GwEtwfezji+3/B4v99GQHxfnji+YczS+CPB91"
    "SNG85nv/Bd8v5wQfi+Dt85X85XRFSd++vS3H9bj2qwW5Br3fPV1YcicaFdz717N/IfvzL+fPvn7Lrd/OJ8X5b+X1M5G/XA4lnHv1"
    "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"
    "PVfwcp0fcU2ich7rxkTdZ2bdFbfeJ04YzW7Lxq7D8oO1UjNq5eJ0Zl5am0SiO250OzOTaM7xQ4+K8Xpj2B62ho2xGjPyOfmoZple"
    "m5x02wWNYeaD2C5fXKVXWLlT1htc9XxZSafOaZDLbaupTWyYnZz65cJFnja13Y6VZtKwqZgDXOudY8Mz0xXSarG/mMh8WZ4Ix3oM"
    "w8xUc7hVBjyeIRZkW+w26Z4xmvXbRHZvpvJSK10ha9XqTq0eho15Rd/u5QEmUENjfNjJxTrd22UnZ5rJKYNYdjHsrM0jL7KdbqZH"
    "N9exZiyR3ipmapGud3GxZhy3O26IYz1+uJgw9amcPPGknCmcdbWTjsmjtDQgzJq+zwE6OT7UB2OqrI8vNbFZvuzanZw8VU5dhU41"
    "son6hL2cyDOT4FIXZZNparhYGYrlGlWt5002raT59SKt5fqmlJ4wzG5lDorZ2D427CiVniHy9ek+kc+cpPymf5BmqXo3O1lgtUoa"
    "665ms9xmzaZz58SiK+TNAlOYd0fUfGDg03mlQdYaOD3IYsVzqtPqnPe9XlWfn+dMWWTLFItRaz4mtwkxz/eJ8ppojFa9dnk1GJdr"
    "s25+2j42VtpU75cHac4op4ZmZlDb5KXieFXJbUazSdNIZGY6hzV24+a+2cMJg6ixzDxp1DvdTreup7KJbDIvjTRmeKYvhyE939G7"
    "WKF/Inftsk6W210KL5utnlxRkkS9eEmvGOGynqu6QY+neCt9YhJZfmUM8WOi2waL1V1z7fS8KFSy6e5xm0hrw2RiUBh052XhOODF"
    "drOyzw34FjXs5C4izdMts31OF2abS79alkdEZVZpksMmW62VxTJp6KfqqVdm9JNO9/rj49yoT8hdjujvcpNFVhwRzCCrDVcnrC1O"
    "+5KsGCemza8neO6I7caTDMCDYlLTVumFPpYO9Umngi9m2fGMJdfFfrolJYz1oTY4H/WjNCALnbFRmU0YbCJOZnytAjrac8qCSB3W"
    "bTK2Saz3+exuJOjjgn7ELq20Ye4HakIB+1fsxWKxYmIq7o88fmoBbOu059VBWx3Vpwn9Iue1fNLo4uPYcbO5VDdko9jI5IeTOp87"
    "mziLJRsdiuOrdTozULaLbjrG5xubxKKRzSqicU7Re5wQOlujmujXE2eSqHKbDleDLvz6Su9zm4pU2ZmVYh3LF9i1dl4JmJZormsV"
    "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"
    "VV1pcvFDqklNs2byO4P5MDc3X0CvLZvFQoO7+zReG296S6jp/aVckT6n2nhhyE3zOc/vZ+ou2zysuXFtqR66i6fWvq3MXqXj7rW6"
    "YxrQjtLhX7Kf09n0o1rNL0bchyQ9vT4dPgSuBvrc3mWk3WZ5fHqRM+JxYBz1qtS86XUq+fGiZGb2/fXLpvSyOz7L9e1TufIFFtlr"
    "Z9Qszxo5k+2/t6r9+lLkrdmX2nxZdyb1Jf++rzcq+fbNfilslJ151xndSPzzPrd+5tYMIxtMX50eTaPelcU8+1UbsIXJ4FU3n+tW"
    "FRxZ5fpqOB+Krf4wl2d7E7HJNfrTXOZL6U4PXHOe/bzb69zczE176muNKxj1yrhgfk2eO73e5KYiVp5GUttsG/KwOOw25szbpjb/"
    "WA43qqFVi/nOeNjP54XsbGOKq/1EtpqfRoUVmHa2tuq/fuyVww3bfmeVQbMm6f0R32hmpM5g1+g8F7s7pbhVSstd4dUqZuel1vNx"
    "qQ9yL3Kt9JJ/mnWODaMyys6qndmSzWufT2AjLhWemOXirflUrynMvj9Zts3OZn1zMJvz2nwyGu+H+16rO5fvnjaLhakJDbX9ctAy"
    "L9Kaq5lqPsPvD4rRKXaHbX79OpfnA1Oqvta5aQWIsYdZpf01HhbHs8ngWOQr5ui4yOzy1e5bbmb19wwYlJdtd7UflZXDbNYYrZZZ"
    "42hlWK7z+bmAPu2nar373JZH1YKQZyfTZqWvvAnLVQaIgKva07jeVN77ebFXO7RMwZwoXGW0muQnu5vXnDgeVvev/IgZ9MoloZIT"
    "n8o8w3a7q8PHc3u449pv3KaxbO7l+bJhZSw2N6u13iurwnqnKGs119nolVpNVl7bjcW7IpW7lUZW7NX1RZWfq2J+9SFtsquqWp33"
    "R/V+tgeE1tdXUxiAXsyq46FuSt0Dz/WX476xzzTGtRe+3nvqdqtrgOND7nLD1UensumWyhmDmx/f3yxjMWnNdp07pnzDjIfSbiW/"
    "Vety4TA67i11luXLx217Mq3PZEt+HW5LX9rL+ENorFcZ4f2m8XUE+u18JZRfvxZMoTOvSksrUywNSoYMxGbhOVf5GEqFgiLtGqtt"
    "syKu2oOm1T8w+3ldzCvD4nJRr9dL09z8SxvunwsNozHutt9yTXn02alVF8evL65ae9qba+V9Yxl38zqv3uQytSduwNQnfXYvMguN"
    "7VRfVp36bP9U+ajWphx795ZnW8K8YHHTbsesKM0v4fCy1Hs5afzV2C3Lnffy9q1pmIXpcV8+Pu8aJU1taI3yE3dzIxan5fayNKl9"
    "tpSSYe662Rm335Wri3G5XHubM/Vco7A7Lhar1+rLPNevvLKVrzw4vUq1vdlQLaN+Y6yFLZCEnu5mn5nddrholTftO7Z+aGqT483z"
    "R7nzWWllRs33Y6H8WZXAApyUjpvRcdjdNnrPXOVJVz5Kx+6muDFagzexfHfXtXJ9ZrwZb3jtKzvqZqvrQp99G8x1o/3EjT6ZGjNS"
    "B+aYfTVrfUvt8eX3RTU/bOutjcmLk6OqFQvj5urublmrKOLHlDG366Z2k8+w++2rUuA/B/oov29Pn57kF1kbfApDoTV6K1rDUW4s"
    "6JKl7Z6Uu9Ugd8N8NWqfenvcmayKB+OrO92tasJCyB/1RbbZGA1Mg681nsTJc+FFYI66lR9bX5LEaV2N/eprS2ZWZ2v99nqkfJby"
    "h+6YV5ns9PnmMOg81ytzrb/Ngf+9Gp2dptZzb8zwvVk86NJirEl7YahsJ1/9zmertTga7dfBzcewtz7UzcEyrw0+bpQ9EIAOW1WZ"
    "Dhrq6tXMZPpmq7NiS2KvvB9Wn1RpoOe41Vdt+/ayWr4vJsXnXuHt2GU/e+Znf1B/LpWXm+dVZleoNreD0lEyFTAw09GWLxfnvdIX"
    "M3iWP/jG00erulfUzV5gm/ne3fiYX86Y93dGeRW+OstDVh5+8dZQ+5qWR2yp8K505Wy935y/dm/e21rpo/U1ziyF1oeqdXSl9qLk"
    "1oe81lq13+/eui860FmX772PfV6VwMIq3G3YlXEDVLXivsV/1Jt3a23Zkdt6bVltLnPTt137vbp5KzDcR3uvPG+/2Ikyfy+1P8ry"
    "4nnYz3C9svRpfnSb6jtXXW8EU60u+ep41nqeLJ9f9tv9YjB5G6i79WJkjo3a86H3uunnyuVS/b3aa9V71f549N650SQJjDn0lhaa"
    "H6+vw7m5f67yI3X01DdKi7tR+dgBG/R+8NRolEr8ZrgerY7N9WG2Xcz6vQ1TGfWYifkGzkt5pNbrs2OvtxpxlappKta+WDlken3+"
    "61VmGt1eZ7oftdoKU9nNjpPhbsh8ZTYdZVa/+/jMPu2ViXEYikDHbmzepalZ6Kq93WrMyovG0z5T/9oZX7OPETfhx9qdZBy4WaHN"
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
