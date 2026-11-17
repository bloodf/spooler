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
        update_settings({"display": parse_display(value)})


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
        update_settings({"drying": parse_drying(value)})


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
    update_settings({"wizard_done": True})


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


_settings_lock = threading.RLock()


def settings_form(url, low_stock, plate_check=True, plate_margin=DEFAULT_MARGIN, weight="both", cart=False,
                  src="spoolman", progress=None, columns=None, stats=None) -> dict:
    """The keys the Settings form owns, checked, as a Save writes them with update_settings()."""
    form = {"spool_source": parse_source(src), "low_stock_grams": parse_low(low_stock),
            "plate_check": parse_flag(plate_check), "plate_margin_percent": parse_margin(plate_margin),
            "weight_display": parse_weights(weight), "show_cart": parse_flag(cart, default=False)}
    if form["spool_source"] == "spoolman":
        form["spoolman_url"] = url
    for key, value, parse in (("spool_columns", columns, parse_columns), ("progress", progress, parse_progress),
                              ("stats", stats, parse_stats)):
        if value is not None:
            form[key] = parse(value)
    return form


def update_settings(changes) -> bool:
    """Write these keys over the saved settings in one locked read-modify-write, so two writers
    (a Settings save and a worker thread, say) never drop each other's change. changes is a dict,
    or a function of the settings as saved now returning one (for a value built on the current
    one); every key it doesn't name stays as saved."""
    with _settings_lock:
        current = get_settings()
        return save_settings({**current, **(changes(current) if callable(changes) else changes)})


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
                update_settings(changed)
                settings = {**settings, **changed}
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
                   spool_cost: float | None = None, tune: dict | None = None) -> dict:
    """The preset JSON for one Spoolman filament on one printer. Values are lists of strings,
    as OrcaSlicer stores them; one value applies to every nozzle variant of the parent.
    spool_cost is the price per kg from the filament's spools, used when the filament has none.
    tune is the material's Advanced tuning row; the filament's own Spoolman values win over it."""
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
    for key in TUNING_KEYS:
        if (tune or {}).get(key) is not None:
            preset[key] = [_fmt(tune[key])]
            if key == "pressure_advance":
                preset["enable_pressure_advance"] = ["1"]
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
        have = {field.get("key") for field in spoolman_call("GET", "field/spool") or []}
        for field, body in ((DRIED_FIELD, {"name": "Dried", "field_type": "datetime", "order": 100}),
                            (USE_WITH_FIELD, {"name": "Use with", "field_type": "text", "order": 101})):
            if field not in have:
                spoolman_call("POST", f"field/spool/{field}", body)
                log.info("Added the %s field to Spoolman", field)
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


# --- Preset options (Settings > Presets) -------------------------------------------------------
# Presets are made per filament (one per filament and printer) or, when "per_spool" is on, per
# spool: "<filament> #<spool id> @<printer>", made for the printers in the spool's "Use with" field,
# else the printer it is loaded on (a Printer tab slot or a Live Link report), else every printer.
# Advanced tuning ("tuning" on) sets, per material, the base preset to inherit and values over it;
# a filament's own Spoolman values (calibration fields, orca_settings) still win over those.
USE_WITH_FIELD = "use_with"  # Spoolman spool extra field (text): a JSON list of printer presets
USE_WITH_MAX = 16
TUNING_KEYS = {  # OrcaSlicer filament keys (all in ORCA_SETTINGS_KEYS) and the range taken for each
    "filament_flow_ratio": (0.01, 2.0), "pressure_advance": (0.0, 2.0),
    "filament_retraction_length": (0.0, 50.0), "filament_retraction_speed": (1.0, 500.0),
    "filament_max_volumetric_speed": (0.1, 200.0), "fan_min_speed": (0.0, 100.0), "fan_max_speed": (0.0, 100.0),
}
TUNING_ROWS_MAX = 40
PARENT_MAX = 120


def _tune_number(value: object, low: float, high: float) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        return None
    return round(float(value), 4) if low <= value <= high else None


def parse_presets(value: object) -> dict:
    """{"per_spool": bool, "tuning": bool, "materials": {MATERIAL: {"parent": base name, key: number}}};
    rows with nothing set and values out of range are dropped."""
    value = value if isinstance(value, dict) else {}
    rows = value.get("materials") if isinstance(value.get("materials"), dict) else {}
    table: dict = {}
    for key, row in list(rows.items())[:TUNING_ROWS_MAX]:
        name = " ".join(str(key).split()).upper()[:24]
        if not name or not isinstance(row, dict):
            continue
        clean: dict = {}
        parent = row.get("parent")
        if isinstance(parent, str) and parent.strip():
            clean["parent"] = " ".join(parent.split())[:PARENT_MAX]
        for setting, (low, high) in TUNING_KEYS.items():
            number = _tune_number(row.get(setting), low, high)
            if number is not None:
                clean[setting] = number
        if clean:
            table[name] = clean
    return {"per_spool": parse_flag(value.get("per_spool"), False), "tuning": parse_flag(value.get("tuning"), False),
            "materials": table}


def presets_settings() -> dict:
    return parse_presets(get_settings().get("presets"))


def save_presets(value: object) -> None:
    """Save Settings > Presets on its own, like the display flags."""
    if isinstance(value, dict):
        update_settings({"presets": parse_presets(value)})


def tuning_for(filament: dict, opts: dict) -> dict:
    """The tuning row for a filament's material (the longest row name it starts with, or its
    OrcaSlicer material's), {} when tuning is off or no row fits."""
    table = (opts.get("materials") or {}) if opts.get("tuning") else {}
    material = filament.get("material")
    for name in dict.fromkeys((_norm(material), _norm(MATERIAL_ALIASES.get(_material_key(material), "")))):
        best = max((k for k in table if _norm(k) and name and name.startswith(_norm(k))), key=lambda k: len(_norm(k)), default=None)
        if best:
            return table[best]
    return {}


def tuned_parent(base: str, target: str, parents: list[dict]) -> str:
    """The system preset named base ("Generic PLA", the part before "@") made for this printer, or
    for every printer; '' when the printer has none."""
    want = " ".join(base.split()).casefold()
    found = [c for c in parents if c["name"].split("@")[0].strip().casefold() == want
             and (not c["printers"] or target in c["printers"])]
    return min(found, key=lambda c: (target not in c["printers"], len(c["name"])))["name"] if found else ""


def parent_bases(parents: list[dict]) -> list[dict]:
    """The base presets Advanced tuning offers: [{"name": "Generic PLA", "type": "PLA"}], sorted."""
    seen = {c["name"].split("@")[0].strip(): c.get("type") or "" for c in parents if c["name"].split("@")[0].strip()}
    return [{"name": name, "type": seen[name]} for name in sorted(seen, key=str.casefold)]


def use_with(spool: dict, printers: list[dict]) -> list[str] | None:
    """The printer presets a spool's Use with field names (by preset or label, case ignored), in
    printer order; None when it is empty, unreadable or names none of them (the default applies)."""
    raw = (spool.get("extra") or {}).get(USE_WITH_FIELD) if isinstance(spool, dict) else None
    try:
        text = json.loads(raw) if isinstance(raw, str) else raw  # Spoolman stores text as JSON
    except ValueError:
        text = raw
    try:
        items = json.loads(text) if isinstance(text, str) and text.strip().startswith("[") else text
    except ValueError:
        items = None
    if isinstance(items, str):
        items = re.split(r"[;,\n]", items)  # typed by hand in Spoolman's form
    if not isinstance(items, list):
        return None
    key = lambda text: " ".join(str(text or "").split()).casefold()  # noqa: E731
    wanted = {key(i) for i in items if isinstance(i, str) and i.strip()}
    found = [p["target"] for p in printers if key(p["target"]) in wanted or key(p.get("label")) in wanted]
    return found or None


def _host_name(address: object) -> str:
    text = str(address or "").strip()
    try:
        return (urllib.parse.urlsplit(text if "://" in text else "http://" + text).hostname or "").lower()
    except ValueError:
        return ""


def loaded_targets(printers: list[dict]) -> dict:
    """{spool id as text: {printer presets}} for the spools in a Printer tab slot or reported by a
    Live Link printer. A printer is matched to its OrcaSlicer preset by address; with one preset only,
    every printer is that one."""
    by_host = {_host_name(h): p["target"] for p in printers for h in p.get("hosts") or [] if _host_name(h)}
    only = printers[0]["target"] if len(printers) == 1 else ""
    live = {p["id"]: p for p in live_snapshot()["printers"]}
    out: dict = {}
    for printer in printers_cfg():
        target = by_host.get(_host_name(printer.get("ip")), only)
        if not target:
            continue
        ids = [s for unit in printer.get("units") or [] for s in unit.get("slots") or []]
        now = live.get(printer.get("id")) or {}
        trays = [t for unit in now.get("units") or [] for t in unit.get("trays") or []] + [now.get("ext") or {}]
        ids += [t.get("spool") for t in trays]
        for sid in ids:
            if sid not in (None, ""):
                out.setdefault(str(sid), set()).add(target)
    return out


def spool_targets(spool: dict, printers: list[dict], loaded: dict) -> list[str]:
    """The printer presets a spool's own preset is made for: its Use with field, else the printer it
    is loaded on, else every printer."""
    chosen = use_with(spool, printers)
    if chosen is not None:
        return chosen
    here = loaded.get(str(spool.get("id"))) or set()
    return [p["target"] for p in printers if p["target"] in here] or [p["target"] for p in printers]


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


def spool_profile_names(spools: list[dict], printers: list[dict], loaded: dict) -> dict:
    """{(filament id, printer preset, spool id): preset name} for each spool not archived, on the
    printers spool_targets() gives it. The spool id keeps names unique and the same across syncs."""
    labels = {p["target"]: _safe_name(p["label"])[:LABEL_MAX].strip() for p in printers}
    by_key: dict = {}
    for spool in sorted(active_spools(spools or []), key=lambda s: str(s.get("id")).zfill(12)):
        filament = spool.get("filament")
        if not isinstance(filament, dict) or filament.get("id") is None or spool.get("id") is None:
            continue
        for target in spool_targets(spool, printers, loaded):
            by_key[(filament["id"], target, spool["id"])] = f"{profile_name(filament)} #{spool['id']} @{labels[target]}"
    return by_key


# OrcaSlicer refuses the whole bundle over one key it doesn't know or one value of the wrong shape,
# so every preset is checked before it is written: these keys only, each a list of text (but
# compatible_printers_condition, text), number settings one number, percentage or "nil" each.
PRESET_META = frozenset({"type", "name", "from", "instantiation", "inherits", "version"})
PRESET_KEYS = frozenset({"compatible_printers", "compatible_printers_condition", "filament_settings_id",
                         "default_filament_colour", "filament_vendor", *ORCA_SETTINGS_KEYS})
PRESET_TEXT = frozenset({"compatible_printers", "filament_settings_id", "default_filament_colour",
                         "filament_vendor", *TEXT_KEYS})


def _finite_text(text: str) -> bool:
    number = None if "," in text else _number(text)
    return number is not None and math.isfinite(number)


def preset_problem(preset: dict) -> str:
    """Why OrcaSlicer would refuse this preset, or '' when it is fine."""
    for key, value in preset.items():
        if key in PRESET_META or key == "compatible_printers_condition":
            if not isinstance(value, str):
                return f"{key} is not text"
        elif key not in PRESET_KEYS:
            return f"{key} is not a filament setting"
        elif not isinstance(value, list) or not value or not all(isinstance(v, str) for v in value):
            return f"{key} is not a list of text"
        elif key not in PRESET_TEXT and not all(v == "nil" or _finite_text(v) for v in value):
            return f"{key} is not a number"
    return ""


def profile_files(spools: list[dict], snapshot: dict, opts: dict | None = None,
                  loaded: dict | None = None) -> tuple[dict, dict]:
    """({file name: preset dict}, {(filament id, printer preset[, spool id]): preset name}): one preset
    per filament and printer, or per spool when opts (Settings > Presets) says so. A filament with no
    usable parent on a printer is left out for that printer, and so is a preset that fails the check."""
    opts = presets_settings() if opts is None else opts
    files: dict = {}
    by_key: dict = {}
    filaments = {f["id"]: f for f in stocked_filaments(spools)}
    printers = {p["target"]: p for p in snapshot.get("printers") or []}
    parents = snapshot.get("parents") or []
    if opts.get("per_spool"):
        loaded = loaded_targets(list(printers.values())) if loaded is None else loaded
        names = spool_profile_names(spools, list(printers.values()), loaded)
    else:
        names = profile_names(spools, list(printers.values()))
    for key, name in names.items():
        fid, target = key[0], key[1]
        tune = tuning_for(filaments[fid], opts)
        parent = (tune.get("parent") and tuned_parent(tune["parent"], target, parents)) or \
            best_parent(filaments[fid], target, parents)
        if not parent:
            continue
        preset = profile_preset(filaments[fid], name, parent, target, spool_cost_per_kg(fid, spools), tune)
        problem = preset_problem(preset)
        _report(f"Preset {name}", problem or None)  # logged once, not on every sync
        if problem:
            continue
        files[f"{name}.json"] = preset
        by_key[key] = name
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
    """{"<filament id>": {"<printer label>": "_local/spooler/<preset>"}} for every generated preset;
    with presets per spool, the preset of the filament's lowest-numbered spool on that printer."""
    labels = {p["target"]: p["label"] for p in printers}
    out: dict = {}
    for key, name in sorted(by_key.items(), key=lambda item: tuple(str(k).zfill(12) for k in item[0])):
        if key[1] in labels:
            out.setdefault(str(key[0]), {}).setdefault(labels[key[1]], PROFILE_PREFIX + name)
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
    """The preset name OrcaSlicer knows a spool by on one printer, or ''. With presets per spool,
    only the spool's own: one its Use with leaves out has none there."""
    fid = ((spool or {}).get("filament") or {}).get("id")
    names = _profiles["names"]
    name = names.get((fid, target, (spool or {}).get("id"))) or names.get((fid, target))
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
    fid, target = next((key[:2] for key, known in _profiles["names"].items() if known == name), (None, ""))
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
        update_settings({"save_calibration": value})


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
    update_settings({"calibration_asks": {
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
                update_settings(lambda now: {"calibration_skipped": {
                    **(now.get("calibration_skipped") or {}), name: _calib_mark(changes)}})
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
            elif name in (get_settings().get("calibration_skipped") or {}):
                update_settings(lambda now: {"calibration_skipped": {
                    k: v for k, v in (now.get("calibration_skipped") or {}).items() if k != name}})
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
    printers = parse_printers(value)
    update_settings(lambda now: {"printers": {**(now["printers"] if isinstance(now.get("printers"), dict) else {}),
                                              source(): printers}})
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
EDITOR_OWN = {"tag", ORCA_SETTINGS_FIELD, DRIED_FIELD, USE_WITH_FIELD, *CALIBRATION_FIELDS}  # Spooler's own fields: never from the editor
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
    printers = [{"target": p["target"], "label": p["label"]} for p in _ui_snap.get("printers") or []]
    # Use with: shown while presets are made per spool, or once the spool has a value.
    chosen = use_with(spool, printers) if isinstance(spool, dict) else None
    return {"fields": _editor_fields(), "filaments": filaments, "vendors": vendors, "spool": spool,
            "use_with": {"on": presets_settings()["per_spool"], "printers": printers, "value": chosen}}


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


def _use_with_text(chosen: object) -> str | None:
    """The Use with field as Spoolman keeps it (JSON text of a JSON list of printer presets; an empty
    text for the default, so Spoolman 0.22 to 0.25, which can't empty a field, take it too), or None
    when the page sent something else."""
    if chosen is None or chosen == []:
        return json.dumps("")
    if not isinstance(chosen, list) or len(chosen) > USE_WITH_MAX or \
            not all(isinstance(x, str) and x.strip() and len(x) <= 2 * PARENT_MAX for x in chosen):
        return None
    return json.dumps(json.dumps(list(dict.fromkeys(" ".join(x.split()) for x in chosen))))


def editor_save(sid: int, data: dict) -> dict:
    """Edit Spool: the spool's changed fields, and its filament's (shared by its other spools)."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    spool_data = data.get("spool") or {}
    spool_data = dict(spool_data) if isinstance(spool_data, dict) else spool_data
    chosen = spool_data.pop("use_with", _MISSING) if isinstance(spool_data, dict) else _MISSING
    if chosen is not _MISSING:
        ensure_fields()  # Spoolman takes only extra keys it has a field for
    fields = _editor_fields()
    spool_changes = _clean_form(SPOOL_FORM, spool_data, fields["spool"])
    fil_changes = _clean_form(FILAMENT_FORM, data.get("filament") or {}, fields["filament"])
    for found in (spool_changes, fil_changes):
        if isinstance(found, str):
            return no(found)
    was = data.get("was") if isinstance(data.get("was"), dict) else {}
    was_spool = was.get("spool") if isinstance(was.get("spool"), dict) else {}
    if chosen is not _MISSING:
        text = _use_with_text(chosen)
        if text is None:
            return no(tr(EDITOR_INVALID, field=USE_WITH_FIELD))
        spool_changes["extra"] = {**(spool_changes.get("extra") or {}), USE_WITH_FIELD: text}
        old = was_spool.get(USE_WITH_FIELD)
        was_spool = {**was_spool, "extra": {**(was_spool.get("extra") or {}), USE_WITH_FIELD: old if isinstance(old, str) else None}}
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
        update_settings({"book_usage": data.get("mode") if data.get("mode") in USAGE_MODES else "ask"})
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
        update_settings({"ui_language": value})
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
        "display": display_settings(), "drying": drying_settings(), "presets": presets_settings(),
        "parents": parent_bases(_ui_snap.get("parents") or []), "cur_code": _cur["code"] or "EUR",
        "wizard": bool(wizard), "log_path": str(LOG_FILE), "auto_keep_slots": auto_keep_on(),
        "save_calibration": calibration_mode(),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None) -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window)."""
    text_language(fresh=True)  # built on the UI thread: Python's own texts follow the same choice
    boot = {
        "mode": mode, "view": view, "version": PLUGIN_VERSION, "lang": host_language(), "pref": ui_language(),
        "low_stock_default": LOW_DEFAULT, "refresh_ms": REFRESH_SECS * 1000, "display_defaults": DISPLAY_DEFAULTS,
        "own_fields": sorted(EDITOR_OWN), "logo": LOGO_DATA_URI,
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
        settings = settings_form(url, low_stock, plate_check, plate_margin, weight, cart, src, progress, columns, stats)
        if update_settings(settings):
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
            save_presets(data.get("presets"))
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
            settings = settings_form(url, low_stock, plate_check, plate_margin, weight, cart, src, progress, columns, stats)
            if update_settings(settings):
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
                "presets": presets_settings(), "parents": parent_bases(_ui_snap.get("parents") or []),
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
                save_presets(data.get("presets"))
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
        name == short and key[0] == filament_id for key, name in _profiles["names"].items())


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
        update_settings({"auto_keep_slots": value})
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
UI_PAGE_SHA256 = "c2d97e1986efa23b6991181666bf72858af763bf000d4616e2139f3c90591991"
UI_PAGE_BYTES = 1358838
UI_PAGE_Z64 = (
    "eNq0vVt320ayBvq+f4WZ48UNjFuM5GSyvUHDWI7tjJ3YsWM5NyvaJEQ2JcQkwACgLIXkfz/1VfUNJJ3JnLXOg0Sg0feurq6qrsvD"
    "3rSatLdLfeeqXcwf/ddD/NyZ5+Vl+pkuP0OCzqf0s9BtfmdyldeNbtPPVu3s6MFnNrnMFzr97LrQH5dV3X52Z1KVrS4p28di2l6l"
    "U31dTPQRv6g7RVm0RT4/aib5XKcnqKQt2rl+dLqsqrmuH34ur//1sJnUxbK9g96ln+XL5byY5G1RlZ//3lTlZ3eKafpZI2WOLqqq"
    "/ezRaPT169fvRqOHn0vRR/915063lkU1Xc31Z49mq3KCqu7oSMfruabv6euL3/WkHUxqnbc6KlfzeTycVXWEr+WdanZHDxrqQxuN"
    "1TiO27PyPD0Z1rpd1VRN+kjTyO602+u8prrWW1WmZ+eqTqM4fURvBT/0TlSeIu8AM/mkmurHbXQcp2l6cnLS73eSTyT5uN+POun3"
    "40cn9+9vNjuJD//3f2JVSeVNm9dt83PRXkXjqvxxOaUBJeNYNXaMedMUl6WapJFWLTrIY0z1oCin+ub1LGrjYfnoiLuEMU9oPtRJ"
    "vFVzW8OyrtoKczq4ypvXH8s3dbXUdXurVrbO+YAWeM4vapo+ruv8dlA0/Ktm6OcNTT0NcXxWcZV3XuXL87FaHvp0qlv6tDj06SmN"
    "jb5d4Rv6g3Wiz3aBx+py50vT1kV5OVaj3fTbxUU1H6vrnXRpZ9zv93pa3eJjdE192Gyu6H/c79PPoL3SpXkkEJ1cxepif6La6pSb"
    "Vjeo5MJMT6xO7bAGDc/0A3V0EiutD41WKqXxtvz5kj7TGvUox/f599RHfXZ8jrcjeh6P7y2xXV+ULa3CCYOZViUVJAj+oG9VrWf4"
    "GxGQ8y/SqvKnkkDqa02J+lW1KlubxC962s0hsGXT5G03S7kIqzGvekrwWPMg/mL7ye6KSloQ2m6bTcS7jr7GMQFjodPPj377+Pml"
    "epLWtJEB+rVeznOaxEIr2Qo8pScxzf6PS4LQJ3mjIyqtcir829fR2eOj9+cxVVHpvTpyrcZHd0/GKPyy+ugKq8bnxR7kPdxt4J5v"
    "OVYTlz2j7Xh33QDpbMfJmKaAUKDZLz0zAUUje2bFXwaDAW9Qh4jS42H5UA/murxsr4blvXuxpjmJON9WTaU6VRLm6Z2goKl1qmdF"
    "qe0u5TxrQtOz4nJV5xdznfSOlS5XC23eTtTHumj5uVbX+Xylk3JLDczCJWPw+mZe5QRgdrHuFA2BIiGQTCftVi3D/ADX7PvV4kLX"
    "9JRQvsOFFlpdaUaYC73ZpGYzXs6ri3z+7qpoHo5X48y/JiZDo+cz/oQHm/iRUFr1kZPlMelUF1SVrLdDdy5c8sFQzKIpdrnpPzJ8"
    "eh04U51iOQjdX0Z1nF1o+p9c4v+Q6ipiW5wPi4IOEX2eFvRva+ah3VK2S0YvQDKxPV74WBkRyA6jrHf2f9H5P36LAbXXlJREZ/93"
    "fi/+XN3Sy2dRlpz932e//Xa++e03So//8dnmvzntv4O0/5aHzW+f//YP+v1H9ts/fvv880s//IvgXKRR2264rXFrt1dw0nz+j3Gc"
    "jccJEBmfkyN6ogE/yydXgH7MpqkUR43kuSbAKc0sPqLzBjuccNiAMOUiis/T8uzEvsTbbazarevjR9/F8Xho5i1uUz3U84Ym2Kzd"
    "v18xqojWjAAYzd9L63vjO+N4ayu57lSCddO85SRzyZntBLWmq76TNxaOetouJlDbkCpbT+Z0DietatrbObYX9dzWQ6fNJW0HOfuR"
    "jTrZEiopOYULpJeMB5XAximj9aLVi2ZCe1zR2VJ9nFFLRP5oXapp0WAzL4sJNaCL0jzY9FovqhZre3uRTz4oGu6irGjbF4zei2aR"
    "L1VZCfWkgi8o0RTlnHALYfN8WpXzW5oON/wnPHwZFZ2fRLXgNBsHi6gFX/Ec2cWhE6w1j2bSeidDWavesduCBS0oLVnh17SgNa3T"
    "11TlWXGuWvwr3drUvtF33Uab4k/NTeJht0EhXGZ1taAFoH1d6o93fizK9gF/iGrbT9etlklFgS2dHp24Dzn1N39oCwxz6izgojjL"
    "CZao062q6ZF6Fa91mg8vaD4/AB3oh8e+U0AW6YlBF71jP6ZnbkzSb+w16i6TclRJvdkUdH7W6VLSlxgNEh2OwVRmbmYStDWLzOlB"
    "lEEDAsUtT5jexntrZYdcy3ZZy3Lt0oqEFYkcbvdTGVfSFsg3mx794ocXtcai1jxFtimLOIW0EmrJPLfBNnyq7bEYr0s6Us6wjK8A"
    "1PJ7jtU+K1ROGIdbR6cYDef81LppKgaXupV2aJfm/NYyaTUsBg0+4fDO+bFVhN0w9iqtzby6A49OZPqC7UGZzTMVrHyfX3egFO3Z"
    "UR8b2FzIWgIyHZTTkma8lBpde1csiBpBWf9GS5sQIIyk8MgCQsZN4MtUvkzdF67PTeFHbau4lozXLmOvxopl9NXlfka5Dy4OSDhg"
    "rg9MIfR6kQa3MRpdj4rmrZ5R1t5xrN5ZMpcoA+ogcCfOmKk7IhkhWtKaCl1QD66CpDjOPmCWs3eUyIRMnHx7+vr7gfABxQzE0GOt"
    "7gfdpHdLlX3AqmSPeTS2OPZUtj4bE9xEd9eCNrbx+Dw5AxU2IM63LnRDpxcdl9MVnZZU+IzmgthBqpHg+Hfe7DEdHemjMUEcgYla"
    "E3WVLE3NxO8cqpnb54oJH+NI/R0jo3JYxAy1xsk1Hxu9qfxo7r6bczpsfpehERKmvgAGsvEpcz7UoCZAFHaZ4C/LWmo60eqVVt/r"
    "lE8hkIw0b6tJSxtcg8Jct0SAUbGWDnk9Jf6C30c5gTDRJkRUyntFp6886tmMMEcD5pjfJ3Odl6ulT6Dlf5OvGqqMiFBJ+ZjX5evy"
    "7ar0FRKYNB+KJRJ6BDiv6C96pQfSbhZxJiJPIYV4ZTrFvG2KXHxENoQO3TO1HseD5aq54qIxcWBJ1B3Kgc4Qcb+9BGbnLJE96O6E"
    "BbdLDCbiTRymm5kLRiu7mjo7tFmlb5ZkCpIMcyGHjsbUppaIGuqH7VDT2VLSSTEwjW99vnARdouE38LShGSb1eLAIPr97iD2B3Xy"
    "/8OgbG+2QRV2RP9xHdt6VRoSrbs8Qlm+0sO2vrUL+0pza4qntCiJyLpdI2273VYlTc+9ew7c05SpWYbDWl+fYogARVNFvK1ms3BC"
    "q/LRcb9/dBRUcMyfXzFeRhFT1NfHhK4hNKijGPNQDw1V41s1xddh2k5FQmwQJvZp2+1O56+rYnrneLtt2mp5cMZ29guvPKE97ldL"
    "a1EeBL72YTlsd4GvPR9wM7KQB4rx0roqLRI5WKf9SJVGsQPDnSIWPYXQqT8JndK03m1Ou37T0TUMC9tGQM/1OijTbCHBVcDYnbYl"
    "2day5BnRIvHBdwdhYbYzj+3OCSEboV7qU+NtiB7tsgbM75sAl73SniL5ho9BRvs7CPeV9hPKWJSOSYhK+IR/odVLzYTzzwRldLap"
    "twfPEwNBs9IeI1NN54L0zye8y4t5J3E2zy+b9J/yUuqbtvPVdKuT1mDiiZOpber+aCy0+SMh8Y3106P7sUPsPn2TfvWlx5VB/q++"
    "tCtly3/1T5oTIS1ROX1+qR0ZiBTpKR3cl5e6hsRqW1YtqJVOxfcJYsKKv7hPZFHw/mCzeW4qZEQnrGhY4sRRtmbyIwO5ZkT3Vdua"
    "Hv3L1CQoPX0BWHivhy8MUnyP8z7Elq5Chyu/s4OjMhoFWtWZlS8MdvHIxXbSCcDMxgAkEK4DxsKSP9XL+FcQQ0MPOIchpg2ntypP"
    "qTmzBeUlirtduk940C5Cd0kzWrF8Og2hwwFW1n2NzHdaghezpwW4HF4P97L+Q1tAsBkjoS2mJoOZU5tvu1V/4nz7WquftN+5z/0O"
    "1XYFH6g2i2Sa0p+QPaXNaROo/NdI8Jv8R8Dun3RQ+qSfzdF/dPSnfmSZUWDSnxy2+kmOn5/sMcHnkByh0tJQd/amdhP8v4oPUK5G"
    "jrCvfdmvJelrV207dJSDVAtA6e76oObWwQ/AsvXbactieqKI1yxg3BKZsGVem46Muvp4J0B6/2IRhuPuUy2w1w5b0wXAHtHmum4o"
    "OzH8quVD8zHjkpdF+SGF+HVpkAsS1G5CGoi1vvOiNz5jLASrOpWjdFgP7azX3BJ1YFi7DqTUhYyYM2KWCKtQDbH6FQJI9Qv+EyCm"
    "tap32693uqx2E+zs1qnearO/lO8cTZ8bwB9/Z8J42dAJ022Wv5hnwmD8aVItlqsWR2T0rY66abHNdKB87PlkJ3kajHgj+V5+awVz"
    "FhK/BCq1LydfUQORB9KT/6HBipj4JzfPZSuZuullSxzJoGhOT9+CoTX13X9Ao+jJVOCUN/0hZpWnK7Z9Hrpte38YTB9BAqHb2qBb"
    "HeBaBs+hFaoStqWqhU8dRm0AFMebzRy3eO6zcM6mMeqf+0L8qCtIRI3ZKnw6Y2sE35R2mP0FilGvasXwG+xvwulu0n/16AkCUBpY"
    "UiqmMFcXSa0AHHgqIAqF0Iq6WA9MalooQ53Ss0BjrArKUbjUWmmX2+YoB83qooF8BrtBXmrVo6pLD0zx2r+4jv9z6M+c4PMnTh5F"
    "JN+2Bwru6IiamaB+4tLNjz3aS4jMAmT7i93sa7ORiUM3tYpAuAXhYBuCpMDueD9AHpdNbZXrls3BNBgDjPpBE6PrT4u7wOs/aCFy"
    "3tOqIdeJ751uI4tpkIupz/cQ16Sm7s0mQJRta8diaK6kNeuo96gwW+0LhmeL24GjA2oBkE50KbpfguKu20NUIyqT05ZW3ROOlrSw"
    "O8CBracTeb4sj+NeLAB57id82cOIdBAX7V9QsxZubNdsfwwpmu9hWDuWLuVLMNR5JzDaIWnTfdEIUS755IO9gHhBR13vPf17YVlC"
    "vwEM8hGMs9MxPmKDJW/RO8K3L+iw3M3LVH7dRi9ktCD0eMNkUetm+UVwpgXPfknC1LSNE/OadpJVDrmru+ppO+cfbxq38sG0K38C"
    "OT7Lpgz93nKdVe6JqzTPrqu0ZQ6Pq93ZhH9noPZNJMuRfSPazF0OWvrFApfHxCXxnwayhU3QjmGgzKDpeHvtUNEAM4PLDKTHGom2"
    "kpgVQOgdJ61Nc/vzZ5afBHwj3wPLmYoCzQRHBJc3R6wnCcOznAGMD0UuRX2i4blj8DhAw+0h7Mutbu0JaKsYgiTQfMbZTVwaXGl3"
    "uMbtmSsAXANUU7WOVcUFQdOmRj6K6/pJ520evvlpWLWB4P499eGFEydVrbk+GLabDb2YC4PUXEPERrAvuXBbAJ0HzoUbfeQqIGtn"
    "dNDSL9BAiQTZ6XFw1k5be+WhCpVLB6qgA0AJFR18BDiGTOI5bPi+nmXxnlpGZsCQAh4YA5nX47hyl7tN7CVRhVwf5CkdzTjw7GUO"
    "NuZYxCBju/WMKkAdD31dESaOehCFBTYbvM1pznqjCJo25aMUon9czGzNVW3zsQCdEmHdLaqqmMM25yDnr8zMUg/96xxXq3SMTPJG"
    "j4mlGydFFnx23Sa2yaY1KDKLdFDpBHcaIkkbck1y5lNltIj/STla7nHSzYNi2y1vOLfAs9ZfgOsy0MDAIhGaj1a4gcKdcJ1TNwha"
    "Y/UDysRZm7zHQ/YL/2/tdQJUbUqmRhNJq0v7VJZBy8vW3+oytEv7O20FpMFCrsVsEWmcWpP2qU1cTcQJP/AmvGrT9WjEulOjUYJb"
    "H3UmW20gbVT1uWeKL4WpVzs5oKKwMJ9wTaLofCZiFroyvvszIxAYBB/tfACSM57mhMu7m53dhsfmyxhNRvrs5Dx1DdNLLM1rQte3"
    "nYm4deXxiUrThjUHRl5frhZUbQOlm2Le6vpwSfkmRVklw/Q9GPhOXeX0UzWVU1ePL75X+gVkiJ+ugj//xVDK6cu8aT9dHl//TjeQ"
    "7990xWX5dHesesrBKuTjJwsX5WS+mhI8dADqxha3n6k8ZxbNyk/l5a+S9feqKKMDEGrSt2pux/XJ+oIcUidDxaFB0odPDpAp/rW7"
    "YTclKHWMj2AaOq37HPRJmjUXoEaPzWa8sBnlM7fvMr8tLq/af1OC89hizVUxaw/0k9PR06Za6MODx5dPjt4ovh4eonyUQbbVW+zf"
    "Rk+j/UULPyLraVUTyXNoeYNvnJFbmH4CW+1836pVKfNwuLvmq/TXXiPvYTH5MN7Fm6FaXNvVMuGTQBVpfdae48wXpVbR4KiFAOvJ"
    "mQNaKLc43F7Ov8svz3HMsy7NnRcGbzv6oKsSat7oOHxjdWoJ/vM49uppLAeE3uCojXJ+I5qF6KMCNEFLfez3D+lDAqdrZaYjWV8G"
    "fG8+MKyRPVsPqBhnenABrJrTMUHsIItJdmvhxL9fyRbHZz4Y8YBkJCrfGd7Ijc8yCLk/cUddDEtkblVqllaJjKd12hBWg+y6NbpO"
    "TmPZL/vtQVpSFr9Jq3Ch1SStaKIBABM765ZKmQygxY8jMHeL1tjjn6nPeVoOTXVRk81T2wPWl7CDKQXKGD4NZUEdI8hOnCbhfSr/"
    "N0q3Ui4WuntFHeRvlZpTAddDaL8U0SpOVn5+L1qvUCRkr8wG7YHObFTEdTS4DDXJUZ5FTWqVwCCXoyxhP1XheorrvYYVD1IzTIiz"
    "wt5zck3wzaPww/+CSn6y2t0JKIIpmKQFrkkrYN9gBjJuaBInk0CzcQcVCAlK1GDdpQOHMj3AEEBOTgUqKphV32zw2zshYvcuEeZn"
    "x+dxxj+okF+VLxonhe/AqekAdDfWEGUpZnOD3uA61kKcV70CFa2wOVXNgP+kheqkozaVU0Gip6L5aaWJ0/soLBr0cjwaCpTWvs8X"
    "hEMEu8UDS68ROQZlfHeojI2uPuafaLbY0mpS7kyfu6KjOOAn3zG5PWKVJ8ru1JTioSP+5V7OU+RE9xPnA3Sv9vTrtJDYz9pP6PQY"
    "Aa3V5Hhr1Dqdbk/RnF6xemnabi91yOsyd2jlT2OnvOxEUpa73amZzo+dmodhZZyRJUy2yl69n8Gonlo1uJ0Mpl73veh8r3P/BYxm"
    "VGdF9nOb/NgSI/i8TX5qY8M1bzaHTyFWbTv8qYTqmpFwihro1LLfBnewjDSHqCK9YnTpZs71sruErrPvBGtWKUHr3LTN65GXojIn"
    "7HfE+mEfW6PKmDyB6AzAVG82LKwYU7kx0KhXB624U2VUOUFZzgw9VVQllZwdQ686ClW87FthlexxdE2FsxqpVZx8x/8rOh+fGsC7"
    "Q8eXLqcNQeIBvbJmRUONCBoJXBu9h221EBxT5pK5W0OnWuHX23adGM5CMvzQsvyg915+CQnR7ili3LSVLBbo0TBzJEH/lJPsYtB8"
    "Feb0JJKid2ymPrcWDW3sNJGTlZxKjVsYPwS7NB69QhxLrdfg94G4M76oQQ9YhsPyAC5axImkQEbBu46a2IqYITTtsFekphe1zFbh"
    "OnOghNNL7fdL266RX3jqGCfNlhVjfRu2TptsKxqxAqKDOQtojJWoT+W2+lh+J2rFoSQhODuY+7ayl6ShQrYtX5TA6fV/Ak7HATg5"
    "vfTjg1PoPm7VB8H+T1v1WJ5et+p3mwZdH/WqZcs79T3/BruxiyQCFRuHNy1lbw9rPnkNlDuBPmEoWA4yqNLBTlQi0VmsS28lD6Ja"
    "vyMB6feJlJF8UNUe433FBifSjJqmZfaqTdqM6N7SErm4xaK1yMNzPJu0vARN1CXKV7FaCx3KNz9iKaQVqE1c/6wMEe4o32w3S2IS"
    "JtkZLTif91OWoMTnrOVr8xFJHAg3vwklUOHUBSQvRm1AGBrJ2osuM4Fn1skIKn3RhoC9FkHhOjyzzEoUsl1lRQjFAjXwns1jnrnC"
    "IFRCE8FbLgf2mrYA4cH0e+AkwhAtFkCbBSAUVQl5Vngt9ztNVFuxZSdHvpeDuSEiMWgb2yJbBTUSaBJHlg4PB2PXXHPPQUqEcjws"
    "uVFDVrKRQ71NOx+1zIPMi0cBZlpaRmVCGNrtH7wVsYiVi6y051PpkIY8FYGkJjgDmIIF02n7UaH9fG9SOyOsdkaXe8mzaHwb8rhW"
    "DXM3kZyKW2cE1eASPVsTCk4IChkVwyKw5TegagJZhjpOMABI2xWQx0lGfE6QD+0hbxFlqDiaze9bN5vMUvC1MvMTcnIRXiwSf/pi"
    "jqTTgEC+59cMip0vWr4U+18KkAIl6zLR5E1x1yAnTA4IY6pvqwRp0n5oNxs+RDeb9/IT2bPTk94yEIb0AuCX5AzvNZCXlRHANqLa"
    "bFInPQ4+SFUNcb4+rxut7YkyB2UjB2VtDkr6REmJpPAwOLOMwhldrLuks/S15L7W3Fcx9jGsEtovwr4GH2JD1dVZ7RMNwUfDbb2h"
    "R3DGTplEtwesduInGIAIqDjZgesirs2MqZJon5p8gdGYnNsCYLbOzg8O3m2szuQ48BIfL8DelbK77VGnj9blWX2evsHMsugNtTns"
    "+bKDPQ0utbyeyA3SR8UBoj7r6aQ4QMtnnWRLwWetTwXdntVJSPyuDOVUwPKozspEWmaO523LSD2hnhJd2YM9+5/dpGNK+jpIOpZc"
    "P3WvBJ93X3/svv7cefUn/r/4yDK3VNpcNslhOk74hcUv48Qs54lcBlEd5vOpthlN3cEbfzMF7w+nepav5q1NOA7OuO/Cg1NQiU5+"
    "xWLR+D+06m1Low2uev4I89t8v7c0cTQNQb5v9/MdE7VEs0nzE+T7NZAkiVqCGNNri8RZoTW0BDLa5TYL+EjYg1lj6Weg+priYq5D"
    "e1mzJ4vgsjO3H3NjkkULcspcNI5UVrfvlG54GYl+uwFBiAz3CdZCCy5BRA1ocK/Qsz+/SLKji5NdQyczPF/D+zY0mdzJzDsjyPzD"
    "JzNbDsjnvRt2TWesFCe9SjpKP2WAHm19nlAgEo4P+STU/AmuK3pgOgIhgJO47iwVISvdyYndZ0SRZQkqmlnK74SlVLVPMlxmoHZQ"
    "dga2a0TWGd2zICtRjJo3uPvKKZ6EdFw0AUIjn7h/TfmXikjQPpKreq+RI90JzZe8GMWZFtEs/yTSWVi78UEjH65dahmkdiphWcwd"
    "zrhjiAQFB6MeEFYHNsjk113C0HZDBWSea4hPfy2nP20s4oVdX+dyy2JV3f1wdGcYZXcY0j2r5h5eNjwN1sosxcBwD7wMEyHSE8NJ"
    "pY86Ah1q5Wm0KxdhjtkVYXu8QKAw9I15/j/zXD9ANNnn6OtOr+chNP7SegiyqGRSChStyr9QGzsAM9KJQJLUprvgxtNR8giJioHO"
    "LC+83CwwKW9m2qYYffkRlUuNZtwIDn7qT0KThUVbLIq7gOTqYO7cT8s0nBZ0l82ueCJmn9hOTG12LUKoXiJMrG5fZ0rUzmSEev77"
    "s/mfmJacfCVvu3q+RyefsDkR4xHhTzrtG0lqz/SflYTT0lt2dKweNmi4Y6vxIIYukbH9saeVse9g9Nk77qxb117CIgEL5d9aYwzR"
    "kuqoywWa1X+BNIIlMXYL8rKz9MvSCOqN3u8dOvttJ65YEyTVMCdmi2WwPagmZtPsmZCOZscsSjhWuio79NZlafeEv/wqjZoxtXkp"
    "ounSorir0upWESNDL6Jb1eISAbp8YrsUEEzXqKuEiFokHMVioacFHCrlxE3oZVKpqpzopFHO2iOZq3x1CYn/t9VFslLgCpLZNi3E"
    "uVFF+MDg0IqvPuT3OLtFUydxcsvIcaEu1Uhdq1uM4yIVe3xBg9El3wIabEg55Io1EWxjvrKh/y2MqFmOkkUXAP5bzC7fh6ePfpFO"
    "SGFl6zR3Emvbmhfji8yX0rmgTV8a+uoqSJtls4hNqqGwRB27THmdy2yWoRH7MWHnWFR2JBc4rKI4CjQMGb1sjfOYckhLvQgNjKSZ"
    "L9TZ9TmauvYFKWe73UKlvN+v7Ea4pGXmGT/OTj4/TqqhDBnTjaNRdAhvUli/qVNx3LUwZojqpt+/GVij10l0Yw3E1EK045p+v7Tt"
    "lMMyjazjnqC72njpsZ08ZfVJLqPTi0wcSlgRMl8FzaNFGSeL0rh7wlQtrEUBbdrFwBgRmPt1B+QLMSBi3WuCrs2G8kQXWStLbx10"
    "4bjWmi8cEpbTaKh+2ckqh35J+n1aFcXTL1/PkJmmclFaWdoFkYoQ30ni2Xmiias9H2rYeGGdSlonIttKo68QLJRWssyixme67uUt"
    "q35/FbXYELzt3+rokp4DG745wxTx3UzMJfTDLrxGQt3RAqkRTYhYd8mqyhgMJljINPEEzmIA1JdGrXjHowfEmFTGsPMLyJ7LLM/o"
    "GXuMBmq6nswzdEaOWFZdE9RMCykZ1KlYVlMB/pWcC6SL8SBq4ofgC+AwPVWnHjPdCpYjULbXbw9h5dFhqIRbiuDywnq8iEp3l3Uc"
    "P0rb7m1T6X1YtEdHclkRoyWDa9iHxUH/OjXcsXhfLPW9e1yOnXaEhZbcNGY81h33QLfmmCCM4TJr5urWO/5EOvX6b7RKBy9nRaQB"
    "cV6855RtafK8aJ4571fWcR0uZMKmts4bk1cDKP3FVLDT60yLgJ0RoDOgOXUjDK7RgxosFjUkaVB5IDq6Zdq0GJhaaeJstVbUAzEG"
    "bmo63qsKtvzouKLRHVc0cvahO/BCI836doMen8qJSOcyDpTcneoVUfbl4BpO3kRjc63ruqqf5+UUh2IjijE/llecMH2Gjy+wSNMV"
    "V5xMtjBZK3Fl/wQeJG/agbgo22zYzs+ht9LYLrOEbgmymvjz8VXbLpvk88+vV/r3ZlDVl59z+0e1nmnKPdGf/z+0/dpioY/uruvt"
    "WIzpQoNCPeFmiPIHu+o81cFyK2e7B9hXm1MgDk3cjmEC7qzBxbFPCa0FTcRLFYuCg1GyhhWcdB8L1BjVBVrrRvGsnRyrMy52LloK"
    "Vjl7+wTzXquKvk0CnvVJ6T2+HWNNThiQCmvJOARVXRFU82xYmvsju6d8x/aKz/j5acneVdRr2KZ8KFNamEXRwOUXlYZ3C/VYcng6"
    "6/dAVPCYcMwHpyal6ayBU0SmMK1qkxjKauj6uCpeBVW8K++BYvvoZlIW6GE5dLcw98pHjx6d0Cg/QhRJwPc1WDXA8maTi5FXYU2j"
    "M2Jj7p0kJTEzzoDCtfu9dfoQ2Pw5P29fi4wXjbjOHJ2cD3s0Rp//Pm6eHyEzMYmUz9q906NRHXzFtym4c1Te0k69KTt6+nhdY/bS"
    "D6XM2U+hrvU3rqO8l5+WEMkUUzHzfOqaeo25Q0uJGw7h/WeuV0EHdk83hl4dQq8rBtpgyP31l2Qe3LBesgsI8ftVq61ntVJWyeyp"
    "0k0bW4ggoZhCKWqwKqa0u5zaPiSA+MZnE1zJFiWRnX5Wa6KRceWU1UcnybtSld6AMyoDA32Fo9Z95CuOwHo/WIGXlj8RhxvP7Egs"
    "KfQMgz1mXQy45grwKFyQFQ9dAXZAthYE+6w8K86HUT4onOlUJpfheZz0KBmupQqM/SGBD+WmaTtP88RY4+WG7iW0Dc0no3uk43Mi"
    "4erWknAMqEdfl8zJh11Pa9rPodH88VA/LJwnFOrmU7PGuAx2OAb5CQ8UjASGr8uHT93QXjuHeTp9Wp69Ls+HgeVsYCp73xt/PiAy"
    "JAptQe9vQywj9jZvwRd6nPKnEcHRaN7SCLRHgAZL++k0lKednGcgMqg5VCjGhASrzuBQvXQvpQqIcG5eevJ1Ke5zsbvY0ZTb6RlB"
    "GlgGfPNd/Ym3pjWreocpe1cGG+FdMGW0E95hykIj4weBCe7+JPLpTw3iLzv5Z3LypZ/JLzvGyfchNrPj4e34N7rRKb+Vg8CVoRPg"
    "JeNAg/JV5D5tNn5/9Ps8BTJ7z03WH3dPiZ8DFP/cnRDPQfhTXrE0Aik2GvH5+oKQAVcUYOvXTOk+Lw2h22uZvi27Avs6FSVBoojq"
    "wYhO7Td5dHRi9Q9/Zlycp49z03tVMYxUqZZinRmU2XJ5h/pRPtRHR/GrnODxZ1bDcG2cOMKw2vpbyhE7q6Lfifmd8m/gV6CU+1Qa"
    "z3O2JofH250BLSv6xjfB4PQaOK47H3Y3dRluaszyWU4kQqMmaQvvmfp8CM0yIBQon6ZrQ9MkuVqJt94k34oLOtg43kLhSxlacE1t"
    "Ur6ibNocIg7rCLZS1XzKkt3Eq80TfbeopsWs0HVDlFx8iFr+rtxT42JFcYhtL7zH4TExBiPuZ+DLM8gkbobHjm6jY9jkH4qB32hO"
    "35uWnd+Yikrv0JNrck6InUWiKTT0bbt6LBJhfbFW2dacgbW9bMIa4coXHcKzW6oJLdXkoYOmid2Q8zQ/m5wPq2w+sFOaVpRixNyd"
    "nvb7PlNwVkbztInWW0Xk9s6qeLXmOXqDk5h46YjJTSLzV7QOD4jUHOg5FS5Ua+jNkDb5wyPj97md7/c5aO7rYqobeCTIne8i9+i+"
    "D70biqDUjl5/DbVmuLVsg5a/3ZMZpj/kkXVl+aawAPSmyN4UtMkMv2CbSHAbbxwc8c7abOrBhEgG4U8CFgO6ELtpQTW7I7KanGLU"
    "aNz4WiYJuw1iM6vv6/zaOuVS+AhvYXEneg1onPkX0MSMRX8trQ4XYGd8fdRMbsax+qVkyQXNyq9loEX2vntfdZdRCrNesznt4GTc"
    "3JaT8Ta8MCx39M7uOp7UXxT+e5GnVD8R0eccos2VgGHBOmXis5N+YAIwXlaw6JrxnFUMTJOUHa5T3+zB9AvEVTPsudFHMLba8I2C"
    "89ze7U1tAfGr700/WD4CBxBGhIJHkbLQk9BSSwLC4YqnPnV3Rsx/L0WUgEwLUCPcP+52tgokTWwZSwTdUi1zlOr3YTrcLHXZwPqA"
    "B8ujgmwO6D4sbF3ttxl8cDL/QYh3NfCiYq6/DN1y0JG/CN/vo82IKZQlSEfFvaEty12/So2weuX59oryz7KZIPSrOJkCAmnDXQUX"
    "vnVXkd/4OgBXXYjLbrgQM6Zu48GYwLdmlRwW39YE9Ilh8GpoiOZDBvEcvkTFuyvz/7hMtM5Q28rcPDQpwVpBp48UjwMt/Srq3Ku3"
    "dahd0tpIDAPne9kJ9nBoHD4iCS2Lm8MUTqb1ubvvM3uvrDsXC3XtrLtH16zDVdRCIMIu4J2ea0S7oLOPE3ldjDflKcgT+8wOj2NV"
    "hdkgkeA8eDAZmjoIPHD607+ezTXgAg7KBdHIKdz5qCZhoVd5e/XqpfkU2hbtlO/kU/N6NwoEU2SVnZxLsLdthisTFusk5Vat6nSN"
    "oB/J2E7DWIWTAm/yBEET3TSh4ZAQJmouaGUxSVZqOUmmankxSWaqStbUSU2ll+qPla5vTzUuWqs6WSg5Kt4Rbk6uzMuTaoH+J5dK"
    "UPT3kDuNttt0rq7TvGZvDdUSql3TW+prMXlyVcynlDO53dIhfuFRAO3p5ipf6m9ok/VPvoK8GY79JbcoXtu+x1t1Ay2wYLqoKW2b"
    "wh1WS+hft+ncJUMCnadXvGfUlVqKo/GKkcX1JS1OAxP4rJLXhD8saIkWc/o2qVkvPKpcGju9KQZF8+QZO7+ZEDy2Zt7fcdsNa6of"
    "SLc2LHHMyn7Yb7gXYLFSTqimFn0I2CqfBm777S1NWQe+j2OTErgx9hNhqapRBPICepzDC55uOmXLyVVV28aIeLqR28Ky9pJnwq4t"
    "lLaG4viYKWPnrUPP0yv2vkDnk6lNEoYiXGbyUi2hQIuHykMCcdzw2EzoelqUl1/XKByvT73G6vaaZvQiElV79LBFD4laioR6XHPr"
    "GJLz02A6YMdFx6CbJfRnFa9X3g9bZ7rCdlsDNadwp+9giN+GcnLZHO6junJpj20fwld12YHMUXqZlbSxLui3Tq6szhOD3GZDELj0"
    "EChfDLhtNhN83IXB2yxiNx/draVu1chuFsqT85pjCpPJZsNm5/T9wm0ngjV1HV9mZoGAd8yDSSE0xBIi+2KcsMhLkE7nWh0Jmpmr"
    "E399ELX7FcZUY6R3WkS6BbG5gxjaucwq+8lX3I4hsuaKRiakyWW/z1+WtMG5Bww817gjgmv9a+sNe71aEBtFmE5Sk4IyCGG9diiI"
    "yCuLfIipErgiUiuAiWSuwqUmNCqvQKXoNy6biTwBAMxwbwZijHrWBc0rsIWHYZNoOKCWaE6bjECYfWUU0SRWPRRa0lISOFRwktY9"
    "aJtdXpQIdDgSHta0GzH8her1il2gwSTxZExrdXU7hWp2MqtD1ZHazp4/ImoqQ7NHiPV+vIbkV+IkBZNEtHU3gbG98olmn3BqubN7"
    "RFNfz2ktzAI0yi/QxC/Q3Mz4CjM+TdGT+5jdKZqvpPJeWRt38rhJIOKA1mWFHTXZn8J5OIW0AjR7PPT78ZCrbHZo9VndOWAxQ+ze"
    "priYE46j7geHY7NzrE6Umcx5eL6uaDmIyvYtiJhCEF7ggVD8s9UD8E7vbtnN8ANJHRB7jokY2+PnDocJuSMzOY672K72LP5+QVtk"
    "vYPrQN2P5st8BwcSVEbtzkKKa+NtnVZRHfK2xh+CQ+HTqGKdNNH7t6bOW+EJ2uBYt8iB9sNVSGhg2RcyUZN0wd3bbBaDWVE3LcP6"
    "sN2hM6KrLJJuKCqKCrud32yIalhQl1aEVBo5eBeZ3K7BGY3rO/f831YBy5oJpgi5aC/aMcbmrLsyyAyE8m5PTTd3DqqdxrgfQTCU"
    "PFgUc+4zob2s01Xt9/eiQ9sT6dXeuDuDVetVhtjzcsaKQnrOQjFTqSgPhVu92NvPgFUYxgzjDsieAISJ8HjctnVxsSL0NwYQHl0f"
    "VR9L+FUpwWeBsjOOCGVjDdGzzjXOVbARA4rFQ6hMWcmkS7V7dnOyUz88q+vztGK9rDrK6biBuJGwiWZjmYrn8DLgTuY6v9ZPLqji"
    "UZBK217XSPUzfe3NCtZFYyJ6IdhT0bykOoAx+MVcfZr3uXz6CUikSYwegWO9v6ujSIhoVyNcz8Xq1+CDr1C+iQLnbZ2efWP6plj9"
    "5Vxd1JBRErYywdLy5RKGM18jzl9eqiWU0hr02qZUpcQZe4bhJrd0upbB4+MZPe5+egJGaE68maRJeUyAloTgkcvvfjpY/rF0VEqF"
    "z6hh/2NYBzEVjqH6Om/0OyJNm0LC18nxclFDqXOFXbhu5lXbJO3WbhjIxQg+r70pSOTVWtnTBYwB+v0PdeTeIlZIES9d9looO6Vj"
    "GsZXzeriXa119lMUB+KuXh56CayMIYysVbNN2V64HjhAsiKvZwTB1rfAU35GXZP9z/P0XR1NiC6sIQWY8J0AIs0Q7fEaH+ZWmuk6"
    "2O9The5N6G1i3sKSvZd5tCKs2O8/DrPaTUAtrmyLiHaDV3Zpgbh/q/aoAO8cdMWZl/txQsxDiMiBieOWOnlOFO40f68u3NWP8E9G"
    "jcxfjQbCrU5+mMKJwB7u2CD2KZXIkBhlBx+FirsT9om4EiMSVjLfPMCiPKIxdgeYsRPy/NYMxXHIAkwfwcOuaKrOjA+CFbszPU9p"
    "1s4uCWdxvwFc8mrk5qZHc6laT3f71P1gBh/F/67cNnGPPAe09lYT1PlDCdVQT+vAsOHs+HwYRJx6FHgYl1ifrMIRrPyacLejJazY"
    "iN1H1OlNcJh99IfZegdxgkQkVC8hg7jqMGwPnWEHQiAqUciS7NDICa+Q3tWd+5S1wZWF4k2ZB8iyAgh2MWXjEOWkiyfn+2hytYMl"
    "Zw5JLrs4crGPIq92MeSlR5CjHfx4fQg9irTGer1giFM3gEWOm3PqpFeED25EReZ/2S+U1juCrfbs5Hx4aiKSilzTuGSDUE8A4WEK"
    "TyTQ4gtSOGELJcz1/syqCz+p1j62ThtGc6U/E41STp1eErstJK9l/rFXiOTCDweOELrh5uzi3DiGeJmzQaf3JqTnyDyUsHJWAYd3"
    "tpbbJ8mwhSiPen5K2xaqHOzBTnpJRdEAVGZCtF6nEzoUCALS1ScHMNpskOl6s0G+281m1RmO2E71Tobt2YhwAMRIEEg1QJQ0+VlF"
    "04fO0HR2NjbcOHQSoJPLVdhrNu7hNOXEULuS2O0605oHqabn0HeGkzSuo/V3jR0IYm0OVISJH8nEq7JDqThkT+fqaTTjTpu14dEB"
    "w5U0OqLyo5wvd6HaGZXZFW0DGWGIBW/OinPRUDJ4DQlmUEQPIuvOoLgE8fEY2xJjq2hsFcY2mVelM9sp0gAPeOu03SOpDU8Enmz/"
    "ijqLw5i/DU+ErPNmQ8WVQfEOEv/3K0zlvKZvG1wVP6uN2tPbOtRBT5/nosxkGXDROQgKPrUFe52SBfP9QLkSZllKg+TxbzAqE2/V"
    "1WJJE1y2XvfdJVkaYtiV2bReJFAar9dGKRc8vr3+M6dO2//iPu5hSkuOuW6WnkALeIvXtbuGDUXVX/FQXF/X8NhqCce0dT7h97tO"
    "9RW1Od1ioaIgowXWdIq3IQN4/0EQttPcdwUKmXCPXjTPWXRD+yYruyJWoihFZVJeIVGTAQ0sGJtmqfLmiYQO74zE5vOfAQFN800+"
    "nyNc5acy2+/hqMKsSiCCNuUb2pQhINjhPi/CmwDsyZI7z1Pl1+dD7exNLP4/g7+V479SuDU6s6xt2xAiEZWjCtjJRqIr43vmiZNN"
    "ljypBIVVrvsZZVji2tSuF1H19+4x02rcmlIXq/BOo4lZgAAXuZ7G4etoXBQ2tjcJ7bdKrdGnBjodOAKIVurKrOpQZlVL4DDTl/To"
    "/oH4m49r5yd6b6s9rqMDICs6+m689szrLFq/v79czmb1cc3B8YRcdHV1iPoAiXzoXKuz7UoTCYOmB/jZIn4yc2SJ3nZsYX/3LDYr"
    "LDiF2EjvKzYPiumbWs+Km81mfD2O742Pxvdwu9sQojAPJ+f37iVhxNRXPHn8MT3byXyfMqMSdayOzwNl11DA4mJiRFGZHtSXf2qC"
    "ABqjVlhCloMwWLRIcd7Uhw3dv6mNfniuKquNLHroetfXhmTt9+l7GWfQmE4gokVJJ0fCar2sWX8J/qrzADH98+Q+LnSM9liOq/e3"
    "oq08RfoeFPmUft/38hC0dWiZsMkvs2UVBUXiJGcFmrTK+HK0UeuCyOM6WYLaX4hCe61G6WxAC82+3TPzuN4m8qSu6SsD02mLoLq3"
    "4K2vEUP+mvMXCQJk0iKOFND1KroF4XvjAofDXp6/Gi3QRY93b79PD+mS5/8FULy6jBZxPDpbnMupeUGvNPfXNsHfm+Qlcjpzppto"
    "QbjyQ8wmR8YWlpkTSqS0EYHhB1MFR9G5woXRRUlEy0yd3FdnczU6D1yEIxD4EjJ3amYplBidPpaYsfwzAYu77s8ucD91fbY8T0b4"
    "d0Ovm02Pms2WRldKOsH3WvGUfXtN2DdIYKxCeL30mgwNu5cRdBfEEYjRQHrWnCu0ydND70jsjIAy0LQs7bQsrVvNnTnBMcFVt1nE"
    "Fc871UKKC/A/UNPu7M5juQ+dx51bWSI53wQ3N9thC+WQoxOkdu9Ta3MMvqjZ2UrUUYF+EfDGb9wtkQQfcVdEYUPx9orINwLfP1a6"
    "aV9M58TxyWmr+MOE+bcwfQic8bKWYK+6s2lfVvlU1+qtUa8wn4rmO62Xj+dEOQTqwQaV/VSzH7SxCp1LfN35ON35+pOhklOrylaL"
    "utF0As8uXn2k9IYhHFiiaJ6Kl4Y8iJQRWHE46z7jJ79mf5u4VPLkkWQ1ERr51lES4rd8Rys6ZqyGhmMMYhaQ86B0U/s5WK3n9a4e"
    "5Y9yLVkbqR69jleLscKoJhE75y1YuSZ3Js1BwC8/L7AhOQlNCQtWIYXuPBT0YCMLgTZNmr7CpLGNE03cXet4s4BuT4lcNyVfyOqQ"
    "J7F+N3OvJ5sVA+u5OI+Twiq/UxY+Y35mkIjMqgHgK+NDs1mONxvuulgUpo+M72Ncj6l/1enPNAcXi3GsvpNnPP5hklf0/K084/FX"
    "m4w8v5h0PL+XZ2orVj/Ic91e0std+zIJxeu6YDoQ8IUV0BPjohojaYt07E6NZqxKep8WtWbKuBn7Sh53XVAUUVso9qYCf1giN6+L"
    "HSXBctrpx++BqT0rcLlaTlBHojebOnCkWhSho4UiKtkjrHevUVhVzGMDH7LSz8vN5n3OWn0WURe8d4c2XnVhN8CCgILpMbH8kK/i"
    "se4J+/nCU6OjJxIX2jJDRrG2KthKgdA134bCbppSAmpKki1hkxMZm5VJHmyYquh6Q0YXaFNQu2dokh9s8+fB0F/t7DOCaxzoMD2q"
    "nBvParO5dGZ2ZUoAyvbRPFfi+xcont5+MP6S2XMG7eylGF4X6Y7lr+MaSvYO7LiG8mE1hC5/cVbSyRLVWZOZiA2UEHP4BH5K8N+b"
    "A0LpBcmOCwrcT5fsunIsDLP4sSR894JmVcLM0MQ8PI7ZdpAPP9fXTiepZzrsGdtx7TXv2r+2/sD1XkyH2DQwmNXVAntbi2MPptV2"
    "KgzO4zLtBqof2n6We3Na85x6YyWa09pzY2KvBC9X1ORZdc6XA9xgfe5MlHk6vEZvxF6xClhcOsBpDMB1J6l1K2lbrKGKyFQL1LHi"
    "rk1WHdpk6TOgcWY+ztmZ8mBWGrkbQ3NtP2EOMosTzZFWIzAcJwXOwiKeLikQq3abINchtf3vu86/cTpkGTwxPCe2gHDJ89KpgBOh"
    "7t5wktlnyuekl5Y6LQOelnWHS2E0c3iypl3RXVIrqHfCfRiMfWakJZ+x8gcmABTYN3TEvIzeiJLO2Z+Ev+cVO4bDHXBEO1wV2dH9"
    "5Ksv463lwdvzIe3bajCaQM+JjTVO7K2VtwL5xpxyc7YcESxIxSZFVLHvWGLj0d3NJt9s+GKNXobzFH3hkcFLQG9E5GbWJOPR3XW7"
    "JZ4v6sFZYzYezS7GxOhBJIbLgAxBQ3HgFuyDCVfV2VdfJjDWcfbEhy1VJt5SxQWzNKYtu2M8tsuNPswHxv4GRgUDzNmpvBOf6b4R"
    "d9mMqVdzDx6T8Pjw3iV6L3JGID3Pt7/OofTqZS69SdGRusRGt8HXPS86Ljm3wx1LcGIZ+/3Pzx4fvT//fABbDWhSjqsyYQvfBNaC"
    "8XkKC263YcX3TsGkZlZDYwEsnY6TVeFIMdF0VdMi3fV3KnzP+m7C7l7v6jk/GAsCYgTvQntA0vCk7sr9LSeI2sjdvG1rk8KP6q7c"
    "6HIKPxJ5QWyhJDCDeFe6hZSwl5SvqnwqXijtqmpaKTtBDxeFecOTulstMbFc+Q0WTt2lKZ0YmxrJOLP0MC4YzcUigeVd6D+8KyYf"
    "JBcsVn8vRWStjRWDusvK+5zB+BhiLfdZkRpMzt5rJAAmfEqxnOEUrC9r3YJqXhbienU9SvTWGEiVhxyL99gL0nrS3iTmdpzZ56RQ"
    "vAa5uTqvVD6BIvIThNuGFTqBXzJRnnqA/YKIM8+Oz0Fa3nVWCY1Bzt7gJu468LtzkjjjD8rKSfcTp8dhk760SbVL+sImVZTkjsZZ"
    "0XX8ivP0RHHdjjeXGVxF+W7G+yoPM66iajfHF6oKc9S2qno345eqdhkvEWSTU42p0zSdokfE3C/55Apdp48FvMfiTdYAuPi/heKL"
    "pZmiWTohCJg0zasK5hEcAXuWzvhct95dhn+ni1D6TedWniYumnxYD7UiztoXXGKu2ZWpgS57c8oQU4RQlCsAVgXQsP0peMqzCLOc"
    "MquVFLZ7BX8p/JeVU/9m2bp4RiHQwrknoeRP4oL98J0kUeXKiZtd6p10SYddKjuQXHMHixCQPcgzkDfbrZoYQzMv9avPJqB3peMT"
    "B/Ky/yZwzUEcAD8AgOS3ML9T+5B/csLxHTZpu6s7p2ZjOGAN4q7c7tgi8dW4oQjgyFPck45j71xKChhfJIyLE8Ikg2Be6CgnCs97"
    "Oj/QXKgUsAgPL3MpbIIWGfEacwrmmokwf1fae9VhLHqIsNlm9L9NxDM9fKxl2grh6VxhQocbxX9EdWNlLrjSCPxXFV4aI0i6TLUz"
    "yREFORRBqGm5fX7Cp1O/f0t1dpKI6hlfgDl0UE6AbeIuEpwsdHtVTRtCi4K4J8oYuiVzVZQ4+OC/imuaJjMVGGkmS2VNSRcqtMtM"
    "Lp1l6Ug5uUlyS0vv3y5Mkad0ZNfVbXJjq5Db1+SUcvMXyqu1WllXHPDuQ0ffVNdJaZ/ewa0Zfap9Avu4o6SCxg+vF0/yJa0PJTyh"
    "/VRf6xpSd40B55TjZlk1Oqk0jfhK1wXrAtKUaOX5daIklOfWk7k2MdmaZKW3aWtUj66LaAVvZUwjNP6WBLRKYxeUFaKv2Ds+s7Vp"
    "a6595Xolt/ly6565jIfXkl1oivQ7Dt+AzAw3quq2VLlgk+CL8/THiN0CGsNDaQvXtpSA/YZE+gk+8Gma9KSPVxJ/Erkal4vybOPh"
    "oVBKtxHkDGvtnOnAFCi8O8A7O22krZWbjYzmtHtN9ZYHN+kOaxJfFNEEQypYNBYIQ3V6RY/Z3MxYnMyH+6EC3N1DS5TNH5BOsXsL"
    "GEfyvplhq3TEKFMTNWwqMxeUh2dFu2hxAne1UXcVqei/arWEDlP0XQ0LIHr4o1aX/PBtrUb88Getbvnh61pd8IMu1BN+uFsTNPPT"
    "D8R3ydOvtTrlh19q1UrSe2JP8RRVhqeudMd7BQxGBMCnRK8RAV11nS4dXkPIEtd2lVjqgiVq5RkXp+Hybl0Izm5T25IlnbIn6fBj"
    "PtW+lpCEaMsKwqQx2HtpgzhSYivn92A6YR+jxtDO7sV0DtMjSuV7scBvn5Va1VhAVr3X6bOCFZS9phczEVYYDJqmGBbpNTMRhrUc"
    "sx/pb8uoZpkErslre0nPB334Sd5ixQ5Es0/Nbfl390fR3R+F3x8JxAZp6JXptrCH6U0ZmYPMuPKz7ncMkR4nOwk7JgUXxa50ud63"
    "/8RXAx2iiBSKwFpBcbiE+aFk0sgRuOzfihO12zDDPcHQdM87WNCpQO4Dyy9tLUwxYvPo0BT1xKahR7XtEYf9Cr1wBSeucKhqvShu"
    "ihJO4U1gEbhUbV1yoQwnJdRYbhYxWUvyK11f6tMWxiyXRBYh8E0aXgArXCuyIiBBuo+zNUmbpFc4e1WYUPdqSiV4mEDi4j8V4eyc"
    "EmakLVuJuRq/tbhCVXJw5KJDCOuAIIDXaeEdR50Yk0w7NjvkHIdb3u9zXqJ++X6hCFtvuXWpCK173zjYXG3MLpZo67PTdkEP49hu"
    "uSfFWQG5LmSqBbEbUHiC5AMPqoV+VIL/XibFCpfEIDIl87Ew9O4H6jAxt/xgKZrXhadz6DmkiZKnhaNpnhYdouZp4aga98WQNfRu"
    "6Rr3yZIvPq+hXyjBEzAoWQbVejKIs3Veu+TK02KXXnlahFQJDSygSuhNqLjHhSPjaI4MHfeuCMjej12BONGsmYui4uPP8W7NdBgv"
    "Tlx4qdCLQfChjbdJG9LH77rtvC4iRsHqmdC+Xt2rMBoh3mFdG4p7jJA5lJ/S1iYceM5o2xty70svn+7I/rPQodLZuaXNWdPhPHRN"
    "9nq34GFZEPKExT7sFgs4gU7TkMdylFOEujlct2cUsmwNR6pBO48LpxTWszqcd1qJgtX1I1N+Qoql4644rY1Zko0JY5eHkHl7sZm/"
    "XSociEDjWERlFvsVzfc5oPFdfklohE48amHB3mOIW9llFhPCaIfRJX3oOA80ov+PeV3uJGE3FPT+2si11rAmFDR2dh7uFaoy2Cv0"
    "5lx6HJqbDnIPvQIwxtlPZvyzlyyXmK9YE8xJ07vw4bYdB3hnu6ErG1ZFpOLQ+baEUu9azMFNVnPnihXB1ZRpmKBLVdBAm4BFnKd8"
    "VZauR6timryCXtjITQudbiPBobViJyo5kSq1LKl1qkLrOHI+gPiL8QydjCqOLSRr7/FGYYQDLGmxX2l7b9Wq2YsFnBvTSHi0ArcB"
    "SpDaosFlUT6QCDnKJUZzKQ3uhWk6n8V9gnBaQCBg7YuBAIWnZNCkS7Ve8uZbDzI7GBIm9Q6ahAye48a6kxjA2H5xD35B8U7iVk6f"
    "SAyo12Ips7ZOfEYTzaYEm82fUajruwroirRg65XecdYYa25+PeFQojYGTNXvw6HDSiHYLH5grc1+quYDDwVprnI4kV3pEdU/GqVz"
    "tayiVaD7RFutKs2Rh7munP9se+ARUOC2gUjSCnVbMFInX2HFxIo6aDKw+fCJYR9it20701s4/zxmZreqXpU/F+2VmZZAu6UYvinS"
    "+bDjl9k7/6JviDVmp3YuO/hNsePT7JtCtMeMixzag2yFladPoP1QpZXGb5O+YLoJkzstowjSMXMnN1cr6ufUtvO+jEIHJmf5OW1t"
    "gmhm++eUcwLHTLEyUYXdAQ03ZJSUicoOAdTcRGqSbiHSbMOfJVEUnHtUdUPQB190K5EDsi/olbt6Z7wyI8Qh9xoix1ymvV40w30n"
    "DovZZpOb34p/0dMxgYNQS3fX5XYsn8PE/FBiJYlEOy5Zdqh5tETrAqlG41VQIwDV9BUTozn+Co2DRzSlHY17BHPFYEbJmmAxTTfs"
    "sxvEkbOTPtm7fg7dQ9uLRhvezgLLw/suht29e1kDWd9EgtT1TrbJWp6OqR1CJQw8LwqrqdeKPy+CcfbTNaayLuVIZJ3g2vD6yvlS"
    "02dj3BS6hDFrK1AatBUOJFd6J91D7UuBWokwyCp2gZfbcOkhZAyWnvpJoF3zvTmbcjfYWm5lxhwEut9/wZcXRrr9P7ScHMAYIScW"
    "7HuutgypcSqEDzC0wc3pQDQROF/O+WZwRi5XsDjDzibE/9OmomGaZ2y1+HzYm8MXAXaJSee9F+OOkg2C5kShfaVyaz1Ime6NXxMO"
    "Gp8bBx1MQDGsYRbcE8hPrzduEiHENvMUpgF1sks1aco4tiwO68f+Wey5Niuzt0XSDjwRgZDqga+Gwt8/uQC2ohsjvYDXOTpeJyZK"
    "QM97ka6dH5cyNQ3DxAhqC4zwG7kk2g7Barb2OHT+kmyCCwKGs9gwh+JgwbwgXfJC5rNXaut1c3qTjBl9Y3htPJbFRpofIQZdlofM"
    "LcSYQu4k6G0OrjYsXhHCDZUA90XyOWhv3LNAa0/A8z7iqfHuY1jIWpr+Wi/nOX37HEl3P+cLKw6henZ8Pmirl9VH2MQRCRPfa90d"
    "Dl+HUCe0hNSVkKuh1qGVLKz5TqZVxkG2YtkLkV0faStxaJjEsLOWkmXDAL4ZbpTcGU+YzEzmVgS+Mg9CdzrnH3L/uQyvjhZ8WXTV"
    "lXBfQkV5lLJ/TgSa4DNRfMB7fWcrYS02mxoh6IbX6Y95tHKh7tRUzdQCjk9ihJuYbJ1wRqetZPZGlpmOZmptB2MHJ4PCxQp9Fd8G"
    "VJNxq5BNkh/he2Rr1B5oZZ2yQ3qsTlmQC4/A1+mf0WvjsOEivcY+uO33L3up22e6o1JyS6dpYL+zTS+G2gN+/3+AigDLrM9Q4bi5"
    "TX8uoluOiXgBQ6QLdaskapzTminZ7yO8CEkGY8vFYpML/pbKTyY/lvuUcjC+5l/Cot5QhS1Oijq6COx1LgjULjq5MAEXitZyRE+B"
    "qqioJFL7Rvv/L9w+Ozloy6jxRQ6VJDFldsYS7EfR2l7R7rk+KmZjozFqECMcbm9Di8CO5sWPhfcstSuIlXt+jgVEZyO/NO3tHAdl"
    "DpxO8wpVcUJ1McSfrOzmWX/1c7Fj8LmvL1Ix+1Sb3fu/uIFtWbu1Fi2RgN8NIvcVgYO8tWWXnL1XIJGBvEyrtb2FDdz4OIsYeLkn"
    "AhVGnEDcZrOzErzx8RoaP3lVB3GIMXlknFRP+ifH97/sfJ4ElmZ19l0RwVf8HBHnKvn8wDvRMi54wIo3/xYkSgcSfxSRWMsTGic8"
    "O/dX60zxBIseEb7gS/0ejajXDO4S3QDLkax3zG5NK+DjOutVm023p6a6IGTbd0XXP2G4iSXst1WU66WHlcb8NHUdd9cH/HbXEETi"
    "DF0x5b7Z0JiBYXIz5tJH3aUx7/f2j53eyq2CqPmFehIC2AicDoi8xn1B7zVsWIs4YUclgS/UIlrLqaGNOx86RqwdHtzx1cYLexjL"
    "wNr6CT43mVn5wDx3jPLEMDXI6TSaiOSjf7XioOcl2wvD/51RVpdvXhleKCYxk5dYDocacXUbfzC/FqBefhHbj6405tciVu8ZZXhT"
    "pW5Mbar118Jv1h/2pNp3uPY8/aWI4qGhaJ/KBU5z0ORei98yKDv6vcH4YxAe0IhVzcnQ1yugJGBINNsIkXV1ViR/INBzYswa5Ewr"
    "klwZ5Zg0Dxyvdm9eDB4pzOmfG9Jh7XEJ3yoQ8S2BwUGIdrtIeEYoQjjNrR4dM8vHjrvkrrAfGHbKohxEDBLaZd/Bv9WXnUUgujoI"
    "DbcPzne/tduuOO+E24b+EuVBBICcPuC0pZ90ii4fd0xtntDpO+T5bfOIqAaaoanoshuM84k6DEJaB8vJbII1sa+9daZc0EMndsWe"
    "B9kbA5F0tNVRN0cgws0TpU8yUfnNzx1NDvWe2r/KxX7uuptbxWUtrvCMiANZJDApldxRFsjjVtpkuZgpkOMeVkY2l1C/Vr2qMepV"
    "gU/X3MZocT7B92ADqulKIp7EHTA3OndM0XbWkJABTEmmw1z0z6asvR8zFu9VXrQ2jbP6bHqezpNoYo5rftuHEijzyx7q9+cIAs5a"
    "+bKb5ujhMV+nV0GQ7Boa8xOEhOmeW9XeuUVMKQd1PGt4LXB91agCpl20ElBqauDs2spSAl+zeVfh2SoJi7ZZ1es4pISSlLsrtgYO"
    "tQtSYLNV9s5YArgbeso6P4Jp4wC6jd/k8Mx2y4LQOEACFl+BwCh4yQRM6tSp/K2db92CqBhOT83VjbjTJzYpslumhsbjYMLhUuAo"
    "tGGsumSx4rYizCbUb09nQKNJdXZyzlJnuKolEhAHuDYUGcLOeAK4Fk+6+WHWt87ZP0fhUHOOsO95Ug+8WJ1Y2TxgfStL0lRGHduK"
    "o+bA6jOIuZf7bG/LROYyFR3RM1rM89Q0ju3fsGgNlqfGM7JEABiyKvYuE1zvsrNthwlu/yYT3DIk9yY0q0s7JmFkcx/SvBRTgEm8"
    "Y2I92fOsWNLem3DsjiLnm/ZozsYX/qp9T3/G4VMjVABbbCtjxZo6nWPjTfn+AbcQmTCt5TYxVxEsl+Dr8Zw9yqRCek4J5uJPBBu5"
    "d8/JXqHuRDSEKBa1rK8/tNq9xp3XGN4cqVJDQuCLmMCP2QEpkD6PL6daJA4Wa/0HFdB+Pz5Pc1UTzKaVinIw5XWwR2O36q0JsrJI"
    "z+Zq5uiz7qosYrUIbKXyUNk90J7ssScDhv48Z+Vy1lkei23TeET8t302tPBYVZwxUNb4MY+TM3DMMbH+eeCFg9kDH/CiNc5aXkfW"
    "0KOixZTn0Im2hJ84UfVWTfIdd05s/QhNwl1tGBxJzG51cH/hECAmPmb9kyZHtHXcRFiYK7rIkXpFyIjzcnBJCEXn+Q6Xhq6DZmJx"
    "gEWTnB+epsNu79xWIqxdL2cuVUxgCPzZTkdNDw2W6xcqkEV6QvB4UccX9z1/NBrqLFrlkXUPytGqCYhGY3uKT0KbWkjQc4kPrWbc"
    "to8tbEj3wog7mEOsWPQmeoPFwS6U3IWa8AhbfgDyk5WcYVC8offS8lS0tMKVwP7EuAMDOsgFpTTp2saDP9kalLpDbGASAfJ8e2Ju"
    "GgOiY0tcR/osD5Rmw01wlXf0rvBqqA5sUhiG4hbppx+fjUYGHVsfrpXxjWvZY5xA8K3KtLhxT77jm3TH9/cUMi7+MsOTKcMJy9Dz"
    "6UKFTlGvkNfYtiSXxL9IfyApKybGw0gywjpdCxhZl464Y8VPJT8ugPBE3ok267V73m2NNTv7zLaiY3FMZ4JlF+lHdgh9oVnHppJA"
    "6MbCvg18aaTp0X2hYKH4u9OOy7+TThCEw2g/dTcJ97AQfLJh2G7lEsVjP12i5n6iJktpyyECYeUMK+ZkbjMoFxl7ipWxp3iaJ7d2"
    "zo3vVrGXeJ0nFwc/fMgTnWU3bHQNki789gYWQKZQ4H7eZLHbYtY/QRTP/Xz05atsfvBLRJ++3Gxm7BwHTgdDd/edvOoZbY+pvcDP"
    "s2/qaKqMZuSMMsEOVvVa4gvs1rMfbRm4quDMAnyCgbbqNg2jmAeu0uFulZhr4h+8bZU4hwoMJr0rc5+LfW1PHIggaGtQBeHui06T"
    "2nqJkfamQXubDYTnjKtcQ1vjssIWl9Az1onrOTuL73jdh5PfIAd7pY/glFlbp8ztthPE3dvX4wpwGBccdpjIXuMUXhPtXEUmZDv7"
    "h9upzR1KuzWVUlMjhrvlEJIndgi3H97AHdfGzo1v4Z1vdZ8MV+rjHa/q2oWBinZrDdcO0wIY0bhSb35a6SfP4MtuztoZLMVn2cvo"
    "Ql8W5RsWm0NH1rLBNpSBvfOWzETAmqxb9lreHVqjVnZyIPA3oolFsJuvlBdbJpfQg2gYiTJ9yF1O58YUkOpb9PuLQcGxEa76D7Il"
    "9kTgiOuKvQ4/CSFiKuCP7lyKPzzulBr1+9+5uDd0RBvNPgQI0KgVrqIE11N+BB4I7CZx/C1i9icg16+WjsOd8dT6eV+wHj32j8mF"
    "UpLDJJh8Rl2XehbNOOTwTzj6v/b6hVTvd3k0E/XT3Y53ImAxzXWdXhMBpS7j4XV2OQj9DE7j5JL6ejlwjgjhROfsXY6rSED8VAgX"
    "GFrxVJu+WF9+m831ZjOi7ixzUTzgKHZB79R1v3850KaxvUl24bMcEG0R+4f+QrixcSOoKqFF6r+ycEaemp3sdV0KBJJMXNgRbvmY"
    "e+dlkFlat2DiVaAMXH/xqevYDyH5hoXshNbBRduxdkX4M7GvxEZ4cmCLp8chNTpPJ8O5F5vPLYdGrOrZnIjk7GcCV3qKkx/Nw/Ba"
    "WPJJt2Jg2FynVnJjEq3CiAhiGSMGEsCV2o1uMpWtR4drOVxt2H2Icwz2lQlxFNzrX0kIXXm5HIpX9xEoX0RniC7Tqy4ci9aGAPIl"
    "7gIALDMGD/b2oXaCtClX3bGEFejtUR4cCWeHhHAC/akPNhit0mORWk0NtRMRDilLXT9/9+plv3/lX2zQr8UA2j8GPJAjeDW4lvZA"
    "NBfjxKzSB2JaTJXDOiCzVRUnNFmXmtdp3sFK8p1nbvVILmpWkLY20OVZqCuOs+INNPv3sTX5votGeiVPQCzUH7kFk9rNF1S+QqBI"
    "ziAXCIiEjgfKI7+c54FnI/4/3PQQtbvArUWVXoHl41A1hbmPcxZ56AOYv4ox43a7QkR6HZISZUBKYIrLgJTAFPRoqI7m6c5QFMKd"
    "QBJw1ixAWJd/AYFGT5tt6emv2j2mw93b0FQ03jNDE+7eBvLWFj+rdEIbb7N5ksN5/jRFIL2Js2QnNvRlzi6qN5tJ6Djxfx/E2YJo"
    "26SkLQ9aMDjEDKW/hcJWsOctzqQJFCUdPLW7AtoeS2chzeeEmheEx4j1E14FdHKnWP0puW7FDiXAPrIjBMij+/02PBWl8oZXm6bU"
    "n4O1fHPnoDkCa3cUQg1qj5bAVFlqwlCiQsCs2D3+LAisk1nyz3wLcN9yD/ctVIjIkyswGFes6jLJJvau/YrIC0dqZRHOSokUBO0D"
    "PDzpELJncKUyCzoeJ8tHxwSIxADQ9v2bzJVRWEiJLDDe1qODyGZhok1xeAnx0NEzuKygNYGI3Hmp6/fDCDuXNsZM2Fe4wf0Ejdo9"
    "9NLGzUjb9bCXFbA3HVgrBUOYwjI4mXbJVEqZSScmbOl7YNfJjgusutJfjEiYT3122cpKY2hSlFt0nT6DiVcVIWAQtH2aAXsNe6rF"
    "tx2bo9RE6hIZVFMi5VvCFoYwYY/DT1mXzHbiRFFkeBGZvciUEh2JUP65quYwT6vBr4gsZQk1Qu3DgEHEo/fES20wpGB4GJRTHzC6"
    "FLbzMO0ZdJwWxj7AFBj/oD+d3qmFNoIp66dQYlOkxHl6P/AimPpb9ZkImCmxU8tPr5p3zBf4hAZ7j7aTVl2sklKtktreUTfmvnIC"
    "JsAcLze5ET6XNFaWKFD/gFoxJm2Mlko3RRIPPdCMNQElOo7xBQA6Lmcz9nhXxMkcarND48Mu/fKBMh+cEqgIgEUXd5RL/DPVZgc7"
    "lrTpBKLAFSv3RtN0L7rUJymlKV9b0paWNswN5Cxl7TC1ZL+6QuW6p3SmrtmD4iJa2rNnSbPzUcN5ouazQnE3Z+jmKrVH6beAN6Qx"
    "7bXMWafgr7prD1h3uIYdLmKv0VUp8MuN0TNjRZb1xSKhOUIkP1n1qWKfJDNxQWC8YL6sjaaGm+I5TyN1sbdgHniCMASfYpgqOjdb"
    "P3eKhvBax12QsLMmM/qaN61N5NkS95TDBYJ2Gr+D4rJYZ7sJsuFpvW3ctxlflc34quwqb06v8mn18S2NM4ptslhZMR4/BSHGHh1l"
    "TjLn4Y/nxGoJmGvFbs8ta1CJ/CNY5QooSezMlwhqURycO7sxnSh76NcU06h5RaMQx9//51ebzZR9N02dD8LpnnicsrHv7Jzbp1/0"
    "oBv0RbVpmYppyhZBKpi/GsCkzN3dSbwLvh18q9nxps01m1nvSql1OkMbsF4ZFzMTVuHGzpfUF7OnRd3e2o/D1aAgUFvB+6Xm0KiT"
    "MPYqTcD3ZbQKYGgO5+OLjqfzEIUP7a1BoAY91BZP0rgZ4fJSidaGuZVkx4+zXNxb20Odkjjq8gvWtIQG/1ZdHjqXcb/l+D0d0tMY"
    "fBYsR3KssKHd54AsmgVCmYVxTjAz3IjIK9fXoLanuxIm7293xqu9Hv1Vtu2i/yBj9qbff4KMDKrQxZiD3ie+iTAmPmcL/DvYZGIL"
    "siU1VfZAioLQWxgR0G4ZmruRTg/IZIEGNpu0hEQ1LY26t+VxeLbM4yxFBNTBooDG9hToVxTDhsuHs+HS80Itu2gF+44nZt/5gfao"
    "pl/ulyG1bR+2q0fT7IkX5INimdEwo12h8IyGcf2pYUjXj7t9tiM5OqEOT49OpMurhymxPvR/OfQs3Eo0zlau9yvb+5VIV17yxV0c"
    "X8v93e4oAi2u4ereve2nW5pJS5+Yp/+spdnRkVoeHTGOezQT5vkh/BcLJlvCqWCqH04zmJeDWSjcFFCXDN781KiZT/TtKgzL3ZSv"
    "Hi1jN8ZhjIsYzKG9i6G8Xvq6SFfqiv4uUxMIizuxSq+kHysLPvrTC6A9VQ8hG18zI0mtRHt5pG5p8S/S5dEVjfkGAo9TSqAjQpwa"
    "XsSmzWNq84Kb1OiwAeNVupCBrEK2fsV3t7eP0ot4TQMs7eiGlhPcigid9QVd/+IivWRljFJczvOMoZERDXiEAY/g9pGIQn02Oro6"
    "l0CMvOjt2egcJG86Mpf5hVOKycIOJChboOyKRls8Sk+z07RIbnCeXHM9xfk+4Khbape7TMfETXZBGFeDzZa+tcFmWaUXtFlWjzBb"
    "R0fOYci9lRJHBeA2z/S9E+iR0A/B18ySW7Rzi6FMLY0rMyCGbb8M74Ju4KX54fFmw5ZHNBHn2S0GiGz342RErUKSeBtifJldc0NM"
    "sJxbv2SBEH3uFYhXAU6fWqF6/6v4Vh/ylm9jgTjX14z1feyGAUck3cv01ZfxZBAEKyW2y32diNv9KsqF8egqe6xC9RTq08qGraT6"
    "q8gFx21DTxCo8UMen5oDuOOU7D4RIJAnzYVlwuzH81DW3csRLyWz3UmieUc8Dimc+aQM/TM3wuwcBJC/TeEYTXCm5cOaQOHSRzSa"
    "IKD0ylKZYEsDm6msgddi2xTxvKEBWY7LGRMBbLPpSZeHYSr8ipqgP6o7PJ2tojhB8D+ukF7UhO3YtnAyncETGY4ujnQjM+o7ceHh"
    "DKij8ESFXMR6L2G4kG08kE325CnzAOxWgQ67lTGrCTS2XhCbfgN/UHpRgeJg6IymfF+92czhWdLcCMt1N+j/xrl+YcroG0Q2NbtL"
    "6DNQSTiajfCDp54Jovamx2L+qB0E1i84gqx56wrUC7gcrJb3r+CjwTBtQEgcIDYjTN57yT7RR+zHBJs5ZUeZXW5O1lwYkhFCWaOh"
    "r+LTzg4MrllF9gtqK9h41iw2MN/dXoV3K62Tn0vOMbfyZWbUhzvBhJ/BuXYCq/B5cHkPddI3RNBDRsV7OmMii/1znAjCzU3Ik/4X"
    "D74kyCT+maXUTMdNTJjcfv8j9DrkGspFFDDrMTwwTd6QcLO52myuA1ntKJy03eE61xhjvnSKROmcmTUG54/WXsQaUOGe017Z1iG+"
    "LMBs5mzV9cZEzuoV8fpGd6bbXCMR6llr1rsokC3cfUUnUFLRiZMURoao0jzjUCaJJtKdR5pnC1bGM20mDSQF/1ED7EOe5zWQI1Om"
    "bh1xgLt0iLvabUqsLjOLSvgezd78hjD4pgd0qrbSIeATdbMTJs1cff/VvffpjvxrfcFhrZmRI+xJPBohGXMWEZqhj41awOemuNo8"
    "ZSE6/RcJxUqzTu+gaasl7qlh9+9iDhClUCkjPksqdlwbhPCx7JlP6hSAoIBgEGrGhh3YDUgqsUqHK+cWXzFvjUE+2UejBFydmz8C"
    "gGHlr1EqOvyYdqzO3Q0owa9mAN6N3WRV+T7qv4h3043B5F3sWnQipslDEYRcuYMW6BLin5KDwSGarDM9ya7YLdJWvQvX8E8jZPMi"
    "4BFPbL9/Ac9m8mLwM1u0ERa5dh82G/GOiNpcFvkH2YVkSvUWWi/2NRNknehODKssnAq4q/g1hwCPMF26XibXgKQLTaB0S5gv+agW"
    "bULdWkySJ2o5SS61Wl5M4MevTD5qVcHB51OtXjsHnvBjesYp52kRPYOq5NpYUr7TLvQ4ZRAVgsfLZfJ9EdGnpzqM9nSZR4KKtDlI"
    "223ow9KqfIjq3hi4vLgsxc7EWrUZhQ+TJS/LCrpnVXl0w6kSwq+cVFMmEvxz4IfrqoXGiJ3GwD3LiLonUhbqILaidK9EACKzrb64"
    "r1xYjy9BgBthanr0xRf2C738M3SnlodWtRHMajW78e3IXWPue6/1iCpwUJbvmT0H4o0iEGZYd+hwmrOnV1zvaUK3aS2ODqFePMy7"
    "eLOX79/ORIRgHC3zMCXCPe9o2X1xnz2LcH0psW/4JbyEc6nlfQVb6aBITxTzbnO2HUFOczH4NGcPJR0NvpNO1ZLdVZx7T9ncdaj5"
    "RP57AIQXeeiwTMwZseHPjs87AiWHnDCLYscz8QY8E3GNDWq8lxrLQoT8KB37dK7gi+vhJF637OVemZA5dcA4ouq841afGK78YTWM"
    "mzS/Vz16dEKVlGfNOdWT5Wlz7ySp0mY4eYjU/JxtDUCtRNwEJVGzNBaY0HDEdq7eVo1WOMcwPzp6dExHFPJVCKkN+6J9d0U33Zna"
    "jQTFaiWxD1nuL2fa7uVM1iY30FQOHKjlNoxZ/BcX65p99ZvzzBd+4gqHVzEexweJQ9v5w52mmoJzYy9Onw9U0LXGy55AiyZMEa/n"
    "rML+UVTYxUm3qUm9y31w8ame6brWU+a3QqeZzwyiYBzWvZRhRffWiIAbZ3ihWUcwTKSUb0qrTf9mJ9bJ7BJE8dN8J7m9QfLr3eTJ"
    "AskfdpMbBG5Rj3OYj/ye7zp3iTQjqce5dIcyaInuddYJDkJnE+dhsoUyPc7PnGk6AagcizyG7/P0xNf/JjfhAuP19/k9oln1Q4L+"
    "33NGntRaqD/rm/umY3mwp4n7PW2h7PecGhUfTeid+p73FWr+PXc+jgLfaC+6hk6mcmrpbUc2zQY+3otIoOAVFPkzKNIt8KLT8wxQ"
    "dQ29Rahms6+iJDSgfZl3/adZlCi3JyAXOGxEynfj4mgjTyOOr6ChwKkzXiv1J1LB4cIt8GyE7y0/EQjQeQnPzvuBUNhL6Hh8T3sF"
    "AV74S3YXlZf8w17x1kXynAZLtX+gemdJr1duEx1sBJ5CuSEwUUoResQpkkvcxuOEjWgkTozFyetgfuAO1Dq+x3OX8FA8qn7/LRAT"
    "s/P08ie/GN225MeyqxMhimcuVmlguy467c6smN+sZp19tXp1Nj5CbSoMuDChBUUX1bJpkiev4dg0eD6FL5kw4XGQvTHq+HCneBzI"
    "IfJADlGrUL0Jnv93BBjSCe8hXUbf3tDabb3Xzehf0N5B2CqJnUmENbzWzYs/NUyxOERboNezSRGaM3uQwIuVbLFeJduMsrnePQJh"
    "0QdbPenQCoj9arcje+QEDP+Zfh0YWHyd/zXwmCBdRj+5hgGyRiRLxVvNklfPnXZIcAj8K2dX+rbfuel3HfImhEfOqIcF5DpsY00H"
    "cWK7zDHIOxE+Vc1B/yrrZZc3+GTyetk2MR8F6U9s4sPRGqDIBrf2uCNFqNyWrSEupWwrim7pRw6MdC12bXdb/u1JVL/QLV4rOm/p"
    "JdsiGp6cnQudJB9z/r3/IEHo3xixU2DXlX3JnuOy+4kLJBPiukqwXeC+pYu77rYmFigxM3HyvvBvZ/MKHpjiZDeEyXNP9waeVq1p"
    "N/ZsCNEdpxHBroISBZTRsufwrEANtjGVXv0NXCEa19LenBHGnBHG3CEMCNJmMGvOM+N9x2hKMSaJk7Nc8dN5wj/g7Q1yCVSrQxyj"
    "u/q04YgEB1Cn+KGDB2wiv3URgv0krx3UoAfBW4AmAuY5mF646rbGt2+yigny7OSrpNrgXxebdI3h91DLvu5WgGc6rn4ZTbLP6u6S"
    "Brg3FCE6FOyJuAARB1GQ+33AVhgVOUDQYQBkl9FFRFYBeZl0lYFgEQHpUW6n3gjvgTVZ/Kom6NpEh8JfGBrbF4dYJ/1+zc5rVmpi"
    "wjKvaNeuAl9NOG3vjAnVHbtN9mf0NFdWoBDuRD6ZDd3k3SpKsKfXtgiB65/BWxDlsLORrVg5oAAujP1oxtphHL+BHk0UKcdixQmj"
    "WNbpRlO2rza4fEj3/Nyl2PTcqejoLvN4AoENpOeZTp53zen+lYcBkI5Dl0W1kbRbRWY5L4J4p7R3y/Tkq+FO3DfKP65EHCHXK/2v"
    "/un9hlgzdfZyILGiShMPS3FnyohVtIIvxz5W77qk421oVeJGwx4BQO99Id6CYW2aPi/Z/8sXCA5GNTwvjd2nRLiiTCn8dNHPfRXM"
    "0iZldzdBELkrNl523eeuOUPH1ut3td78sVUjc/QrdNNoyKVm6UBAQdIeYc4IzM6+Bsqjwz99MAzizUP3I6AEAkbzuTAzf8t5ceAc"
    "ZtixRqljYyxoFMDj1umH11Y/PDgmz8yjMh/PA2/q2ruZiYOT8sw8UxH+PQ/C/u74cIe1N2QqBfGO0AGHvrGcwkEc3SKO+UY+LTPv"
    "TRl3/kmRFBbgS/vQM1QClyhs3ACoGo9tKpp0/gQCh8ffObcMxsb4puSE/1FnlHYu3OIfuXjD/TYPfe5CjGg34reBw5VfjJsM6yfG"
    "mielUZmVg0/gc/gEQmjrNQSU3+b37inrnIcP3MJqwpXd0DysFicUnaNErYxccIwI7fjZeFbkZ8jwJDfL16F28L3mO0MbCQUfxZ2c"
    "VCRBGMKXN/6r9zdny4kXZIz4Ey6Rc/chVsVUsuL3bCyRxjtxiYRaDfzSdd0wW8bBOmK2nfB+72rYPBEtGzoKSf4sfKIZmHhfDCpw"
    "TjLarp+7ohNcgg+yVnzktY6REhc7rTHSZkaRX70LPfPS4STcUV27R6KK6qy2kg96O1ZWpmS4kVCoBK/YToNOXtzNhLwGsYeRcDEx"
    "PIz8XCzk1/xABZfBx/y4ZPMwzU0fzCq1l/bB1KfNbyOddUd5hYOfiM2k2qqKA82lAAKG6YpSsBjpy8LEXWAFRigHTkS8D/95quL9"
    "+d6YUP+Q813M+xzhI9XdXOlqaFUzIMls0yjUrzb9iMQ7nfjn4bhMMECuhTGBEjflr723wTqMUsDBVhM4h8ABux3ezdM2Gotl+ovv"
    "T989/v7Js9Hps3fvnr09HcHOH71LIQiofMbT07c7eYoqNYKqtvKe7dL3uZ26u7l4sPbKkMqqrHrFR5oB9kahykruqN4TU/Y+381i"
    "dFi9P5WqQ2Hsqmx+yf0qIGDwZfLKSJ+MKB4kcWXZs33ndlt7yQYPsGhuyB62amKU6MScsrW/KomSsgqteVZxC7FRdA0ijlI7ICOq"
    "IDBvFZI3gn6HOoznddhDl0QuYRUsxmWRUKbLQobBOxUEEt8lEHp3AapZNBrs4zQAlxmHgWTw5DjWsDpILwjoiBI9Vmcunts5PDzf"
    "EqfEl3QIaI0TB3GAqW4Edxd9AhOShnYCu9QQXfayoiUGV+zcn0syAKICUmfz3UZMlltvXilTt90isvr/y963NrZtHIt+vv0Vkq+q"
    "AuZS4psiKYi1ZSdx4tiuZcdJKVqACFBCTAEMAMqSRZ7ffuexu1iAlOymPefeDzetRWDfmJ2dnZ2dRyaDGEnflzXlX4rUJoDLT95y"
    "jB3lddhyT2+ax9tV+O/IRdX3QIu5HY93YOoQZ1ReDPO0GPFsY+XV7pIjmskY7dDZi2gWRgF3OTS7x10zUY86glVOUZ1ZhDycoM7M"
    "ADST2HShF+Zowa0tl06oH5OBXHA0XwOaZ4QghVDLoYeTlJFlM66IWawE2XAaiTncpClzxNCFRtBCVBeYIW+OFMcMHjc1lp/0ampi"
    "JHvnWqDFCgf4lNE9OSQnx+OUwccyIghy40btlruVGZ5mXlznstxQPVGHqPSqO0fQRpYuaUvP4ZmKp8kOVNTKlI5dKNUPVTIFeSRn"
    "7uSh3/RmT55ipOcuP1yh61ZekfmQr2LteFQ5CmE/N36YwnHz9pV3hXeI5L6nzz/QIMW6PcMXw6OI+fHs9t/VAia0QeOwMO8Vvs+Z"
    "LQxjQxh7oVEKkeONZ1VleN/E8ZKLBXoNSbV7O+k7B2a9MWS83aboHS/Ij/AXpbuCG1H/C5M6nQjPVnLUHEYyjvVc+SrkAyT749Jd"
    "onqgPA298JR4C72aii/KZij3TO9ZdelZ+ix23OZee6/VdmHtKy8kt7BP8QnvM+zC8edDdwE8NT/vZckCr2PfQQFyNnob2wgJqH0b"
    "S9r6JoYR3lruNRry3XEa2tJSNNeVDDt8RwM4x06HkH6tKmNB0oTBsLg3ML7LLJv39/c/f/6897m5FycX+41arbaPN+PiZGN+vdc7"
    "2EfNbPrz80tXHOsv8uMJQQy/aaheJD8bO8fx7u6xGol0AmO5WXAFiEY2yO9gkUunM6a+PyexfhdOIN/Y2CvllybfzpUFB4rZBlJk"
    "hkVI9kNrpOi1xvRzwUQs064gyiN9dWLdxChOzAzVgE2lTqhUtJaFJ98wxTuN/nqWlv3ycTDAqHguCWaSvSvglsP5TIdhC5E6I5Mc"
    "ni9gr3VVvivyshjm3HTJAzDSnWICQgh3vaKjHrOUTCO9Ium9RykgoeDdD8g5PhqjlVz65KVMK240Wss9/XCgZf1e8PvDYYvzBPHH"
    "IkhuTwgkKOmiMRbS5BilJJNpYFAEUiY4Zve6C6FNTgT5kBVch/EiVcPK9uDkzpZDAzZntFBVGmOIm6NlRYhBCWtDFqwR1HH/R3Uz"
    "dlkJjRTrD6Ri4ufYsJM/j9mrH2Gmewg/Rzt3weoQF+qRS8RJo6R7iE8ynx7dfqBi0ECrE/7ugVTZpTbZWaD2cKKcie9Nw0R9M+ub"
    "mSk2RayBHV4uLyMPeK7y0itDROgg9qN4GJsgAFDnLYmvzAXs9OI5EKpcYuuKZzFq64RXHr++jvML8Wu6Uf4EhIZ2NBYqsURAPk/S"
    "tM+KQ9JVnVCCqe3aSviLhFrtj2TxV3QjKZj9HQvSXv4uia+O6QZFFqLUJ3SUXk9/FxfSEKTeehOcvKENzig1QiqHa21Q6oYmKL3Y"
    "wko8ifkG5zwBcNnidzjxBBhm1+QMHPedAXblT/cJEkAbA/PeyXM6XuPC3n6ciDfEryM/+XNMnAAeDYFYSO96RjyBwJIhhPBwys8r"
    "8SrmgPCyuApin7uuRxZHPffN8xR1vEHoJwPU48+nGNWVc5flpPUB6ECReQo+/Rh5Ise9dhl3khwxwjIOeI6LQVGqlFzFEJTuOkLE"
    "hUKs7uEW8WNSKJLF7hqqzDAW0BqeLJy4hCS+MyljyFQ2TslykGvoMi8UUoMsYM9VoQgMEi/ELp3v0N2puHAud3cvUffpjJ/qY3EX"
    "R09zk4D+tYgjfrpVT8cYimg2o3DEccT6szfqKc88EaqlJ/Sx/SBwsDX5BgeZW/2W14oC5xwNZA1HSrx3nQWFvp1EvCXmdOj3J7Z6"
    "XvRj8joYWblPHVldWw/gEZ6KT2W1K/k7h3WAfklRiRWx2pSkwGlqmAUIA5IzkKMpPH0NfgZAAksrYmQ+Y1YHfYvOsoLhrO/Z4iU/"
    "0yBfIdCXy19iMmu7QJt4O79Oh8Qi7HF9QPPXgvToXsbsvIl+0Zq+CF1ZOAiM0jP5u6DSPIvHLEpQs3BMu5+cO7VRm7CqyeM/xVXl"
    "EoOXEnprkzK0XkpAfh+T2MiiXyFTcwgFBWsOS03HSzkdAKgbBhRKTM6In0cCZd3A16EgYbWGi3zWIStp81wPdc4JIqt1XMur1EpV"
    "okDXKSI16Z4RnwalTrjQylQ2ipV2mvZIxgoEeMOkIrXKTfYFWvgQ/GxBz7RE7bE6mb+Icy4UEAyP0LlqkHm2mweFq6+XUjaU7cG2"
    "EGbW/mla2S+EcabjIt17vAzTjCLB4QZgBaPXeBnPv44MuGjbskDew9t/tQdpfpHZWpiEPci7MvaYifdI0V4afgn0AKRditHxF/nZ"
    "wGym2RPFUHyXAPFnvNqcFeA6w/PX09i83fglLgfsJYT2X/hOpfI0Fp503YD+92UGxu5hU4NouzDByJGHV0G8wCB0keG+MRYZp0v7"
    "f759n6ycHxiI5IBZO2tOtC13XHGhR1ewPatcNAzH59eANQjXALhRC21ihYdEa+pkdDzjO3+OGlCpLI7Q0B0NngbGINk86lDmiLRS"
    "x+UME73euHFTV5A6yhMydHUsA8ayAT8sDoqeZGHQa3JoKNHEFVsueUK2YEt6Hq+eofmFi8JCnSL3bBclhe9jvrpIOftZXmGSp+QV"
    "ZliB3L8sWFTuA+SmqFcKkHgOHC2pyi7gEXJiyFEqh3yAfBYPZ7LEMywBX+5MdAnLl7bP3g1G5MM+/KMatDkbPo/7z2I+Uk+dxXDB"
    "vanG+6qNvvRcMHe4xO7u/um5NewTm4zBPpcYuxESxHLH3oeTWppZCiwqBjZAMovltau+O1ZeQhWa+QaaTVEE9U710J8bFOS9nEt5"
    "iuBB5v6c7ID0ZjnEqz4Laxgg90eel+Ue+QEl4RX4S4xa4TI/LuoPwEFgAVzIsNZnRt1SKgI1Ua3bOpaUK+B/e65tP64HTeNa32jN"
    "QpXI+DOg6TMl2FASDnvvPPZvUf4PKP9DEF5cmvehcTnSCNIiDKGGlydDILUY6G3cH9GPvfd7HEaWC6hLEk3SbVQr0Tjzy2vnfjQs"
    "HXSVR7IMOWF6JkY942tX8yQUoynXj2ZKegkpv6mzkZtexp9dM+4ycvQcUw9O83emMuEK9vHRHxS8gG6r1SEBJyCCgy+cSt1+KQ8Z"
    "pwwOd+cFFqT/qxRqqwjPD3YakTJuJI1GKaIle0kxaol45pOsAmOwmA0k0MB2tu2gnYCVDLOhlZQGI2gwdIeru7D7CW+dkENkjcvU"
    "geirsZN1p2EdaH6Cfac+0JBQy6S7MvSyIUG1zzAUwehHAPE2z+U/85mDWftH7OzDav64HNin6WNZH576+3kvO2VMlBoGISlKkr6i"
    "jF+E9niku35HIeMzw7pjC1VTFIUduHbZuqFGUWBZI9HtQ76MHzhAp2XDYZaSTyQUxmgjda1VgZGNA1Uo4FAZZphylIojRsnPc8lG"
    "Y1v7aKHg5LGyjcI2QmyjT2LxUGxfsEP7IZqqq7jEMUa24KKxobYivx/d4ylhSDL6J6xbioxTceDLUfk4wePhO3IxAuD7R8x0NFIN"
    "ZewhuLR0pa7H4A8KyIkNSpdhEbEiuIq8YaJwoI+zSxNP6p8KMxgjbOYzgtQBnujxdng1j5PMi7IdY9azVM06aRsBbxtp1ikC1kll"
    "5/ol0XBIKlyFIJLVKvQWpOoLmeyonQLJsqalQUrXMa4ejYukqFTacJSbOCHfWwzubT4m28OvdEFWKSx5j1Jn5H4Izj+FeDf0c/wF"
    "/l6l7lgkKR3+dZiA1OQwklTGz9IO/CN5+XCsIlihBsw0nGWkgy6DlSleCms7ySBxUhxtSa1IB6rI9YpCJ0ph+6okJE7c0Fa4QbvG"
    "S3MmMle99y5eyfAK757/+u7J2+dPSE0HEz6HfnapQphe0t6EfiEvyHALrdw4FEic3iPr7+3fzMLok5sDLU1NkalzQoz2XYLSdhNh"
    "qBoQgGF03y726sSKU6FiNHaE4gZsiS/lguhBIFIqgWh5dRwwqpSXWFZuAC2+cAc6w/KSo8HGzNvM1LSXkNbHrpbAKggaIm0Xth9t"
    "Hk9aDqUqw/OYezGtkTEWqJwv5SpXu29Em3D3zdvX3799fnLikmlZbklYdbXGuEcBMd+8e/H6FUaivSjs/9L1J3LCAAX27wiopidB"
    "ObaeXAaTT+fxDWzNwNACmelrwAxQGBzi/Z12IEnHJG7NCWEpDjeCHY/oXCYqWmDLnUUGppGDUZ+jtDspCpBj6nhGDk1xX+ulscCa"
    "I42gCiCQKQzSwNdzhnVIRHZuqCKO12c0OZG6GYs3UeUQVSNybJgZy2zDOUX6JtfFF4Xim45NsgYuNT81WK4gNK2ypmnZ9YgM0BCM"
    "/JSPyvCLkZow/I6kVrDyYjuWc5NoujqKBBS9pOB7yZA+CDYphMRtyr7mUjbVXnAWOjHmfHkQZlI6h73FQjOn5RvgJcPrYHnszWFm"
    "A3tnX1xB5kfgpIbAetxTJv+4y1RLYIU0X7dQz+OKNCXmKYYH2b6SWwAcAmyOISmCAm8h7baiUX2syIWAb8XXQuxX9LCtpBnBqIGu"
    "YQDJh6qpJnx7oA8DDWS2x/S9FymgzlnqwN5zFaY4maQCZtnimn0rXqQwLOsszZ0eYhU0dcvwXuwzHpVya9rCBiMNzLdxlWSpzT9O"
    "XtEIZIw5h06EygmoXlMI+5w40n+rssDNFXPQOP/F1VXgh3hTDNund0EH1sH9WXzYj/jKm1SgzrDoXNrc806VaNtVz0FV0+LmFuog"
    "TNt57XyjA4pB0a8ozjPid5scztLH3kTED7ZZtqUNYCQ2ByKHgHONcdQ5Oul5ynaPk0svOY59WMdWDSMM1uvSu7FOrnNyrZTcsI96"
    "nbW0w3qjKW5S0+Obduw9cUJ1WUZHfHnOGv7EQsOJvBdm5m64o4IZ9EkZAY+ry6WxumHpWRivGKvsASXLIx7XbVGHtmTex3IekLoT"
    "Fb1iYttDS+5bFPFZ7ivFTQMIm+kimF6I9ge+euXrZnhfLnVoDIrgl1ekPVlFMQCiccyIjaohaGSqPDO+jD2fwoPvj55U/zmWggUs"
    "t40cBwyYxntMatzYA8KB9tVkEeSx1c/wle+XE4br1ANsqaqPwAVCKbIMmlTkQDEYvBODMJOKmYwEuv0N27tUnEHvCimdHFB30dab"
    "djoPZjMCpKrsJ97FBYWMUq3hWZN0G2QCyiImcZKwjwFuxot83IXJ4iXn41589/bJz89VIRSnqOcZbClrpV+9ef9O9wrbabmAZgsV"
    "AOr6OzYyiPpQV2ZVXvz8vSr7y4tnz1+rl+Mnr355cqLeTl6/f3v8PO9MMbISkGSXt13vM3wNY+sitWTMYp+OSDajfPAGWy6bZj2e"
    "MGXfa9B+pG8Hjzn8KCxGM+xsZK8XYKNqPDxMsmQGh4b0MpziEcKb4d+rIPPgEPEODhFI5FhTAZ8Mcgo0Cm+rpTZFsCdfpNKzhYoK"
    "sylnseCUo7ksEtSFeMfmVtg5FtlGdclk9lNwK2ggMo2eMRFGJZPgCRNwgDIFHzFpFnA9F9icDBg9xuhgj1/RnYC4Cn1/FjxYqC4S"
    "RIwHyzREcONNtP7H55ThC2fMYESXgjAcd0wW+5pAReQ2JNUXZ7Q7aut6rQp6htrwP8d+yhwBGq2wmGzPzY0m4fynYkRbVkRSNdML"
    "DPulyNb8UiTOOzhtwfajmKkEvdmpaxOFuYFqcYUjfgYYEKSTvgt/PFhtIp3DsbSPNlKLed/1kiT+XF3MXYa+fMdnV8JRJtGLK/z4"
    "c6SS8NkVfEnRd9EKjNp2V+J1WorIJuECYP1muEQSxpYLa8AlkUqRs8B4kexDkILj6At2XB7L5TMOPQYrxc7hwiD5lKK6QB4g7CZd"
    "iXexLZ6kOTX+Pc3tO57gmK8861PKq+5n+DoVJU9SHyy+p528cKa4I4kam6RqdxCUptW6E+dNKv1Xbyfm56H3krPcO8MlXY/mSqrh"
    "ntJFQ2/V+gWYH71PoMgHdZ/e8SGqTjIZU83JlTFhPCei2BziVYr7ntZWBIoHh2RgleHAI5WmqI01KdF1dTKLvU8YmaMk4EWTiOp1"
    "1ZvPSe8VWLKVQEsqDeZXqboVNHs7+eV72aEECfMyucEZq/PJMrjpyPZwLzEbKpRTbUnNoZyW0xSoySZjXyUtX9Pd6rNm6Hc6zDOQ"
    "/TAKlPRHvNAZQBxff45UBp+iUvFS5+dqnOibIS8p3m4oMpeZL9LncHAMEgrS9yXN/S3x9jT8jnmIu0CXQqvdSRxNw4uFfv+chJl6"
    "vpbSZrvPJ0/xNF+6SI5IRLXFQe3xMPcyZe47o5DtX/g8likdlBccdZgrAfxf4CZqv72/jlqaK/GL8TVS6xgPNZYlo/5QGExaN6TO"
    "DkufXFWheSTrryMekR2GiAvFskugVRvLSc7chyU2TJTIwO6Xj1Mqg09R6MB+kALVdsica3bLYnTpOAsv439IHWK4t2QM163nQC0T"
    "oHnvUx3Fc0tF7vyLejhN1NP/csUHLqkDQANaHzluDdH70HF7hoTr+zS/VlenYfriLQTiD8BXP/X8LUn7WU+o0FLuHqZwQKm2DlRZ"
    "T5ad3lv2oKvKPpFlv7u3bLs9uH94tLZ+Quqa+7zcYKxRCjrTaUmvOO6Tp8fPnn/3/Q8vfvzp5c+vXr/5x9uTd+9/+fDrb//0ziew"
    "Ui8uw98/za6ieP5HkmaL6883t19qcJBqtTvdg171zIUlMM6JdbCyLYNW/aFBLTfmv7aArEpo0xxb7osIcAUm4RwO9p3WIpltcVFX"
    "uVSje8LpLIbCnceqof0DdLSEEHkfRtkB84V47CAPDTXhST+8DwXaiZ2fYMfDDyB3f2VsuHd8OD3ACpHLncRJDg87y1iEFaeDjnMP"
    "UOJfdQ7QdVKlMnaSo6Nwt9FuU+DhEC+Fk12rfngY2tWvAgJOGCFqRG6dh1lq7Pk06T9qojdNguBLANtzEl4Fi7DvygdgXJTzdZ1W"
    "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"
    "8t1JukmNLsB6t4vaTGhg2Uah1YySla6+pW32TdzstQ2+k3jMU2tV9Xf4TbswdctSRorXHZ3+af0WVBUXzvPZ5IyrrzUbl0JX09U2"
    "OpTYGlynd2jEYbGlv1X5YGXvttK7NReiY35FKk7L3NPe0zJzuiyER73fxkyofXuMlDKIID+TamMuLnjGb/wZPku5OOSg3jzxMxep"
    "w2cpXEfkS9jFIo4l9xjQ7pTg+Tdy70ksJi9DNNNN8w95LYt7ipxmk8+a08I0BSu1E5mXvalV8XEtmKaisb6M4TR17XJbyJ+wC00K"
    "EiZhoaTSjawLGpWSmLwYdXg8Pk5meuzYQEc/TTkMwcVVb9otWpS5O32qYKDaLbrMnuYtM7lOn+auU7rEn5qWuJxK/Mq4BivBKKEZ"
    "aKSylAgm1k/JDoaD06C+l1iOODFk4QPTTg8Mo4EGb1GsIrpBJer86c9OR5+JtaL4qIGe2bpybaTURVe0IM2sjvzsGU8lZbkX2c+e"
    "GEzdW1UnGWPa+RbH1nLWQ45Ds2dshQqDLm/uu5nNy5x6EuOZTb1sJ700GceojEjR2hPHfdVOYpns5us10ws8T6Jdl4slLSKlqnEz"
    "Gib8TpdLgjGrzEo5jEkd1eWh2RgSWQM+AdMcq7aRPQRL2p4XLFVjEtMiI1WjNOuYQJ09wylDQMWXtaZUqbtOY2xbEg8w240S+2zO"
    "sUm4n1LQZRs5QfIx6+cpJZ/J8eak51qvEy1yfRAYIZSD0DGf3VI7kKOOrc5WJyeEAvGDjuPGs7ex3+LjOP9Qn3vgyLp7M55HCteQ"
    "5o4qNcKGragpt3wDnho7OE9P62FqaYhTZ9bEnOO7qq8uTzyn6oFiLbWJjWtLdFUOkfyqU0v9PMh9GVNftzXrwXh/SM6+m/9693Hn"
    "8W8vp7+8um8/+/BT+OTobfPZb0/jZ/ceTJ6GTvj83smHJ0ffvf31yP/t6dHj1tPGDx+e3X28fDy7czZqvHR+af4QPg+/O/Wmk/jX"
    "n3+aPw6hJw8nEy+EeqfP3o1eOc5oOrHJIZZ52fYe/oj53/768y/hk7vfzX/5Gcr/dr/5/OiHxtOjH98/+3B7+Xj6U8sDuJ4enZw9"
    "++2+8/TofvPpI7s+/dF/N361+uHOvWl4dOf+79813N86P/30Ytnbe3O3+/jZ4c97v0QPnKMf9pq/jn/vv3/27tHP8377yF2s2rft"
    "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"
    "9eRm15MmrLYuTVrniSSNuttDKHlMBqfd1DVeP05rjcP4nCgE8uE22CUsntfiequ21GwC7Fsq3d46ANQtbiu0KvsmV421p0roVBO2"
    "tXqYy+43o41SyAVHhcp2fxb57UtJSa3zvfAu31xfRo2R1usMKzAIeXId7qu5jXqKbMCCWU0lu8vKiE0V9+NWlu1vaqfVUJx3+qvL"
    "cL/OLfOrrNpURodTMX9mm43+dtirry/8ZNsS64tKt6CFF/yoHqqGWrEcLxXbueue25Ty01JxutjtB9NAbKwM9rFtez7Z5AS2XEom"
    "R+uXwq7Wja+m8fC8ItfV8aixr43WwiA4rq/rxbgsH4LaJVfchMpDdprPdkpDJRtRRrHWmVvz0x4rhZKrvSYMy8FdsVWMsi9VIJDn"
    "UbBgTg/H7aFRmV5DF754vYwvXOrlkDpPYqeFNKo2cvVQrJhSX3qJQa5SkYK9wW4aHBxyhXFifVGuajO0ENa9aGguRduLfmC0VKax"
    "2DEk5uNVBewcWznu+RAcN+tcp7Esnff9aruxLMQb1/5hfHjunfNyXkkmgHatPk8qQMdTpe2y8rja86ekwC7jgcalUJyMO6X1/Jrd"
    "Xdn+XivxTXaYfCxP5DI3B/pyKXeWay2W61WypbbSvZzkcLcgRYWi1i0etuOUcCw0swdxP+n2rhVWUkeTZ6W3a+6D1eM2qyQPcWE3"
    "ab8o+fXo8lIo7FbLXVSKHrhGqC5yo2YjGBTqw8ljvyNpwV7zMOAjj6dYUY0CoZpqVbfr3Kh+LjfjXGA6TF7U+qJ83dVHnXqyuJJS"
    "beFSXtaKiazSfdYSqU1Wyk3jQjF5nkvcNTC88oVdUM2dEyV1peyVdZzvlJuR5mHdnxeqjXKLDYn8unsVxE58oh34ly4bHT7veWGn"
    "rFe9Sk5Jtppy91jJ56tcfnS81MF2dp0qNZX57loVmmH5ZbWVao3HhtTZFQ5qcdlOXKP50rqTPDx3hpfpKcwdytvYeVENyeFOtZcN"
    "lvOj9YarVcrBxDi4qm4K1+vxKsSmnWKsM61vyofG4LGg7l6Udao/5av5PZetPDcfpX2lwgMh32i91FKh4nES3fHFbHy6TJam4/yg"
    "28tegpNJQmoel9lWpdqvNY+T/hiah/Niey50GvV1Xl6rNbHS6KqHaiU/rj2PucL0Eu5Pe4+TyWLwcg13WtdAJF6IKdloqsFPn/u5"
    "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"
    "wfv9SsMgS9/0ztJn7rsrAXfAXZdRnT9s/jWrq/Mm/XnumtbJrz9Mp/j6Z/7tsoXXn9e/H9fdnL/LO/47No3baH0fgdWxUZx/l++x"
    "g3GfIb6WdXKe4df/PQIJRgbv/vXlu5uNfvi3JiiDcZI/x0meCfj9/JnSMosD++GO7D12ehKsse+bibzDkKVVZHH87cpY38w4s6Lv"
    "OHAZPyK4fA76/d3uyjeM9eeFrS6tly+wnpXm9zrPnXE2pfPj9RYmdeW8ZhngHhue+zqV8f5cyuTLe9DfMuBT28/7I649yqrIUu/n"
    "q7k9js7S7B0dfm661eF/EoiTXEdVRT0alsr5eZnx+UO0bpy13504DvIyKH+0flA5F1KezUdbGPmPZNyVNrAr/zvw49eAq0q6wnSK"
    "Iiu+2SNtgvjnLYC8cL5dQDwNu/waFWt/YYgfn5v9Wyo/Eqf4aY2z/pYb49SCdOS6P1Dgn1/uLeE6/fP3mp/2YPwzz8rgLNTfDXPk"
    "6pHq91eXG57z0xun/TyPEv7yIzds+8xtL57eCEaJvPiFjdYrDrz08tXj0Yh9L0fur348aXSvCOwf5yZjZJTi+xPeaZBeOOdMhyeO"
    "GLXMnencA367cbeIrpCKrP15HTWSKym/n02rU/x4BRoadyJ2uuvGvWGHJ6jnLo/zO5O9+Hl+8B18AB8emdUOmsA+W7q7XsLF5o0K"
    "9PLvCPZmk27MzdizHfn0PozL/j+BePpO9XPz9cEj44xugl0+frb58ve3t4t++eRXr7FhJODIiMm47pHLRuGtk7T8Xji5MzpmRl1l"
    "39yg+vowUikxuj+s2EjyPyD0nw/fHu6B+/rwx+vHyFcCGLXfl3EECIz8/PBfDwRBfH24gho5/POgoK8Icg/U5cc4AHSLL1/usIYb"
    "OLH9msnAL79hqMuov36jrz/QkXe13MVMXrhv9Dy6R+zn+T8L65no/340Mf/7/FXsb6O5c/715XGHzz/eIntu+1ZmbvWCVYLyVY9R"
    "R9wQoi7O3+b+8u9nXP99dUz/dR/jLxP5Ps7HLpfH72O+cTZukVeOEb+D+tz0Ed5z+++RXqDcYiyj/h2EY8tH+Mbm36M7w7jFZmWm"
    "Eb9H3GvjRzivPX6P9hHSLeYmyEbf4h3M18aPMF97/B7zI6RbzMmo/Edj8A7qx9aPcD92+T3yJ1i32OMgcd5BfW76CO+5/fdIL1Bu"
    "MWajo+a9h/Pa+BHWa4/f432E9IKX61F2y/I9fr62fsjT1y7fTO9jrq5Ge/ECc2sU6Ttoz02jc/ER2scufx+tfSZB8Q7ia+NHeK89"
    "/j7aIHWzd5Cemz5CeW7/JMI/H3+aRmr/fDY7L/ueG5+AXczB+82P+vb9Ds86+UXa4w2E65r+X/fyH8j5cev5PD1GoB+3JuhXb+LH"
    "jY/z/f8FAAD+8aTb0jFCiF/BMeEfd+LU66TeSdOk9kvaPdwY0q8vGq5WORjDwvuy+pI8z9v5eulvd/HOLJ6RfWZBv1A8R54voN2P"
    "h38b9357D/c7aMa4/YriW+mMG2SPu/+3pk88ebHXQY+P0dnn0Y1hT/XH99FDOztP9pfv/tlX+mAOt+g+NUcE+vxknh+dJfHWewce"
    "gFdLHVkb+C3kqwa6Js18wx49wBHQ+N9zeuLuJo2/xo3P7kRNtw7tnYAO+V1AcclrvfWEz9huBOh+xPJLNM5Ifi3lIuMP1wWN8c/D"
    "hTDfkqD7I0gfysIzvz68BPHlAQH++fXhkunIjWK05U9Rjh/knwjwwN+u8eyyP0Zk0BhN/Ph7uZhzgvVORP5ODHCXUk8e+QdkehtM"
    "Pm0n8IA9zfkmu/O0Z4/x9XP8eqba7da9SSafSf7j/+6Gwu9v6HVqlyTc/bmNfP/B9F7M7JxFvhG2J/n6eWe3Xp0zvExn4bepvmcx"
    "vQkEH0de5/Kyw7ebDl/HnflyB9QvTfb1tu3p4U+rLsqRDqPO+2bEY0Do2G8yj0+p1DObnvOq1xzkdQZffn64mjPBr0HoNdYfzVE1"
    "2oa/lXN8B2DlO4b9V1X8Vfk/h28XG/QdvCcsvzJVZRVYUf+jyvLbBPwINC8yrxi9UNMovjVGXDs/Xwo18mpVVeZ5sXMl76ufI585"
    "VjS6H0H5xw3lnwn+5aMs+HtLPZ8gjUv9HhtldebkeFy4/fPXaceIOHnSxL8BcR43mrOREmPsetFv35PAtmPnbYrd/1rZX25y6+82"
    "O6O3eNm8K7zx5zOwyn+CcJcdznt4MWCXzNvX18Ocq+n6zbCfYT1urdv/SuBdcm4vpnHZACPOvEeinbNjb7Lxj8rv5VaPaIOR6OO/"
    "385//HzidAD45+uO92T/jgm5pz3/V+KM83v4Iy8c1ynKb4Vj15Zjf0uyC+def375+XeOxR4PBkzHN8YQubgkep6PvX5cBO0qFy8P"
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
