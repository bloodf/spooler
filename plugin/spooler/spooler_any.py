# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.32.1"
# ///

# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

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
import pkgutil
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
PLUGIN_VERSION = "0.32.1"
# Stamped per operating system by scripts/build.py.
BUILD_TARGET = "any"

DEFAULT_SPOOLMAN_URL = "http://raspberrypi:7912"
LOW_DEFAULT = 100  # grams

FEEDBACK_URL = "https://github.com/bloodf/spooler/issues"
SPOOLMAN_HELP = "https://github.com/Donkie/Spoolman"  # Settings > Requirements: how to install it
RELEASE_API = "https://api.github.com/repos/bloodf/spooler/releases/latest"

# webbrowser can only open a URL; it can't use the browser's default search engine.
SEARCH_URL = "https://www.google.com/search?q={query}"

SETTINGS_FILENAME = "spooler_settings.json"
LOG_FILENAME = "spooler.log"
LOG_MAX = 256 * 1024

TIMEOUT = 5  # seconds
MAX_QUERY = 200
REFRESH_SECS = 60
REFRESH_DEFAULT = 30          # spoolman_refresh_s: the page re-reads the spools this often while it shows
REFRESH_RANGE = (10, 300)     # ... or 0 (off); the Spoolman WebSocket still refreshes it at once when it connects
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
        "spool_view": "table",
        "progress": {},
        "stats": {},
        "auto_send": True,
        "save_calibration": "ask",
        "auto_keep_slots": False,
        "spoolman_refresh_s": REFRESH_DEFAULT,
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


def parse_view(value: object) -> str:
    return "cards" if value == "cards" else "table"


def spool_view() -> str:
    """Settings > Spool list: the Spools list as a table or as cards, until a viewer picks one on the list itself."""
    return parse_view(get_settings().get("spool_view"))


def save_spool_view(value: object) -> None:
    if value is not None:
        update_settings({"spool_view": parse_view(value)})


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
    "spoolman_refresh_s": lambda v: parse_refresh(v),
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
        heard(spoolman_url, False, error)
        return {"ok": False, "error": error}
    except Exception as exc:
        _report("Spool list", str(exc), exc_info=True)
        heard(spoolman_url, False, str(exc))
        return {"ok": False, "error": str(exc)}
    _report("Spool list", None)
    heard(spoolman_url, True)
    pinned = getattr(_op, "origin", None)
    if pinned is not None and not origin_live(pinned):
        return {"ok": True, "spools": data}  # read from a source the settings left: don't cache it
    # Archived spools are only for the Spools tab: everything else reads the cache.
    _spool_cache.update(url=spoolman_url, time=time.monotonic(), spools=active_spools(data),
                        **rfid_known(spoolman_url, data, path != "spool"))
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
    by first used, else registered, else lowest id. An empty spool (0 g left) is not live: there is
    nothing on it to use first, so the next opened spool gets it, or none does."""
    groups: dict = {}
    for s in spools:
        fid = (s.get("filament") or {}).get("id")
        left = s.get("remaining_weight")
        if fid is not None and not s.get("archived") and not (isinstance(left, (int, float)) and left <= 0):
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


# What the spool source answered, per source key: {"fails": failed answers in a row, "error": the
# last failure, "good": what the last good answer said (Spoolman's version, the Bambu account) or
# None before any}. Written by the reads and connection tests that run anyway, so the Requirements
# row and auto-send never ask on their own.
_heard: dict = {}
FAILS_OFF = 2  # one failed background read can be a blip; two in a row turn the source off


def heard(key: str, ok: object, details: object = None, sure: bool = False) -> None:
    """Note an answer. details None keeps what the last good answer said. sure: a connection test
    the user sees (Settings, Check again) counts at once, not after FAILS_OFF reads."""
    key = clean_url(key)
    old = _heard.get(key) or {"fails": 0, "error": "", "good": None}
    if ok:
        good = (old["good"] or "") if details is None else str(details)
        _heard[key] = {"fails": 0, "error": "", "good": good}
    else:
        fails = max(old["fails"] + 1, FAILS_OFF if sure else 0)
        _heard[key] = {"fails": fails, "error": str(details or ""), "good": old["good"]}


def requirements() -> list[dict]:
    """The active spool source as a requirement: {id, status, details}. status: ok, missing (never
    reached: the install help applies), unreachable (reached earlier this session) or unknown (not
    heard from yet). No network: what the reads and connection tests already heard."""
    src, key = source(), clean_url(spool_key())
    if not key:
        return [{"id": src, "status": "missing", "details": tr("No Spoolman URL configured yet")}]
    if src == "bambu":
        auth = read_auth()
        if not auth["ok"]:
            return [{"id": src, "status": "missing", "details": auth.get("error") or "", "signin": True}]
    entry = _heard.get(key)
    if entry is None or (entry["fails"] < FAILS_OFF and entry["good"] is None):
        return [{"id": src, "status": "unknown", "details": ""}]
    if entry["fails"] < FAILS_OFF:
        return [{"id": src, "status": "ok", "details": entry["good"]}]
    status = "missing" if entry["good"] is None else "unreachable"
    return [{"id": src, "status": status, "details": entry["error"]}]


def source_failing() -> bool:
    """The saved source failed FAILS_OFF answers in a row. No network: only what was heard."""
    return (_heard.get(clean_url(spool_key())) or {"fails": 0})["fails"] >= FAILS_OFF


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
        heard(BAMBU_KEY, False, error)
        return {"ok": False, "error": error}
    _report("Spool list", None)
    heard(BAMBU_KEY, True, result["auth"]["account"])
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
# local preset bundle and hot-reloaded. Each one is a standalone copy of the closest preset
# OrcaSlicer already has for that printer (so the printer's own tuning is kept), refreshed on every
# rewrite and on Sync Presets, with a filament_id of its own (see flat_preset), is limited to that printer, and
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
_parent_cache: dict = {"key": None, "parents": [], "configs": {}}


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
        own = [(DRIED_FIELD, {"name": "Dried", "field_type": "datetime", "order": 100})]
        if presets_settings()["per_spool"]:  # only once someone uses it; Edit Spool adds it too
            own.append((USE_WITH_FIELD, USE_WITH_DEF))
        for field, body in own:
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
USE_WITH_DEF = {"name": "Use with", "field_type": "text", "order": 101}
USE_WITH_NO_FIELD = "Spoolman refused to add the Use with field ({error}); nothing was written."
# Your own OrcaSlicer filament preset for a spool, by name, in this text field of the spool or, for every
# spool of a filament, of the filament (the spool's wins). A linked spool gets no preset of Spooler's:
# wherever Spooler would pick its own preset it picks yours. U1 Control and Kobra Control read it too.
PRESET_LINK_FIELD = "orca_filament_preset"
PRESET_LINK_DEF = {"name": "OrcaSlicer preset", "field_type": "text", "order": 102}
PRESET_LINK_MAX = 256  # characters of a preset name
PRESET_LINK_LIST = 500  # user presets offered in the editor
PRESET_LINK_NO_FIELD = "Spoolman refused to add the OrcaSlicer preset field ({error}); nothing was written."


def _link_text(holder: object) -> str:
    """The preset named in a spool's or filament's orca_filament_preset field (JSON text in Spoolman,
    or typed by hand), or ''."""
    raw = (holder.get("extra") or {}).get(PRESET_LINK_FIELD) if isinstance(holder, dict) else None
    try:
        text = json.loads(raw) if isinstance(raw, str) else raw
    except ValueError:
        text = raw
    return text.strip()[:PRESET_LINK_MAX] if isinstance(text, str) else ""


def linked_preset(spool: object) -> str:
    """Your own OrcaSlicer preset for this spool: its own field, else its filament's; '' for none."""
    return _link_text(spool) or _link_text(spool.get("filament") if isinstance(spool, dict) else None)


def link_fits(name: str, target: str, snap: dict) -> bool:
    """Whether your linked preset name is one of your own presets OrcaSlicer would take on printer target:
    for the selected printer, OrcaSlicer's own compatibility check; for another, the preset's compatible
    printers (none listed and no condition: every printer). Elsewhere Spooler's own preset is used."""
    info = (snap.get("user_compat") or {}).get(name)
    if not name or name.startswith("_local/") or info is None:
        return False
    if target == snap.get("selected"):
        return bool(info["now"])
    return target in info["printers"] if info["printers"] else not info["cond"]


def spool_link(spool: object, target: str, snap: dict) -> str:
    """The spool's linked preset when it fits printer target, else ''."""
    name = linked_preset(spool)
    return name if link_fits(name, target, snap) else ""


def _link_value(name: object) -> str | None:
    """The orca_filament_preset field as Spoolman keeps it (JSON text; an empty text clears it, which
    Spoolman 0.22 to 0.25 take too), or None when the page sent something else."""
    if name is None or name == "":
        return json.dumps("")
    if not isinstance(name, str) or not name.strip() or len(name.strip()) > PRESET_LINK_MAX or \
            any(ord(c) < 32 for c in name) or name.strip().startswith("_local/"):
        return None  # a plugin's preset (Spooler's own too): Sync would stop making it, and the link dangle
    return json.dumps(name.strip())


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
    for name in dict.fromkeys((_tune_name(material), _tune_name(MATERIAL_ALIASES.get(_material_key(material), "")))):
        best = max((k for k in table if _tune_fits(name, _tune_name(k))), key=lambda k: len(_tune_name(k)), default=None)
        if best:
            return table[best]
    return {}


def _tune_name(text: object) -> str:
    return " ".join(re.sub(r"[-_]", " ", str(text or "")).upper().split())


def _tune_fits(name: str, row: str) -> bool:
    """A row covers its material and variants written after a separator or "+" (PLA: PLA+, PLA-CF,
    PLA Silk), not another material that starts the same (PC: not PCTG; PP: not PPA)."""
    return bool(row) and (name == row or (name.startswith(row) and name[len(row)] in " +"))


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
    Live Link printer. A printer is matched to its OrcaSlicer presets as the Printer tab chose them
    (slice_map), else by address; with one preset only, every printer is that one."""
    by_host = {_host_name(h): p["target"] for p in printers for h in p.get("hosts") or [] if _host_name(h)}
    only = printers[0]["target"] if len(printers) == 1 else ""
    known = {p["target"] for p in printers}
    picked: dict = {}
    for preset, pid in slice_map().items():
        if preset in known:
            picked.setdefault(pid, set()).add(preset)
    live = {p["id"]: p for p in live_snapshot()["printers"]}
    out: dict = {}
    for printer in printers_cfg():
        targets = picked.get(printer.get("id")) or {by_host.get(_host_name(printer.get("ip")), only)} - {""}
        if not targets:
            continue
        ids = [s for unit in printer.get("units") or [] for s in unit.get("slots") or []]
        now = live.get(printer.get("id")) or {}
        trays = [t for unit in now.get("units") or [] for t in unit.get("trays") or []] + [now.get("ext") or {}]
        ids += [t.get("spool") for t in trays]
        for sid in ids:
            if sid not in (None, ""):
                out.setdefault(str(sid), set()).update(targets)
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
PRESET_META = frozenset({"type", "name", "from", "instantiation", "inherits", "version", "filament_id",
                         "description"})
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
        elif isinstance(value, str) and preset.get("inherits") == "":
            continue  # a standalone copy: the parent's own setting, as OrcaSlicer itself serialized it
        elif key not in PRESET_KEYS:
            return f"{key} is not a filament setting"
        elif not isinstance(value, list) or not value or not all(isinstance(v, str) for v in value):
            return f"{key} is not a list of text"
        elif key not in PRESET_TEXT and not all(v == "nil" or _finite_text(v) for v in value):
            return f"{key} is not a number"
    return ""


# A preset that inherits a system preset can't be loaded by OrcaSlicer's "sync from AMS": it only
# loads base presets (PresetCollection::get_preset_base(), which is the preset itself for a user
# preset whose "inherits" is empty), matched by filament_id (PresetBundle::sync_ams_list). So each
# preset is written flat: the parent's whole config, then Spooler's values, "inherits" empty, and a
# filament_id of its own that printer agents report for a tray holding that spool.
FLAT_SKIP = frozenset({"inherits", "compatible_printers", "compatible_printers_condition",
                       "filament_settings_id", "filament_id", "name", "version", "from", "instantiation",
                       "type", "setting_id", "description", "url", "is_custom_defined", "renamed_from",
                       "includes"})
FILAMENT_ID_PREFIX = "SPL"  # no OrcaSlicer system preset id starts with it (theirs: OF..., GF..., ...)


def spooler_filament_id(key: tuple) -> str:
    """The filament_id of the preset for a (filament id, printer preset[, spool id]) key: stable across
    rewrites, different for every key."""
    return FILAMENT_ID_PREFIX + hashlib.sha256("|".join(map(str, key)).encode("utf-8")).hexdigest()[:10].upper()


def flat_preset(preset: dict, parent_config: dict, key: tuple) -> dict:
    """preset (profile_preset's, which inherits its parent) as a root preset: the parent's settings
    (parent_config: {key: OrcaSlicer's serialized text}) under Spooler's own. A Spooler value of one item
    is repeated for every nozzle variant the parent has, as OrcaSlicer does for a preset that inherits."""
    flat = {k: v for k, v in parent_config.items() if k not in FLAT_SKIP and isinstance(v, str)}
    for k, v in preset.items():
        parent = flat.get(k)
        if isinstance(v, list) and len(v) == 1 and k not in PRESET_TEXT and isinstance(parent, str):
            v = v * max(1, len(parent.split(",")))
        flat[k] = v
    flat.update(inherits="", filament_id=spooler_filament_id(key),
                description=f"Spooler: standalone copy of {preset['inherits']}, refreshed on Sync Presets")
    return flat


def parent_configs(filaments, parents: list[dict], targets: set, cache: dict) -> dict:
    """{parent name: {key: serialized text}} for the parent candidates usable on these printers, read
    once per name into cache (system presets don't change while OrcaSlicer runs). UI thread."""
    for candidate in parents:
        name = candidate["name"]
        if name in cache or (candidate["printers"] and not targets & set(candidate["printers"])):
            continue
        # find_preset() answers the edited copy for the selected preset: read the saved one then.
        selected = filaments.get_selected_preset()
        preset = selected if getattr(selected, "name", None) == name else filaments.find_preset(name)
        if preset is None:
            continue
        values = {}
        for key in preset.config_keys():
            value = preset.config_value(key)
            if value is not None:
                values[str(key)] = str(value)
        cache[name] = values
    return dict(cache)


def build_preset(filament: dict, name: str, key: tuple, snapshot: dict, opts: dict, spools: list[dict]) -> dict | None:
    """Spooler's preset for a filament on the printer key[1] names: a standalone copy of its parent when the
    parent's settings were read, else one that inherits it; None when the printer has no usable parent."""
    target, parents = key[1], snapshot.get("parents") or []
    tune = tuning_for(filament, opts)
    parent = (tune.get("parent") and tuned_parent(tune["parent"], target, parents)) or \
        best_parent(filament, target, parents)
    if not parent:
        return None
    preset = profile_preset(filament, name, parent, target, spool_cost_per_kg(filament["id"], spools), tune)
    config = (snapshot.get("configs") or {}).get(parent)
    if config:
        return flat_preset(preset, config, key)
    # Its settings weren't read: still a valid preset, but sync from AMS loads its parent.
    _report(f"Preset {name} parent", f"settings of {parent} not read; it inherits them")
    return preset


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
    if opts.get("per_spool"):
        loaded = loaded_targets(list(printers.values())) if loaded is None else loaded
        names = spool_profile_names(spools, list(printers.values()), loaded)
    else:
        names = profile_names(spools, list(printers.values()))
    by_spool = {s.get("id"): s for s in spools or [] if isinstance(s, dict)}
    for key, name in names.items():
        holder = by_spool.get(key[2]) if len(key) > 2 else {"filament": filaments[key[0]]}
        if spool_link(holder, key[1], snapshot):
            continue  # linked to your own preset that fits this printer (orca_filament_preset): Spooler makes none
        preset = build_preset(filaments[key[0]], name, key, snapshot, opts, spools)
        if preset is None:
            continue
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


def user_filament_compat(filaments) -> dict:
    """{your preset name: {"now": compatible with the selected printer, "printers": its compatible printers,
    "cond": its compatibility condition}}, for link_fits(). UI thread; never raises."""
    out = {}
    try:
        for index in range(filaments.size()):
            preset = filaments.preset(index)
            is_user = getattr(preset, "is_user", None)
            if callable(is_user) and is_user() and not str(preset.name).startswith("_local/"):
                out[str(preset.name)] = {
                    "now": bool(getattr(preset, "is_compatible", True)),
                    "printers": [p for p in split_list(preset.config_value("compatible_printers")) if p],
                    "cond": str(preset.config_value("compatible_printers_condition") or "").strip()}
    except Exception as exc:
        _report("Your filament presets' printers", f"could not be read: {exc}")
        return {}
    _report("Your filament presets' printers", None)
    return out


def user_filament_presets(filaments) -> list[str]:
    """Your own filament presets, the ones a spool can be linked to: not system presets, nor a plugin's
    bundle (Spooler's own included). UI thread. Never raises: a failure here only empties the editor's
    list, it doesn't stop the rest of the snapshot."""
    names = set()
    try:
        for index in range(filaments.size()):
            preset = filaments.preset(index)
            is_user = getattr(preset, "is_user", None)
            if callable(is_user) and is_user() and preset.is_visible and not str(preset.name).startswith("_local/"):
                names.add(str(preset.name))
    except Exception as exc:
        _report("Your filament presets", f"could not be listed: {exc}")  # logged once, not on every snapshot
        return []
    _report("Your filament presets", None)
    return sorted(names, key=str.casefold)[:PRESET_LINK_LIST]


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
        configs = parent_configs(filaments, _parent_cache["parents"], {p["target"] for p in printers},
                                 _parent_cache["configs"])
        snap = {"names": set(filaments.preset_names()), "parents": _parent_cache["parents"],
                "configs": configs, "printers": printers, "selected": selected,
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
                "user_filaments": user_filament_presets(filaments),
                "user_compat": user_filament_compat(filaments),
                # The preset open in the filament settings: Send to Spoolman offers it first.
                "edited": str(getattr(filaments.get_edited_preset(), "name", "") or ""),
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
#                     "filaments": {"<filament id>": {"<printer label>": "_local/spooler/<preset>"}},
#                     "spools": {"<spool id>": {"<printer label>": "_local/spooler/<preset>"}}}
#                    "spools" is there only with presets per spool: each spool's own preset, which readers
#                    use before the filament's. "ids": {"_local/spooler/<preset>": "<filament_id>"}, the
#                    filament_id of each standalone preset, which OrcaSlicer's plugin API doesn't show:
#                    printer agents report it so OrcaSlicer's sync from AMS loads that preset.
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
    # Per filament as before (filament id as text, then printer), so profiles.json doesn't change.
    for key, name in sorted(by_key.items(), key=lambda item: (str(item[0][0]), item[0][1], str(item[0][2] if len(item[0]) > 2 else "").zfill(12))):
        if key[1] in labels:
            out.setdefault(str(key[0]), {}).setdefault(labels[key[1]], PROFILE_PREFIX + name)
    return out


def spool_map(by_key: dict, printers: list[dict]) -> dict:
    """{"<spool id>": {"<printer label>": "_local/spooler/<preset>"}} for presets made per spool; {} otherwise."""
    labels = {p["target"]: p["label"] for p in printers}
    out: dict = {}
    for key, name in sorted(by_key.items(), key=lambda item: str(item[0][2] if len(item[0]) > 2 else "").zfill(12)):
        if len(key) > 2 and key[1] in labels:
            out.setdefault(str(key[2]), {}).setdefault(labels[key[1]], PROFILE_PREFIX + name)
    return out


def publish_profiles(by_key: dict, printers: list[dict], files: dict | None = None) -> None:
    """Write profiles.json when the presets changed (or it is missing). Never raises."""
    doc = {"filaments": profile_map(by_key, printers)}
    spools = spool_map(by_key, printers)
    if spools:
        doc["spools"] = spools
    ids = {PROFILE_PREFIX + name: (files or {}).get(f"{name}.json", {}).get("filament_id")
           for name in sorted(by_key.values())}
    ids = {name: fid for name, fid in ids.items() if fid}
    if ids:
        doc["ids"] = ids
    path = bridge_dir() / BRIDGE_PROFILES
    if doc == _bridge["profiles"] and path.exists():
        return
    try:
        _write_json(path, {"version": 1, "updated": int(time.time()), **doc})
        _bridge["profiles"] = doc
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
KOBRACONTROL = "kobracontrol"
# Each plugin's presence carries "links": the time (unix ms) it last linked or unlinked a spool. Seeing a peer's
# move, the open page re-reads Spoolman at once; Spooler's own moves when its Printer tab assigns. Kobra Control's
# presence also names its printer ({"host", "name"}): its slot links use that name, which the user may have changed.
_peer: dict = {"session": "", "started": 0.0, "users": 0, "stop": None, "thread": None,
               "seq": 0, "stock_at": 0.0, "served": None, "links": 0, "seen": {}, "kobra": None}
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
            "state": state, "provides": {"stock": STOCK_VERSION}, "links": _peer["links"],
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
    extras = {**peer_context(), "refresh_s": refresh_secs()}
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


def links_changed() -> None:
    """Spooler wrote a slot link: say so in its presence now, so U1 Control and Kobra Control re-read Spoolman."""
    _peer["links"] = int(time.time() * 1000)
    publish_presence()


def kobra_printer(doc: object) -> dict | None:
    """{"host", "name"} of the printer a running Kobra Control shows, from its presence; else None."""
    printer = doc.get("printer") if peer_alive(doc, KOBRACONTROL) else None
    if not isinstance(printer, dict):
        return None
    host, name = printer.get("host"), " ".join(str(printer.get("name") or "").split())[:56]
    return {"host": host.strip(), "name": name} if isinstance(host, str) and host.strip() and name else None


def watch_peer_links() -> None:
    """Re-read Spoolman when a peer says it changed a link (its presence "links" moved since the last beat)."""
    moved = False
    for plugin in (U1CONTROL, KOBRACONTROL):
        doc = _read_peer(plugin)
        if plugin == KOBRACONTROL:
            _peer["kobra"] = kobra_printer(doc)
        links = doc.get("links") if peer_alive(doc, plugin) else None
        if isinstance(links, (int, float)) and not isinstance(links, bool):
            moved = moved or (plugin in _peer["seen"] and _peer["seen"][plugin] != links)
            _peer["seen"][plugin] = links
    if moved:
        _spool_cache["time"] = 0.0
        _ws_notify()


def peer_tick() -> None:
    """One heartbeat: say Spooler runs, follow the peers' link changes, and refresh the stock when u1control shows
    it. Never raises."""
    try:
        publish_presence()
        watch_peer_links()
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
    kobra = _peer["kobra"]
    own = kobra["name"] if kobra and target and target_for_host(kobra["host"]) == target else None
    # Last: the name Kobra Control uses for this printer, which Spooler then also writes (slot_bind).
    return tuple(name for name in dict.fromkeys((printer.get("label"), printer.get("model"), own)) if name)


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
            publish_profiles(by_key, snapshot.get("printers") or [], files)
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
    _parent_cache["configs"] = {}  # read every parent's settings again: an updated one is copied anew
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
    only the spool's own: one its Use with leaves out has none there. A spool linked to your own
    preset (orca_filament_preset) has that one on each printer it fits (link_fits)."""
    linked = spool_link(spool, target, _ui_snap)
    if linked:
        return linked
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
    if not edited.name.startswith(PROFILE_PREFIX) or _saved_of(filaments, edited.name) is None:
        raise RuntimeError(tr("Open a Spooler preset in OrcaSlicer's filament settings and change it first."))
    name = edited.name[len(PROFILE_PREFIX):]
    changes = unsaved_changes(filaments, edited.name)
    if not changes:
        raise RuntimeError(tr("{name} has no unsaved changes to send.", name=name))
    return name, changes


def _saved_of(filaments, name: str):
    """The saved preset behind the one open in the filament settings, when that is name; else None.
    find_preset() can't give it: for the selected preset it answers the edited copy, so a comparison
    with it never shows a change. The selected preset is the saved one the edited copy was made from."""
    saved = filaments.get_selected_preset()
    return saved if saved is not None and saved.name == name == filaments.get_edited_preset().name else None


def unsaved_changes(filaments, name: str) -> dict:
    """{setting: (edited text, saved text)} for preset name's unsaved edits; {} when it isn't the
    preset open in the filament settings or has none. UI thread."""
    saved = _saved_of(filaments, name)
    if saved is None:
        return {}
    edited = filaments.get_edited_preset()
    return {key: (edited.config_value(key), saved.config_value(key)) for key in edited.config_keys()
            if edited.config_value(key) != saved.config_value(key)}


def _orca_text(items: list, key: str) -> str:
    """Values as config_value() writes them (orca_items reads them back)."""
    if key not in TEXT_KEYS:
        return ",".join(items)
    escape = lambda v: v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r")  # noqa: E731
    return ";".join(f'"{escape(v)}"' for v in items)


def spool_presets(spool: dict | None) -> list[dict]:
    """The OrcaSlicer presets a spool goes by, for Send to Spoolman: your own linked one first, then Spooler's
    preset of it for each printer the link doesn't fit. Each {"name", "label" (the printer), "linked", "where": (filament id,
    printer preset)}; a linked preset (when it fits the selected printer) is offered for that printer, and "own" says the
    link is the spool's own rather than its filament's. The one to pick first leads: the preset open in
    the filament settings, else the selected printer's."""
    filament = (spool or {}).get("filament") if isinstance(spool, dict) else None
    fid = filament.get("id") if isinstance(filament, dict) else None
    if fid is None:
        return []
    target = _ui_snap.get("selected") or ""
    linked = spool_link(spool, target, _ui_snap)
    first = [{"name": linked, "label": label_for_target(target), "linked": True, "where": (fid, target),
              "own": bool(_link_text(spool))}] if linked else []
    out = []
    for key, name in _profiles["names"].items():
        if key[0] == fid and (len(key) < 3 or key[2] == spool.get("id")):
            out.append({"name": PROFILE_PREFIX + name, "label": label_for_target(key[1]), "linked": False,
                        "where": (fid, key[1])})
    edited, selected = _ui_snap.get("edited"), _ui_snap.get("selected")
    # Spooler's presets for the printers the link doesn't fit follow the linked one.
    return first + sorted(out, key=lambda p: (p["name"] != edited, p["where"][1] != selected, p["name"].casefold()))


def chosen_changes(data: object) -> tuple[str, dict, tuple]:
    """(name, {setting: (value, base)}, (filament id, printer preset) for a linked preset, else None) for Send to Spoolman on the preset
    picked in a spool's detail: its unsaved edits when it is the preset open in OrcaSlicer's filament
    settings and has some; else, for your own linked preset, its saved settings that differ from the
    preset Spooler would make (a Spooler preset's saved settings come from Spoolman: {}). UI thread."""
    data = data if isinstance(data, dict) else {}
    full = data.get("preset") if isinstance(data.get("preset"), str) else ""
    spool = _spool_by_id(data.get("spool"), _spool_cache.get("spools") or [])
    pick = next((p for p in spool_presets(spool) if p["name"] == full), None) if full else None
    if pick is None:
        raise RuntimeError(tr("That preset is no longer one of this spool's. Refresh, then send it again."))
    if pick.get("own"):
        # Spoolman keeps settings on the filament, shared by every spool of it: a link of this spool
        # alone must not change the others' presets.
        raise RuntimeError(tr("{name} is linked to this spool only, and Spoolman keeps settings on the filament every "
                              "spool of it shares; nothing was sent. Save your changes in the preset itself, or link "
                              "the filament instead.", name=full))
    name = full[len(PROFILE_PREFIX):] if full.startswith(PROFILE_PREFIX) else full
    filaments = orca.host.preset_bundle().filaments
    changes = unsaved_changes(filaments, full)
    if not pick["linked"]:
        return name, changes, None  # a Spooler preset: send_changes finds its filament and printer by name
    if changes:
        return name, changes, pick["where"]
    if not pick["where"][1]:
        raise RuntimeError(tr("Select a printer in OrcaSlicer first, then send again."))
    preset = filaments.find_preset(full)
    base = build_preset(spool["filament"], name, pick["where"], _ui_snap, presets_settings(),
                        _spool_cache.get("spools") or []) if preset is not None else None
    if base is None:
        raise RuntimeError(tr("{name} can't be compared with a Spooler preset for this printer; nothing was sent.", name=name))
    for key in sorted(ORCA_SETTINGS_KEYS & set(base)):
        value, was = preset.config_value(key), base[key]
        was = was if isinstance(was, list) else orca_items(str(was), key)
        if value is not None and not _same(orca_items(value, key), was):
            changes[key] = (value, _orca_text(was, key))
    return name, changes, pick["where"]


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


def send_changes(name: str, changes: dict, snapshot: dict, where: tuple | None = None) -> str:
    """Write a Spooler preset's changed settings into its filament's orca_settings field, in the
    section for the preset's printer, and rebuild the presets. Returns what happened, for the user.
    where, (filament id, printer preset), is for a preset that isn't Spooler's (one linked to a spool).
    Runs on a worker thread. Every request goes to the Spoolman the presets were built from."""
    with pinned_origin() as origin:
        if _profiles.get("gen") not in (None, origin[1]):
            raise OriginChanged()
        return _send_changes(name, changes, snapshot, where)


def _send_changes(name: str, changes: dict, snapshot: dict, where: tuple | None = None) -> str:
    fid, target = where or next((key[:2] for key, known in _profiles["names"].items() if known == name), (None, ""))
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
        elif where is None and key in now and not _same(now[key], orca_items(saved or "", key)):
            # A Spooler preset's saved value is what Spoolman gave it: another value means Spoolman
            # changed since. Your own linked preset's saved value is yours, so it says nothing of that.
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
    if kept and where is not None:  # your own preset isn't rebuilt from Spoolman: it keeps your value
        notes.append(tr("Kept Spoolman's newer value for {fields}: it changed there while you were editing.",
                        fields=", ".join(kept)))
    elif kept:
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
    if source_failing():  # unreachable: wait for the next good read rather than report every tick
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


def start_send(post, edits: tuple | None = None, auto: bool = False, chosen: dict | None = None) -> None:
    """Send preset changes to Spoolman: edits (name, changes), else those of the preset picked on the
    page (chosen: {"spool", "preset"}), else the unsaved changes of the Spooler preset open in
    OrcaSlicer. Call it on the UI thread, where the presets are read; post() gets {"type": "sent",
    "ok": ..., "text": ...} when it is done."""
    where = None
    try:
        if _auto["busy"]:
            raise RuntimeError(tr("Already sending to Spoolman; try again in a moment."))
        if source() != "spoolman":
            raise RuntimeError(tr("Sending needs Spoolman as the source."))
        snapshot = refresh_snapshot()
        if snapshot is None:
            raise RuntimeError(tr("Could not read OrcaSlicer's presets."))
        if chosen is not None:
            name, changes, where = chosen_changes(chosen)
            if not changes:
                text = tr("{name} has no unsaved changes, and its saved settings match Spoolman: nothing to send.", name=name) \
                    if where else tr("{name} has no unsaved changes to send.", name=name)
                post({"type": "sent", "ok": True, "text": text})
                return
        else:
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
            text, ok = send_changes(name, changes, snapshot, where), True
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
    # One extruder slot when Moonraker has no Spoolman integration to hold the active spool (found["solo"]).
    solo = bool(found.get("solo")) and count < 2 and not saved.get("gates")
    tools = (list(saved.get("tools") or []) + [None] * MOON_TOOLS)[:max(count, 1)] if count >= 2 or solo else []
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
    update_settings(lambda settings: _printer_changes(settings, value))
    prune_codes()  # a printer removed takes its access code with it
    _local_sync()


def _printer_changes(settings: dict, value: object) -> dict:
    """The printers and moon_slots keys after saving value over these settings."""
    saved = dict(settings["printers"]) if isinstance(settings.get("printers"), dict) else {}
    seen: set = set()
    saved[source()] = parse_printers(value, seen)
    moon = dict(settings["moon_slots"]) if isinstance(settings.get("moon_slots"), dict) else {}
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
    return {"printers": saved, "moon_slots": moon}


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
           "slice_picks": list(_slice_picks), "printer_presets": list(_ui_snap.get("presets") or []), "rfid": rfid_offers()}
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
                             "spool_set": bool(state.get("spool_set")), "hh": bool(state.get("hh")),
                             "bind": state.get("bind") or ""})
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


def _spool_tray(slot: int, spool: dict, target: str, **extra) -> dict:
    """A tray for a slot holding a Spoolman spool. "remain" is only what the printer itself reports (None here):
    Spoolman's weight is shown as Spoolman's, never as the printer's percentage."""
    filament = spool.get("filament") or {}
    colour = profile_colour(filament)
    return {"id": str(slot), "tray_type": str(filament.get("material") or ""),
            "tray_color": colour + "FF", "tray_sub_brands": str(filament.get("name") or _spool_label(spool)),
            "remain": None, "spool_id": spool.get("id"), "filament_id": filament.get("id"),
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


def location_for(name: str, letter: str, number: int) -> str:
    """The Spoolman location that binds a slot: "<printer name> T<n>" (u1control) or "<printer name> S<n>"
    (Kobra Control), n 1-based."""
    return " ".join(f"{name} {letter}{number}".split())[:64]


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
    spool = _spool_by_id(spool_id, spools)
    linked = "printer" if spool is not None else ""  # the printer itself says which spool: nothing to link here
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


def mmu_present(mmu: object) -> bool:
    """Whether Klipper's "mmu" object is a Happy Hare MMU: it reports gates, or says it is enabled without saying
    how many. One that reports 0 gates (Happy Hare installed with no MMU attached) or nothing at all is no MMU."""
    if not isinstance(mmu, dict) or not mmu:
        return False
    if "num_gates" in mmu:
        return _int(mmu.get("num_gates"), 0) > 0
    return mmu.get("enabled") is True or any(isinstance(mmu.get(k), list) and mmu[k] for k in MMU_KEYS[1:])



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
    if mmu_present(status.get("mmu")):
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


def moon_found(base: str, tools: int, managed: bool, u1: bool = False, hh: bool = False, solo: bool = False) -> dict | None:
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
             "u1": u1 or bool(last.get("u1")), "hh": hh or bool(last.get("hh")), "solo": solo}
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
    solo = False
    # Moonraker answers {} for an object the printer doesn't have (only the U1 has this one).
    if not status.get("print_task_config"):
        lanes = moon_lanes(base)
        if not lanes:
            try:
                active = _moon_get(base, "/server/spoolman/spool_id").get("spool_id")
            except urllib.error.HTTPError:
                active, solo = None, True  # Moonraker without its Spoolman integration: the spool is set here
    spools, target = _spool_cache["spools"] or [], target_for_host(base)
    doc, heads = moon_report(status, active, spools, target, lanes)
    # The Snapmaker U1's toolheads are booked by u1control, so its prints never are here (_moon_run).
    # Happy Hare ("mmu" object) reports its gates and books them through its own Spoolman integration:
    # read-only even with no gate reported, never filled or booked here.
    # The U1 (toolheads in print_task_config) is never Happy Hare, whatever its "mmu" object answers.
    doc["hh"] = not heads and mmu_present(status.get("mmu"))
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"] or doc["hh"], heads, doc["hh"],
                       solo and not doc["hh"])
    found = (_moon_found.get(entry["id"]) or {}) if entry else {}
    doc["u1"] = heads or bool(found.get("u1"))
    doc["hh"] = doc["hh"] or bool(found.get("hh"))
    if entry is not None and not entry["managed"]:
        heads = moon_manual(doc, entry["units"], spools, target)
    elif entry is not None and "vt_tray" in doc["print"]:
        # It reported its own spools before (U1, lane_data, Happy Hare) and this answer was empty: show no
        # slots this time, never Moonraker's active spool, so the page can't offer to set one (spool_set).
        doc["print"].pop("vt_tray")
        doc["print"]["ams"] = {"ams": []}
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
        _live["printers"][pid]["bind"] = "T" if heads and doc.get("u1") else ""
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


def spool_at_kx_slot(spools: list[dict], names: tuple, number: int) -> dict | None:
    """The spool Kobra Control bound to ACE slot S<number> (1-based, box * 4 + slot + 1): its Spoolman location
    is exactly "<printer name> S<n>". Between spools with that location the one used last wins, as there."""
    keys = {_location_key(location_for(name, "S", number)) for name in names}
    found = [s for s in spools if not s.get("archived") and _location_key(s.get("location")) in keys]
    return max(found, key=lambda s: str(s.get("last_used") or "")) if found else None


def kx_tray(slot: int, item: object, spools: list[dict], target: str, number: int = 0) -> dict:
    """A Bambu-shaped tray for one Anycubic slot, matched to a Spoolman spool: the one Kobra Control bound to
    slot S<number> (number > 0), else by material and colour. The ACE's consumables_percent is a printer
    percentage only for a slot with no Spoolman spool (Kobra Control draws a linked slot from Spoolman too) and
    below 100: the ACE answers 100 for every spool it can't measure, so 100 is no reading."""
    item = item if isinstance(item, dict) else {}
    kind = str(item.get("type") or "").strip()
    colour = _kx_colour(item.get("color"))
    if not kind or item.get("status") == 0:
        return {"id": str(slot)}
    percent = item.get("consumables_percent")
    remain = percent if isinstance(percent, (int, float)) and not isinstance(percent, bool) and 0 <= percent < 100 else None
    bound = spool_at_kx_slot(spools, location_names(target), number) if number > 0 else None
    if bound is not None:
        return dict(_spool_tray(slot, bound, target, linked="kobracontrol"),
                    **({"tray_color": colour + "FF"} if colour else {}))
    found = match_spools({"preset": "", "vendor": "", "material": kind, "colour": colour}, spools) if colour else []
    if found:
        return dict(_spool_tray(slot, found[0], target), tray_color=colour + "FF")
    return {"id": str(slot), "tray_type": kind, "tray_color": colour + "FF" if colour else "",
            "tray_sub_brands": kind, "remain": remain, "spool_id": None, "profile": ""}


def kx_report(boxes: object, external: object, spools: list[dict], target: str = "") -> dict:
    """A Bambu-shaped report from multiColorBox and extfilbox replies."""
    # Slots only: no gcode_state or job keys, so live_apply never books an Anycubic print (Kobra Control
    # books it; tests/test_kobra.py NoKobraBookingTest). If Spooler ever books Anycubic prints, publish
    # "books": ["anycubic"] under "provides" in presence.json in the same change: Kobra Control then stops
    # booking in that Spoolman.
    units = []
    for number, box in enumerate(boxes if isinstance(boxes, list) else []):
        if isinstance(box, dict) and isinstance(box.get("slots"), list):
            units.append({"id": str(number), "tray": [kx_tray(i, s, spools, target, number * 4 + i + 1)
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
                    _live["printers"][pid]["bind"] = "S"
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
        update_settings({"slice_map": slice_map(value)})


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
    def add(settings: dict) -> dict:
        skipped = _rfid_skipped(settings)
        kept = [t for t in skipped.get(pid, []) if t not in tags] + sorted(tags)
        return {RFID_SKIP: {**skipped, pid: kept[-RFID_SKIP_MAX:]}}
    log.info("RFID spool %s in printer %s skipped", min(tags), pid)
    return update_settings(add)


def rfid_unskip() -> bool:
    """Offer every skipped RFID spool again (Settings)."""
    return update_settings({RFID_SKIP: {}})


def _live_trays(state: dict) -> list[tuple]:
    """(unit, slot, tray) for every slot a printer reports: AMS and toolhead slots, then the
    external holder. Holds _live_lock."""
    trays = [(unit, slot, tray) for unit, slots in sorted(state["units"].items()) for slot, tray in sorted(slots.items())]
    return trays + ([("ext", 0, state["ext"])] if state["ext"] else [])


def _all_tags(spools: list) -> set:
    return set().union(*(spool_tags(s) for s in spools if isinstance(s, dict)))


ARCHIVED_SECS = 300
_archived_tags: dict = {"url": "", "time": 0.0, "tags": set()}  # archived spools' tags, per Spoolman address


def _archived(url: str) -> set:
    """The tags of a Spoolman's archived spools, read again after ARCHIVED_SECS or a card action.
    Raises when Spoolman can't be read."""
    if _archived_tags["url"] != url or time.monotonic() - _archived_tags["time"] >= ARCHIVED_SECS:
        spools = _spoolman_open(url, "spool?allow_archived=true") or []
        tags = _all_tags([s for s in spools if isinstance(s, dict) and s.get("archived")])
        _archived_tags.update(url=url, time=time.monotonic(), tags=tags)
    return _archived_tags["tags"]


def rfid_known(url: str, data: list, with_archived: bool) -> dict:
    """For the spool cache, read with each spool list: every tag Spoolman holds, archived spools
    included (an archived spool still in the AMS is no new spool), and the tray tags checked against
    them. Archived spools are read (and kept ARCHIVED_SECS) only when the list left them out and a
    tray carries a tag no active spool has and that wasn't skipped. Called off the UI thread."""
    known = _all_tags(data if with_archived else active_spools(data))
    skipped = _rfid_skipped()
    with _live_lock:
        trays = [(pid, tray) for pid, state in _live["printers"].items() for _u, _s, tray in _live_trays(state)]
    wanted = set()
    for pid, tray in trays:
        offer = rfid_offer(tray, known)
        if offer and not _tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")]) & set(skipped.get(pid, [])):
            wanted.add(offer["tag"])
    if wanted and not with_archived:
        try:
            known |= _archived(url)
        except Exception as exc:
            _report("Archived spool tags", str(exc))
            return {"rfid_known": known, "rfid_checked": set()}  # unsure: offer nothing until the next read
        _report("Archived spool tags", None)
    return {"rfid_known": known, "rfid_checked": wanted}


def rfid_offers() -> list[dict]:
    """The new RFID spools in the printers Spooler reads, for the Printer tab. Only tags checked
    against the spool list of the Spoolman in Settings (archived spools included), read after the
    last write, so a spool just added, or archived, is never offered. A spool put in the AMS shows
    with the next list read (every REFRESH_SECS while the page is open)."""
    url = current_origin()[0]
    if source() != "spoolman" or not url or _spool_cache["url"] != url or not _spool_cache["time"]:
        return []
    known, checked = _spool_cache.get("rfid_known") or set(), _spool_cache.get("rfid_checked") or set()
    skipped, out, seen = _rfid_skipped(), [], set()
    with _live_lock:
        for pid, state in _live["printers"].items():
            for unit, slot, tray in _live_trays(state):
                offer = rfid_offer(tray, known)
                # Skipped by either id: a report may carry only tag_uid at first, then tray_uuid too.
                ids = _tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")])
                if offer and offer["tag"] in checked and offer["tag"] not in seen and not ids & set(skipped.get(pid, [])):
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
                 "comment", "remaining", "bind", "unbind")
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


def _binds(location: object, letter: str, names: tuple, number: int) -> bool:
    """Whether a Spoolman location is the peer plugin's binding of slot <letter><number> on this printer."""
    if letter == "T":
        return _bound_here(location, names, number) > 0
    return _location_key(location) in {_location_key(location_for(name, "S", number)) for name in names}


def slot_bind(sid: int, pid: object, slot: object, on: bool) -> dict:
    """Link spool sid to a live printer's slot, or unlink it, the way the plugin that owns the printer reads
    the link: the spool's Spoolman location "<printer name> T<n>" for a Snapmaker U1 toolhead (U1 Control) and
    "<printer name> S<n>" for an Anycubic ACE slot (Kobra Control). Linking clears that location from any other
    spool that holds it, so one spool is in each slot. Nothing is sent to the printer. Refused for every other
    printer: their slots are the printer's own (Bambu, Happy Hare, AFC) or set on the printer's card."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    number = slot + 1 if isinstance(slot, int) and not isinstance(slot, bool) and 0 <= slot < LANE_MAX else 0
    printer = next((p for p in _auto_printers if p["id"] == str(pid)), None)
    with _live_lock:
        letter = (_live["printers"].get(str(pid)) or {}).get("bind") or ""
    if printer is None or letter not in ("T", "S") or not number or (letter == "T" and number > MOON_TOOLS):
        return no(tr("Spooler can only link a spool to a Snapmaker U1 toolhead or an Anycubic ACE slot."))
    names = location_names(target_for_host(printer["ip"])) or (printer["name"],)
    location = location_for(names[-1], letter, number)
    spools = _spool_cache["spools"] or []
    spool = _spool_by_id(sid, spools)
    if spool is None:
        return no(tr("That spool isn't in Spoolman, or it is archived."))
    if not on:
        if not _binds(spool.get("location"), letter, names, number):
            return no(tr("Spool #{id} isn't linked to {slot}.", id=sid, slot=location))
        spoolman_call("PATCH", f"spool/{sid}", {"location": None})
        links_changed()
        return {"ok": True, "text": tr("Spool #{id} is no longer linked to {slot}.", id=sid, slot=location)}
    spoolman_call("PATCH", f"spool/{sid}", {"location": location})
    for other in spools:
        if other.get("id") != sid and not other.get("archived") and _binds(other.get("location"), letter, names, number):
            spoolman_call("PATCH", f"spool/{other['id']}", {"location": None})
    links_changed()
    return {"ok": True, "text": tr("Spool #{id} linked to {slot}.", id=sid, slot=location)}


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
        links_changed()   # a location typed here may link or unlink a slot of U1 Control or Kobra Control
        return {"ok": True, "text": tr("Spool #{id} moved to {location}.", id=sid, location=location) if location
                else tr("Spool #{id} has no location now.", id=sid)}
    if action in ("bind", "unbind"):
        return slot_bind(sid, data.get("printer"), data.get("slot"), action == "bind")
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
EDITOR_OWN = {"tag", ORCA_SETTINGS_FIELD, DRIED_FIELD, USE_WITH_FIELD, PRESET_LINK_FIELD, *CALIBRATION_FIELDS}  # Spooler's own fields: never from the editor
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
    # OrcaSlicer preset: your own filament presets, as the last snapshot read them on the UI thread.
    link = {"presets": list(_ui_snap.get("user_filaments") or []),
            "spool": _link_text(spool), "filament": _link_text((spool or {}).get("filament") if isinstance(spool, dict) else None)}
    return {"fields": _editor_fields(), "filaments": filaments, "vendors": vendors, "spool": spool,
            "use_with": {"on": presets_settings()["per_spool"], "printers": printers, "value": chosen},
            "preset_link": link}


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
    fil_data = data.get("filament") or {}
    fil_data = dict(fil_data) if isinstance(fil_data, dict) else fil_data
    # The OrcaSlicer preset linked to the spool, and to its filament: None or "" unlinks.
    links = {kind: part.pop("preset_link", _MISSING) if isinstance(part, dict) else _MISSING
             for kind, part in (("spool", spool_data), ("filament", fil_data))}
    fields = _editor_fields()
    wanted = ([("spool", USE_WITH_FIELD, USE_WITH_DEF)] if chosen is not _MISSING else []) + \
        [(kind, PRESET_LINK_FIELD, PRESET_LINK_DEF) for kind, link in links.items() if link is not _MISSING]
    missing = [w for w in wanted if w[1] not in {f.get("key") for f in fields[w[0]]}]
    for kind, key, body in missing:
        try:  # Spoolman takes only extra keys it has a field for
            spoolman_call("POST", f"field/{kind}/{key}", body)
            log.info("Added the %s field to Spoolman", key)
        except NotSent:
            raise
        except Exception as exc:
            return no(tr(USE_WITH_NO_FIELD if key == USE_WITH_FIELD else PRESET_LINK_NO_FIELD, error=_error_text(exc)))
    if missing:
        fields = _editor_fields()
    spool_changes = _clean_form(SPOOL_FORM, spool_data, fields["spool"])
    fil_changes = _clean_form(FILAMENT_FORM, fil_data, fields["filament"])
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
    for kind, link in links.items():
        if link is _MISSING:
            continue
        text = _link_value(link)
        if text is None:
            return no(tr(EDITOR_INVALID, field=PRESET_LINK_FIELD))
        part = spool_changes if kind == "spool" else fil_changes
        part["extra"] = {**(part.get("extra") or {}), PRESET_LINK_FIELD: text}
        had = was_spool if kind == "spool" else was_fil
        old = had.get("preset_link")  # the page sends the link as Spoolman stored it, under this key
        had = {**had, "extra": {**(had.get("extra") or {}), PRESET_LINK_FIELD: old if isinstance(old, str) else None}}
        was_spool, was_fil = (had, was_fil) if kind == "spool" else (was_spool, had)
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
    # Archived spools too: one still carrying the tag would make two, and the tray would match neither.
    holder = next((s for s in spoolman_call("GET", "spool?allow_archived=true") or [] if isinstance(s, dict) and tag in spool_tags(s)), None)
    if holder is not None and holder.get("archived"):
        return tr("Archived spool #{id} carries this RFID tag; unarchive it instead. Nothing was written.", id=holder.get("id", "?"))
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
            _archived_tags["time"] = 0.0  # an archive or unarchive changes them
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
    presets = [{k: v for k, v in p.items() if k != "where"}
               for p in spool_presets(_spool_by_id(sid, _spool_cache.get("spools") or []))]
    return {"id": sid, "prints": prints, "grams": round(sum(p["grams"] for p in prints), 1), "presets": presets,
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
            t = top.setdefault(r["spool"], {"spool": r["spool"], "label": r["label"], "colour": r["colour"], "g": 0})
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

# Tab icon: the brand tile (assets/orca-cloud/spooler-tile.png) at 40x40, white surround made transparent;
# the same bytes as assets/spooler-plugin-icon.png. OrcaSlicer draws it 20 px high. get_icon() must return the
# path of an image file; SVG markup or a data: URI shows no icon. OrcaSlicer drops the extension and tries .svg
# first, so the file needs a new name: the spooler_tab.svg older versions wrote would win over spooler_tab.png.
TAB_ICON_PNG = (
    "iVBORw0KGgoAAAANSUhEUgAAACgAAAAoCAYAAACM/rhtAAAMHUlEQVR42oWZe5Ac1XXGf+d2z2t3dnallQAJSRZCWEJCMi"
    "bCIS7AGCOZR4KAALaskALbKoyDQxFDnFQCFKnKu4rIcRwnBIMcHuJhK+EZ87AhYAFOANlGQggQQhJ6ol3tamd2Zrr73pM/"
    "+rE9uyunp6amp/v27XO/c853HlcUREARWLfgW5eakK/ayC3WgvSCimAQAQBVR/4QMYCgKGT3DAIoAGPjBYMy/vl4nCCqbT"
    "fsed4WKXl3XbXtr/4DBQWR27jNTD1/sND7dun7JmS1OiVSi6oy4VBiYf6/QwCV7KGxs8nGJcsyBg+DMQYtc//Qx2d/ZfDH"
    "g6GICP8258aHa2HpiiHXsAKiIDFq2RITBNPXpDPnbh5d0uyMcU+JSAcQiiqKTvG6vSOl4JE1O//hSvn3hX/6RTMSrR+NWp"
    "GI+BNXKrnXHA0NzQl0VJAmnE+GqoigzkVdfsWXPm+VHzTaN/hWFcFMjoL+mkkzLFBVRI6CqMbXNX/LM6jTVC2dyzNiIhep"
    "G3U3+NZGi1UREZkUh0wFIplVJ26RYJuIKUdb3kSZxRiC4VGk4FEoF4k1m59EJFIrGriFxiv6Vacufu9kSksFy4SNR0qCXD"
    "pGjEm+Ev+XsQV0TC0QjraZe8FSpi6cQdQOQcaWqpqgKqCRFWNiCbJp8naSCiYJWjJOs+ILGMGGlrDRJjjSJBhpErUC1Cni"
    "xUJncxghrLeZffYCLnz4D5h+6hxsM0RM8maVMRBjmsGPuSzvUWN2JHm3yFGH8Q1ROyQYbGF8Q9exNaozp1Ca0oWLLM1Dde"
    "ofDtI8NIIp+hR7StmqNbKcdvMF7N34LlvXbaQ8tRu1LjGTRFBJ2RH8vGfmBZJEpRmpKNlKmwN1umf0sWTNOcy/fBlTF83E"
    "KxU67Kw1WGf381vZfOcL7HnpHQpdRQpdJYzvUTm2xt4X38EGEWIEtQkk2un+AviZD0zKapJ5sTEGG0a4wHLqDcv5zVtWYo"
    "oeHzz1K95a9zMGt+0nGBpFPEP3cb0cs2wu8393GZc+fTPvP7aJF7+5nvZgA7XKvpffY/byxZR6K7jITeDV1JxUBLln3k0a"
    "1tuJraSBL++lCsZg2yF+pciKe77K7PMWsWntM/zyu89R3z2IGIMpeDEagFqHCyJMyeeECz/BZ9auRozw5OX/xIcvbuOky5"
    "dx0SPX8+Cnbmf4vYN4lQK4DvJST4w4Z4f9CRygeb9TMIILLV65wMonb6Q6awo//Mxfs++V9yj1dVGZ3pMYuGaGnTqEqvL+"
    "Y79gz4vbuODB67jk6Zt44LRbaewbjm256OGc4k1i+empGSNKzT7jD9sKOP/ea6nOnsrDZ/4lB17bQfdxvRjfw1mX2KriUi"
    "czxNeto9LfjW1HPH7xtxncsoeLfvQNll53Lq2BOsPvHcQv+4nipCMsaOIPppPHpQNP8T3agw1O/cZyZn12IU9c8o+M7Byg"
    "3F/FBjbz/vbQKM2PRggbLdrDo4x+NIINLeIZbGDxywXEMzy16nt0H9vLwtW/xc++9TBhvY3xvTzpjjlLApwvcpSoaATbCu"
    "me2cenbl3JG3f8mL0b36U6sw8bRLHqrcO2Qk685DROvurT9J54DFGjzc5nN/Pmv7xA86MRij1l1DoK3SVGdg3wyq0bOOc7"
    "v8fBTTsxBW8s1KnmIk/qAToWf0Vy6IlgjCEYabLomrNQ59i09lnKU7txoUWMQa1DjPD5e6/l/PuupdBTZtczWxh4ay9Lr/"
    "scV7785/QvOZ6g0UI8gwstlalV3ln/Ks2DRzj1D5cTNgIwZoJZaS6E+3nk8vHYWYdXKrBg1Rlsf/QNmvuHKB9TQyOLGCFq"
    "BHz+/muZs3wRG1b8PXv+e1uaiVCZXuO3f3R97Kmn3x6r2wjGN4T1Nu889D8sWH0Gpd5KPJ+MBW3Ju4uImLwXa+qGgG2H1O"
    "b0U5s3nQ+e+lVMI4DxPIKRFnNWnMKJK0/jqS/8Mx/+dCvdx9aoTK/SNaOXsNHiv1b/K5XpPSy65iyC4VGMZ8CBV/L58Pmt"
    "VPp7qM2bTtQKSaNZrFoQRFQVU/DKpsP2koxZEmqpzp6KiDD07gFM0Y8xN4JtRZx0xekMvr2X3c+9RXVGHza0uCjmv2KtQn"
    "33ALue3cLci5aSD7Cm4HHkg0OgSs/H+mOTkXyYExDUGIMLbdNMzPoSwnFKoVZGnRI22oiXMJIq4gnVmVM4suNQHEc7cjrJ"
    "FjKye5Dy1Cqm4CW5X8yPUTPAWUehWsrCqVPtcBTNKpyJITC+YAQ7GiAi+JVinJ2YeIXqlPrew9TmTgNPOrKejC4Upsw/ls"
    "b+YVwQgYlzDXWKV4ppJxoNOuOEpGamGVBGxnFfykXGN9T3HAaBnjn9uDDKahSv6LN9w+tMPXkms85ewOjBI3glH/ENUvRo"
    "H24wZeEMZp17Mtt/+FqcJ4pBJDadnjmx6dR3DeAV/JwGZBzbiZhMtal/qGarPLJzgNEDw8w6ZyE2iG1FraVUq7Dz6c3s/u"
    "lWzn/ga0xbcjz1Dw/TPDTC6N4huo6pccFDX2dw6162rX819lbrQAQbWI4/eyGtwQbD2z+Ks6Acr0i+TBDE16NUkSaJIjue"
    "+CXzL/sNXrllA9bahIoUr+zz7Jfv4sIHv86q125n+3++zuFt+6jNnsb8y5cxvHOAJy/7DuocYnzUKeocfqXASVeczq5nNt"
    "MeGqWSUtckpYKYNN3NVW9ZJu0Uv7vE5rtepHtGHx+/8nTag6MY36BW8Qo+YaPNoxev5aWbH6I6q58FX/o0UxbP5H//5kk2"
    "nPu3NPYcTuzXIb4QDDf52PlLqM2dxpt3voA/MYvpqItEROTuE27SKPHStPpKM1TxDc1DdZbf/RXmXriU+075M2wrwiv5sc"
    "pMbDPtoVEwglfyse0QtUqpt4LxPdQm9YUqrh2xatNfcHjbPp5Y+W3K/dV4nnH1ooIajDi1Q6az5JOObEedUqyV2fgnj+AC"
    "y4p1awgb7TjM+V7Kq5T7q5T6uvBKPuW+birTqjEt2ZiSxAjNQyOcdccqqjP7eOmP1uN3l2LqSettGctoMs70Pd+Qr6Y6k0"
    "FwsSrbQ6M89YXvMvtzi1jxgzUEjTZhvYWkSapz4GIDj21NERFMwSNqBrFwf/dFFl19Jk///p0M7ziEXykmjiD57HPs9QKq"
    "Tk1WHuakl1xFp9ZRrFXY//MdPPo7aznx0tO47Cd/TO2EaTT2DRGMtDIPTSOnWkcw0qJxYJjq8VO4+PEb+eSNK3huzd28/+"
    "gbcaEU2XH8N5bRpPW3McaTdfNu1rDeAs9MLEpyLm4KHq3BBv2nzOK873+Z/sXHs/XejWy7/1UGtuwhONJErcN4htKULvqX"
    "zGbBqjNY8KUzGHrvAD/52g/Y//K7lPt7YuGyltn4toVmKb910ZDckwho0lA2oXwfu2A8Q1CP06eTrz6TU68/j9rcaQQjTU"
    "YPDBM1AwpdZbqO66XQXeLwO/t583vP8/Z9L2ODiFKtgssJJxNxyFIWIyLOuWG5Z97NGqUIjocwLZ4kV2+ZONS1h0bxu4r0"
    "L5nFcafPozZvGn6lSDDSYujdAxx8/QMGNu/BtUOKfV0xAFbHNxmSUkY7TEtV1SDi0CO+qk7a8ZFxiWNmK4nnVaZVcZHjo0"
    "072f/q9rHiOyF5r1zA7ypiqrG3ZnSSq3PzJW8eVR3jYvVtFNXFmB7X2XjIBuUL6riDFQ+J61koVsvQIx1JL6o4p+AczmqH"
    "E2quQMogzFlT1mFQEN+o8X1vc0F8lVSfk8U+yfN32uAZ40q1Dmdt/BtZbORi6sk1mDIGS+1Fx5dBml1TVfXFqFf0thq/u7"
    "jW9zxBxSbx5dc0TNPOlTBp8BxrTCXJu07W+B23cJnQ/RKwvudLubuyVhC4e+43H+gJSqsGo7oVg3SqWrMGYGYfqhO7mR3t"
    "07RlkpqIjmuxje+kpyFWVRXt93u8kWLrgWt23LHau43bzMKrjnt8+P3hOQU1n/Q07hB5GDEY8TDiIeKJjP1Pzg1Gsk9y7k"
    "k83mjyi4gnnngYESSZLzceSZ4XKYgvRb9gohLrpl/02TXzfz5fJb8Nsf4Tt6y0R8KrwzBcHEWRn25DgEvAMR1NpnhbwXRs"
    "N6TbE+mWxTgmnaSV7BBEvYJvfb+wpdTbdfeVv7j1sXQb4v8AanD/N/G27xMAAAAASUVORK5CYII="
)
TAB_ICON_FILE = DATA_DIR / "spooler-icon.png"


def icon_path() -> str:
    try:
        png = base64.b64decode(TAB_ICON_PNG)
        if not TAB_ICON_FILE.exists() or TAB_ICON_FILE.read_bytes() != png:
            TAB_ICON_FILE.parent.mkdir(parents=True, exist_ok=True)
            TAB_ICON_FILE.write_bytes(png)
    except OSError:
        log.exception("Could not write the tab icon to %s", TAB_ICON_FILE)
        return ""
    return str(TAB_ICON_FILE)


# The UI: one compiled Vue 3 + PrimeVue page (ui/, shared Orca UI foundation), written by scripts/embed_ui.py to
# app.html next to this file (spooler/app.html in the wheel); its hash, size and licences are at the end of this file. The native tab, the separate spool window and the separate Settings window all serve
# it; the boot JSON says which surface it is and carries the saved settings.
UI_LANGUAGES = ("auto", "en", "pt-BR", "es", "de", "zh-CN", "pl")
# OrcaSlicer's language codes ("pt_BR", "es", "de", "zh_CN", "zh_TW", "pl_PL") by their language part. Traditional
# Chinese takes the Simplified texts: closer to its reader than English. The page maps them the same way.
_LANGUAGE_OF = {"en": "en", "pt": "pt-BR", "es": "es", "de": "de", "zh": "zh-CN", "pl": "pl"}
_lang: dict = {"value": None}


def ui_page() -> str:
    """The served page: from the package (pkgutil reads it from a folder or a zip alike), else the file next to this one."""
    if __package__:
        data = pkgutil.get_data(__package__, "app.html")
        if data is None:
            raise FileNotFoundError("app.html is missing from the spooler package")
        return data.decode("utf-8")
    return (PLUGIN_DIR / "app.html").read_text(encoding="utf-8")


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
    "zh_CN" and "zh_TW" → "zh-CN", "pl_PL" → "pl", any English → "en"; None for the rest and for anything
    that isn't text."""
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
    Portuguese and Spanish, 12 345,5 in Polish (Spanish and Polish group only from 10,000 up, as the page's
    Intl.NumberFormat does; Polish groups with a no-break space)."""
    language = text_language()
    if group and not (language in ("es", "pl") and abs(value) < 10000):
        text = f"{value:,.{digits}f}"
    else:
        text = f"{value:.{digits}f}"
    if language in ("pt-BR", "es", "de"):
        text = text.replace(",", "\0").replace(".", ",").replace("\0", ".")
    elif language == "pl":
        text = text.replace(",", "\u00a0").replace(".", ",")
    return text


def fmt_money(amount: float, code: str) -> str:
    """An amount with its currency sign where the language puts it: "€1.23", in German, Spanish and Polish "1,23 €"."""
    sign, text = CUR_SIGNS.get(code, code + " "), fmt_num(amount, 2)
    return f"{text}\u00a0{sign.strip()}" if text_language() in ("de", "es", "pl") else sign + text


# Python-worded texts in the page's other languages, by their English text: (pt-BR, es, de, zh-CN, pl). Terms follow
# OrcaSlicer's own translations (Spanish "carrete", "ranura", "perfil"; German "Spule", "Slot", "Profil", formal "Sie";
# Chinese "料盘", "槽位", "预设", "耗材丝", full-width punctuation; Polish "szpula", "slot", "profil", informal "ty").
# Spoolman data (names, vendors, notes) is never translated.
_TEXT_LANGS = ("pt-BR", "es", "de", "zh-CN", "pl")
_TEXT_ROWS: dict[str, tuple[str, str, str, str, str]] = {
    "Spoolman refused to add the Use with field ({error}); nothing was written.": (
        "O Spoolman recusou adicionar o campo Usar com ({error}); nada foi gravado.",
        "Spoolman rechazó añadir el campo Usar con ({error}); no se guardó nada.",
        "Spoolman hat das Feld Verwenden mit nicht angelegt ({error}); es wurde nichts geschrieben.",
        "Spoolman 拒绝添加“用于”字段（{error}）；未写入任何内容。",
        "Spoolman odmówił dodania pola „Używaj z” ({error}); niczego nie zapisano.",
    ),
    "Signed in ({region})": (
        "Conectado ({region})",
        "Sesión iniciada ({region})",
        "Angemeldet ({region})",
        "已登录（{region}）",
        "Zalogowano ({region})",
    ),
    "Signed in as {user} ({region})": (
        "Conectado como {user} ({region})",
        "Sesión iniciada como {user} ({region})",
        "Angemeldet als {user} ({region})",
        "已登录为 {user}（{region}）",
        "Zalogowano jako {user} ({region})",
    ),
    "Global": (
        "Global",
        "Global",
        "Global",
        "全球",
        "Globalny",
    ),
    "China": (
        "China",
        "China",
        "China",
        "中国",
        "Chiny",
    ),
    "slot {n} ({name})": (
        "slot {n} ({name})",
        "la ranura {n} ({name})",
        "Slot {n} ({name})",
        "槽位 {n}（{name}）",
        "slot {n} ({name})",
    ),
    "slots {n} ({name})": (
        "slots {n} ({name})",
        "las ranuras {n} ({name})",
        "Slots {n} ({name})",
        "槽位 {n}（{name}）",
        "sloty {n} ({name})",
    ),
    "needs {grams} of filament": (
        "precisa de {grams} de filamento",
        "necesita {grams} de filamento",
        "braucht {grams} Filament",
        "需要 {grams} 耗材丝",
        "potrzebuje {grams} filamentu",
    ),
    "need {grams} of filament together": (
        "precisam de {grams} de filamento juntos",
        "necesitan {grams} de filamento en total",
        "brauchen zusammen {grams} Filament",
        "共需要 {grams} 耗材丝",
        "potrzebują łącznie {grams} filamentu",
    ),
    "the spool has {have}": (
        "a bobina tem {have}",
        "el carrete tiene {have}",
        "die Spule hat {have}",
        "料盘有 {have}",
        "szpula ma {have}",
    ),
    "the {count} spools have {have} between them": (
        "as {count} bobinas têm {have} juntas",
        "los {count} carretes tienen {have} en total",
        "die {count} Spulen haben zusammen {have}",
        "这 {count} 个料盘共有 {have}",
        "szpule ({count}) mają łącznie {have}",
    ),
    " (only {matches} of {pool} matching spools are in {source})": (
        " (só {matches} de {pool} bobinas compatíveis estão no {source})",
        " (solo {matches} de {pool} carretes compatibles están en {source})",
        " (nur {matches} von {pool} passenden Spulen sind in {source})",
        "（{pool} 个匹配料盘中只有 {matches} 个在 {source} 中）",
        " ({source} zawiera tylko {matches} z {pool} pasujących szpul)",
    ),
    "slot {n}": (
        "slot {n}",
        "ranura {n}",
        "Slot {n}",
        "槽位 {n}",
        "slot {n}",
    ),
    "slots {n}": (
        "slots {n}",
        "ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
        "sloty {n}",
    ),
    "Slot {n}": (
        "Slot {n}",
        "Ranura {n}",
        "Slot {n}",
        "槽位 {n}",
        "Slot {n}",
    ),
    "Slots {n}": (
        "Slots {n}",
        "Ranuras {n}",
        "Slots {n}",
        "槽位 {n}",
        "Sloty {n}",
    ),
    "{name} ({slots}) has no drying date.": (
        "{name} ({slots}) não tem data de secagem.",
        "{name} ({slots}) no tiene fecha de secado.",
        "{name} ({slots}) hat kein Trocknungsdatum.",
        "{name}（{slots}）没有烘干日期。",
        "{name} ({slots}) nie ma daty suszenia.",
    ),
    "{name} ({slots}) was last dried {days} day ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dia.",
        "{name} ({slots}) se secó por última vez hace {days} día.",
        "{name} ({slots}) wurde zuletzt vor {days} Tag getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
        "{name} ({slots}) suszono ostatnio {days} dzień temu.",
    ),
    "{name} ({slots}) was last dried {days} days ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dias.",
        "{name} ({slots}) se secó por última vez hace {days} días.",
        "{name} ({slots}) wurde zuletzt vor {days} Tagen getrocknet.",
        "{name}（{slots}）上次烘干是在 {days} 天前。",
        "{name} ({slots}) suszono ostatnio {days} dni temu.",
    ),
    "About {cost} of filament.": (
        "Cerca de {cost} de filamento.",
        "Unos {cost} de filamento.",
        "Etwa {cost} an Filament.",
        "耗材丝成本约 {cost}。",
        "Około {cost} za filament.",
    ),
    "Loaded {count} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot colours, so a slot keeps its old colour until you pick its filament in the dropdown.": (
        "{count} slot(s) de filamento carregado(s) da impressora. O OrcaSlicer não deixa plugins definirem a cor dos slots, então um slot mantém a cor antiga até você escolher o filamento dele na lista.",
        "Se cargaron {count} ranura(s) de filamento desde la impresora. OrcaSlicer no deja que los plugins cambien el color de las ranuras, así que una ranura conserva su color anterior hasta que eliges su filamento en el desplegable.",
        "{count} Filament-Slot(s) vom Drucker geladen. OrcaSlicer lässt Plugins die Slotfarben nicht ändern, daher behält ein Slot seine alte Farbe, bis Sie sein Filament in der Auswahlliste wählen.",
        "已从打印机载入 {count} 个耗材丝槽位。OrcaSlicer 不允许插件设置槽位颜色，所以在您从下拉列表中选择该槽位的耗材丝之前，槽位会保留原来的颜色。",
        "Wczytano sloty filamentu z drukarki: {count}. OrcaSlicer nie pozwala wtyczkom ustawiać kolorów slotów, więc slot zachowuje dawny kolor, dopóki nie wybierzesz jego filamentu z listy.",
    ),
    " No Spoolman filament matched slot(s) {slots}.": (
        " Nenhum filamento do Spoolman corresponde ao(s) slot(s) {slots}.",
        " Ningún filamento de Spoolman coincide con la(s) ranura(s) {slots}.",
        " Kein Spoolman-Filament passt zu Slot(s) {slots}.",
        "没有 Spoolman 耗材丝与槽位 {slots} 匹配。",
        " Żaden filament ze Spoolmana nie pasował do slotów: {slots}.",
    ),
    " Could not change slot(s) {slots}.": (
        " Não foi possível alterar o(s) slot(s) {slots}.",
        " No se pudo cambiar la(s) ranura(s) {slots}.",
        " Slot(s) {slots} konnte(n) nicht geändert werden.",
        "无法更改槽位 {slots}。",
        " Nie udało się zmienić slotów: {slots}.",
    ),
    "Spooler: {spool} is down to {grams} g": (
        "Spooler: {spool} está com apenas {grams} g",
        "Spooler: quedan {grams} g de {spool}",
        "Spooler: {spool} hat nur noch {grams} g",
        "Spooler：{spool} 只剩 {grams} g",
        "Spooler: {spool} – zostało {grams} g",
    ),
    "Bambu blocked the request (HTTP 403)": (
        "A Bambu bloqueou a solicitação (HTTP 403)",
        "Bambu bloqueó la solicitud (HTTP 403)",
        "Bambu hat die Anfrage blockiert (HTTP 403)",
        "Bambu 拦截了该请求（HTTP 403）",
        "Bambu zablokowało żądanie (HTTP 403)",
    ),
    "Bambu Cloud returned an error (HTTP {code})": (
        "A Bambu Cloud retornou um erro (HTTP {code})",
        "Bambu Cloud devolvió un error (HTTP {code})",
        "Bambu Cloud hat einen Fehler gemeldet (HTTP {code})",
        "Bambu Cloud 返回错误（HTTP {code}）",
        "Bambu Cloud zwróciło błąd (HTTP {code})",
    ),
    "Bambu Cloud didn't sign you in": (
        "A Bambu Cloud não fez seu login",
        "Bambu Cloud no inició tu sesión",
        "Bambu Cloud hat Sie nicht angemeldet",
        "Bambu Cloud 登录失败",
        "Bambu Cloud cię nie zalogowało",
    ),
    "Bambu Cloud didn't accept your sign-in": (
        "A Bambu Cloud não aceitou seu login",
        "Bambu Cloud no aceptó tu inicio de sesión",
        "Bambu Cloud hat Ihre Anmeldung nicht akzeptiert",
        "Bambu Cloud 不接受您的登录",
        "Bambu Cloud nie przyjęło logowania",
    ),
    "Bambu Cloud sent a reply Spooler doesn't understand": (
        "A Bambu Cloud enviou uma resposta que o Spooler não entende",
        "Bambu Cloud envió una respuesta que Spooler no entiende",
        "Bambu Cloud hat eine Antwort gesendet, die Spooler nicht versteht",
        "Bambu Cloud 返回了 Spooler 无法识别的回复",
        "Bambu Cloud wysłało odpowiedź, której Spooler nie rozumie",
    ),
    "Could not reach Bambu Cloud ({reason})": (
        "Não foi possível acessar a Bambu Cloud ({reason})",
        "No se pudo conectar con Bambu Cloud ({reason})",
        "Bambu Cloud ist nicht erreichbar ({reason})",
        "无法连接 Bambu Cloud（{reason}）",
        "Nie można połączyć z Bambu Cloud ({reason})",
    ),
    "Signed in, but Spooler could not save the sign-in to {folder}": (
        "Login feito, mas o Spooler não conseguiu salvá-lo em {folder}",
        "Sesión iniciada, pero Spooler no pudo guardarla en {folder}",
        "Angemeldet, aber Spooler konnte die Anmeldung nicht in {folder} speichern",
        "已登录，但 Spooler 无法将登录信息保存到 {folder}",
        "Zalogowano, ale Spooler nie mógł zapisać logowania w {folder}",
    ),
    "Enter your Bambu email and password": (
        "Digite seu e-mail e senha da Bambu",
        "Introduce tu correo y contraseña de Bambu",
        "Geben Sie Ihre Bambu-E-Mail-Adresse und Ihr Passwort ein",
        "请输入您的 Bambu 邮箱和密码",
        "Wpisz e-mail i hasło do konta Bambu",
    ),
    "Your sign-in timed out. Enter your email and password again": (
        "O login expirou. Digite seu e-mail e senha de novo",
        "El inicio de sesión caducó. Introduce de nuevo tu correo y contraseña",
        "Die Anmeldung ist abgelaufen. Geben Sie E-Mail-Adresse und Passwort erneut ein",
        "登录已超时。请重新输入邮箱和密码",
        "Logowanie wygasło. Wpisz ponownie e-mail i hasło",
    ),
    "Enter your Bambu Lab verification code": (
        "Digite seu código de verificação da Bambu Lab",
        "Introduce tu código de verificación de Bambu Lab",
        "Geben Sie Ihren Bambu Lab-Bestätigungscode ein",
        "请输入您的 Bambu Lab 验证码",
        "Wpisz kod weryfikacyjny Bambu Lab",
    ),
    "Signed out": (
        "Desconectado",
        "Sesión cerrada",
        "Abgemeldet",
        "未登录",
        "Wylogowano",
    ),
    "Sign-in expired": (
        "Login expirado",
        "Sesión caducada",
        "Anmeldung abgelaufen",
        "登录已过期",
        "Logowanie wygasło",
    ),
    "Your Bambu sign-in has expired": (
        "Seu login na Bambu expirou",
        "Tu sesión de Bambu caducó",
        "Ihre Bambu-Anmeldung ist abgelaufen",
        "您的 Bambu 登录已过期",
        "Twoje logowanie do Bambu wygasło",
    ),
    "Your saved Bambu sign-in is unreadable": (
        "Não foi possível ler seu login salvo da Bambu",
        "No se puede leer tu sesión de Bambu guardada",
        "Ihre gespeicherte Bambu-Anmeldung ist nicht lesbar",
        "无法读取已保存的 Bambu 登录信息",
        "Zapisanego logowania do Bambu nie da się odczytać",
    ),
    "Open Settings and sign in to Bambu Cloud.": (
        "Abra os Ajustes e entre na Bambu Cloud.",
        "Abre Ajustes e inicia sesión en Bambu Cloud.",
        "Öffnen Sie die Einstellungen und melden Sie sich bei Bambu Cloud an.",
        "请打开设置并登录 Bambu Cloud。",
        "Otwórz ustawienia i zaloguj się do Bambu Cloud.",
    ),
    "The spool source kept changing while loading; refresh to try again.": (
        "A origem das bobinas mudou durante o carregamento; atualize para tentar de novo.",
        "El origen de los carretes cambió mientras se cargaba; actualiza para intentarlo de nuevo.",
        "Die Spulenquelle hat sich beim Laden mehrmals geändert; aktualisieren Sie, um es erneut zu versuchen.",
        "加载时料盘来源一直在变化；请刷新后重试。",
        "Źródło szpul zmieniało się podczas wczytywania; odśwież, aby spróbować ponownie.",
    ),
    "{printer} now books its usage to spool #{id}.": (
        "{printer} agora registra o consumo na bobina #{id}.",
        "{printer} ahora registra su consumo en el carrete #{id}.",
        "{printer} bucht den Verbrauch jetzt auf Spule #{id}.",
        "{printer} 现在将用量记到料盘 #{id}。",
        "{printer} księguje teraz zużycie na szpulę #{id}.",
    ),
    "Spoolman refused it (HTTP {code})": (
        "O Spoolman recusou (HTTP {code})",
        "Spoolman lo rechazó (HTTP {code})",
        "Spoolman hat abgelehnt (HTTP {code})",
        "Spoolman 拒绝了该请求（HTTP {code}）",
        "Spoolman odrzucił to (HTTP {code})",
    ),
    "Could not reach Spoolman ({reason})": (
        "Não foi possível acessar o Spoolman ({reason})",
        "No se pudo conectar con Spoolman ({reason})",
        "Spoolman ist nicht erreichbar ({reason})",
        "无法连接 Spoolman（{reason}）",
        "Nie można połączyć ze Spoolmanem ({reason})",
    ),
    "Could not reach Spoolman at {url} ({reason})": (
        "Não foi possível acessar o Spoolman em {url} ({reason})",
        "No se pudo conectar con Spoolman en {url} ({reason})",
        "Spoolman unter {url} ist nicht erreichbar ({reason})",
        "无法连接位于 {url} 的 Spoolman（{reason}）",
        "Nie można połączyć ze Spoolmanem pod adresem {url} ({reason})",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell whether changing the dried date would erase this spool's other extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe se alterar a data de secagem apagaria os outros campos extras desta bobina. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe si cambiar la fecha de secado borraría los demás campos extra de este carrete. No se escribió nada; revisa la conexión e inténtalo de nuevo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, ob das Ändern des Trocknungsdatums die anderen Zusatzfelder dieser Spule löschen würde. Es wurde nichts geschrieben; prüfen Sie die Verbindung und versuchen Sie es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法确定更改烘干日期是否会清除此料盘的其他额外字段。未写入任何内容；请检查连接后重试。",
        "Spooler nie mógł odczytać wersji Spoolmana, więc nie wie, czy zmiana daty suszenia nie skasuje pozostałych dodatkowych pól tej szpuli. Niczego nie zapisano; sprawdź połączenie i spróbuj ponownie.",
    ),
    "Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras desta bobina, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra de este carrete, y esta versión de Spoolman los reemplaza todos en cada cambio. No se escribió nada.",
        "Spooler konnte die Zusatzfelder dieser Spule nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取此料盘的额外字段，而此版本的 Spoolman 每次更改都会替换全部字段。未写入任何内容。",
        "Spooler nie mógł odczytać dodatkowych pól tej szpuli, a ta wersja Spoolmana przy zmianie zastępuje je wszystkie. Niczego nie zapisano.",
    ),
    "Could not open {url}.": (
        "Não foi possível abrir {url}.",
        "No se pudo abrir {url}.",
        "{url} konnte nicht geöffnet werden.",
        "无法打开 {url}。",
        "Nie można otworzyć {url}.",
    ),
    "Saved {path}": (
        "Salvo em {path}",
        "Guardado en {path}",
        "Gespeichert: {path}",
        "已保存到 {path}",
        "Zapisano {path}",
    ),
    "No web browser could be launched. Open this address yourself:\n{url}": (
        "Nenhum navegador pôde ser aberto. Abra este endereço você mesmo:\n{url}",
        "No se pudo abrir ningún navegador. Abre esta dirección tú mismo:\n{url}",
        "Es konnte kein Webbrowser gestartet werden. Öffnen Sie diese Adresse selbst:\n{url}",
        "无法启动网页浏览器。请自行打开此地址：\n{url}",
        "Nie udało się uruchomić przeglądarki. Otwórz ten adres samodzielnie:\n{url}",
    ),
    "Could not open the browser: {error}": (
        "Não foi possível abrir o navegador: {error}",
        "No se pudo abrir el navegador: {error}",
        "Der Browser konnte nicht geöffnet werden: {error}",
        "无法打开浏览器：{error}",
        "Nie można otworzyć przeglądarki: {error}",
    ),
    ".": (
        ".",
        ".",
        ".",
        "。",
        ".",
    ),
    ", ": (
        ", ",
        ", ",
        ", ",
        "、",
        ", ",
    ),
    " and ": (
        " e ",
        " y ",
        " und ",
        " 和 ",
        " i ",
    ),
    "Spooler: {text}": (
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler: {text}",
        "Spooler：{text}",
        "Spooler: {text}",
    ),
    " (+{count} more, see the log)": (
        " (+{count}, veja o log)",
        " (+{count} más, consulta el registro)",
        " (+{count} weitere, siehe Protokoll)",
        "（另有 {count} 条，见日志）",
        " (+{count} więcej, szczegóły w logu)",
    ),
    "the address must start with http:// or https://": (
        "o endereço deve começar com http:// ou https://",
        "la dirección debe empezar por http:// o https://",
        "die Adresse muss mit http:// oder https:// beginnen",
        "地址必须以 http:// 或 https:// 开头",
        "adres musi zaczynać się od http:// lub https://",
    ),
    "No Spoolman URL configured yet": (
        "Nenhuma URL do Spoolman configurada ainda",
        "Aún no hay una URL de Spoolman configurada",
        "Noch keine Spoolman-URL eingerichtet",
        "尚未配置 Spoolman URL",
        "Nie skonfigurowano jeszcze adresu URL Spoolmana",
    ),
    "No Spoolman URL configured yet - click Settings to set one.": (
        "Nenhuma URL do Spoolman configurada ainda: clique em Ajustes para definir uma.",
        "Aún no hay una URL de Spoolman configurada: pulsa Ajustes para añadirla.",
        "Noch keine Spoolman-URL eingerichtet: Klicken Sie auf Einstellungen, um eine festzulegen.",
        "尚未配置 Spoolman URL：请点击设置进行配置。",
        "Nie skonfigurowano jeszcze adresu URL Spoolmana – kliknij Ustawienia, aby go podać.",
    ),
    "{url} answered, but not like Spoolman does": (
        "{url} respondeu, mas não como o Spoolman responde",
        "{url} respondió, pero no como lo hace Spoolman",
        "{url} hat geantwortet, aber nicht wie Spoolman",
        "{url} 有响应，但不像 Spoolman 的响应",
        "{url} odpowiedział, ale nie tak jak Spoolman",
    ),
    "No OrcaSlicer user folder accepted the presets": (
        "Nenhuma pasta de usuário do OrcaSlicer aceitou os perfis",
        "Ninguna carpeta de usuario de OrcaSlicer aceptó los perfiles",
        "Kein OrcaSlicer-Benutzerordner hat die Profile angenommen",
        "没有 OrcaSlicer 用户文件夹接受这些预设",
        "Żaden folder użytkownika OrcaSlicer nie przyjął profili",
    ),
    "The spool source changed in Settings while this ran, so Spooler stopped before writing anything more. Try again.": (
        "A origem das bobinas mudou nos Ajustes durante a execução, então o Spooler parou antes de gravar mais nada. Tente de novo.",
        "El origen de los carretes cambió en Ajustes mientras esto se ejecutaba, así que Spooler se detuvo antes de escribir nada más. Inténtalo de nuevo.",
        "Die Spulenquelle wurde während des Vorgangs in den Einstellungen geändert, daher hat Spooler angehalten, bevor weiteres geschrieben wurde. Versuchen Sie es erneut.",
        "运行期间设置中的料盘来源发生了变化，Spooler 已停止，未再写入任何内容。请重试。",
        "Źródło szpul zmieniło się w ustawieniach w trakcie działania, więc Spooler przerwał przed dalszym zapisem. Spróbuj ponownie.",
    ),
    "Spoolman is not the spool source.": (
        "O Spoolman não é a origem das bobinas.",
        "Spoolman no es el origen de los carretes.",
        "Spoolman ist nicht die Spulenquelle.",
        "Spoolman 不是料盘来源。",
        "Spoolman nie jest źródłem szpul.",
    ),
    "Open a Spooler preset in OrcaSlicer's filament settings and change it first.": (
        "Primeiro abra um perfil do Spooler nos ajustes de filamento do OrcaSlicer e altere-o.",
        "Primero abre un perfil de Spooler en los ajustes de filamento de OrcaSlicer y cámbialo.",
        "Öffnen Sie zuerst ein Spooler-Profil in den Filamenteinstellungen von OrcaSlicer und ändern Sie es.",
        "请先在 OrcaSlicer 的耗材丝设置中打开一个 Spooler 预设并修改它。",
        "Najpierw otwórz profil Spoolera w ustawieniach filamentu OrcaSlicer i go zmień.",
    ),
    'Spoolman refused to add the OrcaSlicer preset field ({error}); nothing was written.': (
        'O Spoolman recusou adicionar o campo Perfil do OrcaSlicer ({error}); nada foi gravado.',
        'Spoolman rechazó añadir el campo Perfil de OrcaSlicer ({error}); no se escribió nada.',
        'Spoolman hat das Feld OrcaSlicer-Profil nicht angelegt ({error}); nichts wurde geschrieben.',
        'Spoolman 拒绝添加 OrcaSlicer 预设字段（{error}）；未写入任何内容。',
        'Spoolman odmówił dodania pola Profil OrcaSlicer ({error}); nic nie zapisano.',
    ),
    "That preset is no longer one of this spool's. Refresh, then send it again.": (
        'Esse perfil não é mais um desta bobina. Atualize e envie de novo.',
        'Ese perfil ya no es de esta bobina. Actualiza y vuelve a enviarlo.',
        'Dieses Profil gehört nicht mehr zu dieser Spule. Aktualisiere und sende es erneut.',
        '该预设已不属于这个料盘。请刷新后重新发送。',
        'Ten profil nie należy już do tej szpuli. Odśwież i wyślij ponownie.',
    ),
    'Select a printer in OrcaSlicer first, then send again.': (
        'Selecione primeiro uma impressora no OrcaSlicer e envie de novo.',
        'Selecciona primero una impresora en OrcaSlicer y vuelve a enviar.',
        'Wähle zuerst einen Drucker in OrcaSlicer aus und sende dann erneut.',
        '请先在 OrcaSlicer 中选择打印机，然后重新发送。',
        'Najpierw wybierz drukarkę w OrcaSlicer, a potem wyślij ponownie.',
    ),
    "{name} can't be compared with a Spooler preset for this printer; nothing was sent.": (
        '{name} não pode ser comparado com um perfil do Spooler para esta impressora; nada foi enviado.',
        '{name} no se puede comparar con un perfil de Spooler para esta impresora; no se envió nada.',
        '{name} lässt sich mit keinem Spooler-Profil für diesen Drucker vergleichen; nichts wurde gesendet.',
        '无法将 {name} 与此打印机的 Spooler 预设进行比较；未发送任何内容。',
        'Nie można porównać {name} z profilem Spoolera dla tej drukarki; nic nie wysłano.',
    ),
    '{name} has no unsaved changes, and its saved settings match Spoolman: nothing to send.': (
        '{name} não tem alterações não salvas, e os ajustes salvos batem com o Spoolman: nada a enviar.',
        '{name} no tiene cambios sin guardar y sus ajustes guardados coinciden con Spoolman: nada que enviar.',
        '{name} hat keine ungespeicherten Änderungen, und die gespeicherten Einstellungen stimmen mit Spoolman überein: nichts zu senden.',
        '{name} 没有未保存的更改，且已保存的设置与 Spoolman 一致：无需发送。',
        '{name} nie ma niezapisanych zmian, a zapisane ustawienia zgadzają się ze Spoolmanem: nie ma czego wysłać.',
    ),
    '{name} is linked to this spool only, and Spoolman keeps settings on the filament every spool of it shares; nothing was sent. Save your changes in the preset itself, or link the filament instead.': (
        '{name} está vinculado só a esta bobina, e o Spoolman guarda os ajustes no filamento que todas as bobinas dele compartilham; nada foi enviado. Salve as alterações no próprio perfil, ou vincule o filamento.',
        '{name} está vinculado solo a este carrete, y Spoolman guarda los ajustes en el filamento que comparten todos sus carretes; no se envió nada. Guarda los cambios en el propio perfil, o vincula el filamento.',
        '{name} ist nur mit dieser Spule verknüpft, und Spoolman speichert Einstellungen am Filament, das alle seine Spulen teilen; nichts wurde gesendet. Speichere die Änderungen im Profil selbst oder verknüpfe stattdessen das Filament.',
        '{name} 仅关联到此料盘，而 Spoolman 将设置保存在其所有料盘共用的耗材丝上；未发送任何内容。请在预设本身中保存更改，或改为关联耗材丝。',
        '{name} jest powiązany tylko z tą szpulą, a Spoolman trzyma ustawienia w filamencie wspólnym dla wszystkich jego szpul; nic nie wysłano. Zapisz zmiany w samym profilu albo powiąż filament.',
    ),
    "{name} has no unsaved changes to send.": (
        "{name} não tem alterações não salvas para enviar.",
        "{name} no tiene cambios sin guardar que enviar.",
        "{name} hat keine ungespeicherten Änderungen zum Senden.",
        "{name} 没有可发送的未保存更改。",
        "{name} nie ma niezapisanych zmian do wysłania.",
    ),
    "{name} is no longer a Spooler preset. Refresh, then send it again.": (
        "{name} não é mais um perfil do Spooler. Atualize e envie de novo.",
        "{name} ya no es un perfil de Spooler. Actualiza y vuelve a enviarlo.",
        "{name} ist kein Spooler-Profil mehr. Aktualisieren Sie und senden Sie es erneut.",
        "{name} 已不再是 Spooler 预设。请刷新后重新发送。",
        "{name} nie jest już profilem Spoolera. Odśwież, a potem wyślij ponownie.",
    ),
    "The {field} field of {name}'s filament isn't a JSON object; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} ist kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
        "Pole {field} filamentu {name} nie jest obiektem JSON; popraw je w Spoolmanie, a potem wyślij ponownie.",
    ),
    "The {field} field of {name}'s filament changed in Spoolman and isn't a JSON object now; fix it in Spoolman, then send again.": (
        "O campo {field} do filamento de {name} mudou no Spoolman e agora não é um objeto JSON; corrija-o no Spoolman e envie de novo.",
        "El campo {field} del filamento de {name} cambió en Spoolman y ahora no es un objeto JSON; corrígelo en Spoolman y vuelve a enviarlo.",
        "Das Feld {field} des Filaments von {name} wurde in Spoolman geändert und ist jetzt kein JSON-Objekt; korrigieren Sie es in Spoolman und senden Sie erneut.",
        "{name} 的耗材丝的 {field} 字段已在 Spoolman 中更改，现在不是 JSON 对象；请在 Spoolman 中修正后重新发送。",
        "Pole {field} filamentu {name} zmieniło się w Spoolmanie i nie jest już obiektem JSON; popraw je w Spoolmanie, a potem wyślij ponownie.",
    ),
    "Spooler: {name} has new calibrated values. Open Spooler to save them to Spoolman or skip them.": (
        "Spooler: {name} tem novos valores de calibração. Abra o Spooler para salvá-los no Spoolman ou ignorá-los.",
        "Spooler: {name} tiene nuevos valores de calibración. Abre Spooler para guardarlos en Spoolman u omitirlos.",
        "Spooler: {name} hat neue Kalibrierungswerte. Öffnen Sie Spooler, um sie in Spoolman zu speichern oder zu überspringen.",
        "Spooler：{name} 有新的校准值。打开 Spooler 将其保存到 Spoolman，或跳过。",
        "Spooler: {name} ma nowe skalibrowane wartości. Otwórz Spooler, aby zapisać je w Spoolmanie albo pominąć.",
    ),
    "Sent {settings} to Spoolman for {name}.": (
        "{settings} enviado(s) ao Spoolman para {name}.",
        "Se envió {settings} a Spoolman para {name}.",
        "{settings} für {name} an Spoolman gesendet.",
        "已将 {name} 的 {settings} 发送到 Spoolman。",
        "Wysłano do Spoolmana: {settings} dla {name}.",
    ),
    "Kept Spoolman's newer value for {settings}: the preset now has it, and your change stays unsaved; send again to use yours, or discard it.": (
        "Mantido o valor mais recente do Spoolman para {settings}: o perfil agora tem esse valor e sua alteração continua não salva; envie de novo para usar a sua ou descarte-a.",
        "Se mantuvo el valor más reciente de Spoolman para {settings}: el perfil ya lo tiene y tu cambio sigue sin guardar; vuelve a enviarlo para usar el tuyo o descártalo.",
        "Der neuere Spoolman-Wert für {settings} wurde behalten: Das Profil hat ihn jetzt, und Ihre Änderung bleibt ungespeichert; senden Sie erneut, um Ihren Wert zu verwenden, oder verwerfen Sie ihn.",
        "已保留 Spoolman 中 {settings} 的较新值：预设现在使用该值，您的更改仍未保存；再次发送可使用您的值，或将其放弃。",
        "Zachowano nowszą wartość ze Spoolmana dla: {settings}. Profil ma ją teraz, a twoja zmiana pozostaje niezapisana; wyślij ponownie, aby użyć swojej, albo ją odrzuć.",
    ),
    "Not sent: {settings}. Spoolman's {field} field holds only calibration settings; colour, vendor, material and name come from its own fields.": (
        "Não enviado: {settings}. O campo {field} do Spoolman guarda só ajustes de calibração; cor, fabricante, material e nome vêm dos campos próprios dele.",
        "No enviado: {settings}. El campo {field} de Spoolman solo guarda ajustes de calibración; el color, el fabricante, el material y el nombre vienen de sus propios campos.",
        "Nicht gesendet: {settings}. Das Spoolman-Feld {field} enthält nur Kalibrierungseinstellungen; Farbe, Hersteller, Material und Name stammen aus eigenen Feldern.",
        "未发送：{settings}。Spoolman 的 {field} 字段只保存校准设置；颜色、供应商、材料和名称来自其各自的字段。",
        "Nie wysłano: {settings}. Pole {field} w Spoolmanie przechowuje tylko ustawienia kalibracji; kolor, producent, materiał i nazwa pochodzą z jego własnych pól.",
    ),
    "The presets were not rebuilt: {error}": (
        "Os perfis não foram recriados: {error}",
        "Los perfiles no se reconstruyeron: {error}",
        "Die Profile wurden nicht neu erstellt: {error}",
        "预设未重建：{error}",
        "Nie przebudowano profili: {error}",
    ),
    "The filament presets were not rebuilt: {error}": (
        "Os perfis de filamento não foram recriados: {error}",
        "Los perfiles de filamento no se reconstruyeron: {error}",
        "Die Filamentprofile wurden nicht neu erstellt: {error}",
        "耗材丝预设未重建：{error}",
        "Nie przebudowano profili filamentu: {error}",
    ),
    "The filament presets could not be updated: {error}": (
        "Não foi possível atualizar os perfis de filamento: {error}",
        "No se pudieron actualizar los perfiles de filamento: {error}",
        "Die Filamentprofile konnten nicht aktualisiert werden: {error}",
        "无法更新耗材丝预设：{error}",
        "Nie udało się zaktualizować profili filamentu: {error}",
    ),
    "Synced {count} filament presets from Spoolman.": (
        "{count} perfis de filamento sincronizados do Spoolman.",
        "Se sincronizaron {count} perfiles de filamento desde Spoolman.",
        "{count} Filamentprofile aus Spoolman synchronisiert.",
        "已从 Spoolman 同步 {count} 个耗材丝预设。",
        "Zsynchronizowano profile filamentu ze Spoolmana: {count}.",
    ),
    "Setting a printer's spool needs Spoolman as the spool source.": (
        "Definir a bobina de uma impressora exige o Spoolman como origem das bobinas.",
        "Para asignar el carrete de una impresora, Spoolman debe ser el origen de los carretes.",
        "Zum Festlegen der Spule eines Druckers muss Spoolman die Spulenquelle sein.",
        "设置打印机的料盘需要以 Spoolman 作为料盘来源。",
        "Ustawienie szpuli drukarki wymaga Spoolmana jako źródła szpul.",
    ),
    "Spooler can only set the spool on a single-extruder Klipper printer.": (
        "O Spooler só consegue definir a bobina em uma impressora Klipper de uma extrusora.",
        "Spooler solo puede asignar el carrete en una impresora Klipper de un extrusor.",
        "Spooler kann die Spule nur bei einem Klipper-Drucker mit einem Extruder festlegen.",
        "Spooler 只能为单挤出机的 Klipper 打印机设置料盘。",
        "Spooler może ustawić szpulę tylko w drukarce Klipper z jednym ekstruderem.",
    ),
    "{printer}: no active spool, Moonraker stopped booking usage.": (
        "{printer}: nenhuma bobina ativa, o Moonraker parou de registrar o consumo.",
        "{printer}: sin carrete activo, Moonraker dejó de registrar el consumo.",
        "{printer}: keine aktive Spule, Moonraker bucht keinen Verbrauch mehr.",
        "{printer}：没有活动料盘，Moonraker 已停止记录用量。",
        "{printer}: brak aktywnej szpuli, Moonraker przestał księgować zużycie.",
    ),
    "{printer} manages its own spools; Spooler only reads them.": (
        "{printer} gerencia as próprias bobinas; o Spooler só as lê.",
        "{printer} gestiona sus propios carretes; Spooler solo los lee.",
        "{printer} verwaltet seine Spulen selbst; Spooler liest sie nur.",
        "{printer} 自行管理料盘；Spooler 只读取它们。",
        "{printer} sam zarządza swoimi szpulami; Spooler tylko je odczytuje.",
    ),
    "{printer} is paused in a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está com uma impressão pausada: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} tiene una impresión en pausa: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} hat einen pausierten Druck: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 有一个已暂停的打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
        "{printer} ma wstrzymany wydruk: Moonraker zaksięgowałby resztę tego wydruku na nową szpulę. Potwierdź, aby mimo to ją zmienić.",
    ),
    "{printer} is running a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está imprimindo: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} está imprimiendo: Moonraker registraría el resto de esta impresión en el nuevo carrete. Confirma para cambiarlo de todos modos.",
        "{printer} druckt gerade: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 正在打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
        "{printer} drukuje: Moonraker zaksięgowałby resztę tego wydruku na nową szpulę. Potwierdź, aby mimo to ją zmienić.",
    ),
    "Could not set the spool on {printer}: {error}": (
        "Não foi possível definir a bobina em {printer}: {error}",
        "No se pudo asignar el carrete en {printer}: {error}",
        "Die Spule konnte auf {printer} nicht festgelegt werden: {error}",
        "无法为 {printer} 设置料盘：{error}",
        "Nie można ustawić szpuli w {printer}: {error}",
    ),
    "That spool isn't in Spoolman, or it is archived.": (
        "Essa bobina não está no Spoolman ou está arquivada.",
        "Ese carrete no está en Spoolman o está archivado.",
        "Diese Spule ist nicht in Spoolman oder archiviert.",
        "该料盘不在 Spoolman 中，或已归档。",
        "Tej szpuli nie ma w Spoolmanie albo jest zarchiwizowana.",
    ),
    "Spool #{id} set from a scale weight of {grams} g.": (
        "Bobina #{id} ajustada pelo peso na balança de {grams} g.",
        "Carrete #{id} ajustado con un peso en báscula de {grams} g.",
        "Spule #{id} nach einem Waagengewicht von {grams} g gesetzt.",
        "已按称重 {grams} g 设置料盘 #{id}。",
        "Ustawiono szpulę #{id} według pomiaru na wadze: {grams} g.",
    ),
    "Spool #{id} archived.": (
        "Bobina #{id} arquivada.",
        "Carrete #{id} archivado.",
        "Spule #{id} archiviert.",
        "料盘 #{id} 已归档。",
        "Zarchiwizowano szpulę #{id}.",
    ),
    "Spool #{id} unarchived.": (
        "Bobina #{id} desarquivada.",
        "Carrete #{id} desarchivado.",
        "Spule #{id} wiederhergestellt.",
        "料盘 #{id} 已取消归档。",
        "Przywrócono szpulę #{id} z archiwum.",
    ),
    "Spool #{id} marked as dried today.": (
        "Bobina #{id} marcada como secada hoje.",
        "Carrete #{id} marcado como secado hoy.",
        "Spule #{id} als heute getrocknet markiert.",
        "料盘 #{id} 已标记为今天烘干。",
        "Oznaczono szpulę #{id} jako wysuszoną dzisiaj.",
    ),
    "Spool #{id} has no dried date now.": (
        "A bobina #{id} agora não tem data de secagem.",
        "El carrete #{id} ya no tiene fecha de secado.",
        "Spule #{id} hat jetzt kein Trocknungsdatum.",
        "料盘 #{id} 现在没有烘干日期。",
        "Szpula #{id} nie ma już daty suszenia.",
    ),
    "Spool #{id} now has {grams} g left.": (
        "A bobina #{id} agora tem {grams} g restantes.",
        "Al carrete #{id} ahora le quedan {grams} g.",
        "Spule #{id} hat jetzt noch {grams} g.",
        "料盘 #{id} 现在剩余 {grams} g。",
        "Na szpuli #{id} zostało teraz {grams} g.",
    ),
    "Spool #{id} moved to {location}.": (
        "Bobina #{id} movida para {location}.",
        "Carrete #{id} movido a {location}.",
        "Spule #{id} nach {location} verschoben.",
        "料盘 #{id} 已移至 {location}。",
        "Przeniesiono szpulę #{id} do: {location}.",
    ),
    "Spooler can only link a spool to a Snapmaker U1 toolhead or an Anycubic ACE slot.": (
        "O Spooler só vincula uma bobina a uma cabeça da Snapmaker U1 ou a um slot do ACE da Anycubic.",
        "Spooler solo vincula un carrete a un cabezal de la Snapmaker U1 o a una ranura del ACE de Anycubic.",
        "Spooler verknüpft eine Spule nur mit einem Werkzeugkopf des Snapmaker U1 oder einem ACE-Slot von Anycubic.",
        "Spooler 只能将料盘关联到 Snapmaker U1 的工具头或 Anycubic ACE 的槽位。",
        "Spooler łączy szpulę tylko z głowicą Snapmaker U1 albo ze slotem ACE Anycubic.",
    ),
    "Spool #{id} isn't linked to {slot}.": (
        "A bobina #{id} não está vinculada a {slot}.",
        "El carrete #{id} no está vinculado a {slot}.",
        "Spule #{id} ist nicht mit {slot} verknüpft.",
        "料盘 #{id} 未关联到 {slot}。",
        "Szpula #{id} nie jest połączona z: {slot}.",
    ),
    "Spool #{id} is no longer linked to {slot}.": (
        "A bobina #{id} não está mais vinculada a {slot}.",
        "El carrete #{id} ya no está vinculado a {slot}.",
        "Spule #{id} ist nicht mehr mit {slot} verknüpft.",
        "料盘 #{id} 已不再关联到 {slot}。",
        "Szpula #{id} nie jest już połączona z: {slot}.",
    ),
    "Spool #{id} linked to {slot}.": (
        "Bobina #{id} vinculada a {slot}.",
        "Carrete #{id} vinculado a {slot}.",
        "Spule #{id} mit {slot} verknüpft.",
        "料盘 #{id} 已关联到 {slot}。",
        "Połączono szpulę #{id} z: {slot}.",
    ),
    "Spool #{id} has no location now.": (
        "A bobina #{id} agora não tem local.",
        "El carrete #{id} ya no tiene ubicación.",
        "Spule #{id} hat jetzt keinen Lagerort.",
        "料盘 #{id} 现在没有位置。",
        "Szpula #{id} nie ma już lokalizacji.",
    ),
    "Saved the note on spool #{id}.": (
        "Nota da bobina #{id} salva.",
        "Nota del carrete #{id} guardada.",
        "Notiz zu Spule #{id} gespeichert.",
        "已保存料盘 #{id} 的备注。",
        "Zapisano notatkę szpuli #{id}.",
    ),
    "Spool #{id} has no note now.": (
        "A bobina #{id} agora não tem nota.",
        "El carrete #{id} ya no tiene nota.",
        "Spule #{id} hat jetzt keine Notiz.",
        "料盘 #{id} 现在没有备注。",
        "Szpula #{id} nie ma już notatki.",
    ),
    "Added spool {spool} of the same filament.": (
        "Bobina {spool} do mesmo filamento adicionada.",
        "Se añadió el carrete {spool} del mismo filamento.",
        "Spule {spool} mit demselben Filament hinzugefügt.",
        "已添加相同耗材丝的料盘 {spool}。",
        "Dodano szpulę {spool} tego samego filamentu.",
    ),
    "Added {count} spools of the same filament: {spools}.": (
        "{count} bobinas do mesmo filamento adicionadas: {spools}.",
        "Se añadieron {count} carretes del mismo filamento: {spools}.",
        "{count} Spulen mit demselben Filament hinzugefügt: {spools}.",
        "已添加 {count} 个相同耗材丝的料盘：{spools}。",
        "Dodano szpule tego samego filamentu ({count}): {spools}.",
    ),
    "This Spoolman can't remove a spool's dried date; Spoolman 0.26 or newer can. Nothing was written; mark it dried again to change the date.": (
        "Este Spoolman não consegue remover a data de secagem de uma bobina; o Spoolman 0.26 ou mais recente consegue. Nada foi gravado; marque como secada de novo para mudar a data.",
        "Este Spoolman no puede quitar la fecha de secado de un carrete; Spoolman 0.26 o posterior sí puede. No se guardó nada; márcalo como secado de nuevo para cambiar la fecha.",
        "Dieses Spoolman kann das Trocknungsdatum einer Spule nicht entfernen; Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben; markiere sie erneut als getrocknet, um das Datum zu ändern.",
        "此 Spoolman 无法移除料盘的烘干日期；Spoolman 0.26 或更新版本可以。未写入任何内容；再次标记为已烘干即可更改日期。",
        "Ten Spoolman nie potrafi usunąć daty suszenia szpuli; potrafi to Spoolman 0.26 lub nowszy. Niczego nie zapisano; oznacz szpulę ponownie jako wysuszoną, aby zmienić datę.",
    ),
    "The value for {field} isn't valid; nothing was written.": (
        "O valor de {field} não é válido; nada foi gravado.",
        "El valor de {field} no es válido; no se guardó nada.",
        "Der Wert für {field} ist ungültig; es wurde nichts geschrieben.",
        "{field} 的值无效；未写入任何内容。",
        "Wartość pola {field} jest nieprawidłowa; niczego nie zapisano.",
    ),
    "Spooler couldn't read Spoolman's version, so it can't tell how this Spoolman saves extra fields. Nothing was written; check the connection and try again.": (
        "O Spooler não conseguiu ler a versão do Spoolman, então não sabe como este Spoolman salva campos extras. Nada foi gravado; confira a conexão e tente de novo.",
        "Spooler no pudo leer la versión de Spoolman, así que no sabe cómo guarda este Spoolman los campos extra. No se guardó nada; revisa la conexión y vuelve a intentarlo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, wie dieses Spoolman Zusatzfelder speichert. Es wurde nichts geschrieben; prüfe die Verbindung und versuche es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法判断此 Spoolman 如何保存额外字段。未写入任何内容；请检查连接后重试。",
        "Spooler nie mógł odczytać wersji Spoolmana, więc nie wie, jak ten Spoolman zapisuje dodatkowe pola. Niczego nie zapisano; sprawdź połączenie i spróbuj ponownie.",
    ),
    "This Spoolman can't empty an extra field ({fields}); Spoolman 0.26 or newer can. Nothing was written.": (
        "Este Spoolman não consegue esvaziar um campo extra ({fields}); o Spoolman 0.26 ou mais recente consegue. Nada foi gravado.",
        "Este Spoolman no puede vaciar un campo extra ({fields}); Spoolman 0.26 o posterior sí puede. No se guardó nada.",
        "Dieses Spoolman kann ein Zusatzfeld nicht leeren ({fields}); Spoolman 0.26 oder neuer kann es. Es wurde nichts geschrieben.",
        "此 Spoolman 无法清空额外字段（{fields}）；Spoolman 0.26 或更新版本可以。未写入任何内容。",
        "Ten Spoolman nie potrafi wyczyścić dodatkowego pola ({fields}); potrafi to Spoolman 0.26 lub nowszy. Niczego nie zapisano.",
    ),
    "Spooler couldn't read the extra fields Spoolman holds, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras que o Spoolman guarda, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra que guarda Spoolman, y esta versión de Spoolman los reemplaza todos en cada cambio. No se guardó nada.",
        "Spooler konnte die Zusatzfelder in Spoolman nicht lesen, und diese Spoolman-Version ersetzt bei jeder Änderung alle. Es wurde nichts geschrieben.",
        "Spooler 无法读取 Spoolman 中的额外字段，而此 Spoolman 版本每次更改都会替换全部额外字段。未写入任何内容。",
        "Spooler nie mógł odczytać dodatkowych pól przechowywanych w Spoolmanie, a ta wersja Spoolmana przy zmianie zastępuje je wszystkie. Niczego nie zapisano.",
    ),
    "Saved the filament of spool #{id}, but Spoolman refused the spool: {error}": (
        "O filamento da bobina #{id} foi salvo, mas o Spoolman recusou a bobina: {error}",
        "Se guardó el filamento del carrete #{id}, pero Spoolman rechazó el carrete: {error}",
        "Das Filament von Spule #{id} wurde gespeichert, aber Spoolman hat die Spule abgelehnt: {error}",
        "已保存料盘 #{id} 的耗材丝，但 Spoolman 拒绝了料盘：{error}",
        "Zapisano filament szpuli #{id}, ale Spoolman odrzucił szpulę: {error}",
    ),
    "Saved spool #{id} and its filament.": (
        "Bobina #{id} e seu filamento salvos.",
        "Se guardaron el carrete #{id} y su filamento.",
        "Spule #{id} und ihr Filament gespeichert.",
        "已保存料盘 #{id} 及其耗材丝。",
        "Zapisano szpulę #{id} i jej filament.",
    ),
    "Saved spool #{id}.": (
        "Bobina #{id} salva.",
        "Carrete #{id} guardado.",
        "Spule #{id} gespeichert.",
        "已保存料盘 #{id}。",
        "Zapisano szpulę #{id}.",
    ),
    "Spool #{id} had no changes to save.": (
        "A bobina #{id} não tinha alterações para salvar.",
        "El carrete #{id} no tenía cambios que guardar.",
        "Spule #{id} hatte keine Änderungen zum Speichern.",
        "料盘 #{id} 没有需要保存的更改。",
        "Szpula #{id} nie miała zmian do zapisania.",
    ),
    "Kept Spoolman's newer value for {fields}: it changed there while you were editing.": (
        "O valor mais recente do Spoolman foi mantido para {fields}: ele mudou lá enquanto você editava.",
        "Se mantuvo el valor más reciente de Spoolman para {fields}: cambió allí mientras editabas.",
        "Der neuere Wert aus Spoolman wurde für {fields} behalten: Er hat sich dort während deiner Bearbeitung geändert.",
        "已保留 Spoolman 中 {fields} 的较新值：你编辑期间它在那里被更改了。",
        "Zachowano nowszą wartość ze Spoolmana dla: {fields}. Zmieniła się tam w trakcie twojej edycji.",
    ),
    "Created filament #{filament}, but Spoolman refused the spool: {error}": (
        "Filamento #{filament} criado, mas o Spoolman recusou a bobina: {error}",
        "Se creó el filamento #{filament}, pero Spoolman rechazó el carrete: {error}",
        "Filament #{filament} angelegt, aber Spoolman hat die Spule abgelehnt: {error}",
        "已创建耗材丝 #{filament}，但 Spoolman 拒绝了料盘：{error}",
        "Utworzono filament #{filament}, ale Spoolman odrzucił szpulę: {error}",
    ),
    "Added spool #{id} with the new filament #{filament}.": (
        "Bobina #{id} adicionada com o novo filamento #{filament}.",
        "Se añadió el carrete #{id} con el nuevo filamento #{filament}.",
        "Spule #{id} mit dem neuen Filament #{filament} hinzugefügt.",
        "已添加料盘 #{id}，使用新耗材丝 #{filament}。",
        "Dodano szpulę #{id} z nowym filamentem #{filament}.",
    ),
    "Added spool #{id}.": (
        "Bobina #{id} adicionada.",
        "Se añadió el carrete #{id}.",
        "Spule #{id} hinzugefügt.",
        "已添加料盘 #{id}。",
        "Dodano szpulę #{id}.",
    ),
    "Archived spool #{id} carries this RFID tag; unarchive it instead. Nothing was written.": (
        "A bobina arquivada #{id} tem esta etiqueta RFID; desarquive-a. Nada foi gravado.",
        "El carrete archivado #{id} tiene esta etiqueta RFID; desarchívelo. No se escribió nada.",
        "Die archivierte Spule #{id} trägt dieses RFID-Tag; holen Sie sie aus dem Archiv. Es wurde nichts geschrieben.",
        "已归档的料盘 #{id} 带有此 RFID 标签，请取消归档。未写入任何内容。",
        "Ten tag RFID ma zarchiwizowana szpula #{id}; przywróć ją z archiwum. Niczego nie zapisano.",
    ),
    "Spool #{id} already carries this RFID tag; nothing was written.": (
        "A bobina #{id} já tem esta etiqueta RFID; nada foi gravado.",
        "El carrete #{id} ya tiene esta etiqueta RFID; no se escribió nada.",
        "Spule #{id} trägt dieses RFID-Tag bereits; es wurde nichts geschrieben.",
        "料盘 #{id} 已带有此 RFID 标签；未写入任何内容。",
        "Szpula #{id} ma już ten tag RFID; niczego nie zapisano.",
    ),
    "Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.": (
        "O campo \"tag\" das bobinas no Spoolman não é um campo de texto, então a etiqueta RFID não pode ser guardada; nada foi gravado.",
        "El campo \"tag\" de los carretes en Spoolman no es un campo de texto, así que la etiqueta RFID no se puede guardar; no se escribió nada.",
        "Das Spulenfeld \"tag\" in Spoolman ist kein Textfeld, daher kann das RFID-Tag nicht gespeichert werden; es wurde nichts geschrieben.",
        "Spoolman 的料盘字段“tag”不是文本字段，无法保存 RFID 标签；未写入任何内容。",
        "Pole szpuli „tag” w Spoolmanie nie jest polem tekstowym, więc nie można zapisać tagu RFID; niczego nie zapisano.",
    ),
    "Added spool {spools}, then Spoolman refused the next one: {error}": (
        "Bobina {spools} adicionada, depois o Spoolman recusou a próxima: {error}",
        "Se añadió el carrete {spools} y luego Spoolman rechazó el siguiente: {error}",
        "Spule {spools} hinzugefügt, dann hat Spoolman die nächste abgelehnt: {error}",
        "已添加料盘 {spools}，随后 Spoolman 拒绝了下一个：{error}",
        "Dodano szpulę {spools}, a potem Spoolman odrzucił następną: {error}",
    ),
    "Opened spool #{id} in Spoolman.": (
        "Bobina #{id} aberta no Spoolman.",
        "Carrete #{id} abierto en Spoolman.",
        "Spule #{id} in Spoolman geöffnet.",
        "已在 Spoolman 中打开料盘 #{id}。",
        "Otwarto szpulę #{id} w Spoolmanie.",
    ),
    "Unknown spool action.": (
        "Ação de bobina desconhecida.",
        "Acción de carrete desconocida.",
        "Unbekannte Spulenaktion.",
        "未知的料盘操作。",
        "Nieznana akcja na szpuli.",
    ),
    "Spool actions need Spoolman as the source.": (
        "As ações de bobina exigem o Spoolman como origem.",
        "Las acciones de carrete necesitan Spoolman como origen.",
        "Spulenaktionen erfordern Spoolman als Quelle.",
        "料盘操作需要以 Spoolman 作为来源。",
        "Akcje na szpulach wymagają Spoolmana jako źródła.",
    ),
    "No spool chosen.": (
        "Nenhuma bobina escolhida.",
        "No se eligió ningún carrete.",
        "Keine Spule ausgewählt.",
        "未选择料盘。",
        "Nie wybrano szpuli.",
    ),
    "The spool source changed since this list was read; nothing was written. Refresh and try again.": (
        "A origem das bobinas mudou desde que esta lista foi lida; nada foi gravado. Atualize e tente de novo.",
        "El origen de los carretes cambió desde que se leyó esta lista; no se escribió nada. Actualiza e inténtalo de nuevo.",
        "Die Spulenquelle hat sich seit dem Lesen dieser Liste geändert; es wurde nichts geschrieben. Aktualisieren Sie und versuchen Sie es erneut.",
        "读取此列表后料盘来源已更改；未写入任何内容。请刷新后重试。",
        "Źródło szpul zmieniło się od wczytania tej listy; niczego nie zapisano. Odśwież i spróbuj ponownie.",
    ),
    "Spoolman has the change, but Spooler could not update its history file.": (
        "O Spoolman tem a alteração, mas o Spooler não conseguiu atualizar seu arquivo de histórico.",
        "Spoolman tiene el cambio, pero Spooler no pudo actualizar su archivo de historial.",
        "Spoolman hat die Änderung, aber Spooler konnte seine Verlaufsdatei nicht aktualisieren.",
        "Spoolman 已有该更改，但 Spooler 无法更新其历史文件。",
        "Spoolman ma już zmianę, ale Spooler nie mógł zaktualizować swojego pliku historii.",
    ),
    "This print was recorded for another spool source, or before Spooler noted which Spoolman it belongs to, so Spooler won't book it here. If it is still owed, book it in Spoolman by hand.": (
        "Esta impressão foi registrada para outra origem de bobinas, ou antes de o Spooler anotar a qual Spoolman ela pertence, então o Spooler não vai lançá-la aqui. Se ainda estiver pendente, lance-a à mão no Spoolman.",
        "Esta impresión se registró para otro origen de carretes, o antes de que Spooler anotara a qué Spoolman pertenece, así que Spooler no la registrará aquí. Si sigue pendiente, regístrala a mano en Spoolman.",
        "Dieser Druck wurde für eine andere Spulenquelle erfasst oder bevor Spooler vermerkt hat, zu welchem Spoolman er gehört, daher bucht Spooler ihn hier nicht. Falls er noch offen ist, buchen Sie ihn von Hand in Spoolman.",
        "此打印记录属于另一个料盘来源，或记录于 Spooler 标明其所属 Spoolman 之前，因此 Spooler 不会在此记账。如果仍需记录，请在 Spoolman 中手动记录。",
        "Ten wydruk zapisano dla innego źródła szpul albo zanim Spooler zanotował, do którego Spoolmana należy, więc Spooler go tu nie zaksięguje. Jeśli nadal trzeba go rozliczyć, zaksięguj go w Spoolmanie ręcznie.",
    ),
    "Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; adjust the spools in Spoolman by hand.": (
        "Desfazer exige o Spoolman 0.18 ou mais recente, que devolve os gramas em uma etapa sem perder o consumo registrado nesse meio-tempo. O Spooler não conseguiu confirmar a versão deste Spoolman, então nada mudou; ajuste as bobinas à mão no Spoolman.",
        "Deshacer necesita Spoolman 0.18 o posterior, que devuelve los gramos en un solo paso sin perder el consumo registrado mientras tanto. Spooler no pudo confirmar la versión de este Spoolman, así que no cambió nada; ajusta los carretes a mano en Spoolman.",
        "Rückgängig machen erfordert Spoolman 0.18 oder neuer, das Gramm in einem Schritt zurückbucht, ohne zwischenzeitlich gebuchten Verbrauch zu verlieren. Spooler konnte die Version dieses Spoolman nicht bestätigen, daher wurde nichts geändert; passen Sie die Spulen von Hand in Spoolman an.",
        "撤销需要 Spoolman 0.18 或更新版本，它能一步加回克数，且不会丢失期间记录的用量。Spooler 无法确认此 Spoolman 的版本，因此未做任何更改；请在 Spoolman 中手动调整料盘。",
        "Cofanie wymaga Spoolmana 0.18 lub nowszego, który oddaje gramy w jednym kroku, nie gubiąc zużycia zaksięgowanego w międzyczasie. Spooler nie mógł potwierdzić wersji tego Spoolmana, więc nic nie zmieniono; popraw szpule w Spoolmanie ręcznie.",
    ),
    "Spooler could not save its booking state ({file}), so it stopped. Rows it was sending are marked for you to check in Spoolman.": (
        "O Spooler não conseguiu salvar seu estado de lançamentos ({file}), então parou. As linhas que ele estava enviando estão marcadas para você conferir no Spoolman.",
        "Spooler no pudo guardar su estado de registros ({file}), así que se detuvo. Las filas que estaba enviando quedan marcadas para que las revises en Spoolman.",
        "Spooler konnte seinen Buchungsstand ({file}) nicht speichern und hat daher angehalten. Zeilen, die gerade gesendet wurden, sind markiert, damit Sie sie in Spoolman prüfen.",
        "Spooler 无法保存其记账状态（{file}），因此已停止。正在发送的行已标记，请在 Spoolman 中核对。",
        "Spooler nie mógł zapisać stanu księgowania ({file}), więc przerwał. Wiersze, które wysyłał, oznaczono do sprawdzenia w Spoolmanie.",
    ),
    "Spooler can't tell whether Spoolman applied this. Check the spool in Spoolman, then say which.": (
        "O Spooler não sabe se o Spoolman aplicou isto. Confira a bobina no Spoolman e diga o que aconteceu.",
        "Spooler no sabe si Spoolman aplicó esto. Revisa el carrete en Spoolman y di qué ocurrió.",
        "Spooler kann nicht erkennen, ob Spoolman dies übernommen hat. Prüfen Sie die Spule in Spoolman und geben Sie an, was zutrifft.",
        "Spooler 无法确定 Spoolman 是否已应用此操作。请在 Spoolman 中检查料盘，然后说明结果。",
        "Spooler nie wie, czy Spoolman to zastosował. Sprawdź szpulę w Spoolmanie, a potem wskaż, jak jest.",
    ),
    "Other": (
        "Outro",
        "Otro",
        "Sonstiges",
        "其他",
        "Inne",
    ),
    "Could not reach GitHub ({reason})": (
        "Não foi possível acessar o GitHub ({reason})",
        "No se pudo conectar con GitHub ({reason})",
        "GitHub ist nicht erreichbar ({reason})",
        "无法连接 GitHub（{reason}）",
        "Nie można połączyć z GitHubem ({reason})",
    ),
    "GitHub sent an answer Spooler doesn't understand": (
        "O GitHub enviou uma resposta que o Spooler não entende",
        "GitHub envió una respuesta que Spooler no entiende",
        "GitHub hat eine Antwort gesendet, die Spooler nicht versteht",
        "GitHub 返回了 Spooler 无法识别的回复",
        "GitHub wysłał odpowiedź, której Spooler nie rozumie",
    ),
    "No published release found yet": (
        "Nenhuma versão publicada ainda",
        "Aún no hay ninguna versión publicada",
        "Noch keine veröffentlichte Version gefunden",
        "尚未找到已发布的版本",
        "Nie znaleziono jeszcze opublikowanego wydania",
    ),
    "GitHub returned HTTP {code}": (
        "O GitHub retornou HTTP {code}",
        "GitHub devolvió HTTP {code}",
        "GitHub meldete HTTP {code}",
        "GitHub 返回 HTTP {code}",
        "GitHub zwrócił HTTP {code}",
    ),
    "{slot} {need} but {supply}{tracked}": (
        "{slot} {need}, mas {supply}{tracked}",
        "{slot} {need}, pero {supply}{tracked}",
        "{slot} {need}, aber {supply}{tracked}",
        "{slot}{need}，但{supply}{tracked}",
        "{slot} {need}, ale {supply}{tracked}",
    ),
    " Swap in spool #{id} ({location}, {grams} g).": (
        " Troque pela bobina #{id} ({location}, {grams} g).",
        " Cambia al carrete #{id} ({location}, {grams} g).",
        " Wechseln Sie zu Spule #{id} ({location}, {grams} g).",
        "可换用料盘 #{id}（{location}，{grams} g）。",
        " Załóż szpulę #{id} ({location}, {grams} g).",
    ),
    " Swap in spool #{id} ({grams} g).": (
        " Troque pela bobina #{id} ({grams} g).",
        " Cambia al carrete #{id} ({grams} g).",
        " Wechseln Sie zu Spule #{id} ({grams} g).",
        "可换用料盘 #{id}（{grams} g）。",
        " Załóż szpulę #{id} ({grams} g).",
    ),
    "of {matches} matching spools the fullest has {have} and the smallest has {worst}, so make sure the right one is loaded": (
        "das {matches} bobinas compatíveis, a mais cheia tem {have} e a mais vazia tem {worst}, então confira se a certa está carregada",
        "de {matches} carretes compatibles, el más lleno tiene {have} y el más vacío {worst}, así que asegúrate de que esté cargado el correcto",
        "von {matches} passenden Spulen hat die vollste {have} und die leerste {worst}, also achten Sie darauf, dass die richtige geladen ist",
        "在 {matches} 个匹配料盘中，最满的有 {have}，最少的只有 {worst}，请确认装入的是正确的料盘",
        "spośród {matches} pasujących szpul najpełniejsza ma {have}, a najmniej pełna {worst}, więc upewnij się, że załadowano właściwą",
    ),
    "the {count} fullest of {matches} matching spools hold {have} and the {count} smallest hold {worst}, so make sure the right ones are loaded": (
        "das {matches} bobinas compatíveis, as {count} mais cheias têm {have} e as {count} mais vazias têm {worst}, então confira se as certas estão carregadas",
        "de {matches} carretes compatibles, los {count} más llenos tienen {have} y los {count} más vacíos {worst}, así que asegúrate de que estén cargados los correctos",
        "von {matches} passenden Spulen haben die {count} vollsten {have} und die {count} leersten {worst}, also achten Sie darauf, dass die richtigen geladen sind",
        "在 {matches} 个匹配料盘中，最满的 {count} 个共有 {have}，最少的 {count} 个只有 {worst}，请确认装入的是正确的料盘",
        "spośród {matches} pasujących szpul najpełniejsze ({count}) mają łącznie {have}, a najmniej pełne ({count}) {worst}, więc upewnij się, że załadowano właściwe",
    ),
    "{slot} {need}; {body}": (
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot} {need}; {body}",
        "{slot}{need}；{body}",
        "{slot} {need}; {body}",
    ),
    "{slot} {need} ({padded} with the {margin}% margin) and {supply}{tracked}": (
        "{slot} {need} ({padded} com a margem de {margin}%) e {supply}{tracked}",
        "{slot} {need} ({padded} con el margen del {margin} %) y {supply}{tracked}",
        "{slot} {need} ({padded} mit {margin} % Reserve) und {supply}{tracked}",
        "{slot}{need}（加上 {margin}% 余量为 {padded}），而{supply}{tracked}",
        "{slot} {need} ({padded} z zapasem {margin}%), a {supply}{tracked}",
    ),
    "{slot} {need}, {supply}": (
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot} {need}, {supply}",
        "{slot}{need}，{supply}",
        "{slot} {need}, {supply}",
    ),
    "not enough filament loaded in the AMS.": (
        "filamento insuficiente carregado no AMS.",
        "no hay suficiente filamento cargado en el AMS.",
        "nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝不足。",
        "za mało filamentu załadowanego w AMS.",
    ),
    "not enough filament loaded.": (
        "filamento insuficiente carregado.",
        "no hay suficiente filamento cargado.",
        "nicht genug Filament geladen.",
        "装入的耗材丝不足。",
        "za mało załadowanego filamentu.",
    ),
    "not enough filament may be loaded in the AMS.": (
        "talvez não haja filamento suficiente carregado no AMS.",
        "puede que no haya suficiente filamento cargado en el AMS.",
        "möglicherweise ist nicht genug Filament im AMS geladen.",
        "AMS 中装入的耗材丝可能不足。",
        "w AMS może być za mało filamentu.",
    ),
    "not enough filament may be loaded.": (
        "talvez não haja filamento suficiente carregado.",
        "puede que no haya suficiente filamento cargado.",
        "möglicherweise ist nicht genug Filament geladen.",
        "装入的耗材丝可能不足。",
        "załadowanego filamentu może być za mało.",
    ),
    "also check: ": (
        "confira também: ",
        "revisa también: ",
        "prüfen Sie auch: ",
        "另请检查：",
        "sprawdź też: ",
    ),
    "also barely enough: ": (
        "também no limite: ",
        "también muy justo: ",
        "ebenfalls knapp: ",
        "同样勉强够用：",
        "też ledwo wystarczy: ",
    ),
    "barely enough filament.": (
        "filamento no limite.",
        "filamento muy justo.",
        "Filament knapp.",
        "耗材丝勉强够用。",
        "filamentu ledwo wystarczy.",
    ),
    "quantity OK.": (
        "quantidade OK.",
        "cantidad correcta.",
        "Menge OK.",
        "用量充足。",
        "ilość OK.",
    ),
    "quantity OK for slots {slots}.": (
        "quantidade OK para os slots {slots}.",
        "cantidad correcta para las ranuras {slots}.",
        "Menge OK für Slots {slots}.",
        "槽位 {slots} 用量充足。",
        "ilość OK dla slotów {slots}.",
    ),
    "no spool found for {slots}, so they weren't checked": (
        "nenhuma bobina encontrada para {slots}, então não foram conferidos",
        "no se encontró carrete para {slots}, así que no se comprobaron",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
        "nie znaleziono szpuli (dotyczy: {slots}), więc nie sprawdzono ilości",
    ),
    "no spool found for {slots}, so it wasn't checked": (
        "nenhuma bobina encontrada para {slots}, então não foi conferido",
        "no se encontró carrete para {slots}, así que no se comprobó",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到{slots}的料盘，因此未检查",
        "nie znaleziono szpuli (dotyczy: {slots}), więc nie sprawdzono ilości",
    ),
    "Not checked": (
        "Não conferido",
        "Sin comprobar",
        "Nicht geprüft",
        "未检查",
        "Nie sprawdzono",
    ),
    "no spool found for these slots": (
        "nenhuma bobina encontrada para estes slots",
        "no se encontró carrete para estas ranuras",
        "keine Spule für diese Slots gefunden",
        "未找到这些槽位的料盘",
        "nie znaleziono szpuli dla tych slotów",
    ),
    "no spool found for this slot": (
        "nenhuma bobina encontrada para este slot",
        "no se encontró carrete para esta ranura",
        "keine Spule für diesen Slot gefunden",
        "未找到此槽位的料盘",
        "nie znaleziono szpuli dla tego slotu",
    ),
    "Quantity OK": (
        "Quantidade OK",
        "Cantidad correcta",
        "Menge OK",
        "用量充足",
        "Ilość OK",
    ),
    "Barely enough": (
        "No limite",
        "Muy justo",
        "Knapp",
        "勉强够用",
        "Ledwo wystarczy",
    ),
    "Not enough": (
        "Insuficiente",
        "Insuficiente",
        "Nicht genug",
        "不足",
        "Za mało",
    ),
    "Check the spools": (
        "Confira as bobinas",
        "Revisa los carretes",
        "Spulen prüfen",
        "检查料盘",
        "Sprawdź szpule",
    ),
    "Check the spool": (
        "Confira a bobina",
        "Revisa el carrete",
        "Spule prüfen",
        "检查料盘",
        "Sprawdź szpulę",
    ),
    "{need} needed · matching spools hold {low} to {high}": (
        "{need} necessários · as bobinas compatíveis têm de {low} a {high}",
        "{need} necesarios · los carretes compatibles tienen de {low} a {high}",
        "{need} benötigt · passende Spulen haben {low} bis {high}",
        "需要 {need} · 匹配料盘有 {low} 至 {high}",
        "Potrzeba {need} · pasujące szpule mają od {low} do {high}",
    ),
    "{need} needed · {have} across {count} spools": (
        "{need} necessários · {have} em {count} bobinas",
        "{need} necesarios · {have} en {count} carretes",
        "{need} benötigt · {have} auf {count} Spulen",
        "需要 {need} · {count} 个料盘共 {have}",
        "Potrzeba {need} · łącznie {have} (szpule: {count})",
    ),
    "{need} needed · leaves {left}": (
        "{need} necessários · sobram {left}",
        "{need} necesarios · quedan {left}",
        "{need} benötigt · {left} bleiben übrig",
        "需要 {need} · 剩余 {left}",
        "Potrzeba {need} · zostanie {left}",
    ),
    "{need} needed · every matching spool has at least {low}": (
        "{need} necessários · toda bobina compatível tem pelo menos {low}",
        "{need} necesarios · cada carrete compatible tiene al menos {low}",
        "{need} benötigt · jede passende Spule hat mindestens {low}",
        "需要 {need} · 每个匹配料盘至少有 {low}",
        "Potrzeba {need} · każda pasująca szpula ma co najmniej {low}",
    ),
    "{need} needed · {have} left": (
        "{need} necessários · restam {have}",
        "{need} necesarios · quedan {have}",
        "{need} benötigt · {have} übrig",
        "需要 {need} · 剩余 {have}",
        "Potrzeba {need} · zostało {have}",
    ),
    "{count} slots, pooled": (
        "{count} slots, somados",
        "{count} ranuras, sumadas",
        "{count} Slots, zusammengefasst",
        "{count} 个槽位，合并计算",
        "sloty razem: {count}",
    ),
    "Spooler: no Spoolman address is set up yet, so the filament quantity wasn't checked.": (
        "Spooler: nenhum endereço do Spoolman configurado ainda, então a quantidade de filamento não foi conferida.",
        "Spooler: aún no hay una dirección de Spoolman configurada, así que no se comprobó la cantidad de filamento.",
        "Spooler: Es ist noch keine Spoolman-Adresse eingerichtet, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：尚未设置 Spoolman 地址，因此未检查耗材丝用量。",
        "Spooler: nie ustawiono jeszcze adresu Spoolmana, więc nie sprawdzono ilości filamentu.",
    ),
    "Spooler: couldn't reach {source}, so the filament quantity wasn't checked.": (
        "Spooler: não foi possível acessar {source}, então a quantidade de filamento não foi conferida.",
        "Spooler: no se pudo conectar con {source}, así que no se comprobó la cantidad de filamento.",
        "Spooler: {source} ist nicht erreichbar, daher wurde die Filamentmenge nicht geprüft.",
        "Spooler：无法连接 {source}，因此未检查耗材丝用量。",
        "Spooler: nie można połączyć z {source}, więc nie sprawdzono ilości filamentu.",
    ),
    "Could not write settings to {file}. Check that this folder is writable.": (
        "Não foi possível gravar os ajustes em {file}. Verifique se a pasta permite gravação.",
        "No se pudieron guardar los ajustes en {file}. Comprueba que se pueda escribir en esa carpeta.",
        "Die Einstellungen konnten nicht in {file} geschrieben werden. Prüfen Sie, ob dieser Ordner beschreibbar ist.",
        "无法将设置写入 {file}。请检查该文件夹是否可写。",
        "Nie można zapisać ustawień w {file}. Sprawdź, czy do tego folderu można zapisywać.",
    ),
    "{plugin} - Settings & About": (
        "{plugin} - Ajustes e Sobre",
        "{plugin} - Ajustes e información",
        "{plugin} - Einstellungen & Info",
        "{plugin} - 设置与关于",
        "{plugin} – ustawienia i informacje",
    ),
    "Opened {plugin}": (
        "{plugin} aberto",
        "{plugin} abierto",
        "{plugin} geöffnet",
        "已打开 {plugin}",
        "Otwarto {plugin}",
    ),
    "Open the {plugin} tab once, then run this again.": (
        "Abra a aba {plugin} uma vez e rode isto de novo.",
        "Abre la pestaña {plugin} una vez y vuelve a ejecutar esto.",
        "Öffnen Sie einmal den Tab {plugin} und führen Sie dies dann erneut aus.",
        "请先打开一次 {plugin} 标签页，然后再次运行。",
        "Otwórz raz kartę {plugin}, a potem uruchom to ponownie.",
    ),
    "The selected printer preset has no host address.": (
        "O perfil de impressora selecionado não tem endereço do host.",
        "El perfil de impresora seleccionado no tiene dirección de host.",
        "Das ausgewählte Druckerprofil hat keine Host-Adresse.",
        "所选打印机预设没有主机地址。",
        "Wybrany profil drukarki nie ma adresu hosta.",
    ),
    "OrcaSlicer refused a filament slot change from Spooler's background thread, so keeping the slots synced automatically is off. Use Plugins > Run > Spooler: Keep Slots Synced instead.": (
        "O OrcaSlicer recusou uma alteração de slot de filamento feita em segundo plano pelo Spooler, então a sincronização automática dos slots foi desligada. Use Plugins > Executar > Spooler: Keep Slots Synced.",
        "OrcaSlicer rechazó un cambio de ranura de filamento hecho en segundo plano por Spooler, así que la sincronización automática de ranuras quedó desactivada. Usa Plugins > Ejecutar > Spooler: Keep Slots Synced.",
        "OrcaSlicer hat eine Filament-Slot-Änderung aus dem Hintergrund-Thread von Spooler abgelehnt, daher ist das automatische Synchronisieren der Slots aus. Verwenden Sie stattdessen Plugins > Ausführen > Spooler: Keep Slots Synced.",
        "OrcaSlicer 拒绝了 Spooler 后台线程发起的耗材丝槽位更改，因此已关闭槽位自动同步。请改用 插件 > 运行 > Spooler: Keep Slots Synced。",
        "OrcaSlicer odrzucił zmianę slotu filamentu z wątku w tle Spoolera, więc automatyczna synchronizacja slotów jest wyłączona. Zamiast tego użyj Wtyczki > Uruchom > Spooler: Keep Slots Synced.",
    ),
    "Stopped keeping the filament slots synced.": (
        "Os slots de filamento não estão mais sendo sincronizados.",
        "Se dejó de sincronizar las ranuras de filamento.",
        "Die Filament-Slots werden nicht mehr synchronisiert.",
        "已停止同步耗材丝槽位。",
        "Zatrzymano synchronizację slotów filamentu.",
    ),
    "Stopped keeping the filament slots synced automatically until OrcaSlicer restarts. Run this again to keep them synced, or turn the setting off and on to restart it.": (
        "A sincronização automática dos slots de filamento parou até o OrcaSlicer reiniciar. Rode isto de novo para mantê-los sincronizados, ou desligue e ligue o ajuste para reiniciá-la.",
        "Se dejó de sincronizar automáticamente las ranuras de filamento hasta que OrcaSlicer se reinicie. Vuelve a ejecutar esto para mantenerlas sincronizadas, o desactiva y activa el ajuste para reiniciarla.",
        "Die automatische Synchronisierung der Filament-Slots ist bis zum Neustart von OrcaSlicer beendet. Führen Sie dies erneut aus, um sie synchron zu halten, oder schalten Sie die Einstellung aus und wieder ein.",
        "已停止自动同步耗材丝槽位，直到 OrcaSlicer 重启。再次运行可继续同步，或将该设置关闭再打开以重新启动。",
        "Zatrzymano automatyczną synchronizację slotów filamentu do ponownego uruchomienia OrcaSlicer. Uruchom to ponownie, aby dalej synchronizować, albo wyłącz i włącz ustawienie, aby ją wznowić.",
    ),
    "Keep Slots Synced is already running.": (
        "Keep Slots Synced já está em execução.",
        "Keep Slots Synced ya se está ejecutando.",
        "Keep Slots Synced läuft bereits.",
        "Keep Slots Synced 已在运行。",
        "Keep Slots Synced już działa.",
    ),
    "Spoolman sent a spool list Spooler doesn't understand": (
        "O Spoolman enviou uma lista de bobinas que o Spooler não entende",
        "Spoolman envió una lista de carretes que Spooler no entiende",
        "Spoolman hat eine Spulenliste gesendet, die Spooler nicht versteht",
        "Spoolman 返回了 Spooler 无法识别的料盘列表",
        "Spoolman wysłał listę szpul, której Spooler nie rozumie",
    ),
    "Syncing presets needs Spoolman as the source.": (
        "Sincronizar perfis exige o Spoolman como origem.",
        "Sincronizar perfiles necesita Spoolman como origen.",
        "Das Synchronisieren von Presets erfordert Spoolman als Quelle.",
        "同步预设需要以 Spoolman 作为来源。",
        "Synchronizacja profili wymaga Spoolmana jako źródła.",
    ),
    "Could not read OrcaSlicer's presets.": (
        "Não foi possível ler os perfis do OrcaSlicer.",
        "No se pudieron leer los perfiles de OrcaSlicer.",
        "Die OrcaSlicer-Profile konnten nicht gelesen werden.",
        "无法读取 OrcaSlicer 的预设。",
        "Nie można odczytać profili OrcaSlicer.",
    ),
    "Already sending to Spoolman; try again in a moment.": (
        "Já enviando ao Spoolman; tente de novo daqui a pouco.",
        "Ya se está enviando a Spoolman; inténtalo de nuevo en un momento.",
        "Es wird bereits an Spoolman gesendet; versuchen Sie es gleich erneut.",
        "正在发送到 Spoolman；请稍后重试。",
        "Trwa już wysyłanie do Spoolmana; spróbuj ponownie za chwilę.",
    ),
    "Sending needs Spoolman as the source.": (
        "O envio exige o Spoolman como origem.",
        "Enviar necesita Spoolman como origen.",
        "Senden erfordert Spoolman als Quelle.",
        "发送需要以 Spoolman 作为来源。",
        "Wysyłanie wymaga Spoolmana jako źródła.",
    ),
    "Enter a weight between 0 and {max} g.": (
        "Digite um peso entre 0 e {max} g.",
        "Introduce un peso entre 0 y {max} g.",
        "Geben Sie ein Gewicht zwischen 0 und {max} g ein.",
        "请输入 0 到 {max} g 之间的重量。",
        "Wpisz wagę od 0 do {max} g.",
    ),
    "Used {grams} g of spool #{id}.": (
        "{grams} g da bobina #{id} usados.",
        "Se usaron {grams} g del carrete #{id}.",
        "{grams} g von Spule #{id} verbraucht.",
        "已使用料盘 #{id} 的 {grams} g。",
        "Zużyto {grams} g ze szpuli #{id}.",
    ),
    "A location is text of at most {max} characters.": (
        "O local é um texto de no máximo {max} caracteres.",
        "La ubicación es un texto de {max} caracteres como máximo.",
        "Ein Lagerort ist Text mit höchstens {max} Zeichen.",
        "位置为最多 {max} 个字符的文本。",
        "Lokalizacja to tekst o długości do {max} znaków.",
    ),
    "Enter the grams left, from 0 to {max} g.": (
        "Digite os gramas restantes, de 0 a {max} g.",
        "Introduce los gramos restantes, de 0 a {max} g.",
        "Geben Sie die verbleibenden Gramm ein, von 0 bis {max} g.",
        "请输入剩余克数，0 到 {max} g。",
        "Wpisz, ile gramów zostało: od 0 do {max} g.",
    ),
    "A note is text of at most {max} characters.": (
        "A nota é um texto de no máximo {max} caracteres.",
        "La nota es un texto de {max} caracteres como máximo.",
        "Eine Notiz ist Text mit höchstens {max} Zeichen.",
        "备注为最多 {max} 个字符的文本。",
        "Notatka to tekst o długości do {max} znaków.",
    ),
    "That spool has no filament to copy.": (
        "Essa bobina não tem filamento para copiar.",
        "Ese carrete no tiene filamento que copiar.",
        "Diese Spule hat kein Filament zum Kopieren.",
        "该料盘没有可复制的耗材丝。",
        "Ta szpula nie ma filamentu do skopiowania.",
    ),
    "Add 1 to {max} spools at a time.": (
        "Adicione de 1 a {max} bobinas por vez.",
        "Añade de 1 a {max} carretes a la vez.",
        "Fügen Sie 1 bis {max} Spulen auf einmal hinzu.",
        "每次可添加 1 到 {max} 个料盘。",
        "Dodawaj od 1 do {max} szpul naraz.",
    ),
    "Could not write the export: {error}": (
        "Não foi possível gravar a exportação: {error}",
        "No se pudo escribir la exportación: {error}",
        "Der Export konnte nicht geschrieben werden: {error}",
        "无法写入导出文件：{error}",
        "Nie można zapisać eksportu: {error}",
    ),
    "Spoolman could not be read": (
        "Não foi possível ler o Spoolman",
        "No se pudo leer Spoolman",
        "Spoolman konnte nicht gelesen werden",
        "无法读取 Spoolman",
        "Nie można odczytać Spoolmana",
    ),
    "OrcaSlicer's data folder was not found": (
        "A pasta de dados do OrcaSlicer não foi encontrada",
        "No se encontró la carpeta de datos de OrcaSlicer",
        "Der Datenordner von OrcaSlicer wurde nicht gefunden",
        "未找到 OrcaSlicer 的数据文件夹",
        "Nie znaleziono folderu danych OrcaSlicer",
    ),
    "Could not read Spoolman.": (
        "Não foi possível ler o Spoolman.",
        "No se pudo leer Spoolman.",
        "Spoolman konnte nicht gelesen werden.",
        "无法读取 Spoolman。",
        "Nie można odczytać Spoolmana.",
    ),
    "{text}: {detail}": (
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}: {detail}",
        "{text}：{detail}",
        "{text}: {detail}",
    ),
    "{text} ({detail})": (
        "{text} ({detail})",
        "{text} ({detail})",
        "{text} ({detail})",
        "{text}（{detail}）",
        "{text} ({detail})",
    ),
    "Spool {id}": (
        "Bobina {id}",
        "Carrete {id}",
        "Spule {id}",
        "料盘 {id}",
        "Szpula {id}",
    ),
    "spool {id}": (
        "bobina {id}",
        "carrete {id}",
        "Spule {id}",
        "料盘 {id}",
        "szpula {id}",
    ),
    "Could not read the spool list: {error}": (
        "Não foi possível ler a lista de bobinas: {error}",
        "No se pudo leer la lista de carretes: {error}",
        "Die Spulenliste konnte nicht gelesen werden: {error}",
        "无法读取料盘列表：{error}",
        "Nie można odczytać listy szpul: {error}",
    ),
    "Test the connection successfully before saving.": (
        "Teste a conexão com sucesso antes de salvar.",
        "Prueba la conexión con éxito antes de guardar.",
        "Testen Sie die Verbindung erfolgreich, bevor Sie speichern.",
        "保存前请先成功测试连接。",
        "Przed zapisaniem przetestuj połączenie.",
    ),
    "Auto Bed Levelling": (
        "Nivelamento automático da mesa",
        "Nivelación de cama automática",
        "Automatische Druckbettnivellierung",
        "自动热床调平",
        "Automatyczne poziomowanie stołu",
    ),
    "Heating Bed": (
        "Aquecendo a mesa",
        "Precalentamiento de la cama",
        "Heizbett vorheizen",
        "预加热热床",
        "Nagrzewanie stołu",
    ),
    "Sweeping XY Mech Mode": (
        "Varredura do modo mecânico XY",
        "Barrido del modo mecánico XY",
        "XY-Mechanik-Modus-Abtastung",
        "XY 机械模式扫描",
        "Sprawdzanie mechaniki XY",
    ),
    "Changing Filament": (
        "Trocando o filamento",
        "Cambiando el filamento",
        "Filament wechseln",
        "换料",
        "Zmiana filamentu",
    ),
    "Paused": (
        "Pausado",
        "En pausa",
        "Pausiert",
        "已暂停",
        "Wstrzymano",
    ),
    "Paused: Filament Runout": (
        "Pausa (fim do filamento)",
        "Pausa (filamento agotado)",
        "Pause (Filament leer)",
        "暂停（耗材丝耗尽）",
        "Pauza: koniec filamentu",
    ),
    "Heating Nozzle": (
        "Aquecendo o bico",
        "Calentando la boquilla",
        "Düse wird erhitzt",
        "加热喷嘴",
        "Nagrzewanie dyszy",
    ),
    "Calibrating Extrusion": (
        "Calibrando a extrusão",
        "Calibrando la extrusión",
        "Extrusion wird kalibriert",
        "校准挤出",
        "Kalibracja ekstruzji",
    ),
    "Scanning Bed Surface": (
        "Digitalizando a superfície da mesa",
        "Escaneando la superficie de la cama",
        "Scan der Druckbettoberfläche",
        "扫描热床",
        "Skanowanie powierzchni stołu",
    ),
    "Inspecting First Layer": (
        "Inspecionando a primeira camada",
        "Inspeccionando la primera capa",
        "Überprüfung der ersten Schicht",
        "扫描首层",
        "Sprawdzanie pierwszej warstwy",
    ),
    "Identifying Build Plate": (
        "Identificando o tipo de placa de impressão",
        "Identificando el tipo de cama de impresión",
        "Identifikation der Druckplatte",
        "识别打印板类型",
        "Rozpoznawanie płyty roboczej",
    ),
    "Calibrating Micro Lidar": (
        "Calibrando Micro Lidar",
        "Calibrando micro Lidar",
        "Kalibrierung des Mikro-Lidars",
        "校准 Micro Lidar",
        "Kalibracja Micro Lidar",
    ),
    "Homing Toolhead": (
        "Reposicionando o cabeçote",
        "Homing del cabezal",
        "Referenzfahrt des Werkzeugkopfes",
        "工具头回原点",
        "Bazowanie głowicy",
    ),
    "Cleaning Nozzle Tip": (
        "Limpando a ponta do bico",
        "Limpiando la boquilla",
        "Reinigen der Düse",
        "清理喷嘴头",
        "Czyszczenie końcówki dyszy",
    ),
    "Checking Extruder Temperature": (
        "Verificando a temperatura da extrusora",
        "Comprobando la temperatura del extrusor",
        "Überprüfen der Extrudertemperatur",
        "检查挤出温度",
        "Sprawdzanie temperatury ekstrudera",
    ),
    "Paused by User": (
        "Pausado pelo usuário",
        "Pausado por el usuario",
        "Vom Benutzer pausiert",
        "已被用户暂停",
        "Wstrzymano przez użytkownika",
    ),
    "Paused: Front Cover Removed": (
        "Pausa (tampa frontal removida)",
        "Pausa (se cayó la tapa delantera)",
        "Pause (Frontabdeckung abgefallen)",
        "暂停（前盖脱落）",
        "Pauza: zdjęta przednia pokrywa",
    ),
    "Calibrating Extrusion Flow": (
        "Calibrando o fluxo de extrusão",
        "Calibrando el flujo de extrusión",
        "Extrusionsfluss wird kalibriert",
        "校准挤出流量",
        "Kalibracja przepływu",
    ),
    "Paused: Nozzle Temperature Fault": (
        "Pausa (falha na temperatura do bico)",
        "Pausa (fallo en la temperatura de la boquilla)",
        "Pause (Düsentemperaturstörung)",
        "暂停（喷嘴温度故障）",
        "Pauza: błąd temperatury dyszy",
    ),
    "Paused: Bed Temperature Fault": (
        "Pausa (falha na temperatura da mesa)",
        "Pausa (fallo en la temperatura de la cama caliente)",
        "Pause (Heizbetttemperaturstörung)",
        "暂停（热床温度故障）",
        "Pauza: błąd temperatury stołu",
    ),
    "Unloading Filament": (
        "Descarregando o filamento",
        "Descarga de filamento",
        "Entladen des Filaments",
        "耗材丝退料中",
        "Wyładowywanie filamentu",
    ),
    "Paused: Skipped Step": (
        "Pausa (perda de passos)",
        "Pausa (pasos perdidos)",
        "Pause (Schrittverlust)",
        "暂停（电机丢步）",
        "Pauza: zgubione kroki",
    ),
    "Loading Filament": (
        "Carregando o filamento",
        "Carga de filamento",
        "Laden des Filaments",
        "耗材丝进料中",
        "Ładowanie filamentu",
    ),
    "Calibrating Motor Noise": (
        "Calibrando o ruído do motor",
        "Calibrando el ruido del motor",
        "Motorgeräusch wird kalibriert",
        "电机噪音校准",
        "Kalibracja szumu silników",
    ),
    "Paused: AMS Lost": (
        "Pausa (AMS desconectado)",
        "Pausa (AMS perdido)",
        "Pause (AMS getrennt)",
        "暂停（AMS 断开）",
        "Pauza: utracono AMS",
    ),
    "Paused: Heat Break Fan": (
        "Pausa (ventoinha do heatbreak)",
        "Pausa (baja velocidad del ventilador del disipador térmico)",
        "Pause (zu kleine Geschwindigkeit des Heatbreak-Lüfters)",
        "暂停（散热风扇低速）",
        "Pauza: wentylator heatbreaka",
    ),
    "Paused: Chamber Temperature Fault": (
        "Pausa (falha na temperatura da câmara)",
        "Pausa (problema con el control de temperatura de la recámara)",
        "Pause (Kammertemperaturregelungsproblem)",
        "暂停（腔体温度控制问题）",
        "Pauza: błąd temperatury komory",
    ),
    "Cooling Chamber": (
        "Resfriando a câmara",
        "Enfriando la recámara",
        "Kühlung der Kammer",
        "腔体降温中",
        "Chłodzenie komory",
    ),
    "Paused by G-code": (
        "Pausado por G-code",
        "Pausa (G-code insertado por el usuario)",
        "Pause (vom Benutzer eingefügter G-Code)",
        "暂停（用户插入的 G-code）",
        "Wstrzymano przez G-code",
    ),
    "Motor Noise Showoff": (
        "Demonstração do ruído do motor",
        "Demostración del ruido del motor",
        "Motorgeräusch-Showoff",
        "电机噪音校准结果展示",
        "Pokaz szumu silników",
    ),
    "Paused: Nozzle Covered": (
        "Pausa (bico coberto de filamento)",
        "Pausa (boquilla cubierta de filamento)",
        "Pause (Düse mit Filament bedeckt)",
        "暂停（喷嘴被耗材丝包裹）",
        "Pauza: zasłonięta dysza",
    ),
    "Paused: Cutter Error": (
        "Pausa (erro do cortador)",
        "Pausa (error del cortador)",
        "Pause (Schneidfehler)",
        "暂停（切刀错误）",
        "Pauza: błąd obcinaka",
    ),
    "Paused: First Layer Error": (
        "Pausa (erro na primeira camada)",
        "Pausa (error en la primera capa)",
        "Pause (Fehler in der ersten Schicht)",
        "暂停（首层错误）",
        "Pauza: błąd pierwszej warstwy",
    ),
    "Paused: Nozzle Clog": (
        "Pausa (bico entupido)",
        "Pausa (boquilla obstruida)",
        "Pause (Düsenverstopfung)",
        "暂停（喷嘴堵塞）",
        "Pauza: zatkana dysza",
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
        "spool_columns": parse_columns(columns), "spool_view": spool_view(), "progress": parse_progress(progress), "stats": parse_stats(stats),
        "display": display_settings(), "drying": drying_settings(), "presets": presets_settings(),
        "parents": parent_bases(_ui_snap.get("parents") or []), "cur_code": _cur["code"] or "EUR",
        "wizard": bool(wizard), "log_path": str(LOG_FILE), "auto_keep_slots": auto_keep_on(), "refresh_s": refresh_secs(),
        "rfid_skipped": rfid_skipped_count(),
        "save_calibration": calibration_mode(),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None, page: str = "") -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window).

    ``page`` is the settings page to open first (s-src, ...), as a "Settings" link in the spool window asked."""
    text_language(fresh=True)  # built on the UI thread: Python's own texts follow the same choice
    boot = {
        "mode": mode, "view": view, "version": PLUGIN_VERSION, "lang": host_language(), "pref": ui_language(),
        "low_stock_default": LOW_DEFAULT, "refresh_ms": REFRESH_SECS * 1000, "display_defaults": DISPLAY_DEFAULTS,
        "own_fields": sorted(EDITOR_OWN), "logo": LOGO_DATA_URI,
        "page": page if isinstance(page, str) and re.fullmatch(r"s-[a-z]{1,16}", page) else "",
        "settings": settings or settings_boot(get_settings().get("spoolman_url", ""), parse_low(get_settings().get("low_stock_grams"))),
    }
    return fit_webview(ui_page().replace("__BOOT__", _json_for_html(boot), 1))


# OrcaSlicer on Windows shows a page through WebView2, which takes at most 2 MiB once the page is base64-encoded:
# 1.5 MiB of UTF-8. A bigger page stays blank (0.30.0's tab was 1,573,958 bytes, 1,094 over, and never loaded).
WEBVIEW_PAGE_LIMIT = 1_572_864
_FONT_DATA = re.compile(r"url\(data:font/[\w.+-]+;base64,[A-Za-z0-9+/=]+\)(?:\s*format\([^)]*\))?")   # local() takes no format()


def fit_webview(html: str) -> str:
    """The page, without its embedded web fonts when they would push it over WEBVIEW_PAGE_LIMIT: it then draws
    in the system font instead of staying blank."""
    if len(html.encode("utf-8")) <= WEBVIEW_PAGE_LIMIT:
        return html
    lighter = _FONT_DATA.sub('local("Manrope")', html)
    size = len(lighter.encode("utf-8"))
    if size > WEBVIEW_PAGE_LIMIT:
        log.warning("The page is %d bytes, over OrcaSlicer's %d on Windows; it may stay blank", size, WEBVIEW_PAGE_LIMIT)
    return lighter


def main_html() -> str:
    return page_html("main")


def settings_html(current_url: str, spoolman_info: dict, low_stock_grams: float,
                  plate_check: bool = True, plate_margin: int = DEFAULT_MARGIN,
                  weight: str = "both", cart: bool = False, source: str = "spoolman",
                  progress: dict | None = None, columns: int = 1, stats: dict | None = None,
                  wizard: bool = False, page: str = "") -> str:
    """``spoolman_info`` describes the saved URL, not whatever is typed in the field."""
    verified_url = clean_url(current_url) if spoolman_info.get("ok") else ""
    return page_html("settings", "settings", settings_boot(
        current_url, low_stock_grams, plate_check, plate_margin, weight, cart, source, progress, columns, stats,
        wizard, verified_url), page)


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

    def _open_settings(self, page=None):
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
                page=page or "",
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
            heard(BAMBU_KEY if src == "bambu" else url, info.get("ok"),
                  (info.get("account") or info.get("version")) if info.get("ok") else info.get("error"), sure=True)
            self._testing = False
            if src == "bambu":
                self._verified_bambu = bool(info.get("ok"))
            elif info.get("ok"):
                self._verified_url = clean_url(url)
            if window.is_open():
                window.post({"type": "test_result", "source": src, "url": url, **info, "requirements": requirements()})

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
        if msg_type in ("ready", "requirements"):  # Check again: the same test, counted at once
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
            save_refresh(data.get("refresh_s"))
            save_spool_view(data.get("spool_view"))
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
        elif msg_type == "spoolman_help":
            open_url(SPOOLMAN_HELP)
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
            self._open_settings(data.get("page"))
        elif msg_type == "order":
            open_search(data.get("query"))
        elif msg_type == "printers":
            save_printers(data.get("printers"))
        elif msg_type == "live":
            self._post(live_message())
        elif msg_type == "rfid_skip":
            rfid_skip(data.get("printer"), data.get("tag"))
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
            start_send(self._post, chosen=data)
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
                            "spool_columns": spool_columns(), "spool_view": spool_view(), "source": source(), **printer_state(),
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
                    start_send(self.post_message, chosen=data)
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
                                   "spool_columns": spool_columns(), "spool_view": spool_view(), "source": source(), **printer_state(),
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
                "spool_view": spool_view(),
                "display": display_settings(),
                "drying": drying_settings(),
                "presets": presets_settings(), "parents": parent_bases(_ui_snap.get("parents") or []),
                "progress": progress_settings(),
                "stats": stats_settings(),
                "cur_code": _cur["code"] or "EUR",
                "wizard": wizard_pending(),
                "auto_keep_slots": auto_keep_on(), "refresh_s": refresh_secs(),
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
                heard(BAMBU_KEY if src == "bambu" else url, info.get("ok"),
                      (info.get("account") or info.get("version")) if info.get("ok") else info.get("error"), sure=True)
                self._testing = False
                if src == "bambu":
                    self._verified_bambu = bool(info.get("ok"))
                elif info.get("ok"):
                    self._verified_url = clean_url(url)
                if window.is_open():
                    window.post({"type": "test_result", "source": src, "url": url, **info, "requirements": requirements()})

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
            if msg_type in ("ready", "requirements"):  # Check again: the same test, counted at once
                self._check_connection(self._spoolman_url(), self._settings_window)
            elif msg_type == "test":
                url = (data.get("url") or "").strip()
                self._check_connection(url, self._settings_window, data.get("source"))
            elif msg_type == "save":
                save_display(data.get("display"))
                save_drying(data.get("drying"))
                save_presets(data.get("presets"))
                save_auto_keep(data.get("auto_keep_slots"))
                save_refresh(data.get("refresh_s"))
                save_spool_view(data.get("spool_view"))
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
            elif msg_type == "spoolman_help":
                open_url(SPOOLMAN_HELP)
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


def parse_refresh(value: object) -> int:
    ok = type(value) is int and (value == 0 or REFRESH_RANGE[0] <= value <= REFRESH_RANGE[1])
    return value if ok else REFRESH_DEFAULT  # type: ignore[return-value]


def refresh_secs() -> int:
    return parse_refresh(get_settings().get("spoolman_refresh_s"))


def save_refresh(value: object) -> None:
    """Save Settings > Refresh Spoolman every … s on its own, like the display flags; other values are ignored."""
    if type(value) is int and parse_refresh(value) == value:
        update_settings({"spoolman_refresh_s": value})


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
UI_PAGE_SHA256 = "050a36164a8aead6539a412c808d5ef360f7c678406faba88e755ce99ddae59f"
UI_PAGE_BYTES = 703350
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
