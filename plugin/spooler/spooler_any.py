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
# Change sets waiting for Save or Skip on the page: {Spooler preset name: {setting: (new, old)}}.
_calib_asks: dict = {}


def parse_calibration_mode(value: object) -> str:
    return value if value in CALIBRATION_MODES else "ask"


def calibration_mode() -> str:
    """Save calibrated values to Spoolman: ask (the default), auto or never."""
    return parse_calibration_mode(get_settings().get("save_calibration"))


def save_calibration_mode(value: object) -> None:
    if value in CALIBRATION_MODES:
        save_settings({**get_settings(), "save_calibration": value})


def calibration_asks() -> list[dict]:
    """The change sets waiting on the page, oldest first."""
    return [{"name": name, "changes": [{"key": key, "old": old, "new": new} for key, (new, old) in sorted(changes.items())]}
            for name, changes in _calib_asks.items()]


def _calib_mark(changes: dict) -> dict:
    return {key: new for key, (new, _old) in changes.items()}


def _post_asks() -> None:
    send_plate_message({"type": "calibration", "asks": calibration_asks()})


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
            target, changes = edits
            # Skipped values aren't asked about again until they change.
            if (get_settings().get("calibration_skipped") or {}).get(target) == _calib_mark(changes):
                return
            _calib_asks.pop(target, None)
            _calib_asks[target] = changes
            log.info("%s was saved from %s; asking before sending its changes to Spoolman", name, target)
            push_notice("info", tr("Spooler: {name} has new calibrated values. Open Spooler to save them to "
                                   "Spoolman or skip them.", name=target))
            _post_asks()
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
    changes = _calib_asks.pop(name, None)
    if changes is None:
        post({"type": "calibration", "asks": calibration_asks()})
        return
    if data.get("type") == "calibration_skip":
        settings = get_settings()
        skipped = {**(settings.get("calibration_skipped") or {}), name: _calib_mark(changes)}
        save_settings({**settings, "calibration_skipped": skipped})
        post({"type": "calibration", "asks": calibration_asks()})
        return

    def done(result: dict) -> None:
        if not result.get("ok") and name not in _calib_asks:
            _calib_asks[name] = changes  # not written: still waiting for the user
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
        return tr(DRIED_NO_VERSION)
    if version >= SPOOLMAN_EXTRA_MERGE:
        return {DRIED_FIELD: value}
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
        return {"ok": False, "text": tr("Unknown spool action.")}
    if source() != "spoolman":
        return {"ok": False, "text": tr("Spool actions need Spoolman as the source.")}
    sid = _pos_int(data.get("id"))
    if sid is None and action != "locations":
        return {"ok": False, "text": tr("No spool chosen.")}
    if action != "locations" and stale_list(data):
        return {"ok": False, "text": tr(STALE_LIST)}
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
        error = _spoolman_error(exc)
        return {"ok": False, "text": tr("{text}: {detail}", text=error, detail=detail) if isinstance(detail, str) and detail else error}


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
UI_PAGE_SHA256 = "ed1f43018c622d5c94543d4e2682b267f1ad8528eb3b1107e79ef8ea03451742"
UI_PAGE_BYTES = 1216649
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
    "L8quiaUyeZJt8ZBZNUyubjQuJUAxqYucaTtVN58/VpajOgpWQJW1cWLECyOSnlus78582L1xPjkzN/AT6Jmhb2lL8W3TIe03zqV4"
    "2apoXN3zN7pvvoEv2Ue/6Ry/pXVo9oTcdNyonifrhOR03Nxhj2TcPAiM1n3r0+6przpXzi+YhJsDYSSk35bnf7IdYxYdTe9V0BeO"
    "66Bti5FLOfP27KkvMYzU7bt8KvkJFV/W7l/iqyG2YkUH2DDHovL43KkeUin9dsoGNnNmsd4k1bZSzBi+iGLWKIlU2/TYPcb7Erag"
    "c/ZzuavpiY45qIhZtZtem5fKJzB+zZq02r0OfBxUJrG2XCavH+2c/SYhsTY3dciVnVh7YRKTuCgrp7b2xoon1Y6xEk5W7V5k18mn"
    "rb3Z4um0eVVJ6bQjPEqP6Vj5tG0hn25kMlulK9kkp7WzaMsJJhExnkS7c+MeHAo0O9m08/nk9NkpE2fRzZst4VzOnpn/9DhKofQO"
    "On/h+vxH70bzZYvUrUKQ2Kmyxfnr3BswlQUyZGMsq4gDk7ygnH0XgLhA2DN+9BMw6EdbS7ae+/gIR9DgMH2CPJHk2HbISWeyJh82"
    "Lw+J48Xb+N5/+AQqfUgJbbfTHn9mIOOMa2J0UYg7N9010iWLfdUgkJCJ3301e+Kvc/c/xRAZb6L5R/edOzM//uT0ZCW2trtiJ1G0"
    "Fztyim3E3HzWM/dfhysEwzYQkrMdg76g7PAAeGdob0nxKRapzbiYWje0AYLJZY37du14z0zWfFXa1uJimXL2BrdEe5a7F0XZj25K"
    "nwKqqpiBrySnqWZfPop6dIqm+DZ6X77/Gq+KeTPuPdbFpmRfeYbZ0pJTL6HRdvv1ZLHKkpO6c/ZTdW1wvEE3KTX3YuhWPCW1HLEz"
    "V2ZPHGPJxd5rFc/jrsRIjaejBmD2SkY9+96PyBgz0xJLR81hKaPpqCNRGuP5qAUprHifkUPiTFbYozNvQ49OPurO2dPmk5OJevbz"
    "C52zH8/9+Ors56+J+R7VRdXH2XcZceBPck9BC7W5Gy8zA9K9faT73k2+uQ0GmdTTPL3EzNO2yhK5Ik3D3MCkkTCkSWmnI+BJzj0d"
    "7x9NaSx6mZiFmsOLoXU0214Ai3H+cvft42L8fPbzXjYZ1mxV7mnxnSaalJRxWi8j4rGuNUPd80huycf1r6xHY3dk8t3/nD9KFDN0"
    "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"
    "u7WUSKxhIgH+kYsK15TXC1hFhpZYLl8EGngStHvaaT4ClzG8uq8YJcwUeq7sB1TnXTwD5KKfw6SMhL+l4yKfQk8hpb+Q16tQ8MG/"
    "vEH4Y3rzxs9K+PXkpvfoZmvTh59AdKczkK24hXsPOmUyR8epAzEfaWCnYUKLeu3G4qQG1zUZ1Wkf8E+mRiJZws4ave7pvezJ9sST"
    "/H/Uvdey60q2JfYt/dYVqAh4ELhXVx3wHoQjnKJDgvcehOvofxf28afq1I0OSS9ae69FEgATzMQ0Y4AzR/7tj2P+h+N/+cj/44fN"
    "/nzW7X//bQHlH3JA//H7csrFY20/Xyro78t//CLx87d/H/637d8HAPjb8n8M//1xyOE3Oa7lJ9VM4bcc/8/5/XD/6TvEHwLLP77O"
    "/VVi+ee56c9j8nMl/8+qzf/2p6z/f/33p5kfBvFv/+Mf0da//Vat/+tF+fuP773/Ig9l/+efkcQvy439YdPz3uOH9O6//Y8/H/lP"
    "esL/0NR//CJT9PNHl/+466eV0ftf5rf809pZf3n8L7rV/8uH/+yiD0j4qQjsrxSpf/0u9ocH/KQj8rNq3Q9hkX/79dnffizL+tOt"
    "/PMZ5V/vP/2i3f8zQv6L4fuHgfgXalb/83/+XFP50xX/V1rZv8nB/b6G23/5k7zaH5d6+Asc/ldbfy3x+ZOO2t9/kXn9GWb+t7/q"
    "x88bfweUfxyGXzQ8f8eS/8mxv0li/bn14V8LJ/+Xn1bn+WUx8x/Lqgz/7f/4Taa4/SFT/PefpU1/OuC//+3f/vjq3//qbL9Kfv2j"
    "zf4X+E+K53/pdn//q3f+7Vep9P+1S/AHmfXl7/kv0of/sPEvtdfzH67za4XNP7ngLwf/Ejzy3+UD/sm8/j78+x/f8XOYec75hL7/"
    "+os1/Zj+9JPw0N9+ERb4beG97edMNfx0hr9wwH9y0p+XHKx/Fvv4r/+46c/x5j/+cnj/pE3+Uy298SO6/gvNu//Fq/B7O78o8T09"
    "/vHyxyoXP7v6X+tl/r/wsz+JNv6jC/wqjviLE+a/aub97kfjrysT/eSzP4Y/+9eyb/y/FCr8y0j2r9QL/58JE/5ZJO43zbafamj+"
    "zXGf/fLvGmG/3nr4XWHrH1zun4S3/qA1pv0mGfbrVLxfqrN+b/RfKbv9Jpf2lyJvfxJL+9NkvF8V0P773+0/CZ3df3z1O3Vj/pU0"
    "2K9SXj8Jg/1cXvSvZLn+WX3rtxLnX8ubf1Xl+q0E7rcbOvHvN3T+anx/1NT/gy3+LnLyT+X0f5A5+eMU/p+mSP88I/p36a2fyg7r"
    "P0js/Kqr8/Mk2N+rmP40GennN/xZW+f3KeZ/UNP5tWj1l7XZfnhy/LtX/2bmv3f/D4I7/6k01l+JbP2FFtb/ugjOv5TJ+v+XVNQv"
    "aOU/VYr6+ZhfZN5+ev7XhZz/aL2/XPXfpxpo7r+co/jDZv7CAX7a/Jv9/6NZ/uUUgt9v5f3trz7Sbzv/utU/llL/qrzxT0b3Z4j4"
    "T672D9O1618mXPwc2H8911+Uq/92gv/2jzokf55bUP8y7+OfOvdnyZg/9us/U9n45w78ev71r0v7/78+/x8qcn+qmr3dnx/tXx5l"
    "92//U/itipb5uYrWc//jpzb+re7jMgePPJn+PYnXnMD+/mk70f5GIk0zgf1RLK+jMZ8e6efH+vHHPPiffq3PaTlvPXk22cwAjiC8"
    "BdgOFt+J0aiSR5PWOm3nrq23UIo05LvWYeyzE9axqIx+lVOKFq79Z6nSjn9zrj2q8kcHHXV0rDVq6On4OnR/0zpL6qPzCed24luN"
    "cbNLibeeRGBfJ0FUzuAl+ZC78ZJwbJbZlAMpEASB5y/uFn5R4MlXk4ASBL0IRdPVFxYoidlG84uUNP3xCwlirnVediSFS8JAnIBH"
    "X4j9/LJQMAhww5EMEAFfXCyk+5bbNB/JNZvEelV8kQ9vzyp90aztetCXZ5sBqNXj5FnuTUUz4MOaxnclfX+F1AMGTeqwXeo2vIcH"
    "NdWOrBX1vvZ9skJNfz3XVVCYXKG7cyTQ1ljqOglCsO9kNspIq6oDlV+z9wYv2kv3RL1gEka4qpHn3C8c5wgMnGjz7rDvkWHROSnR"
    "/go+xzGatW2Lb+0Z4lqGl+WYNfbldKxH29ihBQ3nBZZpTg5T0AKip0Z2yj4u6B2ULRtlfOq3cOSufA/vXjTNNKU7OyqEZYM2oi5g"
    "J43BG0bBRZ1cfbjGmaz6s0++wymh1PY6oTRvFisFioIqwHQjxc+doDCpDH0P5pyLhWIOEEiwq16CGhr0fCwjTpNtKEGKgtKhnBLu"
    "rV6x2XCQ5qv8SJLLhAxIG/XjcTlNihhb53++6uck13GneJgXWXvRPodIkPt9Smt59IOK349pUrhWUvppKWEdvk8XxYc6Y3pdi/zs"
    "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"
    "zpqb0VmRr3Lowne2kHMN2LS+onu2Z4qfdpcTP+3+SOKnXVv8tPcji59Ov434aW8Z8dOjuxU/7X0X8dOjovjp9zsUP/1uiJ9eesVP"
    "uwvETy/1XWX3zsVPu99f/PSrNudd1zTUlDO98ln2crRAk7JqkMc1dSxqH2I8Xkoit/E7GawOSLlR5tj9zqPUPE37sL9PScYkjXy5"
    "m9jlU21xk+CwlSiqu+hrLY7SILqH4TOS8kNr2psuOLSmpkGmSkSvU9DzcEzZFk/atQRuoCUwTU/zUQB1I/5KWpAOapfu1PLaRlNs"
    "YIEyykroQlexYEp8R5wthlshSEI/oTcojDE4wVjBpnQCxDihYb4m4gvFqbNfyqjKfSka66qYZ7akLxd2CKnHZFuI/KT/tzTNlvES"
    "lPmEeuh6IzZ6vOQtyC4bVSe9TaClXwe0CmCVAYmlk7+aYQzmT5Sc8pUhp3y6HJf29Efi0p7aXNrzH5lLe/FtuLTny3Bpr++WS3v+"
    "Xbi010Uu7Y875NL+MLi0n71c2tMFXNrPmkt7eudc2tPvz6W9U7JdPj+f0hZdPnYIb2kdakM8066ER1xypIa6whle/M+mo8QIz0H0"
    "LB6n+Xo8GtkFWXI2/Wg0THJQjJCNHQhDfxVfg86cqoAA9MYfAgCFB3Bsjsaz80n8paoRNAGrCogA/A1NclF0AmxnT8CnKoPzCdqf"
    "wqzZynNBzUcIl6VqvpRjnC1qcjRa2KCasBTTlAdOOIs/P1brO/ObZTbRyxjXWzhri1oymEchLghWZXPVfWEYu8wXzDde5wtah+t8"
    "QMtxnQ/QLvhaHYxG1/3kNW2p635FU7/uR5WBJESVN4D+yeJ6uOPMoCHeLaWrLogeIoCdnl9YAS9KaxZDapQqscRDiW4J3VeAvrwb"
    "z8Z0rjVkG2o7Wi0r+iB0YOJzroOBX9kvCpo5k/Fb94FdSXIR15erUz7CF+MZUO+Em1qgl/J9t7bWC37+VJseHwcD8V45WpV9w5Gb"
    "Q6sCnJfHI6HPMstlrXSPn5+NR0mAugCP0bWURAsUEnoU8XQgHuAsOLQsEj3vd5KaPKL6IpWtsxxK50vk6qB+WFO0LjI/kCvV0y2G"
    "XX+LZYPRLc/tKB0eG23NsgOPe/tG2nPkUJY1a07LzZrTJcya0zsza4ZRMH+jDyBfAm5Xo3Ay/nAyQXNl9GoR/ZKLr1pS5WycsKok"
    "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"
    "CHkZJbkSJGs0dhI/iZ/SrH3VdlL7sbhNf3dUW0O/T9hvEI+murOO3t3raG+6ZoX246hu/L9YeL2PiQQ6Mkfvge2G/xwLLcWpCq6E"
    "PtG+KP5zEl3/77AXUPu62jt9mujjVYrujZ+21U2hq10I2I0UZDhYmP1+/Cd04OhQ6UVPL8uDdCYNf/LVUTpTwI8xC35XjtLpeqae"
    "3vznclTuHOUX3dFV+qCef8w0zLKZmaQPGrHbTDM/SA+zD/O7zEUha14OK4XL7OVLbvWYvoin9VpOzyxKQ1RzJpvOD+8GV4XMvLFY"
    "Ne3JYavSGXQnB7OYqr2kV6OyNqx1rYvVRfr0vvW2vO4fHFQal5Vy661w9ZCd3txGhovLerF+Xb9s2JHV8ZH5aid7N8VSs1I8cXq9"
    "h1pkdHzaSXRi6XJ6cTnIzZcdY1ae1Y6OXnLxfqSebM6q6ZOleX/ljEaa0TLqV9ZbLevczCP1ea+iJ+zT6mPTHKbNpv6aj8Rib/Gr"
    "+otVG2YPC4+l4rhypd6s7lrVYiE5eYsfG9eJTOkilxvZuWn98iGzeJmYtZh+W181piPzNK/ejJLNudo7smqR5GO93H17HY61cuXw"
    "Rr3qRq4iB4kX6y3+mMhXsuOL1evLaFDPxm6G9cdmL39vRmfDknl4Ml/Y5UTEvEsYtcLbxWJyhOhkY5qvNW7Ti8byYnyVXo6K5SPz"
    "3ppVLDV+mTzIN7XlrDTvHQziS6t/eOVkx5n6OH1xm8sfv2kJKzHsPiaco+qbkWj2eqPOW+00GZlE6mUrc7MaD/P3k4Pjw5lx3K9O"
    "jVY8X0k2H2MXmUSs0mm1jvpdLXE0P3is6MdvJ72Th8rd7UNtlb1/yFyWLi6zai0ZO53Hy9fl+eTmJrd4mD/00mMtfavFbrvDiFks"
    "jI+H1UK6W7i869wU051aI33RqhzfF18vO879opquJQardLz+dli76B8bp41O5qh/12perQ4OW4tB7HLUuJpc3WQLq8KF1nuIrvLl"
    "SrmSX8STB8nosXHn9OpzdTmtqw8jdRQ5qc5Ko2J6UUoXK7fZ9Nv1jZmxooX86TLR6enL7oO9WKmN++x1YtY7SA47q3r29aBSRINV"
    "6Q6KiYdTPZNMVF5fDhJOPXpQO6lVHtL6a204Ll5lJke14fVtvXy0HKtD9fqtOE+ctPrLai5t3hUyrcxVqX6l5S7S43RptZjlZjfp"
    "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"
    "05vDYuyueF9v6seFofkwKeXur3v16LDy2mwUy3V1fDHIIB7OVHO3g7vbXi93cZnLOpH+6dVFH1HexeFL8k0vXY1e3u6NWfZouCq+"
    "HF6Nc68vi+Jhqxtdvd4gtjn3tjg0tXx23OzfnN42+/ZqeX2panfJEz1b1DN5dGHqza1q1VocGJe1ZvfkZGxWa8nTWj6D6OlN8u5x"
    "eFIr1V9K16vkw0n/AN1YHvVpYfhaa2RyiNMZont6thbpHCS6q8e7qwPEc0cHy/lwury6Kzhz47B1N3xJtu6y2ltm+ZZIj4ye9tKY"
    "opt2a6Z1eycXjoPuua1V5OS0Mmrp15PT05fZoPFYmZSarzH1/qDTe7NeXicz7fKgfDBs9rVxJ2MmW73uMH6XbR0Py+VVLH+RK2Uu"
    "xqPLaTIzLj6sspmJqibvMo8XZcQq5RrlVTd9Osu+IHb1KtG6qurRg1Z32DJmudGiP8xlC+XiY7F6eJfOJS4Pms1HK2r20ZVmUB9c"
    "nxSbrYfD5Osy0z8YNMy34UV+1DKLjfHb6WttmjyolBLD287ba8PUXlqN3GnzthmZzSMvtxeLxM3oxS7d3gyty3jv4uBgMhq8zOYP"
    "j5a6uDyYRquRUbXxtny5TpTjb3nzMH1de7SvR4fl23Ta6OhjZ/5YdfSY3bk7cCw1G0s3S7F762ZQPXq7WsTV2IEebTadqvYSqQwn"
    "r5eGHX/Ix0b9WmFZu1lU7idF6+Cy2XocH7xcJEqxRPLm9C06nd2iq6xeTua6h8cHnZt5ZHhxg9acertIF6xxPJZfJh7jmZdMfTbK"
    "Fi+u1ZHWNDol87i6fLgfv8aPzGR8ldOGnVb2OOHMmovJ9OQtM59YF71ur9fvtszJ6+1JcmkczBY35t10efJQqk3LN7PH6Th6O+vc"
    "v60Wt7eaE1WNyrB2akejlWOniPb3Q76V0Irq2/9D0VkrNghAUfSDGHAb0eDuGxbcg3596dihhcB7956T0DY9of+Jef6tq5DEWh65"
    "pUvoXti1+ZIJyAsivP0EtfRZVRcODuJUVYnS86Bp2v6rlL8tlWfY4u5MBOzJRVud9y+mXTW5gXtwYggcxJOwSaqoW/tTbsmaXTz0"
    "Ww+Csf0gfVeG0SvN0PbmThtTcrMS3sXF4p1jST4MembZ+c7dab9OAEZfsyOoE094/5OcOJCjQGdK71W/8dDzg44Is6pU46TWj7Ia"
    "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"
    "Z8FP2MY1LsK2ABt//s//DyDsNeI="
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
