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
# Units of the calibration values Spooler has its own Spoolman fields for, shown beside them.
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
            asks = _asks()
            asks.pop(target, None)
            _save_asks({**asks, target: changes})
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
UI_PAGE_SHA256 = "24b06aa2cb3a8d1ff0e13c068b6a40e9ac17158f9a8a6ea05a08be9c29d7c5fe"
UI_PAGE_BYTES = 1220494
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
    "/RbhjF79lcMZPf084YxebRLO6PmXDWf06quEM3qetVVffEFb9YVmq/5ktFUfr7FVf4rVwOMvbqs+/vq26h8nKkooaBv7Q+8W969e"
    "Yg67rB01GxXTs+e/e+oMnX6wAgM3bgZpT0bFLertbwjYzcI5WTjn2DqWV0Y43uvq+Mq+dk039rdkbubGp1XoVlx8nTUqD6K5fr91"
    "ivLrEPc25lHyfTqeCr4TRzCUbMjcho0b5l6lN0d1i+5DWe83fYo3SfHTc7X9unn5eIs2c3nmfLTyxsrucaTpZNzup+qmu57hcV07"
    "2PXOCt1RzpSt62XrxrJ1Onc07mX2nj/knPD+sNXx7lmviJv2ZUwiA9Ii/+5evFevDvTiHve6876D3ix13nfUG2jnffFA70w/7zvs"
    "XWnnfa/ss57X/5C+CmNH8ZlXsJ7GuNxU12AmvQ/qdKz9QZ4PApUmjngTOBgKT+koT5C49nImr71c9j5k7rzYcTJZoNA9MOIm/SEi"
    "p50Vjvg6s31pdbkJbuXMwmsn6iXfQrn8fFct7nzgMr6mIbusMI+0WxbP5UWFML5fIY5QiasMGoR+lUG/aGLwcn/as6LGWwXTzK0C"
    "zCQQ8t2AgO4ExEEs+uWj4Ljfn8aH/9UhWz5au835/mne+f6pdr5/qk6Vm07BfVq2SBJR0GcLQmZlYlL4qXscWQGYlHTytrTp1gKS"
    "GKc5H6RMkz9KX0wYg1CTFxP8dVJq1hunpBTILU1KodQa61LqqjfSpNQIpJZXjNKDekYvk7cShtqthDPTrYQzq3+mbicMQMzA2vGs"
    "f5USM768XqdmJV+sO5MmO7Scf53gKwoXs+7+Qox1EFsyrB+UrzI//NDnsVWMM26LC1GsnJiZaS2Ml121A3NgMIgjeYGm0YONzt55"
    "y4MPmRCdIMMs+0M2ioL+PhueTH41xjaLMC3A/ZjqhlhMOQ0usU5jECi9PtvbIBKUZIA7jK+34fge0AikYl/4IvbFm7Ni0dMCa3ha"
    "IoV0aA0MSGVRRKpgTUQqLXaYZynovvYSg4XB2iaITwdrYTlo7RpYaeymK7CbathtGVzMo7PUq+I9fbm5SPGM9HN58fHqomVJc+E3"
    "mHvaEoiW+NryD+3qyBA1xBeRnCxLi0H1IRuACgxOuo8y3TAIlXSBfjssYnxRw5AGsmU9LhVJjlTkE7ymt0lQqjFX6IEEioNSzdC6"
    "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"
    "pHlVbQnsoZLole2jqJSZVHmhC+qlFPGeGrCw2ZNvTLgCxU9NPTFaoJsYLVFMjBZqJUaF7p1MQ/tR7NtMfsou2FS6+PYqTyVq8ipv"
    "WKLs83gyzbmobKxIqtzMpCdKiqkON5fmkpuL7rOSY7CHmi9L8j+GxB9aaa3ZivJZJloylCixsJ5Q0psssulbwYHOP4iVBTjaa8Kh"
    "3IwZI8JUelLLTzr3aAi9hFXaGZMfofxk5x4NSc8mekvJBBrprt0IuqysRD2S2Nld2YwWEkq2I6LeijnKT/YWNmIPl0vt2G62giDr"
    "0p6CPPlSWTLj815RIvjUqI/2dVzY3Vb9jVMrJTpC/IBBN3z1VOVLQiF+yoY1k1q/ZMrqKxVcX9/46lNscPWtbWSVVuxbjS0yN4WW"
    "QNtgOSMTGuoG4ogYKxkOnmRGNBlfeN0x6nn8G/3nbDQs50aZxAhPOL1Q+sTxlA5BT9Mn8AyTP6a3hqWgEZNXr0kUHBbFd7RZ6aSi"
    "nx4d4p9gQuJpj97G5Jeec6wBY0v+wnPQ4iKlF9ocp5CwQHCV8iemHQtOS/70pAJ/L1S6/F41XCmNopzoaU+/of7uq9mHolyyF9ZL"
    "KZ70UaMVKSfprWRmE5lXsUA1CwgcaBYhvVA3MvHMMK60LMwkJR7EmuJyUnp975Ghf0mpwIuynxY8ycOyJosYms93RMZ6Gj1jholK"
    "yGNzfwkplcUcZWnz9Gw8lOdtY3lNKFqq/BbZZVW9ubw6FS418C6ZDi/DeNQTZej7WTziXEApHeIiEz7xfNZcjOq56vwuvK3Jw6XZ"
    "WjGw0pErksR522yvrq2dsyJFHrLNzura+uEqkhAnUHlndWV2LqY7eYN63VX11GFMSKdVBdV2Vx+gslowihJ18DbXOHnx4KVai07v"
    "5v56jRind8lAENi9ZYtYL+ssMBKEJpprNCHLO1ZDQWiktU4jVNqpGgtC/RWrrjQM3Z4PKndWVz421pwJ+87q6hromu2WThPp8mGz"
    "lsNWKqlr8WE+Px0XnsjhTJcnua4NqJ/V5tmsDmT9fLWetcbhqh+ntoNTnZbqiFTnouUI1E698hlXOdCME8zilkw7n+rmYVRXh1FZ"
    "A6xePlHqBjGu68S3blLbuja5tmlUcwfT5kuD5Dq5elWc3xNk84jBOzNZu8Cw13BoCjJXPXwJF+GEZ9fC7JlX63+yfv9k/f5HYP1K"
    "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"
    "rcgEe8Dnxex/I6Qimfg/16gA86//Y2npnxihdmnodPc+4eOo4zj+p6XG0BuNvKHbdvt/pYee57+srmLmII8wjJ9KtT5A6ZO1NJqN"
    "fKdHVsFaWiWtd51VWmIt7Xfd/mOp1qji7zz5zlr6VHXanrN0WYAva/0R2S9Dt/WNNg1ZQdLsL8aQgPr5pRL5Sap/ytVGDXJ/13hB"
    "yel3PWspRwgij+wLa0l8x9oDDLn6NEqnUoMntWjUS6fW9aJeM53a0Iu67XRqSy966qYheK9atA5lO3rZBinblPVGqfSm/LGelrVH"
    "G+pARpvp1Lb8taX2NdpOryuN7KQ35HegkRmPYFabgbL0drASmdROsIyMVhkF2X0+Oe9qB6wIelhXBtipNcE0CVBCOrlEYLxEPln6"
    "t9ROanOjkdq0lpJLZEBLKaU02dQ/9si9Bikvk7TWBq2aTO2s76zvsqqt2shPJ1LrI/a7Xhs55PcO/w3i0XRjXHcbq3Xn2XWGscQ6"
    "6Rv/n4rPE4gkyJX5+GIcN/zPH5KtOKhBKKF3jC+J/+wk5/8nnAUyvobzwp56bneWZmfj22jYSBPWLgbkRhoqrE29Vmv9G0xge9Nq"
    "JnePSu3sfhb+yVces/sFfEwN4Xd5O5ut7lez0f8cPZbq2/lp4/E4u1bN3+5feiVvv5ddu0yd71/l29lO7sfkYv+wkPOOOuXCUe7o"
    "58HsNnu4nnXPDtz9abFDet7PZfOdi/ZxYX9yOZ1djXqbN+V6u9FbG6dqzs/s7LHkdM4aw8PZYXb3+ub56Xtrba18eVQu3TwXjn/k"
    "BqfnK53pUfWk+r16dDlamX3d9n6NtpqnJ8Wr8smO32z+OFt5/Lpb36insqXs9Kh9MHmq98el8dn29s+D9dZKdetqXMnuPHnXx/7j"
    "o9O/6VePh89nOf90slKdNMvuxmi3cnvldbLelfsrv5JKPa8fV38Ozzq5zcJt8aRbPq6dzi5uKieFrd7z+tf+94394uHBwePoYFA9"
    "+rE//dnzzlLueXV2OXj0dvO108etq0mtuT08W9m6rZYaz786XadU3jytHTdWjlfWNn4On9dvN/LlXPdw9uvnY7uaS512qrdXzfy1"
    "lxx3it7mzmQ6Km2seBcb/bPC8+G0t03w5OUgf3Z5np1ePh12j7NPjyelbe96OC4Pa+tHW2v5K+dpXJw019rrT8PW5rGf6+5Xu9nD"
    "84P812dnY7jRadxu+NuV5/7GVbP5WH8+291a6a1US8P901m3k7/urX3dHPe/tiqD/s16vrx1dZs63N9Iles3N9uthrOxPVm7Lbtf"
    "n3eaOz/KF+c/zma56x/7R8XDo1ztbCu1O1kvfS9NeqenB9Mfkx/NbNfJnjup80ZnxTspdL92KoVso3B0UT89ydbPLrOHN+Wv1ye/"
    "jur+9bSSPdtoz7Lr1efNs8PW1/7uZX1/u3Vxc3U8W9u8mbZTR4+Xx73j01xhVjh0mj+Ss3ypXCrnp+tba1vJr/0Lv1md1J4G1dqP"
    "x9rjyk5lXHw8yU6L2ZPyeS77/P3U2x8mC/ndp416031q/BhNZ7XL69z3jXFzbatTn1Vzv9bKJwRY5Ub7ZOPHrru/tVH+9XNtw68m"
    "1852zso/su6vs0735Hi/t33W+X5eLW0/dWud2vfnk8nGzk3rqXKQ9S4K+zf7x8XqsXNwmO1mi7Pp+GB8mm1Ox9PaaeXy149Z/qr4"
    "uF2oPG5f3W51LwrNsy2/Wh+nTrrXlb43nI2bJ53GVW77V+rx8mqTnIPdpO/XN26nl/1B/qq0n7u92bq8cYqN3crG9/7arDE4PJv8"
    "mv7qnxV3Spez/ZurZuqqe3XTOdwnHfXaw9vC+qBxUlxprTV6X7ceL9zp5c70V+rp+8bsuXc2WhuS9ds9XVlZ2V277vZ+dXLj7+S0"
    "lU5+HJydjC7y12vTJ++r/zU5K+cuV361Wk8HreLR7tHm1+pVvrM9ec45qeRR6bzdOcjXNs+GP2/LGyudr0ettdujra1hdzZZr/Vy"
    "Bbf0c3awVsmvTYqFg3ar1D4EF/5pfVppt/b7+4/P+7v51Ncdp+FP6m7KXztuHO57s++b189+vbSfPT+Y5QvbmzvXt7X9X/5x92mt"
    "ub896udX6uvT019bm+PS8fTM28/mt/xBf2N9p1Y6bp/VsmfN88ObyfP4auv06PB6e6PQvHazP87z1cp1c7bdbpz0LwqdjcL0F6Gc"
    "kuPd2lXr4udkM3lVOLv+2Wsepp69r/s7P1zn63nh+/Hk9LrlN7ebx+Nbf7yWrI9n41+3T/WdrWZzlvqRy12WJvv9le7awWS/m03V"
    "L7qzzZ2Vm+Obae62UDp+PPPOTg5nW7lB7uf55ui8+Jhzv58NTwal3k3xsepXJu2TvNs5G17Who0zQhP5/tnRVc1rJh0n6c62t85q"
    "+5PcjxzZUUebfvZntls7HjxNCl+7yYMiQXqH7cNSu12o5ibDVup0ktzIXXknZ5Vs/rR6dHj4+GPzsLr16+Z8v3xwfHRyO2vvf/9+"
    "8niTa1e28uVs4ZL8s12YefWz3mjjcrj/K+eUC2dkg1x3xsWv+ZvD2fcL9/LqfHtztPmUzN7uto8397OFwslR6ecw32qu5VvZ0rm/"
    "m3uqzLKPne7BQc6t/syu3V5P9p+PD/fPrronradL5/JsZf/8vHp+cNi9doeXJb8zu9n68et5vN786RzVrrZS1+vj3uN4Om65KwNy"
    "4fxo+FuFbvlkt7ju9nLls0qvevi0+zWXS3qlg9vO9WRQuS6fT0+Lo63edeoped0rdlOp24ZX3ri5aM5K17PjnR1/5FVn+XLl/Lpf"
    "GoxvCcBytY3Z6Mr9Xs6edbI37cNsu+39mJ2eXzyeZZ+muWz17NIvrRw4hf2DQiF32Pa3Hk+u3Y7fpnei87R/0C8WbmdefnZ2/nXr"
    "pJ3Lk39K7uWv/Mlj8+msujK5bOQfh9WDjZNBZXI9yLcKlZ1R7pHgjUnpJl/ufH9+XqvzvppHXqWfbRCQficgdUfPG7nzbCvb7g7d"
    "8S32SFDL10Lp4nF9fHHi+7e71UZ5w30cFXu1R3fa9Xem/tpu92jQ6la/FqYHhX1vs3JQ72Y3fj5tVpo/i2P36GTra+7wab04uizu"
    "5sqVev3rpb+5MdippL66O6nqeb6/Xj6v5/POzmOrOH068dyf++XG7k71vDIbHVZ3zje/jrrtm6e16kHn6/5ptbIzvVnvtjcufpzt"
    "uMX+1ebh98LzSaW2s359eF7ffOz/GnnNq5/PnVxzdP3Y6dSevHZ5Zau79r24vlOsreT6bvHs1rkqX590b3bOjraqa7+2rk7H7efr"
    "x62D6m3RO9rKdycbuWpn/LxeHs5K7uH6Y+epWKh+HawcN9e83Zzz42p822yWZz9WfjSmhd3h45mzf5NvXu/nyr3Zytr45OTgq5fP"
    "j5xmrv20Pko2C75fLHzttybN2+JG6udt7ubqsez3vm4fHQ6vrp4m26Vzx3Nnvd3JQWptuJ+/HAySt6fFnNccf705Pd/a3BlO/dzk"
    "/+HorLVcBaAo+kEUuJVocIcAHa7B/esf88opZrB7z9k7Ya0BwshHF80z3Uvvj6nxE5Xme0ub142kKrImtE8pA5Qqdj0c7DQHIu0B"
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
