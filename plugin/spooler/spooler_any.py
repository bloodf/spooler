# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.27.1"
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
PLUGIN_VERSION = "0.27.1"
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
            push_notice("info" if result.get("ok") else "warning", tr("Spooler: {text}", text=result.get("text")))

        start_send(done, edits)
    except Exception:
        log.exception("Could not send the saved copy %s to Spoolman", name)


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
            text += tr(" Swap in spool #{id} ({location}, {grams} g)." if swap.get("location") else
                       " Swap in spool #{id} ({grams} g).", id=swap["id"], location=swap.get("location"),
                       grams=fmt_num(swap["remaining_weight"]))
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
# OrcaSlicer's own translations (Spanish "bobina", "ranura", "perfil"; German "Spule", "Slot", "Profil", formal "Sie";
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
        "ranura {n} ({name})",
        "Slot {n} ({name})",
        "槽位 {n}（{name}）",
    ),
    "slots {n} ({name})": (
        "slots {n} ({name})",
        "ranuras {n} ({name})",
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
        "la bobina tiene {have}",
        "die Spule hat {have}",
        "料盘有 {have}",
    ),
    "the {count} spools have {have} between them": (
        "as {count} bobinas têm {have} juntas",
        "las {count} bobinas tienen {have} en total",
        "die {count} Spulen haben zusammen {have}",
        "这 {count} 个料盘共有 {have}",
    ),
    " (only {matches} of {pool} matching spools are in {source})": (
        " (só {matches} de {pool} bobinas compatíveis estão no {source})",
        " (solo {matches} de {pool} bobinas compatibles están en {source})",
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
        "{name}（{slots}）没有干燥日期。",
    ),
    "{name} ({slots}) was last dried {days} day ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dia.",
        "{name} ({slots}) se secó por última vez hace {days} día.",
        "{name} ({slots}) wurde zuletzt vor {days} Tag getrocknet.",
        "{name}（{slots}）上次干燥是在 {days} 天前。",
    ),
    "{name} ({slots}) was last dried {days} days ago.": (
        "{name} ({slots}) foi secada pela última vez há {days} dias.",
        "{name} ({slots}) se secó por última vez hace {days} días.",
        "{name} ({slots}) wurde zuletzt vor {days} Tagen getrocknet.",
        "{name}（{slots}）上次干燥是在 {days} 天前。",
    ),
    "About {cost} of filament.": (
        "Cerca de {cost} de filamento.",
        "Unos {cost} de filamento.",
        "Etwa {cost} an Filament.",
        "耗材丝约 {cost}。",
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
        "Bambu Cloud 未让您登录",
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
        "El origen de las bobinas cambió mientras se cargaba; actualiza para intentarlo de nuevo.",
        "Die Spulenquelle hat sich beim Laden mehrmals geändert; aktualisieren Sie, um es erneut zu versuchen.",
        "加载时料盘来源一直在变化；请刷新后重试。",
    ),
    "{printer} now books its usage to spool #{id}.": (
        "{printer} agora registra o consumo na bobina #{id}.",
        "{printer} ahora registra su consumo en la bobina #{id}.",
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
        "Spooler no pudo leer la versión de Spoolman, así que no sabe si cambiar la fecha de secado borraría los demás campos extra de esta bobina. No se escribió nada; revisa la conexión e inténtalo de nuevo.",
        "Spooler konnte die Spoolman-Version nicht lesen und weiß daher nicht, ob das Ändern des Trocknungsdatums die anderen Zusatzfelder dieser Spule löschen würde. Es wurde nichts geschrieben; prüfen Sie die Verbindung und versuchen Sie es erneut.",
        "Spooler 无法读取 Spoolman 的版本，因此无法确定更改干燥日期是否会清除此料盘的其他额外字段。未写入任何内容；请检查连接后重试。",
    ),
    "Spooler couldn't read this spool's extra fields, and this Spoolman version replaces all of them on a change. Nothing was written.": (
        "O Spooler não conseguiu ler os campos extras desta bobina, e esta versão do Spoolman substitui todos eles a cada alteração. Nada foi gravado.",
        "Spooler no pudo leer los campos extra de esta bobina, y esta versión de Spoolman los reemplaza todos en cada cambio. No se escribió nada.",
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
        "和",
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
        "El origen de las bobinas cambió en Ajustes mientras esto se ejecutaba, así que Spooler se detuvo antes de escribir nada más. Inténtalo de nuevo.",
        "Die Spulenquelle wurde während des Vorgangs in den Einstellungen geändert, daher hat Spooler angehalten, bevor weiteres geschrieben wurde. Versuchen Sie es erneut.",
        "运行期间设置中的料盘来源发生了变化，Spooler 已停止，未再写入任何内容。请重试。",
    ),
    "Spoolman is not the spool source.": (
        "O Spoolman não é a origem das bobinas.",
        "Spoolman no es el origen de las bobinas.",
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
        "Para asignar la bobina de una impresora, Spoolman debe ser el origen de las bobinas.",
        "Zum Festlegen der Spule eines Druckers muss Spoolman die Spulenquelle sein.",
        "设置打印机的料盘需要以 Spoolman 作为料盘来源。",
    ),
    "Spooler can only set the spool on a single-extruder Klipper printer.": (
        "O Spooler só consegue definir a bobina em uma impressora Klipper de uma extrusora.",
        "Spooler solo puede asignar la bobina en una impresora Klipper de un extrusor.",
        "Spooler kann die Spule nur bei einem Klipper-Drucker mit einem Extruder festlegen.",
        "Spooler 只能为单挤出机的 Klipper 打印机设置料盘。",
    ),
    "{printer}: no active spool, Moonraker stopped booking usage.": (
        "{printer}: nenhuma bobina ativa, o Moonraker parou de registrar o consumo.",
        "{printer}: sin bobina activa, Moonraker dejó de registrar el consumo.",
        "{printer}: keine aktive Spule, Moonraker bucht keinen Verbrauch mehr.",
        "{printer}：没有活动料盘，Moonraker 已停止记录用量。",
    ),
    "{printer} manages its own spools; Spooler only reads them.": (
        "{printer} gerencia as próprias bobinas; o Spooler só as lê.",
        "{printer} gestiona sus propias bobinas; Spooler solo las lee.",
        "{printer} verwaltet seine Spulen selbst; Spooler liest sie nur.",
        "{printer} 自行管理料盘；Spooler 只读取它们。",
    ),
    "{printer} is paused in a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está com uma impressão pausada: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} tiene una impresión en pausa: Moonraker registraría el resto de esta impresión en la nueva bobina. Confirma para cambiarla de todos modos.",
        "{printer} hat einen pausierten Druck: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 有一个已暂停的打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
    ),
    "{printer} is running a print: Moonraker would book the rest of this print to the new spool. Confirm to change it anyway.": (
        "{printer} está imprimindo: o Moonraker registraria o restante desta impressão na nova bobina. Confirme para trocar mesmo assim.",
        "{printer} está imprimiendo: Moonraker registraría el resto de esta impresión en la nueva bobina. Confirma para cambiarla de todos modos.",
        "{printer} druckt gerade: Moonraker würde den Rest dieses Drucks auf die neue Spule buchen. Bestätigen Sie, um sie trotzdem zu wechseln.",
        "{printer} 正在打印：Moonraker 会把此次打印剩余的用量记到新料盘上。确认后仍可更换。",
    ),
    "Could not set the spool on {printer}: {error}": (
        "Não foi possível definir a bobina em {printer}: {error}",
        "No se pudo asignar la bobina en {printer}: {error}",
        "Die Spule konnte auf {printer} nicht festgelegt werden: {error}",
        "无法为 {printer} 设置料盘：{error}",
    ),
    "That spool isn't in Spoolman, or it is archived.": (
        "Essa bobina não está no Spoolman ou está arquivada.",
        "Esa bobina no está en Spoolman o está archivada.",
        "Diese Spule ist nicht in Spoolman oder archiviert.",
        "该料盘不在 Spoolman 中，或已归档。",
    ),
    "Spool #{id} set from a scale weight of {grams} g.": (
        "Bobina #{id} ajustada pelo peso na balança de {grams} g.",
        "Bobina #{id} ajustada con un peso en báscula de {grams} g.",
        "Spule #{id} nach einem Waagengewicht von {grams} g gesetzt.",
        "已按称重 {grams} g 设置料盘 #{id}。",
    ),
    "Spool #{id} archived.": (
        "Bobina #{id} arquivada.",
        "Bobina #{id} archivada.",
        "Spule #{id} archiviert.",
        "料盘 #{id} 已归档。",
    ),
    "Spool #{id} unarchived.": (
        "Bobina #{id} desarquivada.",
        "Bobina #{id} desarchivada.",
        "Spule #{id} wiederhergestellt.",
        "料盘 #{id} 已取消归档。",
    ),
    "Spool #{id} marked as dried today.": (
        "Bobina #{id} marcada como secada hoje.",
        "Bobina #{id} marcada como secada hoy.",
        "Spule #{id} als heute getrocknet markiert.",
        "料盘 #{id} 已标记为今天干燥。",
    ),
    "Spool #{id} has no dried date now.": (
        "A bobina #{id} agora não tem data de secagem.",
        "La bobina #{id} ya no tiene fecha de secado.",
        "Spule #{id} hat jetzt kein Trocknungsdatum.",
        "料盘 #{id} 现在没有干燥日期。",
    ),
    "Spool #{id} now has {grams} g left.": (
        "A bobina #{id} agora tem {grams} g restantes.",
        "A la bobina #{id} ahora le quedan {grams} g.",
        "Spule #{id} hat jetzt noch {grams} g.",
        "料盘 #{id} 现在剩余 {grams} g。",
    ),
    "Spool #{id} moved to {location}.": (
        "Bobina #{id} movida para {location}.",
        "Bobina #{id} movida a {location}.",
        "Spule #{id} nach {location} verschoben.",
        "料盘 #{id} 已移至 {location}。",
    ),
    "Spool #{id} has no location now.": (
        "A bobina #{id} agora não tem local.",
        "La bobina #{id} ya no tiene ubicación.",
        "Spule #{id} hat jetzt keinen Lagerort.",
        "料盘 #{id} 现在没有位置。",
    ),
    "Saved the note on spool #{id}.": (
        "Nota da bobina #{id} salva.",
        "Nota de la bobina #{id} guardada.",
        "Notiz zu Spule #{id} gespeichert.",
        "已保存料盘 #{id} 的备注。",
    ),
    "Spool #{id} has no note now.": (
        "A bobina #{id} agora não tem nota.",
        "La bobina #{id} ya no tiene nota.",
        "Spule #{id} hat jetzt keine Notiz.",
        "料盘 #{id} 现在没有备注。",
    ),
    "Added spool {spool} of the same filament.": (
        "Bobina {spool} do mesmo filamento adicionada.",
        "Se añadió la bobina {spool} del mismo filamento.",
        "Spule {spool} mit demselben Filament hinzugefügt.",
        "已添加相同耗材丝的料盘 {spool}。",
    ),
    "Added {count} spools of the same filament: {spools}.": (
        "{count} bobinas do mesmo filamento adicionadas: {spools}.",
        "Se añadieron {count} bobinas del mismo filamento: {spools}.",
        "{count} Spulen mit demselben Filament hinzugefügt: {spools}.",
        "已添加 {count} 个相同耗材丝的料盘：{spools}。",
    ),
    "Added spool {spools}, then Spoolman refused the next one: {error}": (
        "Bobina {spools} adicionada, depois o Spoolman recusou a próxima: {error}",
        "Se añadió la bobina {spools} y luego Spoolman rechazó la siguiente: {error}",
        "Spule {spools} hinzugefügt, dann hat Spoolman die nächste abgelehnt: {error}",
        "已添加料盘 {spools}，随后 Spoolman 拒绝了下一个：{error}",
    ),
    "Opened spool #{id} in Spoolman.": (
        "Bobina #{id} aberta no Spoolman.",
        "Bobina #{id} abierta en Spoolman.",
        "Spule #{id} in Spoolman geöffnet.",
        "已在 Spoolman 中打开料盘 #{id}。",
    ),
    "Unknown spool action.": (
        "Ação de bobina desconhecida.",
        "Acción de bobina desconocida.",
        "Unbekannte Spulenaktion.",
        "未知的料盘操作。",
    ),
    "Spool actions need Spoolman as the source.": (
        "As ações de bobina exigem o Spoolman como origem.",
        "Las acciones de bobina necesitan Spoolman como origen.",
        "Spulenaktionen erfordern Spoolman als Quelle.",
        "料盘操作需要以 Spoolman 作为来源。",
    ),
    "No spool chosen.": (
        "Nenhuma bobina escolhida.",
        "No se eligió ninguna bobina.",
        "Keine Spule ausgewählt.",
        "未选择料盘。",
    ),
    "The spool source changed since this list was read; nothing was written. Refresh and try again.": (
        "A origem das bobinas mudou desde que esta lista foi lida; nada foi gravado. Atualize e tente de novo.",
        "El origen de las bobinas cambió desde que se leyó esta lista; no se escribió nada. Actualiza e inténtalo de nuevo.",
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
        "Esta impresión se registró para otro origen de bobinas, o antes de que Spooler anotara a qué Spoolman pertenece, así que Spooler no la registrará aquí. Si sigue pendiente, regístrala a mano en Spoolman.",
        "Dieser Druck wurde für eine andere Spulenquelle erfasst oder bevor Spooler vermerkt hat, zu welchem Spoolman er gehört, daher bucht Spooler ihn hier nicht. Falls er noch offen ist, buchen Sie ihn von Hand in Spoolman.",
        "此打印记录属于另一个料盘来源，或记录于 Spooler 标明其所属 Spoolman 之前，因此 Spooler 不会在此记账。如果仍需记录，请在 Spoolman 中手动记录。",
    ),
    "Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; adjust the spools in Spoolman by hand.": (
        "Desfazer exige o Spoolman 0.18 ou mais recente, que devolve os gramas em uma etapa sem perder o consumo registrado nesse meio-tempo. O Spooler não conseguiu confirmar a versão deste Spoolman, então nada mudou; ajuste as bobinas à mão no Spoolman.",
        "Deshacer necesita Spoolman 0.18 o posterior, que devuelve los gramos en un solo paso sin perder el consumo registrado mientras tanto. Spooler no pudo confirmar la versión de este Spoolman, así que no cambió nada; ajusta las bobinas a mano en Spoolman.",
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
        "Spooler no sabe si Spoolman aplicó esto. Revisa la bobina en Spoolman y di qué ocurrió.",
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
        " Cambia a la bobina #{id} ({location}, {grams} g).",
        " Wechseln Sie zu Spule #{id} ({location}, {grams} g).",
        "可换用料盘 #{id}（{location}，{grams} g）。",
    ),
    " Swap in spool #{id} ({grams} g).": (
        " Troque pela bobina #{id} ({grams} g).",
        " Cambia a la bobina #{id} ({grams} g).",
        " Wechseln Sie zu Spule #{id} ({grams} g).",
        "可换用料盘 #{id}（{grams} g）。",
    ),
    "of {matches} matching spools the fullest has {have} and the smallest has {worst}, so make sure the right one is loaded": (
        "das {matches} bobinas compatíveis, a mais cheia tem {have} e a mais vazia tem {worst}, então confira se a certa está carregada",
        "de {matches} bobinas compatibles, la más llena tiene {have} y la más vacía {worst}, así que asegúrate de que esté cargada la correcta",
        "von {matches} passenden Spulen hat die vollste {have} und die leerste {worst}, also achten Sie darauf, dass die richtige geladen ist",
        "在 {matches} 个匹配料盘中，最满的有 {have}，最少的只有 {worst}，请确认装入的是正确的料盘",
    ),
    "the {count} fullest of {matches} matching spools hold {have} and the {count} smallest hold {worst}, so make sure the right ones are loaded": (
        "das {matches} bobinas compatíveis, as {count} mais cheias têm {have} e as {count} mais vazias têm {worst}, então confira se as certas estão carregadas",
        "de {matches} bobinas compatibles, las {count} más llenas tienen {have} y las {count} más vacías {worst}, así que asegúrate de que estén cargadas las correctas",
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
        "{slot}{need}（含 {margin}% 余量为 {padded}），{supply}{tracked}",
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
        "también justo: ",
        "ebenfalls knapp: ",
        "同样勉强够用：",
    ),
    "barely enough filament.": (
        "filamento no limite.",
        "filamento justo.",
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
        "no se encontró bobina para {slots}, así que no se comprobaron",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到 {slots} 的料盘，因此未检查",
    ),
    "no spool found for {slots}, so it wasn't checked": (
        "nenhuma bobina encontrada para {slots}, então não foi conferido",
        "no se encontró bobina para {slots}, así que no se comprobó",
        "keine Spule für {slots} gefunden, daher nicht geprüft",
        "未找到 {slots} 的料盘，因此未检查",
    ),
    "Not checked": (
        "Não conferido",
        "Sin comprobar",
        "Nicht geprüft",
        "未检查",
    ),
    "no spool found for these slots": (
        "nenhuma bobina encontrada para estes slots",
        "no se encontró bobina para estas ranuras",
        "keine Spule für diese Slots gefunden",
        "未找到这些槽位的料盘",
    ),
    "no spool found for this slot": (
        "nenhuma bobina encontrada para este slot",
        "no se encontró bobina para esta ranura",
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
        "Justo",
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
        "Revisa las bobinas",
        "Spulen prüfen",
        "检查料盘",
    ),
    "Check the spool": (
        "Confira a bobina",
        "Revisa la bobina",
        "Spule prüfen",
        "检查料盘",
    ),
    "{need} needed · matching spools hold {low} to {high}": (
        "{need} necessários · as bobinas compatíveis têm de {low} a {high}",
        "{need} necesarios · las bobinas compatibles tienen de {low} a {high}",
        "{need} benötigt · passende Spulen haben {low} bis {high}",
        "需要 {need} · 匹配料盘有 {low} 至 {high}",
    ),
    "{need} needed · {have} across {count} spools": (
        "{need} necessários · {have} em {count} bobinas",
        "{need} necesarios · {have} en {count} bobinas",
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
        "{need} necesarios · cada bobina compatible tiene al menos {low}",
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
        "Spoolman envió una lista de bobinas que Spooler no entiende",
        "Spoolman hat eine Spulenliste gesendet, die Spooler nicht versteht",
        "Spoolman 返回了 Spooler 无法识别的料盘列表",
    ),
    "Syncing presets needs Spoolman as the source.": (
        "Sincronizar perfis exige o Spoolman como origem.",
        "Sincronizar perfiles necesita Spoolman como origen.",
        "Das Synchronisieren von Profilen erfordert Spoolman als Quelle.",
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
        "Se usaron {grams} g de la bobina #{id}.",
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
        "Esa bobina no tiene filamento que copiar.",
        "Diese Spule hat kein Filament zum Kopieren.",
        "该料盘没有可复制的耗材丝。",
    ),
    "Add 1 to {max} spools at a time.": (
        "Adicione de 1 a {max} bobinas por vez.",
        "Añade de 1 a {max} bobinas a la vez.",
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
        "Bobina {id}",
        "Spule {id}",
        "料盘 {id}",
    ),
    "spool {id}": (
        "bobina {id}",
        "bobina {id}",
        "Spule {id}",
        "料盘 {id}",
    ),
    "Could not read the spool list: {error}": (
        "Não foi possível ler a lista de bobinas: {error}",
        "No se pudo leer la lista de bobinas: {error}",
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
        "Nivelado automático de cama",
        "Automatische Bett-Nivellierung",
        "自动热床调平",
    ),
    "Heating Bed": (
        "Aquecendo a mesa",
        "Precalentando la cama",
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
        "Düse wird aufgeheizt",
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
        "Descargando el filamento",
        "Filament wird entladen",
        "退料",
    ),
    "Paused: Skipped Step": (
        "Pausa (perda de passos)",
        "Pausa (pasos perdidos)",
        "Pause (Schrittverlust)",
        "暂停（电机丢步）",
    ),
    "Loading Filament": (
        "Carregando o filamento",
        "Cargando el filamento",
        "Filament wird geladen",
        "进料",
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
        "Pausa (ventilador del disipador)",
        "Pause (Heatbreak-Lüfter)",
        "暂停（热端散热风扇）",
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
        "Pausado por G-code",
        "Durch G-Code pausiert",
        "被 G-code 暂停",
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
UI_PAGE_SHA256 = "4e47d306cd0a53654fdd603f044313383976a4066dc02e03d16f8cc2c21ce151"
UI_PAGE_BYTES = 1207616
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
    "ymU2hKVnxeW6zi8WOukdKl2ul9q8Hanrumj5uVZX+WKtk3JHDUzDJWPw+mJR5QRgdrEeFA2BIuGPTCftTs3C8gDX7Lv18kLX9JRQ"
    "ufs/WmlF5wnw5Upvt6nZi5eL6iJfvJ0XzePxepz518QUaPRixll4sInXhNGqa06Wx6RTXVBVstkN3bEw53OhmEVTbHLTfxT48Dpw"
    "oTrFchC2v4zqOLslQIyTOf4Oqa4itp/zWVHQGaLP04L+7Mw8tDsqdsnYBTgmtqcLnyqXBLLDKOud/V90/o/fY0DtiJKS6Oz/zh/F"
    "H6srevkoypKz//vo99/Pt7//TunxPz7a/i+n/W+Q9r/ysP3949//Qb//yH7/x+8ff3zph38bHIs0atsNtzWu7PYKDpqP/zGOs/E4"
    "AR7jY/KSnmjAL/LJHNCP2TSV4qSRMiMCnNLM4hM6brDDCYcNCFEuo/g8Lc+O7Eu828Wq3bk+vvVdHI+HZt7iNtVDvWhogs3a/ecV"
    "o4pozQiA0fyjtH40fjCOd7aSq04lWDfNW04Kl1zYTlBruuo7+cKAUU/btQRmG1Jdm8mCTuGkVU17u8Duoo7bauisuaTdICc/ilEf"
    "W8IkJafwB+mc0aAS0LhgrF60etlMaIsrOlmq6xm1RMSP1qWaFg328qqYUAO6KM2DTa/1smqxtLcX+eSdotEuy4p2fcHYvWiW+UqV"
    "ldBOKsjBF01RLgi1EDbOp1W5uKXZcKO/YTCSUdHpSTQLzrKxn55TLeiK58iuDR1grXk0k9Y7GspS9Q7dDixoPWnFCr+kBS1pnb6g"
    "Ks+Kc9XiT+mWpvaNnnQbbYr3mpvEw36DQrbM6mpJC0DbutTXD34syvZzzohq20/XrZYJRQEtnR4cuYyc+ps/th8Mc+os4KI4ywmU"
    "qNOtqumRehVvdJoPL2g+3wEb6MeHvlPAFemRwRa9Qz+mazcm6Te2GnWXCTmqpN5uCzo+63Ql6SuMBokOxWAqMzczCdqaRebwIMKg"
    "AXnilidMb+M7a2WHXMtu2chy7VOKhBSJGG7vpjKqpC2Qb7c9+sUPL2qNRa15imxTFm8KYSW0knlug134VttTMd6UdKKcYRm/BVDL"
    "7zlW+6xQOSEcbh2dYiyc81PrpqkYXOpW2qFdmvNby5TVsBg0yMLZnfNjqwi5YexVWpt5decdHciUg+1Bhc0zfVgFmKMDpWjPjvrQ"
    "wOZS1hKQ6aCcljTjpdTo2ttiScQIvvVvtLQJAcJIPh5ZQMi4CeRMJWfqcrg+N4Wn2lZxJQWvXMFejRXLKNeVvqbS9y4OKDhgrudM"
    "IPR6kQavMRpdjYrmjZ5R0d5hrJ5bKpcIA+ogcCeOmKk7IRkhWsKaPrqgHsyDpDjOnmOWs+eUyHRMnHx9+v13A+ECihlooe+1Og66"
    "Se+WKHuOVcm+59HYz7Gnss3ZmOAmergRtLGLx+fJGYiwAfG9daEbOrzotJyu6bCkj89oLogZpBoJjt/xZo/p5EifjAniCEzUhoir"
    "ZGVqJm7nvpq5fa6Y8DFO1HcYGX2HRcxQa5xc8bHRm8qP5u67OafD5p0MjZAw9QUwkI1Pme+hBjUBojDLBH9Z1lLTiVZPtfpDp3wK"
    "gWKkeVtPWtrgGgTmpiX6iz5r6YzXU7AXeB/lBMJEjRBNKe8VHb7yqGczwhwNWGN+nyx0Xq5XPoGW/3W+bqgyokEl5Tqvy+/LN+vS"
    "V0hg0rwrVkjoEeA8pf/RUz2QdrOICxF1ChnEU9Mp5mxTlOIjsiF06J6p9TgerNbNnD+Nif9Kou5Q7ukM0fa7S2B2LhLZg+5B+OFu"
    "hcFEvInDdDNzwWhlV1Nnh7ao9M1STEGS4S3k0NGY2tTSUEP9uB1qOltKOikGpvGdLxcuwv4nYV74NSHZZr28ZxD9fncQdwd19P/D"
    "oGxvdkEVdkT/dR27el0aEq27PEJYPtXDtr61C/tUc2uKp7Qoici63SBtt9tVJU3Po0cO3NOUiVmGw1pfnWKIAEVTRbyrZrNwQqvy"
    "yWG/f3AQVHDI2U8ZL+MT86mvj+lcQ2hQRzHmoR4aqsa3aj7fhGl7FQmxQZjYp+12e52/qorpg8Pdrmmr1b0ztrdfeOUJ7XG/WlqL"
    "8l7gax+Xw3Yf+NrzATcjC3nPZ7y0rkqLRO6t02ZSpVHswHDvE4ueQujUH4ROaVrvN6ddv+noGoYf20ZAz/U6KNNsIcFVwNidtiXZ"
    "1rLiGdEi8EG+g7Cw2JnHdueEkI1IL/Wp8S5Ej3ZZA9732wCXPdWeIvmOj0FG+3sI96n2E8pYlI5JSEr4hH+t1ReaCeefCcrobFMv"
    "7z1PDATNSnuMTDWdC9I/n/A2LxadxNkiv2zSf8pLqW/aTq7pVietwcQTJ1Pb1LujsdDmj4TEN9ZPD45jh9h9+jb97FOPK4Pyn31q"
    "V8p+/9k/aU6EtETllP2FdmQgUqSndHBfXuoaAqtdWbWgVjoVHxPEhBV/ckxkUfD++Xb7zFTIiE5Y0fCLI0fZmsmPDOSaER2rh7ZH"
    "P5oHQenpa8DCr3r42iDFX3Heh9jSVehw5c+2KvpG44NWdWblE4NdPHKxnXTyL7MxAAmE64CxsOTP9Sr+E8TQ0APOvRDzsDO9VXlK"
    "zZktKC9R3O3SMeFBuwjdJc1oxfLpNIQOB1hZ9zUy+bQEL2fPC3A5vB7uZfOltoBgC0ZCW0xNATOnttxup17hfHuj1Xvtd+4zv0O1"
    "XcHPVZtFMk3pexRPaXPaBPr+DRL8Jv8JsPuKDkqf9JU5+g8OXuknlhkFJn3vsNV7OX7e22OCzyE5QqWloe7sTe0m+N+KD1CuRo6w"
    "N/7bN5L0xlXbDh3lINUCULq7Pqi5dfADsGz9dtqxkJ4o4g3LF3dEJuyY16Yjo66uHwRI70cWYTjuPtUCe+2wNV0A7BFtruuGihPD"
    "r1o+NJ8yLnlVlO9SSF9XBrkgQe0npIFU62cveeMzxkKwqlM5Sof10M56zS1RB4a160BKXciIOSNmibAK1RCrPyF/VF/jLwFiWqt6"
    "v/16r8tqP8HObp3qnTb7S/nO0fS5AXz5dyaMlw2dMN1m+Yt5JgzGWZNquVq3OCKjb3TUTYttoXu+jz2f7CRPgxFvJN/Lb6x810Li"
    "p0Cl9uXoM2og8kB69C8arEiJf3LzrFsp1E2n442aK5rT0zdgaE19x5/TKHoyFTjlTX+IWeXpim2fh27bHg+D6SNIIHRbG3SrA1zL"
    "4Dm0MlXCtlS18KnDqA2A4nC75Ts8ly2cs2mM+udyiB91HxJRY7YKn87YGkGe0g6zv8Zn1KtaMfwG+5twupv0Pz16ggCUBpaUiinM"
    "9UVSKwAHngqIQiG0oi7WA5OaFspQp/Qs0BirgkoULrVW2pW2JcpBs75osFrYDfJSqx5VXXpgijf+xXX8n0N/5gTZHzh5FJF8ux4o"
    "uIMDamaC+olLNz/2aC8hMguQ7dd2s2/MRiYO3dQqAuEWhINtCJICu+P9AHlcNrVVrlu2BNNgDDDqF02Mrj8tfgNe/0ULkfMrrRpK"
    "Hfne/YB8mQCUYurzV4hrUlP3dhsgyoduLIbmSlqzjvoOFWarfc3wbHE7cHRALQDSiS5F9zUo7ra9j2pEZXLa0qp7wtGSFnYHOLD1"
    "dCLPl+Vx3IsFIM/9hC93MCIdxGX7F9SshRvbNdsfQ4rmdzCsHUuX8iUY6rwTGO2RtOld0QhRLvnknb2AeE1HXe9X+vPasoR+Axjk"
    "Ixhnr2N8xAZL3qJ3hG9f02G5X5ap/LaNXstoQejxhsmi1s3y6+BMC579koSpaRsn5jXtJKsacld309N2zj/eNG7lg2lX/gRyfJZN"
    "Gfq95Tqr3BNXaZ5dV2nL3D+udm8T/p2B2jeRLEf2jWgzdzdo6RcLXAEmJv7TQLawCdoxDFQYNB1vrz0qGmBmcJmB9Fgj0VYSs/oH"
    "veOktWluf37F8pOAb6xbd6big2aCjvH35oj1JGF4ljOA8aHIX1GfaHjuGDwM0HB7H/blVnf2BLRVDEESaD7j7CYuDa60O1zj9sx9"
    "AFwDVFO0jlXFBUHepkY+itv6qvPWhG9+GiZtILj/lfrw2omTitZcHwzb7ZZezIVBaq4hYiPYl1K4LYDKA5fChT5KlZC1MzqgLcBo"
    "oESC7PQ4OGsXrb3yUIXKpQNV0AGghIroXwIcQybxHDZ8Xc+yeE8tozBgSAEPjIHM63FcubvdJvaSqEKuD/KUjuYTDEHucrAvxyIF"
    "GdudZxQB6njoq4owb9SBKPxgu8VbQ1PWG0VQsymfpJD8415mZy5qm+sCZEqEZbeYqmIG2xyDXL4yE0sd9K8NblbpFJnkjR4TRzdO"
    "iizIdt0mrsmm5fhkFumg0gpXGiJIG3JNcuRTZbSG/813tNrjpFsGn+12vN/c+q5bf/39Q6h/gTUiLB9NcAGFK+E6p24QsMbqF5SL"
    "szb5FQ/Z1/y3tbcJLRGPJROjiaS1pX3SZdDytPWXugzs0v5eWwFlMJNbMfuJNE6tSfvUJm4m4oQfeA+u2nQzGrHi1GiU4NJHnclO"
    "G0gbVX3ueeJlyzyx2isBBYWZycItiaLjmWhZaMr47q+lQDwIMu18AJAznuaEv3cXO/sNj03OGE1G+uzoPHUN00sszWvC1rediRi5"
    "75FFX9N+NedFXl+ul1QtcfpqVixaXd//peTJp6yQYfoeDHyvrnL6oZrKqavHf37n65cQIX64Cs7+i6GU01d50374e+T+nW6g3H/o"
    "iivy4e5Y5ZR7q5DMD35clJPFekrw0AGoW/u5zabvubCoVX6oLOdK0T+qoozugVCTvlMLO64P1heUkDoZKu4bJGV8cIBM8NsvLuwX"
    "lDpGJniGTuu+BGVJs+b+02ix2YJXtqBkc/uu8Jvict7+hy+4jP2smRcEJnd7wenoaVMt9f2DR84HR2+0Xu8fomTKINvqDfZvo6fR"
    "3UULM1H0tKqJ4rlveYM8LsgtTD+Arfbyd2pdyjzc312TK/21t8h3sJhkjPfxZkDgLduukgmfBKpI67P2HEe+aLSKAkct9FdPzhyQ"
    "QrnF4fZu/m1+eY5jnlVpHrw0eNvRB12FUPNGx+Frq1BL8J/HsVdOYzEgtAYJgnJ+I5KFyKOCunLZUh/7/fu0IYHTtTLTkWxw4Nou"
    "5APDGdmz9R794kwPLoBVczomiBtkKcl+LZz49yvZ4fjMByMekIxE5XvDG7nxWf4g9yfuvIthicqtSs3CKhHxtE4ZwiqQXbZG1cmp"
    "K/tlH91LSsriN2kVLrSapBVNNABgYmfdUimTAVT4cQTmbtEae/wz8blIy6GpLmqyRWp7wOoSdjClQBnDp6EsqGME2YnTIzym7//G"
    "1618FwvZvaYOcl6lFvSB6yGUX4poHSdrP79XrdcnMlRva8jezmxUxHQ0uAs1yVGeRU1qdcAglqMiYT9V4XqK272G9Q5SM0xIs8Le"
    "c3JN8M2j8MP/hL78YLX7E1AEUzBJC9ySVsC+wQxk3NAkTiZ+Bm73UIGQoEQN1l06cCjTAwwB5OQ0oKKCOXXigqDpc0TE7m9EmJ8d"
    "nscZ/6BCflX+0zgpfAcuTAegurGBJEsxlxv0BrexFuK85hWoaAXJlqoZ8GlP6WjsqE3lNJDoqWh+Wmti9E6FQ4NajkdDgc7ad/mS"
    "cIhgt3hg6TUix6CK7w6VsdHUx/wTzRZbWk2+O9Pn7tNRHLCTJ0xuj1jjiYo7LaV46Ih/uZbzFDnR/cT5AN2rO+p1Wkjs6/YDKj1G"
    "PmsVOd4YrU6n2lM0p3PWLk3b3aUOWV1mDq34aexUl51EyjK3ezXT+bFX8zCsjAuygMlW2avvFjCap1YLbq+AqdflF538Ovc5YDSj"
    "Oiuyr9rkp5YYwWdt8r6NDdO83d5/CrFm2/1ZJTTXjIBTtECnlvs2uINFpDkkFemK0aWbOdfL7hK6zp4I1qxSgtaFaVvWoxSNOWG/"
    "o5EogRlNxuQGkjMAU73dsqxiTN+NgUa9NmiFD6maysnJcvDzVE+VVHJ0DL3iKBTxsm+EU7Kn0RV9m9VIreLkZ/5b0fH41sDdAzq9"
    "dDltCBDv0Spr1jTSiICRoLXRd5CtFnpjykzyiVFx7e1Bke04sZuFFPilZelB71f5JRT0A/IIh/wgQoEeDZIGXaAQ/ZZ+KWi2CnN2"
    "EkHROzQTn1trhjZ2asjJWs6kxi2LH4FdGI9cIYul1mtw+0DbGd/SoAcswGFpAH9axImkQELBe46a2ImQITTrsPejphe1TFbhOnPP"
    "F04plUZv2zXSC08b45zZsVasb8PWaZNtRSPWPnQQZ8GMcRL1qdxV1+U3olMcyhGCk4N5byt5SXL6yLblPyVoevHfQNNhAE1OKf3w"
    "3il0mTv1XHD/21Z9L08vWvXOpkHRRz1t2ehO/cG/wV7soohAv8ZhTTN4d1TzuWuA3EnzCT8RsAuo0rFONCJRWaxIb+UOole/J//o"
    "94mQkXLQ0x7jfc3GJtKMmqZl9rRN2qwtE21JXFxh0VrkwVossqrlJWiiLkm+jtVGqFC+9hErIa1Aa+LuZ21IcEf3ZvtFEpMwyc5o"
    "wfm0n7L8JD5nFV9bjgjiQLL5XSh/CqcuIHgxagPCUEfWXm6ZCTyzQkZQ6es2BOyNiAk34YllVqKQ7SorQgiWRW3Ys3nMM1cYdEpo"
    "InjL5bje0BYgNJj+wYvZpC0WQJsFIBRVCXFWeBX3B01UW6Flp0R+pwTzQkRg0Da2n+wUdEigRhxZKjwcjF1zzT0HIRFK8bDkRgdZ"
    "yUYOlTbtfNQyDzIvHgWYaWkZlQlZaLd/8FbEIlMustKeTqVDGvJUBHKa4Ahg+hUsp+1HhfbzO5PaGWG1N7rcy51F3dsQx7VqmLeJ"
    "5EzcOQOoBjfo2YZQcEJQyKgY5n0tvwFVE8gy1HGCAUAaMSCPk4zsnCAfqkPOGsrScDSbf/jZZIaC75SZm5CTi/BikfjDF3MknQYE"
    "8iW/ZlDs5GjJKe7mFCAESlZkoslb4KJBTpgcEMY0304J0qT90G63fIhut7/KT2TPTk94y0AY0guAX5IzvNdAXlZCAMOIartNnew4"
    "yJCqGuJ7fVk3WtsTZQ7KRg7K2hyUlEVJiaTwMLiwjMJZXGy6hLP0teS+1txXsfQxjBLaL8K+BhmxoenqrPaJhtyj4bbeyiM4YxdM"
    "oNsDVjvhE6w/BFSc5MB1EXdmxk5JVE9NucBiTM5tATBbZ+cHB+8uVmdyHHh5jxdf78vY3fao0yeb8qw+T7/FzLLgDbU57PlFB3sa"
    "XGo5PZEapE+Ke0j6rKeT4h5KPuskW/o9a30qqPasTkLSd20opwJmR3VWJtIy8zsvW0bqCfWUyMoeTNlfdZMOKelNkHQopd537wOf"
    "dV9/6r5+1Xn1J/6PfGSZOyptrprkMB0n/MLCl3FilvNIroKoDpN9qm1BU3fwxnnmw+PhVM/y9aK1CYfBGfdzeHAKKtHJn1gsGv/z"
    "Vr1sabTBRc+XYXlb7l1LE0fTEJT75m65Q6KWaDZpfoJyfwZyJNFJEDt6bZE4a7OGZkBGtdwWARe53XpD6Reg+priYqFDW1mzJ4vg"
    "pjO3mbmxx6IFOWUeGkcq69p3vm54GYl+uwFBiALHBGuh+ZYgogY0uNfmuTu/SLKji5N9KyczPF/Dr21oL7lXmHdGUPiXDxa2HJAv"
    "+1vYNZ2xRpz0Kulo/ASXiq4+TygQCceHfBKq/YS9ANMRiACcvHVvqfr9te6UxO4zgkhdgopmjvJn4ShV65MMk+l3Vll2BrZvQdYZ"
    "XR2WzUuG52COOMXTkI6JJkioJIs7WJV/qYYE3SO5qPf6ONKf0HjJS1GcYRFN808inKVG5aSRjCuXytez91XCopgHXHDPDAnqDUY5"
    "IKwOfJApr7uUoe2GCug81xAf/1qOf9pZxAy7vk7kksUquvvh6M4wyu4wpHtWyT28a/g+WCuzFAPDPvAyNEKlJ4aVSp905DnUyvfR"
    "HbFILMSaEycYxwQiUBj6xrwAIPNsP2A0ucvS151eT0IQM/fbSYhLmlKgaPEBKGIqq2sGQW3RgWwV2sw87plFGJALldvvAt5/Y09x"
    "9Jm87Su3Hhx9wNBCLCaELu+0b+SHPdN/1oxNS2/O0FH136LhjoHC5zEUaIzBi8XSxqiB0QZx6SHwd40ELOzbxf3G6v+LalBHRyxQ"
    "J/6LvRIsiVHWlxcWSHhAWJdGPG2UXR/QmWc7ARIgq1MNG1o201UwjqZqYrZHXgjJZABlWsKXEEFDSGesSqs06e/mSqNbS22uRCBb"
    "2p09K61CERHw9CIKRS1E51BgE4OdgFCYo64Sglnh7IvlUk8L+BDKiYrWq6RSVTnRSaOciUOyUPn6EnLur6uLZK1ADSezXVqIP5+K"
    "toFBHRUL/OX3MLtEU0dxcsk4Yaku1UhdqVuM4yIVI3TZ/dEl330ZJEAl5GIxkU1mctm6/RaWwyw/yKILAP8tZpdvgdMnX0sn5GNl"
    "6zSS+I1tzQuvRdRJ6fyhTV8ZumIepM2yWcR2xFDToY5dprzOZTbL0IjNTNgfFH07kmsL1ssbBWp1P7BanXGwUg5pqZehVY0084k6"
    "uzpHU1f+QyrZ7nbQo+73K7sRLmmZecYPs6OPD5NqKEPGdONEEMW5mxQmX+pUfFUtje2duun3bwbW0nMS3VirKLUUlbCm3y9tO+Ww"
    "TCPrrCborjaeaWwnT1lnkL/R6UUmXhSs6JQvQBbRtKTlK8XDEWZqabXoac8uB0Zx3lwqOxhfitEM6xsTcG23VCa6yFpZecPf8yGl"
    "NUvZExZPaOg7mTHQbPsV6fdpURTPvuSeoTDN5LS0IqQLopAgtZLEs/NEEzN3PtSwa8IylbRMRK2U5pI+WCetZJVFd8103YsZ1kQg"
    "RSe0HXjTv9TRJT0HZmsLhqhFdAICJjkRj1VLIWhocdSIZkPMmWRFZQAGCyxljnj2ZjGA6VOjR7vnwgKiO/rGsLBLyFvLLM9OIPSk"
    "odoZTxYZ9USur1lVS5BynJh8dSqGxFSef6XkEuliK4eK+CHIAQSmp+rU46RLwW8ExPa66TGMGjoshPAHETw8WAcPUenubg7jJ2nb"
    "vV0pvcuG9uBAxPMxWjJYhl023OtNpob3Ee96pH70iL9jHxXhRytuGvMd644znEtzQBCucIU18zGbPfcZnXp9Hq3RvZeRwsRDgBXf"
    "8UC2MmVeNi+cryfrpQ1XEGFTO+d7yCsClP4mJtjjdaZFpMyoz9mL3LoRBhfnQQ0WfxoaLKg8EJbcMjFWDEytNHG2WivcAOOOu4mO"
    "r6aCDR06nld0x/OKnHroDpyuSLO+3aDHt3IW0omMoyR353lFpGw5uIJLM9FQ3Oi6ruqv8nKK47ARRZAfyzknTF8g8yUWabrmipPJ"
    "DhZaJa6oT+Au8aYdiEOu7ZbN2hxmK42pLsukVqAjiSMdz9t21SQff3y11n80g6q+/JjbP6j1TFPpif74/6Ht1xZLffBwU+/GYjsW"
    "2s/pCTdDpC4YNOeXDYZKOav5w5zY4P84tOg6hMWzM34WPzYlbuk1kS1VLBf6RqcYRl/SfSxQY67qaa0bxbN2dKjO+LNzuZW3usi7"
    "C8x7rSrKmwRM2kXp/ZsdYk2OGJAKa7g3BD1dEVTzbNjb7hv2xXjK5nkn/HxdsjMR9RamGC/KlBZmWTRwcEVfw5mDei4lAo6k9LzS"
    "c8IxL5xakKZjBh4Amba0qjxiF6qh2+KqeBdUcVo+Aq1242ZSFuhxOXT3Do/KJ0+eHNEobyB8I+B7Bd4EsLzd5mLTVFhL4KxN60dH"
    "SZnW3l7AtfvU+jgITNycV7NXTHqhJ2euMwdH58MejdGXP4Zt6hMUJq6Iylkzb3o0qnLvoMmjcMumvGGZ+qPsqKXjdYPZS1+UMmdv"
    "Qt3ib11HeS9flxBCFFOxarx2Tb3F3KGlxA2H8P6J61XQgf2zjaFXh9DrPgNZMOT++rsmD25YL9kFhPj9qtXWj1gpq2T2VOmmjQ0i"
    "kFBMoQQ0WBdT2l1OTR0yL+Tx2QS/qUVJBKef1ZqoY9ziZvXBUXJaqtLbK0ZlYI+ucNS6TBbqB8bq4U2X5UzEv8SJHYmlgk4w2EPW"
    "PYAnqgCPwuNW8dh9wP62NoJgT8qz4nwY5YPCWQplcv2bx0mPkuFJqcDYHxP4UGmatvM0T4zxWW4oXkLb0PQxujY6PifqrW4t9caA"
    "evAKYMY0jOtJWtN+Dm3ED4f6ceEcf1A3r80a4/rT4RiUJzxQMBIYvi0fX7uhvXXu4XR6XZ69Lc+HgaFoYBl67G0dPycyJApNH493"
    "IZYR85IvwBF6nPLSyJxoNF/QCAIEaLC0n05DdNrJOQGRQc2hQrGdI1h19nXqtXspVUB+c/PSk1el+IrF7mK/Sm6nZwRpYBaQ57v6"
    "hremtSI6xZSdlsFGOA2mjHbCKaYstKn9PLA4vTuJfPpTg/ifHf0zOfrUz+SnHVvcY8iJ7Hh4O/6NbnS+38lB4L6hE+A140CD8lXk"
    "srZbvz/6fZ4Cmb33puiz/VPipwDFv3cnxHvQ/FRWDGtAio1GfL6+JGTAFYWnBFO670tD6PZapm/Lroi6TkUpjiiiejCiU/v7PDo4"
    "svp2PzEuztPr3PReVQwjVarls84MGjjP3Y55kg/1wUH8Iid4/AlnjnJtHDnCsNr5e7kR+2ai34n5nfJv4EOglBtEeA2AkhX7d90b"
    "UFVRXszCEGLyGvhpOx92N3UZbmrM8llOJEKjJmkLX5H6fAhNKiAUKFumG0PTJLlai2/aJN+JxzWY9F1CwUkZWnBDbVK5omzaHMIN"
    "6/a0UtViyqLMxKuJE323rKbFrNB1Q5RcfB+1/GN5R2+JFaMhp7zw/nXHxBiMuJ+B58qgkDjVHTu6jY5hU34o9myjBeU3Lft6MRWV"
    "3n0l1+Rc7joDPPPR0Lft6rFIhDWkWmVbc/bE9noFa4RLTnQIz26pJrRUk8cOmiZ2Qy7S/GxyPqyyxcBOaVpRipHrdnra7/tCwVkZ"
    "LdIm2uwUkdt7q+LVeBfoDU5iYqMjJjeJzF/TOnxOpOZAL+jjQrWG3gxpk589Mv4yt/P9ZQ6a+6qY6obORbwZVz3u0eUPvdeF4Ks9"
    "PfYaarzw4tgGLX95R1qYfpNH1nPju8IC0Lsie1fQJjP8gm0iwf2z8efDO2u7rQcTIhmEPwlYDNz+76cF1eyPyGouihGfcVprmSTs"
    "NtytWf1W58XVKVPCIXYLCzO5yUfjzL+AJmYs+k1ptZYAO+Org2ZyM47VnyXLLWhWvikDvamvyz29qV8dh+lv0P6z6HK2oO2eTESE"
    "uYCIci1AVbBOlDicpB8osI9XFeyRZhjoDzmDxiRlX+HlxBkq/Am50ww7aHQNNlUbLlAwmNuJvan9QFzCe8MFlnbAe4ERiOBRZCb0"
    "JJTRikBquOaJTN2VB3PTKxEMoNAStAX3j7udrQOZEZt1Enm2Uk2Or/p92L02K1020J3nwfKoIGQD8g4/tl7i2wwOJJmbIDS6HniR"
    "L9dfhj4l6ABfhu/HaDNiemMFQlBxb2gDctfnqRE6rx0X/gNQ+SybCXqex8kU8ETbZx7cgZZdNXRjqA8euRB30/B/ZQy1xoNxnP1W"
    "skoJi2FrAuHEsGs1NBzzIQNsDkeY4pqUuXnchVlPnr/m5gahSQnWCjpL5PM40DGvos698G9lqB3R2iACA+c32AnpcATcf+ARkhUf"
    "fSkcJOtzd11ldtIP3QuCh6UzTR5dsQ6SgABgtGje6oVGoAbVSiKvi3EFPAWxYZ/ZWy+NLCwG+QKXwYMpUNeBz/zTn758sdCACzjX"
    "FrQhZ2onUxXhR9/m7fzbVyYrtIzZ+75Tjk7i/QAGTF9VdnIuway2Ga4+WEiTlDtV1ekG8SqSsZ2GsQonBZ7QCYImumlCsxchM9RC"
    "0MpykqzVapJM1epiksxUlWyok5q+Xqk/17q+PdW4J6zqZKkE8b8lTJvMzctJtUT/k0slCPc7SJFGu126UFdpW7OrgWoF1aTpLfW1"
    "mJzMi8WUSia3OzqSLzwKoD3dzPOV/oI2Wf/oMwiO4ZReSovisO17vFM30GIKpoua0rYp3EW1hMx1m+YuGdLkPJ3WrPUzVytxkl0x"
    "sri6pMWpYcCdVfKacMaSlmi5oLyiZr3mqHJp7LGlGBTNyQv23DIheGzNvL/lthvWtL4n3VpgxDErq2G/QcDPQqKccFEt1/mwtD0N"
    "XM7b25YfysBxb2xSvA/eYCIsjTSKQCxAD3F4wdNNZ2Y5mVe1bYxIoRu59fshkCMTdm2hdDQUr71M5zpXE3qRztl1AJ1PpjZJGIqo"
    "mIlFtYICKB5KDwnEP8PdMKHraVFePqvxcbw59RqXuyua0YtIVMXRwxY9jNVNJLTghlvHkJyTAdMBOy46Bt0soT/reLP2TsQ60xW2"
    "2xqoOYUreAdD/DaUk8uWcJlq7tKe2j6Er+qyA5mj9DIraWNd0G+dzK3ODoMcUTp1tPIQKDkG3LbbApn7MHibReyjoru11K0a2c1C"
    "a5DzmmMKk8l2y0bTlH/hthPBmrqKLzOzQMA75sGkEBpieY99MR5E5CVIj5OmjgTNLNSRvwyI2rsVxlRjpPdaRLqz0nAQQzuXGV8/"
    "+Yrb0SJ3XSgamZAml/0+56xog3MPGHiucN8Dv/BX1pXzZr0kpogwnaQmBRUQMnnjUBCRVxb5EIskcEWkVgATyUKFS01oVF6BStFv"
    "XBoTeQIAmOEGDMQY9awLmnMweffDJtFwQC3RgjYZgTB7eiiiSax6+GhFS0ngUMHDV/egbfY5SyK34QV3WNNuxPCXqtcr9oEGk8ST"
    "0dRqfjuFanEyqQM9gKa2s+ePiJq+odkjxHocbyDHlRA/wSQRXu0mMLZXPtHsE04t93aPaJrrBa2FWYBG+QWa+AVamBlfY8anKXpy"
    "jNmdovlKKu/9UBpf6LgXgOSyxqwSdXx3ChfhFNIK0Ozx0I/jIVfZ7NHqk7pzwGKG2DdLcbEgHEfdDw7HZu9YnSgzmYvwfF3TchCV"
    "7T1PiNBBEF7gPk+ci9UDcEJvb9lH7ueSOiBmGxMxtsfPAw5x8UBmchx3sV3tGfa7H9pPNnu4DtT9aLHK93AgQWXU7i2k+OXd1WkV"
    "1SGnaqz5HQqfRhWfYqK3bg11d8ITtMGxbpED7Yd5SGhg2ZcyUZN0yd3bbpeDGbH1LcP6sN2jM6J5Fkk3FH2KCrudp41WU3qr1oRU"
    "Gjl4l5nclcGVius79/w/VgHLkAmmCKVoL9oxxuasmxtkBkJ5v6emm3sH1V5j3I8gkEceLIo590Vxi0rWgZ5PHdL2RHq1N+4GYN16"
    "1R92G5yxwo9esIjLVCpKQOFWL+7sZ8AqDDuGcQdkjwDCRHg8bdu6uFgT+hsDCA+uDqrrEl5BSvBZoOyMFz3ZWEP0rHMpMw02YkCx"
    "eAiVKSvFB9L+2c3JduLys4fleVqxflUd5XTcQHhI2ESzsUfFczirPXey0PmVPrmgildBKm17XSM1UHDyavGbojHRqBCoqGheUR3A"
    "GPxiLjLN+0KyfgISaRKjFeBY76/qKBIi2tUIv2mx+jLI8BVKnugfzuv07AvTN8VqLOfqsobEkbCVifOVr1Yw/HiGEHV5qVZQLmvQ"
    "a5tSlRIj6wWGm8zpdC2Dx6czetzPOgEjtCDeTNLke0yAloTgkb/fz7r3+6fSUfkqfEYNdzPDOnZq5BiqZ3mj3xJp2hQSeU2Ol8sa"
    "Wpdr7MJNs6jaJml3dsNAykXwufSmDJHXymQ/DVBm7/ff1pF7i1i9RFxM2Uue7IqOaRgPNeuLt7XW2VdRHAivenno4q4yhhyyVs0u"
    "ZWvXeuAAyQqwTgmCrWX8CT+jrsnd7EV6U0cTogtrSAEmLOGnDXtKtMc1MhZWNuk62O9The5N6G1i3sIve3/k0ZqwYr//IizqLjfo"
    "ILYt0tfXeGWHDAhZt24PCvDOQVeccbQfJ8Q8hIgcmDhuqVPmSOGG8o/qwl3kiOaVUQfzF52BcKtTHqZcIn6HLzGIfWjHsAyJUXaQ"
    "KVTcg7BPxJUYAa+S+eYBFuUBjbE7wIw9aOe3ZiiOQxZgugAPu6apOjMW9Gv2xXme0qydzepz6TeAS16NFNz0aCFV6+l+n7oZZvBR"
    "/J++2yXukeeA1t5qdDpvHqE66VUdKOafHZ4Pg3BJTwL32BKmkhUygpXfEO52tIQVGwGJ3dbpKDjMLvxhttlDnCARCdVLvBuuOow5"
    "Q2fYPeH7lLDFUhz6NeGF0E3duR3ZGFxZKN6UeYAsK4BgF1M2DlFOunhycRdNrvew5MwhyVUXRy7vQZH7GPLSI8jRHn68ugc9GmmN"
    "9dnAEKduAIsc9OXUSa8IH1yJwsu/2auR1nuCrfbs6Hx4aoJpilzTOBSDUE8A4XEKPxpQyQtSOGGnTszJ1JlYdeHn1Jp31mnDWK70"
    "R6LRsKnTy+22EYrX8v7YKkRx4YeDHgjZcHN2cW68GvyRsz2id4WjFyg8lJBoBqJf8MbWcpUkBXaQ5FHHT2nXQi+D3a9JL+lTNAD9"
    "lxCr1+mEzgQCgHT9wQGMtlsUutpuUe52u113hiOmP72jYXu2IhQAKRLkUQ3wJM19VtH0oTPqpLOtCZd33qFYyxXYGzPu3zTlxFBR"
    "knjtOtOah6im51Bahn8vrqP114Yd8GHFDFSEaV/JtKuyQ6Y4TE+H6mk04y6bleGxAb2VNDYi8aOc72mhpRmV2Zz2AI+vDVHgzVlx"
    "LspGBqkhwQyKiEEU3RsUf0FMPMa2wtgqGluFsU0WVelMToo0QALetGr/PDoJUjDV/g01Fvcj/ZMgOQtfbICzMvi4g73/09rSV15T"
    "9yQIZVcb1aXXdahBnr7MRSHJst2iNxDcE5/UzkVv50vm9oFoJS6wfA1Cx7/BFEocLFfLFc1s2XrNdZdkKYdhV1LTekFAaRw1G8Va"
    "cPb2Cs+cNW3/k2PcvpSWCHPdLD1ZFnAU17W7Sg0F1J/xUFxfN3AyasnFtHVuzO92HfXV5kyLhXaCZBa40inPhmzf8edBoElzyxUo"
    "VcKjd9F8xQIb2jBZ2RWsEh0pao/yCjmaDGhg4dc0S5U3JxLrujMSW85nAwKa5ot8sUCExQ8VtvnhqMKiSiCCduMXtBtDQLDDfVmE"
    "8n9sxpI7z1MVBMSrnbWIRftn8BJy+FdKs0bvlTVmG8IgojZUAS3Z4Gll/Mg8cbIpkieV4K7KdT+jAitcltr1Ilr+0SNmVY0rTupi"
    "Fd5kNDGLDeDW1VM2fKWM68HG9iah/VapDfrUQC8DmJ8opK6kqg4lVbXEujJ9SQ+O7wkZ+aJ2ro3vbLUXdXQPyIqWvRuvPeo6i9bv"
    "310uZ2n5ouZ4bkIkuro6pHyARJ52bBfZ8qSJhC3TA/zsEPGX+bBE7zoWnM89Y81KB06pNdJ3lZMHxfR1rWfFzXY7vhrHj8YH40e4"
    "020IUZiHo/NHj5IwyOf3PHmcmZ7tFT6mwqhEHarD80AFKhSruDAOUVSm9+q8Pzdx64wlJpvvDcLwxiK7eVrfb579R210vHNVWY1i"
    "0SXX+x4ipGi/T/llnEHrOYFgFl866RFW67uadZDgYjkPENM/j45xjWM0wHJcuL8RjeMp0u9AkU8hUsr18j5o65AwYZOfZlUVBZ/E"
    "Sc5KMGmV8ZVoozYFEcV1sgKNvxSl9FqN0tmAFprdkWfmcbNL5EldUS4D02mLOLC34KivEPT8issXCWI60iKOFFv7Rrcgd29cqGtY"
    "eXOu0eRc9nj39vv0kK54/r8FileX0TKOR2fLczk1L+iV5v7KJvjbkrJESWeMdBMtCVe+i9liyBhwMktCiZQ2IjB8Z6rgwC9zXBON"
    "SqJWZuroWJ0t1Og88GqN0NUrSNqpmZWQYHT6WCrGcs0ELO6SP7vArdTV2eo8GeHPDb1utz1qNlsZfSfpBN9mxVP2SDVhjxaBwQnh"
    "9dLrLzTsFEXQXeD6PkYD6VlzrtAmTw+9I7EzAipA07Ky07KyriD35gTHBFfdZhFXvOhUC9ktwP+emvZndxHLLegi7tzFEq35tPb3"
    "NbthC5WQgyOkdm9Ra3MMfluzi5Coo8b8bcARP62dW3W+8XIXQ2FD8Q5huQh8/1zrpn05XRCfJ6et4owJc21h+hA447ta4pPqzqZ9"
    "VeVTXavXRqnCZBXNN1qvni6IcvDI5QuDyl7V7L1rrEKXCC87mdO93FeGPE6tOlotSkbTCfyReKWR0ht3cCyEonkuvgXyILhDYInh"
    "bPNkgd7X7CMSV0mePJKiJqgg3zVKQvyab2ZFT4xVyaAYC+EK6HhQuqnNDlbrTb2vC/leLiNrI8uj1/F6OVYY1SRih7IFq9TkziDZ"
    "1/bez4vEuQ8sAQtWA4X+O5TsYOEKMTZNmp5j0thOiSbuN+sssoBGT4lSVyVfw+qQGbG+InOv65oVA+ttN4+TwiqwUxE+Y54xSERm"
    "1aglqDGx38dmNd5uuetiEJg+Mf56cSmmfqrTZzQHF8txrL6SZzz+aJLX9PyzPOPxS5uMMt+YdDz/Kc/UVqy+lue6vaSXX+3LJBSq"
    "/yJ0IOALK6Anxq0yRvJbnY7dqdGM1Q/0Pi1qzZRxMw6Ozw7t0RbRb9AWgdU5LPO4rof1nqJfOe3049vAbJ7VtlwtR6gj0dvtw4Ac"
    "00VQnor+wI5cXTalGHXKQwMfBubK7fbLnLUZLaIueO8aZY30N+uTMW2qSOgxsd6QAMziZ+2avVPhqdLRtYQytsyQUY4tC7Y0IHTN"
    "d6DA25QSUFOSbAkbghC4q8mDDVMWXQ++6AJtCmr3DE3yg23+PDRY2dtnBNc40GE+VDnXk9V2e+lM5cq06vfZupnnSvzVAsXT2y/G"
    "xy+7e6CdPRWz6SLds9t1XEPJHm0d11A+robQxy/OSjpZojprMhNlgBJidvnPTwn+epM+qLog2XFBgcvkkh0ujoVhFu+LhO9e0qxK"
    "ZBSamMeHMdv/8eHn+trpJPVMhz1jW6w7zbv2r6wPa30nDkFchDHiaW9r8UbBtNpehcF5XKbd2OpD28/yzpzWPKfe4IjmtPbcmNgc"
    "wTcTNXlWnfOVADdYnzsLY54Or5UbsS+nAlaT3jmKAbjuJLVuJW2LNRQQmWqBElbctauqQ7sqfQY0zszHOTsAHsxKI25jaK5tFuYg"
    "szjRHGk1YplxUuDiKuLpkg9i1e4SlLpP9f5112E1Tocsgx+F98QWEC55Xzo1biLU3RudZO6ZyjmhpaVOy4CnZY3hUhjNHN6XaVd0"
    "l9SK551IH0ZfHxlpyUes8oEJAAX2ko6YN9EXoppz9ozw96Jid2a4+Y1oh6siOzhOPvs03lkevD0f0r6tBqMJtJvY4OLI3lV5S46X"
    "5pRbsPWHYEH6rCiiij2eEhuP7m63+XbL12n0Mlyk6AuPDDb+vRGRm1mTjEcPN+2OeL6oBxeD2Xg0uxgToweJGK4AMsS5xIFbsOcg"
    "XFBnn32awODG2QTfb20y8dYmLv6iMU/ZH+OhXW70YTEwNjQwDBhgzk7lnfhMl0fcZTOmXi08eBTh8eF9Q/Se5oxAep5vP82h6upl"
    "Lr2i6EhdYqPREHgRKjqOJHfDPWtuYhn7/Y/Pnh78dv7xAPYW0J8cV2XCVrpJAwuB8xRW2G7DituhgknN7Df0ESydjpOqcKSY6Leq"
    "pkj3vXQK37N5mLCT0od6wQ/GCoAYwYfQGZA0PKmHcmvLCaIs8jBv29qk8KN6KPe4nMKP6iHYQklgBvGhdAspYS+pXFX5VLxQ2rxq"
    "Wvl2gh4uC/OGJ/Ww4nj0XPklFk49pCmdGLsYKTiz9DCuFc11IoHlQ2g9vC0m76QUrE6/L0VWrY0lgnrIKvso8IvNgm77pEgNJmff"
    "MxKzEY6QWM5wCtaXdW1BNS8KcRi6GSV6Z4ycyvucYUuM982kvUnMnTizz0mheA1yc2FeqXwC9eMTRIiGJTmBXzJRnnqA1YKIM88O"
    "z0FaPnS2CI1Bzt5oJu66nXtwlDgDDirKSceJ096wSZ/apNolfWKTKkpyR+Ok6LorxXl6pLhuWySXGVxH+X7BY5WHBddRtV/iE1WF"
    "JWpbVb1f8FNVu4JTxIXkVGOuNE0b9IiY+xWfXKG777GA95g9hFoAF6+tUHexNFM0SycEAZOm+baCUQQHbZ6lMz7XrW+W4d/pIlR9"
    "04WVp4mDJR+KQq2Js/YfrjDX7IDTQJe9L2WIKUIoyhUAqwJoWKfKBU95FmGWU2a1ksJ2r+CcwuesndI3y9bFsQmBFs49iX5+FBfs"
    "Pe4oiSr3nTiHpd5Jl3TYpbIDyTV3sAgB2YM8A3mz26mJMRbzUr/6bAJ6Vzo+cSAv+28C16YFEet4AADJb2F+G/uQf3DCkQ+7sv3V"
    "XVCzMdyGBrFCbvcskPhC3FAEcD8pTjXHsXcNJR8YfyKMixPCJINgXugo50jO1j/3Pc11PEuFh5e5CjaBdox4jTkFc81EmJ+lvexK"
    "Ci4sfEWzwktQBLGWqXbGM6LKhk8Q0Vguik/4ROn3l0XUTSJKZXwBhs5BJgGjCe9Ha7vU7byaNoTKBNlOlDEwSxaqKHFYwWMU1zRN"
    "ZiowjkxWyppwLlVoD5lcOovOkXKyjuSWlsu/XZhPntMxW1e3yY2tQq5Kk1MqzTlUVmu1ti4wkhNFp9VU1wkNTZ7ewo8Y5ZQ+gb3W"
    "UVJNw4eziZN8RWtCCde0BeorXUNQrjHegkrcrKqG9qimAc91XbDSHsG9Vp7FpsNfeQY7obNQ4kE0yULv0tboCK2KaA33YHysN/5i"
    "A+RFY9eTNZfn7IadOdG0NVe0ciOS23K59QNcxsMrKS5kQPozRwlgryrs+aTqtlTZGiqwslQ8Ym98xt5P2sI1KyVgiyCRfoIMPgCT"
    "nvRxLlEOUapxpajMLh7eF7Hnlra3VhvtfNjAZicU9+OdnQPSbsjN3kNz2r2meseDm3SHNYnnRTTBkAqWZgXyS53O6TFbmBmLk8Xw"
    "rk96d13QEjHyMwRK7FWC2prxtplhp3QkH2sTnGoqMxd8j5jXdtHiBH5Ro+4q0qc/1WoVK3r4qoapDj38WKtLfvi5ViN++KJWt/zw"
    "slYX/PBLra754VcEXeanr2uCa376slan/PBNrU744U9io+CMPcptJCfd8RkBww6B7ylRWETy5l1XR/cvIaR/G7tILCfBCrXyjKvO"
    "cHV3LtBjt6ldy7JJ2ZJ0XDFnaV9bRODRlnmD6WGw9dIKkg2xafNbMG3YlaUxiLNbMZ1A/kypfJMVqGFbOVON9WMVeZ3eFKxI7DWy"
    "mOy34ltQIQUx+1dM9htmcMz+ir8so5qlCLjYru21Oh/NYZa8xYr9VGYfmtvy726Pors9Cr89EjD6aegLaVnY4++qjMzRY1znWac3"
    "hqyOk72EPdX/ebEvD67v2mki10CHaAyFQqtWMByuTb4umZhxJCl7leJE7fbL8I4oZ3rHJ1fQqUBSAwstbS1BMWLz6LAU9cSmoUe1"
    "7RHLJIPZuwzOW+Ep1WZZ3BQlnI+bABZwQN665EIZ3kfop9wsYrKR5G91falPWxidXBIhg/gqaXhlq3ARyAp7BNM+mtMkbZJe4exK"
    "YercqymV4GECGYnPKsLZGRFipC1biVkZv7W49FRybuSi6wct/iBM1Kjw7ppM1Hc3NjvkHGdb3u9zWaJX+UagCFtvuXWpCK17jzTY"
    "XG3Mjo1o67NzcEEP49huuavirIAkFlLQghgE6CZBVoEH1UKVKcFfL0UCqXRFLB3TMbeFoVCvqcPEjvKDpWdOCk/l0HNIESWnhaNo"
    "TosOSXNaOJrG5Riiht4tVeOyLPHiy1rqpQjIF3xZBtV6IoiLdV671MppsU+unBYhUUIDC4gSehMa7m3hiDiaI0PFXRQBoXrbFWG3"
    "mc5ctA4f5Yx3a6bDqGTiOEuFvgOCjDbeJW2ov3DRbeekiBgFK/oLCsZrnBZGh8O7iWtDAY0RC4cST9rahAPPGW17g+u78sbTPWl9"
    "FroxOju3Ki2sm3AeOgQ72f/wfukNyoSfXe9/JqcP0xCdpiFB5ViaCKlyf93MT+Bvm2UbOC4N2nlbODWunlW2fNBKtKWu95byA3In"
    "HXcFYG3MsmdMGDsahJTaC7q8vk3hQASawSLcstivaL7LAY1v80tCI3TiUQtL9tlCvMo+e5cQRrsfXVJGx2WfEdZf53W5l4TdUND7"
    "90YStYHVn6Cxs/Nwr1CVwV6hN+dI47656SD3jntfYJy7yYx/7iTLteNz1t1yGjdd+HDbjqOIs33P3IbvEDk2dLMtodS7ErNtU9Tc"
    "kmJFcJlkGiboUhV0xiZgEBcpX26lm9G6mCbPock1ctNCp9tIcGit2HVJTqRKLUtqXZnQOo6c5x3OMZ6Yk3XFMWxk7T3eKAw7z7IR"
    "m0vbe6fWzZ2Is7kxYYQfKTAboASpLRpcFuUDicSiXGK0kK/BvDBN54u4LIiTBQQCZrwYCFB4SgZNulTrm26x8yCzhyFh+u6gScjg"
    "Be6YO4kBjN393INf8HkncSenTySGzhuxaNlY1zmjiWaV/+32WRSq5a4DuiIt2Mqkd5g1xuqaX484YKWNNVL1+3C8sFYIaYofWFWz"
    "d6jFwENBmqscrlvXekT1j0bQ366idaCtRFutKs2Rh7munL9qe+ARUOB+gEjSCnVbMFJHn2HFxNo5aDKwzfCJYR9it20701s4rzhm"
    "ZneqXpc/F+3cTIun7t4Vw3dFuhh2/CB7l1uUh5hWdmoXsoPfiemdelpYNalWHCJRd9nR0Xi79SkHImgCAY7Xb50zKn02xjWNSxjz"
    "VTGl4ar4nuRc76UH9/oFX2JKUDLWbwrchIaq95AWyX0C73PqJ2GKmi8t2Xq2wSxFYyFtkjFHje33n7Lk2IgW/0VUHUc8RTiAJTvv"
    "qi1vYfy4ICPiWOyqGcg1MJfLudwUjpzl/gvo6IyoXFp8XJSb52uwAefD3gLm33AkZdJzzRm0L9kGY0GH7WcqtwZbVOjR+HsCp/G5"
    "8YnAZyFfTWAW3BMoCa+0axIhQTTzFKZhF7BPKmlK1v/b4n7lxO+KO76hyuzbImkH/jxADObAPL7wwn8X8VIUE6QXcNtFmHJiHKz3"
    "vBve2rnOKFPTMMw6cGfMe7cRCf1uCK6htZjNuaixCS5uENCqofPFpt28IF3Kgn2/89XOK0b0JhnzbMbWNTJCVCNKjRC2KstDPgUC"
    "KTm5EvQ2B4MSfl4Rbgqowtedo7JHiK+Xg4yCkBsqUwKexwjBxLuPYSFrafprvVrklPcxkh5+zLcFHHXx7PB80FavqmuYIRGExY9a"
    "J0BnWTSxOVpicEqUxqA7X1gmccMC8VYZD8OK2Wg6Qa9pK3EwicRwJpYoYa1svpZrlFzYTZhiSBZWmLk2D0JCOH8Lcvm0CuX2S5bU"
    "z7uyykvoh45SdnAIH/2M3sSJtlc2tbKyYrutEbVqeJW+yqO1i46lpmqmlvA1EcNT/2Tn+GxNXCAX9nZtmY5mamMHYwcng4JUm3LF"
    "nJxqMpbs2SR5BXcPO3PnTCvrbprTQ3XLIjm4VL1Kn0Wnxkb+Ir3CPrjt9y97qdtnunOffxur0Hhil14MtQf8/r+AigDLfJlcgWy4"
    "Td8U0S2HUbuAFciFulUSaMqpLJTsOA+OW6SAsaBhDviC81L5yeTHMhLyHexd+ZewqLcSEFuFOroIjCUuCNQuOqUwAReK1nJET4E+"
    "YiF2AYdW9fov/OY6kZbE+36aQx9ErEedpjo7orOGL7R7rg6K2dio6xnECI/Fu9AKq3Pt/arwznz2ZWpyycphVOhs5JemvV3goIRK"
    "H9YAerqE6mJIsljTyHNx6k2xZ2N397K+Ykq4Nrv337j+alm1sJYr+oB18Qj7fRH4JNtYytcZ2wTMNUQfWm3sFVjgOcWZI8BNONEa"
    "MJwD4jabnTWQjZPM0PLE3zOLD4LJE+Pld9I/Ojz+tJM9Ccx86uxZEcHZ9gJBqirJ/tz7LTJeT8BVNf8RJEoHEj8VkRgoExonPLvw"
    "95oIrRouekT4gm9UezSiXjN4SHQD1Paz3iH7hayAj+usVxFd2umpqS6I8vSs6LqECzexRAq2Wkq99H6NHT9NXc/H9T2Oj2vIlHCG"
    "MlanbUZjBobJzZhLH6iTxny3tz/t9VYExKJjFV5SC2Aj1DIg8gqi394LWA4WccK+IQJXq0W0kVNDGw8qdIxYIyh4QKuNG+vQGbw1"
    "tBJ8bgrzza957lhEiTlgUNKpkxDJR39qxXGSS7bRhMsxoykseV4TWSgmsUwWZ/j3NeLqNi44fixAvfwsivddxvrHIlZfMsr4i0jd"
    "PxZ+s35zR0D5gGvP05+J4R0aiva5yOKbe62cv5YqoGnm9wbjj0F4QCO8LSdDWarADa0h0WwjRNbVWZF8idiwidEplzOtSHJlNBPS"
    "PIin1xWiGzxSmNM/N6TDxuMSFhAT8S2xhEGIdrtIeEYoQngdrZ4cAoYj9pXESKTqB1Z1sij3IgaJjXHXQ7pVVpxFILo6CA2CZOf8"
    "3FrLVlx2wm1DeYTKwIV6Thk4beknnaLLhx07h2s6fYc8v79CRg2nQ1NRJDYY5wN1GIS0CZaT2QRr1lx70zi5aoVC4pqdvbEBPJF0"
    "tNVRNxQTYL2A9Ekm+pb5uaPJoVtR+1e5os1dd3OrNarF+5jhVlFEYhnSl3vXvnncSpss4jAf5LhSk5EtJDqo1W1pjG5LELmwsEEu"
    "nFPlO7ABvWAlISPiDpgbq1GmaDtrSMgAevzTYS7KP1NWnY4Zi/cqLyWZxll9Nj1PF0k0Mcc1v92FEmhSyx6iESFuMKtEy25aoIeH"
    "fDFaBXF1Ebc8nSCmRvfcqu6cW8SUchi4s4bXAjcRjSpgV0MrAY2SBt6Crdw6cDlbdLVNrYamqPpUvY4PQGiouGs/q11eOy/vtlhl"
    "r/8k5rOhp6y/GdiVDaBY9kUOZ1i3LNOKAyRg8RUIjIKXTMCEoNQqSW2cO9OCqBhOT40UXvyRE5sU2S1TQ91sMOF4E/DN2DBWXbGE"
    "aFcRZhPqt6czoNGkOjs6ZwEivIMSCUi/wmWLVnlAANeM0H/5AOv7W8EuEQqHmvO0yH4pknrgJaTEyuYB61tZkqYyurBWp2nBYdQg"
    "sVzdZXs5cvtmlYqC3hkt5nlqGsf2byKeD5p344xWXKgPWQ92nwmu99nZtsMEt3+TCW4ZknsTmtWVHZMwsrmPglyKHvYk3rNvndxx"
    "ZlfS3ptw8IMfCr40jRas+e5vTe9oQjh8KjP7A1+nmMpYRaJOF9h4UxYlQ6CcCdNa7hIjVWa5BN905uzEIxXSc0owF38gWsOjR06M"
    "BsUVoiFERaRlZemhVa00HpTGcKBHlRoSAjlifzxmn49A+jy+nGqRQEKsch1UQPv98DzNVU0wm1YqysGU18Eejd2qtyZKxTI9W6iZ"
    "o8+6q7KM1TIIqNrRNA5U13pi/Ma2MaLZywqjYzEsGY+I/7bPhhYeK52jYHDv/iqPkzNwzPG5avPA+wGzBz5iQGscZLyLrJa9ziNj"
    "fBT6LRb//UeqprXL9zzosOkZVML2FRuorYcAqS7uLxwCxMTHrErQ5gjQDKGyhbmiixw1IyMuy3H5dnBBme+7+IV4Zmj0ji2a5PJE"
    "2hZht/cunhAXrEddrRkPaTaZYCMJld83WK5fqEAW6QnB40Udnxx7/mg01FlU5JH1yMgBbgmIRmN7ipehQSP8O+YSUVZV3LaPRmpI"
    "98KIO5hDrFj0Jhpgxb1dKLkLNeERVrsH5CfUn1yJDgW9l5anoqUVrgTK/8YDE/ByLiilSTc2hPTRzqDUPWIDkwiQZ0G4uTQKiI6d"
    "avL0Ig+CoubBJljkHRUavBqqgzYpDDGHuBD46ccXo5FBx9ZtZmXckVr2GCcQ3FkyLW48Qu+5g9xztzyFjItzZngy33DCKnQ2uVSh"
    "H8o5yhrDguSS+BfpDyRlxcS4d0hGWKcrASPrRQ/XZfip5MfFXp3IO9FmvfaOQ1FjSsxuiq3oWHyBmfC6RXrKPnhvNatLVBI72Zg3"
    "t4EjgzQ9OBYKFhqce+248nvpBEE4jO6m7ifhSg2CT7bK2a9cwiDcTZeAox+oyVLacohAWDnDijmZ2wx6IkaZfW2U2W/y5NbOuXGX"
    "Kcrqp3lycW/GSZ7oLLthi1eQdGHeF0mj7UeBx29TxG6LWf8oO7mnGGV8lk3uqyCJKOvT7XbGjkng5i10MN4pq65pd0ztVWye/VFH"
    "U2V03GZUCDaIqtcSW2B3ns2038BNABcW2BMEtFO3aRj2OHBODQeXxFsT++DtWsQjT2Cs5p1H+1Ls3XjiIATxLoMqCHVfdJrU1kOH"
    "tDcN2ttu2cs8UJVraGfcBdjPJXSHdZt5zu65O37O4VY1KMF+wCO4wdXWDW6760R99rbN0CwfxgUHbCWq17jh1kQ6V5GJ8cweufZq"
    "c2fSfk2l1NSI0WQ5hOAJLrju+pN3h7UxMeLrVOfM2ifDd/V4z421XcBSR/u1hkuHWQGIaNyNNj+t9ckLOA9b8DU7y/BZ8jK60JdF"
    "+ZqF5lB2tEyw9R1vLy+lMJGvpijO6FJ3h9aotZ0biPuNYGIZ7OW58kLL5BIX2g2jUKYOucvpwlhhUX3Lfn85KNgZ/bz/ebbClgh8"
    "IM3Zzet1CBBTgX50Zy0eyLhTatTvc1gekzs2KloIYaBRK7z0CKan8gQDy8BkDYffMmZTbrl8tVQcHDdMrWPtJetDY/uYUvhKSpgE"
    "U87oXVLPohnHa/0JB/8zryhG9T7Lo5noEe53vBNAiCmuq3RG5JO6jIdX2eUg9Ow2jZNL6uvlwLl+g/+Ss9scF5EA+KmQLbBx4ak2"
    "fbHe07bbq+12hAM/F6+oHAQs6J266vcvB9o0dmeSXfQhB0Q7BFuBe/EAbsxWIPi6FEqk/ivjUpSp2bFZ15o7kGPiuo5Qy1Xu/UZB"
    "Ymk9MolBdxl4XeIz1zEfQvARacxdbB1ctB1DQ0SPEtM2bITre7Z4ehjSoot0Mlx4ofnC8mfEqJ4tztMme0PgSk9x8so8DK+EIZ90"
    "KwaCLXRq5TYm0ew6I4ZlhBjI/9ZqP5zEVLYeHa3lcL1lzw3OJ9NnJqZMcKs/lwik8nI5FDfaU9C9cIcfXabzLhyLWqMA8iVuAgAs"
    "MwYPdrSg9mJcKVfdofhx792hOzj0yB4B4cT5Ux+rLVqnhyKzmhpaJyIcUpa6/urtt6/6/bl/sTGTlgOocRjwQIng1eDafn8VLcQu"
    "LMv1PUEEpsphHRDZCu79iTnWvE6LDlaSfJ659RO5pllD1lpBzWip5hzYwtvG9Y+xNfm2i0Y6lycgFuqP3IFJ7SaHg2Igzh4XkOsD"
    "BJHGA5WRXy7zuWci/j/c8xCtu8SdRZXOwfBxbJDC3MY5Yyj0AaxfxZhxt1sjlrcOKYkyoCQwxWVASWAKejRUR/J0ZygK4U4gCThr"
    "FiCsy7+AQKNwy2bM4AX3zrIq3L0NTUXjjeKbcPc2kLa2+FmnE9p4hDJzeCufpohDNnFGxMSEEjEPsnC7nYQ+6/79eZwtibJNStry"
    "IAWDQ8zQ+VCGCve8xZk0gaKig6d2XzzbY9ksZPmcUPOC8BixfsKpgErufFZ/SKpbsS0/mEe2QYc0ut9vw1NRKm94tWlK/TlYS547"
    "B80RWLujcAd1vn1aAlNlqQlDiAoBs2Z/5LMgkklmqT+TF+C+1R3ct1QhIk/mYC/mrOgyySb2pn1O5IUjtbIIZyUThxV0D/Bw3aFj"
    "z+DFYhZ0PE5WTw4JpIn+p+37N1kro66QEllg3FtH9yKbpQnvw/78xTlCz+CygtYEAnLnIIz6EIQ0mdugHmFfd2qiP0Cjdg+9tHEz"
    "0nadm2UFzAYHVt3cEKYwykzWXTJ1gpsNbgyBidb37TrZcYF5TvpzLgJhPvXZWyarjKFJUW3RdXoNC/E8QoQW6Po0A3bY9FyLWzG2"
    "K6iJ1CUyqKZEKjeDUQNhwh7H+7FOcO3EiZrI8CIye5EpJToSofozrxawM6rBrogkZaapQu3jLrH96B3hUhsMKRge+2Ky98FGk8J2"
    "HjYag46/uNhH9AHbH/Sn0zu10kYsZV3ESTCAlBhP73hbxFJ/qz4TQDAlbmr24VXzPtECL7xg7tF20qqLdVKqdVLbG+rG3FZOwASY"
    "42WeG9FzSWNleQL1D6gVY9LG+qR0UyThpAO3WMaDf8cTuQBAx9tnxs7GijhZIBzk0LgPSz/9XJmMnY9KLkqBrZoOp7kEnFJtdm/H"
    "kjadQBC4wMWHiqbpnXA+H6SUpnxpiaMjlzhTjHdnKeuGqRW7NBUq1z2lM3XFzuuW0cqePSuanVMNv3WazwrF3Zyhm+vUHqVfAd6Q"
    "xrRXk7NGwV911x6w7nANO1zEXp+rUmCXG6Nlxmosm4tlQgc3QqfJqk8Vu4OYifW3cUD4XW30NNwUL3gaqYu9JfPAE/h9/xDDVNG5"
    "2fq5UzSEFzrugoSdNZnRF7xpbSLPlngGHC4RJdG4fBNvsTrbT5ANT+ttA23N+KJsxhdl87w5nefT6voNjTOKbbKYyzAePwUhxs70"
    "ZE4y51yN58TqCJhLxW7PLWtQifgjWOUKKEnshRtEESjunTu7MZ0ge+jXFNOoeUWjEMcf//Oz7XbKbnOmzv3b9I5wnIqx2+Kc26df"
    "9KAbZUO1aZmKjcEOUQGYvxrANsjd3EmAAb4bfKnZ56EtNZtZxzap9fdBG7BeGxceBIrrlHe+pL6cPS/q9tZmDteDgkBtDceDHJBd"
    "TcJglzQBT0sixDwMLeD2eRUi8g4KH9o7g0AJeqgtnqRxM8LlpRKdDXMnyT73qlw8C9tDnZI4aO13rGf5A3ucnt93LuN2y/F7OqSn"
    "MfgsWI7kUGFDu+yALJoFQpmlMTKfGW5ExJWbEajt6b6Eybs6nfFqby7/qthu2f88Y/am379BQQZVaGIsQO8T30QYE9nZEn/ubTKx"
    "H7JJLFX2uXwKQm9pRED739DcXer0HpEs0MB2m5YQqKalUfa2PA7PlnmcpQg5OVgW0NeeAv2KWthw9Xg2XHleqGXvmGDf8cTsOz/Q"
    "HtX0y/0ypLbtw279ZJrdeDE+KJZZnFxH+zLhGQ1j9KFhSNcPu322Izk4og5PD46ky+vHKbE+9Hc19CzcWvTN1q73a9v7tUhX/uBr"
    "uzi+ktu7/VEEOlzD9aNHuw+3NJOWPjBP/11Ls4MDtTo4YBz3ZCbM82O4jhVMtoI/t1Q/nmawEwazULgpoC4ZvPmhUTOf6NtVGJa7"
    "J18/WcVujMMY1zCYQ3sTQ2W99HWZrtWc/l+mJvIQd2KdzqUfax+q/oMLoD1VDyEbXzIjSa1Fd3mkbmnxL9LVwZzGfAOBxykl0BEh"
    "/uQuYtPmIbV5wU1qdNiA8TpdykDWIVu/5pvb2yfpRbyhAZZ2dEPLCe5Egs7agq5/cZFesipGKd6+hSKmRkY04BEGPILHPSIK9dno"
    "YH4uke940duz0TlI3nRkrvILpxKThR1I8G2Bb9c02uJJepqdpkVywxYVXE9xfhdw1C21y10+SW+yJSFcDS5bunbit8o6vaCtsn6C"
    "uTo4cG4fHq2V2JuD1zzTj46gQ0I/BF0zS2zRvi2GMrE0qswAGDb9KrwIuoF73MeH2+2aUN8JDTq7wuhQ6jhORtQoxIhXIbqXqTWX"
    "wwTIufUHFUjQF153eB0g9KmVqPc/i2EsdtdvtA2+4FwOM8r3PvMHHP/xTqHPPo0ngyA0JPFcLnci7s6rKBeuo6vnsQ41U+j7tQ0S"
    "SPVXkQtF2ob2/KjxJI9PzenbcQZ1TNQHhEkL4Zcw+fEiFHT3cgSoyGx3kmjRkY1DBGeylCF+FkaSnYP68VcpHBEHTox8LAnoWvr4"
    "MROE711bEhM8aWAulTXwFmubIq7Q++9FVJSRi7e03faky8MwFf4cTYwV1R2eztZRnCDUGldILwokXgSHGcMigx4bzi0OLSIz6jtx"
    "6+EMeKPwFIXcwXrvTLiLbTyQTe4IUxYB2K0D9XUrYFYTKGu9JB79Bj599LICucHQGU35qnq7BZlvL4PlphvEf+MceDBZ9AfiSJrN"
    "JcQZSCScy0bywVPP1FB702MZf9QOAsMXnD/WSHEN0gUsDlbLW8n7KBwmNjnLK2eExnvfsS/qEXujwF5O2UFhl5WTNRduZITAwWjo"
    "s/iiswODK1YR/ILUCjaeNW4MjDB38/BipXXCcyk55lY+zYzmcCd06zWcGiew7V0E9/bQJP2CqHkIqHhPZ0xhsZeFI8G2uQk10f/k"
    "808JMol5ZhE1E3ETE5S0338LlQ65g3Ke3M16DO+ZJm9DuN3Ot9urQFA7Cidtf7jOwcGYb5wi0TdnTo3B+a01FbG2U7jktNe1dYgv"
    "C3CaORt0fWECFfWKePOiM9vmCokwz0azxkWBUuHmKzqRaYpOZJrQIX+V5hlHkEg0ke080DxbshqeNJk0EBL8V/Wz526e1UCETIW6"
    "dcQB5tIh5mp3KXG5zCcqYXk0+1AbcrR0OqxqIBWDg4FN1IuuHpa58/6rC++LPcnX5oIjCDMLR6iTuDPCMOYgIhxDmY1awtGh+De8"
    "ZPE5/RXZxEKzLu+gaasVTNFhuu0cvRONUCkjOEsq9hYaxE2xjJlP6nwAEUEDiWFrrT73Yz9KWMjh2vkiV8xVY5A3d3EoQVbnzo+W"
    "f1j5C5SKTj6mGqtzd/e5U6eaoXc/YI6LNaj/IshIN/CN92tqcQnYT8Mvt+zNJjfxVVniCeIGwaQeBiYn2Zw92+zUSbiGL414zQt/"
    "Rzyx/f4tfFPJi0HObMlGKOTKZWy34pIOtbki8gdSCymU6h3UXexrJpg60Z3AQVk4FfA48GMO0R2huXSzSq4ASbeaQOmK0F7yVi3b"
    "ZE2vk+RarSbJXKvVxQSe2MrkVKsKXhXfavXCeU2E88gzTjlPi+gaKpIbY0F5ol2UZyogygNPV6vk+yKirLc6DLGzziPBQ9qcou0u"
    "dBxolT1EZW8MRF5clmJfYq3ZjKqHKZKXZQWds6o8uOFUCZdWTqopUwj+OXClNG+hK2KnMfCwMaXuiXyFOoitKN0rEfXFbKtPjpWL"
    "pfApSG8jRk0PPvnE5tDLPwN1vlkeWtNGMKfV7Du1G7ie+95rPZ4KfGrld8ydA8FGEYgxrA9q+D25o09c39GAbtNaXNVBrXiYd9Fm"
    "L797LxMRgnGEzOOUiPa8o133yTE7h+D6UmLc8Et4CYdSy/sKNtLBJz1RyFvlbDOCkuZK8CZnJxMdzb2jTtVS3FWce/fE3HUo+EQ+"
    "P/TYlYc+p8SMERv+7PC8I0pyyAmzKPY7E2+4MxF/xCDFe6mxKESchdKxTucK7pQeT+JNy67FlYlTUgcsI6rOO77MidnKH1fDuEnz"
    "R9WTJ0dUSXnWnFM9WZ42j46SKm2Gk8dIzc/ZxgCkSsRNUBI1S2OB6QwHx+bqbdVohUsM84ODJ4d0RKFchejFsCu663Fm3p2p/fA7"
    "rFAS++jQ/lqm7V7LZG0yh4Zy4Pcrt7Gj4r+4UtfsIN2cZ4EDLfdxeAnjcXyQOLSdv7/TVFNwbtwJjua9w3et8LIR9GfCFHE1LW6y"
    "col/wp6RTU3qNvdxnKd6putaT5nZCt0eXhhEwTisex3DCu6tEf42zuBCs3JgmEgp35ZWi/6LvQATs0tQxDf5XnJ7g+TT/eTJEskn"
    "+8kNomWo6xxmI29Fm9cP4WWkGUld59IdKqAlpNJZGJEBbs25DJMtVOg6P3Mm6QSgciyKE588PQqc+OQmRlu8eZ4/IoJVPybof5sz"
    "8qTWQr3ZIHJW3vFtvq+B+5y2UPY2p0bFzQ56p57zvkLNb3PnpiZwb/Wqa+BkKqeW3nek0mzY40O+BKpdwSfPgk+6Hzzt9DwDVF1B"
    "YxEq2exuJgkNZ//Iuy6wLEqUexOQC+yrP+VbcXGwkacRO7XX0NzUGa+V+g6pYG/h2HU2Qn7LTwQCdF7Cne7d6BPs6HE8fqS9agAv"
    "/CV7/ClL/mHHZpsieU+DpdrfUb2zpNcrd4kONgJPodwNmNCQiPfgFMglWN5hwsYzEpzD4uRNMD/w6Gi9jeO5S3goHlW//y0QE/Py"
    "CHzAL0arLXlWdrUhROXMBYgMbNZFl92ZE/Ob1amzr1ajTt5ZAiBMnGfBhBYULVTLo0kZji0fPnP0+TDhaVC8MWr48Ih3GAgh8kAI"
    "UatQsQnu1vekF9IJ75ZaRt/e0NrtvOPE6D30dhArSAIWEmENx2OL4r2GCRbHxQo0erYp4iFmnydwRCRbrFfJNqNirndPQFj0wVNP"
    "OrQCAm7a7chOFTm6UPo6MKx4nf818JjISEYx+SECNWuED1S81Sx59dLphQSHwPuc/Zfbfuem33XImxAeOaMeFhDqsG01HcSJ7TKH"
    "e+6EVVQ1O9ytrKNU3uCTyferton5KEi/YNMedpEPFTb4EsftKOKTtmwFcSnftqLilr7laDRXYs/2W8u/PQmlFno2a0XbLZ2zDaLh"
    "yNmp0FFyxeEUaDkTjh6DgBWw58o+Zedf2XHioneEuK4SbBe4benirt9aE4CRmJk4+bLwb2d1Bc9LcbIfN+Klp3sDZ5nWpBt7NoTo"
    "jrOIYFdBfQJqaNmP8KhADbYxfb3+G7hCdK2lvQUjjAUjjIVDGJCizWDOnGfG647RkWJMEidnueKn84R/wNsb5BIoVYc4Rnc1acMR"
    "CQ6gTvFDBw/YRH7rIgSbJa8d1KAHwVuAJgLmOZheOFt2RrdZxQR5dvRZUm3xp4tNukbwd1DLXa2tAM90vLUymmS3w90lDXBvKD90"
    "KNgTcQEiDkLP9vuArTAUbYCgw6izrqALQ6sC8jLpqgHBFALCo9xOvZHcA2uy7FVN0LWJDiW/MDC2Lw6xTvr9mp3WrNXExMJd065d"
    "B04ycNo+GBOqO3Sb7Fl0kysrUAh24ld8Mhu6yXvGkwg7p/YTAtdnwVtA6nQ2spUpBxTAhbEbzVgvLGFi9ZkN3eNYrDhhFMva3GjK"
    "9tWG8u4QSl2KTS+cco7uMo9HENhAdJ7p5GXXjO59HkadOQxdFdVGzG5VmOW8CIJM0t4t06PPhnvBtqj8uBJxhNyt9D/7p/cXYs3T"
    "2buBBOgpTRAixZ0pI1bOCnIOfYDUTUnH29Aqw42GPQKA3peFOHyFlWn6vmS/L58gIhPV8L409p4SVogKpfDPRT/HKpilbcpuboLI"
    "XXM2Wnbd5645A8fWa3a13uyxVSNz9Ct00+jG2SjsIKAgZo8wZwRmZz8B5dHhn34+DIJ8Q+sjoAQCRvNHYWb+lv/ZwCnMsGOHUsfG"
    "SNCofset0wyvrWZ4cEyemUdlMs8Dh9jau5eJg5PyzDzTJ/x77r/I99xww8obMpWCeEdof0PTWE7hIHhpEcd8F5+WmXeIi9v+pEgK"
    "C/ClfegZKoG/KKzrdygZj20qmnR+BAKftc9yJ48V2+KrkhP+pc4o7Vy4xZ9ycWj6VR66TYUY0W7ErwJHK6x2Gvgqt4ZJaVRm5eAD"
    "+By+gBBPeAMB5Vf5o0fKOuXhA7ewOnBlNx4KK8QJRecoUSsjFxwjQjt+Nh4V+RkyPCnN8nUoHPyh+cLQCC85U9zISUXiRz98ee1z"
    "vZ85+504ssWIP+DVNncZsSqmUhS/Z2MJ79wJBiPUauCPrutJ1zIO1peu7YT3d/cb3EcSLRs6CEm+CxLNwMTrYlCBc47Rdv3bFZ34"
    "AHyQteIbr3WMlLjWaY1xNjOK/Opd55mXDifhjuraPRJVVGe1lXzQ26GyMiXDjYRCJTg2drpz8uJuJuQ1CPiKhIuJ4WHk52Ipv+YH"
    "yrcMPubHJZuHaW76YFapvbQPpj5tfhvprDvKKxz8RGwm1U5VHN0rBRAwTFeUgsVI/yiM63xWXYRa4ETE+/Cbpyren18a0+lvcr6L"
    "+TJHzD71Z66+zofm0hy24oR/o1Cz2vQjEq904peHg+HA8NhEiof6NpWvvZfBOnQ0zxEuEziFwAG7G/6Zp200Fov0l9+dvn363cmL"
    "0emLt29fvDkdwb4fvUt1TD3zBU9P3+yV+QFleGi/5t6jXfplbqfuz1ycEHs1SGWVVb3KI80Ae6FQv8i8bL4kpuzLfL+I0V71flS6"
    "FMa+suan3K8fwC/6bx5a6ZMRxRMZ+bVjz+46tdvZSzbCitzc8Bvxn5JDGTdnK39VEiVlVVnzTFdMsxgV1yDMI7UDMqIK4r1WIXkj"
    "6HeowyBK93rmMtGMWPmKcVkklOmikGHwTgWBxHcJhN5dVGAWjQb7OA3AJefYewyeHDxYwy/2iICOKNFDdeaCaBHIVektcUrsPQXQ"
    "ihMHwVepbkTUFmUCE1WEdgKHVhEt9l9yWmJwxc6DNSeXtOSYHWLVYYPZiq1y6w0rZep2O4Szbk0YGuPz8tD6lWJ/AUTl128kTIr1"
    "NhyNf7/55KR3QP+ejKH0rp2YO80NFVSxsqL1GlPKsgSBdyvrzY6d97vA2NTYy3JRlFqazMLmcWragC2Ji0HkMWo6KUHDKW4sjCFS"
    "VqHrvMKDhdS23aaFe6yHZsPxeg15ndmKtWAy2sweL1LLNs3YEXVlBdm0dJXE+AtljogXF0SKg7JADdocGCeM2MUA47zZ8wkSQqR4"
    "5SpgqyJRFU1IRYmDKEEQTfiolhGCObih2rLZhRFGqqrLSUi5zD5xg1B3dY3T1D4Uh0RcEjedHC/EBjEUxyl2ZxqHLpzaFC60HULI"
    "sT9udrIeOiRnDzHGY1dT7OCyVXak73JTOYej5isTD2JaNMRu3n6XL3GHyG57EvmhCjnA6AgvvqZJOHjx3D52AiZYn0lkj58tvK+F"
    "LPwhD4SxCwdSAI7v8+jAxFSt07y+XMNbSOPc2hmfObTqx5nAbY8DMDxl/8HPrOIKDqLkmaA6l0jPUf3kk6w0wYNX1kehMJDih8s1"
    "Cd1Aww39v+x9aWPbRrLg551fIXk9GsBsSrwpkoI4jmwnThzHsexcFCVABCghpgAGAHVE5PvtW0d3owFSsicz7+1+2DcvFth3V1dX"
    "V1fX8dxT4i30Ziq+UtZCGodh0HXpUXoRO25zt73bartiGivvI/PYkTe8GziF45sDdwE8NX/vZskCn2M/QAFyMjqPbdomsTOPJW19"
    "F8MI7yz3Gk347jkNrWgpxuZKxnq9pwFcxc4UNoRzOFWVsSDpwWAs0ksY32WWzft7ezc3N7s3zd04udhr1Gq1PXwZFxcb8+u93v4e"
    "6mTTP9+/ccWZnpEfTwhiOKeh+iHjCcTOWbyzc6ZGIp2/WG4WXAGikfXxHWxy6WzG1PTnJFbuwgXkFxuyXyd/NPlxrmw3UMw2kCIz"
    "LEKyH9ojRW81poMLJmKZdgJRHunbY+syRnFiZqgGbCp1QaWitSy8+YYpvmn017O07JevgwHGNXNJMJPsXgG3HM5nOpJWiNQZmeTw"
    "fAFnravyXZGXxdjSpiseDCCkOsUEhBCeekUHPWYpmUZ6RdJrj1JAQsG7H5BTfDRDK7nyyUuZ9ttQzvDww9Ft9e+Cvx+OFZsniD8W"
    "QXJ3TCBBSReNsZAmxyglmUwDgyKQMsGBktddB21yHsiXrOA6jBepGla2Czd3thkasCGjhUrSGLjZHC0rQgxKWBuyYI2gjuc/apux"
    "q0popFh/ILUSr2PDQv4qZm9+hJnuAfw5fHofrA5wox66RJw0SroH+CXz6dPtByqMCLQ64XkPpL4utclOArVvE+VEfHcaJmrOrG9m"
    "ptgUdAROeLm9jDzgucpbrwwRoSOHj+JhbIIAQJ23JD6zFmN0dAOEKpfYuuI2Rm2d8Mrjn8dx/iB+TS/KR0Bo6ERjoRJLBOT3JE37"
    "rDgkXdQJJZjarq2Ev0io1f5IFn9LL5KC2d+xINXlV0l8dUQvKLIQpT6nq/R6+oe4kIYg9dab4OQNbXBGqRHSOFxrg1I3NEHpxRZW"
    "4ibmF5yLBMBliw+xg979rQJn4LgfDLArP7o3SABtjIZ6L+/p+IwLZ/sdwAm5BHS5L17GxAng1RCIhfSqZ8QRCCwZBQYvp/y9Ei9i"
    "jsIti6vI4bnLemRx1HffvE9RxxuEfjIqOP45ilFXOXdVTlofgA4UXKXgy4+RJ3Lca5dxJ8kRIyzjgOe4T++jVZWSqxhF0F1HiLhQ"
    "iNU93CJ+TApFsthdQ5UZhnNZw5OFE5eQxHcmZQyZysYpWQ5yDV3mhUJqkAXsuSoUgUHig9il8ylGj8cXzuXOziXqPp3xV30s7uPo"
    "q9weoH8t4oi/7tTXEUaTmc0onmwcsfrsrfrKM4+Fauk5TbYfBA62Jn8dOXf6R14JrjfnaBlreFDio+ssKHTtJOJ74k2Hfn9iq+9F"
    "PyZng5GVO9OR1bXlAN7gqfhUVruSf+ewDdAdKepNIlKbghS4TA2PEALsVzGgC2RkD14CGIGhFTGwnm9jVgb9Hn1kBcNZH+6rv/M3"
    "jfEFgny5fBWTOdsF2sLb+WM6JBYhj7sDmr8WpEX3e8xOm+gvWtEXYSsLB4FReib/Lqg0r+ENCxLUGtzQ2SdXTh3TJqhq8vKPE2PH"
    "P/bgdwm8tTUZWr9LOP4Zk9DIor9CpuYQCgqGHJZajd/lagCgbhlQKC85I24eyZN1C7NDMcJqDRNx/lFA1tHmrR7qnBNEVuuollep"
    "lapkga5TRGm+T5GFdGwdc6GVqWoUK900+bSk1AfwfUmF2pRH7HM07iH42YK+aYPaY3UvxzTFgwKC4QU6Vwwyb3bToPDw9buUDGW7"
    "cCiEmbV3klb2CmF46bJIrx5vwjSjUF5I/q1gdIxP8fzXkRHzbFsWyHv4/l/tQVpeZLYWJWEP8qWM/WTiK1K0m4Z/BnoA0iTF6Pit"
    "nDawmmn2XLETrxIg/YxXm7MC3Gd4+3oXm28br+JyxFVCaP+171Qq72IhBYrIUqoMjNjDdgbRdmGBkR8Pr4J4kVF8+dxpYywyTpd2"
    "//z2Plk5rxmI5HZZu2hOtA13XHGhR1ewHavcNAzHl9eANQjXAHhRC21hhYc0a+pkdDnjF3+OFVCpLA7RwB1tnQbGINky6kDmiLRS"
    "x+0MC73euKGQUZA5yvsxdHUkI36y4T5sDoqZZGHUYvJjKNHEFVsu+T+24EA6j1cv0PbCRVGhTpEntotywjcxP1yknH2bV5jkKXmF"
    "GVYgty8LFpT7ALkpapUCJM6BnyVF2QV8Qk4MOUrhkK+Pt/FwJkvcYgmYuTPRJSxf2jx7txhSDfvwD2vQ5mx4HvdvY75QT53FcMG9"
    "qcb7qo2+9Fgwd7jEzs7eybk17BOTjNEalxh8DxLE8qm9B/e0NLMUWFQQY4BkFstHV/1yrHyDKjTzDTSbogDqg+qhPzcoyBu5lvIO"
    "wYPM/TjZAWnNcoxOfRPWMEDej/wtyyPyPdBMuwL/EptWeMqPi9oDcA1YAA8yrPWZTbeUgkBNVOu2jiDlCvjfrmvbz+pB03jUN1qz"
    "UCEyvgE0faHEGkq+Ye+ex/4dSv8B5b8JwotL8zU0LscXQVqEgdPw6WQIpBbDu437I/pj7/4eh5HlAuqSPJM0G9VONG788tG5Hw1L"
    "11zliSxDPpi+iU3P+NHVvAfFaMX1jZmSXkLKR3UzctPL+MY1A+ciP0+OotBU4d5UJVzBOT76iUIW0Fu1uiLgAkRw7YU7qdsv5SHf"
    "lMHV7rzAgvR/liJtFaL30U4jUsWNpL0ohSRk7yhGLRHPfJJUYOQVs4EEGtjOtp1t8r48zIZWUhqMoMHQC67uwu4nfHRCDpE1LlMH"
    "oq/GTpZXhmGgOQX7Xk3QkE/LpPsy9LIhQbXPMBTB6BsA8Tav5df5ysGqfRc7e7CbT5cD+yR9JuvDV38v7+WPMiZK/YKQ1CRJW1FG"
    "LUJTPNJcv6eY35lh27GFiimKwg5cu2zbUKMwnqyP6PYhX0YNHKCzsuHw15h8IaEoRhuna50KDE0bqEIBB8gw40yjTBwxSk7PJQuN"
    "be2bhaJLx3LPUBshttF/GtPb1/YFu7Efoom6CiwbA98ni8aG0oqcP7rFU6KQZPQ17FuKh1NxYOaoepzg5fADuRYB8H0XMx2NVEMZ"
    "OwYubV2p6TH4KaabJwqA2FVYRKwI7iJvmCgc6OPq0sKT8qfCDMYIm/mMb2HxYa23w6t5nGRelD01Vv1XveqkawS8baRZp8g51Nm5"
    "dkk0HJICVyF0ZLUKvX2rZ8hkxwx3r2nptzE9xrh6NC6SolLpQnj3HyVv8mDzHlkefqYLsklhufsvsTNyfw7OP4X4MvR9/Cf8e5W6"
    "Y/FbTFd/HRygwGH8FsuoWdptfySfHm5U3CrUf5mGs4w00GWIMlmWajvJIHFiHG1JqeiXeE2rKHR+ieH4qiQkTNzQVrhBt+apwUTm"
    "ivfexVsZVOHDy18+PH//8jkp6WDCTehnlypw6SWdTegP8oLMttDGjQOABOkDkv7e3u0sjD65OdCy1BSYOufEaN8nKGs3EYaqAQEY"
    "Rg+dYm+PrSAVKjJjRyhuwJb4Ui6IzgMipRCIdle3AaNKeYtl5QbQ3gtPoDMsLzkabMx8y0xNawlpeexq+auCoCHQduH40ZbxpONQ"
    "qjK8irkX0xIZI4DK9VIucrXbRjQHd9+9/+Hr9y+Pj10yLMvtCKuu1hf3KAzmuw+vf3iL8WcvCue/dPmJnDBAgf06hk6+CMqh9eQy"
    "mHw6j2/haAaGFshMXwNmgKLgEF/vtONIuiZxa04IW3G4Eex4RecyUdH6Wp4sMhyNHIyajtLtpNg/jqnhGTm0xH2tlcbiao4vggqA"
    "QKYwNAM/zhm2IRFZuaGCOD6e0eJE6l0s3kSVQ1SMyLEhSfNttuGeIl2S6+Jhofima5OsgVvNSw2WKwhNm6w4LXsdkWEZgpGX8lUZ"
    "/mJ8Jgy6I6kV7LzYjuXaJJqujiIBRWcUci8Z0oTgkEJIzFP2MZeyoXbIWei8mPPlRZhJaZoCY4FGTst3wEuG18HyyJvDygb20z0x"
    "gcxT4KSGwHo8UMZ42k21/FVI43ULtTyuSE8iTTEoyPYk5SMALgE2R44UQYG3kFZb0ag+VuRCwFzxZyHiK3rWVtKMYNRApzCA5EPV"
    "VNPuk0NPFVzWRoEHPdmmeANOHTh7rsIUF5MUwCxbTNmn4iKFYVl+mjs7xCpop5Hhq9gNXpVyW9q0oDbD5uXbuEuy1OY/Tl7RCF+M"
    "OQdOhKoJqFxTCPacONJvq7K/zdVy0DT/9dVV4If4TgzHp3dBF9bBw1l82Y/4wZsUoM6w6Fxa3PNJlWjLVc9BRdPi4Rbq0Evbee38"
    "oAOKQTGvKLoz4nebHM3SZK8j4gfbLNvS5i8SmwORQ8CZpmg4y8/aKVs9Ti695Cj2YR9bNYwrWK9Lr8Y6uc7JtVJywz7sddbSDuqN"
    "prhMTU9v2qH3xAnVUxld8eU9a/gVCw0n8lWYmbvhHyqGQZ9UEfC6ulwauxu2noVRirHKLlCyPM5x3RZ1aEvmnZbzgNRdqKAVE9sG"
    "Gih/4cLJc6V4aABhM10D0w+i/YGvfvJjM/yGsrpx9CiZV6QzWUUvQH8ijNioGIImpsoj45vY8yko+N7oefW3sRQsYLlt5DhgwDTe"
    "G1Lixh4QDnSuJosgj6h+hj/5dTlhuE49wJaqmgRuEEqRZWD3GkAxGLwLgzCTgpmM/7n9Bce7VJsBtL1K6eaAmou2PrTTeTCbESBV"
    "ZT/xLi4oUJRqDe+apNkgE1AWMYmThD0McDNe5OMpTPYuOR/3+tX759+/VIVQnKK+Z3CkrJV+++7jB90rHKflApotVACo63lsZBD1"
    "pa7Mqrz+/mtV9qfXL17+oH4cPX/70/Nj9ev4h4/vj17mnSlGVgKSrPK2632Gr2FqXaSWjFnsyxHJZpQP3mDLZdOsxROm7HMN2o/0"
    "2+ANBx2FzWgGm43s9QJsUp3C5WGSJTO4NKSX4RSvEN4M/70KMg8uEXepc49EjvUU8Msgp0Cj8K1a6lIEu/KHVHm2UE1hNuUsFpxy"
    "EJdFgpoQH9jYCjvHItuoLJnMvgvuBA1EptE3JsKoZBJ8YQIOUKbgJybNAq7nApuTAaPHGB3s8k90JiCuQt+fBY8WqosEEePRMg0R"
    "3HoTrf1xnTJ84Y4ZjOhJEIbjjsleXxOoiGQlqX43o9NR29ZrRdAz1IX/PvZT5gjQZIXFZLtubjIJ9z8VGdqyIpKqmT5g2CtFtuaV"
    "InHu0hHaMyhmKkEvdurZRGFuoFpc4YhvAQOCdNJ34R8PdptI53At7aOF1GLed70kiW+qi7nL0Je/8duVcJRJ9MMVfnwTqST8dgU/"
    "UvRdtAGjtt2VOE7LcdgYLgDWL4ZLJGFsubAHXBKpFDkLjBLJvgMpKI5+XsftsVzecsAx2Cl2DhcGyVGKygJ5WLDLdCXuYlvcpDk1"
    "/pDm1h03OOaJZx2lvOtewuxUbDxJfbD4rnbxwpniniRqbJCqnUFQmlbqTpwfUum3ejsxp4e+S85y3wyX9Dyaq6iGu0oTDb1U6x/A"
    "/OhzAkU+qPn0gS9RdZLJmEpOrowF4zkRxeQQL1I897SuIlA8uCQDqwwXHqkyRW2sSYmuq5NZ7H3CiBwlAS8aRFSvq958TlqvwJKt"
    "BNpRaTC/SNWroNnb8U9fyw4lSJiXyc3NWJlPlsFDR7aHZ4nZUKGcakvqDeW0nJZALTaZ+ipp+ZrmVp/1Qj/p4M5A9sMoUNIf8Vxn"
    "AHH84SZSGXyLSsXvOj9X4kTPDHlJ8f2GInOZ+Tp9CRfHIKHQfG/T3NsSH0/DT8xD3Ae6FNrsTuJoGl4s9O+bJMzU97WUNtt9vnmK"
    "d/nWRXKEs2XNXg62+3vK3HdGgdrf8n0sUxoozznWMFcC+D/HQ9T+/uE6amuuxCtjNlLnGC81liWj/dB1lPYNXpOBHLOjKjSOZO11"
    "xCOywhBxoVh2CbRqYznJmfuwxYaJEhnY/fJ1SmXwLQod1w9SoNoOGXPN7liMLt1m4WP869QhhntLRm7degnUMgGa9ybVsTu3VLzO"
    "v6mPk0R9/S9XvOeSOuwzoPWh49YQvQ8ct2dIuP5M82d1dRumGW+RI2zgq7/y/C1J+1lLqNBS7hymcEGptvZVWU+WnT5Ydr+ryj6X"
    "ZV89WLbdHjw8PPZagNQ1d3e5wVSjFGym05I+cdznXx29ePnq629ef/vdm+/f/vDux/fHHz7+9PMvv/7mnU9gp15chr9/ml1F8fyP"
    "JM0W1ze3d3/W4CLVane6+73qmQtbYJwT62BlWwat+kmDWh7Mf28BWZXQpjW23NcR4Aoswjlc7DutRTLb4qKucqhG74TTWQyFO89U"
    "Q3v76GYJIfIxjLJ95gvx2kH+GWrCk/53HwuwEztfwYmHEyBff2VseHB8uDzACpHDncRJDg46y1iEFaeDDnP3UeZSdfbRcVKlMnaS"
    "w8Nwp9FuU7jhEB+Fkx2rfnAQ2tXPAgJuGCHqQ26dh1lqnPm06N9oojdNguDPAI7nJLwKFmHflR/AuCin6zqtCnSxr5Ndgadb4Ieo"
    "eFsogulVznAFTjhLiwU4DXiZ0LtIvKtipkx0xdyfXofBTXkAkFzldBiBl346j73ELw0AkquU7pKR4EUSlkqoVFdceFGW0YCKJSi9"
    "ShmumIZwpnmRd1EeDGZUZY4LxOgjOSD8OXU67XazI75mwRBj2MfU3oXyM9iXOZZ/l4u+nK9JjOEEJbe8H1O23a0RZ8p2un//OYWS"
    "BnZHez+nepH5GfCPlFv8NnWgl7otfi1udcwcYNxjHGy9a6B8HVC+3taur2gybb1NR/X22Gk2up2uKG3ZXwq3NI7qPuChqzk2959F"
    "g8jYYCwn+piWbaor7CHLnGOCc0Q/ZLAzqtkzAEFGPoVVgOnM0Cr4rTAUXoBmw1gAFX+Y/KlB90n++KIcqoXsUK28GrQMwDRXcCHo"
    "TyV8lpGRNdwSkEo1lXSrTEeajZyCJBSkqRIMgvU5RvRgVA1gjmhEpNSr5OQQY/J2YUDr7sqqH1PUVKW/FYA5RQOjtawN1HC+YAUe"
    "B/9KyxalDPZjjoKAChHFZV9Z5lvKjybvR2tkKow9LSwaIW9iDBRo8yDEgYZqoCj+DmGg+A++r1Us79BhAIZjx6smOEpzRPhWaJgu"
    "Tv5Sf1Xsryr7O6ip3iprvVWL3WUTUwNlYv2RFmYfTYoLizsQ3Z1n6O4cz0FYvsNfU7RZktIOCtiOyQeFZCVU2a4ZzxaTnM6YeLTu"
    "frA22Ijw6kUG8LyCO3gNMdjwvxohEH5JrQ3+xRtAxyYUIDyX/z6Ohsi1VmFu8C/uk4qVILhJDRv2He0OTfJQQr12qsOWHzywfxvP"
    "YLxwuO6QmwT6XamPaYKHh/t47G7wRBgaYCSQbgAYbHLqYUltDQynosZ6eJOCOR62O5EaIvmbTwE9y8dCxr04P6ZWZG8YamoMlbYd"
    "DJV2HDSbCXzXSPA3+YkO8SsSP9KNFK2EUwtKhaKNbtaBweffnqgD9EkRjhP431g0UHPXVrkTmZuKNob40ephf9br/UT82WjX+mb1"
    "CdSDchNbFjeI+ERNgepmXBfu9zS1QU5FoJUIx5oxSzujEcBuw2OvUe902jCpSf6zY6MLm0nhMNyAN3Q0Ntr10sHYrOcHIyJJMGoC"
    "2jTrkq5+iwcz9NQonzGAFnjGFInLPtEWCniPvB6+SdTpfV6uDC5aYYGz4onrF1AElxcSdu9EsHsLpBoWGr4z+JaLjQRW5cJ3nksI"
    "wAVmEzGb0JsBeufKJDpQzT8h9U9M/RORAppPOCp9gLgR4spDMfqa4VeSBza7v6U1x4fEO/yiyA9/4hcpSmacW3CPOjWpJc3TJJbz"
    "wsSh+T9STcPu+t/mP/40f2RGsRW58jKIfR6XZRAi3Q2B7qpcz+kOPEz0IDGhZ2QYX8S6yiGsnafXLhlGjj+h069v0dAAxMbYAOjG"
    "4ACWxugA3oXh5W55zJ19NSndjMgjXUHDW7IGGqF30WqDaYCVIcIeHnZ5xAP66dQb3R36ktK+9TOC2MWNxFqaxTSeReMl/QE6egCo"
    "nZNm1pEB4p+LB/UwQ4fIDvpTRJLzbYq49ZSwEVAxtCmFKA6Ui4nQTOSvlH7NJO56iF2lcd8Tycg2kgwkgohTXHdi57D2iDZBBzPq"
    "wENnFdTLDMgG/C5n20Og3xiANmJXk9a2Vd/5rwTTgIbYqCsGiDFzMkyxBaDEDBAhKeMmdYBy5NyJ62WRSsHKJ9Q5EJiWomlA3Wx+"
    "fdoOirfC0T/lXWUP+4hSfVUZb730gXbVe3Rh3JrHgChbU7gwBv5WhspnYRbCfTINXPuB2/mFyU9MLP7/wIBhSOME1CdyAbDxFDX6"
    "k6n02aRMdEeNZlc06nXRaLVFryEaHdHrifq+2N+H5JaotzuQ1RX1DuQ14L9Wj//WxOP/q3fGxtCvS3wWEvQyn3VwNtnEZx0WkjWf"
    "VacJ3U0evFS/w4+PrwuX6uPNF2nUGXxZujsfle/LLzbckd+9eLX10/q9+AN8bn1Vvgu/gK+v1+6/X+N36bb7Cn5sfZ/fcM8nSmD5"
    "GcmqVBtA7T0N+luTpp9PrLsJbMDh3QT4pBxIOaE7LhX/Bhnm4Tf41CC1NPOyR3QgOLoV+z69CaUAcgJI7kqTtL4USz+9z1Zbclts"
    "hekWZ++6AyoM0J08XDYE9M7SLSq0BZMNY393632A6JzG5Gpj61MQzLcWKQpgskuoco3e1ONItR/czsMk8Df34MdBuhXF2dYkhmrF"
    "+rIbL9uSyIWvjEkgtuJkCx+IYEw++gLZ8lSVrSSYBdCnv4VPQjD0u3iRbLEydCr9DKhhZd4VTOehcaXhReSh8g7DgCROquZNEkcX"
    "KBLxF5NMV3+zeUbYqqp4FaYIJV3lbaz7+xTcbSlhOgwfdmyhphzBg6t05c3wdTzQYwRU0a09WItHqYpBVWXhuxEiGcAj3VpEnyKA"
    "/a7LilE3E2c0qtfrnWa70arti2an1ut2uq32/liM6vu9XqvVbbXqolNr7Pfq3UYbkpu1Vq/ZaLa6ddHsdVqt/Vaz18P0XgPY4167"
    "2wQS2G02eu12C5vpdeq9/S50IaAHIIj7rW4DW2/X9nvdWq/XFM1au7nfbDU62DxQ1CYMp9sCStprwmDq7S4239jv1rqdZqMB3XY6"
    "LRhou1PDbjuNVnO/XtuviUa32drfbzZ7LUyv19q9/VatLmB6rV6v025ht51at9FoN7r7og6T6NShTSxdh97393Ggotnu1XCO1Eq9"
    "B6dyd78JdL1V6+zX9xswUhwNTATSGzUk/PUmNFSn5E4dRgCjaYpOs7lfazbrXRxLo7UP5L8NYwS49bowuQ6CBtpqN3s1HGQDmP1O"
    "vcmQb9WgNJwf3ZbAFYAFahIIOi2oDt0KAH+90Wl0u02aUmsfptGA5Bpkwho0MbnbrcHB2dtvinqr1+71ar1aHWcEZxHAvg6nUX2/"
    "DS3WG802rUe7jesDpxkMut2o7wOACAK9Tg0AuA8nGsCnB4WaOCdou9Vo1Pb3oXyv1+vWoVdeJ6jahIH2RLfT6eIKdDC5125AS/uA"
    "ZI023HN6rX1a1iYgTbPe7CA2NQBezS6sK6YDTNtdQEFYv1qz1WrDbCi9vd9qAy7Q2dvpQDNyWgCiRoewqdvebzY6vE6wCI0WtNKG"
    "kxUqdXtNbARA3QQ8qEFqHVarCwNrEcSaOMg6QKYNCAZ9NgkHGr1WF767mN5o7NcArwligP6AEI0erh7gIPaFfQIM2wCCbq2G6wRN"
    "dmGNCZL7uMa1Nk6p3sLl3a8RLuFSAc7D8Q8I1W336oSqsBM6iOTAagAAal1YYgJ8F7Bzvw27DYr3avudZos2AgAe8BZmC5CsI5Ra"
    "DUKPZqPdgyqAF4DasCfasM8IKQHZAPm7XRxOBwZRqxFOtuuw3m2AClKDDiRC57TPajWYy34NuJtWswG0AAZEuNqDduqAXpDe6cJi"
    "tmnnNLowAOijJfbbsAN7AG4sDSNEtG3BGKFpYKPaONV2DVeyU+/AroQ9Dr33EMKAJjCCNjBTUA62H6Azzgj2OCDcfhdG2N2HKQFx"
    "wrZ7UK0J9Afm3wT417otghegcQN3H3BnQCdg4M1WjZapjUsEAG/ivmkCkvWo03q3BW03u90eAgBg2tkn+gZDgpHgxgQ06OKGgk2E"
    "E0WYw4rUEZtwxzV6DQRkgyYKWARsH5A/2ObNGu0EIBb7QG4bLdGCEXYB0QheLaCMTViPloBZdnoS7ADGDoCrjoSpC/NCz6S8b4Bs"
    "NOtATYBMAtq3YUyM8EA1gcD1aLYwmBpDATYnMKWAsAB5GB9gK4yflxsQogsjFLAtAZCws4iYw77dh7EB6AGTYHnatBcAuwDhali8"
    "VQPo4dYnKgE0tr6Pg68D9tabsFQthiVAowWoCrgImA97gVG1h8QR1xXgC6OvEWQAj5sw+E4Pk4G+AiohEuy3gQTC3EV7v9sCEkJb"
    "GCAIu6RHyLvf6cKU2kQGaoDHcCTg9DswBsQyGl4D0LeGBLiBexYPuQ5t7X0k0kBUYZq1Hoy6zkcfEEjcK3AItfAVsIZbl7Y2wAd6"
    "g7WmM63b6vBJCdMHYCD+AlVCetOrj8fiAx2vgEnQBwwLD8AeUFveCrB4ACjEALwaIMq1Gf9qdTwTAGrQN6wGkB4iK7RtiNAD/gGa"
    "Iw0nvIR6AM96HTEBSnfadSbQuHcbCH7RxRsUFMDiSDyBYjTb0DpsARhqi3ZJu1VvAbo02gB8GCusQG88zvnhlxNlgWNICZuN4ai2"
    "zERtCWxudIA/g8PDw2iZHcCPaiQy+hXwr3F/RL+rzQYmdVpQIFAJGSeMczb5xVqPeQdrDdd0S0YLP0zKxsoW1qvZFSuhv1q3uhJV"
    "rHAP8Anwq9vodZY1ewnXsWVotPZpYkqhZXyYgnQ52wPWBdgUOEFQioVAwG5E6ACePaOCkyCcWVZWqXftPYyyJbzy1TK0MapQQB6L"
    "SJMdiinbMCiJ1yG8O1ne7vliOg0w4CUWxxaaDSus7lM06EJSC8PRYROp82FCJqiBczhCoaEIRoCnKKbgzgG/y1LocBBUHAorWHwg"
    "qndIuDgZNZ7BIGNUa5EdBpX9Zxm0iTkop17Lq7TMTtBn9MF+zQyxhFWtoFpv22OAcP4LY6aOEhGOnZcTskao22LkiVj/BoCOUjEb"
    "Oy/4dxetjpNT7zQVvhOexqdkosztNWwMwKp/UNtX4pLamoo5EDJo7EKc6YQO9nYt7qh1SoA7pnN1enF6LW6dy9Oz0zsxOhZBMHYA"
    "89SoO9BN/o29YCDNQV4QP1SJbl64i2VtUSp3Lm4ZspB2zB8I4oBC6Y5gymMnxXVlKKXomgQANMNPJNPQNX4iOYEJ4GdLzTodIfGh"
    "+aYjpHU003TUHZcQwliqUYzmGQpeLRgtjC9P2NfDlyktgOCRE5+enx6LLHDS09vTAL1mOdOdq9P/mu5coPuR+c7l6X/Nd87E6EaE"
    "PHUYijiCGgA2nYYfUBVq2KKUeoO3dIQCfxAYiyUYghp+tDtGXiDiQKNSg3AJiuZJTZzhLBALIwmRxA/ElBv3gtM0OJ1hQ6eT4HQB"
    "5GcnOc12vNNkxxPRTnga7cxOw52ZPbh2LsSdcyYunCv0IyOunKm4dOZyYaAtWCuBg0UU9si63nMSMXNCJC1oWiN4vdWcaBT2Cpcf"
    "0/AvwoD+1scyNi18cWZdZtYpk01p0MKEMhsys0GZHkrAEWk4sykzm5RJ0cwRjTizJTNblDlFtyaIWJzZlpltygSsw8yOzOzIzA5l"
    "Ah5iZldmdmVmlzIBHTj+xqxMPDstcmVg0smZppMlNCYsXhiEcv9ZIFLGHDodRCmz0uLs+tg8PLZY/Pl84ux3WkFb/D5hY5iPH44s"
    "YA3bKNSzxfda4obGRReRtcnR7P0kvrpaRGF2x8p5V1dBMgm9GbrsssXbyUbvtO+AxzDO6VfGKeW6j3mFzyqOBVexJbkfyJ0kAJHS"
    "lhqDddvN1/JMRZU/dTC/S617EnD02VkBi6+k0hrLpwTLH/qBuArS1LsI+iwF45iruYeFwrvzbhYGZBOn4WJI3N4XnyVfpRZKn9gv"
    "pir0zMpDDUiBzxvvPJgZCqPBtrbFQzsQ6XQLuOb95XLbtEJBxwqyL4CBFulIxyVsic4G5busTpfkTx6NR2qOQoGh50RMnmTjDc8Z"
    "NSHtm9gln17FnZ03Kcl60cysUsFnmEjH/lycw6zIpFkamJEZeFHD7mMU3M7JaGYriz8FEYwbkELVWAGNsXJFbYlMgwEblh5qHmit"
    "0SxIrsIIHRhsSchqEI1gnGPtsu+Jm9soY9oBeowotoYqyUlsKKORE1jVqrJmPjlBO9aKk5Qiy6sOpXw1lPLVJ26f/kI1/thz+1A7"
    "5KDxLIE7pyT35Nw1U6cydVpIjTj1b4XERBZNCqkZp/6vQuLC7Ustgj/lgh4c1BtL/oHH08HBvvrVwF8t9as5piVrCWiU9y89nx1J"
    "zUo04WaVIx2V4mEVy9UKDpiYESg+BDJQLPshjrf8IJgD2CNLsZOBNN9MH9IxNVAMXfPYqrB7DysGayMR4579A1k2a/5A/krjBpQS"
    "iYl7qtg2o1Cxw5eqO7QNQOBU5FBDK+/87IyeAs7OYM9/0dsAGrtt0J7lPkpD6j84pEk8Q7c7RH1wUiNgnjwrRj9CZgPC1Y87myDx"
    "QOMkV4eyKyQFKzXTUQHMo3EZzOOHwSwd3fMAHx3h+F8Y4bg8wieFyuYqZW7u4ols61xb8AMXZU/NbDKkw/y6zo/MfDwWIFv5FKMC"
    "VVj99/g0K8tZBrXLBsb8qmhjCINTv2su0lsddX37vdy1GzBEWnMz8zF4X6DXRg+7DFDs5D/QGp298vtl3rJavQrqYstvhMG/06uE"
    "cMkvEdke0Svs5w4c1Mn3UMtR4iVbkm08WD4oNWF9FhjKwvHKWj84R2Ot82QyP4bmoDqNDuiCm61Hm6VjBOPbUrFDp95r7ewkB06j"
    "0bRDp1nfSYBoYlRFvKUry2co12jIcnBBgOt/m8o1oBxyFjnmUNFWjYu2WmXoK13pjx9eVfeRcDhdaqgJDZHaLq56VPEOHwBZuX7x"
    "Bu/lGp6ZAQyr3mvsZMAvIEw+N54Q1cI7zZ2M9L4P4uUyPKzX6y34Dz+ddruBNsrhgYPC9Obn2jvkaQ1Rt5z1kuWaUDvQ4GG9Jtqd"
    "ZqO2rNcazZ3QxnCuVCLkK0Ficr1r5nJOq9br2MnGw1IabbBjdYnIgQCuH6vkxk8r6ycKQ6RclG/m7Fbkok6H/Iq3dRSs5bJo5Rk/"
    "ylamToxxlb/wCZsenY03Z7gt3gNXju2inyzJAuNv9fwJOw54bEzBv/gTPaPhTzTAtUXoUXH4gx58buf4A/647NBPzm6mmGuTl9Z5"
    "HAAvz9hmYgEAeIXaGwHc0KBFe2MG9GsbTYW+2dCM7geGKUw+Hs4w+qxBse8nI87BkC56zEgklSXBzs5M3TkkN/PI0uD9fEpM+8IB"
    "lPBsuKMjYpNaBIZQB4JoczD1ALHzUXQh9/gF3h8RaO90VKv2vOr0efXV+NnTPeVWYrNFxWVwWzDa4I39iJopXwqzwqUQFaTmXpIG"
    "r9Hll3It8SwSqCzVsAXwhYa2lOt7QbcddDrnvWm7dx6cT/e7fuv8vNGbeJ1WrzVtdv1gMplOJo3zerNx3tsPgnq7F0ClWrvZbZ67"
    "n4ELu/+DUx0BNHfuwmDmG9rlBfnwg1dABGW5DtOKV6gZVwGWrUL3ZvWVoZrh24lUrt+uoScZQKI6/lUoEUoTyWLD0kbfUHfrtJbL"
    "aIP2mzQAD7VGc7MhOi1WjrqeIIUplPNQoyribG+5vJhgNPdCidhQb4deRIo1Yq6RUo20VGOyLj6paP9FgwlJoWOBGq/0GVGz/J3R"
    "WFkGs37wPopzhvJihMpMESozbYpQZ6ooS7as0e6Q/UIFmMyRVIqmEG2Hh/vkZm2QYCBcBGBmDx7S3IY2y5rbZ5PNmtvYYbBKqk4g"
    "EoybjVHtbVOVO8GYvWLhzFEj8HKiN8cUNStTAckzVLuTmniW7yzs3VsxRb1U+D2Fb18rnUGCv3tnZN5x5gAFTEBsVhLHPuXdvFO+"
    "Mg8p0i+bXG8B6r6bsIm9ZY8FfEvGRhBSO4TRGHsW/6yU77SSY4K/tte4rqLEF7P43Jt9gJIUSyP/2ZcF0JEAZZFHgbWIIkP+lMeZ"
    "PdydJHfzLB6ifCObBRxvCUkDbyUeMpwg5FLtu+DOchPvBgiJkN4gpS6hu0Kr5pF7HSTh9M7NzU1VA5xhrdUKOUyoSbLQl7EEjhnM"
    "hUeMJw+5J4MydF5sIHdakwmHOffuZrHn92crZiHm9heUHJQJnCFCy0+5DAZjbRf9m5kGYi45QtEneX4qYrI8ad1cKAmU20JGSVYo"
    "cDFFFavyaHGtrpx60HxGJ7+4NLwHiQvzQc26ql7ae88ntjjbQGVKp+V6fHW7cDvJ+QoM1Qy9c/TAB2WB5Odrg6oyDZaOSENPV3fx"
    "1nuLznJIuZYsPfRpua38f2WHzu+TIQeUWVno6Zm03rBdWsozHbl1+w2p4W48G8W9792lH+GeMnuJKnp3fQw9XMCJM93l2eGV2YrS"
    "6fuiVngMCOHLw6tKs/YM1uOvtnVZHIeUDX+u5sqootz1f7aOGda2oIH/xcqgQ7znluPKMaZEhge3aE3B86uCaFqKxoHgPCgDN2IU"
    "F40FlDOpe0mQMsNl4qMkOHSOiY3xnFv6GzvJ0EQ0Ihmal/nKxCxP3Twk2OD+QV+aHrCERh2uTDLf42GH7wDqjhEKU+COEUnzzjGu"
    "o/RCRCb0oU/B7Ag6SGSK5EMbjK/ySM8F+kShhB4kasP3aLjzLw6tDxBJh2VVUa0Biq6/ZKQyvVYE74FyzYRa9NvbEoLSe1U+3uiR"
    "8cKu3y7BW0WS+2bCQZfzSLMSW/41hfokuECPfolUee2jGDPdUmHCULMUXcKHpFOqyRf0jbhp7Kqfjc6/mSiifGtaL5QdJqxthaKi"
    "q7kvSjmZnZOBbybqfC6GDfx6YtmGjdT33lxkzj2cDwVv9RiZLj+qw2GoeKN+6ABvJALJ64bAA64EBsPcVJ3d66r4QspXcGIPAgqx"
    "TSg5lyKEuhFfmMLxWeQu23BhTNHy7AGFyTJix9wHVoRWGYhrkxkGrEDPjPJrtSraUH83ecDzyB+Txz2PfDv5rOeRXydf6Hnkl8ma"
    "55HvJv+255HfJo96Hvl2YnoR+WVS9Dzyx6ToeeQP3Kf2rw/X0eTGcLE72RTOPZCeQIvyHIwYqK44aEiJXFfB9Qyd80DCcnZFSoZ2"
    "dkzXXoFtNGIYHmudJqeusLJaBzpPYwQ6/6NBhyDP29mJh7W+N0z68bCa9I1u5QGmh5KZhxpHGgwOsmG13q9YwSHeiQ175JnhkDlg"
    "7hJRP2DanBXsUbYDAEKm5TiBKQxTfedp+T0kklEmfw68T7Cbtd9IiqCpXv+kT9VdJsZ5vwleu0mPCu+HshWMzSESGZxD3r/Lywew"
    "LCbR8ckzCeGeVr7g6xszeYgtOARP9GV3kFSr7F2A4DEjO0pAOPgHjpt7qsovdbn7boysljeqiEUZlUToZOU09TAaGmNiv2CYQvQG"
    "g1pY6DAuy3892M/74AJ4rHJPnPq5vvLoC9RZ/jN3FFp0zDRnn4VmCh8yawUB18oFiZEI/wxoXfBjfVVINQrRkJYiI8RJUPwIqxIK"
    "Agc56n5gWYr+qIKsNFrEsA2jheTSaLHgF4yWiZY51k0DUy7DCvQDw4Yo9JP4ZBbI7DXENRxIhIPAxNgvYpqBO0UPqIXh4WOyYZsa"
    "olmq4WYDhjjyWMpGmyLETRGubwrDt0S8XCZGABwjvnM2K15+ZyUGIZoZZNwghIaTMBcnIt0CuvQg4BbdOyZGG9s/FjmicGawY0jy"
    "1m6PaBuvxBUBedWg7TPLQxxBX9LFM2SUXD3K5aI38FlO7LYUNczyoAXAuTnIiOgRYFdaFyZXVMGwM6bEDTimSD+XHGSDSoUv18mG"
    "2EwJrB3GOhiv9NvIysg3PAjMypq8QwJVhGMM+RDuZ+XVinNo6pihFAxVgaGwQzJEU49b1YdAbvWY+xqYlSMFF/YpQ5yc6saQmizQ"
    "vZujNg4+MWiNgeIpTQ5YiBGbzFQYKGtkaBoI12jRRe5ebiXXtPiczfTxbp5Zcq/8NsFQhrDY5hBCk1GA20Mkj0K6ZpCoNlTu/LbV"
    "ManNh/Hk5NNQlGiD4kM91giZzKiqV3C1GDueSJ1sFI8HANcUulThIBDMkGwPQ/jX4W5T9GeK1BU+hjBRmErK/oVnXFr9pLa45gMV"
    "KC9dwVmNE8iJgcGhLGbsbDEXhcFFYgEMuWQlGdIY+1oYPIYt7k3JgT8zr+NVdjibYx67S9APKOg0AQugiBVYIfs+chJFwNZt46cb"
    "2mZKgBQC5eTAxvtvvDR7jbva0nJHEqGrZNjsGHQnGO+ij1YUStlUD8nDhk7n2ClFodR7cUZBKDk0Zd+gdFdrO2UT72hJxo/inKiq"
    "lyahveIOdNyLPau6PLP3LtDvY9Hdudn7BffuulLVkMF9iWTPJF/k1Zvl3PmVDpHPXufLh9Amzn9U2sAELrhu0ajpiQfjDuAZBKyi"
    "dkWKNIoFPf35rBRD/mwNVOt3AgJUgVjkZt4muAgFMHoNiRLN4+UOchDOpZLGZaOOwgPljH7v5Hi5tWfUPze70STVWl/VnFPPZamF"
    "tPPwIoyyUpqMd2B0eDvLXaXSk3+UzXaP4tnMQ5+Z8on6nu6F4YSUXHfRsamXGHhwnJ8CFD1PI76joixm2tm+dqVqFBLRhkPgqEQb"
    "FK3IS9wUNqfUIcmq9So+WZH6DH6Ths3JiTuwo0pFu7/4ewNWIm/qQwHs+TYYnSQn0Uk2rsitoDO27htihYlbhVRrdN9fje0tzHla"
    "N7Os0UBszNjaxrRtM6lPxfrmMr2cqffmktdiuf3gH+VrCqhdSY3G8EGGwNgj3aIEbRLg1zPDCbdmTZ7tQXuVBjoVzIhHGaom+1ml"
    "kV9/WDlsuaSPf5AemwOwjGwakjzRoCcemGeoxWKECdRuCpdLWkc4tAa2BysELag30kRwYDbY3V6lrmMykPsZSOBhoFIojFWpOVlZ"
    "hQagwkEZtkq4NeEkycz9KclMEEHpgChNfgKN4BgbG/Hah2StvYsept1+pOObzuAmMjTCyr2YkddT9GMvlV5EsBKjMXMeP8wcwKrb"
    "o1r15PbVq5NFrV6DT/jTfTneE59mzv3zvi5w1OYC9G+D/m2NATeev+QyHfxxxN9dyu7Qv/v073P69wjLvKAyL7ihl/hvvYbpsp19"
    "7OsrSqZe6i36lxqrU2P151j8ayyOv47oX2qoQY02Gpj/jcxvUP0GDe81d3GEXdB8G9Rgg0bXoIYa1FCTRvT6W9lGk1rUv2je36lf"
    "1PIb9atH/9L4my/oX+qoVcdSb3nqdUpp0r8E1RYBrEXz+oHLNGCMLzrwH42wRWNr0djaNLYfXsoe2zS29+oXzbZN0GrvY86xyqFJ"
    "tqmhNjXUoYY+yPwOQbtD9Ts0p488kh6OhKp1aCwdaqjDKdRQl8DepYH8LJvrEpB+5SYIEF0aVJcG9ZsqReDqEri6LzDHoxovEeNe"
    "MsYRtGoErVqbigRchgY54W/GOP6X2qxRmzVq05e91Wgp6rQUsg3EtpeMbdRDnfqsU0N1aqj+FRa/UNhGU6kz8tDIGk3MD7k5xKyX"
    "nEmVG9R0gyo1KL1JvYe/K3yh2voXze+T+kWjaBLAZiqNgN8k4DcJ+C0CfouAH9EoXjF+0Uq2COgtRiKayZzLvMTvmL8R114Brr3i"
    "YjTaFo22TaONA4VDNNpE/SJYtWmU7R7mpCqHpt2mhtrUUIcayhSuEaw7VL/TxZwFjwRx7RVjFsGvQw11qKEONdSlyXVpIDcKiwhs"
    "d9zEC0XLutTwn6oMAa57pMjbhSGufa4ONLiI/DDTSlNa+xHvKJ9mFK5TnYufZuh2MjOkv3lsYH17lcJNCsGb2z/gr7/nFqFZ/o2u"
    "yeQrQCRq+Y9M1MnbkhkeWHaCQQrQXlQ5cZTiXvJeFuuAVBYJHpZLkvUibxlTYJf6MOqjE7xnnhH+t8yKY5THIdp+Au/9cT5XvHcl"
    "0FY/Jhv+7nFOnvn4apEZ8ap/jm2LYqfYzJNUnzYe4/VfPdoJB2G5EPLeRo5Uh0EfePJKUGzzkS5eK45PaQY/ZhllaiOx/32lD6w8"
    "8DPbm2i2RzPOoRHCy871iQtMjZJzSylQ8aoA5/2IB5vY436JhUhsDiA7AlAg95ABHKRqzCA3Sh5mOgrtLsf5w9sNXAxQWTbXXcqD"
    "tCp2BnmINzPxfsbuz/MV2H1WGZ4+vV9Z9nJ0Mj45weUAvvfpjhn368+Z8mQ2T4JpeNvPBKrX9oFbm7sCvQz10QJh5Wx6+QhgJqpe"
    "oF+9VUNy3w0zpdfKDctGjefzr2ZF/T7iqv729D7AfyI5478B8+sO3syGQ/VOKJf1zUwKf+XruNyDSiA2dK3h9tP793gHXVWtYR+b"
    "xPV4P1MRb5cuqr0Pt09Obmwb49HBptW1XBxHFUs8vfdWrkgdTswwcRA696QT32exuuVap8uTkxTKxqun9+nKGjq8s1zhXsB11I8z"
    "XfTkZPehYp6KudDfOxmdpM/IAT38tUb/tTx9+mw8dDDWKkzmiTU6fTJ+Zj9Z/gO+/gFf/1jCx0n65B8n43HFhq0cyqe5z4xw+VR2"
    "vhIAURRrH6JuGnzLp0tKRkADK6vQ0ZDc/JTLKHiD8n7IbKEQImEECBkBvJVDuKce36PlcjsBUpiH2vyK2Ga4B+wSiJEkPb1PaC10"
    "r9/kNz7VTcTdJNxNqLohUTz0oSNsZhS6HBfEM+AdS2ilKwf655iMrMudb62UhxIRBuiNqXI94e7KTJ0WCyPEo7w/AIoOh8lwGA6H"
    "hHGR1j8b5qpoGDoSrlF9uFPpQ249JJ2KwV1VoT6fNexKXEFt00psSsY+lmTtQyN2vfmNpCjzwghliibibNluJau41pbElhDJEB3U"
    "ecBnu29e2n825MFAELRlJwBBDobCO24eBcs4zWjSFYy1UIGdPICTf3c6A3JpK3L5FcsybPMxXpt3IsHUsWdtU3nna0PeIb2VUdCV"
    "nzE6VVWHDlEfMvqIDLlNhfK2viNqui6bGQIYdEsYsVsEy6U7r6K3suksvqlehr6PljX9XGqOSjZJiM/rOPGdnUJ9Ga3ZjFRbLC9w"
    "WhV3fgvUZL3zYQ7RzeMwcOYPzZepc1g3xibNEiKW60kruV10FIcqXVrLnzco6WVGIk0mQP6dIN86xSgzl7CPXfSkXc5QzaKOOcUI"
    "NgNWy0DVRSh5wCpF/tFlOCNhOYwYts4nyy4V4xA4uth2bbVB/PRtQbiEZ9BXs/jcQufOHJmeXp7CCcXi2puk1wNU64cZOItsWt0f"
    "oHPDxJEYFnnX4QUK1Njm+Co99q6DH5IfYLjYqr2ehOZZFXcX2nULT74f37+R68BsB/y2yOMyrBtDXFWTgLcHKT8dx4uMjOewhSS4"
    "BhqbtwDQbwUtaAZ3p0OBfyjswvq8BDB0Qs4KMDGy2Hbi4/vX5K7T2Gi/PkwKHiIAvDAlGuAY35rCFk63cyRT5s7X5zzQLsjOqReJ"
    "6/6DxOSXhwjAr/89BIAB9AANsMWv/9bO/21WVNJVTR26i6KKbX5HwyBBuT9g3TcN9vgyCLJ0uRyN+bGk8BJo1MowtPn7xSyQZZV5"
    "ArdSesxZq2zbrOhhCJMDFdtbDloRIj7pSXdAQZCiOuKrrWSu4f/4+UbbFm58K/1xllPHewpr2K8JjmjYr5HRFWeTANEZBXL1rsM0"
    "PA8BpdBldoGcjYVUW/sqXkQ+YNDRLARAvoftiToYa/UdV65fuSHHPZ/Fk08YU53G5YT8F581jCMMsnm4kM8feYFv6Pdaw4nYMIxo"
    "U+DwmdbwYzoh8iNE4EtA6WilYHIwdfkz/eruA4eCtFzEYRdv4equwbAOjBMbFYgmBCz5MzF/qkWRNb6RU1VV1O+k8NvY38HCfBYY"
    "kjTaO0ff5ekkiWezN8EUiJWh+ZUt9OQfYiWUeEAS0bl3EfzyA0Ee1gD7s6vEIeGAsP3l0nyGiv5SB7/qDuTAP8Rzoxv4VewlKc4b"
    "VucovprDqewfIwqgmNwPMbgohvUFspdkM7fAB4YLKSrB57acmUBdK8aydx6GoRzqFTWRUy+aiZCrPu06ekzkAuhqh7Eb2Onsod0j"
    "7s1W+qkweupP4KIrZk46HMaq0YUzwV/cru8gvMXUwXUVcwdxG33iiAvHzeK5O4jhsjKvzCrh4Vw2MLSuHE71qyGWO4+zLL5yxRWZ"
    "Jl05Ptzwr5xZRRYSlw6y8dOs4kEb1C3j2ZV3C0y/zJtWFlXP7qtfghZoqHYkcO4BkL9ZGAUvI9+5JEawvyH3GDWaZb7ezzAM56qU"
    "hPFk0dvtDwm+IjoXIqJYuJx75SWQCEjjXHAQdZrgENVyJtbTezhH9qpeNLmMk+rFIoPj9emePeQwbHD5aUBHq61nW9U6XL4/U9aV"
    "scG9hbMX3MKNL0UXxHAXPrGWi2RGH/DP6B9PxkO+If/uXXuA4uE8W16f84fdX/6TjY1O0srjRZfI+dj9vVDE0OOmHog1gqv3Exsu"
    "33jbTheGJgnzsi5wXvDvLUD8U18meay8JCjCrvyBPt0KtbMMIy3inxSDwHrAm8TwkQUUIfYKE6dUZMolgNafYyszGOwpjSy8gt1+"
    "sgezm0cXy4twuvx9HlzAPxfLm+B8vjy/mi+BF53aAw7tJVAYUKv2KnvOSTquPN0Lc1nRYlEy2sktbwrBfb2Flt5qxc54sfYILOM3"
    "ZQ7kBbcBqaCT2tpM1s8otDodxKaK6Bpn7i82e09iHTyltlWMXDcIDpxmndWB643ucrl3ku4pPgGYXnSpY284zKYL8xZAPdN5VZBh"
    "kl+EgrXA/0Y7rWLS3nrS7qa0TYlD1wCIdJIYKQ2CUxbmqoXcrQJiAgbDLkKnasPSUHOVegokDTjjDtnRDyItHIX4aWCuvbOj1idQ"
    "i9OfLEhXKLT7Zkyg+aIgbVhXWN7ZSbliWSS8s7MNgM4KETmuFiUjuUIVOWA4+TaqRu/s7B3AbuVNDRcAoBk3FUhwlvmm7y/1Nedk"
    "7zK7mu2FKoi4oSRTOAgLi1KtukCB+8G/LFU39GcWhp+uiCVvBp0Fvhjt1PG5Ghg2dQPJcv8n+Xt9X7q4OagVo+xmWnqkmVzUEFYu"
    "QCp1lcoy9OUSNn1YUB/zcI/tbQPwmIZ6UfZUQSrEZ43QCXMQlMux/hD3Cy3pLNfWZ40p1GABoCnCOlv8x3Q8rhdlryMCHVFgjMZB"
    "rvxaM7QUBl4enxHVFQbJEEMzwhpt07g8m4yNYY79mBUglsuYVSKGiRNzImzfsFLhbxu+HeN0D+EQ5JwBWkixcqAlnyRyRy0eBe7x"
    "KoaRSqmIjYYwuRKSiVcbDAcI7wAcGSlMWY9jXul5w9A6tMi3oYymHSmLC8CgcqxnqU1OcoqHsSlhaCZfhk3h57HpkmZIAmzznnsu"
    "USrI9apM4Ejg3RNMSOGpz0mohmi2c7vIBRymeiqGb1ZBi3UAbYPrlFdaRsQNrPUgqrB3h1ez2ANyJPktumtUNmS8R7bT0COUHwZl"
    "Ps65cUB5JaPL2fLw32fLvUc4cOTOzTrDoae47ZRZ6omYoQ9Y4PiIqyZatLPjEYccV9Qd9TDVPPbEqdafhTnPrrlsrjMhXpsKUQKe"
    "WU6MfjmZw4aWmNP2iKF+Vq33+atSLmAV06sy3cYqtQILPSmy0Gtc9+xxFnuhHsQy5zGmeLDOhC82MeFZmdPGBHdl3G2PFmVBL1lM"
    "w7K9Ba5JS2vLFhGXHlwq38cxaXlfxinpWzv8iURoo8DkxjhGt7dNmRfGOGd5F43H2F4fFuuGAHJbkdeBYEOE8/6mZ8vt7UD1lEdT"
    "VwX1AHIKYCjdLQwDKmVVvF2wRdi2DGtj3SXcltxLL/JnwctrGBaaJ5RpYkA32bM5Cj6DKEgwSj2cSp4ZRCwBfNV+OBL0w5FUq3Y4"
    "StD9KVrq4PGLv0iTLxpC5VrfUmJC6lo1jxrmXBJIp9JxSEQdQyx59Cbj+X65BhJsPmiY0pvKdAv22SKFDLD1Oc465BWlP4Usy0Yi"
    "CjgcXM2zu6H8i1oAKi79bPbeiy6CFFcswa8joChZ8RdGLiZpGRV9nhV/AbePv3IKlFpK+Z4rlnqyTIHuD7TidG7C5AgFNQ0f7j7F"
    "h8MUSKiydGTiGSl0RkOLIZtb9EdKaGUIm5VqIdte0qnJVRUZVrj0ZToL0WM6C2WbucjGKOl43pcO9EjpK8jDPOB+gcag5ngEdxGK"
    "ikvKj/86r9uX2pJaLQCVIMI1JYjwMSWIFZ7gyLYCzIh1SSw5QHJhh6HeBl/KpZjwxnNJXaIAN3cr9h7xwbFNGz+m+6g5G2FAnH1S"
    "Vc8ByVHHmn59hT9swqFySR6vHSIT5ElEctQHGTioH2hOW+LDtC+6+YJwZ7m84g9FUiLS0nVJ1u8O0dZASRUAVJyKpcdr6iT96AtG"
    "E7G9df40h12v0KeK4XhfbRxpNW3K/B54QMyVwQFiiWCjT3rBs6gNYSqNPDdOA4tFQzkyHpzsWQQwksi4Bycne6hjbaiHmWeJ5EYD"
    "o4EdROAd72o+MJt9Qql/LOKskHxAybNi4iElXmCioTC2II3jsrJxbtOgUH7vlJU4Dg73HJTCaIEKbU3Ae9JAcZ48vceZoGfH1ROz"
    "o7fFyzLRraEZqXH3j0WQ3DEdjpPnM7JMAxplKJFtakKaKdCGortuoRl8qCue868IziixY9+c5rm77Ti9nNNAeg1MBLIaQ+nNg1+T"
    "h+ZB3YOdVUioa2O5bJe9jEhsGpI3l0EguVsZSxoxZdNz1lAaiag0G9irTc3RbRPgHw13U8342NrQrVgHLp/4aqXLlXLX7Xxe5xcR"
    "AhybZgdAuSaLtCCGeJNfNYpnEsLR2Jd5eE/tVSaSO53Mf7TJCpwGlahPsnty2spUXnpoHebp/cjYg+8Ld/GR6QUM181YUluuKQZn"
    "HuALbmEJAa2QWyzUsJThjh3Jq63yR20hgsAVKU4D/x1cnW2NL8NddDgfOlaysXPpTX4Qkr2ddhIe2gMbGavikEIaklJde6xNZdgz"
    "HMLAgLOHUowthi+bhbSLUrCi/enCGmUxQD3O4Ezyzkl4s+VsPanWn4xtTvbDFJ9zffWbqNoz54l8heuj1oMuzG+AYxtpg/jblvF/"
    "I5TdjR/t6S+2HEZwV/2fmEJKROZ/oieUAMK9x/sfWRhonoTi+eK8/m/sDZ+xgfZgMFBs77+pU7JQNskBSuKjxyQcmXpW3paKPEhM"
    "83flbf2+jZajkhzkBsy5JmmBIPGuy0mgZvqH6KCldFL9tOH2W3j/jjYOXB0+VVNCAxQLLk/AU+CramVTxld0Oy/lnceJHyRQh8Qr"
    "GzO5Hufnd2tDsvNNcRocbORLFA7+ilLBoPiEy4Ay9BQLdaJN+gIZ8HTrk/j4f3ESLJH79+fw8xo+kTwDjg1UM8MjJCU/1yT7e8Q0"
    "+d60TdaBFzClJMCI0D87F6gaQu6vv3hLRFq0UN4b3xXagMMbneUyF3McnqN7b+muW7r6N5jEfMjIC61X3Cwe+mPDZnxIGUZqgmTx"
    "HMObx/PKRj2HB/U4tfqDUYYVrPKMmi1Q5tfPWPT3kKbGQ33YxVxs3Sb1ipUxdtdb4Nsu9cPfBqP1rSFZLouQ5a77azLkMoFS6ZI+"
    "PSZD/pV5mtFYDYjwe2AEmsM1hWs+FIyEvtiPimKjX0qoNU+C6zBepH8JvTZX3oxivxUefwYmZH+Vr7p7Fq7DkhHB3kOVLOfwXnkC"
    "yQx5Vgna5N0vZwzlK+K6npmrtO9c20alo8+W++VLC/7qllydb9dXq43nceSUJaFA7rzMA8ySWyCVt7uUHhTVHT5SypDCcFFPT+6J"
    "KvJOyj3QqxA95mjTmtWqeA3EAkFeIDCd9eZKdo9IGIv620UJo+m9CKrrfbipgY2ZhSYMvTYDg/BOsuF2YDAIOLnCDQMlwnDDQFFw"
    "pvyK5npm/kPcCD+9/BVmZO29SOfwg9EmfgPrPMyNUL1HmJHMLxr2UOAZZYZVdOGTSEf+gDDDIZpG5wpuG0ChZPQi0m8Ucs8j+hYS"
    "dFkNHbzLvn777uMHJab78PKXD8/fv3yufn/18cOHH96qX8/VXVjViUp1okKdSNVBnw6TGVxSU/R6Ma/yZU9swScQr8mn8/iWfiSe"
    "H8ac6dob9M4T3zJeStacLe/sSKRXqLuWUJSymZ6PfH0rfUDI8//WDfU/1NP/v7H+/xvr+o21oK3q+cXnSaQq5nu4fDQw3F7lm9SF"
    "AceLySWpBiF15+0IlEHZfKCuxwcs8i4OoyxF3/dGXvp9Kddwg+Vr9zq56A84f/MNY6MyGj5n0PvMntKssO/pSSNRsSLs3BP6SkV6"
    "k08U9xvcJ5MCRFTQidj07HmnOADd8EMPFhsfFPTEJ8Z6uE+e3m+Q2I+eFCxcTY8t0UlyMiV3A84hZqO5iakLWAijuEKDkCcuaZnO"
    "fHTmnOs/osMhd74Iz0L/bM1jCPvWs2a+QCNv+IuhDvDmgB+ViiBD0qf39HNlvCn7vlbgHo1hdS12JNbr9XJLwZATUXPC42f/iuXh"
    "swG++Q5r/cSu1PM7K/FQ95Dbz6SNQ7xCl3tCGts4poVxwO2R+89V/pIZ0l/OQ+knD6oGOZsdV0FL0XC71g/UqPBh1xxCQs9y0N/O"
    "jhmphC7Tf9JeFvUaXovUhQ4YnL4nACv6hGoJQoOM+AuVlCoRegxFZRY0OWK3u33yxYsVLA8l5KLYG/m+EshFLRLc0lg8YUN7VjGe"
    "+g4ujZj7D7jovdqcEcLF/tLf7L33RcCqhsBMiwv/cQ+/Z/5nPfxe+1/o4ffOX/PwO/f/bQ+/5/6jHn7PfNNb751f9PB74Rc9/F6Q"
    "87Prh+toHw/iVvd7hQUuqaY4zkdDjdLWlT1QAMpAjwjoHl02cg/QpB4UoZgFHSOxk3P1qmOMNJEjRXdvpdrXhbbNtvQdWhz5Drq7"
    "Fje+s3dvjU7vV+NnNjqN+gAJ1rB/ujx5YVsnfgX10ivP9qpj+ICf+Jz+EorAEE4sKGcNt+nTHp3aY7tyAvk5lXrh/7f7ZfjB7CJl"
    "h2Zf6KDffUpo5P4rNTiqFcyC65oj+WSMZG90enJTHeu3UnPaW2V3XVh2LN1gmA0+JxrvFtli6AWot/LDsbNzhQiKHjmkc4A+EnZk"
    "IowH5g3tuNXq0/vnPnvMNE6A733pIk5FefsCLxfmCYYH7DaqsTfhHkUfbYoPqO/Qf29sOzUiam99NmXXesInifQ5iixOnjqVqUV9"
    "ZvR9NlyeTBFuf3Nt8Y5bczBAEqvS96RGfU1p1su/TfGKyx46rX3oCiPLwSEJ1QL70Ol1YcfQ9wFUbYjXqmy9sc8NtNqyffz7+TYa"
    "jXw/vNH3R2N+NdfeNjytyvA5mfMWC5NRmnQMA2ce6gOTGhacvlLfOD6IdJyibBTLGHyBo6LaUjBWJyq2rkIaDYKDzs7OKx8NHfNF"
    "jNHdWYwBHzFI5fDdevbOToxqw1AE1bpy18bK5VogXa4Z0UDXB5EY401IpswhbRXPh8OPZZjMLZX4N2UHcJLor2lu81EcisXz9wom"
    "IbgyxflUG7aNiLLPy1bKbFJmvbUxs8WZsODbr8tgqrYRUDDHaptCZf5v1/z1T+2/JVZLASxFGdYBLgUuA4neAxmyFtvhb3RrZwA5"
    "2ATkQnuwbxWAW/Uc4NAvMuJfOJByi9vUmO5XO27GXpotXqZmj/+2YD8mB84+/8IojxgVk4NdohVMwlYwhSXDtF5Dz3C5LA2Ntnl5"
    "3trh4AYMV7NB33yDZLhhsrCpAcMDfMiInSCP50lhKiuVw0Yv7y85gH1exLwRY95aSQfK1pelwrbaMWNZq1qFQkurvpMAaCuWyjPa"
    "OTws97jH2FVwmxiYZhjoNhEj8RJ5ODDABfOTbhOVL353oEZ0rz5W6uPAMLBaR/k6CoUtpFC53DQsBiB4n98c2TMkXDVCmjdxCAXv"
    "+If1oG2qpqLALbcJ+d7Pxe74+xjPwhvfzievjosbny5ccOxYT+/hPIwE+qXKT5P75UqeyrlrWFPrD+6m8VWAyk7SnaitDPnhzAY2"
    "/+l9MrNCOITF1tP7cIWOe1Z27pGF6P7w2OzypS8wDDCwW7bWiw6gTl85ZFrldTNbaygi+l0XvX3nmh1axKmYApJA4g2MVLRI3bGg"
    "A/aVX/LBQkzEPRbmOeA5/ZMvvvGdkRtO0CzQiB3j587KM6Vl6BaCNOThM0uOQSNn73ReNcUAMEd3fnJSRUVOJQeAMaCtQ5r2E8Mt"
    "TrhyfvKHwzzYckAeksid0jf+Rj9KgiMKSscMMnQrBnY72Tt5NjpJT47Hz4bQwMmzk73lU3v5BL5Hp3CLl/f15ckJl7KfPRku/0G5"
    "/9iU+4+h/rEkJhp5O5jV2B4tPo5HyfvxaPZmjIwzmo+MnvxjTHzzsxN7uLROdudVhL/2wGRDGrpcGk2OqN7Iez4epcf0Hyb/1+mz"
    "sSOdL422TrLxs3n18ZEXSj00g3nVlv6XFP4ivB1aiMxYiM0gtRw5syF3ZvOk0FrWzm388o2QsD+ihLyRKXdF/WSYm9qE6oZAWCz9"
    "GfULkYT84sudpnk+bGU2Pis4sw/ycOb8mkcM2EBxvXXyeFBoRESVJhqSGMk2J0rvsbIFGSaBAvgceDZFJF9rK8Rqit5Wq3TxkUdx"
    "uQeyq0IWhsfPhaTaySgS3tgWaxPWlbZV9IbivKX2taVzDSY/eSC25sgT6IadHNphYEst6tjd3f3a17ZeXqUpYpvo40oZ6GlWNQ8c"
    "raNKYPxoL/epG4sErvPo2bASojvF2KHf9XEuUvK0n8HYjNzkF7X/JK9Mkc08o3scSnyQB1WJ1TUmddB/PMUlUyxWyvwVfzxxn2BI"
    "dDjglDkfHHMhOU1MOVZfaovtEHjElBnPnR0P1j7l4x1+VKuCs4S0w9M+HiGTECA3d1IOhmNtACn1Dothygi5h4D7IUba+c5H40iY"
    "OJzxm7zFf+cbr1botgJZ4Uwx7JkyEcQPmCweHaM80CoZdNglr191ARg5UEqEHL89N+JVqpwopsFj5A9fBzDbRftuNz9Jvi2sXjbM"
    "z+XTf868uyABirJXvDMPIOnpnmFzJ1V6I8NFi34TJkVlumtKI2Eyk1Z7puDEzPCKjzwAx5hLDmu5Zq8yT6nU0SOnLVwe4hYeXHz2"
    "CHTj48pg4qNARGPFSiTaz5/IiWtCPprzZhKo3OeQXL/6zr3yoqO9G6IzRPUO3gdKGceZ6NPzrQhuSY/U/y64A8Ic3Pb3Ti2EeYi6"
    "vss0uPKAi50sSWM1Qn8mS+kp4zpIl6qjFPJncZJOLoOrYDkjLyS+l3zCaldxtMQOlxh+DUoGt1kQ+Us4GeynexfhSsRzXNG0MFis"
    "/D0wiMd60OldmgVXroB6b3DWGNANvn9SI0ARXzqJ5wGGelutxC+GzFB5khIZjq8Pa4p/xdxLvKu0Hwk/mHqLWZZCjvoUGLAujiDl"
    "jL8sm4S59wRyfJDF0pDyRv/ePSdJsr0SPloVnvnZyha/+cC2oNQKTuez8QglPIiEP5KIQIYZ0bHEA6nUvDE26PZvvlajl2H38DFe"
    "hd6T++R2vEX2Ee8IlluZ9ylItwCtAJVSseWHFyHMbevJ2ZOtONl6Un2yi2LkpxxEnCreGxFDyBnUZZhqqDi/+oISzgiCcuAyKYeM"
    "8gGhMmLPl8/8D2XDFCm/nEeuE1Pyck6/eYU/YCrqTuvihup2LpV+p0RzsDOxOhygDOOy6G7wUK2CA18dqaUk8aY5kUyVbFaMgCs6"
    "bMtnQhhhRE18cdgoqJfZ4ta3zn0MR/IZ0TzfNUqS8RVQJYJgGiTXQIucYIXbMZxsQTNbanlzT4K/+qszem54nb8MblEDn4K7Ibek"
    "1pPxngCsbhx6z9yvdLGyo1by0GrgKvtsXTnUuKQJSHRVp0NiyKAIOZUkD6Zki2VosNNV5J9IDlGmuZj7HgbeVaE87nn3Z+i7L1c3"
    "C5xzBdgCqqshoKsC9Tn40VfOHnnMdmE36BVCr6GKqsEFrYjLV1Op0UBYzPFUUfUrVUivRiDrUc6RRwoNwBDjelF3pXXhMVA2N1bK"
    "p+yh7AhNoqioHOXmsjJTF+YJrPVLqStA7OPi5jTNXTduXvadYWPbpap5J/hct7n2eOX5vlEvZ1W264NitBKMlFBwhSfZBvIBPXhk"
    "cOxLZXM+evdER47oEgrXeEXPdhsm8kB9FVITI+FtWE9ezlRlKkoskVriskYuua13KdKny5mTS7QHdQVD+N0mpGBsWKU6W3WzhtF6"
    "SOwQF4/Cz2J28Hl83jR62Xw+/M9P0RgezvWHjVgt0RlnqwrAdHFLD79kT5sQWNvcNGQ6wR6bmar2V6e23guvFqHSm9Ipq4bAmfps"
    "tmQzxRYeGv8DOI1ANptc26w5LzBeFZikHMPyIrSVYHprI10vaWya9fkWqU2Z61iFqf7BddcIVLmKIlDpWm/GNMp15GQ4PtiXV5Px"
    "xDQY1mf3QEWTjuASsSqt8YY63S1mMUbRFhXlLbpivcwrDHBP73+lZmTeL3zeC2I1ZB2+HmyuxtTlaL3eC3WXeKzeiw39LdIsvlJE"
    "i6oKI2SysWU1K5K/ZOu3W9jz4UUEd+F7fTlCvxhQL5IasCHcH4bDiO4jxw+XEXwGmIO2NOXIB5/YOfXM9L2nyPDwtSMUYfk4TZmN"
    "01vvB1RhPTo+Lsbn4iHkBRQRVu3TTUj2WdrEqzIuaJceqhfyuaJM1ROzz2JRDh5R6ti4OEmit3Z3Ih6yNAxRuGPoxcwR9Vg7Z83H"
    "CFBPNmKuUXjD+mS8PvEcL4WS/e0nw6E8wRU/LFfB7PihXv9j/cmhf4/+Iphybbg8KdojC38kXuELCyuSKORdebW5EnrWxwvqhqw8"
    "IuKDhxo9KbAPbHX2bWh/uXywAaqLLoutI98WwdTJHdMLT/pEMKI7F937bWXDYVAihhxW/cYveNzdvvHVC0PB3f5WjDIi5YCsEPhU"
    "U5f3+L5lvCGZ7s0MGRjG2iw0QLK1hLUWMIyA6gZoBtxY4+I4pHfd4jzypzNpueLSuxLQJbmFEoFRbj3cYSbgcj09y/QDgjLiQsxW"
    "wzch6gIEB3nQViUSDZ0XwBRjPN5BMSBephysAT+dOHRTSzDyGL57hYYppI3xfFFPMFAnFLGVZxPiSnZxPfnqa8X2AG4m63lIemOR"
    "qigbLGycKE8koRkGfDsUM2eysxOyqhQOKlotMU7GUr7I6QSX/KgSybRm6ppLfp2shRbgLJfQGDMNM1s7fo5H3hjuXUjBhY+SSqVw"
    "iL5ricd0pNEoOWbdnE8iNReOIl/MHyqDZxQVwXFNd3bmOztTGNtcS3CnsLxTqRPpybVHUGP6vJQ+WJALjhjRiDqvYvMWaThj7A3b"
    "5afkBVe3psPhXPl0yhuRUF+Ycqw3vrVANFgox12CoIbrNhMLjQskKinfKD17CPvLvcclgTWReB0JDGm+sPuLlYimKFhLptZTVGQV"
    "ydQp43R+3xIUqyWespaeas1VQk2EpeuuVOQKpouJ8rBSrZIwr7J3wXb7FAZDC14Tpbm63jipj61WwpvmAsqYxvvUNwfHeSLmYni4"
    "6N1KLmQJ+5TmhoxNiPtGH5wpIoo6fiewlNq7OrkI3mVBzHAY61IqDZDd8rCIKWAtFjRzbOUqz9N+fuQ09VpuIro/Tsjh4vZC0zYG"
    "1kxMdstSaSAKNEHfMexvtJ52Ant5vY5yijGbWuuZuNf8nR1Y/9nqpIb7HP9NaMXpK49hUusbfUqXRcN6vwEIOHd8Mpyyppr8zp1c"
    "nrsNuUgNpqhSOXcAdY8xKMuNbwOJRyyODCyeidH6MMdIDWGcls8xbZwUNravY9r4tG2mYg7kRsxXIp06rVqvIyZTx4gvLGa0KSQZ"
    "mBBjYtpbAd2aUkOBfPSmmMSw0ReAexTBit5RvSn/kLsi1wCflkLnMB7rS3jhdj3YFACb3haHH30LH2WNgJWsNh1UogrG0EWjYXHv"
    "Z31vuqJB2PiWA4Mkr49Qm0LkqgKFWLnTqXaDpYeoBX16V+hIP2yLiRshvxfgyS9/rL+ZYLymciK64o7xXTHFfybO6B5Nufr47JBd"
    "9pOVfEeeFEKbFspkK2eyO4/nVslCseh2R528qNWKmsawuQnLgFY+p/gz+C/qrkT8MpWi1ok9kWr21F/I/c1WRmiOwPndh2MMoPYe"
    "XwtnyD14eK4b+K0OVdOx15++RaytyYWgbql89JuhOWXBG3BSQYUY1DnWzJV6663UAa1j6Rwsf8irot7NLrGB9GIG1Ew+kWlh8L0M"
    "gySYi+jHwg8ACxOPr1wzfDrqf0UTk/ry8xzXTX9TAfk6+14+BpJtnz2Gi55zL/mOvuzK3G/MiphJK7zYAaLcJxgYon9PO6J/D2DP"
    "giTq752e7JIHMlRv5kci++ke1Enj2bVxmZeRWqQHLI2cgWCLN59vVrLVkpfjFZ45WZYUeh1Zu8/sk/EjfWGVtcdDlLMDG7B3ap2M"
    "Rqcn4/Gzk7Gd+3lSXQ5demRUakr8izQ7gOx94ZCvAj/0zDH/k1K2cOCPDJsK/RUQ8Tuj2SGnPNKXeprMgaTGiFQkSNIqvY5WmVXr"
    "byEnZX8xACYk6gDM4d7R0MNSeEBZG2eJsoLVyhwyU3+TdrDkDxHSVFyjR0jZsn4Gz4sScy/FfYH2BKiKKf9eeAVSPdsGtyqHZ8s7"
    "LrW4y52ZNWDkZ1mcv+1KHo7IuH5AUtwK0PpcMsVcGgsC+LkHOSf90ouSlyR/7w1z0HlK9BLj82260o9VJIvWwpoZkvWF8AUcuhw5"
    "gV77Z9bEVjXk23k/E+r1HDrmV+/+GZB0cY3qqDCqe0KLY8aKu5VzLc6dY9+6FiPXyEGH+LfO2XqN45VzK4IAq9yuVzly7rgKYls/"
    "C1bOkYio8BEUprsClEogxSh2s3KSQIRUDD7ycl5Q4qOTGakYSvG/XinrHpACDi4gq/17FVJxFO2a1Jc45Uje78YrMYoDgNTY8QLL"
    "1dBDWSAwRMCqyhwFS1ecQwZcMnyZwVcjmBskT+HklMk0cpFh6lUgLtdaCTDnIhBnxWZCTL4OxF2hmRu6D5HctCjogqGrmvm9gQ7L"
    "EG5BMXBoTgqXLooJuaE6JE/Q+GIBJPHxhlYPNjClujzOzVWRT51PgX8AmAF8bHH1yHiucDwXwapAstTI/toIr0utybE+PuRLHPIl"
    "rg+sBexwhxm8Cd48iMkDPCI+b1Z8vVnpMJ5qH5IS4kJxAv4q35aUM1U5cEhfzOJzb8bpVyr9csWyuf7FiizupHzXoDRKpIukRhGK"
    "SBGdhIhOmBMdLyc6sSI66SZ57wQpETBldN9b8P0H6Y6kOBkyTXCNjh64jS2Ar7dzixvFPrlVrcDjEgM9cbIiYVkoanVFbNIl0qwL"
    "JAmTEpkRLheEDyiIdOLMuVonVNcr50zcYQNn63Tq3FkYBAi45nNxjEXPDeoDRO7aKHS0cgIgRkSlApNKAX0DuFxspkvJuK9f+i9s"
    "cWev8NqAMluqdfz5Wsc20hNV7QZr3X6+Flw1j1Slgb955yW4TaJgjUyikviG1I07MeK9I9LNOzERN+tUeH0PGq24QLdgD0ZaFJfo"
    "rxv5gTGEeF9e0p6cyT0Zbd6TiE2+2lZTuavmvKsY+7UrTqUmDqc8v5zv7Ch9cHeEDl6qVNtHH6LB6snYhQWhR5n3C9jagHTyuMJQ"
    "feTqd7VFjGcfePhMFeXHhDy0gNwqcHHP8JJSeOWBI1zfmLUoH526DvPHo6T4TqRaINtee9XPC9LyFMaLoxgO8zumXW7K/Alz2tRA"
    "sRCGnRDG29v/DGfkTKR3S9IVHO5ifEnfUc9Na4ucuxlSRYrUVZHWRd7NI0OW4zSBw0vsy8OYhm9A5cV/GCpbk8cIrYLZTE9mgTDz"
    "nVkJZpPxcglpuaIlpaF0eDMcJ2LxOBwnCo5+3vVfgeO0CEfyefMCcO4op+mmn5uyFqce47aj/SRu19F2n03Z81ZYeFSMv4OjeaBH"
    "eZvAK7a+RmzXSGO6PIahVuday+pvKP1IcfI3LNZeW6WklneJ1lYNYaXzYEW55i6QznCXvBEtl+FuJONasi4n+slgmxqx6QHzM6jL"
    "74oJpn0RA6LeHzlatGI9cCkXGu+KlyzVbRGTPtsRtwxo//0Cg8trF96DokMK5fqc2APbkAqa/s9TFGt9oS12xFyKZolezjBSTIpq"
    "odLi6YBgQMEZnCcyXmz6ZEsepxJA2stHak1kJHWtBo0yKSjurw6f3j/H2a0O9qjaoZs/bMCNZ2xrgRUffv9XVvU/sIwCtaxzX8Qm"
    "yZOb0qC1C7tfTDqCJJu4V6BtD2CDP/xryxKsL8tULgssvG8bS0M7bK0ZFLRQQLEqbcfrRcAsRzX0leNy9LQiiipvpKqsrBQpGJPE"
    "TS5mkacbW763Kvm0eos1InMVrRBLZh78guw5hibPKCTrjG1lt7yFesjxLNi98RIAKA1vK4qzrSk6oYR/ky2S+bLtoS3cs7OPb9+/"
    "PP7hzU8vX5ydqeckjw4m9NImXbhgJ8VADDFadkuBLVDchjZRHtXG8j0QH0Hr8od+ACDfL+j5vtRz6b2RBI0ZvjfKinEeTrFUE4+k"
    "eANQi8bzRuvSS0DZ1Ilk9sqQBa5H0ip4cpBKc6+Z80B7YkIAmnGz92ExqhXcxpSdcykD+CAWkC+cOvIDlXoddkSVI6cM/IN0Z2dx"
    "WBvkJ6thQOuzTL5VGy4qlT591oeLapU/W1CT/SJOpZ8Ea+r4QH0rFTT3wsfr2nI53TzgmR4w9jvX+Mfj06GrrnTGtALDrxaCsGX5"
    "87U0GeJ3atlVbKrA50WHc7x/0/IV3iQ8o7hZda5vRORnqPAje7DWlboAcaX8e6AAwUj6EEraq4nja5Nlg6SnBSwkjoA8jZL7T00t"
    "leD30t68aY/CZLKYod8WlCIH0STY8oMMiEngb3mZon/YAO7gwpVbvSCpAvQz1d6MpJq+shHLByIy4kGcvGJGqllhdEFecZR/AMzm"
    "7Wwo3OjE/D1IB4LReQppUid8YE+SLSRsOyP/XqbS+xWKNSSznQ7N5Qzlm3mf9DoKtVmvZtI3MWEiiw8+FLV/XhZ/Js4HqQ00K1ti"
    "52bYM3zfmGkbuh8nloYbkEfWjNrSSXBTo2e9f2nNjEdoHRUyySdZooUML/UEnuA7gpM7oiqxWIEZXSZAC1F55MQO267rN9L1d3RU"
    "VmLNmd2n9+S8B1hW+guLkAxHiQhUmJZdNMGVT5CebU8sFDTMCvv7nh8i5ZSB8ZDyR4PFMEC2q9Ri5H5/sJxUjeEd3uerh1AnW/5K"
    "GMLZ7YTSqDPDsESkqa/iN+hxZjzOtI++0AaZPiMdfOSwlCog7njj6KYapCCRH5Z1dViGGPkBDXlLKkFDtCTjtNwMWh/JHiCSQqmE"
    "zHfRT6u+XNlFda1wTV3Lg34DmqyXd6xtNotnv9mRpnjaSFKXVKMV0Uh9og4DWtZntkDYwmUPQ+2o6UwkVoqQOGFThdn0vcpSNqnq"
    "xYREaTFIdcFiJqszJEU1MIxQhrUyOplCQ3ErIT2NXN0vlLFCo4cxn8IAGgpyaTGCCEI8XoM4ckIAca9AYTzlELnowGq5lKiXsWH0"
    "RD9zY3cz00/Hhj3BFO+BMrwfHJNEqL0hT86FE4wmzFIupPaagg1VSAjCSq9JKefkWiYLAyU0L19kHPH9iJ8G8cEQRSB6gOTZR/J5"
    "+NBHHysxJebKBgbGKpINX73f4Gnvy1cbe4BqL4a2Qq7SI+ec5w6zfp7NXkseOfe1vqIEwtQWU77HyXvS+8UsyBUsnaLFrWfL+KIq"
    "wJX0uksv7dI3hoI1edtIbK30yfi2J6yhQ62dWPaeXVBRKJh7c4/2cEQXoi3SxBj3R1be387O3imNbvNLPsVkJ9auje4TKpkwW9IL"
    "C8P0hv+HvXfdbttIGkX/z1MwmUxG3AMxAO+kR/H4bie25Vhybl7+TBBoiIhJgiFAy7LMtfZr7PNv/zn7Ac4jfG+yn+RU9Q3dQAME"
    "KdmRE0WxBDT6Ul1dXV3dXRft9JEG7QqBtNXEV6kl8zBMnxWWQvsLv5KbN0PKNqycZjlDKYb0wmNqkLjPxXVI5shluj4Ib2ScgSZ4"
    "XJ1YoW7w4wlfeR47bKYhIPkz1quSWnoUkj2sCvFobKnq2d2Ux7mwWdFpAESXm176HUT4uZSNb6o6UOyqf65oIq3Ropn6jsEIt/+i"
    "cpJY9F4Cll7BgKchjHmSha5PknQDrlFqSDU2UWnfQ0eTVK9qSMf0JsYxW9NZxy9+2aFBekRFz67S9/UNWNynVJ2HSZILeKVPljxu"
    "wA4t12hSP+W56hTj0GJ6MMY+rOk9MNBWaj0giijhzYUO5FrxdjpJtdJ4vtVUpFCFn5Pg4Pzo+Nbz46PXPz06fjgcpRNnZN05fHp8"
    "69HToyHa8yZuOI9H1tPD49dpOuyl78hP957eFbWQuc/ruPfDi1uPISf5feVOeXmRBqXv8eRHT4ejcD6yHt87Onp9/PAWvE4T5fX1"
    "4XNW7PXxIX4CyeXB83u3ju8957lPEj1FL3CCBW7fO/7p3j3IOybJKcFoInch++tHR8j2E/IolgmvAUqR+DRKePrte/cPn99j6bcJ"
    "zEbCP9y6D62y9FtBQpajtfUa8Hrr6d3hyMWLwUP4GkFyOjBvqSv0L/8zdsdk+s2ETBdkGdf2eUjULwVLeRsIVU/mUVT3t659aoTQ"
    "MnofxnlOU0Y30/1XNuYqWQ8NH0mmTr05FHCkWTfMU5aHGZNzGOTZ400BgwzeurZon5V41gE72WaOPrV2mU908jLTs1foSWT0n/+I"
    "99Errv57njuPoe575wdjar0OslGdup0lB7DRoT5AqZcTiYG61NI4x5P/+VD5Ila5b+VhyM1zHwRLVC4a8ieHi+rk5fJf/3oF2wyi"
    "YZf5KcClG/jWOue14NEcSoe4m00wcmotiWqsh6QGEuw+fQY+KnVFG397NK9RjoNZx6Qmclg0v4sIqDG14Lg2W8VJbeK+JTW3lsPn"
    "Xr02I8kk8tEBAtWnBnkOXUik1sOAEAUZqJ3IgyKsdTRhacKjw6TeiqgqNqDIIlmcxNgOyPqIFKUaDMwRgSjQYBWIW3zxjqEbwjkA"
    "cEbPvbkHCHethkAeB2qclXRnrm7IxRUmy3pD+JqVTqRFJ/my36cOW5SoKKNDoXWtTQqqv6mlMC5t0TIgnAgp54gkIy2UY52F7bu1"
    "PKHu/lEc+ua/9m4OX4QfHtXnCTz1PzjdD61mHR7vTN3ZAvXHaA1CTJnXb/L+iJMNJao5x8leIjCafKv40dlLUq860t/unG77hZR6"
    "Y/7vhDovRVdGB6hjK83LKeUcAcNj6nPD7NkjOqmjxMVjtKQ+zVyK+egAWQHsHW7g6GPzUSMGGvpiLz6IGmjnRmnoBqsFNwDy0MU7"
    "EP0B5uLRcIgyXm7I/F1wpb74JZC7hzf7ICG5bEvh1RX3hFS6oQ7DERxYb1cSnCkHZ3UwzYHjg5DPzneDg3AKLfjswC/TcpBrmR0p"
    "rlmAF3pf2KCGr4K+p40APR0oGSI9Q0QzCEzCPGKtDc/TJTwzFAwnkgKQ4KRPQps7P6VH89JPIeOVt6Z0WyaipzCnwjBDSLpRSy2v"
    "bqGzvk2ZU8MuQXYAzHJtCTnj6gKeOoymZ0vABVMR6HOA+oBBLQS0TwkyrLiVoJU3xCnYlgyZLgmGo5/JlblupHFi1K5Q5/ZcJ/8L"
    "Z8gsckKMU5+Ix5sycQ9xlaRvw0rAH1TDBaWbe9vATvfjDHJ7I+Rf7AD5F1UhD+cayBmaSc/17JRylDUFFxLVGTaeu9HjVRpUTJaQ"
    "foktLq1n2swh6aX9Kn12Xim4Mgz4TcyeIujfBwrueOB58QUrU1CJBf9NI/qyT2trmpSCtiXN/VsdN/JvVCJOyKU2cKC3QNVOLrUL"
    "32oNfEvrv9QufKt34VvsAtusbSASGQ7AIBOy7QE5rd2l/pJgYy5udLQ8SZonofEokghfxJyhLENPqgvgYCf5h8P3RSF8bEf7BwBo"
    "JH0OFN1O/5EwfavBRA2YwjgPkybuEXq6b91B86iso5Kh8Oxm8N1i2HUWOHGxcl5cTLv5cncuVt6fS2bTWubYxTJ6dqlSQerixTL6"
    "eNF2g+XOXtbWqWbimR6vHAdiMaXyCUgep9LgE/YfjbwXnIQZ5YcyDjxa6PN7EpnGvVmrvcT6hU6bkI7QXRYqR8Ssbq6LLs7bE7Zf"
    "QFYByxs6TN8LP3w4FcanYWp8GvKT9ZeAC2FkREPg5D3xoEcYBOVecDD6Gz8+VJ2G1s5pRK7h6YQsyd4wjPe4/jCe7r6yauxt4e3H"
    "LFwiLMXW1iWGwzFlIruUdHGmcyjxv3H0bj8O38MEHdZYoMJ9SLpBv6//pjbAw9tt3aWXVJXqn6z4P1/tXAFV4rpA+Xg1noVVK1Aw"
    "5C4WMA3wQAgwRDtxI8We6705WaKSE7O6G9boDQILqmjMFs7cE6gIr0yV7+xcu2bX4mga+tkPNOzhKobv6RcejVJLY+FotaQAtkzD"
    "WjgHRISJnrwfEBdmE4FeJ7A3P4mL8tELBsRLWU7m9XMfuu5RsHIZOH5y6ahit+9Ow5N50Ud5KZNFm7daxljnAoO/kWUJ0YpYd9uO"
    "vWiBayeaWmARErcmSh7vcOtyMnrh1iWjRYI0uLgI/WfI9pr6L0r9EZZIzoY1x0RbWw22MmTAKsP3gOe3GGINNpamuiuuF/RebxJN"
    "fW3VyIKtdJEZ383CdzAzatGbqTu2cBohSdBPtY79D0sllPoFoNs/JeM3YbIfzucU/eFchI69QGXRKtErUzo+oQHEhzUMdn0JcMcw"
    "s7zJvk+8iFlKKU2JPOb5d6FmUeRHM559jBSqNClCfwKdTsM52Q+m5N1lN7cfhGTqx/unS+yYSlTZSZ1pc38Wvd9fhTDW9Bpn2zlB"
    "BZ2J60enxWhcTXdgqzuUmZH5alv4p7AfYjrhWf5pYHzlqGRRCrfGH2XGMIen7iImdKLTpxuGLMUrPR41IlM2Aua5VLlhh1VxskOZ"
    "rUmoVFShi8UpZw+5r+UDMnG2B3/S3KFMa4cy7R3KdHYo092+zGL7IjRiJ9m+3HgaeW9+X0XJDmX9HViEvzV1UgJk6/6WxJlhIDpt"
    "bi18FE1/sRrQWZSueEWMojCHDh5bTcgOkvSUnKDZ+U5s0CCsbs2Fw9nJDtuGtzsUehv6JNq+mOfCShtvXy4MlnhGtXU5MhtX3KHp"
    "CzC9iN52HKWoQyd2OmZCZBZ8fhb6/pRc2vhVHwoF1pn7bv809NGAyrHtf1wAGB7MnTKCnUHLVLKFdDxZbtt1UaO9eSvFpY8kWkhk"
    "LYzSa7yawWQ925liqCQWJmRmqtwP3Wl0cmlcpeJGV6GQrGz4bl/gcKfNuwnbJsE8iLxVjOf823Yddlu419CJZv23kXUXj1jx9X9w"
    "MtVPPXc5yWws9qXpe3blDNxZOIXR9ZO9fyZni+gE9ieTswZ+a7Bv/6xvf4RAt1FiADJV47cG+/bPeh5OKl2HIKnvEzzd2neppat6"
    "MDMPZ3yBXOyzF6KXe7dw537NbjTjGnFjgjtb5egBWF0wxe3QBHgcmZdBMCXuW7IDBGKPsBMM/3lDzuhSEpf3TxnIZTRTXvG/k2Xo"
    "76O+3xRLL6NTPEgKlikI61TsiCqUdfJlq4IrkbE1wM4FALYLAYYxFueiVjah9j82nYJS7sQOXvfJW9Sly3KYVYzHKOycM7/lNrUu"
    "J6c8sDWdOeE0Et8bPDU3gUKzZIxlMU4odXCan3X4SSnIWSpGZd3fX7yjn2lFVrYihTWI2b5dKTxq2Y8nwEHfZOVFDhc9kTKdD6mT"
    "MM0I8y2cB+EcFirKhVyFDLYsIghctKgSugky+x8ZupSif3qSv4wwQNue7ZMTBQuUqjdlSicASkOVm2p1BlUay2UrnuR/sb4DHSK/"
    "Bhlof+bGb9SlV8oSCtljnv30CyN+TGykidoU4KKGzEbf1UV3EcUho9ogfEcUKQlkPk0cmpJAlxlz0rM6UXMydaajW62/+YJphyjC"
    "aQ8a/ortbf9ZR+8Ip+7Sj0tB2GYBzhfcCQTjemboXulqplKGUb4sWc0uh6oECVfrEkNX5S5dFKyN/S7BWUop7tybgGDsy65sQ7Dm"
    "wrWWbc9iWPnHobc/Ju9DstxrOAPLsRrNpuXkFs5cLdsQrLlwNRDKxZAyUi7oeOnYSxnELmSlMSpy7tmNQau+jaBYgIPzYjK5KCyK"
    "U/XDalZSh38mK6lD3UrqjWYlpTs9R4VsYxxM1k7MtZ8OyvLQ2H9c24m7P5ZdTpXtqkTbbKSxNtGskXnVYL7K9uaKdasSWvkWHV+h"
    "HJwcODeSf7vCBEYNdc27L7+9TISC7/l6qKbeSP7RvPlGoAWVzr+wU78Oas9+4ypiUKi+rg839DC+aQpLSt1GbApFigEU60MVJjNA"
    "5rinCOMm7M9pQDDFt5ZE8G+BrlS+lxw8QeOWOsiG5GZxi8Kdu6XFT0XzDHpPId5Pl2EiY6sOCY4KFEmbfxJIFbmDpwiKNMBKpy5A"
    "o8zFZJj8azRKa3iaGnPRiaFFriGpzyJKH4obFtWOEG2yhOlbEj0TLnFf1aXrAzFRhHGbxXwjcDMPaVIkDJ5u5Ez4/vMfpWJmcycM"
    "c2rSB2+NOWWQTtCYVyCOkZtMHXfI4oHXNR7wTEFjdnp863z9dToBnFeyTzfVVBys+cH3LvNGNBf6jHPF4+LXX38xb4Qxj60lMPKF"
    "o9tJcrX8JeUYUClVi73xcLkX1q0H9Pcj/M3C4iQ3UT/7EHknVU68HxzY1qNAs7u0HgcHBQ7GRtZzPYLH+wDtEiVabkvifh8g3/19"
    "RZZnwqT7Fowjs3d/+dX542B98NW5h1qe61eWkvpfLJk6sPsPDMyrkWFuStxTvWDpG23vccBMvQDl86+/fh5wzVqOuhuAoB8D6Yd4"
    "2VjNqTYnKnAuyQyWU9RgZYj5MUh79fDig009LQF9fUEjbKFeKtrewF9qumO5B0t/r37zNJz70WnDjzxakhsNUoceIs2KD6LUO4Q7"
    "jNBNciOcUcf+CUbQ8RR/EZ61OkDf9/OVO7X8g5US03uFbjuZAfziIEirZCP0+qvzf/3rfrAeDQNrhg341uRglnNUMbNOsH5s23p9"
    "cJL7fmK9xUaiuUess4O3ue/oWR59bSzjxHp3MFbAQ2/LSSOac+Kn/uRzxY+sOzQTDyiHrpfv5DJR9/KYCxV00anynOTyzIl1ekD9"
    "NC5idDN/muaA1ewU3cwDDuJoSgVSKyIHbr4SF93FHzwKLOod/kBXR2erJXz/jhkVncsho5z6xhNq5vJU0WSWK32MTaGtNK2dus9d"
    "KdUnwpRzZ9Kkro9YLdEBCADwP9Arepx30Qt3xN1/LoC4IqCEDx8mQFYRG9YPH86weES4EzGmSM0gv7HkbrcSnGzMJNMjBx5gZ29p"
    "qZM5IsypBdWuRv9X55Qmhu94mI3XFm1suMK4tuRmY8/DsJa8NWB6qamojyF0ZGxv7iP5K9/y6jdvejfeBx8+HPiACM8CVoWutnzU"
    "6WbVxDq7EryqwNUi5VI+5U/oEAfY0L0pQaTePnuEbmAwkflW5Ol7wtcH8FDaT94uOuLmj0Bid6L5nHpSQ933FH0g0qxkAR5lQ3ic"
    "HFmhP5waMPXuZtyYENfHeBQLMvdFBfUhT0e1qrl/ZxJO029WLJ9hIUD8KC1HKajRHI0ADgzC+BIHSLjV8JBcCRsyOWIwCHtACH6e"
    "EJjuvmgDe4iWnIA9GDN0f2L4cgAww7qtMPZERa9KMOjtei09PE0xEBbUGZGbK1wVYU1foT3KOaBzYlHoFxaZDkPqbX5prWiPcxb2"
    "N2JctWlbdI7u1YE/3NyTJM2tKzyiEKxTH+7tERVmwhcjzHYqEV6ncftwqNj6lBmqtD5JxMyP59qioMKICYuH4fco5ir25y+qbeRe"
    "/Jk2crTPdHn/KbAeBNb3gfW7ss5/92fe2P3ycTZ231XZ2P38aTd23/0hG7uf8xu7Xz/hxu5XRUj9wbixe7FhY/dDurF78ck3di+u"
    "yMbuq0A3aYSlSngas+uCOoIlIe/JXjGZni/dUxGATS+T4A6D8SCyODBtaHxhuzb6W2Oxzy67913PIzG9G+ZHe1INhJ3WedNwMayh"
    "i+s9u0Z/+DGevLkQCi5CJWRfpmRPB8037Vn1kuKT1PTuxR2DyAz7MpZ+OoEFgho+UL1k1OrmHxQdnPXf/sYvNBAE3n3e51LA9pes"
    "o7BvBEnLW0bT6dhdNmjdQAZY82htJQvq9Jb+Xi4M0suIbU2ZI22zKImRJqmLbZCRF8LvGFr0jaigQBY8gMhd2AmgNzcMLL6wmJ48"
    "iyY9nC8sXZa4lP3lXq5wUy3cNBZuvjKuw+gXswFUfJMM95StD3WK/uGDH9T3fkJZGqbLS4zXQqPhpMGm0YFa/Sbsm9GXfd2CtYdH"
    "70brUeo/DdkoQM0ElTtHR3nHRbnO2GpnbGNnbIoJZukpIU5UL6UJ8/6OrTKPMOjknVgmOYXJb9S9H65apnJc0EJ/fdQj4yfrhYTl"
    "XoDY/YXu2EAixFhEwhEeh4ltWUYWsiRcO4x9van1dkjWvGeUXvO94m6xd+/cfFdCp/7rFYLMYyR1vg+LawbycFeQRyLa8t6SD8WH"
    "D1/5dT2UUcI3yoQdq9Aw51+dYwk5aR5kJw1G0hARcVgUCxpn2TAn93bEGIKZhsiQM5ASL0tnx40fr11Wf77puyImw0dqWtafb5rF"
    "eci2q4lvubZbatstY9uttNs0diQPdqM0T5vIRGehYGR4YBEQ1ciVA5E2QclTQJGN7XFpXAtjg1zsGEqwVrELWUxTbisiKH/4QJkA"
    "RssI9r7XJhSfU7gUWSFG7kgMkTtgcVrWS6J3LBcqqmgginzYFIzNId176sN5KYjVk62LCQbf+Xvk5u++OE9mcbCLiAMPqIsxN9+A"
    "uRF1dLBPpdMRxd6SY2+ejWzCpiFbpMpwBsDsvNDkO1EOfXbVrLPwbDI+y71ADdCS5dqmXlxcshPYZ8OWC7ekMxfD4l4ixfKF5yMC"
    "jwEmGOCXBvIryShoHrGhlJXiTo+K4zdHLG4mH8uhCHFIBVAhFoUHwEV+zy7Lgu8wOUJwHryouYegZEMYhhgPPD9rMJwAHg5uiOIE"
    "hLekhBZxQnNN8ZnmShwPHgfTgDkpDCL4TB7ETQmf+Wxjwn1R4lqo+L91F3uqb05x4cT29V+I1+xB92ixj5vjeUz2mU9vMWtlgcwh"
    "uB++HWFkq9A/yJZFPyoIIHL7Y+jiwQgGfohKpqE7vSG3lUyjbxwlGH7a6cKukW396ON7ajb6bth02r12v9Vt925kdqp0ozq6Ibbb"
    "bpK43uSImvvunc8w7PzIm0Yx8Ufr+g30Uz8ny4fHTx4fjP4NsNdgYwnD505hr/9ljYJ78KXYGzv24l3NaQMYimLW3wcDZ+yMbzCd"
    "xb8HQXCDOhvo2nbNaS3efeM0mjUWqnt/FVpoxD2FbTJNsGIgs/2YLMPghu7iAPuq2CnbtTY23YRfy5Oxu2db9KfRrN/48lvhzRZP"
    "TciLR7XHDOn//gb68+3IkiM1jvwz7U6A8Bj00eLggbdXT2klXlQ6PI4Xf6LDY9rn9KDIW/yJD4uni49yWAw423xYvFp80sNiFaZP"
    "d1gsOqkcFvuLT3dY7C/SpT1YmA6L40X5YXGwkIfFdGJ80sPiePGHHhYjTIvFwahpN7v7jrPvNEfWbHFwDqO+mFLf49TTDw28DIwe"
    "p4PFFzr+Ql14am6BR0f0uXZKXfRLp7uj1Je/6tV29DRKamkEAOk6dnQPnngd3A3rSPjzT72b0tJEJt9nPqIhtcYeR+hAc/SYxHEt"
    "mbjzEfV3mb7XoiUrXUuiETqqHD2gS/yS50bXklqSXoC7hRyhb79aGI8UV4wiDQMCjlQXiPLDmDv5Tz0Ryk/UyG/EPNgB3vDPiEWC"
    "HY5u4R8YJPTbfAtkitETfKrBo0icn8nEOeSEBR0jUEBJ36/hE+w46Q0sS31On/kHPJtfAPC/kBhzURNjQCaAMolAjgBY6N+RtVrQ"
    "Q9/RC/oXvqOnFgDmDv3LAj/hXbGPw84fRxYux0iAo2fsYYRupclR+J4gncfDl6PbILR+j7+e4K8H+OsYfz3DX/fw16/465fbo1eA"
    "uDPm0+/l6AikE/cMi0X84XhFYvb0E/Hn4vl4slryx/vLkD0coTkjPqY1Hk2iZcKqZXWyClllrBpWAyuulHwSzmk5WoyWooVoGVqE"
    "loACsPFJJgL871CraUmhIuMlf3yCTnLg7y2Y3FP6jqnfrTCuFvxBIhjdWp2sUNocHcGwoSU51n8IUgF7egojyxPvEo89qk2Lfn6H"
    "tI5ts2ZZo2qTrEXWIGuNtcPaYNVDzYxKfmFUS59rv1DaZR+eYMPyC30Tn5Dy5Rd8GWE45bdQrYtSLGyu34bRKq6xBJjqIFOLj0/h"
    "WX7AUgwAWYaBgCXYB5qfJWJuDpXMzuHC/PwTLcCTscTDaKXWj68sP/tAs7NEWn84XyVqH1gCb4F/ZE3wD1jqiABP9JVSLIGVEh9p"
    "KfHBnQ1H7gxKw98F/E0iIMrh6DiiZH5KyJuHxKWBZH56gxNvGSd33bPD4Cf4MoT91CQ6pX2kvIhiCrg/Mqf7sDd0gQ/MZt/4/jdn"
    "tDL3DVQDv0dUV2cFTT6hf0ewL1tGOMWP6F8Ax43jU5D3Ye2fIWu5R+0NYMni6cDdIf2MsesnwJjRVxoy8CWJMTQui6YK9VKnUTLD"
    "ub2WOdwlqblv3XCKcsKIh/GBlV3LjKbrcY19I6LVo1xWaFjkoUVkRq31PHjIyIB8Y6K3isliZcp+h0rwc82jybwh9avsU43Hx4ZB"
    "hnV4eA6SP3mM+xUY3iXypQDWP5FyH5+hSVideQqukUey47hSD0dODf+yN1jB6Pq9pmmxwCBdXeBXDnWo3mPIIJIxC9124tJFV4sF"
    "J+KUnBkdMwqGZ/dteMIMZEZP5TPAQe8+j6MFkBN9rMEzkBywNZr4BFcumfRCpLzgCXej0zlPwkeWeJtttlkyexE1HoOUTxL+KYlq"
    "7F18PYIZ7ZH0K3tnX28hlFpxREumCppJq4VnEjUtYOD5kD2Dx9o5Jqz5XH2WfryP7zVMAHnG1T49duUXRLDyhfIK9gWHQ/kiWQz7"
    "igbUz8hSyfAcUmrotWxBM/y2mi2OI/x+F+R52LLPeb7v4AP2hwIvvqn5H6EsacpMPwi6g+ZomwrNCtKSn14otMYM4uWne/SVEiE3"
    "PZef7vAEnAXA7gTPma+AvuCdy4w1TBlZk9Anao6H8K7n4BFJRkLUZO+HC7b7F+k1kSAy3KF7dxB3E5klTYLu+GHaz3vwAsC6bwk+"
    "AZhoHsUSmcjFkpnYxT+gp44fQwI1PIanGj6CJAviDkt8AE88MZ6GuIAe4R/+xvYGyBDSNyDB91E0e0TdWI5+hccafebJc5E2ZwmH"
    "q4SnHOKgMivb5/RcC/qEL7XnLAIi+/QY7VbFF3xhXeB0wiK/1bAro7WIQ0LF2yeRz+PCxcASkZ28PAkaSrwxC15FNDF8VqOL4bsM"
    "KUZfaNgwkY29vbLo1jT0aM2mHPgmw4hpL2qIMPyghg/Lvqt5X9E1lzbI44VZ6SOGDpOvLGKYfKVxwl6trfc05uUQz//c6dBxbNvi"
    "1nVDh7Qs6oUPH5IomibhguZY8wD1/GwVphueBvooAchrBPoiFfkXiUQ9YOiEHLF1NMYtO03AvT68OWvLixfDc6bKK0IHWZMFP6hS"
    "j+JOtHMoYVFwI2nwHefXX7/w9s654+mhTF7XrZ+8vTRc3vkSWIPLZcrFYl3HW+65ZnEhtE1Jgx4nWvzvhw97enjol/yc8RVenTRm"
    "bG3GSNB4wlxfi3Bf5+zQYvgTtcB4i2ecodRTpScG6S0/v72noYr29kJVAUB6Ag/FUQIeW42EwnaacVR/Va9nDwi+ZMD+uCKvaqM0"
    "ay1x3xDc7fKzgVoU1Ea4rX4ksuzVR8zqc/Qf0dQ3HmxNv0kraXxZv7FM21eBpsEzaVzcBjvAfR5Fyddff6G+mrvDvmPIRuxPaXfS"
    "qor7cyTzFHZIaZH2SIYYlUUPlF6mLtXT7/wGh9rZsEFvsIuZ9LSu8ZVo9GAJuRbLCH1M7U0WGIFXqf7Dh7cYn/psQTFosUBXrxc0"
    "xK0M5IcXGXd84ZPeer0wGhCJI6qbjT3UDaeVKKHwstOKWe6oViDhgaoLYrkH6Bx++Rbm182bd3wrws/szuHDh2ihxl5n9ywcF7wO"
    "GR0ZyCA0eMMfefTiT16wWPODcNHQ7x85osMFD39rhfUPHzAi6cG8IU+7ALA5ADpz50noAVRzPhiWh+n0vmt6wFnPHtq9MDClpvoe"
    "cgBgTxkf+oSb+Uj8DJcwixdMJ8elKjDWdLGnhOmk0OyLmKSx1FCypnh7z0tG2ZIC8k0F42xBfhdYXoxifS9XiN0VYk7L40EAsu7+"
    "5fis1zfcBgzyiK0O3sSd46qf1+0A8sBryg8f7gT1hjHwAiXM0sqAQr+Qxgdf7C2VsAgkQW9ZJzQY6+ZpJ3LQdg4SxbZGcGwPTZcE"
    "NVi6dVPUIDOMN81ZugDzfE5Of2RhGK1o6rPHBC+dNfMnyydkwXTTptiIIeiGAI8dsa7Lm+fnsLtDsdoABUWSBsRSLo8fPlDyoPMR"
    "rfxkISEffPgA46qabmSg10faCPyyCHgHgPc3AC/g0OCHFfYLGttH7eHXXyOkGfCkmFMK4bwEvTeoqWoDBA7NgKgYUooxToUBcFUg"
    "7gTlpNeLG4EI3mfxp6l8Wsknnx3ZjxcH5zRgJ+zAdfqhMtSd6d5sQS9s1ta7xYGIyXvwbRqx1zrCU35Y0fA0QXhHucudo4D4b3CZ"
    "sgauAVsrEMrP2QXuT1TZeYQ62s7iXc0eWSydxm2GOjxm1dRgqcyzDVYyYedQ5x7Ph7J7Y4aBzEUea4Ii6x31u/jCnGuUfHpYWFTc"
    "bY+chtPsLPFwB6+vf2J65aOuLXvwnN1Mj2SC6Gq1LlrKnbmSRyaKDt7emI11qWq+h9UqpV4LnyMmzpm++uicJjVocFKatB5xBQvt"
    "E01a04017b3ySfQ8CgL0SztCnXzcZdMrfb0SmoZ0kEQnJ1PyCGD85LSwZocqQPzR4rY25NkhZUoK6xwhrOnRC04FPEKqWAcfTkMR"
    "rBCJES9DENaML0b0nIZQ84qzM/DSyNIrnTcwz/nMyT/g5vyO5ClaS6hc1KAui/XGhDu72wWZpbs7nXrDaUkZ9tVUIj858sUoqZkK"
    "30f63VCY0bhWWB8VFQ/6wDBuUJSZQ6UXoa0VFuGw6EV4DIHCQvx7tpiXzyk+iREyVCYHT1JRGlPDkF35moX3WWlBAbSpAoX9yPyC"
    "/Qiq/jkDB0ttvEtz/GLOcbbOrhaGAZYz38hzM8NVwH5NufKc2JQry5QLsrHPBfgyc26TyKAUKpAexDmUzh54aoOd6JZNoGzODHfT"
    "B8OcWQ6IZ64zRzqZ7ykO8IxyeC554zm+C+KACk7chUiER9p7FuaBrYUaL6G52GcTFxFH3YVlRAZzsful7cmyhoYFjtT8Gv+5Y8jA"
    "6pF45NWbcsqms5nvF9WdATa3QGmZ07HIUIaaKT9PU4Ew0y1YK1kwAZ6NL9W5TGKtZmkPaPQpneLVIjQ61Wa0s2wp8gugZNl0WM3Y"
    "YTlTHBX0SKlQ9MvnNzuSkzUbTJiOZ2kSlQisacruWizlclbETGYhVlXLfUGmfcmC8vkGRmzgviotMQ1/312+2TuPV8sAFsEGPdCv"
    "ydc+vNYNOw5T0aZetMeK5nchprItvWyXleUoMBXo6gVaCpx3ikv19FJNFcSSYn29mEOLgUA9CRdCmpYkodFBI55JcWsn7KmcsgJk"
    "DC5NGeB8A4PDWKVS9FZnoMVtpvlbOscd+m7eD5ilP/G5YBYV7Xg0TpXd1QgWtbZCugmMU9jW1glnnOaNjcov5Z7TbvQ6ZsYjEdHK"
    "IoLzLg2ARkcDId3T8n3Ou6msva3V3s7U3szV3SyomTcJlR+nm6gyqpz5+s7MbnQyjQtsaGPQw0OOWTjnO0fRfdEB2XUfAYh5PTwN"
    "+btafZcfoqjVNbP1NZURUQv3e/nCvWxhMZyI8CzxpgUNpL628DQY413oKy9PzVF3mj4H2TVWzgliql6Vq6k6392WAUKTK+oiobjB"
    "kyUh80aHlWYv7Y2NKZkHHdZQOA+ikm69ORNt4GPFFjCrqB8vUYvrj5Z46iqa4G8VW+G5RUM+vi2Lm1qCyMjbwceKjWBW0YIgjM1U"
    "gCUy7Hwz0pSydeQw94AJyIulDCfACy1CD33eAVto0nO2GfAefJgBUF18gOk26uMDTJ0RGtPQNYUs3ak/PO/Yw9HfiRf4QWdkAdXC"
    "m+8ELoG3Jn1ze0HLhwZa9K1LSG/cG1lt+tZq+63BYGR16Jtjjwd9Z2R16ZvdGXS78K3H3tq9fgfK9dlbtxO0uyNrwN/apDWGNwqL"
    "3Wx6zSbli0CfHMDABgDbEkAv8EhPADgeB70UwH6XAPoEgG3XJ31bAAg1dzpEAOh03VbbFQA6nb7d8gWATrfbabUFgE6702r6EsBO"
    "kzhduuubEQFfLyAIEYMP0Ol5YwGfPwgGA1/ANyZBs9sW8Lkt0m11BHz9tudBzRy+bsdt2b6Ar+33PDsQ8LWCbhP18xl8LQDWaQv4"
    "HLdJ7M4IQ8iL8Q2g0aApwANQm6QpwAuI53quAC/w3I7bEeAF/Z7TcwR4JGjDfwI832t2m10B3njgeI4nwGO2YQK8XuD4jkRfu2O7"
    "tot7IjpvBYRB0ENdLA5hQHy/k0Lo99wUQn/s9iQCg/Gg2fIEhMGg10oRSFwYU09A6DXbjp1CCGOfIrDnNX36xiAEZNo9gNCl+k8S"
    "wDEqRQsUBi1PUmDgk25fQaEP8yIFcBw02xLAzoDYY4nCQa9npygEKrMHEsAmlCcSwH6rg6MvUOi4dgsAPCNTdBwjB9kjfQXCgddK"
    "URjYCoQ+gfkoIXSB6iQNEnfcsvsCQs/tu3ZbQOg63aYtJ3G/0/YVCJ1WoKCwCe3iHEmIO1XnsCvg87xgHDgCvsEg6JK2gK9DiOvL"
    "IW76fnscSCbTHvddOcS2P2j3+5LJBL1ul8g57HRIZyDncKtNcLbzOdyG+YBX396ZO0+ZIAkCCV8QuAGRTLATtAJPMsEe6QcDCV/T"
    "bxEi4LO7464vJ4ndh5nQlPCRXntgS/iAF/U6Ej5ggt2WhK/fasFUg/X/zVmKvkEKHrFhRkvwxi7pBpLF9HyfAst5dH/sB30JHkwK"
    "MpDgNYHl9CR4re7AdSSP7nUGfQme7bVdRK0Arxm0B7j9xFtRjr4g6Kbw+WOioG8MkxbfGHyDltcJ5ATp2oBcV8DXGkPVcnibnW4L"
    "Jx1n0X6b+H2JPtK23UCij7Tcvhxep9fsdNpUqvHDk0hAiFxQwSDp4RuD0Ov5zRRCtzNupxjsO30vxWC31e0GcpVrwzqGayVn0q1W"
    "H3kpZ9K9lu22JJN2mgRXRw4hccbtMUD4NoymIPbzMUYySyH0ySDFoe/73RRCrz1WcOj2+uMUh/1xx0tx2PNaLpHLSNdv9n3JZDrj"
    "pjOW63Dbc/xBR0AIixws0yg9r5aod8AhdAFGCWHQgokgcUgGPv3GIPT7gEMiIPTsPsUog9DtdzpBT0A4aLVaRC7EPQLLtJzEXYDQ"
    "7QsIO33H6/cEhK2x3eviKAcrbxKjMjwDESQFBURXBTHo+HaKxMB2x+kwk35vEEhhBhgLSBKSD9rNrt+SfLDpeK5ci/tdZ9CXhNiz"
    "HbcnkdgG7tlGPrPAsEYSvmaQ8mmQZIKUT4+BCfUlfAO3n/LBoN1r4mBxPu21+wM5kf1xs9eTE3lMnH5HyjID3+nhesTg67ecflvy"
    "Gair10QULlFHX650jiIsBAQYkyIs+IgHsY64bcSDWOl6Tl+uI0G7FaSyFnFg8vYV+OiizeGDdaMl+XS/77Racojbnt1xkNHEGNBL"
    "ANgHKvQkgA5Q5EDSIEyyQAqD3tjvEEcAOGi7wF7kPEZLerkUt3udTiqtAvMF7pxymuagJaUZOwDuki4kTbvr9Ki06kpOPQD4UlGh"
    "BeQoEUiA5yNH43PE8Tv+WMLnuS1XLnTdca+JoiuHbwzwSQJs9QA+yalhtAYUZXzZc/pNiUC7ZfcclKbfh3MvncNuuhADdO1Aylow"
    "2G0UZDl8bfjpSy7jwI/kMigZ9lwBX6cJP5JTt7DTXQFfs9dkGGPwATt1Uml/AD/IB+dkBZuqqRnEDv4oKOwgy1VAVORp/JEgtvBH"
    "A1GuxW0bfySIXSbMchBp3ySILhdY4wQ3WwqAAw3AtgSwBwBKYcYHxuFLGoRFqjmQwkIP5OuuJwHswZ6DSADbbTudJM0BwJ5uSDxn"
    "oADoAYAD3CoKLUKzIg+GIDQdZDP1DHZyTaNvms5C9JPqpqrRQfU71/IC+JA7XsRTIXbgpR7VsDAvD1YJNZeg9cjjGezNOd+Zwh59"
    "zdErk/BQhSNZpjVpWktLa9G0tpbWpmkdW28C07paWpem9bS0Hk3ra2l9mjbQ0gYsTevGgPbDsOkXqOVnEeJVnkewM4b8WTHyZ/hP"
    "PSkoPywXNXf1hlobDstFvp5erMkPpvCq5D7elMgT6Z+VY8b0utxWLoRMZ35qYXGIqJZu9YyHhqnallpB39B8V5w6bj5CzU8NW04M"
    "SuRiHJWgVOmcsHMzoro23cZ7HMPRkFFnZouriJzujKlsx3SMWaBEs2X5+1WuUYzltXuA6tdP+XtEU9m2XrajXNzot4pZ3mhSqcke"
    "PLbTg8fWxoPHXv4yKKtlY0aZVowzlLzKTfWyhco32e51c+eqwTRymfnW1q2mRe8X3JoVcDY2IFoNtzZdCW4CgTsb2lLpCBc/UUSt"
    "OuUUqDD7dxv+s2raIyrRotsjmzk+cvpWDf81W/CxYXfqFW/TqugRZpRXbHZNU7PF/Q3VXqELtVDWVfIyvT8lf41f2QkNl2xeuURc"
    "0j2r+aLFqCYzgeK0iqq6MWmBEoUYTT1S04ShX5jCXpEKTNpCqd5LFhCVvqS+7JbMbNvJsL4sijMui3asdr3SPbGmU1NIZnmtbmWE"
    "tXW8RO148yzKqeOWyRnbLfZbqGyYJ8PG5dIsIBgJPK+ArRH42sKQn0Xbj1Zc2HfNvVu7bun+3rp1BR4Vatw4pg4DziuzsrWFfgou"
    "xJ1oXelN+86sqppCTel98nY8yKApr2f4lFxls7KOuRhTRziXocTpQkatxM8vbWEs4FN4KT9G02lmlf6Hsx4BziNFtSTdCl3pYVwr"
    "esCM+1dhn6nshN4hu/APLUwEx6jx/xtOHQUpFKIw237TmGU3ZnyJHHVtLaIFImE7HR9BY38yXDBHBeWYeDfV7beaWUw00V9ps4Md"
    "7RTioo+ORTHjfveqIkNd2S51nPGkkAEwPOcn/kFAD54zQOOhO9+C4/lxg5070EO5fD6+RNGMTKWSHdXlczaVnFxns2XO2VJy8g1z"
    "25yzreTkPKljF/RH7RDN2TXn7Co5+RlCz5yzp+TkY9o35+wrOfkqPjDnHCg5OXkNzCM0UIZIKCnJLUOxllJ6AgmlKdXtz8J3e+G8"
    "FgPRZM4kLTUSe63f/ke9vkHsEaUZXWxXf6/7j3q99NiUYZwSd7PTscQ/WPfqJYuYKN0vK41aC++SUgnIdDSzSVnZoNtr0bV+68WW"
    "tvRkQ9EChcJUiEBxeU4ecgFljp7dpkzeuO/OQvQvGc4nZIluhFRJRs2oHOyjuurdInXVAo1gKHIoi6QcvUQfWd2AawL4NobLTPTf"
    "ycq0oqYzM/hJ+Te6gZ4x2x9dus7loQKtEQ5jzoyBDZMTjTmFsHhF7RhMsnu2HzRPsRhfkl1u0mMCDIZ65Ko0AlDiTRFNl9iKUAol"
    "vm7V20x3oIJoL8PsEME9nE/Pfsrb3yi4UY0eZ9phjBkGyLQZDCWTCRLTtY1afHpSARDItBkQJZMBEG5tZKAw4K6o+uCGMfGPpIDV"
    "QsmwSHpqSgFLOZ1Vpat2XRzfdswZmvVLMCYqm2loFOSfEPXSdScbzYpq83nvBSKH6djBmJF9yjDZomsWgzVYaYPGnJkWN6n+65y4"
    "MJd+slKYTRn9ont2/SLxEiwP/iCLr437oTJod9tLGYb9T2KhZiCc6oBmKWoXe49yInojL+LwsVWJeN5I/QJ8bG4imhKoysoUglVW"
    "KA+XV6aLIU1dikjCmLeIEIyZNwy/ETk5RrK7PVHp6LOcXbVYJQpgWXtquU1UsAnC8nIlIJYXNMFYRhGqedVmmtByb6YKLXs5XRSj"
    "K0sbu5tolZIGz9rVClYiDp63p5XcRB6b4dxQsgzQDUWNkJYRiWa7tplK9OybyUTPX04nZXjLUgqGRio5V6IK41Kxjb1VoRSetasV"
    "rEQpPG9PK7mJUjbDuaFkGaAbihohLaMUnrMqpejZN1OKnr+cUsrwlqWU3awxS6kko2hUiT4wYy8ts4kyyqAqK1MIVlmhPFxldJAa"
    "om4mAiXvZgpQMpcPvxk52YG/mJFspe3KwCgkV9uu9I1y+cbtSjGsG0uWAbupsBna7SyJN25VTGU2blRMhaptU0yozBKR+eBI96yz"
    "Qn+waOkqjyvK15iqlx5sK65fSwzYtcSGtajyvYepCX6zUrxoKXrYSlWZi8TMeYJ2gDCprLebux+xG3a7vqXOiqESp1u/8F3pFnpr"
    "cs9TYQdTSBap5LwDSbDCxQRRVPkmYkg3I7KSYiwVbgTEYcDG7X0hcsSGcwfUYNFixJgr3oQWsWfnFZQQjmnPLDZCVTY1hRhR5Ocd"
    "kMJLF+OlsPpNqFG2Jmk1xQgq2RSIXUAVib6Y2abC4y6clpUuYbRF1W/ksqlcnlZTjKYSiTgVgTcKtYVYSi0HtkYRFi3Gj7niTcgR"
    "kiqvoBgtRklRFQ0nO5uQ7KQ12aso5fWMinHbyTJrtLgI51e2j81tz78NKg9roSnxpxK9LleGusxB/QuKPn8FOeavJJj89WSMv4q4"
    "8Pms/5/VQr71ijylnka8Mu2JItWKIv0FoQt1y+zT36idt1mFu8ibaKrqjFo0LbMWTV01kixQhaY23/6ZqlqoGQJJZ5aey40V9eQk"
    "TNDvjWp0bggVwpSI4tWYZ69ky2GOOlJs7La2ftspRos0SuM9E7bw6BfJQz24x7rFlGPAjsxb4E9WaLNV9gL7WTpSNh9GVeIJZlWT"
    "En2odMY9uY6icR1F4zqKxnUUDbOG5qfX8v0jFHozlufZmyCTLnjRbVFhvALDsGuK4H/peCXWLBqHU4LBhDFQdcbDw3UMkyscw0S3"
    "NlFzapYmhb0vtDKRFsZrs9+Ggm5m5+slxVehcUb16HFFM3ltPa3mVZ9a+Z9ucGZvVZLLvAnx3mQIPud+nuV5WFGd/lOJen+YwJWV"
    "mTgKS20DNBxWMBHg+e9vdu7Ec94VWK8I9Y4CYqmYdUU3ULtLMGKO6RMsF7yjKD6FHjEk5/nAJGXz0dxoqaHS08bM24ju2O1Yi8zB"
    "uhrrBpXPCjiVQ/36V/K7t6OVpHXpAS5M5q+7R9KBQZ/RcDinJXE/cpFktoQPXejPYOwf5eq5CnOwfEOxbU93dJ6SigFr6/5uYYSX"
    "5G1ITjdN888+VJcMmJwTz7kDkJTDF+wGRD71c4WZmhnuqp4qBuZpN3HnvnrMmVIRdvHR1ifEm8LUVjtUlBO/n/r7NHirY85Ea2bh"
    "bWcg8Yh0sUpMLdkXOPQtW8C2PvoxuPmTnlVpfDHlU1O4zSo8o8cdeZRkkPtxcLu2Hm/rVUDS6GYQOE9nHsHSc24R+6u3XVd2OPtu"
    "FvteLo1vxp2YbYqXbXCTBRh9jiHjs4HIcqcK1BdPOuL6VQIXz2YiKl3RZc5lOeNaW+/NrCXHHDcfweh8NHcqm8224YwmU5sc681s"
    "/oQ7wUY3RCPLXS6j00M+vGmsNIn29FAgW2Hm4MYxCD+ZU66CLqbT2uSmAG/kCtve5cunpZ/bl700XTAaYo4+FEcUkkS2EaSyh3pK"
    "fcbzvex3HpqYeUfJH+pl/WQYztcMV1rZUtzw3ngsl81rPJwyg2G+wS5oPH/Mls1YeNSWzfiRHL+U9thwJFfebVog0/cqrmI+lU8W"
    "5r5weG48ZTY4N1Rr5Z9VwE30pGXbhGUtc0VEa2V0XGteZ6rJkwUOJk0NMozqsZtNo6XnrzJghhIcweOCGa6X2DTH9dypvPfj4mD0"
    "txr8Nw0bi313lUReNFtMSUL22dGvRb/64Vv47LmxB2I+O2Hm3/c5Wq20FmRw4+idVgH9MFtNk1ArrXwsSjfVxsBJloTszyOfGGDw"
    "3QR+xlOyH4RTWGUxSwy8PBS51Dzay36Ceiy1b2vJUubElmRO+ZLLycBCPO/jBNTB4jCHZEn80iw06V1Smgc/jt1lyfcTt7QCuj2m"
    "OdjOrTxPvpZkouFMVEKmU+V7iinDd0jR0Y4pFJn4a2LAvSijDACmfJssv00mtXNagNYtl+xhDY3bbtAv67+NrIc7HJoUb96NDCV3"
    "TJfujbcVhSRuthOGuCcmm+ts2XlPpsxtPD0XNeyiG8oRqaarJLeba9GnOzCeVfqVd1skshlUVow3lh8DXZp6ng5Q0Q1ktooC0V1D"
    "86c4Idt31BhB5juDiww3tLeazY9THT3N1XIFt8lLjJz5KQilIO7AJdJAPozAlRnhZBkutg0zI3yY4lrG53O1aXXpXCUd0E32uI5u"
    "jzsQHptKtq9cmqpAqmxbXpW1XZAHfQTWzObqfX64sMtkFQcTf6YFC5WRnkXhPClU1xaYe04QD6kCrqx/ST88ymno0plZbMgULZNH"
    "m44OiyI9mA4YFWWQaeRibx9ljxcpvz2OTk6m5PYqSSKTQn0VzvqwsFBxdJaq3l21Noo0AbJnw9oBQcf+x9W9f2LbjuF5OEePCQ9U"
    "OYGfQR0JH/x/Ah03/uGZ9K7/cU6NtzwV3nTIvPnUuPI5cMokVvQypNLJQ7onfbydjqBa9Fon8PJ1Arc+Q7o8JUJ6dX0SzrH142hR"
    "WRorWEqV2m5HsBLMLl6hF0MXcmco+xiLCBL4PKGvyp58f3/xjqbtK6yhlo1JpHsu6dQtLTBRq16XW/m19SJzU3nHEC1S70N2GDRB"
    "Y6t9erk8U+mWvbLQk4VZDX51OYCWokzBkAGU6pLi5aGMogt/tkBZ2ZTabpg2TqjtugDT/afdNHmYfssVvV7bZSHd/aBsy04pV6x2"
    "TcSRSk0QM7HGdOPDKtunQrsHRf+ymdO4bKmBcy+qApzJbPLOXZz7c1f+sj4rr91X2gs217aqpuzPxa0nMBcmW244L3A8ZwhAuKWJ"
    "7PYznHX0F+Iu/9z9PGHxPitxW7ZHKeHuvnv2I9U9hR0+rKBpCD+2EFqnhLy5657lQ0oaYC/TYNnEnd2E7HgcUmpSQl1pHP0xR9KF"
    "avIaUMUH2MV63aYjF9P4XMl14NKCU86QpZUS74wxvbzGp1VVj/IMuElpE2eU3VyghTE9Chy7hqDSXJ6uttlNwhl5FnpvyMUq0i/P"
    "GHAPVM8J1sfWU7OSyHcrRPnY2jfmwOgs5EG5UiVTAa1wOMYzlitUagqlRQdnWk3F0jzLls6rnLJ3JmfR2Vg1Hx9d2zaqYioKkXoz"
    "26YbNaovrXK9z2vre/M5Rdmh4La7ez2S5SRahu8hO8b2FKzE4SrmSn+FjU4ezSns0MMk9NSKRLncvDdWJfdWUNfvRuqXxz619BeP"
    "CKpiy5wNoztlGqvgC0doXVaUm3INsDuJ1hVe+ADb3/1xvOby2IeRY1wRhlGYdW39ArhPomhKV9pPapqDKxpt99HuURfL/VL9mVwz"
    "WEX3LbKXh7t6XbiEi45LvFLYZk35BMeFMEV+/oNM1yocCQrDsfzDlhYC5IRApy5b6ekCu8aKOMqeVJfdFuSWenFTX3iIynVQrux+"
    "ceOOAZUqLkefw7hm4ez49YpZz2xD9qYzfI1kTEKrGmFezDWtY6s5jF+F+7yMq0GBXnniUe53oiIXUA2/ghDlE5NLPyffi6LhYZ50"
    "M/sGrJmpBeidWiyBMEkcU+kidQsodOjGbhx62TJY11N3lnWYeOn7aWyHZtnkmHFXq/cf5MwwuQ6bRm6iWzjoi21B3jKrk4IiGQMf"
    "7llkQyHhf0SUMk0rGMgYCDFi6WXe3XiWEvduuVNTBrUqTkt+reZt2/aoWjgYqusjak2iBaqppip36MdVN9bG21cpwvM0fota1Iu1"
    "pdVflAuAmW9wMfQuXqcoqORJSNsTO6Jfa+urzJa+cK28oLSyDd+du2+Fql+1/XVO6ijeY2fdD+DdUGaNUzwTaBtkYXYrdeSX5G12"
    "nPBQGTpAndubvlxVFT9A+aO83S/ICJPVbDx3wykwnspyt664mvJzWdnTdIBVQ/KKpJQdhysqgVW6g93ad3PX5K9/23tUdh2aH46c"
    "vxrFxXFuJioukzuFE0uXJnL+g802J9m8glaK/T1VcIr7+SjcfnKXwohqgOuRPjYbBjxbqDrHblfn2F2jQoI574C6iJ9GMdF5i5l5"
    "f/SFpVO6rnxG2t8KSk1LBLqBOaCjjrpCmeVBNcwxe9bp9zI7krLyBucx0uNMcbmMHKMqicgDdLP82oq5zKasVMJPkGkIszTQToWL"
    "2ybw+uXCh/D+drhwvTA5Qw1X4Q8uYklbCVYZzx5SCLRS22p9+IwBSTQVGzWcQ9v+R10ITJ8SS4K2bdnmJaBEro3iYyfjKU+52h0X"
    "A53Z1Dc0pHBRu4WitkEFTmXvZrU3cxiGI8+dsq1mZzuxW/b5juH2qymvv6xkJrwAbXaZOp999E3uH7BhLdu+WZV2pBffS66t5exC"
    "bvNCk7yPau0ZHk6V4Y3ntvRLOtbynkhgcHg+JQF0GV0xjKylKq9RDIpjJdZRmguEn+kK6u7T/adp4VWigRberKZ5mvXiQ2AxLVu2"
    "4hRzOGqYIn2IRaBYINDh2k4aUAUVHBb9fvDzkRXQuebBufCixkmrI/kb6xZD94axbZUKX3o+0+lqnp9WOnalyN1i+biscSjo2YWG"
    "wpXsIb1+M/KSWhGbq7of1xVj6NlHPtBNmN9bsrPigt2OSfgA3sBNvlXBo/OPujnsFM++bZhKWqxZGMyKfu7lau0WRrOiBfi+XYKk"
    "BK2G+VBrw78+WlLAvy26grG51Gh9W+BSid1XCZlq9LxdQw0X17sNPlmJrhrHbweMFvWHo5RFzKuMz/MzMp1Gp1vgUxbYFqG8YDFG"
    "eYZtUMqLcJwqoG2J1MJOcayS5TJabkWmMmBdJaSmgeN2i0tbVOc2uMT83TR43Q5YNPdCzPU0mOhutiGXHz7dbNuxTY/1aKSGXqeh"
    "/zZ12qCvWsFnccdgMFIeNjXvd2SnHg865h6vrehTrd+fU1yAgk2NH8YLqsm1lf7JZj0T9DI4u8KR1K6Dof0BwdCuY5ldpVhmsDZM"
    "wkWVkDy7B43YNigCwDTbTlMeWL9b3U95DNOBLCurfWePN63MDt2sp/T3gP5nOq1UFzrY+PFlzjYEU7X7GHAVPjj8nymTgzdCu+26"
    "NdiaOaUF2YdolaDvGjUjTyrVyqebcJbvUHWgzmmVrtje2YNl6OcDG7ALUHXRkNAkQrcoPbSGQT11E2+y6Z6hRBF1CjQHXCR7il+4"
    "VFVdBTac8m7BrnL2B7Nw/pNuV35ZEfvW1mqn49Gxftfc3DqIiLAzeVYutOmUoWkV7qI4sFXAaDOPuwLW+iU3Q3fKZHHT9mOjkXjX"
    "ZFuO3tUk3WTDGdMj++39IKAC5Ow6HO+1BFoU0+tanrxKsXGzEc9NBnbFKESfV9eT/XqyX8fevuYv17G3S2X0arI+MNTZDpL8lVWn"
    "g3m6yirt5yxTqa+TIlXrrAsLeuG6wUilxEfBHBDvTqkj/Kzk21L0V0rNZfL2GQiH0Sa3ilIbwHLyKRbR8ceNxvsp5MPqvHfH07Vt"
    "Q77nLeLpR5as2ZZfx4H/DOLA7+aH3+DE/iJx2neNFC9o7AH3/VU05tQ32OahZtmMtn/5bHofzSPCcuoxmAyYUCqUcesxwDSsGW9S"
    "zm8iSqb1fpS4Swy7kDJ0ln4PEZGN5/lERNbbQEQwgV/Prpblu2ZNIs7hDpch5OHazRcOcpc6pDHXW2Y7vt2V5tiNyaOdnLsUR6W7"
    "DtJ3HaTvEwfpkz5WNOfLV4JdVAqkqU9gGXLwwozkE0fq+4iR97aNAvgXDc3IglRKK7m82nEmPsiFI6xspQpzZRXK386uo+9+5Oi7"
    "l7hC/3kW3asX5/avuVTsGAH3aqwtMHhnV3mPVLhtud6oXG9U/qrRxC+4FH/izU0lecQQIF2zx/rcpO9r8ftTid/jjB7rDh4Xt1lL"
    "iv0uG50xFgXRlDqVWhhNkV5TvbCl5opHqWli/jpLv7RVw1ae6C59UxcCRtcCtCLNCBIriLXbuXXGjYlweyNQID3ffMxQkmVUIwDM"
    "uQtSepdBUd7DAler9YdF7sdwloezxZR64DP6lry2H70U+1Gd2kq1T2k1TPXUrDBtd+p1jfp26A/GudcpZItKykclX0Alssplri1u"
    "L93idgsiZPVclAo396kSHRZXs2F8DEVKabG41LWx8scwVt6CIHlFF6XIKv2qRJNlFW0aKVOhUrosK3dt8H1hg+8tyBBruSgNlvel"
    "EvWZqygdi1z2Uoozl/hrWsZvQR7lnSgni2r9qUQeBVY77YpDYCxWSi7lJf96rgV2IBljPM2KJFPana0oJoPJndBfmVpM5QDQd9ue"
    "h6gO9mckIcu4klqvJXbRYg/NDkF1bQSa+ATARn1LUwGDP1+azhy8Cg2pB+qRSqrg9ECBnJY6znl2uoiD/bV1dG0nc20nc20nc20n"
    "c20ncxl2MsWx2jcGu/4TBUK7Nlj4ixss5KJ1bTAtqGikcG2BkLNAqOR1B6+KiLt8VMlf9NYWCHfyPtKUa0D9ylCJKsX1VXbQvCgV"
    "8ws0LrZRRCgOD38JaikX0KapqMuyo+qNUUDIFjRfGa+tU91qUXFzRHf20TTOxSM7TovIsBA7aD7NI59celBE41qRhrm/PIXXLGNP"
    "29giDqMy7XggB+7eG0MLokT/zJShxq+6a842cX+2s0It25te0RhMQE7HFHGmWCqXQFpbkctWgXbjz9NhuaajoWqFQPIcJgdeXXiX"
    "oqYldDaababZcE9yIH70lQrtqDOTa1QZRjyGumta95QZpS15lYOlVg7SnmUllxDcrdwD1mUxzAtrdW1mmpm9lxz4z25uXFokTW+1"
    "xGF9BjLdc7KIlsmlhtQsbPa31WxxHGGrj5jnrpn7Tnc2BxPp8GqZl3ysmLPl3Ks4CO1aWckf5oM3tTLBm7Qg95koyZvJxBD0viR0"
    "rSkaVGn+tfXG6NltK+61cOd4Dn+pOr6qsuTmoN4iEs+WzD0Il7ExyGcSLW5XpM2pGxfECcUILrer+qm8GqZKZkOIi+8E/1I2SRgU"
    "V1Eqz5jffFTDmlswmemFWrX7tC3ltIZQXq0W6GrDCeoiWmySxnNZK52hZnIXHqKKfPnztmyOlN5zJ60iSyoiSJadsZJOYKk6AfZw"
    "fkrcN2XqKp1UjYMrAMwIdGFWVMadjQEAXoq98HLQZjQ/KVcZ7KjKc0JzgNLQcUYL/EIbTCDO37Y/k3hilkQuj4Q20cSWJLaRPGTI"
    "TYcGfHKXy+hUOFGWqu6GVb+YJAFLTzfIaxea9ClUlZx0cVbr5aLxMX0Sg9GjMSAcykfQs2d6pLxD2BJWmC407/FpZNBb7ih6y1ru"
    "CdB/xenBStyPVmalv46m9Cc1au7LrkjThWbWdMEUO7Ho5p86u8ls8LKxD3me/LW9yKifW30qZYI/7Eo/O/k5CkvjR2o4NObUkcjz"
    "388DUlDzXYH1j+t3rfQi/3OKdlLpjrw4Krbmi9ppZKegyVBJcig+Ync2MTeVZjZm3srr3Syv03SiKzMB7I+yW7rtQ8Be1ePgXMC8"
    "yqdX5riwBV+hpcfGRVXh9zxgA/1pOHVFwViNV0h5//M/yN79yrr7DMkpO/PKn9GApOyBLMiCphYe+MBgnYRzhbbFrGhuf3whAn9U"
    "cizKYsEGrs9jVbRtdnb9frfACq5UUhzkY7AWxmu5epx6J91yQNvta3XHa3XHa3XHa3XHa3XHa3XHa3XHa3XHS1F3vNZw/Hgajlso"
    "Ll4Jf8w/FhknlSy9u4k90NjDrSIcXtn9GfDUaFXB9s/k4HydZ6bS94y4X+wW31YXZs1eq8jtohuHPjFVscXFdNENczCNQBSZn9yu"
    "uN/m2Y+EYSKN7thEs0Q8Hdiza/jzDTM7BvhOGHswgU4/Zb0b2qkbH0WHZss777zDnmL92vyhCofslseWwSQS9nDWkpVPaxX6b63e"
    "VgB+lFvinS7Wi7yB5S6Y8cIM731LnZFiFqHkZdBcUPWyC3SmNw35Jg94O+tcV7osr6SGsO0QbO1fcGs1661UuXHQD+fTM6kyxQfi"
    "NEwmbEpw1V66asnPf6z6AyM9bcami6yctbIn/GD8rzJrb7s+ChIb0JJeEIgcaZTWIlyltWkMvJm1winhw+NPo8TMMHG0GkvOdHsa"
    "eW+UZdbSV12Labg84aewjpKW1W2n7U7dRRyOFW+Lhm/H0eKJPNUV7Sjfb5uRK2HP8dYStaVrLnvVuewfyi7dcL6b8JsKjLsUDucg"
    "nW8qafIckd6GbBcfO/WgUS6orq0XW7u8rORwpcAnTxd98rjzcEaH6HbJ/Zt+3dauF1bZZjdxP+10TQPJwA0vU7uG0SHGjTfHtcvp"
    "1YhLKnGsR9WHJKuy85dHVIu+CsTFdgW59YPvwAwNlVSisgEhXXRV6Nmb6szFbnS4Kxf8xy9aa/z/ht2HYcYPDv9nyuS065uJ0DCX"
    "1lfX7eyDC2tqr63vdzgNoQgU+imiQJOJSW4YEz/d7rb4iOw3DUPSxGGjTEYymuyQYQYs3zFnaNI5/PunMk/YhkVwvb5ql8hiMjMu"
    "QM2frMKr7s/7rn9tfbcTy1V9WVfgTQaxJKvwIRdJurY5cqnkg0BZcZyQRc58TPdXhFnyVh+f+TBlIzpBH4+Z0UqJek2pBk1+L1PB"
    "2gXbfbpCDeYqc9sw5rvzAF7ZBY1By1HCKS2z/XOA8bUKtn8Gj+zVl8lulWWyWed4p2elsUb8feEzQLce0sjkwkes6hzS7SbW1i+f"
    "gHUw05vH4fxNZdn2s5jDtFe6MvaF5zCr9XqGfvIZurZ+3m3j4o7ZVbhu08ilrEsLOijM16rbLmtf82RiEIAMsFchBYOe1Bb0lVPZ"
    "3sUPQDnJpRqQmmVmzhpCk1/2OQoyfn2uqM4u0IZ+Y3x56FtL4gGGJDeUqf3lcLTvZKVrg7Lvr1d7dkFD15Przz+5GKludkCwQYoG"
    "arlEqUxIgSVW5H8856Enp7UiFzJm5xrlCNmKCDO6dleFVsRX5ehLiCJofljrSHkjd14qJBM9r8mxsgGLGTf1NvqI38yo7Y1c+odd"
    "uTRz7Xu53Pjqcj0K4bMLcoBPMW2uFH2ura8keW26m+3hkmHQ4ejs7mfIeMiaMQB5N827ZxKXoJwGiq+tBJE4hSEeRI7C0BEGz+Ci"
    "DAsNIV9bwgP9RaMPbOt2f3MQIi1Szg4Rhgqj0PRUS2EBTWk0rvP4Tdl44NdtwMD8HAh8FCCUxsE5j+jtUwkUPMM2gPAiHBb+JsDx"
    "8a04+okSsGPr0CYFYTF6qYG4AGKL8AYG//olRGm6UVpbZLKVlVNVG6ASMxu5wvYzrlyMZim1InuWbaxVLslD1WIZzRZZ01UcsdnM"
    "nfvPSbyIQNhDx1VMYqd3STRo4eTalOzalOzalOzalOzalOwSTMlgAzC5Um4Aq0V13mZnmLUS2ym09XVU9uuo7H+UnzlDCPOMt7nP"
    "M5T51pHM19YSmBV5S9XTZuH8obijYyhJ4zcNWaY7OQdb9ICYypEiAlRhVrsm7qdpBj3WVNbXqK6Opx62N3P3EhfhrMWqeeKkQCqp"
    "lynJ0IPUo49ygymwWdGHtKKWAyx2knGetaUT5wvEX7fG05X01/ZZuMWRFCi2SHRg8GdL13IZjQIWFT6jKbSasWOnEnUfzpd8krjh"
    "tDSnEh/9Mw32/pePv85GuST2YM8QL/JPHrT9OjL6J6OOzzSc+nW08jQY90enkc84xPlfOXb4R6eLzyzg+GcU2/ujD91nGBD8M4mx"
    "vXHo/nqBuTEo1XLmTi/9XFRTjtAQb9Kr2OxrvBx1ZfbkeWSZdqxZvKwtd2IIwbTdXj0XqlLbK+52a+dvcrFcXqzKBdOO11t/OsfL"
    "21yxqPe7216V6MErt1r8+Kw2OFCvXrgSIzIX3ci4C8AtY1paAe6lXtW7qrDm8lVKd3FddTEyeVKv3rWNV1bigGubCXmV8WWM65T1"
    "BFTV8QoDQD2zlbb8phPbpnJiW5gJjafjWQl0bMKWfK44u8xegaPcca/ZT3sGRy16Rqur332Obu9NwaSUiWVQ/i/8bJqYpgwPy6vZ"
    "cXXbcRmBmkhaAIYy3mzK3zLK6yZxQS29QQRQKuza1fl+W4elaxetNxcM2KG4Li+69nFyVz4bZ2F7d9QxuPKOTSphrYS7bucTRSv6"
    "cOumB4UbpZwQXtDTOwVFc4X6pjWklChKY4/gkcDkj4k0UKTaYQ4oJ5cJXCcEwGkkSkew+zQQdZabF+55sqFfi5bTTZGcNPSpXCXt"
    "a0o926s/qnF1p1uM2UZ7HSXULb1g1kyqdwjkXajlXjWM1CeJWrspXm31SLVXxXYno/6Kg7GDDeVO0XqNQbcLFxh5J7vLQD+s5jbo"
    "0vr8sCwizJX1xhu5OAXVu+Ymd58bTqnTGc21Ced7KIPHMFZ/q8F/jcV+siRkH6OXwDNnfvS1dk5z4H/7+4t3NG1fYUS1cpdbnbql"
    "BcJp1es3aIXrv40oHT026EQVMsgd3W1X0CtfW6tr/fBr/fBr/fBr/fBr/fDrUCOXF2oE19XiUCPbxiuA/VC4yDkiyscB2yoQA4zV"
    "ZHvL6eKDauNWMX+OJwMBbLsVRZSibw2ynQFB3olFdsPJFXc5YHfItNId3kfbwlyw15roq4NUfb9TukFn+LoqeyI8NZ+uZnPumS7n"
    "w6OCceESKv8jR/yjDuWVGaZx5J/xyVWNwgvoTqNNieYirqQbuMtX4Zi5bP+hLHwbCIgFLKnKOS44wYvYF5sG93nslF3mgYi7cuU4"
    "M+vac4KALiUdS3XzJf3waO6HHrMOOVUuSbwidxhxtEwu6/Akq6devDnPH6JcmSOSrY5FMuc8H0PV/iMdnCzck3COdHIcLSp6bCmg"
    "V6Wu28xdzQWryx3N0Fn1ic9ngA+AXIgUzA6R4jcXc/Wi26E0RTjqxeTgcPwbSs0+CcI5eQYbB7JMzqyZ+UNIYmsiP52Q5PB0Lsrc"
    "JbG3DBcwDrF1UpDn6Gw2jqax9Vp+XyyjJAJeSBoTN1ZyWm8NWRb846P43nw1I0scGOtscrBHrMSa1w++TWrhvEZuLiY05ZzIXMMv"
    "bLzYD8KTlXw/XYaJeH7rTldkOF/Xh+Rl8upgbo0nB7PJ3h7WA/Wi/L731l3W5thA8uHDwfm6/nrS8NzpdA+b/vrrM2xzbiUv56/q"
    "N8Jg72RSTwtFQe1kspfU62+LyyxJsloC9Ov63vnaureoA6ZRoJ8tojmMdDw8dz0PiBb3BUcLy10lEX6ckoQM78D7Wzdxl8PThTWm"
    "YVOO4QEjhazC4V14XIJc7S1Xs/HwEN4Y13uzsDx36Q9v0b/RCnjO8Dd8jj2gO8aBhk8W7JZrHL0bPl2wTdCzBSO1Reihfd39hfAB"
    "QW0fH9FXvJ8ePl4wrC9nfuhOo5Phc5mwiBarxfD9gulbvEto0dsLy4dusGF5yF4wIvXwBX0mvMGf4I3V9wCf3oY4S76HR4yM8jv8"
    "XbqnkPLdwiJ+iIvRLwuLbr6QX/2Mz1OyWuDsGv66YIEhmH3oDwuQbKZTsgzd4Vfi+WxIZnT60CqGCbwEicsKzOFlhtvHJX8QPQ/h"
    "fT6FmTPj+0sXE+hh0zCij6sEcRkPY/FGJ6/H31j8sSl/mzO/riv+GiWLoc+fE/ckHgbiBe3AFjPrzTwaD2czbvU6mVF7ahzBk5k1"
    "IycuRfbrGYuN9Zb9xYDXZ/jI4B3jI0giDJB38LaaJiEniqOZldqL0kruzCzKUKnh9im+nLjz8D3N4E0wfuDxTJwuMAK9N0s59/Du"
    "jEeEO+QPtNI3+BLHpxESKTzD6NP6f4Nndjk4fDJDtyQnIH3E2IGn6Wu8COdzyPFsZuHuPOJEfx9fMQ7I8BE8hQuYQMPHMx7ZHEbO"
    "HT4Xbwyi9zO+GA9viyde1Y/wDqSH7T6ExzfwDZNfzJieBNApPC0I8ZFYhw/wZRqKwt/zVxT2fp8xh81Is+wxHv4yQ19hFA0/08d4"
    "+Cv9S+fDD/h4MvwK/pDlDJA4HZIJNQOkXUjgOSRLwibkHN9mBKlxuITnCDWbQ3xAEYjD44r3+DQEyhxG+B7RWO8xe0xg5nsTdqoy"
    "ZX85YlbsjU1bf2K9DZfJyp0yLEKngglbVn9crOt16x2ubFQopgvVcPR3p+d4ze7IoksWvLfHnV63BxLG/AiYASxYfw/of5hy28X1"
    "TyZwn0Wjv4/bzZbTFwm3TzCPT9rEEUlHEQwKpHrtZt/xtFQqZMGngecETgdbuasVEY2hJRAVjf/ec9sBCvQ8RTQXeO2RtCgb/d0e"
    "d8ctV6bQXP4gaJLWiBkjQtfHnfHYZq/s+5gMgvGIYtyhbQ8GPZ+9N/G97QW9Pntvwbs7GIwRNnxvI2R9L/BpH44hBVtoO30nwGvz"
    "uX+UAw1Tf8p1C1PvZjGLiY90qDHpSWbQEuJis7bd7XXG7PUoChLWNZf0WZJAuW13mu0BBZeVE7jGTHys1apUcfvvfpc0SYe3wU64"
    "MjU8p1EwIBEyusRniY/mVG79O/GDZtDm9VLuhb3temPfZoloYA4kLL+1vV6rh+P55oyB1ex79C3t4IAENCXtX5v0bErKtJAADrKk"
    "vRPV5DvHGsv3DRK1rgU2TdN61mV1Kh1z/T5NM/TL6Q9Qfhy7UyzfHHc6Xkck8N4Rh/SCnkgUHWw22+0BwQ7eEaUFkCwj76Zepd7T"
    "MbGJzJ/vLEtP+9uBGdIWybLLQeAEfVm/7LXv9ZEHsORsxzv9LhkAjt+G0ZTW0m22ba8vEkTHB6SNHWeJouNt0mq5dGR/FKUFwCwj"
    "77hepdZxYgPLsGVruY6z9LTjAxiAjkgWHYdu047z+kXXvK7XwY6z5GzHu4NubzBGO/QTkC1d5COtZhtpm6fwrgOvsoknU0Xf+03H"
    "7zax709kBQJonpX3PlOt3v2e7yE/EE3m+s8/pAjwYezTdIkBYFqIF9GG6KRve7afpmdx0PM6QR/oaAprI45nu0vPaPBVDHwHpOYx"
    "SxJdb3U7TZsO+2NWTgCLmXin1ap0SvdJ0/d4G7nuYmra1x4wrB5LlB21YVqLeuVAO97Yc1hibpjtXquDyyYLZAUrXLdNPWSyBDHI"
    "NulgN1mi6Giv3xqwjh6K0nIVpgm8s3qV+gB3/AC7y1vLdZilp10GasAus2TZ6RbQd1q/7DYBCndEcm5sB90BdBx9GmKMay5nEAJV"
    "KXLGuD32vIEqZzg2LJdumZwRBK7rtjU5o+02W007K2f4g6afSRWoFSvqZjkjaHleLyNntO1W03FVOaMX+GN3rMsZTq81aLpSzhh4"
    "XhurlnKG47Xsjv35yxm9gd/3epqc4dgtv+XpcobrkLbfV+QMx226iJ8qcoY9dlzHy8oZTqvZEzVIGnbcVq/l6nKG3XXgv4ycAevm"
    "oO2Z5Yye7w7oeFKRodf0fFzvUjkDOjjuOJqcMfB8L+ilcoYzaA5aThU5AzvXbGXkDOhbt9XU5QzoWrfd1eQM6JntZOQM6Fiv4xnl"
    "jJ7rdsa+ImcM/HE/XeF575rNVqc7yMoZYxewEGhyhhMwIKvKGTAIfRywrJwB/W8jvWTkjGan1ezk5AzbtQNnnJMzWna71bOL5Iz+"
    "GOafo8gZnu166QrPOw4T1uu6WTkDSLnDOi7ljGYbAG5WlzNgYnaa47ycAfXAVMnJGa1W0+/k5Aw7sH1nnJMz2q3WuFcoZwwGgz52"
    "PJUzgo5r++2snNFpNx3cBmTkjKA/9lCIUeWMptdsNr1t5Iym7TSbtkHOaAaw7zTIGYDcbruZkzOcDsyVdl7O6AyAULqFcoZLBq2x"
    "LeWM8cCHlUuTM5pey8NppMoZHiHdQV+RM2CNGTukmpyBi5jjZOUMmC89Z5yRM5rjVg+nvypn2J5j24OMnNEatPtN3yxnDLruuN9V"
    "5IwgGDdxNdHkjDZIL043K2cEgTfABVWRM2Dh7DTt6nIGSMBdx8nLGVBP0xnn5Iy23Qywy7qc4bRtgp3OyBmdTos0/SI5Y9wcuH0f"
    "bzQeHJCDb0dv3eXe/n60Cve/OieNJaEHfnvfvLy1/+urb04szLI/+hdpJNHj6JQs77gx2avX8Rb0iB1j1yGHwRb7q/MHe6S+hr/J"
    "+h+aLTYUvSMPVF6mMgQ8dYNeMKBPsM3FxQGYSUBahKYBybl+C58GyJXpU2/c7yPNQa+djo9EivJu227TJxgTr9XFJ2CYdpPWAiy1"
    "Axh+xeQsrXnYrcAulDYV+F2f4JPbHdu4AABH7IF0YtNGnZ7fpw203Q6VVrHRlt+mADf9VqvFmm/Dimaz5h3SbOOTTQCA9ujV2jqV"
    "1wXBMprdg1EKSbz30rY6tgXEbIHMbrXgX9vGJNuCeWMBOVl9+DfAfx37VWPmLsSJ/0tiqVfYX53fmTTo+8sEWqvRd/yCr/XRq3rd"
    "OlbuIfbUyxocOe2yliZ4/DGp53QaHuzN63nVzjT1Tlo056WS5soHN1CSldI5W/IHeyN+xziqZ23I69Y9SaKZ/iV6/47wWqPVTPtI"
    "TH1MjH0kmT4SYx8Tcx9Jto9k6z7ehbmk9U1kRh42yvVTVmU1+2l/lQby/c5UaMBBtrgh3YCTTL0m/OQqMHzYCl/W4a4kMcItWbbC"
    "crcItA6nuy2I0SrBk28/zWyYjmsrDvEuTc2E5PBmcqDFwKg5aJjb4jF095xurdmutTEed8Ppshi5WgYRrbtBXcvcmhy8W+yNJ9Z5"
    "TGbuPAm9oaIHwvRF7ruzcHqGcXMmZBkmuN7OiXCaKRMVF34sUrVJeRD9O8apsvXhwvXC5AzT2x3mwpVX0TY7UKRWSlw3IMYt6shE"
    "4UINoKmqHzHkW1ztcHg6SaNgGKoQ7lYkOUbzZ+VTgAoPhWTMv64tqYk1LJ3UWQfBuQxZqlW8rcpE4YUxm1eHnyfSEwiZSN9E1ifa"
    "J1F3gRvRfsZTKZTgODfzHhYVepSdACP2auipCXpUUlrO7tPb0PNU/5n54UxVnbv5yOddRmga7WbUu52mUsvPvIdppYzaL0qrjoFW"
    "dSxSb6tQwmBroqIxZ1SiFDWbj+Qy3M8Tn8iQGSRPFT4Llg6VQAuZv8GgA76zgyoDDejWGgq95kwzlG9FRhhqQ8iCcgUzw5LxBN6W"
    "fgToGDItbeV7l/k0yhJeyuF0TEu6N6iK5rhAagJ1CewiozWaT79v4jGKhj6/ezUxBI7CN5MMUW87+9fymt3USmrY2rzcRmeR706z"
    "TWp8Aea7XdZmygOrNgqt5pSsdPUtbbFv4WKvLfDd1GOeWquqv8Nv2oWpW54zUrru6vxP67fgqjhxDufTM66+1mpeCl/NVtvsUmZr"
    "cJ3epRGHxZJ+rMrBytptZVdrfoiO+ZVTcVrmrvaePTOn00J41Ls7YYfa9ybIKYMI8rNTbczFD57xG3+Gz/JcHHJQb574mR+pw2d5"
    "uI7El4qLZRJL4Tag060g82+U3tNYTF6OaWab5h+KWhb3FAXNpp81p4VZDlZpJTJPe1Or4uNaCE1luL4MdJq6drktFA/YhQYFGZOw"
    "UFL5Rt4FjcpJTF6MujweH2czfbZtoNjPcg5DcHHVm3abFmXuTg8VClS7RafZYdE0k/P0sHCe0il+aJricijxK5MarJSihGagkctS"
    "JphaP6UrGCKnSX0vsRxJasjCEdPJIobxQIO3KFYRXaBSdf7sZ6erj8RaUXzUQM8tXYU2UuqkK5uQZlFHfvaMu5Kq0ovsZ18gU/dW"
    "1U1xTDvf5tRazXrIcWj2nK1QadDlzX03i3m5XU9qPLOpl520lybjGFUQKZt7Yruv2knE6Wq+XjO9wPM02nW1WNIiUqoaN6Npou9s"
    "uTQYsyqsVKOYzFZdbpqNIZE14FMwzbFqm/lNsOTtRcFSNSExe2SkapTmHROoo2fYZQio+LTWlCp112lMbEvjAea7UWGdLdg2CfdT"
    "Crlsc06Qfsz7ecqczxR4c9JzrdepFrmOBMYIJRK65r1bZgVyVNzqYnW6Qyg5ftBp3Lj3NvZbfJwUb+oLNxx5d2/G/UjpHNLcUWUw"
    "bFiKWnLJN9CpsYOL7LAeZaaG2HXmTcw5vav66nLHc6puKNZSm9g4t0RXJYrkV51b6vtB7suY+rqtW79NDkbk7LvFr3cedR/99nz2"
    "y0/37KfvfwwfH79pPf3tSfL07v3pk9AJD++evH98/N2bX4/9354cP2o/af7w/umdR/Gj+e2zcfO580vrh/Aw/O7Um02TX3/+cfEo"
    "hJ48mE69EOqdPX07/slxxrOpTY6wzPOO9+AF5n/z68+/hI/vfLf45Wco/9u91uHxD80nxy/ePX1/K340+7HtAVxPjk/Onv52z3ly"
    "fK/15KHdmL3w305+Wv1w++4sPL597/fvmu5v3R9/fBb391/f6T16evTz/i/Rfef4h/3Wr5PfB++evn3482LQOXaXq84t+/dx8uyk"
    "O24/mNiHg2n/++ent+/50zsnoxvBau7hIUntyWSP1M+Zmck513z/wrGmoUcwbOdvEyuZkBlawgPvI8nw1oQfr8AKg5vgJ5FPjujw"
    "o5FRI1p6Lt0cj1C3+7F7BgP+hQOj22g0yMHBwWiR7N9+Prp5Po08F1mRC8LdAibdHWYA4oLEuCR4ZTcc/Qj0gO/eJIoAlBFtBlrG"
    "NG6oMbo3fxvSPO7cg+VidIf+xRTNjn/0lMwnq1kNQ3TVyJwdLfsRz3WfuuXJ5oX+rgAAP6phbKsaiRMS19CDzzKKecEj4i69SXFB"
    "taVYz3tur9OMsZIzFmZ+0FMtN8A+j2uxQIKvQJHNrvZWKUD9zxCcKcdnCxIPX45ug5D8Pf56gr8e4K9j/PUMf93DX7/ir19u08vc"
    "s6fujBbzoxnMLxTAY3ICc9DdD0i4dOEd8Pjf/yd9/X3lLhP1NZwrrzFaJqRv//2/xwhk2tLRBAQc1hxrijXA6mXVsVp4aaXoE5BH"
    "Xo7uwocj7BP8+4H/O6L/XlkzwPdEdOg3EDbCJXYoIMBh+TNQ43//H3xwx8twShNCfP1tNZ+wv1P61z2J4oRhAzA+pmWjVbJiT3Pg"
    "2TzRJ+/Zo9q86CXAwNpnLbNmWaOsTdYia481xtphbbDqKQoSch8dnsMU8v1vZrNvzs5w5Jdxctc9Owx+IuTN0LZcNGc6p3drw9F9"
    "guY4wDmX5G0Y4WpwC5aNZRhB2pyqST5b/vf/9y6cRbymZ0BnzFPUCBcbHMLa4r//N1rujKypq2X47/8H+PpM+Y41ahXQqpUMCIaa"
    "gaXXXAkTmyHPcQ1KuUJtCqIxlF7Nlc93SQzI9ORXWAmG5/ALTfCeTg7OZ7CGwNq6Vz8Pg71kEsaNrzh/a8xhdL4AlnXsjh+DID36"
    "8GGEkvUIjf1oxiUJ4jpjnTemJKmRgzT9htGEco9YX2IdX1rnWcND1SzRsU6A1e7VD77FGHt0AV+DtJRy7WcTrlVwPv/660cTvMcn"
    "jVVM9sYL6wm1KYT3WfgunO89ndRpZ+/D6odqhQrvf0RrOfAjD5qeA6z84d6U4J/6OZQhtGfzA/gKG1GgOcriX4THuCrc2JsjT6dH"
    "ooAe+kKZf/3rr58DVFbC2n48OQBeky7ZMAO5KGmNmAIOPFCVG/jL5VprpKnVjF6lcD/fBHfS8IAGYxy1BhMHQSpKVyaSwmkZ+3VA"
    "cum3YJ2aJwf3YT1kZtDMiPbIY/k5lt5NXpJX1vJAHl3NX96fvLLUE0+a9K8RO8GUn6gyFPtCN5yvLCnFQTKIdKN/3Z+8tF9Bd16g"
    "SRjTEYK0RoxL9Z5Tf0X1YXkdqB01egUEEy33KGWisenjSX35krBKFEWjf5G0jgNanLwSBV8CIl5BUU7MhGvQzOv1b/7rpbv//tW/"
    "9tJh/cAH9QMb0g90QD+w4fugDeYHhK/+1TcNWFITkD++/ppONKZfDYS0B3C+OkjqChhzAxjLel0MBrQk59hoB10rYEqMVN8DT6DW"
    "ja9jmP44McP5a5hZ1B6YzH2QcuAJmCuag06ZBfE0Wi1fe+h+E2auH7rURBKfl0HoYxbcMsIflHnozRQ8xwsQd1/jZ4fayaKMTrMk"
    "r+e0LPDIpfuaGaiyd9jkvmbunDAnShOw56UV+IAO2hAA+pryZ1bX6et5lMDQ4hueD71Oe0Bf1W7QBK0vPC1tkr7yvtBn2gn5xiVE"
    "8co7r3Ct2xNgs4xRyrkLjI5P29tnj3zYY2KVZLk/hk3AqH6zgYI/D+kJLzAj9uo3b45GaEz9BfnwAUYeZMQk/ilMJnuj169Hdc6Q"
    "z9c3kuUZF2xr3x0dPm2AGAeDTeprGAVvImRevhb8ODlA8KyHdE2A7iOvRwVWAosILMGw+sKEjakKhY9r9NSFHcZ8NZ1SPMP67715"
    "DczeBYluiLplsAgAPiavZ/GwS9p4XQqkeCayxMP3IEifzsUAv4TmULxBZvMasIi2qHj4SUcWuAGIzz9OLPFheL5awrpIQQqhBv81"
    "f+e1s9dJkiyG33xDJe0JSCjD3sBB7W0YYVSEpJieodAhO0ABBzAT8pru9HAs2Ss/4nFsi5HDa96fIWxWkwneuUEdHlr0Ajky2mbH"
    "d/HQkScnw3NG+7AihvGEzgKgdzrH8FhihFcseKyVuInM62EwTwnqWuBxeA4YeT9Br2Zn9MZ/jTkZ4Y7uvXg+sk7D92jGjnuZ6OT1"
    "wsWt5ogayL9+QwhMb2iaTiyK2oZA7c2bSBHWCyCDL3Feolsuuqf4UmwuRpb8gMITpuPfNBlAnIVxDB/usqf000mE7BK+PIhquIVN"
    "v3C/JPDpMXv6v//z/02/Rljm8Ps0AYh3eQZpx8uzmntCyVN8it23CNQR/EkTV/M3cyC3e3g8Dx9fsNcaPa6HXCBrNdgROoJ9Pl/X"
    "4hqVMukXEPZXwKn5F3hTvrkJJLtJ7RyNiYGNfnk6IXPgriCII3j4N/PtDHdSS/b9F/Gc5pm7b1kQZewDYwawh6EMJOafKTnE4rtI"
    "hZUU5cMvqUQ6p/sElhvJCTPjX5HGRxuT5WSjX9wEWQ009iVuo4gPeBApPAesMvOjtPwhvNaUSrA59G1CTlglfFOmfKJIfwb8IXwH"
    "3+mQDNOvfKTk9+d0k1jjyUrGeXRrHp/SDp+7FD/r2tMIhGRMrKHCa03gzw0AHbWWXYtv1OjEZl9gRtXGBNZYUkvoNGKk1EjbOHVD"
    "7BcKUtBMMiE1ivsaHizXJm48/7//838lNXe5xJWodoby25cMFkDxnBP0EXuqJZFslhH3gqAncDGYL5waFxJqYVxbruZ4L1Tjwnbt"
    "EBjjEYopy2EN4Tiau4uZ+wa69cKxYKcb1/D8CBceGLG5j9L+GyzPqse28RwDQCWsSlJT2gNWb9VOJ6E3qbnTOKohN4tZu5QvNgSw"
    "KY0ZoR3WPFFjBkQJUwZUIyyN2jE2DU8cktMJzDAxmOi0I5YQnU7O6A0JgPTT5KyWnEZYLr6pfL8d+TjXUgzWPKgDTzOiOaGtgNxU"
    "W0xXwOFrC6BVCuwJDGnMU+PaPKqdwiwFNE5CHzIwlMVRSmJQROkF0A8wpljCg9idkhouFnQMgEBqxyt69cdwxauhzUdBgIhJAQYq"
    "i2vPOCjsKg/QMIsQwoSjyqIgnIIcACgW9dGCYnJanHgZgcLrklBp1Kr5nPqhAiR8IO7Qg++wMwyntbNoVaNCBFSLPBthB+xSf5Aa"
    "o6KzQnzxcF/5GhCM0xNHEWYnSLAOgyGTCzCw1PNRFiy4G3NRSaWrmFfpKNjBQyl03pHUWJ5cCVE91FlcKtvQfRcGzNfphn8Cavj/"
    "uXvbHjuSK03sryQ8GC8JFe+S6tFCqt6dRrFY7K5RdbHEIrux+mLnvTeqKsm8mVeZN4tdJDjYDwv4BxiwAX/ZbVvAoAW0gYEwsiHI"
    "EKD6J8bC/hs+rxEnIiPvLXa3NLP+0M1bmZHxeuLEifP2AENao6JhuV+8I372Xj8XuYc4F/1KXjBPeO7Kpa59YCnMFmxp6kGYXW01"
    "lCqX3NEDZFCH7VAvmSfhm6T2UVf7m2aB1cM/xVk8CfjqM1evpauBXwITJjrp3Hyo6mWB6qIbT77JnMZUbOsWzsi//LwS9cY8kr8A"
    "DiqMVDpaHC2Zkfjitqz0nMqbIvsFygY9TcvQ4G/oP9UDFBftQm4DT7rMRvSD1FMUykArWI+fJi0zs92KjwNpxKUDMeOWnfrs4kKX"
    "CaeehkVM5OJiHxE3yx7OvrAnU0lqmsia9mVXzzbCP33nKznXsHvDWo4188GcGeoRHgXIHrow7nK5REkXZ03ZDvV5TU9fgLgz87MM"
    "3WqoRz1XIkcVbFY3ixvsUUX436C9ZdyS2fBhN/gxpTvCNJT5StsJE8aXBTjWfDVzRzXp16SB9s2B/CGjMJPGRWTSfP9BesBThYvP"
    "ioPlkk9onDkps8dTxHMn3GSW1Fqu5gNU+xj/LUAQH3BrrmEYQNum+kOSenBcmC8LmK5doa3tNO3neF3MDHGFz/HT3hWc2b9PP5JB"
    "H16hDwzTIZkBihYOYUwITM/kY9wEvXPCUqiRsH02ZXY9E5HsnnC4+0BlcJYo8dM7Ku8l9Y/xOFvBIQ3r2Q4b5ADIWbFB6Y5ozqDR"
    "p35w8avT8A5abjBgzZfgceJ8AR/YK1T1gb82iDpMGg+chr9isyDvyvjrEzlduY1AtlqKtRWhwPym4EemTFkTJufQoYh5UNdSwlaj"
    "WhAU1uVnXIE+1Sr0A1sJa1aoima4AMY1dC7pxxdUJFQSytmKSPmkI/8U/xgPHB0/tMg5/B6XKHs82Q76BTNb82bp6BUm5hu/qzo5"
    "OjgRJkhwUuhfL3PlVQeF3bjCg1H+tmuEd2O6PRzyr/ESSRE9tET2dkYGKqQIi/Eg73Eds6gSIJlDJYhD2luZluCxf30xImua+1nD"
    "IhbN/X7BMUhJESXnUEyfjIoa6pKiqzGRcVFPQ75glpRw9ck4IasPfYQ/0gKmXS6UaZYK+la12HSjIHPD/VCOcSrtnxSsF0q/GHqm"
    "DiqMf0yUI6XlfxeVpkf0TVoY7UtxWXySLUraK1+slcskPSXlCJHRvGalzONaVTL0+LIjHcWn8E94CPeYDV+2KltFR515Th2QRxwb"
    "TAI0/ggvGDGetB/4wzboHJMU/Gu7Nzjq3WAqWQ/dmpjzGf0wL+CSiY/hH1NFBxcLrAP/DY8pex/yLPzX7xYmRnuBCbeW6J25V3gG"
    "pFvoJOwQODHN7uACos74PBCpqqQMmUZFv1AyDQUjQoUTEi7qVfOyd77XcMYPpJmLXppu+wJMlbMWBU28fm1aOHDfhxe1u0Ae9u7N"
    "+wJ/YpV0PvPhZW4pf/WuwqSr8hoOO5JD4dSFn+E56saRXp4ePwEJFrM1hndwtjrp4u3/jJ380/9RYLv63FT+hip/w0oK/xyOczpj"
    "Vi1sChKTQrt847Wf7XuRhDJTFhdwJr/7VeiOTP8JT8Bzv9/luS+3XmykzDv4+f6vA2sIHWvOZDs+sxuRBkjqWDtx5dItjxuR4oFv"
    "wFK9e4OycShE6wkljmkVeZ7iEvD4KbIRJBuS0rp+M3opBw8q8qAdNp8UrKPmXqKaRPVkcC4RAenJRDenKlyKfO2kuX8hetAn+EdB"
    "WtG4wMFl61/jWi9FtWqKPKuXvkjdoi81loFWS9YdvYNKe/gSZDmYcsSP6+IKZHwnyCNXZfca6mGzgpYyx/hBOMExS2Si4CDiVv2J"
    "FqEdwopUYe6sfOzRwUcLDbRQvAZ+ougNanGQBbXXvrD0J3TH19KEVy/1t/9qSQOAe0QpInFmbagkjZ5Ete41T4VfGnpPYsITKcSy"
    "Apda8rFBhfByrOpfc2fxExf430lgfvSKJsbPacurSA/3sKZLM2dLPn9WvR5u9OISn8iq0tu9YsXECSTxcFaYi6wqTApUvZMqC6/9"
    "s6imYw7K8zfasmCuRgmKqfFyDquDUMMgjIIIhlaihw8f+lp4pwsJ8BfCJM1rI8yz9gCLxAPmgjKwU6jrwpb1M4Wj2yNdCV5cwg2o"
    "2vSuvvi4eEg8DIZPvC9cpEwb6ZCxktDxPSbgh7mxApWdtsTDmNKaNpAEqjLkJapnonf4W6fgNHmuki8pZMo+DOlf9f6mZEjsY+gk"
    "FMULHI8QusnaUHhkO/rvyWYD/TTPDvHohqefAf+Hum7CyR2VCBOEw3yETfz4ofI8uESWBd4ifWPDo8foAYDMXwn/Pam7VYtOCwSV"
    "lKgkVvX3x0C216TkR/uGFi83vsCMRBVyDBwzBeCXQBzvi3vEle7bGfqkON7wJPXh/hu0ub29q6iKwDblOUnj3hhGLw1GDR2VdHS6"
    "gu3QxcVQ17YuHtcHTsys+HzHxJCivWoG98moLV515KekeeKHUGrpNmVV6+0GhDIyZvTFvG1fEwe0PbpxREnyDZf0YhX9OX5r5Cp+"
    "ZBt9zgc/NItHtZg9SGz/Gzg13GtTuHZ9j05qUBx/MlsrqZTyFS2JVoyNXBq9soMeIrmyHh3HUa7XpOeCoqQGeQcn6HvznLTHRCW0"
    "870xUpT0NVuplGdHLzZywdjw2eBfiMR4ItIiCaBeo0K3ZWBSZExJ7rqe0NCEw/YmtjlqF/BblccHtC2aNWWxxS11ceN1jAzW1C6/"
    "sJMPS9KLtECMfzDzXW5kGVGNdPm+uCTLES5MKEOLKaSSfSNkkiy6nslPRDKRx5Eh2ZQGkQdEJ0+RKPyw4JQWMESJz+JSMEkLxwZj"
    "9EXTx3LwvsTrag9zip6R+s5I7gW5bOgLdBfSs42Y+SqSdUzVZ64T8qYWxlPYwSTLOSJkD0cfMLMO1npvYtPQnwdwcYokBkI+IA51"
    "ETbcT/nbvQID8JHkWeJ9R3AHJIMbWiBbuhKEUhXZKQK3IEJlF48ZEMlcLiBCO+ZVvCfMiyUv5BNkpKX4CNr3wPdeExW0r+MXSu8k"
    "WPDPpEl0Qafu35BcTDcOr8x9YbUB/Mqb+z1xNSM3gFFJQ2VYOlOY+v+LAfO7wIlNrhz8onNkkSctMeqo1ZsjeisSginB/4clCRp9"
    "Udb7b3N+KNEbqfUzZEJ8OiKNoHduQR6Bvnw/zJGk8dlSmCPetvpNV63hyb+jQbslGoRBaIC/SV6DEiRJ9yq5xTULawNSRWL5/Nw8"
    "u9rwo+KzF+YpfO26hpQFR/LT0F9c5lwsGVrQFPHGdyYo/m3e4030GeoB3g1NtQG2XOP1vXmfFEHld+YVjPMo9BNH7ab6Ks5ap6zJ"
    "C04rmfenoUDSHp4UKldqCVEHapHOibLwOf0Yny5l31eXDW2id8g12ALNKhAaPlC/FLFfLZcvYYJUEm4KXDA40+LxklEDRaP4ywNa"
    "9R8V8brDi882+jxefHgF80rvJhefhWDWUqD4sx5NKZeQbkspXmZTiIj2nFU3UiZcMvhqO153kOOfigjM9zq0kV94ThYXko13zBaY"
    "KxTm5w7uZ0sEi4ANhdeXcBGPl4mnh36OJoBLKDlIoTIsBGlZeHXlk4gMhk0rxw71Eg8P4i6RBwCTmFisZyz/jsy+ePNEScih/LlE"
    "D5jeuA+I9CcwGbFNWUPI9oqyRsnsBkujhTio/LW/qAAsa72NodkP62/QgQMmFD03Uad1s1+gpV4kO7+QZHOFplFKFtqeYS+LE/z4"
    "BD116FolNjYdN98xZ9GaRvI02sJQ6CKDJs2ePBYjIwcz2VurnNC4NLOY4Hmpl8sMIYtj1mfCx77kP+nia7tLQ0BraOx2JO5XcV1I"
    "8Xevi9iC+ijy9WN6c9FFRL+S+cbV7kXcVmL8ZFTbmXe40gq17I46xcj+CYnkDYjeN2vDZQv80756HNmRYQcV904OTgv0BL6v5cTi"
    "zgyvo+QE/AJ4ZsfSXCeslx4rSg02Kz99Vevq5w7l2oOz4+K1u0k/ObsSQb/Rs1NXgbfTWQeC/wnf60yF9NlTHP6zxaalsdLuOliv"
    "64pvnwUU8x2nsxiEVtHL8PkfnNPCjpEzmz66AuZF7YtCj4zqPCF7KHTSHLDTg4yGLtwTI/FeEn9bnLoNlH4Nv/zwZgU6dqMhXyve"
    "4zq0ZhRBkW2UPZ1APJvFPUotFaq5H5wu0Pe3j+tQqxBm5Rk24suGnINd7cI06IaxM4ETTarE1+gVh42jw4zO/niQ6VJ4z4eCthap"
    "6cLn6okChen1Tx/u0b50X5WYmLB49LMfzx79m5/OHs1+8nD/J6inygwUO3WnMfp2/QjhSLiCZSFJOaxc5y7ochHPYlckxDw0HXI2"
    "DGniOg5L77kADO9dtX6/jwtoiaJtPol54Au+9P6oUFHNsl6n6ja+pQT7ntSGTkJl/YbufT0qOUSLjyoPWI89kEiv0W+ANSB4/q1g"
    "ZRCLDU6NCg6j1vXaZVke9BHVHSLtwMFxcMGKU9ootELVBk6wcKyR9oYcRlxfUChHfcNqIz4EoM+DaDgjNc/xRbKV/VEr/pp6SuIY"
    "+mj0e9B9cdmBdzgctI1g3XtF6x1PuHtk0ENvTei+PYRe1xVGG8ks/5z/0ltgKTMJU0c134ummm6V95nGiKo/b9umQ3dYGgcyhKCn"
    "hsYuOUElTkV7cbHHVpY3lTAY39M36ADD/ZXuFi9SX9vKK7XmN8Yp1VM1B6DjpVDPen1Ts4bxhM0KzCPF8+Y0+DzSAn+EjvB2n+DR"
    "2bXoRkr5agqMRfCVqJXTbiO+V9IRRq9F7b6P3JQ1f8g7Rn002+que4rPyqbQI82finL0k2NR01BKkr3izS4BQL9e8DdRBeLojR1R"
    "RzsoWZG4e6bnRDwt3pPFzkJchA62ZxSXWdb7LFfH+zX0aUni4HgN8Dep2FXVvi969HldsrSHLNOWnjyFtVB64ajNMl2JIw18FQZO"
    "C2How/qjS920Oxo5CnvvoUYqF10/cp8eM3pb8Xc91AgddGT5L/gVf2V87UYfjVwCdn/ZtKrZVNc6+cYW2SHj71kZ37QyQ0PAAjjM"
    "srq40KgI8qZHPnl10zPxFGxuxjnYdOUNZQsPkudo7akMmV5QwyAGdnoIHRUH51P+JTXre6s91MsbveCrUc7beh9E3vdajOfj5SPS"
    "VjcjDpcWe0H77tyuYFp+BVx5xulzaNvQvGrX6OXiSvxYxIsxfmk9qqKHGpVw6N0cS1P5J3FZR1d7f0Ig9QZBv9+0617P7HASoB2B"
    "DCdMM8G8I1cs0iVqPAu1NR96HywRqtcTkz0VQsG0T3zy0FmKo+lQdaoWZqpAgkyC0WiPlADyFLsDTJ10IY4DFaKOnZWidvZHRDwL"
    "2AoVmRU7+1R9z74cJku+0Y0pDgDNzRu2lvsPIsc6qDouEu7IZYbA8K1oRMLIKo4y0FUnO4dZ7oh85ACSnyNa43OIigs/DWFfdlxy"
    "KyY02eC/yjk+gplU3ochKZ9DlSd2kG6iM1uSfIGzrsN0fcH6TfkNjL/5rGIrghhcgyqklPsunBs4P6xkmVmdt+q2+Qahj20JjLbE"
    "83hZO/u4YTHTKDM0rin6GJ1uRDum+4b5KgqBtuTVCvfZ1fsC5JLVexGX/Ft6OX4c6evJLBa5Y8XlgkmyVvV++t4cSPzIFopMFcW7"
    "ZdyCeDMtvcuXfzU2VwSTYViHYLNIq1arBZkd1W5R2ChKXxSZ31pKnvNvLFjr9Niy85KjH/nPxJDo60OF/vOXp6fHp58qlSRLzGXO"
    "nh+dHTw/ojJuTVtrXOj85PhQK5osdHbw8pzqKcWLJXn/9Pj0+PyzCROOFDk4Pjl6gkUoUsFbPpXYn4ZToSRfS36NF48nvFhf4h2k"
    "FLqWBeh9QZSqZnBxIbXp62LlkqtiUnCgS/9jXNpUCjXFWopbeSK3MDiZyUmPC3RuwYbC5/RD2wk9QuPbqdB3sL2lr4W8qUBkeJfp"
    "abGPfpcAe5qzCS1+bTZJWiRvYNMxYGiq+GOOQlV9sQkSZjdBX4pvbDKraGa6fO/fwQbjIbykH/55bDkzLlhqFt881lpP5TAx3cda"
    "pc6oF9KH6BkfGo/5Fx8UMjjmhOfBIiBzw5IesX4Wu1DoMz1vxRTPwkppjypb5Cm7ZrPtAS5kfdoQDPJ4icbGi8oPtPIPfDHybnoq"
    "3uXePJxaM0zZUzLpoYDL4ShYiG+s7Ch17yFqEdDv7H6yV2a+IthQj3lC9bJiAolE0cunoH5qAnW8ejwJB+rLGxbhr8o1uWzu2/Ze"
    "8qJuaY+Tw2k05/ds8U3ZexKDqwb8mVIZPGo2SZmglokLHiyXnHsv1FbiI80VYGocF5VY7HF5dYGXKalbCsKAO9Rio5b8cMlfDiJD"
    "qVRLUb4LP0e8+FMLDvJnteLmghi7rGQFmJdQhaEq0tE1hX7JJIlKEX8CRBtW5Xdc54h0PomLsfQuHltE68BQwqX5DWq7Rc9CQb1m"
    "1fejmn4O1+toOBjaTDashHPTuOj+gWH1onJjWz2uQGe2xVJXDnW/1HwcyOmLYWZkXxLXBQszk6C0BrM1JsRaegMw/ZW8nH30UE+I"
    "jx6SE0xa4Ge+wM/yBW5YuidviRu+6EXvS7IgYFQTyi/+bV815F5DFglRGuoCiIKOiqAL84a9tuk7hMAg129K2YA3PtqVZfx1b8xr"
    "UQDpzFc0DgWl53YC5dJl5AdnJlCdX86sq5x/vWj7jf0W/zZtj7zz6Tns1A01+SX9iBzHudHF5oDmU/zoQYyD+R2Xw43yd+1c5/dV"
    "O8cyrh/rqmQ1rlx9ob73wOzwzzANDflCLb2ooO61JDEtXKagERqmCtN5ocviE2oYQpeRaKj5ScsxXvwgCDN2NU5HbojJ25wboqfW"
    "Ccer6L14UUUksc2RKgy3xc979cSTz4XSrcujfBgIFRmZdI02WdQt/EPdirEL85Kux/26RuZ1E+vHxTBTbqiOWUF5xlC84BQqGmPK"
    "jsJc/8qEN/pQx3gj+CIyNxiPUi66Fm4ZlBLGBEQmH4TlMoE94zJm0caVjbVqdk7xoGI25D/Q6p5pvAxPcssqhj7Z5X1LxoDnknGE"
    "Q7K05fNWY5jU+RnOqy4UNcwmuK3+2+LReAn1svr3+XfS5b+n/RSRFe3UxzfJ1sWVH00pvTkV1QS7rQUri6rrgQro2JcBIZykJjnh"
    "WsgSQylZSOvCfyZvpZHzYY0WAQlyHzrUD6J/6rAmaTVh+nnVM2m8lX3NYkZJFymKzMV/k3c9N266kRSgDnGMnGQ1wXR7qEd6Y+iC"
    "y8L9rZp3GrNxGP4K7L6sRU11UJjSBbkbi6y0aetlEGFQ+mAVNNvXSjb3oEGBLIWslIOn3IW4R+rYkspGfuZo3mYfrS785CWsP6nw"
    "vCUvsFinokt0hcHhoSLxfUlrkAMd4WD0w1W5dHKMU14JMpHRLllwak1TR8uhWLQFqcKLoU6ZNDBRfMN7jgpNbnN4tmkpDRbruuTv"
    "5Kg9FX7Ff5l2PvOfj5zhp1pEx+4ly7dP2Gk0PF+L8uwsOpbwTSbAPOZAWIhDp1Au0ABZ805mhGYmeiMiyKGVPPIduQhpUliHEu7g"
    "6KlJtwLy6Q78GUR89TfH3/6F+2qt3pVkFQdiOTz/Al+7TZxNw/g+yOsL4EpzFmkpj4f+jZdJMbKXxXy4lOLs0hruyeztqn6uWOJy"
    "qMjiB+0A06G/7Bu5CPicG0PX9NYLrIrN0O22DDmcIChkZCKBQC9OdEFGTDM+1jFxKNwVP5XeUZgY539Iu1n5QnjH8Ak3yEDDx43m"
    "YUm+13ZCUKcXWeSRFMC8fD5Ev8C/CjaBE4+WsnKePaCzIKi78Xt4fI5PrTxbCHBLcY+ucfdDUeGRjx385l3EpL0XlBzAt9LAcZRo"
    "JDgRvpOLd2liWHW0lKLYvWGNI/6Kn5/Cia0kw+edtxDJ1G5ws1NZcecQSmBbyqarLinEUuclafdIjIIaKqe9b+Q6G2pPPjzMWFUx"
    "Po+M/H7jjcqPDapIEZNfnaZmia2lP+cd/iMW4mSLw2selM+wJ4Ps47febH9F6+zGS9qKhyqSHIoi/X5UA+uZVCEVvwLGK/rRM/7F"
    "Wl1TAlOJkUoO008y7ZU3rM6PsnGFN1GHNdimCYmPOONa6KVIODCgGjckZrNUHvcGdUwv3rTyuI/aUe9eVDc3ZddBa2+qZklUHT6B"
    "Sw7c6vTyX+IRGtpBVQIKDz0nUsOjGP09lKQkCSZ79uOv+LmPFiCWSazKDLKkJFLi0oGp2ZCjJTWfxxkWC8qFGjfBjqemov3gxxqX"
    "FUGGbYnQ/nqtLkEaj7qnqdfGjmq+Y5SijQKEKFebhjr30XsZ+RNyQxLiQxfry1ZyIGKLyGbIuwtDjWbFGd7I8MZEblHsEcaciH0N"
    "OYWufI9iG+kRsIW+5Y5jKY7PXlxV68DJZsUJOZiUXlCXgE1ku03rxzArDkIJSkC4wFsbC4vXmKgdkQKLswN9fnbw4PCpnxnoCoxZ"
    "9TbyhFW9z6UFjn2i0P7VeynVtPqWGYYNHqdTBV1aPi+tM6//FmY7cBp/YdNoMywBD8l9RgWe2G/xs+Oz81BQN6YXjnBDUNQqFoBf"
    "3AtUltkbj/aDqItiuXXJQaLmgG0viUvMema/3/PHPzqS3Nf+q2khKHfwgX35rFFechGVIYK5EB/P3o8S8+eS59GF2+DNDf8u7v31"
    "/aiA0O+XJUopb8RiRTkSWPUewrx1qJhGi2OWW3UHYK+mEDpJ+0kaJPgkHSNrcc83LB48Zp0u7UkJ2PBjFXO0kY2ITLFxvCkMPKuc"
    "M7hgWCOcapW6/CSyrl3jCtZdu5AUZuLlxCcVXdvRWfZcdttZtXaUnIJzQIaTdZzxlZ+z5jis0DqyhSsVGOal0ilpqO2hpnevpc8I"
    "IRpOFE7Z9vOZ4knTBxi5QrJgSD6CQt6y9kbIRq3rJnGoKYbeO+Rt6dw67fh11Vfz2lY6u2LZkYK41qnJnw6l6tp5Y07sFAB7/ldD"
    "1SFTNnEPRk8g/iIy0fd6vz3Q6imaceonlUJC/Vc2PyCFDmG6Qzf21rO1aAA8h1BThRSNUJzzt/MbCbwQ/+hAhiga98xbIu9UTABU"
    "nDrO1Yj5RKEKzc7t1TeaUfRvi+dAwX+r5Lqf6QH7IFUaRW56gD432O1ZQnywIEvKEJFMOSz6Fb1ix1VDgxpCTsoZGzri605TGftn"
    "gdKJu5HaPFD1Yug61yxuxvyq7SkcZz8UnPVBXfvUB1Ige7z3Dh0L399PKlVhg6qCU9slgTasEo4uWrMirhm2Cd/JtM5CcmeGlJDi"
    "MaycAk7tavGac7ZyOhZybVyIiEGN36zmbf1x7MYNpA0H6Eb6FE2rUHPsVdm5BVwCOFul0TBINluKloB180uqJqCO7QyiBcETD7UY"
    "F1Eq2daYhXwnPNG8sMtoaSbSdJAaeIPmEe6oKFscJvWiXPVIfuwnLg+Kd9fvLWN/uRZ1BnNm3EeswVHyahynmP4ifI+tltclEBGC"
    "lbATZufg1PHcrm7Z5kLeeg49GMvNlbYrmUfJhsc5SGXZdCJC/vLiv+XMb0GexJuEmgCf8J884VLHJ0lRuf1r/AUeWIFISvKjklyf"
    "2BMW2HC5Mc2r1EHktJrFFZvm494j3WDyDxZWiZE4/hPjqkEgngV0iSTBn9oW+jR0HL9iFArdwZTmyMsAGGynbqZUeCoZIb3Mpzuk"
    "Vwb+gbZ0TTPLPtRUQMEtaPj8U19Z19Z5ubz037BXUkgcNS/9NyZJjmcGJlUYlVGgjBBYqf7h0uWVRNwf8q9QNyJpSPat+BsLrcEx"
    "wh2GauCfJniMLVTyQcDeoA/IdM7X4OLej/c++unD4pKVuT+effTT4vXlff10KkVi0LBQMQ/cIUFVlJiKrxM27Q0Zx1gO0VxWvC42"
    "ewJ/do9E/qCY5e/fqGh8P8yTooSwfaW6uIlz/qocyhXA2dmLiYQ+N7AiE/QWIY1kiC4FHslTnoEi8S4snBXoIgwvKryF7gJ4SUJV"
    "nKY9oUADbpJz0I6K5XaBP7SI44qzqvzkY88LXGKZ1g8oI+0LTnFy5jMIIxEEhwwjrYlXRk8sbGYrQhMFN/yCf21vd6HBIDYwZD8c"
    "2Nfv5Dh5b7/yZtzD0KULddfzpfAiI0MiFo/RJnw1LSmYDDv3wvtWu1HC41lamYZujmrDCAqszeYGDkOe5VYmPg69q5cvN6xftE+4"
    "xL+n8GHUrlFOLE2e23eL2a8GnGRia18So+6v6GJmzWBRymdkOp/Ix0NH2RCfn+AEcCEQfB8ggIszech7113zhQe+kSw4OG3whHIi"
    "zyTPcZIbWZ76UuZLMzf+NboyP2OdGoaSc0KP8Oq40bOYXleNkV23tYp7ktI44L/+aT5elt95OI3n9CPpRehAaAIF50NmJyZRd4jv"
    "ZegcicQUTsOf0psblnngh+mDzcNekm999OGWeCgzG0xSoftQwo+AES8yJcIiYBFYB1uGOxZnVw/dsyV5aFzyC/0tAlRSlGfWowDo"
    "AvsNHUq5ZegdJi8wRJJlJMl8+MJwCh2a8ujIuAjM592bq5v3vqznNYsMrxEK+AqtdygSSMqQ8Oc+60To3kE9oQvG0MBFsVqgAmpB"
    "ZIt7jKy0bCfgPqN3F4t8lAetueFMaH5zswIRxXOnHkpCzBRiBR96E9kJ/DGwYpuea7JFhD4s6uSl+Bwf6DUa72N0XdrQlYzK0NXh"
    "qLmsK4ZdwGcEuIqVtt1muBxufwMSy+Ou7Ks6fEZSUL8ub/+Rk1vhQ9o5T9yw6Re+rrdXDw7RnPr//u//4b/8X//jf/k/v/1//qf/"
    "Qd9JvFvo30WL2W37FD1AxyUmHr6qAW9b4dtZ8e9ZmG9R5Yq3G7ogBFwEqcQzZMzQWr2dKas734C8PQoawBL9a46Fgn/Y+VAscPhO"
    "7JGP2WkSnzR8bzhF1GF+EjRDfC/hv31xf6bhJ5hzrV28Rj2TCF9WpULeAkASzvee6GH2kGy/NV2hNx5YJSryaMoQGor8mE0mmN5H"
    "1I/h3Ud8bHUG8SO8/JvwkpUO0duf2BOPhR58+fCHMq3u3dW2ytA4tHoFRspIjjLUsRNKlc7po0hkQl3QjnVBaQF1Rq1J7idzHR1l"
    "2M2Jw06hBe5Z1nNfe/TjRIHav/Z+tEYwoABxjtziEFBU63YVovX4nCsg/UrYzYBerBz1SWMqr9tqiWqLtSOd5RoEi/Wm/9hEU5dr"
    "eAgkTBOMZ4SGpmIF2tePKIM0S5grNT2PcrRkcruQUqujrYvBMWu71OJ/w7HpYje5ETYRKIXRD+LF/Jsy6HhZq8IRwF7ThNKRxd6w"
    "2jNvvb8Xosuw9YPmZjHMq8X9mSyfz98iVCExt14vOtYa+/7NvaKlL/7v//B70ifiv16jiP6n/ktVh1PQfx/MZsTaFHulCTpVbeYn"
    "pffJEqfjffGEpS2jwS3sAthuyTFDlc29gy0Z70SltCdKQQJTij1U/ZeLYHjc12jLsGk9bJUvL77BLND37Bx0MXSktyM6Mlgcs+K5"
    "a9lZwu9zPWR5QXKuFLP//v3el9OQfXTzS0D7FPI4i9qHWmX70uP2KSb5GLbvsITD+BKmrb0jch9yBxg/Ghiv2wx8X31tG0oA/PDf"
    "AjEZ2gZuKtWyHYH4Xd1+zVklRyB++oYj7zyI3+1/7idQ/D5rX7ktIH7PGsQZzwP4udt/uP0n4F1Le6BFGH6P23nVlGMQv+MV3X5b"
    "xAaPcPyO8Mftt4jRVWbw/A5eDT2rL1M4PzgOFlVf4pTDpmqgZ/9bm8f0O5h3VVeEmsaYfg3uwmYrqN9OTD9EiLdLuAPb71kQMaHj"
    "aHdYw1K7oYDJF2g/inApC4sS1ODJgWdlRG6TEH8luU3QHM15YYqyapYltwmH02U75DD+jprrCmm/KLeD/D2zIHFAQ0CKHVAZftkg"
    "SUU4f2WC8tcPqL4F0rr9B/jhYJzXt982i6Fuo/4WsOHRCrUoVwWihs9L0+heAbdz4FGr+e03qwLdi2DCqGX4XwvvMlh/0532gH8u"
    "6WyByQmway7p9ahDswIJmh5Kb1rqYoDWq29/k4P7A4GeCi6xfvg8i/lXRKh/VVkMK25rXXboCrb0qOs4hZJTxvFqtxcOoxRhSQMO"
    "4LAqXrlqQxPeLpCIO61yrwASw++03xGs4YLzFcOSALn6LsMnv8KcmNAY8gjg+Kg5AQkACtXVJewQOBCeuB5/k4JI+xpagb9elQ0s"
    "eQAIbGP7HPkuOJ1kR+hDSCN72Khs8j3KIKXMSolpj9zA0ILT0W/grrDt4WMs7SwfMj2Cgpvbb9AiUl3efv2gLkdogSfJFtuGGQil"
    "Hkm57aCBS04inFSZogaCQAbHORbWU71Fe/QYpC4HHkgf93f/2CsPzuTDaGGIxoAFlXX1Fhd6C5LggZTqsliCJ44Yz4hzTaAJnowY"
    "nPahnIAVPMWeXrRVsW77/vbba1cXBHk5anESYRBYQdc2OAKZxAzO4AlaMQ3nvmyRMyH9wb7F7DswR0ixuVWw+6HdDjnou4KTJnXh"
    "hmi3AA8Sd+/QkBWOc6GkcisCoXxYWgzCy668LmkD+eqIFHqUeGzVZlCwcToiNlgt3rCj8VvKas2rRdvpUQns3FcqcWIJNqE/xnYM"
    "dRKj0Cy0K3TaemKLS2ZjTOnToIVBjtxO0jF24TNDOOG8RpoloeBy6EqSEccohscNXEFXeN44vM3BKUXT2YNgEe5kK+WTMKpFXeGx"
    "A89ekOsDMug1sm5zYlG36eDzm+xXQzWFauiaKzhXouZ900uHmpbQ9wzG4cT2tM1vwTpspjZ321XI65fjWhLMQ+p+KYV4+rPQh2aN"
    "qFGUmqXmWXEI7AdOf/eAYRHD1Jv59mxwAgTxINJUUBsVrW47mIZESCw5BnhqbcdtjYAQ43HToUrVIABX105hIX4+EH7wfOgXMMcD"
    "0Mpq7ZCvyWcsmVxTvjGc+zD9IzDEO/Nli4v4OQlZdnvVFeyXcPv5GGUDqHLJQgPKzH04IiYBEnnEeYBEHNY0QGKrAIk1oSOygIKy"
    "1Ndd1eIU/VVz+/uV69pdGIld2RlSzaIkYpE1gk+2kyCJL3TaF6jC/q44iS/0uJKvqixY4tMSbloLvKRMQSX6ei580Um0xIPLblhn"
    "58ACJj7r4CTIlmLQxMOOoA6jLnnQxEXupUdNPKgpMzUBbHOxf73MfmK8ApgeMVclcMhr5AJ59ERMtlBSUP7tb7+qVuUkgCJXiAto"
    "5MH4Wzw9kfJhhacxFE9gY5YppWi+L3l5MSL8CEJRFmS/YBa/DUbRF6WNsA1F0ZfcjaPoi17k6MziKApRINzjVihFX24nmqIvOd22"
    "hVP0xdeub9mpMPOFRKvHhYeez/ZpQMVQHrXSVYfftNtQFf0Ht7+vgSlmyyu0Ypg6oil4vCjH2Ipnndu0I2zFw6p5W47BFR8Dg160"
    "KbriFw7klPqqzUAsnsCZ0bwqMxiLB6sSbmLtGGQRalu6EcjiwduhzoAsPm+/akcQi8/bvhxDLH6OER+rLRiLUxCL/pI3hbEYGFYG"
    "ZPEcb8yydaYgFr1/faI4zOMsBt6cls9BLULzTCNTUIu+gIVaxEvrFqhF3QZ9Dm+RFYdTgIvuB0BcBDmMOpcgLh6xoqiYl9VXbYK6"
    "+AsQOl1xXb6tygzoYvTlPstA6Lr6gJzb1zuQF3kuRosxhb6YTl1AXzwNG3UH9qJcRpYkJk7BLx7Ryu6EXyw7z36mIBgP8JpX+mL7"
    "ICJ3K5wa1t6wLhNOL5jrztwtlqS/81e+PATjuSNt11X7yuUgGPW16MaXOQxGU4aOUxDg16qsq91q3jlaHo/IWJV9Fonx9n9BpopR"
    "QXBnJTU0fiXKpTwqo8gGKSzjgV5SvRiu2yGCZnxCl6iOj4s1irfzsi6b238oU3zGsovmMUVo7HIQjdS3LofR+AQk5+S1YqtVC8zl"
    "q1JYZglTpMYFySKrluYpLOQYsFFEk2XJV4AwrRa2kTX8TbsLt7FOQRuF6zRhCvdwb+RAG8uejuayn8JtLBG4EQkJSejhrDAXxNtv"
    "jGoMNQ+kHemmgBufVJdwcqJ2Vq4KOPJL7kO5QFpbEn4jaSYfPXw4y8I3KpnIh5aFbAFyDNJKPBMRmmMoXN9+CxSxDF/RXIq6tXeo"
    "iFog19m4GqEc6TZorpnEWifRHGUeyn40hj2aAbjzpaO3gI5KlA1w/QlQx+RtAutYZmEdYeWYdNvoZhc2raHDj6Gf1VdyhPDoSYN9"
    "+xvRJKfgjtLnDMQjoU1F2otJiEeqxLGyuUToPGWteCZdu7fbgR7Z0lEyl1Y1CC2amD1wqC8fEdwjjQO3+0X5Fj7Aw1JsOFNgj8w/"
    "UrTHxvppHEGVfVlhM3ylJzq/bhe3vxGjSkf6fX/FyqE9hsW/js4WbTlqEdU1PEJYUBzh4soxXW4DfrzjRBH845aJUvDHstuG/oga"
    "SPhc2uzGCJCiv6nY0IqnEDM01B5GPUSN1jQaZPh+KySkFvsnl8OFPGfxsMAp5zsH/Pgb5Aclk+4YGxLosaX1wUFwQXtvSiEijd6n"
    "RwonxstZOJ0scwoVSYqhSajIkkSRaajIx4nRJmBFosEvaDQNWOTz0P0EMFK1BO3gzW7JBX/ptsNGfuG6cMWIYSPHhAA0taiH22+X"
    "49WP/SfIbgcv6iuXAZF8MqCR0cHZXSxdDkZSUSQxsSWtYB5HcuKdUNeISFRqYHltDCb5GYsOWSxJFO4eoeg2jSXpZcTKNhqwJFGH"
    "nQGTpIMc+RJZdkaIkkcbVL0CVUme0Dys5OeuX7WRnDQBLNlmJ9UgS4bXeGqvbr+B4ext3XspxKSXb7CChTLEpd3BP9Va9pCz0ZZD"
    "17XLcifcpMjIveUbqmMuAyFncCcPA72NoSfNDhvDT76g20bJhx46+oxqkZzOJ+6a3CDyQJRcTVpAE1sfwsQRUcZIlEdWdzKFRLnO"
    "e7Bsg6OUT1b5bwwq5RLzOOVxKeGAcSguB1+lLDhlUoxWa8KMkgGo9C5XOYjKZ8rzcP+0qsfERIGbyu8Ei1X5FF/Ahgtglchr0QhG"
    "aJXoMUlCGIict7+tK3rsBVKEtkQv3Gaype+DXSk3CHmyG7tyArryUDxK/kzIlf70H/czxq2M/LQmoCtDmS3olWgHQS5R5Sq0GJZQ"
    "zsuDW1Esg3ZJUSw3XTXHY63tJ4AsRRCGixShWQ726iEzIa4zLPd1Pxys5SRdJCgz3dQMjdD3uu3Yli8qkov9FbzdgWupV18UEFxD"
    "jk/CyfLwlmct+Z11CPQIX3ylEgXMamkUGjl4S1qnqrN8PotwqeWs/VVRLpduF8rlkR8EeRYEx4owwbFnAZtpM34XZHfH1BoLMp4G"
    "f5ehH/iy16Dionabtks8F1CR0EFDFAyOJsBXIF40ZD1X+0wW8PL89rc07OuqZ3dAg4wDx+sKjbtLNsua6wxqGvhexHuhGhj1sjV+"
    "zkTfbEhF9rdGt7EwIznsy1iAxGljqbHwGwpHY16jRg/k3qvSkJ9jGWIaB1MvaFnyTwAxDy7hdrQUM69pmO3hLD2rT95WNMydFbV3"
    "xcLU3cjeYzL9weOM9p6l2d1gmJ2Bh9lWaTuFhvmiWrcxve/AxFy1UNnJwWkGE/NI3TdGqJi8AzKomOdAN+UIEvOQ8HChVwdnx1lc"
    "TL4LLUkJZ2lqtRUW80k5xsGk3a3wejlQzDM0Fi2uXEQvFKjabVDSSeSCLD6mcazZKwxHoPh9nAFRUaCdezSiQ/XekTX92+K5g6mJ"
    "IDL57jyIPKOVgqDk0P9oKbqnhZnW4p7/nOXx9v7M+Bczyfua2DGXE3JBL1GvAEITuqUWKWNIYTEP4SbG+g1qvTHTjaPbiot5jFdQ"
    "7AUmhSwL9BNdogot1MAnETuMFo0WRIzMNeWacqt13eYwMjNDlQ5OD7XdCo95YNcNjoGhx1NOJpB+LjJkPULIzHi0lPWCtDKdgPvF"
    "FELOyORWVk4BZ4qgmMXNPDaXK9b5mMrpXIH725qymBAjotue9ylndVG3VzRDsyi99qg3uX5wZ7h98qgx/ki0mrVXemGb1QqPIvEk"
    "wxMS91XHZxH56oJIFk5NPMaCYx+un/uq3HBrsba44ipK+KL2ajbcM3iNYHfn4GtmiQuPYR5RkUzMHg+lLiniCgQZdSffI/VM5HuI"
    "Hlbk7Xzt3nLAXx5aM1qI1ucyirRy7ERX3PNLsvLLQre6+0Srsk9KBdVk+5I/yOFVCIOK/T6FmtRPkdTx7AieDokqCqMqDmLfd2A9"
    "XpO4drAFvwsG50ELos11m8JwIrNTywgPDdUxOTDOw9vfLoGz0cUX73tIfEQzgVV7WM5o+/pbdmutKf3tN8DMEJxTRBroyA5szu+z"
    "mwtqQM/bPGCnWyCTApa/Q0aZwuvE7/mjHFynP9CL47M8YOdpOjtZ0M6FgHb6K0Ob8ocEu3O0cHkEz/q63TfGkpY3+qq0AJ0exVNk"
    "hjY+YSdwPDuvak/APJ8ZJ9XjM4pAWYyoTAJPYlflDk/tZcxFePfpEku8Q+ZwCo184Ek8wvJUrsgmAd6d5V3xPPUK4b/ut3xuQD1j"
    "N1H/9Qjdc+uFZs9faNI2ZwXdM5eVKJ/4cOCttBD3hVZOlHYC4TMligjg8wskrgzAJ0lW2kAC8Pk4+MSKOjdG+TzzHu423ikP9Bmt"
    "VrsT7fNxZo3bbZif8gFN8wjz80XXLkpzD49AP9nSnkX9FCN8uJVj7VnQz2fmPLLXH97OQcrAk6cfQJBFaddc94Olj6+UGEWB7iE7"
    "UD+ZQETyYASwFPrT9kw6UeFu7IwnziYym5Ap9zqYsxt5SBRZq9KoHfLAnwe2KvS3STqL8J/ogVzcoWN1+d06c5gsPAtPkXNJsSIb"
    "BGpiVjkMUFn6TKlEXTDPEJ7BArWjVEnfy2R4bGUJIgMMSh3ic842mYUFZReIqPAWbNDH7MBl9NoxOKiKJ8o6QbTBrCA8qaK7yiOF"
    "Zn3rxWt+Aiv0sVHxoPAqYSc0OwLfRhFXrKZaTWCG8oPWnFViL0jAQ5/Bsd6XE/ChY4MiSm0gqAcFegZNNGxGaB0k3R8MS5RNLmyz"
    "c3cAE114E80WNFEulIUTVQvUFkRR61uTwormzFDT+KJki9oKMKr2qCKK8M4ijJ4hmikyiYWfsmmA0TaxOU8gjB5bHrsDY7TMlkpB"
    "RvOlLMposnwJzOiht25vBRqtr8iGFwONHgrTWcbeaiO40V/wNSzZBuzPWOZgR0EkuBwoRju9X2exR0/kVByL0iMAUmJDJUqNZXNl"
    "qvMQpFwXDSW4RGSBSNVzMWINOUBSb74du35kkUlZ55yMNwNPmi1nbK/R0m5DKU2D77Nopbwd6CjOY5XyzKGdMYdW+sT1FxgsPcYr"
    "VVNp0+5ALTX3/zYFLn1CvkGuS8FLT5LpCfilJ3p2fgCCqYKLcqw4sKQ8jumRCl/h2JoCM32cszdNgJmSzsj0YArPNPgi5KqNAU0P"
    "1cxg7eniL4iopgM5Ktwf7cMcrmmSlAFFEnc5VIPXzHScXKAOW8yG4I39/9BpCy6CkgSgxCszbMghh3F6h7ZxaHCEDKQp+Z4NW6jT"
    "p201JssY6dQrP3LlLHop1kW9vK7SymwxX9+4rAai+PlYY2zHwLqqjToiWKPe0JGcnMjvIYNGcCCdJgKDdRpJ7k1g9O3gkyKEGqkQ"
    "7hKpAERRvqPpSdTmEU91u48IajvyKQoHiHwaZgeVojyJLuJAWdzTg8QtjPwOSfeVOzT8cJd0Xwm82juFLEnDm8NCfZLpUh4LVUp6"
    "PjYBhXr7bavhKgkYKp9O0G8ERBUv/REgqi/0s3whAUU9wtUomzaPiYrhiwVFkMe9UWjUJ4mHU9D1EknoksFJtZyGST1Ik1GojE/0"
    "LNHdPjabddoUHV3FWudtAKomLD1qawuWaohMS9BUj3MDTlFVD4d+MxKzLLTqKAwnhlcNvYDJQ4ZQKRfKw6yirwIv1rjBALX6pFU3"
    "YvY93XTlHAXFkV4xxlw9Ra0yLF7tKvN2BLqK7u9rNaJuwVvNlEuhVp87mBubUGKMtnqGk7Kku9kFjKGcRlqNxL1puNVYzhtjriY+"
    "idtAV4V27uBZmENf5YQCwWihR1DsXuyryOKwkkNe0leDxEpCBHtu3H4D/AEOpEqVbRfJIBqtiMCGyCS8amGzFH0778jZaIOudKLB"
    "Js/vdis8a8XSTttvBWhFuTXgqVY/JDhrlQVnxSkJU03HlDK+DDbrIJHDEThrZmgCz3qwgJ3WmA0csFljZQmriUopPonPmllag9Ca"
    "f2sxWlPyCyit0WYnkt+K0yo7lYMJGvcVH7SxYc5rkNzK5qlK4FrhYg6tBe8PH5CZQW1tO874gBCpZTgwmuRUGGWiQvlaGGDE/5ap"
    "AWISxLXdhuJK3dqC4op2sQ0a8Ugkw9QRb8u7ALmq22uK5Poyvp+Tw1rPUXwL8+UepYHiq6JscnRD5EgMcbAgi7U3tO6pUL7yB9Dt"
    "t4uqzYO8vsyIgzrLhPC6TPXMk5NtUF6N/6NdUxDhrspVdhXV9WsC9xVNNCRUk0+ZrRPvuRyJSdk9IgvtGAD2OPHpJsdwO0s5NFhm"
    "6rbUJI8JwLCI8Xr7WzhBrZ9TdEDFILGRrNDnwWJ3xM3kOhTjxpZZ3Njj8SE7DR5rJZkIPfbM9W0WO/ZJbnothCzKWyMM2UynIiBZ"
    "1JEFBQl6TsvdKwslq1EsK3uAJGiyanQYI8pqmpool2SCKSspl/rhUtTf0L3OwQWR8tThFWteO0qeEaHLHnlvRHZXT7BlPx0qdlA0"
    "3lg8IwnMbLhkYaxRz74uNpqsjZIqTaTyMqmsXJwUEI0JKhKxb9+IEyTAsxzo2mKa1OkhBAjaZ73PaEj9Eu99mUxOw0V3hXx9Y0ja"
    "55I+byTJB1xapYp5K3myyKwKTKrV+Eeuwhta1B4Si/8xUO3BdcUK6qgco9WWGbjaA36/lA3ck69eMKh56QKEPQrbXgpv58+c3Gv5"
    "2a98EoA2h1p7+811VW5DrcWM9yQPaOxEOP99ciRoowp0tXbLCjjDys/VBGptiBOmUHAM12WlhK+XTjDs4Fb42ljU0qm7G4ytF2WU"
    "prZ8fZq1GN6h2QjZltMFjLBtkVUmcSkZeFsfeRdnZiEHDyRgPcTaLeC25TS6bavotqssvO3Bat72Kb5tJn/kGOX28xD36rkPZ8B8"
    "7GXJGOn2JUmg9dCUEcztE8pfSs+zOLdHbH6VJJwOk5iBLLDHDmLyXXENojCXQ4cVojbiIyvXe60SJf10l+goVfVjqNujr6p5ZblW"
    "jHarLFz0l5Jf1I+1MDEozFJXU5i3B2GO8qC3WCBUtx/YcRb39qAvVsOSJAREc63RFKrx/IVTd6HEs2cEe3si+SX6JFXECPq2EhOw"
    "2S+Uywzb6ZRNwd/MxUqbU4Gvp8jaqp4Y4AAvxLkTNa/yCXLGkthrub79Leb9C07Q6nO2R85Rvattagu6KeP+WZCj0xPy3RpWAfvW"
    "+HGpFtUn1pgVL03JBd2cSYklALlOEXLxRRYgtyrHALk0XXiV0PQd1PgESC7l2JGCkyi5XR4ml6XXgPKrUbV5rFzrv7wDK7dUj8Sy"
    "GwPmasjENtjchFhsjo01ZVIOaXHZq8TykHs9XQnsbXUEocvWrtvfNIsqLwZ4NF3Ps5C6iF8tdnzrcXVhIHJUohGkYyXnBLwuygbe"
    "oRyHzqlwjDWILyRtupEwYyNsCnQ6JJcbDkEXfzPK56J9ACos8zC7B2pQMBFkI5xdKwJqrmrtHqae7op4avbRe3BwU4C7iTOi4O62"
    "lK+D9TAfArYbRfyN8HbNeZl3JlESGlXjIVZCFVdtJ8ESdDlmR77N7TdkXIlReJ8wY8GvNOoFo+1CXqqAwov7eMI3JQfE+zm5lEYD"
    "Qh9F9OfNAPFqqKopngPifWZqc1+BmBcrgCwaL3TvXn/fyPl5HF7tpsQjjcLM4KgllHlJUIvhJmPngQwq73GDmEgwngwqbvuWxPQQ"
    "m2HwTYBN7jE7DT3v1bMdgVauWW6WrLjE89blsoPh7wuRfwBAb6teVZR6u6I+d1GPJgF6o6Ug0ZJSLLTo1x4Tqs/2wYzR2lBwcClM"
    "b4pUEMP1emZHjeTKGtxeLbzAW3qytkGOS/B7n7R3Re/Fax/XfH37G+BgbS/2hd4KyJGNqLC1Dz3enVetW5aasbeMuY4PQbBVHEUe"
    "myQabtDvEPfw7beI39t+7I3bCNzrtFs56N5w+fZ2SkRs0LQfLUGciDKITcI48ZxOw9ppY1say2eC4ouLrgGUmt7dmDTHOL4H48W1"
    "NEbOnFG3pOM95TTX7i/bMa4vAvLSddnHsUxB+57BlA5EaUEr908jgN8DggjGGhHiV0JBKoyvIU63T7dDY3WOoH4Pgi4RHkwC/lJ+"
    "1HKc9DtF/lXRWCFacuC/Dv+UPCilqTePAPzMZ/qH4wMovJzoyaw4L6tOkq8vpQ1Mv5O0koEDDh0y5bKowD59D0EDi1FjjA2cpLPF"
    "lV6N039E4MD+5Gw4ybK9L6uvejlCCY6y8H4gRrCGP5SSKHYME3z7v8Lvrk1wgs/xaqCpTgJM8GOyqFHARMjkk0AFU162xEsghQr2"
    "oSnGL3iMF6ypuEaYwf7zljIyTwAHH5arNfA4ehrp9iZwg1Hh0FOkGuaDRqRghg1G8kMQ4Qnc4KAfk1TqNlPwCD2YJjbKthgSrBWl"
    "eiCKl2GKH3yeXNjuLSuv1adrtVaE10G+JOSBhEnETsAIrMQdKJOCN8tg3MugCo/p87tgCmcpdQwrbJPGjcnHIAtPkmqELqyU5Dg7"
    "60SNWwNDcgDDdvvk8IW/EHRT9mRXsXILvPBhktXfawQrVhwY2dS7RIWchBNAw9ubT8BBOZrt7ijDB6FHF+qrm0cZpuNEguRQ3/CC"
    "lC1zt3rQDyA7og/Ess3jD2xBG05qTay3UYxScTE0dBNv/Ek+gTssZ3VwbcogD38h0S4bThShx7ZNaJZBIn7i+FSwTkXXboSUMIYh"
    "FjAIAkPFmDPrUBJjD9NZnaIPs4U0h/cafelnL4c9DEfyBO7wUbORUFjNmDHVmsccfjAFOqzpCDKIw2m/jhtp2wzZIg6Lnj0KD9S9"
    "JAlfy4BFPIE8jPtuDD4sFi5M9UlJlriBSQxijfG8/c93wSCmIXniyyEQo+KqnQIf9vApSe+2QhALl8oWTkCIMwG1Ll4Ei0f8hNy7"
    "ma1MIRLz22R2phCJz9mjjsh0EpC4zLClOwAS4w2q5U1GLAj1rtfokMFIXAxLrESz54O4SLWL6mXk0BhUT74kq1Y8jY2LMGlxhVv1"
    "g6QmGEESHy+rlsyjESAxPy0CWFgOlPj2a8xv/i8Zllh6iApC3JuVjCoxuC4VzQYZX4XIxJjIxiesuf2Gzz3WekY3XJnrFJQYlert"
    "OPrIoBKfYYJOMdLGmMQeb9KgEp9JTrIxMrHcmzh7Y9WN0Yn1UwrRr+aOQqK99ia4vigFI3csuzFO8eO27B9cow6797BIGazijFk9"
    "i1QsN6UYqfjcDX1Ay4qBis8TzcsIq/jFQBqHli9JClX8z2yeL8hXmCzntbsOmTHJBoLwnK1FLz4c4SxtWz3LdkTY6Dg1jEmTK8th"
    "JRNHHJSP0PQA3YJjbCdhLZFLQTA0wF2oaCbmRBHw7cDwXwqDRg5UIIJpSUm4z3Hg7m3hritMiygNMLAxpirsP5bcFHtFyXDGC87i"
    "dW3lOKnFghrLFDxgJ4ZcRq69fAKvWfEZLC4aztvO6t6iiH7kyYhIrbFWkROfwC3GC03IxgcRLXOAQEiwJq7gkXhKeMeTOcsM0LGz"
    "MMfHphFe4Z73+mLDKq4oDdhITT+Jdnz0lVsMKMPdBfIYb2Wk4QtQhGG/NGKLiRCPTaSBMCeMwNtXT/ZgpTE6fYp7aCaTi3kA5INU"
    "O7dv1HF7qhR1Ixc+j4McrNL7/oiQ/DTl0sJ6WjRk4k6VJouQvKjiSeLhuBAJGS6+gk5KXEP2Olz/e8nest29B2GRP/0wWORD13UT"
    "sMiq4MrDIjM4QA4W+QNAkZ87JJcmakS0gp+S6LIdEbmTkL42j4gMLGYKEllfJZjI6M88jYp8swUU+eAGLcF5TOQFJZChXfudQJHz"
    "mMjL74KJjM7HFQK2Y27YRXX72+Z7ICK/clsBkbsPQERu7wCIbBAvJREU9B/4pKAhoyMQCNVjKGQJM+IMSUhr9TQecp0DRL79fYON"
    "wk6va83+sQUReSsg8ghZGPqPfhZQuWuKESRyPcZE5sR0b0s8eW6wgKT+oNW0/YZpLRAWSSwQDTaAVwiULm7/MQ+SXN1+A/1BLYIy"
    "oqq5pkljPpggJU+PxiMll+kYoNOaFz8ezGT3BDLZv9H+1cx4a+esKJ7iJv/pj4ycjM4odIJyLVn4ZAue7MpiaEyrBKOXB1C+QfJo"
    "Lxg9uagNfjLepAfSn3YMyiHZ3DHDWQlXWhqAEvaNBVDu0cBPaxb1GjgWXYGBLNFVjKYdloyyuwh4Mv0uO5rM0FWP0oxEUcDW+bpu"
    "L9sAouxizW21kTxofvw3e0pR5R6N0UMpk9OIYXKagaRGKRCu7hWR5h62SzrkluiWDW/LgKjsAqLyVdlvOHPJ9eAIJrYsZFj/8vGV"
    "YYY/AF+5TrFtt30eIyzLp2bd+opIQaA8tyEsL3ZALN+QQbL+HijLi50wyyiQF2uUjWALd7nG7gywXLs8xLLrzIFwhcLyDYd2AAPB"
    "RMKMslyrZD1ajHjjfCDQcs3OjruBlhfIecnMX3vw4bvALFuUZdb01OSlyrUhMfDjztZshlTOK8JZRs4buQzV8RTYG3ADXDszQTvw"
    "lbeO8C7oyjcWXfnrhkBaiSHcAV+Zw1jrD4BXDjQjZ7+YVHdiKwPrXg4LDNcGFtuh5CeH8sbCKzfeOH0D9F+D1HLWtXOGVu7XcFIB"
    "U9U1EjwbdICGM+xbqGgMkJvgK6OocpO0n1JTDldZ9yMQBVAt7UnT2jZM5WQnwyKTAqjhQPodgMoHXr66yReU2Q1oym2xgVPQBZDj"
    "g9t/vP16SU46ziT41NkN3G4CSTnCUW415QBIl3p+c0t4RSMhE9NpDY7glMdrmWlthKUcVQt0BZRe8XWOAhh2gSof4naibsxvf9/D"
    "ObnkWyie2vU0tnK9DVx5Nze2sMrnLohhHljZMYKMuUR9DDW6CFl58eeFViYvNNR/lCJ0WITlkgCW/zz4yvVWhGU5ZKjY9wVZrgPK"
    "cu2+F8xy/ZfEWT5AVOTlFNBy9qUHWmZ670R3WfrCsOeW2U+zgMv4aAvgco2Ru7df067RHEETkMue8hPQZfM1yazi5V9vw13+xVCx"
    "PbTOIi/L6zsjL7O8tRt3OeyRf1bwZdiv/z+HX+7+LODLrCzgxG1j9OVTd9mN0Zc/7ci0koIv1znw5eftqxzw8ulW4OWq/t7Iy2e3"
    "v+/gj/ID0JeZhP/C8MsgW0c76I4YzO2HQTC32xCYm10IzM1/dQjM0OUcAjMFeRbz8lUKv3xY9lVxXS5uv83BL4fPPPbyu19RI6S/"
    "atzmbtjL7d2glzPIy0dml+6GXuY84M008HLzQcDL23CXqwC8HHCXS4u7TJo1UsvQqWZgBz8IfflmG/iyauG3oi9jIeoCyPyKvwwX"
    "DLzFw9V20xK0agBhBlLYjsKMdsZMMFweh1lEhhEOs9F21duxmJ9Wr0pBYkbpnkT2r3tUf/4QWMzUv2ks5vi1IJ/e/iPcjbtiiMxl"
    "3wGP+SYLx/y4RYMS+3Kra+myzcIxm6taBo75pWWvOUxmF80mevRnYZlbk2EmC8vcIiwzEtiSUJn97bF3QYlVAAcXXcoUJnO4/A9N"
    "CstMEvsNqaEJl5n1m5PAzEwz8uF3gWVudsIyA/PjrcSXR5lLhWWuSEksuMwBlrkxQBvIcydxmY0ipO1HA7kLNrMh0h8WndmpqoxR"
    "csK9MNrKhjQ/Bp7yzauy1kHzXNBdu8tCNHPXMwDNh8Pt13dEaMY6cvjMtPW+K0Bzo8YWGStCNMMfFMWK1hiLHwzfOi2eR2r+0x+V"
    "/aRYzWbyPinOYc9Ke6wlCLp9ViC4SC9hrmlj0GZoUujCRygN7jpCbY7aZtRmQjxdVzAStN813xW1eTx7s+LgLrNX/OmPdwRwvtkK"
    "4Gz1ZOz6wGeQjxpi7Zfp9i4QZ2Guu0CcqZkciHPFAgkxjzvjODPDCWjOTTmCrfUgzkHLxE0gjjNyarxhbwNyZkXUNihnF1v6/zJo"
    "zgHMuf7B0JynqEJEOtlHCZgze30QcyY053oSzRndrb7CUFwfMvovBtT5ZhLTGUXGRyQKbkF19sKnSIxjXGfOnJTDdWYeRgal7wrs"
    "XP0ZgJ3RN9h9MK6zF5BwIy+UZcoOyUI7E/+jjUhocgPrfOOt+aGIz0y1ogDfjvh8gDQ5++54z7D0VZkFegaSv/3tDqDntEBAHVhP"
    "wDyLjmYK5bnL+eRsw3jWD5rMFzSMQwF4Zsy0xabMojyv1mR0Yt9ztwXnOS0ofgCTNp4R2rPxJNuG9sy7Ci2E6vgKuwN5WIr2fCKP"
    "DdxzV94YsOdyG9Qz2jMwlIs9IbJt/QvBe34rCv4pwGc4FocRxrJCPmdfxqDP9QeiPt8B9Hkn5vO8U3GwytQZ4z7Puw8GfuZRA2PC"
    "Mh6wYwT8zPI1yHQE+2xvNhHqs6OEk39R0OejuuKAzfz0GJhZX3Ir6rPYD2p72UfHnBx1ZMCf7wj9TEY+lOlhd4Ekgru4kj3aepG+"
    "nUB/pqXaDf4sxYbme2I/o5JxiB0+/FzH3g5j/GeXwX9uCuuNM/QDcx9xtHL9Gp0G53wLiqqqR1jQN+SQjx4W3miUB4OGtzQR1yTN"
    "AiMOSNA955VCyEJWOMVo0Fdhc7SIBV2OkaDZ+gtMf12ZXZoBgh7LnpQWo5DttRnMxN4gSVy6mBBJ2mBSzGJAy20vtxUSAOgj9NcW"
    "/0tWXZq2K8mKjuoo63K4FQn6Q2oUrrMFE/pPf0y2K0wIfslLEbSJsi/vCgxtq/XwYbtqvhM69PcCh37ifU/G6NBlHhya/B7L3sGS"
    "jyGia8TSncKHNq4IrMbyA6BNuBUkmkWXMU60244T/dyRJqETfyv1YA1A0bDzjTyRwYkuYxchco4U1sFevYswH0ZZUsZkiNqOgKl8"
    "6jYwKa8TtGi6pAtPSurtkXtdo06LlWE6zSO86AEBoxOYyqQu9V5G2XSNY+iRR6FvbnLa53GjxduWu4Cudjr9e8kgx8DRwm1QlhvI"
    "na2vLGh0G1yTQxEPGv1qEjQ6M1zt3PRAt2FGn9iVQxm7fItgnvE0tqGhrcDR4q3jlj6ih0KqBWb2T3/UMaNvRLWMyWYbcvRbMr6N"
    "kaNPkovaMkJTIfjoinGKe0raQwFcxglflVRdjTdIjk7tw+MGZxH9PZuAGU0Sxe03Xu0meHG3v50VL1DEGxq/xxQ3moCjmxFwtPWu"
    "whQdChwdJAnU9RO/LBLd3XlFVMN+3vb4t4uN57aOJJmWPRxR7V+jYkbd7Nmfry0ib0vGW8ZcPJicCe8y0yDSmTXxQNJ2armhe7pA"
    "fnWWktvhPpPwYlA/SYGSHjkPsvsmygUWVdrDSItDZvkx7sCm3cuO7NvSDA0Okjg2oDYT+V1QpI+aPIp05BctCU5IA7QTSXrhApL0"
    "IgMlHe1qunyiEx5IcBZL2jGUtHgpksZ0F5b03TZ4chrobr+hQIw7gEl/XDgv5sBqGbEmuaBtBZTWfqWQ0kEMuBOmtNsFKU069g22"
    "yqnsKMB7N6b0wuUxpTnEDHOQsIWnZQuPcBPC1+ow4qAdwUtPixwjiGm5f7mmBnJL8KVPIi/h4zMSkmOIaSI/E78zgplO10qjNALQ"
    "tPpJj460fFsfeo7vRp3m7fbdYae3fG9wp2OX2i2405N3pz1OyMtOEEGUS9CnaUs2rR4rFW/LOsGhphSHF7ff9kqgE1DUY/JJwKjF"
    "t2UCjXobFnWzHYvafRgWddt9Byjq9KM8EvUiC0WtPp95LGreVlks6j/9caTz4CayeNTmHGvMHWrpXpWR3MICejuK1TE0l4tacnD5"
    "Zzv2hwBUuzxCdeir7xaep+QNI+hZRvogpmIN+2wt3WOljnksfimcfWDtQCrNA1afRDVH4N1exCbQ6lmxq6c/QLcOU0IpU1ccxfjq"
    "iRf2OfDqX4gZf6Ko6DlQfJjniNXAVxvwar1x2GyUQj0wwDikIINfTX0SSSxqNYtgjb4iceHvAWDdsjtIE4AG2k4E4wng6u2BDCY+"
    "YQLF+iRRT92U5rTDmkVt0Xgk62YbkrVRYKhZJAGyPm44VnICylrGE++gxdD1u2CsKV5O8HBQ3v4B0azXH4Rlvd6NZL3O41izXW0C"
    "xfoXTBjJy5xlLbasp/jVZGK7A341FJqqyUL2PgF5kLLPMutYyGRNolh/GIi1+4uhWB8J69wCYy2TnKvFoljXlYHN1e3xst8NYX3I"
    "9z/1BY23QRbCWi6SXeaanwWxfu4P04z4PsaxbjPVeRBrqas1ziB3gLCOhrITwlodX/IQ1m2X6V8OwzpbcGRXLj8Aw7qdhLD2+6Gs"
    "J1Gsn/s0w/uTQNZXCFA4ArLm8LduO4g1npbj8QYQa7x3j0Csn48+CDDWz8M5mgGyfm4tWd8JyprsEuEU24FjLTC3sQVtAs76bmDW"
    "wQEjY5ubRLTWg1FVDuJliYjW5IlxP7Mrc5DWJq0GRf8lSNbybWtjH8dOkui6VrG6DhNadrDPchDW023VCl1Nd+Hv0ZiFrT733Sen"
    "jSxsdWt0ZXEpi0Z97kJQ6BbM6pZVFGlBiQawcNWUuqRmpdhi433DjSFyjFnNhgKfNkISnhgP220LbuCrYzm+UZZ/+1tTuam1b1kS"
    "4xpYV9G7S7T99YPm0p8Asf7TH3XDx9S0HcMaBQTEsPY4lK0HsOZbxlYI63h4lEcDv8kcGGa8pGnrrZo6uLtw9EHZLd1WHOvyTjDW"
    "1U4c6+pOMNYa57AdxzpXKgKyvv3HLUjWY/hqtpdZpbNNYOK3kQjCQOBTGNYno/wfYrfGrPuYPA0d2ZZlrvqSzPe2D4YiJrCsA5L1"
    "8vsjWY/cbkdY1i0nVqwnwazjiKZdSNYgVN8ByTrbnIGy5k3NzhgGzfpVm1H3xnDWR6RQjNxbs3DWcPCv1W1yG5z1uFwKZ32qp9od"
    "4KybiBYuWALeBW4tguAucGuVAH8YcOu7uFfm8K3jMyrWP9V/DohrPMUQ4topo48sOTKaPoK5ZnUyXpQ5In5okLxWrc9BsAPjGu3n"
    "dwG5pghwA01dux8S6NrWlmhbAziH15Ezw8yBXeewrvEUwRGWI6zrc6dKj3Ia9TrWtPTunx/4OmILu4Gv/Z4eGsleSge0zZBDf3jA"
    "SDi8kU1OIl8H35ZJ5OsTkl8E/Zr8KiIA7EZ30NSJxnaPWrnmFqb5XTGw2ztgYN8EDGzq/l0QsBcRhzMI2E2qxV13g5uXBgJbPFIo"
    "T1LLCNjI6gaJ158Vh5z7hJxGwj4nu/Aem0ZW9vCaAsFOZMrIeyYz4QyMbWbdKLinlmEbOrbGSTQgJKGEm2sTtffz2k3hY7PZ3JGr"
    "Q0pGeIP2xqu6DPZnvuFMgGQHN3gJSfSTmMHIPiefBF9imi/FANmtBKRnz7g8PjZJIBP42HeJSMr0yWBkP8Wp2gKSHZPyDw+SXU1h"
    "ZKMcN4GRHfUpxsiuUXdZG4xsCZBhgaWfRMmGBd+Ckr0VItvthMgOkY6Y61x8bDqOwJrGySbVyGYQV/8RTDZ5c5gstJ7pJDjZBqjr"
    "uiJcL+uWaj1M0IQ0lYnNpCG78fZ3UgMgAap0FfwcR3whi5VdY5r8bQMJaNknbQyX7UMg9PTmfGqaynKi2hxots+SeAfc7KEh6Gwu"
    "S9DZG4+cjW6/XTS55E8c3TYmgLNDIUbNbjOo2WeUclePP4OdTWndLFzyMnWvopB7xdB+1XKsI+U6E+fDkMphDKL9BZnq6e9dSNoU"
    "qRkiUzJA2kAvJkkhBrDKARClq5xA1I6ivNfiMCGKEt9Grc4F3OO7Q2uvo/n9YHhtIMGdNagwFouTd2w+gtlWfjUC2e7HIUFbgLZH"
    "pCMiGfCqV4TA51dxF+x2uxN2+5X7M6Fu2x2X5LH1kNRNAr/dMPz2KsXf5jxh+DyPv82kSll5GwHghuOT07AuzceI5kCqFAqxxUy8"
    "ErnOigAW5jBN5CW6X7IBU+SdDBw3bEEjvuQhuem0oA0WRe2G5LUpPLdhzCkq91kyf3lobl/K17dvT4EsQPeJzZHp4CqA/sSNyfCA"
    "Tk9OLeGxP9QIp/u5SUPSR/kuxlDdqIwLykZaniQNh+Ku1SXzy34E1803b8w8XL5FyG5ytVRvWvwGtbgoPxNbp0TBxhcdNalVs8Qk"
    "9HQZchqrKslWODYbJrJEa1OJ+ShfEUM1kN3BQ440xw0p5sIkzIqXprh3dl0MDOA9wu8eJvG7VXcZA3jTJJKK2+R/2YriTeaoUDiD"
    "5C3+QjkgbxviEnQEO5C8X90JyZsA9nyyiBjJWwJftuF4L6KEHDY1C9MRxYBonpoJnnSPnPu2IHlz6Oe0ZDKC8iYVo8B5O3Zu31FH"
    "DOndeEhvCmDdiugtDsukTsAES94UptlcfIJwIWw7Y7h3pAJC7yb/pAjg2zHAd7MD1zvECI5gvWNQb9oHnLiUWnglKBrpJO2LWDKF"
    "7p3J1ssI3xx09kzwvc+8zzr5RTSBefMz5ghTcN870L65zYzHTUppaW0j0O8aUwl1qglYCup7Mzpq1NrLvKkzdlKcAIL+bsbQ3+LT"
    "IBu4mfbumQQCR/4G1Ian4vSot+CC7/omQgk/mpxWHyQeK88sbnhiQGxtSN4EfHjDOcMVIrzsR44ZdIBrUG0mgFFi26dxxMfQ3aRM"
    "uv2WHYuBD5Z0DQubJUIRT0DEyR53Y7M/i9B6gc75+2FTBSjxI320FU+cTIy8OYMbJ2ndCVvc3QVYfHr1Ypjxk9z+8DlqcDzBwDWF"
    "M77ciTNud2HuiwzaOKeoVY2CNTNMIY67uyKOn4SqYQNL1gCGHV9UoxtDZNErbCsDOwWsYAdY7PE8T1zH6OPsitsS9Dhp7jiLMsIS"
    "BPTx1iopQgdzAOTKn9nEzMKj+HpeTajZAnyDXR6LEG5s0kgFsY2U0ijjNc/gk1eiXKyuNQNtiZmwFRV0BFF+MkUXCVD50ZZRwMZI"
    "Bp0HLJfTpt4FWS5+qUZFqjpJg1h+wtinVGeKWY7sWSHLQbye1yZ3nIUt9wpedUSYxC4/HGfRj2HLP/WXhYViKGVwy8kBQoDCTXL+"
    "PGq5hywnPpTJ40/xaD3Hml5RsAennaIGmm0g5VJZFp/8HMSt6o7g5LHergZ6vhtC+RLWYhnHR1hp7M+CUe58UuUMSvnXOZTyJxXC"
    "GaN78HfEKg9JC5Ok+5OA5W4HYHm5Fa/c3RWvPNedKbjyRYJXfie08nwOtxxiuU+QZFOVxq7/HLaJbBj2wXYI86PkCntvKTfEPmSk"
    "gHsRR9py9VshzCOYD70hRFctuU6gxXPxF0EwT+h4jGEud5agsah/MBzzoHy7iRMebwEzdzvAzMe7LAdprpdPCW7wMu8WUPMzg6Wh"
    "QXyavMhWERzlTE7PDKb52R3a/56o5gpjF+qfgDU/w+FId/fG+CImRHeOd38M6pQ0HmjdncQ1t9VyROwF3q8yNnqLkYHUJrCjbjvA"
    "uVnFaYTzF7jPSSQSTxZ/0GeAzfFE1eOEBlt7lJ8YsCQDbU62rBGyuYiKMcA5U1EO4JyN36OIxAjkXGjQLmqKci45+Hp/G8zhncsl"
    "SgrROsAIFlu7oMjnh+gzgNIo0CQmSa8WbQ4GPU68kQNDH/XOd2zcfYuKHmwl2OcxMron3u+HjN74ujWN2XZo9ISYp7DReYSkH+Ix"
    "ToKk00pOFMzDpSddvgteepjCbYDpAcSlmlggi5h+rmSFA1iWO0DTyzthpldNoPpJ0HSX43p3RE0nFDnYweLwUGP84NwxAp/ApjsL"
    "m86dlkh6jyOCJ3tNKpWAnp7FTsd5DzvkAwHUnQHh+68bQ529qGsPoh5b4/e8MXePk17VAUr9xUAsSP3GQ/rlUTT7NJ76djj1c68R"
    "JIt7jKh+ALzv6z5GVD+H0VQSdhRBqoc7nQqdY0x1/7HcveZ1C2RWmvQZxqHKn6C9HspjcPUXUA3JcCi1Qc3XEsAzDbM+8srIoay3"
    "Y4j1Fybt2Qhj/UWkcxojrKOLMaa8tQDr/wL8OhgblF0taoJZJx1IK7p8tF2NoNbPIsy13QsallGx1jGp86nAkPUWcp2WJgZcr+50"
    "hm8BXzfQ6xJxFwRY66yIGRwEf4syQ6ClcNFV89JPfYS/vmBMAlIkSUYED8EuJhzBX297n9KlFOJmQ1MQQSmGWyuJENjr228vXc1O"
    "MVsS4u1NJNKbFZ8BEQxNO4HETlqQG4VLNfi/U+jrIWsOo6/7nCLsPJFK1jWDry/dlqSBBoD9xgKwJ02lGOxMC0GFP2U6mQZif/UB"
    "QOyUEVCjZFecZzWGZA+J+DwWuwbNiJPtfojBENsaBeuMbSrbsvx5MPazrBpyP6gd91RlfBMxDOOSGGGzxy4K+5Jw0PojCICvtBtB"
    "tLccH6Kx+6xIJVeYAPE3K77AxA4I8stGCxd4z8JjtbtO3K52+ZchXPvPc3DtB/M55eBtxnjt54urunK3/8m+C5l2DwbgXoSGlgFt"
    "/+XQ3f5h8TqH2n5Swid3g2w/6hqQJOiCNsRdFL3o+dpV8KJrJqHbXzZz97psmD7dFR9xMXb7ddtNQLfrmwS5fVhNwbZDb90W4PZP"
    "6Xczgd3Oe+rBY9fRoFLc9vP1ULtmBNv+pBsw0UEC2n6OWWaAxl+PAduPYEdvXF0PzaWvzsK2H3UX5Cu4KQ6Gi5XrXvfl6rWrNnnw"
    "9qi24vZ3FxeNa7Ig7vVSW8yiuPPibIFxP+ou3RxkJ+AAsqR3xHC/KjdFUy6uCLu9gAPyalNcOjjV3qA3/OZjTMv8hwu0AlVBiNgr"
    "5g6XH5+hT0NCiZOg7kuqA1cK5Rdg3D2mBYTGuV0HJVEXfHFBMzFCdv+y6pZw4IaT5ZLudG6zA9+9vv31cLEp0AZfwRerKN/OE9RZ"
    "xMju0A9XfAmL+9YNl69vf7e+QGvvskCzLNwEXze3f1jjlFxTwAQOBzYB1H8Fqwszc4EOL+jIBQOrVsWLch4hvNOZD/PEnYEbMGn/"
    "lsVbV11utkO780D2i/ONG3Cr4PxjU1HmNuzpteklFsoOadS3WfEEu9TRY+rOXvGm7EMMBrzd5JDdvyw72PZv37gKP90B6A4yx6a4"
    "uP1DV7zCmyAfow/OYRM5pADoMTZPfqBLFMOBCr0R+TWN4/Pb38F1bHGFG2/PfjP0bwdhu4Tge1XW8wIeVHM1YyIIIFRr5tT3eo9c"
    "84ACYQkx4Kp8vamu0eaznMHMNTLblZfypMswi9K7B0/gpGwviSzMeKFXcN2Dm5GDfYN7ZHH1BilkwwTAs42dYhpaURsR59grwsbB"
    "XoH8IM9OYefOnZbcIwp90bWL143j+aMPld0JwQq0+xy4BdEG/PemIlEUplK7OsJ2N/t2G6w7NvGI+7od1h0LviNGJJw7C+uuUtMa"
    "uEKFafHuiOgef+e2fuiVNqHEgzP5jhkTTDrKMz3erLZhuYdirsnCuVvm9wa5GQjkyAQmsNxtcduHCRz3Jwl7fd3i0e6ZOrVUvEEQ"
    "yGYKz13HjX9eoTNKPBgD6e6Z8Cu3ebspuHIkOQQx8Xtk6zoUcGzA4UHkG7fhtf70EXeZ9kfABLMd3IwB3fnb21+j7yEfv/bg6FU0"
    "SwHdD0aF9ote5CjasAVW5p/gqf4fQxNL55mlUFDPe5LcvxpPlS6SCxJ+celYUNjg8bjHn/a98cPwk5rBeR8PWyZv+tjMwL3Hi0+r"
    "eu7kUMMVHrYjveeoPMi121DecwJBhz/dJovz/qmbywknMxxLXLheB5QK2xXHV51REGDVNK7XNabC4jrK4aJA3RKdHiVJRXQK+qMD"
    "69AT/wo1lmUzAf3OB5VfMe3EBdSOG/FyswX+3bbCW7jJ7uEtOPDhvICrIe7HLawgjwV/iqugo7AcOo8ED9R4dfvrehN9Avdud6kS"
    "CK9RSNo/nv4liK20BhEfvQNQPMqwtl0Y4AokareZwe07SK+4EX/e4s01Sywf2J0USf7noQPoUA6E/HZQEe8pIQg3ExjyzEGMfIFC"
    "dNHigVzf/q5Hidq/45r2ChC3hM/SgN+iNuPK9E7z7X7AkWBB5Q9gRpj0af9iyyf0PZ3aAihPSwrjXIk45joQpXqyKqEIsZmElXfd"
    "JKo8jHkaVB6Y3l5xAjdN6CVwxsMr9AregzVdsX8Gz9lfnQ7wd7cNU15m7cIvywhSHgWr4mnZzV2mVIQpf4DLQCWb74omT1Xogyqq"
    "xzsyfKbnZDeFJE+1ZItFGPK6RbphvdazPYciL+XwUVpMYOSHC2gK9d7LMY78wTz3zsPI//JNxXRdhkpYePDfAVUurnpXN3kwefYg"
    "Y1V32bx1on8fw8nf/serBqkTqZeWaRJM/pdE8EjrQS5lMVsEdaaHclXc/trXyUfiNKg8f6P7OAMrL1SfKRHhyn/q12ufed02bHlb"
    "WPfLNnB5W/7znfjytnSW3izE/LnSz36B+3cLxLwp+fkukHlTdroHFmbefPCczuA3yAEnYOZNYeBl8w5v66j8/DT/VQQ5b76ljhWn"
    "w+YtHDDbcOfNNzUK05MfKfi8+QAPKCFPUnZhkY0bA9Gfw62z7N5moOjLYQxF/6Wrbv/TGIl+kwGif0Y/Mjj0n7p6Psag/xQO5GaE"
    "Qf+4tr3wGPRfVCB2bTZ3hKB/DEPJAdC7q+4CdmF1OQFAr5fVKfx5L/9k4Ofx1LdbbAp9Pmhae0vdefR5q5aNyDuHPg/tgxRMNLoF"
    "gj4uZXHo+USfBqK//cO8o6kbodCzrJMDoeeT+QeAoX879CUe7gkM/aeuo5uB6s4SMPqnsLfIGSkDRZ9+ul+0iP7qWAmKqPRemz4F"
    "SB90rNNQ9MmsBSD6g+x+3QFJ/ynfn3AVpyDpj8MC78Cl/+WAJIWc7Y3egrPY9FLOX0f3UffJLQSBtFeR95rcSFCuX9KdUcQHKtIH"
    "41cepJ5NA6T7RdXVJgdV/4WYG17MJgsyXD3rv4B7or4SDnS8DeOCv2WrC8jNPavYgBAauiXL2jNu/Yvy0syJxa3/5UDcmSoIXcDY"
    "tNeilJnArZe3MXC96PFYExpvpQi2Xg4dkrxRvP2yhA4ifaHW/Yr3hkGv9yFq12GxEgz7L0gHWbl5eJMi2avENwKz969x2uDsuYpq"
    "WQa2kC483JebtwMM9jKUV8/hgxqTtMQkoNMaSkfg9n6R+2W5gcuQEZ8svP2xuXEG80sKcG/4dwRvzyOhE1YnnvQxKbj9F0FIKNAL"
    "eDUFcL/aK1ZwGhEFWYB7umTNXbUqvM0u0vdNId0H9QddPqmJt+VVzeRRPCQd79Xt71hS7RXmHUuPse6RtcGTS7qnU1WkrqidWbEY"
    "8R7Hzcr1pVnqeIoi1PtTOMxboszxZ36eadb3ivaqcUHvDdfbGq4GH8OYaMPQeJHFy/tkOLkpwrps0zpIqGqPdhdPl8yRhZOXUF/4"
    "p3qbo2OM14jKzB1K/SBKNRb4PmBvQhn7QmaHzVt1by60fj4i3YlRQH6sKIGoISS1QHVF6gD4/gI5RGMHwhDnn41HoMD3pAElCvIt"
    "j8qEuX1KddDkPqK5+/FD5fu4mDCxq7LmCfO9GB49FmBLC/Su5qpNdKagwhcXehUsV+36grSsLx99zBvGMDOvq4AKvJkO+dSlQ/aw"
    "iWDsPUeTXKf3iPnej3VUgRd+UnhNSmzDKYee5orUI8GoUprrqU6J3FKjbhDHPHWDL8VmEeqS7Yqhuk+Kv0O72dxdwvmF50Jdz0Zg"
    "9t9/fmcgIX3g/BZPgYlelFc4X6MeMe3Z6vC+jx8SiXlI+yaSkqSnbwbSUDVBKcmWfWh6jnx3FsGGN8aAROXGb41ozDXZLgieOsn2"
    "nrer0pBvaE3xN8WXrZw4Cqod0v2Rk8KmAAGrQtEDNzVbYFv2XfAw3OKlbvRtrItDZqUtwa4SYxkOs1yvSeMLX6n+7l152b43rw40"
    "a4rV1wVrXD3T2JLETFdzEnvxkBh6+8bAevtrhlfqPYl0JpaGYdQPWC1XWo8YhVEjfwnbGavL0VTeTaKPLufAABdXdYs8D5rjBTQk"
    "oC46T+jPvuitq45BQO9pQGxp2LwxoO7lRkgAWIzmDOvadPVsAsf8K6GylFBU7vnUyrHyLvKWMZ+AbApysLSGwvYjlFQzBaRN9c5R"
    "cTbQ/4JROlzVx1j3eIPGRPidUXoYnPtwe3sQNYxhiXqG45hqOpnCuR43cuYTt4aNlZnarvTJCf1btLSfL66aagMihuhJxpuQZl7S"
    "lI7kMtzDr8jSTcp12V8/lUr2CrRgUL6Jt3T3gWsqHHWDo0uZoZszzUJ8wr0QXoTsVK52urEMOr1iexwxpVncet5aRpqK3wsWwFM4"
    "TCpktpcuhifxgB7l4Lr4jcE2eOzI5pc0LdAmMK+i2WJ0dzVqkD9IoljiEt4pynNaN+0aNfrEsF/9rJn6jMb2OQmm5AbHT8ktj9Pq"
    "sfeR+CmlBTQjEhfCJULzWhdbx4CjMNmGzydc+aKXUjfsGiCYVdHc/lpUwmTJbRKWR1/2A/pb4vsKDk7vK4dX9ktKIFXBGf3v4HBv"
    "bn+3IQecSwfHfl3jU1YqYNlwYRg1iocC3zc9sijl5YpB0ilicYSP7gIiPYPTO0PJcZHzK82KKMYRD2wP3PxKkkLFDkemEKo6nl0Q"
    "bjxBMGMGiAQCHYuc0lyNXgH1HIWe4lHpJnq7dBflUG9OWRcdvAEz709DgRSMHd6q7C4lGlZlBzR40XZr4vzVHE+mJjrrGESd9uI7"
    "ZIXiAiOZUDkHxlxtwwYVVnCrjbCNxEbZb8iKjavYivdOMhMsNsbVHRA1/KiI6QFefLbR5zFRwKujr/jdFFF4jEWdQH/7GBWS0ci6"
    "58rRPV8gnfQG3nsKyX4Cl6incqvgL9S+CeLpMltSnVgqkS1HRkyWabEWll6sIideUZoZbvbtQB+PV13J5yjYiEndJzTg0dtyFQyb"
    "Vo7C44aYl/UWeSAzLv41jR/zjG4J/dhppABmcYU6zA0pQZth8xZFTjwp6LZyFjx1lsZtHdbgjb8X0tUWOCZfedAld0M+LuRmKHYy"
    "i5YL7Q9lrVfkQUgV+Fe/rlx9VV5AuwcNOkxu9uVG1UQGOKZ6tNqQwHsF0wkj/EJVmPTeu+/TNXjpBcNOdAfsHkgS8yyiiFS+lM/g"
    "OhO2HM+7Vkjbiu4vb25/fVVbh4GgsfAujg0R7yzeUkQ1UX3+Rq6lxHdWM+x9WXbkQohXzKWqj2l0Gd9O9n8Qv9i4PuI0O+tjfmSr"
    "0etcbh+rqyGu0dXt7zjpJ1bx4JdE0cHRySAV6kb+ZFR5QOUMxe/WBLEK8daJGiC0183N2nAp+Mu+eBx5lsCOLe6dHJw++LxdDpSA"
    "lYGJl+TJg4cnu/R40OCe+qsbSg4IemVCfM/4p4eyL9fVzx2K+wdnxw8wouD2D1BnnX55xrkx/RLx5rXQ8HJ9jOvlz2Q7pXDt7Ham"
    "wNke7Re5Cuz5enR6y75cFSq8zFkwcY3F0qU+sTBrtqbM1V5hp4dWVCdE7OyGDHmMBm/+1KFP+mtMqGYGzl7TxTPUFka1s7Ki7H0T"
    "dAuP59l7whX3SPRHDzFf+f0Qh2o8AKMKVUuxKjC6ftiIdzH5SRcN8Lnr1i/azE4TzjtJpeL7qC5sAch8NPzR+rHfcxjMrDC6Tgzh"
    "oi7CBn+DzsuhZnFphb5TiZ8+FLfyPZIrHgtTLh797MezR//mp7NHs5883P8JakRz0xH14E4TYroys3Dfp45R0wIFoFtXNN8t39ya"
    "dBVRIVC7q0DFBsGbq0VMbHYu5Nt+RwqaedntF8cUUxZaJZ9D8YLefBIz7ResqfhRpC+zZ4lTPTBMo9TY2FnRRog42WQGU84WtQq9"
    "lvD87kqU+xtySNy0K3TehrNJNF37xVEnbJkHg+tb42rESrxLt8S2NjiLM/ITF1Wfbl86nlBZTH1BQTIo8HHW4YADhloOBZ/pxrFt"
    "T0cTNRiOZ3GXX5ZG+pAciNHyq3ecTooKEjTOPfpHd8aV+Fvy8r0d+ttfb96iuIZO+w362uE5zOTiBZ0lgvHV0cH7mvPXySJJNjuR"
    "oVT1xg0Nnc54cY9XhoyEz9GEiCvk7svGWpq4mAfH0MolA0DQWEM4InDPQFZIih9Lz9/AOixdtuc8Ko5lSII8uGcmdENJfz5sNmzU"
    "SmHta9Z343PP7cVLEAW64iOM5Mo4vNtNymn1eyK3Xw6XcO70mCMnxopPtrG/y6pkgejyTUNOevvFC5zL4CLKbM9EYlZNZlN/jx1N"
    "/Ajuzf5o98KBiEeiiSEh+uPiDQlJuoULCdQiFblU3wdMepPlAquoGiqLOgfqLW00mLlLDtjw7tfwLUXPH589SIQKnk/vkWcmLi5B"
    "B/2zNZIdJmeghizvwDD0DbS5CX2lVASZJcTf55J57dNgZ9qfsjPNHceL2O+pO2zNCixvJKP4S2NkS7DXO39cRpNDK2h6Thcado7A"
    "7QsM/y3s5Nexj71dMLyyVDFVOEMQU+ecbfI7nfxumXM8IrnKejMHY83ou5FT0p0+blpVsVsf5XzJO9zQ9kaNiovSZkbbGD1jxFth"
    "BUfzG1ascSQZBmCiwgpZt0YF4C6eKY49oqQF6T+Qj74nJ3DSvIZnBh4K+9drxfreqq5Vc0EvfL6sUeAPJiN8r8V4cl4+EmcpEzsW"
    "zWFU9gXt6C+migcVCoGIU9JIJ14h18nLhcKriyksuMUGvHLyuJW7aPRCI/RsxbgoXPSTuGyKbY9UHi5gfOTYMBZvJ6CSxgOfvByC"
    "MTRElxG1S+MRhrz2MzQn4sul68qli4qm3dQTlKAl+426nhDl9J51N97IKpLFnpGEocAe6++xn3hmXSI3b0h6so2flWIq8SdcMkt4"
    "JCF+NLltFNOd/GG7dag08qJrN29x4wFrNk5FI6qhj4Ry/DdlSkKiG2G2UWZoEwuIKi0MNRDKF1MEEtEd792IQvkEA7GeOiQnJX0h"
    "sdqx+6FGGfVojxGlByPc++ABdWdXhyh5H41QY3nRReftoLq4mS1NgRtboz06jt8wX21gVhrJRG6VWkZxpqJ5uyF38j2VRT0pkBXg"
    "qhNhVoHc1UqDdHgBNyQ4zrpqE9l4JP32MQWOXts3DUvhaugWYk5LkX+haGNlSyITRCHZFrta4ea9el9cYfJ+yQng39LL8ePE+kTq"
    "3dgdNS4arPrGXpWWsGckl4rNZdYOV7xbxq2wJY50gcmrjBEuGNbDihhL3H5ahRrjyDwv5rjCpkswWPIBRxxvknaCUHqEt9HYOZ/k"
    "00ABxgQ/xqh//vL09Pj0UyWczbjE2fOjs4PnR+x1yWTK3uhJufOT40OuaXu5s4OX50ek/hp6r0OPSjw9Pj0+/8xPcKbAwfHJ0RNJ"
    "hcD2/9K6CeheGJ1NASQaNv4TsdbjxS0QvRpGDfB92b8Wn1NzQ6d7X5MUNEnERNqeK48xxVoKrDyVu8oFidEGZF7QccSejM1pOgjF"
    "re43CqXJhTrv2RKVEOqXiiL3FpmnFhG3/UZCCT7urhYw+2hcyNiV/YLpWPqh3rxkp+lsYooAG59QubhOGwIP+PNyHxEVyLvL9xHe"
    "NA2GruaX6OxLG3RVMoNQ+Hg2FptMk2ou9ojxAYpcrEfzwVYxMHK6bSbqImXPjmYJn5rMFVKhRbUXLAVj45RZZJH1DJYZxVYgmXjq"
    "FletZKHRK4Sc3LZyLsRoLcYkMWoMhn68RMv8RWWGnzZJrqdc2divwlro4i88okKyl6QCccegb4MPKwgzcOct7j1klR8eyPdnFsX+"
    "Mc+3XtQkqpE9xmT3yNmJ2RFuf70hx7s4GtQbaqyfHV7iLr0atZRrC/EbvmT2m33bkZdMFOOOsKZo/hfrC7zy9PslWTRT+oUSzSYp"
    "02QpHUoeLJdOcdW5qLjPZ2sdl1ZFXfYbjWIyKWiQfDvXLBPhHWUgDNkFsYS006pMIBTjDhU06yjAF/VSOJlMlbGCNRAQI5wI7qSK"
    "8W9Mvy+Ip31sqqK4d66fJb/FFaogyQu+ucL0LeTLHE7gfhYxjheRQ42SaGdZFjIsvpKZz/iuI24FOFHojRb8s4KuQoRuzjXgSUgW"
    "YD+qVEATwtDJ7UhNDukZhBpWqLb3ith+DSOn+wi51Iia9vXt75rGTnK5VIo4HncoOU6gLPBJJSDklTHlWIR4hi9VndgvQeSAqVgl"
    "r2cfPQyn4EcPyQsuLfIzU+Rn+SI3fEF6wjT5d+VVl5YoyVL2qevLFc7JqDu9ANSqFU5sAns2kQzqRTdEqO8wV/N7r3iG9Q7AplVd"
    "UyzQkyiji/gG9aIKn5f1Ms5WILptSxTeY1ZQqkPeBl/tOGuDoMiPAh4iRz8L4h7OaxdkEAV2JadX/fA1ppZrTH+mQrwMLK53JSYr"
    "Y74bi80BrY7IFbhBL3mhmjggiSe4a1d/186txXS4gMWkCBNXqRLYWZWUgdYmvCa42l8azO2hIXfLpZe2KKZBXS/TMkbgypTDvKf9"
    "eQB8eey16gZMwGLgIqkMHUaxg8C8ZCpQtpks1enIWzp5m/OW9ttgqz9nVGrslmlsHltdMy3kMjp4Mlex7thaUvj4a2vQsl7iAgR/"
    "VamrNnPkuL/oRCo2or+jPj0u69dO0pOgGQjJwAauXAIJVvUmJHthTQD7rQZ2zZ2bIZu4NDlH2JJ7MO/VuzWo131WBwEqNlkDrBQW"
    "Jw9Iysq0SzAnu7dt/yIQxOcpjrwtY8giV13Qyx77zGvKIO1x24/XR6s+RxNZZRgz3AzYFWJF3kdN7Kss+7HlIHjHEkhx6mwNTXve"
    "+tBdFbsuo7KGNwaX/n9bPMpQiaok/n7ipYzj73GOElImtvH4xjAOpq3RlFNBQUEM2z5OMJPYm0STVa2UfYYhkXUyop8ec9hWtUuK"
    "SIvnm9s/bN5qFqA1nDceU5IYMBPvPNi747NN42MiZhqZY0JaOcPg6dbMuK7wb5287Ie1gHJr75IC66ETlTn0V/r+HAHELjFkcDN0"
    "q+SDBZDuvPNR3fQXRzmGU6us1ZkYdrgt0j/ArEHEY/fQ5IXupI1eoGZosBfzNMeBXBLa2wFNutf2om/K/KLkWB7TM2FDR6nQKdM6"
    "+2h18WBibvv0xEqqPm9X6qqQaN686wJcwyjBI0fb9fMSJIqotbRKEXeOerVdkzFMhBAv5zAohfm25dBk60jvwh7nibFngKDGk+KS"
    "35rsjspjQv2cx/ZGW8BjEKYmESlOhUeOWvvMfz3Fx5rJoKSAZC8wHE8wXDV6oWj28dmLb0xyjOjMHHEILBxwaHyWCvNSJiwZG74S"
    "YeznsRCW79RFyDVnFDYXkUaOos8pZGYkbawYtPpzCoENcT780n0lWxqjgQ/Pvyj4gYYAEyyzTRfmugdpslaCtQQ5SRLOP5WfksiN"
    "dQmYa7wm2qqX/qNekct/IfEAXp8iBS4Fdx5apHRkuOnRsxfnbGPLyIVNuR8poRKP1kgWT/PjkYbGJIMbNDEoX/5FSBJTQcRFoSuL"
    "1xtFHsPAqk+3dTrOR4uQmb483jAeuyVmVIeZonzs1C1k6zJBdB2G02Wqap80YOZBfjUBgxebmpC70ndiwZCuXwKfaV633Ry9vMp6"
    "c1Gj0Zgd30/tZ2kK1ku+NfhjLyIzQp97c75p+ZpZdpQkAE+u0Wf36NZ/P3wlnP8lXZGFB2hkvvc0NJllIq8pThiATfhkAXv+Go0v"
    "LzRhRQJQz2ozdFIYUuz4cyVZOfltHLiNbSFhUgVJ9RXTKaPScQ5RJFYOyhSTZZP06Uhs88HZ0BOH9pVU6zo7lYmzTqo6zHhDcM4G"
    "VkVkcO8Ppxwh8Ds66Cc+PB0Z+nY19Tlzqx/R4fgGXd67GLQ+5J2WRU9eq47CkgWfyEqzr8W7SIgUaWE/qoN1qJo9IH4FlyoxGwBP"
    "exv4kLyet+Su9Rhz2cbw9aNkruFVkvxLMgQnAcy2mzyrEtaArjTKqt+0lOYLjVdrdRAK7XhkWrF8AtmsCIz0qUOW3vmslcA535pK"
    "qDjesiTWTkQtFk00028CZM8x7XoHsMj1HHUfPPiZx2K1mA9Yh40sODgxhRhuU9W5Jp0Os5W2xT78+F7q2jeq77iwiHw2seilo9H7"
    "u2dIE0FJkiXDccYraRYAy/kqFhJnOJ//JPSWSsnEvKB0F8uIqeg2W5bdxR51h3ojznsTiVE0XINTau7xOUy+k/gR+rn6kiRNIZeq"
    "2I/DO9yFkXOUG3QAR3uFuRsoMgCqPLyq1kWIqfX+dtctXAauWurDScmpVHlUXpIi5kuskgU5kxsGcyl0khMZz7vwzWWFIj1qPIgD"
    "snfjFyW8wzNwvzg74CL09uzgweFTvxrlTS8zbJ6wccU0XTUcvss1vFspNmrTPncr5Pmd52jhK3/goncdg9ij6d361XkE+zTyxdzi"
    "Zx7tfUPufPoq8RL/7PjsPJRU9kEZJjSiZZlIrAhQvVxyz/xcxhEwvoMbRv+WTDDJCSfajArVnD6dTsKyYoq8h5cRlb3uzywCrpFM"
    "yKQQZpJeP4vS9EeRUVo8lTUQs54Sq5zTVr1CXw90OOuuXXHvr+//f9y9a5sTVdY3/v7+FIGHmzt5rA7dgKf0ZHJz0FFHlBHFGXv6"
    "30kn1emSdBKSSgM2eS48cBQEFUUFB1E8jAfAw8ihRV/4TZ6nk25ezVf4r8M+VdWuJN0gejuXQ1eq9nHttddee+211y+QSsoi0El8"
    "4VesNxQiRBS5pRgXQ7Fv0nrU0BTBG6IUOFhOMxWBgI/HnhJNEEknKxiMQZJi0p2CVY/uFtLaIYP8c7AJrabRzVreIRjK6kyryeJz"
    "uyIJ+/40yXkF58QOEV5cwwkYlIQZDOUi2/N1K1rXms2hcJxWuhkhLEN4NUK4tA9t9+ouxvKS3uYBjSMKCWFCh9P4hv1oJDOFpb/c"
    "akiwKtB7MMg7LvAVvvwu9s8lN5xHHPjK6zG0u922Y4jUeRZVMqKShLGX7gq7Qk468vhPwd1jz22doHYx8KbwOlBZpoXCH84SuLhM"
    "q7Y366qTXHVwZGbRt7+JcdGDewg9uE3LlHmCN/nCnjT5TOkLAGqwJH69MSeH+D5aKRQ2zXRylhHBE9OmviHLkhc+kbVBEkRx53En"
    "wRcF5Y0ZW0huXFMclsfB2wONdOIJl+8E0hai0CjN/Hzx5/NemcNlSwSDPyY2qemArCuxgqINYi8INL9MigvmUEGTrv0GI4anQ7ys"
    "AMatA+XxTciyyyPspwkBw2RzGVlGXpaPDpANSEW9p6lEMlgdJ4UmgQF4HzwD0iqmFwd0v6nVHBTpHvexbNbAIcGQSqGdeL1BDn7m"
    "hjydCFQgg+SxMoKqYkNb38IBpBW6AoPck88kRcPDMunyLMdlZwdxuh6zD8HuR4XMpHvHAce/1gzIbrc4bWykbbD3L6AyiNypJpOw"
    "cIltCy4TjnHELsbb5AJywhbxzdWwEatUmjWKMYSuC9WSVxazI3IaHISOiKLdSy4LFR/hxGD7UYXTnaAbBAFyaJR7gSOyk1/EAtzT"
    "TSj+1TRCPRro9kYJ1ESoAhUTulrylFtxC003alYQsff92i4gFVlGY/HsnwkACJj4AUFYe63jrw1GsLGA25t7BeLZxhS7EkSh7beG"
    "0UUodjsvyq3YphkQKIz3UJb2hAbDAtAx154a1psO1hvXPJFqF/DyQyV59eZZHutAADWCraZIqRNNEVRYBJfE6yCVSfM4NxjXmnJ6"
    "1QkOjSh2gdjqWiJw+KPuIcg89rDb9KkHdHgQNRxvwYubNRHUezyYncHWN0K493RJ4c9A6hdUPBID+B4tCZN0FGlBvFdnQUY4wzDY"
    "PRNOXSEK4dyruHMRmHsO6BrKGAK5f67VLPgvTKFdtaHvYcej3P8Jbxe60k7kKpx7FNawTvVAut8UH1zNBnNP+8Jw1NNEoWpGG+Sb"
    "5TKJOq4V3F2rVMJo9+HNZhJ3avqEQ4HwqDrsWPePBvQMNkqbGwAZV0KcTNJBpR3pPsqpK0C6D/NsEOHejPcojHolI9hRGN8+yq0B"
    "YHuTF0lvCvNtENM+ckfHBmhvmT42RHtDJxWeLrSJ83sg2v/ZihPCoSY8iocnS5ReZ1p+g5or3NRi4O2j7aEwVH4PhHt1R3FwhHuj"
    "lqmwE7UN6F53AJdBmhtVfY8YFf5KmdH4qkQOwQwhyBMZWCUW+N5SjQxM2ECYV9rZk0THuUi5hujeWeDQ21aLHHG1+D/bY7Bb9adr"
    "W4VjoudKoBs+P8VLOhxjSZ2lN4rp3fiSZe+zNfQMRDlhxYqhoCM5ka3VoIDgTz0uIGlEdBI0UeGYm0A/O3CnTjdMMaOIFcicp2C6"
    "C0UJz2yShnBOVBqR06CXHywEY9QwEvmmSXUyZgKbS0VjG30UFj/gBblHmElEak8UDCzxGWBCNG4NbSvQzOXX9sgYEq9dgCM+RQ9R"
    "4PtN1VBLTcR7fTrBO5jN0vW2Ja9wzirweQz1wfeMQ5D3m7W/bhT0HoN2VhNb6AKq3Cpb4O5DjhnmtUn7feAArL3RUQpoTYEaLOnM"
    "sbMn5HaLa5KIHshNVxenNB6USQThvjMdTG3OH3NQFJCabnFE0Oj0bkm2WsL1WGHvt4WoNisFXxzwPbuvz2r5OLdnel9bpR5IHAqG"
    "MoCgKdSZ/AmjlSGsxAQGHOF9l1etTU15L3h8LsnzAJLgFX/Fak5CiTC2/r+A+gLvCqt0cdZ2+RjJr2JggCRMS3h4fR7eKLDvEb3W"
    "iH30WodssgHfC+PJbxj4XrQQVxu5xHC/glYQR8RfIg9C3Foj6n1T7GnlBpwYmN1LYnfvZO9R1JfQxFLI7hBmlOhdNUzV3EX3fjeZ"
    "p+xopG7W6YBZIsRPhnGAGdme9me8AxLvlInR3AxOyRs3nEut12LvRH2caqC6SLcHlF8wkkYzPcIo85WEQtW4ha2x5odpwaxUdtGu"
    "gM7JBX0CyUZi3CZ0ivUkStGOwfI39HmDhDwTkccCHzfKj9psqz/eK1CPmuIqpfg4/Ks6YEgMVcUDwJctsovihUM+ZiEMZUntkVjt"
    "EjfdfYY0qHoa2hI0hLyjZEdzCeOgMyBQCXq0z7IuF/RE0jWFYEr2YX3wIIBC2CT4tE8gBSt3wCmyfMkoDRg2hoNeSu8chp+EWYZ3"
    "EsiMhkHE0QLFMRhgWZri4DTCoIWifgZPuX1x0Xy6VvHZrYEv7I2yGa6Krk9N8xKOMGeUxC1sqbFy3HLZtQ3BM2IJZGeLjdcvph70"
    "ppko41ULZIMmOUqrsw/jmJmPNLEiFHqGQogHEsw8dCVGwdEXjNCLYs/KZ2PIH4+AWqm0cXW2Ehc3MJHUF7mxFZuq+4qtSa+YSgtW"
    "MK7gGH4nyDA6akvw3EQ1c1KZ6ZqJ/3vghmkJx5/KFv54rVBKiCgQhmmHgIMpIBSDwT7PAQ7JZi6v0xuHAwpUPuBz3hRXsjLWa+o8"
    "LqHIAepmlp75quzJsK2bUFIqZHAVtmeBx2y7q6CKKWrzVCYR8UhgRwEFyqxysfgjkkzpoRDm0hatPjakw3Ti57fJ80uDuFQT5pKl"
    "VRMRuYGZqY8fWTrfdnZPZ+ck1nyxUC2SHtI5+Xb3+yMahF6G5+4c/PbWma/0ex1yt/PTzcW3PtZfyjVxN2jpp9Ods//QH/Tdle5X"
    "H3XOfdY59sHSzZsyXiEloYuCixcuLV26qF82XJ8cOm8dPrF0+S39XpheF356v/PVO/q1wAB6COERsa5zny+e//jW6XeXLl/GsOt4"
    "kdMFnZXMYKgYLH76RufoCfFphias/NQ5cujWG+f1Vz6glzfA8Y6yCgG+MH+sc/GfieDHfbgyNDhB953PAgkQgV4rfyxwob7O8RsS"
    "6F76qXTffnfx7DvirT4b7R59s3PiSvecSi/OeRbnzy9duiBfanz7pUs/Lt68JN6r8M5I13MHlj55sfvtZ91XTorPFOpdZ8Wqfjig"
    "ChBw8WrTBwzTffGy/kDIlArtnkn/7x/e0wnEEKkki/Nvdv9xjkcqkLBa21RtsqV/jlFv24pW5z7Dy2I4eocOdr+50D13tPPmic6N"
    "0//+4ezS5audg0e6Hx3onv9YyeN//3C8c+gEM9H/O/BSHOw9U7tz5MzShc86V96DRt068OLSjz/aMO4FH598HZJ0jlxRVfWBuOds"
    "3a8umroL6NRLP51aunAcCGBGD/t/UPSllxffe6Vz9ePOwaudi98tzH/cOXmM27lw7TX1HtMc/HbpxdO3Xr6J1DFr/ODw4lc/3rrw"
    "L6gF6HDrpY9uHT6+cP38wg/vdd/5cfHijaWf3l2Yv9m58SZMJSZOPLA9N181FokdX1v3tU87R74PxkPrXP+eGxrqGFQMRFG5uWVK"
    "G1m6PA/CCciMWQ4d7Fy6bjTUwLdfuHZjYf7AwvUjwBEL1y4uXPtclfjvH873RLsHckDu7uWTmOnkGwvz30OmW+9/2DlytjN/Y+Ha"
    "gWBhx6EjC9dOL1w70Tn44tKlayLLe6eWzpw0k3WPHqAx+xymGbRo6cBBHKFTlxdPfwZfFUO/cdwkYufK1913Loc6AD1GWhtNBmJw"
    "tZ3L15cuv9+9cAiIzsJaUY47AZ1b/HT+1rsXTRob9UNJPMOB45i5um+eWLh5Dn4uXfh46btP4WHx5Xc617+BlrKQYQ669d7Jheuv"
    "ghDoXPwayls8+x0MEsyz7ttXQGpAP3mcAgD15iyzIdR3Dn6dAEY5cRXJx3wgsejhpR2sHvPMcYKeucKw9UBgk6JLB8503z+1cO39"
    "Wx8iQXoB1y8rpwW5PsEJQcZ0z34H5ILZFItX3zlyFVJYgerFhKT5YRI2Bqg+IOGufsNVx6DUd8980P32rWjR0ZYKTPrOqePdrz4O"
    "EsAAol/84tXOiW+5vIBkBpEQZGxgY+AhmHYwe2AmazFgJ7IGomdqgGDUmrjZqCj6fOfKIf608NOl7unrUXFugZ6PJgKKdI8ds7ID"
    "TysUhrSOwkTTU5Mqxkl87nNWZLgRQBL+CVWAlITJDSubyoh9UqUbsyuyMvXrWRyoPBMM5rnIcvWbzovnSFy9J6HkzUltVexiODEG"
    "TJ6XWqViRNHjkcMlHZd+fLNz8GNjfM9d6bx/AHho8aXrncPz3X+9Cms8kvD6q51Trylig6yihetdWPygXZ3DN7ovfYa0p5YaHQrC"
    "w6t2hSvsAQsfmDdGJT1g4KNTrfv+x90bp+yQ70s/vcNKT7BcO+A7sp6RGHoqFu1AiqvzMHAowF/5HqjGpGSpY5AmHtida2Clf2F+"
    "fuHmW6Ha9DQgxWzpu086J6/2qy+M3M61LH75SefUEVRabpxd/OrsrQNHu+9fgEUwQucQejvPg+6pc4vffcg6RPfI291rB2FVNItB"
    "gXTi287Jy9DMxXOvsgSKcIkMyBovI48IGfnvH47iyn3zTdhK8LqEDX3nsgQU4byo14iMMO8uL4GOcPWbpZ8Od8+d51oj+OzcZis+"
    "O3/CJlSxehtEe+fUicVPgdYvLtw8IZb9oyAjrqLGefEw7geOvJ34X4s/vA3vegG0C8pJukfg2bvHj9768NzS0W8izQ1gszOVOaUd"
    "nB3kHdQSD80uximcSp26L/x4FqRo561DcajsXIAtWQCVXQ7yocX5V2IA2cUEfu2Nzo2TETD2zonDwdcCh/3WuydC7xUGe+fI4e6J"
    "Dznjukg6w92C2QsF9s03uhc+sqKsd88d6L728dJPrwPHRegdhFnn4mAxBaWRk5qZpbplTg07sjrPMUtlHLTDnIJxoOpMb1xmz3zQ"
    "C09dpWO27gWlrosM80wIRV2XaeENE0GdRxwS8uTqgaCuUkbqDqKnq3SxVZvQ6br+o/9cuAkLHWx4T8Ygp+u0V7+Btd2eNoCXrnLc"
    "+uTt7pcXFm7+BPl6gaXrTp47ACxjzyCB0nV7SFDi7lamD+Gj35p/nfkoCI+++OKVwGsJkL747s3Ae0bEXrzxYeCtAknv/vPdwAcF"
    "kn5r/pVQtQyTvjj/U+C9wElfevP9wGuFlL743RfBD4wBufjN0WAxAiq9+9FbgfcSK71z8T1+b8NJV7OyB1Z6NE0ALh3mmZpCcVDp"
    "bLNRLGyHSOdEJv/asNGhNTzeoCH0AEcPJTPR0dfFYqPzbECUchs2OhPBCo7OK2I8ODoqxP3R0WlnuqcdAkan+Xly4dqJpe+/DYGi"
    "o/Zx5RB0snPpuAUX3cz5b1JqF2/8xFoNoqLHwKFLkXCSx8OChy7JRFfFLXjooYnZBwgdtZePDqKiHoeDrgayDwr6wg/vdA4eUdLA"
    "ioAOEgbSoMHhyovCKnXwCFMQ9cRrB9gs0Dl0Al7Caqb2T2Q2+35h/m01Fyyg52zeRUFJFhAb5jkxJ6QBAlnSMNz50tX3F64dA9Ep"
    "DClAoe8Pgoon8cwhPxl0Tt069AaofbfePWUFN+cyuh8cXrp0ZeHajWizDIXAVAUCoOYm15MZiaw9YURzUN4WP72IVlPS3tUiYaCY"
    "d78/AsRU9AwBmC9+CtuKz6LY5cFGmbDlfAQR/M4gTLxF4bHELeqXP0ZqlS6fijjRkYsClAv1gxJ0z3wMlA9Bk0f2SrSRt6CTK4EZ"
    "wCZnUjMdQSUvs0JuopLzEtw5+Gr3rSs2QHL+gqbbC/Odi58u3HgtMQz6FtsIume+R0Mu2XFUM1kbswGRw9TgDbQsKMFGTMGKI8PD"
    "DuKO07zAWo2SFP44cwPLi2Crg6jjnEKNUqjzAbxxadA+FsqD7Th8gCh3HE2tp74QyvW5L5dufPHvH84u/vOG0MgvfEFUiYMX1x03"
    "2g2lLh1/uXP2O+AVIAVaRwQFjJI0rjizIO+PLJDisFta+vH14GcTTjz6RU5pNv5cu7F0+WPRmxDPIR0oN3b5rXeh150j73aOfACc"
    "G2wpgzdzQy2Y4YJ6b10xJnIULrx7+SSIGNwCUzlojAXKrB8Oq/vxOOGwgKGlmfvC5n4o4ZkRZCw2pSvDP/aIxETn0svAyUuffgSd"
    "AkJEjza40igw+NInL4bpxQJEBFYGxiNBB8zXOXXm3z+cxwOYlz4L7ZYEC15/FYQ4rhXQmmsn0Gp0+Mbia1fQskX7cyg81A6STpY2"
    "COKJkJBknbgiKEKtACoDPW+9fBPEbHf+AjwvXboQLNsGEb4M0kJhg5MWerA4/+ni/FfcuhhYcFHe9e+5MM4dQQVXDVSWqsV350Ek"
    "o0GDTi65m3YgcFzdKFFPMHBLKoUHzhuOxMZE5/XPuHqlPkQRwFkesD6Fq8vrn1lgv+XxQvf9C+p4QdQC0wLecocMyG8266CKaMP8"
    "FrYfZfWxYX4HjVkm6Pfise+7B160gH5zX6Kw36LBR97m8ymDJxPhvYAN8FtYwmSSANy3GmHQtbpHTiGbR0c46EiwdPmT7ssHowjf"
    "sCQt3vgExE5gqBTEN04TmDKvfyaiFvFBtwXiOzCEwfBugU9SXVDKQQjZm7WHOGjvEaHwxSN7a6UwCuu9MH+1+8EPEVxvkEZhVjU2"
    "HOJwNRbSO6oWWQG9mYq06z9pRfLmBJ3r33beP4zsbkwnO363SPEATTjKzL1QagQu3/OvofnozD9ZTmEFoK9/+ipOkd7g3VyWkil0"
    "YIL1qflvAe9mXrLCd6tJEkXupgOTC8zJVuRubMeZ72OhuzknpLh15js7fnfn65ci2N1qZ9UDs/vWheshV41eUN1xqWUfYOA7Bw/y"
    "1jOM0s2Ht2ymj8Ho7ly+vnjwU/OcwprJ4iZkQ+VmmaQOjxeuvYrKx5HDi0cPh9C4hdTkb7htBMG7eON6IpvoHj0AHaZl+x+dn16G"
    "N2I7C4nMAmFoWN+/XdTtzsW3QQeOSM0w6DYniwHdVstwD7zt7qc3YVsRg7ht/RjE3I5pZxBu2/QmigHcVkl6QG6rNMr+GYHdxlPd"
    "12/CdxPzIoK6jTrZkUO3DkIqwt9eJ6MdojsE9dkKvI1uP3KTiKfzOH6w5sWQ4DYRtmNKVVhpwt3CQtkALC8nS/Box2Bro+RUI50Q"
    "BYcrNpC10aXg6I8wlWITyXl86WV91vThF7yfQIrJ7bcFP5sHJkrNAHo2bqc00hKpGQyiHZdbQ2ezbo5ZjNN0RUZxoo2bcOwgOg1d"
    "Prn46QnL0Ti62Rw5g94AP3669OP17gcn1SeUCK8eZc0LakKhfuSqLPpV4ZEAPHjtE9Rr6PidTy+E05ENLHth/iD0GrWsV04ufXqo"
    "c/ZHtHx/cL174hL0h/utTigXT5+HdQL38GxL0w65OB58mCi7zFvdYM1h3UslRoLQFBDnzvK9OmnVLk7EUXh29+o/zT1dGPlaFGfh"
    "4xDqNR//L351tPPjQd34Yx93Xj+mBF1PmOseBXBje6Bbo3PV/Gsmz5nzCqh6rHPwey6FhyKyyQnjWYsSlYOUKE9V0KNIE8FadWTx"
    "6/nOP17tCWMN+9TO1wc6588v3ny9+9mFzg8n2VwSwrM2/A80nDXzMAhWC5Z15/KhxQ9etCFZJ+DTrTc+tqJYi+0xTEfVBZiUGtGZ"
    "HcssONagESwd/txAj8V8YVBkG4w1zxZeqNkrtHPhC9BTzHUygl8tlEO19OAmvDcUNc5+eQ7PtETnNkk/9HsheuFU4q2r/ATKA8oG"
    "+oregjfPoZzTZGR/GRjF7plPF48e0VWyC4Bkpe6xY6IMdvIhr5TOySuLp/+19MrrC9eOKefCzsnPUfbLvrFgkE4IQYBqcqAKULwX"
    "IjWQgN0aueHon/DJS0Bvowi0tkGZDwwnFr+43Dn5EZrKLl+lxfWYerPw46uQMYpAHektVDJgb40mRPqr0ae1fHj1jcX59xduHGKS"
    "otdClK8jKNPCa+Onf3Rf+5ggX1FWKxb64QD8i0XKCW0DlrYpbxpVmvtozhx+RgFHlhB0Bjkwj+alg0eWLn9468wltnCimebw551j"
    "Ihke8EhDlBCF71zuvPm5aeXhkqEKXE+u3cBFnaYQSHukLQ1s9/wpWCXVAgik7hy/jjIL9e0Dav+P6a98TXUdU7bI7mlcapUXmnZF"
    "vnbMxjgBRzXhnnr1m8X5k2jfDJGF+sj7EeYvNMOQJY0dtVBdvHhCkuJ459QnnSPaOIy0+vAL2LAtXjqzcO0iKPnBJSyIIQ19xtUc"
    "eFrfm0FSX/sk0OJbZw/B0syGCp7wInxUQq+nR0+Y3mSyeUciA3p0wDYHHKQXT39tugJz6cYk6IsbDVsg3qMGkKNhDBIbxKUG5XMa"
    "QoxeuvQTtBumkboxEQSL1moYbS47N06ihoV+XNIRXCsyaIQF6X3oXTsqdM8ZiDwOZAMNjKYiamMXX1m48VpkdTwfhYQmtyksFQ0X"
    "8RqFFQtaOrerRkWBnxPB1TeI+6wIYgF9BsWOfLLeUzMctsqgxYaAntUQ2GCe0TpEUhSKUacA8KZ7/EUU1yffiWA7RxdxmLURXGdW"
    "brjfETRn6WD5xnHVtpBSAAOyOH9OefjhQdW5A+z9HRqx4LqgyrvdhTCE14xkgoXE9E9kO3Ui6BphhWyOzxy2lEZAm2FacdJoktgt"
    "wnFWegL18e5AOQLiNY9L/7j17kE+UEcx9PLBzqF/0XnYcaaCBZKZ1TBTcQ/gMgPzRGGZ0dv1o4PszhFGZE6oXsVBMguHZjToWTGZ"
    "Q5JNnR1Y8JitSU0HzyAas/CuDHxUaMwo6k58GPoY8D2zAjGj9Yy+moUrlSACxsz7VraD8a5KHSXpTQPqTrDY6AUIx/DQCZwL6sST"
    "VkOhJMDqHHSm7Y3ELO4WSbNoPBCzWOF/eledorC5jDfDZv3qzArX5wOooaBwJsOtYK0z6Hh766WPWI8ItVGhMIdpIGq9+k33vZc6"
    "L56DbOHW/UItUgDMC/MnYEvMzIG74qAfUAR7WSQP8Is87eLzDwsPWlGXxZb92LEeQ22BXRaDG2FJK+SyWMlIJJs9s0Mus/eQtsoE"
    "EJdF705eDtkwQEEW6lYYctl000arPZUecrW3IC7jeg8dpB01H3lLrwBSt8hnXyp4IVxlHviln852gjZ/EZYVZN2tM9/YIZXFaIiV"
    "/+zSheOKO+PQlSExLBGs/EVTKoDlzpWTwIqEssxqlw1oOfpFnhQsfvklLzlfv4RLAR5ACiuoOEOIQVyO+WqeSQVTBI9MYpCWpXeY"
    "FWuZj02kQ3v0+CRweNITbDm2CBOCFnU6TRyQHt2vPoyCLOszzihfhOGVeRTZqTAWYblz+FDn4mFrIg2v3CORxFZWQq8HuLKNAAFw"
    "5c7Fr5e++zgCqhxaRmyQymK7OP9m9/3zvE+IoCmrLaray1ihlM2Nqg1EGTdzUMzNt6L4yXyAh8I9mNuETxZuw9cOmEf9NgxlcfoY"
    "9gqwwijfunAdNgOhWi1IytZ05kkfCCs5RnY8ZfNesxVJGfdLAphH8XAIRxk3ztQEO5AyctIbF2+dPhBBTw5df7aCJ2PTgv0TwMmh"
    "MgVkciithkwWuyz6bIFMDhxSBUCTbx14D33OSLlkc0QUNtk0UMdBJpuHI4aKaMdMRhX38qHOkS9seMlGSaED7BisZDVTUJM37eov"
    "3xR7ZNoDy0PwI8N4IAU6R+fie2wU7IGVzFtkDojAqpqyBdhucNGIK82Irf1Ll7/rviN2D7xp4Bv2cajIZpV6E37sg87Zf9yxWk38"
    "Y8XfMdjHURYNIR6r5sXDHOOuLJhEODSb6i/62575Tl8WvKY3myBpO6/Ng7aDO5Bv57GXctCBIN0PrqFlzPCVjCAXi5IMJxlazzEH"
    "0Jj3f7xELfxwZfHSGbbkWUGJcU9Ck9PkB7UniUMjFp7WNw6hFDG24GzECo4n6N2XXmZ6mYNmoBGbZAOlGPbui2+9i4pbUKSzIYAv"
    "YYLyiHfgYaNj8LAFf5jrDd2+tQAPq5umkDoecZjdMNi/04o6LNaNDcMJdvOJgg6LFA9aU+yTG4Njnevf2eGGOwc/u/XyZ8ofJIg0"
    "LM5J1N1meBawwkv/uipMo4YqGkIXNuwo5lmf2k2YF6DRDsyX9pHnTlzCe/sHTnWvnVq68DE0UQfEaMZc5+XMFnxhdl02PY5CyMJq"
    "hke7IvDsVGb0nDn3ZQhdOHxPIogs3P3X50vfXUcVL9oCCSrcOfEBD4PpVGxccwhhCofMJrxbha1Z59iF7tuHF+a/j6AJc+CMeCxh"
    "tBmBDLr03sL81d5owtaUYTxhXld6gAmLrTUpiEj1E+eh57FAwqbGFA8mbEkV505mAxLu4R8WHTmNHBzIZrqRBq+/R5CCgY3YVS0C"
    "EoyezSBwz3/dPU4bdltDYEvWvUTRNq4c6h4/fOuNI92XvgQNDWXc+VOoj176F3qqG5eEzXaYyL+qcHVJKgbxl/w6TnAq48JQHNiv"
    "StsP7Tea0DD2wdbcEJEqko4poYMgv3xVJgTxywOPN3AuvhdG9g1fZQri+ool0UgTMhJYoX3DIyt3vrh3tX4Vjae9LU4yI4VG9kXn"
    "UiIUi7rQnDaBfXn+sbEczVHQA0qsnBNDtzBCYL7C++7EB93Lp+04vqBP4M0MtUobhm9TDql74/wVF1sZ0Kd7+nL3jdfxJPvQN50j"
    "V5UNzWxQELwXzfPknWAH7+UCY6B7uRKorfvmJ91Xv+pcON0Tsrf7wQXYJFvAesXxP/mOsYqOrvfQP8rAcR2UbzFqKSfeWnz1S4xE"
    "c+0Gz0o+QsWTtZvneGmI9FjKAXbMMaQ8HnfKg1QC602YxGbNLFKaAOaVhhmtF4Emde6o3JEqnx6zxGhZQi3onPxcrNV0RMcaVMit"
    "OgjGy13lGRhdZjUIb9yEj5JKw/CKxeS1Q52T31hgeDlrQFyZMLy9RYy1UwYCr7qNFYXgjagSAQzeOLEbQN9Vt9mi4LvcKxv4bkhH"
    "iWmOgb5rbvJpRSa3VVqSNZSlibkrZjBtEaOQu53LP8CkQLeTLTt22sF2EzpUWxBlV4RzOXni1idHcBdK56C3zly69eE7YXRdseuW"
    "IUhMYF1x+evU69CUHni6GA4ndIFJnKCcfAeI2CNyEh/6CTKoQ1tjb7300UGOoMGRvgTzhKB0zah1gcZq9FzuHgrHs9fwvP/AUTT6"
    "kBHazKdu/OmK9GVcHeaHomQFwXFRLhnqqyKBiLr23VeLR/+5dPMTDJHxBrp/dN++vvDjT4GSDBhcsyi+JIr+YgdfZR+xIPrtws3X"
    "YAnBsA3E5OzHoBYoMzwArhnqtqS4Uyx2bfqKqbFCayJo5Fsct0+PxOLe8lJpeosLz5STlzkn+rPcOCuM/XhN6RNgVRl27CU7qC3f"
    "5cNd5cFXqYlv4e3L917hXrFuxqVHithivyvPNBsMynaATE+Ypyf9EgsE287JT+SywSHLghC2XIqWW1EAWzHFTlxYPHqYdy7mWMt4"
    "HjdEmMUoeC0QMw66dvHdH1ExZqUlAl7Lke3C4LWhQG9R9FrBFEbIwNAkCTRWqEcn3oISA+i1nZPH9asAbu3i52c6Jz9a+vHlxc9f"
    "Ee57lBZNHyffYcaBn3Q9BT3Uli6/yApI99rB7rtXeOXWHKSBarl5Vpxa02SJWpGSYcHYhqFIhjaQ2hB57Ei10fLRlcaQl1bMWlQu"
    "Tl9H72j2vQAV4/T57ltHhPPzyc/jfDKM1kqkWnF3mmSSDZ9WdSN0Y11ZhrqnUdzSHdd/sh2NryPT3f3P+SUKsCNv0yWiz7koSICt"
    "lb5uOPkPvIexJqD7fIn+JYqmJKtj+oiwhV+8s3DjErp4kmOcUP3ZpebEt3imTCWQR90BlQDydr//1+LZt0XsSuCgm28CtbdvSvB7"
    "Bo81SMTwscJ4FECPxcM/dd2fu2gDjVVNsaDFSp9kBTeroWK1Zzg1XLdIosTye+3CaYeHRXsj+X8HdCkTF1a4h5vfNB4s7pgjM5yt"
    "/voqF0UeYLtjlEVgiVuYP3jr3VNGqL2jujfyuEPbkOQNpCAerFhxg6mYW8IYsJ1LRzsHP+PFFmr/T728BgBgOwiEgLdMsHd0+cg0"
    "ITD7ChEgI28wB+MyCnzPl07lMi1Cc5yBifc66HdLX30CqpnuZhDslX0d2LukN8wr8KvcrWK8VjyxvnCdO69c9jpXP146eoMVHtz6"
    "8B4/8Udxy6r7rxe7V77DCCPkyUlufeTZFYMJa662tmDFEShX05csJCFDp/oBJFdOYd7X01ZWjd7K01wEhZSbAr4XZIpG4SbQwxWA"
    "1o73LCCu7H0X214TvFXEho0mCmC2mt958AKHEfM3Fr941XCzZOVKU91AZOXjWW6gumJocqm4vEDhHu0grKErOD8cADpwsejbd+yz"
    "KBgqOv8deImOG16TwKuJwPWUt690jp1fevkmppx/Z+nSRfa1RYYkLhU+w8CB4ndP7FVcyK8cAqblI1R1i9DcYIhwtNRikz9DIKwm"
    "5UEA8XBhiyPsiatQ8H6N8D8iNtBVRKJyB6FXhR7Am/3QIm8gr4YM5BbFKIS8ah4skMQ8wuirWpSF8FdFwcFsgV0bX1dGYoQT8QUm"
    "ff3q8OdLN75QvqDIbt992rmGtylYL2L5wi9RzeDYJaevo7sQRYQUzu4nPkQ7jqzWgqmqKCbmFZ3gGSGN8Wzqh/c4pAG7IZi2DBWZ"
    "WZxQHTrBYg2dx4yTEjwEBeny1nfqUC6KlxoawCjrcI3QHtpZYkt0URoWldl+8egRGIpYUFRx3iqdt000VJ0zgZtYWEiuvYyaIBmo"
    "+ScfzAagULtnPu78dIZNUuS4aUVCRbEoY9QiT9CIBUFQhb5I0b0ZLMCCfor6xOkfOz+8LNRPeXIZBT/V8UJtVWNgC4rJsfjJPIwb"
    "8gsVy0FBVZoIvKlZuRXVlNmFA7lYAU1R2ARv2WvLxpFDbInkyJBBSFOxQnBQjI8O4sL75ue3Dh+P4JiakdLCMKZKzbKAmPIFxYX5"
    "j9h3PAxkilLxx1csGKYJVrqC8KVKZ2Fp2H3/Qg8Y04SKexQGMRVKHgURjYKYqnA4QQRTjroWA12q6qTole93Lr7d+epM99K/YpBL"
    "F7/5cfGCiFsFYhCRSocTZdNxNIFYpoldIjBRGL80FCLG9C6JgJfikMLAybhjhvviMSGyjUBmOpCDCVUa2qpAi0Mxw9QWyWhuAKVU"
    "GhoMU9EZW3Btqfpa4EkjDBhGJw1yoQWb1MaKQXzSkClKudiEgUnj+TAAUGryGey4g/wYB06aUDHEreCkel7YcEmFMy7HMiYVrAci"
    "qRCN5C9iBqnGna9RghJYYdBRURnlsVZmovAZ91/eGxRvVBxmSZdCO8RoIPq12MRRk9BUCH17+Sb3M9QNE0DUvOQgrILQtWvXepcQ"
    "AQc1iR+PDYrOce9cxpAjb1/htVGUGwQEVQgMN06DWsdCORq6WyxTChQUvpGXwDuLly4EL7ydO9E5dqHzLm00nnnq8SAiKBMsDhFU"
    "UoZiY4chQc3ht6CB3jpwAE/L3p1nd0sbIqiQPHy5PlphKK8EAr310qXFS1/bgEDVteIQDChyCAHZhGBAwxUYIKAqOJsB9HnrcxiH"
    "F80aFNwnf4oiffIJB443rA6R7PFXvQxixEF7KidH6EIsrCcnMociDtjTBI8JtTcO21MUTsl4EK1ZQgCf3Aw1taOgnqiu2njHKlNw"
    "Y2UQKw7YE30spQyKwfQMiRwrjCd6EH5+vHvgU7lhfE/sNrgJSIH3/9G59A6em9x4nWcerO389dZ7bE/BG1Ss8OEJL6UxXODw7vC1"
    "EyKSIhFVXf4OY3cuXf5q6bMDYehOvgUf/BZwj6bdl0DsFNf5fyOYncI+wDdWr54HgoWwZbhX5Kz4PR5tv3N58dt53O3Qe9zeMBvy"
    "bSfCgklEAGVAH17611VTsJsgndKPv/vVx6FLDmyTMKA6l65+C0uOOssz0DlBQ8Lzf5VB4HMuXHs18FrZjvRWRXpwh/A5xdpEEpdX"
    "OrVCoSJy8GNVtO6RhuLsfvnh0k+vmRtjCxBn6IQ1iMHZff9ljv4axN4U5JZqSxB7M2SQiMBviiNNs8fDv9Z5Lfpn0TjylRNp5jrA"
    "l2E0TenSoKEw4cGATW2IDgqb8gwTyHkmePBe5/XvwwuiuRTi8WpYAh3VjVtvhoalY3e6zUp3YTGGDnp9C9gZdRMwCDelblfwMQNO"
    "sQOfdl87snADKobJ8BkXydyA55kv/tQ5eKJzEu/Ed0+eAnr/+4ez4n755audy9cF1d++Iq7snnoFN1OHD3HhuukbBKTKYPFwhN3m"
    "0ssL81+qgDvaW+4NdHw3b/VjtYi+hdZxk0UWrp3GlDTGQt5otYksGrqFBJRp3gcPOeyoOEAUTG6eAn9glzksELyEwdM37hBdS8Jj"
    "8hjyaJtRQyxWPnlWEWNuVUiZwmCJyJjCZDkISCbfcjQniprcIuKCCrgtT90USKZ5c5Cxh8xrMpY7k0Yt5uQ2ip2MWrIw+ASZrhAd"
    "hEyEONgRl1ujkKLaMyNOAIs4rrrn2afEyGTzDTtiMI6dOpdAFn0bk6t1HXZPYhcScfUQ0ejYYi1lDVbVdh6bzo7lEdc4T6st/HWb"
    "8E/JhX9ozcyPO3+bzrrZPz42nfaqxUqr5DaTbsr563R2zq1mKG/dz8jsbjNDJZTcDBXywnRGlNMenWpVCVcp8dw0lDDXcP1Wo5rA"
    "0D+1qYS7Kptv+ni3M79//yo3DY8zyVSu2qpUMn+dHpMv0n7t8doeUJQLTRd+NesVz0+uGxuaGF+XGhseH89Rjraq6i9QleM7VVXd"
    "37DunJuBNvgpSJ2eKdSTz02ncDksJaGfq1bB9xz2S5eyhkrRTc7h9aZ6pVB0k+v+Ppf8+557Un9vrys7kKqayv6R0Ev93A7qTtIf"
    "q46nMvm5NbCwt/OpjKvLdcuh1lWz2SzSbf9+egJK5vJr5vz231vDw4XhNXOSDO28eMi49/jt2UIj4ZeBfjzF0qjV5J1qmUbomWln"
    "tdCknp3G8fnTNI7On+G1UIp2T7edRjmbhJbPGaPklWmUylmjwYVyMjVXcf2Em31kGjf1U6PeVJJoun+/i01GZS+fEt1xR/3GPpEe"
    "LWWVHX6tQbeGXP9R351J+uXUaGhguIR2ES/PCrKIV9TPWjnbqCaxHSmnSc844CmnWM4+m8QuwIjXymmKoAkJxEO1MOuVC1A50aYF"
    "TWjmcmPRt+NQasUoiWteUTmakC0ipCzDJGeJvtTUFxgGeEFE08TMBSjHB96SeJnAt6aiquOmBAXburY/B5gYeLpaHiuKusfHXJg7"
    "z0zTH0yms02FmfTPyaq7J/Fo1a+kt1dajULlqVYFhIIsCmalW4GtD8wv7EOt6hITu230McpnxCN6D+WduWrGd9LpdLWdotGtA88y"
    "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"
    "izQ64Lrte1toihNU/axXsmyr5tbUi9Ra3uKEvXbIympGBdo3WBSUfb+nKCj7glFQJqNXxPfexSvie40r4jusV8T39bkivkNfEd93"
    "16+I7/v1r4hvMeZqYJ7OTkTiz2v7Ku7Nt1t2lo9WksARk2hoInnNu39x1433iVJmqw8BsU34WkaurMgl7nEFxLYwBEvhEPwlzEso"
    "FfRTinaTeyay0nkiP65n89MTSeOyr+5SMuU8nsw36wg990xSOhiki3uT7K+RcoS/xOpMIU2EQSMrnsXJBClnbDtdkcHWI7Q7NT+P"
    "3hLRmzg7k1vVeTDstcfbqXFn5D5odKq9ZQK201XYKGSfntDtfmgwKfTQ70kKPRSUQluDEY+2ccSj52Wgo13y4clAxKMn/8dEPNo1"
    "eMSjTb+ziEeb4iIebbo7EY+e/01GPFqFEY9+H+GMti0jnNETv+dwRtt/mXBGTwwSzujhuxvO6IlfJZzRw1Fd9dG7qKs+auiqj1t1"
    "1Yf66KqP62Xgobuuqz706+uqT02oKKGw2ji7s3N4frUNMeyielSzkgzPnj9klQ+d6VgBisGAKZ16JbmMcnMDJsxE041E042Mp8bl"
    "lRGO99o7vrJrXNPV9pbIzVztrUK34vR1Vj9d9Pea91sbKL+24NnGXj/4PhxPBd8JFwwlGyK3YXXF3Kvw4aip0e1Om/2mT/qQFD89"
    "qo5fB8+vj2gjl2fKlZ43VlYeR5o841buVddYqQ9PPu94K72zQneUI3k3mnk3WvNuJL+jWjZy9rw7xsN797Lcu5vZJB7apxFEBqRF"
    "/N09fVavHHrxjLufv28x2wz5+1ayRcPfFx16m6a/bynbMvx9W85UtpDbHb4K4/ja5xW0pxpuN9U1mHp2t/KOdXZL/yBY0oSLNyUH"
    "RWE7ufJ4gWsvU/Lay0x2d+TOi6PBZIFCq0CJq+dK2DjDV9jn68zOTCrDVXAtUym8dqJe8i2UmV/uqsVtO1zqaxqyy6rlvnHL4mF5"
    "UaGq71cIFypxlcFIYV5lMC+aWKzcd9ZX1HqroBG5VYBIAlW+G+DRnQAdxCKXHvPGc7mGdv5XTrbsWrsc//5GnH9/w/DvbyivcpsX"
    "3J1liyARBX2WQcioTAwKP3WPIyoAg5JO3pa23VpAEuM0Z0fKMPn98MWEGgg1eTHB7SelmtlaSEqB3DKkFEqtmimlWtmKIaUqILUK"
    "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"
    "+I7pt1YlLC1pYMJTvjYdvqvEVXrzgiW2CAvMIWWQiIQZ8aq7bEFGJiu14i4jNESN4/xmEoVJkPEt340P8sFVxtyoD4WHGBk2A1BQ"
    "PGGYIjOZRBOWPDc5nDKb4GEIkiFeWDJ4HckNXyWHzgwVqJ9GnwpVb4YtUQluWmI4vbGZQK2w0AiU8N+73H1TDaBbU6bUpWBLjZ/4"
    "v1q9UMSrvGb4C2s31qfvNTrSjrllnqf25/Ha8eaJrGKFOR6wFybaKX1TbudgN+V2/p5uyu0M3pR7ZMKMWsj35P7Ef57lP88E7sg9"
    "M+gduWYd1vXSr3M97tnBr8ft/p1dj9sddz3uTxNBWvS+pbZKYpwE76qJa2ryaqHZel3Tn/td4NodZMHdd+fi3mPR2z5/u4u3ff5m"
    "3Pb5q/W2z84+t33+qrl6512/7bPz17/t89xEdvOElOdiSc47cwL6O7zVDMSJFmDXvNV4ilKIKGd4ciSuhqNd9CFaFqPf6Nkabbo0"
    "JFuyajiYmA7SQSFsTFVqe7L5aa9Ucqv5aBKpFWTzDRf3faBepDLcBKFRxjSHv8a3iNQZi1LsCiBKUTphdMMeuNZSANgKQ1XTJBR4"
    "G/R3eq/cFXGX0nRLtT2yi4SC23S3whsiLYcSJDU9tlRu0UoLNoc3Jsg/elo8Wt1F9zrJFLKrJa/yg3yA/0CJqJDXktuERhTYx381"
    "Or4M8QCuxskuLvijphH+LTSn1RQfgS6nhGOaJlMiqqkRMaBW3ST1q4eqImJq8J3RVWeFeAwOxtTxqjI4OobclgEJ0LEANGyYWVum"
    "vQptzbgMt5LF7TIPzABEVTCe1jnQk/vFR5M9CIfezhVKH3VVh4IE0zkJJ9TgmngACFi4Ww2M8fI0BuvxnUagf+wUCUu8gPDD0Bfs"
    "4tRwaF1MC8VfuUJaYT1x/P+G/jw8CkXYbpmck5d+hJGJbSZy8lOFShMSO6t2tkA0r127CkpuSJfA7LaCP52eKexN7m3hPd/H8F9Y"
    "aQTROVRT1rsnX9+bd+RbCvMkXrYZEGE35a6hn1Oh7P51qAAr8ZR/T6lWJCUlPVkr7YNNJUyaytO1+hA1Yd16pyky/A0y+LW6Nf3j"
    "UNAQtX3detUwSJxtBluFFWZr/M5Gymdvn5SgqbkSq1tIwiw6Y/Fj0jzWBv5e5VsH87ZHEph04/AIyuyQNIgIbtFG2PtXYPMlm2l+"
    "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"
    "rdkH7WZ/9mLj9Glv9XW1enp+WexvVB+8KXdv8LJRXT9avn2auirt7290Wqs/+5v1yylvf7sz/7zdiRa6JW+vvj9oPG4ddN2rq6X2"
    "3PFV+BKGm7trzu5q58VfnHs8DFy3dn0z0+3sVG8bSydt93pvI2wcRaVg/9vB5dZBc622tvna9jfWz/sl25ktTb3MPRx15vuDxvzt"
    "S2/39vnb9cVg4B+7p6dbR/sExe5OKQgGT/vVb2ed6uXq6fxg//ph/fL65Pi4d7bWXN2cPagfNl52rhY2DzrFRhAtH164R5sD53zn"
    "p3fU3To+rtdXO6e3zc0gKkaLbrN0VrdnfpbmZoK93vmB9+o/LbW7L91a33vZnluOvr0U685DcFKfajaXmzP1aGnr4mdtrrS063W7"
    "M876+fzNljO1OHv9vHdZmzvcLxKwDu16LfJaM8vLxbrX6tXWj/Ze7eOH9eL+1d6Gv7QU9Ga92cfbrj94PXuozx5GnauL/t7Fy1Lo"
    "Py9vlDa2qqfB/sVga3Hp+efLdtgadL29hZ+ENJcX9lvLBy8nuzfuzdHL+dyC5zbWugf7t1eNi5+braeTQ3t7Lly/GhRvD8J+/2Hn"
    "5DbcPVmbre/vt73SkX+6unhqtzsn/cvr4912e1Btv65dPb82ep3zwwNn6ml26mF9z7t6OituLy6Xnr1FZz962nZvblrti/7Jfm2v"
    "9vNqzfb2/Ofj1Zfto/p+sLY7M3NwtnZ2E5yvX1848yev5z9PjlvhwV7D392eXZ6xb56KC83X/b316l4j3HfnF45ur49fL84XGuet"
    "td5RcD54PW+91AZbr9sXW/3To83+889W9ef2XHXRuT0YbEdLN6uzNzOn+89zW6/RqX1V3+jurF4s1cgQbmrfStV2p9V/On0czLcf"
    "9ovHm/7WbvV25un5dBAe94pHG3brxuv7uzc7u2cP+6fRxuxmbXaw93DVrm4s7V9WV89fStvzq7vV5e2j65v9+ubill1dvL2qu0t7"
    "50en1+3B7Leiv3hw8HTiL3Wqt7XGs+0vVTdmHp5bZ09be0v9x4ud+nqv3duu+7Xm6stOrXey7y8/9Hq3Nzv76+25qdvl/uB2zb2Z"
    "39+/nD/dbrVOeherL8+buzd7u+tTO/u19ef6c/fx8ebJO76pN1dLB8dbD6Vvxxfz+835qHr7MPXk3D7shIc1MiEd93LrpXFw03ce"
    "3MYcAWG7ZQeX/YXX5kPnyd5dqj3ddOq9xdrt3O5W8+ftgnO9uH9w0b3ef2jPN8+La+cbC4u7P53ds8e+vVpd+tm63Jp73TptVNfa"
    "S9ebDfd88/bmacN7WJpf2r053Jvtt48Xjrav9i4OSpuD+dni2uHMYWv9rPU8deh6neXHpXA/PDhb7ATz27tbP2evO09rZ1472Fr4"
    "5p/WZhrB7vNxbe789ai98HBwcDy/0J4ZrN2s7a//PNrYaD75F+2155fDVvF1r31cXFh0ZhsLP3fXb5b2Lrzdxu3c/vrVRndp7xGI"
    "Zetp73bmKtq6uI1eOpv966XSxfLjYHV3p33tHT3e7L7crgaPJ/3g+GGqWpw6PptfWw1q852Fh7C+PPV4s357c34cnJReuxfnrb3z"
    "4+uac3VUeyhV524XOlsn6735y93j5uXh7kFzyjs6W4oG27vPM98eu1def3Pdr7eC1sLcyfKDvf5zq3v9urgwdXhLqNpfrR5450dn"
    "R7XrncttQmEnP935+f2ThdP11duZ7YW5s7X544OXi6PNrn2+MXuxd731erjTiW4WCf1tbrqPG72Fmd3z48Ob48fj7uZee/122w9n"
    "H/zV2vzx+exasb5+UT0u3a7t9f3Dw6t688HZOS4+Xbb2D7Y3nksH3bM9b/n1+ma59e2itbtxvrb33Hlyti/s/snxQfFy9eml8/w6"
    "G52sXQ7m5l/cmYu9253FY+dstTrlrZL2ar1+6cC+3elW3b3L4tTtgWvPvix7L4eLrerOUmNn0270N0726rX+xXHrzD9ZnDoMndXt"
    "vZNNv9ZbWnBf/fNv65355Z3n1gLZOZs39aeN+cZL5+XFvj3qbgzc17Xuceu2NH946pUuBo5bnPnmLa4ePWy/bK8f7YerO9et5vrj"
    "y+tmvd3rrAYX1cPj3dOlutc52Y32Lmq9rbO9vdr1JhmN/bR6srjo/txsb+0e7DqHteruYvvM325fb+7M93q1l7nZXbIcrwf10m64"
    "vDuzUTrp7A0aa1MX7dvumV88OHXJOmhvVBurV6tbs15tpnOzXzqfOqsXX6NS76Ubds6eqwfHt8fFs9urfnUtGjxfDtrR4ule+7Z6"
    "XV1c3mycrB8vXB4FN6/L+72r6uVmszNLmOxU/zQ4tZ8uB6fL9dLJwllx6mGveNSs7mxd3ly9Hj1d3jwXby/ai5vz0f6mt3dFVsi8"
    "7a9dTvWD9vLVt63D62BrabsU7gWlh5tmcHN+GV6fHfiDnld6uFy8Xt1rXh/O9DaeNh9vd3q3i4ur/mljNTp5Pt85aHZOj75tlsJb"
    "p/0zON0LvfnG2mHz+Hrw1N8a7PgnR429tnfQediKbs++zTUv/Nn99mLNbl9eHJfOWqvHc85l+8VZvVxa7Ln2xs+f1ZveyWC+/rTW"
    "jnYGZ9FWp7Y/ODzvLvZ2a/7VxqttuwsXp4uds0H/euN5tbPXqm1Ww/7j4d7R5fnR69TcKqGN1Znr2tXt9ar785VM0eGTfRF6Cw9X"
    "ncHB6qa7tLy+YQfzJ0dLDxerrdmtYmv24WHvcr9dfFh7eLy4bHnL4U3v/HnQnjpvl0qdx/3u67y7Nrt3crZ18OithY/O2s7lwWYz"
    "nD8+PWsX+7sXSw91f3XmaXltbXP/eLH7OHtW3bnacnqrU/MLM5sn9vbrzFzj+nqjuXW2EL7MXRzU+sf7h0uz62HvZmpngbTW7c01"
    "BjPBiX+zf+Out6du1zav16+36w3/5ulpo+lOzTXb20udg6Xm4s3C1cXq2fLJ0a7XqEYPkf9zY3/Gr23ubxf35/cuO939qfNq49vx"
    "U2vturu829ppepsnm9FD63TroHTwcHzgdxePDi4aO53W0lXn+HBpsPXUOg+2N7zQXr3oDI5Pph69h+2r0np18Nzc2Fm7qju9ASG1"
    "TWdt3ZlaW71enf82eAyPTpafVqvP3Q2vtXjb2vMPDqOTxaWd1cv57sn54OoyXA93bvfCi9PG5erOS7gbdrprxY2pbtXvuIev1VrQ"
    "rUfFram92duzxSOScbYz87h1cljvrtq9vYPD/4+t81huVVmg6AcxIKchOQgQSaQZOefM1198Zq/qOZRcRkam6d57LWSVqwoy1fRb"
    "6xGj201si3JulKizkbNlPRG1ITlrm92wY5fzwyEsNdnZScxwdLI26MpTMnD1d9hQKZLnogbCghdyEoIEpIp+a9QQfFH+6JnszkMd"
    "TV1f6zM4+uczNqaF96jqqsAKi18pyTfO4QjnK+A0gSqiDJV1V5xcuEoMi38HXYHpk6RWlppSQeQhhDH59KkFlKa2y6i0TbJYRUlq"
    "J6WeufPjE+XytPndvDZ4d81ooDjduqqxvT/J1IJFJDhBfud/KlTYcRkd9R+t02k726Y80bTPn6OdUn7YG4gPnRynwrDAHhqKKS/V"
    "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"
    "xRs2kHTPmfve5865t4PkklQqVZVKUqn08vjYO2m+lCdXD/enA9G7qSqD68Ph9Wizpd3L3vzBf7w7PJ6VO3dPL/PTrn1T7djepfH8"
    "JF/N5vcP8m5zX+7t6oNhta93HtrmoHcjaFd+fyI1jLZu7JtDpdbfP3rc7WyWWx23WT1vmiX/TNO3O3pX6pUP/RepO5rtlaq+PL9X"
    "T052haneaNcu9vjhtbVdMkf+/dNMP2lb1lH/4KTX3j7f5MvV7v6shKbbiXzk2M+HF+5kujed6k/nbXv/zPQeD8tGZdIrqxN5pjqX"
    "V+7V3W7t+MDuzkt2T78/nXWcynWzjPRD6bxst7qlmnvQOG9LinHc7Fbbw74hP19a1pUolSbzHvpiHlmbrdbgRptN+uK4P/RmlenQ"
    "9q3BvGuf9R73kXHu17z+wN93O5ttpHXM0YEwsvcOjcn18W3jarZdEUt9aW+7vNk71QbT61rvYLvKH3eu5rI2l61uowoa2PW6rT2h"
    "od4/nz115KNt52Z0VX223UZ7e3R2rp2elUzh3Hm6ezw6fRij/m/WBgPv/n6vJ5/e9yYPvNS/7p7ZbstWjKnWPeH1vZsb41gVz7q7"
    "5ubu/sO9p97NhfuGcmmKpd0r/uVu/PgyvJn3bpyue7p3LFxdHO5JB4pvHMv9mwvx+Hp007p25Efz9vLlZK7el4Tth4Zmne+VxPPK"
    "6Uw7s1on1607pCl6rdvLR6VbKh+N75Ty43Aint1elybDw6b74rXvj0/G8qY9FpVZo1x7Gp5Kna6we3/6OGmPD46eX162hxbvnBya"
    "5cnpqT6vXmuNe2n/RuS16v2sXUFG3+m5IVXFgwPD6ExOD3v74tOFVjmfT6/bnZqsHjbaZy8Pp82j++74wH9ujg+6k9r4Xrg9E6/5"
    "2+uX3uBUq1a87YHgHqgX55M+Yrxttyc/OQ+NM/GqfzPaHZ6Le5Z73DlpyXfV9r54f/Z0fHEzazxtX1Y0b7vv7ZdnvHI1uX25fDnW"
    "TmdnSvO4ediQe6Jo9Cu3owvl0UHiIGvbjY7aQkJzdHJSvm33rfYmWk87Tnd3+0K5f3gZSocnremZ2B5ubp/J246tbo6fZtfNq6b5"
    "oj5uKuf9/s3wVPSOu8Ojk1Jre1wxDssVUfHs40fj0H022sqmcTPbHE7HFXl40R49irPT6bSiaP1O43BbqFS3X+6vj+b9edk5vnSP"
    "mkL78GLwWNtr68/y6XCOjNrrYUu6aXuis31j9C9H5ydTc3o4UK9mNeli4oz2LPOlXG0OSo+PV6OW09i9M3uDvce97pM971Qv9va7"
    "/Sfz8b70ePr0qM8PLq79squX7efG8/6zV+1MZeeO72jG9vXmQVe4aF839mSpf6m0N9WWrT1Yj6UjeXRytocsDMeX/Mf7PVuY7Ff3"
    "jjsvdkO/0mTf6vX5qs5X98uliWLOrs/VgwfHu9p1zO2aMlBv7i00Hw5vBb0zkZDpcTudeZ2HvclQt2eVodfZ6zS7xy8XF9veyf22"
    "tvfcaGotT7oUDq4Pq2dO78zdPLUOOsNBUzh76NXsbl8wr9x7e693fjd/PL09errstydP1lA71aRnc+J1hZeJLxxdnc+H0+vy1eEI"
    "GXz8ntfZvhmcHPmlK7VfvTl1rlvV5pPlymXnXFPUZ/Wmcq/7+4+lwcnmrteY7J8d9Pun6tA6u5n0lL2+e8O3aoej8nW72miVL3qq"
    "3ty/vt7f7/DS/GFz0ldr8q25dz18uboXS3czzx4i9e+eHluVu9aT4d9qozPhzm4Ot/3HR/lClAa1+65UPmmfeMK5prfvGpPbyz1d"
    "0c7LL1dnvnas2D5/7ljGiTLfPLp+PDzblp7Fs82zS/5EPBCGomTePT3yj+f7N1ZVNIxm3zfmtz30b+/qxdK20VxyOrwcjU6nl4/7"
    "fGlPUd3h/sXT5OL+RG1N5rZSrk717epQPXe6/vhg9ly7fOrd83e68dJoNHYFaW//pCwJg+5wpjtSQ7o9EarDyex8eybvjR/27tWX"
    "p/HlkX3WvTLm/Ue5M5x7LzX95cZVnPPJzYG+KZ29IMYfPZxP1WnffXa1atu6PLPmF5PSy+jZ9tu7RxXFea68TG5eupprVl5u+p15"
    "Z1QtNQ5v3YvZ6OT4YXo5vX52q8KZdXswaPdkrTveVA8uHkRltHcn3/avj71Te1veR4QcVTrqxZ13xO9eWJ5VPbi6Pjq7PzztnVxf"
    "n+8+8Mf9Tu+kclxtTR+m+7XG6aS5rXtoUDo9o3o5mhjq7ax9c/r08GzdzmT7eV9T9g8HF0had5vS4PpImU1OvBN5t/WkO1PEVzXt"
    "cm6d8Zcmmn498+68cizuH0mK2ZqVtevDnt182tbEh6u9Xq9mPBnOnuo9O/ORofn33mGrcejt3ownklceGSd3+9vG48PL1D/cvbp4"
    "RmJWLm9e30+G2qFgm+L98YXrtI4HV5Zyftx6ljvdyf75y+NgdFTpHu6XHo8OOu3Z5rPZ2lT6pan17M+vp7fN50b/aXBfu5iXTr3z"
    "kXy+v3tbHhiDE+tkd7g9P5xp7YGgXF9rHb3/cL959lA2N5Vqu2z2hqPLA5/ff0RLz/Gz1jvXq0b7Yn5z5tv2SFOf3NvGOZqca7eK"
    "KPLl/rjZrt61zp7PtKfbxnjcb+vIOhcmzw/nLw9y1/C1s8uHsT299rS9I4e/bA6Ve7ToH847zaPx06Az6w5F4flpapZrdnXzSnms"
    "1rTWVNp79u7s2mZfe5ZrB6eV523+7li8ubb1+70DaLbbuus07Bdz5tpq7ca5HEn7R81nib8rTS7OumXP3tZvDnpwH244vxnvjiol"
    "oyua9v6dap1Pby62y0f62cA72D8/eLmbt6QHpbbpHD8Mj5o3gvV0fjnYbV22Dqsnu53Bk+aczPTH8nT7zhS96/1nf/ZiHY969vPI"
    "q9UM0Vfvrg6qZ6Nm8/Dm+tSa+bPqzex8Mjjo3Fx0D28eXtqdw+rg7nz7vDEUL9vu09St3bw02mXt9F5Sblz58NJ94Q9qew830+eL"
    "WnPvpFoROgfy/cQ/mp8ONhV5+/T59MmvXJ464t2xcrbZ790Px4L0cOiU1FEP6b7m+WPJ2vOn09K46UvDG7972SkJleP50Xj6JD4+"
    "Sff7s4vnB1201Cfv4UXSpbJ7Pm36T8gEqtiXI9XX7GpvoAye3WOpLavIBDkenzyODkYlzbwzn6WjqWPP+r3TG2l6Ouh1Lxsz4647"
    "mpSuxPapNb2fPdmjBmpzrtTs291W5/m+q75MJF/rPVSbd335VOw+NE7N/vH9nWRM9ufuU+fKR2ao0b68VMvS3qzZhGt5+9b2/Piw"
    "4fa06dP1g399ZumV60fzQTs+Gl5YfFnZfTEcyxVEvTTYrV0M9jxDmO559kO51DrU7jr8Q6NztTseXR3ZJ7VKeXuza574F+bVobR7"
    "aMq1xjGay82O3hk/eKeupdT85lxo7JX5U6QdENPJzi2/1xhK8/2T3WnNmR4Zu4MrrcNvi1V7ryYZ7vblvVU51W+QhT+6uB4Le72z"
    "iS/dH7efu2elm2OnsquKl4NZwzs1nnaV0uOhI7cnZudeExvHcNp+8nhwIJY7fXPff5wdPV+ozhVabDiT3ZF3O5Hcm6Y1bTwot/b+"
    "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"
    "2Dvk83212hhgi56canJ5vlvvV+cNsb1gM+IWW+Gz5ghTqXFeXEmUmjlgev5QWGCJPNZMXRJqW+hvErX5vIiRrVNrpa1zzTY/IidE"
    "xxzuqNHMmBNCi8hyBpbIWgdF7wk6PmZq64W4rllgV2/hHWUvrbVFiR+mp2D+F2NmT2KD1WArVosKny3MpWpKo4lKXZPm5GQ/XFFE"
    "uq3pujwprNoTsH0wqV5nZF2E2nmVnw26+zWX7+S3F0vPduWMlOZn2lDY9PqLwQxvn5n5jJLm5bwi7Qpltn0CDPqU4VqqUdxnsiem"
    "2MifyrMMP2JW1bJhNBMHk1ttR2W1ftynueJqkkgAimqUF/1eeTPsbUmrt+DmMp/Zb2rcptJbC0d2q5XxCjWiO5ZFSM3xoirNTLk2"
    "UFmrK4/1HIaZejtBl5T1id31yV2H0q2+YDbFPotrjepBo7sdbCztJoYy3jDTc2EhTEhi3VKpUY2r1JnRek538vtxUzJMtkYAChlJ"
    "C8bUF5g82GGXyWG0IWaCdZ5nq+JokNV326EldMZDYmfMqUbjfK41tQNd4hO5WRWfsusdXaSa8xqXAWy/VqvW+UohPZ5icmlwau83"
    "laxRXOG0NjvIs9WIT/DCcGaO5DG+2hb1xD7fHta6k3711FFy1qyeIdVRfi1n+OI4kzmMmPyOHEunEbmWhyNiny6wLSw/KiTGfG5d"
    "6lSIGZYVxs3zObeQsiOcrmfoWaI3m2/4WZNMnfnmQU2xOH0w80ylhu+ZvZVNNawRxw7aImFsZWNWKtJ4dqyeJ4NyJ7PijuJsUtiY"
    "+MgwG8ej2rH6DKeXjD6ttBOcTFc33XObtxqrnUXnNvNpYXA591ed7YU/aNRJa0zp0rwmCRc+f5JJ9dI+DycHbcbTfKfCVwYWzp+m"
    "fJaeSKO6fB7IgplIY7lKLkM16nKBYlqd2SbfyfaGWGm9Xi+KjdxixZJKiWywVkrB5iehTqe760W/3FuZgqKBo0q7M59NTiJzqSZ2"
    "XGa8nlzYUXZwmUkXqzra9Afnrdrsdfrl9nCgMsX1MS0Jq1o7bU4o+tBYDInJIkcd0jwu0FavYFATTLWMY2Pb0s9dfthp9i91Y5fo"
    "19s02tMnQhsbtafDiVgkBWW+p2rTFjtMC/RhMm53hoxU56tAhlOY2oAfDVi2Vm/UcCOxKTfrG8B5zdw2fxGp5m57mcpHvCBY7W2u"
    "KdUOW7Odm63T1qELxObaxcwpHIFLk023PJhsdOvcajDcKF8S8bZYJcCBiT1pvZ5mpuRGf7IulSSl18+X+0QV8NNufrQQSn1quKVa"
    "Vn5e2qTAiWUhqqRw6I+rNSDpCOCcjvcTq1R2bS1GzRSQudP8+SSo5+aINE5ybjYStvnZCOcu1fMlW9nJLLcdq+CkPTtya7ZUNwxw"
    "zp1ZiVKZ3s3E1r5c3h758YLeU5MDxkxTK/aibQ/7I9dIdVLCZMNJq6qSn7FrITPCZ0Wh07Ewol6jqnVp11DzVak9t/DqnmHyo+qi"
    "3gGiUm3csdaV8hHfAnG1mZ01e2I6NVsLM/lY25kboYaTnfai3cuNKrVsIzWZLLS0sgFHGn7It0rtyWyeyx/O1U2KHysXoU7sZkp7"
    "LF3Kh76aT9FUVhisLoexwm1n41p5MpgkjqfEdlA3s93dVqcGXUFrZNh6KrXf8dvjab7QGLORUtO9xK43vpy3rWwncyGUXKXVX+it"
    "Xa4zqFTklSgZp0XPEDF9NUoZGoNjlQmFTbUu3ytcmmaGwVJiejIxetw2QQv7Q0PWM3MC22365LnfNenpvq2lGpPZQkpt61kKy+a7"
    "5UtaPQ7AUVbs5GvrXDG16p4SQr0LcI4ZmBVSkzIYcc4uMtVtdXjc4e16i9lxE3lFKcXeeT6VDpmCks9YNU5YzfBi1jhOzL1aulRP"
    "e63Orll2s54p+8OglD/LqaPZVUbquTSn+mqne1yoUnpwXE0vljkYcEaakWmhX9bTabpotAF9z4lZlmszF8ZMQ4y5wFMX2yQEUsYP"
    "u0VZqh8p9UwW0qPJLL9tTIRmQ2sPscmpYLbbzVJnPRHFrbRpcYbOkCrWw60Vkegrw+y2UxufK1uNIkVMSimVQj6VX0zFBT/baZJJ"
    "botC9TDKboR9ndaNdOfY2ssjrjvtj9QdJTNFvbeoDfMEC/C4SZ7oslqtqtZ6qBzPZgLLgpNdoWTmF7VxY2HmE+tsYtdtglm38tPR"
    "eLIrTFc8154vhM6J4/cJjFXnhCSdOukandM0ItdSzJzat/LF7ijfKdSttYUNjguikh6v67sDn8r1+rWzcZzhtfkZPxxrbY6y1ON8"
    "e9EGi9m0tL3o2z0hTS6nVINpUalOc5vPX/jmqpoQTidCoDs9a6aWdu2CklNbU1peZUZ67qjti0dZKnI9OVuqtLeVXKvW18ktCbgF"
    "Q5scZQqUWFeJfltaLLqX0lnsUPSi2LNwRVUZ8wDEtH7lsJpMtO1FLaaYwYC6kGN9k7vsJUsqneT9hMz3jcWe405Mn8jR1cVqRcrY"
    "gGlcdKw8PZc3MyCviEyP0HqLnXDsUtVhkTtqxMQoY8fybKGUJiLDSb2EgQmJbMMoF1d6ytho7Qu7O9SO8ri4H9BCj53x7RlWygEW"
    "PEtx+uJIaGDQZcbATod9UTC73SIrzsCjdBISu+aldVITGyo1MlabPNvL5+oJviFmuMVBbK/naaFDlbKSXjZFuZ5LHYnLNt3mtrI+"
    "p0+pwprWuPSmK+WO61K5We2JvZRMaBWxklNUvYKR8/IcS521varMTG6bV2f1pmpk2uleZcpRo8uhMUrJJTJHTfVhNTtbd9uMNZu2"
    "EpagdGbYAuNXmbTaI3LgKDKadvIlsl8zmwu8J3Ori3xIK5PNSNkYYoY9bPLpMV6aKg1ZpEctvqavs6XNlmQrTAofTJi1qe82GYtR"
    "1jujZzWZTXukdLV+CvCAWqlfOg/rwwRYxS154rISaPewNk8J6nIpVJlspTrcV7BepctWWvnSJk82KyRf5gl8Nk5MrQaVXmfap15B"
    "2/Rqc45OdAyNto7KpiPUyuOjss4Mmrtq9oI1O7SRSUj9tNirTDqdToLRM6uK1FF2LNhA1sdZUy6x2cvF1Mb5g5DZXPhVtU7MREtK"
    "XFKXYzozIqXmtDgp7KxOfjDaZ2f6TixWUhmrRQgJLKFnKqn5ak0nwIZczjVyrcxEO2lsmyvXzAqXOmjjcqN3UbfrOZmrc9qM6q0o"
    "WV+TZK067vO7vZgbCYo51zPt6mK832Sqo0xL7u1ytXqrmS+UuBZ9pqWuMm9SAmAfrTqeVROp1Eke59QBo87T5wmXzlDz3Tkr76eZ"
    "7nEsTLjWZCz25VSCBRJc2eR4htlOa61KccqWila2oJQWDWs37GhCrd3G2f0kN5hi5DlXGK9lZtdrpoen2lQ78pVjtVmnR6npYpAm"
    "Orn2CU8zbfKSSSlt4axf1PIiz3CJWbdM14+F8WhAMNn0vNJtEdV2/3QYHQ0RgHuo92eiAGCnMmmtW+/s1JHGAb5vnQq9fgMn2goz"
    "OOOD1XFSrE6H6XFGHUzEsdU/lAEh1dTDwCor0rGuFs32itux1U6b7V52rTE1ADI0T5kyg80LdH1mip0ztT9JOrEilDmRwmvdlSn3"
    "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"
    "VyaNlvI+yIv9+qFtCMZUYavj1TQ/3d2+5sTJqLZ/5cb0sF8uCdWcWClzNNPrrQ4fz53Rju28sVZz2drL82XTpEwmx9fb79VVYb1T"
    "lLWa61qbar0uK6+d5uJdkcq9ajMr9hubRY2bq2J+9SFZ2VVNrc0H48Yg2wdC6+urIQxBL/jaZLQxpN6BYwfLyUDfU81J/YVr9Cu9"
    "Xm0NcHzIPXa0+uhWrV6pTOns/Pj+ZuqLaZvfde/p8i09GUm7lfxWa8iFw/i4N1U+y5WP28501uBlU34dbUtf2svkQ2iuV5Twftv8"
    "OgL9dr4Syq9fC7rQndekpUkVS8OSLgOxWXjOVT9GUqGgSLvmatuqiqvOsGUODvR+3hDzyqi4XDQajdIsN//SRvvnQlNvTnqdt1xL"
    "Hn9267XF8euLrdUre2OtvFumfj9vcOptjqpX2CHdmA6YvUgvNKZbe1l1G/y+Uv2o1Wcsc/+WZ9rCvGCys17XqCqtL+Hwstz0c9Lk"
    "q7lblrvv5e1bSzcKs+O+fHzeNUua2tSa5Qp7eysWZ+XOsjStf7aVkm7selme3e/KtcWkXK6/zelGrlnYHReL1WvtZZ4bVF+Z6lce"
    "nF6l+t5oqqbeuNXXwhZIQpV7/pPabUeLdtnq3DONQ0ubHm+fP8rdz2qbGrfej4XyZ00CC3BaOlrj46i3bfaf2Wplo3yUjj2raOnt"
    "4ZtYvr/vmbkBPbEmFqd9Zce9bG1dGDBvw/lG71TY8Sddp8fq0Jgwr0Z9YKp9rvy+qOVHnU3bMjhxelS1YmHSWt3fL+tVRfyY0cZ2"
    "3dJu8xSz374qBe5zuBnn951ZpSK/yNrwUxgJ7fFb0RyNcxNhI5narqLcr4a5W/qrWf/cdCbd6ap40L96s92qLiyE/HGzyLaa46Gh"
    "c/VmRZw+F14E+rgx8xPzS5JYracxXwNtSfMNpj7orMfKZyl/6E04lc7Onm8Pw+5zozrXBtsc+N+r3t1paiP3Ro/eW8XDRlpMNGkv"
    "jJTt9GvQ/Wy3F0e98zq8/Rj114eGMVzmteHHrbIHAtBhqyqzYVNdvRoUNTDa3RVTEvvl/ahWUaXhJseuvurbt5fV8n0xLT73C2/H"
    "HvPZNz4Hw8Zzqby0nlfUrlBrbYelo2QoYGBm4y1XLs77pS96+Cx/cM3KR7u2V1RrLzCtfP9+cswvefr9nVZeha/u8pCVR1+cOdK+"
    "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"
    "2ozaAg=="
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
