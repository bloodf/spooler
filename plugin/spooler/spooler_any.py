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
UI_PAGE_SHA256 = "6eee88ad3488b3a0d56c07db9a8e728ca902d172a9d6b9adc5d24bcfd6564ceb"
UI_PAGE_BYTES = 1208525
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
    "YjvxdBxCl078GRB8GOu477/06hS8vdJxO16v0zj0Gm69XW/De7Pe7jYx4n2n0Wmm702K8Z7mb7qNegPjttc8KFhJ35vdTqOr8mPc"
    "9lq9e4Tx1vEd2q13a1C+5taxfnhvYYj5nttpUz3qvcmx5Tn/UUvEmhf1Hbbcdgf7JdtL37k/Mr/sb5uGV1fjaePwoJx872B3612Z"
    "H/rLoeV7raMcqDZFdJ+3g6tmzBHdF8s0ovsTRIanNPtlwdx1fCmL4z5dfmoc91EOYfGKpAFdMdmfR4yaEfnTpiQgJIyx/wZM7bmt"
    "eruB4G+3O732Yc/t1mu9Fs1cp93Caaq3Wvi92Wx59YrENJ6u+pHERM9z65CgMBfeIXu7or33up0U0xWmipUgMVOuFPUu0ENiKmBO"
    "z214tVbzSCKVrEoinSwqkVK+S6SV+SVSy65p79R1lZ+HdiQXjRx6DnSbMHfxoX5TnzLmTvKY+2a2DW8RS8qwdvTJWHutsBZ9N38T"
    "zyiSatGr87MxX+h6MZ3Q7o3m3Tl3TOwKEGwi1D2f+IuISsPuSlEwS7OYnCari6r8vjUfm/A2ubQVO60ljn1Ve1uj3uFu69Uh71Wb"
    "ndSKurBJTO/f5V3F3uVbfTQb4W5E6YfnUTgZF76Wumkdv2PhVjjlTCGYxp2Ut3jlFBSyOuN3ONCnnPRkNptEuYh++gSOw3CGV/44"
    "Zsa86IxJdGkQrnNzuiGn8wh7QKG47qIr8pWUhGWtiOinB8LflIDZIA1bypBMne9geN15eIF31ec5Dzziol/iiAC2j7Qpt22MFLoW"
    "nVN48O/pX9o7hBI6fdE79zSzdrb28IEAf3Ha9/bmE472VZpFedQR0/dgMEi97sgZpYhp1LVin7xyqB3kYZSGn70IE4Ije8TMgsPm"
    "W9V6F4o9QmCdpytM8xOLt1fDPI6qu9bO/EC5BEJHfeQLIlu3Y3Asq9NF5fRQZMmQSYwcDShgCVd4qou2O40PKYvCFIENc+duOo8u"
    "ojiYkLOGfiJUXPTo7GCAju+nMZ3cK1IMPNSlbkqJaB7znOeGR8jTQpOThPkkM3Jo7ZEktsWYm0480KZpStnweJZAbR6t1lkttmNK"
    "CrMutKBnaVrqRUv0wSldYZC+GYFyVSaySnW1tdhbEUmSW0Y/jCkNK/PrsAEQyNWkfwmN3AzFFkGGBJVUr2VR7oFTQA7177Kzqi8b"
    "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"
    "zYDazS/OULv5yRkiBcfOUKx3/QzFC42eodTSn54hAvinZ0hTNn2GYoWH/2B6WXyH7fuhxrcevE+hsZ3QTW838LviUsGS9ELkJ3+9"
    "bRnvU0n2Chem7KcxJd+jetINdjd6GBPm/+jWKqwRNBMoJ5OEkwQozv0lTMUZOTaWdH5gTKnrqkv5eQNexZJvgAywheGCOna7rVYg"
    "06xUaDflCm2I8GANH4YGCHeWSuCg7GNEoWSJVCgAO4sV32tIBqj+rBjJWqDPawiN7rrdcypCk0c1fD2z/2rg7JnsUgaVgVXXs4M3"
    "k3npwitTcnTskNTQMd/RppTncUu9yeLQAFN76hyLlsG2RIHC0GjY7d6IEsVh9OA0vRfxTHQEIPyCgBY56neqTiBKUCce7NEdK0I9"
    "w+iKoEkVK3XPih1XH51a+KArfk4NQrA4LRYrpT5bG9W9KDmi0JCpZOsXMI0vbl3jQuVdWh/ozcL4g6oreHw2TBwOh9H78u4FrPWp"
    "f1Wh+5mW0+46QW8iN0F9AU7x19zdixLzDnj+1qn6bVhFrAlLRDSgWWBTFgAVw7rBFKus8+nNnA0OdUYjTqxNtTv0VtQjNFjDXkq0"
    "DEmf5L+BT4U+NFHmMJiiQwPHPBQo6LAn9rz3TFhqXYCPPpcAUqZTmydzQU4bEAHSCcI3rMDXkeF4/Y5DPY5MFgzqSakvvsH3KfsN"
    "3m3vw4cSqRJ137qIuG0TQOGOFrMR8jNhVsJmaIbTlhW1gLWoq0Ec2mTJ8hFq6+Nj0uFODR3qtRDdJcq4/W71CU4zhLvfM+SF/kng"
    "dlxQ6T9khV9h7rKQnGwJM8QeV2mPgdQj7y1YDVuBP5i4IF1tBgGEI/rXv6SGJzr9XjjBr+4muiKdejSxuJtqdOArXE/ShcGWeVaZ"
    "xR8XEv28XmDwiSr980b/vFxkpPLw9Z6AcZcdsewwhHvbidCf6HWBVYH2O4eUDZeVfE/M/2PXm0CBFkpWSQYrYWB5Gzy3TFDM9OiI"
    "WzYZoz1xH1srD5nsRMcJW34dhi6AfItmlrq15EQc4YQj/JwWZa4p34dkFim22HRlWaCBZSNXjJzmA3IphcfXFSUJOQWfK2cNrHNo"
    "dwlx4c9zJ7SYv6VG4HdITyamr/HrVVJw5v9myual+7Gb9ULya/mjuPgxN5slPwnT7XTJ2Yq28MdMPnR64Di1zMbDDewinOCkvuup"
    "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"
    "HhROtvztvcrdzPPL2aB30i0cb9rNW6/v793u7p0/HpyFm7Nb1dnB/uN1q7K5fHBVWbt4Le7Mr+1VVnaOb24PaluL23Zl8e665i7v"
    "Xxyf3bQGs0sFf/Hw8PnUX25X7qr1F9tfrmzOPL40z5+395f7T5e7tY1uq7tT86uNtdfdavf0wF957HbvbncPNlpz03cr/cHduns7"
    "f3BwNX+202yedi/XXl+29m739zamdw+qGy+1l87T0+2zd3Jba6wVD0+2H4tLJ5fzB435sHL3OP3s3D3u9o6qZELa7tX2a/3wtu88"
    "uvU5AsJO0w6u+gtvjcf2s723XH2+bde6i9W7ub3txs+7Bedm8eDwsnNz8Niab1wU1i82Fxb3fjp75099e62y/LN5tT33tn1Wr6y3"
    "lm+26u7F1t3t86b3uDy/vHd7tD/bb50sHO9c718eFrcG87OF9aOZo+bGefNl+sj12itPy72D3uH5YjuY39nb/jl7035eP/dawfbC"
    "kn9WnakHey8n1bmLt+PWwuPh4cn8QmtmsH67frDx83hzs/HsX7bWX16PmoW3/dZJYWHRma0v/NzbuF3ev/T26ndzBxvXm53l/Scg"
    "lu3n/buZ63D78i58bW/1b5aLlytPg7W93daNd/x0u/d6txY8nfaDk8fpSmH65Hx+fS2ozrcXHnu1lemn242724uT4LT41rm8aO5f"
    "nNxUnevj6mOxMne30N4+3ejOX+2dNK6O9g4b097x+XI42Nl7mVl66lx7/a0Nv9YMmgtzpyuP9sbP7c7N2+LC9NEdoWp/rXLoXRyf"
    "H1dvdq92CIWd/nTn5w9OF8421u5mdhbmztfnTw5fL4+3OvbF5uzl/s3229FuO7xdJPS3teU+bXYXZvYuTo5uT55OOlv7rY27Hb83"
    "++ivVedPLmbXC7WNy8pJ8W59v+8fHV3XGo/O7knh+ap5cLiz+VI87JzveytvN7crzaXL5t7mxfr+S/vZ2bm0+6cnh4WrtefX9svb"
    "bHi6fjWYm391Zy7373YXT5zztcq0t0baq3b7xUP7brdTcfevCtN3h649+7rivR4tNiu7y/XdLbve3zzdr1X7lyfNc/90cfqo56zt"
    "7J9u+dXu8oL75l8sbbTnV3Zfmgtk52zc1p435+uv7ddX++64szlw39Y7J8274vzRmVe8HDhuYWbJW1w7ftx53dk4Puit7d40GxtP"
    "r29btVa3vRZcVo5O9s6Wa177dC/cv6x2t8/396s3W2Q09vPa6eKi+3Ortb13uOccVSt7i61zf6d1s7U73+1WX+dm98hyvBnUinu9"
    "lb2ZzeJpe39QX5++bN11zv3C4ZlL1kFrs1Jfu17bnvWqM+3bg+LF9Hmt8BYWu6+dXvv8pXJ4cndSOL+77lfWw8HL1aAVLp7tt+4q"
    "N5XFla366cbJwtVxcPu2ctC9rlxtNdqzhMlO98+CM/v5anC2UiueLpwXph/3C8eNyu721e312/Hz1e1L4e6ytbg1Hx5sefvXZIXM"
    "2/761XQ/aK1cL20f3QTbyzvF3n5QfLxtBLcXV72b80N/0PWKj1eLN2v7jZujme7m89bT3W73bnFxzT+rr4WnLxe7h4322fHSVrF3"
    "57R+Bmf7PW++vn7UOLkZPPe3B7v+6XF9v+Udth+3w7vzpbnGpT970Fqs2q2ry5PieXPtZM65ar06a1fLi13X3vz5s3LbPR3M157X"
    "W+Hu4DzcblcPBkcXncXuXtW/3nyzbXfh8myxfT7o32y+rLX3m9WtSq//dLR/fHVx/DY9t0ZoY23mpnp9d7Pm/nwjU3T0bF/2vIXH"
    "6/bgcG3LXV7Z2LSD+dPj5cfLtebsdqE5+/i4f3XQKjyuPz5dXjW9ld5t9+Jl0Jq+aBWL7aeDztu8uz67f3q+ffjkrfeenPXdq8Ot"
    "Rm/+5Oy8VejvXS4/1vy1meeV9fWtg5PFztPseWX3etvprk3PL8xsndo7bzNz9Zubzcb2+ULvde7ysNo/OThant3odW+ndxdIa53u"
    "XH0wE5z6twe37kZr+m5962bjZqdW92+fnzcb7vRco7Wz3D5cbizeLlxfrp2vnB7vefVK+Bj6PzcPZvzq1sFO4WB+/6rdOZi+qNSX"
    "Tp6b6zedlb3mbsPbOt0KH5tn24fFw8eTQ7+zeHx4Wd9tN5ev2ydHy4Pt5+ZFsLPp9ey1y/bg5HT6yXvcuS5uVAYvjc3d9eua0x0Q"
    "Utty1jec6fW1m7X5pf+PrfNYblVZoOgHMSCnITkIEEmkGTnnzNdffGav6jmUXG4ZGejeey1klc92/Vr0zHBHLwwlEZWfUTc2i6AU"
    "xsN6yz19b+VXJfqsPzvzGOVa1bXrWUgAem7sauPmkqVPN0gCPkjkEN93wFHAVrKMtGfi6aMbVQWZavqt9YjR7Sa2RTk3StTZyNmy"
    "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"
    "r/WerBe5vQ+iVuLnkPSFyPrE9ATsKyenL7j7qF/OHrZoID2z5HmZXc0saNafMjN/Hr5+XKlA7w9b0q2ZzMxMAPxRp+NrhsIWHNdL"
    "Uhh9P51MlXwgbWuS/cfem7YnkiuJwt/Pr3D107cGXmPIfaHaXccGvOIVvNZTb5NAspiExJnJZpf/+1VoyY1MwK7q03PnmT4zZaQM"
    "SaFQRCgUCkn3j1fVxVnXvbupNsuz48NhYT6Vz0xnb688k5wm78y59nlBni7K/Xl3u4QIIdv12z2l551t3/CXhT1vXOvoTU857x+P"
    "7daCe3Ir0vjpWihoTQEZYAP+8ebl8bF/2nopT68f7s+GgntTlYe1o1FtvN1W7yV38eA93h2dzMvdu6eXxVnPuql2LfdKf36SrueL"
    "+wdpr3Ug9fe04ag60LoPHWPYv+HVa28wFZt6R9MPjJFcHxwcP+51t8vtrtOqXrSMkneuaoWu1hP75SPvReyN5/ulqict7pXT0z1+"
    "pjU79ct9blQzCyVj7N0/zbXTjmkeDw5P+53CxTZXrvYO5iU03U6lY9t6Prp0prP92Ux7uuhYB+eG+3hU1ivTflmZSnPFvrp2ru/2"
    "6ieHVm9Rsvra/dm8a1dqrTLSD6WLstXulerOYfOiI8r6SatX7YwGuvR8ZZrXgliaLvroi3Fsbrfbwxt1Ph0Ik8HInVdmI8szh4ue"
    "dd5/PEDGuVd3B0PvwOlud5DWMcaH/NjaP9KntZPb5vW8UBFKA3G/UN7un6nDWa3ePyxUuZPu9UJSF5LZa1ZBAztur73PN5X75/On"
    "rnRcsG/G19Vny2l2CuPzC/XsvGTwF/bT3ePx2cME9X+7Phy69/f7fensvj994MRBrXduOW1L1mdq75TT9m9u9BNFOO/tGdt7Bw/3"
    "rnK34O+b8pUhlPauuZe7yePL6GbRv7F7ztn+CX99ebQvHsqefiINbi6Fk9r4pl2zpUfj9urldKHcl/jCQ1M1L/ZLwkXlbK6em+3T"
    "WvsOaYp++/bqUe6VyseTO7n8OJoK57e10nR01HJe3M79yelE2rYmgjxvlutPozOx2+P37s8ep53J4fHzy0thZHL26ZFRnp6daYtq"
    "TW3eiwc3AqdW7+edCjL6zi50sSocHup6d3p21D8Qni7VysViVut065Jy1OycvzyctY7ve5ND77k1OexN65N7/vZcqHG3tZf+8Eyt"
    "VtzCkHcOlcuL6QAxXsHpS0/2Q/NcuB7cjPdGF8K+6Zx0T9vSXbVzINyfP51c3sybT4WriuoWBu5Bec7J19Pbl6uXE/Vsfi63TlpH"
    "TakvCPqgcju+lB9tJA6SWmh2lTYSmuPT0/JtZ2B2ttF62rZ7e4VL+f7hZSQenbZn50JntF04lwq2pWxPnua11nXLeFEet+WLweBm"
    "dCa4J73R8WmpXZhU9KNyRZBd6+RRP3Ke9Y68rd/Mt0ezSUUaXXbGj8L8bDaryOqg2zwq8JVq4eW+drwYLMr2yZVz3OI7R5fDx/p+"
    "R3uWzkYLZNTWRm3xpuMKduFGH1yNL05nxuxoqFzP6+Ll1B7vm8ZLudoalh4fr8dtu7l3Z/SH+4/7vSdr0a1e7h/0Bk/G433p8ezp"
    "UVscXta8sqOVrefm88GzW+3OJPuO66p6obZ92OMvO7XmviQOruTOttK21AfzsXQsjU/P95GFYXui93i/b/HTg+r+SffFamrXquSZ"
    "/QFX1bjqQbk0lY157UI5fLDd6z3bKNTloXJzb6L5cHTLa92piEyP29nc7T7sT0eaNa+M3O5+t9U7ebm8LLin9wV1/7nZUtuueMUf"
    "1o6q53b/3Nk+Mw+7o2GLP3/o163egDeunXtrv39xt3g8uz1+uhp0pk/mSD1TxWdj6vb4l6nHH19fLEazWvn6aIwMPm7f7RZuhqfH"
    "XulaGVRvzuxau9p6Mh2pbF+osvKs3FTuNe/gsTQ83d5zm9OD88PB4EwZmec30768P3BuuHb9aFyudarNdvmyr2itg1rt4KDLiYuH"
    "7elAqUu3xn5t9HJ9L5Tu5q41QurfOTsxK3ftJ927Vcfn/J3VGhW8x0fpUhCH9fueWD7tnLr8hap17prT26t9TVYvyi/X5556Ilse"
    "d2Gb+qm82D6uPR6dF8Rn4Xz7/Io7FQ75kSAad0+P3OPFwY1ZFXS9NfD0xW0f/du/fjHVAppLzkZX4/HZ7OrxgCvty4ozOrh8ml7e"
    "nyrt6cKSy9WZVqiOlAu7500O58/1q6f+PXen6S/NZnOPF/cPTssiP+yN5potNsXbU746ms4vCnNpf/Kwf6+8PE2ujq3z3rW+GDxK"
    "3dHCfalrLzeObF9Mbw61bfH8BTH++OFipswGzrOjVjvm1bm5uJyWXsbPltfZO67I9nPlZXrz0lMdo/JyM+guuuNqqXl061zOx6cn"
    "D7OrWe3ZqfLn5u3hsNOX1N5kWzm8fBDk8f6ddDuonbhnVkE6QIQcV7rK5Z17zO1dmq5ZPbyuHZ/fH531T2u1i70H7mTQ7Z9WTqrt"
    "2cPsoN48m7YKmosGpdvXq1fjqa7czjs3Z08Pz+btXLKeD1T54Gh4iaR1ryUOa8fyfHrqnkp77SfNniG+qqtXC/OcuzLQ9OsadxeV"
    "E+HgWJSN9rys1o76VuupoAoP1/v9fl1/0u19xX22F2Nd9e7do3bzyN27mUxFtzzWT+8OCvrjw8vMO9q7vnxGYlYub9fupyP1iLcM"
    "4f7k0rHbJ8NrU744aT9L3d704OLlcTg+rvSODkqPx4fdznz72Whvy4PSzHz2FrXZbeu5OXga3tcvF6Uz92IsXRzs3ZaH+vDUPN0b"
    "FRZHc7Uz5OVaTe1qg4f77fOHsrEtVztloz8aXx163MEjWnpOntX+hVbVO5eLm3PPssaq8uTcNi/Q5Fy/lQWBKw8mrU71rn3+fK4+"
    "3TYnk0FHQ9Y5P31+uHh5kHq6p55fPUysWc1V949t7qo1ku/Ron+06LaOJ0/D7rw3Evjnp5lRrlvV7Wv5sVpX2zNx/9m9s+rbA/VZ"
    "qh+eVZ4L3N2JcFOztPv9Q2i2177rNq0XY+5YSv3GvhqLB8etZ5G7K00vz3tl1ypoN4d9OA83WtxM9saVkt4TDOvgTjEvZjeXhfKx"
    "dj50Dw8uDl/uFm3xQa5v2ycPo+PWDW8+XVwN99pX7aPq6V53+KTap3PtsTwr3BmCWzt49uYv5sm4bz2P3XpdFzzl7vqwej5utY5u"
    "amfm3JtXb+YX0+Fh9+ayd3Tz8NLpHlWHdxeFi+ZIuOo4TzOnfvPS7JTVs3tRvnGkoyvnhTus7z/czJ4v663902qF7x5K91PveHE2"
    "3Jalwtnz2ZNXuTqzhbsT+Xx70L8fTXjx4cguKeM+0n2ti8eSue/NZqVJyxNHN17vqlviKyeL48nsSXh8Eu8P5pfPD5pgKk/uw4uo"
    "iWXnYtbynpAJVLGuxoqnWtX+UB4+OydiR1KQCXIyOX0cH45LqnFnPIvHM9uaD/pnN+LsbNjvXTXn+l1vPC1dC50zc3Y/f7LGTdTm"
    "Qq5bt3vt7vN9T3mZip7af6i27gbSmdB7aJ4Zg5P7O1GfHiycp+61h8xQvXN1pZTF/XmrBcfyDszC4uSo6fTV2VPtwaudm1ql9mg8"
    "qCfHo0uTK8t7L7ptOryglYZ79cvhvqvzs33XeiiX2kfqXZd7aHav9ybj62PrtF4pF7Z7xql3aVwfiXtHhlRvnqC53Ohq3cmDe+aY"
    "ct1rLfjmfpk7Q9oBMZ1k33L7zZG4ODjdm9Xt2bG+N7xWu1xBqFr7dVF3Clf3ZuVMu0EW/viyNuH3++dTT7w/6Tz3zks3J3ZlTxGu"
    "hvOme6Y/7cmlxyNb6kyN7r0qNE9gt/308fBQKHcHxoH3OD9+vlTsa7TYsKd7Y/d2Kjo3LXPWfJBvrYM9dcjPlfLNZcswuZfSrWyK"
    "jj4Sn68m1adDoXr5Ii0K3eOKJTjVQ7H/MDg9f5pvF8ZSWdelQcepPCkPw21zcNvpdJp3l7dc6VyTDkROuXw0z16ubf6w9bxdG7Q7"
    "5vmR3Dy07toF5e55Ur1WTUXqXEr7Hf6s5c6E2eCsNiqNJqWaKfOTp9l0T+NOboXZ3k31rjBTBaTP75XKsK7ys/ZEHyxO1ILunM9q"
    "pUtnezi7V5sHJ6cHh0fG40tf7KGBKV+/lN3rI+FiOlNqR1Ln4vr48K4s3XWvbyZqqeLq3HldP6lun2mlQfNWPzq7L7/MB/tXs555"
    "0JJPawd7ozunooljazicz6R97nTwUJld2+XTvYtbr9VeHBZUq2O/SFPupDwolJzjMl8aceOjg0tpuGeZk97x0Xz77soenB5funO1"
    "q8wLhZPmifVyVHjRh/3mdPC8MNTjw6tDp9cW1BOj9LDtKJXWrHwiX9ePWmh5MNdu6s7V3pP20L0qI4vi4rhyYj/ct1+sRWG6N7uu"
    "Xh63Hl29p9wXSkJ9eHvhDZX7crt38zhtnw8qTo/nzzqKO+6LA+mqrj+2OoJulgb2qF6rntaenksnas2s3rhTTy6dHx67252K5A1K"
    "x62n8b1eq02FI6+3J9911IeCrg+92cXgRbt4tDpX46FlHl3L3NHw9nH75u5AlLc1vrD3XFInXG9v+0rtzu1Rq/+kT86k8cPgbHRW"
    "tiudx2trMRC9Ye20+qLfHZbdjiYIt4uJPBvcXCwetw/M9rw91dy+sH1Vvr7guY7d3jbKTye10wfJumyduTfmcDjZu3uZH27XhOtH"
    "+dEy58718XPhfHSkH7vjl7PR/Ixzrw9bRnuv/lSoD/qL6f1hda9yXRImp+qgJu3d3AtG27NPO/L5i3XbL5/eObeufv00Oejrj9WT"
    "fWlv7956kqtH+/1qp2Icmtenl4Pj4ynSAYd3t9rj+KU3b03UweDgUXu8r6nz8YX4fCJeIXPiaNo/Ufa9Li8501qNv9Xlw86kqzXl"
    "g5uLKT/wSlNufqOVWpW727k1uHTmL71n97YjNpVxAdn5B+WLM2vCHzxwoz1Dtfa2rZttaZu73+dbFf3Aujw64fY7VvusPbu2ribz"
    "WvlJ8tzhI5q+r6z7QrUw5C6aXf4OTYJIeZe37yyTH4v33bb0cq881FvlsvVUmW8PO72Tfne2vy08a/U+L4+QTaGY5dHZcHh4rI8u"
    "9y7ncn9/r169PjzSng86w/3L51K75hq9vcpztXowUETlabh3vrjkKv3Lk+eDgjkqdPZOukbF2LfHjnh/cW3OFg/qkfFUHonz/Tv3"
    "bjG/bRfq25M7SzZs/ejx8FzThb1zrX3Ml56n5on5sHD2bff0eHx/XZ7WC1L5QK2pVl0sLfbnlcLzeHFrDy5OCoOW4hr6rN1ajM6c"
    "y4I0vJRnV52C3jme8vcPhV5naE9bztHJ2Gh2C/cvVakgdup2/ep8sK8NuuPKs9A7klSpW3deWma7/mBN3Pux+fgwF+bbp+WT0n5Z"
    "PXWtq47e2as8dNTjdqsbOUyy28jt1Xf74zx5MixDnxJr2dZkOGq8ZXNPwfNiJM9/XCz8smjsU/cv9q4oqejUXCS9+UleusRvpcbe"
    "2DygbxDEX9l0bcc7eAc8eejpPSXg6n54/C/52c0GvM/VIHjgBxzTnyHtmUbbdFZ027a9Vd/d0FuiCZ9boZdJEx8QJe3XVtdCgErr"
    "6mra7cWamgBkbT2kz2tqIkBr63J79uwAD++ZOZqkDQQXBrwYk7f+1gCXUK6zP/E8e7RifAFyD14bWQ0ZQQCudeqd2W3TXQO+126v"
    "rbYTrZK9PEcK4NcDYxQbGvMSfroRrVE8N/l5XOENCXHLmrTNQ8tuIosfN7KCDASLo834KAy8jgv8od2wVgBdU6drWiYWeqDXqhrN"
    "+dgYtVf2Gyk2eOVl1SPDjj3bAOTaxI+Frnrz2Ac6bvkcEcObvr6Ycwgg6CailFcwEKq30u6vkAcYXsd+MVeJgWH1u6ODMFRcZVpm"
    "B1QmoukapckxoKOw6kwbIJgJwip0FWswGVmpL/vt9qqeMo28t+6xZUL2VU8tLz3KSV/X/Nb4ncyXbuN70quV+GG4Lxn2NhyF9R/L"
    "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"
    "mJTL1Nzo082cWhPLqqmt8llzZvSzqUqVqwDuKSU643WFaXWqYl8+Tth9slvhm0r7bJY7w2PjspEX5VyPk0ZiNzXI5Lvp/JZsp4WC"
    "XDkUNtW6LAg1hjyNF8Q6kpMTbGy+W/OMkI60m9MyK8/mgsh2jheJG+7MjXzUq626Mcue9kotPzWF/b6RO7J6Y6v3G8m+lK+1xVFO"
    "2407e+4gK9X6PJPJTRrVeUeKLUrx6nhh6szB0Gb946mgMTOFq1DreKs/rbGJ+GFvJuPUqLWuFSZ0rk8cVjVmQmwTncoc7IXjXWpB"
    "NUpsUiuXFn2+tM6QbGSjUrt6g+VauabG7ihO1VYbrjTScpXkuUxMk4NeTepnjW5i2jTLNRaIjCmzJJVqRGRWHY47GYaYj2JKqrTZ"
    "NPtbenZhaqsJZZDKdlOtTTvt2Unvq1KvnZQq4JAem003zHZAdlY0U+Ma40yhrEb4be4IpJlLpCMvTu1KvNOtK9VmNm2elfRFjJWU"
    "7J46dlL6ZNIsaPpWm2qdSX8op3dHlaxmGuu2TG+b50SfFPe7obHjx7lRJjZkm9UMkMyqyVh9lavV1k05s9XlCslnDnW5AkS8yaDD"
    "8IdDQ9IS4/mRiangVL/N63kiISYGcU7uV9PErqtWEwptsuT0PJCzTH+sUZ1mdjEvZ0hp3uoS9e0pLZ/pTUOJH+ncpJ0oZGcDyZwI"
    "5HFVFc6RRVaYbrT8qqdzjX5NoiYlxWwpg2E3k56o40Grn+ivNnpqr1dANeqhJDbHq9XB7Fbbu5pssDMyldXoc6tVy65y7LiRNnnp"
    "3Gztgeho7OVxJ7vOZ2s1OT4+iPMtpRrxHBCK4nM9UgVCXo6bV+rJjMaN9IFcOa7me9ms7ybZbbZQpSvbfXJ34Ls9ZQdqnhvbCSck"
    "BTPDd3dlcZ9s8OUsm91t58ak214fu7SY65OHXj6z4JQ4bw52u86026iOaulFelyuLOoNaZvhWv1SPF2jtv2CUD6q8Un/0qk22sPG"
    "ecxUzglSrHcSymq+FWdkLb5lJ5Q2nY3pZKlqntVWuUxyksiAM3Obi51n88x4ejIqBSa9X+/r5cVuW2pJbCrVr51GYFfIVEpDsM7o"
    "Cl1rH/d8dhUfzgaZZL1T71N1MTbU2EF5lJCBvCEMMkSZAee87mzOCL3MoqcldosN0x8O+h1lltPOOhUB59Barr2tnLTx4ZDuqlM9"
    "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"
    "X//1/wHJ9Cns"
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
