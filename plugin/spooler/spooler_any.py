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
                # The printer presets, for the Printer tab's "which preset is which printer" choice.
                "preset": str(bundle.printers.selected_preset().name),
                "presets": [str(p.name) for p in (bundle.printers.preset(i) for i in range(bundle.printers.size()))
                            if p.is_visible][:64],
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
        if not pid.startswith("auto-") or pid in out or len(out) >= 16:
            continue
        tools: list = []
        gates: list = []
        for unit in (item.get("units") if isinstance(item.get("units"), list) else [])[:MOON_TOOLS + 1]:
            raw = unit.get("slots") if isinstance(unit, dict) and isinstance(unit.get("slots"), list) else []
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
    entry = dict(printer, slice_fill=saved.get("slice_fill", True), managed=bool(found.get("managed")))
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
    settings = get_settings()
    saved = settings.get("printers") if isinstance(settings.get("printers"), dict) else {}
    seen: set = set()
    saved[source()] = parse_printers(value, seen)
    settings["printers"] = saved
    moon = settings.get("moon_slots") if isinstance(settings.get("moon_slots"), dict) else {}
    new = parse_moon_slots(value, seen)

    def free(ids: list) -> list:
        return [None if s in seen else s for s in ids]
    kept = {k: dict(v, tools=free(v["tools"]), gates=free(v["gates"])) for k, v in moon_saved(settings).items()
            if k not in new}
    moon[source()] = {**kept, **new}
    settings["moon_slots"] = moon
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
            "stats": stats_settings(), "printers_rev": _printers_rev["n"], "slice_picks": list(_slice_picks),
            "slice_map": slice_map(), "printer_presets": list(_ui_snap.get("presets") or [])}


def live_message() -> dict:
    """The Printer tab's poll reply: live state, the booking list, and the saved printers when
    Spooler changed them itself (a slice filled the toolheads), so the page doesn't save over it."""
    msg = {"type": "live", "live": live_poll(), "usage": usage_state(), "printers_rev": _printers_rev["n"],
           "slice_picks": list(_slice_picks)}
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


def moon_found(base: str, tools: int, managed: bool) -> dict | None:
    """Note what a poll found on the Klipper printer at base, and return its Printer tab entry (None when no
    preset has that address). A change is sent to the page, whose slots to set by hand follow it."""
    printer = next((p for p in _auto_printers if p["ip"] == base), None)
    if printer is None:
        return None
    found = {"tools": tools, "managed": managed}
    if _moon_found.get(printer["id"]) != found:
        _moon_found[printer["id"]] = found
        _printers_rev["n"] += 1
    return moon_entry(printer, moon_saved().get(printer["id"]))


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect&print_stats&virtual_sdcard&"
                       + "&".join(f"{name}=temperature" for name in MOON_EXTRUDERS)).get("status")
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
    doc["u1"] = heads
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"])
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
                    state["book_ok"] = not doc.get("u1") and not connected
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


def slice_map(value: object = None) -> dict:
    """{printer preset name: printer id}: which linked printer a slice for that preset fills, chosen on the
    Printer tab. The saved one when value is None, else value cleaned."""
    value = get_settings().get("slice_map") if value is None else value
    return {k[:128]: v[:48] for k, v in list(value.items())[:SLICE_MAP_MAX]
            if isinstance(k, str) and isinstance(v, str) and k and v} if isinstance(value, dict) else {}


def save_slice_map(value: object) -> None:
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
    printers = printers_cfg()
    printer = fill_target(printers, host, preset)
    if printer is None or not printer.get("slice_fill", True):
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
    for slot in used:
        found = match_spools({"vendor": "", "sub_type": "", **slot}, spools)
        unit, index = places[slot["n"] - 1]
        here = printer["units"][unit]["slots"][index]
        ids = [str(s["id"]) for s in found]
        if len(found) > 1 and here not in ids:
            picks.append({"printer": printer["id"], "name": printer["name"], "n": slot["n"], "unit": unit,
                          "slot": index, "material": str(slot.get("material") or ""),
                          "colour": str(slot.get("colour") or ""), "spools": [s["id"] for s in found][:12]})
            log.info("Filament %d matches %d spools; asking which one goes on %s", slot["n"], len(found), printer["name"])
        if len(found) != 1 or here == ids[0]:
            continue
        place_spool(printers, printer, unit, index, ids[0])
        changed = True
        log.info("Slice: put spool %s on %s slot %d", ids[0], printer["name"], slot["n"])
    with _slice_lock:
        _slice_picks[:] = [p for p in _slice_picks if p["printer"] != printer["id"]] + picks
    if changed:
        save_printers(printers)
        _printers_rev["n"] += 1
    return changed


def slice_pick(data: object) -> bool:
    """The page's answer to a slice pick: {"printer", "n", "spool"} puts that spool (one of the matches) on
    the slot; "spool": null leaves the slot as it is. Returns whether the saved printers changed."""
    data = data if isinstance(data, dict) else {}
    with _slice_lock:
        pick = next((p for p in _slice_picks if p["printer"] == data.get("printer") and p["n"] == data.get("n")), None)
        if pick is None:
            return False
        _slice_picks.remove(pick)
    spool = data.get("spool")
    if spool is None or str(spool) not in {str(s) for s in pick["spools"]}:
        return False
    printers = printers_cfg()
    printer = next((p for p in fill_printers(printers) if p["id"] == pick["printer"]), None)
    if printer is None or (pick["unit"], pick["slot"]) not in fill_places(printer):
        return False  # the printer or its slot is gone since the slice
    place_spool(printers, printer, pick["unit"], pick["slot"], str(spool))
    save_printers(printers)
    _printers_rev["n"] += 1
    return True


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
        elif msg_type == "slice_pick":
            spawn(lambda: (slice_pick(data), self._post(live_message())), name="spooler-slice-pick")
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
UI_PAGE_SHA256 = "d8381a67b0ab5306a60e50feecda0e5810ecd59be6f6e24f995c48c11b08ae28"
UI_PAGE_BYTES = 1273091
UI_PAGE_Z64 = (
    "eNq0vXtz20ayB/r/+RRmrosHWI8Yyclms6BhlC3biRM7dizHeSg6JEQOJTgkwACgLJnkd7/9654XSDmbvVU3FYvAzGCePT3dPf14"
    "0JtWk/Zmqe9ctov5w/95gJ8787y8SD/T5WdI0PmUfha6ze9MLvO60W362aqdHXz9mU0u84VOP7sq9IdlVbef3ZlUZatLKvahmLaX"
    "6VRfFRN9wC/qTlEWbZHPD5pJPtfpESppi3auH54sq2qu6wefy+v/PGgmdbFs76B36Wf5cjkvJnlbVOXn75uq/OxOMU0/a+Sbg/Oq"
    "aj97OBo9fvXq7Wj04HP59OH/3LnTrWVRTVdz/dnD2aqcoKo7OtLxeq4pP311/l5P2sGk1nmro3I1n8fDWVVHyC3vVLM7etBQH9po"
    "rMZx3J6WZ+nRsNbtqqZq0oeaRnan3V7lNdW13qoyPT1TdRrF6UN6K/ihd6TyFGUHmMnjaqoftdFhnKbp0dFRv99JPpLkw34/6qTf"
    "jx8e3b+/2ewkPvj3v2JVSeVNm9dt83PRXkbjqvxpOaUBJeNYNXaMedMUF6WapJFWLTrIY0z1oCin+vrVLGrjYfnwgLuEMU9oPtRR"
    "vFVzW8OyrtoKczq4zJtXH8rXdbXUdXujVrbO+YAWeM4vapo+quv8ZlA0/Ktm6Oc1TT0NcXxacZV3XubLs7Fa3pZ1olvKWtyW9YTG"
    "RnmXyEN/sE6UbRd4rC52cpq2LsqLsRrtpt8szqv5WF3tpEs7436/19PqBpnRFfVhs7mkv3G/Tz+D9lKX5pFAdHIZq/P9iWqrE25a"
    "XaOSczM9sdLajmvQ8FR/rQ6OYtXq24YrtdKAS86+oGxapB6V+CH/gTqpTw/P8HZAz+PxvSX26/OypWU4YjjTqqYPCYT/0Df0OMO/"
    "EUE5/yKtKt+VBFOPNSXql9WqbG0Sv+hpt4QAl02Tt90i5SKsxrzqKQFkwYP4i/0n2ysqaUVov202EW87yo1jgsaT9POD3z98fqGO"
    "04I2MkC/1st5TnN4omQn8IQexTT5Py0JQI/zRkf0rcp1+vnvj6PTRwe/ncVUQ6X3qsi1Gh/cPRrj4xfVB/exanxZbEHewt0G7vmW"
    "YzVxxTPajXfXDXDOdpyMaQIIA5rt0jPDLxrZMivOGQwGvD8dHkoPh+UDPZjr8qK9HJb37sWaZiTicls1lepUSYind4QPTa1TPStK"
    "bTcpl1kTlp4VF6s6P5/rpHeodLlaaPN2pD7URcvPtbrK5yudlFtqYBYuGAPXs3mVE3jZpbpTNASIhD8ynbRbtQzLA1izH1aLc13T"
    "U0Llbv9oodWlZny50JtNavbixbw6z+dvL4vmwXg1zvxrYgo0ej7jLDzYxA+E0aoPnCyPSae6oKpkvR26Y+GCz4ViFk2xyU3/UeDT"
    "68CF6hTLQdj+Iqrj7FzT3+QCf4dUVxHbz/msKOgM0WdpQX+2Zh7aLRW7YOwCHBPb04VPlRGB7DDKeqf/F5394/cYUHtFSUl0+n9n"
    "9+LP1Q29fBZlyen/ffb772eb33+n9Pgfn23+l9P+N0j7X3nY/P757/+g339kv//j988/v/DDPw+ORRq17YbbGjda7R00n/9jHGfj"
    "cQI0xsfkiJ5owE/zySWgH7NpKsVJI2WuCHBKM4sP6bjB/iYMNiBEuYjis7Q8PbIv8XZLSHHr+vjBd3E8Hpp5i9tUD/W8oQk2a/ef"
    "V4wqojUjAEbz99L63vjOON7aSq46lWDdNG85KVxyYTtBremq7+RbA0Y9bdcSeG1Ida0nczqFk1Y17c0cu4s6bquhs+aCdoOc/ChG"
    "fWwJk5Scwh+kF4wElYDGNeP0otWLZkJbXNHJUn2YUUtE/GhdqmnRYC8viwk1oIvSPNj0Wi+qFkt7c55P/lA02kVZ0a4vGLcXzSJf"
    "qrIS2kkFOfiiKco5oRY6P/JpVc5vaDbc6E8YjGRUdHoSzYKjbOyn51gLuuI5smtDx1drHs2k9Y6GslS9Q7cDC1pPWrHCL2lBS1qn"
    "T6jK0+JMtfhTuqWpA8DpNtoUHzU3iYfdBoVsmdXVghaAtnWpP9z5qSjbrzkjqm0/XbdaJhQFtHR6cOQycupv/sB+MMyps4CL4jQn"
    "UKJOt6qmR+pVvNZpPjyn+fwD2EA/OPSdAq5Ijwy26B0GcObGJP3GVqPuMiFHldSbTUGHZ50uJX2J0SDRoRhMZeZmJkFbs8gcHkQW"
    "NKBO3PKE6W28t1Z2yLXslrUs1y6lSEiRiOF2P5VRJW2BfLPp0S9+eFFrLGrNU2SbsnhTCCshlcxzG+zCp9qeivG6pBPlFMv4EkAt"
    "v2dY7dNC5YRwuHV0irFwzk+tm6ZicKFbaYd2ac5vLdNVw2LQIAtnd86PrSLkhrFXaW3m1Z13dCBTDrYHFTbP9GHl+/ykA6Voz476"
    "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"
    "Z8+4K6kqvch+9gUydW9V3RTHtPNtTq3VrIcch2bP2QqVBl3e3HezmJfb9aTGM5t62Ul7aTKOUQWRsrkntvuqnUScrubrNdMLPEuj"
    "XVeLJS0ipapxM5om+s6WS4Mxq8JKNYrJbNXlptkYElkDPgXTHKu2md8ES95eFCxVExKzR0aqRmneMYE6eoZdhoCKT2tNqVJ3ncbE"
    "tjQeYL4bFdbZgm2TcD+lkMs25wTpx7yfp8z5TIE3Jz3Xep1qketIYIxQIqFr3rtlViBHxa0uVqc7hJLjB53GjXtvY7/Fx0nxpr5w"
    "w5F392bcj5TOIc0dVQbDhqWoJZd8A50aO7jIDuthZmqIXWfexJzTu6qvLnc8J+qGYi21iY1zS3RVokh+1bmlvh/kvoypr9u69fvk"
    "YEROf1j8dutB98Hvz2a/vrhjP37/c/jw6E3r8e+Pkse3704fhU745Pbx+4dHP7z57cj//dHRg/aj5k/vH996ED+Y3zwdN585v7Z+"
    "Cp+EP5x4s2ny2y8/Lx6E0JN706kXQr2zx2/HLxxnPJva5BDLPOt4955j/je//fJr+PDWD4tff4Hyv99pPTn6qfno6Pm7x+9vxA9m"
    "P7c9gOvR0fHp49/vOI+O7rQe3bcbs+f+28mL1U83b8/Co5t3/vih6f7e/fnnp3F///Wt3oPHh7/s/xrddY5+2m/9Nvlj8O7x2/u/"
    "LAadI3e56tyw/xgnT4+74/a9if1kMO3/+Ozk5h1/eut4dC1YzT08JKk9muyR+hkzMznjmu9fOtY09AiG7fx9YiUTMkNLeOB9JBne"
    "mPDjFVhhcBP8KPLJIR1+NDJqREvPpZvjEep2P3RPYcC/dGB0G40GOTg4GC2S/ZvPRtfPppHnIityQbhbwKS7xQxAXJAYlwSv7Iaj"
    "n4Ee8N2bRBGAMqLNQMuYxg01Rnfmb0Oax517sFyMbtG/mKLZ8Y8ek/lkNathiK4ambOjZT/iue5StzzZvNDfFQDgRzWMbVUjcULi"
    "GnrwWUYxL3hI3KU3KS6othTrec/sdZoxVnLGwswPeqrlBtjncS0WSPAVKLLZ1d4qBaj/GYIz5eh0QeLhy9FNEJJ/xF+P8Nc9/HWE"
    "v57irzv46zf89etNepl7+tid0WJ+NIP5hQJ4TI5hDrr7AQmXLrwDHv/7/6Svf6zcZaK+hnPlNUbLhPTtv//3GIFMWzqcgIDDmmNN"
    "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"
    "WSX5ouyaWCqTJ9kWD5lVw+QpR6t4AhSTusiZttOU8/ljZTmqo2AFVFlbVUfcxyKpycVs+MzHnZvnk7OSAz+BLmX6lrYU3zYd0gEv"
    "uJQfiMVD4fzNzjtvownO0e/ax29rHZo9ITcVOarnyawqORU5d9glETkPAqN13v2sc+qb9tXziyYg73x8FYTkhNTjYmJBRq/MoqPP"
    "EKyPGnBAGu0UgVzKmffmTn2NIbTu3ONTyY+u+LL24DJfDbEVKzrAFoUWlcc3UvX0SqnHUzawmTOL9SZpxpVixvBFwEldPqEkUm2M"
    "aPcY70vYgvbZL+Wupic65qAi/iBuanFeKp/A+DVrUop3O/BxUJmk4nKZvHW0ffa7hKTi3NQhV3ZS8cVJTOKirHzi2o00nlA8xko4"
    "GcW7kV0nl7h2w42nEudVJaUSj/AoXaZj5RK3hXy6kcnenq5kk5jXziAuJ5hExHgC8fbN+3Ao0PBk084Xk1OHp0yMSTdnuMShOntm"
    "4bPjKIXSO+jChRsLn3wQzRUuUreKnWSnCRev1XNvw1QWyQ6OcbwinpfygnL2AwDiIiHf+NFPwKAfbS3Zev7TIxz6h0MUCvJEEoPb"
    "4TadyZpc4Lw8JI6X7uB7/+ETqPQhJbTdTrsqm4FMFAETn4zC+7mpvpEuWeyrBoGEi/z+m7kTf5x/8BkaHr2DBiOd9+/O/viT05OV"
    "1Nvuir3b0dD1yCk2bnVzec8+eAuuEIw3Q0jOdgz6grLjmuCdod28JRiCSG3GN966oQ0QTB5v3LfPj3fN4s1Xpe3mIrYsZ29ySzQn"
    "uXdJlP3oX/kZoKqKl/h6copudkJGqfLIKZrie+g2fvFNXhXzZtx7rItNyUE+GGZLS8y9hEbb7deTR1WWfNzts5+pa4NjLboJubkX"
    "Q7fi6bjliJ25SgZZJyN7rQIR3ZP4sPFU3ADMbom45z78ERljZlpiqbg5JGc0FXckQmU8F7cghRXrNHJInMkKe3TmPejRycXdPnva"
    "fHKycM99eaF99tP5H9+Y+/JNsTumuqj6OPsBIw78SX51aFo7f/M1ZkA6d450PrzFN7fBIJN2m6eXmHXbVlkiV6RpmBuUNRKCNSnl"
    "dgQ8yXm34/2jKY1FLxMzcCNzcf4uunWw7QWwGOevdN47Ll4bZ7/sZpNhzVbl3ZagD0STkrJt62VEQm1ozVDnvBjptq/9kfVoHEeB"
    "go58yR+RgB1/n7wfv+SuoALOVlnHsbksBsmB5XP0j9cpDJwajuEj8Va/+mD2HhqisimdsP5sUnPmT/imTD2QDd5hXQHadn7489yl"
    "9yXoLmDQg3cB2jsGU/ydU2FbIOJk2KI8cnJh4+OfjlPCS0xKga2nkpD7WjlT6OTZJvG1cWmhiZsZqZzX/N3Ynicnu0Z9IzmuOLyU"
    "neVa/FrsMpPdGiXm2Alnrb/xQaWQKax3jKMIXHGzM0cWPjxnxQg9YVajnjuMDkm5TrrZreXGdWsxtkQzWrdvnGgf+YIvWxj93831"
    "6qSzbmNaF3SPw9WR16StQmD0FRKgQgYxBuM1CnjP3vLqmpaYQhfg4L0N/N38N58Ba2aW6aauZlsHti5ZPGk14KuSVjHQNL5YX73L"
    "i9cme+3b1+dP3DNm8izjp34r9sydP7/WufU9hkYiS04y6yPLri4Zru3bNinKeiwxtW1LFqGQkVd9Jy8117AdjY2W1eSi5mMu0WyV"
    "UMAOjTZpFDOBRUwB6O64mJCSmq3vus7XTkUtQa3jlZwM1HY5b57zGDFzb+6rU5aZJTNXBupWfml+nuUJat9oG0vF64ri1CanlI5Y"
    "st8/DHDgbtG27+QX8dTOaPx3+HV2f1BppFOOqfr7t9onr8y/8QBrznwwf+Ma29oiQhKWis0wYKD8vWgmabzIbx0FpOUnVO3+bAsY"
    "EkebZmzjZySltA15IEC8XTjjGHriLeQ6Bor9EaGBGSKWTsBNJC18AAv7kUveyiMdUZAnMEaRPNL2wwJRzOOcS9qQskg2aenYbeZI"
    "bRxnAYERrcSel8Zv9NiX8/e+0ragiG7ff96+g25gzBcxfeGPyGZw0KXzd9FciELZinn8mU9Qj6OGTcgQrSEm54pe8GyD9Rnsh2Ox"
    "sBmCrcvQIeXlheroGSZraDxmvZTgIyhQl/e+149y8ezPkQ2Mow6PCPMhyRJnYroySZ4Z7edOHIet6JriWd5blfG2ndvZtEyhEAsX"
    "yZ03kBMkBTX/yQ+zTmLnzoXr7Z8usEqKDDcT8zojWVTBtREnaMfclM7CL1JaAs5ykpDLGfmJ8z+2778h7Kd6uYyncjaBjpOGxog8"
    "FExo7rMZ2DfEF+qWHWh0nViyZnvwxBzNjC4cgSoxPTMSGzc8iNFsHD/KmkgOaesmaJYbgqP5kH8LSL0Lx07HsjLbIR6jSZk1m5WQ"
    "kpk9q2dnPmXb8WhaZqSKP76ZkJE5xUyXm4xZ8yxMDTsfXV0kKXNKB2yLpmQWJo+iH8dTMus4Xm4+Zg4X2SURsx6T3Jo+al97v/3N"
    "hc6NP3fJwzz33Y9zVyXgHpBBzLvcm6rYhqMpzMyc2isR1aLZmCOxrWzrklgqZtxS2DgVMNEyXzwpJNuKwGgi0NiJlyOiCsw4EuxQ"
    "i0jWdJ2cy0rRYKmKLiRlBVCsb0Ky5RgCRnMtu1iYkGk5CRXdbMsRVZQ2sYmmWe6Oh066ZRvPQOJ28bFbquWUdslLTLVszkVSlmUx"
    "xuUg7MSCLZJfWUgj2YvY0fVR8rV60AQrmkJZBqM2iYPZOUUt/5eLS82eLI9ZyqQwOWGyE7ZfhDiaEqoKYW1vPOB1RpZhp0O2nRxE"
    "KwhLu3Nn8R5iqY5t4HfPdIzGcR/cxFhJ79/iu1H6ddMb69Qx984DW8dEOZ5zQK4pneIYyshK4IO5G1ddh7fLZ9onr7Y/JEFj9wvP"
    "ufmNGWDd8hsryFBQ/2iCY3v7E3IbLxw+jK9lH86wuWVSfmOhPBwVJD5gpK1Ka7zw+o25G98mpTXW8RAiSY0RQygDVySpcXQAK6Wx"
    "jipppS1e+BL24TV7BJ28mIvieYv5hQP3G26HWPPurl4WMLolKtZGjrCErkmKuZK9Fd3SFNtZryLz7ZapWDqnaryJiU0i6Yp5Gvpo"
    "x1MUI7uahDuJNAUFKwtY3dIUo42lokFdMhRHSE5iUmK0IPzydOfw50pgvCjSBk8BIfDRH9o3PsB3k3tv88mDu51LFy6yPgU9qJjh"
    "wxdeqmOZwGHQgztnJAQsAVVHrYhmIp6/+c38F4ejiYg5fIdb5phHk/Ql+YclDsk/SQZi0Q+A3H37CkArkhGLl/SX+5eMTeQZNAM4"
    "/RrAkQsxZi77rZ/6Fr6gvMN4ye5PlNUqFUuNBQzy/J9v25TeTjesDPs731yPeD2wksJKOjx/+09wB+nHPSvPMLBMaBCgG0im4dk7"
    "p5zPWplkZBdl0h3JNCyXFZFgvvr0lYWcyZHrumuzIpNUuPP1J/M/vWVLygkphSNPrm424c5Hb3AcazeLsIBb8TFuFuGIhiKWSFje"
    "OO0V9/6jHnDRYIv2kX1QlN7rMHvHGJiSF6HFQeFLQRIfEd8U1u1ZOpErDHDX0fPuD9Eb0r4b8b01SpJOmMmttoNc0zs8ubeScyxG"
    "A0Mz8Os6uAPbjLuJ87S7Bb87oDnJ4c87bx2fvQcDw2H4grtkbMAHztd+ah850z6LTvKds+cA3ujFzw7nN2+3b94VqL9/S3x4z72J"
    "0tWxo9y5mfoaSQ61tMheoshREUg4dJgxn3sHLeGd0B4wLOYRRHW5jSKzd85jTdpjoUGGjyIVh5khpfy1HcQjFjw6olkkegcHOIOP"
    "sHnGBY8irkiiX95D3m07/lGC2k89XnTRv+qcv6LBxBy/osNcSrpfdnu0D4qJ3cFxG3TqAPUMp9P92q6EnEXN9ptJcKK0RrEPt9Xt"
    "SFy1hfErSJeFeY5IZ4ibHbPBtToZ1UI0ZjxhEsdDL/oYqrL9SkAUsszgjJz6oQJR9H2sri96EKdELInZfkhcTVZhK1qDQ01nnxkv"
    "7ClihvYiXb/wr9eE/5Q9+A9dosWh7H+NF7zCb58Zz1X90Vqr7DXTXib7u/HClOfnqW0jzKvmXjNPPZS9PHVycDwv/Uz3j7V8yhCX"
    "enkcepgKvLAV+CkMYlYfS3nLCsVmiM6exUOHlnk5+DmRzgz4rVot/7vxPepDLqw/V98PnHOp6cFfzUatGqZX7ekZHlqV2dM7NDRA"
    "Lab1UP8JQ2VDPdh/4cgDXh5mEGYGBnD2pu4Kt244gF5NjVpp1Euv+v1U+vf7H8v8fnpVJQu1/Ezht5RtORzYSZNOh3v8oUy+OLUC"
    "ru/pYibvmX69CvYLbVTPfqFQQOgcOkS/AF4DxRVT4fTvW729pd4VU2qx00X5kfceC6f3lYJUWAEo8UHKITNTzPoV2ofd49nlwkC9"
    "NI678NQ47sGz8Fl4oVfHp7NBpZCGmU9Ze1Gt0F5UCtaES5V0ZqrmhSmv8PQ4yvJj/dWxNMHu0CEPp4w8XjEjy/H6w2BS6qOCrLYz"
    "rAfkLOSFW0NvIh1WMv2RDeAepkfRZ1bAIp9onfVKoeSncR6ZbJN+47ZmsqOVwu40LgH2tV7JUcRfqMA/oG7NKuf+rFKz6BYtWpXY"
    "Sy9TSV2XAMjgAy3QLHzAWSW/SauF5p2ypoZA1svIaqfNaM86CAf451f2jMrYQ3s8wObd4/QPVjPNxqII9Wza9/antvphLbej1gpK"
    "tRdaNTimqis4J14NpBPAeVxD3fcI4bxpNAMq5uUnGvgUs1N+Pszmcjl/OkM70QD84kQ3eRy00IuYrwbbTgVb6sFEKdSjZacmSgeq"
    "E62JLQFnhHyyWqmGTeh2AjjOhO/TmdwYdwF0hWxx8kBvANy45wPFgVSF5vjLRu01vW8rheO5ACOXwkAZskKaAABM0sJgWXROGxXJ"
    "65MOs6sR4QSE2ZHJkCjfFBwFmZscgGKxH5E/LEg/vxA8NhjUcfF+2+dtIOKQ9lbBz2wfzPupjcU8FjxuCh6ngm0bCVD8aU22Fz7t"
    "3QhEvtxi82N39kBmq80tsCWhh/CQtfyfw+fVcgheY7V6PYAO1zze25vJ+s7Hf8ePqx7vVdNNh0zHUuMpmEgx8xju2nQKth0nUQq9"
    "XSDd4t5qCD0pH2Mwwto7w8kaUArKblnMomu088XAC7vDntLe/4J1AxkIlzzOz+m1VKnTEcCPIPPvT2cQzN0RQoAF253uzVrIF/Yg"
    "MVJ3wW8e7x14FoiVySqPh3A6k/d/g+BVZZJWng6o1ZeP4IfKUqsEgKI15Rsouk/gzsJBns5O4DXRzE+VRkc9vK43ccDSEpz4wHsF"
    "aEO++GK9tg8pAPuWgpxd8ypV+LvVQK8oEI2AXcTikj/q1aAH+hc7oJgq27wmeqrli9vrqfHSZAoIDvJ19aaUb6F8baYW3JkP7/kp"
    "dhsuleupUbwpm9AghandAt1wJ4VpsLtveinPH8XYKKWgbnUBLZpu5aneaatYt5KqSBLhVDi19bRTVD4K5Vxd5hJto9ah2jnNgA0q"
    "TWLs62Z+T7Fchy2swLdireUTkwXQD/lH9eEfg1G41PGPV1rePvqxr+oFXLH58OoIdjek+6PI4Nwpd8jdSV/cC3chza2226o+tHwS"
    "Cp6D/22D//0O/vcM/O9F+N9OqAlUMRxX8/Z8L8BZj3kjAf+CgQ7iv6WRoFqjvyfrNKRf5X9r9C8clyZewMUmYFzVm4Dm8Ed9NGzx"
    "L7++T38tV0fltz26WiVMgSegVwlD88A8Lo/KY/KAPBKPwv0TBEKhAMCclldNTKyahA7oBevJ0uTzY+hmk+/LloJqKT9F2SYAzb0g"
    "wCHJVLXeAvZ2EAWXah2+oWIFzkW10qqiOle62gGIQRZk+eIOVOcFpVTj4dVK1S8Vs5SRwJQ/vFhDP1lTjj3a7fl7qmmGwHkk1Cjp"
    "STFev1DfDzPTuBjgoYL+W75V/KTXjFYASgFco6YSG+FAPrwWVivI5Ss68XIreHh/dK8hFIOt5v6H18ZrWEkRi6fro+O1Uhk/KYIx"
    "ODJCCQD8KMV41qv6XmozCITBw2sVL5lgSKWg4o341SaQgLGH94NUuQprSHHVZHoRa1fxgI+iiSUQiy71kiiFnm+q1GpWPIJA2JVO"
    "4DS4SaniNrBIxM6674elCp7Kuvx4Era9Kd+qYbi/jjrO4pOobQ7k+5bAq/KvncA64a84ndhZp06pQ+qKOqHG1C5GHnYKaXjS+ndL"
    "Enl4BsOXYydbgD7wr20PrwUH4d/BBtOHbSUc7hkgD/RPDf8ZbFVaTTyfOwHRPGST4Pfze8M6/9oOHLV8fNI7yD+TKMMz6AGKQ8uw"
    "PKo9Jg/JI/JwPBAPwv3HSENuYiL3aNKwE1C86j28QiKwJg/6eDB1eAk2B9cRJQ2b4U8vtRNLY2ThOS88aAojNGH7w2uj41bbCEF4"
    "sR4AHw8nVpVbB/5lr1ojdDXH1Y8Xj6hSIAZKeNQUgYMjGGLAyboNLWAlh6EDqIu+/7EhApyZL0oBWD25cPXu3KUbycf/kUm7Od5I"
    "Mg3QqQxUpcjJ58IUnmo0adWVooeYHotIbYpVYbpdjzuMKM8AFNWKqloHvfPBlc7lK50L1wH/+PfsncPm973T1vcT+nf70iWrznnz"
    "/cg3CUcenYZpAPTypd7xB3VNX07wD+6Uis7LF6c7JgfcE3fDfUgH1FqaUjuHOKAW7vJxbiM/7pzgH9BSFZ2XL0e+UXXeUF++ki93"
    "P5IvZ17TP3Tn+Jv7TyIRfVxpNf+zhv9Zy/+s438e53+e4H/W8z8b+J++XvlX+ulbzQPZBGNyEnmJcvlRBEPZhhliwU81gHSKXLDS"
    "nj5EKcbc119DEdlIRugF+j5iUgYujNAL7pFKIqSCB6cSiwpIEOKrpyPUgU+uKZ2etrRI46Q2YbHRQ5ut0fH0qj2/L+eGHlullT/L"
    "wkOHMJ+uXwnHf7PG/P5tYe3KldtF6N6zZgiVFL2s+cut3rDhf+mi3qHMY7l1658wX/rwS1/fWvNl9ZClKKkYRVa5PtpCDj03Gniw"
    "dZuZX08DZ7ivmOnH0EQgBOZG0WrlQFgoNurNKnaRL4006zWQvPr3VZvVkWqtGk7mx8n2sR+f2yokhuX3lYJ0T089GC31jFSyKbjl"
    "/WajhK+eGTj4auiRenkyV2o0PL+8abxaQzWEiNoAv4oXbqpPNGCoMgmkUJgzI2Aa9MCoBUTplAZRV9QkBPNtXrlaShfTqLID/qAH"
    "DZOCniYwXSARpsqlYG+mmOHt8ZoDRfwAgnoNzZKK+fA3favXRz4aUA5bO4yS8e4XnmMqu6OEGpu0soyTsHoZVP6liyGOXES9AU4y"
    "G7D6EXsJCiFpQXE0QAX8zUMOhHnctv5gGaxs5cq0XwiyL4yng0zWG8jBP5np/iDNcKsWlr7q/irl3dkH+/BcFa5P4J/SRQ6SCbcZ"
    "91eilW1rhbSS50eaXgASMYzZX8rV+a+03kz1QzApO1UKw6A6gkJ6fllvVv/FFxkQIsIwoCCjcHpJx14KSz0MoKFpnkC9sL/ql+v7"
    "SW+IHP2+Ui0dZNd4a7SKBeFXle3vuppsiaw+2SYBkITiKOoO6xlWsu5D1R6Qynyx2agiQ1nMTnghkCtMR40TVl+LEhYFXwmC+qhH"
    "08eYw/DPSGsMgI6FQ9PZ5r5KfurARM0H0jYeho38qlX79+/P7V+TqweVVat7e3tXQZVidn+1HI7nV/dmx8kkDn+hH+DG+oF8sTfV"
    "i9kQV/ciBQQSUMRAjMXprF8v452yp4g2usXsFDAX2/pSfb2b+lLrcr2r1z2xQf+Ln1N9m/pW59Zs6F2Hf67NrXt8daovt2HNhjWp"
    "vsdzfU+sWZ9ak1u7bk3f6k3w99on1j0Ofz+x5vHHN2D5Wmy3Nre6r++J9fj36t4n4M91fWsef2JT37rchtVrsHh937p1ULwut3bt"
    "+rX495reNRvw7761j2P5urWPr1+/qQ/63bB+DXS/ej100wezWL9hXWp1bh1OE/7ZtC63ft3a1X30Cf9n/w0LpH/WQqcwmCrqe4Kb"
    "47+bVCF/fMKqLtU20b8bgHYSeJ6AmULhhtxqKFyP/8Wfm+Dn44+vXS3fN5j6G6iLDdjrhieggv53A01hwyYN+A0MbC6FwpfVJooN"
    "CJGxYnavN5kvNtbu31vvLU4PDVkXyWRFKSmXEclYuRJ+FIr6rUG9FsE3VtMC8Vj1v39ffiz9+xz8NzOwYhWZjOErA+m1GwdEwV0k"
    "nB+pFNJ7vGw4JHRoCqfio8I7mC6E2WoB30bqQRqKqBqM9fwIsrposBWAtIkUqLpnRw0GGCqEiiC3UDNo+qpOZ6azByr4bCYkc6pZ"
    "PQiCNU4/v4cvqyy/HAErwUnS8vvq1XKqdzpL9Evqcp1YFTyaUmMjvgaVfF1lWR9czDytqa1AAvJ703zKPUqzJk9mxR66CBpp1LRj"
    "sOBgMEz34vPabvRZ4ee1xzzOBJLuy2Ryr9Srfho2AriIegO1+UCjWo20EL5m3p/OCGHnF5gwh0seGFjdmwGw8rf0FAAHtpjLMitX"
    "Ti3v6Wkc6KnCPHvw0/K8KZ1GSFJi0noANRkq8vf0NOpjpVcgCdQDkifuCp/QJDMcdAawWrlSFeFfxSEMJAXUMC3Ay9jkFfaySFQK"
    "JwsQ2FcRehWI0liIlvpzOfJ4PePKHyIMUPWGLyhZovj5qtQjup8v8V/TWVQhA0WjTRipwLU2rUELgtfOSkHtW3GnosNVH0W7cJDg"
    "vawvOzwcId+8JXxP8+aH04UDlfQ+zYPJ22V6C9wKz6WfTIeZ7K701lLay62gbQSw0k3d9zjNyBzMTchKiXp7xVQpqNDl11QsXO/K"
    "lfob8GlwZhlVB+yvcOZHi9Mrpp6HC1w/rRb39cDGFfWHwVoNsTNbHC5mpi0GZD9RhuX/MYLM6yo04oK7PtUjFGG5Oon7KwWhETsn"
    "J0bqNSAUqoviypVOUQ4l81JYD6BOk74UB1TdhAfq6XxCoRfp0x3OQzvCJmDEKI1S4DpM02QOsOVhHbsYUHPI6wGztGYDgl0Vfi8E"
    "8rgs7aWqqBkCsRrqhplMOB7U96d2QdvNQQAUDBX0fj1MjZZqtVQpRdiXKsH/p/QEra43S9dI+5BO+oXefv83ikPv9x97LDOF34Ft"
    "2+MP9QdADluo2hypeQX7j0OHAC+DHOVDq7S4HLihIiF9seqn4Cing9x+QGMpy2SFwAIBq/reDjgCXhBOwnSer0BNoKkZ4GisR9Mn"
    "o6+f4cqVOH0DSlhI106X61rLs1NqGkg0gb80YzxPyEYv7oW9OJ6yTcgYPKPXVI04YT58rGih616zV7SLywrFOk2JzBvM0zkBG5/X"
    "HTT6TbFVJN7X2yN4QvlFJqoY8X0oo4+X2hQfAwnVaMR+HjGwRlSjBf0xJPmP/7A6Tk20mkDAuXIp1dDfafdygC9SJjYPHj8RD1YK"
    "+mQABmmzBwDQFONSjFz02eSiL5Fc9A3lrV6n+wH5McZZ1gOZB/7NyYsLXNr0Z03Y4IKvJkl4socu5eIIsNU7R4N6rabY5WKWFmWP"
    "Qf00qRYixQ6S35qFl1tpe8BMvzojHpwR7zfJrdTB8eDgJNfY4w0lSCRcreiuCR/weB0tf0krQXRKHDTzt5t7ogjyiOnDfRcG9clu"
    "sE9aXTqy3XQ7RXZcf4pvHlkDTQ9lptPWXfbK0q6SV/6VrpJX3KtkW8UaeWuFLHu28D87+J/tcOGb+vjXVIx6bPVhI+HcYv7oiQbw"
    "ufVUs4Hp6VMgtPUQTGAv9EWV+7etfopiB2HNESiQGlmqXwqC0mSKaVaTadF4CahPKbUnAuWhdCYFoup4vZyzL7EdhuayEGFJC4p+"
    "y5Kf46pMfoHpB/rKRE0IaUY43/XZnj7zVo9aCr5YojvCxNr+Qgwoaj6gzbZSQxl77fTC4sBgoBKWwEh5+j6oCB8JNOmB/O7qoa0Z"
    "P4Rf6w/1PX5ozeoM/NxUK000vHKGe1Cyjp8ZkPUoAcHAZEvFhYV9v3gxuC4TyxBvD9wM6mtRPivYObM3I21VI3F5tUn/GtMSgrlV"
    "X6Y8lQ6VPUoIogjTHhAN0qhJlL/6LbYkGxS4Y9g94FCINQmAJ4GrEhkTuenMMC/8/Zimg/+ETNPTyUzTxgSm6eDfmGl6MTIG7ODT"
    "yCVlYAXeQLe+QYDk28DPGoigBs0GB/5txu2dzuS9PeFQwbeHf9ri2XYn8myvPIJn221Q5ZVfnWd75Vfl2V56JM+GseKqIZy2kPIM"
    "979g+K8X5WdRrk64z3llpgSbmM90OUtl0rECFQSqxd+xaiFQ09xocW0lfFKJsAqe8ArSG7JQuCbNIJGXZAKDYfEgIBx7j+yXq9ld"
    "kxK1G+uimlGltGlUAXIfGyprgIxth1FVTucPkGKAPwXeaCtowj6mtzFI1Qhwo8CNAeRSIfVLgDYDQZ4ZHRl1uNqkbDReeZHBYTRv"
    "IMevFEo7EChSjGr33D7UUGTkgYH3Mu8TcYEbKzx0CMgSz1YPlw6geyRnZiqLQyAbqKFhROgSZrQCo9c0M3omeFJEuRWZS8AnyM/A"
    "kO76NfgS9ovZX0LTsPALFRl7hrK/WKqBtkFhj76qfLQ33FwaHU/rOQIFxQRe1VoZ9sa+sejiGwgKdFeMoqWojSlAenWrDCAJnSxi"
    "Q2C7PPprIMg1Ws1xGCH/Upq3Eq8W02GoNGN6MsY+2bM3GgfD5tOsRkziZxl/pjMZqJQNYlz4UxXb+pkeB5ERahCxHfDyL9bSU/ik"
    "Uz2QD7MYpyL/dHk6a3MQzz6ih6e79YAo8GqlALfuMw4dRDNv6azPsU2HK8dSUv+XuWkADbQ5LXEsgO7PN7CWhcEgpCq2MoLB8B1Z"
    "jB00SbwFlvnCJ+Ii5FUSn7PVdeD3L3u1snLlM8COw8bhGuiibNZrmPsBjlFxDxmdvdjyhlK7xr0UPTCl6jSllDVYajna5i5PUXx1"
    "uDgojkrqP/D+8FrVA6to5HK/sECIRM0UghA7TC1v9CxPMWThhrF25He2WAFnmUY/dGhF2VR52a5C9TFP5D5gtgcGNpVpa/6zQpfE"
    "S15pL3DOBu4r9OOAuuf/s0LvjMZgGnAAvjWZoBZ2pyPnXhO6kJl1YDAy6qEh5NkOwO7itICBrdfoITCj2Wo0LRb9reXeMWxLHUzX"
    "ia9qNHFHfc0DGm+S9J5Sz8GhTHrPYM/LQ5lVlWxxRV/PitXFiHtLtloQrknzX7nxUvP5/b7in4QAZukKCM3zMFX1DoB8XG7yVIBd"
    "4pu2UBCl98qV/p7qEOIayibwc1rdwURLCVzDhWpD+lHaaIxgAmywrRv2h5ckT/vD/0LyNK3ZIEEwbI3cGiYJusr/NPmf+rAtT1PZ"
    "ryKWlYYdJxOZW42/8uzohzs//GtJ8j6pdACIrcD7xwj9zeElC/2jw/9aQr+sJy70S8HfW7QWJFI0T642MtxZElrHEJropWA1U81s"
    "NVvK1rNNYJiyo3jZ1eDWJncsqFoqAPx9fbWSozsaxBR6CRF40wBQaEkiONAPnfRNezU0IIaF9y9LjxaA/ylpTpKS+iGMmswpBcr/"
    "R3F50BmAB+eS6WcegR7ccG5V9CSr+tDT5JRMcdkokNmcMBFy0aTrBfUprWTudB1nWVe6Et0NdFETLUVV0+emtdWt4UdoXWznNme/"
    "5GoBJg7dmvo1wIiFMVcMb1pT3WKL1SFPOeEnu7ORiT086TVHg2ojRLcimKKlHMFL16e9QNOp2iTddvqmspziCBAKm8MCYMlvohx6"
    "f6hUMhb3jooExtyp6bz9tT/899UDADONR1nY8zi3DitrDLPmAxqhM84jVthM1IWgbYGXfVRTRNG8PafkCXVXtjwK+j5AH12G4tij"
    "FmmpdyaGfz31zsSwYfvGh5PUO/7w4uqdcXNT0O39q6p3YMS/p3onTZKPQER8kvNsZ5JROp/KsLL32gjsJRobAqnzw6KYHUw1QjEp"
    "4b2MGZ00lGSzeLWWz7JDF/sUVa28+GjT2apPJuZTK1hFsVX4ifxUrOZ+pML5qWpztx66OjGBVoEhodZ4yS9j6AGbSXxZ1CorDJuP"
    "eTvFZDGvbOlYv4H2b5soBjH03sxkPRTqEkrUY9UwdcK5lvVDVmJXqClCSDxyvoz42Ef/z5o6fds5CuexrGaClpTWbLhwF9XjVXiZ"
    "7o1tcVlx4d37mX4kPJLml8lzWctP7heANp1t0mf6srkmuJBtVcvqJ9mzsGV+PdAfNcj0F8KYp+tNhU9ZDje9icyEY3ojJIBZzZVk"
    "R7O1bIu1eI1wIIfRLhuAyoXWQNpTn40ewAO2qx5U0WGr9iJxFa42AIge7atR3AzJpPqB7qSh0zDeKSoX9iV0FiZ0phofOlTOWJo+"
    "Pzder++NqNzq/kYLELpM69yITI4V0lWe0grSHOxreZtYqtZ9VQtVM181uaoCVaMwNgB8nNuFaVxCzizSIX6LdVhyAavBBtwdDFDv"
    "OkC9UI8NgN9iA9QZyPl0s2tfzULT7Uu1FZg3TNXRwmh8e5zi6JbU4FOXLanxlozKqTU4HpnpgFFpSE2N+4VISxAYIk2b46Vyff8L"
    "9brYWzjHq4DWYfwdTmDBVMAc5Kovu4Gx/mqMotnevuFqGe29smydX47p14cRHOli3ee1l7EuH9RtGDorXp8oh0uUVRcbTTvsZgJ/"
    "uEPSUe9XR9iASYMcPa1DZLqwQrT/bdxhUe2HAqJoy/XfHN+u6pUHGLeAhVjWd+hQqZHWi+Ogj92hsdGqhWvh549FwMdVLfDt9ieS"
    "ARgZgqvRGH5XiKm3C7QMIYKtSLrZhK40PbsouMteV3DvVvOhzSQFAXAoVOzcoCiN8QCsDW3CEWuGpFy1blciTDt2pfXLjPrdUIhv"
    "Tqyaidb5Eu3JFuno5sjoGHUButsnmXGxe+/arh+uEwCKj/+F224YOOcK8dXNBLZgTy6X05LLkDba1SJ7jYKuiPwk11yYyT8d/QLj"
    "kNtet9cS6/uuMbQZ1QRjIDcCPOWhQ5vGskX8VczG+IQ91QblV920cyc2pV1WqvKsxyf2qVp9BKOnMEoM4fsynhdvjHxDVq5cZFRd"
    "K2HolAy9Q9WJTWBaT8FlNPojhHEg8neO2BCYBuoBAKRhWgGRu0gmTEvkE1VXhl/stjOAZfFFdweWWj1hccJOhcOL7ZQ+P1SAOjHp"
    "rVsb2MfpfsW7cJGldcc5oE7qZwAan0DTGQUeG2mSAUSnj6t1PXwVKkYPsKKi2+TZlDEPrXCIBJFArBsbVhpxblmcti9VtXStnMtG"
    "kStir8ekyYgwavq/izP7/cq8bwWhD/pHkI+Meo01A417Xkjs/DJ8ztipHpMwAptXThdrpUkv6CHdbDGjH7SyQeGZclpdVXJgBl7V"
    "jHVkIy0+ktQKz2Gnz2OfNAfAh9gLMrErYRajoCh4BhY87WmxFyQKRUFpP6oGEoGcpUhLvCy9ysj6UGaIgiZOSukNLhFY8u6R0Q/X"
    "2WqBHq2TYIEMNDv0QRsasMvTtZhIICwOHZqazpaQW1ZCfrYOfzW9iZIfVkezTfiDUS07it9xRA2/0gBirgVE3UnPPvRPGKHgIovC"
    "UHVVj3alZvCze2pGe+Lp/9x+2B0y1gv70yU2zY52Qwm1i9Pd9tnqbYAvedKXdyddjA8gBmbL2TGQZ9LAqifiRKtQE5xgvUsSWrQY"
    "LWpRtJgoNAiU4/Avb3y6nDhKmSE/YQF9xZRVkd1ilrwD6bHEUcYS9yVpoMU2abzLJkV7yaiTG+Ma4+dXSeeJdDOtNzK0YC8ydN15"
    "tbce6JvNFxW00O5lWR9pAZMQwpe7rIRWSTLZ+l7PTzcARg4M+OKF3YW+SmJr9EgwZKPkXZgUFsXrgHlAdxJRr1oIEPV2UBqAJLyr"
    "Mt4FWU/JkKJtUwKbQsgSI2SGsLFZ0HtuC3fTPQmYUASi5ZwtpjUGT5uLYmK/2HdbOp/C6EDOE8PvYasEgVdoAsp0ETUSdDpa1HMG"
    "cBU3to4FJRLjgZ00AdhXl2o48gxmias30oktia1J4AvjnM0vtF1yvCoSdYl+VJWIirxEsS4+qYQO+72foVldvOqiFZJUiTBvQHwE"
    "vtYfJ5kKDCQLhiAzrXCsqLpVy2ue0h4KGWFXeZ3Jxz4ZBpFOaL3xYswwUelZYYw93pDoU2KDkWw8kIMa3JfF3Sb1VsG3iV9owlYs"
    "xluutluuTmy5eig/NS1bsmPXi8mGeb8Qq5G+Fn75chKs+Za6IOCXY23X2G3XJLZdM5SnJ+NVuVUVftEP4TZYtgykL+WjmytSTNts"
    "ydiJagRJF/VzTDETVdexDnYgp6sQE1EvlHKkRtjJ0WqQgNcLamqHDtWBREsNUjRkgcTqma9cOZptFYKB6sAiAtWOXZvQXIwlKnwq"
    "zC+m+4jXlkumXKjq+9dUhutlLO1luzWHi2SMrlk/k4X/TjGXmG/h0vENecwC4q4nSyHIwiAbhRlg2QA8y5orV5YHarI4A4O0MHaZ"
    "PPfPQ7QyWSBF+iN8oT+BTaNnuKBeD4sDZTiLHOShMdpTLReHBgYsxahbpPTVcjYnVq5srFw5saxQiN+uA3rMBi90ueloOTJhE9Op"
    "xFu5OJ3JN9ThQ2D+bc/eI3RQT6ct7ZronUh3scfWtCn2g/idIW2UmtHaw+TWK4YJpjt22U00oVGb/TdbL9CLsKD3r8g2oLLtK1e+"
    "lNbvQWaTm3zkikMmhgvK7RQopiomaXpj7d74IzOQFFwVQVPMjoPsOLDYOPmYsjKT9QGtTEds1kddxesSamFlB7sSsCrhNQC9uU0H"
    "MpqaGA7nWZtjznA31Y17ldmbrzdFA3WiRtZtw6TwnGKPe28a/l9G6/Kk+suNuQEVEsj/aveOELJWLURHry59WPczXAnBQIB2ZKgk"
    "QGTIADHHnZSzo+xcqytXIolv6ncyQJb6UGZgoDRtISKLL0uyNfWyRX66KwKA+RfwNPKa577BVdPR504xxscCZqen8Tea1SC7jmfb"
    "8RFAYU4BKokfwmAGaAzUb8cL+bmr4AFKBbWIX+0uTQBPuWBAo0OLFEyzsv6t9hMQvpwZKOO/rcxAK//Iq8y6s+gWy5eVqU+V3uvt"
    "iz2yGQ4j6ryTVKRBlutxL/rGX3I3ZdVC97NiohTsTeTcSXMwqIIspe3bNIEkiabB1E+mWmjjMvG3vSZ+IV2Z0sfTuh6Z8VOvUZ5h"
    "eRx9NRlw4UKq/yQrAeoqt7/c0y9Vw/F6C/dZ1jJBZlLGkOtnnWU/W4RNR02Kn6uWBwbUWzawZD7Bof4vIGR0xQZhfaeUwobuaGKC"
    "l/Xhe/qBf0Z0Ns8cio49VUl8lnGUYHSde81FET+7opKO2GfgYRj142BwGVY1P/RK0msDwd6DpXfptOnVkgRr8kpKbNH859gMEDv/"
    "GkzE1yft0/KoPav6mCmetTvdN84EYNqT3OPw0jvKBkP41DMqsRTzU5XYbWbzlwkHK92NAVBK0ASj5gY+aJlD6E2jDW22HL8C/w5j"
    "e3F44Sstv+2yQKEhhGZIONXYd5yuZUCZYOXHETq43PAhyfPVNqBOK7jP9YNifIToC2jUXEbDQnWByvhe6LPadbpRG6RWFedQ9SN2"
    "FGpPbIt4EYnIhXGAXahI8d3vWrGjO8dmiQwXCRSnZg8tM0nm8GKGPgy70Yd6nn7jNqcTLQEPhISD3yu6rjIKIao9LaaNCa3k8Ag9"
    "1eKJdcLUt6g1yHRW3vjjH3dGB4NDmF5EU8nPCPJSkXUVq/yRtsp9hogvprjHcH7/XVieqPlYPlRU0FAWzDHTJYmY59fx+GpTpG5G"
    "jfggMNpsRO03c9Q8a4xMI6rwaToBdpeP3NMBMSmElvRM0q1+VCetxBgj1OPYdNgXEbSTtklTWOMn7nIbKmydwfcslIaiFF+B+5Pl"
    "GIHWocxyh3mLZko/6AJu94J/W33gn/QLqbxW/CTAJfE4UnVGveiRNDc4uczRmRwAVCwFIXGsqHHNF9HhOfDKLYBPkkM/HefV5MmP"
    "jEMV/unTJ3t0OB3A/yv1bh7VJFpRNpDULUvAQh/RJwK4XHaNAOIXyNXd0zdQRcV6FkvQvzkLe02K9ii//beBEutNDJBUeOd0aF7G"
    "Y2D7WXDTpHBPMEQQVCvCl+AEn9SRUhmfgZjeFf8tBf+Xa/TQ19QU/Yn/h4nOa6XJfIopXc9YzTvQr0tHyE6kJyiVq61mPlUO0/+T"
    "OshxQY4L/mfGtCjBLUQOj3CkUqOU0NkUvtJqhtWxyR7MOIN4HqvQKJUxpq49knyyx7BiTNsVgTiUgkkrPrTdhiNlJlSnArvmGEyO"
    "4m7atfEjReCM1eQE9rG6/NmuPVH1ezhmplUXPuboo11zPNbluNPb9L85u9lTrofWjsbGgOLY1BMnk1QxPpekWhE8Wdf77wl72ps8"
    "+9FqMFqzUTLaYLEBop1xtijYV6u/ZHTRNZeKMKaBgzKxGbRGMRj0o8fnekseXaovOnbVH6s/cmCstNRRqe6iQ2J8hUcOiZWWOiTV"
    "XXTIMr5vB48clKstdVipvejAnCirGT5yaFVxqYPr+otj1oQ1cCKVak4kE6rE0w6Vl0h9oObiBKhWedTMapWfMTOovMSZ1SqPmNmB"
    "2qNmdqD2M2YGlZc4M6gZnVkxq4SLKXzHSnh2kQgZ+HaWUyyg0gEU1d3d6Bk1XopTy10yujz/Ulq5Pq1cqdKwqoyXzBoBl9SXXW5d"
    "HsvzK0atVst8CTekdM+mcnNieZ5BRZ6VEyWMa7ncoIFdWisFyH8sN1thlx6IFiOpoQoeeoCEk1gJv1lVhAZGa8lnqyLSkGgt/GZV"
    "4fMercRf7SEV0Y8NqgqsyuoYR+uq78Vp1MJksvscn9ONzKdJYJJ8ZVi5nvK7kIRHl5jn7L1qwqNTVJKsGiw5PrrUMbHWk8qnhVEc"
    "puH3VcsJUtXUisYozZYlnKjNDilZ7ZBAk0sLgTL5rxQCZdINgTIS9w8/8Cv6hx+w/MN3JvqHTz7CP3yn8Q+f/NX9wyf/8f7hm6yz"
    "6pzTfcOx0PNGvYqi+Y4EwXJrLQ0YMYJ6JiLXLPyLoxuLiYpm6wKHbFNqLatVQVqJE5dDtkUPrIiD+5dol5AqmF8ZEib3DxeU7URx"
    "yJzmXcNpy9NXLwmD5m9NF5sNzDr3dFrZF+RGD6TZXCOTFXOJ5flSjgCDOlZ8ilMVMtk928k/BmePedZp+kU0loi74WxMb9bPwSBq"
    "D01nhrJ9j8OkM9ObhkGa9kFOKOwaNvPevDQqtPlfiQptdqnQk264o20c7ugVFeVor/rxvBPu6Pn/Z8Id7V16uKPBf7FwR4Pdwh0N"
    "/jrhjl75pwx3tAzDHf1rxDLa9jNiGW3/V45ltOPvE8to+1JiGW35dWMZbf+HxDLaEudVt/6KvOpWi1d9LpFX3fwIXvU5cw1s/tV5"
    "1c3/eF71hWEdIhRum+yrhSl8vtqG6evifFSzlo6ent8UtAmdbVcBjMESa2YbtfTP6HdgiRXz8Xp98Xp9Q5kh5TDCwV4Xj63sWU66"
    "Rt0S88s1xirkE2ecWcPcaHjA9m4NkH5twqeNA6H7PRpMBb+JBYamDTFfWDMwryr6NmpzdK/m7HVTkXkjxaKt+vV16e3NC23MdaZS"
    "W9Rf5ZfHkCbDuF9uVBf8UhOeYjFb/aUeK+ShHGu71m67NrHtWjI7qhdiT8+vdjHwfvVnWXc3C2l8s89h/higFt0998xTvbbnxSfu"
    "R5n7jhaaEXPfWmHUMvdFe96mbe5bLrQsc99WdqxQGng16giTDY3JK3BPdRQ3tRNMo/CqNo7NvqrMg+BKEwtvqg6Mwg6y5Kk6Ti9j"
    "yullovBqzOMla/LIAoSWARPXGCjj5CxT4ZCdmbMTmTwPwaOMZdDpRH9kH5SJv5+jxV9tb2mcNNSS9cxDy8lii/JT8I17hVhQiSeD"
    "VcP2ZLDdTBKU3H9bU9FEp4Ig5lSASQR8dg2okkuAiQMzkNtTHRoYCIztv7axZcvan2PeH3Qz7w8s8/5AG5UnGcH9bdHCBaLA52cA"
    "Mk4TXeKn3TjiBNCldMpXOslpAUGMx5ztKKPgD6N+CXUgasovwXsUlWoW6hEqBXTLolJIteo2lWoVahaVqgHVKqXD6KaO0UfXKaFs"
    "OSWMJTkljGUGxrRzwiiQGZAdxwZaETLjKec6fSrFrU6x7DByd2+CfyBxSb67fyXE6jecDN8PWlfZPfbQ34dXSTxxP8Mfii8nRmaS"
    "hdHV1bKXA4ZBLPKq1o1eXZLpXWm6/9VYfE6gYZnsq/EYCvb3eGwyVZoY2CzEnAArDNQTAjF1GXAa+0yMAGX3ly0tIQyUQoC/Yn9L"
    "S9zfftqBSOQLTyJf7BpLp0tWWI2SlUUhGlgDo1FlKBxV9RHhqKzAYaWMrj1gfcRIYSDbVI1xsBWUg2TXaiY6u2CR2QXW7H5mZLES"
    "mVIvFu3p1zuLFM3INssz1tXpTEaxC7+Ds2eJQCTiW+If8tVhQswQT+I4ZTJWBKpX4+GngOEkd5RgiSGolAr0mXIag4smbGlVjWxH"
    "pSLKEYl7gl56SwlJVecOS0CBTEiqJnLXSwpJRV4Hf3UEKtZH0ZbQvoWPjkJFoCogmLzY2v9/9t51vW0jWRT9v5+C1tZoEWOQIXgX"
    "FYbLlp2xM3aSiS+5aLQNioQkxBTIkCAlWeL3nYc4T3ie5NSlu9ENNHjzJVnz7YlHBNC36urqqurq7ir0JLXSBZWwE4eucv/nKC0i"
    "cUE1gDflggrVB+GCao7fDRdUwtvTj5u5oIo0P1GDdMlVHqf0gqN0wXwHU1Han9SPef6kgFbnyNPXuo+yDVCQ8R01TcZG0u9Ucxwl"
    "1lnuJQzj0DKM590hDuOTcIo6nZA+qZE855EcpkfyontJ+HkHv8Jr1CTbhMDlhYZGjJ++zl8UIrR4la3uyorjTI0att/lYDvY1gnU"
    "F11W4AEmdKdUZPfu5AbRuHKa7OiwZ6bgI9wyRW7mnkOQveQgxx99X+kMXffZNO762bKl9PD4R0HK2ZJG2exwLiGXceK5CQ+0ByPX"
    "KEz+mMbLL+zVaLNx/EhnRzsTGkIYrHPgHuhqoGO+dpXXoJSfW/3YAi0g0Ut51x9H+3ffo8hc+sDFDb0b1w3AzkEFUNdtYCGoFhfz"
    "xPg01QTr1GpWG9PFZMf9I9+57QCd4p5308awOYCVONIeGS7O0bH2UDLAtPUYXSKtbW/SvQtGncgV9sHO1KWLXZ3QhUm8eEvPsGAY"
    "9soAyATgEw85jndzx9/OLHKco1R3ctDLh3I+nbGJ1Mkk9KB0bs+1kof7o2n5nSKNWdd4Q8ZCm0xzk6iQ/oCKjLzkuwqtiN39ARoG"
    "ElMcCIBeWbhuduiycKpcVzcQoKGTL0MF7j7ed4Lh3JcjG7r7V+MhutWGCRtCrfLF3RfOJ4S3bXcfKGJYhr/399P7eyMcANojvsD1"
    "uLgnbrplboXN9UgFjFi1rcG41eIW2NLv71P7HPjR8OJuxkco4rjuT4bGpDtRPukTT/aGywTr/VZznwVmdt71Vd6blCeIDD+yubM9"
    "QvdmuVdVhQtIFVI0zhCg6fNxP7NfkBtNQV1idRJz11y76EoBU/PawmMb2bbwq62tSLswm7n4mYpiuKZ/1vuLSZ/ERVHrpVwTlw+s"
    "yMxZWKLzw7XoWAlapK36xDVf1rZ2R8UWQz2MrY5AYtu6e+Pr+uHH+074w/D8kO6v+0lxMEE9Qu4tOXY/Gn/K1qcdldv60ViDSux8"
    "mOdBgxI/ghL6H00Jm8/FxKBlZi9PBlExozVtMG31JYzm0Vu45ggFyfSdHLcbcb7bjThRouJOjEcsOBJrGqCerjdnHXHEuiOOeNM6"
    "Zjd/kdn+oGKjj23JO+xZxnYte7CNbWx63oiSAU7ib52j+UtV3M0ypkG3OOpqWZyTKGl7IH1eS83TnZ74+xQF41QvhEo+xfwIkhBM"
    "1PBkeH/fxRMR+Ggoi/SFXKKy1iiURnXlPA0pahbahmqs+XqnnYlUv8bdfq9MwcfcWdfiihqW/FFwzesRXP+PR0N6kaM01tA/tocO"
    "iqVlkk4KwkruY5s58bmd8jSEpUXgn65ucNTtGyEkggUS2/39eHIECdR30K2PoQje/+veceWdmbtnNLPXGaDPtISTZKIuRbLdfi+j"
    "G7gjWqaLuuXyGJbEY82Yn9szFbMK6tZML/01Kkgo6km1zh8VEAPURbMUk6GVLK7cqSWTHdMRmhHZQpDCQSTR6JrpKSijLG7c9RDK"
    "Q4CSq9xlgjPF0tIQJ7MwlrNQzjZjnTEfFv0JRepBlIpYTq6sJyemUyyXpH8YcZ1kSz11oo0qwZq1arB2yStoNzkTvSg27CVHP73D"
    "3fgiXhIorm2QjCcYX0wkmVHEUiftxFeLQ/Cxiicl6sE1MfRDRjZSGMqNDBVwFudO9V5EhXJliiU6lOr59n2GZkR1NuDSQaUwB40g"
    "NNQfDnHTNMQ/uZuqmVa1YZWxqFxZqzUmVZyxgh1tOU45zuAxyXQGP1bO4MkUMupikLhMQ2jFyjl6qTuJx5h1qrA6Zo8R4VRh+XVQ"
    "znidH/WEa3lRgyqUzgpsraeiasnmaFSjDNHhxlXa7CRNYE/eCTUSz95azu6hU4+4S17U8Lhx4gwFJfQnqHRqVPqHdAwSu/q5tYgC"
    "aUkDE+7yLWnzXWWO6MsHi2sRZpglZZDIeBkJo/c2HyNno/HgveYZYsxufjuF/hnw+Hkc5Pv44CZzLtSnvEN4Fd3/BLkThily1SnM"
    "QOQFxYqjgxCiB5ISC5YOXkcK0jfJoTOlPvVT61M/Cq/YElVg0AqVcn1WQK2wPzVq+O/3we35FPA2kzmTWhBS7RX/N570B3iVV/d+"
    "Ye1GtdzQOrLMuWTuE/w+Xjt+/K6rSOGOB+zDu6WT3JR7u9lNubf/STfl3po35Z69050W8j25f/DPz/zzxrgj92bTO3KzCcj14Z9z"
    "Pe7nza/H/fEfdj3uj7zrcf94Z+Ji9S21BzLCiXlXTVxTk1cLdeiTlv657gLXHyYJ/vFlLu59l73t8+sXvO3zq3bb5xfrbZ+3a277"
    "/JJQ9dsvftvn7Z9/2+e3d93H7yQ/FyLZd+9E3O/0UtNwEy0iXfNS4yfKIZyc4c6RuBqOdtGnJBazafRsdTY9LElIHlTMzLSRDgrh"
    "9Hw0vu76l+FwGER+NovUCrr+NMB1H6gXTodBEBplDjicmg8RqTMWpTgQUShF7RSgG9bA47mKfq0CqCY4SfndBv2dvqvjirhKmQXD"
    "8bXsIoXAnQVP4Auhlj0JkpqeWytDtGvF+vDm+PjHkxbPo/d0r5NMIe/n8io/8Af4B0rEiE4tBTMAos9n/Pfw4EuJB3APJ7u44I+a"
    "RvpdaE575B+BLqekXZoWHeHUVPMYMI4eSf3qaSQcpprftK66O4ZjcNGlThhJ3+jocVs6JMCDBaBhw8w6vgxHtDTjOoJRF5fLPDAb"
    "IFXF8LTOgZXULxJ18qAg9HaqUPpooDpkIiwpSUFCNarJj/8Agns+RR8vr9FZT+xOjf7xoUgQ8SKAH7q+4CNOU5fkYlko/uoopDWo"
    "J47/r3ieh0dhAMstnXJ8eY4wM7H1TK5/3h/NILP74O0cWPPBwQOoeSqPBHZf9uPL8lX/pngzx3u+3+FfkDQC6eypqRs+9Cc3viu/"
    "kpcn8XHJ8RD+oNJjPOfUvwh+KfVBEp/HD4fjASkp5bPx8BYWlTBpRq/HkxKB8FXVnYkCv0KBeDyx5n8BFZUI9q+qCjDI3J2ZUGGD"
    "3TF/s6Hy549HJWhqgQzULThhFw9j8WNR39YG+n4QWwfzo0cSiLRe8ZBnp7hBhnELGGHtP4LFlwRTT3LcHKpLU3g+4lI5N+/H0uX5"
    "krO2gXqRxUDNPVx8qDf0MgoczlLoxRzVJcnz6G6WQ/e2WMwtE20XFn3/etdNfH/O43gcbez8E/o7Qz91Yo2cJADfmJZmxEn1FfPH"
    "u/+UnLFTYOFiMxVIpcDuTo96mO/bM+Ouz8y/yrrQKXiTm8JsjOs6W1F2iJpp0fRoKsrwt/Ltfzm2zzervJFy1g3dkXLmES7n87yS"
    "JsGWOoa5IUGFXlWSuzwEXR8f/stxjYKEgS3LCPvNLkVhchPp7tbsTYkP/6wtuNolLhfM9YlrwNhhlAvX0SrPRX9iVAbvFp+GlNaB"
    "aYtLq6E2k+VcFYeP7AVLIcw80IaBBLSikrrXloF2p8VpPHKyhUs5pTvROC4mdS3wqjuso5xU/alsSZPOijZXAnw2huerbKHqqkLj"
    "aHSb40iXBwVzlTFX1gOkmLwlwUnJ1bNhw0tlQBOvnkzjX1kHXfKJpqZBAqt88F5muUJOX1ZgJvlGHEVrehHOwrNwRGbLNOcWWFzb"
    "tU6nfx4bbl2VmNj7982jyt7Rp2hupQ9VRkyeE1UbJ4e8OcxcS7nJxS1AY2JiJ+As1W5L2FBiU3qwVr6KLi20t0VzK13LCvl2sfmA"
    "Qd6cAdNSblZBs+WA2YCzVLvtgEGJzTH48QO2RXOSx+uYAbVSbhahCgdycH4V5YGb4i1bazWZGs9H83CYxWayS2Qv8YmEg1UkKhHu"
    "dC5R6V3lUdrUMyn7xyiqooIcdTVfl+ZyeQ6qrV3LbJqt6Rvn/5jOyRq27p0ouLp757Bsn5VI+hi7eIkeaa2bipVpE4VzWXTDlHav"
    "CghSykmlpWxqEZFtNIMGqY+Oz8/x9HBO5ZyahwxbLIm0y2yhFrMP8VVxBVZlJEg3yp2ZxtN+OEupSNaB4nypwcnWtk7j0mvkvPYl"
    "QVakbhK0QEjONVELVs4SrfDGE2R91INUH3bkb0k7O3O4TBU7dHIDLpff1U35XdLc7hwvW8cOvd2E62ndzeN/qfWttalV/ChnWloL"
    "r5mkG0TfEJWvDL+xGvWy6OYYXxO8w4B91wkk2th9+pgVbN25jaaOvYsbTxzR1EdMm1QNW/dysykjurnDhBHN7DJdskXXTJZ14WKE"
    "XpsfL2YlqrncxgheGWomgXfH2UG17zw19NLbdWiTSWHr1qYzghrZfToYxbfr2UYTgbq2/SygBnaYAulya+h/XewirnRF8KKVuOVy"
    "GyN1ZdyjBN4d6Z9q35n+9dLbdWgT+rd1a1P6p0Z2p3+j+HY924j+qWvb0z81sAP9p8utoX884bkexZhrF9xyuY2RStlXYxOz7Ej/"
    "VPvO9K+X3q5Dm9C/rVub0j81sjv9G8W369lG9E9d257+qYEd6D9dbg39rw8kx9WujCS3Er+y5MaoXROGTod7x5kgWth5Lpjlt+3Y"
    "JvPB3r1NZ4RoaPc5kapg2x5uNC9EF7efGaKRHeZGtuSa2bFJtEOuek24w5XYTspujOi10RJN+HecJ6qVnWdKuobtO7jJbMnr5qbz"
    "RTW2+4zJVLF9TzeaNaqr288b1dAOM8dWds3cEYAMc9BvPQGiH4Ix2peVrT1rtEHR1QiW2XecMpnW1k+dv2R3N506meY2mEJ/iQ6v"
    "2XpYC+guGwmWwjsD+7H0uc1mw/8kPGxNuFvtRPwVMZE1968HdWvzfabojmB+NNlubOL/n9H/7cl1c/v/XwwDaVP7Whi3tJ6b5XaB"
    "7mOJc0ML+1+6z1sT5Kbm979Mr9Mm77XQbWnFNsvtAt3H0uGGlu6/dJ+3psNNzeB/mV6nTc9rodvSmmyW2wW6j6XDDS3Of+k+b02H"
    "m5qj/zK9zpqA18K3tU03XXI3GD+WHje2+/4P6PvWdLm5Ufgv1XubCXYtlDtYVLNld4X0Y6l0C6vr/xgcbE2t25hk/3JYmIz64XYq"
    "JpXYyehFBXcC8KMtnNT0R9o3/wL93t7USW1/rKHzc/Ycw+/ubne3ZslChI1saHTFrDuSm9HK5sT2ZfqwKekYzWxBOJ+nF5ufuv/E"
    "xLKpkTMHyI+hoF3M3X9i17YirJ0s2F+gcyvPoX9q0trIKGkF8KPIamtz9J/Uqe0Iansb8+fu1opz2p+YkjawKWZB+xga2tJq/MX7"
    "shXpbGsN/qy9WXG4+RMTzQYGwCxoH0M0W5p4v3hftiKabU23n7U3K04Ef2Ki2cBalwXtY4hmS3vsF+/LVkSzrZ31s/Zm5THaT0w2"
    "GxnSbOB9DOlsbTr9U3q0FQFtbxD9zH1ac9r0E5PRhtYtO4gfQ0o72Df/tH5tRVC72Cw/e88ytsjPaAva0DL1aeyQWpOfySz0abqz"
    "nY1oW9Pip+7QyAxb8HmoBRvZAI5tCOMTA7fJqfN8EPM9+eA4lIbBYDwVgRPQR8YUDbtbNLKSoj4xIuyH0v0kYML+ZgET9v+TAibs"
    "m97qg0XGjXy8+HJu5KEt5bQ4WtjcyO+vcSNPpdiN/P4XdyO//+e7kZ8usvFdeBLIqC7/epeKKZL1Fx0kgZA4CPx4MhMDcOIrl0ET"
    "mIRXE3RRHfsuEo7t391e1u/WXofda/0Az/f3MYZleg6vBwcPhB8weiKPQO5exhPZXqfIxX8czxAf8ZiiTuif2F2k7xwciAq1ajDu"
    "E+ANYRCPeiK5PGd+gXUu0DV6RGgfUdwVV3W/tH+HPk0AqjC+XWKYMvniaJnYFxGm8pORxl6FKJEf9VRkr5iEvylQKEnPKzfUML98"
    "TpVRWfRysyuCO/wQEGFdAS0b6aMLPX2EnpKNdHKs5rs0gt/is3PKkaABqziiHT+NdiIC3yUvoTa6s5OaKIXkpI8AEdT+XSyHfomg"
    "0HgTHPigQ4DvFDknXIjAbf7j/ix4LGYHz5lZ5+KdS1B07riGO+QQHZ5tMhp0Bx2iL7kba9IBLnsWH11/+5zpmFzpc7YTkY+Z7Wmq"
    "SpoVq9qkDFvW90pQbg6gas/EV6Mrcj4ej0dBP1JZH3jm+FvrE+6sXckCVtTVX9cJ//Gb169/+N7HrOTbfxVgqH/kJ89WIoGxxZN4"
    "RSViIq/IQXuv+cnqEtMKQNEp5QogxaxflYUmbk4TlGMphMV0gZNhEQ6DbPjzu/3JgCcPRWlw91kPey4jj+LH5XKZ6Ff9xUb6VX/x"
    "H6RfUZ8T9WSc1a9mX1C/mmn61cCqX/UXq/WrQaJfUde+qH4FLf7Z+tV3SnSkxEa4cMPoEjkIxhGYYYCUMEIwOzhPvuUJl5pjKhAN"
    "xenmQMYzC40WSf5SMJOeDG4SduQTwObekXdl5CxybcXJ8g3EHrQ3EGE9tFyZWV1IoqskxUFLs3xFoHyRJLj+UrKRR8CDXpD8zGmB"
    "hGsveXzIER5IHvX8gv8wee34vtPRAejLypeu0B3zWkEZI4GfjcYxf1lSwNaZpdAzhqI/o0Hk+BF9z7vVXvWxUhFmUP48yqlT1IjY"
    "EtKqx5xXKeY5Y6YkpYLAwoQ5eg+hUETLSY9AElAHKXcvaVbG9ZEN7pntq3QpGUW6UnoJ+0zZ2V7vDxiVJGqc3gOO2KGmQpIGJAPN"
    "/Gip4vmoCPxyxb87EQsIJWLyBBqqWmqI2DnaagNfkwVHQn/yhSgOqhAELSoQb/Bd6ryiHlZ7XV8p8xx7SunzcgHAn+UaIFHYObSP"
    "0tnpNUdt5xUBx0GhRUE6s1wX0FJFwE0LmXRGygAZ5ZLKd4sKTcaqKv01WVgliEPixxFEjK4cRTlaoj7jxbEOpKiZqHijqj89IUi2"
    "Sctc4NSvJmEUBdPOqwv3MfGm43cApIyciktqDtD12zsoOFp0T0RkF//UnetviVY0FCqBEcu3+6joi6ZgoGb4Ss3By6AbhypAnJLb"
    "QVkowL3vi4Hgda4vWIEP8oFWBNcYkUbF5XI0xtJP2BxokBwnTfx4TudNVCx+W3TcF8Xfi9iS4z4r3r0PbjsVEQVMr1byjT2olKY2"
    "MLAyMVzHVRLwh2JmOE/skIO2mskZyAlp9FZ848UiAMignTBs2rLEp/A/8I1y4lox4HBhRh5nVbuYpUcoeS4jrKUwsrZZ16gsFwhU"
    "FVyv6TgdMQJj2ZK3aUun7gxICaTomjbcE59q9E8dRIoY/orT0ZFsx24ak+EKFIab4k7hCR/ED61sT9MkRrwn07js1mgB2Htb9CmI"
    "YdIxj4aA1BArNFWDttl84CQo5Hf3LgUKM6ul4z4titod12vB5NdgcAOh54ghnbnUYM1lLV+kusmcTRb1TrJOFZ/l4t2di1hYkCAf"
    "3UncEfDCWo0ZyJLx0obRpuZ8V4w6LAZEVfAoa4DHSYwEoSEQ/7nvOrWlTjOuYm2A+ZOTwemps/yuDAvCYTDtDhe0IDhXHHA2Po9l"
    "kRhjyZ26E0wkf+OQwB7C4euVKkLZ3GyOX7vvi3fv3rFW/sM8JKKWJhy20Mg1M0gJqIR+w1Fgrn8hD8CU+oZWgXg+0TRxXLt1vwnK"
    "WEGKbAwSBskdljCTVLOw9j0YDPy9vxckuKd6hkn42+v5/cGATKq8Ar8Iinfshb3I/tF7PeAGD70qx4wTrtRtaTBIZmhHjgS3dE8U"
    "3IsLJRoIYJ7c3FxSo2xE+7IIg+vH45uOXylUCtU6/PPd83A06nBkQIB9On4P4yGCrB3jngtggj+zV3mAp5p8Qi1n0IdZxJqUmfD7"
    "OIySFPLbQ6tcEZONe4Tz6nnxR6bul0XBNYonIFxPadASCabEF4w6DOz5u/PxFJfMsMxM+C1M22obGCHMlMkCf72qe76QfFhhT+fE"
    "Gg6zI/tXR6uNVv4EXF8tUOdy3MtFV6fM/mRyhooRPGI8qD5AvHQvbHlK0/E1pL2zpoVYbAFJmbkqMlz1p+/9nHlza62SIvYt3bMV"
    "lc7ifjyfQaYb5GbJgg2416uEv/XPgK3h2oJzcEQ+4sCQFAIfhenuowQMB++h5LFo0LM0OMCguISsaH4F7V5jK3EYj5DRvja7MZtC"
    "hqeisqqlsj5JcAT/ySLFax9NJo/7U8Vt6Tty1/7ZDH+vxsNg9JZkmvjKJoE7YKzBVQj69Ik/n0Dvg06SFSAUTNe9w0ydeOncjYK4"
    "EHUDDFmaaM4h8mVMibtRGWvv9U5O3bAbU6zF54ixYoDMmuQcrF+ictIMKL/du0dTIJafaBaGDz2XXjFyZycsee6zMfSm4lLEWhGi"
    "u+QtQTcBRJ2SOUpG9H4g04VF6gg3MgKM6PqE1diic4RwjrvxSbH/UOX+m3w6PZoWLZhwxww6l56lA7iC7v/HPJjFKpzmt1MYgGIR"
    "5t+sDCnTWxkft+ifSBrr7u3fHb96VQ5mwBeComxhuXfqOz32iYYRZQ1xJzneZdAHaQ5CZ+Ge/FT0h+HChzmYPL+D51gaWnAmpSTk"
    "AtK/L8ZKl6TJ5ujKhQtVXXo+TDXSnzi4vAdZXFUvTyZVMzV8lqpYTDiz6oBpRKBcVRD1FzY2Logfi/guh01G02o4iyV7EDYXrpYI"
    "u9djkN1x9M/gFoM6d8Icholl3DhBrbTJCGYZ87CkWSYvo9yU+UhB59s7oKRR/2xP1uyGQ6Gj9M9K/kP5dc9gPSo3zJ1AmzuuZEg5"
    "6b1KB+aPYFUdmIJ26o4l7TlINsmy4EXxV6lMkf7GaazDeQ1NfyVRmyYfJjXK87QYKxUcKYjYIk/anizSMUn0GCgpOqmc3t93VV1Z"
    "bln0C6D6l6DSx0VshCpmQnV4lGCShpllTj6LlQUAKcilO1odS5pfXMHrheu7Bf8htqkyULuAj2tjmYO6+auFJlrrFRA/Oq7UjBIM"
    "3pxST1NTSkoBY06d4htK6x9AwJz4aAXBmPWk6PjVilJP/Ybv3pBictvxa0Cx8OL5y1MYw0kf1fk7oMaX9UJ74Xn9aqFaqNB/8HTp"
    "VfUPperbdqacVyl41cs6fD913xMgWmLVK7STGkpeySu3aqNSq1TXvsIvfCrUHyVN1QAYrWDBK1BByGQAWBlBTVoxaM5r/pYG8apW"
    "rhVahXa5VWjg31Ij2wmoo/rWq1IvHmV6UT5sQSfLh1W9rYJXLzdri1q5qgNFWcstb1SDH70L1XKlWai8gJa8w0WpUW6MSo1SrVQv"
    "V2qQVq9mwYaKmuUG5GjVS9Vyu5GToQDVZDrESYtG2WvZOuvVyo233uGohuBWy7UsoKNayYQfcuLoeYuS2eOSTHjhQaMV6lehlu2N"
    "J7pjgVamFXK7+tJb1aEW9qIOONSGp1Volr3aol6utUYADyLpLX6xAD4qpfpaEigo0Rj+ZkNgu9AqV5sFACc7LJS8oisC/W0itt/T"
    "xNYuVBfZ8fSayWcx0W9oMvOUFpPeayeTHp+nNO3TddUKh5cet/4y3XqtUFt4zTQXaGbhaRe81tvD7Pcafs92GrMvaORP3e8z86tS"
    "aBYOIQdOiQbl+TGV5wozNPG/UpMyfJvOAOXbmFqSOZ5buKKGnzoxxTZhsCqZoju9tfFGwH79MmGFHmJl4SWTwAMeVn3W1N+BVzb1"
    "AqXqZdVKCh7xzuz3puV7G7OXK54toSkSTt0X1PFBOB2gAeRugD2DHg5u+XcKPxVbk81FcwSrXqrjp/QYAcm26nUYI+DDzT6OBHHl"
    "Uqtcb9OfbI2NQvPSW2R6cYXTsI7cs9Vsl9vNZglmfrVQK9ebIq8JepNBbxPkPLQfMtABwhpvs9MGBUJjkR6ohjlQi1LdxlorIC2Q"
    "uTJBPrY0Wa32W8BoBMMptQbAOUDGAVMFjgIcfgaPwL/hP2BdA+omvFeBNxyW6sCfGsdNGNCyB83AvIE/Db2+QusDtfw2K1SBCWL5"
    "Nohn6KBgWtBsu0l/Wy9q5XYdaQgz6hyvUW6D+PXKNUAMsMZGtQ+fGpLDN6s1+H91hCk1yqXz/3atVK4fElApfod4qhdYBXi2A/Fh"
    "DYcloKlMwiHPeqr5TWYEgK9fAtFaVZI6KgM1K9+qLZqrCeJtOzVzGYCfs3pBpVlFxaBWb6uB8BDPzcMmysJWQ/wVOsxhud0SE0fm"
    "LdjzlmRe24ww8clM9R8Z7ADvriTkUSg3GkAVh40RQPwo+UyIWpRaWo/LDQ8FY63uvQBSA0oDPaelFUHEPqtplAd5oFLINAKhWG2A"
    "aDxsHz5KKqTxYGL+Z1bgABHjMDM2DkvwjFg4lKiowOQBGKrw5wWohRZpVls0Lq1itrVoKIb2R7phmIwg2bI8tlGwfgYFpIqcAmZU"
    "1ZhRMOe8ct2rk2ZXHUEOeCnQX0MdAc7ZrrbfVqsWXa26SNVbwHoLer1UYSldrUdqTqv6ljv53Y6c32taeCCpOUqo/JqWt6BKF2xT"
    "Fjk7ymGYOBZ+XGhcelYMXGaE2lUVOSxoBF6lhHMjCx801RZz85csewaGBVTjGeuPchN18GoZAC9X2trsqKCmVxu1Ae8giQ71dRAX"
    "oiTkrnohVBtrHyy91BkzjiXUCBU0LVU3tKr1OYZ12CpufYKKW4Sy3ywcA/RjZOaCZsuNOvyDlYD2FWR9pUV/UI60qrTYsQ6NZxRq"
    "1EtYF6jUZhOVFv0ZYTUlUdep+y+LiuhVBhUUnYckW2uHyC49eGmVa4eHKEdbh8ngYF3VCqDj+JDyVilvgdSOQ36o9NtAwoJDreG0"
    "FY3T7lsWuYd9WMLhMk5xxAqyBfg7Qh2g3ea/j4xcBRRgmuzBlbChVgrtu26uwT/YNC3ggRphwNMlqy3BrUVtqdh1SFAEQGOoVw/V"
    "AHmojVg4JE6uBiAbB0VkxIUZrHealiXBYTY/LbEqKGUaVRuXAL0QZhBqRKJ65I9Uf92SPZMfJiYMP2G91cwqd4jOKopHQlFMKMIt"
    "GVxUeTDah7A0qJLZ5Nbjnyp9zRII6HBMIfQAJAIKno2OWjIfP6mMp25kGaDG6BA63CiJv8D1GygFGh9w6QaL4DqnFyiFOfcprFxs"
    "CurCZuwA1v22apNwuhYD/4HiDJJMzCd4uiwZH0r1t4d6gZKXJc1D0dSpG95mBLBnl7TQ04XHnerfamu4m07dxX16XsslW3heG1dv"
    "1axBC3ANa1fSBNDc4RGHg/XWCCZaDRS92gdal0IuXg2Pb/OVE+xhVjnxColygrYu2wIE1RPLKODSRKscq05XTppPSWg+lkU4rvqe"
    "QfUE/CwNfBNmBWjwsDarFeiP1DiBYWbrOoTlF3Sm6vWRk9K6hFRVLgJvDcsKrwpSB6cmTD184r9CiazQu6VQs1wDed9Hjtws8F/Z"
    "jJiRgwwpN8owYpqKCppRuTkCfRYEn66sl0lpeusdrlHwG6aC/8Gq7pFanGi5QN/P2vo7TBCLLQrGu55ixSxvR5YJWlt47exqCCYN"
    "WkATNgzaVOXD25ZF921dAvJRuRTNtUso37V3q2bV2LQBxMKlx6MyT8F/BRRcBTYACwX6Y+N7nuB6HvE8nmXD26ze0XhWs+qlh7bv"
    "dUSxzUbjtSzfaZ5dlg6tCYc5MxNmbMs23SoLq1Gm+oxVg/PbtP7tVREB8HfaOczgR0usWXpfW9Re1su0jIdVWxkVisZLXBfyl5L4"
    "RC1PTEZZ0xll22SU9VVwNFYletjSVXZy0lRpmFMFZYU5V2xG3XKrhZpYuQZUXMYBxz9StW7UD8kcTWYTQae1cr1BDMmSu23NXc3J"
    "basbVAw0brcB2+02SlevXdfWsbRMqRhsqImL6lYNCxyi/do7BM6WqRUoFqqtW/ZcoO+HDZ1f2fddFqV2ucIjfXm76RpPU2lg1Ukq"
    "DRqFUafBnKTUVDNZm5yzujajJ+sUWZucc33GqqyT+cGFhR94ns2sU8/5flhoZq2xrbQ11sI9m5dZ9gvzufm2njIA1VO2X1Zp3qUh"
    "P8S1b71wOGpY2Eodze6VcqOPFjdpdfMK4s38WhJvzzxeDy3ssqNq20lpoxEdVsyNj7GGnrq3mSZBlnhvvUpKJLZS09zzbAp6RiLX"
    "V5jcYKbWqri2rtRGLZgfuIRt1Y0MbdAhKphYp/V6S5+muB7ISnQQDzWb7QHFxqXY+TvLirhyC1Svdqld0pdhyFjauEEErFg3x9RJ"
    "XDaNhXirVrLKtsOF3e7fUiaXG8sIoOHdojLQZ2EyOHVfQUE+y6Sf3cSDCnhy6dY4gHTWx2PufOF56V7finNUS/f1reVIlcidHEp6"
    "eps6lPSYcqhDScmRT9xYv5O3dpd4AuJOP+HJJ4nwyvsd+Q708a/vkks4H//6boC3yzo+O0TyXemg0hcPvhsF83jax/N6/ADwTUV1"
    "3y24qrNbUc2zharg+4Uq+d1iKc70F/E6QHJChHbl70I83hsOsxgxjxxGJ7E8Tkq9OOVDIvwRb3IQCH7P74+Caex3fHVE7eQDnr7I"
    "Ily7uC2OcPemmUb4iEaTj9f6Ph+3zcCSPsHh+nwEmI5vTHygDz7yEE/HeAFHHOXAM7cwgnSUo88nNB4DZkJ5ikHcGEgdubi+xWMM"
    "YeZeQeoYQ1KN9TDE61Qt9sMQ0KNXt3we4smtvCcYh1cBEMZVEPeBFvsXeOZNfPMHo/GMzl/jfdkRTpYAiJBmSnA1XgSIqtnionN3"
    "czWKYDgu43jS+eqr6+vr8nWtPJ5efFWtVCpf0UFU1rSqFalpwZN5mpTWNvppUhiG8TAAeFIirlz3Dml17x02q8e4SeZVcTe5WqV9"
    "ggaoJLAuo/c22juAEVUaSf4GaBs1XJO1vWqd8tM7rJ9AS6mq/CBa2hWv+QLWdZVmBfcfXsgkAYKoqsAQHIqaqgKClqpJ/B5r3zmf"
    "gDyphjomsr8gGU9tv2BY6qomhrVgdqWhvWNXVW7GRNXEzGHSvszO7b9olw9rh3W0Hb4QKQIVXFGryaiqtrgigIPalxhWiGaoxMBA"
    "t7mUaL7VLshOifzYX2q64b1IjfFvkizMY8XIev3xdTsYjJCnL90fiNMyWb9mEk5feZVsWFC4zlvv6J5mvOzeXBSf3MqLS8VAPy/8"
    "pBg77uvi8z5eOOErQ9opYZxY79XEug6j4fi6dNW/Ca+A7aSmWCbVDyJ2YOH651BhaTaYBgHynuBmgqeJXWBO8Kk/+1NmHcrOcrVx"
    "3CwfNpsNfim0aEeuVq7UavKl/tZrHfNji7PKEm382OTfZ7XjKpfizx7WJguIl7de/ZgfRQOyBDVd499nzd9oVYugoZXKo122qqy3"
    "ChOg0ToUbwBb81g0KPPKX/4qwfPIJq4VPRR11jGzeDk+FFBDxnZB5W/R1wo/PMMWm+Um5hAp/Nf8Btr0MT/WYJ1XpzNanKEq4MLf"
    "Z/VjmVzl3rWSAlXRw8pxVeyTEqxV+vHEvmmVf489CWwlwb4oIF7eCuRLDCpM4sc6/UDffkPzXw1rhMVdE3cP6E1AXaNv4oUIoypw"
    "79XaCLEo0hIDSghrHuPZh3alJb43BdKoSDMhjaYgDWpCFakJIqsRkf2G66EG0Ua9XKk36Bn5XKV9SM91j9iuV/OQHVWbXovkiVdr"
    "Ubkm8Dh8rVcpe7PWqPN7m5PrTarZa4rirRpXh6dA4L1VPWzTe7tFTbeatRbmr1YrzA3rhwQNwoHvh7U61V+FPsF7rdJs1jF/zWvU"
    "8N1rN6m+GgwTvNYaHvHwWvOQsjcqjUPMXgdA8b0NkgBf2x5ybCIC4Ke1CibWm4etGmZutNoIS8Nrc2VNytwQ4qnJPW1CR9qYGwDC"
    "10arQh1ttqmyJqw0qCMgVDAdhcohy2WSq60mvJO0qbYQkW2v3uD3WgvLt5stj/PTEB16lRpVR1g7bNSbVfHWRPLmR0WudfHLlFyX"
    "BF7jWSk+1wwKF29vWwBJpYGCFjgL9sijX5jXCBgeJCrXqjWa780qAiHeQUoh+lT+dhmEYrtGjSHlaO9YUOU/5N8XHm65HiJpm6ym"
    "qThNU8xafmFG0xC5ZO6G4DMNmor1VTLyQ/+PUXjOMvKRJiN/Jhn0UomgPGGZkVV5YvP9zmLz94zYDKNVYlOl+rPLKV0nZ/dQidgc"
    "jEej/oTU12HAgrOE6v//lZ7/V3r+X+m5mfSskaBI5AXuFfORXmZwIKtYVKr3tHxpI8MkEcBcnN6bWKzWVvmb+FNt4VKrBhyZtvee"
    "IQvHFg+ZaFpCVCKqKzT48o1kMD8eCv7Ov5L+G/z4DIgMqK7OAoUS4Y2FDbzV8bWGooheAcBjfPeanFxrIgOvNUA002uDsqPM5fd6"
    "HbPXWlx1zWthMqwv6/QOqgW+e16D06vVFk6AVrtKYqYKgusQzd+HnFxpYPGqR3LTQ4s51u6xnIV3lLvwznIY3ptY3EMpTa8gtSF7"
    "hYQ4vMIEgDeW8CCyUOJnRdghk/khagvtcpuUB3hFXQJeuZ8VoJdDDzK3Wfeo0BFKeGXNBF5RU4F31FxoegB9QXb4qQjxCHiA95ZH"
    "C2qYpHUUly1UvOgddBzMz4oZDC30vy0mZKPeSJ7f4slQ5olIDSQWK0IsEsNp0ANg4ZAmcEMUrCYF5FvjLcjr9mEd9ACT3FdJ1Goc"
    "hjcDlqgvsxJVSad1ElVlzJOov+8sUb+/zTrapNtz8bSPLnWERxC8hf3jbfcPlZNvdX9/u3SSi4zf3m7kGO3b2/8gx2jU58Sv2PNb"
    "9itGfsO6whEa0MIMcuFdS/HlIoh/uI6kazRuZya9ha3Kg9XEBwfFaXdaBrID7CQOSGLVZWsNTwJQesIJXqNEEMuJC7YlEkV5Mp9d"
    "lvuTyei2GLlTeXWyECWde0Hjew4VsOs17yj+uj+9gGqieCbuIx7FDx/K7qs0dODG19Xulh3961H8t2oPcMYAFyMHDZBlaOFpf3Bp"
    "9OwndiAXQSFn6XTW9HBm9UEXBoA/d11RgMLp6DDZAcp3crcO+xFgH/ogEaz5tZOd1Nzqfbj9cm71PtwmbvUe39rc6n17u9qt3uNb"
    "5VaPJsYXdasHLf7ZbvXe3nZ/vJU8MuGjoN9f4dVK3VEd4ako7o7e398tHc1NHfuxwuVIHDyj6/vfSg8GT0cBzR6qgL1B4SVW7bU/"
    "j8ciF5WiJLw3DNIDRUx4No+DovBzMixpUNJ1SvJvFoy6wNz4sutmQAtfWvOIoXGgdJTttHOXzqU7DzwWjv3kfW8LO/fJ9fo+VwPr"
    "tlHRL0+Ei4OScvPgI4/AjCfC91s6Q3cPnSHsnTr7d7ih4y/R9QGAlOoq8zFyCzrtat12Q+C/Yx6U55HbT95+mMdHIGvfTRRa313N"
    "Y7rWPj6bBdNFAHQbXBdeio8/iI8Gb4mtHAenSxknDNLhAJ1kvcBr3AcHD0iIxf0wmhW/nQOuHDlD9OL4JeyGQ3ju4V9g+RaUF1PA"
    "K4zNRAbHgVn/eI56xo7lsXSsWMrPxRDg6cTlCKbNq/BsBNPq4GBaND44y6Pn82L6IyowSyTslehGCgX0RMjM12cWD+SLUqKY+KVr"
    "61gY4U36IAo0VCeaR3hwEBKN24qSS7z8sv2Dg74o2x8On6IThhciu2AsIW7kroTJyS8MrfvrwKIpnJoUzt0aBKJGtftwpDqAlfEW"
    "4o4IAGmyZthQK3HWYWI1HBvhMgcSnQoIlKWL7JtYSZZtZji7ZNZSAwANDf4Bfwoc9Dh3l9SFJLwUtetV2BmexulQzKpq5CxH/teV"
    "4hjYZ2cKPDACjXQ6i5WkUpnH3b6Rue/O9ErdQXemZPvBwcwddYm/+CeYhdB0Khi+jeGEzhIUlAGwQVDbi6Jsbu4xuhIAXoKYBpaN"
    "ALOAzUGK0IcogIDhtQQQg0QxQgEp/JggiyL3LMY4j/qzmMWP4oUBtwU6UREjU4hBBN0FSQAEacLOkd1Ch0A7J6fUAsj87kXrue/G"
    "4BGGXvQ/O4KIaj4KQ//4rBhaAR+gaKWSto06Aao5+fqBmRQm06XSCWH+TPOm1qw7NqbWGCbTtIxjms076g6MvAN3bpM87+cphyGA"
    "2kFU9JUS1afDPiCDg4JN83JlR2Ces0uXyRSwG7EYSDulelBR/nkz1dtSVUOUKJSuTtBjJTgiHjfszpkz5k5wxz1P8thJ3DkabjpR"
    "uufucA1VdWeQxaZ/DzDiNCPGpzFOVw4IPd+YHrvDTOYMJCPIsg4S7KsFEPIHNcG1zZB0iwk9n4MeBvrRM7U38+N4GqM3XnFyjbO9"
    "Hq+LgXA2HmJoBuVFOjd0ALvTtTiRlusNynPdjweXWutadpyHwVExYMYCeBq8BxEt3WAh14qJYRXliiqOQRn/aQwLCkcDUKsxm01y"
    "hmGmYZcZ2pHeeFcCs4/rz2AxDxQ4kBKUw9l4RPNHfO7xNEavmITsosVfd5k7sRSdINfqSKy2nAyFzKP85WA3Mos40VvxvTsd2tF0"
    "FsAiJnjDi8B87Od0eHbZH46vsS5tXIYBNkDz1r6+XD+0MHiT8Swo6ivPBO5sTXpXpUtlUStoG7t0glujTghnzhEe8e5hOvsT53Fz"
    "TFf3nCvPL3vKw70kerJYBKNzH93WYaW28myCSZVTho4hsAGc/ilPbEZ24dZevhrRMt7cmn6h5fpGdjvPW7LpvLnidEI5DNK71nwq"
    "/Z3FYxBSqnX3JJBD1NPcPQvadoRPrqVjOgTOb5vdUp348dhw0rV8div9wr65JYvWz7cWeXpHDsthbL5H3hidg3AdgFgcnfWnZXYC"
    "67CzNRK2lOkfFyhtMW7d+Wh8LSSf7/56Ufzlglb3QBj/uCUzws9B//3L/iRB9z81G97P+Hz0zxFuAgRAvP+4RU/h8E1ZxOXgCssb"
    "mYiKxIhLDGVpNB7grjl+KmOMIgXl8k4C2GEAjyaw1sTYSFPaBAcQ0ExT1ru/RFUdQKdmApcZbRgVJRjYNdWTP6gnv4yK1A3qgdaB"
    "InIDPGVqAZeaQPYdOEV6FjnRDToFv7DseQzD/mh8Ib3V+jLmH3/WAvtd9W9KYpu/cFj5WxKtj0L4Ace76hRmg/4oKHrZCJHT/jAE"
    "bYVC+nHNZU4pc4oZVPKmxPzDyM+fjIyp4JWy4hWhKjsFb3JTAJEC9J2FxYgsmApEKHJmslyHgPzBJR4o7ySoSEdQ5NIlMRM1rCpa"
    "v+0UcNGXVCyIKtU6lS+LNB2O81FwU4JuA9K8nNbZ+6PWOIqEUR9axsJJVf1ReBGVwji4ghFDV8bBNEn8HdSr8PxWdgXGfNIfBKWz"
    "IL4OYCqY8PDZk06hsrpbDFi6Vxn46fi4Bv45gFC6FiSpVUf5ypha5lQDT1iIjrnnFMG0XBDOQaIZKNymm1zYNng5A5HBNbUGczfJ"
    "ctGf2NqAz7l9YGzLCxgfSQ7p9sVQrmo/Hk+SNzeVyAEq8tMx5lp+KjHg/GRoeXV5yLCmCoZvdS2cJ1WRwUmnF2EE83Qa5DEKeZRs"
    "qBXjw1YFr1JZXBcehFek/+phUyV3xhyX1hzQP6BS4IC2ROxUfqrO/qGBv1mb/Vsu46/YO4pPsEYOP6CgLAEXHRozHBTWkGPT9s+A"
    "aYM+aJ3IlTJwdctsOkOhqHHz+XSG7HwWcJvBUQa3Vb0e1THj61R81L/xiGsfMwNK06aUiZbbl55/O4VJiV8Co0ihVqlczQD0s3AA"
    "TPZDGEyLZe/Q9dxytep6eXMMFo6LYLvmqMhWzf03qJPn6LF4lge8xienMKuTVxJ9IDgwDILONq36RKV8WNOY5XJTGLhHWsDj8SeG"
    "wE8CsV71Z+/zA2K6UfeEw0W6PtEPXZma8F/xXfIe0jkpSo98EBk0tuKfkofsou3QB6x8QEEQE2fpaLE4FW+ZgWKLcV1R+YCJQl8K"
    "5qtBsOhG+Go87I+WbtRLKtq/i5Z+x8cDo7lxaGX3k4i0GYDMOLQIV5oJUvv8gnwCo8KqtCW0zkKn46dEnPTF65sahC/yP2IBmCmm"
    "ria6k4E8+yvCJPoZ2ErSh/NkcIyXwTIZ6YqYyiUluZ9WCdFTP0puLYU/YIBRWi++Qv18JaWJMSds03AJVN8pNuqfhzfokF45+ASW"
    "nXj+pBeSAhUXJUXFlZzUR43Ad4U+ciw6waGokDhh8S1iTumvGvX2fFaUYC0e+1yQCTkpabzrtC7KgtoDxMb6h++SUvKcdJJYC3dl"
    "gUJVbYFBTLQsvJuCMRmH+ECbY7MOTA7U4X151lnMi7sUGvHvEz5fhmMCS4r5VZSui2si++Kvyr74RKzVZMxCLQpuOimJgitmBxsV"
    "6QhcKpYoE15u+iIkm/SKgKZEbKuikUq6JxrOb0nk0oPfWqOfinw/ivvBObVpHGMF7DA2V+GMbEgvcWbl58SZvKqyCmcJfoiekmv+"
    "Fflml+PrZ/qw2DKR9vKKVvcroDqDsf+Ndx04Ex/MUXkqvPNpZLG1pniEPYSwIHhobxr03xOpStSzOTuF/OG0f3GxBlvvg2DyPHob"
    "Bteoba7IeBVGv+T2DhJ/ze/6dhZ4Gr/1gY8l898gpzjAuj7nIJEeOl2nkJu1/KtoUlqUZ45R/KCiohk/qCTBmgGhy6QLX67Fd1IB"
    "EBTC9qbvblfHJ2a2tjI+ceYQcSoyieBfdBVmfI2Rp6A1DNJyjhqOeNHumc4j7QXpmCUGPyP7P7WBTEZz3t4Q0LMY/yk477yxbFIE"
    "ZYUQCu2as7EjdnuD6VvBhTkUJL+oUcSNnyTUDygtzA/VF1JN+JuwhosAttL+KKJdyPMdnFW1za+keKgEVADohcXLsZmXZcpxugLF"
    "kIWaxLVpehN9IMoQO5KCsSM3QXMKvwmgn8BXE2I95Wk0NBNxa+9HGMFfzNdfk969HM9BkAIeXidIyh4FFLtAYgwODopqk0kfqK6e"
    "adWmkHYs8IkA/1UMLcq9JU76x2h81h/JDs1k4jBAJwu3JFflN+yJOJOYcP6Dg/NheQCcVWxgYCZte4wg7zKByOSuEKM5u2CaIBCt"
    "8bafgEXbZaIBzpTfx2lazEzSBx6dvniK4iavDM1jAT3Tc/fbuex+ECGBKVQGcQyEoxC2ApcpZNGGAGk2foITUYmSuTI0sdwFK/PJ"
    "4/IHSmUtnPrzCJmNvVMiZA/mekxE8gLXrZZdR6hLbsSFszcivt/Bwc+jYgo+cWrBWM/pFgGMrcjkI+aVGMCc6bM6lSG3wyzGi3gs"
    "HT7Sd/mM8UtIz2RatgTgb4I2BV7tjW9H/HLaAiP9qBkpuqwJF8LPS529ZM+3WbhPN5Db2HrxN5NMP1MarBgtQS7JbO5281qS03ck"
    "tofPzYNOUrbZb5gEmUBVydk17Lo8w8TOWVguQCkRW9oUE85RjCfAjRIsXlSJlLQBpGdKCM1FFVHbn7E8Xq4Jol4xS1ugu8TddEYW"
    "UE6naCPSpIQmzBw8cAdgINm7d1RCCnE6k6ikt40chFzvFc13RZ6Se2q6SuBI6LTsFSO7kdlN6CSFGGj3n7fiiGVy/qLzR/YbHtO1"
    "8ludfIp6Qw8y1KmtcwQ7NWw9JmDOwYEFNHle15iunxGEP2wgUMywzPRGkTCkg+u8KvT12SaXinSSPZzhkT1Yhil+rGak3jfRiNJt"
    "MuzArtLJIc5J7oojYaJ2PlRGx01cvounCloOVr/nuoSczGnByYzSjj05OOgW0zBZzyhvBpYrTh8rSYAae2ZGJkpSsCRd0ZqLGG2g"
    "DBS5NeFppGCZVp2t2VN5sFiKa1qLpfIw1Iqkc4BPMbtu0Avw8KltjWrvWpKeLZsoh/pAh+dFno660p/VcpIDZL5/JO/hRYVQHALS"
    "dFEnftj1DWu+/r//vgpgWVZgJwiFfjQsFHFjS2z/oEHbSe0RpP+n9ljEwex9uYqTEnC5pgJtu2k/o0mfRKdL6/ab7X/L/7Vdik/3"
    "zlJ86y6D/W4qC2rCcs3Nyn1ygovuIcWO3GVYZitTU5QJQHxG53C3fGY2XYIv+vhoUPhqgC75ZsyIjEwuWlgHIMfWnENjdTz1bTbJ"
    "nCWk2hy3uD8v2o+R9eRJbPPAl3N/rzqIM9URKcd4gyYLtq27IXrne/b65YuujlFcm2truwxvNKdLN9uUYIlFxd/CKCTVPSWdWMfk"
    "qTuL2V2eg2eIVhyTxQuJIpao3CuRawRp9pPLYrnCUJqIWoXjjgX+mp9/FZ9/Tann3Lcyb513/Yqv1vplOqFlO9dbmkd89pc2l8k9"
    "pcuhgB03u4w6mxeNKt27PdCSpyKW5p606ZtqvmYewjNWrmVhkBVraRzpMlG3aehr1id5iy+5jjHViUy5lKwtKmG8DlpTZNvAy+Yw"
    "ALRlskCT10qOjS2zIn2RuVLGFwcDRYLyFsLNvBgkhOW40+53qS8YgZhosxQk9Or2xddfta+/uuOuVhTnzWO0gEJzx6OQVAC67TXr"
    "jsu4sfQwdAfwGI8nD/vuqLs/grR5V7+tQQzWgGbYnfSns+Db0bgfF+diCmCQYzzLb0l6PZ44R0Fm6kgDf1duAmIcZN0A3yvOvsGd"
    "wzD65eBg9jD6esTHNOnIYTJtBWrcbAvYwe6sNKTg9Y47ELX9enAweDiF2njX0ajuV4lTS3WApO6gdM61wdJmByDcHVrCA/RrNd4r"
    "XEGTh083lxIz+m4eWefWsLGmuxE4UhCsmK2bTjatiDHfAs2ipM08XLWa7Jp7sQnHBlYdGHy6mGL8+PnE11i1fwpKIt1sTHg0mu3J"
    "+cCmYzufWFCpdds6uDmYXG1b22aI10Ilxlg/Pq9vVh3LcxZ5p+kTAwC/attXPb4blfHh0jEK2nJKo8PSxRPRFGgbRvLx7fNhHhjJ"
    "/qiUkaxtPBB6HItgcuty4iexvKHWs1v/9AFrd47Q2ULgBe/EiRC5gYzS8pEEJg+KjFV3NMbTQGVssLc2B4tktf5BAv/R0tLzUfEu"
    "2cYxB0FsrCfmCt4pkq5pZp27aTiZgHb42ztXXXzqvL3l4aeBhjxia+U7l28ndZ7duuYQdl6qL9Ii9ejWJQexnR9u9SsNv2zm5+aX"
    "/yQ/N7+Yfm5++0/2c/Ovz+Pn5rdN/Nzsf1k/N7/9KX5u9rN+boKzL+fnBtpSB8biM5ufm1/W+LmhUqxZ//LF/dz88uf7uYnOuidC"
    "WUGf/PiWlj8ufxFbh0nm8IxDKpy6fb2ShLuOz8wLY9jeuPuo6DMH93EZAW/ikiko2N041H3tJM6K6OrXzE2ugAbaJbE7ebTjh+yx"
    "hJMwsyNmOtJ/VhQRHabBeadfFpZQEc0AWO0NbjLM8CYSn+8IyjP5CWa+mxxF1M4rspQLpIjD7S5UdtBK24lPPAwUkJWb/XJqU+3g"
    "IPNJMLu+qzgS78WxKgV1Vzeo+80kVfObibVecV17D7BCsh4dmEziK4kPBwMzPB0jAunQXiB3acX9K0dtemNj9GRuG+Pn5DW1WYyJ"
    "2rvakMXv8ou2Varq4jSkjf60A/NcwkwnoEM29jirKSaQhxx6b6LiKlrRDewGweAhyRTBiE98i17eUNtLzTREdVqjFJmIlPYkTeWN"
    "TSgbcvDmpNg+VGAaFzTVV3IOAIrdcR9vMg7ed4Sip3bzVILNt43S7cjDjTTJaXXJT5ZroAK3P4q7n3TbM1GUV07T7EaDMQBCOU7P"
    "vEre7JBA4sSQz7Y5ochJNuBgFI4EqfKYtnC3cF1kcPiUNmTmdFgmZMd56doo8dJEBTtzULgIbRUZiBAtJ9NAQoLRS7hyx/VawMr1"
    "sCFLinsi8Z5F7CMZbCSFD/WdyE/flNaRJClGHiHXVguhvlTYmvxsKPxQJA4lmbu+YeSqfX1oV98vNzCYPjJPRHU8Com4ZevoKCOk"
    "86hmt/0KLBpLng9La17tQ7p8RNxZDi2CRIk7AquWtvek6RovhE6kAXuvI0aAotcs1zA422Bw2Bv7UNjwqm5j98vW9biTUI5WUy8w"
    "VuAJtuhVUVO23xTfR/k7xWh8WDVe4gZiRXp916ktOUWNKoWzwVyuL0YMreVioOhYJA8EPE5iqOp0qfEmORfQuCaOSZvsE1mkomAr"
    "A11Ljubuo50c6ThGiiC1exkGNTLb1oTKnvyoLAN5hJg+rGtSodngpyZBalvQ30pSE2AaFhmO+uIYfEpm0ujJ6MEnI6YE0yvJydMj"
    "MnlN/qORmMZrE8WCd9vFyJ/w0MurNY6rfCDQ1YJTpWro1xIsSgIsh//FTsXK+pUDRyJKNZAWbEmQKsRL/wxL8I48+sEwzkJZ5bYn"
    "5HZ2p9+gbXFDKJEr8kMKHPHZTi+PiyjcOAvG5sJBNTF+6jbrDndleoZ1nwzcO+UL5oFU3E9PTZmYkAUqvEQJT/nWjK9rsvSq6a70"
    "njwlaioSCdYXpYUvNYR+KuQaB3Iuf1U+KsZntBqdnRlB62jpPL0qyZP/Z6kgdMecrnz5WG/BaEHpRH1sUMR3CgmmXjniXLr02Xx2"
    "m/q2zD++PpAgyXhjp9IttnuHhTrxkoPgRd04WVVOYahhoSGKwDy2n7mVS2A31J1o/3oLnEl2PUjOndOKzZc36ToitFtyRQaIAvvm"
    "7vH1t3FUCmhnck+l8BS8E3fP6tUKbteAePuZP8C6f1Dkq86lQq06uXF8ucQaji72sO29cfTG6MheJ+TVYtD9Jri/p23FO3G76Ydi"
    "EfoFAuVJ8TvoEnEhnEXJKLnWew2JlAnKPIaJFyTZRw0qGQhOSpmpFipPcj6dScq6MHZeBjaNohLgJBg9GcRQWJg1SB8oUEfjPnkh"
    "sEEqiUmCGrK+D7iLiirVscAvQUl1RbSFs9RxE2FGaJcse3aGjCm2BfM71eZxQvJyheBLypJB9xKSQkGEt+RGyqiCoRADaXlBS3h/"
    "EMvglUIKITpg+syxzGw6gMfhWVewXo1JBFeTGM9PT98D9Z2bDITTRNDLiZkmIh8u3aszSwRMDNgCaZciraanTcfXkHSR5kZPsbEk"
    "IqZkOnTrRouIKUNlhlf9C3ogVDB7IjRkmE0qeOYd9arzfpGEuByfn5P/peBWxbVE63E6rmUaMzKcJUGAK3F66PV8I1WAtUfkTo/3"
    "94Keae0vilkCXopce2o49/TMkhhlbbRYJqzghgBle6BlU0I4vLrw3eyI8VhTeSDi6aAjKnP7eHksuUFbr2t3a/EluQbnn/dHM4p/"
    "w/NpjlLMAnFq8TqEGVMul6c8OSmqpu6hUINuNgkjWX0JxDh6bBJ8/FfuUtUM62nBrWQpWpIYfkiUEVGR23M0UHRYiFeXjaCi8Ul6"
    "rEVYUTXEPa/dqVY1ziKiy4pYohyEyEkUvfMzCic6Afo/S8URhWeYAvf3UV4QUSh0RUwnsvq7Iu7EGhBWRPpPOrJotDKy6GWq9tzI"
    "oqMz5lPvdD41eB+oGLthtOiPyD68MLkJeiIAviBU56V7izXAR8h5JrnW0r0Rj1ULq3llrxD1V5hmkOHYxqdkNqYOYYzj6bd0r9Ms"
    "6lvI/RPerxNMaiRVH6gGfy7DiHgVMxbmTdj9fJakVJJoFbcRUGr8BmsV3AAfFUfZ09GMGQiU3oOK2qRVgmpxhgwDqlaDLaSfwBL2"
    "idKXRJCU6LiHMDSOMtSJmXp2pmfxyB894kIn0RvOg58pi05+EqRXebLTlR3RKjzmCul7ukYkxneCGF8rYjwfzWeXkhQxrgtQ11OV"
    "yvF93ScmHUH/gpFwqrB0f7BJUM6CZFjQ6PG9jVY5axIX+pGtMaGu/57fFip8kONlmj5/xNSsCE2LTo6mBlSL+Ejr6xTvZjt6Va5F"
    "M32RFEstITnSQ4pasUVKC/HcgybMqAP395IeMu9pZqVsrZlpzmjDdDMEdZrNswxFHm+KlYrO/0UE6UZa1OBPtlE2fuRFkzbX/JdV"
    "H+jPnAPCn0eKkUvpQEolrE5hRDXE4GtKyP6QqpaoNFUrfsuKBzdeKRzepyrOFQ5Pz2wWjkf56nLScMqMINf6v6fKStNAuuXXghN8"
    "nycBBAGXhqBu63P4x6xMkVmBHeME/tYmIl7J+SAmIgVxd3On41DsqpNngtWT7UXx5Zk1vroGmnQJIxesOuXqlMqzH8lXWqrRLg3g"
    "hcW71NoG3TEqGHUe/D3zYC3V5MRqmH9csyoCVelEDTfHee8Jzx9MqeeRBEavRkSExzooJlfFX0qtOUO1ojrl+cZeo0a+XKVnqVLQ"
    "o4qoxeRorzAhShE2TNUHX7xKrerSjrma6GkGgYT7XAmpZKlHr5fBdCyfARcjFGAvTKL9fXzGjG/p/mSjf0yPL+dXZ5DhQ7ZoiAUf"
    "5xUU+F+6bxFC7sGp+8wmuTA7uvgNRzTDovkVFHuTbZAOewRanp+VIDWdi/Mx96X7D/OAglz+0sGHiJwhCJ0IWg+mV2GEK+dT95+r"
    "+oRd+iMvQyK+v0vP/u/GZ2rW00eY3vB6MQ3Q20vynJjQ6Ko8MQFETf4y1sWhTn+jIV+33g3cqPuG6FI6Ay5LMGDtE9HZD//ggA+B"
    "lMPZt7jdGRSTXA6eH+caInZr33vZjy9xo6ZYcfkxjNCS5eqFOhUVtk6zuNnU298Ra2sXy3uK4jEVf1NJhA2hFKOekNF41R7siRrL"
    "M3aBe7eHH4Ctn/WjoayebixSXctTR6vmxZnGq2jqmBLxp7QEp9nlnNr44oezLN8zKnucqizheGZtkwxKS2ySlsIA31iTxydU5N+S"
    "zZ4JT2fqzyRTx4RcXf0NLR+Ifnvmtj2inBUKSiWNgszrHUk+2W1+zE+URM5VilPO6NACWFjtlF2AVCn/bz6ZALhiU9f5+cz1/7//"
    "5//1HZYuP9lJDsZarfgk1dInY7ssKBtzttdj/IlMBCUQ/x6KHuNb/2aP3I0ZX4Ed7XWMOWR2t5NaxWkca6/zIJIxJXTCFqYSNjVf"
    "BEVZu7A6i5ofArqk2JH2zjrpRv840/SstGWB0PbPfNGtq1nVdYriH5sqis+FuvarknrsHQ6Y9i9phvvP4PYtdjDRtchf2p30KLft"
    "yntkksn7ha8GA6tDeuAnbRSgME5CpGdC7EugfALDDdJMD8ldrJNdoxlhFCUeEwsSN5bURMVDnYcxz7oaR2M+BBSNl64vxSYyLCxP"
    "o5+4pxevXd/v0QzpiE+OW8NhgIaqbYcG4VcxCL9tJl2FeYue59H7CO8kn7r/Sg/Xi2ChLVDPxdU6XRmWJpVNxJgsv1qMyVybijFX"
    "L/J3mMK5gixrphxx/5ipXAWkFqbYCQ/+F2AfqRVuBCuEvlqQizHalKtYuInJRn4T5LKfWP6EcymePCjM0U27qazKZNR4T93gxlAG"
    "pSkwvklZaKIbkyRP3emNRVWbgtI7nsfQ1RAX9uGNRSmVeWbzM33d179J0e1PnC9r+Euv5fgM8x3enAlJr4Oa6QdNBsSVJCY20eVc"
    "MUwvNpgU5lSPtamuUe/KPY2p7OSeGkDSpuAX6OdqmLBC2Qdmh/JtI3VM1jHA8yHC1qJbJ3PML5Yx43VSxi7DANMp5yu/59U7XtOy"
    "J4AnsVLG/qyNRpCw1VRD2AtuLEw6B608hdW6xjJJE32TfWUoxPY4PUGSTRwrW05KyZJzmfGYYkY6fcEYS869ZP0JcBHdOLZTmaze"
    "CdEhtTCyRCHdA/h2IKaML8yT0iuhqfiGwpjOzzRDFryZSkR4k1KH52dpKxZ8suxxQAP7gkeNb6Sv0X50MQpK7ECDjaJx/wLPJegJ"
    "uKtFh9z5bRjgLf9ZQNvB18DgT2FWLi46dzdXI/S0exnHk85XX11fX5eva+Xx9OKraqVS+QqyyD20akVuoMHTIgyuH49vQAAUKoUq"
    "/pMhx/kuthuNhwGAdOJPgOFDX4cd/6VXpdjthVa55R22asderVxtVpvwXq8223UMeN+qterJe51CvCf56+VatYZh2yseFCwk7/V2"
    "q9ZW+TFse6XafoHh1vEd2q22K1C+Uq5i/fDewAjzh+VWk+pR73UOLc/5XzREqHlR33Gj3GwhXLK95J3hkfklvE3qXlX1p4ndg3Ly"
    "vYXgVtsyP8DLkeUPGy9SqFoV0H3a7F/VIw7oPrtJAro/QmJ4QqOfF8tdp5e8MO7jm13DuA9SBItXJC3kip/9acikGZI/bfoEjIQp"
    "9k+g1MNyo9qsIfqbzdZh8/iw3K5WDhs0cq1mA4ep2mhger3e8KoFSWk8XNUXkhI9r1yFD4py4R2yNwva+2G7lVC6olQxEyRlypmi"
    "3gV5SEoFyjks17xKo/5CEpWsShKdLCqJUr5LopX5JVFL0LR3Al3l5669kJNGdj2FulWUO/tQXVTHTLmjNOW+mayjW6SSPKod7Ey1"
    "c0W16Lv5eTShSKpZr85Ph3yh69l4RLs3mnfn1DGxKyCwkVju+SRfRFQadleKilmSxeY0WV1U5fe1+diEt8qlrdhpzXHsq9pbG/UO"
    "d1uvjnmv2u6kVtSFTeL3zl3aVexdutX9yQB3I3ITvg2D0TCTmuumdfiOlVvhlDPBYBJ3Ut7ilUOQyeoO32FHn/CnR5PJKExF9NMH"
    "cBgEE7zyxzEzpllnTAKkbrBMjemKnO4+QkChuO7CK/KVFAd5rYjop0fC35TAWTcJW8qYTJzvYHjdaXCBd9WnKQ884qJf7IoAtvva"
    "kDsORgpdCuAUHfw58CXQIZbQ6YsO3BNj7qyF8IFAf3bYDw5+5mBfuTmUQx0xeg+63cTpjhxQCphGkGVB8vKRdpRGURJ99iKICY3s"
    "ENPEhsOXqnUQshAhrs6TCaa5icXLq0GaRNVVa3d6pDwCoZ8+cgVh1u1a/MrqbFH5PBRZDC6JgaOBAorCE54C0SmPo2PKoghFEMPU"
    "vRtPw4sw6o/IV0MnFitcdOjsYnyO78cRHdzLMgw806UuSolgHj+bfhv2UaIFNhcJPxv9hrb2JafNBtx0o642SGPKhmezBF1zXzVQ"
    "tcCOCR80/WcBYMm3xIWWgMHNnV7wfTX5pKqMZZXqXmsWWhFGkltGJ4wJA8tz6rACESjSpHMJjdf0xP6AwX9yqteyKN/ACSJ7eroE"
    "VsGyEuQEFpXfxnSyFLAGeYKKXAusaCQM+zx73BRdpIK0ajlnaco4MYf59FNSiJoBCY/bBgM7Ezvj7DN0JGFvdl88btzNdweh/Fhg"
    "sEjNNYG4RY++Cvm6UuwsFVLIybXkkQ56RzW/oDPGoq9rED4xcaFUsvEuP1bH+WieqwKK+CJodoniFZVsqddxixnVTWOtssmcCSeS"
    "ezlOXkJU199yHiQ9ai+PH2Bir/fggSIU/ID4G2aXAK/JRZ3U8ec34pJEJmQnAcD+7FJRO1XKqjCJKtOGMRJT+fUAiakgmUnOTJzM"
    "dLDOJKs9XqeMqUqb0OkiIrF8ayshNrdyitysDwqqgZYTFzS5Ht8xPG0mXUlVlBQoD+dTcqv5X45rlKVGti8m4uztWHo8jxFZpZ0b"
    "l6FaNymrhZQkhwM0gwtoIFkZLzYzHNmQsUY3RBhW5hT5YWWTas3IskksPZWjwz6uh51LdKmvTS0d+elaKa+Vgla1QLdpNmyB8ubS"
    "aH5/uRyyWUtQXYHKFWXI/PVfzopKkSetypCBVY7f+Px8FsQr2uYMKxBJz6QgbYhEkXvTgYJnIR1KrJ/rzeSyOM5q4XSbtJBPfeva"
    "EyT4ca1mKHJdq4IsN2m1I40/ekRkGZTR20R4yApypIh1yFWZtbOyMxn1B8ElGd80EK21alk3oSK5ZNumCUmr2zRVml2ldQGbZJ9d"
    "2YX7SjEMhXaQxFqpm1WAjy42AXx0sQPgUGgHwLVSKwEnnc8auPdvR9nIobmhM6VjcYrnSNq2FjozUfQy0TN5GmLMTGFCcPdS9CBe"
    "aWkD73huItkXpg29vdRAGCXw/mhSYoQOpEUJcbMmLkuLBH42+Qqlik9YnL+mWiQMcg9IXT6lOIgrA4UpBXplrLDkWvT5zUauDM9v"
    "/oNcGVKfE19uk5uMM7qrmy/njO7qJqH2yxubM7rzm9XO6KgUO6Ojrn1RZ3TQ4p/tjO5CLSEty8fhTWZnS5laxxEVyG4FJDbYonIN"
    "z7aOwLRO0q6WZdH7jC0dmnMtl2LY0UVloVkIWwjzJrX9I2MZ0dtS+llP7LArXagCKd9JiSrDMjAD4tW5aBKfXQOKLCdaCh/95KdI"
    "Pjlk8niHh6sWYo9NOLVQN/jF4T95i9O1OPhb3JgO/jR3fXj3mHcBnxXZEOLzAt/iKE1YmZXpTviTo6O3mnMC+SjOtWj3HiVyUueO"
    "EtcnriSQFU7ARBZ2jkePdhdg/TLvgCoHMu9unOXFjfTOsbih6Xl707WbOcThRauhg9M0Sasiv7MAL2Gk3SNLNPlpgKEtFoFVhnOt"
    "ImSzrXKzVopEXOKjtQUOk5okiojJMspzNgPW1SngqQH0pZCNVS+CAq9RhRnkMoO8oSpslsksyYTSkpNdrAF3s4iIqra3iWxe0G4V"
    "2bx8jl1kVQXracm22pHjnIz+yhqicVxU1TibrQjNkctbE64nES65ar2xElYOPbgdsFxmJ2hF0Q3AFdfE187/PPaRTGMP/jOnsTQw"
    "VjQz1w5QsO+w9byIIpQPVWjxAocWt3HA/tkM0mKtC7DcCGJeLnGMdDKLptMFYw1w0IxkcRaqIB33/A10aXTbk+T4UOKblHJhvxUe"
    "6JwWyhTLuPCaDJCcMSNSPxBYZVAk8PL4pmlehA54qgNbAUvHILcGFsH84qDScxY+Y5xXASKNgQ9pHqK2VqZFor5SXgnX5XgafkAH"
    "Z6O1E3CFtd6KnQ3m/rrWN7X4Wnnsp4Miyzs3AUNyz08Ax4rpJwaltsHk24yY106MHasRJC1423qOvAob5qQRKKjmbmNUdmtnBR+R"
    "UyEH6/z3E+D9k1SkMxM73s8xghFfHLnsz4q5GHIKlElDBMc8Sg3uJlqrfTAWGEUAGJ5uelwhVNdU8lk5miFOcspJSCQ73rDzfyIv"
    "XAPDF+KEeVCs54OfdUZ+PEvN2KK12ln3WzFLN8PQbryRFpFo+6X1tLlQ3g6C9Vyz9vlY3cfKqvXjs7H8So+EbY1iL7nBBkZ+sTVQ"
    "yLrW17QjwW0GrCFmxL6Ik8Ov8evAoKPUbpSm9ubto2nmlA1yX2qnddZk37B3o4tP0bu8zTZ77/Jy5/TOlt1OHoNR0J+moV61to3H"
    "k06hoU8poTZQAq1vSl7h7zxbB+NIwFD4qlB1NrDJZZfG+Yshq/1Cy0rNr5dQNjUpQYuz8zKvmA854KcqF3oaknZZdVoHMIvFz7rw"
    "lO4HPxMi14L9iTGdv4r40sj+NHvbwrav7W7LTejrKR4fm/Jmd86es54xuyGOR/j7o9H4mk4Bd7sYnzJTCE+xYBl60DbRTfKhnfDL"
    "8TU7y58dHEQCZy/6t+O52MMTbj738kZsg0qSzJl6pGDcoBaZNVNHdsPd1bfUfcskwGEGwqLrcH4exfkug/APtF+ms+m2TbyGJ9Q2"
    "Ea/wY8hGyrbVyjtTkLRQW9B31b8RsSTx6gu8UWzf6W3RQQQpPfOzAZzWZNcDHEY6wGGkA4x7qmfZQ8ffiw027dixdEGCXjHivHt5"
    "laWrtb7i9p5OhPZD3mqKLNNUQPEaVh0vTw3C2vyqfqLbldcXVdXrs3LYz03yvMSbfCoQQE5WPH6fgykAKkRXJXj+PjgPb1b1dTY/"
    "X5ODr8sObleDI3M9EZsOKzMDr6TJjlaJfMoB0vxW+JF5El7gRVbOy8SYRUj/ZpvsUxGC+2U+Hi/7o/OnN5M+xgUW92nGU8uJnBN/"
    "EITo4eB8NMYrxX4gCqGHvWiALuqhpmPOg4/finx6A/TyWsuP98X8U/RiMZoPMWYlbpQDTuzd4rECHKxKnsXBxJ4OUzARdivG5BK0"
    "8hFq5j9E31IcgfwpjRP/GJn8ijzk2iMa3a7Iop1jXD1ngU09H67Nok/+E5GNTzGd2rK/4ggUtvvEnEsPFXZ2u6p5lXNVpmnwxzyc"
    "rrrovBSnHG5vNjjrxqO84Wm3m81Ou938J512uzFPu7260QP3Wk6CqWNgsmen9/fBif/f/y3f/VM89/UgogNnj6bT/m05nNEvNET3"
    "hx9hk/AIzUQYAb0bOUd8eKzihvopGnn96m7WCd3IcqZp+k03EAF3e3dDdHADU7Qjnjx5BOhk+vDhKYaMSZ3kwgNoeN6vEy6XmeNo"
    "z8X5+H4co39+WBwXuIcBmpRK9Az6RUHqLuX/9TxiyxlmPQsKModL+fuIgAKfgpvx6bbL/iIo9AsZfBadAh9Bw2NuiJe+O8Z7zDNQ"
    "wBOEaMiI1KE79KiVvREXlSNQW4rqwOAYkIYocoM0TmbYTr9LSNFDs09v78a4HOAKkhu+4hAe0A/e7x3d4pDPHMZlH6ZWQlfHN//B"
    "AaGvbz5LQGjA2fqA0K9vvmhAaB2mLxcQ+nX2DO7TL3gG96l2BveJ9QzuzZozuE+SM7g3X/wM7s2fewZXIeGHG02qvbwhcfA7/zzi"
    "n/c3RS0/vt1twphnE1SjvihfVkA+SkY2oL9StCY4kQj/nrPyIHfvljCKjC3JvcuzUTgIim10SyspK0LkMoWnpT2ThP5FOOalMi/7"
    "EyAuenwVxH6PRfH5dHwFLXXo+yPJcSDjV/+n2Ou8Ce+fO1EMT+17r3lfqzrwCArj1SQYOlzD/lflOJjh9O+J/qi7wwonNKh3dirO"
    "6g8PpG9RU4vgzxJ3BvRJSy9lS2lFQ8e5ll+AfIc0K9wcfiM1CHIkovQJ50jy8wjUkmmXK4bRi76OjyLg5dOT6BQmZHQqR2pKwvpH"
    "87R52m5wlj1vLl0UCXuRL0OFnY3mGLwmudSdvrMtbn2zGeRbNkPQ8eF3zO1G4k2shsUbGZLEMyym5rNXuJPI72qly69iacwvYiXN"
    "L3xGjZ6pvuNLiozthrNXE2itP6IPlE6WSd50YNcD6a+vaKsu/fVpNORv3G5SHwOVvMch9FU4X7K7HRK2ScNJkHRFtKGDnMTXC0Az"
    "KyubnvL5Qs4M9oOR5gSGVinS/UqqHGblDGVxSLG7P4DWeuwJreOzV3Fc8Aqrienshepk5y3Hcvr/2J/OAtZh0naULQuTZWXLMop0"
    "diwnzSZbFtcNKdv2MmNd2baCjL1lywrE/NqylJiI25UCRIOMjE2HGdJVkJGdxn8exRbfGkfKE0jeLCBnINosCLadBfqtl56YBcI9"
    "oKN5QUIdkoKFWG7X3Jm0TzUan4T9QLkaS2iXESLeMqRppIqPBgHyICQfXIpLPb9KUQk3nKY+jk2ekzlNaabxjvLoX+gSkjGsmWHX"
    "pUY3Cq4Lz6N4VP5e+1rUMMd3fBKsFx1WY4IuKHXrS9/pWAI2TCsHzHTYbjUb9VrVq8BqYoohM2dB0XEZItBgMKQQ/DVpXQayd+NT"
    "WKGxwysp8ro/BRdPbyZF/2T/Lij/Pg6jog+UcwryFBQx7gaLwK7skgQMiqGTfsKRyKjko8r8Un6x5JakoTIfiw+WvEImq6xP+N2S"
    "k5mEyviKXi35mC2ofD/SqyUfie6uzQiFxdjIamUkKY5DTsxAzuXwEA47yqNhtWrBcJNls/jVSenk36d3y6Lz94e9svvvf/+f/fv/"
    "/e/Z6VcXrv/vf+8f4MS3Ychi6FhLiLBSh393Sws9ow/gDJ0iKQaSWL1yopbjmidJcHqK7ASldTQ6jFVXTTpxgTLLsAC4KjqpHIKY"
    "XY10CQdZUt0FCWYvYclruH5S+pzWv6C5HtDyAMo8iovo3Frru1Gl0RnLVPr43nhJbwxOIHoCC6vtMJ6dwjqMuMTRhcIWUIuberKk"
    "/1FCyC5nKjkipbJOeqxEoZeg7qt/z3CS+quowkwhSjCQnG5JR36ah9lQz2zP0Z6JdrX3o2A0C7YdmE+iHCyFcNLg0tEIedDBouc7"
    "J5XTNCLE1NHZaDFV2f09IlLDV1o22PDF4sTRnhN88fufh69PT8fpbuag39sc/UllJvq53qzvWLQLCVMGPaPdpeQnFj85LlxeWhl3"
    "Uchk19igrk8OavjrijQ/f4S+tgn/BLyU/KO4mxZ7SpnCTAw/0GkQA3aDG1b6HmpQP4yXSIiFuGt+1GUVDwauLh7qFAx1KSOyMrIV"
    "Ja/x8VgA6inZwZIHUkzAuVILN2OYbGI8jzMaoj+HNeajrZRJFGqk65dzmbCm9TFhMC8w6TAWRsmHyg1kOPu+/z1a+ZB0O5Ha9RCb"
    "tBNYTBoKIRrn2fqMDdIWoBhi3uDm1LAb3983KhXhpRYXgq/RfiO1UzLmdIEo8Ot4Hhf11V2Zm4XW6hVyYxqKUhjUm3yL40X64fDn"
    "ML4E0TEITR6o7T/pVOECxPpr2I2SIweI114kWUWZWIUwEHZwp2yayjrNyzruepW//11FC0LHBhLTWhieYvAwdv4+dr4aL13sVAp4"
    "Oa15GU32QrVTS3iIg8nfY1dKP0XjmVK08GZnmvf3uOkqHDqyx1StTBqbxSlgWbBVXiSQlRP6wyHVKLy6GBVOR0aMWxFyrNjE9gP7"
    "QoDvU0iBYRtHbyZ8OOnlGJgPxkqwuOAWZ7rQd6itR2ToKyreIoiFPSpgZJAJrjCjWLiCBZaZaffNJLNQThrN0Gym+Iugvwh2reGf"
    "we3uzUPhDM4ofN6QJM6rCTAGH+N3yS9P8XC28QWkwaQ/5O+OWNilkYhNYjufc6hK+WOVanp7dKUq2Gm8kjp2GjGj+OcfsxIP2htY"
    "lqe82QhwDZO9aahL8QrmEqP+jNUcMXhG+S4eWBKOTo7TJv4MkaS3BropbzrpTFRNkmkWjPi2IX3P5H4aDS154asNQtxuSKltD4qG"
    "ABPDqVw1JNoCbjugMnhkgt+19rHX831XAyt+JSH7Cd2nF619tvVN7iO+wq1n9Ps+vaUjCCCtis7RgyJuA0eoFuJRjyMpfkX8tSMx"
    "dN+zkoBDVwwlAeGp9ykSUOjehTNhd6FdIlFK+wSl3HCmlvIyh/oA6Uvg7wO0vCJeo3JAG3LivEhUPi+S0yAxIrYpkVElOLbVTIxe"
    "dMH6bbk/wuI0O+LpSDxikBt4dGykKkIDKILu5pM+r4lS2c3hPpLkYKfOyE6LIKyjUgwSOEX6fVoyHM2uQ0IcTXjsz3voy90AQ/E8"
    "mk7H128mfkdXgays8+gMMPf+KClFkYiMcqXNCr4IzmO/A9iefuMxRY27NkqStqDYcXrxQ68TP6weWZGbpf+xO3aE4r+qYgDYQXys"
    "BfknPKtpwjwDlHubwjNzZ5vAsx6a1/0zv0NPzK75WWfgnX6uHqbpcqGKz5DPo7XFaLGfkx26ilvQ4dk8DorpkJx9qw7XNzr0uD94"
    "PyMZ1aH5l+68i2sMWBXE33RDoQgLBpOsodU5fFiQyEylVB7x2d1wwGI8RUSTcdA16MXNWNux9ue4MAL1HfjYvDsqD1Mp7tDyEVVi"
    "WJyweUottk3SGAgBcZ5u9AX1BtpTBXnpx8cqoJj+DZkNNdnF1UYoDogA4ypVnYfyFTtHDKqgahQQp+qUX/Vaz3ub4rXkudhSx4TD"
    "0+BIoJh/U4Gx/mbOOJh0TcGB9FRUcVsyO2GwJHG+Pgc5iTFNjzLNTbQGeWYOgdC8XjGTE4pred1+Zl3Ud76p9PodWHSv6tVSmwrC"
    "65/bFwsemBhBHJRQDI1wi5LgEQ1xGmMvpBWyu76mKcVZMSbaE0pZM8sQz1cawTvu5Rpyv+heZsn9neXjJuR+Jch9sR25X21I7tpw"
    "PKyuJParVcS+2JjYHwKxP0wTuw6FNuUumNgvGAO3OxD7wkrszsNbo0EmrncWYk+ROuTdgtjNXm1A7Oho7PNS/LPxVeB3LMT+s8Ki"
    "VFZNCaVS9dpAzVpZWf9mVWWQujQ11B/RvL5aRU0WB6CwyehCpuIcO9JQo6vLyENJ2Xug1nt4iiIDe5Ftt5D/m25FxqyGt6+7h/f3"
    "0/v7KKPMx2llPjIU9+mSzTA/wnQJtl4KWVQfRgCqrqNwcjbuT4dPaJ10HUbD8bX51SGGAQ9Fn9yzErN4IOMW0b0WXO3ihfKLYIog"
    "AFa+Ovk//x6WTsV5RBD60GPDHKYbwJyjSJ3MMtASabY/sRKhOzvHMCPeZ5esJoWQWd9dZeAQt4oSPOdEQAGa7aojieLD1xgdcGYp"
    "GphlExMxowKNemKfoZc2Ihvs8EHFoRtGJl1kD7+pc77aHoF20C0xgZ6TFeLEL/su/Gdc3RLdMpl14PSK+dw6A97L8TA3/NOVsIgk"
    "V/+sgs9q7p/BeMMqy4BEniuxAHYkjcifdDfADoQxzjYk3aWldQcvaK0Q4J1oyTvbnwkpRjlFd7KklRDF7Z9UWbGXc6S/ZUqF6VJq"
    "K95Enfy8FncEYPIh0s6b8pep2spMvoUUfAk5inW7IX0X5JvqwUFy26N6qg7w9/SvnRS/fuAZ3IBuD3bjXHwr9cg+99m8b/CmIkxS"
    "vEJW8tRmjV1bMgwb/TW50MgxXmFaEZPFnSXHpjQ9dey4g+4sq6eOusQitaGC5Zu+apSrt2STOfl6jsiJdLkr1ykj6r571bXutcuV"
    "6GX3ClW+EDJfHRXxp3J/jz/Dh979PR0kP++O3eLk/r4PY1vhD5rcQSFXHINIBjXXsepI55Doc2bfEUqWAFqjCWcg4Rj0LJWM9Uo6"
    "xcE34cHB4GuQwQPqphCFmcOF+eCGKcOAHdrkAMFFN3PWEPd8x6NFMFQb12Xr7j6sRLBf/Z6st+OTolgSrziE3PtvBqSjhA9jaUAo"
    "DkCR/bp7IZckw2+6YW9Y8jpzfJh3xvJOFoyS0oND52H8UL4mlbkLR31d5Hb+HagONEbb4+0daR1JgdSuqjul3vGGbZluFml7jJIk"
    "IbEqJ20goMWiu0qVEJYKgUJN5DzMmJVg2SAzTJ2OJRl0ELlpPC1FdFxO3NS0ZKb7KJVerNc51cuYwHTMV60UOiRQa5DMBrXcxC7F"
    "et2w9oqpeYU5hsfSOECqvzxMSuAQhnhcbDae2oMSrmOk8QomiUsISZBTUrzccCWPspy/SPQTNyh1QxKfwLylxUA7NmIu7fvqMk3w"
    "MFS3YsbdoOQdjWH1cUQEqtU0VjtDqWrupt0xVEFLs+W4VFqiVVaYAJ0NV+ZTWJlP5eqbNjwAkqPx19GuYDx8uEzMkJsCod0DBbRX"
    "kh0lc9Wwcvh51yC9tYELv3/Ni8nyTRIVriWMrthP1Sp+4EmTgzwJkiwOrJq4/KxZZ5KPmRWGVNyNEzxSYU8+ZnYbFTAZXcTKh/KM"
    "Qys0G3l6ORsjmZnpCs1GbL0cxeo+Q9+ykgSN50Ef430qDYp8RvQqnb6bORjRpzgWcc7hB5QLMKzG5wzTSmYlQcBhlodFTBNHbtzw"
    "SI/YLC6SpeIuB668DMusNw6GIsT60nGL024xtMR0JohUxNYpX1QMc6smG4IJZ8d2dp+OT4sbIg/UsletKOGT5RplLz0UATBjZ+ka"
    "2yXWScFrYVoU02VrOtIkV9nqqsrX8ktPPqjLFyrPN/JLTz50AklwttFTBHcU3993fV8y3XzqG2d3cAJUjvuSsQM5jAFBuFU/llvM"
    "0UDkBYUZmsT8qHberdgnGm+6n1JxK3I7JcORlJa06W7awB2wMktYGW0kF+frFxhHqzpKwA+7Yw2BdPvVUCeNzRqNxop9lqpS5o8A"
    "uZMuqMeClEB3ONctSFI3gyJ8+aSYOQPv9EACX9EpTHGwdEJnSI+umLmOGd2X3XjTyi70yi65sgtRmYD8KmGRDu50ae8PL5LnTYli"
    "7s6TRQna5mZOxBY6wqa4d2yxF29qgJ+DmJ+jAV6vaNs6YCU3xx2rol4Jm5sFhHxebWO5j91WZv+8LjIpvYMZKxQRhMFdaO+Oe9ud"
    "lYbuWTcjchfO0dnBwS3Z+OcPu17nwZnUBAw15h0u0iBDyfv7LZr7VwrKLcezz/zy4EAf0hxmsoJf3KzgFw833n+/cW8EZNDbYWm2"
    "VY+23/gGXlsM11xyDLuhcckx3OGq7zh71dfV+Xj25Gegm7d3XdelttZ7ERkCehgYy1gsJFnYNkl8yGzspHL6MF5dSiyNHqYSO1qr"
    "+TWrhZVyB+KmdxUzB+0166WlXlrf6AtmiS48qZt75HsXWy63ISFXKiltG9gu7moB5WKMISeXE+xhLLMJIS604wmmB8ZOjNRKk+VE"
    "vmA01xlpt2a46WQcV5JnNYWOKZwUaLA+Hs0tF+fd6MgE2VPGXq5+xeFjTQyLY2vy6LEAgjwk5Cmjoggqt3G3GFmUW4RY6bYx67YR"
    "coBp3lmaENNW8o8w7/DzRgOVHYUnc1z3JWdIMwsqOjF/cKBy4KH5JIFvqQv/lnlbJ8IXwjddqdPS3fjNCn3dlcqyEfhwLo4lvwhn"
    "cRAFZhDEZE0s3Vld4WHcoXHwL9bWtJbD4UX2UwBv88lGhd5MkiIj89jvilJ0QJgKvg9uNwFQHGCURdYDR2eIMTvgb6iOBn8qvFnO"
    "am+Cucw56w1xZztevQn2Mmei1+MvdQpbYDC1tM0g74FOu9Y1vJ7BkKfmioyE0beitWneJNEN3ysjc76+wX+fNzgnP+p+ZkWi7h03"
    "k8eREU3Ju/Ssc5f4O764cR+hxvtm0hmJRzq8O7txkRPNOj/cQtlvMRyojPLpPjfeXtBbEhtUJfyUl/AhL+FxTkLi3fFtKq4oWzEf"
    "FbWwsLhwhg8EfeLcS0QenU36EQUezQYbXeLh2SSYq+PepWOFghg6+QCLcxjz84600IQYgFScb5DxSfeRzr7HIKX4cDyO4ul41LmL"
    "xlJAkhdS+BZ0aPUifR4zUNfFE4ZL80uN9t5y4vrz1BH+Ly4wem3i49ORPjZ56vTL5lwS8VFpXgC3xwCp8GN87d/Q1/6N/hWk4p4W"
    "hZXaI/8yQWbLns51Zw5IgZ6M655w4Cd+fa0BXJUr1UCJVcN3aqBHhBcgjpTjUgTSdGWqZzFSEx+l2BI/uhQJIuA5J6dxEkPWFZMU"
    "PoknFTwWA8Oq2xkusTNilSpgrGCJnERXe400Oo2Ep1aS2wEc/ERlSl/EMDOjW3tbVtq3FceBMJ2e6HQMmriTEvgKn1lVVZ/p1WUd"
    "6/9n703X2zaShtH/cxWSxuMBoiZNSvIGhebrKE7iibexnGWiVyNAJCQhpgAGhLZIfJ5zEedezv9zKedKTi29Ag1S8jgz7/c9XyYT"
    "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"
    "jSNDaFGwoNNkMnErwDI7FSbHdoUJxneI5/tzgcxd7CI4KvskUjhZOhUL4MkS188ayEDVX1xD2Rj1ecdao/tVMkt3tCaPNXyz6OxS"
    "0OpF8lKGlIGHWZ6UV5H00kVXpiA6nkJqlUbXZFOq8pSl3mp/LtDUnp1jcRlqSxfozcVRMpktKNGfmwen7b3oZ6ILBqIuCLjIm7PT"
    "w7TUJdiJh3x0J4uwZxhfETKpkqX2ZLG3h7+mo2rfV3yXDUKoOBerlXKfrS3qXpdcUGguVbInH3AZz7P/n7r3WpZdN9ME7+cppI6+"
    "0Ik81SSTJklVa9T0nkmXdBU1LXrvfar07sO17TFbFRUzczNr77WSCYIAAfzm+0ngQ/IDCpW//0I/PrFZ/PzfPz+u+Lo726fEf/zj"
    "H9/Xl/9v+0PX/9v/ij6qB4q0GdJp/sO//OEzF+B/+7qa+3/bf/nCDmidbdQ3H1r0pYi/fdvP4POpjzll04cUf+jNp5S//fVHlN5f"
    "yAb/8aNJI+lvyvx1dZ/YiuZLBuNPtfzlc54r/Y9fjz/s1NJ/FPHXr/fw528V/vypzf/41gXblyX2X2v/0/KX0/7g6CuvG/nr56H9"
    "H9dYXNHGx/6P6bScny74qkc/p93app8ZR/4I/vyZSWn99v2D+/TL8Qe77b8t//6X65Lv1Z/2d2sbfdzKV6LFn753/p+Wn37Rm8uf"
    "l9vf/va9hE9XfaYa/NS0P/7lb/2nu/7bf/zHH9OvpIbpZ9bCT3SJv+zb//m39erTP13W/d++dN7S61PZlh+P9P/9p2+8wl8pC6/I"
    "9jKGn2r81881Tr+o8Wtt078uxdTvf7Cvqthp+tiM6H/9r18U/Id2nZc/fH1194fhW/pnRpO/faWp/kTg+4168rNifFHzn341iof9"
    "C/mx7U97T+yfP+jPH5b9p1/k//j299/do/glxAqX5eO97R+W/g/z8GGqPp5+/8snyf54WfnVJ/6P/0Ps/vAJ0H7kjK4TX3L8/Cl/"
    "+MHc8ofPPTN/bnERXm0M//Bvv9GVf//TT39o06Xok4+mf7tJ+vvIfqa1/CrE3/vka4ezn7N+oab8+z+uUfzcW1+G66cv+wzgP/8L"
    "9J0z/6NzP0v4b/Xqs0j8MuXTcuWffv50jRoOl3B9OrTS5W9f+JayqW+vmv78KZ38+nr1ygj8X3/6659f5X+IP3XLdYT/B4T9B3z/"
    "6Tq8jG47XLHV5xL+O/A/lnT+IE7965f2fJ1g971PPg3q338sxenv+vWPX/d0+rdL/r6m/u1L8te++9Xdf6/J/lrTr5l40p9+2ee/"
    "yP/llv/+IbOfa13+z2/bJ3/QAf3l+2bK2SVtn4cK/Hn6yxeKn5/+tfufy792t9tP0791/34pZPeNjmv6xJrJfPPxv/fvuf27d4gf"
    "BMsfr3O/Uix/Xpt+fUafZ/J/Zm3+86+8/t/+/SrmQyD+/Pffoq0/f5ut/3VQfv547/0DP5T8718jiS+bjf0i6bp2/6De/fPff53z"
    "d3zCvynqL19oij7fuvjLU5/2RW+/rG/53c5ZP8z/hbf6v5z9s4peIOHTJLAfMVJ/fRf7oQGfeEQ+s9Z9EIv8+evRTx+bsn56lH9c"
    "vfz1+dMX7v7PCPkH3febjvgnbFb/+MfnOZWfRvyfcWV/o4P7voPbH39Fr/bLnR5+gMN/lPp1is+veNR+/kLz+hlm/vVH7fic+B1Q"
    "/rIbvnB4fseS/0neb5RYvy69++fEyX/8tDnPl63MP3ZV6f76b99oii930v3082dq008Z/v2nP//y27/+qLavlF+/ldk/Qr9iPP+h"
    "2v38oyt/+kqV/l8bgl/QrE8/p1+oD3+T+EPu9fRDdb7OsPmdCn7J/MV4pN/pA34nXj93//rLKz6bmavOy/T96Ys0fSx/+kQ89NMX"
    "YoFv2+4tnz1V96mGHyjg75T084aD5Weyjz/9NunX9uYvP+zeX3GTf5pLr31Y13/CefdfHIXv5Xxh4rta/PH1Y5eLz6r+Y77M/xd6"
    "9ivSxt+qwFdyxC9KmH7lzPuuR/3XjYk+6exH9yf/nPbtgsv/hKjwh5bsn7EX/j8jJvw1Sdw3zrZPc2j+3NrX+ed3jrCvjx6+M2z9"
    "RuV+R7z1C66x+htl2NeleF9mZ30v9J8xu32jS/shyduvyNJ+tRjvKwPav/9M/ororPrlt++hm/rPqMG+Unl9Igb7PL3on9Fy/Z59"
    "69sU56/Tm7+ycn2bAvftgU74/YHOj/r3Y079b2TxO8nJ76bT/4Lm5JdL+D8tkf68Ivo79danaYflLyh2vvLqfF4E+30W068WI32+"
    "4NfcOt+XmP+CTefrpNUvW7N9aHL4Xau/ifn35v+CcOc/pcb6EcnWD7iw/uskOP+UJuv/X1RRX9DKf8oU9TnPF5q3T8c/nsj5W+n9"
    "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"
    "hNzvr07H96vtYSTCXTX+W25Ofw3qPRrGPQI95VmQL+tbnNgPzH4ejeY+hnn3pw870e9Aefe33kG8h35+j53J3RT8F8Ad/OZm86n6"
    "R9DukSb/Ylz3YJ56vKkv323KT09+TXH5x8/zl74/vG8+/Z+4b362zf/2F0G//iI3e/93V2dd/e6i+V7zx2NXv7pjfn+WP33ff9FB"
    "/moQ7y6iLePdRfRg/OLp8kfu0t7M6LWVBmt8nbH7IWnostl+/u7Lu0BJu9tu8pigcamArH6CoXud5VuQj/t/UD8eQ8/2mi/5R4xP"
    "X26q2ipZtoh/mK1fhD+hl9Nt7yNXP6HfxU+74KsufoKIL+98VJdxc2+3tfvA3+1p/8JbuAeD3sct7vB1JvbXe9xra9/fuIXdX3kY"
    "5BvWvpcnvwC07pF13mufy/iH50A51bMC5Q+Gy/nTR0N8Yzf5QJtvcujLpV4Y//B99G093+OQ36tP/hAnPIadvYWifYz29hyI9iPe"
    "kMUfHkMrf5TD9ZesSe9vPXbz3MorPd9CgKe7vNexW/PIb+5x+j/KM/t2A6UeFrosvmR4+xUD6F8c8P3a9DmZwIth8q39GxJ8Zdzq"
    "/pqx8faPJpX9Sjn5/gh8gIdn453xYHzLEO63yfsIfsuTf9zKf/4Kmb8zennb3ZNh/VLh2aL+YVnx8lNAGO2VL2j1Y5M8OIHyH/lJ"
    "vnIqFo0P3Y2/uzVxz2D7zsz7bsb2+OjnT/Lbt6ubV+PPn4yl9OG4bv3gFhUo/zCu1b0/P3gIhHnDP/PzWH/H20/auJ8/0c8unL+n"
    "80fs5bzx6qSq6qtoMB85y/1Fqr9fUPLNa+bnz5fh5vB5eHCIekgb8OkeiuT2yj0/wL//ezjcMpvcvd2eAsi4Py3juLd6H8otFcdj"
    "Xryb993js6dZLk/du92w9lBg+cHfvjwS8PO99ksqPfeXUxYUTyZZ6V/vLkK3qJef/Latm8//fJOF/SHm/f3JbZ35792UHrt/8SJZ"
    "luijH9+TF8np7gD07N33qLj/50OU2nfFt/j5Pz9WfzvR5x6/9oi5dfmVR8ytEe+Rlv8B/dd/6cyTA9LNYK244/nHd58LlvPr1v/f"
    "b46Jy+tPn+Kl7/feNffJvvOueXr71ZK5xex/1cjTV3jXznPA6Yemwunpg7xlwsdqPwbtzXnq1tuDd2v6ww9/eZeGo7ynSH67CNyv"
    "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"
    "PEax90EPr9HV76Ob057mjy9zhHYNntyPX8JrrPQTGp6j+y0aEej3iXl6ddXE59E78AF4NdVZtIFfQr5boHvRLLTcOQKcAc3/XcsT"
    "by7S/DQvfPFG1vQ8oH0joUN+lVDc6lo/RsJXbM8U6O2M5btqXJF8n8pNxz/cJzTnPx9ujPmcRcMfUf6hrgL704eXID5+QIB/fPpw"
    "q3SUVjX78scsJ4zK30jwwF/O8RqyP2Rk0JxNfP17tZhrgfWNjPydHOBNTj1G5D9h04/J5ONyAh+wR5qfVXce1+whv37KX69ce750"
    "PxSTryz/+r+7oPD7C3on7VaEe5u2We5/Qt4Lyq5V5GfK9qhf395YrVf7DC/LWfjzUt+Tmj5LBB9G3ml52eHzsw6f5pX5+Aao75bs"
    "0/O2x5ffnLaqZz7MNu+zlc4Joef+UHl8LKVexfRaV73XIO8UfPz209lcGX5PQu+5/uyOmtk3/K2a4zsAm9Cz3L+a6q8m/DZ9vvmg"
    "L+BbyvK9UlU3kZOMX5uifF6An4GWVRFUcxRqW9Xnzkpb79tLpUZezaopgiD17ux99TjLmeckc/gR1X884/wTwz/+rAr+3lSvO0jz"
    "VL+kVt1cJTmdJ+5++77bMSPOHi3xL0Bcx83ubObEnLve7NuXLHLd1PuxxB5+atyPz2rr7zZ7c7R4W7w7vPnxCVgTPkJ4Uxyua3hz"
    "YLfK26fXw7y76/rFsG9xOy+tP34v4N1qbi/IuC2AlRbBA9Ou1bEfqvEPxu/lUs9oo5np87+frz++PUo6APzjdce3dP8NF/KW9fyv"
    "zJvp+/BHWXm+V9WfK89tHc/9nBU3yb0/fvz2d7bFHjYGbC+05hS5uhV6nra9vt4U7a4XLzfEvlr5LIzXhs9uW91+zAoKZvWbXeaZ"
    "3fvMzG9n1oPPdta+z2qm7zqZm+DXXyynibrnk/nf22kJ57VKr+v1r7sTiGYJuVdXr3P+vhK3XZOnHr/0YP96iqx/UTL9+u94mScC"
    "Z+oc76fS8xQ2Xcl5dHB+82/63jsoqyxnU/hkVYG3bejXF0HkVaNuISgwRy2fgA+z0fwAIs9eIq9K9HcsPxbp7+9/VmEHXu4U3ALR"
    "B71EoevexPfo5WW/HwvuD7gi9z1U4DVmew3/XTizgCbffiPovdtqGHjaUrn9fr1kP0k6v6cXPxGRJ9l4Rt6Hq2equ+BTlAUfv90J"
    "gZ4Rcvv9hmI8gMit7Af3/Xk2D2/Hqc8OQryOI1ePNeoHwNcSRFv/3p7K88Tjp7XymyYBH66m7wVyFHi5+/L23tULyv563ECaf396"
    "KTsvHq3bVnf9ZGVewJptV/1gma+P90ncVP1J6d9hAfR9P+fzo8pc96lesebNWX0e7mX+V5Q8xn5lEd2wPIoi9IYofpe3N1b5mSt5"
    "ktVnqufPUcvHT/fY/fXrr29mtF+AV2nVTXzeYQz2QuNB6HXCgv4kYXlixkOa/1ZF4XXX/76eH3iIgj33P5uqfcNR/IbuvoB7c5/f"
    "niT7Gkr/PFl8FnI9cONH4mH8FSOJF8xC56c34vdn0txcA6rr2Y07VfiTobj+/KGKAL+do82Cdk3FqJsE/JCgPaf7ec9XpKPAP76+"
    "q1VvrcmHH/n7b1f2Xmn3b5up527jLe29maYX/uS/vnvJD0+IP/xx4///+58r7Lol+e21o3y5y/yWYX29p/zcID0IxEMm8cYG9jwQ"
    "+HDfN7ypJ/rmXD5jP0xyDsJvr//1GxbzGbuQ65D7mHkN8lu96pdO9VdlhefwkZfC+z9RN3q90/++tfpwCyoetfD6An8zqLhP/V74"
    "u68C+hiNvCq73c/9PCwD/AT84f11FeDyR6h/PZyQ+XHNkPe89cPo517u2ZwfzfHvSfqfD0V4P6qyz9f89NuPOvT2ccQfIxwvK5vx"
    "28tzHA9cf8wOf6atbx9JwV4dSXnD5D4Tqpt+vEPZfRGf3PjjXjyCOOG7Y34jmvweSiLPQknkDf/9OxXC3wolb6T99bsJ0FUxn08p"
    "um6Yfivs+FpA8qN5je7G7vGMEfJsHveHN0LRG6h7quMU2RyJNA+m/jmOO0AUe4KHfrdDt34f3jsj9l3W7+DqMsofqwbfM8vvruk6"
    "4nn9/Q2f9TC1Z5Tco5nHHPrLn0T94aoos5mPZmXI5xW4mf6mrfJ3Z/y84nI/sPQbZ6pe6cJ93I+q8PYpnasCP57MAT5dT798eIoq"
    "f7EmN1F+O+t5OP5SVNnvnakCP76f/SH4M8P6wpC8GvP2DB8mB16P/XyCrhP8Pl14fnrr1M6d7Idy7S1hfGWhfzHmry+z9Xss6r19"
    "VPGx/8N25bvVrq//8+fRXqH+66cF4VdHbq+PpVXX/awQHx/8F/baf708lfQS6e1g5N87C/W4Af+yGvkyhHmB5KFgcj0W6Ln//PZT"
    "sbjL/E+Gf/j95bpp3utQ7zrye6CHQE+B3qNy/F3yfoeGN1j+2rL86/EoZ+69c37w8VTX72z4PV/+v7Mn9TwEu4+5U/Qg0m5U3U+Z"
    "f7nz5Q1pvnW/L5kfpek/n9dyn1sR4Fn3W6n5b4f7N8/1aIeQF7O52qJXb+Df4duHN1/eUub/1e00CHsd577D2Ietnac6xqsTh2+6"
    "2PvI28Hw3z9S/ZTK/Pp09R3B76dt4Me/E7w+ichfz/ZmbgcIfsT+8Y04+4VcPId5C4d/vcF+Y8WTF34u4Wlbh//86zXI77n/2yrx"
    "11skPKrFq0Ojz7r6RdH8npL8jnN+UIZrjfkn2zSvPdnb3qv+fvXkeen52vKq8Pz81MSzgfcthu9bC0+lh2d9Prte7Xz7nSPtzx3e"
    "CnLCH0HNVrj+6z8W//Ht95hwBxAX9qfHH/eU7xenNX4MSq4jfzB13yOL34P2xPkrtCacw4Bvr8uac6jgP0jHU9fIfVaeeCp2/pLg"
    "h9LG492Xe/UCKZ8RcStX//Re1d8wOy8N2Os7Lm/bnysRD3c7/o1T3U8w7hfI3ocBD+lbd8Su50eeluBnM/iTQF9j+2sGlL8u9gNv"
    "2sc/AfzxMtr9zswPd9MeLf5NRK3fusvwbPv9edHxXT7PYO8kvxz+eDnypzfMvj6PBZ4VtG8C+OFP5DFDeysffcB9N6PXLbOZX7Pw"
    "zjHaP+/0PCQ+0D+eJX03RZp12vsAXqE/UeRZ9ex2HxPBl8Je/6jXr67J/NIoXkE9usNfZgdvDn8ry3vX8EAffznu5zqaub+G8Cvl"
    "uOnGC20FX8G8njn754124K2Wv15N8t897fZuEPcW0lsY8XLKH38y56fyxt8Bc2P+S2N3u/X8zp2zx8u+95Od1zs1X6CvLx4ee1yj"
    "zqKKrtnG43mT7+L0rM9bFH94aShecPV5FQV6e8LvyucM7LuWvz30rx9U5De8+itAs56m3g8S87PC25sAPrxh1t6C8fIQ869gPUjN"
    "O97mvxJv9KtZIuoP383TN+Af354OZd1+XbPPPz7frkH9qynebIWha+OdmKT79lj4/q0izBwhPeSpL6tNbwQBSXfb/XhseBhWPzZ+"
    "cJufXhC99nC/vSPqz8KPx96PFv4q8P/8/2+KXwH88HxKj0HQW3N+OWqe4//g/d43ffYPKN+pVKVe916F4G3PDr8I824bzw8air0u"
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
