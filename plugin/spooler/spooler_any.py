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


# --- Spool editor: Add Spool and Edit Spool ----------------------------------------------------
# Every value from the page is checked against these tables of Spoolman's own fields before
# anything is sent. An edit sends only the fields the user changed, after reading Spoolman again:
# a field someone changed in Spoolman since the editor read it keeps Spoolman's value.
# kind, then (low, high) for numbers ("pos" excludes 0) or the most characters for text.
SPOOL_FORM = {"initial_weight": ("num", 0, MAX_GRAMS), "remaining_weight": ("num", 0, MAX_GRAMS),
              "location": ("text", LOCATION_MAX), "lot_nr": ("text", 64), "price": ("num", 0, 1e7),
              "comment": ("text", COMMENT_MAX), "archived": ("bool",)}
FILAMENT_FORM = {"name": ("text", 64), "material": ("text", 64), "color_hex": ("hex",), "multi_color_hexes": ("hexes",),
                 "multi_color_direction": ("choice", "coaxial", "longitudinal"), "diameter": ("pos", 0, 10),
                 "density": ("pos", 0, 100), "settings_extruder_temp": ("int", 0, 600), "settings_bed_temp": ("int", 0, 300),
                 "weight": ("num", 0, MAX_GRAMS), "spool_weight": ("num", 0, MAX_GRAMS), "vendor": ("text", 64)}
EDITOR_OWN = {"tag", ORCA_SETTINGS_FIELD, DRIED_FIELD, *CALIBRATION_FIELDS}  # Spooler's own fields: never from the editor
EDITOR_INVALID = "The value for {field} isn't valid; nothing was written."
_BAD = object()


def _form_value(spec: tuple, value: object) -> object:
    """One form value checked against its spec: the value to send (None clears), or _BAD."""
    kind = spec[0]
    if kind == "bool":
        return value if isinstance(value, bool) else _BAD
    if value is None or (isinstance(value, str) and not value.strip()):
        return _BAD if kind == "pos" else None  # density and diameter can't be cleared
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
    low_ok = number > spec[1] if kind == "pos" else number >= spec[1]
    if not (math.isfinite(number) and low_ok and number <= spec[2]) or (kind == "int" and number != int(number)):
        return _BAD
    return int(number) if kind == "int" else round(number, 4)


def _extra_value(field: dict, value: object) -> object:
    """A typed extra-field value as the JSON text Spoolman keeps (None removes it), or _BAD."""
    kind, choices = field.get("field_type"), field.get("choices") or []
    if value is None or value == "" or value == []:
        return None
    number = lambda x, whole: (not isinstance(x, bool) and isinstance(x, (int, float)) and math.isfinite(x)  # noqa: E731
                                and (not whole or x == int(x)))
    if kind == "boolean":
        ok = isinstance(value, bool)
    elif kind in ("integer", "float"):
        ok = number(value, kind == "integer")
    elif kind in ("integer_range", "float_range"):
        ok = (isinstance(value, list) and len(value) == 2
              and all(x is None or number(x, kind == "integer_range") for x in value) and value != [None, None])
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


def _for_spoolman(clean: dict) -> dict:
    """A checked filament form as Spoolman's fields: the vendor by id, one colour or several."""
    body = dict(clean)
    if "vendor" in body:
        body["vendor_id"] = _vendor_id(body.pop("vendor"))
    if body.get("multi_color_hexes"):
        body["color_hex"] = None
    elif "color_hex" in body or "multi_color_hexes" in body:
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


def editor_data(sid: int | None) -> dict:
    """What the editor needs: Spoolman's extra-field definitions, its filaments and vendors, and the
    spool being edited as Spoolman has it now."""
    filaments = [f for f in spoolman_call("GET", "filament") or [] if isinstance(f, dict)]
    vendors = sorted({str(v.get("name")) for v in spoolman_call("GET", "vendor") or [] if isinstance(v, dict) and v.get("name")},
                     key=str.casefold)
    spool = spoolman_call("GET", f"spool/{sid}") if sid else None
    return {"fields": _editor_fields(), "filaments": filaments, "vendors": vendors, "spool": spool}


def _merge_edit(changes: dict, was: dict, now: dict, merge_extra: bool) -> tuple[dict, list]:
    """The PATCH body for one entity: only changed fields whose Spoolman value is still the one the
    editor read; the rest are returned as kept. Older Spoolman replaces the whole extra map, so
    there it goes back whole, as just read, with the changes on top."""
    patch, kept = {}, []
    for key, value in changes.items():
        if key == "extra":
            continue
        old = was.get(key)
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
    if extra and merge_extra:
        patch["extra"] = extra
    elif extra:
        if not all(isinstance(k, str) and isinstance(v, str) for k, v in now_extra.items()):
            raise RuntimeError(tr(DRIED_NO_EXTRA))
        whole = {**now_extra, **extra}
        patch["extra"] = {k: v for k, v in whole.items() if v is not None}
    return patch, kept


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
    merge_extra = spoolman_at_least(SPOOLMAN_EXTRA_MERGE, fresh=True)
    now = spoolman_call("GET", f"spool/{sid}")
    now = now if isinstance(now, dict) else {}
    filament = now.get("filament") if isinstance(now.get("filament"), dict) else {}
    s_patch, kept = _merge_edit(spool_changes, was_spool, now, merge_extra)
    f_patch, f_kept = _merge_edit(fil_changes, was_fil, filament, merge_extra)
    kept += f_kept
    fid = _pos_int(filament.get("id"))
    if f_patch and fid is None:
        return no(tr(EDITOR_INVALID, field="filament"))
    if f_patch:
        spoolman_call("PATCH", f"filament/{fid}", _for_spoolman(f_patch))
    if s_patch:
        spoolman_call("PATCH", f"spool/{sid}", s_patch)
    notes = []
    if f_patch:
        notes.append(tr("Saved spool #{id} and its filament.", id=sid))
    elif s_patch:
        notes.append(tr("Saved spool #{id}.", id=sid))
    elif not kept:
        notes.append(tr("Spool #{id} had no changes to save.", id=sid))
    if kept:
        notes.append(tr("Kept Spoolman's newer value for {fields}: it changed there while you were editing.",
                        fields=", ".join(kept)))
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
        return no(tr("Created filament #{filament}, but Spoolman refused the spool: {error}",
                     filament=made, error=_spoolman_error(exc)))
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
        if action not in ("locations", "editor"):
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
    "The value for {field} isn't valid; nothing was written.": (
        "O valor de {field} não é válido; nada foi gravado.",
        "El valor de {field} no es válido; no se guardó nada.",
        "Der Wert für {field} ist ungültig; es wurde nichts geschrieben.",
        "{field} 的值无效；未写入任何内容。",
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
UI_PAGE_SHA256 = "712d2d4a6cfd430f592746c852e37ec223fae4dbe3a6599b87285b697d7bfa2b"
UI_PAGE_BYTES = 1323354
UI_PAGE_Z64 = (
    "eNq0vVt320ayBvq+f4WZ48UNjFuM5GSyvUHDWI7tJE5iO7Fs56LRJiGyKcEmAQYAZSkk//upr6pvIOlM5qx1HiQCjb53dXVVdV0e"
    "9qbVpL1d6jtX7WL+6L8e4ufOPC8v0890+RkSdD6ln4Vu8zuTq7xudJt+tmpnRw8+s8llvtDpZ9eF/ris6vazO5OqbHVJ2T4W0/Yq"
    "nerrYqKP+EXdKcqiLfL5UTPJ5zo9QSVt0c71o9NlVc11/fBzef2vh82kLpbtHfQu/SxfLufFJG+Lqvz8fVOVn90ppulnjZQ5uqiq"
    "9rNHo9HXr169GY0efi5FH/3XnTvdWhbVdDXXnz2arcoJqrqjIx2v55q+p68u3utJO5jUOm91VK7m83g4q+oIX8s71eyOHjTUhzYa"
    "q3Ect2fleXoyrHW7qqma9JGmkd1pt9d5TXWtt6pMz85VnUZx+ojeCn7onag8Rd4BZvJJNdWP2+g4TtP05OSk3+8kn0jycb8fddLv"
    "x49O7t/fbHYSH/7v/8SqksqbNq/b5peivYrGVfl2OaUBJeNYNXaMedMUl6WapJFWLTrIY0z1oCin+ubVLGrjYfnoiLuEMU9oPtRJ"
    "vFVzW8OyrtoKczq4yptXH8uf6mqp6/ZWrWyd8wEt8Jxf1DR9XNf57aBo+FfN0M8bmnoa4vis4irvvMiX52O1PPTpVLf0aXHo01Ma"
    "G327wjf0B+tEn+0Cj9XlzpemrYvycqxGu+m3i4tqPlbXO+nSzrjf7/W0usXH6Jr6sNlc0f+436efQXulS/NIIDq5itXF/kS11Sk3"
    "rW5QyYWZnlid2mENGp7pB+roJFZaHxqtVErjbfnzJX2mNepRjpf5S+qjPjs+x9sRPY/H95bYrs/LllbhhMFMq5IKEgR/0Leq1jP8"
    "jQjI+RdpVfmuJJD6WlOiflGtytYm8YuednMIbNk0edvNUi7CasyrnhI81jyIv9h+sruikhaEtttmE/Guo69xTMBY6PTzo399/PxS"
    "PUlr2sgA/Vov5zlNYqGVbAWe0pOYZv/tkiD0Sd7oiEqrnAr/6+vo7PHR7+cxVVHpvTpyrcZHd0/GKPxj9dEVVo3Piz3Ie7jbwD3f"
    "cqwmLntG2/HuugHS2Y6TMU0BoUCzX3pmAopG9syKvwwGA96gDhGlx8PyoR7MdXnZXg3Le/diTXMScb6tmkp1qiTM0ztBQVPrVM+K"
    "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"
    "SUrjgP+6p+l4WS5zwFjP6EfUC98B3wQKzvvMTgzkho/vZRA8icQUTsOvUsk1yzzww/TBIqpwUsLgxR3xUGY0eEn57gOF+wLGrkpQ"
    "+ElAEpgHS8MdC3FSfPcsJX8aU36lv0WAikh5ZB2ej06w29Ceqix87zB5gVkkSUYSjYcjhlNo39CjI+PKM5/3by6vPzhax2tWCV4j"
    "K+AtWu9QJJCUIf7PPdaJ0L2DekIXjKGBi2K1QgXUipYt7jGy0rKdgPuM3l0s8lFG0+aac5q6zc0KRBTPS/VQksVMIVbwojORHcMf"
    "Ayu26bmmTUYQ46yOCsXneKHXaLyP0XVpS1cyoqGrw2FzUVcMoITPCDodK2277XAx3PwSJJaHXd5XtX+NpKB+k9/8ipNb4UPaOQfl"
    "sO1Xrq53l/f20Zz67//wi9/9y9/+7p+++7e/+xstk3g337/zFvPU9zEOkH4XKaykryxi6Aj669olJ6ydZ3/JIn6Lili889C1weMe"
    "SdWOTWMG9urdXBmgzQBrcrQDRf+aI6TgH3ZJFLscloVJA/FJmFsQn3h9Ed9W+G9H7k46fAUzsbWr16h9EpHMKlrIhwAWSul6T6tk"
    "fp8swjVdrLcOOC0geTBlHvUkn7AhBZP+iFLSl33Kh1lnEL184Q99IasigtIf2XOQRSEsvP/HMrjOPtbiytB3NHsZxs9I5jLUvBMK"
    "pY7pg0CQQg3RLfOCMgRqklqT8k/GOjjgsJsTR6BCB92xDOmu9uiTSK3av3betUZcoLBxjufiwFBU9nYVovG5TCwgE0swzoC+rRwL"
    "St+UX7VVgcqMTUmazA2IG5tt/7mJsc438BCWMA0wnhwasIoVaF8/JYQIljvXapAeZW5JZHwhVVdHWxdDZjZ2qsUrhyPWxZpyLczD"
    "rxROMRtO5g9zr/llXQvHBTv9E8pMFlvL6tScTf+OjznD1hfN9WpYVqu7c5k+l9VFVoVE4jpt6ViX7Pq3dOqXPvvXX/yatIz4r9Mz"
    "oleqe9PlRcZUAL03phFrU2y1xmtatZkf5c5TS1yR98Q/lraMhrywY2C7I/MMVbZ0brdk0hNF00xUhQSWGPqtujdX3hy5pzGYftM6"
    "WEpHLx7DLOb37DJ0PnSkzaN1ZLC25tmzsmUXCrfP9ejlCUk5WMz/6sPsL6cheek+GIHyPirhbO8mUHlR12wLHS7vV229tQXe73g/"
    "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"
    "w63kQnRxd8kQjewhG9mSG6Rjm2yHXPWGdIdrqR2X3ZrQG7MlJvHfU05UK3tLSrqG3Tu4jbTkdXNbeVGN7S8xmSp27+lWUqO6urvc"
    "qIb2kBxT2Q2yIxAZ5pDfeAJEPwSTaF9WtvGs0RZF1xNYgu8pMpnWNovOn7K724pOprktROhP0eENWw8bEd1nI8FQeG9kP5Y/d9ls"
    "+J9Eh50Zd6ediD8jJbLu/s2o7uy+zxTdE82PZtutXfz/M/q/O7tu7///k1Eg7WrfiOOO3vNkuX2w+1jm3NLD/qfu884Mua37/U/T"
    "67TLeyN2O3qxk+X2we5j+XBLT/efus878+G2bvA/Ta/TrueN2O3oTU6W2we7j+XDLT3Of+o+78yH27qj/zS9zrqAN+K3s083XXI/"
    "HD+WH7f2+/4P6PvOfLm9U/hP1XuTC3Yjlnt4VLNl98X0Y7l0B6/r/xga7Mytu7hk/3RUmIy8YDcTk0rs5fSignsh+NEeTmr6I/2b"
    "f4J+7+7qpLY/1tH5OXuO6Xf397sbQbIYYSNbOl0RdE92S7SyPbN9mT5syzqJZnZgnM/Ti+1P3X9iZtnWyZmD5Mdw0D7u7q/YtZ0Y"
    "ay8P9hfo3Npz6J+atbZyShoR/Ci22tkd/ZU6tRtD7e5j/tzdWnNO+xNz0hY+xSxqH8NDO3qNv3hfdmKdXb3Bn7U3aw43f2Km2cIB"
    "mEXtY5hmRxfvF+/LTkyzq+v2s/ZmzYngT8w0W3jrsqh9DNPs6I/94n3ZiWl29bN+1t6sPUb7idlmK0eaCb2PYZ2dXadfpUc7MdDu"
    "DtHP3KcNp00/MRtt6d0yo/gxrLSHf/Or9WsnhtrHZ/nZe5bxRX5GX9CWnqlP44fUmvxMbqFP053dfES7uhY/dYdGybQFn4dbsJEt"
    "8NiFMT4xctucOs9HMT+SD45DaegPxlOROAFjZEzRsbtDI2s56hMTwnwo3Y0TJgSLrRImBIu/UMIE6nMchd1bZMLIj79gGPmxFkZ+"
    "ZgwjHyzWh5GfxWHkqWtfNIw8tPi1w8gPFtn8LiwEMqvLdJHKKZKNF+3HiZA4Cfx4MhMDcOKqkEETEMLrCYaojlwbGMf43/IgG3fr"
    "oMvhtX6E3x8+RJiW6Rk8Hh3dE3HA6BdFBLIPMpHIDrpFLv5yPEN6RGPKOqG/4nCRrnV0JCrUqsG8T0A3xEH81D9SyHPWF1jnAkOj"
    "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"
    "i1H5A2AMXx/1xJW1rtd0bNf1q/PofHh9ded0B/tmLt4vI6bfMTBetOVqa7wIfYsGj329tOLpeNylO3czzeu2fzydJ/n4zgWkj+en"
    "AR916MO9Crs9If/KQLi9z2S/2OY4ndS6biK+w873+vha/NN0dQsYhlH71Dz80WRnLj6tBG6fD0X95Zr69rD9o+fiVNKfqJHq4cYU"
    "j5AEX5/5FC49jZ+deRrMliz3fOn6lNNlyO6A6W4Jbjh1rxM8V/63hp86+tzUerVr+3DdeDgd7bx8PbxFlMui5LKrfWfOX9cT9s8v"
    "No3fcjRccgwSWH388syUf9eGf2Wn36mBJxJc5fpmNj9FnH4+rk2fgi+YlW8M88nBlpcpdVmBfPkjy8/G/0DfEwd/u3AwNsxDN7fy"
    "82F7CrgOyteHxxnruQP6Sujh60bfN52fJ1J9xzH7SIvzN3l59e7a3VOV9TBBDtNh8qNcfppvf5zT76X4MvhXM+RtI+7phe3v23D3"
    "KR+l9inoTWPMfTj4n2722NuZ7nKdlg6DFvnHF/jbeTDvhuBMsu9GPjxT/heZqO369MTCVSCGUfp4etAtiU9ILn+m9O9V01XtPp3N"
    "+VOVO7T0tDJ65zzPsE6aXoyiP7fsT3J4N/bXuf2Pj6l9+CnyT0CiH8+q+J2ns25IBeeUg8n7NJm8KPisd4vbzPmqxMH6OOV8e6v2"
    "4Y/zKcZXU8KtsZd2fnnemLvXsH+Cnlyi7/blTi7al671gdxu/Ony8lH2TCrugDzOjbm4hsozrsc58cmsyoef5x48VJfDy3fvLT24"
    "T2kvhlRyTX06jHB1258sjyZ5tDvePG16PTB8fqvq26Mj/1HTPl8onYIGybiZcu5Vy79w2bzYuzkp79tO6M0v8my4z6M8iOaJ3ZhP"
    "8kXytgOfPnvXa1hCVZ/fuoR40Q7yw1mcz+9cf3v4rb6crnjUHUl8pznuevl1VF+fjXrOFMmvyRn85fbe6jMr4e7cxUCOCw2KE5D7"
    "9Y72sFg7Efwfw+RwfoL+ZhPeZ3vh97jEndv89fHNr/p6wuP+oMf1FG59e3Tute681zjvtFq8+F7+tJnizUdj3I/GU9Snt1r4+aJH"
    "rg6X4ORhnWef3hgI6O2BeN3m1xR5eiKsfnoi7OlEwItzFY+3QG5U+/xno30Z01vtL1yh13MBl9gnn+fLI6jXBDcv6K2ZH++b/NI9"
    "eNfyj/f7lSdlenfY6Bp527085bt9P9ztY74t8a+gyU97khfCnNdNjxufP5D9hC3+IvtlOUdXn76b++ku1W1EhwXB+WmG376esPlO"
    "U+fHF5utwww2cMVpZ/OEUXY6lvREx+e7sHfe3OdHvG489vHFJu095V9IxXlgn71196m+yevVifXYppu6uSoj8KyIbo389Wp9eG8v"
    "PS4lnjduLzbIX2jHXa43PUI3wyd42wt1KeS8TfyXq77L9bYz6mGC3NsTr5XeD0r3/6bee1vlfa9nbyu/F8L9TNcVJ+fyb79Fv/9+"
    "6fagZ6AxNoQ9W7ydTgPl//xn/p//md+f9Xl7qrrvyP151ffmnasOf5H0T63CZ3PROfMjiP77Dva3zyffeduHcf+b/3Sl5vHz6fnD"
    "6o4Cv745RfxfI8Cfd/3dTt+Y/cwUnnFdIYy/nXTFdfI4eXH98tfr6+WXX18fguwdI/FKrb+/sZa65f3j5gHJLuuVE/lOmJDXOW3Q"
    "pxCIgINoXq/2fD1Pgc/PMV3WM6+cLkGe13/V6fI3/xGZ8dNfYILPv763G/t/YO00+4tM8s7IT1+sl/6Prvf05ye2f7TZbxz0Prf8"
    "4ZVz8geAZf+tvknsfd/ki/eELq7JF4E/4Jl8xFz4Nzsmz+LdGPcCf3MFnOfA64m86wbA+evJt3/+efbUP0Vcfr7wKNz2I66S+VAZ"
    "n7/lxs/l+U3fX1LjfNY7Mn65qpI0zk7MdnqT8MsftR0Oi7db2Nfydp6tapy6tN2T18fz3dI/vZQxaBL/NGV/e6ja8MsfhzQZBPtr"
    "VNfFFwDouu7nDv45L0NgDIIgMCT5+tCd8DK/jMGHqxU9fLWx35H5YVA8H8AP49N/v55PLX+5wJF+ezh5u4Ym/fa1sOto0Cjel68S"
    "NP2A/zxGKWj6MwIh4/OPD8OPKTp8ohg6xa+/IJC6fVxS3nIMv0+h08sHB1PjW75zxPhc4DXP9Qd1/nsr/5b+XDV8/sNBU+vW+CsI"
    "O5Un+TBwZ80aN9hhvP/67feBYKHxy+K6E/RVutA6ziK/jM9Pp1Vf/gY9/OMfz4ZnMNTP6CR/JH79x/m4a/3tl1n4KTI+P959fsg+"
    "//I/r4bb7HR97+B/4uyTWj7B9lb3LqrThcJ/GL8kxc+DXA+McWvM2TA9r8wv652v//Fh+Pdz8dMt4sMf55DTv0dc4Q/nV7oGNfX3"
    "x7hhiihOEKwfLjf8fwoS//AUO5jZ5dVI//LhNM5PUYO+qGPXTn46o7t9+eDkdZ2nT/EXFvrg1Z/++61JP5/D/vvnp0RX9nqe6hJ4"
    "S/btP1727KfzgZq7/g1jWA1W34crTO5T8ScBs8sT3PHL1j+R5Aa1/BR3Xmz9dEZA+OmMzfXlA/gy9kqt19HXbkMg+P+97ubz0ML2"
    "Ttu9z7IPS40wzp4F5YXtxnX/LOz400XbfoDu0jX1GaNhEM/nfXXy8uTw/wAVhw9DXweT4bxxWNgnxn+Z7KfS9uJBez8fkkvcz5e4"
    "74zMc7575K3nTLVtqjoO+p9uzrMPrv9i2E4c9dPFw/cq8i83820SvJXPPSmBZ9lsd3dy3GTey4oeI+6Tn/O/SHnyhL8u+N8lHKd/"
    "T7vAXx7Dnjf+eQlP6X/2mvJsXP/3zw/Ps15ofG72v5D58FMV2V7e/eWsVxb+4YpfMf9P1yF4h8FvDXtB00vgdxWON6i6emjT/0Hm"
    "fqveoZSH77RmmKu/Fx3fNfctjjvz5skH9adc92bKYOjiT6fAH0n8NH4/3cbvyw+P8GvSnGEuf37y8nz+crqL/2qS+BKddus/f0dH"
    "3bP6S1E75X1TN7wxVOcP3/vXarpm/ut66DHjX9RH12w/2Kl/H7H/rB9Xkr/Zmx+g3/sj9kPkuGT/E6L8KDHOS4ufrovnf5EDz2W8"
    "zxXv6bNLttPF2heq7ZmZ8F6W6zz0fpEne/M78a/aedPNeRAMptP7FV/i/33s+O8YgRtrvD8Sr9s5fF7PCn/4n/9ardfsP17f9RTB"
    "T5frov+KBF5yviF674/Dv6Xe9zXYX6j4/76CenNUbs25q+DRmId+JN+/0NBb3n9diT6V8Ff16GPOP5tXqvThjbDvdPct66VKf9Bk"
    "HhL+6ZLyRe1vG14vE33fDns39b1Z9n0bKn1lRr1vxqV/xZJ7nvgNeiRvdCgJ/+IIJeEPjtCQ8E9H6EXtb4/Qy0TfH6F3U//wCA0N"
    "/+EReiPt+yP0IvG3/7g6Zs83sfO8fgNd73RD5fK20xmntyjz4nFX4eudX2j4vN3f/vrwx8fX6vW0Y3r9fPh4v5Ga3W1hF09XY+qf"
    "/1vhUtdCzucEfn0d9AiTcEp+Q0z4+FKRnwt7DX/w8PG5XBUXfR6c7sUOv08tO1Hr/FxQaifJ8wzDMD/LkIT3GZLTCw9fv/3+7eFk"
    "3H19zuAnb9+VKZ5FPYaeEpxmlq8v55oh4uT7+/qCZb+e/Hnto0uXtCufevTkXTx81Zfw8HAevS/XXZmzM9CJM7vsv1xxus57psPS"
    "MR1Ca//LH+dTpbe421m9v0HfHk6H7S/wWJc057IeE4DfHgI7qb6TAvr2dOX0/VoeL4p+pyG3HYJLErlJHb98THGB8bheu7smuWDD"
    "vJXkfKbqmuq3a7KFs/Xd+ve3kuuXEyHn5JdkL1I9v7j2veofU34n0berS/YfxmkY29h7A0Tljzv5OONZPPy3i7vi9j7bOfDbt29P"
    "N8x74yTrH//LOVUPRH5S+GX14acPFzTAj7f73L3xyxUfUO9TJ09OUnQt4uvjiwaXqNOhsvLExSe5OYd8/fUtUO8r3OC3t06N+C/K"
    "fF7dGa+oGnjQPdfyyyXNEP632/dJT9X5qYhfb2348ljhw7nP3x5J4Fwv2d9q/1T/cjBOKH3x0JBfL0P78zAWw2rj9AKkX9b9OcNN"
    "jh78rEn9C+bI38CHC5ZS8/j7hH56/T7h2/5W//7LkOWp+oPxpG31U1NuUIufn4j/qf58R836Sz36+vWphHOuC9jguWt/++Vrfm71"
    "13/+82/+DdbQv+AWngET72n7P742A00/Ddr9tyvx6lwp4zQ+ufR///yILHwDLRxWtoMyPNf490uN5V2Nt9rKv9dRmXcfjKGqWVme"
    "niP6r/+6K/hD2lT1h9ve3YfiMfyCafL1BlR9hvB9BJ+8CMZVzD8/G0XKuOMf2ji/PjG7/DEufzrj0136068/XrWRvy6x7Lo+bdx+"
    "qPMPVXFSVSfv909nzj7tVt7mxJ//g88+nA3aU0pniLimeDint0/YLR8ulKkuPY7soY/2h99eyMrvnz5/SP06yr1T1x8baTyN7AXY"
    "8sbETzS5EXxxSXoFp/zj2zCKF2pdh+vz9aUB7OEn6Ak1/0TcC4e/lKsLS9yHnC8sf34455HsYmCu86fu11+viEtBmadDTV/O4cRt"
    "f3VICPz/n379soz/yX/O6uEL+yc0+Sc8/jx8Dko3LYa11aWE/wb8XPvVCTr112t/bifsnmhyHtQ/3uZi/xVd/3Z71em3gf9uoV+v"
    "wTfaPWv9U030rabnWDz+53ua36W/NvmPE89eaq3/5+MDyidAoF+enlMOBm67DBX4UP5yBfn5/Pfsf9R/z0ajz+Vv2e+DQGaPgFzl"
    "GTdz9zjHv57fW+PVJuIJYvm0n3sDWb7cTh/+Opez/Bfc5i/PZv2vvw/FnBjiyx8vra0vj+f1b4PycNr4fmMe8v7x3JK4Pjd2FzTk"
    "7U7gu1/+eJ7yFaLwi6J+uQIVXZrO30edX0ZPrzdcXr2d9Wb6K3L1Dye/iOhgJJxPgb2FSX3bjD1JwBlJ5IJbd4IW+XL7+nx6lvXs"
    "yj8MVL75n67o/RcL+Q3yvSDEO3hW375dDlWeR/w9tOxHQLinN9z+9gxg7f6thzfs8LdCb2d8niGpPVyBXi9m5q9v9eMS+GRQ3pPh"
    "iuL5ZEt+J+0jKNbz0rP3oZP/dn6e5/qY+eldlezX3x6BiqkTUPHDBdz0nOD3z1/uf/39rdpuoF8vefZv0DPM8zfF7uGtnJ9vYOk/"
    "NgR3QOvlg38FP3wR+Cb6un8SndsRm1cieE18VR7+E4DAK/Z6yP5+n+OiZoY6B9X36cpNpwtQZ+ihz1dogceH9+rLTJWda3hDAF8J"
    "6eXJwfgC9/HpZdBzffPLm+R9hk5+Pkwvn7TrO6h3PzgKT+VcsfiGHp9+nt65uIj624iZ/xty9gy28aUI3OARr0Lo31DznuTIuz1N"
    "dJbZE/m994HfBnP5HajCNzXZe/iF/xo04XOYuEfUtvMhmi+hMcQTTyhhN9fDE8bWC5F7Bb11hza2fQQNu13Gux7Peir0PWy3R8C0"
    "N2HensGlPbuOd8NA+/1BegZ1Jt//elq6Ke+Bg93AvM7QYJfzRe8Bc73G33o843w733zD5Xo8A/fo0LGfHDpv0fd0qP4FLz7BnLw6"
    "T38HdHJ/if98SfpyJ/oJfOt87jC+A9m5IetcrsE+nWJ6dhvpkuE5us7TJfM7PJ3bqdXr42wnSbafpPqRzZ+6fwe5811wrLdgtt5A"
    "w/pxGJx3gbL+3wKLulor38WKuqS5Ar2dv98+yfmSe6+j/nTXYGu8e0nxxDNvCMA5+JH/X7Llm3cInlx5n99q0mPk26Xen6W+YW+8"
    "YrrnJuIrUXtxYTu+3ri4KPZbXW+cV3+s4NeXSCTPLxfE14sfrzr3HDTmvl/fw9l43YFb/dXbZ/v/3fXfHck9H5uVjctf6fqXMD5/"
    "2z0eo1Uux2gZ45dzGV/i1A59oPOd4u+OXfkT5GG5S1itsViCIDfaUlBXCYGsiZwY/qmn/1O62fl/6vKg6gvJGYI0MgNyAKo3SAsE"
    "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"
    "VZ2mtcmVinOrYaR7mJNesZ36Lr2ykI7TdYhteVDB9/tVKm1rhG2gtgosOd6yzLpKuK6qsOy+TG1Tg8y4JgwyM2StudICG3VsY9ar"
    "qi0OWW5yk6zR5polNOU4yEow1iNFsZF22bEMUisv63JrV5I1Hm/JJrIHNnOCrqkyurFavNtUDNEmMtyIaJKr/n5OVEm8NZspu1U2"
    "tTe6pYHIO1LfBX4zmDul0l1yUyGcEkPtsHSbwROykUbtZgFZNJZGnmRHc7WQUdMjo5eja2W1J05odTXIcOZOy5DdZbeQaBbrDadd"
    "EMv0kpY6DL01F/Ruy9JM1ykMDYnQElJrqStUg+qhRGWRKHTJZr6a7q8Rgqsbo7rD5ZB5lRkSrVzLWnVoi3YwkzN6mNVbTIaqzUvI"
    "UOjY7U2zIck7vmhnUm3aFPOuwjaWvYmq2Fa6ksUKbMdODVcTkhZHq4VtkTbqpCbA/2Wq6Y6iF7GlVmVaHMtV6K5kFpZulUjTTlpu"
    "sK2GuaY3edlgnSXKLPbpiZtTSae1W4x2ddzY1p1eMZ8p5/R1ejzKjZuTfW08KrXHud5wv8kV5socpyVK2HRFdSitsBZPaeK2nGdS"
    "CK5n+qkl3Z0VcUxQJcqipCFX4+huNbVZS6a1L8ipbnE0rMu71E4qdPtYbUeXqXyrhQ0mS3ZBqZyZcluLNW3UnM56hxP9aqbWrfcc"
    "I5Mdo4uUuZD2S3dQlitqrdTGZaJcwQwVdye9tkVpjSrRY6Wt1h8oq2FnMMi1cqk+x9rlPS6O2kSu1MnN1i16DGy6me7o9qQuGp1h"
    "ashQCoJtak06kanl88MN2u6WcXSGF3fZ3qbXm/PkMFvaaLQ7qdU3g11ub+5quVUvUcKqdLbRopVVK2tSPYcupHJYyuW5NGc1R3uN"
    "NdTeDBAw2BPspqMqWKqYymoMqSO1dH1ZVpSSTDbKFltjWHu1W9vcOrO1nLKjaPiunq11XG2LVfH6brhPqWSObGXy89ZmBKabSzBc"
    "52i5XMgJWdPq5TpEn52vlTI+zCqJTIbJtuZ0y06D+V1Z7OjkfD3DMnxeao4KdJfIuphNzFy3qZKVzraR6hkqp9hDYyJQ6N6msXRn"
    "MRjUd2M3v0q090p7xhhzktgZ+8YwryL1lTi3aihZ5ES60ScKGMVklhmbaezzda6ZRYa0w5NlFhOXrZ6yrLeFlLbvL4t1qVKe97t9"
    "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"
    "CErn1EyvpWYtBtlmLWWczwklajhPj2fzTmZjdMpKtcfmU4kFV7VbXKeEZUoc3ptVwFjOzen5ZmzVTZHo2fwOmWXz6TqwDkDocH2Q"
    "zs40bFeoZrY9fVtmMmqHmqdTaE3J9jDGTLVHIlun+8DDN1rdDZKVG46NjSrSetHI9Ss6myHRturOrDqzzBC5SUnHJYebjyh0VoGr"
    "7dVJsYjm5yuuYE/c8rpF6h0w2dCdjGENHMzs8+J2NiYGSiFDqYhL5vstnhPT+9yAEDGT0bB1e1NbFtFaa4/vUvMyq6BmrYjJ41W1"
    "sXQTKQPPMwy+kkx2SY7VhLgaSJI0G7YG6VyDxgtYmmxNxPq+oyNFfp3orgRJbJSIWVEZCilyuN7UOpRI4lILz0pInbe26HZV72o5"
    "bZPrigSyWW6dDJ2uDNBtpl8bprYUCuz5iGTVHoVshQ2z2lWoFGM2tt1cy0yo2xE1K1SqhWKJm+xlbAE6Jt/Z561OCW06W7JbwqVm"
    "p1wc5vHhvNPfUDnWYtKNHlOpJep0bjUbMKX6KL93V9n2diEWeKLaLWS0ocnSmKGoqrvFs+nqasxuO3q+mmkObF7YFVOUIul73ElX"
    "8qtUziznkZyWNkqFFq5mFHGzKJfcxLCtr6rlluVSc9JNpSqzirIvpfaMKs+c1XrHUeViu2guBJSqcLlxwiRZfpuvEJ1eiQfTA5fu"
    "98x2ZkmP5+088CiaZbaij0fCXtmlnMy2U2uV+YnFLMhRKof21EHTVslRXlj0J47QWLHmAkHqEmkZMrbC2z1mwksoI+ZWutbr1qrd"
    "5TpXobpirW85NpFrFMtWQmJxe5Ur80tjxHS7DlqyFxliKFHjFMOo9ra52tPNiSK1DVURSx0iXVIHk0R/WMCIBI2kMusctUkvMok2"
    "NXd1jZeXzKaOG+NVXavndVaadJTdCrPVbrW2Z4bFvCXRKDrYbYjtqt/cTRIFUXAFh7ZkNNHOd5pIWtKFBJdfVrrVMa60+LrVF1V1"
    "kxnu3WKii3YmxEQRXbNTXqcaWokpW8a+rrn1tNUp8pyQ6S1TvZW8c0bFWobt5NBNlVp18Ux/hHKCrVclorFXBnK+OjQHFtNZbgoy"
    "M6lVsngmM1KWRK2UlWsSyxXFTrW1KpcdYAOKwwE9MfYLl99Qq1VhQk9GXco1mti6grWBO1Fy5AqZtecIbjrdLjJgiKK0mdMzotBv"
    "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"
    "8Eq9IAzYHQZ+oSX1fFnC9n120BeRKIZn8fv5FCYCCcUguIjTCLs9XcAVy/k2OOEoH/ALw3FhhBjxAcjkMI5HA1jRxfvT3tXHi0my"
    "6A3O0nTW+9vfPnz4UPlQr0znp3+rVavVv0GRQcDvGrVqIF4q4Nf7cfzhx+nH3gDVLmr4H52bgL0oUoYhJUBOAS4MLpKeAacFd+Ln"
    "rUq31W3XtxqVBvyt7bUrtRb8P6TDdqtT32pX2vV2vaPSnUq1Xq11ZPlnYR0z6ltdUR/S9Vq9Buk2tSPTYbVSq7cbW7I8pJvw95ls"
    "L2xSek/2B+kO1pPwyLSEV5ZvVVoAVwPT1L5KNwgAXZ4BfhaGlUa924T+n8lP1FKtrZqilgAEmW6IoThT9ZucXRHxZA8lmoMAg6sM"
    "hkmz2pgBsw0r+vKgfyjjluwxRrzkdRexE37A0NK97TB4+9aLUwugFTMkGpM4vaKTOV32D05Lzw5kaNESnLbl/vcimM1BKS1jvNAn"
    "EQZpocDV5TJHlsFQK4i/fyr8BXZp4aAtZ/F1wQxfxOzmALZbfDrFQL2QOIsu3l3OT4FofAXcDduITu3mXtiuNMJGjVNbkMJ/G5Vq"
    "p9nRKSrGP7tUWFaC9cZK/ONJfa9WaXaa7a74UKOvoo5MNPfkL+pD1aD+6/z3Sdj+DUHsQkkFYZf7wmJdWYmhqkrwqgIsCV6Vx8Q/"
    "TPDoA8Mh6ogEAyfbl+Wp6zr9kaA1zMlr6Llr4rAUaE01dU2ahVDB1hIz17InrqXmTVYQCTFtsnlZvsGz1hCTVrCvwg+ffm8NeV/9"
    "aOyrHwll8/YTI3TeNvrz5tvojdpGszgZjifORpKZA+QW4M+H+Zgj+M2jDxjQaTbCWG1fY+M0K2ENMAoWI9yDRLdea2Cq1a1CbqvS"
    "bjdgXSvNVr1FKFFvd3C1wla720VU6LYbdUi3W/U6IEmnUus061t1XE0s36nUwzaSzXqn0YbykG60kayG9Ua3ht/Dep1wo17rtrH9"
    "ZpfIbbNR63afIXJ1QqLkrVpYBzLdCDvdBiFjrdECMl3rNrotTHcaHSwX1kPoH+GC79hus13ldKPafFarVFt0onSw4l4Itdr1kMHE"
    "7EoLoGjR53oTh91o11qUrnaqMD1QrNloiObxe63eCAnsdrXV5Uns0jQ1Oq3GM5w23BX1SqsRtqB6Ew4RIk2NFswadNesI1mqAzRt"
    "7L7d7hLFCNshDL4G4IVIUcIqAou1QqzV6CK1qddChgAOrC1zFX/DNa3iNMKy4KI2Kq1qC3dhu1HFRcXzu96GdKfbaRGl6lZruGhh"
    "q9ttPsNTuRm2iKLVWzWYtE7YrTcIGcJO5xns3Ua3g8lGO4RTFBel24W5blXDJqwxLFan04Z0HVCJcKhT7yBN6YZNXJsWtYdHZ6NR"
    "b2H5TrWK3cNBWm/hdxhmF3Go1qh2MV0PYW1hkgC3Gli+CkgF4HcbNNkATyesEQ6KtB58EQG5vGjM05QJyBODgLwQWzWPhMitnEdE"
    "3tyciPzqiW+GahhTeSt3IpwZ3zaNcebVyikwN3ZNfdmexqtcY0CVH8vCLXhmmV7rh1ujDHD4s8t0HbPpaDaLozlel9xhFAUQSKez"
    "dR3c5brqXz9Uh8ev+hQjyKWfCsOMFfv3XR3iw6MP1Mz6XDRn/d3042rHnStVtgoVvvIAyncza6JOrj8DRxnEquPV9rhdJN5AZcps"
    "ZCOlqQ0rZtSmNq5vaT5tWDurdrWygc2Up1xlGbN5WyMmh8DY1qEaokcSot6mYK/U2nNMUM2mVxmfriybh6fewoWbEEZxgo5QSUFp"
    "PCEq5epeGmoz9BMDsP5Wqpa3FnBuxKVqJSyafI/jebbxyJwArPVVLqZTWWco1kbNdUXtRwy4hg/PWR3tpl2KJm5ErVTdAr26NcEt"
    "xvgiINgdh4DE77ktf/HDYCs0SptoJHTe1hjPnaKIHOlZsdfyNVZttU7k52yDO1/6QhXHm43EUn78rFUTwQpyPRzlnw/rK0/m1DKV"
    "JfMaNpQjc4qspQyZUzdP+fHzttLtLY7EoPxF8sIMqXHyPkLW7/vP6V40slHH7zHoOBzQeItcSf8LdhDXX5cIZDq+0XF0ewdKBp4v"
    "SKWuvhxtNQA2vZ7KW1e4ZtUbAy1bWNvZsG/EupFNuZcVY/jM40HBtQZAi4vAn108tzms7+Ji/RsalF1H0pCFpNhxTJa5vtiMcb/Y"
    "kHe/yPEXY4I8OQ382Tea5cnp+rMMZdeZ5SwkG84y9LPJLHuKF86yU349vf+s0ouh7mYK7DKafJ4tS1oj/JPUTMQeQ2VV+RvzxcmG"
    "pe/Phi+xHVbzISWQXW9u5b6ohZXET2zLJvTUpMhiPWrMJX1NZ7/MmN6TnjLp2ScePXtn9a06qHmfeDTv3+GTRgZhUT6Lx8vAc+bA"
    "N6G05OLWAKWs/1JPNT9Gi9iYl0HAotdF7/RjQEvXuyLdwR5Jad+Nk2j+qffjdDqJoySYx8AlJpNPvav00yxW2aP4JLqcpL3tkPTw"
    "WXrHRX65vHgXz1UJbHTJw3g6EkVepcjJ+YrsIeaJUkei2OG73+NheuwrTmoPojgXc0rhmj6L3sW4nu8+FXWvShYUWgrR9K8HOHHv"
    "xyPDokCquFzZWNhLz8aLwNG0oszlcrkja2/9dIC7697f3yEEfzuLJ7N4vth6tIWgTE/uSVWxnw76nLP16tPFu+kEcVU0MXjwwPpU"
    "GaesZ4moSTmDXY/OnqgTL70KfU6bdnexCDR2OaRe+lwG8rflb6QM6RSb2JUw9FSHAY15qabgZ0gGaZDI3ktp/w98TSiPAZBdXt0K"
    "LAdcE1AvKJ6nn6iCRN4gTi4vWHGqt10NALaT8emlSuNbpPi9LPfio/S4D1V0938caPr2DwRlsCAMGJT15AM0xmymvfThYKBboFpp"
    "+Wp8UqKhbfcHU4J6cH29HZflnO5gH8kOlLLm9rvB5QDtJ/rxkZi8dPpiPr4Y49PGMTTWfz+Fu0GVYZz3gVcCekM97nCPc6NH2dt8"
    "Jz1DJ3uvoauD+Xw6Lw3+/nej4a2Ly0W6JQpHWzOVT5NaGZSXajFw5Dwju7w3xE4v4yoiTP9RFMdLbf51kHlsiqEz1huKEtS8G9Cd"
    "Cf6+m1zOB8dQHgfTu/IQ9t6V3Jk8LbA3L+L0bAodXZ3G6YvXh6zG4UHrUswK+dMU1hA2YmWWXox78hcMJ7gSOoy9K3mRpK/yjJKH"
    "EufKFBDdZTBN9mgsVrewPNtWUTSgwbQkrhLvKJMJ8O622SX3RGuyQz+9B2DOhwo9w7/ByqU0iMvcmJMZcG1ckZJaD1hYHNJjXBVr"
    "RGZhsWYxjf5HWLgswxAkO2YNWl3sE7AKEJ4+oVDtMZ6Q5Qq3AjsNaS6aBRKiJwwNchOXGBbyirQ7f0F8y9Dgrc3nSLfGRRAeTEKP"
    "YgmMXnBQcX/zTkZvmVYxMnBCUhegmjheIAEWFmzHvUva5QoByjDRqBv4wjPuN5MSkNErxfMQIJLt2QCXA3EB5gaynNGS4UE2Rv/C"
    "191l8O+D/tEA4Xs0k/wdaoBwhmxf5cAm/w0rjDGLhofKgjDvqHelaksOA6vpFuTugZ8I4KOJOuetHJkQ0wA9/lODCKn7ZkqfyPE+"
    "H0fBPBgHkZphfOV+XAIw3g+CN6Ur4pR7cBJ+LDFFgcWJKiYBkvnA/Nqzcq8Xaa7XmR/UhdWsL3/E8rTuwNwdPSsNBBMIQMBKI0dO"
    "HFZAzAu/pwtGvnfE8HGFciDKEqt1LDgakUf8VMBIGjO6BUTSI71BFB5p8BUHGFfkT41YxkgUMxkr0hfcc9YOh25zbWYR66v4oO4F"
    "sRR+XV/zoaBoV3pUPb6+7mc3TFQRRVDrXvyskLlDKQKW8PQSLaoWmrSlR2F+Q1iC28FfOc2I8yE9quU3xGW4Kf7tayyLaWKFlb4F"
    "7K1y8MyPrXi78CArZStcdXHO1xDdODwtcb63KQne/YPyMf79p/j774Py8j8HgBuAQfN+vE+sUrov2QppdWfpnMlMIAfIGiLdwJMN"
    "EAN+oqEf/pH2FV9HabOCKkyseNju1FqUIHWrRliDRLfaRe2tTiVsCa2zMKzvkfZWqwXpRlivkRZZrR1iuh02UeMIylcbTdIQqtdb"
    "qEjFypS1RiN8E3b2REZHaFXWxN8O5YofTzp7baldSR/apOAo6ojEG9Hos7DS6TaboexyD8ZR69S7GqRKu4qKbgrkSqceVpt6SJVu"
    "s9MJ1ZBrlRrpaIWs18mz9ATn67fnnUqr2migEmez2Wo19iDd7XRQm7PVadY6Wx3WKO00qg2RCKtvwjbpeqKC2BvULw1ZLZQLQape"
    "DWuqBUzDcGQPqOJVrQG0ddLtrHTb3Ub3mQNGkaZV6/yPyWmLNa2Sfa1p9VggaJ6mlUTgPE2rdP/GmlZzZ+uQuMO7f8QXY6cAMw5N"
    "KUvXATJeAFn8SG2vr7SXqqgJWJG7CbEHsqptsaEapHDYrXZ4Q3UJ20K9oUjTsIWqdbyhUMWu0UKs5g2F6VZXbagq4ku3C+2+IY3g"
    "PZlLrat9Rdu30e12MV2t8nfYXfg7FHusS13yFoNM1YJKY/tvRG+811pdCQ3vNdK8BmjlXms2eDRyr5FSqxgt7LWumIs27zRUwqzQ"
    "RqtSfxXeawBtoWb/+Wk4ec9oPc6g9WNCm2LUFriVh9/zm+N35OL3As6lMz+Ci08DYaep8BruFmjUAzdJvHiyfaT4+FWsU8IaYhHg"
    "N/xs10KJ3yEqmYesr9usNjjdrHdpL4TVdgPVhIHKUjLsopZwrdWpUfEQtZ0h3W42KAkYBKXr1WqLkt0WNgZlGtRYrdOmdKPTotr1"
    "VohWJ3XAQwKsgfqukO5WOdlqYvEGYB0Vh4wuFG/UOx1qHhAQ9eaFLnCzE9axdqNbZdi6TbRDaVY7qIEMxLbZQRMWAIJwuhU2oFVU"
    "lG7STm7Vmt0Olgfg6Hut3SZFapiCBms2d7uUrrfpOyrVYvlOF7cf7IZWG9tr1RodSncaVL/VbNPegQO2g/rYzRpa7uBea3WQ0HRq"
    "uGFw69M+7dQaZNhTq9fIZqBZr5PCM1SrY/Eam2ZwrVal3WqLdKPBGsU1MuTAaqQAHcJKdHnjinMcyUAzrJlExyE5NYPkGNSmWmNq"
    "0zGIjUGuVDpLbOhgN4gNHewGsak3bWJTbVrEptOp2eSmIakNURpG7N+e08EKhyyfrNBnFxBRH/CYbtSbwCThmV4l8gtNNmtGGgAP"
    "2+KU79L0iHMeClrnPDZknvPUERpEtetQvgN8QbP9DM2swvpWnY/85m+SXzPZNfOAqTsHjHO+tJzzpeWcL019vjQrQMARGxvMTTVR"
    "BR6xv90mff1GpdWo4mbpNKACacNXW5gmlgRV5buISLAVYRfVWcO9iuYAnS5qwqMGfKNJVig2f/METdH24B8y5anTjOLMAmAttF3R"
    "6VpzTyZwyYURDlsZVYjZbKpjpFAJ/c+P75q/8xkyzZwhr5gyrzhEBP3OO0Wim58iC3WKzCaXrm0YZw2iEUocxskQ7q0LvGRcTOf4"
    "J/6Yzr8OJ1Tl9XEsoQQnbdhL1d8IA6jbM8mif99giyJflZK1qA3+sWf3ITs3IXlzm5Ze+M+b+l6XTbLkd1meGqG/hfj66XR4IVj5"
    "oYGvLwgZck0m6Gsegi5ujqAThaCAbBn+RuQNRjGy54rDgR+n0fwdWbQPPkSLr2R4BSdXB2+3cCZWa3U006k2iXGAdKOFdix1PLqB"
    "aNZrraZI4yWs+aZZqRJjI/Mg3W41QjJT7AI7gPZV3QabLXbgAIY/QKme4NVXXGA5R1xt0eq12e2oVBfYeCzZbhDLUG8JLh5YDqTB"
    "XFH8egLEs9uuAqYy67LHaWGT1SBTynbYoDO6TXZDaPiDLAndspEEV9udvQYAWuW7Pu5MpMctbqMJbAil8aDgPt6IrmtoUgUkt62g"
    "ogtDXcEs7A5pOMLskAcqsF7MgpqgBrE5AAy01umoaYTjBs7PrppmTqO1MC3DG1iSPcqjWwgMto5lu8T/ieVF9qJWbcvkE7H6vz1v"
    "AGtkDG2P0i0ye+pU4YhtVDqtkGkEDwCna0tc53kq6XysNWm6ajTFTWCkkAmBaek2GyLddqdPdC1XDiULtRCtmjts3YyMR73eack0"
    "/212iV9otlQ5PBax3huAp1bvYj1laI0WblvUTpcMsbudLtbjfkQa2LIOtCe/hzBXDaN+w0xj+29Ef3uU32kxPG1k4Tr0l/oHrHDG"
    "AwxMyHtODhBWAS4EdVUB0k3gkFSDnM4OUOZLALkdPQDZjxwgMlqtVqgmANJVXb9ppq0Bcn5DTbhsR02wPZ7fngssI1O/Gt5NmmTK"
    "J9JoHwkMUIimft0GsfshIbJJUyiv3lbIjpetrtoKLWThql1FUYB1h+vPHrP0mu7UmXNXdInSTWvDcB7a9YWddrvJVpEk5QNYkV4I"
    "+ihgf8JDKzqbFn+0LoaCl7o0zqbX80IuSpwSeafT5Oan00idTuRWLZq4XiFU9le5T8M9s0EHfpVujlW4vzBrEdZw2at1cWFpokkt"
    "pOmmWWMbVywPl4QWpRs1QoxarU6Syyax6iGUJr4C7pUdwqoaiZDg/ohnR63WaFFrnVaVrcZbHeq92+406cbepdbq1Rpbl3fgQkvp"
    "Bl2T0fCXv/M9uR42iDGH+0Uby9frcPPANFzmG3Rp77boe71L9956u068E1yECJ56t93G2ai36nSeoE0r1W/DhsZbOxwzdGOBG1ed"
    "rulNQla4SdUx3STXFTWmVM+65MoCTw4mNF30fBGSP4lWrUUERqTRxQVSVC7for9toKBt9mCBxZAAYzWZRoKIzTZk8WctuorgwYTb"
    "jBhQmaXt8w0OtEX34VCwoU1xKxZ2/TWrnk6/Ea0/awg/HRLYug1snYCtK2BrgljJ4jXlW4Pde+g0u/eoKd8a9BeuoQ0arJxbABea"
    "p7kGytRG8OutJkkr4ZJIZ2SjU6XvgNIhnZkdXDq864ZYvN0gsOqdBi0BXFmJz0KUaJIdc4suo4AKtQ6UB4JHN/x6o0NMAFz8BSo1"
    "sfUWAIGpWr3WwNKAwJQOGy1kEdokXUBEhS80aACXEL2LjbdbgMm0D7o02+0uIDSlwwYCh7bSTd42DQS+AwSW9k2ry9+b3RrtOkGW"
    "O+1uh9l5QOg9uvFye8DvEFdSRWNtTLdCMpAP67ypGx0EBxpv8mf+Cpwc0wiFM3S3wkSnGaovYavLpIL2sklY4NBtiPtYQ99XqnzY"
    "yStZJxQpOGLhDOl0mygDwDOZ7u7QOLKVgBwkHAJ0If6oLZzIIPogvvIRKsu3hbOZBqHVlpHmerJ8k/4+Q08edXYVQM5kENpuh8o1"
    "W7UaO42p0wWtSUc4pGvMibXCBpWvd+rUTwuFN5gWLhNa7ZBkDjWSzEEaKCGWh1niLVhtkrU9nG+8C5HPRhlFR3jhqMGuIav9hnB9"
    "wKxE2Ar57kgyFZRpdLh8vUHtw2S3OM3th/UW+yqot+qcror6bb5+4CsSphsNYtOrxL4LRyn8A338dGss2msDASdRS7UharEor8Oc"
    "KJzaLUqTiE/2Uid2VkMB6WYrFFA2OV1t6VEgfyHrs4+XTk1ARbOATERozBLQorYYRUjIQe4raI7ZQ0zIwPMaAO506ryGHcYdICQE"
    "TavFqEUiZ1zSDhVvtuu8hCGNrRl2qHQTtzwxMN2OxKBncD9HTJQYhiIBxlyJgTrNGCrLSwwORb7E+NDB+JqF8bg0Nbom4v55Q3Nt"
    "XPTDOlN54axm5UU/nl58+jRnZurEYKbQb+wPkwKPRZrVyeOoRjfnqGYOR3UxvUS/lOST0sNZGZ+/BoclaSVenLuK7rVMsteyqV5b"
    "MvYCBzriLJU40BH8gsSBrnSZJcozX1FXOGWkCXe62sUWUT3Jt0iq17KJHj5O1Bua6LWQ5jHxJKLXIpoXKqLXsmkecm0tJh2035DL"
    "awgahzSvRSx9W9G8lk3y8ObR4O1Jmx3vHqHY3HVyNQQUT5BEJBYtonihInktong1RWwwXe20FDFq2RSvRQRPsUiC4DWR3olKSPDw"
    "BG1U64riNZHgCe6pwTJmGLumq5gOWy0FRNMmeJisNrtqDE2b3qEIvtFqqiloErmrqylqIrmryVMD2YcGssWS4CH3AYyFWoAm0jue"
    "YSJ4yMu0mXwjwWsivetogte06F2TyF1d0bumvJULelfT7tiI3tUM92t14t9UmnCz5uB63cH1uoPrDRvXnzVtctc0qV3TFGvyPsTb"
    "/xa9hyBlZWaYhEIhK52EggvmVG1P/lBFpbIIFeYf9nuBfJ8yqonEXtfqQpYPhRi3yT+fhOi7h8QjdD2mFjqSWyJ/Yh3JLVGK7t3U"
    "pXR5Jjtt0KMeP2DYQHYVjFwrFAkGsaPFzFS6oyDsEIAoQ+E7AgqdjAsCLTuLEhlAStHTDd03pHs1cRcRADaJ/tkAthSALRPAFgPY"
    "dABsKgDJY1tIr1SC32w7/Gbb4jcpVRdi/bqg0bJOXULY3qpnIKwrCOsmhHWGsOZAWFMQ1oS7tSIRxvj3rnBJdOEeunSY7dNRV3z2"
    "modi3hk8u/kZfOY9gy9nufINq8DXknTUu46oo+GIOlqOqGMzSUfHkXS0iiUdDUfSUXMkHa0Vko7QkXTUHElH6Eg6QkfSUV8h6Whu"
    "KOnoOJKOuiPpqDuSjo4t6ah3HVFH3RF11C1RhyvnsIUcYdc+wvea1jNb03xmE4li0YYB3ZeRbdQd2Ub7v0m2QZpWRcKNsFi4UXeE"
    "Gw1HuNFwhBuObKO2QrbRcGQbHVu2Ue06wo2OLdyomyyCT6zRssQamorQOYNCCcPlaEs/H4ctU6jGT8zmg3DbehAW12yHnWhrdqJt"
    "shNtwU60HHaipdmJlvLsSXdq47hWt0QWuXMLnGrsyR/2cc2iGZZhZIBsaCAbJpANAWTdAbKugayrE5t8ABtMD6WkC9eqaIFT4Z78"
    "YTM9gl3jNxEXyFADGZpAhgLIqgNkVQNZVXxPSCpCinlsS7YiZO1gwVZQqiO4x47NPHYkVxGSzo4NZEfB2DG5ig6D2Ha4iraCUCj2"
    "FnEVzcnpJBSP9qdetuLX2Rp3evugz+Mszm7OWbzdNw1z96M0es1xpqSh3Me3tlku26P+MJ9HnxybVdSn/zn+5NjLPhY2Ba7F7Hz6"
    "YeG30a1izJD5Is39mk7TaPIyHk7no/wmVJyuAlthVeaFdFHotbYdsONFYHWiyYfo0+LV2fTDi1XNmyC8ji9m6JxJTo0wDuZu9MQM"
    "HuOwoeX42Tg533oxj9/rhPix2PoFVkZlP4uMChjI6kU8x7QMLzIgKOjzK7Tp985Wk1dDVJWmivkLLdAdC7+MZ4Cnzvjc6StdGTWW"
    "W9OTrStaQkwulmWAcRL9WWTTLQK5rS5Be8ILhLDLpDBNZNm3Jppi+UPyhlhgTy5Sr4rLAphYfHWpC/g7xmLPmbHPWweEDWN05Ez7"
    "AlITZNBJBQd3NbZZMIms27YosmDnIvvCIWWBAfvpZPoumki1bJjvIoTiVp9N0W3ZiuWTFgFy+bg5v1G+FcikCFi0JojmsQqK8mPO"
    "0AajOJ4d/IHxHAZk4Yv07pUDkm9mjSgk65VyG/UuBo/vh8kkp01FaCmkZVHHi/c6KpN/5AEMOP44o90zienEyJkioDq4G3V5sbNE"
    "eZl0oXSi0xVOkx1rMAcQCj8YZOPLFbRM0VxGHOxyHQQzyq+mPEMMyjhbrFnajFtYuM90BEMb4hV0jUEXkV+opzUnxirrpUoYvfUV"
    "YBJGtsmhTPGCYuaIwppp8A4R3bevmgYsA7nGwvlAg0k1XXrkoeL0g+nJI6eUjrJZMG9OgBj7aPXvaSM4a9GAOQzNmxUs2bt5HJ2T"
    "q+aclei2qrOPuA7A0nBQq0UBQ2NFeS0YthEztqBUNsBTQYuaefFOBznTMFeNmFxPmfVdulDxF8z6rjoQn6Kpq1nW070ZQ62g2awL"
    "FxET8moRv8ebAoosgfeFzTv/NAjIMcR2NSA3YfEIf6Kp6yHaNeOSsSvt3hWZEt2sDWAhOaxh7yri0HFmO+PkZKqboHUSzocE4xG7"
    "NUZoQjz317GBJzNjqGo1KkYifDSOMr3i/xE9uMFUY7iqG040xq66YVUOY3XDxVkqP0BPV/gBUpe7Qi9AwXt1I4T9u4c29eT66Wy6"
    "SMkjxcB/SXS8pxx7nDkpP5iUoNOYf891R3gyOteJHAK8ysuT7YKFD/8Xrz3+w64YUnZEQcVE4DyeoN7V2JyiwCh9n8vRISZy8BKs"
    "ODmsikDSJ3ZEsIbbC76oG55cpFOONyXpFqY0EIDev4qXA/QQQ5OZLoXnlGyRVH+ZcjN6UjCuWTlA3z1lYCjM7DxnJuY0PXiQyYJe"
    "dn2ZirvxOqbxDf762ucJ5mo6H+PVenLwHhcoJtGD4ZVmaftmGQrc+kE51cr10TIfX8TvL8mX1Mn4tDKhKwn5eNg1V2x3ZXERqhC2"
    "UG912ctEl1YOhJSnOkBg2h291x8CuU16569Nh12fHPcgiNjT/nlpQOUH5WChEuRSYcfwH/K0tAiuLoC/mjA3odxeSudrQHEM9xnO"
    "AtnuMIQTDnOu9Vpr/xEBDBhJFrYnfwaAHpGBlK9LAwoEqIFeBlfkY26/5AnlR5G+fURkV8jCfijlFikHVyizq6rNGaspYNcSH0qQ"
    "g7/KfIUPOsGR4RCGPg2Oy+Xedm4f5KBMII+AaIq+K7DjMFAeLPCvcF6RMw8V9mSh3VYcGf3/WBoMgu1q+RgleyhKQED12toeayyn"
    "NHJpMDCSWBGMjJdCs8v3+9IJxid2gvHOPCIs91q3fUpQL5nz4i/S/xfpX0X6Jek0vR/+58Akmh/ziKaJ0Q6pnH4OqWRkruCfz6WK"
    "L40IRSZRytvrwolV0S5/p3b5x309Sa/2pYcxnKp8f4+7nNW7Aq6/nyh3j9fXg7//XSaAu4dP6ZSvXa+jU/pqpAe636hkrcuwP3/w"
    "YK49OG7JjQnALHbnvUUw6QunjGgUm8aloS6s1nBvvzQJBm/HyfvpOcyBwkDqijuKgkUwhMaqwWV/fH19BLfC/nYYnACpgAMigf+9"
    "B6SLerPgpDdDv2gjQKJGOTA8shleI7eifgpnL5ws/Tg4qST9JJiaKDjDrstXJ9N5aQHfYJRB2q/ubI8ePJg8eLA9hg323WVlEien"
    "6dlO+vAhwwiz0r88ggvrrH9SmQUX/eiodryTfF/fLY37F/1+f15+8KA0hGxoNTpqHJd3mz34WQ/q5eMAMyC3edyPy73oqHr8XX8G"
    "xaFq8l3twYPZd9FRCDVKCPZJ5T2AhIBTZm/23QUUxZL162us+z2s8Pz7C+yP2k0CapnrXODQgbCMT0owlcn3ofQDORV+IGFq4WIj"
    "nDpuqQkcB5fBBTkqnECdjMvIn+KE8WlrvNiKJui769PW/DJJ2D8mTibM3yXMQwjDKWFbAMglzO7FTintL76r7ca9Yfn6enu0U76K"
    "rq9Li93FdzB5i++hQgkhfxSWgxnwRUM4UzE97OFMDMs76fwTwdWvIWbCrwVUH/c5oizQWZin8TH7WISuhLPACNvJjkNuiy12+IGj"
    "SabpVgTzI9xm7pCvxsoIaJmcunRnCM2yL7QFrheuU3kZTxbx1oKHDB1HFS5exkDbDENZFB/2DRBen8FOkmCMpjFDIG6RW9HW/xk8"
    "HD8c/J8tPk6JjwzLO1E/5g4BPHSaOAI0TL6rlneHPeEHFNa/jE5Cp2WSQC2HUTo8K6Uw27APoA1Yi3R5gmR88ulq0g+XAgcEHwBX"
    "dBhyD86/JWwQJALI1ASTJZPoK2MHLYA8aaenQys1wVQq6QL6A5MU4fCE+JjL/tHx0fx4Ny2lJfpVgnXqlYBMAGsAhCzwn4F41MKO"
    "7xseZfsL47dNiC7LGtoTw52tKLWwwNr15gKJmQBcceXtW+rl7dv+JNjD42sc6O0g78nIHMa54Izgo9xxBo3kBkfoWUl50R1ArwHT"
    "TCt3WA6GFRGUDJm9vgcGrucHj3rif60S4kvRvDOM8sgYZAsOjnjzbKlWjwdQr/RqP+vd7upDLwoueifLZblkuP7dU3yBILd9r7tf"
    "pgUlwBPgua+A7yAkvxr3q8s9ozPVlHG00QkhuvF5QUZuRpxSWBZ9jZaX6e54d5zvY3ju+BieGz6G58rHcK8UlUT4a9hQ8Juo0iAI"
    "KSGmMKghN2hMg56bDxbPFEyBdYNZwFla9OOj6Lg0BdzoS16Mtz0MDEcnDuHlgugZ7LlhuQdzeTFeoP/FxXTyHg7tciU9i5MSHse6"
    "09f7xuQ4jk/ZTS1wJsoVoTzsk/jDlmhfXxj1Od+XXgxxMfQOnWJXMMqIRjgFbkBMl+kcepEtJOYRSk1LwjUysqLY1YFWsZiOPmEs"
    "+g3uSVCaot0/QtEk3jVVhnSBZmeSKBHdLkw/WPVUGuWUZtqqkU5P8ck4YI+dj5QnZHmr1zniweURPoI+cm9z0BQOq0huLq4tRZJ1"
    "euFAkUj+swB09HS1s/dVBRbQyYF44Sp6gyAZTWERMSurSxgv+97Br/Pm5Twu7XEYyJUvFnjtx7JQa1HUfP4b7waPn2qx13j61CNf"
    "KbkXt3zDI7cWbmddcY+mQyINB9D0s/EixZOBBQmwpCd7k/HwHDWv8IkDTjS6WNrFEKY9sd1ejy/i6WUqXngQy7PnyuitRAQi5SLB"
    "YnoeCdyTALAPSB97V7Jw5kas2gGGK7hHAgaddy/XB7ZvbwZX+qIstmdAMSA4i37CdYz+vr1/pcUWy0FgSDLkhlOYzhduUlOzvVIb"
    "QgCSMgx4Pw/KQmjA4bdfpTD5n6T6FZzCAefnOLjeuVmrgT2b0qu13GToShpJ6ECIHMx8pOqWmIO7hWzEJuRZoGvg1gRalDLH00+X"
    "qHsXT+DugMw4+SfHcYbwv3cxXFbiXxOavszk+fDxwYN+6cUHjDpWGojvj4aIwIMgtw6LCsuGUGzokfLoEzZ6WzLGS67UC6VoyA3c"
    "rSSN3vtKqfR5br1jKU/tdP/yf9xl0tBL2We4/awtfcDntgu3+BXtYuRTo8kNxHjzfDHefA0x3vzOxHiCYyPVrn0vFdz6V8miNprO"
    "lFGFExkNPNzziJjJjhQI/UTrS7PNf43TMxKQ9Uwu3GneYnDcDipWWhJA7jYmx9GZDtXLTH6fGS7qZt2OF0h66KwrXtzh2XgyAjS1"
    "11fmEpmbztnR/xIlmKN930FZQIh9BytuvLxv+laUcmNJ/9dLDPjABDKuqPO4T1lAqOkvvpmlEVCQUlK+voYhTKaLeAEzesTevIeP"
    "Fqwt178nCOC948GqksC9xBMsh7dlzwn/4AFpGkjC7i2DVRXMMHJvob7/eMCXQC6HUwSzMIACi/EoHtDpUNZ8SyUajSyKXhrAiQHs"
    "FJmb5c42NnGZrLOuuU3AAiggWJnjJnDkfyLcEzEb1NIDK6aO4cya9EvWquQVFGcezMDiwxiYLLx1vZ6+GccfiKvOjF0xWrLz/IkD"
    "Qrv5CZz7Sey+acJsaPaJSu+2DLsi9rWmB6WyZG3UgNR21COsBjKmR974LKLl3EBX0+IMX+ljIJdFc2KdCQZmpEwUUpsmYJiHORx6"
    "sNi4MMkG64IIYu5Ch3gziVpjxEnMF16T3X8pvhlBVkTxIz01x1j1jS5h17UKrjOrHG9D3ZPQgiAmxhzQesaJ/azyEyOIU6WPykU7"
    "fkzQoocENlqmqmCjfTuvRFEnfo4/oVGtG5bIj+Vlbgef4CG7fDVEl6cHCbrE7tFvuNTPopHIESedQVjjYBDTt/IOCaN3uIHFMJrF"
    "orwf0pxtIAUmt7YRTLDgCpszBtjgFC1lcTY+SWECmT1Dkvx6ijM/BkqMIyjJkEr8Ca1FRDbd09zieRRHsBOv90v4Ali5UCfXlmQE"
    "5sFYlqIiH/ThlvCT1s6OXLukkvDCAXMMCz2HnXwCc8GAye0bjEW2hE+SNeZmS0BGt8flK2irX+M5k3JszAK6XbmPorrXsOdLZZrO"
    "rbA3HZXGqKExJjUYFIubu0CWq/VUS1GphjOVlJdllAoH9jT+N04XwvZfMVUSRndfxzw+Ea0T78HbT5DtU4GZ5N7iB7wyXtz4fnUw"
    "ifF4khOXqlEIjdo8XPFGCZ3Jotzoq/E7uJ2d8hubpPWx3XFenYRe2ZLKJFrIonvIVssAdVvprjXCWED3iHnwQRnD9TFZyEX3tNzT"
    "w8yusXeIuKibDM9TXg6NTPA+e2we3FTjmqJwFz8+TcZp4T1wM/aj6DBejyIbsL1Ctd6VsLFQ/a5h22O94ZXQbXBi3QZ8fK/ERd2L"
    "JhMMYv1ftrgMIK5sPoCuDHD3a697IWcjx8QY8bmjulN86ZX+C1gwJXe2Jccmkyz5U5/w2f81moxPk8eiCM04GrsMpBgFrmH93y5L"
    "YoSTQIooHnGrgpz276XzyxjFFHhuluL+AVQpPwQyvogfT6YRXIEr9K5wNIC7UIw7CWWOj+JkNDi+vq6WxRwabw8VKviUyh0ko378"
    "cIA2QKjRIY6JagAsx2gD0OYUKxZAm1ugzb2gLYCBSdcB7hUW7CcM3pIEm2/sN688ETbrA+a/j+2uKnAUH8tHJq1HbuN3nvDNeOE7"
    "stDseHfF90pWrCnwt1DOJ3ARCw7KLDaHezGMh5SKM1WPMlXf4bM06RCL9TA/Dq0PH0VpupgdG52x7ZU/KqnbF5UlbanM5wV/2skd"
    "pdhOu0dpEGeQ57iH2cfaYHw9+ehuRZSX0hM/opUGohiKFmVUVfXuqBopq+4zQX+tWcnrBPKfTdEST1TXs4FK5CX7vn+FRPFpRtMY"
    "MsmXgJEJBKhKH9BlgJ1fCA7PFUAh1BAfhdQKUlyjlf9dk80fjkZW/jbmCx1l41XJpct0LtOLMj/+3oKthvWuv4bFBne/nsWGfNE2"
    "LDYC5GFuDfhiSIGEmD0jG3I3PWNPJChTVs10FN9N59yX2b2t6r3/2lT2frcf7L9WrzLv9wOR/w80onk/nyYkgtr/IJMvyeT25UHw"
    "IxxgvR8PghdxMhxPek8OAmV+g9LlRe+XT8tgNJ7jQ8J7tIOdj2fAlPWS96Zq7z4pLd37+zuckL+dxZNZPF9sPRIh7u/JPb2/3y8I"
    "am99UkrVRtR339knQ9r7DsbYadPujmZd6vkBYeAykL8tf2uFwV0JQ091GNCYtZrU4b4pRhXn+3n8CdWn8F6qFTMPPyRSrY77WcjA"
    "8kVlsBlkiub9eYWNZEvmA5OtZ2m3sB8vhrBsMEwCsaI16ZZoWlOZXS7OhH4YKcBJuYMe3Pm+LdcId9LvlA5aRmXb0E9DPTx+Lb5a"
    "9szcnfR/13ZhzhjgUkJKrxiK/CAanlkj+0Fo4UGlMnDQK0a42PXpL45jmL9gVVWAAto3YPID5FWQJBhXzX5CpidqgmM9wXKQciFL"
    "af/3feisPIZiu/k9erUjq452ZNXQjqwq7cjA6P73fS1YeY6gDBasc1rWWxegMfYinKoPBwPdwnOB/oDptDG2+wOh2H19va0UumPS"
    "RE5wP1g787vB5YC46vhIbL10+gKI4xiJzjEqVws1Q7FRhOY19rjDPc6NHmVv852MGjpaYKiGty4uF+mWVATZmql8mtTKQC5UieKv"
    "ixnZZUUuoV1XRhqAMP2y3z9C9mEBxyrrF4pf4jKh3LNIyVGuSMkvKVS51q1kcBy8wI7Juk3qqElrt6HQe7Ot34w464/zbIKss0Ua"
    "VOrzZYBqr5CDZwf8nghzS3nMQNalkfWSL4LBiKrIJk/60Rhu4XSYaCyLJF/JZoOPS4N0NJCWg1Vh+h1VbEZcGBQa2cTfBzD2uMfP"
    "KssAKBj8d5UxN+QI8WU3W/P98O3IsKp09QokHyxUzhJ1F5cmfDYPGFkX80TztloBNKmo3y5vraZHZBi2UNg7hQoWOMQ3JIybB61j"
    "WrYJv+1G0JbymFyk9TyTHm446WIL0AfjXiU2RjkQG8P5LrdLWb0Np0f1giDtWETEaMefOfHef44/4Ws9tNXIb0s8z3FrIuFt75bQ"
    "SUVlz5CEe86kWB6dBmXWXQnu+ckGVjbfxlU5k4rc643127gqYVEUFwh5B8Uo9ElW1ya7IXCoaM2lO9ot2D5YWlkkf4kd5JHPRpVs"
    "JuLla9JwmhvllM7TDTdath8+GpyeyJp5rcnlBh88WHN2ubiY35DnN3Ill7c4zZaUWU6zmemX3MqSdvZnzbnZqcq0219/1gVKf/Zy"
    "GMhe+4KLcaOJw8koJD/yRP6FB1BfBkeF5YllYqd82geA2OiCadWCdcNWWFnEV6QJgjYfTo+qFiE31HgrWYVIdA+qpqq8zMytnE0W"
    "I+XYI8eVWWpM6HthbSxMjA23CHKK5dS6Jscrpheni1whzowJW8id606YZ5Ly3MqsheFQWeproscF4edCtn3P6Gd3uyrkEeayhOst"
    "iwTwS66MXpKcGZHssBzReounnE0ErUZmLaGnl+x6L7NPGss1z01oQ7jvwxUoIiN2ybJmj5VjjY9o3aZcAcLkP4GLwYR0LV1+xVvM"
    "728jb8xPyUeH4tjHA9fVx1ERSEFxs8ebgizZ2KeloYSj9oVnxosT4jaGGPFzUpKTI7wYSMiaNmSSM1C3JNJwU5XuWdc83JWW1Fd8"
    "l9c+/G6aP7nOa7wCaIP/ruGe3l+UfGyz2tXINquEl20+govzdAbTFNh8Lw5goPagh5F250LyzcNH5AZS6jZDK1A2ot9iotbmVaEi"
    "A7/GltMFtQcd7S/HXL2nwmfN3DC0c5bK9KxDWETUSn6l3WaTkZDIiNUGDsgxS1N7kGUPDphHXjiDTCvH0sdGjRgkp9PtnF6fliYe"
    "Fz/Z/vJX+mmBr59tz+BdQzvf6GurR+82Yw1/2zd+f8dPS5dyAuq3PwH2+YP39eDFPsomjk6Oj3GZsnZcUZ4Rl3NEtQC3TA5WdiXp"
    "6Mh/wpBrlgN1w4G5dAiM54nIe5ZLkoMXcENJahnwoAz7SGoyuMpxE2PDsgGxUEaU+1liVyD7yaEofClASJFYXF8P+GllIJ3TrwKd"
    "fF6Z55nyb2WghOPQyuBXxGwqziXwXE5G/p1qgIL3p+yKep7e1l1RbNC3otjkihWVsHzlFUVIxYpKR3OrFpQhv+UFVaSgcGVreSvL"
    "l+Ds2nrfNtddXW7Ut77c7IoV1jB95TVmaMUq0/vnGqssof9S6yzYS5tot4Fo/1l6XYoqrnFiCUAIzXPiFzgnlgfK4dVjw+HV0/Xe"
    "bZ9+S++2T+1322fWu63nVUo9ScmRAV8cH5mevo5J7zihxy9yTA08A/2FjsiE9iV2iXo05auE9NqS8g4/ZFWDsSmXlrazV4veOEg8"
    "mgXz7/uxeG/dvSK/QdvVZU/8knKC+Gj+8OExOgZ2lCLxMQxm4KQ3Xi4zT2NPE6gNF/soTeGmnG6lU+EtKd5Kpskj+g2XIeWMrPK/"
    "niZbdEfCou+EbyUoEVD5CCdAOHda8EvbGZDDrWgrM5+lsvC5hE9u7JdsipZbi/52qCfEmIxEPQAir5ZVOUpI17uknpWmMGk4RUHs"
    "zskC+0EXTzApppHQ/NPVFE0quQFpDS3T6EBH+HNCr1jC21WE7okVXr3UD6LC4EdgoH5KlO+Uf3LRHWGBtVRe4+QgKwugDHGpEzwK"
    "1ZgSZPT4YdjdFPySauaQaA0oE9Z5Hs0GMBT8+SpOB7uMsSfz6QVa01D+D/L+BgX/9n9Lu71fx9dPy0kKvzrXYeu6XivDz71JdDGL"
    "R2Vu4f7fKikanyblXTEepbei5kR8uMIHVZ7R9HuJzmTNp5CbPZtpBU3eTjBHyXfpTvLwYXl+lBz3Y/hHzsdcd/Pjt6yK8ebLqGL8"
    "uI4qxpO7VcX48auoYjzJqmL8eoeqGL8aqhj/8qpiPF2hivEvTXme3rkqxtOvr4rxk+WCil6F1vVABSAy56l9Q00/SMta+j16NzGT"
    "pOVuZqTTy+EZ6qNz8pyfoEXKMCDnxubRKSuI6zSa7hrJSaxdWGFaNz0C5NvYk9Udutj6XKdZBa6sqstgVXy2oRX/xhehYg2PW8gH"
    "fSr2yPU/NG5Nccy5zYLbfSnfWBvGJ1rDY5l6czsoWtjqRsG0bhTrqhBKJ3CPB3edoD3+EoQDHOZmReF1/K/dLGrYepGKdClAukUx"
    "nGu4k0vFQ19BS2vFM1rfOdtNvdONF44Vwr70p73WLn86WuXSDgNtjt9dpmLd8gKeCeOfXAdv5ksGwKB9uVlbFFeeIrZcXMDU4dsz"
    "JM7o4Wxe6OvD6oANNAQF2o13K0c+10rie/lY8SM9KLqYXsQln7ShEhNGllLVCnkZpX1imzdtBh7bOBmzQODGuTB6ytswJ1mYY7I5"
    "X67yaBakpk8zTK7wZNa/urG3si/kqd94rkBHszOU42tv/YKZe/E6Y2lkrZnrrWzXzbDMrRCsGKHNel9TSjZ8GHAsod2KjDAId9fd"
    "inVO6BNI+vhhzQwzQBjW0Ungx2E3lSnW2OVk9JIEdNJvat74jFmCy8HZeDRC/bwdaZRp8iQPHmhreE9dYUXnrUps9uW7Mzo/FBvP"
    "xlOamwHMTnKrK6VOZTA6XlCBeITiMHF/0NEMbAPBR6G82m/DXAsa4Cl3DNsDwPhXaY77RNSoLtlnt0imaLozGV7iqSC5I4oQ6/PJ"
    "kgVSTLxCiKLJDOZ9G1aELxj350HUr5JQI0tTHjyIHj7cQVnmGH20w2/WxDaaefgwJSnjtDyG9qfoxZcGaLm7iNAl+i4S815kO49Q"
    "Y1oPqSRi5Kz6gwfpri3ndEuUd90c1uU5hDkuf/8o7Lmf0TBPhGVNRmzi5/NO9CgkbEOvSEJOpCQhc5je+Xcyf2f+8GFZedmRhDQ9"
    "mh+XUXw4F35CtHwl4EJ+gqqs0W0OCJGcqw12YxrBJV2EbfIvfBjQAvA7b5GHAPv6uZ4vQGo/61LLNXcX19Q17MiLfDHsv5us7krf"
    "kj+zNzIeWN2feQ3/zB5f4wX+IBmt8NUob/mxrOdz8+RWU9KAz4TxOcoRVvZmSBsUlPvz6JQszYuXT8slMpAW4gbUO3zvcHu+xlnI"
    "sXHbz+JVDkoMkYk15lULqkQrRi3H2j5bBeUvscYb/9a2ucftbF6Q5wj0zX7pDdkYYMyuZaC47V62DXLqAGCg+Cc34pDPFyiDL9Uk"
    "V1TNiJNEbbSQXuXZxhU82VWlQ8M1qmsxldNEsX+YrEgrLt/QK098U5c58ef4s+HKB/oKvGKxvH6xhXvjYscS5sF3fd1f5T0iSHdT"
    "rwcJ5a9+Y5cAT+EKn3UIsCv8ARCVKFdcR8laLLLIM8mWBXZZZk3XHZPolrXwJfZ4Mjg6DlJ6QTFZXiptMdky07q2ltHXVEzvO3DJ"
    "W9ouVNSr07N9OzsYU+AN5HHmlUWpvLNdAlayAiCV6UFzR8Z3GIsoOdMMOxcFrqo5Qv8rcJKAL/2pZIR0+Ip5JaYHcvHAOa+clMqS"
    "UTpSjjEoAIQS4646uYQ49pUlVsO7IfqvQP236N3YRRVz4WzBnfRcYY3LsDeQLhndz0q/XjpQl+Chu4jdau9RKOMjuD7qM2iEAxWN"
    "GDKuXY9wwJJt+fLWlW9sh9rTGEHtqWbAQmz2thwRcZ9KhuPx9OMRNcvxuWJluR18cJt3AOv6kGlFXQhihFRe3EL7LvzSEmNmd+Qq"
    "EKTXleL7JVC5mK6QabYFPzyPp9PUhqdwHre1iw5rIcpy1DufPZyH6w5HkJZndE3K8XftpU4Yqy3rV2aRfZdN2N2zokCJllIASj18"
    "uLQc78g360fK32HVFV/vCZvSLwTsdj60sSPscEuKi7Ialh6C66xDSXUO9le45DD9avy8nn7Wz9+SftbPtn7WH9+yMsc/vowyxx/r"
    "KHP8526VOf74Ksoc/8kqc/z7DpU5/m0oc/zmVeb4eYUyx29amePnO1fm+PnrK3P80/SrcRzcx2QquEWPJZ8wMZKfLYsjspYnvnXg"
    "WCJlcx6JFwHYVpfQbXwI3Y5H8Cs9tOBJ7OTcSmo6Pj7MD1luuM1YeNxmDNn3hoqmphUAK6SeoD1lzAd+tX4q9jxeLKLTmDwwoB8D"
    "nIcl+j3Gdxm7RDk4eqZ8QLj+HATjsAyAdP3D5wEBjZyHwtWBp3ntVCOpqIdacySstO18kiZXS0stOmzBhDu+K36RJe0O6BjnxwxU"
    "AM9/6UCzmXwO1DfZVdfYxyiPa0pv77pL40XetxRu/ZzF8DJIGy2K04KxLB4WdjfHfrG6wn5RWxNW8z1w2MJxdsRh53kNCy3bSHP+"
    "bBgcTLMs+VCj1/pEaMLfM2a4N21DmQsq+V3kuQoYFoFxsRmgr/ZqW0Bnwda2BcxOrGOlRoavPojyDQWnaxoKrujZNhDMm5YVVoKO"
    "ucz6VoLrTMx27szkmRAu1jQh3GRqsqaDphGRF8MNcpn1bMSSmkiL6DP+Jvj4FX6Fgn/uZzrd9lKZ62vffBUdcFFFy+uUoyIlBgwk"
    "o8CZUshkkN1cRwdCarSrHR+wGpEmaGEhQTM8FMlUjpOiffFUJi2uc5uUD2+qVZmR0/Ce5mCKvSlZz2yqdZ2V0/5r8QZW7F7JeFFT"
    "TcuMlW6bmgUm6Oajm2q5yH/TEcpBT9AQHddWPI1BJ61C4NVTm+pD5eQtqHw8g7bbxSsqH+P0ksqcgrbx7Qya7qxsGl/irJYxo6Bh"
    "ejeDlrsrW6Z3OKtpyilom/EkrK5s2sQTkc5tdjrDNsMVbU5nRoPTma81wS+5GkbMN6ECueG1i0jIPYP8OX4N5C3jXm9726EmHg8I"
    "hgOXewVXkHvkGyWjRLpk33RIUZFFIAr1uzJ5XOhw26kM7z2VtwfJVlCdI5vnlXcNuJnuKl8aRHctk/JUOk6BXYdeot2PQjh2fT1X"
    "anYZ516pjmpszCgT7blWqDKmye9/SrqVS3K1kHbRxNWjAyRDdGgtWG1LrwK/+s3rzbcCSzk1Mf2eFyqHlqb9VNmhChdvDx5MlRvE"
    "pOjljeG2QhzbPNfo4eDt4KGeWEjS5wUFrTe8LmX0RJ040WPnydpV+c6wellN7yzPk1GwzVgPO0/atIt1OvtwTQ4BrSzrbV4dP5hy"
    "H66prpHhe502y8jM7BO0VYrNn+13ZsfRgfOY7BjNZ16MM2bX3mdhLJXJXcuV0kBsUWklLZGHH2zURtSbryK2mNojEvvNXVCEx5ab"
    "GsJH2+mGi1wZTMpYnVt4kkEKEw2cVfcscGY17dWzV8tdG98qqKmHWR9UFrMJPtdX8PZts+pA3WvNlmCi7++b/LMlIJE72rkELtgv"
    "nbFtfZx0LRiPNqIazrXkQH0p54gzjBK3Llkym/e6a/VM0+dfaFIWOgXxYd6a0P3phB4JbyZu4gdG34LVveImLp+7BlaZLy5S4o5W"
    "rIcxRZ+/Ismhe8Xky+7yJ+X2YHxIMvLoUBoHkhUgsjp/mQf+15kH/mXd95d1n8+6b6waXa9wsT3Z2lZ+0uZjPRO/TQwB9YC8BmK3"
    "YQr4l3Xf/xzrvlwbPM/rEffZu1pSqNtLinzsxjlWZFDocnHct8cy1w4AJyPQ6enTanK57IuvWQtSuwcZeu5/BKjK4A4YH0bfAvMQ"
    "qfWXMf/rpXLQOYPJTAUG/KYbQiWdzvr3ddi8nAitZQ4aF6w7tqwi1Rp97Fjzm8FDAlUE1/uyKsYBCeXikzxTpvzYXtQg1OTwgil5"
    "D/qCZj9KUfOpVnz1AC1smiyNVYGsKp2xdkr6VXSF4ytE7nGypk9W0aPkmNR/E8cOKhXqospKPUf7y2rMo/VqHcCerEIjWanoqmoo"
    "l1PTky06YXZtRVhjflmbtFc09rLWipXDJN/UxgFeMGrfCb7r6c5XrswkXmvIjxevbI8Eq9Sf+9Jvksf8Tg8wB3tQy9nvGSCvW0Vd"
    "d69SFLavpABLY4uKDVzYw4q9KmInLgO4XpIGTF6QQeklTNnxGixAKfbaBZflVML3OOfjrjQtN6ZiKQ7pF54xvZmUrs6QUWRjYTFd"
    "0lw4o5Mubik9+/wjW++s8ijeZX7ah09T1DHitwJTxWhxmBvMR7rBKdvC/0H6jm6/b0oA/wnctgVhtQQMXMaQK9BtZ6AeW92Vls8Y"
    "+EJC06TEEKK3qOIsplA6MTWAptLvPV/RxFd169MPHJoZNEQLazqMpzaV83f0zKha8HqANx5apIoRvrWw3YXCBZh9hQ7WYEh8wlwE"
    "FVJvInMh7RgrL//cZHa0OaE3rDniq5+IaK6ueomks/pJRTxfSBJYmpdd9yhYwqZPzo3Jfd4y70DWe5XXAYoDgEODER7rAm5L0axL"
    "d2JqaXuv1V51A327SpQagb5PJUqPwPsy5LkxJR5ewbyLJAYVua0XFPMWbUt/PQKDJGuFYd3hEtN+xL23JY7ZSs7eW/2mU/igVcm9"
    "NLFde+F7WMGNq6Dhgpc731kZeTX5bK8scJ6MRzkOWOBbBJnqoY0eDE4N43BXV07zo3GunXhqW4G72in+JqTgMjVMu/2qKDn1tbAz"
    "tey1h94IXjmNmCLS1DLC9umW5DSixaqpYY9tapGsakFJYlPLyNqrI5LThCG+TU3bY78ySN6capmv1YhX66OgDZYTW0349TsK2hDC"
    "ZasRryJHQRv2ovh1NnKrowQ7dQysoXZtPZSwtobxjAwtrMZMS1Ke+qykoZmVuJmRsKdZi2loZyWGunL51G89DU211m9KS/RTnyU1"
    "NNbeoDEh108zVtXQzlpYmxme+SgOjXTXbmRho601plp17WbsIWWf2KGxlXjstcLGBjd6ieeXd7aeUJZs6vmdGD9m+CSbp1/pbZ7O"
    "ZthMFs2nXmRxXJYzFw83pVgoxTdpfYAsX2SwQmu87htsjceQ1GBaHB7FfP51NASK1BFyWQVLocHDBtjP6H7NmtzX/2U5CGsd8aA5"
    "PSwvo0P5drngt8uhers0XlhXPl6KJzWhcHUzh5vFDuIW64qjfYElLbns+uLiGzRV7D/N9J5m9CBdJuT7UcMrd//K8Jom9GbYd9qN"
    "fawFPp9krL+8QNdVpXSFWAO+rxBrpBVsCQ2cAZPHo8k4AWa+VEpWNIze14sbTipWm2X2c7a207h5vtO4ecZpnF4bxAV0GDcvW0tm"
    "LbMr29UrpeR7Ogt62fVlSsfmgQ/TfEbhPmT1f40m49PksShCuoZsBibk9NUg7f+mZfXB4MgXw7V/L51fxveOWc5divsHUKX8EJZs"
    "ET+eTKO0lPL7wtEA0DLGUxfX6RHyanCgVcvydcUQ7lHBp1TuIBlJST/6ILvSXtrT0QagsZv6A7zpm6DNvaAxS7wGcKQ93U8YvKUl"
    "bbUjFWdx4ii7VkxmyZLCMloXUkrrw0dVnhRfjnkH64jJOW5Qsv0JqWeQdc02WPAnj2m7jVy7R2kQZ+bpuIfZx0vTwnxyuJaF+eTw"
    "G7IwpzFrE9vLw2/Ywnx0+EUszGHOVluYnxzeqYW5CdPdWZjLQRoW5rPDu7Mwnx3ql8SLQ5+F+eSw2ML84lBZmNPGuFMLc+jxa1uY"
    "n5k224GyF1Am4db5Zb64nDovLs7jCutXyncS+yxQ5mv2mWTGmA9c/Vj5MsaAlpXJQybMH38Hbv2wBP+tHaPePLwMe5fbjQ5/Yui1"
    "+kNtKpVQYa5qhwY2A2eKBTF1cCPPcWqEprVMPm3jU64nVWQzc2Z/LgcYeMvXFdzh2q6N+hnc5YbqLnd6qDHo7eGXjz31/vCv2FP/"
    "f4s99f5w7dhTnw6/rdhTYjzZ2FPiwxeKPYWl39mq5YJYbCafIYlSvmajrffsk+Issb3345FH5eLq/pxckLP3UKZY9NJ3XzZrfWLi"
    "tyiKC6Db6CXxh63/nJYYsAFqG8CZ4DTlFOLcAek7vIthzuNfE5IcZYQ9Zk+V4SSO5lIB0OlBfvwsZ/m0Bjke87XcximOHwCoWxD3"
    "8OSIA8V8P5aCj9eIWUJ5QoptLQWVfEELwWpLWxjjfH76zcJpvtzFGr921+9+LJbBUDlLBMO9Z0UzRr4jn7G/KCENq11Y68n8Op+C"
    "Yk3j25bXJf51gC0IU5ou2XmmI+rSH71yLhwGeWiHj0rKJTK9t2g5fbGer9g7QY/1Rs5ZJnML7iIwJXfmg8xSKLtWow9JCnwSAc+G"
    "5q7g8DQaM2U6Z9Ei64uRD+Lt0HENSECV4UOVfefnOA4Epsz2wZooH6yp8MEKvFrGBytebYgF2vHI9eaB4hCvr+cGhzzPML5XBGDG"
    "K2tqe2VNTa+syFc5dOEra8i5Cmz6vaI3PDTFTx/XEz99/JbETx9t8dOrb1n8tPdlxE+v1hE/fbhb8dOrryJ++pAVP72+Q/HTa0P8"
    "dOAVP31cIX460HeVj3cufvr49cVP+1qd95Gmoaac6dCn2cu+Ak3Kqqc8qqhjUVsQ4/GS47eNv0lXdUDKjTxH73cZJOZpugv7e49k"
    "TFLJl7uJXD7VFjcJDluJonqramtxlJ6ie+g8I84/tKb96YpDa2oqZKrQ8zroPINjyrZ40K4mcIiawDQ8zUfBrBveV5KMdFAbdCeW"
    "zTaqYgMLNKcwhO7sKhZMie+Is0VnKzST0E/Z6xLGAE4wVrApHfcwjmOYz/H3Ql7q7I/Sp/KuFI31lMczW9KXCj2ExKOyLUR+0vpb"
    "qmZLbwlKfUIlel5/jR4beWtm1/Wpk9zmpCWfN2kFk5U3SSyd3DedGCzfKTnloSGnPF+PSzv/lri0c5tL++Fb5tJ+/zJc2g/rcGnP"
    "75ZL++GrcGnPs1zaL3fIpf1icGkvvFza+Qou7YXm0s7vnEs7//pc2mMl2+Xz8zFt0fU9h/CW1o42RJp2JSRxyZEa6gIXePG/mI5i"
    "wzkH0bNonKSPotHIzpjHF9P3RsMkB0X/2NiBUPRX3jXozClyB0Bf/A4AUHgAx+ZovJhNok9FjaAKWJE7BOBvaJCrfBNgO4difopC"
    "Np+h/imMmrU8V5T8AedlrZLPJYyLVU2ORisbVAOWYpp8twkX0cc9tb4Lv1pmDY2Mcb2FrbYoJV15ZLyCYFFWV30tFGPXqcF84yY1"
    "aB02qUDLsUkF1AveqIPRaNMqL2lLbVqLhr5ppUI3EqLIK0D/eHU53HGmyxDvltJFV/gOEZOdzC4tdxe5JbMONXIfsUQi520JzVeA"
    "vrwZL8Z0roWyDbUdrZYVfRBvYKI6l0G3r2wXBc1cSO+tr4FdiVPh1ZeLUxjCZ+MFUO+Ym1rxLuWr9+BBv/TiQ2V6clIaiO/K0Cqv"
    "DvttLlsF4Lx8OxLvWWa+LJUccvrJeBSX8C3Ao3QtJdEChcQ7ikgdiQScBceWRqLn+05ckUfUrghg6yyHevMlcnVUPa4oWheYFeRK"
    "9XWL5Z6/xTxgdMtL20eHR0dbs+zA496+kvYSOZR11ZqTfLXmZA215uTO1JoBCuZv9AHki7ntviicjU/PJqiujFYtol8y8VVLqoyN"
    "Y34qKdNLAaI495d9xPmdxB8mJpR3YgsZNF7a+QY2kpXFMC6FMI3eun0fhga57QF29yVnjkRCszFeRAaW3IGN6vbZ66wfs/velspW"
    "rFCL1fN/UmEffV+Z+RSfzoiMLAPKzK6GWd3kKQPBTOpBBMZE9fK28HJ9gFCUmQHHIWx0NvpoGH2wCBmpxKj3UYU8MkIbd/XjJErO"
    "SxmKxjjb85cVCK3j2AHggPtZ2M2d6pkaHS3ObD+XFopuA6u4V1qi1F4yukAoLIFfF6Wy8hRSvb6OM25XsJwqALuSLCwzDlPMw0qc"
    "3yLsrZ2Jord5jMfgPqN5SbiV19E7fDGVFx/G9CQKiwMb4moYLeLBQYKXsR79BhZ5Fo3MnFezaBgPGBc1zChwoVfWHW5iMYxmspQL"
    "PXptYZtguRM9wVf5eu0jWGnOHo+tTZC98WX3lqY08bJwx6frbzB7YL4p55EBjhDLtONbAcCP6QeKYtQzIqGih55f4GzAeK6kQIV6"
    "VhW+qyrDuJKO50ROVKN3HJNzUIVzsXIyHV4uSuxj1MEWc/mo/19n3Ptc9/4C6sje5yt7n9u9z4t6XwofQpnDLVe1oZCV6fdRERC4"
    "OkGRPgPB1KkWb4AhGQlEFvlkEY17zk1a+Ljx4hyODbdd/g6yWTV3iEnuYZze2paSkWtvNLxoNNLs0lqMTJBuxEXs5PM3FFXYWVBX"
    "WlR0UOshF/MPG00IbzTfnBThcgCkYxUfFwehcEeXHasUhBUON1mPeG40XHH9jyaTd9HwPI93ytbSFNJLc1GZ2PbEp4y/dp9c4iOR"
    "827JZoPcjzF3MdxxSGF810eZe/R6RLcg0Rnbk4vEHuooMbCSoHqB9bsOvDWADWLuAXgSufCeOWqw/rNdrzXSJ17qBw/eSCvLeXwC"
    "zBiaod+PJzqwTsKxcbKcj5I2oHb3C7TOJ/JqSwKupvPxKapykRgAKA8frRb3oaiQbjA0uldhaDIjNCGgI0VIHBKLEbWcJu4Ye1CJ"
    "hR48eH1piR4CX6ly8Ba9DOgxDqTl4X2UuMfvyWcBvldU/uQ4AkqQAc3HwdVMGs4OoncLuJGSQwq43MIJDFMw8YHgLApn4il+eJku"
    "YNFp9FK4UjK+s0G/78vLGG2h3S8+YU3fWnLg081O6W7Li4nmF6m1GIA9KBlKNhAMGev3wwkKehPfNXlHavDJqbU194iLgW01U/lx"
    "JbpMp4+ZuzH6oDA+2S1jy5pcmJxKMCtKcBWbhZ/4tuNlsmrduIR/ffibf1XFXPA1e3OJXP76s+BSfHIdkVpdx8gj2ujhpZvDyXSB"
    "9gvSZlrRxv69WZTEk3vHwVb2k+iFjalF6G++ObJsUyGkdIygJIvb1p5CN2/RRfwLMBlkNGR9EwZq+D5dxqspjshqPpfd1ZsU+e7s"
    "tvV26xQxe18GeZiSExicx+EpjxvT+KYoaXaHpxjK3BEZ93/FUywWx0FuJ1YjzNdmmtrdNdrayfbEEiLnyIJViDVZwTt5hgShC9BS"
    "nD3q0MVf+hqIMgBsBlWLnUMGKdUIiAOdq8A9WvgPbLXh6KpoHskkr6AdaxN6phDrk6ucdRY+txWYCgUDc4e3MhxvU+uMqLgTXvN8"
    "rNKfvciS4RjEtrFJZNGGYZW4J1EymuBO6aPNzuNT3wYOLAxykTSWAgbLVbdo13sYy5XOhzXbkHR1azXuPxV4IuxzpGgi5lZJSTPs"
    "3H7hFGyPRqWyMRPBBwBg+sGzE7hVgTh2F3oH5IPuqYbPUKI7L6YW9civUZadhc0e5zoMFqUkwRdaAtsiZpqg8SiAxKx3/EBOsgGe"
    "uaejvJbvjzEqkeQwjYf0Rc4SmpXdV3d51rj8qeBsndJHCmgUNMw8allXE9SLQ8+ObouT6TCaoD6OsI5Nl0uS1b6yFQtyBu1OlER2"
    "q7LI1BOyVIIajy2I8HQiIPZPAwPNLf4ANIVBf3VS+eGX/WWwftXkk656+HJ5vAySKQupn1ETeUvtb3S3sEfZsnrD4jlW78IFCCvL"
    "5L+OKomantoNBPpGbcowtTo2aMW4Gl9fH+UVO2ZdFK27kN+FDYoQ7H8fSsHNy0sphb/91dI9qPUCmvglexTNO+jxQ57MzsURpduz"
    "BpKoIvYE52SLef9ObGJT50c8jX6pKaHG9fxrOdcXmH1sXHU1NDTouMcf5uMo06tptqYt1LwdqMCZMYUS3PUIelYACLXolH6shBu9"
    "1RUQM4wKcnyMHJKseMf22TNq9+F0jZj+Jbs19oyhMsCKZY+1FtSLaB5deGicqTGA+u080+ZzaYkUA5QaAs7u6sYclSHfi2M0RP1P"
    "1Z/RmW2wyE85venrQPA7/wheTOdpNOn98SngWq8m0eKsN90XSfh30hvLVC/ZD17PscDlfvBicrnoDfdRZ3IeEwCogilFMr2fP5n2"
    "kE/X07R/+i1p2j+1Ne2ffcua9i+/jKb9s3U07f+8W037Z19F0/7PrKb9j3eoaf+joWn/xqtp/3SFpv0brWn/9M417Z9+fU37J2gP"
    "OUb1djxjH11MR9FkcBz8itnTZE/E0iTdEBEqUz3gGzaT/8qLhsIEHY0dMcWEHlJDTDGNh9SkH43RJkzQ6EzglNH4PQdPNYwomZR4"
    "XEfJD2RGKG7EMoq4Ms+ULWaNMy0F7z3pLgz7AVrykh5Qk4qrp1v2A5FtxQnPahUry0fURLygivsxXDInvUTxwOLrsfsCGlXsDMM0"
    "jY3epLECNahSsriM7Wq797LlEDpejPLphZFsBiihGgT3CIHouqr9lnnZTlEUWILZdHY5Q9PP+WUsW5BOne/1xi5DwQWGInR1tsBu"
    "VNGiDd551uLOhnsZqAD/fM7BBe5nwkMYjott7SZ8edFBEMLcSl6VK6xvYJiDTV6w2WzX5djoXMwoh4sc9DMndcP3S1kxRQYzTcX6"
    "6+tSZHJxuwPNig16IoHb7mNcehKVvBsC4cQ2aSMQepJd5LIcvEWr3rAFyKqxSNIkiRAyLdcfTXLIJawRPshyT/eyNOReCkf9svSc"
    "EJrsjeLKbJjAjD+KkuHZdB6PHkkhWBmd0tNzYFSxH3nhg/FYaHzVuVCEn+2Mr5Qh62a+6twMOgCNTPgNd7BqRTMb5Oek5KeBHJJK"
    "v7JhnHJjN4mtR8eDZ2Oyie9oHE2mpzJm+ZFJUA/VLCYVx3Li2N44tN3OF9nBbPGVEUN441/B+EWB4s5gCx4NYlYsPC4bO9iJf2Ft"
    "RlO7AJu2c7ydoDd/HavECY/ha1y9OlgdqFxfJznHmppG3zlimxp9/eMkyD9/LyeFx6++8aKQPPeQd4vl2OJrWa1+QkkyJviDyVj7"
    "CKgQASqEbBBcaRUy1HCS+JZD9bPqrDKamXV0HLnBgPJbMc6OADbMvrFnNuj6aCBULXHPwP4hTd5j4AUkn9fDS2Z1d1AdCBsiy2fC"
    "ioWxjqmMfUOJHCi8Lon5Rm+ewHkqs/ngmVqVopV4pXSXViOKUVafQGv2MzBpSj13kQwDi5K7tI0bLK2IqFSwwk6PeSu6erGEp1Xr"
    "3YBcrArOsGQ5XgjJhYIt+V+bw5YVctdMF4BBvEQXDFPxvhJVnBeXAHVOJ2/oRqk/ugxpjpxQwPahJFnEx1Y5DKFEFx8AgwFgMd9A"
    "sCicx30PaE8BHztNfqVQBT0N2L1MWCt79W1FZFr4nJg1GeYwD2CDZIupQ0NnBZFkpySvleGlhCsL91bwrOhChrLQQpqtC+RQa1di"
    "X+Q2xcKyeeAHB0FZTbK4ZFljtH7y23W9gGhENI4WAwdTwxjPj116fDfCLx9iW1LoHBTMwT2PongJ43psioK+Ua1GQol3FjJ6wPdG"
    "CVVYafEawERdDnYLLtp8ec3nj9JV7JBluBVVjNSmjJJwGiDuT8fZ+7d+XPQS11qwGrdZSZsJKd112OnpO3GTtK/Ij406+o0QDj8H"
    "7bzvlsVckKujXsrBMWfD+m60s+kM7yAGFMFVPmZmR7Pc9C6ctU+/vh7QqwNMDcf0zVuFfChIuSf3KpyzM6RQbgWhtjwzUSKQtM16"
    "iLWxCm7vUriTg03qcdaRa62NWj+Yb88WU9XOPSAtc49SHtYUIYp4ki7CEgewjVHE8XoA+IGPUYMckUhOr4wSBk4Ef5YGW4OHyJhl"
    "X+1heXOQ5rOOce7hXZTPnhklYO235RRYrigwIoHjJyQjQqwGqxHGqG+hS2ddHnxjZKH6RahigbQKUf4sUfwCR7tg/aVTfsg0qlnz"
    "vMaBts6F35i0m932HQOeXfu6UFsGR2qnmA5Isge19fmWRvcZR7SxAhvhrTEXFt5288mcBvJmRA7rF5I4E6T18NZVVdkAb8kJnnMi"
    "cV6QWXPb7c1/x2NI8OQQqdvR5PjYGIU1dpQa06nMJtD4S4t9KfmMw/oOTEkvXce5GXFOP1aeAP/F0Sd/Ui6wWK4nw+Gu7wRL2Ncp"
    "P1QUHReDc5MnFxWqG1OGj5jgzOpubd86K32D+Lz633bsRjlEbpwTeqhSSZZSGwRITPM9iaRreBJJ78yTCAZNztgxW5ab0i7XNYiT"
    "E7dtztzScf5uIcZNNZ4MlTHRzRq6YhxH94fJZA01MaBCqrQMS2KpG9EIeq8/BHIovfPXplLQz3mP2WoLWg/UeChcGbf/RCHeO5jh"
    "+SfUY9C7TeGfe53KmV29pvR0QD/XvpY7lAMFIchdmsRenT5AS/N3vnlE55fSUaQENsVqKgwxCP4yxQKiiJIEmFdgRWuxoCUKkNPo"
    "uR5JB37ucbT8SdHYn5nG/qEj/BovKOvF+dVU1ok5fnfOB73eBj8/8HAApyD6VFYeFnIc7MGyUCzsgu+FfguFS+Bb9MlmBtAucshm"
    "xNYWxY7YJ6AoLU+44zvwz/ZXmGeXTcAIa0ZZqRWFs7Xz5VkIN/zzt8gn/BVI+X9SIGX0JS/k6wiKOKQKgyrDJfTMOMsUguplW3oC"
    "LJtqBKuiMB9zkKEMXJnYy2vETi6CQ0VnzonN7I26/DkNHmei6dhcVO+nw2D/tamQ1Xtsxdj5x3o65f/4lnTK/2HrlP/nW9Yp//eX"
    "0Sn/zzo65b/drU75f76KTvlvWZ3yf96hTvk/DZ3y+16d8n+s0Cm/r3XK/3HnOuX/+Po65fG5jrGTG845Pc+5ZbsEVyqP20RXO+Gw"
    "IwPLGB44gxXzPoCWvYvLd3wsYlTUinELgI9OgGGOE6JjGadnhjqLjDKdfwKqiNP5h/cyAEry7w0iRhsn+o0iRttfWEgyRmXGUcw8"
    "2wVcSsYzOAT1K41zoU8qzt3QlGzQZVDLK1zN6dQIlKjEUc7dGQODOiGo84QdbvgVJUUwJAMqJkuh4sA6cbRpCR1FEPkiEXl4jccy"
    "zowXrfjtwP6Eq4mbE77KWzNdkLVjf2f9LGtIqGW7pt9gWH5P9Rs0wIjpd1+/QTMcFMjr036DVvjpzufnfoNG+B3F4/t+gzZQ0pbj"
    "Dn8TSEYjoyGPk/wN2mLBkdFc1nv+phNtNLbQ7zK2wCax3ANnhShZexqP+MTz6gWkRpBWSXDCVQQn43lwqRohXOm52rf5bTieCLV3"
    "fx85UF/VPtWBA/LKyxuYFZAjjwZobclMZI5sFfs93Y3PkS1vv2M6UTpyqZIqIvtQATs8PchvUDYTtMM7QU4hqmdF8LBr2R/pNdZx"
    "/eqq9HpWPiO5Zfx5LsW3qqXGqpayEt9U+joUMMKM9ITmb+EJ6siJ3WaYYGR0T4tbkgJmboxW36+h42nG8lZ+0+Ocz0lyyKJM0Gwd"
    "Pq/Jg/cl2acw4VMz8Jg8+dV6cvXBKjlEVZI/iwxmaF6u1ZaiHa7hjOVOxVW0cZUxHDc2tpuNjMsexzWGPAHkgsFaDcg7LCx4BbW/"
    "rCf+ID43Y9z9oV5d0nO+8pw7L9ubvbcQKBLDZNJwKiazRvPolMVvVhbqSdg5E/FAr7KmM51iX02qna/32LNOpKlbePuh8eLky8jh"
    "+Y87N31FWUznaf4LzWABKVh73f4rKP/YiKF1tEb7m5Y/nAMiFs0L3Y0QkudxGhXEkbq9tzNe8P3Vkb9uPajRnolGPtDm8RTnaz00"
    "+evR7C4ezUhehdKUO30co70TKf8vFlsnvrBoQTqj85egZqSCznjBA3xFeXDhViSpp73nGagXIIHulVLpsignPjF8XxGfOK1gS8Sr"
    "/jQfj/BVZtErlZIVDSf9ZEXDfPiqNsvX1xjiYu1nxXn+s+J8jWfF+V2qH/mddCsW0zy6szpInkcqYT+XiZEhwmEgarGmHTpZljlm"
    "TBIznyOTkIvI4eUcF4x9eVYSKIC8BxZ6/WTw4MGTy5JTJlBBwwXWSpFmWbnbvfEgPeEutJlxZuiezgzuZ+1Z3QfOhx4dVzVu8FEb"
    "NY62yuu0zQzZRk1nXWDntC1Yuw0adwixt13kD9dukt2IrjXTFq8piP1zk+8gh+7reOA0K5Evf6rpeyRLWYMW46H4JJVAtnMKKC4L"
    "hcsE6o/R6DRmHTgviBXvcEplC3SDqRQkyMgBIKwsxRnClv7+Ubgb9+KHIXobVN3EuS5OJRdqCb4tqueeUhIe/yigf+zZPLvW6Vpw"
    "u7vqgxhPyc6QI/cv0cqixmKV5SlrzJHmbv7SCflv1QlByMZ9CZITjMMTtgRWZMxTHfX/o6e5vDNWgtyj6BjgttJFAPddWP3FgtUN"
    "0uKsao4KkWfCaWK/CK5UcnYu6bGtxzyUdmub6NCUzWgcvMl311GgyTLGZ+vq1yg4Mzo1mch76wAk5M95ACm9mH6eZszOGqo8MhiJ"
    "o5ATxMd8z35Fd4vMUDAsDLHMO5KQeGhkWQz5TqgkwBNroszigeoO0ogtH4jqBJFaH4UHXgKHBRGz7aqcb+vIPkqOK3TDlq/uV+KC"
    "FBvCinS5VNcvXn/XAbGBJmrucVwVbi1IxE9qT4cNAjqbfF/dPd3v4a/vqrsX+3Tr7p3sLwNUtkYwVx0N+ti8KRzc92AUL4ZAClDd"
    "oCcgG0Q6a5BMk3iwNHREHf0t4kp6h2+DtRS5AhzbDxMY3j7/JPnBrzPMOjWziC2/2DcVv+bnayl+zc+/IcUvGrPWfBmff8OKX9H5"
    "F1H8gjlbrfg1Pb9TxS8TprtT/JKDNBS/Fud3p/i1ONeKX8Nzn+LX/LxY8Wt4rhS/aGPcqeIX9Pi1Fb8mqPil/IPSG8piFuGbDEAg"
    "fpG1DlL7Qa5IRX1Qor7MFz45dFq+jjjFbO0zo10lv/Zopl3maabRUaLV0TJqasMCNbUtW49soVQFTB5PaY3ZLKp2xRXlnLHKO5fw"
    "xMelhK5bIJbBqS0XpxyIxXG+yyWTjj+wN1QvkxxAriG+7QLPcKxX4FFPOwDs5rclBIHcmkis46Gvmt+k45qv0CefED7RNWeFV0El"
    "XONmVbKgWRSDrXAnKKVqutFDZfTtbZPEX9hovbhRkqfpVimZ2+x0hi02ilqczmRj01mOd8PzEvz3uaqPDuG4l7s/gns5FOVeL8k+"
    "KNyziAy2mnmTuOejO/eUlhKXDjZS0TRgdKkTQ+m+uS3JxbEL/YMH2/72lSorE2KvbzauxyLLOWnJmBupYB8ZUk5eeiNjLf+WTs+G"
    "/5OVLkuGpmYt+9b0uC3xlqIZXEPjjfHPtIL1l9AWsLbWi6moKs4b29FT9j6et2ChZ8Fej1P2c+Yds/jKvv18HZGLv1xwjFPGBki7"
    "CqpleqYD3nV3vcZEYz3UKUTF2ezllhwtiatwpO+S8h6p78buR8q1Jg5z2RWxF/YxeymWWAjrpjgO1Z5psZx1ne0IWB2V6nrGMRwW"
    "FAxG2WvMbRQQgZ6oiJa6Q/v0FDpYXABfODBxTjjomCHTxU7kCvCvSDMc18xSTNi2XLsq3ehGgcq4ZdHuk+xllcoLfFJssH+lYJCU"
    "Vj9XzdwwNDc0zvMBXVsd3Zpe5c3OM6rViupDXozmF1dUJxD/0lT/S1P9L031vzTV/9JU/0tT/S9N9b801f/7NdVZXX1yXl4m51JJ"
    "/ZKV1EdKSZ1U0Z8IUdpfWuq3paVOhrn5usBDS6/YU+BL+/rZQBH+9nS+v2nV+K+h0L6hpvp8kfpHWv1SeuywJ96PRx6PKVf3UQAv"
    "fBa+5YsLYllwX24N65OUCeZqxptt9DDK/H9OpbPml+iHC25zdlNOIc4dkE/Ad/EJzPuvCb2EZ/ThzZ7YqWxJ6Lk4PciPq/Thg9TU"
    "iI/psFbCESICfmV4SxXeqYAfAKxb0Inn6ZFvLYvhfDqZ0DPj7aikq/aKNMZpTLbaONPXxKM7bhZO8hXIrXmKoWR21mmaCpXJqZyl"
    "Vcm9Z3XMjXxH0dz+orTNARbAMGvl+fGYX0fF2se3bfyQ+NcBNitMaYrzDz8dnX390auwj8NA3j+Gj0pdX2R6VTrk9MV6vmLvBHlM"
    "Rb7iHCnThXS1dUO6hnWDNV97hZY060/ZSldb8Xq+tmKPh604WMvHVhxs6GXLBSm3xzznV6TrINxfYY9P9FGRs71NIr+L61Jyd2yQ"
    "2cJSLFM2+pCHjU+tyXNkcFdxEBuNmbqdgCr0Li9v5DkBznUYa5NexyvoddyPV9Dr2KLXeZ7EAE96yXmw/9r1Otr7w/IkdrKeQtnJ"
    "t6RQdmIrlM2+ZYWyiy+jUDZbR6Hs7G4VymZfRaHsLKtQdnqHCmWnhkLZW69C2ckKhbK3WqHs5M4Vyk6+vkLZe8OTmKasprLWJ5+y"
    "lqOhxfr7Qjsr4+k5q6EF3zJKBpxbFq6/gM4beaxzBXNC13J8eDWPvV3Y5hek6xIzjyM6oMCI5mFlq72Ie41Siemtqm2oxaiZutcr"
    "TXMPLTjRpv3pihNtapxoUkNl+GjBD8QYuZnAWRqKFDxoI7SbjCb0O0fA0bwFzLeiALB8bnC3dK6UHsZ6jgdOcCh3dhVbotSI6JYA"
    "HfBMQj95oedcpgTQvwhAMTJLfD+XIrmf40+ZV9V5oK0RxsvgaNv9ejvO63Q3ZXVUzxW/tK33nBvXTnLkJJfHnyqA7hrSfVPeKWX7"
    "mGdp4rXWbMcQlNJl35DhWUP3CMKSrHWgFqslymjDEIUl2irEEHglhuKILeFKbGONjPgvq/HAYj/TQ55lyAQT076Rq7y850wpY3OU"
    "Cb7aY2fnFl47w+6mz52eh7Na9dZezmrhbT2d1Wq39nZWq9/O41mtsfHr2Zr6M1IFxtjERkptWaFnRRpIgWGYZatfWfsQnxvsfQc5"
    "tOPUu8RC/RI7Qn+hTaCSGudVloHhhRo8FN/ICrsnE71S9mCrWgeb7wjznFTypF38Dz+d8g8gFiONMwdR9ZbOoZsdQ7IpUwu8tmZT"
    "xjuf25TQ/K5v0BI/D7oNSXXvxgYtiWdFuylS8W6u3Qq+RN7GMe15rPHpPWef5jw63HIwL/XL6Hq6Bdn3VBzafz0H8S0xEPwOh1/g"
    "b5aduA1u4jaYifD2mInw1piJ8PaYifCWmInwizMT0t5sNVORpSaUaROP/3bmg/bFhkyIV7NYK27bXEntL65EKU97uJJNybXtz/u/"
    "Rge11rwNJdTWbVzL2rd3Levc2rWse2uUtF69HUpaDzempB5WoV67Ea9wQ5q8Pln8kncwx0Pt+/PycqRU/j6xyt87FDbHH2cRZI5M"
    "GfPH9d7hPn5L73Af7Xe4V/ohImYBsXgOuFry4wPK3/t75+rxYPXDXLTyYQ5fxub96s78u0i+hs0fPiwn/ehofhyk7ILy8KSUoI0S"
    "elS5WtKTPjbzdHGg3m7ks0aCh8T4KDnux/CPejAa62HurRpmH37IB7v5Fj4jlaEs9HsWLYxByB7nwjWWAhUfVADUMr4/j5PLeCeB"
    "oQA482PP++CHb/nx8/WXefz8sM7j58HdPn5++CqPnwfZx8/9O3z83DcePw+9j58fVzx+HurN+PHOHz8/ft3HTzUJ5+eW/uNznIjr"
    "69859/r6qfzxw3nJqIWpqwykTxOAAsYcpSmewVvpdGsU8xlxOY+3kmnyiM4lWNUtqQNW+V9Pky26M2Hxd/BBlAiofIR6vls8SQse"
    "/FkEw422jpyT7rhU3mI1T5wFBenvFo0TRHeX3E15ljPOtHp9HR/BEsg0HNuweMk2025eWnwYDvBN+Og4GKLLrUl/G6jN/BNiVtQn"
    "B7689rA70ZNekAJ2VMtIm3a2S8M+EMiIS+D+HU2TGA+SBRG50rxCS1sOJNGCuoBC2FF5ZzlEZhM3wgQ7Hvdhg6DT0MmnK9H/9hDt"
    "1kQoK4Iamp72ZRbcRATpmCLKTssCEVUz0MSkzCs9XkoqsFjqCSaMwWKkkl0ZL+gvjjVLMn6xFuPm87+deHskZ8mIsWV0x1a+SsgH"
    "WlLe4R2I82Poa0kVwqsFXLkSjx7a/Pt+LOZ89wpXBUlRT/wKhY00HK0PH2JMR9dfIM4Y6hv1YNrW2Sk8wrvdJcQmBVNEnQXirJoQ"
    "YzIM7F0GHvdvCaG09rKK+gA4RUCrnTlZYD9RnybF1OkGRJ3i9ZkbkLoDGkNNXFwIXIxQ+03h1Ytzg299ySTsGf95yn8eW+Tr8brk"
    "azGbw/X+61CupwavyFyeYJ41YZdb7E/BF0sWEo4iJvly5SoLuLHFpU4ArKFcqARPCN78Lj/P55qZU0FbJWC8sM7zaIbiDvJ4HaeD"
    "Xd6GJ/PpBfTUo/wfJNsEBf/2f0u7vV/H10/LSQq/Otdh67peK8PPvUl0MYtHZW7h/t8qKZwWQAN3xXik2qyek2fn9lwU045tgUoO"
    "Bdk2Ge8tC3rd08tVZO1P+wIjQL7Cg5d7Tb+X1INceCtaUlYMPjuC5YZh9ZLv0p0EGNK5vEEot2C0UX9UFmMe07C3+8E4OYuBZ/oh"
    "TecLpE9sKsbuGMRFW8QL6JGATybQDKQyi/RXJZA0M0gqKTNs/8/4WfD3KCBj6QD9Gr2bcEI2JD0/0FdO0U+4anNCFBTqs2TwZ9UR"
    "H9AfgFXxEeC50Sgl9U85fOv1BR3A6hzayNSC/C1AkRd2sjZhECaTaLaIKcFfPWVJTEgVSCpo1eIcu6q0jCTdd4SQTCM5tUB3ScMY"
    "xhGPxui/dpwaSVQBnsSpWWKI9GmioIIsoAVqALoRlaIeVMquDnf4aPIyHsKsLExbxyLTIseESApu7xsaXM5HzisyL+JXG+GUFh9u"
    "Rm+1BRP+ggz9ZGZ7YxWfhGNTy+sqfML9+sr+bGVBEft9LetRdReOoGxuuQcs4eitkgvrBzqy1Hqr9sPPcOmWmTwf4omPs/QKmgVF"
    "LlvFwcS9lZJfVoyfwCHMstRFyXDluyirPnJNsAJ7VbzFfmJdRFSPh8l/Pb0cnsUjpDuAPGdTlOOzN3n2Gofbz84aTYd0RJjPqM/G"
    "CyBnatyeEgfJyC40iRYpf3pCcrN/iw4pi2sqRyD4wfADhVcigNf0DPV8+p4HAZkvmQ6g/fK/xqP0TNU3PjyJ0eW4AHcenZ7GIxHc"
    "JptlgSG+OFMC1+SZmwmTi2/vpwitMQICacHujimbLsuUa2SaZV8yTaHhkY+V6UsST+5FsHJc/APeJnpXvNMy7q/FFkQGbm5ZbugC"
    "mI/f9T70FNI+kmPTAjSnJH3EkvYu9ZS2CmANe9N6algFCBq5IXtX44sL2GA4k8C1wvExmnh7hYmEPWmH4zF3dYmcgxsk+HNaPrDo"
    "ADetjFlHcTwrblESiH6WQFBTJqV/RrxKrg9039nAftDzAiKNGVlPLiclFdJEHHP0QdpwZv3NmUX3DIQuSff2OLvSUTY+gYkqaga3"
    "xfBtMlo0s6pZsWjlVTaplwl60LQoFcbtWCjLVJSDTD+RfZQgBNpodWibqwaeg1GbsuZFibLnl884ONWtub2Tidrc1naavIgcf/ss"
    "16PAIwJZYfgH+sBDFljPlKBLgi+waBFxBjuGz/Qh3OjS+Fn056dn02hEq4Ry6oRY4D1cXKikfgecL7ICzxYQj+UmJGVfOYRjYMJm"
    "l8LmtbnsfbxTvwbOuWQusyxrsvTQJL5JDOPFIh7hrJSXhqqVtAN0oybp6SXn6FasGbiSSE55x+N5fR5kfK+P+0kl5ShGUT+n/GPL"
    "Tb73ZZxCSiBZWuA1UMbEUMYA/Xtci4/2OcbFEHexndKTy9I4P4ISoPt29fraLKRaZf9zXDIlR4ZrFBTu3oSXx8IKytkfl7Ljatyk"
    "zqYtZGfUnSAdZwQowBoLwKfIO3orFbUWo5JEATQKKD2/lJvTF4umlGEE+v1oV5D5i+l7hA1PZUmeNB/w/z0KZWAF4edAHfhWq8wC"
    "MF/k9kWX/16m5f6jsJdtwttVts3Iu+UNzR63Rm55of3jAqIPxzhFYlmScXZywgzBcgAdRqqOkrRhOp/Qz5KX8fFlZh7sTFtnGbEp"
    "WsojOBqNlDvK/8feu263bWQLg//PU1A6bh3gGKJJ2XESMjRbkZ2OO1bstuwkHX06BkRCEiQSYADQkkJxrXmIWWseZX7Mj1lr5k3m"
    "BeYVZl+qClVAASRlp8/5znRfLKKuu267du0rDdCxT0lJqcnWs2tWZFfetag7dj8LynRFsIsj2qJ1V5FChw230VoBpop9YNoim+ty"
    "vDizvWUTyytW4NXyTl16ehPa/tMb0bbZ8kQ7tWI34e3I9yexWeF6wOfgYTDzosGPVygGDUjYgVytqA0UT3/LCQZRG+afhRl96eI8"
    "YFFGP23DLnYS72f4f+VgwEoooUbUDonJJvm/7TOHmdbZ4MWkYDmzIqy2VQuhZOvVxEnZphsgpx94x+pj9jL6Nl4PqNwRC61cMQ2f"
    "bU/IM1jhCsg1LB1E5hrW76VS+ePOCZ9P1wgVUy3V36oDpAHGQcyKftD+luq/UooLFM2UtnVdtRPkOMPiO5KZUsEMvPop70TFHm1Y"
    "/pwZMmp7YabXweVNxfvQ9lTVfVj87IRWNIUxdHie4Rz87OSrCgXGlkWVmWjYsN673Wci3lJlAADcw67b6/Rwb3tRbcd0xL3Asz2P"
    "0StxGWXX7HDLzbBevL+l28+fDTpNF7sJcy5gbrrlrRAhU3IUwhp01cVebnkgEGFoYr5aAJbWEiyStTZVxryudV0GdVubXFbsj1CW"
    "L97kluUQShVw76WkHuK2p8HMqZYjof4eimvQpAWDzR13SXCatgtFwEwS70Zi471P6HuLBRxLQa/zdn3WETfZcey9u3LekcUsuitf"
    "osOSwhdltHRPljLKVWo0WDSQnizdJjiUbsVSnScxMyjGeSFmp7A/aEDdkq1hx959M9aWsTwlnmoKL8jzSXIaTEjhiavQ93eFH+TM"
    "eP5kldVTZ8jmYaV4QVWyRZTMQrIUoS5CMOj0g2+k2KkfSF0nJe9FbYWuqjNBdbPYLfS+lP6eVfks9iZA6U9QC5rH6bsLVEqgOZsP"
    "Jh5Q2sdz2nXjtlSvZQDOkG4YG1vRmyka4kzQELPBWYWGmA5mgoaAZhOe5fAmHM2BLExGcq6duRceByfe1PWKrlFH8az9+u3OTnJ3"
    "V07e//E5vGIS9xQozCuNADkzCZAzIkB4/67sfUwHRDWKAKMqhtwkW9nOTurKyb+Atbr4JpVrdSHX6nyQHl/QJGaD52dyux3LZgp3"
    "lXd3N2ftg9c/vtt/+ePRiQO3FsJwjre1KErzpkcZJJhRsURAiP19ECer/2EgKw5HwxFM2s5O1st6+Mv7sLMTMSbETtylwgISa7My"
    "Eqfd3emKhbGrinZIW3IgqMuP9dwZdcg/CsDDMfmjH0TGQ4HzfO+j+X4wKf8Ibmvkx1ZWreb2j8W0IYvDnOujd/tv3x19+Pnlu+/h"
    "pCEBAFOZ6IsUKQFu4gReapl6it+Lzkrt/JkyYyYe/C4DbabhWdY+Tca3b8MzcZsaaRxWNE/Vk5940vToT5Nr+eI/loF/BtsdijOK"
    "Gxbe8rl6y6vYe2I2lXwXub3iraC785fzFhJT0YsGOl/sYch6qopmFjEMgLo+0hshBmY7u4jO8oIDboqVhAy/4DMYEia5Mxi0t5iF"
    "AnYVgVU8eSOlNY6eGAAtSlGikGaJnsVDWoGowDdBkp2WIUl4TrJBXjzJc/kkx7aA3s6KiQag6A1amhHXxi+QRXwSjmgDHMngnYJS"
    "exmr5nCok4G5ctXLVmPT5luDEZJyjf1P3GV5m0jRfCWWdc4y3sLehcWKZAzkcpjcT5uM1DUDadZuM16Z+UCyuFUbd3fHJ/05XKLa"
    "i2TuesfpiZ1xU/Q9r07EvaZhaYYC1eHWQ5YGQ2eNjeF9nrVxe86qifc+x+BLy1cZvBYMFY8Pr+K4ecufbbjlxyu3/NnnmtYiMvSs"
    "BOTwuPIkVnm8G3vwzwo4Z59nUVDhTq5IgSKRioyFDQLfGeRBD5WQolO4YR07fxoayJNz2MEcB0ew8ZnCA9w4T5HF/U60pxjSq64z"
    "H8U4kMqY19/t+t4UaIypltbxRcRnQNDPTydr3rx9/U4UNLw2nVLNiSSg3PZb1Auoti6of6XcJFnlpf5EV+2zZDQvxJzmCttUpAAA"
    "unerK67pTWlQ0iK+iKvCRH2BO6KwCIhXkuUJvWqLCEkQAOLOBxrJxpLuWw+5fKdImUI/u46QIkcTUMwdBVno76eoGoHOE/gFnsQq"
    "BRqG90mCvBG3T8Rtv6jyfmZWeD+rK/59Mg1VWfyoKwhTqMrB7/piSKD26PeP8+kMCFxOUVXhiyujZate9WgWjApY6EsVLPXyLjhV"
    "BeE3F1OtSffQqMVOs4nHEcrs+zs7gbgGV9yXQn9A1yFxSJcsW4UyM3dpdHqAneJumKUh7pvnDJwjzqi+niX63Esl90Jh/R9hfx8p"
    "vAAb1mFLi0iMig4TUtsXTA/iWyBUVKarE4bG0FIeGtCH8cPus4Fk0A0LTl0PMvpixiU575Rwa8i4NThOTgR6TRDzV0fu6dty9ajf"
    "QP0/eNS73W8GnWGnBz8+5yjFgVo9xO/w7WCOcY0hCgSDms1rj3bF9g2EGnWHGLB142IEsHpYr4L/WqOKPbmjG4bGCKryWF5vW+Se"
    "dN+MQ7F1IBGbZfbkRaGhSe5c285lMl5yFvWpt+7yoHoPFYxNcRmdT0olkLUaYbTeao61qd0ulu/DRfjNIBlmcDSIzA2q9bEYP+MC"
    "wJTxENC1WKTDIL9oT6PYCXDk/BXc0BdsyRUrPXIJrfKlYL3HN2AupIO3c9gz6xBlyGdVaB+vp52dFP5XmuEIuRuWBoEGUU0BFfH7"
    "Wr1WORtDJzLoQA9uuwA2CJw3JzCpRnzopChHM8tDYUwFyI/zE+TyorygVJEU8ix3kZXGRIm10OM4ik4n8KSTDKN8+P3cyQuNFmOM"
    "QqFlqJSh7XefChZhuSSs4OCBjJJ59nlAsl1MGkhVpG6xwDLZXVRwnQ3HPVTwa9V26e392pdTEg7D47A43HJ0BuIuHbOw9D7JzT32"
    "05zEFvw2gjZ+jvKLt8E4SqwLhmD2y5ys3P3MLIEybW+gckndi5cigsqKQeuwC/K1X6b3h6E0mdJZRf18aqynYkoN/GhlMeSoGLEZ"
    "iyFeyWJI/5hlku43DN5DVOY9VDkOveOTfmQyxeD+QyP3FUyx6I9YaH0U2ipntctsXvH7k4kkDwx1o7LRED6XC8aqjSmPsQIoaivs"
    "AJiheCjlfxwZm2QVFk6Olut6MtHUSxLSbCOxZiYR4lqGzlK2ZNlI9orLVUua4qRb2bN1ER3qeJjYjPW9uXZDih9IEEmvSTUuTcxN"
    "rus/S90CwyrHmnhcKIVwVfdEyaR7W92e2YmyGE3O2NpwWI9GQvfZrqgf/jYP0IeGVz6FHEqqWrk2xkWhsFFpTGvJShDCkw+PDcpj"
    "xNtAudRgzym57jlFnrACdORRog1x2heiVeWow7MYS1iPa2nuB4ulV7HJFGfzR1JQi5UoOReiZEDcFVGyku31rSvM9rPOz05qLrR7"
    "MuhqAuLcFBDnmoC4udnQ0qxnU7Evz0mIbz+5FlZ9/YFwJvOJ82E2+vkmpAQsE028Y+x2AoJpOkXFZ7VdSP/N52r+ENFA3puTew0T"
    "PGnT87ZEjKkgXv2q0O6ZRbo3lNG2zGRP0ARGfYFsjbRvmto0SsomzbJur7Gw2T9PwST4Xb6IZwEid7bszncNoawXm9+FEom4xczb"
    "R2iW5P3gm0Gs65SkxwFQB6wWkKx/3/MNlZiihlXUBCpLxeQu4eDop9qHLFzH/v/7f/yffj/nWGjVwdBZUi2/jieAmgdVSWCvfF+T"
    "PXe+zp0uL149Q1fTQXtJUtMx9IKqGjt6Nk502Yoi8dCzmLLLgNtoq2uEP5OlhLIQql4M04ei3QxeanC6KK5yhNpBkONv+w+d2m5E"
    "vFKLPUcig9TXZEo3iA+hA1hpvFkqHovw/gII/sXvF/6bYKYimKnom7g8TZGcJhQxyDmK2FGL3nlgnaNyEQnfIsf5ic3JyaWCU0J6"
    "oXV1+8kgEZ5mfB/dNFK3MgjmsJzgLMQhOBPefq2tLl0RzRKOVzsNZ5NgFDqPth+de/72NkYJ4TVLcGKXy2Wxy4SqV6c/su6ykZy+"
    "ibnLRif9EaDVDnI6aDGqYb0ma+06VYrDEdPmy+ybL2vafJV2qvsLipw1ZhqbT7lX8LjdKjJ5MJFx4RS6oQxhTsfQRDCR6B2DYrqy"
    "eYYlZiXbqHXWNSFbljxMH5GH6eqr9W+ShRFOULXqLO8XVpSm/fMglGJF04JImyZpFo2rUE5m22jcSuJyKdldCxO5X3bzhxIgEdrl"
    "FUDFlepsJMuDXX+cFgDVFKMHiKokWj18iK+DQlEfeT5zDFu3JV7+74Xnx52dd0W33mJ7noWpuMm2e34MxJOvHkrEQkq1GWlTG+0L"
    "MhEfKJiSs7MM48Bg6kN/duOvqJ8ns4HfWV0O56R5DdbpTbiSHfink2R05ZcXpiQrRnUx+zK4K6xiixd1OBhpSzu0b67dOqh5NnF0"
    "vdVFdu2Ne5Kwqp4Z1GX4NpnHYzgUB5MoRJ+ro9xx29dogQzEFxylLHwZ505tCzyv04iNlu/uul943Q4xix6SFmv6jXBTtYti89i1"
    "HTx+5p5FuW+IMmzdVXnKzWPYDfvps+4XOzsR/au1Sx5mMIJVRn6WTYUkG3zs0MQ35FEaZ1UsBE3Dw5A3YzLQTzrSVaGYMAJuEJam"
    "bxC4S8Whq4LpekmFoStP9ccozeGxcETHgbxUY+7YEGmvJ/kY6YWZsPvWUsXIwYr9xEGBqoNiGP0WqHilASo5FM4i6tbZG4cTIBnC"
    "lehHHWjCVl6lPc1IErEFOwdeB2nasKVTYB1MOfY1hOmfDHxJQqyylm+2ZV+K4Ona0lvfAH+f155Kl1l1dv4/kq9V21dK3j5pPWvl"
    "Kf5z4bt2wlUaJbGCdPPpc5er/QOwSrSZ02cs4PvweijsdJEKGVAMNRrK9skD4bNBMqD49ZykSxiAZYRYCRWFgihG++qWqF5zcpC0"
    "9bV2uHdROBOFt0987IyarukRivTT6lSmheJsQkLQsAePBfr5sDvMeymcQ58msQeAZsvZTWsrmhIxGuf91jS42a3L9eHJAARty/Kf"
    "B4uA4F1zD/RiwKAU+cx5sEgedmE5G5tFNGJpFpO1ZsebNos0r6VZTG5utrWwtsttj5bWzGpqQQRFWTIJCsZqpm3aQakEEmcyJiBt"
    "bjqKcNH0KlXbUQwb8vt3h68G0dKzo46qcK9wHtHkakjZRDeUMXyZhyVaGVkIJpFEIjzZHlpGE4SyMcenqD/CB/uqrqXu3wpfSE2j"
    "0Irp7i+r43DCyjOg65UHB6057hrjm8/8tSB3yfP76jVdOVM7OwNHAcXXWAkumbvOtOtC0hUj+Cwd6zPCfZedeFB8qZICptskk2IP"
    "HuIGLEclqb7SY0vwEvWkV9qv7RiIvR8R0wPB9/LHN+/f+WjNYMl89+KXd/tvX+yzEwtZxFvHrcewpALcJm9ZCNYAhSv1mZ3KrKHr"
    "rLqn86pZMw/DMK9oLPUULVz2FTb4q0FZiIl9CVTACPkc72cFmV/xJjb4bb26hnOxQWxJNDAv6WTQw59nplBoRvN3VIpKgzg7C8k4"
    "n8wfffE4PkW9Fsu8vv5oNa2sn1YpIa8HRaPta3asbYCkTrRl2dBMghMzr7J4goTS+QpATMFnWkBh6wy1gAqHBvjq3o3oj5eJ74ep"
    "/tR5tNdvXE3tmR/gv9Aa/uvU7o/drmt5yZvNIp6wN6yAMzgQzDZ4lg2ddWAlVkNiDnOXdNFGYTSpPRSP9jYC/LP0gi713iRZRJim"
    "qzRS1hnfHzWiTxsDrL63zhhKjJw1ISyzf5a2c/+KwgCuNpq4z0F2qgd1s+Fqz9z1R0uVLDjO8Fy2kdesuGYYtlFLno58r1rLAG6S"
    "+RX0Wbhe8pJBhKGn+mxt7AS7EdzFXTXl2kbCMCF3d1xgt6ZE1yVn8Vuw59RjrMbNhmmSbsTbyktYWcscNlREkW59zV6NFbyllpSf"
    "SMaNlH9Y/FgU73fSXjCXAh/rkw2bIE8yc4PXQIa5n4XHMF+Xx9BnA7k5wVujjwYTN1qindx8ld4alZuZemBnSjV+gtHbxieelghJ"
    "QtMNHguaB0d69mUOEDSTb0Y1O3BnZ/LwoTd5Nqrbw1Bgd9d7OdH5kpk38iT1zjKWtxU05JgyatMRdEVOHZPHVtaTGZGjVv49UdLq"
    "Pxw/1SMQgz5uoAM1f2gm7aila7NLmhlCgVhDNxWFFJPs/94vIqcU0tvQFDr1i7fCFldikXpZNOX2lbJtzpAwyN/eVjXYS7oxmpP1"
    "flx4wYiltDNlF+t2D4clNNTktRDzVfQWpd5ESi1kEGF/t8GTKFRPIruJZLFj0+SanbryW6pGjrdBM8Ow4Q3Va8jsStPJDZ9VbPYv"
    "TQulP2Mlqyt5Q8bHzMoniQbJBg8R0/+ABotJlRRuBgbKFUTp3elF/FhAohoVYoiE/jtewA8fYPqjPXgQpHVK9cE3ydBJ7QJKxcCl"
    "AMqzBIP2nSZ5nkwxUF0wyeyiynAuVbNmo9jxG9tRbCXT4zRMPDwBsnuAVStA/fvEydaHCg0v1u89x8DQjV2vnhBsw6WO7znyxgX5"
    "n2HoNTvhYddLP/NG2GB7ul5uMQotjnz9G8Q8pKjpWHMEY/KS+ZkXPN5siJ+593yT87/pZvvEnnm3aUto6BKEheF5cTt0a24Hg1yZ"
    "lXPWur5KL7uC4WM0qIf5ks7wTGCe2aoNbYk9K8QDsqy1Ze12vXhgNwvov5w4sXVuHhqanfnDeq/UWqQTm1KmInZtvWj0by7CYMWS"
    "DjZPqCOdBOmrjok2809lwtH06JYhVuC9TTFDT69ccjJA3gYK6x2p/ruQynqRqRbcD6T7riK6y5C91lXSXYyuEQ/RqBnJo3GI0VZa"
    "+CkNOKtNyYUz2zk+wXb41Ra5vWDQ4GZ3K5dq9BE6bLCaCumt+17gekLupq2xUMqAh2iv6hOCQ9KQMUcx++Rwfk1yimYdfWTGFUen"
    "rnT+VAmKY5scziELI4FeZOILUQjjQjnRIFrhGDC1W65UurIZJZmRehqtaRyh6Zx+am9yfer7QqOW8mRYkRc3JYwduV9B1VYnWqyp"
    "skPQF66v691XQxrJULM5mqqIBw9i1kJpo9ZwB/Ph9G0JpX/AzhiSuaQvKXx9FDVEGeH2Y4Ku0/yeaPcaoEmu25QoyrEXjAzQJT6C"
    "SgVFsiwqvWFwLDiOA1fp+KHfirJWnOStoMUR4gjnteCFiYoCLSrbyriw18rmM9QzCEWxrAWvtNY2QbjdgrlsbQsgtjHc29JTmi12"
    "EXa7mCVkWaBxh1xwQ6ufgx+Yqv3slWNQDTqgOVzGuhxMrZyzZQR8RuMR5e/c4s68XXaaXnFeXnJ5Sk2udkQuKl8EmXC8KQarRTJR"
    "TjibAojgNBvRQ3JVvsqhdiQP0RiQluRWrwmqpSdUr4VqLXlMzaqcWoM+y273eGnkV8l8wdOyyNzGZpUkY4Cyi8bcVeZFzD/569Hr"
    "H9sccTA640h10vfzB1SmPIKZHdMOZv29MH+Zh1PHOPIqskWphpRbSutLFe/Mp7jDpOmlQsSsd0CIHVqFAL3hPvof48WT5S78uyf+"
    "fUf/9rR/2/Dv4+Wvj7x0YGeAisNSRGFEGwKKXJi7Q3SN/hy11HK4bwEnchhYnkLSFQVKGW5bMpdaoD+treju7gbtaJEPJoMBh0KP"
    "wDIK3YkhoIIqHmDwIoEOBn5MQX/9whk3Z0R6sJQ1IpoEFvzieqo3wjOWziids9cMihJUcZbWjxYyopj+ajwJreDGgRmCZjynQ8LY"
    "wTLsIlMruHHIh6ARp5pGkFEp8lyd8/VSufvGaADY7oW6casrfD0otjx6lBXJwipb37B1UauiEuov72PK03ayKBuY14eWU3OBFKdK"
    "D6hW3YKV0GwDswb0bDRgr6RtsiKoW7WzUsC3gV7aC/SqtuJuw+1X3ln6vVcsi35BGmXUKOsvT9oGxs1Y2gt6XmlDND2BSo0CJMaF"
    "XM4uD7R6167sVNH3tos6sFzq1oI0H4VVdmkyyv6MACizAl3idZUws3KmTKKgVBoRzxpEwworTd1VpdbgwMioXv7iwsfnrCCOdarN"
    "8i79Y2Sr+dr622HpTLcvkyh2fM9vMOUQrz6il7SD+qKqj86KIByuoSI6tfiWrFMWz1FZPP5voSweWtat8K9W6ISHjTrhYVknPNd1"
    "wh8s4nvrgaemwrZs6j663zVN3UffO7Xoez9YRIU2N//6nLrcebMud66oe/sJLzgb1StSp/8ruTJIMRzB/uojaLsdFdrXzJd0uyRb"
    "Ha+mhrJdsl7D3ns4u9LFuU07ImS5B5q5oGOIl3GU10blNGNES0evsuqBCBS9RnUZU7rSBEWGXqcBKqi5mrXCrvHVtRiSBX9QiytJ"
    "nEGJk6s+bquhrq3upSpzIyA7skuTbIAAFDLcTMm3CnNDodfu/WHjp68Bm2XO/7OgM1dVC5dS8XVmOtUiXjHpS5CaHHtxQq696NUL"
    "Bhrv3YhsjSptATq5RteY7lZCCmmYMGCjeVHPZdv5DLYJILCEO8t4v8SFP/HCpEiWaOYmo4suaSg/lHUGWSEDSE+WVZgHwdKzBZSp"
    "2DPIeKwFXaa3ssBInpaAGBY/PxUBjhYsXTIDi2Dp/Kz2SsHS9ehwpWDperQ0SyT00rPPM+KQq9cVoDF4Cf5Fi4lTxyc+k6/FtQLR"
    "6FU8FYsGNyj3YtmbpYdlWBTen80mt59uvb/Rc7TsrKUUz6Q+LgpuD+05bDl+i2W/cH1VjR5lo3+Z5ycjSKUDdnMKf7qAgPHcRSp2"
    "znAhf/WKRM8I92SElqoJd8RHGGVcS3GcI7KLlP6Qqrp7dkagR28BUz+zPMC4SuDXqpje3YV2TdLCatN4BOfytOrkdwXUfol2kqZb"
    "Bn2l7Im4QUnK+1RIPiwMsgqPx4DUox6NMthkZ+Nqsx4qEo7gfnEE5fRglkbT8OM8dPl9CLCEpMYcn0XnpbRsJhKGws8Z6v1Ba67n"
    "ROPChuLuTsGORLLbDmazMB4fEBVagYgsyaqmr5UDqNdBe6vq+Jlh6ijjKd3Nr+1eEip9hmBdujozeKqG60c8pUpeL/HqIH6oo1V4"
    "guidH8D+C/2IUduw4oKYsslzqHD+jAzDeToij1bMFSM+7iDGD2SeD9AARWziCJlVgHv7wuReuXJOTSlepcfBgnvp5eKqiD1su5d6"
    "3GAPrrBgWahewiv4J/Nl9zY8q8PfTAOXXoKE/cm/c0pLbfNW956pXaQ+5+jCT4QQrznvWuR0jOuJSexrWLkxqDM9MJhRio0AVMqP"
    "V46NXZUqD2qx8KCG3tLKHtQwkh5HiwoKOydNXxUwKrp/Ro9HhHoCPdRpbPpNi8lvmoiIpxStc9SqDhtollxJZ0P3m84SA2ZK/I/T"
    "WsSTr1u6UtR5Na+wehxKvMitsbg1nbYVbQ1Lyue5FldQw7KApBCVsfKqcCSFdBC79fnHdi9cCWH3BQ97XaKFZWm6eFL5u5Ye3jld"
    "XJHzEUej4+pLz8BMlcFKnyW03yhakdQaKYiJLUfi+dJRfD3DpjJ3SzAFQ6qAr9DCz6MkSU25qy5vRedmRbTgwv2DLeJ3XoQ9Zo+h"
    "Tr4ifrVWQwUizl3SmkNdlTyYvA1HcL6zVwSujWtAg9KXSK/W1/CIeQkUzp3FVPQ6QJ1MZ/ltDRqyVd8KkXpQUfGgBXWhvEtmdXvI"
    "EOQZCVIpH6WEQodP3mDlIgMucoE0sMr8lup8Wr+owbdOp7wd6jGMembYAx7bg8OqwwP30mRCUYMrjl4NRFDr7bfqShYy+xor4g9x"
    "29tXV1zulr3QliUuJR+teCjDj2F6a8dehb/pLJmGNlI3lJpkMTyUl/hfT+r7WIL/lnR2bKfZiEfeqwvnPGwODy3cpTOOZxzzLbnt"
    "RkRsQ7MirqyI6brIcE4iOJV+hozocZDewmMJCOAe+pBDlj3sja3OcqkHXtR64OC0UTyJ4pDeHfRk//R229yk682SWYKWCdh2MB6/"
    "nQPRo7UexWdJ0TC5PfOzKXpjRr4oUrPlGmN8yKZ1dQJ6ui7MRDGmZJ4jTONKrdpBCOBps6TMiFprdWhKo3z9aSQRzwbFmQe1wTJJ"
    "pRtzBDCsGlGFZWyB4DLU3KN3d3ztshwDG+H3xxtLUz9NnBdX4n+LokKv1IC3fTYJb3aLhO1yCYlEKEF4DkCaBar5YlVxpYtfrudP"
    "kgDlWIKnIL4gnW43kUq/XUmGA3WL7/jF83dvJMrvvXnhPX9HvpeEQdj4Siagt6te8Fp+sqPG3ikmlJ4PvffXnorv1Pv9nSeCHvV+"
    "eucdzUhI0Ht+vlz25RS2fkJnxovtP58Gp+Hk0QU5ucpau0IhZ1si2J+uBkJ8fnQ7PU0mA0OLzchqR7kMAuxnlOIPbUQ11wmXdS7F"
    "67sLS8Qdl4H0Lfm7YG4NJQw91aFHY16qKfj+SvdvpROaIb18RApQ7RqXjPvJpBlTUxlsJqf41WnlkVFcOdYWnoewE6MZDJNAbIfx"
    "fMpvL3iFeDG9eNqEouh1WvgBV4N7T+tbmAx2+/k3QXpOvATlrDSX5nvxQOVhdHfmTCyWPT21n/9pbwhzxgDDhehtdSxMLxjZz1cc"
    "TAhjGSzd3ooRZkNRYBzCoyIUBYin5q2qClC4PR0mO0C2Djjg0arZj0lxTnv3qQmWg5QLCTT2X8hFcYTUbn2PC6Hi7xVrijiWuURz"
    "9X0N2Fj8hikMcVWgStH9X64K9ssPCIpUaHGLowvQaGcx7+UPfb9o4YcrZelJB2NLKTwABg4Ls1PaH0QA6ifzG3+OD4t4EB6Lo5cn"
    "b9JoGmFQ9xNXOfAv3KETexl77HOPqdajMvnss+7wO+iK9Yf9P/9Za7g1nWd5S94jrZlK5xjZygutQ9hbzMiQHf32fiS9MhdxAML0"
    "29XgmO10GOtnQkKf+dL40z/x/qoKwVeBPf9+JUNpeZEXSLuIK8cXyNbHQFbwqSF6SBpxkobsfbSBLxIR4fto4V4kSe+83pgTS4i/"
    "WO43jut95/jj6KPv/YTkV5BlaHx6gxKnBD0MbtsGuw1lZvDl+G3d0ug6RU5jqmrNtnsB8b3eLNHaJJ9GslnXOz50wvaDbJLkGcwc"
    "64BDxbfOYeItUDUBu2BTJiSCJsHt7jTIrvBxs5Aq48+dyuWOwYD4Th06pcEBku7BkdGGKBsk2OQngCYBU03psKoLHOgs3q3yT8ft"
    "iT5/9Ki37rLaFkZbZdBeOvuOLdf1DFCvHQZWlHhJ0VoBaDK0+so79qmYfwI4TY39peoExh+p0XdFk8eWFj1/Fu1msBExgKmWc6Km"
    "xwSA++8+dcWgXzqJ7GbPw3Z6vm9MtlF9RaP6qE68p0/wX+rqWwdahRsEJYwfeo+XNAG4W6CkpyaT3zNrbADpJV2BIxNK+1Mml6Dw"
    "grbOUpDLmonVZ3FfJJnSzOSNCssAjRXSC9pVhgqyDsJXUXx1hM8F9issP4HMns4mJDXWYBBp1PGbMEU32IJAhmLVRE9Y6WHS2xC1"
    "cN4VrdbmlfblbFRgK28xE8yIHrEqkO4AYh+tS/Ljzsnd3cBCvgVtLoIo1gsm18FtdnSRXAMIxYfqwpsLk0fIlj8ltkH7xm28BmcY"
    "xIjWUwcORXWRs/jQ29OPpZo8pUg1ZPTjqwTfO4t1XKPIMGOPVBuC6RAyYKHoTez9nCQIQhTMWtkzmiBaX/p9AE+nXCTQb7UTMpFK"
    "v80dlBs7iHcbTusB3KCnwehKQqGnEUSlQuUkD60ES2XKSR66PC6VKSfhiFkOrBWqpHkc8anUVjVxSSgAj5nf8Zc9gYGrq5qhhwS5"
    "ovRRXs3mxeQqRWfdps7CeCy7IhfCm3SEFYpu9pq6oWXEXTCBXUD3iei0krHhzrXUX8jDDouAv1xt4h83AYlbxAZjOX1DEKvVmyB8"
    "0gQhblAbhOX0DSGsVm+C8IsmCPEo2iAsp28IYbV6E4RPmyC8nE/hxYONoT3yOLmOdTjtuRtCW9dIE8xfNsGMKBeo1Dqga7I3hLq2"
    "lSawv1JgAzXT7TzeA+KGzXN8oeHi6zjep/4USYC54oqGn9XbHhJr73TMI4LL84tLFz7kFYtd5URjKtrnlf3ZkLOsV16B8KQhSTNc"
    "uJktdzENbphzBiRQneJyaLDYgLBcntS9MKpdACn31hkjmGl41vNLffhYz85T9BYRzCeSZmbEIikQD5SnKx5iaGcESl2NBUehKBVb"
    "esbQ6trwu53On3y5p8eSTVo7ZR7S1Ro/FdZMcNnRX/k8T4ikhN8ZrDNrBPS2uhrhVJ4m1LdZIGWDqiHPLRKO41di6n011eITWgjV"
    "h/EAETFrPKGAf4B5J8WGoURSVPDidlaoLcCT5P2V855VlriUkCboW4Dce+C2gxHyuzmTBPpIvbA0WXbQrojX1VKrmEZIxFAWBUck"
    "mlp9epoBN2RpXxZRT9CupHlVZQnsoZLolY2jqJSZVBHQBe1SihCnBsxs9qSMCXeg+KkpJ0Y1molRg1piVKuTGBWadzINjUexbzP5"
    "OTtfU+ni26uIStTiVWRYouzLeDbPuahsrEiqvMykD0oKpA4vl27Dy0X3VsmB10PNiyV5HkPkD63srdmK8lYmWjJUKLGwnlDSmiyy"
    "6VvBgW4/iJQFOB6vCYdyMGaMCFNJpJYfP9mgIfQPVmlnQh6E8uMvNmhI+jTRW0pm0MjTtRtBZ5WVeEdydr5c2YwWDEq2I0LdijXK"
    "j7+qbcQeI5fasb1sBULWuT0FevKlqmTG973CRPCpYR/t66gwuq16GqdWSniE6AEDb/hKVOVLRCF+yoY1e1q/ZMfqKwVcXz/46lMc"
    "cPWtHWSVVpxbjSwyD4WWQMegmZAJDW0DcUVMFA8HbzIjjowv/O0Y9Tz+jZ5ztjqWe6OMYoQTnF4o3eF4Soegp+kTeIa9H+Nbw0zQ"
    "CMSr1yQMDpviezqsdFPRT48u8RtYkHjeI9mY/NJzjjRgbMn3vAct7lF6oc1pCjELBFUpf2LakaC05E9Pqu/3QqXJ71XjlNIoyome"
    "JvoNdbmvZhyKfMle2C6leNI/jVaknKS3kplNZF7F/NQsIOZAswfphbqJiWfGb6VtYSYp9iDWFI+TkvS9R1b+JaUCL8p+qhHJw7Ym"
    "exhaz3eExnoaPmOCiUrIa/PrBlQqiznKzub56WQk79tOc00oWqr8FsllVb3bXJ0Klxp4l8xHF2E87oky9P0iHnMuTCld4iITPvF+"
    "1pyL6rnq/i78rMnLpbu3YmClK1ckifu2+3h1be2eFSnyku0+WV1bv1xFEs4JVP5idWV2K6a7d4N6T1fVU5cxTTrtKqj25eoLVFYL"
    "xlGiLt7uGjcvXrxUq+727n69XiPG7V0yDwRyr2kT62WdGhNBaKK7RhOyvGM1E4RG9tZphEo7VVNBqL9i15WGoVvzQeUnqysfGXvO"
    "hP2L1dU10DXLLR0n0uPDZiuHrVRS16LDfBYdFz7I4U6XN7muDajf1ebdrC5k/X613rXG5apfp7aLU92W6opU96LlCtRuvfIdV7nQ"
    "jBvM4pNMu5/a5mXUVpdRWQOsXb5R2gYybuvIt21i27a2uLZlVGsHy+ZLa+Q2OXlVlN9bJPOIwDs1SbvAsNZwaAkyVwm+hHNwmmfX"
    "QuyZT+t/kn7/JP3+ZyD9Siy/A2b2cYW4gTCsZ0JuSC/uPb0vwbj35ScRjHtf/VEEY32bgoakEB7LzSnJva8/hZJ83PkUSvJx9xMo"
    "ycd796MkHz++FyX5+Mk9KcnHX3wGSvLx089BST7+8pMpycdffQZK8vHXn0ZJPul8AiX5pPtJlOSTvf/ilCTRbJKeJMLhn1TlfanK"
    "hpusXXuP/WfQol7QNi1yHUPQ5SoVNnJR5BcKdrrEtTRabk0JXqXY0R8Fk5HzYGF00ObMZWsX/RoRlSu0vP89Rs38KYoJl7MbF61U"
    "7JJB2Z2uEKgR2HNvYQrZKkakFvp5fa438XJJK481ArtL1h4kya1Rks324a8mX0WdXbH6elveX68M1T423Ctp9+39/1u7TxhAGgp+"
    "Tx7/4Rp+3O0/lfz+qeT3TyW/fyr5/VPJ759Kfv9U8vsjlfzUxDLZZjWpeGxQo8JhR2FSIRNKJhUyuWxSoakVEmeWY5J/T6ampkGJ"
    "7lFShW4s6F4RubHHkRsL+rWmWkG/ejalKzVyoJ5jNfQnnoCxHHLShBSW6W21iIK0oKqC0wy6w5Wqg76mKZjcqk0RlBWQRbLsfIYb"
    "9O7OV3a/yBEvr8H6E/CFfQKo4VVTwL1/pkkQQ1lzGuRJlRNBU1ixMcKnwG9X7vLbq3ZKgoDB36/IsPGXq4E44TAb6N11lvlL71e0"
    "+sujHJ4ZJ97foIh+OPxkHlFJX9Cy8FgNt2GwoxGcVaj9oGgTi+bpHF1ehKifuq+1m+/XFYv3pdFhTqFKVZVUrx/tM1xfVuACynx/"
    "8BpI5w+MIo9mSTI5oLGhI5xZ1ltkmISRmE7hld5boGln71tICoMY/UQDpkQW3GIS5ujey4sH3zuOO3iG/jChFHqy44SDA3jnMt8j"
    "DadARsNr+cM1Pcm8X9qT5NrFyEVc9sGR8wtFYfX8KP4wx/Bnw18ORG30jcR2mqrBaAxL6PsYrJkb+JsszLsBq+hlvaTa0TiNABu6"
    "w0TB6ZKnDLTPrBQGggrLjrSyxydotsklj2VnZ9EkQKvoYfsjbKYkHbZxnj2ZDcB9iNO7u2pxLHZ39wOePJjFNgc6QGy9iMa9Yihw"
    "xUiDcbEmrnCD3cKDMRHwbOVtXL2dnV/aI6B6lel83YLooRXqynzDiyaMSslcd/DMxBe/XHnHwjWXfEi/cA6PlK0jOR7viRLkRn2e"
    "+0M/RHNev+dfB2nsG5afNLe/O++gmR9cp1KR5wp/98RvgBDnoeueCEYB8hWoW/PKm5Sh/KsrdcHq/V2gJrXm08PTsAO9RraDNAp2"
    "J+g2YbtHEAuoivhvv/VG3DN6y8DTukY5gUrCLN9GBg/2lCitVeK2Ps+ccPDs1yOHT6svWvltHqa3WkM4E8kMJgJ9h6BUS0zwWxj/"
    "312R9sK5vXV5nN0nGnOGaJ4TY16L4RaISJ9kuZPgPDO/ZGfnhfPgyIXufnHFwVJ5vruzsyVrBClgq4/huHQfGXyxFchW2jQnk2i8"
    "jUvH31gBPqHbXelPtLIMkPkd5iE9gjSO2H6lXNxnX8N9YJqKattKgf03OBav5MeDq1J7SfyG6bYF4a5eINeLt7HWemRtXdAolUmp"
    "jovMBcYvsc71BWCXXiS7WmoA5vslAKP4PQVpK9Uh8GAfhPs6jIk6o+QoQqb3LDB/0byQL5zswJXoVrbrDhlLyDeBcTYYo6uBW6vr"
    "A6Pyr1GddTEGQlmh2XF6+wETlm6vUrzYE8VIO9VW3yXQgG+pv3+eQHdxLymm8Wu41eFPJu8IdoJsmbCn6ywy3VTeIg/Os55sUgRK"
    "aPnkZah83s/Ued+rnndPKMb/7vhvv3v53Pd2edXTfdtJrzm3UXlLyXKMqzVqDP3huN6vgx9yhy4+hAao2asMbg+0aCG/ShcoPaWs"
    "szSZ4tmeooaAT4od+Gcc5kE0Yb9Xbj+6htcGpfgeoMlFuLPzKxmMoDM1vFR3dpxf21xiQBEglTOHZB9JHeGxA6Y+Oo+dX+lKDhU4"
    "DN6vbfpLYQTm+9jwzs5433Aqk+079rZoKNxctzSUpVZ/RMAQSN73B2IqM59dVkz2sVtyb6oqUP/sbetdNA3hnnQm+64s52mTgDOC"
    "cwm/fxFuUZF2UA5Sua9pgK52imuGEj/IqcVJ0cE9w+EilRgORE/9UDpCXL83xwZ+6E32B0CJymS8xWiw3uNOB7YQrnhAULy+gtc+"
    "VHoQU6FfBA7czzG1mKkZzZQj4NwaoNtahnGrgBFj1FSWjzdjyDtRlmzcj17tgqjpqZuLX2Gz4nINabA9Z/VUuNqCTPeRaBsA2Vzd"
    "hQRwSPDmGGqFvEQmH0PLegci7gz/7VGcSOZK6Kt/wZ0tlu5CzaqIjLOiwRB3kqjjsbt1mFj+4bXbbYTvL7D90dsxuej4QS52OxNJ"
    "rsdN74qmVdy90oC1Y8an6HyfME8CbeNZlGeTHODTr9N5dos5RLJSxWITfbAgi/N9T7TWoQPS2JS3aqpRAokiGpiFsPDEROhoWZ4q"
    "fTE+1kDGIHTWAcGyEOf7tB11MChpSfDdY5Xo3MoxIqaOzgBMdHgeky8iuF9G0gemKCbSkyuK8MOJQ36JDgGU4ZBedHCICTLhS6iP"
    "FYaQgosxkNUQeJoISEFyn15jo2Q6BZDn8VUM25H8DgGcFOUAiuP8YfRs2R5CCt8btLTkoEG3+HoncloKx8m6hYh8eM+fFvyA7OPu"
    "OblCWXo3JpdgisY3S+/ILHsaoPXrQbVoC3/Aow9yr/d1TgdNHqS+q6buAmmx9F7orIbndlYFtY7uxmGdl95r2/CM10Mx1iutW4yP"
    "MifGyb5qwXxvCH9MuIJGK5eCA9LxbMPWGCqHWnej3Wx+igsG6T/qg3wjWutqT744QJ4SlPzOZMmceC/LCa/0tt7W8nZ+14t9ax0A"
    "OutuQefJGZT/qQyVKgKZ31fZPO/YOFeweUhquRAOSulXJs1IF8iEm0bwFqG3M0yoMC4DuAT/x1tgAbwr6IqP4R5KB7mNnxPewKEV"
    "LARShhjAyQ7bV1E8Zkdc2P4wJEWEDJ6zqKqJ0HoJFgwoeoLgktzdIZSYjLpYzSwTqoj8Em9k7fD0wBF9ur3FLEzxzdiLMFGysST7"
    "Q3kJbMtHeh3vZFhXhBG+DB3SS4tuGEEtvQkDKQCRryf8p6dSH3U7HW9uHY3v9w5Uo3XsNm+MdV9gOVXCU61DoWvSrhUPPG92Lt5M"
    "3hnWE9non1jUILeLqiUV+a4IXy6ShrBEDEgb9i08TVDw0YsRDlmy2ukS+XveTOtZeT6u61aAJXv1HyxU2vJPPj0TsDnBucQt5MUD"
    "3CewdY9zg2G3s6PtYM7w3aEs0+ZD5Z8oF9bl9TiGGzD1Ppw7fG7ajMY8seNk2F+PWCPjIZajivKpzek4A7Xcvv/rf4fXXI/7oRjK"
    "SfrhIrwxAMfUefphhNab8HD+V/+hVhKmcDYJRqHz6D/+9ZEHRGE7T96jY7eDIAsdmn0ZgReagwHnZgRWnZMqsrGTB4ui+LI1ndK8"
    "a2WZqiBmqv+vqI4EZ5TKoHP+5tEuvQtt/bQ5pwtrZ2crbFMMtuGvOuc4YUTAvF3ltR5dPdOiPOsOFQbJE6hwQfy3uCfyvWvcqUIj"
    "o2abAhItnUqCaBioI+mJ4f920YbL/wOHN0IS54eCNwP7YwH/4iOKZv+DwKVCY4u86tt6kaeengZSbxBN+UKiR/Bk8K4jr9XUQqmo"
    "K9CQ633EcTiLbbhiLqLxOIzRByD/8rZZCjIZY1p57sXUUyH5uLeXMxkAgJ9vae6G5WEtBP8Ov7Z7xSAFlxVVc1J4/m7TZSzeoMte"
    "qOrheSIIwlugTTX3tqdIC1dObOrIq46quD18Z6tOC+eRXiy53sg1/vbKlV47WTlLMKSgBQAM/i1xjLeVHucuPkAQeHb1rVmHfBB7"
    "bBujgdHNvt37qBEewscGZRN2EU0J/c5s6AMVI3zZKTYZF0QId08RNL7OUb1qQVYxyXXPWQgNUrzVB89uHR7RsQh1cSI1bpnzHDPn"
    "GZbuVMaJY6WsEvMeeU2v3sEsMUSCVTWJMkJFPMG+q7PSFQFKkGE7HIAsRKiOpeT4ep/5WLMj1/sJ/r47cOmoQ09nqXgvTZwRpWSs"
    "e8fI4fFe70lnqTshlOVRbxCF7yeFfPrdPjFGZ0rYz5TfNJScNwobqDFPnyOnK6Neu4jfS7tMssVOSY/Vl3IRfnDJxBKTTxLqLSCH"
    "cRKlnEGS0rjyeNCt4ge6VVgLnbCaeQN5dJHRGFwlU3ieOfngWfk86MKDYrhX+57/f/9v/sN3Tvlq66JeqMZmZBiHL5zfPyJX9NuP"
    "DTxH5C++Rv4iyQksrBD7PHbt8wgrxs8Dy/zwy48egO/4PUGPaXXuS1KaNYpvq/eIgbTMyX3hfNh3dfRizG6JPfuDmqrH9qna3zfk"
    "2V/BA831prCod3fnjqZeDLv4cl9bvEPcq1O5V42iGtNZPUDgeRQnudr557TzuYEh39AokYWtcE5Nfg1PKJOzq6selJC92e8bgJKu"
    "7Sk8jGDNJha5kczym4GuEy18e8ToQnXBLH0jBYbw3b6p6Bzse0I+LhZPWxEeyokx0hPXlJgJtAxJKwf0UiJOHo+BPmVAm6KOttmv"
    "o3HYIkQK2XVo1BjpHzmDL81NYJkKbYIrkyJ5i9ZJ6ZqTMkUjiKJCaUZSnhLIr5uSFZuy5K4X15ta8xbb6t29jUSXpOcYkOWJRCHl"
    "nLs7vpxJhdnMKgb7d7UBBDZIbxuwgalhxXC/xVNe7dv/f/6X/9VnEV63473aZJVWXekkbbfvSM7baAFe0qET+gP60ZMCXSQPfdlw"
    "5TSuGNaqwUzCs7wYi7qJaSth1goqRaMaqLgprxRMEbE/jseCXDnjvw2KHvoVTCOmT+a2ccI7R7RGuF20WNrR3+LOgOYenhVFtWWe"
    "WSv9BDc+IXtA9DNbPRtuQyakdoLTG7d6t+QpURsV4g3xDazKNdB3c0qgC7yHmWV2iSGlZz7rK1o/Q0A6G+WU6i3gl9HOUne4rVGF"
    "QtWKOY8npcv29337zqJEtk8QdLnQSqUvUYw1UcXWyeXWUVSNnZ75uHteRwdyT0Cy048Tpgsl7RESVScof1GkQm/Y27DQbRbdkALp"
    "nO7btmS1bZpS2qKxFDNrrdyw2PjDuVvho5Qbogyp+KMaONLJnQP4QFWisQUOet1nrvvQp4191lAEgZ3V5w9N5/CI3X93tBPT2DB7"
    "QdeP0lt5XLRzUduEbfcSBQJJt7RNS1YWhW4yPTnxASSfoax3rD0wld4wCujfs5zsY5RFFIiiK3CYX2hKpWGWTD5yxE0RS4h8aJFc"
    "Db178RcJnX7eHyxClo8SiMwT/cv+4E2aTKOMPB9iYzCzP+wP8F0JD/ogu41HLfWs/21fxax4vy8r7Oz8dR8/tf5db+vn/TbsOiGb"
    "VlFUccI+yjCnfQFSSPCEw/ZokmSAtR3/mDD4GdTK8Jl/AogN+Uz7eZ5GcFJDxzcL+JLHKwOFBNdBlLf+su/F4XVLDNCJYUimfO49"
    "3Hq3YSZf8HGi/IJScCo1jT1JRYResR6dYvqNuc/1qcf44PAxFFpFQ9I20KSGf90v9DyLKe0XP1lqDd+iXxSFwaLp40J+3Q8opdZE"
    "1KH3tNOh0L7DNj4iSgv5930OLfgD/PV4sg5j82fR5d1dAY6U7gHExdLly8HP+33rBusLyQVxyLKDJI6JGzaEaRqqXUE6dEciJEZl"
    "9QfbDxYHR0ftMBsFM4ybuNyGDcGsRiceIiU8uggzidK9Fs241+Jj5rUCr3WcB6fMYIGdEvegUqnL9arCLiSoYEq1JfwFlpCD8Yl1"
    "tO/2nR17+tagqIBkztBejMcr5jjnaf/EExMuSR7/6z5ymOhobwHe/VvxyfzKB2VRW3hZiPPGLK7MjSQhO40vqwJRyM3mpxgUzqgR"
    "TIUMMrqEzqKS6PLEC8ymOHT10kuw9FmSosxMVDzxRviLce2JN7ksSxXHQhSOiuZzSy69v5fe2OyRAVl6ZwbY8yw4x8Ize+HpZZ18"
    "UfryRZJ6jpBcXDbIGc9F5l6JRoasD6U5FjU+WgDCub+AvFt9CCVAJP8G9h3QzrNkEtFknF7WSHpRQm6FXMjJL23S84NLTQZ73dD0"
    "u8uKfPW5UIQq6dFvojNf1gtHiWehJS+V1Aq19wY5K4lPUcgmlVI1gZ5UcBcK1esrnxca71GhCV+onad64nwDO4Cx1FvfYg0tUo9A"
    "weP3Qm3LwgR0WToopbOaGPbjeXsK6ODWkQqzbbxR8YLzQrdHL19vKppeFNGr6qDcUi2LG0Zw/EemqisJa0WaN0dnGP6ffA8wCtI4"
    "eNccA31yMkhqZ8OVTgPghYfSdIZqIntRw7OKUxNnooukpKBLk50WUlsBpBSUmsMpgf5gES5bDxY5/pMu/Tbg7CncMD0p9eDiORU+"
    "Tr2qrLbUGTQoFdJJJrtC5Ae7/0KuFNNrYk0xUpgKRSYDp+H1zuAz9IXajYzn5C4pcHk7DXK5cKvb4FPXjpO3xNlgwiEfFDlB/pY1"
    "uM97h0F+0aaomKIX1CelLq/D8Cpbr898qVX5pmuW9r9pdX0ujoJjAQIV9fFxIhoQxI1so7OzY4BGyf/e7bh/6naG3V6nb/QBJ4h3"
    "myzpxS53GQ9/MPv8kJDI1LUAU+3QleDBup6b68oReb8ibY+J0wHqcPALTPn1o274uI/BCmlALTgR6lTP0ijOs+Hw+IRRazr4cpf6"
    "PJskUMHJd+N2DkSn++hp58lXQHP202cDmIj0m69QXew4PXk4iOENFUyzIowf0GwzJFt14DHOn5LHJjqS+2gOQh5tgGwEFHWqf/ZL"
    "US51YXrdWd/ZEUnPOsPwkfj97zAjUpf01uzfkHynhQFUvwiiGSq5dygbOZVWTO12W7tRNObr8YK5Lj9U2axiCysDJ8n27B2feGZ7"
    "0uBKa0zsF5Ej2vpgwasfNGX7ol4utOy1rYd6+6Rj/0GiQ4Kk0iUtieryo6VLwFQz56NspfWodYWqbJWGUFNDtVO6STCvqiV0XFwB"
    "WgFl3rGzI37AQmVKm2Xm6KlrqIbwG9pcAWHFVl0AzhCD0IzcNMsBD9Ao6rurlb0Vx7DaWgbkxHeCglGt2rUsbtWgWNcicWQKXWv4"
    "HsX+TlzvRmzSQEHnLQAKMTRE8/gSwcDF6ypZuN4R0UjwXH0Z55P2c8DW+Eb9Lknh3eZIcgmNQ3KOUNGD3T+OkLilYKJYCmtjRYeO"
    "JbQZhoMFak73SifFo2UWqfBcROkhLL9IoF0kdM5EEn+8YnVHpPxFOv58Jah4uMR4Vn5wwvD41zYyak6A0CnaRJPnUNGPU3E3k2o3"
    "qrjLBHpZoNKbhgpwaEeAR45pmpWat0efbHwgkWVx8JHdVNmY6CzeQXNP2Xwc8tze3U0PnF/xt1fAwgNHyA8qgBOcQ4mG8IsNcnql"
    "sQ3VCet+OEUkrurMu9/iN+0DBrmKvPB49QgsVHdD1aJIAAzNVAAd6uv1MoZycJjEYtHlItPc3qraNBi9Ko8OCP5wgHFY6NGbhABT"
    "X1g0cHse8VCETeZC45SEQweKh54TyAGU2QvEVij4B7BMvXxnpygufOBkjv3t78JQtrpwndZ2UGGZQP3eg0USEq+k6FdXpUcNNGU7"
    "ggPsT/cdtPc95FFv3Fu5swrXaYQ98sT9uu8smJ0p94zQVoL+ibtJZGV8FqVTlSOimQqDK6/0bPKQkVdtDPBpQaGeJ9+iAASmYWfn"
    "AgZbtCwfg71Ua7IM/6SYMR7F36qjGI9tIxiPS9CX4R2P/x5mdeAKJmSJPoA65O1IYX/0tiMIYZMEFrT0j5La5PeF29/ilHYEpycP"
    "zyEvd+/u8m+68M+zvc4QbQvYbtgrd6qOm9ujiaQBWiaRjEmADlqM2EkTqolVJ3aOEyuPP9ngmLgIuxC3D8r7xD1EyGOpoyV53LG8"
    "evnhkwGPOZdXKpm+B//FkMVVvOZslTHb3V3dtqUa1RWfY4yoq2YEKHeAWadpH0i2dAduVt7B1L3Wi5wTyBNYa8XgldadZmtOGgCn"
    "rreoWj7Wsy2k8PzDrZAnloyEmW7Z1ut4C8GKk4psZ3UW450NLMb5lGj6Cihc892yPTeqaTsX+1CI85vttf/6cU177aoAk+RLOJD1"
    "h2DRohJkHzF8fVNjqpRlmutS3i7nqSl44WT7Kwb84hMM1DUjESxa0lYsye1JzWO8C8RqQlp4+EMqfCTxLrpY2O5tjQXaPHENFRmR"
    "PPTjcJ6nwcRXkpqK4mIqGXOFmK+BuUR2ADz+7p5dk1FTYQwvsb9CcUkSz+Tdw7epTHis8Zhfsrw0k8ChIsE9DwG9ozlCndWDwnhT"
    "FT3jdK9W0TOK2zah6N4kHrbZ4k53t9BVxxM1+DQXI8079oePn8elglqc+JJ30RvYRTeh831Q2km6pyNcROmWw3RLIhOlwpbU+Jfp"
    "Vb1/5N+Vc5Waf6oec8LGgGwOKqmrLQ+an7aFlJ82eCqmYn5TzPdUIvp52WUIX1O+noE+Q6RbAXUx6Ji6rA3EJM1UzmjBNZVJ+EGM"
    "LpkAv8XGn8Cdn8HLNpT4wdsWqio2xyGGFotVeai8nUraKp6S7CNMKOCfn5KfVHp/+kbXePQrB3x+U9ZA+9tHeYlmV7fmRAlsj17p"
    "MjVPF9V5uijP08U95kmrU52Ee41+hebFKpSsaypJnCmUlcya99JTKlx1rKGidMJqfQ/2SysqnbrJFR2T6tUsiMPJLhrjKCyJvIiz"
    "D6QuQrn03QtCU1QpJXRCp8iCvZkHwotRQcTk21rETeSwR1eZw75sXji/ukQj7uwgToDBortIPJkn+MHydlaXVkXVEJE1U9FeHu9i"
    "Ml3j1yHePUl8ND9FI0boEbaX3gPr19FMBZf0Ww7hDO2kYcqiuDRfqPyah3LZv/aSS9SDE5Bp5Ls8V0fauRrbmyQvAkJxg5pCNsl2"
    "Er+fIUOqV+Ruy7iTcuKgILz5p8ENa+P3/KdP4KACFqOOgCDPyl3x0o1hXtPoNByTjQgUvUD2g366UPpddIw7Dlqlo2MMlp9G1cF2"
    "P89gHzcOttvZe3LvEeFQqnDvfR64n1ThpuczOyMYh6MIyCIM4ksPWNVemQl1/9USLeMoT+r353eskUFLW9qklr2zJHd8+JhArTfq"
    "/NJJJahh4SMsmTGyohZDGV9RwTu6JFXSva9cUljLLm3vFOGagA6uefeI92gW0JtXBU/WJo1uT8BabDJ2nuhTJe8L5Sn8ZM23kQUE"
    "VrjSXnVZWOlJEXILMbG0dpp2ua6VwnmLbfh5Goy3a/fF8oR08A8kFnoME/l4zy2cLxFGmwh6CYdWeY8SVaFIDZ0SRj4a52rk8Bdq"
    "Q0/xtSpqN9PC09sNn6vNC1EZwlx7aZYHMNdfmiKabAE+1bQt1WYASP51DQwiWwPjSxMMWf/TIREMIDsczJ4poPjKhIKzy5yhuzv/"
    "0wCL1WuAGGWC+43PrB/xzugpVt6PLJGww86GSAXsX5uwc3apq08GnUGTskrtTVji2YgStq4+NHlHW+M9XYGGfAk9r4LUNUGiYh/q"
    "AXO9gi26ErbumrAxv1kCNQmt/cqQlUpNW1fK4iAWEk/vduscjenQ7a0J3TwuGPHaxO2ZE6eVasZqP27OhKuA/lgDXbxTPXi1TqKY"
    "WSfVGa6MYBR+bjDxf94TIACM+1gG/YRlu0jNRYNLhu2txrvpfBLqq4fA5PRMR3YyqYuT1WjvVFxgGkgU2wPlvqX3C9yE80tNrX98"
    "qXzLlcSjrKuP3I+bgoVlcD9LbyOhs7+nkf9nl8VvZWlz8dj3ZkW3miLAmzD9OQyvRNdSUUVK7jWlI304F5WmpKYRW9ZoRc8vbXYV"
    "mqqK3hWZM5yTTpCM7WqYV3yo9Iu1GO/KqdL6nhbFy0pVBOdJyUEl7uy88P0qbFkCjAtOpbKeFLBfR2Og27tfPvVEGBvYbha2AmkQ"
    "7QPl6wube9VCycGh2kRcym66QxOBK/mxMg0UN4N0i8RCyh1wC9NfXlRWQip5bTR3Ekze0WVhylJooGAPnrUhWjthNPLC+XjuSn0s"
    "WZokJzjtuMaFeYmhJKKssDU3BaXeMsAaodPx9jpuHWf2Ap4BCaDQqmNeu+0cqutSkCv0ChAWvr95lf3HnT+hk2+r2Rye1SMUAqLS"
    "VtmL7yqbvaJfGhsh7BrbvOpNo/xWwYC5urLaZOVYybtHKyZO0XsVPeLD/+DynlBL1d2yInVp/r78anbTOIHGdiltFP/ec4obajVs"
    "eytgQ/sntTXrzeZEolCUd+1HBKXAGnq6thxjZJWSmpG1gWXZcpGtr7Q2byyYObbh5dOVuLFq2qWGKQVTgnWpSSSludWLy8Fk1oYX"
    "ZwgoXpgRslMHaRvI6+D/Swv+057t6pmtBaXif6Sr/Rbfv7tnk/Cmr3JH8zRL0l5rBsg0D9MiA262dJftTnotnIEiC6PQnU2S616L"
    "vcQUOcrVfysNYSWATNF6QlFArzXOnX/TIWURwb+5RUGMD3RON5uldJFpVCHn171Wd3bTIufPlopUpNrbDChWdPhVrSFy9MJ5GsRi"
    "hCrNBLnaTFGnPZ6n9KD6N9czqhNQ96rJo9q9fwOC1Nz9FBBudrOLYJxcr1m9vGy7KZyaedarXTPO1ysaUPd4WTBUYZwXZc6SON+l"
    "663aMOa1MU9vlCoI3201VThXVlr+i+3okZcigGTtI4hfsHXhv+gOuEgPJtF5vMu0cgsFVPrxvJxneXR2KzurFjgPZpZRQOp6m1+0"
    "azsE+vm0zvyqZZVt1y7vP4/ZZztm9j2KvBSnJ/meLn1WtjFGrsXMC8T32m5uxM9UuAZL190AFyKsqYaZ7WDXgLgubKJ44x2yW3tN"
    "yco198iqemsMT41nNUZpHqc4X6vGKzfUGk1wwRWbihl2wkhXB7apJ6rUxkAvpU60Y9NcjejQf3Obm0ZSaUWZypLKQ5ucnWVh3gwE"
    "l1m5fYUsxpicxm0nKli3Xc0yyGOtdZLMghFymFrdKuUn3ndr0l+y8fsdoqL2hqdIVVznGNHD37NmIbmtzUsTvapdQhr9W9Nlqd3a"
    "1RyVCd7Php8/BaJPRsCfNB3rI8hia39KhxvtpWyqb5dacimb2iilJhIUalSo0HoYVt8Iq0m5Kox15+d8rXYn55uOGWqsO2aA4XOM"
    "uQpjTX9nk7mBlpm50ep2On9ai9hH3A6/vRWFIq0Lulsu9PfG7Sw5T4PZxW0b80QI739zRf+CPxeSH+8k7+nhmNFvArrHjeIsR0m0"
    "h1agZJMurACP/RKDYLaL4d0Br5EK+7b9YG/3pOWHt60uL0x8IH5727Z5RKVq+lHJhq2M7czmOVlqwTeWxf1AZt5C27i6F4xKk3O9"
    "0iRI0efBydKTbyHfPv0+K7P5FtQhxSy+7SZBIwbv+eVA8GC+DbKQw8h/K/gwzKPJehc30g1AEr/ErjiAnQe0gfHJ9l0iyp5IlFxW"
    "H9Xtl1ilqdCPqMeQhkAuxZNbM1yfKrTVXXrSV4gocsz2FR43d6KKstkg6pdQpxPULrH3XCrZVIhwQEM+bZAa2Nl3jmBwvbjEaUX5"
    "Uq8SjHnxYDbSF6OXX0SZ94BfpC/FYaDE5VJzB/z6Eg/N9p9PcRCPLigEadbaFWa629Jy9vWlNMg/up2eJhPYbbKJwn6Xs9ATaooB"
    "KHEbU4o/tMRLl3bAy54lMyy1aXaHTFQYUDofUS8DLgPpW/I3Hvg8wSaGEgblx37p0ZgLLzFXl2hh4cWydycf7F86uetGAMhQuCWC"
    "9QBE9AY2dZjmt1RBmq97YTyfchxRdD1ENiPnc/V9nUa5+L10e+FxfjKAKkX3+5cF2rpEUFC+RbzTYvIdNDRTs5n38oe+X7RAtdj3"
    "Ew1ta+AnBLV/d6ecBLRCCrUR9wuPDzxX3/hzDK4DaPJYTF6evEmjaYTI7gSDhzDzn2FMB6jhM5lQj33uMdV6lL2l/fwihRf6O+iK"
    "3Fk4/p//rDXcms6zvCV9QrVmKp051X7hcpr9B9OMDPn49PjwuriKCNOhwkh2bPT80oviC5Qso9OdjKLOiPgOHI/dP/GmYX6RQNnF"
    "eZi/eScCDVu2psPWTHDrwDrAYcJgrVFP/nIxNIT0I73g+4Izxd2hFLMoUX6h3RXKsAkYo9Mto9zODn9LfAfLRt+4xUJScnNEhQ9C"
    "/cz16PsBjteRo/XQoh/6+3YyT6t3pxf3YdJhP1BN1Br9Du8at80VXJbg3t3lvA9gL7tLvHGmszlFzxCjriColg4Zmk12lt5FkDH2"
    "rJZ+z0MTV4S7syMTxH0AI5jUVKVysumh3u1Qb7NntNfz/8fNfgfdCwV58MbS6k8TBzDFQtADxqpKjUWea/G15KlH5F/8QoEGbII0"
    "pIpIv0SzGeCG+COk/0jed8RFpWvjCZdLszTMsmrwmOKDrispQ5lJ0qVI0BrkFAzucil9SMFXcS98J5Cil3qRF/DWSAZB5PgMcYGd"
    "foidsj/qnxyr70YZJTlBUZq6kMO2/FmcjlBteaHsKYaOTh7l3i4ZjVUXLGjLI7WzU/xuBwD+rRPA1X1OBr1ZcRaEgYu9KSzBDeEv"
    "WzNADrR19KHGujBUw1F9R1ANus74hDVZtVxKESpgs4IQDRQhWlrWbWPeOBOL047GAKivtMjWZpRxJgvd6ghUlrewtahHOxckC9DQ"
    "QNKUp9AoKQLIy8gBckWl+icDRYUQUVXbCttMVt7dhW1BUtpDd0v992O9SU/1OJQN9VQ7J9UpEIAoiyJNjLnU9ElKc8qn0zKjE6md"
    "884JlAfQL7EtCsb95pL//niJkb6Pk5MTd3l4KYNzf3dJt/hLi0SUJZQ1ElE9c21xTIPg8yNQQRHg/10SzfRapwm0PN1MLGURjuhg"
    "2oUixePTGFK90LfUS6fSv3zfzm7U/zub9FXL7G1iqf2+y8hPsiHX7Qoj73IYkuoQxRoCpZ/m2qgqA+YC/O9mk681AhvvXk2sOVDU"
    "QaobJ3eLAHwS9Js3YIfdystW7HpTDm/Ua2Jo25jujbtyHbYN/ttQt/4MFXJZBcM6LJgy18VY8QrXRfFUCt6NwVypQozsF/qxPFki"
    "Z+KVwZlgpxgNnAlB45PnLY+/mBLkcGWU8FPhoYwTnksShdKmcN9FSL/JZztQxMn1i+ksr+VFdJjC/EG4Yd2A1/DZ2AgvV7AR9Jlb"
    "k43wVjxB6Yk5sLwv1eNScgeA0AqP4U0ov4H4RJ92HOqS1qQdZewVDUN5wHvkJ3zbohcMdxGjA7NBzNEj00HHi3SibSm9uWW9yIst"
    "pHz6bKACTS/GaLcIy9ITv7rSNOc4ffjwBGMBGpubn7UhTHcvWi4rj1zhfaMV5HkI26CVJy0eYYg36C79xmtCbfF/eRm3CAFg0dOw"
    "JUt4VD7ACWjx2zrjN/NFAK/koFWZT8dt8SO2LWIiB14ywHjRg61uMSHaZMTqKY9Ko3oO1kZvbjGcGkcR+glMGk6RF5bnJMN+ggFN"
    "itZMnt4ukru7uM0NyIej/EZPvRj9bnKLS565PJcB7KuCtfH7pcYVen9JW+F7/vMT//n2Uvf4i1+LdRYlm+Ej+h+6JgrInwp+Tehq"
    "HjjDgtMh2Sg/c1Fm3QwWy3ae8NmXKydUWL9CBXO5UBQhlvlWZW4ZM3r0FFLnxFCAUOcwmPmwPvjzKMz9IR9DjO2M8ZYpfV8+d6Dg"
    "o/9whr330d1LN87h11d33ad3j/dc+HkwCaazcOxyCw8etVEV0YndoRiP9AVRzAkt6sLOm6riji2xlUoYZEt3rdMyoC96ei97KiMZ"
    "fc618gLkBXKiBOfjmcQeGBM7V7jEJUeNvFQdLxU+HWH14m/yfvzwoZsexyeDEP6RK5XSQf2Lurfsd9arDflXr7W7zMZ5JbZHUWb4"
    "syM4FFqii6aJqi2+BpvbojLlttjnvNHWW3rJ4P1X1564H4u2RILLDBZzhIS9ouy1eTs3gyqLlaF9rsTMKDKQjb6V0gW9UdypxAFS"
    "F77YPoBsmf6h7Cg7ElEGoVJfh0SSDkMMxqixqMRegrPW7eXImWAguBkNBO22hdp0dzoGsxD2KUNgTg07ktJz5PiQ5S2ZvGXg0T/j"
    "wJx95jdCRtCXkyHHRNOT0r/BwBiccGxRXZ6tObKU4bpuh7/NAVnnt7jgQNRtlaYZWTBqijpi0jkktdnX8BjjYqBauwO3iJ4D7+ro"
    "xO3BP1SPgJWs1cp69oNBys4OomWZ2RrUMVgXMrLrCzSpV9a+wRKZRMW0WqhmONuxdaJD1z7NxsDE6r0tjzfq412M2CltZ3CjbznR"
    "ADC/47p0o/e5YqB7F4b1CLyYR6cvCVyvcNv3T+H6vIKbeoQu/mkZ2yGhTXGjp+0zuJeXvDD5AFozGNOWhtXpWMroDcSZsZzkWzz0"
    "Q6DQYnH4D+RLoqbG1lYI60vVDFa11n0dG1nHbbQLdITUyCxe2LnC9QxgTz2IINkQ5R1eQqUfLo0Y4CavV2fd/mZl3V45pnREzbdu"
    "HF3iYQn2ZZ2XixqO5RKjKufTSGN/WjiHVaP5UEx2VnD8NKlci42qEjYtCtrV+wRxkeaOICjhL3kjBuULBPOkEMCWaeFK390FNsTq"
    "zWN6YWFR+VOG3yQ5gBJUBzbsaxcBaSxo/SoQMsslBjGl+XZ8UwDsi4ikMgwTM1/FHMtoTIpnS5GYmrm2yoEB/6BoKsjDilmbICed"
    "omHQ1k6vw4mK3rPwcnX+KTpdQRcj+EiuGZPkmCLztLJUipG6bIj1Y3iESKSHWV9uAVPuIldRBkf1fLmE7EpN4HuODbRU/hu6T+G4"
    "usu/KL7tb8y3/avNkgU+4XUdVK1YRIbOiKko5osyNqV8mw6SUbys9q/rismCq21SZEm7GqTQOdo9nSSjq1INkde+tVUQNrL2Gjdr"
    "mLwouGrYa+uq1st2NlOr36BWVaV+g8oWdfqNujZV6RuravYYs1kYpMQJKskFbAYPpYW4nw1LRXNatlqrjy0KAJXA2LuivF9V0JVt"
    "CtX9ZkXjcvskBlivfdaWrtuYtUPdQEHcUsVQDrc1qSuGW/LXUwq3VKxVCFenej1lcFl8TUXwovWPSJ8AHsTQCs02Egp6KmlBaWu0"
    "X7/hVvRWZzCySZ+VTbiiT7ET1+hzXWX62h5X6MvbVnqlfrKErUceFS+SydiYcVubWsk1to6k4TfoQG7PDTraSOdW1gEyK/o9MEWO"
    "9faoVDqs0d+XTRoq3nWkg01de9VNXyhcb3DZa5VuGubO0NGuA9qmb70K6EJjegOgtUoa0J+usCxpwYrYjA8yaSLzT1Iarm4SVBRG"
    "q8q3tBGMQmurImtTvlINuUFN2sRdlCuSsDqnmh0qcd8DXd73d1MTWdHRkm96rmR9xcClZEzKwv66SqVWopj15GC/rKdO+8t/J3Xa"
    "X0x++a9Vddq//QPVaf+mqdM+sKrT/rJCnfZBIZ755R+uTvvLf746bXio1GkrR+rvVVFEcpqFKdw7QiKOwQR0zqaUJhKXmlms6jBK"
    "/VXZBMVO5azXIsnkSfw2D7N8P46m9CT5LgUo9QIUKRcqYzSNpeDMyrblD0fwayeoWjYnN5UGtBUQhcataNc7Dc+SNHwf00ArFWVv"
    "oprqHCiZEUdYxTaUsEbcylorkqMLAArC+Q2hHH0aKZPQlzCM8fIBIKYsfBnnJBPtSB4yFRylyWTyPRXs5zs78Tf50LE2M/Bx3L5X"
    "k/lgYW1zObvx3Z6zld/dxc9yV66prX5MZZco1XhJcTNMwXrTxHtl3juqjcI9k0tHmyUlZNqdFr6so5S2BXtS09cWtDSDLy7TWoVt"
    "r6Qe3cgLBpxoZwcLpQ3RJRkKGVBU78VatWLIOBwUoawp0mtVh1i6QLUxjuNDk3FsMogLPpWdS1zW5iQUwt6CGhR7Da0f+imdDVU0"
    "WNWuadT4pSKsp0s/6xR1aYcU0QPyQ3cZHkp2XXzImiWHdY5nsusoH13UOJ7hzAY1S6I2+2VqvzDd4wbki70oeFFxySFKXjR64+BC"
    "TLDpj5c6hzf17J1CpTE4zZIJnDWNn5bMDPVKoGfD3FBKNLIrTxx9gGaqMm7Uqk9hOaPYSFKv0U69nqXBKemswbzSZ3mFUqAx2dkk"
    "Kj0V62Z7g4kwNVbr4KtsG6U3iXuVWaSr7dTNNtd0TSQrWV/4G/kyES3dw5fJ+jVrfJms30CdL5NNQLD4Mmmq/om79d7sVr3lZhcY"
    "4gBcBPG4Rh26Bnd8oW91hTJNlfSVzn4aXQU1bloGeF2HLWalyvGoO6KifJkNUY/Y7eVtuLVSt+ThiDEm3z2yDjw9Rs5ut/Xv/Ku5"
    "+9aj1p67wQaUE/pZfBv9I/BBdVYtex/x+r2Oc7lm0+kpH6aKd4m6W6Zxh9/P60+58hruVzYbRAVTrHNMm8ey6rjaHG3UnSv7yZDS"
    "lN21Ts7DmtPpNk6gdHZSeD+5CDLHStaxsMH9xA3S5LJqxfZYS2T2ecd2r32zkVcuW9U/ZGx/7Hn/hGUtNfEHLu8/BFt8wuqbTXzm"
    "KTBMyNY5xU3k2aZ+xKrVqn7ELE1X/IhVy2zgR6xaudmPmLpipOj42Tqz1rjXN3EwprpfQyq6uu6nHfMGwermXd/reDVC8Jmc9Qim"
    "So2zHhNpoKRI/EQxUmEfHWvsJ6t4Cp3n8JH0bQfV93hpKrmc7Hs8IZVsTvaxbdz/FE1dzsdCPYx8aSfqk3grOjTdWhwJnpPkxVe8"
    "8JQLFLZueTpntqkwDyOul26SdhZMsoYS3fv42BEudkwjNZrGl+MmOzYqckAMRuGsRxRj2dGJrTjHp+fiXOwPdekjpYfp4ToOeXhd"
    "GiWIqww8PJ8wI/w9nczTP8hfieHaQp6fTT2WoCFCo9MSeer1Xhg0bRPSt9q1/TLzP6/3bELShe9wsqrSBVFYTGXY7ARFr0GTjn1+"
    "kmcUOb8rXaOYo2/WMt9g0bxajXTY9YfKDch6fkMSrECChKK43XeJpjFLLP+ifFWbverYRMVs87JDzVOJNzq0+i2ZNMowGpTc+UDD"
    "i00lNbjzqLrkUNfNPXxyiKsF4IrGJAchFClChlDDQO/JYJNS8mA6tqAW0LNFgTxP1JAKDOnJ3VIAvK4fFoX/Q3WShQjHNgtruDVp"
    "donSIBeSx7tRDERFWAxEP/9Aty8FHhRxKD/FFY3F/QivbSGqSg6LkCylvSzIEMvWlTl2Y4ya5gTZYmlO5qz2CiNKeovK1hMOT0aH"
    "/DcTf4NDdxkpSdzksDjb80NNpwVVBV7G+aTNZMZ3gI0DlH4TXg7yd8mbIM0zp9v+ApJgW2NYVdjicKbwQpTBJt2hiGcz9NuaCsj4"
    "0NRhaVGltr+zE2+JH1s5bMzRZD4OMzRsjZkwUC2cHbISySTMW/Hg0X84/2P80HWO296JSz8fPGqHN+EIxdhpNHXcwngXlUdgH3GH"
    "d3fidw5dwDZ9mD+Mjx+flDqb0cRgV3A9Ybc4VOSgo3EWmaA5OF0/hLenSZCOOcW/Cm/JrZIISZl7p/PTU6RLUeuGgjgqPRsJ3YJi"
    "1lItGDT1iBosLIn3ogHMW9yGxmQ8NQ+XzEE2V4TDaosYs8+ZlnIwoFmWJzPUAwrOAz4zXu4A7mYPZW+CLA+Lns6w+dEkmtEwnsN2"
    "G+K+xB8sn4b1HPq+1uuZk27xtQxLJ+B0F+sBQta82HHYwqDgLkyiHCle7EtSlpkeDl47iw8fmBZ/QeHXeUf6gvg+jwivL6S/Mvgx"
    "jWL6E9zgn3F0jrQe/KLo0IuluqcNUhsKFhFPodTSW2jWTqQcE6UY8hPIeco4TMbRWRSm2DScSklRzsuhWfFqhdWdFXvoZYR6U1oJ"
    "tA+HTYZhj2Yi6JTcErRYRZRTM7ZQGHOcnGLbHAQzqBX2IkaVTrvdDl2MNxcjGSVL7eyUEric3BFFI48tjVAR1QJvISqx5Mif32II"
    "Nm3qpAqJPWxtdCzjG4pyAyhJOHlXXE/j8l3GXrdxkcM2/EvrjFHmb7xt+GdXxq3e5YVnCgF/DYcdb3uehbtkagePjm18CWDsSfT9"
    "6czOgUqZn51FNz2OHT70W/5D/imsnNTOUbemLVgu9Fd8Cg0U31fqFdFxtzRiqesnwzf6HF7JH4oU8XJSgcdKQXd5rsrU3RSjgPow"
    "IfxveVowbBmNnOKW46i1AL6iKW0YGDuJor3iVr9QL2cMpZXtjqJ0hA1hRFk4VME5ngMzyx9Nkoz+cvhadGcGhwFTqKB/Am++j+e9"
    "xc10Ag8t/yLPZ71Hj66vr9vXj9tJev5or9PpPIIivgjotteR8dzg18covP42uen5nVantYf/80nRp+dTSCWYO5gygOrYB5wN1N0C"
    "VuSw22l1D7pP2l9/2XmK3ne+bn3R7ux9/eQJ/ux2DvBfmSv/Ygb8e6CXbGltQC3ViipDdX7F/vbaX0DVr7748qun+Jv+r39Dffrz"
    "pN19stdVWd0vKY/+HshMTvxSKy6KHdBfVVdkcvP4ByDZaz95+vWXraf05/EBfH/5dO8pfHe/fPrV41b3cXvv8ZdP9O8vHnceF+Uf"
    "t7/ae7wH31htryW/v8Rqj79S5b/EP3tfvup2252nHez/lcwSIKimJAjqW4CgyvPfAy3dXk8MTZR/hbPGvb8S0KimNGitoxGjVeVr"
    "Z0fNnijPILz6qv3146+f0KhllgBBNSVBkN8SBFleTniRbq8nhybK46hF769Ka/2rPBijeYqckgNkw/pszvlVOp7O0cM1HMZzungF"
    "fwxP6IE4yWVOirybzfOu33gLMhvPl4MX587FobrYQqD/xMVGwRxd7yZ0vg+QtmXlMc0lIGKdDxZtsdFFNKtoiWHi2k74NlJowJZX"
    "izeolMXsrCLO5+bq5PcW2wmqsLbRhFHaMOlUIZuoiKbIYDox4wZ2Vxk9UbHVlk5YrCF8ArVSDVthsTopSpb1NjS1kPpCujJIfSnc"
    "JbvZRRrFVxbXcDyWaXAe1rtCNPRtKpBh3WYNRK3cRcXwWGibWETppG5i2yybDY7IiCbTaGqeSq1pHF2uYI/NgKWkJI8ASUOMFU4b"
    "x61GZJAzEBqbsXJEGtqnGba1XNXksbVPWjs1h5ahWqdqafK1Ma+j4mibaG5ivWPSVLayI5sKl4+zXnYVQjSOS53uUlUjkPrZXBOw"
    "vtr6inz1i7Z2gKrKLK0vXG6qqguYG7vQhMxN5dYSNDc1UBY2l4WWvri1DfEjnUyZxee0iKyhbhMtokaBuHyPAXmpl9YWiCJtfFTP"
    "mAMiIyyCPzPj5oMU+E00AZYUnzFboiI+QwiapHE0yIYCBDVxiuolg9pgrS1Jd3CCUvqwQqyGo76fOI0B8U9IpGJpXJwIZKJoZjrE"
    "h4C9bvoWAkIQqFLk071AdOejN2qR8C2QGXAUR6HvCjsWel6SuyL6VZVNiZ7RAZQueRIAl0VJTRKhYkGE3E18LmUTysdQQTb3zg8h"
    "89aQsJziV5aOdPHKjV28EknwlRtuyU7WvXDr8pb1nASt7148ZEpE9R9Nz7X+YRQ9UUJ5luHz6noGx1skLgtu++mh6/aU95xIuRp/"
    "6ew7RrIru+saw2Xv4UWvpjNx79inwhScPdSaL3sy36vxZB6xz3J765qrck+wpQbMDR3K9J5twR57Vk/mohPNgXmoOTAnrzthsd2G"
    "+uLxNhZ+3/njIJhMkBxHgQAeCXzi4RnT0tW5s624tgoFehnyrJlPQreQa4jpKyr4Cmb6PCnkYX7HVzEGJIgFIjCAExOjt1pdYfIX"
    "hK3RL1EX1x2WT3DvOno0bqh6e6it4PKjEorcsHnSkeXBSb7h2FVy5d2p5X16VOwm7+YNjuPLbzMNpo0iWhv1Ps3Dj97URvrlG1as"
    "mJtsWL9KW24MgEFirqzdyBuwLMDnMTXRG66zNNHKWNQsVzr60btYR7O1qTsb/6Gxw82c/1RrrkN719TSye66hjWKu6bIWsR2Td06"
    "pU69+AYOe4xeVvvsaepljX20uvPVLnyaQFiDlWXpczVjy+xzHV9Leo311GLNPu7pK0hvZC2tVq3C7hhePnil2q62DViqKy3MbLyp"
    "tYLB18yvhLvRiMxaod7Q0xYgYy2E3RAfY2V9+7IAARakZU4RrwCUOKvOb800UTs1nBrDbCe07ibrnNkhJpKW1j+A9tK13CsVETLQ"
    "g8EK8qmhW90H1AXs0F16RSIRdZ0GszXIsnoQUT9it8gOJ5NolkVZ3x5D1jjPGkuwLu+mhs1mLKGVb67zbM1bYx2mbaWGnWtrIArG"
    "CszQWbEI98EgJLxQTNW6ibTxViuQQNpKx2NGB6t9jtkvg8/R+QaOz2puixWLUYdAV3iJq55tDAJxu9a5JrZGNKGLS8+zt47twG7Z"
    "xOhZu0Am4Vlee6OUBy26Wi3ss1WqYXU3vbFUf7V0a+MLoVTddvHU072ycpXonUbxboOvPH1tLsLA3MX3Odq1KHISZfCUoC7qw2xb"
    "wGkLJWIYvgaaKTyzXmjsg9kUjdr6YYf71tvMdmc1NbKef0LjtEUYxavxIl3VNTZRmRnjlNi8g1DH9JTZJXZz2Y1J4zJaQrnX7BUi"
    "BYUzdzzjcCrm09gixq70sXLdeH3XEa7BBXp6FeW7DUyXhqzGK1hsss1vYr1iRXCt9xijsu6kvx7R08Ryqkfh977CVx+5xr0kilt2"
    "k8S2Zf8zdVibG2p0wWJ9cKzJ/6INKTrZiP+1YcUK/2vj+gb7asPaVe7ZygbWv924kQ1eRcKFvuA5VHPEaUU2xDoMpyZCQR5FO5dg"
    "9b7jmmvQVp8wpo14Lf/oETUPZjOgZa17wa0qb/aQKte2oPP7D/9+u1GD5b6LWGpi7dVk5WrLxWo+3JsIjbqLARu24vvVE8J17zMP"
    "XPNeO4Kr3vt216qvfnTTk2t3GmaZqZNWO6lUoS0qrEdT83uxqmDZrDC1+oG+Sm9qvRZW3CH1upYNg9UVxVzbrK4FY3OpmzWYFWX/"
    "5TU015rPhmy6ihPQsDk3cE9eqra23mpNvZvmBauOSnGs2xW903sMsIZbXFf8ogY32MrX7MDzT1imDRyyl6rda5nsbtnXG9X9lqlu"
    "gDXLVFe8bpls5YsBwUsoyJnXFcUrX/NW/NiANBqx4sp6n8EjiK7IoGnkSaf0+GqcoQEe+gep4/wKZyD4jRpbrKi/mbOQjXzZE5lC"
    "Eavxh2yzgNbuyN8sUWoCPQ0I3thPrH7lbZdJnjDGCs2lSt71y9nrhgconaKVEQLQ1wrt0QPJIer5jZIYqUn5KftFql/i1tAY1Th6"
    "pR+lc7ArAysYyNu9LaMo2QSLtcOxkcRKKnjaRWJwEmDfvczDaaUMqY9Chu8JfUdLAVHd1kWhfSrRV7mITIdZTQI8orZ2RFapKVtJ"
    "mSeKih1XLiU55IYeLfNCy0U5FYf/HSGs2l1SZnEWVewlYcDw8q/fdAbTkgvbyvgiIvxfkAyujFN7a8iCq/ctl/NSSkdHDBH8Og9z"
    "3CDC9B7DbDfubxWlb7vx3YYbXouPGLvomOAC7poJ3jevRZBBG+JiQF4ifGiXXkThoyQyBzbxaF4NlRi7eEDoFB0yhV+eQOO9YHec"
    "VHV2U7hSEnOEHhbgVnqXEKYKJ2f+sHCypLSOUdf64FCPJXKIkBwJLbpqOBERp7JHAZ49LWoyu03SYobqCSo4sZZGm6dSlVLh0E/G"
    "aciOBTzd475dh9rvPkkBXSw9DSXJMmt4XZoFMWBizetSfSnd2ZLhJ4rLiDO+si1RbkVrItSqmIWL5PoAsWeDrnmBdptUzTHGbJgz"
    "mngdr2qTEYfK4s831XnmjFdssW2kHaIrhsNkXKNK7wuEk/myM3ItJOePN1rJT5XY2iucZPmnyfjWRy8D/CSr6346DaCURA+IcbJV"
    "XrDQsF1iECqbNXn+4qbxpGBsksaSsMrsOWt/MqlbFVhCcTk17QUhW1u9HYyrrbEkL8/qcvqtumInotrwu+QqXKN3deE3luK5rp89"
    "abmhHYHvo3GTBcfHKM3nweSI0BCUFxiwyePaPE+4GLvrqW8bSzIYq0rSFQSwIupo2BiVe2zl0Za3UMNmV/t3jbJ0ex1tWuG7dUEx"
    "Ls6GciWHfMfitHHZAkV01nN6t74PPWnHc7TCjke7ZteMr3V9uFZ8revD/0bxtWjMhbOfd8KzEIWfGoh4WlfhbSZCxIsUJMuuYxlh"
    "i/vJZNCppjLYTL6z46SDtM2HowixlKshW1t4Tv44ZjBMArFdRPJaokFEezbPLoTTK6ByZUyqVlwM7gWtLzreYQK528+/Ud6x2pMw"
    "Ps8v+vnDh3L4Kg/jgLFly2LZ01P7+Z/2hjBnDDBQnmhLgU6iXgSjC2Nkz4VtE1Ryl25vxQgzayizKIT581ZVBSjcng6THaD6WGmr"
    "Zj+G2ccYWHJ/FhP8/LASne314T8uOtvrw+Lxc3Voi852fdgcne3qUEVno4PxD43OBj3+Z0ZnU5Owr3tCe3NIQb9+5D+H/Ofy0NHK"
    "49eiAuNLofwX5DneKK08aWUzdO6Hegm7hBfROlg+Udv/8jJukYACS55ChijhUfkAadQWz0zGI74IYIxB67iEaU8ct8W2lTh0BeRh"
    "sbLsR1SiwGJO5IR/x0V5kQeLJawiz5ZYLhejLYxC5ytvt1t4VsPJ5R1exsq8JfQUiluFbq+gzmEwQ0ds+PMozP0hUePtszSZQk89"
    "St+XGAcKPvoPZ9h7H929dOMcfn11131693jPhZ/wJJrOwrHLLTx41M7DDI//UIxHvUjVnNCiLuy7OKzM65ZwQBoew/6Tqb5IlnNn"
    "QF/09Eb2xPlRRn8hTZ9zrbwAeYF7Vrg9fRYKDE1B4Abqqy/xeTzoeOmAG4bVi7/J+zHg8vQ4PoEDGZ/IlUrJtdpL9SS3PscPDjd0"
    "mgt/KHbfLr4viq8LIE/QxxQnii/JKfKZ6oNNtSsaPYFeL4mkBALmO/KdtSgRP8k8z6AZMvZ7FWUAroyOKF7x5BJRJHGAO7OYZJ7R"
    "B/Gf6FeJBhdNIrv+LYJG/Jfebhco1SAdXaAFJEAiSlESsyR8X9CyrwVlDjNXYw49wiGgT7muJ7g/2k+N64O98pTpXA+D6YzENtAy"
    "+AwuGCi2uIvsgw2fyhMHLZYtESVryq6IzTiPkRp+bVkcGV6QS7w1VkTmGUu3szNwqqnoVi1Pk1uHjT9lAEqeBqzyYcxmDI6eIQov"
    "DZfO+twWBKeXmx6DSxtCMpiGQDgDRYpokMj/padafFVhoOvtaZys4c+OiC+oJcKNrrXFS93cFpUpt0WJsi36qIIl42BqNQCvDQxM"
    "hr/7mjNpc5SOclHYeu9gXMp3E/gzlI8ZVfgt2dQii6l+ogUTqhiISHB79o4f+h8eLPKlT918T4zsA8GKaHLW3ZJ+uQ233JInw30B"
    "KpI8F3LCDR00Nc3G+tUO0toONK4wXIDy2AuX1zYOsDEDzARG+rPkhLrCA0aPBgB/Ob12WhSzSbKQ3oZAMBf+xQ24h1udnrZ/1Mko"
    "7cTnSgENWQESFOboV+HY2tL3ZMG6RWJCS8NPYvy72i7TGL2WAZbAKgpXmlBc4TVbkeW5oX14wb9JspdoL2URR1CMXkmK2sAZhru6"
    "swqx3QSx1fHQ+27pxagtYtuYX1x/V1AIPTgxXeb71Tpt1+9uE7P+JD1ndLy6XVq/e3e7Q3WbaNwq4ZAe0Od3UZrl31WqOuLoYxG5"
    "72zZlYpeuLPz01zEyE3DM1GGXG+6yLoahzUrA8SofqWVJoYIF5iYyqx0PTSeo3ucPyzzsIvpGo0wABohb1f4g0jWtbV7nrGxHJFl"
    "OH1oQNAhepzmGC/rjtvgqV/ijrs7R59HtcbmIGXM4f/iK7+l+tO4ncI/DBMSL+OfovC6bjCuGfNAhTFYI46BvgGM+ezWnpldkVXe"
    "Fp8cFoHAhcvzedmhjoaE5PVf7AP6FDx1N6w4cO6HkywUTKGwjY5eoQf0yDPK0wn87LPffAcfeWPoaxRkIbza4EWMYPjisohVClRB"
    "AuIUnsNX/aLw+5lZ9P2sWvD7ZBqqUvhRLfIiHqsS8Lta4E1wHhqAyQR7UQ2s/4+7d9tu40gWRN/nK0htbQ2qVYRxI0iChjEyLdpq"
    "izRblNxuczgskCiSsMAqGCjwYhBrzdN5P2t+5Kx1Hs77fMp8yYlb3qqyAEot95413r1FVFVeIyMjIyLjwo++LlGg6dDvw9nNuD+w"
    "3xxTsCIzpIw4onwT04v+2CpFj8Vi7/vnugz8LhY4vh5eZm/jy0x1js/vUF+v69Erp6aSsVA7QGuIYjeUeIVB2ZW6xnc4LT+RfkYN"
    "CBflE+mmP/aXdfleKsx7a2YJITHwWqEHO2kOi/XkxYu7EceNQhl53UvLeNfBOadFD9qBKvZ+7OsgWOS2OaVB0TYOHMVmCZW1dxfu"
    "GsmtnvWvDkECR1C/OTz68D6yviE7AYL38HyWxRWJGnWxMWUGLQrIqAqFHbIHsepRJJ0pUI+TXJ3uM13+2WkUKNKv5Sf7qaruS3Ue"
    "+Hx5ASeTczwcKxjtyMAWngS8Gmh8ItFdcAnA3KU+OZUWinfJ+kTKH5Z05uHB8gO5KRWPPzhJMSDRCPoZvKeZKR47f7z2vp85Mw4j"
    "8qsQsG6wHxSbb+Aqd59hRplnp0EkYPBwHyjBfJGh/fInDI03gFwXubIa031ikibd/H3BN40XL8yNQONUK3l79ltUYQyLdZt23aap"
    "677G82rde2IVxJ4sCHi8/W5ebEHp1EoEVE651meIfkmeJGV4xxL/PuujvzJKp4ugc3KKW+Win1VeHVTs1h8fEX1PXOlNtXPqJW39"
    "IMRsChv1JfwWkL/hMgbXLORBCnUPAEFya2laloteFUGP9G8efgxr5fHjXSEvlcNHF5a5bq9n3YsidUKRfwK9EEmSrsBPcUvARB4C"
    "vQCC6OMlJyGRqYmqNXlSrQQv22SheMF4+sPuQT+7xpQEdP0W9uW5f8/PabdcuBuG/Zf14F99mKaSzosNAK9LFlUfLbcmWZhNeLOV"
    "PK7iqEXrO08nw6th0h9RppROHPLlV7YIhIcvUbwJpua+Cm//PuXVEbmHuvJxwX8qo4r4VChrsWL07LJiuoi3AT+zmy/l43eLZUoY"
    "1D+NKaWoemYxXAnKJkR5pDF1WAFdVE57eTpyOf6Jv1SYZClTuTy3cXRXZZSUhjYuOHJgATMZ8+XUjEcLu1kfdhneWQCn+CoHctiI"
    "jWH+DH/uJAOLbzXSWPYECVwYsJzkXSJyP0EqP4zvndpl4vRuDMNlOUNDoXCIKJ1a7p4FFZxPOJaKnLoGLe1IDzV78tnkvt4lwag/"
    "4tmsZ0HJrOVc8ExXzdSl/ycl7ZwGYTmmE7/tFYQsMf0zEAO505JFx0/L0eIIxvIl0SLxIsZqtEjUKbJM8PMgjsYcIcYO7nwm1izh"
    "5IBrwB6FpucpwGf2Z45sSe/BcoQF8h4qIjOt6Wdg10J9xmszvGOEe9Cp+MvXgnDZxFZoi0KL0SoSIwdBkqU4MvlMHJk8AUdKiAuf"
    "r3/yehGxUUAIfEtQsmChcGnaNsAmCM6nXV+rCe6eJQezWdiJf2GH3XJi4qzr5NOPhOHqdR1+/rpqxV5RLeEoj2te4hE6KsQVTfjE"
    "AF4U2DthGdpl+VtULy/UW34uVWxKsAL+Htrd+QLnGtKUFfJCgf8uhYpiqlaBRRFipamC9goJCcs6YX72SxwHfh2aOtT7032lsXk9"
    "iqlOJehVSC3kLhrL/SNXl2TV+0mxqI66J6cW85X36j5L1+tfx+tYMmfA9zFKg10QDXJUo4wNsvh42lrO8p4NkDZq6SAKZTrP0bQw"
    "vp2RKdvl8Kr6B7VlTE3ez9C0wGScV1HpohCj0UW1aCFTdWWVsEgjVLn8bVZO9cPOEqj7QfHEquSY7sjoMa0Wr0+qyO/zm/7ko7IH"
    "F8lEhvXqEprOwUZgvMrQB7+zeO774jcAEh0BX0Bbw3gb92/jnIxF5u9VCdVFotq0y5n+wk8yRfKPcZmZkoxS3QZbWNsVrysHfMXB"
    "axslhLWNBUUDrIJv3Xc5ra+SStUO1YH8CDw3w+Tv6Azffa1QBkq+jMb3UTgqawiNvEogZ48PGYCYbxK5HU95Tes837q2GXZc2Pcx"
    "qnWtaqS7xdcs9yzCAewFpFvV/oCz7eplikSQL+2aNH6YCvYp8yxtBa3N9CDYwegzxqEs04qouAzYjk3c42MXUw/vX9lUQXvX2mkd"
    "fGAWePpM8Lx7WMGtfLA+Wz5P4/7tx5BwN94ySLi2nQrh3LfdpSBYHwwqDmbdwQDSOw9ecatR6OnC4FP50D3VEIekOy8GLetRYU5+"
    "n3j0HR9m6jDGDS7mR+uaIuAFSf8mPkzxlA3kVgXf6xtA/XbFTaHpSB2HAVtFkWnTtw9Fe0bnzqDEIoqP71E/U/ezVrFpYBuhTenK"
    "hZOR6160I8Z63j4KXbJno0pBVw4CEEwjd8+jbdx7PoPExNgpGnNLtJLrRWyieFx0+yyg9VfzSvUvvWDxVSg6vaKvqFqdPBfCiXyr"
    "eQ86NeiY7eDx+gvwiNyXYdo3fVKDBye109C5FmOO9mWEl4XE/mpX0RXGJNorUlKCB865njf0LupaVQb79YIhZlGvZX3tnZx2/jcw"
    "TEhQg8Qb+ad8PAL3DnXXI3vsWgYWT7yfzAq3kX57CXHZlpANBQV87gZ9EfrkEE8qrL9/7hW0EplqxiKUvLeX2Kbml0v7A/rNg41D"
    "i9CqQoleNUvZjfxtehdP9vpTR8bgTwHLEtO/D7PrSt5W60kNEIW2hu6b4AeajxBkjxVv7qJbGXeapt0ryk+BYcGsF9t8jSg19Rtr"
    "C95RRQf1QtNMOYX33YWbPPeFy/PqNL2Jy7Yvj5K3XYBexkVFYgnn4Br45yhGMmBNkscjM85BMNMd5xRdy/s9G/nUP+EndZi7gCmH"
    "ePz1MlVTr/w6OubL6AI4ltNQvIRXB+U30H7yEtpBPwTP9cCSQX9T6/mhZBlCh587JDUcz8V+ycKp401CD9nus7kKqMcVDD6ZnFLI"
    "mdUYlhQX3B0bcSqxwfksjIs8C1J/tH+AOQYq12IngRMpCXOnilr93ck33druZGMjILuJDL1qtOdH9VZcJjfq1uZ6OszsTSZw633+"
    "jsvBI+N1NZvvnxvXZ+zIZQPCzbl0QF6yKIOBhf4XbNnc8Mu3rpoT7t1/Zk7/9I5+yoitFSgz3fly18EwR9O/O9tK1rPNj0pgVyHv"
    "18S6jV2CPOQHG3Rcq6aykp5my8fQIWMmhzKWWAD4d1R1GXGoaLkp/rq21PwgNpv5k3p+eqfFq+14ETqWv2XiTcFKv8ALPj6CsPSS"
    "zI7FL/5DoUyw5CqYFivpPpFA+lx+hIHmjVFJlhiald3sfE5POUwr2dpfssdO8rKsuVDZ/i2DsmsZWGrrYuz7VhsbOEbk4ozz4gWJ"
    "XMo1p1jAV6nrd+bxOA651Vhq26yh4VvZSEttQPP3OdkyX5/yawrH4fmTboROUZKxm/Tv9tBDqR2SXPMahtbIMJTpcwIU8/3w4mMl"
    "1wEgBCNxnJv0oBM9n8fV58PBgt1NgZX6Ay/j0GU8jEbDk+Gg++z5PFmgPf3upDfRsMlSnMqLF/k3lTkH3o0SPqMiCbxnXmBYjzL7"
    "R7xoz31CznC5PWTJ5AgrWKTIXRfZC6B435wT10qHsOWbqxRlCt2su5y3Rf3zNtWfcttY1JOQQ/1JfIo6nJkPFGbbYAiWWDpFtsVW"
    "cpWqtrSBK5xzRpe5wkVUxOBJPJhd2IIwexyzxbGlnnL8UUEkUMfg8MULN+bEMOgBEmOwoMrcjrGZhORWi3FmOKzVBEj80Bs6RzPE"
    "1AqiEaItPaD+dIG+GzoC4bv4svR6vgtlcTu5ZTSw8VMXHtndvhAmzdtyrgz0YGd2d3GklNh8EWW0Fh0tJZuiOd9dKv1eZp8FHJYw"
    "zNeyX+hQh2FR4bTr+vVbjs62B5c1xHDYPTFxQbxrrax9ShAtW2a1nlSHycVoNsCwTaRGt2j3kPHl9QH+b75Ai0/49zv+LaFpfK7W"
    "Vggf7/dORFmHovAVRhPCSwhl0mQt3NCKjqU4jkU+/rGLE8ZpkiVpoVmuXG1Ipnh7GTc0BXT7SWoBia4FgWCdFV+U1N5r0KLwk4WA"
    "kIF3EN+UFLbFFe+thMeAVLXsqMdtCpC74CFioDDiA5DabiKj6iXV39JhUonCNeWHZE2VTcvWPDAwy4PBGZ1Be9TST4TUp8AN7+lH"
    "RfVmqWJB34N0JWTaB9/xFGhvBodrjoEuPpRpQ2wVMF7LxT7/J35teT0tlF+eGhfp+MvUxq7WWMXbDi11b1lZOyQJzrtjh/JQwpbE"
    "XS1pwo7NCuQpHyDl1IqJmgtTUdaiGxb1CUigfO7ciiqQ5bt4OhtlcsH2HsN7lKJgbrl7Ngk39dWNHCxLJZrXFlFYrv+RdSwGs8SG"
    "cqE2S8ZWHMTKS0VcNV0WLzT9/Zd1Viy9okcJ7ul0u7pCrodIB/p9pUNvLoWGFW14RXcYprMntdxYoSvB8AnzcWaSv9ld1lG+7Cde"
    "GltLfPwJvXorPG2hff2ru+8n9Oyol32AKtlhuXO7Uz4N2V052bAMm8rUO0gQQZ7kMYtIWWKaGHEs2GM4ojH3yWfcY5WEFV0vHiI6"
    "SAwwXeqif+WWWbo1VpY4KdzgR/poijrRLDFPpybcM0gCf/K4SNrg9lWvJYJ4sX+v36KsB1+pUyi74rj7ohen1CBBb10kXhX7znzD"
    "O9Y9FXtdBX0rowEqjvsTzjv3JccyfPHigyvaKEl8oD0x120mFwUsMTn7Do77I8+4fh5VkLWX1C5il6wSvbihrHRaGNoaTriX8NJA"
    "RbKp8PaXV8XcMAuRrmAjmV+ocyJef/lo+X9zO+A/z1oymeRZVTa0oPis7jKUTNA/tjACdJH8I6q4k0bnSYsqUkeBmRWa7Bb/ulvC"
    "NMNgiCRG4laRS8diK2cCN8j7CjwoXRbRC6ysHo3TSdYfbUQvHWPZsvcBanYklfAtpbgYjsewTsktKwcoVQq8JlNqOm6O70MV+K3z"
    "8X34cy445Ie78Ih66vz+EFICmduDECdOzGvn1V1ITVEs+YO7EJW1087hQ8iMTefjHbZ+OwFAoQvpd3fh8XiYoNHgd1fcb+f9nR2Z"
    "++3TInO//T8pMvdbNyTqu2Js5T/+hbGV/7BiK3/rja38dkVs5W9NBN63//LYym//Y2Mr45h+PuieSCSb6DT8AZ+GgyiMFD2EnxaB"
    "gScVYB9+ImFXyaWsBwqVr97E9+M+FB+oZzyUYLtO1XOfNv8gnl4ATehjaiR+L8cQjOmDM8K/H3TnH0HebSzC750PP+qhW8M6DX+X"
    "16fhX30F5EHxturZmr18z9jwlx/RmQTjCcIzBs8hq/JIwnugsSHCj23urIbljZya5oXu69RQln8cqDCW4TDsM/ak3Y+VCKlaFIRT"
    "/C3UCR4v+BNTRnge4bMmm/BiRuWJzMHTQH9GUggvLumFIpTwYowvcuQVXt/gayax8HTd7Q8rERNts+GOKkG4XwH8uY3CnytAFi51"
    "phfEH0qD1wEqdA9V0xQHx4kTQOwxrwSqnexk6/Txseth0ar5UE+YzCn/TgLv90N9+wSn2TOG+7NOv+pySAt0tMpuhmoUQXjy1kxE"
    "DXx8kVQibUzZv7gAgQT5PnSQofrkiQLfCMB6PDCp+TPXENPUfUb0jbqjtEUGciaOTBQCk4VJsiitEWljOxEGM41CjF+eJqMHDHOs"
    "uZrY8Gw2sxQ7zJHOlmFK9zbqHXRk5Q8hrH1MuXLOU8St8JnZPM86zKMTX2J/IALgfKU3UgQ4qXE6nsECRMjcW60qWvGsMyyk73OI"
    "R7FAj+4EX0ZnlKZMZAWplScxWFt2IWq8cw31CzeOTmM6JyIuBf18fJQCKrJjdlIrR1q5RNM/vSgqoQ0zck8saQhLcDv4q6SZH+MH"
    "yoOXnTTKW5KYGdyYPPja8+E37hK6qKu34fAITuFvEHp2DW53N/GhtV/yH/wbTzcBW8naw0ZmcNujZoCMVp9PR2k2DSM6HCPFeWir"
    "wPLdsQgL8DqJHc6fMkj1KkzyDkM6mEBCPfmj8r4iI3t8FG49COsAnnaLbuXy4kOujTq0Edu3FbG5qoh99xQlY3Cm4xvJemzMe+Oi"
    "0rXmGdeT2u1XC/cCqqloCps8gnM81DDCikEHvqP/le6suQh/q5hlMpoTw22uOU0CrmA9gujG83nfdw1yhqYB7imk0lEiQiLRPbtM"
    "J5RSSbDJfM8hFIuDgk+Z+BnsAX+HOc19nHm/avsicLQUH5K9q6ShoP1dhQfJCTFxCHwf5pucjIDEm7iqsmbhwubSbXFB4qvhxJgl"
    "dADjiaF+hhgi/Ca9jZ86i3CcdQRcaqQETCyHwQ0731WK07RgqX7QqLFCL1K/ok7E7WQ4fM60mQOOmiqCB+8ZP38xglM4hs+QuazX"
    "mo3wJKKOgFdT3KIBMTwocBHz905xfuMsOsV2iBZCc/XGdqD2xbcVADhguXwG3lZIZr9a1CT1HGTTcSULs1fVcPr0oKdNHJGO7ehD"
    "NdqUbyqvsC3VTi8aAtBJOoY9rXk43Y3snpNC96HVyKnm4fKDUNvKqqc4Ix0X81nHmvDCHDFmQRTffQqwXYRyAtcMhMsOIZ0C1hw/"
    "5lVgkV0H+vLOC38r6V2E2hLfoWGVydFBIVo1F6hOm4BSw40pMPtR6LR0qhgqOo4BZOjOE5lT0BmXAiETWlzzqeq77pBDt2vsFonE"
    "Z/SkFyu/RDZgFey9kLV1VyWgtfDXLt1j6HYiS6HDuOyA2e0gdNvwg9dmPQq6tQJKlYEk1HKrDZu6EIN3lZtwrnNdxlphBiRVhQT2"
    "0dN3lYMUp0gJZLSg0k8urtNJPFB5iEm64hACuDPteAsYbMkEGLC+mrcYLpX8562v9ELVLXw1bzV0skk/4WgMCJulcyqw55WcfMmb"
    "BylUv2psm0SmhGU22VtD7WpMj6fujjPQkTqUy9XUocdTSzDdLGeo7RB3zFXbb1ay6u2VLTscu/tulchr63L1gujJM+etKROLoE+I"
    "URKJnDjGsMDAx3M+Zu/+WSVHrxUdFTGqgxJUbTGruUTMyg1aJK7c2ydIOcZkkue9Uo4Pn5W4W4qQr+hwaJNBlfi7IJyorEH93H3i"
    "gqLl2EljUbXr2keoIPTKa7Vk79jEX8ZhqTLkBZ2MT+qvJyT5QkSR8AatNtnRvG/fMGJggf7kAUHmU1rItRFa3vIvV/XQrxavRnF3"
    "csBUXGw9Ui+HCwwr8dAlmWqQj3U/oZosndzssQqiM09Skv77GSmngTTn+dzMOv+Fu2Voqgy9Q80N8AFWWihQoFTe2FlVfoXqwMQY"
    "4/ALFo7waxtPGi4SheYYNhXtfu2MwfbBCdxVkOcRTqSj8B3d+LiVQ908HmqfBt7qsJx7sNlm4M5BCsX5Gbxy1dWCLnk9r8INl28n"
    "Zt3iGt298qZyGTrTN+KYxOe1lRYlaKblokKVlef5KFQkWIcUisRueeiYooLMkAA4DiRvGNM6K1irKqBitxYL+OeH03L1IwXLnCdu"
    "Xh9w+Mxga6aicrFfzRkLkVE8XgyOYth0UXp5qWrAuTdFjZylAizV/RX0e9bZa8Aip6nSxJkP+BimrPyyXjNueZZ7FdnQ21XUU5G7"
    "lOaFLJTezvl7Ge8OsDC9eOmBUFtyDaPBQr+/5XSCMnO1c4BVHYTzpyE+UoinI799OjIeiIjgF7BMhvLl8pVdUh9y5pVXUJqF93FF"
    "0UF/JavWqVIiNJlM5YmN81Et5ZMpUn5eDbWJgOfCzDiyg2AtgeEap6Nh9gSWq3B1sW/ZVT7l4gI1eSW2mEFY37IpOEN2lZSOW9i+"
    "OmF2fv7spn+/cR1jrO5nxBKV5AJUkY2oJIivhqnLNQxszbvKWLG6hRZBksCafhMiOPHJ3jnPmqnB8jg77mCsBOUbdUM6S+di7aPb"
    "/HUcAP5iWOGcdkmWYz1UeFEaDMsyE3iUwigipfBIMwin7LKCSk41h5Epy8LTTEqj9Ztc9aGoMBtpQcGrYxM/Egl6QjdYNpF2lR74"
    "CnbSqUBwJLiduyW6wcyoErqGUFAJ5u7h4RinOetPy25pm2nr/lZJl6mYRSfdrxZzKELpfjEZ4BT1FSf9gm2f3sajoUWcLMBEL72t"
    "5bBq1ptR2DhtFWfvHssBA+DJQOR3kV/F7VTIabn5G3khoRMVW6ZntpOHeCZ5h+2j1nw74kkTWHGaDeg+QRSlvx8A1fgxqXigV/9T"
    "oGfNVeaXhO4e6aAQ5gA3j4K5EDdAC5851gZYxvEKkO+KLPD3gjOBboVsErCQZZkqH5WFggzDToJY8WOrVm1493HRcdSP9KFkFNKm"
    "EMub0wlRMNWKfxPlMJZKFeWJLJyGiUJW+8haAmvXIMO6FXYNhf3zfJaz3ihZqwWdMBea11FysDsUIwnbp8PTmGglyJbCZHzBLz5b"
    "kJ0UBVmGsy2joppBPuIxsULG/aT6BfF3UhB/J08Tfyf/tPg7WSb+Tmzx9xOwNr9CnyALm5sqG8HKZADm2YvU3SZ2OjNuHkk/kcrn"
    "9Ij+I+etuql3TgRFLol3VCfAXw/wZDq5Pj3lyzR1sxY6kjBelqePj+mLF6nvftw9dW2qbzt4FA9NGbRbKHdQ0kedTqf84PO76liH"
    "Hd/LFy/8Tc7dqeeK3j0S/4SprZ5U6XRs7j/88cDgrqEoeIcEQg5fXkT8FIWXSQlbK3DY9UiLqq7OuJ6wREa2AbVoIYc+bIR6rVWD"
    "nSOuqRFtk5zpI0lsBXXtZZpmn6qu/ZwldUS9+p8i6r12keNJop5nsbdyQp3Z+n/CmI9dT6SnDtvjwEQjDwtXHk+I4v4fc+PRKr/x"
    "yGUx5AuP3Msn3HfocD9f+LqDtv73B4UDrLngAw73PemXOAMW/jK3jvRId4jmAz/m9CnqplR2bfjzQbB4c1CdkKzW/ccBmXH/IibE"
    "LVmZKL7fmJBqeBH+etD9qTI/O2My9HowzNLJ6/ts0o/C8SQdTztXIHHDUduZkzSL/4r3zJwsMr9NASv6ySJEVdpkeI52j1AK2AHr"
    "GgRq0dNBOhheDuPJFEsEIcarABYj4mAXHUu/DRIxLDSGmJyP4gxj2oVJ980Q7d2tUpg074dKJeh+Qyb3cCzGo8EZDuvxkS1F4bCU"
    "EhUucnGdDmE1ez0MaoHu5DF8UlRNTI3iBeq3+lJxIglLrDCcEYZ8v2J1SirF3OgWCVcKevKjc0Jogf+cojEzWd90v6HJTbon1Wo1"
    "5YKnu5OT+LSLYVXpuTsBWc2ZJC4U5lnG35hiVoeuDEdmtGhnd84rEynW73VleKA5y2dkVrshdp2D8BmBdYMqP+skupV1ZQZqLS9W"
    "sR7DZ2nyIb+CzzojNgoF+KrWYotZVd1HsqAbShuc70zYWD0rXkDy60AIkG7kjF+aib5RE60/baKIDvooG/I7mBa9UNKtsohSr6UF"
    "pcYWA8eOGMmpTaKNZkuhVP8cKMlY4Zd2G/CCyYAkfS8gaTwVJDSKfw4oz/ACdYMMm56hUc3TodLIQ4XH80Vgo3bv46P18hK4qEzD"
    "6+ZATDLFBn05kGbJMOswPuJPwIUrJGx9KVQDwlucuU0vn7afmsswpQgHHAoxdzgYCxrwyr+9qnBoCIE74+MhyDFmvxygcI/AUWBh"
    "ihk9n19wG4vO2vP568qPATDYdJZULycpWppGOQgKvcPA308AXxlIWgKSKUVvzMNDXf4sgwuQ4xH7XGimaO63/Yr+13//H1GIyZEY"
    "BKunnqVLJl7/pya+qSdedyf+tDmfmsue15XjeyENm6uwHbawfTlqbR8cYjYEjqYXNWqN9ka9vlFva7eEm/49M/udeq3h2wyffca0"
    "P21PuDeIZkf4Th3kUP4GnNPR21edehWGffT6/ff4ayt89e0x/Ki1wlfH+K22Fb4/+oCf6uERvqhD4T18Do9+psrN8Ic3R1zHcqd8"
    "fmAxONVsMrypBFUMgzaWYN4YT1BcCmF9ppW/HeioNjHyAxZPEgcYq3qSVYS1yFS4Vh1cALaaySDwt4OT5LRDJJXc+Q8RiMrpEdYz"
    "Iac5OGbZew4Ym/0h4BDGyu7FVC/M8nV0QCQk9Ql9lcl99d/+rVc5qW3s9DcuT+ftRfDVsBrfxxeV7BAalJlrh6qsF/1b9BJ9QSi+"
    "uYpsHuC9Vjg5VMxTJWYuzgDEOIJSGEw7AjtmXtBBoIhvcsEFL9MJyuO9WrCBann1EJjlGh5qz0nVzbruAmRc3AfapRFBtIuzT3az"
    "ycM86f71+KfD6rg/mVL0/guMn2XCTBrOFRsh1lXAvJBUwXYZSRisGLyO6ySb2LxfQo1welx17nH6XT7wVN34EIO12cXkCLAKqzdS"
    "JcfxBi9eJEakb/ROsMkT1DrQjzoQHWsswp/oobuMXL5pYKMttC9gXNDhSD9m/goVZfrq3r0IKKugCpREbbHvaAXzKej17x86cehj"
    "bW5GC//46I6aAuqrzYdpYXKL7IIZOXr3uw3yIB89L6Zo3BymCRFfxh70bEDETgoCq/l1i0FUdOfxkarGRA5SvcmE+uAhDoLpZAjb"
    "JyO5Ket+c0JUKcRt0YPtDDJjr8rvTkNML29tnakDujmSkmF/dHYnN8bUgvuSnDv68C65covlX8P5nV70WZdLBdQjfsjOkol+jQ8B"
    "SLUwb2mLfgfoe4+6ASkoTyABToCXv8XLh15V/WaRiCbbSQ/FiUJP80KmSfu+y80JYqejdHJ2DURvCoRnPMJAjWHEImhyqImYSNMo"
    "2CY6FjQg50kiQ5NWcLlIvooiRdTnt8C+pWq2/NAjaRFOERTu+QO/uOmjfUl/JC/VI4ICeph2JipMAXrWuHPQHxBJR2kCHMVsgGEm"
    "4eh3HtGJsn8PraJwBL2iiXXcQ8BX1XMAJ+LWJrDCaB39oL/yI+9qVARksNrTMwQ60O/JWRbfjGUB/R8DUwlOc2959T4IHeRSKDUd"
    "w0K4eGe/CvIYgJtm9CmbBmmJs1fCGR2Y7nY0G2iwfAPlNo9n7xT2jdk2MwR6YdfIW2fT8IbR+4WKeLaL3i0CphGWo5/udrl0tkvM"
    "6D0t2xNKXRNLUOd6jlfKbZq53iyMR4V92NGhANHR24fhZOAnvxcdu0HYeyL7eZrNvzbt0YGe268ERP4tG5Xe5PYpvTPbtFqtTqxd"
    "pTeU2UpqF5Xun5K949s6xW2jd43smNyGcTbLCiQYHxomeA7McTqpwMNJEk5O4QyTrRTLNgIulxJFAOmhpiKuGXc9Wy5XdaIRqnIS"
    "xqewTWOVIirYtZnsODDxazIecTfmbNJrE6mCn4CB7k4M00o04EbTAGL3+PQdXj5URFUQwMhzXzL5Yvb6tbMtLJhMwqEfJsiS4tA0"
    "UG4OK8MQKpwCIQHma3LaHQJ3lyawiiCoPhVkQwtkcZggzNahZTR7Vsc9AHIJ+BIDPh3oVE/zqmSaa8B/6ElSk1kQTMyS91Sr5RPg"
    "WlwsMJQ3tPkU2cAoCROAqAfeh8AVuScoF8WTEEryw25xQmeHKoYFT2qIk0JhIVAzi2FmJ5HarKSJoU0K4qbKJYXaX0v8wudvarCI"
    "Q/wQTeLfZ0BNBhh9gvKxOGRfI2eR2i/59E2+GVi4YaEUSCVpejDDcBok1vS7EgcHhDxn4TIt0Z5M6HzbneQ4W60rMBm0XE6Vj0C8"
    "2f7qv/3Xwby12IB/G/Jv5eT92ul/PX4Z9J5/JTnllAD5+Kil1UM4YL+DfkTi0kUCbHZ4krzksfFgIqBHaj37mkolTMXCiP5U8Ybq"
    "xYu+QquQRJI+Hn1kr0u/sNCQCMGtLf7SOQeiqqL84q+Gf2RchtAbKq8+yTmhavGjfFz4DoFeT9Qu5sDKDOuovxZPrqzIrOrSOYKv"
    "3i8W4cNhV0xZoynqyc4Pu86dfJTOhhuYpT1y73MX4b2UbIS6/sbVZIjx0o7lU81uhHRba1BomsVj/93qItzz1SQExJpjdKFdhHdQ"
    "CO0zIvPqvT2NjXScwbvXh90TN7rOd0vHdQ11foISwwE1AjwVTvMjtnIr91qvCk3+ZjouNHZgGuN1x/YO7faOnGFfYKChRbh/qCL/"
    "ONcqxjOEbdpPwzeF0bz1jAZafOd2058M1vDzdTxJ6UeabJz3E1y5P5yStJjfum0SLizCn52CfB3Kd6u4q5/RTfPtML7jT4vwBx/o"
    "sS3CiNk5FPngdgRUFL/dlbTLmAzV/l6KsYvw+0P7fvQYSQFfkkb5K0q+pLt6VR0OhK8IE/MSB2DuKytzIiqdyaG6KuwxkZyKoBH+"
    "fl1N75IzfhmEisJ4a2hC5FZaBOb6U9eh1tXuNbecQ9Mmt2WKpN00AWY7nOJfOIOH04yULuEFvuCJjvAnCPlCLE5IoMF3F+67Ab5b"
    "r2MAJjpEn0MDIRJKtGMaiQ4X2lHXTfryFUcNTUoJaLWfK6HGDeOVQvVwKr8q5rPc/EowcDMbzH0BeCKqfBpcOJCH9boMF104hiDt"
    "AKFl28EghAkg+GRgmnaHivgnXVLy7mZViZOYGA5SVRImoKv0ScX3l4GneIKjwnj22M9Y1vFE7rLNzOSK5kd9K2FWcKHseXjy+YL4"
    "MlicYhQswdokjyUlF+nmZugkdhipMJb76+jfMKvJcLBAF38FtdOCyMcC2tr//P/W0IiTbuYdtW3M8VQkgOpeegPHPZ729DYcX8k1"
    "fICxu3gONxpfkgFLk+oO40Ld2VcvhSUPr6TSuizf4+PUXHkQeMIzKQLMn+BvKL32ZMFYIBQ8DTM1pPAWOYTKQLVMbea5LtT8ncmF"
    "UXzaM2sznqTno/im+nxuPi+iQF24PMiofuGdM7XUp+p2CYC/rnlCveuJeHWlDDwQkwkFu0TX1MYJwnNtk8CtmZH1B4P3wwwtemyc"
    "gz/8lq4OqTEkT/duMy9eWPDVeNq7VvdP80Xn9lBtBKh+LNVHarwOH9vr3ct79cyrGse5anmo93oVNa9jaw0xaYyqqoIiquEajl1e"
    "YXIJpYeN86V6B/3sGiOdVmoh/wQ0r4eq4FfHaoYdOUdiuuPaA6xfrxm0DidqOKYL1mH/WBGudZZ8TOBIeBtfAi51jt1SSVxRFQO8"
    "yLSfF2vP59AKA6SaXsLCZSlGGoVCaniLYIEMrxrEiQK3s+Pv86RRoKLeK67Vgg4N5W7tTZKNqszR76cTqF/RM8ccIfgi3wgM++YG"
    "iHm0nJQE4V4XRzxXNJU1T2SI477SSickWdv0X6TPIVUGBrJRD6wS6AxMS5bvIFdRSdcsR+HRgHe5aaztg5ZXx7FVUNzsfoPSa9zL"
    "OgkmstILYjSwrmr2tMz0yexYIM8L9LjCEDuqPe/mFLIpx1pn3RbBz9RyURZduajQQq/QPC0Oo5mobWVlSVX2XcIorgRzfTYDNxgr"
    "4lFRR3/DOruDRX/6kFys6fqzmHNKWU1o8pPqGdaRrdNp/BZQ3jsxdb0DFO18Nn2Q279d1rAMzJngMjKkFZAm5revKl7AzvusNIwu"
    "JjEKqZoHPAMKKlBnvVuHdGiLTqGG9dVwkPB4qYlokX8yieYXzMCQOgqmUs6WuY/I3F0v7yOEj0t5uOKoEGQObiVGz+S8v9SH1BwW"
    "JR3HCTJw3++h1d5lGoUWf5OyEzMGfWJyucEAjBwIjLvWKaqYBjom+UzcjZTuHHpYS168GPeqs/rZeTpLMER5/64/zNZ+fVWZZ3gA"
    "4haDGc2qFDwLT5T7DN9RIODJDRDs0TD5CNRWq+fHWjcP/OYDiOmF0v+gKSQpf7m5SZPqVfptn/w5BjhDckQAAgWopnFkSsaljCGJ"
    "wY7L8K4/7Yh4cmWWPLEw6Mos3SWaSajou3E4RC5R2ZXE50GoUl11XleuXgW0HJYth3x81hmeNJQdnCnYjdFqFI6cKAo5RkTnXLod"
    "TPpXVxwnuW4pD4CUjNKrnLgXK3GNPeLuhoPsuhPhibvTqo3vwzVgHS8q9Vrt9m5tY63ZGN8HAQh+zy5GKTR5PssyEG7JFvYZwAXv"
    "XFHBDt3BIgz6k4eI1xDIyASXPB50tNGkWMmxUZCsDDUbkZsXW9V3vmNi/Q5A9leAmLcLJs9uQ/3kwooN6cx2Qz5qH7fhSX2nCOD1"
    "esFyCNh9DzVsGEPCv2ob0pUDlX12zpjoGyZ9sgbZUDajWojzDNAyvE/UUH0UvDjmum94CRsK+4ZHn/TwRrF3MEooKvTWkJi109n5"
    "DZpfIc9CaIo/FKQUo+kMyeKhnSWnPYs3dBR+TPYUnjve0VNpj2mYVHedq4BS6OAEhI7KUf3hMDzhjmKMzG2m+duDxgTYIShy4nfY"
    "DUTmrCqi9gMBbZJ59+YG17SGSm24S72u13q9MJz9SjSOwvPD8H3FgZeaacABN/No48YHuj+kWFC8OErrxk+GwvCz5UEYIX4c0wp3"
    "vptWgDadkIIJ6GSE6QdPslxfMNBjM1BZcFZozhNlHcgXgTYuF4rvCzXWOGJ9IzUVcW/uvMt3iRPxFCnR978Fjgn/VBsA+wzxhtrY"
    "W7EyxjVo/Hmmw/3RKL3bIM+bZ0jlPRRVzTidTS7it06k3NxOoBI2gjmxdIzFsK0KDUIvW+bgzB7jjEzlrrCupFumVQjfKSNsC6gX"
    "K4CqzsQLDVTLdlvrrjWkbz4L0iyEdHK2nYVpHGEgdWW5OVCIdOFIlOEzWq+NG3Y4yq1TkiqcRXbFY/KpZrRx7ScToqlXrptAqNTP"
    "eCEkiy143x8yEh8dBxjK5Ic+/H6/F6Ae0A5dEnJoXx2SF+1iS8ItGRQpMyF1Zo7Y85b2uiIkal7KgffEuhaZP0NGow9rWgLXBVKS"
    "95WSrz3vWhVX8Id4RNEOmoFD+d1AraHRdRWOf7QDZ0uGKCxc3MCXaNkmtciSIYqq145q/7oZhd95yaNUJopGm+kjspee81yUQOz1"
    "zZcQ8ia8HgL36ivMoHEi9AhPJsbuTjPWDvZrnko3tHJr8FdDhneYdMheulOPN5VBeJ0txaOrEgrm4q065nGyHLGoHFZa82VBa4S6"
    "opBO185txaOSXAEmru+BUcECqQxKzRyUCnfRK+GkCdX6eskU/CeB8RjxQZTZlDKQklSnRUELnulF5AOZGN6bu0Iv0FSDpcBq5YCl"
    "KiCQtNl91G5FlL3Mvpd8KioxLUN6zDFsfjr0RZNB3Rlq7Y7jDKb2S6BkZm21pS3M8qo5IEGxiI37VjQSJDAqabXhvD8eIgXnENPL"
    "cXtEiTXMKmRPWoWsZBXQDq50DTYLa4DFCyvwSSD3Tm0A58VwxGZ41uT4ecW+5EK+2bFVX9nk2rnJUencFtxSW7Dxz8+R9lECkrHi"
    "6NQs8R2K8X2KiRGVLGd8YJaTa3hmLEaLpXPeys1Zyrsrir4saNNwBwdgA8++WZZuTGKOUQPnGqeJi77AsiuxUMwqLZhQghs/IMjb"
    "0zN3bZxZNvnt3OS17XOB/ZTeP2F6RbrhKA81IXijwEBUgExmxTlXLhD5nQLD9H4D7xPh1cI6usRw5yU7fPig9OuBF0Rk4XMSs3mu"
    "H0yZgY9dupuhHA10SzDQGZhzKOUHVyKaFPsms7FLPKwGxRPLhEdRh9YlyuT66NK0E7p6fWjzfVdai+7jAOtBCQvYfDoLeKklVi93"
    "rz8vSKZCTvA35AS9GhK6fC1rnuQtP4vpVVywYpj1Fg+6t7MriwG97qPVXfigbstc9pS+HkJbZfInV/cpONyj9cB7tCbOvdr0E07L"
    "w9WnJTouUwjeMzF+NMRFXqw+NqWgTWlnzphLaY1SSrrFl/AuxgzqCxFVsi6yDhk2Nlo1YzZX8syX7jxL5flabrpY+k9gE5jBmuo7"
    "V2t+8OoJ08NSvtnpS9zSGdZzM1Q1/oRZygLiZejMRlt4sVHzTFKrB468u8y9XA2VY6DjAE3bLAsdgzuhV5LHTEEQB/F8nmGiZ1IC"
    "U6sqljFwKaiNsK+Ml9BNnuAh6Qezl/VFoMPxoqI8rmQhpi+bXMXqSlFA26qF+4eFy2rtIPFUjT7dbgANRb4GPtz0R6Nlo5VENLwo"
    "ZshKK7y6pFK3o60KpTDSAdo0qv4jkHevK6+BmNPI6jbrSfHEXFxyLCCZ/DpJVSxVuCKZftB9vf3Pgc7H2A0GewqLfecHfN8QNNfg"
    "2VsOl5GGS2s5XIq3KiV7cCUeaX7Ne82ivWCsnQrvSohRXlOqjd9UK+UUqJGjQMZhrcC/Yv9aezqNP0d9ukqnvArYSw5lbRhhA6xv"
    "8bemwArRj6p5oSluQ6XAbBaAKdY6jvxX0+KfaGBubnLcrj3UL696USgmhiUWvOLEhpf6vgpcWMsHLnGpKoVWKw8tMdV0gaWh1VT6"
    "qq8ubv7n/5uHmBnsnwawJP3jj5HD/aR/rFIjYBEfcErcyUphtZmDlb++A7o2gI4h9j//n70vx0CcOxL1OTHqS0GARZaCQLvJlc6+"
    "XTZ7VdWZePPPmbjShuq5X96tmjqU8M18hUK3vpWb7pfXd6+YKknbf8/Pd7pyvlP/fB3/xtJZb+cX2ar1hederlfRzgGfqVq59KpW"
    "jG3e07Urs0/SrsyeoF25LNWueMb3r1ewvDp07tmaDZL2+9PhINap31gzSw4py7hqVcTPH6qvLImMo/Bt8SZaNUDKEWXc8U4uSsfH"
    "GPmXL0nvlXXx/HIixmKZYo2E0645GQpVMXVRgA3/caiG8u0yHY5c6slcWSXGVsBIYnETsq0HW4vX1aXqz9jmvSVDPz46Lc8SfDmQ"
    "yQ7jognGDyU3xPfGY8C5JVZt8DWxG/oTmvuAA5pYZYgYTe59QLQw0YZc/v5GPPzsQf8deykp51p6ILIiBr45DMo5e7G+i0w2rqho"
    "86YiIf1oXKvGow1UegO2/X6oEtKLT99p+Fen3N11CsX+4fX/+sUped6flCVd/NXtOsae/+Zt8rn3bXxku3AdjWC3H2HCuxIPrl8w"
    "12+GkUZgkuTfov24MkXIlTlzleeNFiIpGXpMkN5juCMr2tFXQ/ZTRRvyKKDgRninSYYEFSj7VQivJahBLWxL3Ithd55+7GCzIcAm"
    "xmTnd/0JMqbDe7z+4IfpdTrJtOmVWPt3gHLBulqRpvqVYC7zYkONX48rHL8zopdnIHDcDKcAWcuYMw3QWPCXQOChD4+350Z/akn1"
    "VKrKkjVsOhZDpyCGspL1Ij3vj/L2X1QHz2BcKnVwvK483wtMdwfHRsjOyOSKpl48cHCfitqWx9LPMJ0H6UepTU6wwDvAZ7ine6qr"
    "ntKPpf2YKadi4mNatqzqeINPn2TkWaom4H5AjJUg7UWwyze2Y9A6glSbZeXXW7W1WKFeGXyaGiHUiu1w6UxXKkZ4VgorfTOWb7kZ"
    "9z32jmpIp8j42Ra3TLufm7OSW0Zf0nCOHuodg/5VfMYNvFBrXdQuYm6YH726RSEceaUiRjB3VYpMW9UuYeqCsfD418IcWhyNpDOp"
    "xKIf9K0TKx1PrYDPf+VzeZpNUvQNpJJoA0VxvoOX7B/z8r0OQFK36v7jkIriVhUQ6E+/HFK6RE0MhRBFBQMfK1876kwNG3TN5uhk"
    "o30VV8RMm5yjyKyafThHfwHxGYb574S4rOWkYVgtJTHyDktbwiJn44vM1xrbQ9mT+1V4BSIPTBiGeranvR5TW529ArFoWEafYrpq"
    "GQ2TWFMMw1FS285y/Y1Bztf+YqIGK/u7fa1j70Kl15QNaigRHuHZkTlHcXyJey7G8eSQ7ss57vP87hq4MArlrI9JHWo40UdDjPcM"
    "s/oFJ9foPe2SDQRAbBwxZTwZUsBrYQ2xvap6p/hCesnmJHkGGD9tzOp+bT+DbQq9HjHWz25uiPwI2lut310/iMW1xWZ6i32bDh4U"
    "vS+CPg/zyZHDkZDxwtr0FsY7zH1BTWjfvJveblxwEILU93J6VOB01rTL++0GLu/FUd63f3Tk8aBHcrMIZ0cqIMKtutUfuF1wuUur"
    "3A3GMIR346OuyeYnYAhvjiRygZQzto9mute5EYr9LRq0QwtXbv/E4mzwkkLdM5nLpr6MGXP0Axc/6Fp1Ed6a0cASRh4//wdprxmW"
    "lKMRnx8VogFMfybRLcdKoqs8+uQYF/mJ+TlUn/v0I+GLY/Kzj2yLvGnhDbncgwR5EYnPPbZCjvZjEZ/iiZhXTSPlby9WWeiXZT0Z"
    "5pCGjUEqJQQKOVMfgxzVv4pVmjQogrsVNpoduXK9vlg8TyozcnfHFpyqU6laGFgY96AlzE2hAmEujCu9sKnU5Lpjqi7couXnN9WO"
    "qFg75UgC63ZJbY6uHOVvkBuybdXiojkau5hbPuOVXwrWbMZjWkflWhFQ/upJrTmB+1a0eNYd7bFPWuWEI1ohlCiGSxRggOFb6VKC"
    "ZOGUD/pjHWgpw3g9ajAqENNsj0JV8ngeH+cAt4RTH2eVBBgYxIhKEjw+wslZV9KCDjtgRRFQl9DA2/HlFhLvQZp1zsKko0HA10gL"
    "jGhGk5FwUxlNp3rdp+hP7Ol6knEMKgWMzPTFLFCVLly5kyTE8G04VsxJhUkTMNjELaHIUHuS2KKcQjP5SoGC5GUUKfR50K61tGtD"
    "4/sXRvq2PVRxpJb52SrwUKI529323HTBKSKK7YYWUQgjzOCFeihM3H0mD5jQQ/3mzfCUsSDey1CsLLf21luX7UkjVd77L9fXRdv4"
    "UjkGUoAEhFCv1qkHL9egyEhpR5TX/vq64otN0ENleTRRP4bqh6puEa4YPXkzvUY6Z4IdcIEfzEIqPQv8JO9O7dEve8QdkRuAGOh1"
    "PqBCJhX7XXfT6PBgCtX6mk6gp3RumvjZ3vhQJA+AFy9gY/aDdY2fvfV6Zx2+X++hAQDi5/BSKYdUEOIxVFETZvydFohAzEQgr/Nw"
    "aAT6u06DyvpUNiSnWAd0+3oqWyzA0A1IIrJQPunIeH1yq++fOoE7zvYofJhyd9LuzBivrkDxe1LawXo8BKF8p4a5OhYqRsLzY6Cu"
    "eHuKilvcABhB45c9WVQcvUT2xSkFVgSFinG4hQ3BmzKBxdfm3DpCl/4sQs6BMbKRUF35Ej+LYRUF5FEd5jeKxnAJQAzLqrSu2k86"
    "1pEv9pwUIklXn2aBwTxeq14C4gMmkIbfnQRNDTC3WWIrh2I7EN/JqRuI7x5hb4GVZnY2ZaupRAUfrH6EYwjnMmWN7jypjmfTa07k"
    "RLHWQizRke/idyxcfUhtdrJFIUYhRkcE4vsyeow4YhvwTpfWYsaE9XZfseonI9dSzlg7kbyvSBDhAf+E6ADbGZquw6ETpm9N6gR2"
    "4xHwgi8puo1nMoDF18MRef/qRk3YQ2w3VWuvNdLqR/USEP2A6bNwkLgqMuzYTvSyNrDnT196J3PYYRnmUmDdKbp7n2L/HbSgMVgz"
    "LQzAE0NRj0nOC757Ubdq4i4VXmC67o6MUE7xkCKETDvne2roAYN5vTjmxamObnKRI8GpwnuMik8nv4S0Dyyqu47xc09zaAd8Cr6k"
    "deCQAb+gdmR2k0yBcDYwyLbY8DQCleHxlKO0dzfqBu+79d3J16rs7uTly2Cog0xADyeT01M+tzHqBj1v1OUNxtv8uvb4SPqG/vm0"
    "MtlQDX3VCL7WrxP7NfIaiRVMFFrowcgwepJSC2O4UcyNzc/0hImgRjnY/aqjjzEZKQtdgOUCiWQJYIJzZP3XKhqwww8FfxVHQcU7"
    "3xXRJtapO3TwU7MOtO16kmgZinQyHgHzX8TXjGITgkii6P4iTpynoXCy41cYs6Ik2tav5M42DSmwB02egywcJJVAhd5ILyjfFx5P"
    "ksns24c3A5RFlAwZIH71+GIsnU2l1PHwfATnA4WbQKhkeNZBI9+i6gg+7I2GlE76IiPuYPx1Vvr1PM2y9GajbgcFwTDHv8/iyQOn"
    "dAOEi6ooXY7xQmJDlOfIcANRy/rnnJJ1o47RJjHPWGUuvsWcFJuhohJuv0myFIXRyvwczrKPqAnrT2KUfwPFvs5y6HJ2xRmiq7Sd"
    "ozDHlodzTOBjrq4Ut64R9RcMRAWbMp6KO3aE3CMqESl6EDVNCeOy6T7AnC71+A45XxNjCdkvaUB2c3qo0h4O1i2NLQBjGg5ifZMz"
    "iS9idF3o/cK97KUDOXHPZhOMWC4/oGf0FX+NZYjJdcDQk/uVvNTSy8Glx+qGDrbKypGOZJLsaKd7kMLN8Kw+803fXpHGucKF4sGr"
    "7Kt63MQcGEE4jl2VPtsVyFViqAN8wNKdaZeRkL1kd/XtztTSQ9OV7eQI1ZzJUSiav0g0bgsccv6qpKDe4+soW01PiwX0gIJ+8aKT"
    "ylBPOiQVu2p7kdPscc1FOP8iNygSEABmP3mwrgteV0Z3X/oGxNiULlcPhuwlB6t0xPrO9/3zgrdCfKTc8gNzuT43TsRAzihiKvoQ"
    "jzfuhtm1kLdnHZC4FGgpEME7dXV3OQKGBkV1ozkTNdkF5/rLqVGvG8BHHWlFaNK/1cpYfdX97rjEBH0aIwqKKxdAGlhhc8+H8ye6"
    "r4/wGydh3Qrz2ieY1dqC7Pr660pyl0MzNK0VNk4hxVT7VL6unL0KKjr04xeztrVSrhZsQT//zow3HADYM2k0kPh9D20s+Htxo8J7"
    "uUvzeuaLQtTdotiWtZcGq/bS3meDyWeyXbyD024MltVRtjTGwlTfkGY6xoIQVULcHLiLERJcPNfQc2x4vHshD8olvnT5oANulAqf"
    "uXSyYtKFpIPuNJVJ9PUXyfpXDjToTEnP0+WgszxZHLjp96tje3wqDIcrYKjszIfLYXj7meFPSkFx4fUUkLc6pCsGx1DeYI7zS/+o"
    "cIl8a8dEzcxWwHCEveogBSEcKGHgu1jGO83l1WkOvV5h4bVOWF+lrQzrkRaHHuPwygZmhfYwV6rTI7pSTZ4c8KOIKZ9Dou8dCzgF"
    "hyy9uhrF7Npzr/igjq+M3h7xPUwDGMJnyp5S3ssN7JSJ9ZgNnBwUkQY3pEHrvMtZ+XfXZ8pUbRk1/+X2E6m5M37nnnvuhkXJ4Dw+"
    "70825MJ2LX/FSezOLYdMwQMOL6JdaeI08Kfezu2ZGbmbvq8MjPqfefjHR/uV5ud7M3lLfHjTb4v7Y1LRnJpcJspyWNeJMsU185Gj"
    "ZJESYen+V/ggLF2ebE1WkC1ldz9ZTrau/nzS/7O4ci4l/Nop1Vk57Zn6pYl+fwX0lN1+fzn0Hr400Se08HIOjDCfGtrKN/d0xdy3"
    "crH5SuZ+/nlzl9eK44MvhvlbxlOlk8zPUcGHzwLL04RLZ0gmHhNdS+QPO7yuzw0buescG64/DSfCiPPJkW88+l//1/8ddeDf/xEV"
    "ZywubZqyb+ciiBUao4F06MECltdZUkNpueCmnWVHclx/RDxzPO/ExiQ8HyYAWSQUbsJZ6oB84Ny8e37MHMf5ZZZ8r3zCyDRmRoLV"
    "C6PjafjMunkSgyM7wttlsREymZ5mxnDIcQRWVjKuF7Ax55Gvt3b4Cdsr2Icg0iMhCTIO9caiVGjTtjfKZXiqXe7VRajrPGx8h8dH"
    "2ij9yzm8mjnAEaF9Xg2+ag9565p2aQRQvVA3pUvjAMoY0V3A/E5OfkmVY+upMCQ6vIWjZWEVq+hZsrsUNr2r/PumbjEdNqUi8Xqk"
    "SJSXKdFmT886DiciOkM46X2vzarcn+dNpFWZoqBvFJG5bDye4Js5HohUpsVO6+Hwpn+Fney/92gWkvTDZKTtwglDCl/Pyagu59tC"
    "AfWSdAO7LdcD2tiFqim8cDoWbzpH03e5Sjtx9WU0fQQMi2xSNt88NFmh7AFmQ61gLpqqBtgk7g9Yl65h6gGbiqj6FKj9h+hGwyeH"
    "O169qAWL72U6Ik0wrphg2Bppy4p/yU5glb5n7ZrLNwLVy28E5yQ979+czxT7YNXh90GxsWX7JvFpzz9F51qqUbXIdf1P1pR61aMF"
    "peckvpzE0+v/EMX+k7a7ESCLWNNSvjLX2lcmiWfZBA2+PMT0ANtZQk75ezli8OH4qRcrpWe4o2uWxCAmhEfs2ZyW6tuB4wUZ0RXA"
    "6NxRnR35vCvUSZx3r2AR3A3ZMlYhW95VfngVzil6W8wGG1YIiCndzsKUPHfVaXKMl9yI/UoFKCYp3b2K/ApjRMXvyQxkaqIoDHS5"
    "gS5nQYi86sTCBn+oURCkjME/cC/1Wnh9pN0HTkjF3+MMgRH7uACvmrh+LreGQSJUkeX/6RJzu8CpMiUkhIa0hwuZvNSihWQVgjcY"
    "8g6NDly28P1vimQQz6tv2MUwRhW31kCbceu58x2MG5i2sUrUeFP5XhxKGgv3Zg3hUQguC0B4yAHBXHuQA6U4O957bPOPj3y+hXuu"
    "D8UkvQJCNF3uXojc308JXvmOpXw1TXr8Xvk+2Bmb5AtmephiylX6dcqqqls0yoyrv6XnQcf2VLTaRu8ULHyNbscmBV1m/MOlH+UP"
    "92qvOkwuRrMBJpfFpsnVJQ466+u/7Z1Yb049CeZOTjvFlj31+pT9Kq4C8ez1asE39e1amFo5M8lQ5nKUptDAV+2aybOLuY303K5R"
    "FXgN2/umo+z6/h0KV8f9wTFmkqk0QrIyp1xUuhZWukHl8iKcYpfqrj2mK/bwojt/9+Hw8M3h952IfBHCo3evj169e43yW5KgfICc"
    "9fHbN3tUxn559OrD8Wt1G77/5vDN8Q/sw7n/6s3b198ptm4RjrDjHFjIw4mdYjAc/IzkIMAfyT5rSmIZbjzq1Wu1jjedVK0WcpXx"
    "RYbW2pbh7MAgJRUBtDlhjy/LpAd6uqLMCtQlWtXzHADhxCZOymCsvVH/AZDW+kIvXrxYp/HbwKcPHO6Jf7PVmHqawlqhqYdbHn14"
    "5Bdm4bKgoIake5QR2F1Os3Q8RhMKu1ukcomTFcpKTO6Bj4aMvT1kJAH1H19mKqOaNkmko/1vt9rUmsBhTa7aP09naDJivaIAyoHo"
    "BNIKt4w+Dtamvhwmw+m1wFdPmrt7Y7qzmx2wmwk3O+XsuEl6Vwlecg9/acctov1ZAckoKW+afsx19IO/IyzpjB9f4Pj9DceYJucp"
    "E+A5U7AWNQmq/RfctQsbC130y7WePXhbZ7xUTUfP5wpP1r5a0w/TBZrDJMZHGtmNiaMH0BbbypLH5zedN8EYXxVylPLA/I5taJFx"
    "b04yPYvMcmErjQhSziXxyWKFqB9fbQD2o9IDft2kE4zM8U3NmJM8xxlhDthOBouKCYdvxsBWYKGQ7Hc6fTTjk8zFSIvsYA2IDFM+"
    "8NCoSSbRmWGVZ+rR1aXomVK4gHmhYXTPDZm56CCRW7DD5kwzuTieZa7l2uqo1OcbQSRmTTmv73I/8guHzC/1KDc0C/cnRjfRFRdW"
    "h0WnUY+oW0QBJGxhZgWCmd3LUFXOTN4iVfyjM9Twl1vHnEJp+CJrofNiVKh5fuUdyHCzmVlnLohKGIWC0UiXD5UnjN4V5qfWUgtL"
    "eUp8o47gVwSButaPfTsgGqJ9t7ULlOvjGmwADqpQ8AWWYAtPWVQq6WCN0V8ee/Zzkh7x7vB6ZufA6EQeQC72DjhW5kvjBwxWiiEW"
    "5nBgTzsn/CbiqDMgZ7AnE/IpwLqgnApIOr296szvb0YJemdn2bjz1Vd3d3fVu2Y1nVx91ajVal9BkShk/+oGSCScIhx+Ybvfpvcg"
    "PKzV1hr4P0ozMupEopZIUjg9OydAYYBdAdiD2HBQr601q43NvXqzWqu1G/RQq22v1Ter9Z3mzlqrutOo7eys1dvVzR14D39qzZ36"
    "Xn2r2thp1tfwz87WGjxu11v1te1qbaexCcW3q/XNnQY8t7c3N6H57Wqz2cDvO9uNdhu/t6C3nWoD38LTZmtnGx5btZ36Npbe3Glu"
    "4fPOVnsTv7cbWy143mxvN7bpebOGz+36dr2N5dvt+g4+txo7/H2rTt/bjU153sL221vwf1R+u0blt5tbNFpoF/tr79Dk8bnVpudW"
    "s8XlNzfpud1s8Pc21d/Z2m7z8xZ/32k03tLzNj5v1er1rZ/xb6O+uWe/b/C0tnaa9Njewm7X6rU99bZeQwhLZ1CJnrc2c887P9Pf"
    "7e23ahDw3IRJ7KlB0jMDmSZBzwBcNUl63tzaU0Cg5x0BSo3r19sNDUR8hlXbU0DG5yYsjloEfN7c0muEj9u8prSG8Nxq1uk7rTE8"
    "b4J8q3EAn3d4+Igh8AhLRqMhBKrXq7X6VlMjGDw3663NPYWA8LxTw24EP+sNAG6tqfEX8Ly10wb8FfyGvzVsXtAfim21cPI1+rm5"
    "167u7MD4+Ql2w3atXd9UtZqEr1u6Ueyrvb2jO21U69ub+KwGVd1u1bbrZtAAsS2eBE+qutncZpjxpKutzRqDlGEC/bVxUgpm1eZW"
    "o23BtNqEcRiQA8i2ZYU26Wtje3PHLBg8Nxpts6AwqJ16wyw4/NlqbBuEgOfNVsMgDE3CQih4btbrBuHgudHaUQj5Fp/rm/U1Qdif"
    "BYGpnSavfGMHdzuMtrXD5bYQ0WEJdmhN9tQn2DGwn1prqiruoKY8Yxey4X6WDfhWDUU26J4aqt7AMhW9wWWqmgAIKJhA8FQRVExA"
    "tjUoNYERUDMBovK0Ekyg9EJp+iXryPQNP/M6M/1raTzQ9FHwhMgnblHBI6aumxrPFPVVeMjUeXtN4akQb4XGirYrLGfajzSf9wCe"
    "DWtyYPyKJ0cLd8gW4Ga7uUkPa5vVLQBIE6rA/qjDu03YtdAPzLa2s9es7tTr0OB2FQ+yFnbcQrBu4/bYxA7qzS2iq63mDuwP3JRb"
    "LaLLsCoNGPdObbONcINp1erwvA3zR4zcU58AaWAl11RNwvX2tm4Zd067hi1zz7jzACRramTwvK1GDbsY4bGn5gS7HOGxpiYMRIDh"
    "QT/2oHir1mzTE5GQVrVRb5tq8L7VhqGoZoGi1Lapx60dOWA3ce1lRPC83W409YjruAoNRW6RvtV2mi2eL26yrWq9vUV7RL4wkLbW"
    "VEUCYq2hG1ZAVh3zItB3HBev0aYetlpDNS1ZYTVrXH06OhkrCD2IgNL8Wtv0UEPqQliErW8iIRWc2pMfVHhnTVXCt4ocE5tC9ZiM"
    "Q3GiyaoOP9T26C+X21pT5eUj/aWxbWNrO9Vas7lZpwf+h9/wb2hL/lZ32m31jag3N0Y/9vhzi55orPLZvOUJ0g9uY1t/xg4IKjwi"
    "GJomdi69bCOdbADtoLr1Gp0W/AwLvdNobznED8jdW9MUNGtxHvANT9ctIJFSlw53eua2Wy6T0d55S6zJ21wrvyr+8mI2mcRJtsd2"
    "FsTSn8/Su6v7aHEKPO17UtcyU/waWeBhco2XHa+ybDLFLINKk0v8sa2/nb8hwWjRfX1VuTuy/GgSO+VtpqIJgujWxzatOILEk7+2"
    "efKNKcgY10XOXL1nlS3KOsNbyucczRLg1ROOSinR+/4DOHUgWW1cTvq71QQSttVubONzHSgb7sAGkTh63mYqVttsqfJvcZ83a23e"
    "0DtbuO+3G80mPkND7TX93MaGWmu6PP1t7vH7LSlXl3o78kzNbqnCb4FKtOpIrfBtYwu3d31ni4hLg/Yv7IZGs2XxW0CwmU0TpqtV"
    "27GZLuQ7LKar1XKYrq1622G62vhsMV117lIzXdv1HWG6Wsx0NV2eq7Xp8ly8Yw3PxdyJ4bm2t1ymS7gkxXRtt12ma7PhMl3NHZfp"
    "UkyVYroUF6+Yru2Gy3Q1t12ma6vtMl1b216mq7XZkg3eJKZriw4QYLpgnA1cD2IO3SaYDsGLOtMKPDPhuUbS1DaQI2KGaopK7Oy0"
    "iQnbrtWxSzjZWNzZYkjWgWtj8acuz8zLbRLgsdsW83LbDIlmQ3i4Ns+0tcU8HOAh82jEK2wT4w/wrRMPBavaZsC3W006Brd2CJBN"
    "6IhYMlmYzcYm8WSAXg1e52aTeLJ2C0ffqjMLtl2j5ltbtRaOFuC2Taw7DAaLN2pbuFsIGYklq9H6AROwTaxPa3uriVgK6A9wB5YM"
    "ZtlALMbxIkvWxHVABqW1g8csIFsNd3dzuw0sD+wnEIt23ipqQLscNhju+q06E4Em8Tv4SDSCpHqHdvx6sElY3kaWD+k9sHztOkog"
    "W7g9qf7O5g6djPUacoy01+CY38a93mhBd8DvNnH6cD4D1IDfqm/TWrYJvYEzAxYUnwH5aXrb7dYmlgfepkbfWyB94jPs1U3i5GrE"
    "tOxAtw1i51r1TWZvalvEz7Wbwv20WszPsahj+LnNTYefazBDIfwcEieLoWu57Fy7qdk5IUTM0wFubzf1twYuAnF2O3XEwCbgFFJI"
    "XJwaHJK46IgLsJggeiNn0NpEjrAJyLGJzMjWTo2kxSbMDjoGFOFhkcDehjWoMeFq1GvI3UDtBp7RUJuY9SbSs23CiMbb3BIiV8ND"
    "t/Q5Ldbn1FmdA1iNLH2dhWHYwa4yp+Uqc1osLrRF1N7M6XJaRtogSb0pyhzW5mCfjjanZYQZUgRsibCzI4qCLVeZ06gbWYn0DFuu"
    "Mieny9GimKgtmjlVzk5OlbMtkp5oRbYaOVXOdk6Vs12iytl2VTlCy6hXxqKabsBwUjwAJtiidmkxZtfaMiDh8+s1mY8cDzx80fEQ"
    "lUdY8eHVbDUFljv8vd1sUvFWnah6q9ZgHU6dOweEpGFvbouQ0eDmN4XlBKJHsG/VWQsD1Ie0Lo3tlmyzNg0eoEEKDCJyW7C0myQU"
    "NJBokShSp2dkM4nlaG6StqVR3ybWotlusRRAuxeEiiZvzVoDZR7YqfWGbKhN4gDamy16bojyZqe2Q8OB0Wxj+83tTWK6m9T6VnOH"
    "Jg8rS7wF0D4+SgGVSFDaZP0HkQqQoGSudcIckqiaRqTayolUIpfW6iJStV2RqikSVVMkqqYWe4kD26rnRKq2iFRKptphmaquSRJJ"
    "27BrCFQtkSa2drbbxCGxHNPeRDjB805zk6QlWk7Y9XDkIXXfBopCleGsQbl8C9BnCw+XOp5xW6jxIxYShkH0AKBcw2Nks46sIGz8"
    "FuARngYN3HvbiBUtLA/1t+lwrDeJ+lqUlLUFWHV7xxAFoCmN9g5BG3YBnpOAfyyAbLXo3NwCakiY1YD3MO8Gn7NAY5ukAtghHgLo"
    "+5bWkJFshlrHt7nulAC0nROAmiwAsXYUnnd49duiHVVKqU3atvkd/QQpqPXbzm2jzlLQd64UdMzSxhJRSAkkZQLR688XiH466o7G"
    "GOQ/TgZqTOP+dHqXTnQU1+g/rcF/1fGG+rA2pzf4H3oJjPoPnbVhglFVNy5H8f2u/jpOp0PyJFybxKN+NryN+dviPxWatH5vpLfx"
    "BBq1urkZJhssPgHca/9e1soGJbmx6omktTbIKv9ZFapSoSp/+s+BGe15/+LjFcWo9VYwn51KUCCebEz6g+Fs6q9HJapcQlUtGzvf"
    "p3lmYKaN/wksauZNNuknCtj0da0+XYv7lDd7I51lf96I7+L+R2vApVCcZhO6ka9iBQ80SzvAGDSzm0/qgqt8SicckvmTOuEqn9IJ"
    "WlVaXVymSbZxV46iWLyKhSRhi413VJdugZfXxCJLxkVJcn372Wzk0lr2G/K6sdp5ymalOp3Oxs10A6Pq9EfhsiJk7uobKWpKSvso"
    "kpJxf4AOGDmwSbmqfH0SWVB1/ISBHaT9NehbkYoAvMb3a9N0BMD198Qb01P9HpOcDtK7kg7541PpVq67lXQAfZ/hvFuORoS08LSh"
    "E8J11jg4mPl+1R/nhiJNV+HLkgGwT+7GTX/6cQNNH6yRDBM4NTfkdIrVGl6mk5vq5TAeDdSKV+9XLR42XAS9OeL657Bysyy2aHIK"
    "09m06fZNf3IF9Jg+XPRHF5WN+tpf+Bf2RV3wjl37aq0RBAWKnyu16z3pCgV8a4bbKQ+sLzEZ3zwswM4mU4TsOCU7290vt05W0eJK"
    "FQHQwVh4y3AoWErfZDTOgAkGlfJhA3AawdrLPIS+1BC9K1oE658+SjOO/w1BaA3uCeD9M8bfxPF7d/xfzI6HmYhxYjztzCdpmnWU"
    "dSzy/7dwEqJtLKxu1k8uYuH+TyKLoUZPi5sxnI1AmMc8+LtJfzwm699n7hv0SiGn76z6nH+GhRIY/w4L0A8u4PIDXBt/LUDIGV+Q"
    "w+t78kjNQzEKEcgkwUTLyLjNQKmXmGbnk2tzFalPOFCobjAjCuUAdL4rTsKCKzTFx5PbEL+jeyU406M8FygfyGv+KasalcgIaBVL"
    "z71iieilfNPcaieKFtGCuy4siuFOMTMC4fMxin4+3ONBzfVRgT4T6XhaRTRJBu9T8hOJR5dRL1JCXyQeLIsFipwf9R3ctyCeHGlh"
    "k4XQaefqXqXAgD83Yw4v0OFYe+xloA0tUZTFOSGz/y6+iu+l2ImUg3ev78enunz03yqVSq9b/ctJf+OP04B/vtr49TQIHosfahs7"
    "1gcqZn+gh3k7XASYEIJkgSeOwTsCq2lqeJsbRmHpiRBYWYwHubLYZRwPkKeVMhKYXxdary1Ctdi5uXI4W2uu5Ae3CHlrHsAWLGuz"
    "vsDYuTHtSu/QBIMM4VhaCuOgrC5lEZKVre0heVgyeu2FV17EjsayBPyT+PcZsMjLWiIi+mawrBUqskdGtMvXyCpOe16KczFfqSPe"
    "nFSKdEluGQqns3xsVOTpY6PiK8dGpVaMTWj48tFJoaePTyqsHKGUWzFGDEZAW3SEYSSWDVSXXFpolqV0ZJegE5VaiKbvpyMkvbew"
    "EQ3J1xT/+fhCEetOdj2chs/HfVRzvpHjil4ChTd+Tq+O8MB49l/OcZBfXccjYCSmaxtrOJD08pn26Dnq8pu144eb83QEB4hqAj1U"
    "7E8Y13jSz9IJHjL0JuoVDyfpYC1eeE6utTjXptsd5vOCCU1mF9RLl8vA+3X1G8+7LMUmemoMHd1hSHM2rky/HVHo/MQkb+oeHGHA"
    "/iEMRIX/hrWAExfxIp5kD1RBgsclYZzMbmDKQFowsjmM7XJ4NdPPd5NhJr8XQQejb3ehiun+4MgwFoc4FEw9RuEnDPBhNBY0s072"
    "ElgF3QLVyijKPE1tvRulNOro8XE9NsGpsY8EwzY7sP06mkUUXDs+EeBlaFN/M0S24BTTKTCN5TFOuiC29Ucj6nGXe5xYPareJrvZ"
    "NToFvIeuKHBAJfov/8VqeO1mNs3WVP6DtbF+z45BkU6ymHHMbIJIj7dP55Dynwa4ijimI82tFDmVj0cFrX18g1mET6KL635Cfum0"
    "9+Dv+Wg2sdPZQk2cUwe31T4yzZ15bkuiP5JnGwoV+Zntj7BP5jM50UZymRJ3R0/CqmMZPuro90LxC3uYgpDZEy7P/EHh9SRGAeXt"
    "cAqzVh1xPJYf+slgpF4pppkebjC2G3RnjR/JQ1UNsEtPzODhc0jPhXFRYgX+WbFKEJ8VcJ3CoAt1LN4sWITnMYhm8YeERlgY3yw5"
    "HyaDd86MK6one84vXnQrxbcYWAp6e6jwNYtUFMhglbMB++1X7A9SmLjz6xQQa54mP/Gn16glcagYtICJPiKpC9jInTxHNI9vZ0TA"
    "gEhU/6Do5aaP9zPYV4Zvj5SKJwpRg4OO5jJcQNAr1b+aO0KFg57noVIOL7pxUoHWgejSu5v+5KM6MchnSU/1bdy/jUsWxN/1ssWS"
    "aXfl6FWdvLpE0cvtiYHKy4IjsudfGE9RzPlu5iymzH0SXyK2A79UfR6Pgo5TpkrHLfoJ/x3Vet3X0kS+1stofB+Fo6d0AONG38Vj"
    "Je4VBcua9i32bhtJkhv0sm6z49+NVpFGRzlYAnnPunWA+kIHubL7ppbwmIopXFjFDXeFgRp4Okg4K5psMmLsE99SaE3IGkYk42eR"
    "V3AkNLU4U7T6IKZ8Ffh2cCb5j2xYChXtopOaPQ6h2jyMb4F0F+EZJrvuaOr+0eR7Qt/QrAtHotSe3OyjliiockcBp4/AXBl0FCZ5"
    "EPFBwiP7MX74MHaGhgewPQqjVXDALr1TEloFK4U6eGmMJzEdK+EQfpG+YVc1Te+7k9Cl58MQCQ+H9389veiP40iWywUAEMH1umDi"
    "wvP98REWg5NeOotob0RMDuGsqTUuOn2WHjW78WgaE1jipVBwkaYbC0AwhQQDxOo1y3WZhEum5u3Pi2DTu2F2IUOxd3cF8/5c9Kfx"
    "Wr0j80M9AR2kSXdudD74VhkeR81mtdn892ixez6B17tUv6Hq82YvtsDvdRvtdrXdzrXRVG0wTSm2odLdSht4KahbUExPkSNImHYL"
    "2yPOsIrZWTC1IWaqSCFkqyhmi3ZL8RixUcqgw27xVIeFQ55i/8pLpUOrmdiH7Qsf/+A9UVElsXycPkbE07j/1GQguOflMiC4jN/j"
    "Y8Xztrt09uuDQQWz68QeMrgAfEgG6R1GtXqNSVX0QCPuIgo9/QUaSOXz8FRD3ku6m8Q3MJhP6FFxZzKFd/FlEeMUuxEjXqKi6z2p"
    "vDzsDPPh3XXncUExmzAmIwVuyteyzk+ib/OFzTjl6sCQju6qvANkWBsXFDkrnKeT4dUw6Y9o9h3gHOlQ6MimGUGzC4oiMEPefU4o"
    "jkJWUQxZc4bf43hRlukQKy5JFCmpqxWbcNR5+VdKZhpTOSWxLGvP0oGuaJFLKnXosjYthemKNrnkIjT0q6xNS6m9ok0FzCOqsQiH"
    "0z11c6Gkv7JxK4Wl4rr5Ugf2I59qoqvUKP0hGf4+i98Mytp7Phy8jM6UxLGga4/+EPbGdyCjHnlq/TyqzOkqSFCLr4UCuX9YUuu3"
    "o8p8EZqTtacvMLwvA7MtVzYajdNJ1h/h3YjNyJe9D9ReoKsekMnMfdbxfXhEdTq/P4TKgq/z3RH+7rw/Ct/Dck47hw+2Lmz/abqw"
    "/f+TdGH7ri7sjaiSSFXUFd3Xx/hB5RGUN0CQfrpLlDaM+5kqBdGyMthMBocNMKcq+JWecqan7G3hOwrcO8aEYDjEqtG6cZwijF+D"
    "mDF6AIZ8YuUV1JN7S+uLKeyY4a7vZl8DcaUsaCqr1G728qWavv6GOjvOGDdfdOy3u9m/N3oAMx5wJQkwsAQKDK/7wBPaM3snSkZM"
    "27sIOitmOPWqHTH1YByuqgqjCDr2mPwDKtdrroI+MM6YLU0B2FJlvitqUv/4F2pS/7A0qd96Nan7KzSp3xpN6v6/XJO6/x+vSf0Z"
    "081TkKVxdBr+gE/Im5tXH+wChnL+XRY+BGE07PP80u7HSqQJMuVqhxdEdylNOzwwhTbLYweb+bkisQSBwt0D85em1AbdgcBZbl5x"
    "UKjxs06/6p55CxB3x9nNUJUMMC5Nig2DcNBRQcjh/IurclnHIcj7Vc1USYibEx6DZS8RYU5Bc393qgdmLunU9Q1nDoiVnKpCPT1H"
    "tcIh/LYDYo84LHlcdW+Y3JjZ1tdCwpNhjokvZD7JF+hptp/uvPBAsZ+rwwFmd9SXcvhgbvGwtHmSsnK5+PjYr+ZZF0Z/GdN1fzpO"
    "x7MxTkipQpz717hqPZkr17iqfobMvmBqWPhrpePW3FN4i11RFlb5FYrASUtFvzhOU0wWPtZVXFzVv7XSDGbEv7TiC9/sSxnSQfVF"
    "R8San9mYXpAOyBKGuR36vVB4RCAM54LNCJ2NmExdED7mcj4c42QArfPoOEsIBXFi6udCOxKEsI2riNxVQmjRbdoISiGTqjlMtJ6r"
    "DqJVHayqOutpr5peKl4ivS5qNdQaEPANwBWYFXAFplWBqYFetQAtAI2ef1SdjkcoYlVx89tQfPFiaASjA/S8mI7SDNMI848qfsLm"
    "epH6BZITWj+w8RHQEG5sDwg42WHgkhqZ0qUbyoKBiIZ6OBXyZH8OwgJvfCJ+Iq8qpmovGkaWW0pgaOXSDnXMYXes3nEovDmJqGEn"
    "tHMAQ5edXLMiyrrwXV8BYP7IIDa/I87J+TlANoYiUWBga79dAV1TVMPXA1q7wdCutBK87lCeCOC6BWA4lwrSpQ3biK5HNOzs01Ob"
    "0+HJSzoMG6RGq6EHa1Xwge1dZVqAjFXFhcWq5peBwkCi4ctoYU1zfJEASdzg7N4b/YuLeMrRH/wZJfRQuMIrLC/FDQ3Ot/WMswm/"
    "rwy1GjkI61sYdv0inGuDq1gLqE7IOx8YD4gfEZZAptBPLq5ToJnKnJFitvMlI4LTvnWED3xRZn2gF/DBukazvpq3GgLGLQlXY+mA"
    "C9xDJceycaRI5K/06f8uvmQmq8hEeLkEd1sbGEgd4rdC3ZrDfp3o18yBSRV6MDiZcULLohrCAhOVfPEi/0bky36ohcBgYTOgtp5D"
    "kocMhv1RehWVICGIpPy/+SK0eakgdPmwQC2Whgeys/bmv477A4rO6lAEZecKzRdX862f1VaVArNd1ZsgLKvEZrOmijyvqKDSUvHy"
    "zfnyYSgaJPlblSuJyIG0UVK5XUqLhqp8OMJg8G2TGtg3Duah3Jb4nWe3U3OYWd6GtISUp48gONlB2hcYerK5YBInYTplQ9Mv2o30"
    "y2zO6NTUo2xTQlAoeCc09PNRsDg6AvYKuLFJ9+9HJJF+f9SVDWhHZofxbfRvOHm5E0CXHdYArD/66lEOQS7PweUp5C55hECV33Oh"
    "3lEZDa//Ki01ci3p9ISFJnW4+kX4D2/4+F/yg8suNtD4GeP+/uobuNT7G0qqkp0kfG4/xPt2QPr3E9jbfTQZEotmIIcPHdgvfJuF"
    "mk6M0A9/MRvAbeza6AHKYMqIt6osPf0AUIKHRT66faxjz2dV7KXXm1N5PlUmbph4vAMBWVb0ThTenAKXkxNbxS1kBZnXXyTbIwb8"
    "DRQf/BX8BB69EtDbsJ/rkdbC7lBnXKe8pXH3GxVBHkS9AJWN/OjUD4D3i3XesIAzQsAJpqPuo98ZKgP4+flxRSXVi+J7APGZoGWA"
    "OgIus7dX6ascEzxh6FXKhZj9/Q4Kj6Twid0iEsUzlR8Rybm0ApDpI/nuSfLEng6OHBaqm7y6GCWbZ4oo4C/NSWbP8JrdrsCve9G/"
    "RS/dV0DXTpUmVHAqcEKug2QnMyMsirsyCdQYrRe6V8BDddXjo1LzFqC23o0S0vwoLVMU7TKOTvZQRSsH4o8VIRIccD2c33US+F5c"
    "hKkMYiw5MYOXSjOWdXVXvWgtemmaTDGpBge2h0Y9bSwCTCG6wLjlAw+20Hw5J4a1tCc/VpimVLlXzI04J5GboY5XHKF6wEscPBJp"
    "KdW6YGhjyqYXzeoi4UYYnh93rHz8UI+ClQtH+U8vFVZKTGXd0HgSA3WAsY1VFmWa7qeN4v1w/ISBBOFYRrG+rponuqMjEgDw7YgE"
    "P1HyYEVtVWYbMalgcojCXjpSJDGu8g/Y+mOV2pJT6WiVlSGTKtExzYQTRalMUKr2ixeXKs+fcP9Eq+Ur0yY1E9649sYM1Y71V6Ai"
    "7JRo+lu9T8XMUhBf5ZDt9TRpok7qNRBPoESG3U90diNOeZAvuQgvhpU5hbazAmJLWj8Jgc0nt/ouLa4rA6SZnWVGseHfH4Unbtfe"
    "PC8/ctpGZfhB83uvIuAHL6N/j5yk0L9j8G3cwdbqXU7SmyPhCVSCyPB15flxkNumGIseNqk7fBNkfnKvo8FfTjjpjgLeV5ikw06t"
    "xJt7fJG9ZZIEv1TZBcYALx+gFXtd9WKl7LTEyzxUAVh/xdnPNGxwYx0rzgWz4hhuz/mdDzc/dluWzDyACJKA6B+ceVtzEc5eSdLs"
    "mm4zKHnBQSXTzKf0gtxnu2USQknzdUyOqPaTb3WEFgWoFZNimr+4HA5evPBVwi9R4GLeL0e6Jxt4v+KsBgatnTRETxiO3ZagSY7f"
    "I/4ym4CEQ0EgmZooukocvHS+A3yh3f8nz1OScReYXGB3xm4yMlozri0R8a3Mapc6s1qjmFktnLKE+kclerf/5rso3KhTOs7nRyWI"
    "tgwZdAYsQ+wqil4/PkqyW50Zi1MlWImxVNFlGSEoA9DTovsnH6bx8SjNPiExhEkRh2lgepIeSBIILem1UJEpB+eS4d/AOToD4TRb"
    "VraIXHqvUEFZZQZTYJNHG3D2kqjPusm6mzGMMjvoXMLI0XAdEgutg9RK/iZypGZOQ5U4N9JnFLky0EkUSdKubL/rJC4+DZN9fZ9H"
    "1kdG9RZO9rU4Nv64QV6n+46ApvcbiEb7BdFtLVckdYugeAkC0n6JALcGXUp41Yv9ciFv5IhyRJGPYPQoWIs0p6W4+J4SEr3vf4yT"
    "nAy30C4hAgTKigsgEPktnOP3TrZgQS4BQQ7NSYfdFHgskqPghxJz9M+py7YnVXsEvf29yi/Vi8uroINmi8dxFmZdlRUHpKqbSgAc"
    "1tv0Lp7s9adxRbPklkhGHF8CXF2ixS2SvdBnXktmIKihcd969vh4klhyD0IstF8oTHJe2tIRfFD8slOG8O7sOr4/VVxnlBu7lQwq"
    "CALKR15RGXbi3JhYXmXrqj1McjKJYSN5ykA7gKhxpRY2gOdaBLu/TwjcBwn90aLe83jE9t+VwM7vdSGW2DFat9gG0Sg5x2h69x3T"
    "lQqq3jA9Furh+ld9VqGFk4pgSUC2ymvUFJvqQWt270RvVSfEiaD+U168AmJ29116l+BxN3WyIlE9z1icpnowDkZaqQwnB655R51i"
    "vervs3jyoFw8KkCss4w0vT0NltAznPwYP4CkIWqMk2q16m/91WhkOuj1Tk5P0Yodln8Q3/90WRlAf7iKcqS8HsX4RLYPydc1kUR3"
    "l01aDQUYdsym1POtcic78SV7ywSsG/UweVnxzLhX78A5C2RfA2ahLSdMxDadC0eTRiJ0dzFmvmaNLyWnjPJ39iw80Q3mALrrXAhT"
    "cIy87yS+POPkOmyUQAr00GRwV7xMSXr35ETlBB+qjOWSTX0acxp5J9u4fckuBzQRzaqU9ubozhcxR8Pv+cRcVHJDSuYTz/8seY6s"
    "QeBpZx1KRlVr4IKZKBksqdUzvV348p1OiymMBC9VHq+hWHvo96bZYRZr3SdO5hkX1/cH3W/0riNNmKzk0XEgxiVnlyhcAlv/uvJ+"
    "L7Bo3OPjfIFZkSSnrgn0Z+SsyX5oEjAP90keyJM/WxJy1Rys4AiU5Mbr3cdWTuIyuo7CLk3QKERWKRSIY9KjTPcpL1NCUy3ohpip"
    "piylqPrLq/ng+/gq4DYBS5J9k5nKpYdeIXa6b7h7OTd7Dr5Ktl+dGVq/TmKV0DTcrDeQxjjns9XHxb5JO8W1MyzyA6edcqW/sAVM"
    "4j5zW7P97o9ZZY51UGMgCgQAOT5BedTi/DQGbgRTslmZJ/fxaCLmALbxr8cVZlaU8n2KrA3/6vz1+KfDKhyRcMjSTzbuGl4+oPPJ"
    "gk26Lve7ctZCw9QqUMYx8g3IHAAJjHtoJNhJ7NNxvF8JhG95u2eYD2gBiT+1wujGihluVpaJcgbSAJWBCVo5HVJiSbvgy7rKOVoo"
    "TOYsxJGdLk4RkFUFN4BITNO60dO6BHjRPp/D0GRAmeKhFI/QqgV4ouFH3B7Xhdrv9uhFEF6VNcwjwit/+Kv2hwTzTNa73YwyQ57t"
    "UxZjBWoplqHKfziAUrAw4S13geZyq7rBpYLPQyg3hLXKelyI5Aq0WRJjlbHip5D5SHqTThws8P/tNX3YV8aZuLCTrh5hMlDjQ2wA"
    "vkC025JSHafGSrNhN3l8xJSRGbmR7eZGTmiqio47SS+KME3eWNYCuGlSyiXoN4eF1k06dyrJ31XpGTxKa5zvdTbt446Bs3896WVV"
    "/C5lcTPRQp9RbNesah5CYIZJGd8Z9tbrHWKO6fnxcV2mgatW4Z+Pj0NgwwpbjrX5dIkdSls0YK5NivN+twSauyqZcVf9wJ4r/R4A"
    "BjWCajyYuhS/A3vQjSLldgMCCBpMgsxaGd+FTWR09Xqey3qin44saab0fTL+mzRNREXOo+ds0+Sz1VleJgvZDwW2LP9Y7AJcEsK/"
    "CVvmTm7wjOtMgvD7PdjGcKSQ0KkHAXsbG2evXVJcddQrmBcnA0YiAnJVSK87cA4Fi+EdF9rjPuD4mj4kF2sm73ExDbQLczyS1Ulp"
    "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"
    "OFGJ1ZqR5HA47F3cxHuDUVFLFm9Gu5AWeVxP89Xw/bBXv6wNNlNNR1eVUuWx21kr0j4TmMnR9rCzH7VijX13vt9lWuN6Y/u8vK1V"
    "6pelZmMpXQxX4fl0kCuFN51y9eWm1yx0evHyS3iSnVZ3tXOz3Iksd+bq5vnO2N5PmpXb+j5vzgL1fKmKz/TOtBRplR6aHeWiONUe"
    "F+Xcw92oGZ5WXzrtUqUpzfOTDOLhNCnXmLQao1Euf5PLmoHx5W1+jCjvJv6c2Cvl29nz/kFdZc+nu9Jz/Haee3nelOLdYXj3co/Y"
    "5tx+E9fkQnbeGd9fNjpjY7e9u5HkViKpZEtKpoAuTKO1Xqvpm5B6U+8Mk8m5VqsnLuuFDKKn94lWb5qsl5vP5btd4jE5DqEbS09Z"
    "Fqcv9XYmhzidKbqnZ+uBQSg23PVatyHEc4cn2/V0ub1tFc21Gu+2ps+Jbisr7zPbfSw9U0fyc3uJbtrdlTwcJfOmie653V0geVmd"
    "dZW7xeXl82rS7lUX5c5LRHoIDUZ7/fllsZJvQpXQtDOW54OMluiOhtNoK9u9mFYqu0ghnytn8vPZzTKRmZced9nMQpISrUwvX0Gs"
    "Uq5d2Q3Tl6vsM2JXb2Pd25oSDnWH0666ys0242kuW6yUeqVavJXOxW5CnU5PD2tjdKWZNCd3yVKn+xhPvGwz49Ckre2n+cKsq5Xa"
    "8/3lS32ZCFXLsWljsH9pa/Jzt5277DQ6gdU68NzIb2L3s2ej3Lif6jfRUT4UWswmz6v1Y0+XNjehZbgWmNXa++3zXawS3Re0ePqu"
    "3jPuZvFKI51WB8rcXPdqphIxBq2QqUvZSLpTjjzo95Pa+f52E5UiISXc6Zg1+TlQnS5eblQj+liIzMb14rZ+v6k+LEp66KbT7c1D"
    "z/lYORJL3F/uw8tVA11llUoiN4xfhAb368A0f4/WnNTYpIv6PBopbGO9aOY501zNsqX8nTSTO+qgrF3Uto8P85fouZaI7nLydNDN"
    "XsTMVWezWCb3mfVCz4+Go9F42NUWL41kYquGVpt7rbXcJh/L9WXlftVbzsON1eBhv9s0GrIZltTqtH5phMPVC7OE9vdjoRuTS9Je"
    "2oRhxezh1jW6LUyLavZl1ruc51fl5bZ4Hm51uonnm8709kYvNSOd9fmmVLpNVoYdRXmej+9k05CKy0gtuxsUAnWtGXuu5Nrb9LNe"
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
