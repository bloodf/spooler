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
        if spoolman_at_least(SPOOLMAN_EXTRA_PARTIAL, fresh=True):
            # Spoolman merges extra key by key (from 0.22): send only the one field this changes.
            patch["extra"] = {ORCA_SETTINGS_FIELD: value}
        else:
            # Older (or unread) Spoolman may replace the whole extra map, so every field goes back, as just read.
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
UI_PAGE_SHA256 = "b77a81467e7a93c2a0ace8d794b8304d90a4357ee854c6a288c678bd4a8913f5"
UI_PAGE_BYTES = 1271866
UI_PAGE_Z64 = (
    "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"
    "XWIS/x3niWpl55mSrmH7Dm4yW/K6uel8UY3tPmMyVWzf041mjerq9vNGNbTDzDGVXTN3BCKjHPIbT4Doh2AS7cvK1p412qBoMYEl"
    "+I5TJtPa+qnzl+zuplMn09wGU+gv0eE1Ww9rEd1lI8FQeGdkP5Y/t9ls+J9Eh60Zd6udiL8iJbLu/vWobu2+zxTdEc2PZtuNXfz/"
    "M/q/Pbtu7v//i1Eg7Wpfi+OW3vNkuV2w+1jm3NDD/pfu89YMuan7/S/T67TLey12W3qxk+V2we5j+XBDT/dfus9b8+GmbvC/TK/T"
    "rue12G3pTU6W2wW7j+XDDT3Of+k+b82Hm7qj/zK9zrqA1+K3tU83XXI3HD+WHzf2+/4P6PvWfLm5U/gv1XuTC3Ytljt4VLNld8X0"
    "Y7l0C6/r/xgabM2t27hk/3JUmI69YDsTk0rs5PSigjsh+NEeTmr6I/2bf4F+b+/qpLY/1tH5OXuO6Xd397sbQbIYYSMbOl0RdEd2"
    "S7SyObN9mT5syjqJZrZgnM/Ti81P3X9iZtnUyZmD5Mdw0C7u7q/Yta0YaycP9hfoXOE59E/NWhs5JY0IfhRbbe2O/kqd2o6htvcx"
    "f+5uFZzT/sSctIFPMYvax/DQll7jL96XrVhnW2/wZ+1NweHmT8w0GzgAs6h9DNNs6eL94n3Zimm2dd1+1t4UnAj+xEyzgbcui9rH"
    "MM2W/tgv3petmGZbP+tn7U3hMdpPzDYbOdJM6H0M62ztOv0qPdqKgbZ3iH7mPq05bfqJ2WhD75YZxY9hpR38m1+tX1sx1C4+y8/e"
    "s4wv8jP6gjb0TH0aP6TW5GdyC32a7mznI9rWtfipOzROpi34PNyCjWyAxzaM8YmR2+TUeT6K+ZF8cBwqI384mYnECRgjY4aO3S0a"
    "KeSoT0wI86F0N06YECw3SpgQLP9GCROoz3EUdm+ZCSM/+YJh5CdaGPm5MYx8sCwOIz+Pw8hT175oGHlo8WuHkR8us/ldeBLIrC6z"
    "ZSqnSDZetB8nQuIk8JPpXAzAsatCBk1hEl5NMUR15NrAOMb/7vaycbf2ehxe60f4/eFDhGmZnsHjwcE9EQeMflFEIHsvE4lsr1fm"
    "4i8nc6RHNKGsE/orDhfpWgcHokKtGsz7BHRDHMRP/SOFPGd5gXUuMTR6SGQfU94VW3W/sn+HMU0AqyC6XWGaMvlgaUAciwi/8q/E"
    "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"
    "L9pytTVehL5Fg8e+XlrxdDzu0p27meZ12z+ezpN8fOcK0sfzI4GPOvThXoXdHpN/ZSDcXmqyX2xznE5qXTcR32Hne318Lf5puroF"
    "DMNIfmoe/miyMxefVgK3z4ei/nJNfXvi/tFzcSrpT9RI9XBjikdQgq/PfAqXnsbPzjwNZkuWe750fdTpMmR30HS3BDekutcJniv/"
    "W8NPHX1uar3atX24bjycjnZevh7eIsplUXLZ1b4z56/rCfvnF5vGbzkaLjkGCaw+fnlmyr9rw7+y0+/UwBMJrnJ9M5ufIk4/H9em"
    "T8EX1Mo3hvnkYMvLlLqsQL78keVn43+g74mDv104GBvmoZtb+fmwPQVcB+Xrw+OM9dwBfSX08HWj75vOzxOpvuOYfaTF+Zu8vH93"
    "7e6pynqYIIfpMPlRLj/Ntz/O6fdSfBn8qxnythH39Nb29224+5SPUvsU9KYx5j70/qebPfZ2prtcp6XDoEX+8QX+dh7MuyE4k+y7"
    "kQ/PlP9FJmq7Pr2ycBWIYZQ+np52S+ITlsufKf171XRVu09nc/5U5Q4tPa2M3jnPM6yTphej6M8t+5Mc3o39dW7/42NqH36K/BOU"
    "6MezKn7nEa0bVsE55WDyPk0mLwo+693iNnO+KnGwPk45396qffjjfIrx1ZRwa+ylnV+eN+buXeyfoCeX6Lt9uZOL9qVrfSB3Hn+6"
    "vH+UPZOKOyiPc2MurqHyjOxxTnwyq/Lh57kHD9Xl8PLdq0sP7lPaiyGVXFOfDiNc3fYny6NJHu2ON0+bXg8Mn1+s+vboyH/UtM8X"
    "SqegQTJuppx71fIvXDYv9m5Oyvu2E3rzizwb7vMoD6J5YjfxE3ORPHng02evew1LqOrzW7cQL9qBeTiL8/nF628Pv9WX0xWPuiOJ"
    "7zTHXS+/jurr41HPmSL5NTnDv9xeXn1mJdyduxjIcaFBcYJyv97SHhZrJ4L/Y5gczo/R32zC+2wv/B6XuHObvz6+/FVfT3jcH/S4"
    "nsKtb8/Pvdad9xrnnVaLF9/LnzZTvPlo6PvReIr69FYLP1/0yNXhEpw8rOvs0xsDAb09EK/b/JoiTw+F1U8PhT2dCHhxruLxFsiN"
    "ap//bLQvY3qr/YUr9Hou4BL75PN8eQT1muDmBb018+N9k1+6B+9a/vF+v/KkTO8OG10jb7uXp3y374e7fcy3Jf4VOPlpT/JCmPO6"
    "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"
    "6oPBHYWDO/jvuL1wmfDZw/Np5/dASRA9fwcxTz9PTbBicqotVweTAP4D48nNEpeHlKtFLrVgbsoCFEXrXuz+yFGDTprnqMG/P4z8"
    "PJ594gWG6D+D/M6C0C9pwP21ml/SlJNTDzcbk/5Vtdxc/z1U+BPVeAO2fwW0X8/jlebFlggjhn683mimdLle4V9V79UY2aXO+5wc"
    "ntTxzq77CcGPTfNjdb2jfZ8WzqsV/svk9OrM+pe267iWj/TcvSrfr4yJz7U8/Y52/yoi3sOY9E+wxYvunVP1eOG9d7vt53T88xz7"
    "pfT9B5jpEXXhPezlx5+2Lem7lvPfS+j7GfwBquH158bpHO3IDYbhUl34QPjcx/i+GNjnaPm/IcYfsuF/5oLLcVPVO+797T0QlvqO"
    "3RU3K7zuyr5j98UvqP6qob67MvgLKr86rr4jIP/z1Z/Ntm7X+vEKlflPCZcy/9kKf0q4fkH1nxeuX1D5zwjXz1f/QeF6V4WeRbX1"
    "+fzSjt7bhyJ+7lTu9XsZbt3vdPlUOLDTfhOe/Sa8M3Zzv9zVYeG42NVzFbcO71zcmnN1Fenm0Ypziq6eqvj/d+d8fnfOe/dXXVnx"
    "e5f2vYiaf83cqW/zTlFcXDnoc9MzuoTifWu279kecafBH3PiTvQ19D8/5dvdxPWuWx2OW/LxxZVzKj67seIqluvbLK5XfHXTxdUi"
    "n9iCcRXX/aWXGOth3P1FkM0H01YeLx+mMHV4eeEDQqcFcR5hDe67B/PTH/AO+wsZ/GAqNd2wgvv+v03jZzyMpyg1wzT54/eLs5rf"
    "X2zY0BJ8/uuv8AQlqKKuC2Ly94vX6nhlwoect2ZnXQGFV/dcAv/jDzvY2dDxbiqBtcHLMgH49BjV4Y4piOfwdAx1cmHWMSiszH8q"
    "eUOsVxEocFqTP/vzyvo/4RWvxzBRwMCDWujbYvjiBJfqAYCWedmEVU5RTmpT5nEIhTPn4vTt+1sSXkTyMj27msSIDmnCx2kyWNIp"
    "Q8maXluAmiZ9v/YYwn83TRp8lK/zQjKk6eXljWkCSFzg+7wlbb9Lg7s8jqs5uaRs6gN/TISfggs3f/x+69qxW4JxcpXUR0TX/qwA"
    "w270ZiAnDIGvwi7JAW/7Ii/CLG9JLWRM0nwNtwFFiXJhTsHgHUwR/jD1/dMpzC6rQYUuwhvWIFG/QfnbzIJO/+sv7dm7fA2KdnYH"
    "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"
    "uYq/4ppWcRphWXBRG5VWtYW7sN2o4qLi+V1vQ7rT7bSIUnWrNVy0sNXtNp/jqdwMW0TR6q0aTFon7NYbhAxhp/Mc9m6j28Fkox3C"
    "KYqL0u3CXLeqYRPWGBar02lDug6oRDjUqXeQpnTDJq5Ni9rDo7PRqLewfKdaxe7hIK238DsMs4s4VGtUu5iuh7C2MEmAWw0sXwWk"
    "AvC7DZpsgKcT1ggHRVoPvoiAXF405mnKBOSpQUBeiq2aR0LkVs4jIm9vTkR+8cQ3QzWMqbyVOxHOjG+bxjjzauUUmBu7pr5sT+NV"
    "rjGgyo9l4RY8s0yv9cOtUQY4/Nlluo7ZdDSbxdEcr0vuMIoCCKTT2boO7nJd9a8fqsPjV32KEeTSz4Vhxor9+64O8eHRB2pmfS6a"
    "s/5++mm1486VKluFCl95AOW7mTVRJ9efgaMMYtXxanvcLhJvoDJlNrKR0tSGFTNqUxvXtzSfNqydVbta2cBmylOusozZvK0Rk0Ng"
    "bOtQDdEjCVFvU7BXau05Jqhm06uMT1eWzcNTb+HCTQijOEFHqKSgNJ4QlXJ1Lw21GfqJAVh/LVXLWws4N+JStRIWTb7H8TzbeGRO"
    "ANb6KhfTqawzFGuj5rqi9iMGXMOH56yOdtMuRRM3olaqboFe3ZrgFmN8ERDsjkNA4vfclr/4YbAVGqVNNBI6b2uM505RRI70rNhr"
    "+Rqrtlon8ku2wZ0vfaGK481GYik/ftGqiWAFuR6O8s+H9ZUnc2qZypJ5DRvKkTlF1lKGzKmbp/z4ZVvp9hZHYlD+InlhhtQ4+RAh"
    "6/f9l3QvGtmo4w8YdBwOaLxFrqT/BTuI669LBDId3+g4ur0DJQPPV6RSV1+PthoAm15P5a0rXLPqjYGWLaztbNg3Yt3IptzLijF8"
    "4fGg4FoDoMVF4M8untsc1ndxsf4NDcquI2nIQlLsOCbLXF9sxrhfbMi7X+T4izFBnpwG/uwbzfLkdP1ZhrLrzHIWkg1nGfrZZJY9"
    "xQtn2Sm/nt5/VunFUHczBXYZTT7PliWtEf5JaiZij6GyqvyN+eJkw9L3Z8NX2A6r+ZASyK43t3Jf1MJK4ie2ZRN6alJksR415pK+"
    "prNfZkzvSU+Z9OwTj569s/pWHdS8Tzya9+/xSSODsCifxeNl4Dlz4JtQWnJxa4BS1n+pp5ofokVszMsgYNHronf6KaCl612R7mCP"
    "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"
    "mcRPn2zx0+s/s/hp7+uIn16vI376eLfip9ffRPz0MSt+enOH4qc3hvjpwCt++rRC/HSg7yqf7lz89Onbi5/2tTrvI01DTTnToU+z"
    "l70FmpRVT3lUUceitiHG4yXHcxt/k87qgJQbeY7e7zJIzNN0F/b3HsmYpJIvdxO5fKotbhIcthJF9VbV1uIoPUX30H1GnH9oTfvT"
    "FYfW1FTIVJHodQx6BseUbfGgXU3gEDWBaXiaj4JZN/yvJBnpoDbpTiyrbVTFBhZoTlEJ3dlVLJgS3xFni+5WaCahn7LXKYwBnGCs"
    "YFM6DmIc1zBf4vGF/NTZH6VX5V0pGuspn2e2pC8VegiJR2VbiPyk/bdUzZb+EpT6hEr0vB4bPVby1syu61Unuc1JS75s0gomK2+S"
    "WDq5b7oxWL5XcspDQ055vh6Xdv5n4tLObS7t8Z+ZS/vv1+HSHq/Dpb24Wy7t8Tfh0l5kubSf75BL+9ng0l56ubTzFVzaS82lnd85"
    "l3b+7bm0J0q2y+fnE9qi6/sO4S2tXW2INO1KSOKSIzXUBS7w4n8xHcWGew6iZ9E4SR9Fo5GdMY8vph+MhkkOih6ysQOh6K/8a9CZ"
    "U+QQgL74XQCg8ACOzdF4MZtEn4saQRWwIocIwN/QIFd5J8B2DsX8FEVwPkP9Uxg1a3muKPkY52Wtki8kjItVTY5GKxtUA5ZimnzH"
    "CRfRpz21vgu/WmYNrYxxvYWxtiglnXlk/IJgUVZXfSMUY9epwXzjJjVoHTapQMuxSQXUC96og9Fo0yqvaEttWouGvmmlQkcSoshr"
    "QP94dTnccabTEO+W0kVXeA8Rk53MLi2HF7klsy41ch+xRCLnbQnNV4C+vB0vxnSuhbINtR2tlhV9EG9gojqXQcevbBcFzVxI/61v"
    "gF2JU+HXl4tTPMLn4wVQ75ibWvEu5av34EG/9PJjZXpyUhqI78rQKq8Oe24uWwXgvHw3Eu9ZZr4slRxy+ul4FJfwLcCjdC0l0QKF"
    "xDuKSB2JBJwFx5ZGouf7TlyRR9SuCGXrLId68yVydVQ9rihaF5gV5Er1dYvlnr/FPGB0y0vbS4dHR1uz7MDj3r6S9hI5lHXVmpN8"
    "teZkDbXm5M7UmgEK5m/0AeQLwO2+KJyNT88mqK6MVi2iXzLxVUuqjI1jfiop00sBojj3l33E+S+JP0xMKO/EFjJovLTzDWwkK4th"
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
