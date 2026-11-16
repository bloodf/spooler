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
                "preset": str(getattr(bundle.printers.selected_preset(), "name", "") or ""),
                # Your own presets first: they are the ones a printer is chosen for, and the list is capped.
                "presets": [str(p.name) for p in sorted((bundle.printers.preset(i) for i in range(bundle.printers.size())),
                                                        key=lambda p: bool(p.is_system)) if p.is_visible][:128],
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
    with _printers_lock:
        _save_printers(value)


def _save_printers(value: object) -> None:
    settings = get_settings()
    saved = settings.get("printers") if isinstance(settings.get("printers"), dict) else {}
    seen: set = set()
    saved[source()] = parse_printers(value, seen)
    settings["printers"] = saved
    moon = settings.get("moon_slots") if isinstance(settings.get("moon_slots"), dict) else {}
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
    settings["moon_slots"] = moon
    save_settings(settings)
    prune_codes()
    _local_sync()


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
           "slice_picks": list(_slice_picks), "printer_presets": list(_ui_snap.get("presets") or [])}
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


def moon_found(base: str, tools: int, managed: bool, u1: bool = False) -> dict | None:
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
             "u1": u1 or bool(last.get("u1"))}
    if _moon_found.get(printer["id"]) != found:
        _moon_found[printer["id"]] = found
        bump_printers_rev()
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
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"], heads)
    doc["u1"] = heads or bool(entry and (_moon_found.get(entry["id"]) or {}).get("u1"))
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
_slice_count = {"n": 0}


def slice_map(value: object = None) -> dict:
    """{printer preset name: printer id}: which linked printer a slice for that preset fills, chosen on the
    Printer tab. The saved one when value is None, else value cleaned."""
    value = get_settings().get("slice_map") if value is None else value
    return {k[:128]: v[:48] for k, v in list(value.items())[:SLICE_MAP_MAX]
            if isinstance(k, str) and isinstance(v, str) and k and v} if isinstance(value, dict) else {}


def save_slice_map(value: object) -> None:
    with _printers_lock:
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
UI_PAGE_SHA256 = "e3336d47a29d7a139b67fe1163673d0715ed659fdc1cdc5f16233c7646855939"
UI_PAGE_BYTES = 1336773
UI_PAGE_Z64 = (
    "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"
    "a5RnuY/CkLoPDmkUTdH1DlEfnNQAOCjPitCXkNmAcPXbzjpIPNA4idWh7BJJwVLNdJAD82BYBPPwYTBLV/c8wEdHOPwXRjgsjvBJ"
    "rrK5SqmbuXki6zrXFvy+RdkTM5tM6TC/qvNDMx+PBchWfsWoQBlW/1NiJYquWwa1S3vG/MpoZgiDU78rLtJbHXp985PctWswRBp0"
    "M/PR+5Sj10YPOwxQ7OTf0BqdvfL7KGtZrV4JVbHlN8Lgv9KrhHDBNxGZHtEj7LcOHFTJ91DJUeIlG5KtPVhOlJawPgsMXeFoaa0e"
    "nIOhVnkymR9DcVCdRvt0v01X483SMYIRbqnYgVPtNLa3432nVqvbgVOvbsdANDGuIl7SlfEzlKvVZDm4IsDtv0nlalAOOYsMc6ho"
    "o8JFG40i9JWq9KeTl+U9JBxOmxqqQ0OktYurHpa8gwdAVqyfv8B7mYJnagDDqnZq2ynwCwiTb40nQK3wVn07JbXv/WixCA6q1WoD"
    "/sNPp9msoZlysO+gLL3+rfYOeFp9VC1ntWS5JtQONHhQrYhmq16rLKqVWn07sDGgK5UI+EoQm1zvirWc06h0Wna89rCUNhvsWl0i"
    "si+A68cqme3T0vqJAhEpJ+XrObsluanTQb+iTR0Ha7HIm3lGj7KViRNhZOXvfMGmN2fjyRmui/fAlWO76CtLssD4W71+wo4DHhtT"
    "8C/+RO9o+BNNcG0ReFQc/qAXn9sZ/oA/Ljv1k7ObKuba5KV1HofAyzI2mVgAAF6i8oYPNzRo0V6bAf3aRlPB2GxoSvcDwxImGw9n"
    "GH1WoNib0YBzMKiLHjMSSWVIsL09VXcOyc08sjR4Q58Q0z53ACU8Gy7piNikFYFB1IEg2hxO3UfsfBRdsJlJjvdHBNr9PKiUO155"
    "8qz8cvh0a1d5llhvUHHp3+ZsNnhjP6JlKh375C6FqB818+LEf41uv5R3iaehQF2pmi2ALzSUpdyx57ebfqt13pk0O+f++WSvPW6c"
    "n9c6I6/V6DQm9fbYH40mo1HtvFqvnXf2fL/a7PhQqdKst+vn7jfgwi4A4VRHAM2cu8Cfjg3l8px4+MErIIKyWIdpxXNUjCsBy1ai"
    "e7P6SlHL8ONI6tZvVtCZDCBRFf8qlAikhWS+YWmlb2i7tRqLRbhG+U2agAdaobleE60G60YdjpDC5Mp5qFAVcra3WNyOMJ57rkRk"
    "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"
    "VJNqSGf0OkYtW9M1x697mcggFVBRyVX6vr4GW/uUKvAwPvIVvNInSwobsD/LNbR0j2eq0/GGBlOpGPuwpre/gFipuYAoosQyF0qP"
    "a8W16WmqhsbzzaYihWr4jIODs8OjG8+ODl/98uDo/nCUrpqRdevJ46MbDx4fDtF+N3HDeTyyHj85epWmw0H6lvx05/FtUQuZ+7yO"
    "Oz89v/EQcpI/V+6UlxdpUPoOT37weDgK5yPr4Z3Dw1dH92/A6zRRXl89ecaKvTp6gp+Abbn37M6NozvPeO7jRE/RCxxjgZt3jn65"
    "cwfyjklyQjB0yG3I/urBIdL8hDyIZcIrgFIkPo4Snn7zzt0nz+6w9JsEliLhH27chVZZ+o0gIcvR2noL43rj8e3hyMX7wCfwNYLk"
    "dGIOqd/zL/8zdsdk+t2ETBdkGdf2efzTLwU9OQyEbidzH6o7V9c+NUJoGV0N4yqnKaPr6eErG2CVrIeGjyRTp94ccjfSjBtWKcvD"
    "jMc5DFLweF3AICO1ri3aZyV4dcDE2syrp9Yuc4BOXmR69hL9hoz+8x/xPnrJ9X3PcsIY6qt3fnBCrdWBMapTH7PkAE451OEn9Wki"
    "R6AudTPOUOw/HypfxBb3vZSEXD/zgatEbaIhf3I4n05eLL/99iX6WdBGl/klwH0bqNY656XgwRxKh3iUTTBMai2JaqyHpAbs6z59"
    "BioqlUMb/3gwr1GCg1nHpCZyWDS/iwNQY3rAcW22ipPaxH1Dam4tN5579dqMJJPIR4cHVIEamDl0GZFaC8OAKIOB6og8AsJaHyYs"
    "TXgomNQ3EdW9hiGySHZMYmwHGH0cFKUajMIRAR/QYBWIy3vxjnEawjkAcIpTHnOPD+5ajXd8EqhBVdJjuXoaF/eXLOs14VhWeowW"
    "neR7fp+6Z1FCoIyeCDVrbVFQhU0thVFpi5YBzkSwOIckGWlxG+ssRt+N5TH17Y+80Hf/tXd9+Dx8/6A+T+Cp/97pvm816/B4a+rO"
    "FqgwRmsQPMq8fp33R4g1lBDmfEz2EjGiyfeK15y9JPWhI53rzumZX7Co1+b/TqinUnRcdIBKtdLDAMWcO0DwmL7cMCt4RI90FLl4"
    "QJbUg5lLRz46QFIAB4drOPvYfNSIAYe+2IsPogYatlEcusZqQe5fSly8A9EfIC4ejX0og+OGzKSMa/HFLwDdPbzWB/7IZecJr674"
    "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"
    "AlpBOMYzlitUagqlRYIzraZibp5lS9dVTtk7k7NINlbNx0fXto2qmIpCpN7MtulGjeoLq1zv89r61SynKBMKbnu61yNZTqJl+A6y"
    "Y2xPQUocrmKu9FfY6OSHOYUdepiEnlqRKJdb98aq5NkK6vrdiP1S7FNLf/GIoOpombNhdKdMYxV84Qity4p8U64BdifRusQbH4z2"
    "T5+O1lwc+TBSjEtCMAqzrq2vYeyTKJrSnfajmubgjkbbfbB71MVyv1R/JdcMVtF9i+zlk129LlzARccFXilss6d8BHHhGq2gPo3p"
    "WgWRoDAcyz9saSFAjgl06qKVns5xaqw4RllJddltQW6rFzf1hUJUroNyac+LG08MqFRxMfocxj2L+vmdXS7rmW3Q3iTD11DGxLSq"
    "EebFWtM6tprD/FW4z8u4GhTDKyUe5X4nKlIB1fArCJE/Mbn0c/K9KJoe5kk3c27AmplagN6pxRIQk8Qx5S5St4BCh27sxqGXLYN1"
    "PXZnWYeJF36exnZolk2OGXe1ep/LlWFyHTaN3ES3cNA324K8ZVYnBUUyBj7cs8iGQsL/iChlWlYwkTEgYsTSy7y78Swl7t1yUlMG"
    "tcpOS3qt5m3b9qhaOBiq6yNqTaIFqqmmKnfox1U31sbbV8nC8zR+i1rUi7Wl1V+UC4CZb3Ax9DZep0NQyZOQdiZ2RL/W1nKmH+kL"
    "98pzcivb0N25+0ao+lU7X+e4juIzdtb9AN4NZfY4xTOBdkAWZrdSR35J3mTnCYXK0AHq3N705bKq+MGQP8jb/cL2PVnNxnM3nALh"
    "qcx364qrKT2XlT1OJ1g1JK+IStl5uKQcWKU72K19N3dN/vq3vUdl16H56cj5q1FcHOdWouIyuVO4sHRuIuc/2Gxzks0rcKXY31MF"
    "p7ifj8LtR3cpjEMNcD3Q52bDhGcLVafY7eoUu2tUSDDnHVAX8dMoJjptMRPvD76xdEr3lc9I+1sZUtMWgQ61Duiso65QZntQDXPM"
    "nnX6vcyJpKy8wXmM9DhTXC7Dx6hKIlKAbuZfWzHn2ZSdSvgJMk1hFgfaKXNx0wRev5z5EN7fnixcL0xOUcNV+IOLWNJWjFXGs4dk"
    "Aq3UtlqfPmNAEk3FRg3n0Lb/WRcM08ccJYHbtmzzAoZE7o3iYyfjKU+52h0XA5051De0QeGsdgtZbYMKnErezWpv5jAMh547ZUfN"
    "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"
    "e2ropXfr0DaTwtStbWcENXL/6ZApvlvPtpoI1LXdZwE1cI8pkC+3gf83pTriStfkOlpLWy63NVHXpklK8b0n/1Pt9+Z/vfRuHdqG"
    "/03d2pb/qZH783+m+G4924r/qWu78z81cA/+z5fbwP94wnMziRHqPrTlclsTlcDXUxNB7sn/VPu9+V8vvVuHtuF/U7e25X9q5P78"
    "nym+W8+24n/q2u78Tw3cg//z5Tbw/+a8c1zt2sRza+krS25N2g1Z63S87zkTRAv3ngvZ8rt2bJv5YO7etjNCNHT/OZGrYNcebjUv"
    "RBd3nxmikXvMjWLJDbNjm+SIXPWG7IhrqZ2W3ZrQG5MrZvG/5zxRrdx7puRr2L2D28yWsm5uO19UY/efMYUqdu/pVrNGdXX3eaMa"
    "usfMMZXdMHcEIuMS8htPgOiHYDLty8o2njXaouh6Akvwe06ZQmubp87fsrvbTp1Cc1tMob9FhzdsPWxE9D4bCYbC90b2Y/lzl82G"
    "/0l02Jlxd9qJ+DtSouju34zqzu77QtF7ovnRbLu1i/9/Rv93Z9ft/f9/MwrkXe0bcdzRe54tdx/sPpY5t/Sw/637vDNDbut+/9v0"
    "Ou/y3ojdjl7sbLn7YPexfLilp/tv3eed+XBbN/jfptd51/NG7Hb0JmfL3Qe7j+XDLT3Of+s+78yH27qj/za9LrqAN+K3s083X/J+"
    "OH4sP27t9/0f0Ped+XJ7p/DfqvcmF+xGLO/hUS2WvS+mH8ulO3hd/8fQYGdu3cUl+7ejwmzih7uZmFTiXk4vKngvBD/aw0lNf6R/"
    "82/Q791dndT2xzo6/8yeY7Le+/vdjSBFjLCRLZ2uCHpPdsu0sj2zfZ4+bMs6mWZ2YJw/pxfbn7r/xMyyrZOzBMmP4aD7uLv/wq7t"
    "xFj38mB/hs6tPYf+qVlrK6ekEcGPYqud3dF/Uad2Y6jdfcx/drfWnNP+xJy0hU+xiNrH8NCOXuPP3pedWGdXb/Cf2ps1h5s/MdNs"
    "4QAsovYxTLOji/ez92UnptnVdfun9mbNieBPzDRbeOuKqH0M0+zoj/3sfdmJaXb1s/6pvVl7jPYTs81WjjQTeh/DOju7Tv+SHu3E"
    "QLs7RP/kPm04bfqJ2WhL75YZxY9hpXv4N/+yfu3EUPfxWf7pPSv4Iv9EX9CWnqlP44fUmvyT3EKfpju7+Yh2dS1+6g5NsnkL/hxu"
    "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"
    "JVaCZeqStXiZ1aCdumhz3E4ZW5Uuo6tVRGb3sqmGuORqqXKxODioMbSW+KD6mbxvedzUU6k0pCt0R9Oc3Gv+1fWsutTJzauJeHu3"
    "rJ1NSwRW59ady5Cty9Q1QkuS4wHawSuoJ5kbN7a2HPXQsdY0RDhWphTt4WV1s3aEWR1TT5Xw2df1yD9B1/rG1jKBX22VyjZi0Lwe"
    "6FXNkj1Q2VYcbZ8v10My2xBcV4ByTh3Sgv3VndMo0qR5BWpjleuXHR0VcTmnby4wB5D0mxioJYEoSi+7UPBbnA4d5t/NblpJHBdt"
    "oHTL9NCOfYv6Eyj423qtYeSiXgVaLtOrL5VDZmRkGZyxv8zhIRtoOUUal1zVWbgr/ck4GsYnpJwzhtjYqlF0GSySIt1NupC4epOu"
    "OsVplRdoOtmL0+bDfe4xDJVucRIbtS7mDXx8vMzAx8e3GDhUusXAjVpzB048X2MA379s1yOItobQlA7GKa4jcdtGCE3N6NWiaPI2"
    "xNiZQsXg3angg/gk0Qe+0X5C3w/Txd6dykJYNfAdqa4xRkfSooZ4YVN2pcYCk226QrkiCatzaqVHgiDPgNjlfYqHODdgmGKg58YM"
    "08+jzy6Wcml4dvFf5NKQ5qx9ul1e1JzSHV78cU7pDi80tl9cNDmlO7uY75SOarFTOpraH+qUDnr8Tzul21UiZIP4eHBRu+BSqtgs"
    "pQr1qwKto3WUi3jWhcS29pLuthqE3s+sCTGcbHkUy44eLAvOQuhKmDap6yEZ04i+ZtLfutbTznWlCqh8JU9UGZ6BCRBL56JL/O1Z"
    "o6hTopnw1U/+iuQvl1QiO2hkdSbu4IRzC/WSXxgBytecXoOjv/ML29Gf4bYP3yCziuWzw4qQkAX8BodpQgutVHvCrxyZ4BpOCuRP"
    "Yd9ivH+UwKnYH2kXKJ5EkDnOwEQRdpJHP5tdgUVdvgdVjmR2LtzZ7oX00nF+Qdvz00XQrOYQRoyNig7OM05aFQGeD/AORtzdbogq"
    "n8cY4uIsbjzDuVURurmpcbtVikjcYRPbFQ6XqjNF5GQZ7bleANvyV9B4AH0q1GPWi+DAC1hhHnKXh7wkK2zXqYlkgmlpKS5kwNtp"
    "RERTN9eJLF+xWSuyfP0Wvci8BhbjUpO0I9dZr/7cFtKsdFQz7nISob1ybTLhYhThmvPkjblj5RCENxss17nVaEXVJYYrnosv3P9t"
    "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"
    "OCK3RRqGEV2YwqAjYo9IhLuRxgn+glTyGKauyCY7xGAXZEPtgLeIQZ6QTR0hgzIXSaGOZOi7iyTdhI+SdqbnT5KIPpAQiK0hgjmF"
    "W5wfpfcixW2YOALr+IM5o+0UewXnOc9TeH0qlj/Bmbi28Yh25KlNJ2mAbsId6uEr/UmasHOfsbN0IWeekFf6M8/4i7ReePpiTL4n"
    "GBmaV3h6EozhS8FYJT8Siw59bwnF5s8LxVT+9PiXd+2/h+RDotndC25x+u7LMar7Z7hZEmiHj++swKx/vUYfLYruXfUw+/hOb3tq"
    "pk+JXpHlrnX4cHwqOcq/JejK+lClWvLxXff/p4Sdpvvdg42R8fGdkb//j2uLHp5S/uPuiV7v+PuS9Bh5S5W0U273/PwLunP0LeXu"
    "aJh9SDXDLbJvmnBMfDgl3uayu448p22jLhRf//INfy+c+bfx+U+3+ENrJKW37Q61tCX54EaBG5kfzG7gtCKPf1xQS/pmMcdKflRQ"
    "+8u8/zY6ahf/r0S365PXoi03fTU+Sc3ypnmtOGcd0JLYfc7h67CdW/6vHL0ia6F4Wg59fNfNC09JcWmmVmuIfXx3sohvsB5nbmcD"
    "fnyXmoGWu6X5M9IVaeXD7riWfUPQTtj/2M5WzxvyqgDelPaNLIbtKJ8mxLczHdNvM50nzrdznAhus1gtVz9UP8rXUT1Ur2fuXi7+"
    "UdaO5jZju2yPzvy/xj3n/IsCnzI8GEWqdT/+4+7+Wd4jC//5bHGRHxH5J7Pv4vpD5mitMfYzeX9Sg97C7C1lelXW4K8vtMM16i1t"
    "8PH40vmH0s3cdgX7hm74IVGnKX5IdNQbP6TqtMhzohud8sTh76Kse8S3Wwk/nGhvWXUe4p/Lfhaqn6uqW0T/JO03En4BXmxZrb3y"
    "c4070X5v/jmObxTn7x+eHp++u0Q8JzvrzC7d6RTlm8P3TXFvkR/H8aepjyj7aeoj3F6nvgXLz6juY6Z/xlL6Ju+zwXxrGN5m+D/b"
    "4Eu+P9nma/YfNvtsjt/O6K9ajieyh2MvU7NzX32L7+/MLK/l/2enmDfLuJ1r3hqa7H/Tovzn7UIv716PT4q8iz7+6HZfnll29esT"
    "vleEyUMenzp6zPnQ0j6f/F+r8SS7hpu+T/Pg7i1p/U76UT6/k36UyEv6TU+OM58Vp2FrW8W5lpvvIRI0TPva1sdfLx64d3u5W6b9"
    "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"
    "9OWbwRpH7UC0w95au+2UkL/L43eGeWpqkZrd9wc+HNnT3aa+Xtv4yzh6d7xR3pHv2oQzxf2RXusMq3cnnGSn8Xe0dsS1d7+/YPjn"
    "93fvTjZVB4RrS4UnnJvH/1848YSQC/wGJ9IT5D99+dpi+oSdM3jvHrJ2HWS+J+8/QFc5izqoneT95eCcBOQ25qGbYVsN3uWZaUkr"
    "asefkpk//nY0IR+sNG4XEncfj/H0Rf+2hMD/9/63jyv3j/FdlLe/yD8g/A8Evmt/MoEWJqZxdyrhb0A7H2edMvzt3J/rUvvKk3PC"
    "l05OTh8my//LPM8Kd533/9M19OtlDok+gffpp2MVrWL5NfrP/NeonT/S36PPrRKIPl/4kT5VM342w5rneaX738dXlIn5zYD+8Yf5"
    "e6sALuHHozUb/fVYzFmxdBbjfXyfdduU+qdWcQaf/trOdemhG2ntU8v/i+Zp54bj90U61QAegXCdNVrBic4Y+LUtBPpqBpn5ruv4"
    "r399r39qZ3DtVEg3wRitOdvxKDuZyOlpvX93f5lVu42Uu64Y8O7Xr3q3OXM87tW1zf3UavDOJRMcvpyb+Ff9739v7ddj3aeOtUXH"
    "ny5RrYl1bmXctTK+OzfzWkxbRHB3kkP362Waym6G+ijPHdkJXm52GkHz7qrhjxcGxVtn2ctFUMy96RcrTjbz+RLcJdiZgY9nP8Dn"
    "t/eyTqd+ng6j3Bv/OK6grodMnra3vr2Ld96hOia0fD2tvV4h6OK79GfnhL6h65r6X2ALwlb13hT8X58uEaflV2eGv3++Ed6qgs5Z"
    "8O2nAE/ZUrNlyPG7md09x53Zospcnb4c+A3xUVfGhyv1dYX4VPkrN9Je7Mt3eu6/PnVd+c/8BZduOPL/mhctd3Rfmvc3Y3Emv38a"
    "i1Oem33L/OuvtwvU5yi4LeTu/hW6EzxuSr77ZofxsbWsuuXjteNyPHgdAm52PdfTqrEXQwXedT671OxcoOzJvdMx9rZY4eVNyzeH"
    "ux3pH5R2dNd9ryzzpC1OJT1z0P6glfOX9zLfbGUP+nGfee11Tl625b5l5DeYf7WOOGpXq285My6ieP9m2W0JtyLw9nc1j+s7LjC7"
    "ufHm25qpGcZlKzn33xB9On/U+Ukav3WWdJmu7pKXd4///ve/nnm0Oq8uz+LXzuWPj/fps/Xjs6OA4+5zDXet7v/y9df0ofuw9ftX"
    "twMSLc3McTu3m3cfrr/zdvHx6pLG7VYE5vNKTs6Xy3yttfN1fGlWy4K0W1K9CLp3d79q/xlf1oPaZT2YfWqtwvh37fM9fNdOq9nv"
    "4Od2Ym3jst+hz/fQXRcuzhb+vXH+8avxKWjnqF8uN72vRuwta9y73/UP0Ocb6/xklr9/hehsbYH3H+C7ux7Ue0zqx4+v0LVN+aZf"
    "x4TfHrXIePf+6btVf/tifL17/NgOWNT71JrVT4397fHZJ5Re/vvv0DRc7V27LjTN6N3fvhRfbz4u8da/2y9T/O3s0LtYvSe/Vpx+"
    "vf9hMd/5IMhb/77+5c+ltqz5y8Pzq/jBpafXJpy+Ivb1L6/w5MTup6+GdNkvn+F4q9w3uvfa50POg/VKvqcvm339y+vde/x6Ee2/"
    "uVkcHD9+dVZMzxTFC5KHzLweqj7Ny8fj1ieVlZlHk/Bs+X79tjAj1o/2+9kMOEe/fzwSPb6ipx46kfl0/Ao+oHd+rcsHh2+J7rvb"
    "H3o7Rb6/NPeyDXfVhV3KeU/uRVyWnCP+F3tv2t3GcTQKf39/BanjRxc4GiIY7AANMxZJRUpkS5FkJTEPX2MEDElEIIAAQ8kyif9+"
    "a+l9ehaQlJTH1yeOiJnppbq6urq6upYDXrWDpEatVYPKSgY3jmdw3lOwY+T5KmqbQBY8vJjOPBD5RjKdz+PV0zc/PB+ayII93Wat"
    "Hgsh1FyYHLSKRyGhKdgE5zHZynzOq8uT+NS2JhKmkskTdkXzwHx0XIH/rjeCMpTc8wtd/Lx8U9U26MSr09sPbA9Zm4+hyNtB9dLQ"
    "6EohKcDY0rQ+YKrV7+Hn8IyAvqqkksJ/arAEUWrbGVVrl9Gy4tNn1IAtX4KAYFwNqE8SUNt+fptGg3jjRGtQhcji/Wy2APSZUumf"
    "TNlzY8i1GS2M4+mskjJrd1oxBNEsszcyp4PjJxaWWC4o6wpeQJDRbHyFSJJz9BiDb0W48fmFGl0dDr+2D4DpsBOQYoK/R7/CtusM"
    "nUTg5E+wF4O4o5oBWRY2U5IIp8NUm3uV1d78kaksMdqf702rwck8WJ1qz6E8I2SWG7NHD9DjfQ1Al6CYMh3O96ffDlf7U32hNTVg"
    "iZXfyuuETi+pE6pta1nmiAT8AhVfn/ImlWaCqcD0mymqIR08WMZHpxY7ZopNsWqGBaS5fh7OPV3KU2iwPg4sNjKYHQcmlxhcHAcm"
    "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"
    "Wa+fzqzLH6sZWbu/pg6kv55Jb8pfG2pf/c3MqtLIVmZNfgeqmkEfZrUeKstshiuRSW2Fy8holVEQ7AsIOVA7YEXQw6oywHatASZL"
    "QDEyqTkC4znyydw/0lvp9bV6et2aS82RAc2lldJUQ//YIwce5AZM0VprtGoqvbW6tbrNqjZr/SCznF7ts9+Ptb5Nfm/x3yA3zdQH"
    "j0596dGeOLafWF4lfeP/p5PTZSQS5Cx9ejWOG/4v8Akq9moQ6OUD40vhf1up6f8Oe4GMr26/sqeu0xln2N743vfrGXLnSwAfkoEK"
    "KyOv2Vz9DhPYXLcaqe2D49Zubhf+K5w97eaK+Jj24ffJ5u5uJVfZjf/v4On4cbMwqj8d7q5UCre5S+/Yy3V3Vy7T5dxVobXbzv8a"
    "XuT2i3nvoH1SPMgf/N4b3+7ur+4653tOblRqk55z+d1C+6J1WMwNL0fjq353/ebksVXvrgzSNfv37vjp2G6f1/398f7u9vXN5OVn"
    "c2Xl5PLg5PhmUjz8le+dlhfbo4PKUeVn5eCyvzj+tuk99zcap0elq5OjraDR+HW++PRt+3HtMb17vDs6aO0NXx7dwfHgfHPz995q"
    "c7GycTU429168a4Pg6cn271xK4f+5DwfnA4XK8PGibPW3z67vfLau96V81xYTKcnq4eV3/55O79evC0ddU4Oa6fji5uzo+JGd7L6"
    "zf25livt7+099fd6lYNfudHvrneedsqV8WXvydsu1E6fNq6Gtcamf764cVs5rk+e2x37+GT9tHZYXzxcXFn77U9Wb9cKJ/nO/vj5"
    "91Orkk+ftiu3V43CtZcatEve+tZw1D9eW/Qu1tzz4mR/1N0kdPKyVzi/LO+OLl/2O4e7L09Hx5vetT848WurBxsrhSv7ZVAaNlZa"
    "qy9+c/0wyHdylc7ufnmv8G1ir/lr7frtWrB5NnHXrhqNp8fJ+fbGYnexcuznTsedduG6u/JtfeB+a5713JvVwsnG1W16P7eWPnm8"
    "udls1u21zeHK7YnzbbLV2Pp1clH+dT7OX//KHZT2D/K184309nD1+OfxsHt6ujf6NfzV2O3Yu2U7Xa63F72jYudb+6y4Wy8eXDye"
    "Hu0+nl/u7t+cfLs+ej54DK5HZ7vna63x7mplsn6+3/zmbl8+5jabFzdXh+OV9ZtRK33wdHnYPTzNF8fFfbvxKzUuHJ8cnxRGqxsr"
    "G6lv7kXQqAxrL71K7ddT7Wlx62xQejraHZV2j07K+d3Jz1Mv56eKhe2XtceG81L/1R+Na5fX+Z9rg8bKRvtxXMk/r5wcEWCd1FtH"
    "a7+2ndzG2snz75W1oJJaOd86P/m16zyftztHh7nu5nn7Z7lyvPnSqbVrPydHw7Wtm+bL2d6ud1HM3eQOS5VDe29/t7NbGo8Ge4PT"
    "3cZoMKqdnl0+/xoXrkpPm8Wzp82r243ORbFxvhFUHgfpo871mev540HjqF2/ym8+p58ur9bJPthOBcHj2u3o0u0Vro5z+dubjcsb"
    "u1TfPlv76a6M67398+Hz6Nk9L20dX45zN1eN9FXn6qa9nyMddVv+bXG1Vz8qLTZX6t1vG08Xzuhya/Scfvm5Np50z/srPlm/7dPF"
    "xcXtletO97mdH/wku+346Nfe+VH/onC9MnrxvgXfUuOT/OXic7P5stcsHWwfrH+rXBXam8NJ3k6nDo7LrfZeobZ+7v++PVlbbH87"
    "aK7cHmxs+J3xcLXWzRed49/jvZWzwsqwVNxrNY9b++DaP3ocnbWaOTf3NMltF9Lftux6MHx00sHKYX0/541/rl9Pgsfj3G55b1wo"
    "bq5vXd/Wcs/BYedlpZHb7LuFxcfV0enzxvrg+HB07uV2CxtBz11b3aodH7bOa7vnjfL+zXAyuNo4Pdi/3lwrNq6d3V/lQuXsujHe"
    "bNWP3Itie604eiacU2qwXbtqXvwerqeuiufXv7uN/fTE+5bb+uXY38rFn4fD0+tm0NhsHA5ug8FK6nEwHjzfvjxubTQa4/SvfP7y"
    "eJhzFzsre8NcZzf9eNEZr28t3hzejPK3xePDp3Pv/Gh/vJHv5X+X1/vl0lPe+XnuH/WOuzelp0pwNmwdFZz2uX9Z8+vnhCcKgvOD"
    "q5rXSNl2yhlvbpzXcsP8rzzBqIP1YPf3bqd22HsZFr91UnslQvT2W/vHrVaxkh/6zfTpMLWWv/KOzs92C6eVg/39p1/r+5WN55ty"
    "7mTv8ODodtzK/fx59HSTb51tFE52i5fkv83i2Hs87/bXLv3cc94+KZ4TBLluD0rfCjf7458XzuVVeXO9v/6S2r3dbh2u53aLxaOD"
    "499+odlYKTR3j8vBdv7lbLz71O7s7eWdyu/dldvrYW5yuJ87v+ocNV8u7cvzxVy5XCnv7XeuHf/yOGiPbzZ+PU8Gq43f9kHtaiN9"
    "vTroPg1Gg6az2CMHzq96sFHsnBxtl1adbv7k/Kxb2X/Z/pbPp7zjvdv29bB3dn1SHp2W+hvd6/RL6rpb6qTTt3XvZO3mojE+vh4f"
    "bm0Ffa8yLpycla/d497glgAsX1sb96+cnye75+3dm9b+bqvl/Rqfli+ezndfRvndyvllcLy4Zxdze8Vifr8VbDwdXTvtoEXPRPsl"
    "t+eWirdjrzA+L3/bOGrlC+S/Y+fyuXD01Hg5rywOL+uFJ7+yt3bUOxte9wrN4tlWP/9E6Mbw+KZw0v45maw88r4aB96Zu1snIP1J"
    "QOr0J2v58m5zt9XxncEt9khIy7fi8cXT6uDiKAhutyv1kzXnqV/q1p6cUSfYGgUr252DXrNT+VYc7RVz3vrZ3mNnd+33y/pZ43dp"
    "4BwcbXzL77+slvqXpe38ydnj47fLYH2tt3WW/uZspSvlgrt6Un4sFOytp2Zp9HLkOb9zJ/XtrUr5bNzfr2yV17/1O62bl5XKXvtb"
    "7rRytjW6We201i5+nW85Jfdqff9ncXJ0Vttavd4vP64/uc99r3H1e9LON/rXT+127cVrnSxudFZ+lla3SrXFvOuUzm/tq5Pro87N"
    "1vnBRmXleePqdNCaXD9t7FVuS97BRqEzXMtX2oPJ6ok/Pnb2V5/aL6Vi5Vtv8bCx4m3n7V9Xg9tG42T8a/FXfVTc9p/O7dxNoXGd"
    "y590x4srg6OjvW9eodC3G/nWy2o/1SgGQan4zW0OG7eltfTv2/zN1dNJ0P22ebDvX129DDePy7bnjLvbw730ip8rXPZ6qdvTUt5r"
    "DL7dnJY31rf8UZAfLt78ulzzSxenlZfjzrDnXNaOtvc6Z6XnfvBtq/WtvVk6aBYXt44KT5301WA7v7L6e7i4urbRv6lN3LZ/cv37"
    "pXSQuxqvprzVvYa/+utxstY7P/tV6Trbo9r2Wfpg6J9snD2tNHNbi+XaOLW+d7JyPrnIrbf7a6XxYel8/TF/cHbYG2+nfz/mHr/V"
    "NkqpvOfd9i6+XXkbucX9n+XxS3642Svd2mup9KRZ2iqOms/d1NlGZ+A/XW9u7m1s+r+D01pzb3s4XNnePSpMUqfpVrN1XNn30i8X"
    "B/n9jn/T/X85OmstVwEoin4QBW4lGtwhQIe7B/36x7xyihns3nP2TlhrljuYKluya9fX9J8V9WK8ow8CgFbea1XeknpJRDJgFWnt"
    "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"
    "578L4GfYJjonDdsCavz5j/8H8rgOeA=="
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
