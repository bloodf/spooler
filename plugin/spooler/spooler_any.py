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
        save_settings({**get_settings(), "presets": parse_presets(value)})


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
        "display": display_settings(), "drying": drying_settings(), "presets": presets_settings(),
        "parents": parent_bases(_ui_snap.get("parents") or []), "cur_code": _cur["code"] or "EUR",
        "wizard": bool(wizard), "log_path": str(LOG_FILE), "auto_keep_slots": auto_keep_on(),
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
            save_presets(data.get("presets"))
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
                "presets": presets_settings(), "parents": parent_bases(_ui_snap.get("parents") or []),
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
                save_presets(data.get("presets"))
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
UI_PAGE_SHA256 = "a337c5cbc132fd9668b5e86027ca500c0332625431a39b51d1b21dbda48bf019"
UI_PAGE_BYTES = 1342980
UI_PAGE_Z64 = (
    "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"
    "/SCcwC6LWZZAy0ORS82jvezHqMdS+bYSL2RObEnmlC+ZnAwsHOd9XIA6WBzmkCyIX5iFJr2PC/Pgx5G7KPh+4hZWQI/HNAc7uRXn"
    "ydYSj7UxE5WQyUT5noyU4Tuk6MOOKXQw8dfYMPaijDIBmPJtvPg2HlfOaQFat9yy+xU0brtFv6z/NrR+30Fokn94NxKUjJguORtv"
    "ywrJsdmOGeKemGyus2VnPZkyt/FULmo4RdcUEammqySPm2vRp7swn2X6lXVbJLIZVFaMN5afYrg09TwdoLwbyHQVOay7NsyfQ0K2"
    "76gxgsx3BheZbmhvNZ0dJTp6mqvlEm6TFxg583MgSk7cgUvEgWwYgSszw/EinG8bZkb4MMW9jK/ncsvq0qlKMqGb7HEd3R63Jzw2"
    "FRxfOTdVAlXZsbwsabsgDfoEpJmt1QdcuLDLYhWCiT/ThoXKSC+icBbnqmuLkXtJcBwSBVxZ/4J+eJzR0KUrM9+QKVrEjzeJDvMi"
    "PZgEjIoyyCRysbeP0+JFSm+PopOTCbmziuPIpFBfhrI+yi2UH52lrHdXrY08TYC0bFgTELTsf17d+yd27OifhzP0mPBQ5RO4DOpQ"
    "+OD/E+i48Q8vpHf9TyM13lIqvEnIvFlqXFoOnBCJFb0MKSV5SM6kT7bTEVSLXusEXr5O4NYypMtTIqRX1yfhDFs/iualubGcrVSp"
    "7U4EO8H04hV6S+hCRoayj7GIIIGvE/qqnMn39+fvadq+Qhoq6ZhEuueSVtXSAhM1qlV5lF9b36VuKu8aokXqfUhPg8ZobHVOL+Zn"
    "St2yl2Z60jCrwa8uB9DCIVNGyABKeU7x8oaMDhf+bDFkRUtqu2nauKC26wIs91920+Rh+i1X9Hptl410d0HZlp1SrljtiogjlZgg"
    "pmKN6caHZY5PuXYPiv5lPaNx2VAD515UBTiV2eSdOz/3l678ZX1RXruvtBdsrm1VTtmfs1tPYS2MtzxwXkA8ZwhAuKWJ7PYrnHX0"
    "F+Iu/tz9PGHxPktRW3ZGKaDuvnv2E9U9hRM+7KBJCD+2EVqnhLy9555lQ0oaYC/SYNlEnd2Y7CgOKTQpoa40Dv8YkXSumrwGVL4A"
    "O1+v2yRyMc3PldwHLi045RRJWiHyThnRy2p8WmX1KM+AmhQ2cUbJzQVaGFFR4Mg1BJXm/HS5w24cTsmL0HtLLlaRfnnGgHuoek6w"
    "PrWemhVHvlsiysfWvjF7RmchPxcrVTIV0BLCMZ6xWKFSUyjNE5xpNeVz8yxbsq4yyt6pnHmysXI+Ptq2bVTFVBQi9Wa2TTdqVF9a"
    "5Xqf19avZjlFkVBw29O9HslyHC3CD5AdY3sKUuJwFXOlv8JGJzvMCezQwzj01IpEucy6N1Ylz1ZQ1w9G7Jdin0ryi0cEVUfLnA2j"
    "O6UaK+ELR2hdluSbMg2wO4nGFd74YLS/+uNozeWRDyPFuCIEIzcrmngMzuMomtCd9rOa5uCORtt9vHvUxWK/VH8m1wxW3n2L7OXz"
    "Xb0uXMJFxyVeKWyzp3wGcSF6Mp3+MaZrJUSCwnAs+7ClhQA5IdCpy1Z6usCpseQYpSXVRbcFma1e3NTnClG5DsqVPS9uPDGgUsXl"
    "6HMY9yxcHbPp1bKe2QbtTTJ8DWVMTKsaYV6sNa1jqxnMX4n7vJSrQTG8UuJR7HeiJBVQDb+CEPkTk0s/J9uLvOlhnnRT5wasmakF"
    "6J2aLwAxyXJJuYvELaDQoRu5y9BLl8G6nrnTtMPESz9PYzs0yybHjLtavS/kyjC5DptEbqxbOOibbU7eIquTnCIpAx/uWWRDIeF/"
    "RJQyLSuYyCUgYsTSi7y78SwF7t0yUlMGtcpOS3qt5m3a9rBcOBiq6yNqjaM5qqkmKnfox1U31sbbV8nC8zR+i5rXi7Wl1Z+XC4CZ"
    "bXAx9H65ToaglCch7UzsiH6hNwz9SJ+7V16QW9mG7s7cd0LVr9z5OsN15J+x0+4H8G4otccpngm0A7Iwu5U68gvyLj1PKFSGDlDn"
    "9qYvV1XFD4b8cdbuF3iE8Wo6mrnhBAhPab5bV1xN6Lms7FkywaoheUlUSs/DFeXASt3Bbu27uW3y17/tPSq7Ds1OR8ZfjeLiOLMS"
    "FZfJrdyFpXMTGf/BZpuTdF6BK/n+nko4xf1yFG4/u0thHGqA67E+NxsmPF2oPMVulqfYbaNCgjlvj7qIn0RLotMWM/H+5BtLq3Bf"
    "+YK0v5UhNW0RwNQAC4HDibpCqe1BNcwxe9bpdlInkqLyBucx0uNMfrkUH6MqiUgBupl/bSw5z6bsVMJPkGkK0zjQTJiLOybwusXM"
    "h/D+9nzuemF8hhquwh9cxJK2YqxSnj0kE2glttX69BkDkmgqNmo4h6b9z6pgmD7nKAnctmWblzAkcm8UH1spT3nK1e4oH+jUob6m"
    "DQpntRvIahtU4FTyblZ7M4dhOPTcCTtqtrZju2Wf7xpuv+ry+suKpsIL0GaXqctPf8j9Aw6sRcc3q9SJ9OJnSSDM0wu5zQtN/D6q"
    "tadoOFWGN8pt6ZdkruU9kRjB/vmEBNBldMUwtBYqv0ZHUIiVWEdpLmB+Jiuou0vPn6aNV4kGmnuzmuSpV/OFwGJZNmzFKWZ/WDNF"
    "+hCbQD5DoMO1HTegMio4Lfr94JfDK6ytCeCk8KLGUasl6RvrFhvuDXPbKGS+9Hwm6WqWnpYSu9LB3WL7uKx5yOnZhaZiJclDcv1m"
    "pCWVPDJX9jyuK8ZQ2Uc20E2YPVsyWXHOacfEfABt4CbfKuPR+mfVHHaKZ982TCUtVs8NZkU/dzK1tnOjWdEC/NwuQVKCVsN6qDTh"
    "XxctKeDfFl3B2FxqtL4txlKJ3VdqMNXoebuGGs6vd5vxZCXaahy/HUY0rz98SFnEvNLjeX5GJpPodIvxlAW2HVBeMH9EeYZthpQX"
    "4WOqgLbloOZ2io8qWSyixVZoKgPWlRrUJHDcbnFp8+rcZiwxfzsJXrfDKJp7IdZ6Ekx0N9uQyw+fbrbt2KbHejRSQ6+T0H+bOm3Q"
    "Vy3hs7hlMBgpDpua9TuyU497LXOP15b/ufbvLykuQM6hxg+Xc6rJtZX+yWY9E7y7nl7hSGrXwdD+gGBo17HMrlIsM9gbxuG8TEie"
    "3YNGbBsUYW3Np9tpygPpd8v7KV/CciCL0mrfafGmlTqhm/WU/hHQ/0zSSnWjg4Mf3+ZsQzBVu4sBV+GDw/+ZMjl4I7TbqVuDrZ5R"
    "WpB9iFYx+q5RM/KkQq18eghn+Z6rDtQ5rtId2zt7uAj9bGADdgGqbhoSmljoFiVCa5jUUzf2xpvuGQoUUaeAc0BF0lL83K2q7C6w"
    "Qcq7BbnK2B9Mw9kr3a78siL2AZLvJB4d6XfN9a2DiAg7kxfFTJuOGZpW4S6KA1sFjDbTuCtgrV9wM3S3iBc3HT82Gom3TbblgDcn"
    "Em/S4YypyH57PwhQ55vpdTjeaw40L6bXNT95lWLjpiOemwzs8ocQLQ2vF/v1Yr+OvX1NX65jbxfy6OV4fSCoZztw8ldWnQ7W6Sqt"
    "tJ+xTKW+TvJUrdMuLOiF6wYjlQIfBTMYeHeCoI3SnG9D0V8pNJfJ2mcgHEab3DJKbQDL+8+xiY4+bTTez8Eflqe9O0rXtg35nrWI"
    "px9ZsmZbfh0H/guIA7+bH36DE/uLxGnfNVK8wLGH3PdX3pxT32Cbp5plM9r+ZbPpfTTPCMupx2AyjIRSoYxbjwGmYc94m1B+E1Iy"
    "rffD2F1g2IWEoLP0+zgQ6XieT0VkvQ1IBAv48IpZvmvWJEIO93wRQh6u3XzhIHeJQxpzvUW249tdaY7cJXm8k3OX/Kh010H6roP0"
    "feYgfdLHiuZ8+UqQi1KBNPUFLEMOXpiQfOZIfZ8w8t62UQD/oqEZWZBKaSWXVTtOxQe5cISVrVRhrqxC+d3pdfTdTxx99xJ36D/P"
    "pnv14tz+NbeKHSPgXo29BSbv9CqfkXKPLdcHleuDyl81mvgFt+LPfLgpxY8YAqRr9lhfGvd9zX5/Lvb7KKXHuoPHxW32kny/y0Zn"
    "jHlBNKVOpRZGU6RXVC9sibniYWKamL3O0i9t1bCVJ7pL38SFgNG1AK1IM4LECpba7dw65cZEuL0RQyA933zKUJJFWCMAzLgLUnqX"
    "GqKshwWuVuv389yP4SoPp/MJ9cBn9C15bT96KfajOrYVap/SapjqqVlh2m5Vqxr27dAfjHOvY8gWlRTPSraAimSly1xb3F66xe0W"
    "SMjquSgWbu5TKTzMr2bD/BiKFOJifqlrY+VPYay8BULyii6KkWX6VQoniyraNFOmQoV4WVTu2uD7wgbfW6Ah1nJRHCzuSynsM1dR"
    "OBeZ7IUYZy7x17SM3wI9ijtRjBbl+lMKPXKsdpolp8BYrBBdikv+9VwL7IAyxniaJVGmsDtbYUxqJHca/tLYYioHgN7fVh6iOtif"
    "kpgslqXUei1xihZnaCYE1bURaOJTABv1LU0FDP58aTpz8Co0pB6qIpVEwemhAjktdZTx7HQRB/tr6961ncy1ncy1ncy1ncy1ncxl"
    "2Mnkx2rfGOz6TxQI7dpg4S9usJCJ1rXBtKCkkcK1BULGAqGU1x28KiLu4nEpf9FbWyA8z/pIU64B9StDJaoU11fZQfOikM3P0bjY"
    "RhEhPzz8JailXECbpqQuy46qN0YGIV3QfGW8tt7qVouKmyN6so8my0w8sttJERkWYgfNp1nkk0sPimjcK5Iw95en8Jom7EkbW8Rh"
    "VJYdD+TA3XtjaEHk6F+YMlT4VXfF2Sbuz3ZWqEVn0ysagwnQ6YgOnCmWyiWg1lboslWg3eWX6bBc09FQtUIgeQaLA68uvEtR0xI6"
    "G/Um02z4TVIgLvpKmHbUmck0qkwjiqGemvY9ZUVpW17pYKmlg7SnScklBHcr9oB1WQTzwlpdm4lm6uwlJ/6LWxuXFknTWy1wWl8A"
    "T/eSzKNFfKkhNXOb/W01nR9F2Opj5rlr6r7Xnc3BQnp2tcxLPlXM2WLqlR+Edq3s5I+ywZsaqeBNWpD7VJTkzWhiCHpfELrWFA2q"
    "MP/aemH07LYV9Zq7M5TDX6qOr6osuTmot4jEsyVxD8LF0hjkM47md0ri5sRd5sQJxQgud8r6qbwapkpmQ4iLnwT/UjZJGBRXUSpP"
    "md98UsOaB7CY6YVaufu0Lfm0mlBeLRfoaoMEdR7NN3HjmaylZKip3LlCVJEvK29L50jwPSNpFVkSFkGS7JSVdAxb1QmQh/NT4r4t"
    "UldpJWocXAFgSqAL07wy7nQEAPBS7IWXgzaj2UmxymBLVZ4TmgMUh45SWuAXOmACcj7eXibxxMyJXB4KbcKJLVFsI3rIkJsODfjk"
    "LhbRqXCiLFXdDbt+PkrCKL3cwK9daNEnUJVy0sVJrZeJxsf0SQxGj8aAcMgfQc8+6JHynsORsMRyoXmPTiOD3nJL0VvWco8B/0su"
    "D1biQbQyK/21NKU/qVFzR3ZFmi7U06YLptiJeTf/1NlN6oCXjn3I82Sv7UVGXW71uZQJ/rAr/fTi50NYGD9SG0NjTn0Qef4HWUBy"
    "ar4nRv3T+l0rvMj/kqKdlLojz4+KrfmidmrpJWgyVJIUis/Y3U3ETcWZjZm38no3zeo0nejKTAD7T+kj3fYhYK+qODgTMK+09Moc"
    "FzbnK7T0yLipKvSeB2ygPzWnqigYq/EKKe3/8Q+yd7+y7j5DcspkXlkZDXDKHvCCLGhqrsAHJusknCm4LVZFfXvxhQj8UcqxKIsF"
    "G7g+j1XRtJns+tVugRVcqaTYy8ZgzY3XcvUo9U665TBsD6/VHa/VHa/VHa/VHa/VHa/VHa/VHa/VHS9F3fFaw/HTaThuobh4Jfwx"
    "f59nnFSw9e7G9kBjv28V4fDKns+ApkarErZ/Jgfn6ywxlb5nxP1iO/+2Ojdr+lpFHhfdZegTUxVbXEzn3TAHkwhYkdnJnZLnbZ79"
    "UBgm0uiOdTRLROnAnl3Bn2+Y2THAd8LIgwl0+int3dBO3PgoOjRb3nlnHfbk69dmhSocstse2wbjSNjDWQtWPqlV6L81OlsB+Elu"
    "iXe6WM/zBpa5YMYLM7z3LXRGilmEkpdBc0HVy87Rmd405Zs84O2sc13qsryUGsK2U7C1f8Gt1ay3UuXGSX8+m5xJlSk+EadhPGZL"
    "gqv20l1Lfv5j1R8Y6mkrNtlk5aqVPeGC8b/Kqr3j+shIbBiW5IJA5EiitOaNVVKbRsDraSucAjo8+jxKzGwkDlcjSZnuTCLvrbLN"
    "WvquazENl6dcCusoaWnddtruxJ0vw5HibdHw7SiaP5VSXdGO8v2OeXAl7BnaWqC2dE1lrzqV/UPJpRvOdmN+E4Zxl8LhDLjzTSVN"
    "niOS25Dt4mMnHjSKGdW19d3WLi9LOVzJ8cnTRp887iyc0im6U3D/pl+3Nau5VTbZTdwvO13TQDJQw8vUrmF4iHHjzXHtMno14pJK"
    "iPWo+pAkVXb28ohq0ZeBON+uILN/8BOYoaGCSlQyILiLtgo9e1Odudi1Fnflgv/4RWuF/1+zuzDN+MHh/0yZnGZ1MxIa1tL66rqd"
    "/fnCmtpr69cdpCF0AIV+iihQZ2ySGy6Jnxx3G3xG9uuGKanjtFEiIwlNesowA5ZvmTPU6Rr+4XOZJ2xDIrheX7lLZLGYGRWg5k9W"
    "7lX3l33Xv7a+2onkqr6sS9AmA1uSVviQmyTd2xy5VfJJoKR4GZN5xnxM91eEWbJWH1/4NKUjOkEfj5jRSoF6TaEGTfYsU8LaBdt9"
    "tkIN5jJr2zDnu9MAXtkFjUGLh4RjWur45wDha+Qc/wwe2ctvk+0y22S9ysedykqXGvJ3hc8A3XpIQ5MLi1jVNaTbTawtMv70pIOZ"
    "3jwJZ29L87ZfxBqmvdKVsS+8hlmt1yv0s69QOILstBRid8SuwnWbRs5lXVrQQWG+Vt52WfuaRRMDA2SAvQwqGPSktsCvjMr2Ln4A"
    "ilEu0YDULDMz1hAa/7LPhyDl1+eK6uwCbug3xpc3fGuJPECQ5IEysb/sD/edNHdtUPadXe3VBQ1dL64//+JiqLrZAcEGLhqw5RK5"
    "MsEFFliR//GUh0pOK3kuZMzONYoHZCskTOnaXRVcEV8V0ZdgRdD8sNKS/EZGXio4Ez2vybGyYRRTbupt9BG/mVDbG6n0YlcqzVz7"
    "Xi41vrpUj0L44oIU4HMsmyuFn8CnSPTadDfbwS3DoMPR2t3PkFHImjIAeT/JumcSl6AcB/KvrQSSOLkhHkSO3NARBs/gogwLDSFf"
    "G8ID/UWjD2zrdn9zECItUs4OEYZyo9B0VEthAU1hNK7z5dui+cCv24CB+TkQ+ChAKIyDcx7R26cCKHiGbQDhRTgs/E2A4+NbfvQT"
    "JWDH1qFNcsJidBIDcQHEFuENDP71C5DSdKMEW994KyunsjZABWY2coftply5GM1SKnn2LNtYq1ySh6r5IprO06arOGPTqTvzX5Ll"
    "PAJmDx1XMY6d3iVRzfzxtSnZtSnZtSnZtSnZtSnZJZiS4fHxSrkBLBfVeZuTYdpKbKfQ1tdR2a+jsv9RfuYMIcxT3ua+zFDmW0cy"
    "R1uzwTl5R9XTpuHskbijY0OSxG/qs0x3Mw62qICY8pEiAlRuVrsi76ffMSVoJdZU2teoro6nCtvrmXuJi1DWfNU8ISmQSupFSjJU"
    "kHr4SW4wxWiW9CGtqOXAwhqnnGdt6cT5AvHXrdFkJf21fRFucSQGiiMSnRj82dK1XEqjgEWFT2kKraZM7FSg7sPpkk9iN5wU5lTi"
    "o3+hwd7/8vHX2SwXxB7sGOJF/smDtl9HRv9s2PGFhlO/jlaeBOP+5DjyBYc4/yvHDv/kePGFBRz/gmJ7f/Kp+wIDgn8hMbY3Tt1f"
    "LzA3BqVaTN3JpctFNeUIbeBNehWbfY0XD12RPXl2sEwn1vS4rK3V2BCCabuzeiZUpXZW3O3Wzt/kYrm4WJkLph2vt/50jpe3uWJR"
    "73e3vSrRg1dutfnxVW1woF6+cClCZC66kXDngFtEtLQC3Eu9qndVYs/lu5Tu4rrsZmTypF6+axuvrISAa5sFeZXHyxjXKe0JqKzj"
    "FQaAKrOVtvwmiW1dkdjmZkLj6eW0ADq2YAs+l1xdZq/Afkbca/bTnhqjBpXR6up3X6Lbe1MwKWVhGZT/cz+bFqYpw6Pianbc3Xbc"
    "RqAmkhSAqVxuNuVvGPl1E7uglt7AAigVtu3ydL+pw9K28/abCwbsUFyX5137OJkrn42rsLn70DG4so5NSo1aAXXdzieKVvTR1k33"
    "cg9KGSY8p6d3c4pmCnVNe0ghUhTGHgHKGYz/mEgDeaod5oBycptYW3MJcBKJ0hHkPglEnabmuWeedOjXvO10UyQnbfhUqpL0NcGe"
    "7dUf1bi60y3mbKO9jhLqll4waybVOwTyztVyLxtG6rNErd0Ur7Z8pNqrYruTUn/FydjBhnKnaL3GoNu5G4y8k91loh+Vcxt0aX1+"
    "VBQR5sp6441cXILqXXOdu88NJ9TpjObahNM95MGXMFd/q8B/tfl+vCBkH6OXwDMnfvS1ck5z4H/7+/P3NG1fIUSVYpdbraqlBcJp"
    "VKu3aIXrvw0pHj0x6ETlEsgd3W2X0CsHXulaP/xaP/xaP/xaP/xaP/w61MjlhRrBfTU/1Mi28QrgsBfOM46IsnHAtgrEANzkDpbT"
    "+YJq41ExK8eTgQC2PYrikKJvDbKdAUHWiUX6wMkVdzlgd8mk1B3eJzvCXLDXGuurg1T+vFN4QGfjdVXORCg1n6ymM+6ZLuPDo4Rx"
    "4QIq/yNn/JNO5ZWZplHkn/HFVQ7Dc/BOw005zHlUSTdwl6/CMXPR+UPZ+DYgEAtYUpZyXHCB55Evtgwe8Ngpu6wDEXflylFm1rWX"
    "BAFdSDyW6uYL+uHxzA89Zh1yqlySeHnuMJbRIr4s4UlaTz3/cJ4VolwZEclWYpGUnOdTqNp/IsHJ3D0JZ4gnR9G8pMeWHHxV6rrD"
    "3NVcsLqMaIauqs8sn1lbb4AvRAxmQqTl24u5etHtUOoiHPW78eD56Dfkmn0ShDPyAg4OZBGfWWfmDyFZWiP56YTEz09nosw9svQW"
    "4RzmYWm9z8lzeDYdRZOldSi/zxdRHAEtJLWxu1RyWncNWeb84+Pl/dlqShY4MdbpeLBHrNiaVQffxpVwViEH78Y05ZzIXP0bNl7s"
    "B+HJSr6fLsJYPL9zJyvSn62rffI6Ph7MrKPx4Gy8t4f1QL3Iv++9cxeVGTYQf/w4OF9XD8c1z51M9rDpmzdPsc2ZFb+eHVdvhcHe"
    "+3E1KRQFlffjvbhavZtfZkHi1QKgX1f3ztfWb/MqjDQy9NN5NIOZXvbPXc8DpMVzwb255a7iCD9OSEz6z+H9nRu7i/7buTWiYVNu"
    "wwNGClmF/afwuAC+2luspqP+M3hjVO/F3PLchd9/QP9GK6A5/cf4vPQA7xgF6j+Zs1uuUfS+/3LODkEf5gzV5qGH9nV35sIHBLV9"
    "/Im+4v10/9Gcjfpi6ofuJDrp/ygT5tF8Ne+/mjN9i/cxLfpwbvnQDTYtv7MXjEjd/44+E97gL/DG6vsZn96FuEp+hUeMjPID/F24"
    "p5Dy1dwifoibEZla9PCF9CrG5wlZzXF19WdTFhiC2YcupsDZTCZkEbr9UDyf9d0pXT60in4EL0HssgJLeJni8dHjD6LnE3ifTWDl"
    "TPn5coUJVNjU9+njKsaxXPYD8UYX75y/sfhjU/42Y35dx/w1iuf9E/4cuyfL/hvxgnZg76bW21k06p9NudXraErtqXEG30+tKTlx"
    "6WAfTllsrLvsLwa8PsVHBu8RPgInwgC5D2+rSRxypLg3tRJ7UVrJ86lFCSo13H6LLyfuLPxAM3hjjB94eyqkCwxBf5smlLv/dMoj"
    "wj3jD7TSF/iyXJ5GiKTwDLNP638Mz+xysP9kim5JToD7WGIHXiavy3k4m0GOD1MLT+cRR/o7+IpxQPo/wVM4hwXUfzTlkc1h5tz+"
    "j+KNQfRqyjfj/kPxxKv6Ht4B9bDd3+HxLXzD5O+mTE8C8BSe5oT4iKz9n/FlEorCv/JXZPZ+mDKHzYiz7HHZJ2P0FUaHIaaPy/6M"
    "/qXrYYGPJ/0Q/pDFFAZx0nfH1AyQdiGC55AsCFuQS3ybEsTGvgfPEWo2T/ABWSAOz0q8L09DwMy+j+8RjfUesMcYVv58zKQqU/aX"
    "D8yYvbFlezK23oWLeOVO2ChCp96M2bb6/XxdrVr3cWejTDHdqPrDfzgdx6u3hxbdsuC9OWp12h3gMGaHQAxgw/pHQP/DlDsu7n8y"
    "gfssGv5j1Kw3nK5IuHOCeXzSJI5IOoxgUiDVa9a7jqelUiYLPvU8J3Ba2Mo9rYhoDC2BKGv8j47bDJCh5ymiucBrDqVF2fAf9qg9"
    "argyhebye0GdNIbMGBG6PmqNRjZ7Zd9HpBeMhnTEHdp2r9fx2Xsd35te0Omy9wa8u73eCGHD9yZC1vUCn/bhCFKwhabTdQK8Np/5"
    "hxnQMPVVpluYei89spj4WIcak56mJi0mLjZr2+1Oa8ReD6MgZl1zSZcliSG37Va92aPgsnJirDETn2u1KpXd/offJnXS4m0wCVeq"
    "hpc0CgYkQkaX+Czx8Yzyrf8gflAPmrxeSr2wt21v5NssEQ3MAYXlt6bXaXRwPt+eMbDqXY++JR3skYCmJP1rko5NUZkWEsBBlqR3"
    "opps51hj2b5Bota1wKZpWs/arE6lY67fpWmGfjndHvKPI3eC5eujVstriQTeO+KQTtARiaKD9Xqz2SPYwbuitACSZeTd1KvUezoi"
    "NpH5s51l6Ul/W7BCmiJZdjkInKAr65e99r0u0gCWnO54q9smPRjjd2E0obW0603b64oE0fEeaWLHWaLoeJM0Gi6d2Z9EaQEwy8g7"
    "rlepdZzYQDJs2Vqm4yw96XgPJqAlkkXHodu047x+0TWv7bWw4yw53fF2r93pjdAO/QR4SxfpSKPeRNzmKbzrQKts4slU0fdu3fHb"
    "dez7U1mBAJpn5b1PVat3v+N7SA9Ek5n+8w/JAPgw90m6HAEgWjguog3RSd/2bD9JT49Bx2sFXcCjCeyNOJ/NNpXR4KuY+BZwzSOW"
    "JLreaLfqNp32J6ycABYz8U6rVemY7pO67/E2Mt3F1KSvHSBYHZYoO2rDshb1yol2vJHnsMTMNNudRgu3TRbICna4dpN6yGQJYpJt"
    "0sJuskTR0U630WMdfS5Ky12YJvDO6lXqE9zyA+wuby3TYZaedBmwAbvMkmWnG4DfSf2y2wQw3BHJmbnttXvQcfRpiDGuOZ9BCFSl"
    "8Bmj5sjzeiqf4diwXbpFfEYQuK7b1PiMpltv1O00n+H36n4qVQyt2FE38xlBw/M6KT6jaTfqjqvyGZ3AH7kjnc9wOo1e3ZV8Rs/z"
    "mli15DMcr2G37C+fz+j0/K7X0fgMx274DU/nM1yHNP2uwmc4bt3F8SnDZ9gjx3W8NJ/hNOodUYPEYcdtdBquzmfYbQf+S/EZsG/2"
    "mp6Zz+j4bo/OJ2UZOnXPx/0u4TOgg6OWo/EZPc/3gk7CZzi9eq/hlOEzsHP1RorPgL61G3Wdz4CutZttjc+AntlOis+AjnVanpHP"
    "6Lhua+QrfEbPH3WTHZ73rl5vtNq9NJ8xcmEUAo3PcAIGZFk+AyahixOW5jOg/03ElxSfUW816q0Mn2G7duCMMnxGw242OnYen9Ed"
    "wfpzFD7Ds10v2eF5x2HBem03zWcAKrdYxyWfUW8CwPXyfAYszFZ9lOUzoB5YKhk+o9Go+60Mn2EHtu+MMnxGs9EYdXL5jF6v18WO"
    "J3xG0HJtv5nmM1rNuoPHgBSfEXRHHjIxKp9R9+r1urcNn1G3nXrdNvAZ9QDOnQY+Awa33axn+AynBWulmeUzWj1AlHYun+GSXmNk"
    "Sz5j1PNh59L4jLrX8HAZqXyGR0i711X4DNhjRg4px2fgJuY4aT4D1kvHGaX4jPqo0cHlr/IZtufYdi/FZzR6zW7dN/MZvbY76rYV"
    "PiMIRnXcTTQ+ownci9NO8xlB4PVwQ1X4DNg4W3W7PJ8BHHDbcbJ8BtRTd0YZPqNp1wPsss5nOE2bYKdTfEar1SB1P4/PGNV7btfH"
    "G42HAzL4dvjOXezt70ercP+rc1JbECrw2/vm9e39X4+/ObEwy/7wa1KLoyfRKVncdZdkr1rFW9B7TIxdhRwGW+yvzh/ukeoa/sbr"
    "f2q22FD0uRSovE54CHhqB52gR5/gmIubAxCTgDQITQOUc/0GPvWQKtOnzqjbRZyDXjstH5EU+d2m3aRPMCdeo41PQDDtOq0FSGoL"
    "RviY8Vla83BagVMobSrw2z7BJ7c9snEDAIrYAe7Epo06Hb9LG2i6LcqtYqMNv0kBrvuNRoM134QdzWbNO6TexCebAADN4fHaeiuv"
    "C4JFNL0PsxSS5d5r22rZFiCzBTy71YB/TRuTbAvWjQXoZHXhXw//tezj2tSdC4n/a2KpV9hfnT8f1+j76xhaq9B3/IKv1eFxtWrd"
    "Vu4h9tTLGpw57bKWJnj8Ma5mdBoe7s2qWdXOJPVuUjTjpZLmygY3UJKV0hlb8od7Q37HOKymbcir1m8SRVP9i/X+3cNrjUY96SMx"
    "9TE29pGk+kiMfYzNfSTpPpKt+/gU1pLWN5EZadgw009ZlVXvJv1VGsj2O1WhYQzSxQ3phjFJ1Wsan0wFhg9bjZf1bFeUGOKRLF1h"
    "sVsEWofT3hbEaBWj5NtPMhuW49pahniXpmZCdHgxHmgxMCoOGuY2eAzdPaddqTcrTYzHXXPaLEaulkFE665R1zIPxoP7872jsXW+"
    "JFN3FodeX9EDYfoiD9xpODnDuDljsghj3G9nRDjNlImKCz8WqdqkPIj+HZeJsvXzueuF8RmmN1vMhSuvoml2oEitlLhuwBKPqEMT"
    "hgs1gLqqfsQG3+Jqh/234yQKhqEK4W5FomM0e1G8BCjzkIvG/OvakppY/cJFnXYQnMmQxlrF26pMFF4Y03l1+HkilUDIRPomsj7V"
    "Pom6c9yIdlOeSqEEH3Mz7WFRoYfpBTBkr4aemqBHJaXF9AG9DT1P9J+ZH85E1bmdjXzeZoim4W5KvdupK7X8zHuYVMqw/aK46hhw"
    "VR9F6m0VShhsTdRhzBiVKEXN5iOZDA+yyCcypCbJU5nPnK1DRdBc4m8w6IDvTFBlwAHdWkPB14xphvItzwhDbQhJUKZgalpSnsCb"
    "0o8AnUOmpa18bzOfRmnESyicPtIS7w2qohkqkJhAXQK5SGmNZtMfmGiMoqHP715NBIEP4YtxCqm3Xf1rec1uaiUxbK1fbqPTyHcn"
    "6SY1ugDr3S5qM6GBZRuFVjNKVrr6lrbZN3Cz1zb4duIxT61V1d/hN+3C1C1LGSlet3X6p/VbUFVcOM9nkzOuvtaoXwpdTVdbb1Ni"
    "a3Cd3qYRh8WWflvlg5W920rv1lyIjvkVqTgtc097T8vM6bIQHvWejplQ+7cxUsoggvxMqo25uOAZv/Fn+Czl4pCDevPEz1ykDp+l"
    "cB2RL2EXiziW3GNAq12C59/IvSexmLwM0Uw3zT/ktSzuKXKaTT5rTgvTFKzUTmRe9qZWxce1YJqKxvoyhtPUtcttIX/CLjQpSJiE"
    "hZJKN7IuaFRKYvJi1Obx+DiZ6bJjAx39NOUwBBdXvWk3aVHm7vSZgoFqt+gye5a3zOQ6fZa7TukSf2Za4nIq8SvjGqwEo4RmoJHK"
    "UiKYWD8lOxgOTp36XmI54sSQhQ9MKz0wjAYavEWxiugGlajzpz87bX0m1oriowZ6ZuvKtZFSF13RgjSzOvKzZzyVlOVeZD+7YjB1"
    "b1XtZIxp55scW8tZDzkOzZ6xFSoMury572Y2L3PqSYxnNvWylfTSZByjMiJFa08c91U7iWWym6/XTC/wPIl2XS6WtIiUqsbNqJvw"
    "O10uCcasMivlMCZ1VJeHZmNIZA34BExzrNp69hAsaXtesFSNSUyLjFSN0qxjAnX2DKcMARVf1ppSpe46jbFtSTzAbDdK7LM5xybh"
    "fkpBl23kBMnHrJ+nlHwmx5uTnmu9TrTI9UFghFAOQtt8dkvtQI46tjpbnZwQCsQPOo4bz97GfouP4/xDfe6BI+vuzXgeKVxDmjuq"
    "1AgbtqKG3PINeGrs4Dw9rYeppSFOnVkTc47vqr66PPGcqgeKtdQmNq4t0VU5RPKrTi318yD3ZUx93Vatx+PBkJx9N//17uP2499e"
    "Tn95dd9+9uGn8MnR28az357Gz+49mDwNnfD5vZMPT46+e/vrkf/b06PHzaf1Hz48u/t4+Xh252xUf+n80vghfB5+d+pNJ/GvP/80"
    "fxxCTx5OJl4I9U6fvRu9cpzRdGKTQyzzsuU9/BHzv/3151/CJ3e/m//yM5T/7X7j+dEP9adHP75/9uH28vH0p6YHcD09Ojl79tt9"
    "5+nR/cbTR3Zt+qP/bvxq9cOde9Pw6M7937+ru7+1f/rpxbK7/+Zu5/Gzw5/3f4keOEc/7Dd+Hf/ee//s3aOf573WkbtYtW7bv4/i"
    "FyftUfPh2H7em3S/f3l6574/uXsyvBWsZh4KSSpPxnukes7MTM655vsNx5qEHsGwnY/HVjwmU7SEB9pH4v6DMRevwA6Dh+CnkU8O"
    "6fSjkVEtWnguPRwPUbf7iXsGE37Dgdmt1WpkMBgM5/H+nZfDg/NJ5LlIilxg7uaw6O4yAxAXOMYFwSu7/vAnwAd898ZRBKAMaTPQ"
    "MqZxQ43h/dm7kOZxZx5sF8O79C+maHb8w2dkNl5NKxiiq0JmTLTsRzzXA+qWJ50X+rsCAPyogrGtKmQZk2UFPfgsoiUveEjchTfO"
    "L6i2tNTzntvrJONSybkUZn7QUy03wD5bVpZiEHwFinR2tbdKAep/huBKOTqbk2X/9fAOMMnf46+n+Osh/jrCXy/w13389Sv++uUO"
    "vcw9e+ZOaTE/msL6QgZ8SU5gDbr7AQkXLrzDOP73/ySvv6/cRay+hjPldYmWCcnbf//3CIFMWjocA4PDmmNNsQZYvaw6VgsvrRR9"
    "CvzI6+E9+HCIfYJ/P/B/h/TfsTWF8R6LDv0GzEa4wA4FBCgsfwZs/O//wQd3tAgnNCHE199WszH7O6F/3ZNoGbPRgBEf0bLRKl6x"
    "pxnQbJ7okw/sUW1e9BJgYO2zllmzrFHWJmuRtccaY+2wNlj1dAhi8gAdnsMS8v1vptNvzs5w5hfL+J579jx4Rcjbvm25aM50Tu/W"
    "+sMHBM1xgHIuyLswwt3gNmwbizCCtBlVk3yx+O//fR9OI17TC8Az5ilqiJsNTmFl/t//jZY7Q2viahn++/8CXZ8q37FGrQJatZIB"
    "wVAzsPSKK2FiK+Ql7kEJVahMgDWG0quZ8vkeWcJgevIr7AT9c/iFJngvx4PzKewhsLfuVc/DYC8eh8vaV5y+1WYwOzeAZB25oyfA"
    "SA8/fhwiZz1EYz+acUGCZZWRzlsTElfIIEm/ZTSh3CPW37GOv1vnacND1SzRsU6A1O5VB99ijD26ga+BW0qo9ocx1yo4n928+dMY"
    "7/FJbbUke0dz6wm1KYT3afg+nO29HFdpZ+/A7odqhQrt/4nWMvAjD5qeAaz84f6E4J/qOZQhtGezAXyFgyjgHCXxP4ZHuCvc2psh"
    "TaciURge+kKJf/XmzR8BKitmbT8aD4DWJFs2rEDOSlpDpoADD1TlBv5yvtYaamo1w+ME7h83wR3XPMDBJc5ajbGDwBUlOxNJ4LSM"
    "/RqQTPpt2Kdm8eAO7IfMDJoZ0R56LD8fpfvj1+TYWgyk6Gr2+s742FIlnjTp6yGTYMpPVBmKfaEHzmNLcnGQDCzd8Os749f2MXTn"
    "RzQJYzpCkFZb4la951SPqT4srwO1o4bHgDDRYo9iJhqbPhpXF68Jq0RRNPqaJHUMaHFyLAq+hoE4hqIcmQnXoJlVq9/8z2t3/8Px"
    "13vJtH7kk/qRTelHOqEf2fR91CbzI8JX/eqbGmypMfAfN2/Shcb0qwGR9gDO40FcVcCYGcBYVKtiMqAlucaGO+haAVFiqPoKUPX8"
    "LTnrD2GvRJPI+E0wiU7f0OtzOOrCvlKzHTjyvu/XLT88CeNlvwkkJwQaCQcSVhR5JTgskTeu/w4ZElbO3lBKNggkZeFSVH8zIbOT"
    "eKyWb9migjqvYDotrIIaG7IaHF6DrMKWVXyzzFYCmd+8QyEMVBZ6akU1PgJJTY6s6f/7v2pd7uwNFFDLsm44WSD+qZeCxkuWOrYe"
    "IoF58eQ2si73jx7Cn9t3cKO/fYhJRy9+xA/0611YWt8D3QdUgepRSR2obbyiKug3sFe4xbiTJW4S1u9j1N8DZIGVuFdNsOn/WX4N"
    "uDSsDKv6euQLybbqzar1HS38GhjfGTmtHJJ4D58fjpEV5ogMnV0C+h9XFeL2Cyft1qJ6jks3HJwj7/w6Pj44AJhuLYB4zVaTyceP"
    "+DSE1YJW8LA44HXIjljDmzdvPKNPtXD5IIRhIrBWDnw0RSWV8PXsuI+/BgukWudQc99FoKI10DFucK4CGFZrDA0PEJLIwgLhuh/R"
    "9fKzGCJ1PSnr7n+AStj7va9x8Q2H1aSfv9J+sj7OBj/jpgWEk9SYj8w9qJR+ivETVA99FNbwN27EN2/u4coH5nL5Koxx/4PdR02I"
    "UX9SdGYh4F/0CQX6BwY0kB3xBaeGHPdxYK2vpPrSd4fPn0Gt6KciDM7o/JGDg9fHxzUUvQHdAKplyBNreSxyMjinBtNvlrCucK+H"
    "BQGbNXUxQGY+HJxu2BLzmFOCSbRavPHQoy8gpR+61OoanxdB6GMWlELBHzxG0ctueKbo/AY/O9T0Ho/9NEv8ZkbLAtu1cN8wm3f2"
    "DiTiDfMQhznxgBK+I7QCHygsbQgAfUNZPlbX6ZtZFAOS4xuKnN8kPaCvajdogtYXnpY0SV95X+gzX5P8jR86xSvvvMIIxSd7DIVI"
    "wg4A78Q5gTtnj/29Ia2SLPZHURQPqwc1lCXwKMEHfGkfHAyH6J/hBvn4kah4NHzzZljlPN75+la8OONn5QqddzgZAr6T6hpmwRuL"
    "YzRnL2cnAwTPWpwgmwndR/YRdeIJ8KXA1QNDDzzAkmpl+cj2T1wgQhQFcZzhSOG9fQP8owuHREr5gK+E8Ri/mS77bdJEDQxYZWci"
    "y7JPTqzodCYm+DU0hycm5F/ewCiieTvep9CZhb84safQRyCISKNOLJGnf75aANdNoQuhMv8Nf+cNsddxHM/733xDz/FjOP/0Oz0H"
    "bUNgslHNmg76FI80si+0DwBxTN5QORJOK3vlAmTHthhmvOFd6w9HEe5+yzHU4aG/AMBMhubscgD3HSGX7Z+zZQD8drgc0wUBqE+X"
    "Gwo9h3iBi0Lz2I1lXg9DBUtQ12JI+5TknqDPxDOqT7TGnAyHh/d/fDm0TsMP6CQDJSXRyZv5/0/c2/bGkSXpoX8lMYO9ljDssqSe"
    "HvRQ3pFLFNXiDkVxRLEbi/tBm6xKktnKyqzOrKREERzMN/8AA17cCxtw3wvcRQ/QBhYNw8YAxgLDfzJY2H/jxhMv58TJTKq1Owv4"
    "i1TME+c9Tpw48ZpDkPU3HH7j9ZuioJNOXfMZEwzuuMVfnyMuTct6//9TV31mq87U/XqrJGT5CU4v4gGyMOMnJtX4m61QgFcbvuP/"
    "+JlGvyq7jgqeyK9YdNaAT6OSL5oMsrNYogGRqGhffv3pd/9fLG1Q58Wv4wcwFpf07VV7meVnjMRW1OUXGNQR/Rc/9vWbmpByF3pB"
    "KjyWPzPWExIUPfJmorvDsK/q66zL+HnLJXTx98Qiagn95cryDX3ON9kVohgQ//aTt+dFTdfQMufh4f9B2SVEOK2U/7X9jjB1fiHZ"
    "2zEHIRlZJ4KVTosZUzort6/EwuNh+hN+CtcsoBBoYBqA8b99093G53AkuSTfgCBRZz+B/KZY0jrYF4Ug9rY+ivVf0J+ZawTdIahS"
    "cSaNqDTIFfGiHxIVKd9ROW/JdizVnQrlL1k6lelnB1g387p7yxO+Eh7zOjto6HWOjxks7TNbv/yUliP79F7WPcz4zEsJHbbspCDm"
    "vsg2fMIElWaxj7d5iXnhBUfdbM6LjNc+g0YrO8+7+k+/+782Wd62uK+ySzwcfyJjoSWuFaGP5Fe2aUK3gtzEVrZxM4/vZ/o6ycou"
    "a/sazGCmr/zsBZHPI7B17XaGcRzV+XqVv6FpHd/fyogTzSC4xvVEO1YvIWZ4g/rSPPqGAJWGWkiTReb6owthK3t7Xi7OM+I5mwyE"
    "rpN+mWTObLARxyZHu50trMXBEMOYBkOdHMsse4Wu6ZeO5O05nTDbTEQL6sKI3p5fsmqWhvTV+WW2edugXvfIlT9uljhrcQWzBbUB"
    "MWpTF9wLcc7ZuuqJ+GdrwlUe7Bltaadfu6xusrd0SmkZz8slAciSdU1EMariZkH4Q4SpC+PB6lZFhnuE94AQJHvVs82BrJU2w903"
    "p6dYmDhgwrIuO9ShiA0BLcOqwQg3ulRbPATcpLTE1h5XtMO5pcgrCEp/tgU/g7eypWI/NQDEJ+QuF1Te07Gvssumz5jVoGZBszF2"
    "Wl0ORJsQKj4VVrKAQOs1LTCOJ3aRTie9Du7LGAZQtAJtCsck2KibxMaVG0ybvO9WJ7OXYiYwoxrWPLV5e61hR09z2rBlijdaRNhA"
    "BGkNCedyO7tienZt1ZU7YsrFvwYFQhNeFvnS9j6SFCELHppHEFfXeo1Q+VIGOgeB2mn6aik0CSWD1kdD7S7rBZqn/7LDdBFQ9Kyo"
    "1jrUSC+JCDOetMVJX1bLDHLqy4C+gzVNsdi3rZRRfoV1ZexNaaTUIAqqhFQHmu0uhZAEcA+rI2d4B7KdgTfoeFn6Gr9p/NwOYVxy"
    "CqUP3HQTBzFM0m5RgqFe0E5YJoOZ+WGl14F2Ugwn4uatJ/XF6altE5aep8VE5PR0G6l+847uvngmh5zU7UhWN8dtNdso/QyDL/Ve"
    "w/D6tV5rrsKJENRdXAUgD22cd75cggnGqhnZ4TGzKCp7RezOLKwyDavmEXXSiF5VdFiLWdphB93ET6DoHffkDnw8DWFOwxPhOpqo"
    "Zf3EBZN3BF1roZmTgluy2qz6Ct0R/6GzcIsmILpoYfzEPeBWEfBZNl8u5YbGyinMliyRrJ1Sk9mg1Xx10lOzj/F/Rox4j6O5pmkQ"
    "brvmd5jrwbwQqI+Irt+hD/ZTN8/xqJyY4grfUbUrMhGXdMNKOumdcxjfCR6y/jFr6BJGJHL+ppVxCLqiUJLCncTjs8kn93PAkt1R"
    "CneXsIzuEkN+LmP4wKk/xHW2okua9rPpN6AAoKzoUIejInvq9GmYXFp0EMuo5xqesgFC5on1IjqwlZmABL82SHfOchEsw09FWCan"
    "Mq29r7er9BHR1qBEphEBTi4z+eRg8oqTAfctWMx5VSmEb8ZkJWDW9WfagH21JoJ00oGJ/IWbqPtTIlx9WwzG8SWDxEYinG+IRVQ2"
    "8y/wx3jiEGkZyBH9HkPkHW62ebcQYutKlgUXISLouKxs9eqQCLzEwSnQv15OwZukCsM4x8Wof/s9wtuYXw878mu8RQpil5by3oXj"
    "gTIFETae+D1pY5Y0QiizYwixw2droif6HIpPR2jNaz+rhcXitd/OxPlxAGLoHMHsywjUYZeCrsZIJqABhwLgJCph91krqrtPY6Q/"
    "hgCuXwGa6JYBQ68GdnunxHPT+1CvcYYOXzIRGQ1r9J1gBwPjj1vgWLT5OoHmT1xnCAzFdgqLL5OgLNgKYI0+JvkrC0cYjU4qEco8"
    "rkwkw5/PWpZRfEH/xY/0jtnIY6v0TbQ8mJc8AP0kQQmYgcaPWHBZVFXzlqUf+OE7LApBKfrfD68veHS9a2Tdt2smzof8wxXQIxOf"
    "6T/XREsPC7SB/+NnDhsKmoX/w2kRZPQPmPhqScrcuyIQIDtC+/GE0I3pTocAqDjjeURSE0k5NE1AvzQ0jYAJotINSQ/1sj7uijBq"
    "uuN7lswlhW7YAUCwctaA0cTza9PQhXsdC6riFDTs6u11hp9oku9nubzcK+WnVyWiPWsxXXbMh9KtSz/jd0jQgS9P954QB4swsbGM"
    "7tZCh3jztxjkH/9bhn7tu2v8LTf+VoQU4Ttd53zHrBo6FMwmxX7lxeurbQeWhEPiZqd0J199E4ejy78vC/AynHf9HuDWi43CXNHP"
    "67+IpCEOrD7U4/jCH0SeIEtq/cLly2K5VysXT3SDturqLXjjCMT7SRB7vIuyTikEfX4KMgK0YS6t7TajQr14IMijfkTJkon4WkYJ"
    "MYnJyeheYgSym4lfTmV8FIXWWb7/SuWgT/BHxlLRFGB+1oRi7PVSRasO5EW1DCBVAycOwFCvuciOrqjRjmoSL0dLjsSVbdqAzm8f"
    "NHKVt2+oHVU+KJS7xufxBkd42oGAg5Hb5CcGwidEBKlK3EX42MGy0IB63ijZg7BQXAIpDkhQcxGAdTxxOKGVOhYd2+9Qa8kToHdE"
    "rizxxN4wJM+eWbX2jSxF2BouZzbhiQIJryBQS7k2GAiPYxP/ujdLWLhI//Yj8eMiXpiwpo3sIn/cQktnbs2Wcv+sOrvcuOAMX3RX"
    "uXQrWwlyEkrcm2XuIWsCkwyidxZl4dk/S1raE2/g8KLNM6FqWD8GyPIT2h3kOCdmlFgwKJDu3bsXWpGTriggNZRIumLHzIv0ACDp"
    "hAVQJ3ZAbZ162LBSmN0Wy0rwcIkvoHLTFdXpw+we0zCaPtO++JByfQynjEbiwLcEge9NzZWw7KBhGiaYVjcRJSDK0EKIZ5Iy/LYl"
    "OBh8N86XBTJ5F6f0r7rwUnIo9pAGSaB4wMkMaZgiDaVPfqB/zTobGqf7toOrm74+I/pPbV3GmzuBiAuEad5HFw/uGc2jR2Se4RWJ"
    "ziSKuzt9R8oqxAITUKO0S0vxnxXzmnXJLapQiLrNGpxizVSSEPMBk3swvgM4wy/h0ehec6ffgfEo8dBhIf9gUO8gAWYud1d/TrRS"
    "F28ZTd9O9cBikxHKAy+xubBEGfSJ+OkeNCUpDujwnAUKsMWmXRh3DZggueQbnhUTSbdZd563Jju3Jli2J0zgVrYhzCraHMxVFGAV"
    "m87teN3YYLsJuY61ypKgh6pxwHmhMdB96to5jRtmDW7JAJd40UM6GHDUlpdLlc175ScBkscqHCIW9/1NDREQ2HCWspQblh+KBFRU"
    "Q66F2gnZIGlcr6tLgIDCNs1sPAzl1m4dCKOsYxr+7LGoMmtqNAeyKNYBj/qj2mdtjhM94ZDR2M4gl0Zvfufl7RlwVZ+fWhqkMjv2"
    "oEgKDkIJ1iWhE+H5LqR1MagvNC4AvRSSt5hoa1m2ojEOfbGKzg8lf6dvY6izCM2QLCCWg88qN/0SwfuZXS1Uh5rXjfLg1lWB0D7M"
    "48kvf0Dev1eRIX74MxWBTviOf4y9mSoWhsovdng/27Zjs74ysN145Y0gYYGmk4ZlTfJoT0GUfnBj2ynGDGt4kUBytfvFtEeQ2sXF"
    "PZ9kPAN9fbdhAvvOtXWiL3V5qIeFVnSXuxUqpmzBX5aM1bV+e5tDXC5KCaOWbXNSEXK3xTd9aY94+TkGovP2vGeh5vPAbvFdfdty"
    "WsWlvHrmzEBmXQ89c0cX6oNffHL//icIuxiIITEeWMkWvhb2cdOwRC65euz+OhhfJX2NA7lkHpl/Td0S8DDgC+xQfgWm8/5jGBHj"
    "GWcs7DUrrk0fzqhFdCSHutcU2Q+JAb1gdT0sFQw83wSAGQsd2LdozN7rPZ7d4Wv/rqdKj7K9jbA7XZRkR71s56WORl19V4ErCXdf"
    "J+pV7jDpaDfnR7BuJ1Hyvqp8WzKvf+LCzLLnP7IwrDIv6754NOpL+De8jJj4y0eCWhabvKxMTnnQZGyW0GUnTfPGiHwYEV2/s1hH"
    "IIOAhP8clzoJiXzynb4UZKZu8ehWAwYWwP2cDkDxxgFXRdfBz4XA8VNOTM5QRiMMEvYIGxX/BrUFfwTjKRpxzINuQNZYESgrNK7o"
    "LXztvrMemLGEefhgVqTq9kropTEsScFGRYUbeeWFApX97Kvch0VJQTfCcm9i69gsYiC1DogGYwyxHBHrIRsC6trh7WEl5PZUBBDF"
    "0jY33cfE9Iz7lQK/+LQlnb77+QnXu/XON7qNUAidXWdnbAOCjYkwvJmKKpMliiaDTbfX9ROVMejnxCTMQeeX3fysCRgJMYaIQIYA"
    "DinxLYWiRVoUYvoFO3/7rE/oYwie6SI4hXOVlTkZXMYmmlYA82D3ijiiH56CuqYPi1bRm3sYLyFd54W+CBXtiR0kYtbSXm/dcmj4"
    "z3lb5snbn5OnMYU6jQfuc6m7lSGGF1BeZFdXnDGNpWkOF9gqzhDCsIotDjb+DWR2nDNCkhMVJSruuKL0TLiCpWzkExDSXN2MfDnR"
    "vTeMBc2btMDwnfkI+TnoEl6sPPxL5iFYdhjUsq+8XF+KguFeQK56ZNA3gnRYBugJYB7/b3qEiCRWi40ypYB4TmiZmfuGttnsMpNS"
    "Za0chPxLWxJ186p2D3WnLEqTEm31GYiQ3I7y3ntHD+qqdC11/QlQGt+WShzxkIbh/Jq+/CVPWtgmev7T3yx5IQiWiXUmg0lbVtJG"
    "qApkeX7kvjFTSp+yZ6/cV6pdtMJa7+pPh38pzJHaJBigAwlmdIJQ8tuVQ6b8AhL9K/ioEFmuIIivrwcgeJFMFNE8d+M4MevitrGq"
    "RfaBvIui+elE+UEEGPSHm8IkBgahLysDaQt9er3kH+PbJe+68qzmQ3QFqiG2ZKLM4OkT9iuIr7VcHtMC2cOrzrBhdKel82XzBLBG"
    "ac057/rPsnTfqeDZxr6nm09Fu++k7NbNl6defOStR0sqEDpshZJtdkCMtEfy/lCYKC4UIfV43+m18FRZYJHQwtrtNFCyFEgP3p7Y"
    "UpxDLHdSFHUmTj5LrKJTiqfbJMvDP0cLIBCGDgqUx41gfYnsrlZJ0KDfNHrt8ChxeTB1SWz5BMVMsCP878iAC3IMcEIF+M8lbFk7"
    "Zwio3J9m2kutwywKxVaWV+DMLgENaU5U3tt4ocrLK5OrwoAH7dcwxaQFxfME2il6isLmTjm7sJFsPUVdg0tW3J5hlNk+Ku/D5pYF"
    "pGotY/MWafEs2dOEn4ZVC5guNk3i1dPPai4k8RC8/FlvaGzNLEV42erlcgKR1cT6mdKxr+TPICq04fIUYNeUGhCrIXXaFjD+49ti"
    "smDeBvL8uP1w8UPEaul6i5hP2G1Dxkej1g6D6bQ1aLA/0qaayz1ilrx+wz5ojkTiT1/0OLEIoxOU3dmfH2Tw/LlrcGo7JwSv5fhm"
    "UkA0sxVurlXSy58t0SW61Z+hqXX56wJ87fxwL3tTXA6rsLgWjH5td6ftghynw5YY/31517kGuRqkANmLxabhufLpmq/XVSmvz4zA"
    "wsD5LiamVcXNcv9HM/N4YvTO5krnRLy4f1XNsXmcLMgWmE5eA5H+6mz4wX3LTIK946+yg2JD0G/oV5jeLIMjFyTD1vCWtGEtlyKb"
    "gWAEN5CsZnaHo9PGZu5G80k4+HRpG2bfgcCe/Uat0kE5xGg+LoMdGL8SWGhWCr6BnBqdw/TVVn88yeFWBBvGjI8WK9xidbMpJWAu"
    "/vzeFp/L4l2O2ObZ/V8+mN3/xeez+7PP7sE1+N7URDGoj5pj6DfMkK6Ec9oW5pTjzrXFKT8u0lVsswEy93ULyoaoCNLGTh5sEIng"
    "XZXr621soEeKpn6U0sBX8uj9WWasmie9hSnO5JUSLXW0NYiw8+otv/s6CDlUHw+RB+3HFnGkF7AAFAkI7r8V7QzSOdOtUdJl1BSd"
    "DVm3B7ohOyHaD10ccxHzykHhHSo3W07RItIbNv0suoxdN6tLERvJJUBj7lVXmYh59k4HRzlctep5Ybck5tAls9+i4avxLZVhOqaM"
    "2MqaNpXPsmkO/C5o+P4SelOVcJDWVf61/GWvwFxXkpaOW76TLDW/Ku8KjjFWP2+auoVjC88DBCFqnKmzM4lxj6VoTk+3RPXxtlQC"
    "EyXJMGWV8epws1dDr5kyCLVOLp17ScBqiWGFR6Hd9VZSiYRxXwwEhEaqDe1B9F7gDf4ULm3+nODqbBs4hHDIywwOh6ERs1fyx0je"
    "lXyFcbEKurdBTUXyB9oxGqM7Vh97puSurDO70sKtqFc/KzzqmqMabmVvf4wBsNoLqZM0oC5bGIiZzBNkyezuod0T6bIEm1S/CikI"
    "X2wvOLRLXm0LX52e1zimJbOD4z3Ab1aWm9J8WzXiJ1Uu3B5Ipoe+9RY2oOGDo3LbdK4msVQrTlzUcXFs3rNM2+bTUetV2AVbcxa5"
    "2P6xI9SY0PuG/7mXGlGzCRu+TIqklrOaH1UaGff9eM26CVqJJunNg/wIj7/leXzXywyKgAVRmGV5emr+jewXBzp5ftkJ8mRiOIY1"
    "2LT5JetTIuc52nuGYSMKU3fZR9UZOY2StGzlXnpojzcukKfRlN/UNrG81wYm63F8n6XV9YjCDcFe8bk78js4hF8RVZ5JBE4+Nryu"
    "NjQuFJ1Y9EdIC71tdPLR7DN2gsNC7hp/lMKK0i7cEKz+Dox+t2nWnd3Z8SaAHoEVJ4IzUb2jTyyWJZpnKvd10nfB7TE2bzem2BxG"
    "wOGY5ObhuxSzaSE6NVsxbsD05EFptMVCAP2K4cBSBbKQQlwOk4Ed5ip2DldEugrohUFm2Y+Oqfwzx7Iz2PJN4y1siJRcvhW7t1Ah"
    "MZGHcUICEt/I+QSCoVQlInFmpfgL2q6znsNtd4I+egHpzxGuyT3E4EpPowO3n5e+isvFG4j4zBNFwgRGYxItj1MyOgeRJwbIL9GZ"
    "h2SvnkknIH6+oH0Hv6H5189K0SKo6VQUheT63qV7A+sjQpaZl3mbbFteEPbZQyCkAu7jZVX4z7WwmU6YYR7KSWWYz6p0zM6N0FUw"
    "gR7yHDrpq/PrjPiS1bWyS6GUC8efE3m9mW1Fw+oULqokKxPvD8vdhSSfPFCiqsiulmkPape8DMbboWisrogqw7gPUWcxbNq0FvON"
    "01tkPh5CAAXxWyvkkfwGYGXL42FPcoljIH8OFImhPQj0Xx4fHOwdfGFYMthigTl8uXs4f7kryv41H60x0NH+3o41dCvQ4fz4iNvJ"
    "1R51UP5072Dv6NktKhwFme/t7z4BCPscBs2nIfvTeCvk7DUhxXh4PJHN+gpvkFzxWjegC4Dgqmb0cGGx6ZtsVQyeigPAnh/9j7G1"
    "Qy7UgTXsgfpEX2GI6fUmALTFQhSFL/mH9RNHBOXbgeJ31L0NixW9GSBRvOvyNBhjOCVEnk5EhZYWu0MyBJlWsNkcEGRCPStGQScC"
    "2C0oLAb/AUpebLqqUDOdXYcyOmAyhWP+Eb6nmjNn+Whq8c1ja/VALxM3fLSqbSaj0DEk3+TSeCy/5KLQyQklPIoaAV0b4fSY9Avb"
    "BabPjbxRVbzZZLqryoM8FScr0T3Qg6wbdkST3FtC2XhahomW4UMAYzvlp+onFtTDQ22Ggz1glR4YXLHuA5C8WMXk+c49SBFgQX53"
    "cFZmoSE6UI9lQe2x4lyCVdArt6BVdS63QTw+cOzt8kth4c/zNTtfbPv+jmVTP9CfxJe2uAx/Zo9v8y6gGD01YCs2wDL6VG8GMFEs"
    "kwLOl0sJ3x1by/HJov64FsegGlVlDG/ObLokVcPulPSGWmxMkx8f+cteeSjjatkWbhHWSDb/tg0n/rNcSXeRjV2WugNCS7jB2BTL"
    "6OrMagpKQigSboDkwBr/jn1OUOdRCibcu1psMa4TQYmP5reQdquchcNzuF3fTlr6dVGsk+kgSAnrsAaUm+fF7w8EyFGRm+jqsQOt"
    "OxZL2znIfrn7NCRDAENylQCJfQGwEAkOUDRbI6buMiiA+a9B4ezTe3ZDfHqPjWCGAL8MAL+cBrgU7p6tJS7loZeU56xBgH8y+JdQ"
    "2pU1m9ewRkKFhrYBKqBjEDgjbcT/iushix47cXHwJbz4+FTmae3OqdeSUBCz0NA4qAN/9wuojy7HPxRuAc345dCbyoXiRdMlRrb4"
    "2/U98rPj73RSN9zlV/wjcQGTThebOa+nesQRG0frO4bDQfmr5sTW9+vmBDBFN5ZV6W6cF9WpedERscOfcRlqtoVaBlbBHGWYY1oU"
    "E4COabgNmO8L25YQGsshus7EgsbsN+KtLR8iM+N342BkhjgonTJDDNh6i+FVUq5WVAlKfMiQKk63QfXOLPG0umK6N3nUihFRQch0"
    "aHzIkmHhD3MQwhBOcn4ed+sKxOsylY+rYibfcBuzjEMVg70oNOaiRIsQlx9pf+UCFYSgBelBCCC6NvAszRdtQ68MDu7mQhsMKsTt"
    "ci66Yxi3aePGxlI1v6a4qIQMhQrW3AvzfJVFbkTE0A1OedewMuClxg4T52rr+agxb2RzY6L7qo2gjthEs9V/k90fb6E9Vn87XaZD"
    "/i2fpwSt+KQ+vhwcXez8aEm5RJ05NA5d1LKYuJ6wgK99nRAy0lu4MmmFNTEcXI2lLvLnoFQ7OerX0Aiot0/fQj4I+9R+zdzqgOhP"
    "i55Z4m3ka5YSSn5IcYwN/D8o66RzN4wBAA9IvN01PhkidkOO9NbhhcDS+608ac37cif+Fcl9cHGYZw46Y3Nj5ZU2TbWMLAy4DxFB"
    "i34tF3UPFAqsKRShHH2VIaQjMsOWIW8UVo7Xbfbp6jQs3oD0Dxo8atgKLJWp2BadI8xLbEhtX4Yt6IWOjJJWcZUvC73GOUIUq8j4"
    "lCwkOr9roxGnaj6C3OBpXw2JNBFRlMiZY6Bbjzl92zQc0FJkXfr34Ko9UHolf7l+noXqI2P423qEYbe6ZTwRo9H4fa3Cs8PkWkLJ"
    "RKiYlAIBKPjsfGXuIK5MV4RXJilRFmTHcx7TAzmNAc9EhhLf4LDU5FcB23RH+kwsvtmb43coKN6tzbqSteKELDtHX6K42KRxsZzt"
    "gxafElVSdxyOyGV/4zGpSvY8O+nPFFxMWuM7Waxdzc4VEGd9yRo/6oeIDv/lS/QhEKJn9W3deSuwMlVDNx+KdSeh/mJsRWYI7OHE"
    "D2SkRZZrHbkH6K34hY6OHb4lktNwmGUAwhsjhM5iBY1cNxZRbVDf+onhGQLLop8UAMF3Q7CdDH9logJnGq2wep99wndBFHejPn0+"
    "wlfPz2aa+zG7w8+4uxFUaeTjgn7LKRLU3opCDqJbwxAw4Gg0zADV04d37qJR2GynfJDc9wO6sQ1l5L4LGiJd2g0OO8OqOYdiguhS"
    "Nm15xsESbF0G/e6qUtCc3m30tT5nY+uDijsTWlV42rOSPxy8EfxYoQqMuLXWwVAt8UHo53LCfyZMnB5xKpZJBQddnWSXlga1/Tnv"
    "czHe0kYtVIFyYEW67aQFkTOZQCotIsKr8tFD+SVSXQeBoKAskkOMacG9/FLE+UlczViSDNicbeoYwlBip8ZRKodDE6rYYbRf1Ubj"
    "3rJv3dtGP3dJP2bdC3Fznbct9fa2rJeM1bEKPXLoVWeP/xxXaOyH/Q+RX0hCouIqhr2HoZRGuhbLfvxKvwdvASaZTKrcJHMOB6km"
    "HQiyCoo2aPkojZWccezztAsxPHUNbUc71hRWGRlzLhZv5CSyxJYFUR0bqoWBcbBVdhDiqKsWtKRLynXmT9gMSZEPJtZnjXriokeQ"
    "GbbugqvRLDvEiwwvJjaLEoswoURiaygh87U+2DaWI6CHrpGBA0oirSzOy3WkZLNsnw1M8sCoa+gFkN26CXOYZfMIwe7fC7zahFm8"
    "QK4nBB3PDuf2/XD+yc7TsDI0FJqzyW30i4h6X2oP4vvEQXpW1wpVN1YqBMOHgeFbBSYtz3NvzBvq0mpHShMebOZtBgj6yOYzxvCk"
    "dovP9g6PIqAdzMAc4UBw/AkA0C8ZBYRl/sVj42Ds4qgstuXEUUvolcCJa/SZifN+J1z/MCS5a+M31UIU7uCDL3xRGy05TWAYYU7V"
    "xrMLs0SQfLY8Oi02eLnh7+zOX9xNABR/v8rBpbxVjRVHOxLRewzYYlNF4ASJPtKYOYBYNUXXST5P2iFnYLU5ihSX3br5wmaZLp9J"
    "ddgIc1V1tOONGE3ROV4KvayqJAbIJDMqltq4rrCIIms3v4J12yw0GKlaOclNxc92GMse6Wk7LNcFh5mSaM7xZh3HbpfvIjmOO7RO"
    "dOGGBY54GXfKEmp/qdnbaxliO6mEE8yp6H6e0X3EWbS4AjxXmBeMYcTA5C2roISsTbvuQoA7MFjvsLVlUayHA78ou/Kk8o3OzoV3"
    "ZCeu9VDlz5dSeVEEZU5qFJCpAzuIZfR7cHICtRfRhb7TheMBradKxnmcDAVE/Vc+0i+7DiFwcTG21vOtWCgbcaHmBtkbITuSuhLQ"
    "A0IPsY+OaAjWuBPaklinIpRfBi93Nns7ZWmJZeMI4huLDf6r7CVh8K8MXbcnRiA2SKV5kbsRwOYGw54NkI82ZMmxngZLTpt+zkVi"
    "uOpw0FzIWTjjXUdC28OkBOFbxHSmbiw2j1i96Nu2qBeXY3rVdOyOsx0BZ10U1z4NjhQgj3euYFh4fXfQqDEb3BTd2sXA0UZEwslD"
    "a5alLdMxkTeZtZlpFOwY3Fktho1S0K1dcogaC60hpo0LC5CCzi9XJ031MDXjJtSmC3SjY0qWVbE5tapsiwU9AiTutJMwaFx69pag"
    "fQtbaiqgVvQMKgXBjQcpxmkSFL5xaqEwiIA0r/w2epxJJB0sBt5APSIDVWFLgfCcnJsG6Cd24vohu7q49oT9eK3iDKHMOEciwTH0"
    "qgtJFvFlrM9Bai5yQiLkOxQjzLagWydQu6oRnQtb6xWwYMw359avxhBnHZ7El9Fts4WImUiy/0NiuEZ+Ei8JUwE+kT9lwbWNRwNQ"
    "ff2b/wUurIgkOdtRadRujEQYNmw3ArZrGzGQjWvYdZ+OHniDkFTCrDIhKeRP+FUTQzyL2aQGoXpNt9ANXcdRS7JO2Ql+KxF64jMy"
    "mJky8G1hhblwOnAxF7l0TzHejtpQM4Als+Lpy08r8qatJ/nyLNQRq6QYAvIkD3VcuLtADFzQT4axxFjRsdLsw3XIK/W435FfsW1k"
    "zhqGkOEin0pLfIRbuGrgT+c8JhoqrRBzbXEFVp3LMzi782Dr08/vZWcizH0w+/Tz7M3ZXat6W7DjKGFhsJCoS52qOMSkPCd8ADtW"
    "jgkfYlEpZV989ASpdodZ/iiY1eg+xhrfjetkWcFEv1KeXqbR+40PlQbo7uxURcLVXRqxW/AtySw2gXTDRGPTmOdSjwUTFonvdxqn"
    "lwB/AO9isrIBVknClQEGumRmUwbaCdjUKQiXFlNcNVbVn3LtBYZLNdNWgWPLv5IQJ4chFwCQIBpkOG5NrTI6JmEz3xBUFNLxK/n1"
    "4X4X5gziHUO244V9caXXybWvFdS4O3FIp2auF6DwkNEpMYmHt4k8TXN2JsPgXgXb6mKUumA2bMxcN0etwYMCrfko/3HKs6mdSa/D"
    "YOoV4Pr1q+aJQPw1uw9DusbRLS0MftcuZt/0WGQma18xoe7O+WHm1WBJ8gYQnUdauW85rvHLfSyAABHj+wmytBUuo0hXtBfy4KE6"
    "GgUHy0ZfOLvBTDMWDLIc6NcA5Wq6tQnFMGV+ITI1uJJLQI9YtFfbXczFZe141w/1ijPJYRzwf/g67S8rZSEx1kv+MRhFHEDsAozz"
    "jpATl3Ij+vdKfjz1xFRKI1W55FJ4HvrhxuAzqkhQwqTiB/yh3GoISsXhE0SYgeSumoCImwAQ2gcPIwNL86TE4XlImZpAfmm/lYEa"
    "gMrKhnw+tsHhQEeoYhlHh+AFDkkmCclgPQIw3UI7Dh6GjItIfK7enl9eB9hAaxYTtEYx4B20d2AJNGRI/HNbZCL87uCR8AOjr+mh"
    "WC4ggFow2uKMsZZW9AQyZlh3CcvHEU3rS4lpGg63CBDBnhdmoaTIzC5WVDGoyPbpj14E2/zdwiYje3pWDQrV5nhuz2i8x/i5tOEn"
    "GcPw02G3PqtKSaCEb+vNJ49fotGm3fRn/c3viWN53OZdWcVqzAV16/zm7yW4FT7yyXlS9JtuEdp6f/7JDtSp/+u//O4f/8e//8f/"
    "/v3//A//zsrU3y2O77RBnPpumAfI5sUCKx2rsBi2gvG5di4Ba2fZXwuL30AQizcPPxti3iNtOpBpRGAv38+MAPoIsC5GO0F0b8RD"
    "iv4Tk0TVy6EsDRqIL2lsQXyJ8iJ5rcjfATzcdKiCSGzN4g2kT8qSeUEL2xAQohRh9Iwls3usEa74Yb0JidMSkPu3qUcjyANRpCDo"
    "jwolY9mncpm1LqNXLPx5LBRRRFL6mb8HhRVC4b1/KYXr1sdqXCX1He9eBv8ZjVwGyTtnobQ1vZ8wUpAQ/ci+gIeAJKlxIf90rZML"
    "DsO85Qq01EF3PEG6ayN6MBCrdm+Cda1jF9htXPy5xDEUwt62RDa+EImFeGJ1xulh2yq+oDyn/KIplxBmrAuWZK6J3VhvuofOxzpf"
    "00dCYV5g3BzmsIoGbKyfcoYI4TtXppAeRW6ZiPjCoq6Wjy5cZtZ+q9UqRzzWVZtyqcQjYoqEmE038+d5lPyKrEX8goP8CTyTz63l"
    "ZWpBp38n+pyh93l9uehPysXdmW5fiOqiWKGeuEFaOpYlh/GdBPFLl/3pd39gKSP+D3JGWKWGmiEuMkIBdFGZxqTNcqvVUdJq3XyW"
    "B0stNUXeVvtYPjLm8iKGgc0HIs9wYyfB7JZVeipo2lJRISdLTO1WQ81FVEdumw9mPLQhLWWAV4thYfM7MRk67VuW5jEeuVxbs+xl"
    "0YgJRTjndvXKhkwZWIhbnGBg9IozImclenE9M3Rj9d8bu7w/ZA6SyAp8ZyvhOzkoCCO8PRQ9gA9hfeiaH4LZO/XQIkE7AKtjyShC"
    "X3zGxmGZksMmUV6rkgb5p9/9x6Pjg/3j7HB/nnFCm+zf+pAKf/rdf5plu2mYZxfdQgODlxu/CAw4PTDzSOUBaPLNTp/gW7eO6Kf3"
    "H0yMam4+4yHhR57eEHe8iL1xARXuSpjq3EYm8Q7yjQucAM/ykBfCG182mvNE6JJWeMgBpDAfzlDAkemPZKrw7UyiMgh6cTCpbJ7K"
    "hDKLzlmK5N8WNApOj1jDJmpwMRMY52GkM+NlOI2FicA6CQGPQmwahnDmg1SOEJf2qZB2WxX2KgfFgnacMPK86QpvhZ+kx/PJMlXj"
    "ajrETVviumY/CafnKWHom32mJF8UT+Es9xo6er68yFk9I19GIIZ9yPiorIMm2CQiU25U6aBZwkaCHbmNmBQkigiJk7kFLbPc1LTS"
    "tZG8LUbwVdB6y5ZzcwjbLh1zy9KMGGQnB8cqm7EpIgYJoGBbOHbmfR5tBzQkltkMEO7vR6OB/fnPxPiDvh2VFaIivbpcF06FUqjm"
    "fXCST3JNmCODP5Uw0770WQx2MV7GZIzuNusySYaK/H5NnfJ2G3G3Ak1RNiUenF5jwtjGsTP1cLxzeS7teJjsTlBC3nXgb4rLQEhf"
    "n0Ieyoa9UICBB+E/BuCM1X1bvM4FA42t7CGVl0+3dYAc7GKN8Loq6rON5Ly1b5l8+4jK3brQwOOhLn+6reoqf/f6AsZFBF8uQvXn"
    "+bssfp5uIq9f0zEMVZ7m2tUWTme56ldTFai7qQr5u0EFOanO2JktZE6ady6wiR6bwhJKxGMI+p+kogDjoCfLvzTunIat3MrWg63i"
    "YY1WAQ/URf7aHpV3VdP2lpplnwrmWhL63BWIVqYSfFCwcaE7KAGfGdfP7KBEE0mpSvduDKgfwxBGpQ/Nk9/SyVWkxF3g/M01MeD5"
    "QLLwN9db+dlfXv0EqhWEWMASVRJqiH6wFN2KNJ7004JuB/c9iTwLDb0vPGvUpe3Lptr4guittZO3bXFGtKqxCIMMwJ6kHDpXP+A4"
    "cHRovKmIa4Sx1kUTy4MqsbrwHamD8i6SnkLyQf9nyFTZEJotSvYGZtfegr6whuj85luJ0K0leim5EoliwF574Odu/nMXffkh3AiB"
    "rJ81XxeDoksiUEUrxS9o81z88Tq/iMm0ipu/u/mvhNdLLwYARGfWeo+bk7LOO/0czWP2VozyTZtbDTUk2MWPm++RuTxUM4QHSnzd"
    "d6IKRkEIaizUblF2OZacCHtNI/t/GwXjWOWujZO2bLPYEnrsuyjQfQ70OCtqV8bZaKmH0/Kdbs92LNTNC8XidJ4v0y10FepmXnei"
    "xL4SQnmdvYjiOho4bDjWtNVFT9QHTpL0NBZv4TzzuZNrvLchYUjQbRa70shZ+yULfXI2QeU1OpGNyYjJWebSJz3pz5oeSCPqiCjC"
    "3a0vSuB+lg/TWxNZauNuv3CRfGCnRKjYEpahZg2UclfxNvyAHOe8lXU9VOGEWjd/Rz/omZJd3HxfL/qqScab0YGHRc8iXxG7nuUn"
    "uet0K/umh7xldXLz3SqDqTYtGPeMFEJUNrMxR1S8fdDbZvReDAabIdAThlYMRj0aENFKLDg+6mgaHmI4MFl18/swqLfnIRrQIdFP"
    "AC7RPlVnOwIDeizpmF941mZBvEzWr6Svdd7CrJ52dn3zLb32ecs1Pl8hu92cFoj4QFvaaQnxMavs66Lc8II3CyBxa01uZYRiqGfj"
    "LvyyLST3A20JoWsYMlX5BvHFqTPQCKL70ELRpUBAVXlGJ4SeBE+KDr9Z2WZjjb3QX1/nNW15MI1aNqmtE9uBFrbIBedkBo5soVM9"
    "5MwZ50asDJm22KQe1jAt/ybqSseeKgO68HTIjYgANzff4dVSnt18+0mVx3ztShX3B0cspmCI5vZXHH/0GlD3FW4AZlb2ERBEfdCk"
    "XpvR/7RoifUAsHEgSBrj1mtU0bumonL38ZWDIuZQKyYbwzhGJCivyvfY6O1MU3rHdO2cnxz0WKHaQZH6SRdMeEaUy2L5RXhx2B0R"
    "OBtDPk4Uz75HBxjpaVNm66brbr6/KOjlzo4Uwx5HU4AdodjjL9qmxgx0ET2AZa3Ec8ZR7rMGlAn4R+cWkQxpjYCxU7vgz8PUhqAb"
    "1bWFoWDRtC0ciCHdlnqiPGTq3sIoKF7nikl5EgQgVLK8SlLRAW3D5+Qi5wMUmmNU6MDx+KbdpOjgtIxstFtyYEfz95jVuKJF09pV"
    "SeQ8NKrSrzDgwTX2I1N1S6RW2i84bo7f6CKzZeuYLC6FjAmmE4Z1jeR5EdIwwUd+GKXr5ritgojwhUOceF8DZ5kpOOvbnHlEV/VE"
    "roi9+rRpV7hvCsjA6Zbi5eyIsYiS7JXRyQxP2BLXDn17xWakINBrkG53Y/Gw+eILh+ybvpylA+g030Fd1Od0ryTdh66XBfRTcezx"
    "aIa533I8ffcTtUPvtx3upi1B65fjVsS3K3TPw88VSJY/hTyxyzjMijsF16wtz7IdIj90+xefSFLBuPRuvQMZnA3aV2uSeaLf4T5K"
    "3t2mdx0pk5hLPJXb9nbcl8aEu23efKlyM0hL3jbdsJ6uwvMe/Hd20ncLWuOecGW1LkDXtJpwJvxYbbD2cfnjebXwth9Ll7M7Spfv"
    "IhAhmCx/vKqSzkt8/TwEb0BNLoVpAM/cxSti5vKuh9RIT8OM06KDWEZDqFnpHZK2W7C+gwYRwmHAVeG/jTAo4KW+bcsGS/TT+uYP"
    "q6LVh2XagMu8SdNqHaoaXMhSaCDrBpYTPuV9XlWaPFDTFvGyL2AO4KCm7eFcG89dUIZXdl1prdK3FGzvnub00lrgkZK2JCnQk3ZO"
    "A6hviQ1TQ/KIs7ZfT64BPSODx86Llm6CSai8w2W9Q7OG954fEp5pbFqwmCosWxN7VpzlA6y2gv3r5WQVZ2Ep+Ii430QhL0AF/N6J"
    "KJAtUSCh5QBHNz+8K1f5GCrEo+RXRN55fjCti9sTmE87PEvaIZQKWSf36WDmQ0yx2KlaeDpCfMlkr5EmdUO2MyHxIzBnSxtA+SCM"
    "IB3uBcjVGAkFOKBXAD2dwjMghWX4VKSgkTarEYzrPMBNdM6woe8AeXvfPqNkAF8XXSMOGhM1NPJPCtx3crcnkGxq+3oED11+2aLO"
    "qAaivIwq3PyhIqI4Cb+2DPdh6Rin6PMiZ7kV5z45qURwdtgWmyZ+JiYQl8FOWb93wG/PS27yMRHohYOWdJVfFsSnVOfuO3HIEvN1"
    "n+6M+mvX0mVRSTCj+SqH/sj3XLDJEbXGZjNhnD1j7Pu+ih/XfbtmAv+yeeeaWEt2xJdN5yfaSkDB5/CeXcXvK3okl3zv0f/4huMk"
    "eJoGrQ6PvKTQPb8iwbJDtu9s0fFi1qMjxSp0ej4RyGEgOEzgvxzT5iG8JAbkoKph9NS94EhS6EYfANQXugG/jEdrNG6SAoth+vY6"
    "HAOWs3FuY9G3asxF5jssgbaUhwys1DDyBoUCZ+RM7PcmP+tiGV3WhY705m8xViTcpu6JD+PBudbfigASgqLsJC8ZK6RM3Lh/Q0xn"
    "kV3k78s8dh1iHSQ1t4UHgg7rE3YUxL189U0clm7IvqzHS12L0WYw7HqxUTgNjzFeuqY+1BN7EA8qT5V93vwaQkS/V8fHyJLZxCv2"
    "4IhwvMdsEYudlUVLIYiaPA0OAnkbyM8IwO5PPPPyALZNLHK7wtKI9EZkmXR70Vq37m2xZPldePKF1tlp4JUKsY8KlnadN18XKcD8"
    "rHHFKhtfpjAvqmUKw9cp8hibsK4qVidtwduD0HCXHbVR5l3ajE7z5v8GUYWHNb1ZWQyNWipcCjWSlMHKG1juWpMkze2RGthwOw4M"
    "xieK+RY8olq5LtZgb0/yKq9v/i40KH46vEl+HblM8wUgO2tr33xmWx5bKOnrWPaEOOdBseWpLRfIi2Bc2MQWMrT5iDzHSoEXWTW8"
    "TnEjGYy5kicKq6zJMpcnQFxWBoWkP0j460R4ISsbSeq+klP+TieVbwKlOnVcwi2cjTO3kEt19oAhQqcMHZdx7AjFAQHYEkQCCt2b"
    "Ze6BePOdE41B8sDSEebWYlN79QVBiF/XGd2ckM7qUwEzP5Mx5AvgGv19TyWT9+/dmyHtjrUlbIhDE63oSYgDdC8OFbEYYLoSAq3T"
    "jcDVzfeEEctYi9dSxa1dAUHUAlRnU1QPs3vyGnTPTCatg6GP1iHvRnPY4hWgN99w9oSQpsgNSFkT1bdyeMJZJDv6OShFlgdbkIPB"
    "d/MQxs4J6jbJyy4eWoeHD2mc5Tu9QmT2LMG++b1Kkm3QkjI5jNmV7KgJMWfuTKQXCURcNW2kEGFzjjTERlpxJ10U72dJ9vqJA5yU"
    "m4bidiD8Z1C6qgP6ZTnfN+zhurvJ17kQ5iJ7wFeNRQl3gC6VLc29SsiJA7PUHax3GY3sXWluRxFn+aM+4WJict7yi2ayGzZnHp8U"
    "COaai3GvMLVKAFPK5KA4QMUucQDVOc7FVOcAU9x7WaybruQrBuo01zdIE8uAWlZ94CorWiI5rWjWnJg5Icwzn4s+WH/eKoCEiCvU"
    "hYaSaDRTKdVBWi74uHFhCVgKska6eZrpUq4tf+VXbjPYls/igO4mAw6qPtHb0XjuC/ugTc2yOXIVEKNh2p/OCaMTSXIqlqPDQ43x"
    "AcWFqt3MxoNSzvLHhqU8jWP0/4WG1t06Ng2HMuwFotqP6ipo/IaSOt6ejMnvojgpfM/63obQC3LeCfQN8qodfiolXw9UEiKRvyPF"
    "CUKLSHJwZyx8C6IIDJASH6aVM5A2uCxbMaVXYxA7Qsx7mlQsjCt/J6+r/VxkivIY1+KqqelG6pel5NY9hqp0ffMDtNS84a7Tou5K"
    "zs7zBL+W+dJTm+b9e0n+HM8plu+kXLjOTiQXiwchJrPoXC/BG/UQrOD0BjD7+VUKmN6/EZb4hY1Mn+Hoz4UIRdJyJUdfUmUiRI0w"
    "otO9e6HImMXwKyuqOWV3GhadOqSY5p4D9WavmPkFc3AOSU4GZj5h/TUSFLoE97nql00f8L/GJwiiC2h8lp60rdvmhE7jTKOWsHCF"
    "eM8z4sR+aMtmDLhpmuf9QsIQKWuo6zVaXKui/p9ALuZ6mdd4cO/BLz65f/+T+79wdLZtVoxg8ZOYURFbmFxtMbvVxGXV12wEnewP"
    "GDcVnYXBxZh3N99dlPGpcf+xJh2+Mmb7Wo0lcnnomSZFzrBYTgAFj+8/zIwVwsV0mr+nCnhvqxnIzOViHb9QlGfI7jCPcddTskfZ"
    "LjXZ5SW6Ea0As8oXzeLm92qX0bKJQJDSJn0NeCLcs54YWs9Jj9D4KJVa8QwX54WwttZsX1ciafqnLxT0HB9aKLbLgD1G+2jUoXCW"
    "/NzLWNygfbIrerHJyypkElIVUCm2WjgK8ibC/Z+MECzBLNaXyKVBeBTrj0GcCMnA/isT4DCUl5orQCRMGZZcxJb04+fAzFy4X63g"
    "Yh4TPja8P5iEAHpKYxVy9Th2qqMOTDK/3SQpSqHbzBrdfL1mTSNnPKOluMrPmmv3nY0KVEeVO6M7te6ogvvE44HdRyWZZZR3jUpR"
    "lFSpmChI4oKSyhQNTR8sdwY6guVEnnW2jNPhfFk4Tt4yedyGCIRTi6q/+X453v3UBJNNf6igOvfbCmk0G2PiGlsU9PzPlm5P8o3u"
    "ei4xIvmhIjsYgXwE61vKFLtGSGKCBxH5xO/eJNJB55fd/KzRriAfug/pzwSA9hfETKXvlCP8iKz85u/cUVCZwnHHHAboEhuHRAAV"
    "bu5uoL0lrNK0LVqK2CzuafS86Fbpzeu6OXTh5pvJRSXOwsI8x2IwsKub72g6Wx88e7zqGo89EZGggYURxKU/wZ9bK1vMzeDIwWfw"
    "LN/OrsRo+jrFmkNLgKBits7TDVNTu1stJs8KubV2Ir650vEJc4Wa7OcVCyxzeTeDiRi1oim29osLtqR0JS5tkTQzBLA8Yzu0cIyU"
    "4lNnCvldr36RomD+6hIQTBrBjsCTjARcZTVdh2fDogbmWTO2dZYiqmfJjuiCKSBxi+bOCUgIyJWC8W7dYokh9aettpMyc6gxmofz"
    "05gqFHkbNmU4CVKx6zlDBQrowAl55njTJSgoffpLut3gqspynC16K/1Qlfw5yLQIusMTp761J0sXzdFk58+P3DfmuxGT79kr95VY"
    "ViiX472Q6ZcJmKNzC3Y9hAiZ0hmPxCjVFUMV8AKamaueOPdrn2fJg+AdNlFESLMbRxlu//E4NazdgTwGE1PvCZCDBGbQJy6sKIHD"
    "qzJcQ2mD4nbGBxicauAH/WZ0EhuC50/UUKwqNei8RAbMN215gmut6dKk38e0Xl6W1q84rCLdtk56qSuh1rfC97VpO3NGiJ9lKUpQ"
    "wbONfU/xgop230nZrXgxSPrb3rZCKNSJGKQggoNiYbsmU3xVMl8cpPjNFMLUzeapcvwmPQeDUNRsO62UbACrh/awYdN1umZwvop3"
    "xlHQqubuVZfunywT71PZejrvgYLNiMF5Ey5RicnuWzJT30K/aUwkHCbBxonRNjMucGqcKJZeE6abLDlDpNMF219Fk9m+60VeXDfs"
    "9EiPq4HxI3QRbZtLbD5YEX1N7EXNBnhm4mFDp176vNLBH938wNO+KDvxKHCJiul6XcE+bCmWXe45gxepvIvkLJT9jH1IG+dgzvgt"
    "tlggf2tYnscVmSUbPsVAYtmEa8zCgcJsXDGUgiIFjehXCA9hzuHuhAhOhAfaJPqrJ4SFiZ6f0etoqZZirmMxqRPu2cz61dUhbYiD"
    "cX5MQ4Q4TFzMcUgeYx84jWKArssfjdb57HmcfTRqLmaIDi2GbL0fajTYdoY07JvLNTM85bpJ8d0DWJyrGMLozqqhxvbnB3dDHnoJ"
    "dsCHSS1AQ9r4jod6rCfAPrugS0eEN6HHfF3+uriUsN0XrM2YH+4NK0mEZ34LLVmP53GKzl1LDKlPXS+Ncq0ntD7s2aoRmOi7GLUv"
    "No0lrpAE8DjqxHJXwswTpTsvEnzhuGHtBpzOgC8Iedh5IOqX52xztzJHETicIlZARRQwlRvNaMcMgHVPf5W9LGhpfhWnOsvk7dwr"
    "P2ONEqMkAi0VKS3cssJFXasLP97cnTkXJUH50JL49kh8dBol5ArENMGzJRsShrAAWFU2xyvlfS691265MbsQJvNXo62ZZXt4gmIU"
    "yNGRZ3A1WUILF1uQm0h8TrLaAD+/t8UcfPGuWK2rJrv/ywez+7/4fHZ/9tm97c+gPZyaqg7w9qm6jsNM6S45P+AgfXO/b3QN9B1u"
    "OV1A/rmYQOu+5lArCGsqzUwYxebVQuSc2VW5vt5OqZAoINgyPX+UEs1X8uz/WaaMoifbhSlF99zjSmQ+rnHRIhT4YLks+bUX3NJE"
    "XITADn29yIP0qHOhl3Eyim1WsjiTZt7NKgi90Ge5wlWkxui4IXGu2qAH2UrUZXyNRd8A7F/xLt9Ib6nCuZQmcqpRBTEbzgyeEeIx"
    "Fc3VPXLhGpYZZYOF2ZKpVDmHuoG+RXU0WyyeSdwXYKTNDlMXxfui8/faG4kePbURTQgtnUjlVLlzJ2zJKmwLv+ruMq7qOcENtSnO"
    "WjVRCRc5FcX4M6nriGKTuTqwRl98yYZT4obirLJ56j5HpCdIEtcFHUHnMGeoL/lg2OJD+Q4rqVTw2xBrcxGoqpmNg9iZcYVMDeKY"
    "T9UfNpxK0J6bH5ZE2fjhi/cekI9xJpLqLpilerwPr+zGG2R0N98RMaPzZywNDWQ0dneg/8zTnHEHdt+Gi1u5E3luFwsQKSL5P8Kj"
    "WOVhuEDUl0oYjLmnEGC59hd6tneYLlh4sQ1XJwXja/fFmrm2ajs+GZohfYjjk2Csw43z5UcWkSSvLpptZ2/RyEFf5RqXP9TwPEOT"
    "3rAGNnphmajdX2msJy/corAT62KEZeq7mno7tbi1lykVkdNnW6wukxOXU+zkn3gTF8tJK1VTQ8jpzAehEdOKYwvWWLv7QPW6CVqo"
    "1NMk1PawP/6g2QoPmmGfs4zfmctShU9yOchRWqgFZKM3CuuYCA8uWZkW2ekhUjAIu+eY3tM+usyQzFlZB1auwtzH0a1GxblcGmL6"
    "HgYnOe8yfbW+NkhZmmOEj0t2y9PSIewrPraPJ/Z4UGtFFwC7vl04ozheZiuU2Dt4IbTNwpsASWniR5B8NbsgteOLr3K0/igFFTXu"
    "C3cf+eePHOfIZeDm6XpiZMHtuud+1PTJkxKOmFDOz6yzk74LbtfuvcQIopyHJGSP0OOR6SBKnMbWGfNuErVJnVjpKJ9Q54KRlQmN"
    "mj4Z22GuKoK5bwomu4PBrnMWt4NC/OjAqvyfN5idwcYL85TYd8EoYQUtWleukqqpd8kE1EBccDKBeAAxma+bpXH6gSfDtTWJEAmK"
    "qYsxBiT3nO9S7jsG1ggUwYoyAeZJq4ygXLyBENW8vx6LDbiTawuATdTYEyOdxNogbJksqsquZr4aO9vd6p6njneuBoJF1Zor57ET"
    "8YB5Vc9VXh0RBIjTtoipVjOvnojB6uRD4+4q1RcYqCaWeUHXepdoYGphnKcViuDaiFGPAnRrDWboKo+Mh5F6J07Xw53D9OHq/Do7"
    "R1Io5fZCKReOP6cqF7NAjD4LKWDUaC+CimYI4K5DAeo81FADlV0t027UyH+ZOkeE8g+ooaKeOe6Z00UNezJt1Hzj9FFZEiQmwCLT"
    "zFpBD/OW4IBxYck8qES4d0iS6JxDe1DDvDw+ONg7+EKfNoHGDqAOX+4ezl/uiqQFx2IS6mh/b0fa+hDU4fz4iFsSMjkGeLp3sHf0"
    "TFhflUVPAM339nefsAapOmcdnujK7YTsKNFZpgbvAoToOk9kE38jz7DBMRCXiKiB53iLefdGWIKznsO8DN/XA2gJnrSvt+KYlXaw"
    "Dfu1MxnK2SCzPnfNifFDaEvMPINJRACDWtaSapvzQ0IaEjBzxTH17dj0Q9ezeUz4GzWbLHMezNdgvDpzCs7pXpOttWkiXs+x+OPc"
    "Gr8ngI+PA1/F8MsJMJK0N6wc9Ixn16G0r/UgPym6U8RbCSUjjWpqKWxWGZvH1v6Be/83SQfafP6+aJNhRdRIPutNaHenXGc6YaG+"
    "R1H3o+smrOweQi9w4PqlkCRlaG1GjZiD7BrzFa8t34nASY7Ax1P6pjB36y/Ov3QjCJDsQyHtpbYIU80ycEhJtmNqBq9PV5eDO/cy"
    "TthYdndH53AW2qMT+1jWehDXCSxJcdaXfZDMtBKfqIpHzHvxj10IYLRFD0GNI5TjyUwHst/2fR/L/n9E35gawsyxpOTP7Pht3gW8"
    "fNqUY7QkgHqAuqe3wM2XS+TRELt5guFRXpTDxjxYaG8Ma76sMZoo3EN7kVVtzBDBK/X6lvnkAf8eg3BFH5TbkcAS9Q059zoSemdl"
    "GltkIJwSbYBYUXmj2U3UzJKTHrJP6XEfIdSjFFweL2q0yHJoIk5erAChqCxikVCg7aQdTU82H5iFsd0hy76mLo0w3SW/VyKtDkYh"
    "S5bwuqO0tA1+MjEkD0YkLIUMdEyzkHPqdJNN0XV6831jHq+hePbpvXA70bg/vRcc/TzQLxOgX04DXcpzh10D8nrUUc4KJERAYBPg"
    "wWg6TWz/ZGDhFGW9jBIhQ0HRiWviRhw0JcF6WVXs6DkfxrMyHp/xWQPEhPAuItPmACtlKnX2sXWki8nINklffgf0HRsNi8253aWJ"
    "7wbC7jBhl2VeYib03WbEZtmoJj15uUyChad+O0UHglAaFdLRLDZz3iL1uYWtgmzWuENIi/6qgV3Rk8bMiMX2dNPmJ2AUR3JF3WZE"
    "wGRhEZ1u2ryqKF1pX7PR4DIm6YbnhylRhzA+MfcYjtO1HsVUii8LWhsfkypOxgX2WrJlxgqpoc89hvNOHUyb+A5AbjXxDafhNpvE"
    "BEDtCge48xGWhXEFGrTThfenU1rYFZSaF4cmIr4jIKoOlw3yBmOFBaQll86D5cbNd0Qf6EIqTdh2OphEbQ1x7mdWCa8aBBXumpOW"
    "jY02MKVTCTZbfjdxTCsXmOW5xWORlrsxkK4jPODBtyJSqIvhMgCOO+zTHI9g3BaPGxtIRONS8zVlhC9Ox1p70WvwEV35Zm1eE4Op"
    "dY3EGFnQSavdAa6bIykZCEtETJQruKNl0XT832T3p7bWJAC/va1Uh/5bPYMJ+vFRf3w5POyM8qPVZWD14NKTKs4EdfFOLtpUMRck"
    "SMXKh7qUxjjIsORGb6i3aP0RYjoEIO3yqIeqnINGrfv2LI8XRj24FUbBLMFfKwFM6N9yqIBw5JgfoxzDAv8PaPWs69drMXi0YQ0A"
    "MEQWTvFQQabpKmKWDNGn3ucD8EVelSet+YHvyF9m9qpXTHBqOk7f52yw1kkggIWrucWRJOWpqIccZojiiaEGFqyxDorWLWPKV+EC"
    "uvl+UTaDpVFqcjzBDtoqzz5dnabiuPSyGbR41LCdZCrsSvaUWLjzfDW5i2b6NWxTuRWoaJipZpsy3ybeuRLMgQOEJRpa11gj8ST2"
    "BjbdbBjuV8kTdQwgEnUPdSuN0SQinKW6Y1+thbdzSi4oYRgOlGYmvIIncs9Ckz/mNzM1IPh4qKPXk3yTJ9/XKjXdG1+yKJ4I3DXg"
    "qwCVuAamJbp+T6aWFwCe30qv9+lBncbYmiIjiwISWE7r24sdO+Jt0rTei2XlL5Di3drsndmAR5UOO0dfaoZbE71ZpLskHDUnUSfe"
    "R33/NGpj15+p+JuG1xb0QGSn0kyd7nLL/Mue3s4n28zVtZyTukDC0JdioOissWRFDCiojEIaKnphdmLr4r3JmiQu4y3RQF00zCKN"
    "K3wu7sbBUHKC7NKI4PbzhQ5dYmU0yE9z+xTKAP6iC0GReVxqva+LKZE8+a0w3Z6NIEbNeakReEecPBJC5+3GYcVJo6E2Wa1KRKqx"
    "EArSRFC0mD4kZf85DfTbo03DiDC/KEVAncBld+QRfjdWCNFruHypB7hjW72oUAvcBTF7HPllqbRdqhX6rpVv34Q4Qk1M0j52qHTf"
    "D4iXUVQUuwyxYjLfiXj/h/iK1EcZ8WpdLEuiDKuwVoN+d2vLoWyhRtgpFRE/RCgR2uUbDAMctLAzZUigrJYtXTz0o3oTdgQBpz5Q"
    "+2BSY/gR3T4XgvMzycLH3vkKoFmUo3O090txACZICJ53aXA3NvAAAtsl1mwn9UXmGKSTaRmdexW9Hzb8K480R0HoMHDw5NVJY5Wr"
    "/FL0SxMhqGP5cNye+kgQ7ceBl7QhyyofMwda9bUh5+Yti5k5BDp/T3uyMMGiftU43gXioBIvsCUGYlovuyBWWOBgsMLYxnRkVXRB"
    "qsRxw4szGEqVnUt/jgRffD2UJ6WnWlpkw1ASrvJLDVEe5po5HxQhqatBF0cW5n4e12jYkxqXE0BsbjuS4xTcItN0cDhnDqHT6A4h"
    "JFBWmLnQwLInjK29tDjZEqKqG0SbCjC6DE9KVQG788LhUNFPa2SK/hYqlvuwTPI8BWkrOyaAPRWocSckr1oFlDFn8irRELwRtNmc"
    "bbFxVFdUPjoWv5RxfhZs6PSEbbf6VUwn5Oy4TIoaYnPNsmMHueCXMwuxNPcQMkUdzrXgcP7JztOwhvklds1kePpFdAe8XHhKWAQw"
    "7vxqpXmm4aBcQHfJ1IvD9ClguOhgMPY8T8z8Q23amYSCucRJ5lULMPoqRmohiZO3X362d3gUAcPxDi2ZRWJu7FC+XMqAosuEf4Da"
    "uDaSMa4dIIsP0yVhW2JkfbEq8TTkTsdPAv9avWvTSrVdN7+vF+U0GwC4F7WnWcAupleLH6lLKHlWauRGvSqhBGlFyHnnL+4mcHbX"
    "X0Dp803U0Eo0PacNkgdJMzxIGw71wkaHbHIjLuhqb8Yh4WwMhIVheyVn19FGuJ25KRScB1lYBTXlSDI/WLAZGx6yV0jkk7g027Ae"
    "7GNGNhOjZZxWfGiMSFwwmypyyC+Rw2S/ytAdMrwdlrTtiNsnKRkiHzCZ3EWKRHGR7KHTZ4xfr3lCQY2Nt9y2sYnzplVnCX4ciyHf"
    "5uY7Vq4YEy/6yydCWFDLvF7gbRdDW4LPXQYb4ltsU7YdJAzr5IxIcj43Idgowp7XQ58rB62uqg7cbs3yoghKyBeuteIdsXmpACh6"
    "Y7Hy6k531/H5d7pwxqD+V02NDVP9kUZuZoglk3Uhxj3cTcbGA75NPS17HLmE5oNvGftFcXo9pA9s3jObHn0zXGJZIpNbQk7jyDuz"
    "bEeG2wvhmzWwPtO8db5sOdyVILklBfkVZzL9VcxjOh5KY1ZVnL1Doq20yYhmA2x9Vi6XHE4w2QpmLTnEQgO79hRRQ7QPIYxeh4LJ"
    "WQ+3JTsKZSmx406mYCXd9uLSAS/wSh/sbeTjqIKEnxAdwBP32rxzBVvo67uDps3WrrOWL25+TxSs6VS/0HkGOdERZb51iUe2aopl"
    "bkH/85TqBBcE38RuYrHJrOEGdoc4wzffE+tbNQ+Dcpuu1k1hw0qWWg9AfHwHPSWSPlnYj4Zzy6owSFTCWHgJp+H1tKkuTfgzcGZV"
    "ARFXZw6UliHGqTTDiAJuzceb63GMjTmTYenAO06LYsNfhnckEiuKYPNL+sXP5eDHcnVx7e+S47VKnA5pSXvGtCiVUwkYOJxCUlXN"
    "8fzjFqkdcwVB/KyaKd02vw6d1jm8oM9ClB6mzvQBlsz55txGE9OIzn2kMpc3xJbOZ08Da2xZ3pSpRv5Ppw3H60sD+7h2Hw3gVTAT"
    "kgXR9UEYnt8ykll2lJet5m9Zah8IvzPoZZb2kg7IwSkYMgsiVGJwvZAHDzKVbFSpgbWWEOivO3F1H0TEx06vxuE/UK2sX0sM2HBz"
    "1pKnwb+XzVY9t1rTgfy5aDpbABdJLLfXQ18Ni9fGMEu8BkzicPP/IMlhGKuaFR3haWChTvBdbAsfs0aNHSZiJB8UD0O7DqwEGIZJ"
    "3+ty6V1TnF2wDn+loVR2YjTP2Mnmdd1ORibjcsKlNn99WhaVhmBYrYnG8ddEthfh88XmdSKb7dhTDSklHsw+/fxedqaKggdbn36e"
    "vTm7a1UnkgyEbCw+2QAD0+a/PtVYzbywScDmGKM1y80CUa0Mw4aFiDnpg+3OsgxSfX5WW0N4Dsoj4W5cvLev62YjUXCYxR7kM/Ic"
    "d8RMdt7Mo3KP20KQi9cfwE8u/wCScvnHYCoDhg36YhB3dow+DP8jqMowFgXKMKmQAO+3tPhBx5AEcuL4WP5EIftCYuh2YIs5sWQ3"
    "tlKNNQyeGZdXmqJikBgoSARLERw43jSYRMWwxqFJaM9kBNzMB7tXdzSz2xRvtu3IVFxc6W137WsF84V5HNGp2eoGKJhD6Mz0OlEn"
    "OcgbXrGw5aRYfdL1xDvCBmLZTKcwmg0bNaf4UasD7W3io5Sd9jW/xOtwk6c7Nryro2mTQfbrV80TgflSvV02EijCrm0f0Iw7aRcz"
    "2tLOYmEWcit4o6KLYpRs6ZHW7FsOefly3/JJdUULo7s2MSghQA2vJlhD3zif0SxfLDSQsWhIUycxgUlqhtULxQj08aKXHSzb5PNe"
    "HeIP1xt1hbWIGbf1hsiUHDj4E/wInyfCEUhByBf6kn4Mx8VmV+jbTRnr3u4IsVE5e+IeaGfJopFmIa5CaIJBLt3xbd1w0nRuGofX"
    "Oghwt/l43vxnvyqCXHE+BB6nFJAvKQ9bMSiWgQ0ysA1G5+FljmMqNQksax1SEU441BbpJkgIIBnrEzbvFrIyXJ+U6AxWJwDTdbbj"
    "4I/Eoo7RdBv5Ei6vA2ggS/kEWVIEeQfTQDAdfGftuj+3+QXVyCFjEgS56wUMMiSZJwcPDUizFZy4WLQL8TIoNJzq2ZZk1ailsTMR"
    "ZimuUquu19AE7Cma12dBx7q3LBtWj/JXy1QgX7OYb9QAcpfJ+eZbpEjBQ5Pflht+azJUIah1VpXduX1bbz55/FIUIJv+rL/5PXFE"
    "j4mNKqtYTd7Q6/zm79ltkT/K8Sr6TbcIbb0//2QHCvz/9V9+94//49//43///n/+h39nZeq560cIASHOZqmzSngUmOx2nkqqBzzz"
    "KZB8E+ZWNFoIByyGzc13chWKIDR59GorWOe35fuZEUXI2ZuxQxJAujfsxnmImJ2qt9WSYXhbfNNYuIcapky/BklaeEpJQMcyVgvX"
    "o1Vlr/3ypGAv6SDQidYwhtQgmHmYEOPN7B5b9efdJxcQa3ch2WLRJmD3pzXtEeCBcEAI/KaPp1j2KR/Avos5OGPZz9l4KBXGJACf"
    "4Z7pWQjRyLsJZff+92vsMzYfZmV6VVzEYJmsFkHS78ZW+v4EkzbLPrR7nhIp/9FKtBgXOVe3wzMrBRNVuVWHd+odT8Tu2tgeDGXW"
    "a3VmiryiSwcK2TPTK3aKb3pJKmrJVdmmirgyg9Q0PuIaXrzPiosSkRK1A3A86wLRC7uHGq5iK8tply80nBRfQ5G101Zs4J9GjPxE"
    "7BqmgnRtTcf0mmXPaHOhS29aL45LnPxBphGW3dyvErs+TeKcbvTPc1Eaeqlpl8ZcU+vwhGM9J6y7PYzZnehLW2Tz+nLRn5SLuzMn"
    "2+x0hzs564uNSL2SyGAjyX0YM2yjTVr7p9/9Idt9Vyx6sHX4I4ht95t8manbfdBRsJJYhH4xwXE8L7WqZ6yrz/LUY02JE5zyts24"
    "PSpunJifXSHqW+ONcdsnqt1NBHbbTkK3ZXLSYmTVxw0sEkX1drgiNGRNvvTJwkMto06lxY/QUKlqXBKSfM6ylwW9hTXnOVMNPevf"
    "9GWnAV0+bPEjbr+c4Tl6/RpFtYJzi+jJaU+CVBUqry6S4A9RQR8iy7+lrIeVPspb5WVl5wcAPrXEYZMmN0rg7LENIBcyUCCsVrD4"
    "NDRLj21C6EdxOmCpIKrRP/3uPx4dH+wfZ4f78+wxEuRl/9ZHv/nT7/7TLHs1zqmQBjBqfIKMlV8ZnsvkWM2RX05lDE1TsR9XzZlI"
    "bxviT+8/mBjmsVP7hmRhtbmLDyjIQBVChykQhrvZGWhb3Mho5QFa75p56KU/tTeU5ghPMbG9vyNZmkUzYzqcZJzZsqAPWXr5W+x3"
    "iEtnQVkdBWdipbhijrv3qx9l1RoAoeV4o2Xus6pEti57MUqKLt5QsppEoXE+N002lRcbVw3fyktlL2+VSm/z/8WWSaT51kR0t2JC"
    "NO1TXSdZgceJzLM7cTSmZkYQ4Ty4a5mGj6MuEY/xmV5WooEMhKTXnA9Cp7L8Ivr8pTBmpWJaPzWe0cU5LyTezXpCCpYkQW0kt3px"
    "wtluLvIKeT38EdaTwOzHjHBU+lJqvJUY5W/FDnMZQZslzZpKq00ImNYOyTEqtR1hJ6JT73zUFdHuY2izkt3BGS2ZOcdx/RlB4MtR"
    "Wb2h69nkCNDRq4JTbDqgeUpo+UnOCoBnMn6NWx2LQkyNyaWl3WVD/0HioDDqDuaTHZ0COYKDA6pOAozCD7OY4a/vmNtJ9m045Lk8"
    "IJ8ne3snj6+1u67Cm+IyUPPXp5A3s5k/Dmv+TsxDqv5dM6jBw+zb4nW+vMhrlU4DPxuxhXAhLia6aQuaC+eTeV0V9ZlEFms4pIFx"
    "HwwS4mr/SCPEM2g+VOJ5JOj2RzWxyt+9hicvdCnlYqoZLr35DsXEP9x8q3mGk9by+jWd38lBNMQX13Qdwfpsi+p/X99SnwbyMfWH"
    "/cv5D/4OiDCxbtTiC0G7QHsaOXOs03QUgaNiJcc86JKnsyjd2Xh82FJ6lOz3Fg33g0tHZIEOyGsTwN4NutkVG/GB6RL3Lc6bntwh"
    "XfFVyYhiF9e40CyR0lsLB0mzLnluOEa8n2WahWcYJ9TkQQNVH9vwSYKncBX5gJnh9p0Y/3wk2/mb663m7C+vfgIdGkLs4DRVrAfD"
    "D5ZJWJEmidgp2tZ/dxHfTV0aC8+ax0HCIdkqtSDxQj2L8kktFkf8X8cPOE2XLLnFS6NOOlEd8xcsCHPfNV/rLjLNg4fH/xogotH4"
    "EBwsAW5ArPw7p9cpS3A6LeKLsUiKJB4N+y9vWDRY+YwhiBbiclJcDkougVitlM4vYVdoxXV+EURzR8WCwxEyixmFLgDpzKB1R1Iy"
    "dvp9aMklFlhcwxmuLJ0xCpfpQYiOGFoQ8g6oL1tJb1JONbAob36oFYgzkbgW+I0S20HHfRdl7s+RDOBrX1RgQw5buojf2fZsx1Ld"
    "vVA+jPHBW+jg62Zed2L3cCWE+ToK/NjIG3FFafx0bOAk3j3MYFdOrGx8u5tkQ73WJeAmkC06b/adBWyEyTbyxliCInVyYIPe/OYP"
    "NXolBrqqLJqcjGo2IVuPY9CgVEXRxr2Ogd4sO13NdrvnYEbl3ehDztGA/Ktgi9gTCXT8PofY4hIAGkqOtzMZOC1shlTdatJSowfI"
    "pEGwbv4+d0HnRGANFrO8+Y4GBLWUPWPL+oKXTV7RPJuIobdPZ9scVfLhJGjUlmgpnc2tw2MxnCux8VXybK+KwgtyeYhvz0NQuT/+"
    "A96d3/SwbmYWSlphVZrBPm6Wl5xuPfBci7agB1PtegVTKtywCNn5uhLTnkvgR3PK8eUxrE4L6JVA2NGzQr6VRLGaHgghc/Pu5nue"
    "gKH2pZtz1sFilPcsGTURLdapEF7C94CXnbaMwwU2Hay2O/6dt7yYcajWCdqkW6u8+bZqzppgw7csUlOAcqOBdcP8L7cMo2jsmKPS"
    "hy0mm7mjc4qBKID8r+lKRs4tdMxWCQ1jrphyBULmBrlFh63bCOd60RecKDHPdF6VBtDsNoHK7g8PbUzeFN1irrpzokHXkohVAQdw"
    "5gYTISWUWNqoXsQxOFIQizkpY51aCKQVfcQkrlx0H1/9qQsQEKq6vetKRgexJUPYSqbNIQcW0WBqh51XAtCgzFwaLpmNmiKKFow2"
    "1tH00CPiaX0s81ghXz6NTooHeORna8jX6CC3k92NJtFd1hDljZ7MVdwlgCgbt492481wDqbsUlyGiY4gQQVehZ0c3Mn9SM/PeGvQ"
    "maxaHFId2GSlxem9IPUSpfECBJjNR6v45HX6/FDFfGqkWoTZNg1ixd5P0hrwQT63vmU3pfykhOMgE+DEFL1Kl8A/SWsi3hMLpHLE"
    "MNLB5fjBGbp1keu1e8EB0vwuX2Y6ab3SlkbuaP8ISwi3ukYSxQmBGLGmP4bOdXPcVkH0GpFGmQBl4E1mG9PESb0TuUf2QMKX/QJx"
    "gDLOeBpu503vpD91sHq8pBNQEf9y2DYnUAPBHZhuLCKutkmaKBGedXSXfU8NdWH8s3QUnWYoYqblcjCAIT7F4xhmHY4koQXhLR9L"
    "391EVddlcpppn1mRWIvt6bgNDuMbfYgDr3V5C6SucFjDGpKNoo57OcvmN39/8y0iGTBLESBtiSPZmw2aThJqiLKtbiygFTGbuMwx"
    "QO0K4n5mOhGttWe53MSOTnSngUTjeqftEnoRxpeiG2AHWZg5VxqPI2lBV2MHx4rHcXLzh45uzaWoNHCJV7F2dCON9G6EQhbJ/WPo"
    "cnZH6fJdDtkf+DIDrQrJUegeVg+pyUL8fpkede6GwBgw1KLtYmrFp2HmadFBLKNh1GzOYBAhAuxBs2I/B6jTcmVCYDG6pcniwdbS"
    "Sv1UpfVCB9JWXKJxMfGPaGmAIauywTCrSB9bB5RXleRH7jTulK5/U2nSYwOctpt0zTx3EWdiQ1YtaWvaRtO19SUDpC2dBljfFNs+"
    "h8xOavs8sRj0Xg1ecC/aZVFPg+XdggUsC2hJ02HhTagiiInCsrWEdoz0rWrD8wBMJ285WXXCZlc+aSyJsJ2QjojVJTYHEic+OhaI"
    "cgCnw3keHiVdwjWm1cHHqi9pJW6ksTVCt5BB+zd9KVZ3KRJZaG8tPh2dDd4lC3Csu7TNOZRHQM5kOwDGczICd2gZwFdj/BTggHcB"
    "9HQKAYErlrVccWUbmjI6s0Mo132AnOieYUPvAfL23n1K7ACeuJIPa2gYtRTYQn4kkGzz/XoED9l0q25vCTxitI7AJR5WMwW/tsiK"
    "BisiBAkPzLIzYNPspNIQjcUZ2/nr57OWZVdftKxb1o9vz0tu8jHSpzhgya79svnafSM2WoKRHyDm79eux0uIHd6yfzxR2KpKei0K"
    "9Y9hLUgYY88Y+76v4sd1365FA37zh5b+cD2sJXnzSwlybY20EkL2OR09QWEtWNGbu+QzWkFQKmdKMDXNwBCfhUlpElc6kDI7a/vx"
    "IBGrmp4hgVH51/OJWDGpDDMB/3JMvAfgkoWYg3SHKRR1DCwVC90MAoCGMmjAY6d2blJg8bDfpvGwWZY1q/vVSdFqwFZhWzgSewAQ"
    "t899umyzKyT8CwVqIg/reOLYN/lZF8voai8sRPHfYrB//G8Zx0qrxczItQ704mgi2UnOWCkFGuI778rsIl/cfB9LYtCTWG1bQra3"
    "2dU33AnLtepiEyrpVuyn6WmH28Cg68VGwTTajiMgOrb6UE/srjuoPEf2CfWLly+L5V5tDxe2f4dJKy15hOK9ldaQnJvXKoUgYvJU"
    "HU+iz0nbjMpDlBV5CCrYtrmjyJUlIlWWuPETji+2cM0JTzdwAedO2HvllQrSj0T+c95cpuXzs8aVmoR+mQK9qJYDIB4DPQCgrBIl"
    "C7/r6bG7acDbSVjOy46auvk+79LmdNYWNRvma0nwGJFVhTqOf5gb34AUBUXdB0nUPIrBqsDP28FgSD5czCt+zVKLjt0KhXf/toNY"
    "1CDFZ4z3zS8ql2lCHE4kb990fHF4oaSvYxkEhINiyeFIzyZ6LNPFFB8iU3vKNcwh6TmWq/WrpTvLUMytPFHQxw10TeI0aD5Mcf2g"
    "gAiKB/dqC+sbaeyxp69cSCdYgr/rsItkOeE7yvFnbFGX6krUuFiGXMYxYRQpBGBLEIyGe28WX5JdEeVaGdFwla7Mknb26gsCWCbS"
    "AFpal7LqTMawyi9ZPk19mNzz/r17M2TCswaFSQlIoxU9UXZg7sGiwhkDTFdCoHW6EZionxwlfkZusfhIsorhcK3bZl02hiAPs3vy"
    "pnQ4I1R3MPSpxQARGc5ki5c6G68AoajFawloCruqTTgt8NW0xLFig+RLkcQoZjJOv+sSHBUmPZOEjPGB6M+yw82HRFO++zqHCgZz"
    "1szD/OpWIbUN/a9Z76gjd993zAmnv/mWAzU77iKBievHjRQixM6zB/ecuge6CTWexWI07eBgR+YmFr8KgpdbYPBf8OaRdR2SNYUk"
    "QrEW2/lgOv+A7yRLQeHgnkbLwd9AMeMJjAOzJFVshT0e2rvSvNki+vJHffgpXM2BvRyG98WF74hDe41Pjd/1QRWkd0l7TSiWg+LA"
    "MbsVB5Cop6YJIEXAl1FVgpSMaedmkMhXHLOwonfZ0NVXtPmmh0rociTCTsm3Q426CQa+U3JOkamFit1DU4jp8rmWnBXo02iSbfaT"
    "GjmiS8WHtvTn9Cy2+Mq7yVCjNjIoFgN7zkR5lu17Ibcd3loVXKdTe0MLBNrNqUzr2ENeVTffz8bDUk70Rwc2eu7/S45NVLij0Wng"
    "It+PyIU/rjenfRRZoN8gxiLIK06K2qOMPNRFppZqByJQkIXt6DMr+X4QhCqS/yESoiD58GxI2oQEcxqKSOw4pC2yzNtcKxEmQQ9W"
    "EEMHsVsYX/5Onmb7nAIxq4Q70eKqqc/KTb8kZpgdL3FEcOIacZ23Xou6Kzkr3RP8WuZLf+Dev68kf1A4sZK4IDtp6NKomPFT4BOx"
    "cR1B6sNeoRLP9ds2hHnXr0aQ6XUdwcu63Mg6MKhEaqlG5cGuErWZWq0/MAYvZBmzJX6VN2neSvXuNzSZZsADmWdfq6PyrC/TC0A9"
    "s+abls6m3xFJp9aJtJuPEaT8bJgVjodoNGDNq2XuRGi8UpofbaA8hl+cwHKWHx9juE3TPO9ZMP0cbKU+WNaTC2111PP4GEYEzDsz"
    "d/Lg3oNffHL//if3f+EIcdushMFfusmzldgzsJXJjWhX6870DdfXOO1poH5wgkE4F0ZpgTO/ZIk//x1fMPcfE/eCVq6Mgb8Oxh+F"
    "u9QzZSHZFERx/fj+QzDXHLSt4k2gV3esXBj4zCVij8+cP/6DPYKUAcnuML9y11PBR9kRDIOlP1FZRMMD0WYUqZrESYyTfpnRoj5T"
    "NqqTZe1iJq60d45SjzuVDnpJc4GBUd34hvu6EknXP2sBZ9n8YxYw++M/hJgnj0adC/PKL00RrWsTHPig2ORlFeTNTnsn9o/yFg5x"
    "ctjOMRn3LDYiKQsGSQ30mTcAGSU14H78eF7KqWF5XCeabZ9b4OcuPrzWcfHnRYEm0ePgGVK7TAMGnat7fFR7SRfEkfOTEddnYTZo"
    "V6KSztdr1pnC0kw0Y1f5WXPtStgiIqjZEnNEtVOpgjfNztCEpZIcaWYg2PiSKhVgBfFgULOZRqQ3C6WxIiNNJydpstlwUAf0ZeHf"
    "D5Yx6oOYofKlpQTn0rVNrVNV2LQhJs1vMWTlbKiKyxEehTAKXoZAaQqVbxQRcolCm2a4UCCfW+CWMkW4EdLEwCwqzNDvzmzUAeeX"
    "3fys0Z5YfHWfxVITINphFISp9CoehIXEoygkXrh+V+nGcScCMuARm7tECJW+7m7gdkLFFuNHShHayL3NnpejeEaxn8PbU4dYX3mI"
    "oB+LOX4j3R50x37oOPLCa7aMRFiDsyw5R+pwSMY5Q7aUBvJZJIwnpkD00Onp3M6u6GFN5/c6xaxDy4UTEuV5rFW1vH+SxiSSIc3k"
    "HEg5S8vGx9AVDvJL0t6XaZZLyylJOH/zQ1ricuxJ/SFATLa55kZBwIIBwq5TGklJsBoO9Lidsh0eATvKbBXqiRo8jR3sC/HIGad9"
    "X2xi70i3YsFJV2s2iZGQC8KjJEDPgjPkAFCtFW+3P5Fmpm3ekzLzzlHCKOeKhWHqEUPnA1Qsjq3rT/glIZ+ViEMY0uaX+PCXWV0s"
    "IIgt6anc3fxQlfwxRK8mSDj1QGSqr7jJvpQISyTr+fMj9425fUTYfPbKfSUWuWjlCROEpfypmQA6OrfA/0MIwsPqXKMt75j9riuH"
    "NuMF1EpXPT0XCBXyGmTa0pVGoAMxup4sJ1TajcP1IrjReJbFaU57cyAPVG82PwFx4EEGfeJ6i2JCfeeCapQTbRJqS4cvC2aLA6vp"
    "t6aTkCe8FkQ0k6wfMm04ohJMyFarFZfLY1q7KPEj9g7b2XhZq66EunJytpU2bWPOqPGzLEUOKni2se8phlDR7jspux1D5CUuki0J"
    "Vza9PoDSWQRIQQkHxloCzTHs3vRRBXEbgtTN5qk+L8IrxrnhNxOgepIP2QQJTD6dMuJJcJpLPatNZPFH+yhLxrvVJsTfAwUbGYVz"
    "+yXRq4H410kydd9Gv2lMjB0CCrD+s08le2HFU8vMmTwqJi0zLY8QmvPGw33XCyVS2/CiW8PR4USeRklTlWXVAplr4Z15yREoYA0a"
    "TFpsLtRln1c6myMq5Tv7gtlbosoQr8N0c1uCGqzWTS0mb8mDi6N0xEPSsL+xC3qgOXHEQo3VE+60zhIcuIUV5diwmR6zTe9W9hJ4"
    "cVYM8JG5D8HIWXpyBD/0DTh1JNTdxCLV7yJEgXqNsF7VDV1DtXOPiZ+EupWkLXKw3X9ii0p+zFlL3nzJof3jPwyOLYSUve1FNPjX"
    "4+lR+tGozcPgNeKbNfgfbVntYB/xq6aml8vlmrmlct0kx8GXP04sOulgZndW8P/dnx/cNTjaNrBILCc0O1krI4rNXi5yPuyri0nG"
    "zhp5V9CWh/bW5a8LNsqscsLR+eHesB7rBJy5pKgrwwT4GB62xO0Cv9NmueoTYXrna5YVg+/KqEjcABYbSfNu1ToQBeLoK76mIF7Q"
    "F1V0u4mxIAjNHXfB9RFqgscir4rUnpkdOpR4iC/SIq6Hk6HkKRpCBKK+ZtmvsoNiQ4vyhn6FOc8yebcrVRq0K9I46NtET2fLnN0J"
    "DSjH39ydBfNpM4xP2zJpBFjVNebQgUrBoWhw7c/8gmCVOTqGugjJEOAYYMu/NZjkcK8CuQFn17PNRVfG6tHSXJk/Afn8nqYe+FpS"
    "D9z/5YPZ/V98Prs/++ze9mdQl05N1wZ3+0RDv2GWdAudHxSSfNztHFju/P3ND8NlbGJHDt/7mhaIKtA9Im2ZSXGxDEFsOLBgdlWu"
    "r7ezP/6DzRnGm+UyRZtHKal9JTIHcCmMyJ7QF6YI3h883JZJTmHMqIPpSMt8AP3HMYuc76AJrtoKL0qJ0dbFzzVWEeEf6pBYI2O+"
    "4ua7IIor2RedTssse8Ve93U4Y8q2sT+VVw5KLJrEBhyBakW24dkJ6IuYXmYDed5RyVgjzmmeAfCbjZvbZjJYli3MqArFENQEfRQr"
    "mZpUsST2AYhIjbgMeNn4i/GNxJS/fU806Hy6tNLRHdugsDtLDRtxV1B40ZtXBzo7a/ORo4M4m4jdgguzJBG0g/tI/hAnsG62Jmf2"
    "fe6mRhdJ6tBYuYV0Xot2Dk76zUYiIxvTYiWVyKp3a2KKLgLNNQv8o8SRS8P8skToU3VdDmfVB9CFccpCVAr6sI4tm/lhcqr5KQpX"
    "AeLhnHkKgIvtLDdvCtCQ0QzcGf/4Az64Dey0X7L3qN7P4Z5XBsfHg3yYFYHNod1ybM3gpcYN3BZy08Zlzj8EWq4TNiDbO0xXLjwN"
    "B6uUQvEl/WLNsWOqbZG7b9BrFgNnBEGlDjGNgWxb6MuPNPCNuMYjXIpYnzSqwtPgPMgy38JLMqn8IyyHgYZ3nb3D6orQzV99gjtL"
    "v0TMJftIqop+zuk4zW/SFsvhXplradj+zLy6RlfadF//1Hu8WE5b/ppyRVzTqXIadzStOmEWHOt3H2qgbkxoPvT9CfU98I88oMTa"
    "omca7rg53/Uskzdv3djNUrb61rIEORKYgm1NT2++7wxHsWKEMpesXow8/BiDGIg9qUwxHL4OkhBrN1aqIumd4P1Um1Sai0fBt1MX"
    "+av1tUHKeh0jFGPcRjBMkSgPQV+Va9f1B2qt6OZgt8QLb2kobtdWvDhXg3hzTYkiAilPvDeSr9FZfSwCkU4epfCi7Hb3We3eUsvi"
    "6zzhX4RRb0ZOxo6ZmPK4LipqABIMsedD7yd9FzzrY4eCPsrrFBIpPoIPxxqGhXuVLXY1l7zjQpi4CPeb2EFtiYzHf1fSIWG01gXx"
    "p8loD3PViuwnbfvHamS21wScz7IfG+u/yMB2huiSD0yGLel9x2SxS+omqCRZASZAVeYBTmIxibIAMAemMOfw+vD5WRSDaIYDN8gE"
    "L+WU86i0UtqvXLYMrxFL1Kp1AM3zV0lHuXgDcbH59D0Wi30vyBcInexBI6ardSTKOM3CKYt8yuDZifIjHDCdX6Wrv6HFqjUl2P5Q"
    "ZHWZuwsQVFslGXVjUrg60Q2FYI/ywck0THFikJola68OOxmKauHsdUZ9PTxMi77tkgrsQaCyV3d6LVE0WHAPfg77kqvz6+wcWfSU"
    "CQ2lXDj+7DVP45jKKVjn7uN1PlWc3LlrFZkrTKp5y66WaQeie/uN4MagcEr3lurf4045JdywGVPDzTdOEZfd1hJREnr3CPATwhxO"
    "yyQX60IXy4NLXguPIE7dEJqE+unl8cHB3sEXquiIJHkAdvhy93D+clf0yGAfJ6GO9vd2pLEPQR3Oj4925S3DNHQM8XTvYO/oWVzk"
    "qVaezvf2d59I6uqqZKdFsSOw43E8uMQCAGIyPZFN3JEnofmupMcgVODIpHn3RubFb8t24uU/gJegWy/DvTrB0TvwhuMXHDQTzUkm"
    "iNhW40xGAhBU0Qd6JMxLZWIqCmaOU6ayHpvH6Fo2jwmFY/iSpp0YnwH5UCWTgCPNc+62reVAT8fiRHVb4KcAPXke6FIUf6oAdkID"
    "E3fEkH9rG+YdAaCv9Tg/QWCSxXnswdTK4rifJMswe5XNY2set+Z4vmhcm84lAkgclUeNpEDuuZfxOpWrTact9Pel13Hp8glnvAdP"
    "Zs7EoJypssc2p0bsZYKZuV5Evg8BkqSqO14bNVSuhWWwTiWzA8Lxx0EEOPZ0kVZTI40JtZ2rEdIs7kRVShRDqFPInXuITnnzbXd3"
    "4ljOQoN0hB/L0rsIYRy2QNUPEiwk1G1C2IZprw7YuJUiw0Oul5ZO2rbv7Fj2//bOOOUcQhbyA/nP6e1t3kVkDBNgy44AUEd8FenL"
    "JNR8uURuHMb9oyKGtEhb8lAHajA4BFQHRps+AvVyHLZKRGWLTXBncwpKpMzZjNh7Z2Sr0ducS9CHtlyyjao00bM4tVH9mx9c467V"
    "rhFmTFoQCUZXMO/X9ZZnspklhz0+zezMp/j0KIWWx45ae/YItEykKUoxKgsoUrTy4gixe5JmNGdiOj0OCYY6E3eGmy/L3zovvI42"
    "MeIvmbfLwp2gpW36kyJEyxtRRoIiKpYAMluhiZAQmhCJ08tmaVKyQ/6rGZTOPr0XLimawKf3omemh/plAvXLW6Au5RXEHhrIQzIs"
    "z1nx9cqPAilWi6hF86JoH4stHCPlhQnBr2CKfR0aIh6kYg/d/VEkM9VnIyMlPDhg7rbMp5rPWa3vx+AwYha6mghjlHTo90Afu9Fs"
    "20IT6MKYZdvetIFuAFw0GgJDMoykdv02rLETNhcQNdkMRqHh+GHk7kez2Mx5i9RlWl+x2WR3EED9VXOie9eYLbbcNjR6DGFCCKzb"
    "fl5Up+p5zcEKoxksxxVni8plYIpg674248ohjOOJJuCQvKU7imleD+xe85m5ZEIukhunOYMHutuWU2GCu8HmHUzbSA9AbrWRDgfk"
    "NuvNBEBNMAfo9HFGmHFJGjTVje+oVBo13Uo8Bpvz0ky02WJxMGKYjKqSifkKMVTBLVZelJJ5HIQ+0e/obDprbJYd5npZ460soXyI"
    "pdrg/gjxk2II0Riup3NRHQrnWTyA0vWUoAYIXMOBaH3snkGFuNs+S/wIxm33RGsDAWxMXBsk50Iw3bysxRcaYUa3oFmb98pghl0j"
    "ETAKk3u4pJE2iCOBGYpbOpM/WxVH+aJV/r/J7k/tuIkMfntbqc7jt3xcB4jJVOHx5ZAuJAHoU2D1uwuHmvX/yOPDN7QP88d/BJkQ"
    "AuaBUMapcXD0Tl701F+0eQnhOwKQc/brALux2K/rnq6DIFCyM3TbnSb6kMro5gfI5iwl5fya5bAl+H9A52f/P3Nv2h3FlS2I/pXo"
    "rnvfglUiC3C5lktul68YbHMLZD0E9uqqW0uOVIYys8iMVGVEIiSVegljQEwWnsA22BibwcZm8FBMYlir+SfVypT0qf7C29M5Z5+I"
    "SPDte9/r98EmFWefeZ999tlj0pmcZEvRURlcBgBHSbItGu00kPg2G1bS8DPA42GjXm4bZ/+t/Ne4R+PGrf/Z3jgr051sd6KyBClz"
    "VQc42iMFFBd/VHFlKgVbOXQbGZO4k0764gHWlzT19dXKrI0JmZ7hKj2rmoIFLz3XnPBW3cjonrINoy0yN/VlaBl/ihjYJJLrF/SJ"
    "0vxyI8q2KgzRKKvTIzKByKIRPqNtqtlG6PTS/MhxLbY42siOjLm8hFGwi6ivBhyEPLcVRH/KhOl+WhRB/DX6xWF0Cm85ZkSGheB6"
    "PIgmjq/ZFod/nvdSbkzoYyOeeq/gUnkFkyKU3ZG/rrG4IOBbhmlDKM/Z0y+RBdxWsLxYrjk5n08oHtOEC86KYjgUYBoZDPnzsyMN"
    "syzqwmq1tR9Rk10tuSw6MGlMyfEHxSzdOvqGZN+2wR+dithFSkeACeCoxIfTREq1wRmSwNretNlZKxDPydCkLSf/fisfSTviESDF"
    "1U69wiHnycpDJWSyRMdAydtOpbHfX6es957BqjY9QY1Sv4CyKprqtFXMkyQAMdAwWM4AMkcYYFjofvWqTIBjpzQwi+TTZlK3FUhn"
    "wQpOCVgjrhLmAudoQCYwd59mzVBceCUVxyArq0VA9LHQDmdxUG6lKnZ5PRVGC0NHx1HbX12yNfZeHJTlfopeIZLZmg0zLFCwjl//"
    "6x20sQOnJALmApSTnbANkBcDTjBLMSwUKIjvBqpPnpEUslXMEl0EKrNCfX1lVeEw8EiCrmKqgv06Fxan0jKhPMXazMVbRp9XuQS8"
    "8NuZYWw3SQZ0dJpJMaYQcYntpGGsDnjMmaa2FlpSMEs36S0x0Y7CykW2FIKHz2zC8GQZtvJnDmAXE65fMicuZAuKmeAmNjF83oFI"
    "QRmZh8HqHAIJawY0689RGuow6YQvg15zLCW1QlW/DAjKuE26hr/CP0c+BJwniu+NAeINzofTrBsrCpXuALLT8I5eJj7/VvfdjJ73"
    "YS+xxI1OMzbInU6RyJzjLuB3v1cbzprNW4gDIW6K7E05zklFVcYkpyRYIc9cTDEgkXd4h5ixw8DXVTTRZI2m8D6JQV1M2d4gH004"
    "jIqV8YvNyOjmoJPmOfu6qPxuMYIdWSItbY2aHBAj2RXM9snOARbMNjiorwS/kjGu9MOOmGgiLkYVRxkR/bhvNWWH25426goXSC3x"
    "QnY5MJMwDIVzTvhIG5SJJJaIx02jxbQz0VHD+NlNL3FMqhDOtDDtFxpkGptbrINSXeSmicRT+A1lsY4N1+MKpgiip1FkPFwlXBw7"
    "dcNChqiACjHE9p+JuNo0WtqOjiTJMQnq3CKUgr0K3JrEjnfQTwy9F2zesMFgZEi+jwxt2PqKXdtwGrfWyjLlE2tQeBFJ5K0i2LHP"
    "UHNOwOPW7ggmLIEMSUPlgO1VjGZ8u0LlUeUagH0bznvCOJmBGSp8IavBXTYPmzY9f23HyKgDtGTDrA1udGjDXSFUWKnwgIx7jH5e"
    "m2ERDlNMOY07Oroc4xF5iphIe/3I0jqyATSs2Hozr6xnaX8+BQFfjzPUkJDP6LfGn9UGYG21LiFJ5QbH9NZtcntd98/rPTAThJFU"
    "IWLXTOIFDBJptWMmIJ1NfiKYrZcMD480gEmw2HiJ4xmIsR8dqGpkmYJyBCx0NJoybzZklC/Op9CuiBi8KO7VHgQOGkU9/Fnyy2YX"
    "aVA4FCuTMILFYCs2XpSCACqPM1MWBySMQlcRa9pOthKxo9/8jUmCY1OKMipxCZsfeNvMfRZY4WRRLduazettESYMKNkECwYqnPOs"
    "HuduG6MBZuLUVqpTXAD00XRRXZGFZwsgsXOQExz3t/gZVPXQ8pFPWcwEDrANL8b+s9aVa/xyMJ7Qz6qD9u1W17u977Ja13JfmOZ8"
    "/HIaxZZ23TMUppMatZmdXGJTR1DC14yxBt3hxgm3wNNRPOJ143JGd1C0ngC/BOR6F4xOY1Zsli1hFC6kPUAIQ3qUucMywPTcjd44"
    "P5SCYVLQTeuUFsK8TqAN/6A7VCZnz++C7ebT71wW5/ygSOfIh9NZeZIYnqIOee6jmYPxWr1Socic/XeP2WyKGtIi34j8+bDxbXA+"
    "TuOld69fbjNb5lNi1UtRDVSlR/H4dJaVbRkBg9Y7DLpKHFyF9Tbb1Dt+3Sxa0c+tzzRv8su4phPMPWieCqwYyr0cPB1foLvpsIdd"
    "E45AxaQ1FZOwPFFEfxbXzHY21W2hEIEdYzgnBKZcenIdXgKN1osszdRCCxmhtwlyhmwaXFI6S0g5Vs3V+ojdXG4qvT8KP3RcLUQD"
    "X2tKKSHwwWd0p8jCi7CxjgbJHMwDMyqLXbods0XTnf0QwxsGLlf/WcDJyEza9AVP4YTl0m/gL75urKPV7P45fVHunRSBoBisKpGp"
    "kVEiPxdxnrud9NDmNqEh45+EoetipM+D5h0+2Sk3VABcFmhUbUi0lrKZQLOoyTCtmWG57Mlb87mBzHJ6CRiBHI2bHJHy2oCpVDyT"
    "CI6ZoVMOvZyBZrGZEe+ZdC25EZDfWsI+qTVyCuGQVdRBXPIb1fE6TGMCsQ8QGEOVSkIm4LcwpnCFTZIxzgssKucpGEs4gINJZ5GR"
    "4zUAoXMBcLByPR7j4MyGuFRgMypZL4qONpGmesXpOKioOOsHFXHoxLG8k5CJj0hQlTqMkbmcbfUnFzERrR2v2JFto3ipaDRsw/5g"
    "KduVbiFtKSGPVY5TcWHo5UwmIQIk2jlGPSkHqcwSYD5Pll5stTJc11M6FrcLIwBSOeBROxybqEcNiTzSnETpJH4tGg95TY55cvOE"
    "XSnRumxz6bkXNgZVUvFsHnjuhWBfdb2pWZAppE8QOFMD0GFsQiKt29hKOuR6xjWAXTyRFMNZEEtVMT+1GyqxpbZnHrLrKvJOTFwM"
    "C3gdiREWt7/eLenUWNxK65JXmYwevQxm5p3gvbjkUYF60HG7OxjwZewpGEzlT0FjKv95uEygduPEstDGpM74hXiVnoHLBGMCqOWR"
    "FMidl73B1XmqE5IH2fesmQytfDsYd0R+G4kLq+V9xaDH1KBUwns44NyIyhNmfP5M6CPdhLOgU+HJbYsYvY6HMPIz+hcXyqiivTAH"
    "Hd+yf1Zuxjldy5q3mGy9rn0NhvYyZm44HRnuQD53mvLoLaMQAH1AJewHKn1L2VZN+AfdLDvQTuA7q0B3r1N/Ib5NdGK6rUtF+2cv"
    "eLWLmYXrTO5pbWOgPXjUiTMSExd731Pj7fHSX1C0yIQWL1ZzqdBkGzaFYSYX28tSudOmuLS7d0qSOfQCrcNRdYvGLKOAS/RCRiP4"
    "RrnPSuH4uI1ITkrxnP8iw3m1vV3lcnS1eZ0TcXAMv8Q+Cx3AjtiwEfKaEiDaCJjB+FOHgBFlKYwV2hIgVwpIiUlf6kSwGKZvoA4u"
    "tumM0ZwyPzo7sPzw8fHY3so0zOlPcMyOoMHukrW0xV4bhMQ2QyDTzE0SbFuNzU8NicRZ2jZR0Bjwad7Nat0YL930AF7NkARFPMcC"
    "QLWTfQB5tJlcj9kh6wo8c65gJk8+G3YJs+PYEdu8pyozXb3PBnHQLR74qEErnEAlzK6cT9TgHizCNrhCtyrwUc6JwFg/iFlXpucs"
    "rCV7URHZEwQ6gBYExP80WC1u/xykVyBlyoUTLIYQQDXiTjniNMMUKNhiFOdu5kGL571NjIaXe4NkK/Cm5AjwLo82SdbFqRrX3Z0Q"
    "cpIO46rVzO+o1FskCqGvJtcJfxVZiWQaNjBhLjs9vqHp2ZzSM5qgWLIQVxv1pGa+TaYbtuxm5VbaqXaeXANebQsMrN5w1STSEVr8"
    "NszHCptAdNJk3LY1U9uwFY0/Vm7MLz/8YPnu9d6Zo6ZMvNn1CMW+uhHU7cwUo4SR+uo6DXlDwuQPcBCCauPJN0kp2NMhYmRsy11O"
    "iZwfvMpZPVWfKRnSqxMoqJxMAJHsI2/lUSskJJW8FGaDXOO3gpDY+NnKKd0rz7CgtqK9k21leY2VGy1AuFAF3lAmV/YyTcz9bGZH"
    "qFTaSF5CQYUYOowlBi3vFz8fZfThKmwqtNtw5ZuZJWuiUN4reA57UiHTvMJfS6ETQ3nFz4vNOIWEbknRxv+fWH5wLnQ2xmg0ov2i"
    "EWiJfB8VWvW4w7kecNybMjwjvrKftaNuH4UBCjFG9LDge6IiWPPeaLYpEqL8rOt8naaB681oN/uqBRP1xTGz2p4Rgz9IelEKKoHq"
    "w/F2vRzapS+hBz8ACXDSMrIliaQQzQTRftSqiFqnHU1GmLMisdFgQsFu2hLFjuKVFppGzOifI2x9cr1qks8+JZreQJ8ofKXgNUAC"
    "DAqOwlIlp9TRMqZNevhQmZviCP29/3XoBdwhebMLR8KWFVkuuxHU4MnLXGS/iIPrnK/4dDAUT4/jq2k9Cn+9rnijExsLhnHBifX7"
    "qVPs8NHW3wi7/z5/34m78Q8r8N7ZCiuBRKaw+iR0+o4j603b5ICt9vGWieGHvT0fKm9MscMddI4aom8jj568nuWpEQKp9bJW6Xui"
    "yUEnihwwcuRpj2Ios0Xb3njOdGFQohVqOwUeilliW9kQOA5mQFIrFq6SnYzLYlwK3sBgEBhenjUZkSM+Qi6IvQjZMOtZJmjs8U5Z"
    "7J3DuyPQpkiu5q1PfkRDKoyypl8+P4es6igo2p3G9NAU+QO03Wa7J2wzA6Az24y0/CRsHpwRKCCQjgrKIKaaNVk2aOifb+/yyEbG"
    "6ZjMC6wM//v8+dG9wzv3BiM7h4ItmN4z+Bcdkerv858BI5LL8SxWbK7Phksr5C0PTahwvFbBLDE/TbwoPgKxpFvuN8hfbNpcMNC9"
    "StXvkh2qmAk+7SlQL7UcUVkviWvcrrI6hGOtJeomfdGLpEt0QqRFqC4fYBIcmiOkLmAS68H8iYL7ObEG5AimT+4rE2oOMLqzWIIY"
    "TNYxFSqtX9KZbul9yAjs2ZMVjco43nAu25PhKPVRIEaVHAVxbZ2KxiOHVtnDrGuLDGoAKaphkaB+EM/3RfjVaFGg9WQc/krxL7yC"
    "KTYjsbr53OujVh/bdgNfZ0+3MSRotEg3mRLH4KlUYZ2el0tODIiAbmFc7PUebelIshkmY3C7h/GMCTigQYz5klO5DhqKSUuD2TQr"
    "matDrS1nwIzgQ9wiv4Ym78n+kLIL6TMth4L4mBImhZfeCF8GPIeTAa8/NqbhgbQlw5dpn0RUmBLQo23SjEtrx2ZgsB8u7bvL7GUt"
    "X61h07RvyxSswwMMG9foTEd4mH8JEPhptN7Ytx75UeS5IkqFxAdGLH8aHi6XQ9KYvCYTqUSZMmtqV7zUkQ2lg4HRyf6vMNeZWsQ4"
    "c3KN+Rnh9YtsVchJTDvYHKp71H5mxz7EL9rtPlSwzhkVtNarKvuiaUv5xyZQDE8+LeTnn3Ji0olG58+tTBWS9Hba0VhYAZwVqT3+"
    "YN8WFQ2moBsgLe2Qsl6NNWCOZAS6UxJXsTQcy8d/ZhPAdBDpeQOY2XEyWPp5TTTDA2Po/o4aqPp4QTNU+OQbLA3l+IbZxsJ4DE55"
    "4RgaZCFaxzBdbczPeT3uUx/G8XPqZ/tnyqDcetCUu+GyPDYxuCyqbbAlPIisA9YEAw0ad6pzyqLXxHej9cIArGt7WDFAJMvf9QEY"
    "99OWcADex+PhmJE9rzdPBIyjQSawk/C6YMszNAqj89JKvOsmid6sE9aYKy5faEwefE6fffgpYZxPLL1cP4FJF5YNB9wI80Ho0IYN"
    "06goqwIs/yZ/VRdMYSgnfnprbiCpvjT7X1H/iMGqcHUpSnu5TIkkOFs4l0n+mdHxWqMePbmgy1y2iKEOPJxhXXVptSX+8X/otJ88"
    "GN/nSpwH984QqpiY21RGwSte/737gIeMfBLbcdRJSU/Q8YcoWvrRyagOBW1VIgmrSeVC+FuO9oUxP42iGotXKOgI+sORGnU/584L"
    "Eimh2zXSJRzQiYIAIC/cabpYRhh2x2W7gdFGmbJpxIA2l79Kv2MHEYf7rTRRmIANW+AE4aSkODFW06PAQdAS4Fdn0bet3cFgXAZa"
    "rIhGMTAivK72me9yKHBR4TGZRo1GJ67a5mwCE1r0CXJkSYOhzgTwtvuSsLkvqqcCSgmP+rQWPLk9MRFHxpOqkzgVw66oUTE9ShmJ"
    "h0fa0UT9AHmN4eYMumLZSAuwvV2NynEdJTyypQo4bg3FCRuSzDL5nrM8XS1Mgzgcr2GohSSIYW3ToBrB4ZlCX830RUwt8mACiVFd"
    "syvlCLcfv6HFUgYTS65ric+KfgVo2Uxt4E6h7Az49gSDWUPn3C8wdVU0TJiYoJXgoZac8uDNersCPJKji1XSLESphIKLorbDCBef"
    "MWg8udSZSAM0Ca1DjaYXIXIbqs7UowPtSupAv9+EzZ2JOtV9T25PTuCDAW4HoDJvwOf4yYNJXJL95M+L04FDAO3XYHdhZSbQABtd"
    "C2Bi9WawJyyrYJHIEWNgKCijwcTBFiJWlWAmqlcpxjbNw+FwbiKDwWgadfCo4PpjV168YRzpfjVKBCqcUm5spWAbDqlNn2k4A8FU"
    "mDgPYSh1I5yq2VCPb4ZtOPYzU1Edq5LW0YBsaVWmfaldI6qmwcSTB+3gz6iPYAnOhlE4RBFiAIwYuycPpQqKgAELrU3jPprHrie3"
    "q9BWDQ/egK7TSWY6QnbRdC6phY1yAB/o5jGzwGbVmtpRD5CzCGAgbCEGBAj3AReOD5tKCVYultWu2+eQDBlWUUa3YRtwlq0qoYWW"
    "NnSSZBxGAkRkgM7IeG0KMSRlBODVxkExDjWpD49yDATu4OCoWrH5NgwntxwZyAHC0D3t1vi+OOL1o4qG3AnC0ujhCAO1INyA/6bq"
    "JAWFpTRDLZn8cI4C23PrUsc5z67ZpAb0aI662MRjzYAZHy4FOEuESCg3wcpNbd3FjMAOeCTkGeqxb1jh11FeYn696KkVrerQQWwY"
    "kXpMmGDRUZKWoFR/MJgl2myz7gEJhnbIpcqBuRlJsZibKeI3hdSsCk/qxNz4Gp41iQpcj8HBhpVXnD/utgx53dfCq90SdeopmCJ5"
    "Qm4WyXQ8zsHucEkC/LOGb3F/MvjZvBwNEf5zlM6kATeOKIep+OwZeeo+BHBtwOVB6Ov3YYxPeDA8ZDoftldvgKlaP9GM8wY+uYS+"
    "MHz96osjMayZrWLcK3JAg0EifBQd2AAbs1/wVn/HdVGJLLEUDEr4TJI3QmyxMvL4ggy9qEbMKKR4PQ5w1SRRzwG7qCU9AWuvk5m2"
    "LF7/a5Na4Ls2eZ1CEo76m0+7OhrJpYY73EkAfwD5khanrmRCYZnYIix3fC0Bx6297YaV8tqRFTEEbfwZpX7NMl8rr0ZlueFkhX2O"
    "C/driBK4RMGOWlvpprBpmte+BoZr5TbCzkSAek26PULiiugWtFcHtmFu/BrqzUNHJ3lciWRF44vK7pgZxAS0jgexWnCEnT5d9cJH"
    "OC48wwVNmO7dfQEvJzyPTyEFphkKzm0HMYy7YGahKTSDyforhWZae3KpkXpV4JkbVQ0Hwnvkkk3ll78CbCvtgUdHS5mOvaQ9rFRE"
    "Hlb3CxNsAkcdpaVgRHGveBB/38K3dSGy/DuHI/GB7YL93g0AHRwBkWc6hsWDA5vyO8yrKovIFETxF8hEBy28kBtPbifIUdsybmkg"
    "AHZL6CxNeAYVaTU1OpMl4t9xJQTr5EpYXwqGYEUY9en8Ys87qT7d2vRAe5G3FObZFHYsagMrlZBtE7IQRJ4maLyJyyTLE8iVDNsi"
    "GEZMNiAGwIZ2xvR8A0ApgShuraF/2kDwi+F2iamKD73TY1qCCbv+BswmokcOKnglbJejAihYYk4oT096XG+C1CDFJq2qgV0qAhQ1"
    "YT7UvXas6exr5kJs++28QQC2lUIwMlvPzB2N1yfNJW5XCchEBg4/ZcHCZJxkGRPQFRpXVFQZCvZJQlJUVm/LffqHqTojcOgaYS7B"
    "1gP0G68lUcPrOJvLne0pwngmEiMPu5EojqHH5ZN3ajGiIaIpbVMeygyKMBuR2jGgzE8LR874EDaDJ5dsm3z3lbxGAde2GkTiOubA"
    "ZsEcehdA0LaZAOWv2v0aZKKWA1Qm9xp4Zwh3ZYuYQx9eoaiGL0BXhreoqKEL8Q1xpiRpLkcN/gwGeFCzUGoQCrJgDARth6Bg+4+g"
    "jeaeotNRFXbTZTuFpC5bQ8IgKmAgWuU2PstRp/FqcS0y4R/L16WBBcOddAZukmwlDL9cUKeBXHPfSpMmkKqrgDeRoCdJtRCEnmJM"
    "ykrlhgRwhedl2J5xBdU2i9dgdu7jVK1OHbwZ1Z9ccJ/bHDm5lbpPrbbkIXidfriCadgLCvH4atQo6+6iiFHzyYNYD69D3k4NPYrJ"
    "TnuSboU36sBfparXSc5rv7tFscJNG22OE70FpqKabnYaaZ2kaLX2BJzCOi4no7KfxcW8Sr0y9Wi0jI45kDvdScPrXR8xBhEx3C6H"
    "3E6kmmjs9sDfMNit5a8eenP6dYq/78I5xoCXjKNZCB3N0YOSkB+tCZLXxtpikEsk7D3Gv3ryoNympSMRWinuNMtR2z1DOemCLWaf"
    "ZL6Hg1nMWWqLxMcBHRvgmZCG1cSVwW0fmUjkZ3G8GDIKOp/pJCG6/qj2GbXa9AQwQjJbzOFKXoGzRcbvrm8bZyhbdTBoxejdzNLO"
    "2b/MBVZszlVlc3a6JNxOmGqBJsdTAZCQV5lVa8UjcnSHCs8rzRcduhO9lPA4qpDB9av8UMJdnJ1CbZGDoq0mm2y7wbx4PhhQmlfE"
    "0+gPHUQppGxT5rnrw5jrkOHsu3MQhZzcg+M8E8Pb7ieVFjLwFXocCvtAIIkzsLKdkaPSHk8HQEJelFGlPtRQFdUyb4heYU+pL+Dr"
    "DQooT2VAPVEwCRc6Pntxw2dYvQIMcsKyNECEmJ7DsvcYVAPaD6tqTahduyBEnakBNwSMibBPpC9cp5BLwQQmUdyxcrMhEdixyNM/"
    "SgRIJ5H2ni4dYrGR938zhAEifqF4vcZngyqwc6ENjbDfbZaBkDxdb5CwsR6VXYkMWY9YNRwXFOOywd1T81qpOLKQ3Xh4GMczHZhs"
    "1cEbZ7WhBsYK9FHALKuDJoZpm1Sxm5xUwhRePYp9ImDUuPCpsE9Lp2fhjXBEXNFvKkrGJZcezYRuWLPwJHipqiVnRbFlEgL0O2ua"
    "corIJNhDBQNBE24jwiCTdxOHRq+pclRvBlY55wn2Sl6DO+L9UFDx5Bz0yqQuZsJag9Ej2EjC3NqT28ypJsGmjRtLGzduRGjbJHNJ"
    "QtrgS5Ue5NQUySUakdoxBjZPBJw3S9Eraqv9JeIasgbDcJm3CDPz1ew606oPBK1aHDkBNxoZwdPgRZgTHRiaL5J4Kc9Mp2iJsC3d"
    "tZkkNDVAp4uXS9aopJBa1PrwT32mCI/RTdiDKUfI9QMrZUEwHZvLEQ8wukBWh/VYDZRGNNnL1a2HJyRRksYXTRZrFAXS+79eo3c/"
    "1J9AChHrifx30tC+lp8BlG0VT4KhmDDI9pyDcWv7CrVBi7uJ1m7zRkP3cTNhYZthgxcMR4HL1Gp7VMJfTAewx0oA+0LhPz4Yp7/y"
    "1l5gAfsnmQdu19OUrhHc8M10U5p0OAr2FWfD+WbUgIV2aOoDmoR829xNqEZ4oG78JeHyquHNGBe2FFN8v+GoU9wPxfYzyGOPCx0D"
    "xOk46uS6xmRTGjjsJNrTWUFRuCYLNwUv20aUATGHFy7JfbCvg6gOVL3KXVRvNlN+IQ8EezAEUBsIsxETG71J9lZQaBG37FctQSRF"
    "tBM6WlE5In6V6B4NJRGZqzSmjHAdWcItT1gtaAWCaQTvK7XWwLjagO7b/MGSUIv4K0TuTcEUIplldUqexF9EZ0DQXe3iA0zLU41Q"
    "tybq3xbT+8yIhDt+6pgQr/1Rxf9pwyJ0g8soNzSJC6a7IRn4z+9rAIleS+l+hYMIYcM0grBAwbQWszRBCsc9eUv2+7AVxHBWGUdo"
    "MnKaQkrDkdEykLjWlsY6WPKKELYCATHuO2yNHlB4gJ+Ew3gzAToSx+wAGmJ7hxGf5NTlgWBlkzrlzNxGahB9jGZmWMT75EGCB8Wc"
    "RAdSJqZlC9zFRaXWg94stJOVmH3HPXzTgO2E+0dA3KXhgOtxPeX5DsUTIfBrueYEwtiIRWh9gTL5vv1ruU4xC6JX071HY3i7NvUq"
    "9mPULVk+wDdAPdW1yllrLbvynJuRMhbgiPGVwCo3g+Kx+cyKNoXcEn64RFGt+Hk9MoEiRsCwRiUPl7Zauzok/t5lGEpcs35rbKqJ"
    "7/l2OInbiG+eAlK+eePm32zYtGnDpt8oAtpuNeneUrhN1nFb6ol3cdmUtAW3UCfGQ1oRiUYs4o/8JqkYty18mpAsiBnsTVuA5cAW"
    "Zg2/PuesWFLvBYp6YKTuTWfQ0pqcIOXr3k0vMnutnj5WhQENWOsdfNUA1YPHBG2O5GdSzyNJ0bOOeI31vurKvZxeDqyCxTftwHsY"
    "DwlpTZytRaiE2YaBEpm2NwzinNxKx2ItQUPSQ1Fk7OXgX5GklqMqvHbxFdlo6CY7KPzY9x9f31Kw5d+7vsErcNNNhDVcr9yImFPV"
    "zeGFhBWJ2sJahvWGkY1bmYqMdKpDV49iG9jgD7ou4yut5FrgzCdWmEZw+VIlSOOW9BB285kiSaB9CRpdIstz4+DXwZsteZ9KRZWk"
    "gmwXgfmK4joKKvAws2FWi00aTY1QQigoNRxfssgGmp6ABxcbGpxmODlJimCoZdR6s2G1NaeKhkyEX63Gc0Y6DeuplLHeaXD6RTGc"
    "7CS6pOGkZVYoaXV92zwNi8ZhmPUG1nCG2lBWjN7YjFIPRmt+TA66OKOmDstAbsdrjRa+kKA73kCFAsZydxv9mQSJtuC1S58QW7qb"
    "dypKp0JXGKaCAkBiTKD7diu7ezrtSHGRYFkWUYyU5FUt9ZIyz4hWVQmnk6FqS3pD0dwmlGsVAEifxmjXCL8c/o9zftmIyL58FrHH"
    "Fkzh2FYqEgehZL0bvI4xdpZ6Xb3aIB7QuxRUJyM235A7WAVLCxyMyahhS5HxhPce8BZw+YpWJX8IaeUlu05OioNn+M9kAEc6dzlf"
    "L0gjAwEaNpCp+gxJSgeDWXgYw1NkzsebEZM8ayePQmgRklMRBJuD5bLO2qy02xnTVIkcLcX4+OWSxfIVuEzqSGyrkZ9Y16aiDTvE"
    "1agSlZVzS0QcSqZrScoL6yrsBSmkrK0Dv4J9NRRDWFtpS2mj/hbTuSqK/Jpqcb9qNLddJMYi63j+Stb6nAuCjZLFfDkLYPyJGAi3"
    "CK1u2r7RDFAURltXvY+Fv1cobcOpAYRpBvGTS6JAJgOvOEPyqGbSQQdgLAduN7Am9Ci2qFKk8zrc0S/B5R4/uZ2SXW41gmu/0cCv"
    "rIJAWCdezHWKlwIzvYbIcgz5oV2j6hsx+hhR9rU96iuwx7AREosEf0YKk32Q0ZpJ5SGmFAYAkLFRk9jlvh2yAkLFyOuoq5rtwHme"
    "ozilNs+xAxmmtcoVAfZsdyPFqzLqM9pKNBF2GukwPzSdk0BB+bADyHSHN5kR1giEPFUNBDA8YVMxk6hRg5sp9u66MOFwNDRrIIVi"
    "GSvpezhSa9mYjNlKlcpeWCFfNIfIRjGaSViCu9gSo97MSjDb6Dc3RNjwy8DHByh4LTXffaSAou0HuKwfUvB7Wi2gfkf7QDIb2fci"
    "ONIKSDJyI69PLIYUVolb6SvyquAaxuwJ2NNKIaSxba0Lb5mzbWKeFlth7kW/Jv0dpZXhbmc6VDm/654JDstFSDkoOCDAc4UNdNKW"
    "XIU7YiJe2oh0g6y4mN3Gds4leiUkeVvSAIhFDaVBKalM4046gywn3hT0WhlxBrwVFUgB9mDKSpFJGAsUk5886KmTkukryeLEqqak"
    "5gD9d8KGEah3BFWBfiWT9ahRCyeg36EY/SjSQXlRxZ65DmM9PoKJ4a3BcsIM3zAKTyq3vt8kNK9YxrAtmgb2GiCOueRhRJa/lGrw"
    "nHFHjtfdNEjHit4vIl51doROv2GlXzEhb8k/UoQ1XntWSGWgxKXGJIJ4k/zz+YlZMcpmml2BywebRYq7jN8eUZpntsf0SDdjnnNF"
    "59h4IOAe1Z7c5jw12MSGPxBGO/tnh+v2IL+ca3zE+sQ48J/XhRWLayL0Mj1kYniwTE8qKgV/6YItnsEpnNhg3c6h4Q27WpUO5Qwi"
    "QNg5ZJ3w8mRLX1MAFJ1CTsqBkguCilT8uRH+mdrmJuu/j5DdHxrZsQEdDZ88gDYb2ZojnMfFbhEf3pE2vJAogkpono9+u1xNjtPQ"
    "JLl/I/8VQFnC1ujjaYsW21RMkKrAmW/kbm85l83AMC9lZkzEYBjqYrwOGhMzs+poyloNBHp5WI0gCyJWeQoNeY7Gxy74XTAcoava"
    "Pgz7rybOzlTB66hb9FpnYUWY2C7oFe6vs5XbBeuI9UfDcdv4ehckTTkGeA0aKUUzwNiPnVScjsh9KoiBzu1v2U0r6WXCdSeuVFwi"
    "jGW73Y/89HP7J3oPO5lSoDSjGFSIhggHfAp9mlzL4ukCYyeIFzaKt9kA8RVbhCgHm367ubTpNy+UNpWe3zj4POpPi5bDG8HPWhA1"
    "FLskcMfVhimu6jaFAago8ta7xS+3OLuLKBBoRDWHxZ24HYXjNQy2xM3O1ifn2OeAX/ttEtCUMYbFjiT18I5cEcQ5Kn3ZJ9p7WFLx"
    "S09epu+SyGiNYRmlxViviumEkJMNbGDJ2f6mjqJsvL/bIfL9MfkpYCyJFC1rjaRrMNjeFrLMk8H9RYVm2xfiVaMK9pXiKpbIfUxE"
    "feb40vWEqmUaCzKSTq+Gqw4XHBDUsBPwna7s3QfMbLwO3fUsXnSVUHEfkqnD235jNG8WxTASNM8B+secjJqooHj7ZjrJk0vpDLJr"
    "6MsXowk+3sOpp2UIKq3JyajhXbz7OMuCbJLkXBAeyojeuKNO26x4sI53hkyKdqOGAHcoWi8Hq6LcZTfsgF6qnLWU5uoCZAH1dGiF"
    "qPiijHwK9qESFY6cZ8UujhnfTx6Z8ug0qF/upCmbwBh2yJQ0WN6N3y21F+cBZOiC59DBu8APTh9SzgWZELr9oVNFzQTGcLbtGeNI"
    "fYztW9ZwFgBkNDeDwR5cS+c5wmRPxQarxwWH+j9wookewbvZXu2WORD2SCQxxES/GEwRk2SOcCD+2yQil+YTU98LwYpN1GOCRZkD"
    "jZYOWg11a0T1rVcW1KWAjjtGNmSYCl5P+3hQC+dD0EX/+iSiHUYOpY407cDIiCn0mbqxUuCrgi3E36MSbehVp9Ed7GeVUo7YjVTX"
    "p+Gw7YsjeTkexT4aPV2Cft7Z69JbHNpBNXJ60LApJR5fIPgzcJL3+a53esPwyVL3sSJSCNHvntNd/m/d/FGlyEyZ+Crt5OSUNbl6"
    "ORPmn1U5bhkRu3ZdKob8GS+0gVynYtCclugYox2t2DY24WqeYsEaO5hjXAYUWCHpNs6CeIpxidJ2OE1aSsf9O/Qx5eQbJkpl801l"
    "NTfaWGrYlGvRtZFcUIGN5p7zB8aMGXMGjBdn7yYxrVYu5d4aerB76ES/0Q/ciVCacEOQUyYbY6IreqZwvCZ2+aIKc040XCxeJ0Nl"
    "Z+rjCow9lW4YN4VBX/ZhWTuu76wJ9V7jK0d7t1o9AUEqxzyyiXTKUOd0TtgunZdM5+VOYgMMuO6EfalG7bASeaDZYZobFEZGxtxi"
    "kkSYk1jSrcybmLMYUJwwAAyw/B7HiXdWFak5GSt54xwJRVVib7jMKuGVNAlAZOQZ9B/kf+6wthoc2dNupTN48IA0axu6LNZQJcEc"
    "WyfMopDIRphshAW4iQAiSnNTdYjyRj8E8fBOYrRpDOUbDNh6GpDclFRDQrhkTATF+ThBfYwIPepEeq1PoXF+M+bTUu7N0IT4QPuL"
    "mY6RxZU0NPlzPtUJtM1unapWCqsSS748LdRSgjPDmrdScj4bMLyoRQXSAtTawsyK/sZqaRAPJ+CFlLA5pIaRJHE7KJ7Efl0SMxdu"
    "FN2CzFko8kYQaawcSSSCyCRrsBralszW5oIa5piUUEG2lArznzPaJ2vF6ZxXfFCn1Vf6qiyEviMZyleXaT1cMFvxe2FNHMkCM0UF"
    "SjinWHc7ojRxg9kmjDKO1POijgt0FCULmaT4ADCA9UAvEHKPUOrNndOdvOIwQKng/XZRB7V77/DwjuFXDeKkeYiR3dtHhnZvZ/Md"
    "RlP2XcvAje7csZVbejrcyNDe0e0k/uokVobuQbyyY3jH6Gt2gQsAhnbs3L5NIiSx/j/UZgLmLOTuJguBcai2ibYeH24O6Y1ilOEo"
    "lmuY7BMPFfVCp3dfnAFUIcaE2y4bGqPAWhRvYVjeKhPERluIdiSZnEWfjN2ZKFEMgVrnYcF+BmpbyxYPQrBfGvLMW2SdWlsAR+1B"
    "Qg7eH64BUOcoD6T0ynbDzFySTiPdyy5WhfGqLGgWy8XRSiE4w5VhPPIeERHIbHXOlgLbzZOhp3kVXYPogDZDJhAMZZTFKg2KURcb"
    "M5N0i+lnWLRH5Y5uAjvKdOMNkVK8eauEX1VAK2mQ7ydZAlFzOR2nrCKzrCOwzci2Asr4Szdea0lwOvOEkJtbN85AnFRYqSRyncHU"
    "d1RQMz9RV9PPdkmOKtxY3q5Ca+j8GjbvZ+YsSQNijkF1nccLMDPw5g3WbWSRH17IFNiV24WzuYXX2zzUJNgBW4zJ6ZG7E4MmPbmU"
    "kuGdHyTCKmq0nR0bSRsxaijPFqI3/MhMKN6aHcheRor8QFhSVP7/bCxQZPH3TdJoZvEXIOI0AxMXYjpADlUqmDiJzgyDirNdYat5"
    "aCOoK6xjfJ5VZDpE33YUVzLMO/JAGMkD2BKSThthAhpht9oooJn04n6gXAoXk7HSF7A6BOI8vGnksfFTatwTRNNeVE1ROBxunzm/"
    "8RqKIMlnLkZHEJIwqBs4KXmEY49nUGNQtK1JFhIsfpKpavzWEbMCXCi0RnP2WU5WIUw3hyCyKCQbMOg1Kpk93dTJ7MioHLJ3EEpY"
    "odnECmKTSZg5vUfIpEbEtPue3I5jvchhxWDEjvyAMtcJwAKdNAiEtNLHHEmnhdKDEmaLaFWMTOwPwHLAUjQzxaXnNrpb8LmNZAWX"
    "BfmtAvltMcg0P5DEReNfw1o7CxGSpuzVKAmbuCa54WDm4Uhp4UQnMKDjy6FcNCVEnUVr7jkreIb9tg1N1BsN8hze5gV6E9ugRETh"
    "5bBR8YMYiWxbI4W1mOWWVTgn22w+mBPD5t0jPUM/WRpjHif3deR4EAbA5AaKVduHuQ5iNZ5+DuFUDAQnNYNAM2xi3gqHMZ4O0e4I"
    "X4EHtMobFfvuy7zA7VbzX1tlrTHtTMBmkj9qVDdC4EiLpGSPa1FjgrKKw9O+yqnsebViMresWG6LPCCN6WUWRjFcBXCYiicZdWmJ"
    "t1ipuvICk5mYMHfbOm2MeQMMc4WxwJDNzFYN56ylM6VF1tL2GDzVntODyptlJp4rUX/TTLcMLWwoYaqizbENpNDxfVqhpa3EuZm0"
    "Vjem2kyR/fGiEanoiP6VxrQlbOyLJGoZqoEQDbSbq7iduRhwLAlgu1VHrnlwJSQTVRWKjDW5Q+XEWLc68boN9sQDa6oYQ5oL80MN"
    "ZWBl2SX0A5u3Pb2GQwgV2SIPo9CiqDknl91hA7IaAqmv2yS/P6bpUVSR1RVhhpcBm0I0yfoo9m2V5Ty2OGROxBxIMBzpFuLWaMsG"
    "+jBsV9WDVbTRmfT/t2BTAZYYkcT/6FMo8/gfuEYZVCaysWVaEQ7GrdySE6A45blj78edy+ibRJJVbxry6aZE2kkPfxKMoF1vRBkQ"
    "6XE0ffIgnTHBASfhvrEZAogAM/KWnb7bv9uMf4xHTD11jIs2qwg8vZop1hb+28gUJp3JSTY/NaPLAEx22iIyh/HK2HdjmvsqBhhI"
    "O+1mpsI4oG65bWPA0F8cE8HdWtajDZ2tNEiyAYMJEo0dQJUXmpPG5gFVQoW9qKfZDwSOPi4ILbqV9qJtSnkiZF8eNTIhQ9uzTKcs"
    "a+m55sSGPmubZG+sTNOjraYxVchI3qzpAjzDKO4z++Yn5RA4Cq+3bJPC7mxPjO6alGHChFg+h1OmqrotDmSiDekjd8Z5YfQdgH0Z"
    "wSWXqqDPhsa49jmx0rTpwblwapZiWGhkrrfXbO1+dCzu65RkGJ6GcdQjJz2vYFKksP7diyUqlJZ3Z+YoBAK7PMnWVVAVyoJl5oZF"
    "woz93mfCigc14ULQKoHNhCeRIw98cpnJcRtN+Mv6Nzo/Hy6MDsiRxtghW0ffCPiDCRiCGd29KKJRe0M2hjvCTACfJP6cr8hPie/K"
    "soQR9ptkExpTiR3yocr/Lf4AVp4iANVOvSLHkKKU4qFHy15cs1TDyIPNUD8SQmUsWj1ePBs2lyQ0KkZsx8QL58e/MEmiKvCoKAxl"
    "fF8qGYrJserVpw3aD1MPNeoWHl8YW6IKJreAlaIMgTY0gSwQPYfhdunXtA0xZMbjwjVZtil2Ia3tIMZDQoE3gc7E+1rtMlp5hY10"
    "ooFKYzZ8H9bVspHZq/xqsNeeh2YRhq6dGk1b/MwM2xRSCG+uXLV19Opf72rZLFgpSxiQBpg4PtbSUMWh86ymOLwQdmFDCw3YZzQW"
    "TpjwVma5Cv1nVcEwMDGCsnLz66gx2reFmEnDSBpbMbNkBO2HFkdkZadMUVnGmTFtF928Mza0yGHGSqJ1szp1FZUl09TWAmsIjvDE"
    "oggiI4VV8oYQWI8u+j4Vh3OKvmd1tYup1S91EAaBYFrr0lHIpmeKjYxCowXfyAZn94l1kSAp4sKg1wbLUE2sIb8IHlWiNgCaNuPo"
    "kBSXW2SutQVD3CcGkcNpVn75Md5dUSZUqCQOyDgw62HyqjJ3MommNIZUT7UoKCgqryaNgZDrR47TDqP5BLRphtjHKxGSdBtrAinn"
    "jGqEwPGVJb52wmoxa2ISABgsq9STyQY5Uw7xyP3vJkaPs+BnGovNYpoAM20kwc6Iyflwq6ZGTS4Kt1rZvtiGH8ulrUEl+vaBheXT"
    "8Tckbod9e7qgUpQ7QRIfFFgl2YG2Jc22C7MV2WhpbrQEJQuzh4JjVTyiYo5ZJWxPDNBwaDRivNcnjJpx1+BI2wN8D5PtJFZCO1cL"
    "SdwUUqk623FYgzs3c/ZygwHgbGsY6Yk8A6DJrbX6ZOB8aq293f4WPAZqLRrDzpAjrPOsLCdFxJdIJTNyKpIcRl5qS6oEvO9cnWq9"
    "kepQKlTzDcmXFg8GI0MMQqUjQxu2vmJ3I5xOZIXVF1auqK7rMbvvisNQc06A49buqIk0v20pmqtlL1y0rttFmXpQ9a7t6mSrh3Oe"
    "L+oVb4YKPCiZ8+2yCdU8K/HXdoyMOkhDPigelfFoqWQ4VgANKxUemV1L3wPGDpAOwi4TNy5zw4k0o45iTht8L0OyfIxch48Rw3ut"
    "N1M0ukHHiz15MOFWkopf97L3eJ5RBjzLawBSVykM2ygd1RraeqDBWXt/FKz75/UelKFFwJOkYlfsHhQSUJLMUpRjKM7NSI/abkXQ"
    "Q5TyCZhjZiMQsHpstwxBQMsNDMZglqIcTcCtR76FdHeY3D8cbMKxaeRZyy8EnQexkzD5HLFLwrY/CRmv4JkYlawjLsuQWkk4wdAu"
    "oj27W9G9liQbsuHbyTNCJEPoGiEm7RtG6pMRRv401uYex5HPFMXf2cqA9jdrR2OQKUv9zVPD5E8Hvgdzv+AF32Dnd3k/V6JsHVH4"
    "GvcYet3uGt1A7DyTKhN/kXhyNt4hc4V9GSMdo/4zcGh6WGQMRLqBtBwa411dpSYMf7aK57hMt3Z9f2Q1uVZxpKs4729CXLTg3oAW"
    "3FoypTV45ZmpEtlMOQcAu1loUyFKKoMaG9gfrZIJsqqNnE2ikKCm+Q3TlnH4RNQGSoCfxMcNk2BEFYklho6CxmOmKFMH3ikDTI99"
    "74F2KRiO2CeQnhBhu9J8cunJhXqVs2iYxEa/C4bscUDUNdmr8wNiKwgUv5TFwRw6SMjt108kUsrg8mv1SoViZRZuFMcXS6oR73Ba"
    "osRYGs1NZBnjLJ/foKL8avY7HSWiwVadlDkE4502tDo+ndMBORazHg86YI5XwnqPIRX3Llg3i9bYc+sz7Zp0rkBiWKyBW4IBGDMv"
    "8ck2GfjpB3kp8DowIXWZGUFWse2kb9m8EjbpErVDPDHHzsU2yXlWYkeRTIzcY6ab5VbjRaGZ5HfsGf51mkC7o/GaekjTEsvhMPRz"
    "BplBxE57mETCJc8WvCYGlIpd9ltjARlhS9oTu22EKhjlCmMMoelCXKlX5XTktMF+Rik7VA8ZfawoxkR//MjCuUmQB4G3HBiLiWW2"
    "kl7sDf4QzO6f05cVSxxNGgj+K1GBoZGrijhznmqBhghdIGNCriW7o0YUJlFerCApedLWPlgqkoyiCXmY1swoXA7nvV5eIR3Nz6xb"
    "Jqtj8H/5EWzkqTAOJMaYFei3AuFse4JNCTQsi6a2ZZOOUUoXvpQ7fYemMqNxGqiqkSe0OVsQqbmmWthvye+33/AEah/gMmbPFkMp"
    "3msv5Cc+izhjwVgiKQgkFDW6gzTKWp3rZ8GgmvV4jAMpyysQR90KPOWP9UMwdYqTdFBRcR4QKuLQhGPiXINe8OJZQ6WVOgxReBBU"
    "zDZx9LZZ7aTwe1jqGRuPhIrZwhMlCWVSRZrvKuax1QWp4McEQ9RzrO7yjFkXIhl1U2L32Ci1rvV0LG4XhNujUsCndjg2Ac8Aetv+"
    "oZOE6QwGtxO1j1JMC3w4no4pOXUcdiIjJwKeeHPpuRc2BlUk1nBPbR547oVgX3W9qd0nU0hGNmGgYcfHJiQ8Or0LszHSMS+Rik3M"
    "nuUGxKprBbtbDbvHJnZT9rG5Dl9qTsNhc/PZPta7RZ0ai1spx2Ha4fEZLJTWDwATV0I0k6SoNA1hlJWxp2AqlT8FXan86ThLIHbH"
    "dGhGEerp+JCuRj9spUIv+JigFPFNWbwl6P4+Oh5Y/+Njcr7yPZDzzhNLF3rEGTsjU4OycO/hCG2/L0wfxqEm6hQPz7RorM4c/QY2"
    "V8zUSrp5DDXVbzwUhio7HvEwtCY4HU5b57iVWbkO53Qtaw6iepnIGlFbaLQzkSm7CeA1SGcjdn7EyPA3qpykN6blEGTIZEIzgVVK"
    "2V5MvIWCbkxgwnYAr0h62RNFx7NItTaQ35mn9C7qxey4vfzffMpmdyb3tLaJYWI9MvnvWH9K8Yjp1Wp16e3x0l/wI9PeN1toGYh0"
    "ojCFHAUdeVmqddqUPmT3TslUJ9FJUESFe67z/43iS508TLGixApkzINvlCGtFI6PS5xvvTSU/szCSE21XqnfCMaoeZ0kw0Nlqxlz"
    "RTtiw2jsokKR+AEumDdCM8j1HoSuEYzvSlGlNuwK6eTy5+LIGFxmcybvph+Z8dB1nhkpqp7aW5mQOe0Ev2C2GNPbjnHhRG7dhfpg"
    "P2NuB5a8PjFN8g9rr6uGJXknMWhnHGwlB1TzVGaQpzkCa7fJYn9gN0toQE2U0l9QoIYCOL13xYA8bnGTxKTCPHTrOOXSROpFEPOd"
    "mg+tz4/eFJtf1Y04R2gcfFQxozZZ/LIrSG3tyqzafkP4LDRcpltVBTZf3+/o4+xUbXrOQv8scigIdQCtPIkl4pBo5k/YLYqZngQY"
    "cITfXfW4NTFRn6mzXpLPAYCgi79FtYHAkjCW/s8gv8CvwpgcZ4ucj3H5bQyMmAN2Y/5ipQ9vh2x7RJ9dIl/67EI2GYACnxV4SdPj"
    "OaXHNEHRq217DGQ1qZlvk+mGLbvxtMJQOtXOk2tJsG5LO0zqDVeN8qEnk+GT71sN85HFTFEHpRDm20xtw1a0uVi5Mb/88IPlu9d7"
    "Z46aMnH61iPE28ZcMTyvTDpVlHeax6lZw7qx6K6F6UDAk4FLgomzeZUTVrPNSd8nPQmB7JbgDkzVZ0qG8mbTEKjsSwCV7CNn4CGt"
    "ekfJdTJJWudYwHJRqPFjNmI1frNyR/1CnDBuOFzLXuLyoKI5TrSRhySXAmssjAvqTkKC9wL5KVBuA+OajW0SspU20i3aaOyjpwIp"
    "z2V9PLBNfWwpHMRmoq8o3GCinCl+zqRHlXBkXuGvTaGT5brC5yVxYiL+lVK48f+oVYbJt25xIKigiyDHnWVOf1cdaElkVntTX5YT"
    "X+LP2FKfH1UsFAyETKbMRF8OlPbTo7KUpvwZd7255YN1kaaM680cNvvaAYprE7AKsMyaBWsjOEHiMBO6AWPJcCRMY7JDu4ASTHRU"
    "INka5iFBsRQHZoC7aoIj1oiUC+l/E1XfqXif11qNlG0d2IvvRZbNxWgPlWjPHJFxVMQ127CxnPrETO05X3Fskt4WBcx7VqA9mE0S"
    "VNH/AtEgIetpqxBRumfWc2JHSAkVl4haCkYe8pMxQ/x1qOIxykOWFWaIH68Br2lZdKtw6RdMMFjnvLtxFEPx9HinXB9fXxJUUH45"
    "yhgFEcaFcvGVKXaYZSu7S4K/z9/X4nH80wrId7ZCzDpCahwl78F4mRwlihPH/5mjHpIg3fjYK42B6fZ5zxA9ET+twULfdd6XTDgB"
    "667lTr5tu5wVgFOitQZJYUUgjau4v9iBwTYz7mRWg0HOTIGtB7AbDoFmajH5oyWZcFshMtQO3T5FWZFLwZMzZA7m8sDFgb6yHL8i"
    "4RwYmZ5hXMb+6pTd3bIrjqSbkppJlxT5zyf15s+SZC1gcgFIVJvNljF+M6ihE9BrKJ1bZkSdviyYEVwgjIuAygCmCWUhLL1OEnQ2"
    "CKd3sCWTAqVu+Pv856N7h3fuDUZ2DgVbMNVn8C868tPf58+XgiGVEZqx0x0IMuWOUW2UyHvYjJHG32+AJAXDA1un8MjDLJapizHz"
    "AF9UBYP7xabNBQPc7mRXNrqBTJd1neu0wqlV0TGf1qO9BaUYj9wgUWNi7MxUzLABLSWrGzN6XhIVf1OgX6QJutCENN3YRN+wImc/"
    "qGc9ysQRheXPyx9RYcE2Crh+iV52J/nHRX+TA3EEHCA41bbyG8xF12mWNLcBj7lKqnhZuJfwrkdGmeOGkRKFI2VkG3uKSB954kEn"
    "pRpwknnekMTFb2TLgTDjm1qYQ32EZ221sZJNPVhnDjZSPSKymOEJyavIP8h+pRY2ysRBP2+uNHEzXO8Rko7kitneZrqGwYnK6NTZ"
    "NOEHNOBr5jGRDEpQXEsQynx3TJJmvIKR33NiRpqqSohFikBOUq1I0AAd3jLFz8es6h7BpiNmTV0kuF7UZjmq6oWF0AFGMeG1p348"
    "oiaNmAyE1ryIrz0XQI49Fm1KcuYdfAOlYB2e4k5zgsKXwO9fckRO+Dhab2D4Sy8ZoegyE86u12ni/tW0nY8eZzkkjct2nCPuZ6bI"
    "KGhhJXLrPWClbqwV9dKMuQkBUBlY6JjB+RK2RIHC5SSI4C8aFaw5w8SGxZldzw59iB/IIxYAnrnK1GC9At8XTVviPzaBsn3yIkFZ"
    "eqOTJJjIIANNUuVOOxoLK/vD2GRjoE/AbdKnfu23o7QdUjKqMbQ6JQNP8jMHhjnhrKg/oyqQA87+bGqS6APz2dSrJvJ+URPN8MAY"
    "sNydJjRVH7fN7AoPlAL7HT2CAHGe2mAYjzXrbhw7UZpEYjBdCW8jOHGkrsjVhpE8s3Z4IFObqYFzqOFsk3Bq4J2DcezozjHHTtxF"
    "kURE5hZK6B0nHjxyOnP3r35HrrM4MBBk95hG+IyFGwhacDzGjIx6PVtSCjNXw+w0rTYm6/aumyR6s06Y4V10eQhlJeEOTj3SzLTO"
    "ZqGsICWjlwuxOMAsZZMuKaVOFSO0kOzQzY1FbyVzVZMNdsHwh3IiqrfmBsarL83+V1RXYuQoXEPkxrqLZ3q3FyiENBdI8pfu4R/X"
    "zl53311Ch+7jhysfXXYl1ZZ4nq8+/rB77nNX4Dyje9e/6p7/unv8i9WHD000bAKhMBQrF2+s3rjkPuJZQ/nx2tFTqzc/ct9Fsb/8"
    "+LPu9Y/dZ8lHvb3dJkVe7/y1lQuX1z78ZPXmTUzqg2FCovFWTEpWlDCtXH2/e+yUFDXpmjRF3YUja+9fcKVs/mniC2EEHJtgZnnp"
    "ePfSN4FfOI0ihjYD9D7+2gOIw/1KtMiXOfTXPXlfChNjBd0788nKuY/lq7O86x37oHvqVu+8hRcropWlC6s3LpqPguu4HTcerTy8"
    "Id9t8hBc1/Pzq1cO9n78uvfOohRTIiFXFbt6MG8bSCidkVMpAML0Dt50BREuPRzQifoBbJ6W/h8PPnUAskUWZGXpg97n53mnPMC4"
    "NRQnbEcyy+R2zq7V+a8xFAHu3pHDvR8u9s4f635wqnv/w388OLd680738ELvq/nehcuWfPzjwcnukVOMRP9r/m3XiUQqxQxPdrW7"
    "C2dXL37dvfUpDGpt/uDqo0eIAjSCkpP8Cx4vvgcg3YVbtiuJmYYeKHYXVeBCrta7fkmzpct3r68+Pr168SQsgH4A/C9o+sahlU/f"
    "6d653D18p3vpp+Wly93F4zzO5bvv2u8Ic/jH1YMfrh16iKuje/zi6Mr1R2sX/wa9wDqsvf3V2tGTy/cuLD/4tPfxo5VL91cff7K8"
    "9LB7/wM4Srw4NHqHbbnh28HiYvfvrffu1e7CbT/abvfebR5oZmLQMSyKrc0js0/Y1ZtLQJxgmbHKkcPdG/fUQKdqNubh8t37y0vz"
    "y/cWACOW715avnvNtviPBxdUhS2tyrQvU4PlgNq9m4tYafH95aXbUGntsy+7C+e6S/eX7877jZ2EiSzf/XD57qnu4YOrN+5KlU9P"
    "r55d1GC9Y/O0Z9fgmMGIVucP4w6dvrny4ddQahH6/ZN6Ebu3vu99fDMzAZgxrrUaMiwGd9u9eW/15me9i0dg0ZlY25XjScDkVq4u"
    "rX1ySa+x6h9a4hMOGMfI1fvg1PLD8/Dn6sXLqz9dhR8rhz7u3vsBRspEhjFo7dPF5XsngAh0L30P7a2c+wk2Cc5Z78wtoBowT94n"
    "yn1mKJ4+ZS4vmvNf6h7+PgBEOXUHl4/xYDapAc2Yw4+ZGuK+hHVmGeCpteRutJ5SsMB6RVfnz/Y+O71897O1L3FBcrWUs9S/q6ZV"
    "56kaDAg0pnfuJ1guOE2zRDxtejmgkFAb2Y/uwh2AyHzXZIjPh15YExHZwVP/HoW78wN37QDDyivOL7V39ovejx/lm86PFF+oOMzT"
    "J3vXL/sLgEXCHq18e6J76kduz6PMQBJ8xAY0BhyCYwenB06yIwPFi4x96NUAwugYRz0otSiieu7eOsJFy49v9D68lyfnGl7mkQeC"
    "FekdP16IDnyskBjSPQoHzR1N6hgP8flrzMjwIGBJ+E/oAqgkHG642WxFnJNtXZ2u3M30rJmpxeDLLXmdIuvxgsE5lyp3fugePE/k"
    "6tNZwJAE7mF9qAsZuz6YGLf2thu+7zFtEV21lsVQoGUm04jhZh1XH33QPXxZ7e/5W93P5gGHVt6+1z261PvbCbjjcQnvneieftcu"
    "NtAqurg+gcsPxtU9er/39te49jRSNSHuOJGcXHZc2Q7zZ8bOyzs3qpOCKrab3FHrfXa5d/+0qUKxmm0Hq48/ZqbHb5eBZMnscBH1"
    "FDDMVC5tD+LOEmwcEvB3bsOq8VIy1VFLIx14yV1Yx8U9MNO/vLS0/PCjTG/uGBBjtvrTle7inWf1JzFi3cJSLyvfXemeXkCm5f65"
    "levn1uaP9T67CJdgbp1NdVkRPge90+dXfvqSeYjewpne3cNwK+pmkCCd+rG7eBOGuXL+BFOgHJaYcP/9aeSC0Mh/PDiGN/fDD+Ap"
    "wfcSDvTjmyZdHddFvkYqwrm7uQo8wp0fVh8f7Z2/wL3CGxKYscQlCuUx50qGbREOIcbuFYyN4ds9fWrlKqz1weWHp+TaPwY04g5y"
    "nJeO4ntg4Uzwi5UHZ+AbH2C/CeOeJitn1t0A2YzjvZPH1r48v3rsh9xw4SXLWcP5kYGrzJAKRllcAr2DXvz6u1QIH9mnLJS16Vx+"
    "dA6oaPejI34Tb1C5a6AIjOyld2aYlyMrS+/oVYFz7IP03n2/e39R95bQHXnqqP+5EtH3tU9OZb7X2+a+WTjaO/UlV/xVDk4Z8zJ6"
    "IcF++H7v4ld6P/Alz0+c8/O9dy+vPn4PMC633gIm/XJzcJkC08igurJht/TRcO0Aktic8HzGCjrjkHD6CGZX3QSV5vXGa/bsFzkY"
    "Zbht4Ritc6AKoVyTWZxhUIs5rs0C3MB9L0nGQt5xAOTDlYXSyGwgc30TpO3awvXtWqd7d/0f+2b5IVx08OBdzFaQsHMO9s4PcLcX"
    "w5LV91i2xtqVM73vLi4/fAz1sjUwdG6uAmANoExxhUkJYOnGQ4QSX7cGnmlJqdxgydLa0nuMR/K92iYRy8rBW97nqVqdGl755KH3"
    "ndPHr9z/0vvaakvQ9943n3gF01GDg+itLb2T6TYiq66Vpcfe93KjQ1f0B595nyc77Ukm2z996xdwhvGVH475zbQ55m/vq4+8781O"
    "I60jUl76lL8zsvrJMOypzJar50seJm7tdAcJzpk9QlwscptdCotJZmNR2AN7w6IwAWn85YTXFAxdj5j3GziELIg/aA0m4RlayLX+"
    "SluK8XcJQc6nIZidIlNuZHpKMWYVbasHEce+t+XsWco3YjCLySVtkbKOR4Y4DauJK4QrOJLhPjmLA/6fdwJ6mU7pthGd6HwuLt89"
    "tXr7R1vEASWQ+7h1BCbZvXHSdWuDvuia/yCmduX+Y+Zqgtm/uH5kI3bqRYCKvB8WanI83ekvEwUickOKR+SEZg4mxSZCF9xETy2s"
    "RBUytEXu5avDyKjPTsGCRA6IdpXmIRtJLWWAgIS8Ii4nyw8+7h5esNTALzc31fl5gEGBw62DIpU6vMAriHzi3XkWC3SPnIKPcJvZ"
    "9xOJzW4vL52xZ4HbJ9eUPZ54FwklSUB8oKFqyyAnwMACFcC83kCUWb3z2fLd40A6RZACK3T7MLB4GKp0OqH6JNA5vXbkfWD71j45"
    "7bcic+U2el8cXb1xa/nu/fywFEOgWYFmFHcyIhjJ+IC9krTHQNH5YeZt5eollJoS924vCQJiR7De7QVYTLueplDSEa1chWfF1+aj"
    "DIxwSQ+qE6sSUkH45Zzik58ovJf4RP3uUa5X41BkFye/cwRHnMc2A8zsBwH0zl6GlTdgKAjnx6f/VqKHvF1RRzMtwaSCZFxeCLTU"
    "vI7AkleZITdLKLuEuHr4RO+jW6aIgtUY/o9KUHR7cal76ery/XeDjcBvsYygd/Y2CnJJjmOHydyYa2hHvD9sEN2Co8EPaNNQwEJM"
    "QcVNGzcObNy4MaBzgb2qlpjVsMoEphf+qBnE8MEMYXcpM3mGNQdYBNrHM3VwHEfnaeVOoqj19LfCXJ//bvX+t/94cG7lm/vCkV/8"
    "llbFb75o4mrc0OrqyUPdcz8BrsBSoHREVkC1BOgnik5GQX4fmdKoUjeJCuG1tProPb8Y00DZ9ciVmCPNwp+791dvXpbZZHAO14Fq"
    "45Q/+gRm3V34pLvwBWCuP9L/TvorHqj6vFWsq2X1PrqlDrIpdmvVu7kIJAafwNQOCmNhZTZvzLL7OPdW2zuflo66MiObLwbAfwwE"
    "L2DmRha4JCU/7ZXvvqOHR+/6ZSTocLduxt90h5gcHarGK84cDZ+pJ77RNEPBmaxeKB7PDvBA3fiWocD0/LGCJmKKLwYnsKh5ii7m"
    "3oa3hCB8+k4BMKa5yQhv+gNSMJm+00IIwS8W4SMnbnrv/fA4fxPyCw1FAXe/6d6/0n3/JAsQvc2OW1Y/nxmolUqpE4/aOFQFGAWK"
    "15SyFdREAi5kLXSBPSbh4zG1pLWwbUNB60nAEJCnuP9ud/FK99KZgOT7FmORSH54D/U8Rroa9FtokUrDNfPFnbX5t7lRezq9WZjB"
    "CN/3tOGI2uA/b0AkA+s7pmG7QN1L7+Al/+/rzt+GtUMPUYn04YXeRws+QvDj11a1j18pt6IgKwDwCoZtiSS8cITDCRCIcmTrc1gm"
    "C8T6raKmKvV2NG703SzHgNfmwlk9lPCASAXu3YZCV9JoxdV62qnUYyqGt2/31qOVc3d7715WHURxUqdcet2bR+Dk6NMyM0OkrXvm"
    "Tvfjn/hgueIyP0YPXe/eP54ts67CTulh+C+zy7h5bxowexNmwepxPTUij8+6V0/0KTdKGrpdSIKCJKJv51rwkLm09eq5d5Ta2mIG"
    "1dJSctNZvnsCSAaQdrVaLAAALiFbErc4a1tihcSM66gKPH+N9RgsltbKY0MoOYwpzOgvnTo/CruPDwM/kQdJW61dHZKfMr9UvKAG"
    "WjxlmansffGg+2Cxe+VtuEc3/2bDpk0bNv1GkcJ2q0kvjXfdN7LagUPqXTP2ojKU3JV2YjyKFX5zd997CAex6Fqw4TCRuF9dsLzo"
    "pi3ABGDtWcPSwpPk1hF7I4rWHojG3k3IHzJBt/p7ZEyI2+/eOASEYvXqV3AagWLmLRR48U2Wesf6r145mGV7GDfkZoergXgCuAq6"
    "p8/+48EFtKN4++uM0FM4yXsn4C2GVAxGc/cUKn+O3l959xYqqEjMDo1nxkFMTMEYhAeSvCGkZJCl51EAswRsEZBHeC31li7C79Ub"
    "F/22O3GDpTz/e0sLjf38pYUZrCxdXVm6zqPLjYIZRGnv3m1ujGtjFIAoDesNI3W1A7RX+8onS/CyQr0EGSDxNKUSpziwIh18pBJQ"
    "HkJJdAqg4tZuOTgkNwx+HXTf+5q7t1IAAVUx5ZkGsVgEH4nvabBQvLaNlUDvs4vWSkB6Ae4WvvKEwslJUtLRswG1MyjpCautOVU2"
    "5MzBAqu8cbYJDevi4OukqCTl+a0cv92bP6hLPImVlYNZlY8MeOEMm5konAyyIj2TpZuMucxIWKFlQEzGqthTKXZvnOwtnEY0z++w"
    "bw+4evNK79BhvcoJ8YTwslwB7nHxprdVYWp2FY4JHJn3vpbQ1myvJlA6D4C3hX4OAK/IvPrtG1+++9Z5Cj6cToaqLSd7JLlNQbkW"
    "PGZgKNEItX0HCLv77l70WVRVckOxkXJlGIpHvVTy0g3V+ojNEsKrSML7RdVPaAPdM0D33o/dz47STeiOU2ZhJa2FQLxAB44q8yys"
    "NABf4Uvvohbo7DdMp7CDB/NwCeIRgfdjJyJ5oEKJEZPChtuyNIXsHrA/e/5d7kibWZJxyS/LHhJVJOnr6NlykTHZB5CkkjiOs7f9"
    "IpWHj2sCxNrZnzJ9S5rN7vdkfYaExWqnrYDUllhDS4traxfvZSwuc5AK6/pBmznAxncPH2YJMpegEzBH4GQbLNa2Z4uNXOnmvZXD"
    "V7W5QWGlAmtfr0BaY5pkbcCAf0MZwsLRlWNHbY2kU3ZUk8vw5Q6Ed+X+veClAB4cMGG6tj/vPj4EX0QqDUC6QdgaFtspSsfBnYd2"
    "japvxBjDp+C1PeorMJhRm/l5eJWtPLyRo5oGYlTMMxhMAQAeNWoSiNhew6ocBeOvo1pitgPcNVw4Vx8uPzwlzxINhM+fwkJAg+3P"
    "HGclmgg7jXRY9I/KKLgAYliDZHrDi8SKKAyMfckZqHYkjz00ziIGUydGlW1IOCCFMPcLR9YOAxRSrrlfmZQY+AamOet6lcpeWCq6"
    "XRasrBeN7HD/4M7rswRQb4h2/peBv/dQ8FpqvvsIAEXbD3BZn1b5bWlflUUryyAyZgYLeLcVEEmaJeUvUk6704E0nO04bqWvCB+O"
    "loHHHsFR6gtkzvGNQ85k5MtvWSyIK2ZeVv7e8LxpY/KrSRAGE1Aq6tJxE5uBODvXt3Ynbcndw7w5VlFGcXYZxTANZek4QRSF3Fxc"
    "uXqqwMINrWUXzqJR36Orq4/u9b5YtEVIEU4cY84LekKivnDHNH1CJCaAg3evIF9DVnRGxPW2GjV01wkbMu7lpcMwa+Sy3llcvXqk"
    "e+4Ris2+uNc7dQPmw/O2hkYoDVk4jaJ4Vok5B23cD7YJMlNmibXfc5b3ssC4ICwtZfMx890aTDlLZcIoFgJqQZBCddpvaa4Aj8UC"
    "3oRVZyu+levHuo8Ou8Efv9x977gldGLi7jdAfuJPb4AHa5w++FXiHSO0kV56V+OcPlewqsdRKkWt8FbkHjnc3Ig1XZcWrZ2ztGc7"
    "eEqT+FoqpdOTHmld+X6p+/kJXbrFM4eDo4MizO/nuxcurDx8r/f1RXj1s/CSasB+ICtBJ8SaEcJ3IJBtYUwW7gBhNd9VWKfuzSMr"
    "Xxy0DU3Wfx9RQP6RHQEUrb1/OVuH5MPyPIbjaKcAh3KkDdw/YSrbh/utcsXPLq8evRa8Pp5ycnM6/0OTk3CU6QkbAGBi6iV4wIGF"
    "pfuDTgtf1Ozc0b34LfAp+p6kSuiqTgNxzKG9evARLj4owe8wmgVMaB/8cgPH02/M6Xgt0UbdrB+ar9J64VHip6spAuYBaQOVojD0"
    "4Xmkc24ZWVwEu9g7e3Xl2ILrki35DCr1jh+XNliaSsal3cVbKx/+bfWd95bvHrc+At3Fa0j7zdyYMBhbQlkHXGbRNforrlYhu/i4"
    "BOydwANHM8Mrb8N6qyZQaQZtvrAxWPn2ZnfxK9R43bxDl+tx+2X50QkUTG367ebSpt+8UNpUen7j4POsBPNnC538zNmqIeTmC9dE"
    "bThK9bHqnXh/Zemz5ftHeEnR+DCP150YHt7jtbDciKQ6G18+/rz37uVgtj45h7TaotCDefg/NmkOtKKJe/hFDPdgAfMWR0ajx3PU"
    "J4d/I4EjSQjadM4voXjp8MLqzS/Xzt5gRSWKaY5e6x4XMLTTMIIoIYUf3+x+cE1Lebhl6ALvk7v38VKnIwTUHteWNrZ34TTckk7U"
    "vnite/Ie0izkt+ft+x/hb31PfR23Soveh3jVWmNy51F093gR4nj25uJlcueHlaVFVFNmloXmyO8Rxi8Uw5Akje2tkV28dMosxcnu"
    "6SvdBScuxrX68lt4sK3cOLt89xIw+f4Vto+DgxvGYvEa3uaA0y6OCi713SveiNfOHYGrmQUVfOAlxnjg7tNjp7RRuBneQm5Dj/3M"
    "MXt+Tisffq89erh1dQjKnTQljYRlGkxJQywhbnzOb1QmsGJvDHsQPCe+idZ1RB8s0s8/hnHDMbKOj9yEtduybBg9Lrv3F5HDQnNs"
    "48/lGBkUwgL1PvJJwSF81glEHIdlAw6MjiJyY5feQW1Y9na0t62wEmI/RK2i4KI/R2EqenECjY+aHZTxQABACh+2YyTwb19eGqun"
    "NwviF9OtCIwdmVZ/ak84PJWBi3UDoVApdgv099HQKj2YikIzVpkPX3onDyK5XvxYV+pzicOpNVCZtwrPW98tesZwL9qxZZgC2JCV"
    "pfPWUB/tTc7PsxNXZsf8e8G29x+9CKOK7wYGywQXiXYzYDl14Fs4+lWNhLBv5aykVKrHLSsmPX+NQfMgfZ8IJ5np8frj14G150dv"
    "zRufr31ymO3ikAwdOtw98jcyaznJq5C2w2nSBTkGltkwzbgTELlisNbPfHI5YtFp5avDbJVJRZ7w0cyKSgpiAotfEgr0JucMHC/B"
    "3k3Eo3qUzeoOPLg9dNAKQbWfRhNoOHkf7XcSNL9wvGYsc4HUnfoyU+iZkHtfjU0JSs+oVDduWQIFz2pHfreyHIxfVVaV5B4NyDvB"
    "ZeMuINzDI6fwLFhzCroNhUmA29n3iTE9lzuJdV11zYuLsBGLOkgeouqWb/jHn1gtCovL+DGs+7c6K7yf55FDQeJMgltBrbPoP7P2"
    "9lfMR2TGOBKKYDu7BtLrnR96n77dPXgeqmVH9//SiLYatFheOgVPYkYOfBX7xkMOXjBFwD18Mdou1n8U4CACiKzFTU+e7MePP2Wr"
    "PQzTl1MeJfmOImjx23c3GZFkPTN5gNcp+pv16WEjYCeV4WJ/dos3MzIMYJCF3TLg5DSV8bZCqT21nvGYk0oprEgsSYzwvocJ0oua"
    "rUqMcR+xW+R6Zxg8katb/y7a+NXH57q+zF9y9wCtWzv7gy6ImVl1Wn+5+c+tXjxpsdNrCY2PRR4HwHBFMPOXh6yhPn62horaRUBF"
    "TBkmbJeGakpKsHyJ0RQYg7Xu92+LwZqRgooOwavg1Kd9SrVOyofwVSbBbGXOq+8befuFntrE+KXl1See8iTbhlGfaL1ovglKxCNA"
    "yNO5xQHq0bv+pYblyPdOx5nHC1KklnbvHR7eMfyqxR/2DcgAjezePjK0ezt2e/RI99LRQqDRnTu2cktPARoZ2ju6XYwBiejlQV7Z"
    "Mbxj9DWrSCoAGNqxc/s22qzvV3+6bJWx1sHTv0ZsOQYW2SbnmZ+LSx/0PrvA7wQGofB6YUIbZZ6o9i2TgeLAMPqh6gO0yB8YH3PQ"
    "zMOPbGE7kmyZrMBD4u7XRr2fSXwv3j9357Wq3wMzlnOsfcxaBcjKtLYA9mk9GjwGMr0aGF+DlofTmj4gVmaPzNySTiPdy84TmfAk"
    "FiiDxiZ7s8VhhirDaKyBNw0BVd62uBNXLKPbe//S2ofztsgo8TJRTJTSPt1iGseh+fPDhrHAb7Msp9eHxa/6ruFivl9krkIttZJK"
    "loq5yrX5T9F0nJhLFkeoebTYYkALqHXjDMDZGrVyRLGIdsY7KqginaibWa/ePNJd+NZCkKF7rqWMAtuHtmnY7ElBTl7L1Q89lDcy"
    "vYGNEnxhIyqkgOfoXvqUhYK2XTh5W3ih7QuJnsgc14hZNSsLKHLEph23nBFL+1dv/tT7WF4P/GjgQDm2y72840Vdukf48S+65z7/"
    "T+t1Kky25PBbl8ZPQ1EoH6pUMHEF4bkdnt+ABsFXmQ8ifkma/UW3mbM/OZ//u+6xCZS2++4ScDv4AvlxCWdpNh1tlL+4i5Ix5fLA"
    "fWBWiqbYrXBLykiG7nOsAWvM7z++opYf3Fq5cZYled6h1G8SOpwaH+ybRMEzwy9XoDhM3T+CVEQ9wVmI5e8n8N03DvF66U3DRiXh"
    "mV42YIrh7b7y0SfIuPkknQUBHEsBmEcMZQMPHYXDDg0rdjep30wQDQsE1MZsqQkYAdCSQYTS12MA7FbFqqPJDIPdNDIgpec2unvj"
    "uY0Bm/l4EL9VEL8thJg2D4Pj3Xu5DkLSaHQPf7126GtrD8IQSZ0DDoqexIYogd+zaPk5F6z+7Y6IRhUrypUn6o3Gjlgf2ePHta7P"
    "viZ0HBOUA3PsHcS5Uzcw/M786d7d06sXL8MQXVyrpE9UDq6sl9rzQNIWR7IKxnbHnvD8VMZbiWeljJYz579TIylyd6QiOOOcZqL3"
    "t2urP93LODrICMbTId6DU1/wNmiPBeWtyMvabjX/tVXOi034tQpPs+7xi70zR5eXbrt9rEUNCntC8a/cysRk41XxnGqBBt34dHnp"
    "TgFUxrU2B4l5BJJRl3yR7xV9QmQKJlKQPK2JQcRVP3UBZp7ZmeFCa8sMRB9rS4vnxeZkXvGz7cPyOxe3sGaSrabNSP0oNlwtrdWN"
    "SSegEZuqCbrAV2fZhgT3wve9k/RgLxoIPMl6Nyho1q0jvZNH195f6L39HXBoSOMunEZ+9Mbf0OFMxfrQ42iq2BK2cevrnIGR9WG7"
    "jlMMpfx+fWC3aRa2EEjtWx5QCfvgaa5IpA2Ipyk013GxstDj1a14a9Kak6Ej7aVP3dlocVSFjEeyjGCUS+VKVDAZIYEQAmer+99Q"
    "gpvZWfPyxbdrYakMnt62eMgUBB3hLdNiXEoLxaQuc6YJTrxi+PyxsBzFUTADArbGiRlnSm6BAtImzvru1Be9mx9mSqUD4CfQwdLe"
    "0krwremQDf/CpXjZmrh8vQ9v9t5/DzXZR37oLtyxMjQ9IKKh9Fqju/Lri2ydoAuTzuSkRBmiBjPFk502CdK4E+it98GV3onr3Ysf"
    "ZgDHw0a93LYBAr64CI9kdwtYBxJR/5PtGLPoaHoP86MKHJ7J2hYjl3Lqo5UT32FAubv3+VSyChU1aw/P89WQm7GhA2yYo6g8qjuN"
    "IjUoPdecCPRiM2eWa220RVZtRjDj+CLgpM4fMy9Sa9OjW8y3JWxBd/Ga3NWkomMOKmNWLdVa7OjOU+UTmL9mgZxi80858PmlAlKa"
    "tih8qlwm7x7pLv6QuX+HbdceuYpbr7naTyUxhZNCa3bP/8UrmTRSuywr0dBRUvqRXQSz3lHW+UaVmYWiWXlFwqxkeJQ+w5lwofD0"
    "I59uZDJbpSuZzdgdBW+1lak+PRFtWXRADmL35gM4FGh2snX0DUne6kVFQ0bSRlzF/OjAPYj7k0RlWzy1dmUBX6GkB107e2Pty49N"
    "0lvyOHWvbhNJDMuqnbooKMmH+/R7MBRdJE8OxZZmfQRFg7L4MSziUwIgstJPlsEqbdXbevWrwxwIiwN2CvLAONBl4VUZpg4+6w22"
    "7kBoekgcz91Fff/8MRT6kBBa17OO+64jF1PDeWySp6zJdhy2U4kpqthXuwQSPPWn6yvHvll9eAUjXb2P5h+9M/eWHz32WgImeDRt"
    "sfeaaopjPZDL6wm2ERNg4xf+8F24QjD6EiE52zHYC0pH+cE7wwY9kNAg8mpzkSLUDe0WocAfTH0ehktekImvSm0tLpYpize5Jtqz"
    "GG9UclO6AqhqoodmuttuzPPIJR9flYdP0BA/wiAKn77Ds2LejFvPNbG1OOQNr5k7lLkKRTFw+lca1tqTZwHv4rPfXbxirg2OPIog"
    "TLBcSGdHt1xhJsbYqYsrx47yy0XvtQnLdV+iJdv6LNTigBF+AbDxIrFd+eQRMsbMtDiAcossRzhArcHDcJo1Cpl4ra4sE/BMRf7N"
    "HBJvsMIenfqIXXCJ9k2R8dviSfeJezBOqdfOdhe/Wn10aOXaO2K+R7Ao+lj8mBEH/iT3FLRQW715kBmQ3t3DvU9u8c3tMAhz3TYk"
    "MDcOz/9s/BmUyBK5IkvD/BDFmYDEqp1RP4a3rZftTexuc+2jKY2il341wwCRmytaR7PtBbAY5KEtxs+L1/rZZKjRtiU1pYRAIZrk"
    "lXkxOvKBZ6xkqPchklsKVfENy9HYS5ZC8Fzjj0jAFs6QE9E1bgoAcLTG1g0P//ynGDIKps+xcN6moIimO14fiT787cfL92+giScZ"
    "xgnrzyY1p35EnTK1QBZ18xYA6vZu/23l3BkJQQ0Y9PADWO2RoYC/ByNDG7a+opYonGbHtm/UBxY1o/LPRu3hKQpM3NodNTFrVJt1"
    "KN7Css3OrlD7DjTn3KoPZy3DaeBuRMAliZEufncmnK/tGBl1IOZ8oryR7L89XgpgwkqFxyDm4bqMRmFt+XMnnKX+zpWLAgix3DGP"
    "InDFLS8dXvvktIqYe8zNxqg7nAzJeCDZ0tdje1ozUIwtdtLtKsWo6d441j38NV+20Ps/u+uVQYzrBGbLRC8TnB05H2kRAqOvkAAT"
    "QIsxGK9RwHt2OjXXtETYOgsH7z3g71avXwHWzE2zHE3ABTGaMlvBtg5sXaJnKmp0HQ353gXzWsWw66ixvniPJ29N9rp3Lq8eu88M"
    "Dz59+I0f/E68rHp/O9i79RMGCiNLTjLrI8su+z61+W624iD0bVuUc4BLWKf5ugRJ6kchM1p9YmdN2k2G0P56TsqKnCzrnviYS2xn"
    "8yhgvyBNGsVM4CmmAHR3fKrA0V5J8kj0Th7sO14CrTG/KSHe80Bot2k1SrqcN89TRizdX/n2hDKzZObKrTqqZo2gntSzPEDrYqix"
    "VJwXKGpzprpgecYF58E8rAM3i7Z9x78OEFYS/Y1Ow/u1gsZ/JspIYCxnPfeUM7e6xy+sHnqIkEsfr964xLa2iJCEpWIzDBgof//O"
    "5R/MdUc6jFtHAGlZhWq9CPUDQ6LK04g1fjIWvlavVChcl155IEC8XTjiHHriLeT714j9EaGB6yKXXMN+VFRJHvuZS54zAY9P5wXk"
    "BYwRALPXOEuItWKBKObCLBqEzjlSZlo3FzQ37FfzXm3sroyLkQViBybnfnX02ur9b60tKKLbT1e7d9Gbgvkipi/8EdkMDkH24T00"
    "F6LAzmLsfupLlOOYbvXaCXrbFZNzRRo8lZkAdVMPPuWQBmyGoGUZNsGCaKiOnGKyhsZjSlOCSlCgLh/9ZJVydhgWbzIbmEcd7hHG"
    "Qy9LHIlrCjOxiVyM0H7l2AJsRTC7f06T9r2TRiTC+lZjvE3sQsSpTlzNAB+xcJHcPYScIAmo+U9WzNrXYpVlLN3HZ1kkRYabYVoz"
    "XbukeUgWTah5Gw/ILIZOqMNJOjjnjzCd8BiuaP3lh4+6Dw4J+2k0lxqU5Qgu7HdR1xjYgmJyrFxZgn1DfKFmJa6RgfFbJjmm61wK"
    "9wE2ba8Y63FGFw4nht7owDNzVN+xhB1Ykdj4XvZOsrFwhCWRHOCZ6tbjMQl3yDcEB8X46jBevB9cWzt60gAWhpumkqJQ1lTAYZDG"
    "xHCcHRSXl75i23GCqNRh0HwHI1V8ZIeViSnACnYqYdspy7MwNex9dtGUq6iFigZI+EKCIEI0VnchUjkWuBt100QrMFHtpOF0LG7r"
    "oD/0GbChHY5N1KNGxQsbRlHHPuteOtO9frZ3428OPBxPx6yMb+WHRysXJfwkkMHNA8+9sDGoasPRYHPpuReCfRJfkNroHxdbW5cQ"
    "KOzt2ISEG8UthY0z4UOV+eJxIdkqHqkL5ED7JIEoMk8VGHEm9Kd9IqnhYrq7uJVyWAkjaFCiorNFOTIM60stoD/6WH8EpOK+WEil"
    "z0ZFArP7khFFWRMbB/osPCQgP1IK4xm8uH18JMj+1uoeWOG5MNmwmBR7xrickoBYMFGOG1hKMCjp34U0kr2IzjWBL1/VgiVY3AJG"
    "nvE6ozqFnYkTi8Eh4//yqT0t+2flnpnT1azGWJRZxqTQAqgU9pkkFvKIoyGhqBDmdughzzMzDWxjS0HiB5EKwtTu3n16C2bZ3SWo"
    "Fj+zEp3JPa1tEnb4zg9oXnN+Hq5Kvhul3fZ46S8dXNyWtqMAnAe2jolyPgOHXFNQtdMmjHv7a7IS+HjlxkXf4e38qe7xi91P6KGx"
    "d/dOqSVhhHjB4BulwiiF4+MSXtNbGUpxYYG8qtZHh8vQ5/71DgepnEdt2SdLbG7pinfENsUVUx52rs93mKmLUdoocN3bN1ZufG8/"
    "F7kVc4lN7IYYQvno9CDYVs7rAF+HW8XrycRYDawzdLB2DfbhoO4BcLg+QTn9qEj1bHLykIYD9xtuh1z1/q5eajEYn9zIAZoGb40c"
    "YQoFMLwJDKS3QoPyMPM54DLj1VV4xroKg/EmFlbh5bZpo3gY9mg7mKjCY0Z2tQh3CmkKPqzUYllguH+2Kni0sTQ0aHaqNj1nAfuR"
    "HEGJA2g9hewBxy658TlMsTd/1TwYJbSgDAFX4LPPuzc+Rr3J/ff45MHdzqVrn7I8BT2omOFDDS/BKBM49B2+e0oCItOiWudvdN/C"
    "tJ7WtPrm9dWv581XEw+bveD9Ms88ml5f9NxK5QFGMPRy2B5XG/WkZr5Nphu27MZMtK122ql2nlxLgnVb2mFSb6y31ZAJ2p5Mhk++"
    "bzXMRzpC26JOihk65dtMbcNWyuhyY34ZRVXXgcU3ZeLaJ/IBeHffuQCrlckPx1P6x4NzzibyFJoBnDwI68iFGEGaYz2e+B6+4HuH"
    "8ZLdnyjHW5BLFAcM8urf7mhKP1WfKRlCmA/Ta5XrJKRA2GQf+Yit3vkRIyka5R6WFAR6xM8FkSHxsxUmubeLMenmWvb2k8uKSDBf"
    "ffbKQs7k8GXbtJsR4U2JrAi/+3L18bv6pRy1PaBNeZWrK9xMLNchjuruPj/HtxDxwcLHuMJf20Ite3PlzztFrp7xxv9TClw02KJ9"
    "ZB8UI/eaZ+8Yt6bkRag4KNQUFPER+U1h2Z6SiVzgBfcdPe/dzt6Q+m5EfWuWJB1zg9usQ76THp7cW8k5FoPqoBm4pJOzroF+Gknr"
    "bsF6BzQnmb/ae3dh+T50DIfha26SsQEVnAcfdw+f6i6ik3xv8TSsN5xXcTi/ead7856s+plb4sN7+h18XR09wo27oT8nqdJ+XoAc"
    "EeTcOLS89J2NwOPM595HS3jt5o/dYlZNFJdrFFm++yFC0h4LDXJ8FIk43Ah/HXqqLmM3nQ8MRNHlligSCE6Z4wTBR9g854KHWTOH"
    "4unxTrk+znvIu63DiBSI/Yzyoo/8lcZZtqKc4O/z940ME39aKebOVlgJxFFXJa1mt0d9UOzhlhAMNpGGUcNhj8+H1qrMxoyAdrTf"
    "TIETpepFH27VbDkv2sJoFCTLwlDfJDPEzc7Z4KpGxu0jGvP/MInjrp+qDKW6bGu+fP8cW2ZwflqrqEAUPYPg9qKH55Q8S3K2HxKe"
    "jkXYhtYYX0JJTC7XvKWmpkBuS/tOuPI2emmy17YTR5DLdj5wVYY0+l02mfnlurl+yZFKRTrvnfQCyHtg9iF88piKrcUApgkj6+0X"
    "LwtR3j+3fI16h5Z047AEf58/P7p3eOfeYGTnULAFEywF/6KjWPx9HrGge/ok3vZaUpaLzw5kxF8VmosbrA17XjgUVEdRlC4tAuCo"
    "JwVD/MWmzUXDZHmcO++5U4GxPfI6qoUzjg5gaOHFa5KIwYZGUBuL8ubPb4vvs8znfma9jd//ORgNjF4nNYCBQkX8SJoV+BNnTjiP"
    "bNyd7+VsKUVLXmqFNww5s3QP3y7CRyfv5cRxyMHZeH1+7lGSbc9Dp/m0pIUCW7a98IRQp7h50gehjwHfJ6yXNNyhkRbD7XnriBbu"
    "FmVS9VJCwlL5+VsxQYBlZckGAO/q50229iOHmR3mTN/2XrfUoSMRy9e+/Xjl/tXVW4d6X1zMldu0K6LQYvSVbK1LV3vHHnt58HKy"
    "KLgT144e9fQpksJj/gFpRt5Fgye8Au5y5AfWWWBPxnxZsjpQLGfoz94gGL7jykFLPaHBDC0S+Z61YVGpC9gqneKdscmDPcg6+wIe"
    "s+7Jw70T3+GJ+yXdsfhttN6QAFiSRoXTJnGjbENPNgT+eMohic15FrA1mSJDH65fEtMNe1Mem+9euA8DL1xgRBKaVu/EZRz+zcsu"
    "la5/FvEU8kAtNWTxiZcFMX+GcHBD/P6zoCjHlbfgMQW6L5q2xHlsAsW4ZCNNsp6DaA5AtlYamoSKnXY0Flb2h2It/O6J7vFzwPyx"
    "MUBh2+0obXOi3rFGFFfJYKt77vPe8YdrHz02ntFPr5dMRkwYuNr8hadUa4YHxva3Gp0mVK+P26pkn3wVsefqzeIGwnisWXd9rX0F"
    "3PxRBuUoxN1bi0V1oL+n1Ll0NXdOTdodFUIHfgPqMLpZnOBTom9I72Ay5TXHc8HuGqZCVduCZCw3d/jYAuwcM5JLQA2OMCFaApOj"
    "I3dQO0n0Zp22kDE5X2Ryt7x7p/vorI2a7BBd3RE2Z4OY6RybdzFmVOhIpMJwQdL9hbwWrNhdybCtW8sPZUhLQt6aG2hUX/rjW1H8"
    "1sBbJOuAf6ME/leJ4H8ksXjrTwOd6kvRS79rVEv1eLzRqUTJumj9QKX60mwUD1LdyXTQVI+SQWqhEg1SIzO1QWln7sWJTky4G0xU"
    "oYVZQOZOOw4w8GJrIoj+y0tvJSlG1njrr3/9L1EJfjbXrX857jQag5XqH82HUtra2ZqK2lvhVMNfyWSjnq771R83jP3pV+v/uPFP"
    "f3qZaszZriahq4HUdtbBnl+OBmEE6fqXX8bRO9imD5u+jC7kk8CnROt+9W+z6/5t6pfr/23uV9UBgIrXv/S7OKgj0CgNel36x/hP"
    "6wffmv2n2Xhu7q31g5Frt0btQh3TcvzSSy/h6vz1r/QL1uvlt/5pNp37t87GjeHGf5o1k517S34MRr9M5/aH7aBahVXiO7OEkqO3"
    "BsZ4H+pV2GqWVoVV3IVWFfcggc8ieBqvzg3sr760DkY+q/ZimvYCCtSAy9V162cbURpEL7WrSOMmXqxPrKO1++tfIxwyCtTeWi/T"
    "iV5M29MCj9rIxmjaapNndpTuSKPmump1/YuZDeAW5sYxQIksi3yieR6ovrR9HQ5j/cAo/sRNXT+wtfrS3nU4AdjVA9USxSiHcv4B"
    "oFOqnFtTpW7Ke2jKpkRPfDuVHLAlsGDwgabnpv2yN0c2/zPTHPTKEjv/gWi9zHXO9fZ7D90A+8aqf9wqff/pjxHgcr1K/yCYq7Yt"
    "i06/XxdHU8GOOG2URhqddtjY3WnAITVNwSmJGtF4ChiPc2jFEaFbNIcW128Nyk+0pX7r/2HvbZvjRpoEse/7K1oMPlzghIYa/d7N"
    "B9uPRM2MNCON9Iw0nBcuTYDdIIlRE2gB6CYpqh3nsC/CG3H+thF23PnivBHrDw7f+fPdxUX4w/wTh31r/wtnZlUBBaDQL5RGMzux"
    "88IGClVZWVlZmVlZVVnGbTBMDNM0g6VO/fACuIvdsDnESu0G8r2o7Gv68HkYgamS1mbcgvT3L+eXn3NN9dg/95MYwIImUaUvdfOM"
    "gQCpQtuehyBtgNzY5yNnVDsnHO9WayOD/txNLswIYy1DRTpt+L4EAtxQw6BZNEpfnPMLRbXEaCLDcRIapzcJyb1bGAgcN87+jrOP"
    "rJ/YHM4dySOTQQwW768sb0CiQfMewKNhAd5fPHKG+KGbfejSh+ePiFAsqWU0IOnNIxDxkzk76ZXHHoSsH3+OFwZ5SA/elv/rn/+t"
    "aA7RC4ygMAKArW6joRtBLvEPmPig2xDoagmTYrWLGiDi6Pex15Y16HZEAqzZ1/6lh32bUugxTyzRCHO/Sm6mICdijNvuGBiFJpeS"
    "0QvBISTN+2fQbhADycb1bAPVPQ9pCGCiGYRXmo5krmYITizobq1hSMyX1FEYCU3wx25j9BUIK5IW4zCYxDgIl/ow+COSV3wDIs4T"
    "j74NJVgBkh8y81wuEIraNHyBqySX2LMwkJfGG1QS8fDWHY89VNYHLMSyCyM+8n4C2TB0DsPpAiUAC+MxdD6beuc+vM9neAB96Lya"
    "n+LrGK3cKUCgXwRA4euegxkMGAydr8PahXtTA4GDlmcY8++f00XRWS7QmD//p6DGIrS4k7AGTa95MRSo4Z3SUVrwFUXEksHHXs0L"
    "xhiGzo1CCQSUiPOZbxtL6XNaimedsovEcrlTtGv0fQzfWXaOS7GMaIcolysGRpB7g9H64+GRMwmhC88hzZnOAzKxgPoJe/B//t+i"
    "Mah0fPlp7i3oYeF7EcsY//x3pwjuOIVHdxkwoAwgA8dhMSgMBC8ulX3uB1DyMXx4Bv8/h/+/h/+/hP8P4f9XkBOkYnIh8PYCL0Ks"
    "z7zTiD1BRe/w1z2N/Cm934RUZeCz3yn9wnCJUQE7MXCc711CcXgJx8mcPQXhIk2d+GP+LNcuWgkoMATSVkLVrGJWL6uV1ckqZDWx"
    "Whh8okDCJQCYppMHl5cPbgAAbRZ67N68OMMTzUPLcGHSPbyl+3GAzb0owirpVFA4B+P2IfqI/RDScA0LxoV/Pvdx5ZyDegmMQZv1"
    "h85LXDmN3Nrs57879wPXMegOlez7z/9qiiFJsu8IUS7P0mtxVgXiocjhpkgxvv4mvALMUl6McFAB/HkgfX7sxcUMICnAZkylxCMY"
    "kD//feKfo40v5MSP8+jn/zx+kwmKh/P46ue/v5hiJiEsnoTji6k7wSQhMB6entKVJUFRYnzl+YFX+8yHofnz3597aoHBM0Xn3mng"
    "xyACzn7+z1Ft4kMbaiyrWl6Uyp17YEcRYgphUZFPJSlSfGvuPD73iAJJpZxANFgR9zxfQBIRr8IgSNxzHJUhf3gM3R7zND9JrkJc"
    "TnYe48J+xNM/jzyfPb0C0wmfynLiVUhACSCBIiBUmMqVxMMrLhoeS7+fq8TDl3jhAgL5HOQDe3r+899H7+D34YzJh+cuVvcliAf6"
    "meLPw/n5PMbx+QoYzUMzCZ5fvElC9vQ1WNQ88bH3jj2qJMOXGGwDq+bVslrlOlmVrEZWHauIVcLgl0SDeXlprhcNr4DFfe/nf0sT"
    "4FQ8pMODSYfvoHOwHUXR8Bm8erVX+LUkFp55ybvsY0EmfP3z348vpLIFgXAYRmDHw4gV36UB/6PnT4lds+EalD+fiq8gDMTUMZUI"
    "LA5VJgz+3//zbymMk5AFzNeZyQFcr/jP/0smBNiV4EUJwFaC/7+/+4//8K//D/Xwl+NXMi/MP/x7XIT6L//m73CH9r/671hoN7UM"
    "SC9fEZkKI599rOGoxtNDaabiIKZ9ObRCjVkB3crhDjXyHRcUQJSySgP9v/xP/xZvkfwf/1fgP/b8f/+Hf549/6d/KaX/Tfr8//zr"
    "fy3l+dss/V/8e8WQx/gsVAEGVCHo+ECgKeVv2AMDSp/+lqfkwDFxwCAxMAwGB0CleVEqlxMOuOD5P//3rAx/+A9/wx6gpPj0tzzl"
    "X/x7kee/FSn/O0/5j/+Gp/wP/036kALHZwZfJSIslqnJflrsp81+Ouyny3567KfPfgbsx2rwXw7HarKKZIFxc4O2xGSyTmCIbfiZ"
    "sEiX84S4YPsjKKEoMf7h3/07+ETHUQryAl2ZeI0M+1iQFwwifSmIClY5fZGkAF+t+Lt/WZAObORmX5dLyYf0kNwmbNro4cLF+EJ7"
    "cPTXE/P4/oPU9XMvef8+MZm7+4+t7Pmv7Pbe3td80n3UOkYnRYP5/czmYPDP0k+NY/2+2en3shQLUyyrnaU0jyVHyU+ZG2sSjudo"
    "oZvjyIOu+4zZ6xpYhgtH38cokDAJNMe4Qfg6sZ1ZGPsIYuiexuEUZl77Cz/2T/2pn9wML+iYyT7ubDqnadhw4UZavY7e4/rpuVED"
    "LR/EMxc3mOkw8EXVp+HkxnRnMy+YHFz4U3RD8Kk20O/cSw7CyxlUNaEJKXw0sxrwZuQocwtwp5MGU13uJiGaP/cmvqs5GjrswD6o"
    "4x7wqB6D0QUzwtrEjd7ojs66x4tHDibARH2KO8CdYfJHq9kvJGakfC71MM6Mv/3mGZOyL1302GjiEAKPYKyj609zEqzZQb8BImlE"
    "zPmIUCI7IR8o1gasgM+sylEyxG7bj+5By/b2tMCOjG8vtEg3vJEJP/pyP9IY3Xx781bv+3RT2AL64ZkP6hPsJ81h8chBmzF4LrXs"
    "+Tyhlrw4jb0IZsRQ575rhuxNSztTPHBOMm7dJIn8U5ykD+81jPSNKTIQRMRhIEHGMHrJw+4mbp0R6HjJEAjtKz+YhFfkN0SLfuFO"
    "tchoea3UxYL083n3V7bGcOmADdv+CUxCIatTgKHOXKxfo2sPROXQiWc+GpSOceklIK7AhkTpnaY6PAIdrhFE4dgj9PF6B/g5nZ8B"
    "0fHj8dKIF+fD2+vLaQCi7SJJZsMHD66ursyrlhlG5w+ajUbjAWRxjCt/klwMmw3jgk4f4BOGXHgUXg+dRq2B97c2GygBQQQ4GPPa"
    "WRpBOEGdcuTgcSjHuAXj4rlVsxoHVq1jNpqd3iD9xeSadWA1zdag0cHXttnpNmuWOWgNWjWra1q9Vr/WMtudltU8gPd2r9OF916r"
    "2x3g9zaWa5tNy+r18b3Z6MFrx2p1ewdWxxw0W/i5b3U68Lljttv9Nr63Gq0BvlvtLn7vtLv9/oEFcAf9FoBv9gGMBVj0B51a0+wg"
    "mvBz0DH7nXbToiT8X36HBtJPG4BCZeKT1WPF8fdAfGSJPSk7z3ZAvwOQnUSeHmAKHwdmEz728S8+HsBjt9tu8vRBln9AIAYIddCD"
    "DOnvgFAYHKSEHzBis6/w8UfRiXy7LYkxx3jj3QydWfvqTdhwlsfHkiJ5eS6clPdIZOztwYPtpCsNYq0I0pibFoTHg//qryf3tb82"
    "4a8+2n1Au/NxjYH82rNr7uB2iOc/P7e1I89IjrkcukVUAnR4R0s7MXwbV0bCSINPlA3qenGKpi7ujY9gtokSyD96N4UKju1ECGTy"
    "DGaw/KW+NJ7SohkXmbex/w4m1oj+8IgpK4OtG4Epwa51HC5Cf1JrLA2SXzwvy1PKgkOT53iEa0FukGa5Z4FiZmjdPgURMHyjsVHu"
    "0cWQfMHMqZMimGnoacd7GaKHidbAxbVv8XgwW1y777G7wDRL182fQj/QoCPAighn6M0HGTWfaVzwxcNgqXPBzlZgEhObPBo1GzqQ"
    "laVpt0Ac6GL2Td/bu92p12fXdR/wrGPSzjD7ukRK0lXKYQQ5GVX4+3KJ/lgOFUQCQUDxxEDhAhq/yxKAAa329sQnfHOOcWUcpKHG"
    "iafL4hX60iEphcgCBRbnXF5F3GnMhZZ43UEbr34hjp4mEbrecAXFIIk/9Hk+kvtDl70tDXQhg0SjTvj8HNTaMiUtTLyendui35xX"
    "Qg77AU7tkodE73uWcXJSEN+sS5ieZp2fLO2n59rXqQ3GVy61z0ErPNMea4luXHvaoat55i71I9CVVLXVJZSykfkN2lLcv71760bn"
    "pP1iYcM19vbSNDDUYNAyXh3JqTDox85y9/Yn0ODpyqqzqEPPOWnCw+kU2dNwThx9KVkg70g07PzpFK3XB7gFEJR9rc5Fwo4Yiu/O"
    "bS4kXt1cnoZTkBQChLO3l/tk4tTcTcII8sSU4oxEXsX69HKo+OgVYOar8/DMRgwsMaZabJaHCTWOA/R5EiKIkcBhmFZoUJszEjzi"
    "69MgH+9pXs1H1xDMqyFvouvJRRRe1V5D2c+iCEQYeuiDMKmN3em05taI/Wou/FdLEZRAH3LQKPxQUAZ2Yz/4ozDR94P79/VbTAe7"
    "7Sg43o9AHs7Rt3k69Wz55f17YMzIpCscz+fsO5hDDnG94wc1GMtaZF4BH/NvusElLEgwP/BewhjwouQG0Pn2HHKCUNXBpJFWTZ8U"
    "lz+TvT1EPyMlNKQS6E6aa8e4FWig1AQDM6vjW7YoDg1O7O+wPrE1Qc/4jJZTU8ZJhsl9R2LX77K+ol68ZzshoUS7G7KVcyI2rq7n"
    "2OiPztwh49c74nxCd7ld+ni7zrGeDi/RKQEGbZxSjfusxkiqUdQW7ZeY5E9/kgDXLucxSHCW2a3N0nTqPRP4hX/jWx48tkb8xbmd"
    "jgzgIEEBDwh0y3ipJC4sWVxYSnFhHQ8lqMt9YH6MJ2t4MOmBX5MvuYDWptcpt4PtQCBJfHJEWtk5Bbv61TgKp1NhLzsGNUqug+DE"
    "lAuZ4iVN4GIbl+ykCvV9MUY8GCPeH9WlxMDxYOCocxx5x4opCcvm5NuEK3isHfNgo5YgOykr1T8e7so5yBr0QeElUXhTRXtV67RC"
    "d5N2KvR4mqToPNwMtDzWl5qky77aTJV89XtSJV/lVclbeQfWj2xjz/fs5wf28yUo/Cw/vt2WpMfTADoSxi1eeX85A0M3rMUwDXcn"
    "NZi11Ykm0BepojL/4mlQoziNmPMUPvAcBuV3o8i9qTGZFTNZdOGC9HFrRwUqH2t6DeaqF+HElJXYD5nMZbMIabog5Ddv8p9ZViZ+"
    "weoH+cqEGhekOjd9+0bdyhbr0U3BFEuxR5iwllPIAkXXB5R57s7EXq9XXuKMHkbicjioaUjpD4XgoxmNNhp+679/qgcJPPXfW933"
    "raYOjwdT93LmTXQGQUx2An3E2yNmCBlNvj/P00LWL16Jrvf41hDvCDSDSHV4sqBdDvusph9FTey7H9NvtreEaC7l5yjfaonYkJLA"
    "XITJHpgbaOhK5G/7klliRDYDDL0HFgqZJhHYJKAq0TDhmi6rZveXM5q8k9+e0RSdKI2m5KRsNCH6H9NoCgp1QA8CNkBlaIE3qoIN"
    "M0imDQIjowi60GRy4HtWb2OpD72j5NgO5OqhrtRm809UNttXa2w2/yRlla8+uc321Se12dyTdTYbxuX1ExhtCV2Nvr+b2V/Q0fTo"
    "cNUJ+py1LPuCRbJkUs48MzlZQQqC1GLpmNWOBJrEqNxqc3FNpWAqeNxW4NDQhMI2pQYSRaRQGBiSDQKzY28tXJZNBk1e1CrTRRSj"
    "TFpW6BzEfakqIyMylj1BXzmNP2CKEUuKvPE8iqEftbeM7qIGoDFoDBCXgqm/A7YZRUNm6PBaT/yYbv7zJisqh9q8kcmWKYR7IBKi"
    "GP3u5gJdFDpfYWB9OQxIuIDGSt6/B7HEsE2r0yIAj+IsQ2U1BYxIVA01AkjAaBcjBcZ6igmOFO7dKuASsREU6FBlvv0p+RT9xcxf"
    "YtPEvqMj4+jYuPOsBspG9lGqqgLccPiZO77QUhxBguJlqf50An0jayxSfKPIJl0xxq2iMqeA6E1L6cAkNLLIDIHu8uhtFJmzeXwB"
    "NQy/01hXomrJACbCNZYik21Q9uSOxsqw+JL5EVX2LOOfpa5DJiMqWeHhibz9mVYH0RCakbAdecOvptotrun418PEwJhgw7eTpSFb"
    "EPEaCG+rICALjE9s0LrTnBzEfd4cmJXbmg4qR/JSzzNNA2yQ7qcliwXY/cUMc0kcDJNUYVYWOBjS0cR4SUiiFrgXcDsRG8GXJXE9"
    "W6iDYP/e+GRvb3qiYcdhG0hRxuEU79mCYeQc0a6zw7l3XHt94dVohakWEko1qbLaDm7O3anRXTagOChmXe1PqD+8uX/9gGqe7HMT"
    "CJkoriEJEWBtZ1bfqTHKgoaRemRyIjPAyKTa3793z7IsZ3IWyo93ci/A2B6NXkyoa2YnpCS+89w3YDlndL88EasDQs/PTmihMdsx"
    "DTwAaTETqPa3WmHcp4IuYcY6GBi6WGlIGLYj6F1ECwzYcEorgXpqVuPeYu7AlU53nMizDibXya6axdijQWoDZodJtCO3/u5Y144e"
    "1n881h+cG86uVd9tOoXTLYZvc6sptb/MCzd+cRUI+4kLQINUQJKtD1NW7xrmx5OYoQLmEtO0ts293nt7wZF/jLyGcxN4XAodTLKU"
    "Tpuc2NMZhyPc0RgtDsxg2Td8crLRfPrk5Hc0n6Y2Z0ywkLn69QnNoG/Yzyv2c30iz6dvTj7VtOw0JyQFblcslWFHD3n88G2j+T65"
    "dICI88j7dSb9r042nvQfnPy+Jv28PeVJP//wS0+tORMJmcdVG+3c2YitSwxN8pJzNZOahm+4RmjEYDAZY1R2U9DadB4Lsro20D9I"
    "VSsFFcIdMXaDGIF1GhAKt5JwHtgHINbSm+IOYmj4/j1tbIP946aWJF2gjDSKmaUUiQNAwsoDYEAexEXfZzYCrbghbj4eJfMDgHRz"
    "y1G8NwYxa3IjgisaLbRFkibm3FqIWIbCV5KCARBT7qXwU/kcS139+mSN10U+3ZbrL65awIjDc037KcHIhMlUDOu0WGixVXnoqBy3"
    "J6vNSCWEx148jvxZgueKAEXJOYJKN6C+wL1T0xvSdqmmkk7FESEENyc2cMkfixb6fiJcMpL1jo4Exrm3y6Gcup/8oTkCmqV8ZECf"
    "l611aNkL7vmAQngaZ00LY6UvBDcXeMa6osiiQxmnCoQqnS3rqB8A9fHMUJl7XpTdO28+oXvnjeTeeah075ycrHbvPMw0BWnvT+re"
    "gRp/SfeORjMfThF+JHnINprowufz04nY8PUIzEvcbQiiLkgcvu/gdpbwPSWsL0u7TmZiZrM62zxgc4eKDSoi22R1bUvDD2iP+e0u"
    "c1E85fbE8LaU8wql8PDWj79Nq/YvL3FbYEKsdeEGEwzzJBuJZ8xTZe5mZj7ekc73LA7FZjrm38ANcAd03wNAj3XDw0md4otYrDoh"
    "IAcEI13IUoJCTxFSYi2+jPERxv5WqFPaqzGMx4nABLdSStiwj68pH2uFp1cXlqfLwgqvhrNcSw8VfvqQfZsHarhAtKURUzKlfDbl"
    "vGDM/Yl4pP0sbGt+GKWJKcnSFOKYJ2Es+MlgV3sc0D7hkt8IBaCRWiXG2Jgac+bFmyUjEyOLz4CV7flI80Ry5gfwwOwKIx9PbE0P"
    "yarIewNA6FG/Zo6bY47UPsgdDYAmZaDoXFgogCUKYKLw+/cTXfL0BeZFGL4puNzC4JFEiPRb6nMjMXlmaz5DaZc8B4u5d8Bm1Sks"
    "3/YzfAVyviDVzD4bgR2XB5EVdtEyKwDEtBJAN0/YlGxg3UEFYWUFoR2WKsC0UgUhI/JQiythxXachyXKcprPsqxje1zuntznYpdM"
    "IamiS6asS8Z81GY8XsB0lLk0eM6U9+1CSZgwFIrGF+4kvPomDPl+i9zwsnF3GEuHEWhnGWLTnwhYcoFs99dsjPv2Fif+BPd7GWx7"
    "/qTkXz9BcmhOGLC2TzAvG6jPMUxpOT9JjrxQFiAeZeUQzCU+5Kukob4vhnBGppTkeNQ6QaMLMxThP2cAHdEfgojcW56+s1jCvjcZ"
    "Md4CE+Ke9f79fKaljWMBtqup8UjKhW1hyx8ryMeySuT7NrhUE7BQBctGdQSVFBNrF7gzhAS2EOlZJ1TKdGMluSdeJbm/FfhQZ5KD"
    "ACwU+pzToDgbYxUwb2gMQyxOyLkqaVcSTC9fa+nKjHieCcbPRqzAJPX5kuwxHBq6Ju06Rl9ACvYxM1xk6JXl9kGdAFEC/Ava7gQs"
    "53Oyq2OFWXBkmmY6czlOd+0Kw3g8pZgrfP7E1VyiD58UU6AeOrdXtVoipT88wz2jqcAYUZit9+9fnBkOPjlGyU44ms7oLvuDV6+w"
    "KPWycJUbHhuxX0zDUwyfwljiGNeXcbx4Z3Q4ZG9vRa1pLkXVNV71S5GnhMAyRSFvaOwXBOOo8G6SGQJooB8ASJpogogMhFowbWgn"
    "ClCZvVjVM8Bl5UZXE0u0nrhY0VPnJ6t6Kh0/9AF9YhxaVRnox+W+sF3YJ8nrjjigT2oLQuMSqKYL8shMoyYQjT6WrXLwndNnPALm"
    "CLlNR5v0bKEVBhFnJJjWPT4RHnFW0lnKSlU0PXXOGUXmKuzXY6Ipm8II9CdlY39fbO/bJfbBAxJ0SEasxmYVXXheQub8PVzOeCUW"
    "kzDarTfRnKl740V18s06erqgZUT2Lt/ymA290Z9Tw7rQkZIdSW6FZwj0BcIkHIAfSivIZK4kBoZBEfSMJHrKaLFjkDgpitwrdA0o"
    "iWxQqCXWrLSVhfbhnKFImrIopTU4JbH4uoeeLlwbvk2L1ipaoAHNTvRBGaqwYumab5FAWrx/f7s0XLSWxSTfCOEt9i7dIPHHRgwv"
    "jNWMMaZjjSn93BFyrkTEFEh9gQcUTim6yEoaClBhEZTAYGtIcRESQ39bOOw8ZAkKO1CnLGqMq1hC9OKyqp8laCOm5MlfXi26GD/A"
    "NNCYGGcwn9HAVFfyxNyecp5gfhcVW8wZW0yLbHFpz4iUF/DLOl6bKGuZMMpfSkTfvZUysnMxG/eAdqas5UzZL6qKVnXSRUUnFaHo"
    "YuSWrMby+BWzc6Xc1NKOTCTa8zl0mFu1lxbo4/hQUAv3vdyzyAuoYoiA6zIXdyVxZMM3XqC9ABrlaMAUL/QuwHL5XqO1ZDCK4p0b"
    "KWwqHgLngdxRsp5vR8h6LykUpIrvfMZ3keGJOST3tokJm2BIlzGkTtwY22mfy5O7ZV3BCQ4IrdzYYrIm49N4JSfu8/3dks/HHo9M"
    "j2/8PpG+IPHsGFimYqqh8OmkU71cBXnHjexjwRlJdgRbhQD0a15q5OYzeCNvONOUJcmsUdiFZcvmjnuXcqcqlL7EoOhKREeeclpX"
    "RkoBcN/bwrO6OuvKDCpXIuANjI/ET/3Hqq0CI/XEEOZMu7ldVFXZhqlNKVeFhnDeea0PS0mZgUgjNJwdljYmCj8r1HHkHXN/Sqky"
    "mhuPTMjBYEnWrQraNa5N3HELm+OUSzblkk1lyebx8HbJu+Tl60P1xrw7cjXKV/vuzVHs5tu0QWAvl8q25LItZdnW8ZCWjB+YD87Z"
    "in4C2uDeveAoEYd0TYdC2hputk80ZRDNSZdjHL3ormM+2JGZZiEjIrRdk9wIr1i4GhTgoS1Qe/8+BBHNc5CjwQARm2K+tzc25nY0"
    "8kcrJlQvXx/gdjE2o8KlwuEq30c5N1cyE9tP9W+WGdTLmeYZVcVBkTwmNRvoBvy9ZVbicI5NxzXkM4mIrx+7iYtRkfEA7MwG8tyL"
    "9/YmoylvXEYDjRt2+pDBZ1XMdQNEUZoIKfQKZhotw0VhmDijCYxFFuVhNq77E+d4NJIco/lPwl8tQsHu7c329i7v2XZZu47SOmes"
    "oTsZoB00wi6XNaVWdpb6cCYGHxLz4469NT6oJ5rkXeN+J/JdHMmeNmF+kL1znG5K1VPvobr07gnR9OVruUgqaERnf7T2grxI7LT/"
    "HLYHlHf73t53WroelHVyzIacc5wFccF5O0WK8fmWtLRjZWgskRmQFF0VSeMYpzB3HK2qZ1hyVupGsLcnAWLb+ghUOS+xFmbOcZeC"
    "qxSrAXiaOwPAaxOIYXWe1DnZGK5y3eRVmdz5aaekRL2Zsi135PC8ZUfuveXQE7VVLKnefTM3sIJC/DfzOoKLNd8u1u5vXm0+GVRC"
    "NIpwHxk6CZAZdBDm2JN87Ih9rv7eHor4OF0nA2YJj/XRyF1KjMimLxvtNfUMhy3dOUBg9gQ2DV/Ny6/B+VpxuZNvxscPzJxe4jNu"
    "q0FzHcd27owATuYEoVT2EEYzwM1A+3LAkG1bwSpwbdGIT6ZLFeSZ2Blp0oDpdlZskj6L/gSGn+ijCf7O9dF8uFaVSTqLtNhwIrb6"
    "+LReLyv2QmfkDNHcOsk5L2CwfAxKqvE3BjMRJVI4u5du9EZpuZPn4KGIsqTJ2lQhkrinIcuvllq4x+Xy46qJO8qV23R4SuqRGX5i"
    "NcrLTJ6cv5o2cGFD/N9IS0C6cu3P9TTeQxHOsZ95Wy5pm1S25XarsRwYDnQ6elIC05+MRmItG0yygOgQ/g4mGZXcwE3fW+GwIR1N"
    "RvA9C9fTr3+L7Jwtc6TbK06UyzI5Jxipcy9eyfjG5YlW2J+Bg2EclMmQN1gFfngqKW0bTOw9aHoF0NibqibWdCpJWSL+bXQGTDs/"
    "hBNx9Sk907Kuz/xg6gfcu1PdcVkEpiMlxPOTzQEZ0TEu9Yx5MMXh7XlJm8n2pWJgaVUGgHCCKjY1L3BBKxuE3hL30BqTsgr8Ber2"
    "yj2Aq7TkYuYTipRCYBwTqqV0RFfaQKnY5ccidLDvmR2ixjfdA5orBfo8XVAs11BcAS1ul0lpIUCgM74BMP1KdIt7kOY+4uAHhX0U"
    "ok/kHfF8SkRHGEfsCBU5vvfzu9jxOMdnPDRcIVKcwB5K6qrt8Gwb+ikICsNCP89+dmwuvWcJbCAUHGy9orKVRQpR7iXf2qgoxQcP"
    "l6fp9EQaYSKtuBtkafA1/nLiq2JlMAi1FZ5KtozAVyqMvGOVJVJX5Zchyo1xjjLL77+2d5Sej51jR1BD7GAubV3iIfOCEIdvuhWp"
    "alMjLgiM41lx/6ZJxY1sk2nBFb6kESCDXNunI76lEErSMklV/qJPWkxjskk91k2DfcVEW9VNqYTNzonnrQ0Rty7jdwO+Jtwpvov9"
    "Y7AggdKgNBjAoSQzORw8Ai5DwXcJBr7SE0r51PGjoItyOFJ2xnrFIZlpcDoyR2NyBKzoRglZrOhxHTp44DnyJnOgj+pAPw3nJp3k"
    "R8PBhx8rHdkHJ9oCw3Nw9+4Q3SSpo2ykAstmwFw+4pkIsHLZ0QgQfhFX3XVr5KNj3cAveL7ZgL4mR3vR3v44VGJ+k4xIIr6zlmQr"
    "4yWybUW3VBQeRcdEQdEi6PLnijOpp+4El4GYvHP+ogb/mLM6pdZu6RX/mfhAePdmWGOSrn429a7306+ntE+kHrkTfx4Pa5NE+0sC"
    "YLIPJvvwl3pWwgUtRAceYUjVxng/R5R9/GkeJ/7ZTR2vnEE+L2WYuRMMqivXxJPkOqQg03JGEA5udCMFiJbLsFCZiuz0Qc55BshR"
    "4E05NyZSCM5SzisW+bKYlyXLuS/9oM6CZkp5IdGkRDnnRQnkRQ7a8i9yvVmfhInUo6U64HMJdSUyqoxlXFS5CnzSafxB0acNNfZj"
    "PxpPZZYsFlhVQREYuy4K+lWCp2aXNOemDJMVyLFMCYP5GKNBr6+f5du4dp59Zd1+cBaurRgzbVor5V1ZJcZXWFslZtq0Ssq7ssoJ"
    "rm9Haytl2TatludeWTG7KStO1lYtMm5aeZp/NWddShUrpVR8qRZUytEOmTeUPpBztQCanq/DbHq+BWaQeUPMIOdqzK6n6zC7nm6B"
    "GWTeEDPIWcTMMcTk4hbXsRTLLjxCBq6dmcIEFD4AR+juWX2cnVK83cmL0Z3hd5o4+rS3J25hFVdeMtMIrCTL2JGUx87Qn0ql7gU8"
    "3JDwPWeZ48udISMVnay8dDGu5U7GBvLXqRuh/bGTdYX89br4GUUNZfDwBEhyg5kwTcrCZWAxF0+WMqIMKebCNCkLG+/FTCxVrlII"
    "/VKl4oOUWQzjYl6R7izRC6MbX+fOnD5idhoPTDL86UQcPWXrQjw+Og96zk6vZvHRKSqJISpTB0jnebJg66rvS24oPqfqF/5EMau6"
    "3Z2NCVs2wynu2SEnqxwS6OVmIVBe/p5CoLzMh0D5vHw+/OknPB/+VDof/kx5PvzlmvPhz7Lz4S8/+fnwl7/++fBvpLGaG6dfn5Ri"
    "z2fuVZyav1RMLA+nGnDE5+hnInHNJv/8oBubJgqZnX7IiW26W0sqZfNS/BBXTmxzP7AQDvk37l1CqZA96TSZfHdii70TznE2mh+d"
    "aNJJ37RJGDX/qebEM7x27okm9heY42uNbdfQDb5dYmfomkQY9LHiUpzIoBtHX9P5GMQer1kn9B3cLFE+hvNIe50uB8NU+3ipHxtW"
    "F5DWl9+cwGw6gHmC/egkw/twMyl0+HuSQod5KfQkH+7oLQt39JWIcvSdePg2F+7o23804Y6+2zzc0Re/s3BHX1SFO/ri04Q7+uo3"
    "Ge7oHoY7+n3EMnq7RSyjL3/PsYx++GViGX25SSyj7z9tLKMvf5VYRt+XbdUfP6Gt+qNkq/5ZaaserrFV/5ypgcNPbqse/vq26m4W"
    "IhS0jfHWvsXlq+d4f13ZjjqbasXR80c73UIn76sAw2DDnMZiqm0Bd7RhxmE5n1XOZx3rx+LACAv2ujq2sicd0s3cLaVzudlmFToT"
    "lx1mTcxxci2fbo1Qfh3g0sZ1kk8vBlPBNL4DI5UNpbOwWcWsVcW10ZxFZ8rtpk/ZGil+epquvm5ePluhLR2duZ6uPK9y9xjStDHu"
    "7pvqortu4XEcw7/riRU6oVwq25bLtpVl27TtKLRLS89vKzZ4v91qd3dsa7hmb+L9MSAtqk/uZUv16X5eXOJet913bMeF7b5Teyxt"
    "98X9vLG83Xdiz6XtvnPjzHZHb4sHYYwk2/IK1lOI0830EMzMfptujjXeiu1BoNL4Dm/KDobCD7STx88dejkTh14u7belEy9GdpEs"
    "UOgeGHGz0QSRk7YKJ+wws3GpD1kVrJYzHQ+dpInsDMrlL3fQ4oP3W2aHNESTU8wT6ZDF9+KcQpAdr+A7qPhJBimHfJJBPmaicHJ/"
    "3K2iykMFUelQAV4iELCjAT4dCUi7OxqZR/7xaBRle//TPbZsZ+022/ujqu39kbS9P0o3las2wX1ctsgTkdNnC0KWZWJe+KXHOMoC"
    "MC/pxFlp1aEFJDEOc7aPskj+pHguIQShJs4leOukVGyHBSkFckuSUii1QllKze2pJKWmILVcLSl26hkl5g8lTKRDCWeqQwln+ugs"
    "PZwwBjEDc8ez0bwgZjxxuC4dlexY3Zkw2aHm6tMEv6JwUevuT8RY+5klw/RD6qusjj30y9gqyhG3xXkoppwYM9NcGI+6SvvlwGDg"
    "O/J8SaP7G229c5f7b0vxOUGG6cbbcgwFOb0cm0x8VQY2S/BOgN2M6opATBUVLhGmMgKUDM9wNwgDJRjgA/rX3bB/96kHCpEvPB75"
    "4uGZprlSWA1XukWhGFgDo1HpFI7KXxOOSgoc5upp7pGUiJHCYG7jZ5uDpaAcNHf19SJ20QrsIgm7LSOLubSVelW0p083Fimakbwt"
    "L9tdrem6MBcmJ1ogTYFoii9N/9CuThQxQzwex0nXpQhUb8vhp8DgpOMo0YYhqIQLdHeiYXBRRZf6omY5KhVJjkLcEzylt0lIqpAB"
    "dEECZSGpYrSuNwpJRacOPjgCFfNHUZdQvyXro1ARqWwkk1dqO0aSWhmCivuJfSMN/6enVkQWgmoMb2kIKjQfeAiqOabnQlDxaE8/"
    "bBaCKpDiRI2LJVdFnJILTosFqwNMBcV4Uj9UxZMCXp2jTF8bPkrVQV4pdlSU9Y3g30gKHMXnWcYFdONE0Y1n9gS78bEfoU3HtU+h"
    "J89YT06KPXluXxB9TuCXR42alavgtDyXyIgXqK+LF4UE1S7L4C6VNC5BlKh9UkFtb9sgUJ90WoEbmDCckkbyMqAwiLkjp9mKDovM"
    "5H1AWKbAKJ1z8MqHHET/Y+wrWaDLMZtC2ymXrRe7x9n3CsGWJM5mAecydgmzyE24od2bGrnCFI8pXH7iqEab9eMHBju6M6Mhht66"
    "AO6ebAbq+Vc7jRpUiHMrb1ugCSRGKbedMNi9/QZV5tIBKZ6zu3HeAOIcTID0uA1MBNPJxTxzPkWSYo2UbrWQDibrxtvq4LZjDIp7"
    "ZhedYXNAKwukPc2FOMfA2hMhAIveYwyJtLa+mX3rTYeBwf2Dw8igg11D34BBvDikZ5gwTEYmIDID/PhDReDdyv5XC4uK4CjNOwXo"
    "ZZtyPp6ziczJ7OpBEdyeQaUI9/uReZKyRmzn3lCw0CLTPM9UyH/ARbm8FLsKvYi2T46BzBUHCmBk8tDNOh0WLpSzZQcBOjrZYSjP"
    "2MXzTtCdu6JnfWP3MpxgWG0YsD5AFS/GLg8+waNtG7vAERMT/r5/H71/n7sOAP0Rn+B4XDLiJ91Kp8Lm8k0FjLDpsgajrXRvger7"
    "+/eFdQ5MzEVxz9+PoGG/7s4muUF3lMakzyLZ50ImKM+35tdZYGRXHV9la5NiB1EujmzlaA8wvFnlUVUeAjK9UjQpMWA+5uNuab2g"
    "8jaF9BCrnrm75tJBV7owtaou3LZRrgtTVXUF0oHZ0sHPwi2Ga9qnPL+YtYkfFFUeys3T8p6SmBUTSwx+uJYcK1ELpFkfP+bLrK27"
    "k2KLrp4kykAgiWrevfFxff/DYye8zUV+KLbX+Kg0mKEdIdaWdHUcjV9l6VNNym3jaKwhJTber4qgQR8/gBPcD+aEzcdi5tDKZzdn"
    "40ArWU0bDFt5CiNF9OahOXzOMq5eEXYjqQ67kWRGVDJMcIsFu4m1iNBItpvLgTgSORBHsimM+Po3MtrvNVT8sS17+yNF364VD6q+"
    "TfKRN4Ksg7P7t87Q/ZUCtsuCaWxrU1vKoh8FWd1jEfNaWJ5GdOTs0i0Yx3IhNPLpzg8vu4KJKp5N3r+3cUcEPuaMRUqhkKjMauRG"
    "Y3rkvIgpWhbSgmoixXqnlYlCu0LbHZl0+ZgR24pQ1DDlD7wrNh/B+X84ndBLyvQS+UP11UGJ8EzSTkGYyX1oNUcOq8eMfJhaeM7x"
    "6gqntpu7QsJbILO9fz+Z7cMHajvY1gdQBM//2bcM+DA2dnLV7AzHGDMtkySlW5cCUa87KtkGxpSm6Ry2mB7DlDiUnPmVLUvvrALY"
    "kuvFXWOC+BxOoXaWmCIxRlu0zDElXinTyogUmdSUDtCNyDwEBRoEgoxG/nsBy6BMG2M9hmIToJAqt6XLmRLhaUiyUZiIUShGW26e"
    "cTHRnBnd1IMk5Xc5GQJOxZ1OiZiSvs3d6yRqGqU72ggIQpbAIHQhK2g1uXR7UZLzl+zvnuBqvIaHBLS1FZLzBO8X45/yt4gVdtrx"
    "VEVA8DC9T4rDwTkxtEPcbJRSqPJmKI9l0W/T1vNboQzxRXE7VNry7dsM1XBwKuSKl0phDupBqMidTHDR1Mc/lYuqpVqlbhV3URkC"
    "qvJOqqTkBdvfsp8qgsHjp3ww+DANBk+ukKmNl8SVKkIvVsXWSzlIPN5ZlxZOt9njjXBpYZE6NktR56cjHlqeQ0gLFbOCWBult2qJ"
    "6qhXgxLT4cJV0e0kXGBPTrgZiXtvFXv3MKhHYlMUNdxunAVDQQ39EYBGOaBvRWCQxJD3rQV0kZZwMOEq35IW39PMAaV4i3JoESYw"
    "66lDohRlxA/eqGKMnE7D8RspMkTIwvwOa+4pyPh54lXH+GBVVhyoL0SHsBpy/AkKJwxD5HJYi0HleVpDl1HwMQJJnSmWIR5H8oon"
    "yaExdZfaKbXJDfxL5omqMdRqDbMd19AqdKMchD+98W7OIqBbLHJmUBBT6RX/CWfuGI/yytEvlM1omh2pIcuKQ+YO4e/gseNkYaes"
    "cMs6zFss9eykXLDY6KRcsPgdnZSjNmdHCKKFHLRwQVtrQ/bjsh9/IZ+Rw7eNzsjFM9Drk1/neBxivuHxuPHi93U8jrenfDyOOvVW"
    "fQakfErtnrjhJH9WjR9TE1fLydhnNcWLNQe4xnkW5Cj/0gf3povSaZ/54tOd9pkvskWayUJ12idYrD7tM8m4mgbxJz3tAzX+2qd9"
    "zkAML4Q85yrZMW75vd/FqWYuTDS/6ZpNNb6hHDzIGa4c8aPh6Bf9jNRi+Rs9K4NNT+oCk3uNfGZaSAeDMDqbhle2c+FPJl7glLMI"
    "q8B2Ig/nfWBe6EOGArcoK9BhX6sxInNGYRR7/BZKDp0u6IY5cDhPb79OL1DNaFKIuw32O6Wn2xVxlhJ7k/BKNJGuwI29x5BCpGWR"
    "BMlMr4TKMLorYLl7K2L8406Lp8EbOtdJrpCXc3GUH+QD/AdGxJR2LXkxIOGyPf47uPGlzjpwBwc7P+CPlkbxnVtOOxQfgQ6nFEOa"
    "ajoPaipFDAiDh8K++izgAVPzaVJTjTtex2BgSB0/ELHRMeK2CEiAGwvAwoaRdXDhT2lqxmB4Uxuny6xjNiBqeoencgys5H7+UWYP"
    "uoRezRWpPeqlDcoTLCtJl4RKXFN9/wMo7nmEMV5eY7CexIhy7WObIkHF8wv8MPQF2+IUGaQXTW74p1shlZd6Yv97cyjDemEM0y2Z"
    "cxyxj7A0sOVMhnPmTmPIbNz7CmBhFCO8QFNsCbSfu8mFeelea5/N8ZzvLv4FTcOJziI12f59Z3btGCKVojzxxCW7D+HPVDrEfU7u"
    "ufd93QVNfJbcn4RjMlLM03ByA5NKGDTT1+GsTig8aBoxL/ADFEjCmTL/MwBUJ9wfNFPEILMd57HCCu2QpalI+cP0g0kJlponLurm"
    "ktDGzVjsUZOXtYG/7yXKzvzgngQmbTcslNkFaVAS3BxHmPtPYfIl0JQ/6UYF1xU5vJpwhZybt2NpsPFSMbcBuChiAPIIJx/pG0YZ"
    "BQmnKPRkjuaSkHl0Nkunc1tMzS0zaxcmfbOFncX+nCdJGGwc/BPaG2OcOj5Hzj6A3IjqMUlSecb84eE/hWQc1phyUbkKhFGgDqdH"
    "LayO7VkK15fPv8q7MKxZs+taHOK8TlWUBUQt1ZiPaMrLsDTz5i91VfL1qmikLOuG4UhZ5ilO56uikmaXLQ1z7oaMFDKoLLc5AVsf"
    "H/5SN3IFiQJbluH+m7sUhcFNrHu3aq/rbPPP2oKrQ+KygpUxcXM4DhnJeejoNM+5O8sBg3dFTEP6NoRhi1OriTSSxVjlm4/UBes+"
    "jDywhoEFpKKCu9eWgXojLUqmerlwvaL0MAgTLYO1wKPuMI/SC/AL2bIq9RV1rkT4NITny3Kh5qpCYTC9qQikyzoFc5mYqxwBkg/e"
    "OpekFOo558MrZEAXr/yZ+r+xDrssiYZmjgVWxeC9KEuFirasoEyWRhJFqnrhx/6pPyW3ZVFycyqubdpw6J4lubCuqZrY+evrh42d"
    "/Y9R3coYqowwVUFUVZIc8lYIc+nLdSVtAZs8Je6EnALstowNJTblByXwVXyp4L0tqlsZWpbrt/PNOwzyVnSY9OV6FTZbdpgKOQXY"
    "bTsMSmxOwQ/vsC2qEzJepgyYlWKxCE040IPzy6AK3YJs2dqqKUE8m879SZma2SqRusRHUg5KlZiqcH14gUbvqojSeTuTsn+IocoB"
    "VJir1bY0K1cVoFrZtNKi2Zq2sfwf0jgBYevW8YKrm3cG0/a4Ttont4qX2ZFK2FTMpEUUlkthGxas+7QAZ6WKrzSVLUwiypWWyCDs"
    "0fDsDHcPVwBnX6uIobpLohgym5vFLIb4qnsFVmUkTDfKXRrGkevHBRNJ2VEsX6FzytDWWVwyRJZXPSUoq9RNLi3gmnPNrQUrR4lU"
    "eOMBsv7Wg0Ib7ijfsnruLOFKIO7QyA2kXHVTN5V3WXV3l3hlGHdo7SZST2pulfwrzG+VVa2SRxXDUll4zSDd4PYNDnzl9RurSS+K"
    "bk7xNZd35HC/6wDiddx9+OQBbN24jYaOuokbDxxe1QcMmwKErVu52ZDhzbzDgOHV3GW4lIuuGSzrrovhdm31fTErSc3KbUzglVfN"
    "ZPjecXQQ9DsPDbn0dg3aZFComrXpiKBK7j4ccsW3a9lGA4Gatv0ooAruMASK5dbw/7q7ixjQFZcXraQtK7cxUVfee5The0f+J+h3"
    "5n+59HYN2oT/Vc3alP+pkrvzf674di3biP+padvzP1VwB/4vllvD/7jDcz2JMdddaMvKbUxUyr6ampjljvxP0O/M/3Lp7Rq0Cf+r"
    "mrUp/1Mld+f/XPHtWrYR/1PTtud/quAO/F8st4b/118kx8CuvEluJX1FyY1Ju+YaOhnvO44EXsOdx0K+/LYN22Q8qJu36YjgFd19"
    "TBQAbNvCjcYFb+L2I4NXcoexUS65ZnRsctshA73musOV1M7Kbkzotbcl5vG/4zhJa7nzSClC2L6Bm4yWqmZuOl7Syu4+Ykogtm/p"
    "RqMmber24yat6A4jR1V2zdjhiEwqyK/cASJvgsnVL4Ct3Wu0QdHVBBbZ7zhkSrWtHzq/yeZuOnRK1W0whH4TDV6z9LAW0bssJCgK"
    "3xnZD+XPbRYb/jHRYWvG3Wol4rdIibK7fz2qW7vvS0XviOYHs+3GLv5/HO3fnl039///xihQdLWvxXFL73m+3F2w+1Dm3NDD/ptu"
    "89YMuan7/TfT6qLLey12W3qx8+Xugt2H8uGGnu7fdJu35sNN3eC/mVYXXc9rsdvSm5wvdxfsPpQPN/Q4/6bbvDUfbuqO/s20uuwC"
    "Xovf1j7dYsm74fih/Lix3/cfQdu35svNncK/qdarXLBrsbyDR7Vc9q6YfiiXbuF1/UdDg625dRuX7G+OCrOp629nYlKJOzm9qOCd"
    "EPxgDydV/YH+zd9Au7d3dVLdH+ro/CVbjtfv3t3vrsxSxggr2dDpilnvyG65WjZntk/Thk1ZJ1fNFozzy7Ri8133H5lZNnVyViD5"
    "IRx0F3f3r9i0rRjrTh7sT9C4lfvQPzZrbeSUVCL4QWy1tTv6V2rUdgy1vY/5l27Win3aH5mTNvApllH7EB7a0mv8yduyFets6w3+"
    "RVuzYnPzR2aaDRyAZdQ+hGm2dPF+8rZsxTTbum5/0das2BH8kZlmA29dGbUPYZot/bGfvC1bMc22ftZftDUrt9F+ZLbZyJGmQu9D"
    "WGdr1+mv0qKtGGh7h+gv3KY1u00/Mhtt6N1So/ghrHQH/+av1q6tGOouPstfvGUlX+Qv6Ava0DP1cfyQUpW/kFvo4zRnOx/Rtq7F"
    "j92gaf7agl+GW7CSDfDYhjE+MnKb7DqvRrE6kg/2Q33ijcOIX5yAMTIidOxuUclKjvrIhFBvSneyCxMuN7sw4fL3dGHCZT5a/UU5"
    "jPz5Jwwjfy6FkT9RhpG/XBNG/iQLI3/5ycPIX/76YeQXivtd2CAQt7rMFoU7Rcrxor3sIiR2CXw4i3kHHDlpyKAZDMLLGYaoThwD"
    "GEf53+1OOe7WzpCF13oBz+/fJ3gt01N43du7x+OA0RNFBDJ2SpHIdoYaK/4yjJEeSUi3TshJLFyko+/tcYASGLz3CeiGOPBH+SOF"
    "PGfyAmEuMDR6QGSf0r0rRtr8+u4txjQBrPzkZonXlIkXXcrEYhHhV/aU+8aiCtFH9ih/RfGKn/C3gAp9kvOKBTXML54LZdIscrn4"
    "kvD233nEWJfAy7nv03P5+xQjJee+U2A1x6Ae/Byf9WN2EzRQFXt06BTJTkzgGBQlVMV3albjpZCd5B4ghtq9TUTXLxEV6m/CAx9k"
    "DPCdbs65WfCL25xHbuw94qODjZl4+NOJQVgMbxmEW5QQQzbaxG3QQwyIvmTNWPMd8FJncTD0t8MyHVAofZbtiOdjwva4AJJGxao6"
    "KcOW8F5xzq1ANF0zcdLe5TkfheHUc4M06z0r3/9KeDyctSFEwApY7rpGOI++ff36xdcOZqXY/qsQQ/uj+nO8kgiMWmwQrwDCB/KK"
    "HLT2Wv05PcS0AlEMSrkCST7qV2WhgVtRBeVYcmWxWOBgWPgTr3z9+e3ubMwGD93SYOwyO+ypuHkUE5fLZWZfnW5mX53+nuyr07x9"
    "dV22r159QvvqlWRfHSjtq9M19tVBZl+dfnL76vTXt6++TFVHQW3cLAw/uEAJgvcIxHhBih8gmkMcJ5+zAVcYY+lFNHRPN7vIOFbw"
    "qEb6ly4zGYnLTfyheALcjFuKroySRcyt2GfxBmoP6hvzaz2kXKVRXctuV8mKg5WmSEWkHP6JS/2lECMPQQY9I/1ZUQMp11H2eJ/d"
    "8ED6aOTUnPvZ69Bx9KGMgCuALw1uO1bVgjpGIB9Pw4SlLOnC1lhR6AnDwo2pE9n9Ea5l3Uivcl+lN8yg/nlYAZNDRGpxbTVikjc1"
    "zCv6LNWUKQYKIcxu7yES8ttyij2QXaiDnLuTVSvu9REV7uTrT78Lzci/p0YvUZ9xdrnV/pSRklSNPrrHbuxIh0L2DVgGqnmpAHE4"
    "1UBervjvlt8FhBoxewILNZ1q8LtzpNkGvmYTjoz/xAtxHIDgDM0B8DdIFzYvh8PMXsNJjXl291Rqz4sJAEsWc4DMYGdX+6Q2O71W"
    "mO1sRsDuQaFJQTGzmBfQVIXjTROZYkbKABnFlMoxtJRMuVlVMTWbWGWEQ+bHHkSKruxF0VscXu5FV3Ykh0xcvBHoj88IQmzSNBck"
    "9auZHwReNHx2bjwi2fTNCSApbk7FKTW/oGsBBa8W9hG/2cU5Nl7Lb5lV9Bk3CXJ3+doPNYdXBR0V4ytVBy9j2/fTC+JSve2Z3AAe"
    "fa15XNYZDhcFDugHmhFc4Y006b1cuiRY3EzMgQXJ7knjP5Y+/CLQtM813Xim/aRhTbrxRLt9490MG/wWMBmskBs7AJSGNggwkwSu"
    "bqQa8IVW6s4jNeZgrZZyemJA5lrL09hkERBkqB0x3KRpiUPX/0Aa5cS5oseuC8vl0VfVi1lGRJKn4oa1AkXWVmvkgFUigaaCYXV1"
    "fch7IBQ1WZvWdGzEwEqgRdfUYRw5BNE51pEovPsb+lAmspq6RUr6K0job0q7lE74wH9oZntcZDGSPaXKRbOuFkC9Q82hSwyzhlnU"
    "BWSGKLFp5nibuQ/0jITs3bgtoMKE1VI3Xmscum5YPRj8Eg6Gx+0c3qWxQRW2DGbl869GNmazSb2ezVN5spi8G3N+FxZ8EI/GLBly"
    "fGGuxgTIktGlD71N1TkG73WYDHBQ8CggwOMsQYaQCIj/GSfD1lLmGSMVbUD5o6Px8bG+/NKECeHEi+zPFjQheJxKwDg8S0SRBO+S"
    "OzZe4EeKNw4fWIRwSH2TFqFsRjnHD/Yb7fbkhFnlL+Y+MbVw4TAPjZgzg5YAIPTrT738/BfyAE6FNPQKJPOZZInj3M3+K89EAAW2"
    "ybEwaG6/jpmEmYXQd6Az8Pf9e86CO2nL8BP+jkaOOx6TS5XNwM897ZZFYddYfPTRCKTBfavJ7ozjodRV36CT8lc7spvglsZRivfi"
    "PFUNhDAb3Ky6DKKoREpZ+N7Vo/B66DRqjVqzDf85xpk/nQ7ZzYCAexS+gf7gl6wd4JoLUIIls6jygE8zS0IrZ+zCKGKWVP7DT6Ef"
    "ZF8obg/NcvmdbKxFOK6eai8Zdz/XuNTQjkC5HlOnZRosVV/Q69CxZydnYYRTZphmZvIWhm2zD4IQRsqLBf5aTePxQsjhlHqyJJZo"
    "WO7Z3zpZVbzyK9D6zQJtLt14uLBlznRns1M0jOAR74NyAeOl8ZMqTz0Kr+Dbc+U3H4t9DZ9KY5VnuHSjN07FuHmpBEk39i2Nz1cA"
    "jRM3mceQ6SlKs2zCBtLrWSbf3FMQazi3YDnYjXwkgeGTD3IUhruDGtAfv4GS3/AKLUWFY7wUl4gVzC+h3ndYS+InUxS0j/LNiCPI"
    "cMiBNRXAXNLgiP6TRUHWPpzNHrlRKm0pHaWrexrj72U48aaHpNN4KnMJ3IJg9S59sKePnPkMWu8Ns6yAIRe6xi1mGiZL/XbqJbXA"
    "9vDK0sxy9lEu45fEDkyEPhodHRu+ndBdi0+RYpqHwpr0HMxfAjOrBoxf+/ZhBMzyDY1C/75l0Cve3Dn065bxJITWNAy6sZZf0V23"
    "lmCbAKGO0R3lihu974nv3CO1jwsZHt7o+piZsZq+j3iGdnKkuffT3H8QT8f7kaaghBEy1FnpuHiBK9j+b+denKTXaX4eQQdoGoy/"
    "2IQv0Y24H1dzjgSP2Tu7twevXpleDHLB00QNy51jRx+xmGh4o2xO3QmJd+G5oM0dGJvG0TeaM/EXDozB7Pk5PCfC0YIjqaAhv4bv"
    "X2tJakvSYNNl48IAUBeWA0ON7Cd2ubwFWYwULhtMKWSq+PMCYD7g8qA9xiOc5CmAwF2oxDhnfiziGOzaZHSt+nEixAP3uTCwxNij"
    "EUPZCIOvvBu81HnoVwhMLGMkGWmFT4YLy4R1S1FksmmUUXAfpdg56gak2sg93RGQDX/CbRT3tO7cF6k7OdGT5oax40ljxxACqeL7"
    "qDGE8cNF1RCGoJq7E8F7OrJNNi14pv0gjCmy39g3ZsNZHcl+JVVbZB/GapTntZakJjhyEIlFNmhHosgwz6LfACcFR43j9+/tFFZJ"
    "Wr7WnBqY/nUA+kjDSggwY1Sd9RIMUr80zakWsaIAEAWl9FCCsaTxxQA8WhiOUXPuY51pBqoX6PEuN81B2/zZQlKt7QaoH5lW6Yji"
    "Aj4/pA4LQ0pogdyYOsY31NbfgoI5ctALgnfWk6HjNBupeep0HOOaDJObodMCjoUXy1keQx/OXDTnb4Ebn7dr/YVluc1as9agf+Hp"
    "wmrKCfXmYb9UzmrUrOZFG9KPje8IEelj06r1Mwh1q26Zvda03qu3pVT4haRa+2FWVQuQkQrWrBoVhEw5BBtTgCQVg+qs7o9FFC9b"
    "ZqvWq/XNXq2Df+udciMARvPQalIrvii1whz0oJHmoCnXVbPaZre1aJlNGSnKavasaQt+5CY0zUa31ngGNVmDRb1jdqb1Tr1Vb5uN"
    "FnxrN8toA6Cu2YEcvXa9afY7FRlqAKbUIPZp0TGtnqqxVsvsHFqDaQvRbZqtMqLTVj2PP+TE3rMW9XyL6+LDMwsqbVC7aq1yayze"
    "HAW24lutsqnPrVUN6mEr2kBDqXt6ta5ptRZts9WbAj5IpENMUSA+rRfaWuckqFMf/qgiYL/WM5vdGqBT7hb6vKIpnPx9YraviszW"
    "rzUX5f60ulkyH+jXNJjZkOaD3upngx6fIxr2RVit2uDCYrW/LdbeqrUWVrcoBbplfPo1q3c4KKe3ML3caMy+oJ4/Nr4sja9GrVsb"
    "QA4cEh3K80MhzyVm6OK/9S5l+L6YAcr38Wtd5PhRIRUl+rRJKPaJgk0hFI3oRiUbgfrti0wUWkiVhZUNAgtkWPNJV34HWdmVC9Sb"
    "F00lK1gkO8vpXUV6H7ObDUv1ocs/HBt/poaP/WiMDpDbMbYMWji+Yb8R/DRUVXYX3SnMegnGbrGPgGV77Tb0Ecjhros9QVK53jPb"
    "ffpThtipdS+sRakVlzgM2yg9e92+2e926zDym7WW2e7yvHnUuwz1PmHOuta7KWIHBOsclocNKoTOothRnXxHLeptlWhtgLZA4coY"
    "MlFU2Wy6PRA0XODUe2OQHKDjQKiCRAEJH8MjyG/4F0TXmJoJ702QDYN6G+RT56ALHWpaUA2MG/jTkeHVeu+o5uCmpFRBCGL5Pqhn"
    "aCAXWlBtv0t/e89aZr+NPIQZZYnXMfugfi2zBYQB0dhpupDUERK+22zB/80pfmlRLln+91t1sz0gpAryDunUrjETILrZnvkQwqAO"
    "PFX6MGCjniD7pR4AuX4BTKs0SdpoDLSUcqu16K5miMN+YeQyBNxSR4CaaKJh0Gr3046wkM7dQRd1Ya/D/3IbZmD2e3zgiLw1dd66"
    "yKsaEXl6MqEaKqjTvCjYWc2yhddfb+B1zR6owyb+fQiWClorwiyDOhadjAexYRdATDlTHcuhnm10S6zzvFPrbYMgGoEwwqjBcanB"
    "kL8h4WJ2OjAMBp0pdNFDCUXkjEW9J3Wx2bHQEmi1rWcwtmBogWHXk4ogJz1pSUMN8gBQyDQFK6AJjYBBN3iYASQGZKN3fFPSsDBq"
    "ka9Z9w/q8IzdPhB93wBp0UMC9trPwA5WqO/WonOhtCt6i04qwafFiqGvQJW3FX2gTAaLq4miEURIMydC+tibbatNpmxzCjngpUZ/"
    "c/YXqIp+s3/YbCqM0+aiALeGcGsyXAJYL4K1yK7rNQ9ZI+c3d1N1Vlch9MmuS7XopEC/S5g71FQyClUZGh4wfBQKqNa5sJQUuChp"
    "8csmqhQwgaxGHYVBGT+oqs+F0VlZH4GEBq6xchMus4uTjqYJiJuNvjQ6cDCBLugD3UH1DqzcKMNC9AnViVwI7eTWO0UrZU2EfQkQ"
    "AUBXAbojgZbHGMJQAe59BMA9ItlMITFgQoDai/Os2WnDfzD1kVLBuGn06A8qzl6TZnfKrrFyhTrtOsKCOUS+ikaP/kwRTJ3DOjYu"
    "b8o2sdUYN9BWGJAx0RqgfrDgpWe2BgM0HHqDrHMQVrMB5DgYUN4m5a2RnTVgDw23DyzMJdQa1dKQVMtF2QCpDSqF/BSNnn6f/S3r"
    "i5akbLnEbxenG+28TnqnMi1bZb1DyJ6r7LSG2mgGyweUW7s5SDvIQvNLISFxcHWA2NgpPCPORGGC11XMgQbl/DSnbKCW6TRVUgIM"
    "YRhBaAJy8CgfCX5bkb2UHwYmdD9RvdctW7NIziaqRyLRCZEI16BwFmlBbw9gLtQkP9GNxX6alFpmEDBaGYfQA7AIWLQqPuqJfOwp"
    "zXhsLBQd1JkOoMGdOv8LUr+DWqDzDueqMOtvs+81+sIk97Fxo7TIFyrvDojuw6ZKw8lmG/wLMwXQZHw8wRPaT1JCvX04kAvUrTJr"
    "DnhVx8ZpWQFbak0LLV1YrFHXN9Kk9XrYNnBjApu8ZmuWVh+nq82yBw9oDZN1sgTQv2ORhIMJ5hQGWgss29Y7mohDLjb9f7XCOMEW"
    "lo0Tq5YZJ+jcU8240DxR9ALOxSTgCLoInCyfOrd8FF4HnOY+AfCE/EER+S6MCpiywGS0VaM/wsQGgVmGNYD5JjSmabkoSWkiRrY5"
    "KwJvHYUp3AStg0MThh4+sb/ciGzQu9J+boG+d1Eid2vsr6iGj8irsvFuQo9JJipYRmZ3CvYsKD55dmKS0XRoDdbMaDr5Gc07pblH"
    "ZnFm5QJ/P+nL7zBAFM436O92QRQzfftaMUBbC6tfnv7BoEGXbyaGwZpqvDvsKWzf3gUQH41LXl2/jvpdeldaVp1NK0AqXFisVz4r"
    "WoDAwU0QAzBRoD8quWdxqWeRzGOj7LHC7ug8aSnt0oEqvY0kVjmlrJ4incbZRX2g/DCoGJkwYnuq4dZYKL1QzSfMNHhRsr+tJhIA"
    "/kbDQYk+0seWovWtRet52yS/BczaTDQoOs9xIsxS6jyJan6TF5QtWVD284KyvQqPzqqPFtb0UDWzhqHSyQ8V1BX5saLyYpu9Hlpi"
    "Zgu42MQOxz/CtO60B+R/Jz8R59OW2e6QQFLk7itzNytyq2CDiYHe/D5Qu99H7Wr129I8lqYpjZwY6uKkutfCAgN02FsDkGwlqMCx"
    "ALatWGSCtg86srxSLzQt6n2zwXr6p43neJJJA7NOMmnQC442DeYko6ZZytplOZtrM1oCJs/aZTnXZ2wKmEwePFfNQyyVH6tdkT6o"
    "dcvu517R/ayQnt2LsviF8dw9bBc8Xu2Cs5uZNF8XMR/g3LddG0w7CrHSxnWGhtlx0cUo3IxWjb/lU+v87YnF5kMv1bqjqVo66uOq"
    "AcyYOx/i/j02Pi9VCbrEOrQaBZXYKwxzy1IZ6CWN3F7hY4SRin4ts99oTXswPnAK22vnMvTBhmjgxzbN13vyMMX5QFmjg3poqXwP"
    "qDYu+FLn07KKM3tgevXr/bo8DUPB0scVMRDFsjumTeqyW3DR1ZW6bbBQL3T0UpfLM0UP4EqDwmSgZO4yODa+gYJs85a8WRV3ZjjH"
    "xrub3I6rUxf39bMT3kvj0Q3fOLY0Dm8Ue8h4bmkX1k1hF9YjypHuwsr2uOJOgltxTHmJWz5u5S2tbOsUnvG/pWCJDv51DIqB5+Bf"
    "x/DwON3QYRGgHENE5HT4g2ME3jyJXNygyB4Av4iDm98wUE9vOJjoJgXw5SItOb9Z8kMMGp5/yLbE0DaEWx/3M/uTMkXyeyyDo0Ts"
    "n6VWHLNdMSwRj64QCs7IcadelDhDJ92Td/QOt5uUCS6dVOd71kdRqRK2J6XL9hM7DttfXMKluGXFcNieZ9qvMnOAP9gejyQK8cQR"
    "37uCm4yhB2nvisu2pDwCyvhi2wY/IlHYY/LoBvdt+KWDFIV9GxkY9e6PAhT17g9o0Tc3fAPIjTgYmfiXHjDGpZe4wIvuOW7y42nO"
    "eBrGtOEcDwhPcbB4wIQ0UrzLcOEhqeLF+fD2+nIaQHdcJMls+ODB1dWVedUyw+j8QbPRaDygnbfM0mo2hKUFT/ntszS3kbfPQjeE"
    "Ew/wKag4s20NaHZvDbrNA1wVtJq4fN5s0sJIB0wSmJfRex/9HSCIGp0sfwesjRbOyfpWs0356R3mT2ClNNP8oFr6Dav7DOZ1jW4D"
    "F1yeiU8cBQ6qxjAYcEhNjkEvhcR/D6R0lo9jnoGhhvHsz0jHU93PGC7tFBLDtZZvSkd6x6amuRklmnnKDLL6RXZW/7O+OWgN2ug7"
    "fMa/cFIwQL0uI1WzxwABHlS/oHBKaIYV7xhoNivFq+/1a6JRPD+2l6ruWM8KffyjYIv8PmoUvU541ffGU5TpS+M7krSMrV8zFi6e"
    "8RVimHO4LFtv6WBqsrSfnmvf3oiTWponb5B+rCW6ce1phy4esWGHpKR90TiyvkhH1pUfTMKr+qV77V+C3CmMsdJXxwtYyA7DOQOA"
    "9XgceR4KH+96hvunDZBOkOTGv8qwQ+VpNjsHXXPQ7XbYS61Ha5Ats9FqiZf2odU7YI89llWU6GNil/0+aR00WSmWbCE0UYC/HFrt"
    "A/bIKxAlqOoW+33S/ZGmtYgauqksWmZrCrhNGAGd3oC/AW7dA16hyCt+WapAzyKnuFR0wGG2MTN/ORhwrCFjv5bm71Fqgz08wRq7"
    "Zhdz8C/sbz4NzOkD9tiCiV6bdqWxDE2OF/4+aR+Iz03Wul5WoMlb2Dho8pVhwrVJPxZfKW6y3wNLINvIqM8L8JdDTnxBwZSSmNim"
    "H2jbj+j/ayFEmN11cfmA3jjWLUrjL8QYTU57q9VHjHmRHu9QIlj3AHd79Bs9nt7lRKMi3Yw1upw1qIq0SIszWYuY7EecEHWIN9pm"
    "o92hZxR0jf6AntsWyV2rZaE8anatHikUq9Wjcl0QcvjablL2bqvTZu999rndJchWlxfvtRg43PcC773moE/v/R5V3eu2epi/2Www"
    "cdgeEDaIB74PWm2C34Q2wXur0e22MX/L6rTw3ep3CV4LugleWx2LhHirO6DsnUZngNnbgCi+90EV4GvfQpFNTAACtdXAj+3uoNfC"
    "zJ1eH3HpWH0GrEuZO1w/dVlLu9CQPuYGhPC102tQQ7t9AtaFqQY1BLQKfketMmCKmRRrrwvvpG6aPSRk32p32Hurh+X73Z7F8lMX"
    "DaxGi8AR1QaddrfJ37rI3uwxZdc2/2Wc3BYM3mKjkie3chzO3w57gEmjg5oWJAu2yKJfGNeIGG6dMlvNFo33bhOR4O+gppB8af6+"
    "CVqx36LKkHOkdyyY5h+w32cWrrkOkLXzoqabSpouH7XshQmaDs8lcne4nOnQUGyvUpLv3LdT/4wpya8kJfkd6aDnqQqq0pYlXVWl"
    "N7+4u958W9KbfrBKb6ZfnfgiohP0LCJWpjfH4XTqzsiAnXhMc9ZxAvBP6vOf1Oc/qc/N1GeLNEWmMHC1mO1iZhIOlBXTlel7UcH0"
    "UWKSDmBinN67WKzVT/N38afZw8lWC0QyLfA9QRmONQ4Y0/S4rkRSN6jzxRspYfY44AKe/Qr+77DHJ8BkwHVtplHoI7wxbQNvbXxt"
    "oS6iV0DwAN+tLvvc6qIEb3VAN9Nrh7Kj0mXv7TZmb/UY6JbVw88ww2zTO9gW+G5ZHfa92ezhAOj1m6RnmqC5BugAH7DPjQ4Wb1qk"
    "OC30mSN0iylaeEfFC+9MEcN7F4tbqKbpFdQ2ZG+QFodXGADwxlQ86CxU+WUdNmBsPkBzoW/2yXqAVzQm4JW1swH8MrAgc58ZHw3a"
    "NQqvzDSBVzRV4B1NFxoewF+QHX4aXD8CHeC9Z9GUGgZpG/VlDy0vegcjB/Mzywy6Ftrf5wOy0+5kz4e4GZbJROQG0osNrhdJ4HTo"
    "AagwoAHc4QWbWQHx1jkEhd0ftMEQyLP7KpXaTHz/esxU6pdllZpqp3UqNc1YpVLf3l2l/nBTDi5KJwaTyMUwQjwKCp48//7Gfpvm"
    "ZCfZf7hZ6tnhzR9vNgoG9+PN7ygYHLU5i6X25xsWS41ipdk8+BswQwy58HwpTzn3khdXgQgHx+qJRYS0VXkQTLK3p0V2ZALfAXWy"
    "oCtJ2mQlhMceWD3+DI+OIopmFnZuiUxhzubxhenOZtMbLTAicVy0FmSN26X+PQMALNyctZ/80Y3OAUyQxPwM5n5y/75ofvoNg9ax"
    "I3q3y6Gcup/8oTkCmjGEtUBHH6QJNXzmji9yLfNOWUgdKKQv9eGaFsbKuHu+B/Qz1hUFLPShjJMaoerAfuuoHwD1oQ2CwFIsP9FI"
    "KZRgcvrpQglCXWkoweBUFUoQuH1lKEEqxUIJ0sD4pKEEocZfO5RgdGp/fyNkZCZHwcC/xOOkcnA+opPGz8u+f3+71KXQfCx2F85H"
    "Eu8JhSz4XERt+Gzq0eghACwCFh7clV7deRLyXFSKPuFZaVAfqGP803niaTy2y6QuYUlHSCmmmze1QbixA76bIc3jh80Dho0OpYNy"
    "o/XbYi45YOIBD2YozrgrxLlD4eZ3GRiYuE01x5zxsA71NLSFgzICMx7xeHfFDPYOBoDYOdZ3b3FNx1nCnAxRKjSVyTEKhRrZUrMN"
    "H+RvyDrlaWC42duLebIPuvZklpL15HKe0FH+8DT2ooUHfOtd1Z7zxBc8MSdbEqXEweFi4oBBPhxjYLBneHR9b+8eKbHE9YNYezQH"
    "WulihMjFMcW3pxN4HuFfEPkKkmsF5FOKxTyDrsOo/2KOhsYdy2PpJBUp32m+PvKHiRnAsHnln05hWO3tRVouQV/uH861YiIaMEtk"
    "7JXkRg4F8gQozNdn5g8Uf1OQmOSloWqYH2D0AC/wJFJnloe/t+cTj6uKUhjA6rLu3p7Ly7qTyWcYeOIZz84Fi49ruStx0qsLQ+3O"
    "OrRoCBcGBSji1QREi+ru3VFoAAJjq4h3JABokzXdhlaJvo4Sq/HYiJYVmMhcQKgsDRTfJErKYrMk2YWwFhYAWGjwH8gnT8coe7cZ"
    "LGThJYcug1ALPEnSoZpNwYhRjvLPFuoYxOcwAhkYgEUaxUmqqdLMoe3mMrtGLAM1xnac6va9vdiY2iRfnCPMQmQ65gJfJXB8fQkG"
    "yhjEIJjtGi9bmTvE8AkgS5DSILIRYaZgK4jC7SG6NCEXqQUIg0wxRQXJY7egiKKQNLl+nrpxwtRPKgs9VhfYRBqaeLwTwXZBFgBF"
    "molzFLfQILDOKRA3R7K6ecF66bsxekShZ+4vTiDimg+i0Pe/KIVW4AckWmmkbWNOgGlO8Y1gJPnZcGkMfRg/UdXQiu0wN7RCGEyR"
    "iX1azju1x7m8Y2Ou0jwv54UgKUDacaA5qRHl0n4f0MFeTWV5GaIhMM5ZGJtZBNQNmBooBuK610hjEpfAq76mFdFHbnQNvREzggOS"
    "cRN7ziRj5QDXjbMsj5rF9f3JpgPFPjMma7jKjiGLyv4e4y3bjDAO9XEROBD0bGN+tCelzCVMppBlHSbYVgUiFANrhnObCdkWM3o+"
    "AzsM7CP/VCzOvAyjBCMQ881rLNvrcN29D6fhBK+jSCNnV16XwEIIKwJni/kG5blyk/GFVLuUHceht695TLAAncZvQEWL0F8otRIS"
    "WJqYUSUJGOPfhDCh0CUEJYjlbEIyTEoVG0yg7cuV2wKZXZx/eou5l6IDXzzTj8MpjR+ePGLDGCOBErE1RYxykzViyRtB4eSRWVU5"
    "GRYiTxojCJtRmsTx1vJ0ezxRk+nUg0mM9y2bBFZTv6LB8YU7Ca8QltQvEw8roHGrnl+u71rovFkYe5o888zwLkOSmyrCSHOoYG3c"
    "pRGsNmoED2Ad4C7vEX5nMdRZv+n58P4sV1Us+kJUf8H05LHwpmcOhupDoKryzAVTKJc6OiYgBnD4F6LP5bLzUP7iNXdDiHuaj4Ut"
    "5jei2VURovMBqxv60BfdICKKzSIR4y0JQUmltRtHnuiikRTimvO2zuOQLfV8EOTqulkoriMnCXOByZb+qYiF656SRys8VejTWwrS"
    "Dn3zNcrG8Rko1zGoxempG5ks8K3OAsyRsqVM4QlqW7yr72waXnHN5xjzE21yQrN73PF7Sm6E7zz3zXN3lpF7LPnwQnze/3GKqwAe"
    "MG98itHRIS31iIvO5Z43chFpJIjrDMv6NBzjsjkmmXgvU4rl8lYgOGQI7s9gron3QUW0Cg4ooJvGlJu/RFMdUKdqPIMJWj/QBBrY"
    "tLQlU2pJMteoGdQCqQEaSgPcaKpAl6pA8e3pGj3znBj6HSkzPy2veUx8dxqeiwi9jrjnkCVLlxleutd1vs5fGzT+kN1QSNcWgsS7"
    "HNbisTv1NKt8K2bkTnywVugaQwbZZF9M9iV/keZ1ncmPXH6WlMtYuLBTAF5xPeewZs2ua6BSgL/LuORuUyxcvshzlrJc+UD88QXu"
    "KR9mpCjeGslK1/lIlKia8vrNsIaTvgwwZ6pC7VTe5N9kPM6m3nUdmg1EsypqZxEvpcpRJUxdqBkLZ6DcqX8e1P3Eu4Qew/DNXpR9"
    "/AnMK//sRjQF+nzmjr36qZdceTAU8viwzSfDWmN1sxhixVaV8Kcd5BL6Z4BC/YqzpASO8pn41WRfc3TCQrTTvaIIfqtE4Qw0Wo6E"
    "2zSTFVZ1XkVHlGhNtcHYzbKcuzNVHZBc2QZGbXEG4wPZoVg/78pV9SfhLHszCh/ZpRzV3/GeueqvJICrP0PNq8tDhjUgGH6robA8"
    "BUA5SRqd+wGM08irEhRiM9lEKsZ2W9WsRmNxVbvnX5L9K18VK6Qz5rhQ5oD2AZeCBFR9xEZVf5XFP1TwB2W1f6gU/A11Q/EJ5sj+"
    "O1SUdZCik9wIB4PVZ/fxuqcgtMEeVA7khglSXTGaTlEpStJ8HsUozmOP1entl2jblOGkDculRjxRTmM9LiWWOpSGTb10Q7Aroh0P"
    "a7M6e/FyRWqtRuMyBtRP/TEI2Xe+F2mmNTAsw2w2DatqjMHEceFtVx0V2aq6P4E5eYZRmuMq5CU5GcGozl5J9YHiwKsfZLGptCca"
    "5qAlCcvlpjiwFkmXPIcfGQMnu3z20o3fVF8CagT2Ebsi03CIf+jU1Iz95elC9pDNSTcTiQeeQRIrzjFFBddUmz5g5gMGAh84S126"
    "fzSVLTEYtniXLRofMFAopZZ/zTEshk6+DCfudGkEowzQ7m2wdIYO7hitvHtXND+7hbeEUP7uXcSrKASpfvaCcgJvwk2/LaF2pnSG"
    "TkHFifjDTt6CcHj+h0wBloqlpxON2Vjs/uVXQzol3OoibvVsfIDnwUoZ6ZRYmktocqdoEuLtBKi5pS8sAS9VpfniK7TPV3Ia73Oi"
    "NnUXJ/VtKkadM/8ag/CnQU1BZGfRTumFtEDDQE3RMIQkddAicAxujxzwRrDrt5A5YfLN79mSXyXuHTnMUIK5eOKwgoyRs5K5d5nX"
    "eVkwe4DZmP3hGGSUPCWbJJGu+FJgkYJW4MAHWhnfTdGYhT4+0OJYPITBgTa8IzY783FxWyAj/n3M9pdhn8CUYn4ZFGExSORfnKT+"
    "xcd8ribuaZRu/i1+ym7+5aODORVpC1zh/lTGeJXfFz75pFdc4krMtuoGVsH3xMPVNfFc8oW/yhtfeb6X/IhwBTRJYqzAHfrm0o/J"
    "h/QcR1Z1ThzJq4A1WBbvRfAZXUewIl98EV49kbtFlYmsl1c0u1+B1Sn0/Y9s1YFlYhtz0jwNtvKZy6KqLZUR6muTOcNDfZHnviFW"
    "FaRn7uwC8SeRe36+hlpvPG/2NDj0vSu0NldkvPSD7ytbBx9/qG76dh546r/1lz0L4b9BTr6DdX3OcaY9ZL4uELfs+U9v0JJutmb3"
    "Mt9rpDc432tkF1QDQZdZEz5djSfCAOAcwvxN89PVdzIzsbbyTubSLuLCbSxcftFZmPAKb9uC2vBimjO0cPiLdNJ0HkgvyMdMY7Bn"
    "FP/HKpTJac6WNzj2TI1/450Nv1UsUnhmShC6zrZiYYev9nrRIZfC7PpL9pL2Ii78ZNcbgdHC5GGaQqYJS+PecH5pr/A/8hs+xP4O"
    "ljWtm72S4ZF+QAOAXph6OcjnZTrloAggFcjcTGLQJLuJEogz+IokF+woTdCdwt440o8hNY+x/OWzYJL/iEt7L6EHv8+//pC17nk4"
    "B0UKdHidEam8FZCvAvE+2NvT0kUmuaNsOdOqRSFpW+Bjjv6rBGoUa0vs0xfT8NSdigbF4uPEwzgLN6RXRRq2hO9JzCT/3t7JxByD"
    "ZOULGJhJWh4jzG3GIOKzzdVoxSqYpAh4bWzZj+MirTJRB5fK7+Iw1UqD9J5Fuy8+Q3VTVYbGMcee8bP9aC6a7wXIYCkpvSQBxkkJ"
    "toKWBWLRggBZNk5GEw4k1bniOmaxCmayncfmO/rKrHBqz0MUNupG8WuKMNcjYpJnOG9VrDoCLLEQ58ff8jsN9/Z+mGoF/Piuhdx8"
    "TvYI4H2SjH34uOIdWDF8Vn9lmKtx5v1FMpY2H8mrfLn+y1gvL7RUH0C+cd7kdFVXvh3zi2ELgvSDRiRvsqRciD7PZfFS3t+mkD62"
    "J5ax5eLfzkrtLFiwvLc4u2Sj2barahLDd8qXh8/yG52EblOfMPFKl3Nle9ew6WIPE4vPwvQClOL3aefVhL6f4A7wXAmmXtISBW0D"
    "RC+V4JZLWiRd/kzE9nJJEY20Mm+B7ZLYxYxMQelDTcWkWQlJmem44Q7QQLY3bqmEUOK0JzHV3ip24Hp9pOXfU/YU0lOyVTxdYCdl"
    "b+Sy5zIbGZ8UCAP1jk/5Fsts/8VwWk7DbbpKeSuzjyZXdK/EndI8h4vTnK8nj5i+t6dATezXzQ3XXxCFqQoFuietNLxRJUxo4zqb"
    "FTryaBNTRdrJ7se4ZQ+mYak8Tkek3DZeSWrblMSB2qQTXVzx2eZbwjh0tqmMtpsY7DBeWlCxsfoNg8X1ZEUNeqmX7tiSvT1bK+Kk"
    "3KO8GVoG332cagK02EsjMjOSvCXZispcJGi91EFRCQl3I3nLoumszF7Ig8UKUlNZrJCHYZ2ydAXyBWFneyMPN5+q5qjqpmXfy2Uz"
    "41DuaP9MY8NRNvrLVk62gcxx9sU5vKDm801Aki2qJ/dtJ+fNl//506UH07Iai4JQc4NJTcOFLb78gw5tvbBGUPwnXWPhG7N3xSxO"
    "aMDlGgDSctNuyZI+Co6XyuU31T/Lv9jui0Pnzgpy67ZEfbuQBS1hMedmxn22g4vOISW6WGVYloGlQ5QxAE/G+HA3bM9ssQQ76OOg"
    "Q+HBGKPynTFBlMtkoId1DHpszT40Zo4X0uJZaS8hQdMNzZ9o6m1kI7ETO7/hS3//Pm0gjlSdfznAEzRltFXN9TFA35PXz5/ZMkVx"
    "bi7N7UqyMT9c7HJVXCRqqXzzA59M94J2YjYmG7pxwiLm6biHaMU2WTyQyO9PFWslYo4g3H5iWixmGKklks7CccUCf/PJP/DkHwrm"
    "OWubyZbObafhpHN9k3Zoqfb11ucB2/tLi8sUodJg1x/rRnka9Xqu5UAatztgJUf8/tAd4dPPm/mSewj3WBmKiUFZrRVpJOtE2ach"
    "z1kfV02+xDwmb06UyhV0rZYq43XY5lW2Cr1yjhyCqkwKbKpqqfCxlWakz0pHytjBQS9lQXEK4bO55mWMpRuRvVtIwVuXiTfrXsav"
    "hstTf5BSfzBCWyqK4+YRekChuoOpTyYAnfaK7dDEhaX7vjGGxySc3XeNqe2j12Juy6c1SMDmsJnYMzeKvc+noZtocz4E8GJn3Muv"
    "+PQ6nOn7XmnoCAe/LRYB8e5n2QE/0uK/wpVDP/h+by++H/xxyrZp0pbDbNhy0hjlGrCBdlyf3Hdm1zDExhzaD2Cy348AGlt1zIH7"
    "QdBUAQ6IZI/rZwwaTG3ugIRxh5pwA/1ai/cSZ9AU5NOo5MSSvVvF1pUQNrZ0N0JHKIIVo3XTwSYVyY03T/IoSSMPZ615cc1asYnE"
    "BlHt5eS0VhD8mHzkSKLaOQYjkU42ZjIa3fYUfGDTvp3PFKSUmq3s3ApKrvatbdPFa7HifSxvn5cXqw7EPouq3fSZA4C9SstXI3Y2"
    "qhTEZZgrqMopnA5LA3dE0+Xi0JOPbp5OqtDI1keFjmTWxj1uxzEVTGFdjpzs/nKAenrjHN9j1p3ObTYfZMEJ3xEiFpBRWz4UyFRh"
    "UfLqTkPcDWRihaO1OZhKTuc/yOAvFTUdTrXbbBkn3wl8YT1zV7CVIhGaJh7eRv5shtbhwkgPPg2jU9b91NGQhy+tfGmw00lD/9TI"
    "d+Hwyxsj31XDr24MihE7/O5GPtJwdrpRnJuz099RnBtqc7Y5f3b6O45zc3n6i8S5AZqtj3Nz8Wnj3Mg4fbo4NxflODfnnzDOzbl0"
    "RuZEGefm7HR1nJuTLM4NDYxPGucGavy149wsTu0jbqw4x8YNvhX1j8FS+NJhlvn0lN2qcGxcy0Ay6fqqcGCMTlbZDzWHSXA83YNv"
    "/JApGNi278uxdtJOZEe/YiM7AupJh8RuxdaOF+VtCUd+aUUsH0v/icYvdYi8s6Frck8ov9AARO01LjLEdBKJ/BaeGYskGPlGthVR"
    "2q/ItJwnVBwud6Gxg17aYXJk4V0BZb3pmoVFtb29UhIXdq6RSiS2FsdMKYDd3AD2t7MC5G9nSrj8uPYOUIV0PQYwmSWXgh463s3w"
    "U4gEpE17nlil5eev9HTRGyujp/yyMSZnr4XFYvwovacLspguUqSl0hQW+4a84UZDGOcCZ9oB7TNnj76aYzyxyWH0RaCt4hXZwZ5j"
    "GNwkWWAYnsRO0YsTajuFkYakLlqUPBOx0o7gqaq+8UVFOp6c5MuHKZq5A5ppKgUHAMPuwMWTjOM3Q27opat56QdVbJvUtqMIN8Il"
    "J8ESSYpjoJy2L/nZTzrtmRnKK4dpeaEh1wHcOC6OvMb/z967rrdtJIui/9dTSB6PB7BAmqQutiHDXI5sT5z4NpadZKLRCBAJSYgp"
    "gAFBkYrE79sPsd/l/D+Psp/k1KWvuFCU42T22d+elWURfe/q6uqq6uqqpt0hB4kbQ/6u2xMKnWQHLgbi0ECVZtrC3cLM4eGwlTYU"
    "5nwQE6rrDHxZDSae2aBgZw4KFkldQxYgRM96G8iRYAATbtz1ug+BlJuRQxYU+kTCvQrYZzLeSAkeKp3Qz7yUNoEkMUaakBvSQmKK"
    "CrdGvzoQ/uYQhZLE3bww8tS9PvRr3pdbECybzBNS7Y0SQm7ZOzrKSMge1Z522AGhsdUNQbRmaR/y5U+EXY3RIpwohS+gWtP3Ham6"
    "xgehY6nAvuOLFaAANosbCFzdYnDkm/qlqIOreo0dtWvlcVdjjtFSP7YkcA0t+lTYVJ03hfhR/k4xIB82jY+4AVkRX4/8zQXnqFWl"
    "iDZYygvFiqG2XCwUmUXyQsDPcQFNHS4M2iT3AirXhJm0TT6RRCoMriWgN6KjfftYj45kjlFCSONdhoWNTLaNQ+WOTFSagSZELBvr"
    "2lhod/i1UZD6Fvi3FNXEMC2NDAd+cS06JQsZ+GTN4Kshk4b0UnTqmkGZujv8j4FiBq3VjAXftouVP+Cll09rXE/5QKCnBYeK1TCf"
    "JdQwCSAOw39XC12fVtuVgFIdlA82HacK4TI/xhp8I49+MCxbqNpzuyvO7epNv4Xb4oWQPldkQmk4IrkeX75x8HDjIhieCxfVhvih"
    "t7Pl8lQuj7Htg4F3pXzBrEvG/fDQPhM1WiDDS5jwgl/NhCYnS58G70rf+pdmUxFJsL2L8uFLHaGfCinjQMnFUPmo2GcfFXvHVtw6"
    "Ep3z85aw/J8dl+LQ7XG+8uVT+wrGiEsn2mOFIn5TVDD1yUHnyrWPp5PLUtqi2Xx9IIckQ44dSr/Y3hVW8osFx8FLg0JLlTksNQga"
    "ogrs43qbWykCe4npRXsIqKumHmu7c5LYQvmSzhfR3fQTGUAKnJt3h5+/ZWkrppvJOyqHt+CVeHu21evgdQ0cbz9yAsj9A4efOrfW"
    "NnvjuRtKEWs4Or2Dfd/J0k/WRO74CUuLcfA0vr6ma8Ur8brpnePAvOBAee58B1MiKoS7SK+SV/uuQZ8ycZvXUHtBknM0RiVjwclT"
    "Jjei5UnKZxJJ2RaGz6uMzcAoPTg5jL6MYyg0zMZI19VQR1lEXgjqRiqRSQ41YX4fYJc6KtetGb8cSmkqoi/cpa6nDzMCuyTZe8dI"
    "mIq6eH6Hxj7WKC8lhFBiloy7p1EKDyJ8JfdRKVUwGmIsNS+oCY8GhYxfKU4hBAdsnxdYZ5IP4Ofz40CQXoNIxOfjAu2n88+Afe9s"
    "AsJ5Iu7lZztPBD9ceM+Oa4JgYsQWyPtF5G2aeXk2g6w3ZWr0AjvTQTEl0aFXN0ZQTBktMzmPTukHgYLJE4GhQmxK8TOvaFb+jxc6"
    "ymV2ckL+l051aEvUHpdDW5YhIyNa0ghQEqcf/X5o5Yph3SF0p5/X1wKfSfYX1WpiXopSd9Ry3jELS2SUrZGwTFDBCwEqtm4UU4dw"
    "cn4aetUV47Wm+qEH+OKLxrwIH4/pF7RbW8bbWvzQz+DCk2g0oQA4vJ9e4ClWM+KS8Pocdky73c55c1JgTdNDoTG6yThJZfMtOMbR"
    "Y5Og4//kKfXsyJ41sJUkxcgSyw+ZMigqUnsOCIoOC/HpshVXtDgor7WILKqWuN995Pd6BmURAWZFOFGOQuRqRu/dMUUUHYewzUqh"
    "ROE3bIHr67QpjihUekZEJ631d0XUiTkgbIj4n3Jw0XRpcNFfSq03Bhf9eMx06q1JpwafYxVmN0kvohHph9/b1AQ9EQBdEKzzwnuJ"
    "LUAilHwlqdbCey1+9mpIzYf6BpF/hW0GBX6ro1OyGGOHUMbx9lt435RJ1Eso/QHf1wkiNZKsDzSDf86SlGgVExamTTj9ZpKkWJJ0"
    "GbURozToDbYqqAH+VBTljglmLEBD6a931CWtOqjeHyPBgKbVYovTT0AJ50T5C0JIynS9x7A0rlLUiZ366tgs0iV/9AgLE0VfcxlM"
    "piIm+skhfWg6Oz05EaPB37hBSi+3iMj4ViDjDwoZT0bTyZlERQzsAtj1rcrlEL/eJxuPYH7xSDhVWHg/1p2gXATRcM3Ax7/X4SoX"
    "1aGhv6/rTLDrvzb3hQwflPiujJ/vMbd6hJaPTg6nBliL8Cjz6xTw5nb4qlyLVuYiMZZ6QnSkHyVsxR4pL0G7B+MwowlcX0t8qHyX"
    "iZXStVa2OYMN8+0o1GUyz2co0nj7WOmY9F8Ekd4uHzX4p9opKz+aAkrbMv9ZLwT8s/eA8OdRIuTydCCmEqRTWFEDMPhZOmR/LDVL"
    "WFpqFdOqx4NXLD0c/l5quPFw+Pa4TsPxfTO7rDsuqRGkrP9rqa5UDZR7/kFQgn82nQACgVtDYLfNPfxT9UyRRYEc4wb+ue6I2Jf7"
    "QWxEiuPuNW7HobhVJ88Eyzfba+e749oQ68bQpEsYKbCamGtiKu9+RF+pqUa9NHSfOFcl2QbdMaoxmjT4n0yDjVybEqtl/ukGqQhY"
    "pQO13BzqvS88fzCmnqRyMGYzIig8tkFBuTrhQnLNFawVzSnPN/UtGujLTXZrmhT4qCJqMTrWN6iRUsQNU+1BSrez2fPoxlxt9DKB"
    "QMT9hzqktKhHn2dxnsnfAIsRHmB3baT9JTtmwgdsybwG/zG/OJueH6Mb2XmlaoIV06aKAv4LL58HB2IGh14yrzm5sDi6+E1GtMPS"
    "6Tkay1U7JGOP2CiTzeVBajsXZzN3wNe5ZaAgxV8yfEjJGYLgiaD3OD9PUpScD73BsjnhlEZNBfTxPZ2Xdv932bHa9ZQI2xs+T/MY"
    "vb3o31qFRk/liQggaJrFWA+XupxGS36TvBt7afCJ8FI6A27LYYDsk5LtR3jvHhuBtJPJS7zujB1dykX7cW4hZbf2/TdRcYYXNU7H"
    "459Jiposz6zkd1TcOkPjVsfe/oJQu1FYvqMwHnPxbymLoCGYYuQTKhyvuoM9UGt5zC5wr+5gApD14ygdyubpxSK1tTh0jWbuHhu0"
    "iraOfSLG89IJTrvLPayji8W8SvesxtJSY5ri2a2NKyBtsUpaHgb4xZw8/kJGPp8j68CIZxL1ZC6IOmY08urRHHklwt++fW2PIGeG"
    "gnKJoyD1ui/Rp3rNj+UJk8i5ipNzQZcEYKG1U3oBYqXCv4akAuCGbV4nm3vh//of/zN0+XT5UI9ysNZK4pNYS0nWdVnctvZsv8/w"
    "E4VolID8d/DosdKi+R1yN2alAjm641t7yJ6uX5LiDIp1x19PZUwJE7GFqoRVzaexI1sXWmfR8gaASx47Ut+5RbzRZG7wWWXNAoFt"
    "MG88uk02q3cToziar8go/kOwa8O5PPXYOxwQ7ZMywf0+vvwBJ6h5LfKXdiU9yt1W8h7ZaPL5IlSLgc0hPvAvYxWgMm5CxGcC7BvA"
    "fBqGF5eJHqK7kJM9qxuhFCUaUwgUt0RqwuKhScOYZp1nacZGQGm28EJ5bCLBwvq0+to9vfgMwrBPO8QXSa63icsAHfUeubQIwzkv"
    "wni101Wot+j3NP2c4pvkQ++8vFyv4wtDQD0RT+tMZliqVFY5xmT95ceYLLXqMeaZVe7DFm48yKpqyhHPj4nKeUxsYYmc8OL/CeSj"
    "JOGmICFESiAXa7QqVamhJjYZGQt0OVN7diKcS/HmwcMc3bTbzKrMRo730Du1mUGpCjyalzQ0FyWUPPQu61i1HJjebFrAVBMU7I/r"
    "mFJZZjI9NuW+eRlvP3C5quKvLMuxDfMVvpxJiK+DlukPqgyIKklIrMLLeWKZXq+wKeytXhhb3cDepXcauZzkHbWAxE3BX8Cf86Em"
    "hXIOTA7l10rsmGxjgPYhQtdiaicb1C81a8ZyUkUvwwMmK+fzsN/d8rs7NXcCaIlVUvZXdTQChWtVNQS903kNkW4AK29hJdfUbFLN"
    "b7KvDAXYPudrINUdx0qXU2Ky5F5mOJaIkYlfsMaSci+YfwJYXMzdOqtMZu/E0SG5MNJEId7D8OsHccnwwjIlvhK6OiJ2FPaLociC"
    "L5uJOC6zw9PjshYLkmruOKCDM0Gj9ufS12iUno7iFjvQYKVoEZ2iXYKZgbdaZOTOX8MYX/lPYroOngGBP4RdeXHqX83PR+hp96wo"
    "xv6DB7PZrD3bbGf56YNep9N5AEXkHVqvIy/Q4NdFEs++yeZwAKx11nr4n4w5zm+xvTQbxjCkg3AMBB/mOvTDN90eBW9fe9h+2H38"
    "cHOvu9nu7fR24Hurt/NoCyPeP9x8uKW/tyjGuy6/1d7sbWLc9k4XKq7p761HDzcfqfIYt73Te/Qa463jN/Tbe9SB+p12D9uH720M"
    "Mf+4/XCH2lHfWxxbnsu/3hax5kV7e9vtnYc4Ltmf/ubxyPJyvDs0vZ6azw5OD+rJ74c43N4jWR7Gy6HlH2+/LoFqWUT3fCc630o5"
    "ovveXEd0f4bI8JxWvymYu4kvTXHc9+dfHMd9VsJYfCNZg6+YHOYJ42ZCDrUpCSgJo+x/AFUft7d7O5sI/52dh4939h63H/U6j7dp"
    "6R7ubOM69ba3MX9ra7vbW5OoxuvVey1Rsdtt9yBBoS58Q/GdNeP78aOHGtUVqoqtIFFTbhX1LfBDoiqgzuP2ZrezvfVaYpVsSmKd"
    "rCqxUn5LrJXlJVbLoRnfNHRVnqf2Wu4aOfUS6Jah7uS33kUvY9T9WEbdT+ObEBexpAltZ1+Oti8U2qL35hdDfrj1bTaiWxrDi3PJ"
    "HOwc8GgkxLqQzhERfYbdkiIDpovUOUdWD1L5+8ZyrKpb5rpW3Kg2OPBV/d0Y3Q5vVc/3+E663hmtaAu7xHT/quwS9qrc693xAG8d"
    "GjNeJvFoWMltdMc6PGImVjjf1BDU8SXla125BJWi3vAIJ/qck56Nx6OkFLnPXMBhHI/xaR/HxsirTpfEkIJ4UVrTJSW9uzgCCrl1"
    "lZyTT6QibupFRDndFX6lBMwCHZ6UIamd7GAY3Tw+xTfpecnTjnjQV3giUO1dY8ldFyOCLsTgFB78Z8anR4dQQucu5uCeW3vnxhGu"
    "C/BXl/3evR85qFdjCeU4R6zeehBo5zpyQSkwGo2sOqRuM9B2yyDSUWZP44LAyI4vbWi4/HjaHEJ1RAirE73BDHew+Eg1LqOoelLt"
    "5bvK8w/64yOXD3bbXo3/WJMsKt+GoohFJTFANGCAIzzeqSG67SzdoyIKUQQy5N5VlienSRqNyCeDXwhJFh03exiH422WkoFelWCg"
    "7ZZ6ECWCdvxo+2e4iwdXXOcK4Udr3tDXXUlpq4E1vTQwFimjYmiDJfCa52oM1QjgqOmg7ScLBqbTtKssMQavcXtB+nL0KTVZyCbV"
    "+9XqaEW4SO4ZnS1qAtbkvGEJIPBIk04kDFrTF/cAFv1paN4oonwAa0D2zXw5WDWWpUPWY1Hl64hOFQNuAJ7AIq9mrKgMTCLePV4J"
    "L0rBWI2SkzJmHNjLfPg1MUTtAE3jbgOBL0Z2htkfMBFN3up97nhF0Oz2QfmrwKCQhgsC8VoefRLys6TCXSigkDNrSSNd9IJqp6DT"
    "RSc0OYiQiPhzi1F9lY5RCyb50xdzyXSyEq85ZsfJaNrIIoo4I6h+SYsljdyS7+MeK6ydQXpllw0bUmT3G5y9JAiLH7gMoib110Qv"
    "MLPfX19XiIQJCN93Vfh+JFd1EsbP5+KxRCV0Jw2A/dqVoneqnGXhElWhFWMllsqbgRJLwTJ1yUq8zHLQTl20Pm6njK1Kl9HlKiKz"
    "fVlXQ1xyNVSZ3xwc1BhaQ3xQ/Uzetzxu6qmUGtIV2sNpTu41/+Z6Vl3q5PbVRLy9L6ydTQsEVuuLO5chW1epa4SWJMcDtIPXUE+y"
    "NG5sZTmqoWOtaYhwrEwpmsPL6mbtCLM6pp4q4bOv66F/hq71ja1lAr/cKpWtxaBlPdCrmhV7oLKNONo8X66HZLYmuK4A5ZI6pAX7"
    "m7ukUaRJywpUxirXLzs5mcTFkr65wBJA0m9ioFYEoii96kLBb3E6tJh/N7tpJHFctIbSrdJDM/bd1J9Awd/XawUjb+pVoOUqvfpS"
    "OWRGRpbBGburHB6ygYZTpHbJVZ0bd6U/HkWD+IyUc8YQa1s1iq6CRVKku00XEldv01Vrcl7mBepO9sl5/eG+9BiGSl9wEhu15ssG"
    "PjpdZeCj0y8YOFT6goEbtZYOnHi+2gC+f92tRhBtDKEpHYxTXEfito0QmprRq0TR5G2IsTOFisG7U8IH8UmiD3yj/YS+H6aLvTul"
    "hbBq4DtSXWOEjqRFDfHCpmhLjQUm23SFckUSVufUUo8EQZ4BscuHFA9xacAwxUAvjRmmn0d/nq/k0vDz/P8gl4Y0Z+3T7dm84pTu"
    "l/mf55Tul7nG9jfzOqd0n+fLndJRLXZKR1P7U53SQY//aad0b5UIWSM+vptXLriUKjZLqUL1qkDraB3lIp51IbGtvaS7rRqh91vW"
    "hBhOtjyKZUcPlgVnIXQlTJvU9ZCMaURfC+lvXetpl7pSBVS+kieqDM/ABIilc9El/vasUVQp0UL46id/RfKXSyqR92hkdSHu4IRz"
    "C/WSXxgBytecXo2jv5dz29Gf4bYP3yCziuVbhxUhIQv4NQ7ThBZaqfaEXzkywTWcFMifwr7FeP8ogVOyP9IuUDyJIEucgYki7CSP"
    "fta7AovafA+qHMm8n7uLt3PppePlnLbnq3lQr+YQRoy1ig7OM05aFQGeD/AWRtzdrYkqn8cY4uIirj3DuVURurmucbtVikjcYhPb"
    "NQ6XqjNF5GQZ7blaANvy19B4AH0qVGPWi+DAN7DCPOQ2D3lFVtiuUxHJBNPSUFzIgF+mERFN3V4nsnrFeq3I6vUb9CLLGrgZl+qk"
    "HbnOevWXtpBmhaOacVeTCO2Va5IJb0YRrrlM3lg6Vg5BeLvBcp0vGq2ousJwxXPxG/d/E/nQ27gL/2dvY6lg7Bhqri8YBfsQu5kW"
    "UaTyoQoxvsYhxusoYHQ8gbzCmAKIG3HB4hLHSie1aDlfENYYF83KFiZRa9KBz1+Bl0b3PbrEby1+USkF+1vBgcy18EypWReWyQDI"
    "FTUizQMHqxSKNLwmummrF2ECXTWBWw2WzCFvPVgc5p8+VPpdHZ+1zssGIpWBG7QPkVtrk5BoSspLx3WW5clv6OhsdOMGXKKtr4XO"
    "Cnv/pt5X1fjW0tivN4oq7VxlGJJ6foVxLNl+YlE2V9h8qyHzjRvjC5sRKC1o280UeRk07E0jQNBrvMbofFk/S+iI3AoNUOd/vwLc"
    "v0pDJjGph/sJRjLiByRn0cRphJC7RoUMQHDso9LirsK11i/GBUYTAIJnqh6XHKo3NPKHUjTrOGmoJ0ciyfGKk/8P0sIbxvAnUcKm"
    "UdxMB//QHfn7SWpFF220zrzfkl26GoS+jDaSEIm6X5KnbUH5diO4mWpu/nGk7veeVTevz8rnV3kl6mSU+porXGA0V7thFLKtm1v6"
    "QoRbbbDWMSPuRdwGeo2pAwuPSrdRBtvbdI9mqFNWKH1mWOvcUHzF2Y1Ov8bsmi7b6mfXVLphdnXF69FjMIqjvDzqZbJtkY39tW1z"
    "Swm2gTJIvml11+7zbh1kqRjD2oO1nruCTq4qGjcLQ7X6C6ModX/zCVXHJmmwuF8s5jnNIwf49KSgZwDpS6TO2gWsQvEPFTylG8I/"
    "CJA3DvsrQ7pZivizgf117raFbt+43ZaX0LMczcdyvuxuuHM2C1YvxNHEPxqNshlZCQcBxqmsVEIrFqxDP4xLdBt96Cb8LJux0/zJ"
    "vXupgNnr6DKbijs84e7zTtOKrdCILlxpRx6MK7Qii1baqF64e+aVelizCXCZAbHoVVzYhHGhx0P4O+ovy8VM3Sa+xhNsm4hb+HvQ"
    "Rp5ty5l3xiCpoa4B33k0FzEl8WkMfFGM3/zScRFAis/8wwZc5mRvHnCSmgNOUnPAeKf6ump0/FZcsBlmx9IVCXrHKJre7XUWntH7"
    "ktd9JhLWG3mrLbIoYwHFbVhmXl5ahBvLq/YJb5c+b1RN31yUw3+uUuYNvvRTAQEaiqJ5fgOkYFAJuixBt2nxSTJfNtfJ9OSGEvxq"
    "dnC5fDiy1HNx6bC0MNBK2uyolWjGHEDNl8KfzPPkFB+6cllGxipAovltiuciFPebZjieRaOTF/NxhPGBxXubLK+xyDkIB3GCng5O"
    "Rhm+LA5jUQk97aUDdFUPLe1xGfz5UpQzO6CPj0Z5fE8WHqI3i9F0iLEr8aIcYFI/LV4rgMGy7EkRj+vzYQvqw27JmpwBVz5Czvxd"
    "+pLiCTRvadz4e0jkl5QhFx/p6HJJEcOOcfmeBTL1anhjEXPzH4hibMV0WFd8nyNR1L035lJmyLDjy2Xdq5LLCuXxr9MkX/YQeiGs"
    "HF7NV7B141Ve0drtw2rWbh/+T7J2+2Bbu/02NwP41liCKTMwObPD6+v4IPzv/5bf4SHafa2nZHD2LM+jy3Yyob/QEb0v/hW7hJ/Q"
    "TYqR0IPU3WXjsY6XmFY08nnW1cRPvLTGpil/GsQi8G7/aoiObmCL+uJXV5oAHeQbG4cYOqZkyYUGaBhYy08Wi4o52ithHx8VBfrp"
    "B+F4jWcYo0qpRb+Bv1iTvEv7v16lrDnDosfxmizhUfkIAbDGVnATtm47iy7itWitAk/HXWMTNDRzQ7hEXobvnCfAgGuAGMBIldEd"
    "etaqvphL2ymwLY4yGMwAaAgiLy7DZIL9RAEBxQzRnl9eZSgOcAP6BbAwwgP8wfe/o0tc8onLsIxga2m8+mb+f3Bg6B/mf0hgaIDZ"
    "zYGhv53/qYGhzTH9eYGhv63a4H76E21wPxk2uD/W2uB+uMEG90dtg/vhT7fB/fCftcFVQPj73DjV/jmn4+A7/vMr//l+7hjl8etq"
    "FcI8GSMb9afSZTXIX/XKxvSvPFo1TCTAf+KivMjB1QJWkaElqXd7MkoGsfMI3dNKzEoRuIzh5dOeUcJMEQ56qc6baAzIRT/34yLs"
    "81F8kmfn0JNP6c8kxYGCD/7t9P1PyfUrNy3g16Pr7s71Zs+Fn8Awno/jocst3H3QLuIJbv++mI96O6xgQot6VY/FVf5hXfoYtbkI"
    "Tpaws0ave/qn7KnMaJgwN8qLIV8hzgp3h08lB0GORhQ/4e5Kep4CW5IH3DCsXvqk2E2BlucH6SFsyPRQrlROh/XPtrV5WW/wumpv"
    "Ll0YCX1RKEOGHY+mGMRGP+ouv9kWr75ZDfKS1RBkPnzE1G4kvoQ0LL5IkSR+gzA1nezjTSJ/K0mXP4VozB9CkuYPtlGj39Te3hlF"
    "yPaSyf4YeotGlED5pJnkSwd2TVBO3aerunLqi3TIadyvbo8Hpb+LBOYqnDPVuyUSuknLiZB0VbSiAx3tCwZGM2krnZ7yCUPODu7G"
    "I8NJDEkp0j1LqR4W5QJtYaQYJEgB+uwQzQ/ZuzgKvEJrYjuDoTbZucue3P7vo3wSMw9T1qPcsjJpVm5ZR6HOF9aTapNbVjcVKbed"
    "ZUW7ctsGKvqWWzYg9tcta4mNeLtaAGg4IwvboYZ0JWQVp/WfpkWN741d5SmkaReQsxBjF8S33QXmq5e+2AXCS6BreElCHpKChtS8"
    "rrmycZ9atJKE/kC5ItO4ywARXxXUtHJFooWAvAg6waP41NPzEpZwx2Xs4xjlDYXLmGYr76iMmUKPkKxlrSy7eWoEaTxbe5UWo/Zb"
    "I9UxIMdvfDTUHZfZmDgApu7m2lcmlIAMk+SAhR4/erizvbXZ63ZAmsgxdOYkdlyPRwQcDIYWgn9tXJcB7b3iECQ0doglj7zgQ3z6"
    "Yj52woO7V3H7lyxJnRAw5xDOU2DEeBp8BAZySnJgUA2d9ROMREF1PqrCb2RKTWmJGqrwnkioKSvOZFX0OX/XlGQioQru02dNOSYL"
    "qtx7+qwpR0d3UKeEwmqsZK0lJCWKQ07O4JxroCEcfpRXo1arBctNmk3nwUHr4F+HVwvHvb/Rb3v/+te/717/5V+TwwenXvivf929"
    "hxu/DkI1io4bEREkdfjvalGDz+gLuIKniIqxRNZuW7PlKPPoDLev0E5gmm/gYaGmauOJB5jZBgHg3HFLJQQyewbqEgyqqPolQLBn"
    "CSKv5RpK8XPG/OKdmwfaHkCdZ4WDTq6NuVtNWpOp2Uq/fzZdPRuLEoiZgGB1O4hXt7A5RhRxzEPhFqMWL/VkzfB3HUL150yn4Ujp"
    "3HR6LAVhV4Puwb8muEnDZVhh5xAmWEAu92QCv0zD6kDPZM81fhPuGt+78WgS33ZhvgpzsBCHkzEuE4xQBh0wdkP3oHNYBoTYOiYZ"
    "dUqNXV8jIA14lc+GOnjxceIavzW8+Ps/B6+vj8flaTaAv7s6+HVjNvi53apvWdQLCVUG/Ua9SyvUGj+5Llxfahm/hCGTU2OFurk5"
    "qOMnHal+/h382ir0E+DSCneLoHzsKWYKC/H4AU/jAqAbz5np2zBGvVEsEBHXisBONM8qXgyULjZMDIa2lBJZKdkcSWtCNAtAPqW6"
    "WNIgxR44N1pDzXhMdcd4E2W0jv4G0tgMtlYlU7CRXthuJMIG18eIwbTAxsNCKCU3lJvIZPI2eotaPkRdP1W3HuKSdgzCpMUQonKe"
    "tc/YIV0BiiXmC27OTYLi+nq70xFebFEQ/Ij6G8mdkjInAKTA1GxaOKZ01+ZuobetDrk5TUQtDO5NLsbxIf1w+GNSnMHRMUhsGmjc"
    "P5lY4cGIzc8kSLXJAcK1n0pS0SZSIRSEPt6U5aWieVPRLOh27t9XUYPQsYGEtBGOx4k3Cvd+5j7IFh5OqjR4ua1ZjCZ9obqpJTgU"
    "8fh+4cnTT+F4pRYJ3uxs8/oaL12FQ0f2qGrUKUPTyQHKgqyykEBaTpgPh1ajMOtiVTgfCTFeRci1YhXbO/aFAOk55MCyZemnMRsn"
    "vcmA+GDMhBoX3cKmC32L1s2IFH2Ooi0CWdijAkYIGaOEmRbCVSyQzEq/n8YVQVl3WsHZSvXXcXQRf2kL38eXX949VK7AjMLoDenE"
    "2R8DYQgxjpdMeYHG2VYKnAbjaMjprhDsykDELrGfP3KpWs1rVer69uAqNfBF66Xb+KIVs6r/8WvW4kX7BGJ5yZuNGK6lsrcVdSVa"
    "wVRiFE2YzRGLZ9UP0GBJODrZK6v4K0hSvhoISt50yoWoGV1oEo/4tSGlV0q/SIc1ZSG1boR43VBi29Yd6wATy6lcNWhuAa8dkBnc"
    "tYcf1M6x3w9DzxhWsS9H9gHdqzu1c66bm7xH/A2vntEvfH5JJghwWjnu7rqD18ApsoVo6rErj18Rh21XLN1bZhJw6ZxEIhBaveeI"
    "QIl3lUyE3oVuiUQtIwlqeclEifKyhEqA/AXQ9wFqXhGuaTumCzlhL5K2TxxyGiRWpG5LVFgJjnE1EauXnjJ/245GWJ12R5GPxE+M"
    "dQM/3TpUFaEDFEIHzajPMlGpuL3cuxId6rEzrcdFOKzTVgEncAn1IxIZdiezhABHGx7n8xnmcjXAiDzP8jybfRqHvskC1ZLO3WOA"
    "3OddXYsiEln1WqtVfB2fFKEP0M6fdhmjsqAOk6QuqHDdfrHR9YuN3m4tcKv4n3mZKxj/ZQ3DgF2Ex41D/oC2mvaYJwDy7qrjmXiT"
    "VcZz82g+RsehT7+YXPNvk4D7USMfZvByiYrf0EyjDWHUiRqKw1TxCjo5nhaxUw7NGdXycJE1oW+iwecJnVE+7b/y5D2UMUAqKJ4G"
    "iWCEBYHRMrSywweBRBZqlcqIZG/FBSvQiog24yCw8MWraNux9VcoGAH7DnRsGozaw1KON6xJRJYYhBNWTylh20aNgTggTsqdvqbZ"
    "QH+qIot+bFYB1cw0JDbUZYDSRiIMRIBwtXruhvzEyRGBWlMtihGX2pSpZqsn/VXh2up62JNvj6NrjEOPYvq0A2v9dMowGAf2wYH4"
    "5Ki4LpWbMBBJ3CcncE5ibNPdSndjo0PemUNAtG7fqZSE6kZZL6rIRZH7tNOPfBC6l81qYWwF4fXPi4TAAxsjLuIWHkMjvKKk8YiO"
    "OI+hl5CE7N3cUk5xWKyN9pxybthlCOdzA+Fd7+wGdD8NzqroflSTuAq6nwt0v7gdup+viO7Gcmz0liL7+TJkv1gZ2TcA2TfKyG6O"
    "wthyp4zspwyByy9A9otaZHc3Lq0OGbmOapC9hOpQ9hbIbs9qBWRHR2N/LMZ/m53HoV+D7D8qKEpm1T6hVK7ZGrBZSxuL5ssag9yF"
    "zaG+R/X6chZVCwfAsMnoQzbjXLhSUWOyy0hDidlbV/IeWlFUxu6w7hbKPw06MnY1fD0JHl9f59fXaYWZL8rMfGox7vmC1TDvYbvE"
    "txaFalgfBgCyrqNkfJxF+fA5yUmzJB1mMzvVJYIBP5yQ3LMSsViXcY3oXQtKu/ig/DTOcQgAlQcH//7XsHUo7BHh0IcZW+owUwHm"
    "7qbKMssCS2ro/oQkQm929mBHfK6KrDaGkFrfW6bgEK+KNJwbIqAAzgbKJFEkPMHogZOaqrFdV6uIGRSo1BP3DP2yEtkih+sdl14Y"
    "2XhRNX5Tdr7GHYFh6KZVoCekhTgI26EH/2c93RLTsol17PadZmpdGd6bbNgYHupcaET007/ag69W3T+B9QYpyxqJtCupGdiuVCJ/"
    "1duA+kFY61wHpKvyae3jA60lB7ifLvhm+w8CilVP4Z2sWYuI4vVPqa64y9k1vyq1knItdRVvg04m3wg7GqBOSA17U07J1VWmTkso"
    "+BJSlNrrhvJbkKe9e/f0a4/eoTLg75upfoler3ctakCvB4OiEd6KParf+6zet2iTA5sUn5C1uuqypp5bshQb0Q2lUMmRLVGtiM3i"
    "TbTZlMGnZq43CCZVPnUUEIk0lgrEN1NqlNKbvmTWqScInNQ8d6WcMqLpe+dB7V27lETPgnNk+RIofL7r4J/O9TX+GW50r6/JkPwk"
    "yDxnfH0dwdp2OME4d/CQczI4koHNdWt5pBPIDLlw6AomSwzawAl3IMcx6Nc0kpmN+M7gaXLv3uAJnMEDmqY4CivGhc3DTUqKgfrR"
    "agOC06Bia4h3vtnoIh6qi+t27e0+SCI4r6gv2/VDYhRb4hOXkGf/dEA8SrJRSAWCMwBG9klwKkWS4dMg6Q9bXX+KP6Z+Jt9kwSop"
    "PjhxN4oN+akb8y5clXrROPkjYB1ojW4PtyPiOnSF0q2ql9Ps+MK2TS+LjDtGiZKQ2ZObNhajxapfeqokICrECjSpu1FRK4HYIAvk"
    "rl+TDTyIvDTOWymZy4mXmjWF6T1Kp1+YbeZmHXswvv1p1EKHBEoGqVxQy0vsVmG2DbJXQd0ryPF4ajqHkZofG7oGLmGC5mKTLK8P"
    "WngTIS2WEEkUISRC5sR4eclSGlVjf6H5Ey9uBQkdn0C8pcbAMBuxRftIPaaJNxL1KiYL4lZ3NwPpY5cQ1GgpUzdDpWau8iCDJkg0"
    "W2St1gK1skIF6K4omecgmedS+qYLDxjJbvYk/dJhbGwstBpy1UEY70AB7B19o2RLDUuXn28NylcbKPjlQ0eLbxKpUJawplJvVavo"
    "QVeqHKQliBYOajlxmWxoZ3RiRcKQjLtlwSMZdp1YuW1Ug6nwIrV0qEk5tISzkdbL1RjKTEyXcDbi6mW3UO8ZohpJEjie9QjjgSoO"
    "inxG9Dt+5FUMIyKKY1E0GD/guQDLaiVXiJbelTQCDsM8dDBPmNx4ya4Z0Vk8JCvFZY49+RiWSW8RD0UI9oXrOXngJDUxn2lEKqJr"
    "zg8Vk8amSYdgj9Ovs90n82nxQmRdib1KooSkmmeU/fJSxECM3YVnXZfUbgqWhUkopsfWZNIkpWz1VOWJTOnLH+rxhSrzVKb05Q8/"
    "lghXt3oK4XaL6+sgDCXRbca+rHqDEyNzHEnCDuiQIY0A7MzkFXM6EGWBYYYusTyynVdL7omyVe9TOl5HXqdUKJLikla9TRt4A2Zm"
    "CSqjlc7F6c0Cxu6yidLgh0FmAJBev1rspHVZY+CYE/GpKs/8EQB3HAB7LFAJeIcTU4MkeTOowo9PnIoNvNuHE/icrDCFYemYbEh3"
    "z5m4Zgzus6BYtbFTs7EzbuxUNCZGfq5JpIs3Xcb3xqn+vSpSTL2pFkpQNzdxU9bQETTFu+MaffGqCvgpHPNTVMCbDd22DZDkpnhj"
    "5ZiNsLpZjJDt1VY+93HaSu3fNEVGpSPYsYIRwTF4F8a3610Gk9bQOw4qR+6Fu3t8794l6finG0HXXz+WnIDFxhyhkAYFWt37l6ju"
    "X3pQ3nI9I6aX9+6ZS9pATJbQi/kSerGx8v373JuLkcFsh63JrWZ0+4tvoLVOcsMjxyRIrEeOyRc89c2qT309k45XLT9jU739pXJd"
    "6Wq9n5IioI+BsSxhQRdh3STRIbuzg87hRrG8lhCNNkqZvtFrc8tKsFLuQLzyrWLF0N7QXta0S/KNKTBLcKGlbqPJ95focrkPOXLF"
    "ktK1Qd3DXSOgXIEx5KQ4wR7GKpcQ4kE7WjCtWzcxkivV4kTzwWjLGWW3ZnjpZJkrSVtNwWMKJwXGWL8ZTWseznvprj3krlL2cvNL"
    "jI+NY1iYrUnTYzEI8pDQxIyKKsjcFoGT1jC3OGLF2xbM26ZIAfImW5oE85bSj6TJ+Hmlhaquwpspyn3ahrQiUJHF/L17qgQazesM"
    "fqUu/Fs2XZ0IXwhPA8nT0tv41So9CSSzbAU+nAqz5NfJpIjT2A6CqGVi6c7qHI1xh5bhX2HItDXG4Q77KYCv6XilSp/GusrINvtd"
    "UosMhKni5/hylQEKA0ZZ5ebBkQ0xFgf4DZVp8NeCW42t9iqQq9hZrwi7OvPqVaBXsYm+GX4lK2wBwZJoWwHeuom7tTK8WcA6T22J"
    "jA6jl6K3vGmTmIrvpZE5v53jf39scE7+afqZFZmmd9xKGVdGNCXv0hP/Svs7fjv3niHH+2nsfxQ/yXh3b+4hJZr4P15C3X9gOFAZ"
    "5dO7a33F+/ilY4OqjKIpI23KyBsytHfHZN+OK8pazGeOERYWBWdIoNFr514i8uhkHKUUeLQabHSBxrM6mKvrXZVjhcIxdPAbCOew"
    "5ie+1NAkGIBU2DfI+KR3Ec/eYpBS/LGXpUWejfyrNJMHJHkhhbTYJ+lF+jzmQc2cAx6X4Zca9b1t7frz0BX+L04xeq328elKH5u8"
    "daK2vZdEfFTaF0DtMUAq/LFSozmlRnMzFU7FO0YUVuqP/MvElSt7suuuGEgBn4xyTzIItV/f2gCuypVqrI5Vy3dqbEaEF0McKcel"
    "OEjblalZxMrVPkqxJ/7pUSSImPec3MY6hqwnNikkiV8qeCwGhlWvMzwiZ0QqVcBYQRI5i572WnlkjYRWK/p1AAc/UYXKDzHswujW"
    "vq4o3dsKcyDMp19kHYMqbl0DPyGZWVWVTJ8e81g6Fb+8MUIBdksZSacp4SWCTf6shNxdsOnYIy9MhuTsrE14L+UrA4HbFrq2LTRt"
    "W+jZVjipcEkhkIky7RLGGN8KDWj922LR5VKryL9qcdt6LdvVlWuX10dCvy2g3xbgFjwsAFNBrC3onnlHCNtfuSJGvt4k7+umv/v+"
    "W6AIdyejrJh4IXGU7J3+ShIXpi1KtMW26WMPjlBUgdBKa/MpOI/Lhx0QwQnSUCKDuiFBvg4qHRxaGGc2LXDIGowMnnwQUntwDIja"
    "4aF7uPBEHOeO6//ghCFeVwjQqOMvboxL0HfKxwCwJ37XijxtePFXZ0Iptf5kMOGufK8rb/YjxQxG7QpjXQfjD7JT47gSoC15jhdn"
    "Q9U7PEBrlDg1/RHUrurobxEds1u4VleQzrNkOIzhqEAv4HHoccBuMTIFnuqIVgeRQM86GNByvXZ+cYz5IZr0eQH9ULAu0J9xpFtF"
    "q0NkPFMDHLQmrHK645fGtKji4qELKAj4DEnxPv70zCkpN/q1q14jGNxy3UsRAGjd66ICyHWv6fGrr3x1TDeuvKqy2spbwQnslac3"
    "UNbaW4Wrg1yy9vaolq99sa9+3p27BiX6yjRgKWFbryNsBuogaet4/5dw/O9GONJ9A2P+EBLytdHm/9Kd/03oTl5CHUr8x9xd/DwH"
    "7hWgmAfJPl9P70sRvcALCi+kuFYYk4Mi0sGPiySefZPN4ZdmgUEEz6gi/JjgD8y+rNY+9Aay2Ej+mMofQ/wxwJqDS/g82Q8+O1dH"
    "R+xP99002R9H+edQRt654JsS9OaG64x/0fE//OVIe/BDBNGDXxw290oEEBGBQqAGKaHh18KbwDKOUXE9igu8Q/DS4JPjuMHTgiN7"
    "9fuPd/DNhkzktvv93iN0GiJTeVDSB30MSdqQgdVBoXyu0U4mL/F2DPVJLpqViDa4QiEU5Lpe/6DdbifybbzIPvRFiutlahBoxNB3"
    "oAg0hUzscZRPwn7HZ/8jSepAQ5FUqaPSgyvSzOOAgjj1+8pZiVFYqkTipxmn9GNf/NroLtBWF2Ys1OetXsuJWyLXfeBMRLJMuS+1"
    "+q0tfJtZAiC6fUT3IG4dBPsHqpywqO728wdOKbHVhT5SORh3o+uLjwc9bwAwPySvwa6xVtIYha7IeUDSSlmMp4Akp+iHr2E/vwnd"
    "jfigc9guspfJPB46+ORwLYS0rpnmKjeUrjcstapGH969mooLi9d3r0T2gV2s1T20e1us3b3Kq7U6S4r9HOIDMO/EXnEJF7XkXa8E"
    "S0RxldvzEJ5KO2otGZolaRw2luxq7qf34w1AicSFBbjUyDigt1BinTZdb+Yn3plvjEUjVFMdd8FrqVzXwTgiXCoptF2cKjE2zKZJ"
    "a8KU5I6ic6jhwb/9fhgNMKxuKKiIgI0kJaJPT9BAP+ysdQC+opQJ6lBo6ZJz6LukS6IfHl2KUeCB8CQaTWI4og4Sa8n7cWkPw4Tw"
    "OHzlvPdYAF14b5wTMSYBfDFpUQKOlINCndYYnzv0xEk994v2HFaiaF+KyQKpkxMFAuflML9ue1trF6/uKOC18F75jjCULe27hSsU"
    "Nd0OHAbmwePtbCHF6QLRdH17oD0Y6FBQFTnccYRnh8VY6OVrRXkchd7QF7WUcmhgdulJ8lGlpzW9dKu9cDXsJ3yDSw2kQzTlmpvs"
    "W40EoRrJyBrJB9VVpROMMIldTEtTme4DbbRRQo56kOSDUSzG3auOe5hh9MG5v4yYeIPLJfndQy/3wx4ggBrPsLqa/mqLRdYOBMSu"
    "3iQPegbcAG90Rxl0dAh/o328gXC98X5gQS0uiiQ9nUCF8/qc1mme4FXIGfIUFp9yiilneXwiGRi+uy/krQGwuEVs6o68I+iiOi3Z"
    "0Qnq/BfeRYVbkWOUDIvg3IhlSaMLEQurnvV44eDNO5eHheq3kyG6jkEG5AV6Kdv9PmcKjjbUbXGfJVD9Fb4bFZXfHU/i/CLOMfqC"
    "e5VI53+VfDz+ZPfmiQhMii6enrrtSZYX8iTEYPHsbxEgBRD8gHFYimzcKhoy0LaD4vSk8opdWhkkQ6AZFAr1DQUd9sPW9s54vtaB"
    "/2/tdP6KP4DFJftzOrTWiEeSIJKgE6Bo/zqN80s2CcKgIX+5e7W3vy/cOaJkB72FFDEoaWcMAb5BdL1/MlyTPsoZwFenZPzg6nuk"
    "iP3Y8PjjXavf/g0dc6/99mQAZ8MIAJv9AOeIc0U2QBThMQc0PI7Pooskg703OQeAnCFrD5X4SemVeGm7T02Q/14ViMVLjDNvmFwA"
    "5u17qBai3+f8GzCvRIEkIlNO6aSSeArE2Th7aJO+cWIFfy/WHUeCCCCYvTPS9P4FuCL8qusVSN9n2a3YiXfkqUuHC2A+y3Mi0og4"
    "tWmb4hDph9ITv5g4RfA04kUGSUiAC2QhmEJMkaP7QlT7pyRWmOhzHl/kdLcVIToISbo6LBFyVgNTmY+OONBd9r9D4yn10ZV9UCae"
    "5zGGswn7z5380vWfO68uXdH1Zj2RGUWn4bJBIbE83VeHK36e7dNQafFR436EIwmPsyHIZbgseW1PlL9A+bcw5F+6WUF9/Ha3B9go"
    "ctpI++JcnUn8GQLBtOuLdNcaMH7hjrtEelwRMmmNp+nnFAXmQ+9YkeAij9IJXk76YZ4hNJ3W485abwv+c2Hcc2wNY0tOijz7HKsf"
    "LdmD+BxGkzOK/mMnZScnAAnocJ/bOfT29oOd9rY3qwqjWTZStJ3jlF/hXTn8IBJ/Iu4x8Tct7XIpU4p9stoygVGXcrVIKvaMFtw6"
    "nuKXkaHXVfyOFlkF5Xra0fW6HZgvfU1+BWK/t39/b39DlLvvbG11W5QEuObDv0pwVeIjgwCfhvMvLebIFP9A/ELr6kOAgSP43g1o"
    "EKSDPOixs8z3r+6nSuiUEgZx9lfjKEkLerE79FPBv4pWYHweLqYPYlX+QLI0xJwDW85L7LccneXejxauJT1ky6UHWnruky99+/2t"
    "jmSdjRRLTNh6BP+F9aqqiiwgqJzYAXf8dbG819cygOtBBqfp9XXwweAFy4NEuoH2zsgIhr2tEBk++ouM3aYkKGigrPFAThsmfbxf"
    "R/YjKW8IebiOIS1qesTbfTZeESE9PN54eB+MiwnIIA6APcQNAIG5dZHU0w+VrLYwWRjAh5XDy4xZ/KsixCB4xqMIjRnWxQhMwWVu"
    "EFOT+FcBZU28JEFgJ/GwfgWSErO/X5YWmpf1bHpc1+LePtDTDBj3m9DiOMsbkKK9ZWAFniKXggP/qPSCSEYuYkmjMQobauteqHxN"
    "tZ8busQMee93tZw0HBKC6154n0vsPOadw9pA1rOaLOLxf8FuiqSAuR56b+q6QD+Aa/iDAhJzT29FwW5lLBFFwIEi72vbQhtHyHxZ"
    "Vx9INmS9WlbvtcjsVfqN53C4QYkPosRmdWTMbkGZ3yrn0QgFPnEcKXUnwp3ljfOY9Z5wECfRSB1V9pmVxwhrCkvNL1pF0Sn8xL+0"
    "2FJw8cRCq29GDDt0L8aimpWSlhyD6wXZdaBtXluO1dC6ykNSjdM8JVWuGLiVJxPNg650QKpGH6jSsCHZyUvyBYccuXCUh1c/RBk/"
    "ykEujYYoEzmPO8P41EOFoak6Q9fzeFKl97udjj67/gpJTrrRdUvJ6m0QNORuhG7oGyfrAg9n4MwNF9MxKi1ekwsX8WhpCCcPXiK0"
    "5Y8XI7pUaOPJIU+bhpMxQsuRCoUhRLxjkAoyn6Jfsj2RTeikuH3jaAPidRZHQ+QlK1t+Ep2PRzUHZGK3os3cREb/Cm1UTgkOivYK"
    "mcLlPpmrr/R4HAEFX5PbW2kNsxFrDTOQjgwh4DGQPYNFNsQBZT7yrsQfM/Gz2WM4eoCmag7+8z6aEM72PcFrSnaPXjPGvOhyJ4vP"
    "ieZBrdJSWu23d5gz3e4ZosWAD1/+i0Y0shGQN9RonrEwOa6BFu7f0CNyTALkOXQkF/ajlPz7cdugJVyMHLaqPf8YyDrG3+XiEixa"
    "2xQCpbehiESeLudwox5843x0zPa6LHHgP3pxmNL3bU0kImClX7MjcT54Vwq8UukrbYyUqZHQkTVOg4D5dh9FU4Om0dtCY6bv9wnB"
    "THrb74f/63/8zxDnZQHlJS8MMkLpqZJQUR5W7bskqH7j4GUFN5sU0NxpKARYRT5pGJUhMwq/2vfCtQfUAgnbkl5u1LaKkPd+c87n"
    "VZjxrR3snmwGNDKbUby3nH04KZxUKOiFdCtJS6mXUcinfQuqr/ebhFhLPaxQgY/Wiiz7odSMPILdsvT9UTBK3yimR2oS6UNYAwKH"
    "8kMt4wFlpxPW2tZJCAvv2xL7wxVYq7nwPlX4AcrXykcci3UTKm1Sa8TSq1mUp/6rS4+0FH5+iUITnl/+6SXQVQxI+Y8LbxyTig9+"
    "ykjt5HTEEJyq5FQMqlaFc8eE0x1tKwtYRBQYtRLFgSh9WK/F0flSnVKnNLEH+AMsnNbpfEvrnVbQpkRYlMYHURGX/xux/D/W8MF/"
    "rywOxSFdpj24WWPw/zNWRHMQN6CIAM0N8q8+3q/utFq6YoWbEGK6I6Xybg8GN56HUlqvZMAa1m9Algx7sMK80t9XrhZ+reP7kUE4"
    "BmhPpufnUX65ZskjzFBwI8QpheNslJB88l0dmZCNwdaDIv8s49VHzta7nvs0972BUWpF0rLe+KrapbzPpEfG9TeaTVpDVIryQEp8"
    "0K98rolMPsuqlBnmalP270okGYFRIcffi1X6CVbp4MG/379+9iCB0yOOcKEw4cXHv1//+/3ex79j+iA7jkYF5zz7Zh+TMn4qzkn7"
    "VPsiARCIUh/ff7qGf15g+nl0CtsoEg0/u/7323++fvcWW8fcyWeQj42XKD/vG94pftpvnyQY++WgOCQDCPawQpc9br8Nsjz8TOMp"
    "SIZA5tFA5x/7gdC8EAVAp3tHRxeDwbsxupON5RXJQezlhygOuelBfBjkKqL4wrsLmAWy3F5wZemnSIca1iloGvQySEYG0fgOamKB"
    "qV5VtbXQoCj2LL8gpsIt3vPQ4KVgJdeBpc7Ae+ku6y26m6S32Gl3K/qicMtSZng3NEE33Tx5e7oSCAQSuz1x50nXmpvtnbWH7c29"
    "7g79eLjW67Q31/CjB02vbWLz5RH22j1T3XLo0gqne8E/9p27gOUHIRtnAT+9B7levkc3ePv4cHYPX9Pqa6k9jvK2LhysZvkgcouz"
    "PJutvcBD3AnfQco+vqrO147zBCWa82QyoQj1EjeMujpoekYt711fO9hlx8Oe2ln6Jp5MInxEBHio7x7RSieT4erzPXxF9CLCl+pQ"
    "CkNUUIRRCgcBlMhFpSu55N9DMdWB8tEQZVQ6aOGL3SugfZQ3oCLU9zibFKp31xvV5+Sn6oVRER2H/StAJrbb8EN9fexDA9M9uaFi"
    "2ITrgQXX4Z4+e4XEHLNPkPLL8H//5QG9/j6nYBcP/n3QaT2OWieHVzuLB4k2l+njbRhitR/yfj6h8cu22+dAMpMjOjiPztAJovBA"
    "wg86POpg7Az3lOGS0KoYV5TjvZLHsxoTqgJtjupDwaXeVUPEPR0JzlIpuIu105AtdqJj9Pb6NOjGm8s7qA3112sI9dfTHccPoGno"
    "8DP0CB1Y46BhhH0G6zmBVUkmRzM67pWvTTRurWSRwFNO9+lCPEKdSL/NSRrUZwZ6nONvjz3DClFLNLFrr0NhaabIfThnGJc+9Vqq"
    "jvjgGacPCuTBXKGl0lv2dE++dUQYhK+zAni2eBHySJPg4HCXvMnD8XmU5vfuTfeACQj5C/2hJO3xdHLm5KoIvSIaZOcIBFlcfBrl"
    "FQ6LLMttwgb6TVhT+wYbJH2nJh38bRIQ7oiSj07w3T6IXa40ASjQBOAdFUU324B33IBLdNCI4la4LjD+sOGnfF2P3geoJOx2ipuT"
    "B9/tv3vLDgfkJGDKkk5p/3D4K9SaRvjUYxUwIKbZ56sm5bwiEZzx2v/7/wAE9Dod0ToFz0FeaQObC1BRR/oNsOmLlPYwT+Ih8/fs"
    "lIb0lUa4PpphWjPDVM+QofLg386/hldbC7eFf3v67wPoKx4Y9cg/d271woiF+x1nw37SzNB2NMdPH/ecBH28voQq/wQRBE1ZKK42"
    "rM+Z/KAGXLelqmzkZIt00DtsdT342ARe78Gjna14246ix7sl4jPlQlF1tMjOL4+G0eWk3++47K6/lKh39KWxo5/h7VI7mdBfVKGc"
    "JMOjIjqduH3jA5WA8EcOxa5UuP2CKLZtCyydmsU+Oo6J29NkiOqvZOheX1tmqZK6+weHNK3jPWBnw2PYVZ/hMPhLl/6HjCcw5nSZ"
    "/ZdHEf4fJc3OElJA/OVkC/+P0nJ6H/2XeHvr0daQUgSji8W2H233uOpljM/iOXH4uBOJLuIYdTB/2dqJHm4/orTj0ZTqbsY7m0Nu"
    "cDzNSUMLY4m34sEOJ5KdB3T8eHP4qMdVcxSPsdhwO9o8pjQ6/kj7mCYDLaGK8XprYjjwg8cAP7hn+MFlXIvZnu8J7zAn+EOJxgJ3"
    "RXfCigfP+rY6eRnLC1mSC6XBQdfb9LYP5ZrSloIjzpEua2Iv3uiBKLPjPuhtb+PdhWlJnWpLWrbDTnGjOPkGWcVmQd5KvEmQkT/S"
    "jp89cLotda727kcY9wiHFT1pd3vX1/Cnd+/e5El7c1sOkzGDyjxtP6ZMlcfogHmQ2lXJhDg0u0GAXldTNDhzUthzrRT2nPsg++uO"
    "zxldyuhhRgczNnq+gz9bmIXfW3IXDAJncH+ns7G503H/Cv94A2AKttEB8Rb8CwPf6vUFAviDJ93t62sosLm13YdhP+wztviErJC9"
    "1elLLIWvh/Al0BOr4icjJnwByPuMkvjxGLIEMvrcpKa9+0L04FUlNg/WCv4WvPDp9XUtietoG7Sguxs/ebgbb6D3XUYhhQ5pBR1a"
    "Ki+v5O0mG0FxX4Wt1cYXiXFa7Fkj1lzJ9TXe3AWA4IRdNFbLTi43zOT9g1Sj+KFsTAADoyRoN1fSN076BGPDQYL2xpQQLZppxllu"
    "B+cKyKE39MVYF65lX98eSgv7kh3hsFW0h9rNXrfnygbj9sQgzh/5wFzvApvVBfJPEo/0IS4WC7h3Ps9EVIy4zKlTdAJ8GS1xtWxe"
    "k1O8ln7+NOj4+VP0350/CVK9EC/2lFsu4Pr/Ndy4q6NQiCYVKwQUHQApiUPX3a1bPTEQWBrU5HipurbA+w8QALO8zzkxhV/AQXiS"
    "NdOM2WH5zJBcR8iXfrM434vg/HdN1kjP6rmSGiSTZA1RxKIrRPw5uuXxhQYpF/c3YbknPsw4Douck1FLJt1Qk0Fg1DNhckNdxYrL"
    "6koYqnDpBvNdzfR1k+h0p9oaptY1ZKQbbZwk+aQ4slpCeMvEPvE+zK6Z6a7RBBrgl1tQaXYDKtmsD5uhUEu4lrbPognjaz9FLox/"
    "c3mhyfPNKNAacd7tac8qxAG+icaMRFFASJWiB6wMfxf0W+67SLmBzaRDzY4vE/tdX6W2un70JOvjGRRGk0GICZD01Ezq+pDY0aP6"
    "bPBxYlCKKqZIFUUuPn/R8l0y5OAA6F4vucAorqhBYJHx+lqKaRXsWFcrXhY1CoYl4OTVAG8N0YIxK6IRDHWXAoACfERO3qa/GHuK"
    "SuRt+rtR7U7Z/K4VRIifkaxr2m9XSAu/3AzxYU9p83iF+dPckt4JnoZSq4+h3fF4NDikQ5F3Xd6BhorvF2MdOkC2Ox6GiQVMQS2L"
    "WI/IWg+QoyN3t+7hHAZ6j7G+ftcRLdnGaGi+EVRLYOcdCcKrcZzjgx8f5OCExPEvEL0Nw5mkn3KS9Evn533e+caWebNnuHdWPOaa"
    "cYx+TtIhuvghS0My3J34woqaEv0YzlaBY2X0LixwPiOWJhe4hjrVXOBkv39w6BWHEhKcBaAAkXLiuMziOgexR5ppcSqQTvbQOr43"
    "1tfRPVcL/8T6VJVcx5Nev2E2OT5UUxPCr4UvizK2kh25B2fy+cTPPaRgsCvEKZcqR4sL4xR7WzrFyrBJLNgkNhMVBeT0Q51U/djY"
    "D/pUpngB8lSCMvaOkke2n6jDGhPVwQ1MPsE/AvjTBU8k7mYiMVGQ9MRyRR5qLTOZjr/b9NtLDhf2svETLFw1uTT0EA8HKntGl65c"
    "XQBunczrjYS+nd+yc+U1T4mZ4IBQ6LImymMnrSvjGgv03lb5y22uKSiQ2ScYUQU9EqKDZXQyeL8N0kI2xTAgyPYT0XvJCj6cIeb0"
    "w0GesCMbP+Zpz8KSRYGmSq8MqkSSoX7OqHhlcS1b0EMpvkctFvKytiQrwqDpooJ2vnHpauz518YxKY9H0tTmxpFYo6klN7yCSIXs"
    "Hp19T6Om6a+hH/mFckeNJiG+yCAgfRBaUPmMcJxPJxE9uUB1g0zNBkU2Boa1CL3f9oIrMhrsehHg3JYHbEvXQ39v3YX3jczsUGYX"
    "M3uUubnwftgLDsIPn96+ffX273BavP/w4v2zDy/g1/7rV3si7dmn/Rcg5n8L7YiSAM8R0AJ584JGl1yxlDEG7h0yRVv1mdS8yEIL"
    "BplNvxfey1dvX+1/K/KzzzIXfkHes1evXzwXecfRUGbiz4Vxmn2qMMlo5zKxhBykYMTz4w+UyEC0QD8F704wbEpXY5ooGJJxLOw9"
    "NHkDic/XOQDlkPTobfiFd/HJIjSyzwDtc+sVMTRSyHL4G/6B5dFI+KOFhPh4DMRcdf4kWDjO4dDaPwMqwkpiHNVEl6BB4vU/+9M1"
    "hmKUKXYZv5eAh+aGbCGXOSKygVp5rqEDWfTNAojc5vf1dSJBE1lQXoS7ajh4TexkHg5aQ+LvNxwUfIheXx8cysNC0FS87UIPw7Bo"
    "0gU0U2sl81Ge6+E+pDNhgXpfWBvUCO86Bc+QWlb3Yzlef4GgGl2WMpyE3jtgQM0fkX/OvchD8dd1yQAK1gtG49APL7WXDyZrvZaj"
    "hoVlVqmXAm+e5ZMeq2OaexbohUZvbf1STzZKojddG7XVrvFTXgyV4EWESffureckgAgYJhjO0YJqQvCMTXhmCE+D39Br+32J99+P"
    "C/2KRE6QkFGgp5lkg0Feb9LNpFxhfCuC4CcS+yuRWNKvs1Y3Obl01OsIoq/RKbqtf9p91PELQ5vxHQzTUP57hdCYR8A+oD5DnJHh"
    "GBk/FWVgc8fdoHInowzWF/jQ3uMd18rXkPinVlWs/7Z3UBwi2Td32NPgEayXXFi9/ybZeWzvV3LTpzhVqQ3FW1Wu4jHrVngEQJ/V"
    "39Qn6YBGDj/Rt3nHb/YOuIfDFvxkvDmUS8pXttQ4hi1EYP+0F2zGW97Pe8GjeNP7Kfi+QGdygxhlNQyRR1sPWSjBfjMrPsmmcHwK"
    "BvQcLU9GWTSke3E8RMjKbQ+9UoacEw+foaA2zjMYOPsYQSv2/BStFI8mRTb4fCRkYm9GYSnDY3yoiY4pxz4OG4oKd++y4GThDdAv"
    "IwwS+IPpeYrn5+DkFMdKZ2+cTz7EF9AtuuB5zykfo2N/veOhadA7CgE4IgN7NqODo+vkJFSVsSE82Sdk5IMFv0dGOwS2GfDPv4pT"
    "9qADrZAHThCbP4vaxHNyubcZ8FAECJj9KbmbFPORl+ZtmbFAU8Cimk+pC4/0Cwz/cYzju5p2B8KhKYYJkmwpDfw8y1LoWpRP4Rcl"
    "w77wzQ0C4PjHHvyga3zoE/8ujB2FmWRnwBSbWNP9IsthYshzvwJu1mEsiIHaRsccalZwRgTGUARPpUmoIy1Wd4G8IxnNDG3yXaI4"
    "P2GbQUxXblbfk7q+PW0KYY3g3r0ZTJbQPZ6h1/6ZPpxkf+nMECBT1yL0P7UJfvahG19SoHA3n7FiR4iOGxvxTJJGWY/uMa8SELU8"
    "2tHQEbJ4BUljqRcVxpKgf3WG13QwAJyQ4EvSk4wia8yIiOeeMC2BD+mmnGw8Zk7uwm7G62Bmc8mkNLyx4pUcrKZTCVIpUt1yqwCi"
    "UJpget87IW8aqPYsnczoZYEwRMYISHgZ6v2E4zCOEYSVPEY0UNMhhVPgM5M6BemhoDjMalBjDqiN9tS2a/aZEL0Bl2favIXWOpnh"
    "OWLNi7rgpaMzSJJiCSbzWbpCCJg3yE1yPXzx0thD1/bUTzYTBqTOFTLxABmBeG3myIBpNNLOyH5vbqXJs59zDDagpgxloGdlOBR8"
    "QfSNYpj8DojYFb0wAgaLVgN5TB8tFz6S2cICnRTJUQPf9lMbqVtbEj7vpzbQUQ+QRLg08gay8GcszJsVkkezkt8b3lVeg4LwpzaR"
    "sH47z2YT1JWobZavkRYwAb44FmgaE/uSu33iUnCR0fs+uYah85D4cfoFO2a9EKVRMUDa3SeFqIN7RjQpstRpyOdqDCcb+jMu0Lhx"
    "qtayOlhj/x+g+5h4hNfD5+iwBN8807qYMZrbvEFUUEnXG8rWf2rT2dAWRwgiOifw6WFsQvW+XaIo8hsqUW5HWIsT3TaR2naW6mZF"
    "P6431qXkKd//qa3Oa2wzzY6mOfCYgFTo8A62z6d81ObpuT6gijzpgceUuCDVHbIO+vt9GSXoQFdWDENf04xZlODRhj7pcOzns0DQ"
    "jneffWmPJ4478TWMC2hPffJBaX29mI9xy8g0PAD3shRW/FylxcOkwJc+/LnwzmbKpOF8dhAfEk9asLUcJwiKUpgOK05nfDRJAKIN"
    "H2ALHsmBeSTjI1hM7LdVIrqjyz73HQOKAXAG5grQp+SZTGZWwjoQ8hBJHJDKfFmg7k3Et3llYrJuqhzzcNp0Auj8TzJR5qJRkWTa"
    "KF9+BDrd8AikmbnTHGifpTjGSc2CShmjNuuSj2RUH3tgxBUG5ULk/pB/GqY9ugVlTAQtYGrQwEp6xHWL1IUxJmQdj5DNRI9RfAvI"
    "rVGakU822bgsR4IZ5VL8OyjlYbScfs+Hw6xsECNJsMvVT04DI00PSyYd5fFFCcoG6xvYBcvTEnlHyGKVZmdzzEG1AqIjM9G4pPDj"
    "KPsMs4KdEDPJuXfvAhkj+g3ytUAkYnMlItFHoNOlrw8uQL8CkaK7Y17O9a0tFPP+ub4GCoN3t1kqn3ZRfuhaO0yUhsUY4iUN0qqj"
    "EyJWoeeUtpGpRdVpgdx1vExiX5q7kb3eEXtwNCOhCuD7Ga8zUH4ABgx/AtNukJWLGUuWgmYH8AGtH83aoub1NfwWVV0rB2mGzsPL"
    "oMGewy+EYXYnAFt0eWMIsZczGeGJGH7yQyoteClSEVSlRFx1LBG64raa88SVtWDafSKIHP/VugkVR2jV6gtOVBf7wR/y6LjCD5/T"
    "PAy2g1Zg8Ic90cERwY1ZqgX0I1Tu9oj4Q935yrUJ6ljPENsCgcF9ZCLhmy7xTMTuIGrRBpISzr17HwFBzYZ56/MBFvrnyKbiT0tX"
    "RE5OMdUeEzV5FNPJRlWNk65Uv6airlHuizdVzSgHHGU09OswyCzOxzWQlQm+SPEJl6SfFX1DAuzv1U/qpga3c/YZF16l4Bkm2DGM"
    "Xmw1wqc1bTydOIAhFHEpcRJdxCgcwXS5UgU2Xk3DQhZlpSxKZC7w/AyHlnwdiYd49tkT+RyrcEXZ0G7JEBQZCDBWyfKUsdK7CfjI"
    "2xzx5R9DfsCMjntlKVtLYzOEH2pBXH/SyMhh2C6MyWCbGhBs8VNbKheCKw65MvSyz74AFYm2DC96p+YhUI3ubJCSsYmFhngp49NC"
    "4CukG0rjmRCyM4Sl56KdQwTcOCdvODdvd0i7wvbxV7zPwvG5GP844PPr+/iSWSH+HRTiXBOHqNt0egrIG5dfx0BkrurwhMR0KSx4"
    "miGnfJJxPVXaXfwjFdKA5Dg9doI3c3She/ewSSn/lpsEYmG16HpWm3QAe0LpW9OsEKargsMzfCHKz2Ux6JzZg2GMilConfDkMh2I"
    "2RIimZsK8zB8O5x5k9C8695vbk4qCOqao7eDfNjvgUQBczcz5csYY9jIwlxpjqbMb2GKOFO0CusnOqr5Nj1BNk33QbtADOBjZQB0"
    "EnjjOE+yof+CVEx6JPhN+j2hslqu4ONG0G4l3OyEQtcmNHiYYNi+Ybv40GmXNQOTPedy5u6aCBuhWzS5Ww60VorcI15EI8eeh4Hh"
    "wMCLryMUIG6sWqDXSajXjbdqS89m3na82diQtVIVuR0Wat1aqOq6eJsNHSvF28wQ9Li4PBWpSIyqWkWOOUSLaMNlNf67Wfnp7GeQ"
    "qfmBaTTCgLPy0euEnokjQLxnM+sBPLl7WHi/qIrqcXnNc9qa5t7MzMez/Fz+GbmULb+G520t975g1eUVsyA0vqY4qPv0WQOq3sjr"
    "J5zq/XbtUSzvWqgr5BpkiqE6yW9oYF01gCeJTNENyKWKLX+RwpWjfvs7iUqvfJ8737tKJZLHp8QnLLSDyc+zOm9h0oGy9BD52nnu"
    "fAuSsPYRSQ4gCnkPpDyH2LDoW71T2nvYVck8dO2BiXnKzIVU8078dwS1g99gAN9B/5P4AuhDgbZIMTAkwyi/DJkdAKaZnt+Hk/No"
    "NAqFeQ73IuQ1kL3x9SReYAvHk8B1PHfymSvci2qvA4zhViwiFWxNjol9ChDThg40vK7hkODZzPsIQ3536pKAgTxnQY/g2PuAd4Su"
    "k7udzR70JVz2C19YhgMz5bjll9pFyr90kXDIxlwb+8cX2e9m/CL7LexY3nTHowgfhUwuTv2r+fkI1ig8K4qx/+DBbDZrzzZBPD19"
    "0Ot0Og/oSTC/5O8pR3u9koO9Hv5nPWCGoYHUPPHpIS25vuY2wq56/48/6179Ytq7cTQgDOkIq7Xhr8Xlo4twcXi48N4T/eCJfMMT"
    "SdIzRCmMDzvBezZJXOQ8Dbpy9YrcVSyCV6fO25mxJ9VbfFyDwvXmsfMDeli5G2GrOsoVw/KlguXgLEaLOaSKwGHis6QDmRYOeVkw"
    "jiPqBxEZMTkaj/MMaD5M5k9ZAvO19MP21s7jh2ub7cfwZ3MPvh/u9Hbge+fhzqOtte6jdm/z4ab5vb3Z6enyj9qPepvdta12D6r1"
    "1vT3Q6j2SJXfbnfgz6PXD+kTyu1gwubeQ2qevjd78HcHu9/eMb5heDsPZfnXXfnd5frddvfhzkPop4Mdwvj0Nw5oTZZ/LMcr2n8s"
    "5tMT/etvHp8o/3qn/Rj+B+1utbc2H2+/LsHr53qcJRx9fPHweDNnHH1l4OgeI0MTjgpcacLRl1+Oo69NHL3Is7Q1pDu5MqoaWaH4"
    "c0L0lyOdoACFj1Tx7u4/gbFbvAI7ckW3GGN3JIZu45Jumd+wpJu6/DZiaG/tocRY9S0wVpR/JDAWvbDid3dTYFyH24dvwtDH1H3P"
    "+Mbh9WT511viW7S3t4UY+mhT9ae/eTyyvBzvlmhfzoemB/X0N2KsggeMFzcHI6sNqmXIGnUn3fEOI+sHG1kRHShczjKUNXCmCXNf"
    "fznm/qYwdxLji4ASzsrEEC+F4Q85/yYczT6jj5SQXIhf/Gfw9RGs3+NtwJ92b3uv22s/7hFZ6m0jTes9eowYsNPdYZrXe7wmyu/x"
    "F2Lfwx1Eyp3tLlRBeoX1t9rbWBWQbLv3GBb9kUBSJk+CLK9Jai6pMlNzScU35d89I53LWfVkq7L4a9GrHMWeGpUcpRi0OR/+2jPn"
    "ShMgQJhQUfOHjw58U42HPfVXpptw/VlBudd+uL233d7awnHgBxaVfzl9i75VP/QBI+g83upSia3Hj3FmD3F4qhP4frzHpcSX/NdK"
    "U4MX9alH1brZL30s25Fp0RkNZrwjvzF25L5A9qbNKDdD0zb87cu34Q9qG2J7L9ERQEiWB+lw4ksODI6HmtxfjoSjqNG4zWlyPgkp"
    "Iakwlwj/aw3+1x63VM7aFSXh/2Q4Vn8tj0cRurLcVXniHs5fIzf+nL74L9Uaxn7FJmtbi44n2WhaGK0V2dhf2+78VaecU0SEFmUM"
    "otHAaXXX7q85w8L5G7ZL7qv+5q49WOuBbKdqsZn6mixFEyIX92y1/jejKPrxaQlys9bV6b+1OL6aTDMmpUBkztAne4XW4CyxYJek"
    "gBNQirrh4MQ0LPTo0eZxjaMhisntuRzWjV3hk7blPWFk49/VD8mCIGI75rxcr7nCLAeOOs6rdawmTTzg4ZRgQ2vsNI8cFr/nrm2s"
    "lRDgVjPS4HObx0MQ/Oqj8dH0RY6IUlqTc7dpq5xkadEiaby8lhPU+KeF6E9jLR+gq5aWaL9i8SV7sbG2uTNXg8fo9AvgMTq9DTya"
    "SjfAo6n4avCwa9vwEKo5tLLF8C9+aIAmpNA/IKMmw9ivhFy8ujseKJLvF2fJxLuLb5DS4hVG0k4HMSUuFovyoWU86Ph2ph9EeFHZ"
    "ExmpTIxgjRjTEkep4jsn8rsSMVJFzIBTbPHDTEZZ/HZGURY/6SMNF5mjYNcdadXcJUeaxJc6mKo8AVPyO0nTondKN4BZDuNWYPZQ"
    "4YBez/HRVFpEQFNyCvdZ7eQAmzDA6/E3xwY1H+D8uHS9VHRunlnUtvstL5p3VevpcflaflJr+SOv5d9nwc8D6P/7WVBZkoskL6bR"
    "iAP+oNHpAFWr/wWbu5QjtngTn4FSxAnaoK9F0yLjNDE3fw0NjwYFJ+rwKPwTzQh+djpiu82A62vxpTlUo65bskvR0bQgR68gaaBw"
    "sftfQLGqo21h34ABlVHb/AyRhQ7/HsUnhfo4B5qhGI6OZHYwVVArnWgNWc2uaVyAAIMaYK44LDWk8Vx2zqOR36r/lrBRAzCJuuOM"
    "blRaFG5o4i+FHt1eVkc5wZufyxvGWAGQDcdlHbbOo8ln0atiWk9GsZhcNEpO0xa/NV3D14Zxzhm/TGFkJ5dy0XVmfWdnAJvfEDdH"
    "a0/XbsSd0kDqm2SGZO0WiIi3Acmgob21BhABSyMaMrYRLuTaenKORixRWlQRWCFA3ToyS0qSgeTvOmaOzfp1cMAVgWQp+uD/DMf2"
    "dHCXKvBtObrbmHxu67J/q5cWllW2RAfNyzTAsrWcd2noyGAia5mY21QzuZlV68ECwAnwqzqg8Rj+gevuKzJuHMbiLE2GIsoFP8NS"
    "Nzx8uvKK8utgdeiKd91cjaw1SrUwf58cQVORA3ZUwwYeh6psB5qngX2rvYyIlB85hqlwR4A+ajkiVd1AQzhi+P00Xuicf8QrdDg8"
    "hq+MQYoB2KMcxrh/awt0MKQIAvd5c5luB50T/3ZpBwlR2fhUSEX/bi7Cq/n85oLy8VUz1AX2LmkD7R/26aRpKtThQq9pVEtaUjHM"
    "7RXmpbGWmAnFskEV8bhxFVAwTYfv0tEyMCNrYaBbTRGJyN/PlvOLpf2yjGv0jmOgs/EbcoFiNPb9jHbo3v6+Q7zgXer53ZjjPZos"
    "4XdkHnrnv4/xovXBWTwCGXyy1hJv6e/I503fzaTR+f7l+XGG4WFkE9qlI2eh2wPA/SxHszhKCftqaHHFd8HCr8mMS23a3ZENHPBt"
    "0wH1EnAZSF+Xv9HOuMiwib4cg6869GjOxjNPYYxL3oMDyykmvXATKadx8Q6vxjOAUHHJ/Uy4Vh4sK4PNoHlvHij3G2rK2pdDbQvP"
    "YyBFyRjDYeIQ2zHQFgAu7FJ81pPSa7M2oOfokqIHLJSbajW5n2h90VQQB1oE3d3iCYidFKxG2uPuFhsbcvoq76A4FI4Rrha+mbpb"
    "/LXXB5jxgNFt2npHP4Y2Z/azEDfwFevC9W+Y4aQvCsCWgc0qCqA3ldi7qSr61fTNMdUPqK6DSxrjTdBPAfqu9hwUawD/PLP9BTtF"
    "8I8ZPiJJMFpAc49XZDTgp55eU3ytStL76VR9z0AkFL8BhOhjOYAquvt/0Pry2t7FociXFK7eujAaYy8WfrERmq8vZ+qVM20M7Zf1"
    "+no91m+WCT/Ib4G5MzE2LroKCuIDsfWK7H2enCcofh26ymWw3ChpGw7JETvM4x5zo0fZW77L3rc/QlfCA/d//7fR8No5cNVr0hPW"
    "2lilcwTbUId1DQx/oXwwCALvyqeD8UfJrDQyKr/OKtJ5fI4Pqw/C6XjIL3VLZz6+EqN21A/WBwtpDC+64NgmZi+EoyoqIpN+07gC"
    "It3J5JsM3bvKh2ykGvVjYUOPCDNC59LwC9WStRljfMJclwGjpsG+SjGULj2pamqYgfI+m2AJlK8gGSUrKjA8qvI8NPhKMhSVHAIV"
    "EB+CAwGGAh8usxy6T4clxfUgKUV+w6kXc5QtwRIKwYo+7KEazJx4RCodTiFbZSWJc5p5vo78FEyh+t7jvkqlRKoqnEw+4BrvsX09"
    "vTyHtUZ2Zl8GkuER4Ju4OEWltx6VDCotmFz2pg3p1A5F6fCvqtA2z1ACbM2SBLFmz3R53Pq8FDBGPkML8YfbEVXQgZiVEMD+kUw4"
    "zHSIrEqpWXyOqXyROOwPRCRcX3NzOEFHaqyi0WCKOpdngpdy8ApLM/LGBlml7sJi28uVLUyxt1oFwUsywq3HYcoTt6288ChgFqx/"
    "uSbebL8yat9mRp5acoWWQTUJ/XotPCZxVv/raugCOWGl7SFhgMOmgU9T5Ns/WFtATsJoM0C2+jwuzjJU68qmzdamQ0YiQQ9ciaOT"
    "WO7JFyNOEUTC6GQJzDnDpAhBVOrJKsJoEXw/XVLGpByqNXtUddRENVqdgIJSRySKfsVS1IGYw1JW1kNKiHJPAvhMQCgICflBpmMx"
    "ptRiqwLh+0GIwVXJZo3qGDuS3cApqTmZfKtUXyvW1royqo+ovmJNcjgi9+XHrEo+bViKr7Ysj6yDqkwODawWmBsjsc1gqJWrqXv3"
    "NDvdPVQcUt9M9UOUJ0Mvt/exl8hvDSyHGKkcndoDOC+dOnHqaauL3CP84dFF3AzxEl4WmJNED9pqomNvEEyUD89+x594I5X9GoiJ"
    "Nw1GZj4cpIGNNG8Fj+G4NdzACRc+Vfv1vdADwlTHYqqC+nvnQYVBqsC2Y8K2UwvbzqHfUf6MngROdX3shRDsK8wNjs+zwDzhjCAh"
    "8f1iI114p19vjLD0X4g6He0kTSHsFVF+jBc49nPvOD6LLhJ8HY8vFo68C+9yN+87RwHzfudOjG77huimnNlATOliShckOe/UOXOO"
    "UJ058caYfNLG1l0PU+lJ5xirn4AkMAYp9TKonk6YBaMfXF/X5GFjkDn1LgJuDz4i+nF9zd1SAv5wfRg0DM5DV3F9Gpc3VuMZuP6p"
    "M/VkYvNwoD0n6U/9gYt9YuuSzlqcXABwkkcMbZ3gCM9nBjLz0CUOiGVqogQ1y9kzl7NXu5w9SQlI8OIGkxJNiJpoQnIrmpCpvfiB"
    "bujiIc0dOkCKwKRiAL8uhKgAlODrIXvxu5E9rUf2QiN7jsg+ZS+lRca3BiHSK5GAT7sQbFOShRN3wJMmzGtN6M9T3Bj9kSOzEAfv"
    "W2QK94Nj1ey6pRKwq3yzgdaE/jzFuvfujRyr9Wp16MBsv9o4v1yFKYhiLWiaF+gkUGnlZncjmNaJ13H9kdPxTgCvZStDBQ7cMyY0"
    "ngTY30b3dgDZaAAItW7AA1vvQusVkGz8LpCQ8Q42viHwfqyAslELlLEEyhiAIsDC/I/JAKArUiSNpd1TFeptAmHGLGCXdPEDp7i+"
    "Ri95XmGe0mnQIRpgcphCp7ICiyCJhDzkMyCg+pCfqC880/EoKMRREDuZV4EmnwmxM/HKy4BPd0RNsdhSDVDSM/A5Qe2IRW0qiJlA"
    "p2BEMRC0iV8aD8aMKpoqKzfVrDQxoEm6EnUQeJKm+bIkF0hR2VDhZG5Q1MhlKy1AWmJn8iWsT2ItVt/iQbOTE2C8SY5o5W0W6Eqr"
    "W1eBxYkWukVHQTBbgoeDOBmZaDgJao4Ps2QPCg0CqTnKnMhLNZpkTuJRgJMF/Cz6iQ+5SplVo4AaeA26pBqNBggscf9gAvuX3Ex4"
    "+IvYgkMffpLyoCy81C+eXjOxhqm59fJGlpb801YnAeuR13C7BtDJCEce55Wjb9M8+jYPjbhrZrL2yglI9DrCEBob6YZTPMn7PX/T"
    "vY9eanH1CrUwKW+7hP9E5iKlzM8l/CdCkopu3jGHbIV21WYJxLavTjtIvEbdU8RZd1Fv6izRmjY1IGVOdS8oGTGlOYR58uP9kzw7"
    "Rx6A3G7zXBccEqUqHNbWYJIDRKcuFy9eDH3Ze8hMJhjyYpKNLtCld3EWp2ZPcUnNIjW4bbxz7Be2vpWXYeF3/JRJkPKhL8rzH5DD"
    "hHvxvtKndcisTgBYK5e9Uv94i+FVlB7124IXXd5s3ru3XlYJ3jx76bKiUOcVulIy9llcJpQ5JUlFgoM+NET9Nt1iIjSEcqQmhxUs"
    "Qnou50srkyCUBmJYRkn3VEYYhgX8PGSXd+hBNHRirdj5fmp8HcJuT1DgyeBP93AX6SY5Cyq3PGPdz5PYUi31IwqcjPigtYT4eNks"
    "REVcD5vO65pmU40g020zhPqZ3TinGq1zgmj+SwC9DMhLgIuGlMQtId3y/1g5ok6e3zWVQ7yR1E4r+lLlRsYOQkalQkgxjR3nG9V1"
    "qhe7qDKunuy+vS8svZ6YOFViu0+67ygr/zhG1kvYgOjaR1iSI9Mm3Bpj4A2rCEnCOKgObra62h9whZuq55Qp6ue19YGBbKqNEreo"
    "m9TWBSpQZOdN1Y85l1uQLANxPHAms7WOVGhQST/x5j6cgd6ln28ki4VZoyNqdDxmgESNDtToQPkOh/ZeQgpree8GtqFC0SyGjC05"
    "XghOXPB61uZH5+cNPB8QAPNzgcHYI7MJucXr25C5ufVNrdjcidYT2FuYLqAXu0jj+k7mhEx5YAyuB19E4kLgO1zfyhPQVdriG7gw"
    "3FCGwiMtQTmvhXKyhKGOfi/n1TdTieF2UvM66z4gHFHRXXT/p64vOSRyRBTbSA5+mjnwH8YRN5NdD1J+pnRgITHwxy4AOdKALCqy"
    "GDBslzA9BfkS4UI2riIqJ+05rE/eb6xlV6HyfvMoaAi8wI30zlKK75Zon+QrtJnV7ZY97osoX6aAF9ULOPH9YmFi+u8+cNKvoKU1"
    "L7g1atjpgBvarDZU1umbQwe9/I7n5C2X/nZc9ENDkbhckMUcwdJXRHUPs9gDX1nAZ30JgQY4dycpidy7eT8D4b+Dm7zjoT0ZwDRV"
    "2lRae1aZNl+LYNjXHPaqdyv1Re3mbpBlAS2eFv24Baw23eDeRvMyKOn5Sw8m4idBgpJsP23lrQSOnKSFVpRmJVHFy7yJN2A2+EmQ"
    "SfuWDvGVo8AIljXpx0/Sfu7HrcyPn/Kv3v3MRY2lEvBG0JbEm9HTaX/aivwRKjXrenbFAqZAmnr3IyUuPiWCNNkIMHyEpxsHARWm"
    "PgxQGNS6oYhOce/ESKaLn0go2cdBXmMycq617N4Zeqk8rVG7070Vj/Ko4ZLgSTD0LoKGS4InwQmHmbWph2DYdAI60Ly+vnC5q0uh"
    "oJo4wybV1sQ5qVNtHYuaA+fS2Dha76iv4Y3PJt1Xk6CLRP1IjAM70ptXa0CNjvRng+6suSM4Ci6AUIzFrEZyVsd/zuRGcnLHf/Ac"
    "SZEBGMnTnMppjr/qtMSkpnJS4687CZrCWTCW92Glxbm+Prdy1Hyur8fyxqwEX6xi5qhBSnnHuvqC/UsmJEM2ITkRinDaUHMghieQ"
    "s1+zT58E8xW36L44iuNg4szLB844GDlx7A3wH+OQ1zSmAbCNMPX23a/X0HkwxYGNf0czLi6utUiwPubSNK3KfGHruMesNjovG6Gd"
    "iWtKNIs7Nc7rped0u/5Ud1jrrrWjPGc4ucvjiwJ5By3IfSLvGsVwhZYrXyimsMpGOpm5VkGqwRzkdZZPtqqx1vgys3R4ArLvIzVw"
    "tCAWp6d5d0AaOK0nEBwJ1vvm8iUWg3r3VUnPqVUPuC1Vwq1o+XQ3Dc2rOypSA+ZefRcYKatizcXwA6RSGFZTBodDRfCHK2BTVSpO"
    "3DoLsonJCTZx/9XFwWAu0gRqFF2KqVt2m/fu2aFAKgXUhb25iqgqq+gsG/TIjahewmkBNQR/Lea4btVSUploWUMOjLAspklW296b"
    "uNsKawL26NcLWgUMHCb7U0bXOBRzHF0P1Q+nMbOUJmbRfaNaAgzNakFFDQXXl83KlqmMLQPburWzCgjgWGkNwMHreVMV26hS1vpj"
    "oVAuCY230Oji9ShF+zQ1smgKYSayIgW2XR8O0AFI1xM/hYmzsrbWGLfmgiguGR16peaDTKeUDQq1lr1SRpsSWoXYChJFdwP89NYM"
    "ed2K+eDN6y1LSjtCO1WeKNwq2SdSMeUtNRoOX+D7X2WvGHIDoVfT2pJahq2fpPe1DRiJ0uiaYtl8sJLsqxw5fAreVNNAO+Mftq6Q"
    "rGGXQ7RmhPfuBY6YZB6fZxfxF0CntuKqAKLABnWzxJHVTZ5cdqUpPsERtUkNXrl6VQeCcUKa2jSvpPrpl9jdjdhQ9WzEUjXMjwFT"
    "jyOCF55gMYAciscR+LNodT18Zu6nf+1hRjYc4s/1AFXAKAoTXa0O2Tbn0teO8g2VjAM2c8Q4YjGOVIwj1uPAn6kcR6zHEfM4oCsa"
    "ikGf/aYreFZdOE7cN4DkbjTxmfe33Aeaybi+7rLZrnGA1fVknHjr6tjn/vA0kXxq6Uixh8TPOg3D7KrRraBNQSzOWPF9ff2bbVnt"
    "hQf4YKY1HrSE493gjih755C8i3C5D/FJo2UvPoYQdWqLqbGgDcEtPXGMB6kTVh52W345PFXw6k7Ti/074nqJPryaYmjFvDamPy1O"
    "lFXkWXhnqYOBsfFRbsA8LhfuoQJWw8TX1HwOwkY/A6FXN1nBnNzxbaZpgRoX3mVf1CdXbe5SeHS446+LF7IUuZRzdN/DJRY/1TvE"
    "yg15v4aMcVTwCQe5s6Xgfsf//7h78zbFcWRv9P/zKarq6dsneSATm52sqclj9h0DZq1bb2NsAwZjGy9sVfndryTLK4bMrNMz5563"
    "Z7oT21pDoVAoFPrFfatLwI3BY+y0zffweh8uXPCXLHiNK4K734eODiGDjpVbp1in6c8f6oXbgQiKk2lRtQ8tMTcGNEA8/930F7/w"
    "BUW698jwYNl1FPFd9dBDV/TpA+5bKHAIEEuR0JZiWgWaKgQaCw8MAs33tsYetZeAocZLTLtI1vcNUffV2zJcJJZdioxQVX4OVFGG"
    "akcLGgAM5tv3uX2Dfv7DEx2T8du8rf069TDH2d2bpYJzc+QFA6HTFug1+XoDBCjmfetKBYuvsEdLDAcHsh5sxAH2yTeqQCTFMikY"
    "GyoANgWrJ2IaEOnsk7sMxMIhjVwEAXgcYf3El/QF67jT3c1aIeq/XTMt62yS/vzT/Y1vZbMx59AHKtp3Ya9ceqCqi54m24IX37dj"
    "vfwew6EbbJWFfXJVLue+n+gy67WSg3L4Xrl37gSPxyIcF7vqPvbfDBsc78LqtB+Ogvdip+g9+fTf8RR9J18x+5IQKMu3r3MXL/TF"
    "t8GDayJ6a03q19j1Ut13mUYLNpQLo70e0jg8pA/O4MFBvYaI9w9Y6Dm7lxMgyfG0AGqsEjKwDzLok7XJt//IcEtiIcZDqK0fryjG"
    "mgO28RI+U2xwtnCdBUNCwRCk14Pm9N1O5EEefR49zOcoZNZnISAXUQB4jwHDw5qhbSSd0fBoA07deJmHZLfpByvwLecvngGxuv0K"
    "xkR05fDbI+JoE8rNOfMgx1yG+/NP6NtaRH7Slh4e7td8exBdCgbbAaOkI5y6n2FsfXlQIOV0IKxhLIY3xtcLNuTg8j3Y1SDsPHdY"
    "Y9/nqDgYheHV4jK3mfARLCpgPyEwNsabzKBzTo25xnbTgXCGMQUCaE3Waw/skYNwhbGeXMQthLxkajqEXsL4YV/fBTlr6pCxUUU2"
    "0tgtLCgr1Q3Yp4UVSxYCnH3SFQmMnzcL+ngNF4tO7q2mOe/8NXtLcVM/8aaGduz/iUFUfeBTH8xjNe7xd7JiiLvH36v29KivWV45"
    "vpkxSOVHDTCkqT+HkNj64s3iayPGvbOcrrzF2m3xlWm9ugbpwuwC4V/Bk632RJ7XEFvQCybmoayvYJQwlCverAT8Xiqcqb+nGpTw"
    "JvPd6LSVCWJjBPrvwzQMz4A8iP4zcqs4OLtvfr1qnz1wlm/arSqtr7fIBxHVIC6lbDxCmG6BvwP1ZpeN0oXM8jfLfgdD3K0Sc8Xf"
    "UHEYk9ytGnPKe6oW5QMLxds7+A8nfReje5rvKVrBYWO8WNo3emLnfkcvHtERRBBTzwJtBCmWfszGAKgfrg4VcQMFPBw8226npqgw"
    "zII9WW400U4Wtvr5l72bYJN3AScdJEFQFhADYC5tHTzFIJVDZeY1SZyeXRHEgzl4lwoebkIXMiHxPiTscWaY7SNZr6iPIk2Fkd4D"
    "TI86tgZ0t/RiqD1A2HKPAHOQZi1UXD/RAU+D/7kYtF5EUg9kPfaN9vXBxgw/+4XpFSQ7UjGApvXotkSQJFHVRf0dWlMIz18tIW8x"
    "ia0VEQHV6gob1wdsefRgTToSXzZwCHBvAwI4mN7EfiDKsPEFj2BQOWGtSH4Q0Ouee9K9KcZsAfn7tdly8yO1OsLzNhOHzFhbZt4t"
    "3SroUdipxtkrm2+ytyO1CV+BCDj7TvMwI2L70I22wFrBTPxICAiPVPPh/95ZTHAtb0O8BtKHKFl3tgVOLTc1tFvabiBnmCAMVe7s"
    "fNeaXShidDhQM0Y/84qtcGDp0AFcCwHI3TAJh0KvWiltsXaTOy0URU+BV924ZmgRxmywrX+hPO0K5msWRFv8R8gXagj/+kW6Bevv"
    "47mwDltlPqEygz2+x6febO9mVm+mK6a7JYF9uT4kjq9z3pfNYHA8ZL1HQO/MhkOKdhiPCHI1sK7cZLIQWq9Y9TodeOlNc0MXQ9oU"
    "L2rWQeTzJ8smepePQjjoaikG47HYisbjHWPFnU9vjOjvjGV4eIx7ytA9G8ztleR3VN470ytsYt3QUG5Om48rQe+08iA2w5V8yNTz"
    "wYxX9p4P5/cZbj6Y+9pk9GYBdxdEb+736fZWYnvP7Jfp1hPcuv/+ltqZIuFb6rvMZWW6r439Xvvfa4v497T+ZsPf3UA7w0fb6OT7"
    "6MLnZAyRlx/t5YeZyVP5b4xLIHdggMB/whUcFGv3KvJAiL3gloaEAqE+3ozYdr0Q3DJG4NhI14HP7I0prAgk2j6tYGgu7QklCYmu"
    "dMMmc5VfeIuybo777I42TY87QYfR499QelHaJ5w2bK36dyzk1+q1ZPqsfTeW5LeVbn13Z28a3shbscPs6GrIGhPM4bGOfL0Rj+1W"
    "ltNNKvga79jmcPCx3+7HtV3sPcHV7iS9VqZXHyb6rQBlt4kOcnyU6J4sp/c1/sNEf0cUtzdShhA9LKnb7iXEKrCsJaJ8b4vqo2WI"
    "QLtLTitTUIZdZbkOCHftcgv9vq0YEshTHgVgQS7yMOiP7UoLHerwUaz66LgQffKHarR862x148uz7BiXoN8htmh9eTae/sC/kTui"
    "7xgDfcWvIAqf9XYOE6KF68uzZq1gdplu7d4SrJ/XKQJFINgDyxwyEnURtBRmcRYwGMTsTgIkFa3q4C/PFyApAhEZITEgvyD0+R2K"
    "w/3Fy+OBgIXe5BK8Fj1/ha5ykKveOYJX42bNfGuIPEbFL8+f5SeBt2IKIHhumAy6I3tNj97GuobAQN7Phu1lgUD30VUTuzTQDJTF"
    "asSvX6Jkf4xEYNfQUQoKiTcPOaGZx+yZ7/lsv5rHPM4Jnu8+TwangEAi+zVOhcfak8C2NXq4fh6zrFKeVNaLeUzlKmiaez5Z8x40"
    "EmxSira5ydtMnx3KShf4PMceP1VoPfG2zWOE8qVpIUYJT2jzAd5ChHGTJQJkWwRYwgDrjxBewZ3WLHjAc8lyerlmO6sei+/CNWEw"
    "ySDjrYGglaCw7coD9AVx1M6UDFHF7OVoXB55IPsbgLAXAcOxMZ8oEiGTWfXeII6PLEVYUYBVrhRaO3EB6sjhiV31eR5D/N+2NDtP"
    "Sp92iMJJiow3WNYA+8XYoSdKJztGlu15ZEVd8nbuOw5GVcGD+wN/HaEII7e+OuGebiXw8NbdJEUYCVcT5JBUPtj88MBZZEoTdvPX"
    "mDVxnLhJ1iPtyiQ7o/WhpXCsJPjftWFwhLbCCzdqwrNOdypDsU/vBbOyhZ3TKo+MvBewTBP2pqjdjaSlARGi3I8oBe84NIUzjmKx"
    "Vo5FKCHvZEBrSv1uKDWUxPIsxUGzcDIrUM2PsOQ48AZKbiULxvyCPHK/XpTk/fWi5G/Wi4X1e9O9v3rLl51R3kg8Xyj8eW6F/prV"
    "PZHIwiKaLcDk9iW6jjP2duw0d90MpbXlRPjqX/3uprQmwtvpvGvu3YSaoAuGtSp25ZrIC3fngCftW8x98AfnsX2X7ww7HBYrWQUu"
    "GW/EbrPa8VZKS4p33ywRLVKAAJD17jDF1SJ4J62zGt6p1l4+77XMkpV4YboXdRE1CFDvHWnRqjb4aIbKe5viW0vvpHt/QEC45bCW"
    "tjvFOYnAKrk430lpR/bTmPuR/fAY3wsD7d7DYJl3ReZjmf+LIvOhPruhyRTm/+LIfDrzL4nMB2j2dmQ+jvm3RubztunfF5nP7qQn"
    "Mp/E/Psi80mMu8kymbDIfCxzPzKfyTiR+dDE+LdG5gM1/k9G5nOIwDMe6bOGD79+7aw/qvVnyTx40sOnn1dtrGMPLdYw4GLyyVA+"
    "6SrUweEZ8COSi2AoP9mGlaf/qAPpA48WYcoF+IBTxFB6Fu4VPlmU0a0er1nQR/bT94Ck/fEQ+WSFsIJddxqpuiMrWNcSsQh0aWIT"
    "fGUltQb5289XMIoWtfBwRfC9wVzskXQ4CwU5sjg8KJUtlvC+eYK7T4ibAfK0WRUwF/o5EIy5F1FbiKD783PKljggYfz/PLw8D8Vf"
    "9YhsgF+5X2TmVzIRAT+Bsr1TBT5ilfBH/MkQEH7NC+6PrTC6NEGD+jOci4Urun5GEvDXL+E74D/77Ry/jlyje3tZam3XZH0XdfQX"
    "vPPS3JMeN/kn5FmrVuOfApbQCGLlm/P01Zbn8jcYwccqGIye/A/jqwxkufZd/gEmpOyAt2soBuVfjg0guP8XmZuhJ51IkkjZBH8X"
    "kqnBPygm8CPcMbpPa6CUwFCU1kv8hI1VYDdvGjp4VQSctPUHJcQ7eBzfzxOn0J8M7++usrvvGQT3aL3doZ062F2zXReKwp9xbwra"
    "2fMVx+HGBjurbGg6Q78CewPccrCf4Na+II+w274XuLwydCfxfbAyWwYUKxCjDi0LEnrjCeyINmSof9ZzMJAn1v04NwU2X3l+eixZ"
    "z48kVtA9Vfst0lYkaRwIcue06Tqu4HWDv8FthHIdB8FBeR8iWP6Kt1lW0DhsV1hKQKt5nqsKNFJexXx0QEygEt66YggUy9AxFfy3"
    "i7odF/FmT2JOYLywIt2v7XvsiUIbXkdEtMBtfCPlwENdDYSNE+BaOz3oUNYdQTvKlMwPsN3UwyYPEQfuKmSQSTss+NCKwHgj/mI3"
    "ZM7bVLgXodH6dpuC1vc3aGhDYWBcKM0NKuiVNw7OjO8t0NnA0qWcH3wINZj2ThbXKPPnn3/xVlUP3pQOQo0TYtLTnCuaoW81V348"
    "+Kv1ShDYhGvEq5CEvvb7xFV4Eb4k1wA7wUCEHpRbHJzTJyVdnIJnGOcQIZ3BEjwltq5OoHwxFd00L5biGHgbgSHznMICYiq0MJTm"
    "qjD01i4MPVw3zIZ28OQAysE3nzoAf3/1oBv6+wk3gzjh+AFC3zES+PNiGwOcxFZ8J2iYDSM1hn6zTLeenuA3GGrjquZIdP7XPGp4"
    "q/FBZFxHk/OXY4kFAqRycNChaR69FvSrza1nP/8P7TXixzCyA/X6oEYEGzSdBRuFQLUarFYB70W96x4LeOip/PmnGI3al6efhZhl"
    "pWERzIDFtloMNfhZiUFvIXib6pl9FKNkDN7X9tToUB+0iI3E7EOl58+gDtgAW1pC1Dz7PMj52PUdfEAdD0ehoBkvgsLtKQQvR4MN"
    "IrpadTKenQ5htovZYBJOv9wGes7UbBXAEvFhx1mCNRXdHriHcKjJwa68Ma2cqR6cWSXHVxCdH3iH740i3cMhuL/wvIOPaCg9vOw5"
    "SQopNdgoN3UkWIZz1PTeYuwMMBASUH2vcZ7scxgbs+6WnMeAlV7d2r8C4EUf6FixW+N6e7wfyRdn0fKYrF8cJQAhalWusj5geWIf"
    "VL08ks/3FYdbTBcDSsgIw2z9oQlLnKYOVT+IEbb2GTWDaO4++Eo/qdBWAyJYBukEsSixXmw9hFDmEb736OIwpozxdHXGgHwPPHqz"
    "JfXtLl335/Xr3bH2bBNuYnR60yAtHWnKEKU5WOqVKuHJGr7OexI4q7x9iHEd6D0QvBlT0eHDoE768L+SO2/px1cpI/75irfGCNQf"
    "Ht2b2jUTx+SvfsqRN2fwI+lV1lyW9EoItAkXYLCmbw92GDlF26HD5siT1YiIY0iwrDhyzEJWBetaCbq93A6c8fkBgpnCGEFwmVzB"
    "UE5ghSyCXQAYqEQiH3FVIZczHNQpkCMCHT4g8KBRso4wHjzRHqBlCKjDUFOBJXOGJoGfX/WjCLR5hB7KgxZxrC7MKU1TjrCxcxsp"
    "1nmDVufI1wWQrduvbuKh6k86VK1l3Mcj19lgtIH5s/uM4hX5S4JJ3iqrpuwEJxd8eCtDWead9OD3W8kh8qGPHPaLa2rALx5iWI/X"
    "yRBuj5MKPb3dZmjPsYjVMXcqy+M3Tj8MrDz5s+kcq7pVWY/XyRh24aQBv68TFFhuq/ta7bx5q+WDtbg0PEONnvFQW8mcQ0z5zz+P"
    "YK2HfO8CPIduveEyDYT6Z1+19jc0hW3sHiFmlWcDjcOlxN6lBzL+IQPVjwHrln9BwIuMdZ4OVxn/4uO+B4ICCHQgkPAaZK+AFnZ2"
    "GVeGkgZ3OJ99KovrwWWFUrH88L6GCajPoV02Yp/JyJ0V4ZG0t/TI3oFMDUgnjoXT3No2eSiPelR0IddAV28hzXsNaV+v3jgyOVym"
    "gScorjAZDHbVYXfImbLeoYfM3PMN/AvtqOLCNISHeQBFdB6BeVC9yIfLk4+TFB0asMOQR+30EHvUXoUda4T3yUaf0x/scoPpMSlf"
    "HDUA4lY9uxQFT47pBBOGQAtH0SHWPQ0hoPH6SfgQQnUidPy9pquX7z+e/TjBAZcON2B6QD2zlBqoOdTQFcBr/WYEAavRlRGBt8zH"
    "3zDSbFCje6maPjrG5ug2FB6sR+uOoeVCCEnx7YuhmcKXH5E5Ju61hhiDe/O/pWmTf0HTrFmK3QnCjAS/GWv+MxEWp/6d4WiRdhIm"
    "GcIZL8CWV7tzsO1wdRmb3SJ4XfESoI2/WaJJu7OPcRUdMWA/QXwJD2pC+F0ESjieyPaUtGR1WCPeb7Kxq4yJ3/znUBhbFElzjBmL"
    "n56//7AjYXksHUbkRbxt4flswj5oMflJ2JusJBpnaIZ6hWisUB5xrPHAMw+gj9+1H6HdZz0c11bAGhHQUGE3hScgUA0FQW07Zu8R"
    "PHHFtndsgETsgBcg6Htgg8wi03XIBkKIGcHa24C3ArW76xf2uII2CKtB+r+qRZaMuxU9xRPgzLsq+2Tgm5sMewuDPcp/WmAMrITQ"
    "3J+FGHZTsIHob5h3oWD/FpbAswfxR7InPB0M25C8axfyr90ygCn439snBAq4sTkIpArdEVyl+Xdr4Cg2lDti/j2ud3IEuczNM/zI"
    "eRa6id+1vjxYs9P2rw2qH9Xjk8XDuKBHpLWEsLI1VfCCJ0iv3mLDWNBiK6itYcLZipaPcrAQL4eFq9P+Tka8G4cw9f+eZLh/ZOeu"
    "PsY7jC1YwQsYWcKsJW8bYGCSDti1eD/dsp98fYf8uzYhOKRGMzREyX93lEz/a4S7DVgOTlu4H4vcaPZnSDiHCbwLsz0uQVEfXs4P"
    "e28TOJoNnQlIG4Aou/cMKr8x0lDxvDGK8NP9caZBW/6WcZZvbfO8MySEExxWwNLWxwy/yQb3N6mwRiy0g1P8N+tzt9acqUE3XUvH"
    "h8F9oV0CHu1Bu7ThuDyjCFEPRMxZ9R3v6QG86Rl5fghPbweGutExyEef3i12riXEO4bwa/hktta3fzE50eS2KRoJo9ANesawWuW4"
    "XXknnO/T17BSZcjcdxbGD9L9ar7+PtkdW+D1Nt5n/SZCp17MZ3V8o4gQqYhpBu0+t7jCCB59h6oKLw//Q3La3qDBCfeGen2lfd7q"
    "tG159XX682/PBVdVcVVBRFtbc3mLuLYwtPsKYd4NRYU+zOyKtfS3W32xlMa/QySHW67sYWD1im3RwIHu9YfIywMym7gi1N2kS35b"
    "iydf19YDfeaQgNkoLH0YCW6zxd/ImG8oDJ6dYAQfS3mM5H/Pavmm+PHo14gN7wZrDLhSAXnqaPTzGKaOe70N23P+gK7fwsFErsZL"
    "cfV0QV9d7ysG8ELsp4MNM7ehHOcxCOE4J+b2xta/4Qg5CrSP/FjD0Kwxg27O1jt4Ycq+Y/Mg3HPaeqfL1q0vt6M5hqRFJ8bGU+De"
    "GbwW7R49+K7pf+x0ARc99NhxwIiT3lGnliBHYOixtHnLORB+t4wIYV/CnQbteJ/Ib8LTjJbAHoTA1g7dpXrCiHhoh6h/m0Ootnns"
    "Q+6L4W2859qIW2m7LHhG+hu+Seoj33Xjb3seQhnvZeRrr1V85xRdixCk5fylFDAc27tjOzSnfcTgS4WptxNlKzJk2baFgnzRuXqa"
    "x6RbxeKoj2GEvRf7Mcx33FkcQr598977sVU2hLYAJCnNwugZQDkKyi7B7e9n+UmUOcnk4QUk1PLgO1vGwGzWJu01xoMZBgVkSMBI"
    "bJW42WJoYXFCOL5FnpulQF8PpxGhcRnf0w7bH+Sawe+Nkc9/9tcvFOayuvJayR1Iipg/3uXVMGB6hrnrhkoGm263Gxvm9xtSePik"
    "/pdEKr1Lgs88CizsctZvhS/9HwgJ6uGca+/tGzRzrGRe3Bcr5liwBCemp8i7IuflxWb5yBO60mGvzzCaNCjh+1LRvn3546dbZt05"
    "ELJuHbzCY1V4S9Pk0fHyw43qvYP22XWXROukEHaKFigHn+LBreV9CRHSc2j0uOUWHxZ/7hbxhK8PwrfQdjnGeuFt0RFS+q0PWBEJ"
    "pQS+2XzrDsaNWwX3b1aEXuWIvXlf4C3mvHufyOZLN9HD/METAheC72qGxopGZI6tYsHLR99wGMO79filRtBKHlpuGKd5A/Le75fD"
    "dO+m3duFOtcnrpoaznbvb204BbDvpCWZwnaNIVEix797oG7vogjX1bl8YjkD0e+OE7X/4FCIOFfgw3353TuceB27SvHyZCgWgk1L"
    "OQpaEeydvNtC61MEOxR4XHnelc3tHDKV6WPRWP//rWsWWidq2sNvdRL10tP0sA6OUX8+P4S7F8Cbw74v9qUFt2j/Mc5HaBg4obcG"
    "xX687UYd5iDg3qLw+93c8RnADcCPT7qyE8KufiDHABmsdwHHAPDemz+GT6p9qWJh9uZ3hMkN2BthKZbNNDSmbeDEHl7zj4UYXO/X"
    "+5cUZuqMfajCwOHZ7REU/nHPrPoS9hGHfY2SkTByeHjtitHAWD2SzpXvf4Ly5SgoB16UCjkJutPofxIv4VTCjSOgP/PvNsluTsih"
    "6L+KYfxVecYxpA0VRWvdAFq0yfPOcQnUConhUAKZF3/9wrGmLbxKSJq7RX82roQTtAX5BYt3Ll4fU4RT+PYhtRPa9x/E3ZNnwZ2I"
    "/6JKrw9BhdeYz4P1nqvVb/u/XbvPXi1Qv37N55Go8dXyI/tMQj10fJUqYl+Xeycbuwzl3lTzaicWP7HfLDv1w3+rXFcxQKVGYiw2"
    "fz+I0KE0Ztdy7+zabcNdBwS37LeO01gPTE7Yjdg378Nev7thk5WD7tFyIJtl7EsTgBQiBN4Kb/Pf63j59fbBhHHv1s5te7gPq+zP"
    "P+UPnW78gL7h8Nacp+DweR0Lce7wHUgQoZ0mfsCV4rZHPZ7Olp9EAHa0zj/P/wCbrD9E/vWvP34ar3Mw5S9wnw8xIWJzSfwu8tCs"
    "IFvWA+1FcyhkKLArf/4ZfPPw00K5nsuAFQSISoAxrJ0XEOXntpfd1SdoIgq8Cjja3egc4i1rzboBZRAKeeC5mfXmLa+7M9ZbLTo8"
    "+CjCQoDxwlvoWwpvACIEWNU1VrzzLA7ysI3WEOiJ6zgKcZwE7IwbE/wnAfb+9obvpYFWX4k1rlck3yma/161JvAm59XIYxAhDLAz"
    "xAx7+OkF/5XxrejPBL5arL1G8LpjPIVfjX2QnfVUhMG1w9C2HH0J1QhZLQYWV9A2dN+WkqTuNUjIvSvAeNV2CeG9i6/b5xXWE6SB"
    "A8kJI8TfOu3+BpoEp7M/jTNs8NM38GhBF1zhQ4aWHEgDagDSXdmpJtyV/fQz1U1hZ2/SXDI9IMCsoIevLcJKS9s52/AuURb4bCyY"
    "y/vCAbSNXW+Av/oBDzx3pjGcV5DmMfEb8h6Hpv+BgNDhlG+EA0MUyidWB4BYvcFq8P4K5Ojb8AIsdAWwVBfZsziIXnw8Mfbdx/Q6"
    "8wD+//MVevOD/3LWbwyQFXa52wMkFvr9eY7iRoF1HqgjgQmlRKOvXkd4GZ7Jw2XfAeyzGf8KkP0jfOHcX0B+p3f27vbliL+8TkzQ"
    "iT3iwyFwcYiBNuoDW8dAYXCY26zq7KVCxxe2RQjsMYyIzUFCyPUIGY2nBpopIz8ACP3wah8G2Y32AUdg+6towUaAx5cXAy1AIRIp"
    "pDF//mlKoJaQtoB3fsOFI/ZehKBdSoxg3E5Q/6vDrxgeNfK0UUT5YR77NI+8eibPGxtGSA579ni8OX0QJYG7HNgt6s7oheODGPBu"
    "hgtHjU4wrlCfPDutABfazPlWhzympvd2yPv48jKfh8ObIJjJmGe07i8sFgoMXO2fvdgp9vYPw3bfKMIL7Q2kUxCT5oeNgNsXdDAn"
    "MagsA9E87k7sq43WDbTQEBYO4qt8Ml68Qt5tAdAMEGuAsXuY/ySAVms4jr3OAmHlvcbPRV1wv3neYpESniUACBwkxDVlccJbXj4S"
    "Wp7wGueknc/DIH/vVXad+o0aMQSxr9q3MwRqmDvY8JQDEHyXGrR3Kt+tDoIJv+BcfkTjN8nwgf74ehJEcL5XUTDtm+MbTO4M8eAD"
    "tYZmeN9Ah9VvI+y8OavfZUZ/CVmJn4ln0meftG15oUQMn9R4JRIikefbRMBzM7DrvcWLN64XIBE6x6fr9mY5PMPr3MK7BqrhAIZV"
    "ulFTuGH7GnDK+vAa87586xT3SpPFwUV+YMyu7z/uWoaD+g3eVPmlsYwsqGjboyEnFngwU7RR9W2IxavOf3ZcJ1Ha8Bus4RerXz5j"
    "0JPfOLmxFeZn79vP2Dx1wxJxq/Hh+Plw/4Mdf0pglaVDxn0kPUAVHMdwwl64dkQnB6DKRxCLb31gLjEUNAnntgIoWTMHv7oOAoXP"
    "zKEPi/sLWieQpnRPqtyLQuR8j7zM/98TRWCNBb3CRd8nBKSFNwxIKEaE3YKgumeBAyHUaD9H3SKkE4HEV0s4aWJz1Nt5LNxjJxis"
    "6f2UwgztGmd+cweD3J29sSneYLmbHIAtBG9mn0PPDlZ6nEd9Lpa33iM/HhzK+YBCqIkqutJ9sMwEKBwUeI30b8SAnVNsFMCeFZgY"
    "jUp/FhcxlBIFzRgeY/Av0kufR8cYNDXrz+NzrLgWDhogBbzi2D/GBqooQ6+N1ipmKTPPhWMMxSd6rh9jKPbQM30E7Tww377PRX4e"
    "wygW8x+xs/MKYgmDP2gEwF8PB4InW06Bn3bABFgKZjmUwApfA37CWWnHSvI8oIAI9hvhpLKgECc5lCiAGLr9zCJy8oLOASqzMKCW"
    "9R7LEG8PFsEeeBqI8gSb5unLv6ep6NFDK6fpJ9h052ngdARlQFPH0g5gRpCgiBP8iB39SX09sBWakIrxd8Ny+LMebehE8Ixvy1sR"
    "0+wn6MGDnoqWuxhur7ca/AZLbfeFU/MPN0IFgwH2Y1pMjLHWoq58ox7mmInnkZgOH535Al5w6DvibPAkOZ/h5AAvTPTCnijgBQ9f"
    "IP4HD0v4gOYAeFDhQ2D2gdc7+NqageBp/U0UH+bWPHaB9ytgT1x/ACx/mMdqD0BsLJ3oUHCGiBBvEahLVixF8Js7gTIUBbYf0+7Z"
    "+E7COzDfrqUP+xTEvPnzz+t32PbFxpwTESDXvljE/vLMPvmX5Vd4l8XYiXYzIrHvggur9oD7gzwmUY8gaCYRQ/1yfR5xxxwvS8F2"
    "sYwh6HEB4cAjQ9vzHMJb4liSz98tAmADRQxnQ9GUYsKTG9npB46C8h2nQHGZ7BTo4Qe2m7NP16YMX2wtwbdoOrGyBEfHckO9uK6e"
    "EF4O3hdc3MTORAcbUJJLggE6qSyX8xhgHAGO/m6hLBQgZ5zYXbAy6+evX9bpVeyLO0O/PFtbOqSpej8geeP7it7gJGtWVxXVBEM8"
    "hwZsVKP1xds0/NX+ZEutL8/iVXhKnxi7TvCCGDk6/wuV9+zrR1DYwdx43kMLbaAg9uoIzleYE+4TDj766VDNhi40vhO3Zww+FXJ+"
    "hs4PjOBnfL8z9WAKqxz460YxTeGMwksa3xO3S8LAA1Zh+OFGeRZal/E9ebs0H7CXVabv1VsCwVVNsTBwZqTl2R0jM0ABgDfcsDTQ"
    "AdM4woD8PWHw9wuAt+dtcEJ+8S38X27PS1s2fPHIiTen7q9fD+wNNfjFymrTPvJ3zPL/5VP5i08L+eIVre4sT/1dszz9t83yzN8w"
    "y985F7934HUDtNdyFHAcUUhwXCpvrnWvsatWfi88MDaPQiUqEiMjP14jP+CEXzDQwebp2oTx4m2Fi2gX+2nN6OODNaWdeIKw5Rb0"
    "GytJCxYoOEhlccDgwtqFBE3rYQPLsst5mYvz5zna3ABJ4ehWTjV+ieKpPuYp5IejZQUbgYntzffzSwCR78uzp8OvrnD8Pkd1e/Tf"
    "HxFAyBhm7UTkefQAoRKJSKzv6oZeFdAJQRxxWuK+QiqZbfPxUh+/C6W/J6ziHG5sr4nslImoGyrbiYCY9pYJ9n7iow7U8XnMV9IP"
    "W1Ihb3lAMugkP3e52dcum4T24tJ6UNx1xUsgf9Ww2uf5/HdqcgbLN0RE5NlLWJv2oZT1mhlukNbDv97ULxZ1n+eenbnFyz4y+yuI"
    "+csIJ69XhFyZQa5Y6hZJ3D2nlzYkEgiR2OVhF/vpxC8VHNvGa+ynDaDafbimxeVhg8YUL/4qJz+AxZCVubUCFlo7LDba/1iXhuHM"
    "9F4gh6Av7pViz1f3LYRURDdmPV/RCzvv1Vf3rUMdQ2Nl68Y4pM3dPl2tew+BfZ+7S2KfXIcU/2xye+7cBPTpOs5bS9lxt4f520uO"
    "Fy/LWne8b95czEjizaJ9i5r/3Vtrm9e25lDdoQKQcn2P+LGUyneAMcwdOYFZC1/TYTlO0NHofLq+ugPvYNvqoncbkb2jYATagnWN"
    "wNswGjh9tVrhusdZ3fGsNNdt/wL9Sb7cuID0BQUIdGRozCvC7EDyVwqCHaWJDRxzQE8tfIh4g5298hgX7y5X9gswjJcHM/bTlBEX"
    "w52A/TOmGs84tR3e3rFcwJLeECN6zGYKB5Jg7rMpWD0VfT5PQG2RFV5o44BO1pB5gOnsBDZO3XUCv/C3Gw476le1rk5tY/jgAbp2"
    "Wr9iYUSxNiXWqbZHncf7CfYpcGgcZmiwcoAZqH959qnyN3X4Kz3dIwZcEuB5bavN7gf46OxN3dcWZmXIMEMDm6LtitYO5PmnrCDl"
    "H9AXcvCrxcE5sA7ZZmX/sLkv8KDMY86K5TdAY0KDXzZ9Q42fkFR3DLMOLdDvghX7DncXVmmABRIsh9J7uRyut+/ndO8stgYfqyHh"
    "SpwbZ/u+DudN6cxa91WoMsbFTsKDrY+FZ/LkglsHIEX+ek6+osH0DAEi2d2PMZ/wt+aEwRowxAKeEGCUvsCwbpIIkVzeEvpe0YTF"
    "ruub86bIBS2FO6Mb/jxgn5S1lKK3NXs4Dz1jj9f2n1927OlxLUAg0S9IFN8IoGUjFaCUQOV1F5NAwUjuqvbKeVUi0D5gzvCj2thP"
    "5MV4tSTYjbXa+exvjCcm9iPpmkRv9sUzLw5B0zogty4+WMGPZN+s8AB5oMZYpiEN4XqgxFCtUsAj6kFMt5yXPSGXYpyb1lKkJJwa"
    "OiNgsz3UPEzJ0TtCvU2xwzAKV/XqGPIdSevfKMFXYGbYqhyHpXzAZBM4u4HC2z4Jte0ivuFGowymJmS3+gNtzbw24FNfaC+whdIj"
    "YZcQLelAx9B0RtGuX2PfDcu7wpEdkuiRHJ5ezqMGjhzlZwrpRULgL3bUVZ+W4PG7AOSwaKBCIHd8Rxts1iDB/wKLAwpEb+uE3mwB"
    "u4f1DbV57oT9MrCHh9fRA3vhGnbouWvZ6ZU4N1rdsmwvbzazZdtoGO9ouJ8ewloYseQINrgUoYW1Kj+EDAQZPhDXbb6miBslzHCj"
    "hLkeAQG/CucWiE21yFujbY2pXXvAFIr9Aqyvrs0z6IKKE9hWULuZX7xNDpoHPS3/4j2vhMLU42yEP9qnlzCf/TvmOccMn/FX0OTw"
    "TNIiDNo3OQef78gOscUD2a3tXFl/uJvbvUtljyjYEKDQDN/nEJsPLp1fAoetYAUDXAFPNiFGGXRLcunoP4X1WHP9Ll42j30JHNJ6"
    "KR+YFWhgfeHuHgx7vmIjltMmW9xgYUQgQWQ38gVrH3z41sMqER3cWjrIB9rhyRVqEbIVn2W4FcoqBB0Tf7hqT65wY1Qsk/LqE9dC"
    "752z+78p98JF3r2ehQu/wOT2ybojNC5//77+8cPqNpAzZCIH3vk2b9AbSPn1S/nzT8Xr6xO+VHk74vVXvbXuYBkeSPqmVuhbi1Bm"
    "B0T/toE93D/ZY20H4/5ZcK/UOD/dAIi6hwIvoUvE/xgB3u76zU7bzI6YYsDgHULiFcoKvHhAK66gveAY5tbTPLaUbyiJmFpfQ/ZS"
    "dt6ftgVEtvYrkHwQExKvaUCekkSKAFMTX+2ZoyXQ78dk7WeujC5LRTE+anT5LDjIjA8fYILIy63T2H/B3qn8QSa5MfLZwH7pX7rf"
    "G/g9tt/b7BBHb9Ty2JVx8h3Asn+rbTJ32zYZiCdkmSYDL99hmXQwF/5mwySa3ifGO+FtUwBaA7FHHj4AQL9c2z56RJZ694P1GLAo"
    "2OcReGbGDkzk9S/mSUNhfb8xDPL1LjPfsCjZiTJkNhiT8Pmnwa7A5s1+N9dsfzbdXBgay0GrDy9wmgAjZQBJIsAl+zWmH1bPP087"
    "CUzs+dow1Od4/Hg8Ph2TT4q2iicIgoiDJPPYEeJlPieIGNaiwa+DKBwLygkInk/EpwT8/xx5LT9bcKSvMWjtAk36PldZYw0kCv88"
    "b5PZT/mnRLpIZp9SZCqBHj6Bh2wa/Ezn0tk8fiKJov3DSmnnAM/wbdb6UUsWE3Y+9CGBCsR58EMR/bXLt9OjqpPoT43MzuzGYxD2"
    "oiIpYOCQZBXN3Cmxn7/+AAQrMd+2+CRo3rZoLcprQRNR6DT9+TMZ++sv3/AARR2hk/yUBOMncnc1Xr/VVw9lJuLcfY7JkW//xIpb"
    "CV7fOwkPIxaKZQjbq3tNVPBCYZf5JqlPYF4DxrAbgxRTtDO39jvz//gE/nlSH+0Pn36iN/AfB1f4E4rSBcTUV+cbWCJUCMH6ybrh"
    "/7iUhJP7FajZGlbSnz/BcXY/AXlhiBwrPSJ0t+dPC8UwlJ373WKhT7zx8J92k57Qu/+MuIkwe/lTWS/tZK//EezZI3Ko8fQPjKEO"
    "tL5PGCbXLR5OMFaDcMfB1rsksaGW3W9os/WIEBAeETbX8yci+BVT6/oz7jZJEP/PdTf9b1WWh8e9vuxgq7ESZd8rRWU50Tj73l0e"
    "LWn7ifSkMw2E0QCmp7+vC0WDBv9PpHr6BPoKVAZ0cKiykPGDyR41lheB9PYPifXtyfp2Z2T8fOfwlp+pNqZuiMvzo208+8QJgWGD"
    "HPVoWfiuPn64meEkCMvHQSHgy8ZyW2i4kflgRc4Hb3KUP5ASWsKvC/67Jgf8xz0Ffnbe+RvvL8FN/8SbGlKu/zMS82e1aIya/RuZ"
    "T4/6muWV44ezYhZ+d8VXzP+Ih+AGg9sNC9DUenlX4PBA1BmgTf9C5g6rF5QSu9MasFbf+yx6mhvGcYg3oQ3qTa4LTbkEXXyEL9+T"
    "2B2/R3v8nt89wtekQTCXT66VJ/IM7+JfLRLPa3haH7kjo7ysHpxqMG+obAgZKvRD4H+vJpz543LIyfhBeYSzvbNTfx+x3+oHJnlo"
    "b95Bv9sj9i5yWNnfIMp7iYG2Fo948/ybHIjKuM0Vt+SZlQ1erA2INp+acCsLXoduFwn1zTvfr9ppy2ZluQSq0+2Kre9/Hzv+HSNg"
    "s8btkbhuJ/iJfYU//fP3asXZ318f9iJ4tK6L/s4MtHKGTL3b4/C31Htbgn2g4v95ARU6KnZzPBU4yjz5nny/0VA77+8LUbeEj8pR"
    "J+db64q+i4W8u9PdMO1F371TZQYJ39xSBmoPV7yCie7rYTdTe9Wy+zrU7kqNuq3G7T6iyfkTh9BDCumQtPrgCEmrd44QSPjmCAVq"
    "Dx+hYKL7I3Qz9btHCDT83SMUkvb2CAUSv/4HNsyim9iKYoSg68EbKlZsJ4TTq2qK6pwqzD12IfDTvr89j/38ci1e4Ykp/hn74j1I"
    "lT1H2Kp7NcZ4+kPlirgQ5Cfwcv3KgUmAyW3EhC9BQY4Ku4Y/iH3xzyvVkudLeC8WPMOWQWqhcEE7VpL8GcAw+zJIK28GCUZ4mL/+"
    "eI1B5W7uZ3Bo7cNM4fvkvIUJ4MoyD6414AO0/c0DLDuH9rytY9ItsLpQdCx5loVPfy6dYmj0nvGpDDIGLkSZ1c7PGKcLnZmCreMO"
    "vDWE55/Iq9T+ZvvqfSZfY9DZ3oLHstKgspwExGtsyUr6nRTkq3vl9HYtzkXROw2xTwisJB1ztxA0J4UF44Gv3eEkFjZMWBLkU4VT"
    "fcfJuouNwBk/wpIPLI8QlNxKFkjlv7h2r3on5Z1Er9gk22XgMB5EPgRE5adnfiA8i9gflrnCjs+GXr6+vro3zCkGzvUv/7WA1cfX"
    "gqQKmv7p8ZOFBvjFvs9NMd8wPuDgvFsoEpxFuIi5E9HA+gSdyjTIxXDeoDfzlzBQbww3+BrmNSIEyvRXh/CKdMCDHKrlm5UGvP9s"
    "/4ZyylBgES92G56dCmOoz68OCTb4kr1d+4Pxrc1AlD4RNOTFGtonMBZgtwEjQAqacUYZ7HkUE2RzJ1iYI5+JmIWlZDrPEP0U/4b4"
    "tt+NH99AFrf6NuNK2w5sig21GHGJ/2BEPNQ0no3ofO6WgHJZYIOoa5+/zRXU6vmvX58FG9ZQsHALEWCil7b/mJuApg9Aun/HxDMU"
    "WhN3IjTp/4g4yMI2aCHY2QJhiGr8atWoeWq0a9O+GmtNOX5iQFVlTYPhiP7rvzwFf9qZuvHJPrv7pDrvLUyTuQ1UjSB8HfBJa2Lg"
    "aR7xjSLNePinz6DoEy3rT936U2EePOnh08+rNtbxFos1DHhw+8lQPukqFFXQ+v2IOBueVtpr4tN/1OVPSKGFKRfgA04RQ+lZiN3y"
    "yaKMbvV4zYI+sp++B+bKj4fIp51grBUedt1pZN0dWQvY0mZilyY2wS9WUgxO+fMVjKJFLTxcERxpIBd7JF3UfEhci8OD88piCe8b"
    "dGE5EkN52qwKmAv9HAjGHCMuLTVlB2p6Ru8p+3wVJIz/n4eX56H4qx6RDfAr94vM/EomIuAnELo7FeytrBL+iD8Zgg6hU19wf2wP"
    "O5cmaFB/hnOxcEXXz3ZUp++A/+y3c/zapp2v9W5NfbsmPxaPEPHS3JMeN/kn5FmrVuOfTgBlCAj0zQ2nvATcZg0VEdO+YZCfyFf5"
    "H8ZXORqNaN/lH2BCyg4gl4ZwMwvOGn+9vm+Zq0NECLEMz3NtkGXrdjr4u7B8+S3c5mffqj//AYqBDPH8M6htPTv++vagxODBd8g6"
    "xP/l1yRwuDHPK5D3CMF3n3/6U14hCgeK+oaBiqym172fUGT0Hb7hchU7KzQ9Rq5+d3JrigIlAXmBhWFS24excAYgJBELtw5Cizzb"
    "vyIwLCsy5Z8AlW37E0bvtzTkEPIFCHEDz+r11XKqRCN+Cy3bAYRzY7h99gGseWM9hOjhYW9tHx8fkloMA71aauZLWD+sl65C6SUD"
    "RvF0dck7aR1QLH/p8m3o5M8oPA8OZg7jqsgv3x2gYhoCFccscFOU4Efk2fv0Naw2G/QryLOfSR/meei0i4XljNhg6e8bAg/QuhYT"
    "MPhh4GUo+roAp47tYnM1BXFiLDwEF0Dgir1i8ldvDkvMgDqB6HvA3AQvQCHooQiGFnAC7xnWSiWjGkIm4NUktUIOihbcx0PwlV/e"
    "fAslrw+dHDnTd6B0vYF6985RcMvBWHygx/ARxrmwpno4YuZ/Y575YBuDU8CGR8STULBR89x5xNuhidCcheTnbwO/bW5CFYZKslv4"
    "hb8HTeiHiXNQ25ATzXOJAd9HLkqYbXpwMbYCU+4KesuDNlZzQMPsy3jYPcst9Ba2mwOYFgrz5oNL813HszHQfsSGPqizsffJ3bpV"
    "b4GD2WBeCBrM8i+6Bcx1jb/l+Djb/s02LpfjA+cYdFjXoBNGX+hUH+BFF+bkyp/eA3TivcSPLklbd6Jd8C3kdyh6QHZsZB3rGqzr"
    "xeS7jWRl8KPruJfMPXg6ttcqDs4GZzLrzmqHzd3ueyB37oJjhcFshaBhvR8G5yZQ1v8usCisrdzFirLSYKA39DvckzPIvXjU3bsG"
    "NebmJUXIMyETAL12+D/IlqF3CFxTXiSsSc7H8FK9vtQ29sYV0/lVxKupFriwLeIbF5Zgt+sK8Vd3KngJIpH4LxeI+OLHVef8oDHe"
    "ft3D2bjugF2/Hu7b/3fX73HJRW6zY8b6O8R/R0zkteC40VYtN9om8w2V8Szu2JUQPwoL9euC1YVMKjbcStW+OatSVGHSHzZ6I4lK"
    "jSmFAv/04H/oYxn92xueeoNuewFe9QtyXImTxiR1iC9NtdDKr8rJxbZ36g8uYq9bWVUpYsz0jp3DfjAV2WpDGa+FfKM11XdDbc1J"
    "5W6J6SvN+rAdHzSVQU+fbSj1aA6o3YVqF3NtZTCc7rdqedsqMPy5wRq7XIIct3PxZJ0ntcUwd+hka+nUvl7kSvF8PB6Pgv+mmeV4"
    "uUwvzFYtuorHR7NkktPHFY1YsMVNa7zkcvRYMYlKVWhJI/64WDI5Msou4sfdsrrbZ3vJ+GSS7gxqnXgini2xFe5gCH2qPKuLxQXb"
    "Xi/NxLDc3zepM1XsMyPCLBc3clRsHk/lYqmbn+2jY7LVKksr6mJWuFFUbtWk1KEmGekdKTe51pHfVts7cTzOrZP0WD/peqVREBqU"
    "dFIyyW1HE8XFZBrfSfXijM/11uKkWdb5rkFqrWx7VG0vC4tC5bxWyiXGJFkhQUZPyU1XSplHPjU7qY3ZITsZHo8KLfb71W4LkFis"
    "k5p23LeK2YFUHFH91LE12ZRGkx5Nq4PCkqok2lyHP9XH6UpbInjNyHeGYrdyFJj6Re7uqjTNcZTUny0rmkEYGXFJDjg2fiGTca2p"
    "Mm35rOxz691ptzDlUy2ZN7InghM2Wo+LLpf5ZZwzctXhZZEkcw15t4sLJSY1rQrRTGJyaI4WyU6LAM3qsNzCkFfxfJ7g5JW6KHWb"
    "Z5belIjWuFlWcjlNTciJ7WynHM+DDZfoGNJ4aDaHp5yuHPJlslwt9rXW8FjN5A6XU01fHXdyM30BrJlPt1b59qnXmIrT7olJpmWR"
    "L+zardmYH14qq32vw9aSeml8JGZt3TQ39d5Mb/QKCa7VWstkV+lTmT67lnrmaEI31utjcX0ujA9nXpWYTluI7hPRTakpj/cDopbJ"
    "kwc5I7SMfU2cTlfrodlrLZqLy7jAyk3lQFOnWpdraYVGPN4eFAZTjSlNhkKqd2YuPXqlt5u80qgl8nF2uifSy3OrWSo2eb0lptLd"
    "2YQ+D5k0z6wKaldjjmdmdVocq+fasGr2uxXzcFkVL7VkMSPM2seakZtSiWm83zokq2ejz4658q5ODXML0IXpIksW19LK3Pe3x9R6"
    "0yLoilJtFGfx/aF/1GmV6JbZ1VQ2lca03hhsWn2jnKgsEsfmZrwulnOtUZFiTmQtRTWK+Vp3Mm1xlUyVLWZmY07MNZluf7I+JrKE"
    "kmm39z0lJxVnC/7AKrliOb45rAb7ajNnbod1rqSu1RqnLJbUqb5Qey0lv1HV2bTeKq2T0VnePM4K4jTVao1S/dpq1VOH1OlQaUyb"
    "jVK03lqUDtxht91O9zI95ZYU2aarGzJLD1OtZcoozjbRvTDb1PXOAgyIJI6qJ749NYWNyCdBE2orVhuZ6fNyI+3ZRm6xn0qcmlnM"
    "ko3q8jJLC5NMqz3cTVqbdWrJEAWmnM40LkJjsDVZqpi7rEbV5Lna54uFdW5S4UWmMpvuy/Iml8o1pp1mwlzT6W5t3By2ycoxlSAK"
    "nXhnVRqsDtGOKEv5bU5v6e1BRtJStUb1kphI+8JAXmvVdFbpL+K81jjQiyRz7q7Tm3abTqXX8WNhWmiVLt1yeblXhuvC4dRZEefm"
    "mibSGSHBpy+N0jTXHMoNfpZslcblXa65hcxS3Tdn8bFRHc6Mk1QxJzlymN8eqUZ9PZG722njNKO0bc/U6E20SETpQapAaYuUlN7o"
    "XD66nZZmU4bWeuR5N2RWTYaeLIRxd7Ehi8lZWqr2Smpq1KCXo06jvYzK3UHOONYah3h2uxvLZqWkcCttlU728hu2dKnuJudMOtqZ"
    "Aa5WqGJbZrqD7mJSH9UAh/UuYirV6qX7JWoWr6WTg0KKbp+G3cqOZcqJYXNSPXfqkjHNAP6rVMRtWU3HGwzdmdJbeldprkuzmqIn"
    "Ngq1SNFMokBwpWGRJmeFpql0OmNuuRHqNLEfrVrtWvlAtneDppw/T6b5VXa4apSZQvMg7YXakDV7dJsYUfuTdDgnjF5hdEymTmJ8"
    "2JzVM7QwoIpRmQLlLVSTbLOz+q4oNkdEdNYW2cQpL586mVWxnuPrFZY3y70mtzCH9Gqg9DLRji5QtWavoizUXFo8K0y2JKXy9cMq"
    "DVbO5ZTbl1P8STqd2Fl3Vz6K58KOXs3IVKcvk8OjIBLxrJyhupvaqVbqtnSqPlktS9vTucKtVYnShsUO3ejnOFnqNYzmcKFWB83m"
    "YlIBvWH3VC+TES+VdbXRbgidRbGRWQ+U2npSqadUdXFKJhpgOk6OHNnQ8414mexJzSNfiA7Xs91AIdp9EcyDdbnIU2OqmpAXcWna"
    "IpnogCPOBqmedro0OBTb9IwmBrOxWSwYx8PouDYy/eZ6VpwUM/kK3yvR6VFXm57zLXVcHFWWUgII2ajZ1/rsfnTs5zmylx4Q0U2T"
    "6C6L9epoOj5396PpgZgN15lKymhV5OYYzJAUqxRGUVNb58fZameiVXM1Um9q5Ga61KbMSJ8M2spRlcnNKDOhmstJJ66W95XtrK7O"
    "MhlK6fOU0Tsw9fZS6nezFVKfCeuL1m/qcoovdJb05Lg3q8e60uvyzbXcljZVYzbIJpdDJdFaZxbsejSkycGKopPCaH0SqFEuo4ps"
    "+XIpTtXeMcXtC2ujfhwYVWnROnaYXUZtLJRx+cyyYnrYz0iDozkpHyipuVpUirq57TS7I6Z7jiYpwBtUfLIYzyaUeDmDIers2aEu"
    "pzdj6dimKmIuXyqzWqrXzW2G1CpRJVaJzaY5aq2JTWGzHY5Wcl6fqszhuI4ya5KUtq3dOSUWEs3eoNreygV9KxTqo3Zlqafo/mBN"
    "mI1hbsMpVHyfLxQqLTqz2yYGxfq4KqhUNJWOV3ps7RxP8pNJeVkdpPVTcthemHSrk0uUdHUaradBaTs1yR/jWk+ZtqZiaR2dFSqT"
    "0qTG8cp0vy8vxWhyua7lpHZumZmmx0NqkO91GzJfNDaGcim34sqi0qoRrVRzJO1aUabIZ+n9qjDZ5Rur+lKu9CrGZtWvtsn2hm4r"
    "u0y3PeTr0io3luhO7ljdrxitVpZ1lhpKR7oX3cqb2pgsFY+HZbleGHOCegSsVhEKJSFaoCZUKnvc6t1efk8VD7uyvMrMVk2l3TF6"
    "mVydGqV2PeY4HuklvT5r6sM+P6LqJ72hS7sCUY7uiookds7FhbbjDKIabSZmg0wXfBjU49tqr8PtKFZttjvrNUE3uK7YnlHt/obt"
    "V2pCZ5UcGNl9r3eZ5YyEUOjTkmymToNhmkhxdGE/WNBTZcBvJ9LqWO2kG8NDn1hVsketMSlr6WVtMY1niEZlvO2IBHnKjZURXTBL"
    "hJTPnbq9pjxoN5vKhu6ld8kG04jqZKVbXQhGcVDMDLrldD6TrFdqxEqUlsfiVK9ShXRXbtfJ/DGb0ws5lStXSkSCokvcRSwn8znj"
    "1Fm3jGqvUK8vxAGXu+ylMXtMFgVuMzyXWvLoLFKteEU9txutwm6s1nJaapaNq8RYGjfXybKZriWV9jDfznPbfZ+uqfn8uHRU+lxu"
    "PN11EmPiWCw2SLJcOLSSqTrQamf61jyqJH9qFTWeEBMCWTkVFocRJ9YLKtgSmJ1ESz1Uy4PSoNWtNbrJTadBrVeN+NkU8vXioWP2"
    "t2VFLPXTIpcwTWnbK5LpOCNcBHK3KwxL1IgrUGu60yBUhZqpZ75Q71CFQrbGx2tgz7Dqt3jCrMcB/VWiuj0duXZd72+Efma70jbx"
    "/WDSHgLNoMy04rn9MVXOADrV19XouNCuFFTzMuDU3Emrb8v90uioptP8RE6c6eKydRrzZ2Z52CaXBS5FF/u00ZX4fLMdTQDadMlD"
    "MqtcCvEOvwQj1EkW1eFgvGTTVC5eqhij9rhOTAWhkkykOws6q9aNwbBtjKhDqcLvEhV6GN1km61iot1XTnlTjlPDclsC68r20OHG"
    "QDfpTLf0Vtin+P6w3KpW6sPquZksRgmlmhgXhxmiT6vpU6NLb/Kd1WbVziVy6VZFbTJx/tBqZY/cLn3KCcvtaFPvqGdxpY/Os4vY"
    "KRaK0phcLqvNwfqQLWh5VtyKp9wlRyqUOJXWs1qxUTtztd2wPiyT6Wml2alTu8r+OD1kE50VJ7VS9TQ5yW6NxrY81baHAkMfSJMa"
    "Kyl+MDrz+q5IdOO70bLZOPf2h5y8zrc5frviWaLfGI7lY5WGa6+pEo1DmT7T7bg46mfGs2Q9q2U6LV2kclyROXN9BeiWRbWTrsjD"
    "RlqeSOnlgBmc1rzQ70+2GQLoZpLQaW5r6QlYUWpapq5uq9PULi8I48mOHQh1Ks10e/UhNVIzpVq/3SO0ZUVubBPMmTHkXiOVUFO7"
    "qboiy9pi3Ni3RlWyo9WXx925X8/0OmDqG+MdNzNaqdYgm8qNUzXjkE9H0zNzmVg0FDVKxlM7xQCaGl86RFcCyWYuB8NIjrKni77L"
    "cocEHWeMcSJhdEgVfEhk4tzS6GjnSqLOZpbTVqOqpZN6fJLJkvtkfZNh1HSd6amN9tgEKy01iTKVdH0rSrLcpwQtrreFVS9lLLKn"
    "WScps+yUOhzGnXq/lsucDJpMElV60OrlZ1kqqi+YS214PMRHy2WvpVWJjkCxmrpMJBuVYuk4Ic+5nF5ix6dM/CQs88aM3Z32i50k"
    "mhl1sa1Uz5k1qZCdRFM8FWfGQtN6q/qGTU7as12SZ6ZEnekkOutzFTDRQrukBqe2aGz62qSTqTMDstHZ8OIwf6kWtv38YGwa1bTe"
    "212GiU6JXZOH/WSQWS3Am1N/bOiLNrXrd5ipsoHfF5XFQsr1F7yizQxSTKTZpHJWxllmfFmIOV0oT2oL4VTslxfgfw29X12MxVSy"
    "c26I5cs0wdZA3ZeF1tj2QbnFXXrNGjDNTjpkgBLFl7TWmN4NVVU31dqqM+ky6e6FACxSTnXz7CnTvADxTBbzF7Us9eoFJp/UCtyp"
    "lquoebgMVTOTYnrCsutyhwYiCChyo63AnSanuqRT8mnQPTRaJfUcXx46OkPW8lx8MDoKFUHoZRdEvEbIy0TWqK7X0c5SFfd0fLzu"
    "xxOVzXpca+6ntfVhUFxlx8mTyU/29Z6cAexY6mTi+XpSmE4JeZMga2x3Xa23t+PhmU4y8aQ64chtc8hdgMA6ncGH9lgem51zr37O"
    "mXKLqqc6s1FHjw9SVamkr4urqNAkSCEzZXPUcpvJy5SyX2Xb7Wo1TpkC0FLYejqv8d1xu5ii0sncge9zzeWZk5VtT+k29GLrXKcW"
    "7UnlYNLCcNRMJo1sYb0ZxQsUWA+z+UtFHOUnpaNcODfbq/K6vDkpRY2+nDa9Y3nAmZWhygid/lLIpIVlOl8g2pcRt7q0iOiozo6W"
    "tfqGOk2F7L6xKZ/3OaFQHO5rh0unwkVzuW2ZOO7Pxn44nU5z/Yoc54zVMVotdiq6zrJa+UyJberUSUUrRZYqHQ6tXpmpbOsdc9CQ"
    "wI4jt2vs41uCTDBUZVFaL+vkSlp1SqcMP40XtHSLyZ2PhXiBXWbXvURylBZ7Ok2MFzx/0vjDipKMfB+oR6esJmfL05R5MlPaNhOd"
    "ZHNJ/jChueF2cVxNyd76IG5H2e2ApFZ0Sx3sssl6oRPdM5NlzRRm7LhYPOYOecU885TC1rfLqb4y08b4wo2mWqZWbYmasjzwdYWu"
    "LI5r0dyuDn12vc6vyUxJqK/zuwxZz7aloz6oGUeu0l30KLCbHHIlcVEt9itkehZPrrUC3W0qpiQw6qy/P++57I6jDytuW9+kDilh"
    "EqXbfXkdX/AJs5dK1oaEvOvz2eoxLlWVPhBk0+RxmbiUu8Q+JZTkTrFRXDW4y3ApZfv7ESW0AEHjRnPT3ja28ehxRhiLXS3J9fKF"
    "Y31bEbjlkm6vDrXDZjRQ0qdzulbeJkrtKtPRunQpY65XYJu9zGaS1OKSSFT3Y2HVqu9LpXhqxvItBaiko6ZIdhNUBawR64a+PKbb"
    "qU30IrCD5eZSSE/Hq1aHWPKtVueo6mWDMhtydqqPN/1T98QtVXXCzCbD036fq2250qWsVrN0mp6Maq0JkWpXiPpelJfr6bgw2a7H"
    "yX2r0Reqm/0yER2ZvSapyhyt7CizrEV7vU6PB2vRnou2T+M4Xcu2NmZn3djs2hV2PKgee7sOcR5x3D5HVg7rBjUdcHy7szJ2i9pQ"
    "O3KT/XHR1pVzfXYk010uMaZOiXF51biM5AybJrbmdAcWq3i3k+G20wFNxNs6NVCNAZ1LDhOloUxe0qVGO85vFOkElsd9P1qXaplW"
    "a0ZcygdZKo4KXUZpc3JlWIhrQ2MnnKJDqphLzGbN/mxd2J8rlcyAKYGuNShpwFZ1Vj4Tu3NUXbHLy5jZ11PnCl/ftbOySB6PE+ZU"
    "Vje8Ip1l9SJ1h+JBHFUuhVPdqLU5qV5clkRGyo57w0V2s6kWV1PB2M8qC2N7OnQuglo2mAV3yR+3CrXLzHLT43ha3ZfBotQYFcmB"
    "0Nr3G+VSQe+uDut9Lnnam4RKST16k+huU0a70s8nToaeUldazihxjdllWcowDbFVavfEJSX3DlSqm84sc/JWZRJ5oQb257lxM9er"
    "H9UcobJ1I0FU6K264TZat1M7dodgfwHGd2XERb7EtCVqt1lzxnlNlGe5KjQnXTKppd6eakKhI/b5syClpRUVZVb5Q3s6qTbVKb9h"
    "CiSYDbM1pV34hLAvtpdRsD/j+H6dGKelosIQ+c3hsF33k+fF5EgkosparKW7rWy9kqt1m2NRK5Ryw7KRPY3OB1PsFvlStpFemGKn"
    "35GjdaB+NXPrbV+ZssaqMu0cp4oy6m32RM7MxWe9/DndNGeN1n58zJSiRbILdgncZCWvNnpHpzJg31Lr9VdRoG4JG6lT27WFeqo7"
    "04hDQ9o0mqRA7dajtVYqxEel2mZ3lMXNpaLlV8U+uS22V6dRa2T06WENBiHPrciBXljrh8QaLJj1fK7H10Zsvrwbdyh2sG4clkN5"
    "QQ+Wp+FuVeCLS0pva6P9oVw8su3WYDPsN1cncbrpyE2u1isZJCeOmkSd6KQKolLuFs47YV0pzirlGbfdMbNoaqwxu9Smu5iuCxJb"
    "reRyo9WltG300stZmlzU1KY+HrV2jdFKYuLj5qpZTqvqPm6cCuU1UR2ysyJFV4YaldBGqc5RWImzPqsQueXOkIbV+LbcKSfZSx0I"
    "5EUSLJizvbnZt2qzM3ESy+fT+CTkL/v8cZo6cMqo3io0iVQ5r1/6GaZQqynxPrOdxZl9oTTOrE7aWW8TnLTqJ4mFkuxyg+iI12ap"
    "lEnIxXRdAzvHTkGY7OPjdlOgW3zluBvUuy2+lG6dB/vxftI/FtWilssA7VqfTGtAx9OVDV/LLnfiISexfDraOpXK0zFdWS3O1PbM"
    "DnZGRWyzw1y2OlWrwgLoy5XCUW10WKFfoypdrXc6qGSvpCSlstEr7zfjvGSW2tRe3k17/XONVfTRdKL1t+1dvG5uKC23T0vbafei"
    "FVej06VU2i75bVJJ7oUW0ZSFUbsVj0vN4TQ7oBUj3m/vGTGRPaTKehII1XynvlkVRs1jtZ0WorNh7qQ3uep52xzRzVx5qeS70qnK"
    "N8oZSutNjEx+TSmFWVoq544LRThHh2extI3rhWOmoi+1nbZKi3S1nWjvV4NFqd6qdlhCFle9syTT6amxFy89Njmc7ERpq62W/VpB"
    "y3Xaas+sFYt1oTgyT02wnV3lK21tsT3XpTapXpYbpdHKthR6W9rrZb6bOSeLlRWd20/o4Wl2IIV9dZM6cnVCJel6n4pXi6PVWmjU"
    "qvHMOL6sr0vns3mWUjO6nKJnzXV132KyJX170Vb5wUysF3cCVZu0s8quVhOBkG91Lo08UTanya1YptIzPleZjYtMr0+d4tNpRmmb"
    "PNWp1QeNtjkdjKF5uCh3FxLdaq6K6kpvyLVWT9/Xa8VxYzIWSrMTOZj1s9Mpx1zOJN05RxPpUkqjkvmWOJsMCvVtIbsVN/l+V4hK"
    "OSnbjoPV99hqzs792qrSBttxtdCJy6JyUlfxUneQqxTq5UW7Npi1KtvTLG+MEoLRiG5Is94QiNmlwIp1jmkf2PNomiYkMU2QlWSN"
    "2k7JTGO87CfWm35tJl7Aht/MQft4U9EXCzlVKSrF9aHYP6azq+a0Vk8OGDW+quz7TUlKHDK1cby8FSfT4kQ8F4WxxFDJanWgVcqj"
    "4bQwWpwHtcIlPehos8ZGPa70RDPeXdOpdHMn0oVicaG0lPi6u9XPQKCNa1U53iiA9b5BsCKtg8HmzGOrLVwaDWaRlwY8pS6mBTGe"
    "Kp7H1ErK9Kd5arpdHePZAbcXTjueLG3k8ypaLdR3rcm4lSJKUXqljHe9osjGG0U53qby5xY/nO7Z6mzNDcg6wRHEuTiNZ4a7wVIB"
    "CnCqd2xHVTqd7pvnzWhJjRrJxXG6TalAz+9Gs7rJbLKp4VmuEvEBd1D3qz1Pk/vBgiG2uW2hnTcVpkCk13R3XJxOGTq9ETNV49Ki"
    "G0BhSqeXDTCZzObaIAghc+GSqZmaZU6paaK8TgmXvTLbV6uLcpU7kfmBmEstme54SBeGJ1rpCoXGOjtK7xNMu5nWy/pYaGWYXDGa"
    "q7HDDCltlT7Nku0mndpzmZG4zfPjWoneblvLizjhOvFRoy31i9n2JdfggFrWp8VToSGRBn3uNOttOTeROaY5XQ6GYk087VvZ6kkv"
    "tneUkGT75qlDX2b7yyTdIhoddZ3raGX6aJY6nU5h0CfTvdO2Uae75pqqF+QuyeyaWj7ZKHdrirzJi9HGskiu0kyiZEwn3ctGWhrL"
    "aL7aY7mleahtqMaJUNPN7YjKpbhGmdIEmVhtOhpQLghKGdMrUkqJM37VnXZ4KUqXcuSClEu547CqXbhBv945StyGPqfbXMpIRweZ"
    "gnI5pcVlfr+eDs0teQbLdafXarPKrK8skuqstewOozMDaKEds2aq+cYQ6GmD1Y5mLnq7NCqImnm5LI12tL9MDKbige6O0n05YS5n"
    "Y+3I6MuTua5UDZ3tbGdH2ewXT4Vkc9hfZutTklfYbjaRLdSWxmld15Nq2mjWabBHru+m0XOcZrJ5dpji6OVSzU8T+fUmYWajmeiu"
    "pzQMuqCyB6Z62PSz3B7sAJY54sBcmuWmJMiVbHQwiC53s/Rs2j6ocbrfTlblfIbrttYi0K9GGuhAPkdVmSJDTrPZzvpIc+dy4TIj"
    "kzu6lldTit7sqcXVWk9XCgNalnNyI71rmOVWe7oX2VRyzSrdZfq0GI0Vsyp2KtVCNp5bpy77NDWo5OMm0+VGaqsSpZqG2TydpEpu"
    "ManuR41oZWi2FXWwBtpKWzwe1fNqk+8O5VS3RZjb7qxRXgszrVaqpBqTWYk4DdhSJ52eEsVtklHXVfLQb4pEtHTqpLvHItubnoUa"
    "kTix/bQxrU3i8nbXjJ/MBt1g6H0e6FRlNicuesd4K4e+q1RuSIxzGzHbgPvHSpcCUi1ONYdZGqgu+W2V0+W8MCluFHHIgm1s41wt"
    "X6RseiLrqdEQzIN8vbWOlrLUoZFLm/1zNX6KDgx6t+ZnQMeZCIPU4lCq13oNJc6UMvUuly9I+rq/1dZNeatEu7WEFJeAajja6908"
    "15cGo0Q+DrY7CUPLN3YXnomDnQNPakymNRbpfS2dA12LCvvMYTQ7VfokyUzIRrKkZyeZTWcm68uM1GnWlkuDkXOjE9/iF8khk95E"
    "+bquphfjUZNuj6VDa89P2eHIGLKEoTGjym4xljrGYsyx+4QRrQw2p8KeVBfj3bkiJPJDsDZ19Si1VJdjKTUpVork4VBNDKlSPKqz"
    "2c2gMc2c1EPxOFYUU8/H5fFyD/7NHMYd8jgsks3T4VAkhkoNsGzyfClWT/w00VygM5lloaSPyerpMCFLTWUj5S9lvV2hTlV6w1eI"
    "DRD0251STcxoQxjqRI00zrmemYhX0nJiVluZXE+JZzi+lqjHU2DXNDmVUu36YbpL5rudw0Kp8UL8TG97bcXMVmUjW6YXZF4EO0NS"
    "L0fJupQ15UMWqFzt/G5n8IvioR/n99q0W1+OVK1PHcXMYZMa0sKmdJiCffPeKI8q2ma6mp5aGWFhEOD/8Vo2X82MEgc+yY6yUbKg"
    "bRg1usmz+Wq7F9Umw140Pa3pw7xGdkh+fFgS+X1pDP4mppPSiu5HObpyzhHCYbU+TsXuQqsXZtntLLExznzB5KG5SFhX+dKO4Xcb"
    "g6SyxqZu1jNlUHU5a/T2BKkYUzY5XZlka82xGaJfXkzGu06x09on+1mwwy3zhEkWlD4xBX/bh36Nj1bEirKp7/adTI0FUygJJFui"
    "vi9U+o3UTqmNlGx7ke6W15U+mxxsmmB93hdIlk3w3PpE82JhGx9usqXEkGWNfJFY9dfbPLGspoepzHhsTi6TboFXhEKmVpXYKc1w"
    "Zo7KtcBWcqZk88fJEbBxfTVdqyWRE+nMucNNS42UNp5wU/lU65BlaW1OZ9tDodwcVA9prbpbGclDfTJUjGH1tG1veXXW6YnKUa/v"
    "9OOyUC5WWpkjobfB3lnsTQ7HU6m3/f+Ie9Nmx40kQfD7/Ap1W9uMZJQSxA2oVtsD4iAAAiQuEkdb2STu+75RU/99wXcpJaWkqtq1"
    "nWdpSUaEh4eHh58R+dLV5cwHi5hJphsy9+s6SDdqd5oi4DuwsKg6Jdh4WqeL2CvHtAqpM0XOeFEfZMc2BCMMeLXjzrQYAMoEDbsv"
    "yKUHdg+u9u6eUnNZATO086USUndyDzzUKaBqHmDHuR3pUxdgt3m6dIcCGappgHRjQqrorAQoTmbnPVRGAYAENoCm5pN5Z+IYpmuK"
    "4uiEEo+nS06dVIo92PqqaamaThhbcmfII6hZtLeuBs3z+DjqFsVsIoAwhB7NGzIz3rS72lgjGeAC5CcY7ifgrCBVtRLLQYVHSw+m"
    "e1gTaATjJAnIPEpFKnPEIngDKQW8AeYEIpG1obGCLkA1QS2JwMcagKt9GBOBcAIaSKnw7jBfDztugAwZclYSE2jhwwJ4HcIAkAEQ"
    "cE+F8WmeADIFGIsUJ4kHRKBI0OlgWeiA94fZyWCcISAeGYE6QpjjgBNACbQcUEykD8CHgwshJDXNVxSOYKtyyGayeYKIaKQWorY7"
    "hqRoQBymoNBK9oqwR41t49zd6KvfMip1lZxdz71nhwx6rlZRKFDP8aWMMdC+EYjzVjuP9UgmhUzWPDMeGhXFmShJKDOBlOMMB2dQ"
    "zipRT1AVnjjnZntOTCAx2JKqFdxdwSblAxBFh4QIiw2Ay+jmyOAZV8h0g03QFQ84X5iQA9YyYkV+OgiwGI2bipEubcw6fQJxVgzV"
    "mj3Qus9T4iBIK8hAYlctZnceSSD16UldaQdM4D4tUdaPuWyr5UP1qM76hGh+PETlrR0RiCp43FG5kQ7unn3GrrcQcOysAFPneKQu"
    "dHaMJYFPGjEw6BIVtcGg74I3RaBxFK6CEO6G7hyOcIykhsrJmEVyLVsWUxqoS0JfTdZBJqONIjSBlgOFGW2TabcsiSl2YxFLOzL+"
    "coXqPnIyZKCFarhUKlLj/bY1M9j19y6wpdjhIM1ro/RKCMI1MODDCXiwmr22ew5a+SeDSu9gx1xtxWkabze/xKheAhZnvABWeT/q"
    "x3OhgTE8dzSBY/aFLuzwpog3ZgY0XqEF+mio7S6wiHOP81kW0b7k5auvkETWIxykerkNJBqolbuAWzOkwdEaVjruHjdJvRJ4rTUw"
    "Gq0tvKwcdpE6KGP7guipWhEst+xmqtVEABPQbj6L+UaOh2kjZkuT0wfNGlA75TMVAImaislF7jppj6O867oHzkCcrmt8HLcyBSrL"
    "v/sP4qGXq7rj5ZtbC18rM3MuQXJs8GZGeZHBLeh87Dxl09zzPdA90xi2wXZOdqcVtk1GYHleLusDukUp1XePHgeAwI3imqzHhd5m"
    "jZO562PIiwuPhGe2CHV4V15w6qEApqTnC9ylcbMLrtuHOWvnwWTQw+4b8ouNBsliumvj9rtuc0dE9q/oVl0Vj2wUDpX0YU8naa6u"
    "b8yJFAChd7B7/zCVMTmHD7vnqslSVBN71NLVoocJQ7p4qkkzjmyfkCnPn64Ok2U3rz3JOY2jxsHkuNrKZkQmZvZSO7tJVU4H9qr2"
    "PmbCj7Hs8ox+yHv4PshEy/RCNx8proecEFc2V+4dU5kWaa7RICjU4s44gFrbTJT7igp6Mqry0lLKFKywLnDu4BLQBsHbWiTmzwFP"
    "mizqUuGN4MYmXLVTXlX7wfjaVPQziKZFU5wIFz2ehAseERl0YWPTB6RxE8wouBUV4hkCjlsGZ/Nwpp2k6Q65xkNe3Yc2EqgU0sWG"
    "Df1W8mf5cbuJFusnzkqiyTYSRFlfGYIjt2hWaZjkJ4bSEsYy+katlNZmJ/Zmq3u0xuCDEDNW6eWlh4L3rEtUH9lVNLoaBGGRRPSo"
    "H2J1u7V7BLqHfwYooTxKnvPbAndnLvfMDncCNoFZ8lxcveRxSCYcEy5beAuni19XmnVSY5lVsenA39Ihd0cJBjdevUdn3rZBneHN"
    "AMCt49VTx2pAbdc3YvDES6cOCkxymk5kgJRtUWgNkepi2BYZQjEHwEQF6hc/l5K3zUosAUzRBC2hKkzeAy8apy7+yrNDLDhDly5W"
    "ePAqXWBWe/RbVWP5G3oc3UVRZvpEI1rkiY8XbIGaoN1FHu3EM5aRdlwv6XjKFvTiLBLtQ2uJx5Xxhj3/NPVFlAa88RNRnHah5jzU"
    "NVlG2QUqa2DJhC7rSSJL/Mq4krKHfrhtWAlfQ54todf2gLoNVPhU7UpHHXMst9K5RQOUmmACivXbmEHoPRDUanKxvcJHzuwjIYCb"
    "PxS5gp0Oj7sz2EyRaLLQyuYKIZxnUUm1TsQDugAV2KxgVF6QETE5Eu68GZQ8G1X1tCM9Q4Hi5nqfSLzBGFOd9fpcTSY/9WrtaoAF"
    "6JtYdMiZRjp4OOkFXzW7wYJQ7Wogq+0dToV0pD2eT3iSbGRJ6Qt3dleBjYLLuQMyswcyxCJSpqEUnW0oNTsmWqcwypEywlq/o/Vp"
    "gIwH4/EdCy9p2a6lyytBDGaPpVbE7gRXsRZMQTwdzip9KS2KtfP80NrVzDKXR3tX4zp2HKxjGgImABaWHWAaBh9ioFS5WoU+PALV"
    "9pdq52R1Pd4f5Z4hhD5spSWvURzHMrIaHWN3s6+ZJ9RIERIg1on2ml/HCw3TXnsgS2dEUflez6nW0tE64BsYiewy8j2K77HmQTpW"
    "EgUCZgturcYAKXBuNVqg4GOFZ0lEqoMWTqMUUrmLwasOMzjdzpRYNlV65pl9su+AmJo5R5ZL5Z7w2bXIh9J2rhhB3DXYkbrw0glV"
    "fzudkXZjGAeceKSPYFfXTfUELRfQA44cg9x6WRsOFrViquzE5iFgXa9T1tDu4pOMmWSJcdIo+seG1xF7mR2Lu9zJ3XIz19U7gUXU"
    "H9nKRxmTU2Xf6LGDwIbKRbZ3j5WmKhR1WR8BJOrWtV9U0GwTpz1PCrcMS5DjnOU5jqDhUb2L/vU6MtAtfIQxHdurRioNiTPZzU6J"
    "6rRBmD64CrOxIQYhJzzKHE/XdWLE4WS7JndtxGb1AhaqNnaqJMLYAs4Ed4Nx6w6XvniylLnq74Fw7oc8bvwULiL3GEnA1KXSdBbI"
    "GbvXnIFBYRKHByYgrblCH7mgwc1EbAUNnbBhUXu+7DtX90lRW7cxEgU0msLihiunYE1x8k5Xt9zBBfPBX6TTPFAz3NXeLjYwHfv5"
    "ha6Y+mLzU1FA4VAAWUnZAX9c+xueccXiClBlzLglS1fdAC7erbWPIdSNKLbIqO70ScyPJ43M3V5cmXN8ZzNYO8ZTfpgRIYgEwA1G"
    "iO4JnqgRDUQ6Y0Aa/qFI2NRRtwMaWlDCTbysxJZ/ae5rCwhRGjhXK0FZe2uK2Ygd7d7wCVCnjq9Rqp+WpIW7BHm9TJebMkwUyKCY"
    "xN2qMyo7UrIgFw6R9NUqt+shVqKwQEF9Q6kkVWo7Y+CLWAlRH1hubQn3oX/gVxtIQXEUGUY/t9mcHVV+cLEwzqbgWjAgTGnVJUlk"
    "XTo/YkYOwOIBYT0p3olWx8/CWRYdA64EAGfzicJ0SKHG3dlfu+Z2lzO/AS84tzIZyoC03KwQq25OTxanEz8dOjSsjvzgVPOZo/Sb"
    "E+Z2+jhhqxLfFVeF0HXry8K8wNrJOUduaYUKErXasXEp6JLN5F01UApjAP6hciGCuWdp9Ur++hBmmtP3gK9fDfcgIIdRPwVuhQM8"
    "JJOXQiuTM5eVlxryj9vRWaWgPC4ny7xwm1VMxAFejqmUidwFsLjk6tk8Pai4PhhXkJ8hkhcPPkKukS5cc/e222u5lgQCmbJ7CtJq"
    "qiuuUsbpne2O/LmS4iK9n9vcvINrvQr66DNsXuPHw0ST5x46a+TA0y56QtckiViWkXgIWTgdSi59v1SQ6LaRYMqPhR+p6yFVD4+q"
    "l6uD9ugONUOCqXds2wpqTjNjzOnkC3YtTkduStEcPke+KsfrxZN1gTyKiZRbKweKK+xVccKZRnqyiE5cxT4Fod4fi+MmICfbZwVj"
    "fFxSmsm3G0KNyBzWlA/sxoXbU1GE1VWnoGCL81daXluLj+HaKfM9BPTrQ+LrN1JobvnBmNtu1EQXW8cTxW10JBqjNmWHB5EEp3SS"
    "9d3ehbFAV0d4kkvF7lrYOnt+kevidKPF833SqtDUNhYuil0ZXPdqnwME1nO8nh07PV+9cQ70W6qZgSpox0Kz9Wg8j+7JZzcVGJyt"
    "2UOcm1r2gs7XW4hNMc6zYemjh/mGiDEY3e4lBZ6QJRdwKylyB15h/7xtwLYncyxzv1FGn19kMFQ2Rz3ZGzbdVb0GqAQe0Zt9tTOE"
    "uRZK4uZReje7MD1UqVSAQjfRZ2YTLN640QVhpJ3EW/3t0Euad+ZSDHYmdMTG830TBNWS9whJ1FMM8+bdj960SUlPIuMm3TEZ0j3a"
    "xHy1xmthu44W6VKzF5W0xUkC3LvwJsalDeFqK/tWYGTIsR0fh+s+kiWHTr0iLpB4xKnbAiVqVY89U4dzZeGzdYSzDT606J54ylS2"
    "W/wNRnQnn6+ADuikat5IExOxrrL6lZ3dkNaaBO66/hKcmxCYtcMA9MAM77qJhkrs2SynRrK4CaEvXsxba3SVUm6FtPjwASqKeUip"
    "B0I2FQyM+dWIC9ng9QResxzRW6SIVj1tne2kQp5uA6xRqnAN09Fmh7JOssL0/G0dAEbCXqWMtD52jwOUW7zpWGNT2zOPDnUM2lmg"
    "Ynot9J0KLtVJjATOxfxjf7OtmmJuRNGw/c1kaVd9rJJHyFNKH0Tacq1u993O4JlgdkLtrssvz9+qyrZjTbKaKFM5W+maaZm+lgk8"
    "4QLhPLkE7OyKXtryHREZ69gspw4vk3kYzNuMp8AB4C/rRi8uPMc39pRLZGEFHZDI/dGRZhM+MWmQEiAhLxf+wSK4ZyfDSZ5C5tTU"
    "6Vm9szBssLCrGhuYLrMwePzkG5CqsPPU9uyeogFAC3ub4dZhRaZC+jCrKJC2qvchLc8zYpf0I95UpXxqrW3SIES4lAyp9kd8sZUH"
    "c9oUKWWyo4KdS7ekHneOWAbMe9xgf0/ACxFcj3WDsOQo1DMPHYwC64dFFG9cOT8WIb238oETRst0CQ0UVIZy2zyDsgm/HAunKuDR"
    "hRPceGDTI3fqFGEvHCpMMRHDXMKmGrsG/tGVbyQBl5GzuTpFQHdOOxQr3SCGONBn8VFTu6nYfc8F6GO77RKvsMwQEcyTtCldHyWQ"
    "DmnopMOYh0TM1DEpdjcupFMRKIBNLWvx0Zo8osNwulHLPA3kVQVD+UpTirbWtaMYkk1MlgQ3t8dj6ljBhNyUvuKuI48TJlZLNqKX"
    "CO2Nh7J6COwE3MYnpWpUxbHHHue7njX3xiZ3844vZAn2F3Kxrgu7+XJTsA7K8BUvtcjxcm2zU8+odzQqPNf3eNXyYJkxww3wPfUE"
    "kBjIXsfjECHaAQ5iGaW3Hogik8PEHuOCe5oRcLFIJp2CyTAWQNMwZ+PKjnDLjTOzYhQTpGJmGew1JaOERQvQ0QrnYe8GF3PTfkat"
    "uRVZmTmolV1KYO3KOK55nVj2N+DeMAEKxZnZdCKM3qYYu15Q5dD6QpG6lcNm54vhRRjYNCpppqANPbQBO4C+fz5ISFp1N7sJPN1c"
    "sC6uDj6Dg2ssjXtiRyKEwaXLnp7NBcK0Vvi4MTevLlwYmG9D3B0DMvT3GAd0qj4/4TeZVs9LbhLdwJFX84o91EPWn/ucTF2GmXTu"
    "JMGx5mWWL98MsEi8xNVKN9JwD0jOM+2jYbZtGiM+aPY4n+hthl3zIY0sd7InuVGaqYs9TYWEBaYwZyM4sb2gJKCFFSKQZ/iAaYN3"
    "Hls+YRXf6ZetjqpWvhdDjbvpQWVR2Ovp4eFHWHyIwd1lQO2NKA+hicUsVkC+fR0SJ7vvCcR2bsR2xIY0tZWCJB+nca1kG9wj/Ifv"
    "oLZJ8JmfC0CzJMPW3R1JFDVuvaD8iixshNuNfqZMYgwfMplFx+vFTStAhurLmb6bTW9PVHRZbgTtUL6LX1ou8W7TSg4nlu6wI6Kl"
    "kKWeiZxnC2V06AYKFS8ojLIDEAreMx03NKpDzO8xkocekLyf2Uf8WIUjG/P5CBLmWRrLu+FcDjVq2vN4ZRAdqjaergT+wmcOTJvX"
    "qYk3iBV1LgcI/xwrshjC6aUlJjJgllGYgsmvA9MwAzlYiu5EWKR/PbWmQ/G3++xSFgAowGwrArmH9SearFDUwEir1zeMh0prfNDO"
    "TafrKfWPg73BGR9eCy9Abkq/kfQe6h4oLyMV1X1cKdzLb9OBdz0rBkg1IESU8R/9gHXyNJTGCekeUX5lWv7AqcgVm5LzyPsnTXtM"
    "06yRJ+PuMMYm+2Z8OmAzCeVifDU0ZWkzZEqnAK+7HAJBWDn0Y1kwRKBx4pmTuWJq14OygbHVIB7UCV62Peq8LO9ETMI5NjczYzdK"
    "2kuxMZGqFYoJebYatdKT/jIRiBLHbZhfZysFU5rIkiLlsFpjaw9OWuN8CeQNu7eWznIIFuU0JNroGnadqeb+w40AXKK1BFION1yl"
    "kryVig1e6qM/I9G0KQf8juUt29xqj50vCZQFSZ2l6XWV8rOBLD7WcLEguSfMz6Fubl21a3zTajcvE+HJ3rUirBSNjK57WI6nVbah"
    "u104gqht3A6BOTv0gBOKKRi07AuI68KckIB0x3eGJ3X3qDxF4KnWE5HVHRU2LJzQ3LI2WTbr7tXq1c4YIpMvBpq67JJszJMfnbFx"
    "jSz+EDTnQD94j4DiSTN87GGa5imEhQddo9APFLKEnANW5gqyU4wYZGklnH4u6c0MiRmIl+uUJ2IHl5SB76HrJtBBnvg+y07HSdzT"
    "4OsjUL1G2rda0pV9QkiAGluSCzfjXB/huhWPi25cOzW/6gsR2CEwxR1MHw2CdS4mSKV2fzGpNecq6SIxhFaB8uPhHa1NTvEh8Yfy"
    "0giRfZBWpIRnMtrcmt9T7IPIZevmgV4setJiAmHlbQ93ZuJCQ+73x6qIfE3y3jGE74bOH0GRY6dTr5qQETka5R7P+AIjabzQcUFV"
    "3KXOIjgkMRc4VpSfIsAe9gJ1ciYdrE3PoYNc0y7tfFcOdd3PkqC4KRV3SGhrXbY1Ne0IYIhrjUh7IizCHRnX+QEEtYOzaUFAlIt1"
    "7gKh2ZBJzmvYOzF0CT7W+UjSV41GJFLSipspLyq+lo+qWnR22XMcgiYPld7vfoy8qQnRHU3jwF0PgnMgjQN0nmVIpec+G6D24NOA"
    "ckFyfYZTXukNbnTABRzM3f8c2upWQjUzZailBec+bfmSP+3contOE8Hm2AsshD78M5C3Cqj4JFyxBFMtnYVVi0ZR2TGj3VxbApY6"
    "XgoVirj1cdsT2aYXTrgXgokdSGsvEfyjHYgAu6PEFLA3RnRSHLnqpnTPvTsWPTamzbcZLR4FeoglKJY9cjvZ0QEJ+iiD5POEUbl5"
    "IsogxewH1Q0GzkwnFuhUNhkioQ6QdSPIR75ZBHq6l5NwygtvmUheXkmtGeTgEUPzHqeRc3nBUecopmZ+YiBTrE2uE404tehxBO8H"
    "oWxahOYeojmlY289mElsAuPQ9mFVIlQJjKLtj0Au1fIDzQ3YdNZ+o7K7HYIjCaskBHKyw1rbFmtARE03Q29v6c2iYid3t4jxeqXX"
    "rkHDq9K9s4QO3XMw1kpm4n6NshvQs/6aKCVR26I0yEiyO5FKtQt8KFM1zj3XfkDC/Sz7l94P7kySUfNoXZSYnRxvnEbzUoxgMrVd"
    "tt69QDjfjhfH8w1RYxTMbdDHpbmBl8vhvCWNe6xnQyLFCEdNlSn9Ji0GrBy9ivROom5fJ+GM13dA2Vz+ikANlOoZgjH2FbxSKegG"
    "ahae6t0mKUBvrSW5W+VMJ849cU6zXFCneZ0q3XxsVq8ghLqcNU06r1o7iwWtpHrUFm207LmEVcx+QWZnW4pJ2+R6+bS46j0oD8yy"
    "TcYdLW4ukqkZxeuzE9yPitFU4HweC7EUF5C3XYpalN6TcN+U0UO7wVWEAK5PROZslFKBZzHHF1EHXy6acQkJUZyHsNqSc0reaJlw"
    "IirzbMT3cCyxB4zWtscjExEOtMgYdK5HY7rqszXc/GGBDKdv+sS+StKh1/rQDclzWow4eQCkCDlo0aIDYixKIuGOpWJG6BkSt2uO"
    "E+R5IC5k2nauNkXZlK+FPKDDHqW42KR3llorN8cYDmcWxPs+9x0guHD56XpumHZaR58b4CLG4E0tyubg2/cTX0oP23Cly0oGykGo"
    "R0S8w7qR+VowUGQhcqCed+mQzl4mVRZqcEWAKYDuuFVkNpKM7Vk/39nAHjVNM7RKICzYD380VPRxnNrRVx5zMZ8Za8PEzQc9wZG7"
    "6eA0B0TWgXp6BPKeSgPRCEMZskF2f1MvHsP7VEyIBIY90x2N0yM35sMwIYYA51BtO64BEHdQjUKKWnAMAVJnXzZNvAs8zyRw/66c"
    "+wqfj5R/bQNOOQfFbnhGnHAsdnuYwWK7EET3B/iMJ0IIBjEl7huyz0pz61P5ZpmzypzgRdEQhMsnPEKj8pH7CTKGxOUREsGE4KX5"
    "GDlfR8NLtswjBI98saQJrV8bjkuOnjWwY8jktmCplHIyE2YKVTbaUNSedZtwb1WujvcgjCS9PGCUEkW+OUGbl2PUBLgnYmFX/jAw"
    "zuIaJcNRgQrnK6lmMUQNJ/Jwv/GOP98sbN34mjrPwWEC25qudKLYc03uUDm52cIhkkdba4sjFl9RM6wO/EhfJEi5ZCWl3JKH6aoR"
    "rcUY5Ao86xR81GQAWNna0KrAnCUYvl3q80Gg0mHx0dRrp2vLxtbNAHR40+VIYLtiA+yFdSTdCSW1o+Dhwp/EyjjyTVDhxePYrxCX"
    "jyHcUr4ZJD0BPTIWsR0KPt8dMnO4GUVb/SqLz39PfTuhBpCkZjMbC+tGCTkZHrcseFd4SPbo7CkcAolZfSy4SQGE6CKdnW6Oxpg5"
    "jhdqfDcDSqcS2wbS9NDoZLw6AphAfVyOlcA6uxmvDdOkGKywibaWezHU9HnUBp2cqjwQ6IF3EGeBEos/9nHVLnHX5kMMNdNZPfUZ"
    "0TqN4bAHsMCqU1cqGZV11aRwG0QsEo1mD0K7Hk+2mOQljx32eK5FlnQh9rBEY257OmggQsq6JrhoJcra0AW+sRVcFlWXZdRtuGvT"
    "bjCpO6+n0do54pgOK4wdL+h8hs9wt4yJx4oserkCHJdrdnWZbv1I8+e4vzZHA56OOavJ6zHvQW3SJ3QWHiKybTlwHCp0aKCh3C05"
    "ovSdXKLLUhYsuwn4DDwoWwoelAe21RIlsKUNjWdcSsUFs5F2To3q3ngImCYwD5rWKooBVIWpb7BKyORUWfm08hEl7cBtt5kO1OIC"
    "NPaKv9yKJhxQyrXQG5bftxi9YIjiecWan4Ct0flH6E/Rfdnj5j13Ao46NoroxJP4Ch9VEjmkzREabhyYXLOGwVgrLjmqPFqNQROS"
    "UBqhQ5T5g3K7taIwPdO5w+0sXyeVCwUiIyKNJOYuIdaZJUh94swmQqtDpGR1gV9xA0LF5MDp2I25HO8tiLpyY8mTS4PxhTRRhVb6"
    "XCN6YoI7tzHg3kgcsxz8CDQDbVDH2zVKV/88UIBKdCGzFOw1M5yyGPqjeII5VhsAM3cwIrTyZOixAZoAZ49/yctRK+oznFUXUnFZ"
    "VyT0qOOy5YIeiemYXlnl2rXEyKQNO2UQmWxHZ6FLbFLWxFplpJnlyTgzlEDX7dG2aPvmbJJt8apNG+Y20lxcxAgR4cGoh6UZ5bDi"
    "41U4CwwJgEhN3YGM0L0zAgdlhPd4ZLqSS+gXYGyjrt+4FNDPlimnK7BGnH6HpZUQcEZR4IeTsQleuh2wKElLNNKktSuC3i+UpMvG"
    "1FAnG0qALom2bHkIqVhKvIqkqCDCTYksjqH2eHW9oAYbzdX9UeSm9njQCg3cXXYQNiS0VJTmNdprFcLebXp31OrBkcNGMwGTxAsQ"
    "HqUbcaAkhjFHSNUFBPKQ83oyRsOIfcw88WNFLI4kj4+V3rpVonPjwMMX4nRViCJXTh1uTAQH0DCw+O7R7W/WVrFNaXg7AY8NZUet"
    "LGDgDJwqEqtB6ShnQlHwKXYVelYi2SFf28FtqbmfhKmokFU+SdpSzfAFkVdzA0qMxhSKiZXR2tPNbHfXNJEKHB2cut6gNfTOxm0h"
    "IOapOFAUeVJiQhmOe34nhFqNxa0HUz4T3SyO0NHTAg+otyy3EhO1+QoYTekWg9k4AQ5tAwEfteTxkFd7YfKDuhWqRzYxhq7NdjWZ"
    "EpTzMO4lCDu7IXG9oxyMk1RGDeR1Y2T3dgJNYvIxgYXDTDGKTFYDoNru2VmORCG+6/cgM27Bnryd6Cu2uye8izJHGyLpoU85N0Ak"
    "j/Xk5MO7avEtpa/u7qAusnbIBOsUD4suu4JxuqApfi0w3Q5SPPEIEk8X86x73O4qRkFcG2ECHZs9Dhfqwj8s2xmNzqJgfSXPdmRX"
    "YUMYEho1V3SXi1HNWjnlLJJxXM1aDnHUzooxntp2j9ucOrUddOSOxqIMAlFT6OlWz9j5DiL3ak5xOsD4i8NQwcN63Ka+OFyO7Z3r"
    "0AloTJdowYqgSsyfcoXR1d0s3nobE6Grl2uB0wIM4qstyB6Rm7of1h5yPy6QmHCX6Sx3WFB6yoNFbrw3m6wx1vKij3YOW+etPT8e"
    "gZa0J0BJL3Gg3B9ofzHOEbxeTjGZK15LtdiBmVK/3jNDdrCmZY+kEHLdCp6IGes89F5gOaq0ynFv3iWPmYVzCSwTKocdRTEz0nlg"
    "txyDK4BOK5Mu8YHeGYHWxoPCkkE+3EEFoIZGj0hvwK6p0NT+esx6FmkyDQIID9oDsBx07pvjpBd/YybNtuQS6u8SWup8pTeHALeQ"
    "frUHx+TFhYnNbFvlpLhLcdGrZJsh2rJaNkL5HJJSRFlJORHbkVumdxDXhnyCPTIiSM6tUCPnBIeKD0wQd7508116uOIEEBMJnDL8"
    "sMFJs5xoaUBWC7tcKHAmvMhQTsdKDwHabQYrW4hLFIZCfr6kEXA7HBkp4RZ6d7cTItRFyyvdNJ/mmchuUcFd3d7hGZKdUgabkAWr"
    "Va3TTMoQz0Wy0kVKWPIS16zuM7t9oG9MESS00Z29WwSjpOgnUlTlJNKqYahBMD2t6T7iCuEhCMo7vkw5NOZVv7BzVQxhuSbFNXW4"
    "PTgfjD4vB66LD9FuddzmDDbFiScnXXx42gKwEJ3DJ4A5pDJezrqRngHpKMbaiuArEiae9LTAXZ8EJ9DDrPaaxYgA1PdGk9qi8yKg"
    "ud5w+Uq74K3OTEeQ7XHf/8Eoy96yTikiW+lkH+FcT65FFxQoOePJ5Uic7ndSxKBrQrkHirOtHjNX0PJQ1YVoSjtu5uhs1X1N73XS"
    "yScR1BT+BJ/RgRSR/K5Aot7cA71GHPehbpcVs2gQsD08vJ1o6MbKC34Ng4semLulSIOH6qAJzQijiTJONUHXh05PFe93Wx9Z4mVE"
    "DsUIoYvHGFklw3ECUpbsTNF4FtptA6rwWF94l5lkmVglHfcsmLtDR1yylojdgz75RsISdD6TZDzJfMpBmYKzt3XWo9hAMN6Lrpst"
    "+4KVjOeh9cdzMhmjBT6ukH586FtayrjE9kAJdmdMuU35LnhAlyJZbXtXSMvvDVXdoFPYifElQEwp4iDrmonKffEyQGXxHsh7jlmO"
    "qDY9NnUTcXm5or7o8x6SQhCZs49GQZ16VwcEB7wYC3alES4X5hHlYXTY8+m6TihAQS17q2D+EsxXKKoOwBUB6gI7jNmi+5rvbphz"
    "QG95fq9kqBeTSrjQATCyJM+wENoXokPyXUtG6IG8L4dqHlmkUqLGgRZ5nlkUz2OPB0BWAjZLF9Z8ZWpR7QQfjHildIxTRLSIXK17"
    "UKtXAXyPeqgG7mSuNrfL7M58iWmLAStT3ZxCd2Mkv6QdR2uC2qNMNy1PzinJijWWlBOX5JnrWLQjZw6xnhV9YDqCKVqv5dpeimek"
    "No8xTgL64ZyASqR7JwTOVTQ6YEGB26FDC0hzuZ72CKMe4MGxTgU4cdJJjLfCIzQcGcI0P0rEUeIYekLdRb9hZ7vuNap2AQMtsbsV"
    "7v6weoBEPMF76PGYlz62T1NFFAtb9fEp9hNxUxSgv1gAfmo9Hw96WAXPOi9d6/TaHeTwHFelD17t1CiSHHS1zipO6c1cHfkhZGoe"
    "TVlY4TIOt+7UJ+A2DaCg3dZq1hmNb/aA73jqY+BeXoSB1rBcusu1Hkh+FnYIU99wFGuxO2sRA+fQ5eVA9d7EXc95LmNVeL1PKXrK"
    "u/sxMPiG0SPJCxglxQif03WOi4/wah+mHDOQh3vSq02zINpc+qLazX8niyFrBhk5PPDmCpqFXwGD4yAKBJeGlcDMJbr04A0nItOb"
    "HuqJQPEbs2nXARfRYjje6pC8oOtB0B3+CsAtdD1c1eMFOoMVBLtm5hydG3cPJYgk/Xwg10e6/51qW4gDuy+RK7Vp5Fl1uCN9QrGu"
    "4pRsUqwLFkxrgTLSTABShd3qZBjPS2uoWWodTYLcPM+jQPjEXRgYLJNqIWrYgx8XUKqm5QYsyGm0Txa2ZaMqFNdEI9fcQeJq7TeD"
    "2O4dWt+m+5k4wNdtF/zGvs3YnHdth0tRqF7DVZnorWmLIaIEFq1bdpvuW4J3Lrvd83iNG4n2+EenLM1FtGd11ttOAq/h41xGKYIn"
    "4wE7KzaENicTeeS62MsFgHA7Ixs2xhSzF46UEvahdNZ04WrxcnrR9RtlH8U8Ti+sKAWzPXOGJ08+QPT7ocQpKanNRGKPJbrLmd2G"
    "jwUpWg5HOb5Udm2lfLjUBXSZLv0FoYKMqOddrgxcXcPrUXV399u75o0VIU6AUTdYGFzn08LPAByytVOaGmRG1iesb+u1IfHB6vnA"
    "43vqPk5wzzTkxeQA0rG3eeApTWl3NWOYg25NFc6DhQtZotLVgVhqIXoTgxaJk4m7bU7ZCGzCc7QjnONoObRucEBzeg7bYdXnh996"
    "eVZahrLScn9rkBtHPZiSLC/hhaqAlV/wqARRXcdjIretw9Vm3AMqRYybVo16Ho6cs6eeY4unN0IiI2W9X4eiaHAs6x7ebXfOxgOF"
    "oCOTj34kmcG1veLZwxvHPCL26BycWvu22UhCDvhVtcdi1nv8JNRH1a9Qa0/6qzX2hTEr4yWpILDNZpcxCumgoY5k4MEMn9reLIxD"
    "jreIcZbZFjiaInTXC8I6nZ/LJoEZe8XmLl2BGfdabWBO8Fv4aNKTck2YvgCI+zl9/j5ctd5HqmFpMoHcgjOx8DbfFYARiGvZn7nb"
    "eTPXALZR41CLdiX4dzDMbmpJBWrASxcqLjO8viyEw8yA6UK9zrXDsoVikxZt0xsGCQ2YqZ2la+P7/F2Xw2VYpPtym8pzfFcS/m5v"
    "UcxLpXkDbl4FqVGXzZ1x37yIwWULRu8dwqvddjwbJ/s+t4rhny4SC8ZnxJoGYZXLA4oAcitnA6vKNWSK6PWQp1Y1grDN1zTWpLvt"
    "828OHZ6GeaZHf4Cr+5CoMQ2y4iqMcwY5GWxxi9LaBBRiWW9vMAEz3W32h2wPgdhCbbABL6S0RMu2E+EIwfYQRBwvTnNuaNw13RYW"
    "5rpY8lS+w7NcponqLaSZNBOtQZEcztaSFY23r7miRvGggri1Emyb4AFPbck3c0SGEtuT3Vy0TJicuLXLYm3Yw1AyUlWMgU+L7z9/"
    "LY8LgVXkvS7F50y3B/0aEqzuuDYuCpUSHhmU2sg67ECIoEvKUMpTT4LzqS9shg543IyPthdr1NhoQnExWAY4JO5lUFyNhyneRQxP"
    "3H25GxPxaPdyF6LG4K+gd2KO8m4ddqFD6sfx5FXwyl2o2ahngaRKDY+PACQVJwMmO0C1QlYm7nuE3yj6CJ7S6zTAlhi1yZW+izVL"
    "YZBaLl4vkxmF0g5fI9HkxhYOeeLztf3inM8QE+cuNziL0CpYre3JRj1RTf+Y4O7uh7Nno4+Co/ASXDDmrvhueNzoBxrCHVnBrTpK"
    "2RmSlA1ZgVhgC6iTznBq55drthyABmFIEsmjjs0wuzyE+SOKIs9UHkf6SiAcfMQUJ5Q3rQbPfnvQ8yAKrzzqnQszADCzHSUNDzEk"
    "UpBTBMp+P0NzLusVXY20HqLgmM0TRRzFBzRTd8kEZhza7bmFsaWBg3Mwkvkq4gDZXWedVrpDOVu4x4kX7sy7zpbCyX4wjLYxvcZD"
    "t2nGdB6JbppwNhnEjLX7iNNsTx6vBilKB5mgc+9B8rLFbEt+Uuck5Hz0onNUZXYsATdFWS4zcjpecpudtZq5ULfH4AfrGcCLqN6Q"
    "6SgyOUB3AgPS1bHhOQUpqSIcE4FfDqZa5xdB6Rc8xhYAED2x2HhgI8vUm/J2dXHhrJ67JIBw0aXtQ4ex/syIqGbw/p4eLMTd6FQq"
    "I+xYZfaI4iawYm1bwVaswETNmqQIvtOTCWYBNGSUj9tQYhYTJHdnCq452yUgKEdY36RwjqgG6fgRRIZ0XleGLl30rKVFXA+lez8N"
    "KH09C/0hYpEhpwU/ayxS1yeIHxIKNSPcBkiyHOZbvhE3p4jUpixCXkOPfPlwDneTg9EDAQJUS+PjMaEOKh4vdeWnGTnKSGPnciUz"
    "NRs5WrHm8FDqF2kjzTPTRwQEPdYRnfP7bXUOXBgswUT0KXRQGe0GHqM6OLhMJuoXGykUX+7vYVmOlLkt54MOaQ7qFOHSaUILXCue"
    "FPpmk6tFPvba2XcDysgAI0/XyTpLFKvR0HjBcx2h7hbkBkN9idDrVjxS5mJ2j57UspFLSUcSTwhFWUWGSvwplSLWPYfaRckFYdpt"
    "wNl8EE6zJYs/4nnOOYRj6fjS3OBWhNU9nOCnVMROQwwi3aTr4INEz9EYEx7K3W8TmA/0dFzuBO2z5mMpcqVbtqTtHxHsYQ2wx/kc"
    "c5OLEeTsY0W5eEEdivsBORytE+izJFcovHg8RUUgB7NWqOOiMxky9KWzu2+1sAAJKI83LwbN3Qnuxps5mEUINrAVB8hmYbbhM0yR"
    "scuhjBIxjefTAWoJIwXRao8psJCp5LI8C2SlUMqCpifKkLQzT7RcVJ6Ulg703k0otpUkLsdgLCup66oc2VQRWw4IKyCixNhl3VPd"
    "dLB108J5tXHezZgKXk5mb67LIwCMw2gWqFuTvHO+EiREXYlAAOl2CsXQXrtT3V+ExtKYyQAQhsN1vDBgej0tLNA266PObyKQ+1jv"
    "knPgr5XcKQBSKuisRgAZCRNo2UASlfXkd7zYuF4MWJuEAHBk1IZ6zU9EHjdsCyU8giOx0W1+GBh2MfZWEzr2Ai2HCyPSJwa/9IUa"
    "kRHF2hEuBH78i18m+enz963xU9F8ei0Z9u1bKTG/Lsay+vz3774Xfy4v9tr3UVzsy8qivxrK/td7XdFXRJdw/VrNz9dKly+1Un9V"
    "Y5N7q0Hw6yqbfd0N3D8B/1ro6Z+Z8fyv+5/F/75edvPzsz7X51c6Xgo4/n4Z0iR0g7D7g23X9fBH4/0XtUS/Mux/UZn0qwVEX9fX"
    "/xjLKxD9Z7i8Olj/BNMT5E/xvO75TzC9Av0prj6pZ+7leOWwGn/vII5fAt6a11p/fwJM773daRyGuvqD831CUs9qI38M+QsCnv+t"
    "UyLXQdj/CTgVBH+KNvolyvfKc68TXqoH/opjpbvQL6Ub9xxl6L9eHhf6+67EfjEG4bmovT3if1nkD9jwSgX/j8nRl8B/JgUfR/sP"
    "Yn2C/gnOPizCF6V/8uuPMIZL41bBH+57N2zPKi9/VGS4q+d/AEQLX4qF/lHN4w8gwf+QiF/R/VZ98fvuFfBpm16N8h8I0I6XDdI/"
    "0Ifn8Xb1Fv6RGrhFGlfcl1C/NplFGD1N5s7TPzGax3cg/kvT+XsH9PQEX5rQPxKNdx35Q3uZBsEf7fTdIrd/Vmz5le1/VGr5N0U5"
    "36pr/tfn/3j1l/3nv36tauVLYbi/fPteG+4N9qNYXvjJDYK3mnfPcnnVv4Ii2HVkCH/G8lrc5itl394qUNsf8YHb7QL1Q1DPeyBQ"
    "hoO7s9KNn6VGvxz4/Pwoavelrlrod+EePbz17h9FPYfd57/urJ7iH/+2lMVuzz4nw9D8CADzPH+a4U91FwPQ8XgEdpDP389pMCQ/"
    "Qsfv3wrc79+mNJxPzwLrx2+O30DPP59fKsv9+Lmqq3AXxOrF/v7Xf31u3CH5/P3fgh8/y+AO9wlCafD4CQER6KVxPMLf7G0c3Vso"
    "gRLgWwt+gOgnkCBRaf9EMJJ49u+fOL23cQzCn20Qx8hvQOwTBOPIl20UfsX6Co99IiAYesGLQdg3H23wbd47PPjyKe1wr2385fNJ"
    "7Ssc/jqPfEHzZfu5DPIOL8Ev7Q98NPwki0A+1vtov9HzAf9GL/zSDX/sB/nl9pAnVuiDHRL5wsR9O6/sesD0e88LQ3FyJ/DJ2Bdu"
    "f/N2BM77aflj99SdXZ3q7vP3z2JPn8GhhNrdlvx1lxDL+Cl/j1app4AxLyL0a836X//rt8LZ7wLcPOtT7pL+txeTOvz9JyH+1jbe"
    "S+J9G35ffffT//1WbYr5dvju+yX89uE+a3C5T9Q/1w57FiD87nvnV1owNl/VgWf357F5k/+0+pD/l4Fd86aXarv//8v/fhD7wT5P"
    "AgFxEtwPioCO5FPyQfxFcndJQ1H82SZR8EViXyQRep40hkvvkkq8tMkPySaeEoO+Sza4H/guMfDPkk2+iAxCv2sK+QKGfPOuSV+0"
    "XzTtDV561UTkEwEe0QeI06/tXc5ftPddi/c2/iJYL1/oN2l77f0Qzrc5P7cfr2ilV3HGP2h8kXb4Z5petQH8ov2UeugD/lWb0Lc9"
    "o2/aBb/xhPiAf+OZ9K6t7zz91Zn8kWL0yDBj3atiqL9WjHvzZ2rxlL7fUwrnX1eK/zB++vzfvtl/PjU/NG78rOBWd9/87aXr+ROk"
    "fVO464/fREW4/OWj+yWieNZVL/sfv/H3nYbdz4PZ2A9ptP7wUiq5Gn4L8MT1w9y5zY/fPP/+ecBz/fxZsLEKfvwmGL79Hx8Uffp5"
    "5H989zO8/+Tvr0FfOr+EanaX+yw//yu4t+4vIb2XwOyHzg3Ssf8NCS+Dn14Hv5wVPzfyS9i96x3i7//tN/x958z/MT7/yxT/sAdJ"
    "3Zd0l263g/yQVkVahT+Ez4Nzx6H+c0Q76O+ieVnkzxDt38Lvf9td7cn/V7r3/ORr3VHafbW/6cLpC/J2de6fgtbU6S85/HFsb5T/"
    "f3l6Y7+L4ms69OM3T7/w81A9hV20B2I/fvMaEX8h63WfPmPAH7/pwsId0in8R7SrcqdP3ksu+zuK9ir7P+7e6peEfFUBv8D2G10s"
    "91N+dYi/P+ll/MtJb47z92e8Anw5Jdq5+sP8Z/OeUJ/mr09+Vi7+s6lPmC8n7ml79cb/j75fcv5XCH+e8CkYO/f55X989/0v5r6w"
    "8J+fVo/Di0T+i9O9evmhT9w9GPtH5v6DFvRLMfs9Y/phrI9/+ZV1+Oj6PWvw40ul8x+mtE/3DPZ3bMOfAj0txZ8CvdiNP4V6WpFf"
    "An1hU37m8B9K2bOI7zMT/vQK+yWr3o74H5v+plT/2FLPJPofhP2Nhr8LXh1Fe7zyjxH3CvtH/uflfKt6+PbTz8Wnv3vv+CXYm818"
    "jidPQ/m7x/cbdL8H/nKO/zD0i5T9w9Av4vZ16C+F5R8x3S+T/plI6Tdzf3GYv3cMv8/wf5bg93n/Is0f0/+U7Ldw/EuP/tXI8RXs"
    "08suu/B5ffVb+f4Dz/K1+f+si/ldHF/6mt87mv7/ZUT5z8eF2fCsHt+Mw7P75cvz9eUXkd3ydYefjWXzaahfN/oy89MO+0vn/7UV"
    "X3U3SLtvu6H47ve09Q/GX/TzD8ZfNPJ9/IudvHi+qO7KPbaqB3cIvwWJYxDGH7R+/sv7Ddw3IftM0/79f3rP2u5AEhZN2PXf/PDN"
    "8+Kyjv79LVvbwX567flGX0uvLn766fM7is///b//YujTfmQvDyM7TP/S8/k/Py78wo8bv7c54d9//Mpg+Cucv1wu3GX9+fIw+i+r"
    "/PQKs/f/2/v3T82+8fqJ4j/fafjxY8HvX/b89w8WDHvz+2FPR99W/3b4qWL3hPS7dCfkP2/e8zb1UxBGu69Qunrnz7C+TPjb5Bbj"
    "buu/D6uxfL0l//Hfjt/vtEVpPH605z1Vfvv+9+9+DP9r+OtP+5Sfl69eTuB5lTr81D1J+dy/3Ch//u5n5u/UfMHN4cfh8Pnzzxhe"
    "Zg3f/S2Nvn3Z2r/99Ll+ofrz//7f/xZ+947lpaB49Zcd6he8/b8+jztPv61+Cv/rjXlDrXRpmT5j8r/uyH56fQ54pbH7aY+V3aJ4"
    "WfEvryt2X6z4vlr3lyHp9pjs+frJdl3dffv5f/7PLxB/U+5ZxTdvwO43zUf/C1M/ff7u7x+H8dz5K0f+8/Wu/e3147vnKT5pStnf"
    "vjl/aMnnt5v2/zBeXzmfr2Ufg7+QvdcjeKr46wX79ztLPuXh+nYM//X5y4uHZo9Xy2ZPMarh8/e7BP3t37/UzLeb/n//8d+GT4nb"
    "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"
    "nMbd6xrR3j2khu1utxLESaddHfdh0X7uYewVVCx5/vtexVvHHJsfN5vv08r2prd+c175uOkHIQeiZR9jrnOx2fy4iVldz/q9GmdT"
    "3E/iUZhk/TCtPR5hTo1LYEc2Nil6w4Wqi3GABuFsHeTMrR7JlwpU+SACdxBYzVBEZOF5z6qbB0Fr7xx4eNFS46J3FB6v5zugXjc2"
    "UYrJMGmCj6hvcGENn/kNPeL7GQV/GA7Dbh9ZE0rECgMcooRXCf4VmEQY+D+esOry139ZWPgHhQ5dSMJB8xE9pudhmD1a6CRxmsZJ"
    "v9ePfm0kcZxNq1VKcxmDqPjofTtCLD3yF9LrNAuHMAv+QhVaH4RVLvEXNgf96OJ9u3NIv3fgO3/h0WHYi8OFL7v4ZTtKYb0k/bN1"
    "bhpT2DXEX3Lkx/o7C+/hJ1R/tNVOO3Byt2XB+zAaxP7CFrBCMawLf0F9J9pD2li9Shv1+ujKLEqHjfqqXTTsNuprdtGg16g/s4uu"
    "Bg2MqmoWrWLZC7tsDcqe6nppvfFU/1ht6NrpmglI+rRRf65/PTP7Sp83Vo1GXjTW9Hd4FzNOcVRPc2WN5/lKMKgX+TKA1oACVl8G"
    "+93sQBRhD6sGgOftLtokIUlorCwAjhfgk4V/rb+oP13r1J/6CysLANBC3Shd6dofx3CiYXr2Fa61xlVX6i9WX6y+FFXP2mnWqNVX"
    "U/Ebw3/D7xfyNypGG53xab9TPQ1v+mFSqa1C3/T/dW9WIyIBh+XF1Ak3/l+WwFLkaOH3gG+F/nuxMvs33AsAXyeciqdhf3DdEHtj"
    "PU06DRDqKshoNLDCk0l8dra6jgN4/tTvrrx8/b63sbmB/+3sX2xs7tJjPcHfH55vbBxuHm6U//f64v3p851J5+LNxpPDnT83v8Tv"
    "483hxpMv9YPN33Z6G+dbf1x+3ny1uxW/Pv+w+3rr9bft6z83Xq1u9D9t9zcne+fQ8+bWxs75596b3c3LL5Pr39Lh068fTnud4ZNx"
    "vR1+27i+eB+ef+okr65fbbz8/evN1duzJ08+fHn94f3Xm903f2yNPh4sn09eH747fHv4+ku6fP3L8/h7+qz78d3ebx/evci63T8+"
    "LV/88vJ07bS+8X5j8rq3fXl1Go3fjz89f/5te/Vs+fDZb+P9jRdX8e9vsouLMPoaHb5Jbj5tZR8v/z+azlu7QSyKoh9EQU4lUSCC"
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
