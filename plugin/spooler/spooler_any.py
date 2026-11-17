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
    msg = {"type": "live", "live": live_poll(), "usage": usage_state(), "printers_rev": _printers_rev["n"], "rfid": rfid_offers()}
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
    settings = get_settings()
    skipped = _rfid_skipped(settings)
    kept = [t for t in skipped.get(pid, []) if t not in tags] + sorted(tags)
    log.info("RFID spool %s in printer %s skipped", min(tags), pid)
    return save_settings({**settings, RFID_SKIP: {**skipped, pid: kept[-RFID_SKIP_MAX:]}})


def rfid_unskip() -> bool:
    """Offer every skipped RFID spool again (Settings)."""
    settings = get_settings()
    settings.pop(RFID_SKIP, None)
    return save_settings(settings)


def rfid_offers() -> list[dict]:
    """The new RFID spools in the printers Spooler reads, for the Printer tab. None until the spool
    list of the Spoolman in Settings was read after the last write, so a spool just added (whose tag
    that list doesn't hold yet) is never offered twice."""
    url = current_origin()[0]
    if source() != "spoolman" or not url or _spool_cache["url"] != url or not _spool_cache["time"]:
        return []
    known = set().union(*(spool_tags(s) for s in _spool_cache["spools"]))
    skipped, out, seen = _rfid_skipped(), [], set()
    with _live_lock:
        for pid, state in _live["printers"].items():
            trays = [(unit, slot, tray) for unit, slots in sorted(state["units"].items()) for slot, tray in sorted(slots.items())]
            trays += [("ext", 0, state["ext"])] if state["ext"] else []
            for unit, slot, tray in trays:
                offer = rfid_offer(tray, known)
                if offer and offer["tag"] not in seen and offer["tag"] not in skipped.get(pid, []):
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


def _rfid_tag_extra(value: object, spool_fields: list) -> dict | str:
    """{"tag": <JSON text>} for a new spool's RFID tag, or why it can't be stored. Spoolman takes
    only extra fields it knows, so a missing text field "tag" is added first; a spool that already
    carries the tag stops it, as two would leave the tray matching neither."""
    tags = _tag_ids(value) if isinstance(value, str) else set()
    if len(tags) != 1:
        return tr(EDITOR_INVALID, field=TAG_FIELD)
    tag = min(tags)
    holder = next((s for s in spoolman_call("GET", "spool") or [] if isinstance(s, dict) and tag in spool_tags(s)), None)
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
    "Spool #{id} already carries this RFID tag; nothing was written.": (
        "A bobina #{id} já tem esta etiqueta RFID; nada foi gravado.",
        "El carrete #{id} ya tiene esta etiqueta RFID; no se escribió nada.",
        "Spule #{id} trägt dieses RFID-Tag bereits; es wurde nichts geschrieben.",
        "料盘 #{id} 已带有此 RFID 标签；未写入任何内容。",
    ),
    "Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.": (
        "O campo \"tag\" das bobinas no Spoolman não é um campo de texto, então a etiqueta RFID não pode ser guardada; nada foi gravado.",
        "El campo \"tag\" de los carretes en Spoolman no es un campo de texto, así que la etiqueta RFID no se puede guardar; no se escribió nada.",
        "Das Spulenfeld \"tag\" in Spoolman ist kein Textfeld, daher kann das RFID-Tag nicht gespeichert werden; es wurde nichts geschrieben.",
        "Spoolman 的料盘字段“tag”不是文本字段，无法保存 RFID 标签；未写入任何内容。",
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
        "rfid_skipped": rfid_skipped_count(),
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
        elif msg_type == "rfid_unskip":
            rfid_unskip()
            if self._settings_window is not None:
                self._settings_window.post({"type": "rfid_skipped", "count": rfid_skipped_count()})
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
        elif msg_type == "rfid_skip":
            rfid_skip(data.get("printer"), data.get("tag"))
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
                "rfid_skipped": rfid_skipped_count(),
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
            elif msg_type == "rfid_unskip":
                rfid_unskip()
                self._settings_window.post({"type": "rfid_skipped", "count": rfid_skipped_count()})
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
UI_PAGE_SHA256 = "976488b9133a9637450e0c0d7acc4317c89538ac6d1fbeecb062bde7a2cbe1db"
UI_PAGE_BYTES = 1280337
UI_PAGE_Z64 = (
    "eNq0vXtz20ayB/r/+RRmrosHWI8Yycnm5ICGUbZsJ87DTizHcaLVISFyKMEmAQYA9QjJ73771z0vkHI2e6tulS0CM4N59vR09/Tj"
    "UW9aTdrbpb532S7mj//rEX7uzfPyIv1Ml58hQedT+lnoNr83uczrRrfpZ6t2dvD1Zza5zBc6/eyq0NfLqm4/uzepylaXVOy6mLaX"
    "6VRfFRN9wC/qXlEWbZHPD5pJPtfpESppi3auH58sq2qu60efy+t/PWomdbFs76F36Wf5cjkvJnlbVOXnH5qq/OxeMU0/a+Sbg/Oq"
    "aj97PBo9ff367Wj06HP59PF/3bvXrWVRTVdz/dnj2aqcoKp7OtLxeq4pP319/kFP2sGk1nmro3I1n8fDWVVHyC3vVbN7etBQH9po"
    "rMZx3J6WZ+nRsNbtqqZq0seaRnav3V7lNdW13qoyPT1TdRrF6WN6K/ihd6TyFGUHmMnjaqqftNFhnKbp0dFRv99JPpLkw34/6qQ/"
    "jB8fPXy42ewkPvrf/4lVJZU3bV63za9FexmNq/KX5ZQGlIxj1dgx5k1TXJRqkkZateggjzHVg6Kc6pvXs6iNh+XjA+4Sxjyh+VBH"
    "8VbNbQ3LumorzOngMm9eX5c/1dVS1+2tWtk65wNa4Dm/qGn6pK7z20HR8K+aoZ83NPU0xPFpxVXe+zFfno3V8q6sE91S1uKurGc0"
    "Nsq7RB76g3WibLvAY3Wxk9O0dVFejNVoN/12cV7Nx+pqJ13aGff7vZ5Wt8iMrqgPm80l/Y37ffoZtJe6NI8EopPLWJ3vT1RbnXDT"
    "6gaVnJvpidWJHdag4Zn+Wh0cxer4rsFKnTRcrZF9Qdm0RD0q8Sp/RV3Up4dneDug5/H4wRK79WXZ0iIcMZTRYtCHBMAf9a2q9Qz/"
    "RwTj/Iu0qnxXEkQ91ZSof6xWZWuT+EVPuyUEtGyavO0WKRdhNeZVTwkcSx7EX+w+2VxRSetBu22ziXjTUW4cEyzWOv384F/Xn1+o"
    "67SkfQzIr/VyntMc1lrJTuAZPYpp8n9ZEoAe542O6GtV0Mf/ehqdPjn4/SymKnK9V0eh1fjg/tEYH/9QXbuPVeXLYgvyFu428MC3"
    "TLvOFc9oN95fV8A523EypimYaLtdemYCika2zJxzBoMB70+Hh9LDYflID+a6vGgvh+WDB7GmOYm43FatpDpVEuLpHeFDU+tUz4pS"
    "203KZdaEpWfFxarOz+c66R0qXa4W2rwdqeu6aPm5Vlf5fKWTcksNTMMlY/B6Ma9yAjC7WPeKhkCR8Eemk3arZmF5gGv2arU41zU9"
    "JVTu7o+WWtF5Any51JtNavbixbw6z+dvL4vm0Xg1zvxrYgo0ej7jLDzYxGvCaNU1J8tj0qkuqCpZb4fuWLjkc6GYRVNsctN/FPj0"
    "OnChOsVyELa/iOo4uyVAjJNL/B1SXUVsP+ezoqAzRJ+lBf3Zmnlot1TsgrELcExsTxc+VS4IZIdR1jv9v+jsH/+KAbUjSkqi0/87"
    "exB/rq7o5bMoS07/77N//ets869/UXr8j882/81p/x2k/bc8bP71+b/+Qb//yP71j399/vmFH/5tcCzSqG033Na4stsrOGg+/8c4"
    "zsbjBHiMj8kLeqIBP88nl4B+zKapFCeNlBkR4JRmFh/TcYMdTjhsQIhyEcVnaXl6ZF/i7TZW7db18a3v4ng8NPMWt6ke6nlDE2zW"
    "7t+vGFVEa0YAjOYfpPWD8b1xvLWVXHUqwbpp3nJSuOTCdoJa01XfyXMLRz1tFxOobUiVrSdzOoaTVjXt7Rzbi3pu66HD5oK2gxz9"
    "KEadbAmVlJzCH6SXjAeVwMYNo/Wi1YtmQntc0dFSXc+oJaJ+tC7VtGiwmZfFhBrQRWkebHqtF1WLtb09zycfFQ13UVa07QtG70Wz"
    "yJeqrIR4UkEOvmiKck64hdBxPq3K+S1Nhxv+CQ9fRkXHJxEtOM3Gfn6OteArniO7OHSCtebRTFrvaChr1Tt0W7CgBaUlK/yaFrSm"
    "dfqMqjwtzlSLP6Vbm9o3et1ttCn+1NwkHnYbFLplVlcLWgDa16W+vvdLUbZfc0ZU2366brVMKQps6fTgyGXk1N/8kf1gmFNnARfF"
    "aU6wRJ1uVU2P1Kt4rdN8eE7z+RHoQD869J0CskiPDLroHQa7wY1J+o29Rt1lSo4qqTebgs7POl1K+hKjQaLDMZjKzM1MgrZmkTk9"
    "iDJoQJ+45QnT23hvreyQa9kua1muXVKRsCJRw+1+KuNK2gL5ZtOjX/zwotZY1JqnyDZlEadQVkItmec22IbPtT0W43VJR8oplvFH"
    "ALX8nmG1TwuVE8bh1tEpRsM5P7VumorBhW6lHdqlOb+1TFoNi0GDLBzeOT+2irAbxl6ltZlXd+DRiUw52B5U2DzTh5Xv87MOlKI9"
    "O+pDA5sLWUtApoNyWtKMl1Kja2+LBVEj+Na/0dImBAgj+XhkASHjJpAzlZypy+H63BQea1vFlRS8cgV7NVYso1xX+i2VvnNxQMIB"
    "c71mCqHXizSYjdHoalQ0b/SMivYOY/XckrlEGVAHgTtxxkzdEckI0VLW9NE59eAySIrj7DVmOXtOiUzIxMl3J69fDYQNKGYghj5q"
    "9TDoJr1bquw1ViX7yKOxn2NPZevTMcFNdH8taGMbj8+SU1BhA2J860I3dHrRcTld0WlJH5/SXBA3SDUSHD/hzR7T0ZE+HhPEEZio"
    "NVFXydLUTOzOXTVz+1wx4WMcqU8wMvoOi5ih1ji54mOjN5WfY2S4Kaez5omMjHAwdQUgkI1PmO+h9jTBoTDLBH5Z1lLLiVYftPpR"
    "p3wIgWKkaVtNWtrfGgTmuiX6iz5r6YzXU7AXeB/lBMFEjRBNKe8VHb7yqGczQhwNWGN+n8x1Xq6WPoFW/6d81VBlRINKynVel6/L"
    "N6vSV0hQ0nwslkjoEdx8oP/RBz2QdrOICxF1ChnEB9Mp5mxTlOITsiFs6J6p9TgeLFfNJX8aE/+VRN2h3NEZou23F0DsXCSy59y9"
    "8MPtEoOJeA+H6WbmgtHKpqbODm1R6ZulmIIkw1vImaMxtamloYb6UTvUdLSUdFAMTONbXy5chN1Pwrzwa8KxzWpxxyD6/e4g9gd1"
    "9P/DoGxvtkEVdkT/cR3belUaCq27PEJYftDDtr61C/tBc2uKp7Qoica6XSNtu91WJU3PgwcO3NOUiVmGw1pfnWCIAEVTRbytZrNw"
    "Qqvy8WG/f3AQVHDI2R8YLeMT86mvj+lcQ2dQRzHmoR4aosa3aj5fh2k7FQmtQYjYp223O52/qorpvcPttmmr5Z0ztrNfeOUJ63G/"
    "WlqL8k7gax+Vw3YX+NqzATcjC3nHZ7y0rkqLRO6s02ZSpVHswHDnE4ueQujUn4ROaVrvNqddv+nkGoYf20ZAzvU6KNNsIcFVhLB1"
    "p21JtrUseUa0CHyQ7yAsLHbqsd0ZIWQj0kt9arwN0aNd1oD3fRXgsg/aEyQ/8SnIaH8H4X7QfkIZi9IpCUkJH/AvtHqpmW7+laCM"
    "jjb1w53niYGgWWmPkammc0H65xPe5sW8kzib5xdN+k95KfVN28k13eqkNZh4YmRqm7o/Ggtt/khIfGP99OBh7BC7T9+kX33pcWVQ"
    "/qsv7UrZ77/6J82JUJaonLJfakcFIkV6Sgf3xYWuIbDallULYqVT8UOCmLDiLx4SVRS8f73ZvDMVMqITTjT84sgRtmbyIwO5ZkQP"
    "FehY7tGvpiZB6ekLwMJ7PXxhkOJ7nPchtnQVOlz5jR0cfaPxQas6s/KFwS4eudhOOvmX2RiABMJ1wFhY8md6GX8HWmjoAedOiHGD"
    "4dyqPKHmzBaUlyjudukh4UG7CN0lzWjF8uk0hA4HWFn3NTL5tAQvZ88KMDm8Hu5l/b22gGALRkJbTE0BM6e23Har3uB8+1Orp9rv"
    "3Hd+h2q7gl+rNotkmtKnKJ7S5rQJ9P2fSPCb/FvA7hs6KH3SL+boPzh4ox9bXhSY9KnDVk/l+Hlqjwk+h+QIlZaGurM3tZvg/1V8"
    "gHI1coT96b/9U5L+dNW2Q0c5SLUAlO6uD2puHfwALFu/nbYspCeKeM3yxS2RCVtmtenIqKvrewHS+5UlGI65T7XAXjtsTRcAe0Sa"
    "67qh4sTvq5YPzSeMS34oyo8ppK9Lg1yQoHYT0kCq9Y2XvPEZYyFY1akcpcN6aGe95paoA8PadSClLmTEmxGvRFiFaojVd5A/qt/w"
    "lwAxrVW9236902W1m2Bnt071Vpv9pXznaPrcAL7/OxPGy4ZOmG6z+MU8EwbjrEm1WK5aHJHRHzrqpsW20B3fx55NdoKnwYg3ku/l"
    "H1YuZyHxS6BS+3L0FTUQeSA9+h8arEiJ37l5blsp1E1vW+JIBkVzcvIG/Kyp7+HXNIqeTAVOedMf4lV5umLb56Hbtg+HwfQRJBC6"
    "rQ261QGuZfAcWpkqYVuqWtjUYdQGQHG42fAdnssWxtk0Rv1zOcSOug+JqDFbhU9nbI0gT2mH2V/gM+pVrRh+g/1NON1N+ncePUH+"
    "SQNLSsUU5uo8qRWAA08FJKGQWVEX64FJTQtlqFN6FmiMVUElCpdaK+1K2xLloFmdNxDPYDfIS616VHXpgSle+xfX8X8O/ZkTZH/i"
    "5FFE8m17oOAODqiZCeonJt382KO9hMQsQLa/2c2+NhuZOHRTq8iDWxAOtiEICuyO9wPkcdnUVrlu2RJMgzHAqN81Mbr+tPgZeP13"
    "LUTOe1o1lDryvbuPfJkAlGLq8z2kNampe7MJECVLxdYi12aaK2nNOuo9KsxW+4Lh2eJ24OiAWgCkE13K9+lMcbd3UY2oTE5bWnVP"
    "OFrSwu4AB7aeTuT5sjyOe7EA5Lmf8GUPI9JBXLd/Qc1auLFds/0xpGi+h2HtWLqUL8FQ553AaIekTfdFI0S55JOP9v7hBR11vff0"
    "54VlCf0GMMhHMM5Ox/iIDZa8Re8I376gw3K3LFP5ZRu9kNGC0OMNk0Wtm+UXwZkWPPslCVPTNk7Ma9pJVgXEru6mp+2cf7xp3MoH"
    "0678CeT4LJsy9HvLdVa5J67SPLuu0pa5e1ztzib8OwO1byJYjuwb0WbubtDSLxa4PCZuW/xh+BU2QTuGgQqDpuPttUNFA8wMLjOQ"
    "Hmsk2kpiVv+gd5y0Ns3tz19YfhLwjUXrzlR80ExwRPD35oj1JGF4ljOA8aHIX1GfaHjuGDwM0HB7F/blVrf2BLRVDEESaD7j7CYu"
    "Da60O1zj8sx9AFwDVJO3jlXF/UDVpkY+itv6pvM2Cd/8NMzbQG7/nvrwwomT8tbcHgzbzYZezH1Bam4hYiPXl1K4LIDKA5fChT5K"
    "1RC1Mzpo6RdooESC7PQ4OGtXrb3xUIXKpQNV0AGghIommgDHkEk8hw1f17Mo3lPLKAwYUsADYyDzehxX7m63ib0kqpDbgzylo1nj"
    "gtLc5WBjjkUMMrZbz2gC1PHQ1xVh4qgHUfjBZoO3Cc1ZbxRBz6Z8nELyj3uZrbmpba4L0CkR1t2iqoo5bHMOcvnKzCz10L9OcLNK"
    "x8gkb/SYWLpxUmRBtus2sU02rcIns0gHlTa40hBJ2pBrkjOfKqNF/E++o+UeJ90y+Gy75Q3nFnja+vvv+6ECBhaJ0Hw0xwUUroTr"
    "nLpB0Bqr31EuztrkPR6y3/hva28TyjJqS6ZGE0krS/vUlkHLs9Zf6jK0S/s7bQWkwVJuxewn0ji1Ztov+WqC/uGBN+GiTdejEWtO"
    "jUYJLn3UqWy1gbRR1WeeKb4Upl7tlICGwtJk4ZZE0flMxCxUZXz3p0YgMAgy7XwAkjOe5oS/dxc7uw2PTc4YTUb69OgsdQ3TSyzN"
    "a0LXt52JuHLfI4u+pg1rDoy8vlgtqFpi9dWsmLe6vvtLyZNPWSPD9D0Y+E5d5fRTNZVTV4//fO/rl5AhfroKzv6LoZTTH/Km/fT3"
    "yP073UC5f9MVV+TT3bHaKXdWIZmf/LgoJ/PVlOChA1Dn9nObTd9zYdGr/FRZzpWiH6qijO6AUJO+VXM7rk/WF5SQOhkq7hokZXxy"
    "gEzx2y9u7BeUOkYmmIZO674EZUmz5v7TqLHZgre2oGRz+67wm+Lisv03X3AZ+1lzWRBC2u8Fp6OnTbXQdw8eOZ8cvVF7vXuIkimD"
    "bKs32L+Nnkb7ixZmouhJVRPJc9fyBnlckFuYfgJb7eRv1aqUebi7uyZX+mtvkfewmGSMd/FmqBXX7iiZtKIBUJ+2ZzjzRaVVFDhq"
    "IcB6cuaAFsotDrd382/zizMc86xKc++lwduOPuhqhJo3Og5/shq1BP95HHvtNJYDQm3woo1yfiOaheijgroyaqmP/f5d6pDA6VqZ"
    "6UjWOHBtF/KBYY3s2XqHgnGmB+fAqjkdE8QOsphktxZO/PuVbHF85oMRD0hGovKd4Y3c+CyDkPsT96KLYYnMrUrN0iqR8bROGcIq"
    "kI1ao+rk9JX9sl/dSUvK4jdpFS60mqQVTTQAYGJn3VIpkwF0+HEE5m7RGnv8M/U5T8uhqS5qsnlqe8DqEnYwpUAZw6ehLKhjBNmJ"
    "UyR8SN//ja9b+S4WuntFHeS8Ss3pA9dDKL8U0SpOVn5+b1uvTyRkr8wG7YHObFTEdTS4DDXJUZ5FTWp1wCCXoyJhP1XheorrvYYV"
    "D1IzTIizwt5zck3wzaPww/+CvvxktbsTUARTMEkLXJNWwL7BDGTc0CROJoFi4w4qEBKUqMG6SwcOZXqAIYCcnAZUVDCrvtngt3dE"
    "xO7PRJifHp7FGf+gQn5V/tM4KXwHbkwHoLuxhihLMZsb9AbXsRbivOYVqGgF0ZaqGfBPWmhOOmpTOQ0keiqadytNnN6xsGhQy/Fo"
    "KNBZe5UvCIcIdosHll4jcgy6+O5QGRtVfcw/0WyxpdXku1N95j4dxQE/ec3k9og1nqi401KKh474l3s5T5ET3U+cD9C92lOv00Ji"
    "v20/odNjBLRWk+ON0ep0uj1Fc3LJ2qVpu73QIa/L3KGVP42d7rITSVnudqdmOj92ah6GlXFBljDZKnv1fgGjeWq14HYKmHpdftHJ"
    "r3OfA0YzqrMi+6VNvm2JEXzXJk/b2HDNm83dpxBrtt2dVUJzzUg4RQt0atlvgztYRppDVJEuGF26mXO97C6h6+y1YM0qJWidm7Z5"
    "PepSNOaE/Y5YPey4NZqMyQlEZwCmerNhYcWYvhsDjXpt0IqP8DKqnKAsZ4aeKqqSSs6OodcchSZe9oewSvY4uqKPsxqpVZx8w38r"
    "Oh+fG8C7R8eXLqcNQeIdemXNioYaETQSuDZ6D9tqITimYv+ijZJrbweObNeJ4SykwO8tyw967+WXkNB95BEWuS9igR4NE8gJhWB5"
    "4heD5qswpyeRFL1DM/W5NWhoY6eInKzkVGrcwgRDMEvj0SvEsdR6DX4fiDvjixr0gGU4LA/gTws6gjgFMgreddTEVsQMoWWHvSI1"
    "vahltgrXmTu+cGqp/X5p2zXyC08d46TZsl6sb8PWaZNtRSPWP3QwZwGNsRL1qdxW1+X3olUcShKCs4O5byt7SSr6yLblPyVwevaf"
    "gNNhAE5OLf3wzil0mVv1WrD/81Z9lKdnrXpi06Droz60bHenfuTfYDd2kUSgYuPwphm8O6z55DVQ7gT6hKEI2gVU6WAnKpHoLFal"
    "t5IH0azfkYD0+0TKSDloao/xvmJ7E2lGTdMy+9AmbVaWSWuJXNxi0VrkwVrMs6blJWiiLlG+itVa6FC++RFDIa1AbeL6Z2WIcEf5"
    "ZrtFEpMwyU5pwfm8n7IEJT5jJV9bjkjiQLj5UyiBCqcuIHkxagPCUEjWXnSZCTyzTkZQ6Ys2BOy1CArX4ZllVqKQ7SorQigWqIH3"
    "bB7zzBUGoRKaCN5yObDXtAUID6Y/8mI2aYsF0GYBCEVVQp4VXsn9XhPVVmzZKZHvlWBuiEgM2sb2k62CGgkUiSNLh4eDsWuuuecg"
    "JUI5HpbcaCEr2cih3qadj1rmQebFowAzLS2jMiEM7fYP3opYxMpFVtrzqXRIQ56KQFITnAFMwYLptP2o0H6+N6mdEVY7o8u95FkU"
    "vg15XKuGuZtITsWts4FqcImerQkFJwSFjIph4dfyG1A1gSxDHScYAKTtCsjjJCM+J8iH9pAziLJUHM3mj342maXga2XmJ+TkIrxY"
    "JP70xRxJpwGBfM+vGRQ7OVpyiv2cAqRAybpMNHkr3DXICZMDwpjq2ypBmrQf2s2GD9HN5r38RPbs9KS3DIQhvQD4JTnDew3kZWUE"
    "MI2oNpvUSY+DDKmqIc7Xl3WjtT1R5qBs5KCszUFJWZSUSAoPgwvLKJzNxbpLOktfS+5rzX0VWx/DKqH9IuxrkBEbqq7Oap9oCD4a"
    "buvtPIIzdsUkuj1gtRM/wf5DQMXJDlwXcW1mLJVE+9SUC2zG5NwWALN1dn5w8G5jdSrHgZf4eAH2rpTdbY86fbwuT+uz9BVmlkVv"
    "qM1hz5cd7GlwqeX1RG6QPi7uIOqznk6KO2j5rJNsKfis9amg27M6CYnflaGcChge1VmZSMvM8fzQMlJPqKdEV/Zgzf6mm3RISX8G"
    "SYdS6mn3SvBd9/Xb7usvnVd/4v/KR5a5pdLmskkO03HCLyx+GSdmOY/kMojqMNkn2hY0dQdvnGc+fDic6lm+mrc24TA4474JD05B"
    "JTr5DotF43/dqh9aGm1w1fN9WN6We9LSxNE0BOX+2C93SNQSzSbNT1Duu0CSJGoJYkqvLRJnhdbQEMhol9si4CM3G28r/RxUX1Oc"
    "z3VoLmv2ZBFcduY2MzcWWbQgJ8xF40hldfvO1w0vI9FvNyAIUeAhwVpowCWIqAEN7hV69ucXSXZ0cbJr52SG52t434YWkzuFeWcE"
    "hX//ZGHLAfmyP4dd0xkrxUmvko7ST3Ct6OrzhAKRcHzIJ6HmT3Bd0QPTEQgBnMR1Z6kIWelOSew+I4psS1DRzFJ+IyylKn2S4TL9"
    "zqrLzsB2bcg6o3sWFM1LBudgijjFk5COiyZAqCSL+1eVf6mIBO0juar3GjnSndB8yYtRnGkRzfI7kc5So3LQSMaVS+X72bsqYVnM"
    "PS64Y4gEBQejHhBWBzbIlNddwtB2QwVknmuIT38tpz9tLOKFXV8ncstiVd39cHRnGGV3GNI9q+YeXja8DtbKLMXAcA+8DI0Q6Ynh"
    "pNLHHYEOtfI62pWLMMfsPmFzvECgMPSNef4/81w/QDS5g6Pv9HoSQuNvrYcgi0qaUqBoXv6F2tgdMCOdCCRJbboLbjwdJY+QqBjo"
    "zPLCy80Ck/Jmpm2K0Zcf0Xep0Ywbwb1P/UlosrBoP4viLiC5Opg799OyCqcF3Z2XVhI5/cR2YmqzaxFC9RJhYnX7OlOidiYj1PPf"
    "n83/xLTk6Ct529XzPTj6hM2JGI8If9Jp30hSe6b/rCSclt6yo2P1sEHDHVuNr2PoEhnbH3taGfsORp+9w866de0lLBKwUP6HNcYQ"
    "LamOulygWf0XSCNYEmO3IC87Sz8rjaDe6P3eo7PfdgKkUFanGtbEbLCsYCZO1cRsmT0V0tHsmGUJt0qLskNvXZZ2T/jLr9KoGVOb"
    "lyKaLi2KW5RWt4oYGXoR3aoWlwjQ5RPbpYBgGqGuEiJqkXAUi4WeFnCnlBM3oZdJpapyopNGOWuPZK7y1QUk/t9V58lKgStIZtu0"
    "ENdGFeEDg0MrvvqQ38PsCk0dEe/AyHGhLtRIXalbjOM8FXN8QYPRBd8CGmxIJeSKNRFsY3LZzv8WNtQsR8micwD/LWaX78PTx79J"
    "J+RjZes0dxJr25oX44vMl9L5Q5u+NPTVZZA2y2YRW1RDYYk6dpHyOpfZLEMjNjNh11j07UgucFhFcRRoGN5nDUNZuMtySEu9CA2M"
    "pJkv1OnVGZq68h9SyXa7hUp5v1/ZjXBBy8wzfpgdfX6YVEMZMqYbR6PoEN6ksH5TJ+K2a2HMENVNv38zsEavk+jGGoiphWjHNf1+"
    "adsph2UaWb89QXe1cdJjO3nC6pP45jg9z8SdhJUg803QPFqWcbIsjbMnzNTCGhTQnl0MjA2BuV73MC72Q6x6TcC12VCZ6DxrZeWN"
    "nINP62O+bkhYSnMcO1E/zbVfj36flkTx3EvuKZWlaVyWVo523u8f48aO007PkmN1dTY8JiyNBSppgYheK42iQrBCWsn6iv6e6bQX"
    "tKyIRIw0dgLv9x90dEHPgfHenIFpTmVAxSX0w567LoSso5VRI5oKMeuS5ZT+GxSwkAniqZvFgKQvjT7xjicPyC/pG8PHLyB0LrM8"
    "0xqi3+TYTncyz9AXOVpZZU1QcpyYAupELKrpA/6Vkguki9EgauKHIAfwl56oE4+RrgS7EQjba7dHsO7oMFLCJUXwdGEdXUSlu8M6"
    "jB+nbfeWqfSuK9qDA7mkiNGSwTHsuuJOtzo1vLB4Fyz1gwf8HfvqCD9actOY8Fh3vAJdmeOBMIUrfMwqIzteRDrV+jxaozvvZEWS"
    "ASlevOeJbWnKvGyeO59X1lsd7mHCprbOB5O//S/9fVSwwetMi1yd8Z6zm7lxAwxuz4MaLPI0lGhQeSAxumWStBiYWmnebLVWwgPp"
    "BS5oOj6rCjb46Dig0R0HNHLkoTvwPSPN+naDHt/IQUjHMc6R3B3mFRH05eAKrt1EUXOt67qqv83LKc7CRvRhfikvOWH6HJkvsUjT"
    "FVecTLawVCtxU38Mt5E37UAck202bN7n0FppTJZZMLcENU1s+fiybZdN8vnnVyv9oRlU9cXn3P5BrWeaSk/05/8P7b62WOiD++t6"
    "OxYbutCOUE+4GSL4waU6/3Qw2MrZ3AFm1Qb5x6Fl2yEsv50RuLjzKaGsoIlmqWLRazC61TB+k+5jgRqjsUBr3SietaNDdcqfnYly"
    "gtXJ3p5g3mtVUd4kYFVPSu/n7RBrcsSAVFgDxiGI6YqgmmfDktrH7JPyms0U3/Lz85J9qqhnMEl5Xaa0MIuigaMv+hpOLdRHKeHJ"
    "qyel5xg/Eop57bSjNJ0x8ITIhKXVaBL7WA0VH1fFh6CK6/IBCLVjN5OyQI/Kobt8eVA+fvz4iEZ5DAkkAd+f4NAAy5tNLrZdhbWI"
    "zoh7eXCUlMTDOLsJ1+6P1tdDYOrnvLv9yXQXenLqOnNwdDbs0Rh9+Yew0X2MwsQbUjlr7k6PRmPwAxSaFK4alTewU6/Kjno+XteY"
    "vfR1KXP2NFSx/sl1lPfy8xKSmGIq1p3PXVPPMHdoKXHDIbT/1vUq6MDu2cbQq0PodZ+BKBhyf/3dmAc3rJfsAsL7ftVq60+tlFUy"
    "e6p008aGIUgoptCFGqyKKe0up60PwR/y+GiC/9iiJGrTz2pNpDGusrP64Ci5LlXp7TajMrDLVzhpXSbfbARG+8EKvLRsifjZeGtH"
    "YomgtxjsIatgwCFXgEfheKx45D5gt2NrQbBvy9PibBjlg8JZTGVyB57HSY+S4VCqwNgfEfhQaZq2szRPjBFebshdQttQeDIqRzo+"
    "I9KNWFpDujGgHvxZMgMfdj2taT+HtvKHQ/2ocA5QqJvPzRrjDtjhGJQnPFAwEhg+Kx89d0N75tzk6fR5efqsPBsGBrOBhexDb/P5"
    "NVEhUWgC+nAbYhkxs/kB7KDHKW+M5I1G8wONIECABkv76TREp52ct6AxqDlUKDaEBKvOzlC9dC+lCmhvbl568mcpPnOxu9i9lNvp"
    "GUEaOAXk+a4+5a1pramuMWXXZbARroMpo51wjSkLbYu/Dixv9yeRT39qEP+zo38mR1/6mfyyY5P8ENIyOx7ejn+jG53vt3IQuG/o"
    "BHjJONCgfBW5rM3G749+n6dAZu+dKfrt7inxS4Di37kT4h3IfiorBkYgxUYjPl9fEjLgigJs/ZEJ3XeloXN7LZO3ZVdOX6eiG0gU"
    "UT0Y0an9Ko8Ojqza4S+Mi/P0Y256ryqGkSrV8llnBmW2XNmhfpwP9cFB/CEnePwFZ45ybRw5wrDa+svJEfuoot+J+Z3yb+BOoJRr"
    "VBrPO+iasZ/bnQHNKsqLWRJCHF4Dd3Vnw+6mLsNNjVk+zYlEaNQkbeEzU58NoVAGhAKd03RtaJokVyvx0ZvkW3E8B9PGK+h5KUML"
    "rqlNKleUTZtDsmHdv1aqmk9ZoJt4bXmi7xbVtJgVum6Ikovvopa/Kfe0t1iWAWntufczPCa+YMT9DDx4BoXEufDY0W10DJvyQ7Hr"
    "G80pv2nZ542pqPRuPLkm53rYGSKaj4a+bVePRSKsJtYq25qzq7Z3TFgj3PSiQ3h2SzWhpZo8ctA0sRtynuank7Nhlc0HdkrTilKM"
    "dLvT037fFwrOymieNtF6q4jc3lkVr808R29wEhMnHTG5SWT+itbhayI1B3pOHxeqNfRmSJt875Hx+9zO9/scNPdVMdUNHBHkzmWR"
    "e3T5Q+99IvhqR52/hjYznFm2Qct/7IkK09/zyDqwfFVYAHpVZK8K2mSGX7BNJLiEN36NeGdtNvVgQiSD8CcBiwEViN20oJrdEVkF"
    "TrFlNM57LZOE3YYLRqvm67zZOp1SOAZvYWgn6gxonPkX0MSMRb8rreoWYGd8ddBMbsax+q1kuQXNyndloDz2vntN9TOjFGa9ZnPa"
    "wcm4uS0n4214T1juqJv97HhSfz/47yWdUv1EJJ5zSDRXAoYFq5KJp076geb/eFnBkGvGa1cxME1S9rJOfbMH028QU82w50bXYGy1"
    "4RsF57m925vaD8SZvrf4YPEI/D4YCQoeRchCT0JLLQkIhyue+tRdFTH/vRRRAgotQI1w/7jb2SqQM7FBLBF0SzXL8VW/D4vhZqnL"
    "BkYHPFgeFWRyQPfhx9a/fpvB8ybzH4R4VwMvIeb6y9AbBx35i/D9IdqMmEJZgnRU3Bvastz1y9TIqFdeSaai8rNsJgj9Mk6mgEDa"
    "cJfBPW/Z1d83Lg7AVRfiqBuew4yF23gwpveaNXFYalsT0CeGwauhGJoPGcRzeBAVn67M/+MO0bpA1ZW5cGhSgrWCTh/5PA6U86uo"
    "c51urR4tq27CLwycx2Un1sOhcfcRSWhZvBumcC2tz9w1n9l7bd25TyhrZ9Q9umLVrboWAhHmAG/1XCPEhSokkdfF+FCegjyxz+zm"
    "GFaLQTFIJLgMHkyBqg6iDZy8++b5XAMu4JZcEI2cwp1M1YQf/Zi3lz/+YLJCk6Kd7zvl1KTeDf3AFFllJ+cC7G2b4aaExTpJSYdN"
    "na4R6SMZ22kYq3BS4EOeIGiimya0FxLCRM0FrSwmyUotJ8lULc8nyUxVyZo6qenrpfpjpevbE4371apOFkqOireEm5NL83JcLdD/"
    "5EIJin4FudNou03n6iotanbSUC2h0TW9pb4Wk+PLYj6lksntlg7xc48CaE83l/lSv6BN1j/6iqXNg4kpLfrWtu/xVt1A+SuYLmpK"
    "26ZwddUS+tdtOnHJkD/n6YL3jLpUS3EvXjGyuLqAKi4s37NKXhPOWNASLeaU19SsDh5VLo193RSDojl+zj5vJgSPrZn3t9x2wwrq"
    "d6Rb05U4Zh0/7DfcB7BYKY9pxUQNAibKJ4Gzfns509aBx+PYpHjnxcFEWKpqFIG8gPrm8Jynm07ZcnJZ1bYxIp5u5JKwrb3gmbBr"
    "C12tobg7ZsrYOenQ8/SSnS7Q+WRqk4ShyJaZvFRL6M0yOvKQQBw3/DQTup4W5cXTGh/H6xOvqLq9ohk9j0TDHj1s0cNY3URCPa65"
    "dQzJuWcwHbDjomPQzRL6s4rXq8D9WjhdYbutgZoTONF3MMRvQzm5bAmXqS5d2hPbh/BVXXQgc5ReZCVtrHP6rZNLq+rEILfZEAQu"
    "PQRKjgG3zaZB5i4M3mYRe/fobi11q0Z2s8TELfCaYwqTyWbD1uaUf+62E8GauoovMrNAwDvmwaQQGmIJkX0xvlfkJUiPk1UdCZqZ"
    "qyN/exC1+xXGVGOkd1pEugWxiYMY2rnMKvvJV9yOIbLmikYmpMkFIQ3kLGmDcw8YeK5wQwSH+lfWB/Z6tSA2ijCdpCYFFRDCeu1Q"
    "EJFXFvkQUyVwRaRWABPJXIVLTWhUXoFK0W/cMRN5AgCY4dYMxNgSABOC5iXYwrthk2g4oJZoTpuMQJhdZBTRJFY9fLSkpSRwqOAb"
    "rXvQNru8KBHo8B88rGk3YvgL1esVu0CDSeLJWNXq8nYKjexkWocaI7WdPX9E1PQNzR4h1ofxGpJfCY4UTBLR1t0ExvbKJ5p9wqnl"
    "zu4RBX09p7UwC9Aov0ATv0BzM+MrzPg0RU8eYnanaL6SynttbZzI4yaBiANalxV21GR/CufhFNIK0Ozx0B/GQ66y2aHVp3XngMUM"
    "sVeb4nxOOI66HxyOzc6xOlFmMufh+bqi5SAq2yttiJhCEF7geFDcstUD8E5vb9m78NeSOiD2HBMxtsfPPQ4Ock9mchx3sV3tWfz9"
    "D+0n6x1cB+p+NF/mOziQoDJqdxZSPBpv67SK6pC3NW4QHAqfRhWroom6v7Vw3gpP0AbHukUOtB8uQ0IDy76QiZqkC+7eZrMYzIq6"
    "aRnWh+0OnRFdZtHSHHnRAhV2O0+f15TeqhUhlUYO3kUmt2vwQeP6zj3/t1XAoGaCKUIp2ot2jLE56y4NMgOhvNtT082dg2qnMe5H"
    "EAIlDxbFnPtMaM/qdF77/b3s0PZEerU37s5g1XpNIXa4nLF+kJ6zUMxUKjpD4VYv9vYzYBX2MMO4A7JHAGEiPJ60bV2crwj9jQGE"
    "B1cH1XUJdyol+CxQdsb/oGysIXrWucZZBBsxoFg8hMqUlUy6VLtnNyfbictPy/osrVgdq45yOm4gbiRsotlGpuI5vAy4k7nOr/Tx"
    "OVV8EaTSttc1Uv1Mj7w1wbpoTBwvhHgqmh+oDmAMfjFXn+Z9LlnvgESaxKgRONb7mzqKhIh2NcLjXKy+CzJ8hZIneptXdXr6wvRN"
    "sdrLmbqtIaMkbGUipOXLJexlniK4X16qJXTRGvTaplSlRBd7juEmV3S6lsHjkxk97mYdgxGaE28mafI9JkBLQvDI3+9m3fn9E+mo"
    "fBU+o4b9zLCOrTp3DNXTvNFviTRtColZJ8fLbQ1dzhV24bqZV22TtFu7YSAXI/gceQuQyGuzsoML2AD0+6/ryL1FrI8izrnstVB2"
    "Q8c0bK6a1fnbWuvs2ygOxF29PHQOWBn7F1mrZpuKmfDAAZIVeb0lCLYuBZ7zM+qa7GfP0+s6mhBdWEMKMOE7Adqwz4j2eIaMuZVm"
    "ug72+1ShexN6m+iw8MveyzxaEVbs9z+GRe0moBZXtkX6+hle2ZMFgv2t2oMCvHPQFWdV7scJMQ8hIgcmjlvqlDlSuNP8UJ27qx9R"
    "1DLaY/5qNBBudcrDAk4E9vDCBrFPqUSGxCg7yBQq7l7YJ+JKjEhYyXzzAIvygMbYHWDGvsfzWzMUxyELMB2Dh13RVJ0a1wMr9mJ6"
    "ltKsnV4SzuJ+A7jk1cjNTY/mUrWe7vapm2EGH8X/7rtt4h55DmjtrQKoc4MSap/e1IE9w+nh2TCIM/U4cCwuAT5ZhSNY+TXhbkdL"
    "WLERe42o0/PgMDv2h9l6B3GCRCRUL4GCuOowWA+dYXcEPlSijyXFoZETXiFd1537lLXBlYXiTZkHyLICCHYxZeMQ5aSLJ+f7aHK1"
    "gyVnDkkuuzhysY8iL3cx5IVHkKNd/HgHejTSGuvsgiFO3QAWOVrOiZNeET44FxWZ/2V3UMc7cq329OhseGKikIpY0zhig0xP4OBR"
    "Cv8j0OELUjhhC93L9f7EqnM/p9Yqtk4bxnKlPxKNTk6dXhBDLRSv5f2xVYjiwg+HixCy4eb0/My4g3iZsxmn9yGk5yg8lFhyVv+G"
    "N7aWyycpsIUkj3p+QrsWmhzst056SZ+iAWjMhFi9Tid0JhAApKtPDmC02aDQ1WaDcrebzaozHLGY6h0N29MLQgGQIkEe1QBP0uRn"
    "FU0fOkPT2dnXcN7QSYAmLldhb9m4h9OUE0PdSuK26+yYx6imZ1Byhmc0rqL1N40d+GFdDtSDeb+QeVdlh05xqJ5O1ZNoxn02S8OD"
    "A34raXBE40c5X+1CrzMqs0vaBDzANsSBN6fFmegnGayGBDMmogZRdGdM/AVx8TS0JYZW0dAqDG0yr0pnqlOkARLwFmm755EOjwOe"
    "av+KOou70b4Oj4Os82ajw5XB5x0M/u/Xl77zSr46uCd+Wxudpx/qUO88fZeLJpPlvkXhIPjwuf2w1/myZqYf+FYCK8vXoHf8GwzJ"
    "xEN1tVjSBJet13d3SZaAGHYFNq2XB5TG07VRyAWDb+/+zJHT9r94iEuY0tJirpulp84CxuJZ7e5gQzn1VzwU19c1vLRaqjFtnR/4"
    "/a5TfXVtjrZYSCgIaIEyLSPekYc//DqI1GkuuwJtTLhEL5pvWW5D2yYru/JVIidFX1JeIU6TAQ0sGJtmqfLmWIKFd0Ziy/lsQEDT"
    "vMjnc0So/FRhmx+OKiyqBCJoT76gPRkCgh3uuyK8BsCWLLnzPFV+fV7XzsbEYv9T+Fg5/CttW6Mwy6q2DeER0TeqgJxs8LkyfmCe"
    "ONkUyZNKMFjlup9RgSXuTO16EUn/4AFzrMaVKXWxCi80mpilB3CL6wkcvovGLWFje5PQfqvUGn1qoNCBA4AIpa7Aqg4FVrUECzN9"
    "SQ8e3hFy82PtfEPvbbWPdXQHyIp6vhuvPfE6i9bv7y+Xs1P9WHM8PKEVXV0dij5AIk86d+psr9JEwp3pAX62CJnM7Fiitx371yee"
    "v2ZtBacNG+l9reZBMf2p1rPiZrMZX43jB+OD8QNc7TaEKMzD0dmDB0kYJPUDTx5npqc7hR9SYVSiDtXhWaDpGkpXXByMKCrTO5Xl"
    "n5nAf8aQFdaP5SCMDy0inFf13cbtP9VGOTxXlVVFFiV0vetfQ4r2+5RfxhnUpRPIZ/GlEyJhtV7WrLwEH9V5gJj+efQQtzlGdSzH"
    "vfsbUVWeIn0PinxKv+97eRe0dSiZsMkvs1kVBZ/ESc7aM2mV8c1oo9YF0cZ1sgSpvxBt9lqN0tmAFpr9uWfmcb1N5EldUS4D00mL"
    "OLq3YKyvEDX+issXCWJi0iKOFNtKR7egem9crHDYyHOuUQFd9Hj39vv0kC55/l8AxauLaBHHo9PFmZya5/RKc39lE/ylSV2ipDNh"
    "uokWhCs/xmxnZOxfmTOhREobERh+NFVw5JxL3BbdlkS0zNTRQ3U6V6OzwC04Yn8vIXCnZpZCiNHpY4kZyzwTsLi7/uwcl1NXp8uz"
    "ZIQ/N/S62fSo2WxpFKWkE3ypFU/Zn9eE/YEEhiqE10uvxtCwSxlBd0HsgBgNpKfNmUKbPD30jsTOCKgATcvSTsvSutLcmRMcE1x1"
    "m0Vc8bxTLUS4AP87atqd3Xksl6HzuHMlSxTnq+DaZjtsoRlycITU7mVqbY7BFzXf1EYd/ecXAWP8yl0RScARdz8UNhRvEdeMwPeP"
    "lW7al9M5sXty2irOmDDzFqYPgTNe1hLfVXc27Q9VPtW1+sHoVpisovle6+WTOVEOgW6wQWVPa/Z9NlahQ4k/O5nTndynhkpOrR5b"
    "LbpG0wm8uXjdkdJbhXAwiaJ5Jp4Z8iA6RmDC4Sz6jG/8mn1s4kbJk0dS1ERl5CtHSYh/4AtaUTBjHTQcY5CxgJwHpZva7GC13tW7"
    "SpTfyp1kbUR69DpeLcYKo5pE7JC3YM2a3JkxB0G+/LzAgOQotB8sWH8UivPQzoNdLKTZNGn6EpPGBk40cT9bZ5sFFHtKlDov+TZW"
    "hzyJ9bWZeyXZrBhYb8V5nBRW852K8BnzC4NEZFYNar2V8ZvZLMebDXddjAnTx8bfMe7G1K91+gvNwfliHKtv5BmP35vkFT3/Ic94"
    "/M4mo8xvJh3P7+WZ2orV7/Jctxf08rN9mYSy9ftCBwK+sAJ6YtxSYyS6SMfu1IDjK3qfFrVmyrgZ+0o+dGiPgkiaQrEHFfjAEqF5"
    "WexoCJbTTj9+DMzrWXvL1XKEOhJNmC9wnloXQXkq2rIXWB/Jo7B6mIcGPmSl35Wbzfuc1SAtoi547xqdjVQXdgMsCSiYHhOzDwlg"
    "LV7qrtm3F54qHV1LKGjLDBmt2rxgEwXqNF+FQomDUgJqSpItYQOnjVmZ5MGGyYuuB2R0gTYFtXuKJvnBNn8WDP3Vzj4juMaBDruj"
    "yrnurDabC2djV6YEoGwTzXMl/n6B4untd+Mjmb1l0M6eibF1ke6Y+zquoWSPwI5rKB9VQyjyF6clnSxRnTWZidJACTGHTOCnBH+9"
    "LSA0XpDsuKDA5XTJ7irHwjCL70rCdy9pViW0DE3Mo8OYDQf58HN97XSSeqbDnrER117zrv0r6wNc78VxiE0Dg1ldLbC3tTjzYFpt"
    "p8LgPC7Tbmz6oe1nuTenNc+pt1SiOa09NybGSvBsRU2eVmd8M8AN1mfOOpmnw6vzRuwJq4C5pQOcygBcd5Jat5K2xRp6iEy1QBcr"
    "7hpk1aFBlj4FGmfm44wdKA9mpZG6MTTXNgtzkFmcaI60GsHgOClwEBbxdMkHsWq3CUrdpbP/U9fhN06HLIP3hXfEFhAueVc6/W8i"
    "1N0bTjL7TOWc7NJSp2XA07LicCmMZg7v1bQruktqpfROsg9rsc+MtOQz1vzABIACe0lHzJvohWjonD4l/D2v2BkcLoAj2uGqyA4e"
    "Jl99GW8tD96eDWnfVoPRBEpObKlxZK+svAnIS3PKzdlsRLAgfdYUUcX+YomNR3cJP202fKtGL8N5ir7wyOAZoDcicjNrkvHo/rrd"
    "Es8X9eCgMRuPZudjYvQgEsNNQIZAoThwC/a7hHvq7KsvE1jqOGPiu81UJt5MxQWwNHYtu2M8tMuNPswHxvgGFgUDzNmJvBOf6fKI"
    "u2zG1Ku5B48mPD68R4nei5wRSM/z7c9yaLx6mUuvKTpSl9goNvi6J0XHDed2uGMGTixjv//56ZOD388+H8BQA2qU46pM2Lw3aWBa"
    "cJbCfNttWPG3UzCpmZVQVwBLp+NkXjhSTNRc1apId32cCt+zvp+wi9f7es4PxnyAGMH7UB2QNDyp+3J5ywmiM3I/b9vapPCjui/X"
    "uZzCj+o+2EJJYAbxvnQLKWEvqVxV+VS8UNpl1bTy7QQ9XBTmDU/qfrXExHLl51g4dZ+mdGIMaqTgzNLDuF00t4oElveh/PC2mHyU"
    "UjBXfVKKxFobEwZ1nzX3UeC+zYKK+7RIDSZnjzUS9BJ+pFjOcALWl1VuQTXPCnG3uh4lemuso8q7nIn32PPRetLeJOZqnNnnpFC8"
    "Brm5N69UPoEW8jFCbMMEncAvmShPPcB4QcSZp4dnIC3vO5OExiBnb20Td5323TtKnOUHFeWkh4lX4jBJX9qk2iV9YZMqSnJH47To"
    "OnvFeXqkuG5bJJcZXEX5bsGHKg8LrqJqt8QXqgpL1Laqerfgl6p2BS8RWJNTjZ3TNF2hR8TcL/nkCt2ljwW8x+xf1QK4+LyF1oul"
    "maJZOiEImDTNjxVsIzjq9Syd8bluPboM/04XofGbzq08Tdwy+VAeakWctf9wiblm96UGuuy1KUNMEUJRrgBYFUDDxlspeMqzCLOc"
    "MquVFLZ7BecUPmfldL9Zti4uUQi0cO5J+PijuGDfe0dJVLnvxLUu9U66pMMulR1IrrmDRQjIHuQZyJvtVk2MlZmX+tWnE9C70vGJ"
    "A3nZfxPqK42z5AcAkPwW5ndlH/JPTjjyYZC2u7pzajaG09Ug1srtjiES34sbigDOO8Ul6Tj2DqXkA+OHhHFxQphkEMwLHeVE4Xnv"
    "5nc0F2oELMPDy1wJm0BFRrzGnIK5ZiLM35X2LjqMRQ9RNduM/raJeKOHX7VMWyE8nStM6HCj+ItIbqzJBT8agc+qwktjBEmXqXb2"
    "OKIdh08QXlruno/5dOr3r6jOThJRPeNzMIcOygmwTaxFgpOFbi+raUNoURD3RBkrt2SuihIHH3xWcU3TZKYCC81kqawd6UKFRpnJ"
    "hTMrHSknN0luaen927n55Bkd2XV1m9zYKuTyNTmh0pxDZY/VyrrhgF8fOvmmuk5a+/QWnswoq/QJ7NaOkmoaPjxeHOdLWh5KuKbt"
    "VF/pGkJ3jfEWVOJmWTW03zUN+FLXBesB0h7SyrPrREgoz6wndK5KbI4mmett2hq1o1ERreCgjEmExl+SgFRp7HqyMvQlO8RnrjZt"
    "zaWv3K7kLjqk9chcxsMrKS4kRfoNR2xgOSu7X6m6LVW2hgpscZ7+GrEnQGN0KG3h1pYSsN2QSD9BBh+mSU/6eCkhJ1GqcaWozDYe"
    "3hU96TaCmGGtnSMdmAGFVwd4Zz+NtLNys4/RnHavqd7y4CbdYU3i2yKaYEgFS8YCWahOL+kxm5sZI0puuB8dwF09tETYfA/hFLu2"
    "gGEkb5sZdkpHirIygcKmMnPB93CmaBeN2G6oWHRXkT79tVbLWNHDNzWsf+jh+1pd8MMftRrxw5ta3fLDn7U654f7tbrmh58RAZuf"
    "fq8Jrvnpu1qd8MNvtdKS9J54MvjFj3IbVkt3PFfAWEQAfErkGtHPedff0t1rCFHi2q4SC12wRK084940XN6ti7rZbWrbsqBT9iSd"
    "fcym2tcW4ZC05QRhzhjsvbSCmETs5PweTBt2K2qM7OxeTCcQZlMqX4sFrvqs0KrGArLavU7fFqyc7LW8mIewsmCQNMWwSK+YhzCc"
    "5ZhdR/9RRjWLJHBLXts7ej7nwyx5ixX7DM0+Nbfl390fRXd/FH5/JJAapKFHpqvCnqXnZWTOMeO9z7reMTR6nOwk7JgT3Ba7wuV6"
    "3/YTuQY6RAsplIC1guJwB/N7yZSRo2/ZtxUnardhhntyoemeY7CgU4HYB1Zf2lqXYsTm0aEp6olNQ49q2yOO9BV64AoOXGFQ1XpR"
    "3BQl/MCbWCLwotq65EIZRkqIsdwsYrKW5B91faFPWhiyXBBVhFg3aXj/q3CryEqABNM+tNYkbZJe4WxVYT7dqymV4GECgYvPKsLZ"
    "uSHMSFu2MqZqeGtxg6rk4MhFfxCWAUHMrpvCO406MuaYdmx2yDkOt7zf57JE/PL1QhG23nLrUhFa935xsLnamN0r0dZnP+2CHsax"
    "3XInxWkBsS5EqgVxG1B3guADD6qFdlSCv14kxcqWxB8yIXNcGHL3NXWYeFt+sATNs8KTOfQckkTJ88KRNM+LDk3zvHBEjcsxVA29"
    "W7LGZVnqxZc15AslePoFX5ZBtZ4K4mKd1y658rzYpVeeFyFVQgMLqBJ6EyLuY+GoOJojQ8ZdFwHVe9yVhxPJmrnAKT7kHO/WTIch"
    "4sR9lwo9GAQZbbxN2pA8vu6286yIGAWrt0L6em2vwiiEeGd1bSjtMTLmUHxKW5tw4BmjbW/EvS+8fL4j+s9CZ0qnZ5Y0Z0WHs9At"
    "2bPdD+8WBaFM+Nnr3c8CRqDTNMSxHNgU0W3urtvzCVm2hu/U0B9O4XTCelaB814rga+6PmTKTwixdNyVprUxC7IxYezuECJvLzXz"
    "Ci6FAxFoG4ukzGK/onmVAxrf5heERujEoxYW7DmGmJVdXjEhjHY3uqSMjuNAI/m/zutyJwm7oaD310astYYloaCx07Nwr1CVwV4B"
    "E2bdedw1Nx3kHnoEYIyzn8z4Zy9Z7jA/sCKYu5vrwofbdhzTnW2GLm0kFRGKQ9/bEkq9KzEFN0XNlStWBDdTpmGCLlVBAW0CDnGe"
    "8k1Zuh6timnyAWphIzctdLqNBIfWih2o5ESq1LKk1qEKrePI+f/hHOMMOrmoOJyQrL3HG4WRDbCgxebS9t6qVbMX/jc3ZpHwZgVu"
    "A5QgtUWDy6J8IEFxlEuM5vI1uBem6XwRlwXZtIBAeKs5EKDwlAyadKnWQ95860FmB0PCnN5Bk5DBc1xYdxIDGNv/3INf8HkncSun"
    "TyTG02uxkllbBz6jiWYzgs3maRSq+q4CuiIt2HKld5g1xpKbX484eqgN+1L1+3DmsFKIL4sfWGqzj6r5wENBmqsc/mNXekT1j0bp"
    "XM2qaBWoPtFWq0pz5GGuK+cy2x54BBS4bCCStELdFozU0VdYMbGgDpoM7D18YtiH2G3b7iW5881jZnar6lX5a9FemmkJlFuK4asi"
    "nQ87rpi94y/KQ3gxFz1TdvCrYsef2U+FKI8Z9zi0B9kCK0+vofxQpbnGb5O+YLoJk7sqowjCMXMlN4eXADW17bwvo9B5yWl+NpwA"
    "opntn1PJCZwyxcoEEnYHNFyQUVImGjsEUHMTnEm6heCyDWdLoug396jqhqAPfuhWRgyI+Vy5m3fGKzNCHHKtIWLMZdrrRTNcd+Kw"
    "mG02ufmt+Bc9HRM4CLV0f11ux5IdJuZ3JVaSSLTjkkWHmkdLtC6QajReBTUyoEpfqTl+gmxRRjSlHY1rBHPDYEbJimDEK7NtdoPQ"
    "cXbSJ3u3z6FjaHvPaCPaWWB59NCFrXvwIGsg6ptIXLre0TZZy9MhtUOohIHnRWEV9Vrx5UUwzj66xvStSzkQUSe4Nrz+6Pyo6dMx"
    "LgpdwpiVFSgNygp3JOd6J91D7UuBWgkqyBp2gYfbcOkhYwyWnvpJoF3ztTmbcTfYWm5lxhz3ud9/wXcXRrj9P7ScHLMYUSYW7Heu"
    "tgypcSiEDFjZ4OJ0IIoIXC7nclNKNzewOMNOiTXCpqJhmmdstfhs2JvDDwF2iUnnvRfjipKNgeZEoX2lcms5SIUejF8TDhqfGecc"
    "TEAxrGEW3BPIT682bhIhwzbzFKYBdbI7NWnKOLUs7laPfVPsuTUrsx+KpB14IgJR1AM/DYW/fnIxa0U1RnoBj3N0vE5MYICe9yBd"
    "Ox8uZWoahn0RtBYY4TdyR7QdgtVs7XHofCXZBBf3C2exYQ7FuYJ5QbqUhcxn76utV83pTTJm9I3RtfFWFhthfoSwc1keMrcQYwq5"
    "k6C3Obja8POKEG6oA7gvkc9Be+OaBUp7Ap4PEUKNdx/DQtbS9Nd6Oc8p73Mk3f+c76s4aurp4dmgrX6ormEPRxAWP2jdFQ7fhhCO"
    "1xJFV6KshkqHVrKw5iuZVhnn2IplL0R2XdNW4mgwiWFnLSXLdgF8MdwouTKeMJmZzK0IfGUehO50jj/k+nMZ3hwt+K7osivhvoCG"
    "8ihl35yILcFnorh/9+rOVsJabDY1os4Nr9Jv82jlotupqZqpBZyexIgwMdk64YxOWynsDSwzHc3U2g7GDk4GhXsVyhW/BlSTcamQ"
    "TZJv4Xdka7QeaGWdrkN6qG5YkAtvwFfp0+iZcdZwnl5hH9z2+xe91O0z3dEouaXTNDDf2abnQ+0Bv/8/QEWAZVZnqHDc3Ka/FNEt"
    "h0E8hx3SubpVEijOKc2U7PMRFI8UMJZcLDY557xUfjL5sdynfAfDa/4lLOrtVNjgpK6j88Bc55xA7bxTChNwrmgtR/QUaIoWYply"
    "aJX//8Lls5ODtowaX+TQSBIzZmcrwT4UrekV7Z6rg2I2NgqjBjHC2fY2NAfsKF58W3ivUruCWLnm5/A/dDbyS9PeznFQ5sDpNK/Q"
    "FCdUF0P8ybpunvVXvxQ71p776iIVs0+12b3/iwvYlpVba1ESCfjdIFhfETjHW1t2yZl7BRIZyMu0WttL2MCFjzOIgYd7IlBhwQnE"
    "bTY768Ab/66h7ZPXdBBnGJPHxkH1pH90+PDLTvYkMDSrs2+KCH7i5wgyV0n2196BlnG/A1a8+bcgUTqQ+L6IxFKe0Djh2bm/WWeK"
    "J1j0iPAF3+n3aES9ZnCf6AYYjmS9Q3ZpWgEf11mv2my6PTXVBVHavim6vgnDTSyRvq2eXC+9W2fMT1PXaXd9h8/uGoJInKGM1Wmb"
    "0ZiBYXIz5tIH2qUx7/f2+53eyq2CaPmFahIC2IiVziEmcF/QewbH5kWcsJOSwA9qEa3l1NDGlQ8dI9YMD674auOBPYxjYE39BJ+b"
    "wqx7YJ47NnlilhqUdApNRPLRn1pxnPOSjYXh+87oqkue14UXiklM5CWOw12NuLqNL5jvClAvv4npR1ca810Rq/eMMrylUjeMNtX6"
    "XeE36+97Uu17XHue/lZE8dBQtM/kAqe509z+vlQBXUe/Nxh/DMIDGuGpORnqegV0BAyJZhshsq7OiuR7xHZOjFWDnGlFkiujG5Pm"
    "gdPV7s2LwSOFOf1zQzqsPS7hWwUiviUWOAjRbhcJzwhFCIe51eNDZvnYaRcjkaof2HXKotyJGCSqy75zf6suO4tAdHUQGm4fnN9+"
    "a7RdcdkJtw31JSoD7/85ZeC0pZ90ii4fdixtrun0HfL86jwiqoFmaCqq7AbjfKIOg5DWwXIym2Dt62tvnCkX9FCJXbHXQfbEQCQd"
    "bXXUDdUY2M8gfZKJxm9+5mhyaPfU/lUu9nPX3dzqLWtxg2dEHCgisUjpyx1lgTxupU2Wi5kPctzDysjmEt3Xalc1Rrsq8Oda2Pgs"
    "zh/4HmxAM11JtJO4A+bGbpkp2s4aEjKAJcl0mIv62ZSV92PG4r3Ki9amcVafTs/SeRJNzHHNb/tQAl1+2UP9/hxxv1kpX3bTHD08"
    "5Ov0KoiLXUNhfoJwMN1zq9o7t4gp5TiOpw2vBa6vGlXAsotWAjpNDRxdW1lK4Gc27+o7Wx1hUTareh1nlNCRcnfF1r6hdgEKbLHK"
    "3hlLzHZDT1nHR7BsHEC18UUOr2y3LAiNAyRg8RUIjIKXTMCEoNSq6a2dX92CqBhOT83VjbjSJzYpslumhsLjYMKhUuAktGGsumSx"
    "4rYizCbUb09nQKNJdXp0xlJnuKklEpB+hcsWu4aAAK7Fi25+N+tb5uybo3CoOU+LjHiVeuDF6pCeBaxvZUmaymhjW3HUHFh9BjH3"
    "cp/tbZnIXKaiInpKi0kspDSO7d+waA2Gp8Yrsnj/H7Im9i4TXO+ys22HCW7/JhPcMiT3JjSrSzsmYWRzH8W8FEuASbxjYT3Z86pY"
    "0t6bSNyOnG/aoznbXvir9j39GYdPZWZrsMW2MlasqdM5Nt6U7x9wC5EJ01puE3MVwXIJvh7P2ZtMKqTnlGAu/kSgkQcPnOwV6k6I"
    "wsiX0i2r6w+tcq9x5TWGJ0eq1JAQyBEL+DE7HwXS5/HlVIvEwGKl/6AC2u+HZ2muaoLZtFJRDqa8DvZo7Fa9NQFWFunpXM0cfdZd"
    "lUWsFoGpVB7qugfKkz0xvwT0FznrlrPK8lhMm8Yj4r/ts6GFxyrngoGyxrd5nJyCY47PVJUHTjiYPfDBLlrjqeVjZO08clpMeQ4d"
    "aEvoiSNVb1WT77hyYuNHKBLuasNA3sTsVgf3Fw4BYuJj1j+pcgRYx02EhbmiixypV4SMuCzHk2ShaL7DpaHroJlYHGDRJJeHl+mw"
    "2zu3lYho1yuYSxULGAJ/NtNRq7sGy/ULFcgiPSF4vKjji4eePxoNdRbN88i6BuUA1QREo7E9xZvQpBYS9FxCQqspt+3DCRvSvTDi"
    "DuYQKxa9id5gcWcXSu5CTXiEDT8A+clczjAo3tB7aXkqWlrhSmB+YlyBQbyXC0pp0rUNAX+0NSh1h9jAJALk+fbE3DQGRAeh2Tx9"
    "mwc6s+EmWOQdvSu8GqqDNilMgYe4RXr3y/PRyKBj67+1Mn5xLXuMEwh+VZkWN67Jd/yS7vj9nkLGxTkzPJlvOGEZej1dqNAh6iXK"
    "GtOW5IL4F+kPJGXFxDgYSUZYpysBI+vOEXes+Knkx8UMnsg70Wa9ds+zrTFmZ3/ZVnQsTulMfOwiPWZn0LeadWwqiX1uDOzbwJVG"
    "mh48FAoWer877bjyO+kEQTiM9lN3k3APC8En24XtVi4RPPbTJVDuJ2qylLYcIhBWzrBiTuY2g3KRMadYGXOK53lya+fc+G0Vc4ln"
    "eXJ+Z8brPNFZdsM21yDpwrwXSaPtR4HreVPEbotZ/wjxO/fLUc5X2eTOnIiyvtxsZuwbBw4HQ1f3nbLqLW2Pqb3Az7Of6miqjGbk"
    "jArBDFb1WuIL7NazmfYbeKrgwgJ8goG26jYNA5cHbtLhapWYa+IfvGmV+IYK7CW9G3Nfiv1sTxyIIFxrUAXh7vNOk9o6iZH2pkF7"
    "mw2E54yrXENb47HCfi5hZ6wD1zN2FN/xuA8Hv0EJ9kgfwSGztg6Z220nbrs3r8cV4DAuONIwkb3GIbwm2rmKTJR2+IbbqcydSbsV"
    "lVJRI2a75RCCJ3YGtx/ZwJ3WxsqNL+GdW3WfDC/q4x2H6nYBSx3t1houHWYFIKJxo968W+nj5/BjN2flDBbis+hldK4vivInlppD"
    "RdZywTaKgb3ylsJEv5qiOKTLnaE1amUnB/J+I5lYBJv5UnmpZXIBNYiGcSiTh9zldG4MAam+Rb+/GBQcFuGy/3W2xJYI3HBdssPh"
    "6xAgpgL96M6l+MLjTqlRv/+NC3lDJ7RR7EOkDo1a4ShKUD2VJxhYBFaTOP0WMXsTkNtXS8bhynhqXbwvWI0e28eUwldSwiSYckZb"
    "l3oWzTjW8Duc/E+9eiHV+00ezUT7dLfjneBXTHJdpSOin9RFPLzKLgahj8FpnFxQXy8GzgkhXOicXue4iQTAT4VugZkVT7Xpi/Xj"
    "t9lcbTYjEMK56B1wALugd+qq378YaNPY3iS7yFkOiLYI+wNH9wHcmK1A8HUhpEj9V/bNKFOzh72uQ4FAkIn7OkItx7l3XQaRpXUK"
    "Jj4FysDxFx+6jvsQio9oY+5i6+Ci7di6IvKZWFdiI1zfscXTw5AYnaeT4dxLzeeWQSNO9XR+ljbZLwSu9BQn35qH4ZVw5JNuxUCw"
    "hU6t4MYkWn0RkcMyQgwEgCu1G9hkKluPztZyuNqw8xDnFuwrE90ouNa/lOi58nIxFIfuFyB8EZghukgvu3AsShsCyBe4CgCwzBg8"
    "2NeH2onPplx1hxJRoLdHeHAQnB0Kwsnzpz7OYLRKD0VoNTXETkQ4pCx1/e3bH3/o9y/9i433tRhA+ceAB0oErwbX9vvLaC6miVmu"
    "7whnMVUO64DKVhXR/sQda16neQcrST7P3Oqx3NOsIGytoMqzUJccYsWbZ/YfYmvydReN9FKegFioP3IJJrWbHFS+QoxILiD3BwiB"
    "jgcqI79c5mvPRfx/uOghYneBS4sqvQTHx1FqCnMd5+zx0AfwfhVjxu12hSD0OqQkyoCSwBSXASWBKejRUB3J052hKIQ7gSTgrFmA"
    "sC7+AgKNmjZb0tP/fPeYDndvQ1PReL8MTbh7G4hbW/ys0gltvM3mJIff/GmKGHoTZ8dOXOjLnL1TbzaT0G3i/34dZwsibZOStjxI"
    "weAQM4Q+VOjCPW9xJk2g6Ojgqd2Vz/ZYOAthPifUvCA8RqyfsCogkzuf1Z8S61bsTgLcI7tBgDi632/DU1Eqb3i1aUr9OVhLnjsH"
    "zRFYu6NwC320XVoCU2WpCUOICgGzYs/4syCmTmapP5MX4L7lHu5bqBCRJ5fgLy5Z02WSTexV+yWRF47UyiKclUwcVlA+wMN1h449"
    "hSOVWdDxOFk+PiSQJvqftu/f5K2MvkJKZIFxtB7diWwWJtAUR5YQ/xw9g8sKWhNIyJ2Pun4/DK5zacPLhH3dqsmnaNTuoZc2bkba"
    "rn+9rIC16cAaKRjCFHbByapLpk5wtcGNIUTW6q5dJzsuMOpKfzMSYT712WEr64yhSdFt0XX6FhZeVYRYQVD2aQbsM+yZFs92bI1S"
    "E6lLZFBNiVRuBlMYwoQ9jjxl3THbiRM9keF5ZPYiU0p0JEL357KawzqtBrsiopQZtAi1jwDGJsx70qU2GFIwPAzKaQ8YVQrbeVj2"
    "DDouC2MfWwp8f9CfTu/UUhu5lPVSKGEpUmI8vQt4kUv9rfpM8MuUuKnZp1fNu+UL/EGDu0fbSavOV0mpVkltr6gbc105ARNgjpfz"
    "3MieSxorCxSof0CtGJM2NkulmyIJhR4oxppYEh2f+AIAHYezGfu7K+JkDq3ZofFgl375tTIZTgdU5L+iinuRS+gz1WZ3dixp0wkk"
    "gXPW7Y2m6V5gqU9SSlO+taQtLW2YC8hZ+lTsO9irrlC57imdqSv2n7iIlvbsWdLsHGu4TtR8Viju5gzdXKX2KP0D8IY0pr1mOasU"
    "/FV37QHrDteww0XsFboqBX65MWpmrMeyPl8kdHAjiJ+s+lSxR5KZOCAwPjBf1kZRw03xnKeRuthbMA88QQSCTzFMFZ2brZ87RUN4"
    "puMuSLi9zTP6jDetTeTZEueUwwXidRqvg+KwWGe7CbLhab1tyLcZ35TN+KbsMm9OLvNpdf2GxhnFNlmMrBiPn4AQY3+OMieZ8+/H"
    "c2KVBMx1XbfnljWoRPwRrHIFlCRm5jPEsyjunDu7MZ0ke+jXFNOoeUWjEMc//OdXm82UPTdNnQfC6Z50nIqx5+yc26df9KAb70W1"
    "aZmKZcoW8SmYvxrAosxd3UmoC74c/EGz201bajazvpVS63KGNmC9Ml5kJqzBjZ0vqS9nz4q6vbWZw9WgQGQ2+L7UHBV1EoZdpQn4"
    "sSRCzMPQHK7HlyEi76Dwob00CLSgh9riSRo3I1xeKlHaMJeS7PZxmotza3uoUxIHXH7Bipb32ev55V3nMq63HL+nQ3oag8+C5UgO"
    "FTa0yw7IolkglFkY3wQzw42IuHI9ArU93ZUweW+7M17t9cVfFdsu+l9nzN70+ycoyKAKVYw56H3imwhjIjtb4M+dTSb2Qzakpsq+"
    "lk9B6C2MCGj3G5q7C53eIZIFGths0hIC1bQ02t6Wx+HZMo+zFMFPB4sCCttToF/RCxsuH82GS88LteygFew7nph95wfao5p+uV+G"
    "1LZ92K4eT7MTL8cHxTKLk+toVyY8o2GMPjUM6fpht892JAdH1OHpwZF0efUoJdaH/i6HnoVbicLZyvV+ZXu/EunKS763i+Mrub7b"
    "HUWgxDVcPXiw/XRLM2npE/P0n7U0OzhQy4MDxnGPZ8I8P4L3YuNBEi4FU/1omsG6HMxC4aaAumTw5qdGzXyib1dhWO6ifPV4Gbsx"
    "DmPcw2AO7VUMlfXS10W6Upf0/yI1MbC4E6v0UvqxsuCjP70A2lP1ELLxLTOS1EqUl0fqlhb/PF0eXNKYbyDwOKGEY+PR8Dw2TR5S"
    "k+fc4jGaOjTJCxnGKmTqV3xxe/s4PY/XNLzSjm1o+cCtyM9ZWdD1Li7SC9bEKMXdvNDD1MiIhjvCcEdw+TiLjk9HB5dnEoCRV7w9"
    "HZ2B3k1H5iK/cAoxWdh+Qp8W+HRFIy0epyfZSVokNzhLrria4mwfaNQttcodplPzJrvNo2Nw2NIxHeyTVXpO+2T1GDN1cOBchTxY"
    "KXFRAEbzVD84ggYJ/RBozSylRZu2GPK00qAyA1zY8MvwEugG3pkfHW42MDnSmgadXWF0KPYwTkbUKGSIVyGul5k1V8MExbn1RxaI"
    "z+dec3gVYPOpFaf3v4phX7jvt9zGAHHexBjf+5gNAw5Dulfoqy/jySCIUEoMl8udiLv9KsqF5ehqeaxCvRT6fmVjVVL9VeQi4rah"
    "CwjU+DqPT8zR23FG9pBID0iS5sIsYfbjeSjl7uUIk5LZ7iTRvCMYh/zNZClD+cyNGDsH6ePvUTgwE5xo+XAm0LT0YYwmiCK9svQl"
    "GNLAWCpr4K3YNkUsYWg5luNaxoT92mx60uVhmAp/oibUj+oOT2erKE4Q8Y8rpBc1YQO2LZxLZ/BAhkOLA9zIjPpO3Ho4A9IoPDkh"
    "N7DeOxhuYhsPZJM9Sco8ALtVoLxupctqAlWtl8Sg38APlF5UoDUYOqMpX1RvNqDx7VWw3HOD8m+czxemiX5COFOzu4QyA32EQ9mI"
    "PXjqmRRqb3os4I/aQWD2gsPH2rWuQLeAv8FqeccKPgoMUwWEvgFiM8LhvZfsC33EvAk2c8oOMrt8nKy5sCIjxK9GQ1/FN50dGNyv"
    "itQXdFaw8aw9bGC3u70Mb1VaJzmXkmNu5cvM6A13Igi/hVPtBObg8+DWHnqkL4iUh3SK93TG5BU75jgSbJubUCf9L77+ErozdKBD"
    "Ps0U3MTExu3330KhQy6gXCQBsx7DO6bJWxBuNpebzVUgpR2Fk7Y7XOcTY8zXTZFomzObxuD81hqKWMsp3HDay9o6xJcF2Myczble"
    "mHhZvSJen+vOdJsLJEI962P2gI9S4eYrOvGRik54pDAgRJXmGUcwSTTR7DzQPFuwEp5pMmkgIviPGmDX8TytgQCZCnXriAPUpUPU"
    "1W5T4nGZS1TC8Gh24jeEoTc9oFO1FQsBnahz3dXDMnfef3XhfbMj+Fqfcyhr5uAIeRJzRjjGHEWEZSizUQu42hQPmzcsPae/IpqY"
    "a9blHTRttYTtNOz9XagBohIqZeRmScX+aoPIPZYv80mdDyAhIBCEerHhA3aDkEp80uHKecNXzFRjkCf7WJRgq3PlRwAwrPz9SUVn"
    "HxON1Zm7+tyqY83wuxuyyarwHeu/CHPTDb3kPetabCImyUORgFy6cxbYEnKfkiPAIYKsMznJLtkd0lZdh2v4xkjXvOx3xBPb79/C"
    "o5m8GPTMlmyERK5cxmYjThFRmysifyC0kEKp3kLbxb5mgqsT3QldlYVTATcV3+WQ3BGiS9fL5AqQdKsJlK4I8SVv1aJNVvQ6Sa7V"
    "cpJcarU8n8B/X5kca1XBr+dzrZ45v51wX3rKKWdpEb2FiuTaWFBeaxdunAqI7sCT5TL5sYgo67kOgzxd5pFgIm3O0XYbuq60uh6i"
    "sjcGKi8uSrEvsdZsRtPDFMnLsoLOWVUe3HCqxO0rJ9WUaQT/HPjfumyhKmKnMXDLckHdE/EKdRBbUbpXIu6Q2VZfPFQumseXdByY"
    "jH568MUXNode/hm6UctDa9oI5rSavfd2BK4x973XekQVOCbL98ydA7lGEUgxrBd0OMvZ0yeu9zSg27QWB4dQKx7mXbzZy/evZSJC"
    "MI6UeZQS3Z53tOu+eMgeRbi+lPg2/BJewrHU8r6CjXTwSU8U8q5ythlBSXMj+DxnzyQdzb2jTtVS3FWcewfZ3HXo90Q+PwDC2zx0"
    "VCZmjNjwp4dnHUmSQ06YRbHfmXjDnYl4xAYx3kuNRSEifZSOeTpT8MH1aBKvW3Zur0yknDrgGVF13vGmT+xW/qgaxk2aP6gePz6i"
    "SsrT5ozqyfK0eXCUVGkznDxCan7GNgYgViJugpKoWRoLTGc4SjtXb6tGK1ximB8cPD6kIwrlKoTRhl3Rvpui8+5M7QaAYn2S2Icp"
    "97cybfdWJmuTc2goB47Tchu9LP6LG3XNLvrNeeY/PnEfh3cwHscHiUPb+bs7TTUF58ZeeD4fn6BrhZedQH0mTBFn56y6fiyq6+Kb"
    "29SkrnMfUHyqZ7qu9ZTZrdBZ5luDKBiHdW9jWMG9NbLfxhlcaNYNDBMp5afSatG/2AlxMrsATfw830lub5D8bDd5skDy693kBvFa"
    "1MccZiNP8h2nLi8jzUjqYy7doQJagnqdhjFB4FifyzDZQoU+5qfOJJ0AVI5FHsOPeXrk63+VmyiB8frH/AGRrPoRQf+TnJEntRbq"
    "zQbBFzoWB3sauD/SFsqe5NSo+GZC79SPvK9Q85Pc+TYKfKL90DVwMpVTS392hNJs2OP9VgSaXcEnT4NPuh+86PQ8A1RdQWERKtns"
    "oygJDWdf5l2/aRYlyrUJyAWOFpHypbg42MjTiMMqaGhu6ozXSr1BKhhcuAOejZDf8hOBAJ2XcOi8H/+EvYOOxw+01wzghb9gN1F1"
    "yT/sDW9dJO9osFT7R6p3lvR65TbRwUbgKZSrAROcFBFHnAK5hGs8TNh4RsLDWJy8DuYHbkCtv3s8dwkPxaPq938AYmJunl7e8ItR"
    "aku+LbvKEKJx5kKUBjbrosvuzIn5zarU2VerUCfvLAMQNs4zYUILihKq5dKkTF7DoWnwfAIfMmHCk6B4Y9Tw4UbxMBBD5IEYolah"
    "XhMc/u/IL6QT3jG6jL69obXbem+b0a9Q20G0KgmZSYQ1vNXNiz81TLA4Mlug0LNJEZEz+zqB9yrZYr1KthkVc717DMKiD6560qEV"
    "EPLVbkf2xAkYfpr+GRhW/Jn/NfCY2FxGMbmE4bFGAEvFW82SV++cWkhwCPyaswd92+/c9LsOeRPCI6fUwwJiHbatpoM4sV3muOOd"
    "wJ6qBk+9qKx3Xd7gk8nrZdvEfBSkT9m0h4M0QIMN3uxxOYoIuS1bQVzIt61ouKVvOR7Sldiz/dzyb0+C+YXu8FpRdksv2QbR8OTs"
    "VOgoOc759+HXCSL+xgiZAnuu7Ev2GJc9TFz8mBDXVYLtArctXdz1c2tCgBIzEyfvC/92OqngeSlOdiOXvPN0b+Bh1Zp0Y8+GEN1x"
    "FhHsKmhPQAst+wUeFajBNqavV38DV4iqtbQ3Z4QxZ4QxdwgDcrQZzJnzzHjdMSpSjEni5DRX/HSW8A94e4NcAp3qEMforiJtOCLB"
    "AdQpfujgAZvIb12EYLPktYMa9CB4C9BEwDwH0wsX3c7oNquYIM+OvkqqDf50sUnXCH4PtewrbQV4puPil9Ek+6ruLmmAe0MJokPB"
    "nogLEHEQ/LjfB2yFwZADBB3GPXYFXSBkFZCXSVcLCKYQkB7lduqN7B5Yk6WvaoKuTXQo+4WBsX1xiHXS79fstGalJiYa84p27SrY"
    "Gzht740J1R26TfY0ep4rK1AIduK3fDIbusm7U5QYT8/sJwSuT4O34PPORrZS5YACODd2oxmrhXHYBno0waMcixUnjGJZmRtN2b7a"
    "kPIh3fNLl2LTc6ebo7vM4xEENhCeZzp51zWj+zUP4x4dhq6KaiNotxrMcl4EYU5p75bp0VfDnXBvVH5ciThCblf6X/3T+wux5uns"
    "3UBCRJUmDJbizpQR62YFOYc+RO+6pONtaHXhRsMeAUDvfSFegmFlmr4r2e/LF4gJRjW8K429pwS2okIp/HPRz0MVzNImZTc3Qey4"
    "SzZadt3nrjkDx9YrdrXe7LFVI3P0K3TTqMalZulAQEHQHmHOCMxO3wHl0eGffj0MwsxD6SOgBAJG8xdhZv6W0+LAKcywY4ZSx8ZI"
    "0Gh+x61TDK+tYnhwTJ6aR2UyzwIv6tq7l4mDk/LUPNMn/Hvmv8h3fLfDyhsylYJ4Ryh/Q9FYTuEgfG4Rx3wVn5aZ96KMy/6kSAoL"
    "8KV96Bkqgb8obLwA6BiPbSqadH4EAkfH3zh3DMa2+LzkhP9Rp5R2Jtzi97l4wf0jD33tQoxoN+IfgaMV1joNHNxbu6Q0KrNy8Al8"
    "Dl9AiGi9hoDyj/zBA2Wd8vCBW1gVuLIbkYf14YSic5SolZELjhGhnQQcE4+KwslV56Y0y9dZ30DzlaERXnKmuJGTiiT4Qvjyk8/1"
    "fubsd+L9GCP+hCvk3GXEqphKUfyejiXAeCcckVCrgT+6rvtlyzhYB8y2E97fXQljJ6JlQwchyZvCJ5qBidfFoALnHKPt+rcrOkEl"
    "+CBrxTde6xgpca3TGuNsZhT51bvOMy8dTsId1bV7JKqozmor+aC3Q2VlSoYbCYVK8IbtVOfkxd1MyGsQchgJ5xPDw8jP+UJ+zQ90"
    "bxl8zI9LNg/T3PTBrFJ7YR9Mfdr8NtJZd5RXOPiJ2Eyqrao4vlwKIGCYrigFi5G+LEy8BdZchFbgRMT78JunKt6f743p9O8538W8"
    "zxE1Uv2cq/v50Fybw1ac8G8UKlabfkTilU788nA4Jhge18KYQHsbgYG9l8E6jE7AMVYTOIXAAbsd/pynbTQWi/SXr07ePnl1/Hx0"
    "8vzt2+dvTkaw70fvUijqBQVPTt7slKmr1AiqdOU92qXvczt1P+fiudprQSqrq+o1HmkG2AuFaiu5o3pPTNn7fLeIUV71flSqDoWx"
    "q6v5JferhoDBf1NURvpkRPFERt537Nm+U7utvWSD0TuaG7JnrZoYJToxV2zlr0qipKwma57l3EJsNFyDQKPUDsiIKojHW4XkjaDf"
    "oQ7DeN3pmcvEwGLdK8ZlkVCms0KGwTsVBBLfJRB6d3GpWTQa7OM0AJcVR39k8OTw1RqOnG8J6IgSPVSnLozbGTw73xKnhMo5jjVO"
    "HIT/pboR013UCUwoGtoJHI9HlNjbipYYXLFze87JJS05ZodYdZhgVmKq3Hq7Spm67RYB1VsTvMj4vDy0fqXYXwBR+fUbia1jvQ1H"
    "43/dfHHcO/h/2fvWxrZtZNHPd3+FnZv1khFk6y1LMq1NnKRNmyZpnHS7lRWTFimbjUyqJOVHLJ3ffucBgCAlO9nunnPvh7vnNKbw"
    "xmAwGAzmAf87dFHnPdBibseTyiMx6SoqrzEpL4sRxjZW3uwuOJCZDM0Onb2KZmEUcJdDs3s8NVWUn76OXJVTVGcSIQ8nqDMz8Ewa"
    "m67zwhwtuLXl0gn1ZzJQon3CTVpnhCBFTsuhRySFTJpxR0xiJci2xSzmKJOmzBEjFhqxClFbYIK8OVIcM2bcwth+0pupiZHslWuG"
    "pioc11MG9eRInByGUwYdy4ggyIMblVvuVmZYmmlxn8tyQ/VFHaK2q+4cQBtEli5pS4/hmQqjyY5T1M6UDl0odRGqZIrtSE7cyTO/"
    "6cWePMRIj12LcIUuW3lH5kOex9rhqKwlg4j4YQrXzds33iW+IZLbnj7/gQYpxO0p/jA8iZiTZ3f/rhYwofEZh4P5h8L3KbOFSWwI"
    "Yy80SiFyvPGsqozqmzhecr5AbyGpdmsnfebAqjeGjLfbFLXjJfkPfqZUV/Ag6j9jUqcT4dtKDpvDSIavnisfhXyBZD9cukvUDpS3"
    "oZeeEm+hN1PxTBkL5R7pPasuPUqfx47b3G3vttquOI2V95Gr2JE3vGs4hePrA3cBPDV/72bJAp9jP0ABcjJ6FdsICaotaeu7GEZ4"
    "a7lXaMF3x2loREtRXlcy2vAdDeA2dk5hQziHp6oyFiRNGIyGewbju8iyeX9v7/r6eve6uRsn53uNWq22hy/j4mZjfr3X299DlWz6"
    "56fXrjjWM/LjCUEM5zRUP5hUH8Fmjnd2jtVIpPMXy82CS0A0Mj6+hk0unc2Yiv6cxOpduID8YkPm6+SPJj/OlekGitkGUmSGRUj2"
    "Q3uk6K3G9G/BRCzTPiDKI31zbJ3FKE7MDNWATaVuqFS0loU33zDFN43+epaW/fJ1MMBoeC4JZpLdS+CWw/lMh18LkTojkxyeLeCs"
    "dVW+K/KyGN3cdMUDMNKdYgJCCE+9ooMes5RMI70i6bVHKSCh4N0PyCk+WqGVXPnkpUzzbShnePjh+Mr6d8HfD0crzhPEH4sguT0m"
    "kKCki8ZYSJNjlJJMpoFBEUiZ4FDd666DNjkP5EtWcBXGi1QNK9uFmzubDA3YjtFCNWkMHW6OlhUhBiWsDVmwRlDH8x/VzdhVJTRS"
    "rD+QeolHsWEgfxuzNz/CTPcA/hw+vgtWB7hRD10iThol3QP8kvn06fYDFXsGWp3wvAdSY5faZCeB2rWJciK+Ow0TNWfWNzNTbIpU"
    "Aye83F5GHvBc5a1XhojQsetH8TA2QQCgzlsSX1kLOOnFByBUucTWFS9i1NYJLz3++TzOH8Sv6EX5LRAaOtFYqMQSAfk9SdM+Kw5J"
    "F3VCCaa2ayvhLxJqtT+Sxd/Qi6Rg9ncsSHn5ZRJfHtELiixEqU/pKr2e/iEupCFIvfUmOHlDG5xRaoRUDtfaoNQNTVB6sYWV+Bzz"
    "C84tTA54o6dw4wkwuq7JGTjuBwPsyo/uZySANsbjvZP3dHzGhbP9OBFviF9HfvL3mDgBvBoCsZBe9Yw4AoElQwfh5ZS/V+KnmOPA"
    "y+Iqdn3ush5ZHPXdN+9T1PEGoZ+MS49/3saorZy7KietD0AHishT8OXHyBM57pXLuJPkiBGWccBzXAyGUqXkKoaedNcRIi4UYnUP"
    "t4gfk0KRLHbXUGWGMYDW8GThxCUk8Z1JGUOmsnFKloNcQ5d5oZAaZAF7LgtFYJD4IHbhvEM3p+LcudjZuUDdp1P+qo/FXRw9yy0C"
    "+lcijvjrVn0dYQii2YyiEMcR68/eqK8881iolp7SZPtHDjYmfwSBc6t/5ZXgenOGhrGGAyU+uk6DQtdOIl4Tbzr0+xNbfS/6MTkb"
    "jKzcl46srm0H8AZPxaey2qX8O4dtgO5IbfRagzvLEKSEaD4YIAjYsWJAN8jIHvwOcASOVsTAe76PWRv0NfrICoazvmeLV/xNg/wJ"
    "Yb5cPovJnO0cbeHt/DUdEougx+0BzV8JUqN7FbPTJvqLVvRF4MrCR0bhmfy7oMK8htcsSFCLcE1nn1w5dUyboKrJyz/Oi/3+2INX"
    "EnhrazK0Xkk4/iMmoZFFf4VMzQEUFEw5LLUar+RqAJxuGE4oLzklbh7Jk3UDs0MxwmoNE3H6UUDG0eatHuqcEURW66iWV6mVqmSB"
    "rlNEab5P4ZSg1DEXWpmqRrHSTZNPS0p9AN+XVHxWecS+RPMegp8t6Js2qD1W9/KXcc6DAn7hBTpXDDJvdtOg8PD1SkqGsl04FMLM"
    "2jtJK3uF4M10WaRXj9dhmlH8NyT/VjB6jk/x/NeRYRZtWxYwlJ/+1R6k7UVma1ES9iBfythPJr4iRbtp+CXQA5BGKaYClZw2sJpp"
    "9lSxEy8TIP2MV5uzAtxmePv6EptvG8/icpheQmj/le9UKl9i4UmPDeh1X2ZgxB42NIi2CwuM/Hh4GcQLDD0XGU4bY5FxujT757f3"
    "ycr5hYFIbpe1i+ZEm3DHFRd6dAWbscpNw3B8cQVYg3ANgBe10BRWeEizpk5GlzN+8edYAZXK4hDt29HaaWAMkm2jDmSOSCt13M6w"
    "0OuNG4/OBZmjvB9DV0cyTCzb7cPmoJhJFoa6JjeGEk1cseWS/2MLDqQP8eo5Gl+4KCrUKfLEdlFO+H3MDxcpZ7/IK0zylLzCDCuQ"
    "15cFC8p9gNwUtUoBEh+AnyVF2QV8Qk4MOUrhkK+PL+LhTJZ4gSVg5s5El7B8afLs3WAcPuzDP6xBm7Phh7j/IuYL9dRZDBfcm2q8"
    "r9roS4cFc4dL7OzsnZxZwz4xyRjic4kRGyFBLB/be3BPSzNLgUVFvgZIZrF8dNUvx8o3qEIz30CzKQqgPqge+nODgnwv11LeIXiQ"
    "uRsnOyCtWQ7sqm/CGgbI+5G/ZXlEfgSaaVfgX2LTCk/5cVF7AK4BC+BBhrU+s+mWUhCoiWrd1hGkXAH/t+va9pN60DQe9Y3WLFSI"
    "jK8BTZ8rsYaSb9i7Z7F/i9J/QPnvg/D8wnwNjcvxRZAWYeA0fDoZAqnF8G7j/oj+2Lu/x2FkuYC6JM8kzUa1E40bv3x07kfD0jVX"
    "OSLLkA+mb2LTM350Ne9BMdpx/WGmpBeQ8oO6GbnpRXztmtGWkZ/nSHpwl78zVQlXcI6PfqSQBfRWra4IuAARXHvhTur2S3nIN2Vw"
    "tTsrcCD9f0qRtorr/GCnEaniRtJilOJYsnMUo5aIZz5JKjDyitlAAg1sZ9sOWglYyTAbWklpMIIGQy+4ugu7n/DRCTlE1rhMHYi+"
    "GjsZaxmmgeYU7Ds1QUM+LZPuytDLhgTVPsNQBKM/AMTbvJa/5isHq/Zb7OzBbv60HNgn6RNZH776e3kvP5cxUeoXhKQmSdqKMmoR"
    "GuOR5vodBYrPDNuOLVRMURR24Npl24YaxX5lfUS3D/kyauAAfZUNh0FKrpBQFKOt07VOBcYzDlShgANkmMHJUSaOGCWn55KFxrZ2"
    "zUIhyWO1Z7CNENvohym9fW2fsxv7IVqpq2jEMfB9smhsKK3I+aPOphKFJKNfYd9SPJyKAzNH1eMEL4cfyLMIgO+3mOlopBrK2C9w"
    "aetKTY/BjxSGExuUnsIiYkVwF3nDROFAH1eXFp6UPxVmMEbYzGc8hsWHtd4OL+dxknlR9thY9SBVq066RsDbRpp1iuDirLJz7ZJo"
    "OCQFrkLoyGoVenusZ8hkR50USJY1LX0c02OMq0fjIikqlTb84yZOwq8Wg3ub98jy8CtdkE0Ky92z1Bm5/wjOPof4MvRT/AX+vUzd"
    "sYhSuvrr4ACpyWFEqYyapd32R/Lp4VrFrUL9l2k4y0gDXYYoU2WxtpMMEifG0ZaUivJXC61VFDpZCsdXJSFh4oa2wg26NWGaM5G5"
    "4r13/kYGVfjw4tcPT9+/eEpKOphwHfrZhQpcekFnE7qDPCezLbRx4wAgXnqPpL+3dzMLo89uDrQ4NQWmzg0x2ncJytpNhKFqQACG"
    "0X2n2Jtjy0uFiszYEYobsCW+lAui+4BIKQSi3dVxwKhS3mJZuQG098IT6BTLS44GGzPfMlPTWkKaHrta/qogaAi0XTh+tG086TiU"
    "qgxvY+7FtEXGCKByvZSHXO21EQ3C3Xfv3373/sXxsUuGZbkdYdXV+uIehcF89+HV2zcYf/a8cP5Lj5/ICQMU2K1j6OSLoPxZTy6C"
    "yeez+AaOZmBogcz0NWAGKAoO8fVO+42kaxK35oSwFYcbwY5XdC4TFe2v5ckiw9HIwajpKN1Oiv3jmBqekUNL3NdaaSyu5vgiqAAI"
    "ZApDM/DjnGEbEpGVGyqI4+MZLU6k3sXiTVQ5RMWIHBsmxjbbcE+RHsl18Vmh+KZrk6yBW22RGixXEJo2WX5a9jsiwzIEo0XKV2X4"
    "i/GZMOiOpFaw82I7lmuTaLo6igQUvaSQe8mQJgSHFEU9S9nFXMqG2jPOQt/FMp8vwkxKpykwFmjktHwHvGR4FSyPvDmsbGA/3hNz"
    "yPwEnNQQWI97yuSTu0y1/FVI43ULtTwuSU9immJQkO15ykcAXAJsjhwpggJvIa22olF9rMiFgLniz0LEV3SsraQZwaiBfmEAyYeq"
    "qabdJ3+eKrisjQIPnO9FCqhznjpw9lyGKS4mKYBZtjhll4oXKQzLOk9zX4dYBS3aMnwVu8arUm5LWzhgpHn5Nu6SLLX5j5NXNMIX"
    "Y86BE6FqAirXFII9J45026rsb3O1HDTNf3V5GfghvhPD8emd04V1cH8WX/YjfvAmBahTLDqXFvd8UiXactVzUNG0eLiFOvTSdl47"
    "P+iAYlDMK4rujPjdJj+z7EoqIn6wzbItbf4isTkQOQScU4yezjFJb1O2epxceMlR7MM+tmoYV7Bel06NdXKdk2ul5IZ92OuspR3U"
    "G01xlpqO3rQ/74kTqqcyuuLLe9bwOxYaTuSrMDN3w59VCIM+qSLgdXW5NHY3bD0LoxRjlV2gZHmc47ot6tCWzPtUzgNSd6NiVkxs"
    "e2ipCBa4cPJcKR4aQNhMz8D0g2h/4Kuf/NgMv5fLWDeODiXzinQmq+AFQDSOGbFRMQRNTJVDxtex51NQ8L3R0+pvYylYwHLbyHHA"
    "gGm816TEjT0gHOhcTRZBHlH9FH/y63LCcJ16gC1VNQncIJQiywA5NIBiMHg3BmEmBTMZ/3P7G453qTaDvhVSujmg5qKtD+10Hsxm"
    "BEhV2U+883MKFKVaw7smaTbIBJRFTOIkYQ8D3IwX+XgKk71Lzse9evn+6U8vVCEUp6jvGRwpa6XfvPv4QfcKx2m5gGYLFQDqeh4b"
    "GUR9qSuzKq9++k6V/eXV8xdv1Y+jp29+eXqsfh2//fj+6EXemWJkJSDJKm+73mf4GqbWRWrJmMWuHJFsRvngDbZcNs1aPGHKPteg"
    "/Ui/DV5z0FHYjGaw2cheL8Am1Xh5mGTJDC4N6UU4xSuEN8N/L4PMg0vENVwikMixngJ+GeQUaBS+VUtdimBX/pAqzxaqKcymnMWC"
    "U47hskhQE+IDG1th51hkG5Ulk9mPwa2ggcg0+sZEGJVMgi9MwAHKFPzEpFnA9VxgczJg9Bijg13+ic4ExGXo+7PgwUJ1kSBiPFim"
    "IYIbb6K1P45Shi/eMUf0JAjDccdkr68JVEROQ1L9bkano7at14qgp6gL/1Psp8wRoMkKi8l23dxkEu5/KjK0ZUUkVTN9wLBXimzN"
    "KwWgEdy24PhRzFSCjuzUs4nC3EC1uMIRvwAMCNJJ34V/PNhtIp3DtbSPFlKLed/1kiS+ri7mLkNf/sZvV8JRJtEPV/jxdaSS8NsV"
    "/EjRd9EGjNp2V+J5WorDJuECYP1muEQSxpYLe8AlkUqRs8Aokew8kGLi6Od13B7L5QsOOAY7xc7hwiB5m6KyQB4W7CxdievYFp/T"
    "nBo/TXPrjs845rlnvU151/0Os1Ox8ST1weK72sULZ4o7kqixQap2BkFpWqk7cd6k0m31dmJOD32XnOa+GS7odTRXUQ13lSYaOqnW"
    "P4D50ecEinxQ8+kDX6LqJJMxlZxcGQrGcyIKySF+SvHc07qKQPHgkgysMlx4pMoUtbEmJbqqTmax9xkDcpQEvGgQUb2qevM5ab0C"
    "S7YSaEelwfxTql4Fzd6Of/lOdihBwrxMbm7GynyyDB46sj08S8yGCuVUW1JvKKfltARqscnUV0nL1zS3+qwX+k4HdwayH0aBkv6I"
    "lzoDiOPb60hl8C0qFa90fq7EiZ4Z8pLi9YYic5n5Kn0BF8cgodB879Pc2xIfT8N3zEPcBboU2uxO4mgani/07+skzNT3lZQ2232+"
    "eYov+dZFcoSzZc1eDrb7KmXuO6NA7e/5PpYpDZSXHGuYKwH8X+Ihar++v47amivxzJiN1DnGS41lyWA/JPmhfYPXZCDH7KgKjSNZ"
    "ex3xiKwwRFwoll0ArdpYTnLmPmyxYaJEBna/fJ1SGXyLQr/1gxSotkPGXLNbFqNLt1n4GP9L6hDDvSUjt269AGqZAM37PtWxO7dU"
    "vM6/qI+TRH39L1d85JI67DOg9aHj1hC9Dxy3Z0i4/pHmz+rqNkwz3kIg/gJ89TPP35K0n7WECi3lzmEKF5Rqa1+V9WTZ6b1l97uq"
    "7FNZ9uW9Zdvtwf3Do731HVLX3OHlBlONUqyZTkv6xHGfPjt6/uLld9+/+uHH1z+9efvu5/fHHz7+8o9f//mbdzaBnXp+Ef7+eXYZ"
    "xfM/kjRbXF3f3H6pwUWq1e5093vVUxe2wDgn1sHKtgxa9aMGtTyY/9oCsiqhTWtsua8iwBVYhDO42Hdai2S2xUVd5VCN3gmnsxgK"
    "d56ohvb20c0SQuRjGGX7zBfitYP8M9SEJx3wPhRfJ3a+gxMPJ0DO/srYcO/4cHmAFSKHO4mTHBx0lrEIK04Hfebuo8S/6uyj46RK"
    "Zewkh4fhTqPdpnDDIT4KJztW/eAgtKtfBQTcMELUh9w6C7PUOPNp0f/QRG+aBMGXAI7nJLwMFmHflR/AuCif6zqtCnSxr5Ndgadb"
    "4IeoeFsogulVznAFTjhLiwU4DXiZ0DtPvMtipkx0xdyfXoXBdXkAkFzldBiBl34+i73ELw0AkquU7pKR4HkSlkqoVFece1GW0YCK"
    "JSi9ShmumIZwpnmRd14eDGZUZY4LxOgHckD4z9TptNvNjviVBUOMYT+k9i6Un8G+zLH8t1z05fxKYgwnKDnm/SFl290acaZsp/vX"
    "f6YiMrE72vtnqheZnwF/TrnFx6kDvaBaxaSw1TFzgHGPcbD1roHydUD5elu7vqLJtPU2HdXbY6fZ6Ha6orRls4l5S+Oo7gMeuppj"
    "c/9JNIiMDcZyoh/Ssk11hT1kmXNMcI7ohwx2RjV7AiDIyKuwCjCdGVoFUWEovADNhrEAKv4w+VOD7pP88UU5VAvZoVp5NWgZgGmu"
    "4ELQn0r4JCMja7glIJVqKulWmY40GzkFSShGUyUYBOtzjOjBqBrAHNGISKlXyckhxuTtwoDW3ZVVf0hRU5X+VgDmFAyM1rI2UMP5"
    "hhV4GPwrLVuUMtgfDBSc0F1JRCvLfEtJJgbvR2tkKoyFhUUj5E2MgQJtHoQ40FANFMXfIQwU/8H3tYrlHToMwHDseNUER2mOCN8K"
    "DdPFP9dfFfuryv4Oaqq3ylpv1WJ3sTl56PvntDD7dFJcWNyB6PA8Q4fneA7C8h0GE7RZktIOCtiOyQeFZCVU2a4ZzxaTnM6YeLTu"
    "frA22Ijw6kUG8LyCO3gNMdjwvxohEGD2GzyMN3Z2YI4YIDyX/z6Mhsi1VmFu+C/sk4qVILhJDRv2He0OTfJQQr12qsOWH9yzfxtP"
    "YLxwuO6QmwT6XamPaYKHh/t47G7wRDgzwEgg3QAw2OTUw5LaGhhORY31WEyK5ooTSyKjgRB+AT3Lx0LGvTiwpSJ7w1CnxlATOVTa"
    "cT4uDr5rJPibPEWH+AW7Y0KuoTz8BaVC0UZH6+iukX57og7QJ0U4TuB/Y9FAzV1b5U5kbiraGOFHq4d9qdf7ifjSaNf6ZvUJ1INy"
    "E1sWN4j4XE2B6may7sqhqQ1yKoJt4VgzZmkvaQSw2/DYa9Q7nTZ6Ic9/dmz4fVE8DDfgDR2NjXa9dDA26/nBiEgSjJqANs26pKuP"
    "8WCGnhrlMwbQAs+YInHZJ9pCAe+R18M3iTq9z8uVwUUrLHBWPHHPCygSMRbt3opg9wbWAtqA7wy+5WKHRm5o5jICUIHLibic0JsB"
    "eufKJDpQzS+Q+gVTv9Ar44TdkKX4RTGEJk4ov2b4leRxze5ucM3pIfEWvyj4wxf8IkXJjHML7lFPTWp5Xj4qrgoTh+Z/TjUNu+0/"
    "zn98MX9kRrEVufIyiH0ebmIQIt0Nge6qXM/pDjxM9CAxoWfkU1wW0lUOYe08vXbJMHLO+fTrWzQ0ALExNgC6MTiApTE6gHdheLlb"
    "HnNn305KNyPySFfQ8GZczBF6F602mAZYGSLs4WGXRzygn0690d2hLyntWz8jiF3cSKylWUzjSTRe0h+goweA2jlpZh2ZlMhLeZih"
    "Q2QH0MxDkvM4RdwKCRsBFUObUojiQLmYCM1E/krp10zirofYVRr3HZGMbCPJQCKIOMV1J3YO6wW1Bx3MqAMPnVVQLzMgG7ZYy7aH"
    "M/wBbDq7mrS2rfrOf00wDWiIjbpi+JruxJhiC0CJGSBCUsZN6gDlyLkT17MilYKVn1DnQGBaiqYBdbP59Wk7KN4KR3+Xd5U97CNK"
    "9VVlvPXCB9pV79GFcWseA6JsTeHCGPhbGSqfhVkI98k0cO17buc3xukCO4H/PzBgOKNxAuoTuQDYLBS9+cJU+nhSJrqjRrMrGvW6"
    "aLTaotcQjY7o9UR9X+zvQ3JL1NsdyOqKegfyGvBfq8d/a+Lh/6t3xsbQj0p8FhL0Mp91cLyRzzo83shn1WlC15N7L9Xv8OPjq8Kl"
    "+njzRRp1Bl+U7s5H5fvy8w135HfPX279sn4v/gCfW8/Kd+Hn8PXd2v33O/wu3XZfwo+tn/Ib7oeJElh+RbIq1QZQe0+D/oVJ0z9M"
    "rOsJbMDh9QT4pBxIOaF7Xir+BzLMwz/wqUFqaeZl39KB4OhW7Lv0OpQCyAkguStN0vpSLP34LlttyW2xFaZbnL3rDqgwQHdyf9kQ"
    "ripZukWFtmCyYezvbr0PEJ3TGO/B8dbnIJhvLVIUwGQXUOUKvanHkWo/uJmHSeBv7sGPg3QrirOtSQzVivVlN162JZELXxmTQGzF"
    "yRY+EMGY/AAH4KkqW0kwC6BPfwufhGDot/Ei2WJl6FT6GVDDyrxLmM5940rD88hD5R2GAUmcVM3rJI7OUSTiLyaZrv5684ywVVXx"
    "MkwRSrrKm1j39zm43VLCdBg+7NhCTTmCe1fp0pvh63igxwioolu7txaPUhWDqsrCdyNEMoBHurWIPkcA+12XFaM+T5zRqF6vd5rt"
    "Rqu2L5qdWq/b6bba+2Mxqu/3eq1Wt9Wqi06tsd+rdxttSG7WWr1mo9nq1kWz12m19lvNXg/Tew1gj3vtbhNIYLfZ6LXbLWym16n3"
    "9rvQhYAegCDut7oNbL1d2+91a71eUzRr7eZ+s9XoYPNAUZswnG4LKGmvCYOpt7vYfGO/W+t2mo0GdNvptGCg7U4Nu+00Ws39em2/"
    "JhrdZmt/v9nstTC9Xmv39lu1uoDptXq9TruF3XZq3Uaj3ejuizpMolOHNrF0HXrf38eBima7V8M5Uiv1HpzK3f0m0PVWrbNf32/A"
    "SHE0MBFIb9SQ8Neb0FCdkjt1GAGMpik6zeZ+rdmsd3EsjdY+kP82jBHg1uvC5DoIGmir3ezVcJANYPY79SZDvlWD0nB+dFsCVwAW"
    "qEkg6LSgOnQrAPz1RqfR7TZpSq19mEYDkmuQCWvQxORutwYHZ2+/KeqtXrvXq/VqdZwRnEUA+zqcRvX9NrRYbzTbtB7tNq4PnGYw"
    "6Hajvg8AIgj0OjUA4D6caACfHhRq4pyg7VajUdvfh/K9Xq9bh155naBqEwbaE91Op4sr0MHkXrsBLe0DkjXacM/ptfZpWZuANM16"
    "s4PY1AB4NbuwrpgOMG13AQVh/WrNVqsNs6H09n6rDbhAZ2+nA83IaQGIGh3Cpm57v9no8DrBIjRa0EobTlao1O01sREAdRPwoAap"
    "dVitLgysRRBr4iDrAJk2IBj02SQcaPRaXfjuYnqjsV8DvCaIAfoDQjR6uHqAg9gX9gkwbAMIurUarhM02YU1Jkju4xrX2jileguX"
    "d79GuIRLBTgPxz8gVLfdqxOqwk7oIJIDqwEAqHVhiQnwXcDO/TbsNijeq+13mi3aCAB4wFuYLUCyjlBqNQg9mo12D6oAXgBqw55o"
    "wz4jpARkA+TvdnE4HRhErUY42a7DercBKkgNOpAIndM+q9VgLvs14G5azQbQAhgQ4WoP2qkDekF6pwuL2aad0+jCAKCPlthvww7s"
    "AbixNIwQ0bYFY4SmgY1q41TbNVzJTr0DuxL2OPTeQwgDmsAI2sBMQTnYfoDOOCPY44Bw+10YYXcfpgTECdvuQbUm0B+YfxPgX+u2"
    "CF6Axg3cfcCdAZ2AgTdbNVqmNi4RALyJ+6YJSNajTuvdFrTd7HZ7CACAaWef6BsMCUaCGxPQoIsbCjYRThRhDitSR2zCHdfoNRCQ"
    "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"
    "tTH5UXjNnqgSg1aqOo15Ca1Cf5Zq4b/fBXcXM8DbXJZMWkFItUf832TqD/Eqrx7+wjiMmtPUBrIquGXuEfweXjv+11lfkcI9T9jP"
    "ZysruSn3/XY35b7/O92U+z59U+79mR61kO/J/cJ/fuU/36XuyH237R25+RT0+ujPuR736/bX4378m12P+7HoetwvZ2lcrL+l9kjm"
    "OEnfVRPX1GR2OR36pKffNl3g+jFNgj9+mYt7+/nbPsHyy932gb6ScONL022f7zfc9qFaTNXff/HbPt//+bd9omX/X2dSnguV7Nn3"
    "IvV3dqmZihMtkl3zUuMnKiGinOHOkbgajn7RZ6QW89/otzHa9KgiIXlUTRemjXQwCGcX48lN37sKR6Mg8vJFpFXQ92YBrvvAvLB6"
    "DIKwKAvA4a/FEJE5YzCKA5GIUrROObphDTxZqATYKodqgpNM4G2w3+m9Oq6Iq5R5MJrcyCFSFtx58BTeEGo5lCCZ6YWtMkQPbVif"
    "3oIg/3jS4tvoHd3rJFfIq4W8yg/yAf4DI2JMp5aCOQDh8xn/PTz4UuEJ3ENmFxf80dLIPgvLaY/iI9DllGxM07IloppqEQMm0WNp"
    "Xz2LRMTU9DttqPYD8zHYGFMnjGRwdAy5LQMS4MECsLCBs46uwjEtzbiNYNzH5TJPzBZIVWk8jTywlvrFR508KA+9mSqUPRqoAaUR"
    "ltSkPKEa1RQngADFvZhhjJc3GKwntmep8fGhSFDxIoUfhr7gI04zm/SiIwx/dRTSmNYT5z9YQB2ehSEst3TK8eQ5whxj64Vs78If"
    "z6Gw/eh7aAujGGEKTXkksP/Sj6+ca/+2/GyB93z38V/QNALpHKqpH37lTW89W76lME/i5YoTIvxItSd4zsm/DH6p+KCJL+KvRpMh"
    "GSnO+WR0B4tKYJrxm8m0QiB8XbPnosKvUCGeTI3lX0BDFYL965oCDAr352mosMP+hN+ZUPnr+JNRCZZaIHN1C0nYx8NY/LOsb2sD"
    "fT+KjZP5yTMJRNqouiizM9IgJ7gFjJhnBhZfEkz9k2UXUF2WwosRlym5/ThWNvNLwdoG2kURAy0PcPGhnjDMKEg4Q6XnCzSXpMyj"
    "u1kW3dtiNbdKrF1Y9M2W/ST45yKOJ9HW0T9hvHMMVCfWyMkHkBuzypwkqb5i/vT4n1Iy9kqsXEyuAmkUmOPp0QiLg3vm4vWly6/z"
    "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"
    "Pz+CGrWlF9RmkXkg5rMSwZZjNxuUET/JcEIbxps4Ootroh29puoKn3gkIRZBiM7aQu9GBoz2Mc4zbhSjlDYL2koH4i2pAb7m4Ntt"
    "D5HG64jctFsVr07pYUQ8PgoHL2qKYykdy+Cc8orBKCWgd5qkHBvypdSFQr31cHIReuO2ZkXcRxtg50V/tFmPq8PBkhfoL38ky0b+"
    "FoCSfogwfgYwR3XaFVfzXU27Sfr/U/fubYoiW/ro//MpquvZZ0/mo1WAimL21NQgqICAiHjBOnV2cgflJnetzu9+APGaZlZ1T8+Z"
    "8+vdu1OCIC4rVqxYsWLFuxQ7VosrSGXLb9OOMqb47LBJe6mr+QwrBOSdkJGVVeLNFhcWllMQx5+R581SCmePUyPuRmb8lXYcHUJe"
    "M/h7Y3TlQfvHH2Wgy4FxaSU/gVLUryNevhqGip73HHbvSoYj3d5u7D3P3zuF35/U/yOxSt8lwW9qGVr4zFl/KYDp/0JQ0AvOee2/"
    "/QbNTlayS+SXQ9Sx2xJOUT0t9Sxyvn49svzj5/JSx3F9LuJJ5yV8073gy8d//DiXSZ4OhA73Dl6KY9XinmaslsfLD29Ufzlov539"
    "Jct1Urt3inZTTnWKV2wt35cQd3peGD3ecoy/F4HuLeJpvz9oX+6262Ss134uOu6U/taLShG5S4nqbvNbtzDeuFfw/t2Ku5c56j+9"
    "MfAz5nz3RtGRL8+ZHp4fLoLgFvC7QRRIVvT4XFnFbq8ffakCGb5bz7XUuLWS3y33HqddhuR9v18npvtl2v280NMFildNvc92v97a"
    "+xSonCcPkunervFOnMjFXz1QP+6iwLOvcz+TlKik3zte1NcHh9rj6RL8fWf+8y3Oah17lePr58g7YNjQXqoFWL53utwWHl49Vg4F"
    "F748v/TZuXOlqSxcWJH5/7euHfA6y6Y9/KVOlr28aPq9Dip22aHfHu77F5SXhy/fHK8tnMu+Psf5M0S8OaI/jMrx8W1H6nseAud7"
    "FNeON+84DVQNqB4/h56j3bv8UXoGuPmCd+MZkKdffl+vjqqvctXvGZx/IVLujcGxKOVgNL0b1vbmyL646V+/Y3F9v95/2fdsnfU/"
    "VeHN6dnbI6j9x3t21a/3XlaRX2vQ4z1yXPDaK0bLx+oTdLr1/Z95+W4tL6e4K3XnKOidRv8n+PU+larGgYVH819t0rE5d05F/6cY"
    "5rqqi3G804aBF9BvYC0eyfOL43JTa0GMEyVK++Iff1Thpg+QlQVp3i36t+iVcCqMQdeC5XIuvj6nuE/ht0+pT9F9/wN89+hZO0/E"
    "/6FKX5+Cai/1Kx/W93yt/rID3GsH2lcr1B9/PD8/1qLfD45kv0GFIqrYr7I9Hm/M/SIfnznqfFntUj85MJT05WCpfvhvlXtWDcpS"
    "H+tSZQB/sAqX0vqxlvdOr89teNcF4Vz2zw7UpAuonHu3Yn96J/Z12htWWffWQ9q9+exg7oPBnBRWAb51v81/r+vl728fTUTvXdx5"
    "2yJ+hVf2z3+6f+p843vhHl5cnLso+P7Ert9x77g6kgDvdhr8XiwVbzvVV/P54ClxAz1Kqk/P/8i3Wf+w1Jd//eNH9PKcz/l9sdMv"
    "cCHqz7b1zVILw4J7sB8EX4MThSKv6Mo//3mb8vDjgHT97OasoBXIBBWO9SmhQPp528/u1avCSHSTdONq90bnSt46LFpvwBnchT24"
    "uJz104te787Yy2rL44M/i7Jww3j3W3i1Fr4BinDDqmdzxS+exhU8fERsuOnJ2XW0wHLSKnfcunZ9FnDc4b7hfRmVy68tRa+XpKtz"
    "tOur1YGmxsqlSl4vUMJydi5wwx5+XAIAu9XF6N/A6nZx8PJYLTzR5/u3Yx/c04JqFQG27yFunRSmssaC1er56pq3rbxyi9r2+DVQ"
    "yHu3gKtl+0yIy/v44fHE4vBU0OAEy1lEiX/rvPtL3qRiOl/nOQ1b8epL/niAL3iFEXm35Js8eQ25dPccPy62ZT+umepNYXfcpZ3J"
    "9FCCZt36+B5FGK4f3bOjyyXqAEBbv/3qMuEEalt/vQX+/Rr04OLadAXpdUvzuvWl9B8vjP9TrUSI876AJyiiu3xy6EAuVt9gteIG"
    "S8HRbyMMSIUzwEF1cS8WB+sSI8+qf7ti+mX6kP/746Xw58//uzr8rkCy7t3vvgATu/v+6bmMHZWv87k6cjOhvFrt5dIV3i1O5Ytl"
    "/wTad2T8V6Dsf4YvTjcYSs/Tdzbvx+sR/7p0Yyrc2B+voAjOWMS5OnoFuF6BhRXDzEj+aTN1d3yLtmg3m4zo8chB2p0LEm45nkEB"
    "wFZ6AhToDy/H46Bjo6+wIyoLrHVAjsgfv36NygXojkS605h//jO281rutCVPu7ZcnMTeV+3WMmU9Vtidef0vJ36tIFIfP689y314"
    "rn94fny5mDw/2TEW5DjOngt/ziuYkpvbHJVj1Dujdx8iJCpuZ5whqcszjFfITxdbrRsuPDLnzzp0YWv61Q5dPn79+vx8H+GkhJqs"
    "X4zW+wvLAQmmWO2fLuFTjvu/Crr7jSIu4b1z6XSLS/P9iILLa2E+JytgWaEA9Hh3Yr/aaL2BGHqHhW8hVj5EXy+F/LkFuWZQskY+"
    "dg/PP8Bcq41Orr2nBeLw7WsM3bIL53cXqZVIuf/JDSjwLSFeU7bK+Jafj10uT9Uad8r7/HwP9ve9yl7n/kmNFQzxVbU//+CmhucT"
    "Pjx6Agl+lxrc5VR+t7oCUPhr9dU1qvFPyfAn+nPVk1sU5/cqus370/G9zX4a4umfqPXuB7820PfqP4Ls/HRW/5Id/eudlfgJfIKu"
    "DJRHY95dIt6f1NVKpD0+Pr1NhGpu3ux63+LFNy4YlCL0uTpfP26W73/w8nzAvM5Vw2kRWumNmu5btl9jTh1evNQvE392jvtKk60C"
    "jHyvcLu+fX/XNHyr31Sbqmtp7JYm1HLbE5RuLMXJDHZE1j/CLL7q/G8n58ky7/07rPevVn/9rcI9+QtHN0eF+eky9bfKPPWGJeKt"
    "xt/H0C/2P5XrD56vstydcZ/bD4UKXsVxqvxwj1GdThhVVwQ58O0Vnku9DJxUfX0IonSYOVXS60BQ1al54cVy/lVYJ0pN6T2p8l4k"
    "otP7x6/P/3eGgpXGUiZVRb9PiIIWl6FA7sJEHFtwq+4d8IFK5OhrjnqLkKcoJFe13CdN/bns7XP9vs/ObcCmX6dUxdBn48xf3MGU"
    "Ds+X8Sl+wnJvckBlIfjp58+Fb4dkf3quXTlZvpVeevJU4ZyTMoya5ReXut3kYCYoQ0LlyaX+XTLgNKvPb/BnZ2mdK0t/2u7qZc4y"
    "cAaT1ou/pV76hKb1wtQcPrG7OmZqSZCTorjkiKf1qW+5hd8GbtQPyszTJq2XMYqehLRexh96wtIi6oDw5duzpT7XKxyL5+915ZRU"
    "4Annf8oRyP9ecGD+dJRT+c9j0ISilIrlygyHEDb5z2JWHuMlXTyUQRGOKVrmS3khp+yFRMmJER6fpZKcqhYqOZWlIqjWIb2SIZc9"
    "sG97cNHA8pvbpl305f+bppaPF7Q6NT0umn56Uk8dKT8op85BOyg+zDPoVYbvdf8661UPjgrNnYqr99HB5e/weERPzJ+r+/KHqGnH"
    "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"
    "4OQyWfZyEmSzb+bFwiJmPh6CKx+zMPDxmAf49vZaVrHr57wZpSr9M59BnTaZnJe3Xp/FO65Q5S8AX4u51xWArDx7/2yf0Cu4jNR/"
    "wEAIgem9QPyPh7KgmH5lYfjN84VwYAqyZMHrTwEW1TwZMCT/bmZ2znErA6mS58WXA18B57bSOZygTzPEc+NXTqS9WJfP7Nw/HrKu"
    "/GfwgksXHPn/5NLK5elLuXoxFkfw6nksijoX65bB05fLCepzKbhEclu9AleIxwXm21crjI8gssqmj6eO807rugjo/mlfDzBjL4YK"
    "vs1ydp6cpUCbRXonY+wl2snLk5ZvDjcY6Q+w5em693DJhbUoMD1L0H5A5ejlucw3qawgH/d5IFznZLks95qRr2T+ahuODWarbyUz"
    "SlWsvokbYLhUgbe/q5nP71hTznzjxbc1PdlyIqA51VdAD8ePOp+18XWyJKt0Spe8PHv8229/P/JofpxdHtUP+PLHx6r3bP74bCtg"
    "N/tcwy2w/d+fvnh32Yetb64uB7iC58td4Nvl28+n3wGYfFyd0ujZjEB+3kiRfCn9tQD8tVOSBVjgZVOqF4/67e0X4T+dcj4olPNB"
    "/wFEhc5X4VsVvQVu1f8KfwOOFZT5X5FvVeQ2ew6PEX5VOv74Ij2YwEf9Up70PgWxl6zRb7+Kn5FvF9F5EZbfXAE6Rltw9TN6e1tB"
    "Ko9u8nh/BQ6Q8qpf+YvfHwVb+nRz/m7Vr9+lp9vHezBgduUBhNVnYn9/fPYJpZf//suSJV34BOaFsmx/+vV7+HTxcYm3/l1+meLX"
    "Y0KvjHqLvJbjPVU/RPPOB0He+vf0t597C1jzt7vnR/HNsqcnEoqviD397QpPCnafvxqSVS8/w/EW3je6d+3zIcfBulLv/GWzp79d"
    "797jU6nav+q+Y+YfvzoapmeG4gXInS+fNlUXfjnfbl2YLF/OQ8Jj5Pv0GpnkiHn8fgwDjsU3jznQ4xU7dZepzEP+FXxIzPJayvGD"
    "w5dA1ez0hwhc5E1JbrkMd7KF2ZvjmtyLMt89FvxeaO19cJdju63e6OXHjWUTzPdOtGdfnr/Nsk0gFmxounmFoms90W1b9jr8cPBw"
    "ySzg05+b1is7hLLMxaUFvc2mQsdMwVNVlfO9Mv+TS5df5W/PdxMdt0oGreIo2hWaG+wN+O/701EyTnHPP/OFnwl/e96Dntvq1+4H"
    "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"
    "cVkjL1gfRNleg/OSXoMFPdveglloKXAZdHxnyrsMlkHMdiZmsvwJVyX9CTdBTdqP0PQo8lK4wS7TYY5YXzPWmvpU8AnefkWQoeCf"
    "+6lOt71c5urKh6+8DW5c02o7FbVIaQMDKSjwS6lqMthuZtQDoTva1VEQ2KZIM7Qwl6EZ4YrkU0bEon1xYybdrzOblPdvqlX5IqPh"
    "PS3B5IdWsm7bVOv6VUb7r8VVWH6sJeNiTTUtXxTGcGrn+KObd2+q5bxgToeoDj1Br3ScW3FDBp10coFXN26qD/Uma0LlHRq03c2f"
    "UXknp6dUvslpG6/QoOleYdN4IWe1jC9yGqbrM2i5X9gyXcdZTdObnLaZTsJ6YdMmnYjnzGbnC2wzLGhzvjAanC98rQl5yTU2YrkJ"
    "rcmNEF7EQu4Z7M8JciBPGfcG29sON/GEQzCiudzLOYLco0ApKYvSNQeqQ46KIgJxqJ+V/+NKJ99OZLLvufIoqBh1Dm2ZV5414GS6"
    "qwJrEN+1/MsTGUUFVh2GjHY/CuXY1dVSmdylIn0lOsexgVFm2kttW2WgyR+MSsaYizMNknbR39VjDCTzdWiTWO1Yr9LA+n3tzRsD"
    "y1I1NoOg51qKVubDRDmlinhv9+/PVUzEOO8CjuG2Eh7bMtfkwei30QONWHikzytKYW+EYEoZjTpZo6fOzbVr/50S9dJm32mZJ2Vt"
    "m3Ildm62aRXr5/T9NUUHtF5ZV/Rq+8En9/6a6hovfJfUZhn5Mn0TbZViX2j7utmJeuDcKTse9KmL45QPtvd2GEul3paKqzQSS1S6"
    "TEvi4UsbtRD14quJJabWiKR+cxXk0bEVs4bo0Y7A4RJXipJSLugWnaSIwiQDZ9Y9E5yaTXv27Nly58Y3Cwr1gPVRbbWY4a19DU/f"
    "tqgO3L3R7ggh+pt9U362FCRyRTuHwBUHqTOWrU+SbgTTyUZcwzmWPFZfqhnqDKPErWuWzOa9sVs9aLr5gSZhpVMQHWTNCZ2fTuia"
    "8HrqJr5i9E1Y06tu4vKZc2CV+ewqJe6oYD4MFN18RuID94jJh931DyoGwvSAdOTjA+kpSC6BKOr85Sv4p/MV/MvV7y9XP5+r31Q1"
    "Wq5wvnNZaZc/6f5Rzt9vE69APSCvt9ht+AX+5er3v+Pql+mQ57k94j4Hl2vKe3tBaZDdpMeKDQqDLk4C90S+tbPByXR0Gn3aWC5T"
    "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"
    "cfu4KV4qw5bX6N/euPvGxYey/PFu30nay8f5/H335nR3dnzhuK3+52L382B+3rHMc+t8d6+xuam2+7vX753Xk+dLo+O489v6oLGY"
    "7x6OXnZ3T46Hwpl03pp/jkbjo8MfQ+l+/0jc/2jC6dU5WbjnpuecbToTZQaS0N724Jmfzx5Hl7vT623xbHlhvX5uHlzt3jzvX/JP"
    "F6efrd3nQw0W4Gvnc/r0+Xg7O787aOzv2cZV5/N22p46lw/H6u729q0n3Qsv05epbH3Un27rh5PWvXj8MLSd673G07NwIjyZD+6L"
    "eOSe3Hvmnbx7OjpsPl7bl1NXVl8/TavderkYb2+/n+wb6lVfcGeTC2uzyYuL2ZHRkp8f7Kfm4rq/t6f/0K2HZ+VRuXw6bnuPT9KL"
    "YmueNd8ztscP0qbwcX7ybF+/3LyO20vn47Y/H58oI6X5aY/qF+dPD64jn5zvqa8HrR+K8Gl7zRfvQ9Ma1q0lftxb78LgTDy5v548"
    "Gc+d5vL2RTaFev9gc/lwc3C2P7TuZxL878i5mVvmmXQsPJ5etJe2NnqxtIXyaMxeP+5vni8vR5/O9dHD5tXj3WR55j68N62Hq01j"
    "AQLQcmYa/Ydzc3zk8vy9e3kzFjvq3e7i8XDP1B5sqTH+OJkd/xi/n45e2wd3rePPW/H5zn2+fzg76Oy+Tw/G/Lx1eDF76HxqrgED"
    "03+aybvt4V3nQ3g40K/k872ry8OFYU4XinjRvNt++Wy+D4TTU8E4Uj5u3pd1/fFD9h6tj/7uk9hpnRq3ev3s/mJ4dLt5em11ri4/"
    "Xvh35fLKtG5s4+SHIU2WTetyfH26fXz7wwad9f307mrRNDVYWK3tqTh2NkFVay8u5auzi+2J9X6jX9sn74cX71L/eH59ejg9bgmN"
    "q+uFcTD7EF+N4Wnn+mpXHx083vONu13t2b26vTBPG4eTqeKah+/y4cvg8uD1/eDHYrYYPbweP5jzyejJfXFODpZ3R9N7aXe3c3Z6"
    "eHd5dnd4//J0erNpaRqMOfKWti6ujo4eh+7i4FB+Mp/27p3OaPtp9/MGNujFw975eacjTx8nT+PPi8lyMBsN7u+mwv7TnfDqHsN5"
    "qT+ZZ2eDz7u78VNj/9B1DW/R3l/yd/fyx5EunN/e3fQXT5fXhrA/H3y+Ps4fhQ9+emMMzravnut7C+PVWT6qoGOfT0+1vtu6Ne/m"
    "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"
    "5dvO39vwE7XBTl7UFrhx54//A6EQIFw="
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
