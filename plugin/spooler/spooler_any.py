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
UI_PAGE_SHA256 = "f10db1d620feb8204c118d08512eabb0deea0f5e884c06605d239c5671eee0e4"
UI_PAGE_BYTES = 1273449
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
    "tZa22bLFPNRpg41qZ+NO78LJuYU98Jh4JjQ5vuMKTY5vuUJQcOkK1Xr3r1C90OIVai196xWCgd96hTxl21eoVnj+J6mXpXfYRVF5"
    "fOvh+xSO7EReeqdlMdWXCrGlF4Kf6vV2LK7XmuQVL0zlT7Fm36Pm1g321DyMqbr3pqMd2QiZCQybSdpJAhZX/hLW6oScGms6PxBr"
    "7r6aMj0/wlex8I0jQ2hRsKDTZDJxK8AyOxUmx3aFCcZ3iOf7c4HMXewiOCr7JFI4WToVC+DJEtfPGsj4/6l7r23JbXRN8H6eoqpX"
    "X5RW6DTJoAlS1TXV9J5BF0FTq6ZF772POnr34d47naRUrbNm5mZSyowIEAQI4DffDwIf3qb+fv6NyP78Np+XfZnRpYIpob/M5H3M"
    "8E0/LfuP76P306eXMu+TgWHRBuPx0yeWrvdXpmfo2Jypc/LTv97XlH6+9nml3p+hX358W2r/QY71kee9rC8ZwF9+TIN6+jc5oF++"
    "bjj941q+bBP9Nw/y+QXBRxZtacJk/JLjg8Tj06a7T1k+mGG+l+V9SdWnXP/4lO0elkk0//N72a2PBSHv2T+y/SbXr7et/bvqv+T8"
    "N5l++TQlm9tvw7gW8XcoVP71jX68s1n8+N8/pis+n872nvjLL7983V/+v+03Xf9v/yt8qx7Ik7pPxulP//GnDy7A//Z5N/f/tv/2"
    "iR3QOpqwq9+06FMRP385z+Dj0tuasvFNit/05j3l579/j9L7E9ngL99bNJL8psxfV/fOVjSdMhi91/K3jzxn+p8/f3+zU3P3VsTf"
    "Pz/DT18q/PG9zb986YL10xb7z7X/Zf7bYb9x9BXng/z9Y2j/xzkWZ7Txdv5jMs7H+w2f9ejHpF2a5INx5M/gjx9MSsuX32/cp5++"
    "v7Hb/mP+59/OW75Wf9hfrW349iifiRZ/+Nr5f5l/+KY355/my88/fy3h/a4PqsH3pv35bz9370/983/+55+Tz6SGyQdr4Ttd4rd9"
    "+z9/Xs4+/ctp3f/xqfPmTh+Lpnib0v/nD194hT9TFp6R7WkM32v860eN4zc1fq5t/Oucj932J/usih3Ht8OI/tf/+qbgPzXLNP/p"
    "86u7P/Vf0j8YTX7+TFP9TuD7hXryQzE+qfkPvxrF3f5Gfmz7/eyJ7eOD/viw7L98k//t179+94zipxArmOe397Z/mrs/Tf2bqXqb"
    "/f6Pd8l+e1n52Sf+j/9DbP/0DmjfcobnhU85fnzPH7wxt/zpo2emjxbnwdnG4E//+I2u/PMvP/ypSea8i9+a/uUh6a8j+0Fr+VmI"
    "v/bJ5w5nP7J+oqb81y/nKH701qfh+uHTOQP4j/8BfeXMf+vcDwn/rV59iMS3Ke/blX/48f0eNehP4Xr/aiXzz5/4ltKxa86afnpP"
    "Jz+/Xj0zAv/XX/7+06P4T/GHdj6/4f8JYf8JX384v55Gt+nP2OqjhP8O/I85md6IU//+qT2fF9h97ZP3Qf3X96U4+V2//vnzmU7/"
    "OOXvc+rPn5I/992vnv5rTfbnmn7NxJP88G2ff5P/0yP/601mP2qd/88vxye/0QH97ethyukpbR9DBf44/u0Txc8Pf23/5/zX9nL5"
    "YfxH+89TIdsvdFzjO2sm88XH/96/Z/bv3iG+ESy/vc79TLH8sTf9/Aw/VvJ/sDb/9Cuv//M/z2LeBOKnf/0Wbf30ZbX+50H58e29"
    "93f8UPy/f40kPh029k3See/2Rr37079+nfN3fMK/Kepvn2iKPh5d/PbS+7nozaf9Lb87Oeu7+T/xVv+Xs3+o6AkS3heBfY+R+vO7"
    "2DcNeOcR+WCteyMW+enztx/eDmV9n8rfz17+PP/0ibv/AyF/p/t+0xF/wGb1yy8fayrfR/yPuLK/0MF9PcHtz7+iV/v2pIfv4PDv"
    "pX5e4vMrHrUfP9G8fsDMv3+vHR+JXwHlt93wicPzK5b8N3m/UGL9uvT2j4mT//x+OM+no8zfTlVp//6PLzTFpztpf/jxg9r0PcM/"
    "f/jp219//V5tnym/fiuzf4Z+xXj+XbX78Xt3/vCZKv2/NgTf0KyPPyafqA9/k/hd7vXkTXU+r7D5nQp+yvzJeCRf6QN+J14/tn/9"
    "9o4PM3PWeZq+v3ySprftT+/EQz98Ihb4cuze/OGp2vcavqOAv1PSjwMHiw+yj7/8NunX9uZv3+3eX3GTv6+l196s6x9w3v0XR+Fr"
    "OZ+Y+M4Wv/18O+XiQ9W/z5f5/0LPfkXa+FsV+EyO+EkJk8+ceV/1qPt8MNG7zr51f/zHtG8nXP4DosLvWrI/Yi/8f0ZM+GuSuC+c"
    "be9raH5q7PP6/StH2Oeph68MW79Rud8Rb33DNVZ9oQz7vBXv0+qsr4X+EbPbF7q075K8/Yos7Veb8T4zoP3zR/JXRGflt7++hm7q"
    "H1GDfabyeicG+1he9Ee0XL9n3/qyxPnz8ubPrFxflsB9mdAJvk7ofK9/39bU/0YWv5Kc/G45/Tc0J99u4X/fIv2xI/or9db7ssPi"
    "G4qdz7w6H5tgv65i+tVmpI8bfs2t83WL+TdsOp8XrX46mu1Nk4OvWv1FzL82/xvCnX9LjfU9kq3vcGH910lw/pAm6/9fVFGf0Mq/"
    "ZYr6yPOJ5u39+/cXcv5Wej+N+tetBpX9h3sU32TmOwrwnvxF/n8rlt/dQvB1Ku+H7z3Sl4vfL/XbpdSfmTd+J3S/hoi/U7XfbNcu"
    "Pm24+DDsn+v6znL1LxX8/bc8JL/eW1B82vfxu8b9mjLm23b9O5aN3zfgc/3T95f2/39d/zcrct9XzZb2xyf56fNu//AL82UVrfqx"
    "ilaz//Zexk9FE2QJsCVh/9cwmBIM+fFR1by5+DxJUq75kIxnTSIO2ZHnH+PtH31j3/8aj92w7mp4JplUC3QANLvICqRLTylExsJh"
    "Zeym9SqMO5fxJOjYxqatg+UVAS91Tp4QkuJNzWPMo5q9M7bZyeJDBSy5s4zJL8l+WyyyeZEqjaud9fCGqmcrhbLjQwrmBr9CjooD"
    "sBhDY/jAV+0moMgg0hEDEAAAXM5/UTt10hQNF0W4ZADw9GE4mhxuBMOALhUnjXDd6RaQ4xOlfsZbmNo4dAlCYGtSvhluBgy4LqpZ"
    "ggZcgRsTcNE6JybJ+mJBh4Gap8v1wZqDTB4kbdpPcGHpsr0U8razNHMn/OHiQIrC1hn5WrjoeWkVoUZWoZ7RBmrlSNniilebwnHw"
    "HNadaZ8mTqISiaz3DoMrbSyK0PWAphZpP8aNvHBldorvMzQqN/XJqykVUtyRdyxjL1CQXKHLDpf3Glm2GPH3XvLXm/vYtk4vTJO/"
    "K2cXFyI0jtug0Derpp+kiWyKWzJP19D13qJSkruqkRbvooNyag3G40xoj+LObYktvtp7w+t6FJG16afcOIMzVqSQFQXAC4KBUe5t"
    "tT26Ac+bvQmXdhdgYr7tYJSUoxFd0pRIgWjG+ccrhCFcapsGSBgb8fjkgl3dVX6GsKaA52NpQRTObQYQBBi1WR8yd/kI9JIBFUdm"
    "Oxwf+2t7rfym2w6rjK7aXDuPRX7s+NStBAuxPG2OymPjMXx97cKUbU0ro69TNAlUyQh1NySv8O67DaNtEVONqvhO/Hhx2WBogQBP"
    "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"
    "L7NquVROs00Vr3S7Y6x/qEiMNZ9YSkkvTAfh8p5SyC03PfBaHiyxw8XsYn8Y4+NZcVze9WKiOj50+W16JjepTqe7rxfzGpcfYyLZ"
    "abfyGF7MZjZJs9Ej2tNhM8FjOWZHUtJsl5rJCTVb0hZTUuTifAxTExOJigGzN6bNc9wwvpJy4pCqSoZkTPiK2GpNFnNBrtXVbHie"
    "6u93h73UG0xjabaqUWWwEC6SBjfTlmEcb4aHh6YgsMqunzOEgn6gNpWlRo6T6ZSCd/dbjEtVmymqzJWbcq1X2TWYvdJV1V0rswNr"
    "HDbFhdWWCeYxrtaYswbWa4ez1XBhGObaYSK3rRCN1NZcWMQqPEnF6iVq2dqSUr5utrPrIb7DrR6Yf8IrtaYQWnqzoPtNIWdKq7yS"
    "TwJqpcxss4jrmFnIEHR3kostV3W8PuFINcOm1Z3Rj6u7ZiKxwBYpftncCZkEVpIbxDS779bAQlY3C0lmLOLzgVDem2U2311ZrBDv"
    "0OxGyNTSxaHEUNVWr9xZjjvxafeQXi0PW1ruynR4ViZmlTF3SA6mYUowpwuiktvEE8teklUEKT7oJgyrzaQ3yUzMaGTm1rSgCdT+"
    "wHLd5aHP0smOsikkl/J4t+HylT3X1K2K0J0RW2CncVulxNBDrCj1lsk00StqvaxRbM+kfmq9xjvhgqKvqFS2W+xtpLXZ76Y3RV1o"
    "h1emqCpUQomti4PJOrYsa5UuvWyTveHePCQWnYGIrzmywRF4tjLM9A+HWTM2TWxq7daqJtX6idlwyR+m6bFZN5tVQc83yh2jXzBo"
    "sAbL9OdbtlOdLmoxMzPZz+sKqw2KZatCzcEkojYGMmMpUmO2HPODLlHo5CqTkjkROun5IrFd90v1WWYzHK83615JXuPzzcpY7Dtj"
    "oZCrYaXheNIuNtP1OK/T3ZJew0ulcO4w13lM27bLXHHK0L1GWpnokmzFlfVY5cbJYmtQ3RRyjNaJ1Q98vkoROiG1FlQ8Paji1YSE"
    "80JjISY1oJPqMbO/VziglRctNmeyOWmxLDQ22/1GbfW6h75Zp9jGLtdslnP75mpblFN1qTVdyavpDqwl+vJ2InOL3KA84wa9rFlJ"
    "7vhGR1DC6d1h0+7Qco2nFo1FIt/aDoUOVm/rKr7NreWiUtzh+QGfSOzq5rjMTHoVOrw6kOqUivETdtrbtpWyzCxm2bw8NchSqdku"
    "iWyxuLVE9TDPSVwtVWGH08RiPKAmYyY+H1jxVPPQ7S6KVBbvczN8WMXam2pr27dqE2tHtIembs4H1XI5bDZNkRe5nCSvGS4cK0+p"
    "cHO6a8WKs2K5yPJrpd6b0jmieKguGZbLWWyJk1YG39xMF5vlXq5YtAWsFD6+aRn9hlavDdtWOJfBGdNcToYxoZRdJqs5Pb3a7NeT"
    "rEXKszh5aMiKHp4MOsm8Uu4O2ny5tOeEerigralih2y1F5OmYCU4uZjFW0tDsqTteFFW+3Q7Kwvxeqw15NVpTy9X4mDVnzcGMWA1"
    "bbbEvoyThUF3sm436C62Wa0n9e5W3ubS/UO8eJjg48KwYmzCQz1MVVoxbdMVKmApHZuuSWJBHYiBWWuUxun8JDFji2w8Dpc7zWxr"
    "ys/yojhnLYHJ0s0DthdiM4PQaKLekLNpFk/kJpVejzGE8bjHMpNOPWeqzBZLTKorIVvPCTJQPGuGHfYzh25P2A14gkiZYTLHzAsi"
    "LswSRdChQa6u10ypUuv3to10ktzVmxSVXW6YKT1VusvJnFqLbKkrssKGYpRed52dtGixtNht1wS5zss7aZ5qVfVsdo6N+1ZmLaaX"
    "g0K/kagne/P0RmxkpgeaHmxbA5avqcvGuiOI03JLCccT9el00tsQh/EyntjE+CS7y+zzYSs93PFtJZ1NCA1yuecaixmRsJJcuFPL"
    "DyfbWj++P+S1RG4rhDf4SkupLVYGa81sWB0ueytSpJbTw2pQXMdnVbonquH8OlUqE/XSQknUa/Nuj29MU81ZnOAL+cxQzk/1RQxX"
    "B01r1YhtF/M4cyhpuXAhIVm7CS2NV5vqKjPr19qxFnloVaaFjCEfYoNdZlhuDcVyw0iQVimfLKptLK8LKiN3MXNPZJdrkVwlJj1h"
    "brJEd5GhBsMEmesMucUwu6XpVataKUJ/6lqSbsfmUk/ftncZfjrnNu1xdrdjDHlMLbrGYCNaQjm9n8SFWlkgqFYxtUjWhs10b8kw"
    "cmPW6QmJVmI+GMQkKay3uNl+WMDnhDlT1mohMwRqXGv3eol0XB6wK61iFsVma7tuWi1uoy6FQsrKD6nhjpj385g5U1e7mbFaWjNC"
    "3+QaSXPBroZ6e5gJ43JcTRpKfZFYGOqmnj0Q7K6cohddtlnFkoPifKnk42Fgz62onbRjgVnSTNfAcrBNFaQM38N3TYXODIgSWcuo"
    "pCKrxmKRqFmd5gYozEQn35Kme2NYXEvWnoxjJXqbI3OksVvPx5lihi5VY9nssjlQS5uauU7lczOzqmNtcoMtM83KHluaeHPT2tDb"
    "QrdIHQ7LGGaptKUTlgI0OVU3jYpC73aKnMkcCsw21k0MykI3McZX6m46J/tNSx+3S0qdxxfr1DCpN/hanohtNvhS0Fd9WbbwRmFj"
    "6nG1sKhI9X1eUidUXTLwA9CZQ2LFFIi1WZ/sarIuWnSC79O1+LJzmNGlOFUfj+X9Mhk76K18V5xspp0dsJvB2imGteLrIr3Jc8ye"
    "xBocFZZ0jLBqWXxeXejpeKY/U7IJBevr7RRbLihtccgqy26CN/ZqIt5atLLhWq5S3TSyYoFdsNMmx26NObvfZliutcn29Cmthqf1"
    "hSYzVaZN0MV5ONuK19IlrLPCab6i9ysbPoXPSlyPrqfq5rLJmuyGNHi9TZrt+bCnWJMp3hOaVmNdq06l/SRnJWIN1hDTOzlTXbSH"
    "imyZWDFJZjNNK9ZbDuOs2F/OLTNuEZvYENi/XAlrylqOXKglrs5n+CLbmhrZxa5EY+wGk6qZetVYseu0pGc2C4KbH7DhLqXEN/X9"
    "vL+vUPq2smnn0olCSlthg35qUBseyoN+vjFItXuHdSo7k2cUO2WEdUtUetMlWZ8wqrgtpLkYTmmJTmzBtsY5ihSUKWMy0x5f5tlW"
    "KbZeTQ3zkJVirVy/V5H2sf002+qQ5T1bYNL1OtkdLjJzRuGN2K4+X7F6edNc7Sm6U0qUW5X2Rk8kB8Q8Zsynh8WuW5CKSjnfoCS6"
    "UCR1hdoN2w2TUaslup2ZbtVOV172mt1uqp6KdfiMVThQYr9Bp/LN1HhVZwdApxtYU7OGFVFv9mI9jpFxcl2useFEOZ3urYlGq0AR"
    "Yyq3T7bX7fZsEu8l82uV3Q3LlXV3nzoY+3Jq2Q7nyRKbrNZZeVlPGkx7w2ZjKTK2m/AYb9b6BzWjK+0xQKB7oDPrpiKTsVwsqXJx"
    "DS9jlUVBlvNSvFowM2UuYy33K4tfJbbmprCRVWpfSZabO3VLlqjKvneIKfFUvJ5Iz+rrPlhuLsB0nWKlQjYlJA2znWrSncxsJReo"
    "XlIOJxJcsj5j6xYG1ncFsanFZ6sxmZikp7V+lm3RyR1p0ePdrqbEi81tNdbWFV62evpQYIiDxZJYc97tVvaDXXoZbhzkxpjTZ3F6"
    "rx+qvbSCV5bizCwT8RwvstUOnSUZLrFIWFz1kK7wtSTeYzeTeCFDiot6W15UGkJMPXQWucq0WJh1Wh1h0a4JYPGWTFXjYHpijOli"
    "2LSm5W5rs8xaBJePm9xmQgLRyq8SrT0PJqhSpRleFPrJmbVrVfhCO1miJaYqx1sDQWLmY5ZjpF0v1xpnwVSxLhT3emGDDwcZzCol"
    "SvlufzBct41+gmztudxgOlBFnW2X6alepQFfrBuLVUXK9rn0kG/2d+HZdLWtt9fJ1QrYbUNNGgzpdRZr7+pWgdUSdLKmbeO5Dk51"
    "1K3EpIR4vjRMJ4Ruv1vbmHK4hK06WYPexPQez65wlU0o8clmWU+3GkAt1sxBvEhUx8umMFzF0tSkscIzGFVrgMECJne3RBTn2dIm"
    "VzHigjKudzNULT/e9jLttVbZtdaDJdnPHVa5bldozlfJWF0qzYR6p0ubpXZuSu5LyRm3rI9XiVU8nN5IEw2sDDNWf7MDlhTF7Q9y"
    "np2l+znLHAv9YaO8r8zMXqc8Tm8LOSW229AV0Ugk0lvKGOPGDhOqMXqzT0u7WTgFCEFr7W4iPrcq4Q5ejyUsvTXlxla8KhV0bbLH"
    "FmaG0hdNIsaOCWCALfFh5zAcSqXJIb1pDvoVhTA7ZVpp5dWWHhaYPmXuB9awly/u0rPe4rCvzOVOeSabDW61oJq7fX9AJSZZSkqw"
    "ilpesrPBlFekDs40reWGHHNTlsvyKt1eZgvDxCycFmbGpFyb8CmryrCxGTsnpXTeOpBzfZdMlS1q34+XSgl8y46n7XoSU1tiLMXr"
    "Vn+xY0tTUSwscyVpGquFsXR5nt2lwHS7oQqavMrXjc02ud2yi9pUzlZ5c5hPc5mNlI5vqF1cazSNZi/RLubk+T4lS2y/sptpmdYk"
    "DfRDqpaWhXmqbeTGtSlJc8XJvDxVlxy1aohikyBTm70EvvAFMSwISofZbZbEeqmau8xWlS1R2c/lqjTMAuPcaptLxcoas/AUaB1e"
    "z+G6nMxzm1axO27uYhkitSSTsXRYqjDKttWWcrEyVpw19xSzp8T5uAw1sGHOhSQ+jvdX1cWMKsS0jt4sr2RjPI3p1RpTqaZ4vKYt"
    "esNCZbAG/Q+3FcXs95MSVelLmwFGLlvzqmwIMs1tmXkJY5OdDleME9V5gg8nsoO+Ge/t8f6YbvBEKtHEDr318KB29lJHmxuVZBFv"
    "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"
    "5KiDbvzd07UHJ3HbV0X2jZX+LW7jv+gzwl9gwkjLwU+Yd6IFma3/+kUZlbWNOq2q+DiCHjaSMg2kwcXNTy932/H/+H+AXvz4vh3/"
    "z//r/42jj3ub7fhhzFbHKQZRmWKGStG3tilzLCCWvrTGaT/F7cZk4BhpgMy8ahmhcOTKHhHTc8ncTEsq8Qi0FqTPO2uh+PgmywHo"
    "M+IR8cJr7wO8tNemAv4NJ0Hyu6lUvqeq5lGjs5usrNTf/piiSnFcqYROtRqr9Y+MdGHCiYhVqHXXozez/I4iDFTvtj1V6Z30Gqzz"
    "GlQRunCJWN5TkTsUrZj6Yq+EqQ/0D+etDKSNr+k6MQxCAU2lDGzhupSUj745iTCboQNAKKFIH2T5A9nu7a3qomPaFEcASJwqTNiZ"
    "oXtNTiMcAP+F64O59l4NU/z58ro3ACJ4fL3K56rbIiYNU2RqqcdESFtusOkKrSvzaUf290yNIidzhEFHbOb/z96bbrmKZOmC//sp"
    "orLy1opYnAgmIeDkzcpmFIhBzELUza4DAgECAWIURMXT9Jv0kzWSy93lfvzEkJV39Z/2iLWOu2HYsLFt9u1te/j528Nr58Xw79A9"
    "A0BafI8uMegx11b7wzXb2S+fDs/7xbwbPJraPm4LV157ffTznQ9f7DyvSoT55TioXqwz/p//+7uZD788PYi6+uXBzI/fzYx5f9I1"
    "4cuTP383s+mXa06D6nVIT3f0V0jwMKTrufHTU9nV7rSeafxS/Oef83vmvtsOdrNTXSe/kk7z/tZ9w7uGu3sk7n0ne2NmfiPvv/xL"
    "OxMveRnp7bB8MmF6Q7q7tcE9Tm01Xsfz4jV0tT++Rzi56UKvDqNPDdVRWd8EjzeNPZfeWzuNL/WfWKv58tF2/hIlN3+tP0/jep/4"
    "tvq98F7b7V9q37Dh+zVxK7vXVV/r3on0rvZz6b3+9qF+/VXd+u4KcqtKv1Z9yWb/pvpz6b2+/zrJe7bct9/jVnavq/QPBLleKr9d"
    "Fe3dCP9Wd9fPS/PVpCd+b9Ij3q8s2ltYnuieEi151tgUfv8uLvA8mHsHX+ng2O+dZxn2Tag36DkezotzzDuI9yuh3+buuuIK58Iv"
    "jzGmHuMNsd/bD6Lz3ZfTuEnP84N3kbXj/0Cgf5Ym7iPV4bPT9ZNbxTv94ftALOz3f/69t/NvLDKuC+LJx/rx8kgQX6NBsd8b818f"
    "GZS8QuO3jutvPLPZ773rwH7NtmM//sFYUS/au9ewUY8z/VCjd1ui8n2J8sEPnx43rPtAqpcQ2qcZlBdXCeJNuKXH3eyJFLeL24fH"
    "N4vcJ/+Uf1ZawGuzV33+6m7s+4bWD2bA9we3k3WWHsd3T1+/Ryv/+kL5NvmM2z3Z8wXDo4ppejDBmsebPo/2iWXufMzIz9ZbT9Fs"
    "30XLeo0Z8kDbl5hzr1/s5WS4f7XTuxxi7z/Zy5nxccCtIfiAJ67eKzOtn6zWknL48VbwcQPsV5YCVxu2F5evjy+N4wdt/2P1dzYR"
    "r31/CtJiXijfjH3zsRXUp2/OcEbr5hWsP8/yqjK7ofcvn5L5OHlb8zm050fT1y4fTP/VN+lb04cfp/9S/d30HwY1I7jPd3t2GPr0"
    "p1n0/PEmIM/M/6ebj3V3OKSXz7f4ih9tVi8qwW+R7yErxdvF/DL/98FunlnnSq8vD3f3jvwaK194UXTbb1u9GizcPMtuiuZ7yL2/"
    "3f/96S4XPLLY6sP3uaeT/4HP3ufsfNVOPzde/O05gPFrO8zT9cZLlU8/x+++5GuM8te3brGmP6r6rD2/KuMl+aNAFM89XcWel1i+"
    "2A/fSAE0y1IPhhxn+RtJI9bXB2/T6T7G3HwIB/oy0X/HHom8+5DIyjWC4/Xq5+WtH7Ff3mvPv8r7s/2wLbU070fIPUT3r+yEX+99"
    "Lyj3MbHqu/3uBfP+gf3u/s49U/CHwZ/ehCd5MaT9VW+FP/1KD78vNslDiNnop/7Te0v8qL37M7xaRr/fid655X5rO3pjlftOi/N2"
    "TxquQuxP/S/PNtV3FcIL6r/LV3ONb1jVPrf1kJv003tL6ZdOfnlMkEN+8uTHZTy37cp/cN9/2Xc+/MhP9NblryL2fvlX2L/+d9Ub"
    "zZv38g3wvc3ziyZT382810bf/fgdnd+uhn98a7H65ytHpM9mE/APv52g+DfY4VmI+yot3DVx0leM8SLdfYzdnh7/2lH38UF6e+1/"
    "I+e86+CrO8T/gD8hf79fIz7yyz/CLW/90b/FLOgb6PLGnfctr8ylzZPO540DwrX4VeX932CT1/ZvfHK7MX9AzddECI/C5lA+BR9v"
    "jR8e07hExj+Vhx4/9y1v5fVu6Tbjn+cRfEDn6xX9VevzsSHT19/7JZPZPRr702p/Qr8fLoQ3GfJe6F0YLzRA/hgj/hZCv2tL7lyp"
    "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"
    "3f8Bm/C85w=="
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
