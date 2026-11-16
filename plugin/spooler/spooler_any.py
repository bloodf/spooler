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


def moon_found(base: str, tools: int, managed: bool) -> dict | None:
    """Note what a poll found on the Klipper printer at base, and return its Printer tab entry (None when no
    preset has that address). A change is sent to the page, whose slots to set by hand follow it."""
    printer = next((p for p in _auto_printers if p["ip"] == base), None)
    if printer is None:
        return None
    # No extruder in the answer (an empty or partial status) says nothing about the toolheads: keep the last count.
    found = {"tools": tools or (_moon_found.get(printer["id"]) or {}).get("tools", 1), "managed": managed}
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
        _slice_picks.extend(picks)
    if changed:
        save_printers(printers)
        bump_printers_rev()
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
    with _printers_lock:
        printers = printers_cfg()
        printer = next((p for p in fill_printers(printers) if p["id"] == pick["printer"]), None)
        if printer is None or (pick["unit"], pick["slot"]) not in fill_places(printer):
            return False  # the printer or its slot is gone since the slice
        place_spool(printers, printer, pick["unit"], pick["slot"], str(spool))
        save_printers(printers)
        bump_printers_rev()
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
UI_PAGE_SHA256 = "a81320298f28a4907ffbe7bce3bca669600c49c2f03701b379587f953c07ebe4"
UI_PAGE_BYTES = 1273162
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
    "6/9n713X2zaSRdH/8xSSxuMBoiZNSvINMs3lKE7iiW9jOVctjQCRkISYAhgQsqRI/L7zEOddzv/zKOdJTl36CjRIyXFm1t7fzmQi"
    "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"
    "6fkRvoqFbxwZQouCBZ0mk4lbAZbZqTA5titMML5DPN+fC2TuYhfBUdknkcLJ0qlYAE+WuH7WQAaq/uIaysaozzvWGt0vk1m6ozV5"
    "rOGbRWcXglYvkpcypAw8zPKkvIykly66MgXR8RRSqzS6IptSlacs9Vb7c4Gm9uwci8tQW7pAby6OkslsQYn+3Dw4be9FPxNdMBB1"
    "QcBFXp+dHqalLsFOPOSjO1mEPcP4ipBJlSy1J4u9Ofw1HVX7vuK7bBBCxblYrZT7bG1R97rkgkJzqZI9+f+pe69l2XUzTfB+nkLq"
    "6AudyFNNMmmSVLVGTe+ZdElXUdOi996nSu8+XNses1VRMTM3s/ZeK5kgCBDAb76fBD7YH8O4lckPKFT+/gv9+MRm8fN///y44uvu"
    "bJ8S//GPf3xfX/6/7Q9d/2//K/qoHijSZkin+Q//8ofPXID/7etq7v9t/+ULO6B1tlHffGjRlyL+9m0/g8+nPuaUTR9S/KE3n1L+"
    "9tcfUXp/IRv8x48mjaS/KfPX1X1iK5ovGYw/1fKXz3mu9D9+Pf6wU0v/UcRfv97Dn79V+POnNv/jWxdsX5bYf639T8tfTvuDo6+8"
    "buSvn4f2f1xjcUUbH/s/ptNyfrrgqx79nHZrm35mHPkj+PNnJqX12/cP7tMvxx/stv+2/Ptfrku+V3/a361t9HErX4kWf/re+X9a"
    "fvpFby5/Xm5/+9v3Ej5d9Zlq8FPT/viXv/Wf7vpv//Eff0y/khqmn1kLP9El/rJv/+ff1qtP/3RZ93/70nlLr09lW3480v/3n77x"
    "Cn+lLLwi28sYfqrxXz/XOP2ixq+1Tf+6FFO//8G+qmKn6WMzov/1v35R8B/adV7+8PXV3R+Gb+mfGU3+9pWm+hOB7zfqyc+K8UXN"
    "f/rVKB72L+THtj/tPbF//qA/f1j2n36R/+Pb3393j+KXECtclo/3tn9Y+j/Mw4ep+nj6/S+fJPvjZeVXn/g//g+x+8MnQPuRM7pO"
    "fMnx86f84Qdzyx8+98z8ucVFeLUx/MO//UZX/v1PP/2hTZeiTz6a/u0m6e8j+5nW8qsQf++Trx3Ofs76hZry7/+4RvFzb30Zrp++"
    "7DOA//wv0HfO/I/O/Szhv9WrzyLxy5RPy5V/+vnTNWo4XML16dBKl7994VvKpr69avrzp3Ty6+vVKyPwf/3pr39+lf8h/tQt1xH+"
    "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"
    "zDBRCXls7i0hpbKYp+xsnp+OzuR5W1teE4rmKr9FdllVry+vToVzDbwbz84uo2TYFWXo+0Uy5FxAKR3iIhM+8Xw2/Iuauer81q7W"
    "5OFSb6wYWO7IFUnivK03V9c2zlmRIg/Zemt1bfNwFUmIE6i8s7oyexYzPbxBvfaqeuowJqTTqoJqu6sPUFltMIzH6uCtr3Hy4sFL"
    "tcpO7/reeo1Yp3fOPBDYvWWL2CzrlZgIQhP1NZqQ5T2nmSA00linESrtFU0Fof6KVZcbhmnNB5VbqysfWWvOhn1ndXUDdMNyy6SJ"
    "dPlw2cphK4XUtfiwkJ+OtRtyONPlSW5qA5pntX02qwPZPF+dZ611uJrHqevgVKelOiLVueg4Ao1TL3/GFQ406wRz+CQzzqeqfRhV"
    "1WGU1wCr5k+UqkWMqybxrdrUtmpMrmsa1dzBtIXSGrlKfl4V5/cbsnnE4J3arN3AstbwaApSXz18Cf/ghGffwezZV+t/sX7/Yv3+"
    "Z2D9ciK/Qxb2cYVkCWNYLoR8JL/YaH8qw9jY/V0MY6PzRzGM5W0KHpKieCwez0k29n4PJ9ms/R5Osln/HZxks/FpnGSz+UmcZLP1"
    "iZxkc+czcJLN9ufgJJu7v5uTbHY+AyfZ3Pt9nGSr9js4yVb9d3GSrcb/4Jwk8WySnyTG4V9c5adylUtOsmrpOfbP4EWDQdW2yPWs"
    "hy5fqbCRi6JQK9iZL6650XJr6uFVPjuGZ4PRmfdkbnVQ5cxFZRv9GhGXK7S8/5KgZv4NPhMuJh99tFJxvwzK7kyFQIPBngVz+5Gt"
    "YETq4J/Xl3qTLJe08lgjsL5g7UF6ubVKstk+/DXeV1FnV8y+2Vbw3bWl2seGezntvsb/3tp9wgDSUvBrNf9wDT/u9l9Kfv9S8vuX"
    "kt+/lPz+peT3LyW/fyn5/ZFKfgqxzLY5TSqaFjcqHHZokwqZkDOpkMl5kwpDrZAksxyW/FsyNbUNSkyPkip6o+Z7RfDGLgdv1Pxr"
    "STXNvwYupSs1cuCeEzX0ViBgzEedtCGFaXpbLKIg1VzV4DSF7nCmyqAvaQqQW7QpgrICsliWnU1wgT48hMruFyXi+TlYHwE7bgRQ"
    "w6tQwL1/JiSIoayJBrlTJSIIhQUbI7wKfHPtL95eV6f0END79ZoMG/923RM7HLCB3l0nabgIfkGrvyzO4JpxEvwMRczNEY5nMZUM"
    "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"
    "rVHq4uEQp4AU2r6HPpEfjDwfZPsemkV+kHg+KPyDGe+r4fb2Pc4ymB0B2jgF6IfaA117Yrdn1+vvV+2v9NtT0dHjqL7O0Ns8krVo"
    "3rXvlTGe73tljGdud9DQl0E2BNxt2EpYxKR4TeQmNnE8b3su9aLc+HYFxg61TnSt67mrcyDaeFLpCyuxMaorrpWls2hLd3O17/Nf"
    "ei+a/9a3+ELi+3LfpHmFwfI+xmpUZO9wEfE61KSqVx0APDxz0IiflTOE8s/J7G+x4rjTONQ1jzod02dodXUkeSADsQ1IuKUo2Ost"
    "RdBoovXALJQuPmMfQ6Vzb2v3Hvu9oDVpblLaSghL5hnT3jPuh3JJ5GdniGXDjlCpCl12Z1P7nnBaY7QoB0KVXrea/5pF0pBNRcsW"
    "8tiO5OQtJXde/AT9oIgYyRvpHSJpittbSYOtr29JA0G5CE2zbFxcpDx+ko0YG6q9PVBVL4wLhdpejGKfoTeCMpHHBgB0bKhxQ7pt"
    "LkQ7og6QXaMstaopLfhhlB5BzdQeCiumD/lViGk1BOwkcrqFpCDO5C7BeKHlwDVzhKmaXmXUMpQdWtqblIQGx1K4jw5SajTD21v1"
    "IDWMqDcVRRiATSapIY0XfCxGKYqlZ0SnkZylCBjPmt9vdgRRgJcXKsGkCBuPT4PLwllLViq+ODX4uMyeshpiCoM4bxXaUYjqYOEe"
    "msO3zJJYKY9Vb4Kjiyb5CJOUUhB0tzHj3R55H6FWWi3RTPdhVKzWmkl9SSqJp6NOlToym+hgTDv02tSyOFoI3YBepV6R5xh7kzSn"
    "WMloUwgzYjUhWaBHbn5eGTgQIJdefCDSnovDnD4sLTwQbQJc3dzpQ5cLNho6EQ1d6s1Ryh1g085yYipRO9q6ETwG8x+XylHMBFvU"
    "vJtN9PuoqEM68to7Yo06JOqjTDpwfFJvfYF+2t+jhsapQf2bncMzik1j9sQx3ogbnl+acKkwY1qKl1Jwbc/rIsknyYCrhFGeakPr"
    "Ef82OPXw6a+51GlJyyFDaW6jqfX1YJQKEDMbiVhp9QWtffPUY2jqlLIXfoDhsabZxUXaz0TkGcN+JkuFwknZMzkjMV8BOwMoamsv"
    "0DUiOVLoBZHGAVmYCTtGMhxBOxPUSShhDlmNwF8y07DNQmhseqWkPVrkWyNxCTCABgcRd+r4w+ohmHhXD0cJg+mR3tDwFMCNKemG"
    "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"
    "Npv3ftdrWIqNb+qsk1YLTcc0lYiCrV0ZfWTbHmKzppVHditv68fxqKaFx3YLX+pbeFzTwhO7hef1LTxJNEvlfX+iu7Da/J3bxEg6"
    "KsIJRsuptPCt0YO/wsmiCj3T5tM3ym/VIBWV8Wa3Gt5nfxctca2ARTJYKWqy040mrJ2BpiVKeKQD0dgAQ3mAX3Wt5Mh7NpgY9na1"
    "nuD3dHGpp0aa36bNJ5uPHhM10jUE8CkSHLu73mxt76x6Iq3X111PijFxsb8QIv9BcbVxjqEEKskMP1abrFF0vHJqXpJg7iolyf+H"
    "3WouNyj+tFufuOynOeN+bfc14Ixrf+zW+Zf8vOtxHvl1Tuefd11Pl9+w5BR95KNf7N7HCXIt8NEDXy/pO7el8p1qKX/nZJwbveMN"
    "uajZjuydd+OTd56NL95513xs1yXdIIrpenpYA/+Xk5ov+/rL03delda7mpVe0aO98H55Xlm9M93ZsVgsvMU20BqkZtEufatz824O"
    "uJ74F+D6XT3EHLzzZArd8k7qqjKp93pSL+f0sf3OTd8II0e2DRiIdx7Y++Lt/nltD64z8+/vPKpIXkH6i77FwGOoUZHGNrlMN67O"
    "b2LP+PfetW3+gWTzTi7B16MA9eNhlJ2hMENrwyfZ8SDJzybJmdLFoDeIyI5zyD4fx3AaKeRSfjwZ4w92VMDArjIERxRzGIxjNkKB"
    "ywY+oXy18egUsyLHFPE6lq4M6IRKJlj0Djl6CmkK78vjHCsCKTVKjkkDOo4d74Qolr5U8BNGBNUwXBj0OsqoDK3S8qLMenj88zaH"
    "XjhWo6YnY+j0bI+filR39MQToJ80dPmAGv9U1aLZHin/MVzB5AJnAMw0h21lYzUzL5yVEy4thXmbmREuU5bztukbObdRB534uyeb"
    "K2dxy1dF9o2V/i1u4b/oM8JfYLJHyzlPmHeiBZmt//pFGZW1jDqNsvgwhB62knEaSIOL6U8v9lvxf/xPoBc/vGvF/+v/+n/i6MPB"
    "dit+ELPVcYoBUGaYXVL0rW3KHAuI1c+NUdpLcbsxkTdGCSAzr0o2Jxy5skfE1Foyr9KqShoCrQXps/ZmKD6eZjkAfUY8Il54rUOA"
    "l9bmTMC/4eBHfjelytVUVjxqdGaS9fXq2x9TVCmOSpWMqVJjo/qRkepLOBGxCrXqevR6nt9RhEHm3bZnKjWTXoMmr0EZoQuXiMM9"
    "E3k/0YqpJ/ZKmPpA/3DexoG08TVdJwZBKKBpLINSuC4l44ffnEWYidABIJRQpCtZviLbvb1VXbRNm+IIAInTfAk7M3SvyWmEfeC/"
    "cH0wT97LQYo/X9x0+0AEj242+Fx1GsSkYXpLLfWYCGnLFJsu0boyn7Vlf0/VKHIyR+i3xWZO64dXAjA82xTR+7M8ePzdt5tmnqwy"
    "xExls+hU4gvABqaprYkW8KzpV1NxDpWdJwoR4OOzk6GyzviP/7kC5zDmF+lkpF7AeVyBgyneTMZ99ebBChzTGPMRDPWQWEePJIEx"
    "JLw3GlyGdqcjWGNV/GA6EFn3CIORnerP53NSYYqvBMLDUHXm4gpMZpmZ0/KurpaweOdqpHRZsgmTtXTC2kDEmB3e4HiU1xDaH4vo"
    "JCQLRYdRbmiUFiNiPKzGZKlo7eJG1eejNY596FxFuB3o+jAN1Cfa1UWhqP35/2PvzbscRbJ8wf/nU+Srrtcn8xCZbEJA1KuuYRWI"
    "RexC9KupAIEAgQCxQ3V+90Hy3cMjt6535p/xzHPC3TBsudg1+91rd+mfa9+x4fs1cS97rKu+1H0k0rvaT6WP9fev6tdf1a0fXUHu"
    "VemXqs+Z6N9Ufyp9rO+/TPIx0+3b73Eve6yr9K8IcrtUfrsq2kcj/HvdQ78szReTnvi9SY/4eGXR3kPqRI/pzJInjU3h9+9i+i6D"
    "eezgKx0c+73zJMO+CdMGPcWyeXaOeQfxfiFs29JdV9zgXPjldXyo17GC2O/tV6Lzoy+ncZeelwfvomLH/4lA/ypN3Eeqwyen6we3"
    "inf6w/dBVNjv//xbb+ffWGTcFsSDj/XryyNBfInkxH5vLH99ZFDyAo3fOq6/8cxmv/duA/sl247j9DvjPD1r715CPr2e6YcavfsS"
    "lR+XKB/88On1hvU4kOo5/PVlAeXFTYJ4Eyrp9W72QIr7xe2rx3eL3Af/lH9VSr9bszd9/ubR2PcNrV+ZAT8+uJ+si/Q4vXv68j1a"
    "+ZcXyrfJZ9zvyZ4uGF6rmOZXJljLeNOn0T6wzCMfM/KT9dZDJNp3ka5e4n28ou1zvLiXL/Z8Mjx+tcu7/F/vP9nzmfFxsKwh+IAn"
    "bt4rC60frNaScvjxXvBxA+xXlgI3G7Znl6+PL43jV9r+19Xf2US89P0pSItloXwzbs3HVlCfvjnDBa2bN7D+NMubyuyO3r98Spbj"
    "5G3Np7CcH01fGz+Y/otv0remD7+e/nP1d9N/NagFwX1+tGeHoU9/WkTPH+8C8sL8f7r7WHenUzp+vsdG/GizelYJfot8rzJKvF3M"
    "z/N/H6jmiXVu9Pry6u7ekV/i3AvPim77bas3g4W7Z9ld0fwYLu9vj//+9CgXvGaxzYfvcw8n/ys+e59v80U7/dR48ben4MMv7TAP"
    "1xvPVT79M373JV/ii7+8dY8T/VHVJ+35TRkvyR8Fonjq6Sb2PMfhxX74RvqeRZZ6Zchxlb+R8GF7e/A2Fe7reJmvQnk+T/Q/sNdE"
    "PnxIZOUWffF29fP81o/Yz++151/l7Nl/2JZamo9HyGN47V/YCb/e+55R7uukqO/2u2fM+zv2u8d3HrP8fhi46U14kmdD2l/0VvjT"
    "L/Tw22KTvAoPG/3Uf3pviR+1j/4ML5bR73eid26539qO3ljlvtPivN2ThpsQ+1P/85NN9aMK4Rn1P8pXS41vWNU+tfUqr+in95bS"
    "z538/Dq5DfnJk18v46VtV/6d+/7zvvPhR36gty5/FW33y7/B/u2/m95o2bzXb4DvfZ5fNJn6buG9Nvrux+/o/H41/ONbi9U/3zgi"
    "fTKbgH/49eTCv8IOT0LcVyndbkmPvmKMZ+nuY+z28PiXjrqPD9L7a/8HOeddB1/dIf4n/An5++M14mt++SPc8tYf/VvMgr6BLm/c"
    "ed/yylLaPOh83jgg3IpfVN7/DTZ5af/OJ/cb81eo+ZbE4LWwOZQPgcNb44fXKVgi41/KQ68/9z3n5O1u6T7jfy4j+IDOtyv6m9bn"
    "Y0Omr7/3cxayx0jqD6v9Af1+uBDeZLd7pndhPNMA+X2M+GsI/VFb8siV6rtEi+/Z8kmP8jFX3p8KT1HsfzN+v721K57A7d2n/XFY"
    "vwPEv44F8S1eWL3mhVcvvOOE1yP4V0P5B1/9t3N9LHuP5R+KfzecfxP54luUwL6mxGO4gY9I8TTAB1x/8cfP2CO8x16w/P/88gHS"
    "/wjdX34rtq+NN6DsNT1+Bd7/Zm54JQmkxlf6hmec8Mgd+/59yq33/PGiOfyYQx6ff+ujPo3FN55z/pRvifDYwN3zrHnnd9cYX29A"
    "7e8/bO7s9XoRhI/HwjMrfPrApe1xYP8Z/f0hkMVjEN6l9E+fv2WN3f71Py539fVrVdLLUfLaU+3ROOXW3l0B8lVrHx054ct580DB"
    "2+vPGbPIT8dXZ8v97RvB8w8JLkR++J7e3Qf0Lv5/en+b3uF7et8i+H9I7ldZh//40XZX1j+yLv3LcPNZi/8Ntr0/fubat/rvh3lc"
    "3s2jfjOH91q6rwWq46NA9ZxC7lmhPjxFIH66B4oeDo/nO7pfOBzeLpzbFVv7+d7hm/X21NCrDf5+AfcLmpsvwKu5+tPtkuIbkPj2"
    "lL/ZE/zzcrOZeOco+VSrKI1o6f3hvuibqze8r95nh8inkqe75ofrzecL5r89lnx+H2X07UJ/xQEP07sbTjxbyHztWvk1L3zscPl4"
    "T/DrKuRvUK6OLmUfLWLaM+2+Vpe+r/EqvuftkvaXlfnjb1XmvyHHE/O90UI/JrlBkVeH8d2o6FkC/nR8m0H7o9R01QdM9Jzd7Jsu"
    "ws+WXG/8A/NvugK/QkzPqce+gZOefOGers6jG3M8TODzF2T15bUxVHwXFT9e3he/1ZJv88jy+Flm/C3uva8NuP64h+/SsR+Gt9Xz"
    "+kbprSHCLy+g9A/fBn0Qqv137e3Pt6uPI/GfLxaOt0AMH0Czl5vXb6gU0j5Soyi8R7P57dLLU2CrFwHmfg/wVPy7RJjHd34qvw3c"
    "8TfA/eWFj+4insfwrxZinqz/H4WYpZsfH4v+yGwfXv3mjIkPZ/zw0ntp5dVIXqGn17elb6n2LW5763LwOyhzCwn2hi73gj9ClduL"
    "36QJ+SFNbq98RJH7GP6/occtDtz/GU3bU8sfqFwews4tsmD4DR3LH1C2PRPp1u+3L8qgDz/M7Z13H+ZW9Ebb9lT5x/vEnhRuf+Bb"
    "faWLe+vZ8x6zvwzk57fXwmEevYLu8Vs1XPJ71XA3Aygpiqon5ni2m/5K7fFU85cUHx+yzrvAfN/+SG+uM9+H83v7mV4N85U09oFS"
    "450d+K8rN/7xFuq8nfVvvb3sjZfby8l4ukIMjF+4vXy/jD7IGvrQirm0txALf7o9eB3J4gsbNdk/dnXsL3ttVP9Du2uQ4C/PxjOv"
    "UnV9uUUv/EVrn5cN7PbCT4atqqK6eWv4c7vIIL5pwfNgcv4Fxf/nq1A8yxwY49NH/SwC5g06/LNYcAvy6BaGEjdTB+BdvtSXV6LT"
    "DWSHn9+VJzc4mnxGPl0+f4FWt4CqH5H54Uz65bzA7xoOH65rb47on7/A8Gfk1vgH6Vc/fX0G/JZEsI9o6F5/d1o6uuUL+fyFUszv"
    "ls9YLGj+Wwm531+dju9X28NIhLtq/LfcnP4a1Hs0jHsEesqzIF/WtzixH5j9PBrNfQzz7k8fdqLfgfLub72DeA/9/B47k7sp+C+A"
    "O/jNzeZT9Y+g3SNN/sW47sE89XhTX77blJ+e/Jri8o+f5y99f3jffPo/cd/8bJv/7S+Cfv1Fbvb+767OuvrdRfO95o/Hrn51x/z+"
    "LH/6vv+ig/zVIN5dRFvGu4vowfjF0+WP3KW9mdFrKw3W+Dpj90PS0GWz/fzdl3eBkna33eQxQeNSAVn9BEP3Osu3IB/3/6B+PIae"
    "7TVf8o8Yn77cVLVVsmwR/zBbvwh/Qi+n295Hrn5Cv4ufdsFXXfwEEV/e+agu4+bebmv3gb/b0/6Ft3APBr2PW9zh60zsr/e419a+"
    "v3ELu7/yMMg3rH0vT34BaN0j67zXPpfxD8+BcqpnBcofDJfzp4+G+MZu8oE23+TQl0u9MP7h++jber7HIb9Xn/whTngMO3sLRfsY"
    "7e05EO1HvCGLPzyGVv4oh+svWZPe33rs5rmVV3q+hQBPd3mvY7fmkd/c4/R/lGf27QZKPSx0WXzJ8PYrBtC/OOD7telzMoEXw+Rb"
    "+zck+Mq41f01Y+PtH00q+5Vy8v0R+AAPz8Y748H4liHcb5P3EfyWJ/+4lf/8FTJ/Z/Tytrsnw/qlwrNF/cOy4uWngDDaK1/Q6scm"
    "eXAC5T/yk3zlVCwaH7obf3dr4p7B9p2Z992M7fHRz5/kt29XN6/Gnz8ZS+nDcd36wS0qUP5hXKt7f37wEAjzhn/m57H+jreftHE/"
    "f6KfXTh/T+eP2Mt549VJVdVX0WA+cpb7i1R/v6Dkm9fMz58vw83h8/DgEPWQNuDTPRTJ7ZV7foB///dwuGU2uXu7PQWQcX9axnFv"
    "9T6UWyqOx7x4N++7x2dPs1yeune7Ye2hwPKDv315JODne+2XVHruL6csKJ5MstK/3l2EblEvP/ltWzef//kmC/tDzPv7k9s689+7"
    "KT12/+JFsizRRz++Jy+S090B6Nm771Fx/8+HKLXvim/x839+rP52os89fu0Rc+vyK4+YWyPeIy3/A/qv/9KZJwekm8Faccfzj+8+"
    "Fyzn163/v98cE5fXnz7FS9/vvWvuk33nXfP09qslc4vZ/6qRp6/wrp3ngNMPTYXT0wd5y4SP1X4M2pvz1K23B+/W9Icf/vIuDUd5"
    "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"
    "nytmM2q7VkdIkuBYWhM5jdbPBqssijCceX7dLV0J0m539OthQ1tGbqz1igiWBjkps4EeDmueJwirPWZGMgnZ6HSBo2stSBkaaNb7"
    "2V9GRs5xzqRpiYFSdF2nzYBTI6Dp1mUXgbyqKfZgiHIKUr0zmcf+CF6AVkkdbimd4PWQmtV49OYcm2/Z0K5Xaq71yRmKAn49ANyl"
    "ry6OZKCmdS6WYTWizkpGV3MGUOs8mFFzaDtHgJZpUpYFNQxTm+W0dqLoQlmlmbLsKlKP4O50aL2Ja1g+O1uIttBXuzkVxy+5Yx3b"
    "Iwcy+TI9sDKo1v/50S+qzGr++D+3L/79n49fb98H7L0oCJsvCAB8WAHA/d3tk5tf8mv39P7Gjery+s3BurfKf4VNlr74uGBnVX88"
    "fYjzAfD9Q7xwOfzr9pXUh8+ifnOKOaJ6NuL2nfGv18/7BtX1K1/Pmp5efvyaWVUQ5V+Af30H9JyAKA+vHyl+hvglgs/ZDMJyHG9u"
    "fk3A9WuqVjV+/OpYlfdj852+G5CZEK9Ko9z7PDOw9povf0Je9nXmoJ1Ezec77qwomvD6/XErbyIrjazac++jK+86/NpUlE2UzUSm"
    "XhDZURo149cb1PC+FOCfyPdZfviPT99/frG9eQW9Zy8sv/Gqb3YxXOd8hWwX1Yzj8/zmCcJ/h5Hrevk/vz2uYV7k3v8TZWVRNTOR"
    "Tx2/9DMTvT/stmmK/FOUl23zqZ6JdJrb955n7lgfb1x/ZPcPQ0PwUwh9CuFPIfKp/OSmn1z3U5t+KtJPfhS0lffx2w/L+DT0DvvN"
    "1UuDj9cP1c6T/Xz9lOp1pp//BAB05v5zGcZQ4BUj4R/xXOn7CaqroPwc5rPFsb69J0zP8H658zAq8h96F/mT9L2pAW+Au0+juX7x"
    "/FPRNtdF+vPaNW+z7z9sr/r0Z/n5toT3x/vvh3l31+/yzv/OTfMyOl9mYG1qVdfn+j1xsN4WiE91m10p/PTfM5BoFvDhnx+/+MUc"
    "h3/uojqaifw2E3ll4JfrZ0rrIo3cD2/o3kOnR8Wa+/5AyDsCWTtVkaaf74L12U4LJ/mCA7fxM4Lb16LfX+2h/kGw/ryJ1a319gXW"
    "q9H80palN1NTe19fL2HWNt5rkQHeEsNrX6+x3qelzj6+B/1HAXxs+/b2iHuPuqmKPPj2iraH0UVevGPDr03PbfifBOJl91FN1c6O"
    "pfG+3Si+fojWT4v+i5emUVlH9dc+jBrvxsqr++grq/yazavSR24TfgG+fh9wN0l3mF5VFdVnd+ZNlH57DqCsvM83EI/Dbk+zYR1v"
    "AvH196j/kcsPzKm+OTPVn0trJi3KZ6n7AwX+8fGtKdzJv36v+XEN5p9lUUdXpf5i2bNUz1x/e3alFXjfgpnsJzpq+OPX0nLdq7S9"
    "ePtMMWrkxRM2e680CvLbV49nJ/alnqW/+fpo0YMqcr9em6xZUKovj3iXUX6TnCsfHiVitjJvkPMW8OcL9xzRHVJV9N/uo2Z2ZfWX"
    "q2v1qq+vQEPzSqTecF+4H8ThEeq1ywN9V7ZX364vvoAfwA8PwupGXeRePd2bUcLN580G9PbvDPbZIj1zN3PPfpbTt2Hc1v8RxON3"
    "qp+a7y8eBGcOE9z64bPNt9+ff5z0yzffe80NMwNnQczmec9SNitvm+X1l8orvTkws9qm+OxHzacPM5cya/jDSa2s/ANC//Hh84e3"
    "wH368Mfr18gnApit38d5BAjM8vzhPz4QBPHpwx3ULOG/Dwr6hCBvgbo9zANAv/r48Q3R8CMvdV8LGfjxFwJ1G/XXL+z1T2zkm1bu"
    "5iZv0jdHHsMD9iv9T8p6Zfq/HlzMf1+/iv15dnfePz8+rPD14UdkT22f68JvXohKVL/qMduIZ4xoq+u3uT/+6wnXf94D03++jfG7"
    "i3wf50OX2+v3MT8LNp4jbzwrfQf1telneK/tv0Z6g/IcY52M7yCcW36Gb27+NborjOfYnMK20veYe2/8Gc57j1+jfYD0HHMXFXNs"
    "8Q7me+PPMN97/BrzA6TnmLPZ+M/O4B3UD60/w/3Q5dfIH2E9x55GmfcO6mvTz/Be23+N9AblOcZiDtSC93DeG3+G9d7j13gfIL2Q"
    "5XbW3bp+T57vrT+V6XuXz3bwc6luZn/xAnNvVfk7aK9Nc3DxM7QPXf4+WvfKguodxPfGn+G99/j7aKPcL95Bem36Gcpr+28i/PPh"
    "0bZy99uT23nZ99r4COzmDt5vfrC373d4sskvyh4/QLjP6f/6t/9B3tfnkc/jawT6+twFfe9NfH0W43z5vwAAwF8fbVs+ZwjpKzg2"
    "/PWNPPVO1Dtlmtx9ybsPzxzppxcNd68czWnh27r6kj1Py/l66j+u4htUPCH7nQl9R/GUeb6A9nY+/Mu89/N7uN9BM+ftdxSfa29e"
    "IHde/b9FPvEYxd4HPbxGV7+Pbk57mj++zBHaNXhyP34Jr7HST2h4ju63aESg3yfm6dVVE59H78AH4NVUZ9EGfgn5boHuRbPQcucI"
    "cAY0/3ctT7y5SPPTvPDFG1nT84D2jYQO+VVCcatr/RgJX7E9U6C3M5bvqnFF8n0qNx3/cJ/QnP98uDHmcxYNf0T5h7oK7E8fXoL4"
    "+AEB/vHpw63SUVrV7Msfs5wwKn8jwQN/OcdryP6QkUFzNvH179VirgXWNzLyd3KANzn1GJH/hE0/JpOPywl8wB5pflbdeVyzh/z6"
    "KX+9cu350v1QTL6y/Ov/7oLC7y/onbRbEe5t2ma5/wl5Lyi7VpGfKdujfn17Y7Ve7TO8LGfhz0t9T2r6LBF8GHmn5WWHz886fJpX"
    "5uMboL5bsk/P2x5ffnPaqp75MNu8z1Y6J4Se+0Pl8bGUehXTa131XoO8U/Dx209nc2X4PQm95/qzO2pm3/C3ao7vAGxCz3L/aqq/"
    "mvDb9Pnmg76AbynL90pV3UROMn5tivJ5AX4GWlZFUM1RqG1Vnzsrbb1vL5UaeTWrpgiC1Luz99XjLGeek8zhR1T/8YzzTwz/+LMq"
    "+HtTve4gzVP9klp1c5XkdJ64++37bseMOHu0xL8AcR03u7OZE3PuerNvX7LIdVPvxxJ7+KlxPz6rrb/b7M3R4m3x7vDmxydgTfgI"
    "4U1xuK7hzYHdKm+fXg/z7q7rF8O+xe28tP74vYB3q7m9IOO2AFZaBA9Mu1bHfqjGPxi/l0s9o41mps//fr7++PYo6QDwj9cd39L9"
    "N1zIW9bzvzJvpu/DH2Xl+V5Vf648t3U893NW3CT3/vjx29/ZFnvYGLC90JpT5OpW6Hna9vp6U7S7XrzcEPtq5bMwXhs+u211+zEr"
    "KJjVb3aZZ3bvMzO/nVkPPttZ+z6rmb7rZG6CX3+xnCbqnk/mf2+nJZzXKr2u17/uTiCaJeReXb3O+ftK3HZNnnr80oP96ymy/kXJ"
    "9Ou/42WeCJypc7yfSs9T2HQl59HB+c2/6XvvoKyynE3hk1UF3rahX18EkVeNuoWgwBy1fAI+zEbzA4g8e4m8KtHfsfxYpL+//1mF"
    "HXi5U3ALRB/0EoWuexPfo5eX/X4suD/gitz3UIHXmO01/HfhzAKafPuNoPduq2HgaUvl9vv1kv0k6fyeXvxERJ5k4xl5H66eqe6C"
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
