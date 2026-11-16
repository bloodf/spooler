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
        "{slot}{need}（含 {margin}% 余量为 {padded}），而{supply}{tracked}",
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
UI_PAGE_SHA256 = "fd8bbc98542cc938cdfb9c747052cabe4bc380f6ae3604488620f80cc538bbfb"
UI_PAGE_BYTES = 1207692
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
    "PzsJbx9We4P+2Wr35+pBdenAP7u4eXrsbTzur503XnftqLs0W7o6WJqZ22mUgtrF0vPht+2F+aedan19ZnlmZmaK/HfhvHnVbC7U"
    "+vvbU62Zmcvbubl6eLUZFGt29WH/qllfOr7y+8XNLWe/c9kY1JrnS6UpuzYz6Da3uk/fTuZmrq8XDs+2D2dmZ76t25v158g5Xd24"
    "3XGrNfug3ezPXmycPu2tvq5WT88vi/2N6oM35e4NXjaq60fLt09TV6X9/Y1Oa/Vnf7N+OeXtb3fmn7c70UK35O3V9weNx62Drnt1"
    "tdSeO74KX8Jwc3fN2V3tvPiLc4+HgevWrm9mup2d6m1j6aTtXu9thI2jqBTsfzu43DportXWNl/b/sb6eb9kO7OlqZe5h6POfH/Q"
    "mL996e3ePn+7vhgM/GP39HTraJ+g2N0pBcHgab/67axTvVw9nR/sXz+sX16fHB/3ztaaq5uzB/XDxsvO1cLmQafYCKLlwwv3aHPg"
    "nO/89I66W8fH9fpq5/S2uRlExWjRbZbO6vbMz9LcTLDXOz/wXv2npXb3pVvrey/bc8vRt5di3XkITupTzeZyc6YeLW1d/KzNlZZ2"
    "vW53xlk/n7/ZcqYWZ6+f9y5rc4f7RQLWoV2vRV5rZnm5WPdavdr60d6rffywXty/2tvwl5aC3qw3+3jb9QevZw/12cOoc3XR37t4"
    "WQr95+WN0sZW9TTYvxhsLS49/3zZDluDrre38JOQ5vLCfmv54OVk98a9OXo5n1vw3MZa92D/9qpx8XOz9XRyaG/PhetXg+LtQdjv"
    "P+yc3Ia7J2uz9f39tlc68k9XF0/tduekf3l9vNtuD6rt17Wr59dGr3N+eOBMPc1OPazveVdPZ8XtxeXSs7fo7EdP2+7NTat90T/Z"
    "r+3Vfl6t2d6e/3y8+rJ9VN8P1nZnZg7O1s5ugvP16wtn/uT1/OfJcSs82Gv4u9uzyzP2zVNxofm6v7de3WuE++78wtHt9fHrxflC"
    "47y11jsKzgev562X2mDrdftiq396tNl//tmq/tyeqy46tweD7WjpZnX2ZuZ0/3lu6zU6ta/qG92d1YulGhnCTe1bqdrutPpPp4+D"
    "+fbDfvF409/ard7OPD2fDsLjXvFow27deH1/92Zn9+xh/zTamN2szQ72Hq7a1Y2l/cvq6vlLaXt+dbe6vH10fbNf31zcsquLt1d1"
    "d2nv/Oj0uj2Y/Vb0Fw8Onk78pU71ttZ4tv2l6sbMw3Pr7Glrb6n/eLFTX++1e9t1v9Zcfdmp9U72/eWHXu/2Zmd/vT03dbvcH9yu"
    "uTfz+/uX86fbrdZJ72L15Xlz92Zvd31qZ7+2/lx/7j4+3jx5xzf15mrp4HjrofTt+GJ+vzkfVW8fpp6c24ed8LBGJqTjXm69NA5u"
    "+s6D25gjIGy37OCyv/DafOg82btLtaebTr23WLud291q/rxdcK4X9w8uutf7D+355nlx7XxjYXH3p7N79ti3V6tLP1uXW3OvW6eN"
    "6lp76Xqz4Z5v3t48bXgPS/NLuzeHe7P99vHC0fbV3sVBaXMwP1tcO5w5bK2ftZ6nDl2vs/y4FO6HB2eLnWB+e3fr5+x152ntzGsH"
    "Wwvf/NPaTCPYfT6uzZ2/HrUXHg4OjucX2jODtZu1/fWfRxsbzSf/or32/HLYKr7utY+LC4vObGPh5+76zdLehbfbuJ3bX7/a6C7t"
    "PQKxbD3t3c5cRVsXt9FLZ7N/vVS6WH4crO7utK+9o8eb3Zfb1eDxpB8cP0xVi1PHZ/Nrq0FtvrPwENaXpx5v1m9vzo+Dk9Jr9+K8"
    "tXd+fF1zro5qD6Xq3O1CZ+tkvTd/uXvcvDzcPWhOeUdnS9Fge/d55ttj98rrb6779VbQWpg7WX6w139uda9fFxemDm8JVfur1QPv"
    "/OjsqHa9c7lNKOzkpzs/v3+ycLq+ejuzvTB3tjZ/fPBycbTZtc83Zi/2rrdeD3c60c0iob/NTfdxo7cws3t+fHhz/Hjc3dxrr99u"
    "++Hsg79amz8+n10r1tcvqsel27W9vn94eFVvPjg7x8Wny9b+wfbGc+mge7bnLb9e3yy3vl20djfO1/aeO0/O9oXdPzk+KF6uPr10"
    "nl9no5O1y8Hc/Is7c7F3u7N47JytVqe8VdJerdcvHdi3O92qu3dZnLo9cO3Zl2Xv5XCxVd1Zauxs2o3+xslevda/OG6d+SeLU4eh"
    "s7q9d7Lp13pLC+6rf/5tvTO/vPPcWiA7Z/Om/rQx33jpvLzYt0fdjYH7utY9bt2W5g9PvdLFwHGLM9+8xdWjh+2X7fWj/XB157rV"
    "XH98ed2st3ud1eCieni8e7pU9zonu9HeRa23dba3V7veJKOxn1ZPFhfdn5vtrd2DXeewVt1dbJ/52+3rzZ35Xq/2Mje7S5bj9aBe"
    "2g2Xd2c2SiedvUFjbeqifds984sHpy5ZB+2NamP1anVr1qvNdG72S+dTZ/Xia1TqvXTDztlz9eD49rh4dnvVr65Fg+fLQTtaPN1r"
    "31avq4vLm42T9eOFy6Pg5nV5v3dVvdxsdmYJk53qnwan9tPl4HS5XjpZOCtOPewVj5rVna3Lm6vXo6fLm+fi7UV7cXM+2t/09q7I"
    "Cpm3/bXLqX7QXr76tnV4HWwtbZfCvaD0cNMMbs4vw+uzA3/Q80oPl4vXq3vN68OZ3sbT5uPtTu92cXHVP22sRifP5zsHzc7p0bfN"
    "UnjrtH8Gp3uhN99YO2weXw+e+luDHf/kqLHX9g46D1vR7dm3ueaFP7vfXqzZ7cuL49JZa/V4zrlsvzirl0uLPdfe+PmzetM7GczX"
    "n9ba0c7gLNrq1PYHh+fdxd5uzb/aeLVtd+HidLFzNuhfbzyvdvZatc1q2H883Du6PD96nZpbJbSxOnNdu7q9XnV/vpIpOnyyL0Jv"
    "4eGqMzhY3XSXltc37GD+5Gjp4WK1NbtVbM0+POxd7reLD2sPjxeXLW85vOmdPw/aU+ftUqnzuN99nXfXZvdOzrYOHr218NFZ27k8"
    "2GyG88enZ+1if/di6aHur848La+tbe4fL3YfZ8+qO1dbTm91an5hZvPE3n6dmWtcX280t84Wwpe5i4Na/3j/cGl2PezdTO0skNa6"
    "vbnGYCY48W/2b9z19tTt2ub1+vV2veHfPD1tNN2puWZ7e6lzsNRcvFm4ulg9Wz452vUa1egh8n9u7M/4tc397eL+/N5lp7s/dV5t"
    "fDt+aq1dd5d3WztNb/NkM3ponW4dlA4ejg/87uLRwUVjp9NauuocHy4Ntp5a58H2hhfaqxedwfHJ1KP3sH1VWq8OnpsbO2tXdac3"
    "IKS26aytO1Nrq9er898Gj+HRyfLTavW5u+G1Fm9be/7BYXSyuLSzejnfPTkfXF2G6+HO7V54cdq4XN15CXfDTnetuDHVrfr/H1vn"
    "sdyqskDRD2JATkNyECCSSDNyzpmvv/jMXtVzKLncMjLQvfdayCp3tXFzydKnGyQBHyRyiO874ChgK1lG2jPx9NGNqoJMNf3WesTo"
    "dhPbopwbJeps5GxZT0RtSM7aZjfs2OX8cAhLTXZ2EjMcnawNuvKUDFz9HTZUiuS5qIGw4IWchCABqaLfGjUEX5Q/eia781BHU9fX"
    "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"
    "AP6o0/E1Q2ELjuslKYy+n06mSj6QtjXJgsjSbr1c/Z+W8Kci9eB14Hq+MAx/YksCLxeUGSB+3Hx9lQD3Hgh8dD2GqDYd+MHmf+y9"
    "aXsiuZIo/P38Clc/fWvgNYbcF6rddWzAK17Baz31Ngkki0lInJlsdvm/X4WW3MgE7Ko+PXee6TNTRsqQFApFhEJSKFTY88a1jt70"
    "lPP+8dhuLbgntyKNn66FgtYUkAE24B9vXh4f+6etl/L0+uH+bCi4N1V5WDsa1cbbbfVechcP3uPd0cm83L17elmc9aybatdyr/Tn"
    "J+l6vrh/kPZaB1J/TxuOqgOt+9Axhv0bXr32BlOxqXc0/cAYyfXBwfHjXne73O46repFyyh556pW6Go9sV8+8l7E3ni+X6p60uJe"
    "OT3d42das1O/3OdGNbNQMsbe/dNcO+2Y5vHg8LTfKVxsc+Vq72BeQtPtVDq2reejS2c625/NtKeLjnVwbriPR2W9Mu2Xlak0V+yr"
    "a+f6bq9+cmj1FiWrr92fzbt2pdYqI/1Quihb7V6p7hw2LzqirJ+0etXOaKBLz1emeS2Ipemij74Yx+Z2uz28UefTgTAZjNx5ZTay"
    "PHO46Fnn/ccDZJx7dXcw9A6c7nYHaR1jfMiPrf0jfVo7uW1ezwsVoTQQ9wvl7f6ZOpzV6v3DQpU76V4vJHUhmb1mFTSw4/ba+3xT"
    "uX8+f+pKxwX7ZnxdfbacZqcwPr9Qz85LBn9hP909Hp89TFD/t+vDoXt/v9+Xzu770wdOHNR655bTtmR9pvZOOW3/5kY/UYTz3p6x"
    "vXfwcO8qdwv+vilfGUJp75p7uZs8voxuFv0bu+ec7Z/w15dH++Kh7Okn0uDmUjipjW/aNVt6NG6vXk4Xyn2JLzw0VfNivyRcVM7m"
    "6rnZPq2175Cm6Ldvrx7lXql8PLmTy4+jqXB+WytNR0ct58Xt3J+cTqRtayLI82a5/jQ6E7s9fu/+7HHamRweP7+8FEYmZ58eGeXp"
    "2Zm2qNbU5r14cCNwavV+3qkgo+/sQherwuGhrnenZ0f9A+HpUq1cLGa1TrcuKUfNzvnLw1nr+L43OfSeW5PD3rQ+uedvz4Uad1t7"
    "6Q/P1GrFLQx551C5vJgOEOMVnL70ZD80z4Xrwc14b3Qh7JvOSfe0Ld1VOwfC/fnTyeXNvPlUuKqobmHgHpTnnHw9vX25ejlRz+bn"
    "cuukddSU+oKgDyq340v50UbiIKmFZldpI6E5Pj0t33YGZmcbradtu7dXuJTvH15G4tFpe3YudEbbhXOpYFvK9uRpXmtdt4wX5XFb"
    "vhgMbkZngnvSGx2fltqFSUU/KlcE2bVOHvUj51nvyNv6zXx7NJtUpNFlZ/wozM9ms4qsDrrNowJfqRZe7mvHi8GibJ9cOcctvnN0"
    "OXys73e0Z+lstEBGbW3UFm86rmAXbvTB1fjidGbMjobK9bwuXk7t8b5pvJSrrWHp8fF63Labe3dGf7j/uN97shbd6uX+QW/wZDze"
    "lx7Pnh61xeFlzSs7Wtl6bj4fPLvV7kyy77iuqhdq24c9/rJTa+5L4uBK7mwrbUt9MB9Lx9L49HwfWRi2J3qP9/sWPz2o7p90X6ym"
    "dq1KntkfcFWNqx6US1PZmNculMMH273es41CXR4qN/cmmg9Ht7zWnYrI9Lidzd3uw/50pFnzysjt7ndbvZOXy8uCe3pfUPefmy21"
    "7YpX/GHtqHpu98+d7TPzsDsatvjzh37d6g1449q5t/b7F3eLx7Pb46erQWf6ZI7UM1V8NqZuj3+Zevzx9cViNKuVr4/GyODj9t1u"
    "4WZ4euyVrpVB9ebMrrWrrSfTkcr2hSorz8pN5V7zDh5Lw9PtPbc5PTg/HAzOlJF5fjPty/sD54Zr14/G5Vqn2myXL/uK1jqo1Q4O"
    "upy4eNieDpS6dGvs10Yv1/dC6W7uWiOk/p2zE7Ny137SvVt1fM7fWa1RwXt8lC4FcVi/74nl086py1+oWueuOb292tdk9aL8cn3u"
    "qSey5XEXtqmfyovt49rj0XlBfBbOt8+vuFPhkB8JonH39Mg9XhzcmFVB11sDT1/c9tG//esXUy2gueRsdDUen82uHg+40r6sOKOD"
    "y6fp5f2p0p4uLLlcnWmF6ki5sHve5HD+XL966t9zd5r+0mw293hx/+C0LPLD3miu2WJTvD3lq6Pp/KIwl/YnD/v3ysvT5OrYOu9d"
    "64vBo9QdLdyXuvZy48j2xfTmUNsWz18Q448fLmbKbOA8O2q1Y16dm4vLaell/Gx5nb3jimw/V16mNy891TEqLzeD7qI7rpaaR7fO"
    "5Xx8evIwu5rVnp0qf27eHg47fUntTbaVw8sHQR7v30m3g9qJe2YVpANEyHGlq1zeucfc3qXpmtXD69rx+f3RWf+0VrvYe+BOBt3+"
    "aeWk2p49zA7qzbNpq6C5aFC6fb16NZ7qyu28c3P29PBs3s4l6/lAlQ+OhpdIWvda4rB2LM+np+6ptNd+0uwZ4qu6erUwz7krA02/"
    "rnF3UTkRDo5F2WjPy2rtqG+1ngqq8HC93+/X9Sfd3lfcZ3sx1lXv3j1qN4/cvZvJVHTLY/307qCgPz68zLyjvevLZyRm5fJ27X46"
    "Uo94yxDuTy4du30yvDbli5P2s9TtTQ8uXh6H4+NK7+ig9Hh82O3Mt5+N9rY8KM3MZ29Rm922npuDp+F9/XJROnMvxtLFwd5teagP"
    "T83TvVFhcTRXO0NertXUrjZ4uN8+fygb23K1Uzb6o/HVoccdPKKl5+RZ7V9oVb1zubg59yxrrCpPzm3zAk3O9VtZELjyYNLqVO/a"
    "58/n6tNtczIZdDRknfPT54eLlwepp3vq+dXDxJrVXHX/2OauWiP5Hi36R4tu63jyNOzOeyOBf36aGeW6Vd2+lh+rdbU9E/ef3Tur"
    "vj1Qn6X64VnlucDdnQg3NUu73z+EZnvtu27TejHmjqXUb+yrsXhw3HoWubvS9PK8V3atgnZz2If7cKPFzWRvXCnpPcGwDu4U82J2"
    "c1koH2vnQ/fw4OLw5W7RFh/k+rZ98jA6bt3w5tPF1XCvfdU+qp7udYdPqn061x7Ls8KdIbi1g2dv/mKejPvW89it13XBU+6uD6vn"
    "41br6KZ2Zs69efVmfjEdHnZvLntHNw8vne5RdXh3UbhojoSrjvM0c+o3L81OWT27F+UbRzq6cl64w/r+w83s+bLe2j+tVvjuoXQ/"
    "9Y4XZ8NtWSqcPZ89eZWrM1u4O5HPtwf9+9GEFx+O7JIy7iPd17p4LJn73mxWmrQ8cXTj9a66Jb5ysjiezJ6Exyfx/mB++fygCaby"
    "5D68iJpYdi5mLe8JmUAV62qseKpV7Q/l4bNzInYkBZkgJ5PTx/HhuKQad8azeDyzrfmgf3Yjzs6G/d5Vc67f9cbT0rXQOTNn9/Mn"
    "a9xEbS7kunW71+4+3/eUl6noqf2HautuIJ0JvYfmmTE4ub8T9enBwnnqXnvIDNU7V1dKWdyft1pwLe/ALCxOjppOX5091R682rmp"
    "VWqPxoN6cjy6NLmyvPei26bDC1ppuFe/HO67Oj/bd62Hcql9pN51uYdm93pvMr4+tk7rlXJhu2ecepfG9ZG4d2RI9eYJmsuNrtad"
    "PLhnjinXvdaCb+6XuTOkHRDTSfYtt98ciYuD071Z3Z4d63vDa7XLFYSqtV8XdadwdW9WzrQbZOGPL2sTfr9/PvXE+5POc++8dHNi"
    "V/YU4Wo4b7pn+tOeXHo8sqXO1Ojeq0LzBE7bTx8PD4Vyd2AceI/z4+dLxb5Giw17ujd2b6eic9MyZ80H+dY62FOH/Fwp31y2DJN7"
    "Kd3KpujoI/H5alJ9OhSqly/SotA9rliCUz0U+w+D0/On+XZhLJV1XRp0nMqT8jDcNge3nU6neXd5y5XONelA5JTLR/Ps5drmD1vP"
    "27VBu2OeH8nNQ+uuXVDunifVa9VUpM6ltN/hz1ruTJgNzmqj0mhSqpkyP3maTfc07uRWmO3dVO8KM1VA+vxeqQzrKj9rT/TB4kQt"
    "6M75rFa6dLaHs3u1eXByenB4ZDy+9MUeGpjy9UvZvT4SLqYzpXYkdS6ujw/vytJd9/pmopYqrs6d1/WT6vaZVho0b/Wjs/vyy3yw"
    "fzXrmQct+bR2sDe6cyqaOLaGw/lM2udOBw+V2bVdPt27uPVa7cVhQbU69os05U7Kg0LJOS7zpRE3Pjq4lIZ7ljnpHR/Nt++u7MHp"
    "8aU7V7vKvFA4aZ5YL0eFF33Yb04HzwtDPT68OnR6bUE9MUoP245Sac3KJ/J1/aiFlgdz7abuXO09aQ/dqzKyKC6OKyf2w337xVoU"
    "pnuz6+rlcevR1XvKfaEk1Ie3F95QuS+3ezeP0/b5oOL0eP6so7jjvjiQrur6Y6sj6GZpYI/qtepp7em5dKLWzOqNO/Xk0vnhsbvd"
    "qUjeoHTcehrf67XaVDjyenvyXUd9KOj60JtdDF60i0erczUeWubRtcwdDW8ft2/uDkR5W+MLe88ldcL19rav1O7cHrX6T/rkTBo/"
    "DM5GZ2W70nm8thYD0RvWTqsv+t1h2e1ognC7mMizwc3F4nH7wGzP21PN7QvbV+XrC57r2O1to/x0Ujt9kKzL1pl7Yw6Hk727l/nh"
    "dk24fpQfLXPuXB8/F85HR/qxO345G83POPf6sGW09+pPhfqgv5jeH1b3KtclYXKqDmrS3s29YLQ9+7Qjn79Yt/3y6Z1z6+rXT5OD"
    "vv5YPdmX9vburSe5erTfr3YqxqF5fXo5OD6eIh1weHerPY5fevPWRB0MDh61x/uaOh9fiM8n4hUyJ46m/RNl3+vykjOt1fhbXT7s"
    "TLpaUz64uZjyA6805eY3WqlVubudW4NLZ/7Se3ZvO2JTGReQnX9QvjizJvzBAzfaM1Rrb9u62Za2uft9vlXRD6zLoxNuv2O1z9qz"
    "a+tqMq+VnyTPHT6i6fvKui9UC0Puotnl79AkiJR3efvOMvmxeN9tSy/3ykO9VS5bT5X59rDTO+l3Z/vbwrNW7/PyCNkUilkenQ2H"
    "h8f66HLvci739/fq1evDI+35oDPcv3wutWuu0durPFerBwNFVJ6Ge+eLS67Svzx5PiiYo0Jn76RrVIx9e+yI9xfX5mzxoB4ZT+WR"
    "ON+/c+8W89t2ob49ubNkw9aPHg/PNV3YO9fax3zpeWqemA8LZ992T4/H99flab0glQ/UmmrVxdJif14pPI8Xt/bg4qQwaCmuoc/a"
    "rcXozLksSMNLeXbVKeid4yl//1DodYb2tOUcnYyNZrdw/1KVCmKnbtevzgf72qA7rjwLvSNJlbp156VltusP1sS9H5uPD3Nhvn1a"
    "Pintl9VT17rq6J29ykNHPW63upHLJLuN3F59tz/OkyfDMvQpsZZtTYajxls29xQ8L0by/MfFwi+Lxj51/2LvipKKTs1F0puf5KVL"
    "/FZq7I3NA/oGQfyVTdd2vIN3wJOHnt5TAkL3w+N/yc9uNuB9rgbBAz/gmP4Mac802qazotu27a367obeEk343Aq9TJr4gChpv7a6"
    "FgJUWldX024v1tQEIGvrIX1eUxMBWluX27NnB3h4z8zRJG0guDDgxZi89bcGuIRynf2J59mjFeMLkHvw2shqyAgCENapd2a3TXcN"
    "+F67vbbaTrRK9vIcKYBfD4xRbGjMS/jpRrRG8dzk53GFNyTELWvSNg8tu4ksftzICjIQLI4246Mw8Dou8Id2w1oBdE2drmmZWOiB"
    "XqtqNOdjY9Re2W+k2OCVl1WPDDv2bAOQaxM/FrrqzWMf6Ljlc0QMb/r6Ys4hgKCbiFJewUCo3kq7v0IeYHgd+8VcJQaG1e+ODsJQ"
    "cZVpmR1QmYima5Qmx4COwqozbYBgJgir0FWswWRkpb7st9ureso08t66x5YJ2Vc9tbz0KCd9XfNb43cyX7qN70mvVuKH4b5k2Ntw"
    "FNZ/LM/MG+02ffMOnssbfaSKNpIRzwxqIY/bJDz7Rl+gPvPtA8NBDLXTtmfIEBianoFIaXThqdHwhwb8sWwDv6tmthwTWQ80F/2x"
    "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"
    "d7WbukeWNHgf48NYGxsO3U8wfmiZH2prg/59mDlTG/zb+DR1Zf1L+xVt5T0jt67JzYVx+2M95zbo969CYhPCcD9BFry7t4xVNiEf"
    "B7f9mIx/nGK/FL9/gJgYqYR8GOXsT+sWbq3m/M8iujmB34E1RD8fx9doETMYtkvt9ju2z0mNm+2BfQyX/xf2+BkZ/mceuES7Olxj"
    "3q/2gXCHG3hXrGww3ZTdwPviFzSfqqjXngz+gsZT59UNNuR/vvml1dbqVt/foNX9Keayuj/b4E8x1y9o/uPM9Qsa/xnm+vnm38lc"
    "GzWINapnd7tJHr2rL0X83K3c9LgMq+I7Jd8KR3qadCFPurDh3s36cqnTQrRY6r2KVZd3El1zUk+RVl6tWMYo9VbF/3rnfNw7Z1P/"
    "qpQTv42kr2iOSJi5uG2zISv2Ui76rLSMkqrY7Mx2E/eINR1+nxEXk1dmf37ItltZ10ZRHaI9ef/hyjIWH3WsSK0l3c0iveFUp4vU"
    "Ih9wwUita/3RS4j0sO9ebPedjONZ2eTLFI4NwQszvMa1za5fK413j9anrxDDPuEBP3hJzR67NNz/t0b4jsd4x3+ZoZF7/S1xVfNb"
    "0YOOHkH6xw92gxI1cWa3zdxviWF1cBmWKOEzOzcFFEL3JIF//uxRz4ZrHKkEWoNgmQi8Ea0qiDEF9QSpKFQsYFYUFBojqSM8xeKG"
    "UIF4S2T1h8uSnxDiNQrjbxhgqJ49O2QZsbqGGAD1DD8mPDQsK9aa1Q1DWIbTNRtv399yEIik2FgKTTL2L2lCspGjRzrHwFmNtAOo"
    "Ro7YtVEIktfIjVv+c50JbyE1ko83GtuI46jt85bzyJDSWB7RZmJByhoE+H0svEMDbr7+tirs2CrGiIWSeg/reh9lYBhGvAKJEQSy"
    "2JCUkLWdSAv2yFtuxAiTc3aZG5D/Ti48KUjz4IXwTIPYpw14XHYEAn0IEdYAqU/Af5MmHfQfP0Z5HHwNWHt/Ae/NhqtxIEazaUG8"
    "1a/fGikXJeLDEQkMBrQK40U+NrJv34sbVxjzB4hXyT43smkjF5RbPdYRlwcA77sEroZzMrEGNupoHKd4CKPfihCAy8+leAHLhNkp"
    "JkvRQGMNCnpEOIkuXhprg2mxcnVwy0qExw5bDOwAr9AS4cjirZEDyi2rIN9dBHQMkHIf3LkSYLCbVyNHrlu+UzOQQnHWiUQggiGi"
    "q0MQTSQVMR0cvWgfAwe/UyzK5Ct9mi5F2aWFNwIKkCE+wBD7xAhLpGn40mm8XMkyjQ0KtwDMr4JkXpB5I0HFJxHUj6G0wnhIjhrw"
    "W5EO1woilvywCNW+6yWSMBYgqLFUcr3WHMKzz6D7VjBOqJ2U7iUEwkCyC3q/7yLtecYaqdGPSO+S17yTultjQSDW9dmPFuEPH706"
    "n1iQ3asHdjmIgPtvYDU2uY7PGrueWGbqyPiX78PQqZABSgEVViIVIkKAFqvjGt/phgaThCD14ndQwV67vaZ07PI56+Q+uwSeWMi/"
    "Ih7qbpqoJsqoj994bC1WYQff/VJ4RVtMfNiQiCCZjRCbfm0sr4TTwl83isvADfw4OrYmjhJsyXgw1wZA1/GqJ6kzS8vREPzyPBJb"
    "QWHY99hMOKJeru9bT7XI2sbY/fbdf1owuu7Bb6PBk3+NdKc5NNNToKj2CO8q/Fbsfw2C0oDq+J1sw7BXYZfSPbQ+sWCNckGxLQbl"
    "47ZL8u0IYpfgb2foG9NObz66zv8Rdnc54AsoBq9w43Gnx3TQLTzklfkY9piSxsRknxo+byTZCgFvMHMBv0lwZrquETcH8JedIfnU"
    "yAHnLVnIVJmvND4DXkixQlHfAuMLyccRDhcZQzwxpCTIKipQafeR5jwe9b0EwuBvyAiBVWwIumZMzVRoF32MQJcAfSsVvoU/Ix0A"
    "VI1JLGQhxYXJ/XfRj8aIqNEYETUcgCKKR3KQCoZYTL9R3ghbv8csqOgKKziIPIq58JqMmV/yZrxMwKTwpomFy0tzVHrIU6QgidGJ"
    "X3h2i6+xNfGrf4bQgFhMDbY0fPVPEBokHAZ8wUOa8OUNie9TZZe+RNHqmVPHRoQARdHIDU3PgGa7Llpixb41OuSVD/QLnuOCF2Lo"
    "B6QmW6bZbqARdafd4ut8aI3cYqPneeNioTCbzfIzMW873YLAcVwBgTRy5FxD4HL0pAL9mvbN2b49LzbA7UKA/8PzJuJe2FJGXRoh"
    "dYrwgsdFvB6ytNCa+EzJ64quiltSXkJ/hZKaFxT0P5TmVUUTt9S8Kqqi5qe1PCdygsbgq7wIGeKWTsujtCiIAkqruB6W5rm8IKrS"
    "FoNHaRn9rbL6eBmnS6w9lNagHMOHpRm+DF7JKwgvCdK4fj8tYQQCeIJwlefzkqjLqP0q+4RrElS/KlwTQoGlJdqVGKkeGXXpiycl"
    "2NFs5OBxlUZrJHPSGBnbaETPKrt77N2SEuGIazLu9O2EPXhZuviJz/31VyJPuUhXjEFpWKb3imdm72133s08VdjLohk022Z3/6SP"
    "2VxkvGyukjkw4I0W/Gx1NkseloGXVoB9z332RdaSG+NakkVWC+HXi4i12UDSZnZteKYXJXrGsDlxukhn/AOsy6vATapc4tW8xEsC"
    "SW2hFPwr5TlN1oIUBiM/dQzMCqHhhkLkx5FYEvKyJqs6/SDgr7QMS8gl9gu34ZfA7Yvk7xGvPgKKOoL0MdRJWwCms0IEK46hx1G0"
    "GHoc6RP5EUYPfyB40DI0QZBj9TN43LSI/zDUpDDxpIB2MnTLR032SSdjKvA+bgqlnBIlnOLTjRWgCUo2Vj2DlwjVJEq0FWLFzxZP"
    "SouI1WVIrPYxy6aJE2HoNCk6/7AUHfhSNDZHrb4VkyOW2QBbAf2ZOX3yfp9jzOA5p3EbXmr7J+RGzvMCYig0FnwJJXRRkCCl6BzK"
    "VfKqKqFhzcuKqGCOEFUNBotXVF0HTtBVSURpVRFFxCNaXtBkcUuEwQR4LS/yKihNUZNUBI/SkgpKlRclXYDvvChi1hAFXYX6ZR0r"
    "W1kSdL0KvKXxWI8rAi8iJS3xmi5hXhQkBSlpQZd0BdKapAEcL/KofcALfYd6ZZUjaYmTq0KeU/B8okHBEo9KqSJP0ITsvIKwUPBn"
    "UYZuS6qg4DSncYg8CEyWJFo9fBdEicdoq5yiEyLqmEySpkhVIBsIhZhXJF5BxWU0hWDNJCmIaqg5WQStJCJsVGheVXWsMHiVR50X"
    "EHo8KBSeA2ShFA+lJB2UjSjwBAM0XW2FR/ERxpQDMqJhgUGV8gqngBCqEgeDCrO3qKK0pmsKVlQ6J8Cg8Yquy1WYk2VewQpNVARE"
    "NI3XRQkzA69pVSS6kq5BUlJ5NIfCoOg6orXC8TIaYzRYmqaitIhYCfOQJmqgUnRehrFRcH0wcUqSqAC8xnHQPJpGRQW+o27qwEOC"
    "xOmQFnk0tohIiLckgOcQUyH0dQkTG+Gj8QLmQZoOOr9Kf0yGkuN5RH8ch/THJRXVNA3CRDlNhxx8WIdUEx43Ax8Mmy3JY8+bhb69"
    "94GzRJecFXeN4/d8yWWaRM+aEFbpD1nEAXuRe9fBqW0IBpn344m3yZ1pYzw2DQfWSvFurHo9wLPHm0a3S43Tv/k7HQlB1W14Ps5b"
    "rHxjbHVw3/XveyQ4A8nLARfDVG/a8/VRO9f6a6309kpDKD3GbJh1UoMZxDxBImUSXT1+LRO/w18qXMm7PKbeWXDJZ+rd5SNuT+8s"
    "vexztbaC93lOxT1lwtVH3WFSFEz0amiA0Q7DqPhetNe67MXun4arXnfzdC1sGp8mAq8UQtSLDkRBxd5JfQtrqbjjZchnBv+E11cf"
    "M1x2y0Xzhpnh8vwq4idEnScXPJZmAOLylV2tp5YjoUQENTUOdTJjoDV4a0B80T7aJK3iQ9rKL7vCqW5DdFdz/CokSCwOikly2Lb0"
    "wedzW3wIOsxG1OFtg/78R1mE9bS3OmT5BqO23iHyZ8TgPz70K/0bP9aTiOfjT40afakgNbxR+vywuedkSqmwp2RaxSHPyBSQjTwh"
    "U8qmeT7+nCj9usFhHJQ+SIk4o1R/NDXA9PvzZ5qnlbyr4Sm8OI4maFhErtX/KySIlN9UCSw1/KHp6NdNKEv4/I1a6vXv060hhMMh"
    "T9mqi9+w6IeRZjVsHGk4qcdBJe+1Xtb04SenBx+vDRByh7nk7NW0TTF93eHmKzQEu8lOwzImq6PGLBvXw/cZ7sN32u7DlGAxYZSt"
    "bi45+0NUtrqbUxnBbkLlZUzeSWXUznuonAC+ksox+M2c/pc9XkK+buENuyU3vgSRxS4j5Cf2MaEyBp6q7Dfk05kNoH8ft66hHuLj"
    "gz1Avibm5n+npaAQ/Ql1RRU9rpJmESdqyMXOmjF5GRN9j52UsZP9KMHJPjb6kTLgdj9KcLtvwonGEsPC9ixML42EOQd9ox5Lcd5q"
    "wC7rtX9Ss2+4ZogujRzZenWLk3kOD13xFTsOFvEubbM/MpxFcd+2LdMY5RwTWYkja1F89RZj089umx1jYnnFTzx2wie7dwTkfDJs"
    "mo4PAZW+kW4ctylIzQNLLgmkBJxHob5RsIvmk9nyvieBY58HCk7AYlAwplWjacJ4NhermvchVwC90a3pagUIN+23Q9cJmH/La5QL"
    "i16v7+ZiblY48+3t7QsrvfVSAen67d9NwKDQM62x6bhbO1uAit35jfmJvVR2Sc5WbTFs2hbwKq2i8flz5FO+7xEnS2BNnNP4muCw"
    "R8uYb4nefLE6o82Z9JWxSQu3sktgUP4n9hs0g2dDFV8ZDkW/wRzu85tPgn2UzHm5EWs94+3eVjJeNttHiHwlo5tHw4GWCeAUZDre"
    "AhdgzJszR5Mh8ZoqfuJyCLdOvzvx03AUSX+/ZYvmN+/7LioSNH9bCfTbEaDScDEHNLIB8RE2IWp6RW+70QhqwKW87Gu/k8Fd+7Tb"
    "sDHWjR8/PplZRtMv0MboC4KK0PaPxqQBlyd2zW+UeJ596fSHfTja+I4q253aaG3AERydXWQrIX2DW/xCWnRCLbLWnC9eDyLs1VFT"
    "FcexnUzj3/8OVbw1nLjeFgU2tsZ+PiZqvpF98wcDek4o8pXIBpX0LIwi4HTja5xEbXNdWTprMlFjxGnIGIHbXQOvmdDfpjVxGt8R"
    "PHSm+Jqg2IuvTDIJWZBsDk2vZ6OGXrumd1m/IE4cCWydMYk3vu2hMUSCmB97w36R/ULdyb1SB8biK1tI4q9sjmKTEsllKaR033L2"
    "qIT7EmkWDc+nCCjcnoE0U66M73AmUcBfP4WbJC3hMfmCfyZOgCkf8vgU/hYKZ7ycmSWVxTJzpDSMSMYfDzSw0KUDGJVIj8LAdMxM"
    "3Pt9NHDLBkNu9CVcAo8utIm4CjE8/gSbagcwQ2bzpBYkaaBz4U4gZvQRwQasiQm8CfmKXTvPgd+WdPDW+2kU1EZAAB9IohbpEIRa"
    "gU6Zu+9vpP0X0VWEGUiCaRekNaG/SAVEuOCTWTSwlPsMkEWEBsfAy4R+H1sZpEZffZsHI8LMnnfwco4ugEkFy5bRG8EHzJjgF5zu"
    "vuXuKrvfGoDfzpjZd+AAQjJY/X4OEvJDKNCHLNw98BREdAevK780szCgWFADkx70ExDcsfx5PpLDEpQMqMXTAEWUeg6nghn5hE5H"
    "OSfXzxkBhTPZXDWD0Jg2cjeZV2wpF9FMOM8QjYIGx8iHFRDLR8ZvlCq/FY3A6o3RBxxhA9OXfAR4PO7IuPv2kmlQIxAhgUYaLHJs"
    "YeWw8ULO06khX/xG8CMFsjkKi02t79SioXnYnsoRJjUJu+WwSjcCAfH5KEDftwDNPPsZMFaoJ74xafqqL/dbbOyg61GrLQwS+Uo/"
    "+OsCk21+/fhBJgVfd3nfuO8/fuwuC4yRpyDgck9/5vFdh4yBTMLuBK5TuYFq877x6RUBBKkHfqVUQ+cH75uQXhGBIVWR30mVLXMa"
    "HWHf3wLJVjb3ksytsLpIYFac7fNqnOeSKsIrjoSaSH5iVQy950r2O/w9pX/vKtm3mwriDcRBzu5JBZtKD75Zwa7cRVzOWCZSB2Aa"
    "gt6AmQ0xBvoJt/zgD7tc8c+4bObBg4m4HaqaoOAE9raSeAEldE4H5y0tzyvU6YznxRJ23lIUlJZ4UcBOZILKQ1rlZXA4QvCcJGMH"
    "IVFUwI+KuFIKksTf8lqJZmjUp1KgfzWcS38caSWV+VbiDyp2b6RlaOKWVlrl85ouyzxrsoT6IWiiHqCUVznwc/NRzmsiz8lBl/K6"
    "rGm832UhL2AXLZ54dRIqHQG9Hs+0vMJJErhwyrKiSCWU1jUNfDkVTRa0LY34k2oSJ9EEz93yKvb0BP+wW/Au5YlTKAFCKZHjBb8G"
    "SKPusBbAw4sTELYi9uzM66ou6dUYGqscrZTBs9VViKPVfcjR6oAyaJqjFWPgNEerhw87Wj3GJAfvdiSKD/0SEhRki6Oq/FuuDbC7"
    "EGLmji9d/5AoceAHmGfCBMyDsjiVypOE3Q11TiPypGNm4wN5wn6GCjjWEXkCBztJAaYm8gRpRffliQN20XVU7y12By6xXFy7L1ZY"
    "eiVd1yHNceQ7Ei74zVMR03GTRMJQpl+Dn4b6b2lrRNQUnWFDRA27XSNsmajJEukNEzXs0kp7i0RNp7RQiaCBC2YeyxmH28sTUUPY"
    "rvTqH3R5a0q4+mqJqw8w26zmbMpbaez9+GH2/j3O3i6alXrJ/E0/NegVTZ+t0coC7vOgdSQsO8nVSPrxH7mYwgvARIi90U9V4Bl7"
    "8+BgzhNnXZmTSFoWdSwKPKdK4COMdCxO8jq4CAuKJmBwHlydUVqVJZxEDISgRY5TcFJXoDIEI+HKBE3FaUlTcGlR4eHCiYjYECMm"
    "gbMrSuscSSoygEuI6TA4ytARuCRqGq4e8R/4zFNHYFnjRSgt6RzBTZfhCorMaeB+jFStrMHtFYQEZmmFl1Ct4CUtY0FWBFnXAB4h"
    "h78Lqoq9qBEJJOLWrOs4Lar4O3jUArymg/QhYVBUqE8RJA2nNQmXV2QViw6aXjVwxpYFuLQDoqZooGc0AeQFJB+LqSZI+E6PIAr4"
    "voAsitjbGRUTAVwg1zJIKSWvKipNSxJxJxbwJQ4ohr2feTQSOpFbOouDFpB5IaxzYhpHCGmckLLhBKJstJCuCWkrP72sa/C0HtI1"
    "eFoP6RpRjuoaTo7oGk0TotpGYsoGKxrC2I9neFpFUyyZV1GbOmLEYHqHtCTKyESCGZ3D2hdVKQuhNEKcV+kcr2Py0FkeAUZmeago"
    "PMvjhuAulCoieA1ZBbJahRtWvLglkglffmTWWthYC88vYmx+iU0vSmx6UWLTixxML3Ie6W/gRonYUjL4vwP3qyp21pfyisSBsGgS"
    "KoBd4TkF0tggAT95HRgJiSKSIpG4t3NwF0DTwQ0e3N8lGd9AiVo3R3ALrYT+wdd4RExRoCxCTIF7K0FakEssAUNOL+CQG0Z5bGrK"
    "/iyy0gP9Zd6Un8gUYpbjU0iNaOY1cwjV32mTyO8fnkS8sn+hxZrEr4WRrIbRhu2G/qiFFq0urDCGtgN/zLnn/DN2EEeGJ3YJiprR"
    "oatS4i29+/TrbmPhf2+hRprvQ7FSuA7yoxRtgzUexuT2V17ygn9uxZJObmOx7wweV4L/rmTXRbc1pHb8KMSul5gZUq9L4K9p/OmV"
    "P8qfjs+fiNeWrBua12ibYJv79g360TWcJr7K3pgZ7j905wrNWxqsbNGMyAki3NDhZGw2oLSkwBUWESZupDJFQZFpGhZg8q2c57BZ"
    "w/JQWlUkHl9Q1JExAFerdIlcWNTQ9Iv+ID11BMteunglOXRZC9ddZV3zUzqy4QFSlbDBICrUhEcGB2hgUpD+OkKqU1c5xKjEcCmR"
    "NL2OJeFLlCov4RlaxVeG4M4PGCR4hQ0KmFO1koQQ5cg6HwQTtLFC6pCREYLTME2QNm5p0wLcpkIKV/WxwqsF0ceZ3jjE3aEXDklH"
    "KdNTKvgEkrCRg5BBtWmaT0Y02aDZU/fJTNJwTRgPwy0akhLOw0sQ1FkRYHVs/dHhBeNC4FSWPKKj/3gmIcMo1LUSTiv4xpPGoQlW"
    "ymsKT1QE6QCQa4su5Qkp8ewoyJhcAiaxjMwoMEEQWXRZomk1Tj7aNBs52FUQeLjOrJFrzWB2iKKmsDT5K+vYWpAVHw4mRSh3i/AR"
    "RB3K+Tes4XLbFq5HxzewdU2HcqQdmkZGmYbqY995RCspVF4Kp6H+W9peCedrCsFHBQNOw39x+4grYv1B5gtPZI51EI0CWg6IfgGU"
    "lpF95FdI0ssdZPkMQVJP0AHWDusgmFmKwvsEQGkuKC+H05EOknzJJzirxydwtD+PZ5TL8C0/AVYmMr7FR9NwNRKZPzzc8tMlbOzz"
    "mJHDOgXniarP7LDU0n1RUMCA43RfoyDDHS1+SsSgD/SOSOx2Xy/htBwRGJIHV/p4TVVlciES7/AhXEFfUP1IcT8iXVs1NbnPyrBF"
    "Lal+aGqqOyttKDpLpE1OzocnJ8OfnHA4NcOKR4Pws/+RxTRaZEp4uufwspFDixdiWPACjDon0tWKDJdpURovMwVyuxXg0QpBwWlJ"
    "wHwhCCLetJSxnc4jaGxVoEWlhplKwNtHaPEIU4cgSAquTVM4cl1c0XDruqrJeLmu49pETiDXyjW0msVpCa+R4cov+U4WySIvYasc"
    "LS5UgBdFtOyANFrJS3jFriv4u6jjRa+oithyQqsgjI+oqypQQ1REPJ3AbVZcXkXyDEt2NMvg5Qpabol4jS5jXkXLKBHSMg5ZIRBF"
    "VdVxCAuYOIie0SHiBY/jSCiCgvULTUNoC1CoBF7Bf1WkQFUSuQLAQP9CMZYGfQjVSgy8quB1CMxLIGXY/GRZwcX8kP2p4MUwT41Q"
    "mS6J6YV+IVIuSN/S2qsSjc/BkBWjyIoYWdFHVqC6ioELfkwNEtYjSJOwHoIfUwP/RWtQCXeW0Rahi6rHtEaKSQX0RUXGO5VohYin"
    "SEnj8HfE0jyeMjUYOljo8gCuShgtUZPwEKD1KjazgCVkfINZwStRxAqChuCRvsPLe1HSsA2AVv2UlWSoXUFIQEoQBQmgEQPjNC8p"
    "YCGoeGsBGBV9wZ1G6GJG16FyVUGcjOVAx9RWdcTQOM1LgBzckpaJ2EiAvIb0K5YbRSffZV3AUke1sqbqGjHmEUOX8HKX1IfMHWyU"
    "cHBNG9IKj6/G8yIRakkDdFDlMvlMviJDjugIn2fwygoSmsz7X3hFJ6oCy3JYsaA5V6KrMSlYrXBkrmMLMo2nKTTDoilE02XYAIAp"
    "GS/cUeVgVSLmwDtDiF2weaTS4DHAPsCvZAZl8CoNMiNhttoKpUk5Bi/jv1UI4SGSIAE4iAxgq2sYTlYEgQSLEfHyTMYzOEoLxBBT"
    "eAnDi5qI21Fg5wbSNFiCovJ4w0HA23IojTQhwCMqERHkZHzPHk1vRArBzIYNCo2G3xCQ1OD7+hINekAsCV7hycoRb6jAhoZG4EUJ"
    "14+IrZA0qZ8XFRKlQFREkuZoeZWsPuAACdKShK10DlvvNEIK+QGxfXSB7OupSIHjfRZOoqXIPp5GDFE0aSs4jff3WCsitmYDLFBa"
    "VniKpUzSnBL0AswLVp4Ed9EEihWmAtgQfIhKSBeptBc8Zg4cuALTmISG4QnyZAwQ72giGUON8A5SJBgbRSGshfebYUg1DC6rIhlC"
    "HvdN5jUMLYPIY/tF1xgHVdHqHDiRcRhsCBDOZRwYpAmHMnjGwTzNZxzPxzheiHA8DI2AV4kgP7eY1qFlPi8SLU+j1Kxd5pv2cLFw"
    "iC1lh2wpiBe7Z62IVBSYOmkGlfFhg8qNGVRDewLhKHEoygTDKvT5nzCwmKqEZbPuqz0lrPWUqNJTmVlPWUCjUyljAY2aC4wFdBYp"
    "i8ITs0L0WSqUxqyjB5G1sNJjZgtTekpU58HBhCgFOk8BlUd0J9Z5ClZ5vK/zlKjKA6NNIZoDixsYeRJVcaDyFGzQq77KU6IaD9Yd"
    "EpFOLOuw8uCpbIs4xBBSeFQjgq5QsMLjfY2nYIUn+LoG0pym+LpIiSo8Bes730Ki+k4GdUcLgb6DCVTiRF/hyaDvqPEkkf1l1PdA"
    "rUKaVxQfCTmq7yDJybrfBzmq7mD7XVJknwQy1naiTyIZtJ3AJg2wHiSwipm+A+MD2RX+AMig7giFsb4DU0Yl2hv0nQzqTgv0nRxR"
    "dzLWdqKv7mS2JqfqTgiisGF1J4SironYfPPTmDeFGK+LMV4XY7wuRXm9Kke1nRxWdnJ4T5PIIaz9t/BZCChWYgvjLSGeuJvw1Agm"
    "KaHEfvigzE0EA5Mf0bMCdjYVKkYTJT3SBIPn6R6uTH4e8RC0B2+O4MUxrkFjxhKOI6YxYwmn8KobN8lCnbFGJXygRw4vokjqPo6k"
    "FE8TBEUt2GPG0JqPoYYRhB0UskSALafQ+gAPO9lIJAjiFD62wcsNFlaNLkUogjLWf1EEFR9BJYygQhCUYwjKPoI4UhuPT6iouanG"
    "zE01Ym7ilEj39EWqo1kZkWGobolLGIo+hmIYQ5FgKMQwFHwMBRpmbdUGRv9Jp7GIWvE5F09mZTzVrZ56w5Ni2hTsfngKthKn4Mk4"
    "dXcjAvBP7XOIemyjQ4ptdCixjY737XNosX0OZfU+hxTb5xBi+xzKmn0OPrbPIcT2OfjYPgcf2+cQ1+xzyO/c59Bi+xxibJ9DjO1z"
    "aNF9DlGPbXSIsY0OMbLREd/liG5x8Hp0Bi/JkSM2OXzERhOrNzZC2P09OxtibGdD/e+0s4F9rFZtbfCrtzbE2NaGFNvakGJbG7Gd"
    "DWHNzoYU29nQojsbnB7b2tCiWxti2EJI2tRQIpsagRbB0wxsSYQijSrB0TGvhLfUyPFy+DBYjRwG00V2zJpQA2tCDVsTKrUmlJg1"
    "oQTWhOIH9MQr6tBs7a8RyX47qYGkpBL7EZ2tycYM2cFYQlIKkJTCSEoUSTGGpBggKfoTNo78G7J5cIpFbuVoDSTFl9iPqM1DrTVy"
    "IBJHkg+Q5MNI8hRJLoYkFyDJ+WYPj72DfNtRZVYFT9yCqVWBUxo1HrWo7agxo4LH7jpRJDUfRy1sVGgERTVmVKg+htSjd5VRIVtd"
    "i6cH9pNEq+JmvMGKPjrRpxkW1ocNi3Y5fCG3bHhGnTwuxS7Idf+KXscl91D3HMdYxO6qgh/9qbmI3ZM9oHcJ4jdlHXvmJt/N5eCh"
    "EMf1Ur96tmdY12bLdtrpVfiPc624I+zDXLLQhIm3bBsk4CKydAxrZizcWs+eXa6rPoxC3RyOISgTIw29FEyaCQjTOIBuo5rNan80"
    "2Lp0zGmQoD/crXM0Mn521QgVgNerLk0H0uxNkQbGAn+uwV3+RGrJZDRoUXZFMX2gKbcD8LU5Rmwa61+cfJnXUIm3Lbuz9YqHEJLu"
    "WxbhaBkvq+5y09fb1kNgkUhEgt7HxG8z4Rt9G7IpwF/gKIgr7pHTVG01LEITwNdDDdHfPoCdEbs+bRwAN3iYI4XsLkpZYJ9j9xuQ"
    "aqhzBRGJV5u76uY6ASnTQJQrLq53LbtpWMwfG9F7FUORWqs2hCtbM3zsKgAbPlJd8mX8yOslq5CFawSGY/ovoeyndK3RNs1x5Rke"
    "cWjgm72g72oxlJIoG3p6ZDOoeKWJg0H6t2dZKXX6iha/Y7mqYXcaPMWU3PMc6rA5H2PpsUw8Y6SQCGkdkMYAnkoWhWfJOJaxJ+lW"
    "kin6wGAKIvjNwdzyo3IrasZPuLTJC5ebMFgIfr3macFLjGN3Q+jwY4Ur5Sx4tjCK8Rq9RlCnz73gljYkTAQ2USvBk601xEnwnE2K"
    "ZjJd/FAOBQ6MhsQuQtT2dWQAGJQbGrgk1BBRw6E80ljRnoUjeKRABU9rrqBb7FWY6NSaLNOhF1lXdZi8PXO7xiRrOqYxwCGaU0ZC"
    "V7jxHMYBmTTkJSt3hUETedp1RbdDD8WugFp+1WlFjYHxkkgOHEQjPGrYyE2A2TyUCwa/JKbvugnxGK64hmETmg8/nLai2uXQLfQh"
    "yFfXnMJCATYske2LhNdZNHI4IMQnLofDg5lt+AlXXC/gPjMMGQmhXXzFl4g+VgcyIclbhsVXg7wXF66nP+rYQRV4nGjQIWp4mPES"
    "bbg67CSXiSKPrxejopFKaU9obMb2UqvwH9YHHyA1vFH1QULDg1UfLErervrg4Lz58X/21sT/8Rd3K6P/5Dr+ihDJbwnu0uOQTz3b"
    "9XAkikbyIjEWNeV7QhAnP/4lTuDZmPx2goZgZowtJ1IU8LroTtHQK2Tyv6wnxA17JZiSABQYjL6WRwhUfO2HSZQLQf9O4PAkRnNg"
    "EexbclAUkMSfSACCDcJdkIV6KIILC8Zxk2HhYDINiujvr+ZbAyLDYGJ6bzRiyjKIF3yxSTUBUeAxs2wOYvZkkUERzk4LYhIm0+fP"
    "S1mola9Jmb51kxiQJqnzP34kRYB5tZ0+LK2tyhQGyMRbD6FoNG/RmCwtylt7fjCt1NgsTn9oTic4hlSn381beEmCYzt8DY/Y17Xg"
    "9H1CJELF9bCTUQDtBw7yI9QhBsbSUVzMckxMiqV6OFDXuBwNCwKMbe8+ZRoYvpHNuX4Ch1L4Eoobcp1xc69DZF9ZxJrww12yoGtI"
    "44TCZsQGKBoGgwbfCNM6GOsgbkQOdRhUFtTHfuYQexghpqxnGvj1vwDpt9wrji03yCS834ef905SIl/pVthZJhUkm3uFLTvOF07T"
    "JwEJKVHPoBz4lSVL+JyW+xYKBIM/Nb5ns8VPqW3gwGSUeShGNsSsgIb5nB+5Av7SoBUpdMiTCBZBuIpvofaPMo1G7hOX/Y4UwV+w"
    "lQCIBmMbjVQTCUbDhgbeQ6IjAs/heajat06ZBb8Yl3Hwi2F4ioiE1frVswRuZWm++F/V/7+qf53qZ6ozHPXwphJWmr00pRnm6Jiq"
    "tH9GVRJmzsOfn9WK16GXicJKKU3WafCqVVI+9KW8Vw6I1C2zyGJAqvQ4j19JVvEVWf27Iz/M448fjX//myWQdY8+eTZZdtWNLv4a"
    "SjeCdo1MZFxau87nz04QuXGLCSZCxv3qFN2ctUuDMcJ9WM/MtAJgfwz/KmesXOOv/mhqDxANfA7ETZGGjJyba6HKuNxkt//jxze0"
    "Ktz9xOc6SFWgCWKE/n+KmM4ojnOd4hjiobURE0nZXCgSWyha5Jax66G5F80su2aukx/tjnJ2ZN6GprOvHdvJuOgb6mXO2+W+fGp/"
    "/mx9/vypjwTsj0neMkddr/fF294mOCKq7E6+oQXreLeTH+eGu8Y34fuX0Z/i10x/d7i7u+tkP3/OtFA2qtX4Jn3PfpWL6KeYE7Pf"
    "c5CBcuXvu2a2aHzjvv+xO0bgqOjoD+Hz5/EfxjcelcgA2p38FKEEiOPM4viPIQIFSPHHDyj7Jxph588htIfrHeVwzaTMELqOFEu/"
    "k0GkHP3Js/iPNo3/iEiLFjY0mOOWT8B+bpIb4gCFFiqzFCry0BwRftrqu1uGBTG7FlvOZDT6v+y9637bRrIv+n09haSflzdwBDGi"
    "cpkMaYbLtuyxZxzLYyvJzOhoGxAJWYgogAOAvkTik+0P55HOK5yq6vsFICjLcsYna2VkotHoe1dX1+VfDBcTBxPGbwHj0IfuBFgW"
    "NGQBo3sxDOpRdW9vnA4m4dXV5nQYXiZXV0E1ru7B4FU/wAcBtnynH0Zz4IsmcKbi82SAIzEJh3X5gdo12sOVCb8q+DwbsTCyQGdh"
    "nLJjhq0IVXGQwATLcfshtsUGg/rA3uRFvZHA+HC4zCFhNPamQMvE0NXDCRTLMNAqnC+cp3CZzqp0o2JdhoqTHsseYnRt1oaQZ5+M"
    "tCYcnsFOEs2YFilrAb9FbiQb/yvezrbj/7XBjlPiI/vhMBmlrEJoHoIlTmEZ5vd2w/FkwPE/Yf5DBActQpJALSdJPTkLahht2AdQ"
    "BsxFvTxFMj77cDkb9Zd8DXA+AK7o0OUBnH9L2CBIBJCpiWZLRqIvtR1UAXlSYKcT42mGT7WgC4gDJijCwSnxMYvR0fFReTyugzqg"
    "XwHM0yAAMgGsARCyyH8G4lELO36kIcmOKu23SYgWoWrtqQZjy3NVRrPG3lQgMTNoV9p7/Zpqef16NIte4/GVRWo7iHsyModpY3Om"
    "8FLsOI1GsgKnCKkk0XNjqDViNNNInYTRpMeDkSGzN/K0gX3nbx7VxP4aOfibtnFnbRRHRuxmjI/Y5tmQpR7H8F3wZt9Ftbt8N0ii"
    "i8HpchkGGuTva8kXcHI78sL8MloQwDoBnvsS+A5a5JfZaHf5WqtMFqUdbXRC8Gp86MfIzfBTCvMixmi4rMfZOGvGFi4tbOFSwxYu"
    "JbbwIEgCHvMaNhT8JqoUR3164EMY7SE3qA2DGpu3Bs8UFcC6wSjgKFWj9Cg5DgpYGyPBi7FtDx3D3vFDeFkRPYM9NwkHMJYXWYW4"
    "i1UxewuHdtirz9I8wONYVfphXxscC/CUwdMCZyIhCMVhn6fvNnj56sKozvmRQC/EyVA7tKDLwT7QbOxhAdwAHy4dFLpyM/FxhFxF"
    "wCGRkRXFqk6UiUUx/YAB6Ne4J0FuCnG/g6JJvGvKBIF9ZiaSKBEhF4p3xnfyGeWU+rPxRV28QZVxxJA6dyQCsrjVqxSucNlBJeiO"
    "fZuDorBbbXJzfm1pk6yThgNFIs1qAajo6WqQ91UZKqjkEddwtekgSEbTmoWPyuocmmbf2/kuOi9LufSQhX9cqbHAaz/mha+qtuKb"
    "dbxrKD/lZHdQfaqer5Tc81u+hsSthNsuBPe0mBBpeARFP8uqGk8GJkiAKT19OMsm52h4hSoOONHoYmlmwzY95NvtMLtIi0XNNTy4"
    "yt1zZfpaLAQi5fyBielZT+CeBA17h/RxcCkyOzdiWQ4wXNEWCRhU2lYj9rVvb0aX6qLMt2dEsR9YEv2E6xj9+/rOpRJbLONIk2SI"
    "DSdXOrtwk5WaiUatCQFIyhCz/RyHXGjAom6/qmHwPwjzKziFI5beAGw9vF6pkTmaAs1abDKEkEYSGnORg56OVN0Qc7BqIRlXE/Is"
    "UDVwa3xZBM7x9GCBtnfpDO4OyIwTLjn2sw//O0nhspL+lNPwOYPnW493746Cg3cYbSyI+fudCS7gOGr8hokKQ00oNvFIebT4Cq8D"
    "rb8Eod4qRUNu4HYlaaTvC2qBdW7osSRCO92//C/HjDQMaoYVbqq1BfZ7Y7lwi19RLkY81YpcQ4xXNovxyg5ivPLWxHicYyPTrn0v"
    "FdzIZoFBbhShCdGGEzkNPN2bqJjOj7RI/XjpS73MX7L6jCRkA50Nt4o3OBy7gp7xLCggqzYlxGinQqmaaa7TYaOuV21WIe2hw659"
    "didn2WwK69ScYJFKdK4oGcL/EkWY033fSdlCiX0nK+68pnfqWlSzwvLRywVGemAUMu3JA3lESUCp6V9UmtUJkJAgD6+uoAuzokor"
    "GNEjBuM92amYudxoi1PAreN4VU5gX9IZ5sPrsueIv3uXTA0EZffmwU9lm6Hn3kwj//mAqkCWD4cIRiGGDFU2TWM6HkLFuPSS6dQg"
    "6UEMRwbwU+Rt1jjaWMQi7zKvjUXABMhGMGuO67Sj+RWtPR6sQU498GLyHHbmZBQYs9KUkR96MALVuwy4LLx2HRY/Z+k7YqudvktO"
    "S1TePHBAadc/ghtf8d1X5IwPdXVUarc5/Arf14oeBKHgbWSH5HZUPdyNRDCPpv4ZRMu6gq6mxQ5j6eMgl21jYpwJ2sqoGVGoTZqA"
    "8R1KOPVgsnFi8jXmBReIvgst4s1IVIce5ym78er8/kv+TouuwrMfqaE5xk9/VjnMb42MXUaVBdqQFyV0IUiJM4dlPWcP+671E1sg"
    "1icjtC4a+leCkj3ksNGcTzkf7dt5AYWb+Fv6AX1q7XhE/lUesnJQBw/J4eUE4U4f5YiGPaDfcKufJ1Oewk86jbCmUZzSu3BI0ugh"
    "K6CaJPOU5/e3tGEbCInJjW0EvVlwh23oA2xwCpNSnWWnNQwg48+QJB8WOPIZUGLsQSBiKbFX6C7Ck+miZmdvojicnfiwH6AKsHch"
    "T64NwQiUUSZyUZZ36nDLmU5rOBRzl/dyNnHAHcNEl7CTT2EsWMPE9o0ynizaJ8gaY2cDIKObWXgJZY322JgJQTYmAd3u3UFZ3SHs"
    "+SCk4dzoD+ppkKGJRkZ2MCgX13eByLc3kCUlwR6OVB4uQxQLR+Yw/h6HC9v2uxgq0UZ7X6esfzxMJ16EN58h2ycjMom9xTR4Id7c"
    "2AXr0SzF40kMXC17wU1qm9aKNzzoXGRlhb7KTuB69oYp2QStT82Km77JSc2W92ZJJbI+RLZaRKbbqMdGD1Peuh3Gg8chxuljZKFx"
    "udfhQHXTnWNvF3FS1+meJ7/oGvngfXTfPGtT9qtA6S6+fJpndes9cD32o+0w7kaRtba9QrvelW1jUvXbbttDZji8snVrnFg30T52"
    "r8RJfZjMZhi9+nc2uayBOLPNDbSFgOPPPe+tnI3oE1sRH9urW10vg+B3wIJJwbMpOtaZZMGf+qTP/rfJLHuTP+ZZaMTR2yUWYhS4"
    "ho3+tgh4D2eREFHssFI5OR1t1eUiRTEFnptBOnoPn4TbQMar9PGsSOAK3CPFwlEMd6EUdxIKHXfSfBofX13thnwMNeVDjzI+pXyP"
    "8uko3Y7RCQhNOvgxsRuVo3+s07SSgsRC00qjaaW3aRUwMHWXxr3CjKOcNW9Jks2fTaVXkwybGQQ2K8jGqzIcpcdCy6QMyc313SR8"
    "01R8R8YyOx6veN9zxZp8/bbK+fhaxIxxyOTmcC+G/pBVsfPpkfPpCeqlyYiYz4f+cmK8eM9z08XsWKuMOV/5w5HadVFeMpdyXlfs"
    "1bCxl3w7jY/qKHUWz/EAk4+Vx3g3+ei4x/ML6Yl/oQUxz4aiRRFOVSoeZSGhrN6J9muMSlMlkP6sQFc8/rkaDbQiD8z7/iUSxaeO"
    "qTEkEpiAlggEaJdeIGaAmd7aHDZW0Apuh7jTp1KQ4mql/PeeKP5gOjXSNzGdGylraiWbLtO5TCplpv29AWcNQ7HfwWWDVd/NZUOo"
    "tDWXjQh5mBtrfHtLgYToNSMbcjs1Y00kKJNuzXQU307lrC69etPWe/9Qt/a+2I/2D5VWZj/i6X9FL5q3ZZGTCOr9O/H4knxuf3wU"
    "PYADbPDiUfQizSfZbPD0UST9b1C6XA0OPiyjaVaiIuEtOsKW2RyYssG/Xuu2ve/Jamnrf05wQL46S2fztKw2dnhs+y2xp9/vj1qi"
    "2RuvpFW1Fu7dd/aJWPZe5a5Vplkdjbow9APCwPJA+qb4rSwGx6INA1lhRH1WdlKv9nUxKj/fz9MPaD+F91JlmXnwLhd2dayeSkSU"
    "b8uDxSBTVI7KHvOSDXQFk2loaZawn1YTmDboJjWxp0zpluhb05svqjNuIEYWcELuoDr3cN+Ua/SH9T1phObYbGsGamiIx9TFl8uB"
    "njqs/3tvDGPGGhzkZPWKMcgfJZMzo2fvuBkefBQCB72ih9XYZ8CYpTB+0apPoRXhQG+Tv0FeC0lq46rRz8n3RA5wqgZYdFJMZFCP"
    "DvehsjCDbOPmGr3mkbuWeeSuZh65K80jI636w30lWHmETYkrZnQaqq0LrdH2Ipyq23GsSnjElz+sdNoYm6OYW3ZfXW1Ki+6UTJFz"
    "3A/GzrwXL2LiqtMjvvXq4gUQxwyJzjFaV3M7Q75RuOk11jhkNZZajaK2cujYoaMLhix442JR1RvCe2FjLtNpUHuxmKiAAq/zERkz"
    "Sy5uXhciDcA27e+PjpB9qOBYZQaG/Be/TEh8FiE5ahQp+SWFMtW4lcTH0QFWTO5twkhNuLtNuOGb6f6mBVg/b3IKMs4W4VGpzpcY"
    "7V4hBc8O+D3j/pbimIGkhZb0kl0Eoyl9Ioo8HaUZ3MLpMFGrLBF8JfMbfBbE9TQWroO73Pc76ZmMOPco1JKJv4+g7+mAqVWWEVAw"
    "+O/S8TdkoeFDO1nx/fDuSHOrtO0KBB/Mbc5yeRcXPnwmD5gYF/Nc8bbKAjTvyd82by2HhydozlBYOwUJ5muI3ZAwZh6Ujs+iTPht"
    "FoLOlMeEkTbwDHp/zUHnW4BeaPcqvjHCiG8M673YLqHUDddHX7dEZ8csPDg7/mwI9P639ANq66Gsb5rL4uo5Vhp/8JZ3Q8tJhmN3"
    "SMKWNSgGpFMcMtuVaMtPNvBjXTcu8+lUZGuQKd24zGFQFLsR4g6K4edz19bG3RDYVXTnUhWNW7YP5pYuyZ9iB3nks0nPTcR1eUgW"
    "TqWWT9o8XXOjufWwo8GqidyZOw0uK/Du3Y6jy7Lz8e2z8U1syeUNDrMhZRbDrCf6Jbcip5n8UWOuVyoTzfK7jzpf0h89Hdpi3/uE"
    "k3GtgcPBaCU/4kR+zDrw9TI6as1PLBND5VMgAHyjc6ZVCdY1Z2HpEt8TPgjKf7g+2jUIeapRctcgEuFB5VCFS2dsxWgyMVKDQ3La"
    "m9fagL7l7sbcx1jDRRBDLIbW9jleMbw4XISFONcGrBI71x4wzyA14cp0WuHwsbDXRMgFDnQhyt7S6hlv7nJ5hD4t/W7TIhr4KWdG"
    "TUnDiAh2WPSo2+RJtInou2+cuYSaXjLsPWeffLPseG5CGRy/D2egjYyYOUPFHktkjffo3iaxAGHwn8DFYEa2lja/4s3mB9xo6vNT"
    "AumQHHsW21gfR21NitqLPV63yYKNfRlMRDv2PvHIeNcEv43hiniSB2JwOIyBaNm3ZssEZyBvSWThJj/aMq55uCsNqS9/L659+F73"
    "f7LRa7wCaI3/3sM9fVIFPrZZ7mpkm+WDl20+gotzMYdhiky+FzsQyz3oYaTtsRB882SHcCCFbTOUAnkT+s0HqjOvCh+yxnfYciqj"
    "gtBRgDn67D3loDWl5mlnTZUOrUOriKiVeEu7zSQjfSIjRhnYIcsvTe5BJnuwmnnkbWfklHIsQDb2iEGyKt1sqPVlMPNg/Lj1Nc/0"
    "0xawn01P521PO1/v91b33i7G6P6mr//+il8GCzEAX9/8AJjnD97Xo4N9lE0cnR4f4zS5jlxJkxeXdUR9B2tL52BFVYKOTv0nDGGz"
    "PJI3HBhLi8B4VETes1yQHLyAa0ZSy4h1SnOQpCKjywacGLMtaxAL6UV57hK7FtlPA0VhlwJsKRKLq6uYqVZiDk6/quWEeaUfZxLf"
    "SlsRFqCVxq7wwZSMS+S5m0z9G1VrCl6f3An1aN66TigW6JtQLHLFhIq2fOYJxZbyCRVAcyvmkzX8hudTEoLWid1rmlh2BXan1qvZ"
    "7Dq5rFDf9LJiV0ywatNnnmLWWj7JpP1cPcmi8Z9qmjlvaVLsPwHF/jnYD5Ke7ZoYQBP6+iGxD4fE8kTCXZ1rcFf3uylt739JStv7"
    "ptL2V0Np61FJSX2U6BkwxemRjvN1TEbHOWm+CJYaGAb6FyoiB9ofsUo0ogkvczJqy8Mh02LtRpkulBaes5fVIItyj1lB+cMo5crW"
    "8SWhBm3uLgf8lxASpEfl9vYxwgJbFpGoCYMROB1ky6WjF3uaw9dwq0/qGq7J9UZdcKykdCMv8h36DTchCUXW+6+n+QZdkDDrCUdW"
    "ghwR5U9wADi0U8XUbGdADTeSDWc8g5AjLqG+jaGSFei2VY02+2pAtMHIpfYPGTXX3ignQ+9A6pQKGDQcoii1x6TCehDgCQZF9xAq"
    "P1wW6E/JChC+0OIZ4XM4mhNiYnGsqwTBieW6+lFpQ7m3D1+BSo8olJTPWdYhd79aSsw40cleBZQhDb6PdvqyTzlyeUwrbG8KpkbV"
    "U0iuBpQJv/kxmcfQFfz5Kq3jMVuxp2Vxga40lH5fXN4g41f/OxgPfsqunoZ5Db++v+p/d/X1Xgg/H86Si3k6DVkJd77q1eh5modj"
    "3h9ptCLHhL+4RG0qG9H6B7GcyZVPLm6Ga6asM9l2gjHK79XDfHs7LI/y41EKf8R4lKqaF1+yHcbjT2OH8aKLHcbT27XDePFZ7DCe"
    "unYYz27RDuOZZofx0muHcX+FHcZLRXnu37odxv3Pb4fxmwFARSqhrvhT0ETGeCpkqOKdcKul39OTmf5IJu56Ql0sJmdojM4ez5n+"
    "mT9p3uOssDJ5w6zD1TP67WqPs1QBWOGzKnoKi29tHKtbBNj6WMisFiCr3WW0KjrbxIh+44tP0QFvC/mgD+14XP+hUWvaI86tF9ru"
    "UyFjrRmdqANemVS4PWqb2N21QmldK9JVayutsD2etWuF7PHnoDXAgtysyNwFfe16McO6xSlSuWDRVe3t7AAmV3MtX0tJnaIZdYdm"
    "uy42XVZZLgj7Ak270y5/Ol0FaIdRNrOTRc3nrSncGff8aYR309UY0AaF5GZsUZx5itdycQFDh4pneDgjrVnZCvRhVMC8MzgFGqfj"
    "3pEXWIlnCI8lQzKAvFVxkQY+cUMvpSUZ1LIUAhmljWI6N63XPubhpA0Da2/a2EjPB2ajc7fRKbmcL1chmkW1jmmGjyuQzEaX10Yr"
    "+0RI/Zq2AoFm5yjGV2j9nJ17ceg4GhmTZqOVje0Ew9sKm5Via130NWljw44DFkto3BMRBuH2Ou4ZJ4U6gwTEDzPM0AOE4TfqEThy"
    "2E8hxRpbzKYvSUQncFOb+qeNElwPzrLpFM3zhsInU+dK7t5VzvCeb7kTnfdTYrQXJ2d0gkhGnvlOKX4GVnbe+Lm06ZT+ollFGdIp"
    "CsT4DUJFMzD9A3f64nK/CWMtqIAn4zHsD2hHhkDcubgpIJwLoXbzxxp9d2aTBZ4MgkOiGLE+UBa3mXzo5ZJoG86oHFmtxRZG2aiM"
    "ktEuSTZcunL3brK9PUSBZoYw7fCb2WJrxWxv1yRqLMIMKygQyZe6aCBeJAiLPkaSPkhM/AjZq24LSyyOhpm/e7cem9JOO0c4tlOY"
    "Oc8BjHL4w05/YL9G3zwemjWfMi8/H0DRTp9WHAIjcWmRlIeUML7lPZE+LLe3Qwm0I4hpfVQehyhELDlUiJKyRCyTn6hKh3STD8KF"
    "zj6Lxyn1IKEDwDwCOIwBTQBT9baBBJiX0G5wgFS+i6ple7zzy2oHV/I2OIb9k9nqqtRd+SNrI/+B1fXpl/GPrPEQr/GP8ukKuEZx"
    "10/Fdz6kJ/szKRP4yDb+iNKElbVpMgfZyv0yeUPO5u3Tp6QTTktb1wZ8d/DW4vl8hTNRx9plP0tXYZRoghOjz6smVApYtK8sh3v3"
    "E5TCpGrd+Le2yUJuumlRExbo4/3gMbkZYNyuZSR57oFbBuE6QDNQCNQYdcgHB8qaLywlV3zqCJX41+gkvQrcxhY/mZ8KTMMOnyth"
    "lVVEO0SMK9hKw2sC86TXRc1JPwbShn38SF2EV0yWFxubQxy3Y0voB9/V1WgVgERUj2sviITErF8bFeApXORdTIAxhwQgKhH2bLBk"
    "JRypmryyRYYxk1zTlUcnuqESwaQeMIOj46gmPYrO9lJug9EWicbdNUS4qZS0PHDRW5ooKlL39Ou+mRxlFHwDeZyyVwXhcDMAXrIH"
    "TQpJrTkUMR4yHimncNi5JLKtzbH1JTCRwAnVo0JwQiqGRdlLSU/O9Zxl7zQIBad0JMExKAqElOauOrq4VPaVIV3DCyJiWKANXHKS"
    "2WtFnzlTfifQK4yOaT4HApbRfi1t7AWKumgeQkaMdwc7fREkwQaqd9YRdpQXoom6xh4RgSHi8qV1FnNs9hXcGDXb85nWGGK0N0WX"
    "iP+UshwP3I9H5Cw6aIuXxYbwNly/Bhg3CKcYeSdIsani9tY3r8QvDXmmuylXtkGAr7TfM4HSpewmWbtF+Fv0uChqs0WtQ7mpoDqM"
    "uQhFv4cf36Htzh3iFOYZ3ZYakK+9RArDtrkIM5WrpM0Z8LMkRLkSWMC62t5eGhA8QoG9I5EPd21Z9kPuXfqJGrvZ3NrUknvYOfl9"
    "WXZLdcGG7ZACnpP9FeAcOsLGg27GWg++JGOtB6ax1s9fsmXHk09j2fFzF8uOn27XsuPnz2LZ8ZNr2fHLLVp2/KJZdvzFa9nxYIVl"
    "x1+UZceDW7fsePD5LTv+piNsHEf/xsea84wenz7ubCReG75H5DdP3Gts+SS5KTtcOQDbagHV/hWrzabw659me/5hPv7LeFR0/O8t"
    "0cs1AI3KA6AxYSgcMrCasgbska2CwswoY7+FP2X7Ma2q5E1KWAyIaIDjsEQEZFTRmDnC6Og3iQZhIztwxmEZAel64sNCQHfnCQc9"
    "8BSv4DXyntTa6j1hBtzWK+F8tTRspPvfwYBbKBaPRU6zAjrGmV4DjcGblR7oQNPMhfoGe9d2+9Hy45ySIl5VqannfVNhf98wGV4G"
    "aa1JsUrQpsXDxI4bPBl3V3gyKr/C3WYsDlNGziA5zDSvi6HhJamPn9kGa6UZPn1o3mu8omXC3jsOudctQzoOSjFe4rkMaL6BabtD"
    "oO/r1V6B1oR19gp0B9byVyMXWF+Lml0Gi44ugytqNl0Fm4Zlhb+g5TrT3V+wy8BsNo5MkzNh1dGZcJ2hcZ0IdYci7wrXyKWLccTk"
    "NYmS1DvIE+z45QhD0d/2nUo3vVTm6so3Xm0HXNJTYjsJWSSlgZFgFFiiEDVpZLcR8oDLjsYKAoHZFCmC1m8laBpWkXhqgCva5xoz"
    "4XvdWKTQv8lSRUJDwQ8VB9OOq2Ro22TpKqmh/EOuCmsHWtIUa7JokbASwOnbFmd0XfcmS25DcjpCcegpuqTj3HINGVTyXWvjpcZN"
    "1iFTmiZU6NCg7D+1z6jQyakpFSktZaMKDYr+fmXRqJAzSsaEloJJfQYl/3llyaSOM4qmlJay2Trp764sWl8n/Lmx2GKOZfZXlFnM"
    "tQKLua80zi/ZxkaMb0Jrcg2/i0jIlkb+LIQDccvYGmxuWtTEg4WgQblstVxBtgglxbEoXTKUOqSoyCIQhXou3R8rFXm7FpG+C3F7"
    "EGwFfXNk8rzirgE307FE1SC6aziX1wJCBXYd4kXbL7lw7OqqlCZ3DsxXrQIcayPKiHapbKu0YfIjUQmAubzRIGmM7q4eYyARrEOZ"
    "xCqvehkD1u9or2sMDEvVXEdAb7UUDYpRLX1SOdjb3buFBETM2xRwrN1GtGOT55pux6/jbTWw8EivK4pfr+EvOUajVsjozNJc2/bf"
    "Dqvnmn27PI9jbet4EluabdrF6tnVXxM0oJFkqOjl8YNPtv6avtUSfEpqPY9IdDXRRi7mCm2qmy3IA0unbPnPO4pjxwXbqx3GXE5q"
    "J1ClmG9R4TEtFg9T2siNqDZfj28xuUfE6td3Qds6NgBraD2a8Bv24nJWkuOBbqwTZ1Hoy8Cadc8EO7Npzp45W/bc+GZBDj2Metyr"
    "5jPU2vfw9m2y6kDd9779jjPR/97X+WdDQCJ2tHUJrBhCnbZtfZz0XpRN16Ia1rXkkXwTNogztBw3LlnSi/cCt3qG6eMvNP9kF5ro"
    "r41zQvenU1ITXk/cxFSMvgn72ituYvkb58DI88lFSqyiFfOhDdHHz8g/nCsmu+wuf5MYCH/fJxn5HekpSC6ByOr84Sv4u/MV/MPV"
    "7w9XP5+rXyYL7Za53bmss8ufcP/o5u+3jleg6pDXW+wm/AL/cPX7z3H1a3TI82iPWJ2DyyUFvV1QDGQ74rEkg9ygi0WAeyxSzVBw"
    "IhadGj5lLNfIvviKNVpq1iCC0P1HNFX63gHjw5Zvi5eIsP1zXQEHteh1Q2+cscDY33RF6NXFfPRXFaauIVhryOLHRV0751pSdahj"
    "aAywsxCpqTzO3qc1NY5IKpeeNrk0NYf5ogLhSxZpsCYsoU/o/iPNNZ8q+1dPo7lvk2G4ylerfHa8nvLRLgLj+DIRWI7rAmVkPcqP"
    "yQo4t/yham40Kn3WG8y/jMI8xq/GCexJaveYFfau8hOJQFWcbtAZMzbtYbUBZjalg7bOh8o4VvSTcKq1I7yl274zfOypzpcvZERe"
    "mcpn1SsToGCVGfRIwCh5/PBUBxuWD1o7+4ECmqqV9HV8WaO4fSUJWGp7lO/g1hpWbFYeR3EZwQWTbGCaAg4K0DDp1KsxAUHqdRIO"
    "xVDC+7Th5Vg4mmtDseTH9AtPn57OgsszZBWZ5zAfLuE77Nim83vKwDwByfHbNR/F28xv+4jxdjA64gZLupFRfdAY2Eeg4oSm+D+u"
    "T+j++1MA7T+F+zanrIaIgeXRJAt034mlutWeaaHIQB0JDZMURPDakp41mdzsRLcBKgQGPruk8bfy3qdUHIod1IQLHcHjqUwJBI9A"
    "jbIELxq8pmoRRkaobWEOGHItwOir5aB3hgQojI+gTFIrUnJ5RyYR/1mRbm8bwnAYY8Qufzy6ubzs5YLOKqUKV2AIEhiUoY2WgjlM"
    "+mTdmWwFl34LMjRWXjwUqwEWDcb2GFdwU45mXLtz3U7be7H2Ghyo+1UuDQnUjSqXlgRe3ZDnzpR7mAX9NpJrVOSmdCj6PdqU/3pE"
    "Brnri2Hc4nLdjcS+ueWW+0rD3lut1WlVafUar03Mwb1VI9Zy52opuEV35zsrE68tnwnSAudJNm3AY4F3CSRKVRupDN5oXuK2tZwG"
    "8tHoMF6b7uC2fYq/CCG6rDUfb78xSsP3StxZG47bE280r4ZCdCFpbXhj+6xLGgpRgtVac8zW7UhWlSBlsbXhbe21EmkoQhPg1roT"
    "st8cpGlMldTXKMRr99FSBpMUG0X4LTxayuDiZaMQrylHSxnmpPitNho/Rxl2bXlaw9d73ZaEsTU0RTKUsHplGrLy2ucuDcWsXJuO"
    "jL12XaehnJUr1JbM1343aijqu+5FKZl+7XOphsL+tEZhXLJfO+7VUE6nVet0T1eLQyF/7lxIZS5bo097u52LMbvkKtmhsJXr2OuO"
    "jQWupYtnunfmPyF92aQCnhg/xvAJNk/p6U2ezmTYdBbNZ2BkcFwGqouHm5IslOSblEWAyxdprFAH/b7G1njcSTWmxeJRdAWwZSPQ"
    "ZpDQyCoYJg0eNsBUpPttaxr1/8sw6u99z1Wa6UG4vCO1l/UB8/A5ENpLTce6Un3JlWrc5Op6+JvteHFVV4G0L8ikIZntLjC+RlHt"
    "YGo6lJpWg8BOaAZVwyv36FKDUOOWMwxI7dqAa5EPoIxZMFeIYhXUK8Qa8H6FWKPuYUno5AwrOZvOshyY+SDIVxSMYOztBec9o8yQ"
    "gZ51RpArmxHkSgdBTs0NrgVEjytDY8qMabaFu2qmpHxPJUEtY1+iwDmPfCvN5xjuW6z+t8kse5M/5lnI2pA5gnFB/W5Uj/6mhPVR"
    "fOSL5zraqstFunXMBN1BOnoPn4TbMGVV+nhWJHVQMwXDUQzLMsVTF+dpB3k1ONB2Q6Ff0YR7lPEp5XuUT4WoH8HILhVo+z/WaRpD"
    "rX+PN329aaW3aYwl7tA4sp8e5ax5S0PaakYtdtfEkTtXjMySL4Xhts6llMaL9zI/mb4csx2soic34KG49XGpZ+RitMUVe+VxbjcX"
    "1/iojlJnnI4HmHy81H3My4NOPublwRfkY059Vk622cEX7GOeHHwSH3MYs9U+5sXBrfqY6226PR9z0UnNx7w6uD0f8+pAqRInBz4f"
    "8/Kg3cd8ciB9zGlj3KqPOdT4uX3MZwea13YkPQakU7hxfukal4WlcbGUK8zCUuhJzLNAOrCZZ5Iebz6yLWSFZow1NJROD07IP/Z+"
    "GcHWh/86x6vXDy/N4+VmI8Wfapat/rCb0iiUO6yaYYL1IJp8QnQr3MRznGphag2nT9P9lH0njGSdMTNfhxHG4fJVBXe4P9le6jO4"
    "y+UH4i63OFAraHrw6UNRnR78EYrq/2+hqE4POoeimh98WaGoeH/cUFT8xScKRYW5Lw4M43JOLNaTz5BEqdm20bR89klxllje22zq"
    "Mbm4vFMSHjmDEWUUizR9d0SxxitG/Kq2MAGqjEGevtv45U3AGhajtQGcCVZRViaWGpO9w0kKY57+lJPkyBH26DX1JrM0KYUJoFWD"
    "ePlRyPk0Bw3w+UpuY2XHF9CoGxD3sMHhB4quPxaCj0NcWdx4QohtDQOVZkELtdWUtrAV5wPt1zPXzXIXo/8Ku99+2S6DoXyGCIbV"
    "7opmtHRLPmO+kUIaZnZhzCfj19kpyOc0vWl5Xe6fB9iCMKT1koFoWqIu9dIr58JuEFQ7vJRSLp7ovUWL4UvVeKXeAXqsNnLDNOlb"
    "cIyNCeyRj5ypkJ6tWh2CFPgkAp4NzaqCw1MrTJfpnCWVi8fIDuLNvgUOSI0K4cUuA9FvgA4EpswEY80lGGvNwViBV3PAWPFqQyzQ"
    "0CPXKyPJIV5dlRqHXDqM7yU10EFnrU101lpHZ0W+yqILn9lCzjZgU/qKQX6gi5/Ouomfzr4k8dOZKX568yWLn15/GvHTmy7ip7e3"
    "K35681nET29d8dOHWxQ/fdDETyde8dPZCvHTibqrnN26+Ons84uf3itz3h1FQ3U50yufZS9DC9QpqxrypCePReVDjMdLA3IbeyfA"
    "6oCUa2mW3e8yyvXTdAz7+zXJmISRL6smsflUU9zEOWwpihqs+lqJo9QQbSF8Rtp8aBWjYsWhVegGmTIQvQpBz5qjy7ZYp21L4D5a"
    "AlP3FB8Fo67hr+SOdFC5dOeG1zaaYgMLVFJUQnt0JQsmxXfE2SLcCo0k1BN6QWG0xnHGCjalBRBjQcN8DOIL4dSZLwWq8liIxgYS"
    "88yU9NXcDiH3mGxzkZ/w/xam2QIvQZpPyIeBF7HR4yVvjGxXVJ38Jgct/7hBaxmspkFi0sn3B5q8cnkh5ZSvNDnlw25c2sMviUt7"
    "aHJp775kLu3w03Bp77pwaY9ul0t791m4tEcul7Z/i1zavsalHXi5tIcruLQDxaU9vHUu7eHn59LOpWyXnZ+PaYt2xw5hW1pBbfBn"
    "2pXwiFOO1FBluMCL/0UxTTV4DqJnSZbXO8l0aiaU6UXxViuY5KCIkI0VcEN/ia9BZ04bIAC98UMAoPAAjs1pVs1nyYe2QtAErA0Q"
    "Afgb6uQqdAIs54CPT1sE5zO0P4VeMyvPFTnv47h0yvmjaGO1qsjpdGWBssNCTNMMnHCRvH8o57fym2XuoZcxzjd31ua5BJiHgwuC"
    "WZm56iE3jO3yBeMb1/mC5mGdD2g61vkA7YLXqmA6XfeTl7Sl1v2Kur7uR61AEjzLK1j+6ep8uON00BDvllJZV6CH8MHO5wsD8KIx"
    "pwup0ajE4g8NuiV0XwH68nNWZXSu9UUZcjsaJUv6wHVg/HOWB4FfmV8UFHMh8FsPgV1Ja47ry7JTPMJnWQXUO2VFrdBL+b67e3cU"
    "HLzrFaenQczfS0erpm8YcnNoZIDz8nTK9Vl6usiVH7DnJ9k0DVAX4DG6FpJovoS4HoU/HfEHOAuODYtEz/th2hNH1JiHsrWmQ+p8"
    "iVwd7R73JK2L9A/ETI1UieHAX2JTY1TJSxOlw2OjrVh24HFv3kh7iRxKV7PmvNmsOe9g1pzfmlkztILxN+oA8gXgtjUKZ9mbsxma"
    "K6NXC6+XXHzllEpn45SpSkLSFOASZ/W5SpxDEn/oKyEcpsZiUOvSTNdWI3lZTNKgD8Po/XbkW6FRY3mwukeCM0ciodgY70IGltxq"
    "G307Yriz/pU98pYUGkFDDVbP/0rGf/S9Zcwnf3VGZGQZUaI7G/rnOk8ZcWZSdSLSBmrQtIWX3RuEokynORZho7PRR8PohUHIyCRG"
    "6kfl4hFR2lhVD2ZJfh44FI2t2YE/L1/QKpodNBzWvtt2fad6hkZFjNPLb6SFvNrIyO6VlkizF8cWCIUl8OsiCCVSyO7VVerArmA+"
    "mQF2JXlYOoAp+mHFz28e/9ZMRNFbmeIxuM+WecCB5VX8Dl9w5epdRipRmBzYEJeTpErjRzlexgb0G1jkeTLVU17Nk0kas7Wo2owC"
    "F9KyDlkR1SSZi1x26xG1hfkEi53oicLKrtc+glU37PHU2ATujc/dW4rSpMvWHV9332Bmx3xDznoGa4RYpqFvBmB9FO8ojtFAC4mK"
    "CD3P4WzAwK5kQIV2Vj12V5WOcYGK6EQwqskJi80Z78K52DstJosqYCij1mrRp4/q/2nOai9V7S/gG1F7ubL20qy9bKt9yTGEnMOt"
    "0bShlZUZjdAQELg6TpE+YoHJUy1dY4U4Egh38Yksau1ZN2mOceNdc9g33HbNO8hk1ewu5o2HcX1jW0pEsL1W95LpVLFLnRiZqF6L"
    "ixg28zcUXtiaUFta1HZQqy638w9rDQjbaL4xaVvLEZCOVXxcGvU5Hp3bVyEIa+1u3o14rtVdfv1PZrOTZHLexDu5XykK6aW5aExs"
    "QvFJ56/xswUqiSy9JXMbZPVoY5fCHYcMxsc+yjwg7RHdgnhlzJ+cPzxEGyXWWEFQvY31YwfeWIM1Yu5p8Cyx23tmmcH6z3Y110if"
    "2FTfvftUuDKW6SkwY+iGfiedqdA6OYuO43I+UtqA1t0H6J1P5NWUBFwWZfYGTblIDACUhx2tBvchqZAqsK9VLwPROD3UW0BHCpc4"
    "5AYjaqAmDrU9KMVCd++eLAzRQ+TLFUaniDKg+hgLz8M7KHFP3xJmAeorer+xSAJSkAHFp9HlXDjOxslJBTdSAqSAyy2cwDAEma8J"
    "1qSwRDzFDxZ1BZNOvRfClUB7zxz6fW9epugLbb/xCWtGxpQDn65XSndbNpnoflEbkwGrByVD+RqCIW3+7p+ioDf3XZOHwoJPDK1p"
    "uUdcDGyruUxPe8miLh4z7kargwL5uFvGlDXZbbI+Qk2iEFyleuYnvu24yFfNG8vhnx/2zj+rfCzYNXt9iVzz/DPBJX9lI5EaVafI"
    "I5rLw0s3J7OiQv8F4TMtaeNoa57k6WzrONpwX/FamDM1j/7Nbo5MtikXpABGkJLFTWNPIcxbcpE+ByaDnIaMd9xBDfXTIV5NsUdG"
    "8Y3srtqkyHe729ZbrZVFr30ZNa2UhtDgrB+e/LgxtXeSkro7vMZg5pbIePQST7GUHweNlRiFML7WKWo81soaujUxCZF1ZMEspIqs"
    "4J3cIUEIARqk7lGHEH/1IRBlaLAeVi21DhmkVFMgDnSuAvdorH9gqzWgq7ZxJJe8lnKMTegZQvyeoHK6THxjKTAUsg2MO7yR7niL"
    "6tKj9krYnDevKvXau1gcjoFvG5NEtm0YZhL3JMmnM9wpI/TZuf/Gt4EjYwXZizQVAgYDrJuX6z2MxUw3t9UtSEDdGoX7TwU2EOY5"
    "0jYQpZFT0AwzddQ6BJvFNAi1kYjeQQOKd56dwErlC8esQu2A5qZ7PkM1FK/Ou1LbamTaKMPPwmSPGwGDeS5B8LmVwCaPmsZpPAog"
    "MemEKchJNsBG7um0qeQ7GcYlEhympkivGqZQ/9jWuouzxuZPOWdr5T6SjUZBw9xjlnU5Q7s4RHa0S5wVk2SG9jjcO7ZeLklW+8o0"
    "LGjotD1QYrEbH/NENSBLKajx+IJwpBPeYv8wsEazEu8DTWFNf33au/98fxl1/zT/oD49eLk8XkZ5wYTUz6iIpqn2FzpurVGULHVY"
    "bIylXrhlwYo8zdpRKVFTQ7uGQF/7mhJ0q441StGuxldXR03ZjpktirJdaK7CbAoX7P/QF4Kblwshhb/52VI1yPkCmvgpa+TFW8vj"
    "fpPMzl4j0ranwyKRWcwBbkjm436Pb2Ld5oerRj/VkFDhavyVnOsTjD4WLquaaBZ0rMb7ZZY4tepua8pDzVuBDJ2ZUjDBsUfQs6KB"
    "8BWd0o+lcGOw+gNcGdoHon9scQiy4u3bR4+oWYdVNa70T1mttmc0kwFmWPZYWUG9SMrkwkPjdIsBtG9nI62rSwMyDJBmCDi6qwuz"
    "TIZ8Gsdkgvafsj6tMtNhkalyBulhxPmdv0YvirJOZoMnHyL21atZUp0N0n3+CH9ng78/4k+DfzyKDkvMkO1HL2aLapDvo81kmVID"
    "0ARTiGQGP3/Q/SHvd7O0v/8lWdrfNy3tf/2SLe1//DSW9r92sbR/fruW9r9+Fkv7566l/YtbtLR/oVnaP/Za2t9fYWn/WFna3791"
    "S/v7n9/S/in6Q2Zo3o5n7M5FMU1m8XH0DJOL/CGPpkm2ITxYplTgaz6TL5uioTCCjs6O+MQIPTxN8InReHiajdIMfcI4jXYCp0yz"
    "tyx8quZEyUiJBzpKvCA3Qn4jFnHEpXumKNF1zjQMvB8KuDCsB2jJj6RAzXu2nW7ob4RbihWg1cgWCiVqzjWo/H4Ml8zZIJc8MH97"
    "bGtAk56ZoLmmMac34axABconkV1EdzXhvUw5hIoXIzG9MJJNjBKqONqiBUTXVYVb5mU7eVZgCebFfDFH189ykYoSBKjz1iCzGQqW"
    "YcKDV7sZxklPiTbYzjMmdz556LQK1p8PHJyvfSc8hDqlE9O6CTUvKghCv/Ejr8kVfq+tMGs1eZvN3HZtjo3ORcc4nKcgzpywDT8P"
    "XDGFszJ1w/qrqyDRubhxrFixeMAfcNs9Ch4ngXc/YDOxSNoHtDrJLXIZRq/Rqbf/HaxVtYgESRLrQTyL6UePHEKE1aIHGeh0D4IJ"
    "q6W10w+CQ1rP5G6U9uaTHAZ8J8knZ0WZTneEDCxETHrSBiY9U8cLLzRdofZWpUIWprXT3lKC+NZ5q1Kd1QAkMmcq3HjVhDr740ke"
    "+Ekgi0illGwYqFzbTHzn0eng2ZfMw3eaJbPijQhafqTT0wM5innPcpw4NvcN7bZXlduZDXZjxBje+C/n+5JIMmewA4/ilNkVHofa"
    "BrbCXxh7UTcuwKLNFG8lCOavQpVY0TF8hUulg1GBTPVV0nCqyWH0HSOmp9HnP02i5uN3MWs9fdWFF2XkjWe8na3BFV+JapUGJXc8"
    "8ONZpiACekSAWlsWR5fKggwNnMR6ayD6rjWrCGZmnBxHdiyg5lK0oyOCDXOi7Zk1qj6KuaUl7hnYP2TIewysgGDzBnjH3B3HuzF3"
    "ITIgE1ZMjHFKOe4NAeEn7Ad8vBHMExhP6TUf/SZnpW0mXknTpdULRcurTqCO9cQ6Tfm6cZI0/4rAntpvrjG1PKBSywxbNTbN6OrJ"
    "4kCrhtqAEFY5YxgYuAt9QlAwBf+dGWzxQeOcqQzQiQeIwFBw9UrSsxQuEZqczn6mC6V6afOjDWJC3rbDQHCIj418GEGJ7j3QDNYA"
    "JuWLOYvC0ljdMe0pYGOL/CeKVDBQDdtyolqZs2/aIdPEN4SscXjDpgZrJJsPHfo5yxYJdkrwWg4vxZEs7EvBb233MRSFttJslaGB"
    "WtsC+zbUFGOVlZG/OdiU1SSL5QzVilYav7ENAqIWona0aGuw1nzx/KtL9e9a68u3sA0hdMMSbFh7HjvxAMN6rLsEfb1avQjFujMW"
    "o6f53iChclUavAYwUYt43HLPZnfXZv6oXsUOGX5bSU97WpdR4pgB/Pp07F6/lW7RS1z3otVrm9loM0JKdx2GeXrCL5LmDfmx9o1S"
    "EcLhZy07r9qynQuyTdSDhjVmbVjfhXZezPEOorUiumxemW5vlutehV339KurmJQOMDQspG/TLDS3gmx7Gq/CDTtDyORWEGoDmIke"
    "IkHbDD2suaoeBUK007CYpGrWkmp1Xln3dc2zwVP9qfF8NJw9gqZF07ZOuEK6bZFYDVt7hViYB7A8UBUV+wUiDZWyBaGtiOjnIN6I"
    "t5Etc1X2MLkNS+ajDnFWw0nSzJxpOWDqN8UIGDgUGI7AAglx5Ie70er1on1vrJbvu3Lga68V+r5tpRhNWrVOfg4oeIFlWtB96iQI"
    "mVppxjh3OM66XPe1QbveXd/y3hmbl4W9ZXQkN4qOPuIe08brG+rdRxzQ2gystW61sTDW7Z+bqZxq5PVoHH7fSuH0JnVbt7adyhrr"
    "lhDwrPOIpUXOnJuYN78PTUj09ACp29Hs+FjrhdF3lBnTmcz8n/GXEvrS4zMW0zfW5bx0GWfF8FP6XMIAvmShJ3+T+FdMqidi4XZH"
    "wOLOdRKEikLjYmRugnGRcbrxSQOIic6M6joD66wEBvFB+t904EbRRVY4e1BdFRay9LRGdMS6GUak7gAjUt8ajAhGTHacmA23TeGU"
    "a3vDiYHb1EduaSG/GwvjuuZOmr0Yr6aDoRgLont/NutgIwZUSOYWMUkMWyPqweDDu0h0ZfDwULcIetCkyZZb0NBO46Fwqd39c7nw"
    "TmCEyw9oxKB2m1x/9mWqYXTVnJLigH52vpRblAPFIMhd6sRenj5AS5t3vn5EN+dSIaT4akrlUGhCEPylCwV4FikH0C/AktZiRkMQ"
    "IIbRczkS6H32cbT8TdLYB4zG/qzC+2r6k25BfhWVtQKO3x7yoBdq8OOjDkdwCiKgsoRXaEDXg2mhQNgt71tBCzke8A0CsunRs9vQ"
    "2LTA2jzbEQME5LnFCXd8C+Bsf8R4ttkEDK+m5RUmUThaw0/PQtixn79EPuGPKMr/SVGUEUieS9exKfyQao2oDJfQM+0skwtUTdvS"
    "E11ZNyJYFYL5mEUYctrlBF7uEDi5rR0yNHNDYGZvyOWPKfDYCaVjclGD3w6i/UPdGmtwbgTYedLNoPzJl2RQ/sQ0KP/pSzYo/+XT"
    "GJT/1MWg/C+3a1D+02cxKP+La1D+t1s0KP+bZlD+b69B+ZMVBuX/VgblT27doPzJ5zco/6sWYKcxlvM/m27ZNsEVluMm0VUIHGZY"
    "YBHAA0ewp98H0K23WpywYxFDova0WwC8tKILsyAhKpBxfaYZs4gQ080noAw33Xx4LyOgJL+sES5aO9GvFS7afMOEJBmaMk5TxrNd"
    "wKUkm8MhqLQ01oU+71l3Q12yQZdBJa+wzaa1AKBKHGXdnTEqqBV/uknYYcdekVIETTIgA7K0mg10CaJNU2iZgQiNROLhNR6LIDPe"
    "ZcV0B+YrnE3cnPBW3JrpgqxQ/a35M1wh4SsTl36Nbvlh6tcogC1MP3b9GsWwiEBeQPs1SmGqOx/I/RqFMD2KB/h+jTJQ0taAhb9O"
    "S6ZTrSAPQv4aZTHBkVacC52/7kBrhVVKL2MKbHIDG9gVorjONB7xiUfrBaSGk1ZBcPqrCI4DO7iUhdBaGdi2t81lWDCECtrfRw7k"
    "W7lPVdSApvziBmZE42iiAcpW0gnL4X5i6tPt4BxuflOPaYXoaKRKMouoQ0br8NQg3kFeJ2KHd4CsTPSdEb7D/Mp8SdpYC/fVNuj1"
    "zLwjuWXr50chvpUlfbOqJFfiWwugQ95GGJEBt/ttPUEtObFdDCMYjuVpe0lCwMwKo9n3G+h4ijGgyq97nLNzktBYpP+ZacHndXjw"
    "apJ9BhM+MwOPv5PfqqfRGqzXQFQF+TPIoEPzGl22JO2w3WYMLBXb0MY2xrAwbEyMDQevx8LFECeAmDCYq5igYWHCe2j8Zaj4o78a"
    "Ae5+llqXfzKtyz9szfZ6+hZqilhh4lFDFBNJ0zJ5w8RvRhLaSZgpM66gl0nFXD0xoCZZzudT9nQJM3UDuh/qLw6+CBverNy5rhal"
    "Ksq6WUMTV/AEc6/KfwX5H2sBtI46lL9u/oMSFmLbuNDdCFvyY1onLUGkbk53xiZ8f3XYrxuPaPRQX0a+ppVpgePVbZn8oTS7DaUZ"
    "yatQmnKryjHaO4kEfzHYOv6GiRYEEp0/BxUjDHSyinXwFaXBhVuSpIGCztOWXoQEehDUAq+oITgxvF8RnLjuYUnEq/6lzKaolakG"
    "QZCvKDgf5SsKZoevLDO8usL4Fp3VimWzWrHsoFYsb9P8yI/QLVlM/eh2bZA8SiruPecEyOCxMHBpMUs7RFgWKXpAEj2dhSUhfMjJ"
    "osQJY0CevRwyIO+BmQ6fxHfvPlsEVp5IRgznq1aINEOJtXvtTnpiXSgnY6frnso07qfzqO4D50NKx1WFa3zUWoWjp3KXshlDtlbR"
    "Lv51Q9mctVujcIsQe8tF/rBzkQxDtNNIG7wmJ/Y/6nwHobl3gd/UPyIgf/rSpySrmQUtBkPxSSqBbDdkkFwWCpepqQ+S6ZuU2cB5"
    "m9jzdicIjaZrTCUnQVoKNMJIkpwhbOkfdvrjdJBu9xFqUFaTNuKbCi7UEHwbVM8+pUR7/L2A+rFm/ezqUjXndsfyBe9PYCaInvun"
    "aGVWbbJCccpqY6S4mz9sQn6vNiHYsmwkmmRF4vDELIEZydhQJ6NfVF/CYSYFuUfJMbTbeG5r8Mhuqz9btLpAmpxVxVEmgiUsclMj"
    "uNLI2bqkp6Yd80S4ra1jQxPqoTjYJh93MaBxGeOzrvY1sp2OTY0Tdq9Lg7j8ualB0i5m1GQZM+xgyiMikVgGOVF6zO7Zr+hu4XQF"
    "Y8IQyzwUhMRDI0Pe5VuhktCeVBFlJh7YHSKN2PA1UZ4gwuqj9cDL4bAgYra5K8bbOLKP8uMe3bCF1v2SX5BSTVhRL5fy+sXm30Yf"
    "1paJHHvsV4+VFuX8J5WnYgYBnc1/2B0v9gf4697ueLJPt+5Bsb+M0Ngam7nqaFDH5nXbweqOp2k1AVKA5gYD3rI4UUlxXuRpvNRs"
    "RC37LeJKBg9fR50MuSLs2/1ZDX1lP0l+8NMckxZ6ErHlk33d8Otf3Qy//vUlGX79yzT8+vuXbPh159MYfv29i+FXen6rhl9//yyG"
    "X6KTmuFXfX57hl9QlzT8wgCzruHXv1YYftFXzPDrX7du+PWvz2/4VZ6PjhQ4KOlQqnmCOhloAf9F3jpI7eNGkYp8IUV9zht2cqhn"
    "oR2xspnWZ1q5Un7tsUzLzpuQTPEoUeZojpnapMVMbcO0I6ukqYDO40mrMZNFVUBcScMZK7G5OA4fy8Vt3SI+DdbXYnLCiE+O9V5M"
    "mYD9wNrQvExwAI2O+CYAngar14Knp+D//txcFhcEstL4Qxd8vt3mIi1gvlZEPi58omvOCkxBKVxjxcrHlmJRDLYCTFBI1VShB9Lp"
    "21smib+w0K/bCyV5miqVHhuLLeZY4jdtJRZzUVgx92Mbwll65+NNHy3CsdW4P6KtBoqyNchdhcKWQWSwVEcnseWjO1vSSonljtYy"
    "0dTaaFMn1kpb57YkfGO79XfvbvrLl6asjBB7kdnYd0xkWZKVjL6RWvaRJuVkU68ldEK3tGrW8E9WQpZMdMtahqzpgS3x5qIR7GDx"
    "xtaf7gXrz6E8YE2rF91QlZ83JsyTex9vmrC+Z8IOs5qhnHn7zN8yZD9fRQTw19gc7ZQxGySBgvaciul8t6GuO4wzfocmhWg3695t"
    "CWWJ34QTdZUU10h1NbZfUqoxbpjKcIi9bc8YRLFYhDBtkuGQ5ekOyy5stiVftSyqv3ZQ4TAj5y9Cry+3loEHeaIsSugO5ZMmNK4u"
    "gC2M9SXH8TnmyHMxBLmW5ddmGI5zZtglbBq4rtI0+psWi3HDod0n2HNtylsgKdbYvkIuSDarH2tlrvmZawbnzQ3tbI1uDK+EsvP0"
    "arWd+oRNxref3E6dmviHofofhup/GKr/Yaj+h6H6H4bqfxiq/2Go/vs3VGfW6uV5uPyHtFHPzkk6m5wLG3WyRH/CJWl/GKnflJE6"
    "+eU2mwJPDLNiT4ZPDfWzhh38zZl8f9GW8Z/Dnn1NQ/Wyqv093f1UZuywJ95mUw9gyuUdlL9zyMLX7OKCqyy6I7aG8UqIBBsN4/Uy"
    "Bhhh/pc3Aqr5JcJwwW3OLMrKxFJjggQ8SU9h3H/KSRHumMPrNTFM2YCbuVg1iJerzOGjWjeIT+mwlsIRIgJ+W3jDEt76AF9As27A"
    "JJ4Nj1C1VJOymM1Iy3gzFumyvDaDceqTaTXO6GvuMR3XM+fN9uPGOKWQ0x11GqZWW3LKZxhVstpdE3Mt3bIzN99IY3NoC6wwY+aZ"
    "7pgpR/ncpzft+5D75wE2KwxpjeMPPy2TffXSa6+P3UDeP4WX0lqfJ3otOsTwpWq8Uu8AeTxFPuMYSc+FerVzQ93BucEYr4ftjjSd"
    "h2wl0lbaDWor9QBspVEniK00WhNky25SY41N2Fdk6sDRr7DGJ+qoaNjeOpEf47wE9o6NnC0sxDKhVoc4bHxWTZ4jg1WVRqlWmG7a"
    "CUuF1PLiRt4Q3FyFsNbpdbqCXqejdAW9Tg163QQkButk8A+0PbNBRwc/G0BixXkne7Li/AuyJ6M+K4Oa6vwLtiebnH8SezIYs9X2"
    "ZLPbtSfT23R79mQz155scYv2ZAvNnmzqtScrztvtyabKnow2xq3ak0GNn9ue7PRcAYkpyqrbas19tlqWgRYz3+fGWQ7Qs2ugBe8c"
    "GwOWGnLkL6DzWhozuYIxoWs5Kl71Y28M2xz+u1yilx/yOLwCioqoH1am1Qu/10iLmMGqrzWrGDlSW4OgaDy04EQrRsWKE63QTjRh"
    "oDLZqZiCGKM2U3OWmh0F67QW103EEnrOAuAo3gLGW1IAmD47sltdSpuHTI1xbEWGskdXsiXSiohuCVABG0mopynunM2UwPJvayDv"
    "mSG+L4VI7m/pB0erWkbKGSFbRkeb9tubwa5T1YTyqC4lv7Sp9pwd1E5w5CSXx58yem4H6b4u7xSyfUwzDPG+61iOJiily74mwzO6"
    "7hGE5a5zoBKr5dJnQxOF5copRBN45ZrhiCnhyk1fDUf851o8MLGfDpBn+DHBwPzpWkh5TepMIWOzjAk+m7Lz+xvQdvb/vK6606M4"
    "29u9Mc3ZXv+mVGd7ezemO9v7+maUZ3vfrK0962g/I0xgtE2sPckty+2syAIp0vyyTPMrYx+iusHcd5BCO07qJSr5i+8I9YY2gXxU"
    "a14maSu81YKHwhsZMffEwyBwD7Zd42DzHWGek0qctNV/+OnUfAAxMVLmHES7N3QOXe8YEkXpRuB7HYvS9Hx2Udzw++s1SmLqQbsg"
    "Ye39zRolcbWiWRRZeH/buRTURN7EMe1R1vjMnl3VnMeEW3TmpdKMdrMtcPWp2LXfPQfxJTEQTA+Hb+Bfl524CW7iJpiJ/s0xE/0b"
    "Yyb6N8dM9G+Imeh/cmZCuJutZipcakKJJvH4vTMftC/WZEK8lsXKcNvkSvb+4Eqk8bSHK1mXXJtw3r8bG9S9b2/CCPW7m7iW/enm"
    "rmXf39i17M83Rkm/3r0ZSvp1f21K6mEVvt67Fq9wTZrcnSx+yjuYBVB7eh4uk3Nh8jdnJn8XKGxO388TSJzqMuazbnq4sy9JD3dm"
    "6uHeKEVEygTEXB1wuWTKB5S/j16fS+XBasVcslIxh5qxcrQ7LO8lQhtWbm+H+Sg5Ko+jmiFQHpwGOfooIaDK5ZJU+ljM0+qR1N0I"
    "tUaOh0R2lB+PUvgjFUaZ6ubrVd0cwQ+hsCs3UI0UQl6o9yyptE6IGkuOjCWbigoVaGqI+ucsX6TDHLoCzSmPPfrBt1+y8vPDp1F+"
    "vu2i/Dy5XeXn28+i/DxxlZ/vb1H5+V5Tfr7yKj/PVig/X6nNeHbrys+zz6v8lIPw8Nywf3yEA3F1dchSr67uix/vzgPtK3y6dFr6"
    "NIdWQJ+TusYzeKMuNqYpOyMWZbqRF/kOnUswqxvCBqz3X0/zDbozYfYTeMFzRJQ/QTvfDTZIFev8WQLdTTaOrJPuOAg3mJknjoJs"
    "6aFB4zjRHRPalGc6U6fUq6v0CKZAPMOxDZOXbzLazaYWFcMR6oSPjqMJIm7NRptAbcoPuLKSEeH3srmH3YlAelENq2M3RNo03Awm"
    "IyCQCcuB+3da5CkeJBURuaDs0dSGkSBa8C0sIawoHC4nyGziRphhxdkINghihs4+XPL6Nyfot8YjWVGroehiJJLgJsJJR4FLtgj5"
    "QpTFQBGzkM10thRUoFqqAaYVg9nIJLuXVfQv9tUlGfvGZFx//Ddzb42ElYwrNkQ0tvAyJwi0PByyHYjjo9lrCRPCywquXLnHDq38"
    "YZTyMR9f4qwgKRrwX33uIw1H6/Y2hnS04QJxxIDPOR3AsHXZKayHt7tLiE2KClw6Fa5ZOSDaYGirdxl50N9yWtIKZBXtAXCIgFZb"
    "Y1JhPcmIBkW36YaFWuD1mRUgbAfUCtXXYsXXYoLWb3JdHZxrfOuPjIT9yv65z/45N8jXeVfyVc1LuN5/Hsp1X+MVGZfHmWdF2MUW"
    "e875YsFCwlHESL6YuV4FN7Y0+D4C1lBMVI4nBNv8Nj/PzjU9pYe+SsB44Tc/JnMUdxDgdVrHY7YNT8viAmoaUPp9wTZBxq/+dzAe"
    "/JRdPQ3zGn59f9X/7urrvRB+PpwlF/N0GrIS7nzVq+G0ABo45v0RZrNqTH49N8einXZs8qVkUZBNnfHeMFqvavpxFVl7bl5geJMv"
    "8eBltdY/COpBCN6SloSSwWc4sKxgmL38Xj3MgSEtxQ1CzFRJG/WF9BjzuIZN96MsP0uBZ7pf12WF9Im5ijE4Bn7R5uECBiTgEw/o"
    "BtKbJ+qtFEjqCSSVFAkm/DO+5vw9CsiYdIB+TU9m7EEUJJAf6C17op9w1WYPPCM3nyWHP+Mb/gLxAIwPd2Cda4XSo/opum9oXxD/"
    "VaXQRqYSxG/eFHFhJ28T1oTZLJlXKT2wt568JCakD0gqaHzFUsxPhWck2b5jC8k1kj1ViJY0SaEf6TRD+Nqs1h7RBHiW1nqOCdKn"
    "mWwVJAEtkB1QhcgnqkE+mZ/DHT6ZvUwnMCqV7uvY5lpkuRAJwe0dzYLLesnS2tyLmNaGY9Ki4mb6Wnkw4S9IUCozE4yVv+K4pgbo"
    "KrzC/frKfG0kQRZTv+YCqo7hCHJTwwGwhNPXUi6sFHTkqfVa7oe/waVbJLLx4Co+lqRmUM/IU5lXHAzcayH5ZYbxMziEmSy1CjQk"
    "3yqUdTS6YEXmrHiz/YXZIqJ5PAz+YbGYnKVTpDuweM4KlOMzMHkGGofbz0yaFhM6InQ16rOsAnIm++3J8SifmplmSVWzV09IbvYP"
    "XiElsS8lEAi+0GCg8EoE7dWBoX4s3rJOQOJLRgfQf/mXbFqfye+1F09SRBznzS2TN2/SKY9t4yYZzeBvrCGBa/LcToTBRd37G2yt"
    "1gNqUsXQjimZLsuUqiXqeV8ymkLdI4yV4iWJJx8mMHMs+zu8TQwu2U5z0K/5FkQGrjQ8N1QGTMf3ah96MimI5FT3AG3ISS8xp7lL"
    "PbmNDPiFuWk9XxgZqDViQw4us4sL2GA4ksC1wvExnXlrhYGEPWlG49F3dUDY4BoJ/piSHxl0gBUtnVmnaTpvL1EQiJFLIKgondI/"
    "I16lEQLddzYwGPSmeEgZW6yni1kgI5rwY45eCB9OF25Oz/pQW9CBQLfH0RU42agC45/IEdzk3TfJaNvIymL5pIWrfFIXOQJoGpQK"
    "w3ZU0jMV5SDFB/KP4oRAOa1OTHfVyHMwKlfWpiBR5viyMw5OdWNsb2Wg1ve1LfIXiQW3z+R6FHeEL1bo/iN14CELrEaK0yXOFxi0"
    "iDiDoQaZPoEbXZ0+S3778KxIpjRLKKfOiQV+iJMLH8nfEUvnSZFnC3Blud6S0JcP2xHrbTNzYfHKXfYO3qkPgXMO9GkWeXWWHopE"
    "ncQkrap0iqMSLjVTK+EHaAdNUsNL2OhGqBm4kghOeegBXi8jB3o9G+W9mgUxSkYN+R8bKPlezThFlECyVOE1UITEkM4Aoy32FTva"
    "SwyLwe9iw+DZIsiaAyjBct/cvbrSM8lSGf4cy1kTjmGHjBzujYM8tn4gwf5YLjOsxnW+WbcEd0TtAVJhRoACdJgAdoqckK6Uf5VP"
    "A7EE0Ckg2F+IzekLRRM4jMBolIw5mb8o3mLb8FQW5EnxAf/XTl/EVeA4B/LAN0plLADji+y66PI/cEoe7fQHbhHeqtwyE++W1yx7"
    "7C8a83PrH7sh6nBMaySWgQiz0xBlCKYD6DBSdZSkTepyRj8DL+PjS3QUdrqvswjYlCzFEZxMpxKOkjoY+IfEMmry1RyaHzIk70bS"
    "nYc3QjJDHuviFS3RpqNIksOW06hTfCm1DkxfZHNeji5PfXfZwnOL5XTVXqnLSC9CW396IdoyWx5ru5avJjwduYYYRV5wPOB18Mdk"
    "HmWj/XNUgyak7ECpVtYDjme4GSSjrAfjz5QZQ4FwnjBVxrDswSoOiiibwR9nZ8BUSK1G1ktJyiYEwL3TgEmtq9H7mZI5M0tYba0q"
    "reTGj7OgZE7d0HT6gYes3umoomfj+oDWHTk3y+XjcGOLQmxCRywgJtHaiUxs2LyYrPxHu8dsg4ZGqBg313CzqSEtbRzlzNIPyt+U"
    "9Tu5WAZVjLWumz47RpEzTH4gpCkOaeBhANhSlPLRlumvmURGLi98Ge3i9Jb8gui7q+ogFhkpbX1DmIuBhp0AuepVuRJj0aLVTDZu"
    "mfGd/g884pLTBWjedj8c7A5wdUdZY8W0y6Mk8t2QEZjYptoNa9xzOHSL+LcMh/UPo922s91sc83b3HbQe1uEcslJCnPQl2e7XfKI"
    "08LUJH6NDVh6czCtrLcom/iG3nkZNS1uQq24P0F1Pr+We6aD21XA0VeShUjYu0jmgZuP9Pp7qLFBrxYg2uiVgrSq7ClbwErw70Zi"
    "69FPFHyT6TiWnGVny/WHXX6YHeXRh/PgAznNImD5EjFLFBxltgyPlyLOVWkUqAooj5dhWzukecVS7ic+MqjJecRHR7kgtBBvIdnw"
    "0++hGW3LmB5LrFrCJfLNrDhJZmTzxD6h58cKCrkybkCVM3tyD/lAVtQlynnN42Qq5VKG5gjJaHeY3BOap2EizJ2kyhcNFvrymxla"
    "nOWhMv2SJnxe+7M8mgGzP0NDaNbPOLxEuwQas8VoFgGzfbSgVTftCQtb1oBTZB2mxlKM5pKNOOVsxHx06rARF6M5ZyMQQoCNcvo+"
    "nSyAMywmYqyDRZQeJcfRRRipqoGivD7tHby8e7e4urKT7z/fh4tMEZ4Ak3musSCnJgtySiwIW78ra5/SBpGFYoPRGkMsks3q7t0y"
    "FIN/BnN1dq8Uc3Um5urNqDw6o0GsRq9OxXI7EsUoxMqrqzenvYcHzw/vP33+6jjAcwsb8QYPbJ6XBk4PNEiNRuMS3kSs8DXfWsPX"
    "I/HheDKewKjdvVsNqgH+il7fvZsxUoiVhEtJBgTZZgZJLO3qSjcuzEOZdZcsJkecw3zbLKGRu/wtb3g6JUz6UWZcFti7OHpr3iFM"
    "7j+D8xplss60NTAAOR82FHOYg/3q8P7Lw1evf3l6+AS2GrEAMJaFPk2Z1OIWQRKVnrGnGL6IWOoX0tjSmXz0QgTbLNPTqndSTD+8"
    "TE/5eWqksdCidSnv/SSYppt/WbwT1/4jEfxntLVLsUbJwGYa1PJCL+Pv8eGUSl4U+fILg47pLwYuJclilI104dh2yoxVJd/MAxkA"
    "h/1KL4SkmL3qLDutlRjc1C1xRb4SNhhqJrE0WNNe4ivUsssorPzem0nTcYRjAMIo9IlcpcVr5rdp2UTZfLNJolK7JQUbk2pUq3t5"
    "Le7lWBbw3JUaaGgUXUStEQl9QgORJSYNidbBiQjgyXm1p7ksDrs6G5kz5x63mqy23hxNkJlrrX8WLu1lIvTzTjzrmil6ldML0y2S"
    "R1DIQuV+3GCUoRlMs3GZsZlZjIScW5ZxdXV0PFzAMardShZhdFQe+6U3qu6FOxDXGoalGQ5Ub7cetjQZBx0WRnQzcxMOglUDH91E"
    "563pczqvBUTF7cNmcdq+5E/XXPLTlUv+9KaGVUWHnluNHB8512L5jq3GAfxZ0c75zUwKWt2JGVEkEvnInDsisDODYPTQEik7gSM2"
    "8AupoYC6eAMrmAXD4bJ8xuMBbVyUKOc+5OVJqfSq4yxGXQ6kMsob7/Tj6AKYjAstbTfmUZ+BQO+fzDqevEP9TORcvDacwtaJ1KCs"
    "7JdoHOCWzvl/aeEk5OVWfbyq3mkxWShdpznDPjspaACdu+6Ma8ZTWitpEh/lrkZRn+BdnpkHxbMUety42qNH4gwAP/OBSfLJpYfe"
    "TS5uKkKxMKzeZciTox8ovp0kVRrfL9E+AhEU2B28yGUKFAw3lAKlI+GQuNuh+uSnufnBT/Om7E+Ki1TmxYemjDCEMh/8bs6GHOqA"
    "fj9fXMyBw2Up8lN4Yh+je6v+6at5MlFtoSeZ0arlMDmRGeE3yyZLExjRaMpOo4nbEfLcj+/eTfgxuOK85EYEuiFJQAZl1SqSWYVL"
    "o9KHWCmuhnmZ4rrZZ40L+B7V59Ni0KNSyC8k1X8O6/uVpAuwYAPmbpHxXtFmQm77jPGDeBlIJZcZ6oyh0bWSdQ34w3y7/8NIiOjG"
    "SlY3gBdDPuKCnQ8s2poy2pocFcecvBZI+d2eR/qyXN3rF/D9J+71Tv/eaHe8O4AfN9lLvqFWd/Ex3h3MPnboIicwaN7cubcrlm/C"
    "bal3SQTb1C9GAFZ361ny++pVHokV3dI1RqCc23K3ZVFHAsMZu+KrQBA2z+iJg0Ijk6xybTnbbLyQLepD713liXsOKdEmP4ymMysH"
    "ClczjNjrvvEWtdPH/EM4CO+NinEFW4PY3MT9HrOxa1wClDIfA7nmk/RjUp/1LrI8SLDn7Cl5T0+wJFfM9CQkssoOBe85voZwoRw9"
    "X8Ca6cKUoaRVkn08nu7eLeE/a4QzlG54CgQeRBYFXMSLTrW6ko1xkBl8YASnXQILBPZbkJhcI150StSlmfkhM6ZCy4/qY5TzosbA"
    "+pCs8jxnkZfHRLU1N+Z4lZ3M4EonBEb1+NkiqJVZi9FHbtUylhbR/rNPRozwHBLe5uCGzIpFdTNN8h1MWpNcou5xwzLFXZSxy4Jj"
    "NTj01XVgen698sWQpOP0KFWbW/TOINzWNkut+0ltrrGnC1JcsLsRlPFLVp+9TKZZ4Z0wbObQlmTV4Q2LBGze3iDlgrvnN0VsKrMO"
    "6iIuqDvfTK/fBmswBWJF83hqoic1pAZ99IoYarSOWE/EkK8UMZSfZpoEBoche8hs2YMrcRgcHQ8zUygG5x96uq8QimWfYqL1Xmiz"
    "XDVOs3nE35/NBHtg2BzZnkN4XVaCVZ9QHgMGUOhWWAEwQvlYaABZdGxSVngkOdrbMBKJpnES12cbiQ0jiS1uFOgsRUmeheT/cLlq"
    "SkscdK94timsQ5MME4vx3jc7FyTlgdQiAZ3UgGtiLnLdCFpYFxiuOd7EI80whH0bHku19GCzPzBrkX6jxSnzORw305E0/GGHf5/+"
    "e5EgkkZkb0MWUMr9uDHShbLZcArTSvJyhHDnw32DChl+OZDAGgw/pdbxU8QWU01HISV6EpdDrl2VcB2Rx2XCu1+twR9dLiPHM5Nv"
    "zn0yU8ulNrnm2mSg3I42WWr3ht4pZl60qEotzZkOj0d9TUlcm0riWlMSryg39ZQb+Uzt7VFJ8fonZsNrtz/ioDIfOSJmoTc4JFZr"
    "GePEFo3fYYALTi/QAlquGLKDi9ln8RhJQT1IaFzN5gnnnpcWQyajeQ1dxd0PHg3fWITdMpMjzhcY33OCa6TdayvTyCmKNPOGg9bM"
    "Zv1sCGbJb+JWPE+QwDMX73rHUMxGufmsTEn4SWaeQNy+pB4m90a5bllSHiXAITDbgKL7mc9OqcJUN6ziKNBkKifchIevfm68zMKR"
    "HP+//+f/iYc1C4rmdoY2kyz5IJ8BdR652sCBfWaTY3fd5VwXh6/+QjfWQcdJMtYxrINcux39NQ607U5RRAgxJh004EDa7Btx0EQu"
    "bjKE9hfjcpuXW8FtDXYXBVjO0EYI3sRb8XbQWA0PXOpx7ChEtPqGlwIPcRsqgJnGw8WBLsIjDFrwX/FQATnBSGUwUtm93B6mTAwT"
    "qhnEGGUMsUWvPPGOkZ1FtO+yxvHJzcGphZlTwexDmz4eFqOCY87EMQI2Ur0iHObYTggu+S445bi/3lKXIY9rCfurV6bzWTJJg6+2"
    "vnoTxVtbGC+ETVqBI7tcLtUy4xZfu8OJd5lNxPjNzGU2OR5OgK7uoriDZsMN8DXrtOxkLhaYmFZf5V99Vdvqc8pxFxhkOW19aaw+"
    "CbQQsXJdavLXmYgQJ+kNveCOdaw1GQwk4mRQdFfmqOGJXsm81Xa7OpMtLazpV4Q17V5d/y3kGOkMDaxO66HypzQ9oUep0C2avkTa"
    "MAkHaZwFO5l5SeNS4qeL5YHNneX+sVNviwbxIC/PoFXsoyZvSbuz3fvpaaAcYsSCcNXR8vZDwh3UjMYo+FlgALtNfv3/iWNA3r17"
    "oqqNLrcWVVryo2xrEOfAPsXytkRypFIbkR6V0TsjZ/GRbFNxelphRBhM3Y7n7+MV39fFfBTvrs6HY9I+B11q46Cyo/hkVkzOY3ti"
    "LIUx2oz5pyFc4R+rrtXpqNSmduxfXDtNrWajib0brM6y4y88EpyVu2fQoOFBscinsCkezrIU0VcndRD23qEvMnBfsJWq9GleB40l"
    "sHG9yJj78tVV/9uov0sSo20yZi3vccCqHdSd56Fv47G77mlWx4Y+w1edK1hu78NOOix/6H97925Gf7VyCWsGY1lVhLhsWiX52seg"
    "TWJDKaWJV/lE0DBsp2wxFiN9pyNjlfIBo8aNUmv4Rkm4lGI6t5lhVDhSXbGr32ZlDbeFV7QdCK8a304NvXY39cdEz8w4uweeT4w3"
    "+OGwCFCrGqAuRj8FHHwaYJNTDhvRNM/RNJ0By5CuJD9yQxO1ipzyNHdJpBYMJrgL0fRRy0BRHUw5ijWCGR+PYsFCrPKbb/dqX/Iw"
    "6trUey8Bvywad2XI5HV+JQDyr64XLCVvHW/8sFGX+OcsDv2cq/BOYmbS7bsvXK5GCmCG0eabIaMCcQzXB+Wxi1zIiKKpUVe2ju9w"
    "9AYhhGLX56JcQgc8PcSP0FooyXL0tN7gnzfsHGRtY60cVjvPXPHMW8cxVkZFN9QIWYalO5Slsp4tSBOaDuC2QD+3++N6UMI+jGkQ"
    "B9DQajl/v7GZXRAzmtfDjYvk/U7T2xjuDMDQbnj+785lQu3tuAYGOVBQioEW3Lkstvswna3FIhnxFIvJWrHTdYtFntdTLCa3F7tx"
    "6S2XlT1Zel+6qYoJyqpilijpaqUt2pGVA5kzER2QFjdtRThoBs6nvSyHBfnk8Mdno2wZ+UmHq+FTMBJtoEPSO7olj4Fqnlq8MsoQ"
    "TCaJ9HiiPPSRphaKwoKY4v9wNPZVVQsDwBWoSG290LLpQJhuP4LUuQb0I7tzUFoQdujfYh53anlIGPCr53TlSN29Owpko9gxZrVL"
    "vO0y7LqmdEUPbqRifURY3TacB0WasqwwwzbFFMPy4CegHZ/EvaXnnjAm8kovTWB7OTB7z5HSA8P39PmLnw5jdGnwvDx89I/D+y8f"
    "3WdwFiJL1AXgY2zZAfcINwubNUIFS/PLXWfUEESr6eq8atTMzTCuHbOlgeSFbdSw0U8GZ8EH9ilwAROUc/w0V2y+gys2etLtWwNm"
    "bJR7Eg3KS4YZdPFnI6OsmtEPHi2jyiSvTlNy0ycvyJhfjk/QuMUzrgdvvR6WzcMq1OTNTdF4+4YV6+sg2RRtehY0Y8FJmudMHmeh"
    "dLkCMFPwWKpW+CpDUyAFbYC37p2M/okq/rxd6ledr/aGrbOpXfMT/Aul4d+gcX3s9EPPTd4sFumEv2DZOEMCwcQGP1TjoEtbSdRQ"
    "mN3cIYO0SZrNGjfFV3trNfxGakFwvRdFlRGl6UuzlC79+1Q9+rg+wOxHXfpgCXI6ttAW/yx9+/4ZBQRc7TlxnY0cuBt1ve5q19zu"
    "vaWPPDTOwDBbCz8rb+iGr9dCpiPuq948QJvEe4d8KhCmqBhlGIRqyJyOg2Qng7O4L4dcW0gYMOTqimXYacjRDwk2fhPWnLyMNeBt"
    "mJ7pRuSt2qLK2stxy4eo023+ctDgDO/5SuhPhOBG6D88cBbq/k4WDOZU4GV9tmYRBCmzMGQN5J17IzKGRVcZw5B5yS2ovQ1GaTBw"
    "kyU6yy1WGa9RvrlpDHYq7eNnGMdtehxpiZDEzd3gsqBhOdK1rwqAoZndmzSswLt3Z9vb0eyHSdMahgw7O9GvM10uWUWTSHDvTMfy"
    "0iFDgamkNiGhHUV1TtitzFZmQpCt7PdMqqs/OX1qJiAGf9zCB2rIaCbvqKVro0umGdyKWCM3jkmKyfY/iVUMFaW+TU2l01DdFTbZ"
    "R0ynbqumwqG0uK1ZS1iTH3xwzdgt6xgNbn2YKzCMXGg7Swa27sc6tMhQG34hvpdxXKSJE1m1kFeE/94GV6JUXon8fpJqxZbFOwbv"
    "yu5SDXq8NYoZpy13qEHLy77wn1zzWsV8/4V/oUA2lro6CxcZLzMrryRaS9a4iJggBFpbTK5EYQ2MJCCEde+MMnZZQKYaLWKIhf4n"
    "HsDbf8X0r/bgQlA2WdYn94pxUPoVlFKAS6GU5wWG7zsp6rq4wJB1yazyqyr/KW2z5pM8iFvLkWIlE3saBh6uANU1mtWoQP1lFlTd"
    "W4XeF91rrzFEdGvVqwcEywip4mv2vHVC/hO63rAStvtRecMLYY3lGUa1xzNUbfnmO4i5SdHWsWEL5oSXecMTnq/XxRuuvV5n/6+7"
    "2D6yZrbatCk0bAlS5X2uTod+w+lgsCtz+02n48u62SmBj1GgHvBLYOKZjfnB99nYlzjwtnhE7rW+Vzv9KB/5fQOGv8qFZjVn2zDt"
    "rLeb8am1mCc+q0zJ7Ppq0fjfmgfEygUfbO7QQCAF6bOOiT4fUOnH0XbpFsFW4L5N0UMvzkNCGiDIAeXCI+x/L6W1XmYaBg8TAeOl"
    "Ar2MGXqdkx5ioI18jK7NyB9NUwy8soGPwo3TLUrMnFnO0TGWw65tWThIRi2Iu5u1sKXPELbB6zCklx5HSRhxxZs2ydwqA26iAxcZ"
    "gkWnIZcONfyEPd+Rn6JhJ7TM3ME8DQUGlBMgxzc67A05GnECIxIf8UwYIyrIRtkKhMDS78DiVOXzTTKj9rQ61QTc2Ln82NrEBDXX"
    "hb4t9mB4yRcrivs8sno5X+sONJ9U5Yygz9xQt7134xuJuLM1eqzwOw8SV2W30ejAg+9h/21yw38g0Bif2TKZ5Jgf6gueh8N/zBBC"
    "LR7wct9Ba4p3PUrk+RgaRgUUE+9BVkaeLLIKVAwWGI4FhXMq3o43smojL+qNZIOFiyOytwGXTLQV2KC8GxXLHG1UizmaGqQ8W7UB"
    "F7WNLWrh1gaM5cYWb8QWxn5bRtK4xa/F7qlRQqkFeniIGTcs+1kkBNO8n6FzjNwIBBr4Mn7LIqvZbzaN6M/oQSLBzz3Y5j0bQd1B"
    "MrfAT6nI1ajk/OOzpOIQnLyzWlgTCcfZFk0Eh9kIJVLL/K6QOhBiRKNDWlLoHhT0lZ7gHgzuV2Kfmp+y1Ab6acPvsakRT5YLQ6S9"
    "Ipcbn2+SCAjKsBrrUPoYMRHKX18dPO+x8IPZKQtbJ3CgX6M95SsY2SmtYGbCl9ZP6/QiMLa8DHNhfSFUl8ILUwY/iykIMRl7yXgx"
    "3TYISUTdFiAu7lf/9/Tym+UO/N3jfw/p70D724O/Xy//9VVUjvwyUL5ZVEhG9COgMIZ1OEac9H00VKvhxAWayGLCsiEkc1FgluG8"
    "JZepS8TV2syurs7QnxZFYSIycMpNCTy90MEMgRS4dIA1L+PkYBTnFAE4VsDc7EWmR07pEN4k8dCXMJK1EZ3xVEbp7HXHCCmJS7O0"
    "erT4EWr43eASWsa1ozQk7XRObwmjDp5uq5daxrXjPyStNNX0hcysMHRNQOxWvusGbIC2XYt041KX9HqkljxCy/Jk7p2tL9imEFaZ"
    "RfrtdUzvtJXM8ybm8aG9aThA1K7So6u5S9CJ0zYyv4CajQL8H2mLTEV4cyuzor+N9NxRon/qyx62nH72ytLPPTUt+gFp5JG9bD48"
    "aRkYJ6O1FvR31oJouwRZhUJLjAPZfm131D1rV1YqGXzfQZ14DnVvRhoP5ZxtDYaNawSNMj+gQ7zpI3zp7CmTKbByI+HpwDSs8NTU"
    "ISu1AkfGC/fw5wc+Xmg5c6xzbZ6b6adRr9adTbhTa0/3fi2yPIijuMWbg1/7iF/SNup71ySd2YKwwA2O9tSDMdlkL16jvXj+RdiL"
    "p555Uzhryiw8bTULT22z8Fo3C79zmV/bFLw0bbZFUdcx/24o6jom36XH5PvOZaYMutmvmzTnrtvNuWvJ3ft3uBJtuEekzv87b0XE"
    "YtiCw9Vb0Hc6SrKveTDprkm+b6KGL6T7kvcYjkoM1i6wzn0WEinTfaCrC8JDPM2zujFGpxkxWiC+ik8f8rDRHT4XEaadIihOdJcC"
    "KKOGOettuyZb1yJKKgmhFmWSZIOCKLtgt27gay/OlDM2vGWv/BolX0OgFSLyjIWxwgSiUGv/+m1jd1+jbZ4x/1ytM2dVi5zigJ6Z"
    "6FokLiabCTKVY3BOKLnntUbJSBO/G3Gu0awtQbRrxMgMNwsySsOEEXOc59+FzH++gmUCFKxglVVsveQKWFy5FYkc7fJkxOoSzvJj"
    "8c2oUmqA8njptnmULCNfbBnHp0FEZ1WMmV7KJcb19ITG8OD9OEocLXS6kAaq0OnsXh1ZodP1WHFW6HQ9dJonLrp174uMqOTyegVk"
    "DK6Cf9HC4zQJik/FdbFTTBr9k0iGpcEFymrxrE3rZpmqzPfn89mHj/fgX+s+aiO2WJFNmiOk4PLQ7sOe7Xe5HCoMLDeQlI8BZkI/"
    "EUyqHDG8U/inDwQY910mw+iML8WvgUqMjMhPRpSphshHbAujmmvJt3NGvpECFcm13/NLAiO6DJg2mnYHc5fDbzQzvbpK/dakynPT"
    "uAXXYrfq/LfT1KHFPAn3LYPBkj5FrEDBy8eUSdwsDL4Kt8eITKS+mlSwyKqpW2yExoQTOF8CzjrdmZfZRfp2kYbsgghtScmUOT/N"
    "3lhp1ZwnjDneGdr+QWlhFNzR/CiurmTbkUsOe8l8nubTh8SGOi0ibzLX/dXZgPo36HPl9p9JTAPpQKXj/frOJW7WZyjXBeSZIVQ1"
    "MCBxl0qdvaCro3xbJ6twB9ErfwjrL40zRtrGDhYxvSYIUY4CjRLDRTkhWCsmFiNB7ijHB5Sej9AJhS/iDKVVQHuH3O1eYjqXphrP"
    "qXF0yWoZ1PyoyCMse1BGrMABHGHJUplfwjX4Z/Nq9zI9baLfjAm2roJE/QnouaSp9qHWETMM5wSynwsE8+MRxRs2vBZIHaN8YhJD"
    "HZZYBk3+B4Y4SgoSgE3ZPw98AqtSAqnlHEgNQdNsIDWMqscCRyXK2UkzWgWSikDQiHtEtCfRA5/mJnpaTuhpPDqetLau0bQ6bWFa"
    "aqmfTcN7u0sMnykOABxWFV6+ae6sIPRyXGH6WGRx9bbB7daEblNljS0LdC0svE5mgUohLWMWrBxOChkhhu1zu9VzPCGsXkmxu3It"
    "TJumKygl8rXAemfp/IxcTFhkOvb5MjJIk9NZAVxC643iFgnLEcVNbAaC0Ft78WCORVXhJhcLpvQBXkMV4KPgSU3Nq65xRYgzFTxY"
    "YUD4AoDXKgoyww4N6hXhrLUvZFziOiTTObRXqZPZy3QC+7t6Rs31yQ2oU/oU6Z8NNTpingIK5pkPxWAX2JOLef2hgQz5Pt9MkX2Q"
    "AfKgBHmiHBbzpjVkqPKMBGGZj3pCbsgnjjA7y4hlOUMmWL58QN98XL1oxtelUrYcmimMvGf4wx/7A8XKzQMH02xGMYQdyFeDEDTi"
    "/rqgsvByqMkiPgmA71CdcXVoA9LaShcLrRV3Zfo2LT/4yZeCnq6Ki9TH7KbCnCyHq/IS/z8SJj+eSMCW2Y5vOxvxyQdN0Z3H7dGi"
    "OXI6I/KMyDwgBG+kxD46y4PM8gCvlxWOSQbbMq5QFj1Nyg9wXQIWeIBIcii1h8Wxubtc6jEYtRpYpNosn2V5SjcPurR/fLk9VmQY"
    "zYt5gf4JWHYynb5cANujlZ7lp4UqmMDP4uoCgZlRNIr8rP3FFK+yZdM3CV1eL81E3qdiUWObps5XjZ3gjafFUjJRVKfZoSHN6u7D"
    "SFqeNbIzKdQa0yTsbsweQLcatBWevv19ErQdpFdX7NxlqgwshN1AXniKejoLTs75f5fqg4FVQLR1Okvf76iELTuHICKUwPEDkGmB"
    "z2I+qzjT6lcYxbMiQVUWlyrwJ0in442n0u9Q8OHA3uJN/nL/8IWg+YODR9H+ISEwcbew5FwkIObV4M6+eGRwjYOLA0iwLhCDZ+8i"
    "Gepp8Pww4vGPBo8Po1dz0hMMXr1ZLodiCDceI6jx5db/nCQn6eyrM4K6qjZ2uE3OlqCwj89HXIP+6sPFSTEbGYZsxqteVouIwHFF"
    "KfHYx1Wzb9JlE7p4c3Wpxd2xPJC+KX4r8dZYtGEgK4yoz0s5BE/PdZQrndNM6erDU4Bt1+RkrJ5KODO15cFiagpmXTq3DHXkeEvY"
    "T2ElZnPoJjWxl+aLC3b5gmtIlNOVp0ckiu6nChFcdu4Zza9yHOwP63tJ+YakCRKytBZOfPlIvsNQ70w2cbkc6KnD+r/3xjBmrMFw"
    "IEabux6xF/Ts5TmLK4RhDZbhYEUPqzHPME3hVpHyDCRVi1Z9Cq0IB3qb/A3yVcBiH60a/Zxs57SLnxxg0UkxkcBk/0ZIxRmyu801"
    "XnJD/0jNKdJYJidayOd3QI35bxjCFGcFPlHV/3auBDAPsCnCpiVUWxdao+3FelBvx7Eq4cG59PekjbEpbR6AAqfK+ZTWB3GA+s68"
    "Fy/wZpGP0iO+9eriRZldZBjh/TiUUP4KFp0EzFjjkNVYajVKx88hMx8+hKqYCXH8P/+jFbxxsajqDZ452ZjLdBYvW2LRBkS9+YiM"
    "Gdzv4DmZloVIA7BNP5+Pjpi3DqP6FVfSV7FwAY2PoycyEzwp6vnTuYiqFWVRIrwjfg1iTmxjjGkFjxqhh6QJS9KIfYye8CoRCX6M"
    "fu4qSWD0RlOWaBF+Nd1PgzB6FsTT7G0c/YTsV1JV6IL6HnVOBeIMbvk6uwV55vAUxD3d3+hdibLGUn413xokJPl6sUSfk/oiE8WG"
    "0dGLIO3dqWZFXcHIMTNw+PBBcFhEl2idgFUwhyZkgmbJh52LpDrH282lsBo/D5zDHeMCsTN1HFidAyI9gC2jdVEUSG0Tj9A00TBZ"
    "lN5WeYADn8VWq/hnNxzwOh9HVFt/6ZaFgVdZ014GPwa+t2FkNPUwYI3lOZ5S4FZoNLlbfR8dxZQtPgaaJvv+VFYC/c9k7/u8yCNP"
    "iVE8z3YqWIgYy1R7cyyHx2wAq7//Xcg7/TIoRDV7EZYziGNjsI3PVxSq9+o4+u4b/EtVPQmgVDhBUMf4evD1kgYAVwvkjORgsvtM"
    "hwUgwNJlc0SCtT5FstWKKOnpMgUxrRWffabwy4RYmol5M+UcoMlCBknPlaig7CB9luXnr/C6wNCFxSOw2RfzGemNtTbwNKr4RVoi"
    "GDZnkCGbmxhxXz1MepmiIc6hKrXxnbUu5xNFraLLOZdGDEhWgXwHMPvoYFIf7R5fXY087FvSY1mQxEbJ7F3yoXp1VryDJqgHWUW0"
    "4I6P8Fr8FNQGvRy38BicYzwjmk+9cXiLyoLL14M9fVvKwZO2VGNGfmKZEEenuU5rJBtmrBG3IBgOrgXmtt4k4K9Jh8CVwcwwe04D"
    "RPNLvx/C1anmCfRbroSKp9JvcwXVxgpiqw2H9SGcoCfJ5Fy0Qk+jFlmZ7KQIfQWtPHZShMDHVh47CXvMNMFaJictYsGfrLLcxCWR"
    "ANxm8W68HHAK7M5qhTgJYkbpwZ7N9slkn6jK+m2VpflUVEVAwutUhB+oavbaqqFpxFUwg1VA5wmv1Hmx5sr1fH8pNjtMAv4KtYH/"
    "uq2RuER8bbTT12yi+3lbC79payEuUF8L7fQ1W+h+3tbCb9taiFvR10I7fc0Wup+3tfC7thb+uriAGw8Whl7J0+JdrrfT/3bN1jYV"
    "0tbmP7W1GUkucKlNjW54vWarG0tpa/b3stnAzfR3v94D5oZ56MTcxiXWaXxM9UmWAN/yIxp+uqc9JDae6fiOGK4oVocuPIgjFquq"
    "iceUvM9v/mtDzZS94giEKw3pmuHArXxvLy+S90xyBixQk+1yaojYgLFcHjfdMNwqgJV7EEyxmWV6OoitOmL8zi9TjC4zGE9kzczA"
    "RUIjnki8K9bF1C8IFNYalywWhZVtGRldayoj7u/u/ncs1vRUiEkbhyxCvlqTp8KccSk7opYv6oJYSvhdwTwzm4DBZl9jnOxhQoub"
    "S+Rs0Djk3KPhOPqND30sh5o/QgmpfDAuIDxyTcRt8B/iu2O1YCiRTBWivFcpwwW4kjw7D54xoyWWi2sT9CVAIB+47KCH7N5cCQZ9"
    "Im9YmjI76Tn6dTnVMrQRMjH0iuIkEk8tHyPNhxteaU8eVU/Sc9Ii11oCa3ASI9s/inKZSY6GLulZKVyfmjBhcyR0TLgC+U/NPDFr"
    "sE3MWgwTs0arxEzZ3ok09B/Fus3kfQbBJtP5c+SoSuTkOTosnvdpPl/ULKsoTCU5NzOBREkx1eHm0m+5ueiYlSwGe6phWRL+GBJ/"
    "KGWvYykSs4yXZBhRYmY9wbKbVK/pWbYDwT+IlYV2fN2xHRJmzOgRppJKrT76Zo2CECXMKWdGOEL10bdrFCSQTfSSijkU8l3nQhCy"
    "0ol6JEbnTyuL0UJCiXJ41Fs+R/XR942F+MPlUjm+my0nyLq0R5GnWBhLVuy8l5QIHjXqoz29Un63Lt44lWLREeIHDLoRS1VVLAgF"
    "/ykK1lxqY8uVNZYmuLG+8eUj3+DyWdvIMk3tW40tMjeFlkDboJ2RSQ1zA35EzKQMB08yI5pMzFF3jO8i9hvxczZ3PeeGTWI4Es4g"
    "FZg4kbQhGGj2BJHh8sforeEpaMTk1b8kCg6L4gltVjqp6GdEh/h7mJB8MSDdmHjS37zSGuNLvuY56IFIGaQ+4BQSFnCuUvzEtFec"
    "0xI/I2HAP0ilLX/khiulXtiJkab6TXW9r+YfinLJQdqzUiKBUaNlsZP0UiqziCpyPFDNDHwMNI+QQao7mURmGFdaFmaSFA/il/xy"
    "YmnfB+TobxkVRFn1c4NKHpY1ecTQfB4SGRto9IwxTJRDHJt/biGlIlsgPW32T2YTcd7utn8JWa2PXyK7LD/vt39Oma0CDovF5CzN"
    "pwOeh54f5VP2FoaUDnH+Eh7xfNYgRvW38vxWaGvicOnvreiYdeTyJH7e9r9e/bV2zvIUccj2v1n9tX648iQcE/j429UfM3AxHeQN"
    "vvtu1XfyMKZBp1UFn/3p/2Pv3bbbRpYFwff+CsnbWw1sQzRBUhRJFYtHJdtlly3ZZdlVLmvpCJQISZQpkEWCuhTFteap32fNrDWf"
    "0u89f9JfMnHLGwBSsqv2OT0ze18sAshLZGRmZERkXO4/QFW1bq8/1Adv+ICTFw9eqrXo9A6bD2vEOb0zDoLA7i1bxHZZb4GTIDQR"
    "PqAJVd4rdBSERioPaYRKe3lnQah/z6rLDMP254PKtfsr7ztrzoV94/7qFuiW75ZNE0n4KPKWw1Zybx/Eh0V8dWwikcOZrk5y2xrQ"
    "Pqvds1kfyPb5WnjWOoerfZwWHZz6tNRHpD4XC45A69TLnnG5A805wQrCklnnU8k9jEr6MMpagJWyJ0rJIcYlm/iWXGpbsia3aBr1"
    "3MG0RcohuUShXjXn9wOyecTgHbusXdfx1/BoCia+vviSEOGEZ7+A2XNF63+xfv9i/f7fwPplVH47rOzjCskSxnCxEvIr+cVK/VsZ"
    "xsrmn2IYK41/FsO4uE3hISmRx/zrOclK889wktXyn+Ekq+Gf4CSrlW/jJKvVb+Ikq7Vv5CSrG38BJ1mt/xWcZHXzT3OS1cZfwElW"
    "m3+Ok6yV/wQnWQv/FCdZq/wvzkkSz6b4SWIc/sVVfitXueQkKy08x/4zeNGgW3J9cj3nosvXJmwUpSgyBnb2jWtmtNyavnhV147R"
    "SXdw4j2eOR2U+ON8ZR1DGxGXK1be/0jQMv8SrwnnoxsfvVSKbwZVd7ZBoMVgT4OZe8mW8yIt4J8frvUmXS5Z5bFFYDhn60G6uXVK"
    "suM+/LXuV9FmV2bfbit4+cUx7WPPvYx1X+X/39Z94gHpGPjVqv90Cz/u9l9Gfv8y8vuXkd+/jPz+ZeT3LyO/fxn5/TON/DRimW0r"
    "dKmoOtyoROwwLhXqRcalQr3OulRYZoWkmeXM5C/J1dR1KLGDSuoEjobvlfyNLc7faPjXBdUM/xoUGV3pkQP3nOih1wKBMZt40oUU"
    "pul9voiG1HBV3eMJdIcztQj6BU0BcvM+RVBWIOurstMRLtC7u0j7/aJGPDsHD0fARjECqOH7UMC9/0VIkKE8EA1qpypEEApzPkYo"
    "CvzyxZ+/+1Ia00VA++MXcmz89UtbdjhgAwO8jibRPPgRvf7SfgpixmHwGorYmyMaTvtUMhJeFoTV+BEM9uQE9irU/t20iUXT8RRj"
    "XsCog5/sdn9bWOyTdjpMKWGprvLZrv+zwLWZg2sePP7S3gbW+YhJ5P5oOBzs0NgwEs5o0ppN8BWmYzoGKb01Q9fO1g/wKu4mGCoa"
    "KCWq4GaDOMUAX0HS/tXz/Pb3GBETSmEsO35xtANyLus9xvElsNEgLR9dk0gWfCoNhtc+Zi/isr/ve58oF2sQ9ZOjKSZB6/y6I7Ux"
    "OBL7aeoG+z2YwiiilM3UwGtVmFcDVrHLBsN8R71xH6ih34k1nD5FykD/zFxhYKiwbGKVPThEt00ueaA6O+0PuugV3SldwWIajjsl"
    "xHOgPgNwR8n47i5fHIvd3b3GnQdYLHGuA6TWs36vZYYCR4xyGJc58SUS9gpujIHAs5qWcPbW1j6VToDr1a7ziybEzq6wqMx3PGni"
    "VEruuu3vXXrx65fgQGJzKUH6rfd8X/s6UuzxlpSgSOrTNOpEMbrzRq3oujtOIsfzk3D7i/cMmnnte7mKjCv83ZLfACHiIfQPRVGA"
    "egXq1j3yBlkof/KVLdjieBdoSW3F9Ags6kDSyKPuuN9dH2DYhEctgligMlngfm+dcM8YLQN36wPKCSmJJ+kjVPBgT0NttUra1uOJ"
    "F7e//3Hf490aSSu/T+PxrdUQYmI4AkRg7BC81RIE/wDj/82Xd2+9y1ufxxnWLOUM8TyHDl7NcA0hspGsVhLsZ9aXrK299X7f96G7"
    "T75sLP0t8tfWVlWN7hio1VXcy5xHjl7sHmKrfJqHg37vEU4dP2MFeIRu11VE0dw0wMcX+A35EeRxZPllvuI6a8J54LqKWstKg/0a"
    "tsUf6uH3L5n2hsk75ttmRLtaXTVfvIyt1vuFrQuPkkNKflzkLtB7hXWuz4G6tPqqq7kF4G9ZAPvJR0rUlqlD4ME6+MnBwFDvUQoU"
    "od63CmDeWD6Rb710x1fkVrXrd5hKKJnA2RtM0fXAC6vbA6Pyb9GcddYDRlmT2d749ghfYICKbHGzJsxIy/lWPwyhgaig/vbZELpL"
    "WkODxiac6vBnos4IDoNcgLD6QyaZTqpglnbPJi3VpORKWIkoylB2v0/0fq/k93sghvG/eNH7F6+eRcE6z/rnL0U7fcG+/Tm7pFQ5"
    "ptUWN4bxcPzgc/vX1KODD6EBbvbLBE4P9GihuErneHtKn07Hw0vc25doIRCRYQf+6cVptz/guFf+1s87IG3QmygAMjmL19Y+k8MI"
    "RlPDQ3Vtzftc4hJtSgOpgznE28jqSMQOQH3/LPE+05Eca3AYvM8l+kuZBPrb2PDaWnfbCSqTbnvFbdFQuLkwM5S5VT8hYAik4NWO"
    "oHIScciK8TZ2SwFOdQXqn6NtfehfxnBOeuNtX5ULLCQgRhCX8PuTBEZF3kGHSOW+LrsYasccM/TySKEWkWKDO8ThIpcYt6WnrVhF"
    "Qnx4b14R+HEw3m4DJ6pe4ylGgw2q5TIsIZzxLkHx9gscllDpp4QKfRIauJ3iW4OpCWHKEzhX2xi4lmFcNTBimprc9PFijHklqpJL"
    "12OwcEI0ehbh4jMsVpyuDg225d2PCt+akJNtZNrawDbnVyEBHBO8KWZboTCRw6u4YL67knqG/7YoVSRrJezZH3Bns7k/01iV5Dj3"
    "NBjjSpI6AQdcB8Tyj6BUKiF8f8AEY7xjCtHxWk12aSKv/ICbXpemdeq9zICtbca7aLrdFrZGXVKSlwExWyBX9baNSHi1fkYhKebB"
    "6bYjrV2iE8Q8GLllj7vohXiZL7qCP4D5hq/n27bESSOAt2f5t+tA4ufB0bYl8l1tF4qM1DoGfgaszIPbouE5XJwZ67HVLWaqmJIA"
    "e7PddiJsuMOwBNV9q/rJ+mR6jBw0vN+xgb6W1kKLlU66KKtDyQ/bjqh7GDzPvnhmt/V2e5HM/MUutl04AIyCvAKdD0+h/EUWKl0E"
    "Pu5u58TnD+z0KOIz3QbNJPAj/Zoo97wZKjcu+8DjkUwCaBanHYBL5OpghgVwDxLpTHB/t9MiOTm+gcUtohldMrfhbItLX/pJjwMc"
    "YfudmC54JyAmoAkcQguiMBTsUlx6kT7v7hBKfI02LstFUaqIcijIvkUdXu540qffmo3iMfLirZ/3vVirB5RYqaOvlZTws0gm7Swq"
    "wienSsrQ+my66XQ46OWAgRRAFFeK/7T026dhuRxMC0cTRa2jHW9R96LGCHpY9xjL6RKBbh0KXZPVojDOwcmZ8KLBKdaTzxj4VWpQ"
    "ODvdkk4qZnJDy6sOTBEDUoJ1CywfKpRbnxAJqmS+0znqTYKR1bMOKbuoWwFL9Ro9nul3879HxH5hc6IRwiUUJG1cJ7B0D1JHEbK2"
    "Zq1g/hD5HVWmxJsqOtSxgbPzcQD0fxycnnm8b0pMlgJZcSqjakAiZ6+D5aiiEmH4PWJgoRblf/x34JJb3A+lpx2Oj87jGwdwfDsd"
    "H52gVxwIJH+LnlglAYWjQfck9p7++9+eBnDYltLhRwyYtdOdxB5hXyU3heZgwKmb3NLWUMln7OTxzBSfr1xeEt6tsnyUkpIq+hua"
    "ecAepTIY9Xz5aOHgsebPwjkdQCCVxyVKb9X50dbIDZkQsM5MhwPHELo0Kd+HHU1B0iFUOCe9RtKS78E1rlS56V6wTIGIZnYlQdR5"
    "rPd5IMN/eV4CbuGIE8cgk//ayLywPmbwLzKnhP0joaViCUPhyot6UbueWC5lj4UuUjEm4UhwZ/Cqo2jA1EKmqC9kyA+ucBze7BEc"
    "Mef9Xi9OMLYa/woesXZ50MN3WdwL6qmQEpqKy7mCFdDnW8JdJzusmehF8OlRywxStFdo8jAGseIRHcbC289bsa6H+4kgiG/ncKIZ"
    "HvqYpJPsjh176qijKn4L5RfdqQnKFyRKm4jauHdffBUNkY1eRNCHFgAw+DejiXuk7ePWkbFD4DmEsmV1fyRr7BHmWaKT/VHrymI8"
    "JHYBfea08dyU2M1NOhFwMRIjTKsfuCBCuH6MoPFxjmYrM/I2GF63vJlY5uGp3v7+1uMRHUgOgUNlycgavYQ1enigqAxcbOySUYqi"
    "DH/xAbDEEIkKYNCfECliBEe+raLUDCVBhu1waqcYoTpQN3Ln26wfmOz7wUf4e7vj01aHnk7HwqEPvBN6M2GbJiYO1UqrVp7bwd1U"
    "ebTHwkvNQ3Pvd7ZNCqeRvkRlzu8yVhoNSshmKaWutoNn3oR6DZG+Z1aZUjcck31gpPTNLGWolxnliWK8V4C9RSQq/a1ijXHmcaMX"
    "qnXpVGHrXqJq7gkU0EFGY/C1rvZ44qXt77P7wVbKmuEebwfR//1/RU+eedmjLUR7O0t9wzB2YMtcobbpxdUSXQ7qbW63ncuvBkgR"
    "fnAJkN7dnXmWLSJMzc22BdE+TsClmgCnqKWh0lw18PzJMNXTeUbTyQ10+NjB6xsY3xk12QS5wFUD2feUGQrm9nsNUNJZdAncPkzU"
    "oEDJrD5Fy4FepId8t897QHfB+j/nDQzhw7ZrFfn4SyCXaULwrBnhoRw6Iz30XfW60Bp4de+A3itqwONxaIJKf2HqWFThut+LV4g6"
    "wOdFtMEZ6T8Tg8/dRVCACgvBOaQoRUQhUkIXKZdoMW0qZDAyZpTA90UouWdRZmJ74nxTa8HskRYmHyEnoZgUBmR+qG6Fsl/u7vjE"
    "IXtH95MZ7G96AYhm92dNDap5auCaYzDcb3GX5/uO/uf/9n9GrO8PyyB2f8Us3XdO0dVc8Yrkb181Ae9p08llo7311O0P8jyRaji3"
    "G+8Z1n2DGcSnqRmLPl5oKeGne45e6yik4u7lhkj6sj4OenIGn/LfJbfC9rlCI6ZHVgnxi2eetEa0XVrMrOhtXBnQ3JNTU9Sa5lFh"
    "pQs4xojYA6EfFdUrom2oKbN28M/Hfv5sScd0hOY4EqQ3MCtXwLRM6QWd2i38mNUBOFd6yZcE5Ic3NH/ObcroJKW3wQx+Oe3M7ei8"
    "FqsjdhmsUDvMHLZftotXFr1kY2ZhNsWEjZ6kGJutydJJ1dLRLE8hs4Oqx0XMDfcEfCj9OGRmR3ErMbEqws5KkdzdUXEbBcxIwUWy"
    "ITq97aIlmW+bUEpLNFF3UlYrp9t0x3R65ueUA9mG6IOyEtANjGx25xIe0O6gVwAHiawT338S0cI+XVIEgR0t/t5xI0kjdf/Fs3bM"
    "0oY5ZLK9lX5Q28XaFwubKFq9xIHAqykt04xJtjFkJDkKuXqThz5ypSZtZIi3eXvbdJ131Z/0KWp9KDQsMmYV43gyHFxxgj5JPEIB"
    "d7BwH0MB8RMq6oN32+1ZzJcpBCIr+l5st9+Nh5f9CYVJw8YAs6+22ygsgZTandwmJysmBcK2DnC/t60qrK2938ZHq38/WH23XYJV"
    "JxdZOukiIuxKZUXcEpBiggdE7pPBcAJU25M88KdQa4Ky6yEQNlSebKfpuA87NfYit0CkFJcqq0D3uttPV15sB0l8vSID9BIYknuh"
    "sbcdzG7jiRJLk6EOIkiZbDQaW4qLiAMzH2WDfgf3qY16TCcMDx0xQejQ1aR13/N+2xiFGZRumZ98xQXP0m8bYIJJs8eFSqhXeKVl"
    "3WfFQb1cpkygnRIKEZmJ/GObE5G9gr8BI+tt4v40Xd7dGXAkrcAWQGymLp23321vFS6wLVHHk9pnsjNMElLxdABNHb0qyOBmX+Ln"
    "52a//ejxbGd/vxRPTrojzLI2fwQLgvVnXtJBTvjkPJ4okh6sEMaDFd5mwUo3WDlIu8esNUBjtBZUynT5sKqwCgkqQKk1hT/AFHLq"
    "LpnH4tW+tlb8frVtKiCb0ykuxuMVHKeM9j+5Y+I5Z23YRrUJbe1VoLsvzSMr4T5m749+te6oenyn9qPzSi74Xhfc2sHXyfQYTTqd"
    "Gt1LuSj7CTvrZ+7XDoPf3KY40+08+ISlT4djNOSUiofBz/iLae1h8Dh3VdaT2020So0v8l9J/p4H6YXTIwMCxP/CBns66Z5h4XFx"
    "4f7FokszFfgTWeopQtK9WHJ5NpSPlQyPDJ8mbs+qxkkBQIj7c/g2sIeQAUQpbWDdAe88Gg76hIzpxYLrS/jWK4Scv51eFF7xXlgX"
    "i5dLmj6/yF0aPhOriYzR7dcY2GaNSPEaz5jUKosWYyO75PKQ7gTx5khZsFm3VMoaVqwvH26pasxjf97XZrPGRvWz/XL6FUbDPWXk"
    "usrmHJQNBm/TfhUbjwLjCZ+vvNSVo3W3ODorXQI5uPWUdV0JT1Q84ILYb5HkG1xK0zOT6mYRlKu6ZTlhRI194trF0Q2kvAum6Dkf"
    "/T0KgKIgj4NnzQHwJ4ft4UJs+MrDGCQ8vCJmqAaqFz28wjvCoTew71nU7Y11IWiuIgVIdfvnDicD+uNZPF95PEvxn/E8KgHNvoQT"
    "pqVU+Vw8pcIH4yB/AZnpDBpU1qt00XjPPRas/nM1U8yvyZxiWiGdt0hlWcLjncFn6F+j18glrAWVGAVapDTHpXE3VRN3fxu860rJ"
    "8D1pNphxSNvmSzd9z+aeZ63dbnpeohR60gsan1GX13H8ZfKwPtO5VeW70C0dfbcSRlwcb0MFBCoaoXAiDQhzo9oor605oNHrf4Rl"
    "/+9huRO2yltOH7CDeLWpkkHic5dJ57Xb59GQ7gH9AmDyHfoKPJjXM3deOX1ng0wYBl4ZuMP2J0D59dMwrm5hZjMa0ArsCL2rR+N+"
    "kk46nYNDJq3j9uY69Xk6GEIFL11PSikwnf7TernWAJ5za/x9GxAx/q6xtubFB+PDJ+0EZKju5cTk/AKebYRsqw085a1Xl4yWcwHe"
    "AjqDUFsbIDsBjnpsP25lUuLZN8SL9vramrz6vtyJn8rvfwBGlOHZrdu/c507Nt4SWybjXqwvc2PVyLFyeSiVStaJYilfD2asdXmd"
    "V7PKEtbeEErt2To4DNz2lHeG1ZisF/kibR0V0NUjyzLX1EvFJNdaemjkSwa5R4ocEiS5LmlKdJdXBV0CpRp5V6qVlacrX9DeKtcQ"
    "mh/odjInCX7Lm74cmCPAKqBtwTFbvYpSN9EmGiPPfvsAeweWod0ZEJeX/ATwBzWXZoFbZsYBkFE0jtUzeyvbMN/aBNiJF8LB6FaL"
    "TQdu9aDYgGDoqTd0rKE8iv0d+sGNLNLHmscIZgCFDA3JPEoimOX0oZYDfrCPDASKq6+SdFB6BtQaZdQXwzHIbZ5il9CSPOVw9i1Y"
    "/b0+MreUeRBLYW2s6NG2hDbjuD1DM8tWZqcENM3yFsRFvGWE6ZcXtIrEkEpe8cMbtuJDzl/e4883wsXvKF8pL44PPpdQT3MIfI5p"
    "EhWosWYfL1W2cDQDRXNY9YIECz9IYosS4Mj2gYwcEJa1SWhAj2yorGil2feobcqtSwws7floJ6b43lhlXz/Z8T7j78DAwuNGyK9z"
    "gBOcHUWF8ImN91uZsXX0BguPjpGG6zrT8Ad8pmXAIOdpF+6uFoGFJlxoLjMWgKGZHKAde7peJVAO9pLMFZ0t6p3fuq82DcauyqMD"
    "0hC3x4nHMm83Bpi2xPqZ2wtIhSL+WzNLURJ3PCgeB15fDSCrXSCtglEfeJiBGyiQLi7xMiZesejvw1BWQzhNF3aQ05hA/dbjWTcm"
    "VYnp17bRH8aWnTkOcOtk20PfwLc86q/uLdtZTumEdlyCuF9ArmNtplozYoET+azcJK4yOe2PL/UXyXwozhlBRmoKUI+XbwzIqWFQ"
    "z4Y/4P0HoAHOfBisaVnJgq2x1WQW/hODMR7Fy/woer2iEfR6Geiz8PZ6v8WTReCKDjLDHkAdioyiiT9G5hA+2OWAhZXeU8wmixf+"
    "1iq/KfVh96TxGXxL/bu79LsQ/vm+Uu6gtTj7GAbZTvV281uESBpgARLJ8BzYoNkJB3RB06c8YgcxhQZRR7OXpUXYhRw+eN0nxxAR"
    "j7lNltR2x/Ja8EOJAbc5l9dmhlEA/8X0pnm65q1mKdvd3aJlSzXyMz7FfDJflhNAtQLcOsvWgdJKl+Fg5RVM3Vu9KJzAN6Fa9wxe"
    "W5JZfql4fbiL9yF5L6nFWgt1d356K9eJGYdCZlse2XWCmWjilHHW6SLv0vJXeJfyLrHMFfBuLfKzvp9wor71BttQiL8v9+38ePVA"
    "3878/SVdL+FAHj6EAssp4fpI3xu5PrCZT65rH31b528aBW+9dPueAd/8CWdWyx0Ci2Ys8DLX9mTl0VsHXnVIlmX4Q9l7DJN1dMd+"
    "1FrtCdk89B0LGXndiZJ4mo67g0hf1OSM8cZKL2du+Zbolsi2nccfVoqt8yyzvF/J+M/YLSnemSIBREUWEwFb8f1I5nkKslC9fi3G"
    "hG8B/ufei25mCHY4DrxsVb7jru+8eqkMhZT5tHqfN6JGvVH2q7aZHmshQgy2yYA79/Z+M+7lIpW5XSbM/i6Y6N6YpTlQFGaa9Wtn"
    "+hjZH9CxXfm+aopkk4isFQqfpZcKo0Zbp17hAylY1Av4Ldt3AIfNBCSqWC3M4JGYSBR5tzvWE4VGK9mdl7GSCPSNMsKEF8vTYwrm"
    "R3JP5HSNay5HXgmrjuXT71eKek++3LqIEjKDoZMmGk/neTydZ/F0/g14surkkfBNo7/nxv8+WmBbyKj9KkYybs1vso8x/uQPMI05"
    "ZHOyj9uZGVWRh9SM9sjkZ9RN4sE6ejbocxdl4NMjMlOgr/Tc6sfuFZm6GRJbloIziWVvnowcO0ABWCW5F2f22J94HHDhrffZJ+Zk"
    "bQ2FEBgsxjTDnXmID3zPy5a9uqgeIqoEclazvXV8TefHdYwn6DDZnx6jRxj0OIidHtiuizD1G5uuqCFAG4SyfpLBFxpd7qhZbwaf"
    "ttH8SgCz2Ea1rc6sbdUrbpE8XcVegJpC8fzRMPk4Qj1Iy3x9pDKsKbxBQZA1L7s3bNnciuo12KdAxKgjYAQn2a545nqA1nH/OO6R"
    "vT0UPUex195ceOlqOsYFB63SznEGyyx5frDhXzPYytLBhuVK7ZtHdGjSsVtwV/4auKt5uElsY4fZXnzSB94OE02S4KTbyyo/vn22"
    "pGXKCr94fb5hQwCa2swiLVg7cwoZhUwsGluxJYqXKFBjE8dmOGJaRS3GKgeYhvfnbbJgrDR8DoKwXcQfi28z7Vv36BE5aNIlWUsn"
    "+LSQRocnEC12vzkb2qhSx4WOZnv4QJ68AAS287GkiWGc60lzdzNBLM2dZdRsG0Pwt9kj+Hnc7T1auC7mh2T6fa2oUBUQWa34JkAI"
    "EbTHwi7h0HJyEDEVmtPQ6hsK/ZK2+KslJdX0gj5BKUlqL5caBrdfKSYtn4jcEKaWhJMdwNSWcCRtogGfahZN1dcBoPSmC2CQzxYY"
    "dRcMVf/PQyKKh2I4WC1goNh0oeDPWY3E3V305wBLtDBAChrRumL47z08M1pahbTHmvBi2Nn/xcDecGHnz5mu/jToDJq6IjOdN11V"
    "gRQo6uloWQCfB+gycsBQuItnOYjCjPaCih0tBswPjDbuXtjCB8LGak4F1Elc2K/KyaaNg21TII6zrsj0ergoFo4NXeWB0E0To/+1"
    "EBe6iLNKLSdqb79e95MDvWqBLlJqADIrJp3uZY+ajAZbjWAS/9Vg4v+CWjn4yTmOVT47mLbzsTtpcMawl09vfTwdxPbsITCfUKIy"
    "mbQ5QfixnF8WSBR+Hm8bM9ILHITxhWVMnl7o8EeZSzm2EEfdx41RnjhKt4xkJJbiFYv5Ty6s38q/47wKYo/p1rp+fhePf43jL9K1"
    "Mo9Q98WWqYs9nG6uKWXfwv4cVtHhRZE1v2UgYXdFRvRnZImichc6Rv2TXL9Yi8muQpXVd98Uz5ryEJyHmRhq5DRlhBzxoOhi6loq"
    "NWmpa93rfg/Y9nCzHkimBVhuBUoFslvZBsY3Evdl3UImBpdeRFyq2GGEEIEzeZJDA4V2J4sWmUi1AgaA/uyksulLJrCYu5IAeacX"
    "xoHC2D1gD0FhQzR34qrw1hud+coKSJUmhT2iHefYODU4pgnaodXy+M70NgGqEXvloFL2i8MvAvMJUsAQSGg+dmSxxxYaiVIeFnSw"
    "jk14Wp7lqFr+O8ahLXTWwr2K4QfIVCgbaPI+TzHTL42NCPYCj7D8SaND+sCAubr2FWSTTKUyRt8ZfmP3Kj2i3D+6+EaolcFo1nw3"
    "g7/NxuhmKQKd5ZJZKNE34xQX1P2wVe6BDb1u9NJc7KwlL8U82y/eInj5aJGny4JtjIpSMm4pbGCe9Zdjnx+rzV4BZU6K6PL0XtqY"
    "dyjSw1T3IaK4tC7ClJPPmbGQHg0oIAJGqLpQFvdiln0YXDnlrs9Rwr0ttK4+dkqiV6DoFFQEjQh2BJ7dN27XMfa8X9jkTuHba8c6"
    "m4JxvmN1YsYWW9kXU5z1DkVxIHtCy0RbtL06IgiPmzT7dOSOkXF7+u9/6xyU15sgMxzO6vOn/RKuAi8m7p+uI+L89YMig3W21gr6"
    "7dnwSwubDQA38eBW4ucGl/0b5MX4YXI+HKctdfstetxW1O8h12NFCvT8mYyL/XRMjDZ6edTrTy77Ewrxpu9Zhz7yoJ98wYd75Son"
    "qnW9R6VKvJL0LWuib1lPhsfdQdbplSPaw27FqVI0/a33+46/JL7w8jjCdL4xLN0UM0aRvofatLc8bIRkYSTjUPUE2F8Sr1i6GX6J"
    "Mi1bWyxzc7xUzlt4Pcz9jOMTzDCXuVV1vrGJkFH66Cvk7Hyrtub3yBTDr1OUmDDB33CbnB+xWpVFI5ZvmRF3C/RpCiS8WaJ8BdYN"
    "LxDOHUM4uWW6n5khA9Ayy58YAtzAKm5vwXXxFHo7uyhSRQrhCDJRtQd90USmgUNbdXBjoi4UxYd+zc1164xuMltjj+80p+OieaIy"
    "ji/u1UWxLy6FJrYYPuYwFOfJdW8vqChu1axv7fEFxS3QxFAIUZSLD2x5wkLlvuGAzlFnKmf5eezJce4YjaMt+D/CchnA/Hukmewa"
    "gWG1lMRo9rG0JSxyNDpJi1rjU9Ie3M0Fo53IAxOGvh4tWlgStQWJAg6vJKUd1l9EnzBZW7eHkqemGMChi9+timNuut5nlCtPn1D8"
    "d48ujJp68Tluyxp4hH+wzlGE77l7LsbxmAQv5bLE4aAdlyUnmBPvjRhDj0xDCStl0dJbc0gQ/e8np0PD0VLj5IiC7BDe6csOhPZK"
    "6p26iqSXKhpu5gCBT+vTsADbfyiGCeSbD7Lqp5eXRH5k2VutX5/ffuCTyzJvKCz2A+bwExqQR30W589cjoRCA61MrgDet5kvqGP6"
    "cmHHFD0ZjvBqfbvo5cXFwkCj0Pw6Tu/uRfvAdU7cK3Jh42Cc7+ATXyteURwyePXC7YLLvbLKkT8rvHtz0TY+48pd7j0UpGsFKbd+"
    "7gRoouH+kYFQfCmPp5NbaOEHt39icXTAsuAXGcuGHQILF4i7Puj+aB68NNDAFEYFLnwftevignIE8a95R7/JL/34OsdKwi5BE9XE"
    "WOqOzc+++tylH8zQB0N6MOaA6JmXfXNCb7qTkwj97KSVKf4YyY09LFIJCBSRKx12yrbb6EFnPRnmkMBOx7cq0R/q2Qf7IHB3z8h3"
    "5FUaY1wn3K2w0U5wNqXoajif/5R4Uwq7jS04VSdSNQdYEHegJYw94EtzuFV0CGfOYIhNruLNu7GRYW5xbU2HZp9oLzesPeTo36t2"
    "SSnBYb9xaiiUpW3RHmfNfPxDsVHXzmaXXt7G3WT20AGOfPXV0/5wzNKwf8HZg1qzTaPua/GoPd7h+IbeQXyI3kh0iQpEsB/5B+Fh"
    "ziEJhrzbHWkHqhQdqBQwKiBtf8dLXZfTLYqFOMGUK4HH3kSJf3cHJ2eopIUD5Y6muLjXJi4V8HY7xKEg8e4N09ZRgAGfBQUiB6P9"
    "LQ2GpsI7SGk4mFfVSwUN8DJI8LVCRmr6YhaohK6J0kkSUPgSgDVF69FDGAYskStaItq3ZtUW5dQyk68YDVx+YkhtWT7KxeqAd63l"
    "F2UF7dKhTw8XzZ+FHo5lglbpZOZqOWBFHDCvoN3AthqO2F2E844dyQPqD9Vv3gwPgQXXvYBibq+drbcq25MgVV44T1ZX5e7midc1"
    "25Uw1Cm3Qv/JChRRLqnBvvbvVXyxWHrrvDl3d2P1o69+qOp29H40x071HKmbGZZwx/aDmUiVGQZ+znFCd9wt4gJUSodvhtfKJhDI"
    "tV62slBTqdhtu3tGudglaqV1NZlAH67MKPGzve+hSHb8a2uwL7v+ql6endWwtYpoge0aKL9ShSPpfQJV1Hh5+U5yNCBmGpBVeTgk"
    "Aq/kJr63OpH9eHcXc4LS7yayw2CzTIhCACz8SXsZdttIbbtCVEUA6u3gD5W1I1DexhNo2ssR/I6UdhY9noFQvlXG0NhzcmyKC/NM"
    "ra3pRFMIvSSakrRR2sfJM6bpr1V8oQQmX3s2qukzn0XG2TVh93gOcyV+kTjIc9vrKbtP9AJnk76zHWXIpT32lTkL+UIp9x6m2fos"
    "883C46nqJCA8UDr4FBUe3V4PfgSJpRrqxxwqh1s6ONQrY4xTf46ot7BKAztCnz5yJvApOMs4E6vNnyWl0XRyztnlxhgHM8ASkhAg"
    "ktBtwtNzJHUMeLWFUkQ/mcZz3oxeim76IKDdoQEvttJvn1pzGdOit/uKVT8cgpNv9sYcYhMd7HrwgH8CtKVv9U3XQd93doTU8e3G"
    "I+AEn5CzSMFgYBFjmFSMtqMbVW7ECY2nq6Ze+4+pH6VTWOe7TJ2Ff8RZEbA5jqia2J49fvrSOUDXR/QWCFhzyn6Z0H8LWtnRi2aY"
    "619iDGFqi+cgvvXjiadBksPigPpQRjoxW1EG7CSTiYnKcadaVoB4xvJqHuQ5ikmSiy12CXBXmUphpGo69nmlp75Fc1e9GDiEfJBk"
    "fEnT4NPK+KRykQPZrNzdpQLpdxUhkMA0iWf8emiWfTvcGn+nym6NnzzxjccP9HAwPjzkQxszddDzeihvgHol35Xv7kjZ0D0GdK6r"
    "hp5W/O/068R+jYwGyAlm635X7gBkLVQxiE44PQDGJ1DP9ISZSE8yuPtsTCeIiFinlYqBTRGssZwEoiIvrLu71c8lzE8DPxT+1SWg"
    "8hUX3yz1GVabdmHPButNTU4CiWnCzBcxNSfaWa/fYxACFdDjMBA2lrK1BLP+JTrYoroFHYkC7eRIiXjEy9F1cdzKRPGCw0lcE3+4"
    "fdXzrIjXGFGAggbEV/3hdCKl9vvHAzgdOJwEICPFkw4aIS9R+LAz6EOp97BpiDcYfZcu/Mo5ztdD27UNIzBkXBRLKFqy6bNozpHb"
    "BpqWdo9fYTQnWJrA17Cn4kyMg/dPxkOYXsIKLAp6epWkQ5REvdkxnGRfUA3WHePdE7pOMWIGmeWCjvLiVUCB9DI8ucp9s+MsiLlv"
    "oomMxkPYk/GkRLJ5h8OD/I//vvJ49lpaBoCBK5i8AJSTLxYVbGVrAqWM7JcEj92chlTaQ1jd0tgCOitOY32LM45PYrLP+cS97Gi7"
    "4KPpeBB11I+WFWWGGFwHCzp7Yfa9i5YOaxowyekR60VaUXw5Sm8jTKAj93BBz0BndZlteXRGymbPJDPCsBecD/M0drX5xSl7cOKO"
    "dA6uACM5zq3EjhNLBU1GBc9Iw/n8QuWAU6mn5ghy7pYkq9njmyhbQ09zJQ4OMuekLdSDDki7rtrO5kDkmnm3u2+7PJHbUBg9FPMt"
    "37Lx9V99+eG4ky3RDAaEDZyld6zq/NA9zlm7XV/IZRTyjUXOaKP1szHlgntEYXXTc+27uLp6Ypvj0rjo1u50ANwMSulWKFrWkBWE"
    "oEfjlEoUvDX3I0n3SuthtWXH7n7GiFdLkzEuQTGEAkwDG/ygmbz3coiXFzTnGFmvAlJ3fDSK+GUH7Qb4e35Zwnu5NCo0YRfNn7sg"
    "sS1r5XTvWzlXX7tytM33w3wTf1COAZblv7pjKjb8n+irQCUwx2IPxdOUQTddTp8PB/kw41LcL3K0KZz5LCpFvayx4jgHWP1mQuvx"
    "Yos/uINO7hm0sqVM9KCdYbI7wES5cUEz9EKNSk2Pen3FzSpl9yPcwetk2EoZSBcjDTpTcuJkOeqsKO4O3vT7RZgb6tTxX4vD/j04"
    "VJ4u/eU4vPo2HC5GBSv1soiQt3NlTYYmPsqNw7Gt+nKRuy290hH1gB9OzVYARt7vlHpDkDffekd+0Q0qXt4tr05j6HRyE6+Vn/rO"
    "iDFBkMvPDOjbedBjBG8RYLEVO1k3csF3h0n+qmrBusmvlG8h0cpY1sUDp9LYI0uoG3Xqt4rK6O1hQllPHZcjO4PN1bo4BjpLRBpc"
    "V/k7tGWydn5SjrerU2X1u4ya/3j1ldTcTcFnX+jOXO+aFM7S4+54XW4mV3JJA/Fwv2KPGzrg/CzrfOgXhsLM7hkOWvrMm8aWyzGe"
    "/Hd39ivNvXYG8pa4zmqxT8zLxNN8idyayXTYZo08xBXz8T53zex6EAYmS7bG95At5Rc0Xk62zv75pJ8VgPcQfpUtzZ05efvXE/3u"
    "PdhTbknd5di7/auJPi2LQs6BF8z9mLh/7MN7xq58oYbLx378bWOX14rjw+AXmvlbxlMNx2kxRwUfvgktDxOlHJCMDzkp4LOHHd5L"
    "Z8BG7jrDhutP/bEw4lkHdW48+p//7X8H8fl//rf/I8qPGPA3tim78hxTjeQaI0Ba9GAhqzAqiMYSi2n5aLOZNBh7clzv4Dp7RN60"
    "65SUXhlTBMf9BDBLWeppetSi0GkxtDcRhtAqL1iZp3F2mte1fbJxD39n5DU9MU467uLUMC8ubB/zV/lGJIS3sZDhaGGBY+YRiVDB"
    "7ImVpUK+8pkyULdb0d8a9J+ocIFIjy/Z9TRpUYSTBUKbNjIZJq8oCtVEO+SpG7+4lHbHZ3HqOPrUysGbC1/dkv11EX3MGOCI2FGc"
    "rFmvzQxwUVTkm1YwT+8XzoyDJ2MstgvDOzj4OAyE1zkUfkSldnBVCqxNFKVCej0EeuhqhL8PLZ7DJlQkXQ8UhSrkSbR5D/B0NiMi"
    "CjI46IteWz78x1lTYFUmL+cbrVsmgrnGstHLZFggUg/mOw2D/mX3DDv58qFAsZAMP44H2v6ZFkju6zEZj7nUjNSE68lwHbtdrPSy"
    "FxfqYfBuZT9OUxjjxFFrDe9TTvT+GrUWIcOimpQAOotNVp4WILOiZlBM13PoHMfdHuuNNU4L0Ma1H4a1/xRF4MM9e++f1Jxl8z3h"
    "q5hg/MAEw1a/Zl1fincC668L5q66fCNQvexGcA7S4+7l8VRxD1Ydfu/nG1u2b5L4gfMvy+p0HE/O/1MUwQ/aMUYEyyO+ptwqptqt"
    "QgUUK6JHu9jOEorE3xfjls+Xr1XELzwFHW3tvjDPOh9VvDwShoNHiTGVRaNzp/FLoSG+OsyylvgmIFHqGpRGJH3ubgec+D1Wed+H"
    "qiGdN7jgZnOY7OOVKOohlfZV7Bfa196pik6CS/FHshmYGOfvni7X0+UsDJEDlphjTHSqJsGUsQ3nCEx/XJgEZKQkV9nH2B1CJR4z"
    "LhEvDY9BS0Wm/+0pphgAwjyhRQgNaWeIolxSlRpeUbuM1fmFE8xF38eKFYUqbs2Btvhdls0vqBCzDiPLOhzgcD5mhmOuAMQzjky1"
    "fywwyH5d6FD2u2s4Px6eAUmZLPcpQ1bobYKXfSMpXxomHX6vDN61WVmsapQw0uakUzrgX4estrmKKSP0xfDYb9nuaVbb6JKAhc/7"
    "mMNcpxRJTUoR6Uc5QV3vlPrJyWAKjLVHTXPqRr+1uvph58B6gxET+m6Gks7BYSvfckG9LqXJjktABjudsv992ChzahJBlhWvP35a"
    "L+ur5hQjNuuxnaNa7Bw26mVLWXP9HQqXRt0ebLdx6lUCMi3GEMumFla6bFHssgl2qW5ZY7pcDU7as/cf9/Ze7f2IOfYmQMfevX/+"
    "bvv9c5RlKBkUsZn7b17tUBn75bvtj/vP1T3oi1d7r/ZfsuPei+1Xb54/UzzOPBhgxxm0kFsLe0LE6MZJQgGm0SUTDqskluHGo05Y"
    "LrNHy2X3xitzboXLfuJhBDiuMjpJ0UTXspbsWUlnsAgsmwN287FMOaCnsxiTvFOXaErNY4AFJ6ZQUgbOE2D2b2HRWl/oxdraKsFv"
    "I58+SHp4+s3WQuppMuew/W75SaT7wCgdFhYUSLpHgcDuErMuj/Dy3O4W6VXiJhXR+DktwI/GjL09BBKf+o9P01UyuSGrDTYWo0P6"
    "9yttX0vosAZX6h5jHMiW/cqJ6jj0uGU0bLc29Wk/6U/OBb960NzdhenObrbHvgXc7MTD4PSYR8Pzn3AP/6jHNaLiaW6R4fDS4fBL"
    "pqM3xR1hSQd+fEF53QobBgr8sAHwmK2sCoh/qE0B9uf2KnSXX6b1T8Wt87rUgakfz9Q6WXm6oh8mczSESNwAxGNHKNZ2uk4Qhoyz"
    "bPbyfXSW9YYVwIq9mfAu/kfLV1GNIrX8lvIMz/g+fodPFivq1+hsHVY/agDg1+VwjFHjvi8bQ4KfjslFfzxsYa7VMmZbGGE8JCgk"
    "wTK7aL5FhyPTooXBCgI1iBZmcw0eqUdXsaBHSj7is1zDEdupIJvQ6lEi8hkL+wp5XZ3NvNifWNubLHT0RRSJQUvG1Xex8/CJQ+aX"
    "uhEbmoX78/HMqji3Osx7ChbIffklgIQtSK2Y2TqcquhrWKpIS/hHton6cuWYFihtV2RN9P1hTxlvNlvqjIUDKUeyjKzIqOL+oHeF"
    "+ak1tjpGAXKAqv2CXdDPRwI0OyDqo1mvtQuUv9sKbAD2pM85gIqH/UMmlUo6q8Yo814X7Odk+E5CeRS542bQ6LibkxcVcKzMl8a3"
    "gD3yq5/BgT1pHfCb6Ir81UBiYPcV5FOAdUGJExbp5OqsNbu5HCTokpumo9bTp9fX16Xramk4PntaKZfLT6FIJPFyKmUVLgd+Ybs/"
    "DG9ADFgpr1TwfyBY9DF3jsjoyRBOz9YBUBhgVwD3IADshuWVaqmysRNWS+VyvUIP5XJjJdwohc1qc6VWalbKzeZKWC9tNOE9/ClX"
    "m+FOuFmqNKvhCv5pbq7AYyOshSuNUrlZ2YDijVK40azAc72xsQHNN0rVagW/NxuVeh2/16C3ZqmCb+Fpo9ZswGOt3AwbWHqjWd3E"
    "5+ZmfQO/1yubNXjeqDcqDXreKONzPWyEdSxfr4dNfK5Vmvx9M6Tv9cqGPG9i+/VN+C+Vb5SpfKO6SdBCu9hfvUmDx+danZ5r1RqX"
    "39ig53q1wt/rVL+52ajz8yZ/b1Yqb+i5gc+b5TDc/AX/VsKNHft9hYe12azSY30Tu10JyzvqbVhGDEtnUImeNzcyz81f6G+j8UYB"
    "Ac9VGMSOApKeGck0CHoG5KpB0vPG5o5CAj03BSllrh/WKxqJ+AyztqOQjM9VmBw1Cfi8sannCB8bPKc0h/Bcq4b0neYYnjdAUtVr"
    "AJ+bDD6uEHiEKSNoaAGFYakcblb1AoPnaljb2FELEJ6bZexG1mdYAeSWq3r9wjqvNeuwfmV9w98yNi/LH4pt1nDwZfq5sVMvNZsA"
    "Pz/BbmiU6+GGqlWl9bqpG8W+6o2m7rRSChsb+KyAKjVq5UZogAaMbfIgeFCljWqDccaDLtU2yoxSxgn0V8dBKZyVqpuVuoXTUhXg"
    "MCgHlDVkhjboa6Wx0TQTBs+VSt1MKADVDCtmwuHPZqVhFgQ8b9QqZsHQIKwFBc/VMDQLDp4rtaZakG/wOdwIV2TB/iILmNqp8sxX"
    "mrjbAdpak8tt4kKHKWjSnOyoT7BjYD/VVlRV3EFVecYuZMP9IhvwjQJFNuiOAlVvYBmK3uAyVE0ABBVMIHioiComIA2NSk1gBNVM"
    "gKg8zQQTKD1Rmn7JPDJ9w888z0z/anodaPoo64TIJ25RWUdMXTf0OlPUV61Dps6NFbVOhXirZaxou1rlTPuR5vMewLNhRQ6Mz3hy"
    "1HCHbMLarFc36GFlo7QJCKlCFdgfIbzbgF0L/cBoy82daqkZhtBgo4QHWQ07riFaG7g9NrCDsLpJdLVWbcL+wE25WSO6DLNSAbib"
    "5Y064g2GVQ7huQHjxxW5oz7BooGZXFE1aa3XG7pl3Dn1MrbMPePOA5SsKMjguaGghl2M+NhRY4JdjvhYUQMGIsD4oB87ULxWrtbp"
    "iUhIrVQJ66YavK/VARTVLFCUcoN63GzKAbuBcy8QwXOjXqlqiEOchYoit0jfys1qjceLm2yzFNY3aY/IF0bS5oqqSEgsV3TDCsmq"
    "Y54E+o5w8RxtaLDVHKphyQyrUePs09HJq4KWBxFQGl+tQQ9lpC60irD1DSSksqZ25AcVbq6oSvhWkWNiU6gek3EoTjRZ1eGH8g79"
    "5XKbK6q8fKS/BFsDW2uWytXqRkgP/A+/4d/QlvwtNet19Y2oNzdGP3b4c42eCFb5bN7yAOkHt9HQn7EDwgpDBKBpYufSyzrSyQrQ"
    "Dqoblum04GeY6GalvukQPyB3b0xT0KzFecA3PF03gURKXTrc6ZnbrrlMRr35hliTN5lWPiv+8mQ6HsdJusM2B8TSH0+H12c30fwQ"
    "eNrfSF3LTPFzZIH7yTleW2DO8UlrNQyUJpf4Y1t/O3tFgtG8fXPm/XRheVAkdgqiVJKfgOTWxSattCfEkn+yWfL1CYgY53nGXL1n"
    "jS2KOv0rSiMbTRNg1RMOnM557v8zGHWgWHWcTfq7WQUKtlmvNPA5BMKGG7BCFI6eG0zEyhs1Vf4NbvNquc77ubmJ275RqVbxGRqq"
    "r+jnOjZUW9Hl6W91h99vSrlQ6jXlmZrdVIXfAJGohUis8G1lE3d32Nwk2lKh7QuboVKtWewW0Gvm0oTnqpWbNs+FbIfFc9VqDs+1"
    "GdYdnquOzxbPFXKXmudqhE3huWrMc1Vdlqu24bJcvGENy8XMiWG5GpsuzyVMkuK5GnWX59qouDxXtenyXIqnUjyXYuIVz9WouDxX"
    "teHyXJt1l+fabBTyXLWNmuzvKvFcm3R+AM8FcFZwPog3dJtgMgQvQiYVeGTCc5mEqQZQI+KFyopINJt14sEa5RC7hIONpZ1NxmQI"
    "TBtLP6E8Myu3QYjHbmvMyjUYE9WKsHB1Hmltk1k4WIfMohGr0CC+H/AbEgsFs1pnxNdrVToFN5uEyCp0RByZTMxGZYNYMlheFZ7n"
    "apVYsnoNoa+FzIE1ytR8bbNcQ2gBbw3i3AEYLF4pb+JuocVIHFmZ5g94gAZxPrXGZhVXKSx/wDtwZDDKCq5ihBc5sirOA/IntSae"
    "srDYyri7q406cDywn0Aqar5R1IB2OWww3PWbIROBKrE7+Eg0goR6h3Z83t2gVV5Hjg/JPXB89RAFkE3cnlS/udGkgzEsI8NIew1O"
    "+Qbu9UoNugN2t4rDh+MZsAbsVtiguazT8gbGDDhQfIbFT8Nr1GsbWB5YmzJ9r4Hwic+wVzeIkSsTz9KEbivEzdXCDeZuypvEztWr"
    "wvzUaszOsaRj2LmNDYedqzA/IewcEieLn6u53Fy9qrk5IUTM0sHablT1twpOAjF2zRBXYBXWFFJInJwynJE46bgWYDJB8kbGoLaB"
    "DGEVFscG8iKbzTIJi1UYHXQMS4TBInm9DnNQZsJVCcvI3EDtCh7RUJt49SrSswatiMqbzBQiU8OgW+qcGqtzQtbmwKpGjj5kWRh2"
    "sKvLqbm6nBpLC3WRtDcyqpyaETZIUK+KLoeVOdino8ypGVmG9ACbIus0RU+w6epyKqERlUjNsOnqcjKqHC2JidaimtHkNDOanIYI"
    "eqIU2axkNDmNjCansUCT03A1OULLqFdeRWXdgGGkGAAm2KJ1qfHKLtcFIGHzw7KMR44HBl9UPETlEVd8eFVrVcFlk7/Xq1UqXguJ"
    "qtfKFVbhhNw5LEgCe6MhMkaFm98QjhOIHuG+FrISBqgPKV0qjZpsszoBD9gg/QURuU2Y2g2SCSpItEgSCekZuUxiOaobpGyphA1i"
    "Lar1GgsBtHtBpqjy1ixXUOSBnRpWZENtEAdQ36jRc0V0N81yk8ABaBrYfrWxQTx3lVrfrDZp8DCzxFsA7eOjFJYSyUkbrP4gUgEC"
    "lIw1pJVDAlXVSFSbGYlKxNJyKBJV3ZWoqiJQVUWgqmqplziwzTAjUdVFolIiVZNFqlCTJBK2YdcQqmoiTGw2G3XikFiMqW8gnuC5"
    "Wd0gYYmmE3Y9HHlI3RtAUagynDUolm/C8tnEwyXEM24TFX7EQgIYRA8Ay2U8RjZCZAVh49dgHeFpUMG918BVUcPyUL9Bh2NYJepr"
    "UVJWFmDVRtMQBaAplXqTsA27AM9JWH8sf2zW6NzcBGpIK6sC72HcFT5ngcZWSQPQJB4C6PumVpCRaIZKxzeZ7pT808jIP1WWf1g5"
    "Cs9Nnv26KEeVTmqDtm12Rz9ACKpdNK8qIQtBn10haJ+ljSWSkBJIFslDn75ZHvr5ot0fleKbNE56CqRRdzK5Ho514M7ov6zAf0qj"
    "dfVhZUZv8D9oLz/o3rZWOIXD+ukgvtnSX0fDSZ986lbG8aCL2an52/y/5Jq0fq8Pr+IxNGp1c9lP1ll6ArSX/76olXVKP2nVE0Fr"
    "pZd6/1UVKlGhEn/6r76B9rh78uWMwpIWVjCfnUpQIB6vj7u9/nRSXI9KlLiEqroIdr5NKxiBGTb+R3BRNm/ScTdRyKavK+FkJe5O"
    "YkxRNpym/zyIr+PuFwvghVicpGO6jy9hhQJsLuwAI49ML7+qC67yNZ1wFN6v6oSrfE0naB1pdXE6TNL168VLFIuXsJAkA7DXHdWl"
    "O+DlNbHIErhOB9N+4X42G3lhLfsN+Z9Y7Txks3KG8tb65WQdY6l0B8GyImS2WgQpKkoW9pEnJaNuD30RMmiTciX5+iCyoOoUEwZ2"
    "FS6uQd/yVATwNbpZmQwHgNzinnhjFlS/WZ+cd3vD6wUd8seH0q1Md/fSAfQChuNu+TKiRQtP6CzG7i6tFQ4JZb6fdUcZUKTpEnxZ"
    "AgB7p65fdidf1tHwwYKkn8ChuS6nU6zmEDN/lk778aCnZrx0c9/kYcN51JsjrnsMMzdNY4smD2E4GzbdvuyOz4Ae04eT7uDEWw9X"
    "/sG/sC/qgnfsytOViu/nKH6m1FbhSZcrUDRnuJ2yyPorBlM0Dgux0/EEMTsakpXt1l83T1bR/EzlEdDCCGjL1pC/lL4JNA7AhANv"
    "MdiAnIq/8iSLob8KxMIZzaP1nw6lgeN/QRRawD0Avf8M+KsIf+GO/4fZ8TASMU2MJ63ZeDhMW8o2Ftn/KzgJ0TIWZjfF5KLC/B9E"
    "FkONHhOXIzgbgTCPGPjrcRezqpM5ofMGvUvI/TktPeafQa4ERj3DAvSDC7j8ANfGX3OQcUYn5Pr5gXwzs1iMAkQyCTDRMjJuM1Dq"
    "JWZW+eraXEXq0xrIVTcrIwrkAHS+K07Cwis0xceT2xC/o2slONOjLBcoH8h//CGzGi2QEdAmlp47+RLRE/mmudVWFGFqXnqZmxTD"
    "nUIRXs/7KPoVrT0GaqaPCvSYGI4mJVwmSe/DkJyz48Fp1ImU0BeJJ8p8jiLnY30F9wOIJ++0sMlC6KQ1vVFZD+DP5Ygd7VscY419"
    "DLSZJYqyOCZk9t/HZ/GNFDuQcvDu+c3oUJeP/t3zvE679I+D7vofhz7/3F7/fOj7d/kP5fWm9YGK2R/oYVYP5j4gjWWBB8JQCIHV"
    "NDXc4IZRWHogBu4txkDeW+w0jnvI00oZicWuC62W54Ga7MxYOYipNVbyZ5sHvDV3YQsuajOcY8DUmHZlIWgq4Zre+ktLYUSQ+0tZ"
    "hOTe1naQPCyBXnvTLS5ixyVZgv5x/PsUWORlLRERfdVb1goV2SET2uVzZBXf5+xtVJyLFZV6x5uTSpEuyS1DgWWWw0ZFHg4bFb8X"
    "Nip1D2xCw5dDJ4UeDp9UuBdCKXcPjOiXT1t0gAEVlgGqSy4tNE2HdGQvWE5Uai6avp8vkPRivlZD8jXFfzw6UcS6lZ73J8HjURe1"
    "nK/kuKKXQOGtmPC7eGA8+rdjBPIpZi2Px5OV9RUEZHj6SPnzxLttfrOyf3t5PBzAAaKaQP8U+xNGsx130+EYDxl6E3Xyh5N0sBLP"
    "C06ulTjTptsdpnCCAY2nJ9RLm8vA+1X1G8+7dIhNdBQMLd1hQGM2jkzpLoVLT0y+nnayi0Ha+wCICvoMcwEnLq6LeJzeUgUJo5YE"
    "cTK9hCEDacFw1gDbaf9sqp+vx/1Ufs/9FsZcbkMV032yaxiLMYKC2aYoEoNBPkBjYTNtpU+AVdAtUK2UQovT0Fbb0ZCgju7uVmMT"
    "khj7SDBYr4Pb76JpRCGV4wNBXooW9Zd9ZAsOMYQ+01iGcdwGsa07GFCPW9zj2OpR9TbeSs/RJeADdEU+9F70b/9mNbxyOZ2kKyrm"
    "/cpIv2e3oEjn1Us5UjJhpMPbp7VHmTJ9nEWEqb+ruJU8p/L4Iqe0j6EntCI6OceEzZgJAvce/D0eTMdsN9Qd9HvRIdTEMbVwW71A"
    "prk1y2xJypWZ34ZCRX5h8yPsk/lMzq2QnA6Ju6MnYdWxDB919Huu+IUdzDrH7AmXZ/4g93oco4Dypj+BUauOODTJy27SG6hXimmm"
    "h0uMcgbdWfAjeSgpANv0xAwePgf0nIOLounzT88qQXyWz3VyQOfqWLyZPw+OYxDN4o8JQZiDb5oc95Pee2fEnurJHvPaWtvLv8UQ"
    "S9DbrcfXLFJRMINVTnvsf+/ZH6QwcefnQ1hYs2Hylj89Ry2JQ8WgBUzuEEldWI3cyWNc5vEVJftFIlH6g2JWmz6Op7CvDN8eKRVP"
    "FKAGBx3GBVxYoGeqfzV2xAqHus5iZTG+6MZJhdcGokvvLrvjL+rEII8lPdQ3cfcqXjAhxV0vmywZdluOXtXJ9imKXm5PjFSeFoTI"
    "Hn8OnryYsz91JlPGPo5PcbUDv1R6HA/8llOmRMctegn/imq99o00ka31JBrdREH/IR0A3Oi5uK/EvbxgWdaexYXbRvKi+p20XW0V"
    "70arSKWl3CuBvKdtzCk+1+Ge7L6pJTymYgqc5bmBnzDgAg8HCaenySYvjBfEt+RaE7KGsbn4WeQVhISGFqeKVu/GlKUA3/aOJOWN"
    "jUuhom3KYW/BIVSbwfgBSHcen0Gy5UITFkOT7Qk9Q9M2HIlSe3z5ArVEfok78jlpAGZIoKMwyaKIDxKG7HV8+3HkgIYHsA2F0So4"
    "aJfeKe+owpVaOnhnjCcxHStBH36RvmFLNU3v2+PApef9AAkPR3V/PjnpjuJIpstFABDB1VBW4rzg+90dTAbnOXQm0d6ImBLAmVML"
    "Ljp9lh41W/FgEhNa4qVYcBdNOxaEYOIARojVa5rpMgmWDK2wv8IFNrnupycCir27PUz2ctKdxCthS8aHegI6SJP2zOh88K2yO46q"
    "1VK1+vdovnU8htdbVL+i6vNmz7fA73Ub9XqpXs+0UVVtME3Jt6EynEobeCmoW1BMT54jSJh2C9sjrrCK2ZkztSFmKk8hZKsoZot2"
    "S/4YsZeUWQ5b+VMdJg55iu2zQiodWM3ERat9XsQ/FJ6oqJJYDmcRI1LQePGpyUhwz8tlSHAZv7s7r+Bte+noV4c9D3OqxAVkcA7r"
    "IekNrzER0nNMpaEBjbiLKCjoz9dIWjyOgmrIe0l34/gSgPmKHhV3JkN4H5/mV5xiN2Jcl6jo+kAqrwJ2hvnw9qrzOKfYSxidkAIw"
    "ZWtZ5yfRt9ncZpwydQCkt9cl3gEC1voJRcAKZsNx/6yfdAc0+hZwjnQotGTTDKDZOcUQmCLvPqMljkJWXgxZccDvcNwny3SIFZck"
    "iiyoqxWbcNQV8q+UvzKmckpiWdaepQO9p0UuqdShy9q0FKb3tMkl54GhX4vatJTa97SpkPmOasyD/mRH3Vwo6W8R3EphqbhuvtSB"
    "/cinmugq9ZL+mPR/n8aveovae9zvPYmOlMQxp2uPbh/2xjOQUd8V1Ho18GZ0FSRLi6+FfLl/WFIr3fVm88CcrB19gVH40jfb8t5G"
    "o9FwnHYHeDdiM/KL3vtqL9BVD8hk5j7r7CZ4R3VaL28DZcDX+nyBv1u/XQQfYDonrbe3ti6s+zBdWPf/S7qwrqsLG4oqiVRFbdF9"
    "fYlvVfI4eQME6e11orRh3M9EKYiWlcFmUjhsgDlVoa/0kFM95MIWnlEI2xGmgUIQS0brxlGKMHoNrozBLTDkYyuZnB7chOYXE5cx"
    "wx1upd8BcaXcVyqb0Fb65Ikavv6GOjvOEzabt+y3W+nfKx3AGQPsJT6GlUCB4XkXeEJ7ZCeiZMRMrRjJf/kIJ4VqR0w4Fwf3VQUo"
    "/JYNUzFAi/Wa92EfGGfMkaUQbKkyT/Ka1MF/oCZ1YGlSp4Wa1O49mtSp0aR2/8M1qd3/fE1qb7d9EFGIpVF0GJziE/Lm5tXILmAo"
    "56VMfADCaNDl8Q3bF16kCTKl54YXRHcpMzc8MIU202OHmvnoSSRBoHA3wPwNh9QG3YHAWW5ecUio0aNWt+SeeXMQd0fpZV+V9DEq"
    "zRAbBuGgpcJxw/kXl+SyjoNxd0uaqZIANwcMg2UvEWEmOXN/d6gBM5d06vqGY+jHSk5VgZ4eo1phD37bsaEHHKA7Lrk3TG74aOtr"
    "LvVHP8PE53KAZAt0NNtPd154oNjPpX4Pc/rpSzl8MLd4WNo8SVm5XLy765ayrAsvf4HpvDsZDUfTEQ5IqUKc+9e4ZD2ZK9e4pH4G"
    "zL5gPlD4a2Vg1txTcIVdUe5N+RWIwElTRb84SlNMFj7WVVxc0r+10gxGxL+04gvfvJAypIPqio6INT/TEb0gHZAlDHM79Huu1hGh"
    "MJjJakbsrMdk6oL4MZfzwQgHA8s6uxynCS1BHJj6OdeOBAFs4xIu7hItaNFt2guUAiaVMivRei45C63krKqSM5/2rOmp4inS86Jm"
    "Q80BId8gXKFZIVdwWhKcGuyVctgC1OjxR6XJaIAiVgk3v43FtbW+EYzeoefFZDBMMXcs/yjhJ2yuE6lfIDmh9QMbHwEN4cZ2gICT"
    "HQZOqZEpXbqhLBiIaKiHQyFP9mc/yPHGB+ImAgRWV+1E/cjySvENrVzaoY4d7MJaCIdaNwcRNeyEaPYBdNnJZSvivovf1XsQzB8Z"
    "xeZ3xLkYvwXJxlAk8g1u7bf3YNcU1fgtQK3dYGBXuhe9LigPRHBoIRjOpZx0aeM2ousRjTv79NTmdHjykg7DRqnRamhgrQpFaPvB"
    "m+QwY1VxcXFf88tQYTBRKUruYA1zdJIASVznlM7r3ZOTeMLBH4qTK2hQuMI2lpfihgZn23rEOWSfeX2tRvaDcBOD1p8EM21wFWsB"
    "1Ql4V4TGD8SPCEsgQ+gmJ+dDoJnKnJFir/MlI6LTvnWED3xRZn2gF/DBukazvpq3GgPGLQlnYynAOe7By7BsHCcS+St9+r+PT5nJ"
    "yjMRhVyCu60NDqQO8VuBbs1hvw70a+bApAo9mDWZcmrHvBrCQhOVXFvLvhH5shtoIdCf2wyoreeQPBq9fncwPIsWLEIQSfl/s3lg"
    "81J+4PJhvposjQ9kZ+3Nfx53exSb1aEIys4Vms/P5h/FrLaq5Jvtqt74waJKbDZrqsjzPRVUgiaevhlfPvRFgyR/S3IlETmYNkoq"
    "t0tp0VCV0S4Gda+blLBFcDAP5bbE7wp2OzWH+cRtTEtoePoIgpMdbH2OgSercyZxEqRTNjT9ot1Iv8zmjA5NPcq7JASFQndCQ71d"
    "f97fBfYKuLFx+3KXJNLz3bZsQDsuO8C33r3klNVO+Fx2WAO0nhXVo2x6XJ4TUVDAXfIIgSpHu26gd1RGw+sraamSaUkn6ss1qXNE"
    "zYPb3aLg8cdZ4NKTdTR+xqi/N0WAS719lFQlUUewYz9c79rh6D+MYW930WRILJqBHN62YL/wbRZqOjHSPvzFqP5XsWujB0sGUz+8"
    "UWXp6SVgCR7m2dj2sY48n5awl05nRuX5VBm7QeLxDgRkWTs/PYUtJyc2zy1khZjXXyTvIYb79RUf/BR+Ao/u+fQ26GZ6pLmwO9SZ"
    "timDZ9z+XsWPB1HPR2UjPzr1feD9Yp1By+fMDnCC6Zj76HeGygB+/n3fU+nlovgGUHwky9JHHQGXOdrxuipXBA8YepVyAWb9vobC"
    "Ayl8YLeIRPFIZQpEci6tAGa6SL47kkawo0MjB7nqJsMsxsjmkeISKC7N6VaP8JrdrsCvO9HfoifuK6Brh0oTKmvKdwKug2TnpqGX"
    "QaDGaDXXvUIeqqvu7pSaN4e11XaUkOZHaZmiaIvX6Od9VNHKgfjaEyLB4daD2XXrE3zPT8JEpaGQ7JD+E6UZS9u6q060Ej0xTQ4x"
    "OQaHtYdGC9qYUwr3OUYt7xWsFhov57awpvbgtcc0pcS9YpbAGYncjHW84gjUA17i4JFIU6nmBQMbU165aBqKhBthcH7csfLxYxj5"
    "904c559Xq1IiKuuGRuMYqAPANlL5hGm4XwfFh/7oAYD4wUigWF1VzRPd0QEJUpPiHgMS7FMaXUVtVYYaMalgcojC3nCgSGJc4h+w"
    "9UcqySOnxNEqK0MmVcpfGgnnTFJJkVTttbVTlfFOuH+i1fKVaZMaCW9ce2MGascWV6Ai7JRo+rt/n4qZpSx8lU2109GkiToJyyCe"
    "QIkUux/rLEWc8CBbkrPIU2Q7Kxy2ZLiTANh8cqvv0uKqMkCa2tliFBt+vhscuF0XZnk52yXeTBl+0Pieqfj3/pPo75GTHvloF77i"
    "DrZm73Q8vHwnPIFKlRi89X7f9zPbFCPRwyZ1wTch5n82KeNOx5w8RyHvKabosFMk8eYenaRvmCTBL1V2jhHAFwNoRV5XvVjJKy3x"
    "MotVQNYVjn6qcYMba19xLpgTx3B7zu9ssPmR2/ILCaw/DySR0O0u5aDWXISzV5Jhek63GZS64J2XauZTekHus14ziZ2k+RCa76n9"
    "VDQ7Qot81IpJMc1fnPZ7a2tFlfBL5Lsr73hX92Qj7wZH1TPL2kL1g8Cx25JlkuH3iL9MxyDhUAxIpiaKrhIHL503gS+0+//qcUpa"
    "6hyTC+zOyE0qRnPGtSUevpUhbaIzpFXyGdKCCUuov3jR+xevnkXBekiZKXd2Fyy0ZYtBZ7IyxM5T9PruTtK+6gxXnCjBSnClii7L"
    "B0H5fx4W2z/5OIn3B8P0K9JCmFRvmASmI8mBJH3Qkl5zFZlycCYZ/g2cowMIp8uyckVk0nQFCssqw5dCmzzaiLOnRH3WTYZu5i/K"
    "66Cz6iJHw3VILLQOUiuJm8iRmjkNVArZSJ9R5MpAJ1EkKbs+oBhkJzYOnpv7PLI+Mqq34JkRx0Zf1lFOfOsKaHq/zYMvedFtJVNk"
    "2y2C4uU8uFgkwK1AlxJddXeJkLfniHJEkd8B9ChYizSnpbj4htIRfeh+iZOMDDfXLiGCBEoQCygQ+S2Y4fdWOmdBLgFBDs1J+21g"
    "nViOgh9KzNE/Jy7bnpRsCDpfdrxPpZPTM7+FZov7cRqkbZUTB6SqS88HDuvN8Doe73QnsadZckskI44vAa4u0eIWyV7oM68lMxDU"
    "0LhvNb27O0gsuQcxFtgv1EpyXtrSEXxQ/LJThtbd0Xl8c6i4zigDu5UKyvd9ysztqfw6cQYmllfZumoHU5yMY9hIBWWgHViosVcO"
    "KsBzzf2tl2NC99uE/mhR73E8YPtvz7eze52IJXaM1i22QTRKzjGa3j1juuKh6g2TY6EernvWZRVaMPZklfhkq7xCTbGpHrRm9070"
    "VnVCnAjqP+XFNhCz62fD6wSPu4mTE4nqFcDiNNUBOHjRSmU4OXDOW+oU65R+n8bjW+Xi4QGxTlPS9HY0WoICcLIwfgRJQ9QYB6VS"
    "qbj17cHAdNDpHBweohU7TH8vvnl76vWgP5xFOVKeD2J8ItuH5LuySKJbywatQAGGHXMpdYpmuZUeFKV6SwWt62GQPPEKRtwJW3DO"
    "AtnXiJlrywkTsE1nwtGkkQjddYxJoFnjS0kmo+ydPQtPdIPZg+5aJ8IUnGFyoXF8esSpddgogRTogcllrniZBYnOkwOVLrOvcndL"
    "XvFJzAnVnbzb9iW7HNBENEtSujBddbaIORp+z6blopLrUjKbgv0XyXJkAYGnnXUoGVWtwQvmoWS0DK2e6e28MG9pPoGRrEuVxasv"
    "1h76vWm2n8Za94mDecTF9f1B+3u960gTJjP5dt8X45KjUxQuga1/693u+BaNu7ubzTEnkuTGNYH+jJz1TMQyenjL8kCW/NmSkKvm"
    "YAWHyjgv8/0FWzmIF9F1FHZpgEYhcp9CgTgmDeX2LmdM3veLdEPMVFNGY1T9ZdV88P3kzOc2YZU83zV5qVx6WCjEXuwa7l7OzY6z"
    "XiVrr06SrF8nsUpnGmyEFaQxzvls9bG7a5JOce0Ui7zkpFOu9BfUysBlMbf1brf9a+rNsA5qDESBACjHJyiPWpy3I+BGMCGbOZle"
    "kBUbMQewjX/c95hZUcr3CbI2/Kv10/7bvRIckXDI0k827uqf3qLzyZxNul7ttuWshYapVaCMI+QbkDkAEhh30Eiwldin45tdzxe+"
    "5WLHMB/QAhJ/aoWXGytmuFmZJsoYSAAqAxO0ctqjtJJ2wSehyjiaK0zmLMSRHc4PEZElhTfASEzDeq+H9Qptz3CfzwA0AShVPJTi"
    "EWplH080/Ijb449c7d0deuEHPyxqmCHCK3/4q/aHxPJMVtvtlPJC/rKLZFijWoqlqPLv96AUTEzwkrtAc7n7usGpgs99KNeHuUo7"
    "XIjkCrRZEmOVkeKnkPlIOuNW7M/x//acftTGmTix47aGMOkp+HA1AF8g2m3JLo5DY6VZv53c3WHCyJTcyLYykNMyVUVHraQTRZgk"
    "byRzAdw0KeUS9JvDQqsmszmV5O+q9BQepTXO9jqddHHHwNm/mnTSEn6XsriZaKKPKLRrWjIPATDDpIxv9TurYYuYY3q+u1uVYeCs"
    "efzz7q4PbFhuy7E2ny6xA2mLAObapDjvthdgc0ulMm6rH9iz1+0AYlAjqODBxKX4HdiDdhQptxsQQNBgEmRWb3IdVJHR1fP5q8wn"
    "+unIlKZK3yfwXw6HiajIGXrOGk0+W63lZdKA/VBgy/KP+RbgJaH1N2bL3PElnnGtMWynHdjGcKSQ0KmBgL2NjbPXLimuWuoVjItT"
    "ASMRAbkqoNctOIf8+c87XGiH+4iC7uQ2OVkxWY/zSaBdnOORrE5K+8IKeVF1ISJXXfpqQt4Qara6191+uvILSJasz1FQo57jA8vf"
    "M+mdgKdM8a+92GRupQzHsKx1tXdddECNWlZDeL3stnMbT1pJFntYdofTwTuA7IgbLmIwQU5iiJ9PhpeXUOBs+EP3BPPL9rAQ8SKw"
    "sGHFuPigJIg+3R3/aMTzwZRY2gmmYsec3q7gzkzaPPjdfX3SHffwSvYnLa0zM8yZRTMcIg4CxHvSC/xW3Pyn4uY/F5f+ubj0YwEm"
    "py+MXOjmQbxnKxLewPr6iPTXqBGu6EoY6M/yi105NEHYuMKcpEZqt7KYO0nNkYKvrcVoSYsKw7U1N7E4Z07u8EfeuHZ2cuiF1u0R"
    "AITN8rU62Xkr7bS5GhbYjI85VjfHDHAE5JqMb1HzORGBbDZtJXYyYD6tUUtFpSJ/TgJcCZgcuq8616brxTXx+3wrftIOt4RqKTiO"
    "BuxxZRXuXk60ebjVXKYKJTNWY2HuAiAJ4RyMHs/G85XHs3gezekmUd15A08hjFmnhMtxbc28KY3wqKVbNp/zrRukwER9V+vET0LR"
    "320xdTI+JsA4LaIfRAiZgGiiYX/JUATskxkWogxO2WjBhpdtzsCLU6Sr8zDDZD9sUzo2ngLBICvv/mgulYpvL86rEZAKzSkTqKLD"
    "1PIItfT7LopL17sBW1rEOEz0JeaZjZ5HmbtDqz3m2tX3c8BT7vPLeDBChftMdK5KHUuZmFH0iq8wGMwtisZwivW649uMdGxfNjHC"
    "mdL6OWP71dWuEsuJupHaYB1wokgcIrqF6YkRv3NFBAEyu0CkBcvBQYhiPBxlb713u76eJ+fecDZSKajpyCRvdS1hKy2xA6jy39Dg"
    "oYit0G70+j8ZtX4Rjmi9RvfiShbnAoTQZxsjauiTgkHkgF52s9a11+Z7b29XDWbxdA4T1BW3TgiI4SQG/Cs1iot/jk+SgS8Djr4+"
    "wEWd09qbBYsGXCjzgjSM0OzBIYj3Ttaj4mIQQ7YY+tNuLquyW2/4pRMNvwCPwTck2vcBVS39xVcldhMp27gV3oc4A150z7g4lTQQ"
    "lbEhKlJF2BHg5pEheQKwPxkbcvIbkhPJrO2QkE+7RT1hK4j9SeCNSWKStXAta6EfEMEZG3sGoemd6EP0xOs/CX0FEP5mQ4eh1/eV"
    "mYM2nzD2Anjk0GGBAzCv8VSH131r1ci6KL7lsbNUM26VDkTtU9Lsa4AXUuDPlq5CjlCMhDVOuoMMGf75XjJ876gjDkaaHaIekxqL"
    "uadc7WdU3KsuHeKV/pi1Xnq07njwcIU5esnMR6vwI14xTvLKGb4PJeVMuvdttpLJXsE11rioMWUT2d8rYkLlY3cvd4FF16O56ytl"
    "hMhiCvy47E8mqEhaZo641AKRWupkVJPjzOef9z356bf4WqtvjPJ0GwuN8rrGbutTofbPGAaqxj7nepxYln2qFWXT11FL0tZottgw"
    "T5U1Bny6tLYQgpJ6FEr5ubZmVVYvobIU1OXuN7wy9lUnWfuqj95ssVnVVxpPiUktAoelZTj9nnI1lKWS2Ucgf71AW1LYQ6qOa1O1"
    "TMvMb1HXLLHkFEKzTekPfIiqz6wYl0I+rudZzrZqgR2VMZ/yC+2n7hsvc4ityRIzKwWlwwGne8pKJ9krspx66x2Trp9Rk9sSalB0"
    "4F7vDnuxMkO0NODWV9SOjWKQ5oAW6QgAQ4UJpbjQXxb1a+k4XBOW8Z5jz5U3ymSFvjKGcWGd+zk7HgU3ngvHw/Q8ypp7fTuofQYV"
    "9hRIc2LU8/coQ9z9/EUDWZ0VWJmVc1ZmztKyLc9SECkAE1cws9qGiPdtpqa9WabJl2R4nZCBmv8Qs7ViyzTsu9BAbTknXGwLpKyA"
    "lEnVInufDIfZ/1brm/6ftL75jzO+qZXzxjcu927Ia6HhzRKDm+Eee9AfBhPNBWQ0TycuQ6G0bgP3NWUpgNdTbPAUZuAw6BWXODWv"
    "RyMcArwbFfEnqsJlQYXzIp5FVTgrqHBUDMyVAfd2r8A1BOMaQBunsPrR1cOUvnHbc8vt7+WtjczXHemoGiwuc13YPLK18PHDXqGO"
    "8fleoY7x2bLuRMf51uHyxCD1HTp7aUZvdB+7NjLMWaECHKRWlhmRImljd+1/0XfrYsFJp3RgSh52OrZPyOrqWHH91lYekDpH82w3"
    "O/oIN2yaUorc3Q0VxVSOHGjqtNsdeVkjJoDd9hkhdSS8O3C01TEJScrNgwIMauhHd3f6Qd2o4D2RvELHchVOgzT8GG1DgBMWTem2"
    "St2zuNMp+9+HjXJHiCBuVlT6K5UdIq/E7/x5SxUC0dstwciab7HadQZAnLeGxg2AyuDLPTR2bdlvIn1ZpnsTDjaYJuO4e3JOYVCy"
    "jVnf9si3AG/hNIrmpg+rYL7UXIedVofFYSd/GthNdKLh6Sn6ZBndAyHCNGCwdDJMEkwtRTdFWMhqU4S3SA9IvTCQ29VzgM+Nr4wt"
    "qWKwuN70JFZ3pPGTVC5OWQoNyr7xMHlYxSzXbzWkPD6mZnK0MhvY0rOEmGiK+Swm0QHzW1PtBmIvW7xptJvo9fBiwnbqcCGeDC9j"
    "pgVKHy9ujJeFxRnw79sNPzjPFKDe7a7hGZVEEVvZW1++DPqYf4Y/2qtSs95xKh+Vms4d1WU3mXYHXMQPzowN5RH9tKQSf+unROnv"
    "lU2AdUEYO8Rvbc07ktVltxGwfv4tmvGdFRiQuS8nZNvmYRSzWf8S49LhOsYLNXO1fiWKdW2lkIHC/gRsG5Cm97ueKREcKSI6R1px"
    "S2YjYpxE9+N4nY6qVy2z0uV4FPFttHv7TZAZJCkjk6AIPRKRideldxtIwgPXyc2AYJNbA47WedEjfSHw9EKbYFzKYmCNvky9AmEB"
    "o3HKtfqxEv0lQpQCRl8qEVFAQH9gY4W5iiVlGQwoldY7fPMG35hSw5N0SKtQl3p7QrGV4A2antwIAK+92wJThA73ryMqtkwh07AU"
    "6o76r+PbqKXoWI/W+r60byqKRYQheL34HZovFfavSukwhOf2SUI94is4POPM7janpFc43+jeyV36wc5DkIDh8gjDS7GApRDDCg/n"
    "JIxbWymNPdpKat227d/26kUSYp6sdAoYsnz20dlfaLRwO8cozXZrUTTPXN6NY8N7Pde8TeCQzIP4MPi4Ixu2yFRAETWOYUrUGuh9"
    "wgbkmkMQC4qiUsq+y3FxM5eAy9t/gBmAl70C/MFBFpKhDF6uiy81XUiiRYNTDljmavMhA4u+bSy/2GMRgtqPlUnX6qopD/yhdeVb"
    "eAds00rr0xTvZ5w3E7wDsAJJxmSaM87ftr50UQ2FhMcdo+ccU21tJp2x3D5wL8Taj9RtmrUN8G4N/0nnjw4jy8TbivAYc4i7LGRf"
    "2zkfGg/sHWdhomfB5U060fOoZV6RBN6xdl9stpu+L8LrmZO4bWyCsvVdLseIGZlyvrZNj/0nYcuYRnzfDtfW0u/atY5OMWWyd6e2"
    "Mnf32DjLjkZwTrKDF2ZzIOVRdAkSRUKRD3Jx3lB+dhAYsUso7zDRZfBdZCFrYXRbZEWug6+wzTTurlfGnvzMtic/WmpPnuqL0CNt"
    "T+7c+152bwYSOLxWjgrNxRXrB0CoKB/G+P0g5avu/Yl3PMF5uaLLvINITP/xhvogiolswM/0oJItHeZLswPHIUUfolhs6UFVhkHN"
    "L7JEd2zPjXWx5ekXomVcfrICowUhrRB6GjrMatAMhnvkSGYrqQfuVXWBR91AsUX4lDGk4rWhSiDFLdbC2SWKlWzKmSw/6AkqXE8t"
    "h828llFdI57sBbJCi09p1TBGO4wCVwuF2iOoZDlQDJP96TH5Wh2ENHc833CmZyd8bgLLDFgdL9o6jO/aipAByW0tdTOqmUbkjJrB"
    "dA8DOL314g8wDdYeYTZm4RbZkLUl3A4UJOeNdcyyWdR/MByxRcqx3nv0Qu0bNQD1+oo7iq54mTrXkTiCdRrBokWtYEGXPu6XlaoG"
    "Ub09y9HgFGc8x4Ra6KJIA9YzCKJovyaXytqRxUFff7QQeXWNvP4IUGd7pBRzj2GzUgrrjVJY2ii3NsrlMnCQ9ruIQjdiLGg4EJCx"
    "Pz19kOsJISU3cLVqBVUjG1WXe+5CYrlHxx1aiA0utxAjmxojXDCDlVyHyNf/iTFbdzeFTH0GA+c2Bs4yGEAJb+nQscDCgTf0wLFY"
    "ZthwepI3p3Xg1GtFc12wPwisYnxkMKAoyVEBJUEhqYCS3BiP8iuhH/3d7Lix7sJxN/W4KSeLSz8KejU5P1fD4JGVSfcRCtUFGHFi"
    "qcZy6FjThn3sd69ivAHeF5rEEVWjh5CV+3dRzmGHl8/tHhsy7eTorWW3vwhrYdnsE10akHfcT7rjW8SEjUb8mJu8e0bmEEleA4XN"
    "uEQAYXkBxfhIOd6jUBhqXd3IiNHETvzy6JhzDehE0Jl0SW2ctzcLltowKvu8ghZPMJEXM2AqAl4YOpZutkxc0DGUp12qKYBzYzWC"
    "daA32npogir0R8utC1mSKwadsKolQQvwigCOPEHZv88sjy/s95Fg7Rh+5gFLFWrt7OVsqbQiUzzHqhXfCdApNyb66mR16PJ68Z5i"
    "KAdX2syBrMqttWUN6Qrvf5Ee47AcxawNsLKD4/u1ebDnOeJPACJL3vRubHFQ13vagOwDD/q5sc4I8NL/444YKMAMNL9iKTxoyS40"
    "KV2s6iiGcG5WCqyQcQxSdYFdqRVd1GzR53tFJoXiYYXGi5ZBYXdPGRQysJOYXLTYhIdS5iknmo4EocBg+sr3IvWVzYxYcK2uonVf"
    "ccm8IXNaYPxXXPevM+1V8zAEErHPEbdsRL/1km3f41DyDPQSnFv75esXxxJBk5QhbDs3S1r9J5TSyQrHsqxc3lq5WLUyxn/6ltky"
    "Df7lrm8rdTAEvmQj4mgvlmWFFQHmRkeAqeUjwNjCmiWemvAfGdtoZ1Fbtrn25IfB19m+u7dWBebv/ZjsbAuwt0A3pNG3ZBq56hs5"
    "fXH3tTLqIrd8eh4/1waumbaw9p41zQvUj7ZVvgzWnWDbFlwGrW3xrYmftsbBpNWfL5/3/kPn/YG2/IG7QOwo0jmhXQGfM5J/JL7P"
    "6+TZ/Ch7GOeWgpjOA3a61CSq1pUVPbwccj+FdOCdiTNDQVayZvRwfhUHxFEGOEI2l9hMn+fDRj3DY+28KATVobGNcg5Y1vq1FtsY"
    "LdPLuezEt5LgJduEusXLewIvs6CLyN7SCvYOUAUNy1VzWEU9YJtjWbbgf7n6dkJ3aKIAdP40QSOWUkUnyVGzJUosBz98paixEy8f"
    "/OerP7XbM7tDWcQFS1aqBCK2FupEc6OXCx24/ho+rdvrfWDuwKGpvd4672GLjTeL6g/3+BTFfJEYopjpLLP+zxjHNjoe2gBvLASY"
    "fBS/WV57CDAvUxeW+kJYyLkyDwrTx2BUiMAH7KmvAfb5TQbazYXQStTtvAiX9RtJDyrlPyV1KFFzOE3RUKn3FWKHNZjr5Zv97OuO"
    "9kPbItXEgeMEDlHmskhZlH4pNhfdLrZZvCi2WdzdWxJSba8oCve7jH80xp8VA8aMzaIb9IwN/rYw5xp9Xhme6hBmKppail6+FM6Y"
    "QkNoM0AMe9tPprG4CSfK4NFxEHajhvTbLASN0e6R+w66bZFMEhKH0Xqx+30bOIUOrT9JgVXqT16g8W7sdf1OF4/pdp+aGpqmtihv"
    "tTfUrGi5pZtGXhPWKYDAZQIK2Y8/iROSiPsYJ6MUJyCixRPPP+TIHQdxkB6idCl5IFTsEyic2oXduGkH5UMNR7PZbD3BN/66l+Y+"
    "4Bsy2UfzAH0Hq8vA19b2WEVL9WaiZ9UxtKoBAMLAUCJAXzu9ZDDn+8BlByoQCZqr0oVrzobuIDzkZEtl39ypinidc+lzwzjpC1eO"
    "4UTWXCpqgQ6/Ke8XX8TSZdxb7/RMmIK4Vzphn6+xJzoTkrwXXHl9WaAqEGWLns4iT8fYN75628iTxgvkGuO1hz7sGSJLB87K49mT"
    "GDAeOW59F4XA8a01zH5WhaEc6mPnNl5FD8RrdtFk0F5IfL6fziBGfSzUou26lwWA62QoOgR1tcjct25lMcv91xyoS7UYCgqO67Vc"
    "d5RxUMiH8mSRZbGgwtrJvQIMKR3jYVYoUgoAOSWIPJsO8IR4AQQcdfggH6KCe30Q5SzTzad58Cp7FsDHUReN99/sqWihhh8N3hce"
    "D38UGferrri1H7SdvADHId1MpxLM7Zc9FZF0PIVzM3hpOoRC6BAKhT46L/v46lfnldzH/1gI7WvdBVJt6ON3py69nAc/uS9pKufB"
    "b0VHJwX/nQefClB5hkFLClv6uciT9HEWkVCBfBZyAUveZdwOpOCK+DNAkfRd3k0CSnUnyDAk7xazAON3C8KmYPXrc4z12y+qrpiR"
    "7jt7vNOkNzRX/PNg+G5RFNnJuwKMnLwrmsLBO5sf+TgB0l7MjqD9sGcbGFLC7vGtyvlDkUb30+EYWsCt/yqNL8VbCxPAD4eo9ZmQ"
    "OSSyaScYTE7qrobz+U/o3IlmSNik09ZkYVtB3IGmkHL40t5czF2Ng8cURwSHP2XLW1vzTPAo9Y2omTbgLvu2i4dTQoVA27D8cZUb"
    "tm0YpYMXqUhOyqzd+HsAOZig8gbFTiSGp6fRoXLW8MSkNjbGuQwGUpoSRWBBHsTyE1mNrxVS7u7gNy4U+I3uItAenHrIdr1K0kGJ"
    "GY0Xw/FlN/VUfohgBtxJ/3J6+UJc5p71z5BvCueU8BaLWglT4n+EZf8p/H++cgbHArEmFOZfH8zAqNCVpvf03//2NIgi0dJPiWPC"
    "IFvEzAyvHa+VFKPKaczhaPA6tcBv4GwMpzZyPHoh9swixYE+gzYQyriK57QFufdEf9Y/MMAu/hDgfX9df0qzn/ynjXot3kB+bHRW"
    "SvvoH6Aj+nEYVUzKcR4nULOHHvwzLNQaoycChdFRn2/jCYw7W0RNEnaKwcpy0wQVWhEl9u2fAPMFXP05pfkbA5XVU5WyV8GYTAVP"
    "Fec4AS4DEXsKDObkHFDb0ctKv/JbdknxvbQK8reP8t43CxOD+o7i3rZyx8QEbGmng37FIzLBN4b07paiDe+INHai7JHvx5YbBkXz"
    "wBBPBRvs7q4X44X9yuggPRQacKk4dG90IH5ZbYAECtCP4Fx9V59LB+yVAr9okbVVmuGOrLqWlFTlZC2eWeaTahNw9OUHBZ7O+mwp"
    "6YQi5WrHrXx86YIuKLBhuRWC9KLjVn9dxbu7BwWSTpYHksb4ejlyhooKpmiLI6jm+369LDyribhanE1nYbQEkxvn/2HvXbcUVbZG"
    "wf/9FFV16quReTRT8W6unStbURRFvF/rVJcoCCgCAoqYlWP06GfoNzh/+ynOo5wn6Yjgjph12evr7h9de4+VEgQRMyLmnDFjxry8"
    "H3gAnvWS3x0iCnMsBw0/BrkVlKYtGEHPOZALdkrqcHJ6Oeh0Lv/9nAb//ddznsteOcKAk7zuugB+/A5DkTqRnV1T3V8ACa6CD9A1"
    "qr+8uva49h2RXZ608d05lAtORE9wdJUdh/5X+zTjYZkdZ+IN+l6CYfj70bO9OjbV04oB8AM67viRIdGL77A2kMyOso0mcFwxgRMD"
    "xteWG4LTm6C73+4U8DNFgpkBvH7tGYC6rbUClftvQXvvlR1NFn37/Iqit6LfyBr4iXu7an+Pgl06b23T7bPvkTWMFzJ8F1TE71zr"
    "KMf71EcQDrp3nD2FtL/rw2jn3sPzx/QVWPCVPeaz6yh3/+awZ/9LV/3wigLmgEbPrgMYupG1WSwOKSOc2ywcADVKkWBT8DUVkMFp"
    "0TuJjh9bwJN8w+lA7OkynOhvjnKCPLnKCUmEly4b6agLyIgpaM2GPl1emwL4ZkqEf4S0+4H7dc2Lceybt35CNk+ubSmKleBLaeGj"
    "s2uuqvyZueq1sXvgQBpv3bWK2mY9OI2FTVgj2gd/EDbNhKN2kI7pVd2Ctldoql0XVWdxwl8Hwxk5V1Ahm4VwAKOX2ODiWHxkcTB+"
    "22pveXX55Oq5otna/XOyq6jwQ7073zx/NNw8N2F9tOFZ/PVO8GaceO8qKhkXz8RHJ41bc260az/u98DGOqRHs+uBgcIb9/Ak2V8x"
    "P7V69+SiW2ElAh0ZShXxXsZzPw9mk/EjPpWSFH0f0kddoqQSCAWejIanMuLya1Xp9+KcBSLOMxrAKORi7YWct1FhdPcVruwapZ18"
    "haxLRhnoXQHRLkGXAp9cVYgdhD5gtNWkA7lVwxFppkiz6PggBFesYb9wNGFOIqtlonYHHWACjyxMZgE4kjuv12ec99ZR2b2bDcie"
    "dqed5Cv/tL472gHLvVVE+q4MvAK6npWX27mCliIrcb/Qt9NSBGtCXTmniOu+Mm5fP4uA4vS1FjjotvazdEfZXyWCIOIaVUdeCrX+"
    "7mq5F32537w89ycOuuCJOlJMuEGUHCxFdSDTQlv1tVkQLEfBH213CD+dwmv3rlq5BxC6uzWq8v5l2/fftaNxgX7fespDg48BNPBO"
    "bx/j0NCd0nz87HHmvSfh2dGpX6J0YMc4iJaCiZYUBiJDbCtXq+BI25HFsGXUwGSf0CXElWbb6So8UXFme2Bu424/oPCbNKJZUuC8"
    "OLK5vwtC9aQbtAy8+eTUCKTReLXzM0ooLjtMvxi31nbCq2AiigNgg1Eq0V1TP6cTx4zVO1bGGENM7jxG6NezE1SErqXDjNEl3Pjg"
    "jDaALRrec8RTZwQEP/IlVIy4QlwgNBMKOPKLMT5vsF1HQRDHeZ2hGuFIaIFIn3EQGo+CYsKBobR3kShe8+jGa+fGi4vRGDHsyDiY"
    "ESPB7qG8b1++OpCiE0e8JMuHlvP35Fn7uApF82uvHJfRKygfVJzZVrAGAYXPAD4GCEPnbsrG8vPfV2N9ln8qML+TZwdS91VHrtlK"
    "EM/QRvf7mAa2J5IFUqO4EaNblJeZMIYWbjiNzBw5vne+wgH7nB9xUAUH8DT0GnrKc9nkJ/DjwY2s9sAiPfEnIDV8OurcA0rXBAj3"
    "E/Sr0Y+bjXh+WkIl8c11RERztYyiDOCB6QxsfYkNlZ9oGbBg5IwbXUlbZ+cqWaLx/VxHZlsX/UuoYTd4GzVCKOAAjZDB8RW+gRa+"
    "Vc41L/D424K+jthrv+nDNz7H8bkpgBsdyEIBYOmrUMe/FdTYafKaqYVsim6Je+7mxfUCIzN6aGSK6kqiy9Auzui7MZKNniKl6Jji"
    "H8J/LQT5lXzlRr2/1b3J6BUWnCTtEAlPkVeulOgfIp//tjyMARihqhKi0QDOBISA67vv/+ShyMY7g5GNnw0HMJ7vvz2kb5FjY5sO"
    "xmC+2uRRcj4JFML7H/uG4WPwnuI+iM5yz45nDKqHhgoLIgPkdHDsYjwPIx9bY2FA8l6wJ60X2WMRtdEcx3IxWy2WTk7ogHFCxDVj"
    "DlUmJ1EXYayxjx9dF0HAFewgRPAuPrIHwuV0ExzA9IgoTNlHW3p1NXSsxvC8/QKe2yzw49UUWXgpBPP05TNp9Zz8sGak9R2WTp/M"
    "Dw8fshn1fH8PiN1ngA5cMPed6xH2ChV+4c6uFIAAZyobsJE3RRbqfi4VaOdjm8z+kpFJjHedH5jERfXweOFlKTprwDnz1TiuA14Q"
    "vrgg+C7SBqgueLJwegkzIxbiRwz5gBcOrOGDhQtq9BgXPjtw3DvHhjjN3DBOeyL2vDC613omhD92Ggx0sz8Mhu2yFQUuGgIsvfcz"
    "3R0BLEwvTi/jNhF/6RC8tQ2qbiTR09rcOppwv3U0UVwecLUz6j1bmF7f4W704Huki0mgE8j6jnP3TFD2/MHLyh7W1gW/TnDBXfY+"
    "aH/kmBytezET3+Y41UvjHpvbwCG6pZ0aGwmULpUjZuqRVuQIHjJaCjaOQvb1ri1aP6gnQO1sL9bWdePYnoBdXX3PDGXfi4m6ORE5"
    "84bNqncj4F/egklEMeq9a857LyLnx4+zR9XeAf7IXMO/UNCiuVaOPYhu9W3y1RQ4zc9DtnwLpMb0NYnqCciwUIZ7/QR+6mD6P7kO"
    "Hm+hQBksavewjTvAIz04TOsXMLWkA4pL9SlI/WrA5ixphDW7Pdo9xoYi/7sd+KH/jZuXKNi1WIcCC6BQO/Aud40s/W5beMZ5wNh6"
    "3tuZYW6Ys3vODM5lDPRmcNfDY43dO6pz/w/7fYVMDb23jt2ffzcRUim6GLTpJX99H/v/2mBhBTlu61DRqMwt3AmlXkRky7iZHYQ4"
    "fqIbkKHwvWjYXxi6uGfbS4IqD2rIVlKHTgWnWPszyy+F3xmixEGrvFW4GJHlW/Lceyc9xLAXzcmOwxJngZNmLz6zOjgfwkE9mHBc"
    "o+AX9ZgvUE1ofFeLHU33PQB3VwBWeq79pBOi3O16Gx6+xEE1didc+1uSjjPz670HAhFpF5qtRhYA2qvGtTt4r93LdbvVuEYm7zXS"
    "jI5vfN3q9BraRvSzdlzPh/d6bkXtNNEyi9BKNX7nnF0t5eLWUvbjlvJzFGaOiIHZIOJwTCauPVQQXsIU0RrxXgIVItIrQ1xNsEJc"
    "TbAe/WwdB6xExBg5HwmfJQi2WTJ7E0I0CNvGeUPEGM4aUCh4MDUGmgirYTjt6EZAVCECBCwQt01z+WDF78RVFHMflhPhWhJHLIct"
    "IpRyBhTrsULRv2c5q4I9R2Ghidsymw7bzaKCN9ve1bMrEeFPOwC5V6bAnzDwlw5/rEPArH8HGLiGCtj2blnxQlgk2EcRRpC2Y9JA"
    "BwR06Z3Uj6qqaAYMyrNiJJib56jxYOpOImgcmrAzkrjSnJQwBsdAfGSfvzp6N2ikv1Z0aGb+dek0BV0DvDLUGlTUeiWBBqGEbZd/"
    "88e+AWP3zWPgwsJElWjC3Vt/x3BHff767a+mZrtkgQeYW9Wpj+IBw4st+0OUxMoxy3GDoT9zSS+fvK1RQwZzYI/12qmf7fHA1tzk"
    "JOBY71zLP78q4Nj4qOxQVF8nKDiKSAcbeoOKYDAW0F7DBlGF1qB1Zi0g6RvarvqD3kPMNDzAnPB2z0U3sQo6QP/1czNsBzFhtkPH"
    "+BqC4HUj3HnGWc8fnR+/0KqLYZ638pWFt9cDD3rwpirtTRWSkiKr+p1zpjd2cb97VtmAoJLLMvyPBdPvJZdQ9faeZTZq3ZmKoG32"
    "CdkM/v2McdmX5edXlXfsF++4FCgCMtbbhx2/fAq9ChpZ39vm1VYoMic0CiGdMJvLD0vfsPBf6RcPNBTVBeDEk2d36VplGnYycK8E"
    "Bv98A6IWsoFxMsoEFOYqjOUqc5Yf0R/GLIDJDcCSPy3/5//+fy6TZ9/829GsDwMQX1tjuyVJzX8pQzZDgG/nYMrvoMQKnjvQuNl9"
    "sC217+FPaBd9B5nctQW24b//+1mLN8UW3+6fwvUekE33bcts8d+1zE4ih7/QEJFPfKjk5RWsF0Q5v5W3K5Nu8c2PPh1YE3nNvfwK"
    "hNCSHeoIlzD0Otyyvfa9pdDccJmwUbRmMCU4jFsd74D4yCeh/t8FyvN0TMNB+3hjctxOf3n5+s0zCoYqFpXRoHsg1ARwdhyqf8T+"
    "PYJ090mNs6FH/bkALFHqTEjFb08fPr8GSe+RR7QXNgROmmF/XGdsyNmWQ6bV+otrpeW4qH7zzHThW48KCwHLaDvbOzxx94aumdEb"
    "Uo2EPirc35h6z/ngBbmVOro+jy0phgDjCSb5J9k518vc0dDgvvoNxbgWr9DJBCyGe3HxAD09OnttIlxq7922fMFwsbPjNOelwXix"
    "rSOlhN+m004CKgH9zfrHj/Q9VHskFTs0MZhl9D6UeuSGEbSXG8vUfWYWYBKOvaFxy7Xkv94Z4FPwZKr3YIqddGt6OEbyrT6hhPG7"
    "vcJv/I7WXMDa/Lb3S1Jy6kmKCW9OEIm5KbROUD/KbQxogoNe/Au5nthIAc7X+hQULu+fNrxbiGotkyEyQGVB9ZocVa8JPV8lxveC"
    "ER+/+2rR4A4Zje0ZY4fgGnC6pgbf/ymjWUcrEdLKuCJM/HXw/hesaH3t8wnppcPRIe2xI266tFmwFz/yzctnhurAwIik7F3ui1c2"
    "npZnGxhjeyu6hqv/TLJm5z4GLDwU9T111eZ9VZXyB0EbIort0M1ZfJLsTEANaznKOajuRB3G6TqZM8oR6QApeSpO91ASHLi9FjCl"
    "DNRvWncnb0d0rwFe7UmTeKhCRn1iBV+ZGBmZjeQ/he71Sv3qno+uYbO132BRbOHOBc9xp/KBiyyAf1F78qwQ/gTEQcTM/hpAdMZy"
    "wXP4ogtlmDu+rO6CLxwvwf/0IazcWXY7Bxz0xTbN8ffHmIGhJHuRaQdl7wEcyjv4p3D7uMt7+OEemK+hRBsuwl6RC+dVfPXNX96e"
    "IGq7FUJYDc7oq6fQRv9yF9734VoFls4vdK2eocSYCOHs2qhAFoN8AwNbjAtA6o7hXMNL7P6/Yun0fZQ7asq+pazQifkG0SVhJNh/"
    "Y3It62eYrQuctIEz60nJsOAlyCVQCZAf75+Cs31reu3vV5Gv7TVJREqPMiDxNce+OAaVjg2/w7Ccl8tk/EdIiA+NReY4VkehG/Zg"
    "7/pPnNbmKUJtG0YEO7LDsF7ccELvUp79SZQjOw3x1+gbmhu7I9qfmhAAgXl2ym0eZZPMEsBlT/cqrtp97LxFiD48fYE4qavA5vUa"
    "vGbzBCZbSnMv5zqnyM51fbVncLFbJhbYMoM6U0fos7Wa4j7eUC8ETQW8hlnLnqCDscsAYCteosHTXeBol0RpgG55WCZhYmfn91/Q"
    "1zLO6CDUS9CuwLeKRgYImpGMjMyVjRAMP344uUcChmgmFNh8aF9CoKNjb9C4IHBNDHuAGXHBcUsxYZAcxYQOJrYFjsDdvQrI1+0p"
    "2HggCJBfmnIXDPG8pzSY2f9YvsVPhPNNMpg1BUyDa11hBLrfSNwZgMUnYYxzHvHap7NvZfHyAnYi7e7hwVO83y+9WIc/Pxc72xyW"
    "SY56vj0EONb6c1W3TTTAvITkYEMQ3ZMHzC1lL5tjwFhK4sHWSslhzzWxqEXPEnB1/eDRYVtK+ME5+oGsTBGqB+LkxNtTJN8hSNfe"
    "WfdJcuaRJFJW2+GQzLBfW2wTiI6Sr+ZTVMBMeomU7fO/3QjYDV30jZK8GetF9xPC1zn+18j+zwGOxWHz2rPLtw5ClkmfvGumTyiF"
    "u8zF4HUYWVHkTYirJxtFAwhaCaPUrudZOG17vwifFAYwyD+CM7pbxoDuCYSdXoA4HDOjOKcyGiKuPYyAC1mYBlOh+UeMA7EN29go"
    "Eh4pSBXda6oABAn9Zd6nCi800nvEYSiqTxaC9dOdyh0E+M5F3biQV733YU7e3i9Aw1FWGfCjCe4Vtu1C1CotwC/ftUYjblqjkbZC"
    "BOJPEDX8yzAPr22bzeDaAui/pr898nB53T0BAZG7D3ZOBfAlsv5/xOJ0BQV0dZbx4HE3fWe9s4bwq/cWcXC9iEPU0c/WEDb8/8gi"
    "XqKLWHWT3Hvp7VFIk1Bye1Tip7Z3zpFrTTTENdgMgDiKYLqZjz4IQBUCIEFB5Z9ZRyj9Vy1/KSvhY/v1Wn4MHRx+/Ag/B1l70Eh6"
    "El1ZVJv23YB9Zc47q4xOQbYG/eXrt1syXjBCYWDFf4Ubd+96w3tPve6uSDPIlMe9Gyx5Gk/FoSZjSfnuegYRSbtH3BBZg72q0QuR"
    "dtuxZfWpO8ndjDkccLNb3XFBR+6om91volbIGgYGs7jGNaSwD8hExpWSIqRxReqCd5iJo3IIIkAroGWe9/5NicYF15ZPQgjJwoiT"
    "MN5kU767BCSTEC4dYdbSiEgSgh28D8onV7oZ95LYlliin4bElwXA0K9fx0oyWuvv9DcYzxu5foEFnPlyTb93Y1x2JE17ZL5M84sE"
    "BAft0c3nGGHm1ijDtMQRLk5fDTte3IlWi1EUubJP8lof9eNHuAwZj/yMesJdGt9ukFEyj2WcxUGuzEFDk2i/gXfBhXOPNwYRN4HO"
    "+Qbd+9YiyjZbdfGvsO735aqJoWKHqX+K+9pJlR5uI6J1s1tBlxfuvYRLe2jd3fCr8tUIFE13Y1x4ncOy98QEjbg+tSFm8VM5ATX9"
    "e4LCL2I9ypfho75IBLCZIbwt48ePKxV9FPcVInYf8fp4VxxEA4wXCAGb0InQzrEmYnaOX0F9R4v7033jW/hccYgKATaLDUgBf7bV"
    "OPtJ2xNdPA1hfGwf13DoLRnO+noJxJSJjSaDbBOF61Ay+q1QMp4xo3czJrwF3eXtafBM5TyJ0rsr038noAzk8BIRTX0aiONyQ8/p"
    "KDgDnPX6NitAn0G95ztpAWKZZQRvkrGbecjj3Wvk+u6CjugZfmqD4DrdX4UUiIgY9uZn+4UAGnFbctYpKt7a1v+E4yu9u3cT3Uc/"
    "c806JDclSuhWNWhJi5x74v0xtvAePOQF6F6mSY8scmJMhu1tkXnq+oG1w72+rhTWgu3BK2YGBhtzMGQYiT7jkaHjdeQQ4HvdO9zs"
    "RifuhKpEKGxOSMdxmzuivfElJk3wdUzgEGd21G3XwihorslJKgQ3TigJ7tIou+CeCHuG+tEv7Ux/8NrB90tF8TPtu4j3QufYN/Pv"
    "ufUHrzXCQTN//EgnoS+hyt+7VoF2GjTMddGDKdLuf5dQ0UcBKomEBgqF4XC8VMKEIBChcEeRvD9/gleuavEmat0MjRLZ6ANoE9rp"
    "934Ue1uf/Z56wGG/6Tg1AVw3Lhw80xHLQuvkcFU4NQkU9cBWa/NE7JHr1yfKD1kZxwFs2/ubDCAWk3z4/gwgWyr7I3iUIPYiE9Iw"
    "sisOiAjCP2dajhHCn0AYIpa4zkNunIEcuAGRiL0WZZtBaSCQJ/fmRvS3dCtbU/o3A045qnxFCyZg8aPfOf0knjPpd3OAJt/bMP+d"
    "bFI2fI6Btu9QrYQiYjlCnmvG7Q6Df98k6fK7SaN8J+zrbKSRjepEXIXWcCo+KrsXGFPo90JtMD9NMx+JrRA6hToi5bcYH8dv99ep"
    "DH/XQdTZ2rzQVtdbr/vqPuolExMF0vG0dNwMV77zDSvxD3D80NUv7JKzETkJOfmBYpRJGFZFmYZBIR7bghlyz8EVeSNq+xpg4Qof"
    "cNHxvAkM+ASElUHljq44mX6RIaCbc8axgOyC1/ePqGsf9+e+eZ4b58Gu5zzFxHqAb9GUhOM42OgOhvHJnvdoVIfcu1EdoBM592Af"
    "cB5UTVHBeeWdJB8f00mkaeFY+DNGaebmPUYZBu9jw0YYvxEJwiV7OHZZeXmJD/8QC29wXpw0zAFmlvEyYw0q93d2B6ElfCepWDiP"
    "NLQit9EI/vI5FWzR4vQIzEoIXruWbdLim7bYV7fhAdjIGAjq8jGAVhObD2ji/i4uvpzbXTimxfV5B+wx9hCQB54/oit3RjCPQzR6"
    "N5jGSr/jQogehOjLl+Ak+6/voQeWBmAD4r3rLA/2wpW9FyJsdzibn82bCNoMD/2aqNXIfQyPbPjYIOUnAznPo+DcCvHk7XvRD565"
    "SEAyH5BAeSgIya0M6NGE7ii99S+EfwhT7lUgiAD/Xnv8+wa/cRm0z2U+OUjnE/g7KP3JJp5w3dsUa6N6CP9vsQqHD4OFyIZoFm60"
    "cYzkGqlhQvFrpIqfXlfdFBo7fA4MD4WxtJPaRSccbk8jAgLZGnZpaIEDhEP0U0eBz8WNhe7s6gT0eRwRd00BerQZMDsJKO7D5AdX"
    "pTUC5USARAwDuo016WkbqvPovvp+1AD+u08jJy2Tm54J6g0DUU7vk59D7cLNhFmjdFwo2B6Drv8UXoSRUgxOBZ8CPmAqMHKusWGe"
    "XLfCq5aTMIa3ZLdhfwB/axyP3DR5CdoqA64Cw5wvIRhde3yro24FG5U5E4X9g6n3CNcftWLXhYmk7CBGAK50MA4+mBmwLTtuFJHk"
    "Cogd+clG/lsq8RmlG3kD8taHDuG4pESWq3//8fk5UlYnvDsz2v2s/6iDg+E6mNr+86M/tx8BYP1HuD5fvng/Qd0a8RhY2Ptkz22P"
    "Jlx/xuVTTNvQPcNdfmicWUXFKMdGqHzEIc26P0EE4TsaQ38igG7ecKAXFvf2lwGBA7QGFsF99QyqAbJxsm3Y2Yjv+klUClcQkRX8"
    "APxECwd/15zi8BjfG/9L4BGhb3A4KJ6vLTKCaigz9W+0bAvYHvZ780ESd/evt7/78iUC0stdzLDgCw8o2BNgvW614BDAfqfr9pL4"
    "1b2kJD5QFAQqrgF4rAlPgU92bc+FFdYCRItw5sn2lIVmu0kwwic0TldYCHQ5gF1+9npEaAbOxbIMFtzu8fOvdmijaLDxC4FS+by+"
    "eV28erzB6wziFGgXerUk4e/vytG4ets9wrkD0wiA8F/az/YkfuW+vbx4b9AKWTcGgAjK7QpGlvMpFqYdCgwQNfYd7OXCMulaeCBH"
    "zeAoq2iU968euXLJAMl++fLRb/7LF+PLFzjl/tcTuACAfCAfhO7J3Zjld0nA3iiX9yFy86FF1b4f7UpBCJuwD5ezAIB23s879yfs"
    "2m9JZ2C+C2dh3XFd4RE4g5vfwSEfiNb9R+93EgVp+o6AAeWBJ+fNntFgug73lf2YtPVX32EWFomxwNtwQVIXQAdrRjMgPO5vO1ni"
    "97UiHfeyDt8En5NAPuIh6T1Bjgf6cx7f0DnVLUW/35Jux3ah8wSKNYhFbil6eEPC3fcdx6nfYawy2G+kBGxeJsA5xYSbNfRRBYhm"
    "Oz768w2EkBx0PPWXaQyXKbCc9vEFLCSjW/L6g1dvCus5e13HX1XGZETjwwQcZm2pzsYgOBQY996NEmj4/NV7hdICJ4GMF3kBCmXF"
    "LYOjq7OiwxUcUe4j2IVfPmJPdxB2FGDMg7JBOLlpwIkAjAfRHFy3E4x9gV7MHuHvZ87+A987CL988X/CIFNQFrFrfQzWug/OpuN/"
    "+AY2uleIqJy9my09NOYcNAZlPmv0MZi7gcFcEIPtsAooqWwQef0MUNA/O4Tl4YpvUTTnImgOgFspkNv46M756A76AWQaxnkujPOg"
    "SuYlA+R9H/cB0wJf2ZEy4S+UvQb8hbH7UXp1bukMyfnkx4/XN49G7K/XRy24o6DqqIJdFz07Q3h59QfnktHTq1sHURCoYpOVW+BX"
    "AB19hzLiy6v768kvRNVM8QJQE4hWYO7Qzyty5KLkiObtDd5a2F98+dKGPJiTdO4DwEMgU8NzGcQtg1mhm5wrjIxgss1kv9sXPst7"
    "j39jHv9G6j3OZtNQmAvy86M6QinjUCo1J85H2zsuOcFx60gpGOD1sEUYP8RukoObio5k6+Vf7kh8AP2dywPSgQgKz7CGE1T/8yOc"
    "WbiRwH3JjsZvV4CbI3wPjwTP7pHg86NzWIBfROUGuKdyrL1XR3ddIBp9tpu2e4Afb5hnvzvwBFu0e1ujnEjR9jl4q4TDVzfad2be"
    "n1IfLlImHP8g71Nb7XofM3tQsPHmDa58gNEkuSuxHIo37rRw7i/Ee4KSxUe4AO4I4e8fPz5yjoDzshTl5ZM/yT4KRYUylIDPK5QV"
    "A/fKYfhC6+l6+J5jlDf0K92zyz3Ri7uwLPwMD1cuN0USaFD+DQsqAVhc9PQQFXT/nsD9awJ2QMIODtSDwB2r/5Wzym+BiDCQ+l8r"
    "BEpM/OPHXbVyt4Q/H/ijiHArfN6pEEnn5Jn2Tp6Bfe6A9jmnNTAM5xfEFH8vt/nOMokSz9i86MsXXyKDAlqgyRaEbzy8s7Nncc/T"
    "4V2D8KIE+K1qHMNa8KT8B0eu+CPW061jy/VZ1BZkk0GFhMtdXY4a4qA/foDSa75q8+IkEo44wJTRqXweiNq1gnHUYiKcobTGurZG"
    "4cgWMZG5Vg/grWvuqTGsqKDI8/Fe/047/dh2FBVeFHx+5x1HOvcNYLJhRDbSjmcG6eHBueJwuxVP0DRBVSQRGWXIZEzwMdv8TCPj"
    "4rqJZEy4wZWdtBiIpmTsfYgSX6y7YKMlfYCHM5gBOL6y5AzKrmsrdtCkHcnAarmAsPGNbMi4SXS+UcHL+Fnak8/E8C4YRg1hY1VS"
    "oGI6Ekjtq2OD4ymdbOX8smE/vrk2OuDAJMqM9xpHT2/fwgHYwBk2oAF7dVVlnx+RusvXdUG+bv90dV6fH+0fiO26L8G26URig2E5"
    "0Da7g+Lucb0GxLZ08sIjlvXi/PVN2vwYG2LUhHFOuJr0WeBWWVs/Ho5Qd+D6UXg69QURsG7sO3eU43pMxrr+vXv++4TU3A8i6xCM"
    "Lw/aa4KeH+zKS8cFPiA0xmvaxYCmvUrc3wU+gMeJ+NAaMPTFVwzd5vgXAzYmhwB7Sy497+XkAxYygPz8Z4O2md97I3Zq3BouFh6u"
    "U/tnY83eGqujdUkukSrwAy4pR9YZK/gyMBLEdt3JiM+Z4zTOkSEMgizNQx7nqijCq/yrIdHW16/0uzsoz6OLUIpAt0Hgj10WvQEK"
    "XdvA3sIXNmAEoPDmfPp3enbFZ9//Y/UAnlH0ViBXK9FMMk3h3t+6nPsDqEpH5wl4qQ0zBT+hpNsO72Y5fa2JK2fPCDF3N9lI944k"
    "7n/lwsdPAHLzjvGngYTh6hj2/hwyf0Bl75s8aL8dhQVeTnnswyCjWR418FQj7pHQde/dK8ESKJmE4QvOXPDmPxQR9co7MWAZ2r37"
    "fG/L0QCpxWgeEZkM8DbNR2ZbGnY4eMDyOpqGEbTtyfDBLwPHm5/nFwmuk/25s1J+VOcBEXdv+6tZP9wLk+uOIJz2IcztS/ya86jk"
    "gpisq/2Mu/KGV4ihGbaPJd4kOzwgHAl39eAcXjxWAHiAHH/ZK0bXxD6gOSoqd12cCWGCqxlyJHEOhXAfDqwI4iQhBgJGYm/Wt1hI"
    "3psctypgItdcIJ6svwUdHhQyyEj16Dg9QcIHV+zEgOuJErcgLgQh9mSL8G4VkOmSGw4wLQZgAjQdsZOiPuwZfYesR/5opOvQSKXo"
    "SG3RJxrDKzpOu9bNURaDo7TrPvshv4x/P9jXlSj702EfST/Qe5hbx9MhutYImm+4GObo0H/8+Bhaw/czkjhs2LciDJBi5h1SBAJE"
    "yGID8gDULdLEvCI1G3pGWrY4Ew0HGPZnxOhraN4nSNjRzXUvBdcdqaeuyFHmHqDF+gNSFP3Cum1+Y93sy6PrdYN93ba3iUsc89sp"
    "bXyGXQ5TuK+Ci7NRQpWMDROx9A6bg97eMOx7tFD3WDq8YbhV4mw/Xaz0JlslnS3aQDent4LTaTYOhiUG56vbYkHIojySadrOnBe0"
    "OnTQ8gxD+O1hrgopNAZP1nDs3ZEpx9evy+/f9bWicqSXvPT0wJbKpRzGlZffQL9CzNE84sEqXh5sQeMtyUfP+OYF5kEgI8HLUekp"
    "9tBvkc9hIkd1V05pNlR6dkpzodKhU5oPleJ+b+blgVUMT08hiCzLyVCY1I6Qwkzn+0JMkPQR+VxI1q+O6PBUPnUUX7EJYCoEYkAf"
    "n5+xHz9ozxxBDr8GEkg+YMmg3Xlhqb98uXPzVhwIaBr05HySeMYC6jTR1vbBF3+nv3x5eHAefINN5t5PwhJOw9W9qwARFir0buTh"
    "AutsW049Qi9eWBk1DblH0F7TT86V/ufNLyEM+k5EDi3XpqCFd01BIziLFivGJovxzq2vyFPnAJjCR+yX8nu5S/Qeb/plCdcf6jW5"
    "oXKPhzEBxYIH7TXzSjJfXT1C2NUTGT6q4MCmuSz34Xdkfgjo6ipPmYsfAKfT1wNYOWaWDhP+rexkciiiKOzdvvHzIrrBItm+6fX3"
    "NSPOeh6CgmrGp1LTfiajJGON8QRfRISg2LwR+h37s5LAHH/jEem4MYVnLHzM48nYxGaw8bSfVivUAhZu4TsSCvak62N9CoOI3Wgl"
    "E27Fug1H5kYL2XALq9stZG+0kAu3cL7dQo7xj1Sx71d+F6E2h3abMF6A58cNYwJctZAP9BBfYfWzCuug63gclHkPSE/KwMnrIAYj"
    "EgYGCYVlcAOywZts7gEDcxdg0y5LyPju9mGEQQkOaSKU9NEMo0nA3u6mw9sfWvLelkawPIfl0pkskkZqAQU8BwWOLhmbjmYXqufk"
    "LamQMTlUnI1966j8JcV8EKDH5FW2ps51kzcuOuhIzRNSzJkc0vz3yOtkNTAPEXk7Mwv5DtxUuC/JTikzCHcCBBt5bXvGXsiYTDXV"
    "dzqfkNHEPk1YsoGugMlxuHedgacWmJQorpfGVUttv6UDGUmp03IWZH9jOebxCz+LW/hF/Jz3w3XR3SBU0332weKo2C8NKv5LmfK+"
    "1KjYKy3qxkx/8KFlYr9UqOjs6X5na8qeLLiLPUBrkBuTJlExs3Ok3kFXNn4CNtRtjFGpmFRo+9hBCVeD4v1BfX+njxMVzU8FIIfH"
    "NnCAoGJwbxXb/flmD1GfrSEVcxVpzyD6C12owBnDgwrd2DIn7sEUrGUM/Cb1HD4/IN18JFlSQ7uD9+P3SZGHygz/NvwofpcYmT8y"
    "vHcXwwExwkkA8HWJbn+/A2pEgSXk70cd/jiB+YHOd0vP0zi5tL19v9tGKGCzAZ+ghHxLbYNSd6OonkuYoMaJ1GWbYKF38ESPAreB"
    "98Z3GVYEopTGfEc3oDp6ZNbGd8dfF6YHt1Ndgp8AIlANBkUBvWqinTlZMb/LiiGuIfnLz7aH6XcPavQUAB09h+FHRV536MkeAPqJ"
    "QHcf4I0/59VCowU066W9QZ7L8B6D0+zgdLaxWjDxTSjpDWc45m3BlDeiZzkfNn2Dima7g5dlIZf+wC+f4qq4fcNK/7F8gv+FDuz2"
    "FzCbVSjDhGPeCS3Iwvdffc+o7ClQ59FQxiroAWd07s41uHhtVHtPy//x35fJ+njwtPyf/8f/tUyOh7Wn5eelbXXMQT9vmIXC7du3"
    "KYtYQHycPWrcmoPLDTOVQmdIZOZ1lbACQu7ZI8LsIW7qCD+/PWjtjvv7OX3vfPzqpJaHZ0S44T19BfjylH5z8N9LtupE2TW8dBQw"
    "2QS0sQQwOmjiB1//8uX67b84eKWoGV6+iasaD9cfBbKZABBRhlNE5RyEh4EU8+JEgWg7V8COrzeyJXI+gWa1T9fdvXnZJ/w5wOw5"
    "MMAUuOGEoDClu1nP1s5aOaY+oH9Ab/qda+MbdJ2Q7u4dbNJd39uoS4meSPFJmGopgkBQQ8F9EOUPbrs/fnhdPAdtipMAkVAmEzcV"
    "FvSpkBGELDh/wfmBmYDqEgd/Vi2SBUKwZj3YdPXyiA5pMH+Xr/U4OtqWV9i0Aa0r5bdnt7+/PChkZI7APjuL+XobPAMgw99pJ0Sx"
    "KN9lC/l0MBWIcQ+TsYBd0OUXgBsETW2DbAHSmv/q1aFDz84TKhHAx/xK9awz/sd//wDocGm/4I6a9wLQ4wdAmM6bo856bz5/AGS6"
    "hDGXVR8k+44eigQBkOC+8WiXQbtTDcyxV/z5VXIyCyEOhuxUW8I7ub6crxyGBwPyBCfX4WQhM3M0vR8/GmDyBA9StFnaJkyhqXOs"
    "DZxIeqoF4fG8hqD9seOEjXShb29JpyGNUzR08Ag15pY6re0tr75NWvoyjp17cfwkvz4YBrxPDFd3Cp3as5NXG8mGUZxAZU5d2q/r"
    "TFKktlvq1J8G6mtXdTXHFQRVrfpVvVS7oepuqVOf8QfppPILrwcqc+p2ToEJgZfKYawwHCN8VHd+Aqjpm/TwUZOemnNlYaDIAZyT"
    "sUVwNTYyc4pELgTAOB1c6eC6dx33DBuKRpN2XfY955iIiPdOdBrQ3VGG4hy7DIbBCIZE6N71AkdnW7+GU+j0DF5EYn/yXzPpf0oT"
    "F6c6dJ3UbbeKiP4w6ivevZv+6u18yCIDIgR0nglfHtGEH7Cie7cDT3EGJb5oHALNdsbxAWsSP0kGvf7dZNCe9s6PbBFJh32t0UMo"
    "2nVQlFjdJ4MMywFEfT9ReIib2VOBLm4Dr5FFru2f8k9lLYLNQn1+wzH2Dc11wAzYeYF2VnB6tCJv/fVo/wRRbk/fDt2TuRcMQRVT"
    "JWCCBeAVXWhtknHoeE/6id/fSVoO1tefWxdxAyvm7QzOqu0jKU6iS+btGfExQcxVDE1A7xUw17bVmqCYD6ggvgH8ylIA2rB5Ll/x"
    "l8Z8QNsfrB6xifD7Tq5EGSDKTff8eCuo5M0RAml9CIV1d5RQZYak92VSANtJuKYbfSxu+L1zzPB936Rbw8eCw/eqR4YfAApIcE+O"
    "PTuWTn4CR88HdEAGxP8J+VgfNxvx/IRCQMUxK08leGv6fEvLbRiZvfFH/fFd0oHztQzc3XdIP5ov7Sm6e+FWocEC8ixDimYnKtCL"
    "8/fRORcESYyM/b5u7/wBOoumFPO1027j8osbYtFvB7evN7wqyVc+spJ+FFX/KxQNM66qqz2HyniKjEtK4PYEjz1etMH8/Y0kBeAs"
    "FTDkGJA3wlpf4Itwtr9gWLBAxDJvoH/ng5NcjZ3kDgwyBa9+vK8e8m9R7flVZgIiti1aGTpbiBNE9B1OeM37PCk3mPctwu88mfc3"
    "+J3zjZPIMDY+RSg4tWdI+663wqd3eridFCeIAoEoeNzjKRm1xOcMx5/Bt4yOcqKIW+4tdhSyyo1occI8yYSH2MfTm2tT7agQPKnf"
    "TU98umVV67YVSJ2WjFpKe528BUP4l5NNMojGoO0J+Zt83+M7sYvshI0nr4IKLv8LxsD/Qb0RYN6FkOCLxrnsUZUPgPYM7sPDh6qE"
    "roYfwharU0gRoms2gd3/PH/iT8jBPcRdJa6BqR2uCMM73cXLbvbr97a6+I0UffafSDmRDq7uEL9iycw35xoxSC9/Qi1hf/RbxJIN"
    "iS4hd94wrYBS3db5hBwQYLGv8v43yMRvH9EJujEPSM0wVHPwsGkqdnzUNqIiL9B845+loeByo7xa8G4JjfgVQBAzz/CKHmp94g2Z"
    "rtfby7XiBIy1sd2WfmMRIZTDx5vvA+nNQeb3CPFnErqjLXGoko6kk4qSpatHiadK9LbpBuv9ZfkdftWVXeEW+bQ7YP2GEB+MBXGL"
    "FnJBWgh8EKGEIAT/tChv++qHx+qURWV5u/i3xflQ5ItbM5G/ngkn3EDcVLgA2nL9njk/5R3xPu/L8v+xjJH046T7/a/K9q2wUBac"
    "j5+I979MDYGTwPxa3+DJCQ51TE/RxCJR+vA1h/EU4ry/taguLDPSy2ywCE+C0wDyPNMjfnf9GKMV4/c3G0ReQSRgnW3BI4VkjEub"
    "A9hX7psdyMKJNQhKPz3dssY2nv/eI/V1UJXkbyXhhNdee0gBctVa3JbD+vuNPYPwcy8vSDn5ObC3oK/hhHNU3IQ3OYaNzrdBXc+3"
    "/P/P9+35lqn7q9wjWux0B3Ir/vnWhpT1DulW3xc3PS3+DbJFrz2qDeu/7XEwkXFooTFEtXTXB6q1c6DyEuV4CnXTDbTo3gNx9ubh"
    "3dG9szlEEtv/nX4x7BzXIXxzGwoweHQB947mZpkIjJWx4CXFDZEYviWgPcHrHtpMRBwl3VqyMuBA7/Z90U3sZRH2eg6Rbol71+wk"
    "m/ayezslaMS3XGBDwqs9PGQ44VnIXLtWXtNCvMOlc0/wcxXyjZnTuL1y4sAxzZu7a3VptIarOgZTAy9p31fmn39VmR+aDpf4Qlpo"
    "J5Z/NhPYjJFRkXcCTq7DeULjEvCIMUTk5XC56SLsWXKF/AOlm67AAYnJS7ByQ05yfeHcq3MOEoc9gKdlJrcMGkPx6KgYj957xugJ"
    "t2kEvPbOjL/i3hs04PpzD1/QMcOyEHuCN0phQ4T3EUj849ugmIi0v8XbvdtVBxLGu1hYw0AMMaKZf/N6Q6Ugnjia41g7zfcvn17c"
    "wFb+AQbdA7jFv3WEcb55VG4L7sWQ4O5/EHcX4cHwTx9iXOt/5xADunlwiv5ktPanN0dcih2x/VH0tBKAJCA9BW9Lw7N2i9rCLge/"
    "MTMwJFhoXlDBn8wK/PDmnJRj5wR+EjcjCIb/d+YDxoH7z9G0uS3HqFzssHPgLMje0LH8gbLNmyTY7+2LsnTswsBvIgsDi0LaNrfy"
    "AxqYq3D7g7W60sWFPXuiMrsPyFv4WpiVuIDorlMhNZxC/SYiQAOoNsepLnF4dtNXag+35nuKj1jSiQTmu71IoevMaDi/8DIFwAyc"
    "xmKUGhE78J8rN9ZhUSc86l+9vZQo//bySLlXiCz1zu1lFI3i87WDVlTQHpisont7EIxksaxx+u57V+MZwGs57XsPaZCwpWc8E8hI"
    "soTRC9+19vEZGPzgcTCmaZJuhA1/4EVG6aYFj21yvswW/yMQigeMYU8l4/oBB0woOrzKQG7JOG5h2RI0dUhEssL5n3AbKGSzT5Fy"
    "AYqjwlMmuX9apnMwoGrcNNt70vvZDyMNs/Z1LXREf1pi2FMGNh6TZC55vQf8Sro7RxpC9bsb0NFRBmLzstIZfgDLKANp/lba0ejV"
    "6SaKbTYkTaQa/5Wb05+Jeo5hnCPodbyDvKLBOLExZj+O0Vy8mIfe2pzoN6Q89FVExLP7+R07E2QK/o5wh4VuNt3qcaKdMyf/sFxn"
    "m6euofoywpTdNz9TXP75fu73HXvfvPnPuG/2bPNvr0j2ekWgvX/k6uyoRS6aUc2H9VEL3DFH93J3ff+hjTwAROQimqciF9EC9e7u"
    "8id3aaERBa00TtR1XlI7Nxpgtk8flpFASRbkJk4eKlAhk3vE0qgOWIuyw/9XmrMNefaa3qawopJLqKpVBcAivg8NRmYfs/sN5H3l"
    "3GP2A+9ywUAXj+nSMuKjCuD+HmZrCPAIT/sHb+Fsg16Hxc2v880GeVzQ2vcXWRj6xAYyRNqoXHhH0EKRdaLaZ4W/9wLlqJ4C5Q/D"
    "5XyKAzFkN2nPzU0K9S/1WP7+jrut53NAjqpP/ogSnLCzMBStE+3NC0QbRxtd4t4JrRyXqu49a1L0ldON10pAzwcmwL3LC8ZulThG"
    "5/wUzeF0emEGerYRvUv4iWx+YgD9LsDo2tRLJuAbJsP2oSQYMG6d/MzYuPWnufOulJPRLdAWD4dUxHiQh4lQGUOIRvADb77D8rcr"
    "yTxi9BLuzjWsBxU8i3obreqkGxBmFPAFVR90wXYCrcf5SQacimtUrLvxB9gEStQXMfNGZmzOq7dkN/y1Cr0a35I7UGpv1wazglGB"
    "pNi4Vqg/ZmUHwoTyT8WD9Te+drVxb8mt58L5O507slcn5NVZUdWraDBxznJ/NbQ7ICVDr5m3p6MJHT5btkOUnTYgiUKRwE9QfoAv"
    "X3QTZjZB3m5uAJnZI4ADtYpA+fLl4xy3eSH0vnPeuaMEb2fIbrhnF4yY1cvSmcAnVPvec4WcvZ+yQHZNssRn5CIEo14mGcPQ9KfX"
    "ULJZO+Y9egPxjIm6KTnd+14kAEUdPz7Xi2SDHIA87z5Hcf9qR6mNFMP4+W9O9fBAvR6vPWJgl1ceMbCRgzOXf6d//GjhrgMSNFiT"
    "kTzvfOsVgP0L9v8NOiaCz92l8PuOetegwUa8a9yvAygDY/YHGnFXIdKOF3Daboq13AUJE6FT7WFlQOcp2Jvt3Sre3/8VScOhoEyQ"
    "YSSYXWep+PJFAZj5dBfz6scPO2cHTOhx/+ULicOtESKw7uHZVQaoUJzXJz+8re/SCN1PA46mrnuoc9IP5PZxZsi9X3EzgyALYi9P"
    "59tfKFMHCkWMOzMuK99RUNhwy7ZS7J02ZWWsSRDzoC+A0+6VC+wVJjutgz+3m2dU9REGQ0dZstFxXOVRRnOnB5g/O4VxWei/5znI"
    "OVlX3wEYNmlnDfChtj1BZ7FBdZ3EY272LC9mvu8p+r99ZR4u3xJP/y3131IpMRl65yUmQ9nbngPDgnGneQWOCfyJDCk5A/NqOoP7"
    "K7wiyi52eNzLEioNoZj9+dV4Wz4Zb2/378SWHlH2+awGtvpXxzcfjhmyCUB8+pPxYqc/cTPbRmwhXDvkT7ByWKKEpOkJlLHSowLE"
    "jz2j7Xzx4zKEG7jtoeaWGhEns7ovNYSpP86wH3u7StHr3oOip3i9mHdV6qafjMvE6596ahCidTR5r2tnEfFs+mjAgMmze2+bQXtc"
    "jG7ql5zgfnaP7eD6RuPQhVHoHBN+5YuKExwFBXRfhJioWxwQIzXzJ2Kk8m9dc8fJlL8hHwdkO8Dhw/Ky7U8Bi+9vzp3z2tcdfASL"
    "h9/DOGlonpzoilcTC7+ztTXx/oCnOG9ABKE/s+LPZva3k1uHZjjgGnhtU5C0RXB3Iw4g6W9Ed/sZdkZ27+AkRl7d3skD86X8bL7Y"
    "f8jgIt6V5RcyoP/qxKBbXieu7/La7iTwyg/rmb46h3rV3n4yL59Pfz4v38KqGLgPXNmy+ZsDxCwvbKhJ+U6OMXy7Kd8BFmunCOui"
    "fUow75N2qe1jiQqn21AadNk1Q3p2RexvCJtn91HBGLQU2gsrqLl9z2nuuj1XVAYNBvX/c/z+qq0tassibrZlC7/BloKDuN4gvl2R"
    "JJKN3X4Dk/lb5ziXwpxlD8AaAsGrFwYY4j7gxSbhnKb/8gJarBTWekS8l4LckGHZu6WirZmHowiQ9sjDICpQsQQwh7+7/wsmhqGp"
    "57p+16Hu/+oJdzSVXHIyCt1jexfbdXrUM009olS+/KOdAqSnKSqnGSKnP35WYSDYExBHCApFYeh5dWFAH4l7+wucM9c8Ol96oLo/"
    "nAAcCKxnzgmtYq+78VAdLF86ApDhnZae9vxX7ttf0Q5QrwSF8ki+vLy+JeHUP9mFj/C3/Qb9hO/fUBCH/Z5jRSiaoOxBYIB7eMK7"
    "W/4XICSCgf8rZasu//5fPnz4F4oB+kHjpOdP6KcucJzx6cNaU3Rd0URelP9+0hTFeH14QLlZFHBU/NRhZDhLn5IfdEs3uD1YheSH"
    "B9C6xD3YJckPVUmUdx1mPUTPBPgu+eHTkOMV7sOYhF8ysg7wRRM3f9lNw7wLT85f5MIP6xMfOuARVP+EM/oa7NyMW9DhZElJfsCB"
    "KKQAvEh+8L5z2oO88eGsP2GYeg4W6fsnLBMu2rNPWDZcJPFPWD5cdJaeYHjUYFEGlpXCZVlQlvPr6dhTzn/IPPm19WwQED33hBX8"
    "p3ywL73wlAk0UnrK+t/Bu5ijDkeVi5Q9FaKVwKBK0TIAbQAKgH0GoPdgB04R7CETAFBgWGiTBFnCU/oDmOMP4JMP/wUrYbnsGssl"
    "P6Q/AIA+YIHSNBv+WAE7Gkz+l7ZrZe2qaayUKWXKTtUNoxtPj1hGd55XjM6B55L7DBWjT+vjSlw/rLiLyGl3jxnQN/o/dv/2iJgE"
    "2Cx3r7Fww/8ZGkBFlYGRXH4BvjT6V0q//a+QFgB8a+7V+bUXJevJoY2/dG39BA51d1DQeIIVUqay2WT+ggMo5JJsutzo8JVqBf4j"
    "ertKlUQ/MQ0+04VKZVgdVm7/a+w6qwJhrnfNSmpILKpjpaNU95XUGBtUJwRfEfD5aVStk7jSEGiygTe2NWtRqWcqYr8mVk1KAD1X"
    "8QohjPgmWT2NTWui73MzesWv96kjxnDbirXrcEJ/rdWteqU8nV3OrU0qRY8bdGd2IZtzXO0OEoLZGLaHrWFjrCesYkE56Hm226Ym"
    "dLtksOy8n9gVy6vsCqt0KmaDr53OK/nYOfYLhW0ts0kM85Njr1I6K9Omsdtx8kweNrVLHze6p8TwxNJiVi/3FhNFqCgT8UAkMOyS"
    "aQ63Wl/Ac+SCakt0k+lao1mvTeb3l0xRbmWrVL1W2+k1ddiYV83tXulj4mBojdWdUiaY7i4/OTFsQesn8othZ305CBLXoXNdprlO"
    "NBOp7Fa7ZBZZgsalunXY7vghjnWF4WLCElMlfRQoJVc6mXonm1BGWblPXurmvgD45Fgl+uNBxRyf61Kzct61OwVlqh1pjck08ili"
    "wp2P1IlN8Zmztsk1DVyqDqVKfVAjihcuq2WF9SJrFHoXOTth2d3q0i/nE/vEsKNVu5YkENN9qpg7ysVNT5VnGYLOTxZYvZrF6NVs"
    "VtisuWzhlFrQYvFSYktzejSY9y18Oq82qHoDZ/p5rHzKdFqd077brZnz05ytSFxlwGGDtZBQ2qRUFHpkZU02Rqtuu7Lqjyv1GV2c"
    "tg+NlTE1e5V+lrcqmeEl169vinJ5vKoWNqPZpGmlcjOTxxq7cXPf7OKkRdY5dp62iA7doQkzk0/l00V5ZLDDE3NWh8x8x+wSpd6R"
    "2rUrJlVp0wO8cml1laqWJonyObtixfN6rpsWM57ireyRTeWFlTXEDym6DSaLXvPt7LwsVvNZ+rBNZY1hOtUv9el5RTz0BandrO4L"
    "faE1GHYKZ4kRmNalfcqWZptzr1ZRRmR1Vm1SwyZXq1ekCmWZx9qxW2HNo8l0e+PD3CIm1K5A9naFySIvjUi2nzeGqyPWlqY9WdGs"
    "I9sW1hO8cMB240kO0EE5bRir7MIcyyox6VTxxSw/nnHUutzLtuSUtVbr/dPBPMh9qtQZW9XZhMUm0mQm1Kugoz2vLciMum5TiU1q"
    "vS/mdyPRHJfMA3ZuZa3Lvq+nNLB+5W4ikSinptL+IODHFqC2Tnte67f1ETFNmWelaBTTFo2PE4fN5lzbUI1yI1ccTgihcLrgHJZu"
    "dAa8UCOYXF/bLuhsQig2NqlFI5/XJOuUYfY4KXa2Vi3VI1Iniqzxmw5fh7775srs8ZuqXN1dqmUCK5a4tXFaiZiRaq7rVcVq5aYX"
    "Y9WpVgY1iyALudJ0wVQPRlM6p9hqQZeJxCpjdg/53LHTNPtKtULkDVXOZkpMp8n3mUqfHdRnp8txku826tNClmSnYmU+IIa9KWsV"
    "+HVbHpFCljQPQHJKH8vMZDPannLpCdmfbvdsHbsoxWppLnLFAdlqnrrTjcEW2OZxYRxT6dXROh4W51Upz7IWNsfxcedUlRNSqnaq"
    "ShVsNZKsXCkxa85MfEF2mru+0m/XrTyu4ttBTh9QO1xs9bW22tnPqN3Q6J34NiEKfW3MaOs+kIkMo9+YMAqb5ri0aBXyfaZ6wuc4"
    "wKhGzqhsKxLTVM8nsiilaxRgenW+3uF5coiftA3WPaWz+ERp93sVojts1Ou7ea4+zB9mgypdazbaC4uvtlrt3Qzne3mCrpBj8K9A"
    "Wsqqv9ezY616wDma7AMEmQpHqkjM6lZrJI4ng0JOz53TlUWZb+aqFZJsNzpbjdiwKWJT6QyMMn7uWZWdINVquDjcVlKL6al6adar"
    "/YnU3pzH3LifqA4Gw0GtLk1FbdwxBGuWnx8uxwy75RrMJI9NM8f97mgeN2JCBRvOfG3kSYlul6mMuMfpfm8/rJ/LRRxPK53aQpie"
    "1N6UHphdSs/vp9g5Pd1TEoYt1gqdnY1YqzO1mqWSoStDi6B7g6ncUY8LMGE4k7X0idiiK32hMuPrFZ5X5lZ3MNr1K2cTrwz7Y6OT"
    "qHFktUaSeJ038rv2VBQM3t4TuXO1JlPkwlIIqz8o5ts8ToB/HXF8INo79twfJk7jNbHThrVsW+2dpiqxIXslHd8BvnHqzAhaaF0u"
    "qZXbF9tQenJlDaa0BaZU1C9ZfFDZVHhJE48L1CNgLUWyM9pljqO2YSzKwzWdFXc6tWd2oikZJdNIlaWGupGGRdKskVUl16utpEp2"
    "e8712C11FBvtfBGvnzOUPqbKON1brYpjI5dVSz2sKJaw4YCQM/RgRRBcabehzHNbEbdVel0uDQc9S68PS4NcUZf42Tk1rAnFanfY"
    "K5mzjMRnR/N+SaTkSa7eIi/tHlPKTOuDVW4nH3SFnWwvAs7q050gMGeFpxN5KdWiMiWKSeCySPUX3ISetqVZqd/ID1OH/KR75C/T"
    "Xb42XFBKI09Ipyw+FI6XDK1ZHbGe2QlnihwW1USTTSllnJtPjguWpa15Yr42ybK263PVGcFOqzi9txKpY7tdKyoEoXMszp8zepol"
    "DYMii/LmxC6oLLZd4LPJjjb2xUKjrk0m51OhM+AU0dqXTzUspVWJsaqmF10KV9hjcdYd5HMlzTTwU2I2H2c1atQdnjvSSRXHTLtc"
    "k3rUQTeKJb4oFKjGhkyU2sROwibHMp7KbE+JTDavz5iLLGj0dHumGtWJlUkrmRqrZearS1bt9+bDvVg2mXIPa5w0Ot/bpTbVUmLA"
    "WOlcjU71L6NqTtCzlNWk+rkV3ug1VauMbVfVVZHJU2lcURbqqDhR8tVEvTWwzvipoFILLpvGLhuqRJqbwz7dy0tHbTctFGr5grY1"
    "usymVj6dUuVKm7ikuxi/4TvDuoKdRw28Lmmz/cGaKHy/2ReGY6pj9OYSsThmL5lEqsdKFM9ui51NYU4metxKGJaO7HhIr6aHdrG6"
    "bqVzCy21TmeK20qtj59nQyE91OeNo15rllZWIz+hqHl+kzut8WNR3rFmKj/I9hPdQSNrJYCUtiodrexoqmLUZrMvtDdbZkSkzFli"
    "sDl29cU4V5JrLEtqpwRWyRjNGldS8JJuCqvRWMyfuExllp0y8jZLD5u7tZ4ZYIMe3SlftDEvS/wxUc2fcOw8ZAupppmgMqcJ12CV"
    "rmSpzHCcHnb3i7GWyIzLeSoj1To8K1BTglOLQu2y35QyI5o+YVVM7rY6w/NMGVEtZctz+L6ZPeVy9Gw175WP3eZmVTztBX6Tn293"
    "8qq0GvYO+XxfrTYG2KInp5pcnu/W+9V5Q2wv2Iy4xVb4rDnCVGqcF1cSpWYOmJ4/FBZYIo81U5eE2hb6m0RtPi9iZOvUWmnrXLPN"
    "j8gJ0TGHO2o0M+aE0CKynIElstZB0XuCjo+Z2nohrmsW2NVbeEfZS2ttUeKH6SmY/8WY2ZPYYDXYitWiwmcLc6ma0miiUtekOTnZ"
    "D1cUkW5rui5PCqv2BGwfTKrXGVkXoXZe5WeD7n7N5Tv57cXSs105I6X5mTYUNr3+YjDD22dmPqOkeTmvSLtCmW2fAIM+ZbiWahT3"
    "meyJKTbyp/Isw4+YVbVsGM3EweRW21FZrR/3aa64miQSgKIa5UW/V94Me1vS6i24ucxn9psat6n01sKR3WplvEKN6I5lEVJzvKhK"
    "M1OuDVTW6spjPYdhpt5O0CVlfWJ3fXLXoXSrL5hNsc/iWqN60OhuBxtLu4mhjDfM9FxYCBOSWLdUalTjKnVmtJ7Tnfx+3JQMk60R"
    "gEJG0oIx9QUmD3bYZXIYbYiZYJ3n2ao4GmT13XZoCZ3xkNgZc6rROJ9rTe1Al/hEblbFp+x6Rxep5rzGZQDbr9Wqdb5SSI+nmFwa"
    "nNr7TSVrFFc4rc0O8mw14hO8MJyZI3mMr7ZFPbHPt4e17qRfPXWUnDWrZ0h1lF/LGb44zmQOIya/I8fSaUSu5eGI2KcLbAvLjwqJ"
    "MZ9blzoVYoZlhXHzfM4tpOwIp+sZepbozeYbftYkU2e+eVBTLE4fzDxTqeF7Zm9lUw1rxLGDtkgYW9mYlYo0nh2r58mg3MmsuKM4"
    "mxQ2Jj4yzMbxqHasPsPpJaNPK+0EJ9PVTffc5q3GamfRuc18Whhczv1VZ3vhDxp10hpTujSvScKFz59kUr20z8PJQZvxNN+p8JWB"
    "hfOnKZ+lJ9KoLp8HsmAm0liukstQjbpcoJhWZ7bJd7K9IVZar9eLYiO3WLGkUiIbrJVSsPlJqNPp7nrRL/dWpqBo4KjS7sxnk5PI"
    "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"
    "j+/jziujDA4zS2a54kHLHzbsoGlYrPDVmS6LYHq2Un4zPQgSw38UmP7z17aVz/ZWb7f5ak283dRau16V7bBqv8uWX9lsm31ja4u3"
    "Qd9cKItaVlm2+vkDK+TvrQ+1pC3aK8m6nTXzpfWA6bSZhsksRrnRS3b60lMLi7Ze2Oki/7KUN63NAAhD5ecN0zUFq1MDe9htZdMp"
    "M9XPQvF+9MK03hY9qmloNXPG39YsqULPb1sw5dX6o1RlZ+AsaNSmfeNZV6df8/ILc1iV18Z9sWlUhZ10+2WYr/m2qFnsvMnorSk1"
    "A6eXNuofPvm8ulK4eYf9einnboeCdri11Obzy0pZW+3xdFiwmrnJ8c2Q93TPvF/mitAHPj/uWr2Ssprpo2ZuONq9c815bTi/nzOf"
    "r1RRe91v6vmFsVtUe912mddZacs0d2+dozifyXvqebYvWONtedtTzb3x+tzolnqV3PBj3IfpE7Msmy+9j+Zbhd8tjOlbf0hLreLX"
    "sSODFdApN8UcL0+L5erb9pBt8/nRfnocWLvPVivf7g/znP7Rub9nlY/yhDPY3FyZD+u7Nljdm+brki+8DjrdRU1g+fVA0ecfL4qm"
    "V7vz7aF3fNPq5dXyAJTl0mdxx7TKn/P5ZLamJkarKKjS/Ud5dm+t73n1hT/SswHbklV1pcnFD6kutYy6we10+sOwbr+AXls2ioUm"
    "e/+pvzbfNm2hvhks5ar0OdMmC11uGc95bs+ru2zrsGYn9aV66C0q7X1H4V+l4+61tqOb0I7S5V6ynzN+9lGr5Rdj9kOSKq+Vw4fA"
    "1kGfOztK2lnLY+VFpsTjUD9ualLrtt+t5ieLkkHtB+sXq/SyOz7LjW2lXP0Ci+y1O26V+WbOYAbv7dqgsRQ5k/9SWy/r7rSx5N73"
    "jWY137ndLwVL2Rn33fGtxD3vc+tndk3Tsk4P1NnR0Bs9WcwzX/UhU5gOXzfGc8OsgSOr3FiN5iOxPRjl8kx/KrbY5mCWo76U3uzA"
    "tubZz/v9hp0buVlffa2zBb1RnRSMr+lzt9+f3lbFamUsdYyOLo+Ko15zTr9Z9fnHcmSpulYr5ruT0SCfF7K8ZYir/VQ2W596lRHo"
    "Tra+Grx+7JXDLdN5Z5Rhqy5tBmOu2aKk7nDX7D4XezuluFVKy13h1Sxm56X283G5GeZe5HrpJV/hu8emXh1n+VqXXzJ57bMCNuJS"
    "oUIvF2+tSqOu0PvBdNkxutb69mC05vX5dDzZj/b9dm8u31esxcLQhKbaeTlo1Iu0ZuuGmqe4/UHRu8XeqMOtX+fyfGhItdcGO6sC"
    "MfbAVztfk1Fxwk+HxyJXNcbHBbXL13pvOd4c7GkwKC/b3mo/LisHnm+OV8usfjQphu1+fi6gT7tSa/SeO/K4VhDyzHTWqg6UN2G5"
    "ooAIuKpXJo2W8j7Ii/36oW0IxlRhq+PVND/d3b7mxMmotn/lxvSwXy4J1ZxYKXM00+utDh/PndGO7byxVnPZ2svzZdOkTCbH19vv"
    "1VVhvVOUtZrrWptqvS4rr53m4l2Ryr1qMyv2G5tFjZurYn71IVnZVU2tzQfjxiDbB0Lr66shDEEv+NpktDGk3oFjB8vJQN9TzUn9"
    "hWv0K71ebQ1wfMg9drT66FatXqlM6ez8+P5m6otpm9917+nyLT0ZSbuV/FZryIXD+Lg3VT7LlY/bznTW4GVTfh1tS1/ay+RDaK5X"
    "lPB+2/w6Av12vhLKr18LutCd16SlSRVLw5IuA7FZeM5VP0ZSoaBIu+Zq26qKq86wZQ4O9H7eEPPKqLhcNBqN0iw3/9JG++dCU29O"
    "ep23XEsef3brtcXx64ut1St7Y628W6Z+P29w6m2OqlfYId2YDpi9SC80plt7WXUb/L5S/ajVZyxz/5Zn2sK8YLKzXteoKq0v4fCy"
    "3PRz0uSruVuWu+/l7VtLNwqz4758fN41S5ra1JrlCnt7KxZn5c6yNK1/tpWSbux6WZ7d78q1xaRcrr/N6UauWdgdF4vVa+1lnhtU"
    "X5nqVx6cXqX63miqpt641dfCFkhClXv+k9ptR4t22ercM41DS5seb58/yt3Papsat96PhfJnTQILcFo6WuPjqLdt9p/ZamWjfJSO"
    "Pato6e3hm1i+v++ZuQE9sSYWp31lx71sbV0YMG/D+UbvVNjxJ12nx+rQmDCvRn1gqn2u/L6o5UedTdsyOHF6VLViYdJa3d8v61VF"
    "/JjRxnbd0m7zFLPfvioF7nO4Gef3nVmlIr/I2vBTGAnt8VvRHI1zE2Ejmdquotyvhrlb+qtZ/9x0Jt3pqnjQv3qz3aouLIT8cbPI"
    "tprjoaFz9WZFnD4XXgT6uDHzE/NLklitpzFfA21J8w2mPuisx8pnKX/oTTiVzs6ebw/D7nOjOtcG2xz436ve3WlqI/dGj95bxcNG"
    "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"
    "fPrX/wf2Sgzm"
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
