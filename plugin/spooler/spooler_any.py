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
                             "spool_set": bool(state.get("spool_set")), "hh": bool(state.get("hh"))})
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


MMU_KEYS = ("num_gates", "gate_status", "gate_material", "gate_color", "gate_spool_id", "gate_filament_name")


def mmu_units(mmu: dict, spools: list[dict], target: str) -> list[dict]:
    """Happy Hare's own gates (its "mmu" printer object) as Bambu-shaped units of four trays, read-only: the
    spool id it reports, else the gate's material and colour. A gate it reports empty (status 0) is empty."""
    def at(key: str, i: int) -> object:
        return _list_at(mmu.get(key), i)
    count = _int(mmu.get("num_gates"), 0)
    count = count if count > 0 else max((len(mmu[k]) for k in MMU_KEYS[1:] if isinstance(mmu.get(k), list)), default=0)
    trays = []
    for i in range(min(count, LANE_MAX)):
        kind = str(at("gate_material", i) or "").strip()
        if at("gate_status", i) == 0 or not (kind or _int(at("gate_spool_id", i), -1) > 0):
            trays.append({"id": str(i % 4)})
            continue
        colour = _hex6(at("gate_color", i))
        trays.append(slot_tray(i % 4, at("gate_spool_id", i), "", "", kind, colour + "FF" if colour else "",
                               str(at("gate_filament_name", i) or kind).strip(), spools, target))
    return [{"id": str(unit), "tray": trays[unit * 4:unit * 4 + 4]} for unit in range((len(trays) + 3) // 4)]


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
    if isinstance(status.get("mmu"), dict) and status["mmu"]:
        return {"print": {"ams": {"ams": mmu_units(status["mmu"], spools, target)}}}, False
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


def moon_found(base: str, tools: int, managed: bool, u1: bool = False, hh: bool = False) -> dict | None:
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
             "u1": u1 or bool(last.get("u1")), "hh": hh or bool(last.get("hh"))}
    if _moon_found.get(printer["id"]) != found:
        _moon_found[printer["id"]] = found
        bump_printers_rev()
    return moon_entry(printer, moon_saved().get(printer["id"]))


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect&print_stats&virtual_sdcard&"
                       + "&".join(f"{name}=temperature" for name in MOON_EXTRUDERS) + "&mmu=" + ",".join(MMU_KEYS)
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
    spools, target = _spool_cache["spools"] or [], target_for_host(base)
    doc, heads = moon_report(status, active, spools, target, lanes)
    # The Snapmaker U1's toolheads are booked by u1control, so its prints never are here (_moon_run).
    # Happy Hare ("mmu" object) reports its gates and books them through its own Spoolman integration:
    # read-only even with no gate reported, never filled or booked here.
    doc["hh"] = isinstance(status.get("mmu"), dict) and bool(status["mmu"])
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"] or doc["hh"], heads, doc["hh"])
    found = (_moon_found.get(entry["id"]) or {}) if entry else {}
    doc["u1"] = heads or bool(found.get("u1"))
    doc["hh"] = doc["hh"] or bool(found.get("hh"))
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
        _live["printers"][pid]["hh"] = bool(doc.get("hh"))
        if doc.get("hh"):
            _live["printers"][pid]["unit_label"] = "MMU"


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
        # A printer that once reported its own spools (U1, lane_data, Happy Hare) keeps them, even when one
        # answer comes back empty: never set Moonraker's active spool on it.
        if heads or "vt_tray" not in doc["print"] or (_moon_found.get(str(pid)) or {}).get("managed"):
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
                    state["book_ok"] = not doc.get("u1") and not doc.get("hh") and not connected
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
UI_PAGE_SHA256 = "90fe03efc54a9fef044c32b30f1d8aa73d2d43aecfa3a4c100a7522be97ca86d"
UI_PAGE_BYTES = 1337797
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
    "IqS8DTYwRXBgv11JcKYcnNXBNAeODxw+E+4GB94UWvCZtC/TcpBrmckT1yyaC70sbFBLV4Hf00aAng2UDJGeIaIZxEjCOmKtDc/S"
    "LTwzFWxMJAYgwkkHhDb3dErl8tIpIaOVT6f0TCZCpTAPwrBCSHpKS02tnqJrvk2ZU0sugXYAzHJtCT7j8gKeeoemgiWggikL9DlA"
    "fcCgFgzaxwQZdtxK0Mrr4RRsS8ZHlwjDh5/xlblupEFh1K5QT/ZcCf8LZ8hMcEIMSp+Ix+sycQ/HKknfhpWAP6g2FhRv7mwDOz2M"
    "M8jtjZB/sQPkX1SFPJxrIGdwJhXq2SnmKHsKbiSq52s8VVHZKo0gJktIJ8QW59YzbeYG6YX9Mn12XipjZZjw65g9HaB/Hyhjx6PM"
    "iy9YmTKUWPDfNHwv+7S2pkkpaFvi3L/VeSP/RtXhhFxoAwd6C1Tn5EK78L3WwPe0/gvtwvd6F77HLrDD2gYkkb7/DTwhOx6Qk9pt"
    "6h8JzuXiOkfLk6R5Ehp8IonwRawZSjL0pLoADk6Snxy+LwrhYyfaTwCgEfU5UPQ4/Slh+l6DiVoshXEeJo3dI1S0b91Ge6isZ5Kh"
    "8ORmcNZiOHUWeG2xcm5bTKf5cv8tVt6BS+bQWubJxTK6cqlSQerTxTI6ddFOg+XeXdbWE82mMxWvvA6k/2bkT1D7RFp4wvmjkXd7"
    "kzAr/FAGfUeTfH5JItO462q1l1i/UGgT3BH6x0LNiJjVzVXQhbA9YecFJBWwvaF39L3w/fsnwto0TK1NQy5WfwFjIayKaLybvOsd"
    "dAGDoNwIDkb/4OJD1UVo7YyG3xqeTMiS7A3DeI8rD6Ns96VVY28Lbz9msRFhK7a2LjEcjikR2aWkiyudQ4n/jaO3+3H4DhbosMai"
    "Eu5D0jX6ff0PtQEey27rLr2gelT/YsX/9XLnCqgG1znKx6vxLKxagTJC7mIBywAFQjBCtBPX0tFzvdfHS9RwYmZ2wxq9PmARFI3Z"
    "wpl7DBXhfanynYm1a3Ytjqahn/1AYxyuYviefuGhJ7U0FntWSwrgyDSshXMYiDDRk/cD4sJqItDrBM7mx3FRPnq9gONSlpN5+dyH"
    "rnsUrFwGPj65dNSv23en4fG86KO8kckOm7daxljnAiO9kWUJ0orAdtvOvWiBqyaaWmDhELdGSh7ccOtyMlTh1iWjRYI4uDgP/mfQ"
    "9gr7z4v9EZZIToc1x4RbW022MmVAKsN3MM5vMJ4aHCxNdVfcL+i13iSa+tqukQVb6SIzuZuFb2Fl1KLXU3ds4TJClKCfah37n5aK"
    "KPVzQLd/Qsavw2Q/nM/p8IdzESf2HJVFq0SvTOn4hEYLH9YwsvUFwB3DyvIm+z7xImYmpTQl8pjX37maRZYfbXj2MSyo0qSI8wl4"
    "Og3nZD+YkrcX3dx+EJKpH++fLLFjKlJlF3Wmzf1Z9G5/FcJc02ucbdcEZXQmrh+dFA/jaroDWd2hzIzMV9vCP4XzEFMIz9JPA+Er"
    "H0oWknDr8aPEGNbw1F3EhC50+nTNkKV4p0dRIxJlI2CeS1UbdtgVJzuU2RqFSlkVulmccPKQ+1o+IRNne/AnzR3KtHYo096hTGeH"
    "Mt3tyyy2L0LDc5Lty42nkff6z1WU7FDW34FE+FtjJ0VAtu9viZwZAqLj5tbMR9HyF7sBXUXpjldEKApz6OCx3YTswElPyTFam+9E"
    "Bg3M6tZUOJwd73BseLNDoTehT6Lti3ku7LTx9uXCYIkyqq3Lkdm44glN34DpRfS28yhZHbqw0zkTLLOg87PQ96fkwuav+lQosM7c"
    "t/snoY/WU45t//McwPDI7ZQQ7AxappItuOPJctuuixrtzUcpzn0k0UIO1sLIvcarGSzW050xhnJiYUJmpsr90J1GxxdGVSoedBUM"
    "yfKGb/fFGO50eDeNtokxDyJvFaOcf9uuw2kLzxo60qz/MbL+QBErvv4Pjqa61HMXSWZjsS/t3rM7Z+DOwinMrp/s/Ss5XUTHcD6Z"
    "nDbwW4N9+1d9exECPUaJCchUjd8a7Nu/6nk4KXcdAqe+T1C6te9SM1dVMDMPZ3yDXOyzF6KXe7tw537NbjTjGnFjgidbRfQApC6Y"
    "4nFoAjSOzMsgmBL3DdkBAnFG2AmG/7wmp3Qricv7p0zkMpopr/jf8TL091Hfb4qll9EJCpKCZQrCOmU7ogplnXzZquDKwdgaYOcc"
    "ANuFAMMcC7molU2o/Y9NUlBKnZjgdZ+8QV26LIVZxShGYXLO/JHb1LpcnFJga5I54TIS3xs8NbeAQjNnjGUxKij1aJpfdfhJKchJ"
    "KoZg3d9fvKWfaUVWtiKFNIjVvl0pFLXsxxOgoK+z/CKHi0qkTPIhdRGmGWG9hfMgnMNGRamQq6DBlkUEgosWVUQ3QWb/M4OXkvVP"
    "JfnLCAOy7dk+OVZGgWL1pkzpAkBuqHJTrc6gSmO5bMWL/G/Wd8BDpNfAA+3P3Pi1uvVKXkJBe8yzn35hyI+JjTRRWwKc1ZDZ6Lu6"
    "6S6iOGRYG4RvicIlAc+nsUNTEug8Y457VhdqjqfOdHSr/TdfMO0QHXDag4a/Ymfbf9XRNcKJu/TjUhC22YDzBXcCwbifGbpXupup"
    "mGHkL0t2s4vBKoHC1brEhqtyl84L1sZ+l4xZiinu3JsAY+zLrmyDsObCtZZtz2LY+cehtz8m70Ky3Gs4A8uxGs2m5eQ2zlwt2yCs"
    "uXA1EMrZkDJULuh46dxLHsQuJKUxKnLu2Y1Bq74No1gwBmfFaHJeWBQv6o+qWUk9+itZST3SraQea1ZSupdzGqXFFPeStRNz7aeD"
    "sjw02B/XduL+jmWXU2W7KtE1G2lsTbRqZC41mKOyvbli2qoEUn5K51coBycHzrXk364wgVEDW/Puy28vEqHge7YeqqnXkn82rz8W"
    "w4JK51/YqVMHtWd3uYoYFKqv68MNPYyvm8KQUp8Rm0KPYsTE+lCFyQyQOc4pwrhp9Oc0ApjiWEsO8N1AVyrfSw4eoHFLHXhDcr24"
    "ReG/3dLipaJ5Br2nEO8nyzCRsVSHBGcFiqTNPwikitzBQwRFGmClSxegUdZiMky+HY3SGh6mxlx0YWihakjqsIjih+KDRbUjRJss"
    "YfqWRE+FI9yXden3QCwUYdxmMccIj5iZhzQpEgZP13ImfP/5j1Ixs7kThjk16Xm3xjwySA9ozCUQH5HrTB13yKJ/1zUa8EwZxuzy"
    "+N755pt0ATgvZZ+uq6k4WfOD313mimgu9BnnirvFb775Yt4IYx5MS4zIF45uJ8nV8peUYkClVC322r3lXli3fqC/3+FvFgcnuY76"
    "2TeQdlLlxHfBgW3dDDS7S+vn4KDAu9jIuq+H7HgeoF2iHJZfJHI/D5Du/rkiy1Nh0X0D5pFZu7/4+uznYH3w9VmAWp7rl5aS+l8s"
    "mXqv+w9MzMuRYW3Ksad6wdIx2t7PATP1giGff/PN/YBr1vKhuwYDdC+Q7oeXjdWcanOiAueSzGA7RQ1WNjD3grRXP55/sqmbJcCv"
    "L2hILdRLRdsb+EtNd9Do3t+rXz8J53500vAjj5bkRoPUm4dIs+KDKHUN4Q4j9I7cCGfUk3+CIXM8xVmEZ60O0Nn9fOVOLf9gpcTw"
    "XqHPTmb/vjgI0irZDL36+uzbb98F69EwsGbYgG9NDmY5LxUz6xjrx7atVwfHue/H1htsJJp7xDo9eJP7jr7k0dHGMk6stwdjBTx0"
    "spw0ojlHfuvWwWGu9KF1QvPwAHLocvkkl4k6lMdcqJ9rHR0kJJcFhm2OeagDQ/QsP1fywG42J+hcHgYhjqaUI7VcchDm6wnRS/zB"
    "zcCiTuEPdH10tl3C99+ZVdGZnDNKqq89onYujxVVZrnVR9gUGkvT2qnz3KlSfSJsOXfGTeq7itUSHQAHAP+jlyDAURe9b0fc+ecC"
    "sCsCVHj/fgJ4FbF5ff/+lHrpIdyFGNOkZpBfW3KnWwmuNmaTGZMDz8LgKZa6ml3CfFpQ9Wr0fnVGkWL4lgfWeGXRxoarNTq6vt7Y"
    "8zCQJW8NqF5qK+pj0BwZzJt7SF4Glle/ft279jx4//7Ah4HwLKBV6GjLR6VuVk2s0ytBrAocLVIy5VMChe5wgA7dmRIc1JunD9AJ"
    "DCYyz4o8fU+4+gAiSvvJ20U33PwRUOxWNJ9TP2qo/J4OH7EerWQBHldD+JscWaE/nBpG6u31uDEhro8RKBZk7osK6kOejnpVc//W"
    "JJym3yxfPsNOgOOjtByloEZztAI4MHDjRzA/wquGh9h6i06YnC+Ygj1AAz+PBkx1X7SA/UNDThg7mDH0fWL4cgAQw7at0PVEHVwV"
    "XdDT9Vp6d5pi4Cuo0yXXp7gpwpY+RXOUMxjMiUWBX1hkOgypj/mltaL9zRnYX4tx06Zt0RW6B4uGXN+TCM2NK2KioKtTH+7tERVm"
    "wvcizPZEDnedxunDiWLbU2ai0vokCjMfnkAfENQp0C1u8DD8Eblcxfz8z2rnuD//Suc42me6u/8QWL8F1q+B9buyzf/0Vz7Xff1h"
    "znU/VTnXkcVHPdf99EnOdaKTyrkuWXy8cx20JXnU+cJ0rvtzw7mOlmLnuj8/+rnuz0tyrlsudItG2KqElzG7LrAjWBLyjuwVo+nZ"
    "0j0RAdf0MgkeMBgNChcHpvOML0zXRv9oLPbZXfe+63kkplfDXLIntUCYsM6bhothDd1b79k1+sOlePLiQui3CI2QfZmSFQ6aL9qz"
    "2iXFgtT06sUdA8MMxzKWfjKBDYLaPVC1ZFTq5h8UFZz1P/7B7zMQBN593udSwPaXrKNwbAQ+y1tG0+nYXTZo3YAGWPMIowKwADjU"
    "R/nCwLuM2MmUOdE2M5IYWZK6115b3kJ4HUODvhFlFMIFDx7yB/Cc6MqNxEM4KDM1eRY9ehgtLJ2XuJDj5V6ucFMt3DQWbr407sPo"
    "E7MBWHydDPeUgw91iA7sf1Df+wE5aVguLzBWC4a3IWlw6Xvo+QZOzejGvm7B1sODdaPtKPWehlQUgGZ8yq3Dw7zbolxfbLUvtrEv"
    "Nh0IZucpAU5UB6UJc/yOrTJ/MOjfnVgmNoWxb9SzH25apnKcz0JffdQZ40frhYTlRoCj+zU9rgFDiBGIhBc8DhM7r4wspEi4dRj7"
    "el3r7ZCsec8ouuZ7xT1i7965+a54Tl3XK/iYH5HU7z7srRnIw11BHongyntLPhVwnqVOxhUHkAk/JRMmVKFRzb8+wxJyzfyWXTMY"
    "REMEw2EBLGhYZcOS3NtxxBDMNDqGXIEUeVk6EzZ+uHZZ/fmmb4twDB+oaVl/vmkW4iHbrsa95dpuqW23jG230m7TUJE8zo3SPG0i"
    "E5iFgpGhgUVAVENXDkTaBEVPAUU2rMeFUS0MC3I+GZQgreIQ8mqaUlsRMPn9e0oEYGuZBHu/aguKrynciawQg3YkhqAd94DRLInb"
    "ES/UkaIhKPIBUzAqh/Ttqc/mhYyrnmydjy34yd8j13/3hTCZRb0uwg2UThcO3HzDwI2ok4N9ypqO6OAt+eDNsyFN2CJkW1TZkAEs"
    "O28z+T6UQ5/dM+ssLpsMzHIjUCOzZGm2qRfnZ+ukR7+gYYqzpJMWw9ZewsLybecDAo+RJRjgFwbyS0kmaB5xmpSV4jGP8uLXRyxS"
    "Jp/LoYhtSNlPwRSFB0BDfs9uyoLqMC5C0B28pLmBoGSDF4YY/Du3aO7tuXUUDG6I3gR4t6R4FnE8c01xmeZK/A4e+dIwcJITROgZ"
    "M4gHEr7u2aGEu6HEjVBxfTtd7KluOcVdEzvTfyFesyLu0WIfD8bzmOwzX95i0coCGfG3H74ZYUSr0D/IlkUXKgggkvoj6OLBCOZ9"
    "iPqloTu9Jo+UTJlvHCUYatrpwomRHfvo4ztqMfp22HTavXa/1W33rmVOqfSQOromjtpukrje5JBa+u6dzTDE/MibRjHxR+v6NfRP"
    "PyfL+0ePHh6M/g2w1+BQCdPnTuGc/2WNgnvwpTgXO/bibc1pAxiKTtZXg4EzdsbXmLriV0EQXKN+Brq2XXNai7ffOY1mjYXl3l+F"
    "FtpvT+GITBOsGLBsPybLMLimezfAviomynatjU034dfyeOzu2Rb9aTTr1778XjiyRYkJef6g9pAN+r+/g/58P7LkTI0j/1S7DSA8"
    "3vxqcfCrt1dPccVfVBIc+4u/kOCY9jkVEgWLv7CgeLH4IIJiGLPNguLZxxUUqzB9PEHxLC8onnxEQfFEERQfGwXF/qJcUHycCorp"
    "wviogmJ/8UkFxQjTq8XBqGk3u/uOs+80R9abxcEZzPpiSt2OUyc/NOAyEHpcDhbf6PgL9d6peQQeHdLn2gn1zi/97Y5SN/6qQ9vR"
    "4yippc7/pdfY0R144nVwD6wj4co/dWxKSxOZfJe5h4bUGnscoe/M0UMSx7Vk4s5H1NVl+l6Llqx0LYlG6KNydI9u8UueG71Kakl6"
    "Ae4RcoRu/WphPFK8MIo0DAQ4Ur0fyg9j7t8/dUIoP1H7vhFzXgfjhn9GLALscHQD/4ysGbpsvgE8xegRPtXgUSTOT2XiHHLCho6x"
    "J6Ck79fwCY6b9PaVpT6jz/wDyuUXAPxvJMZc1LoYBhNAmUTARwAs9O/IWi2owHf0nP6F7+ikBYC5Rf+ygE94T+zjtPPHkYXbMSLg"
    "6Cl7GKFHaXIYviOI5/Hwxegm8Kw/4q9H+Ose/jrCX0/x1x389Tv++u3m6CUM3Clz5/didAjciXuKxSL+cLQiMXv6hfhz8Xw0WS35"
    "491lyB4O0ZIRH9MaDyfRMmHVsjpZhawyVg2rgRVXSj4K57QcLUZL0UK0DC1CS0ABOPckEwH+D6jQtKRQkfGSPz5C/zjw9wYs7il9"
    "x9QfVhhPC/4gEoxurI5XyG2ODmHa0Igc638CXAF7egwzyxNvE489qk2Lfv6AuI5ts2ZZo2qTrEXWIGuNtcPaYNVDzQxLfmNYS59r"
    "v1HcZR8eYcPyC30TnxDz5Rd8GWEY5TdQrYtcLJyt34TRKq6xBFjqwFOLj4/hWX7AUgwAWYaBgCXYB5qfJWJuDpXMzuHC/PwTLcCT"
    "scT9aKXWj68sP/tAs7NEWn84XyVqH1gCb4F/ZE3wD1jqkABN9JVSLIGVEh9pKfHBnQ1H7gxKw98F/E0iQMrh6CiiaH5CyOv7xKUh"
    "ZH55jQtvGSe33dMnwS/wZQjnqUl0QvtIaREdKaD+SJzuwtHQBTowm33n+9+d0src11AN/B5RLZ0VNPmI/h3BuWwZ4RI/pH8BHDeO"
    "T4Dfh71/hqTlDjU1gC2LpwN1h/RTRq4fAWFGN2lIwJckxpC4LIoq1Ev9RckMZ/Za5nCXpOa+ccMp8gkjHr8HdnYtM1qtxzX2jYhW"
    "D3NZoWGRhxaRGbXW8+AhIQP0jYneKiaLnSn7HSrBzzWPJvOG1K+yTzUeFxsmGfbh4Rlw/uQhnldgepdIlwLY/0TKXXyGJmF35im4"
    "Rx7KjuNOPRw5NfzL3mAHo/v3mqbFYgTp7gK/ckOHqj2GDCIZs9BjJ25ddLdYcCRO0ZnhMcNgeHbfhMfMNmb0WD4DHPTe8yhaADrR"
    "xxo8A8oBWaOJj3DnkknPRcpznnA7OpnzJHxkiTfZYZslsxdR4xFw+SThn5Koxt7F10NY0R5Jv7J39vUGQqkVx2HJVEEzabXwTKKm"
    "BUw8n7Kn8Fg7w4Q1X6tP04938b2GCcDPuNqnh678ggOsfKG0gn3B6VC+SBLDvqLt9FOyVDI8g5QaOixb0Ax/rGaLowi/3wZ+Ho7s"
    "c57vB/iA/aHAi29q/gfIS5oy0w8C76A52qaCswK15KfnCq4xW3j56Q59pUjIrc7lp1s8AVcBkDtBc+YrwC945zxjDVNG1iT0iZrj"
    "PrzrOXgwkpFgNdn7kwU7/Yv0mkgQGW7Rszuwu4nMkiZBd/ww7ecdeAFg3TcEnwBMtIxiiYzlYsmM7eIf0EnHzyGBGh7CUw0fgZMF"
    "docl3oMnnhhPQ9xAD/EPf2NnAyQI6Rug4Lsomj2gHixHv8NjjT7z5LlIm7OEJ6uEpzzBSWUGts+oXAv6hC+1ZyzyIfv0EE1WxRd8"
    "YV3geMJCvtWwK6O1CEFC2dtHkc8DwsVAEpGcvBgHDSXUmAWvIpAYPquBxfBdRhOjLzRimMjG3l5a9GgaerRmUw58kxHEtBc1Ohh+"
    "UCOHZd/VvC/pnksb5KHCrPQRo4bJVxYsTL7SEGEv19Y7GutyiPI/dzp0HNu2uGHd0CEtizrgw4ckiqZJuKA51jwwPZetwnJDaaCP"
    "HIC8RaAvUod/kcihhxE6JodsH43xyE4T8KwPb87a8uLF8Iwp8YqoQdbpgguqVFHcWJNDCWOCa0mDnzi/+eYHb++M+5weyuR13frN"
    "20sD5Z0tgTS4nKd8tVjX8Yp7rhlbCE1T0qDiRIv/ff9+Tw8L/YLLGV/izUljxvZmjACNEub6WkT6OmNCi+Ev1PjiDco4Q6mjSiUG"
    "6RU/v7qnUYr29kL19l86AQ+FKAHFViOhqp1mHNVf1utZAcGXDNifV+RlbZRmrSXua4KnXS4bqEVBbYTH6gciy159xAw+R/8RTX3n"
    "wdH0u7SSxpf1a8u0fRVoGjSTxsNtMAHusyhKvvnmC/XV3B32HWM1Yn9Ku5NWVdyfQ5mnsENKi7RHMrSoLHqg9DL1pp5+5xc41MSG"
    "TXqD3cuk0rrG16LRgyXkWiwjdC+1d7rAyLtK9e/fH2Jc6lsLOoIWi3H1dkFD28oYfniRcdsX7uittwuj7ZAQUV1v7KFeOK1EiYKX"
    "XVbMaEe1/wgPVEUQyz1Av/DLN7C+rl+/7VsRfmZ3Du/frxZqzHV2z8LHgtchoyIDGoQGR/gjj977yQsWa37gLRr69SMfaG/Bw95a"
    "Yf39e4xEejBvSGkXADYHQGfuPAk9gGrOJ8PyMJ1ed00POOnZQ4sXBqbUUt9DCgDkKeM+n3ALHzk+w+X6GkBIFXJcqv9iLRZ7SoBO"
    "Cs2+CEYaS/Uka1qvW6JklC0pIN9UMM4W5FeB5cXoqO/lCrGrQsxpedz/f9bTv5yf9fqa24BJHrHdwZu4c9z184odgB54S/n+/e2g"
    "3jDGXKCIWVoZYOgX0vDgi72lEhGBJOgo65iGYd287EQO2s5BoljVCIrtodGSwAZLt2uKGmSGcaY5SRdgns3Jyc8sAqMVTX32mOCd"
    "s2b4ZPmELJhi2hQbMcTbEOAxEeu6vHkuh90ditUGKOggaUAs5fb4/j1FD7oe0cBPFhL8wfv3MK+q2UYGen2mjcAvi4B3AHh/A/AC"
    "Dg1+2GG/oGF91B5+8w1CmgFPsjmlEM5LhvcatVJtAMOhmQ4VQ0pHjGNhAFQVkDtBPunt4log4vZZ/Gkqn1byyWci+5PFwRmN1Qkn"
    "cB1/KA91e7r3ZkEvbNbW0eJAhOM9+D4N1mvdQSk/7GgoTRCOUW5zvyjA/hu8payBasDRCpjyM3aB+wtVdB6hfrazeFuzRxZLpwGb"
    "oQ6PWTQ1WCpzaoOVTJgc6szj+ZB3b8wwgLnIY02QZb2lfhdfmF+Nkk/3C4uKu+2R03CanSUKd/D6+hemUz7q2rIHz9jN9EgmiK5W"
    "66Kl3JkreWSi6ODNjdlYl6rmu1+tUuqw8BmOxBnTVR+d0aQGjUtKk9YjrmChfaJJa3qwpr1XPomeR0GALmlHqI+Pp2x6pa9XQtMQ"
    "D5Lo+HhKHgCMHx0X1kyoAsgfLW5qU56dUqaksM4hwpqKXnApoAipYh18Og1FsEJERrwMQVgzbhjRaRpCzSvOrsALQ0uvdN3AOucr"
    "J/+Ah/PbkqZoLaFuUYN6K9YbE57sbhZklp7udOwNpyVl2FdTifziyBejqGYqfBfxd0NhhuNaYX1W1HHQJ4ZRg6LMHCq9CG2tsAiH"
    "RS/CwwcUFuLfs8W8fE7xScyQoTI5eRKL0nAahuzK1yy8T0sLCqBNFSjkR+YX5Edg9a8ZOFhq422a4zdzjtN1drcwTLBc+Uaam5mu"
    "AvJrypWnxKZcWaJckI19LhgvM+U2sQxKoQLuQcihdPLAUxtMolu2gLI5M9RNnwxzZjkhnrnOHOpkvqdjgDLK4ZmkjWf4LpADKjh2"
    "FyIRHmnvWYQHthdqtITmYp9NVESIugvLiAzmYndL25NlDQ2LMVLza/TnliEDq0eOI6/elFM2nc18t6juDLC5DUrLnM5FBjPUTPl1"
    "mjKEmW7BXsniCPBsfKvOZRJ7NUu7RwNP6RivFqGBqTYPO8uWDn4BlCybDqt5dFjOdIwKeqRUKPrl85sdScmaDcZMx7M0iXIE1jQl"
    "dy2WcjE7YiazYKuq5T4n0b5gRvlsAyE2UF8Vl5iCv+8uX++dxatlAJtggwr0a/K1D691w4nDVLSpF+2xovlTiKlsSy/bZWX5EJgK"
    "dPUCLQXOW8WlenqppgpiSbG+XsyhxYChnoQLwU1LlNDwoBHPJLu10+iplLICZAwuTRngbAOBwzClkvVWV6DF7aX5W7rGHfpuPg+Y"
    "uT/xuWAVFZ14NEqVPdUIErW2QnoIjFPY1tYxJ5zmg41KL+WZ0270OmbCIweilR0ITrs0ABodDYT0TMvPOW+nsva2Vns7U3szV3ez"
    "oGbeJFT+Oj1ElWHlzNdPZnajk2lcjIY2Bz0UcszCOT85iu6LDsiu+whAzOvhaUjf1eq7XIiiVtfM1tdUZkQt3O/lC/eyhcV04oBn"
    "kTctaED1tYXSYAx1oe+8PDWH3Wn6HHjXWJETxFS9KldTdbq7LQGEJlfUPUJxg8dLQuaNDivNXtobG1MyDzqsoXAeRCXden0q2sDH"
    "ii1gVlE/XqIW1x8tUeoqmuBvFVvhuUVDPr4ti5taAsvI28HHio1gVtGCQIzNWIAlMuR886ApZetIYW4AEZAXSxlKgBdahAp93gJZ"
    "aFI52wxoDz7MAKguPsByG/XxAZbOCI1p6J5Clu7UH5517OHoK+IFftAZWYC18OY7gUvgrUnf3F7Q8qGBFn3rEtIb90ZWm7612n5r"
    "MBhZHfrm2ONB3xlZXfpmdwbdLnzrsbd2r9+Bcn321u0E7e7IGvC3NmmN4Y3CYjebXrNJ6SLgJwcwsAHAtgTQCzzSEwCOx0EvBbDf"
    "JTB8AsC265O+LQCEmjsdIgB0um6r7QoAnU7fbvkCQKfb7bTaAkCn3Wk1fQlgp0mcLj31zYiArxcQhIjBB8PpeWMBnz8IBgNfwDcm"
    "QbPbFvC5LdJtdQR8/bbnQc0cvm7Hbdm+gK/t9zw7EPC1gm4T9fMZfC0A1mkL+By3SezOCJ3cifkNoNGgKcADUJukKcALiOd6rgAv"
    "8NyO2xHgBf2e03MEeCRow38CPN9rdptdAd544HiOJ8BjtmECvF7g+I4cvnbHdm0Xz0R03QoIg6CHulgcwoD4fieF0O+5KYT+2O3J"
    "AQzGg2bLExAGg14rHUDiwpx6AkKv2XbsFEKY+3QAe17Tp28MQhhMu4cuVaj+kwRwjErRYgiDlicxMPBJt68MoQ/rIgVwHDTbEsDO"
    "gNhjOYSDXs9OhxCwzB5IAJtQnkgA+60Ozr4YQse1WwDgKZmi0xg5yR7pKxAOvFY6hIGtQOgTWI8SQhewTuIgccctuy8g9Ny+a7cF"
    "hK7TbdpyEfc7bV+B0GkFyhA2oV1cIwlxp+oadgV8nheMA0fANxgEXdIW8HUIcX05xU3fb48DSWTa474rp9j2B+1+XxKZoNftErmG"
    "nQ7pDOQabrUJrna+htuwHvDq2zt15ykRJEEg4QsCNyCSCHaCVuBJItgj/WAg4Wv6LUIEfHZ33PXlIrH7sBKaEj7Saw9sCR/Qol5H"
    "wgdEsNuS8PVbLVhqsP+/Pk2Hb5CCR2xY0RK8sUu6gSQxPd+nwHIa3R/7QV+CB4uCDCR4TSA5PQleqztwHUmje51BX4Jne20Xh1aA"
    "1wzaAzx+4q0oH74g6Kbw+WOiDN8YFi2+MfgGLa8TyAXStWFwXQFfawxVy+ltdrotXHScRPtt4vfl8JG27QZy+EjL7cvpdXrNTqdN"
    "uRo/PI4EhEgFlREkPXxjEHo9v5lC6HbG7XQE+07fS0ew2+p2A7nLtWEfw72SE+lWq4+0lBPpXst2W5JIO02CuyOHkDjj9hggfBNG"
    "U2D7+RwjmqUQ+mSQjqHv+90UQq89VsbQ7fXH6Rj2xx0vHcOe13KJ3Ea6frPvSyLTGTedsdyH257jDzoCQtjkYJtG7nm1RL0DDqEL"
    "MEoIgxYsBDmGZODTbwxCvw9jSASEnt2nI8ogdPudTtATEA5arRaRG3GPwDYtF3EXIHT7AsJO3/H6PQFha2z3ujjLwcqbxKgMz0AE"
    "TkEB0VVBDDq+nQ5iYLvjdJpJvzcIJDMDhAU4CUkH7WbXb0k62HQ8V+7F/a4z6EtE7NmO25OD2Abq2UY6s8CIRhK+ZpDSaeBkgpRO"
    "j4EI9SV8A7ef0sGg3WviZHE67bX7A7mQ/XGz15MLeUycfkfyMgPf6eF+xODrt5x+W9IZqKvXxCFcoo6+3OkchVkICBAmhVnwcRzE"
    "PuK2cRzETtdz+nIfCdqtIOW1iAOLt6/ARzdtDh/sGy1Jp/t9p9WSU9z27I6DhCbGWF4CwD5goScBdAAjBxIHYZEFkhn0xn6HOALA"
    "QdsF8iLXMVrSy6243et0Um4ViC9Q55TSNActyc3YAVCXdCNp2l2nR7lVV1LqAcCXsgotQEc5gARoPlI0vkYcv+OPJXye23LlRtcd"
    "95rIunL4xgCfRMBWD+CTlBpma0CHjG97Tr8pB9Bu2T0Huel34dxL17CbbsQAXTuQvBZMdhsZWQ5fG376kso48COpDHKGPVfA12nC"
    "j6TULex0V8DX7DXZiDH4gJw6Kbc/gB+kg3OygkPV1AxiB3+UIewgyVVAVPhp/JEgtvBHA1HuxW0bfySIXcbMchBp3ySILmdY4wQP"
    "WwqAAw3AtgSwBwBKZsYHwuFLHIRNqjmQzEIP+OuuJwHswZmDSADbbTtdJM0BwJ4eSDxnoADoAYADPCoKLUKzIg9GHzQJspl6BpNc"
    "08CbJlmILqluqhodVL9zLS+An3CniygVYgIvVVTDIrzcWyXUXILWI8Uz2JszfjKFM/qaD69MQqEKH2SZ1qRpLS2tRdPaWlqbpnVs"
    "vQlM62ppXZrW09J6NK2vpfVp2kBLG7A0rRsD2g/DoV8MLZdFiFcpj2AyhrysGOkz/KdKCsqF5aLmrt5Qa4OwXOTr6cWaXDCFVyV3"
    "8aZESqR/VcSM6XW5rVwImWR+amEhRFRLt3pGoWGqtqVW0Dc03xVSx80i1PzSsOXCoEgu5lGJR5WuCTu3Iqpr0228xzGIhow6M1tc"
    "ReR0Z0xlOyYxZoESzZbl71a5RjGW1+4Bql8/5e8RTWXbetmOcnGj3ypmaaNJpSYreGyngsfWRsFjL38ZlNWyMQ+ZVowTlLzKTfWy"
    "hco32e51c3LVYBq5zHxr61bToncLbs0KKBubEK2GG5uuBDeBwJ0Nbal0hJufKKJWnVIKVJj9yob/rJr2iEq06PbIZo6PnL5Vw3/N"
    "Fnxs2J16xdu0KnqEGeUVm13T1Gxxf0O1V+hGLZR1lbxM70/JX+NXdkLDJZtXbhEXdM9qvmgxqslMoDitoqpuTFqgRCFGU4/UNGHo"
    "F6awV6QCk7ZQqveSBUTFL6kvuyUx23YxrC8K44zboh2rXa90T6zp1BSiWV6rW5lhbR8vUTvevIpy6rhlfMZ2m/0WKhvmxbBxuzQz"
    "CEYEzytgawi+tjDaZ9HxoxUX9l1z79auW7q/t25dgUeFGg+OqcOAs8qkbG2hn4JzUSdaV3rTvjOpqqZQU3qfvB0NMmjK6xk+JlXZ"
    "rKxjLsbUEc5kFHG6kVEr8bML2xgL6BReyo/RdJpZpX9y0iPAeaColqRHoUs9jWtFD5hR/yrkM+Wd0DtkF/6hhYmgGDX+f8OpIyOF"
    "TBRm228as+xGjC+Qoq6tRbTAQdhOx0fg2F9sLJijgvKReDvV7bea2ZFoor/SZgc72ikciz46FsWM+93LOhjqznah84ySQgbA8IxL"
    "/IOACp4zQKPQnR/BUX7cYHIHKpTL5+NbFM3IVCqZqC6fs6nk5DqbLXPOlpKTH5jb5pxtJSenSR27oD9qh2jOrjlnV8nJZQg9c86e"
    "kpPPad+cs6/k5Lv4wJxzoOTk6DUwz9BAmSKhpCSPDMVaSqkEEkpTrNufhW/3wnktBqTJyCQtNQh7rd/+Z72+ge0RpRlebFd/r/vP"
    "er1UbMpGnCJ3s9OxxD/Y9+olm5go3S8rjVoLb5NSDsgkmtmkrGzQ7bXoXr/1ZktberShaIFCYcpEILs8J/c5gzJHz25Txm/cdWch"
    "+pcM5xOyRDdCKiejZlQE+6iu+keRumqBRjAUeSSLpBS9RB9ZPYBrDPg2hsuM9d/JyrSipjMz+EnpN7qBnjHbH527zuWhDK0RDmPO"
    "jIEN4xONOQWzeEntGEy8e7YfNE8xG1+SXR7SYwIEhnrkqjQDUOJxEU6X2IpQDCW+btXbTE+gAmkvwuwQwX0yn57+kre/UcZGNXqc"
    "acIYMwyQaTMYSiYTJKZrG7X49LgCIJBpMyBKJgMg3NrIgGFAXVH1wQ1j4h9KBquFnGER99SUDJYinVW5q3ZdiG875gzN+gUYE5Wt"
    "NDQK8o+Jeum6k41mRbX5vPcCkcMkdjBmZJ8yRLbomsVgDVbaoDFnpsVNqv86JS7MpUtWCrMps190z65fJF6A5cEnsvjaeB4qg3a3"
    "s5Rh2v8iFmoGxKkOaBajdrH3KEei1/IiDh9blZDntdQvwMfmJqQpgaqsTCFYZYXycHlluhjS1KUIJYx5ixDBmHnD9BsHJ0dIdrcn"
    "Kp19lrOrFquEASxrTy23CQs2QVhergTE8oImGMswQjWv2owTWu7NWKFlL8eL4uHK4sbuJlqlqMGzdrWClZCD5+1pJTehx2Y4N5Qs"
    "A3RDUSOkZUii2a5txhI9+2Y00fOX40nZuGUxBUMjlciVqMK4VGxjb1UwhWftagUrYQrP29NKbsKUzXBuKFkG6IaiRkjLMIXnrIop"
    "evbNmKLnL8eUsnHLYspu1pilWJJRNKqEH5ixl5bZhBllUJWVKQSrrFAerjI8SA1RNyOBknczBiiZy6ffPDjZiT+fkWyl48rAyCRX"
    "O670jXz5xuNKMawbS5YBu6mwGdrtLIk3HlVMZTYeVEyFqh1TTEOZRSKz4Ej3rLNCf7Bo6SrFFeV7TNVLD3YU168lBuxaYsNeVPne"
    "w9QEv1kp3rQUPWylqsxFYkaeoAkQJpX1dnP3I3bDbte31FkxVOJ06+e+K91Cb02eeSqcYArRIuWcd0AJVrgYIYoq34QM6WFEVlI8"
    "SoUHASEM2Hi8LxwcceDcYWiwaPHAmCveNCzizM4rKEEc05lZHISqHGoKR0Thn3cYFF66eFwKq980NMrRJK2meIBKDgXiFFCFoy8m"
    "tinzuAulZaVLCG1R9RupbMqXp9UUD1MJR5yywBuZ2sJRSi0Hth4iLFo8PuaKNw2O4FR5BcXDYuQUVdZwsrMJyU5ak72KXF7PqBi3"
    "HS+zRouLcH5p+9jcVv5tUHlYC02JvxTrdbE81EVO6t+Q9fk78DF/J8bk78dj/F3Yhc9n//+sNvKtd+Qp9TTilWlPFKlWFOkvCF2o"
    "p2af/kbtvM0q3EXeRFNVZ9SiaZm1aOqqkWSBKjS1+fZPVdVCzRBIOrP0XG6sqCcnYYJ+b1Sjc0OoEKZEFK/GPHslWw5z1JFiY7e1"
    "dXenGC3SKI33TNjCo18kD/XgHuoWU45hdGTeAn+yQputshfYz9KRslkYVYkmmFVNSvSh0hX34CqKxlUUjasoGldRNMwamh9fy/dT"
    "KPRmLM+zN0EmXfCi26LCeAWGadcUwf/W8UqsWTQOpwSDCWOg6oyHh6sYJpc4holubaLm1CxNCntfaGUiLYzXZr8NBd3MrtcLiq9C"
    "44zq0eOKVvLaeljNqz618j/Z4MzeqsSXeRPivc4gfM79PMtzv6I6/cdi9T4Zw5XlmfgQltoGaGNYwUSA57+72bkTz3lbjHpFqHdk"
    "EEvZrEt6gNqdgxFrTF9gueAdRfEp9IghOc8HJi6bz+ZGSw0VnzZm3oZ1x27HWmQO1tVYN6h8VkCpHOrXv5LfvR2tJK0LD3BhMn/d"
    "PZIOTPqMhsM5KYn7kYsksyV86EJ/BnP/IFfPZViD5QeKbXu6o/OUlA1YW+92CyO8JG9CcrJpmX/2obpkwOQce84dgKQUvuA0IPKp"
    "nyus1Mx0V/VUMTAvu4k791UxZ4pF2MWbW0uIN4WprSZUlAu/n/r7NHirY85Ea2bmbWcgUUS6WCWmluxzCH3LNrCtRT8GN3/SsyqN"
    "L6Z8agq3WYUyejyRR0lmcD/M2K6tn7f1KiBxdDMInKYzj2CpnFvE/upt15UdZN/NYt/LpfHNuBOzTfGyDW6yYETvY8j4bCCynFSB"
    "+uJJZ1y/SuDs2UxEpSu6zLkoZ1xr67mZtOSI42YRjE5Hc1LZbLYNMppMbXKuN5P5Y+4EG90QjSx3uYxOnvDpTWOlyWFPhQLZCjOC"
    "G8fA/GSkXAVdTJe1yU0B3sgVtr3Ll4+LP79c9NZ0zmiIOfxQHFFIFNmGkcoK9ZT6jPK97Hcemph5R8kL9bJ+MgzyNcOVVrYUN7w3"
    "iuWyeY3CKTMY5hvsgsbzYrZsxkJRWzbjB3L8Utpjg0iuvNu0QKbvVVzFfCyfLMx94fDMKGU2ODdUa+WfVcBN+KRl2zTKWuaKA62V"
    "0cda8zpTjZ8scDBpapCNqB672TRbev4qE2YowQd4XLDC9RKb1rieO+X37i0ORv+owX/TsLHYd1dJ5EWzxZQkZJ+Jfi361Q/fwGfP"
    "jT1g85mEmX/f58NqpbUggRtHb7UK6IfZapqEWmnlY1G6qTYGTrIkZH8e+cQAg+8m8DOekv0gnMIui1lioOWhyKXm0V72E9RjqX1f"
    "S5YyJ7Ykc8qXXE4GFo7zPi5AHSwOc0iWxC/NQpPeJqV58OPYXZZ8P3ZLK6DHY5qDndzK8+RrSSbamIlKyHSqfE9HyvAdUvRhxxQ6"
    "mPhrYhh7UUaZAEz5Pll+n0xqZ7QArVtu2cMaGrddo1/W/xhZP+4gNCk+vBsJSk5Ml56Nt2WF5NhsxwxxT0w219my855Mmdt4Khc1"
    "nKIbiohU01WSx8216NMtmM8q/cq7LRLZDCorxhvLDzFcmnqeDlDRDWS2igLWXRvmjyEh23fUGEHmO4PzTDe0t5rNj1IdPc3VcgW3"
    "yUuMnPkxEKUg7sAF4kA+jMClmeFkGS62DTMjfJjiXsbXc7VldeFUJZ3QTfa4jm6POxAem0qOr5ybqoCq7FhelbSdkwZ9ANLM1upd"
    "LlzYZbEKwcRfacNCZaSnUThPCtW1xcg9IzgOqQKurH9JPzzIaejSlVlsyBQtkwebRIdFkR5MAkZFGWQaudjbB1nxIqW3R9Hx8ZTc"
    "XCVJZFKor0JZ7xcWKo7OUtW7q9ZGkSZAVjasCQg69j8v7/0TO3YMz8I5eky4p/IJXAZ1KHzw/wV03PiHp9K7/oeRGm8pFd4kZN4s"
    "Na4sB06JxIpehlSSPKRn0ofb6QiqRa90Ai9eJ3BrGdLFKRHSq+vjcI6tH0WLytxYwVaq1HYzgp1gdv4KvRi6kJOh7GMsIkjg64S+"
    "Kmfy/f3FW5q2r5CGWjYmke65pFO3tMBErXpdHuXX1p+Zm8pbhmiReh+y06AxGlud08v5mUq37JWZnizMavCriwG0dMiUETKAUp1T"
    "vLgho8OFP1sMWdmS2m6aNi6o7boAy/2H3TR5mH7LJb1e22Uj3V1QtmWnlCtWuybiSKUmiJlYY7rxYZXjU6Hdg6J/2cxpXLbUwLnn"
    "VQHOZDZ55y7O/bkrf1mfldfuS+0Fm2tbVVP25+zWI1gLky0PnOcQzxkCEG5pIrv9Cmcd/Y24y792P49ZvM9K1JadUUqou++e/kx1"
    "T+GEDztoGsKPbYTWCSGvb7un+ZCSBtjLNFg2UWc3ITuKQ0pNSqgrjcNPI5IuVJPXgCoWYBfrdZtELqb5uZT7wIUFp5whSStF3hkj"
    "enmNT6uqHuUpUJPSJk4puTlHC2MqChy7hqDSnJ+udthNwhl5Gnqvyfkq0i/PGHD3VM8J1ofWU7OSyHcrRPnY2jfmwOgs5LdypUqm"
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
    "znZst+zzLcPtV1Nef1nuTHgB2uwyNfrwh9xPcGAtO75ZlU6k5z9LohHsudzmhSZ+H9XaMzScKsMb5bb0SzrX8p5IjODwbEoC6DK6"
    "YhhZS5VfoyMoxEqsozQXMD/TFdTdp+dP08arRAMtvFlN8zTrxUJgsSxbtuIUczhqmCJ9iE2gmCHQ4dqOG1AZFZwW/X7w8+EVgFkA"
    "nBRe1DhqdSR9Y91iw71hblulzJeezyRdzdPTSmJXOrhbbB8XNQ8FPTvXVEwleUiv34y0pFZE5qqex3XFGCr7yAe6CfNnSyYrLjjt"
    "mJgPoA3c5FtlPDr/rJvDTvHs24appMWahcGs6OdertZuYTQrWoCf2yVIStBqWA+1NvzroyUF/NuiKxibS43Wt8VYKrH7Kg2mGj1v"
    "11DDxfVuM56sRFeN47fDiBb1hw8pi5hXeTzPTsl0Gp1sMZ6ywLYDygsWjyjPsM2Q8iJ8TBXQthzUwk7xUSXLZbTcCk1lwLpKg5oG"
    "jtstLm1RnduMJebvpsHrdhhFcy/EWk+Die5mG3Lx4dPNth3b9FiPRmrodRr6b1OnDfqqFXwWdwwGI+VhU/N+R3bq8aBj7vHaWn2s"
    "/ftzigtQcKjxw3hBNbm20j/ZrGeCzjZmlziS2lUwtE8QDO0qltllimUGe8MkXFQJybN70IhtgyKsrWC2naY8kH63up/yGJYDWVZW"
    "+86KN63MCd2sp/RVQP8zSSvVjQ4Ofnybsw3BVO0+BlyFDw7/Z8rk4I3QbqduDbZmTmlB9iFaJei7Rs3Ik0q18ukhnOV7ojpQ57hK"
    "d2zv9N4y9POBDdgFqLppSGgSoVuUCq1hUk/cxJtsumcoUURdAM4BFclK8Qu3qqq7wAYp7xbkKmd/MAvnv+h25RcVsW9tzXYSj471"
    "u+bm1kFEhJ3J03KmTccMTatwF8WBrQJGm2ncJbDWL7kZulXGi5uOHxuNxLsm23J0ByrxJhvOmIrst/eDAHUez67C8V5xoEUxva74"
    "ycsUGzcb8dxkYFc8hLDYX10t9qvFfhV7+4q+XMXeLuXRq/H6aLq9Ayd/adXpYJ2uskr7OctU6uukSNU668KCXrhuMFIp8VEwh4F3"
    "pwjaaZbzbSn6K6XmMnn7DITDaJNbRakNYBl/jE10/GGj8X4M/rA67d1RurZtyPe8RTz9yJI12/KrOPCfQRz43fzwG5zYnydO+66R"
    "4gWO3eO+v4rmnPoG2zzVLJvR9i+fTe+jeUZYTj0Gk2EklApl3HoMMA17xuuU8puQkmm9HybuEsMupASdpd/BgcjG83wkIuttQCJY"
    "wG8vmeW7Zk0i5HBPliHk4drN5w5ylzqkMddbZju+3ZXm2I3Jg52cuxRHpbsK0ncVpO8jB+mTPlY058uXglxUCqSpL2AZcvDchOQj"
    "R+r7gJH3to0C+DcNzciCVEorubzacSY+yLkjrGylCnNpFcoPZ1fRdz9w9N0L3KH/Opvu5Ytz+/fcKnaMgHs59haYvFuX+YxUeGy5"
    "OqhcHVT+rtHEz7kVf+TDTSV+xBAgXbPH+ty47yv2+2Ox3ycZPdYdPC5us5cU+102OmMsCqIpdSq1MJoivaZ6YUvNFQ9T08T8dZZ+"
    "aauGrTzWXfqmLgSMrgVoRZoRJFYQa7dz64wbE+H2RgyB9HzzIUNJlmGNADDnLkjpXWaI8h4WuFqtPyxyP4arPJwtptQDn9G35JX9"
    "6IXYj+rYVqp9SqthqqdmhWm7U69r2LdDfzDOvY4hW1RSPiv5AiqSVS5zZXF74Ra3WyAhq+e8WLi5T5XwsLiaDfNjKFKKi8WlroyV"
    "P4Sx8hYIySs6L0ZW6VclnCyraNNMmQqV4mVZuSuD73MbfG+BhljLeXGwvC+VsM9cRelc5LKXYpy5xN/TMn4L9CjvRDlaVOtPJfQo"
    "sNppV5wCY7FSdCkv+fdzLbADyhjjaVZEmdLubIUxmZHcafgrY4upHAB6tK08RHWwPyMJWcaV1HotcYoWZ2gmBNW1EWjiIwAb9S1N"
    "BQz+fGk6c/AqNKTuqSKVVMHpngI5LXWU8+x0Hgf7a+vOlZ3MlZ3MlZ3MlZ3MlZ3MRdjJFMdq3xjs+i8UCO3KYOFvbrCQi9a1wbSg"
    "opHClQVCzgKhktcdvCoi7vJBJX/RW1sg3M77SFOuAfUrQyWqFNdX2UHzopTNL9C42EYRoTg8/AWopZxDm6aiLsuOqjdGBiFb0Hxl"
    "vLae6FaLipsjerKPpnEuHtnrtIgMC7GD5tM88smFB0U07hVpmPuLU3jNEva0jS3iMCrLjgdy4O69MbQgcvRPTRlq/Kq75mwT92c7"
    "K9Sys+kljcEE6HREB84US+UCUGsrdNkq0G78eTos13Q0VK0QSJ7D4sCrC+9C1LSEzkazzTQbbkgKxEVfKdOOOjO5RpVpRDHUH6Z9"
    "T1lR2pZXOVhq5SDtWVJyAcHdyj1gXRTBPLdW12aimTl7yYn/7NbGhUXS9FZLnNanwNM9I4tomVxoSM3CZv9YzRZHEbb6gHnumrlv"
    "dWdzsJAeXS7zkg8Vc7acehUHoV0rO/n9fPCmViZ4kxbkPhMleTOaGILel4SuNUWDKs2/th4bPbttRb0W7hzl8Beq46sqS24O6i0i"
    "8WxJ3INwGRuDfCbR4mZF3Jy6cUGcUIzgcrOqn8rLYapkNoQ4/0nwb2WThEFxFaXyjPnNBzWseQqLmV6oVbtP25JPawjl1WqBrjZI"
    "UBfRYhM3nstaSYaayV0oRBX58vK2bI4U33OSVpElZREkyc5YSSewVR0DeTg7Ie7rMnWVTqrGwRUAZgS6MCsq487GAAAvxV54OWgz"
    "mh+Xqwx2VOU5oTlAcegoowV+rgMmIOfd7WUSD8ycyMWh0Cac2BLFNqKHDLnp0IBP7nIZnQgnylLV3bDrF6MkjNLDDfzauRZ9ClUl"
    "J12c1Hq5aHxMn8Rg9GgMCIf8EfTsmR4p7wkcCSssF5r36CQy6C13FL1lLfcE8L/i8mAl7kYrs9JfR1P6kxo172RXpOlCM2u6YIqd"
    "WHTzT53dZA542diHPE/+2l5k1OVWH0uZ4JNd6WcXPx/C0viR2hgac+qDyPPfzQNSUPNtMeof1u9a6UX+5xTtpNIdeXFUbM0XtdPI"
    "LkGToZKkUHzGbm0ibirObMy8lde7WV6n6VhXZgLYb2aPdNuHgL2s4uBcwLzK0itzXNiCr9DSz8ZNVaH3PGAD/Wk4dUXBWI1XSGn/"
    "/U9k735p3X2G5ITJvPIyGuCUPeAFWdDUQoEPTNZxOFdwW6yK5vbiCxH4o5JjURYLNnB9HquibTPZ9fPdAiu4UklxkI/BWhiv5fJR"
    "6p10y2HYfrlSd7xSd7xSd7xSd7xSd7xSd7xSd7xSd7wQdccrDccPp+G4heLipfDHfK/IOKlk692N7YHGftwqwuGlPZ8BTY1WFWz/"
    "TA7O13liKn3PiPvFbvFtdWHW7LWKPC66cegTUxVbXEwX3TAH0whYkfnxzYrnbZ79UBgm0uiOTTRLROnAnl3Dn++Y2THAd8zIgwl0"
    "+inr3dBO3fgoOjRb3nnnHfYU69fmhSocshse2waTSNjDWUtWPq1V6L+1elsB+EFuiXe6WC/yBpa7YMYLM7z3LXVGilmEkpdBc0HV"
    "yy7Qmd405Zs84O2sc13psrySGsK2U7C1f8Gt1ay3UuXGSX8yn55KlSk+ESdhMmFLgqv20l1Lfv606g8M9bQVm26yctXKnnDB+N9l"
    "1d50fWQkNgxLekEgcqRRWovGKq1NI+DNrBVOCR0efxwlZjYSh6uxpEw3p5H3WtlmLX3XtZiGyyMuhXWUtKxuO2136i7icKx4WzR8"
    "O4oWj6RUV7SjfL9pHlwJe462lqgtXVHZy05lPym5dMP5bsxvyjDuUjicA3e+qaTJc0R6G7JdfOzUg0Y5o7q2/tza5WUlhysFPnm6"
    "6JPHnYczOkU3S+7f9Ou2dr2wyja7ifthp2saSAZqeJHaNQwPMW68Oa5dTq9GXFIJsR5VH5Kkys5fHlEt+ioQF9sV5PYPfgIzNFRS"
    "iUoGBHfRVaFnb6ozF7vR4a5c8B+/aK3x/xt2H6YZPzj8nymT065vRkLDWlpfXrezv51bU3tt/bqDNIQOoNBPEQWajE1yw5j46XG3"
    "xWdkv2mYkiZOGyUyktBkpwwzYPmOOUOTruHfP5Z5wjYkguv1VbtEFouZUQFq/mQVXnV/3nf9a+unnUiu6su6Am0ysCVZhQ+5SdK9"
    "zZFbJZ8ESorjhCxy5mO6vyLMkrf6+MynKRvRCfp4xIxWStRrSjVo8meZCtYu2O7jFWowV1nbhjnfnQbwys5pDFo+JBzTMsc/Bwhf"
    "q+D4Z/DIXn2b7FbZJpt1Pu5UVhpryN8XPgN06yENTc4tYlXXkG43sba+/gikg5nePAznryvztp/FGqa90pWxz72GWa1XK/Sjr9C1"
    "RSY7HVzcMbsK120aOZd1YUEHhfladdtl7WseTQwMkAH2Kqhg0JPaAr9yKtu7+AEoR7lUA1KzzMxZQ2j8yz4fgoxfn0uqswu4od8Y"
    "X9zwrSXyAEGSB8rU/nI42ney3LVB2Te53KsLGrpaXH/9xcVQdbMDgg1cNGDLBXJlggsssSL/9JSHSk5rRS5kzM41ygdkKyTM6Npd"
    "FlwRXxXRl2BF0Pyw1pH8Rk5eKjgTPa/JsbJhFDNu6m30Eb+ZUNsbqfR8VyrNXPteLDW+vFSPQvj0nBTgYyybS4Wfa2sp0WvT3WwP"
    "twyDDkdndz9DRiFrxgDk7TTvnklcgnIcKL62EkjiFIZ4EDkKQ0cYPIOLMiw0hHxtCQ/0540+sK3b/c1BiLRIOTtEGCqMQtNTLYUF"
    "NKXRuM7i12XzgV+3AQPzcyDwUYBQGgfnLKK3TyVQ8AzbAMKLcFj4mwDHx7fi6CdKwI6tQ5sUhMXopQbiAogtwhsY/OuXIKXpRgmw"
    "YLKVlVNVG6ASMxu5w/YzrlyMZim1InuWbaxVLshD1WIZzRZZ01WcsdnMnfvPSLyIgNlDx1WMY6d3STjI7uTKlOzKlOzKlOzKlOzK"
    "lOwCTMnWVjS5VG4Aq0V13uZkmLUS2ym09VVU9quo7J/Kz5whhHnG29znGcp860jmKOs6OCNvqHraLJzfF3d0bEjS+E1DlulWzsEW"
    "FRBTPlJEgCrMatfE/TTNoMeayvoa1dXxVGF7M3cvcR7KWqyaJyQFUkm9TEmGClIPP8wNJh/Nij6kFbUctCTMOM/a0onzOeKvW+Pp"
    "Svpr+yzc4kgMFEckOjH4s6VruYxGAYsKn9EUWs2Y2KlE3YfTJZ8kbjgtzanER/9Mg73/7eOvs1kuiT3YM8SL/IsHbb+KjP7RsOMz"
    "Dad+Fa08Dcb9wXHkMw5x/neOHf7B8eIzCzj+GcX2/uBT9xkGBP9MYmxvnLq/X2BuDEq1nLnTC5eLasoR2sCb9Co2+xovH7oye/L8"
    "YJlOrNlxWVvTiSEE03Zn9VyoSu2suNutnb/JxXJ5sSoXTDteb/3lHC9vc8Wi3u9ue1WiB6/cavPjq9rgQL164UqEyFx0I+EuALeM"
    "aGkFuJd6Ve+qwp7LdyndxXXVzcjkSb161zZeWQkB1zYL8jKPlzGuU9YTUFXHKwwAVWYrbflNEtumIrEtzITG0/GsBDq2YEs+V1xd"
    "Zq/Aq5y41+ynPTNGLSqj1dXvPke396ZgUsrCMij/F342LUxThvvl1ey4u+24jUBNJC0AUxlvNuVvGfl1E7uglt7AAigVdu3qdL+t"
    "w9K1i/abcwbsUFyXF137OLkrn42rsL370DG48o5NKo1aCXXdzieKVvT+1k0PCg9KOSa8oKe3CormCvVNe0gpUpTGHgHK6U8+TaSB"
    "ItUOc0A5uU2srUACnEaidAS5TwNRZ6l54ZknG/q1aDvdFMlJGz6VqqR9TbFne/VHNa7uYos522ivo4S6pRfMmkn1DoG8C7Xcq4aR"
    "+ihRazfFq60eqfay2O5k1F9xMnawodwpWq8x6HbhBiPvZHeZ6PvV3AZdWJ/vl0WEubTeeCMXl6B619zk7nPDKXU6o7k24XQPefAY"
    "5uofNfivsdhPloTsY/QSeObEj77WzmgO/G9/f/GWpu0rhKhW7nKrU7e0QDitev0arXD9jxHFo4cGnahCArmju+0KeuVra3alH36l"
    "H36lH36lH36lH34VauTiQo3gvlocamTbeAVw2AsXOUdE+ThgWwViWFuTHSyniwXVxqNiXo4nAwFsexTFIUXfGmQ7A4K8E4vsgZMr"
    "7nLAbpFppTu8D3aEOWevNdZXB6n6eaf0gM7G67KciVBqPl3N5twzXc6HRwXjwiVU/iln/INO5aWZpnHkn/LFVQ3DC/BOw005zEVU"
    "STdwl6/CMXPZ+UPZ+DYgEAtYUpVynHOBF5Evtgzu8tgpu6wDEXfl0lFm1rVnBAFdSjyW6uZL+uHB3A89Zh1yolySeEXuMOJomVyU"
    "8CSrp158OM8LUS6NiGQrsUhGzvMhVO0/kOBk4R6Hc8STo2hR0WNLAb4qdd1k7mrOWV1ONENX1UeWz6ytY+ALEYOZECl+fT5XL7od"
    "SlOEo341OXgy/gO5Zp8E4Zw8hYMDWSan1hvzh5DE1qn8dEySJydzUeY2ib1luIB5iK1xQZ7D09k4msbWW/l9sYySCGghaUzcWMlp"
    "HRqyLPjHB/Gd+WpGljgx1q3JwR6xEmteP/g+qYXzGrn+akJTzojMNfzCxov9IDxeyfeTZZiI5zfudEWG83V9SF4kLw/m1snk4M1k"
    "bw/rgXqRf9974y5rc2wgef/+4GxdfztpeO50uodNf/PNLWxzbiUv5i/r18Jgbzypp4WioDae7CX1+mFxmSVJVkuAfl3fO1tbNxZ1"
    "GGlk6GeLaA4zHQ/PXM8DpMVzwZ2F5a6SCD9OSUKGt+H9jZu4y+GThTWmYVNewwNGClmFwz/gcQl8tbdczcbDR/DGqN7jheW5S3/4"
    "lP6NVkBzhnfxOfYA7xgFGj5YsFuucfR2+HDBDkHPFgzVFqGH9nXvFsIHBLV9vElf8X56+POCjfpy5ofuNDoe3pcJi2ixWgyfL5i+"
    "xduEFv1lYfnQDTYtP7IXjEg9/JM+E97gD/DG6vsNn96EuEp+hUeMjPI7/F26J5Dy08Iifoib0dcLix6+kF6RGcrmyGqBq2uYzFhg"
    "CGYfOp8BZzOdkmXoDpfi+XQYzujyoVUMXXgJEpcViOBlhsfHmD+InnvwPp/Cypnx8+UUE6iwabiij6sExzIe+uKNLt6Av7H4Ywv+"
    "Nmd+XWf8NUoWwwl/TtzjeHgsXtAO7NXMej2PxsM3M271ejqj9tQ4g+OZNSPHLh3stzMWG+uQ/cWA17fwkcF7go/AiTBAjuBtNU1C"
    "jhR3ZlZqL0oruT2zKEGlhttP8OXYnYfvaAZvgvEDX8+EdIEh6I1ZSrmHf8x4RLhH/IFW+hhf4vgkQiSFZ5h9Wv9deGaXg8MHM3RL"
    "cgzcR4wdeJi+xotwPoccz2YWns4jjvTv8BXjgAxvwlO4gAU0/HnGI5vDzLnD++KNQfR8xjfj4S/iiVd1D94B9bDdH+HxNXzD5D9n"
    "TE8C8BSeFoT4iKzD3/BlGorCv/JXZPZ+nzGHzYiz7DEefj1DX2F0GMgEH+NhQv/S9TDHx+PhEv6Q5QwGcToMJ9QMkHbBheeQLAlb"
    "kBG+zQhi4zCG5wg1mz18QBaIwzMV7/FJCJg5XOF7RGO9++wxgZUfTJhUZcH+8oGZsTe2bCcT6024TFbulI0idOp4wrbVe4t1vW4d"
    "4c5GmWK6UQ1HXzk9x2t2RxbdsuC9Pe70uj3gMOaHQAxgw/oqoP9hyk0X9z+ZwH0Wjb4at5stpy8Sbh5jHp+0iSOSDiOYFEj12s2+"
    "42mplMmCTwPPCZwOtnJbKyIaQ0sgyhp/1XPbATL0PEU0F3jtkbQoG31lj7vjlitTaC5/EDRJa8SMEaHr4854bLNX9n1MBsF4REfc"
    "oW0PBj2fvTfxve0FvT57b8G7OxiMETZ8byNkfS/waR+OIAVbaDt9J8Br87l/mAMNU3/JdQtTb2dHFhMf6FBj0qPMpCXExWZtu9vr"
    "jNnrYRQkrGsu6bMkMeS23Wm2BxRcVk6MNWbic61WpbLbX/ld0iQd3gaTcGVqeEajYEAiZHSJzxIfzCnf+hXxg2bQ5vVS6oW97Xpj"
    "32aJaGAOKCy/tb1eq4fz+fqUgdXse/Qt7eCABDQl7V+b9GyKyrSQAA6ypL0T1eQ7xxrL9w0Sta4FNk3TetZldSodc/0+TTP0y+kP"
    "kH8cu1Ms3xx3Ol5HJPDeEYf0gp5IFB1sNtvtAcEO3hKlBZAsI++mXqXe0zGxicyf7yxLT/vbgRXSFsmyy0HgBH1Zv+y17/WRBrDk"
    "bMc7/S4ZwBi/CaMpraXbbNteXySIjg9IGzvOEkXH26TVcunM/ixKC4BZRt5xvUqt48QGkmHL1nIdZ+lpxwcwAR2RLDoO3aYd5/WL"
    "rnldr4MdZ8nZjncH3d5gjHbox8BbukhHWs024jZP4V0HWmUTT6aKvvebjt9tYt8fyQoE0Dwr732mWr37Pd9DeiCazPWff0gHwIe5"
    "T9PlCADRwnERbYhO+rZn+2l6dgx6XifoAx5NYW/E+Wx3qYwGX8XEd4BrHrMk0fVWt9O06bQ/ZOUEsJiJd1qtSsd0nzR9j7eR6y6m"
    "pn3tAcHqsUTZURuWtahXTrTjjT2HJeam2e61OrhtskBWsMN129RDJksQk2yTDnaTJYqO9vqtAevoE1Fa7sI0gXdWr1Kf4I4fYHd5"
    "a7kOs/S0y4AN2GWWLDvdAvxO65fdJoDhjkjOze2gO4COo09DjHHN+QxCoCqFzxi3x543UPkMx4bt0i3jM4LAdd22xme03WaraWf5"
    "DH/Q9DOpYmjFjrqZzwhantfL8Bltu9V0XJXP6AX+2B3rfIbTaw2aruQzBp7Xxqoln+F4Lbtjf/58Rm/g972exmc4dstveTqf4Tqk"
    "7fcVPsNxmy6OTxU+wx47ruNl+Qyn1eyJGiQOO26r13J1PsPuOvBfhs+AfXPQ9sx8Rs93B3Q+KcvQa3o+7ncpnwEdHHccjc8YeL4X"
    "9FI+wxk0By2nCp+BnWu2MnwG9K3baup8BnSt2+5qfAb0zHYyfAZ0rNfxjHxGz3U7Y1/hMwb+uJ/u8Lx3zWar0x1k+YyxC6MQaHyG"
    "EzAgq/IZMAl9nLAsnwH9byO+ZPiMZqfV7OT4DNu1A2ec4zNadrvVs4v4jP4Y1p+j8Bme7XrpDs87DgvW67pZPgNQucM6LvmMZhsA"
    "blbnM2BhdprjPJ8B9cBSyfEZrVbT7+T4DDuwfWec4zParda4V8hnDAaDPnY85TOCjmv77Syf0Wk3HTwGZPiMoD/2kIlR+Yym12w2"
    "vW34jKbtNJu2gc9oBnDuNPAZMLjddjPHZzgdWCvtPJ/RGQCidAv5DJcMWmNb8hnjgQ87l8ZnNL2Wh8tI5TM8QrqDvsJnwB4zdkg1"
    "PgM3McfJ8hmwXnrOOMNnNMetHi5/lc+wPce2Bxk+ozVo95u+mc8YdN1xv6vwGUEwbuJuovEZbeBenG6WzwgCb4AbqsJnwMbZadrV"
    "+QzggLuOk+czoJ6mM87xGW27GWCXdT7DadsEO53hMzqdFmn6RXzGuDlw+z7eaPx4QA6+H71xl3v7+9Eq3P/6jDSWhAr89r57cWP/"
    "95ffHVuYZX/0LWkk0cPohCxvuTHZq9fxFvQOE2PXIYfBFvvrsx/3SH0Nf5P1PzVbbCh6WwpUXqQ8BDx1g14woE9wzMXNAYhJQFqE"
    "pgHKuX4LnwZIlelTb9zvI85Br52Oj0iK/G7bbtMnmBOv1cUnIJh2k9YCJLUDI/yS8Vla83BagVMobSrwuz7BJ7c7tnEDAIrYA+7E"
    "po06Pb9PG2i7HcqtYqMtv00BbvqtVos134YdzWbNO6TZxiebAADt0cu19UReFwTLaHYHZikk8d4L2+rYFiCzBTy71YJ/bRuTbAvW"
    "jQXoZPXh3wD/deyXjZm7EBL/F8RSr7C/Prs9adD3Fwm0VqPv+AVf66OX9br1WrmH2FMva3DmtMtamuDxx6Se02n4cW9ez6t2pqm3"
    "0qI5L5U0Vz64gZKslM7Zkv+4N+J3jKN61oa8bt2QKJrpX6L37w5ea7SaaR+JqY+JsY8k00di7GNi7iPJ9pFs3cc/YC1pfROZkYaN"
    "cv2UVVnNftpfpYF8vzMVGsYgW9yQbhiTTL2m8clVYPiw1XhZj3ZFiREeybIVlrtFoHU43W1BjFYJSr79NLNhOa6tOMS7NDUTosPj"
    "yYEWA6PmoGFui8fQ3XO6tWa71sZ43A2ny2LkahlEtO4GdS3zdHJwtNg7mVhnMZm58yT0hooeCNMXuevOwukpxs2ZkGWY4H47J8Jp"
    "pkxUXPixSNUm5UH07xinytZPFq4XJqeY3u4wF668irbZgSK1UuK6ATEeUUcmDBdqAE1V/YgNvsXVDodPJmkUDEMVwt2KRMdo/rR8"
    "CVDmoRCN+de1JTWxhqWLOusgOJchi7WKt1WZKLwwZvPq8PNEKoGQifRNZH2kfRJ1F7gR7Wc8lUIJPuZm2sOiQo+yC2DEXg09NUGP"
    "SkrL2V16G3qW6j8zP5ypqnM3H/m8yxBNw92MerfTVGr5lfcwrZRh+3lx1THgqj6K1NsqlDDYmqjDmDMqUYqazUdyGe7mkU9kyEyS"
    "pzKfBVuHiqCFxN9g0AHfmaDKgAO6tYaCrznTDOVbkRGG2hCSoFzBzLRkPIG3pR8BOodMS1v53mU+jbKIl1I4faQl3htURXNUIDWB"
    "ugBykdEazaffNdEYRUOf372aCAIfwseTDFJvu/rX8prd1Epq2Nq82EZnke9Os01qdAHWu13WZkoDqzYKreaUrHT1LW2zb+Fmr23w"
    "3dRjnlqrqr/Db9qFqVueMlK87ur0T+u3oKq4cJ7Mp6dcfa3VvBC6mq222aXE1uA6vUsjDost/bXKByt7t5XdrbkQHfMrUnFa5rb2"
    "npWZ02UhPOr9MWFC7RsTpJRBBPmZVBtzccEzfuPP8FnKxSEH9eaJn7lIHT5L4ToiX8oulnEshceATrcCz7+Re09jMXk5opltmn8o"
    "alncUxQ0m37WnBZmKVilnci87E2tio9rwTSVjfVFDKepaxfbQvGEnWtSkDAJCyWVbuRd0KiUxOTFqMvj8XEy02fHBjr6WcphCC6u"
    "etNu06LM3ekjBQPVbtFl9qhomcl1+qhwndIl/si0xOVU4lfGNVgpRgnNQCOVpUQwtX5KdzAcnCb1vcRyJKkhCx+YTnZgGA00eIti"
    "FdENKlXnz352uvpMrBXFRw303NZVaCOlLrqyBWlmdeRnz3gqqcq9yH72xWDq3qq66RjTzrc5tlazHnIcmj1nK1QadHlz381sXu7U"
    "kxrPbOplJ+2lyThGZUTK1p447qt2EnG6m6/XTC/wLI12XS2WtIiUqsbNaJrwO1suDcasMivVMCZzVJeHZmNIZA34FExzrNpm/hAs"
    "aXtRsFSNScyKjFSN0rxjAnX2DKcMARVf1ppSpe46jbFtaTzAfDcq7LMFxybhfkpBl23kBOnHvJ+njHymwJuTnmu9TrXI9UFghFAO"
    "Qtd8dsvsQI46tjpbnZ4QSsQPOo4bz97GfouPk+JDfeGBI+/uzXgeKV1DmjuqzAgbtqKW3PINeGrs4CI7rYeZpSFOnXkTc47vqr66"
    "PPGcqAeKtdQmNq4t0VU5RPKrTi318yD3ZUx93datu5ODETn9YfH7rQfdB388m/32yx378bufw4dHr1uP/3iUPL59d/oodMInt4/f"
    "PTz64fXvR/4fj44etB81f3r3+NaD+MH85um4+cz5rfVT+CT84cSbTZPff/158SCEntybTr0Q6p09fjP+xXHGs6lNDrHMs4537znm"
    "f/37r7+FD2/9sPjtVyj/x53Wk6Ofmo+Onr99/O5G/GD2c9sDuB4dHZ8+/uOO8+joTuvRfbsxe+6/mfyy+unm7Vl4dPPOnz803T+6"
    "P//8NO7vv7rVe/D48Nf936K7ztFP+63fJ38O3j5+c//XxaBz5C5XnRv2n+Pk6XF33L43sZ8Mpv0fn53cvONPbx2PrgWruYdCktqD"
    "yR6pnzEzkzOu+f6FY01Dj2DYzrsTK5mQGVrCA+0jyfDphItXYIfBQ/CjyCeHdPrRyKgRLT2XHo5HqNv90D2FCf/CgdltNBrk4OBg"
    "tEj2bz4bXT+bRp6LpMgF5m4Bi+4WMwBxgWNcEryyG45+BnzAd28SRQDKiDYDLWMaN9QY3Zm/CWked+7BdjG6Rf9iimbHP3pM5pPV"
    "rIYhumpkzkTLfsRz3aVuebJ5ob8rAMCPahjbqkbihMQ19OCzjGJe8JC4S29SXFBtKdbzntnrNGOs5IyFmR/0VMsNsM/jWiwGwVeg"
    "yGZXe6sUoP5nCK6Uo9MFiYcvRjeBSf4Rfz3CX/fw1xH+eoq/7uCv3/HXbzfpZe7pY3dGi/nRDNYXMuAxOYY16O4HJFy68A7j+N//"
    "O339c+UuE/U1nCuvMVompG///b/GCGTa0uEEGBzWHGuKNcDqZdWxWnhppegj4EdejG7Dh0PsE/z7if87pP9eWjMY74no0B/AbIRL"
    "7FBAgMLyZ8DG//7f+OCOl+GUJoT4+sdqPmF/p/SvexzFCRsNGPExLRutkhV7mgPN5ok+ecce1eZFLwEG1j5rmTXLGmVtshZZe6wx"
    "1g5rg1VPhyAhd9HhOSwh3/9uNvvu9BRnfhknt93TJ8EvhLwe2paL5kxn9G5tOLpL0BwHKOeSvAkj3A1uwLaxDCNIm1M1yafL//7/"
    "3oaziNf0FPCMeYoa4WaDU1hb/Pf/QsudkTV1tQz//f8AXZ8p37FGrQJatZIBwVAzsPSaK2FiK+QZ7kEpVahNgTWG0qu58vk2iWEw"
    "PfkVdoLhGfxCE7yHk4OzGewhsLfu1c/CYC+ZhHHja07fGnOYnS+AZB2544fASI/evx8hZz1CYz+acUmCuM5I57UpSWrkIE2/ZjSh"
    "3CPWl1jHl9ZZ1vBQNUt0rGMgtXv1g+8xxh7dwNfALaVU+9mEaxWczb/55uYE7/FJYxWTvZOF9YDaFML7LHwbzvceTuq0s+9g90O1"
    "QoX236S1HPiRB03PAVb+cGdK8E/9DMoQ2rP5AXyFgyjgHCXxz8Mj3BWu7c2RplORKAwPfaHEv/7NN/cBKithbf88OQBak27ZsAI5"
    "K2mNmAIOPFCVG/jL+VprpKnVjF6mcN/fBHfS8AAHY5y1BmMHgStKdyaSwmkZ+3VAcuk3YJ+aJwfvYD9kZtDMiPbQY/n5KB1NXpCX"
    "1vJAiq7mL95NXlqqxJMmfTtiEkz5iSpDsS/0wPnSklwcJANLN/r23eSF/RK68xxNwpiOEKQ1Ytyq95z6S6oPy+tA7ajRS0CYaLlH"
    "MRONTX+e1JcvCKtEUTT6lqR1HNDi5KUo+AIG4iUU5chMuAbNvF7/7r9euPvvXn67l07rez6p79mUvqcT+p5N33ttMt8jfPWvv2vA"
    "lpoA//HNN3ShMf1qQKQ9gPPlQVJXwJgbwFjW62IyoCW5xkY76FoBUWKo+hxoArVufBXD8seFGc5fwcqi9sBk7gOXA09AXNEcdMos"
    "iKfRavnKQ/ebsHL90KUmkvi8DEIfs+CREf4gz0NvpuA5XgC7+wo/O9ROFnl0miV5NadlgUYu3VfMQJW9wyH3FXPnhDmRm4AzL63A"
    "h+GgDQGgryh9ZnWdvJpHCUwtvqF86FXaA/qqdoMmaH3haWmT9JX3hT7TTsg3ziGKV955hWr9MgEyywilXLtA6PiyvXn6wIczJlZJ"
    "lvtjOASM6tcbyPjzkJ7wAitir379+miExtRfkPfvYeaBR0ziX8Jksjd69WpU5wT5bH0tWZ5yxrb2w+GTxw1g42CySX0Ns+BNBM/L"
    "94J7kwMEz/qR7gnQfaT1qMBKYBOBLRh2X1iwMVWh8HGPnrpwwpivplM6zrD/e69fAbF3gaMbom4ZbAIwHpNXs3jYJW28LgVUPBVZ"
    "4uFzYKRP5mKCX0BzyN4gsXkFo4i2qCj8pDML1ADY53sTS3wYnq2WsC9SkEKowX/F33nt7HWSJIvhd99RTnsCHMqwN3BQextmGBUh"
    "6UjPkOmQHaCAA5gJeUVPejiX7JWLeBzbYujwivdnCIfVZIJ3blCHhxa9gI4Mt5n4Lh46UnIyPGO4DztiGE/oKgB8p2sMxRIjvGJB"
    "sVbiJjKvh8E8JahrMY7DMxiR5xP0anZKb/zXmJMh7ujO82cj6yR8h2bseJaJjl8tXDxqjqiB/KvXhMDyhqbpwqJD2xBDe/06YoT1"
    "J6DBl7gu0S0XPVN8KQ4XI0t+QOYJ0/FvmgwgzsI4hg+32VP66ThCcglf7kU1PMKmX7hfEvj0kD39n//5/6ZfIyzz5Mc0AZB3eQpp"
    "R8vTmntM0VN8it03CNQh/EkTV/PXc0C3Oyieh4/P2WuNiushF/BaDSZCR7DP5utaXKNcJv0CzP4KKDX/Am/KNzeBZDepnaExMZDR"
    "L08mZA7UFRhxBA//Zr6d4klqyb7/Jp7TPHP3DQuijH1gxADOMJSAxPwzRYdYfBepsJMif/gl5Ujn9JzAciM6YWb8K9L4bGOyXGz0"
    "i5sgqYHGvsRjFPFhHEQKzwG7zPwwLf8EXmtKJdgc+jYhx6wSfihTPtFBfwr0IXwL3+mUDNOvfKbk92f0kFjjyUrGeXRjHp/QDp+5"
    "dHzWtccRMMmYWEOF15oYPzeA4ai17Fp8rUYXNvsCK6o2JrDHklpClxFDpUbaxokbYr+QkYJmkgmp0bGvoWC5NnHj+f/5n/93UnOX"
    "S9yJaqfIv33JYIEhnnOEPmRPtSSSzTLkXhD0BC4m87lT40xCLYxry9Uc74VqnNmuPQHCeIhsynJYQzgO5+5i5r6Gbj13LDjpxjWU"
    "H+HGAzM295Hbf43lWfXYNsoxAFTCqiQ1pT0g9VbtZBJ6k5o7jaMaUrOYtUvpYkMAm+KYEdphzRM1ZkCUMGVANcLSqB1h0/DEITn5"
    "/4l7u944kiwx9K8kvFhbwlBlqXtm0EPttlAiqRZ3KIpDij3Yp3ayMklmKyuzOrOSEkVwsG/+AQZs4D5t2w+LHqANLBrGNQYwBhj+"
    "E2Nh/417vuNEZBal3VngvkjFjBPfJ06cOJ+XcMJ0MzFoR28jend5TRoSGNJvL6+z9bsW6/XPXPnztsCzFlYwW0AbKM1om5J6Ab4p"
    "W9UDUPhsBbhKg72ALe3la581bfYOTiks42VVAAAvWd8GFIMqbhaAP0CYehsPrm5dZnhZ0B4AgmRvBlL98VpJM9R9e36OCxMGDFjW"
    "Z0cyFFblwTIsWxzhWpZqi4bwDvgAWGJtjyrq4dwS5GUEhT+7krjRrawQ7IcGEPEBuasFlMPLsKqz63bIiImAZpFm49hhdSkeZESo"
    "6FRoyQLfld/AAuPxxF2E0wkc7BMeQwIFK9DFcESClbpxiErirnpp8olbHRRKYfCOdcYwoxraPLS5uVba0YscNqyI8UaKABuAIK1Q"
    "0FBsZzdEz261uvA9RLnoV1LANOG4zAvd+0BSmCx4aBpBWF3tNUDlBQ90jgRqpx3qgmkSliStj4baXzcLbB7+y47iRcCil2W9kqEG"
    "eglEmPCkK8+Gqi4yFBddG/omaxpjsW9bKCP/snUl7I1pJNcACiqEVAaa7RVMSAzcw8rICd6BbGfIG/S0LEODv2H81A5gXHQKuQ+8"
    "6SYOok1Sb1GAgV6wHVsmhZn5YcXXgXRSphNx85aT+vr8XLcJl56mRUTk/HwbM27mPdx94UymnNRmJGva066erYV+2uAruddweMNK"
    "rjVX4YwJ6h5eBUgeujDvvCiQ08VVU7JDY17R1zfA7sxslWFYDY2o50bkqoLDWs7iDnsUEf4b1LeMe3IHPpwGm1N6IlxHE7W0n7Bg"
    "/FiAa82aOSupJa1NEmjrDvgPmYVbNAaRRbPxA/eAtwqDz7J5UfANjSsnMFu8RLx2Qk1mSav58myAZp/j/xkw4gMezRVMA3DbNb9D"
    "XA/OC+NlAdH1O3RvP037Cp+LE1Nc4nes2pcZR/bv00oy6Z1LtIFhPCQ1QNbCJYwBgembVMZD0JelkBTqJByfdT65nwlL9kAo3EPA"
    "MrhLFPmpjOCNU3+K19kSLmnYz3ZYIwVAyoodynBEcgadvrDJxUWHoQx6btBhzSB4nrheQAe2MhV94K81Zh0miQcuw1+wWpBPZVz7"
    "QG5X7iOgrUKxtCIAnF1n/MnB5DXl5Bw6ZDHndS0QvhmVgiCzLj/jBvSrNqEVfCMsWaEmmuEcCNfQlck4viaQ0EiA8w2R8Eln/hX+"
    "MZ44Gn4oyAn8HkPkPd5s837BxNaVFCUVYWC+cVnVydXBgTCBgxOgf19MwasMCodxiRej/O33CN/G9HrY4V/jLRIQvbSE9y4dD5QJ"
    "CLPxwO9xG7OoEUCZHUWIHTpbEz3BZys+H6E1rf2sYRaL1n47Yx+kBETROYDplxGowy4BXY6RjEENhwxwEpVw90k5IbsPY4Q/UgDX"
    "LwNNdEuA1quCbe4UeG54H8o1TtD2JWO5UFpj6Bk7CBj/2ABHQstvImj6RHVSYNQvxbD4ZRKUpFcG1spjkr6ScITQ6KxmoczzWkUy"
    "9PmiIxnFV/Bf+AjvmDU/tirfREeDOaYByCf2DSYGGn+EAs4YT9IP/OE7LEtGKfjfD28oaXSDa2Q1dCsizkf0wxXAIxM/w3+uiQ4e"
    "FtgG/h8+U/Q+pFn4v50WRkb/gAmvlqjMvSuMAOkROggnBG5MdzoYQMQZrwKSqkjKoWkE+rWiaQCMEBVuSHioV81pX9qo4Y4fSDIX"
    "FbphGwBj5axFRhOfX+sWLtzbUFCX50jDbt7dZvgTm6T7mS8v90r5i5sKg65KMVx2xIfCrQs/w3eUjSO+vNjfBQ4WozWGMrhbSxni"
    "3X/BQf7p/82wX/3uGn9Hjb9jIYV9h+uc7phlC4eC2KTQL794fbVtY0koMmV2DnfyzXdhOLL8B7wAx3be5bvBrRZrgbmBn7d/GUhD"
    "GFhzJMfxtT+INEESx/qFy4uy2G+Eiwe6AVt18w554wBE+wkQ+7SLvE4xBHx+gWQE0Ya4tK5fjwrl4kFBHvTD6pOMZdQ8ShSTqJwM"
    "7iVCIL2Z6OVUhUeRtU6S+zciB93FPzKSisYA84vWinGvCxGtOpDXdWEgdYu21AgDveYsO7qBRnuoCbwcLDnmj+viBmR+B0gjl3n3"
    "FtphtYJCuWt8Hm5wjBKZCDgIuVV+oiB0QliQKsSdhY89Gvgo0EAbxXtgC0UlKMVBEtReGbCMJwzHWmlC0an+tloFTQDeEbmwxBN7"
    "Q5A0e2LVure8FLY1VE5swq4AMa/AUAVfGwSEj2MV/7o3iy1coH8HgfhRES2MrWnLu0gft7ClC7dmBd8/y14vNyq4wC+yq1S6lS0Z"
    "OQElHs8y95BVgUmGoncSZeGzfxa1tM9OefaizTOmarh+BJDlZ7A7mGoYmFFgwVBL9PjxY2uFT7qgANcQIumKHTPP0gMEiSfMgDKx"
    "Q2jr3MPaSuHstkhWgg+X8AKq1n1Znz/NHhMNg+kT7QsPKddHOmVsJAx8ixH48dRcAcsOW6JhjGlNG1ACRRlSiOKZqAx/6xIcJt+V"
    "8yWBTN6HKf273l5KDsWewiABFB9wPEMYJktD4ZMf6N+SzgbG6b7t4NUNX18C/Ye2rsPNHUGEBcJpPsEuPnusNA8ekXmGr0jsjIMp"
    "u9N3IqxCKFABNZb2cSn+p8W0Zn10iwoUBr8lDU65IioJiPkZkXtkfBM4xS/m0eBec6ffgdEo8aFDQv5kUO9RAkxc7p78nGilKd8R"
    "mr6b6oHEJiOUR7zEzYWqaZ8YxtiDxiTFAR1dkkABTSJhF8ZdI4xJLumGJ8VE1G3WX+adys61CZLtMRO4la0Bs8ouR+YqCLDKde92"
    "vGl1sP2EXEdbJUnQU9E44HmBMcB96to5DxumDW7xAAt80aN00HBUl5dKhc174yeBJI9UOEAsnvibGkVAyIaTlKVak/yQJaCsGnIt"
    "NE7IhpLG1aq+RhCksG07Gw9DuLWNAyGUdUzDnz0WUWZNjeaQF0U7oFF/UvukzXGiJzxkMLYLlEtjb37n+e1puCrPTyk1qcyOPiii"
    "gkMrwXWJ6IQ935m0LpL6TOMM6JhJ3mKiraLqWGNsfZGKzg8lfy9vY1RnAZphzO5QjnxWtR4KjKFN7GopOtS8aYUH165KjLBBPB7/"
    "8gfkwwcRGeIPf6YC0Bnd8c9xb6aKmaHyi23vZ9123KzfKtheuPJGkMDRrmXSaDMTPdpjEKEf1Nh2jDFpDS8SiK52v5j6CGK+wu35"
    "JONp9PX9mgjse9fWmbzU+aFuCy3ozncrqpiyBX0pCKsb+fYuR3E5KyWUWnbtWQ3I3ZXfDZU+4vnnGAjO26uBhJqvjN2iu3rTcmrF"
    "gl89c2Igs35APXMPF+pnv3z05MkjjH5mxBAYD1zJDk2e9eO6JYlcdPXo/XU4vkqGBg9kQTwy/Zq6JdDQly6wI/5lTOeT52jLh884"
    "ZWFvSXGt+nBCLaAjOap7VZH9FBjQK1LXo6WCgudrA5iR0IFM/Mfsvdzj2QO69h96qvQs218zu9MHSXbQy/Ze6qjU1XdlXIndfT2r"
    "V6nDqKO9nB7Bsp1AyYe69m3xvP6ZCzPLXn1kYUhlXjVD+WzUF/Nv+DIi4s8fAaoo13lVq5zysM3ILKHPztr2rRJ5GxFcv7NQhyFN"
    "QEJ/jkudhIQ/+U6PGZmhW3x0iwEDCeB+DgegfOuA67Lv0dwcwPEnn5icoJRGKCTaI6xF/GtqC/qIjCdrxHEecAOSxgpASaFxA2/h"
    "W/ed9MCEJcTDm1mRqNtrppfKsEQFaxEVrvmVZwUi+zkQuQ+Jkkw3QnJvYOvILCKRWhuioTEGW46w9ZAOAevq4R3QSsjtKQsgykI3"
    "N97HyPSM+uUCv/iwJb28++kJN7j1zteyjagQurjNLsgGBDcmwNBmCqpMlgiaJJuur+tdkTHI58gkzEHn1/38ojWMRDEGi0BSAIeU"
    "+C2GgkValGz6hVbl+lme0KcoeIaL4Bx9HLTMyeAyMr7UAjT8da+IE/jhKahr+qjsBL2ph/ESwnVeyotQ0B7YQSBmHez11oZDQ3/O"
    "uyqP3v6Uw4go1Hk4cF9w3a0MQ+kgyrPs6oYSF5E0zeECWcUpQihWkcXB2r+B1FhzBkhyJqJEwR1XFJ8JV1DwRu4iIc3F2t+XA917"
    "S1jQvo0LFN+Jj+CfSZfoTEbDvyYegmSHppZ94+X6XGSGe4ZczcigbwTpsAyhJ4Bp/L8ZMFIbsFpklMkFwHOilpm4b9Q2q11mVCqs"
    "lYPgf2FLgm5e1O5Wd8qiNCqRVl8iEeLbkd977+FBXVeupX44Q5TGb4UQR3xI9+uuWsGXv6ZJM9sEz3/4myQvAEEysV5lMHHLQtoA"
    "VRFZXp24b8SUwqfs5Rv3FWqXHbPWe/LT4V8McyI2CQroQMyMjhGKf7tylCm/Ron+zQB8LZDlGgXxzW0Cgi+SiSKY514YJ8663DRW"
    "Mbs+5HdRMD+dKD8MAEl/eFOoxEAh5GWlIF0pT69j+jG+XfK+ry4aOkQ3SDXYloyVGTR9wH4B8bWK4hQWSB9eTYYbBndaPF8yT0DW"
    "KK45p13/WRbvOxS8XOv3ePOhaO89l23cfH7qhUfearSkDCHDFijeZgdESHvC7w+BCeJCFlKP9x1eCy+EBWYJLVq7nRsli4Hk4O2z"
    "LcUliuXOyrKB2xhTsBW4ik4pHm8TLw/9HC0AQyg6CFAeNoL0Jby7UiVCg2HdyrVDo8TLg6hLZMvHKKaCHeZ/RwZcKMdATqhE/rNA"
    "W9beGQIK9ycJr2LrMHUG38ryGjmza4RGaU5Q3ut4UZWX1ypXRQMebL9BU0xYUHyeoHYKnqJocyecnW0kWU9B18glC27PcJTZAVY+"
    "QJtbEpCKtYzOm6XFs2hPI34arVqQ6SLTJFo9+SzmQuyW7OXPckPj1sxihOetLooJRBYT65dCx37Lf5qoUIdLU0C7ptiAWAyp47YQ"
    "4z+9LSIL6m3Az4/Nh4seIlpL1pvFfMxuKzI+G7V2ZKbT2qDCfqRNMZd7Rix5A6z39cpR2Qz/9EXPI4swOEHZg4P5YYY+PQ8VTmzn"
    "mOB1FGaIC4BmdszNdUJ66bPmm8Nu5ac1tap+XSJfOz/az96W12kVEtcio9/o3am7wMfpqAPG/4Dfda5BqoZSgOz1Yt3SXOl0zVer"
    "uuLXZwZgNnC6i4FpFXEz3//BzDycGLmzqdIlEC/qX1RzZB7HC7KFTCetAUt/ZTb04N4wE7N3/DI7LNcA/RZ+2fRmGbpooWRYG97i"
    "NrTlimUzKBjBG4hXM3tAQSJDMw+D+SR68fRxG2rfgfH1hrVYpSPlYKP5sAx6YPxK4EKTUvAtyqmxczR91dUfTzLdCrNhzOhokcIt"
    "VFebUgCm4i8eb9G5LN/nGGI4e/Krz2ZPfvnF7MnsF4+3f4Eap4mJ4qA+aY7Wr80QroRL2BbilMPOdeU5PS7iVeyyBJmHpkPKhs7J"
    "3MZObjaIQPBuqtXtNm6gR4q2eRbTwDf86P1ZpqyaK77I2b/o1avTjH4nZcg1fYWys/iqxiJVaFlVMts9w8s4ubG/kk4O2aIrsIBy"
    "dJRs0vkZnZhoqHa5kp4RuyahTtGWvS6M0VeqMMte5qvVNfzb8Ymav9hRIOilgvV6xyL+yM0DyloSssAFjLKiOQuheVBC1/HdoxeT"
    "Xb5NdtGSgwd1nzX+Prq8lOG7IfFQerFm5XXE0aBIqXc6GACAR93FJX3CIQddM7R9IUGmbRIOL1GHsAUPhys2k6/5C6+zTgh7DGuI"
    "fUfzIwrID1c/n7d1hS7RiFa6Mb/mT8m0Aj08G0g7K0vPU9smxKFBkQn2v2SxtYd4wYVbSn0pIv5rDD4fiB49v5ZjhR9pBdCXU+n0"
    "uJryjJu7YlwNs5riIAVU2Nu5QJO0AF/2LIToS2tSdzSsD6yfmvjjSi8QkRvRzF/bkGjhRMvn50XLV6GgzZybUJcrjBatNbPAzwyQ"
    "1QWmgxA9sR3h7MGNmpbdPmTbbaIVKIypnWLOmDqcJ5shUW/Grai10q2NkeTTJA0RtXyORwaGaQDeikYMx71SOX2BlGpGwDKbYLco"
    "q0ZEpH5HUrAeRb5inYQnBtrVYybyYHwNQJcV5pgGHrqaoFPs+2bYy/1M0ptqveXUzoxKupgkPNcdWg1iseGE3U/5VtRFp3pbwYWs"
    "f9vLSFBDnO2fJ8yP0RrxVdN3BROp+HAWrSMiMGVV325lbRdrtMiYET3VYIoTZCWhKCI3y2W1YXmp5QfRdpAc7iFTP5rxq7ZtOnQF"
    "pHlsopuE2OfnW6wsflcJIgbdGxr/83hluNmb1M+wMjUAnKrgkGd8AAffQmTV15GW1KyTOWCTKuYqxevgMPh7ERJ8jk7AnrPAA9q1"
    "6EJHsToz9MO2RtTC0zMeLImje4WKRTW4jeefdSXIbY3G6BiRT+VC+HXRZPoIsHeEPJZIRdw0FI5xK3v3sSeT1l5wnagBcXLFgaiT"
    "EUBWJCA4chTbLYtZ8ftViEHoKfCaYtLk9TZLIuIzHcZU0AN6vAf4m8yL1MxoW2yIzuqc38fIZHroje8WBUpFNLXbpktxIoBaYeJs"
    "wBDG5n1x/QXfyOOhN+8cunZ0/8h1dMwa+4b/pc8AoHgTVs8ZF3Et52c0qjQyh/54zaY1PW4b9eZBPiIV2fJSEdfLDFWnC6AwRXV+"
    "rh7h5EmMdPLyumfkkTsO12Dd5dekgQ5v9dHeEwyZnamBgH4ULbvTwXPLWu71LSruogLmEqY8Tbfh2r1VMF6P0yek32tGFC4Fe0Pn"
    "7sTvYAq/BKo849ChdGxoXXVoVMhWBMGDKy703iTRR7Vo2zEXr9w1/iyGZb7FboiY2ejX7arXez3cBANxsyYQDApxEUqR9kV9+amv"
    "s6E3R/HQvN6YbKUdANMx8c0jDDm+Fvq1WddSA2pZZGr2LeavW2Ol0LYPpcclO2lHAzvKRVFnV0S8CtgLgcyyj46p+jPHspNs+br1"
    "NonIvL5jS2GrEDkVIfcXgQSpYj6BYFgqTHaYWcUe1rrrpBl22x2hj1xA8nOEa3wPEbjQ0xDyws9L5IjArOKLWH33OL5hML+T8jAl"
    "pXOoJMIBkuxu5iHJD3LSbZIEPti+g1/D/JuXFetdxdg0CI9zkRDCvYHrw2LpmdcS6muBZS762UNgpBm8j4u69J8bZjOd+FdjOkSV"
    "0eFA9Al6bpiuIhPoIS/Riufm8jYDvmR5K+ySlVLh+HOk4dQHTHBFieGCEUetCtG03F1I/MkDRcrd7KaIexBPjsLcXaxorOANRhZh"
    "H4KWN21a9bzztdP0Zj6CjIEi8VsJ5An/RsBal8fDnuUc+YX/TEwvrD1UgR6fHh7uH36lWJJsMcMcHe8dzY/32DxqRUdrDHRysL+j"
    "DW0EOpqfnlA7uVjwJ+Uv9g/3T15uUHoLyHz/YG8XQchL22xFFNlfhFshJz8zLsaHxy5v1m/xDZILXssG9AaIXNUMHi6kaHqbLcvk"
    "OZkAilgCtzblQh1YSz77u/IKg5uZDPYYoCsXbFpxTD+0nzAiNFc4FPwO1gppsaA3AUSmSrI8LY7RTgmQpzM2OoiL3SFJQaZNEnQO"
    "GJZHfNFGYXoMbAMKs4uUQfGLTVYVFfMXt1YGB4yncEo/7Htsa+BsxdWQaP1cWz2Uy8QNH1uVNqNRyBiib3xpPOdffFHI5JgSngQd"
    "qqwNc3pE+pntQqbPjbwV4yW1YndXlQd5wW6prK2FB1mfdgST3C/QPOO8solW9sHAyLPjhXjWmkFNqv91sIdkBIEMLttDIxC/WNlJ"
    "5MFjlCKgz83D5KzMrCE4UM95QfWx4oIoiGqMb0Gt6oIUmEIxCYXQ59fMwl/mK3JX2/b9nfKm3tMfB8bWSDZ/Zo/v8t5QDJ4aaF2b"
    "YBl8atYJTBDLxIDzouC446G1HD9pnDTX4hhU4lCN4dX9V5akbskBHd5Qi7XaPoVHfjEID6VcLVkPL2yNePM3bTjwn9WSuwtsbFHJ"
    "DjAtoQZDU6wMyLQmoyQKRewGiA6s8u+4zxHqPIvBmHsXG1fCdSAo4dH8DvUbImehgEZu17ejln5dlqtoOhjWibT+CeWmedH7A0OK"
    "iciNrZtwBzp3LArdOdSWUfdxEBsDw6wwBon7gsBMJCik22yFwYALM5mhv5LC2eeP9Yb4/DGZDaYAvzKAX00DXDN3T/Zl1/zQi8pz"
    "0rliRAfkX6y0rxoySCQdrggNdQNEQEcg6L65Zo9VqoeCdHJ7pXB1JFcn1jeu3TuDhCh4zswaGofBoe9+AeXR5fiH0i2gmgseeeNi"
    "K160fSRux79d3yPPZPoOJ3VNXf6WfkROs9zpYj2n9RQfYmDjclTGpXB4UP6mPdP1/bY9Q5iyH8uqZDcuy/pc/Y6B2OGfYRkash4t"
    "jFVQ10LimBblBKBjGjYB032h22LBBB2iy0w0zNZBy/Et+ENgZvxuHI4Mt5PSKcNtw9YNpqpRudidRihxn+lpmG6L1Xu1XZbqgune"
    "SFwqBkRFQiZDo0MWDQv/UJdKHMJZTs/jflVXpOSN5OOiys7X1MYsoxjLyF6wM5DG12EnSW5/6UK7WJiX+CAYiKwN+uLni66FVwaF"
    "w3TBYJIKYbtcUIMxjNu0cWNjqZpfU7yomAxZBW3utcYK4EVuWcTQJ6e8b0kZcCzRFjkchfZ80mr8BnX8RE1xAHXEJhj6/1X2ZLyF"
    "+lj93XSZDPl3dJ4itKKT+vw6Obq486MlpRJxf5PInUHLouJ6wAK69mVCsIgW4JFbIU0MhaMkqQv/mZRKJyfDirXLZCEzdCgfRIv+"
    "YUXcakL0p0XPJPFW8jWLCSU9pCgqEf6flPXcuRtGAkAD4vggEtERQ42jHOmdwwuGhfdbddapv/pO+CuQe3MKm2cOOiMHDeGV1m1d"
    "BBYGuQ8WQbN+Le/NZoC0iSyUg688hHhEagqY8ka2crRus8+X57Z4CelPGjxpyW42lqnoFl1iYKzQkFgLpi3IhY6pMLXiMi9KucYp"
    "ph6pyOiULDitgGuj5TAUdASpwfOhTok0EFEs4TNHQBuPOXxbtxQCmGVd8ndy1R4KveK/XD8vrfrIfWhTj+gKI45su2xmH76vRHh2"
    "FF1LWDIRXCumQAhkXo6/VQc6VyYrQisTlQgLsuM5j+mBnIcQkSxDCW9wVOfTq4C8YAJ9BhZfPXTwtxWU71dqj87GO222c/I1Fpfr"
    "OJKgsxaT4nOgSuLASDEM9W98TIoiPs/OhgsBZyeA8E5m/wD1DECIi6EijR/0A0SH/vIl8hCweIND1/TebraK1dDtfdFBOThqiEZL"
    "DIE+nOiBjPmc+VrHpAnwVvxKRkchMjj2XTrMyoDwjWHBBklBw9eNxqBM6ms/IaCNsSzySQAwJrmFJ8vwr4xV4ESjBVbus0d0FwRx"
    "N9aHzyf41fOzmSStzB7QM+5hABUa+byE33yKGLW3gpAD6FYaNAs5GgnMAvXk4Z27+D062ymvTff9EG5sRRm+70xDJEu7xsNOsGJo"
    "IZjAupR1V11QeBldl6TfPVEKapgQHX0jz9nQelJxZ0KrirFJSMlvB28EP1aoIkZsrHWYqiXuhX7FJ/xnzMTJEYdinpSFNJBJ9nGp"
    "qe0vaZ/L8Za2YtOPKIesSL8dtcByJhVIxUVAeEU+esS/WKrrIDCMMonkMPQ+415+zeL8KBJxKIkGrO6JTQj6ytGmwyiFw4EJ1eRi"
    "PywbpXHvyBv5XSuf+6gf9YdAcXOTdx309q5qCsLqUAUeOfCq08d/jldo6Ic8tjExEgeRxqsY7T0UpSQBAPtC4a/4u/lXEckkUuUm"
    "mVMAXTHpwLDUSNGSlk/i6PIZ5YGIu2BTfdfQdrD8j2GFkdFwDBy/IYrFs6Vhp8emvTYwCk9NLpUUp1rDPPVRucx8l8yQBPnQKeWi"
    "ldgF2COSGbIAQ+fMWXaELzJ8MZFZFFuNMSVi62xOHyL1kW0jOQL20Lc8cITi2FSLy2oVKNksY2u43Bh1CVaDZLdpbQ5oJmgQFDBj"
    "ga82ZhavMEkVZknPjub6/Wj+aOeFrQwMBeaschv5wqLeY+mBvUXJ0HF5K1BNq6VMMHzgLLpV0KTlVe7dH6wurHagNPZgU/9chICP"
    "ZD6jDE9s6f1y/+gkAOrBNOYIDwRF7EEA+MWjQGGZf/HoOAi7KI6Vbjlw1Bysyjhxidc1cd4f2PWPhiQPdfyqWgjCHfzgC183SkvO"
    "IxhCmHOxiu9tlpg7hCyPzss1vtzw7+zBXz6MAAR/f5sjl/JONFYUH45F7yHElU4VQ81wvKZWzQHYqik4m9N5kg4pdazOkaW4FAiD"
    "LmyS6dKZFBc3m6uoox1vRGiKneNLYeBV5XwpGad0xaVWrssWkWXt6om16tqFhG8WKye+qejZju4FJ3LajqpVSYH5OP59uFnH2S74"
    "O0uOww6tIl24YoEjXsqdkoTaX2r69iosGp5IOJE5Zd3PS7iPKP0XVUBfP+IFQ+BFZPKK2pSQjWrXXdIEB4bWO2RtWZardOBXVV+d"
    "1b7R2SXzjuT2ukpV/nQpVVelKXNio4BMQn4gsQyeYk5OIPYistAPejseqPUUyTiNk6AQUf+dj41OzpYY6r0cW+v5VjT4FwedoAbJ"
    "ESE74bpsHI1CD/YoCWiIrHHPtCWyTsXgpxnGBSGzt3OSlmhmIhPfaDaFL7NjwOAvFV23J0bANkiVxt1wI0CbGxz2LEE+2JCCouMl"
    "Sw6bfklFbLjqcFCDbpBwxjvbWdtpGhf7FjCdqBuJzQNWL4auK5vF9ZhetT05MG4HwFkfxLUvzPUMyeODGzQsvH2YNKrMBjUFt3aZ"
    "uCaySDh6aM2yuGU4Jvwm0zYzyRsQwuGLxbBSCri1KwrqpcGI2LRxoSGlsPPr5VlbP41NvQG14QJdy5iiZRVsjq0qu3IBjwCO1O8k"
    "DJLJg/zLYN9sS1UF1LGeQaQgeOOhFOM8SqPROrWQDcKQ5o3fRo8zkaSDxMBrVI/wQEXYUmJAY8rThejHduLyIbu5uvWE/XQl4gym"
    "zHiOWIKj6NWUnF7n61Cfwnpd5YBEmKiRjTC7Em4do3Z1yzoXstYr0YIxX19qv5J1gXR4HJFLtk0XIuRuyv4tR70O/CS+JFQFuMt/"
    "8oJLG88SUHn9q8caXlgBSXKyo5I8BzgSZthwuzHFhbQRQn+5hl338egRbzCIHzOrREhK/hMjUQBDPAuZ9ZLg5uaqkQbbwFqcgU9P"
    "8DuOaRaekWZmSsCbArFT4XSodypyqe9ChDKxoSYATexH0+efWuRNW8/y4sLqsFVSCJp7llsdFyDUiIELk0wwmiQwuKKrfbgMeSkx"
    "Snb4V2gbswimQbeoyKcV5KgKHbpz4J/O3ZY1VFIh5B2kCqQ652dw9uCzrc+/eJxdsDD3s9nnX2RvLx5q1U3h4YOEhcAsaaG4oVJQ"
    "Xn5O+JCfpBxjPkTj+PK++HgzXO0BsfxBMCvx0JQ1fhjWSTMksn6lOr+O850oH8oNwN3Zi4qEqruUihvwLcqyOIF0adLFacxzaRjN"
    "hIUjop6H6UXA9+BdSNyYYBWnqEow0CV2nDLQjsCmToFdWkRxxVhVfvK1ZwyXaKa1AmXjeMNBoY4sewoiQTDIcNyaWGX0RMJmviFU"
    "UXDHb/jX/f0u1BnEO4Zshwv76kauk1tfy9S4O2FI52quZ1D4kJEpEYlHbxN+mubkfouDe2O21eUo2cssbUyd3UetoQcFtubzooQp"
    "z6Z2Jr4OzdTL4IbVm3aXIf6WAi6gdI3iAWvikL5bzL4bcJGJrP2WCHV/SQ8zrwaL0t0g0XkmlYeOIsEfH+ACMBAwvo/QMbB0OZj6"
    "srviBw/UkbhhuGzwhfLBzCTHS5IXRr4alKvp1saK0ZT5NcvUMPgGh0AKRfuN3sVUXDWOd72vVzyTFPgG/7ev0xEGuMxSCR7Tj2QU"
    "YQChC2Scd5icuCRFISICpw0V33WhNFyVSq6Z54Efbgw+BxWHcY0q3uMP5VaDUSoMHyBsBpztbwIibAKCwD54GB5YnFkqDM9D8tQY"
    "8mv9LQxUAsoraxnQdIPtQAeosgijQ0dRhySThCRZDwOGW2jHwaMh4yIQn5t3l9e3Bmu0ZjFBawQD3qP2DlkCCbIU/txmmQi9O2gk"
    "9MAYGngoVgsUQC0IbfGMkZaW9QQ8ZrTuYpaPYkA31xwF2g43CxCRPS/VQkmQmVysoKKpyA7gj4EF2/RdXWQx7XtWJ4ViczzXZzS+"
    "x+i5tKYnGcHQ02GvuagrTjmH31brR8+PsdG2Ww8Xw93vgWN53uV9VYdqxAX1q/zuHzkcIH6kk7NbDut+YW19uHy0g+rU//vf/+6f"
    "/td/+qf/+eP/+c//UcvE3y2M77zFzB59mjlN50UCKxkrsxi6guG5dsm+xLPsb5nFb1EQi28eejaETHHStJFpzFlRfZgpAfQxs11W"
    "C4Do37KHFPzHJomil8OyOMwqfomjseKXIC/i1wr/beB202EVjF3ZLt6i9ElYMi9oIRsCQJTSRk9YMntMGuGaHtZrSzUZgTzZpB4N"
    "IJ+xIgXDpIlQMpR9zpeZ98IPhT8PhSyKiEp/4e9BZoWw8PG/lsJ161M1rpwslHYvQ/8ZifWIknfK26tr+iRipFBC9JF9QR4CJUmt"
    "C5Iqax1dcDjMDVegJlt74AnSQx3RZ4lYFf2/hY9z7AK5lrM/FzuGorC3qzBChcWuAp5YnHEGtG1lX1CaU37VVgUKM1YlSTJXwG6s"
    "1v1T52Odr+AjoDAtMN4c6rCKDehYP6ecOsx3LlUhPYp1NREji0RdXZlJHpGV32qxymGPddGmXAvxCJjCQbnjzfx5HiS/LGthv2CT"
    "P/lgCk7oHAeCeBB8zigmSXO9GM6qxcOZbJ/FwRKsEE9ck5aOZck2vjMTv/TZ//67P5CUEf83OSNapVpNiySPYQP6oEyTiB+cjbIJ"
    "klbt5he5WWqJKfK22MfSkVGXFzYMbO+J1UWNnZnZLan0RNC0JaJCSi8b261azUVQR26rD2Y4tJbI1+DFYtjCaNAGDh1J8wiPXHbC"
    "WXZctmxCYedcr17ekCkDi9l/uN36m81JzOk9mKQxf1HC3d5tyGOOsmZfaJnMv27rtS8Idsc7OVzRF7Bs7SfmMkfqAPNHteNVO5HQ"
    "vL7yHSUpzfH/DLPUtQ28X6qiHaU1v7z7nqPzjtKaawn741la87u/7zfkNX/Zflvek9b8NSD1ckNK8/LuH+7+B9Cuwl9oUVbz5+1Z"
    "1eTjtOb7S3oTt12eZDbfwx93P2LW4nwiw/n826FnoWaa4Byug0XV57jkcKgaGNl/a6eznM/PuqrLQkvjLOcNnsLm3jTnH81ynhfx"
    "Fn4k2/nrwHjCwFEbsYKtLocMFl+SnZPfS575vKkN3hx4V0botjHpeU7GFLRGZ7wxWV41Rc59wuV00Q5TWc/3mqsKcT/L7097/tqn"
    "zQYcAlTsAMuwZoMoFWU+z5O85/2AQl1Arbt/gB8lzPPq7sdmMdRtNN4MDjzqphb5Mmty4A9y1+lWBm92oFHLs7sflhkaHcGCUc+Y"
    "PgTKJrKfbx60pUAvk8FmGLIAh1Ymox4NaJYhQtNHGU1LQwzJxuu7308lQAc2nwALbB+qT2ZBz6I86FWeDUvua5V3aCAGO7u6+x7u"
    "LdpyiTRT8m635yX6LsKWhszowzL7tqzWtODtApG40ya3MkAxrKfjjhK9LzjuO2wJoKsNGap8h7GFoTOkEUDxUZ4CHAAA1dUFnBC4"
    "EHbLHn+T2EjHGnqBv77NG9jykDK9jbV2ZNFQ6iKXlI8VcWQLO5VDvkWR+JRYKTJtkXEY6nU6+g3UFY49VEbo0tMhNyIAXN/9gHqS"
    "6uLu+0d1PsqffpAcsfuyqAPUE4G7P416wcHYkybTPOrAkMF1jsB6q2PCiIm03VPp1Kly/+mVTaRwJBWjjSEcAxKU19UH3Oh7cqvP"
    "BaqbzK5+UBLhGVGuDfnVD0YETseQb0i0fogjPW+rbNX2/d2PV2WdUQSnUY8bc64DKejaBmcgiziRef0AdZuOcl+0SJkQ/+DcYkwe"
    "WCPE2Kld8OehvT8Juw0FF03awgPR3pOKnah7h+qtcJ0LJuX35mSXirnPyn7R5Vc5HSBrjlChR47HN+0mBQenI2SD3eIDO5q/x6zW"
    "FS3aTq9KIOfWqHiPJdna7Rr7yFQ3Zm13G11mumw9kcWCyRhj+uY07oGPvB+l42zurx3ihPsacZaYgouhy4lHHOd132/gCbrE+6bE"
    "1xzcUrScPTAW4U22VDoJs1rUFV478O0NGUQggV4h6XY3Fg2bLj47ZN8N1aY872VzCfdK1L11XZQoaQljn8j6vuF4+u7vyf7ebDrc"
    "bVchrS/GrSRZ4Gn4uQDx8k8mg3d7RJ0i1ywtz7IdID9w+5ePOKFYWHq33kYGN6SFn0eSCuqjot1tB9eRMIk5ewZv2ttxX6PU8PG8"
    "6VKlZjAlcdduyg7/akD+Ozsb+gWs8QC4slyVSNekGnMmVxSFDNc+LP8oPfwn02WfKf4VMVn+eNUVnJfw+nmKvAE0WTDTgDxzH66I"
    "jSnjecbTKeNxWptTxreaMr6mfPHMoCAv9X1XtbhEf9Hc/WFZdu3HssZ3eedQdTJvPIKsWtQBbEwb/0aXfYGC7X9p5vg3el1JrWoy"
    "ffyLHF5aC3ykbEoeb+2cG+jG/PHzi25YTa6BTyH/uoObYBKK08jvdJT8PRqSpZFfTBVaHvl5TRH+kdUWsH9fTFZxtgKMjxjlEijk"
    "FVKB6XzyGIIhJ1f9u5/eV8t8Y0p5bhA30PGDcV28PRHzYYc3Z5U/gIOZp5iiUcCk8HyE+FFSedmQ7YxJ/H2J5Q2UDsJ9eeUN8uOZ"
    "5Q30fArPfGZ5QQoYaXtvcnmD+2h+eYPc3LfPJmfgq7Jv2dRwoob4sMfAQ893++YU8wEepdJVh3Xa+/LMW4W7P9RAFCfhNdl8WDrC"
    "Kfi8yMfZ5o+6ct2Oss3vVM2HfJxu/jkQ6EWb5pv/ugQ+pb5sJ5LOH8Cd0XybT2Sdny9zeIm147Tz0FpRjtLOzz8M9UTa+eP2fTtK"
    "On/c9vk46fwr9ANZ3pN1flPSeXvkbco6HwjWRNr5E3wxy9HZlHTerO4TweF05vlAm1P4qeTz0D3jyKbk8wbgk8/jo/We5PN6DPqp"
    "DPQsONyUgr78V8hBD3wYDS7JQb/HgqLsLK/et0ke+t8A01lmV/mHKp9IQx/V3GYeCA1aH5HJ++ojueh5LUabsSkffbp0IR/9YTio"
    "H8lGL4+RgtjETQnp92hnP5qQPu+M/GxKSj/HZ15uYNvAIndLXBqW3rAsE24vWOvOvS0Kkt/Zk286Kf1JSdKuy/bbciopvRaLbLyY"
    "ykrvYOg6xRymKqyry+VZV9L2WI76Ku8nc9Pf/T9IVNFXCN6sJIbGWiJcms5TL7xBmqh+ro9UY8P1OETJ6nfpEdXxdbFC9vYsr/Pm"
    "7h/yNGN93kXrmOas76aS1tPYuqms9bvAOSfFmqOyWmCEX+XCJrYwzV2/IF5k2dI6hY0cp7AX1qTI+QkQltUnsmcJf9N+LJN9naax"
    "F6rThCXcwrMxlcY+7+lqzvtNmexzTGWPiIQo9HiWuQfi3Q9ONIaSB5KOdJtS2e9WF3BzonRWngo48wseQ75AXCsooz1JJp88fjyb"
    "TGivaCIVPQm5J7V94FbilYjy2wfg+u5HwIgi1KK1FHFrX6IgaoFUZ13WmNyeXoPumUmkdWN+e1mHvB/NYYtWAN586ex9intFygao"
    "/oY090lpkug+n0x0DzvHqNtGL7twaB0ePoVxVu/lCuHZkwT77vciSU7T3cuYJ5LeU9a+SHqxMek9NVKysDnHFKRKWvFOuio/zKLM"
    "1RMHOCpXDcVmIPxPoWRVE/rlktcjzDpf5UyYy+wzumo03qUDdGksYe51RE4cmAahJr3LaGTvKzWgDThLH+UJF5IS05ZftZPdkGHO"
    "+KSgYK69GveKAWEjwJgyOShytdwDDqC+xHMx1TmCCe4dl6u2r+iKQXWa6xtJE8mAOlJ9hHTcrFlzYuaIMPu86K3ZMWwUQKKIy+qi"
    "hhJoNFEp0UFqHuiwcbYEJAVZYappmGnB15a/8utynJqeeNG9aMCm6mO9HYznCbMP0tQsm2PUXWA0VPvTO2F0JEmOxXJweKAxOqB4"
    "oUo3s/GghLP82LCEp3GM/r/S0PqNYxPH3rQXFNV+Ulem8UsldbQ9GZHfRXlW+p7lvY1CL5TzTqCvyat22i79eiiSEI5hGSiOCS0C"
    "ycE7Y+FbYEWgQbKnc8dnIG6wqDo2ChNjED1CxHuqVMzGlb/n19VBzjJFfoxbNvgGbqShqDiv5imqSld3P6GWmjbcdVo2fUVx5nfx"
    "V5EXntq0Hz5w4tdwTnH5zqqF6+yMo4p7EGAyy971Yn4VR8gKTm8AsZ+/jQHj+zfAAr+w5ukTHPy5YKFIXC7k6GuoDISoZUZ0uncv"
    "FBmzGH5lWTUn7E5LolOHFNPcs1Fvsu+cXxEH55DkLDHzsfWXmAbYJXKfy6FoB8P/Bj+hILpEjU/hSduqa8/gNM7E/5aEK8B7XgAn"
    "9hMwAWPAddu+GhbsUC+soazXaHG1ingyIHIR10u8xmePP/vloydPHj35paOzXbskBAuf2NQY2MLoagt5GiYuq6HBQ1xE+4OMm4jO"
    "bHAhesvdD1dVeGo8eS4JR11qeTaWyPmhp5oUPsNsOYEoePrkaaasEF5M5/kHqIDvbTED8Qnsxy8U4RmyB8RjPPSU7Fm2B032eYXd"
    "sFaAWOWrdnH3e7HL6MhEwKS0UV8JT4T3rCeG2nPUI2p8hEotaYaLy5JZW212aGqWNP3zFwr1HPctFNlloD1G92zUIXOW9NzLSNwg"
    "fbps4hoTX1RAFdtq4VHgNxHe/9EIkSWYRQnMG2eVEOqPQZwIScH+R9n7oUhu9xOWMGW45Cy2hB8/R8zMmfvV7OAheh/gY0v7g5Ng"
    "QE9pLJ24+M441VGPTDK93Ti8dynbTBrdfLUiTSPl7oCluMkv2lv3nYwKREeVO6M7se6oZ+qw9jyx+6g5RrrwrkEpiiV1LCYySZwp"
    "qVTR0A5muZPoCIqJHMtkGSfD+bp0nLzGpN6ECIBTi3q4+7EY735sgkmmP1BQX/ptRWk0GWPiNbYo4fmfFW5P8rXses7RjuihwjuY"
    "5JYXJNtQJtg1QhIVPLDIJ3z3JpEOOr/u5xetdIXyoSco/ZkAkP5MzFT5TslXnWXld//gjoLIFE574jCQLpFxSAAQ4ebeGrW3gFUS"
    "gFxK0cvYPY1elf0yvnldN0cucGo7uahdbgELQzEysMu7H2A6W/eePVp1iSwaiUiwgYUSxMKf4C+0lS3iZvDIofX7Rb6d3QCjO5Qk"
    "uXRYc6ShfEXM1nu6oWpqd6uFNBCWJWIn4JsrHZ8wVyhh69+QwDLndzMyEaNWJFnEQXlFlpSuxAXg52ZSAM2YsQMLR0jJ1uGqkN/z"
    "6hcuMvNXF0p30gh2BB7F1qUqy+k6NBsSNRDPmpGtMxdBPQ3bDxdMiRK3YO4cgVhoiRiMdmuDJQbXn7bajsqk7ddK8/D8tKoKxQjE"
    "68pOAlfsB4q1jAVw4Jg8U+TECikofPpruN3Q6YLkOFvwVvqpruizybQAuscnTrOxJ00VS3HR4nTyxHePMslrfvoghJQvEzAnlxq2"
    "MYWwrKCER2yUGqWHbdevUTMjCbAnMsbjJ3yHTRQB0uyFUdrtPx6nBGg55MdgZOo9AXIYwaTpIwEgSODwVWnXUNxgV8rb87hETtX4"
    "wVEeejqBN0gN2apSwqdyjJt83VVneK21fZzwV/KHmyxtWFKAILhtnfRSVkKsb5nv6+J25oQQP8tilICCl2v9HuMFFO2957KNeJGk"
    "r+s2rdAoEXonmdAdFAnbJS3Qm4r4YpPit1MI07TrF8Lxq/QcGYSyIdtpoWQJrBzao5ZM1+GawfNVvleOAlY1d6+6eP94mWifqs7T"
    "eQ9kNiMK5024JOUp7f5Eulh00FSRsE2CjBODbWZY4Ng4kS29Jkw3SXKGMbsWZH8VTGaHfmB5cYPPrLqEx1Vi/Ii6iK7LOcoMWhF9"
    "C+xFQwZ4auKhQ4dehryWwZ/c/UTTvqp69ihwKffgel2ifVjBll3uOYMvUn4X8Vmohhm6gAFNDa5ShN9si4Xkb4WW52FFZtGGTzGQ"
    "uGzMNWZ2oHA2rhiVgiwFDehXMg+hbk7uhDBO2ANtEv3FE0IDHs4v4HVUiKWY65hN6ph7VrN+cXWIG9IM2x9tCBCHiIs6DvFj7J7T"
    "yAbosvzBaJ3OnsfZZ6PmQq5Da9Hyzt3XqNl2WkLR9fWKGJ5q1cb47gE0YkNwxn+wbKGxg/nhQ8uoym57dJjEAtQSoPY01FM5AfrZ"
    "hQ84AbyxHvNV9evymgNQXpE2Y360n1biWIX0FipIj+dxCs5dBwypT8LKjVKtXVif+WpVaywB+M5G7Zq311KZapJ1ZuaB0l2WEb5Q"
    "BIxujZxOwhdYRlEaiMSIcba5W5mjCBQYCFdARBRoKjea0Y4aAMuefpkdl7A0X4apzjJ+Ow/Cz2ijwCixQEtESgu3rNkDq878ePtw"
    "5lyUGOWtJfbt4UifMEqUKwDThJ4tWUoYbAFwVckcr+L3OffeuOXG2VnApy9HWzPL9vEJiqPAaNN5hq4mBWrhQgt8E7HPSdYo4BeP"
    "t4iDL9+Xy1XdZk9+9dnsyS+/mD2Z/eLx9i9Qezg1VRng5qm6jmc+n/AhhZuZ+32Da2Do8ZaTBaSfiwm0djmCuZkJo9i8XrCcU7IG"
    "xxhCCgiyTM+fxUTzDT/7f5YJo+hKL3L2JfwqX7ON/KtXp0nxoRQn3AAWqYbS1zZLb3j7/T08Jv9bG90SX0mHh2pJGNhROWtKbt2B"
    "23TIollo8nFWNNNQ8Ipz5tO4CUOfETTu/Mt8tbqGf7uSnNDmL3YUcEmaM77xWnZRc15cJIPrzV4eL3EcVSeqGny+hY3Bg+60LtlV"
    "XjFcSwPJGn/DXV7KLKLB6ejZLJuGn5UiofM3OlmEhHuaU3SzxiP2DNl280GkhinCtLayZmjQmJucl2ntNyy9epaFIfineZGswER6"
    "csTI3qaqcSDdPB2NRdsKcS2JNVPop0PIlj9Sx4Q/c0uC8DXaFXGDYpxk9A736iYGcVx/zvFAjso68dEgr3f04HOtR8dGGrCkUZ8+"
    "CjoCvHE8xSk+WJoXXv106XcaEYdkObwpq6RrQ5R0zzPUYsQTUiKN3B6KU2k8zZhhpO2YXCTNuWqiEjIP0DeZamCZ6X9msKwjeu22"
    "nER2EUI/uFFD4NuH3tUIUOIKb1PnvZDtGb9KPhbU7SIysDNWTK3ybm3kFOqXdDfVe7WEoiYMQDb5uWPT3YCWaEQUzcST11JNXPbd"
    "eWySvRGdcIkfNMceye7MyZjPdacEQXUBvQsJi92X26Qyjyjsd7gjeoqwz2qJD4sN5xKdN73xQzJbVYmYzlLPKYDVdlifKkOgO+WX"
    "a8uROqAxF0PDDESNzBLKj9hVNvgpea4C319C40YkRAkgOtaiol2U81skl4/81rBH8pS9Kj9wsJiEGk7tWWtUMVLHiFb/ge3e0naQ"
    "zthDoueyHskdYDcDXtQWQiO+GQSd1ceNTLnYiTidEjUUZpXNY79p4DlNhUSH2XlKK8/DKS3I1E8enFpSi8YP9rS6MnZa/YWQy1Wr"
    "Op4ayuE/l0AIxo4h03n3UwEsLUk8UdCHeErYEXj03vwR/BEx8WrrLfH6ux+AiwXGS9+yMJDR2B0n92eycRl1oA8te7HJs5TlrOUC"
    "uVPg9T/yONXKacQzrM+VcDDqlwiA1cq/5LL9o3jBTFSXrk4MRu+t1yt6rtfbQVbUpqQkjI/jSaYb58tPJBotWuS1287QrmXysMwl"
    "tLjV8I/FNn5aKdhItKY6Vv+WoXukdItCrOFihGUStCB2c8XLMJZqbsnp0y0WX/mJV0no5J/5BCuLSfcE1T/z6cyT6G5xxbHrQqjd"
    "31O9ac38IHYxtNoe9uOSrC2TZKV9zjISMBaVaB3aiZu5lcuHjAsAD67JiiLIUVKkIBDyy1SDF/3oktvRk1o70HLR4j0P/pSix6NS"
    "C0t6ZN7RPlbGzepWIXlpTjECVrRbnpamsG/o2D6f2OOk1hIuAPJ5vnLW0LTMWsgh81A01LULb/vJpZEDWfRVDULFgDuIY7H1ZzGo"
    "8mbhPvJyLz7OgSHBm6cfkGNaRnLeYOLB3CV64KNV1kw7Oxt6i7fhBGWEIMKkcE7pAD0emQyiwtPYOS+OdaQvbyLzTOETGuEVa9UW"
    "tEM0Ns6z7i8hYpU9K8mDXeWkZ0UK8dGB1fm/bDA7ycbL08gb9qI12hLfY321jKrGboUTUImc+GwC8RBElX1uliriMZ4Mr61JhIhQ"
    "TGJL4ID4nvNd8n1HwBJ6yMznI2CatAiHgUlHcYW6/T5n5x+n0GQAnaiyJ0o6gbXBOJO8qKK0mPlq5GW90S9bPK5dDYye10i6D/9o"
    "QOZVQhbQ6khCcHpHs35iOfN6aX1THcmH1t1V+hwVUMmN8Rqu9T5SvTfMOE9bkiDXBjx9EN5oa+h/JIqocBihd+B0Pdwl2rzdXN5m"
    "l5jXRrg9K6XC8edY166m58FZLQYMpkwL082nAO46ZKDeQ6WmB9lNEXcj3l1F7BVn5ffYHwQDo7Bnzggh7UnNEOZrZ4iQRdHBDBaT"
    "ZawE9CjvAA4xzpbMg3KQbockkbGRtYf69+PTw8P9w6/kaWM0NoE6Ot47mh/vsVwDj8Uk1MnB/g63dR/U0fz0hFpiMjkGeLF/uH/y"
    "kllfUUJOAM33D/Z2yXSgviTjDTaS0hOyI0SniD2dJNf7Zdns8ib+hp9hyTFgX7hgeoX5Umd5/5ZZAnqgdqOneALNkqQDuRXHrLSD"
    "bSmgCZGhnCzxm0vXHFu9WVts32+2cC4hfb/WvMDq9RaRhghMfTDVbmds8yfr2T4H/A0mLaRsTOarMN6OZQrOGd1EW6vTxEBtp+yI"
    "uTFwm4GPjwNdxeiQaTCcd9RWDg1MLm6jPPSNuM6dY6AtKxmZ0jQTieSBxXyu7R+6938bdSDN5x/KLhpWQI3os9yEenfydSYTZup7"
    "EpT+sm7Myu5jzB2KvV0wSRKGVmfUsh3gnjJf4drynTAcpzl7PmVoYHPX/sL8KzcCgyTnOW4vNkKbapaALavSjuqXvSGV+Jo9eJxR"
    "zrmqfzg6hzNrD07sc17rJKAfsiTlxVANJpnpODBdHY6YD98y9h1Da114CEoAuRyfzHAgh23f9ynv/yf0jVODK2QgScmf2fG7vDe8"
    "fNFWY7QEgCZB3fMNcPOiwFQA7DAFMDTKqyptzINZe2NYDWLghX0YVJFkVWu1QPNi8qEjPjnh30P0xeB8uBkJNNdYyrk3gdA794LQ"
    "IgENrOrABoAV5Tea3kTtLDrplkBHjvsIoZ7F4Px4EWt1UkACcfJiBRSl8iKWEQXajtqRDEvzxB6YDM5J9jV1adh0C3qvBFpt1oAF"
    "CYPdUSp0g3cnhuTBgITFkEbHJJEyZX82PUnZ3f3YaqgDK559/thuJxj354/Nw9sD/SoC+tU00DU/d8gnLG9GHeVkOYChb8j3IxlN"
    "L7m5dxP9WZD1EkpYkPWyZ5/0NXvmc47oqq7Jw3+eBjJUHp/wWSKDmQ6TZdoUWauKpc4+qBp3MRnSLOrL74C8Y4NHiUY1cZmu+0TY"
    "bRN2ibI5WM7Qr0dslo5qMoSDyyIeO2yWPRKESqmQjGaxntMWSbAFNFLjzRp3iNKiv2nRoHS3Vf8RdjpYd/kZMoojuaJs82VZEwuG"
    "UmXYvLqsXOnQkLV4EfIMo8ufWs+kMD638BiOMk6ehGxwxyWsjQ9GmKQW5yNSkEkeKv3qS4/htFOH074dCchG3w47DZuM0SMAMShP"
    "cOcTTMp9Knq0TLf3p1Na6BUU+5VYEwHfMWC1DJcssZOxoum75sfNzWTv7gegD3AhVSpsO08m0WhDlL6WbIGWLRyWrG/POrIyXaMN"
    "tUiwyeWnDWNauohcrzQQF7fcj4FkHTH0CfKtGCLaBe9KgMMO+0ytIxi3xePGEoloWGq6ppTwheloa68HiTolK9+u1F0umVrfcnCp"
    "BZy0xh3gpj3hkkRYwmKiXMAdLQs+Q3+VPZnaWpUA/G5TqQz9d3IGI/Sjo/78Oj3shPKj1SVgcd2Vk8peZE35fmyykYUgeOXSxzjm"
    "xjo0l2ILhRZ6C4YBFszHgKTLkwFtpMiSZDV0F3m4MJrkVhhFMUb+WghgRP+KVAHhyDE9Ril4Ef6f0OpZP6xWbOmuw0oAcIgknKKh"
    "IpmGq4hYMgw7+CFPwBd5XZ11GgBkh/9Sqwq5Ysyb9TR+n5Olcs8RYBau5haFEOanohxytD9nFzyxrCPltilat5QpX9oFdPfjomqT"
    "pRFqcjrBDuoqzz5fnsfiuPiySVo8aclAPhZ2RXsKLNxlvpzcRbX5TdsUbgVVNMRUL1O7H3znchQfspuINLSusZYDCe0nzjzkEeRX"
    "yRN1HEAg6h5qI42RPAiUaLcnJ92FN3CNLihmGA6FZka8gidyL63JjzlMTg0InfvEw3c3X+fR95VITffHlywWT0RsTPgqhIp8wuMS"
    "Wb/dqeVFAM9vxdf79KDOQ1BllpEFAQnavMjbizz6wm3Sdt59cekvkPL9Sh1dyHJTlA47J19Lkk4VvWmI0ygPAeWBBt5HnL4lXG8/"
    "XIj4G4bXlfBApGgCmXhb55q8lEJ8uGAc6qck5ZSXAiUMQ8WW6c4Ml1dEgUxlZJl04IXZs1mMt1xro4C8G8JAOxOuMg4of8lWTmYh"
    "P0F2YUTo7/mVDJ2DJLWYYmPzFCoDf91bNHwal7htyWJyCGd6K0y3N7N09Bou7VhCr484ecxpy6nMFSvOWomxTGpVIFKtxs7hJkzR"
    "ovqQmP2nTLbvTtYtIcL8qmIBdQSXPeBH+MNQwcKWUXkhB7gnI+2gUDPuApg9CvlVCG3naqW8a/nbdxZArg15psee9O77IfAygops"
    "l8Hm0uo0F+5/C6wLfVTe+rOoOrTz07VK+t1rNA2sxpiiaAQY6omFEtYu3WA4wKSFnSlDAmG1dOnCoR/Vm7AjMJy6p/bhpMbwE7p9"
    "xQTnZ5xIjMKyCIAkgg1RMbxDogNQQYK5XMdRPcnAAxFYL7F2O6rPMkeTTsZlcO5F9H7U0q880BwBgcNAUfOXZ62lhs+vWb80kXsg"
    "lKfj9tSHsyc8N15Sh8yrfEocaD00ipzrdyRmptwX9D3uSePDs/pVEjiUGAAbeIEtNhCTetkVsMIMhwYrbAPdEw/Vm1SJEkaUF2go"
    "VfUugzPmKKLroTqrPNWSIh2GkHCRX0puCptr5pwPmaQuky5ONL/JPKxR2pN4FQFAaG47kOMYXEOS9RhphDiEXsL6WCy4rFRzocSy"
    "x8bWXWuCBI5N2CdhBg1GlmG3EhWwOy8UBxv76ZRMwd9MxXIfj4+fp0jaqp4I4AAFYgeKklepgpQxJ/LKYXAiY1qxOdsi46i+rH1Y"
    "RHop4/lZkKHTLtluDUt7Hnk7LpWiWlBGtCoOkAt6OZMQ6wqtH1D4uJ0dzaXgaP5o54WtYX6Nu6YyPPnCugNaLnxKaOhHNpReavrz"
    "pj0uUXdJ1IviswqgXXRoMPYqj/y7rDbsTETBwvgtnAKCwVc2UpPS2HHl5f7RSQC0420tqUViruxQXhQ8oOAr5x+gOi5Czlf4CoiQ"
    "xcdn5HhdIaUKW5V4GvKgpyeBf60+nPmU9abtuvt9s6im2QCEe914moXYRfRq8ZG6gJIXlYTslasSlSAdCzkf/OXDCE7v+itU+nwX"
    "NLQcRtVpg/hB0qYHaU0xvsjokExuOPaI2JtRLFAdA2ChbS8nCDxZM7czV4WCcx22VRBTjijlj0YZ0+Fh2iIOeRWWZhutB4eQhFDF"
    "aBllRk6NEYELJlNFivXIcpjsywy7w4SERxVsOwZs5Vw8gQ+YzOrFRay4iPbQ6TPGr9c8oqDKxmt6ztDEZduJlxw9jtmQb333AylX"
    "lIln/eUuExaspe6O6GYdYhojn1uYDfEG25RtB4mGdXxGKOOfnxDaKKI9r4e+FA5aYhQ4cL01q6vSlJCvXWvle2DzYgFQcMMl5dWD"
    "/qHj8+Ev3RVU/4umRocpjqgj/2IMIkYZ5jm5CTppjY0HfJtyWvYpZBXMB79l5KGVnVw3i7IANP9AbHpwynO5MYFMbjE5DSPv1bId"
    "k3ReMd8sGVWI5q3yoqM4h4zkmg3qS0rG+GVIxTgeSqtWVZS2icNsddGIZgm2vqyKguLIRltBrCXF1mnRrj1GVAvzxITR61BwctrD"
    "pix3VhYTO+pkCpYzBi+uHfACX+nJ3gY+Dipw3CHWAey61+aDG7SFvn2YNK22dr22fHX3e6Bg7AZ29w9t7xnkSEeU+dY5EOWyLYtc"
    "fQDzmOqYC4JvYi+y2CTWcI12h3iG734E1rdun5pyG65WvJ95WNFSywEIj2/TU2K2P4331FJ6TBEGsUoYF57jKHk9baxLY/4MObO6"
    "RBFXr57zmhrMqTRtRIZb8/HmehwjY85oWDLwnvJh6fALe0fCIvQs2PwaftFz2fxYbq5u/V1yuhKJ0xEs6UCYFqRyIgFDDqfkHIVz"
    "fP5Ri9COuoJg4MSGKN02vQ6d1tle0BcWno2oM3xAS+Z8famjGZpejPbnPkSlSxilS+fTZiJrrOk9hakG6l44bTi+viSim2v3WQIv"
    "ghnLEgfXB2B4vmEks+wkrzpJ3FVIH+jzmfQyi3uJB+TgBOwtYCjGyDXXC37wYIqqtSg1cK0598U3Pcc4SVKh4E4vx3GfsFrVfMPB"
    "v+3mZPe16L1sbmpaazqDCxVNp4mhIg7i+U3qq6GBOgmmwNeAShzu/iv87mysYlZ0gk8DjXGF39m28Dlp1MhhIoRww+I0pndiJUAw"
    "RPq+qQrvmuLsgmX4S4mhtRPCOIdO1t803WRISioHXOryb86rspbYO8sVegi/p6ivxXhA5ft8sf4mks0ieI6E9sFns8+/eJxdiKLg"
    "s63Pv8jeXjzUqhPZZSwNl88yQ8Cw+d+cS5B+WtgoUn8Izp3laoEoVoa2YRYqLX6wPSgqk+rTs1obwucgPxIehsV7903Trjn8GbHY"
    "SSI7z3EHzCSv/Two96gtjG70zT34SeX3ICmVfwqmEqBt0FdJwPEx+hD8R1CVYDT8n2JSyZk9NrR4r2NIBDlxfDRxLpN9JjFwO5DF"
    "HFuyK1spxhoKT4yL5LzfSTLCmUSwYsGB403NJCrEs7cmUXvGI6Bm7u1e3NHUbpO92bYDU3F1I7fdra9l5gvzMKJztdU1KDSHkJnJ"
    "dSJOcihveEPClrNy+agfgHdEG4iinc5dN0sb1Wgoo1YT7W3ko5SdDw29xBu7yeMdS+/qYNqkkMPqTbvLMF+Lt8uaIwTpte0jWVIn"
    "3WIGW9prEOSSbwVvVHRVjrLsPZOaQ0exjo8PNJFgX3ZodNdFBiUAKHE1GWvgGyWym+WLhcSHYA1p7CTGMFFNWz0rxghPrwfewaqL"
    "Pu83Fni+WYsrrIZK2tQbhiSmiPGP8Id9nohDwwWWKPoYfqTjIrMr7NtNGde922FiI3L2yD1Qz5KGoc4soI41QSDX7vh2bjhxHk8J"
    "wK4dGNwmH8+7v/erwsgV5gPgYUqGfFG5bUVSzANLUm8mo/PwPMcxlZoE5rW2HLQTDrVlvAkc+43Hukvm3UxW0vWJiU6yOgYM19mO"
    "gz9hizpC021MlHN9a6BGlvIJsiQI8h5NA5HpoDtrz/25TS+olg8ZkSCUu16hQQZncaao0YY0W+bERaJdFC93Gbu2ky3JshVLY2ci"
    "TFJcoVb9IDFpyFM0by5Mx7pfVC2pR+mrxiPgr1lINK0A4oyA0S2Wd99jbix8aNLbck1vTYIqGbUu6qq/1G+r9aPnx6wAWQ8Xw93v"
    "gSN6DmxUVYdq/IZe5Xf/SG6L9JGPVzms+4W19eHy0Q4q8P/vf/+7f/pf/+mf/ueP/+c//0ctE89dP0IUEOLZrGRWEY+CJru9p5Li"
    "AU98Ckq+AXNrGC0KBzR42d0PfBWyIDR69EoruM7vqg8zJYooZ2/HDkkI0r8lN84jDNYselspSeOa4zcJgn4k8Snlq0nS7CnFkXyr"
    "UM2uR61KXvvVWUle0ibQCdYwitRIMHObEOHN7DFZ9ef9oysUa/eWZbfsIrAn05r2APAZc0AY8VMeT6HsczqAQx+SL4eyn5PxUCyM"
    "iQB+gffMQEKIlt9NWPb4/3+NfUbmw6RMr8urECWZ1CLwRmSXZRzskwkmbZbdt3ueEgn/0XGYMBcyXbbDMyslEVW+VdM79YEnYg91"
    "bJ+lMmuLtmG8ossDjbJnolfkFN8OnE1as2qTTRVwZQop+dvYNbz8kJVXFYbIlQ6Q41mVGLa2fyrhKrayHHb5SuII0jUUWDtpRQf+"
    "ecDIR2zXMBWdcWs6mOMsewmbi7r0tvPiuMjJH8k05uNQ96vIri/nMcYb/fOclYZeatrHwTb7DTFyNsevfBB8acts3lwvhrNq8XDm"
    "ZJu97HDPZ32xZqlXFBJyJLm3MaNttEpr//ff/SHbe18uBmTr8A8T2x60eZGJ273pKEhJzEK/kNk+nJdG1DPa1S/y2GNNiBM65W2r"
    "cXtQ3DgxP7lCNBsDTVLbZ6LdjQR2205Ct6Vy0nJk1UcNLCJF9bZdERLdJhcVPJMIq6XUqdL4ERIjW4xLLLvzLDsu4S3M0cCYashZ"
    "/26oegnocr/Fz+w/3G797eVf3/wbFISgnzRGsalJmIE/6GLRIgnxvlN2nf/u4jWrzCsUXrTP7ZriXHNSELkSXAQmU4rZm+rX4UNX"
    "rsnc7rhEdGmiTkRQ+BVxM+67ZFvcwzzRuBH4v3j5teLkRx5vaMtJEpxLIDF0DfdSREexjIrYqZicUNbE39U+3j+6fLqI8tdJyTXu"
    "VMel82tUDmtxk18Zf3VSLiimDJ3acHMiSK9WCTucUK2X76k6jtVoVMNpHwqnUaAyeU4GazopsKjhYpBcAWGhQOGL6u6nRoAoj4Br"
    "gRAttIMdD314OL3CUN7f+iJK4H3UlefVe92e7VAqu2flqaMmbaGDb9p507Pw+iZfcGoN49rIUgfDQMH4gVCipw/cEGgcBIx2IMB6"
    "PYnrEUdNQmQLFvhDr1F30O4Gsz645OSS5g6V5H9osFc463WtIUF4VLOJB1IYg0QWKMsu7HWI1qGRzRoyvoDGy4YPv48bAgPy8ZeA"
    "gR04hN6HHO+eawSQeCC0ndHAYWEzTLQreokGe8CHBTIYd/+Yu8gh/OpAdXR19wMMCGULSouq5oqWjUkhzSZg6ObpbKu1YZ5OAkat"
    "aVLi2WwcHvFSrkTHVzPtrcvSc+M0RHjBqSDhT3+ElwgAookKXaLcCslDFPZ5W1xTsmTjcxZdmWdD43qlxOx5eCmRvp31M9eIH+05"
    "RYfGYfVSAHwHYMdAUtWO0zxKcg8MkZbDQ5cmoKh97eac9aj2pz2LRg1Eix7GgJdoQEbLDltGMV9ail7Z0++8o8UMQ9VOsE24iKu7"
    "7+v2ojVFbFHG8txqLdHRbP7XW4pRMHaco9CHLSKbuaNzgoFYgExc21eEnFvYMYmWW8Jc1scZIXOD3ILD1q85oMnVUFKaszyTedUS"
    "BalfG5U9SA9tSL0SbBtv+kugQbecRlEAEzi1ZQyQHA8iblQCKwYPd+NtHKvYxGLeuKJ3e6fKZf/p1V84Ly+r6vaurwgdWCGIsYeI"
    "NlsGG6DB0A5ZIBpQUqZ2adekqpwiihpRLNSR5K4j4ql9FHmokBcvgqX5IXLm2QqZJDjI3WR3o0n01w3yYydm89DZQnoQ0YEfYLvh"
    "ZrhEtvma/T6AjmB4efQP7PngTu5HfH7GW4Od8aqFITVFG1rDkxPfC1wvkvwtkACTDUCtSJV7oaxVUcNIrpa7CLAiBqrJhJVbQ3zg"
    "z51v2U0pP6vQ+psIcGRPVMdL4N/CDRDviQUSwbqNNLkc752hWxe+XvvXFOXC7/J1JpOWK61Qcgf7B1gCuNW3nOaJCcSINf0YOjft"
    "aVeb0CwgjTABonBVxjskeeJ6Z3yP7CMJL4YFOnNnlK/Qbuf14KQOjamur+EE1MC/HHXtGb7l0acDbiwgrrpJkuYMzaPhLvsRGupt"
    "/LN4FL3kFyGm5ToZQIpP4TjarO1IAloA3tKx9N1NVHVdRqcZ9pmkQQ0bEIzboFhswRHEeK3rDZCywraGmAUebsSwl7NsfvePd9+j"
    "OxqxFAapSxzI3ixpOgqHzxKTptWoBMBs4mWOA5Su8M1GTCeG3BqQSZra0YnuJBpUWO+4XUAvwPiKH3jk5YC2KrU4VUYtyGrs4LGi"
    "cZzd/aGHW7Pgdyle4nWoHXwBAr0boZCG4/wUupw9ELr8kOKuGl+moHXJGcbcw+opNFmy8wbRo97dEDgGHGrZ9SEx2gubeVx0GMpg"
    "GA3JpBXCwngdtksyVkOZSC5MCKr9tyTVM7K1sFJ/IdFAmQ7Erbg0wWynFdBSAS0nqsIQqwgfOweU1zVnN+0leICsP4JFrU0rv10z"
    "r5zbcGhIq0VtTSvaXVtfE0Dc0rnB+qbIgMXysogBy8RiwHvVTJlfd0XZTIPl/YKEYQsUdcXDwjehiCAmCqtO01ER0nci0swNGE5e"
    "MVl1wvCCP4lDoG0nSkdYdY6bky3vvqejo9GEEjgZzit7lPQR1xhXRz5WHAJq9gUIrQG6Wf7b3wwVq05jJNL4jFJ8PjobtEsapU52"
    "aZsyoI6AnN2NAYZzMgJ3aGngyzF+MrDhnYGeTyEg4ormHBZc2UbXETizKZTr3iAnuidY690gN/fuE9oaeOQPlNaQWBgxsPptRpBk"
    "uPPNCB6F7J3YLkfwGGhrBM5BDdop+JWGx1FYFiFwjDeSnSE2zc5qibNTXpCxlny+6Eh29VVHKhf5+O6yoiafYwxsB8y5cY/bb903"
    "YKM5ouQhBm771vV4jWKHd+TkBBS2rqNey1KMHCn3no1xIIz9MNTh42roVhy88O4PHfzhelhx6tVjjlSojXQcB+wVHD1GYSlYwpu7"
    "ojNao56QzxRjahxGNzwLo9IoOKCRMj1rB+EgAasanyGGEfnXqwmH31iGGYF/PSbeCTjnEKVIizaFsgnRAUKhm4EBiD9aizx2rKzk"
    "Ag1q+C4OakiyrFkzLM/KTqJuMdtC4TQNgG33D1pMMYKx8q1A7JzQxAk49nV+0YcyuNpLjTP3X3CwGGr/HY2ZRudaR/Qil9DsLCes"
    "5AKJ05j3VXaVL+5+DCXBczVU2+a4m1128x11QnKtplxbJdmKgzi5ZLoNBLparAVMXKYdAZGxNUdyYvfcQbV0Ar1fvLwoi/1GHy5k"
    "xIR2CbDkAYr2llvD1Lq0VjEEEJMXYj0YDAe7dlRurrL8EBSwbbUp5CuLRaokcaMnHF1sds0xT5f48VAnZIL4RgTpJyz/uWyv4/L5"
    "RetKVUJfxECv6yIBojHAA2C5kujQNb3r4bG7bpG349hK1z00dfdj3sfNyaw19CHqICMPYJZVWZ0oabnwDZo2WyVR8yAGq42f14NB"
    "kHS4iFf8lqQWPdmGM+/+fY9iUUvFTZtL++YXlcokqjmlgdZvPqc2Dc9KhiaUoYAwKZYE2Xf/CI9luJjCQ2RqT6mGWpW+wuXq/GrJ"
    "zhIUcSu7Avq8RV0TW36rIWpYP1RAmOLBvdpsfQONPfX0lQrhBHMETxl2GS0nOgCQE7EuaiH2oK0LSENl5NgrSMEAW4xgMNzHs/CS"
    "7Msg18qAhot0ZRa1s99cAUARSQNgaV3egQsewzK/bjmjy2OVez55/HiGeay0QWZSDGmkoifKDsw9WEQ4o4DxSjC0TDcAA/Xjo0TP"
    "yC0SH3FqCDxcq65dVa0iyNPsMb8pHc4w1U2GPrUYSETSmWzRUmfjFQAUVadbQ1M0AVjbaUGDe037WBB37EsxEn3IQxp/lyU4KVV6"
    "xunUwgPRn2WHm0+BpvzwbY4qGJyzpL6hV7cIqXXonLNdRu6+a6atneHue4q257iLCCasHzVSshA7xzTnQd2DugmxgMDFaLvkYAfm"
    "JhS/McHLBhj8z0wyeV1TsiaQQChWbABl9k+f0Z2kcYQdnEt4/RtUzHgC48A00wCZ0oyH9r5Sk+SAvvRRHn4C11B0BofhQ3nlO6L4"
    "DONT43c9qYIxuuNeI4rloMj7d68mL8BmapoIJAh4HFQlmIIn7pz8lHL0k8ISZGFZ77KGq6/s8vWAKqHrkQg7Jt8ONZrWrDSm5Jws"
    "U7OK/VNViMnyuZbOw16+CHY1MtxK3P/6WHyoS38Jz2INkrcXDTVoI02xaOw5EeVZduCF3Hp4G1FwnU/tDSwQ0m5KRNiEHvK6vvtx"
    "Nh6WcKIfHdjouf+vOTZW4Y5GJ97nvh+WC39ab077yLJAv0GERSivOCsbjzL8UGeZWqwdCEAmC9uRZ1b0/dCEKhzENxAik3x4NiRu"
    "gj3yUxGJHoe4RZJ5q308+rrJwTIxtIndbHz5e36aHVAeGzhchZtW3TYX1XooKk6efYpHBE9cy/5P2mvZ9BWlFtnFX0Ve+AP34UPN"
    "QeDtxHL02eyshUujJsZPgM8kz3wKKQ97gYrcjzZtCPGuvx1Bxtd1AK+aas3rQKDsbluPyoVkfU21iVqt7hmDF7KM2RK/yus4+ZC4"
    "aCmaTDPgRubJYPakuhiq+AIQ89r5uoOz6XeEc2L0LO2mY4RSfgqEYceDNRqYaVXK3ImQoFMwP9hAfgy/PkOnZ3p8jOHWbftqIMH0"
    "K2Qr5cGymlxorSPuI6doREC8M3Ennz3+7JePnjx59OSXjhB37ZIZ/MJNnsy4XyJbGd2IerXuTN9wQ4OnPY62ipygCedslBr96GuS"
    "+NPf4QXz5LmkFr9RBv7WjD9Kd6lnwkKSKYjg+umTp8hcU+SNmjYBXt2hcqngM5dGOTxz/vRHfQQJA5I9IH7loaeCz7ITeDlIf6yy"
    "CIYHrM0oYzWJkxhH/RKjBX3GbFTPy9qHdApx7xRqFO9UOOgVzAUNjJrWNzw0NUu6/kULOMvmn7KA2Z/+aI6rz0adM/NKL00WrUsT"
    "5L1WrvOqNnmz096xeSa/hc3ZOe/Nykl1aKERjjubRKaVZ14CMopMS/348RzzqSF5XM+abR8g9ucuyKfUcUFEWYHGIUDQYLtx4WIV"
    "Ohcfp6D24i6AI6cnI16fpdqg3bBKOl+tSGeKlmasGbvJL9pbV0IWEaZmi8wRxU6lnvXxyY2K1iJe6tdONY0ldSzAMvGgqdlUIzKo"
    "hdJYkRHnBOFch2Q4KAP6uvTvBw37fy9miHyp4AgLsraxdaoIm9bApPktRlk5Gari5Yhm4e8xiohFuxCofC2IkHMosThMsQD5ALEb"
    "ygThRkgTvGtFmCHfndmoA86v+/lFKz2R+OoJiaUmQKTDIAgT6VU4CAt2Kiw56KN8F+nGac8CMsQjMncJECJ93VujvwEUq6M2l6J/"
    "unubvapGTumhn6PN8Z+1r9zCoIZiCsIDtwfcsfcdR1p4CXkcCWvwLHPg6MYOyTjw85bQQDqLlAF9YD10fDq3sxt4WMP5vY0x60gD"
    "mlu2E4+1opb3T9KQCchyBc0RKWdx2fgYusIkSRDsfRWnKtLEQIDzdz/FJS5RCtdPAULGpBU1igTMDBD2nNKIS8xq2OhxN2U7PAJ2"
    "lFkrNBM1aBo7uC/AI3Nm18U69I4xszXC1HJFJjHsN8c8SgSk2uARoFgrbrY/4Wambd6jMg2lIoSRzxUJw8RFB84HUrEwtn44o5cE"
    "fxYijsKQLr/GD3+dNeUCBbEVPJX7u5/qij5aCEKA7DEIIPqh8ytusi9NBk/hCOevTnzO8TV/yl6+cV+BRS47fsKYsJQ+tRNAJ5ca"
    "vTWFADysLyVk3o7a70ZZ39v1a1Qr3QzwXABUyBsk03FaYwQ6ZKPryXJApb0wXC+CG42nKM9z2JtDfqB6s/kJiEMPkqZahvIgJpR3"
    "LlKNaqJNQG3u8LgktthYTb81Pfut0loA0YxCN/O0gT4hjKUck4pFcQprFyR+wN7hdrZe1iorIWmXKWR2F7cxJ9T4WRYjBxS8XOv3"
    "GEOgaO89l23GEMuquldXHHNien0QSmZhkIwSDoy0BJIozr3pgwpiE4I07fqFPC/sFeN8qdoJUDnJR2SChEw+nDLgSfA0V3JW28Di"
    "j/aRl4x2q4uIvwcyGxmBc/vFIQgpdXiUEdO3MaxbFWObVxjpP4dYsmcrHltmzvhRMWmZqcHgsTlvPDz0A1MisQ0v+xU6Opzx0yhq"
    "qtbUCEjmOgxoeE1uhGgNaiYtOhfocshrmc0JlNKdfUXsLVBlzQC7zZ5pyxXmXiZdmH9wkatlOCTtDEOgOM81CWzOFmqknnCndRbh"
    "wAZWlAJ8ZXLM1oNb2WvEi4sywUfiPhgjZ/HJYfyQN+DUkRB3Ew03uod+ZuI1QnpVN3SJt0k9Rn4S4lYSt0gR0/6ZLQr5UWctfvNF"
    "h/ZPf0yOLQopB92LYPAvx9Oj9LNRmyEpr2/WMqF+rGWxg7V82evrFXFL1aqNjoMvfx5ZdMLBzB5oUuaHllO8KJBFIjmh2sla0u+e"
    "vVz4fOhXF1iCnDXyvoQtt/ZW1a9LMsqsc8DR+dF+Wo90As5cktWVNgE6hkcdcLs+/zg3S1V3memdr0hWjHxXBkXsBqBJ7i1fNxIF"
    "4OhruqZQvCAvquB2Q3qrdcXG4Y67sPTYNBZ+VcT2zOTQIcSDfZEWYT2cDCWP0RBFIOJrln2ZHZZrWJS38MvmPMv43S5UKWmXpXGo"
    "b2M9nS5z9sAaEI6/fThLM24nbak0AlnVFc6hRyqFDkXJtT/zC4KrjBusLkI8BHQM0OXfSiaZ7pWRG+TsBrK56KtQPViaC/PHIF88"
    "lvix33L82Ce/+mz25JdfzJ7MfvF4+xeoLp2arg5u80StX5sl3EKXhyVnkHQ7hyx3/gHzksfL2IaOHL4PDSwQVIB7hNtSk+KyME9k"
    "ig5DSeq3sz/9UeeMxptVEaPNs5jUvmGZA3IphMiu9CJnP8+vcvViePXqNCk/lPKEpcAiVcpG1XHUZIhNeehj1uIr6e+QfL3aiMWV"
    "06fk2Y7gpkMXzUFuziPRsOMwRCItsZiVkhP0LHuZr1bX8G+HNrDzFzsKZo+ffrhuUUtoWV9K1BCi29gb5EOHxoYiLGXIoseEyWuT"
    "muyKrR9wGRt/E15eysjdgNyIeSFpzOSGw8LBWAMlLIXe59DsRZePfBi2bSaMzmjAXJZbEhKFtVi04NPrzX57NoA6eeYXZbIAfo5v"
    "OdopoqHukwRAHU810NoV6jWaNtzp6t8EvE+tKrw/azdUBBxtiHiOJT5jGzjIcb05x4JBN8rUn6Xm6ATBn2dc2+Xt+1jXwrLgpBth"
    "lidYZGlX8/y4ZUKsGZo2rLwxzIoHyYZmUFv8kJDkAtdb6Wqr52YY6hX7gI5cegBPcRE0ebdJVf70R7JtUM4RGU5UFhP7/8yAWWu1"
    "5/eSrSccnj64UVPn24exdwiGSPdeHNmeMqwSu5rDQ5oFobFbanR4a8OGZ5gYiH2LTtJ8u1ILBiE7ueN5cx1Oo/KWaB6eUJZqn3Pw"
    "sYMGl2GJv+m6gPOJ8UCcS7ee2K5GQR8f9j58bpAaYHCHmFB+x5vBx0Mykt/9tPGwkZurt9mIZiuoZpuLqntiXbNItfIUr/WwQrxb"
    "wadL55Ythrvva2R76LZnp2L/cPOXNL64jGalNKFp2emWilHAbnYEZBzQxhvEdl0YDhbjA6NEaoLEbd40JXjR2nNHD3QHbfsKCS/4"
    "kGn1YlBvvE3EnYkK25u5GCccvtbc/nJa4qbdmpzZj7mbGjwAYkf02i2k8zZX/uVsWK85LKk+NrWkZh3jHuxodWW8snpOnUQOuBJj"
    "kyT5n0vICeOxfPRKNCpcsCpYBKKhZTUbj7gxEiGiixcQIGdWiMDldparFxye+9EMHG/26YxZwsUrl0ZkTd9V9j6Th6kPxvY0K+15"
    "CrvlnqOJhI0a2BTvTselTpsAWq2i51u2fxSvnIn0klWKoehx9XpF4ZTqbdaXrrFXjqZOMcZMwSRDjAOQ6hb68hOJkMwhTTAMJlsN"
    "tmJ6weSGUjx36N0eVf7IU1FBTR6n8rOmBnTzTxbGncIvEUk3fBhDQT8XLCJOLtCVRbpXGhLAtj9Tb9zRU2S6r3/u+6sspj02VCnO"
    "IUWgchz0L6464c4R6vf3NdC0quxMfTatvgf+iOCLreQGouGOQfVdzzKWVTatXiNVJzKyiRv+/O7HXnEUVwxQ5prMQoLsZYxBBEQe"
    "sGrQY1+TDKDSjZaKKnHHvFYb1SZS8SjybRza5GZ1q5C8XqcYBy1sI7JagSinoG+qlev6nlpLuDnInfzKW4hzuAwtXlyKI5O6FAbR"
    "LpdHXnfR1zeO10tF19zJsxie2T13n3mmrADWK2JwWMDSjoJDOM5jKlIGMbIoeWY7bOz9bOgtIkrokNFHmKGSwzQH8HSsNiy8V8nT"
    "QhI5Oy6EiAtLLSL71S2WzfvvQjo47t2q/ADMmO/+KBdt9kHUthcyBiHJCoCBnf/YWP9VBraTokueuHpoxumeyGIf1Y1QiUNyT4CK"
    "rBo5icUkyiKAOp7anE1q5JMjCAbBDBP39Qgv+ZTTqKRS3C9ftgQvkabEGyGBpvmLhBqeDCgDUV/s5+xp5RWwDCGTPWzZ5aAJRBlP"
    "M7PV3czDk/P7JzjOO394V38Ni9VIPp6DVNVwnbsLEKm2SKCbVrUnTaTT18feEX9wsmhVeCukpKjZb2wnrahhzt5kSOlhWgxdH1Ug"
    "zy/RmbnTq1lakQX34JdoF3hzeZtdYgorYUKtlArHn73FwDigaQzWu/t4lU8VR3fuSlSdAhNbTGQ3RdwB20z8hnEjKZyymYjtpsJO"
    "OeOJtBk1n5ivnQFFtqkloCTw7mHgXcAcyonCF+tCFsuDc1B5jyBOTWxNotnA8enh4f7hV6KgDiQ5ATs63juaH++x/Q+yj5NQJwf7"
    "O9zYfVBH89OTPX7LEA0dQ7zYP9w/eRkWeaqVF/P9g71dzhtbV+RszvZfejxOk0vMADCW3i5v4g4/CdXnMD4GVgEzTs/y/i3Pi96W"
    "3YRoIIFnCdax3asTHL0DbynuzGE70RyHYQ9ttc7Uz4DQhEgzsKt34cRUBEwdXtXUaGzWKGvZPgcUDmGn2m5ifArkQ0xNAo4shnK3"
    "bR0F6Dtl59dNAfsMevI8wKXIfrAGdgYDYzdyS36zjWZ5BjA0cpx3MaDU4jL0oOZAHHAlilSvdobr59o83prj+WLj0nTOUs4wKo8a"
    "UQHfc8fhOuWrTabN9PfY2ybI8jFnvI8RKCgMunCmwh7rnFq2czT3ILmIfB8MxBkNd7wVQWoUYcugnXJYdYyFHQZhcOShyK3GxnUT"
    "5hauhuU42wkq8CCGEGe+B4+zlqzsHk4cy5k1CEf4OS+9i+xI4WZEbcxBnqxua+F2pr3x0Da5YiEfJlro4KRt+85Oef83d0b5nq7a"
    "eqAH8p/T27u8D8hoEyCLPANoAr6y9GUSal4UmJiCcP+kDKGI4pY81KEYeqeA4nhukkdKhf4Te88ACV2szQ3ZyeYxX8V6xN475wiJ"
    "uulcOe/bck71J9JEz+I0SvXvfnKNu1b7lpkxboElGH1JvB9riehqnUWHPTzN9MzH+PQshubHjljpD5iwDEhTkGLUGgiq7PjFYTqo"
    "qBlJWBZPj0I5Yp2JO8PNl+RvvZduB1tG9nPPu6J0J6jQTd8tLcrpiDICFFCxCJDYCslCwjnhy65qC6eogb/apHT2+WO7pGACnz8O"
    "HvUe6lcR1K82QF3zK4g86zAJQFqek8HCGz8KzG9YBusHL4r2MTTtGAkvDAh+gy40tyHLfVXXFFnhYBSBUuyQMB0cet6hmXKRTzWf"
    "kzmWH4PDiJl1NRF+LurQ74E8doO7jYaUkYVRi+T9accKA1y0ErqIw/vH/lg6rHHwDCoAarJORiGxsNE5yY9msZ7TFkmoC3nFZpPd"
    "oQDqb9oz2btWfWj4toHR4xAmhMCy7ZdlfS4RMyjIbHBfwEVryBK+MKYIfZRWahSfwjieaAIOMyf0JyHH4qHeaz4tDk/IReCkHEMY"
    "OcRtyzkzwX2yeYfTvi0JyEbfFjsgm6zuIwAxnU/Q6dOM58OStNhUP76jYmnUdCvhGKwvK3WtIUvzZMRo6i9KJuIr2MAQb7HqquK0"
    "v0joI/2OzKbXxijBNV/W+FbmEGzAUmE28Nbi3oXQzyHMWu+i8ZQuIkQCJevJwWgw4BgFEPcx15IKYbd9iuYRjNvuidYSAWzIGmmS"
    "cyaYbl7a4muJDCZb0K7U6zCZYd9y5KJS5R4uY5sO4oRhUnFLr/JnreIoX/Cm+qvsydSOq8jgd5tKZR6/o+OaICZRhefXKV2gXR8t"
    "NwFbtm451GS3hUk06Ib24VnpD5MJYaBTJJRhah2acfX8oof+gq2ihV0yIOek3SPsWmN2rwa4DkygpGdo053G+pBa6eY9ZHMWk3J6"
    "zVK4Kfw/ofOzflit2ML/RAaXAOAoSbZFo70GEt+xQTwNPwFe5HV11mmQlh3+axHRuIX5DZ82qUx31Q3lmQSXDFW3OEovPjdziSMg"
    "LqizbIdDbpKZQjjppC/eYn3J0l9fbbI2QnFOE64yMhSaWPDZ58vzaNVVRnfPNpy05CYQy9ASP7gG2CSS60/0idL8s7pMWxWG6ITV"
    "6SXZSKRohM9oy/NY50EvzY+c0GLLUaL2EzcnCX9ji+ivBhyEPLcdxGbKhLk2Wsr88JJ+cfizyVuOGZFDIbgRD+KJ40tr8fDTvE5H"
    "Y0LfSPGwfoFLFRWsRCi7P76usXgiUGfCtCFU5KQfl8gC7k4sL5Z7Ti7mE6bHdB6CaqMYDgWYKoMhcx92gGSWxV1Ybef9P5fsIs9l"
    "5fuVugDhD7Jb3Dn5WlLfWtDeoCIOGS4o7TtwVOJ7rxGuLahOn5lxTsdOtpl4vGvSeI7LYvKR9SCeXFJ8MXBW9q8GsvJw2VCM6CiU"
    "vO1cDumrilJOR44G3vSkbDYHAnfmatemmCdJgFh4Of+ASfoMw0K32a9kAhzzqsYUbvfNpLIKpLNgBacYqIqLm17gHMVNEypsaFaH"
    "EsLiufgzqayWUk/n3do7CjfZWbt2OSeqtTBaGPK/Kbt4dcmgM3pxUIrpd/QKkbSybJhhQNkDfv0/DNDqv0PJX/QClJPdsw1QFLtT"
    "MMsxLBTgje8Gqk8e7RRqW8zJQ+TAkFZ+Q4wDV3gIPJKgq5iqYL/B9TCotDQE83fONrDX3AZyCURpE5Jh7GlyGB9VbCXGFCIusU5q"
    "tTrgMSdN7UxaUjBLt4qWmGjHZOUpWwrBw482oTxZwlZ+4gBeMeH6GXPiQragmAlub1mZx46fDkplHorVIwQS1gxo1reUJD7sJeHL"
    "dtQcS0lNqBqXAUER1QGgL/7Kvy1jCDhPlJcBE3sozufXrBubSnERANJpREcvyauyE77r6HkfToklrodlo8i9fkcic46Xg9/jXi0N"
    "AZu3EAdC3BT5CXB8qsJVxgyDJFihiAqYGkYipvEOMWOHCQsu0IaTNZrC+/i07KuafOvhMDpWJi7WkdHNQSctCtIQsqmExcj2UyIt"
    "bZ1o7p6jdAXTPtmpy8CswW1/JcSV1LgyDhelUaBCbEGODiX68dhqyobbXau6IgTA7KNQiwFMFmgXhXNB+EgblESA1AThdcu0s/fR"
    "HvnZTS9xTIaTf2gxkSYaZKpRLtZBqS5y00TiKWySN26ukREoMDUaPY1KjUwgYT45GAcsZI4KqBxTI3xLxFXZr8iOjiTJDQnqwiKQ"
    "mbeBm0nsYkD/XrTDR7tcElxvZ0dz+X40f7TzwtY2v8atNVmmfGINCi8iibxd5FE2X19KhmsMSVLChCUALWmoArBdxWjG9yp3nrCh"
    "Adi3w7EHY5AZ6FDhC1kNKksauwy93D86CYBGNnRtKBO8hSlEqLwoeEDq1uif1zoswmGKBepxx0cFZTwiDz+NkLqJLD0gG0BlxR7q"
    "vNKIAJv5FAR83STUkJBP9VuLj7UBWHtRSShpucExt2xH4Qoe/OXDCEyD55IqROyaSbyAwX1NO6aBRC1plWC2XzI8PNJA356J8RLH"
    "oRFjPzpQF6UxBWclsNDlyZp5s7kqX4IvuK2IGLw47tUOAgf7ox6+leSO6SJtC4diMgkVLGY72PhU6hiovGCmrMlIGIUufmbaTrYS"
    "TaDf/I1JQmBTpjLhcQmbH0TbzH1OWOGkqJa2Zkl1DWHyjJIEsWCgyBlFmtFtoxpgJk6dU53iAqBvfYjGjSw8WwCJnYOc4Gazxc+2"
    "q4eWj3zKGiZwgG14MW6eta98yS8HjWDxsTpo32663r2Ny2ohQWJhWvDNHmkUW+9yrRRmWKvazCbXW8ofSjqcGGvQHa7BEyY81CWS"
    "iW9czug+RVnL8EtGPnnZyTWmpGXZEkZPRNoDhDCnR1k4LFtMz8Po1flhlh2Sgu7apyIS5vUcbfi3w6HSXGtfZnv66cuQQnU8KNI5"
    "8uEMVp4khqdocZHbf3IwXlZFwcm5Nx8KYrMp2lNLvhHj82FxyXA+QePld29TTkoriymx62WqBicYX1ynrGyrAgavd9gOlTgoFutt"
    "dt07/sENWtHfPkya17xgoWk4wCFGDCuGRi+HSMeX+W4G9oxewhEgYoEERUzCxkQR/VlCM3tsqtuSByRJ8jiXD6bKu/sRXgJ1+5Sl"
    "mV5oISOMNkHOkHlEktJZQoGyau5yg9gt5BT0++Pww8dDRDSItaaUygcffKo7RRZehI0VGiRzECaYfi526TZmQ9ODTYgRDQOXa/Ms"
    "4GQkk9a+4Cncs1z6a/ylroviaHVzdesvytOVCATFYNWJTFVGifxcyflJD+ihzW1CQ+qfhCFHG6TP2/oOXw1ntQtczgKNCwtl2Tqb"
    "CTSLWuXrSx3W0PTiRLIzzummyxklzgVytNDcvvLagKkUkUkExzryqeKeJdAsNlPxnqbZGo2A/NZ6jiVwSU4hHGqQOmhmcaM+zpI2"
    "JhBvAYExxLQk0gN+C2PBF2ySjPG5YFE5v8w3PQfe0TREiRyvBoQeBS7DylXzDQfVV+JSwGYUqRfF4E2kqd50GqX/j7k37Y7iyhJF"
    "/0pU3+pa0q0kLTHYIIpiicmmCmQagd1tlx+KVIYyo5SKUEVEIksq3SUPgMBgsI2NDbgwNnjAZrDLxSSGtZ7+SV9lSnyqv/D2dKbI"
    "SOzq6vfu+2CTirPPvM8+e++zByoqztZERRzy9lCnk5CKa0tQ1RDGyFzOjnDpMvxO9HjFjmwHxblGo2Edrg1L2a50G72WEvLox3Eq"
    "LgyZn8sAR4BEOw9RT5aDVG4JMA8zay+2ax2u6Sk7FCWFkVupHPAo8Q+NhUFDIkZNTKJ2Er8WjSd4HY7cIUdvjtBoowTSwdryuo19"
    "Xo2eeNaW1m30xmu9qmZBhqcuwTtVDUCHQ2OSIUPHxLNTZeRcA9gHFEkxnAWxVBXzU72hEhNwZ06Q7amKnJia2EMgHYkRFrffa5Z0"
    "6lAUZxzlb5CNHp3Mk0pOcCQuESrwHXRU7w4G6jr0FAym8qegMZX/PFwmUL1xYlmocwnk/EKcSj+BywSjAl92IimQOyfrjqnzVCck"
    "B7LrWVOZtfl2UO6ILBuJC6vmfcWgR9WgDPUHOFDoPiu/o/L5UyHr7CaMBZ2VVkK3iFFHeQj7fkb/4kIZVG0vzAHDtxyelZtxzq6l"
    "zVtUlnXTvg2G9jJqbjgdGW6p00He8uitoBIAfUAlXBM++pbzraqwPXaz7EA7hnJWwdu9nbIR8W2sGdFtXS7aP33BW7uYW7jm5IF4"
    "BwMdwKNOnJGYuOj7nhpPRst/QtUiE1q8WNWlQpNt6NSzuRyaW6VyM6F44vv3SHJQ9AIN4aiaRWOWUcAl6iyjEXyjnJVlf3RUZ5Kg"
    "R/EO/0WGc2o7u8rl6GrzIidQ4tirqRYLDcDuSLERIk0JEG0EzGD0qUPASOAUQwBtCSjkwigaFEFLsYbpGmCJi3UaejSn7BydHljn"
    "8FF4TLYzDTPvJzhmQ9Bgd8laWmOvDh6lmyGQaeYmCTaxxuam9EXiLG2r6JUM+DTvZmvdGC/N9ADemiEpiniOBYDWTnYB5NHmcvTm"
    "h2xX4JlzBTV58tnQS5gfx+5I56u2MoqGXTaIgyXywIcVWuEEqn5+5VyiBvdgEbbBFbrdAh/mXDaM9QOYLWt6TsNqshcUkT1BoNfR"
    "goD4nwY/i+s/B0gKpAzncILFEAKoRtSsBJwengK8a4wqEaHiQYvnvU5oiZd7g3QrIFNy5g5NRFizLk7VuO7mhJCTtB/V9Mv87moY"
    "kyqEvqrwHfxVdCWSIV7BiKPMoNa4YPARFpszEqMJijULUa0RpnX1bTJbs20/P25lzVpz6RrwattgYGHDVJMIdWjx21Afq2wC0czS"
    "Ud3WTH3NdjT+WLkxv/zwg+W719sfHVNl4s1uj1DsqxteqGdmMUoYYTX0LLv/hqQ3KXEQglpj6RuMgNQkYqRsy00uoA4/eGkKV3sq"
    "nCkr0msnvrFy6QFEOk7eysNaSUhP8lKYT06A3wpSGeBnrac0Up5iQXVFfSfryiKNVRoxIJxvBd6wTK70ZZqq+1nNjlCp3EdeQl6V"
    "GDqMAQktHxY/H8vow1ToL7TbMOVrmSWbQKW8U7AOe7JCXTqF66XQqKGc4g1iM06h/GMp6vv/ieUHqTXEGKPRCA7Li0As+n180Aqj"
    "JufowXH353hGlLJ/akfNPgoD5GNs/yHB99TKPMB7Y7NNgRDln7rOe2wa2KtGu9Z9WtCBbTQza9szYvAHSQtNQSXw+XA0CSu+Xvoy"
    "evADkACnsdItSSSFYMYLDuOrijzrJMFkgLmGUh0Nxhfspi2x2FG80nzViBr9OsLWpes1lTT8KVFQS12ip2L4tWmKPoXKUktPaUfL"
    "mGZaFVmOGjxCd+/X+07AHdI3m3AkUWEYKh2J6ymRYnuMr/i0NxhNj6LU1IvKX6cr3uhUx4JhXDBq/W7PKXr4aOuvlN3/OX/fqLvx"
    "D63w3hP7VU8iU+j3JHT6jgLtTTvBgba18JaLvYq9bfAtb0yxwx2worrxext59HS+szw1siu1XrGf9B3V5IBRRZaUHnnaoRiW2aJu"
    "b7TDdGFAoszadgo8FLXEurIicBzMgLRWrFwlOxmTfb7svYTBIDAtCL9kBIb4CLkg9sJnw6yfMkErj8yV/r2+ZfZfUAuEIQN8OJwU"
    "47hSoTDsnGuXyyR7w/BovREGS5fsMhNrfbAJ5ItSdJvSWixeSq80k6UHo+OmxPjR7PGhiopYS2XkQvji780H2EwyCd2ZRMBVkLTW"
    "dIcoutLhySCEgsQqkXSvJPiSRUwlGPcjRtCgzpccuX6iVTIpsw5z5ikvlRI6yIFdwm715IqF93JzwniUo/OzyRUBow1yZdP45Jtw"
    "+fP0OzIQkX9Y83RyqNZsCxKalBSnynZleLLZoCXAr+ZddUfSxJAIClrecoYxPA3g+Lj6LmIxLioc6SxoNJpRTTenw//Too+ROWHm"
    "DTbHJoJkPPUnxoMwE1BKF9KlNW/p9thYFCh71mZqBL29QaOqepQyYtL3JcFY+DrZ7uLmDJhi2UgNsDOpBRXgnoAEyJZawFE8GKWs"
    "zp/1RznJjrqr6n7mRf5oHR3eUg9uyHrm1QK41qbQYj7bjIH5H4zhy1AYWNnVKgFuP37Dd6McJpZN1xIlC6270L6E2sCdQg4GKHeK"
    "oWChc+43AEhUD4+N0UrwUMtGhHs5TKpw45qrpUbyXZBJQI4gSAxGmCg5XmPpSnMs8/BhPoQaE06cnh2owLCipqF2PwQK/TJs7kzQ"
    "rI0v3Z4cwyfgqodvtSAVjkdLDyZxSQ6TVwVOBw4BtF+H3YWVGUMzGDTwgomFE94Bv2KF7MHEHeieD2U0GJCGSRdY9WaCsMZBFgMK"
    "AqlwuGMiA95wFjTxqOD6Y1dO1Dcc6WFrlAhUOKWOsZW9HTikhD7TcErelJ8aPw0oNSME4VIpSl72Ezj2M1NBiFVJ96NAtsXVaZd3"
    "AqYj88aWHiTeH1Eq5Ht0zTAcogAxAEaM3ZOdaBUZccBC/bI8TvPYu3QbRLPROh68kl2nmc40heziA2Za9xsVDz5goj89C2zWWlM9"
    "6hKZ7AEGwhaiW5Y/noWH8R2oWoaVi2S1Q83myZBhFWV0a3bATRnXCC2s+cKoQPQD2SiAc4NnZLQ+hRiSMQLwauOgGIcmqA+HcpQ8"
    "c3BwVMBAyLchOLmVQEGWCEMPJPHoeBTw+lFFRe4EYWn0cISBWhBuwH9TIfGisJRqqGWVXclQYH1uTeIlY187m9aBHs1RF/081hyY"
    "sqS1AGeJEAnlJliJfaqNdhXbNAlUIURp1lVvu3UsW123XvDUilqBYyDW7JN6TJhg0ZGfSVG2GvBmiTbrnFVAgqEdMmw1YGZGUiyP"
    "fhbxm0JqBhw5EgEV68/Asz7HArfHYGD96i7jFbEjR17HY7zaNVGnnjy4B+B4dMwinY5GOeQILomHf9bRQsWdDH5W6YQVEf5jkM1k"
    "HjeOKIeJrPQZeeo+eHBtwOVB6Ov2oZ4AeDA8ZDofJke1PcDMWj/RT/IGLl1Bi0S+fu2LI1Wsma6ijNw6gAa8VPgoOrAeNqa/4K3+"
    "tumiGmhiKRiU8pkkm7BIY2Xg8AU5elELmFHI8HoscdU0tWwz9KKW7QnoV5PctGXxul+b1ALftemLFBhm2N182tXhQC413OEmyAaz"
    "gHxpzInfmFBoJrYIyw1fS8BRfDBpaD2eHlkRQ5DgzyBza1b4Wnk+qMgNJyvscly4X4OU/iDwdtcTS0OATdO8xhsYNIvb8JtjHmqX"
    "6PbwiSuiW1BfHdiGuvHrqL30DZ3kcaWSU4gvKr1jahBj0DoexFrBETZaTasXPsJR4RkuaEJ1b+4LkA3xPD6FFKhmKESiHsQQ7oKa"
    "hU2hGUzW31IrZfWlK43MqQKCd1BTHAjvkUnV0rn8VWBbaQ8cOlrOdeykvGDVDvKwdr8wwQngqIOsDOK34V7xIP4+Rsm1EFn+weFI"
    "lDa9YL83A0Azc0DkmaZi8eDAZiyHOVVlEZmCWPwFMtFejBdyY+l2ihy1LuOWSh6wW0JnacIzqM6oW6NTsXr/gSvB65ErobfsDcKK"
    "MOrT+cWe91B9urVJQNvMWwrznBB2LEiAlUrphQlZCCJPYzTe1ORh5Al0lAzpIhhGRJp4BaAD7GFyqxJQSiCK2+toJVzy/sdQUmaq"
    "4kLvcZgWb0yvvwLTaZyRg/J2+UklKICCJeZ0zCTS43oTpA1SbFhgNbDX8sOnJtSH0GlHGzC8oC7ExG3nJQLQrRSCkfFQbu5oQjSp"
    "LnG9SkAmcnD4KQ/mp6OkyxiDrlDFXbXK0ACKNCRFZWEi9+krUyEjsG8aYS5B1wP0G62nQcPpOJ8JmbXafjQTiKpdbySqY0i4XHq7"
    "HiEaIprSNnVCqUERZiNSGwaU+WnhyBkf/Alv6Ypuk+++stMo4JpO18111IHNgxn0LoCgbVNhIp/X+zXARK0D0DJ8soH3+HBXxsQc"
    "uvAWitrwBejK8BoVbehCfEOcUWnThxX+DHh4UPNQ1iAsyIIxELQeggXbfQR2+m2rwn66bKeQ1OVrSDAaCxiIViVBsRy1nM8X1yJD"
    "qkOddWlg3lAzm4GbJF8Jg+AV1Gkg19y10qQKZ2Uq4E0k6ElaLQQhUYxJWbnSkDBaIF76yYwpqCWsXoPZmY9T9ZA6eDkIly6Zz5zj"
    "e3+cmU9xItFgX6QfpmAa9oIC7TwfNCp2d0HAqLn0ILKH1ySb04Y9islmMkm3wksh8FeZ1eskZ4XeH1PERtVGwtH6tsFUrKYnmo0s"
    "JC1aPRmDUxjicjIqu7G0lVTqlFlCo2Z01IHcY04aXu/2EWMQUcPtNchtVKqpjd0O+EsKu239q4PenLyYoqCaoDoR4CXjaB7Cjqnj"
    "QInjZTxG+trIfrflEgk+ilEIlh5UElo6UqGVo+ZEJUiMGMqhb3Uxe4bwPezNYqINXSSWZmheBmJC5tdSUwa3faDiQZ7D8aLjPnQ+"
    "00x9NMC02mfUSkgEUEoyXcxOo7vgbJEJkulbe3vnqw54Mab7DljbOfunOU+rzbmqbM4ek8LWKFM10ORoJgASeCC3anG0T47uYOF5"
    "1XlJUnspQTiqktnL8ywo4S7OTsEyBQaKtposY/QG8+K5YEBpdom95ytNRCmkbFNK3HVh1HXIcFruHEAlJ/dgOM9U8baHyXYEGfgq"
    "CYfCPhBIap65dGdkLnrAeQMgJS/qqDIXarCGthkvybvCgXJXwBcbFNaTyoB6omISLnQUe3HDZ/h5BRjklHVpgAgRicOy9+jaCO37"
    "NWtNqF29IESdqQEzBPRMGxftC9cp5FIwjHQQNbXebFAUdqzydI8SAdJJpL2nS4dYbOT9X/ZhgIhfqF6v89mgCmzirR3UDpvNUhCS"
    "LeElUjaGQcWUyJDtEVsNRwXFuGxw99SdVqqGLOQ3HgTjaKYJk60ZeGUyPNjAiC0uCqhlNdDEMO2QKnqT06qfgdRjsU8EjC8ufCq0"
    "aGneWXgjDBG36DcVpaOS0YRmQjesWnhSvNSsJa/ygiomwUPr3wlVTn7xgj1UUPIm4DYiDFJZ63BoJE1VgnDC049zjmKv7DS4OzoM"
    "BVVHz0FSJnUx49cbjB5eHylz60u3mVNNvf6+vnJfXx9C6yaZSxLSBl9qJJBTU6SXaATWjjGwEhFw3qxFr1pb7S4R15A1GILLPCbM"
    "7Kym15lWveTF9SgwCm6QYxsgGmyGOdGBofkiiZfy3HSKlgjbsrtWk4SmSnS6eLlkjcoWUounL/wTzhThMTprODCVALl+YKU0CCbF"
    "MBmWAcYukNXhd6wGaiMm2NfArIejJLE0jZtVDlhUBZL8H9ZJ7of6Y0ghInsi/0EvtC90zgDKVP6/wYgwSPfcAWPWdhe1QYvbT2u3"
    "tk/RfdxMWNgJv8ELhqPAZYoTh0q4i2kADmgNYFco/McF4yQEztoLLGD/JPPASZhldI3ghq+lm1IFJbdgFU4SJ9yAhTZo6gKqtCg7"
    "zE1ojfD1UFmtw+VVx5sxKmwpoigrQ0GzuB+KsKKQRx8XOgaI01HQ7OgaQ/7bwH4ztf1NLChymtdwUyDZNoIciDq8cEmOw74O4HOg"
    "1avcReHERMYScsk7gI7YCRBmpSZW7yb5W8FCiyjWX20NIj1EG6WjVpUj4teI7tFQUtG5SmNjZgMNWcItT/lZUCsEswDkK2utgXHV"
    "YTV3uIMlpRbxV4jc/d4UIplmdcqOxl9UZ0DQTe3iA0zLUwvwbU2ef2Om97kRCXf81DEhXrujiv7bhkXoBpdRx9AkOoPdDenAf35f"
    "JSR6sfX2KxyEDxtmIwgrFFRrEWsTpHDU0bfkvw9pRQzH9jaEJqenKaQ0HJ8iB4lrrWmsgSXbNGErEBCjb8LW2APyX2eRcAhvpgBz"
    "PlZJUhGARhzVwqxZRb97OXWdQLCyaUiZi3bQM4h9jGZmWMW79CDFg6JOogGpENOyDe7iolLtx6QW2uhK1L7jHr6swPbA/SMg5tIw"
    "wGEUZjzfwWjMB36tozmBUM7JAVpfoE6+a/+2XqeYBbFX08ijEciuE/YqdmPUNVl+nW+AMLNrVfLWWnrlOUMO58SFEaOUwE9uCsUj"
    "9Zkf2izkliBwZYotwOL1vjFUMQKGNaqdcFkc722S+nuvYihxzbqtsaomHkA74STuIL55Ckj52r61z67p71/T/6xFQJN4gu4tC7fJ"
    "RH5bmDoXl04MVnALNSM8pFXRaESi/ujcJCvSWIyiCemCmMHu3wYsB7Ywq/j1OWPFkjkSKL4DI3WfMAYt8eQYPb4e7N/M7LUl+ugn"
    "DGhAW++gVANUD4QJ2hyVyd3IPxIovYd4jV736cpITls9/cDimnbgPYyHhF5NjK2FbymzFQMlOm1nGMQ5mZWOxFqChmQPxSJjW73f"
    "IUmtBDWQdlGKbDTsJpuo/Bj/59e37G37R9fX2wU33Zhfx/XqGBFzqnZzeCFhRaK2sJZ+2FC6ca1TkZFONenqsdgGNviDrisopZVN"
    "Cxx/WivTCK6z1FKkcUv2EPbzmSJNoJYE1Vsi63Mjb733cizyqVS0QgWT7SIwX0EUoqICDzMbZsVs0qhq+OLIZj3D8SWLbKDqCXhw"
    "saHBafqTk/QQDLXUs96sX4vnrKJBFWfNfsYzRjqNsnJAzVnvNDgJjhhONlO7pGG0ZVopqd/6djgvLDYOw6zX8AunbxvKqsysZEZp"
    "D8Z++VGZQKLcM7VfAXI7Wm/EKCFBd7yBFgooy90d9GfqpbYFr176VBKZswFCNuWbQj8TFAASo8KNJnF+9+zgz8VFgmV5RFFakudt"
    "rZeUOUa0VhV/Oh2sxdIbqub6Ua9VACB9KqNdpfwy+D/KWb4CIvvyWdQe2zCRTmI9kRgIS9e7xukYIxhY0tXzDeIBnUvB6mSfjvpu"
    "DlbB0ia+jmusS5HxBHkPeAu4fOVVpfMQ0spLjPMOLQ6e4T+SARy9ucv52iiNlDw0bKDYVDOkKR3wZkEwBlFkzsWbfSqFwR4ehdAi"
    "JKeiCFYHy+T+0rnBdjKmWSVytCzGxy2XXEK74DIJkdjWAje9mU4I5jcl6bkusXIjbQuIQ8l1LanRYF2FvaAHKW3rwFKw+wzFENpW"
    "WlPaoLvFdEcVi/yqalG3ajS3vaTGIut4/krW+hyRl42SxXw5D6ACKDIQbhFa3SSu0QxQFEZbU72Lhb9TKG3DqQGEmfCipSvygEwG"
    "XlGO5FHNtIluGFgO3K6nTehRbVGjeJMh3NFb4HKPlm5nZJdbC+DabzTwKz9BIKxRL3Z0ipcCM72KyHIkz8G9w9Y3YvQxrtcLB6yv"
    "wB7DRohHKP4MLEx2QYbrKqCymFIoAEDGRl0iSLp2yBYQPoy8iG9Vs004z3MULSqXZR1BhmitOooAe3aakeJVGXQZbTUY85uNbIgF"
    "TeMkUFA+ZADy+d6hVClrBEJEVQUBDI8/YTGT+KIGN1Pk3HV+yk7BNGsghWIZK0HUOV5WRZmM6UrV6kFYIVc1h8hGkfJIWYK7GItR"
    "b24lmG10mxskbPi15+IDFLyQqe8uUkDRzte5rBtS6LTNagFtOdoFktnIvhfB0auApIRU+vpUY0hhlSjOdolUwTWU2ROwp9VCSGXb"
    "Ggpv2WHbxDwttsLciy1NujtKK8PdzjSpcueuOyY4rBehx0HBAZ0GtqiBZhbLVbg7IuJlG5GukRUXs9tIz7lMUkLaaUvqAbGoozYo"
    "oyfTqJnNIMuJNwVJK/uMAW/VcmeDPZjSWmRSxgLFZJEHPXUyMn0lXZxY1ZStOUD/Tb+hFOpNQVWgX+lkGDTq/hj0OxihH0U2IBJV"
    "5JjrMNajEEwMbx2WE2b4knrwpHLt1kdK86pmDBN5aWCvAeKYyw5G5PlLqQbijDlyvO6qQTpWJL+IetXYEZr3Da39igh5y+6RIqxx"
    "2tNKKgUlLjUqHO/LfkKeBShiVtVjM82uwOWDzSLFXcZtjyjNT7bH9MhuRolzRedYeSDgHtWXbnO0cGxizSuE0cb+2Up5rA7y1o7G"
    "TZZvA/7zutBqcZsIbVUJ5LPpSYtKwV92wTbH4BROrNezZ3Bozd642qTI7QQIO4esE16ebOmrCoCiU+AfOVByQVCRFQVkH//MdHOT"
    "4e8DZPcH9+1eg46GSw+gzUa+5j6Opq23iA/vvgQkJPJj9ZX46LbL1eQ4DU5SLGbkvzwoS9kafTTjjL2qYopUBc58o+P2lnM54Snm"
    "pcKMiRgMQ10MaEBjYmbWOpqyViXPXh5+RpAFEas8Cw15jsrHzvutNxSgq9o4Bl+1Js7OVN6L+LbotM7KCj/VXZAU7q6z1tt5PcT6"
    "o+G4brzXhKqwHAOcBpWWYsLDCDzNTJyOyH3Ki4DOHY71ppXtZcJ1J65UXCKUZbvej87pd+yfvHvoyZQ962UUXbtpiHDAp9CnybQs"
    "ni4wdoLY2CfeZiXiK7YJUfb6N60t9z+7sdxf3tA3sAHfT4uWwxnBz1oQayh6SeCOqw8FnHXVYAA+FDnrHbPkFuV3ERUCjaBusLgZ"
    "JYE/WkeXd252NpycY58DlvYTUtBU/GTA251mDt6RK4I4R2VbXaJ9gDUVv3b0ZRZIzWeP2b17D6553pfc4FYZ8pj4PcdgYpF6rH0J"
    "FugFn55qUpYuixqL4uelq9+L5ahhm+UAKzI/+JRj64xbrudd+jEeOuZjGaKfAnUo66eM7l/wJyen4f8JH+bBXdu5KOIqpMhRbiW2"
    "ayEjSZm82kQDqYanHkFT67odj+klUjEw/BZN6+jc5PW6TMEaFo9UdIk8BfI2RKWAuulYacUGFiRM0LAN57QbWq9xQqiB3DzQMh7Q"
    "uqRWVb6EndTS9IpdiMZAHk9lnrK69pTGOTYv4p3aHwnX687MJdUlOBHodEV7FRonk4Gcmwa96qFFyD+3E47y2NkR8btzPe5cjrUT"
    "epAj99CI8GC+EKeZ9qupEoUmh6vOmorL7toZozOz35qxoBMTdbamNAdhpJfEKMxFz6OYZb397nqV0fNEgNg/bJyrq/VEZgbud+0D"
    "VkPWnGzXhJW2J08rG6LeVXnjkiWDMidJ6TmWxYqtGpRfvPSOcVifVM0o9XpmlcH2XK9xZ0GbJufN+WWbzw1lIUObnVP2jnPKCQxH"
    "pIcMMh2HKojFskUXOM4JJWHxPGfAk7qGIn+Bss6B60oWM7JvH7W+xASwISNcbWznGOKTIcpJiY/6FT6sWTyBvrOw8PKiMODt1GeM"
    "DhLeo7jciYvvtaCKfWV4W3U/RmjCQ2NBgd3YLyBGoGUPbbXlUVRS83C6MgLQZlkStU8ljyZjXH55qOLOXPUtMVAC1zv3cP6UK4mO"
    "FqJE/ygWpS62AExbZprp0pVsBuVmdKqOEHkQUTLnuderYlb1RhFhc2manFb1BsIdNRO1JV4Pbx2dj/34VIuzDnqFw6mGxTSb5mri"
    "xQBhNvc74uhmGfkUbFQ1KBw5z4p9zXNO+Dwyy7Ve8SCVZpaxLaKSS1VJgx8e8btmu8WLCyVrbx1G2ihwSLa5JU6NlhI+vtKs4RMx"
    "hjTV7SkrdZuf0kpFdfEBkHpCH/AO4Fqau4H5TytUThgVcFf/BGtFN2I44WkZS0tpIqeKSpy0GZu9KZJW1Rn3JJAG0TJ1far6TkRC"
    "bCKMCBapN42WTmIdjRyI/dbusVCX4pvt3rcmJ93xemotjrVwLgRJXC9OItphID3qyCYuGCgsgz4zM1YKG1ewhfh7WKJlP29Mawa6"
    "mQdWAvbnt+vTcNgI0dDEDmFRa++cR11bz6blFmdxaAetkZNmiW3a8fgC5z0DJ3nc9YG2NwzZptDFisBCiG4Ch93lf0kEC6pF/iLE"
    "stnepubVvKNehy/Jz6ocxeqt0/YhLYb8GaqyUken4lmSlekYo0ODGJlPAEc4xS8cHOkDA+TgywGS7vyFnSX+NJmLGDWMQR9VTk66"
    "Yt2jvllJfpVZDDWsyu03RKVCpgId3LgjMAMGkJ9TYLw4B/vFx8WK7eGsoQN7gE70S93AjS57Am4I8o5nq3iMCZIrHK2Lg5TYJBhv"
    "Ri4W97/BirG5NAXKsNVuGDeFQbe6sMy02XfWmMVpiRhhhRnQD7YEaXlIE4NgrFJM9A/Cdum8rDqvNFMd6cV0J/xNLUj8auCA5oep"
    "blAY2X4t5clxTzXptuxMmbMoWSoJ4i3pIRXHiXdWDak5WY0649zny5u1vuFyq4RX0iQAkbW9132Q/73D2q5w5EASZzN48IA028bM"
    "eayhSoI5uo6fRyFRUjPZ8AtwEwFEYDFTNYjyUjcEcfCOz66DoXyDVYDxJL6Ob0qqIbG0crbaEgWCVBeifQ6J9GrnbuWFrPxYpNyZ"
    "oYq1hIZwM031KFK2ocmx/qne+An711u1MliVSNJH2fKG9YKhePc4Iy/gkuJFNSrQc2w9EWZWHtL1czni4VicYAhYtEu3YSRn0m4K"
    "7HPYLomYC1cWR4LMeShyC5NnMTmSSASRSbbB6mjkN1uf8+qYck1itulSKuz8nDMD0Ob0xovQBTXmVZbhQB7CviMZyrVbsA0ivNmq"
    "2wubRNCjTK6owBrCWDiZHbFMIgbyTSirCLKTErsIzw5npyHTDAUABRh69gIh9wilztw5+v8ugwGWLZTbLhoD7D84NLR76HmFOFkn"
    "xL79O/cN7t/JdpSMpuxEnIMb3rN7O7f0dLh9gweHd9I7RDPVj5kOxK7dQ7uHX9ALXAAwuHvPzh0Sqo4NsXzbXkudhY67SUNgQMAd"
    "YjaFgptBemWhwnCY873sp+PiKmiJ8CT3RTlAK+CzcNsVRWMssJgC3wyJrDKmNAsMQUnsM2PYg92pcH0MgeY/Q4L9DJRoE0MHQrBf"
    "GnLsDGWd4m2Ao/ogIQfvDlcBWOeoE8gy8NEbpuaSNhvZQfZ1LQwcqEHzWC4erxaCM1wFxiPyiOhIZmtzuhTYbp4MieY19NGkAzrh"
    "M4FgKGW1Y2UFUHY7yt4v26b6GZJn/ErTbgI7ynXjDJEyHjmrhF+tyILSIN9PsgRib2CMTWQVmWXdB9uMbCugjLt0o/VYooQqEUJu"
    "brtxBuIcm9bbcEdnMPXdVTSRGgut6ee7JI9BbqzTwM02lXBr6DR4ubMkDYhdHNU1rofAzIDM6/X08dsLXsgUKZnbhbO5jddbCWoS"
    "dYaV0nJ65O7E6HVLVzKygHaj9egXc9vgmb1V1HuWL2IL0RsWMlMKfKkHcpCRonMgrCmq/H82FijS+PsymZbk8RcgoiwHExViOkAO"
    "VquYR4TODIOK13Nhq53QSlFXWEcFn7BChCL6JkFUzTHvyANhSCVgS+iZUCkT0BsmTkgj6QRgqstbCmOlq4E1CMRpKbPAYeOnrHGP"
    "EU3bbDVFccm4feb8RuuogiTn5Qg98kjDYN3AadkhHAccy0aFoolNspBgsUhmVWNZR+y7cKHQLNgYyhpdhTDdHAtOo5BswIDTqCS6"
    "M1Mn+0/19pu/g1DDCs2mWhGbTsLMSR4h20ZR044v3Y4ie5H9qsKI3Z0Dyl0nAAt0UiEQ0koXcyS7DGoPMA14GFeVTuwVYDlgKSZy"
    "xeV1feYWXNdH5sh5kE0WyKZikGkWkMRX7nd+PclD+GSy8HyQ+hO4Jh3DwUScgWUOIY8GJTvQJ+pFM0LUWXSrmdOKZ9hv3dBY2GhQ"
    "CIcdTsRN/fzHqvCK36i60eREt20jhXZd4JatuHq62c6oegzb6afuWFzL0ig7ZbmvA8ODMADG+rZYtXEM/R1Z4+kWmYOKgeBkahDo"
    "D0PMW+EwRrNB2h3hK/CA1nijIjeOBC9wEk/8Lq7YpivNMdhMCgwQhEoJHNgqKdnjetAYoyS7INrXOLMzr1ZEdu9VzW2RK7qygc/D"
    "WAxXARxmpkiHTZbObVqrbrnjykxUvNEdzQSDjwHDXGUsUGQzt1VDHW4rudIitxV9DJ5qWO9AddrHp45PZ3cbebMMMTaUMlWx/WIU"
    "pNDxcfvFy3bX4Wayeqh8Zpgiu+NFa355I/odjWmb3xgPJHwkPxBPOPEGxP/XBONkTQA7EBhyzYMrI5moWTEh2aRmsJIqNwOjXtdR"
    "93hgE1awN5sLc2O+5WBl2SUGD9sZP72GQQgrxFAnjIUWRc0ZvexuHRlbEUj7uk0790c1PYxPZKFFmEEyYJu0CTIDjVynETmPMccu"
    "C5gD8YYCu4UoHo51xCXFdtUcWIs2Gt+q33j9BViiVBL/q0uhzON/4RrlUJnIxrZpi3AwbnUsOQGKd7Q59m4A0Nx7k2iywglFPs2U"
    "6HXSwZ8Uk4ywTYQNIj0OZ0sPshltTgP3jUIBjwgwI2/FPIi7d5tyVHSIqfMcY8J+WwSepGYKeoj/NnKFaXNykv0A1OhyAJPNRFTm"
    "MF4Z+37M+lzDSC9ZM5nIVRgF1K0kOhgX/cXBacytpV2L0brCBknXYFRXorElfPJCu/5ICVBlfNGX52l2yKtRiu5BWnSt7UUjwcqY"
    "z06V1siEDO3MM52yrOV1E2Nruqxtmr+xck0PxxPKliGnedO2DSCGUQB+DpKSVtC2yekt36SwOztT9XZNj2HChGg+hzMIWnVjjihl"
    "ezQF5ozzwth3APalFJdcakXfVzTGtM95RqZVD8aX3mYphoRGdvT2gq7djY5FXb1DFcPTUB7T5C3tFEyKFta9e7HEimno3JkdFAKB"
    "TdpQ7bNtFcqC5eaGRcKM/d5lwooHNWZigVsKmzFHI0cWOeS72MFtTMBf2tHcOFxyYfC6HGkM4rR9+CWPP6jITZjg2AnnHCRr8sk0"
    "EGYM+CRxrN8lPyXQNusS9rEDuxgMquTPFBkFqvybOGZpfYoA1JphVY4hhYvGQ48uFrhmmQ0jApuifqSEyrkWOLx4Pn45aWisYN1N"
    "lbiBhX9hkuSpwKGiMJTR8Uxli0YP1+efNmg3XwjUCDU8ShjbgiqmvIKVooRZOkaMLBCJw3C7dGtax3pT4zFx84wVn8ktoAeBea3Z"
    "RyCIxuOkgua2fiMba+CjMXsgDdnV8ikyaiw16GvPQTPKGD41nMUsZvoJxXbDm6ujWg9J/b2mllD+gyQiCw1QAdW0ybcVENQxruI4"
    "bwmZ8kmMt5IWo7FwTMUZVMtVGMjAKhgCJkZQVm5+O3yX7WRIzKRiJJWFlloygnZzPCCysne8PFlGuTHtlLd5Y/WtkUONlVTranVC"
    "KzxWrqntBdYQHGqPVRFERgqrdBpCYD266LtUHOp46PuprvYytfq1HQ1HIJjWmrxAsum5YqWjsNGCb2SFs+NiXSRIirgw4LTBOlQV"
    "9M0tAqFKng2Aps0YOiTFlZjMtbZhrhGVIb7hT/Pjl5tswxTlYjZLBpdcJAl7mLyqzJ1MoimNItVTMUVnxserSWUgZPqR47RbvXwC"
    "2kz42MeuAEm6DvqDlHPGaoTAUcoSp2dhtZg1UZlYFJZhbuoGebUP8sjd7ypYmjExZRqLzWK+FjVtJMHGiMkE07CaGlZJgcxq5fti"
    "Zyosl7YGLNW3Cywsnx0ISQIoadnTRPcjA2/JQFNglaQHmkjWWRPvMNBhK81oCUoW5gBFKaw6REUds6qfjJVoODQaMd7rEs9S+c1x"
    "yoMS38NkO6ms1jUkcVNIpUK249AGd2bm7G4MA8DZ1jHkHrloQZPb6+GkZ4IbaHu7wzEIA/WYxrCHDViFVGpOiogvkUpm5KyQnmgo"
    "m0jOGrKr1nVqYSOzY1pRzZd8KMM7cMDbN8ggVLpvcM32XXo3/OlUVtj6wo8rVtdhxHEUxHR8QrKMY6iQYAJpfqIpmqmlL1y0rttL"
    "KdPw6d22q5OtHupwQbSkeDVU4EHJnE8V5dx1Xti9b9hAKvJBgQGVa2E1x7ECqF+t8sj0WrquiHqAdBD2qgCeuRtOtBnkaaCjoOZI"
    "louRPSiMKN6rV01RvQ0aXmzpwZhZSSp+0Umj5rioKvA8rwFIXaN4mMN0VOto64EGZ8nhwOv5114HStEi4EkysSs2AoVE9iWzFMtD"
    "H+emtEeJWRF01SejfnXMdCgYfh7bL0MQ0EoDo+KopagEY3DrkZM33R0qCRtH/TFsGoU4YAnBYlYnmimTz316Sdj2JyXjFTwTw5L+"
    "yaR7s1YSTjC0i2jPfq90r6XpmnweDXJRE80Q+qiJzfuafeFkgCGYlbW5w3F0puzj72xlQPubt6NRyJSn/krUUOmEge/BJFx4wTc4"
    "ConIz9UgX0cefJWfIkm3e4fXEDvPpEoFwiWevNrQ5grjOSMd9fyn4ND0sMgYiN4GsoqfGA8IXaUuDH++ihNBgm7t8HCgX3L1w5Fd"
    "xYThIMRFC+41aMFta6bsF7zKzFSZbKaMA4DeLLSpkEcqhRpr2DG4mot2bRs5q4xNXt3mN1RbyvMeURsoAX4SZ2PMRhRUJagjemwr"
    "18WilEl4p5SYHrveA0nZGwrYOZtECD+pTixdWboU1jidkcow91tvUB8HRF2VzLVzQGwFgeqXikT6gA5Sir/gZnQq53D5hbBapaDF"
    "hRvFgR7TWsA7nJUpQ6GN5irEl4pa0rlBRYku9Xc6SkSD9XNS7hBwPvTR6Y43IMNihtGAAebAUfzuMWgFIMXU6kDl5npz7cpeoxzL"
    "ag3cEoyEm5PEJxMy8LMF8rLndKBimzMzgqxiYrRv+QQ/OvsdtUM8MQcxxzYpioEE8SOdGLnHTE9U4sZmoZkUAMIx/GtOAO0ORuuW"
    "IE1LLIdD0c8ZZAYRO/VhEg2XiC14TZSsJ3bZbxsLyAhb8k/pbSNUwXCDGOwNTReialiT09HxGuym9tNDdZDRxYpiTHTHjyycmQR5"
    "EDjLgUHxWGcreR5f4g/e7OE5+7JijaPy7+O/UitCP3JVAacwtVqgIUIXyJiQa8n+oBH4adCpVpDcaFk8DktFmlE0IfezuhpFM0rF"
    "q+Kgk+DNDquq1i2XXtf7lRtKTESFUSAxyqzAlhUIZ5MxNiWwYVk1tSOf/ZFya/Gl3Ow6NCtFJefjqyl9QsJp2+iZayrGfstuv92G"
    "J1DjgMs7q8r1hmNkurGXUSzi1DGHUskFIzkB0B2kUbGfc910RFQzjA5xRHuRAnHUsec8/mg/BFWnOFsSFRUnZKIijhF7SJxrMByJ"
    "eNZQaTWEIQoPgg+zEzh63aztpPB7WOoZHRiKitnCEzUJFXqKVN+t4PP6LciKQk8wRD0PhSbho3YhklFPSBA1HS7ctJ4dipKCuKdU"
    "CviU+IfGQAwg2faVZupnMxhlVJ59rIdpgfdHs0OWnjrym4HSEwFPvLa8bmOfV0NiDffU2tK6jd54rVfV7pKyKaebUNCw44fGJE8F"
    "yYX5ZBWYIM4KEs/+nwpEP9cKdscNvccqiF5e2OxBSc28cOgkqbqPXrOoU4eiOOOAeLsdPoOV0rYAoAL8yMskPVSqhjDc1aGnYCqV"
    "PwVdqfzpOEsgesfsGLmi1LMD9Zoa3bCVCp0okIJSxDfl8Zagu/voOGDdj49Kvs33QId3nli6kBCn7IxUDew7PcChMn9fmMeRY/6E"
    "FJhUtaiszgz9BjZXzNTKdvMY86/beCgeYH484mGoTXCanD/UcCuzch3O2bW0OYjVy1jeiFpDo52JTNlMAK9BOhuRcTRGhr9R42zp"
    "ES2HIEMuJaWKcFXO96IC3xR0oxzeEw+kSJLsiaLjWaRaa8jvzHn0LupF7bi+/F9+ymY3Jw/EO8QwMQxUIlJ+P6XA8CS16rf0ZLT8"
    "J/zItPflGC0DkU4U5vKk6E9bpVozoTxO+/dIylAJE4UqKtxzOxHrMErq5GGKFSVoK2MefKNUlWV/dFRieNhLQ3koNYzUtNYrcxvB"
    "YGEvkmZ4sKJfxkzR7kgxGns5zgavEOCCkhEmvI7ePd80goG2Kbzfmr0+nVz+XByiiMt08vr99CM3HrrOcyPFp6dkOxMy8zrBEsw2"
    "ZXrbVC6cyK2bmEvsZ8ztwJKHY9Ok/9D2utawJAEwRk+OvO3kgKpEZQZ5miOw7TZZ7A9sZgkNWBOlPEQUMacAzt67YkAet7hJYnZ3"
    "Hrp2nDL5eu1FEPOdugttnx97U3SiazPiDkJj4IOqGrVKp5pfQWprb27VDivCp6HhMt1uVWDz9cOGPs5O1afnNPTPIoeCUK+jlSex"
    "RBybUv0Ju0XJK1IPIz+x3BVG8dhYOBPyuySfAwBBF3+NaiVPkzDW/s8gv8BSYUSOs0XOx7j8OhhRxJkTMJG89R6e+Gx7RJ9NbAv6"
    "bGLnKYACnxWQpEl4zkiYJiiS2nZGQFbTuvo2ma3Zth9PKwylWWsuXUu9nm2Jn4YNUy0l+49Jf+n7uKE+spopaKIWQn2bqa/ZjjYX"
    "Kzfmlx9+sHz3evujY6pMnL7tEeJto64YnlcurzXqO5VwqtYwVBbddT8reTwZuCSYOCupnLCabU66ivSkBNJbgjswFc6UFeXN54Ox"
    "0uABVDpOzsCD9tM7aq7TSXp1jgSsIx0AfsynDsBvWu9oS4hjyg2Ha+lLXAQqmuNYgjwkuRRoY2FcUHMSUrwXyE+Bkswo12xsk5Ct"
    "3Ee3aKMxTqICPZ7L+jhg/V1sKQzEWqKvqNxgopwrXqfyVO/T8XpM4XpVaHS5pnCDZLBNxb9SCvv+j1plELFAoy+FA14VXQQ5ALiE"
    "vQqBlgRqtfu7spwoif/Elrr8qMVCwUDIZEpNdKsTYMemsjjDiZ+469Ut7/UENmXsVXNY674OcKwYfgKs8MuCthEcI3WYCt2AIWc4"
    "JLEy2aFdQA0mOiqQbg0TQqFaigMzwF2FgWo8dhhOWM0wgU/fmXif1+NGxrYO7MW3mXVzEdpDpbZnjug4quKardhYzkGlprbOfThW"
    "2ceLIpf+VMRTmE3q1dD/AtEgJetp/SBivT3zOyd2hJTQ4hLxlYKRh/xk1BDX+1ZgXBFkTbAxJ7qVfnDpFtXV6zHe3RRxLZoebVbC"
    "0d6yoILll2MZoyDCmFAu7mOKHmZF6+5S7z/n79vqcfxTK8j3xD6mf6JnHEvfg4GLOVwfDZp2LhVFuvKxt14MVLcbHEP0VPy0Bgp9"
    "13lfcuEEtLuWOfm67UpeAU4ZLxukhRWFNK7i4WIHBt3MqNFZDXgdZgpsPYDdcCxKVYvJHy3JmNkK0aE26fYpSk9f9pY+InMwk5Az"
    "8uwry/ArEs6BkeknjMvKI3OlV+pbZv8FtUzo8O9Ho8SctE5/1L69QCFYuUCSJ7SO/PXJuevmuwmI3nr8cOXDq6akFovD0Orjs60L"
    "fzEFxqGlff2L1sWvWyc+W334UEWTJRDyHly5fGP1xhXzMQkysvJ8cuzU6s0PzXfRxy4//rR1/WPzWfK57sSc9tjXxWsrl64+OfvJ"
    "6s2bmBQDvTsDYGRJN4aMwcpX77eOn5KiCTqwqqi1cPTJ+5dMKb/aK7dwdFzWCRqWF0+0rnzjuYXTeDMkDND++GsHIPIPWxwhE1zo"
    "r3XyvhSmynil/dEnKxc+lq/mwbR9/IPWqVvtixpeHn9WFi+t3risPooYjdtx49HKwxvyXQffx3W9OL/65Rvtv37dfvu0FFMiDlMV"
    "u3owrxtIKR2IkQQBYdpv3DQFAS79vgRI6uvYPC393x+cNwCyRRpkZfGD9l8u8k45gFE8GKWs/p/1Ke3WnF6ri1+jBxnu3tEj7R8u"
    "ty8eb31wqnX/7N8fXFi9ead1ZKH9xXz70lVNj//+4GTr6ClGov89/6bpRAJMYYYUvdqthXOrl79u3ToPg3oy/8bqo0eIAjSCshHY"
    "BI9PvwcgrYVbuisJdYGGg3oXrXgzXK19/YrNuwCjvfr4zOrlk7AAdkix/w1N33hr5fzbrTtXW0futK78uLx4tXX6BI9z+e67+jvC"
    "HPnr6htnn7z1EFfH7vGzYyvXHz25/DfoBdbhyZtfPDl2cvnepeUH59sfP1q5cn/18SfLiw9b9z+Ao8SLQ6M32NYxfD1YXOzuvbXf"
    "/aq1cNsNkta6d5sHmpsYdAyLomvzyDQ3snpzEYgTLDNWOXqkdeOeNVAQJZUqZPnu/eXF+eV7C4ARy3evLN+9plv8+4NLVoVtcXXa"
    "ZYVgOaB2++ZprHT6/eXF21DpyaeftxYutBbvL9+ddxs7CRNZvnt2+e6p1pE3Vm/clSrnz6yeO22DtY/P055dg2MGI1qdP4I7dObm"
    "ytmvoVQj9Psn7UVs3fq+/fHN3ARgxrjW1pBhMbjb1s17qzc/bV8+CovOxFqvHE8CJrfy1eKTT67Ya2z1Dy3xCQeMY+Rqf3Bq+eFF"
    "+HP18tXVH7+CHytvfdy69wOMlIkMY9CT86eX770DRKB15Xtob+XCj7BJcM7aH90CqgHz5H2i3EGK4tmnzOQVMmanrSPfe4Aop+7g"
    "8jEezKZ1oBlz+DFXQ6xOsc4sAzy1lgT01AausMD2iq7On2t/emb57qdPPscF6ahl2bj+QzW1FsaqwYBAY9oXfoTlgtM0S8RTp2cC"
    "Cgm1UahsLdwBiNx3mwzx+bAXVgWyM/DUv0Ph7vzAXRtAv7rLuBO0z33W/uuHnU13jhTNPHCYZ062r191FwCL5O1/5dt3Wqf+yu05"
    "lBlIgovYgMaAQ3Ds4PTASTZkoHiRsQ97NYAwGk7cHpS1KKIxbN06ykXLj2+0z97rJOc2vMyjEwhWpH3iRCE68LFCYkj3KBw0czSp"
    "YzzEF68xI8ODgCXhP6ELoJJwuOFm0xVxTrp163R13Ew/NTNrMfhyS1+kgCi8YHDOpcqdH1pvXCRydX4WMCSFe9g+1IWMXRdMjOKD"
    "ScN1GaEtoqtWsxgWaIXJNGK4WsfVRx+0jly19vfirdan84BDK2/eax1bbP/tHbjjcQnvvdM6865ebKBVdHF9ApcfjKt17H77za9x"
    "7Wmk1oS441Ry2uhx5TvsPDN6Xs65sTopqKK76Thq7U+vtu+fUVUoxJ7uYPXxx8z0uO0ykCyZHi6ingUMM5VL24G4swgbhwT87duw"
    "aryUTHWspZEOnOQIrJrgHpjpX15cXH74Ya43cwyIMVv98cvW6Ts/1Z+E9jILS72sfPdl68wCMi33L6xcv/Bk/nj708twCXass6ou"
    "K8LnoH3m4sqPnzMP0V74qH33CNyKdjNIkE79tXX6Jgxz5eI7TIE6sERFae1OIxeERv79wXG8uR9+AKIE30s40I9vqnRPXBf5GqkI"
    "5+7mKvAId35YfXysffES9wpyNDBjqUm0x2PuKBnSRTiECLu3YHTotdaZUytfwVq/sfzwlFz7x4FG3EGO88oxlAcWPvL+x8qDj+Ab"
    "H2C3CWVVLCun1l0B6Yy97ZPHn3x+cfX4Dx3D9RsNzrrLQgauMkNaMNZDOdA76MWtv9fyvJZ9ykPpp/jlRxeAirY+POo28RKVmwaK"
    "wMjMZU+OeTm6svi2vSpwjl2Q9rvvt+6ftntL6Y48dcz9XA3o+5NPTuW+h4m6bxaOtU99zhWf6YCzbDAYvZBgP3y/ffkLez9QkmcR"
    "5+J8+92rq4/fA4zrWG8Bk365ObhMgWlkULuyYrfso2HaASTROZX5jBV0xpE87COYX3UVC5DXG6/Zc591wFj2NhqO0boD1EIo02Qe"
    "ZxhUY45pswA3cN9V8mrecQDkw5WHspFZQXb0TZC6aw3XtWs7XbLp//g3yw/hogOB93S+gkQLMbB3foC7vRiWjHUO5Ws8+fKj9neX"
    "lx8+hnr5GhjxrKMCYA2gTHGFSYk7ZMZDhBKlWwXPtKRcabBm6cnie4xH8r2WkIpl5Y1bzuepekgNr3zy0PnO6ZdX7n/ufI0TidXZ"
    "/uYTp2A6aHDskyeLb+e6DegxbmXxsfO90mjSFf3Bp87nyWYyyWT7x2/dAs7Qu/LDcbeZhEO1tb/40Pk+0WxkISLllfP8nZHVjWGs"
    "T2W+3BJfOmGieI85SHDO9BHiYtHb7LWwmHQ2GoUdsJc0ChOQjb+cMJZiWNoj5v0GDiEP4g7aBhOvuhi51mfsBz7+LpEj+TR4s1Nk"
    "gYNMTznCrHyJJRBxyFJdzg4BfCN6s5jJQBdZRk3IEGd+LTWFcAUHMtylczjg//uOR5LplN02ohOdz9PLd0+t3v6rLmI/QOQ+bh2F"
    "SbZunDTdal9du+bfialduf+YuRpv9k+mH9mIPfYiQEXeDw01OZrtcZeJ/MfNkKJ9ckJzB1MneUjtqfnVoEr2Eci9fHEEGfXZKViQ"
    "wADRrtI8ZCOppRwQkJBdYim4/ODj1pEFTQ3ccnVTXZwHGFQ43HpDtFJHFngFkU+8O89qgdbRU/ARbjMtP5Ha7Pby4kf6LHD7ZFF4"
    "wFHvIqEkDYgLNFiLFXICDCxQAcyLDUSZ1TufLt89AaRTFCmwQrePAIuHEaamU6pPCp0zT46+D2zfk0/OuK3IXLmN9mfHVm/cWr57"
    "v3NYFkNgswKUct1VwUigXuyVtD0Kis4PM28rX11BrSlx7/qS4OzttIvt2wuwmHo9VaFEkV/5CsSKr9VHk2jdHVQzskroCcIt5xR5"
    "LKLwXqKI+t2jjl6VHahenM6dIzjiPHYoYGY/CKB97iqsvAJDRTgLn66sRIK8XlFDMzXBpIJ0VCQEWmpeR2DJa8yQqyWUXUJcPfJO"
    "+8Nbqoh8jBX/RyWour282Lry1fL9d70+4LdYR9A+dxsVuaTH0cNkbsw0tDs67DeIbsHRYAFaNeSxElNQsb+vr9TX1+fRucBerZaY"
    "1dCPCUwv3FEziOKDGULvUm7yDKsOsCi0T+Tq4DiOzdPKnURV65lvhbm++N3q/W///uDCyjf3hSO//C2titt80cStcUOrqyffal34"
    "EXAFlgK1I7ICVkuAfuL0yCjI8pEqDaqhSkAD0tLqo/fcYozer9ejo0QdaVb+3L2/evOqzCaHc7gOVBun/OEnMOvWwiethc8Ac92R"
    "/ge9X/FArc8qpZis3oe3rIOsis1atW+eBhKDIjC1g8pYWJm1fXl2H+ceJ8751HTUlCndfDEA/qMgeAFzN7LApRm516x89x0JHu3r"
    "V5Ggw926Fn/THaJCK1s1rGzkKKa+841NMyw4lYwB1eP5Ab4eKpNgVJhePF7QRERhIeAEFjVPQSGMbHhLCML5twuAMTp5TnnTHZB8"
    "gLtOCyEEv1iFj5y46r39w+POm5AlNFQF3P2mdf/L1vsnWYHobHYU63f+3EC1Vso68fgah08B6gHFaWrMbI5NJOBCtpUusMekfDxu"
    "LWndT3QEP3sSMATkKe6/2zr9ZevKRx7p9zXGIpE8ew/feZR21eu20KKVhmvmsztP5t/kRvXpdGahBiN839OGI88G/30DIh1Y1zEN"
    "6QVqXXkbL/l/rDt3G5689RAfkc5ean+44CIEC7+6qhZ+pVyrgrQCwCkY0iUSp9gQDqNAIMqRr8/e9BqI37eKmqqGSTCq3rtZjwHS"
    "5sI5eyj+66IVuHcbCk1JI45qYdashpxgHGTf1q1HKxfutt+9anUQRGlIKVBaN4/CybFPy8wMkbbWR3daH//IB8sUV1gYfet66/6J"
    "fJn28DCPHor/UruMm/eyAtM3YR4sjMJMqTw+bX31Tpdy9UhDtwtpUJBEdO3cVjzkLm179YwcZW1tMYOqaSlZVy7ffQdIBpB2a7VY"
    "AQBcQr4kijnZRqqVxIzr+BR48Rq/Y7Ba2n48VoSSo0/BjP7UDFkobD0+AvxEJ0gWx3ubpD9lfql4QRW0ODgwU9n+7EHrwenWl2/C"
    "Pbr22TX9/Wv6n7VIYRJPkKTxrvlG9sBwSJ1rRl9UipKb0maER7HKMnfrvYdwEIuuBR3FCIn7VwuaF+3fJmnTZxVLCyLJraP6RpRX"
    "eyAaB/uRP2SCrt/vkTEhbr914y0gFKtffQGnEShmp4UCL77K8mxY/9Uv38izPYwbcrPD1UA8AVwFrTPn/v7gEtpRvPl1TukpnOS9"
    "d0AWQyoGo7l7Ch9/jt1fefcWPlCRmh0az42DmJiCMQgPJOGe6ZFBlp5HAcwSsEVAHkFaai9eht+rNy67bTejBmt5/mtLC439/KWF"
    "GawsfrWyeJ1H1zEKZhClvXu3uTGujc5bQeaHDaV11QPUV/vKJ4sgWeG7BBkg8TSlEkem1SodFFIJqBPC0ugUQEXxfjk4pDf01nut"
    "977m7rUWQECtUKBMg1gtgkLiezaYL842ykqg/ellbSUgvQB3C195Qv7kJD3SkdiArzOo6fFr8ZxVNmjMwTz9eGNsExrlVJ9U+02K"
    "SjKe38qJ2+35N+wSR2Ol9WD6yUcGvPARm5lYOOnlVXoquSIZc6mR8IOWAlGJBiLnSbF142R74QyieecOu/aAqze/bL91xF7llHhC"
    "kCxXgHs8fdPZKj9TuwrHBI7Me19LREK2VxMoO3yrs4Vu6FanSEn9WsaX7651ngXvT6eDtdjoHklvU1BuKx5zMBQfmtq+A4TdfDcS"
    "fR5VLb2h2EiZMvSgtiSVTu2G1fo+HdyZV5GU96etfnwdn5QBWvf+2vr0GN2E5jjlFlaiEQvERjpwVJlnobUBKIUvvouvQOe+YTqF"
    "HTyYh0sQjwjIj82A9IEWSuxTkce5LU1TyO4B+9Pn36T80QmBGJfcsvwhsYok6wiJLZcZk10AyQWE4zh32y2y0qdwTYB4cu7HXN+S"
    "Han1PVmfIWHRr9NaQapLtKGlxrUnl+/lLC47IC2s6wat5gAb3zpyhDXIXIK+Gxw4iW2w+LU9X6z0SjfvrRz5yjY3KKxUYO3rFEhr"
    "TJO0DRjwb6hDWDi2cvyYrpE2K4ZqchlK7kB4V+7f87Z4IHDAhOna/kvr8VvwRbTSAGQ3CFvDajs7JzvF5BvcO2ynAc/4k/fCAesr"
    "MJhBwvw8SGUrD290UE0FMSzmGQxmAQAeNeoSP05fw07q9Th7EZ8lZpvAXcOF89XD5YencrneEQjFn8JCQIOdPznOajDmNxvZkLw/"
    "WkbBBRBDNkiuN7xItIpCwWhJTkElgQh7aJxFDKadz0q2IWU/QmHuF44+OQJQSLnmnlGRjFEGpjnb9arVg7BUdLssaF0vGtnh/sGd"
    "12UJoN4g7fyvPXfvoeCFTH13EQCKdr7OZV1a1XlQxWqyYGUZRMbMYB7vtgVEmmbJ1IaUU++0Jw3nO47ibJfw4WgZePwRHKWuQOoc"
    "33jLmIx8/i2rBXHFlGTl7g3PmzamczUJQmECakVNFkViMzitd7fazSyWu4d5c6xiGcXpZRTDNNSl4wRRFXLz9MpXpwos3NBaduEc"
    "GvU9+mr10b32Z6d1EVKEd44z5wU9IVFfuKOafkc0JoCDd79Evoas6JSK601r1NBd02/IuJcXj8Cskct6+/TqV0dbFx6h2uyze+1T"
    "N2A+PG9taITakIUzqIrnJzHjV4P7wTZBasqssXZ7zvNeGhgXhLWlbD6mvmuDKWOpTBjFSkBbEWShOu23NFeAx2IBr6JhshXfyvXj"
    "rUdHzOBPXG29d0ITOjFxdxsg956nN8CDVU4fLJU4xwhtpBfftXHOPlewqidQK0Wt8FZ0CDncnMlWKy1qO2dpT3fwlCYp03E2PemQ"
    "1pXvF1t/eccu3eaYw8HRQRXm9/OtS5dWHr7X/voySP2svOSE3VXy76ITos0IMZF2SsNlHAbCqr5b3vitm0dXPntDNzQZ/j6gOKr7"
    "dntQ9OT9q/k6pB8W8RiOo54CHMp9CXD/hKlsH+62yhU/vbp67JqVGR7rDU5OwlHmXOoAqPNsp3jAgYWl+4NOC1/U7NzRuvwt8Cn2"
    "PamzSNNADHOorx4UwsUHxfstOiHChMbhlxk4nn5lTsdriTbqav3QfJXWC48Si66qCJgHpA1UisrQhxeRzpllZHUR7GL73FcrxxdM"
    "l2zJp1CpfeKEtMHaVDIubZ2+tXL2b6tvv7d894T2EWidvoa0X82NCYOyJZR1wGWWt0Z3xa1VyC8+LgF7J/DA0czwyzdhva0m8NEM"
    "2tzY5618e7N1+gt88bp5hy7XE/rL8qN3UDHVv2ltuf/ZjeX+8oa+gQ38CObOFjr5mbO1htAxX0xaPxRk9rFqv/P+yuKny/eP8pKi"
    "8WEnXlvJ5qU6G18+/kv73auUzh1ptUahB/Pwf2xSHWiLJh5giRjuwQLmreazF9jevQe9J/Pnn7zxQa6QdNZUkGOjsFA/tR1/p3VC"
    "7F5xIwtbi+LnpTM2bDOsoZwnTVW7HKr8sNVTJL0PwOYL5T5ym7uWgcBmvOBPTk57L2DyCHQ+Gdy1HU2kGRzOfevO9/giRJUsPxFU"
    "P7Erzo23lhe/w6vv7n3GBLPwNEi4pPC2+u47LwKqazSR7bN44/N3uL+4B/fOqtdlFtYYzdjozUMPDHAOfq8+PoZjvvulYyX/5MJR"
    "VGWQyorvRnSvUh43p6/ZM+H35WV113cuNFmUX2IYpQVzpp1TmajJjHNESkQ4tTkSpDI/J0uVenL54VF78/ToxZiarNiVw84/uwW2"
    "ntEauHiuuD4rOQ6uE3yQw1iQ2a94NyzfXSSKLtddrkIxrynr/1T2sbMt9ZzOLxeMKMwO3sPHBC074gI/OM/7mls5vC4uXhM+b/ET"
    "sWW39li8dk4eR7sha2atk/egiixhiFo7lT2dWWY02/n4ZuuDa2zBonb0kgbnZw8eI7/Gqbdue+/QqFsZkpImnLpFR5Er5+3XeUAU"
    "eRn+4gheAGZpld0WDQkn9OYXPCRr7CC1KPfa9sk38A45/bEuU9YM1HPRGG1DfE3oAmUl0e3YINNI5wrt5OcXcYOOLKze/PzJuRv6"
    "cOIhPyFgaPumlPvCXsr6GozmlqELPiUoKFkngy/L9qUz9uD1grr7dLJ163vq6IR+BeZjpL1zjIsmXoYX8htDWOeQUZyZjRJF17dD"
    "z8TX784PK4unO888rwprhfiWR2U4vWcwvUCh/coptXgnW2e+bC2YRzsc0uffrt64vHLj3PLdK+3vLhfSMSXenb6GMhUglglC0JUC"
    "s7qYV0DRPiPVHD9lu+ao4S10oMDxnzlmx9t05ez3tl8lt26xIpVmltG7sBbdVElD7NFu/IU1hczmitcH7IG3TjzEtQOfzd6QldRj"
    "GDcwM9r9nJvQ1rOampGKr3X/NMq56BSjvGqNOIlPYUCtjn5SwAr9FB+EKAbLBnIwMUQoE195G20S8jKKlnlEoBMrTmoV1cfd5TpV"
    "0QmypTyF9aCUHxgAUuyd3fs8VwbipdHWUmpB3GKSTUC8JgeX85omtC9dbR9/ZAZCwY30Ftjfh3399My8LDSjTapyBE9X6iJKwVFX"
    "UDmNEc/b5vDtGQPHpceWE81gQ1YWL2p3KbT6uzjPrrS5HXO5c93ePyuOBFXXGReWCdh529mLXws9187crareabpWzr9XSfUo1o9V"
    "cAsTaCdIV0XNSWbenP5YR6O9qtBn/sZfnnxyhK2TkQy9daR19G9kXHiSVyFL/Gl6kTdqBBaGbfUJAZFDHNteqE8mwSK6Dn5xhG3j"
    "qch5AlKzopKCgJriHYrPKpNzCo6X4GA/cfgOZdMvuA7cATpohaD2JT0BNJx8QA+bdwy3cLSu/COA1J36PFfoOPI4X5VlH75hUKnd"
    "uBbMLHjhgkh7yK8RzMboB33DyDD7Yl1AuIdHT+FZ0JwI3YbCVsCV7nomqp4rzVQHEDDNS6AG9ThlIHmIVrfMFjz+RL9l86MFqyTt"
    "/rXlAN7P88jTIHGm5zNBrXO3Ozky3fM+X54X82sgvd75oX3+zdYbF6FafnT/L41ou0KL5cVTK2/fZuRA3aRrwmngBVME3MEXZXPA"
    "r9AFOIgAwuGb6Yni9MSJp2y1g2H25dSJknxHEbRETzE3GZFke2aiBg0pdJL2rGRXDMMAc7E7u9M3c5rk5ftHDftN4OS6mvN5xbdT"
    "aj3ntyyVMliRSDKA4H0PEyS9JksTysSa2C1ygFYMnrxuai9b2vjVxxda7surJL4AWvfk3A92QcTMqrG9kpv/wurlkxo7nZbQBURe"
    "RQAYrghm/joh62gVNVtHc5nTgIqYb0fYLhtqQvLpdJao91olprS+f1PMhtVblLzkOhWMEUuXUtsywIVwH6692eqcU991tXELncdr"
    "5R3c+YjtPGHn21CP2LZ1SmcTlMVCgJCnM4sD1KN9/XMblsNGG0uTTrwgc5by/oNDQ7uHntf4wx5aOaB9+3fuG9y/E7s9drR15Vgh"
    "0PCe3du5pacA7Rs8OLxTTLKJ6HWC7No9tHv4Bf2cXwAwuHvPzh20Wd+v/nhVm8RoN3v3GtHlGN5ph5xnFjAXP2h/eonlBAbBTLll"
    "P6WNUkKtlmVyUKwxsUVbFyCmqAwozEEzDz/UhUkgqebYjAKJu1sbrS9U1mjxwbw7bxtcOWDKfpltQPK2WbIy8TbAPtuaAYSBXK8K"
    "xrVj6ISz7S2AWKk9UnNLm43sILuw5YJEaaAcGqvUpxqHGaoCo9FuNjQENDzSxc2oqhnd9vtXnpyd10XKlCIXS8oyncq2qcZxaO78"
    "sGEscNusyOl1YfGrfddwMd8vMlehlrapgCwVc5WsBfWIuWTdgzWPmO227GdCu3EG4FRn9hO1xSLqGe+uoqHKWKhmvXrzaGvhWw1B"
    "7kYdLeXMiFxoncNInxTk5O3XzbceioxMMrAyRVroQ7MA4DlaV87z04xuF07eNl5oLSGRiMzR5ZhV07qAonAYtOOaM+I319WbP7Y/"
    "FumBhQYOV6a7PMg7XtSlEcJPfNa68Jf/tl6n/HRbB37bpdHTUBTKB6tVjPpOeK6H5zZgg6BU5oKId6jN/qLz4rkfTeSVu0bYBErb"
    "encRuB2UQP66iLNUm46eIp/dRXWa5XjGfWBI9wmxHuSWLFNFus+xBqwxy398RS0/uLVy4xzr/pxDacskdDhtfNAyiQXPDL9cgeK2"
    "ev8oUhFLBGcllrufwHffeIvXy940bFSyBdnLBkwxyO4rH36CjJtL0lkRwBFtgHnEgGIg6Fg4bNCwqneT+s2FMtJAQG3UlqqwPQAt"
    "4fc523SQhHFVGwWRMRw7y+VAyuv6zL2xrs9jY0sHYpMFsakQYloJBida9zo68OlduXXk6ydvfa2t8hgileTm8lqtA0XB71m0v5/z"
    "Vv92R1SjFisqqbPDRmN3ZB/ZEydsiwstTdjRpOhNhSKgIc6duoFB0ObPtO+eWb18FYZoogumXWIjcWV7qR0/UNvu08r7ndonvHMq"
    "kjHcvPEsnGlf/M4aSZHTuZVoHcf4t2urP97LuZvJCEazQd6DU5/xNtjKfstnnJc1iSd+F1c61SYsrYJo1jpxuf3RseXF22Yf60GD"
    "gk9RFEKzMhFZ2lad0AZAg26cX168UwCVC3DQAYlBuNNhk7mM7xX7hNhJ1TW9YQYRV/3UJZh5bmeGCm3ecxBdbN41nhcb9TrFP22l"
    "27lzUYw103w125jfjSXG1bJ6qAzrAY3YYFjQBb4a+2IkuJe+x9cwEKKLBgIiWfsGhS68dbR98tiT9xfab34HHBrSuEtnkB+98Td0"
    "+7UiLtnjmLAi/OjGdcSJHIysjzxHMZQVfcEFNpumYQuBrH3rBLSUfSCaWyRShyW1KTTXMRELMe6AWfF4Uhv1YjiDK+fN2Yg5tk0u"
    "LoSMYJhL5Uq0YHJKAiEExmPiN6jBze2sknxRdi0slcGTbIuHzIKgI7xtWkz8aaGY1OXONMGJbyKfP1aWozoKZkDA2kQ859LOLSRo"
    "A5MaG+hTn7Vvns2VSgfAT6Cbu76lLcW3TYd0EC4u5Qdicbc4e7P9/ntoT3T0h9bCHa1DswdENJSkNborv77MNmJ2YdqcnJRYb9Rg"
    "rniymZAijTuB3toffNl+53rr8tkc4KjfCCuJDtPy2WUQks0toN34xIyBLHiZRUcHKJgfVeAgedpcAbmUUx+uvPMdhvW8e59PJT+6"
    "4svaw4t8NXTMWNEBNo+0qDy+kaqnV6+8bmLMsxebObOO1oZjsi1WihnDFwEndfG4kki1ZaXdYmdbwha0Tl+Tu5qe6JiDyllqSLWY"
    "w43wVPkEdl6zQE6x+acc+M6lAlKaxRTEWi6Td4+2Tv+Qu3+HdNcOuYriF0ztp5KYwkmhT5HjheiUTCqtXZ6VaNixqrqRXQTTPqra"
    "BdIqUwtFs3KKhFnJ8ShdhjNmApLaQj7dyOQ8QFcyOxMZCh4nlsMUiYi6LHhdDmLr5gM4FGh4sn34Jcl86MSmREZSx73G5MLAPYgT"
    "qsTGPH3qyZcLKIXSO+iTczeefP6xyhhJfv9G6lbxHLGs1gzlgZIiaZx5D4ZiF4nIYbGleU9teUE5/TEs4lPC0PKjnyyDfrS1ZOvV"
    "L45wOEIOmyzIA+NAx7HnZZh2CHBnsKEBoekhcbxwF9/754+j0oeU0HY9HT7FdGQiGxm/eYpXoFKFct5rpEsW+6qXQEJY/3h95fg3"
    "qw+/RMOj99FgpP3RveVHj52WgAkezmL2Ibaa4og7FHjgHbbUFWBtTvQuXCEYA4+QnO0Y9AVlx1oj8zEVekYCNInUZuL1WDe0WYQC"
    "r1zr8xBc8oJMfFXaPjtiy3L6JtdEcxIVE4CcRb8EVFUxnHPd7VRG0hQYBaXKI+/QED/EUDbn3+ZZMW/GrXc0sb048BivmTmUHRWK"
    "IpF1rzRkv578FPBePvut01+qa4PjPyMIEywTWN/QLVOYi/R46jIZZJ3I7bUKjnhfYtbr+qzU4rA9bgGw8aKxXfnkETLGzLQYgEpM"
    "liMcJlzhoT/NLwq5qNmmLBd20oq/njskzmCFPTr1IQdCINo3RSbIp0+aT9yDCg1w7Vzr9Berj95aufa2GFETLKo+Tn/MiAN/kpMg"
    "2gmv3nyDGZD23SPtT27xzW0wCBNFNiQ9Ag7P/ay8yiyVJXJFmoa5geJzYeGtdobdTAq6Xr438X7oaB9NaSx66VZTDBAFG0AfFba9"
    "ABaD4mSIC8rpa91sMqzRJpLXTQJREU1yypxISZ3hv7RmqH1WLI5bV75hPRrHKqBAaNf4IxKwhY/IlfMaNwUAOFplHce2vxi4D6bP"
    "EcnepNC0qjteH4kB/+3Hy/fREJVN6YT1Z5OaU3/FN2VqgWzw5jUA1G3f/tvKhY8kEQBg0MMPYLX3DXr83ds3uGb7LmuJ/Gl2L/7G"
    "+sCqZnz807HTeIoqgXS8P5jAlCsJv6E4C8s2O3t924NrYs6s+lDeP4cGbkYEXJK4SuB3Y0j/wu59wwZEnU/UN5IXjsNLAYxfrfIY"
    "xEnHLqNRaI+qjhPOWn/jUEth3Fjv2IkicMUtLx558skZK275cTMb9dxhdEjKD1SXUhp5uXFdKMYWPemkRpHCWjeOt458zZct9P6v"
    "5nplEOXAhqnm0NcPZ0cuoLYKgdFXSIAKY8gYjNco4D27/qtrWuIcnoOD9x7wd6vXvwTWzEyzEozBBTGcMVvBtg5sXWLPVJ7R7Zj0"
    "9y4paRWTX+CL9eV7PHltste6c3X1+H1j888yvvdbsWdu/+2N9q0fMVwjWXKSWR9Zdmn5VCeZ2o6DsG/boswvXMJvmi9KqLpuFDL3"
    "qk/srMpZxxC217TRsiIny29PfMwlwr4SCtg70yaNYibwFFMAujvOW+Bor2TMjbuOl0DrzG9Koo1OILTb1C9KdjlvnvMYsXh/5dt3"
    "LDNLZq7MquPTrFLU0/MsD1A7ettYKi5kFDs/V12wPGfJ/mAe1oGbRdu+E197CCtZsoanQX6tovGfivXkKctZx1T9o1utE5dW33qI"
    "kIsfr964wra2iJCEpWIzDBgof//WJO/q6I7eMG4dBaTlJ1Tty20LGJLbg0Zs4ydj4QthtUpBE+2VBwLE24Uj7kBPvIVcL0exPyI0"
    "MF10pDjSHy2qJMJ+7pLnNJqj050K8gLGCIA5dgdriO2HBaKYC7NoEDpnSJlqXV3Q3LBbzZHaOGgELkYeiN1IjRPssWur97/VtqCI"
    "bj9+1bqLPm3MFzF94Y/IZnAgyLP30FyIwuuLefypz1GPo7q1107QW6+YnCt6wbMN1hfJ74UCy7AZgq3L0Glu5IXq6Ckma2g8Zr2U"
    "4CMoUJcPf9SPcnoYGm9yG9iJOtwjjIckSxyJaUoybeN8CO1Xji/AVnizh+ds0q4zT8t7qzLeJnYh4IRTpqaHQixcJHffQk6QFNT8"
    "Jz/MammxxjqW1uNzrJIiw00/q6uum1EqhsdIFlXCDx2VTS2GndaMUyVx5jVhOkEYrtrvl2cftR68Jeynerm0QVmPYJIvFHWN4YUo"
    "MtLKl4uwb4gv1KxEl1MwbsukxzSdS+E4YNPOqrIeZ3ThoI4qMTwFiT6UchgBJDZurBOj2Vg4yppIDrNPdcPokASd5RuCQxORfwtI"
    "vU+OnVSAhUH/qaQooQAVcDC6Q2I4zm7iy4tfsO04QVRDGDTfwUgVH+lh5SK78AM7lbDtlOZZmBq2P72syq3YsRYNkCCyBEGE6FBo"
    "AlVzRgYz6gkVM0bFFpWGs0NRYodeo8+ADYl/aCwMGlUneCO5NX3auvJR6/q59o2/GXB/NDukdXwrPzxauSxBgIEMri2t29jn1WzD"
    "UW9ted1Gb1yivFIb3bMT2NYlBAp7e2hMgj7jlsLGqSDOlvniCSHZVlRoE06H9knCAeVEFRhxLgCzFpGs4TbiqUNRnHFwH6VosFRF"
    "54oyFSnWl1rAqCCHuiMgFXfFQir9aVQkML0vOVWUNrExoD+FhwTkxqtiPAOJ28VHguxure6AFZ4LlZOQSbFjjMuJYYgFk8dxBYsd"
    "ppI7WUgj2YvYGX9Q8rVa0ASLW8D4X05nVKewMzvPueX/cl6flsOzcs/M2dX0i7E8ZimTQg1g5X/OpRISIY6GhKpCmNtbD3meuWlg"
    "G9sK0u+IVhCmdvfu01tQy24uQWvxcyvRnDwQ75Dg73d+QPOai/NwVfLdKO0mo+U/NXFxY9uOAnAe2Domyp15kOSagqrNhDDuza/J"
    "SuDjlRuXXYe3i6daJy63PiFB4+D+PVJLgrnxgunE8P6oyvztrAwlGtJATlXto8NlGPnkxSaHCp7H17JPFtnc0hTvjnSiQaY8HOKk"
    "s8NcXYyVSeFD37yxcuN7/bkouAOX6PSaiCGUFdQeBNvKOR2gdLhdvJ5UpGtPh6TwnlyDfXjD7gFwOByjzKpUZPWsMqPRCwfuN9wO"
    "HdW7u3pZi8H4ZEYO0DR4beQIUyiA4U1gIHsrbFAeZmcmztx47So8Y7sKg/EmFlbh5dbJ+3gY+mgbmKDKY0Z2tQh3CmkKClbWYmlg"
    "uH+2W/BoY6lo0OxUfXpOA3YjOYISOv83R5C68ReYYnv+KyUwSoBXGQKuwKd/ad34GN9N7r/HJw/udi59cp71KehBxQwfvvASjGUC"
    "hxEc7p6SsPS0qDoEB7pv+VHNmFbfvL769bz6qlyKORaJW+aYR5P0ReJWJgIYwZDksDOqNcK0rr5NZmu27cc01nGSNWvNpWup17Mt"
    "8dOw0aurIRO0M530l76PG+ojHaEdQTNLR3VbM/U12ymv1o35ZVRVXQcWX5WJa5/oB0DuvnMJViuXpZOn9PcHF4xN5Ck0Azj5Bqwj"
    "F2Icf/Zbf+d7+ILyDuMluz9Rpk2vI10nMMirf7tjU3rMN60IYWewdP24TkoKhE3HyUds9c5fMZ6tetzDkoJwu/i5ID4vftbKJCO7"
    "KJNurqVvP7msiATz1aevLORMjlzVTZsZEd6UyYrwu89XH79rS8pB4gD1dz65msK1xHK9xbk1zOd1fAtp936ncL0utHVvpnyDeci1"
    "Z9z3f+oBFw22aB/ZB0XpvebZO8asKXkRWhwUvhQU8RGdm8K6PUsncokX3HX0vHc7f0PadyO+t+ZJ0nEzuLV24g16hyf3VnKOxdBm"
    "aAZ+VQd3YJtxN5mvdrfgdwc0J5n/qv3uwvJ96BgOw9fcJGMDPnC+8bh15FTrNDrJt0+fgfVGL352OL95p3Xznqz6R7fEh/fM2yhd"
    "HTvKjZuhr5OElT8vTJkoclQ4FY6DZszn3kdLeCe0B3SLuY1RXW6jyPLdswhJeyw0yPBRpOIwI1zvO09dym66MzxbLnoHR2uDj7B5"
    "xgWPwsdE06PNSjjKe8i7bQdzKlD7qceLLvpXGmdFq3K8/5y/r3SY+FNrMffEftUTR12tPk/F7dE+KCZ2B8dt0OmM1DMc9rjB11Zl"
    "OsoEtGP7zRQ4UVq92IfbarbSqdrC+BWky8KEC6QzxM3usMG1GhnVQjRmYWMSx10/9TGU6rKtOUXOQcsMzhKuHyoQRT9CcH3Rgzgl"
    "YkmH7YcECWUVtqI12NVc6d/qW14dCaKR0ghdv/BvkML/qgH8jy7RkddKv6xvCbb89t/q5TAabTSrQdoT9JaC2pbZIBqgupPZgKoe"
    "pAPUQjUYoEZm6gPSztzmsWZEQf29rAYtzCZB1kzgj+nJIB7zgl9sGUkzdPYc+fOffxGU4edET+/WqNloDAS1V9WHchbviaeAc/bT"
    "AP5KJxth1vPMq2sOvfZM76t9r722lWrM6a4i6KqU6c5+WYeetwYDMIKsd+tWHL2BTVzYbCt6NU02/NGg55k/zPb8YerXvX+Ye6ZW"
    "Aqiod8tvIy9EoGEadE/2avRa78DI7C/h+p4b6R0ITLshtQt1VMvRli1bcHX+/Gf6Beu1deSXs9ncH5p9fX7fL2fVZOdG5MdA8Ots"
    "7rCfeH4NVokPUhmZmZFSzPvwp3rpX4SB+l0dd+E/6rgH/w6fhRd6pT5XSmtbemDks9ZejNJeQIE14Eatp3e2EWResOX3dZTlxzaH"
    "Yz20dn/+c4BDRh5vpFemE2zOkmmBRwVZYziLE3IWCrLdWTDR49d6N+c2gFuYG0WfWVkW+UTzbNa2JFEPjqO3VKXfuK29pbHalpd7"
    "cAqw4s1amcIXAwD/ANhJq5zbs0rNpCdo0qrEnnqdSpq6BJYMPtAEzcS3OrPkN2k10QGnLNUrUAp6ZbZzprc/OQgH+BfXXh2Tvl97"
    "NQBs/lOd/kEwU62WR6g/9UTBlLc7yhrlfY1m4jf2NxtwTFVTcE6CBkgngPM4hzgKCOGCOTQDGhmQn2jgM1KajQayUrlcjuZ6aScO"
    "AX5x8r0B7HRLHy6u6myICnbFyYSf6d5KsxP+6+FEc2JXwlmqd4S1MEuh2QngOAu+z/WWx7gJoCtkizMA9AaWG/d868hWr0Zj/K/1"
    "2mda3+tn9XKCYViho16yQpqABZimicG06JweqkmuwZ6stBYRTpawVJnOiPLNwlGQsckBGBnZjMifbZF2/ovLYy+DOi7Bb/uDTUQc"
    "eoJn4GepH8b9/LaRASx41hQ8SwV7t9FC8ad1pT74NL4NiHy1yebH7uiBzIbpLswlEuB6yFz+c/6smg6t11gjjhNocN2zfX29pcj5"
    "+K/48Zln+9RwezKmY17dg4GM9P4ad23Og23HQfhZcACkW9xbvUI75GPHGiH0cDbdAEpBGbdHSuga7Xwx64XNYUs9wf+EeQMZyH52"
    "P/9Iq34tpiOAH0Hmn+rpxWXujhCyWLDdPX0lC/myNUiM1F3wm2f7tv4JiBVRi9E4qqZ4COd6B6Lf4PKqMljEZhZQ2YDVVoTLD8AC"
    "5cNC0ZwGDqHoPoE7Cwd5rnQYr4l0YNYfHQ3wut7O0Vd9OPFJ8EegDQMjL8WNw0gB2LcU5OxGUAvh7+YkekWBaATsIhb70WjQgBbo"
    "X2yAYqrsDVL0VBsYGYq9uj/tAcFBvi5OpXwX5ZA1UHBnLt0Hmkduw3419mDqHoibcephutlEVxymMA1282ngBdEoxkbxk9hqAmqk"
    "LvBs35xVrGsJaINzDDnQetgelY9COYPLWPJ11DxUPacaXD7+NAbyTgdeHanGsIU1+DbSaEbEZMHqZ/wjXPomGYVLHf/4YzM4TD8O"
    "h0HCgOnS5Qo295puj8Kcc6PcIDcnbXEr3IRUt+ruDSOouQMK9sB/e+G/f4f/fgf/vQT/DQMkUMWsrsYdREGCox4LKgn/go5m8F+/"
    "koQN+ns6pi6jkP9t0L9wXFK8gEdSwLgwmIDq8Ec8mjX5VxQf1l+r4aj8tntXs4Qh8AD0LKFr7pj75V65T+6Qe+JeuH1agUwoADCn"
    "1WcmJp6ZhgboBWuHP/3iGLrZDPSX/CT0B2YpdQageZAk2CWZqsZNYG8HUXAJY/iGihU4F2GtGaI6V5raB4hBFmQDI/tQnZf43uTS"
    "5VoY+SMlSq9gypfON9BP1pRji3Z9/u6lpgscRwGErwfFeL0/noKRaVxM8FBB+83IKt4RpHkAoBTANWoqsQ0O5NKVLKwhl6/oxCvN"
    "ZOnB6LghFIPNdGrpSr2BQIpYvBCP1ht+FT8pgjFYqVA2gyhPMX4fhFHg7QSBMFm6UguKCYYAJbWgEoUpkICxpQeJVw1hDh6DFtOL"
    "jnq1APgoGlgBsegCV0Qp9Hg9v5nWAlqBrCudwGFwFb/mVrBIxHAcRZlfw1MZy48dsO2pfAuzbCpGHefIDtQ2J/J9VxKE/GsYWCf8"
    "1UknhmNqlBqkpqgRqkz1OsjDsJCGHda/u4rIw+8wFjs2sgvoA//au3QlmYF/ByeZPuz1sbvfAXmgfxr4z2Cz1kzxfA4DogXIJsHv"
    "F8ezmH8NAUctH3cEM/yziDL8Dj1AsWvplnu1++QuuUfujjviTrj9DtJQnpgo/zRpGAYUD4OlSyQCa/KgjwdTh5dhc3AeedKwE/4M"
    "vGEs7SALe4JsxhTmaMLQ0pXRulU3RxBeihPg4+HEqnLrwL8ShA1CV3Nco87iiioFYqCER00RODiCIQarj89SbAFFC1jJYegA6qIf"
    "fGaIAGcLzlMAVk8+uXxv5cKN4uNvB1VitcjKddSMtD+9jGZD59/meCPFNEDnZVBAuZPPhR6eajRp1UD5Q0yPRaQ2RVAYbtfjDj3K"
    "MwBFtSJQ66C3P76ECebOXQX849/Ld+fN7/snre/H9e/WhQsWzFnz/cj1giOPTsPUAXr5Uuv4g5qmL8f5BzdKRWfli9MckwNuiZvh"
    "NqQBqi1VqZ5DHFALd3GB68iPu8f5B9RURWfly5HrCuYt9eVb+XLvU/ly6g39QzeOv7n9IhLRz0Br+Z91/M96/mcD//Ms//Mc/7OR"
    "/9nE//T3yb/STv9a7sgmGNPTyEtUqz9FMJRtmCEW/FQDSKfIBSvt6UOeYqx89x0UkY1kjl6g7yNmmODCHL3gFqkkRyq4cyqxqIAE"
    "Ib58Mkcd+OSa0rk5S4s0TWoTFhsDtNkarfc88+ofquXXfv2MVv78Ivvzn7MyUJZaVv/NOvP7t1vW/+pXQyJ0v7ruNVRS9LHmr7x2"
    "06b/qYv6Xuv9dXnDxufMl3780t+/3nxZ+5qlKKkYRVY1Hm0ih14eTQLYup3Mr/cAZ3h4pHczhiYCIbA8ilYrr2dbRibjNMQmBvxK"
    "GjdA8tp8OEzDStgIs+mBOtk+bsbnthqJYQOH/aRnzZo4GfXXVGolD275KJ308dWzFw6+6roSV6fL/uRkEFW318MGqiFE1Ib1qwXZ"
    "9nhiErqqkkAKhWXTAyZNTYxaQJROPSDqipqE1nxvUA39npEeVNkBf7AGDZOSNSkwXSARelU/Ge8d6eXtCdKtI/gBBPUGmiWNDGS/"
    "6V+7MffRLOXr1g6jZHxw/x6msvt81Nj0KMs4CavXi8q/npEMex5BvQEOspSw+hFbSbZkpAXF3gAV8Dd3uTUbwG3bnPwCZvarX/VE"
    "W5LSC/WepLcUbC3DP71zm5MeXrdwy8+f9eaQkggdhn3YE8L1CfxTzwgHyYTbjNvzaWZ7mxnN5MVKGiQgEUOfm/1yzH/16M1UPwST"
    "SrN+liVhBYX0gV/0lfRffJEBISIMAwoyCqeXdOx+5q/hBXptjgcQb5kKo2o8RXpD5OgP+42epLQuWKdVLLh+oWx/19mUfLL6ZJsE"
    "QBKKo6gbjHtZyTqMqj0glQMj6WSIDOVIaSLIgFwBD4nUW38dkbAo+EqQxKMBDR9jDsM/leYYLDoWvjZXSg/XBmZfn2hEQNrqWTY5"
    "8MwzU1NT5al15TipPbO2r6/vGQAZKU2F1aw+sLavVCeTOPyFfoDb4tcHRvq8PkztuLYPKSCQgBEMxDgyV4riKt4pr46gje5IaRaY"
    "i739Xn/f9n5vQ7lv7YbnNul/8bPXv71/bXndpr4N+Of68oZn13r95U3rNq3z+p8t9z+3bqO3rrx+w7r+tdvh7/XPbXgW/n5u3bPP"
    "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"
    "qDY6ubMVWRcImuSloGqWmk7o+M7UmYPB5IxQ2U1Aa9N9LCjqDwD/kVKtdNMdT8QM6ux3p0kDROFREkEDR9CIuwomeIIYBn70wBoN"
    "wP7xlSVJr/ohjuZsKcXyApC08qAxQA/CYh+xjUA7bghbiFfJwghaur0TID4YgZitCSNCKBprOpBJllxzW1OEcip9JaoZaGIivBSh"
    "ks9zbaqvzzZ4XfTbbZn5EqoFjDi813SkEEYmTKpieNLmUoutK0NX5YQ9WW5GGlt4HMxHcThL8F4RgKg5R1DpRjQXeHZqckvaTmkq"
    "7VYcIUJSczIAKvl33kI/SqRLRrPe0ZHAlHu36uupR8m/GkPAmaIjB+a8aK3DyM7O2PMBlfA2zoYRzo2+EDxcEDibqiKJ9nWYzACV"
    "O1s2YT8C7OOdoSL1yEFq7p3l2edz7yzPUrPv9szk3pmerXfv3KaagrT3Z3XvQI9/pnvHopWPwIi4lNzngya29Pmcn8kDX4/AvMTT"
    "hiDqosQT5w7uZok4U8JzWTh1MpMrm/XFFhGvHUoOqMhi4/W9rZwwojPmd/vsovhG2BP9u0LJdyiF+3fh/LXqOry+xmOBCZHWlR+N"
    "MfZAxtlzxm6V/dTMx4c7xZnFvjxMx/4NPAB3TEGIofW57QS4qDPkyM2qM2qEH1tWG1nGptBThJjYCC8TPrZxtBPolPZyBPw4lpDg"
    "UUoNGs58ReV4FIFdXllfLksrvLyd1UZ8mOCz+5y3iMztAtJWzpySKeXJRNCCswjH8iedZ+Gj+dNYJSqUqRSimKfTuaQnh+NNH9M5"
    "4YLfCAWgo6wSZ+RMnAV78WbJsIbhLmdAyoPF0ApkcuoHCMDsmsYh3tiavCGrIusNAKFH85o6bk4FUEcgdyxoNCk2is6FpaGxxNCY"
    "rAxmv615+qLa1XT6Nudym0aPNESoPOVzIzF5MbBCBmmfPAfLRXDMq2rVVjgIU3glcKFE1WxwMQQ7LttEWtlHyyzXIKYVGvSziFVo"
    "A+sOOpiWdjAdTAsdYFqhgykjuW/NS9uaD+bZtmRdgfNZWnQ0GBWnJ5Odn5IJJJVMyYSnZCS4NqXxHKTD1KUhSiraH+RqwoIhV3V+"
    "5Y+n736aTsV5iwx7DfB0GKcDBw7SAvgIuWxLr5Ce/pqN8Nze8iwc43kvh4/njwv+9TNEh+VNIx77GMsyoz7H2FnF8iQ5skJZNvEo"
    "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"
    "Pt0s9+k5iiOrA2J0sr+//vqcaLn7/Pi7+el5AXV0TzDGQOATCqHwKQGCyIcuTWBdCiMxErqkkC2EPUEkhfHdXxSnyD6/+0swXZrA"
    "YaJPQwROfYDwJxgh0Ps0hpy5nunxJxJG4BNfHMY/3NLQpdyVHjr95Tu6c5o4/e1be6YjzuWoE5v7dF8NeqXnkVP6xo9B+maR6K2+"
    "W/rSnhv9pb3IKRu59Qd93T205wrfxMFTJyF23TmLa4sw15yTQAmqa2Av2JO0P1yGQL2OllGkve506hSnz4/9ZU/PUB7Cx86W/NYh"
    "ZCN/pq/eKt0DjD1B6K1m/f3vX4Mz6wCc9PdTdkj//WRS8y+fZefjRL5eiffReowePv/X5bap1cf84bGxPg61/g4urWf9cndYfwHh"
    "w+PujRYUybs60Gc/F8kF/150w//pQad55em23f/9+O8GohvYfiRQiKCgbqBIGKR65EPECbkd0jCM6NMUBp0Qe0Ii3I80TvBXpJKn"
    "NHVDNtkjBrsiG+oGvEMM8oJs6gQZlLlqCnUiQz9cNekufdK0Cz1/1kT0iYRAbAsRzDnd4fykvVct7tLECVinH8wFbefcGzgvZV7S"
    "2zNb/gxn4tbGE9qRlzadtQG6S/eoh2/0Z23CLn3GLtqFXGRC3ugvMuOv2nqV6Zsx+Z5iZGhe4elZMcZvFWOT/EgtevR9Syl2/7xS"
    "zOXPz//tQ/ffU/JTojn9DW5x+uH3U1b/n+llSaA1nz7YgVX/fMs+eRT9veph9umD0fXUSl8eHoos9+zmp9NVyVH+NUHP66cq1ZJP"
    "H/p/Xx7omuH3FzZG5qcPZv7xv99a9PTy5L8/vNAbvXzfkp4y76mSbsrtr59/Q3fJvqfUT47ZT6lmekX2VRNOD5/OD+9LOX1HXtN2"
    "WVeKL//tK/leJfNvk/M/3eKfOicpvW93qKUdyU9eFHiR9ZPVD5xW5PGPGXWk32RzquRHjLpf1uPX2VG3+H8nu1ufvJdte+m7+Ulq"
    "lXfN69Q564GWxN5rCd+G7dLyf+XoFVkHxfNy6NOHfl54eRSXVmp3jtinD2eP+A7rceb1PuCnD6kVaLlXWn9GuyKtfNJPa9lvKNoZ"
    "+5+62ep1Q95VwDtuX+li2I3yeUL8dqHT8/tCl4nz2yXOBPdF7E6qP1U/KtdTPVXvF+5vLv5R0Z7mvmC3bI8u8r/lvZb8G4YvBZ7M"
    "ItX6H//94fFV2ZMI//FicZGfEPlPFtfj+qfM1Tpn7M+U/ZMW9B5m3zKmN2MN/vzGOtyyvmUNPp1uOv+p9DKvW8F+wzb8kKi3FD8k"
    "OtmNH1L1VuQ10Z1NeZHwd1HWX+Lbr4SfzrT3oroM8Z8rflGqP1dVv4j+k7RfafgVeLFtd/7Kn2vcmfZ7889pfKM4//j0cvn0wzXj"
    "NdnFZvbP3d5QfnP4vmL3LfLTOP5p6hPK/jT1CW7vU9+D5c+Y7lOhf8RT+qrsq8H81jB8W+D/aIOv5f7JNt+K/7DZF3f8fkZ/13M8"
    "kz2deplaffjqa3x/Z2Z5r/w/OsV8k8f9XPOtocn+Fz3Kf9wvPOT97fFJkffZpx/97ssrz65+f8I/FGHylMfnjp5KPnW0ryf/92o8"
    "667ppR/TPHj4lrZ+5/lJP7/z/KSR1+d3PTnNfHachp1vFedabn2ESNC0nFtbn3++RuA+HOV+mfbX/6H3d7sDrhUkVpp9+OlDH7iM"
    "7b9eVmsd2edzzgepCfU4+Pz5+cri+W9/e/XoqRuy08ZIR5Odcp5/uQX8rFvE71LG+vLpnYfWG56vq7M6rPc7D4VxquXzmabL/8v1"
    "91PSdTzuWfxybcOnW4WPpz5/uYlg1iUf8245eqn9Y/55L3cL0geva8gvK72Ppj6Zlt3NFUIad/LJm1OB30stKDpb/2hFRXiOkn/6"
    "C/jYtc32nOKWrrql8uX3l4dP1q/5b5+7Ii/V708j0IdS889K35Tn7BRRfn54EX7Xmjtp5p/ywfPzC4dTqfzhd8/+eOraXz4/x6dW"
    "P//xx1+sh6tMTxeKRz93VK9k+5/PRSfTj9Fn69eL8PJYSL3Q633y3zpmn8/bAec2pp87X1kLglONP59rTO9qvNaW/py7aeeT9buf"
    "XJrG6cfn//E/7hh/CLtVxYcLsfYhueWfhPr0/PDlNhh9z88S+eUca7/sfjz0o9i3SX1nz/mmJc+XSPtcPu9y9rtlt4evsHcegl7F"
    "zwH2x04kT77VXIbh1+f7wEPS+ath0i0xovz5sUPQ73+918xLpP+vn/6SP7laNkwtzT8tybKPD18e7xn99B+/R1+eH78me/it3xY6"
    "r7ie31mXPl+fSqc16PM318A3Qq6b4p6/scLtw0EnR/ErXXzV7bNNe37se3v1Af766UVkl9jN0/XZl9++nBmfYkBfc/rJ6/KfH8/u"
    "5w+q7on+sZr7El9X3Ode6j272T+otyf6x+rtS3xdb597qffsuf+g3p7oH6u3L/F1vX3uVc79zPtGGn3W+cm7ynB68+Lnd8ejK3Ju"
    "3zecrL65fQbvRf5PUKfGZ1+hb+nFd3gDx3Nm1xhDjCvBSoWOmu3q7wPtr0nTpJPK5UlPP+umaDn+Nn0/+b9PP+3nc7nHwfO73sJz"
    "H3tcvwTkIyewfjLjopP5T6e9yDeR+a+fP9v9AJwl2O9KnTN7R7L704PRi4vs3xGmJy8hYuyJ6jdmGPKyIYM94aeNG+ocRX9J9pFo"
    "6kZ+jlQjH/An+FTsnCa6NNEVg270xBPYb+Tw+BOGg330HuSvjyC450XeWEFIz4u4serSxDmQf6FHe16nnZ8uG+7TyG1joN+qOqWh"
    "D9eeXeh59Nzk60YDg166dN3yQm9dPPO50l+C6PwbSamLrmF9w2+y6CrqhXCTVZcm7mUHYaeGvNBj54ZeZXdOwzfZXemvsusEBeLg"
    "SXbXR1fZXVldZXdldZXdjf4iu2vTrrI7N524ye7atavsLvtvN9ndth/B1/t1t+3CC/1Vdm9E9b2Nhyar9Mg/bzz8x/3GQ69U7Emn"
    "+JP2fHMD4mvt+9ZOxPqf34mwuHetQdor4/fMwYXgbA86u2pYVr9xd80+zzPPnd9eaan57zAIZ9jDN5RiJ3TCFxT36O2Qg5C3NH5C"
    "J3Glv6g1eR36i1q/7CSf0/gNOtTLFu9pR/nK7wpV7DVSr825IvXa3Cs5emnWFfl36ZNy3ujPmsMTTxRCoSeluj666NuNFX7p8Uv6"
    "3IQ3kuoMwgX1NwW/bHpfRXXdFL9LY3cG4abVV9FdtfqmVVetvmrdVasvorvyu2n5ddMfvZU7vxRw1fKrVl/pT1pMvliNl/RJdjf6"
    "i+y6fBShsJNBujy6yu5a9Cq7l/Rl+F6L6nsGISWtsDjbg5x71x6IZ+X5UwbhomjfsggW909bhOiNRfi2KXij7F9bgX+j+hNPBHSv"
    "/uQTCL2oP9rPquSL+vdpgrxX/w4bMHnDcIcp+Akjbi+SnPTulL5h+EJ/xfCV3xWT1/peZvlze67pa3uv9MQTCt/r/136hOEb/QnD"
    "RA9cnKR6rPPXR1cMX4teMfySPmP4jai+h2HnqOV1cwZx+hbEfwq+P8Bt9M/j1nuD2286tK+d1re+7L/Tie0NHXRveDtDCL02vBR5"
    "b3gvoLvRX0B5s0639MV6XejPyOjfo0AgEDuB5obfM55urG428yVNvML7i40+Ne1moy9Nv0ufunb1xG74vXhiN3xf9Omavurblf6i"
    "j/wbUX0PtHhsp6h+Bq32FrR/xgf7vvPl/fOQjW+Q7Y8KCC9Rnq9PC+RxrgWiZcSp+Y33k8+vrX774Tkm8q2n17Wt1AfH3yXCzvwv"
    "S9kfv1OdW2ESaPmV26/n2OPjOer1crbgedS3S7hU/0Ho1O8lcfmRfVh2Erll89pdAfGlTdfl8vNtTd7niqdovvy6Na9egX7++Psd"
    "/ZcPsf3hLO8+mX15eO7f5a20JpPcuPr2K7rX12DVH7wGexvn778Jm93AwbztzPOjG2f58vTwu6jpR5XpX3X95rjfdfy72PgnYfVd"
    "RP4pTL+B0dtXqH84dH3gMUyK/mXf3/NXIbKX6H3/Ru+1nn73J9AM6+PzK87Pjyequ6yHO8q7Ki+EN8nfk51k9RXFf4G/nDJOTwfQ"
    "J/C+SB/w6kosukniKfSij3eUp5+9gM/87qX5cM+iJ7lW2v/+quGXQleaV4w6JL7srxjceXPhMX30HrWb/Hp7x3987t/of37cdCNy"
    "OpZgPRn1x6s9fn748mg9JXl4l/PwyH7UnvoxeXiEiIcvGfd0fqX6s8GdwvvBTQNe2Yg/jf430Lmea3ptp770LoIb9wh0rFyQr4bt"
    "vV2e07B1fbAefz+Fmzs0/X6NWX46vxf+JpD55eECwFNwvavjzfL/03/IXx5NL+0PX5R9ND/1kqSzIVF5L/fijdx74cSfU+/j85n8"
    "ZXdlF338eBmO83btVwNyDno/PJ5EciXqDNzTfe9fyH7/a3/s66fE+KnfKU5+ys7HRP562pSwrsUfHn+9zHqLj9FNlf7446tox8O7"
    "zeln0x4h7zbi/PA2cz7++nwq//zbw8Nvp5n08ddf499+e/gS3PBTnPFj3vDzdUj1xyCyQi/vncZTGNhwO1fAev7t3rBejdWLkb1a"
    "ryskrpPEVSDZ9bjRFXFxxJwYv0LbGUh99R9fVf5oPbyyZsndNHxn1LpF18fTWYbPv/72mH8Gf87/87W9+TkfDB46ZSwy92NnX3Qr"
    "uFjVj531eXg8bwTmX26Yst5AeCYL0vn9uEK+R6n9LkoPH59vBV5wegZL/Ph72LnBwfa893hq4mN86ZL2dNfBSy5/au3zqdHPl7xz"
    "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"
    "mhBW2T9L17l/RgEBV1tOvM9B9uoH9WbDNZ6564+WKjlwnOXD7Eb+s9KGYbhGLXk68r3qLAO4SebX0Kd2whRkwwSDUA3Y6NiLthO4"
    "i3tqyo2NhAFDrq+5wHZDiZ5PbuM3YM+px1iDvw3bMt2KvFVWsLKROWqpiDLd5pr9BmN4Ry0pP5GMGyn/cLiz0O930mCwlwIf69Mb"
    "NkEuZeYWr4Gsc2+FxzBfl8cwYCu5OcHboJQGEzdeorHcfJXyGpWb2cpgJ0o/fopx3CZHgZEISULdDR4Lhi9HevYVHhA00wfjhh24"
    "tTW9ezeYPhw37WEosL0dfD01+ZJFMA4k9c4yllc1NOTZQmrbJXRNUJ2S71bWlRmTy1b+nipx9UfHT80IxKKPW+hAwzOaTTsa6cbs"
    "kmqG0CI20E1NJcUm+78NdQwVLb6NbaHTQL8VNrgSy9Sroil/oDRuS4aEQX50VVdjr2jHGO7WB6l2hpFKaWfOztbdvg4raKjNfyHm"
    "qzguSsWJtFrIKsL9boMnUayeRG47Sb1j8+wtu3flt1SDHO8GzYziljdUvyWzJ+0nb/isYtt/aV8oPRsrWV3FLzI+ZlY+SQxIbvAQ"
    "sZ0QGLDYVIn2NTBUDiEq784g4ccCEtWoEUMk9D/wAr77d0y/twsPgrxJsz56kI283C2gVAxcCqU8yzB833FWltklhqyLpoVbVHlH"
    "6WbNxqkXtraj2Eq272mYeHgCFO8BVqMA9W9Tr1gfKrS+WL/3EkNEt3a9ekKwDZ86fs+Rty7I/4ShN+yEu70gv+WNcIPt6QelwzJU"
    "H/nmN4h9SFHXseEIpuQv85YXPL3ZEG+59/Im5/+mm+0De+bdZiyhpUsQa+tzfTv0Gm4Hi1yZVXPWur4qLzvN8LEaNAN+SZ94NjAP"
    "XdVGrsS+E+Ihmde6srZ7QTp02wYMvlYbrQLOXUu1s7zb7J/aiHni0spUxK6rF4P+LUVArFTSwfYJ9aSnIHPVMdFlA6rsONoe3TLY"
    "Cry3KXro2wufPA2QywFtwiP1fxdKWy+xFYMHkXTjpQO9jNh7XS3dx0Ab6QhNm5E+msQYeKWDP6UZZ70puXJ2O4dH2A4/2xK/Hw1b"
    "PO5ulFKXPkG3DU6DIbP1MIj8QAjejEUWWhnwEu3XPUNwdBoy6dDTT77n16SnaNrJW2Za83nqSx9QtQA5rtnhHDI0EghGJn4lCmGM"
    "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"
    "If290kmVClbNdjGyD3U+pnXKha1SATIVtZz2Is0Qcup7fdsPHTtY/NqHOLFDQq0cFjBIQ1nUhXg/XXvynbChrTayn2Ko/IHF58Bh"
    "bdks8goFi3ChUKnlyx1C4rOWcsP2rX33PdoB9npYwDST+fzrxIKdydHCRXimb/AR3k8wxkOvZzcdoFwwuRCZYA8YwFTt3wgNSSb+"
    "zyUq2fzxf83M/BNDhM74dnfrCz4GHdsOv8w0fC8IPN9pO+6PnO954evCAqZu8Qgn+eWo7sIqfbFmgnEQ2j2yC9bMAmm9ay/QEmum"
    "0HXcx6N6o4q/S+Q7a+ZL1W579sxFGb6suwEBJ99pfadNQ1qGHPuLHv5QvzRzRH6S6l+K9aBBLvY6Lziy3a5nzRQJpeQRuLBmxHes"
    "PUCdC89BLpvtP6tFQS+XXdaLes1cdkUv6rZz2TW96Lmbg+ipatEylG3oZSukbFXWC7K5VfljOSdrByvqQILVXHZd/lpT+wrWc8tK"
    "Ixu5FfkdqGoGAcxqNVKWW49WIpPaiJaR0SqjINAXEnSgdsCKoIdlZYCdehNMlgBj5DIzZI1nyCcz/5bdyK6uNLKr1kxmhgxoJquU"
    "Zpr6xx658CA3YIbWWqFVM9mN5Y3lTVa1VQ/C3GJ2OWC/H+qBTX5v8N8gN801Bg9OY+HBfnFsP7W4TPrG/8+mJ4uIJMhd+vhqHDf8"
    "X+gTUOzXIdDLB8aXwf82MpP/G84CGV/DfmVPPac7zrGz8T3wGznC86WADslBhaWR12otf4cJrK9azczm3lF7u7AN/5VOH7cLZXzM"
    "+vD7eH17u1qobif/t/d49LBeGjUe97eXqqWbwoV35BV620sX2UrhstTe7hR/Dc8Lu+Wit9c5Lu8V937vjG+2d5e3nbMdpzA67JCe"
    "C8XtUue8vV8uDC9G48ugt3p9/NBu9JYG2br9e3v8eGR3zhr+7nh3e/Pq+uX5Z2tp6fhi7/jo+qW8/6vYP6nMd0Z71YPqz+reRTA/"
    "/rbuPQVrzZODw8vjg42w2fx1Nv/4bfNh5SG7fbQ92mvvDJ8f3MHR4Gx9/ffOcmu+unY5ON3eePau9sPHR9u9dqv7/stZMTwZzleH"
    "zWNnJdg8vbn0OtvepfNUms9mX5b3q7/9s05xtXxzeNA93q+fjM+vTw/Ka72X5W/uz5XC4e7OzmOw06/u/SqMfve8s6xTqY4v+o/e"
    "Zql+8rh2Oaw31/2z+bWb6lHj5anTtY+OV0/q+435/fmlld/+y/LNSum42N0dP/1+bFeL2ZNO9eayWbryMoPOobe6MRwFRyvz3vmK"
    "e1Z+2R311gmevOiXzi4q26OL593u/vbz48HRunflD479+vLe2lLp0n4eHA6bS+3lZ7+1uh8Wu4Vqd3u3slP69mKv+Cudxs1KuH76"
    "4q5cNpuPDy9nm2vzvfnqkV84GXc7pave0rfVgfutddp3r5dLx2uXN9ndwkr2+OH6er3VsFfWh0s3x863l43mxq/j88qvs3Hx6ldh"
    "73B3r1g/W8tuDpePfh4NeycnO6Nfw1/N7a69XbGzlUZn3jsod791TsvbjfLe+cPJwfbD2cX27vXxt6uDp72H8Gp0un220h5vL1df"
    "Vs92W9/czYuHwnrr/Ppyf7y0ej1qZ/ceL/Z7+yfF8ri8azd/Zcalo+Oj49JoeW1pLfPNPQ+b1WH9uV+t/3qsP85vnA4OHw+2R4fb"
    "B8eV4vbLzxOv4GfKpc3nlYem89z4FYzG9Yur4s+VQXNprfMwrhaflo4PyGIdN9oHK782ncLayvHT76WVsJpZOts4O/617TyddboH"
    "+4Xe+lnnZ6V6tP7crXfqP18Ohisb163n051t77xcuC7sH1b37Z3d7e724Xg02BmcbDdHg1H95PTi6de4dHn4uF4+fVy/vFnrnpeb"
    "Z2th9WGQPehenbqePx40DzqNy+L6U/bx4nKVnIPNTBg+rNyMLtx+6fKoULy5Xru4tg8bm6crP92lcaO/ezZ8Gj25Z4cbRxfjwvVl"
    "M3vZvbzu7BZIR722f1Ne7jcODudbS43et7XHc2d0sTF6yj7/XBm/9M6CJZ/s3+bJ/Pz85tJVt/fUKQ5+ktN2dPBr5+wgOC9dLY2e"
    "vW/ht8z4uHgx/9RqPe+0Dvc291a/VS9LnfXhS9HOZvaOKu3OTqm+eub/vjleme9822st3eytrfnd8XC53iuWnaPf452l09LS8LC8"
    "024dtXfBtX/0MDpttwpu4fGlsFnKftuwG+HwwcmGS/uN3YI3/rl69RI+HBW2KzvjUnl9dePqpl54Cve7z0vNwnrgluYflkcnT2ur"
    "g6P90ZlX2C6thX13ZXmjfrTfPqtvnzUru9fDl8Hl2sne7tX6Srl55Wz/qpSqp1fN8Xq7ceCelzsr5dEToZwyg836Zev893A1c1k+"
    "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"
    "fM7lEUlJcjniI+/CwHNnNfnjRCASGEqXnonLmrHgcn/8ZrK7QnyG9ttv8fFYIf6/3y5iNG6TGF3hDyCksxVD/AF+vR8jTC4yH+Vd"
    "ziBOHq4TNDBL2nMs6LOYswzjS4LN/lIAeCZ0G8q5a3qtM11oLAcOmD27uxzuXTXobpM7170fpGk8e/HuAk2jkw+xzX/8pTx4j0Ff"
    "9S3prJynoedVyMmfce8kPA+Noz7qib8nUSQPULnj5ThVzQsFjY8cz/EEGAllg1xvwpaPzsVk38Tgnkw8ddjV4F/fYk/QIQHUa5rp"
    "6UtbN+70eLHtcLZ7navvzjZNztKPV6/w91/QcS6W7QfP6vy3N7jwr0v+9uRR/DPRPl88qD+vTDzUyxsr16zssLRXV83ekiBq4ny3"
    "DJZypFkynSdpRl5K2ayA+Fyc3WXwv/125vC/5XHvG2XhYax97s2gexME+CGff8Xnkgee70wc1XoLSOF7acQeXY5MWsY7GezaJyyT"
    "KxuhgCAXNsqRjE4W0peAlaF8g+9ssWVwvvRjFm4Hk2OroNkxg5lQzQ8rVk+9/Y/veLZMFOQco/ixzRZLkwL+lSG8KT53batdGZJ/"
    "f59gssXrTnMPnC5cwNmZfb1XnDOc02Wcw3AOmxuD7vZxxu9Qt3xcNd3yPh7bVtn7F8R1iN77r943+aVsG88GMMajSkk5vUP9x8ed"
    "bi6TuVxpDycgSWj2BYyEgI+xTokVf/BM3d+I16lr31Lj//Ja37nnn+fguPjnm8vGDrqX0xWkC10jc7MvGzR3csdmINyEuCan2W+c"
    "6AWiaL7/3WpvrBf8emBlshNvr8GdNeH8+0CZ4f6Vw6DsmU+S3+W18CXOi+FXiCfbp3w6OUrQ5NiYKz4zowc3YeZmIYI9uvoYZ6j+"
    "gnaeUVau7ir++jrd3pM5L1359ubU/Tv756k6OtktPdc8iAte7rf5/Tf4t7uJkiwdftgUedQUedgUfdQUfdgUe9QUyzZNjIrs9euP"
    "v20pM70YsYD/nE18GvqYADu4HT6/C5LUTmJwPo+s+SQkJy/g5h4hZtrkn6tfC4nCFbZPJKHFoQzbf2ON5P5tPCvXl44vMg5cTU3a"
    "rJC9pXXvJDH3KCkBAmo4bI42cK/P/Oi4jO4eGzyXJde3as4W3p3I8QMlHyAkP+6l2U1L89PoHi6XAdv1KPgeXK858VfkEX+No1Gf"
    "SDl2wuoe303Kr4UqDN+/x49fXE2nwJa+5aY3zxHcv9qfIpAS8SHj/++JGn+695EsTf647uQlOA7jrD3eObDOdp46RSztj3urfZUm"
    "NW+9Tzk6L+vE+vDVffUTtCwicc6PLDKc7+7/eM1+sYFiBcZzyvt8g2Q2zehfxDAB9Qi9JLfrBXrpQedd5K4yvv5F/C6jd26XMvVv"
    "3cPlMgnsX0TlwkF2aQClDCS7pe9s0bjN6xXclMF8llsmZ+/mbdCLHZCdtMOx150Q+3zBkzaMD1N/ISvEe16WinvLqAqns/P8XtN9"
    "n6/jZw5rbwADTmzGppwpPwE+zUaWmFqf3Cw+MvJstNoX7xHf4ppwghssL8PUFVa3CsiDGPWruNG4v4+LwFDHijv7BsclL39e14/h"
    "x2GmN2od9GkukRt3xp+xXwj0fQMLP3oLj16wgPV45U7UYFL28lcNPPImz8kDyr2SY1mvW4LN32fxIZ9afCl3KBDXk5v4FdCToZfe"
    "8Hki/+lXkhGcnqL4gv8kN6FhZm6vfQMHpeO53Hz5fCoZ+0/VkPOSGTx0osb2TRyK/uVggE/99egTMceH3u/d5FaTdByifrqxTd6/"
    "sY0ip8OLA9S3Q46+vESIn6SuOpqoR0hxTslfus/+3OVNl30F/+S/B3NjGbhsmhJaYd1vmSQoLy9X5/NHgD/SZCRXhXaSgvbJO6hP"
    "39I/gn3Y589zSuPrC/dxFTBHmfy1qTsmE4qNXKTUS5okyTgLyf9/pIk5QaeW7wFDJBSF9+sODkcOB7Ihjl+BiDmmlUou7SUfwUY5"
    "fIRh4vxVlI51YYw8fLak//YTRplDpRgNSz8cJ/38nToER1xjh0BQHnYZ5SShxqwFcnWk82d2hg9ZW68ytWWOms9VnfjvFO9bMkgX"
    "4C+6N1Jy0oXCGWKu2zYDD39JmrEOaLgTsy1PZyll5Izhc44TUDtxQnyZg94MRxRU78kMOwh25aC8I9SucurdS2/3MMfn2bjM9Rwe"
    "EP96pMLFQzlZIvLSu79XuGffOnycii5nWDfxVQDrZJ/ES3QbLReXgp3/wDXwcCFB25/nDK/3oj4SwnGO12ue9eBkr+FcZf12d2/y"
    "8wkiMp6Y/EW7mPCb/D5PUtaReGJd7WamAL7J1rkX+Z/I/MurT3GbWF/JS/x4mWbluLLn5tSNa+8eR81ktsuwtiB59uxi8h9AwKF8"
    "CLfs8EAFt+ztQlKlYXLfXSF9AOHzNb58tA7/RB0DcFXhDiUCFgM95oHCJ/dm46jKX7rfgSbAE86Yr1c/ocm5QnLP5UHCzpupyDiI"
    "70blkafYlvSdy7uaMPz51LP8KVb0yp2LvRwr/MoladAyNnmfyqOA3IlEfKqHn5nH5lKSOageMbnq9sdV0qPD53w9UYjPZ+5HZ4Fy"
    "xweq3r3JP8wYUJLFO3OK3iXG/IuOAJrvxmncnj/WfZSsIhcn/Kk40E9PhT+XtJ8uZzLUTw854h19K1XBst5dF/xqU8TVP7d2AETV"
    "9Sxgxj0RSIa+vGSbPGkTCPEEgd1+ZR6LZvxQwIFy7zLAdNrSuj8vc4595AkwMPeGr3vqx8O4OeyTZQJFtso/GUCbeygBICQPqD1v"
    "1wLT6/EkuHlvq955FdW9eg/VFc/x0V9IjncIiPskGDIrpMWT0VQ+xOCdun4ikBxJHzMGTWxH3Kli8JH/nkdSJeG8z6e+ef8sKxAA"
    "6Yr8E29GfMolrvZYAvdLeX4OTWIvYPIOxRUHBwL844mAzhSOJ9qZl8jjqVVv3SBwWtmyvb9A8wDAY8mSLLv7S66e660QQ/p48r2N"
    "Q/VCwjv+4+3t2Guvx6c6h7ysGS/7bSSMa7zGd9VPdk/ewl2HSX1BjMTqfNbfcib9T3m3mLxd+/HrKW+xXyDlXC02Y+w80GLFTzM0"
    "vcLfYQR3RONZdTYl8S9pn+JbcJPQ4BCrIrrJqbEnXqRGS2y+65zbtp5k73rw2nWsartxQMteFy/9w+l0pBA+nk3ImryuceaW37HM"
    "ZR/i+vbPscIjr/cJi0CxXhNsRPfjgd722E2Ttr8I3LlNNJNU+2v5oE7ywBHB9Ki7nJfI0z4K6sety+/4kkkaZ36umrp84xjWb6z4"
    "yjrgf/wrx4N/tuorr3Gvwu5VYl9lXXtVxFfNfzUi89XcWq+2yb3a7qsrvPryq++87tWXl4/Y83EB/e8B/OEcE1YeAH9X2J34OBXG"
    "kcwuD91993fQXtQvwgLARyNW3uKEQfcBn4/LU8AX7V3FcuJrKfebn2TBcQimKArPnW9h19kt0oO3wxFX9tQLOeS2eD+5HYnrGwPx"
    "i/EnVwJx0FSOO/KZ/SedB3HaPJeZHkDx2TebiqP4U+F4bHLl4bmWmqc7Qo/f44tB/seyRfOPO8YY/HJ9LuXaubog+rfogol3N7nY"
    "8KSykw20TYza5NDp8CGxQoBY2Snxu+xouqjZvJRZlddO3uy60ulip5CnHLLyFTLYZXpBE63zPoX8/B2GidMJQAbeZzptOcOSk9tF"
    "r3hCN09hlTP2pOWh69x7gFjykkLqKfu4vFucmSZQeDFLl062eBLPA4ew08C9wPp5gO1+PLxihbxe0MxTRANAFI+YHyjnwun0SF++"
    "P4J/gxGg1HfqxlWY6a6QPC6Yc5p2i9FninviQD2kTn5W1d+BDp5VuzN6Vr6iu3szP+6ein52foOm6DzW4XfxSR6vnM73HqvO/5+0"
    "Zlt+M+LbIV9w8Xy6MABmHDT08fclsY1hXufcvUgJn16XAB1vLO4lS0HJED9uNB2PT6Sk+3Ev0//jjEp23ml47nCfi9A4iaxHXb5t"
    "P7LeIVtLX1rMML7UG35hul/nIj69xKglQ/5aNuIv3//Ji2r5G89w7np8YqXtZqzpQeDr7feL5xFfPslBCBp5Of6z29VKEoLk0gQo"
    "PhzN5hsNSXlyJ/EpW/Su+nHn2m6iKxzEyxXWdhyK+CsZeG89rgCW5Ou3aQzSwacu8GOMBUXEOZ7Bd01X4xR7//1xZ8k+dobfzIMN"
    "1FLRczNIEtAByUNR/Jpp4jBNn3W42JuAnAxLEN/0nOPApBQM58mcmUdiBY3SB3S/LO+eYe3/xU360B0VB79m3XTp/IOviX/myXOg"
    "X8uLfn/zHrr/DoYC9nAy9Y9uc1ynXkhUBE8BUyErCbDnj74/m6tTBvAk3uxz38IR83t8BpTneFKQZzwpJPko58+n3hPQ8x32AEpY"
    "V7s4q4slSRoNc/88/qknxR6cEcR9xE+JfxbOd9rgcuoV/TiysAOigbK/mykiqRBT1bOU/Ykj7ACtoKu/tIRfWbBHXgD8YOIdqelp"
    "L8BxXV+T+bzO93hmopeRDd/t3X/RDH/KmAUYuHHExFesWORkxQJbwNslz4K5T4/hUqbp+lGowdQ9YR738aVp+izLB/qVLB9x78Fp"
    "ii42eFIkilpezMDp5S/y/DxebgqIh0Mgr63oHNwAAh+379Rdgo391Pfe87r/Xh76OCIl7nz3mv47Tz94GEL2Z367JBf5bdqvuO5d"
    "p/HxCv7xmY1/Xry39/je9hOu5+T1nlgRyL21/+aIgJW7F89dHIMSsvdnrp+RvvVZH8b4U82+wYL85WvnSRKOB7cSkqTqh76/x9nc"
    "vphiIG7qinI20/p9eo+37FX8x8FrkUIpqB8P3km/Qfwyp3MKRQe43LwS/In4ObTLFz8PBMoZ97R1eq8mDml4MiA+tWVjANrXBn59"
    "A+r6llAK9EsqEXL/cCmOwH4sYrNvX+UxCv2u5pZIkK/mEM8kDc/dR95XCOlLycFTcfDxMBCQ+FXBlMQ+vNxl9crHA0FyEd4L6irP"
    "KeoXycIu7aQvxp/eeXU7RuZpIzFZu8xdg/OyEMiJqvk3AUzq0UxFkfP3ZOdlLxjEfSeBR39DvAGAZXxJysVOhjv9YrkPJz8RXyHo"
    "cvq0bBYRYMe/pQdB7uEZiN2bQFIkBovUH5/HEHBvrsN/2i5ZHi4OD8mvmt7d4N58R7+tkNpA169BJvV1C8zCM1h/aUslhs9TLhKA"
    "Qmy/5WBwnbbyHEETRMfqMC7CGISgn09zEBXs21ZZmPFNTPe2yp3LbFdPLydOglu5eoBaUG/hfoHlnl+1vb5pe4L/3TKf7CKjOoje"
    "F1hDWjmJoco/5kSOtR6kYXsQOpc2Tpw453eb09V5XpE4QIg1iceRrPfJ5Rij4iWhWOetJZ5SH/2V8CzvcHZ3YELpqsYCKAk9fE0e"
    "eckZVNzouxdY92xiySmAf851CznvcuU61T97zPL0NnSeInzQzAs32awTNBSRP5hmzz5Fc882ve9oPnf087RkZzFykBA3UcuHFM3n"
    "xoX04nzeS+8H719aW441uvynddMK8TXKy1saB6K05HsamOIZ+mt8DvX6P6xtf1w9cJ4Up9ErkfJGD44pGRJN4bc+azqWLf72Wvht"
    "BJBtgGqFKR3/7Ku8Y8VLWFixLVGNPw0sYH9OgSFSoDvdQ7Xzt/T31PIdXiy0WDPz1d27YO6AavNaeAMo6oA2ki+vhWp8uNBn+Wny"
    "uwFwimGIsiUWZu24JYAB7ApHldKoBEXU9asR7pTjw5ay+PM/jqWLvwPdIzmd+yO7INf+FIBIHL1yndQ57mVv8oXTBcs0J8JrUhBf"
    "is/J8ZyCihWf5B2V9AEvXmdd94+X//aNxyPC1xdC809yc4+PobycbdCff/6j9K//uwN4/t8f8L9K/y4lTPPnP/5dSp5P/ce/k4yp"
    "ySh//+2guv4GPgvqrqAKv/8GJuW3n/8ugZ9xm+ScNG4LqPHnP/4fGTm4OA=="
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
