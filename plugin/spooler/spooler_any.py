# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.22.2"
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
PLUGIN_VERSION = "0.22.2"
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
                "spool_columns": 1, "auto_send": True, "send_saved_copies": True}
    return config_view(defaults)  # The Spoolman address and source stay: they are yours.


def get_spools(spoolman_url: str) -> dict:
    """Return ``{"ok": True, "spools": [...]}`` or ``{"ok": False, "error": "..."}``."""
    path = "spool?allow_archived=true" if display_settings()["archived"] else "spool"
    try:
        data = _spoolman_open(spoolman_url, path)
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
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
    return [f"Spooler: {_spool_label(s)} is down to {s['remaining_weight']:.0f} g" for s in fresh]


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


def _spoolman_open(base: str, path: str, method: str = "GET", body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors."""
    data = None if body is None else json.dumps(body).encode("utf-8")
    request = urllib.request.Request(f"{base.rstrip('/')}/api/v1/{path}", data=data, method=method,
                                     headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8") or "null")


def clean_url(url: str | None) -> str:
    return (url or "").strip().rstrip("/")


def ping(spoolman_url: str) -> dict:
    """Ask Spoolman for its version, which doubles as a connection test.

    Returns ``{"ok": True, "version": "..."}`` or ``{"ok": False, "error": "..."}``.
    """
    if not spoolman_url:
        return {"ok": False, "error": "No Spoolman URL configured yet"}
    try:
        data = _spoolman_open(spoolman_url, "info")
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
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
    who = f"Signed in as {auth['user']}" if auth.get("user") else "Signed in"
    return f"{who} ({BAMBU_REGIONS.get(auth.get('region'), 'Global')})"


def read_auth() -> dict:
    """Sign-in result: ``{"ok": True, token, ...}`` or ``{"ok": False, "error", ...}``."""
    try:
        data = json.loads(AUTH_FILE.read_text(encoding="utf-8"))
        token = data["access_token"]
    except FileNotFoundError:
        return {"ok": False, "account": "Signed out", "signin": True, "error": "Signed out"}
    except (OSError, ValueError, KeyError, TypeError):
        log.exception("Could not read %s", AUTH_FILE)
        return {"ok": False, "account": "Signed out", "signin": True,
                "error": "Your saved Bambu sign-in is unreadable"}
    auth = {"token": token, "region": parse_region(data.get("region")),
            "user": str(data.get("account") or "")}
    auth["account"] = account_text(auth)
    expiry = jwt_expiry(token)
    if expiry is not None and expiry < time.time():
        return {**auth, "ok": False, "account": "Sign-in expired", "signin": True,
                "error": "Your Bambu sign-in has expired"}
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
    return "Bambu blocked the request (HTTP 403)" if code == 403 else f"Bambu Cloud returned an error (HTTP {code})"


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
        raise BambuError(f"Could not reach Bambu Cloud ({exc.reason})") from None
    try:
        data = json.loads(raw) if raw.strip() else {}
    except ValueError:
        raise BambuError("Bambu Cloud sent a reply Spooler doesn't understand") from None
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
        AUTH_FILE.write_text(json.dumps({"access_token": token, "region": region, "account": account}),
                             encoding="utf-8")
        try:
            os.chmod(AUTH_FILE, 0o600)
        except OSError:
            pass
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
    raise BambuError("Bambu Cloud didn't sign you in")


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
                raise BambuError("Enter your Bambu email and password")
            reply, cookies = _bambu_post(region, LOGIN_PATH, {"account": account, "password": password})
            return _after_login(region, account, reply, cookies)
        if not _pending:
            raise BambuError("Your sign-in timed out. Enter your email and password again")
        region, account = _pending["region"], _pending["account"]
        if action == "resend":
            _send_code(region, account)
            return {"ok": True, "step": "code"}
        code = str(data.get("code") or "").strip()
        if not code:
            raise BambuError("Enter your Bambu Lab verification code")
        if action == "tfa":
            reply, cookies = _bambu_post(region, "/api/sign-in/tfa",
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
        raise ValueError("Bambu Cloud sent a reply Spooler doesn't understand")
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
            f"slot {item['slotId']}" if item.get("slotId") not in (None, "") else "",
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
            return {"ok": False, "error": "Bambu Cloud didn't accept your sign-in",
                    "account": auth["account"], "signin": True}
        return {"ok": False, "error": f"Bambu Cloud returned an error (HTTP {exc.code})",
                "account": auth["account"]}
    except urllib.error.URLError as exc:
        return {"ok": False, "error": f"Could not reach Bambu Cloud ({exc.reason})",
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
        error = f"{result['error']}. {SIGN_IN}" if result.get("signin") else result["error"]
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
    raise last or RuntimeError("No OrcaSlicer user folder accepted the presets")


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
            publish_stock(origin[0], [], result.get("error") or "Spoolman could not be read", wants["request"])


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
                raise RuntimeError("OrcaSlicer's data folder was not found")
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
    return {"ok": False, "error": "The spool source kept changing while loading; refresh to try again."}


def start_preset_sync(post) -> None:
    """Sync Presets: read Spoolman now and rebuild every Spooler filament preset, even when nothing
    changed. Call it on the UI thread; post() gets {"type": "sent", "ok": ..., "text": ...}."""
    if source() != "spoolman":
        post({"type": "sent", "ok": False, "text": "Syncing presets needs Spoolman as the source."})
        return
    snapshot = refresh_snapshot()
    if snapshot is None:
        post({"type": "sent", "ok": False, "text": "Could not read OrcaSlicer's presets."})
        return

    def worker():
        result = fresh_spools(snapshot, force=True)
        state = result.get("profiles") or {}
        if not result.get("ok"):
            ok, text = False, result.get("error") or "Could not read Spoolman."
        elif state.get("error"):
            ok, text = False, "The filament presets were not rebuilt: " + state["error"]
        else:
            ok, text = True, f"Synced {state.get('count', 0)} filament presets from Spoolman."
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
        super().__init__("The spool source changed in Settings while this ran, so Spooler stopped "
                         "before writing anything more. Try again.")


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
        raise NotSent("Spoolman is not the spool source.")
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
        raise RuntimeError("Open a Spooler preset in OrcaSlicer's filament settings and change it first.")
    name = edited.name[len(PROFILE_PREFIX):]
    changes = {key: (edited.config_value(key), saved.config_value(key)) for key in edited.config_keys()
               if edited.config_value(key) != saved.config_value(key)}
    if not changes:
        raise RuntimeError(f"{name} has no unsaved changes to send.")
    return name, changes


# Spoolman versions whose behaviour a write depends on, read from Spoolman's own source:
# from 0.26.0 a PATCH's extra map is merged key by key (before, it replaced the whole map), and
# since at least 0.18.0 PUT spool/<id>/use adds use_weight to used_weight in one SQL UPDATE,
# clamped at 0, whatever its sign.
SPOOLMAN_EXTRA_MERGE = (0, 26, 0)
SPOOLMAN_ATOMIC_USE = (0, 18, 0)
_versions: dict = {}


def spoolman_version() -> tuple | None:
    """The pinned (or configured) Spoolman's version as (major, minor, patch); None when it can't
    be read. Cached per address and source generation."""
    pinned = getattr(_op, "origin", None) or current_origin()
    if pinned in _versions:
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


def spoolman_at_least(minimum: tuple) -> bool:
    version = spoolman_version()
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
        raise RuntimeError(f"{name} is no longer a Spooler preset. Refresh, then send it again.")
    filament = spoolman_call("GET", f"filament/{int(fid)}")
    base = orca_settings_data(filament)
    data = orca_settings_data(filament)
    if data is None:  # Never overwrite what can't be read back.
        raise RuntimeError(f"The {ORCA_SETTINGS_FIELD} field of {name}'s filament isn't a JSON object; "
                           "fix it in Spoolman, then send again.")
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
            raise RuntimeError(f"The {ORCA_SETTINGS_FIELD} field of {name}'s filament changed in Spoolman "
                               "and isn't a JSON object now; fix it in Spoolman, then send again.")
        data, clashes = merge_settings(base, data, remote, target)
        for key in clashes:
            if key in sent:
                sent.remove(key)
                kept.append(key)
                native.pop(NATIVE_KEYS.get(key), None)
                patch.pop(NATIVE_KEYS.get(key), None)
        kept.sort()
        value = json.dumps(json.dumps(data))
        if spoolman_at_least(SPOOLMAN_EXTRA_MERGE):
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
        notes.append(f"Sent {', '.join(sent)} to Spoolman for {name}.")
    if kept:
        notes.append(f"Kept Spoolman's newer value for {', '.join(kept)}: the preset now has it, and your "
                     "change stays unsaved; send again to use yours, or discard it.")
    if other:
        notes.append(f"Not sent: {', '.join(other)}. Spoolman's {ORCA_SETTINGS_FIELD} field holds only "
                     "calibration settings; colour, vendor, material and name come from its own fields.")
    if rebuild_error:
        notes.append(f"The presets were not rebuilt: {rebuild_error}")
    return " ".join(notes)


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
            push_notice("info" if result.get("ok") else "warning", f"Spooler: {result.get('text')}")

        start_send(done, edits)
    except Exception:
        log.exception("Could not send the saved copy %s to Spoolman", name)


def start_send(post, edits: tuple | None = None, auto: bool = False) -> None:
    """Send the unsaved changes of the Spooler preset open in OrcaSlicer to Spoolman. Call it on the
    UI thread; post() gets {"type": "sent", "ok": ..., "text": ...} when it is done."""
    try:
        if _auto["busy"]:
            raise RuntimeError("Already sending to Spoolman; try again in a moment.")
        if source() != "spoolman":
            raise RuntimeError("Sending needs Spoolman as the source.")
        snapshot = refresh_snapshot()
        if snapshot is None:
            raise RuntimeError("Could not read OrcaSlicer's presets.")
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


PRINTER_SLOTS = {"ams": 4, "ht": 1, "ext": 1}


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
        ip = str(item.get("ip") or "").strip()[:64]
        serial = re.sub(r"[^A-Za-z0-9]", "", str(item.get("serial") or ""))[:32]
        printers.append({"id": str(item.get("id") or f"p{len(printers) + 1}")[:32], "name": name, "units": units,
                         "ip": ip if re.fullmatch(r"[A-Za-z0-9.\-]+", ip) else "", "serial": serial})
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


def printer_state() -> dict:
    codes = read_codes()
    printers = [dict(p, has_code=p.get("kind") == "moonraker" or bool(codes.get(_code_key(p["id"]))))
                for p in printers_cfg() if _live["links"].get(p["id"]) != "none"]
    live = any(p["ip"] and p["has_code"] for p in printers)
    return {"printers": printers, "live_ok": live, "usage": usage_state(), "progress": progress_settings(),
            "stats": stats_settings()}


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
    sock.sendall((f"GET {parts.path or '/'} HTTP/1.1\r\nHost: {parts.netloc.rpartition('@')[2]}\r\n"
                  "Upgrade: websocket\r\nConnection: Upgrade\r\n"
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
            "layers": num("total_layer_num"), "name": name[:80], "stage": STAGES.get(_int(p.get("stg_cur"))),
            "tray": tray, "took": round((end - start) / 60) if end and start and end > start else None,
            "end": end}


def live_snapshot() -> dict:
    with _live_lock:
        printers = []
        for dev_id, state in _live["printers"].items():
            units = []
            for unit_id in sorted(state["units"]):
                slots = state["units"][unit_id]
                size = 1 if unit_id >= 128 else 4
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
    code = re.sub(r"\s", "", str(code or ""))[:32]
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
    _live["links"].pop(pid, None)


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
        run = _moon_run if link.get("kind") == "moonraker" else _local_run
        thread = threading.Thread(target=run, args=(pid, link, stop), daemon=True)
        _local[pid] = {"link": link, "stop": stop, "thread": thread}
        thread.start()
    bambu = any(link.get("kind") != "moonraker" for link in wanted.values())
    _live["keep"] = bambu and usage_mode() != "off" and source() == "spoolman"
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
    return snapshot


def _moon_get(base: str, path: str) -> dict:
    with urllib.request.urlopen(base + path, timeout=TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("result") or {} if isinstance(data, dict) else {}


def _moon_post(base: str, path: str, body: dict) -> dict:
    req = urllib.request.Request(base + path, data=json.dumps(body).encode("utf-8"), method="POST",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("result") or {} if isinstance(data, dict) else {}


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


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect").get("status") or {}
    active = lanes = None
    # Moonraker answers {} for an object the printer doesn't have (only the U1 has this one).
    if not status.get("print_task_config"):
        lanes = moon_lanes(base)
        if not lanes:
            try:
                active = _moon_get(base, "/server/spoolman/spool_id").get("spool_id")
            except urllib.error.HTTPError:
                active = None  # Moonraker without its Spoolman integration
    return moon_report(status, active, _spool_cache["spools"] or [], target_for_host(base), lanes)


def moon_mark(pid: str, doc: dict, heads: bool) -> None:
    """Note what a Moonraker poll found: toolheads (U1), and whether the card is the single-extruder
    one fed by Moonraker's active spool, the only kind whose spool Spooler may change. Call it
    with _live_lock held."""
    if pid in _live["printers"]:
        _live["printers"][pid]["heads"] = heads
        _live["printers"][pid]["spool_set"] = "vt_tray" in doc["print"]


def moon_set_spool(pid: object, spool_id: object) -> dict:
    """Set the spool Moonraker books a single-extruder printer's usage to, or clear it (None).
    Refused for the Snapmaker U1 (u1control binds its toolheads through Spoolman locations) and
    for AFC / Happy Hare lanes (they manage their own spools), checked here against the printer
    itself, not only hidden on the page."""
    if source() != "spoolman":
        return {"ok": False, "text": "Setting a printer's spool needs Spoolman as the spool source."}
    if spool_id is not None:
        number = spool_id if isinstance(spool_id, int) and not isinstance(spool_id, bool) else -1
        if number <= 0 or _spool_by_id(number, _spool_cache["spools"] or []) is None:
            return {"ok": False, "text": "That spool isn't in Spoolman, or it is archived."}
    entry = _local.get(str(pid))
    link = entry["link"] if entry else None
    with _live_lock:
        state = _live["printers"].get(str(pid)) or {}
        single = bool(state.get("spool_set"))
    if not link or link.get("kind") != "moonraker" or not single:
        return {"ok": False, "text": "Spooler can only set the spool on a single-extruder Klipper printer."}
    base = link["ip"]
    try:
        doc, heads = moon_poll(base)  # read again: the printer decides, not the page
        if heads or "vt_tray" not in doc["print"]:
            with _live_lock:
                moon_mark(str(pid), doc, heads)
            return {"ok": False, "text": f"{link['name']} manages its own spools; Spooler only reads them."}
        # Body per https://moonraker.readthedocs.io/en/latest/external_api/integrations/#set-active-spool
        # {"spool_id": <id>} sets the active spool; {"spool_id": null} clears it and stops tracking.
        _moon_post(base, "/server/spoolman/spool_id", {"spool_id": spool_id})
        doc, heads = moon_poll(base)
    except (urllib.error.URLError, OSError, ValueError) as exc:
        log.warning("Could not set the spool on %s: %s", link["name"], exc)
        return {"ok": False, "text": f"Could not set the spool on {link['name']}: {exc}"}
    live_apply(str(pid), link["name"], doc, link=str(pid), full=True)
    with _live_lock:
        moon_mark(str(pid), doc, heads)
    if spool_id is None:
        return {"ok": True, "text": f"{link['name']}: no active spool, Moonraker stopped booking usage."}
    return {"ok": True, "text": f"{link['name']} now books its usage to spool #{spool_id}."}


def start_moon_spool(data: object, post) -> None:
    """Run moon_set_spool off the UI thread, then post the result and the refreshed live state."""
    data = data if isinstance(data, dict) else {}

    def work():
        result = {"ok": False, "text": STALE_LIST} if data.get("spool") is not None and stale_list(data) \
            else moon_set_spool(data.get("id"), data.get("spool"))
        post({"type": "moon_spool", "id": data.get("id"), **result})
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
    url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
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
            path.write_text(text if text.endswith("\n") else text + "\n", encoding="utf-8")
            os.chmod(path, 0o600)
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
    while _live_active() and not stop.is_set():
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
        stop.wait(MOON_POLL if not fails else LIVE_RETRY[min(fails - 1, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


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
                row.update(state="unknown", error=row.get("error") or UNKNOWN_TEXT)
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
    # Only Bambu Live Link prints are booked here. Printers found from a preset's host address
    # ("auto-..." ids: Moonraker, Anycubic) are not: on the Snapmaker U1 the u1control plugin
    # books each toolhead's use to Spoolman, and Moonraker's own Spoolman integration books
    # other Klipper printers, so booking them here too would count the filament twice.
    if str(dev_id).startswith("auto-"):
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
                            "trays": _loaded(state), "pct": pct, "late": not new}
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


def _try_fetch(dev_id: str, job: dict) -> list[dict] | None:
    link = (_local.get(dev_id) or {}).get("link")
    if not link:
        return None
    try:
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
    return " ".join(part for part in (vendor, filament.get("name") or f"Spool {spool.get('id')}") if part)


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
    if usage_mode() == "auto" and run["result"] == "finished" and not late:
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
        return f"Spoolman refused it (HTTP {exc.code})"
    if isinstance(exc, urllib.error.URLError):
        return f"Could not reach Spoolman ({exc.reason})"
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
SPOOL_ACTIONS = ("weigh", "use", "archive", "unarchive", "move", "add", "open", "dried", "clear_dried")
MAX_GRAMS = 100000.0
LOCATION_MAX = 64  # Spoolman's own limit


def _action_grams(value: object) -> float | None:
    """A positive, finite gram count up to MAX_GRAMS, from a number or numeric text; else None."""
    if isinstance(value, bool) or not isinstance(value, (int, float, str)):
        return None
    try:
        grams = float(value)
    except ValueError:
        return None
    return grams if math.isfinite(grams) and 0 < grams <= MAX_GRAMS else None


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
    version = spoolman_version()
    if version is None:
        return DRIED_NO_VERSION
    if version >= SPOOLMAN_EXTRA_MERGE:
        return {DRIED_FIELD: value}
    spool = spoolman_call("GET", f"spool/{sid}")
    extra = spool.get("extra") if isinstance(spool, dict) else None
    if not isinstance(extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in extra.items()):
        return DRIED_NO_EXTRA
    kept = {k: v for k, v in extra.items() if k != DRIED_FIELD}
    return {**kept, DRIED_FIELD: value} if value is not None else kept


def _spool_write(action: str, sid: int, data: dict) -> dict:
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    if action in ("weigh", "use"):
        grams = _action_grams(data.get("grams"))
        if grams is None:
            return no(f"Enter a weight between 0 and {MAX_GRAMS:,.0f} g.")
        if action == "use":
            spoolman_use(sid, grams)
            return {"ok": True, "text": f"Used {grams:,.1f} g of spool #{sid}."}
        spoolman_call("PUT", f"spool/{sid}/measure", {"weight": round(grams, 1)})
        return {"ok": True, "text": f"Spool #{sid} set from a scale weight of {grams:,.1f} g."}
    if action in ("archive", "unarchive"):
        spoolman_call("PATCH", f"spool/{sid}", {"archived": action == "archive"})
        return {"ok": True, "text": f"Spool #{sid} {action}d."}
    if action == "move":
        location = data.get("location")
        if not isinstance(location, str) or len(location.strip()) > LOCATION_MAX:
            return no(f"A location is text of at most {LOCATION_MAX} characters.")
        location = " ".join(location.split())
        spoolman_call("PATCH", f"spool/{sid}", {"location": location or None})
        return {"ok": True, "text": f"Spool #{sid} moved to {location}." if location else f"Spool #{sid} has no location now."}
    if action in ("dried", "clear_dried"):
        ensure_fields()
        value = json.dumps(f"{today().isoformat()}T00:00:00+00:00") if action == "dried" else None
        extra = _dried_extra(sid, value)
        if isinstance(extra, str):
            return no(extra)
        spoolman_call("PATCH", f"spool/{sid}", {"extra": extra})
        return {"ok": True, "text": f"Spool #{sid} marked as dried today." if action == "dried"
                else f"Spool #{sid} has no dried date now."}
    if action == "add":
        fid = _pos_int(data.get("filament"))
        if fid is None:
            return no("That spool has no filament to copy.")
        made = spoolman_call("POST", "spool", {"filament_id": fid}) or {}
        return {"ok": True, "text": f"Added spool #{made.get('id', '?')} of the same filament."}
    url = getattr(_op, "origin", None)[0] if getattr(_op, "origin", None) else clean_url(get_settings().get("spoolman_url"))
    if open_url(f"{url}/spool/show/{sid}"):
        return {"ok": True, "text": f"Opened spool #{sid} in Spoolman."}
    return no(f"Could not open {url}/spool/show/{sid}.")


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
        return {"ok": False, "text": "Unknown spool action."}
    if source() != "spoolman":
        return {"ok": False, "text": "Spool actions need Spoolman as the source."}
    sid = _pos_int(data.get("id"))
    if sid is None and action != "locations":
        return {"ok": False, "text": "No spool chosen."}
    if action != "locations" and stale_list(data):
        return {"ok": False, "text": STALE_LIST}
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
        return {"ok": False, "text": _spoolman_error(exc) + (f": {detail}" if isinstance(detail, str) and detail else "")}


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
            row.update(state="unknown", error=f"{UNKNOWN_TEXT} ({_spoolman_error(exc)})")
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
                return ORIGIN_TEXT
            for row in entry["rows"]:
                if row["state"] in ("booked", "unknown", "sending"):
                    continue
                pick = wanted.get(row["slot"], {})
                spool = _int(pick.get("spool")) if pick.get("spool") not in (None, "") else row["spool"]
                try:
                    grams = float(pick["grams"]) if "grams" in pick else row["grams"]
                except (TypeError, ValueError):
                    grams = 0.0
                if spool in (None, -1) or not (math.isfinite(grams) and 0 < grams <= 5000):
                    continue
                row.update(spool=spool, grams=round(grams, 1))
                if not _send_row(data, row, "book", lambda: spoolman_use(spool, grams)):
                    continue
                label = _spool_label(by_id[spool]) if spool in by_id else row.get("label") or f"spool {spool}"
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
        return "Spoolman has the change, but Spooler could not update its history file."
    return ""


def usage_undo(entry_id: str) -> str:
    """Add a booked print's grams back to its spools. Returns a notice, "" when there is none."""
    with pinned_origin() as origin:
        with _usage_lock:
            entry = next((e for e in usage_load()["prints"] if e.get("id") == entry_id), None)
        if entry is None or entry.get("state") != "booked":
            return ""
        if entry.get("origin") != origin[0]:
            return ORIGIN_TEXT
        if not spoolman_at_least(SPOOLMAN_ATOMIC_USE):
            return ("Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use "
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
            notice = STALE_LIST
        elif kind == "usage_book":
            notice = usage_book(str(data.get("run") or ""), data.get("rows"))
        elif kind == "usage_undo":
            notice = usage_undo(str(data.get("run") or ""))
        elif kind == "usage_resolve":
            notice = usage_resolve(str(data.get("run") or ""), data.get("slot"), data.get("outcome"))
    except OSError:
        log.exception("Could not write %s", USAGE_FILE)
        notice = (f"Spooler could not save its booking state ({USAGE_FILE.name}), so it stopped. Rows it "
                  "was sending are marked for you to check in Spoolman.")
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
        if row["state"] != "booked":
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
                     "pct": entry.get("pct"), "rows": rows})
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
    """Grams per week each spool used over the last 4 weeks, by spool id."""
    rate: dict = {}
    for e in hist:
        if (e.get("time") or 0) >= now - 28 * 86400:
            for r in e["rows"]:
                rate[r["spool"]] = rate.get(r["spool"], 0) + r["grams"] / 4
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
        hist = hist_load()
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
        hist = [e for e in hist_load() if (e.get("time") or 0) >= start]
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
        return {"ok": False, "text": f"Could not write the export: {exc}"}
    open_url(folder.as_uri())
    return {"ok": True, "text": f"Saved {path}", "path": str(path)}


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
        hist = hist_load()
    now = time.time()
    lt = time.localtime(now)
    sel = [e for e in hist if (e.get("time") or 0) >= period_start(period, now)]
    total = sum(r["grams"] for e in sel for r in e["rows"])
    costs = [r["cost"] for e in sel for r in e["rows"] if isinstance(r.get("cost"), (int, float))]
    mats: dict = {}
    top: dict = {}
    for e in sel:
        for r in e["rows"]:
            m = (r.get("material") or "Other").strip() or "Other"
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
        m = (str((sp.get("filament") or {}).get("material") or "").strip()) or "Other"
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
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            error = "No published release found yet"
        else:
            error = f"GitHub returned HTTP {exc.code}"
    except urllib.error.URLError as exc:
        error = f"Could not reach GitHub ({exc.reason})"
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
        message = f"No web browser could be launched. Open this address yourself:\n{url}"
    except Exception as exc:
        log.exception("Could not open the browser")
        message = f"Could not open the browser: {exc}"
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
    return f"{grams / 1000:.2f} kg" if grams >= 1000 else f"{grams:.1f} g"


def _join(items: list[str]) -> str:
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def slot_label(result: dict) -> str:
    slot, numbers = result["slot"], result["slots"]
    preset = slot["preset"].split("@")[0].strip()
    named = preset or " ".join(part for part in (slot["vendor"], slot["material"]) if part)
    name = result.get("name") or " ".join(part for part in (named, slot["colour"]) if part)
    which = "slot " if len(numbers) == 1 else "slots "
    return f"{which}{_join([str(n) for n in numbers])} ({name})"


def _sentence(text: str) -> str:
    return text[:1].upper() + text[1:] + "."


def _need(result: dict) -> str:
    grams = fmt_grams(result["need"])
    if len(result["slots"]) == 1:
        return f"needs {grams} of filament"
    return f"need {grams} of filament together"


def _supply(result: dict) -> str:
    count, have = min(result["pool"], result["matches"]), fmt_grams(result["have"])
    if count == 1:
        return f"the spool has {have}"
    return f"the {count} spools have {have} between them"


def _tracked(result: dict) -> str:
    if result["matches"] >= result["pool"]:
        return ""
    return f" (only {result['matches']} of {result['pool']} matching spools are in {source_name()})"


def plate_notice(results: list[dict], cost: str = "") -> tuple[str, str] | None:
    """The one notification for a slice: ``("warning" | "info", text)``."""
    label, grams = slot_label, fmt_grams
    where = " in the AMS" if any(r["ams"] for r in results) else ""
    short = [r for r in results if r["status"] == "short"]
    mixed = [r for r in results if r["status"] == "mixed"]
    barely = [r for r in results if r["status"] == "barely"]

    def short_part(r: dict) -> str:
        text = _sentence(f"{label(r)} {_need(r)} but {_supply(r)}{_tracked(r)}")
        swap = r.get("swap")
        if swap:
            where = f"{swap['location']}, " if swap.get("location") else ""
            text += f" Swap in spool #{swap['id']} ({where}{swap['remaining_weight']:.0f} g)."
        return text

    def mixed_part(r: dict, prefix: str = "") -> str:
        count = min(r["pool"], r["matches"])
        if count == 1:
            body = (f"of {r['matches']} matching spools the fullest has {grams(r['have'])} and "
                    f"the smallest has {grams(r['worst'])}, so make sure the right one is loaded")
        else:
            body = (f"the {count} fullest of {r['matches']} matching spools hold "
                    f"{grams(r['have'])} and the {count} smallest hold {grams(r['worst'])}, "
                    "so make sure the right ones are loaded")
        return _sentence(f"{prefix}{label(r)} {_need(r)}; {body}")

    def barely_part(r: dict, prefix: str = "") -> str:
        return _sentence(f"{prefix}{label(r)} {_need(r)} ({grams(r['padded'])} with the "
                         f"{r['margin']}% margin) and {_supply(r)}{_tracked(r)}")

    if short:
        kind, parts = "warning", [f"not enough filament loaded{where}."]
        parts += [short_part(r) for r in short]
        parts += [mixed_part(r, "also check: ") for r in mixed]
        parts += [barely_part(r, "also barely enough: ") for r in barely]
    elif mixed:
        kind, parts = "warning", [f"not enough filament may be loaded{where}."]
        parts += [mixed_part(r) for r in mixed]
        parts += [barely_part(r, "also barely enough: ") for r in barely]
    elif barely:
        kind, parts = "warning", ["barely enough filament."] + [barely_part(r) for r in barely]
    else:
        kind, parts = "info", []
        fine = [r for r in results if r["status"] == "ok"]
        unknown = [r for r in results if r["status"] == "unknown"]
        if len(fine) > 3:
            numbers = sorted(n for r in fine for n in r["slots"])
            parts.append(f"quantity OK for slots {_join([str(n) for n in numbers])}.")
        elif fine:
            parts.append("quantity OK.")
            parts += [_sentence(f"{label(r)} {_need(r)}, {_supply(r)}") for r in fine]
        if unknown:
            many = sum(len(r["slots"]) for r in unknown) > 1
            outcome = "so they weren't checked" if many else "so it wasn't checked"
            names = _join([label(r) for r in unknown])
            sentence = _sentence(f"no spool found for {names}, {outcome}")
            parts.append(sentence if parts else sentence[:1].lower() + sentence[1:])
        if not parts:
            return None
    parts += [dry_part(r) for r in results if r.get("dry")]  # after the stock sentences, before the cost
    if cost:
        parts.append(cost)  # last, so fit_text drops it first
    return kind, "Spooler: " + " ".join(parts)


def dry_part(r: dict) -> str:
    slot = r["slot"]
    name = r.get("name") or " ".join(p for p in (slot["preset"].split("@")[0].strip() or slot["material"], slot["colour"]) if p)
    which = f"slot {r['slots'][0]}" if len(r["slots"]) == 1 else f"slots {_join([str(n) for n in r['slots']])}"
    days = r["dry"]["days"]
    if days is None:
        return f"{name} ({which}) has no drying date."
    return f"{name} ({which}) was last dried {days} day{'' if days == 1 else 's'} ago."


def cost_sentence(results: list[dict], code: str) -> str:
    """"About €1.23 of filament." from the matched spools' prices, or "" when none is known."""
    costs = [r["cost"] for r in results if isinstance(r.get("cost"), (int, float))]
    if not costs:
        return ""
    return f"About {CUR_SIGNS.get(code, code + ' ')}{sum(costs):.2f} of filament."


def fit_text(text: str, limit: int = NOTICE_MAX) -> str:
    """Whole sentences only: what doesn't fit is dropped and counted, never cut mid-sentence."""
    if len(text) <= limit:
        return text
    sentences = re.split(r"(?<=\.) ", text)
    for keep in range(len(sentences) - 1, 0, -1):
        note = f" (+{len(sentences) - keep} more, see the log)"
        shown = " ".join(sentences[:keep])
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
            headline, detail = "Not checked", f"no spool found for {'these slots' if many else 'this slot'}"
        else:
            headline = {"ok": "Quantity OK", "barely": "Barely enough", "short": "Not enough",
                        "mixed": "Check the spool" + ("s" if count > 1 else "")}[status]
            if status == "mixed":
                detail = f"{need} needed \u00b7 matching spools hold {fmt_grams(r['worst'])} to {fmt_grams(have)}"
            elif count > 1:
                detail = f"{need} needed \u00b7 {fmt_grams(have)} across {count} spools"
            elif status == "ok" and r["matches"] == 1:
                detail = f"{need} needed \u00b7 leaves {fmt_grams(have - r['need'])}"
            elif status == "ok":
                detail = f"{need} needed \u00b7 every matching spool has at least {fmt_grams(r['worst'])}"
            else:
                detail = f"{need} needed \u00b7 {fmt_grams(have)} left"
        rows.append({
            "slots": ("Slots " if many else "Slot ") + " + ".join(str(n) for n in numbers),
            "first": min(numbers), "name": name,
            "meta": " \u00b7 ".join(p for p in (slot["vendor"], f"{len(numbers)} slots, pooled" if many else "") if p),
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
        return ("info", "Spooler: no Spoolman address is set up yet, "
                        "so the filament quantity wasn't checked."), None
    if spools is None:
        return ("info", f"Spooler: couldn't reach {source_name()}, "
                        "so the filament quantity wasn't checked."), None
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

# White line-art tab icon: the Spooler symbol (spool rim flowing into an arrow). get_icon() must return the
# path of an image file; SVG markup or a data: URI shows no icon.
TAB_ICON_SVG = (
    '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" '
    'fill="none" stroke="#FFFFFF" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">'
    '<path d="M18.05 10.43A7.5 7.5 0 1 1 11 5.5H21"/>'
    '<path d="M18.5 3L21 5.5L18.5 8"/>'
    '<circle cx="11" cy="13" r="2.75"/>'
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
UI_LANGUAGES = ("auto", "en", "pt-BR")


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
    """The page's language choice ("auto", "en", "pt-BR"); anything else is ignored."""
    if value in UI_LANGUAGES:
        save_settings({**get_settings(), "ui_language": value})


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
        "wizard": bool(wizard), "log_path": str(LOG_FILE),
    }


def page_html(mode: str, view: str = "main", settings: dict | None = None) -> str:
    """The page for one surface: "tab" (spool views + Settings), "main" (spool window) or "settings" (window)."""
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
            f"Could not write settings to {SETTINGS_FILE}. Check that this folder is writable.",
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
            title=f"{PLUGIN_NAME} - Settings & About",
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
                        "error": "Test the connection successfully before saving.",
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
            self._panel.post({"type": "live", "live": live_poll(), "usage": usage_state()})
        elif msg_type == "printer_code":
            save_printer_code(data.get("id"), data.get("code"))
        elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
            spawn(lambda: self._panel.post({"type": "usage", "usage": usage_action(data)}), name="spooler-usage")
        elif msg_type == "stats":
            spawn(lambda: self._panel.post({"type": "stats", "stats": stats_data(data.get("period"))}), name="spooler-stats")
        elif msg_type == "stats_export":
            spawn(lambda: self._panel.post({"type": "stats_export", **export_history(data.get("period"))}), name="spooler-export")
        elif msg_type == "spool_detail":
            spawn(lambda: self._panel.post({"type": "spool_detail", "detail": spool_detail(data.get("id"))}), name="spooler-detail")
        elif msg_type == "send":
            start_send(self._panel.post)
        elif msg_type == "sync_presets":
            start_preset_sync(self._panel.post)
        elif msg_type == "spool_action":
            start_spool_action(data, self._panel.post)
        elif msg_type == "moon_spool":
            start_moon_spool(data, self._panel.post)
        elif msg_type == "tick":
            auto_send(self._panel.post)
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
                "error": "No Spoolman URL configured yet - click Settings to set one.",
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
                result = {"ok": False, "error": f"Could not read the spool list: {exc}"}
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
        return orca.ExecutionResult.success(f"Opened {PLUGIN_NAME}")



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
                    self.post_message({"type": "live", "live": live_poll(), "usage": usage_state()})
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
                    "error": "No Spoolman URL configured yet - click Settings to set one.",
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
                    result = {"ok": False, "error": f"Could not read the spool list: {exc}"}
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
                f"Could not write settings to {SETTINGS_FILE}. Check that this folder is writable.",
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
                        "error": "Test the connection successfully before saving.",
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
        raise RuntimeError(f"Open the {PLUGIN_NAME} tab once, then run this again.")
    if not snap.get("host"):
        raise RuntimeError("The selected printer preset has no host address.")
    with pinned_origin() as origin:
        result = get_spools("" if origin[0] == BAMBU_KEY else origin[0])
        if not result["ok"]:
            raise RuntimeError(result["error"])
        state = profile_sync(result["spools"], snap)
    if state["error"]:
        raise RuntimeError("The filament presets could not be updated: " + state["error"])
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
    text = (f"Loaded {done} filament slot(s) from the printer. OrcaSlicer doesn't let plugins set slot "
            "colours, so a slot keeps its old colour until you pick its filament in the dropdown.")
    if missing:
        text += " No Spoolman filament matched slot(s) " + ", ".join(map(str, missing)) + "."
    if failed:
        text += " Could not change slot(s) " + ", ".join(map(str, failed)) + "."
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


_keep: dict = {"run": None}
_keep_lock = threading.Lock()


def keep_context(snap: dict) -> tuple:
    """What a Keep Slots pass was planned for: printer address, printer preset, slot count, project.
    Not the snapshot's gen, which the pass's own selections advance."""
    return (snap.get("host"), snap.get("selected"), snap.get("slots"), snap.get("project"))


def stop_keep_slots() -> None:
    """Stop the running Keep Slots Synced (cancel, unload) and drop its marker."""
    with _keep_lock:
        if _keep["run"] is None:
            return
        _keep["run"] = None
        mark_keep_slots(False)


class SpoolerKeepSlots(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: keep the plate's filament slots on what each printer lane holds, until run
    again. OrcaSlicer only lets a running Plugins > Run action change slots, so this one stays."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Keep Slots Synced"

    async def execute(self):
        if _keep["run"] is not None:
            stop_keep_slots()
            return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")
        try:
            names = sync_for(dict(_ui_snap))
        except Exception as exc:
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))
        run = object()
        with _keep_lock:
            if _keep["run"] is not None:  # another run started while this one synced
                return orca.ExecutionResult.success("Keep Slots Synced is already running.")
            _keep["run"] = run
        seen, synced = {}, time.monotonic()

        def live() -> bool:
            # Checked after every read and before every selection: a cancel, an unload or a newer
            # run while this one waited on the network ends it before it touches a slot.
            return _keep["run"] is run

        def mark(printer: str) -> None:
            with _keep_lock:
                if live():  # never after a cancel or unload marked it stopped
                    mark_keep_slots(True, printer)

        try:
            while live():
                snap = dict(_ui_snap)
                context = keep_context(snap)
                printer = label_for_target(snap.get("selected") or "")
                mark(printer)
                try:
                    if time.monotonic() - synced > REFRESH_SECS:
                        names, synced = sync_for(snap), time.monotonic()
                        mark(printer)  # the sync can take seconds: keep the marker fresh
                    trays = printer_trays(snap["host"])
                    if not live():
                        break
                    if keep_context(_ui_snap) != context:
                        continue  # the printer, its slots or the project changed: plan again
                    for slot, name in keep_plan(trays, snap["slots"], names, snap.get("current") or [],
                                                snap.get("gen", 0), seen):
                        if not live() or keep_context(_ui_snap) != context:
                            break
                        try:
                            orca.host.preset.filament.begin_update(slot, name).commit()
                            # The selection refreshed the snapshot before the slot changed, so it
                            # still shows the old preset: only a later snapshot may count.
                            seen[slot] = (seen[slot][0], _ui_snap.get("gen", 0))
                        except Exception as exc:
                            log.warning("Could not load %s into slot %d: %s", name, slot, exc)
                    _report("Keep Slots Synced", None)
                except Exception as exc:
                    _report("Keep Slots Synced", str(exc))
                if live():
                    await asyncio.sleep(MOON_POLL)
        finally:
            with _keep_lock:
                # Only this run's own marker: a newer run's stays, and a cancel already wrote its own.
                if _keep["run"] is run:
                    _keep["run"] = None
                    mark_keep_slots(False)
        return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")

    def on_unload(self):
        stop_keep_slots()

    def on_cancelled(self):
        """OrcaSlicer's cancel for a running action (Speed Dial or Plugins > Run)."""
        stop_keep_slots()


def permission_targets() -> dict:
    """What Spooler declares to OrcaSlicer up front: its data folder, its worker threads and the
    fixed addresses it calls. Spoolman, Moonraker and printer addresses are the user's own, so
    OrcaSlicer asks for them on first use."""
    urls = [RELEASE_API]
    for region in BAMBU_HOSTS:
        urls += [BAMBU_HOSTS[region] + LOGIN_PATH, BAMBU_HOSTS[region] + CODE_PATH,
                 TFA_HOSTS[region] + LOGIN_PATH]
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
UI_PAGE_SHA256 = "b70909451118612891f064979fce42868cce4c3bbac7663d08e77a4fdaa908fb"
UI_PAGE_BYTES = 826994
UI_PAGE_Z64 = (
    "eNq0vXlz28ayB/r//RRmnosXOB4xkpKT6wsaRjmKkzhekmM5zqLokhA5lBCTAAOAWkLyu7/+dc8Gis7JeVXPVRaBmcGsPT3dPb08"
    "6U2rSXu31A+u2sX86X89wc+DeV5epp/o8hMk6HxKPwvd5g8mV3nd6Db9ZNXODh5/YpPLfKHTT64LfbOs6vaTB5OqbHVJxW6KaXuV"
    "TvV1MdEH/KIeFGXRFvn8oJnkc50eoZK2aOf66emyqua6fvKpvP7Xk2ZSF8v2AXqXfpIvl/NikrdFVX76e1OVnzwopuknjXxzcFFV"
    "7SdPR6Mvv//+3Wj05FP59Ol/PXjQrWVRTVdz/cnT2aqcoKoHOtLxeq4pP/3+4nc9aQeTWuetjsrVfB4PZ1UdIbd8UM0e6EFDfWij"
    "sRrHcXtWnqdHw1q3q5qqSZ9qGtmDdnud11TXeqvK9Oxc1WkUp0/preCH3pHKU5QdYCZPqql+1kaHcZqmR0dH/X4n+UiSD/v9qJN+"
    "HD89Oj7ebHYSn/zv/8SqksqbNq/b5qeivYrGVfnjckoDSsaxauwY86YpLks1SSOtWnSQx5jqQVFO9e33s6iNh+XTA+4Sxjyh+VBH"
    "8VbNbQ3LumorzOngKm++vyl/qKulrts7tbJ1zge0wHN+UdP0WV3nd4Oi4V81Qz9vaeppiOOziqt88Dpfno/Vcl/WqW4pa7Ev6ysa"
    "G+VdIQ/9wTpRtl3gsbrcyWnauigvx2q0m363uKjmY3W9ky7tjPv9Xk+rO2RG19SHzeaK/sb9Pv0M2itdmkcC0clVrC7uT1RbnXLT"
    "6haVXJjpidWpHdag4Zl+rA6OYqX1vtFKpTTeE+ReUi4tUY8KvMnfUBf12eE53g7oeTx+tMRufVG2tAhHDGW0GFQtAfAHfadqPcP/"
    "EcE4/yKtKt+XBFFfakrUr6tV2dokftHTbgkBLZsmb7tFykVYjXnVUwLHkof4F7tPNldU0nrQbttsIt50lBvHBIu1Tj89+O3m00t1"
    "k5a0jwH5tV7Oc5rDWivZCTyjRzFN/o9LAtCTvNERfa0K+vi3L6OzZwe/nsdURa7v1VFoNT54eDTGx6+qG/exqnxZbEHewt0GHvmW"
    "ade54hntxofrCjhnO07GNAUTbbdLz0xA0ciWmXPOYDDg/enwUHo4LJ/owVyXl+3VsHz0KNY0JxGX26qVVKdKQjy9I3xoap3qWVFq"
    "u0m5zJqw9Ky4XNX5xVwnvUOly9VCm7cjdVMXLT/X6jqfr3RSbqmBabhkDF5fz6ucAMwu1oOiIVAk/JHppN2qWVge4Jq9WS0udE1P"
    "CZXb/9FSKzpPgC+XerNJzV68nFcX+fzdVdE8Ga/GmX9NTIFGz2echQebeEMYrbrhZHlMOtUFVSXr7dAdC+9wLBSzaIo9brqP/I8v"
    "AxeqU6wGIfvLqI6za4LDOHlHf4ZUVRHbr/mkKOgE0edpQX+2ZhbaLRW7ZNwCDBPbs4XPlCsC2GGU9c7+Lzr/x28xYPaSkpLo7P/O"
    "H8WfqhG9fBJlydn/ffLbb+eb336j9Pgfn2z+m9P+O0j7b3nY/Pbpb/+g339kv/3jt08/vfSDvw4ORRq07YbbGCO7uYJj5tN/jONs"
    "PE6AxfiQvKInGvDzfHIF2MdkmkpxzkiZSwKb0kziUzpssL8Jgw0ITS6i+Dwtz47sS7zdxqrduj4+910cj4dm3uI21UM9b2iCzdL9"
    "+wWjimjJCHzR/KO0fjR+MI63tpLrTiVYN80bTgqXXNhOUGu66jt5pw0Y9bRdTCC2IVW2nszpEE5a1bR3c2wu6rmth46aS9oMcvCj"
    "GHWyJURScgp/kL4DElQCGheM04tWL5oJbXBF50p1M6OGiPTRulTTosFOXhYTql8XpXmw6bVeVC2W9u4in3xQNNpFWdGeLxi3F80i"
    "X6qyEspJBTn4oinKOSEWwsX5tCrndzQbbvS3PHoZFJ2dRLHgJBv76TnVgqx4iuza0PHVmkczZ72joSxV79BtwILWk1as8Eta0JLS"
    "alKVZ8W5avGndEtT+0ZPuo02xZ+am8TDboNCtMzqakHzT7u61DcPfizK9jFnRLXtp+tWy2SigJZOD45cRk79zZ/YD4Y5dRZgUZzl"
    "BErU6VbV9Ei9itc6zYcXNJ8fgA30k0PfKeCK9Mhgi96hH9ONG5P0G1uNustkHFVSbzYFHZ51upT0JUaDRIdiMJWZm5kEbc0ic3QQ"
    "WdCAOHHLE6a38b21skOuZbesZbl26URCikQKt/dTGVXSDsg3mx794ocXtcai1jxFtimLN4WsEkrJPLfBLnyn7ZkYr0s6T86wjK8B"
    "1PJ7jtU+K1ROCIdbR6cYC+f81LppKgaXupV2aJPm/NYyXTUsBg2ycHLn/NgqQm4Ye5XWZl7daUfHMeVge1Bh80wfVgF660Ap2rOj"
    "PjSwuZC1BGQ6KKclzXgpNbr2rlgQKYJv/RstbUKAMJKPRxYQMm4COVPJmbocrs9N4am2VVxLwWtXsFdjxTLKdaVvqPTexQH9Bsz1"
    "FZMHvV6kwWmMRtejonmrZ1S0dxirryyNS2QBdRCoE0fM1J2QjA8tWU0fXVAProKkOM6+wixnX1EiUzFx8t3p928GwgMUM1BC32t1"
    "HHST3i1J9hVWJfueR2M/x57K1mdjgpvo4VrQxjYenydnIMEGxPXWhW7o8KLTcrqiw5I+PqO5IFaQaiQ4/sCbPaaTI306JogjMFFr"
    "Iq2SpamZeJ19NXP7XDHhY5yoHzAy+g6LmKHWOLnmU6M3lR/N3XdzTmfNBxkaIWHqC2AgG58y10MNagJEYZUJ/rKspaYTrZ5p9btO"
    "+RACvUjztpq0tME1yMt1S9QXfdbSGa+nYC7wPsoJhK+pwKF5r+jwlUc9mxHmaMAY8/tkrvNytfQJtPw/5KuGKiMKVFJu8rr8vny7"
    "Kn2FBCbNh2KJhB4BzjP6Hz3TA2k3i7gQ0aaQQDwznWK+NkUpPiIbQofumVqP48Fy1VzxpzFxX0nUHcqezhBlv70EZucikT3oHoQf"
    "bpcYTMSbOEw3MxeMVnY1dXZoi0rfLMUUJBnOQg4djalNLQ011E/aoaazpaSTYmAa3/py4SLsfhLmhV8Tkm1Wiz2D6Pe7g7g/qKP/"
    "HwZle7MNqrAj+o/r2Nar0lBo3eURwvKZHrb1nV3YZ5pbUzylRUlE1t0aadvttippeh49cuCepkzMMhzW+voUQwQomiribTWbhRNa"
    "lU8P+/2Dg6CCQ85+xngZn5hPfX1M5xpCgzqKMQ/10FA1vlXz+TpM26lIiA3CxD5tu93p/HVVTB8cbrdNWy33ztjOfuGVJ7TH/Wpp"
    "Lcq9wNc+KYftLvC15wNuRhZyz2e8tK5Ki0T21mkzqdIodmC484lFTyF06o9CpzStd5vTrt90dA3Dj20joOd6HZRptpDgKmDsTtuS"
    "bGtZ8oxoEfcg30FYWOzMY7tzQshGoJf61Hgboke7rAHn+zrAZc+Ev3ij1Q+aid+fCFLofFJf7z0TDBTMSnsUTDXhdmnDJ7zLi3kn"
    "cTbPL5v0n/JS6tu2k2vWqpPWYPKIG6lt6s4RQE8WYjxaT3xj/fTgOHbI2adv0i8+9/guKP/F53a27fdf/JPmRMhDVE7ZP2hHyiFF"
    "ekqH7+WlriFy2pZVC4qjU/ExrXpY8WfHRNoE7483mz9NhYyshJsMvzhy1KmZ/MhAnxnRsfqX7dG35kHQcvoGpMB3evjGILbvcGaH"
    "GM9V6PDdj7Yq+kbjg1Z1ZuUzgyE8grCddBIsA9yABMJXwDpY8q/0Mn4JgmboAWcvxPyrM71VeUrNmW0kL1Hc7dIx4TK7CN0lzWjF"
    "8uk0hA4HWFn3NTL5tAQvZl8V4FR4PdzL+idtAcEWjIQ+mJoCZk5tue1WvcAZ9Uqrt9rvvj+Z2GTiStsVfKzaLJJpSt+ieEp0qE2g"
    "718hwbMOXwJ2X9Bh55Pem+P74OCFfmoZSmDDtw7jvJUj5K1F9XyWyDEoLQ11Z29qN8H/q/gQ5GrkGHrlv30lSa9cte3Qnf5SLQCl"
    "u+uDmlsHPwDL1m+nLYvZiapds4RwS0f9lvllQvt1dfNA+8F/y2IIx6GnWmCvHbamC4A9oq913VBxYtpVywffM8Ylr4ryQwr56dIg"
    "FySo3YQ0kEz96KVnfE5YCFZ1KsfhsB7aWa+5JerAsHYdSKkLGTFYxPAQVqEaYvUSgkT1B/4SIKa1qnfbr3e6rHYT7OzWqd5qs7+U"
    "7xxNnxvAT39nwnjZ0AnTbZahmGfCYJw1qRbLVYtjLvpGR9202Bba833seV0nPRqMeCP5Xn5jZWsWEj8HKrUvR19QA5EH0qP/ocGK"
    "nPe9m+eHWgp10x9q4ioGRXN6+hZMqanv+DGNoidTgZPa9IcYTp6u2PZ56Lbt8TCYPoIEQre1Qbc6wLUMnkMrFyVsS1ULrzmM2gAo"
    "DjcbvoVz2cL9msaofy6HeEr3IREmZqvw6YytEeQp7TD7G3xGvaoVw2+wvwmnu0l/6dETZJg0sKRUTCWuLpJaATjwVECaCcETdbEe"
    "mNS0UIbCpGeBxlgVVKJwqbXSrrQtUQ6a1UUDGQt2g7zUqkdVlx6Y4rV/cR3/59CfOUH2R04eRWTbtgcq7OCAmpmgfuK0zY892kuI"
    "vQJk+4fd7GuzkYnLNrWKTLcF4WAbArdvd7wfII/LprbKdcuWYBqMAUb9oolZ9afFz8Drv2ghcr6jVUOpI9+7X5EvE4BSTEF+B5FL"
    "aurebAJE+S83FkNzJa1ZR32PCrPVvmF4trgdODqgFgDpRFui+w9x1ul2H9WIyuS0pVX3hKMlLewOcGDr6USeL8unuBcLQJ6DCV/u"
    "YUQ6iNv2L6hZCze2a7Y/hhTN72FYO5Yu5Usw1HknMNohadP74g2iXPLJB3uH8IaOut539OeNZev8BjDIRzDOTsf4iA2WvEXvCN++"
    "ocNytyxT+bqN3shoQejxhsmi1s3ym+BMC579koSpaRsn5jXtJKsSslN3W9N2zj/eNG7lg2lX/gRyvJJNGfq95Tqr3BNXaZ5dV2nL"
    "7B9Xu7MJ/85A7ZtIhyP7RrSZu9+z9IsFLo+JHxLBZiBb2ATtGAYqDJqOt9cOFQ0wM7jMQHqskWgriVmBg95x0to0tz/fswwk4P2g"
    "KWDOVHzQTHBE8PfmiPUkYXiWM4DxochfUZ9oeO4YPAzQcLsP+3KrW3sC2iqGIAk0n3F2E5cGV9odrnED5j4ArgGqqVvHqkLIX7Sp"
    "kXHivj3vvFXhm5+Gpg2E799RH944kVDdmiuAYbvZ0IsR+qfmKiE2wnkpBYk/lBa4FK7kUaqFvJzRQUu/QAMlEmSnx8FZO2nttYUq"
    "VC4dqIIOACVU8RqAY8gknsOGL9xZnu6pZRQGDCnggTGQeT2OK3c/28RemlTIFUCe0tF8giHIfQz25VgkGWOH/OUqv46HvqoI80Yd"
    "iMIPNhu8VTRlvVEERZnyaQrpPe5WtuaytbkpQKZEWHaLqSpmsM0xyOUrM7HUQf9a4XKUTpFJ3ugxcXTjpMiCbNdt4ppsWoFPZpEO"
    "Ks1xLSHCsCHXJEc+VUZr+J98R6s9Trpl8Nl2y/vNre+89VfYv4YaFFgjjTZxiYRr3TqnbhCwxuoXlIuzNvkOD9kf/Le1NwK6jB5y"
    "AWISJK20Tw/DC7FV6y9mGdil/Z22AspgKjdb9hNpnFqT9h+2fLsQJ/zAe3DWpuvRiFWfRqMEFzfqTHbaQNqo6nPPEy9b5onVTgko"
    "GUxNFm46FB3PRMtC18V3fy4F4kGQaecDgJzxNCf8vbuc2W14bHLGaDLSZ0fnqWuYXmJpXhO2vutMxKX7Hln0Ne1Xc17k9eVqQdUS"
    "p69mxbzV9f4vJU8+ZaUK23c/8J26yunHaiqnrh7/+b2vX0AM+PEqOPsvhlJOX+VN+/Hvkft3uoFy/6YrrsjHu2MVTPZWIZkf/bgo"
    "J/PVlOChA1DX9nObTd9zYVGM/FhZzpWiv1dFGe2BUJO+VXM7ro/WF5SQOhkq9g2SMj46QCb47Rd39gtKHSMTPEOndV+CsqRZc4dp"
    "9NBswZEtKNncviv8tri8av/NF1zGftZcFbN2Tz85HT1tqoXeP3jkfHT0Rm91/xAlUwbZVm+xfxs9je4vWpiJoqdVTRTPvuUN8rgg"
    "tzD9CLbayd+qVSnzsL+7Jlf6a2+C72ExyRjv4s2AwFu2XUURPglUkdZn7TmOfNFJFSWMWuivnpw5IIVyi8Pt/fq7/PIcxzyrwzx4"
    "YfC2ow+6Kp3mjY7DH6xKLMF/HsdewYzFgND7W9Cxym9EshB5VFBXrlrqY7+/T58ROF0rMx3JGgeu7UI+MJyRPVv3aAhnenABrJrT"
    "MQFuEFKS3Vo48e9XssXxmQ9GPCAZicp3hjdy47P8Qe5P3EUXwxKVW5WahVUi4mmdQoNVArtqjbqSUzj2y365l5SUxW/SKlxoNUkr"
    "mmgAwMTOuqVSJgMo4eMIzN2iNfb4Z+JznpZDU13UZPPU9oBVHuxgSoEyhk9DWVDHCLITpwt4TN//ja9b+S4WsntFHeS8Ss3pA9dD"
    "KLAU0SpOVn5+R63XCRKqV2aD9kBnNipiOhrcZ5rkKM+iJrV6XBDLUZGwn6rwlBUmgXUHUjNMSLPC3nNyTfDNo/DD/4y+/Gi1uxNQ"
    "BFMwSQvcdFbAvsEMZNzQJE4mfgaud1CBkKB0stddOnAo0wMMAeTktJiigjn1zQa/vSMidn8mwvzs8DzO+AcV8qvyn8ZJEShHmg5A"
    "/WINSZZiLjfoDW5ULcR57SlQ0QqSLVWL9mML7UdHbSqnRURPRfN+pYnRuxUODao1Hg0Femdv8gXhEMFu8cDSa0SOQZneHSpjo2uP"
    "+SeaLba0mnx3ps/dp6M4YCdPmdweRSJtTp2mUTx0xL9cy3mKnOh+4nyA7tU9FTktJPZJ+xG1HCOftcoYb41mplPPKZrTK9YQTdvt"
    "pQ5ZXWYOrfhp7NSPnUTKMrc7NdP5sVPzMKyMC7KAyVbZq+8XMNqjVpNtp4Cp1+UXnfw69zlgNKM6K7L3bfJlS4zgn23yto0N07zZ"
    "7D+FWDttf1YJ7TMj4BRNzqnlvg3uYBFpDklFOmN06WbO9bK7hK6zp4I1q5SgdW7a5vVoS9F6E/Y7YhWv29ZoIyYXwLgApnqzYVJ8"
    "TN+NgUa9RmfFbZdR5eRkOfh5qqdKKjk6hl75E8p02TfCKdnT6Jq+zWqkVnHyI/+t6Hi8MXD3gE4vXU4bAsQ9mmHNikYaETAStDb6"
    "HrLVQm9MmUk+MWqqvR0osh0ndrOQAr+0LD3ofSe/hIJ+RR7hkF9FKNCjQdKgCxSi39IvBc1WYc5OIih6h2bic2uP0MZOlThZyZnU"
    "uGXxI7AL45ErZLHUeg1uH2g741sa9IAFOCwN4E8LQr+cAgkF7zlqYitChtAww96Pml7UMlmF68yeL5xiab9f2naN9MLTxjhntqzZ"
    "6tuwddpkW9GINQgdxFkwY5xEfSq31U35UvSCQzlCcHIw720lL0lBH9m2/KcETe/+E2g6DKDJKZYf7p1Cl7lVzwX337TqK3l616rv"
    "bRqUddSHls3m1DP+DfZiF0V4jP67w5pm8O6o5nPXALmT5hN+ImAXUKVjnWhEorJYGd7KHUQ3fkf+0e8TISPloGs9xvuKDUakGTVN"
    "y+xDm7SZLpOHrb0rbQkQib4M1mKe5S0vQRN1SfJVrNZChfK1j9j5aAVaE3c/K0OCO7o32y2SmIRJdkYLzqf9lOUn8Tmr6dpyRBAH"
    "ks3XofwpnLqA4MWoDQhDpVh7uWUm8MwKGUGlb9oQsNciJlyHJ5ZZiUK2q6wIIVigBt6zecwzVxh0SmgieMvluF7TFiA0mD7jxWzS"
    "FgugzQIQiqqEOCu8mvqDJqqt0LJTIr9XgnkhIjBoG9tPtgo6JFAFjiwVHg7GrrnmnoOQCKV4WHKjR6xkI4eKl3Y+apkHmRePAsy0"
    "tIzKhCy02z94K2KRKRdZaU+n0iENeSoCOU1wBDD9CpbT9qNC+/m9Se2MsNoZXe7lzqKybYjjWjXM20RyJm6dEVODG/RsTSg4IShk"
    "VAwDvZbfgKoJZBnqOMEAIG1XQB4nGdk5QT5Uh5xFk6XhaDaf+dlkhoLvlJmbkJOL8GKR+MMXcySdBgTyJb9mUOzkaMkp7ucUIARK"
    "VmQCXsFFg5wwOSCMab6tEqRJ+6HdbPgQ3Wy+k5/Inp2e8JaBMKQXAL8kZ3ivgbyshADGDdVmkzrZcZAhVTXE9/qybrS2J8oclI0c"
    "lLU5KCmLkhJJ4WFwYRmFs5pYdwln6WvJfa25r2KtYxgltF+EfQ0yYkPT1VntEw25R8NtvaVGcMZOmEC3B6x2widYcAioOMmB6yLu"
    "zIytkaiPmnKB0Zec2wJgts7ODw7ebazO5Djw8h4vvt6VsbvtUadP1+VZfZ7+jpllwRtqc9jzhw72NLjUcnoiNUifFntI+qynk2IP"
    "JZ91ki39nrU+FVR7Vich6bsylFMB06E6KxNpmfmdr1tG6gn1lMjKHozRX3STDinpVZB0KKXedu8D/+y+ftl9fd959Sf+t3xkmTsq"
    "ba6a5DAdJ/zCwpdxYpbzSK6CqA6TfaptQVN38MZ55sPj4VTP8tW8tQmHwRn3Y3hwmluY5CUWi8b/vFVftzTa4KLnp7C8Lfd9SxNH"
    "0xCU++Z+uUOilmg2aX6Cci8DOZLoJIglvLZInLVZQ1Meox5ui4CL3Gy8qfNzUH1NcTHXob2r2ZNFcNOZ28zc2FTRgpwyD40jlfXl"
    "O183vIxEv92CIESBY4K10ARLEFEDGtxr89yfXyTZ0cXJrqWSGZ6v4bs2tHncKcw7Iyj8y0cLWw7Il/057JrOWCNOepV0NH6CS0VX"
    "nycUiITjQz4J1X7CXoDpCEQATt66s1T9/kp3SmL3GUHkQ6aimaP8UThKpUuXZJhMv7PasjOwXSuwzui+D4qWJYNzMEWc4klIx0MT"
    "INSSJfoB5V9qIUH1SO7pvTqOdCe0P/JCFGcbRLP8XmSz1KgcNJJx7VIfBqmdSlgS84AL7lgSQbvB6AaE1YENMuV1lzC03VABmeca"
    "4tNfy+lPG4t4YdfXidyxWD13PxzdGUbZHYZ0z+q4h1cNH4K1MksxMNwDL0MuRHpiOKn0aUecQ618iHalIswxu0/YoC6QJwx9Y57/"
    "zzzXDxBN7nP0dafXVQiNf7QegiwqyUuBouYjUMREVtcKgtqi89jqs5l53LGKMCAX6rbfB7z/xJzi6At529VtPTj6iJ2FGEwIWd5p"
    "34gPe6b/rBiblt6aoaPpv0HDHfuExzH0Z4zNikXSxqaBsQYx6SHwd20ELOzbxf3Gqv+LZlBHRSzQJv6LvRIsidHVlxeWR3hAmJRG"
    "Om10XR/QkWc7AQogq1MNM1i2tFWwb6ZqYjYpboRiMoAyL+EMaFV2yIxpaXUmXYOz0qjWUptTkceWdmevSqtPRPQ7vYg+UQvJOfTX"
    "cJOrQwZ7ibpKyGWFsS8WCz0t4AQoJyJaL5NKVeVEJ41yFg7JXOWrS4i5v6sukpUCMZzMtmkhDnkq2gYGdVQs75ffw2yBpo7iBL+x"
    "WqhLNVLX6g7juEjFjlx2f3TJV18GCVAJuVdMZJOZXDZQv4PxL4sPsugCwH+H2eVL4PTpH9IJ+VjZOo0gfm1b87JrkXRSOn9o05eG"
    "rLgK0mbZLGJTYGjpUMcuU17nMptlaMRmJuzQib4dya0Fq+WNAq26X1mrThZuWg5pqRehUY0085k6uz5HU9f+QyrZbrdQo+73K7sR"
    "LmmZecYPs6NPD5NqKEPGdONEEL252xRWW+pUnE0tjPmcuu33bwfWWHMS3VqjKLUQjbCm3y9tO+WwTCPrbSborjauZWwnT1llkL/R"
    "6UUmjhCs5JTvP+bRvIyTeSkuijBTC6tET3t2MTB68+ZO2cH4QmxmWN2YgGuzoTLRRdbKyhv2ng8prVnInrB0QkPdyYyBZtuvSL9P"
    "i6J49iX3DIVpJuellSBdEIEEoZUknp0nmni586GGWROWqaRlImKlNHf0wTppJassqmum617KsCL6KDqh7cCb/msdXdJzYLU2Z4ia"
    "RycgYJITcTk1E4KGFkeNaDbEmklWVAZgsMBC5ohnbxYDmD43arQ7XigguaNvDAe7gLi1zPLsBDJPGqqd8WSeUU/k9po1tQQp05aW"
    "fHUqtsBUnn+l5ALpYiqHivghyAEEpqfqNLjRFvxGQGxvm57ApqHDQQh7EMFJg/XREJXu6uYwfpq23cuV0ntdaA8ORDofoyWDZdjr"
    "wl6HMDUciHjvIfWjR/wdu5kIP1py05jvWHf82SzMAUG4whXWzMasdzxgdOr1ebRGe+8ihYeH/Cq+50Jsacq8aJ47Z03WzRpuIMKm"
    "ts59kFuDq9JfxAR7vM60SJQZ9TlzkZEboa/hMqjB4k9DgwWVB7KSOybGioGplSbOVmtlG+DbcTXR8bZUsJ1Dx3mK7jhPkVMP3YHf"
    "FGnWtxv0eCRnIZ3IOEpyd55XRMqWg2v4JBMFxbWu66r+Ni+nOA4b0QP5sbzihOlzZL7AIk1XXHEy2cJAq8QN9Qn8Hd62A/Gotdmw"
    "KNhhttJY27JIagk6khjS8VXbLpvk00+vV/r3ZlDVl59y+we1nmkqPdGf/j+0/dpioQ8eruvtWEzHQvM5PeFmQOoSVeYcq8FOKWct"
    "f1gEG/wfhwZdhzBadvbL4oqmxCW9JrKliuU+36gUw+ZLuo8FasxNPa11o3jWjg7VGX92LpfyVhV5e415r1VFeZOASbsuvYOyQ6zJ"
    "EQNSYe32hqCnK4Jqng172X3HzhQv2Drvlp9PS/YHok5giXFTprQwi6KBjyr6Gv4Y1Dsp4Sms56Xnld4RjrlxWkGajhm48GPa0mry"
    "iFmohmqLq+KroIqL8hFotTs3k7JAT8qhu3Z4VD59+vSIRnkH2RsB39fgTQDLm00uJk2FNQTO2rR+dJSUae3NBTzja90UBBZuzi/Z"
    "10x6oSdnrjMHR+fDHo3Rlz+GaepTFCauiMoZqjGhR6MpR4MjPIpLNuXtytSHsqOVjtc1Zi+9KWXOXpTB8j5zHeW9fFpCBlFMxajx"
    "1DV1grlDS4kbDuH9W9eroAO7ZxtDrw6h130GsmDI/fU3dR7csF6yCwjx+1WrrSuwUlbJ7KnSTRvbQyChmEIHaLAqprS7nJY6RF7I"
    "47MJjk+LkghOP6s1Uce4xM3qg6PkolSlN1eMysAcXeGodZks0w9s1cPbM8uZiIuIWzsSSwXdYrCHTHjDmVSAR+E0q3jiPmCXWWtB"
    "sLflWXE+jPJB4QyFMrn9zeOkR8lwhlRg7E8IfKg0Tdt5mifG9iw3FC+hbSj6GFUbHZ8T9Va3lnpjQD34GmDGNIzrSVrTfg5NxA+H"
    "+knhfHdQN0/NGuP20+EYlCc8UDASGJ6UT07d0E6chzednpZnJ+X5MLATDQxDj72p42MiQ6LQ8vF4G2IZsS55A47Q45QfjMyJRvOG"
    "RhAgQIOl/XQaotNOzi2IDGoOFYrpHMGqM69Tr91LqQLym5uXnnxdirNX7C52jeR2ekaQBmYBeb6rL3hrWiOiC0zZRRlshItgymgn"
    "XGDKQpPax4HB6f1J5NOfGsT/7OifydHnfiY/75jiHkNOZMfD2/FvdKPz/VYOAvcNnQCvGQcalK8il7XZ+P3R7/MUyOy9MkXf7p4S"
    "fwYo/pU7IV6B5qeyYlcDUmw04vP1BSEDrijA1s+Y0n1VGkK31zJ9W3Yl1HUqOnFEEdWDEZ3aH/Lo4Miq2/3JuDhP3+Wm96piGKlS"
    "LZ91ZlBmy5Ud6qf5UB8cxF/lBI9/4sxRro0jRxhWW38tN2L3SvQ7Mb9T/g28CpRygUjjeQUdK3bQujOgpqK8mIUhxOQ1cLV2Puxu"
    "6jLc1Jjls5xIhEZN0hbuHvX5EIpUQCjQtUzXhqZJcrUS57JJvhWnabDoW0C/SRlacE1tUrmibNocwg3rt7RS1XzKoszEa4kTfbeo"
    "psWs0HVDlFy8j1p+X95TW2K9aMgpL7yD3DExBiPuZ+B8MigkXnHHjm6jY9iUH4o522hO+U3L7lpMRaX3QMk1OZ+5zv7OfDT0bbt6"
    "LBJhBalW2dacObG9XcEa4Y4THcKzW6oJLdXkiYOmid2Q8zQ/m5wPq2w+sFOaVpRi5Lqdnvb7vlBwVkbztInWW0Xk9s6qeC3eOXqD"
    "k5jY6IjJTSLzV7QOj4nUHOg5fVyo1tCbIW3yrUfGL3M73y9z0NzXxVQ3dC7izXjbcY8uf+idLgRf7aix19DihSPGNryYuyctTP/I"
    "I+t88VlhAehZkT0raJMZfsE2keD62bjk4Z212dSDCZEMwp8ELAYu/3fTgmp2R2QVF8WGz/idtUwSdhuu1qx6q3PE6nQp4dG6hYGZ"
    "XOSjceZfQBMzFv2ptEpLgJ3x9UEzuR3H6puS5RY0Kz+VgdrUy3JHbeoPx2H6K7h/L7qczWm7JxMRYc4holwJUBWsEiU+I6EHB13d"
    "ZQVzpBkG+jBn0Jik7Oy7nDg7hW8gd5phB41uwKZqwwUKBnM7sTe1H4hPd2+3wNIOOC8wAhE8isyEnoQyWhJIDVc8kam78mBueimC"
    "ARRagLbg/nG3s1UgM2KrTiLPlmqS46t+H2avzVKXDVTnebA8KgjZgLzDj62b9zaDD0jmJgiNrgZe5Mv1l6FLCTrAF+H7MdqMmN5Y"
    "ghBU3BvagNz1q9QInVeOC38IVD7LZoKer+JkCnii7XMV3JeWXS10Y6cPHrkQf9FwYWXstMaDcZz9UrJGCYthawLhxLBrNRQc8yED"
    "bA5fluJdlLl53IVZZ5w/5+YGoUkJ1go6S+TzOFAxr6LOtfAvZagc0dooAAPn+tcJ6XAE7D/wCMmKm70UPo71ub+ukp30c/eC4NfS"
    "WSaPrlkF6V+G3INS+zs914i0oB5KIq+L8eY7BbFhn9nhLhFidVAM8gUugwdToK0Dp/en7795PteAC3jHFrQhZ2onU5XhR6/z9ur1"
    "K5MVGsbsfN8pp+p6NwIB01eVnZxLMKtthqsPFtIkJe3yOl0j4EQyttMwVuGkwJU5QdBEN01o9SJkhpoLWllMkpVaTpKpWl5Mkpmq"
    "kjV1UtPXS/XHStd3pxr3hFWdLJQg/neEaZMr83JSLdD/5FIJwn0DKdJou03n6jp9WLKngWoJzaTpHfW1mJxcFfMplUzutnQkX3gU"
    "QHu6ucqX+mvaZP2jLyA4hld5KS16w7bv8VbdQokpmK6HZaRtU7iLagmZ6zata5sMaXKezmtW+rlSS/FzXTGyuL6kxWlhv51V8ppw"
    "xoKWaDGnvLJmteaocmnssKUYFM3Jc3bcMiF4bM28v+O2G1a03pNuDTDimHXVsN8g4GchERTXarnOh6HtaeAz3t62/FwGvndjk+Ld"
    "6AYTYWmkUQRiAWqIwwuebjozy8lVVdvGiBS6lVu/nwM5MmHXFjpHQ3G8y3Su8zSh5+kVew6g88nUJglDERUzsaiW0P/EA/TKTa+I"
    "f4bHYELX06K8/LLGx/H61Ctcbq9pRi8i0RRHD1v0MFa3kdCCa24dQ3I+BkwH7LjoGHSzhP6s4vXK+xDrTFfYbmug5hTe3B0M8dtQ"
    "Ti5bwmWqK5f2zPYhfFWXHcgcpZdZSRvrgn7r5Mqq7DDIbTYEgUsPgZJjwI3WDpm7MHiXReyioru11J0a2c1CR1fOa44pTCabDdtM"
    "U/6F204Ea+o6vszMAgHvmAeTQmiI5T32xTgQkZcgPU7yOhI0M1dH/jIgau9XGFONkd5pEenOIZiDGNq5zPj6yVfcjha561zRyIQ0"
    "uSTAQs6SNjj3gIHnGvc9cO1+bb0xr1cLYooI00lqUlABIZPXDgUReWWRD7FIAldEagUwkcxVuNSERuUVqBT9xqUxkScAgBluwECM"
    "Uc+6oHkFJm8/bBINB9QSzWmTEQizo4cimsSqh4+WtJQEDhUcfHUP2maXsyRyG45shzXtRgx/oXq9YhdoMEk8GXmtru6m0CxOqjrQ"
    "A8hrO3v+iKjpG5o9QqzH8RpyXInRE0wSUcrdBMb2yieafcKp5c7uEUVzPae1MAvQKL9AE79AczPjK8z4NEVPjjG7UzRfSeW9n0vj"
    "zhz3AkQc0LqssKMm96dwHk4hrQDNHg/9OB5ylc0OrW41XswBixli1yzFxZxwHHU/OBybnWN1osxkzsPzdUXLQVS2V4oQoYMgvMB7"
    "nvgWqwfghN7dsZvbx5I6IGYbEzG2x88DjlLxQGZyHHexXe0Z9vsf2k/WO7gO1P1ovsx3cCBBZdTuLKS41t3WaRXVHQUNo3BmUfg0"
    "qlilStTWrZ3uVniCNjjWLXKg/XAVEhpY9oVM1CRdcPc2m8VgRmx9y7A+bHfojOgqi6Qbij5Fhd3ObzZENSyoSytCKo0cvItM7srg"
    "ScX1nXv+b6uAYcgEU4RStBftGGNz1l0ZZAZCebenpps7B9VOY9yPIBZHHiyKOfdFcatOizrQ86lD2p5Ir/bW3QCsWq/6w55/M1b4"
    "0XMWcZlKRQko3OrFvf0MWIVdxzDugOwRQJgIj2dtWxcXK0J/YwDhwfVBdVPCKUgJPguUnXGiJxtriJ51LmXmwUYMKBYPoTJlpTg9"
    "2j27OdlOXH72a3meVqxfVUc5HTcQHhI20WzrUfEcrmrPncx1fq1PLmA4EaTSttc1UgMFJ68Vvy4aE04KkYaK5hXVAYzBL+Yi07zP"
    "Jes9kEiTGK0Ax3q/r6NIiGhXI9ymxeqnIMNXKHmif7is07OvTd8Uq7Gcq0UNiSNhKxOoK18uYffxJWLM5aVaQrmsQa9tSlVKkKvn"
    "GG6ypNO1DB6fzehxN+sEjNCceDNJk+8xAVoSgkf+fjdr7/fPpKPyVfiMGu5nhnVs1ZVjqL7MG/2OSNOmkNBpcrwsamhdrrAL1828"
    "apuk3doNAykXwefMWzJEXiuT3TRAl73fP6kj9xaxeol4mLKXPNklHdOwHWpWF+9qrbMvozgQXvXy0MNdZew4ZK2abcrGrvXAAZIV"
    "YF0QBFvD+Ft+Rl2T+9nz9K6OJkQX1pACTFjCTxv2hGiPU2TMrWzSdbDfpwrdm9DbxLyFX/Ze59GKsGK/fxMWdZcbNeWaFunrU7yy"
    "PwbEnFu1BwV456ArzjbajxNiHkJEDkwct9Qpc6RwQ/l7deEuckTzyqiD+YvOQLjVKQ9LLhG/w5UYxD6lEhkSo+wgU6i4B2GfiCsx"
    "Al4l880DLMoDGmN3gBk70M7vzFAchyzAdA0edkVTdWYM6FfsivM8pVk7W9Xn0m8Al7waKbjp0Vyq1tPdPnUzzOCj+N99t03cI88B"
    "rb3V6HTOPEJ10ss60Ms/OzwfBhGPngbesSXOJCtkBCu/JtztaAkrNgISGxH7GRxm1/4wW+8gTpCIhOolZA1XHYaNoTNsT/w9JWyx"
    "FId+TXghdFd3bkfWBlcWijdlHiDLCiDYxZSNQ5STLp6c30eTqx0sOfNIsosjF/dR5NUuhrz0CHK0gx+v96BHI62xLhsY4tQtYJHj"
    "tpw66RXhg0tRePlfdmqk9Y5gqz07Oh+emmiYItc0/sQg1BNAeJLCjQZU8oIUTtiqE3MydSZWXfg5tdadddowliv9kWg0bOr0crNp"
    "hOK1vD+2ClFc+OG4BUYb4Ozi3Dg1eJ2zOaL3hKPnKDyUoGYGom94Y2u5SpICW0jyqOOntGuhl8He16SXuPmnBqD/EmL1Op1AVEX0"
    "yeqjAxhtNih0TZQllbvbbFad4YjlT+9o2J5NCQVAigR5VAM8SXOfVTR96Iw66WxrOp4671Cs5QrsjRn3b5pyYqgoSbx2nWnNQ1TT"
    "cygtw70X19H6a8MO+LBiBirCtE9l2lXZIVMcpqdD9TSacZfNyvDYgN5KGhuR+FHO97TQ0ozK7Ir2AI+vDVHg7VlxLspGBqkhwQyK"
    "iEEU3RkUf0FMPMa2xNgqGluFsU3mVelMToo0QALesmr3PDoJUjDV/g01FvuR/kmQnIUvNkZZGXzcwd7/bm3pK6+pe+IR2kVtVJfe"
    "1KEGefoqF4Uky3aL3kBwT3xbOw+94Zf/ggSMEa0E9pWvQej4N1hCiX/larGkmS1br7nukizlMOxKalovCCiNn2ajWAvO3l7hmbOm"
    "7X92jNuX0hJhrpulJ8sCjuK0dlepoYD6Cx6K6+saPkYtuZi2zov5/a5TfTQfpZ0P0E6QzAJXOuXZkO07fhzEijS3XIFSJRx6F823"
    "LLChDZOVXcEq0ZGi9iivkKPJgAYWfk2zVHlzIsGqOyOx5Xw2IKBpvs7ncwRJ/Fhhmx+OKiyqBCJoN76h3RgCgh3uqyKU/2Mzltx5"
    "nqogimHtrEUs2j+Dk5DDv1KaNXqvrDHbEAYRtaEKaMnGPyvjR+aJk02RPKkEd1Wu+xkVWOKy1K4X0fKPHjGrajxxUher8CajiVls"
    "AK+unrLhK2VcDza2Nwntt0qt0acGehnA/EQhdSVVdSipqiVclelLenC8J+rjTe08G9/bajd1tAdkRcvejdcedZ1F6/fvL5cztLyp"
    "OSSbEImurg4pHyCRd13/oGx60kTCl+kBfraI2cuMWKK3HQvO556zZq0Dp9Ua6fvayYNi+kOtZ8XtZjO+HsePxgfjR7jUbQhTmIej"
    "80ePkjBQ51c8e5yZnu0UPqbCqEQdqsPzQGM1lKu4MA5RVKZ7ld6/MrHnjCkm7PfKQRigWIQ3H+r95tnPaqPknavKqhSLMrne9RAh"
    "Rft9yi/jDGrPCSSz+NKJj7Bcr2tWQoKL5TzATP88OsY9jlEBy3Hj/lZUjqdIvwdGPqXf973cB24dGiZs8vOsqaLgkzjJWQsmrTK+"
    "E23UuiCqmDh8EPkL0Uqv1SidDWih2R15Zh7X20Se1DXlMjCdtojlegeW+hphy6+5fJEgLiMt4kixtW90B3r31gWrhpU35xpVzkWP"
    "t2+/Tw/pkuf/d+B4dRkt4nh0tjiXY/OCXmnur21C4AC+RElnjXQbLQhZfojZZMhYcDJPQomUNiIw/GCq4MAvV7gnuiqJXJmpo2N1"
    "Nlej88CrNYJPLyFqp2aWQoPR8WPJGMs2E7C4W/7sAtdS12fL82SEP7f0utn0qNlsaRSepBN8nRVP2SPVhD1aBBYnhNhLr8DQsFMU"
    "wXfByGM0kJ415wpt8vTQOxI7I6ACNC1LOy1L6wpyZ05wTnDVbRZxxfNOtRDeAvz31LQ7u/NYrkHncecylojND7W/sNkOW+iEHBwh"
    "tXuNWptz8PeaXYREHT3m3wOW+EPt3KrzlZe7GQobircIy0Xg+8dKN+2L6ZwYPTluFWdMmG0L04fAGa9riTGqO5v2VZVPda3eiGaE"
    "zSqal1ovn82JdAh0fA0qe1Gz966xCl0ifN3JnO7kvjD0cWr10WrRMppO4I/Ea42U3rqDYyEUzVfiWyAPgjsEphjOOE8W6G3NPiJx"
    "l+TpIylqAgPyZaMkxG9YO0AUxViXDOcYpCsg5EHqpjY7WK1X9a4y5Fu5jayNMI9ex6vFWGFUk4gdyhasU5M7i2Rf21s/LxKpPjAF"
    "LFgPFArw0LKDiSvk2DRp+gqTxoZKNHE/W2eRBVR6SpS6LPkeVofciPUVmXtl16wYWG+7eZwUVoOdivAZ8yeDRGRWjVqCHhP7fWyW"
    "482Guy4WgelT468Xt2Lqyzr9k+bgYjGO1Xt5xuO3JnlFzz/KMx5/ssko841Jx/NLeaa2YvWHPNftJb18Z18moVT9FyEEAV9YAT0x"
    "bpVZp6hOx+7UaMbqV3qfFrVm0rgZ+0r+1SU+yiL6GfoisDuHbZ64dah3VP3Kaacjuggs51lzy1VzhEoSvdk8DCiyNixPRX9lV67e"
    "mUNhNSoPDYTIWr8qN5uXOSs0WlRd8O41+hrpz9YrYzqpIiHJxIBDwiiLp7Ub9k+Fp0pHNxKQ2HbF6MfWBRsbEMLma1AqjpSAnpJk"
    "S9oQjMBhTR5smbro+vBFF2hbULtnaJIfbPPnoc3Kzk4jyMaRDguiyjmfrDabS2ctV6ZVv88GzjxX4rEWSJ7efjFeftnjA+3tlVhO"
    "F+mO6a5jHEr2aesYh/JJNYRKfnFW0tkS1VmTmTgDlBCz039+SvDXW/VB2wXJjhEKnCaX7HJxbHhmfiGM94JmVWKj0MQ8OYzZBJCP"
    "P9fXTiepZzrsGZtj3WvetX9tvVjre5EI4iKM9E67W4tDCqbWdioMTuQy7UZIH9p+lvfmtOY59TZHNKe1Z8jE7AjemTCX1TnfCnCD"
    "9bkzMubp8Iq5EXtzKmA46QCnMADXnaTWraRtsYYOItMt0MOKu6ZVdWhapc+AyJn9OGcXwINZaSRuDM21zcIcZBYr2lgpiGbGSYGT"
    "q4inSz6IVbtNUGqf9v3rrstqnA9ZBlcKr4gxIFzyqnSa3ESquzecZfaZyjm5paVPy4CtZaXhUnjNHP6XaVfsDXr/1En1Yff1iRGY"
    "fMJaH5gA0GA/0CHzInoj2jlnbwmDzyt2aIbL34h2uCqyg+Pki8/jrWXD2/Mh7dtqMJpAwYltLo7sdZU35vjBnHNzNgARLEif5UVU"
    "sc9T4uTR3c0m32z4Ro1ehvMUfeGRwcy/NyKCM2uS8ejhut0S1xf14GQwG49mF2Ni9SAUwy1AhkiXOHIL9h2EO+rsi88T2Nw4s+D9"
    "BicTb3DiIjAaC5XdMR7a5UYf5gNjRgPbgAHm7FTeidN0ecRfNmPq1dyDRx4eH949RO/3nBFIz7PuJzm0Xb3YpZcXHcFLbJQaAr2W"
    "ouNKcjvcMegmprHf//Ts2cGv558OYHIBFcpxVSZsqJs0MBI4T2GI7TasqB4UTGxm/8qZu4fCQtIUjhgTFVc1KdJdP53C+awfJuym"
    "9KGe84MxBCBW8CHUBiQNT+qhXNxyguiLPMzbtjYp/KgeylUup/CjegjGUBKYRXwo3UJK2EsqV1U+FS+UdlU1rXw7QQ8XhXnDk3pY"
    "cVR5rnxUsL4mTenEmMZIwZmliHGzaG4UCSwfQvHhXTH5IKVgePq8FHG1NsYI6iFr7aPAdzYL6u3zIjWYnN3PSNRG+EJiScMpmF9W"
    "twXdvCrEZeh6lOitsXMq97nDlkjt60l7m5hrcWagk0LxGuTmzrxS+QQayCeI8wxjcgK/ZKI89QDDBZFonh2eg7h86MwRGoOcvd1M"
    "3HU89+AocTYcVJSTjhOnwGGTPrdJtUv6zCZVlOSOxnnRdViK8/RIcd22SC4zuIry3YLHKg8LrqJqt8RnqgpL1Laqerfg56p2BWeI"
    "DMmpxmJpmk7QI2Lvl3xyhQ6/xwLeY/YRagFc/LZC48XSTNEsnRAETJrmdQW7CA7bPEtnfK5b9yzDv9NFaPumcytREx9LPhiFWhFv"
    "7T9cYq7ZBaeBLntlyhBThFCUKwBWBdCwEUMKnvIswiynzGwlhe1ewTmFz1k5vW8Wr4tvEwItnHsSw/woLth/3FESVe47cQ9LvZMu"
    "6bBLZQeSa+5gEQKyB3kG8ma7VRNjL+blfvXZBPSudHziQF7234T6SuMs+QEAJL+F+Z3Yh/yjE458mJbtru6cmo3hODSIFnK3Y4TE"
    "d+KGIoADSnGrOY69dyj5wLgUYVycECYZBPNCRzlReN5D957mQm2AaXh4mdtgE2rHCNiYUzA3TYT5Wd7LgbXgxSKI51J4GYog1jLV"
    "zn5GtNnwCWIay13xCZ8o/f5VEXWTiFIZX4Cjc5BJwGgC/NHaLnR7VU0bQmWCbCfK2Jglc1WUOKzgNIprmiYzFdhHJktlrTgXKjSJ"
    "TC6dUedIOWlHckfL5d8uzCdf0TFbV3fJra1CbkuTUyrNOVRWa7WyXjCSE0Wn1VTXCQ1Nnt7BlRjllD6BHddRUk3Dh7+Jk3xJa0IJ"
    "N7QF6mtdQ1SuMd6CStwuq4b2qKYBX+m6YL09gnutPJNNh7/yLHZCZ6FEhGiSud6mrVETWhTRCh7C+Fhv/N0GyIvGricrL1+xI3bm"
    "RNPW3NLKpUhuy+XWE3AZD6+luJAB6Y8cJwCFGWxU1W2psjVUYGXz9NuIHfIZkz9pCzetlIAtgkT6CTL4AEx60scriXOIUo0rRWW2"
    "8XBfzJ472t5arbVzYwOznVDgj3f2D0i7ITd7D81p95rqLQ9u0h3WJL4sogmGVLA8K5Bg6vSKHrO5mbE4mQ/ve6V3FwYtESPfQqTE"
    "jiWorRlvmxl2Skf0sTLhqaYyc8H3iHptFy1O4Bk16q4iffplrZZEgOjofQ1rHXr4tlaX/PBjrUb88EOt7vjh61pd8MMvtbrhh+8Q"
    "dpmf/qgJrvnpp1qd8sM3tTrhh5fERsEde5TbWE664zYCth0C31OisIjkzbvejvYvIeR/a7tILCfBCrXyjNvOcHW3LtRjt6lty9JJ"
    "2ZJ0XDFnaV9bxODRlnmD9WGw9dIKkg0xa/NbMG3Ym6WxibNbMZ1AAk2pfJcVuKWycqYa68da8jo9LViX2CtlMdlvBbigQgpi9q+Z"
    "7DfM4Jg9Fv9YRjVLEXC3XdubdT6awyx5ixW7qsw+Nrfl390eRXd7FH57JGD009Ad0lVhj7/LMjJHjw0fafzeGLI6TnYSdrT/L4td"
    "iXB931QTuQY6RGkoFFq1guFwcfKyZGLGkaTsWIoTtdsvw3uinOk9t1xBpwJJDYy0tDUGxYjNo8NS1BObhh7VtkcskwydSQXnrfCU"
    "ar0obosS7sdNCAu4IG9dcqEM7yP0U24WMVlL8mtdX+rTFnYnl0TIIMJKGl7aKlwFss4ewbSP5zRJm6RXONNSWDv3akoleJhARuKz"
    "inB2rgkx0patxLKM31pceyo5N3JR94MifxgoqvAem0zcdzc2O+QcZ1ve73NZolf5TqAIW2+5dakIrXunNNhcbcy+jWjrs3twQQ/j"
    "2G65u+KsgCQWUtCCGASoJ0FWgQfVQpspwV8vRWKfUcTSMR1zURgK9R11mNhRfrD0zE3hqRx6Dimi5KRwFM1J0SFpTgpH07gcQ9TQ"
    "u6VqXJYlXnxZQ71Qgidf8GUZVOuJIC7Wee1SKyfFLrlyUoRECQ0sIEroTWi454Uj4miODBV3WwSE6kVXhN1mOnPxOnzkF96tmQ7j"
    "konvLBW6Dwgy2nibtKEGw223nZsiYhSs6C8oGK+WVBg1Du8prg0FNEYsHEo8aWsTDjxntO1tru/LG092pPVZ6Mno7NxqtbB2wnno"
    "E+xm98P90huUCT97t/uZnD5MQ3SahgSVo2kiqMr+upmfwN82y9bwXRq087xwmlw9q2/5oJV4S10HLuVH5E467grA2phlz5gw9jUI"
    "KbUXdHmlkcKBCJSDjXDLYL+ieZMDGt/ll4RG6MSjFhbstoV4lV32LiGMth9dUkbHa58R1t/kdbmThN1Q0Pv3RhK1huGfoLGz83Cv"
    "UJXBXqE350tj39x0kHtowM8Y534y4597yXLx+D2rbzlHa134cNuO44izic+VDeAhcmyoZ1tCqXctltumqLknxYrgMsk0TNClKqiN"
    "TcAgzlO+3ErXo1UxTb6HMtfITQudbiPBobVi7yU5kSq1LKn1ZkLrOHLOdzjHOGNOZhVHsZG193ijMOw8y0ZsLm3vrVo192LO5saK"
    "Ea6kwGyAEqS2aHBZlA8kFotyidFcvgbzwjSdL+KyIE4WEAiY8WIgQOEpGTTpUq17uvnWg8wOhoT1u4MmIYPnuGXuJAYwdv9zD37B"
    "553ErZw+kdg6r8WoZW2954wmmrX+N5u3UaiZuwroirRgQ5PeYdYYw2t+PeKQlTbaSNXvw/fCSiGoKX5gWM0OouYDDwVprnJ4b13p"
    "EdU/GqVz1VTRKtBXoq1WlebIw1xXzmW1PfAIKHA/QCRphbotGKmjL7BiYvAcNBmYZ/jEsA+x27ad6S2cYxwzs1tVr8qfivbKTIun"
    "7p4Vw2dFOh92XCF7r1uUh6hWTkonO/iZWN+p3wurKNWKTyTqLvs6grm7SzkQQRMIcLy+dv6o9NkY1zQuYcxXxZSGq+I9ybneSfdY"
    "5HXBl5gSlow1nAJPoaH2PaRFcp/A+5z6SZii5ktLNqBtMEvRWEibZMxxY/v931lybESL/0NUHcc8RUSABfvvqi1vYVy5ICPiaOyq"
    "Gcg1MJfLudwUvpzl/gvo6IyoXFp8XJSb5xuwAefD3hwW4PAlZdJzzRm0L9kMY06H7RcqtzZbVOjR+HsCp/G5cYvAZyFfTWAW3BMo"
    "Ca+3axIhQTTzFKZhF7BbKmnKOAcs9qsn/lDccw9VZm+KpB348wBRmAML+cIL/13MS1FMkF7Acxdhyonxsd7znnhr5z2jTE3DsOzA"
    "nTHv3UYk9NshuIbWYjbnpcYmuMhBQKuGzhezdvOCdCkL9v3eV1uvGNGbZMyzGXPXyAhRjSg1QuCqLA/5FAik5ORK0NscDEr4eUW4"
    "KdTB6hyVPUJ8vRxkFITcUJoS8DxGECbefQwLWUvTX+vlPKe8T5H08FO+LeC4i2eH54O2elXdwBKJICx+1DoBOsuiic3REoVT4jSG"
    "Sl+WSVyzQLxVxsmwYjaaTtAb2kocTyIxnIklSlgxm6/lGiUXdhOmGJK5FWauzIOQEM7lglw+LUO5/YIl9VddWeUlNERHKfs4hJt+"
    "Rm/iR9urm1pZWbHZ1IhbNbxO3+bRysXHUlM1Uwu4m4jhrH+ydXy2Ji6QC3vTtkxHM7W2g7GDk0FBqk25YlFONRlj9mySvIXHh625"
    "c6aVdTfN6aEasUgOXlWpqejEmMlfpNfYB3eEAHqp22e6c59/F6vQfmKbXgy1B/z+/wAVAZb5MrkC2XCX/llEdxxI7QKGIBfqTkmo"
    "KaeyULLvPPhukQLGiIY54AvOS+Unkx/LSMh3MHnlX8Ki3lCANf7/VUYXgb3EBYHaRacUJuBC0VqO6CnQ1CvENODQKl//hetcJ9KS"
    "iN+/59AHEQNSp6zOvuis7QvtnuuDYjY2CnsGMcJp8TY0xOpce78tvD+fXZmaXLJyJBV4e2GvMO3dHAcllPqwBtDUJVQXQ5LFmkae"
    "i1N/Fjtmdvcv6yumhGuze/8X118tKxfWckUfsC4eYX9ZBG7J1pbydfY2AXMN0YdWa3sFFjhPcRYJ8BROtAZs54C4zWZnHWTjJzM0"
    "PvH3zOKGYPLUOPqd9I8Ojz/vZE8CS586e19E8Lc9R5iqSrIfe9dFxvEJuKrm34JE6UDi2yISG2VC44Rn5/5eE8FVw0WPCF/wjWqP"
    "RtRrBg+JboDiftY7ZNeQFfBxnfWqzabbU1NdEOfpfdH1ChduYokVbLWUeul+jR0/TV3nx/Ue38c1ZEo4Qxmr0zajMQPD5GbMpQ/V"
    "SWO+39tvd3orAmLRsQovqQWwEWwZEHkN0W/vOYwHizhh9xCBP8kiWsupoY0TFTpGrB0UnKDVxpN16A/e2loJPjeF+ebXPHeMosQi"
    "MCjp1EmI5KM/teJIySWbacLrmNEVljyviywUkxgniz/8fY24uo0Xjp8KUC/fiOp9l7H+qYjVS0YZfxGr+6fCb9Y/7gkoH3DtefoN"
    "MbxDQ9F+JbL4Zq+h8y9SBTTN/N5g/DEID2gEuOVkKEsVuKE1JJpthMi6OiuSnxAdNjFa5XKmFUmujGZCmgf+D7tCdINHCnP654Z0"
    "WHtcwgJiIr4lmjAI0W4XCc8IRQjHo9XTQ8BwxO6SGIlU/cCwThZlL2KQ8Bj3naRbZcVZBKKrg9AgSHb+z63BbMVlJ9w2lEeoDLyo"
    "55SB05Z+0im6fNixdLih03fI8/szZNTwOzQVRWKDcT5Sh0FI62A5mU2wls21t46Tq1YoJK7Y3xvbwBNJR1sddUMxAfYLSJ9kom+Z"
    "nzuaHLoVtX+VK9rcdTe3WqNaHJAZbhVFJJohfblz7ZvHrbTJIg7zQY4rNRnZXOKDWt2Wxui2BE4qCxvnwvlVvgcb0AtWEjUi7oC5"
    "MRxlirazhoQMoMk/Heai/DNl1emYsXiv8lKSaZzVZ9PzdJ5EE3Nc89t9KIEmteyhfn+OyMGsEi27aY4eHvLFaBVE1kXk8nSCsBrd"
    "c6u6d24RU8qR4M4aXgvcRDSqgGUNrQQ0Sho4DLZy6yC6YtHVNrUamqLqU/U6bgChoeKu/ax2ee0cvdtilb3+k6jPhp6yLmdgWTaA"
    "YtnXOfxh3bFMKw6QgMVXIDAKXjIBE4JSqyS1dh5NC6JiOD01UnhxSU5sUmS3TA11s8GEQ07APWPDWHXJEqJtRZhNqN+ezoBGk+rs"
    "6JwFiHAQSiQg/QqXLVrlAQFcM0L/9SOs778K9opQONScp0X2a5HUAy8hJVY2D1jfypI0ldGFtTpNc2D1GSSWy/tsL0edXC9TUdA7"
    "o8U8T03j2P5NxPNB82780YoX9SHrwe4ywfUuO9t2mOD2bzLBLUNyb0KzurRjEkY293GQS9HDnsQ7Jq6Te/7sStp7E45/8LDgS9No"
    "zprv/tb0niaEw6cysw/5OsVUxioSdTrHxpuyKBkC5UyY1nKbGKkyyyX4pjNnPx6pkJ5Tgrn4IwEbHj1yYjQorhANISoiLStLD61q"
    "pXGiNIYPParUkBDIERPkMbt9BNLn8eVUi8QSYpXroALa74fnaa5qgtm0UlEOprwO9mjsVr01gSoW6dlczRx91l2VRawWHjc87Gga"
    "B6prPTF/A/TrnDV7WWF0LIYl4xHx3/bZ0MJj1XLB4N79bR4nZ+CYY5qnPHCAwOyBDxrQGh8ZzyJne5RHxvwodF0sLvyPVE00Yr7j"
    "RIeNz1glbEexASiM2a0O7i8cAsTEx6xKUOYI0QyhsoW5ooscW0ZGXJZD89GRrIp81xkKxDNDo3ds0SSXJ9I2D7u9c/GE0GA9zVyq"
    "2B8Q+LORhKr2DZbrFyqQRXpC8HhRx2fHnj8aDXUW5XlknTJyiFsCotHYnuJ1aNJIp3WRS1BZ1XDbPiCpId0LI+5gDrFi0ZtogBV7"
    "u1ByF2rCI6x2D8hPqD+5Eh0Kei8tT0VLK1wJlP+NEyaQILmglCZd2yDSR1uDUneIDUwiQJ4F4ebSKCA6tmqSp7e5R+PzPNgEq7yj"
    "QoNXQ3XQJoUp5hAXAu9/fD4aGXRsPWdWxiOpZY9xAsGjJdPixin0jkfIHY/LU8i4OGeGJ/MNJyxDf5MLFbqivEJZY1iQXBL/Iv2B"
    "pKyYGA8PyQjrdC1gZB3p4boMP5X8uPCrE3kn2qzX3vMpaoyJ2VOxFR2LOzATYbdIT9kNL9/+5KKPoayBcxv4MkjTg2OhYKHBudOO"
    "K7+TThCEw+h+6m4SrtQg+GSrnN3KJRLC/XSJOfqRmiylLYcIhJUzrJiTuc2gJ2KU2VdGmf00T+7snBuPmaKsfpInF3szbvJEZ9kt"
    "27yCpAvz3iSNth8FTr9NEbstZv2j7GRPMcr4IpvsqyCJKOvzzWbGvkng6S30Md4pq25od0ztVWyePaujqTI6bjMqBBtE1WuJLbA7"
    "z2bab+AogAsL7AkC2qq7NIx8HPinho9L4q2JffB2LeKUJzBW8/6jfSl2cDxxEIKQl0EVhLovOk1q66RD2psG7W02kJ0zqnINbY3D"
    "APu5RO+wnjPP2UN3x9U5PKsGJdgVeARPuNp6wm23ncDP3roZmuXDuOCYrUT1Gk/cmkjnKjJhntkp105t7kzaramUmhoxmiyHEDzB"
    "C9d9l/LusDYmRnyd6vxZ+2S4rx7veLK2C1jqaLfWcOkwKwARjbvR5v1KnzyH/7A5X7OzDJ8lL6MLfVmUP7DQHMqOlgm27uPt5aUU"
    "JvLVFMUZXeru0Bq1snMDcb8RTCyCvXylvNAyucSFdsMolKlD7nI6N1ZYVN+i318MCvZHf9V/nC2xJQI3SFfs6fUmBIipQD+6MxUn"
    "ZNwpNer3OTKPyR0bFS2azVqjVjjqEUxP5QkGFoHJGg6/RczG3HL5aqk4uG6YWt/aC9aHxvYxpfCVlDAJppzRu6SeRTMO2foeB/+X"
    "XlGM6n2fRzPRI9zteCeGEFNc1+mSyCd1GQ+vs8tB6NxtGieX1NfLgfP+Bg8mZxc5LiIB8FMhW2DjwlNt+mIdqG0215vNCMPMxTEq"
    "xwELeqeu+/3LgTaN3ZtkF4DIARHouhgexgO4MVuB4OtSKJH6r4xLUaZm32Zda+5AjonrOkItd7l3HQWJpXXKJAbdZeB4ic9cx3wI"
    "wUekMXexdXDRdgwNEUBKTNuwEW72bPH0MKRF5+lkOPdC87nlz4hRPZufp032J4ErPcXJW/MwvBaGfNKtGAi20KmV25hEs+uMGJYR"
    "YiD/W6ndiBJT2Xp0tJbD1YZ9Nzi3TF+YsDLBrf6VBCGVl8uheNKege6FR/zoMr3qwrGoNQogX+ImAMAyY/BgVwtqJ8yVctUdiiv3"
    "3j26g6OP7BAQTpw/9eHaolV6KDKrqaF1IsIhZanrb9+9ftXvX/kXGzZpMYAahwEPlAheDa7t95fRXOzCslzviSMwVQ7rgMhWVZzQ"
    "ZL3jZZp3kJJk88StnsotzQqi1gpaRgt1xaEtvGlc/xg7ky+7aKBX8gS8Qt2RKzCp3eSg8hUi7XEBuT1AGGk8UBn55TKPPQ/x/+Ga"
    "h0jdBa4sqvQK/B5HBynMZZyzhUIfwPlVjBi32xWieeuQkCgDQgIzXAaEBKagR0N1FE93hqIQ7ASQgLJmAb66/AsANPq2bMVM//Od"
    "o6wKN29DU9F4m/gm3LwNhK0tflbphPYdIc0c/sqnKSKRTZwNMfGgRMuDKtxsJqHXuv99HGcLImyTknY8KMHgDDNkPnShwi1vUSZN"
    "oGjo4Kndlc72WDQLUT4n1LwgPEasnzAqIJI7n9UfE+pWbMoP3pFN0CGM7vfb8FCUyhtebZpSfwzWkueOQXMC1u4k3EKbb5eUwFRZ"
    "YsLQoUK/rNgj+SyIZZJZ4s/kBahveQ/1LVSIx5MrcBdXrOcyySb2ov2KqAtHaWURjkqmDSuoHuDhpkPGnsGJxSzoeJwsnx4SSBP5"
    "T9v3b3JWRlshJarAOLiO9uKahQnwwx79xTdCz6CygtYE8nHnIYxaD4KavDNzHHaV2Hb9EQq1e+SljZuQtuvcLCtgNDiwyuaGLIVJ"
    "ZrLqEqkT3GtwY4hMtNq36WTDBcY56Te5iIP5zGd3mawwhiZFsUXX6Q1I7ipCiBZo+jQDdtj0lRa3YmxVUBOhS0RQTYlUbgaTBkKE"
    "PQ74Y73g2nkTJZHhRWS2ItNJdCBC8eeqmsPKqAazInKUmaYKtQ+8xNaj90RLbTCkYHgYlFMdMHoUtvOw0Bh0/MXFPqQPmP6gP53e"
    "qaU2QinrIk6iAaTEdnrP2yKU+lv1mQiCKfFSs4+vmveJFrjhBWuPtpNWXaySUq2S2t5PN+aucgIWwJwul7kRPJc0VpYmUP+AWTEm"
    "bWxPSjdFEk86cItlXPh3XJELAHTcfWbsbKyIkzniQQ6N+7D088fKZGx9WHJRCWzVdDjLJeKUarO9HUvadAIx4BzXHiqapvfi+XyU"
    "TprylSXtaGnD3D7OUtYMU0v2aSo0rntKZ+qandctoqU9epY0O6cafus0HxWKuzlDN1epPUl/BLwhjSmvSc76BH/VXXu+urM17HAR"
    "e22uSoFZboyOGSuxrC8WCZ3biJ0mqz5V7AxiJrbfxgHh69poabgpnvM0Uhd7C+aAJ3D8/jF2qaJjs/Vzp2gIz3XcBQk7azKjz3nT"
    "2kSeLfEMOFwgTKJx+SbuYnW2myAbntbbRtqa8TXZjK/JrvLm9CqfVjdvaZxRbJPFWIbR+CnoMHamJ3OSOedqPCdWQ8BcKXZ7bhmD"
    "SoQfwSpXQEliLTxBGIFi79zZjenE2EO/pphGzSsahTj++J9fbDZTdpozde7fpvdE41SM/Rbn3D79ogfdMBuqTctULAy2CAvA3NUA"
    "lkHu3k4iDPDN4NeafR7aUrOZdWuTWm8ftAHrlXHgQaC4SnnnS+qL2VdF3d7ZzOFqUBCoreB4kCOyq0kY7RI6JQhz5GFoDr/PyxCR"
    "d1D40N4YBCrQQ23xJI2bES4vlWhsmBtJ9rnX5OJa2J7plMRRa39nLctf2eX0u31cJe0Mx+zpkJrG2LNgNZJDhf3ssgOiaBZIZBbG"
    "wnxmeBGRVa4vQWtPd8VL3tPpjBd7ffVXxbaL/uOMmZt+/xYFGVKhhjEHtU9MEyFMZGcL/NnbZGI/ZHtYquyxfAoyb2HkP7vfwDWF"
    "TvfIY4EFNpu0hDQ1LY2mt+VweLbM4yxFyMnBooCy9hTYV3TChssns+HSc0ItO8cE744n5t35gbaopl/ulyG0bR+2q6fT7NbL8EGw"
    "zOLkJtoVCM9oGJcfG4Z0/bDbZzuSgyPq8PTgSLq8epIS40N/l0PPwK1E2Wzler+yvV+JaOU139nF8bVc3e2OIlDgGq4ePdp+vKWZ"
    "tPSRefrPWpodHKjlwQGjuKczYZ2fwHOsILIlnLml+sk0g5EwWIXCTQF1yaDNj42auUTfrsKw3CX56ukydmOkqmj9MIf2GobKetHr"
    "Il2pK/p/mZrIQ9yJVXol/Vj5UPUfXQDtaXpI2PiGGUlqJYrLI3VHi3+RLg+uaMy3kHacUgKdEOJM7iI2bR5SmxfcpEaHDRiv0oUM"
    "ZBUy9Su+tr17ml7EaxpgaUc3tHzgVsTnrCro+hcX6SXrYZTi7VsIYmpkRAMeYcAjuNsjmlCfjQ6uziXyHS96ezY6B8Wbjsw9fuH0"
    "YbKwAwm+LfDtikZbPE1Ps9O0SG5xnFxzPcX5fcBRd9Qud/kkvc2uCN9q8NjStRO/VVbpBW2V1VPM1cGB8/nwaKXE2Byc5pl+dAQF"
    "Evoh6JpZWov2bTGUiaVRZQbAsOmX4S3QLbzjPjncbFbQjaZBZyOMDqWO42REjUKGOArJaplaczNMgJxbZ1CB+HzuFYdXAUKfWnF6"
    "/4t4pPd5KbfBF5zHYUb53mf+gOM/3iv0xefxZBCEhiSWy+VOxN15FeXCdHSVPFahWgr1aWWDBFL9VeRCkbahMT9qvMnjU3P4djxB"
    "HRPxAVHSXNglTH48D6XcvRwBKjLbnSSadwTjEMCZLGVon7kRY+cgfvw9CkfEgQcjH0sCipY+fswE4XtXlsIESxrYSmUNnMXapogp"
    "9O57ERVl5OItbTY96fIwTIUzRxNjRXWHp7NVFCcItcYV0osChRfBW8awyKDEhnOLQ4vIjPpOXHs4A94oPEUhF7DeNRMuYhsPZJN7"
    "opR5AHarQHfdSpdpcom+ekEs+i0c+uhFBXKDoTOa8j31ZgMq394EyzU3aP/Gee9gqugZ4kiazSW0GSgknMtG7sFTz9RQe9tjAX/U"
    "DgKrF5w/1kJxBdIFHA5Wy5vI+ygcJjY5SytnhMZ7r9kV9YhdUWAvp+ydsMvJyZoLMzJC4GA09EV80dmBwf2qiH1BagUbz1o2BhaY"
    "26vwVqV1knMpOeZWPs+M2nAndOsNfBonMOydB5f2UCN9Q8Q8xFO8pzOmsNjFwpFg29yEmuh/9vhzgkzinVlAzUTcxAQlJfYK+hxy"
    "AeUcuZv1GO6ZJm9AuNlcEfYMxLSjcNJ2h+u8G4z5uikSZXNm1Bicn1s7EWs4hRtOe1dbh/iyAKOZszXXGxOoqFfE6zvdmW5zgUSo"
    "Z61Z36JAsXD3FZ3QNEUnNE3okL9K84xDSCSa6HYeaZ4tWAnPtJk0kBL8Rw2w626e10CETIW6dcQB7tIh7mq3KbG5zCgq4Xk0u1Ab"
    "crx0Oq5qoBWDhYFP1N1OUCpz5/1XF94XO7Kv9QUHEWYmjrAn8WeEZMxZRGiGMhu1gKND8W84Yvk5/RXpxFyzLu+gaaslTNFhuu1c"
    "vdOUVMqIzpKKvYUGoVMsa+aTOh9ASEAwCPViwwvshn+UyJDDlfNGrpivxiBv76NRAq7OnR8BwLDyNygVHX5MOFbn7u5zq041A/Bu"
    "zByrwneq/yLOSDf2jfdratEJGFDDMbfszSY3IVZZ5gn6BvGkfg1MTrIr9myzVSfhGv5gBGxe/Dviie33QSeYF4Of2ZKNsMi1y9hs"
    "xCUdanNF5A/kFlIo1Vuou9jXTJB1ojuxg7JwKuBx4KccwjvCdOl6mVwDkq41gdKIMF/yXC3aZEWvk+RGLSfJO7W8mMARW5mcalXB"
    "qeI7rZ47p4nwHXnGKedpEd1AQ3JtDChPtIvzTAVEd+DZcpl8KCLKeqfDIDvTPBJMpM052m5Dv4FW10M09sZA5cVlKeYl1pjNaHqY"
    "InlZVlA5q8qDW06VgGnlpJoyjeCfA09KVy1URewsBg42ZtQ9EbBQB7ETpXslwr6YXfXZsXLBFD4H8W3kqOnBZ5/ZHHr5Z6DNt8xD"
    "Y9oI1rSaXad2Q9dz33utx1OBS638nrVzINooAkGGdUENtyf31InrewrQbVqLpzpoFQ/zLtrs5ffvZSLCL46UeZIS2Z53lOs+O2bf"
    "EFxfSqwbfgkt4VhqeVvBRDr4pCf6eIucTUZQ0lwJnubsY6KjuHfUqVqKu4pz752Yuw79nsjnhw678tDllFgxYr+fHZ53hEkON2EW"
    "xXxn4u12JuKOGMR4LzUGhQi0UDrm6VzBm9KTSbxu2bO4MoFK6oBpRNV5x5U5sVv5k2oYN2n+qHr69IgqKc+ac6ony9Pm0VFSpc1w"
    "8gSp+TmbGIBYibgJSqJmaSywnOHw2Fy9rRqtcIlhfnDw9JBOKJSrEL8YZkX3Hc5cdmdqN/4O65PEPj60v5dpu/cyWZtcQkE5cPuV"
    "2+hR8V9cqWv2j26Os8B/lvs4vIXxKD5IHNrO7+801RQcG/fCo3nn8F0jvOwa6jNhiniaFi9ZorkujpFNTeoi95Gcp3qm61pPmd0K"
    "vR7eGkTBOKx7H8P67a2R/jbO3kKzbmCYSCnPSqtE/2YnwMTsEjTxab6T3N4i+WQ3ebJA8s1ucoNwGepdDquR56LMG/hliDQjqXe5"
    "dIcKaImpdBYGZIBXcy7DVAsVepefOYt0AlA5FcWHT54eBT58chOlLV5/nz8iklU/Ieh/njPypNZCtVnf3LO849p8VwH3e9pC2fOc"
    "GhUvO+id+p73FWp+njsvNYF3q6+79k2mcmrpVUcuzXY93pFBoNkVfPI2+KT7we+dnmeAqmsoLEIjm73NJKHd7Ou86wHLokS5OAG1"
    "wK76U74VFwjJ04h92msobuqM10r9gFQwuPDrOhshv+UnAgE6L+FN937wCfbzOB4/0l41gBf+kh3+tCX/sF+zdZG8osFS7R+o3lnS"
    "65XbRAcbgadQLgdMcEiEe3D64xIu7zBh2xmJzWFx8jqYHzh0tM7G8dwlPBSPqt9/A8TE3Dy9/MAvRqkteVt2tSFE48yFiAxM1kWV"
    "3VkT85tVqbOvVqFO3lkGIGycZ8KEFBQlVMulSRmOLh8+c/z5MOFZULwxWvhwiHcYiCHyQAxRq1CxCd7Wd+QX0gnvlVpG397S2m29"
    "38ToS+jtIFiQhCwkuhp+x+bFnxoWWBwYK9Do2aSIiJg9TuCHSLZYr5JtRsVc756CsOiDq550aAWE3LTbkX0qsjeE9OvAruLr/K+B"
    "x4RGMnrJDxGqWSOAoOKtZsmrV04vJDgEvszZfbntd276XYesCeGRM+phAbEOm1bTQZzYLnPA505gRVWDp55X1k8qb/DJ5Ptl28R8"
    "FKQv2LKHPeRDhQ2uxHE9igilLRtBXMq3rai4pc85GM21mLP93PJvT2KphY7NWtF2S9+x31xhyNil0FFyx8EUaDUTBFyNEa4C1lzZ"
    "5+z6KztOXOyOENVVguwCXNdFXT+3JgAjsTJx8rLwb2dFBb9LcbIbNeKVJ3sDV5nWoBtbNgTojquIYFNBfQJaaNl7+FOgBtuYvl79"
    "DVQhmtbS3pzxxZzxxdzhC4jRZjBmzjPjc8eoSDEiiZOzXPHTecI/4OwNbglUqkMUo7t6tOGIBAVQp/ihgwZsIr918YHNktcOZtCD"
    "4C3AEgHrHEwvXC1bk9s3WcX0eHb0RVJt8KeLTLom8Pcwy32lrQDNdHy1MpZkp8PdJQ1QbyhAdBjY03ABHg5iz/b7gK0wFm2An8Ow"
    "s66gi0OrAuoy6aoBwRACsqPcTr0R3QNpsvBVTdC1iQ5FvzAvti8Or076/Zpd1qzUxATDXdGmXfm98ScO2wdjwnSHbpO9jU5zZcUJ"
    "wU78kg9mQzZ5v3gSX+fEfkLg+jZ4C0LLdTayFSoHBMCFsRrNWC8sYVr1rQ3c4zisOGEMy7rcaMr21cbyDsmeP7sEm5475Rzd5R2P"
    "IK6B7DzTyauuEd2XeRhz5jB0VFQbObtVYJbjIggySXu3TI++GO6E2qLy40qkEXK50v/in95biDVOZ98GEp6nNCGIFHemjFg5K8g5"
    "9AFS1yWdbkOrDDca9ggAei8LcfcKG9P0VcleXz5DPCaq4VVprD0lqBAVSuGdi36OVTBLm5Sd3ARxu67YZNl1n7vmzBtbr9nVeqPH"
    "Vo3Mya/QTaMbZ8Owg36CnD3CnBGYnf0JlEdnf/p4GET5htZHQAgEfOZ74WX+lvfZwCXMsGOFUsfGRNBofsetUwyvrWJ4cEqemUdl"
    "Ms8Dd9jaO5eJ/UF5Zh7pC/499x/kOz64YeINiUpBnCN0v6FnLGdwELu0iGO+i0/LzHvDxW1/UiSFhffSPvQMjcBfFNbvO1SMxzYV"
    "TTonAoHD2ve5E8aKYfFlyQn/o84o7Vx4xW9z8Wb6Yx76TIUM0e7DHwMvK6x1Gjgqt1ZJaVRm5eAj6ByOgBBOeA3p5I/5o0fKeuTh"
    "87awKnBlNxgK68MJPefoUCsgFxQjIjt+Nu4UxWlkdWFKs3AdCge/a74wNKJLzhQfclKRONEPX37wud7JnP1OvNhixB9xaZu7jFgV"
    "UymK37OxRHfuRIIRWjVwRtd1o2vZButI13bCO7v7F3xHEiUbegdJfggSzcDE5WJQgfOM0Xad2xWd4AB8jrXiGK91bJT41WmNZTaz"
    "ifzq/eaZlw4f4U7q2j0SUVRntZV70NuhshIlw4uEIiV4NXaqc/LiriXkNYj3ioSLieFg5OdiIb/mB7q3DD7mxyWbh2lu+mBWqb20"
    "D6Y+bX4b6aw7ySuc+0RrJtVWVRzaKwUQMExXlILFSF8Xxm8+ay5CK3Aisn04zVMV78+Xxm76j5wvYl7mCNinvsvVL/nQXJrDUJzQ"
    "bxQqVpt+ROKSTpzycCQcWB2bSPHQ3qbytXcxWIde5jm8ZQKPEDhft8Pv8rSNxmKO/uLN6btnb06ej06fv3v3/O3pCMb96F2qY+qZ"
    "L3h6+nanzEOUkaiquXdnl77M7dR9l4sHYq8Fqayuqtd4pBlgFxTqV5mX9UtiyV7mu0WM8qp3otIlMHZ1NT+XAK3gFoN4rJWRPRlB"
    "PFGRvzjm7L5Hu629YSOsyM0N/xDnKTm7kWETf1USIWU1WfOs5RZsiPsgxiO1AyqiCoK9ViF1I+h3qMMISnvdcplQRqx8xbgsEsJ0"
    "VcgweKeCPuKbBELvLigwC0aDfZwG4FJx4D0GT44drOEU+4qAjgjRQ3XmImgRyFXpHTFKqJyDCOPEQeRVqhsBtUWZwIQUoZ3AcVVE"
    "if3XnJYYPLFzX83JJS05ZocYdbbaFUPl1ltVytRtt4hm3ZoYNMbh5aF1KsXOAojIr99KjBTrajga/3b72UnvgP49HUPnXTshd5ob"
    "LxEVKytalzG1LEsQdbeyruzYc7+Li02NvSjnRamlySxsHqemjdaSuABEHqOmtBdaiBJ4sEFjdRX6zSs8WEhtm01auMd6aDYcr9eQ"
    "1xkzyAGw3OzxIrVs0IwdUVRWjE0rXEmAv1DiiGBxQZg4trYBaQ6ME4brYoBxruz5BAkhUlxy5TBVkZCKJp6iBEGUCIgmdlTLCMEc"
    "3FBtWW/D8CJN1WUkpFxmn7hBqLu6xmlq/yXeiLgk7jk5WIiNYCheU+zONN5cOHVS2GQOq8fOuNnDeuiNnN3DGHddk2ILf62yI32X"
    "J5XzNmq+MsEgpkVD3Obdm3yBG0T22ZPID1XI0UVHePE1zcPBi9v2sRMvwfZMwnp8a+F9ImThwzyMxORACsDxIY8OTEDVOs3ryxVc"
    "hTTOp51xmEOrfpwJ3PY4+sLv7Dz4rVVcwUGUvBVU5xLpOaqffpaVJnLw0jooFP5RnHC5JqEbaJih33Mr3IIrU/XWGgs5GKZOHxl3"
    "0rP/l71vbWzaWBr+fn6F05fDYzeK8TVOnBofCKGl5XYIlLYhRbIsJyqK5EoySZr4v78zs3ddbCcECj08fU6w9jo7uzs7OzuXaGC3"
    "6916p2tb00i4HjmJBvyCdwqncHT6nT0Dnpr9rqfxDB9jX0IB8jB6EtVom0SDk4jT1ucRQHhetd+jAd8FS0MTWgqwOeeBXi8IgONo"
    "MIUNMbg7FZWxIKnBYCDSI4DvOE2n/Tt3Tk9P66ftehQf3Wk1Go07+C5uvS3Mb25vb91BnWz68+SxDXRNjGgcuYQxHNNQfDBSfY4I"
    "uH37vYCEe36p2ql3AguNTI9HsMm5pxld0Z8lMeUunED2XkPG6+SMRh3nwnQDpWw7XGKGRUj0Q3vEdFWje7dgRCyVHiCykD7drx5F"
    "KE1MNcWAolJvqVSYy8KLr5/gi0Y/nyUlv+w26GFQM5vkMnH9BLhlfxrIMFo+Umdkkv3RDM5aW+TbliqLgaV1PzwYPUh0igmIITz1"
    "TO88eimeRkpF3GWP0D5CsfvYI4/4aIWW8eOjSunG21BOc+/DQtvKb8PZDwsUqxKsP2defL5PKEFBF8FopHEYuSCT0UDPRFJqsSjJ"
    "eb9BRZ4D2SXLe+9Hs0SAldbh4s5MhnaYHWMVlaQxarMOLVOD2MmsWp/J1QjreP6jrhnzUwmNmPV3uFbieaSZxx9HzJUfrUz7O/jn"
    "7q0Lb/4dbtS7NhEnuSTt7/AXz6efdt8TMUSgVZeNe4fr61KbzEOgdGwiPIjXJ34sxsyUzfSUGkUcgROeby8tD3iu7NbLYsSSYcMP"
    "omGkowBQrVqylswFnPTWGRAqJbC1rf0IdXX8E4d97kbqOfw9vSefAqGhE43JlJhEgP92k6TP1Ia4fzpLyKXWGnNrPIup1f4BL/6U"
    "3iMtxv4eWqS6/DCOTnbp/YQXotR7dJXOp7+MjDREqZNvgiUXtMEyMo2QvmGuDUotaILSzRbm1suIvd+cxICumrUXDdC1f9XgDAb2"
    "Sw3twonuSySANQyFesHv6fiIC2f729h6h1wC+tu3HkTECeDVEIgFd6mnBRHwqjwEDF5O2e+59SxiIbh5cRE2XPmrRxZH/O7r9ynq"
    "uEDmx0OC4z+nEeoqKz/lpPMBy4EiqxiO/NjiCQf2e5utnVgtDD+7BpyBfesinG9Q8gaGELTzCyIyCjFlD9tcH65RJI3s3FIJMJZL"
    "bp3MBlFmkYwHbnaFTHjjlMyBzC2XqVFIAGmsnhOjCACJ72HHg3sRujs+Ghzfvn2Mmk9v2a/moXURhfeVPUD/vRWF7Ne5+LWLoWSC"
    "gILJRiFTnj0Tv1TmviVaukeD7XveAFvjX7uDc/mhKsH1ZoSGsZr7JHZ0vfWMrgex9ZR40+G479bE71k/Ik+DYVV50uHVpeUA3uCp"
    "+IRXO+H/TmEboC9SVJrERa0LUuAyNdxFDDCnih5dIMPazgNAIzC0VgSs5/OIaYI+RQdZ3jDow331CftNMD5DlF9ePorInO0ITeFr"
    "6ikdEk3M4+6A5t9bpEP3JGIem+hfNKI3ccsLe55WOuD/zqg0m8NTJkgQc3BKZx+fOXFM66hq8Ms/Dox5/antPOHIy83JsPqE4/F+"
    "REKjKv1r8VSFIc8w5KiK2XjCZwMQdcYQhfKSt8TNI3mqnsHoUIwwz61EHH/okXG0fquHOiPCyDy/1FSVRqZK6sk65pJm9ykcEpTa"
    "Z4XmuqJRJDTT+MuSUB7A5yURZ5MfsX+gcQ/hr2bRb9qgtUNxL8c0wYPCAsMLtFIL0m92E89493rCJUNpHQ4FP63eeZOs3zFi8NJl"
    "kR49HvtJSnG8kPxXvYNdfIln/w54uLxajRdQPTy9ag/c8iKtSVES9sAfypiTTHxECuuJ/5cnAeAmKVrHz/mwgdVM0nuCnXgYA+ln"
    "66o4y8N9hrevh5H+tvEoyoZbpQU9fjQerK8/jCwuUESWUmRguB5mZRCuGROM/Lh/4kWzlILLK4+NkZWydG72z57e3fngMUMi+VyW"
    "/pljacIdrdvQo20xO1a+aRge997DqkG8esCLVtEW1nKQZk0GKV3O2IM/CxSwvj67i/btaOu0owHJLKO+4zlWst7E7QwTnW9c08cw"
    "ZI78fgxd7fJwn8xuHzYHBUyqYshicmLIl4ltVWxyflyFA+ksmj9AywsbRYUyhZ/YNsoJX0Ts4SJh2fuqgqtSVIUAK5DTlxkTlI8B"
    "cxPUKQVMnAE/S2qyM/gJORHkCHVDdn3cj4YBL7GPJWDkA1eWqI65zbNzhvHUsI/x3Qa0GQzPov5+xC7Uk8FsOGO9icb7oo0+d1gw"
    "HbASt2/feTOqDvvEJGOoxkuMvAcJ1uWt2h24pyVpVaBFRDAGTKYRf3OVD8fCMahYZmNtmU1QAPVS9NCfahTkBZ9LfodgQCovTjWP"
    "dGZZgE55E5Y4QN6PnC3zI/IvoJm1dfhLbJrxkh+ZygNwDZgBDzJs9BmbXhX6AQ1ro1mT4aNsC/6r27Xat02vrb3pa61VUR0yOoVl"
    "+kCINYR8o1YfReNzlP7Dkv/B84+O9dfQKBtcBGkRRk3Dp5MhkFqM7XbYP6B/avU/Ij+s2rB0SZ5Jeo1iJ2o3fv7m3A+HmWuu8EOW"
    "Ih9Mv4lNT5noTb8HRWjF9UpPSY4h5bW4GdnJcXRq61FzkZ8nN1FoqHChKxLO4Rw/+IHiFdBbtbgi4ASEcO2FO6ndz+Qh35TC1W5k"
    "sCD977lIW8TnXdhpSIq4IbcXpXiEzDmKVsuKgjFJKjDsit5ADA2spWsDtBGoxsN0WI0zwFgEDL3gyi5q/ZgdnZBDZI2VaQLRF7CT"
    "2ZVmGKgPoXYhBqjJp3nSRRZ76ZCw2mc4tLyDV4DiNTaXP6mZg1n7Mxrcgd38++VO7U3yLa8Pv/p3VC8/Zlci1y/wSUmSdBV5yCI0"
    "xSO99QsK+J1qlh0V1EsRFHbHrmUtGxoUw5NpI9p9yOchA3fQVdlw+EtErpBQFCON06VKBcal9UQhj0XH0INMo0wcVxQfnk32GWvS"
    "NQuFlo74nqE2fGyjjzFAUdP5iPmwH6KJuogqGwHfx4tGms4KHz86xROikPjgJ9i3FAxnfQAjR8XjGC+HL8mzCKDvz4jR0VA0lDKv"
    "wJmtyxU9dn6I6OaJAiDmKCwkVgR3kTOMxRro4+zSxJPqp1gZbEXUGJ/xK0w+zPWafzKN4tQJ01varP8iZ51UjYC3DSXrFA7uymyl"
    "XRIOh6S/ZcSN3NiA3n6VI2RkR491L2nprxE9xtgSGpyCbGkjtvstzpuUNu+Q2eGSLsgihcndf4sGB/Zrb/TOx5ehJ9Ff8PcksQ+t"
    "/0Z09ZeRAQwO478RD5klffaH/OnhVAStQv2XiR+kpH/O45PxslR7EO/EgwihzegU/RbllIr8wW8RHF/rMQkTC9ryC3RrvEQxkUrt"
    "3jl6yiMqvNz75eW9F3v3SEkHE079cXosopYe09mE3iCPyGgLLdxY9I80KZH0b985C/zwna2QFia6wHQwIkb7IkZZu75gqBoQgGFY"
    "doo93a+miSXCMm5aghuo8fWSLYjOA0KhD4hWV2ceWyrZLZZmG0BrLzyB3mJ5ztFgY/pbZqLbSnDDY1vKXwUGNYG2DcePtIwnHYdM"
    "leFxxHrRDZEx/CefL+EfVzptRHNw+/mLZ9+/2Nvft8msTFkRbthSW9yhGJjPXz569hSDzx4Z5z93+ImcMGCBeXX0B2oShDdr99hz"
    "342iMziagaEFMtOXiNlBUbCPr3fSbSRdk1hrAx+24rAQ7XhFZ2VC0/ianyw8Fg0HRgxHqHZS4J+BruAZDmiK+1IrjYmrWXAR1P8D"
    "MoVxGdjjnGYZEpKNG+qH4+MZTU4o3sWiIqrso2KEWg2+ts0K7incH7ks7hjFi65NvAZutSjRWC7P1y2ykiTrdYTHZPAOooRdleFf"
    "DM6EEXc4tYKdF9UiPjexpKsHoQVFZxRvLx7SgOCQQkycJMzFXMKstB2WhZ6LWT6/CDNS6ibAWKCJ0+Vz4CX9997lrjOFmfVqt+5Y"
    "AWT+DpzUEFiPkjLa024i5a8Wt1yvopbHCelJuAlGBFkLEnYEwCWgxsJGWp7BW3CbrfCgeSjIhQVjxU8j3Cu61RbSDO+ghU5hYJEP"
    "RVPtWp/ceYrIsjUUeOB4xwne45IBnD0nfoKTSQpg1Zo1ZS4VxwmAVZ0kytchVqlZD4DtrIfRKV6VlCVtYqjNMNvyNdwlaVJj/wxU"
    "RS12MeZ8NwhRNQGVa4xIz/GAe20V1rdKLQft8h+dnHhjH9+J4fh0jujCulOexS77IXvwJgWot1h0ys3t2UkVS7tVZ4CKpubh5su4"
    "S2uqtjrogGJQwCsK7Yzru0tuZmmwRyHxg10m25LGL3w1e5bCwGCaoNkse9ZOmM2je+zEu9EY9nG1gUEFm03u01gmN1lyI5Pcqt3d"
    "3sylfddsta2jRPf0Jr15uwNfPJXRFZ/fs4Y/M6Ghy1+FGXM3/FEEMOiTKgJeVy8vtd0NW6+KIYqxSh0omQpy3KxZTWiL5/2ezQNS"
    "91ZErHBrNbiy8C+cOH6umIcGEDbdMTB9EO33xuKTPTbDN5Bm2Tg6lFQV6UwWoQuAaLxnCxsVQ9DAVDhkfBw5Y4oIfufg3sZvh1yw"
    "gOXWkOMAgAneU9Lhxh4QD3SuxjNPhVN/i5/sdTlmeJ04sFo2xCBwg1AKLwPrQkOKxuC91QgzKZjx4J9rKxzvXG0Glu1xQjcH1Fys"
    "yUM7mXpBQIgUlcexc3REUaJEa3jXJM0GnoCyCDeKY+ZfgDXjhGM8hcncRfFxjx6+uPdkTxRCcYr4HcCRkiv99Pmrl7JXOE6zBSRb"
    "KBDQlOMoZBDlpS7Lqjx68r0o+/OjB3vPxMfuvac/39sXX/vPXr3Y3VOdCUaWI5Js8taafYZfzdDapJZsZTFXjkg2QwW8xpYLs1bS"
    "4vET5nMN2g/l2+ApizgKm1GPNBvW8gWYQXUClwc3jQO4NCTH/gSvEE6Af0+81IFLxCgZXCCRY3oK+Esjp3hQxN57rkvh1fkHV3mu"
    "oppCMGFZTHDKIrjMYtSEeMlsrbBzLLKGypJx8JN3bhEgPI1+YyJAxZPgFyYggDwFf2JS4LF6NrA5KTB6bEV7dfaJrgSsE388DryF"
    "hZpWjAtjYZmW5Z05rtT+OE8YfuGO6R3QkyCAYx+Stb4kUPjSYp0l8t2MTkdpWS8VQd+iLvyTiI5e4AjQYoWJyeq2MpiE+58IC12t"
    "hiRV0x3AMJ8Uac4nRTwYJQdozyCYqRi92IlnE7FyPdHiHCHehxXgJW7fhj8O7DYrmcK1tI8GUrNp33biODrdmE1thn3+jb9tjkee"
    "RB+2NY5OQ5GEv22LPVL0bTQBo7btubWbZIKwcbwAWlfGS8hxXLVhD9gkUjE5CwwRyXwHUkQc+byO2+Pycp9FG4OdUlN4YSg5TVBZ"
    "QMUEO0rm1iiqWS8TRY33EmXd8RJhDpzqacJ23QMYnQiMx6kPFq9LBy8s07ogiRozR5WuIChNKnXHg3cJd1u9FuvDQ88lb5VnhmN6"
    "HlUqqn5daKKhk2r5AcyPPCdQ5IOaTy/ZJapJMhldycnmgWCcQUgBOaxnCZ57UlcRKB5ckoFVhgsPV5miNnJSovcbbhA57zAcR0bA"
    "iwYRG+83nOmUtF6BJZtbaEYl0fwsEa+Cem/7P3/PO+QoYbyMsjZjyny8DB46vD08S/SGjHKiLa43pGg5TYGYbLL0FdLynOZWn+mF"
    "3pORnYHs+6EnpD/WHzIDiOOz01BksFtUYj2R+UqJE/0yqJLW04IiU575KNmDi6MXU1y+54lytcSOp+E9xkNceLIUmuy6UTjxj2by"
    "+zT2U/H7PZc21/rs5mk9VFsXyRGOlmn2ski7TxLGfacUpf05u4+lQgPlDxZomFUC/P+Bh2jtaXkdsTU1PuhRUmRT6fH7uHl2euQ2"
    "WsY/aADvZq6kB8xNumaRyY0Ub98uDOWOjWivepwlk9Fm8dE3G26PhShF10VrqbL9XJM9ybRUT6ModuT3gf2SVBw4hpCelT3xuiyC"
    "cWZGDtduMwn4VPLPw88GJhqKlJ/iaE06/VV9MTc4Ebq9wQN2By0F13DcB84hzBH8CTXIZGB6JmD0TS7HHeRwj9bl2TTuGCgw+DsX"
    "vXJKKeERe46F694gVR/C8bLe4AvvaO9siv6M86nY7mxtMDY6mt2+PVYdqUdDcgUiv7gPfXONkAu9wUTDp1Egra2G3SUEQOyVCQbw"
    "XtxUMsBCFpuvBOcrKZkv9bhpat2zFa4/Suq7T9s2GoW1EUDOU9lA2oNz2+SNX6km1mg3a6+UvHu5Yww1EBSAqVBBiO5XVTmcipSK"
    "QXrh5qVm/9L2UkVEeU7VOw+wG2SgL9cA9iQNlfljUd2ml3rdHS06zpAM2XcpizvMtFJz6izxID7A56FDFbZ6ruVrD66JePCQjvQI"
    "QyHCeD8hitl/kZ2jHxQSpZo16Y8LNCh9QSQ7uFJ+Zq1KkjWX1x01a0nWuMLYaAzjzK0epMYzPBEHYgegCP/ysnBWyAWY6uY1ZCED"
    "iIqN4vr0kPu+EMdBZleJJ6BYKpzFOwAtvo1hiGZ+80X4MWWIb2uD1+yLfDzX+pSEP+collFvmQm3rpb0IPbGM9erynM1JAfNaf81"
    "Q7l1oas0/WTcATeabMF6NbKCQJ4XWIPxYydJyYMB6gmxBYxZgUiGNYnP6d5hHW9fMcoDqR6u4nne79if2CfplwqgaccOudJpX9uG"
    "P+YmVNvPiYx6jRFCyVZaG9mvOhX4kXUgX7TuVDcu39buHCFHZwoy9d5/Yb3bNhyfYqbjwa80odouI3kdXhKlD9SKP3xFPUILONqD"
    "zKoi5AD/TDCi8J/eDw7Ju6y6UuDG4V4M/0wytmC/5RCT5yoILcUr+L86cl5R6TU/eeo8NSjdrYRcS2QKaswKuhFcEyLlO2/2Lyt3"
    "tOqeK/d4qvwoCHmzvE3IZQQEKizY1KlrrnCx4jUrPFdnt9h7A5/nN3fefFsd9qvDtTffvrlTO3iTvNk/rH2LH5cHb+I34Zv0cJ2v"
    "A1mpctGy5phYMVKrBxf9+WGtgjm3mnpW9WDHKsyorGHamp7Up2J9W7zUa29irrhI3L595+DN2W5j483Zw4dvZo1mA37CP709IePz"
    "pCbAxb2+LLzbZYXpb4v+dg6hu3t7rMwmfuyy3z3K3qS/W/T3Hv3dxTIPqMwD1tAe/m02MJ23s4V93adk6qXZob/UWJMaa97D4t9j"
    "cfzapb/UUIsabbUw/wee36L6LQLvEetiF7ugsbeowRZB16KGWtRQmyB69CNvo00tyi8a90/ii1p+LL626S/B335Af6mjThNLPWVD"
    "b1JKm/4SVjuEsA6N6xkr0wIYH2zC/wjCDsHWIdi6BNuzPd5jl2B7Ib5otF3CVncLc/ZFDg2ySw11qaFNauglz98kbG9S/U0a0ysG"
    "yTZCQtU2CZZNamiTpVBDPUJ7jwB5zZvrEZJ+ZU0QInoEVI+A+k2UInT1CF29B5jjUI09XHF7bMURthqErUaXinisDAHpst9sxbG/"
    "1GaD2mxQm2PeW4OmoklTwdvA1bbHVhv10KQ+m9RQkxpq3sfiR2K10VCabPEQZK025vusOVxZeyyTKreo6RZValF6m3r3/xDrhWrL"
    "LxrfO/HVs+gfwlggEgn7bcJ+m7DfIex3CPshgfGQLTCayg5hvcNWEQ1lysrs4e+I/cbF9hAW20NWjMDtELhdAjfyxCIicGPxRcjq"
    "ErK625iTiBwad5ca6lJDm9RQKhYbIXuT6m/2MGfGIMHF9pAtLULgJjW0SQ1tUkM9GlyPADkVy4jwds6aeCAIW48a/kuUIcT1dgWt"
    "O8rYjaSkuChIKV6/lVGTzr37bubsR4WxoXfQwFfLV9OpOOzXPfnUo5/7jruQdWCMw4Z5ADgbfx3WqvQMU2PnwMat1iLmInKrMgop"
    "j5XCVT7R/ltXGyMLZSXTGkq/Dv0YjWItUr6o0qNUeuwncwv9IixqAW0ckX8ByGN5qwhrd+/ebVhN0QiaYRe3gtU1u6ELJpScW26A"
    "lgr4JM9/Gaba4hQnr7D87Do4XNUXEBMuGlE5faHJwDR6NFWFy0tf00+opdIxr9Q3G+iuntgkmPxTXBseMJDj2qF4yPBCaN9DCSPT"
    "jj0A9gaNqdKhCluWSmHFMJUqtnWmxITYAn4JQ+XJy1SqNFAFQ6AZi7umx8+hpnav/yYTQwduOqiLwwQHVbv6+2WlZq+n63a1cnmr"
    "Zlv2kY+dEPugdFVrho/RQPFs6JJcsm0wzRwY0kwphoLJenRF2HX0YrYOt4Yd7us3pasBIYNb+9UMGzTBVyM6pNpcTcfJzFVSba6k"
    "TvLi1/iwtiGlnuIHF5xybWEqpDksp42ev1IMAQ2yJVQ2tuCib083IrjdTILodOPYH4+90EYP4WvSddl7J/ZRJokDv33bqM8VTXUl"
    "O7O8hcNat6dnqOue63yoMFoMh8ZFTspnsGzepAGHocOs/ZaETltbb96McHXpE8ZW8qUNA6lCtlp0xEnf4BqYls3b5OPMG0NQydTV"
    "rMkHTdgJDUZFItbM+rkWGb8Eyj4IqP1jz0sTuqebspIhasm+mAVeUjMaDYesIjlSE5oCXJrCVNBTIUrnwz5Sy5Ve/vHeK2gUl2MV"
    "ioSOXc30kx68+w2LvXX3G2Rfw7LJP9ngQKhhv/cTf+TD1J9bGc1s9LhG4NyPZuQ/ajfwAREvgChXKUZipv7A5njONjSwR0HkvkNt"
    "W4Jr4LN/8aKsUQjIZuBCPvuhCjCDg1zDsVUARligUnqkzn1GvuAaL2bWIkeDJuWiZ8YjafGf3D9/yZQEqjauNbsGXI3gHBiuPY0g"
    "omzeJWTxz1j/FJPCa/zAhyqqiO/Y+Nb24Vvj4j0kAxJnlKCilxtHQfDYmwBR0US379Xgyyi1cGnFafvUOfJ+eUaYv7yk/mobdAAh"
    "QNj+5aUu2Di/Vge/ig4E4C+jqdYNfJm9jMxxFxhJ1bkrt4iUMOM0sI1j9swVvm8bOkeEXBZbZc9ZaFQ5o/rilJNmWMD0adeRMIoV"
    "QMsrtroxBIC5epOBcSJaLltjRdvLCgaIVGs2wMmzxgNcwNbEmlonAzuNpvaOC0zudD1a9++OedfDKppXYWqw4WO5UZSmaOE8QX/u"
    "kIlRwieDaJ0XsqZkjTVJ1x1og2AeSmukhsXzZuvJhlPriy+LZmEoth06O0iZ06W9cDyY0mHaL8glN7o8X25aAGMwySQJy6pnsX/k"
    "h4MTtKCpitwTJ4ZEWBmDE6ZDSwMc4sOCW711AUT9zgZzELtxNEvhrLt1pzZkenbDod2CjuaVbysbzZrdX1LW1k++fX66ox2D5rZU"
    "nH8COmEnkWZZV3KhpI7V6kGKBrdMsQYq0vupfjjtatyELkrH13nxJi31I7QVtaOEfumgYH8Agz+YOnHiPQwiYAhSjk8iGOsFGS9w"
    "WWnCZP5DIy2naksByeTsuLa3/A/fW052G0ULtk3CNgqGM50NYphH2it0j8EQVrjunXVxvNxN5M5xBxvNb0U6VJV7h9VxaQdRIUqA"
    "jeQOHNik/CSDltj+iWibfLvR7LNf69kCVTN9g6fXsErD2BiuuTFyeylYvHFm4hKZDhYt9Z381poVba00u38wwdbvmi+lILVW5KdI"
    "Od4zHlxV2Gp8hzqOEnoRGrCfcCsu5nX2tKNgbU1nK1FxhbGUBI8eH8PNP1DyzUSOnLwCtZV+0fs/XCZFT0pFRhSUACj6oEB4huck"
    "YEiZ+TINEcgzuRMjq1pD8rGDPtqm6fmQ/4tyDaFREwQvnPDIS0gIj7/IVPUuKQRDS5RJ6sNkWSz3C6oecS8iDc1eQLRmXIrf0Uan"
    "BxkYAOFSkCASgsBFh5zZccWgKvp2qN8ip3M16dEJreMOZPqwDt+H/QPBSB3E8qKiXtNirjEXr2m2AisLIbwVhBB+XggR0pAWCCCI"
    "emu60GiNwWJpNWpD+9aFd2Uh1byP2oM22rpKqQa6JuJSDWk47OekGt5cyeJQ53wne/iYB098WIJR8aD0O6y4+nrtTm3HHxaYhfg5"
    "KwREFeFiuoEeV4V+7PQ+fgxp4cToiG6gq5Tj0yX3hlANpUFvXKsd5kQzhtJ5KGwLoSwvuaNKxhawCmx1DcQPOnuJh2DfZMFWs3LG"
    "U3GN/E5ojifEksdn09DkGCWbW+bgDIYd47tvzJ1HVakNK9YdTphyJtpTQ7YW0TMNAGwokd1D5Q6Mf3Co+aUoaoI/DdLUo5/IjC5a"
    "WsuEhHiquBs5LOb1hg9rbcACv08gNzG8VjxXjIpBEjL2WkoKyp47QzKYYwrxIgYdqbrbWno/7K+HGroeuvxdWHRC+OOauv0wSmF1"
    "OyMSrFYGlW82mt/g+z0mw20RxQZj8U0L6NvBN8L6FM1MZWF2hz2swZE3t/5V0f7v4Dj2JocLe7pmy34IbNqnGAIzgvgUPaG+KBz+"
    "zieZGGie3rLV5Dz6iL1xz3LemClDfqROSZHoQPfHj9KkWvGtl9pa4wbTt28XFVICkjUpqME3BR6GSz5TaMFmXF1LhW0/pXEtOYdh"
    "eNA4zEaZKeAFDR4+LLyeCOZsQ7+lhMBFjpHRR/HAelHGfeJVM3mjKB6jV7EpXTEKM1k9lq84TV3nbWUMaBEKM6j4qwAVZTI14X0k"
    "mvZTuncUiktKpe1SiqKVYfJUlYGRvVFfP2XXkDKBT1kfNTMXW6+RlGauwc7ckQi7APytkfH72t02e4lli+Oat9js8hDpfHUsusX+"
    "7AoffRwgujvsaCFUWRTaPhQMLfnCRH5ZNO0613hj0wf4s8tc+NypIjou2XzU7qCAFd0Lce3FtNz/D/nzVZuUC5LzsmJbyLztWg1F"
    "iEvL/bJqwV9RfM7kz1JbaJ6lTnI+zcuRV0d9fphgvhITzoskzBHBhTD4FD6NbM2zADYciyLE74T0GuqTcb98ZZzPVafAr2xjAU8V"
    "8GrzAqnwqwX3MfOxy7yP6fq+aJ4qtkNRA4WZRhOaimMp2WRykutQzZxwR+Yw6U4RYcQ65WST6i2gmt+rt0JY7+E4hutM7Y7P3V44"
    "7/0jB+a+Pku8+N4R0hRNMVJVRfPFUgfSAqm5BJMf11r+U3GPJczyJ+ckD3T5vvgivB5+CiC+Mp1fmc4802k8mPyYEbMhJdeluVyC"
    "oKn/qv1rA8DRzD0mdymo5892Ktz2JAU4cc5eYpHncI1PE4xPqeUlTzK5moawKzWEaxe0jSkklBABZu71IbO9+801vOL810Ut2+nM"
    "f+uP3yqiwGUnzLCi+ptroaEN/IsmgcA60Y/1dQtFPPNbF/Q51wR8t9RD2MEhDxsDx/729raw+HMGPveTgd4tmAx2veqIILLDRj+u"
    "rTd3VNxlPL0uWLRY9k4coWMMjBlGygUDXc2FOy9ZQxsjtJTk9lg+/SvdpHCgGpBTrEAOLYXDtUZfhrZFAaQOQjy3WEDm27fpfHiE"
    "og8uR/6LFqTVbCBfKDhajLLooPPyPncZgN4YyFOlXknGPmP+Q9GUnus3kfN7ckvFwoJZZm+kg27h2chMjLF4zJyaMQcfXjDAqbHS"
    "oMT8LizO8L3EioNiy7wHHjAz/hTZGMsPFlvvOcFS670oWNF6Lwly1ntp8MHWe26w0HrPCXRLvCQwrff8wLTe80lSFZXXUQLLQPYb"
    "YoGYalozBQ01KnxZ4wf3SCUgQuEisnlCoy6u0VsNmQKjuyzm4FqKoBWkMYcUzS4ytSOjbb0teYlQlGQclGjKU3CMYIAqh9Y0GNy5"
    "qB78Pj/8toZK7ifwXX0zXn+TrB+8WX+zgarxh/ABSSgjPoZsqP4GatQO199AkurvKFikJ8lcUhxZItwOmaF4fbtur3um2HaBluRb"
    "vQuyqUC6ai7Yqn2Le80ozCMHDQgZK6W3/j6ompYzBDqKN+9UskYBB7+/OT3kip+avkEgom9q/Bw0C2RZ6J3evv0jWkGhBioR6w27"
    "jxQbjzhNo6CgHXtj49bFecAspzTSfhYYZhnVqrTAuLhzBLQOLo9cBrCusuaZrNq/W2u6neh+oGxd4A8KfLhnLppYzUUF8y8IGWeB"
    "UiCipe3CMKdBTZw7qY7QaYBRwWxYStVbFzDa0EItW4Xei8s5x7iyrNEfGGJmHA8nDTcrqQmhO3rqqgFCX1V9wLBVuXXhz9HB1rym"
    "rPI9va/jwLIbdg1Wfk0+KnpQGqZFXsxgOGQjU8srF+8GwuBNzCvFLcXT0cZppeeTHX1yT4OMGietgwsszCBVL5eBEkkoe78xoCNj"
    "8af5h9MFQzhpgwYcieSpi4WsQ6fI6P3J/06qpu6IgOpoX4ZTV3VR2P2NfXlJP/6P//jG/gYHd+BvNA/RvurNG3xfigYYH9hl8d/d"
    "moUhvlkDVchOgCmhjxp+bGxYLMviD2ICBKTD9EglVosjVpZn+LWjsWNECsQvRw+wi/yyTScwjdZfX2cujlwAlD1bobOt9QEAiHl5"
    "M7RYu9uiDhWiIRVoSAUaUg0NnhKtacbTFalEbonoSeFAuL/NPzfgWcfeuWCyHF2umqI7Y6UCna6vk6oenoro7oaczLCeUitdb9co"
    "FdHD44/jI/X6oKXcWvGaOBGOFBEqfE+jKaDb0czGMdQNNcU0m3EXrPmmRXBFWZTG8lFwA9jEuwB9vLHBFPscKzoc+HBOoaYRPThJ"
    "51/OehuDIKK3cN3VmFNbT6Q6frTe1NT68fTaC7Qggk8CMqg+9igkYjh4FpC/fu5j1BbKmXL78+gRQ0ELNzYO3pxuoN1XbVjH6Aii"
    "Rj/k7EiuRTpe5nPrAbAD3G0GlDEBYR4zniHDQNahgr2UQsQL2Y9vRTyApzPH4fCIJ/RCaF1M4U7un6FzcencOZnjKzavdHnpUEHY"
    "v5zkDtO+zemJHqeLA355+SghGVUi3qfd1B5y4KN3Xii0O/twCrhi1JF14Ne9M3IdM/7JO3/hHcEVUxlcAN3Son0EWZtOQ4mB3hKH"
    "uH21B3WGHm89XEcjyRRXy8U47T8I5jVSeyKnow+CGrN+FFnaq2ggFQHYptMQKTV0JTZRqsd+WkLo1/dR0sc/rOxQ+w7kZhMxdkWE"
    "OzfBP+7g4ILHuJ066THcRthu3nENQmuUSecDl2+9TEwUoaaENh3BADgfH7XuPBT0OrXhOZ62ffyLJyd3jQUcEZy3Lr+bUTcB62Y2"
    "5z5f4bhKLDhwZzULZjewZlZskVn+DqMDMxRhGjQ3XsczFd+p5f4U0SBhX8KVjwsy1eG9gUc3+vOez+fMwX3CD2e1B9nGSqwUF1yC"
    "MeU9N3CYg/cEoMYwQHBQ+lbAb0p/BANYSzgRFzFqM/cv6Gm+j15vgCsI+3d+f1MnnQZkNGlHf4teEoULQRWCkHyoi4d9OfmexeRt"
    "4z4avNR5q8I+gh1GOCCKgWv0elCtf1t7c7igL6yidWX3MSIsHvpWH7WJ8Je9avfkQ1Dv/z+UUkEgFoBAha4z3OQ8Sb0TvUOWsqAv"
    "VkAfsIARdxxc6DfcKIjijcRFUtmvjJ34XW1lBLizJI0AoNKJpfzCoa41MF6kDjc7QQzrfOydVpjOcJI9OW+ZadtAoiqK/hOlv0up"
    "LCSK0Q8MlFFXPSuJhhD0joHMqRbrrDO9BkD+No1+5pTM9HpBxE/QtnTISducCx+ik5MorLJzj90rCPGkQjKFTXeSwFGHQpBYBNtK"
    "+j6jo9hmQkIScURFSPQSpslojVH1l3kJcGqkyCjOqDV1toiG/BMflTcoRvSJE6a+C916Z6kXjvsn84FjHaMXbjzyaH3ss+VxNB8c"
    "W28Hs6B6bB3YWo59WLPeD07yNc7ng/fWCGu8z9c4GxyxGrjq+vvzwZnleVj2DMpiGhbaHZxrhVJvPtjFGEVQalcrFXuDV6jKQrNm"
    "TI0+2DnwN/0LjDL0qvq2sLDExltR1seWPa+wdMBUUj1R1sGy+4VF+RB5wQgLjhZDMBKFEywcLoIglBC4hAevHIRUFj2AI3jmHQ4O"
    "Yq+uU3w84QGfdXYcHFoHY8+aYLnTfLFTXgrvr1ByCvsbS/oFLfqeWfaldYxFnYKiTqbokWe9xbJRQdkoU/a9Z+1B0aSgaJIpeu5Z"
    "I2zWLSjrGmV3gFdGfModtbu/j3GePMsOmOc6xdoCd0ZOhd3BDB0U4cWzoCokj1HWMMXjprSReWnll1iNFn9BLYxeo+vO4e8JMYEn"
    "9BcQXzu0xgtgO0LY3ntz43AQUF4d2vNMSxzwcvgnOfjfEuR7+GdE4E8HwHw6qE+vGFB++Kgdf4G8i+Rs3LmidpQTiJwZEOcgGjkB"
    "Sx+L9AnUQBkyhnCx6N0bKbBOvjlNJvotyHIoKHlMlNxXlNxRR2HEmWMi34xso0vQsJxskxGKDNSywe1YMO4csuMzOAoM0jsW9HxC"
    "HNx0PphZJ0g3ZxlKbNmsIPyAgkhNjweTKxP/sUalTaovaPSK5P5V9aSQfMEtpO/CLSigUIw16y2cqCFRsrScmhqVRjXoUNYKsdb5"
    "8lrnwJ7LSkAsrVOgGbt5krFrUhffAzoGJdMC6pJmKFHkwbqAsmFB2TBLiQp3bYzbLMZd65dQlBCDFGBsj+LqAEJ+P8o6Nl6oMjvy"
    "FPeiQ9syoR0Z4I6c5najuQX5fgr0/bR7s/zQwBnWpXNL1CD3DqX+A448t4/FJk5UQ4v61iB/cD3IKfhB6U4W44okOAmOyx1EmXE5"
    "h5eXkCars7SFY3XEWF3V+OKxkg+2B7AydtWON2TzuGqewP1WKA+vDaSOYWHmWpNzwrK5ZwSJGbAdgS/pmrPmeAFVPHmuJwxV2him"
    "QjKTy+/nqwwXFCedaoT7sXPuxc9Qx0VofotAdrjSKRcQp5yy+kP7PwGmVm5dwP7w66QfQ6GSuQ0ynFbezMeHaiZzVveEfWlOvGyd"
    "kXPofjwgdtE8cuYilLNYEOYdRDRnrgKzAUt6DdXsHJS4SJmqKVn74BsUtn9DLz/WgR7OK+OHTbQYMfu3fKsXTJqC74Pmy3vIzisZ"
    "DSR0qyHyA2hqSTBsCEqW2DsCtu+I/pBtz+Ab1AW5AzW+qZAvWZqJ9zNvg8ps+GMchD//BmYumd8F+opRpjHrrq0JQbXR8Rfmm522"
    "1efJQu+qutN7RVj4ptEIF1wCzKRdSKqRiTqQmpuf7mR4ddx72hTiLLg4CzDNSU3NBO0YHs2dzhgp42WvZXj1kJJIZyBklHLzkkYn"
    "qhgqxAmpx7F8ZEKvhFHg1U+dGEa168fuLMDnYRSheKHrVcZeSpEDKk5a4QcsNoAa2gYTJUSNogB9JlJpggl45zv8FUUBYqVELgaq"
    "YlpHzSU/PKLHd+7GlbJlSAxhhioTddd804Drc8rcmjTzkUlc2CPPqmlgaX4S9dcVNMEktoLmgD9erTnFCKSJqoRRWpmgijMGP6sQ"
    "XtgTYc2y37599fTF3v6zxz/vPXj71uaBzRw6/2YsrB0Fzyp0sReR+EM+nrSGjB3aQJpevXURobchGt7cwq+m+KrZ/UhZ92ZAmGM0"
    "oBOOND/7ZKneK31sRkasegSrSUwUQMXcmVdkkhUygfOVFkmsbfEMkDXhkSIG/oqiivOXjsx+9nR7L2A+D1V0D/aIK6X0OTl7bRj2"
    "wyH5sa/DRRHf6eHYon+BA4wxJ8YcYEP7HnrSTDDsB91yav2qf+CiE3b8Z3DBhoXSej6rfWNXMtKPRQkLiebdUCwrlYlzKheHmcwu"
    "nZaGdKbvAaRK8io19XTW2Im/y3W6Ewu3R85Aaz2mZe7wLvARVUBmLlWt63kOdCGc9LQqEugD8ZN8787hLNYqsscFWiyBJcT44rau"
    "rRJtcdXZzaDG94RdWo4uA1CM/hWBF+VEOYKh99HpvQpYI8K9WD6dhNoblhFx0fAmk9EnII0A03gwXLAca8otZw0fWtFKcbWRpyuN"
    "nL+5YbgfmO6htshqWZ85OChJkrTX2+bQkSSn76iTlM4pFcYgc3+P5zJ4WIVi+s1QNyN38wYiJuJUWVJ9PIrRzUwuQl6ojCu5RR09"
    "hwxPA5I+DLnKYop00ZtXSBWmT5aZpCgBf9Cim55M2HMJWWPOrYzERwTuQokohdO64OKNDJvszge+jCbIo0EKDRXJq2ZvCRifcicd"
    "EPQ0Q0P95ZI9PIRKzBLPAcHQOSlpeesDnXgeALiHMNOxuouxJAzHIyAwEIqheigohuXRIyjiJcmiJKXneVe8ffIgspLNJ/5ffc+R"
    "RrqkQsaOeLgkuPTLkpwfjgkGUrNe8ULkQ3YAnau7BcuYY/cWXIApGW3ME1GlpnRo5DPx3HoSDC4kC6mewcX7hT3NPZaJYeZeZe/8"
    "XpWSt0shaLtUN9ZLdVG9lGzdJS1nRrMuaWNe4qxiNbikXGKHl0kKzF1yyaRUl8jh37pz5Ct5mw5s7ponn8DkskOjFOstY6f57n6r"
    "0NXnMg5IwxhOzISiIAeoOWVpyZwkXojgu7TD2ZrnzPt84O2Q8wImc6JDIxCCJvQALYYkpU9UUr6d82xkB8XPOXMLWOe9D/4I6gY3"
    "zLgI4vDNxng90p19nBkqvu8hNamkTIPCuJYzuFk+azhTgPKHvFO81rGyHOLiwlKBQpRmw8l1TansbCkAjUOWiFz0RYbpfD74NACn"
    "Z02COvlRtFmSe4zuDGBR69KdTONsPNQ6zxfN52ZSwqKkOd6yifKuMj0KfiHPkQMoG5oGFI3xWeF08HmgUYoSKw1TrFw5zqWQy7V+"
    "ZdAfK+ImoEeJJANSbeVDGoVWWA5EleHRMFizOWDNxZclCHPLT+QXq6y7DymswyNzMMjMPA28bCUBJLs/rF6PlaeqJdNRVlM4Cs1y"
    "cXJ4f+SUlNT1z8quZf3tmwlDMu0Uy6TktAuhR6rEHUYHJAu50Ig45RqTTyw4AUkuHDhA7GiSMOkn9seHYsdAgZDChAy4B+Kw/IyA"
    "eyCA2yWNCEEFCT4pBq34g4xcPZUntU5iFF+hvZd9PNiBX8/Ib4lZ1bXDWXFTwKsDTMNKJGeoU6F5bsGbPDFH0UA5JtE6zbHPMTKZ"
    "Rs8rj71842lSSQkOsicF+zAvwFyw3JgMM7zRnanDWgzo3wsiR9ETdKHEiL4io5IxlFSbl35FTMiqpcV5wm8B6by4VuL/5UmG0szi"
    "xD/NHaukC49l6cxdK282U4+qkPLTU7g17L+89+Ll/tvXj17+AEy2VFK0rd1nT1/ee/R0v28L58e29fTZy7cqPYwoThzL2nv6QLQC"
    "7D1vY++/r+49hpLenzMn4PVFGtTe48mPnvZtP7Stx3v7+29f/nAPPjFApfx8++wFq/b25TPMgp33/Yu9ey/3XvDSR6mZYlY4wgr3"
    "916+3tuDsiMvPfXQdekDKP72EUCC8/kokQlvAUqR+DRKefr9vYfPXuyx9PsebHOPZ9x7CL2y9HuT1It1rd3n3NyAWTZxQS6zFGNG"
    "zt4B+6r7UBOtIQ8vL70D+z//Ed/2IY8VipfvbAgSjIM4eEh2TRjvm+zsvEFY2yGjp0EDLu9SUF67EPT0Iun7VtjXcoRG813lW/ti"
    "DEcqqvf1+a8ml0x5B/H6+iEsHk+1QFshjk7xGWXS9+dz9oUG+ntxHMVV+1EItX2Uq2MYQrwWVNgIvUoYhRv0G+6RUqW5/q9HYYWu"
    "2Fh05FVECYvKO4iACvPtlVRO4BirHDvvvYpTyeGzWquceOlxNK7bzE7LoUjqVjKQsa8AIRoywoEMHj030UTmhZAbwhVWhaLB6GmI"
    "IhThmDhJsB9nQEjRmkEfEBE6gWUNiOh14hu9BPghAHCOU57UGC6due6A72Gge9ZQbwTa04CQYD5iRXeEcZ30RiAGycX/W2RcoUuY"
    "ngkveEY4J4pGb6QwuYRFdZ44UyGTgru0bfi4orj3A/tefET2+yi8uvN7ddh/5V8+qgH3NuxvXTY3L9utGvzcDZyTKWpwUgu3eFSW"
    "sDbk4xFvLJoPG46Taiowmt7VjGGqynF8TRoYhgP0ZSlC4+2E36XkGD8+CA+ZW3zpKgdLPwZyyWSEff39iYnJ2PJwuDsQFfXVIcxH"
    "g+ckWk92hD/pqA78xs5aNRlE9RBN9HAN7bBW3EH++cfVppZmHMk9gwYF2FUX1TxqtQtuq+LWdoQzfxaanBoOEAw4SWYSjICDMRsE"
    "OTDGgxm3JJ5goDHXGrNAaZmeJ7meR3AhfjfnPqxJKbhOtxexroP6hIIXqAKRWSCiAgKDsH9Yb/0LdUBlpoDhRM48RYI0gi96Rgw2"
    "2PuMRsZuVY/pxywlYWd4SnCt3qdiJtNeXFha3AidforFPLfEKfr5Aq4sY9fQFg6onzrgvwSoBwxqwX58SpDRLfQq0Ep1EgW2JY28"
    "5ILh6GdcU24YQjBhDoWs+Ln3orVmX8bHRINp/nNoBM3Uo2b2VwJ+sBouaN3sXQ32poK9sRT2tWvAvrYq7H5oAJ1ZNZotn1o72mmC"
    "R4geYkWEVSRbeFVDulWyODea6TOHpoPGofrdPNRwVTDlQyyuEPTdQMMd9xMrcrAxDZVY8TvyAMmy5laQLgTtiqvuO33evO9SbN+7"
    "0Q4GZg8D6OLoRodw1+jgLrV/o0O4aw7hLg6BXUaWLBLp+aBaGMORhUF6QA8atZqVd25OPJIsQ69jsEfwQ8W/pQC4elJNAAc3pb8d"
    "vrVS+NiN7W8AsHDpc6Douvh3wnTXgAnNuI7Q928WJoPh8w5hQc6tF8HAJrdF3zLvRf3+iFAsvhwcW+VCejYaRWcbif8XgNSvMN9i"
    "G5C0Q/nzf9E/9SlasQXONPHhoreBLpDiDeadVmvICf0T0qvuV6Yb7MMz651NnRCuBvVWUvGAqm9Es3RHVhc+7voV5gxpEQSBB3fK"
    "a0DAf3vXguE/77zzSYzSqsXjU/Dg7Ur7xP87iv3xBt60A6wN98ekX2lMYgXCXP6C6/Xyus183VXBlci4MsDNDwC4UQowzLHwmWVl"
    "Eyrfak27sziJ4n6FyxdVc1P0UgVL00Nn2dAX6tSoXPR1t8H9oGlZC3qXT+t9CYeCIpo6rp+eAxhp9f9Efp2n/l8t07ivYxk4d9xy"
    "Hqvrw/2D5IG5ShuYpVVkYRuKK+H/8RAOy1rFVR445xsnTvJOJwSO++4oRn3BfgWdlWxsTM+ozIbKsahtTKyrxP+raTCQukFfFaNv"
    "HchplPhsj078M2+8oy2fKSwP9U2uS/UEPvxmo/Hv/JhVavFAr0S18hXVgOgxgUZQH8+YIcn/1VDD8tSJx8lCEK5CtvIVrwVCIRUo"
    "GN5CGqCvDOqbhZRYiQbczKoShGK1ITF0rTykDwVr6bgX4EytFBYbxBvLoVxlwRZXrrQbjZME6OXIdzdG3l++F1frzW2radVbLauZ"
    "Iwy5Vq6yYIsrXwmEwpktGdrC2ZW0WaMeNEvSq0glwQtmtVHfbteucoCWjPKifCF8KCy2erT4i5x2ffOfkTPygjvHXjAFvq+ywQOp"
    "fCNEGH8F5oMGOvbnTdgySEpGGo98KaXYQ11Qngk9P+8XZHqZNs3uDIE0XFNYGaYazGGQvvaGAgYZ8mVu0Zg1z9XGu40ZXB5FRYs8"
    "ALJa8UIvgdgMKpDFg1honcohp1kPlWW+CJmrR+UIEDULmcUBM7mq4lN+gV+mnwMRDxEBTQfNnfQ7RwjldedIfPgyj9wd0TX2Yt7X"
    "U3fSf7eGgDMGMIrD1hpKNV0f2Q/ct9cBej+SYVdKvS0OSzw1QiPLqqIHl74OUzFAhT4iCcZl2CcF0nlRdOQfAlPcBTewV+TKjTw4"
    "lvfIXbiE1srOHZVTR637VzS/bG5fIyjy3UBtXYBG24tpP13XvaS9Vs9LtDHWZBydy0v1suHxNyX5hplGz4XiKD2ChNJTmNgT4mUN"
    "H6RY47HWuGg43sm9H/7nP1rj7MFPvA5UpLZqhRm7SKuuaqqFCxoyiUCfOQ6rGdv9ew1j2Z1wt3n7tlrr5KaNjWmop8Jc7PzpoHgN"
    "/+r2nT+jk7J+OkRhzh4SNHpK+ilAr3HSY/WH90/WFs+qa030Pf+MBSp8ViV5tuUM0Nn2MOM/WyjNRlpITCsh13Oig35EgQv9E3I2"
    "k6IjBFdmX166aK1eP3HCmRNY48FMcww3syYDZutkTQcT1SRTnHl762J9/adgbvcn1gl2MLaOKcwfL8WtX06sI2wf+7beDo5y+UfW"
    "e+wkCl3POh+8z+Wj8XoK9DVOUutsMNLAG1n7GGou5JofaMC+n6u+b+1SIa7wgfbpu7lC5MUES6GiB/ovCb1cmdCzTgfk7HWaoCOS"
    "U1UCCOkp+hvRn+nRrYhOoti74rXXxQ69Il+wV0ig/T+T0qeP4fbQvUXEDVinMLkRzMTl5TFMa8TQenl5vuNzo7MkE1yITeVBudmf"
    "O//m0K5dXiZadNX754/G1YASzXBKwnDA4t3V/WQ3CkOyxru8rMYcCAwhar1zq7wUNxSwhRWibfnjfsA9Or21aAzoqcs6G2IAQGeM"
    "2r8Uo4k3UOvzdBa6affYD1Se9YvqyC4ep225NR2eSA0gClHRZlDAysTesC41glxURPIwxa0xExmofHk5qMKq+CmsxpbegGgbx7vL"
    "3IQPgJiy2nPrQu5UOhuYU2RB9IEbWhvfvg20LkJFX0DUsUUQTC0v6PvkXSK2ZgS1rq6QoDcL6hb9PaIdz54cL7q8Y/hjAeUy+OP1"
    "BmtNgRXuRdyiTiLP8hOmINX/Ho9o7TX/x9WY0B//SUwojZmOh18D65fA+i2w/huoU+KW6eXUn5EGUDzjUeNT8cOb6YEm8OtiFX2c"
    "scdAn8WfVidHQsoHsIpSSzj7Zym18PHklVp4xkdSalGuWmf6fUc8VpH/2esrrYUi6iDxfswHiXDrCGxsgApYqIaCppeDqqZ2VSMN"
    "KwuD0TXIonNnreoO4LLksBIhV1NBBHDryViQHHE8kmP8HeyotqPpoWDH/sCTiia8/zUXiRx/lRUPLtFAqWTx20A1wjemSLzk6opa"
    "AVfU8mX0mUSbR9qsRSp8Bf6Pndk/+PIZzT7K5RNwtvzymcw+6eVTh+nTXT7FILXLpzv7dJdPd6auMsGs6PL545LLZ6COgR8/5uXz"
    "x8/k8jmbmS+/wPtJr82C7sBh43l/edXyFXkRO6d9PodmnRR13Rlb8VpYsY6cxCNTSoPJYbPm1cfC6439r/p0g71Rbjiu6yX0pMcl"
    "j+wVVwoc3cCf9ito7FJtVOg/LmWUTydT/tzLYrX1KxsyJSu8LH4g5bGsZKnydzj1+OOMkiiYpTz99BhOqI0EevOw+GnsTHkGf/NB"
    "gOb/+hd/UUEQ+PD5mBcCthGzgd66wOsMRT8bOTEL+g3LAlu2hSO6F4FFBtwe2Zn6PNY32aFecO44PzMfIhqo5iq39Mqtwsqtw0Im"
    "eF6rvguqvwIzMoDFe2Cjvys0Ya/JPf4KmZo/4aRGR8oW0Hxu/YCKBGTfTE7m0UYUh7q7v59Xs87B29DhbRTC26D7rm64h80zhVV0"
    "iOPxmwdhOt8llrPS6/dshdedItsugZpWC1DnDKzxdYFUHT3JGCylXA7gMakN+f+4dQHz/Et2ntHBVc1whEtWukVL5YluFShnX5jn"
    "SsO95fW5gV+uCWlet6QJZYaXa4LZlWXrG+qKHAzdWk5rhopmjNKoucy6Nhoz7ddka1m7qRvbFxT65INkSGIXCc7sz0RtLOEs8PKS"
    "nDXBtoeF85uxcPjaQSqBoslc4HLu/MHUPGI93UKf7C0UbGL8WagdAlSZuFm0XrmjL3JfNS/2X4UuJK7hwkpRrm/IuZHpRgydV0ln"
    "DJltUTSXH07Rdwo2mGZLZ6zOmrKz/zjAoJ+fJ1lzPhOEQ7mCCGWCislCyCsRUzK0mQdXhn3ArI57nggrAJbXf7N0SSxIRjPFkkTx"
    "N6zHLLlDiw2My/bpFyLz6x1e15FdTCswwhXoFDiyCzUfdsJxbJ4owomMhzIzM61Z5CMWmEH+IsBYFC6LQDI5t8YzCm6lhFGT2Ury"
    "ucnsHySfozErxn36T76nn3yce/p0lXv68ae9p0//lnv6cf6efvQJ7+lH2j39beE9fTJbfE9/q+7ptDE+1j0dGv877+kI0/vZ4AIm"
    "dBqQHSxF02VXCAoARt/kdjpMWUpAdiWGtZq9T7/hpol20dIWzFYG1Lqxlf00SivK7FpaNNl78Iu3wa2DbGFErYxuqLYnkx8yk0VI"
    "rbCfNlp12I/hOg/XDSe0yQhDfVeimNWuYGj3Iyj6PT3Vxbw02jsYSWYFbqtgo8J5xU9szT5ApKHPSFvXy5cZI25ZrdTjZRZplNs8"
    "SKi9i//YzK1x376H//B4J/eCoG8/wV8V+CkSw3OZGEJJuLGjJzCoOR5X8BfGSsAXLJb6gn7zDJR8TAH4X70ES+EqRGQCKMdRlEDp"
    "XfrXtmZTurjbr6bMKt/FVxMAZpf+ZW730JZ/jNPOf9oWvjvimrOfsx82Wjt6+/5fFOA86R/Y94HB+Qn/PME/3+Ofl/jnOf7Zwz+/"
    "4Z9f79uHgLhz5v3gwN6fhfCF1SL+4+XMS9iv1944FL9fHs9i/vNh7LMf+w7sDfypWtw/juKUNcvaZA2yxlgzrAVWXav5xA+pHlWj"
    "WlSJ6lAVqgEVgIlNjwX4P6JeQUxQeaOY/3zixC7WuQf7OaBvTP1xhl4N4R9cBPa92dEMPZvZ+zBtHm5k+P0Mznz26ynMLE984Lns"
    "p961GOePuNaxb9Yt61TvkvXIOmS9sX5YH6x5aJmtkl/ZqqXflV9p7bKMJ9ixzKEvkYUrX+bgB8UpeA/NOmPIgJvoez+aJRWWgD7m"
    "z1KR+RR+ywysxQCQdRgIWINlUHmWiKU5VLI4hwvL8yyqwJOxxg/RTG8fP1l5lkHFWSK174ezVB8DS+A98EzWBc/AWvse0MSxVosl"
    "sFoik2qJDOekbzsnUBv+ncK/aQSLsm+/jGiZn3reux88hxz5vX6HGy9O0gfO+bPJa8jpAyd8HJ3SGIkWEabgAEDi9BDuEQ7QgZOT"
    "O+PxnXNqzHkHzcBfmxQQZtDlE/rXBo46jnCL79O/AI6TJKdRPIaT/QRJyx4pm8IpxdOBukP6OSPXT4AwO0ceEfDYS9DXCXO4iz79"
    "cD/IAheNuSzhxF7Fee/4AYsBwCwS4Nw2CgPLfZLwqO2e6HU/VxQ6FmWoiixo9J4HDwkZLN/EM3vFZHEyZfOhEcyuuJTMO9Jz5ZiE"
    "IzqY5BjjdwFf7z3G2whMb4x0aQLnn0h5iL+hSzideQqekfty4HhS9+1mBf9lX3CC0fk9pzQZ14xOF/iTQ90sLCwgkrGIG7DjIqDT"
    "YsoXsVrObB2zFQy/WYB0FGPbT+VvgIMkyy+jKSwn+lmB37DkgKxR4hM8uWTSK5Hyiic8iE5DnoQ/WeL9KMUIYCyZfYgWXwIP76U8"
    "K40q7Fvk7sOOdj2Vy75Z7j2E0qiOaMk0QYWMVngh0dIUJp5P2XP4WbnAhDnfq89V5kP8rmAC8DOOkfXYkTmIYC2HaAXLwenQciSJ"
    "YbloVfTci7UCLyClAmx5ZUoF/pidTF9GmP8AuPUxYJaX+xEycDwEvMjTyz9C9rGoMGWIdQfdUZ/amhVLS2a90tYasxKTWXv0SYuQ"
    "22PJrF2egLsAyJ2gOeEM1hd8c56xgim2deyPPb3ED/BtlmA31WdTdpfHeaFMkSAK7NJNHNjbVBZRSQD+2Ffj2oMPAM557+EvAAvV"
    "SlgiY7FYMmOzeEbgJ+nPvgctPIZfFfwJnCuwNyzxe/jFE5PAxwNzH//hX4z9RwKgvmDJ/RVFJ49OiBD9Bj8r9JsnhyItZAnPZilP"
    "eYaTGEfo/PQFPRDBmPCj8oIFd2FZj9EMSeTgBxsCXxfMhWMFh4LeXhkKiZ1FJ6nPhANVlB/1D54Gdc2pkwWfwmUT/tZdOOG39NtE"
    "H+SbSRRjX4cWXTR9l1ouKoFf0leT8aH7YcIM3UdT9lsve0hnLHXInTJZ6if6Z5KfzC2T/CRnTIdz669H6F6hf3ECB33QbzYbDYub"
    "UvSbXhvOZ1i8+CONoiD1p1RibhnOZGF74R1vjCf+VGrLTlOJbUDKkbfPjsoE79yU8JyclKFpv5tM+xdMBVHo9VjnMy5p0mVpI0OQ"
    "dMGu8v1XKT7dKukiS64z8aiSctRvCTEhXvBRgPUe1mz1fGaFNWt/Vq1Zu9g8fIR0lz2bUUhkGZYc1cMmgXAUaZ3N8hIQTb42rFfR"
    "VS01okXsNiVhXAtZe7pA4S8fwJB5ddPCy6w9Cep5D5w2cx2McUHo4cMKB6/rpmh9yAQFr2sUj4rFn+W3fItFnmXOi1ECzPGGQbu5"
    "gDgZ8MmpogIvA64mtKwoNCtMIE8QmrweU4ud77xmb3QxC7RxIh44bQmAFrRkbiW1msVr+NkaAsiyCk62ApePFxcnLFZzhZncHAui"
    "hirgu8BtqUT4fL4DCwLmLeO+VZeIaXqqK6xMUYI5nk1JL5Up7/mo4yqwb5ky9/GMu63jG0LAcRF6pz8zX2RWFIzZz3Se1X+1xp43"
    "ZXqwDvaSf4kT/daZbGe+pH8uAbo+GNESMLjbYw0KX8M0mzXhENmStQSduryMq4bKbRZ+czYLwffLwG9S9KDF4AtAjBGEtYs18nSh"
    "j/H2bQQ1C58kuAtBDBdgeAeoFz2r+ETI6KejfkbqZ8IEe6ezwQWptwLTbk4+o8lu9f2MJLhz6+VMBiYfB+yXtYdywShK8fIhbGUf"
    "cFNZ4B4KDGjnNoYNCuFMv2D6M69J88RGhZnm9KzSsC2WTh7zoQ2XaXnXWSqzc8ZGjtm1lYUawL7g6K+fYEQDUcY6xhNvV88XOczU"
    "ckHWD6VVhRKO3aw3W90Y74JoaP6aKfnYmw05ghcO3H3hdiMTxFBXG6KlmbZqZWSiGOD9pcXYkFYt98NqjU4id5a8QExcMOUh+4KS"
    "6qSFTElzm7+kGVmUNCc+nEavZYmRR5MJ+jK1UUEKmXJnjJyw0Qil4TpIo6OjwHsEMH7ytTBndzBY/NH0vjHl2SmNKX2eWwhzuqnh"
    "VsAb54pt8OksqNJA3phXy+6vG1t07sJdAbuY74v8D4TugaQYRk/4Kl2f+F4wNjsTDh/ulxSWDiHMtekHC+qw3KIa+aWfr0YLqajy"
    "Q1ydSyqzFWxUNmdFx4M5MWyvlxXmUJlVqLfSKhwWs4rPzCJKK/H8bDU3X1JkiRkqaExOnlxFGLzkGE66wr613Cy8zxdWFEAXNaAR"
    "F1leEBexqn/JwMFS62eqxK/FJc7n2bOgYILlvi6kqJnpKiGuRaXydLaoVJbklhRj2SX4KqbLRQyBVqmENxCXVJM88NQ6E+8s2kDZ"
    "khnqZk5GcWE5IW5xm7mlk8lXOEABRv9C0sYL/BaLAxo4cqYiEX7S6Olq3WcnnUFLqBTLLqIiQu5VWkcUKK72cGF/sm5BxwJHenmD"
    "/uwWFGDtSDzy5otKyq6zhR+WtZ0BNndAGYXVXGRWhl4osyzELH0PKJhm1qleDROny5HFiimUKVayoBhm108pv3RMrKQc2dwac5mr"
    "JCutOuNbkxOVRMezFSja02YpN3M8ZQoLDma10h9IQW+YJ71YQhXzpBBYsmN/KvgxOQ4D+HpyglNlPPZcLFmzc0sPs3ZBQaeAB6a+"
    "8gQkmcUTOP7qrUYjuzVF1hZm6etlVNRAkxrIXz3MDgruHKJAmwq4mc43VbNZuHpai8Uwzyle1vLB98oHv8rQt5YMvbds6JuFQ2+X"
    "D721YOhNNnQY/DPJVOvb2eKGJ/wLaQcqVcDNlb6LOf1ivk5kl2zJkpvK3PLpWpaoXufWESebxZcRnVrKW2Cj3usW0yc5xHZ2iJzE"
    "GQDUuwYI6pbJ7yZngWy9Y7TeybTeyrXdKmmZdwmNv1MXn0V04GRs3qYa9W6mc4EN46zoodjhxA/5bU8MXwxADn2MACS8HZ6Gx4De"
    "/CYXa+jNtbLttbQZ0Stv9fKVe9nKYjoR4dllqSoWLOJikodSVifO8ow8NbeWVXoIPGii3eYT0pnIt2RSvkLCBZVnZB+WqXoUe15Y"
    "7xZWpGp+OImy3b07X1QDQw9n2eMY5YWLKo2xQJypFgOXtKCOQFAJNra7ZTUFNf5U87JVTlUXz0vHqMjSaFil82LWwBRevnxWzCo8"
    "kdcqnRazEqbwGksmpQgRrCbSoHtAg+QDTYYQ4VuQR3KiM6BKLRK8nQDpwx8n0MUm/oDdbm/hD9i5dhMLIc/ixU4w7l90G337/3nu"
    "ZDzp2hbsFfgaNyeOB18t+nJ6k/YYOmjT16bn9UY92+rQV7szbm9v21aXvpqN0fZW07Y26avR3d7chLwe++r0trpQb4t9bXYnnU3b"
    "2uZfHa89gi+CpdFqua0WkWX0MM4AnDQAwI4E0J24Xk8AOBpNegrArU0P8CcA7Dhjb6shAISWu11PANjcdNodRwDY7G412mMBYHNz"
    "s9vuCACbnW67NZYAdltec5MuikjOGHy9iYcQMfgAna47EvCNtyfb22MB38ibtDY7Aj6n7W22uwK+rY7rQsscvs2u026MBXydcc9t"
    "TAR87clmq9kS8LUB2GZHwNd0Wl6ja6NfZDG/E+h00hLgAagtryXAm3iu4zoCvInrdJ2uAG+y1Wv2mgI8b9KB/xPgjd3WZmtTgDfa"
    "brpNV4C3vd0cNUcCvN6kOW5K9HW6Dafh4IWMNpWAcDLpoS4Hh3DijcddBeG45ygIxyOnJxE4GW232q6AcLLdaysEeg7MqSsgdFud"
    "ZkNBCHOvENhzW2P6YhACMhs9gNAhfQoJ4AiVKgUKJ21XrsDJ2Nvc0lA4hn2hABxNWh0JYHfba4wkCrd7vYZCIayyxrYEsAX1PQng"
    "VruLsy9Q2HQabQDw3AvQrFdOsuttaRBuu22FwklDg3DswX6UEDqw6uQa9JxRu7ElIHSdLafRERA6zc1WQ27irW5nrEHYbE80FLag"
    "X9wjqecE+h52BHyuOxlNmgK+7e3JptcR8HU9zxnLKW6Nx53RRBKZzmjLkVPcGG93trYkkZn0Njc9uYebXa+7Lfdwu+Phbud7uAP7"
    "AZ+W3XMnVETQm0wkfJOJM/EkEexO2hNXEsGetzXZlvC1xm3PE/A1NkebY7lJGluwE1oSPq/X2W5I+IAW9boSPiCCm20J31a7DVsN"
    "DsJ35wp92wo8rwE7WoI3crzNiSQxvfGYgOU0ems0nmxJ8GBTeNsSvBaQnJ4Er7257TQlje51t7ckeA234yBqBXitSWcbBQ34tsnR"
    "N5lsKvjGI09D3wg2LX4x+LbbbnciN8hmA5DrCPjaI2haTm+ru9nGTcdJ9Ljjjbck+rxOw5lI9HltZ0tOb7PX6nY7xBCM/aNIQIhU"
    "UMOg18MvBqHbG7cUhE531FEY3GpuuQqDm+3NzYk85TpwjuFZyYl0u72FtJQT6V674bQlkW62PDwdOYRec9QZAYTv/SjACIBsjnGZ"
    "KQjH3rbC4Xg83lQQup2RhkOntzVSONwadV2Fw57bdjx5jGyOW1tjSWS6o1ZzJM/hjtscb3cFhHDIwTGND7+zGBUIOIQOwCghnLRh"
    "I0gcettjymMQjrcAh56A0G1sEUYZhM5WtzvpCQi32+22Jw/ingfHtNzEmwChsyUg7G413a2egLA9avQ2cZYnM/c4QWVaBiJwChqI"
    "jg7ipDtuKCROGs5ITbO31dueSGYGCAtwEpIONlqb47akg62m68izeGuzub0lF2Kv0XR6EokdoJ4dpDNTP3yn4GtNFJ0GTmai6PQI"
    "iNCWhG/b2VJ0cNLptXCyOJ12O1vbciOPR61eT27kkdfc6kpeZnvc7OF5xODbaje3OpLOQFu9FqIwRh1fedI1NWZh4gFh0piFMeJB"
    "nCNOB/EgTrpec0ueI5NOe6J4La8Jm3dLg48ObQ4fnBttSae3tprttpzijtvoNpHQJOglXwC4BavQlQA2YUVuyzUIm2wimUF3NO56"
    "TQHgdscB8iL3cafX2ZJHcafX7SpuFYgvUGdFaVrbbcnNNCZAXdRB0mpsNnvErTqSUm8DfIpVaMNylAj0gOYjReN7pDnujkcSPtdp"
    "O/Kg2xz1Wsi6cvhGAJ9cgO0ewCcpNczWNqGMH3vNrZZEYKPd6DWRm/7LD121hx11EAN0nYnktWCyO8jIcvg68N+WpDJN+E9SGeQM"
    "e46Ar9uC/ySlbuOgNwV8rV6LYYzBB+S0qbj9bfgP6WDozeCKFBSD2MX/NBR2keRqIGr8NP4nQWzjfwaI8izuNPA/CeImY2Y5iDQ2"
    "CaLDGdYkxcuWBuC2AWBHAtgDACUzMwbCMZZrEA6p1rZkFnrAX2+6EsAe3Dk8CWCn01CbpLUNsKsLidvc1gB0AcBtvMELrbxizR6M"
    "61Ekbmf6Gky+nkSBPy663pvy9Jau4kEKkXP5ZvyMu8VBoRSTt+mSIuYj/PtZSlZy1I6UOOBoLvjNtE6CCkKvTGKinJaRxmStbSON"
    "iWY7Rhq7m3cbZheYtmmkMWFvz0hjEuItI42JL7aNtG2WZgyDSwDw/eMhPn/IB4JfNKGgepBuaK88RRI6vbIQ+em1271CEZ9Se9Ib"
    "2CroflPICJcLPPMrqSHXEa0JsYw0F/9qCTVyC+gq2miZR9oGE21WGkLmSa+0tLqEyplWlum3aOUrXMwtXnKzZeVErfAaZLwzljaU"
    "1T7LqwAtwPzcwrgLZZu82UXlWs0O52JlZAHDnHonHzJ+1paSUs9GqLTO7AGugA1R8ZEmrZfrda4pHPCQNSuI58Via1Q607PKJvwP"
    "FdUq8dHIqTasCv//erMGfyuADCq20SosggxdNEUgrvYwIMZ7w7Awc4HFkJwFphpkKwtJqwHNt7rYUbcUli3IaWLBjc0yYPSFd7Pj"
    "LH5H4ALT/gXnXScTYqHIDAZ4Rv0cYQn6KcJS9DOEpegnCEvRzw/RsDo9WIp+drAU/eRgKfq5wVL0U4OnsDNDnovZ01iI/5lQmT/H"
    "ybEbT5KiymbBk6TI6zGZ+zHgk+O0UPTfla+w94uyzXcWo23z7VZk8YdrRsr0Hvnc03/1Ti0vG281smdqqVi9UBUx86qe1zsUBbqN"
    "BVqGBYUelr5hUyHz+bTgIfl+YYGOwqFZIMudFeoB5h8mzIfvrKqfgrhRrNxnFijX5cOO2bKbBJHDbMKK21D5D4sWSraRe4UP69mm"
    "uK/oK2oWIrtajH9FyxqV/9eA/7Mqxk8kbEi5Gox2NbesCv6v1Uby1ejWSBh6lqrdbE5DoSIBIxakE108XKr1pCifP3AqpqJsh5Qr"
    "RrAdXbxoW8aKMrSK80rbTM9VvgzmD+8y2K7at34s31yb4ni9sRYF+1quOGhOQaGeoCTXqyoHqgoLNAKNmTTIdn4mczqAqoeFin9Z"
    "QPS9l98enXLtny5XIypV7TMuHuV2BnOTa2E88LJJWaAw1CzfHMtQWmDXYBa4HpJKlJEEAk02/ToYNBn2mwVPaCaUc3oo3NIZPfrW"
    "+TxK0Nk8StC5PErQmTzepuLxKEFn8ShB5/AoQWfwKEHn71jCEvauU8TeKcWA/HEhKrYXMHmthUwegbBx4p9V/bCSwAFmVQxwLD1M"
    "X2Wr8+9aASt4tUZ6m/9WrB0dma1u1xL/g7tezVwxxUWW8o+b1+cfma7MQg6yt4yD3GqswkLqpcp5yK0F5/HmMiay+8FMZLtM6aiU"
    "hewsYyE7K7CQnSUsZGcVFlKS3yVMZOdLZSJLWchSBrKzhIFsr8JAbi/RrV20ZHsfnYXcvlbvy5jI67a6iI28ZpurM5JbXxnJbjkT"
    "0vl7GMmtZYzk1idnJJchqYRT63wiRvLDwCN1yj/KVLrL9OHn1hNZRQlQF2jj69tBF4df6YGDrZ1r2UavNi5uyKbWK3oyPmE2bZnF"
    "kS1D4dML4SgsaWzO+Wdr75N4sDzJ+9NKA4caT8uW0gJrJ1oY3tg0AW+pZxixVm7CihXBfRYG56/zFmTqadCwoT1hxmr44FJqSQuF"
    "loOhFSqCpOiNUq8eHK0ACBRaDohWqAAQbi8XMHqlP0N16RkqdvzEG+9Lrq2N7x9lbxQt+YyhsXD6G0anJni8bnGBVu0GzOEW7YE5"
    "kKzxkac/yF/T5LfoKYbTyJUMCPI8oyhRdI4VFmRZGbJXxvkXXI0WdlhYMtPjMiOI4lt6rlTxhT1XTFsYZeoZ5oP6qrYxH2wVWMy3"
    "NpddSY3WFzyN3KTRYREWzXazOFxo61OAunfmY1sus1eEskyDuczNclTJJt0F74Ay0UCNTC1CigQpt6iW2kzlscJyS/HCsoswk2+2"
    "ILscO3rDN4sfHbAshpYZe+Xxw7NLEcTzizBU0HJRfjmOjLZvFkkGbFksYfSN7CFBqsalWOLZpVji+UVYKmi5KL8cS0bbN4slA7Ys"
    "lpbYAOaRpJ5dCzCEmUXoyTaYyyxHjGryZrGiQMqiZCUTx/JDbXu1W3fxoaY3Xlxg6aG2VSpHLRXgFR9oS44zBmoGeXMrmqUYtm+s"
    "MWrlvFi3sZgFK3oiNl4cyjRJDd7keLFuxdKXtlUeYM03JXWIlZ1V3YVHVbP0qGoVWKfyPhknUcwydBdwDM0SjqGVM2vlHbHzp/SU"
    "6S4+ZJrlh0yryCqWd8rIeSnR7i6m2c1ymp1ZRxqxVNSxmAx2F1DBZgkVbOVseLuNjA3vx1muvUa5GTC+ofjhp90oPS7SY+8NN0Yr"
    "PgU9+Jh7/iPs7I+0gz/eNv04e/Gj7rmPu6/K9k5AVl/uIpFEmbyiTCggZI9MJeKrxOULk7jckDOi0QLOcgFz2lvKnN68r6NFLGr7"
    "KhKXzgKJS3uRxKVVwj91Fklc2gslLq1ijyIZFMnkDHpkeoncpXNluUtnodylvVju0iplZjuL5S7tJXKXVpmnFhNPeoaJKT2nVAbT"
    "uaIMprNYBtNeIoNplbPHnSUymPYyGUyr1OuMiTEjx0SZkVUukulcUSTTWSySaS8RybTK2fvOEpFMe5lIpvB+UIA0IydzAuhZ5RKa"
    "ztUkNJ0FEpr2IglNq+Ru0lkkoWkvlNC0il0TmRhSySZ6VHqJnKZzHTnNKsrnCw7C1oKDcMkx2Fx6DLbKmcbiY7CQzht5C47Ba8tp"
    "FmlcMg7F1LncJp3LPFKv2g5TAC1m/3rXv+blVDwb9UanEOCCks3N2tWu1p1lt8IirKgj5/qYLWujCKsFDxj6sVd69SzqV7AW14e8"
    "uIUiuHPPUoqxKb3dFvWoHVfXB7u0kSLIi55DjFOz9A5duIvUyfEBW7GskcJ9WPBQYRxgC27qRZ0L+n598ItbKII995agTpfVhAFL"
    "Nep6C06NBV4Vl8oJPqjjzUa5U8Zl4re/9wj4MGneikj7Qgj3502eP38y/EXQ2s+eoH5cwvlRiWMxAfx4MlRo/HlxYJtCVd7l7hXK"
    "HG8rqw/U/WsX6/7VdPuPEjcJ5JZlfK7rIRs+PKTfDdfhFgFmcuqn6MlN9wtTEA2rKzxw8OIL9d0fXiuYmLQq4fAJpzPor89FHdzH"
    "psuSZsEYZdkSB+pCk3ZFdejPNgxBgaKlNvRR+d24fEOWi2tK3hmWddhb0uHmyh1Cl4++Rpv6Gm3qa7Spr9GmCg+Pv8F84e+wVJgv"
    "CAFUMF2GZcr/dDwu6yQa+YGHkbQxSnvGs9vXGF2fb4yujNWZXtKwOCsdfd7azMq7jqOQ4aZ1Ydk+mluPV4v/Qp7vTpeEXbFW4maA"
    "0XPfZZZbLvgGK/PDigodn4pB+tvYlCynwVG4UDvFwOEKSiq8/MPlDhR4yQcC6ytCfU22aiFz8nneaT7g3Bd7zNxguTBTZZGUzNhW"
    "ygHqAt6Uz+ZSXSF9PS0tfBWGF4edGDGk2FD1+FwwsBcllKpJIWBW8jl7fVvlE4p8d7ogAlRBTDH4C8h6lM34LBbtQr51kfHjFUJQ"
    "cf+HxXb4PFPHkbswiN6C7rcWBLIqbHlp1yI00V/XiyQfe+9973TZbv0HhJCcOiHaFed4XO5gRBHqEpZalNOzy4xveV+jK1u0cDm7"
    "E451YV9haLAFXSz1YLKkC+jkPqymXHi+3P2B3Kioq44pSRRBAX8uFiHl8Lr8CmROQU6akS225I6UaU0u4OUr5Ih7TEfvu7blxHF0"
    "+oyvTBXXTyJDMeXZBjMXp2YBec7cMkuGiI4cIgTposhvAQq7S/u+Tg7O6g9XltbnQlXeZKTM/Kxp/iLkxH2AV3Pd/0ThrTebzwNS"
    "l/mdybqzKLh1Fohos7W4SnbhZTVbtvDKVgxG8aNNSef5y2e2YOkFNFvwI7lFWTjigovq4mFTBXPsyttO/6JQ5FHgQl1vl2ezprn0"
    "qmBkRrFlgzMKrzg+o05miLpPllU2NODk1bVYEhEk4Kp0Zeyk8B/w61ejLNz7SIO/+DXyPuJZRAJi/rUsFt2hIp/A8B5gvJFV5Fkg"
    "xrTrBcEq48q/3YhiBa8ZV/Ej9oEIMx54TZBW9x5WckIZqP4UPORGU4+bUnw5/pAph/5mJ+FL9cprBlWIMVbg37gUPuocfybzx17o"
    "+a5bbel/hL3PWLNV9/4HbtGPAD9byA85g5lfyYL1/CfRa3zueR75YVqq7SLw8sLD81rpPcj2Y8p4lFOMoGVbrqsXxal5z1/J3Rzb"
    "oGaprLjdCiIHR/soH3UdiNHL6Ogo8O7DzSYq1B9agez8UFqp3Cvlqn70jD7KpL3izlQYIKfb+PfnK5yY+AHtIT9EO4Pv9SOS32f2"
    "i5yrfqGviDzjeaFr15uTC1zx3r9MjLBcLrDyTV8RiVngrchOo0AhAZYZiNLjq73C6lW/vrre/KvrVS9GN/hMS3LNIz/E3l9G05XZ"
    "nJKjVGvtfgQnwcmHN7hAPL8SrohPhsXrTxfEBdIZPblcCx8Gm0WC+nID7hX6374aANvC/a31OvNKtFsQoM9Ea3ZlGLzPlW7Oi1ms"
    "JZK6K/JhWZjL/JhfH9CFKNMwVADK6szrzaGM0IX/XQFli3b51aZp6R6/2hBgIX9/vZenggeMz0d6fJ2z/fqiqysOSpPrNyoifqNS"
    "KTckLHll8lJVNu1Rv5V7xm/rkUg/VK8kU7jI+re89Jf/FOmH01m6mtoTZ0qewCweX/Fa9gESnoLwpFfR3xdQ/+o58RcE9BGPNbDK"
    "1mQ89gJSMHbOf6aHdTj1gdyqOKuMalqnnvfugXOeDwWb37JlSMFOMBD7h8sIsxdpsvra/3ukiaWKOgZQ5bLHcs2XIoFAEfY/T6Jx"
    "giRg4ZI6YUQiJ/NafQecw4Zd2MU57egP6GFEAqaRUxAEmrNEq10LUv/Ee+6777wPa8h8jWDAfW+aQRVdYNQR+jFded+kr23AWDR2"
    "zhfaKLmF2ijirrRkzDfkTOsmvV0tHvMCO0cY80+LlVaY4ssKoilecLHCiqFGUya2MloqZ1xZMSVry4Vcz5Qsk0ytZp7IXgDyqi6a"
    "wonZzVXTtSvaR2jcHPPc+rP4Sr5IJHfVi6wZh+o4iv2/oDgGoxIkt8nYeZ3Lb3IloDyaFewwwtR39YZEvRx9LGxKXiOgrR8LV790"
    "9FJRf8gS1lz7xcUwnEamsxXMeIX+zIrXuFwH7EWg/Tkf7HPr17+P1twc+SikGJ8JwSgtOrd+AdynURQQR3JD1/ZVeSHe76PrR5da"
    "bFT/TzI9s8peO+Qon13XquwGnhluUKB/lTPlE0jGYIv8dtOanisS8xWkX816k131cz+uqOvpHXnh+Mb1cT7gVrwijrJC2UWC8dxR"
    "L97JS+WFSKw/2/twSgoLN6MrUXgiYSf//cy0nD9Uj7I88mNud6mdZAxsFsLsrPAwlfGBItAr5TWL7fZW3OO62vzER+6jyEtJMz+K"
    "sulhLqIytwJsmT25m4OaxtFR7CUJ8Q7K04kQHIycxHdzjd2SK6rI0B+DHdcpAl7xEVRSdpF6b0mVjPK2XxpcWa8k7B5FraLlCAhI"
    "YAIjlr7IFwMvssAZQ04SyqDWmUxJxfSynQbtXqZdIuqk0RS1BpWSFzpKIlG8XDb4uCbZVp7GH8nKYJxbRvtlpQCYcInh8lkyVwNc"
    "yT7ZuAc2xbjmljc2r7Gl58MHntBXoUah814ol612pyz3SJq7V7rl0e6KvNHql0JhyiMVkmPvfXaeUFAMAyDnf0U5n+sJCSh/lLcl"
    "gpPzeHYyCh0/ALKyMq9pqkoqKicbe6omWDcZWzUAbmYePluuIzfcR3lrWunxK7fSNQ9i3dKFa55hOUdcxQr02bJiLsqttFdwAfUl"
    "qVD6yJg8MlG1BP/ZSqsTqM7qBGpzsdNko+w2wuQGUeKZW6mYVn10OtpdSEa/oLWhobSQIha98RQRtmUu0q/6YlOwX6/vQ06+1FwN"
    "8gV+XUvnflW4V3JFR+8t6VjYGy93BBOOPzoL/Teww4vYR2sVftf6cF52bsXjD/Ii4BftrhMneZdZIJhULCuhHDXXUjYrMAj705vA"
    "kJ1ZGtlWrJ9nhEFx2WMDpVJwFQtm0PYW8b9LPNeXvmaoMq1aueBFkMN2Q3P10bfrRY5B8VQo3JslcF2NPOsnB06LKZP/cog3rGtY"
    "k8JfAV9aXcQuDZ0Ni6F7ydy2F56GZrkimUdep20lYQghd/XddGPzUDKyD5oKR5IHJfIupCWVMjK36n3AfIymu1delbHAk02xi9Zs"
    "EKsiT85AJGhPmZ6cu3nP+FTQVJmgJDNmOazISgf+t4WqsvC/BV0W+p8uCTJV7gt9FdDLY0FdHXgVdbEQ+nzQp3wjF+deEESnK4HO"
    "i5qw88SrAy87LoHei+Osg90y79+rAF8c9ufqYIt4jMXrZUm8u6vHHb06gHr8hkIglwWMXhrvufAUvA6I291iEJWf5StQjRUiapTW"
    "7uVqbxru42UXfytxueYIVdCcRUPUIrh+ahq0gBasOERef9kYtW7+Rlp1zTGKaDCLBpiPEv/RSdrWlYM4tz85SSuHcEE43JulaPj8"
    "8Kk4ty/Jz2XJdXbsJ1PSm7nSa//yV310EzT+jP3pf3WJ/ze4xP/q0f5z8mgP1PzYn67gYrr4pskq51XQFrPZpvfQZW0sVlx3gcDA"
    "5OdEsmUUZtXNu0Qse4VVllPSPfHD14YlIkYaupYccmQ+erWu7LxUKFE/X3xGlsz+qEAWbmjc3HCI1b/F/PIKLwXdBRYam8aa/wDM"
    "XSva3+eOufYCzLXko8lMbpJsNCZ6CLi6eS/Ox/hrwJ+v3M3XgD9f2aP/6YA/c2tyDQ7ks1WAgP01y2oV5sxFyMC6TBcsa39LLzIL"
    "oxFOP8VJMvq4ET1uiG4uJGKrE6Br3miuGrQpb/NFmSzZsJ76Gsnp84/kJGbpe+7dogxr5P1iObJYMYUy9SRbUIyI8ynll46JldTs"
    "uSh6ywm7Ci+YLaYNt586MTqDVZ4IWPoejk8mzi3vZJqeP/GShKKjLMFu8e1OLPalzsjEpWaVCsod2Mn48zKzMtRMxb34WexDGUZ6"
    "Ptw3vrJ+Lm53kaHS1SS6IyfxHl3Lkrjcmf1X3/7/K779pR2t4Uvus9ilK4W9MPeNjFTwwfuXt/QYlSFLmhMRBZjCpGrXODhKy5vn"
    "x6hkt5h1lu0Xs7Tys/U/GKGBh+eUKrx5tbWMR+UP9kl9pQe1z1Yh8Xj8NfbNR459c4MH3T/m7Jr/wyjulePJHH3OLHIp1/qVT/3K"
    "p37iGFQfSLk/MW+70vFVEFbLUP/+0pi1r9zap+LW3o5L4oav7lTlKiS83LVaob+Vsig1m62iODUivaJHUVfWEftG6N6M7wTz6UaP"
    "C3Nkeu1qtooiNCuvGyoKcjMXAlkLG6Sbscrosr1seNmPGKtl0aoRAOZDHusxnrcKgjxr6IlmKYZrGffLvC3gLvdPpizQaqGDmX+M"
    "uYo533nKQXWZlos2sQsACqPQM5FcULhgpEyxRMN7Lu/LtqxZhmhWuRTTRTCVo1ovXTTeEmTrmV+2JdAybPPapeguBKsc30bxwlGX"
    "YNzI/RLNl5YhGquWYjkPTTmKVdn8GEuQq7K+CCOrZag0wSlAZzFk5Sg19f2Kx94tRq2Z/QWYh62K3K1lyO1eDbdsdAtGXo5blv0/"
    "Yde2ZHaKXZ800BVPGVPSvQpT0i1jSroLmJLudZmSL88i70anpwjCZZxMt5ST6S7iZLpX4GS+dHvCG52jQhiXsj/dcvanu5D96V6H"
    "/fmSLCJvdHLy0C3mmrolXFO3nGvqrsg1fQZ2nKse7L1lB3v7ilxTZ8HYO4u5ps5qXNPfboG6Km6by3C7fUWuqXzkC/HKdbLm1vur"
    "yg51j7QnXurFyUoKtTJYs5A3sQc+U3GDEp8AD4fKmUUVClwRUjpzhid0uIzowkoF63sF+dw6/2oF8tUK5KsVyFcrkP9tK5DyWJlL"
    "4zb+g2JvfLUg+N+2IMjoj35x5gSr2vMHnhOvGJX1auYEc2tkWuqqR0TGukdBkgsUcKaqSL+/19AoCqOxd+OBTZIrhAb9IAXIZGm4"
    "z6sFhtWDbLMAIsjaPC8qUOFv2YUhucuDOiG+X1LLhZ5xPxz3V8LnlaJJJV+oh1DcQyEsExT5uDeikSTDxnbYI/6+3Iv8qqn4AVQP"
    "yXWqzRfeInfzvpe4TkhTVwhpXSWUqnX9iPU3ELZhiW+GGyIdH6zAlKwcLbhu6qW0vsBNMItxOp7DifTCm0bxYvNc64/ZyfRlhKUf"
    "/X/23m05juRIFHyfr0i2Wpyqo0QRF5JNFgRBuJBNqnmBCLJbEofLyqqMArJZlVmdF4BosI7NR6zZ2p6no12zlUlmepKNrdk8Lv5k"
    "vmT9EtfMyCqAze5m63TPiMiK8Lh5RLh7eHi4s7eIafS24YXl9OMydP++YhotphbtQY7mFg95UBd5tS2XxeytEInLAyIuCHzkDYq6"
    "CH4ePvf6CrkSLZhFKSqlPqhxqG1ltzzgmw7sfjVSOU7ywhsMp8xmu5dceZOoaImng57Gdy8bTO/jeBLhN1y/vM10G6J/iLcPeIFt"
    "GQHXXm59f2a+0IN7sIdIqXs5ne4VhY2eMja8XByEJRqGWTZbJjs2QC+lY6hBtyoZFFzzPFqHMMusoYlQIEYVoSllPcBc046yKIEn"
    "HMFOPT8V0ZuGNRFfZ00F9H/qZEbTITQpb8bgcJYeeQzsbjn+q5Y0dXNxUzcXN3VTvxHfv/ox8mm8MLjwd18my+b9isto6RLQYXDW"
    "yOd/lOfZ6VMpN2nzYw9DbV92gKU3SwSd77SxTa8u5YZF3v2MGqER+Y7PUZYsiAlym2Pg7cDIfJvDCqDyNBXOlqDE56eZa9XCqcew"
    "ImvWFJRxP6s89/C8ObxN3fQ2dbOtqZttTZnN8bWeQ21tvl63Nl9vRk5qvdQiPxS1g0o9PpaEad5IKUBXE/FD3ZP9aLdVddogUbgw"
    "1qeDQy+ki0QJf7/ZkZaa9xXWv19fQQvvqH5KXpEvdf3THlfO8Su41qtvQd/bEk3A5IztLaN99ppZCnwlT03T5tX6kXunDn1/XD9M"
    "XTnm9McbRq/xIOayWpj67lscnH4ePlnImTyh++j/MBJSjbMsD/tD/OHg/VzKRtrY4m4zzJPnIuEj1pJ6PNZG+SI7duOftRXujua/"
    "93+2GfnZZuRnm5GfbUZ+thn52WbkZ5uRn71O/rTMRK5g/fEReKichw/bTJPb+ZBfBuRK3k88qEni71sJVPPoipbWi8ayIIZylMIx"
    "BHG5JAbozcudMtx3FhTqe2EDLvxNeTJ59l4nE0gevfmgCksZMhZtHrzOoBuqShWVVTE60sjqO/TV5nmJbtAv0+N2m4KGfCoVvZ6G"
    "FlRiExylqrht955/2W8gVnu35AsI/F89nPzqnW5IGWvyfz6gNZzxn9QBUc2wQXPLAxPzvvRyRdSjVCj27Xe+mp6Hu1enhiF1SakF"
    "VQEKjQGrPylEfKhmP9iQk7qy7pnVdZz5AHPwf6u+WUcALH/LD7BO1ObLH8ra4ipURt62XM4rvBulmaynwlZTjZ90PDmYrgfvRbVt"
    "r0+XIG8e/2t1PRv8OEow0nyA/7emPAdJar5O1Lwoxaxhfea+VkKQphHLTz3sX831LYzxOdvgLNBqLlRchs0o1Fjrkwpvci+zcz0z"
    "+v473BeA6OomoYsHLNeRvmDUbqJubvgdTfk8k12ej96+DB9d70q8k01S4SztO8qFlmsM5SyCS5syLbdJQk2VbY8yD1/8AISBLYke"
    "JembSz9N/EnsUBqVewH+AXYo1vrzDv3Bd+g8/Or9TjbRkLVHrgGmlKE+mO91ZY13ecNmJ7e5TDzijafvl1kKniuBK6yvxj34+7wG"
    "WLzkjEmtY2jasEBxpJMViQJHzP9oL0Jhbbj6oA+HvrlePECQ9InTmJP2BytrddnZc4P6+ce9u6ChnzfXP//m4qW6ZDfBWviAMpeS"
    "8RaYvP/4dCVJ4XfQgo+WdzWLEXKlJVa7fPpoVsIHoHxeTZWFUUeWQSEF/7mlxZSGIva2pey9VDU+Fyiemav5VVz9pdT3fvG+dJsd"
    "eXxY+vzx0kHq4cF3pBo/wFb7ya/Hb/R69PiHdrjOZ8h1PO9xbr3/O0avFrZmV/V2Mh/4LQb9uJcLqeX6wnV6pFI/k66WLuXf0+sp"
    "s8WFn+OR1/UrJ9tsemQ8L97U+4kpEr7phu48o/uaWhGZKEvF+KN+ADZuVW23XbLEMmect1oD0cvF650H32JVk9Dmja0+WRuXm6w7"
    "7a7DPpi/RXdGN9pm1Os1683yESPMRtu0+yqVk76sXgm20b42ruoxz15AG5daQK2+x4gq/e5q9oTDK0Zh9xi0aXnkTu1hnNcALGiz"
    "HLvCffwsz6azuhkx4m06jdL4mShmGUiR+DiXBX26YML99cefjS1/Nrb82djyZ2PL/9XDtP/h51h833csvp9jgP0UY4B5Amb9rxnl"
    "dB7+CWiEOCFbpGmSPlA3YYwS4wG1z0B7jafDpIYlsUv5UG0FXQ3ULTABuN5a6+5HXKs4W6W93tCBfReC1m4hpw7TyjR1kdotJIXm"
    "4fdyT6iweUk3TpZpyzz8ff3d7xX9KH2naF/eCFlXe35eD2tO0bzqIZunfI5u3OTWon7BSU6UUTJZCGnFtfqJBulaaPw7wefha7g0"
    "L30Q/0CxtBj3fv/lH3ucrR8lKNaHQtiPFDDrxwht9aFQ9uOFvfpBo1N9KHT94JGrvr9IUx8KJT9qFKrvK1KUHzk/pRhS9WcrzA5X"
    "r84Nf6DQTx8G4x9BUKiPOYLTh0HyRxHb6WOOwvRh0PyRxGf6GMMofRgE/+gBlr6/gEgfln/9KKGSvqdwRn7M/MRCHRF7/9TnTvpq"
    "So+akWBNVfB+t4XxMjdbi4td5mLrPa/V/umcb13lase+V77qFY1VVqm6rjBdXrfG2mTosystWOnwy9Y+rqkHlz7d47qle2wFutll"
    "dLb2jjHWnn3lR+iSQHk8C7oQy+jGVcjfLVNjCydxna65JyivCz/XSZSZ5kUDW503XNt+kB4ueKZfP/At6B1DtKN9afjd0B/Wzzuo"
    "jUWDWop0Ge33Uki/s7oA7d+hh8SHxLiuePc7+6vt8Q3yC+DaCv4UfSf6fIFb8+V57NCa7ZtvH8CDxdW8J3t8Tz4ENQlTAKaysF6A"
    "t941Ldff+9axFG7fSy5p39Q3W6nxd/PzaqGhTX699FDaHWL4CMaS/AeLK3kfC+5Wj53LHXW6OLsEGf+sfRW4ysJ2ZN3+cab85vKe"
    "313S842looPDsNun+q7/kNTODO74mMF3mGh8DjT+wFY7lxUjW4x7/AERLDkv1R02cVLWFL8zAbrq7KzViXk9EFCbPLzEXfqVCalf"
    "d7B6lf3XEiw3zK8wp0ufeFmBkcgWwnlj/x4B0FrfLFzWl/sPEuNoWXSjy8c1+kiee4U1w2acjPd4VPtesZ28sdhaxRJt9PA+E/3g"
    "co6mPtiYHyzyu/yxPqieZBFuQduYY10GM0om5GPI8WQj6SI9GRz/bOz+s7H7z8buPxu7/+xZ+GfPwrBKhGj3LHxVT6rfS4BgwPj4"
    "fd54++IbXuZUhChBvx7iaq8Zmg40/LFyVcf2xGTyEQUTvvKoLxEseLlovfCsKCO6fjTeFqBQNU2ft8WdzKHojzmf3+tEfTSTMMzi"
    "M7l1Lrd+W1aVaxTOIUAvuyW/485powu8vu7LaKTNBabilH50BI07/kwgm871AtHIzSnjYRonI35qcuoJVNrwV1Fkefmhjrd1U/32"
    "41PzmPvRHGKvdHCtncR/QrGXZxGcW3GdPM9ml3Sp0rJerbp22SHOd6xugX7wUk5iDO3SdN3rBmbNdxfrvb+Ud5KXrfiuDjBUgEiF"
    "u4BVBcWb7+bPxX27s65Ce43GW0+HX6PAGYtxkooDkLlFXp6FE39GIoqw0llHonx6mqoy+6IY5ckM5rII4xaYw7PpMJsU4Vjnz/Ks"
    "zMqzmegdR4UFGc48IDOZ+bC4l1ZTkSPJDKfjrY4IyzDtbv2mDJI0ENujMaWcCw3Vv7aKd8jj5KjSv0/zpFTfHKsynXf74mX5aisN"
    "j8dbk3Gng/VAvSj6dk6iPEixgfLdu63zeXc87o2iyaSDTV+/PsU207B8mb7qbibjTjzumkLZOIjHnbLbnbWXyUVZ5dD7ebdzPg93"
    "qi5gugPzPJ1lKcx00T+PRiNYNChS36vCqCozzJyIUvT34fdJVEZ5/2kVDqMYjgJv4GOSjd5USf9r+MxBpB3l1XTYfwy/mHI+qcJR"
    "lMf9A/qbVbA0+/fxuxjBuuOF2n9Y8W3HMHvbf1Tx+eFZxUttlozwwd+3FeM2n8ZJNMmO+rs6YZbNqln/y4ov8N+W9FrzQQUbp4wY"
    "+S/4x0kiTvtf0beQ1X4Ov7i+L/DrJMG98A18wqj6v4O/eXQKKX+sQhEnyLb+UIV0OkHK9if8nohqhnuo/3v4BR8lRxv9tALhYjIR"
    "eRL1RUw7g8r1S/gxLiOGSuHHFA9VufxAbEe56CfwO53AppjKU1eECaQ66Wf0WZWIpqJfyF8Uf6M/kr9S9s06kT+zctav5Dc9h4vj"
    "8E2aDfvjmJ5DI+JncTgVRxFhb4rf8PeY/2KwsiP85L68xk8QQrjJE/hVTcpEzuVZHBLVoVfWQ/xxFKXJt3QgGx1j5I63sTo98yo6"
    "jA2J7u/FMir6qfygfjzHH0VxCjX378E3TB7Vvw/ffI/Tfxqj748jEDMK7O4b87OYJWkKEDtxiKfPTK7Mr/FniazvMXwlM1jl/Sdx"
    "CAQmm0y4Dwex5LP9++pLFn4Iv99AAn4/ivnqPu8/g6+ZEDEuqf63+GOSqBK78icKb1/G7DMZPh/wZ9F/EaNzLhrtV/RZ9D+nv7Rq"
    "v8DPo/438EfkU8DVpP+7mF42wmqJ+n+E70TkIqbyf8BfU4HLp/8n+M7Q8vP3+IEijezPp+p3cZrAUuqLMfzOJoi7kj9L2IXpmJUD"
    "Of+V2Ij4F2+ubByeJHlZRRNGHQyqGM/n3W54hOxFhcUzfOUX41vj2+M7IAMw/8IU+m/ATzUHv1hfXf9sY20QEnuB37fWb699tqZ4"
    "MiSMRvFGPBqoIM27Kv2z6M7duxHIqNJN0uAXq6u3P7s11CkkLlHyzfHN2yCjADNQoKoT0nXP4BfDm+sba3dUgip6Z7w2XNvAovsK"
    "0C25e8RJq0IMyLSepOVf3Fm9tYG2oDJFQd2O7w70Owfo2PD2cCPSKQQl7o5vQ10mdKCFy7U7a6P1dRuX6+vrdxB5EpciHq+Nbxlc"
    "Dm+PVkexhctbt28Dtpu4BEzeie7YuPzsbnxn9FkDl9G6+CweurhcW1u/u75h4XI8jqLoZh2X4/Ho1mjNweXGrbVba+sOLm+urt/B"
    "ygwuxxuj0Wc1XG7cWRdrsY3Lz8bxMBq6uFyLAW4EgsnmuEpHSJSC18Ahu+fMGo2DLZZzUB6gBG1CvSfT9WhtIV2D0wCd5/hulnqV"
    "rFrBX25FlEKTplLoBwM9bqRb5mvW+hA9uS4aCgfbtYRzUlTnw3Bx1/Agmk/vE0vzt+i5NHIabVwPeXIfLOq1/8LHdMAdlbO8m/c4"
    "ZqIb9zUmy3MvI3q8UF10udctauoaFysqo+3+RFeO4oNbxDVjN+poSaH9U7J0nueanb53BdMsjibvXRz+0/vyhCXsdEuE+ZbZoXbN"
    "bo2yqrKx2NPmfKf2ki6bHllSj4vO1NnQZfOtQd54XaAHc2YTGfnWQJIaHKdeYjZhcUlG13riQkWsrSCXncG0LtpVJJiKyOWEjeyr"
    "T4sidzXxJGhNN0P9HXpTu/yCjAppkhzq79Cb2uXHk61DcdLUaGClVyUKNnG/nVQPvZt3IQVszL/jekd78xu523LoIwTNdhQr87Wi"
    "8pwHTA4tWU7G3mtMigO1YvG74KttLN/DHLwnuu29OaS9CcJ8UG7Jw3hHNWM7cKnNRW2zq9P1OT/yK+3tppqVG6XsePeG2X5lx7vj"
    "5JbB3MYmsckDAjCbcCDmc9QUvB1vPa86x+MQeMU0Sstk5L9RW+2t3Sp8GkIyH5MqwSIDvtWqv9UqwA1bpy9ZliU/mCvdNarc3N7e"
    "aUa84zByzg21U+oP8nG2Vctteqv9QUay3hzJvM0h0BqHivIoDEHkPBr36LvLUj2n4GeXKjQaGXle8wZjI1ywKqF5VeBt+azR8pnT"
    "sjrjO801TfLtDnjbGTbaGTrtSK2Ld1QSb434teursrWmjyjMCmS+uiHxZ8N/XSP7HzpsmZUA19bCkocyywVO+tuxjL0Ks4H9f5zF"
    "4pDkLFwqvSwfRSuYDqunKB5FZ9D4tTUYY6/XE1tbW4NZubL7bLB9PslGEd4aRrCdZzBLe6y/ivJBmAtUQ/YHX8KxG3+PjrOsgFVJ"
    "zUDLmCb1TIN76UlCMFE6gokf7NFfTHHu6QdPRHpcTQN0bRaIlM8vcSah7pOFWB0WxltBB+IsQI9ggShKUQRoTJZnhSx4KKJ8dNxe"
    "0G6pcGHPV+cGsLAgC3WfASN1oKHvaREUCgmx1Ys6uD1aqwDZhQkkE8/PZqLovxzsDsLBF/jPY/znc/znOf5zgP/cw3/+hP/8cXfw"
    "Chbu2ZNoSsXibAqLCeobFOIIqGm0MhZJDif1AeDx4i/m5zdVlJf2zyS1fhaosjG/Lv48xE6alg6Ps7zk5rgpboDr5eq4FlnaKvo4"
    "SaHgPmQc4pjgf7+X/zuk/70C2Twtj9WAvo5S6AUOaCyAhcpvWI0Xf8GPaJgnE0pI8OfXVXrMfyf0NzrKipKxARgfUlkQzSr+SoEp"
    "y8RYfMufdvNqlNAHbp9b5ma5UW6TW+T2uDFuh9vg6gkFpbgP/CSCLRTHN6bTG2dnOPN5Ue5HZ0/HXwnxpr8aRqiNPaf3xP3BfYHq"
    "SNRmiJMkQ7qzA3QlTzJIS0l3cpBf/ONtMs1kTQewzjiS1gAldJzCYHbxZ9RcIhF2AC7+x6QEBmLysUanAqraAsBu2ACcHkS6T7xD"
    "niHfMVQhAFn4GEpXqZW9LwpA5kjnAsnrn9sCzx6drLrnolcVonNahYd0cWAATglgKwaOOcUbIPVxbyLwT/e87I1gxAWGT+ixGrEz"
    "sOggkT367IZQOiojmDkilC+S50hb4UxX8h1iz2IeW2IT7zNAEnuZhvmrbBzI6xloM09EAQzkpXjV7aqiUKm6y+kMVlayKln59Dzt"
    "5YJO2p0bL3dW/vTqBshYW78ZrAx+BVJT9ig7BQEOutOB8QLd7ZJM9Hy8dU7a7NcFLE+8rEnS14AburYRaQx0Hr5geaE+f8IXPZOs"
    "yl+P0BYeGAawM1KJ43c+TmIEQVUq/EGqTxIVfBezLJu8xuw1ckmNbIxAytcplYVVkkev+YaBf4MQ+5pDbyMk0lOQaamCGFBCDUFH"
    "X9MK5bpOX6cZSHXUeeShr80I6Kc9DEpwxiLTTJP0U46FvmkQ+pfkkeqnHLylXrs37rBwLcx6OhJqKe2ePYw7A6pS5CtDYN2D7jZJ"
    "t9IVJPyAzdbpbm8PBnjndU28ewczjzHAi6+S8rgzeP160O1KFj7fLPMzyc+D3x0+fdIDRgaTLbpzmIXRsWL1c5aF98db2L3wKcz/"
    "FIc/KFFhSCp3JEJAf4A0FiQPx0ilJiDI99NqMiE8AwUcvXkdi3EEPK2/troKfHwM+Dh+PS36t8VN1APBUjxTIEX/OYgSp6ma4JfQ"
    "HBJ43BivAYt4G1EgUcOZBbIGAsT+OFQZ/fMqB8pAXUqghvi1/C1r55/HZTnr37hBssYx0Oj+Z3dRnVrADKN6mDA9RbKrB0Adh26W"
    "4jXdwuFc8k9pPr62GvJyeC3H0x8Ms/IY5WCoY4R3OrAceW2zFUjRX9PXL/1zXvvjJE2KY9oFsN5pj+HzrgGe5imIZFRq2BG6WNJd"
    "nSs89s8BI8/HaLd5RnL8HCF54Q7uvXiGMXq+xdtG6A5Il69nEYqtA8ZjT+FxexunP3wDc/4JbkK0MiQR6hMlSw1CnYG8AtPxr0mG"
    "/kyTooCMff4yWUcZHjgh5/MswLOXyZH2JpD1iL/+69//H5ObYZmnX5gEWKn5GaQ9z8+C6IjWosoqohPs1CH8MYlV+iaFtXUPT5+Q"
    "+YJ/BnQaBShgLT0+IWK3z9N5UATEVCkHZBs4L6oc+GXlRSUkR2VwjpdKQDM/OT0WKZBSkDuwe/i3lneGgmPO+X9U3wYmjU56dGjB"
    "MfDOB5GNqEUhs2nuC5WvUuFQhuzwE2LAKYlFDI1rB4Hxr0qTs43JemdRTlQiXYHGPkGpUcSAB5UiIYClpIem/FP4GViVYHNosyKO"
    "uBIpg1pZhPQDIAbJW8inKembXDlTOv8ZycSBTLYA02wnLU5pwOcR4WcePMlAJsDEYJxn00DhLxoDOoKN1aDYDGgXcw5sn2AogKmK"
    "oKQ9w0upZ9o4jRIcF3JyaAYOPgHhPsD71eA4KtL/+vf/swyiPEe2E5yhAPYJ9wVQnMoFfchfQZnpZnlxzwS+0VOT+WIt2GP9VZAU"
    "QV6lqPcga4dj+P0UqODhBBhX3g+wH4dpNJtGb2BYL9ZCEOyLAG8lkcvAjKUxCjdvsDxXj23jsQ26KrhKEVjtAV0Pg9PjZHQcRJMi"
    "C5B0FdwuEcGe6qxZY97e9oORqrHWRd2nWle9fekFz7Fp+JI9OT2GHaYmEw0pCt2j0+MzMjeFLn11fBaUpxmWK7at/N0sxr1mMBiM"
    "oA48vGWpoFZASApmkwrIORztjgR19gimtJCpRZBmwSnsUkDjcRIDAKOsyMwSgyLWKGD9AGEqdH8QuxMRIGegOYAFEjyvSLXFuJLV"
    "UPPZeIyIMR2GVVYEB7IrrBwANEwz7GEpURVSF06B6QOKVX1UUG3OUC5eXqDwMxesKA1iufqhAlz4sLiTEeRXsO0nwVlWBSQxQLVI"
    "s7HvgF0yb3cIFe0KlTPKoPRrQDBuT5xF2J0gsq5xH2pQgIHchSMSrKgbW9yTKFXIKtcs7OAZHC0zyoBhGiVU9VBne6l6Q/cjmLDY"
    "XTcyC1YDEKQZnqvifsAqzbkqLoUcolz0VctgmvBMRLGae0NSmCzY0NQDg13VqoGKYu7oDhKovayaxEyTMKdWe6OrxVk6wurhT3Dg"
    "IgGzHojJTHbV0EsgwrROcjGskkkc4On4TC/fGk7dVWzXLSkjf2m80up1aSSXAAoqCansaHAvZkKiwW1Y2XOCt0D6AcoGBaEFzoQR"
    "0mxB9cCKc3Yht4GczrMR9SAVFwUYaAXr0WhSMD27Wy47kI2I+kCsccud+nQ8VtOEqKdhEREZj/voXi4qgPeZPVmXpNoXWZq9yCe9"
    "UtJP3flE8jXsXjWTbM0qMGSCeg9ZAZKH3Iw7imMUaxFriuxQn2eU+hzEnZ7GMnQrpR4VXIlkVbBZRc9tsECNyCeoUm62ZG14sxv0"
    "mOo7wmrIU0q1YxDGJwNga7qaoaCaVGlSuOnmQP6Qo7CQxiASabr/ID0gV2HwXrATx8yhEXMSJmQUMe4kNenVao2mwwqq3cW/AQji"
    "FW7NGQwD1rZV/R5JPTgutGEEomvP0MJ20uwxng09Q5xiOhYtRMBvaot6ITnovWO84uF1SFrPIAMmjO+bKE0Wxk1QCCFJCjVitk8Z"
    "eeezJpJ1JIXrwioDXqIWP+URvJbUN5GdTYFJw3xmVUkGokBZsUHZHam6gUbv68G5WU9MHrSczrsWBI8T8QV0IAyUngO/yjCQ6g1E"
    "wy/YGpF3pVv6keSu3IZZtgqKVRMGYHgWcJIFE03ICWGVo4i5M5lICLsapfJAYV1+uhWoVFWFKmBXwmoUqiKtxkC4qlzU+vElgZhK"
    "DJxdEWma1Mg/xx/NgePDBwVyCN9NiKhAzrZTjJjYWjmxoCw0lm7mJblkHfzAASQ4CXQj9sErhRN24xgZo/xtzxGejen0sMdfzSmS"
    "IIppSdlbWDJQIEFYjAd5j+voOZXAktlTC2KP9panJUjW2ePGsibc91IWsQj3/YCu8eogajkbMJXSALVWlwSdNhcZg+o1pAG9Swln"
    "v5fCtpKzD32EH3UAq10G8jRLgLpVBdbeKMjccD6UbJygdUrASqB6iarg1UHA+KMFjjSUrx1oSqIydWBUp7uwmOIFJVWVBsvkYZJS"
    "STlCy2g4YaXM7kSpZCj5KCcdxefwxyTCOabkw1ZiV5FTZ55RB2QSh3wkARo/TAZ7ASbtB37YDQrBSwr+2t2rBPWusiqZVfmMiPMB"
    "fVgZcMjEZPhjVZHDwQLrwL8mmUyzkWbhX71beDHaBxhzanHyrHOFJkBqCz0yOwQ4prU7GECqMx6bRapUUtYydUC/VMvUADoLFTgk"
    "HNST9EUhdK+Bx1ekmXMyrW5rAF6VvQwFTTx+lRkw3LnJmIgx0rDz03mAn1gl8WdmXtYp5RfnCT6EkdnA7EgOBa4LnyYdFeG4Xu4/"
    "3AcJtoyOCpMHvFXILl78H9jJ/+//DbBdlW5VjosI/mUlhU4Hdo46uck0g01BYpJpl0+81CdZrK9FEnpSEIyBJ59/Y7ojZfD7hPsd"
    "/sFASHUMnJymR4yoZ5ouyHQNNxuVEuYcPue/NCTEDCA9kNv2qb1hCRGoHi5sBEexiB+mUtoH+gJTen6KMrQBonkHiIc024xPFwKS"
    "7yO5weVF0lxelI1MyaBQ4Qft8J1KwIpr7iWqU5Q+DfgXLTTFweiElZjDk66d1PnPpb50H38EpD11AXaOMp2NayKWKlgL5Okk1iCT"
    "DE2KEAZajVjHdA6VFlASZD5AOXp4yt0K5PgeIS2dYiStOOC7Br0UDLvfMZyeQoe5ihDaBErPokBoJ7HCVTIBVlIWaPeggCqaKJ4D"
    "jSjKQW0PkqrsRAOzj2lStPOXypAdNf3U1acm64X61qViGhkcRCIpU3smjRtGtJCsl79hHOk5o3ySM/YlEAsbDBUz3yEgPF0r/bF1"
    "6NEYNQT0kaGelEUY08jOeHopMcSajixkxszApoXijpRxhClyuik3DFZRFp/C0u0F1jlY6VsC1NyTJgy1Bj2nnodsn6wPxFHARBGx"
    "d1SvXHdtbRetzpAKqIHOST+q1K40NBD3ItQqKn3pJlRyQlphVIgr8KjUAD3ibWQ401wEkmIFHVqeXRvp28HDEgi71o6wrkmr/wpb"
    "uFVnSrspa+Wk4tSsHtmi3ZJVjIdwRRz0gsdLcEBK2CStRLOtP9ItDu4h0kpwIkDxTlKSLzBsUnQXwTDL3tDitnsER/ueKcOQmuXS"
    "z2auxXM5yW70GRN7aBbJs1SJk0h3EyiFeGMB5wx6fjQPjgAvmBugjeeCIhM41aOJB/JKPOATQZRFJS+XkFQQmZMcTTTEk/HaElA5"
    "NAbGAVJeDR75F7EX51hOicH6qtT4klIfE7Wy4bktrXKWvo7SKE8b11QNSAv9CO0BphvG31do8lmeBXTVyBm5oBsj0mKgDkXdNjq5"
    "kpZYEPwvjM5onKQySZf13ZM6ObLWB3jjwJsRsYbGMkGB6kgNX1RDRC2mxVK/gVy+KPNkBilbNGgR44UFUCr4jZODEESoC0VC3Zr5"
    "qqcHBAz39uNDK+245KTgwXMrFUqLPCVh9p781HJzHeZQatoUoAWiL4foGC6/rXyUgJ6inHpepUkJovcko3VXA0HljCcLxnnP9BNH"
    "Ldr6Ki0HnvBJ01yqevKfGIBae0gAlapCQcjjqgLJhTzMPqMPI1jqKSiK5CglXnaObIxvSFhEp+HD6pcgdqk4fgEIUoQ5DXDCgA+5"
    "4yWlG9qLuCV3aNZ/FbjzDhkPSpXuTj5kAV4pr3Xy+cqKpWMkwbMGShlCdltC8TRbQLRoD/loIWGMGpBFqua8p1l5X3JcFhvwDmeM"
    "KR4gufEesobwGNgiyLUgAMT4qBU2FGDRUvW408Tooc8GAhhCLQcJFJmJIOmeZ1cWcZZBVWZPMqL/1EvkFERdnBsqXmLyRqUX3ItG"
    "x81rCRRtkMcL5IEx3tAW1vWW5EAF0J1hVLvzUE7BwiCaoEb1DKHxBsOopFR/8YAaTWSPd1AtjfWneMEICEUzIjxznfUDvEmSwrCe"
    "SLoTgKaRU8u13cNeBo+w8CO8SQaEaR2wGjf0REzGPWdOHZ6Oulpk4KRwJ+zJZKkEZ9tia0GhPwPEIU5Nz13wPNVx7FnI0nDggaRj"
    "X/FPOjfa3aUhoLbevRaX5gFuXbjiL18XkQVlQ8MiUPvmImFIlZL4xtkueFL0Ytxu1HagDQJUhQp2SZ3yEmibFPzpmx4b8qOwr+ZX"
    "5UxYiH3EJxVKUrcBT8w9LKFjA41zFBBsFzxufZVneLVNj0QCNIbSlSjNy3MLiSxLULcpW8ryfbxuYokTd0ujj1Wa4yLBZ41sJ6Vu"
    "KGDhnCezeR83nD1ZwHEj3sGPdp4EaF2nMSGnmy47KEIxMu7TZZOuSo+4jFOBND7BjqjLP4BMiMQdqIs0Fy1au25jwQU5OKbTG0pR"
    "0aTPtDRAGjWNKGj15Mz0KSYS0JwD/EZDrVgabMV9PoUEw0nEO/yNEDMbmlpFITJVUovZfARUZzITa5qOpXIfSpmB00RY68O2kZF1"
    "EwlMRXmawXm30LdmdF2t5o9MOtTVJva6UNdtumKlfsUHLFUpjUaQBLJNi6GAaufLfpMXmYY2MuAsLmXd/zUKNdSUy0umGY3Euu6T"
    "ZWyQJXQ9tOm61UoPz5ojYEZxMh4rSy2y8EFZ//is4MUTsGoLcVDm0Rnfd6LEKBV6lAidkAYVT/hLllL5lp5RM2PKYFbns+7oAwmb"
    "KzAe64u1T8gSE3E2PLPMfOpgz2lPHdqzU4efZjrGvNQnngjdNcocHUu9ubw1dTPtGxwnUVlB7elr1ciqfNuFFSSqPYaEnAy0YGUa"
    "wl2U2YyPvkRxFOfHsykdxnk9GO2AZJmo/dP2c9SWYb2RZ5yYKwUt05GEjWtU4xWaDlqtOqOQNE5+NobMpI7A5ZY11o5yDKQIkcyW"
    "XN6Ya1t+yWP0+jLfDEltJTxJYQeJwfVsSLoC996YoyqB6rfgSxh/+gCmQNt12hJWJNkokCbED8tuLI6wIbE+MhNHDlSyDYEWxUjy"
    "44mwk9OMilgykjLncwqjDlkK3QREawO3LmqSbcjjKRKb43kArG86lxxZ51JmM3mCD8NI+XrGR6jAuYVw4Yy2hX768i2ax0k2EKkq"
    "cPexyiJ2W5DK+VjfdOismJvdp5VOr0aN2a6Zh4xUCXByfVOvmnXl0lbrvvwR2MbDGhT34ExCHvI3Ak4UemzYYcRGv/zTqN3c+lBP"
    "8OzFkycPn3yuVkltihnm4Nm9g51n9whGzGhrNYEOHz3cUxW1Ah3svDikeiKpe63l33/45OHhAwsVHpCdh4/u7SMIGegAAFEEvdjv"
    "G+IU0RUjZ6O2dp8n6ysU6iO5ruUEFBoQGTecyt7QaexNMNX3F5IA1QBBuMFLRJzauqBjgWVkrgXtkxAIDILuphggFyORsvyNH6od"
    "0yPU4T2R65tuIpRC0cmWy5sAHJ2iRE+GfdS7BMgTttPItjZJHUQtVXd21BjQIlteQzYstDVYyxLmWy8NxRpWiVXUXh3NdR5sMB7C"
    "C/rQ6a5Czro44GwgkLuq1ieSmVjdx1plnU4vZB+cNGYau/zFjEIOjinhoVE0SNywwEGkn7k/yh5WzzP5ZIJ5ZmSzKhuErxtZkkCZ"
    "v6g3BIN8iDFK6K2LHGiiEzQYXUDcl0YV6hqkoSSxYJ+QphDlLLbCQiA+FFF20NF3Gd3aXunpimBD7TJClTxs2c/J8yNzQVXUsk/T"
    "p+6aFVwRnbGUeBzN6Aayb7f3gid1QXv83lkZMX/HFk+jQi8xkGbhZ32VQVJa1mCkAWEDcCeO2dePqS3CJPVExqqxCSqfIDThleWH"
    "RMkkI9sjENNHJZ9c7HNkXEkZCmVwTCPj9pHGEU9+24SLAt9zlsI+TIN4L2eAaQlVaKpCSQbOAKokL0k8d2sO4GxYJd3iPDtLZ9sF"
    "Y8FWXjvRWgeCYs5lp8lkoo7yZMtuzXrfqekLOME5w0GLflKN1Sg3jYvEYHxNgqwB6uYrAJyB3NoWsZo51BlR8679sgZDhxcaEucF"
    "gZlI0Gue3gyfvcZar0y/apm9jVXFITZW8da7qAPc1QB3/QBnfNagS5gzPm84+cD6pDEfyi86t0jSETFnnFJ5kaYmQF6oEQjeyJds"
    "hEDl0GUVWTLQSyU8eNCujNzShaW1c+yme7qipgU0pdsIlFfDlvwgLARS3UpKsrY2Z4+yorTL4m+r7VPbukSnw04tqcmv6MOxg+BG"
    "R+UO4VOahYAYB/htwuFG+V02VPj9OhsijCia6hA5G8diMlamJEDs8KdBQwrgIxFrUQEJAwrFJDGNhAfQEhragIlfqGnR78ishS5H"
    "ol5YPMrYtJETjDBjz8aTxg1rLdd3w6pXq7z/fIEEAR/74BVlPX8nT6L6ktDaX/lAgG5Y7+gbVjncDIsXfIDSx2W50u3bXFnQLFQk"
    "ZLJrtMmcbuEPqTwnJT6I+QHdQU+QeJ0py2mrs3QNjsV6AXmsQvGCXw4q0+qkNI1PLatebeHrbgQNInGDZljRKM/glEEvIS074FoB"
    "M12WPVsTxpq0ZmVN5Y6NU2RUTIZ0AVXdU2UmxkjOWMVQ1HZ5kZG++Zl8aMeWiKrlw0yZ7smjO/Kr3IBaxMZcr/9a3pU7U6gOq//d"
    "nye7/N/1xbm7cXfPalsXZ76BUsp5IlUTfBtu7nyURhg9FyDblwPCEPPqbR/XQr6N6CUiaV34Zy1XNnJYzVDpLN92VDmqqdBGpJqR"
    "tFoj+n7tJilVFfnquYSSDlJkkI5/a3kFN251owZAHWLTUPmYDx0WoR7p1FoXBKtup+qSiO4n9bK3MR3rrtYIba3nhxld5boaDIWQ"
    "Y3yBYCqSF1j1GiT7fIqKYVlwGsVCMk16vER3HrQmSccr7DoytuOjBU8VjqtJnSQCycIcXuEE1LqpIK3M6K01a5bk7xpjeyKpA/+y"
    "2nmgizesatpaHKFBHkuT+2z5YdJnUlV14DABzPG8YnD3OwKx3R1yYWWFbeVJjBBmnBzJ8PdsPu/vyNi8xWONhTnxorkFyeBku2Oo"
    "IQjU6vkAfusM8XamTCToUg8Wy97hl5gtSvfJFuww+/01ZI+BBgxZgKTHYuo3Ht3kHWEUDKsjCc52KeZUyiYrylgFIY6qhK5woB3Y"
    "4vTLzpFit37YVeVpYV/lWlI2v5Vb8AyTX6GaZ7/EftUxhY6j6ASUmSi6TYGT2eeyd2RKyI+M6t1MNBBK9PpVF2nlmbirx3618qod"
    "YzmsBQSZJAHQ04N+BxLgr4DvNIkiSljJPVaI8hrlMpaH5ENMtaXHQHq/Czp0aOoaUKk43xVo/lyy7IArOjQqBaBb9dcJKD9Iy1Yo"
    "J4+5tqG0Gi25/RGnrN/DLzf9CfBHtWSYu+hrAYnaEjc7wcp35XIlnOLBPCjz5IjscxVeau3ek3fKyqBS9T6Vh0dTe63gnueaDK04"
    "6dZWb7wGfPOGDFdEa6kn9UuAhdCPeYf/ikUmucUhmwel3TjIQRZurr6HPaZ5Fs0pzaSZCS45ZPxF36mBtTpK/eNmAeGV2sgD/mId"
    "qgWB79VJAYYOTXjtRWesPHeefJscp8PK9js1r2v5Wb/ppZQnYEAT3JDoH0XRuFPU6Dw/zWRy4bSjTHRQuZtGeQ6tnSZwbsdVbYrA"
    "kQLOUOqoHSELNe3gwR0VBQW/1kdWTCGAZDvSrQqb5+GXm65N/ohkEqmyBhnRS2V5R4/v/5Gi1Wo+dN14BORdx22CrUesivrGGMWF"
    "lYIM3xlC+7PZ5My1Wg7V+/6zxkW07hj5ASArenIIoOzkCydfjnwf9SFq26Od1FEmHW1gi0hmUBNCdt+94ADPP3g+CZEHpfjEU1Ki"
    "kE0PySmTLI8miHRqxxaKjDuOUGzcj6EdDCXrBY/IYiDSYjGTMiK7aabH0At2DAR5uRjhGYmNPU7Q+Rk6lAwOdlT6wc7K3n2NGegK"
    "jFlpSWQKK1afyRZIh8JPQ6ZzCZVmKpcJhv3ygLgK2ig8jmyLHF0WsG0ojT4eKfNjhIBEsodQAk9IrYu3EUYlCR48PDg0gGpjauEI"
    "N0QcSwD44l6gaso+X6h+0Ooie3815VEhjfq16k4+ePDs945m/2gZ0FX9V4p8o0rBBDvzaapoydiBoQUzTthqvNCjRI9MZEoyFiWe"
    "k/B30Pll1wGQ6/erCKWUU3k/RA9sWNE95QcskTHNw7faeBlIi5dZGJupGINq2k+ywQKjlKgxss70sGTxYJc1qLQnpdWlHqu8/LVk"
    "I1qm2DieFCrGKnuhCjgwBaJaSV0aiazZVsaBszwbyXfy0myFORUdkovgN8Gh3G0HyYyiYkhHI4azNt0KcTrrac0MzZybZ7UKLOKl"
    "pFPSB9tMTZ29Yv2cSOoTUTjlm5YHKt4eFUDzU5IFzQs3FPLiib7yS9VdtuWdxgJDkw2ERTVvveMnSZEMJ3alvWOWHckSe1a/YCem"
    "lJwIfXXiXsHDnv+mSnIkypbxonUqZ988SsbtFN1eDcXQbExvZWoVw9COKQsd5jiY5sUlHWrYVo5abq57hdJpZj5pD5Mq1szdqMpz"
    "kY7OmrsyK8hytG8Ae4VRAd7XNn9IBNCBdCzm3VqliqVSVcCbRM0mlNWMznGiF7g1w2Lgk4eqM5BuSIx3DZCL0XpM7QfgTcnoDbu/"
    "4RdrZJE1koyUGqegWeQxIM5Eoe+VgE2Usk8OWuXdgWsMlguKHUWOP6xztHQMhM3gvOkpVdcKOeuu5Vmfo00FydjxypNZVw26E3rR"
    "PLen0V4zznmeVIslqty5o1KlIPB9NPn4w+XHLpJkQnB+MrfJ14uZPLQz/UFOxHoKtbxSwd66vjTlsdXoBE7KFCyHbcdyAbRV7+lJ"
    "xnp8MkQSaJwVUdQ9ypROXOheiN25yGlTiDCu4ILr/IjeSE0oL6trpX3+yQiXdWzXQOUZV3k1QbJsFklEtjnSbQr2hMUSnG70mCPr"
    "oOU07bkVW827vcd1g25uWCQjSiX4J76rAbGvZ7xy1nwlKH01ZtlXCFSKvXeqHUwvQTWnQ7twZUFHwG1+HSjT7zmCsiy3mbSlJ4RZ"
    "Nv0kAOUUlIbPnyrLttqjKFgqgy1dzNvaYaTLWM8FNTGwXl0TjHIwat4AKLNW2WVyykHdndoIYw+k8iGzW8Z2ScrPWfIo4J+WnTPf"
    "esgCxmcpFaDrWD7sBZ31cOPOanAUkpHXem/jTvDmqKuKtnmbMHoEAtMOT+VDUnq7y0Kzeiqp3htIbque+/K8yGeblqzdIcHWqB+5"
    "/KkSALsGT8q7Kuvsk/GZ6z5JSVtcAbDlQqrdqbjljrVlvTkeWj2Lru6w1b/yLBeu2iyCzPjUppGWhgZ4wbozTl9rq4o93tVWoOUU"
    "1md76oD5doFmWkRxpQGk/GS2p8UKedupCpBzn+f8Bu9AO2PCRWAu+S2ZRN70F0TCenZF+GSPG37OX4vbHSkbdtuevW8Y9sm5ZCdz"
    "u5S+GtwzXRorEzANheK6HBKReDSS5wMYCPRokAmdo1Ha7r0s31G9emW70ptSozY0/MbabDdLZsg938y47FCbD2m4avY822eIP9JL"
    "F9QhzXBClB+iIh/1vqkQyUTWviJCXRzT8cO+WnG8ZyHR2ZaFq5wcSzx7hAhgIDEZr6DjW2G5dCtEfsJiPZSRzzQRbZBC7qV60mVU"
    "zc2UTNVQVkkLNzobzWOfsuYIXz2Rm3Ir62GqeDFlJ6kluy5qFfckvTjEvzpVxUMk60P+1HnaM+kz+qj1wnTANIGC8x6TE8vnGfcK"
    "jtUBuxzmna4oDRelnDOWeeDD6oPt0o4fTTsFFzzjsLDBS8p0HwM2qxGw81APhJkEBIF5sGG4Y66jOtM9G5KHxpBfqm8pQNVAGbPa"
    "oaKaYL2hDZSITe/wnZ21SLyEpIYPDQxcaM+CR+O4kSE+56fHZ3MNq2nNyENr5Ap4i3dUKBLI163mZ59P/nTuoJ7QAaNKszGsCFSz"
    "jGjZ4h4DQq+8rHKf0WKIRT68JorSMzr3GmslVpOheC6U1YtczPQyBArqi6BH8KNi9S2lK38U6DQ/mNQypR3rjjJhxfMYHZdKOpIR"
    "DB0d7qVHk4Q9WGIaherASrO8rI6qi7+BxLKbR0Uy0cXkCxtT9ThDHz9F3Yei6pK8g+BTFpClKeb2gj+yHJ6hThAPJiTbG++QshJN"
    "S9FPTfJtT1GpwxJE5YYNOUIUb/iFBvxhWzR5RYR58sJsl23oMCVlkf8J/JEpRnXBRwr+rcE1O8Ii6F0gG71BRYiUm+wzP1JJnE2h"
    "e09T2Vuly8kJnX5L7V7WAVlru6kzIOus08dH5FI/ZvI2mOPklt9Tk3nTZLK+wMm9ZTMrllcwc/VD3f2Fl738YwfBNHsBPpyAU+SQ"
    "LZHYV7fC6Zoj7fSCpfOCjB6qf5JZrjEkrh0uhN1s4VPKwWLHphpd1aP1moaveKPNKi2eDkJEIZ/k86Mz1DvmCfos1i97QXCVrzAq"
    "NGrkd2Y0pugkS2LUOMwEKdVmIBPMymKTPfKcJmh4PINEWMKEYCTv6jEcVqD6ukF+tFg4nKq70cZLYM8LYtJH5bR18a3EzJ5qaY7B"
    "T26lYv9MkgmzUtgHpDuZNyOjhGSFCL851EoiFGxsD6S24ktfL3fMYyNsfSc9G1XDZNTtyenTr4TlqpCv/LTirqnW1P0bah1JEfzX"
    "v/9n8KxK6a+c2H6A5oi6pNLXwpRW8I++1yHSpjzQSlOTSWTQcCvSJjrSBrUvDSNpy6i3DmwRli14yUyVDbW9Jd0uSW1QKPV55FLa"
    "NVjUJUfmZqyv3oCZTaudd2t4aSrKsnjB1ivjKieVG60jyyNpL3gmMr7N1/tc8UeeEN9df28wD3faAxfQoa0WukDFufHGLoAmCjtT"
    "Ry9QgaiawQv2IuCjR4C27JLxC5A6wPjxBuwk8wQxmJzYDdXCGODfAD1TZikcMpI4a4QyOL74M/uRbIQyUDn8EEuHMrj4n0VLLIMH"
    "2ddiQSiDpykGl/KHMRAXf7n4D6Bdsc3QnEgGu9kwSaNmKIOHUzq4ZhgQyolmcA8/Lv6OnsojT1SDna+rgjWP9aAGwA5GSREhymFT"
    "pdCz/zvzRzbYGeZJHpiampENUtyF6cLQBksjG2BYMHsKl0Q4eGqkQ+g4RgybwVSLKgDkywAH9OAhCmxfySlyDuSVznJrDXQQ0b0+"
    "4WjIExNESRpH3CYwp6Os8kU6oOBraKEfLQ518NR2lQ9rCJZiDqsMS6a4pJxoB1Et1kFRoeYVltbFX+BDwDhPLv6ejqpJ5vQ3gA2P"
    "RuSjaBpgqKhhZDUaBnCwBho1HV78dRqg/YsM6Ib/ZJDniXjQ3mkd9kDUOhvgc2jsmqj1utGhXoALmhJlbzLqogkwMLn4my/oAcji"
    "BBhj/VDcG/kgcGIfJFFQTbktCmQ3imIdagtRKCMhCJ7tbCzw0RpMqYmGUE2Dr0VSEsKzES7iXFUZBrDEsJzqtxPcYcSeuWBKYLnq"
    "LkORb9DzEjSGNAIoPio9MOzaFBbiEUa26wX7osBv0u2ovppW4BeGbJtEJkyCI2nyRTvWywMX5IMZ10iIjcpNHuKldqSIlVpMIdkp"
    "4eVLTt9AXWHbQ2GEFjYdsnoEgOXFX/EyIzm6+PPKJGrETHhU22KLIicA1JqEWxw6IWa3wbUq67ETQCADdo7AiqtneGHadNXvC6FA"
    "hYvLF9bn/gNZ0JkYWmNAgqJJ8i1O9IJ4CjsSKvdGVHgkiPA0KFdLTIVHDQKn+hC1BFd4gj0dZ0kwy4ri4u8nYhJQ4I9Gi61xFoAU"
    "5FmKI5BI9ERbeIQXkBblPsqQMuH6g32L/j4wOGRWeGfB3g/Z4sALuiuINFkXbohsQfgFDq2Jd1CGncuVFC2MwyALRnYkhqM8Oolo"
    "A+nqaCkUKPHYVVuDgo2T02KD2eIN2xi/vbIyK2uU5YpVAjnXlcpnQ7UIDZqNLRlqa6QGa6JFoNBWEFmMmYzxSm8P3WDkyMVL2o3g"
    "8NRaOIZf45oloeCo4sijnlgOD1OMOIz8RuBpDrgUobMAwcKcyaaKTsKoRpME2Q6k4ck6ypFAz5B0WxyLuk2MT2+yb6qkLbYDhyh1"
    "mtdNxwI1LabvnkgPLdvTbn5BxIe0bXNneYK0Pm7WUov8QN2PJBCj3xsAwpojahSlZllzL9gD8gPcX6xwcAiDegvfmgy2hILYcTQV"
    "1EZCs5tVVkNSSIz4SWjb3DbbaoSDcMdNTNUNjOuNCPG4oihKw6oYAY4rWCvTmUC6JouxZEKOLTPEvUF/IyTEpemyHR3iMQlZ9vaa"
    "JLBfzOlnE2UDqDJmoQFl5sKwiNYwETxif5gIHFZ7mIhMhYmYUIwIFlBQlvpznmSIol+kF/85FXm2LFJEHuXWUvXGikCQGYbgyFpD"
    "RTxXaB+h9vl9o0U8V+xKlkq8ISPuYzjdER5S2gJG6HrGGrQ1ZsTOUV7NvDiww0Y8zYETeKE4dMReTgEfnC7p0BEjX6aOHbEzIf+H"
    "FGaMwW7E3iLWhT6vR3QrCBTyBKmAP4YEvr2P6I02h8htDSPBFeIEWvKgWxa5J658mOH2SBKPYGNG9ZWivBDJzHFj4TuBJOSE9AMm"
    "8YuCSWhQ2giLYkloyOXRJDTo2LfO7GgSclFg0IuFASU03NKYEhqyvW07qIQGn4mCDvelr4R8vOwCVwXz9vawEgaeAzRjmWxRbAld"
    "4OI/MWCzF14FmDCoozWFMYajZoSJg1yUWSPCxF6Sfhs1Q0zsAoEeZfUYE18KkFMozHYj0MQj4Bnp15En0sTONIKTWNYMNQG1xaIR"
    "amLn22riCTXxLHubNQJNPMuKqBlo4jE+SZguiDTRFmhCH/LaIk0YguUJNXGIJ2a5ddoCTWgD8Jri0B9twtDmOrwv4AQ0z2ukLeCE"
    "BrADTuChdUHACbUNCl/UCVYctoWdEB8g7gTIYdS5WtwJqSgKhlHyNqvFnvgGhE4RnETfJpEn9MQ9u2SfZSC0Ol0h6+vZwvgTRjex"
    "JPwEo6wxZ20hKOoYNiEonpj9vCQAhTyzxCRNtsWguEcLYGkMiijXVKotDsUOngYjDdYHSTqfIgZZycMqT2ByMCW5dQSJSc2nT4b+"
    "OBSHgpRix9nXwheHQmVLFXrsC0RhwRDXBTl/pnR6EzEd5oKmR4elSKLCG47i4n8g7cXXLXC0JW01lpI6KH9oCilC1GNT6MWjpXW1"
    "a5z4FPt01sqZq8xQCh5Gkyi9+EtUD1IR5Q4e62Eqcn+cigk74GoEqqBe575IFfsgeteyVcSBZITuR5UY55nceryKEQkz04wwaKa4"
    "GbZCyjZxxGcIg3A7eAVfEaTZsugVk3roCkm2UoPcEHeNL3RFVBBvj4q26BURR5ioaJ31AuuAefFXS7WGmgvSruRt8Sv2kyPgvKjd"
    "lUcNHPhRo4WFMSxY3x3xJlSHYVIOS+U3Lr8XaxTJ4uJvKxOas3H0LRRAkik1+W1xLHgR1ANZpPZt/T2osogSbIYPdqSHPclGF3+T"
    "qvWctLxa0PYFslDLCvudZieRWV+qbbvNJSEtLokSCmyxACUqrEWUL4prgRonKC7bzJuxLeR5PeGLNSQnvP5QW+T0EDUY7XEuTPmF"
    "wS4U2H8IX8SLQxYHAqTLLGPCx03Ya4DVqC3qBTJIhlhazvLNASs2I76Jg5fFLfm6JQLGSADBYO37ZcrIgetSdPPKnXJ4bD0ohqWN"
    "KDAcBjEMdhWomL0nOMY9W9BuC44x8193LoqQIYtM/WWsQBkxeqXwh8qA1SmQNJqLbW+8jBoYqY9adG6emBn6ft4XNeOpvJei7Z+p"
    "Qy86GSoTzR3s8Bn3MQOmwMTPQPqBGlMKoIHmNaSLCYPi4h9AMDFZTSpF20CTrbS1pe8STkNyC5myPJxGSzSNPXn9+D0F09Cko9lP"
    "N5SGc6nfEk3DwCwIqIFKMySeia9CO6wGwEX5ZQJrmKOICqxR5smwuvh7nBUtsTWIVxDXpAAbVWCpQyUm5D0r9ALQn3+4SBut66Lm"
    "BD1vw1AjIEC+ONzG84TYp2aH2ZJQG0rMQTYjUrolZ8G0JeLGQUZGCjnGnoASb0cTRD1piCNLrPVF3KB5SnJzgG4JuqHgbGW9CrwR"
    "i2WBN+7pQdA1lLmFMwh2r6FYp++5pKNLGnwoPCJNu7kcrYqKdb4YvhkDjmR57ZoLhcYcGqJHf6gv/hoOGSldtShlnjcGx+HFP2jY"
    "J0nBtiOW4/aoD9IRfMasw7cOTHhkYfGJ90JScSCOzDKKo/XNWnckfzO0MTAY8YXjcMUQRBsLHIHeUDgaKxvPdSOgZVFgS2Mkw7eH"
    "5lBynHf512J07ByBaBXLOwGrYb48YalRGXAsDNCxtKLssuE51G5kUwOJfqMCoL1nr9nl8Tlyy8/7okqzqwfo2MlgYZ1k9RgdKOOp"
    "QwgfX/FI7IvUsXfxjzg5okNHhNwW763o3rbMGjE7dmzEahknsw8uxcVf4SiHkTvkgoKOLAnc4blKiiYjEo9zGcfDXZNkBUT3ubRA"
    "0ZQIOvFo54k/mocYoblXGERLVkhbMA8sz4V8sTzu6avThwf+aB5P6tjxRvQYyYgemmBnlrfrqbzDsAN7NCbOH95jcpL1ASZ5y6qx"
    "jKnGNLKjd+gQHywS44zW2LsvyEeuT0m1SB9PrfvkhwdkLDZqrDJpI+ZaFeQirokWoTSQUFMsTZN6lkkeT6vVCFuzsZsVgMXDGQiP"
    "aMsV1AmkN9CHJHTyNIdmWqiPuWSwD0XAdeliQXEr4od7o6tLN0J/LGQnoWYn9TZ7AXH5OJGiPyvFeCuNpAqRpgfk56wR/uNLXDme"
    "8B/EuFTpWviPXXM3Lb1xuzFADrSliW136A8D4kxFtjQWyK5nArNFEUFkAcJhIyLI8zwbRZaI44QEYYWVNyaI1GUZgQdr94YEeRoY"
    "83ibs/BejYVUFqAOLS0qOOTgCd6SpIyuhbk1WjOh/rURE6RmLmEP1woMYneHhUimuNQJpITebniihBAGmHTaTXpjhLAC1AFeEChk"
    "l9X31kHVjRSiOJ7ajcAt8TkX4VMy39wfNsRrWSFtJloCh+xaMhsKhdLoiLAjfbmTvR3LndOWACKckFnkTyoAapFEngKnKKKWWCJN"
    "PRMKAiDimROxJ7QIgidTQn6MxkIfLLDIXjTF7Xee2me8BZFFRgS/JLQIA3lji+xpHVBreBFbI1SPMfKc7jIiUnad4GsD7nVLsJFH"
    "4gROSIuijXB9AOTY93vDjRxgaBNkuyONsvZoI5lzFdUabuShntblAUciL1Q94ogfyg45Upu+WswRoL/ycLkw6sjkmCzd3agje5Lo"
    "xO5VQyP2CGrJ8EDnbgO+pop8MUiAER1VZKGvLfYlvfUGInkkaXFTOmtEIyEyFKEgEqXHVnU6HgnXRUMxqkdvVBJ1IeWQBl90EgnI"
    "FiiuItgbpoQPkbXxemKVeOGsgCXO1C4KWVJ/euENXcLbAW80WwKXMOZQcegLXbIvijGayjeDlyjdZ5otCWFi6eizehSTfbopEHk9"
    "ksmjGnpMMJNHindeIZyJijTCLwWAJPmDmtxTLN+wrbbIJrs+BVJLZBOyYLR60BbcRF+Ueat1o5vsKb2BrSDnqy4KccJXXd3GPvQF"
    "Oak9yUGRRBxVSaVCj7Dxr6qCtphtgCn5u2vuCacH9QQkwlMYbMjKF/DkEm3j0ICFVHT4/o4N23FP7sM5ubEs3bAn+jztg7NDmWBd"
    "1MuTpF6ZDabra8IqMySNjxla9lRs3lqqmwVbS1flpLknmcrQMvN+KirUgmhfBFbgkx2bxqeG0GeVfhJjaiQg3CWyAhBF+WSgOFHm"
    "D3+itntjQS0Og4LCAYZBMdg5iRQShUOBvEFQnKGpJzykTvExDT3cGARQm1brW56YLMV9gVH2PV3yB0aRkJqOtcRFufh7poyVapFR"
    "mDtBvzE6ijS+aERH0UB3/UAyQso9nI0ozfwBUtB4NaD3A25vVJyUfVgQFnvU97EFLwk1ZcCp4vaYKTv1p0hKxqf1LG37tWU+tcC2"
    "8XbL6eJoKtajBKetBYFVjF1iLbTKQ9+A6yFW9qqibIhZdpyVe3UjLDfWiukFIA8JQqKokD/mCl4+8GQ1GzRxV/YzZT7AN8pwvB2i"
    "oNhQVbkBWJ6gohImbyISK7cRgaUQGDQHNVaLg6944OpxV54JwI39nKgZeuUAkRLT2WwMY4jaw6444l577BVXzmsGYMms+/slEVjk"
    "2sG+keCB9DK2b/zvWDf+jVAs/JzE3JooFuQaDegqvEFZ6Ia91lcrLAsJEXwVc/FXoA/AkBKl4hnXBpGqisgXMl2fTDMMqVpkw5xu"
    "D0u8G5dKUbIDyRbGaklY2smKhdFaUG41wVWSDxmpJfFGakGUGFQTm1KEzxOopZJ2406kFs/QZKyWnRHstNTawCZQi6ssYTVRJMFb"
    "g7V4ptYK1+LPtQO21JefCdnibHZa8guDtsidSjZBkPKWGa39HC8wz1jE1H6lXIvdAgdzaM1c52hzXE8Ilyzn9z4YLyUyDCOtcYXG"
    "O2SUryUBdOhfXNdpt0Z0yRaFdKFuLQjpglctJd4LkUiGD4e+jbxRXV54BCzVbwrp4ii4XPLdHtbFMhGwsQRC0XE09eJF3Y62BHpB"
    "PTqJqXTtateJJ0c2WaXXUs41WjPii81ScfGQFZFkfBd/HyWZL/wLk0kbqnXXmkgwGNTl4h/AkzLr6tsh+W5UGIf7Fv7oMEvs0nwd"
    "cgPFRN5AMQ+bbKs9WowtGzjhYg5EkXmDxez70GvHjEEJphE0xtMpJ3IMap2MygGNi+Rpxhs7Rr0dmtokuRY+Bu2pcRU2Q8ioZ3+O"
    "b45aEBn5hLWojqRCGbqXCzhykYkkHlqGE0GPkZxwMvf0hT1bdNWCyXxeJXyHr96mKkOzelwZc2xBK7mC7khtCwXbpAKlIv/TaOtp"
    "sHCdLKB6XgkZfP3doAS1SDNs95uh25n2IZiYM08L7SGC+iUN3CQy+VkzSd/++poxaJ5JdwQN2dgEolGrYpjJd8d0PQZEStIj5dFA"
    "X12oGwZXoHYj0+ycJKzydeA4PE3kiU+zw/mx3MAYy8E8a7IM0UF8Ivt2utGZZrJaIU+KnGYeVWS+MDUXfz1JokVhatD5H3FYZV5o"
    "OKp+bAptJGZdzUScAGWYaly1hKkxdtNkM4923HzM1/WSWQx2cGG8Gld4Uai7XNwaLRyoNbWg9BPvHdwlmnVC2fC7ikYwGySVNdNN"
    "TzwbtToz96Ub3cLjAlZMLFsQzSZqD2eTqXA2U288m53pMCvqAW08/jiaYW0eGwtyTX3Yo8iuls7c0DYvSKabVGnkxLXZJ38wlO4N"
    "bHOPLzSlUxOBj8JBFgjZaYosF5yAcMlwaFVAq43oyFQUWk9DTlTEEVqzJEUzts29t8kwsamWG95GkXCpEZT+WvRYA8tMk0nqtC3I"
    "zY7BkT/KDQKY6vqGHHsD3ewUwbSKSULA8C0TvFxU7xsCoWw6auYXjTg3j+RDnKL2pqYR6yaRl6rWfqG34dhOrsgU/GYqFtlPTPjA"
    "h6QtKYgAVpARpFU6ikiXKYsgZYyIvEazi3+gHwVjP6wMg0KyYCnExH4DRGdP3D8jskbZJwObamqC3VjGNkovqV8g9YIXFuSIzqKk"
    "FpIRcYQKiYMZ3og4SdSMiEPoQuFcvXOixlui4tCbRQnYGhYn98fFYenVhPVRbxb8wXFmFBxHTGeAvyXBcSJlNhblzQg5yqpwUZyc"
    "2mKxnxzNyDOVcTM0iZQ/KLWvOgUdCezzXyNmDt8fXfwtHSV+MUCHz9E0C1cX0avRkrI6kA4MRLJKvFbIWW3YEk8HZYMIOai68+Q3"
    "g9b9Ch9IsvpGQg8YsCnQMgwXXcBPNaRRED18U32AVRj54+rsKBW9ZWTdCKxji4DK95fqHrryygMXNX008apEW4SdmsWYDLST0UMu"
    "1mxcJbqOYxTfCLBj8Uu/eYZaQo1qtMtaU8VxlrOFMR+O2dqqvPgrXVe4YXf2mbBgKWUYigbp5p2vCbuD+7jF2sMXeecx2f05A0JD"
    "MjS69ETeUa85LHBf5J2nVm3iLYh5rkrFDr8D3esUXUvOXxR4x6mX5CRye5ZhUDEX62oByl1uq9ghtxF+p+7G0A3Do3cuNeKDteLx"
    "KOARHjlrxx8jlNTi8uxnl43Kg2cYrvnk4m+wHbNCqp8LW9pzrhACu3Y4XaN73kzEkXLnE7lbKFO243YV9xwzMpJzSrSCwwV58XeM"
    "y5Nt6rtPDMgjVLd8IXnMSVJfY6E7R/X6KiP/p1KzwTeGiHh2cWdf47lXLSxsyOg8OOnKYF75frNuvJrxeXaak2uvsQiv7ZxuyY4X"
    "5PBMdT/OmvF6MNAOnf0y5dOvLWTPAaC0opVmVEz/0Qjcs0Ohf7BGDN3DfUSpLEtp2/bpqGNdSjohfHaMYgwSWgP5kPOUqOkRrB7R"
    "R8l5yn+rL6iPwJ+lfO9p1euP7PNUuwEEWggrPGrpSS84jODwz57ZYtkGvtWsteIJ82M6ZMF5o/3ot54U8kfqvJsxf2q+bnCmQfaf"
    "uvdXbtAfzQZS9sBkH/6UAW3UiP7juOi5YuwfZXAdSS8yzfA/F/8XfOdZLf7PIcq50tLECv+zSxcuZKJtnmLWQgDRm+vaJXI9BJA2"
    "hrfMRptxgJQHpkYsIF08I3dNLQGB9qLpDGgcpTqKqpZ4QHh6RvAICW0HIwBxOCBcfhgcqCUekFH2SD9rthuhRlQgQqzjY4EeoqvH"
    "UNJATRqh1eMCHdZOH5040SpqOiOqivBswxKvP0AQyYs1T4W2+GhWZkIqFHP344kW1Fyf7xMryLtSm+GC7Ne8zeVjRQxqXapO1CC1"
    "kgS7bmmpcaG1ui9wkL19fHGDvpRRS9jQWclIC8IG7dVc/mn1VsKnYEvQ0hYzxuFASwChxc3Xgn7w+5nLRw/aMT0aK1NOf/QgYify"
    "WQ4enp+T5mAopitFNRJ0RR5nfueEC6II1WqtXe45ryKCcZXSsTLVnLwlnpDk1cbyxRNR6Etpgl/yw0DFtu135Z4IQ/uCuYJtc0JB"
    "Tl03is3wQtJTJAU5wVcutr2BG1OIeHU9qtAeuSD0xXFxSmrs+WIKAUtuiSd0Ly05dmKgXki2taZjCa20BRM6FOlx5I8kVO/Xw1S2"
    "bQ3ZjiQklcbOgyS1l6Sbl8jEGGqJKIT7rhlUSF7XoB8PelTPDbTGFlKvyi7+52ViC9GQ9OLzRRZCLUzWFlRI+1at9W5haCFJpbzA"
    "teBCnid8wp0EO87QPln/MllpizTEuTXstEUaOmSDK1qmrYGGIg9ZukSgITxBZbzJiAShEvEE7+vZTTeHG1KLhj2cax+WqCtFCg38"
    "dUKmBtNMGqJaFqSkkpTUquATxnHUCDX0ME4yuutzAg1xamA8ifuCDV38GZ2ffU/hhmTlqKjCbZXIDtUu/mLlpRZpVoIRh/DNsX5b"
    "fPFXZlmsfXMOpxJN9WBDqNzNmu9KrGhDB+iIRV4WurGGdBwJK9rQgXQf0Yw4JI88IzJvT/Jm1CFVFEcxSYaC3k9KiSqjkENCXi7y"
    "4kPCFuXN+EO7WVSsnKAutdDujj0xiDzXu94IRPKQ40YgOhRVYbxguwGIDmtKk0YMoucVKQsyPt+oEEQ/8jVxQFagdIM7EbiC1Asg"
    "1FBj2I3Mjkq01/CfvGj2bIoh5QQogcTGcnwkp8MWKgQRP+Z+dd63ID6RjYSZfJNiZDrLITcqPImu0HPZrGK33sq9ORmbg/SkIKUj"
    "PX40Kr4NxEmCHmxkAxywCL3KFJtIemCwYRBxmKIRO1w4sUUwWYsdrEiiYIUv033OE0K/r4Ve8AAmFy9ws9xWmznPf5GcYqQp9YrG"
    "Mc+SYRTciaaIRTvOWmbTb+MLQxr5OpIlxTFqdS9hBTASdviih1YjPMMF7/VRydopx2NDQ13cGsXo3lsxqlD8ukwoIzxQkXLOhBgw"
    "+yWVdwJOJCPLhlwSJ3xb1Vc2yua2wNItk0V72uoHQgc22qkr1vqWJi1U+kzhmD858Y3M7WhfswjuETVownXYUY6IOiXqZTkL3fJa"
    "3bjZxghHcGaVUUeIasi9Dif3ghSUALvQzKQ3mG8iNaDAZV+PO6J7now75dlMZONAXNsaQMcwWPS7d9dEDz6nnW43FxQ0PK0mk03Y"
    "HUG5pbJASsPJEZ3B60E4WBl0e2X2KDsFeTUqRKe7KUuWW1tbg1kJlZIeMy+Lr5LyuANJUGR7QDx70CcokTagREpQkNPHLsx19x9D"
    "98MyTLvnsh2haxDcIta7LfowzrK7vZ32ptGs8/W4iwwy7oit31y7JiAdi5han1Ctus5yW+hR3vi3886/nf6q+2/zG0chQKXdrd9Q"
    "CKpy+5DQ1ilfpq+6/cH5p8Db54NuX8yRsh2MAa9SEkARZBDeH2+di7T/Zhx+IiWWnfE8fDje6kCV59YUPaIpggxhevhs3Ome40SI"
    "radjPG2PN2EOvYNXcyc0BIpWKpl/bJb5mayOdAmHQP/o8ZMoH4Ko0zkY64lsQzBXNB/hK+Rzu+45jf/b8dbTDva6G+7iJ05jN/xy"
    "vPWgg+OFefx23DuJJpWAfPmRRifJUQRd6amwj8X29stm6iuo9IFVE7f7XvUYrL8grKs6bNx/RTnf6hyYM0ggFBr0bjt45Itphcq+"
    "k1doHIeiK/E3N6197ixFWJn3xy+/lG2/eilebW+/GdMfBLOK1TfG5x0M1/cwLSc9oNJ5NHlWAVfqqKq6PWR7oxJ2CY4ByP9ge/Dp"
    "uZijldGgLz/RcGgQnqf9Muz1eum8S3P7Baxkdq3bx0a3VnFPqMaeUMZ9FKpK3Vp4Po1AZqmm93P2U0un2gKqBUboS5/DhuUqRDck"
    "Y54+7F1AN66j7cF2cER9fL9WV03tj6PyuJejZyloqEuGTMMzILuSSMoG1d4ZSFpIU/TeY7bHpnfZb9bEXZwASLwBn+EadObz3UEf"
    "M26bjNuU8XiXRs9JG+EqJL3ZHcxDfKuGLbm9B7qeFPcBz6XAQcqx/Ne//+9qOISE8STLcqhw4/bqajdMncRfYuKN26uqu52SeoQv"
    "7KEjg+6vcCr4ST10IirFcxAXccI0hvZlYgNHCH1Ynk2AoFCMjUGIj86dFIMvrA5r6oj/BuMGKlBeup2r1BodZbSuMREO7qedLqK5"
    "fUFIZMF0d1ZDa0WVK4BuNcPpr2+vbn8OtMrE3cOdNe/2018jelWejLxHu86qK0X0A7CEigBRNKb+F+Me/oWZhd1pcZFviGop3j1F"
    "MtO58fLf4t6rX904Ur26ViLnnYj0qDz+9Yb5/s3WzevXeVUDf9t4hTRidRtH3u+t373733TW6qvur3q37nxmUtYwZW3tpklZf2XR"
    "qd8ZRhZno4oiRY5yjD96byLwV2cQJyeD7ia+robp6o1Qr/y2BM6TFQlW0Y+GRTYBHG2eJAWIXZOkPOsf0y3pJp6XjwhhfSBUnZWV"
    "DA4oK8OjkI96+HIhLbuDUDeNYUZ60WwGcvXecTJBKiA3BeAPuOEe2YSJmJYOZPZMCxj6IDcbWNL8DixKSaUI549FnESdQQdZtsiL"
    "FfLpvlKMjmGwfTgZ5m+6IEIRKF44YgJsqQneIoB49Ou19Tu1RIPKP1ozjGv4xbNHh+Rt5CBCgtlR91zSB0kXuXtngDFaxQB3OHYy"
    "zFn8wFryLRLHqDVYCvjNTW6XfZy2zfwajOz69U66lYen407eDcV2D/5055t5h/GWbF1+1JsJ+Sg8gXlAm0qRwmoZsA+bQZhzfRGN"
    "7HFV0kieDjkGPbS5GfUy/tXRk6k+5EoKz6OSHKegddq11VD/uk+BCfovB7TCQIodTaICdtwAnTivMIJezbkD2dYpqilPiW3jIQbo"
    "SScPN4AeKGKI+Evk9LeOJozogpdVgLBIyOeMrjDrstT0B+Csr9lVOq049HJZ9BEFh6IMYf4e1fPUaugY6RWOLr1GJfMwKfQvrsWU"
    "FUsK944j5IjzsGj0wKmkpTTMMpWO8aAt3qMCLkh1EN4WYaGlCirXcSjkn8YaacC/ovyIFk+hSODq9es6DegcrH0Mlxysbtup/cFs"
    "NJh/en4vt09GJyuwmAY6YWcy6Qww6fWgOx/QRP9+vPUVeWUF0k7PrzGsPIZuBb5kevgp7fBPfjtE5ekNVGJiwOGVgM9unyja8+l4"
    "S57mDs/Q0gU2rqpicP26k9VL0KAAJFGAKShlsO1bBvJwOPetEVGr021OoF4cTpTViFrZYhhIv6a+0WyqzLCKbdWHvm4wpDEbIidm"
    "VssF/gDSxH8S/pPPOhY85VnnW27y14MKu/ayhgSYVBaQxMvBb3+rUgcyWR2kdnL014Xvep2epTNHUpd9yziVe0cfbv/wF6zRPDsN"
    "nkMPKUJvZyB9qwfoaHk6KwN+iUxIrHK0dk9XqHfDiYCzJ96GjkTvXx6mAT30QPAhZEiIkODxSvksyIZfA71BG+iiDI4xGH0UNLDQ"
    "6QZTUR5ncW9g9VQOgKQeR2OwpTUGCkMRg27iyk63zue9MuPDcQ/OPRNkmwUqCTt3wpU1IxAhg3lK/asvG+IxTgq580WmBWUeRzPg"
    "T/QJVHGw7cxPn9J31BYFwBv/W2e7/yJ597ALwsV2/867tdvvNta78Lk3iaYzEXe5hk9v0DViJ+1uy/H0ecNbhzOZcd4plWhd/kZI"
    "gtGFXqOoJX9tgnTZYYSsApelJuCwtZn+utxMf/Wrbv4yfbUl4B+Fj9w0IxfRORdXpx4Svy61rBsLGlUBqVzVVGseJmEUZmGx9fJV"
    "ONoC7jjZurZGZ1oAjbYA/6mavC5dOaBYAyc9zOZJA0ShPCDXwCZUsjYXkwKjreedzWud0VYn34q4khQqQUc3iKOiN6uK404uz6Gh"
    "IrhQGaAH+9Ld5GMxiTfYtwSP40kKNZ2dyy5eG12/TuGxUYqlgUHV2ZZKAg4re5lhLzN17NHVQBWTLu/DZD5Xe9ia6kIREl5eScEz"
    "qA9QgaUhGDnzxQ333ogzZJqbGmEofz3FuM4ZkPHyjCetkPOxtQiG1A0wvnwr73FUpY6my4YCeWvAm8s8mZV4jIMu9gQc3JlMzOGk"
    "k9JcoAA8OeukIKYoTKRmcF8gHtRiLrdgkfy6zis3S1jQcvSGO5av5MI9n/ft1M3yl+vbgDK9jEKYcjyM3Ytgzu2BTWas1IBCePZZ"
    "MsBiWwKQ2aiQAAke5sNlRXGF9u0++Tvka+CM+rgM+SkgH09ozcWjBqnmEYhINYPGuhhbebu9xXPaP/00NFOKUq7W/crfp3lSym9A"
    "ocBZgSKm+YrWOc9tjF3RxN2IF6Qk0vJC2S9/NbDOIbFhFMS8r20NmO2QRtmoIyU1U9SqRB+A0wStthR9khKW2hKKAiFr4cpzq3JV"
    "cb7ZYKe//a1VOfM+xanIlI3TCX/I8jTeDWeTyt0+H2K7yPixT+PZlpTWdqNC4OEQiFoKZ3EQaWZF/3xW9s+RQsulGkpn9YqRhLPy"
    "6YzCNC0Gq1I6mcQSahfVyFHaAIsXtwYif4rp/fNP+eD7UEoO/fMG5CnS2/55UrzQTSfTKZ7iSlpFcI6J8T7HFgfHE3QaJ0+UfXXU"
    "MfL3Hr27gMoKOCi+e9fx5eBxmZKpkj2qQx+fvFWBCE8DX9I9Q46xls1FfaW0wxFsrVg1jSdbq3nOfE5w3G3RbS+81TyTpe31zJci"
    "wNe/bp/zqtRfL2AJTmuUTCn3JnKuwzzLSvOrSmL1+Smejw9JKZzlKpFfz+yRgsY+ZZGJAVKtUEsS4SichBWhuzcrt3toRzyDRblV"
    "bXeESu4quQmSRA/tAZAff0mSgOQW3DJSKizyaQ9XOIl/r2SnNkE46UClZbNSSJJihVtZ6alMFX73LjYVoNhznGVvCpOEdChLdy1E"
    "6LxcSTdE28ZbnYS79CnZy55UgpyoHZm6kq3E9Fd1LlGomm2Nt0H2cqswhSOUpmoVYlqjwshFrEYbSGTQQNbaQLaVNRrAtEYDGSO5"
    "3yla6yq2CrcuVVbifGZAR1uj5vQ42fUpmUBSy5RMeEpGcn86i3oLT/ycDut+ywCgp1oQ5RsFzIkeTvnhYHbyOonxDB+yxjJu6h2w"
    "o51BlnKvYoTlLfQYzYAa8LwZtx6POvsj3u2fikl3W3311cd2jym40mwNXn563uzu/NVADo/rxQOJ+QWzNNr6Qmob6vgOnc3vqVqi"
    "c0aqxW7XIvM1Qq4wsGuGjViY4scijD1mAIMxNmRtL7BrQWGpir4WtMCgdgvp1Dsr9SYYjNpIW8fB+j+iwYpKG6S0kuka0l6o+gll"
    "dCYHUYGyHdaLByCekIzliR7agqCmS4lyst1CHDyXbAREU/UNtKa+AFRPUIClKol0hAPaeT28DSSdsa52nyUIu/bWcpvADWCoKf4L"
    "bOk1SKtHJMsWzqC44y97vZ4+LbySigOjNfgWeea2kEcWyaXgqP5lPQXaQZzbE/WHca+hBO0MhiDJDYAidb4iF3Z7h4dyJ5IgJOU1"
    "e8F/PsmGeJ0rZxBqbapFVbV2OZc/h9bm8esvLykbqaqMjNRg1JvXvEO3hrnNiwAohmTVnNxVR2teJJD9+/FyLOlFSXnXr1uACwv7"
    "MWmXpk6qAdvz0BiyWakM1rpQjygbr5kGLo3bfNFBhPCqAIFSkU5ZYqBIojMG1TdrrpuzgbuXe2PkbcV+aK7xIIJ+4WH90FZ/PPEt"
    "XKkw7sqdg7LYVkdJRXL+LMGGDqd7VIZ6V+PL8rAF5853787h6LCV9/RRKYy20JM9huBIRmEGPxgHYYHp2NCmRFOyjZg0uNJVrJCj"
    "ADiHFi2IC2UNUa0G1eylK8hqFXBXL1ucL/rqhfmiyFswhP+H+fGRADVB89Y5vPIO5LkmSTuMQ5A4QTzyzjeKSPL+ko6ovinXshJP"
    "OYifhLkp/OVJ7VTeyitG9MzgWEkjZpfOlyO8E3trj33z4Gtg0aRM2yalQU3aJ2dAnvxXSMWudtlxeBS+3uoc+5F+tHWMSH+E5TDQ"
    "eU5YB3JXQ7zUix931bZ5bVBpNxrSSzzU3Pgx2LLunH7jQdB/+GwyX0lCltCQA3phtoiGhGKBhEqLrUsrLdlyNgChIm+uKqeGFc9S"
    "aFlhm5TonILh/CUmgJAWgaxJq9VudGpxT7H2gfPdO2MIAM14OHeTU73nzaNVz3wTWKf3ZhRkCFR9pHXNB+odvCKrXe1VFDzLYBdD"
    "+FQc0EFYbA9ArtV6K99l5LZfDgYR0ZJugaG2gfW1WGA31RG9mtKs228kaUUcydYgz/Jxu+Va/aV4JZl8ozFM7W73AILrsgQUX21/"
    "QI12Y9Ws2atmzbtq1l71B4NmyXW75Lq35PqrPmxaOdLntZ59x4UMrKfcev/hpFvvPSCgdo2yG3bZDW/ZjVd9upS60btxxHeGJfDt"
    "a9fSl2WvmE2SsjPoDbowtFeh1OY4CwSNoCWNwnOHT2ME530FQqw524p6dGo6FITyAiSvbEt17d27LBwpCDpXhcD+dc+vXx+F1Va+"
    "nWwvkIkPnu+hEQwLxXgb0V901GtCy3NXvJVonZsBBuJN5qktxb9APj+HWkL495xFrn6FA8c7qrGFwufovxOYT4E3qerS7t27a8X1"
    "6/H2RI7PoKEjxaRuH5ugRqpuiLSIU+A3/VDrGvv5YZf1ktPslx3rnC5PsJgSvrTP7BJzn5K88grVaqMI15zWLvhLf/qadFsHz+0i"
    "eqwKkx9svLAVyy02oZqNVnBf0jkGlU+D69dfdLRi+KUGKng1D14ZMzqofEC2eom0J5HzZNeFSZMZppIVKqJlEP6x6KTbi9po6Lzw"
    "/vP6dasitsehqpqwtDgNcFMwIZOfOthcNY+VCgv9ZgO0HV1dPmBPr0a7RtvvCjI++RMpR87JnK0v5vD/sjWPnoVqSr8D3fXQznWX"
    "wEqakGzVW08u36ybjAfR7RzNPATQRJxyOH/h31LuDmWTl1y/jvSx0CpxWBLZq+72djS3lpo6WR1HhXVr2xmwPn4AqOQvYP1SRe8q"
    "1pNO/Q4jPNEZLBbO8RsvuFHoxH3q3FGhwK1Q4hMb8MEJ3srTU47l/eWqoi3V3R+MuXgQEW8ZJCiUV1umWKy/1RzBIo672zH+rbrb"
    "VX8pYddEnIh6P1aX6wldq9l8rob0mrmjpSU9kgVChuNaNAO8dDWxKqHrmZXTD0tp33Pjnuv1b3EYFkuUalgohuyow8h+AYeRfCTj"
    "AOIl2adkdPh0LKsQ6XIkU7oGNgZnagOljQ2UxAPUvKS9JN7elkeFBESDlEac/ROIuq2zzgLYubIqJC5Jsti1NbzoevsxrlqjNm0I"
    "mxbLdHQ9xBNFsXBxFx/HYOFs8V0mGi01lQXNUrQkKbpZ5EN8G25SvYVeeuv7/fiy1YT5K1RHjeSjiv75UYM+2zKQZ8122hhaKIUN"
    "j13cNyAehGaBiznaYYVxk6h/D22LJvZDwbJKyHKtuVN99456Wk/Gzlp2OS0G/8pkyHBVf2+1aZFTah4CuWurun5FXiUEn9Zu8BT2"
    "bPNHKUafpFkstntkJEXav03XZBFtd9FfDNrqySQhf6pRQMmuz/aRbXzSGSBuDY/cWrrbhkU5mlSxQCFxjtub71ZaR1nHFEFDKcKQ"
    "pxQtcklWtKhr7QOVVr+FnIfyDqyZeFhvCjZLZ4HKiDWpUk3ru3vrqv4rs7OGfpMHc56iA4a+vnpos19BdeeomNVNdXpUHDpbK7gU"
    "19vSRgRKptGCuamr7ZRgaw5o2DZtmAXHKR8CNY2CBaeQ4fBCadpnrcOQor/KFDxmkvFEYVlNQCGqsG9RHVkPDNmpBX9bdeBP+kI6"
    "qQ/wHrx4twmB86KobxVzqKB3C7RXtmsv8/sD2Ci9XMQV4MdnSkfbbB3I+FYKxeFglwK/2rQeAcw6udKA9fEwrBUe275q+fQjbbjR"
    "MhUvv8hAFahYLhnfytp2grrHEHOAMMLHPCRdZF3s+zBY4tOxQZJ6KdkplfhYNtF2JbxpEvUyf0UYVCOCKZ/NGu+CymhYDEKmQoN/"
    "CeC/3mwFE4Nz+oX/SZ/3/WA8EW83dTL+WomTnM91fYoHME05f/4vVl2TpCiXV6dfYHJQl+REmDz0vT6eZKfoOYOeYuoc601mEJed"
    "f8Wu92Sb1nPKf+229GsFI0pgbBqrg6q1lbd9imrc7MfKWbMnxSjPJpOVoTiOTpIs7wfFNMvK4zrAMMpXTpO4PO7jQ5raGBt1kKuc"
    "JLW60T6Cfn/lVAzfJOWKbsmHddNqsyr4u1KbrUXT0jKTQ7oc5BtUQEM2SeJGJr3Z9E0ZZZPz1lxNmlVMYq6tGGW3zzWFkk3t0dEa"
    "hiUCK2utrVQanawMq7LMUqtgNEFfaGkhSt8KVo+Ig2vJlAIfpWVt3xTHeZK+6QerJj3B2laGk2z0ZoVogJP77QqGKoAVuW7Sjskf"
    "KHR9dfWXS2clmiRH9NALuFhAzhdzk4nuYJLxmcJQE8C7zwAzPcaMZ6vhf/VZtgo0Zrg+tRasM634n9Hh9nWabs9aHRqsp5wX/Gs3"
    "dEoAbUehauXqJYcZzmIUZ6dLitmLWBXxj5Pz7BJO9/r2O3MLyVVeYOYsS8ycLVrG/XE2qtC3WpHgk7/z5hpbu3yfqa4ePcdr7f7S"
    "knKClzaAFGU5WGNpKSxm4zFssaW9YbB2MmJh8pijglxmwROo27dm1RjiqElsmDKw+F8jDZ7eAYNfUoXAXbx6iT70gb138nIil76/"
    "FQ1kNad93wHbyFAU7azdWY3FkW/gdXLsIY3eJY7/VQUyGrokqfPTRYxrIYc6PQYiuQLbDARrqPM0j2Ym8yiaueynBynOHm8RSFoo"
    "ZDtf8/K0xRy0lXv6YBtAMw5tXQOTqTbgGJjEyqnkPQ4w5sgoV5ch1wYlV6S8BgFXKviRswcOZFNDKSdehSc4m6ufZmUHPkEoQHO5"
    "uPvdiT9P9JWofq1Ig9zXq6zT+Vr+5Ql8reACyq4QhSIwelQ6wdfeddzVyX3rZmdiv3DL+/akLHaFXbyMq8ixXKbPDHn1TqtyV+i1"
    "LNLe7RlGnCsu0WsCvKT0qcEvR/oY1kP/9PpebTtMUdHWnda2q7jBq2+tRjnf/mpW7tlkDaAr7bRG6WWCFC+DFfeg6qND+khDp6NF"
    "Jy7/cUo4y0YvdNxqIMFM7QEe1/maBX3c4GzeZWnX712YFj8M1m+tTjGo0TAZwbn/20TkndXexq0wWIX/763Dx5rG3yBUGuFzNFbx"
    "WO+9HEjtzWxlZN4Pn3/CqVIxgMTsk75gjXnPpM3x/qQbTvUz5OekHGKFEbRp3ia7GeOZeqHM9gn8bPglP3IO+ZHzq8b74kn07VnL"
    "E+Rra/i8VHVrEdBxdvpEeV4s2gDRwDka8qpiEO6ThlhF30MoQz5N7+PqbW9xLlVlMxrySRJ7tMrnn85GiCBW8NatOukGlF5PH4s8"
    "KXdIMXttLRRTdN/3csAPzfqEycEr9HcXeZqIXzOqSedIn+aZ9UnDspOtBl4r35PW4y9u7cuFJa5tbQn12E9XIu8DsNcdt88hvaFJ"
    "ii/RPcIomrSp3bM8QafPmIPWVycSfDC3vSgdzzrWQ2BdwUGnG95nX27hlx1lktQbve2wFVcX77jQmkD97oYvH6PVLTrnLcKBnNFB"
    "91W4drs7n856Ofk+3jqe0WPbo6aiFF9cJSO0tRpBW4N/ATKGPyXh0gRKnrAsOqUGtkIKGCBhUBHCcG79xANEUtYMJ5BEVa8Ue1FK"
    "YeSRbthA6wXG5iQfjAFWHckT0hXAod3fqlbeiLNxjvbdQbMnq7+0SLUq0DztWWc9/3HQOQziv6jDulTVG7fuLqvcAZnT2P75xuT4"
    "8no9u5Qvr9ezfyJfXjRm4yjk5J/ZTc7Z7Hvxk3NyGT85wx/WT87Jj+InZ9j0k/P2B/ST89byk3Po9ZPzerbYT86h8ZNDG+P78pMD"
    "lf/YfnL2HD85D4kpN2VRigkjJTkpitZFUOQBy2W9oyWyHnZgkaxnpK1Z6TFvfChvjqm/erphw5+Rnfe1mk3a9etS3EFRnwUSFO81"
    "T/uEZUL8BHmeHz2AJI22ANKgYpBMjwbhJ/iAckUGzhGOpRslSoBjGSBU8A3yqUb93rE4ybP0kRiX7gzszSz57bntYPENOzF8yn/2"
    "+c89x4Hhvcs6MCxmuYjiH8d34f7lfRfu/JP5Ltxp81349AfzjPlmmeu8HVcu2PlhvCp+vfCkUpwc0UmF9fyDtZuDUCoa6Buv8Hez"
    "t/3BarAarN0MMA1kjEmfH+qHb6eTFA4dx2U569+4cXp62jvdgAPU0Y311dXVG1g5H3gSjIgAew5dZ797t/XyUWeAAW6BRMT9weO7"
    "vdtr63dvB2sbe3d7t1bv3v0MPntQw63gbu/m6md314O19d7dO6s34ffG2vod+nlz9S6Ar699dvsz+r26htlrG2sbd/H3nf+fuzdd"
    "b9tIGoX/v1chezw+RATB2EiClBkeW3ESJ/KSOIsTjV4BJiEKMQnSICTZkXhd5/93ZV9V9YLGRoKS7WQyk8di79XV1bU0uqtcx4G0"
    "2e6Z1LzbNa1Dx/AcqLDTNdqua3UOHKPjdRwX0k6va3k7kDYdz4O01ev22jLdMXrQjX2Qpbue7fZ2RPuO0fYcG+uz/juG63Rs71CO"
    "D3CaDsFrdjuYNrsWTAunB3DsmNB/pw2AAyrMru1iBdO0bGjgQUNqYDpdCzR3+OFamPbaiCfTsNxuFwewe+3eAaTtHgBgGU7XsW0s"
    "hx+AWqPd6fQ8lu5if4APs431Hc+EfKPXRcAxbbbdHduwOr0O1begIaQdy7O7h23D7bmwVBwhh6LcsoxOBxCE7S2ni2nP7BG8Tq9D"
    "C2CanqumbatjHShp13YYfNTeNjq2Y8nx+QJifbPntuUCEz48RyGAnkXzkATiWZ5pKfTTtdpEaoK+BOn9LiibR18jR+dAvuQvHJjg"
    "sUYm+aU0yf9gJvmzouT5EbfPGtHzXBU9h0zYPGV/vmZ/XuZEz8v/BtHzdXPR8+M/TPT8WCd6nn420XO4SfT8mBc9P34e0fPn30b0"
    "PK8TPS6wvy7yP+fANWzPpZ+MNbgGcDzTkazDBZbb6VmStTjAAq2uJ1kPpM12xpmEKBCcS4gKwdmEKBGcT0kTZ1TSxDlle85ZZf+M"
    "8x56IDnbZldyZlHOOTf213NBVArODmmQQBnnh7Rte10pGTDdQU7LJYdjAJ5IcjDJAv23bYSHSx5EB3FWLpkQfb1uJrkA02w4Jthc"
    "o91rw/Sk5HMNkPNuJhpdwLKViU4pabholZJGiF4hSYRoztJMdIu0EO2ivRD9on+uGhzK8fn6uYYHC5Ctr4vjOJnq4cL6kOTm5IET"
    "tC1bIR+3Z5pdhbwE5TWUPM+k5PlzkUmTx80O2B7/kw7YHue52S95l/TfMyH6jfBE/7P48W1OrH77X+OS/ufmsvXXf5hs/bVOtv76"
    "eSTYN39Ll/R30CX9P8Pf/Pdb+Jt/908+SP/u0xykv2tykP7b5z1If/eXHKT/Vj5If/0ZD9JfKwfpv1cepD/ecJD+eyYGHn/Kg/TH"
    "f/1B+rvBFb5cexZW3TE4+nnZKu6MhwPpT0F9kAxCv2FN/d2ytUW/w4YV++V6VrmedaxxF1jFB4QZv9MT4eQjC3BIslloISWndJl7"
    "anIRnjn2To1R+l719J0gazrAFxbv03x+0S92Ip1gZtu+MHCiDKxlLx2LDr5eL9d61ap6R97Y2UB8C/cKyU3foPu+Ht3UrxaMG5Tb"
    "umpbt7KtS+/m54PSx5t3NZ503m3lRmc5QGpLDbyjBNu03gFg9iZWOlnBV6abfLCMBsuCD5bpYKT4YEEnK0vVB8t4cK74YDnXTwfB"
    "8F3RXZeeZp5IQEOZ4/GDdNW1GLyTPkv0d+KNO4gN7kqHqoMw/o4+ckU551ynwjnXbPCu5JlLz6IiYuxRUJQWwzECp/hvSdEtl77Q"
    "Z1qfDcFGOdX0hZZlolNSTH4yn1W39seR+buSNCQgTxWPVb8Jh1Bx5q2KuwHgLqOUGqrLKNVjV4UTp4/rSqTSe1NS8t4EcnIYMx9M"
    "EfleksudDI2j6Hg4TDInS/fvc4WCuVxBcd/Uu1JS510pUbwrJdLXT5Unh49LFnkkcvxsgcgyT8wzP+kvq8wA85yOVwyqfEYhinGb"
    "M0cgRfSnesFZ1ByYmnAWFW7iUsvBvMClgG8pXAq51lzlUueDqcKlpsC1glZaXNRTysx7ihornqJOqzxFnWrDU+kxagRsBuyz0+F5"
    "gc2Ewv+f3JXM+d+pUIth5HonT38hc6mW3Z+JsMQiSPkgz67r3dZ/Gl2lcsdt4XiOCSdGzGRvwp7hvi4iRYRHa5xa7L8rxSxK9UDT"
    "35Wd+qv55VgPorQyUESqodzNUFsRQ6hmwBX2WRkhQO2vQZCAz7J45Pu+OhhBlR/0dU7Qk/0sYAOY9KTOFzxWJ2qFmugCeWfgDdz3"
    "4164BaaSbTDVUnyWZReMWhpZPBn9xsxZTYmCxVnYTeIJ0GEcaL0R9F50BB7AjlkbTIAfw0XcszzKjSyYwAhSMpgACgweTOAc89Vg"
    "AkvmyR8Z97poAknm+39UbFEZPUBpMC02qIgWkBSCA5QqC0f0wF7ObxEMIC7tgDTDfeZ8JNsBXIXWz2CZxhXLdDoY4zJ9xRyAcJ5T"
    "WKlTtlJjvlLowR4RcgJ/eQyARbnnBUPeRMEbKK717v8Rg61ZuZ9ZJVZLXSn4PanDb3wLp/4X+gf9zaB1UYHCD4OLRh79PzA0XkiP"
    "/m8U3NS49E8+ogf/z6rw4rskDAHQolOyGNlyzhWucp6P0QSSQVjCK4YXWRtKIGIITUDvwFAC4bo4Avthwcl/K8zHFAhyhBqWIwqE"
    "pXAC6LwonK7+633435IsagInhjndIp8cSK/4hbBV6gUIMj0wZuDAn8f3rqIR6uE+SIOcxoYaJ4iFeGjcE4d7YEJItfQ8O7ZIlIB1"
    "SeWBzJxcm2r6u/pYVSOMcXU6KB6jnANYWVi7aS7gIIa5Gwv+WjwARJf/G8dbDK7CaT/W+clSP9HJW14/0tHLwy/0O1jtj4cGALIA"
    "+PiPmjhatStevZlrPJTbN4q3xS55fbxjCtIrZW8y1CTrleJN7ifGiSQNDEakpJA90CeA8zxRIf0BFeXqUmwGPH/Cu95gUmaHOKCX"
    "Dw1+PVwjP6SFdgPVtMQjMubJLtTvobM6WM57YmUj/d5sPo5OI9yiEfQqEvo97jV6yChXx9B/Y4z7Byrs9bWIz8nuuuNYn97rYDrk"
    "DgRLLv3OC4FCW4j2e4txbk8cyQCOWdhHtVW1983M0GGb+rzOuSZ9B5AeOnPxaWo3Y4zRNWpdafLwN/LLQlqij3yQ0Xulg+Da0KPS"
    "yaaWnWOcK444Aez6sfCbd3kszK0aK1YcepacXdIU9+Wnpw3zq/QAmc2JO8dkesDNR9kCi+O00on2LYyx6u8U2zokfpfzplycr/5R"
    "cbBACSrO47Vq39R/yeeialRu65t6Aypx8lGdW2oqvAUlBLemhKqVzqw21XoXC1pSDVqbeYGqRytht7h364hTR1Dtzvov2ix3zCr0"
    "bksd0bACXxt3VxW+0ry/6jhDWhYQ/VTTk0zrHJT39WjQmg6UKtpRnI09YtbLVKosenLk36NoqMdqI9QOKfZrmEXSpoEX4+vrAZ4W"
    "4c+clkE5FCuKqRtc25COZouQosxTvuFkX9HJPEuL85oPgqFBbgr05aAiQBzYcnF4yRRZNOzm0zElxCrNFfTPqyNApww5AQttASbA"
    "bYc58tk4RhKBThr6x2sH3A+MezRB0LwOAnTCOXo7uGI99Jf63Vxfd/sjDJCRbcFShOxYdB4MS1JTH5+T3cY7F9YTWExz5SJBLfwy"
    "wDh0rljOwQbpHPF+isOzXAnFCJWhMmGUSKKMrX0w+VvYNxqGhbnFAj96oUJh9Lg8aX3zyOK+jmAKV6VA3KmwMNNsE6ViE4nNklNg"
    "fxi1/AUFXEZU8bjduuinJn53KkyRd7kg2GKkobyMQp1gz0o32LvY6vT9qRRUWs5iY/dkIkP3Im50CfBiGO2Q1dCuJEw8hLYuSipC"
    "aW8PD++iAp5i0G2sQKiM8CtI7QeS0lAKVkWEbl30VRmpO80dPuy35gPRaT7cfeEeEc+tCQCJRfkAkHMZAJLwEJdXBsRL0VQWZvsv"
    "ixaTcnjjq+KmCnqRTgch3tPCm22Z920UDh+h0yTX6TvhYSXV1VsaMcXyFkYxnmOu6CuUrBxTzg9lFy1sr+9JI63k1zqK31Z5RN7C"
    "qVTR3xMbcr3PtCQYR+fLopdexcPHEthw2DJVf2TMz+VeeIEorPbZDJMpO3dTPL4w0HZMw13mnMLwHhSPKLxm1kvBbwn5/VoEoyj9"
    "kPPKWTkN22grE1nVeK7yCX4f3U3dw6tCYiHZgv2wUH2bhLNGTy/C2T/o6UWYf3iWzpSRgxndI4vYn4T9iWfqowtM/e3fMiazxu8t"
    "5rN/1nsLPp/yewta1M/yljGYbXgRUKjPQf7UL0GWs9L18dHs810fH82yc+XprOr6eDhbf318qlD17BNeH4fO/+rr4+ezwb2FYN1c"
    "+vr6FXdDVzR1VB4aDpnPE6YQ/0g1ePwMPNfm0Wbw7OoJScByGf3Gr5voQC96A0K6xW9LjvcEJHfMfGX6BidCOAx85trEL1cRCsDA"
    "F56jfa3PQODKVw04rLQeIlJcKnRH4XCP946f3lIwwebnwlVN5kImw0keoUYwZvnyhg4q7ctwPL8UU5zHzzDnK8gh1LIgNaTN1vbK"
    "ILppx+ry1gQJxe+0T+O39CaI7O1HYDAtFwH0DawA/mPOa3w6C+buAv2CbxrY13cZplGpKKa5knQXnSyyS9dFlzot4F+MHKX/QH0e"
    "PxKq1JOYx7PK5ylTFcHIch8hfOgF1Bys5WcxA4U/QvysCboy7JyDs2g6bklCCqcDNNoY4hsgTXhmrKbxtdTNC9Xlb2Gkp+pVl6pl"
    "KCeUR0jWsoWLr1BFfYBYkMHsMe5PYDCEYMPk5hcTpwNpza4DUVg3dp8joVe7msF1+DvyChLdQKpY39MRtPFVgvDxKKyKgah1dP80"
    "mC6x7p1D6AEDcf+Kf0VY1WdBembMgvetgxHeAnuM/4Ko4Khm7+wH0a6/eO/rIpce4vPMFQup+ie1nuPdh2ASvt4LQJSeprvj+Yi0"
    "DOPNfPyBO2r9ab7YIxAe2PqSN/gNGqTzRWV9dNC0d8gaSMCg8mCZhwoHHMxZXhUCpzdFIChYWJW65FxtgNcy2M+W+oUOaPlO+pEX"
    "DijRNS1kvIUtXeK+HLj79+mehIBPLdL0GtIqknER3kJ5c+hXOtsKNRYI9IvcA3oeookgUxh7CphTRaOXI1RqxLsCei5AF/i4hFpl"
    "OimYZuOZ4gkYOUGdM+B8WeaDTbhQq4g6NaUmJaswK+GRaPxy+J5y6CMfHfwiEGp1EczI1xlWHweJWpw5n/bpMsRjFszCrw7GURX9"
    "w9fxnXC5nRqBo7Id4naT+2CazVYehKMYNcH+kc/9D9d7D46WL+WEn8Tk2546WD6X85HZ+LkCZG/0Z/jizTJMQLJkFwPeAkqLuVz7"
    "K3hmzit/Urv7MddxS+srAqlYtuLLyJ5vXJ1Oz5dngPU5LvBZEI+n+ZtTrCc6J3xKgLYUrfJpDvQWHZqVtLJcwM5qjhUWRwiru9et"
    "ttBF84gR0pt1w1D/ivy9KtAWMVF1hsonXOy9rvPa81KBuMolUPWF8hyljgqjkOgps9im4Ol0CRD1D35RqkUKRUa1B2Duv60Jxngv"
    "CU+XBmcWeqYx/cIc8bMOfkUhjJff4gFI01DbQ92DpDnsnFaoCE9tL/7C8HRF1ie6qe2rVQZvsIvhnvVF1I8Q0GwffU5AdzmgIpOa"
    "7sV6wEGPYrrzVgN60A9WennVa/YDt1fUmoM4vNwpkEz5/k1YSY6ctPIdGnP2o6VgC1mpNFk2QLovIo7mu5Vn6QBKXDdEFTzy7mGZ"
    "/tdhqXq/7CvqfJ4Q4sGzET6lOlKl9OAuyJG7xzyPCy/IBOXq7rGv0UczppvkxtluTQQbE8uR70suR5wZjRuwIFcg35OyAqDAw7xj"
    "9FJQOajEuQrhuv2E3xoUVOLD7bcg4+k7L8ZAoMMVqb5vj2geqpUkrJF5uW9pw1acV/vBGIg0plDHit79J2bjr70/USsnxR0raX3Z"
    "AbMQDsrtSUlnHeBP3gPZCtTFSuBJ2V0bkYX0rscK1vCsSRobGIdV5SfATUT6W5qnjn5KWKQPVmEp07zCKONXscqv9Ong6FeyfA7x"
    "32N80Ieficbwxzpeh2muhZe0mEGCPls4HZW1mUGaA+zLAYggUK6WQFYpnaYNgr2xOOqp6n7UrHvCw5eDudL7CHuP9s6ZRl/B4Tcu"
    "U6aj8gsMYnRYLzMXULykYiSDVjpUYbu+NrXdVlzKA8sqF0EdvxNMgYaW9bGW2fKwwAp5FW1DEx5KohTEY0OzfO2Voro/SqLgkJw+"
    "bwoMzW8RGNM5frIy8DBpuLEGLUA0P19K99HZEnzqoXEkOSxyppcVAy1HrSslakoea1mQF42vMMWGAW2t4Mi5f7nQix42+88WMKy8"
    "+wrWGjvSO5/hXabZ4IgblGBxLDCVuZZG+5+HXoHCWa7qmayqhAKB/MmaLpSIB7OKO/+DNJIH0fLEvhAsBDZU31esz1zcEHFweLcf"
    "GITnikAiQWmDRVXMYvg4brX42MJehOHfhh/6pk5AZKQL9is6IZf1VMCUWlrea3dgVBB/FuomkKsvsnShj3InjWUaCoySln3/fkUm"
    "/84fKN/5VxxVBYiv7grpih/IF3vc/8Ddvh8LDPqgbxwRqp62wqgVGJLtsD0HFHh9XXI4riE28wfB7KwpBwerqjEnf1ZHo4gvQKW4"
    "kEfz42Ot/7jls08FhwUa4eIwvxoiE0+IuZWTgrCqRSarw3DIflehro7slPEA3iKALHa3Ch0/BcETMjo1l6cpd4v77K5CHko24PkM"
    "kn9i2OlphknZb10cHUQeO7UXwDG1Kw+ePIeRAK471i+sptI4W05azbMZ+zubaXr15iyJ6jWb02KbM2Pu6zanUqu0OSvEQ8PNadfT"
    "U8GyZIRVyFy7OXMQ325zYlf5zZn5ZN68O7F19e6cVOxOKjidaavxTLjnPJmRDXUxqwpqvy5UGrO8MpdO/NHhfLHcz0VRk4HT5Cek"
    "lMd20+9mUSHv9mND/OYR1D6o56Z1Z6a3jZ8mxlwTHi1YFvpi38+zvvzHP//004vnPlal71Cbo2FczDYeXd7y2FL3sxNQVBqyYyUW"
    "nK14ViV1HDWEm/iiRxdCH2VaKTtIKp3KrKv8ffhhXPyItbyMyKUjKGtjSI5gSf1HSTK/pB3gy++FMgs6wc91b5IweLufVUdplq+N"
    "OeXK385noayHiXKVJ/FY1oDf5Qovgwl9jZO1REZ11Z8XuYo/L6qGTMPE79NvINNFMFZzXmEEZQUkKGFdsG8xKmrqvnPiVwxkbrC+"
    "xW8sYIkPlVWjRQ/HVBFv1pRQVXOkqOJ8HRSo/9wYCrkcNUBwKNeN/zU+7MZ++QlE5Xg13bPh1/V+GNy4c4WIKs57SeN5Gv8ShZet"
    "8mjr+iR6a9pjhp16HDDyK/dYuesVwrvNi9N89jDsM7v9yTTEvFcRaGfxRNruw5d0HMVPngR/9zFSgVIwElKafbhjAglVrWFpywAF"
    "1p9w+VofxS6bKyfvjzxXYTF/6vmKzdl8voJg6uz1HBYzIYMiiZ/WUqRXcrfAZ0fyE1UVNgIn8nUDSLDrBwAdpqL/EsnWykQlvmcr"
    "ixUqu8i2eMEX5vORvJGS33GaiMzKMsoEsx8qj2dC2TqdY3V58JuKy2xXdPka1W3QFkDey+MJdgDFVrsCib8sVbQth+I4Sc/NMhqX"
    "m/r3rvIt70Xj1Qlg+4QXsGMp1IlAe0V3nTCD5Rb9UBjkcmek71RMhM0jWJJCxMAPLOuDklTOH0TGyyAJZnTHijeso7MAPagJNW94"
    "lbdkpArJYrsKJVaqmBKOqm/IvFU0zowaNiIt2TBHhrLGnpVZpsLeY3obKtJKe1424ugXZcqK6HfVTX5XdFngJnfzc5PlUqNXhhQK"
    "JpfalFD0P57Nkyt8IMuWoQI7I+blVRKwMgzqwOuO8Cpa4J6oOX7LDsTeND4QCw2u7Q+rbHmdW8EMRn4ewY3eJy31sEzjx71QiWMw"
    "I5hAIWKhb6OpSr9WYNdx+5uMSgRIyw7HGhzLVfQJpj/tMbBqhdnyqPytqyYMMBhtJ31nhUbmkU/j+0L+wA8+hH8s7dLVB2mGvmFm"
    "6HvV5ntJ4evrLL9iaaP7MgveqOrGDC9rcq2Ejb2VhabQ2KvZzcIxV532bBei+b3E9yuG74NKs58w0ThMOq/NrXxKScaQHQ+IXchs"
    "+8vSOq9d5tta+ZtN+K+e/tLEftfPwgDQRzoQ/81ccygZB7RwSgZz/6JkPCJEKtn8fFLpiucoffEcpZUUPBxQQfcHs2YEfOuLUX+N"
    "hlGjGYjTQUDImw+3Ulg26BjbqBU3Ef0SQnmmKYU932rKESnNVpHrGQqqJLtoXy++byOQVTn606zSmdS+PIQVs+Tnx8+5wFzpR80E"
    "6y1EKQjO/KjAIY7utFrzgQRLeoWYg/Hw5wd0zS9Usu1k7kcXqEx6/jrXW8sKcJcE7vCOKVGQP/7tuBr/t1+PXBNUpUspKX5ikuKJ"
    "5NivFlEch8maoIFfqQ/t/mBP6x6xP2/Znxe5h3Yv/hse2r1t/tDu2T/sod2zuod2jz7bQ7s/Nj20e5av/+zzPLR7Pvu7BA2EPVcd"
    "NBBDynUxqKh70DY8DBeHUd16PQpiZ/cw/qxjdC2vg0HzbBODwDmG5Tn2gQ3ZFAbVNjouxg40PJeC0cGPrkNhXM1Ol8Ka9mzPPTCN"
    "dqfdprilPc8x2zsYpK7t2u6OZ3i9to2RY03XcjyMY9dt97zewR7keHaHBWnt2G7bwTpdx7LbO23D7XbMLr697rUtG4PsuZbbhWF6"
    "VteyMJ6t03YwrCoGr2vbOzaUUwxBF3rCqLOdrtnFWIKOY9s9DN7nmLaLwf6cLvzAji0HUIAjee0ugduxu+0DAMW0rO4OQQc/ADoA"
    "uGPCDDCrbZttp42T6lgUFNBuWxaFv+11HJx1GybdpSB9vS4FCQTobR5mto14w9iL7QNI96w2wGtabo9iI/a6HRbN1rF6Stqxul3v"
    "IEu7XRuj5IrmHVgGW/YOq+Zg3W7btjDhtU0WdxFAtQ3P9roESQdwiOm213GxetvtIOo8z6MFdgFDOxgs0PEIEqfnOCKN1R1YWbXc"
    "dk1XaW51em21d7PnddXRTcftZMCZGHSwxyDvIWkSrVk20JYHebaLgRrtDlAOBUC0bUxbHa/bgaXC5aBAjt2O1SaaNj1Mu0CrLgsU"
    "2cW+bdtqI023gQRw5j0gKiSSrt3xMECiZVNgRsPpOC4RnwULfkARIE2KoWx60A9OxYE19QyML4m0BxTTbVOo557dOcDFs00K6Nhu"
    "U6BKy6S9g5EpLaQ9u9dlgTYtz3QOkPR6LgVm7MKGgHEQZ20WiNGDYayua9EW7FrtLmAHqneoues6FBey08Vp0Dwo3mbbwriWkA97"
    "/QDqOR3PwsjBUJ/iO3pIW54Bk/B42ga0HohfAIDbtllQ6p6LwaE7vU7PZpEgHY8iWAJpHSCTsByMWAnTY0wDVgi3MSCuQ5Ej4Ycr"
    "0li/3bVstbxr0baX7T27Z6n99xwgJjm+m4HmIrzEVYDhWGxoFj66w6I591xGlT231z2g7HaHV6N92yZcuDsZb2wY1vKJVIueM7Xo"
    "ZdmAfhOMJ2WvGZRb5TeD+bnaO52G72udXqCTDOrAYAUGK1DdZICqNCGtCBT3nVGIH2qywj9A3YlOP4i3P+UKi2BM/i+VkXhWzhVH"
    "wW8Hr5hEsyD5UOO+Y4SIrKpOBWrNUwBuD+9Yq7Ux08DMUs1LJkmLdVm2WnsWxXtMAit1IZNdEFZrnpW6PMv1lrkNodK98TxVVrQ0"
    "BhSXQK8EpqpiGZaqWgU6aau+UeSamtXQj6JklHNYUmywboBiZ8sQaGsM66r0V00usmZTgska5EimBMH5aBQul5vHZ/Uaj86rrx07"
    "ik/nGwfGSk1Hpbprh7wMQM/cNCRWajok1V075Bg/diUbB2XVmg7La68dmL5fBMt049CiYtPBZf31lDVTBq7kUstZNaOq3O1QuSH3"
    "gZrrGdB0sgmy6WQLyKByQ8ig5nrI3k83QfZ+ugVkULkhZFCzCFmTW2x0qKyrIQqVW2xMdi/25IVvdtqtstG7/Z9lgKT795m1LzO4"
    "pQmWuKXfVYTH3f7TpdLqTswPZEREuKzycobX5hBV5FBkFkzxGC8jA7V0indqlNL3U7X0fbEYWQ1VCC/wvPcDVsI8pQrngcVaPFup"
    "iDykWAvzlCpsvxcrsVx1SMH0S4OKAqWy2MbFuiLf518dvpZnWPhx4THT0272ZYFdghCD8cq8bqEO0n19uTi0f7nh0J6gXXtin52/"
    "PW3m6+vpP8nX19P8+c9h2QPSj5/RA9KPigekPys9ID3d4AHpz+y48emn9ID09K/3gPRY2Za5Lfn1rPQVKvvktObrPyw+/HfFOHM/"
    "+7ojTskFe84+QakcGg+bPyitBrwV81qR59DcZ43gA/mUuPoDDCD7pdEz+V/UNzzZxv12/XGieBpwsxc31Qf+K738MeLP1lcyfKNu"
    "4WcIujj+y0xbPZYG8LfMAP55NshsXOatoamRC6b2EvUx7qcxKzhfgsnBLrSoXhtvb+YKlz79HXadvspdpfBWVa020gzrbdiSWpqv"
    "v87DZX/HWrzfWc7xk0dVU2b4l0bMW+68DcszPvwfrSr7fY3VbSXhrFBwGsyiKa0fbcNiaRgAvaCwTlPoeFlRjzxbMszmPF5mmFAh"
    "zGobY2C2+OP/aHquISFgyzbciL1J0/l5SpR7s2Hf7y3PgjGw0U0N15/8sIa1Rz85GPsM5UxFyOpMgkWuM0hXqO7MCYu4V6BsZLFV"
    "Od+obriHz1j2ElS+laaCuDe2gXGTVpJOtXLjvZrW/XietrK+LvjjZq3Qf6FaNqS2Zsy1AL+Zw+9ZuZG9rtE8nn6oOS9ii4K1DKxV"
    "NnT43t3jjBQ0vyTNHdQUKqCTYbWY1t/cBF2WRVszRwLrjppyZtjauazBTJZHNxuUoS/woXc0Jc+5RcbNsbhxav1+cJrmTi+klLj7"
    "n/ePzLv7H2O4tUcFDDF1ZwVVjBzq1vBypeR9LW4BmjwmbgRcRbfbEja0aEoPlZ2vo8sK2ttiuLUnKKy3uiOUqgWDujULppS8XwfN"
    "lgtWBVxFt9suGLRojsHbL9gWwwker2IGtErhrxw1OJCD57O4DtwCbyl/S+AgYb2qTwqlHk+n59G4jM3MUXl1i48kHCpFohThWv8M"
    "dd51B6d5NZOq30ZP5R3UaKv1qjRrV3cOWzm1kt/2DXNj9W8zOdHD1rPjDddP7xSvyu9dMK8mOckr9MjKvqmZQdeLWK0K3TDXUGnA"
    "SammlE6mCjZEedASGoQ+ytyi1A3NSuuQUfXJtHgyzNVidlS+7vPZuooEaaPapW2cBNGyoCJVLhSrV1iccm+bNC61R1a32iQoi9Qm"
    "3+a45NzwcW7tLlEaN94gmz/uFeZwQ/6WjXNjDlfq4gaTbMDl6qfalN9lw92c45X7uMFsm3A9Zbp1/K9g31YOtY4f1WzLysYbNmmD"
    "j8y887VfmdejXjRtjvEN36hzsN90A/Exbr598h1sPblGW6d6io03Dh/qFtum0MPWs2y2Zfg0b7Bh+DA32S7lphs2y6ZbEVyvrb8W"
    "sRbVrF1jBK+9UZHBe8PdQb3feGuorbebUJNNUTWtpjuCBrn5dsg1325mjTYCTW37XUAD3GALFNttoP9NV3RYp2vu6KzFLWvXGKlr"
    "r/dk8N6Q/qn3G9O/2nq7CTWh/6ppNaV/GuTm9J9rvt3MGtE/TW17+qcBbkD/xXYb6B8vHmxGMda6CW5Zu8ZIperrsYlVbkj/1PuN"
    "6V9tvd2EmtB/1bSa0j8NcnP6zzXfbmaN6J+mtj390wA3oP9iuw30v/m+JOt27YXJtfgVLRujdsNtSxXuG+4EPsKN90K+/bYTa7If"
    "qqfXdEfwgW6+JwodbDvDRvuCT3H7ncEHucHeKLfcsDuaXOplXW+41bsW21nbxojeeCk4D/8N94kc5cY7pdjD9hNsslvqptl0v8jB"
    "br5jSl1sP9NGu0ZOdft9Iwe6wc6parth73BAxjXor7wBol6CyY0vOtt41ahB0/UIFtVvuGVKo23eOn/L6TbdOqXhGmyhv8WEN3x6"
    "2AjoTT4kVDS+MbC3pc9tPjb8N+Fha8Ld6kvE3xET5eP+zaBufXxfanpDMG9Nto2P+P875r89uTY///+bYaB41L4Rxi1Pz/PtbgLd"
    "bYmz4Qn733rOWxNk0+P3v82si0feG6Hb8hQ73+4m0N2WDhuedP+t57w1HTY9Bv/bzLp49LwRui1Pk/PtbgLdbemw4Ynz33rOW9Nh"
    "0+Pov82sy0fAG+Hb+ky32PJmMN6WHhuf+/4XzH1rumx+KPy3mn3VEexGKG9wolpue1NIb0ulW5y6/tfgYGtq3eZI9m+HhcU0iLZT"
    "ManFjQ69qOGNALz1CScNfcvzzb/BvLc/6qSxb3vQ+Slnjg5wb37uXlmlDBEO0vDQlRzy3ozccqM0J7bPM4empJMbZgvC+TSzaH7r"
    "/iMTS9NDzhogb0NBNznu/gunthVh3egE+zNMbu099I9NWo0OJSsBvBVZbX0c/RdNajuC2v6M+VNPa8097Y9MSQ3OFMug3YaGtjw1"
    "/uxz2Yp0tj0N/qSzWXO5+SMTTYMDwDJotyGaLY94P/tctiKabY9uP+ls1twI/shE0+C0rgzabYhmy/PYzz6XrYhm23PWTzqbtddo"
    "PzLZNDpIqwLvNqSz9dHpXzKjrQho+wPRTzynDbdNPzIZNTzdqgbxNqR0g/PNv2xeWxHUTc4sP/nMSmeRn/AsqOHJ1Mc5h1SG/ETH"
    "Qh9nOtudEW17tPixJzSN4refnFpwkAZwbEMYHxm4JrfO60Gs9+SD67A3Dkdz5lSvv4M+MhI82N1ikLUU9ZERUX0p3c/cgf7azI/v"
    "r/8kP76/5v34flP24/v9Z/Tj+73ix/ddpR/fXzf48X2X+fH99VP68f31r/fj+11FLBQeI5n5uP551sATu/C/Ts7YySO36omdOQfK"
    "uWIHEqn7j7y0F5xsoZPws2CJ4evI5TqxEfpFLn/0uyVXY3f7LeZ+6+Wc4kCncwq4pmYxf5C+dv8+71DpZjoP0O3b3T4UsZ9qITAC"
    "KoG/2OcFBnGMCdmY5a90Oeu9e1ex9C288vVYcTTsF5wSYSn7lStjboOokP1US5F/YhH+LYBCRWpd8cUM64vfhTayitpuOSO4c37s"
    "1fLpRC1nrurVchKzWIV+qCXkU83XaW2/xt/a8Urn+Ma17vvFBSGS8HVyEFobEqBEe7wVEpe6NkRe965SQRQrBIUogeDAHyoEmKZI"
    "w7/lXdLz7VL2Sc96WONmnqaxoRzgqq7iT8PT1GeVWMjZ9eFyWZe0X9aNSRW27O/VWpf6ivt/ubprovWq61/ZX/MAwTz4e5MYwaRX"
    "1Bc3CRrA9u6aTvj+XVODBWqtLZaPk9YAuj5ygc43+7oqTGuvH4J2bU15LjzCd5vCIzAXes3iI7xuple9/ifpVa/zetXvZb3qh8+o"
    "V/2g6FX3KvWq1xv0qnuZXvX6U+pVr/8GepUUEQXx8NusLko3bomv2d4qbCcW2RbY3SRMX/70YoHIXFaQY4skMAUPGMpA133xC2DT"
    "s2jQMhA5FYsUiDcYTwnYIGqVYzawyAoUJ1k2v76uykWgfF7EuftKcIxHIv513QgkRIfZz10WAoLkztDf8XezZN/3tb4KgAyuvdK5"
    "9lg3CgpRATwLFoE5m+OKL5Wo4oUg4+payYgOKIpqgovv8B4RW1xwDRmTlRp5zZplEnFN6HIl/jgPHl5cgVLwcTGsCD0uBrybH1+W"
    "CyHJy6XaS9hnlF2e9VMebJ6kija8c0fEU2cNsjIgmfroIcAa1/x3taqM6qH70sDgceAzGyMjOJEgEoM2nIJ5C56CfKHM8n6YPqv7"
    "Un+ngkyFFzo/yxZqf6ajU36mpvPQJpWaOjMCqAazA4qVhSlA1gmHm2yXYkWqABWFFeXrLbk9coZUMTezpTLEIbXjkiFG1y6bWB7e"
    "Xy5RF4+FeiaybdT1R1h5wRjJggVerIRU7z+Z6SzW0+MZQMa8Wl+QxRwtFiBRz2fQODxT4sfAqJXRZOKzfDQZlCXzwQ8gqtQQ7pq+"
    "pDwWe0fTR4MUo8bQYJk4xkD3pPcO6+PGW8y67z9pqaFpNIWVBBljA7XgcdxqYWibp60wauEAGga3oQj0eqMQN9AddqXpUsg9apWj"
    "2TSPexOKLZibJM9jdl8BwCMGoWJnAKAsj+qj8UeBeAp1tHWjY5Vhqxj0Z6th9VxntUBQdFuro2l9vhBzMZLVeIL6EogJxOWGMfQj"
    "n3r0jzUMKNRXMZxDbWHkIhqjNfiLmiJOIgl/8D9kpx4XqYwYTmlwMafwDFD3uOX7+h0TZ4VoJx2jEgg7R9XsDEDL0MbS+lUBAsaY"
    "oG+MycSYoW51Yc8rQ+shV2L4Mi7ZhnR0pq3zUmV7Zpa5ltmjPFtY4Pp5TLbXGArET32R9jm8PCQdzoDQ4cEK03C+zlcalHreFfwU"
    "PcDPRYpEoOINUXfSd1YqneiSo2HwqqPR8bG2+k4En4rPSLFPkPEtkxHwwOhs8FPSujo5Yary4Xwy92Fq6flC1WlBqR98+bb14lSD"
    "/TGZy3WKZhPOxEwd+utnVfQArX9fZ47Hfdvzde4tnH4zlMI672FlX+IiUZcHD3qCswEf/moapmiSGCcnF6MRaHXL6+tw/xRMCCg4"
    "CvXkGCy2VAOCPh4kgv+C/jg/GwRnregMkOGfnCxHYJU9HQs0XewFpyPH69iBD4jSl2fCZvgpmoUkjjKz4WCh2MKjM8UEPcXE9fWY"
    "/Tlnf6ZnLcVwxNRVyfZ5GsPSg+II/BjDp+2k853lIgmDMYbv2iPjGF3piLNd43+exixkDtZ8AwW8hk71gyQJPuwwi2vJLKmzAGyn"
    "YOeoYG4ft7QdZtGgSSWBPD+TxmFI/wo7OLO1hCG3YFW5nXi1AguRWWHcDNSM5TQahS0Po4DL1UA9hRnJRdP8/v0Wrq2SY+BCAM/A"
    "Ns8COjrGn69CsKwe4UyN02SOJmyf8h8lE7CsQS2Aig/+tzXs/xxdP9XiFH5511bn2rE1+Al7d7YANY/1cO8BaGvLtBVrQz4focdn"
    "OKFFVXDBMPnQP8cZlPDKQuUBYR6BXStyfZ4tcJeDPhvpVIzEyqMl/YU8FedKfQ7yFdrCbNT0y5BH5AMtsIWHsTxF24QtlaknA9Yx"
    "rF78MN2Pd3e15Cg+BmM/PhYrlWTDzM7WBte7mBCj5vvccrN9jr8vovDy8fx93zd3TIwcj3ksYDzGp/P197MpmNH+WZou+g8eXF5e"
    "GpeOMU8mD2zTNB9g54zRRy3gZrDn0iPz+Pp6cHQIjDRIz4D5jPv+M88wLcvr7HQN0+w5zqFlG3Z3xza6bcvqHEDKcS1Idrw2Bq2H"
    "ZM/DpNm2XUy6TrcN6bbV6VhY2+12epB27S7Uw3TPsyHtOLbDkj0stp223cPq0GkH0pbjwaBY7jnYvelaPUq6XRjF6LWtnku9WxYA"
    "YXgdq0fVnTb8MbqeyYCxPQ+rdwFyB6vbFgJhdFzHtLEchoFk2/N6BIzpethbu223ARgchqWtjt3esWgY7B6m4GKy23Ex2TYBYVi9"
    "0+mytAVThHS7a2PSdswOJmEqCEwbOmtjdafnEjCmbVJ3jtXGZNtDGC3Ddj0s7tq9XvewY/R6Zqe70zZ6nme5h7AcDsLEig8Ab712"
    "22G9wSiIGFgIHM2xPUSobXctmqvTgVWEqTqIeEz33A7DIALXsWAdWLe4ukYXlq97ANV6nQ5273kmTgYmZdKytL1OmzBEi267bc/F"
    "2paLa+w6jukQfp0O0YhFq4jL4ViCog5hSh3EhKQ3Xo4o6HTb2F2X4Y91Rpj1Oh3xu9v1rAP+G3qifGwAqwuTl8MxasC5eG6ny4jJ"
    "RkyZjunS6tMMbEZn7QNEoeN4oqDd6zKSYY0Y9lmXcnE87KttH8rFE0PC2npsDGyN8Hd4xwh/u+eyIYnizB4vQep0O7IR7ULZI2Sa"
    "bSebJG4Uy8lQkKUZerI0Q51oz7HKOmcIPywwgN8FkxmdJ3ikfYBXBYSSAfIIJD1o76vlmdCLZkwvOjsrfYkFLWAZYHBVdp4uY3by"
    "/KqgnZMkGisR5CC1h9J9GqThHsj/ZX/HOk3WRi7knW8OXaiEdSm0KUXCE03YPJi3wOIFD96HCAS6d5kEi0XufgvGkhFRX8wNzatw"
    "k49kujYqaS5OmJgd71rEBFMnKEM1FutWxmwUsBajhWFMrOVZgp+i1kxwOl+Ga8K2bjHLjbFXqyCilQiSSRQXAhsG5+n8tmFbK2iK"
    "5msIb9brgslXtsgHlt9A87mWtRtg4/WihgFUxahbRVDdolE5DuoWjQuBULcZdhGMwH7cMQ1nuV3AU15WCkgrd6NZ9j6aDzW8bXji"
    "uu21Po5fnlwoyFsxRFUtIVfWrqfiUvX1DGGjG9RNG6wcZ6yWizfpg0cjWx9nbFMndVHHJBtdH7NEdL8maEmFk9h8q83P0nP1N7qR"
    "zdWucxybm99NF7wWxBpkbwd67brfZkqbLjzXQ1B38bkaACVZ4Zy3DnGKO4yaGHobW1aR00YQlxGocWEDAFnFTb1vjoolOl0fFmvN"
    "pLfwqVhs0pgKRYNNBCem+xG3kYT1tjtpU0e3nVvT/VQJR/MtJZpvu6tEuxttrFLjZnurDGuT7SWJrdEO2xBKSHS6JpbQmnk39cyX"
    "q9+YIqn2JrKj+X3E/cRAvO1mWtvLrabUdBuVIWi+h6jtthuIGt1o9+RbNts6BRCb7BtGTo02TYjfJhogmeptv214s+b7hjVoTH2s"
    "+iYyY5P8iFuHQ3nbvbO+m9vNqunuqYCh+fZhjbfdP6zVjTZQoWmzHVSEsskW4oTVTLVrEDtYirQNwYPXid5t/LuXGzVXj2STjYqQ"
    "nPjHVPMyiG+t6G3s6vYzbKzsVcOyhbonO9ha4ZMtb6bylZs3VPoqIG6k9mUE2Gj/NYiSpB4TrwmTtAYL2zhyLLVpTLGyxSbClHP+"
    "iDsvA/e2G29jT7eeXtNtVw1J810n22+76WTDG+25cutmW64C3CY7LiO7Rhuu4N6x5rSW3nxjWen4lRpcVpzBZk0uc58RNn/KqQah"
    "6VFx40PiBsfDy9n6z2NrP3UtZ8WvXZsG2GItoPPScmzqfhs8z5qjerYFtmfbIfyG3xNm235SmG39VWHTRKaTW1DOdLKZcvIDbEE5"
    "0HkDysl3vwXlQPdNKaeiai3lFOpuRPjNKKcZ8OsbbKCcjRO5Say7NV+oikIn92WqYgMWJUzjsdd9nFR1i3UfEPno2+8cKesqbxms"
    "QfJanURvAF9TRaaElwrbFj+77pU8cgRxNOMePhZ7LBHm29Dn4p0wWNLEgM6TyyAZLzddKKjYRGFwEW4JAbUBCKw2ByGKt4Xg/74N"
    "P5wmAfRYO0NlFyfzmZJUvprnvnHXXeEx1Ss8q+zawbyuT2tzn1a5zyYzY5hrNrObQbF+ZgVssYspN0Xi6n/8Bs4uij4GxG0sxcHF"
    "TkaO/m4qX8Lp6NuiuH3Rt0XVwy79bnHPFmqyzHy9GdbJu2pQy6cTtZy5algd47sm4jm/sitXfb/2NpYvqlbU4W4Z/LzI9dmjdj8v"
    "5xHPc+E7IdeXwot4paejqirUN17Sn5yp3hieiStzZXcM69/w+/jt1F/RkPQKep2vgFNRzF79NnbrIB5qZvPaXI3h6CWbA9Wmm4T5"
    "IW//7F882j87W/9onyO44av9k7NGr/ZPzv5Br/ZP8jflL85Kr/Y/nH2+V/sfzjLe9eas6tX+ydn6V/tvsocZNLVP9WofOv+rX+2/"
    "l7ykxEcmZ6V3+yEMtOzj2yfYpj4+rz1FUT/G153RLAROzrdqkAYVm4mfheHCrfQZaFhp/p09AhQOcEvt8ye7p0C4yzD9iXWuPpsM"
    "Dd7bAOEy7iForQwgbaXLLjTFnwBBntsh7EVw1hd7jc264/MM8y4CKHfjM/57uC7hxTltLiBgYzqHxQ/pif5wYw1mfEi+uOYhOOw2"
    "+O9KekqpfTetM/FZqsClqng3LCR3LlX3KLnu7W/u3bB83NVfnqms8lUzVvnqn8QqX+VZ5QHnNIyTcNYI2ucSaiGH4DmTMH1xGQtm"
    "ycZZCqayrg52k96/30oGiXEaTQE72R5K5ZQre/gqXI5gQWGaBKKRMeUVvi01FufLMwNUpOmHVqwngufsxNnkLml9xVuodGDtpw8D"
    "8W6Mv5XaT3d3xfRlGbJ0emM1vFr11dz99N/2EHDGAG7FGr5bNGCEJ8HoLDezn7gMgkYaSIkNM1xWSqUoBPzpm5oCFFpfhakaoHqx"
    "twn7MWAf5iAQrEi6n8qC9slnFLRPFEH7VaWgfbVB0H6VCdpXn1LQvvrrBe2LnC+Et7nUo1zqD0xlvkuUJ8b6s2oXCs9rXShk72rR"
    "gUKVywT2FPsJPalnioC0O3wdLaAgyZ7NQ/vsOjw+MV/r0iASYlU+YB5HF/5a7wnJHF/9gBBMwGDiDlwA4XchD2zUBJEv8oHNz6IR"
    "lAAzDv0Kvwv8Bbjw74CPGMX46sh5S1B56l4sgC6EMwA6sgpgWyU5HwwyV77SJil+AKSIh0p9LtVX3JFBASGWXgFWpUeJPIAEWdlR"
    "wVXezQV3ClDlUEJ1b0HOCZhDAFLltAxdVV4Jjuuhi2o8K6gv5pkzAo5TTkoNiIV7d6kdmpUXsCKcamjHCM2jgmMCYQQPhbsPAEDY"
    "5NXrk1mqCIrqa4gvc+ZmKO/TCJ04REAN/HFthQrCO0DWUTFJEKvw39WKQ62ay5okDRW6IiaokBNJtYMRaa1nrgfqnFTIqr5AI6XW"
    "EIbSIqOOZ2eb3Xt8pKFqCJHI4o8zcuOwPD5WPD9gwVsowB8s9aLoUYO7hdBW7+Ujx+fskePLs0EcXu68ClP96zOwLzKu/RR9FIBw"
    "unMZxeP5pTFPRoHGBBIXRi8g5xW+60923iTReAICKVoucxJWaZuJ1UPs+euz6+sWDmnqOJIxj7mF1woHX15lWi56G5gLJwEvz6Ty"
    "kkKtNPlwlSIZjoJ0dHaFvtI0Js5+PBtANy2oH4zHUENvaYMvITUOp2GKlKvpf1IVGnsxX6ZydE1/XF3y4tSYzcd0UAd6hz+8Mgwj"
    "pDft6FEzTWHiS3/Vhw5+E14qUCkB4a+i9RfSStB7RTpgorgVXl/7vmZAYgZDJuFiGozC1oP//dcDHfNnODlIHpl7vWDv9Piqs3oQ"
    "SQynQ/9f/i5uVpSDOPdvCXzRtzEDrhKd0IeUk7Pwfbhkoy0XUzQhdRpg0frlTBMaOD9h0zKYf1Zg/hZ/y8G5mvzQvn8fJ2bIYbTr"
    "a8ZA/H95nqfoVL+W+kJvCrIfofv8LIryE+Dm3JycPEzn8SRKz8dRHEyF0oQes0An2JvgK0GQPi3LaY/Dib6DbmX/mEcxTHkHpKjm"
    "7zMPIk7HfCCG59NCyRWNsi7wxBhxxBfVv3cVrrC/L+IVdA2/WumupbEUoDMbZdfXlJl/U1CHdxQKj0kbAw10CL3jhnwap1OD6Whf"
    "zxMgAdCzr2bB+2h2Pvs6CajHr6IJnneA9ou7Aus8C9Iz5tIMSXy1M/H7lBW8QVPry4EVOusHiOKKAWy9emA7Gzh8AF3DgG9hRBgg"
    "BweB4Q8ZcX5PxIkPY0BJC6Yn7BqHVJDRgi0VkalVzAc5B/QaoOk15JdBMoJ9pxDZ9/ib/GAn4QzUH9gVvIv9/Dqk2ToA9/nSlCwo"
    "VhaIZgboaJk6+wlrbZk8wWYcP0i/gCyQa+wgV0L1ndSDEQf+4TzdQVLyGaTR4OiYETyIwZM4uX//t1aKjrMwgY7cIrJpW4msoZGc"
    "mc8QB7w2TynVJR/gRQqD+c9y98FE93ck78H+QDdJgoz7srTKg2kcyj05jcLpeAnCi/vd2Ul3oE3umIC110iSxLCEo+n5GOxWMAJR"
    "PYzi85D2IWCE1SQrGth6Mvju1YvnxiJIQNHgc4AJC06fcLK4fx9/+dlBS3JHAZWjAAgyXfUB18lK2kQ7Ed+nO//f/9tRvd78Ros0"
    "+CpIQyOeXwJSpKuhDagZ8hxjnEThmNaerL9Bzt0LZeMM44oZxtkMGVYe/G/rP+Mrd6Xt4V87+/sAxgpHSjsc6k6SG4VRFW52nA3g"
    "XA8GCp22aI4//3TQitC6/xqa/AasE3QcSj+D9TkTCepA0/Zkk93kyDrWkyP7eM/SIeGAlvLA67hhWwoHZasETCq/lu6bgDDGyYeT"
    "cfBhORyaGm22Yma2nX9XtnPBHY6RnEbjkzSYLLWhkgDugH/2cz52RKNUGzKGDruw7NNoGPZB+4Cez6Px9TWwnTHIMlrBooDsHx3T"
    "tH4As/fIfwOb6i3I039Z9D8wh498ECHotutfXoD/p6zLsyjFs+l/nbr4f8pLyKPXv8K267ljypknGJ2JqrW9ts2afgin0/klyxz3"
    "zIAPEYYx5rmdoNv2KO8NcyD2LyfsOGPW4eI8oW+TAEvohqMOyyT3kzBwzxl7NmsK+h11543bgfOG8kgA+3pRLHJ49R0ODvxgMMAP"
    "NjL8YHU0/1g5D7gnXBuR/Oey90tLSHA23D5b7oJWQVSeippChh9ZuqO3j8Wa0pYC+QZqBXM7Ferhrk1ePh7Y7TaY8QNJm6DDxUDj"
    "A8nMWUYwaCW7EVTX54NkL9KXgzloHObQ7M8ftKw9KVTtL4I9i22+4KFh2dfX8AeUoeVDw2kLMBllUJ0vjR4VyjJGDlgGuZbMJsKh"
    "2Y0GeI4bgy41bMWw5/Zi2HPag/m/O31WYFGBjQUmFuza/Rb+3MMiTLtiF4wGrdEXHXMXVB7t3/CPPgKNoH3//uihC/8C4K495ATQ"
    "Hz202tfXUMFx20MAuztk1NInYoVi1xwKKoVUF1KcPLEpJhlhQgpQPmQkiYkeFHFi7LMuM94bTth5G1tV0pRhrX7BUzpa+Pj6upLF"
    "mcLxG+xjaz982N0Pdwe24BiSHOISOezJsqRUth/tDtIv0pXKzZbvkrQVKdIizUGcqSTX12C6JqjgEnURrBJGFJKJJPth0j+KMxI/"
    "lp2xrvdjKepa0UD49oofRhplxJlAI14UT6TtIbZD6wrYoT7uc1hXmmRkpImNef9gEsxhdrL1eC81xsJxm6lbtiY6DI2lwpyTiTwk"
    "BZPlP+Nd4Uctla7KpA4CvBSmILalpe1X4U3c5IjJ55seowEUJqD5wc8LMF7nyZCVhPRFCoHQhUqUKUTHRW4t5D1qO/PD+WWYHAQg"
    "eTVVKckWNpoIZV2oJzkQl5cRGmUw7RF04iM4fp+ftjJfddymU0diYmSfWog5Ka1E1oaWDAVKOxUnG9pKDVg0lzZISTlWdN5yYT/r"
    "8hydJpd6w9yqjpR8pY/TKFmmJ7meEN8ic0haB1OU1HxN6WIalHuQefkOZLbani4iybYxuh9m9DqMUf9hv1l9caas8CHFQ2AwyQ67"
    "Sfd6FiwYEQUDIqpYjzSQKvA7pd+COwcDsc/n/BdIG5E5tPoyd8/qBw/nQ+T+frAc+ZgBWV+qWVYfMs0Mqvkk06A4UJIfxciPeGk4"
    "iBWzKhqTAmsEyegsukCv13j6wSw1sO+5dVSijjtyxYtKfspwCTR5NcLv631TT+dpMAVQ9/FWVso84mMJvmSAv7sWr5EY9He3PFz2"
    "7SklFricoHnFJ1vNWkDXI2UtLW0eyFJ+qltS/xb3u7DufZgDCiZFNznmZdfFHag6ClXWwdSZ/0UMOEBHRHw9gtx6gPkaaPvlowJ0"
    "6bg7CLG9qem8PFizjdGn5u6gXAMHNwUKrxZhgj6n+mB+RmQF38Di1eUQ/WgYs6x5Ek3wnKafDMX9pswbquS1qna3owiwt1E8Rv+w"
    "wMp9HY9e/WXf38U9qVNmHz/6chorkneaQ+dygspEwmntCLS9hNPkcHh0rOPnWE4jVASoSPA7q8aUy9ZRiFU4dSUDrASSRhWcu3fu"
    "4AfVPfwTanJ3J/KEa1gzmwR0tmxCmFr1RVVGrVg11JnrsERHDtaXn81joUfjIWjmwrUgxYq4iXK4ifLqSzCg74ZSUg1DZT9kUrlP"
    "tbhUgjr5HSVEdj+SwhozpeAG9ZrwHwD+6VA94HGeAj5RsLH4cgU6nrjORT7+Nui3Hh2v8stGH0Bp1cTSxLA0zKM+H9nHKGPUnCMO"
    "1KAwlzHMl+/lS/vcj3RBmWB3ZA7mM7yI14qr6mjKAo258lSQnxkHBTb7cADMNvxykA59vx8+BKXUAD19fp6CAo0KNzG90wlaQYbX"
    "1o2ubrThj6sbNvwxPd1UbK/FhNteoVAl77BDQLCOv8YTtpDYMwxjin3ocVMs2/06HahVad27mjSNTidH4fFeqj1Uc2LMYd59Mz/A"
    "u5biX3ayxfEw0x6B85ROcIunwD2TDoHXnOT+WznH/feaU9wzBcBQnM3/Szmb/8+b6yzpQPLBJAKMssO9OwLQogkrDyRk16wekKwL"
    "m0oozOLY3s+U8d1QAOtr/aymfkQqyPHgyNRt3W1sHMt+Hw4M0zXB+gsfWLbRA6uyFe4aJlR5YNGfL76wDVeuomFbdueLeNfoWm37"
    "iwRqdm37i2iVLbOBl7U+sL4Ns6MN/XGQgEWpFoChCflTlEu++J4xmQyuAtjxrg5Ko4X3//rWSj/huWaWa6/0C9gG/o8/P3/+9Pk3"
    "IKRf/vjk5aMfn8CvV4dPD3jeo59fPfGP9Q/QAa+Jd+aW6J+c+Qn1VzpvWChYJOECCnlf1YXUPS9CNxuimH6v9K+fPn/66ltePn8r"
    "SucYpPDrR08Pn3zFy94EY1GIP9WLaW9Ktsk5bNxlzqpDwUGmFv5AExQ2eDwO37+A3aTtWtkHHF7RB1z69G3AgF+4KaKV38+KYT2G"
    "is1KFUH14vXwN67j+zTbKO8VRZg4TgK8Rgr3iDyrJqARvDoDFs0Ovs/CYLzMamASdBaL8wAFFKVOus906zVIoLmhzs3qnPBYIqKF"
    "3GjWUK2A3zHU9PV1JFAT5HC58vclOPgJuzXXEegME682SGGmoSCLEJKYCyz8DAo7GhWCO+K4m0ShNKipTNPxhJsE7gqPs2Ft8KB7"
    "H3BGM6Se5YfTBBSqBN1GfigUtPByDqAN/r5H4yTRAx1001jDL/QprhdA06IfepxfPpiseriRUsetsGr4FOSwwW5UFAamuc8H2ULj"
    "NYlhYaQCScqt0I8Z7mWGHhDh3L9/JyFjjqMs0rQCEiNCX6iib47oU3Q35UJkwY56FaZZcBcxH6I9To1qVn7W4jM3faEWC4o36RDb"
    "xPguyZChrwTsbDo6xQty4oSGKHsS+sP0S8sz+6lyJvMTdKV8wtC58E4CUMXwOw/XN/wFKtHCV3/L6Wi7VO90OoflBJ3e7nW0XLly"
    "uy479rkzmRylx6CpiEXL9tZyPgvze5HdfZFX5/gBLn5KZ010pvOmOmGrz07saQA6tpq26KxqlVe6T0DXoBGO9+AnI5FjsX7sOz11"
    "3o9XhNmvJgMndPUXk4EXOvrrwc9pC1AyCtHIxYvktK1Q9+R2C7NhlvNzMI645j7DmCQYpYUuQ6AYII8wB/Mxhj2jknD8CC3cRTIH"
    "wPECMsbSvOy/OAUt8fJkmc5Hb0/4YYJ++YwavpmjG3t0HdxHsKEqdyMsKi5X+gid+wKQYHmez+IlXkM5nSCsy7P55cuE/Kz+FLzB"
    "K5J4Oe1FjJXxV/8KDIn0HAXP6akPcFFVmibGmUIAV1Txe7RJfLAw8F3JVRizGGfQy4yADJZveWtSz1m95/M0GtHUYb6TJMRwpWwG"
    "4m6EIQrwZUuQlsspl8JdpvxNzSJE+K7OLfI/AGYRi0fKNHgCfDafxzA0rx/DL8oGsu+r9A/oeDuBH3RbA8bEvytlw2AhXSdh/Je0"
    "+FfpPMFnoGCePAXFv8XWHTRlvP3B7iYgQXM0+uxwxKdJSAEVyg+WbMMxwlLUyUfEUF5jn4OQvgvmxl5Wja1nN15yENy//ztMgwj8"
    "j8kALPRJJmrkXUzV1o61HNt+bRD+8iI0/IDnTpr2kp/fcit7d/ePiYwyydvRx9arCKxSnfZwyF6apWS4xnqQKkuy0nSGPu7CT6CP"
    "Hn0Bi342IR6d6PwGkfLKgq7y4Ndg2L/4yZpQAEYmHmtubHglgM04U4R8KUGrhPUKKPLP47cxfQj7puWzTQPNHsXLS7o8yW5B9FOY"
    "BH6x1b9COBQp8VKREhlS4/FT1BqYBKRB8fb7lwPz/n0J1IJU8lQH/X00BQtGgA6zYqcUGqxqdouJ1vprEhO5edEQbOlIxAjmK9Ck"
    "UP5TSRAwbzAxxXr0feJnPihwfJzDyeBbwmGLFG/ADCc8g+lXoAIqeailkVau5AlJzkoUoV5RhwrwWjCIgT5n80o1zH4BTOwK+TpQ"
    "GlsN1Bj7eLfiJ7pYgS8BfhRQgxb22kDuZgjGp782gHPqhxN2XoB3wkTlOVZmmxWyH4tscUbKdpVec5b62iAWNjTwXSseK8ltluzQ"
    "gWkEWm7IyTQk7STRhqSE4CInQFE7FKYcJSBp1/QLdsydlNfGMxQ6CH+Y8jYY6Y93yYuk/GOSNNSZg+4U32j+IteyDKyy/4/A9khC"
    "jMnnz6L39JV6SetynH01CQ22QTRxAqXp34reXxvnzFkaEyFI6CyDSQ9lE2IfuZ2Mn95lptiOsBY/Z30TqzUwRmBhHE3/Nasl5Prw"
    "tSElNPYZz0/Ok6k//AafZS1BfZ7/nEwNNj2t/9qQsh1USEEL4mRItMHgTF8HINzHsqHv9zOecRlEKNoOoS7C/g2YnFy68TuX4zCF"
    "5jLJ5GIu9eT9AncIz1vp38sPfK1v8ISF1MeUXXBkGZw7pJqyy99xMSOQgdcuYeVRvA5U8XonZJlDQ2bibdX522FLwcgApLyKTUoK"
    "jUfVOwXeBtxSIVsAcplWNZCfi3ha/VKkKl6yHtPAsrsawLNfi0xRSpeMucpF5SIxyPK1rMtMFZskwMdy5+U4qctBqY7Smh2hn3Al"
    "rQAY6XSDYiWEj/9U7hJlPcjbS9AD5g5qFEGddGaeu1JgQjXwBJVECgNKHz9Zb5SnlCMktCwnXJVktdjvQaEMtow9tPsgmIo3cAQ7"
    "1Vjz08lAySuAxfNPUN0pQJfXXgflBkhOTKHFJYEfJ/O3ABVQcsi2//37v6GSQr/BcuWEQCqnIARKDLJ8QgFuMwYC/hrwnGw4pldp"
    "/dwW4B4gr6+/adGtu3lscC5F5b6W2yG8NiBzjN+WkG+cnBLjwIiu+W2gHv5meQOxaxia+b5SdxMZRjzY9YRMGsDvW/wKg7o8KEP4"
    "ExRohS38xo04zj8HkIDev5sYvOX1NfzmTbVcCe75rAy/Yf0Juh97SZCEp4DbMxS/mU70Wh48k/KNt/bkpWm0F7EpZeKqYw1f4x/Z"
    "WRn/0s4V6D4xtP03gMi3uQ+4XJyVr4mBdNNwHPwh2PgVOZ5gefRCGK+NwZ8VYzvfTFhnOSseCKE07AnpatngjVsT1rGdYkINOAUP"
    "UaGDNH17VAnbRNKiDSSsjfv3fwACVTtmW5dJFxBIqDLiz9wpDF63o9w8TNTlSUhih5oqYqjQvqJh1qI4FttUFVCOzvAW0djvV1GQ"
    "Wp2p3SdQgg9l+kRLgXIbnJuFPtKzTA1QeuHCyxw6i2eq0Yr6QCtFAz2YwbPHuvR1FIbztzov3w+ny3Cnob2U70kxnjZNEc3ZE/Zl"
    "EKhCGLcDNKroa+f8bZ+DRaZVyONL45E1TgAbiA+jOfDpXkgO9XhLuE+TxvfoG2ojH/T73KK5xMlgDlgvxJf4kQETmOz3IOXck7Nq"
    "rY5Hs1FWytdg5LVXGestCgbM4cSf2b2viaewr5URypMMzwT6irHFH0B3AjUpK2Qkqy/CJJqP+/fQela44z1xKMDt3PWnAqwTvBfg"
    "O6bPDXRu9mOGcs3tBPrFRzD7zJz48az1epKnjWD8ASmDIfwoM2Wf4oTBWmnl55ERkw6aAk+doKaysSmwmLfYzgrdytq/T/R26NR2"
    "lFupkrIPC3Unt1DlddGdmoGltX6paJSsuti+VCXE8x3JbIgTiz40dtqXnuRfrB7r8cngKveWU0SgDfbYt/aVnkCVLDfB76x6lOXN"
    "z6O9GXBPyA1kZ0zrL7wMXcyndOO3PMT8BGPRqgF3X1EHj2D9lbC7jAiuQnbOyK1yrmuIb0zcau9L813HgxTuQ0fnNhU+U+KOczH8"
    "nbSQKriYOKylwVANETmKJZZs6OCO7ADZr8jJOtiX8YQjtGZECNGQs98M+37+/eLb1jeatLCScEIsdpU9oI1PdHwzinLy69Zz9q7u"
    "j1bMjHw95EM9bb1tvQdblS4dsJskwh1RKg6TV+oDYpyqHCM5ofFYZGoagZJgL4HyzzIw0nQej8Mc5JT3EvZq9B7MxlwRx5Eo1PA4"
    "6E+8urj7lRBXu5DCbAlEdAIjvm19f6qRCoOiMaVHOdj6WNN/hMLvYLrM+ZPPHBQJj1TsgxeDgSuzYFjgaz78biYehGLQ55cTjYky"
    "JWC1eAfOK/rHGv5fP8EPspbp2FBFxrA+xs8blu1pWENgM6hcseSjrNifLYkzhoiNYB3DpNITjQJOV0eJtkbdXmibpyxK9Inq7upp"
    "vDhPMyc1SsmTMXNX8O18OsZTRMUflvBbc74Y4+EAnrJPf+FRwAkHe0xHAs7FXWdlVapcUEm3LCy9sR4BudbxVcRCU9f44JLjRUv2"
    "qaDeVRe+Fzvgpw2sFnsuVOwLh8T8/lXRpdVVcdR7ixG+YKst+BpfKZVKV3VegMYnzP0E+ZFRMSivPjL3OMoSlKpC75co//MLNQ7D"
    "BX6VgbUcg9gpu/nhQw+wfW7t1tTU7yFKn9MKRrNZOI6QhGpGIWmox8x90anAzaAFOjp3+UMY08TdoBZeTEEWuwTOznOHDAl97sMi"
    "1bnLnXvK0mp4wxOUOv1ebr3/Gvgy6J7TrfE8cF/l9shGCFXs36HT9VZ+QTTRcblHq37O+8UZiu/9dLxLWEDdIGzlJ6Mxzz4qBFUA"
    "sW3H94HibQo9qIRFCpP+fvSErQM/BySVrtB3zhtVBffCM3W1So6Z4S0yWMBWMsgvN74FP6Aqcp35Wib6lbhH+uQCb6mmOturISqS"
    "+IXl+Tx+MluARCi7DTAMQ/rqOabPMa2f846z7uH35bzLL3HdLDdvGOueYIhF92C6uA9wR1mpOdUF5MB60lQVSFnPvDv8JqaSAcOH"
    "pHa0pu6dKnmC1sOsg7qdkg42kFKhy1R0qaksps6ZWH6asg8sY/dASyyCXRAtcIia7pUqoicFP0O1XAArYVkLcgaLrF/FFoqLvJ8D"
    "rrSYnEz0Ckj5G2bqtrjY+XVWay6Ly32UX7tjLcdzammyAuAbExyb4kckN7G1MnZTu3QRcyeC38IUn1R4/CFZj4aXzRpXvn9/Q2VV"
    "GvvEa9YCyIqR8QpXpxvcgZ5Oz2u1q+YOQ7dSmdiIJa1IYYdiyJpZ8uLhsFXtLjBCVfgV+jCVm7aqxi+sGyJhgqmOCWDhcHjnjiQ4"
    "zFiBTF1+va4d6xXXYlTW1H8i17dCFV+ecJ+rxbjvBChzk1uI/C5Lii7hT4NZNP1QETuZlYZg6CUYAYcdgdfVY47lrSScVcaRkaNX"
    "RF4pxDvJqlZHtuHezffeTOdg6xWa8ELjQ1ULFnS8rsn7cqRvmNDiPYs5XwStJnROw/jdWUdbRfDeqhkPVn7D1uUI4FsOnosBvqGt"
    "EnSeHKURLyjE566IvV5ajnLA9W3d8+e7rYvtI2v0xZWzku97BfnFXnnInrVRcMojUMihhiOw8ER1NFo/39qwRgoq17ThwRXWdMpi"
    "etdXqA0spAb9rmxZF+lb2ed7XE9siEReu+lCwW8uZ/aYUF0T0kmZAVVdG7+pfoR66ts03uaoUQ1GLVHkplE5WTYZtS9OaNR4XxXR"
    "AOrHFB3USJHKJZdtNu7KPnmmOaMTsuqAVAoCs6pNqEgYbNsMIWh1m6Ew2lBtdBiFB86qI1+tFcNZ8KdtJLHS6v06wKeTJoBXRfrZ"
    "CHgWe2gbwJVWawEnBU+BnQessUzz3/tbhJGIuLpMvqKKMSUyPU+JKuFT/Ai2DTGOA9f7McBDjh54kgwpCgkRV4SEyC1ErgUGiYgL"
    "QSJYCyJPGlnY/3eLfIVKFXfaLLcwImGQzYCU5eMVHn6vDTsg1eeGgQemJ428aU9P/kHetGnOymvck5I/5PHJ5/OHPD7JqP30pMof"
    "8vRkvT9kasXefNDUPpU/ZOj8r/aHvJC2YoWdODophR6QZ6rzmBqUD42zw1b8HoWbOBUfuPLHkAH1WbZmf2F2NvNzTG6D0VdCTILz"
    "iisR6vFD9jmGnUrxFO7swoHrWgf+QLVXQniKQxLGa5i5rhjZeg6KMtNZ1bnpX+kz/EZ/wb95kTsV3RcQw0/6/svHVTyjZuzl7CTv"
    "Y1pxH43uYdlXuV/kpQce8abk4JkfJ8sjPCIB9jYsQ2cocck/TEtGHErkXF8zCi85f9UFgRT96yrudXmV+/flT+7JPtDlETbSTGAQ"
    "rWS+Y2cn2mpxIly8np1k+Jk0Y7+TfxL7neTZ70nGve60wh0h7vG9oqaVOMtBEMfzdAf5EvASIpWdAP7bkQCqIWV41yKYAD6Ojx/K"
    "R+mxCCKQDNKj+Hg/UaIVDNQEsFFLTwyVs+P9Vr4xQEwkGCzBEJyeXH/UyY03wETxOpqG0Q+U8DMnRS+k9+8j+BkqYSK1nd6Vte7q"
    "V5nAsdBRthKgRpE07yslzWSDpHmfrdXkU0qayaeVNNLzFRMqr07U7Z7dB2ulpRgT8qk1MAEZYcI6lvMZqrkq417tA52TShZyPh9O"
    "Q6w4SEXImSVIMWAPsQCSSOKIrlX4b6J4/GqE5++HvJ7PmaIyBuPdVAvX/yWpfsvBt6OWOqC2L7ZDCNshfFjdSuwR9B1RXYM/cqAv"
    "fgKols+q+fk5IVNk8ziPG80EH5ZXDqp9PNiTcDa/CLcDfxziXaIPdbivml2rsNzs5UR+xWVWefHYJ4RjbQX9HGQH5dMgfkseyqXy"
    "c7BQtPrLE4Wbvzgh3yFfsT9P2J+fTloKo8TUVWlvPeUnSCDNwtkixeiCywVegsTDyj2SMxijXHBs43+exjt0fIQ130ABr6FT/QCv"
    "fO+wHb1kO/UMYyIGO0cFyXXc0naY4mao3PxJxnzYlfWyk1DBKN6yqpwPXa3kY2nOZoT/PE/fszJPGKgSvRDPPHJSjrlGUXNI90B3"
    "K9DmWbAA/kc/X4WpP2SX3DHCI4zUp/xHgi1AxQf/2xr2f46un2pxCr+8a6tz7dga/DyYBrNFONZYD8JhX6wN+Xzk56AsFMpJHhcM"
    "kw/9c5xBCa93+GfA8Aj4psj1ebaWc8rKoc9GeiFGKlzh11ScK/U5yFeo1bNR0y+F9xR8s5D5UskYEnO8JbzBoqgmGZ2AcAZhEh9X"
    "vPx/tFbBXF5MSL1kRw++5fo6D9lLv/F28uP5+75v7pg7lruDecy3B57G+/r72TRe9v2zNF30Hzy4vLw0Lh1jnkwe2KZpPsDOWcyA"
    "CH00w57juiPeOUR/6GAIiIGVccUQo/MEt/gBHlyB3Y+Ze/zQ7y5A5PObfHt0Ow6DBBxIDfLRCVH2H5IfHJyFo3X84JnKD54yDvA1"
    "+/OS/Xme4wfP/xv4wcvm/ODwH8YPDuv4wdefjR883cQPDvP84PDz8IMf/zb84FmOHywC9CBxNe77z1zD61i93o5lGe2e6x24Rtfr"
    "Wl2Wtp0dSFtOp0PprtuGdMdt91jatTtQv931bJa2zC6Ut61ul/pzO20b0m7Hs6k/1+xZh6bRbTs9r73TNTownnNgGh3PsTpdzHC9"
    "nrUDGbbTNTuQ0fa6bcxoe6bZszHDatttaNJ2Om7XgwzXtQF4yDChTwsynA4MTxm2bWOG3e12LWji9gBuSFs9nA5W6FhtHMQyvR61"
    "cDqmixmmY5ouDtJp95z2TsfotS2L4LIcBwDtGJ6Hqa7bhR4hZdumB/W7MDbA0DG6HdfCITyzh+Vd2+y1MdkzXacDGZ1em0Dqdc1e"
    "18GMLo6MHrNgLTDdcQBDlmE5vQ416Hac9oFl2LZjUX3P87C+Y9pUDiPgkhlO17Yp3en2bKjvupaHaQ9miuVur0fgd6l127Vci02v"
    "1z2UhGAadtt0Di3b6DhQ3UbMwTpBuuu6LqZtWLkdSHsdrwdpABJHt41ez7Gx3ARCObAcw7K6VN/yYJaQth3XwXQXx4W0YwO6bKPd"
    "7ppU37Xa2F8HBvCwHPCL9bvtDvSL6Z7jQdrrAtawftsCAnUM03SsNpUDWiBt2T1W3e5aOzhqt+MdtmFWbUmGB5CE9fckmbYNy4VF"
    "kWTcNsyuZ1qSzCFtwTDKNgAy8pRdkttFv1eK1ZIM/UPK0B+ZDP1TlaEXyTz+an4Zr5Gkj1VJ+iuTnT+zP9+yP7/kJOkv/w2S9Nvm"
    "kvSbf5gk/aZOkv782STpr5sk6Td5SfrN55Gk3/9tJOnjOkkKggP4nYsMFATcAfBVCxglT6IY8UDQUBIkF/Boy0auBUmn24PaIDuQ"
    "KwL37XWRSbftLopdSDvEw922a1J9C6TLIckGEree27OAG4LUckBmuihVTRekDYyJAtBFQYeyBLgkMCjXcKxe28P6NgwAactBGQL9"
    "mZ0eclMoBS4LsgZkWAfSILzd7gHKFhAHkO70Om3sr912TGSvwPtdYLcgHExWbromyp4eCl5It3tmB6WCZeE8oNx1PEzbnbbnQroL"
    "/NU9FMjzgOk7PfcQGGm30xPFB5DsWR51D8Kih8IGRCeNjrOGJECJvL8DvN9CWeUC/mi0NohwlGXInh2UlCiLUJb1sL7nOraH9VGo"
    "4OwBKptkGSgYiB3bc1kaVhOxZ7Zxdg6Ci+WuZ3VYuecisjss5QEWcW2sLs0N9BfPobVzbPugi9pKj62tZaMm5IJkJMIBnGEalqRN"
    "5Y7tYH3b7qGwgTRKXFBZbNfllAXt8oTXUPb8KWXP90z2vJOy51WIvrzXiJ3vVLHzAxM0v7M/r9mf33Ji57f/BrHzurnYufcPEzv3"
    "6sTO759N7PywSezcy4ude59H7IQXfxex812V2GHnNMn5FN8QhxdhPB/jrY3RNFqUclFE2WhJmDaqqWA5tA+AP3Y6pNSCRYH8Cli6"
    "RczVtdAyMMGw6Yj0AdoRltuT5V3UdR1Sgj2vjbzbsV3kcyAcPOCqHjBVE2UWCA9QvXso+EyqbrbBTOnBcA4aDmgBMoOjhzzfQpnj"
    "WsRkgf9RmlRxSPc8SvdslxR+q0vZvTYYrmhfEDQOij5mXoAxZbkg+Uxq5ZogMC2XLI0uWGRKEZgGbaVlx2HZouMuqf7ZuACmpcIF"
    "8Loq3D00E7GeBXYgpns9jw3DLBORBojIkBFpaE79iPakMIjuCT3tQ4auLqEPRRdi0yHkdrsOx7UDa+F1el2brQUAT2vTtg/YWnXZ"
    "2uFi0Fq6ZCNaVk9Jw9q3OwciDbRh9zxOKagmdEAQ9zghoVHW6ba70D2KqDaqAx2v3XEBLJDePVJHQF8BeASNgD0ONNIj2eZCvglL"
    "YXdMBA2GBvvQ29kDcQkqiEWE6XYctMAtMGS9DtJt13OxWwdWkmxGABaNcpD+DqgxqD04SEv410HjHAo6PY/VdLrUEsYnhaTrWQ7r"
    "G4Q8G8y0DtjwzN42QXfxGIwwDxLRALZrsWm0gZYEfnGiYHd22cwBA4SJHlP0Oi6Bqm7B358BnbbboKEBoq02nr9YrovCH63ZDjNE"
    "bVRxDNRclE3J0ojAHu0iXu6B/eqQAgcKZpdWAFQkNMM7FipSAIZFmhEYzybpGJ7l4ay7Dp4diDQMY4JBfJCle21QVLG8jYZvF2nf"
    "I53ENAGNHhBEr+sdwHAeWvU9RAzU86BfIFOq13XwdAXogmnFLhA5aske8RzT6LLDCcBCm3QZr+fS9EHBJbhA78PjJlCTHWrfxs0I"
    "e4arUibgFWdpA+Hjduh1ui6qoe1ul8Cw28g7QPUySYXyupaJq+NYSMcABmjNQO4G6pMeTb+Hmw/WGQkLwABFEum67XldpEir4/H+"
    "La9LYKA6bxswuy79dfEUIr+4DVWzd1I1Cy9Ix0gv5D0j0BHoOk7l6/GK0tNF3WsVuj9AdYuvVUSJcltyMecvK3aScBrgV+zsfib3"
    "LtbfoVudlTcwscvK3oI3y/n0PFV6S+eL/k5bXMrE/82CZBLFe1QA+tWotWftfLHTomug0C+/ZLrzYMfWai4ZiwlRuO/yRXe65c4F"
    "t3rB+c898uAt85RJSRSpM+yTR8W90VmUwx0osGHKb6+iW4+E36XHq1UGg2vdDdbqoTA+0fqRQnEv+6bj0J2xeJ621HnxtyaVDS5Z"
    "lPlym7o3UPmbvQI3tMateshh8W1tZ3enQABbzShDn1YPD2Hwo0PTR+ecRuG2r1a3VQpXrBUY6i6H84vNDWsLsm9Yfc1erG2t7sxm"
    "+JhOboCPujvn1fioq12Dj7rqzfCRb53HR/HSua+gxt98wVpw/LUXrIsXURVTPl5r4JDjFTBwypcgeXh6cckUI84/a4XGPXIjq4un"
    "sD6LN79KL4REi5lESy5yN2fzZw3F95f50nqJJsilCqWyjKMU39uyWbGXs5uvsSMUW2FZua2LN3ADYCnJAQ1Z9jvAfChkV0xZGisf"
    "5y7IR+vtUXLyI9crMPLjFtcM7Ee6mXoWjcdhDLZimpyju621S5nIpYzYUgYXg/kIxp/LJX05T9Jg6gs0o1CIxz/N+avkI/4smR2F"
    "HMvnyf6bOfoza+AfptYrywyDwZETerwszBPFa1E8f/D9qKWpN6r585KaB8ICKv5KWcyJ7oiH01M/t0rL6lXCiCA4xrAKvexOF17K"
    "jwSIQ+7RaJmwQoxy14/l2KvadUJ/S+kc/RX1H7d8H71BruZy3ZZs3UYXg+IOuoiS9DyYsntfeBVuhL61/gefoeVLOEOu0wrxhdsp"
    "RjHYCc7TOcvjpNjfwbO0EX8CSm9CkVHy56HoCvP3lsmZ4yUebjA/INCMht4TQ/KBxLtIk79YBflShnaPLsDHaQnqvPZJTNxkv6fh"
    "aSoTM+DwUj2U74Uwt/SIKAeynF0dXLBfRxXIbAiWBGnxXgzOoBFpOf4e95MMaOJtF3NytreHp0Ppsr8We+SzuQzlEp0CftgAYwlB"
    "eTyuG3BvFizf8lGliXE6Dfnkgmk0oVPiGYCP0QjDhBX8cQ6QnX4Qi54VVg92Brj5E2lzuvPlzkbaKQBS3SXb5TtbECK6dItGNf3t"
    "1KAImCjvSNlGuJA7d6IZOmINxEtrlYAlAVStIzMgyI4T2ripluQVdRMBLpmPa8mn6t1ooQHzEY6RbpdvNz8gXde45hVmDS731mua"
    "NQMpKn+lyrlNM1X3bNoOFgAE9vRCdVrxC2v7SrJxRXXiMln6Eal0NMJWlE4lMh2Jh1RkzegQvdAKy19lLkyO2GMp5gk8E/MmdE+A"
    "fZsF+OU5vxLaRCRQ2CfkoqAaUB9EDBAuqBl4fDL7Cb2rgvAYP1WA5ADkoRyHuH8rKwBoSYjI/aq+jgWVpsGfH9Z4r2vg4I6t5leb"
    "K4rwPfVY59S7pg90jfuKJE1dJZNVOiSo1vSUBm/YiUgd+rgOtQaWNFzUtmaKzYt4ug67qFEoVFapHjL6HV2s1+oL22Sdbq+/CYG9"
    "hs8o6HDJ0dPogrbnwatXoEjNsVXmMIk7szmgxzp5n0mj5aLkMImarzRVmTy/aPQo6/ziH/Qoi+asPEq9UDzODfizI9CIlzz0J8+Z"
    "hKnij4mNsxRvetbVwW7Qp30ykKFy5ZSzuKuVPXwVAu+KFjBNAlF5poVxZWIKd8Tf5cX4xkp8DFbey9L6im+U6cDaTx8WX/jsp+Jx"
    "mPL6B9/uMvK5WvXV3P303/YQcMYAbsUaGgDS+bE6swU3VDBwGlgeG2a4rHx+jJGPQ31TU4BC66swVQNU/755E/ZjwL6WRflWHpqJ"
    "SSovqmcXn+9F9ewie+d2dlH1zu38Yv07t7MLeTOBNsaneucGnf/VL6onUpGpVWKmF6WDloJr3JI+gBGJ+FMq/oOd7Esnkz6KdFIE"
    "/ePS4QJ74MU8MC4fz1P0yc6lCB1y90MeIwJpYwp/VvALD5grCxYYLq+qAKAmYJ/Gv0ThJcXzqeuYIeXlfIk10PaCbLS6qML4pKwP"
    "MR+LxWyoKrQH9gSMJbh2AsoGxQskzYE8tKFbUG7BiDSIRv6UjKuL3OiiRB5URdHjActEHHhUuXJZXJgzfdAUSa4wyvQBG6tQi+fK"
    "ytHyR1xj5iuU4hPiWqOqQx4HcU4MAvFEToXqxZtlmFyIPO5tEfKpH+68t4ztClewpUrolFcgP+9WlS0FwMjdtua8t/ImmY9VnoEe"
    "XIWCXvYfS92im1gZxbbFIsnyDHTFyByMRql4IYin2ed4HvOIK1wtDGLHvRMryn7xeG1DH6ucal9snKOY/JYrEXrBjtgaDtXm2LZx"
    "/eki3vl5qrTeZka6XHpJnoNyFvkl1hmry41/R4LOiZQ7ks1AgmZxHeDsteiPua0gJqH0OUAdXPqxEF2rvX1XeOAraHUZir35ZNqS"
    "PoOxht4E57rqP5tWbfBrYaRcFUYWg8N1dVQOInvLQ1XFVWSn5QlILJn5h7Z8KapQvCK+UlqP7MBZok9FhMTQiwXFqxH5WI1xbLFl"
    "o+Uv3FSuO9tWdiRKaMWyjpbfyuOxhq2z8zRqj6TesCWFtRX78qd5mY3mcclThqiPKoRsTEE0Kxw4kY134xf0Phqfvp7k97EeiXSG"
    "rBYpVMkw5GHrqyyoL/csVBjhD4Mu4C6uUafQ5wN1kvpyMJcTXeijwTLzM2/2l/pUFh8CM9HPB1O1HATqIE80z7mu0dIqtIJTVnki"
    "9+tLflYIU13wqXLur88GJUWphFtTxa1ZiVvzuG/KENkPB63y+uQXgquxMDcQo2cDVdIpTivCL9LdeKVPPh6MsPQ3JB05PYVgr4jz"
    "A8wgBhL9TXgWXERz0DXQT/nJIKlQ/i4whtoH+Gc/GbYoogxUmLVCAE4fwz8aq4s5FuZY6PR50jprneBh6FJfYPapgeNqOuZSULMF"
    "Nj8Fe2EBJuuHQVluYRHMa8Q/fuXLsDMoPAfgWH+QCOjH9TUbljLwh9YHoAE4fQybZkhw6QsJz0jrT1rnusisBwf6a0XD8/5IwzGx"
    "d8GBc7re4EL/IIQPbarBCUpuhn6mZVd5tGc8omKhbXWh7cqFtgWPwN3PO4wK3CKo4xbRVtxiLnfpj/RZLxzT3GEA5BWMiYzg1wU3"
    "JoBHfLxtkN56G8TV2yDNtkGC2+B8QEZjOmffHHzkZDwDI5KR1UqGcaSN2KSJ8vaW9OdL3BjDaUsUIQ1+kWNguB9auZaWVqgBu6qv"
    "drC3pD9fYtv796etXO/l5jCA2n+5cxYzDqbAq+1B12yBTgcyr9jtfgDTOtVNrT9tmfop0LXoZSzRgXtGxcbDAY63a22HkN0ahFDv"
    "Cj6wdwt6L6Fk91YooYta2Pkup/uFRMpuJVIWAikLdBnG0KJ4M+GqAex3jKBc3D1lsz/PIDjxPgvSM+N0OsdDvwet9Poa/ZPpqSq/"
    "0bmT8BsjdE/h3Wmz8iCYhBD/c2CgmfhfyhRKexQFKRcFYWuul7DJZELYWurFZcD4TLwlX2xxUFA4iWBygvrhi1pXEQuBT+H7C2Bo"
    "y34BHnzSktY1FgdF/FhFwSadpkhBoAue1hc1WYWY/LcXdZwNRzli2QoLEBcUnWSNUhTlFmuY006Zb2SyMPYSg5l6hdWtasAMDWjB"
    "TMT5GjochdFUJcPloEJ8qDVtvPYyEGdL81agxxmZzFsRJJE04Gc6jPpQKo+7Ko6oRnrNaVPFmQd+9xgeLWH/UqBVHX+RWnDch5+a"
    "pq4eN2uqFy9bM76Gsbr1klplF1YqqaA7WI+kQg9WkE53eYQ4L4k+RxV9Tib68tlSv0UiOgR6bYF2uttKHyZDu+9oXyR6RKuXyoWJ"
    "2baL2J9AXaSY6XMR+xMgS8VLPlhCV4725WYZ8G1fnvYg0mtPp4KqoD0V56p1HQhrVH5VFIqYPFuEeSpPwa4YKvtsrivNmAWL/5+7"
    "N91SHEkaBf9/T5GZp241NESA2CErKpp933fy5k2EECAQkpDEmhnnzDvMw8z/eZR5kvFNu0REZGfVt1R3VSBfzc3Nzc3Nzc18zmOj"
    "aw3McgDTcct98fuDJo1aB2RyCvsos4rIn4C09KhuWMHcE2tTwGg63kd4dfmsWoVyPA1AMs8ImAWhdbbnBB8pj/+AExqLWInyrGvc"
    "wsiEkiDYUD8Hbf3DK42gQx3ivizwpGsXpFq4EpPS8PXRo1C3mlrDcHpsrDPWzihllKSpGIAkq9fHLuchNojaxCUHq17Iudqer9mo"
    "PM018zJYRj/3ozLErOwJP6n7jFfolzHjYw2VT8P89RWsdg4eeETwh/r6GfJNFC7b3jIy4nii/2AtSqdnOjCXLnNID4b+EMa+NBdC"
    "RfxB2LTs1jQ29HgSjbYxhp5Fa+M41dQ6TiDN/wyi7yH5DnKh1SySliDfyvy15wi3k74lNBFeSPpKU581ZRwylSBnVFQIckzTisuY"
    "qhupQdYPlcnOnd3NBaBlabBPqBI2IEU3Ina14JNEywpbAgsQBrcmrwag0OYPYPjpi89SBJ2EIVBhuNjcavfgDHtVl1EmqS+71gcC"
    "pFdteOImdTnXuoALqOLeq/oC5+IWNJEBSTxgT8a2PpqqA5XMcMFLBuyBwWtGDnAvL+YaYVIjHMQCEKkRBjXCQWgm+xIkClEPVugq"
    "e3uIDQ6OZhHIsEFIkUjiRNazLP75b9+9ZD7AAMyfL2DhatKfdYm7t6HlypZv1IpVOjH0BNYljG6jXz5DHvfsE31zzHkADP4g+EIs"
    "bg7kDn/Gkkewq+uRX5HC4IIyKTwEG5ZlVyxzdwRq+t+VvJ7NqSbV4qPpNvNpdfKB/3+H27Ap2R+UUCKckJd50CeYL8r+CQgVc1//"
    "y2eAUdrAmuo4eAHp7ArGoqPZxqWgzOY4F3OPFzAZ8rNnLWsVVD7jDQUCAc+mJ3Oz6MY/2xidJkQYplnvm2MWSECO0xztfpph/6m+"
    "mMn6395dhF+grDXfdxsUY02HAZN1C9y5bsgeXfp++86CxRr88Nt3Af0N+2E0c2SM4QcHLx+R3x3n8iDMQlK/4zSPlSMINUBM93G2"
    "8/Vn+VkEJ/0wXNHhoILcpouCrjpFc4/1o963I5rn+eC7dBWuK9nj4ArI4k/1mX0AcjW6yH2PmoWxqfttjyzYP544eGx9Fh7kBw7s"
    "L9wDNLg0VyJVgmJQCTJY5v3jSdTMXcJIiOSf9E0OoPGZ/UN4ljPsg5hh/8S/Iv8U/VA9qZ/meNCWHiPhz+Pz8YHO8FCD6dazn0yg"
    "APhJ5J+0zqD+fKKBvKgEnugABSPWa42D0yi8fX+CJz9DEUSjLTu4MiWj+x+aaNQl10uEvaFSD27ghcLaRceOrq8wlN88bgT+eFoG"
    "T08eNwJ/PK1gE3buYXk+AxPAaL/9+HHy466uRBul+JZeeizFt3LTYy1ITcZ3NS0cQ8lo3MabPr0UXV6nWsjUvxE4YEfG4jXUnaaO"
    "jE8PRZl3R2ArOAFGIZFR8dqoFn/P4HhtcIu/eIxIawEoEg/zqA1T+qXDIoM6aoOSfu0g0BA2T5J2+WWbnB8/9pYcfTw/fkja9ZgN"
    "v7CKOUcHUjvcWO65wPpFliRLbEmyIlpvtKAugBmuQE7fZZ3+8XR54xLtk62YfVJ8F/uGIz3xPpYNMvA/pk3e4DEeiPXEabDv/3UN"
    "7Z+OEDDp32jGDyfXMklgfsxT4zUrlxerQlvCOqK93SZtQ+4koZXc2rRf392nH913dR9WsRuqUDxmsHPb4QPb9qNiZvecdrFIwCUq"
    "LflFFwqdYqRPNM/Vk2Cg+Ul2M4Cy6hVdbTFFi8KOYLZD64BD22Gye5ovCpC6zVAKEIkE1stdS7AYqPdPvWTQ56oL8D/oJfwOlZ7R"
    "jUfz+oUU0vnJQfcuXj77nEZdGH+AqHQKcykDwUFF4A8/wY1Tg6j43QzJFLMk6CX9OydnrkeIQA9nns2REIjN5u+/MzxLy+TLpYB+"
    "O2+eRagXcygoPZTGnqRuo2mCNYh+V8rx+52Gk7qllgXkJ0Dq2oDMllmP1rUJV5tqGYAV+o8qmgUAl2Zcq9vlIFDMcFBBqGtYs1ik"
    "NFMWulzUp8APDogWrOigwPnF1mX39MMWe1u3ubMUIMixpHkgB3CJmlnT6qk/NpTFRHtsOzS+Q30L70LBkrCqX6HdgzkRa03AsnsG"
    "GygDTtdKRgADx5pZV9tcl9sgaxeAkdmafxKNFLtdoaFSd5QxLAothbAxJDy6m9CPnqVBWddhRfj6fGslNXNCa6q2o+BWkZkiKuYP"
    "nsFP8ewSWgU3MA+6tHanlsnkT+P3rg2YEjUb7CeBPX/oWZKs9zYa+D7/i2sDjyL+YVUMIqPY+xh1gfD33598ZJCukVvegh3Xim9F"
    "EHKp6DZKCJnb4JecAuhLgI9vSG2k83bcs+obgmmHNKvAgjbVz7NN3A2wJlVPgNX0wPjdoAAkcfiETg0SEQOwQ/JWAv5UH6ggfJGe"
    "Ef5XBGaIyyX8+fEJ6nvhURjxVSfIVtst445Rez1FTtdQd4PhYAkcAoGDNeCAPwUNDtaAg8VwBFWMNxN/znjdt2PVhc/HPpuQ5A94"
    "yZn/jPlDhpDx4weFrXdNG5hbT6Yd76O+7eP+4G6iyam2LcUKEn4BarLPdtreEt70xJI9lnz/+NG0GlgH519wLDvmQWFRE0+fSNlP"
    "X5HbGFyux648DXzh2whSx7WYDoslIuKrPlbmjqffc5OfFRSl1f0l/ydycYQ+gi7FoOXyBwn9ecCJWhVt4/t01/GAZPqwN2DeG1++"
    "6oh5+yA1pwNz1xES8eNTxioWwZ7wMnpHR7iCdz/Ep8OnDCZU7LiErFa9w+Udox3nNaDjkvvZhTmhksQlr+1s+xzO3Nel2CwRTCpM"
    "TSkPn+uRxllry6xZZcIap3hoq+Ayu0Rk1ZvVQc+8axTGAPyZLzpWe1C/4uXbxoo86+P0ZytLBU0aj8XIZGl95Mljddd7U5T1Dgss"
    "eOiEzMbvCinBlQ1U1gYsvAawgW+GRpu1Z5v6xYxMrUnakoew+2KGjDRJOBIK/KxkvvclDmy5MnIdVdyDzG+npy9z7Rm9OTTpyeYy"
    "CJ/Eu0AiMLVhPBk1ootiJ0ElX4v4CPLyChQ0pxosARMYsU4JYiNC8qH5HqAfLdP7AmTwRAwcQnw2J2HIf1FQBhybfjS4fNDdF5Xh"
    "SwDeNuCf5N0+i68ujcPq3SCouAyOgop/u4dBveuuzMAH6jpvAlnjteR1HW0mfCgIwB+aREI/GhKV/rqPM6jWKcOgGpYk42Uda7I+"
    "hPOidd0jtphuk2PeN3X44SyYn3Fy5vtO64tOznKxFdSeAoG2LMc2Y7tCOZbzG9wFUSpe3S9B597RMIhGtgPKuOFecQGOTKlPnzw4"
    "qYAm4YEeLgf0ZHPrs06Y6525mRIgyokvLgFNBZBVRZfp9QnQMssfpCIpP/aM9hWGN300nG08u68PPL65lzOouT5W0xzpQyVl/How"
    "X5OHr+BH1sYPoR8GszrCRImuwFE68k1bv9432d0hljV0wQ4su/izCf/EnxmYAs7gv69PgC5E4CkQPReKTwgaVPb779A4NY8MnbFs"
    "7W6YbMyZgTd77wA92Ivgdzfa7flEiC8FcOXMfO49nWavQnMLEkEqZubGLH59wTRkQAU/wW4BjgBr3XHbCTtuuzodtymA38IIfzZX"
    "TDjZ5NNId19FHDkZ7rSQW6WjrEC/SsQ52Oc3ef89KpB2UUeaGzEvR0+4lIdPpwUK7YC8l31QRBgXwlwFZTo996K7dgyanmbt2dyK"
    "UfpxeZTRGfsfxJ+txbPUO+tg4B5+pirxX/fwc91eHpQNvRTPr1a0Y/lBBlR4VDIuKMY55ioWGIlTO2wTZW5Wg8XSJk5yeuAi5AI9"
    "8YIvTZLxZzbQcaDZU5gJs5aGUUFXqni1E/B7JTJH5S3doIKexOcxaFwJRQOxjt/isNC9ArL5+Yffqzm4uj1zHfBpE4dNx7y6xLle"
    "6IPu0qCPUEF9gJ7L2eUdP25a26icyyp/te03EMTdLglV/IKO3YjkbteEUt7SNUfC3ryB/kjRNxG6CXxT0ySEq8WtucdItNpvGMUD"
    "ujSwO8zDHhmhN1SrQ0abxz7SHWrCwyG7ux9zDU5ZlMCqErTF4gGiVsxt97Nue56eJO96k9TdBIK2ABsAa2mnO0u0Y9mVZzpRoo/M"
    "gRCTQ8G7WDBRE3ovCZH3LmZPKsNq76nqwD4PnZW5od4UIwANbAPwjkVfKD1AD/ImBqa7kcUeiq1IBzQN/mc4mDW7GzVFDyCmy5Yx"
    "aO7br1Zm6vCOj0QMIGk9GJCwPM9JCqe8QWpyoXnHFvIakWhSUdgmWjkc37p4raRkdn9vesAnmBOG3Yi81UGnE3BTuVe5kMbffr43"
    "je29p1ed93nToMuC01je3dZxQw8wRtnVzFo9qVNnumFLg8gH+R3wCB0RjY0HLLBXsJDeE0zDxJQsvnnv7AWkl9fdr9rKu8hId6R6"
    "vRdPActLWLXVdONjrrKZVs8pmLl6c3Z3oky8j5m5jrvTZ9cJ3LA2d7huDIrnFCDkopIaV/KkTuyw0NSgYxhOguZg9AtNH+dK0wZf"
    "dZIgOn8/QLqQXOjXypFxgAQLzbkNGLf5iNq0j/genZqrvZlYzZUcRIcY6NnkidetFormgAt5cw2AZBN67iHCvELh1CBB/wH5N7Wx"
    "d09iccHZmpac5UCiuYyHSISEmiUn4xu8zAesbbxLDy6U4NgRLbgVwBqh+TeKAvc0EN6M+GcEvjvU6UaXHvuzJ9W9XwT4767jeIee"
    "4t9Rjrxp28Bz8DYRFhfWjoZW3oe/4An150+OBBivk+NdKsKV7kstPwf/W4/cfw/0noC/GUCtwnth1Ov9W2C+mxr0ij+FWFttG+jg"
    "P+47+YKnhZ3D/b3LudZLFGA2LONo4B7L9jo0k3BKzlhp2gEKdgQK7R7XMJqX/IiKuARk8tAdOOqzr2HWqHGfENDp4GHPKgq9Zl+R"
    "7lDZR1L2dfmOP1q0RR6b2utSn7K/cziyRTvQFLgeYcC0QGnoNG+vYTpdf/YIreZV5eKJBQvwum6HxBH76XE49SpviZN2p6hTCly/"
    "G+lesca8kQ5qvBfppiqXtwH/bqS/ISDbKyVdkO5W1IB7BZ+i4+M6J9w7I1lw6cJo7qITV7LzFkcVZ2w3p5EltPTFkQaQbTSKzoGM"
    "omFEGM14Etpakas86UE3L/lgjbqIza60ffxTRtC1G9D4jKhUPmXUx9/Ib2STZlGDo1ySBJ2s4dQ5LIg2lE8ZGe8sWptG7+YW8E9n"
    "CVsT6FU7Po+POIWDgdw/mTYWGJDsTgHEFXF38JcpB3AKW3BFiAxIL8j9ODhz8HNTcUDjttiD5uI8fAg7R8ZpkKreOIOOecMrH0+R"
    "Sav1KfNReGSX2H888s8Mi0EDVLPuywysoYmy1f2oajfxyOs6elygtQbAQFUwEOgxAvz1bLiDDmPTQqiSR7ZKcxdN/zyocQBTtpY0"
    "D5puzk35lltwvQFbH1oyKUXm3FRAU3qZqB9GWkfRSuY2zco8KDEltNxNWXj9AyDBETiv6T3MYFoUIricLXtOTBHKUAFghs2kDbGU"
    "aSCCcS+o0QOR0d/LF+DDeiLzBWnwk6wobBjhJD5cElOfu5wKFxKn9MmXj/P//rvwuAHMl4cMuC3gHDdGgPtEPvUAHdFBCw+CjeIC"
    "mkkKaBpSGu7eA0MW3OSh/GWjF4fUqRXOQUHWvbAh486DaDE0sfhlKmkR4VCcyIUlrFKfGFlogQiUb1o0Jc1IBcfnMQ9OC3ZYIjP8"
    "leSOUGgJr1w9MJBXAROB3S2ShxFuZVZwKWVxnu4eYomKyex+/hLEq0cPtYM/OwaD0irijIbI0DxrTWtCV/lNccl69ESWnqJ3hmKa"
    "3gt7pHE+HSoTw7wX2goap9ehZRGKRrARz3nI4O7EG0JbQ/VuuCxUBNsM3g9xaSpOAiig4riYPa4TnN37/aIib+8XFX+1X4kW3tMo"
    "Yc2vNkvKvb1hBMerzb4ztujrwbKMPdAV8fjt3ot1J7tbEtPz6+VMlmH3C8qswqp4h2sLFW55L9yWpexrlH6yRlzRTFTvYf+oirhY"
    "Ce4Gr0TtwnC8VhIz4/arLaL9ByAAEtaduGaOTexOWf2sf69bzM/I5nEvhh7qDaDmDWXRztN/b4XSW0Gx7Hd3yr0a3g0eDfCuc6cV"
    "vRDYwBbXOyW1OG3XV+K0kXm7F3rZsKO/vC1a2uV/UrS0izVaWv9k6rkIP378GOA/Z/wnf/KZysOv744QT1VyjU+rKqSfD6r4QZFk"
    "IGLDm44HhBOw/X7QxNTH/6gKH5BeHZZcgAxSIojK03AL/4ADSyk4YNSGPrEf6A9fbFj+6vN/wPFFYOQoHcizEQOLxc9KyPCNkFLa"
    "S5ECLkrCYX1/eVRFTH4k2pWfvPtIBR8o/UEFikCBmZx9RsBZSniypDxCoRC+ZgZ1mrQEjlToZ59V52anpqwfvWqcZ7V3CKBg6P/4"
    "njND7kfVL6jgV+oHlfgRjfjBT7A17iV26cct/BZ6VFnkVeCZjEfbAAycoEk14QJj8o/5EY7AgdePJPYg+2X+r39pqXOS7Hc6WDWT"
    "VFHrCedzCvoL0sw4N5UnIH+HIb9wr+qfLDluoofvT/rXZy3ynfAEwyvghsHsCX+on4VAwC9/Eb4+seA/2kzJRjft/8lxAXd/TVzA"
    "9lviAmb/3riA7f+UuIBZZ1zA7d8YF3BrigvYdI0LeHklLmDT4ImXvzIu4OU/Py5gSz+J20/hC+9wgHp0PyQrgr8L/ijDPyiY6wM8"
    "/RlfGyB/wPCAOJF8Eb0ROFMfVQUk5cHGsbMGiiPnaBJzzRQ7zlqMnNUc1ffoZAxOs3TbePlvLaLpw3A7UDOFftnEdQINEPGZjSWY"
    "Hk7CCgccxk6BJ3EepZjC4tnDHhIBjIEw4xJE5WP6adL+ZB4oIhyburKqb2HFw5GVr6ahaqIgCaa31yFzxmRzgv0EpXbR6Sle94M9"
    "RI7LUb27UdscZYN6uK6GY+LMuc1704cCrjnjtGFfGxbM6N5qHEPUfOKYgtZoEW2EpaawM02Dz69723FBF6VFMh7iOHAeUeDaLtSu"
    "jfpenDic540xnP8KzszeeMiy0n1aWFIBbwZMQ7z6LN4wCGJhFZbHVuY+c4bu/EIPYqc/6rMHDTO5oiSB9Cwrznh2nIExyZA7ItiC"
    "ya9Gw3FpYIl/ZpR5zsHN0p7qh+Gt9MZsy8K1MVTG0RhKtTaGw55ATZjbeImTJKwrMzVHUsjzdeswoTQYmH+bB1TsIGNgfhlrd9lp"
    "hR0+jZODyIMDYOuaPjXDBjWvIZqeWns2r2uqgRSucSW8Kty00lZg8TKBYoERqZ00a9NVg73nBbngsKa/MgU6WdhnoaDb2CC9ImkV"
    "3yfcb9JQ98KjiSkNfqILBdPMmnTDLq3agTJK++1t6MrjtzajVcAtZWWO7ohKFb7l8PI3ZqY2OzzQPSxedYhFEkoiZzfotd0hkptw"
    "92hBL5xJzX9NhvUHKBzv3ulZhLg+MwsIVrZC+DXYeIJe9OZNhw/Us77bmNRmzzo/R75ZSo6qPrLeNJ338wOVub8HeC2GINhpWsRh"
    "y28yuyJlqlAjDZ1YWnQwdrfAFj9oVkwhcQm6QrOjCTo1IxIE/nBBzANMN0kpMBKB+uhQc6IrTZOEgc+t2ohchvPZ3U2ZALflMHKW"
    "hnWMznC9ttCbBGZ90u17t++/JSl4yRWOkppEQaacCNPIFzO8cjvKXqvbHf/oNBIEhwcDr+8iDI3ykCwP+L9PePJBP5fQ5h5dG/kf"
    "MVh+TfdAjjNyELrIo8J47sE2VoB32a/4QdcNI+ElLPQJpRawDtNHHHGDgmUGSF3KmQNiDfLitgRNMbTCznM0s0MGzXPNY5+eArrX"
    "OKg2l/7PC5mld59R1SK0Sp5n0G9wFpLoZYFluD3N602hEqgZraKmXXUBFfPFF3ISfASyD9zHYWQRRpV58POzG/xZcKo7Qyzpneop"
    "lo6NwkPJWnQovTZQVAx6rSaDRd8oyIW1JVjktbYq4t5ANfx4HctLEz6XrxWHHrQs6NASnNiAOSZk4E9nsb6FOvo/RxkkxZMucDWF"
    "oSWjK/zpLDagF3oZ8NtZ4N+g6f6GW6mmqUbfZKqtFPxR+P3334CIAZV5hqNQ1zMT3KTBCeCjpVstD/EOzV8EG8TtaQ5r4U6iOVEV"
    "gNw5ANuU1dkn2VPwDR7cVKx7jZEOmBKQnwBHJP7EtA0PuVwtEqBQSVdbD+xuH1vufDZBrnO9j67DMWJruzJP7dBlOtfCOkF3ZA59"
    "uktZjFIIet7w2QOGdG+n1N0sccIashUyJJVet+g9MqWqtjrDwdyUB2VEVZW5xVFlfXOb17i5H9ZBxzdktGGqx/CiAlXjbp7mtPLQ"
    "15y2fesnQvOX5o4IEhlu116eYAZvyVDAgZ5NMgaCwJcWi1ubb7yzoHtWD4RZJ8PqxNF2U2uErrWJPEhygeJBBT13cQoxLehMFBld"
    "s8sBGpt2CLILSc9VxjLm4Bw9CCCIfcDvabDND5znp0+qfGQ/ffXPCSJcZEh4GvwloPX+AtDwAiEXim7+I38y6O9HI9inlXosMT+t"
    "J3l4yeFCE9C3JyFVjeheDNCbIljnTdCHDXqDC5Arcc2ZHNL8uMiRbFAlhASpy9PTuBtvMhOkGvTmP1apkVjgfcevKGke+T0FR3ys"
    "TFdfNL7koWQh47Hl2oK6hk1DcpPvoLd76G8YxuwSFcCp/H+t1APm7t8TdWwNeMg3tlKuQo2jzN8uRLwYc2M9NJip105DRp3hexSp"
    "6IVfG+fgnayt2R/Z2TJ9esQUShp6QNzchVDxQiDMheVfzM26ERumKbiLEaxpG5AFbbARM3k56NWNqZgFHze5596qv687NoILqW84"
    "vZKNz3ZqdTt+vn6ihUVaQAozZ3kdSD+/gbc5D0E6qtHydGF2b44WZU1GnioBycE1Cw2x/R5gf4SI04nAvBVp82JVdX3xaOerP+hN"
    "+WjPgI7o3E+rJi/J75tZuKl7zBrMuj+vHQDLL5lXwUt6Na8Il5nXp56wVisH+Llpvy97wx4Jh7Yv6Z/sz9iSmaMMjaCw/PQZ+vjj"
    "0KieobZE1e3IUGQEqCnV9nDdJK0P37vAIN2u5bWACB4DMyKqv4XNODnCG6bws/vixZvZX4xOtJg1jPrdMOSBzyARknTDFvOCs2R9"
    "dmtVgMR9ZyN8J94d6/Xn0a7rLpzHGYv6MOy69IIWLckrTbgp/DHO4HHWiypU+0WWq2jw7Pub+LImtsMF9opw7BAtvQapaYYsg/z4"
    "07RviCKGnIdwqUkmryHTdkJxgRr6QlVFCVrO0GsaS2ywCywP/goG7H5e1yCjlZJ2NiSxWxWf/9lnu/2wHaNNpduabOc2OO+p/fs2"
    "edNZzE908SZF3K/Z4V5lGSYZGJGSlzqd5SHL04XseZAg4zdoFcSejsi8csWtH29o9MZlfZ8BePuuvyWfaz6O5igw8Dw812J9WEV+"
    "l9sN7RaDVlUZzwg07WQhXIYaylkkOJ/7g17RgGxm7fAJn6ZXvKMoDKouxilByozM7ArUsGGULMTXDDRgPj4fu+W4G25oIZ/QhacJ"
    "jAZLn1jPOdUjiCM3L+icpJBA7MF3WZO4g3vP0sSJeLNO11UZ/It0vBaEafeeplXyRN67WGbSiUfdNgUyXjPtOm2TyBMXZCTH8qv5"
    "89mmGdOOpFpcKE3faSllDwWf1xghqIdCGgcvXs2SkENu83gv8JCbzZzOs13ynswGn5rchB58AtbYoaGbZ0BzdmbEGuP9KDxyAsMf"
    "l9DyFEFuT9PYCqyGT0ovwSUgIBQw2xmtiKgCPCGGWhU9ftBr6PFsBZoq6UC4BgV6CxyaWZNzPd2bI4tB1Y8fKMZS/5t5i9RfxQat"
    "wZYc00Dw6Wa/5cqTNLx5A+tmCObSuDsP+UvCZN1Fwccp47NQ1k/FzvpPiEdlohyn7Z4HznTVlPkJOg6NYW9B2zR0Gkc2oNr+CkMX"
    "ghpfVqL89Om370Yb1eULvMWBBvg1xmfcdTk7ME8LumBw0f2/trxdwIZqAy+LRrcYJ14jZ3925CwaOYto6lW+4NL7C57Tu/aWr03v"
    "XftkbWaNQr65zxTBDLqAk1WZ5lT/nCh37Pa/2g3C3X6s686u3HVt1226zfHU7o9Ln/k34+71RnUjVgeo7nP7dmjdMYAEEW1tux2H"
    "XMIBlX72zk07WIQNw8bihWZUhL87JpOcMoKvzHANROrkLZO7ganxToDsBI4Sz4+qiF+gN8QzK+dpxXJSwll+cudoumV/UzVjcEjj"
    "o4w5dfNfbWjYJRYCzfdTg0SjNIHuNsAhGs9Hn5fdrB4R2WqEaTRtvX14Dw4dBsCwTe3TraGRooV8RTq4oNtVrBbjlj0cQX8qvM+B"
    "gWtc9JdvCExm01/BVrAOzjWKmHWIKnyqFHRR4N3vt664qc6C7+rQdvnibQfK/nFPTffsbbTLBii/GzqsdrvWGX/xZx4o/ZHmn6B9"
    "IQDagbbsLjcLd4D+M/zsjiWTRXHwZ0HSwHG5VPurCMbalWkePe7Z3OHwvgrUI439Eb57v8ca5PoXdeq8emJfghZbKM9QoE5jKgdP"
    "/PFjPvcH1M/YTuOBCnJPH/XZHTqK+9Fz0DdOm0FFwqPbtoiIKSg/YZ3hv9eusSOhVkGzRBXp41CMa62Xe3d/Bgx3L2yNtl+7jpA1"
    "EynLuzTXgOHmAm6VPIJOC3ZTOcFWDatj4mGAAg66eHCH1dOcxq7cVe+Ze3trHS1eLd6lHv4a/IgCwZpbdV9WQZcbbItGN+xqvhT+"
    "CtmZt4qMrCZ8OWzzNVVdZua/AZH8N2758g0cYV7mgM6a8AgG3ykG5zz3hVvCw42ATzTys6yjRxXhUH7/3Z7i+44dHM4FMI8sdLxF"
    "3BfqCfA5rZedELQTtGXB49N9uyGPwSHCwIzVpq91fUBosuN/9U3A/eXlSTKObkgkVexyz52u0DHgPTcPkOC0h4u20RqLA75uZokd"
    "W5C1akW1o4u3rRfYM3j6Tuxp8+MgFkefltnlEWzTJlDQMzIWvaT3fTc7ZxOC6E0UfISNH5DJL9gbBPekPrq/cfIJ+t7DwUB5bm/Q"
    "9R0Y9QjpIgg2IgCb7t3INVqxphcGZeGisJbR8QmznsAnfkjocMbj2rKtjC0esnW2PVmG+9srTBvGHJmfaCmanhl/wenRrR9NtoEa"
    "52jw2kMt1czWsYevoL2WOUH3GhZ0nlIMe0v7MzazxaUJRLCvfzF8SLhOMK7IepGIeu/FmVnNDCjjs2ziwBymmN0J/v87DCEOQwtm"
    "8W/ixsTtHZ3pVbxrfgZFq1TmwT58oA8vATULAtPEcSbfEprQifQBXkcw6wmMsBaH/8t3ynMm0yKTozYge1lcU7o+K3VjXSxcdKzZ"
    "rt7xZvxnwSPHRCgWvhMc4+zohUzzG13IljPmR7WaTEtc33k0YXaPB8ja/mL4q+ahqscqR14lTp8G8FWts8Gh22D8z+YVaNQHDBjN"
    "XJbnffPv4Zd50PsUqD1Sc3ipgg3ZfGh5wOYEgugUHDfGPGIIhKvoZedzNy9Z9zpzln6lR+K1y9Lt6xVsPehwvhXCd3Rl6cTuj+xe"
    "R/ayr6LeXlwfVf8dvbpWeNscuPWvvRl/Q8+EyT27Dt6d+OfU3EzlbuN8CdplZS8y97DERCxiTm4GNBHbvcLLHDte67Mqih39E0oH"
    "D/dGyGDerMZTjbfUUPWW1xwmak4+vGhK87VJpFTCZ7H7KU2QXerW/h/ND4oc4pDzKb4OrptkRAb5EtQvMwuA53ZcQFUYH9yXiYts"
    "YuytOcy2ugvQ3Wuj2bA8sw0in9SkNvZPTQJN4iSnj21yiwHv5Yxf8NiHNsb70EKAzd5PXa0fNF/Q9i0YO7xEfoqs0+Q1Wt3xqqUX"
    "d/iDc7Q45kH3q0K7w2oznA6f1Xqm2Ws1xJDZFecr0+qJZSKjv1p9Du+zaP5hHrCYZniloytEEkbphLzAc5IEUHfcY0EdebIGyUiC"
    "QQxK+hYc2fz6rE/BDmo9I56CqCTyESqDDwY+jgCSQEY9BaG+Q0E5yiaY37AnGaBD81B6+xbsS5wgEEekxX0Q71vo6/AtaHhZ3n4L"
    "Gl6U898A/J3T05c5twQsD18Dzb8GSzAJumMCiSgHTSH4ayIs8KX5k4RVCfmAn5D2NR/Ppg/kLVJLYS8SDWrqxeG6BehQtG8aIRQI"
    "2wzAMw29geN0slLNsFbtsJqg+ntAQZ8mBOigNSBo+leP4Plr8Kb/yum4d4Kq7W8uPZB8Fd/540/04AmkgW/yjAz7bde+4BWkDpy5"
    "cZJCWJuRoPf31fC+OTppDl6CXJDGe4/41JV9cxP5QXs6lKaTPUhhcCmdKkESbxQiKUecopE9SFmiFJ18QcoKpeg0DFIklGJbViB9"
    "j9Lx2gKfmyeV883xCjV8sHV8MJo9oN/THIZ9l8E5fG5yFA+4PNJ+kTjwQDy5gDZEEQ4JvgSFr43UL1Tk648fT06+Qj/an9j+/rsz"
    "jbgJpIO6zg5wrE94Fj5l6EfrpkZCzXMaGP7gF9ZwF+Ej40E+qNGIduC4Eg6icRkGE/MgcrbGIkeXeJDEMgHq14hLbHR2zcyhyx4S"
    "6CLzBSMA0yk0nDVcYwfZR8Nf9Vfi+vULKYH8PGsl0MdXoiyiH53HPIuvb9aym+kubFl9x4IuMqDJPs4wtjWjBNLuQX7MsyoYkLha"
    "zYOASlg40/uFuBABr/hkLMBPoKru5NacgfiGJRelkCLgyC2J0hFM2Rwqe0ytaizmU4ZzBLyw8BxngWdEfYH5NxSigLgIJbXsnAnW"
    "Jqv4mXbocS1V9XAhrBaM9ccPUkDzmqJ+CXsTNdFO6j9dSZg4D1GRKbdHQ7AEbgf+8mgGHJ5RWAr1y511Rp7o4cbIh0d7+KG++iXq"
    "3ZrlTT9u05L02po1xDqyXvVFg82xglQC7LLQzpwsWAWQiL5eqZ9br79+jb6+3N66jn788NEewt8zpjwNa/6/eclZVthfurQ+Wfbx"
    "T2YOZay62K9adfFftuoSv2DVvXFtfGlC8z50btClTuKPldUtPDy3h5egA8ovN1/Bm/Lm//uSDc81mJ6fyXnGH6T8X1/8X+EqrYJV"
    "GqQfnQfhZzOohiOLIFrBEbIYiz68GvWwA3CQ6CNP8zwM/5dBAoHuUsJtCIhHVH0sBxvTGnqec/PMXD8VAJh18UXvy8oRTDAETQ19"
    "1QUZOyRkcsz1vn+y+eT4lDGN/cVgbl/mqG8kf6Lm5l/9EKeZnA/6Own7gw1D6jILV3rEIb8OgJGEhB2iNLDg3xSdiMxA2DYDpvgL"
    "c3gkdKJZbxmh15Uxh2081twmOB1xDwoQg+dBS0tfNWaFrOsAvqBR3dwgfQtcGv60naHqE41NwYwma9ew28x8/jM96TNF5seMVQ3x"
    "JrRSNrSaT+ceeDWTr7n4M8ZtZm47zWJStiDa2kvQ2o47gs0cx6FCcJCWF1KM05xf4wj+YM+3D37XI5OwujrgJfhdc3CU9Tnx0PMV"
    "0WRiP8fSAy0wG1Fmlw/6oynyXg8tRPOrK/i62XgwZMo1UqFfFvQIxZSLErS6jlwjVceGEXgX4uLuYByCqs92kjLOHfSjcX1qXT/a"
    "wNETPD0uTVA3vbfLKUbMGKMMkVRMh7E7cqvZSwTes8wpr26EFPVq05YN0Zr22r5oVlLpU6KjCLC+hokbYQHxDc8btaOOBD0QEdNh"
    "d0ZB5mauGwLTDMMqaHY/OI2D54ZwaD40JO+ILzZoiSRjS3XDko4NDIRhWYEHbNqXnKB/gmYCnzwsnD8h5+060w2amZ8Wbs4hfmgO"
    "qWmbjh3aCxA9u8dqMDNw0ryxy2kJYKJ7vmPw+1FAdA9lfe1nUELO/2BpLQierkqALb3CfpSgRjb6o7e55ZCPR8pZ7uuBvCOIS7ZJ"
    "PGvjKTM5bNEKaP5bnAWsG4YGOByoVZBzxB0LEj06tAbCv4JuSMH0je8H0RHA5biP6R0swjcL/A4x38QJjDGSpa1J3UYG/NSPmkYy"
    "dsTkMo9QsyXK+zw+lmS+CyI6OwAEQhJ9wSSaAvuSpoq1zouRQLA+D+o7mFVpSzAJfmkI1DSIEDt3tJ768NHvHHa1T0YIe1HBHgm2"
    "Rv6tlAu33LdTr3llYkIhQom7JGdE5bovyJlL6ivRSHKVyJjglfVpQpl7JVMtKDUAzvAtE31B82fCOkLZ3cygheVjOgcsHPpnJYdk"
    "MEuAf0siz6l3OfjcwUMNK4JX+ScAER6iPCwPwGkpiSWj16V7S4BOKLjiAHCf9vTlAUcD/oT4qocj9kdLVMP53NgZbA0jJippG6Wj"
    "RSCJwJru14jB78jsxsHfNWBJ1GIrMKboWg+UoYT0HItpQZzsmmuAbo7zYXfpgmU5CEYEDwQMlpdEGNADF4YilgI+0QiCDPi1ZlWT"
    "o/Ygb5TFgtSRlIbXylpoUTB5R14XM1ysoehHYurmAxsEfKGxtHFV6zEJJvmDsibJ8YRlazobyySiuQMrDRJRydfCC2nrMz12MLuX"
    "x2u7hc8m9KPT/T0oTdt9w8tBBp5UvtC2m2/BrzMLnjOxCtPo5gHX1mykcXw+oifXekw/8xIwGXpBpCBMkAiuL2iD/gY2AhSvThMB"
    "zRVsKhKcR4LTan71BbMxGTGRdAXbjXeaOY4H2A2srXkV2oam1YHMw8V/vc8CqB/zEaJ2uUHlaE7wuUwI9ZYJcYJuwo/VcMMDN69O"
    "qmXqrIpP2m5VJmhaTSMiL21+5qTnG9pB2vnwytQKuvuDhUxWISRTuwkkYJj99Pvc10LQdGPovtwdtuwCOhrpN4v3a+leLUFFr9Vo"
    "HOBS8AhxUcxCAFisc+htBm6Jn2xXmGCDAtOshXaEhwobXq0XnCZVri22sSsdfbLdhnrMi20toLYsETIAH2KCsrZgiSZLh1rjO4SR"
    "hQlzMg3jmQgfS/fThC2Y8v3FaSrmqgbSBJ2Vu+rJFov5fl+mYu4qp2AiZpYbnMzNvG71OCH2Sf6lTO4N/M2dtWlr3cLJclCB/OXL"
    "5utXPFjAWKhICqRZzlnQCbby4wc4FCtmAxj3DckMstkS0LmfEKBthV6V9ix7DKqs+3f11rG7m2OadOlgnj+yhs22/tMIemIe+7Mr"
    "6/9PGPrrg/YcrkbWiBB6JyLsR17g4ifWUVAry8rPRCuIv+bBlWAW+0z+UgiePrsci7S6erhyAR89IOKgIyWycQEWSoVjYbAIiXX5"
    "HO1zViMefDRx6ERWoqi+VyfyM1Nuvw39lSef4jsJwmOWk7bTzl9zTOtbjVzfCq+LbSwCOehQIfL0fzUNYtpbg2jzPI4ViLbEN+gP"
    "9besv1h9iFZ542Re99rhHm16RL2P1CaG5h59Ij28kYE/bcoB7ZqBrMxg5+R/aZ0eZXTUeRqd0BOoih5IsckJR3w1qMdSzEumSMpD"
    "cxjhAw4cXMd/yvjP2BJGePzfIYxw+e1hhGv/w8II17zCCNf/tjDCh9fCCNesYYRrf08Y4anNatFq+qec1ogdnqHbtMycis2D5MSH"
    "fp849pwTL2AH/RD+QMU+wDRo1J0hjvAuex7se/ONqkqZUOh8Pj+eo4+ivA5FwuFwCDaOuQ8HH36CNUfsqqAIKtHqBuylS7BWqehj"
    "BPzzIfmYBP+kKmH0N5nKhx/jSSqWTmk5H8KP0WQ0kUiChEQ6noqBhEgkmQonQEI8lk7DKuEUlY7FYGuxcIyKAMCTj5FwIpJGvwBc"
    "YSof/pB4TKZBWx+M8onHeDqeNlpMPMbi4XA0r/eZeIyCBpMfdKgSCGzYBoZXS6iQAeXB31gkFdcLgu9EJBHVWwLfyWQkoncFvtNU"
    "itJAAQjXwAQ/NdjRTzwgrbw2VK09DRlafxq2NHg0dNoQP9MmlzgNzos8oH6ifgd8AApPCf9LRWe7U8x2J6en8SNms9oFLzrcofsI"
    "rEeY/8cH8M+j9KBlfPiOUuA/uv/LDyh2BpAWPut5QCqToN/AD/iZ9MOKZy9GLjjHyuQonIEs1FTxBIM0A172gBwqZT4sRFUV90Y+"
    "JvgPS9X3Dw2kR5T2D79RiCwFaymcqBV7+Q/7yB6QQZlpfACbCjhGfSCuJI3m4Z5Gy3BnsENvoERzCWrkIfXGA3pG/oDc4WQ+hO25"
    "BFvObDJsKhz+X85hWlMlegktJizVwXF9zQmWJFGiGU69WtJuD1iy+UCZyh1V9NAdrELrWBdoRwRlpcsHMFbAv9FNvERDErQXe5Dp"
    "JQckJeuU4LxHnHdnZqx0p9OWlai2YOPlVtcHTQP9gWFt0wYp6gGryR2Z7wbTHQVu9Ri4HC3VaGYHtZ/C0t6RnmEu/qtIHv5jGEtk"
    "9DQrSNYWjPKPy6OMpOh/+IOWqmh4765F8P2zlS8PyoZeAqnuvVUJOb+5Y8dCwDUzXsSuAWabCZx4j/kAsjXRuAHLgwZL5l3QEigt"
    "VWAfTmpcgfXyABWzbqVh+mu06FrQlR4dJZ2IQL7dHg3VpT+zoRWfg01nNtDGxH+HS5gJzL4sYF3X1ekyMegHu/y5nkjl93MCvaKD"
    "I7wRRBs9eZMD6eiNaPh10/PayMkkuXLEN2D8Z+b43xjce9GNwXsFrrfCg472D0SH9ZNrArXhTadefA1XQwdQK4uziA5eVcgu5t0k"
    "lEHv5Dvg1Hi0uFrBAM+eFXH+r6OIXzEDGml4z4QTTvCT2Ot/+PPneiXV394fMcV5wG+Ef2aF45rvYm2/pN+f4amOjv/zGaDrrGjg"
    "mDrQBXzqLfV+AlCt7s8zaaOFt1KfJ7w/w4z17l/bH5R90CXtDs7cxCRl/0apHRR89axq69024vsi3f4dUt3+PYLd/hXZ7oFfB13S"
    "3olHfv1GPIKCr+LR1vt78AiafzMeXcp649FW+OU/yBUFeqsviu7RejVdNfQq+ijJoqTfts1NyhvwU3vhPw9+/+Tkd58yqrY6g5/M"
    "BgTGaoHp+nsx9fE3icmTRpBFzLMzSXdWAYtrfis+2TkraszphCL4yUr2EmawK/jWGnxDyCC2UCCKPc3z1gpgfi0V+LW5Ag9DZs1f"
    "vr4EobQ1t5IhdPEHOfnczttBBvRDMLfRzfzlxR+c6TcZOVph87o2TbvMUL4F0eRkyGUkUtEtOIGWr5mcKPIsLSCzAJWV9yBVZTPf"
    "ka2zlqfHoqZegvD2CnuYwmVQW3qB8EtwRfPKnRKgCXjnIQr89U4vMns4cjL03eYNiHYjhou0jvsFK+slsK9L8tyTFMF3Fm5FkHEg"
    "KfWFFMNXF1/divextRMqjovZSlmfYN7rXi95p9ALUYtOTnAaT9zSxbPMdxP5I38kwd+wmqBKlihKfHkx3Wp10RXEp38tYPehDctL"
    "rKx8ePiA7z4+abcD3dOT5TYELhLSxFx35G27GoHLAqXMn938CJOLphc3UyjW1qa1O8ulEVhMuAxI/6j9hmxIFWETzxoMGb3DYNd6"
    "q/Ibue7QeofXKPCuxM8BQJ7x1D6CuQDSPYzexcoqCuuuXeoLQVY47vGtHLz8xA6Zjvo39AxJfkNHnV/Ur0+gitE9Cjam+XmELesX"
    "bwbyATQmbKoZNTCfGy1geNBFEhrax6c5vhKc//jxkdXuklhyc6dfYaliR+b2HNSeI4eFgu4N1bCaxVd78NoPNy6bGtcalj87bjn/"
    "9S9T4/heUruW/iDp6TgG4FxzyIfcjuoe/vAaICvab5kw4WoiFfGK7l5p/IfDf+Sr+SYWfv2Xv4nlrm++iVWu/7NuYsl4nDexaFL/"
    "lptY8frKTaxytZQnIP9FN7GwNHPVtnPnVj47gS1owwLGAiO1KWAnDEJPs0rmi+5rFjtDAH8X+OEJdl+bsWzw86+gGUgQme92uSmj"
    "Py7RJiUIbTpctpzlN6vQgAMSmJNA3TP0XJr5bi3p8N9qa+qJOKXCoFfNWSiE7Z48sbL7HnYvTxz4vrk4XqJAHkCWqW6ueTV/vHAF"
    "IN8yxJ+nuucy2i8/jNaHroUuAMuaaoe4Cceyrgv6bIjwcD32gkNue8aqtwausbuS0+Qvs3t4F4naLVWzYstY4kgQF7NYonx2GwdO"
    "NGRHMxqIl01DbLxTlng/s7cueLuj/ThS4HrFrtVgwALh+ctXyPAYGnCgK7SIxa5DUYGv/oz567Nbb5p/NjvNfqQsrp9dl13Qrabm"
    "5vqNU2DyNy0HWeJ60Zbo6oRaCzyPrMccS5AUJsyDNfxjOMgrKHw218BsBvQJWJ9Pj6gt75FjKj/xnOHXmSXeqQTUg8sCdCxSHMGK"
    "w95lfPYkK795ckWvxRc0egDSgtzVywPm22bBaIf4NgQjhp/QsT5e6u4eeP+NdWZxWmlfAh+pjHkRspqDQ2MdVbSYH2jNQvQvvZ38"
    "/ebp+tGVk3n5g/w5V49Wl4AWj3y6qV6mcgLl+KvuN05TJhhu2WxLz+GtzeR/7njVvMtpj0aJnzyjUXcXfhovRT/xmdXbgZ7FaZ3m"
    "FQ+cMK8m53fG+Wx19fIgZ3byhv3HGRaMXu7anF7Z9LcX2rsLzVubbuKpq2doQz3jhlv4UMRGj4YnH8erEJMvH7PjCfSWHz/dN1yy"
    "IcNbTf+xzNgdrhmGQ5ZXdLiC1aGT9qLO4sJJs83GSwLJXLSxsnVSN4Zv8vJ0142aruJg9d3W0GnANPzz7f6bPN2t/ffyT0Yklrvu"
    "yXAZ4v4P/XY3VLZTL5l14+3M8er5uBbSjMsCQMk6/VvI0mzbT95TO8nDKtA5FoXtfT9H3vpgNqz15fJ+Qu/g2e7pxvrAhSNvjByY"
    "sXokMo/rnhcX5wC0/hX3Vya/un+TbTgy415e8V8gur4wV82ucHVFx2EJnJqIUb2ynL/hIQQQ9EEVMxbn4pF7ANI/DfI2JI9yyVsb"
    "XZlSv7mmnkxgSQ9IHQRSryBVYUTEw0QeJCzsCRdrggYFtLDse2fljd7kD6A/4bgHqWfX1MGd0RevT/TGN5B93799w0fRviSKfAHk"
    "cqBHok1eos/Md6ihBJQK49p951kVXg3AG4GnP02KDAFpc+bPPqhQg9WewW6/Fp6fYcyp+uoR54MdL+LPzP+//+v/huFzQAswCm9V"
    "UPnHAiA/6MKrBOQsILnrcUS1H+QpxiMPGIbOAb9D8RJra+d7dsnBcfuRcAqFf9A0bNXH/pNio35t4/SpQc7/9KfFLYl0hc+QCNza"
    "j0dJ5oz4QrZ3ifDhErRbngNiCRZ8O1955QeNmStC51duLfn9gfmH//f/+TAPwHr1lV/HjVZ8LdN7JUihgmutqGDkM6Kiwpd1iP0B"
    "EL4B8OEbLL2ADGVlLJE/A9AMyASxB2Ulf8aSKiP56fs606TVzSO6c7W2haJsUf6gJfHjE3ForqeeWXankGSXd5w3nz5ua5U/KCuU"
    "PKsoY5CB4TQhFpVusCsgLbiBirL9CFTbY0rsPwKvTrBk0dyp0M3MHHMo9C2bPzZzsIjxzIL+IZ+BAaJ5yNjYuY58WGzhVgzNuLXc"
    "xa3cGV3YWQv23QrCOcfFvmqjWYjLqway002Anfi02H8RUAxpuIw1AEeOZknFVK1qaCn4IFWqYFkaABp52Afnjx9mUO3jBqXzeDgW"
    "QrdQ+NxU+AwLQ1LXafwrmlD4TBQN3H1N/RkxXsyBBTEwMKiRFK2iAFvfhYx7C5jCze8UEQGZGt04GkXPHkg9U8G9URCcc/bw8hX7"
    "myNlv8IjEHwIO//2DfH5qn5WOT1QsSUTjy4S869gsIXrE0rPcHt6zYbO7EL6vKAVNhELDnd8uXdY97PZ3KQ3rHVHfDY2zopZ8E8X"
    "/kc443+7w0u3nw23QFIuVV2ld9dKLXRKj26JSzpZ4JOL1jGyWBr/HpeLZrJ2O95E7pAIyG22OCuO5FBsFO5l+XJEpuV2fHQZ9ITK"
    "KddL1wLd1SKUatWEyHo0iQjbymSyYhcyxccvm36gx3JUsjDjKT4auUWjkbJwU2crqdzKr4fb4oUay5XoatWrBJoCFTlQYI6mFSoQ"
    "n1WP7VVsX04f9+MIeyxT0dg0OtqrVERJC+N2gD32d+nx7HC9dOlYN83EF9foRWj3mqlx6djfJE7bzTYkzVb7caVBp2OrMUPdZhv+"
    "KKidYiGcXhz4dOq0m0m9bTzMxZYVJtJejYVGIrYazMZRMdGYyIlNmlK4wrS7SYdOEeE8DbeWp/OVSeajAzZR2HDx/ZYPX6IJlZPU"
    "PpW81MNDNbc+tlbHNhspT0aj5WrK1JVlOn0LJbaVXllZtSu51KR8GQ4a8eOmNRPkWytAh9hI8VzrVLbxUDeypAby9LSZHsbV4vh8"
    "YMtyr7QfdCt8qpI/Sqms0ucrQrpezEd25d4tG6qeRuNEiKJ28XHgWAukFgmxX6JakXa8GRgwstrj5NP1NJnmZa4Qz6Z39U6guQ53"
    "6VHgGObrUS5NhW4Mnz/n81Ehm4qrxdSEBmOqDOQ2w+3qaqzcOPe2Uy7VWmy6ZWFA19bdRHKUSGQHQkFkDpMCz7VTDLWRw51kdMHQ"
    "x1G5mopuuZwiSvFthDrmTsoyupOF9S7NnYULu1uwvbK8yittIZ/f1vb9Un0UEeJVcRVdxgKLpHwob4b7Aidlp5HINNFs9i+jSbp/"
    "XAxWcS4yFssHpdgbx/Z8l5up40G9sWryonzZibnochDuLlm6eVol8tzo0Au1VLYwo7LN5KIyLLRKN/qYup0a5eWI6lf621CuwG7U"
    "mLLjY/HmgR8yfKQcCaRjA2lXLa8a+d3oWO8Iy9DweNss0hsxxnSnxWNXjQ93rdxElgKtCx2flFodhuopG7U7U9INKdfsLPlUNJHv"
    "JwFzGWWbzeo+N2Ep/hjIzUbyVm1T6QWvNLunwH6Ty66qVH28LYYnh9No2TlKMXqY2k64Ab8QituDWivGeq0mm64VD5PTrCjwci0Z"
    "CSdGgVJ2Wczne+z4NuUHg3hv1biqp14zQFWPMX7Yz/aqfHjfrbZyxRwdOXRXt1aUPS2O+dGUiYyZSzEb2w6oYai+3d1OyuhQ2J0b"
    "tZWixGbdbGfFy8PELDluDplRfzJKD8VSLy52q1Uu2dpFm4NciG/xtw57HQ2pXqRcyo0ntWWSlbtLaZM8VaOlM12o8NHEodtkz5Xi"
    "YTgYXGq39LjePKzFan4f4ev7Ru4wVKer0vUsCoF6XqmPC4kWt9smrpVxf8Ds19u+fM4mDwKfaB6Hp0IxWu2fSpNm71oNh/liLp2/"
    "Sky7PsmWW+NCdckPWoVUvnGq5RvNdnnbSJdL9XXhOjxU4ufzJhCJXtvN00LNVvZHNiqKYq5fKtY5kU3Ujk15IZUu7a4yFbKtXZbd"
    "XIvbwHLIXhuRdrS0KB03bXYgN8DUZkc7JnSpH3rbwHZ1Piaiy9puPe4ldpdE/agma5PTRiheJa4zm9JUi+/WlvSk1R4DEovGE4Ck"
    "pGRFOkcH/fbyNJDK5f0ivU72kvJ5EC/Ui0KlX23u4ye2FJYL41y9tiut2So37Ir7YwQIsY3+abKjb4fGWtln6VLx2Gy0u5HoWNw3"
    "+mVmX+1uGoHFeVzdUqdZs3URu4vIKN7k1dCgdh42Qt1iupuNVLudxLmwqFfDp0JOzQvT0Ca0ZWeD8TI/UIr9E9+5zJqpYfw6pMtM"
    "NRBrjNT+EZwMB+3pNXuodNRc9hLIDlu5Srh7qrH9Wiy3HlCTZeecu61q0Q1dGwx7jaTExBZl7sKPAsy6Md7n89d9Nb9utbPN8bQ6"
    "2VWr52OeO8qn7ex0maY22a3SKJRXhUO1o1YjlUBok5xIi8XmfFwvNk023wxtZvXybBRYtyab0D507kjT6FQ8L3apVmnZqoilRui0"
    "ay4Oi1AttxcbrCwMcl22whVHy1YHsPRkqBEqhZiZlIrlc7XzUlU64VrgXNvy0TJYP+PeYttl6caEbtaUZb92iKpxJb8upqvMdd+t"
    "0FOhVB3sxl2JS+1n6o2JMuwgywvLXl4dZm+0ypduneSWXlwVJd/d0uvLpFRXWsXuOipep+d2iykyuShdDCSEUHFdPRTOxUUvG+pm"
    "c1mRSdASP5K4eicvJYVWmt+c9tvQpJVrxgXhUtzWeodEqLMZxqPHWeCyLNcqQC7O9fLbc2tfDVOjNr+MjSd0OH6J75cHtZgvVXPF"
    "5qocK/DTSSl9ASt6Fw8tldOtXUiXK9xkLB62+d1JPrWvyUEAbKjpSHY6rqXarWWAK14HQ46rLiipJJzGWb4q51brRJ2RpgllOF1w"
    "w/pB3HI9LlCZLphCNTlZdUej3qI4DvdvAhMrT09SeHyIUblR9ThuCoyYu/Zm111d3Ak1pRBh6dx6I3K5cbdQiJc202Gu3l/ULsNe"
    "PL0aDcvdMF9Sq5Nuic9X1Zmqtov7w1ZeH1Lhdq5aEVP5w6LVLsXzAbB55lPlaT1JMcMd2MGrvWazLo1UZlFsSkKtEZpd6a6cDZRz"
    "y75QoDmZ70+z+1WylTp3Rbo7zE+ZcX60TQ+zp6JQ7vLJ9lYslw6DUXPc4xrLJaWADXm3Flg5Mtklat2ywrarjdk6QfWYISX22svE"
    "REwOmGZ8StVqYOlVK/nBIh+jFmFGysaaUVh3Rpe5Vv28TDXY9F6qHfqDyHg4LSoMWz5H1Nq20k3tU8lT+UZXE5OKMlYusew5S3Va"
    "krwTo/1R/RA7hqUTfY4Ux5tTvjW5LXKA4rvn8SUvDg+0dG4NdzGJGd+yybPS2dbLZZU71m+zVmVAzfL7a5/LUZXwsRBZcoHbSlpV"
    "iulVnz+fZ0o5FFNo6nZrjmf8VVjVJ32h3liW+WZ+KGzFYqy7HU1DjW1okEp2uBgbKmZTW3VXv8S55TSSU1dSlcpPjjF6oeamingo"
    "D5bNw/46aSqFaFcdx0fH6VEKD0+CUCnvQtT+kALQ1EtN6dIJtQ6BVXSscBtuEBqOs1RxsU+vz6v4JsCEO+dbkS/1LvRwICSOI+E8"
    "CJWU4S7XP0ZvFzFXqzZHp8sksQ/EuEK7uzwDlpzfbzeTC3Nm6/WacDgPwqdBupM/n6bceNRq9nbjLbXm+lShvWAGp2Y0wtwqm0q/"
    "z4x3Qio26UqRQ1zOl44Vepli9sV9tkin89lUrxdND5O51L4za5dql05N3BVrTFfsJ5R2t34dD5hAQ6FC6uRci4avZzoAVh0QvlvN"
    "S1euhYeL4WYbrbRvtU4vrTSyza24WeW63RE96hb70njMnjsFuX6anDepBtjS67tpOMs3i5decyEO65VyU2g1R+fVuLjjB/VRbLkX"
    "aaodLgYKlUptUjoNGtfuZtQvxaYtejDhr0NpXG5XwsVsMZcvb47NcWnTnDHX+ja5Cw+abKHXyQ6Sg96qNDuzx2ufqQ5yyzI1i4da"
    "0eP4kLuwl2SoNb7WemuhNQu3+nFxdcutDvx0JXSbkUt6UNlxjc6532zwR17lA2PuIKxifCGyutBrviFtDu3DqTdr94RhJHfdjitt"
    "Pr08FbqxyvjYrF3lElVORGKl8OyaCrXD28poHBUajd42OxO2DL0Wajepm2xXhUW+dZCurR0f5pupzmDN12OpTXdxqC/q4U25VhN2"
    "l3CvoPD95rE/q7S7SZ6udPuDSiNSk0ahpLQeylWw2Cd5dT0BS4aBc9hI1gKFVa2fzJbjuWO/Xy2nQqlLexxOF/qRQrNAn+hWjI3L"
    "w0ZHXJwDa3BKOG2n/X1HOklbRe2HJ9fCVWQo7nxWG1y4EN+GmnyNOoVHZ5kXhXB2XGhPUunTIByNB5qlPtsfz84tIIPG06nxNSyK"
    "+VCMqU1Lm9k43cutp2qRlwIDOnWlG+lp9dZt5NU22BaiifJ2cgOM8SrXBod2ZDgGP5nLrl7PTdqDevQ46QbGU1rJH/fZ5b6blzsr"
    "aqfUE3wzfanLs+NusMjS1CG3bezHFL8bh1Ol4yCn5FPFciwZ207yg1ADSK3hlBDIdRrSrJrNd0S+LFYbo1SYGd6Oh52wbvGx5GSc"
    "Ew/7TbMv9sp5INbVmcUtlKJ3fTlyjKTX63axPepmE7ESVe/GwdqK1+OTyDR6WmfrwnJ6K+5329t0XMqGJIqNz4qto0TnZqdeMi3n"
    "SpNqb9vKccWpugjHuqH6Qu7Ht4FKc0jVpc11t94n8pfBdCCIaWp8Tbc3/Gm7rPXUpFi+diL1fVyhSu399XZQWWbRL8cX8W1pzIE9"
    "htvXS+tlS4hcDpdZnV1X5M760u81qbo4KwNZuR2enPjJNT4JH1t1MHeJ1YwPZUPj/bY9FcX1NKvcEtP8SSjKi/a1WT8f08Vz+pwb"
    "t+gaOEGsurHy8iCMmiF1FJcah1gWHDOFQ381TAQK+fylPp5Vx/3iNL/Jhal8kq1uLoPDcqYEzgzbya42+Wp0X6nVW+vEsCNdouVO"
    "qJisLzlpVqcWq8uxNY2l6PoytytzWZWJbqOF8HkXKAV4Nimy1eVmNo0vjptdc3DNq9l1vzrrXmubmliZyd1VkopVF/lDJdkp5UpM"
    "vz05szRXoqjbssuWmm3qGJleT11RuFDdxPZ0WG+oCVdISONEGCBSnLbbRSDTD/orpirGgBQp7rKHW6s3aCmnVEMMHJqFAMscgeSa"
    "OnKFm7y9UqcjGwgU5El4CVZqnemEBz2mJ8cn51V4qdyoXD3HDY6D7mzFhpKL5qUzrvOtY6VSSoXoaT2eKwxLanIShtvF5RavyQuh"
    "06dii2gbEJ+wX04WjHKYzTq1yEmqrQbSOBrq7K6RQDwQmzUG6kVOLvaVcb2rrjrt4vm0OPRqtxBbA5ih+DhXixzDKp1cBFKR1WI2"
    "7jVCgfHtHK8pKSnRoirRRm86DtBNKV4vc1K6vuazZXnSmPXizdjtwqtLIX2Ld6V0Lz9bbIAIEYmdF5PTgE5eWkn6UOqFNkI6xUQX"
    "NzUmB8A5s6509pPJZFtZrRgmtFy2KPVw5JOzUGTUyK1z42FhvV5mh9lsK3vI1sK5+iELNTOBRf/a69FdTpxtk4N1LptT+uE1WI/l"
    "WykiBuJbJb08MpdmWY72V+vuqsiuc4GdpFKBaLWaFYfnaeuUOKVyTUVOng9XZpxL0SFwzhsy4Ru9V4e7RDZWuQktpgn2x3R6G+aa"
    "cY7PXqKr0ybBLBO9ynYW7VcD553auXDF7TZZajR49tBodWPLdUitDpu3SqiyLia23fGUG0Yv8UFi3V4oa2lXKdf217Ny3U4ni3g+"
    "2gjVdtm2xDKrUzEHzhyzwTIQG/RGy00tXUz18rl+L5KvDM+7UiV2YW7RhhRXy6fsfnhNSdNK7lgfNavF6WG8rSUSI2U2SMnr0aJY"
    "4JT2KNffluLhevGyvx3yASCyUNVcaHwIpE7h+qYc3q4ZWi1HUkq5yLK50GrfSBX3s3z1qo678WMoWUmHa+sef76mj+JQoKhJRc1P"
    "GmdG7sdi48RynS10qrK0W/BN+toND7OSmDtdqUuBjXeAvKnkpEMhdd0Bxhs9balBd7s7TvfqdFS+0BMhxyab2WwhEKqHV9FweCaq"
    "1TRPhaLJVrgX7hQPN5odRrlyYphbd7vbzWaQS0y5SSl+arQ6UUnJCdGUnLzxeeU8AafKQiE2PcSu2/DxNkqBHad0at3yleuytDtW"
    "O92JEBaGl/UJnDXLl8ZYPsRj9XOpK+dqp+UsyqrxUncNqif4KsP1NrXzgIrF08pKPXJJ5XZJZ7sdqd8/n/hYhxbBxrAcr2OJI53b"
    "TNr1yiLFM4oSvUYiSv802M+kHFdJ79J8L1EP97nwQOmCXaU4PYdyqcWtxSiL0a3bjueby9K1MsyOFnKlNl1WSoXOIdE57Qfj6q0/"
    "i1VWJWayyDWj2WioXF2XZiJY0YszOG0u25NWakXtm7PV5doeXGez6EWly50BTUeaJTVaifDcJiuux9z4kE6XKr0Nd1pVyxV1T80k"
    "rsSr5V6gMZl2c8PNrHHsNZfT4nAnV6rpVO22WtdmSz5/GYP9cd0qj2/NXqM7G/Ti1U7k0J6m2+X0gK2IdLHSEsOz9lgZntvrdHIc"
    "43MResOEhO1hwogyna2mLtFtJ1W/pXbTyV6KNOq9s1SPJ6/5NUWllUkyUY5N1KLU75zlYr2c3l/qy2P1GBnQhXT7EFsyF/WsbIq7"
    "4nldGFwrhR57TpTPOSZ2qu4GsX5cnXVLy1hS4WupsrzMxymuzCVv+fBy3BNC1KA1W+w2s3xjO1xPor3xKrUM3BYrKp2j0odqYby4"
    "hG6DYYGNdAbd1KmfUirjTbsdiDUXlfUpsDiuxFY5vrw0cpw0qSTESK6yTcR2i8RmEmIERQiF2On+cBszeTVdOaUYulPa8PtAYaCW"
    "hVCh0Khy9ZYM1sNw15XZS4cOSBWGCy9mfCot5QLxQ/8ymV0GzVH2eIg04ql9XS1ewvlwIRTZrza3Wmwt0JV9vTzdFNeA7baulVu1"
    "0BwUr0wiFOWm8mifiOb6dao1nXREcVC8rErDUPY0kuQc4DqNbOAqTehavHapTlN9cbAZdAMztnE6NeXNsjkO5CK5SPOQqOVHYUWO"
    "9DbbgLBJT1rSoKEAQanEjvbxVXS2LNB9sXE8d7K9xAZ0tU/MytvjqRk7sQslWt0JajyWXUTkWnRRXSgTEVoTJJR8MRYKbcBW0U3v"
    "1H4gkeqsEvUBv6ZHUilXzsZz0jpwXQeU8XlAr3bt2DIw5aRlIzQcTBNdtXeYhK/xU55l11Rb2SqtZBJQzkxapXbHAZfK1Ti6PKzt"
    "9qU+YN+zgrI95juhEFUvVAd8oyI3SuH0bFfkhs34sB0TWv1hub45NJhqu7MqlAPsGS5ZLttsTdrdfnnQUcLx6llkpuNGuX3pgeGu"
    "qIbcbtDFSHi1rBdj+UT4JHbDs44aiHWT9KocGXTOw0VJ7faSXaahVsar7Kkn9QbUUTzKF2nCtcMLtjFiY9ltdM0cp9nkaZDiOb5Z"
    "OO9DyUBirK6Zw7V+jEiNQGoVom+BZLoiFOP8RLkVY/VCahqPXaLXUa0cL2zq+WSaP0bq8dIivQlzLSYkTflCJzDKiuNxKDlNNGvb"
    "bmJ0ii2l0ilfGuUToUtPKFWzuVWMEgr59HnLAsK6ZhluIEcPteMq3UNXGU/zYPuVixD5PH3TRUgj3EYXIcWRGknWhchiuhwFevVq"
    "MXc+BDrD/GVySB7j5RIrQ6dHyeNNjUYXUWalpquTWbFe4da7S3tCq4HotJaKF25HJSVHBwdB5Kr5QSE0ix7k9SwVOqzZTkWOqumy"
    "MJCOkVT0Wq4Ip0S0E08EwHaRrEQHDM2ulEBhv16djjdZvh1kNdRZBdqt+Pg0kUt7kLan5FFnehzzAyasCrewAtDP93rxcCqdZGV2"
    "l5fpQ5jvD/P9Wq98jqeXi300nt4kAqloK6by6+w6m89nueKmJpSvaTpekC6XYydwjFVG61K2l+9uVhsmuTisL6HVKnbsByKH9XDd"
    "WPM35tihlvRiFT0trpsJVQ/k2tleoxYfKJVwJMwGJnK1WtqUq0eqe2gvN4HJbCKpoSUriethls0OstN8oHEZtVZUOJUMN7lZt5jt"
    "zuqhxQDQ/fqiyqVsMkRfZtdZL58epxf7Sb1zbKdDoWR8T+cBLy+t1X5tUWtIab4qMuyKFdrLcbGwCt9GwoZty4VbaRFrFoeHTmOx"
    "3ZZ67WRy0jgqATYc6Y6X1HiaTyRPdK80XshCsnteLwdionGUi6XZ7TIUebkVY5qnrNRb1scTdQ/O6P2QFOsWsuVm9RSlYvvs7hhV"
    "N4fsML8q967nK5iNbGWwKUiT3Zlf5PvXGhCwL0KRukTZM9uLt+lCdpc81PrZWqTAduTLpdJolKul6a6bXW7Smy5sj5dii0U0Fz93"
    "uu3COB1ilVKusxo2e/Uwt+LCRaacS09Yal+RwuCUs6osZ1x1U5i2UgGlUG2GAEoG1XWnvzhJzVyLXo2aydiiAwQEsE7yAL/5AZWm"
    "w4cuW2aWglysXav54owdhIpxNVwXWiWxpOyPlaTUr6eW5XQrN9jIFbY4yHcLxcJQmM5mrVaiFG+UhsV0LTEo83znqqaG3GakFnPF"
    "fS58bebz7XM0z1W2oUSsmrxFS8MYl1+N0+XkISkCLGfBvlxYKpN2TShkC5eiXIoKh4oYyXe2O26W6ITERLYRE2erbHVd3fGBQ17e"
    "J7hbOXXmO6FZNR8bN0Rllmwmx9NZ9xhdy8XkdlGLSVM2mRZijWZudaJmIzoRYRXAX4piPsDFouthkx1ta+UVVR+XLqfrqEJ18nSF"
    "S3cnhwR1LE5aI7nPTFOjI0OnKl2aC6/2iVWB2hbbCTV+ysrL9LjGtdhFJUt1aqFy/dy6jTrKojerH6Virq/k1UihsN/kI/tUp7UZ"
    "haguk2Z4bnuasddzv7ArF4bLhFRIysymBnhLujTqpNhi+MR3qoNUuNNoNc5cLK324kJXuG6qO8CWijs+fRm3ArxYTwPyiVLbQ39T"
    "SnG1YiHUWlxSXHgZW0mxfENJdyhwMuqDg89ayS0Geem8W/fW0YugBmZ0pcNHAqtJYt/IK50dYEHHSKMCDv7yLpTtZzvgqDWLJcvD"
    "TjI+rAUWm/bwfN3VQpNRK1LZ8/n6ctlkRjfmfKMq1JGOgiXJn2vFfa+djse358lMUTh6OwrfosI6mzhNJmz2yqZyt+6gkRO36VlR"
    "Kp6Tnfqstj5WjsP4MR9pSqujzAjdSnbW6/Q66W45UmovFkyxOCifLnJnFLjRxbRc2tTkQGGi5pRuG4iA7Wr0MmgcqPOok6ZTVC+3"
    "bLVuAnuI8bNiu3yo0K1mLJFSimPh1DwlB8eAMOC7LN1pAZroMdLmFqOqzUSTvW3LK/my6Lab2/6GTcq3WrxyuqZyu+yuNcwfW+V9"
    "W7gwXPZElatMrrlaVvprNtW5tobtQ+Rc7VWrO652ig5S42aor9S62W430WksB538uHCt1DZhdjaphVb5xLK6A/QLZL8KOFBsL6fA"
    "ptfYqolNqxWvcaFdaToZFPJx+bSPt5UBX6ovG52OFFsNpX0iG0okWrlRLS6LzCQkLU4n4cQtVtN0/FztLi6AeQ8CUrYS4c7ZxSA6"
    "kQpbIFMCyGe3zqSYmvSy+Woe/pvP5RYFJdwZgQPqrEUvFvtkS4zGzkp8Et2uN9PrMnKehc4cVxivttdLoT47X+qnFuBLS/pWmzZD"
    "y0Gi1N4qwrhTGG5Gq4IUYgr7ZnmRrPRrndJ+o9KNUSFxE7MKNYgoQJpbB07tQ2rfDwNGGcmncsd9bc+n2NCMyveq55YK+NMyJU7B"
    "iUhKjKTubjVOdKXhsNChV3v5SI8XTPPANGpR5jzq9eMdcTYdjal2f8NExosNJRxvy7paah3DyVi4dhicbvzkEmCGswg1jYvKqhEQ"
    "b7vkpkeJgdppUAuIhcOBUodJVjoNmvL41mGAiNcNDOOB5ZpJ7891YdUSS7cWpWT5Y2Al1EcX+brOL1dlMVm9TEv5ihRjDll6qIwG"
    "fDhwvMZu6jJdVkphqjVQF6vItjDkessJwxSjRTGbyxYWoUNTVba126kb5SQ1cmOorDyhe41OvraJNriK/P8zch47DgPZFf0gGmBO"
    "Cy+YJOacV2bOpJjD15s9mIHhhTFe9EZQS+SrV/feo6oiiMl2LAnJO9XGn7gIXzyNB3987TGjGaHhoqrDVOW1+UIvs5VAxQdEpmjl"
    "xVopHbvWKVR71rCxSFdcEsCk3tzQdqKF7vuzGvBNnLqEkD8wH4iKRcKgP1O8fRXqx6e5vvyoFf+9TC5uNRKObkdBGIh7ZLy2WupQ"
    "S/iI+SXsxrIbN/TA6WP1r180BRWDogt1jWIBZsKu2emwrF7T2RDPZQ2KvXHSTE5bLDQwMtOSd+LcoRWBHc7hSDm0FeGotjZTSF8+"
    "8pVJH4ozJGpC9JPpGP9OhnwCZa9pXM1eQ/BTt7TxeeEF2U/qBfFFgsYhVlyik5kBbE9bEu9xBKrUdDEj7A00cidZdgEgHuwBt4Sv"
    "Y7ZgzrfyikgSto62gUSYwVC8qpF6KlwvknvC6MivB6P9ahwuMvYzwNdgffDWA8GJoHl+SUBfAIsO7h3U12T47BGuKO27oWBIJE19"
    "j0gEPtapOHbXm9xU7dFbZm3Ct7ZDqZi30KHvxyLoEEOCEH/xIe+JlJ1USf+eWSaO8bUAi8SK1t9833p4CK1btsWRKnozbkbaEypx"
    "NRrhCcjnYCp2iI2bHF4f2INn4Cb7ocgXXNLesmhZ175PVLX2+c6hQd2ECqC/wsO7QOgNHnN1v9GHgAxK3HpvuSgefmC0O7Ysvyax"
    "ptDRmh+9frwqUn43HTKjq88UrMEZ5bAC0/AcY99m1JaaL1p7U4Vp7rLTE0cP9iL5fNwF7jss01UO42BJ8DA1HrwOL0wmlY9V94DL"
    "sREvC3XKV60la/ky2Nd7BWQeiY2SdajU/W4T29rGF4u+445Q7J2pzq9jcXIk7vyDnj0njCSR3euXN5c4FT247YbzzHe5rpSqq79E"
    "CLH+C+w3New3hHxtGkF+3/Aa9WlNS6P+2dl7SQBULuU3R34ma/gpQ8rdI1n09as1HgY6cWxl33gSEgOfR/8JtUalkfMjQFszBCMM"
    "5GuiIDgTBYMrr1+lgKAn3A3CgPFytSMaAh2brwryo/WM/VrcSy/xQSlrMhlUFnMLoNmw8NmRsUMv30QVGzJLRJeHVQHsGenmlFk7"
    "ywl5F23xx6/ofNs9raNEjjzeGFGajCnB0ST3DPp0LHYlswWXr1KOXONs3o5SkNqVfglNvMyY2cGNzKj3CvOW63YSdUeRalI9s80G"
    "c88z4mbbL8HQXFOB0Gy8RE/M92r6FOu1jQq/hkRYOzMwWtVVHLA/DKPr543vpan2Rx91udHMHyYFTpkZraOVNp3Wg2BibJs5mR11"
    "UuGjRSsNWQK8kffxhOo8qHM69MPJypW5eIR6auNMMSZzCfxnNXlhfgpzG+CMKN3oxPata5xYZUiq7H9GhKptxXPc33avsKF6N0eE"
    "L5NvIvBOHlNJTyER6Wg46SccKKtkGFmuBA7igPClTt1/G1NtB1JQeZQdfxLz/fvlIXPNxZJy5yNvQGnv45ugpA9nM/xkwxq/dFnF"
    "Zdx+JEnU4EuZsOybxT4nQpZi/xU7AY4YWePTMvPx76R0y+9OOFS3Q8xJM1Yuth8ejv6if05P/pHE0walNqBitn0yIO9hUWM8wjoC"
    "u95cI709RrDKDpzkhaqmFPumT3l0EfjGwQacRWSxB1XVJHgolOX1oOh0WXxEn8gmziFlylSGHewylMYceKhSo+NDG/wA159X4R1h"
    "DmmbcehNYbThTvr4jfNIFZzi4QypKEi9UirhhCBLM4yh3CwNxUb6CP2iCKrbe8ZqhsHGBnnWbAKAHiniETpWhAtT2P3W7zDcBBvg"
    "1K8CcbT4kNpiKZbKmt1cO0iZm5wCyPi8N48XKuJdIB7uRirQ1TSqoGdD8c/2LedkgmsIIfG5HHBp0rMj1L0TNGeOtkcCvtKyrro3"
    "o/7eEl32Ez0M0KTC49O/0pdPZdWX5XOwjk8+rffmuAaTG4sWJteYsRWf7e33ej4EcvAXfLrZBZIbnezyHU45G9Vtab+hw00HnB7z"
    "iG3VTXQDfOsl9LfITpXZUpHcEzVzCKWRSIfDfT3Bxb5UwrsQSmgNOXJWzo9w/AYzTTt3NBe7w/j84pip0AJ7NVWw9dep8HsSegJD"
    "d5c+h/e6oa74El9Nj/LSFpIeFAEnRr3SmW5Ae2QQb7tYYhgzyns18mwUcrRGpWOy3c/mKIMN9U7BRLwmLD6QVB0E/uXtoUrS6+2F"
    "8aqicqewFz95AKeTD8uoFDPxC31C9/ocE9PxZkqsdIDSk1n+tAjyzv1G7ZqpBYE7Xx6AP6nP0zRkvEBpcD/wUxKbhOaP51OrA39+"
    "DMM4b5MLIcOX62dIhSP5OfSJViqKirEeFbHTDy+N7e8nKg7Him/Ej8TB7kqFY5xTx57SSKe8Us7RL+K7HSf4+exvokjbCnsuAkA4"
    "Ndb309JGAmDA4kn26tfIzRUwUsM0nCtwIYw4coWnqadDSymycsP3xL6PMHR+ymDRq084+5bzRnOZStWHZOrnbia9GD5Vw4/VS0/G"
    "wit+nq6hyuiC0wSsB95MGcBOzY+NaCHWF4KxNP946BcBYGh6vzowHbZiEBn07bh9vS2rmZVB3v6YbjMAW67xXzYQmCXOdeWcH+nB"
    "gS7urQX3F/EaGpqyKs5WZa9zI21vpVvWnuJjbsoOA5sUQRdtlJ3H/D6c43W98iK9Lcd60347jI6/vYKTxVM6JoRnE+PV69Rbs+y5"
    "AMzWvWtCiIclUbmoL+StgPdeWNVwaCNbwpHmwVUGz4dE8LNWX/TsLCEgqF3nQDh6CgAfdF/Yvw7TCAQF/tHBZYEJjSe5qpOW+0yc"
    "45Dt/AgSGGP3b2jT9kbg/IihfKA3cg5m2VZ6T6hFtp535X3TFe8XK+M4SeoiKY7ksPkgfj5AuLBBsxHZm+PGNMsA5jlFFo7glFzg"
    "CsnM8FnGlnhADIxNsCiONi920Ciux34dJD+8IfAhMDVuYbQwYDs+zwUC6L8W0pA3SjIqA/+vhTSX8+zGaqVG+NHtw/yNXmIhpyEx"
    "kcSbjIiPIMPqX5DOaa5sLiCldII6MRLJwEMUvxZz5HWMUjisynYIvH5ekiM4m0hO3y3IF9sCnoVf0vsL2uRQnDBwckbg7jw5yplB"
    "mjjPve4uyl4OAMnhlxs2WCZVV6NiDyyl8a2+3vgJwIw/2FT3bX8WMS5MT4YMlDZfwzLJPYtzcxDSEXIEiOZAXEUMQo/RaY1+dWi6"
    "GfnTieSWZPZXINwhLkh5IQg656Bzf2E8nnKIBkFjCH9IMFJEt1wvZMpxK4TitKo+6pN24k9jrE0OtRmlNnU+jzob9qYH8vv7gd8m"
    "CxPEJa7vXAMG830proF/CV82goqS6o9FMIt6+Z08VLPsFt9lOoqm2mAJGynZh6DONfUTW7by2l+7o7tg9T71g2pOCMxoHk+yCmNr"
    "2MzSgMaAU1EC6iboUr6flkRUuJ9zNp1JOPo1qy7tmW9xT6VzVZ/8OtV1eV6ACcONfpHI+VyJUECIXTVIinUg5B7J4RxHxSzJud5o"
    "fLvaD4S5AHl1Q0CqYOldwy6sUalcA7kDOLEQSb6ll/obwfwt3sHZuABs1C39YgoBFslhrqDdaoNIuc9lOYMOEb6pPDuuCwcvnJPd"
    "deJrqafS3xCow5inh4FSA18WnrWH46j6L30LXKstYpbWX5rvDyAkca1Ym1bGpxsiPoxKyk+Q/7YkhNTIcWxwuvsX2Udt+RHAWlCn"
    "avy2TV/BRqnJbap06I2VNnAE1IdNyb5E3jgupLgKqtS56luQNm8CCcbMuc8XNxtRo+hTQSOZsdUj9KuI+aHX2tyNyn1IwVZSvKmt"
    "ezfB34cNREj7IpHok2RKh20GNw0ezBQR2Dzd4a/ryBOrqNePTtaJjOpXOPSvet71h1cBGL4fcbV2pJjrnm5kB3ubZ7jNGRCNUIny"
    "0V0F91Bwt0DoKtET46PZuN4ayfSx6l/Gk7VoUHEz92hgX0fYMN/ckx62gF76gQNrNYBQMuqHyGKXboTQbdLHZzoMIYoA7zj/tOGQ"
    "ilcSJqCNAdjAQkctiewOSLRmvjWm7O2++/Cc+qNS+4AlEm4ts3VaHZ4cvtijmfiAl1H4ITx2IK+rlL6AmZjY+MO+8JlPkPbGTxkn"
    "Ky+JZPyykZ9+JMqBcNOXw/m1Sy5unq82K3CxGfQ8d1BXafA3w3cMJnp5asrYup794cI4XNjbMUZIs4KC+2aXVPimLIv6tjl/MOW1"
    "gc/ksWYfxhReRT3f0+cOaK+2Frz73AuMb9b21e7hJqxUKQO55e/negNdzX7uU96lrW6fGkpATIEOEeMusyV9i/UtsJu29zrpPtoG"
    "YGkF2xG4zAvsL7BYmEokCtB5Vg/xfs48QKcgVxooNC0yuM0efVNIDDATA8mfpRjxE21oXsFw+uAFoKoH8NM+EdZjB0xSY1zyOWZK"
    "H539VR8cWVvOGTs5oPafTVsxLDtBI21xHRPtupmbxeqr8zGDUap1sUtm5HYkfkuY1DvnFiizTOMbDZJtsBu30W6ESWFVx3PUv21B"
    "EuaJBQivPpRIseDUVBL56yAZ2zEHPZFjiMbFCbF9CnZBnV+vzd6dxZtGotJpUeuJa4heVPoqxcPe740r3q0WZjXbj6PZRyaJQr/W"
    "IFmwofPV30yVnaPQPEGqdQErpBiV2AHAklcUSqom7bKufxbV+ZbOZTbWrxRDxakO03zZSJPiTVAOaIRK9ZWV76HsfEqdH68InK+q"
    "fhqi60XFbGfSzGMmx60ccWXvKyePwUkxJC4OZ4qW/8G6D7ESRNbHlOhG0Cj90g0gNMwwq9M7OjqfauKn7N6rUoU0bwyYgsr6YosJ"
    "3rVBhol8jt6JgYmz5qk2sFa44YtI0t6eRRsXc2/nz/bng48X+e1rEstreunCjBafjDCBNgoLEE1UpmVL9fWRjUMJM2820MwhE1oL"
    "U5vMdFur0KDEDZMxT8mI+lprj1u+rw2decPSh+SFX02LBfRAiB6DnOg3fJ7+jp8245KIRELXrstPAatET2WF5U3Fdf7AkSI5mZpf"
    "dX8qVghwjzUI3xgEcKqDaynv6MMhlJUQ8f2QQfS5lP6AGY9/MZG/hYYnIDbYdSHbV2HVwKvaf9ax2jJ4J2OEGXUojlW0WgF+RbvD"
    "Gya7hHc0GyPG5cpePHNAAsNo7ZPvpPfi9t5ou4Y1N5gfOVlIpP0PwrE4thXfqubDm4ccgBLebxilXoRPEYk9t/fpy5J3QhUdio5E"
    "+W3wY6LLMcXqLzmeTlDH2zmV3RdZFhKuyy9GcPRW/yr94GAVuCGgG8h7WfgXTmkxr2bFiMuUF4cMkEtj83us537k7V2XrBF6Iu8E"
    "cjUGwUxyRQ/LL4Y8uXMBMOcUfPxO+CdJeX9FblgApftMozL3/K+BEBUArOJPJX/oQ3Qh3OpGCmrNepJcwbAHYHhAfsbPV0v6YY63"
    "8AkcqfVx0qsLI7v4o79dznZfW/3FfIJe7Ud9h9ZkPogSCxqLc272xdRN81xGEnM8GK5uDGTr0uvlNiv6EDpZikQiBukZdD+Jrx17"
    "lydPErO4VNN1mVzNMAmmforyRwRlXmedTz9DJvzgCBKSM1ZUqDrV9CNRv1PYnWdMqLT42MYGfT4RnPy2EcJsog8VDCu1NjKpWQqP"
    "cDbH0nzfpJ6dwZcMjuXIHsiVqFBntBguabOqksspTGOHg39Rsopx0mIlyfKeqdWqn+zPz5tcCfZxHaCuG8Ui+1P1Z5ILeIhie8HF"
    "1FCZrOaz+EGrNn5iLtSSL2Jx9ZDWbi6jikWFEIcESzY3/rjWEdSXnj9kQ7MUinqEtJxwb+nDnH9H1Lv8+6dri4QT+xvgg+tHwCdM"
    "Ow8QrQUchktURVLdGKnehYGq67SUrvYHuNcBqTSmc3hlNV4MRRYnHrJ2eAgl4EyVr2lRLx7q4+Q3aqpDsbEGDzKkBITGVZjqCD0w"
    "BZBXARiz7lNAGrWnZkAOePNW+46TA2N9xBfzm+f0eRw1jIxe06um4aFusLL6OtE8HrUnETPkr3BJUy7T/QJnaAyjgN7NJ+GdKoLz"
    "Q8zxiGhHjqw3j8hWrhRz38FmbJDjLr9yff5OwgXD8YyWqm+k6Yx0N3CCoZl9HAFik4EyqcKqqzFzQULRz6/F5x1uFLDs3x+WQt6G"
    "YO4CE7+uY8Y5nT0jIVWlljI/MGYNZ1NfcXR/HwTkmfHFMqgGARqsak8nSegH1Gl3HtL10pRET36hHyX8teWvuDm1xIcZSp6wETjk"
    "OJ45+qhxzGEkepKA7l6tieijdbne6uUbgvGM3UfRKcgYkmMoofcsVBLW+ICFgcDpw2SqhdXmUIlDg8eMgvdGWAvaF8uEETu4gCXa"
    "j7zI1VEE0eH/ZiMJwb5Y8fu7NOhKTvB3Q+WPxD0j8489Ev/5X//R/ZtNEgP2/zstqq3a3yYJkfF/34fbSrojvy+mM3M792Bylq7U"
    "IdmUFBi+IWT8P3/wk5ZmCi28uM/RIxU/Ym61VpvVhVJuqXJ+kq/Lk9jM9SuR+2SEeinxXwflGwdUi/g0MNoSMxgXWMES+fSWv92S"
    "dWx2hO/9euVsAmJA+dyMEAACfUWRfEJ4WFf/8A67d3NItz3/6r8QEY9mGbqAPG5oiuZiqA00elybGS4gFEzvBHKrGycBMzSPYyHO"
    "q9wNc69aO70nhHiUBz8gqG8EToB1oXNc8Kh2LlAeWCVRszVONdrTWPViRDvJ43md9EDD3H4TPnH0pCs/Xfj1Klh+MEDU7SDZG/gg"
    "c+rtmgmDEFYDKDpcqFE3WH8D9jtjmc9aBCfr6EuJPtGsmgF5fCqOQfEhMurPDev0UuSmNcoUslKeMPvdfQz6ldjEDuejhLTnO5XA"
    "owPgZlOLJScXLMv7HWs5sikCpZEW023zyQSA9Fvpv3gNPWKpYaEPkqVvUYufXTqa0OlF91/xlVRDIY+xm4etGCkQsqYf+g61z1GR"
    "w1OP+FHsn9UDkOXawnDn2W+hiw3mVhDq1+cCTEdxRcQGqtemDA2IeOoUy6Vnqm0nxHHc4ZPiWvblgogzoXtWPlH0srT6VjYwEEr3"
    "yQHKQP8DeMaKTzk5URXzaHy1f1xEDIPMrw5UrGZ5cmIqMckY/4q1n3uu7uZ3xe0YjZKL7xn6wnxsscUlES/WkUKC5tyRH7AxDDet"
    "7lKBrTEsV0w2B/TVKfjHBcz1TCYo8sIDEOUKH69dEJNuWWlIXzYlBbjNiFp9HqOzBfqR/4wKZ2qeGk7yVBiiqcvO2cWnku2OyR2A"
    "c/GISrb+NtPWS+fqqZiPEIlVCgvNRzP9dySwnophEKpEeWoYvpBYA2GH9GeHvV0g1IGTDNCyKcJdmGnYdjRJyjEf5k/pZ2DNkYsD"
    "VUT0hF4TMPFJssgAch57zTIPcpqa92OPGN9RB0frdzcuP8mY/1iFCd08Djt/0SknUYsbGmJ8NaUKZkjMUXmfwUDlI1JMSrVtnkE6"
    "njoKFs8/IruQ09qrwQHdkuwy8MdELgnxvbzLFGPm0/BK/9p4D86Djfk6C5GQl4x0E3UAuWM43UMf/ZCK+uhqXAlRu4nzcZMdZ9qR"
    "TgrUhbwE3SxqGIILkfkSIYTEAxbGSb8MQhCYbF8BPsjdmSEhBzJ7aPmOyCzLxFs0WFrEqV6LjJRKcN+l9fhNG4sWaQETmBsIIAUR"
    "FregY9MqV4gmuMsBDZkul53m3zkuPCPNjU4IwKyf7ruL597jA2JQMo9GM1wal2aUKmtlvnzJaZ3RedrfkulMX+dugIyaFHyAth8x"
    "6lse9Py+HJvlE4hFo51JvhiHposn9HVEN32Et8UoGHaQL/F+nbO3neUHde7DEdLxK1ugJGeHBlD3NdYMhYftPZMuSIcovGLVmcm7"
    "2xsWtd9WFuf6ZXzsyHPVa2F2hgzNQAuhIvDCzYN6SMxWE/S6PSJR/9iJT8Trtg9fUeVGqB6nOFu4NwfSDTuJ4tdJasssdcSXBUHG"
    "S1oDnKG8d0UR72UINU6MYFMgxJktDP+XitBH+Wx5Q8Dkbp05tq3qgwps9YkxNeN+N7u2LCoDqOeQPBPOLrgizIf6hLw1hdZVGP0p"
    "jX6dT29gUQ6roa9RMBFGeyJ/Mhac1Zor66+ef4XwxaFSMYWZvCne5VoZVnjPwLx57mrhbDsu5SX6k7VE5zIlqWoP0wnibUOcqPe8"
    "/5I5nRXU26HpiqdML2YVXnTTKK8rGXxGbZ6BU3NqFyRnSgHX5U6Ccsp3hxLisP8WL/BFqznURtx8SmqtNCs9+L6r5FneTDLTCyfg"
    "+/P623T/RQyNN+DNkjNc5Zf4rSo7nN3CkrxVorz48bGV9mAjGxq+xTQF4SMNnzMQlesXpW4Rd+0gV410E0Ri6KJBvPMi99mQ7g3e"
    "P8bj7Mk57HY+vkx5TOm43grEkzq3OfPlPhIBZ5I5BZkeqJsCYn4IcKURO6HXSr3cMNmObaeMdICw6PkFA0iXBf+uJpU9hJBqu+eJ"
    "UdQQlsP0EqYIxKLE6ZgnjpIMfdXkz869cy3/baGJA/psoGgIMYpz4vBZgryO81hTc6Ov5ZfwSdNs0c8QdK/f5aCTGcOMkbiUklZa"
    "M/V+nVWfM2u0nNvHI3EkR5HMdtjgmrymcLGWIWH9mrp+31Iwia+8XsosYKUXENd1q4Z24z1tqFXHNN0Z2yuHNXcCGThqSThc4Ra6"
    "28Mv5zfIFOKgp4JW0I+bPa9eRpl2tcsvq+lUPtToN5AySFx5Q89eD7ueMXRyRJroqyZHAL4FHnkZGcf9oOHQVef33BBcHXYgIW/R"
    "EmshJaYfmN1jN7ZONbBjmyCmhpeq1kB5E0yeY/KJjZA2joWzpQgE+rP/Ziy/20CrIdW1Nkaus519axnygEepESyJPRxROvLw8Scc"
    "MBfMRV8LEgLZNu3Ty7dQR7B1Lbk+FU/KxbcK9mZw3bBrdY6hBMiiGTq23y85F2UCjl3HWk+o15pBVpp3VNsrD8LXYj94SsY2Z0Mb"
    "DFXAGHCeZPcnAVmeAODelJwQvDEwHYi9z0TTGDCyzFLQjOQZqV7VZ9/DgtPh603Mg/vQEnMxH7E90JLD26gMJdJyO0afTE+5YeLR"
    "TxAs8cnTWJ3kR++9vSDG/k4og4bR4jnb1w3SVjuyX1/zsBtal894dqG3T17ilEzmYJOHalk1EmmcgS3k14fdye1Flf4yfq3F+rkw"
    "WS4GD+BO/1lTF0qLruE/csKzOAna6Y+6j98vBpL8wXfG8M3gG3RCv3A9DzqexGTuPOrZ8wX1aqZUvctZeu7po/S8kPQ5XZmguZhl"
    "HgvKwlvHmDjcECCDrOsvImc0Vt49VkbE5PkmAGslbWdAWKEXgnapCyoE3w8UxUJldJHkJ4YeJRxQJWSFVWhq75Jn0ja2Li7CTr9U"
    "JU2wEQpePO6N5sGfj7KKV1Q5M6QrSkqMU5wCxVCCNpz5XTxPzXBtkitTmGPuQ2Xb71Vh3NMSCP+y/fsaXjQ/L9yPdeY7OnKmvVtO"
    "EKHOvVjwr1x+UPw24oQDa8DVXKPUnane4XixX1Rr5+mTxpwdvwZLbRTo39Mv/106xS/53wMUMzmYBrpPG1LEyJd6Q4kO6c0nbD1N"
    "cLP4/KKm2V+XHcvBdi5C6eV2Qyjic3Yw7eti+yHu6DkQXxRWUzPYLTy/pb4P1lKum+LVkI69ZS86utaZCm+zxck3nN/tpF8hcJjq"
    "DTTmNfXsH7ieWBHn1eorkV4qPqDrXy93fofrDDSpW48+aSkfXoM3B7gVNXRRRWmX2NzPDAUvzQnNJ2XS0JyxgZzfojtg7F3Ic6Fv"
    "cIAr50Dc9Zckc1nxDUlJGh4qTsTjh+DlO5RkCE4BihpUlx5fRzYf2il74EZB1dXSMjVFbh0dHSSX/UPZl4Xg8eR1vCwA936u5/Od"
    "tcNDe4t2asJthOfj7hrk/ba2oku7VOwH6qOSuI6ehRc1zKpaapQFVnHhA6UGnCSi9gnjjWOsMRBsDdLCphthUQG/OHgBARzYe3KE"
    "kMDtm6AdRfFDjUfKK76sX/0xMJg16C8rx1sMkjVWthaFXTdb0d1o67WvFfR7L0vnqSIhCRpN3WwOVZYT69Gux93C08WA6xWMkrva"
    "HCwATOuasp/hMn5KwQr4sPhorwbtKkcL97H5B+0VsStFaQea5mmQa3eUuI177Ot33IavXVbGoamZMI+p+SnTqJB3xYWe2BQfk+Ze"
    "hF7fu0TG9c+MkqX+e4pMG5SVlcdExU18UtrXRIY0N2qp9kXTFMTAx4d/d8U2RxyDV1l5kisX7d++7hWQUIXYmsmMchwepXooLtbl"
    "Md/Vrwz2PPhL8pBDUtNrkXXmsgwAoPuhGz7ls2mJ5+TnuwbfVqymIKhYyjUaYvaOIZKRGbefBU+y03RO+vrI81EpyyFToHvWT5Hp"
    "gofpMCrjn4J71ZPbaHlCPJUIYUzwvdNX3fyDhGoZAGdKidRSV+6JX4eMc58befDXFn2FxHl1FPXC2L6YX9Q5wPoFcCGQMr4Ae7Ui"
    "0g7st+idbTnSbEDtu0M7xxuRg6uzFI4FHImojVf9hnF6dO4sWmMCDmLwW4nLIdafHbIMP1zCFuiQq+4WKIM0szQVuDAbHZd0H8Lg"
    "sg+gj2jz/Ip5UwDd74S4HK0A5tD7BKXxmxCAHr9lqJqt0MdFUjYNA/5+H+SSix5PFYAumGSLYllr1eU46rQsSwD5BRSYJKD31eo+"
    "DoCgDqyBWJ2kEkf729wLk3ySpKr8AKZDn9WfOAFjYj4dI3IVTRyP1OkmnxEybiLPIcnRQQcxyrkO/jFTITcvmLYnf64ZDKu/8geM"
    "SPBJwvJhCbcDkScBjghUURpAQJ+PUnCFI7SUUzHkqSQpylcc9+RxFpACEuafi9Hl36lO+f861VmTbGv/41Rnzb+855DIvOPqxtPn"
    "LmO1UohXoDoANWnMaA+iFjN5C4C/A9kNEc2IT2k7PUhQjHEBbTSUjdOILSuQFF+yoBZIzZp8DsJ7IN6zfY4Py6guc5naylnRAYuR"
    "k7U/6m5vNIV/dE+cstPhk78FAHDMVikDm5YlFgIhk1WX+98CKUHj+LqRVFLpIRg8gSF1Om7+oJwscI0BogFkJ/bHhy7lB7BQD3a7"
    "YN0zVacRuG1PGGkul9vrGgXM9BSK4rQYpOVGtq67IqobjpjlBO623o9TGTECAA+ROgjEozqJ9uU+VMqIBCfmwUf3PaW6f5DFQbRy"
    "gEANjI14hFgtgt/UvPmPf902H8i/aow/iQTnxr3kMyUQdUrUFUma3G8Avx8mS+Is7XNv6jcPPvcbIchzvPJAQyd8ODV3t62JNV+p"
    "gcT9HQDu213zCgUIwzDgJn5rMC49fINapdoXzJIEsnZwmosqsQZkZznb0vlucZ0QW0syUVhrO3ucxSVJsLiDTUrolSkEFwhD5pgs"
    "x8UfPA3PygJm7BupjWtIjZ5+y8ABYEnSLy2aQOsyF8+IhQilNxNbulu99Rc2YusrweNLSuHrr/vV8AQDF3KXG2XD8pIy0pgh4YaW"
    "NlnaQrgCw84D1hyjSpKtc9HWJVkfjseZ6L7cfRAKFbrdxAWgF+0mPvxx5JdkvCz+6D/bT9Ayi74WN6vttpTuZ3kcGqjsBNTt5Lrx"
    "c2Jy7MqOtzX0IPm03xf3KYefyXxMMxk1UuU6CWqXbpFJwbaoJF4humRW0I1ylTsyPcMEStCvmWF86mtcPMkMPuwvni//Y15LM9ld"
    "8vGpyai+1hghPHmD2iabAng6IpUg8L3ZIqTzY2TD73wAneQeTQvFtp9yy/WdWC9/v8IJk8IVXtxHGmcjNn/3lhmPXKXH/AO8Biii"
    "50Nu73ww7YdIaCp0zmpwR4kyxQUGl+dLAm7ahuyL3SYVY2v2Zg3SuetyoCMgkHw4oc3Q5x4VrsQ8dzX21c4FYrq2/qy//hVYmD17"
    "90793Ny+h/GM8FL0XpfSJopIJ4ypUxT3A1lPL/jgyUfjuCQ/zyELHlDng7Ca1Ub35jOXvsp2sRmotHWuHqCpJjlS0tHKs8sxvxrY"
    "rOO4d0+5z+9nsQAfIvpuGbAGTqYfs4oBbhYmInHEY/HnS9pRsr4tDbHRHb50ZD0dhJ96/LELuo+UVX+QFbWNruTDYH6nnOMNGGXu"
    "5kb7UDCB57hmYMYIWxkUUhMnjz+eoGa1v5MLxjnC19F0gEdzcqiQX4iAifDWr0riQpXBBE9ozURB3dO9mQ95XAfyO+JocUv1DeeG"
    "ZfQgeUnKwvJdSB44YSBeP9nq5l6kXCEHK0Q0tq/oXbPGzfzMCRyGPW6lV8vlurZ95GT9XPkoKjU8ELL4ItT5PKBTshg4EtZULycY"
    "Q3CN2HwVFSxgM63OgOegH74usSCQyo/iO6eFrzAhONHBJ/5PHfI75Ncie3obtDnSnUzr+UzgqGTMZpsg+IBIeHSK6zhPQQVg5YXN"
    "EShLaQGT2jkffmU+yOhZimxKCWrXqspkZItw5CypcPOdGcN1ttaEFfvNBDRPQOHPnebqNDt02/I0R8Hi+9lO5TBBAiCOM31gCFo1"
    "ySHIWgKtdinLvXQjQhbLN39b5wccNIU8LGYJsZSTwDCHmVonf6XOHi3Xp0SiO1J5PmsPOcXzEdhfyJKtAPFEFwZcCEndcxfgWZkg"
    "xbgKTrDgRsMLoSiEgLHZJyK6LQfW1HDjE+8AhJxj7RSSnTTtwsFa7YIqQdY9J9QoB7fLRHwtIewoP4lBq2GZuulWwj4XExL4GRmC"
    "iO8+9B6cuCZBFMPV96qzThmXtvwBrOlfixfMv1m86P+fJzzlf57w1FJwRAYSLKkjNdPLyQg59W0bdWK4Iy9bJv3t+ITpNqDpVgfh"
    "GiOtbGRCgZNm4cORRgAw3U/kUSZGw3QneFN4DF2yk5Fda/QO+CuadTcrM6JAmlKWhSSPuz/2174AAyBICogP8SHJ8fZBLpnI9LjN"
    "BqbKg2BwEr8mMQhjKngxhRztoAC0kUQSabI/8GdSv2j4XLi9YuaybpomqxQqNU/FrLzAbsB5rphYYlTx3f+20LCHhj9BwDtlp/fX"
    "xo7uEaoLqHICO8MhEyx25n8nBJZ90uT1jZoLUxU9JuWqcsvjBDCg3E/Sao+l5s2AUraXAlcIrKAKyEhmCQ1Fowe0N2jTBHHwSrS5"
    "v1/jC4i4VFy4ZLUgDPG+0s9G4H50td/ODsy0pylnIFmLvCqGrRYrzLARiAZBL4N9nMO9Gb+t7TPaTEHErrpaf+Wewy5pcPZADMmB"
    "MXLGiw4CuhdTMSUoPmCAfJO89PsyPBo2RfvUCBh+mQ3XN6OpcfdiTAUAEeV2k6fm+jMjI5RYFNdvW4bpa3IYlJE9Jqbkh7WQ3VJ2"
    "2FgT99rz8wwy3Kp7stnCip09+ZeAaOITQfxrW8xhBZaI7vO94gVus2d2FiK4r0zAglioZA1UTLHlWri9tISmmPqYi5PwTXl3/qrS"
    "2dZTPjeQAf766LFEkklAyvTnFgmNb/W6AJzfVbPSIb+9dlChvtlI01VPaRmAbmolaknA3jc3HxnqS0NA0ztft5L4ewYqJ4lnMGw+"
    "3P+yV1pzs1anIkwn5MfDpwiBuqiJyxh7EvvwwftPLNLMJMRmOUROQtTxRQIhER2aXNdZjDR0EQft+vZrg72qidhcrImaFwnUWcRf"
    "YxlqO4uF4OVXskP1bVlNcHK63cNKsr6k4h/j1jYWDX2HbUvZ8YuEPXPigHbYTmHJdZFqt0P27veBC1tB9Nj6YiP6+/H9+GEEHjOH"
    "ZbsfJLgEKl9p9ypuQRYf1ArW0Le38bGxb3B09FIGoSm738vB46+eToyjOWowHGzsbhPf3yJrhGnekk/CKuVG9dZT6pygYxxjyk5f"
    "xHd/sn02FHrrfXEdL+rXxnLLlbizkdkv3IOjLhbqOXG0gP6EpUKbbNPzY9cEcGo5r8xEEPb4s2aKWYUedrL2j//2NrmjV0eYFlV9"
    "wsK7vqJnY0qnsqez61a99PsdhvGMXiV2F3al2tv3e3iwW+UCqsh15R3Nneo+kg/bM3ZR65UOQzWknv7ck2uhdO+DKtTb3R7TYb8K"
    "W/wxwvT025VWrBeB0yu1jbEGvLVmG/cWCsNQJEDBxmIqy5bt4bQYtV6LiUZCq33pXCXYJY4dHCe2O+fqx7IY/tblG8i36Nc8VL0s"
    "3Q2mrPozhF9ImVvdvZpzSdEwta2wYhz2ZO5OS5CdFck6e+Ys3ZuXx62aRdAsCLbFRLopBd/kWe6weJyEQpH5u5sk1TXPhuy1dFYZ"
    "A9f6a2pn9iAP3MC8WPdfZaizTuYAVPc74OkVe1O9IOOLSJZyUH5++OT/av0gBSC/sdNJVd+jlG523zd+7/SWB4ovmsyCyW8YlD6M"
    "Ck/+yLE4k9erSxI6mfhJK9fwALKn73gIqrmSijNGWPWqa9tKMZbKVJUaWC2yutoIF5ILZ0BB3QJZijfOxjIe9zNo1ZFrCzI740/j"
    "FhjWw6zGwh/cSQEZ2o8v/HTgdxce6G8fblQg7P070qYYvzcxCYi8fTOoKBADRBi4GdNcxXluRntQED6a4rclshDEj507SlWgqzjx"
    "v9/BDDSwGaYzA9vJDI34ZEokNgYx8G6Aqm1y5kEe/JIZvGVmbfg76vza2xZiOzxBEkHI7c3dcwSa0qKasMTMdlISzotdttgTKBlo"
    "K2HuK3gnX9sLT/2KO++2+o0aXdAl21qzH/w4M6oPEHcn2oNPIVqGiM/EyQwzCHh8jb6XX/2FkkLyQ1CksGBmdzfjY9VOMv6yWf9s"
    "FMypuAmSqezDqftyWNq1bux0jMpx6Hd/NRZzKpyn0nFOivFcIR4Puh94ylZ4pio6D9MR+ZWfA6K/F8O8kFOchPdmuln8fNmfvCHe"
    "fj1v7TBjOYgYCLoI9Q4f8MeGcHX1u71mjXJAuAuR+zvqJurm9bP/KPI3lE9tWZLGfJbF8pkW3s8gaXP9ITmADi496CcADrKQnMeY"
    "4o/nZ0y1Hw25RcIj0FFvGCF9z1PYBj6NNh8n0PFQx6ja6w2epmwTNI8oRMMnJDH/RpZcgkT7+HuHAxXOar3UMR3tXRKRsHADzRA+"
    "i8xoeR2T6hOuJ68+c6ptafK9nUOJIbItNtgPUYZEkQ/UWUGXaRjdFPJrva1zCg7W3YTLT3vSZFi57iqm/X5fPPYAcVZE+W2+35S9"
    "RU/XDp8R8VxYhu0ah5WqF6Yx2zM4KPXEj3F5fujqg25DJZACv+is2jbm8Io2X2TYla36CbZUleY+/g4Etyn8FLv3BW1Yv7Yxg+7p"
    "0dm4JY4gCQaXrEkXAzohmOJ7YzbEVgLSWvvf0rdgjx/i7CCT7dvvb86fDjBiLLM+X7v5Aa0gMA9LOyv/Wb7Sp0Fp1zNbVGQqj7WM"
    "iXBz3s7hlqWHaoA/J2y0Af2rXn18zdyCw4NwBSsIaemM0vAixlJuQzp+arOa2loX4cGQPbBEWlbvxypXcICg7dXUNVZihWOZf4fU"
    "NlfEh0eDAYDt6Q4ETBsVvxOx+1JurXVNrinxgYs88PXRt0d/xzsUKV/NRwS+EIKv547etmuXPuEOR1LGESZEErWMeo+uPv/kn35+"
    "dM9gPmY0f1u6ixnlzREAxLod/ztnmf1bsFIdgMy+52/1sO+afJwfGHjtTLA/1ImEC0HJXRQE7vp2P2Qg8Bb+vUGYK7ZyF5Uee9U4"
    "ZNxid7nNfMAhYjm1HUzfgBIUEcLKitiVmRKJknoX+zFK4/6oxY2SxQi4WzM/Qzptv1RlWAFjhL+HNjC88SYGdVRmj2NeFE03I/6W"
    "VVI/Osr9+BoVY03uKpvxGtwfNUEiLHMa515u3U+u/sZAN9EplBcNyyABtrEZkwsymz88DO4Nw40H/cS/p4Iis2VHb0MH1fnIJ5Mx"
    "MtszhDE4kIbprGZUoDr3SqmOXmUcVYtx1Cjjs0lrn5OVgRAnPeASl5DpvpHAAWuDpp6Ry1XDVNyTvWNCl5tGQRYnAV/SeL/eD65f"
    "DCZ0RtnrDd8iYynqbaU7szsfIQhx4uf1bZzFSXnPv0zVUP6Anz4xRTwDzSFT3hh/mAOSe/GwRC7ztaueJuvtR6vSTeDbNrvWbC62"
    "/jvmvOzHFPi89WNjXrwhfXieqVYcKPR/k9f2ZMWos1kMpQR+39tJOZNl29GctfUInK3h7cIL+jdbDKZV8ZWBabeuTjXTIx77CY/N"
    "VyL/AArDAPLD2TRUWpLubW/0EjE0sfN1MX8m8+b7xoqljJmmwRXA/KNG0BO2waajsgweB99vIdrAOpHbOHNnPjsYC70zNs1UUkt8"
    "JWf5Eh91NRwvdlQqndcoJuCRE9mDXgkFSYNCiCxJqs8KvuhgYt52ehU9iSjFLWiZWXxy46dFulWIcWyGnRvv72DVfZ8sIyx84QSK"
    "dkM0PC5RKeKxvcyACHOOa/A60akQ6C/V5DylAbvAtLJHatmr0UAtvloUqFimzTOcraSI0vH6BL1xqovhydg7QblfvOI0Ap916Fg7"
    "hgVqmvl0FDz2d4zQcKcxmbR/2So68kZk3mYJU3zXUWZYvibr/OJQVGo1TbGBZ/bN4IcrdDEkzB3jjtwkJS3OoYUgvjStdywklnpe"
    "9gGYKh5vXL8yZs9z0fu1Fn8UtP7+ys9e9yFXlseKSBsqe/Yok6ZqBLJsdYwW1yeByW/qCzKXWKkdcW1NN77uZ2goX8DCvtb6Tcuw"
    "2ifyI7QxONX56imTWOF2N/e70TM5ilk+Pu3tUHrEEuN854Fef9pTUsM6sjv4Y7p2wAbm0zBTKOSlv++ZKnYEmsTaG9oPTRrq8rq4"
    "0srxi03fi0HS9MsJwWt0iRcTRyFrMkcdqswPcDtK3jdGP14oM3xAItKNmpsoWcen31bymnsgOKcr/XYrkDDIO5FDI0ZgJ+B1yUn3"
    "Se32xuvzUkTG3a6zDHflbCkOy1fs6c2BVGfH4+sDExfRKFk++Qudr/e9OX/z0p8uclWCIfHxNfJwBs3X6RJw4Oi/p/YBLhWigcEq"
    "jO83C5VgoLkSn+5PE8LHF6nCwon9frNSQznNJiK8BIaXV9Dw5w6vhHQ20l+zfsf39c2UrtVzH09nuKwrPuQud+bc3oO/wbsydRmR"
    "joUgZtxXonxiJFvo6NpSZfaM5BvxKdDAAXPNIQG3falyP8vF3Ulijy559avEDP+eRw93xKCYKf7mnmDV4ySQ9nPLI47qHHxeN3Rq"
    "3jAgbX2VIsk3mADIdsV7zjIJjtJ1xHbU//wdJ9H5EEbxU05VC46KtIc7l6VVuJdsNgyYLU544v6Yn3uYxx+DF9lH3mp0qLQ10mG0"
    "gh5bFXvFFJiMQ1YbKyRb2d7BjAaYnFlrPinBc3PagHXBpRqey3gOaJ7u9mYfCZT7pZfB1ZqsJurF1CcPQpDRyJyL+Z7em68D5QSD"
    "If48o4ZtaK9cRGiJO+eNPZv52YXkLDaf/KMALUVog0PNQ37FkYeXiiuPLTfcFkUUSun21PUV1O8p7Nx/M3beShIqWxb9IAy0MtFa"
    "FRoPrSk0BV8/9I07EzHWe0Y7XdFAk5lnr1Vkkq30tyzZz+BySXsMOJCp6CqxoB5f3UolAgwZB6D8uh7Qq5X+eSVomdQ3wjcZlM5S"
    "qzVlqIqEeMgiXsFSW+1kpBNcUQ60HaRteXLy3DHWEdzkgXcstiobCYLJGu6fw7a/Hf+cgnLP1Von/Jf5e+1PnZGlFfsLUpGz+rG8"
    "oRsTHonSk0JygmExvbtQ/vl8yx/eLWcCkkRaTa+YZtBuZFjcfr3rVALMbKXATr4REiApiyBWmKJ4ilqMdsG1QtzyvmMIorjovh8A"
    "3S1UtMqMiAki/EQlXNVSuyowjZFYFKHnBHXPoI90kaq3yqUEKgL1/lQXYmghHUTDUCCo3a1+dVbAOrz8+yP2/NlS/PilK/wqRgAK"
    "oRLCa1KetZ4gNwgmuDzJRQm8avebm1wDTXCsBebv+zlFrV894C6j5grGXWpGYxh7hK5ByHtlURpNFA1EYcw27N8YihWOB6kvBxo/"
    "07BpmWbA5gRMyiSZDRsQFzxl6Xasv0WbMknAr9fqb+/wO/IET9uOCCQCYNw5EbIyypYFDkLxyAk9Db0gmRlGjIANzaj77YObk283"
    "a86eS4BPFGj8xwmzGTV0ZY2DIkb1CD34gaHAQRlgcifDDGEMB6MEC6E77ehzxfxwtUdKd8fC97yPSC4wOlLhONuUCCcgOvdTWv3s"
    "OvDIhelvuiBTDQyymYQEkRGRCLQH41DsdCVSF9JNcqQMC3jjvGInwOvLnbqJt2PXj/xY/M0C4eeOI0oe4drpTID3rkqOCCOc9cF/"
    "AJVXjXDPSPt5eA8ECo1QLy3qaoMFVYi3IZmLBRZ6I2lyfzreSj37xfDO/PhPHrdqNGoMcsueAVdUQ+UpzwCVgX63hw0jil+wwlRt"
    "7T3YtvVyLCv0+ksGYkXnpcOIEdtF7jgbpfihxn5c6E/Kfe+MOWYSaOBi1hvqwjqxzOZQCBAGyeNee/S++FNz0Of4lQrpCUITRhEM"
    "OfEP+nsAF6mYKGQ3hrPyyIoUvgbnzV+f6aBKOUF12dMZ+miOl8f9WK2dNzZ3R29tehA1X+U+XU83tMkm0WrHM8nsVP4eDQRbLDat"
    "eCoS+SpOocWhRfUheQHPrAp1EOfKTV5x9PujBuagBcQ2R2fdqh4WNrF3IiCZv8R9xLC3JBl3VLhjQuQNDPSXStmzDFzh50qliiq9"
    "tlafJsDFJHO8Vh489rZAaT47iEmoqTgE/+7Eoy0/pcYY5BdSKob/8WrapgfzQ5bhdtYcDB3xfu+qaJgMhH7LautpCGYncXkt4fAB"
    "V59qLYfBKotSPCasV4/5QHiSLSSeooqpnGwv6pJpsuCUSu4vz1zyC0NSBKTcFDHkvizVi4c1Dun3I8lxxQSaQhiwddUVWtOw01JD"
    "tdqGMvkaR6+nM1vC0rX/2uQVG7jrZXupXUXj4KRp3Sjdri/QY9H32pL2GNfyMaljeR6pC8ExBQKsGwcgTe89IV+kEt6BdU1EPmIC"
    "9gmca30+oKVQISQEhrkCOAaM8GN2wIAb9ap5dxJ4vv8jfWedFDmyXrvZrwZzyJ+8s6U4GjVKwJwyJ9Z3ZuqvLMuR29a3rvj+sYmP"
    "iKZ9hL3j8nWJW4GBUWxm2TqSs5Ofik2J2se+rn4Izmz2KNxGLYVuJl6D5Q8NdBW4Ih8fEaZdoxnpk+NG966WKZQysojz2zQ3qoR0"
    "DZyIg216uuN+fU9tWHHzfsp7qNn9KIZfH8reGW+mBV3KNnGQOA6njhpCflcJ9F4xV5V4ZR781UzAo6kPgGeElGdZaj6CPmdPTt/N"
    "Fq8AKw5Z2NTVY177NH0g6nTHvPAJaPnVmyphrDYyl0EGj/7tQGxXQg9D9RUKf31c/C4e00GovQeaXpzXcEt49TeFABZWJnmuiifS"
    "TFv4atSpNlevKAsH+56/u9/t8vkAjKwAMBaamkNnjHf06SDcEDd2slYa8uOCaluGPspIaAiCG9UwTlF7HYTGfRcWiFDD+PeJqIxe"
    "6/wVK45CUs6ZAF2LKleVqKKlcx0tZmv2KTQ93nh6G4QMOu2bYS2qfuLQleiUY+ltIN5i88nSFSS1etqjonYRaQShntlICbL5WSN/"
    "wOYc7O8RuIA4pXJveqAeJMF98+20rGft7WZsoI1i9efCa+PURRUIwxuKY8uOnnGaHQZeW31Ke915GYLw/PaoYIpBhqI918/YgIzJ"
    "JQUZ6qlTmopECvTPFxI2dwLLlv/m6PidbX7APC+E1//m3botPpHqs2My/DUYVSm8T0xoZkyTLIeHT6GVZbFnSpdXLY3szvHrfwJK"
    "Y49sw1TvyFgYm/ynX3e5AJN3BOhZjvVwnX1UIaN3+CFx0TEdU+tlhuY/UsQ+Acm92IjNc9mrkYnu3zf+Pa1Wd+s3v8i3X05xO4b+"
    "+D1mJ+7PAfQuDzHpi9kPnzjdPgxjX9z8SySkBcoXNJR28NoO8xiWpBx6vMzcPtDjCa2xopXWBkXesT3BhyML12SEIRMb/6bQU3tK"
    "SLBQ1Fzs0xPv7azdgmn6xxJSdYYz4wIrL5Q1cG/IsiRoSuKqm5IONhUDx0q/Whh7nT7fvn4LmmJsmW5JuWpj4S1qKraBjfkpnVLZ"
    "4qEccG8VZUra6h172JvvfUOnKp5PWC7V5g/TfquuUYSgnNLCkYHPrMQK5fD3Oolhs9hzeNUxK79K1IOIX/p1TFRN/+m8Rc5So4bo"
    "/HK1jGJf4UxQRqvzbSuvPqdSppgeaQsMYNrlrO16BkBoWyaHPSaF1wiG0CYKQ9TWbthbCMXOXKxKj3BbGJ8d4xOFQ6QcdbnqFbj5"
    "kPXk/YMDn53cV8Ij4g4DpNzkG3nF7pgkGNsn1VU/xhaGYbXiz6mO5U7fC+M+fJIGRJuq+2suzJnhgPFaXXzAo2jlrvMnsh7o0xJQ"
    "qXMm1l1SqgoB2y4R8mTM8/SxSwFiwrcuDXitUJ+tLK5ZCdKy+SwtMa+YDan8L3pbAJKmyDtpr2x+18hHIWA7RM1bVfGUp9cs/Ncy"
    "INASOlqd8CrYuwHIq3F+2cUTGo4vDZqaBwIOlDVriGitaqhWHs/PfiaHfj3Aq5/l1lj5rgszUNKMsdKoiHYPvCQCO86EVuIv1pS9"
    "Nrz1pf8lh5uW+TgrH2VQFWWkxqJ75KSJvhli2y/w/ND4vh+b71dVa0abBehM74Gv4HaCzx+E5gXEQh75UWMfanZCKyCHiBry59I2"
    "p7EWyR/CkDaulSo5fHNWsxLM7VibvWTyQcq+Og7f/o/HTaNMJLF1Od0d3Y+34X3RLmJcXwFmcc8njjM7KweYGkXl86OIO3ka7j5v"
    "yU5qbE5VC8BNAqb8fCIgAz4gWEtx8JNhPkuFiIK/spJlMSpZQvzpNxWY60cwTHWDoL7CtgYIcNqBTjU5wykajxV7Ek7A/AdcikMO"
    "DWB3q9Py00GxHcb4FbL6Q4d+YuFNAlwcf52224HPqVHFfatvUaQSzsmBd8iNEJ0Q+if03x7lK+kMB0DX4Nyv77IvZGf6g6bi4Hu9"
    "CvrW1AUNzQF8Mzu+JwURkbZFiFKgJsdoJB7VmMThp8Y24enb87hwJ1hmBimtz7ijuPUTx0s2n4Ch/Yofszdq04AExAD/hhyJO3pf"
    "lzqtXvXuheANADQBtO7wS8/9MDKJCPILAJ8jhXWG/V4AmgPxLxtotz1m6Ovh5yJC7RruUgyAnWDTJwfDwsmuyyLWywfkQRDEFKUF"
    "oFUZ9UWlWSAz4E7QiWRw++9v4OIP41B+4GfL8JM/9Hooyr+TFLr/MEmhjb3/apKCZPyzH+emVPvffpzBGWBntG9/qyhLNNj+d0Wl"
    "BBYY+UHtRMgCCvrJIKe0KUUG0U9o/ETvjxGS2AdnBPOie/XT4s5xg9gRzcMYRVKZTVlVpJYvNrsHQETnm7QXBdMDRYh8ujj4thY1"
    "ryWyQ1QGUgdhKnh1ABCFFwDDEQD+IJ3/Diq9WpO8OKgipR4vWcTzJqRCKn6F6DUfvlW96VMUlXfdBfGhr+994bQxRxW+5tKrYw/a"
    "l9ad0MAbVBroQ4Hq7mYKggFaWL67+7sOAC4Jlk/542Xw6GpUd1El+fAARlhvAlSVH89fWFGotAVKMShBmd7NZp7IOHgkMDC6j1Xm"
    "u4dct8PzK6QSonG3Khv4KEBgIl22wzNVc+cwiSry/QRkjhwQeHMRD+Kym/h1jq9wLfOy8nA7D6SCIlI1eAVWJyRSQx/ird4J1d7N"
    "LIF4Jy9mqKkiS1TrS4uYHHk5TVb+qPhDdx7jWDFIYXwXgcNPVf5CxUBKWUhWPzGuUNFfSI4qB0r2FMN5RY5RKulzRFsAxkTiCPIv"
    "ZUBtr6b+jh2uThU5OWbxkU1dIxmfzuxLnGZV4d3ElQBs1uVos1/v4xSGYlNYdAmjxa1GX1/e6431jJ0hwkDMiU9L6SEPWgT3CztX"
    "eZjldkLp2wV952oIDvKF0eFu6qwmwkENEFN/FtHx2suDYm6F3/nSOTFHh5zeusunmDybuV5KVIac11DN8VL82isP2SdykH7iMUv+"
    "DZjdEBb6i0cneQURQDzK4KN0nlJU8sI7G089w/sONcJycmqBPQbubbtFeNLywopdL8AcvIbYz/CZS6H0WhpWVEdDmqqBz0pYls21"
    "WR2WrMj0onYxNhDk+mD3BSD3iFZywP75YL3cBW2YianePPdzDPR8HaD+ExVkjkXzC9d0aHN4JTWjGacL8kUXA0t6NpD9G7fTY4Pz"
    "6zQ8a7b7G7d2mdWMr+TjNrhPH/WLP05dEjpx9IcjUnCNSazfHP6efFQRd5/wgGx/1w4riM27i2SDL7YkOB84qp6hlysA/HtZwIC8"
    "JBQxpB0cYZ5k/N9SIf2WYyrUkr+XcJD+ac2LkEdPTSsPbvllT9WbxcaCr5Tdia/xMqpdTnjjWhjP1gXaj71rtpNc9/y86UWJ57rg"
    "ehc9lf9jBSa86YbhRIq1PpVmBL749jkbX7FjOLfPHBXtZbY+myxtajNZRBhWbhakc0bVQgJz1WeJnah1AC5I3+4WwRPu99AhRPcL"
    "uI6dNSrFsPBLMDjnQuU6sNyI/rFVYKpZ5yxbt57i2BVmihrxvQ9lnBjhr1s3+J3S+lGc0MtiKiPRTpv2PyJRIkBykUa7fk39u8Bi"
    "NW86KTlL2f2neDuAIlpJc+HC92/x5KqEk4J6hlvtIKWwpSTLhSjo5SVRenxSlNIuFalK9pO6g5ttEToU/VdzVRVwwEc1D3BQboer"
    "1EWB8gHvzxc4xnSXl/t8ROB2IQ3zWyLafVEklvNJNaUpeFGM/GJU1gKB/COQwE/DvsDvcJkq/IAcglJiJM3GeQeLJJgYtTBYZP9W"
    "V1Kr4cTH7+Bv/e5wyqXkwm1R1BDA1U177BcZPzFckkuByaIp88oCIWVViAvqojbyeX2+ufUoE3jSHzUo2wUx8ZsBGa+yxzw2gw1B"
    "s17a/FyyzQCL/DVdvaddVHV7DNW67yhRuMgujidodh6uDKxdr6Aox5Cp+XcSDiuOJaMBR49izSKP/CUbqlahahaRK+QUjTD82wOU"
    "YABhnT9cN2FEIaw8RgJ1SPDRxVWlJMhizazJ1jXdoucM6dNh76t3WnM2hEOoWV+m3E033jHL7+AfNsLV8xkEC5HjO9LN7weVWZX9"
    "oLDezSC0No/iBIqLJwp5dYVILjiSWRnFtETS1xHWL4FywIE9YGpX6Z0mucvwWTPTZpB7xXfUwpB0DaZr443s68Q9ZJodCBGYevD1"
    "eIQffQojva7FfexZu+3EKXzSAK8tdf/aUL/euNh8dbjxPk1QlefMUPW3J4RGxZcm8xit0befNq3lb7qkZtE7wWXy3aVa11UilueC"
    "+YsWIC2B8FusdnNLWeXj17JLpCb9uQEdnEUdunSR+QhSA1YvUpWdg2uWnd2bMQv9tZavzoC7p8Hbi9W4OEPdKV1Q5NYSv6irxO69"
    "EmqMrlqqpG82ratwCPv7o/PphNdf/WsYDCNdnjM32tfv34xgNwyI4r+1mZM528wZbxBXlhChQFKRthrry2wbhxYY/+wtURzq+trE"
    "4m81S46giMqCz3Yc0FyAZlDM7nJDYEJaonZ+8E9quL+uV73PRjpSH2PNx28jNQl/OdlGPtUTnnd5H1Z1a3ehHW+9meGnIGBSehuw"
    "K8z5xVumw4VIXxR5fLI774sDhFhJ4A0H0gQVPoNHGOSQnqSB32MjDwOZX+a5O7hB0gH6CBaPwHtu78a0Isauxq+QkiWq7Xfh5Tqk"
    "+HYyDqMmZn2eUsbnin2ElG6H/UpP6vqNr5wDteNVzvgqb+glm8iBCPVolIuOrh4YHz11genWovTLxDRd4hUsri+hi73tNvi8zz7M"
    "ufhvFGs4aKE8eDMZWD3MwRlWg3TGKKzh4jgLZByZEGavJilSF6IHrmWoxpvvj1XaW6Xwu56mRRnJAbzZwDac5YS4RgAm7WWaj8n/"
    "GI0wuwTEzme+AujyfjqWfyElfSoeery2dr9j3TAvyz8GyJnM6Lv4xZMmUyZr0zbesplNIOpHOGCzydwZFHx65Go6t01NeRJZEAMJ"
    "ODyWg6gLdcl/R6sutSezsKUVqPoLUHTU++Kuf7/DvzMtpr3VwmdOyGH5/ZtisKf3PDAhsJWjONXB1tsvnvX3X9XbUlCsS4wMezRT"
    "0R4UY4jv7OtvLvhBMxyXD3r4EpxZ44i0+1/PvR59dvoHeD6X+vceqqdFSIVFjn64J+x5vlTNiz4EJ9dOF7qt7BI+ryqkVcC+fmDL"
    "m9S0DUirdvro9llBlb6tLzOTKagGJw2sQBb9xKm7Ue97sewm9AaHGUda94EeQ+VAogUL4/MtDqTxiPKTeEFttUljY6e4OK2xMI0w"
    "Z0iByqfVJLY5Buo9Td+PMgKCOLhtnqJNwoyTz2LTyOCKf/LyjCpGuDuKZN9dWaW7OxOY0Hpw/wj5Yqveq5aN2vA+PoOmsLXsSnLF"
    "KFbQZpn6HBt1/OHXBTS33pFb6wjuZasF78U3uUaxXfYN76P/gniP3sTqZrM3wly3sKUW2M8OpICuSlaZQczimYMioMkQdimnLDh2"
    "8kIwFMuqxUyQz4JbP07n5CiZB2OYTTlB/ZS9ERnASLu0+RDpIc4v4N6cr/FentXk+JPRg/Bd0aVsT+hMMXTBFtNWNfzyiCeGRIdd"
    "Ltwj48s3NpIIQKA7Sn6EW8vN7QzQoahJp/p9EgrTBmnKIJ6NFemWkYrYaX9S+YOS+sYw8F/Lx7NSe9sZhsE3BGpstKMBU0QJlkhT"
    "o/Jxa9Mh/xjiT2e8HcsL+vG9oRYmiwumZTuWrySxIPmLtgOfFxby8AzaxhnEiestuQ1BKDvwZYTs29uVvhKz5q1epvXyzl/iaZ8D"
    "6+T1qf4IJJnTCghntVEIvuHVZmSBhuMv0hWVkxyhbx2ivgEE6aZdczyVvM2m7EIcSSJ5Xn4z6S9MEcRJVXeK+EA7B4+Bvk34lths"
    "17D1wuzKPFQh/KlH2NJFEFtmWKAjuGp5Fa0lm18869g0h6iZhdm3810kE5BezRgzlQuCPkUaiY+dQNzzb3ncaNyhJuvIJ3q8JdZt"
    "C4lKi1nmsYSFN2pNuDD8ZUBbi1eXCz2b+5/R9fcbwKXA2EbJC8uXa+6O4DPYKRlpz4B0P3R4zHQ/4NnXkPvwmQ3n8T+qKXDeToGu"
    "TwlmTl75e3K2RL7mWdPRkru1FvzC6IoDVO/u4hGE/s5Zmeq5JXgzZIyRCj2PVXZv0o9/y5hg1CY0ohWLblVLWjx0WbAPyecXLeVF"
    "LmHOJN9DNNqc3ZGXh4Y7qIW9WRZ60ZnBdHeUFRBTMAARp0pT2j+nwqaHqyKZ7X65HfaaL7MF0Kd4G6v9HopNGSfahOxxK3JryngZ"
    "55x1hgrfFhSTdGrBYXamuRsfbGAEH0dsQx3Kr7+Kw3lRfsPoJa16ZOCVv28a+TbVETjOx4UL33CQlL9pfjrsSElb+IRpBfvBkamK"
    "lEsvVFnhBHTTlTCnAjz1MeN5yM/Dp6AUtcrOqBb+UfpiNVi5ImmmIiUjOObM/+2MxBZBs5SdH55S7/8kZvLpXW4MOKna9ADvh5CT"
    "JMJ9o5NlGImGOD6J/TWxi0KEOO30D1Va7BZNLkqtzM+5vFsDDgsxg3FOrNo/PeeoAAklff+QdX1SOLD9mRU6PRufHiV5YCiDixn5"
    "wdALXOdkcYIawj+DWdl7sftkTG8cHk0lRn6eeyrsSeclQZWdTuuLynzOVFhxH5sXo0LTMj/2Td155HutJCovj0MB4OHyJk78aHB9"
    "6EF4YNwi4Q89a6WLc9OEfiCbTHRIXEmC+C0x0FVvT+z73LIe8fZGdsh+CkyX06OGQTRoTKL3Pr93L+JTZDtfwocfzLKyFMCdkwwq"
    "C43rHEX/HOAooJXXEodnQ4NGvG5KEIlqJctZFSdeuBZtvxqOUPhDkuSKymq/GcvogcMNJcyrVhbH5azDMBt3MZMjLF+Gqxke33VV"
    "fKun1ozyWnYCI/10l+0YxkTK3Sp+Z8qSfdJNPOp3ppJdPKQ9akuOBjpYi29WILmHF9FDNqRGIHAuWHUNo9mClfejF8eSZLbuIFfM"
    "kfPGzGGcCEr1hb2lTpDy0ROo10js5HDK70/WsuUZDXIxIFdQ7GnrWPJuQEwi4akbTT13RW/kfpsyh7V2JL3P067XqrJ+Mekwv9Wv"
    "xHbhYehz02j+axa/k7i8ueQdiMMqkCoW9uOe0hkEbiQHpILBWVNP/CJaXITmuJCOzbw+yd3xhptWLnQlpug1KyH1to031Jf9ynjE"
    "EPrj0r/MT89uWVA9SuTs721qvyeIAkLV2x3e7MOwUGMl8BZkkbCdVD0mM5SHRzPZGmdjvgX4PFtUa7bLmN+YtUWXx8XLiMlvM8Qs"
    "uBmrcurcit9AWu5yUnDP1T/El+5mivxMeHXzlUadkHtMt5tx1peFqh+Whwe+D3Tn8eqrL+ZLd4xNUutnqn5IDUeM/U08+YztLQ54"
    "rQZvo+7O7AFs4OYI0q22SVQA5LoMuuA8XeIH6TQ3XtjA6shPJvPHIureQUYmimxGLq5uMtALw67xYTT6EXT00E4fFwxMvzjNebOp"
    "JIpgT1yGoIuWzq34BVGd03F5+oxobKbxMiz/fH5k7soexHT0QSO4XXYLlxsB92mxysfriWorctN02NmPS5RN9EJcGeeUk4aVTGwL"
    "0EkG1vbU2LTGxxsLz/IUEVfGRtBBDOI39+eTZvxrRB+7rIytfdafoy4xlEX+LJtu/bJL7yNTx+kEswu/or6CoGVdNYFEGNUIX/x0"
    "bq+01UeRkEq0FQ3ysKXUK+FsgkXcfUcjO0bQuh3v00VmlvqouwJAidl+6DcDK8bsOwEBwSuMRye7bg+EXyac1crKSupvr5BqSjF0"
    "JsJdsKGgG1Y9riUXOHWlm4MdPYRNqMj56MlQd7HlN2PoDWfOGGf3c3/DPnax/lFtzxYuBJDAQIym8PfV9HpqVLLRbKt7SidKKgMq"
    "wwr4iEQtSEWYzDG1iuEcZM0Dhu4ZVauEi8QMtxvwq3PltNJoNeG+C19OtA72iBtdGDTHdbHiJvjQXFm5RtyLtDRxGsLEI8JbBmyB"
    "98eOcUe1L5orfVRFzp/DdjrKIHO0RFncOdqeLwdv3Sfluj8n9X7WirVhqghclT8tPQIvVYEPARuY+dNYFQIC15qB4drc4Bh/47cr"
    "vscP+fkbAUe9G4IkPphgF/UJkot948qgQRjdOlgW7xWTn3/7ABc/fRbaRmWlBEMt+5WLANnrOOwdOjguh1diwDxsT7bhbPid3o6H"
    "hgb/NpKYoqR6TLumQcVz1J5mnhnITRjOmIGBiYHSfXtnQ1DqeJNpVPAwR7qLFaDTCWas5ZnBN38rIwYZ2xqm75e5izQjyELkzqpl"
    "c/IRTgKdAPAUA8JsRNaLTUmS1kmre9nrQaZ/bzuel6au33vIngBcIlWYKCQLmqEhihpTPSFHLUDqTJboPJ4eWjoqZ1Adp+jzBX7h"
    "kkcGXPPWFJrU/NpEyQP5jzVcFhff+xmqfxu+0MlL/3H2ve+lpcxhmZ94Ah3yG2QVCJJ8YnM79xEBeoEwTgO3UgMsPuqGX/3ygQlm"
    "3xx6+9R+Z5vb14b3VWcZaF8SN8XbVlsqfjH5mfcoFhKIGe/YWKg5buSy/ogJk0kxfMUhCFy5zMu2xsH4s1X5+T2TXxe6hRk0oW9o"
    "guRfjXg6utF605eNKBkjvk6LLAUj52HUwe3hVaRKqneKKCTWZkzL53geM9jH9YkKo0GcQ/lnLmkrBw+IGxQCc7OGBUYJbwKVoIip"
    "QH+XP32XVAqy7W3NDfuecJ4AlBIiIm3UGp2V5x0AXac47FKBFt9jVTCKRIIwolfb06GgSu9bYOKiYNDcXUP2sAwlVkoGzQkiNqv4"
    "ZCLzoEb9u2+o8Z9WlTLRf/XARhb+b1XpifQoeAJ7TxtY6n1nlAzNLUZRRP/3oQ2OWPiDII//22dhTEVjIOy9Wq+BXPeqSgDUOc6R"
    "+hiOPIIPaAWRN1uRG28nWX1yBItyAqsKLbIh8ufN0J2UX5AlQCrvhioto29ME+mZXO2zC/ixtHSOhwFK8N4xn0vkYDhODCr0LAIk"
    "LgxPl4lox6Wv39KbKMCPHexdx1GEcEf+2znO2O+MPJ4rNiYS6amLMWMhRFF5ErSBmaA3tQF4lYPQIAqcwUrmJzvWJzAfnYzAHbsJ"
    "TDo2fw2Ps2M3P5ziw9xtZAu/XitkzsPk+9B8BoCAqMKazLqLm9GzAG4GgVTzbOr5kdiqKmMdOEbImNcaRZ8huaGQmT/R8nPph15I"
    "tPdAALzL1w8GCsyzE6HvzWExQY9CM/0dsBRM+zMLSNbC8Rew8JA+ojE1jNAuK+IzCeV0D13TiMJE1FIkS1M0v/JlyVvrianwuOIA"
    "lTH0+y0PSJPo8AntC3k/j5oPNy3zB/fxrxKrB7HyDu2oF5KbdMeLY0OD1sOWr27RiKG2BkrBBUw06HQA9cj3BP330FAEtwy7fh8K"
    "TVevgSa3g74bG+FBuILAWOOKBjNnPylNhqV80HlWQE+gv7NNEO20odd16GTgN83eXsOGgm6OmLPIsxlzEANEN2ekGblBYCjGEh3W"
    "tc0F6hR4nZ4a+6nYnl7UtH/eA8Pa+seVbGNZqXKk9vwpN04MgoWmtxpOpD2PGuJrJbtTcDRE5XFOtb7uWWj+s3mGacEuD/UuSjvC"
    "wQHosC0uQwbGAs6/8ycIDT1BdzBxz5xLC+fpLVb87kCguTvBjdsiT55DF1+25nX8q+kAEazxl59r34kdl6GDPiP47qPJVqSsZC5G"
    "s/2VvcdrMdQh0mJKkV18RvfDsd81DmFGu2GhqlbHQFMDhrb7a+ARBWfMXjOo/YM9C3o9J10Q+rCkb8xwJACLTXbki7VNgOtcgkGs"
    "2RnCOoxGS4pkYai8IsSZtW5FgfU8f7P5FCBSDS+xfk+Zj264zJQz/XLGDeeNVRgqSgk8+mhvVK0+8mGwipJbOtOgMDHWXvdDRs32"
    "LPEG/Y6eYPIN6VKHZ60NPMWvzhobZVz2IgCRv28IxzcR6/KLxptMW23DnxHhswJzixv2IMsa9eB4bTcIpoJn36CSIC93tD/fRFh2"
    "6kQTLt8s9CdyITvD/lma9oVghAWpXmUEkTaTlHl/Xn03Eh9vLiVhgAyOMA2PD40CHKiADUPrY0ti7Vz/gvSpScpDQZ15feOzSfrr"
    "byykGsPB7nucp6m9L1VF2GDrLA7xv1sZM6qZUs0QPYVVb2ULjPxl+Tpm79YYav9tCI7vIRQbD3JaZad1WIZzWbazw/GwzeitOh+l"
    "UPYyie3y/JTW+MbVjVpBp8T9dfotk8OlnvgJrX4vtkTqb4FZC+1zHp5KXuM7N2wMmVnJhrVSWlESp+AKD/iCI1ZlmiehLq4xvROz"
    "CjTjb7V7LpaWf8ZiF1mSYYB82T0wvjVA5Z0R5jPxAoXMtnRC+4zpW+oEHHR7B5AQ50arfKU+Qs9wn39WtJMg4hrlThE1S6CW0rno"
    "Z+wfQBi4Phul5zzf6xX670v2SXpzW8AlfbM+jHZoycti2fFZAa1Eyi7Ss7u4dlVTx9ii8x499x8BtUSSVoNXPQG5LnNHDdhO0K3A"
    "cMorNukmRTou3BGBp0pPp5nWI+7x0boHA/NcroHEsYGW56Th92XIoypZjx0akIAABSoW6NJSCqiQ3b2ifEayxTjKaOy2hpdocZzQ"
    "xf0Bl713fxNM0E+hsVhI7kkeB3oKRoLDCLgWpKVsurdi50l/gkenMLxywKgHW+ha87m0hGumTgdMY5qS71Kafr70db1X72rIs0Hx"
    "kE2uRm9qRB1jGsyk4pqAX5dBJYYnscpeG5zh3MLoh9k+kS5G45os/idwp3YKQLt6zC4Fj3FPjimNiR/bAyA+H9+PMpNnrvFlptXu"
    "gFdaaioo8EkZXBGiQYcGdrFqzDXl1YEkX/th5YiT6e+HQDYfiMWHmj7RVynXBnOokCUrl4EmFvoEMxJBSxCpQMtEFM5TQy/InvfB"
    "vJu/Tg6aEjHzZo1s5G/UNvpDdbO9ufy96TSQ0M76A3JmJJOfAXtQecjWW6rnsbhqjFJZF+1vcHWWyZqZMozMQrui1uwqc+vsYDvj"
    "z5cps57aBSiLT812oK++A68ZmPBZFdZDPAqTKGzPMNx8bIfQQZ9tzEwE84mmnTiQhk776bcA3JzDH54lHqRDN3/Bt9Zz9LK9d6hS"
    "lMDINSfkUr4Wym8l0AXaEd5/e1OzBtKqTb/QUWJP5QTpbfuGdLSO+jmMagPRCY59y/DFHkrzArYV1P/Vep1ASF+Fp7uOc9mWZsZg"
    "3BzY/LSfK2h0OEtjnuSQgnNwL4pzV2dG9pgBPiaSQ+WA+07tKuroDxSSNdkMyA6nOOaBsNnuv+L4Q9fOh/VrYoT6637AWfElh6Jz"
    "hQ8fxzA5ys+F1+WS+BDnhegI1WH9gVOZpv+eIe8giVbfQlQaBOsdpT1r5RGang/SszGIkqsC2UnObftdgLmGtKL7qOl+/3PtJZ12"
    "ai06YuQ/zR8ZU1AmAg/Dz6qA2BBt8NFotGnN8hFvcgQ7F1uUWXv4gfTnh/F+IU8F69e2gMZPc2c9DqoF96SQ47R7ZVKdmfmncWGK"
    "IqF9u0NacL4Mx57Yl/vCyfYGcc2zr9Opcf4W5cGN0eAoyHly6bdeP3Fh9MxHPdZs54YCV/FncWe7lJPYfVM2jj+cyku1YpR3arZ3"
    "vmTAL/g4lOa/5aVgHEXog1cMsrnskLV6i7cU3RDrxtRmje7YiXI7pdsefXia0WW/ZgoFXZt1pjDXYGvOaUi6HK+kNtGv/dym99GK"
    "BbN8x1UtORAiZh+xfImu7W/7YgolXAinkJ3ZWRO5y+o7EWDrKDUTMy8FeXuJJZr8XSewGQtxMAFMAy0rm+JZn57P87eHU8uofHQJ"
    "dSk+YggY+kR14m/p2AGgiCsgL9oKyoHtf7Bacy4lpJBNnthnjuVOSkWOXDYkzYlzn8yqB8hjumq1rA+WXiiZnZJKCGRth0wj94Df"
    "FDt2NSuKUl7h2sjxrPYAs7DUSWAzNeTNywKGInCSuFzhyDOos4IGYtY+gBL2S2iMatmfi0wyotZ4cBK01ENL0Qb0iPlJ8TSPXZex"
    "RJf3qoLKQxq2qmRnO99yH65GTvHGvK3NmRqsw7cEGLF/okC6sE9mBTtiutfOR9Q+tm+9bFye+a0vYFnykzyuDurBWSSZMZq9FY1L"
    "ozhi/XMJra83QmamqJC7cpa58+PgVxZVUbJMa/jgxNsG7+1lVYZvrLhcSpEVk1xKZ7eUiOrpmdjed9tT+258IueNQlZHGFT7/kBy"
    "ah4aPNCV938a8nVD/pov5QRC/eRFdLUZFvLddZjCxbyraoeoSdALcD+yCl1i1KOuUO7lA7O7PWq/3/JXy8NOEovKbUfkajdtCERU"
    "DHtjxADM9w9LOm/d+9Xs62TmglejqngvYDl7QKcrPde1k0BkWozzMWsQs9VsbX/o2tA3sODYi83pY0TankQ53e0f8To1JLXnQGFY"
    "K0K2HhNDzWQxLaBgPvJBiIpqgFiLTHVfg/RZipV5v74vcbLJpMlPNBcdl8xU8nMocPApM4VSiAz6xNKblrHiMLJWxlNgl2k96NXC"
    "TNv2gR/tIZG7n0Djc2m9d6CWx80oXM8LqikmQ+REl/kMZpPHgEfu+8lHGcdXLyffO41iVz2d2XP87doXWPSoBkQ2B5mfEWso+Laa"
    "PqMUWlajZyr/cujJCWAbBSPD26R+vQyFCbZ3D/p2hV+9VhGOpxbxyE5R6F/xUvgqbOCQVCvD3mCD5L9svMLV+Bs6czhbwdzaeb8/"
    "LqJf3aUxx7lrlVnIXzkFSXWyIZ21Z3qPtzJcyXr00aN+K1Drl5c6WRubyre9N/i2DWBUxMp35c3xThw1Mx+FM2peIb2pMpyXsWIY"
    "C4A70kJbI+9IYWr+wKY6eK6OWrqNP26IZ6R954Ti7RCP+0aw2Ns5+futVAedLdnoFT9CjK56x48O72Lpayd8LwBF8hNJtyyJr9bb"
    "7/OLZFKZ5z0Y8EOnNGoOqEWC8yPzFHLTgo4QTeGUWahRg8Nuymz6BLdVFDHu5br7lbIaMtKJUSgczsIB+N7BE5TrTmPdj0if12XF"
    "A+kiq+K/YsasMMgFr4/yEYCamH/l86Sy8ro5fH8Ft1E+gXa4qAN8DDbm4HrEv1n1t99H025UhVVmg7VmPV/0JNCFnQ85dv4GiHqF"
    "42CEJwcOObLGJY6DySsyd+pC4T0wD0qL8Zh3cCW3CQ0bw8f7jCapKYmqH7GjTti7nAlbEfMr+gRRVCifW0Px6RmVAdRtwF6jCYGb"
    "ewzp4KygRroY6efXSEQSeWblwpCnmDYJbHaQOBqSq8dLmGkKAXL2mUzJ8xCv+VyhhojZXAj9MQs1EXAYVW23pDE/U+1zGKZiMMMH"
    "9DTNfyLXfZnzIzXFZ1MPwDtAi7EfYPcDbkWss3xKhYPhWmHGG1RT6o4z+Mp3xPMggwPncqKebI5QsKl3d0SQ+9dMHMMcxmFWuzl7"
    "fY5WdOAQFQROw+fQDhDLFWc+WiP9mYKcPmcL8qKRXPhS8Cu+hqBCW/v55gsGh41XcRtqVSXX3JfHLNgXKkM7m5z0to6AGwEAZr0Z"
    "8qidlJkyvWEKHhZmo6torO5fi6NLslr3o8AJgK2qyjDfWINEVPsc1myA+Rf7Bsf9QN/uQMjG/3HyssUdEw1ta5DDfn715y4BPmi/"
    "NEiea09TkPMKDyV3BWjBnWTa4LUMF2MOv3mYkmHKi4r+BTpJAlflDcpGfIS8PTHAilHl05Ew1cQHuGy7/huGKuz256GOEgTH07rW"
    "BGmVlkLc0no9/wFCms4LYUnGoIRHlAH4ELVKHrt/JEkZgEjT1WvW6XJuHmUBj38UAIFjsIIN9N9cFhu8fe3fB2PY2xyMwFH/78GY"
    "MX9klTPArzs+N3ZefDy8vxkh3t2xt4DXTKaxyK/Cvet1LiYnP9HO/rQVQDEqAEGl8CVfAm9bDKmBrj1aKPcCvc4FrLWyVYGLpSTp"
    "AQkxkeziGoBCP5pjnDIQNOL8uYzI/FrmyoLNWjGxDnHh5aJphZzHYChrPaHSWP1K8G9+44fxhWyZXu/G11mYvm/z6fNX3o5dRilo"
    "hrlBkr+ScUV7F4c5ynoN4kvTnOdhBV4KRn3on6n5uL5j4/VBKg/z0OYa+PkDUtE2Y06iZ1mJncTznimKdNhUDaPOjdCHhXHA644l"
    "EdhXUIjJyjIb7RkGe1jRXPXCX9PRXgSHgtAh99sDolpe9jvZOdgcdNM3WkP5ev6R7CcYm7/jixsaf2TYnFYcoIOneTGoMt9Sy4bE"
    "sXK+R5DJo6j5gH8+pg7BTNVGItzvMQbklcLGGm5i4+1CgP8skxSYYXzOypdO8PDIXYeNBOv42wGyBp/bd7OySSQj3F2Nj8L0jILL"
    "+WcvzpEJcA/vmLn5DdTFxrF4/R6YaSciIlQCJCXYP4C7aGEcVCouIX8fYoG/kfE61VMWuG7h1cfgvvzLq6KA7lGMlGMO/EKLE7+c"
    "BQXIJTG5UNnezrgS5Oi54KHOF1e5sF+HzgknyF9r5CclGyj1E/UORHo3OD3MBxJrtZ5vcUtdzWoxYTSk5I0TRalzxAmwfAgKZDeD"
    "EpysF9bmr7Zm1N/nFrhlVLJVVMQUHs0wQhXUFB/5QTPH+BKe9ND2SEzZvZXM63bk+QLUo7ASOpORuNu61FMEBvgcHyk4DDoDryHb"
    "qXlU0pAQIhIt0ATdakFhzgewGm/jO7zLty8E1ynaCH85QmizWBTI/Dl5BD58gCd7b996aLulzjbjh1tnMldae2XLr3sQOenLaz6t"
    "+ZdL9RK7/po5dDio3Y7vzCtCAAME0pyZlNhwZp6bE0PZjbNFj6FoajoVp461x6F1i6bfAdmh58HJOGgV8KyBbybyLnmjOTFn3Ks2"
    "SKOpgf75ss+T4+t6Q72/+ABiVaQy5pNNn53B3T3+yMgZ3QD9oIP1JI28/EqUs2MrHIu3n6vbEw2YkKgmOEaLCwKWGi5cjxeO8p2+"
    "aqTEBRoBekGbYbqbWRbxcGswECNfHYrdzWuOZzW/skLZvLvK+Yi3wHDaby6O7Zm+w92jhgxPaDwZAN3OC5Rzpeb2zMvaguyERNJX"
    "hoq94I1OfG3Odual2qR2dtrE073shsQ5BghRF4S/6yeTILSy0+9zKfoTWIFDbbRbAylCkqcA2QjWnVkio1UuMSej4MhsReH9nUd6"
    "65dIfVLYj8c1xwM4/AYhFOoe20yGtfZdBIire3ZkBqlgdNeM+ym+DfztGLfHgDruOECqXrL5aDtyTDtRbWD2GyqqtmaKdFCD6LAY"
    "2OrhKNvcv6o0yUCanpMaBCEW9HfBY7w+sQpbTqPfNyWi68mPpXYDfSJ1MSflQ+4EXoykT6+ugoQsdRl6lAg2wfUpeYGXmoyxPBh8"
    "EfDOI4icZYa3k7kvDsk2VYiqhdgP04sD6J+ALt1Pgs7xN16jTRgnrL6xEnGUpUBXHCyl8tV19GC/T8JF6HVJ3mj1VUP9swbFfOyr"
    "JiYj+Q4JSgrkCCNWn+UEtIT7L/JnOhG2ajk4oS4QTRq1EEiAn5Hq6Kk5zlxbT0zbYQmfwfWrwuMwPgQCmEPxhT6L8BNCKzw+UW9E"
    "J/gbsoPq55dZ1/PlKPJZno2vxE/53HJ9hp1P6rsJEuFnIVuqh5MElS3tCFSOtpw2mIshFraGMonh60xMP00NKUSNYqUYG8XFmnmx"
    "3hyPkTmHQHp4mPztjpxlKp084O+Gqpxvi2FW/Q01PAAIKv/OAbwnBDr78s9vP0Zgb7DEsvrSotfRKMbF2Fmfs3SywcNtR+ncaBvB"
    "xKGH00FAnqBcRsgLBbiPsxyMpWTj9DDV/zD2HTuyM8l6D0QB9G5J732RRXIleu99Pb3Y/1xJkBZ3poGz6gOCGRnxmU5mRCqvZpPd"
    "4wJmDZ84u9nQyCvFSRoXdLuGjQb/rb+Pskhk7s7X6IamyZj2QX4OC8vaPLCU8yh0rIz5x1NxxRFQb2OnAzV0ccIpSbb2+DdlZ/Al"
    "25+3AGcmYvrq5tRnSWBAx3iVZ3Uluu6BR8cKD2mPKmUqvWkknW3viKV22X7tAEWpdREq/61Du0LE4SMu6M5+tW4RskgxWD1iVlCS"
    "H1pO1uwL5V1nc1MVjyjjeLIkJ9mCQb/jlsnXZ6/igLea+S5WKpXQvGzmL6lDNERP3XUbjN6O052FhnEM1wfOmvzeOIlWWGGln0yz"
    "ByiX7L+JJQGgt4hXDRzP/WqvGo8vKH/vXSwvsH8t0ZUwhv/F6Uls2V/LYuPv3HtmpQme1a7AGJUtSl9PtjmZKKcmjawVGG8/AMav"
    "V6KZ4Twd92h+RHLlYhliGtEHiFSuJ51veJxCMMxaoTUCFDGPoVBUIk9v+I+zuDJOIhIGdBAKKj+OiFBgYj40OlC5m0nOaSt7X9z7"
    "PEsWKZa9lS/5lwf4LZtIq+LpxXUJMumv0eterJ9s0osYQ2Afqtfq4VCn5X2ZPd1FNZhlHr4xRmT48lP+HquTpnfBmCPJJBpMYPWx"
    "5OtKLt/VfZ8QyUlQMJUN68lz72vMmt8kn+KHfvaJaxRHjsRcNqGroon2CLePeQDyTwufXCi0/GSXuc0JT6jv7g7JjpYOa/SwEZzf"
    "d467sA58c0jGpA3nQHjQypxvCX5hsuBIDi8H43BZya406hOpvH0hW8llPsZovoB/SwL9YtUNwdivmg1INuOdL0+i/EQQSZX9w36+"
    "Fim0k3RyJFoiIRId1z47RpJzH2suPu5YphaCFyHSUyqJsVT1z3R7i369mikqpGaiubSQJd+b7yv1bfb9WHbySbAqzIo3kcGmlHnd"
    "evenZseCuw4Xx3J5ltw7bdOe7GU1H7NpyqXv6SWHYKnAB1XC8HIrmHJRjv7JS5JoLrA85kcFjbDjB9YSUrZxUVK3Us3eJY3BdKcf"
    "mQLyUL9qV6dBRSPNWgWFHy5fMFbYL/y0G2Nes2TlX33+P/+H+W8OzyvmP7vtyEHmfzdPEvwZnRctyAunv3/aMf/vf+2ApKm3Iwu5"
    "LFNd4rbZueevEUnQuHO4FByR7Q4P+bk/hlF0/00urwIh7sbQru5Q0IxOtMkGUs1NxhXZS6EGVzV7KV+6Lz7LcXSWB1voINZLADXE"
    "pDymW1fu2wbFMLoDxnXqQHXFfl82sZ6TFcAUwBjIn7Fb0fx19GBhz6/pXoB4d7YjAsQfSaAV1d4TCZDRFqYtjjSXBK1nv44gymKr"
    "Y5laNTlMzsZ7T9Zw1I/AQqfnPQVdduzayHP6Z1nd8yZsjEelH0BptwGbeeJ36TTZls7gdq58QZND6aN3J1+u+enXUmd4mSPubmHV"
    "RlAVKW+ZIW8Bo7tAPhAVox8DiJlBJFm6utl018UL585bEMF4MamI1cyL7uNQnr++r8ZAHonC4kCnPvNa/gKIxH9IZLJNxQqszmnR"
    "HkbR4Bu7ymJJKiFuxvdvUF1O7bWmfE5q3bTbjQ49YdqPTiD+ZUbyd4H6SSiitnsFy4/e1iqiCrB6N14BJTWC6Pooggj/4sW8zgif"
    "YWiQMB+lVllhXZ5Ew3YrdAeLdc4nItTft+K+lmksSnKOdcd9aNgkQ3n1uUxjGDHxmGpVxGfJNYGyqvlnSibJaGI8JcmxbGCghqL3"
    "6QEJRKOslGyMkd69TWAi5btNcnLsKb9d2WDY8SJfMs3Ek7JMQg3jt7+qU4RMYEKYjApuBRQzEBGS2WMZ+GV8TjuVjCd4DM1P7STG"
    "oFjiT0Ce/CR3N69VAUcw3/QeoTbrLxr2hF3TJ+Wmsl4lzHm8w6rGPc8/2tjfPpPF4d/gnAOXSjL8uqZZePPFXqu3bINLaYJo+WxN"
    "cnVV4OiklNt+EVmQMiuPiOUKkSPSOow5ZX7lsvKjyvnUVCjdu7VvZYZLvTInhZ1OphLeQjhr0EJ8rge1A6WflFowuqsvzjUxQpE6"
    "aL+kodCyiZEQvjg/F97RWL4cENfPdc9FLNDhuqlZTZc1o/xdrStSZePDPS7vOPV2UerpJ4QLxNeDRJGevLefhgw/U5A/O+jpdXn5"
    "NrtY9avthL8sBwcij3UJ+pAetKE4Ek74V3EcXBkLue0WQ1FiGItWIKCoMyECAQn9pbsIcDhElLnV+saARt3pL/bK0J0oiIjFH9+/"
    "4/DzmgdYLcRtVX8cCvJ6nVvyWVoWLW9Si3H4QA/V8z0f92VIbHoFVYvLbHz1wHq49AVaz348wqW4zWNLXNApxWIiHB1rV+4jXT96"
    "uNICYvJb6oGOWOIHKTnkIufcBNL9w8cz4oE1bgNe0Jga8A01ZUtMfUbvGqgmxhyRW8OGZL4683dOiwx4z7QgK6vyh00/3E0URtSC"
    "z5EvTnqyOezYEA96bUkv8KJQ/jFSv+o1iNT1rTID02swbzBTKaPM7YAuJPfxqZw0EQeBwGM4zJIrS0icgQth2Sr2gz3SJ9/Qm+u7"
    "z2SIQC0POOkyH2KeYGlSZKgU6XJQrTdNnbOiE9j8en17IUVvi55EEPfWrNhpM+s0JOe9qeM9bznqlVcGvbAB1gQy6Gle8K1eKqWx"
    "x2h4BfhyhuF84vxoF7aOVBZrYAfX2/LtT7UKfp2ChYxxEnfqBQZxMWJKDM+gq13Kp9LHMQW158cJslsf2uA6tLgfB2LF0/H2d/7y"
    "Cc6xNP7QNJoYCUVs1dY5j3JUmXtYFpi8qXL0oRWKMUy0LchRwK+YiVfKYQi1YZcVVo+5xUv80GUXFuvgVD68jnzaDLSkrqI0uDDF"
    "CubPulhhftVhSb16GUR4MbBhz5CbBAsYFAMKfvoU9iVTa97+mtPRwYVSdKRPLHVTxa/169XBX28kmTDpBGPSeDAc+6ze5iMxChPz"
    "b4JXNBkQ+cOpN51eaEroKsZTKlPs08ud6O7eWDDHU2pMBfVa8emra5aJFZ3B0VAvdTutefhWpWbkh3m849nsfV4lJw7e3MpHUq6F"
    "3P0kA00L0PL7rhZbqbqdTbPoogsAiJVUk2uSGzz3d40sUfc/JsobiJoO/OWOpnJWK6/CK7EUmnvIYPDzWJvfyneoBGjLoO/7LjGN"
    "D/zpJT+ZZBxvMNjFB7eE+6OZLmcV5ys7EkmZkLtDkQFIzbzbx7pOfcwyE2MNVCFtjKYgqP31G3XlkXGMmx01M7r1y/oVEJyqo28R"
    "nDMxxv/u4k/Fgp3Kz3E4aO300wa8ARSq2p4zTCTCt74f7k55uFa7jkftHrfJVNo0D5wgyYUexRtL8EjxgTskkj/1HjV/qmi5QAWI"
    "byxk75yE8MEudKq8Uh8wfCFYSK+jR3gNncwvxguZP73fIleXDEXwafHWUldgMnNFI0PDbX7zgQdRplpMI8o6JUDPJTKF8fDiu9re"
    "69WppAxHTCFK6tRsIvjvQzOdSrboQr6Rj0zcQMiX99lSRGJ35vzWewhhL/6zHgqWWtzsGWzkqBZo8eCd5Ms1komErhgsyuKI03dU"
    "SULWHCMTMtYyJKCnQ8YRQ8G6wc7ez310fqOKUoFF0tAqkNd+S6JIhye+NMITio3EYikpth7Rfq8DuzZmNqcrqO8gdqmYYtfpepVL"
    "+dpl4XkRxIzIWAL8sTOZ7fqkuBq06a+y2R6PB/Yi1jr5NoYniUC+MmMCx4h1GGUZv7ojSlJEHxkzezAWftHFTKTgUrvPyb3l0By3"
    "zxgoJ7LJOtWGGTr7dIIo6pac8KvNpTv4/qtonfXb2Gp24IaoSs76YlIGuv3e5Fkbhpa6spwFrhZoI/kgFvwhvFRfvF5/YujMYTJU"
    "Sm+XMEAAjSu+VDcbMi7sjDzVWl+yAfHNr4xXcJpuKx2rmjHKu+ShRcRq/nYJ/WVncx+Q5HF2ceD7JJiZaehTdluABiY3K8rVKXLV"
    "DH+Mp42re5rJKKPm626VgpqYSxTbmgktjYInUbimAeDpaBMcHCkCZ31SAByNBUPMb7YdVgFN5WxXkZ0hDz7Gdg0s304s6s/wdx2H"
    "wuvqC8/z6OlFhWDUJvWfPnCtR35hYx5gDGzGqb94Pg8JbyzgiTVgp4jRmYvM+JFPrlgtw3m8I29OpAtRVakJLrg2wcMfN4iIRm/l"
    "M3jSqz+1GE1q7DuI3e8WKNKcWL5/fMGaGIqJNtwy2t36Cbe0Tgv6yplaLwfXpj6KIoytyA9cTcmRjI+YppFPkd+wYOPXMFjabhd9"
    "glvt8h05UZASzxL7ewsL6gdTA7/YemXn98snFW0uMwgvgj213bcQTuwED+N+DCHEi1tJSP2b8sLlvE7e4UPuQyCJw+ue/DjLR4jL"
    "lmkxnPikYBCmmQI5n6OfaDH/yCD7gb9Gw24N7aUgEgULBSvJ3cToULDd8to6R8x9oBQuWm5VdXn80tEkDeKXJA+70z+4HZsjISlh"
    "t2Jp7DpzbANyiZOvpnTVai6C+x7aNDF+Yvt6ctr+BEMuherxIez+yuPfQQ/X58DtRiVF9ITe6FN985roW4YxZPuhOr4G6Ybb4KyG"
    "xRts/WxzrDOpwgqJ3/B3dBLDbT5FEN58XaRLfeuifJB1AC3xQ5T+VWgpRlnfMuXhqOWyWEwq4/5m4NKI5sjrJ0W6t8pzhgQnE1tM"
    "gDXSNbl7P4llhQY1aJzvRch4N7vefmB4ywmGZkQG82WK/ucK951GieXKzGmJlgxXddhA4UVQHCbZkezxRcTqpveSjxMNRLuCRaZI"
    "mo79ln7mTNquS1O6tBtxucYmCKWltXBOP35HYWo7aeu0+0pi1vrNVumHEccQtdKcEOapGazHxFOBK5tewiocU7obFCvHlbrEXuHZ"
    "DIRVdYC+CzchvZb1VjibzwH0m6nlqV/wvfNn5TcVI/tCM7RYoENJ3ZPe3VjbARudRbjMmEkEWzeoa/j2F2qFz9lMUuB54zGdKvUd"
    "PXS6VXfXNhb4hrMlgLfzHJ359Dc0pm+1uXX51FksI0VckHvJi6x2hb2ZMGMuVZgK/Jbf34h74SKpbY3eMmzHqAm2/G8QhLW+Oorv"
    "XA4s/czx6GYufkvFEiUuVGPgba7jaqib9w3l+aBmfZUqeJ4fnMN44+vU0CiE5WGL0OgGthfXPYyMuymAUBz0+hNGr3gYwVYk+xZn"
    "lQMOaux1jwaXhUDIPLpcxbqGrzpo7Gu0pTutBT34hroTq1+Sd44ARB43T9vKADt5tt3v9eZ4R5Y0xu9G5HChbq3eLvbAxyypWl2K"
    "yx/4Vg4gnRxdv9FpnE7Er0LMJkg4fzdqyLgIiz0lqiCafdSYq4dhZk//Ab1vfELuCw13xPP2cHz9yJxDP16/JwWDyStUcDHj1+eV"
    "b1zTi4hrtDbBQCkF0FybLflq42gwzAJjvdJnyCJVv4lfsTgfKJghbHcyMiLtQGWJCLI8BHOrwaNLHGNeX79i94+WQFsPCLTItsx0"
    "nm54oNI2paGerDLcvEEUmDPqxlfGTefPe47XunwDMTHne/JC8oSpUs53+KMiOY2w2OJTT13XWZ9RSg/gF0o5h/zXDPbjvpbovs/w"
    "cV+OI9Fz3vrXIwXtinU5OO5E0netnvo/eyEyMxRPivLTUPpMRVluBI7jD0Y+KU1RIRj7BvNfh7Hb3y1F6P87jP0/txSN9fj865ai"
    "YDE6xrCHL65lwtG/7Ok0c+xOJgF0owzZQW6X7dQf8MFb0ti/CmgYFTi5ZhuO8UqZ8Yf+XcKXO7YlKyTztxGad/cXqui/DYQIBKzS"
    "bWolBus+Yt0TQybHcHfHYO25NM1ayRWzNhT8PDG2CdeQog7hPiQuDKi/D8k3b/IQsfoyZsMGyQ+i+1z99XJX5/Vp/tQLh75h1EoV"
    "iUhG5xL4LAhCygM58kTRqresjxh1uhXANu3XxnbQ+NViUsIlE7fCkbxWnMFL3htSfWPfMiXY135ox6CV66sWJ7fPhbiOOZrIADKL"
    "hgP/jcLmreXkgtMjgLPy1z5QF47fDs+lCQOGOisBkmfB8a6a+1YGaegioae8Ua4y3Fs+DmJYB+4AQssvgNy87y+FeuUOrgdBXMZr"
    "sgkBOMkdYjGeUKTdXgm3vwHMC6AZtVU1B4A0HhGcBsqt8qP6Co4wUMqm5NGe4W+sNEh304y+3pGJx9fJBR/0O7hexDA8AGWJDGQi"
    "Y29PkOzhL2VdOFEGTUBuFKZvGxmPajog8TqFmPA/TXJq5kXE89zDbtijLp/YIc7BreMIT46YgIxnrzVg+u1Xcct9rhFrMibfeRnj"
    "IQSPtQ8Fym4boeMG/KY1cMMFrrbwY97UfeJFktDp57zd4pSBcwJmWCBTdMN9nv1hFIN53tWi50Ek38vb50DWYcqWAYeKTpb7HN4L"
    "xz11JcpedpdrHzEXRp8Y7YyHlOlFu9IRtnoLZ4lOU5qHZB7mpnT6py8dZcKBPiIAyW/hTRG6c93dt5RqAkzWlmD8awSKQQ+S0tgK"
    "hbUDA8IO2ef8GdfVKEtpBrJ0t2lKUyskOqO4a2SGhYMO0VMxtuc4qtNIixtP64eYEMTC9ZEry8VW4x3khcuOpZuyx2C/DnXp3a/h"
    "LLQcJIEIEzoz47VUD4791ivuTXgaNkcF22OCOk7Hck5Rj5JkW8EKS2TjyDjdWpIJ+YH4YSL1x13i/aDMPhQXnq8/1KamXdHgwGvo"
    "ralX/5zUJLTuq4r66yDYXD3Y1pCluc5Qy/BmYKn5WoTirp1+ycnQzluXcNXNXtEdl1v0lBfKWuh1oqnG/CcjhNu43XbG7TxYkLYX"
    "SlIuF3JLHCGXcZkWBaxt4+QAdOBZRP4zYviljfnfCOhFVdNGL5JDio6hP632MMmLvehi9sZasfUzgfwMXEZZPRUoePRkX9i2Bq89"
    "P8SqxK5fdm6DRTYMmEHNEQLWl7FKE0GV6T40WfAYiQM4jW8+fpW+eg/hLnTT4rpPfnhLDYSNRBlI5TFHFkFM/DXLigyRewMa+s1e"
    "eyeEAPtApTZm475dAcsm6riqoOcXdiC3eMCya9bRag40UhFvOpOwWV6kGx6X6ZdwTDy5AAMgiBY16Gqe/nadkwyJLVOrY09Cfv6C"
    "qWm+ISoAh4OgQT80mba+qBrQt+82BKUD6vXbUzTtt+0Gws4RrE8AgjZnjIRqCE+ry+nPqlzQNZt+L7mp56HIrjXu2s7iE9wiB7IB"
    "Rczpijp1mM9sy6FIokCUvw295/AEoyZATbHK9kVAwDWoL1jOhW/9XVhdH2CmoTjBtOBVkQ2I0JFYN8W9ioKTIkHW4nG5mK0cEU78"
    "imLsyuHGfqacimWaVxCa+RK3pTDaeGtBjcyBNUore3Hax9KDsBazCP181h/iM8JZeqo6iUBrPuF9M1LVjRVzlx+5xDvKhsJ2kJxv"
    "Doa42ipSuRYOvIRdJEC1GezKVjDnr0Uafvj+8KHqH2fTdjJptnzKv83FWnjVgc6sIun5GaQqf/XsE7hzTc8nYHop9ffHpi+WXqjP"
    "EXxZsuKk08JlLR7v7gLY6ltiUmmdlYRGJbuldc7wqeVKXrwPJ+BK9c3n0vN16Wz5ja8R2DNeLvWXA0Ei4PO9WHf4+VKr4kcxsAOw"
    "Is665Ppu/8oS+Ofwxf53rSaZ4D86fDEZ4+/w5VJScHy0ef/OQ4xC4bY2pIWKtsJhTn7RFmqiOftBR6bNXmMqYQVCZqGbNu/m1Xmx"
    "ogsI6OuyHoRLHshtuALBAwiFLK/IKD02+8bV9Bv8axCzoB9hOjkFY010EB0+pVXKOnvaYwDngT3WtUgTANKaDStKH0+LaMgP5dNA"
    "UnrTZbeRbdXupSkD5jGWI0YvIyzdFHfCVrREdKvwp0BG0+clGes88vJDgleAG1GiIfWUSdKTLSBBebTVR0tQ6s92km4vxyqOS9r9"
    "S79Evpo7dX2BQsKyT3EmiLtPWKVML3x+O7tYS3WlLv2royt49oZdEn0d8A4d3kDsoiutJ87NKB3x8S2H0Ri4eoObtnNSBKXJfGtB"
    "WvORLuvJqAsa4vpy138XEixSrYNfTp3iOiB7n9QEtuI5lF3Mp/0RhdADi9os9RdjVLbjnNIeFeubnsvAboz8nFDoLgZht89psJeP"
    "mmxLVJ5Hk/otAklqfSWK4dM9tg3Otc70UmowoOfvj+rkEMXCK2MMIwrJAw/DyKvMaXWMJORlxS/XBa47vsxddwRdPRxnbk2EoKx+"
    "gSGmOH2OxSWBP3AitJ0KqSxYkwloXw6exnTO+muqKNNh8RkLbDg1pKAqlxaV6Bf64QD3iEDdQr1rMzeKCk6wZHYtjGAmZ4m0oMPd"
    "bbplknnEFw/PEjOhqMgLf7djMF7MCScdJ+ECXsj3EJ2gLjDHYgYT1eDC0jtnXCl8K69bYEx2tYMYC35XzT2PAUgVD6Fm8voSQ1a1"
    "M7TgcbgbotxtKQ4NSomn1HnZzI38naAySyqrRlBnLl/5Hwl+MecqbVFfxck0ieRxivc3e+MYOgUZ4/jjnqbQQI9K48n6Fdavymix"
    "mlQbcthHRzX6ij6TQkm4cSyZyp5Hk535Z4ukqp7WD8Sk9VrT8WuodF9SeADlnC9jQJMHgxGZOcLXspgzhWMCdUtJWyns2YFHSfl+"
    "MJz83EOs4pzmzbWyCChDJeEF2WctvH3BZHjFBaDXCKg6x9JCPJInFpaKOSUtaMpxP5MtxM4Mvf99Kx4ybGeil5ox9te17gV8lXE6"
    "EIR5mD3h3LgKN8gL5OeKwzMygcJedDLnjPSE3ZvAab/c9sRPj9waxwqdE2VIifrW5ANbdHlb344QAglFofmjfw67wSm8+9hPY7Bh"
    "wO6MJSe84f31Z/M4pj5Mqy8+/gRppEt94ldfQDBGiVI/r7yD6Ie/4OsTZvGOsE0yUz/qmyW6hYW/Bo4xiIHEef1afx/6Erl9ZzJB"
    "kKYqrSjsRQU1qCorred6XYwI+AD+mnIelV+Z/VXPvv20Sz0zHu51DvliZ4PqJvnxALhULvlXDsVfd5GRZdNuUE+0gVK4xAAIyj3T"
    "92R0dUUG3PFcDc8qqg3XgVmArBuXOJ9tyoIXcrCuNZfTfRlBU8OLItXKlIQZjocpsDf847gMKg7ddVBIAU5VXzpky8CHMXsSO3Ju"
    "s5KxHh/CPPSHdwe9E4lacUq6UzEdEdVeQr2qGoiZ2CeBc5B38nPMoPmb42tnoO4kncymkKYLvdEv9jCX8GLk93sn8E4vtI02P6Kt"
    "HmZ0Sc05M5Zb9+XzhcFccQ7pg1UMi09cqCYgNZXzp6P5Q70AQQHEOEc/TXPQSy8eH8j2T464jI7Dz414wACRQOeiZ5EsfTff3s0y"
    "VEvydMXp1uyRygDsoXHVoP1MdC8Ib2vU4Cr8FUolhcZRhVt2nbTUkk1dvcIOgNrccqRKNmwabXsca1RBco50lo/cQruLnQF7PZa8"
    "gkoYYzILOShvp0OfJQPd7W+0Mr6NonS63tTz3zcAb2AS9gjsZzlrnqkGxv/tK297mOiwCqOWO0Silf9j1UilijPCILYimU+rpC+a"
    "mz3YGEzEyTiEuYZsrkBkGSblHsTQRoQnxI145k8QwkeWHQN17a9evna9VBVQISO5ioXdSkZzwY/ynsBBQ1EzA/PGQZ3+mCFSIY6J"
    "Ntw9/ZU/PdS/+6xw0K8l0iFl9IPyXYJ8LlnAwK6BiZqouU/fRDpWmn6TT5Q2urJLx/XTQvn0bKplxef03SskXcZZ3gSGIT9u/CXv"
    "Q5T/ZjEOZagi1fWGIOK4wpMn19lUdiCvgZ1YaSJt5BtKW1LnqLIUTbaaisDS43JeSSSlKiN4GGogY8MwgxTSGJxSp/oS4MA4qtS1"
    "b+qoZZLKBoozl/gE2zUI/Svg7wSpvnXlTV9eH49o+ZvvNvdm6xilc6hfQKtqVmhT7+VEYzzwBZwGJzd47a7Nx2wwvHdpjHHjxFNU"
    "1qPhKaC/ob1wO5F42Rgj8BCEPDYncTo+22YK5oNHru8KzPCB9vixkG9T68DmmnIA2j7DqEct2J8Nj0Hcl1Su0hEqPphNqTxDYQ12"
    "EjxX7SJRt4aRmlRF6FBOsZjXak7K5hoFu65bEx+dqTBcxEb4lOUq82V0zlWytRQblRGx7j7yfa9drirNrsmbDLIkpuXCjMGcpRQi"
    "Z7iP6CjD71+7zPBB9JD0tppx2Upj1WMlVEfVRvvBoeX8679hq4L1Mq4FHIbqtIzjbPRekw31vZSudVOXcpnZT0FtZmftxHa82mKG"
    "0a7KTb36uOd10vCycZhvfv34bt2pmPgOgB5SGwZ+PFYxOkZKFJks1ZxQlBVXS9FJk3yzfzRwO4fwhiANI07kR4u/b9+4I0heyOY7"
    "ttdUHmsXAkzocg5a4M9qZzVDH5KHcC7UU/4gSuhVoATKbWW9v+iiFAAclAONdVAtlE71J6JYvCyt3LljNthVgddC8FhslQZ8piYl"
    "Q5tN/2c+zCwDWPg+eLJ8cAQwPkME2xEbjqGrcQ2miNRoKpRXvhfwErEYoNBlYGhE4Hhf6WNQD5OuEDieCPmDa+Hdu89b+ZwzK3kM"
    "m0id1g6nCP2nQC38OYE4AyblYjXoraAoN+p1TjDevA9GZaBS65Wb5Eugn+XZFV/rf7nK1U1oImdUULgLPcfRx0YhsVmkG8Skbwjz"
    "caw8PuYrUJVGqILJfVFMPyfplhTYP0ZwkSglGAr8GZpcIcvBZpzB4WvW/Qk4KZrkV+PUNG364K+h+uIITLwUkNfzRIhovOqvek1B"
    "VGB3sOltgJ2ITu3DvTK09LKxmv1ihfVd0BRCGa89K9fRBxLGAG3/1uGzBeYa6hcdyj3mzyOh17OOAX38eP3j+ySfMIxeWJSyQrTm"
    "NwgI5vrmim34YVf+QA1eFinM62qHrRRHZhxPIdUufxV/yFCKD4Q79OXGn4mvhjcReBJY+aimt/oIFo58EZdhePzBOqD7fWmFp5GP"
    "/+jYh9Ikh584tsdOuDus9Ro3UQUIK1rKnqw+pX43i9elw3a5GoEDISiJkPt9UfSI5me9HloCUB7vHXob1co3v3GQyx5L9aobqxkC"
    "dRbwStDoVOLCX+AE/F274QQf19qUt3yf5eGWCc5SQJ1IWd7PqgJQOcme7cb1Vl0fKq9vOBGi5ehejyi9ittFVkdWNOiLTMi+Ww0P"
    "wvAzo5v1MUCFm8s0u1iuPsKxbF5Wl9JqX++STPjmJxJ1J8LeUn7LLz6s5ORK+aaETrtwVMh6Ymlmd+QvvVxnzQ2kSKLPoELzV0EL"
    "91JHyWdEZu/EDpDuFivW7KHLXVuFFI2gcH6HpB38ecoFTNC0l+ttMVDcBRVhRGf2bc4cm/YKLj94AbhWKMMVTSPdpzP4Danq9OS4"
    "OynI24/Zg/gNASDj1RjI6yXUpsXejSNCKz/mG3PQGYknEoYvtX/27AirCm4oJ1l7M+27D0D18IrgHMzvTx6M/Y9mNT7kk1xAViX7"
    "8yNpoDOgGnDwgdrXUzGlaZp4ILf01qlV+eTCEBnBGL3ykTlFuCHgup30v6bb3TLecU4BTogUrbEM4quw34z7azhCvxhSF7sZr8O+"
    "Xas2oweIHSqvV9dPDqQEQ5Vnx4LVE84d/uD5mfVCF/FIk57k7byAq8NRfw6aI0eGMPZoNqkyZhz8t9mZe2L2G8rd9fO1Vt3nFRmn"
    "d88C/GIGD3qfK+urKO/jqfo89ZRN0YT95NCGTwAdiLi1x3XkXTSWZWhRnvuu1r9koie4ck/LtwcCIOgmMU2gUzsxHBBAFBsYfhPC"
    "oGNbN+qUjTIAoPfvd1KThG5fhhELYrl32uQsAA9+OHBoAYudxOeZnW/7oSyfTxLAI5x6WR0h3e/f4NXFApokCGcAIjkp9Yu1OlzW"
    "PLkihhnjAzGRgL6OdP+0twW50zx8KVjlStbGsw3YLIWuSSbzmZkBw7ZkP+6DhTY4tMiFi3n8u38CCNcTKnV8qjR4ABBn20ebO2sm"
    "ACOrNE2LcqgwfD9+j5ZpgHS34BrfD414sk99qD3stR+hFGcJ/pYLXwiaAg1S4jM0jHAs2m30vB8oplfzV355BqmtMzwQAucJYv4G"
    "30D+SU+f78+8t0cQjOHxPtvGnhLlADtNPiUcEhD3z5xCbvrr03Pp/++cwqf3i055lFr9GHr1f+cUGp303PRSAgllgDpOXf1IA12k"
    "b3Tfly/fkbSIz6+EBGbKsMkc3EEnJeAQ6HHVXstKK4+afJlWljTJXN/cNIomf53qI3ENR2sHtHVKBOj6MDg2FH7KoKRWOBJEBL4Y"
    "p4ZGqAvRKSCmCSBA7hao/Igsdu7XvV8zI4SqLtdHA0oImy4wY1pcuHZWzqMAu5WFMvhJ4kqfRs4Jca2PzAmf7ITZFL8w10SdIaxE"
    "oPRkhFrbkCyOe09P1UV44IzpLqzm9QFmaVxpuuLDD8kAU+L/mBvYxKNCfsGyup6Ps6K2VQ4oasoJh+LvUKNHNOy1qROHkpqIPnqa"
    "Qf19zpcYZfkyVzAq3Sh6iKhub1KG081f1X528XoIpK4dhQcJqyOoKRwGOrkN8RJvTPtG9Zk1aK5QSxzuMpkDKZfr8UsU+m8LmfLg"
    "b/f0pjVZcEXB9rtGeJHifg3Q5G/i+ucrSIX15mvic/1r7mAl5q3xOwbCO5BKhlXoUyG7S5PsIn0o4TIfgP/gBijYvfOKHnaWJ7/S"
    "tcR/IlB3d+FLNlLLdxalX/aczmwBAZeXa9OuRKqmD2P8wuWdGtzVmWfUKdIH7wvOJqWf/Zw/t+E2ldhTihZwsc01yqlL/tibm1C1"
    "3rgG0HE9/vvkVNgUaJuw56GUsqkrUglZZAhm1S5IwX6ar2v51cBToCGaEm76BFwa2MJNTQYPUar7kw7W+X3LWNrOaAYREHA0ODhp"
    "tuoAHctqwPSF5JNGKil2vA5WdDYobdIJLc+80QWM+RKOu17Kj0I4prlXspL/dWdjPnAU6v2herVMIGKx8yf+q4jbdtcvY7Us8CtH"
    "RNoh2Gc7ls4NtmOSETXoT6ulbol/3GJrfeF+NQ+t/A033NzUHGKFEKK8qL2VNnd8vZRT9mjV3XhKvp64bz5zh78UsDqGfFStA4tV"
    "ZFsU++rE7xWmv1oKMKFfpECIlVqTH+z0O2tnOJ/vn/LYunzoUcU8v4dfK8gDFnDqj+HH1Var7GTRU6wW+64VAQwL0Zgso3rjsDDA"
    "0qXREiB588RA98os7roOhfrKGebUzBFicRTQQji66oUz8fUR9kCOryDOIdCX73GP8KTg1eYHx0s89ztIMR8UuriGneCi1f035lTI"
    "5EYHB62i6imyVV43wV1NF9VJ80Cn5KcHaPos/p0Km5Bo07Yn+pCXMyQpJ+VO8ryqAQqODaK2xPjBh7+hPGESG3+FuY56IArOmrMM"
    "mgceDCltCH/lz+Jj6XkcEghhD/EtEUOuDKpJHXGGQ+X3Kpk4PHOhBvMS6C4QAEe7Mip+yQ5v3iGD9pkclVUEFBwNgeFPKbBbMCIL"
    "2AR+dXdy80DBBn2wcmZJuW8Najj5yimJeT2AKVAyFx+W+FEMBnh6nhdxHB/I8tm4H/FBhnDCq2ibP/6UT7yYeff0SqcrqwaqnruK"
    "cPgc34Cfahad+GbfQFZECuFGav22GE4blfNHa6XQmHZicd+kAfzEaBW4pYsjdVJwQKrlG7K46ZFvmFGSd1Ypnig3v8PMkqXPQAKW"
    "EGIz1wgkzY8pKSP3dYcUZ12t3BGt+iobc/u8MLY91/r0SV4bqxsc1N2OjtG8yP4WID1nM9siyAD2O01unplad1VLC+Q5CqrF5tX+"
    "GgCjLzrRP+5MvSSfYjBK6HtrsvLnH6Du71TxcSWod6dWwMPVl7YZz3DjN7DeGpUUI6W0IJZrwcJ3rf0sDAXi1MCCwdi40pe8h4mc"
    "yLE9+2WNUZi/rienvxhVxMtimuRXeeaktHA94hOiVJTjFeSIGy6d6NcqZ6mKKgrYJCFmaBvDE0BBzB2hP/kZV/2PwwwrCO2dzQ/h"
    "qriqUuj0ptQwpUw/sRzylQsPpmpmuz1bb/lIiBW/uJv7CHJAGmJO6RgSurBLL9ivvMUJyN74rvOh29nJS0MyICLjZIVVcBJkbDUQ"
    "SEXUc0FA88JAuRivh9/HsLYvscutD9dPyofa9sAzKUREdOg7o/XCWvjZcQlg3ysf61j7dO//yG78WLGEqFlRUcz+o9vJoeLITkOI"
    "NuK/iLdur56y0ZFeZKHtmLU+s3X/jioIvrhELOzJjy1YFiiGu4Y+HK2pU6XF1jhWDqVKlBO6u4keHHe43frvMaprpM0wxevu28B4"
    "WTXB0uY8oVg/fb7m0LMfC1SkWgecaXN6vqe2ly4Y1BmCnCi+2iy0F+Sg9+ezMLquRNQ201ET0sL3a5/nVyjIn93HvZ3Ns7v3o49U"
    "/d3XG2OvP5mXLAcdn335Is6nmzmX08zC9nZefaACp4dyurc+6DZLqIYgmwSQIKp0tSnoVUQ5DpYjocm9ITWdy0AfB50nWt0cP4L8"
    "5ZzOxVwO2mQR7qduOQV6gvyNGnvRocqVMBcREFlzs6wrFByoyaKijhG+Fxlj1vLbadBoctmvPT7rR6KfJkN/8BumkcTkxXaMJm2K"
    "z37IfuuAje0mnt9uLs36PxeKlDjjW+wW7GJP4s92/Di+bKaE/PG0MbNP/dK+0hJ2Xziz1cOjOyYsBrfSTo3MN4HFYemQxEUJwn4L"
    "I3NFcPywte2Tj0cy5vTLGg5YKfxjfDVLXE8PhHfzVcZToHU36+cxky64QxSaxFvqT7HQGjo7knYKnow0l8o6kKjhillilVjq+nW/"
    "FqcpCcraSWy3tJ4BmIAjxmhMri3+fotPW6WPBfwB8T9W0rtRFJmhDE4R8sMMbzJWgfLEnIHrwV1xxiIHdZQWgdj6b+z4z1sMszQB"
    "8DPK4/e38CrsgtqRPocqifynf/nn5NpEJQJoYf7r529+nfhvDhWX6vMftkP9b250EVf5UzqkBMBV7Qo6JuAW+deNrvvQxVcEImm+"
    "r9LPXEnqZSpyaqaFWLXWaIxlL0Fua2S93l/cW6yzNJBhHJEdCi1par23kH2aVIHj9sNXOCidxqlGvyu0z+0qhxQVFxsPdYEXdeYf"
    "CLXKD0dckXXaGlTm5Tnwu/talhyma4xAEASVOVge/SLQkIdEvyeYD9jJQ1JrHt/PiRLwZBO1LuUlOBOpDHo2DBJZ+PuM+vCTqBKg"
    "yijHATTy/JAfK8D8sspH8ZnMgafrKiIwpZ/j7l2MCE/BTkErIYzXRVza7KxNEdDZDn1310bZlCJtuOtEAV9hTEuCjyTr0pXBCBq5"
    "EPA9wmhJw71Z2wFN1phOH6XivCdMlJm9UL3LNTRebipLu+AhGzNa4k2mRLTYs+Ndp+twJpobW+Y3vrGvBJy92EvdwiUKM8VaP6sN"
    "L0TLRWj+CrPTd5ABpsHLKexFc4a3EGawjwDgbWd2Pk1f6Nj7YECNyBT/6w4VXFGtqDWZZvLUNvmom8rgfsxnvfZ2Ru6Wkb7VYDEQ"
    "BJC+iEu/2k572f3CCP3qu4WslNZRubblWYMJPUSPH00kwFvDlLJDGlJODa9z7gp0VRRaaoREzdc70U7Fda4ivdqsB7bvIcJGmVza"
    "wnbC65BxeQcTW1s09NvNz7JCS1b6lQhZEru3dceGOCgH+pIYzxcIaee8Q2I5nY3ZMYJIv5YVmDDYaaJFYdRJ0MJe08s1yzzX3/fr"
    "KIT4pOJFaxmrdoBbJEXNMlyB2tmTeJIEubC3Nk48CC5wrX2On/ra9PBjW1Bx1DqMOmYj2YN32zB+CkZhwbUkV7YNkYSfubU3hhy5"
    "QjKWLeKxqgiZ/5K18oWZbFjptL8p6afXFsOJonUbcgQfrl85XBTKOBYu4M2sMknn6vUVZ5YtMQYg58ve0wKtHuA2v76oXSUu+Qyd"
    "ckT6oX7zdicKtfZSpMfo0lTK+nJO97nENyf0UEhy9LFxYWOqNfAV7PQ4ra70S6njUmCKUT85b8F7JMnYkVkqFmK8n7CPqsnrlnt3"
    "+EvJHtD9RAZGqE+DyAjQ8RsZK59fuOsDUDUWT9x4+D0El7C43S9qGq53sx8r3exQTCAjMK9W+curW5+xPu9foLOOYekD0Bq9HlJ2"
    "M0zy05b1P+EZWxoxLzMjqxEc1IQL8IKSUXiWXO0t7q/sL+j20KbMIbHnYaRsuoNcJVxiWQvMFoEr7Fs+drrkCxbiG456lPquRF1G"
    "nmlR5giT9j90ClPfK6hCrw8h2yLXLEL8xwcUkGqwwtx4ubp6lPNLqNKK22kl/87fnZ9W3YDPZsm0iwxm5eg3TQc2zf8pW9pPnEnL"
    "vhBzTilO5p0M2ybl0ZcWh/N86F1DhGp91H+GHA6ram0SxY2d5G4Oaz8cLl0BLQKOi2f2yF4FHr88FUUGL43fVky1d1PO9IZPBxWg"
    "gLX0PTDYa2uteK+8azEQsx1jDSUqnf6cRUIc+z7mlad+HNqsJkZa4UQyk7jiZ8bAjSfGrgQfIFYE4KXariyEVaSG0HufaftDLP4x"
    "pzbf6cFFuTydNXFvapuid+Sjt+mPwhK7ZRkYsK8j6KRZv0sSort8/o2HlSeR+pEp+oGhVyxOl2V+204Qqa8V3mStj1Vx5WgWSKdj"
    "5Q9HOqZDwVdjMnmROWGFiLN8xmDTm5Gj/wCancUt0LCHPOMWfH7U7WvkuzlUsBo+GfEqZL713uzzfVcdfUWRLJYezVrFZN0kCaDP"
    "uiwBE3NUaPOjWzsX/m0xsHays3mVBW3R3VYPLYYdMjHlTPXmhJauLTbkjc0wIXSFii4cp2p/aSmhl6St5klW1FWRdOaL0HyfFqud"
    "RlsjPEudsFE9AdQEv0CaiQdY/7Lx+zcq2v0qXmwj4oUgckJ96K6AnfSKPMOMsPo6wJ/kzbP0+q0V1aLcBLoz51HXUL+M0kvPvOUT"
    "7N2FrJ8+5YUAq19QocZyH43hJNz0PnJWNLyKhQ+oGD7HD9g67oZdGaj9QDLOB91yAjZWbpBGQjiLHXy34uwYtOvdncFeBrcK4EVU"
    "maAPtVGHT8PZk+ZAPsnvcoRsF1VM0r/qapd2Sm7b7USQFBDVIe+Ctoiho3xpjTldsnzBLYzJ3I7x2GKJ01gKE45sFsezjoh3gCLM"
    "yeVB34NOaEU+HLb+jWTFvzPkOV/hOI4f4dyrLBND1zZkUb444ZW0ID15U5OtSBaXQKQebnnfR+EZCv+dmJA8XTlP9ata1tvv++R1"
    "8YloCCvBW9BYH19GY5u8NCuD2eqxvELIqiqo/d36gDbwh1qck36KJ0FSH/7Igk5/VwmKMv/GLqyUXTBzX+daMmaRKhP/2jevcu1k"
    "9D7bPm3piKdoynUwiOUweHjQ54PxkVlcClC48zfmgxLL9j1+Q6dtEQzj1hN6OrSVenyeNw8kXzu82pqZMCJjvpUH9AqJA6kY4gi2"
    "AmQq6GqvnPBbfWRjGf61XmhYvUsHtWGT5G+sE/+LsfPakZBpzvAFYYk8wCE55zgcmQxDzuHqzX62ftmSJVurXa1Ws9ADVW+9Dz1d"
    "HWK7QLPwcSwsQpYIiABsETT+yZI0p0O2RHIYXKJx8QsbjxcE4Q6+fIX6nCIdbqVEFESBBFPEwxY5Hesm110R6tRDoEAOg9Mh6BDO"
    "GKRKlARzEytD+E52Kqwhm9FWlFD7VVyDGl43LFrm1u85vezqmPVzWKn1K3kuRMbjKQXv0sT+ZISmZiS31XDnZ/nHN/Q9sAQvUtfY"
    "2CCfrxwGXjWIWAUZ+MqBVtmnLZgxBfFZY/HmKDnDNNsAtcGewINl0lBof0TRHZPgosSMrRRzf14TYKWFTfl6VmDbzkIGAvIq8EFW"
    "TCd7Haa1+B1nLMWuG5cannxAMilRXlBy+xWx218ujJxg7vtGm7Cf2FzRhnRnF3/vkU+Kuhhz+fD5ii1uLojgnEyf1uAQoAecd5AZ"
    "/xBbD4On+26wV4Bjd3Ogp/UBCAgpxBYylb0uxU+9H/CVpeeH4wc38sB9BauowLmd7QBXXuTYL+FDlLXIbWzyo+GRvXc7gOq2aw2n"
    "3PjRNodzJIr2A0hHG0y4T2TXDDdV56a1/0KQ68zRCQc9bQ7a6HjB5+Cyl5iTmZmXnxKMIFouHEiI4Psqv+eYFUWWri9lSKonI4VS"
    "DZq4b0QwqvzbSFuVJvyc7YoX8dI0TgniwdxLmDu83/jOKAQaa1mda4IRfhUa8CPXt6GjgOByZsaFp9g4yEryI7Ja1GCoaFTneRhO"
    "Rc3Ktk9IrYMKFrC6vyEROll/qVS+5rRrv73uPBidLWCAc1xgcAAJJ+WtNhlhR4c+YlcdEj9G2lSI7/X5aUJ/kyDGicvEd/VVvLWt"
    "u3K3/bp75UOGDmlnlKqGJg8UYRnZ/TSG3krR9Q4lHpo7tBAXDvMqgdwCl35eL0GPhbj0Md3tTdDrjvTSx0phv3q0+auVA2+immqM"
    "lzVO1dUmhw5IydXy40sr8u8vM6RdaS74IfrHnLv192BUVepPPuUk7PpnfFDCYmE89VmwN+Kj0fIzHh/NFNfPZ0xFQ/G5a3IU1mCr"
    "7mv8uA7VgaSNL+CzNyUyzq+ZPr/OMKWl0oHNd+mTL3O2leSDmUyXevXdbQrXqcujyNIg3aP5hCd9vPcnwH3pzgntVONf1ZHlcS0Y"
    "/GrznxeZhTuJVsMpHtwYaYaY/cK5GYyDaNvlkmf/rM/Ij00/Flv3qIn/fathXExI6xkJcaYyjssGQeOCjawXeERakam4HbqkoOBf"
    "K7qyBlUDqh6Xp7nrpMdOeXweIt5LjOyq8BL3Zuh8eJ/yTRLpHDMM+YB0XabjQ6jxNbtv3PO5VL8RLoEZvsIhytFxXv+NqfQBLX4w"
    "TP0dm5alyRMLnQur6KLWtHtlfdM4exqpPWGgyf1IvWMMgRAnEtclZm9xHEb5jw8V+fOtyNaMymgdPsEKqw0joFjwVnM9WE0FgPJ2"
    "BUTiJkY//JHx8gwlxxA/KId3biFJawv5hYHGb8+2V+ygpOT1+m9NZLXknMRs3EI9f5U+/+rGraf5h7cU63AeXlvQr7SHn3WeAEYo"
    "P3X99eDrzuKrmGSzJ/RfynnFr6fqTTUHLtxb78OJVR0WczEYBYL/tnJwy+phUwh16g0fWtIa2KLku9p5nIENFisIbhHKV97HVU4N"
    "lTTQDpLqn9znGEdqTfnXfqhp0whaxAVOMtj0N3YtXPwynd7NJ/TGCZBeU87j/ERYFNVHu91CbbCV1CdQ0YmEvrhD03AEIxHQmUJJ"
    "yE3cOPLG3yuoU+IlVLqzqlBIpTqlomS2DVPS4VKPUsYSryy41c7H6GSvG4Lf+x8/lc8S4uUwnqIybh8kMP9kWhtEQ9SsdvRSeBNI"
    "1W7MOfp6b0FrYqZ0BTshM3Lb5Y0m4wlnvxR7AhSxtliDRCxmEgBV+ekLQxn4mtBdzfDMb7XvNnC6+im2MPaT7+8KJDB+8/5qTQ61"
    "/IqNGWEBYG0CltFYCQrs4QhBrTQtxxsAQXCQ0gfEN8pAwyUwx0gNEjJu3YIzw8GNurMog8OBBhpUvWJXpe/x6jLo3vnx9wzLHqUm"
    "kOMawOFpXokUeCuh8AS6DyQ/P/a4ZDQolEWU3aHbTUSdXz4so0yOEl4t65h3Zg/hQfdA4sGJY+L305JfRfjjdgxfLaI2qwt8li6d"
    "ih7Arw/fDcPgjb9+9Z+SGpqTp/+ZLGVokaY5W7P/x2Tp2UJFK89irXasbv7nZCkt5PKFpTvTexUehvsmSO0OzsCPojkqbb1W0g9a"
    "ARYno1MQAFjXq30tvLPYf5wDe973hVEcQASpLY8ROIKWYwUxY/50T3ym6I0K+qcjDkIc0ak9WkEcD426k504fD4vZv5ycGbfpaxQ"
    "46wUQIBp2YXTkmhocv0JZ8lBGTfy/j5ikvWgtupG2Z5ftd6C2Yy4Ui90m39hA++a72uy5AE8Bz76/H1EAM33I8kTh4LNhxPMZU4l"
    "JaTCBksxGvypF73TZ5CE4eeYWj7w4d/ErHikUcPWowyImG3FdJdr6Ldt+4Gzb+Im1XYYHYrAdM3ILofU5s2M5f6TvkSEWqp5Z61I"
    "DaAkH32Z0l6zBfIlf7sEnRNhzSiJOatPyPc9Z2jq1Th0FtIe6DcOKs1pt/JotS1mNENm74jjt2O1jQYejawG4+K0VqVtqmF4ty6d"
    "rFhfwYJLoC7SWKV5pDlwqdRJpohEkqbBA0KyEeANACogWnHagPowdIzCvzTeGQNxiBkcmOIALzmiA0iMsSdxviqou5Sx2/vUdwrU"
    "tkM+V3vU8QPN9Ax2TtQhlEMuWRsEljFBFws9TjB08tTSbt5HQCekbL9XDCvwI/41xX4AZI4qvjiwi8EqXAQV8LMSP5K28t/X7+iF"
    "l2gy6sWrXKbCa+nvNOxP24CTTzyvkOsSYl65/PnZcPrJN5q4/D0oit+yfStu6Sw0SKK2YNv7ZOJz0/mTwhajyLS0U9TDVM3d2r/6"
    "SSJFM2GYK4C2wKj4ak789lqdSPGV0E/e2MYMnTRktjTiJbsYmFbLglWNs5/D1W/0jfjUKnLXlH8Qhtd8Pi7tf3DIl8zYjSrIGp1H"
    "i1fZfS/tkgo7paeQ82uGwwpBzgGtRU+XiZS2DXLi95pLpmVwnnY4wXCyeQ2WZ13x3SYu+nH53Kg9O7JlDEH+BPGWpLgrZ5R+BX7H"
    "MgBC429KHnnmWiuCwN/aupAuWZ7Fsb03RUHbSZVcKb3smbYuGhL9ew11NtTPZf1Iq1CtPv+NogFK7OokBTQiHIJhHwslY9MxtbA1"
    "EZ/gjitoOc5DpXc4S8V2T2wDdSp20QRjrTwxfIEHVFLDTQJvlPjecAoJBQcGzO8gCjIA4RjdF2iUO45/FAF53bI45n6ygpkUNV+W"
    "Xb22ObVfcKUf8VOL3rk6Qq/ZshAqEEaJnLKoyr4YO0gc7Q4BYukMRJG4TJ5/Pxz2tzsUdX1bHWkSYl6SwrsR/8buH4qzvnLuu/jy"
    "z41VY4PPslzLTIFTWTGA2PS72JKPiaU/DJ/UcxE2cOJcZXJSkTLhqVonU/gZ4AiIndrj02RHIQUvTMxeg/Pb8XwWwkaWhbt4KK3G"
    "GrBzg1NzTGxyhe6+kHrzlabgkIrUwVFRq74TUA9x0Q+cDWwlw0rYbzIVuLbKNKpB9AV3C/sSpQpyh8kZA4XDMigEGdI0n4TSUBIv"
    "z0Ks4L0lnjTXZmYv2npCHmqqU9b8uDGtbwDMhKThs4XOLP7I6873rRrqWzfc1rOm46eq6sYRqHeZFCzpeKSfEIFKkFosEmgXf7uS"
    "3HPCl9hJjV94IT4g+AEEqAbB7a2m+pzVlPVAO7FA64r3e1i9RRCJU8DSxxVSBhvOVYXY9YI5xbTsdIzLRPhCHAxy96ZKJ3SzoiMq"
    "AomThAlFKLyymd8mhGRx/WIKIbe/9RUVE6e4dKjXpBfk3X4swKzeyks0lbkLrwUclVlj2OUNIJUVCybDkdaEHstAsdRV0OmjLqRS"
    "Zra+hQXcMC837+3upGkUlc9nwvO84d5cW7HjNXDJjcmiw1bcYMZb3IUQoIkkATjCMSGd9rNAnK84Ai+UnQXptkpsf0Jt5ceBmYaj"
    "K9sWOeX237ldsRSvknjtC/z7qeemQe+RQBAd+xGSvi4QM32JihaoezA3/IaLpvhen0s0rF+TWRD1zTOwwczzozoqaHm+ebbOIMqR"
    "5ycClNJKrwTnhrWBsvsWxZLyvEqbJdUdpPDujDNEd+OI3WpjTkaY118H2SI/f2nrC0dNBOJVfgkWld70HDnCe/AZ8Ze0edTsj8Yp"
    "2lF2g0/+fTj6b8Wa/H9MLi3f/2e7QEz/1157N4+DB5ATNd4J3L4gXFqe0fxsPbR4fRr+0yZwh8fvSoktJFk5h5Q4GtbPrwusIHwC"
    "6p999maQutaicGnw+Qk5SN2FgI13Serz4Zr3ALN9FMufiBTg6AhWsKtzjfiNTvpmkIyC1BfgjGjv1z0xLlGBJkj65eix6rqJEEbs"
    "igvI5Qbne53UpflODyohoZE1YSuaqq/RAjMgcaJQ+wFhnZjuhX+jS7iJKlrBY74Kh7bO3YRtPL4gt/QmPpZnLThsZfuaQIRzncOd"
    "P2txyreK5BQFPYdN1Wi2a/45BjkNC+/rizJ0AX5Z821U5UKI9+gesx0lf9XPzWNfs1B0wdLhHVb+3rN6vhiTuIwEKD+vQ+EwmsWd"
    "5b4z2YIC3jDdOhB/MyLyF1z2DTtKOXmy1CqX3iOfikwPM25bnPuJm6SY1+Aj1Z9hoCXT/yRzKOp4C8jahQ0L7hrGSX3e4Wmjf7Bf"
    "LZSQkcikh1TcklLsZk+h/iNpO1dFDaCUABz45XBtcK0+IZuBkIznvy6GBPtewvBcivbzsjgZJ2RYs42lpEvWYaKcXsVXnyhvqvFZ"
    "QrItrREesqquH9Q1NyxzvNAGOoXl3GUYTd4U13AuHlupaDwK2jJuvrj3YMyaDLF4Kq5FZcjSLvuSf3VMLHvNDD6qb+HL5E/E6dd2"
    "fqUCv+faMM/BZq3TAcZX0unMRzrg59tTMW3LhhkppjzohZCzJsQQLflBXYWhBTYk9i9NG95bwwPdroN8f294ZbGMt0VeVxqZ9KX5"
    "2ciMVXgG+W7LHGuCKAHfLznxXEMGOAT0CHz5oEmDQ1par2KIeLZjAB7v6gdBpd/kbF0PJ6XX3U4UrAHJxgjA5/A5LSxjSk0VPVDI"
    "hx7rqmKLJl8HBvnhXca81YEkwjKZZZt2WylPrjF3c2KtK+tD+ScDs2Hz3NQudBMUsckD41ByPF+bjAARI0ZSI2yGfmve7r6CTSqi"
    "zUkKeE7aM8tGobvKXKclYEUK7X6ipNT6u68c3TE4iHeXEzPIlrUC/F4Ii9um8Id133E3/7qCgmtUzju3ow2X0g5XUIWWV8mqNKzL"
    "LszTQvsnLJgFnW7e45UFQz83ih9luA+Us0BVrtlSOxunDRMOULNA2E+yPocdu5WlUrmt/4HTF/CgTdhIFUix2fpG3TC/dAve8r4u"
    "7JGtGJF/VhqVPmszJEtHFBxsBB77AUtboXnP/smpY3G+rQPCKVd0MnydM9CjJeZy6z2AXHXppdIXv1rT49PnDvzwZ5gOYuYnaaa4"
    "HfktxqQxGUalYbQVAOzDLOhQ8mobk8xL3Gm1ZnmfnbKlM+gpYmSc7sLHFkmZn0MmQPWL37rCt4k3foSsDqiTTMlmPQJeyPeh6NWm"
    "9r/SA+doxsQ+ObEHOBDPqjxfd72InGgxnbnpzxm39qcPpXifdgZ/PqtECPJDhs3NM77UUWAaN6XugR8km3PvEu2N7eDy7j9TzxHU"
    "6/LSNo0xBSvWJVAMCixljuluwgmLDYubfgb2J0G/5eHf95Wgv4GRKa5uwmRwPKb9dhtFamuPC3WDQa3qasv+m/3fNSQlmvRY0opb"
    "MZbkR3cP87d0fcF7UyLyNqBGkayGq510HeHlhwibK7G70Ow2ERGlM7caAr2SB+d+M27re1cwgdekQAMBiQ4Myr8Rm5CX7ya6W+q5"
    "z5aCHFJ6ow8WyKzEPX8GsuBj5LdZN45T8hkpvnIZvqV1ncezj8ZJnc+zDGevfX3LRK/D4vFxeo3+4EVRmrY7ftvW7lOYqDCUPS8x"
    "jBQs7S25gKS3IvdOYpG4Pvh8StcbBjMplq4szyfseqANyCcnBL0JxOaSXUHENpwEHdMtSF9SAFxzAhZpfnBL32/auuWHfIqFdCId"
    "M58/m9m4tgNTZJh36Md5tAGfiftmCPF1IUv/tUVNkIpe0FYltxz93HrWbdWQstrkHD0SbymysFmVN+7v9TchowujDY87vlWWK/M9"
    "9lkCSlx7rQiEEQBohK6c8Q2IPThijdUZ6aVd5Qgt9Go5+QN2jk8HEXQFlW7NI/4cmcwkdDnSRo0E24KMLNlFj6s2Gi9z9ZtKiFIQ"
    "aO+iVRj06T6aPGhUMzv0M3xr22kxZ9ugaP3XKEAxb+PXfhp72y2kr19H0g5+9f048HKfe4d9mxV0yU9yqGtxT1ONQUhFfzGcGxlm"
    "/lr3Nlee7bU1VI2vc9gdRqmheagML39koEF9P5e54HOgRf0TpglUbIYRCA2A1AeO6qIeJPiYB5lxbU131uPgaP5xkGKjbJC9mZcf"
    "prFB2oxW6N610+uHMg2vNy+YZ5SQGA6QnmNkEbkTQuzyKwm9Tb8heo52pdjE+onNhS3bHU8cX+qtyQJzFRW92mbkN0fS/HNvSLyy"
    "+iv6Mtu+MVBeMSaQAeMaQ0higG5G3EK8ac4AEiRIpukCGC+XrgQz1GYr4V+/ChkW5S1q0B6dzPErn3TGXpyIHEy+VTpETLXUSpaK"
    "oqrY9P2D/xS65ekTwJAewd9iJ9PSjAxQWgUaNTzQos/L6CSw8nI+SxsLVCr7B7J98ZbfjPblQPBjiYiu7mdj/PeuO6TqxeAcX9Zx"
    "CeLlM6Mmmfal92xBuU/8mnMBpkZ5ea/F4uacX80WPpW6ekcfxNKGe1StWAz2iab5ariVYtMyHeFtRxEbusy7+BqIijw/NC0Wjea3"
    "R7l5GD3xZMh10lWiDuWydk4xVK4pKAB5Hj3BuRFAaNVKJNt6rLNVCKepYcm2P3bmsmxWFvbSG9DgG+y1rWmV75qm9xJj2wq/TPVf"
    "9xLfMCKm4mkJqljFEM5aU8q54pNcCvAmHBMNmjmaNmldqa9htUb3mOQh/gTzNdUbZQ1ei4vL5ksvA5jK3zvjUVWi50IY2XZZ5tnn"
    "Ivb0KNtYiUnQopbLVnPXP4rCsx8rflnsK4Cs/4tLPtmT0c7ROqaxD2TygZlfg4Ot2hIyL8gzE13h8R5y/XywtThZ3D6JvTTJN01j"
    "03d/X//65xkPMJ523cwtOyWkJMY5yePYJQvt6CVZ21xZBSemT1QvOXJMduSQpHgIsrRim72e7y9e58uMzVSEwt8kUSj1bCk26ltP"
    "jyO5T5/heUY6Mvu8VSMyfG6HssycPjwyDN9aVR515Jp9vyJ4MbWMrrN51sFI1qdRInOfM4jNOV/5/OhbhHiPNCc9qgEMt3AuI/Wg"
    "zq5SSr11V07QmjigxaDF5zRnr5OFKRa8Odr5s7g+QOIiodMQDl3ZlfSUcCHxnH4WuNX1av21UEjDqkug49Uw7pz7gK56vum3Nd4h"
    "0JtdTKZ8EejXY6XyE3IZuqmKxEip+lzQpqU41IpgcvkeMzmYMWaTRQSe3GTHzMocVNnIEKYLOaJQ60tA0qz9HvvUGiP1x8mAU5kf"
    "J1N9svU0OOwRT6MW3nE1BxQj6+fisnQJ7o6RwhspnBqCQ3/GATTJuEtGY7oBSuN6K6X3eRMw9wIKlSIh1cFkMtmbkSkOz5bTtPIx"
    "SMhVfZooXcbYCTtjEwwOs+dAiT1BEpppdBEreKhoCc4zjJYmVbpjCw37BAkOzlSBJsU05hbNyQMzsdnwFasi1N4UuHO1Ud+0Oso9"
    "9JoU0Boge8iViuvvX9MMuQYNLYRFBKe2sJwA9T0rQS1gkMSyDLYgT/KAC38lU+E5bDGGCEDu/DBkMg4ihwhjqmSi79GSHTasLRHa"
    "wQbGIU9GCTDnqEXvVTDCUYYvdkEiUC4VTGcJPzj/imKKfL8E3KhWLZ7AYAfnqUe+t+GZ1XQZzk2b/fvNQNKfIyn0r93F7gr+qC2c"
    "c8yHmW2LReW6jLEIM9dwWq7IEfB1KlS8sNwIViWZ+Lb0ero0jvYFAmy48t7l0riCq4x33N+hFvYPgll08uIKQqQ+81OBk59AFZBJ"
    "PddeJ+3zvHkZIZgX6oppyvyadHGnN9G+RRuwa1jZ60+cW8aablNVAvlV+hAIJ/r+pcylTkcrTOyCOBQtNVQvIfAEBU7MgXqaV7Ws"
    "H0q54Cv6jYPRwwoQc/xQYEX0XBxinqyFmvyW79jc877l/PLxerDFvNEVw0EJbpG5IqVXsBlxEhmGNDcJklmgFoEAMq/8z30j6hVX"
    "dFD3WX2KNQS1NCUoktrx6ADBE/wd6LODr9dtumbbdOsTk18UheF9zKlgLlRJcKd0tT75NsAnliNT1BoAaO8NDc7xMg+cKBEejPyQ"
    "TooGB0d8fAdhEvxnskKUJZpmT5X+X1Z2zXKt5Ga6/mtlV3Qy6Eib0wqOQ4KCQ3kLJFBqswBANCHEUaZHgPfp9OEAq0IZqAaEyuFH"
    "JRoYkC0IXycPoj7VcFTEuahBKXv68b7Zh0cv1OjkaTl1qzN0OyGFXa7vHCwsfD1+AQwUXKWOqtqUg/WesvnMK8SnhzLkbsfXrolw"
    "HdrFa9RbZGbmq64iacOW2/NqqepFAYjZq+a1rZTG9HQ7qD2ZxHYq3NhwP0r6DeIpBuL8AmE/8gB/grZ+G7qOZt/QYNHdkjoWtiX3"
    "kawhGTeI/DXlmjcgAONB8/zccwDXNwIXcvJBYs2KyQbY+LU0ANyneQpbXBlratL1kSL0gxXp8Brf+XdI1gu0LkKefahuWBGIVexq"
    "aCa2ADcVHnOaHGEu5IAu//Yc1x8aKJ/oBHF+B3+rpBv6vJ6c3vyt+aZfhby/9Lz4UVNjS01IHQl/Dyz/5bHZBNDQetHXsNBz+zEx"
    "rtQv6gi3Vzwla8eQAAqQUCb5PQBmZH9LQMHIQ78cm0jjnGVjn5BpLtF82Epue04z8dqCvstDLuTWTb4SXihcgok6e6i/RK8ZN3mN"
    "Y83D1GCSI+RkxRDsC7RqDf4J1d0Oneu4y4ebX+W2lMjSdyLdeBADcA9dP6kEkcOqkCOuulF5FRC/28TewQdhCMsurLLoAtW6xp/f"
    "2FamEwDphAAEi48bg9r+NQW4DTbJdVnW16SipYrD5OBk3H6aCelV79UuvHngQA4JoL3L23EK0gzF69HF32SIP6AZnWXN3WPl7hS0"
    "kScfoJUakeE2vodZz8TiY6CKCwQ6SbQIZmvFFafmCs6ObdfIVoZN/TrPW3WBHP0SrPSxrwlV/Pa/Rr4VU7d9wfOrgeVvJXDZSYn4"
    "l9bFYBh+UO7IsG/4yA2JjNojX8+3V1u3p/7YsoUfUPLk8/CQoIHSn4ygbayzA0gmMRDM0II0yli+83GP951mRsnNrvtg1xM3NQf5"
    "FLZ1BTG4tkp7bdFIFw9NMDsyosWXz+SXwelBSn5cklETBFB5udIgyiXfMhV+inbX4aTQT5Nfcsrj8XiwE3oUUPRlnMuzwMVSHbyz"
    "j5DuqB/EeOI9lZ1W/u0LOrymxPar+KKr0vn4cPD7TQtxWTa4AtiO23y3Nmh5qiWPYN8IcYEQKDFyAXd3WCnt9SvdWHLZhnzcr1Rw"
    "rQmuRfnzPPLr93cGVWHR+2qNhXgs7sOjdYFkMrGA9ECCcNDngJE6/k6dMcp0HJ4DZNIx4z6Ws1wqjru2nOm4Be9mMZzGN8FyOudK"
    "6rFv7NdUULE3zVS+riH9QFs+UuG5qRAL0PRnUH4+l1SiawUGDf5+dke+mseCHEAHU2rUVd/u4QPoOsSt5r1OW+AXYOYQ1YS0iu8V"
    "+0Ro+JwzdzE6RY/WG+oL1yZU+q9AIGHGndk6U0O3CAHMsubXWT+urBLp4GY4bUpo28DF7Qy+lOwwVlj1Kd8RyqJPt6pqe6emBopQ"
    "dl+rJxfd/dtuaB4H9BcrR6PVbEpl/m0lBeQCMXAazxYUT4Jy5vJhAQC9iAb+zEwB4viDjNpOSiblNndyReX3dVEHdtqvln0HtnK1"
    "cKJqgVcfBoZhKYRCYSsGPjnCWUikzrZkY4fZOyjpX67DicStfUiO3sCqqkO8BhoNrsHKc1TWRx4TTFb72ccYtayd5tujXQgrR7hY"
    "tMrOU+oQzhypbN3OpIjJYPTxUeyhG/fe6PyIYxfDoYmXsLlPUU4PRPiXdcdN8fpzePZqyIWjfvY40FDph6DVYkycGtTJqiF0am7Z"
    "7b0FFvjms/H+ICRIXLhXTr77dHyiCkIGl8z3GNPjWnSI/CX0DPWZ9j1fhk5P5wXs9o0k2k5Jk5ZWOZkWH7UoWuRX5COgxc4+J9UZ"
    "zPbZe81L4ZiQ/HsRxAKArCcN5IRjYAp6Ykhkma6oCZ134A4OWlibZoCMHBMJdxLFkYFggRL44s+MwpL8iZGeH8D4x+Sp7miqWeoj"
    "BianW6fhSuRi55jU03yYO/1NKNra4CZY0bduAgWFosaNwn3E7Fp466Vjd9Fb5HFgUhmMN+Aqyb2CjhBSGAtYAOc3B6A+wuEkO4ey"
    "FTTl3jvrUqMoYdycmUAoWEoklit+5vCJvSQFBArf+k0vQ4vRFEDCq/ORfkmGgqpV+Gj1InAsTRtT+Kzs9nog7wFeRg8/0ePN+Mnr"
    "11oLGgzT5XgG9Par5XYYZ0WVy0lcTODHmbTDJgAXWI7jvBcCdqxsNjcQWZdVwHSeqkZUEU2ExMW7jcFPxCfS78WeEgp/R3EGGknV"
    "pL1S+xPPfn/hdCSiP8NLzrqsWY3oUf+XKYEcLavxWELOqDh8IW++Npg6N2qAqx7tD0Xk0AFZvPZWEGkT3AenYX1k6AouL5GJPhsf"
    "QLbeAnzlZ5wHO/C0OhrEpP8u3/j4wSWBCdvSzNDZFLt9NqzBXaQspLK2iBr2zQcnrnTdMUixW+LqOH/AAMdaXU8Tz4ATFXg6vEzV"
    "96hBIfMp7ybAz5TNJcrkQIoWDAEPAKg61Ic4z+2/ljP9+79p/9dqptH9f004Kec/E04rn6Zb3xLI8NcfNt6Q//ZtQkS8jLN3rxtB"
    "fW7YQw5U20GCDHLeVpxtRuaHdt7qrpxa0msEk0XgCVtSLm/HYVCXgv8tufksD4Ue0QvOsKRv+/rc931CN27nXDf3IYDKxUPgaXRZ"
    "bMCY4oHCDVBsFomAjIp6GgFquw2QFBj+tUWgcBLk0GUBCQEJ+/zihxckAJThe0dmvbiZDSvJsSufDLu4knDpEbP//EBiX+Zx/rpm"
    "t49sYcHYp5h4Mw/3lyQp3RHGHBoJPwA5qngNHRVeCbWrdfRFap6R4SgPgR0ZDLTX3jy5Ds+IRg+C6FbkaG5B0rzfAwQlhInBvLpP"
    "+cPdYZ39gsRU8A4Tf/XZuTaScAb2wuCCVGwXbZwj0tRc9/BlQ/l2vjVml7WbcGvLK1K7Ojfk0bClHPAgWhaLZ6pZP10HOKDB0zNK"
    "xzReogkupzbYKq2I0k+a1wIpgwuj7b8kiuI5z9rSAWAA7yQqEcQ7TzSP7w12Ya8encBirn876cFBbwd1mDsuSzLF783Q9ZVbIB3o"
    "KPszCiu+8qbubeocEwzAvtOrwBkCG/2c8jMeZEg7XKv/cF6ZhveiACUNsjRjXdPPjav7t2nOvQXc162sLgN6tgQhgMu0g5pkkf7K"
    "DAWRn7Tow5bK6punQ5q1BNr5EqXxqAkIxdrByiylM8M0xP2zbnalSbovmzy9yXrjc/tiuJZn1UbkScgnrg+Fs67uim5ogDPub2dg"
    "OQxUkUaET4KTL83FVdDayvP9wpXSSIthaH1M6ZQAL/3zZcBwoqUHhiY3PsYrQ0hDq6sxTl2Er6jEM0TRkjTbRzBMYvEvVnnCa67r"
    "sReUT4GPWRzPUVv5J83NleOv4mes0qofvwfkm9wbeGhqMMysGP2tuEETljNOF8RVlPh12dHHNBfZUvUqsRrCnhRMCbI/dMpAQofW"
    "qmcT5wW4ljsxIX4PJzqCzyb7gnyUmDI2PhMQbuNsmodmpMoWJSLP4PBw60fUbQ13TR26Xoh9dqRmWnXRiX3XheNRv1Cbi42217o+"
    "6CtYFo867KkMdoUK1Nf0kQ2GSEDPpt0QSgxJH7MT1r/yKhFkdzNTpYryhuekjIzOldGAMY4F0rxDCMUNW1/CRh0vKT5zpH75Kvr+"
    "wn1Lg4pVLL5S2tcB3Xryond2WvOcqSMgMUKAOwbzxVML+yDivRh82CAz+0Orsel6Xq/v5h09YH6Jz8pjZpMjP2HA8VbUb5qYhU9q"
    "yVe+ryKL86xF+5OK0tAWt6w7oHhsmk9H9ajCyCPNyjVif6ugy4rn++YEMxkfnnOQ1BkEeiM/mCLaqbY2MX4hY8OwXWUQOWaKykRa"
    "HFnGTTLrn4Ud5cC28jW1PwSu0plbVDWuWX3Q77adWfxh66CvbcyKfC28+8Ba3z7GZ3Ma5DWE+DdodCT+4vfnd89i84O2CdBzElug"
    "j7GlukGdXwZJWFmqzN+zL3c3cdEognEImm9kZ7kI41swEYsIqj0hFZADn2VXnGcUqCNEMLFMNW/VY+SXMWUkwPfZKOUB2gRJ6+es"
    "kuadYRgg3tSk0P6aA1LacizhT10SYZF1BgvJ6EBi1GWpxM/G+ztzyazR1M/NjEyYuk+2HLy0WDMNr6+Z2pchfoEY7jC15m1Pycbn"
    "KOGj3Sn9UuGJ9iELljow+eXeoQh6ukWl3sI60MsIeP21KIO++akj+uq8kAxntwhoe9fBhuFc5Qm5jly5S6HLiXxewMnWs8vUOD/t"
    "+fT4kFoRgcJDGYOYBK+7V4lWgBXlA9t8HcXJ7+3NeR5JjKEjQ1rGE/dAEcBO1X0KL7D6oB4r0RYqn+3jU4fnUkT7cdht4mUf5QUc"
    "+mI53ocCTT/ioh13zFbr36Y5dvFbYjBLGwCyc/fTiB3v80u1BpriYFVcdCDkCcYI2SqwaIVGx0Jl9OlnbID5euo4h69zkWZtO3vD"
    "Hj22ywkkWrSqvU7D3X6rCXNfukoP93ZOoISIkXnjZU14ZWv05RXJ3ZMhnhHok6A6pkXTgdmfytwYKK7wkrTQWg+MHDcdv7vv8ctm"
    "Lkdv+cd8ccHSdk398bLWArHyRXKVgLN+rktuBOj9Sxf0/ZXkiaHcr+bFwWd/B/VYYJeGHNI2kMzwpv2oKJ9iKuUZb22I0R6XBzE+"
    "jVEJsddvqCBqK3QVeot634Gy2auuZJpBtgod0ceWHNvH9ICac4gEb6VCeF7UNBbnxlvDNrJD2kOxn6vqHp/yjZrMNeYTUhn1nHW5"
    "mSb/4r+/4HBuhTFmw+Gi7Izz00SBQ2MjK9r8jq/pX332rdWpEUns8Xfd8Y4UTH8SWtTem08F9Hmq9b3ubiFZvievVmXXOnDDwyK2"
    "mt3YFVpGZNZ2pWEIyhBijmunWvgXP4/y/SpfKZeEAAvDj3eP1MzZuuzTtKcxnDQ7Hlo6xBgu/KvQauxyI4en1c3g6GyiW4nARHqG"
    "SfHjJlpVxOXhmxnjxU3/ZvggLUKBQ4kfwOqiTLriObrj8zaYWEbftASQvolRf3XuTCEm4VjmufgVJ/N7BEMI0lU5Zngh+ABovtKA"
    "WXA/UAP5wKdHJtyZ8Vcd5lnfyNdNsqjsv3F/VJeXZlNYiUMSyHwcqHaQCzlyRjZF9GpVJ1/D1S8DkQXoaYboKjRAs6bcb21NzHp7"
    "MXruK46yNe7+AqG5I9rcjAQa/QFystPb8xc3IOhy7UTP8JHKXU0Y9E/htIila/Jy2UQXC86WRxU/IEUKqdiU+/kNPTbmLQvLfW0E"
    "IaV78xWRAa1ceVgIJ093PdCMMLfNcPmsiSp6TW/nc3adjcisAg8ILOlGt0aYf9rQ4TMmM87cU8ygBm5dHmOhfNm8DsUytjkgxExA"
    "ztvTWjhpqUEeV8kO8UTLUVsW04EmZMLW31zpM7LxS2KQNCWV7O027eXd7IL8zczY+CDqL0vVbgvZkC9vggNZoZkqenn98qx+yUB3"
    "A6T7iDqCsdtc5j91bJdPaWF3OOOmCrkTpve03bBasKLQty2pDwQ0ltBZDyIHjn/B8Ul3r27r1ngfFa01dCLQQl82YHDeLRjHvtun"
    "GQrLNCO1nykRR9rxITqwD8/B5TX3eTKZHkotsO5AvB5aYldKRlYZ7ptVXdHD23YL1FwirfjrlyoAETOt2kdHYp2p8WINJYg//9Ct"
    "V3yZiz585TZ+fdGdjW5ZcSMyCR20NtL+TXUePnkcSf2QAXudVdONn9R/6TwrG4iO/HqezfaHfNWp+z0pQseTfm3jewG+FZBzssJE"
    "Oli/3uksHZyOM/8RufxHip12ApkyUXWz0Ke6azKkLAtbmaUYumg9xb81c6/gI2D0LQUn851IERiG6/syWQVLTfSZCj+lw1C9qPD4"
    "ziYxapzaWkfmks7cKHBrnp78YYd5veTGDNVDbrsU5/yI5wNJvAsm83tX7mYmQWwVm3zydTkYR7SvifYdHTVXb/SAVjTjn7jEdusO"
    "hnXbTCV8V36lYznmkvsJmhxrBiEfXLA2g+TEoPNkzE2q1Q8TTB/pcTa61kmPDeVt2dzTzGRhvAVKhEvUNQblm/32r0Ar2euG9axo"
    "vZN0u8ffT7JblfXms3qSISjgZ3Ky9ApML5L/3mEBowrEabLYXVsqWrIk0XhHuKKMAJCgmeTAX5byoWNFZ+LmFYIIv+GGTy33BLaO"
    "PdlmDUVe2JHoQ/E4Rr76xH/JYSnVaRfDzExfDaWPfWuwnd/MnF62o4ljijxns04WViSmEHCSj+ATh5OuFfdhCNbScwd3RdCKCod7"
    "ZjgFv3RDq6zeoUe6xiYQfga5EtiXdGrjaE/RNxuLi8VFJZhXMIOj/QKNb5nJAL+xfq6Cy7x1vkb93pE0GtHq+j0ZJIvn2I/0TryF"
    "c/x9YjxNPiEsPKPfeRG6zy8SA63jlstHN4eSQci9en/FsGycfslH60ZabXahutAv51Zsl0jmBlChYWLHlO4wU8n0DU6/gup4pQCT"
    "1OrT4kZxTWO+Ij9cMDmeRpZbGSrrwIdmS+SNqS6YMI/4Wgl8UERHLb45+0qeAAd6OVQV/ObDkAwsFQOCyF7okx3suMdyVI74S5AE"
    "dPV/e3H45ze3xgbqovDYgNeNfOoz2hehDcTOeDBR14nbhXfJ+kUKX7VB0hGXSRPbtHF+XnzQYYWTq2y5vDOyK4+xoAVtAP9cL8Ja"
    "O9o7OA7iaSulz0VQeNATP3rsweFb5RC9zfANaQTVTCnJfgZXTlkqJ0AFOOIb5Y7BHFosoH8s8aUA1ro+Wgk53W9dgiCG/drbkkz0"
    "0HpUzjpkZ3/5Wc9GiGUAtOWh4PnSzu9fDcNPFAoEsS/5U1AvSjrob7psOlt4SA6p3CwC9tcCYj/ABytjgtC02B0sSAMxsD+n0Oeq"
    "6kO/xVijd1qBGHWm/56AAKmn+s5s/0y3H8n28mQaURK7Pml2amXSQEhsMGX5A4YHd6PVr01j9ddlncCsPAejXsvfwpY9xzVfhXih"
    "Cnx89paNV+R5DQH1le4QUwERrAokuVusEYHHH9gVS3LfKVSmgtGyo8TpdGxHpHkgDwJzAk9z+f1t2kAX3Vl+6E6mlU5BBRwFlxEx"
    "QHrsvrclNGgJPjaNmlxNxLd24B82Ph8jkLSOzK4ZlJz6SbvP6+m8PaSCy7g7XC7mjg/ZawBM2CrpQ1eVquVD7nUTOZN9T6KAHeFX"
    "WwFEz+7ayeA3ZYE6uBi5Wp/VSZobFM7ZACMa5maVYAOpMf8aIv7K3aF/xQB9Oyzfljaw3TSKAHDLYrzDrbv1QRN0TYUami6MJ3gF"
    "qAy3Po09HRAMxMmOrlaSoOAx0mBAsN89MjaVhjV8KS47XOrmF+k6rvIhKgE4snpSncqTz7I7+xCnUOIruP0kkkpneF8oYlIaHIuJ"
    "K3jQTMieomC/aDqzzOIP/7Q4VPWyCBN2I70QqpSvDkPVCl33RSZan+7cL0Ri/BACTvZG7jH1hoiDh0JqhH9Nh0kN5UaaREbdZFYs"
    "xUbz4+Y8rb6OB98Rr8X2LiCNfgAFD2Z2ZAxfZRsAlrGUuXPpYfQRB1Vk6oOWlUF6pNSdessq/6j611CtCnBof0Y+jXme86ws4+Co"
    "OiU1wD2emDDgddf3r2J/WuLcQNDOXt9w64qwUAyABWAhW7cw6ocenq+xR7v0us/yQqWvQZWHphsHtvnZUFOz2tn6ei4gOfb3Liym"
    "HnFq9fvoXaiNp8B8lRPp7rRI3eN5fvbrydpVPb6mNelWvWTBbgF8OX+2GK0gyQvmt/qiK/QoHv4bPZxRvGENWAiCaQfHKDrqN3zE"
    "QhaEqS4ByhARtsYinmb2ndFV2VliL/CthFY2gQTix03nwWovCA5MOQDjhZW2hcbwG58XHmm7AGbz5H4mlSdbm6bgEFyvyG0f+Icz"
    "nGOrjUDorCaOq27iwPc8i5se9UtHspb2qBNvm3EYQxAoptcvxBlVfn5QTO6OpAjRa0C1sDrxwVitKtk+LigPPrzrX4BWJdlFs3Lz"
    "w6UXTZOsETL112fvz4R4bgomSfknIvJgu0Fmq25+DJyr78K1f4mBevJBc1faHQB6fK907wvqrzUTa1G13raOB9U/TlsHclKxobJC"
    "Bdf2pIlzOgQLdE+PTuZG1x2iDTPrEUkTha8abh0ARWzEn+aW5smTq/5rgjoHQAZES+ybbgBXo3GiVqxSEgGkhtNn5OkEZJeP8bXV"
    "6LahzVGkqWzcgdN/e4DnF3/JRQrnV+WYLCahhjYEh8zq26WlSgURPuZP1DV4aztzLH/HVt0q9cN4aRWkPIkqs7Ey4weBdTT8hkPO"
    "wTaY/oBgIZ8JVD0gbgPvHKNyjQjM+BE2/IbbXoYga1Rp6aqhtdTkfhHAB7gxkVaKoKSC/lYHYYTpIsQJJEkE4KVlFUaNwHtKMtou"
    "gXgjzMIN66VjlhA6BHr009ND8e9pljbDEp63jkyPo+aZc05QvJVs1HvlwDFz5vVUb+K30h76zFZfoShk3D+5JyqVIVzU7OyQkG3C"
    "wjkesfgz6SUoa13SnsW/7WKGZWpvTEMWJ8YGF6XgjVrq3iU1vExvbs+8VUqg5SFBFYvYt5YzVCEl+/7b4k7ymeALrgt0uSJbgs0Y"
    "4A4Igsczm28daplOoaELurOdjDBQRkVAWQyIK7ao60eJNV+pwwouNiNeuQJZiLl0KFuJh1sPbeJ0D9sSREIYrfLAKBrswW41EOIb"
    "+hZ1LF1XYacClHIBewKIVL+iKebfw0OUp+fQ0NJGQkKyi2hVx24a2wmtMbHh7TvNi9MEsSUSQkvkixiSbB6wpiMhpyAvePtI4oL5"
    "tvYfjJ3HkoRAkm0/iAVaLdFaa3ZoSERCovn6oXqm296M2bPuZVllVQZBuN97CMejm1/WStPy8twslw6cV54JJcZXsqHfhX+khBZm"
    "zXldluru97ElG18ZzSnXLi89BUu2Li0CAwgC6M1b2iJFmP4xVSz9OR5jv4mBuTXziVuzo+bDuda7v8QBkmKzfrOCrnzaNwT05J+t"
    "3dx/d15UYv5HmyFMr/zj7Rul3MZbVMGDFr8l/HmtDkLm4b82RCr4+Gx5gWc9HuMxKlNQObpiUothTFLd2qk9T6PvbRZbVCdxLz5c"
    "17YsX2NhkC5WCulyz04zsnLJKx1czx3bHqnytT5Wm8o8kygBPJEY8FutleObMXrYmgDZBhWzFWplDKs78Gs8oAWoNfhCAIA+PH6j"
    "n+MDQ3cAFPzxmp1pr68NlbVi4ERG8yOh7449lOphlrOYphZOTeSiO7vheq84YQQuYe/izhcgYH5S4b384g4oHmTv1SsYKBk9afep"
    "q0pA1j1PpUjI0c+/qxzHtVW3QEt66sVuGvEY/XJi1NdMHgJEXJHAclWW22x9502yEpGYj/HgJjhCiX57Khl+vb7By7Jtf8ZvHj1O"
    "HgtU8Jg01Okgil6kFSSHtiatSHKaZkveoNi/4xYckraHo7pHmBb7zTz0dwaJfSH5cowyd6aLX/WQP1NrGRt9BMO2foUzBFktqp8n"
    "8lSOWeKJFGxBvoKi5kPdfXwe8Ul1VLF68HNwDy+l594F9jU2soXZHKZNuWHzY/ON4LgjJy3ssgy9DW4YR+Q+8fvV+IZb51yB+yJI"
    "5deR6USRPlX/kM734zz5LgQ/uBJecfCt+3gsExBz9uKhsozUrbfEKTTxM6Nn2ekOnU+UQxGqFcZNc89/s8fx4PzFwDuUMA3WOrsN"
    "c2KcO7FrYW8mxTl+qvc7JYZnFFZYq3lQcKp/XHdoYBeeJR5GNnwvWlaOixk+GVY4+WUfxznIkXoeMwfUCZNre/IXkoBs/RVD7OKX"
    "fz1xj6CiNu3mk+qNfV/7uZQF1aE0WT6B5VDCl2Pbvu6WUMUvOtC8d4WxeMx5OmDdv/HhSbzf6pz9O2vGh6P5AzznL3lxUlNunE9y"
    "1zRshn1nkyzMQf0RtRGWCRyNqC6lIgszgs241TAe5iCIcay+juEE6KyNWz1A62VNScZgKj9Dc1+dZmAFEO0D0+QGKidLgV/2F6ZJ"
    "kqE015EkDHGZ5LWEp3sdvNjEMfrb7jQco5jJ8bCkNUyF/mxJxJkc+CpyRs1EuD0rrQVCL3hNXVKvU1gQr0X3eN45NlITR66XmzBt"
    "OdwEuf+wxfzThWeheRNB4NA3ueosJw6X9E0j8uLjciuKu1UfEi+BfsCLcD/kr9AZ9hs+QXtUeqyjqgRl6LBrIMY7ogL1KojeAI1M"
    "NDTwZgBVd9aRS8ghn0+V8rZFxPFXBK0iCFf82WrvOmmaoUryiDlaXSByzxTp1vPw+ztfhf1J0vMUnEebI4AbwPL6GBL9jfYv/645"
    "n3tYmMVouKA2Trbs4sr1DX7T/Q5MwxoeCCDgWKzXgebDBANDyhCjCRdHD/6+Ut5JqDjYgU5+i/z1lQyuruf0u38L+a0KVJq02voY"
    "zPYqkJ/b7pZhX2BomgdIC+Jr5sR2OasR7ShyKDOA2l4je3nomRKo2LVmpb1AEXHXCw67YYSfY+FTfOEYncZroQM6HpiWVhl8f/+3"
    "uadVZAXa/Mtq5VvmX6R3XOaIRXZco3qRWZH8sTcQ5+fiLo0Vte249I+NPEf3RlY0vV7DNCCPVXpmgE6QEgsXujcIuWig2cx+YjUo"
    "677vxMXqOXz5VDl72jE92jbHJDwMZ2TqZnd8i0hV58FATf/1zY1QFZCr6av0dg88EO+1azmwtMCjx0INaXYOzn43UIda/hFlzZYF"
    "HGlz38UCLa4MSDJ0hN/+nEuXAAShx2mg9LGNSw7vNRC2VAaPfBOW5Zi/NWopv2lD24pJOpbpv9xKzkGpiTG2frmQfBKBCTgGnMxg"
    "WzgESNHb22n0Ykr9NwO5GbgvIyDjm2m4Vjirno8F8iqQHK0E/DY2mp9mCLVtOVlK4bfVp6p4PU9kuJ1BRD2s6yFji3AEm1xAbmHb"
    "mMLH3Gb1BGI7NkTH+YbQnc9IffKKmV/Q1Ehx+LsCkjMHZw1i+sb7vbJQQvmnwiJt2pB2j7VvsdNDzggelxjcGJf7glkMqtFUKo2/"
    "qQx0fJ63H2ycWbVHP9OGXn8zmslewB2d2/z5vao5cGyBwsvXBk1+S20Q1DOOovTy3uWugqc6JJ0C/Vf4tIs9DxprQmM38R2+JVnf"
    "EEMwhnKPVYmM/uM1CAiON+CXVCjNbP7dcZfy6p6mjjhjmNOpqeuv0GaQVsGjAqXD4ZwRITz2RwwTiVYdT8bQRVsCXTo8WczeO13X"
    "MK8xaznW3Z/95vFN0Qupp9PThQSMiVUchgw3olRar/kh2abhXNn+42Jyxw1oaCKOatu3lvG8jkQZ6VWLeVMO3H8YVpV4jAcy9F7c"
    "DosjY6WhjK80MqKgVXT7lIyFSvJbIvpS2JopFQb/Ui1Ti186IF8/S1kZ6yb18D+soYBCMy3baQ9uecPpDzYdyDcGBIGaczsDrvpB"
    "cLCXg76S6CuUirDtkwpoU0upzAfRWURlZQ+r5uusEIKU2sNj4csTO/xpz9pugAA6cMabd1nFN6BoTHaCc8TmPjWeVijJNMCA94At"
    "12Ceut+0hev2VE+tYtHuHNzidvULHOjVVzXkzPLS+atVPAVTqXyc17SIIP9aiviUllf+6wEa1Qx8zLcUEBBrB7eGkKHMFUo9b0CN"
    "x1vJr3VtX0bV5HbrwcZ1EJT9c2Lf0OaeTBXAoX3hXNXjBL4AbCwWKIVDYLwZNVi3WoD0dZ3ST1rGh43SefQGeTSoXnDoVfEUBQIP"
    "A6rIH3UBVjDb1PGT7VGY3QnWWgWQGdPz+jEVtOKXLrZ188d8aNDFuV4lwBFCYe38GFqq2b/A7+UJGi0Y9h8PvejmtbUiU//vh15e"
    "6HHOR+mED/Vbk+bvoVdEUrW8DswyTEBKzyigURpBTxc5kaSYBhPxeyxMjk/8WGXghRv5Z4ME2Fe1DXQssLs+ZDTpJ9IqrWQBmKQc"
    "4/rGp9sdcJnKhviYPfNmhahWZAz32yq+WP9L2FfcYPjBYrOrjEUB9+mNd0xq9iz4qyp/4UG87Gr3h4WVhQJfOhpkdo8tluj8qWDs"
    "nQBsBC8sCOtWNX79FMMHHM2BjvoziKO14/5WcQsnHYxNN7sx1owh6iuDEzv/wqBXh+G6g8eaOPhvmcvpNrI2xUGS5LfwRBGwUhGk"
    "BmTiJ/rZbUv7FhZzpfsdiMFzj7/2nvl7oHTJr2HoDJn0Uvy3q5ijjj4KJNZui/VyiPFaAcFtToXPo5bmT5N99uQMe1NEGdVs5gYP"
    "wrl8Hm2nglO45GUEweblajtudth6Pn8tfIc9XZnjMztL8h0zO1K4XcQDvT8Z5Dj3hgdidPCpwZopNhuaq6GehAHPrfqcFeGhPsZU"
    "pT98wtv6BEoNwM3qj6FKXpR9URIKQRunQ1tZp/GatEwj8IB/5HJKdlnUfBAY0J5fgUiJhyrRV8arCQoolo8x57t+AZiGM8v7aFME"
    "d9bSSfnZLXbZAJ77qb/zpejbh04ZioRy+6q35R1MNygZATHut7VPMLBB9T53DJuwfd0vZvpeIax+NRyBlVPT8SyGp6fvZ91pN3KY"
    "y68EbWj1xdnkIU/hpz2nsJqKxTGvR5EaYBEFX0qsoZihivpOUGHBikSlL65JVpgwNMFAfh84fFE7f7Ujcx4xxO6imV2udEPF8/wc"
    "ZsCqFLyNGQLsODQuHcDY98Zmzhkfb2IAQAAiQZBS/Ah6F2gPmi9bAtMSWK0rqdL61+nvJWMn7X1nWxhOAU8kQQOPGb3UEaYnORKH"
    "V51WXB4hYDmvwX/UbtWFo+VgZsSuwcTr9oUOlv+gU4zdl2I6Braape9fHTq9dwHizxBbJdFwivIsmXzwnsXRVGGmzW/70HY5tB7b"
    "bb32zp9T/bISt+Dkc35A6l5CwInmqAmqLRRVuFLI4TSSs4v+XitKbtEXOEzn+AGQRnA8v9phFRGyuQxt2xAh8LZ6ljJwXA7wAXVo"
    "gdGDn+O/KvGwGgXLxC4EJVCS/aI9FwRR+XzQiOUhbausHhZvQvGYbTq5lW9BjBbVR+Obqul8Yqy535tGCZL07MH+KLF8HamUFWrH"
    "f9TP4H9bC4txD6HGT45e6ELeQmKlfvxK4w8Czrp9IptkRMK7OPV+g8vBO79JDiWEz7Gi4mcyuMguSKGwTwrKVbm9MwgW6kBLf/FZ"
    "iM5XeX9YY0+ubfIT4eKWycqPOidPSE1R1fCV/C0OFGWWW4Gy6o8XJHlXXgnEnBUkDpAdjanfci2W18bBQbT/piN29QLMW0KXKg6e"
    "M2AUc9lVJh3AjsUw48RtZarOThX2Nxzc2lSOs1C0Ha0KnQ/gFz5TXy+LNagYLIz2k6ZNNIeD2saRWCn++WlSBf0y0plC/865mpXC"
    "BBVmXeaQ0NyQ3ku5JTxTmSH36pZzbq0pl1Axc3LPVSV+8QRE8l5AOAFSU5aMW/9YNO8axY9Du4N2FX84xDz6TIRBNENrg3ASLJ8T"
    "+1CgU8UlznLUeaRnO8nEQ7IlVLHfssWkm19ZmL/XEyOAmxIY8FNLAEDb8889/R65drIJQmTMNvsnrKy6XCRp/at69fk3D2w25T+r"
    "XtUF4//fiz87a1/pkeLnIh8CycsdyVPgQUc730akvuqIzugDIdfbQkLEHQvQl93elcqQpMNSsFSn15BFas+y2k+6+9g9755y0TYw"
    "+Bzqb43dm72ZTtU7Exc6zxw3Y3yGIVQQWsY/YIvXXv7by/JAGuBMy5oi2Yj0y5FrFzSycrSuq4oCSnPfMrEXL5IydxD5BNTva0RG"
    "A4XGgxMVyVsIViBPghPfLK6vGyzMKDOzPX7cH0xHVkzSQ+Ta2yeeF0yp1kIVem6vkZWCJhESd1Sr76iAiTRWYxj97LlGkYMouRE4"
    "8bS5BsXkgdRSKDhHJ5zedyxdTNDxg/q0WV6ghepp4A9ZVtXdQPM8nWhQJ3tn79WDDvBBaYuzVjnWIx8YMPXK+Q5dQ1O102M5a08M"
    "9unIl0bK8zeDG0t8UHMkXF2hrb0mBinJZRmkViYjaK8zo/JFL4Nd6+IYc+5JFd6sB0uZX/CC6sbwG+4Mu56lQ3Dvy2M7xNF6XKR2"
    "cxZEibpBrB8sfQtz3VB21HPf31uIPtMAr5gHSEZR/NaUg3JUYXrYlVMIx6uyS3yET3nTPdeRaSu2w0j3r1mx35k8peBiPqsPfDHG"
    "yuQSHZzglmtJzpCWxxPLagMNHYDlTc5dkXGRmUstMQ8IC+tlLuz85rqdTd545lrGxgaSbeJvvBiYP/lnw6/GgqrKh/uyFom4DOcw"
    "YadUDPZK6/bqjXMU6DdMQpaTHccxE6LYt2B5OaNZFGZ1G65ogE/mJ8tme7H/Uv0bGrA7pkqnuMXMRCBeVUuRAdAboKZnf50gY1M1"
    "ivprCAZOo1tYJokWV3jp+kXVh18dDy11KpAxpb4T5X692z2DpsiG8/PDq/HapyH8JYLRyYmNh1I7MMbhVUNWwe7io+onDhhkKELa"
    "tTMlyifQuh9znxxwhQRADttp7Pyc+TTij7kjVPSsrSJWhuhyML7RhnF84hMYDgrsZDq7GgBiIu7sA+rwwXN4TdsbyVCUKJP1p2x+"
    "NNNp/MvdZGoUCL1gdoFhBnieJC+2olMrV+C72TvadaEOS/2KChM4HPta89XLoftUKF//BtMwBauB7zjCdRajbNpGjkKfB9yrBsbV"
    "jqnuIO7XRhHlUcFSXm1/5dh3dSOIql+HA7diIh4SLrXX5+5qPBZGER2yva2B+IqSboMYwJK3sBwu/rDMd4rHV6I9G9aScoXYZXhN"
    "EhlL68oDuq0mqlb1jtEn32EgP6BCcKqgfxsmwr4lHKhXiXLddvU5BpUmuVw5e0/90Rs+tewquWxpje8J8jmai1Vdm1F+diSd1W0S"
    "3fVgv2TH+9+xsTBG+WWUzHYMOQsOxC++g56nuW0dAkCRNu6MzUcefw3TF3ETb+e9vR1YDc+FrGPg+DZ0PuxQwYr1p6qiVJWOSYk1"
    "VOztx4EdMYa0hEKucACLTfR2oHVfOMLMEUxbcE+kvAFfvRwnv4bT7L5BHkS6dB4Ovjg5sgqSOl+PkzjNWCxz3imWnNu8+ldzA0UQ"
    "Tli38dpOmCdd5acY04AOzfZ+xislUBnKS2NpdICMFNNfRtQUSbYT/Q9CfqhbwzJUgQvvFjRgprbbkjzZdb90HhyTgOG0QwHLFsra"
    "j59NGdfX5O4DwtHdqAMCyz6OWjl5dxlhvvrphig0jrqHAJ/pRkfeWSDscTdfDcfWkMbihIVmHOg1mzXX/O0MyoulhDoD5ybTeAJa"
    "3XcgPE/gMhSL6U1YqSH4RLVFkIVsZde36IQEuVGgLoKs42zIMgfHNDKDmdxrfSod/7nE3YzKPvIo7TSYc5UhHxITVpF6iT3jr3PH"
    "b1Pc/pPMp8put4OnStZgmjrHttHwIMpQ16qzBxOzCKSW254nhASGJAl/veQbIPkbLexnGql6V0K3qKHvOtWAqL403074Xf8dze48"
    "iiWAD5CLq7lt7mcxbG+atf2FwzLLNNln+x8GDw8dRU0c7rO+/KSQepnNlXzr+ErU4Zq+07jMORxFT/32MWrc5FLU7BnJ1uCmT+YK"
    "hhaiwsi4CtvlFDos+8Pbt9Inp+XwSUcZjqQciaQXJy0KWw2zwGViLr1ssWpUoks6A26qmRwXT8V29Cslc9CMgYhs8JvOn+2LgPjp"
    "6ebtxbfDdMz7GbLTuUwg1vr3uMFPYizK249qd5B2obtGc7fRbv8wXql23zJxQKhJpJLtX5HIL3DPr6qi0qqP5ALIq9O5kHeDq+up"
    "tXE6j86L6YZiiDi6sz+pvx4fPhV1MbkPfGhgmihr9thGzfRk6nPFIU8nq8diF1nPRFXuKEuBoYSGm636lpX54YWwPb0bNS32Nn06"
    "vs7X+JNnMpcJOilGQiqo+msxsJEkaWFGEhHPyfBXyPsG/CXKCOX0jG/sFqblFNy1X2XVfGokpofgObi9TnoTQbRAm6aRs5Hp75Fb"
    "1GGgVCC4ZNXYKheh1GYFKhTq+E5e4Qgg+f71fuOHIjfX2Iva139ch8CveqZ7YN+1ftjCDMyAoHWyaHmkpNuxa5r0pNCt/WK3n6D3"
    "TqJI/jkf8BdvJIytABKZ+jlTXlt+0Jh0RR2UGxZJKL/pB7ayBYs5CNHgUPtdTrKLQ4zECKbJcwp+hhaLNxhIfRGIGsi4dwqNlQQY"
    "Met2aqRt3kRJjhA9eHS4EA2wHRIfbEw/aczwd3hE0npq4tvJKFA00lGqzxZV9mzgrvRWIoyWU46yGAYvcUpBX3rcGJF3//2uaK+f"
    "1jo5+jZEDS3aNmLKu8tVDBF8VTzC707GMRYxAv7nGNu4zlzlS8+HHKIagq6Kq4x2KWCoGx2A2djJJ2KaVWyIZu47WEhd9rqNjzi5"
    "/qn6HZM39yLKBwe7GZIBGLuI3ZcmBXJLqaQsdsw1lbv9tT858debzRWVtAlJx6s1TR21e1gMVkRqOjMHexpDlen7qgB+JRIUfx4M"
    "vAuMiRelm7pTizFLAvubEdu5CmSNFiduLqTmjYWs4ER8RxRLEfLXP6vrlyq/aYomsQaexdksbn+eOpzMiodvXdTigtZ7hFopMA1u"
    "m9htSORAwi1nh8Oxv89tPGX8BVBUX6Q1FVhFLRLLUEfb25zTJB2ngIafjSz0+aHJqRQ/9BUKSG+P1IdIMbNvl2vYCY/QNvtg1UzK"
    "5Ukek9eZoSTjgN8t6ubmN156tlk5JmiQ+rzeOzx9v1ZiN9XW1ByFs86kXeASKwMlzATLKdcGDcpNaAM8an5AZu3WozGm1h7GvvsM"
    "1JEFxvdis26uu5bwzPUiKJLOy7HWydsAEs4gdJ/XLkowSG009ixoz7EF1/MSR4qp/xrY7ZhuO9FqDu68VjVZFMBFM2WuJfJEU31h"
    "vYKPWHtOqIV4Qp+R6j8IJz0UWWS1Pxv0V60Av2d0QfU/wiA/5We5nDN8Cm107FWX5bvm8RZaeNmGkU6wOakxOOnYEXyO9/6dkXXa"
    "vwxSVO8UhyOly5nylfu7VCHCdvT9KLXGYFtOw7mFi4w3awq/4NLwuoVv1aYEjlsWscQJ3rtTCUOyUEbY0XcpHPX8RsWFfGooG/xO"
    "7jxueK9avWMK3OlS3Kwu6yvPaaprPbM1nDc1Kcv+NA3+8uZMyttWclM3zqRycTf3OnAqEcd3QArHRGSV91mqjFmLAxTCBAKTX00z"
    "T3V68GLH+Br/CXqUnp+laRi1tUDFT52Rq7NJ3pfwSm8IZXJFv7650L8qLeEnBRbXEhl7FB3ilGkapmTcKsfxyGgNYGTLqZ7J3gld"
    "Hirwj3RVJhgDOjvYE+IHIHFjhSq6v7ZLxt03Haf7xJze9zVMn+IbC2kiOvMAwDMxGlxzq2F1lKPKFM03s7+bIvGkFYbXEnw9E5vs"
    "CXE8Em+kETk6myXeBBlHAxEwobWe7EkaSCshV2N0v0WdXGFCUTX68VMQ3Mi1OHzxHF+2+lEhUQRECvs1VR79cHaL64TEAHw1BItg"
    "F01EDznGJnNYlfl0JuccRu3iVfLkpKLK7/DF8oLzKrjzTZRzfQXlBW+xl7aZQid3IhXJWjUpwVQ1IkLhKJMgZf4VrogUPTh49Xfy"
    "mxII3QH/IHj0CNFGjeTHFQQrvYBqdWw5gUd+SCOAMF++/B0jF//yF3R3tHgvS6+wioDNZmCFdnhtUo2jGP26APmcI0+/SSLZc1Kt"
    "dqCgaHwwoYukqcscWTEvjh+mq4K1Gpzh6keLFLBxT8zPTfUWkZaHuXGAUMyjvkDiJsvDRv3tm24Ku44RfeOC5XGgtuo5UrJ+AZS2"
    "DXY4rnvjJr+YPcL5QH0GEjyWYK9VLClPxAnR8qnEQEBOL+qD7ohC8jgSgF2adjbhv2N3MYMU1SPweM1nCvgKezMnZ6YCxp83zt2Y"
    "p+yhi9iF0XpTQX5+z39NA5Yfaq9VVRchHOI4AOlJ+dj/Ty96+ysyDOvo5/9q77L3ffTXiz6OjuQlwlzYFAdjWMP4+etG0JClYl1e"
    "mzdahRc52QwAmFqaXSPitM6nqsEYBHc4eI3DcIudOHgARBW23zwZqqWhk8keGSXI3wFEvfM5vlmp5j3bcRocnEYwntMrR1uXBYCS"
    "nkr7tGOxzckP4V459L5dFqbEYPaYjQ3N1eqgtlEVvupluB6AtmV38vlOGai5N+Bct0Ym3BWsvq2osMbRtklBwV/m0XUx1zjwyqvv"
    "qmdmGvR/B3wzwiyLLETfjufgeBtOdnaDcmTu7JTIABmwgxty1hf/lB9Rcjoy5tB2SrReZkBar4zGb370kkRbH0GDaUv9A3HXmNA4"
    "v1DrAYaXsvrEbvDr1ESeyEEdzacrrg87U6G+TCG7jcLfUoAZAWHoYnFbawp1LNrc3MVhVJzqwsaqPtOj6J5yT9ncEARFT6UClBSy"
    "OXDBG2CNY22aqApbdlIBU7IJZAZzMBT3iVGcudCs8HTTEnX0GlUfMN6Rn103qb7+Y0NClhAQViNodaAbfebyWA3IN9Kd9dmsDFIc"
    "yZvgvL/2nP3w/DDDGIbt/X5OekStLdD7jbRUiEUPFgbZ+iUVmFi75Xhhpj7G21++2PLt4LsXD3+GRXOrbUgu3inVRfKE/a4TSFbR"
    "QooI/U/XyIUiHy39panizlEM+2BuPGcu7zyuf7Ot9DHllDbiCbIbGufEGMBfeqcoqAaH6SGBDlQ+7ZqzMxj+vN+OtWBkbymOr9kS"
    "uVf8uf1Lp0Hg+0Nc0K0NwUZoG4CL0ldUm93x+cPKBDBQtPSxwgO8cwWdHuYiMAYWO6IZ3GYAsUWH8d80Kshda76akoj+uhZubzSB"
    "7Wbx97Ezk+wMZQ5gY06VZBeZkgDIoXEI4lh/Xu3AU4qdh9I6oU3ew2ZQW098Wp7ZD5InDW9E5W7nv7jCJlEhSJFwHo3nrCadS1Qu"
    "54/SameQ5IzLzVcM/yZljwD4KT5bGvWpoGKC9F2YgNjEMBPa118WlQa+YlSzvit8XPfMCTsYMQn6gO5a0VeLxWAgxJ92dL5vnu/N"
    "gkSORMRF7Ke3YXZbGtDjMbvIixpnWNxxsAn5cLHxqSj74R2gG9yLte546HFajwKHn0njGdDt6yMxQDhPzAJKx5JvHwXjDp7ssItR"
    "DYOQB8S9eAdRSdE6m1BXJZf7aLXgdQ3oi2z9hLYrUgyNDRNcbogoeMpoJN7npgmJmmE4yjeO0MnPjkFgsYDz19MYpTja9gOL9xCc"
    "5eu6VDMweGvBC9iD51A8XyScfiyGwXZNmlHICNnBKd3xYlrQfXn2rLedq0tJzKrXALhVOLeoTp3tzqfTcFCVPIDMCZVS3PvaZZSz"
    "qLiYB48GmeJbtn6k1SpTfmysWDMvWNeJYs15B6CEzIIvOo/7WL37pUBBsHWzFa5BckgF/GOa4ssMGjWgZ/tSDvObsjs99N6iD6hx"
    "AtdB8Gv7Cnblrf1RgDdl4vaxHlq2zoDq7HCEn1zIBk/W5eACMyWdC3VfGjt/C+YlbV6hzn+9RJsatk651D78qqwuVj9Q73/32aQB"
    "mJYPMCkbM+3hO6l5pxpies/Hd4CsbH/DheIWdFz2g3mO1T/TDh5fb3XHa0XsWzcYz8ZZuJkZdXI2loelJpVv1b4Q+fhJLj9r15ie"
    "kA7/wAZCyen3NyP56iB2+Gs8m52g3o5AgPkeGeXoYhQmMJbqsAiC4BK4pAo+4Sf/zlShf5BXewTGEYx8IAhP9PMje7R449JKhCv4"
    "QWajmdcQMJoF8OydIjVka8c+Olp3d0G10zNI/SGJb8jL+H6auvig9EvcZdBvZfB2/TUw5sxvuQgy27n4JAbO4F1wCmgqLDZZYt5R"
    "ntyZXf7mjC34+Bg3bsIQ6A/LsfP3YJxSNLQdgZxv9lr4DUDlnLy0PtP2x4oovhdGuxmDYfjUykpW+uhj1IX+HZ6mgkcNgk3Jfz7C"
    "2hmbXHKndUeSilZnf6WsO1+bPVOW3c4Ye/1Ehs4tNMg+z5th4/Tel9M4R0Xl8DX4+ZznFr+QSeWQppSjhc7hg+bd3AYceoET+M8N"
    "FPbfbKB8TvE/2kCxKe5vA+XL+Oo2Tvm41ciKIDlK5hdi7/+9aVKuyITApUJhaUKRkv0ryHGnxYvxE/6gDxDxrU6G9YGbKpqQw9dU"
    "BWp8jB0YuCXiq9AxanwgR+RILJ9j7X2PAX6wO6Do+93iYhuwjMZt3wsSEHaPCjeO2SNn6fumUU2nw/gwXCf4N0KFgsn1ZfsiY1YH"
    "X54pcs3x8gXjIvbSANr1RmqAWsqmTMHOv63gHPKoteXRUFzMP3bIQ/hLejn9hGFGvsg44fmve+Rt5iHeNU240tBmdKjg9nVcgC1A"
    "Vy91X0O/0/cHzwb8tzKRXqF3Put6ImNLv8QdDvXPY6YdjSkQX5pwFCteU3+Qey75EWIFuZyIWIMZpMvTXImOy2A2CHXnGrgZ+bpe"
    "KLMyLnFivJ6LqWc6tb7TYsDNhidaL/0RXsEanzAf8G8t7BO+H26BcSy+dxgfdnWXDJCU9l39XfdAd9677rBluWCDwNMxkauyXciY"
    "l47SJVJ06Y8U53H5Z4sHk+Eh3TchJLcqRtpeDx9rYqMDNUKX7IIjzWt4CVMFZ8f8WtAS6z96GjVYh/2CZbj6FxxsdHag+9In7Jov"
    "LgZHxFx99eC1SPYfLKZhyMo917GvYA4OG7yeE3bq4YZ1qJ75Zt7Nfg13XrW02RbHdw4kFtDZZOiEH9Nz1MTROlWu6bF0weVhDWMD"
    "03jneEDMKz4kHDhRth8twO5J5EVT1ipLkTrH9W+Gv+YzMpVUdr2nf2AqxLdx3ZjMiXmx7CFFw2DoV3ENB2TfplNdUMzoAFneCNEv"
    "YPTsXobe+1XW0I+xuD0W5BWyI4BePhxyWUCqNN0elEdHBj6AYjFrt03rcUh1oX55xcdR9uo2E/0tiRsWRyTiQ9Yp1vv0kjH5HDtq"
    "fesH/RpeSF8eUuDrpL6Lbjg8JGIoXKiy+ZMe343ZjCOAKRu+/3oy/cCKb9mYkMRxO/0UPcpSTIfz6WGYFRhOD4pvsuUwiLLHQqOL"
    "fJSTB6s3/JRx/FF/MD6gevChobD3NGK5UjmvFaB6Y0DnQXoLuf+pHBIbhWF4xv0/lUOx5zndtxPakOmZ/6kcagtPgkIQggGGZJpT"
    "DT8GSjUyRJLM4TE0b9MJg6PtQDVLgezoF98W3MtdenakVomVsv/7LZ8oCSJeTwIKUeWEFt+nJyBNWj9zU28a0jNE53OFg0AkVtk1"
    "naC2i1/vGaYV7Zx/QDy9TUaIzd9G5DzrjzBCy+bZ/PVNBOOa4YWNaL6lCkTlEQRY1vsPARLdz0snnGaMFKvfhOfmCrnX9fwRHKUe"
    "nm5hITaUDWLfpy3yCRzFPemJ1pgFEzQPCp6+rYNmC9SUQvlsdH0S+J95sEvAvcrAQ9ns3MWsL7VatxndDU68/G5ldmKBoKlUM3a4"
    "tkMgtcIguSOXrZJ8ZofGD/j6vFKQOu1CMheCu2OjNcrwdyx3b1UTvYFU0pTqTjUYm5TUQe7fH8zm62D+Cnp0io/Rrqexpcr3K1u3"
    "MoGXjlqeJ9goTcpSzoKqHTRJEDIJgdXxqmNpIB3tEWDgrOEa0hw66kqfgFubc2y0K7GOMsE3nASO+qu41QICjSEdim33Kbc6Odn5"
    "JuPSHN/WNVRzkUv/FH9imSRLayVXdOu14vJy5me+/XLsXTelo1ZiSUt6LQRO9h38uOXe4JoH008hUJY/gBjXyyfeVIvDFolf2auC"
    "DVGiekF8zqrpyoOnF3hkoSSMEsU1u2Ac8AZi48mF0SMHgeIcCNJUYL9FE4f552sh4b8RyTn5D3tkOf/dI0tJ//FaSPjJxj3/3z2y"
    "EDJ3kyeQ7BAJc+i1nkgszMSnbGDKZQLJw/XcZDgmUaQfyjenpVMfQIYx6cl5yPxWdWmrV4vcJMjdG3g7GbJUZQJIwzDQY++P45s/"
    "HNPcspZG6btk/hpNHn774HRkTT9ehu3bCFeCRgkztmvb/cAk555nDdI2wacAgEVapXymaAeJjCQGePMJiKGYWDrkqcO+MOxvJgXQ"
    "KBm7gBYdcmVVlX42NGTHx3kIUEGmK20u2ZesJE2jnwOnaP8hvb1aEZt5iJOgFs4ReDPfY1nDiym85njXK5KTHZHoNbUvHgoj4IzA"
    "43GrsFIogk7b/HliNwoPlAvCyQx3YU5SJrYw6YciHvgOtJg/yhZg4XJRw6PcKSOytbn7gv4lNf3Mn3R+QTeSyPVwVTHJNtcJ/vbo"
    "efTxXXnIJj6TZyz5jZflfZ005Ez5whTADcakf+2zVWU/Nql1OJ02eoLtWTaEYVRAjrI/qBVYq5CJhRzjCzUhX/JLzcpoZ3F8O1ZK"
    "sm+STbWabftyBstLCnn8s5iTUMgUcuTEwqApLVb2+qi6z347571nk8wSHgoVUzXt2TasXVLxbPm82bm0Y5/n7cDjLxfvwiBLApf1"
    "IRu4ndcBwi4SoqzfcZSiUJ7dDUJWFwhoTOodFWfG/Ugnv6bbZ426+GDyggRvkvZvSIVbHV5eyDK0DYvWKd3Ntgm3ZzRvZTwPFECq"
    "0Vt/3fSMHzPhatQS3tx6ixYwnoPwoB+9XHgruKjFLEC74SmeOsYvMa733qVtMyHJrrJ6p0uzdhHZxxmsoHWXaOVC4ptN3jYovxRF"
    "RbyfMa11Z8E7HrN5+b2TTdH8O8k+sBM+7GH+HRiT6swlSMzKbXsekOzGUcQK481khA0EIinOuTK9rdASbU/Dmx6ofp6jDCfGeDX9"
    "s38YkKuf0TUdwMDxYvOaxfB+jtIm1SfJV9XCD6Q7yOZN8/mHZs00dRfNpRcDIDK9ASPCwVuPVXd+ePx9AJ/SidjszX12a9/E4Nor"
    "56FtZlnok2x3p/615Nvu8YMFEYIBaT6lPYciI7S/gqU6vZeecbBnxTJfwsjMLyyfjOjZq3lXeGTbzDZCniAWRHDJgFHnfDl+5Ot2"
    "vgK2PpYquFV3uM4F3rWlwORXwqFB6L/vH73GTLcl1Diz5RI/3Q+hIAznlrpzPh7UFyYmIIWu/g5+D0UXtqs2ONnTcTgohvaMEH9h"
    "iyyizR5kN8/QUWRcm/s6M+ZSLhr5dEuFw91gAUjzCATEjUz30ixKu4yMxwvpj+m8psr9mAiLuHbCG55Kkec+b7A4BXfgb6A2xu9N"
    "s68RxbamNwnlG755yMdHwKLbMsNiFy86e76/2rTmoG2AsIqHh9GcvlY0OhjgajiDIRlmUj+G2tSGC1MB8j2xXoFlbHHehNlykpVT"
    "Jmjnh2oJ7eUGIyA+hqWkzp1g6HqoZ3t4LzA6pqOO17z+njRDlXryZdiIQ7m8EO7yoeBaN8//cdZ7xYUBDh6vvBe1zBKlcP4bgPdi"
    "i2cAXw1Fi3SgzO089+jASpKNzSKbjTn57BuBnDn9UVwmPOQIl+ZIGizCL2se0z2KNzzOeYg8fmkKjB6bhSnfoOKAXaDi5fBsAOnW"
    "/EQyC4DCX6MvFBb9E3Li5uVucRCfNq3kmBDlrks5XZJOZes/wxCDS8Vdzj7UE1uaahIyLKRLvwUfxoaCcERhyLQRZ8ef08LwvDuw"
    "6Iho6v0HEnxA744u2G1/KVr1qD/aYmwJL6qvDF4qz+DgrRCsyf0u3/caIH816mPpwJRHK+rtT0d3wvd21OBrO/H+hKxQ1Jw7JTF1"
    "ID3Bs5DfIa6TwIKMM+atF0oZfLbqitWQF+PRzDEe9ZyB0lLJHmC+lW5adpyKCrVLnPGD1tRS4J0+BA41eSYXbS48TyHPy2OlYZTK"
    "6XW3JNzI6ASPA49w/86dKpE9r3bhsmuH87pXWrCaFoI+QwtF5ce4y9+ekY6kbK4UF1TDKuerGBYkq75SF+bFHRlscy4ktHzmC+Nn"
    "Hy9kpol8jnhGUxehXYnQxCGO8VjnCBk9r/WyMd4wAF8LJEAd+0kuRxdrJuOjtFnTjqVxHMHmGOdrQw4lrHvn3znnqaDpd4l8mkii"
    "7OX7UNUiGH2ypVqUnZtS3SJSxGzHCjgFE4r0nOG1ov0YRESYZAbViwkn1uRk5VFBYDLBGDPuUpq4Hi3FdrCMB8O5rmmoWUUl2HaG"
    "iz9k2ZxH7cEP9hVHPdwM2JKK4R0RZ9s1qmnY3Mu6tEGw+SwCHyruueRP+nLbRUWSZSDco7TCQE+PYnKvIaqWsQ5IHjc+Dxsw/rd0"
    "zA5mFp4L4B8QjmP/crJ7fXLUbQX1SxFfXcyaVkdJoxt/2XTvjdWyZHdOUuFKnMz/YGGMWMkGedn+veH+HSpZiPWxJSe9ZfhOtKXN"
    "SfDHkTugIIwpwOHXZJjv7DuzT627lAliWaCEO9HY1/oGh+xC6yeC0dt5FDp7c/mt46dz3UKgWOO4SejRyA94DfvZ5Km9NZs3GetB"
    "0cepO7UILR2YNI9b1s4ef1ElTLzF0kzNub5V4COO34yiofAfUf7reIecO3fkxWnc08TF1KNjhT3haiRovh/WvqGX+z3hheIos38H"
    "Yi+U+7mo3QmbImuOrSRMxevz+DmxImYweJy5j7x+pN+dn6BfD93LFDZ7Z5yRVYkn3D0meJ34dxJoymYwEKZjYnk6BYnfImS8Dk+Z"
    "CJJWbPeNuX21hRTsPokZVkMlzCjEr9+erJIR8ON2v4i0usrVePLKGpZzrR8jXO8FjJf01GskRrvDGtYlGg4pe3mHI0nLlugiKXbH"
    "8s3P25ygM3LxjNaoR33tt07UoGKT6TrNuNU/WWZGQZiyHfyNihRskJBIDc4a3IfNBMBlz2704wocrFzI5QAn3gFmPM8ysH90BdYo"
    "krT1hQZKUxqnw4FJSTAZRe2lNvEFXa5FIVaO1/GbrPAeOBW2/zqU7UK2qN/gDbYNKK+Zt2b0tAzmE+HhO9bOqVSyJ74HV/bhGIFO"
    "eQfuXXyBTGO/Ik20rXBJRXZo58yBj4HszJbF0pKamXB7XUXw3AD4P3lPc0wkSDdBAlYhg64baIGueGNbTto6/OZF9XYXXE8JeV07"
    "PPAZys7CP5eubmNhqjwrClhrSQZzlS7Ky8oo3WjnXIFkdIHDS4XEVV9T8mfE7550TWzbtJRv5rTWn8sU+xvkTX9UjVKte3GX7rqg"
    "lziBiNjWT798LVJWfEZQUyIWFeF+xbILFilTMLh1NPrYO3ubA65s611lG4hgzrrHHvEUuLvWZtX6u/fBT0lGkfMo2gQNiPLW3vgN"
    "LAUI6ckdmzxhb04Kmr39xio0fLMUBUPnUIBfYioZvwRic4PAx518SGU3iDCXr6C8M6LOoifN+apYUfbzyua4oSarhZd4Ya9wu0Tr"
    "azRbUsnTawtS/JMNNd8L4SruYQfODWhLyn1vpV5DizQ2EjD3etNVCp+zAvGkj6cf9LSMMdB2jac8VX13KXH5min70UoErlPQmrpg"
    "M0hwTP1C9NyT4Qptkh5hn2UQ1GUxJaJqv6aKKG0+PlnERx7aQXKdzyQyIyxGFn5i88YsGcQnEiOp9YsZMGmfcoHi65JKxuSwMeTN"
    "ZblPnA8nfXFtQxsdM2Rp9Rs45mSqgu+2utQ2ZVRUIhh6YjaX0FQAkYLyqJ/GfVZ+HfGnWuWRY2+igkVNSTJJDIC4nro1z4W2JLYa"
    "CeSGUhinJ0NTZRbQA39tBH7S5hNFaFqTjLzJBp1xJKVxiJY3fAhuRPeN8e/NfhFgvdjN0HqGJEkKGgzR5RZtOOx4GKPP8YFo49t9"
    "sAutKt+C0+y1bA95JrVRhuDJ3ab7yakGXLVPRDnx1C6EIWsTYm851g2W1VcG+eIoXqQr3lS/M5l7apNt/UNT251dOWxjFch3JZrE"
    "fVu1kC7bx4Ov40elDJouhfKcsDapqQEmzSibuV9c9sywAE9y0M+vb5oS/6zfI6WovEuPfW9Gi32zkT3soBGsalnMDjsgI7Lfo3wX"
    "oTwNFllzAElYvrhoRTmfJ7RWM+/ZAmYr8UB19yByU1exGoQ+pA3OfEnF+Np64g97cGDLtnQXKzHPAV2qbu8iZBmNAV3sy8FuKDxm"
    "2SyFP58aegcDzCJMk9jfjt62TUPY9zqNPxPY5zNHI2BG78jwPEFfilgmDXWuzNa2Z3i0xHv1PeLzxVrtoCrr7zTGa4R/VcqOOnCn"
    "AazHR+WSSPPskAaDtgXVBqp+jGXrADkyrXkaJd+4QLIaPseliEta318Zx17tg+fXppz8vW3rTTzPlpFkPulXd1hQKtM1mfb/qB4w"
    "/zYHeEdn/m/1QPKPk+z1yf4R/zocJlEY+V1cHUZ+EOqJnNTXI/quGzdaYavoFFCq+YtSdw//Etw9DTiH1jcYErxrK0CaNXPup/gb"
    "OjVHLmadOu2vpUOC9rV7T5rgl+0n/l/svd1y20ySKHh/noJyuzVgC6II/pNufWyZlmRZkiWbkixboRFAEiRhkQANgCIpiU+wEXu3"
    "5+q8w0ZsbMTuxca52EeZJ9nMrCqg8ENK39fdc85OzNczFlG/WVlZWZlZmVWH3ydm9WA4/X78tTcbFe2t8tmi9+1wdvqwV92xauXj"
    "3udx2R7Nv16/L19dG64/vrY/uc75SWtYL51cag+HF0eD4qVbvPi11e4eX+8cX7XOjmfXxUez7pf9+S8A6vNoUj1636nv5T89eD/y"
    "LfdxR3uY79WK1dG8ev7x59HnL9MvV91CdVycn3aOvfrlYOu6fZH/MdqrVS6/n5x/6f3sVJ3yN8e7/jQevN/fP+zYnblvlUxYJhdO"
    "p2MXD79cH1dKVxfzrnH1betTvtQ1TnvT6/fG8eXHvfsFiIPf3MPPH2Y7vcHF7H564f44/3nQByQUSh/3v5fsb+P85a/ZYD6rj93j"
    "cb31ZVwyT65mR9X3pZ/2wVat3fp6eHneqXcn7bPjU7NQL86OZl+rtbPzbzs7v5zzs9NPxvX7qyvg9Z/PLsqOcdA7/fllsHde/Tq/"
    "/1Q73Jvu9ffqHb92PS5+2jmvnZ4cP55f1junrW8XVyePVxf1Tn60VfkxKOxVHi5qg059/1fp89hvXRa2epct7eJKs3YmxvAx//E4"
    "b9nF8VX9M15EWRztfL/6dXxgLeaLo97xl52jQq9b+1I/rx6OP16fHG+BuvFlUd+ZWn1v/K2Tr8ydyux8PPw5aheu5wPT/DXvnxSG"
    "x4WHg/PZ48PobHq9882//KZ1P3zvtka14ne7tsjXtfcPx2et4qfvB19gIQGt7e/tPHbmo7F2+HXwvf7zrF/39oBbwr6yVzveOT8Z"
    "fhtefHKvSv7XE0s7+1bYq3U77x+6X5yjg2vQGfbP3p91gRn7X42r4y/movXBG3yfuu3h3uOHo/zYns+PHz7VRsWPfeNh7+TUtnof"
    "h8Od+w/nefN78WK+tdXfuboE0fxT9+vJ9/etT/v3hUvzauD67vjq+v602POs7lVt/3zs/PppPQ4m1XFBOzyZH9c+9stH3Z9HR/bF"
    "N2BZ06MqKLmz8uOPWv+y9b3uOfXZj2Pb+PL1Z/7+R37aPj0++HJ49Wl6WP72ffLLOtq7uO98NO9/GY+F+WP10js86w8+utq3D6X8"
    "hQass18deuPzratBVft29kvbcuy9futx8X52+v3k6PuX6a+T8/38r5PZ6fj+6GOlPTvs/8hr36yS71y+nx5fHSzup8eDIxC4P12b"
    "7rXln31r2dez/Nmnx8Xw6PPFiX/sds8+DK36DFSuCjCWnfbJjvWxVzV+frrasWb+yZfxnuNP9rrj+VcXBZJflZ2P5fZZZ3wIQvNO"
    "+2wwPgZuftivDw8eF9VT8/23K/f8817p7JMGyDPGp8bD93536+zw58C5rwBgrufujO1CfvL1Q8V6OK8Vx/s/8vZOrdXuVyfXmv1Q"
    "n3/Y2bK7/Z2q9fmzNnK+9XdmvcHX3tnPhbnnnnes2mFlsVM5PBrdd2tX36eF4tHM/XlS/LVXKRcfvNrZ53rv4bg1Pu58dPLjXz8L"
    "87z55eT4+ujK3zn8ePV98P59ud+9MMrftW9GuXrqTIyRtfWhWjIW3++PC4u9z4cze8e6/vTl0uscDc0vVzvj8w/9WWkPtNLKQrs0"
    "Wt9/fbsEKaX98+LDwWxhf8p/035MJifFy1bf6p4c5w+sHac4PTS3el9770d++Uf788M+qAIf2oPO12/fvl/1D78sDioz7ctB1bua"
    "al8P35/2f1hXn35qi07+cupUqz/6D+cHP8x+bXa9N7/uVHYmM9Ca76+Hw4v3Xx/7X85m+dnH05POr9n847mxf7izuHx0x8cPB/7H"
    "q874wrw/Xzy2/aF7/+Hx69Vhf2x+OTxrnXx7/NT6AVN/aWrGD//9V/sHvj+g9d8fnB140y8nX0aHVne48Pqtn98LJ73Cx9LZ6OC0"
    "3X1/cT2we4+l+x3zvLbzwfiaN6zOnvVjetr+7H04b0++PeTrnutWjzv+0fmjdjL7+tHOX57tfxy731tdf8v8VHEWi/rhvudcfCpo"
    "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"
    "Ppr6Bpvbdqcj9LvFd7scfBv7TXdkTRKp+MBqPpcvF8ulej1TzRXKBa3YyucK+Vq5UoWEcl2rFDKFXClf0or4AmspU6U/LU2DzHKd"
    "pWnFXLUOoxEV4LteqpSDFum7hg0WSlWNssv5Cn0W8yX2XaDPfF6j0rUiltYqxXolQw3ngSvV+c88lSplKrm6VuXdYYVKrlas5Mui"
    "vUquWhHtYXfwXa7UqxkBDX4X6iG08F2q1motMZoKDLsG0ImR5irYMSKA/WoFeOE5AeKoJoAb4la0jSlaoazVg94hpVQv5QvFAD5M"
    "qQXQwxegQZOGlw8Gng+wkQ9QFJYX+GPtCeyG/Qn0hzDx+UmQxI/TKqKh0CrmKhXCCGAtVy3iFNYLOHRIqUhzQ3kVgAjzWKVCrsbR"
    "x3+1tHyuCMVEBr7vWykFteCTdcCbLPAeeH+sLkHCYPtxWs6V4T8tU4dxa7VCq4xUka/Bd6lUhXSYlVq5WoFvaBb/bVVzlVqtjjXK"
    "9WqtnqnliqU6fBULxUINvgDfQAf8bytMZ6VYHbmNOqKsJX6F/bH+Q3gIvgyHtwXtVysafmuFah37K1XzQK8lIMMSTmO9XgKyKGGH"
    "dQ2Ahqmq1eC7lNc0JPN6vapp8A1gVZCMSvVCFauXYArLhIZaCfPL5Xyhit3CZBep+Wode61o5YL42wqSRSlRS7RCrYpeWmGvAgoG"
    "VQglQS1G0eKDEmMMxyxwEJnDH6eVXAH+g/RasVwvtaDbMlAtfFdqBZzSaqGImMUZLdOMFqt5WMvwO1/AXquFchmLV2kUAEUNFw4Q"
    "mVYoVgH1BQAKvwvVUqmCU0uTWslVCvUiTUUGSyHhwWgZiWhs2sswqVhDq5TyyOqq8F8dyua1PAAMf4GOEQ8w+jIOWKtVS0jPsLSq"
    "ZfjGDootbLdOCCjW68U64bFWop4LiE8cYaWG9YvVYr5OCIABIRj1PHKJQr5cK1Hz5SqtHtBfyzRQaBYmv6aVCgRevaQRXmp5mo4y"
    "jBenuVKo0DqvFjVcMuVqoVajVaeVGRoZ5yyw2ULk4nepUiqw1gvlIkFRK+Es1etanRFLvYocS568H2KrizwyHqo1IG1qlexy2hYW"
    "0rs2iVMPsgjaBkF7uEYOXchyaItJnm32Z87+dCJyaOf/D3Lo/PVy6Ow/mBw6WyWHtv/d5NDWS3LoLCqHzv595NCL/2nk0MU/Qg4l"
    "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"
)
# --- END GENERATED UI ---
