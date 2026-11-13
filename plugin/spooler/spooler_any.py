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
                       ).get("status") or {}
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
    _live["links"].pop(pid, None)


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
        return urllib.request.build_opener(*handlers).open(req, timeout=timeout)
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
    return "IDLE"


def octoprint_job(answer: dict) -> dict:
    """Bambu-shaped job fields from OctoPrint's /api/job answer."""
    job = answer.get("job") if isinstance(answer.get("job"), dict) else {}
    prog = answer.get("progress") if isinstance(answer.get("progress"), dict) else {}
    file = job.get("file") if isinstance(job.get("file"), dict) else {}
    path = str(file.get("path") or file.get("name") or "")
    pct = _pos_num(prog.get("completion"))
    state = octoprint_state(answer.get("state"), pct, bool(path))
    name = str(file.get("display") or file.get("name") or "")
    out = {"gcode_state": state, "mc_percent": round(min(pct, 100)) if pct is not None else 0,
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
    _live["links"].pop(pid, None)


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
            self._panel.post(live_message())
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
UI_PAGE_SHA256 = "ba6aa688c04772eead65a2a2101ff3989658ba0c7695e81351994a58f4fb8344"
UI_PAGE_BYTES = 833597
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
    "/X/23rU5juNKFPw+v6Iky5zu60ILAB+imoZhECRFWnzABCnZ5nDZha5qoMTuqlY9AEJg35gfsREbez9d70bshB3hT46JjZiPi38y"
    "v2TPK19VWd0ARVnUXGnGRHW+82TmeeXJc9hbxCx60/LCcvJhGbr/UDGNlmOL7iBHC4uG3G+yvNqWyyL2VojE1QERlwQ+8gZFXVZ+"
    "ET7z+gq5FC6YRxkqpd6rcahtZbc64JsO7H45VDlJi9IbDKfK57cvuPOmUdkRTwc9jd++aDC9D+NJhN9w/eI2012A/ke8fcALbMsI"
    "uPFy64cz84UR3IUzRErdi+l0L8lsDJSx4cXiIKzQMMzz+SresVX0QjqGRulOJYMq15ZHmyXMNmtpIlQRo4rQmLIZYK5tR1lWQBMO"
    "4aSenSTR65Y1EV9nzRIY/8zJjGYH0KXcjIFwlh16DOyuO/6rVnR1bXlX15Z3dU2/Eb9zeTHySbw0uPD33yar1v2S22jlFtBhcDbI"
    "539UFPnJE+GbtPmxh6B2bzuA0usVjM73OthmVBdywyJ3P+NWaES+43OUJUtigtzgGHg7MDPf4bACqDzJEudIUOKzk9y1auHUI9iR"
    "DWsKyriX1557eD4c3q6uebu61tXVta6uzOH4Rq+htjbfbFqbb7YjJ3VeapEfioag0oyPJWXaN1KqoKuJ+Efdk/1ot1VN3CAgXBrr"
    "04Ght6QLRCl/rz2QjpbvKKj/sL6Clt5R/ZS8Il/o+qc7rpzjV3Bj0DyCvrclGoHJiu2uwn32nllZ+FKemmbtq/VD904dxv6oKUxd"
    "Oub0hxtGr/Ug5qJamObpWx6cfhE+XkqZPKH76P8wElKDsqwO+0P0Ye/dXMpG2tji83aYJ89FwgesJfV4rI2KZXbsxj9rZ7mbmv7e"
    "+9lm5GebkZ9tRn62GfnZZuRnm5GfbUZ+9jr50zITuYT1xwfgoXIRPugyTe6mQ34ekBt5N/agwYm/ayPQzMNLWlovm8uSGMpRBmII"
    "wnJFDNBrF5My3HcWFOp7aQdu+WsimTx9J8kEksev36vCUkLGos2D1xl0S1WporIqQkcaWX2Hvt6Wl+gG/SIj7rYpaPGnouj1dLSk"
    "ERvhKFXFDXv0/Mt+A7E+uC4vIPB/zXDy6zf7IWVsyP98hTZwxX9SAqJaYQPmjgcm5n3pxaqoR6lQ7bvvfTW9CG9fHhuGNCSlFlQV"
    "KDQG7P60TOJ9tfrBVVnUtU3Pqm7iygeYg/9b9606FsD61/0FNgnbfPWPsra4DJaR25aLeYV3ozST9VTYaarxk44nB8t1/52wtu31"
    "6QLozeN/ralngx+HKUaaD/D/NpTnIMHmm4TNyyqZt6zP3NdKWKRtxPJTD/vXcH0Lc3zGNjhLtJpLFZdhOwo1tvq4xpvci5xcz4q+"
    "+wn3BSC6vEno8gnLPtIXjNpN1LWrfkdTPs9kF6ejNy5CRzf7AneySSqdrX1TudByjaGcTXBhU6bVNkmoqbLtURbh838AYmBLoodp"
    "9vrCTxN/EieUZuVegL+HE4qt/nxC/+EndBF+/W6STXTA2iPXAFN4qPfme11Z413csNnJbW8TD3vjGftFtoLnSuAS+6t1D/4urwGW"
    "bzljUusYmrYsUBzuZE1A4LD5H+xFKOwNVx/0/sC30JsHEJKWOI056XC0ttHknT03qF982KcLOvr5cP3XP1y8VVecJtgL75HnUjze"
    "EpP3Hx+vpBn8Djrg0fGuZjlALrXFGpdPH8xOeA+Yz6upsiDq8DLIpOA/1zWb0lLE3rCUvRdqxucCxbNyDb+K678Ufe+X74q32ZHH"
    "+8XPHy4epBHufU+s8Q84aj/5/fit3o8e/9AO1fkMqY7nPc71d3/H6NXCNuyq3kwXI7/FoB/2spE6ri9cp0cq9TNxtXQh/55eT5kd"
    "Lvwcj7yuXznps+2R8ax83Rwnpkj5thu6s5zuaxpVJFFqxfijKQAbt6q22y6pscoZ5/XOQPSyeb3r4NusahG6vLE1F+vqxRbrZrfr"
    "sPfmb9Fd0atdK+r1mvV69YyxzNWuZfc1Kou+ql0pdrV7b1zWY569ga5eaAN1+h4jrPS7y9kTHlwyCrvHoE3zIzcbD+O8BmBBl+XY"
    "Je7j50U+mzfNiBFus1mUxU+Tcp4DF4mPc5nRpwsmPF9//NnY8mdjy5+NLX82tvxfPUz7H36OxfdDx+L7OQbYTzEGmCdg1v+aUU4X"
    "4Z8ARyTHZIs0S7P76iaMQWI8oA650G7r6TCpYYntUj5UO4uuB+oWmAq43lqb7kdcqzhbpb3Z0oF9H4TWbSGnhGllmrpM7RaSQnP/"
    "B7knVNC8oBsny7RlEf6++e73kn6Uvle0L2+ErMs9P2+GNadoXs2QzTOWo1s3uY2oXyDJJVWUTpeWtOJa/USDdC01/p3i8/AN3JoX"
    "FsTfUywthr3ff/mHHmfrRwmK9b4A9iMFzPoxQlu9L5D9eGGv/qHRqd4XuP7hkat+uEhT7wskP2oUqh8qUpQfOD+lGFLNZytMDtcv"
    "Tw3/QaGf3g/EP4CgUB9yBKf3A+QPIrbThxyF6f2A+QOJz/QhhlF6PwD+0QMs/XABkd4v/fpRQiX9QOGM/JD5iYU6IvL+ic+d9OWU"
    "Hg0jwYaq4N1uC+NVbraWV7vIxdY7Xqv9l3O+dZmrHfte+bJXNFZdpeq6xHJ53Rprk6HPLrVhxeGXrX3cUA8ufbrHTUv32FnoWp/B"
    "2Tk6hlh39qUfoQuC8ngWdEuswhuXQX/XTYsdlMR1uuZKUF4Xfq6TKLPMyya2vmi5tn0vI1zyTL8p8C0ZHZfoBvvK8LuhP6yfd1JX"
    "l01qJdAl2u+FgH5zfQnYv8cIiQ4lk6bi3e/sr3HGr5JfANdW8KfoO9HnC9xaL89jh85s33r7Ctxf3sw7ksd3pEPQUmIqwFKW1gvw"
    "zrum1fp73z4W5vad+JLuQ32tExt/Pz+vFhi6+NcLT6XbIYYPYazIv7+8kXex4O702LnaUacLswug8c+6d4GrLOwG1o0fZ8mvrR75"
    "5ytGfnUl6+AQ7O6l/twvJHUTg5s+YvA9FhqfA03es9XORdnIDuMef0AEi8/L9IBNnJQNRe9MgK4mOet0Yt4MBNTFD69wl35pROrX"
    "Haxf5vx1BMsNi0us6conXlZgJLKFcN7Yv0MAtM43Cxf15f4PiXG0KrrRxeMafSDPvcKGYTMuxjs8qn2n2E7eWGydbIk2eniXhb5/"
    "MUdT723O95f5Xf5QH1RP8wiPoG3MsSnBjNIp+RhyPNkIXqQng5Ofjd1/Nnb/2dj9Z2P3nz0L/+xZGHZJknR7Fr6sJ9UfJEAwQHzy"
    "Lm+8ffENLyIVIUjQr0dyudcMbQca/li5amC7yXT6AQUTvvSsLxAseDVrvVRWlIiuH4y3BahUz7JnXXEnC6j6Y67nD7pQH8wiHOTx"
    "qRydi+3fjl3lGoVzCNCLHsnveXK68ALvr3sSjbS9wVSc0g8OofHAnyZIpgu9QTRwC8p4kMXpmJ+anHgClbb8VZR5Ub0v8bZpqt8t"
    "PrXF3A9GiL2U4NqQxH9CsZfnEcituE+e5fMLulTp2K9WW7fZIc73bG6JfvBCTmIM7tJ43esGZsN3F+u9v5Q7yYs2/LkOMFQCS4Wn"
    "gFUF5evv58/FfbuzqUJ7jSdbTw6+QYYzTiZpluwBz50U1Wk49WekSRnWOuswqZ6cZKrOnaQcF+kc1rIM444y+6ezg3xahhOdPy/y"
    "Kq9O58ngKCqtkuHcU2QumQ/Ku1k9SwpEmeFsstVLwirM+lu/qYI0C5Lt8YRSzhJdavjROt4hT9LDWv8+KdJKfXOsymzRHyYvqpdb"
    "WXg02ZpOej1sB9pF1rd3HBVBhh1Ub99unS36k8lgHE2nPez6ypUZ9pmF1YvsZf9WOunFk76plE+CeNKr+v15d50iqeoCRr/o984W"
    "4U7dB0j3YJ1n8zyDlS6HZ9F4DJsGWeq7dRjVVY6Z06RKhnfg93FURcXwSR0eRDGIAq/hY5qPX9fp8Bv4LIClHRf17GD4CH4x5nxc"
    "h+OoiId79DevYWsO7+F3OYZ9xxt1+KDm246D/M3wYc3yw9Oat9o8HeODv+9qhm0xi9Nomh8Ob+uEeT6v58Ovar7Af1PRa837NRyc"
    "KmLgP+cfx2lyMvyavhNp9gv4xe19iV/HKZ6Fb+ETZjX8HfwtohNI+WMdJnGKZOsPdUjSCWK2P+H3NKnneIaGv4df8FFxtNFPamAu"
    "ptOkSKNhEtPJoHrDCn5MqohLZfBjhkJVIR8I7ahIhin8zqZwKGYidUWYQKqTYU6fdYVgKoel/KL4G8Ox/MrYN+tUfubVfFjLNz2H"
    "i+PwdZYfDCcxPYdGwM/jcJYcRgS9GX7D3yP+i8HKDvGTx/IKP4EJ4S6P4Vc9rVJZy9M4JKxDr6wP8MdhlKXfkUA2PsLIHW9iJT3z"
    "LtqPDYoe7sYSFf1EPmgcz/BHWZ5Ay8O78A2LR+3fgW++xxk+idH3xyGwGSUO97X5Wc7TLIMSO3GI0mcuO/Mb/Fkh6XsEX+kcdvnw"
    "cRwCgsmnUx7DXix0dnhPfUnlB/D7NSTg98OYr+6L4VP4midJjFtq+B3+mKaqxm35iczbVzH7TIbP+/xZDp/H6JyLZvs1fZbDL+gv"
    "7dov8fNw+C38SYoZwGo6/F1MLxtht0TDP8J3mhRJTPX/gL9mCW6f4Z/gO0fLz9/jB7I0Mp5P1O/yJIWtNEwm8DufIuwq/qzgFGYT"
    "Vg4U/FegEfEvPlz5JDxOi6qOpgw6mFQ5WSz6/fAQyYsKi2foyi8m1yc3JjeBB2D6hSn034ifao5+sbm++dnVjVFI5AV+X9+8sfHZ"
    "hqLJkDAex1fj8UgFab6t0j+Lbn7+eQQ8qrhJGv1iff3GZ9cPdAqxS5R8bXLtBvAoQAxUUTUIcd0z+sXBtc2rGzdVgqp6c7JxsHEV"
    "q95RBd2atw85aT1JRmRaT9zyL26uX7+KtqCSokrdiD8f6XcOMLCDGwdXI51CpZLPJzegLRM60ILlxs2N8eamDcvNzc2bCDyBZRJP"
    "NibXDSwPbozXx7EFy+s3bgC027AESN6Mbtqw/Ozz+Ob4sxYso83ks/jAheXGxubnm1ctWE4mURRda8JyMhlfH284sLx6feP6xqYD"
    "y2vrmzexMQPLydXx+LMGLK/e3Ew2YhuWn03ig+jAheVGDOXGwJjcmtTZGJFS8AooZP+MSaNxsMV8DvIDlKBNqHclXc/WZtJ1cZqg"
    "8xzfzVKvklUv+MttiFJo0VQK/eBCj1rplvmatT+SgeyLlsLBdi3hSIpKPgyXDw0F0WJ2j0iav0fPpZHTaet6yJN7f9mo/Rc+ZgDu"
    "rJzt3b7HMQvduq8xWZ57mWTAG9UFl3vdopaudbGiMrruT3TjyD64VVwzdqOOFgztX5KV67zQ5PSdG5jlcTR95+rwnz6Xx8xhZ1tJ"
    "WGyZE2q37LYoTVWtzZ611zuzt3TV9siSeVx0Zs6BrtpvDYrW6wI9mVMbychbA0E1OE+9xWzE4qKMvvXEhapYR0G2nYG0rtpXKJiq"
    "yHbCTu6oTwsj9zXypNIab4b6O/Sm9vkFGVXSKDnU36E3tc+PJzun4qSp2cBOrytkbOJhN6o+8B7epRiwtf6O6x3tzW/sHssDHyJo"
    "96NIma8Xlec8YHJwyWo09k5zUhSoE4rfB15dc/kB1uAdwW2fzQM6m8DMB9WWCOM91Y3twKWxFo3DrqTrM37kV9nHTXUrB6Xqec+G"
    "OX5Vz3vi5MhgbuuQ2OgBCzCZcEosFqgpeDPZelb3jiYh0IpZlFXp2H+jtj7YuF76NIRkPiYqwTIHutWpv9UqwKu2Tl9IlsU/mCvd"
    "DWrc3N7ebEe84zByzg21U+sP8jjbauUGvdV+LzPZbM9k0eUQaINDRXkUhsByHk4G9N1nrp5T8LNPDRqNjMhr3mBsBAtWJbSvCrw9"
    "n7Z6PnV6VjK+013bJN8egLefg1Y/B04/onXxzkrg1opfu7kuvbV9RGFWIPnqhsSfDf/1De+/75BlVgJ8tBFWPJV5keCiv5lI7FVY"
    "DRz/ozxO9onPwq0yyItxtIbpsHvK8mF0Cp1/tAFzHAwGydbW1mherd1+Oto+m+bjCG8NIzjOc1ilXdZfRcUoLBJUQw5HX4HYjb/H"
    "R3lewq6kbqBnTBM90+hudpxSmSgbw8KPdukvpjj39KPHSXZUzwJ0bRYkGcsvcS6l7pGFWLMszLeGAcR5gB7BgqSskjJAY7IiL6Xi"
    "fhIV46PuinZPpVv2bH1hCpZWyVLdZ8BMndIw9qwMSgWE2BpFs7g9W6sC2YUliCaenc6TcvhidHsUjr7Efx7hP1/gP8/wnz385y7+"
    "8yf854+3Ry9h454+jmZULc5nsJmgvVGZHAI2jdYmSVqApD4COJ7/m/n5bR0Vlf0zzayfJapszK/zPx/gIE1P+0d5UXF33BV3wO1y"
    "c9yK1LaqPkozqHgHMvZxTvC/38v/9ul/L4E3z6ojNaFvogxGgROaJEBC5Rt24/m/4Ud0UKRTSkjx5zd1dsR/p/Q3OszLiqEBED+g"
    "usCa1fyVAVGWxDj5jj/t7tUsYQzcP/fM3XKn3Cf3yP1xZ9wP98HNEwiq5B7QkwiOUBx/Opt9enqKK1+U1Z3o9Mnk6yR5PVwPI9TG"
    "ntF74uHoXoLqSNRmJMdpjnhnB/BKkeaQlpHuZK84//ubdJZLS3uwzziS1gg5dFzCYH7+Z9RcIhJ2Cpz/j2kFBMTkY4tOA9S0VQCH"
    "YRfg9CDSY+IT8hTpjsEKAfDCR1C7zqzsO0kJwBzrXEB5wzOb4dklyap/lgzqMumd1OE+XRyYAidUYCsGijnDGyD1cXea4J/+WTUY"
    "w4xLDJ8wYDVib2ThQUJ79NkPoXZURbByhCifp88Qt4JMV/Ed4sAiHlvJLbzPAE7sRRYWL/NJINcz0GeRJiUQkBfJy35fVYVG1V1O"
    "b7S2ltfp2idn2aBISNLuffpiZ+1PLz8FHmvrN6O10a+Aa8of5ifAwMFwejBfwLt94omeTbbOSJv9qoTtiZc1afYKYEPXNkkWA56H"
    "L9heqM+f8kXPNK+LV2O0hQeCAeSMVOL4XUzSGIugKhX+INYnjgq+y3meT19h9ga5pEYyRkWqVxnVhV1SRK/4hoF/AxP7ikNvY0nE"
    "p8DTUgMxgIQ6goG+oh3KbZ28ynLg6mjwSENfmRnQT3salODMRdJMl/RT5kLfNAn9S2ik+imTt9Rrdyc9Zq4Ts58OE7WVbp8+iHsj"
    "ajIp1g6AdI/628TdiitI+AGHrdff3h6N8M7ro+TtW1h5jAFefp1WR73Rq1ejfl9I+OJWVZwKPQ9+t//k8QAIGSx20l/AKoyPFKlf"
    "MC98Z7KFwwufwPrPcPqjChWGpHJHJAT4B1BjSfxwjFhqCoz8MKunU4IzYMDx61dxMomApg031teBjk8AHkevZuXwRnIN9UCwFU9V"
    "kXL4DFiJk0wt8AvoDhE8HoxXAEW8jSgRqeHKAloDBuLOJFQZw7O6AMxAQ0qhhfiV/JbW+edRVc2Hn35KvMYR4OjhZ5+jOrWEFUb1"
    "MEF6hmhXT4AGDsOskld0C4dryT/FfHxjPeTt8ErmMxwd5NUR8sHQxhjvdGA78t5mK5ByuKGvX4ZnvPcnaZaWR3QKYL/TGcPnXSOU"
    "5imIZFTpsmN0saSHulBwHJ4BRJ5N0G7zlPj4BZbkjTu6+/wpxuj5Dm8bYTjAXb6aR8i2jhiOAwXH7W1c/vA1rPnHeAjRypBYqI8V"
    "LzUKdQbSCkzHvyYZxjNLyxIy7vCXyTrMUeCEnC/yAGUvkyP2JpD1kL/+81//H5ObY50nX5oE2KnFKaQ9K06D6JD2osoqo2Mc1D78"
    "MYl19jqDvXUXpU/IfM4/A5JGoRSQlgFLiDjss2wRlAERVcoB3gbkRZUDv6y8qILkqArO8FIJcObHJ0dJBqgU+A4cHv5t5J0i41hw"
    "/h/VtymTRccDElpwDnzygWUjbFFKNq19qfJVKghlSA4/JgKcEVvEpXHvYGH8q9JktTFZnyzKiSrEK9DZx8g1JjHAQaVICSAp2b6p"
    "/wR+BlYj2B3arCSH3IjwoFYWAX0PkEH6BvJpSYYmV1ZK5z8lnjiQZKtglu9k5QlN+Cwi+CyCxznwBJgYTIp8Fij4RRMAR3B1PShv"
    "BXSKOQeOT3CQAFFNgorODG+lgenjJEpxXkjJoRsQfAKCfYD3q8FRVGb/+a//ZxVERYFkJzhFBuxjHguAOJMNvc9fQZXrbnlzzxN8"
    "o6cW8/lGsMv6qyAtg6LOUO9B1g5H8PsJYMH9KRCuYhjgOPazaD6LXsO0nm+EwNiXAd5KIpWBFctiZG5eY31uHvtGsQ2GmnCTSWD1"
    "B3g9DE6O0vFREE3LPEDUVXK/hAQHarBmj3lHOwzGqsXGEPWYGkP1jmUQPMOu4UtGcnIEJ0wtJhpSlHpEJ0enZG4KQ/r66DSoTnKs"
    "V25b+bfzGM+agWAwhjZQeMuzhHoBJimYT2tA5yDaHSY02ENY0lJSyyDLgxM4pQDGozSGAgyyMjdbDKpYs4D9A4ip1ONB6E6TACkD"
    "rQFskOBZTaothpU0Q93nkwkCxgwYdlkZ7MlQWDkAYJjlOMJKQBXSEE6A6AOIVXtUUR3OUDYvb1D4WSSsKA1i2f3QAG582NzpGPJr"
    "OPbT4DSvA+IYoFnE2Th2gC6ZtzuIik6FyhnnUPsVABiPJ64inE5gWTd4DI1SAIHCLUcoWGE3trgnVqqUJjcs6KAMjpYZVcBlWjVU"
    "89Bmd61mR/ciWLDY3TeSBbsBENIc5ap4GLBKc6GqC5NDmIu+GhmME54mUazW3qAURgt2aRqBga7q1ZSKYh7oDiKo3byexoyTMKfR"
    "emuo5Wk2xubhT7DnAgGz7ifTuQzV4EtAwrRPiuSgTqdxgNLxqd6+DZi6u9huWzAjf2m40u51cSTXAAwqiFQGGtyNGZHo4nZZGTmV"
    "t4oMA+QNSgILyIQR4uyE2oEd55xC7gMpnecg6kkqKgploBdsR4NJlRnYw3LJgXSSNCdizVtO6pPJRC0Tgp6mRUhkMhmie7moBNpn"
    "zmSTk+reZFn+vJgOKsGfevCp0DUcXj0XsmZVOGCEehdJAaKHwsw7imNkaxFqCu3QmOeU+gzYnYGGMgwroxGV3IiQKjisycDtsESN"
    "yMeoUm73ZB14cxr0nJonwurIU0v1YwDGkgGQNd3MQUItqdqkcNPdAf8hs7CAxkUEaHr8wD0gVeHig2AnjplCI+SkTMggYtgJNhk0"
    "Wo1mBzU0exv/BsCI13g05zAN2NtW87vE9eC80IYRkK69Qkv7yfJHKBt6pjjDdKxaJgG/qS2blWTSu0d4xcP7kLSeQQ5EGN83UZpU"
    "xkNQJomgFOrEHJ8q8q5ngyXrCYbrwy4DWqI2P+VRec2p30JyNgMiDeuZ1xUZiAJmxQ5lOKK6gU7v6cm5WY9NHvScLfpWCZ4nwgvw"
    "QBgoPQd+VWEg6g0Ewy/YGpFPpVv7oVBX7sNsW1WKVROmwMFpwElWmWhKTgjrAlnMnelUStjNKJUHMuvy6TagUlUTqoLdCKtRqIms"
    "ngDiqoukMY6vqIhpxJSzGyJNk5r5F/ijPXF8+KCK7MN3u0RUImXbKceMbK2cOKEsNJZu56WFkA5+4AAcnBT6NPaVVwonHMYREkb5"
    "ba8RysYkPezyV3uJpIgiWsJ7JxYPFEgRZuOB3+M2Bk4jsGV21YbYpbPl6QmSdfakta0J9oOMWSyC/TCga7xmEbWdTTGV0ipq7S4p"
    "OmtvMi6q95Au6N1KuPqDDI6VrD6MEX40C1j9ciFPt1RQ96qKdXcKPDfIh0LGqbROCVgJ1KxRl7w7qDD+6ChHGspXTmlKojrNwqhO"
    "d8tiircoqap0sVyESUol5Qhto4MpK2VuT5VKhpIPC9JRfAF/TCLIMRULW6ndREGDeUoDkCQO+UgMNH6YDPYCTNoP/LA7TBLeUvDX"
    "Hl6d0Ohqq5F5XcwJOe/Rh5UBQiYmwx+riQIEC2wD/5pkMs1GnIV/9WnhzWgLMEZqcfIsuUIjIHWEHpoTAhTTOh1cQNQZj8wmVSop"
    "a5s6Rb9S29QUdDYqUEgQ1NPseZnoUQONr0kz52Raw9YFeFcOcmQ0UfyqciC4C5MxTSaIw85OFgF+YpNEn5l4WVLKL85SfAgj2UDs"
    "iA8FqgufJh0V4bhf7j24AxxsFR2WJg9oayJDPP8/cJD/3/8bYL8q3WocNxH8y0oKnQ7kHHVy01kOh4LYJNMvS7w0Jqk21CwJPSkI"
    "JkCTz741wxEe/B7Bfod/cCHEOqacLNNDBtRTjRckXZebjyspcwafi18aFGImkO3JsX1iH1gCBKqHSxvAUZzEDzLh9gG/wJKenSAP"
    "bQrRukOJB7TaDE+3BCTfQ3SD24u4uaKsWplCoFDhB/3wnUrAimseJapTlD4N6BdtNEXBSMJKjfCkWyd1/jPRl97BHwFpT90CO4e5"
    "zsY9EYsK1iryZBrrItMcTYqwDPQasY7pDBotoSbwfABy9PBUuA3I/B4iLp1hJK044LsGvRUMud8xlJ5Ch7mKEDoESs+iitBJYoWr"
    "EAFWUpZo96AK1bRQvAYaUJSD2h5EVfmxLsw+pknRzl8qQwZqxqmbz0zWc/Wta8U0MxBEIuGpPYvGHSNYiNcrXjOM9JpRPvEZd6QQ"
    "MxtcKma6Q4VQulb6Y0vo0RA1CPShwZ6URRDTwM55eSkxxJYOLWDGTMBmpaKOlHGIKbLclBsG68iLz2DrDgJLDlb6lgA196QJQ63B"
    "wGnnAdsna4E4ChgpIvQOm43roW3cRqszxAJqogvSjyq1K00N2L0ItYpKX3oLGjkmrTAqxFXxqNIFBkTbyHCmvQkEYwU92p59G+jb"
    "wYMKELvWjrCuSav/Spu5VTKl3ZW1c7LkxOwe6dHuyarGU7gkDAbBoxUwICVsmtVJu68/0i0OniHSSnAilOKTpDhfINik6C6Dgzx/"
    "TZvbHhGI9gNTh0tqkks/27kWzeUku9OnjOyhW0TPohInlu4aYIrktVW44KJnh4vgEOCCuQHaeC6pMgWpHk08kFaigE8IUaoKLZeS"
    "VBGJk8wmOkDJeGNFUZkaF8YJUl6jPNIvIi+OWE6Jwea6aHxJqY+JWtnwzOZWOUtfR2mQZ61rqlZJC/xY2lOYbhh/X6PJZ3Ua0FUj"
    "ZxQJ3RiRFgN1KOq20ckVXGKV4H9hdkbjJMokXdd3T+rkSKv38caBDyNCDY1lghLVkbp8WR8gaDEtFv0GUvmyKtI5pGzRpJMYLywA"
    "U8FvXBwsQYi6VCjUbZmvegaAwPBsP9q30o4qTgruP7NSoXZSZMTM3pVPzTc3y+yLpk0VtIroyyESw+XbykcO6AnyqWd1llbAek9z"
    "2neNIqic8WTBPO+aceKsk66xiuXAY5Y0zaWqJ/+xKdDoDxGgUlWoEiKuqiJFIsLsU/owjKVegrJMDzOiZWdIxviGhFl0mj7sfili"
    "14rj5wAghZizABcM6JA7X1K6ob2IW3OHVv1XgbvukHG/Uunu4kMWwJXyOhefr6yYO0YUPG+BlEvIsKUUL7NViDbtPosWUsaoAZml"
    "aq97llf3hOIy24B3OBNM8RSSg/eANYRHQBaBrwUGIMZHrXCgAIqWqsddJgYPfbYAwCXUdpBCkVkI4u55daWKsw3qKn+cE/6nUSKl"
    "IOzi3FDxFpMblUFwNxofta8lkLVBGp8gDYzxhra0rreEApWAdw6ixp2HcgoWBtEUNaqnWBpvMIxKSo0XBdRoKiPeQbU0tp/hBSMA"
    "FM2IUOY6HQZ4kyTMsF5IuhOArpFSy94e4CiDh1j5Id4kA8C0DljNG0aSTCcDZ00dmo66WiTgpHAn6EmyKMHZttjaUOjPAGGISzNw"
    "NzwvdRx7NrIYDtwXPPY1/yS50R4uTQG19e61uJgHuG3hjr94W4QWlA0Ns0Ddh4uYIVVL4I2rXfKi6M243WptTxsEqAZV2RVtyiXQ"
    "Nin4s9cDdC9hoUj8aWfddu454AQFvYc7jwM0S+urcnIjxAgPv1QG4MyCpapCUC8lq0fz2K186qbm6ZcJCqQ7ew+C18lps8rekbAy"
    "maKdahX4OO0VdRk9ZN7SapCq3cPpPxlXOc2VTtfOfD5NmQMOoJgeONHie+lULgGY/hvjCXNihGZTpSNAXtS/CJJ06cMACZHBJBjw"
    "pZzMhvj7jpnoW7zfBI+TCkq/hi89vUGAVoZ40aQaDrkN1TIyzYg2opIoEEMz6NEzTtNM31wKvk6Seem2obSW+O6jrsTWAjEHm4IY"
    "MKgDY0MCAU2S6mu02sDO8UJXQb89yeZS6Ju5gI4WyYGmurophcKUfXM9pHOZvInQMUiw8fnmYOPGzcHG4Pr68Pr6+rpvojioC81R"
    "96tnCCThCJaFOGWzckUyIVWzC8UiaGzmOisQs+FbXG5jN9I3a4DwztL5YogLaG+KnAQ4Cwcih0Z4ULFqNupNKsH+eyxOaf2ztIaX"
    "2NH0JDpFBgYFLdEeodiFz7+AI0XZRqQwpH+ziAKiI9UA+S/Ok1INWZYHbZjUCZF+gHDsTFgyp4NCK5RWQMEMWSMJki40QQImu+Lp"
    "KemzhAjAmOuKx++Img8mjaOsSa3YEykqiXMondmHMHy5UoY8nA7q5LDtMMj1xSgPjxTOaE0Ew7eJ0Otpio4yBMpf8i8lvEYCSQAd"
    "tdxzQE36uz7vMdrVj/I8K9Bci+aBCMEoQqCzQ376hqDIJ5OQtXsnqSAYPdITvKDl8cpwg2dNW7BUC9YHp5bRlN7V/KgLFT+K1quc"
    "KSs0HrLWinGk3Aw/NjY5tMBX0VDTPidIOosczZzowWCAhrG6EaWFt48Ry5VEwihb9DpDxKasfUDc0RqjdawueqaYVmaBImmaKgrp"
    "p4tvilaPQtzJKgZA1R5zHacBMUTEgShDECiZEru7p+iECxZ902pDwS1ChO0JPQOLpkPmq93zasYUEzvYXgP8RqPdWIx34yFrpIKD"
    "acTcHqJMu3QnFVaFmgLH1FqmI7nohVpm4rQQ1v6w7SWlbTodmZDCUltQkOmSWj8y72sjervhdyVq5FGsdTMVcBbXsmxBWpVaV1ar"
    "a2Y5zcQy/ZA6dpEVPH5o8/hWLwPUO44Bw8TpZKKsdsnaE/Hk0WnJmyfgaw6EQVVEp2z7gtoDudyhRBiEGNc95i+ppfKtOyctmFEG"
    "iz0+S78hsLMLVYzn+nzjY7LKb2GvZrFndKb27dVplp8Bxh3wO2y5WzpO9NAoc3wkd6hiQeNm2rf5TqKyiN3VJjaR1fi2WzYhsV1j"
    "f9yZhokvq3xeKnpssDzqKUkxy/vBaIpFfELKqW2pqS8jhkWeeWKuCN1mICkbWqrOazQjt3p1ZiE4Tj5bU2ZUR8XlyBrLd5kDKcVF"
    "8CL3Z8aEh191mjteyTdTUkcJtWo4QBJ2BnZJMofyWk8Rh4ztW+UrmH92H5ZA2/jb0nYkIhWgJoQPy/HMFfCjEq0+ZSZVJdsl8HUJ"
    "ovx4mtjJGXMylrysTLudynifKAoYKkR7A48u8hl2yaMZIpujRQCkb7YQiqxzKbOdPMVHwnQRd8rqtMC5kXbLGc07/fTlWziPk+xC"
    "pLbG08fq69jtQS5qY33rrbNi7vYO7XTyIGCecJh1yEmt/Az5u0bTfG8qdrv35EdgPyTRRfEMzqXkPn9jwakCj132IOIHIPzTXMG4"
    "7aHO+Onzx48fPP5C7ZLGEnOZvad393ae3qUyyZyOVrvQ/sMHu6qhzkJ7O8/3qZ1I7uEa+fcePH6wf98ChafIzoOHd+9gETLWhAKE"
    "EfRmv2eQU0TmJpyNvO0dXqyvkc2NZF/LApS6IBLuAfDGpJl7HcyShjTSKFiTXHkbl7bJ6FjFcjLdvSOMPhAIslPgAkUyTjLWxeCH"
    "6seMCO9zHsv+pltpdbnkZMv2pgLO/ZKAJ8cx6lMC6An7aWVbh6RZRG1Vd3XUHPB1jpiktF7r6GIdW5gtIHQpFgoEqniTcbjQeXDA"
    "eArP6UOnu5cz1iUyZwOCvK1afSzExBo+tiptOqOQMThpTDRu8xcTCpkcY8J9o3QW2DDDQaifqT/yHtbIc3k+xzQzskmVXYRNT5iT"
    "QJ6/bHYEk3yA8aro3aNMNNUJuhhdRt8TAzt1Jd5SmFtlH9OtEfJZbJGLhVgoouygp++1+42zMtANwYG6zQBV/LBlSy26RKaCqqpl"
    "q6w1sA2L6DI6ZS7xKJqTNcrQ7u85L+qS/tj3hXrQ8j17PIlKvcWAm4WfzV0GSVnVKGMkf7fgThyz3zfTWoRJ6rmk1WK7qDxHa5dX"
    "VoACkmlOdqjApo8rllxsOTKuhYdSugp66DTWMOLF71rwpMS3/VViC9PA3ssKMC6hBk1TpAbKAlWTtyTK3ZoCOAdWcbe4zs7W2XaL"
    "MWMrJgi01wGhGLnsBBWqIsrTuyZr1YdOS1+CBOdMB1930TVJA3PTvIgNxpeFotXh62BcgcI6FrFaOVQvUvfuWxZdDJ0f6ZK4LliY"
    "kQS97BzM0QVCrO8Y6Vcjc3B1XVGIq+toAVU2C3yuC3zuL3DKsgZdyJ+yvOHkR6SkRsNu5F90bplm40QpvUUvpRZAdEBUBK2zKjZI"
    "o3rovpCs2ujVKgoedCojt3Zp3eA4b2gGuqH2axhKtwEoZkIW/5BYAKS2jQpTn1jOHudlZdfF31bfJ7aloU6Hk1pRl1/Th2MTx52O"
    "qx2Cp5gIAhsH8G2Xw4Pyu/xAwfeb/ADLJGVbHSKrcZRMJ8qsEJAd/jRgyKD4OIk1q4CIAZli4pjGiaegxTR0FSZ6oZZFvym2NrrM"
    "RL22e5izmTsnGGbGXo3HLWubRq7P2kbvVrGFeY4IAbWlaK7SzN8p0qi5JfRNoDwWI2ubm9raRqabY/WSBSgtLstOty17pKLZqIjI"
    "ZGh0yJxh4Q9R8tKFLrD5dLWCPpORsXBUsKL7jypqYxCQ90JkL/gVuXpmk1am85n1wkO/9nAPgi4isEGT3Ghc5CBl0Kt4601Io4JZ"
    "Lsu2uV3GWrR2Y23ljg1TJFSMhnQF1dwTZTLMQM5ZxVA2TnmZk775qTy6Zqt01fN+rsy4RXRHelWYohayMaZWvxa7KWcJlbD63/15"
    "MuT/ro2o3IN7+7RxdHHlWyClnMeimmDLKKPIVxph9GKDZF8mBEDU77y5FVL206t00rrwz0audLJfz1HpLO/86gLVVGgvWM+JW20g"
    "fb92k5SqCn0NXERJghQ9TsK/jbySO7eG0ShAA+JnAvKwG53XoR7pxNoXXBbkt/SgUFanu+aXQffRVNRUO4FVOiA7NuGVqnwaGxYG"
    "uQ/WcvIVTsQ3CqizpsuokHQ4kMpDcEekbCeavJGGHMFtcHU20cBroP5Gg/s5GRq5OhW1REf4Ps40JOYVzRaEoD9BVbVUnEVxImSc"
    "ntbSLQydEpp0YreRs5U5HUFqcFJPm0gakCjm8JmjQp3HHNKqnDyBsK5LfjdI7WPBV/zL6ue+rt6y+ezqcYzm4szf3mG7RJM+F+XZ"
    "nkOWMMfzxs7FQFiIrcKRL1BvhKw8gQhBxskRFmTX5jz8A5mYl+KsQzEyOBoDklRAlqUGPwOLrx634bfOSN7MlQEfXbzCZtnd/wqz"
    "k8p9UGxdr0v2BLDSAbO09JRZ/UZhUu5xo+CgPpTibDVp5GQ2qFSmlFjisE7pUgn6AaRDv+wcEQT0s+O6yErb0Ch1bzrzZU4C2EeC"
    "cUpBDIESnEhARhfVTNbRqRfIil/I6MjQnZ/ANoeZ6kIoY+g3x3RPwORGPUVv1Ff9mHctmmWRJCmAfoj0K8UAfwV8y0o4WsoKPVsj"
    "WmDU3Vgfkvcx1eZnA/HNGvRIjOubooIjbyf4OKdibgZ3dGiUHIC3mm/nkKORdxdQTwRv+xmPmi05pUtOWOOIX276Y6DYasswvdMX"
    "FQLaCg87lRWLAdkJfHldFekhvR5RcGn0e1csnpS5vxp9JuKsab1RcddzcYdvDOgeWR+8Vvn2nR3uiM5aj5vXEktLP+IT/itm4uSI"
    "QzZPSjsZkkmWbq6+GT6idU7aS5qLESRuOWRFyqHTAuuZlELKzQLEK/rRPf5ira5VAr2pkEoO3W3x3otOWZ3vOCQxOc6A1cukzPh+"
    "YKczZpTC4cCEpngg0XuXwnEnqGN6dpJLcun0owxIUd2cRUUBvZ2kWUy72lQBIQekOiX8R0hCTT+oSkDmoWRfMkiKKUCd9CNOv9h4"
    "HL/cdG2QTiiTUJU1yYj8aIjVAHqnQYzWaHnfdTIVkO83twu2bbQaGhpTSbesMDJ8iwn9z+fK6kS9qQmV95m2LZQeGHmpoTde5K5G"
    "veIqnXyZ+R2ydJHNh1a8h7m4gcIeEc2QARG+ShoEeyiRocREljdsdMSYiM3Z2GWg1Ee2jfQI2EOZ88CxFD89w8BDBpMNgodkwxBp"
    "Rp1RGaHdLNdzGAQ7pgT5YBqj1MbM4jG65kR3x8Hejkrf21nbvachA0OBOSu9jaSwqvep9EBaHX64OFtIqSxXuYww7HdxRFXQauJR"
    "ZNuL6roAbYNptMCmHsdgCUgkCw3F8Limcfcf7O2bgupgauYID0QcSwH44lGgssyWeNQ4aHfRazS15MBR85MzzYnLczzPee9p8o+2"
    "Cn01fnW1YJQ7mGBnPskULpk4ZWjDTMSMsNSzRH+BZNwySSqU3PB30Ptl3ykg+/frCLmUE7mxouefrHqf8fPKyBiOoycRvJ6kzcsk"
    "jA1nzHMfOk/SYYkxtNQcWYu7XzF7cJt1unQm5U2AnqtcR1u8EW1T7BwlhZqhyj4SAw6bhKBWXJcGIuvalen6vMjH4sVFDGmYUpHY"
    "jvaY+3La9tI5xWwSN1iGsrad3nE6a47NCs2du3C1CyzkpbhT0lDbRE3JXrF+7CoaTmRO+e7nvooGSxXwcQTxgub9NTJ58VRfQmbq"
    "dt3ynWYVQyMSMuhLknlz4MdpmR5M7UYHR8w70juhefPKn4hSepzoyxzXKADO/Ld1WiBStkzrLT0Be45TPG6v7A8aIIZuY3rJ2WgY"
    "pnZEWWwBaEGaN5e4e7Jt8DXf3PRZqNPMetIZJuWwWbtxXRRJNj5tn8q8pHcNQ1NwUBql5D1tkY5IAMMbxMmi32hUkVRqCmhT0nix"
    "wIpPR5wYBG7LsBlY8lBtBuIky/h+EtNLdR6ANqXj1+ycjd9Tk43YWAgpdU4hHW+59rCwgEAmKhmTA1a5zXDN04qEIhuSWypLjha3"
    "dWR2Duuml1RddBSsTRdZn2MhBunE8RmXW5cfehB60zyzl9HeM448T8rOCi8BeKCiUkjQewd5oMXtxwa3khCcHS9s9PV8LkI74x+k"
    "RKynUNsrS9iX5FemPvYaHYOkTKHc2JqtSAC36jM9zflmgUyjEjQXiygmLGWKizG6qWJnY7JsChDGUWlwhV28GK4J+WV10XWHfzLA"
    "pY3tRlGRcZUhO6Jls0kishYSp144EmZLcLnRn5u0QdtpNnAbtrp3R4/7Bp2wMUtGmCrhn/jqE9i+gfEZ3fDkozTomGVfalAt9i2t"
    "TjD5KdCUDl8tKZs+KtzldYgy/X6NKMty6kxHekqQZWNUKqBcVtP0+VNl2XaEFKNRZbDtjfH8cBDpOtZjdo0MLJ8gVEa5vzYv1JSh"
    "rQyZXEbRcGc2wNg/trjZcOvYDrP5sWWBNu/403qFw/cwUsF41KYKdEHMwl7Q2wyv3lwPDllluTm4ejN4fdhXVbt8IRk9AhXT7rjl"
    "dQp5lmCmWT3kV6/hhNoqZxS8LuJUwOK1e8TYGvUj1z9RDGDfwEn5/uZbhHRy6jr3U9wWNwBkuZSLAKpuOQvv2G+O/3DPpmu6E/fv"
    "PMvBuDbUIMNCdWjE9tEUXrLvjEvyxq5if6yNHWi5LPdZwzrFfKdAEy3CuGKSKZ9M9jRbIfevqgK5nnvGL8T3tKtA3ATG7MDiScT2"
    "oCQUNrAbQkU8d/yMv5b3O1ZW9baF/dAQ7OMzIScLu5a+rNw1Q5ooozRdCtl1mRKheDTbZwEsolc5ODiape180vJsOGg2pt7AtVpD"
    "U3RszXYCaKY88K2MSw61QZMuV8+f5Xe4xB/pHSbqkOa4IMpLXlmMB9/WCGRCa18Toi6PSPywL3sc346IdLalcl2Q26OnDxEAXCiZ"
    "TtbQLXtiORwtk+KY2XqoI04EEGyQQs4PB+LQsOEEUVJ1KaumBRudjQa7T1hzhG9yKYiGlfUgU7SYstPM4l2X9Ypnkt7D41+d6n94"
    "yHnab/ZT+miMwgzAdIGM8y6jE8sjp3koyQ7x5UmbYBquSjmnzPPAhzUG2+Equ/RwKi55WGJBg7eUGT6U0DNg19aeEmYRsAisg12G"
    "B+a6UTXDs0vy1LjkV+pbGKhGUYasdverFlgfaFMqic3o8BW4tUm8iKQBD10YqNCuVR7N9cYG+ZydHJ0udFmNa8YeXCM74A3eUSFL"
    "IL4XzM8hS/4kd9BISMCos3wCOwLVLGPatnjG6C6SteE8ZrRhYpYPr4mi7JTkXmM/xWoyZM8TZYcjm5neqkBFfRH0EH7UrL6ldOUt"
    "CUO6BNNGpljW7iijWpTHSFyqSCSjMiQ63M0Opyn7V8Y0CiSFjeZFVR/W538FjuV2EZXpVFeTNz+m6UmOHujKpodfNSS5g2ApC9DS"
    "DHMHwR+ZD89RJ4iCCfH2xnexNKJxKXpRS78bKCy1XwGr3LJqxxLla34zAn/YOk6uiDBPLsxus1UfpmTM8j+GP5JiVBcsUvBvXVyT"
    "I6yCvm/y8WtUhAjfZMv8dJ0Nq5no0dNSDtbpcnJK0m+lnZ87RTa6bupMkU3W6aOLE9GPmbyrTHEKyyu3ybxmMllf4ORet4kV8yuY"
    "uf6+7v7Ci17+sft6Wr0An3KAFHnAtlEcSULBdMPhdgbBynVBQg/NP84tx00Ca4cK4TA76JRy/9uzsUZfjWizoeErX2tDT4um0yNZ"
    "dhjDz+BQ71ik6FFf+50AxlXehdRoZskv32hO0XGexqhxmCekVJsDTzCvylvWi9JoDomwhQnAiN7V8zxsQI31Knl5ZOZwpu5GW34q"
    "PP4tSB9V0NHF1xtze6nFQITf54pi/1TQhNkp7KHYXcxrkVFCskKEX0FqJREyNrZ/bFvxpa+Xe+b5E/a+k52O64N03B/I8mkfFrIr"
    "5N2hVty11Zp6fAdaR1IG//mv/xE8rTP6Kws7DNBAUtdU+lp6+Fyaex1Cbco/upiaTCMDhuuRNhoSq9ihmGrSkVGvL9hGLV/iZ4Ma"
    "O9AWoHS7JNqgUPR5FPDANaHUNcfmZmyoXqWZQ6tDS+jyYrzKvHjJ1iuTuiCVG+0jy1/2IHia5Hybr8+5oo+8IL67/sFoEe50h9Uh"
    "oa0RWEdFYfNG1oEuSjtTx9ZRYRLboXV2I6CjhwC2/ILRdRA7wPzxBuw494TYmR7bHTWC7ODfAP0m5xkIGWmctwLtHJ3/mb0ctwLt"
    "qBx+GqYD7Zz/z7Ij0s79/JtkSaCdJxmGPvQH2UnO/+383wF3xTZBc+Ls3M4P0ixqB9p5MCPBNcdwhU6snbv4cf43jKMReWLu7HxT"
    "l6x5bIbcAXIwTssIQQ6HKoOR/d+5P+7OzkGRFoFpqR13J8NTmC0NvLMy7g4GrbSXcEX8nSeGO4SBYzzLOSx1UgcAfAm/Q08wosD2"
    "5J8h5UBa6Wy3zjA8Ed3rE4wOeGGCKM3iiPsE4nSY1744PBQaFN8MRMsD8TyxA7nAHoKtWMAuw5oZbiknFk/UiMRT1qh5ha11/m/w"
    "kcA8j8//lo3rae6MN4ADj2bt42gWYCDDg8jqNAxAsAYcNTs4/8ssQPsXCTeK/+SQ54nH0z1oHZQnaQw2wAfaOLSkMerWgAYBbmhK"
    "lNHkNEQT/mZ6/ldfSB7gxalgjO1DdW9cnsCJzJNGQT3jvijM6jiKdSBIBKH41Uh4tfNJgs/oYElNrJ56FnyTpBUBPB/jJi5Uk2EA"
    "WwzrqXE7oYfG7DcSlgS2qx4yVPkW/QJCZ4gjAOOj0gODgs5gIx5i3NVBcCcp8Zt0O2qsphf4hQFFp5EJ4uNwmnzRju3yxBOKEIB7"
    "JMRO5ZCH5EVHISu1mUKyU8LLl4K+AbvCsYfKWDqx8ZA1IihYnf8FLzPSw/M/r02jVkSfh40jtiyuD5TakHLLA/vE7NS+0WQzsg8w"
    "ZEDOsbCi6jlemLYDyfgC/FDl8uKVtdy/JxWdhaE9Bigomqbf4UIvifazI6UKb7yfhwkhnhbm6oj487CF4NQYoo7QP49xpJM8DeZ5"
    "WZ7/7TiZBhSWqtVjZxQgQAVFnuEMBIieWEAP8QLSwtyHOWIm3H9wbtEDCYYuzkvvKtjnIV8eFkgPBYEmbeGByJcEB+LAz3gHZci5"
    "7KRoaZQgqRjZcYIOi+g4ogOkm6OtUCLHYzdtTQoOTkGbDVaLD2xr/vbOyq2scV4oUgnoXDcqD5ka8YM0GVsx1c44QtZCJ4ECW0lo"
    "MWY0xju9O7CQ4SOXb2k3vtATa+MYeo17lpiCw5rjYnsiDT3IQASdIb1JUJoDKkXgLIGxMDLZTOFJmNV4miLZgTSUrKMCEfQcUbdF"
    "sWjYRPj0Ifu2TrsiD3EAbad73XWcoKbFjN0Th6jjeNrdL4lHlHUd7rxIEdfH7VYacYlo+JEUYvB7wxNZa0SdItcsLQ+CXUA/QP2T"
    "NQ5dZEBvwVujwY5ARTuOpoL6SGl189rqSJjEiB+pdq1tu69WsCJ33kRU3bDt3nhFj2qK8XdQl2OAcQ17ZTZPEK9JNeZMyO1yjrA3"
    "4G8FLLowXrZjFz0iJss+XtMUzouRfm4hbwBNxsw0IM9cGhLRGcSIZ+wPYoTT6g5ilKsgRlOKYMQMCvJSfy7SHEH0i+z8P2ZJka+K"
    "Y1REhbVVvZGMsMgcA0TlnYGMnimwj1H7/K6xjJ4pciW1Um9Ao3sY7H2MQkpXOCPdzkQX7YxotHNY1HMvDOygRk8KoATeUhzYaLeg"
    "cETOkHRgo7EvU0c22pmSd14KgsnFPo29VawLfd6P6K8PMOQxYgF/hCP0BhDRq3EO4N4Z5IgbxAW0+EG3LlJP3Pmwwt1xjh7CwYya"
    "O0X5RZLMSWvjO2GOZEGGAaP4ZaGOdFE6CMsiHemSq2Md6aIT3z6zYx3JpsCQTEvDHelyKyMe6ZLdfdshj3TxeVKScF/5ashzardw"
    "XTJt7w56ZMqjVjotsE6+LPKRrnD+H1NAit7yKvyRAR3tKUgeR+34R3tFUuWt+Ee7afZd1A6AdBsQ9DhvRkD6KgE+ZXqUe8IgPQSa"
    "kX0TeeIg7cwikMTydiAkaC1OWoGQdr6rp55ASE/zN3krDNLTvIzaYZAe4ZOE2ZI4SF1hkLSQ1xUHySAsTyCkfZSY5eh0hUHSBuAN"
    "xaE/FpLBzc3yvnBI0D3vka5wSLqAHQ4JhdYl4ZDUMSh9MZFYcdgVFCl5D1GRgA+jwTWiIomiKDiI0jd5IzLSt8B0JsFx9F0aeQIj"
    "3bVrDpkHQqvTNbK+ni+NjmR0EyuCIzHIWmvWFSCpCWETIOmxOc8rwiOJzBITN9kVIekubYCVEZKiQmOprihJOygNRrrYEDjpYoYQ"
    "ZCUPqzyByMGSFJYIEpOaT0uG/ihJ+wkpxY7ybxJflCSVLSr02BcmySpDVBf4/LnS6U2T2UGR0PLooElpVHqDJZ3/D8S9+LoFRFvS"
    "VmMt0UH5AycJC9GMnKQ3j+bW1alxoifdIVmrYKoyRy74IJpG2fm/Rc0QSlHhwLEZRKnwR1GaskuwVhglGnXhi6N0B1jvRraKh5OO"
    "0SGqYuM8i9uMpjQmZmaWEwTNEreDKglvE0csQxiA26GV+Iogy1fFVpo2AysJ2soMcEM8Nb7ASlFJtD0qu2IrRRz/qKZ9NggsAfP8"
    "L5ZqDTUXpF0puqIr3UkPgfKidldEDZz4YauHpRGWWN8d8SFUwjAph0X5jdvv+QbFWTr/69qU1mwSfQcVEGWKJr8ryhJvgmaYpcy+"
    "rb8LTZZRit2wYEd62ON8fP5XUa0XpOXVjLYvzJLaVjjuLD+OzP5Sfdt9rgi4dEGQUNilJSBRQZeiYlnUJdQ4QXXps2hHXhJ5PeWL"
    "NUQnvP9QW+SMEDUY3VGYTP2loZhUsX9PfPGY9pkdCBAvM48JH9fgrAFUo66YTEggucTKepa3ENixOdFNnLxUt/jrjvhM4wQQBmvf"
    "L1JHJq5r0c0rD8qhsc2QTZY2osRgTUQw2HmhIvae0E13bUa7K3TT3H/duSx+k1SZ+etYYZxi9ErhD+QEuzNB1Ggutr3RnBrFSH3U"
    "oXPzRHTS9/O+mE5P5F6Kjn+uhF50e1SlmjrYwZ3uYQYsgYnuhPgDNaYU3gnNa0gXEwbl+d8BYWKyWlSKBYUmW1lnT98n2JNQC0lZ"
    "HeypI9bTrlw//kChnjTqaI/TDfTkXOp3xHoyZZaEe0KlGSLP1NegHfQJykXFRcI+GVFEhX2qivSgPv9bnJcdkZ+IVhDVpPBPdWCp"
    "QwUScs8KowDwF+8vDlTnvmi4ZS+6INQKV1MsDwb1LCXyqclhviIQlGJzkMwkGd2SM2PaEQ9qLycjhQIjI0GNN+Mpgp40xJHF1vri"
    "QdE6pYURoDtCQqlytrJehYWKk1Vhoe7qSdA1lLmFMwB2r6FYp++5pKNLGnwoPCZNu7kcrcuadb4ZMqnTpMqLxjUXMo0FdESP/lBf"
    "/A0IGRldtShlnjdC1P7532nax2nJtiOWK/loCNwRfMasw7cEJhRZmH3is5DWHCYqt4ziaH+z1h3R3xxtDAxEfMGiXDYEwcYMR6AP"
    "FM7Gyka5bgy4LApsbox4+O7AUYqP827/RgSpnUNgrWK5E7A65ssT5hqVAcfS8FErG8ovGjxKnUY2NRDwGxUAnT17z66OHlVYnueX"
    "NZp3hY96ls5zd7+vCCI1y6GxhzuPPUGk7qq7vlYYKT4BnjBS+7BvolYMqV0KIAej2tl74A0kxQxWTAKXvadmS+NI3YnagaPodKt4"
    "NL4oUnuoWRwfJc5+oQdJRYWcToMv8AaUsm5hw8DCCPROEyEgkgxeirRmtKuuemVNfxM8TQA0TkwpZrxr4WdUo8AoJXhZzTgADb0M"
    "WIOero66lfQw7w8sYzTe8roltuJi9yIwShRKgGlCG6agiRiacaR2Qf5m4Yh6zyxw4+yWBpJ6kAHBwFGgi6soQKMigLfdAlMiti5C"
    "0HFBDCo1J88ZyWw+zX1BpTxTlQF2TzVfGk9qx143IAMgCNUagPQ59mzrVkgpz/VnNB2TSFdINBx3h5DlGtkgRF2RpoRR9AaaemAk"
    "OhEYrcaJroDEM6fX6oSIIrpHVIIMy5pFGGR1No606FlaHt7xZCRDun61Lq9pNadaYsY+0xmSIjE7QAqJ56pgWkSGXcCSGaqJZMxY"
    "geD6JW+iinuzmYHjKOUmIqgx1TI6nhkUI9g2zhgm2JsLyTDPKGgAJuSpTCMyzwdGRtkehrjSrqEKXseTadxx8h2/DvHHonIWIg9U"
    "aCpHpGeLi6Cnl2Sml4Wkuj7tVTknkYpCxVpGTcghy9jMu0ZCspuUUQvME7YvWQ02p0QNmVkFO66hJKAerYaYJ3AE3yVo1U4OrM1x"
    "3oxbhchOqcF4aqiU9UWv2j3/ewyYjQRflPdw89GeMahax7Fyjq+WsnNbdVae/wWQGUazEpYGBrIimNX3Oc0BdaDorT/CVTJGJAUo"
    "fwWP0hXgCutzJV98K03Qgwd7/ghXj5vQ8Ua5GkuUKy0y5E380Ah21Vo4f8ir6XE+hDLpG76cyfmgzyI7opUOeyU8Q+5S2I7AV4XW"
    "0zWiXz2xLJoe7JG58ri1y8RK2bVrK5Bqxy4W4dOnlliMYz3EyXRySUrcCn6lsCLrE/l0RhcNgKVECF27XFLdioLl2hTp2q1wWEsF"
    "mlALNM0+BwHJmXEqyicmDnyUxnKJlQtFyVshsb7CneMJiUVsk6rdCIl121hHSYQKNy7WnrZ1tC3f/aGxnKXIV8bHuu1ZwHxZlCyp"
    "QDBsRcl6VuTjyBKynTBZfGXijZMltylG5MbWvWGynljExpZt+KwaFgLJSlkDl4qsrCXLG20/y4toT4s3gK04WQ2DPXu6VrAseziK"
    "edRkHjGhdxieyFkEAUaddpfeuFl8BecUXhI86zZfIFuqUjd6lqJ46jQCtcQHxczkiDrEH0rLa9snVnsdwbRuW1oD5IfE7JWgI/FN"
    "yOKbNR+zjqBanJBb6E9U0I3oWk+AUpRRR3yt9k0HMgLA+xmdrCfclnCWCPwYmaf3FmxrN0JemC+MkwtE2xpT+RXhtriQN97Wrr6F"
    "6Ay5Zd9JNONuPaPbdJKQ4DxN+Ra0MwDXw+QYGNllEbi4PSjkvDDzhuDaw3BfSHbHGmTdEbhyxxiiMwTXA72sq4NwRd5SzShc/lJ2"
    "GK7G8jXicAH+FfXm0khc0yN6a+VG4toVpBO7l92teFy/Z86+cQzYUCLyxeUCQnRY0xuxpsjmDc71UHBxmztrRegiNBQhIxJlR1Zz"
    "OkYXt0VTMZdf3khdyiTCQQ2+iF1SkG0g3atIb+guVmM25uuJ3+UtZwXxcpZ2WRiv5uM/bzgvPg5oU9MRzIshh1dXvnBed5Jygo+1"
    "2gG91O1blq8I62WJlHkzstcduqtOimZ0r4cN8JgAXw8V7bxEiC8VfYvfqgFK8gf6uqtIviFbXdG+bvuuMDqifZEawhpBV8Avbarh"
    "bdaN+LWrNNf2FS0bW1DYLza26LfOoS/wV+NRKLIkyWGd1lrYL/hx49QcMfsJgNB398EBSA/qEWKEUhgcyNoXBOwCfePUgITUJHx/"
    "z47tWGD3QE5ubUs3FJiWp33l7PBe2BaN8jhtNmYX0+21yypDWA2POdqW1qz+qNTdtn1PVBd0d2zriqB584I3KtWG6N4EVjCwHRvH"
    "ZwbR57V+lGlapEJ4SqQBYEVZMlCUKPeHBFPHvbWhlocGQ+YAQ4MZ6KCejYGYOBjIGxjMmZp6RErqFB/R0NONgQG1cbW2M4hJaegL"
    "FnbHMyR/sDApqfFYR6yw87/lyly2ES2MqROMGyOGiflfK2KYLvS5v5BEDbuLqxFluT9oGD6fCOgFmzsaFTsMLzos8mipD2lLqCUD"
    "ShV3xxHbaT6GVTw+7Wd5XabfhrGalF5npa4ic1mEMetZnNPXkmBjxjK+EW7sgW/CzbBju3VZtdgsO/bY3aYZsBt/zIwCgIcIIVVY"
    "yB+HDK+/ebHaHZpYZHdyZcDGNk0g3h4go9hSVblByR6johIWb5qkVm4rKlmZYCA5uZdbEpDMU64Zi+xpArCxH7S2w5HtIVBiks0m"
    "MIeoOxSZw+51xyNz+bx2ULLcsiBbEZVM9g6OjRgPxJexbXN207I5a4Un4weNRg+uSJBrtqab8AYqIxuvxlitUGXERLAxwPlfAD8A"
    "QUqVimfSmESmGiJv/HTLOMsxzHiZHxRkv1KhdZYoRckSMV8avyxlbicvl0YwQ77VBBxL32f0stQbvQxBYkBNZEohPk/wslpeLjnR"
    "yzxTk/hlO2M4aZl1gE3wMldZwmqiSIp3BjDzLK0Vwsyfawcxa24/E8bMOey05ZcGMpOTShevkPKGCa1716M1SMnM9pPRiGcGgjn0"
    "ZgwK9IMQT1izvOAXpxhDLDIEI2tQhZYnDOSvBQE6+C9u6rQ7o5zly8Kc0bCWhDnDq5YK74WIJcOnq99FF4l0piwpm6HOnrvyOdlA"
    "lfw8YGzVDMkNBYuKcsjRso0tg+XOni5B9d1dqJjymSZA538bp7k/CtpzDzuooEwh0Bx1nEtsusOgWSZ19poCC3cUzbyrqKyJOgKj"
    "odafmGoyU7LbRDmXn3jQ62Ln0q8dIc1mAHCrk9WtDSVfuDRG6napThxjIqdhELTzvwMFtU1nHALlRlFzeIXSH01thR23b0BuYLXI"
    "G1jtQZvIdkdXszkZJ7zaXlLm3uBqd3zgtWOsIb/VCrLmGZQTaQ11ZEZBgsa4Int5Y62pt7Yzm4A0wq0pO4J2yDX1TN7xZdUIuiYu"
    "H8r6UNTfMLwiAQGRnhSgiHUwTejxrhN+7a42cGML6EbwtS/qlG3eLAMfhkgjDpsRstCqvGTzCfsJVO44dehwJWK50khcp0R4maBY"
    "IjYXa2GCRmQ2fieTo5u27imYGG1PSu1RicYlBuECTHYDQrKCv712zLan4r6nxcmbwG1qVxzk4qeDLvMASQk+Uh6A9EWLug9x2X83"
    "ktvOccoKaqcch3OLPPHcdjg/lgNckvmXNjI3D7eA2aP3YLHgdq6WiFzLaeYRYu4L63b+l+M0WhbWDZ3lEj+gzPEN/dfOGaCP1Oyr"
    "eRKngBlmGlYdYd3MOyN6Y4bvnlgpodslCoYDXBrfzWW1FOguFudNszJqTy2p/dh7Y3iBbp3Qb/wOsRX8DVFl46mDJ/6b2p25+zKc"
    "bAZwAysili+J/hZ1h3/LVfi3mTf+287sIC+bAeA8/qvaYeAemRdXGvuwB67bmpd0Q8E9Jw50WmeREwfuDvlPo3RvILi7fP0qTsAS"
    "dKICvEDINkdSLzgGVpjLoQ0E7TbCI7Ok1FolcjqWHKLtTVq2Y8HdfZMepDbWcsPBKRQu+kvxb6bnGljPGhilzrqCwu0YGPmjwmEB"
    "09zQoGNvYLidMpjVMXEIGO5sileh6j1gkCgLlIaxSCsu3EN5uFo23qC2YsOlcgVsnRfypYL9FApNwW/GYpH9JJPFU0RtaUkIsIYM"
    "sRdEzatUQcwYEXqN5ud/R79Dxq5WmTGFZG9TJlP7zSxJynh+xmQ7c4fMgeqZCQ5nmQYpLap+sTsInlslxyQ5kxJLIsglKoQcZngj"
    "yKVRO4IcgQtFCfUumDrviCJHb/ylYGcYucIfR465VxMGT73x8weTs01iVwSTi5SRW1S0I8opK/xlceUam8V+ojsnT47GLd80Uv4T"
    "1bnqlSQS2NJqK8Yc33ad/zUbp342QIeb0zgLdxfhq/GKujrwHExESCVeghSs5OyIP4e8gbZRxqnzG3vrNogFkrx5kNBjFBwKtGMj"
    "s0p+2igmTPRQXI0BdmHkj0O3oy4UrEdJrUB0NguofGWq4aHryyJwQTNEg7Q66YpI17Bvk8B0OT18Zj3MZaLROY/IWgHpLHrpNyZR"
    "W6jVjHbxbpo4yguxvyfhmG3DqvO/0OWKG6buDiMWrKUeUuADLuMXw4Spw3PcYZvii1T3iKwUnQmh2RuaiHoi1anXj1ZxX6S6J1Zr"
    "yRtg81wFkB2uDobXK/sWn78sUJ3TLvFJ5CY0R7tfF+pqA8opty8EILcVrq7p9tcNW6dPLnXiK2vFr1OFxyhyNsQfw5Q04tjdyS8a"
    "xQ5lGG75+PyvcBzzUpTlpc3tORcegd06SNfozj5P4ki5v4vcI6RNtO0m7jpGb8TnVGizhxvy/G8Yxy6/pW9qMYBdooblC2FnJEl9"
    "6Ybuj9Vr5Zz8hYtmg+83EfDsEta+dHQvhpjZkGh2uOjqgZnylWrdz7Xj2e20F9feYxFeMjrDkoGX5CBUDT/O2/HtMDAdyX7azr8r"
    "xN0egLSmnWZUTP/eCnS3Q6HysEUMdSem8im+P6BjOyRRx7pCdULe7RjFGCR0Br4jZ2NR24NmMwKe4vOUv3NfELwEf1biH8Fq1x8J"
    "74l2mwu4EHZ41DGSQbAfgfDPnkxj6QN9GzR68YTFMwOyynmj42nfCBQiTzT07Rh5Dd9wuNLA+8/c2zY3SJ4mAxl7LLSFP2XuG7Wi"
    "5Tku7S4ZK0+Zh0fida0dLu/8/4LvIm/Ey9tHPlfsYqxwebfpeogMyo3rgkbIPPJR0rjybobM06b7lpFrO26e8ljYip2nq+fk3rAj"
    "gN5uNJsDjqNUR1HVET8PpeeSXvKgc0WMmMfh83D7YTC9jvh5Rtkjfkltt3utKHoEWMcnETluUY+HxZxOTOaacfT2G9JHL061ippk"
    "RNUQyjbM8foD6hG/2PDsa7OPZmfS47bI3FR5ouu19+e7xNbz7tR2eD3b+0V7+1gR9jq3qhNlT+2khF2ddbS41LbeF2jPPj6+OHtf"
    "SZQvNstWPNKSMHu7DRe5Wr2VshRsMVravsc46OkIuLe8+0aQLH7tc/FoeztmRBNleOqPtkfkRB4RofD8jDQHB8lsrazHCV3ox7nf"
    "me+SqHuNVhtXkc4bjmBSZyRWZpqSd8TfE1pt7HQ8Efi+kgcDFT+kV2Tb9sPiich3J2GqYFvIUFBw1+1wOxyfeFamoGD4Jse2jnBj"
    "8BGtbkbh4+s+X9wzp6aGni8GH5Dkjvh7d7NKngoqjwJdvenYe2tdwffUc21P5L3muB5k0rc1ZTvyniiNnedT6iyJW7TIxOTriMCH"
    "564dhE+ua9DvFTmh4Q46Y/GpN3Dn//MisfhoSnrz+SLxoRYm7wrCp32RN0a3NBSfYClv4UYwPs+Dw8RdBDsu3x2yVWa00hWZj3Mb"
    "0OmKzLfP5mG0TTsD80UetHSBwHwoQeV8yAgFoRLxGK0LOKwFh+dTm4Yjgmifz6grRQyNj47JMGKWi9msZe9KKknBVmUtT7dbofke"
    "xGlOd31OYD5ODUzkDV9wvvM/o7PQHyg8nzSOiio8VqkMqHHxFyuv7oizUozQhz46tC+O878wyWLtmyOcCpiawflQuZu3X8FY0fn2"
    "0HGZXBa6sfl03CUrOt+euFtqR+gTkWdMxvhp0Y7Sp6rS6+P0IKHXntppgDHBUJsPEVtUtOP13c6jcu0YdamlDg/gidnnud71RuwT"
    "IceN2Lef1KWJGuEG7NtvKE1aMfue1aQsyFm+USH7fuRr4oBsVukGd5rgDlLvlVBDjWGqcjuK324r3sCy1bMxhvAJBXu9sBwFynLY"
    "TEVCyI+pX5P2LYnnZwNhLi9oDE9nBbBAhSfhFXrcm9ccBkOFAyFDHuCeVElxPMtPXJPvguQ4RY9v0gEH+EMvbOUteXYfBhGH9Ruz"
    "g6JjmwWTVuzgfgKCNb5M9zkbCv2+iQbBfVhcvMDNC1tt5jxWRnSKkRnVmx/HmEzCDrkLTRH+dpy9zIbqxneUmCQ7nCXF/et0x2QF"
    "/EvscH8PrE54hUs+6+OKtVOOh6OWurgz6t/dN8m4RvbrIqH/UKAi5ZwJyWPOSyZ3Ak7kP8viXZATvgQbKotqc1tg6ZbJ/j7r9Juk"
    "AwHuNBVrQ0uTFip9ZtIyJdPxAM3t6FCTCHG9EcV2eCs7KiBhp1S9g2emW67VTVgKjAgIMqtE6SKsIWcdJPdSHFMsNzMZjBa3EBuQ"
    "w5hvJr2kf5ZOeui2KJ8EyUdbIxgYMFGjt28/SgbwOev1+0WCAU2B1E+nt+B0BNWWygIuDRcn6Y1ejcLR2qg/qPKH+Qnwq1GZ9Pq3"
    "pGa1tbU1mlfQKOkxi6r8Oq2OepAEVbZHRLNHQyqVZK1SSUalIGeIQ1jo4T+C4YdVmPXPpJ9Et5Bwj9judjKEeVb97e1sMIvmvW8m"
    "fSSQcS/Z+s1HHyWQjlVMq4+pVd1mtZ3oWX76L2e9fzn5Vf9fFp8ehlAq62/9hkI2Vtv7BLZe9SJ72R+Ozj4B2r4Y9YfJAjHb3gTg"
    "KpwAsiCj8N5k6yzJhq8n4cfCsexMFuGDyVYPmjyzlughLRFkJGaETye9/hkuRLL1ZILS9uQWrKF38mrtEl0CWSuVzD9uVcWpNEe6"
    "hH3Af/RUK6keAKvT25vohewCMDe0GOOb6TO77QXN/7vJ1pMejrof3sZPXMZ++NVk634P5wvr+N1kcBxN6wTy5SOLjtPDCIYyUGGS"
    "y+3tF+3Ul9Dofasl7ved2jFQf05QV23YsP+acr7TObBmkEAgNODdduDIF9MKlEMnr9QwDpO+wG9hevvC2YqwM+9NXnwlfb98kbzc"
    "3n49oT9YzKrWPBhf9DC87YOsmg4ASxfR9GkNVKmnmuoPkOyNKzglOAdA/6Pt0SdnyQKtjEZD+UTDoVF4lg2rcDAYZIs+re2XsJPZ"
    "Ff0QO91axzOhOntMGfeQqap0b+HZLAKepZ7dK9ivO0m1JTQLhNCXvoADy00k/ZCMeYZwdgHcuI+2R9vBIY3x3XpdN60/iqqjQYGe"
    "GKGjPhkyHZwC2hUkKR2qszMSXEhL9M5ztuemT9lvNpLPcQEg8VP4DDdgMF/cHg0x44bJuEEZj27T7DnpargOSa9vjxYhvqzDntzR"
    "A15Py3sA5yrBScpc/vNf/3c1HQLCZJrnBTR49cb6ej/MnMRfYuKnN9bVcHsVjQj9AcBARv1f4VKwAwAYRFQlz4BdxAXTELojiS0Y"
    "Yen96nQKCIViUo1CfCLvpBh4YXPYUi/5bzBvwALVhfu5TKvRYU77GhNBcD/p9RHM3RtCgAXL3VsPrR1VrQG41Qpnv76xvv0F4CoT"
    "pxZP1qI/zH6N4FV5EqmWTp3VVobgh8JSKgJA0ZyGX04G+BdWFk6nRUW+JaylaPcM0Uzv0xf/Eg9e/urTQzWqjyqkvNMkO6yOfn3V"
    "fP9m69qVK7yrgb5dfYk4Yn0bZz4cbH7++X/TWesv+78aXL/5mUnZwJSNjWsmZfOlhad+ZwhZnI9riqw8LjBe991pgr96ozg9HvVv"
    "4VtwWK7BGPXKbyqgPHmZYhPD6KDMpwCjW8dpCWzXNK1Oh0d0S3oL5eVDAtgQEFVvbS0HAWXt4DBkUQ/fWWRVfxTqrjEs1yCaz4Gv"
    "3j1Kp4gF5FAA/IAa7pJNWBLT1oHMgekBQwUV5gALzu/BphQsRTB/lMRp1Bv1kGQnRblGMVDWyvERTHYIkmHxug8sFBXFC0dMgCM1"
    "xVsEYI9+vbF5s5FoQPlHa4VxDz9/+nCffKPsRYgwe+qeSzym9JG690YY0zwZ4QnHQYYFsx/YSrFF7Bj1BlsBv7nL7WqIy3ar+Ahm"
    "duVKL9sqwpNJr+iHyfYA/vQXt4oewy3duvisb6Xk0/cY1gFtKpMMdsuIPe6MwoLbi2hmj+qKZvLkALVaUAxyo0HOv3p6MdWH7KTw"
    "LKrIzQtap320Hupf9yiQz/DFiHYYcLHjaVTCiRth0IM1BtDLBQ8g3zpBNeUJkW0UYgCf9IrwKuADhQwRfqksf+dswogueFkFCJuE"
    "POToBvM+c01/AMr6ikOL0I5Dr9DlEEGwn1QhrN/DZp7aDT3DvYLoMmg1sgjTUv/iVkzdZEXlwVGEFHERlq0ROI101IZVptoxCtrJ"
    "OzTAFakNgtsyKHQ0QfV6Dob800QDDehXVBzS5ikVCly/ckWnAZ6DvX+cp3Gwvm2nDkfz8WjxydndwpaMjtdgM410ws502hth0qtR"
    "fzGihf79ZOtr8mIOqJ0eiw9HHOoc6JIZ4Sd0wj/+7QEqTz9FJSYcpmAtYNntY4V7PplsiTS3f4qWLnBwVROjK1ecrEGKBgXAiUKZ"
    "klJG275tIMLhwrdHkkabbncJ6sVBoqzH1MsWl4H0j9Q3mk1VOTaxrcYw1B2GNGeD5JK51XOJPwA18Z+U/xTznlWe8iz5lrv89ajG"
    "ob1oAAEWlRmk5MXot79VqSNJVoLUToHexfAVsjOybO5w6jK2nFN5dPThjg9/wR4t8pPgGYyQItr3RhKLJMDABLM5IHR+C4FArAu0"
    "ds/WaHQH0wRkT7wNHSeDf3qQBfTQA4sfQIaUCKk8XimfBvnBN4Bv0Aa6rAJyqxoFLSj0+sEsqY7yeDCyRioTIK7H0RhsaY2BglDE"
    "RW/hzs62zhaDKmfhGN/6TZFskqfg3s1wbcMwREhgntD4mtuGaIyTQu7vkWhBnUfRHOgTfQJWHG076zOk9B11RKHgp/9bb3v4PH37"
    "oA/Mxfbw5tuNG2+vbvbhc3cazeZJ3OcWPvmUrhF7WX9b5jPkA28JZ5Jx1qsUa139JhGE0YdRI6slv24Bd9ljgKwDlaUuQNi6lf26"
    "upX96lf94kX2ciuBfxQ8CtONbKIzrq6kHmK/LrStWxsaVQGZ7GpqtQjTMArzsNx68TIcbwF1nG59tEEyLRSNtgD+mVq8Pl05IFsD"
    "kh5m86IBoJAfkD1wCxrZWCTTMglw4rc+6o23esVWxI1k0Ai65UEYlYN5XR71CpFDQ4VwoTEAD46lf4vFYmJvcGwpiuNpBi2dnskQ"
    "PxpfuZINhIuliUHT+ZZKAgoro8xxlLkSe3Qz0MS0z+cwXSzUGbaWulSIhLdXWvIKagEqsDQEY2e9uOPB6+QUieYtDTDkv56cZPhO"
    "OCmqU160UtZja1kZUjfA/IqtYsBRCHsaLxsM5G0Bby6LdF6hGAdDHCQguDOaWICkk9FaIAM8Pe1lwKYoSGRmcl8iHNRmrrZgk/y6"
    "SStvVbChZfaGOlYvZeOeLYZ26q3ql5vbADK9jUJYchTG7kaw5vbEpnNWakAllH1WTLDclgJkNppIgRSF+XBVVdyhQ3tM/gH5Ojil"
    "Ma4CfgbARwmtvXnUJNU6AhKp59BZP4Vi2909ntH5GWahWVLkcrXuV36fFGkl3wDCBFcFqpjua9rnvLYxDkUjd8NekJJI8wvVsPrV"
    "yJJDYkMoiHh/tDViskMaZaOOFGymsBV5j56laLWl8JNwWOpIKAyEpIUbL6zGVcPFrRY5/e1vrcaZ9ilKRaZsnE7wQ5Kn4W4omyh3"
    "hyzE9pHw45gm8y3h1m5HZYLCISA19IcPLM28HJ7Nq+EZYmjZqqEEd1GEJJxXT+YU1nB5sTojySSWUrdRjRxlrWLx8t6A5c8wfXj2"
    "CQu+D4RzGJ61Sp4gvh2epeVz3XU6m6EUV9EuAjkmxvscmx2cTNHFnUiUQyXqGP57l95dQGMlCIpv3/Z8OSguUzI1skttaPHJ2xSw"
    "8DTxFcMz6BhbubVsrJS2P4ajFauuUbK1uufMZ1SOh530uytvtWWyrLudxUoA+MbXH3JenfnbBSiBtEbJlHJ3KmsdFnlemV91GqvP"
    "T1A+3ielcF6oRH49s0sKGlvKIhMDxFqh5iTCcTgNawL3YF5tD9COeA6bcqve7iUqua/4JkhKBmgPgPT4K+IEhFpwz4ipsMonFF+D"
    "2L+XMqhbwJz0oNGq3SgkCVvhNlZ5GlOV376NTQPI9hzl+evSJCEeyrPbFiB0XqG4G8Jtk61eykP6hOxlj+uEY1KYttKt1IxXDS5V"
    "oJpvTbaB93KbMJUj5KYaDWJaq8HIBawGG3Bk0EHe2UG+lbc6wLRWBzkDedgrO9sqt0q3LVVXYD43Rcdb4/byONnNJZlCUseSTHlJ"
    "xnI+nU29hRI/p8O+3zIF0K8usPKtCkaiByk/HM2PX6UxyvAhayzjtt4BB9ob5RmPKsayfIQeoRlQqzwfxq1H496dMZ/2T5Jpf1t9"
    "DdXH9oAxuNJsjV58ctYe7uLlSKbH7aJAYn7BKo23vhRtQxPeoXP4PU0LOOekWuz3LTTfQOQKArfNtBEKM/xYBrFHXMBAjA1Zuyvc"
    "tkphrZq+lvTARe0espl3VZpdcDHqI+ucB+v/CAcrLG2A0ommG0B7rtonkJFMDqwCZTukFwUgXpCc+YkB2oKgpkuxctJvmew9EzIC"
    "rKn6BlzT3ABqJMjAUpOEOsIRnbwB3gaSzlg3e4c5CLv1znq3gBrAVDP8F8jSK+BWD4mXLZ1J8cBfDAYDLS28FMWB0Rp8hzRzOxGR"
    "RagUiOpfNVOgH4S5vVB/mAxaStDe6AA4uRFgpN7X5HBvd39fTiIxQsKv2Rv+i2l+gNe5soLQalstqpq167n0ObQOj19/eUHeSDVl"
    "eKQWob71kXfq1jS3eRMAxhBSzcl9JVrzJoHs309WQ0lvSsq7csUquLSyH5J2bRqkmrC9Dq0pm53KxTo36iFl4zXTyMVxt573ECC8"
    "K4ChVKhTaowUSnTmoMZmrXV7NfD08mgMv63ID601CiLoxR72Dx31R1PfxhWFcV9ODvJiWz3FFcn6WYwNCae7VIdG16DLImyB3Pn2"
    "7RmIDlvFQItKYbSFfvcxYEg6DnP4wTAIS0zHjm4JmNJthKSBlW5ijRwFgBxadgAulBaiRguq2ws3kDca4KFetDpf9DUr80WRt2II"
    "/w/r40MBaoEWnWt46RPIa02cdhiHwHECe+Rdb2SR5P6SRFTfkmteiZcc2E+C3Az+8qL2am/jNQN6bmCsuBFzSherAd6Lva3HvnXw"
    "dbBsUWZdi9LCJt2LM6K4A2ukYlen7Cg8DF9t9Y78QD/cOkKgP8R6T7AaQR3QXQPwohc/6qtj88qA0u40pJd4qLnxQ7Bj3znjRkHQ"
    "L3y2ia+gkBU4ZI9emC3DIWGyhEOlzdannZZuOQeAQFG0d5XTwppnK3TssFuU6EjBIH8lUwBIB0PWxtXqNDqtuFKsLXC+fWsMAaAb"
    "D+VuU6p3vHm02lncAtLpvRkFHgJVH1lT84F6By/Lajd7GQXPqrLLS/hUHDBA2Gz3ga/VeivfZeS2nw8GFtHiboGgdhUbarbA7qqX"
    "DBpKs/6wlaQVccRbAz/L4nbHtfqL5KUQ+VZnmNrfHkAJbstiUHyt/QE12q1ds2Hvmg3vrtl4ORyN2jU37Zqb3pqbL4dwaGWmzxoj"
    "+54bGUhPtfXu08m23nlCgO1ada/ada966159OaRLqU8Hnx7ynWEFdPujj7IX1aCcT9OqNxqM+jC1l6Foc5wNgkbQgqNQ7vBpjEDe"
    "V0WINOdb0YCkpv2EQF4C55VvqaG9fZuHY1WC5KoQyL8e+ZUr47DeKrbT7SU88d6zXTSCYaYYbyOGy0S9dmmRu+KtVOvcTGFA3mSe"
    "2lH9S6TzC2glhH/PmOUa1jhxvKOaWCB8hv47gfiUeJOqLu3evv2ovHIl3p7K/AwYesIm9YfYBXVS90PERZwCv+mH2tc4zve7rVdI"
    "s1/1LDldJFhMCV/YMrtA7hPiV16iWm0c4Z7T2gV/7U9ekW5r75ldRc9VQfK9zReOYrXFJlTz8RqeS5JjUPk0unLleU8rhl/oQiXv"
    "5tFLY0YHjY/IVi8VexJZJ7stTJrOMZWsUBEso/CPZS/bXtZHS+eF959XrlgNsT0ONdUuS5vTFG4zJmTy0yy2UN1jo4kFfnMAukRX"
    "lw7Yy6vBrsH2u5KMT/5EypEzMmcbJgv4f+nNo2ehlrLvgXc9uHPTRbCCE9KtZu/pxbt1k1EQ3S7QzCMBnIhLDvIX/q3kdCibvPTK"
    "FcSPpVaJw5bIX/a3t6OFtdWUZHUUldatbW/E+vgRgJK/gPSLit5VrKe95h1GeKwzmC1c4DdecCPTiefUuaNChluBxMc24IMTvJWn"
    "pxyrx8tNRVtquP8w4uIBRLxlgKBAXm+ZarH+VmsEmzjub8f4t+5v18OViF0jcULqw1hdrqd0rWbTuQbQG+aOlpb0UCqEXI5b0QTw"
    "ws3EqoZuZ17N3i+mfceDe6b3v0VhmC1RquFEEWRHHUb2CziN9AOZByAvIZ9C6PDpWF4j0GUmM7oGNgZn6gBlrQOUxiPUvGSDNN7e"
    "FlEhBdYgoxnn/wVY3c5VZwbsTFkVEpUkXuyjDbzoevMh7lqjNm0xmxbJdHQ9RBOTcunmLj+MyYJs8X0WGi01lQXNSrCkGbpZZCG+"
    "CzaZPkIvvO39fnLRZsLiJaqjxvKoYnh22MLPNg/k2bO9LoIWCrPhsYv7FtiD0GzwZIF2WGHcRuo/QN9JG/phwrxKyHytuVN9+5ZG"
    "2kzGwVp2OR0G/8pkyFBV/2i1aZFTaxECuutqunlFXqdUPmvc4Cno2eaPwkYfZ3mcbA/ISIq0f7dck0W03UV/MWirJ0mJ/FSzgJp9"
    "n+0j2/hkcwDcBorcmrvbhk05ntZxgkziAo833610zrIJKSoNtQhCnlq0yQWtaFbXOgcqrXkLuQjlDqyduN/sCg5Lb4nKiDWpoqb1"
    "3b311fiV2VlLv8mTOcvQAcNQXz102a+gunNczpumOgOqDoNtVFwJ622xEYGaWbRkbZpqO8XYGgEN+6YDs0Sc8gFQ4yjYcAoYDi0U"
    "0z5rH4YUq1ZSUMwk44nSspqAStTg0MI60g5M2WkFf1tt4E/6QjypBXgPXLzHhIrzpmgeFSNU0LsFOivbjZf5wxEclEGRxDXAx2dK"
    "R8dsE9D4VgbVQbDLgF7dsh4BzHuF0oANURjWCo9tX7Ms/YgNN1qm4uUXGagCFiuE8K1tbKeoewwxBxAjfCxC0kU22b73AyWWjg2Q"
    "1EvJXqXYx6oNtkvBTaOoF8VLgqCaESz5fN56F1RFB+UoZCw0+qcA/hvM1zAxOKNf+J/4vB8Gk2ny5pZOxl9rcVqwXDekeACzjPMX"
    "/2S1NU3LanVz+gUmB3VJjxOTh77XJ9P8BD1n0FNMnWO9yQziqvfPOPSB9Gk9p/znfse41jCiBMamsQaoelt7M6QYzO1xrJ22R1KO"
    "i3w6XTtIjqLjNC+GQTnL8+qoWeAgKtZO0rg6GuJDmsYcW22Qq5w0s4bRPYPhcO0kOXidVmu6Jx/UTa/tpuDvWmO1li1Lx0oe0OUg"
    "36ACGPJpGrcy6c2mb8kom5y3FmrRrGoCua5qlN291hT4NrNnR3sYtgjsrI2uWll0vHZQV1WeWRWjKfpCy8qk8u1g9Yg4+CidUeCj"
    "rGqcm/KoSLPXw2DdpKfY2trBNB+/XiMc4OR+t4ahCmBHbpq0I/IHCkNfX//lylWJpukhPfQCKhaQ88XCZKI7mHRyqiDULuA9ZwCZ"
    "AUPGc9Twv+YqWxVaK9xcWquss6z4n9HhDnWa7s/aHbrYQDkv+Od+6NQA3I5M1drlax7kuIpRnJ+sqGZvYlXFP0/Os2s4wxva78wt"
    "INdFiZnzPDVrtmwbDyf5uEbfamWKT/7O2nts4+JjprYG9Byvc/gra8oCr+wAMcrqYq2tpaCYTyZwxFaOhot1oxELkkccFeQiG56K"
    "umNrN40hjtrIhjEDs/8N1OAZHRD4FU0keIrXLzCGIZD3XlFNZev7e9GFrO607zsgGzmyor2Nm+txcuibeBMde1Cjd4vjf3WJhIYu"
    "SZr0dBnhWkqhTo4ASa7BMQPGGto8KaK5yTyM5i75GUCKc8Y7GJIODNlN17w0bTkF7aSevrKtQnMOxN0oJql2wQkQibUToT1OYcyR"
    "KFcXQdcGJJfEvAYAl6r4gZMHDmTTACknXoYmOIdrmOVVDz6BKUBzubj//ZE/L/SlsH6jSgvdN5ts4vlG/sURfKPiEsyuAIUsMHpU"
    "OsbX3k3YNdF952FnZL/0yPvOpFS7xCleRVVkLhcZM5e8/KBVvUuMWqp0D3uOEefKC4yaCl6Q+9TFL4b6uKwH/+n9vd4lTFHVzpPW"
    "daq4w8sfrVY93/lqN+45ZK1ClzpprdqrGCneBmuuoOrDQ1qkIelomcTlF6cSZ9vojY5HDTiYmT3BoyZds0oftSibd1va7Xs3pkUP"
    "g83r6zMManSQjkHu/y5Nit764Or1MFiH/x9swseGht8oVBrhMzRW8VjvvRiJ9ma+Njbvh88+5lRRDCAy+3iYsMZ8YNIWeH/y/3P3"
    "7v1NG8vD+P/nVRgOh8cqitDNtuzU9QMptLTcCpTS5ptvJGwlUbFlIysJNPHrev7/vbLfzOxFq5stJ0B7OKcf4r3Pzs7OZbU7o+kz"
    "+Qz5FR0OsQMjGDN7m5wvOFqIF8rsfgJ7NrzPHjnr7JHzQel98TT462PNE+QbFj4vFWCtq3QyP38qPC8u6yriBefgLaMqVoXBJGuY"
    "6HsIdchn8UOk3voRV/yobEFTPosmFafKF7cWY0QQO+At3uqkL6D0evokTKL0Hh3M3rD0cIbu+/Z99tBsQJj0D9DfXVAxxOSQoZrO"
    "HOln9sz6rHSzk90aOBS+J5XHX2y012tb3BgOQ/HYT3bCvwcg1O08zDq9oYmWr9E9wjiY1h27z5MInT5jCd6+OuPV/ZXqRelk0VYe"
    "AssOnrc1/SHz5aa/bosrScb4Q5vd4tLwGxfeJhBpTd9/grdu0TnvUvf5ivragW51tdVsYSTk+3h4sqDHtsflg1J8cRWN8a7VGMby"
    "/wVsDJOccUkGxS0shU+Jie3QAQywMOgI67DSosUDTJL3DBZIJLoXB3tBTGHkkW+olewlxuYkH4wt7DrgFtIW1WHc/ytGeRd+PErw"
    "fnerDIn5H4VViwZla0+x9arNwZwxiP/iGVajrp1Of1PnuSormtvXN6ecL6/DRSNfXoeLr8iXF805cxRy9jW7yfm4+Cx+cs6a+Ml5"
    "+2X95Jz9LX5y3pb95Hz4gn5yPih+cl5W+sk5XKz3k/My85NDG+Nz+cmBzv9uPzl7OT85j0gol3VRignDNTmuihZVUJQBm3W94w26"
    "HgKwTtfLtK1FWnG98RH/ckzwyuWGDf+R7nnfKNxJu32bqzuo6jOFBNV7KdNuMp0Qf4I+zx49gCaNdwH4hQo/mh37+k18QLnDA+eE"
    "uZtulMkrnPAAoSH7gnwuUb93Ep4l8/hxeJTmV2Bvoehvr1QHi++YE8Nn7M/37M+DnAPDB00dGC4XSRhM/h7fhd8391147yvzXXiv"
    "znfhsy/mGfPdJtd59/J6wb0v41Xxz7WWyvLsmCwVds7vW66v84MG+o2f8O/PPwx8s2W2LLeFeaBjTAfsob7+YTaNweg4SdPF4O7d"
    "8/Nz49wBA+r4rm2a5l3snBk8EUZEgD2HrrMvL4f7j9s+BrgFFjEZ+E/6Rtey+92W5ez1jY7Z7/fgpwE9dFp9wzV7fbtl2UbfM11I"
    "O5btUdI1+1DdtnrdHqVNC4stx3L6mPZcx4G02emb1LzXM63HjuE5UKHVMzqua3X3HKPrdR0X0k6/Z3ktSJuO50Ha6vf6HZnuGn3o"
    "xt7L0j3Pdvst0b5rdDzHxvqs/67hOl3beyzHBzhNh+A1e11Mmz0LpoXTAzhaJvTf7QDggAqzZ7tYwTQtGxp40JAamE7PAs0dfrgW"
    "pr0O4sk0LLfXwwHsfqe/B2m7DwBYhtNzbBvL4Qeg1uh0u32PpXvYH+DD7GB9xzMh3+j3EHBMmx23ZRtWt9+l+hY0hLRjeXbvccdw"
    "+y4sFUfIY1FuWUa3CwjC9pbTw7Rn9glep9+lBTBNz1XTttW19pS0azsMPmpvG13bseT4fAGxvtl3O3KBCR+eoxBA36J5SALxLM+0"
    "FPrpWR0iNUFfgvT+EJTNo6+Ro3MgX/IXDkzwQCOT/Fya5H8yk/xJUfK8wO2zRvQ8VUXPYyZsHrE/D9mf5znR8/y/QfQ8bC56Xnxl"
    "oudFneh59MVEz+NNoudFXvS8+DKi569/jOh5Wid6XGB/PeR/zp5r2J5LPxlrcA3geKYjWYcLLLfbtyRrcYAFWj1Psh5Im52MMwlR"
    "IDiXEBWCswlRIjifkibOqKSJc8r2nLPK/hnnfeyB5OyYPcmZRTnn3Nhf3wVRKTg7pEECZZwf0rbt9aRkwHQXOS2XHI4BeCLJwSQL"
    "9N+xER4ueRAdxFm5ZEL09XuZ5AJMs+GYYHONTr8D05OSzzVAzruZaHQBy1YmOqWk4aJVShoheoUkEaI5SzPRLdJCtIv2QvSL/rlq"
    "8FiOz9fPNTxYgGx9XRzHyVQPF9aHJDcnD5ygbdkK+bh90+wp5CUor6HkeSIlz1+LTJrcb3bAdv9rOmC7n+dmr/Mu6X9mQvQH4Yn+"
    "V/Hjx5xY/fG/xiX9r81l629fmWz9rU62/vZlJNgP/0iX9DfQJf3X4W/+5y38zb//mg/Sf/o8B+nvmxyk//5lD9Lf/y0H6b+XD9Lf"
    "fMGD9DfKQfoflQfp9zccpP+RiYH7n/Mg/f7ff5D+fniBL9eehFV3DPZ/XbaLO+PbofSnoD5IBqHfsKb+ftneot9Rw4qDcj2rXM86"
    "0LgLrOIDwozf6Ylw8pEFOCTZLLSQklO6zD01uQjPHHunxjj9oHr6TpA17eELiw9pPr/oFzuRTjCzbV8YOFEG1rKXjkUHX2+Wa71q"
    "Vb0jb+xsIL6Ge4Xkqm/QfV+PrupXC8YNym1dta1b2dald/PzYenjzfsaTzrvt3KjsxwitaUG3lGCbVrvADB7EyudrOAr000+WMbD"
    "ZcEHy3Q4VnywoJOVpeqDZTI8VXywnOpHw2D0vuiuS08zTySgoczx+EG66loM30ufJfp78cYdxAZ3pUPVQRj/RB+5opxzriPhnGs2"
    "fF/yzKVnUREx9igoSovRBIFT/Lek6JZLX+gzbcCGYKMcafpCyzLRKSkmP5vPqmv748j8XUkaEpCniseq34VDqDjzVsXdAHCXUUoN"
    "1WWU6rGrwonTp3UlUum9KSl5bwI5OYqZD6aIfC/J5U5Gxn50MBolmZOl27e5QsFcrqC4b+pdKanzrpQo3pUS6eunypPDpyWLPBI5"
    "frZAZJkn5pmf9JdVZoB5TscrBlU+oxDFuM2ZI5Ai+lO94CxqDkxNOIsKN3Gp5XBe4FLAtxQuhVxrrnKp0+FU4VJT4FpBOy0u6hFl"
    "5j1FTRRPUUdVnqKOtNGR9Bg1BjYD9tnR6LTAZkLh/0/uSub870ioxTByvZOnv5G5VMvuL0RYYhGkfJBn1/Vu6z+PrlK547ZwPMeE"
    "EyNmsjdhz3BfF5EiwqM1Ti1235diFqV6oOnvy0791fxyrAdRWhkoItVQ7maorYghVDPgCvusjBCg9tcgSMAXWTzyfV8djKDKD/o6"
    "J+jJbhawAUx6UucLHqsTtUJNdIG8M/AG7vtxL1wDU8k2mGorPsuyC0ZtjSyejH5j5qymRMHiLOwq8QToMA603gh6LzoCD2DHrA0m"
    "wI/hIu5ZHuVGFkxgDCkZTAAFBg8mcIr5ajCBJfPkj4x7XTSBJPP9Py62qIweoDSYFhtURAtICsEBSpWFI3pgL6fXCAYQl3ZAmuE+"
    "cz6S7QCuQusnsEyTimU6Gk5wmb5nDkA4zyms1BFbqQlfKfRgjwg5hL88BsCi3POCIe9YwRsorvXu/xGD7Vm5n1klVktdKfg9rMNv"
    "fA2n/mf6R/3tsH1WgcKPw7NGHv0/MjSeSY/+bxXc1Lj0Tz6hB/8vqvDiuyQMAdCmU7IY2XLOFa5yno/RBJJhWMIrhhdZG0ogYghN"
    "QO/AUALhujgCu2HByX87zMcUCHKEGpYjCoSlcALovCicrv7rffhfkyxqAieGOd0inxxKr/iFsFXqBQgyPTBm4NCfx7cuojHq4T5I"
    "g5zGhhoniIV4ZNwSh3tgQki19DQ7tkiUgHVJ5YHMnFybavr7+lhVY4xxdTQsHqOcAlhZWLtpLuAghrmbCP5aPABEl/8bx1sML8Lp"
    "INb5ydIg0clb3iDS0cvDa/odrHYnIwMAWQB8/EdNHK3aFa/ezDUeyu0rxdtil7w+3TEF6ZWyNxlqkvVK8SZ3E+NQkgYGI1JSyB7o"
    "E8BpnqiQ/oCKcnUpNgOeP+FdbzAps0Mc0MtHBr8erpEf0kK7oWpa4hEZ82QX6rfQWR0s5y2xspF+azafREcRbtEIehUJ/Rb3Gj1i"
    "lKtj6L8Jxv0DFfbyUsTnZHfdcazP73UwHXEHgiWXfqeFQKFtRPutxSS3J/ZlAMcs7KPaqtr7ZmbosE19Wudck74DSA+dufg0tZsx"
    "xugata40efgb+WUhLdFHPsjordJBcG3oUelkU8vOMU4VR5wAdv1Y+M27PBbmVo0VKw49S84uaYq78tPThvlVeoDM5sSdYzI94Oqj"
    "bIHFSVrpRPsaxlj1d4ptHRK/z3lTLs5X/6Q4WKAEFefxWrVv6r/lc1E1Krf1Tb0BlTj5qM4tNRVegxKCa1NC1UpnVptqvYsFLakG"
    "7c28QNWjlbBb3Lt1xKkjqHZn/TdtlhtmFXq3pY5oVIGvjburCl9p3l91nCEtC4h+pOlJpnUOy/t6PGxPh0oVbT/Oxh4z62UqVRY9"
    "2fdvUTTUA7URaocU+zXMImnTwIvJ5eUQT4vwZ07LoByKFcXUDa5tSEezRUhR5infcLKv6GSepcV5zYfByCA3BfpyWBEgDmy5ODxn"
    "iiwadvPphBJileYK+ufVEaBThpyAhbYAE+C6w+z7bBwjiUAnDf2DtQPuBsYtmiBoXnsBOuEcvxtesB4GS/1mrq+bgzEGyMi2YClC"
    "diw6D0YlqalPTslu450L6wksprlykaAWfhlgHDpXLOdgg3SOeD/F4VmuhGKMylCZMEokUcbWLpj8bewbDcPC3GKBH71QoTB6XJ60"
    "vnlkcV9HMIWLUiDuVFiYabaJUrGJxGbJKbC/jNv+ggIuI6p43G5d9FMTvzsVpsj7XBBsMdJIXkahTrBnpRvsXWx1+v5UCiotZ7Gx"
    "ezKRoXsRN7oEeDGMdshqaBcSJh5CWxclFaG0t4eHd1EBTzHoNlYgVEb4FaT2A0lpKAWrIkK3LvqqjNSd5g4fdtvzoeg0H+6+cI+I"
    "59YEgMSifADIuQwASXiIyysD4qVoKguz/fWizaQc3viquKmCXqTTYYj3tPBmW+Z9G4XDJ+g0yXX6XnhYSXX1lkZMsbyFUYznmCv6"
    "CiUrx5TzS9lFC9vrO9JIK/m1juJ3VR6Rt3AqVfT3xIZc7zMtCSbR6bLopVfx8LEENhy2TdUfGfNzuROeIQqrfTbDZMrO3RSPLwy0"
    "lmm4y5xTGN6D4hGF18x6KfgtIb9fi2AcpR9zXjkrp2EbHWUiqxrPVT7B76O7qVt4VUgsJFuwXxaqb5Nw1ujpRTj7ip5ehPmHZ+lM"
    "GTmY0T2yiP1J2J94pj66wNQ//i1jMmv83mI++7reW/D5lN9b0KJ+kbeMwWzDi4BCfQ7y534JspyVro+PZ1/u+vh4lp0rT2dV18fD"
    "2frr41OFqmef8fo4dP53Xx8/nQ1vLQTr5tLX1y+4G7qiqaPy0HDEfJ4whfgF1eDxM/Bcm0ebwbOrByQBy2X0G79uogO96C0I6Ta/"
    "LTnZEZDcMPOV6RucCOEw9JlrE79cRSgAQ194jva1AQOBK1814LDSeohIcanQHYXDPd47fnpLwQSbnwpXNZkLmQwneYQawYTlyxs6"
    "qLQvw8n8XExxHj/BnO8hh1DLgtSQNlvbK4Poqh2ry1sTJBS/0z6K39GbILK374HBtFwE0DewAviPOa/x6SyYuwv0C75pYF/fZJhG"
    "paKY5krSTXSyyC5dF13qtIF/MXKU/gP1eXxPqFIPYh7PKp+nTFUEI8t9hPChF1BzsJafxQwU/gjxsyboyrBz9k6i6aQtCSmcDtFo"
    "Y4hvgDThmbGaxtdSNy9Ul7+NkZ6qV12qlqGcUB4hWcs2Lr5CFfUBYkEGs8e4r8BgCMGGyc0vJk4H0ppdB6Kwbuw+R0KvdjWD6/A3"
    "5BUkuoFUsb5HY2jjqwTh41FYFQNR6+j+UTBdYt0bj6EHDMT9G/4VYVWfBOmJMQs+tPfGeAvsPv4LooKjmr2zH0Z3/MUHXxe59BCf"
    "Z65YSNW/qPUc7z4Ex+GbnQBE6VF6ZzIfk5ZhvJ1PPnJHra/mix0C4a6tL3mD36FBOl9U1kcHTTuPWQMJGFQeLvNQ4YDDOcurQuD0"
    "qggEBQurUpecqw3xWgb72Va/0AEt30g/8cIBJbqmhYy3sKVL3JcDd/s23ZMQ8KlFml5DWkUyLsJbKG8O/UpnW6HGAoF+kXtAzyM0"
    "EWQKY08Bc6po9HyMSo14V0DPBegCH5dQq0wnBdNsMlM8ASMnqHMGnC/LfLAJF2oVUaem1KRkFWYlPBKNXw7fUw595KODXwRCrS6C"
    "Gfk6w+r9IFGLM+fTPl2GuM+CWfjVwTiqon/4Or4TLrdTI3BUtkPcbnIfTLPZyoNwFKMmONj3uf/heu/B0fK5nPCDmHzbUwfLp3I+"
    "Mhs/V4Dsjf4Kn71dhglIluxiwDtAaTGXa38Fz8x55U9qdy9yHbe1gSKQimUrvozs+cbF0fR0eQJYn+MCnwTxZJq/OcV6onPCRwRo"
    "W9EqH+VAb9OhWUkrywXsrOZYYXGEsLp73eoIXTSPGCG9WTcM9S/J36sCbRETVWeofMLF3us6rz0vFYirXAJVXyjPUeqoMAqJnjKL"
    "bQqeTpcAUf/gF6XapFBkVLsH5v67mmCMt5LwaGlwZqFnGtNr5oifdfAbCmG8/BYPQZqG2g7qHiTNYee0Q0V4ajvxN4anK7I+0U1t"
    "V60yfItdjHasb6JBhIBm++hLAnqHAyoyqelOrAcc9CimO281oAeDYKWXV71mP3B7Ra05jMPzVoFkyvdvwkpy5KSV79CYsx9tBVvI"
    "SqXJsgHSXRFxNN+tPEsHUOK6IargkXcPy/S/DkvV+2VXUefzhBAPn4zxKdW+KqWHN0GO3DzgeVx4QSYoVzcPfI0+mjHdJDfOdmsi"
    "2JhYjnxfcjnizGjcgAW5AvmelBUABR7mHaOXgspBJc5VCNftJ/zWoKASH26/AxlP33kxBgIdrkj1fXtE81CtJGGNzMt9Wxu147za"
    "D8ZApDGFOlb07r8wG3/t/IVaOSnuWEkbyA6YhbBXbk9KOusAf/IeyFagLlYCT8ru2ogspHc9VrCGZ03S2MA4rCo/AW4i0j/SPHX0"
    "U8IifbAKS5nmFcYZv4pVfqVPh/u/keXzGP89wAd9+JloAn+sg3WY5lp4SYsZJuizhdNRWZsZpjnAvhuCCALlaglkldJp2jDYmYij"
    "nqrux826Jzx8N5wrvY+x92jnlGn0FRx+4zJlOiq/wCBGh/UycwHFSypGMmynIxW2y0tTu9OOS3lgWeUiqON3ginQ0LI+1jJbHhZY"
    "Ia+ibWjCQ0mUgnhsaJavvVJU93tJFDwmp8+bAkPzWwTGdI6frAw8TBptrEELEM1Pl9J9dLYEn3toHEkOi5zpecVAy3H7Qomaksda"
    "FuRF4ytMsWFAWys4ch6cL/Sih83BkwUMK+++grXGjvROZ3iXaTbc5wYlWBwLTGWupdH+56FXoHCWq3oiqyqhQCD/eE0XSsSDWcWd"
    "/2EayYNoeWJfCBYCG2rgK9ZnLm6IODi8OQgMwnNFIJGgtMGiKmYxuh+323xsYS/C8O/CjwNTJyAy0gX7FZ2Qy3oqYEotLe+1OzAq"
    "iD8LdRPI1RdZutBHuZPGMg0FRknLvn27IpN/5w+U7/wrjqoCxBc3hXTFD+SLHe5/4ObAjwUGfdA39glVj9ph1A4MyXbYngMKvLws"
    "ORzXEJv5g2B21pSDg1XVmJM/q6tRxBegUlzI/fnBgTa43/bZp4LHBRrh4jC/GiITT4i5lZOCsKpFJqvDcMh+V6GujuyU8QDeIoAs"
    "drcKHT8FwRMyOjWXpyk3i/vspkIeSjbg+QSSf2HY6WmGSdlvXRwdRB47tRfAMbUrD548h5EArjvWL6ym0jhbTlrNkxn7O5tpevXm"
    "LInqNZvTYpszY+7rNqdSq7Q5K8RDw81p19NTwbJkhFXIXLs5cxBfb3NiV/nNmflk3rw7sXX17jyu2J1UcDTTVpOZcM95OCMb6mxW"
    "FdR+Xag0ZnllLp34o8P5Yrmbi6ImA6fJT0gpj+2m38yiQt4cxIb4zSOofVTPTevOTK8bP02MuSY8WrAs9MW+n2d9+fd/ffXq2VMf"
    "q9J3qM3RMM5mG48ur3lsqfvZCSgqDdmxEgvOVjyrkjqOGsJNfNGjC6H3Mq2UHSSVTmXWVf45/DgpfsRankfk0hGUtQkkx7Ck/r0k"
    "mZ/TDvDl90KZBZ3g57q3SRi8282qozTL18accuUf57NQ1sNEucqDeCJrwO9yhefBMX2Nk7VERnXVXxe5ir8uqoZMw8Qf0G8g00Uw"
    "UXNeYgRlBSQoYV2wbzEqauq+c+JXDGRusL7FbyxgiY+UVaNFDydUEW/WlFBVc6So4nwdFKj/XBkKuRw1QHAo143/EB92Y7/8BKJy"
    "vJru2fDren8cXLlzhYgqzntJ43kUv47C83Z5tHV9Er017THDTj0OGPmVe6zc9QrhXefFaT57FA6Y3f5gGmLeywi0s/hY2u6j53Qc"
    "xU+eBH/3MVKBUjAWUpp9uGMCCVWtUWnLAAXWn3D52gDFLpsrJ+9PPFdhMX/u+YrN2Xy+gmDq7PUcFjMhgyKJn9ZSpFdyt8BnR/IT"
    "VRU2AifydQNIsOsHAB2mov8SydbKRCW+ZzuLFSq7yLZ4wRfm07G8kZLfcZqIzMoyygSzGyqPZ0LZOp1jdXnwm4rLbBd0+RrVbdAW"
    "QN7L4wl2AMVWuwKJr5cq2pYjcZyk52YZTcpN/VsX+Za3osnqELB9yAvYsRTqRKC9ortOmMFyi34oDHK5M9J3KibC5hEsSSFi4AeW"
    "9VFJKucPIuN5kAQzumPFG9bRWYAe1ISaN7rIWzJShWSxXYUSK1VMCUfVN2TeKppkRg0bkZZslCNDWWPHyixTYe8xvQ0VaaU9Lxtz"
    "9IsyZUX0m+omvym6LHCTm/m5yXKp0StDCgWTS21KKPofz+bJFT6QZctQgZ0x8/IqCVgZBnXgdUd4FS1wT9Qcv2UHYm8bH4iFBtf2"
    "R1W2vM6tYAYjP4/gRu+DtnpYpvHjXqjEMZgRTKAQsdC30VSlXyuw67j9TUYlAqRlh2MNjuUq+gTTn/YYWLXCbLlX/tZVEwYYjLbD"
    "gbNCI3Pfp/F9IX/gBx/CP5B26eqjNEPfMjP0g2rzPafw9XWWX7G00X2ZBW9UdWOGlzW5VsLG3spCU2js5exq4ZirTnu2C9H8QeL7"
    "JcP3XqXZT5hoHCad1+ZWPqUkY8iOB8QuZLb9eWmd1y7zda38zSb8949eN7Hf9ZMwAPSRDsR/M9ccSsYeLZySwdy/KBn3CJFKNj+f"
    "VLriOUpfPEdpJQUPB1TQ/d6sGQFf+2LU36Nh1GgG4nQQEPL247UUlg06xjZqxVVEv4RQnmlKYc+3mnJESrNV5HqGgirJLtrXi+/r"
    "CGRVjr6aVTqT2pWHsGKW/Pz4KReYK32/mWC9higFwZkfFTjE/o12ez6UYEmvEHMwHv76iK75hUq2ncz95AKVSc/f5np7WQHuksAd"
    "3TAlCvLHv11X4/8O6pFrgqp0LiXFKyYpHkiO/XIRxXGYrAka+L360O5P9rTuHvvzjv15lnto9+y/4aHdu+YP7Z58ZQ/tntQ9tLv3"
    "xR7a/bnpod2TfP0nX+ah3dPZPyVoIOy56qCBGFKuh0FF3b2O4WG4OIzq1u9TEDu7j/FnHaNneV0MmmebGATOMSzPsfdsyKYwqLbR"
    "dTF2oOG5FIwOfvQcCuNqdnsU1rRve+6eaXS6nQ7FLe17jtlpYZC6jmu7Lc/w+h0bI8earuV4GMeu1+l7/b0dyPHsLgvS2rXdjoN1"
    "eo5ld1odw+11zR6+ve53LBuD7LmW24Nh+lbPsjCerdNxMKwqBq/r2C0byimGoAs9YdTZbs/sYSxBx7HtPgbvc0zbxWB/Tg9+YMeW"
    "AyjAkbxOj8Dt2r3OHoBiWlavRdDBD4AOAO6aMAPM6thmx+ngpLoWBQW0O5ZF4W/7XQdn3YFJ9yhIX79HQQIBepuHme0g3jD2YmcP"
    "0n2rA/Caltun2Ij9XpdFs3WsvpJ2rF7P28vSbs/GKLmieReWwZa9w6o5WLfXsS1MeB2TxV0EUG3Ds70eQdIFHGK643VdrN5xu4g6"
    "z/NogV3AUAuDBToeQeL0HUeksboDK6uW267pKs2tbr+j9m72vZ46uum43Qw4E4MO9hnkfSRNojXLBtryIM92MVCj3QXKoQCIto1p"
    "q+v1urBUuBwUyLHXtTpE06aHaRdo1WWBInvYt21bHaTpDpAAzrwPRIVE0rO7HgZItGwKzGg4Xccl4rNgwfcoAqRJMZRND/rBqTiw"
    "pp6B8SWR9oBieh0K9dy3u3u4eLZJAR07HQpUaZm0dzAypYW0Z/d7LNCm5ZnOHpJe36XAjD3YEDAO4qzDAjF6MIzVcy3agj2r0wPs"
    "QPUuNXddh+JCdns4DZoHxdvsWBjXEvJhr+9BPafrWRg5GOpTfEcPacszYBIeT9uA1j3xCwBwOzYLSt13MTh0t9/t2ywSpONRBEsg"
    "rT1kEpaDEStheoxpwArhNgbEdSlyJPxwRRrrd3qWrZb3LNr2sr1n9y21/74DxCTHdzPQXISXuAowHIsNzcJHd1k0577LqLLv9nt7"
    "lN3p8mq0bzuEC7eV8caGYS0fSLXoKVOLnpcN6LfB5LjsNYNyq/xmMD9XO0fT8EOt0wt0kkEdGKzAYAWqmwxQlY5JKwLFvTUO8UNN"
    "VvgnqDvR0Ufx9qdcYRFMyP+lMhLPyrniKPjt4BWTaBYkH2vcd4wRkVXVqUCteQTA7eAda7U2ZhqYWap5ziRpsS7LVmvPoniHSWCl"
    "LmSyC8JqzZNSlye53jK3IVS6M5mnyoqWxoDiEuiVwFRVLMNSVatAJx3VN4pcU7Ma+nGUjHMOS4oN1g1Q7GwZAm1NYF2V/qrJRdZs"
    "SjBZgxzJlCA4HY/D5XLz+Kxe49F59bVjR/HRfOPAWKnpqFR37ZDnAeiZm4bESk2HpLprh5zgx65k46CsWtNhee21A9P3i2CZbhxa"
    "VGw6uKy/nrJmysCVXGo5q2ZUlbsdKjfkPlBzPQOaHm+CbHq8BWRQuSFkUHM9ZB+mmyD7MN0CMqjcEDKoWYSsyS02OlTW1RCFyi02"
    "JrsXO/LCNzvtVtnozcGvMkDS7dvM2pcZ3NIES9zSbyrC4+bg0VJpdSPmBzIiIlxWeTnDa3OIKnIoMgumeIyXkYFaOsU7NUrph6la"
    "+qFYjKyGKoRneN77ESthnlKF88BiLZ6tVEQeUqyFeUoVtt+LlViuOqRg+qVBRYFSWWzjYl2R7/OvDg/lGRZ+XLjP9LSrfVlglyDE"
    "YLwyr1uog3RfXy4O7Z9vOLQnaNee2Gfnb4+a+fp69DX5+nqUP/95XPaA9OILekB6oXhA+qvSA9KjDR6Q/sqOGx99Tg9Ij/5+D0j3"
    "lW2Z25IPZ6WvUNknpzVf/2Hx4b8LxpkH2dcdcUou2HP2CUrl0HjY/FFpNeStmNeKPIfmPmsEH8inxNUfYADZL42eyb9W3/BkG/fH"
    "9ceJ4mnA1V7cVB/4r/Tyx4i/2t/L8I26hZ8h6OL465m2ui8N4B+ZAfzrbJjZuMxbQ1MjF0ztJepj3E9jVnC6BJODXWhRvTZe38wV"
    "Ln0GLXadvspdpfBWVa020gzrbdiSWpqvv87D5aBlLT60lnP85FHVlBn+pRHzljtvw/KMj/9Hq8r+UGN1W0k4KxQcBbNoSutH27BY"
    "GgZALyis0xQ6XlbUI8+WDLM5j5cZJlQIs9rGBJgt/vg/mp5rSAjYsg03Yq/SdH6aEuVebdgPO8uTYAJsdFPD9Sc/rGHt0U8OxgFD"
    "OVMRsjrHwSLXGaQrVHfmhEXcK1A2stiqnG9UN9zBZyw7CSrfSlNB3BvbwLhJO0mnWrnxTk3rQTxP21lfZ/xxs1bov1AtG1JbM+Za"
    "gN/O4fes3Mhe12geTz/WnBexRcFaBtYqGzp87+5wRgqaX5LmDmoKFdDJsFpM629ugi7Loq2ZI4F1R005M2ztXNZgJsujmw3K0Gf4"
    "0DuakufcIuPmWNw4tcEgOEpzpxdSStz8nw/3zJu7n2K4tUcFDDF1ZwVVjBzq1vBypeRDLW4BmjwmrgRcRbfbEja0aEoPlZ2vo8sK"
    "2ttiuLUnKKy3uiOUqgWDujULppR8WAfNlgtWBVxFt9suGLRojsHrL9gWwwker2IGtErhrxw1OJCDp7O4DtwCbyl/S+AgYb2qTwql"
    "Ho+mp9GkjM3MUXl1i08kHCpFohTh2uAEdd51B6d5NZOqX0dP5R3UaKv1qjRrV3cOWzm1kt/2DXNj9a8zOdHD1rPjDddP7wivyu+c"
    "Ma8mOckr9MjKvqmZQdeLWK0K3TDXUGnASammlE6mCjZEedASGoQ+ytyi1A3NSuuQUfXJtHgyzNVidlS+7vPZuooEaaPapW2cBNGy"
    "oCJVLhSrV1iccm+bNC61R1a32iQoi9Qm3+a45NzwcW7tLlEaN94gmz/uFeZwRf6WjXNlDlfq4gqTbMDl6qfalN9lw12d45X7uMJs"
    "m3A9Zbp1/K9g31YOtY4f1WzLysYbNmmDj8y887VfmdejXjRtjvEN36hzsF91A/Exrr598h1sPblGW6d6io03Dh/qGtum0MPWs2y2"
    "Zfg0r7Bh+DBX2S7lphs2y6ZbEVyvrb8WsRbVrF1jBK+9UZHBe8XdQb1feWuorbebUJNNUTWtpjuCBrn6dsg1325mjTYCTW37XUAD"
    "XGELFNttoP9NV3RYp2vu6KzFLWvXGKlrr/dk8F6R/qn3K9O/2nq7CTWh/6ppNaV/GuTq9J9rvt3MGtE/TW17+qcBrkD/xXYb6B8v"
    "HmxGMda6Cm5Zu8ZIperrsYlVrkj/1PuV6V9tvd2EmtB/1bSa0j8NcnX6zzXfbmaN6J+mtj390wBXoP9iuw30v/m+JOt27YXJtfgV"
    "LRujdsNtSxXuK+4EPsKV90K+/bYTa7IfqqfXdEfwga6+JwodbDvDRvuCT3H7ncEHucLeKLfcsDuaXOplXW+41bsW21nbxojeeCk4"
    "D/8V94kc5co7pdjD9hNsslvqptl0v8jBrr5jSl1sP9NGu0ZOdft9Iwe6ws6parth73BAJjXor7wBol6CyY0vOtt41ahB0/UIFtWv"
    "uGVKo23eOv/I6TbdOqXhGmyhf8SEN3x62AjoVT4kVDS+MrDXpc9tPjb8N+Fha8Ld6kvEPxET5eP+zaBufXxfanpFMK9Nto2P+P87"
    "5r89uTY///+HYaB41L4Rxi1Pz/PtrgLddYmz4Qn7P3rOWxNk0+P3f8ysi0feG6Hb8hQ73+4q0F2XDhuedP+j57w1HTY9Bv/HzLp4"
    "9LwRui1Pk/PtrgLddemw4YnzP3rOW9Nh0+Pof8ysy0fAG+Hb+ky32PJqMF6XHhuf+/4XzH1rumx+KPyPmn3VEexGKK9wolpue1VI"
    "r0ulW5y6/tfgYGtq3eZI9h+HhcU0iLZTManFlQ69qOGVALz2CScNfc3zzX/AvLc/6qSxr3vQ+Tlnjg5wr37uXlmlDBEO0vDQlRzy"
    "Xo3ccqM0J7YvM4empJMbZgvC+TyzaH7r/hMTS9NDzhogr0NBVznu/hunthVhXekE+wtMbu099E9NWo0OJSsBvBZZbX0c/TdNajuC"
    "2v6M+XNPa8097U9MSQ3OFMugXYeGtjw1/uJz2Yp0tj0N/qyzWXO5+RMTTYMDwDJo1yGaLY94v/hctiKabY9uP+ts1twI/sRE0+C0"
    "rgzadYhmy/PYLz6XrYhm23PWzzqbtddoPzHZNDpIqwLvOqSz9dHp3zKjrQho+wPRzzynDbdNPzEZNTzdqgbxOqR0hfPNv21eWxHU"
    "Vc4sP/vMSmeRn/EsqOHJ1Kc5h1SG/EzHQp9mOtudEW17tPipJzSN4nefnVpwkAZwbEMYnxi4JrfO60Gs9+SD67AzCcdz5lRv0EIf"
    "GQke7G4xyFqK+sSIqL6U7mfuQH9r5sf3t6/Jj+9veT++P5T9+P78Bf34/qz48X1f6cf3tw1+fN9nfnx/+5x+fH/7+/34/lQRC4XH"
    "SGY+rn+dNfDELvyvkzN28sitemJnzoFyrtiBROr+Iy/tBSdb6CT8JFhi+DpyuU5shH6Ryx/9ZsnV2M1Bm7nfej6nONDpnAKuqVnM"
    "H6Sv3b7NO1S6mc4DdPt2cwBF7KdaCIyASuAv9nmGQRxjQjZm+Stdznrn1kUsfQuvfD1WHA37BadEWMp+5cqY2yAqZD/VUuSfWIR/"
    "C6BQkVpXfDHD+uJ3oY2sorZbzgjunB97tXx6rJYzV/VqOYlZrEI/1BLyqebrtLYP8bd2sNI5vnGtB35xQYgkfJ0chNaGBCjRHm+F"
    "xKWuDZHXrYtUEMUKQSFKIDjwhwoBpinS8O95l/R8u5R90rMe1riZp2lsKAe4qqv40/Ao9VklFnJ2fbhc1iXtl3VjUoUt+3u51qW+"
    "4v5fru6aaL3q+lf21zxAMA/+3iRGMOkV9cVNggawvbumE75/19RggVpri+XjpDWAro9coPPNvq4K09rrh6BdW1OeC4/w06bwCMyF"
    "XrP4CG+a6VVvvia96k1er/qjrFf98gX1ql8UvepWpV71ZoNedSvTq958Tr3qzT9Ar5IioiAefp/VRenGLfGQ7a3CdmKRbYHdHYfp"
    "81fPFojMZQU5tkkCU/CAkQx0PRC/ADY9iwYtA5FTsUiBeIPxlIANolY5ZgOLrEBxkmXzy8uqXATK50Wcu68Ex7gn4l/XjUBCdJT9"
    "vMNCQJDcGfkt/06WHPi+NlABkMG1VzrXHutGQSEqgGfBIjBnc1zxpRJVvBBkXF0rGdEBRVFNcPEW7xGxxQXXiDFZqZHXrFkmEdeE"
    "Llfij/Pg4cUVKAUfF8OK0ONiwJv58WW5EJK8XKq9hH1G2eVZP+LB5kmqaKMbN0Q8ddYgKwOSqY8eAqxxzX8Xq8qoHrovDQweBz6z"
    "MTKCEwkiMWjDKZi34CnIF8os74fps7ov9XcqyFR4ofOzbKH2Zzo65WdqOg9tUqmpMyOAajA7oFhZmAJknXC4yXYpVqQKUFFYUb7e"
    "ltsjZ0gVczNbKkMcUjsuGWJ07bKJ5eH95RJ18VioZyLbRl1/gpUXjJEsWODFSkj1wYOZzmI93Z8BZMyr9RlZzNFiARL1dAaNwxMl"
    "fgyMWhlNJj7JR5NBWTIf/gKiSg3hrulLymOxdzR9PEwxagwNloljDHRPeu+oPm68xaz7wYO2GppGU1hJkDE2UAvux+02hrZ51A6j"
    "Ng6gYXAbikCvNwpxA91hV5ouhdy9djmaTfO4N6HYgrlJ8jxm9xUA3GcQKnYGAMryqD4afxSIp1BHWzc6Vhm1i0F/thpWz3VWCwRF"
    "t7W6mjbgCzEXI1mNJ6gvgZhAXG4YQ9/3qUf/QMOAQgMVwznUFkYuojFag7+oKeIkkvAH/0N26kGRyojhlAYXcwpPAHX3276v3zBx"
    "Voh20jEqgbBzVM3OALQMbSytXxQgYIwJ+saYTIwZ6lYP9rwytB5yJYYv45JtSEdn2jovVbZnZplrmT3Ks4UFrp/GZHtNoED81Bfp"
    "gMPLQ9LhDAgdHqwwDefrfKVBqeddwU/RA/xcpEgEKt4QdYcDZ6XSiS45Ggav2h8fHGirn0TwqfiEFPsEGd8yGQMPjE6Gr5L2xeEh"
    "U5Ufz4/nPkwtPV2oOi0o9cPv3rWfHWmwP47ncp2i2TFnYqYO/Q2yKnqA1r+vM8fjvu35OvcWTr8ZSmGdd7CyL3GRqMuDBz3ByZAP"
    "fzENUzRJjMPDs/EYtLrl5WW4ewQmBBTsh3pyABZbqgFBHwwTwX9Bf5yfDIOTdnQCyPAPD5djsMoeTQSaznaCo7Hjde3AB0TpyxNh"
    "M7yKZiGJo8xs2FsotvD4RDFBjzBxeTlhf07Zn+lJWzEcMXVRsn0exbD0oDgCP8bwaa103loukjCYYPiuHTKO0ZWOONs1/vUoZiFz"
    "sOZbKOA1dKofJEnwscUsriWzpE4CsJ2C1n7B3D5oay1m0aBJJYE8PZHGYUj/Cjs4s7WEIbdgVbmdeLECC5FZYdwM1IzlNBqHbQ+j"
    "gMvVQD2FGclF0/z27TaurZJj4EIAz8A2TwI6OsafL0OwrO7hTI2jZI4m7IDy7yXHYFmDWgAV7/5vezT4Nbp8pMUp/PIure6lY2vw"
    "E/bubAFqHuvh1l3Q1pZpO9ZGfD5Cj89wQouq4IJh8lv/FGdQwisLlQeEuQ92rcj1ebbAXQ76bKQjMRIrj5b0F/JUnCv1OcgXaAuz"
    "UdPvQh6RD7TANh7G8hRtE7ZUpp4MWcewevG36W58546W7McHYOzHB2KlkmyY2cna4Hpnx8So+T633Gyf4++zKDy/P/8w8M2WiZHj"
    "MY8FjMf4dL7+YTYFM9o/SdPF4O7d8/Nz49wx5snxXds0zbvYOWP0URu4Gey5dN88uLwc7j8GRhqkJ8B8JgP/iWeYluV1Wz3DNPuO"
    "89iyDbvXso1ex7K6e5ByXAuSXa+DQesh2fcwaXZsF5Ou0+tAumN1uxbWdnvdPqRduwf1MN33bEg7ju2wZB+Lbadj97E6dNqFtOV4"
    "MCiWew52b7pWn5JuD0Yx+h2r71LvlgVAGF7X6lN1pwN/jJ5nMmBsz8PqPYDcweq2hUAYXdcxbSyHYSDZ8bw+AWO6HvbW6dgdAAaH"
    "YWmra3daFg2D3cMUXEz2ui4mOyYgDKt3uz2WtmCKkO70bEzajtnFJEwFgelAZx2s7vRdAsa0TerOsTqY7HgIo2XYrofFPbvf7z3u"
    "Gv2+2e21Okbf8yz3MSyHgzCx4j3AW7/TcVhvMAoiBhYCR3NsDxFq2z2L5up0YRVhqg4iHtN9t8swiMB1LVgH1i2urtGD5evtQbV+"
    "t4vde56Jk4FJmbQsHa/bIQzRottux3OxtuXiGruOYzqEX6dLNGLRKuJyOJagqMcwpS5iQtIbL0cUdHsd7K7H8Mc6I8x63a743et5"
    "1h7/DT1RPjaA1YXJy+EYNeBcPLfbY8RkI6ZMx3Rp9WkGNqOzzh6i0HE8UdDp9xjJsEYM+6xLuTge9tWxH8vFE0PC2npsDGyN8Hd5"
    "xwh/p++yIYnizD4vQep0u7IR7ULZI2SaHSebJG4Uy8lQkKUZerI0Q51oz7HKOmcIf1xgAH8IJjM+TfBIew+vCgglA+QRSHrQ3lfL"
    "E6EXzZhedHJS+hILWsAywOCq7Dxdxuzk+VVBO4+TaKJEkIPUDkr3aZCGOyD/l4OWdZSsjVzIO98culAJ61JoU4qEJ5qweTBvgcUL"
    "HrwPEQh05zwJFovc/RaMJSOivpgbmlfhJh/JdG1U0lycMDE73rWICaZOUIZqLNatjNkoYC1GC8OYWMuTBD9FrZngdL4M14Rt3WKW"
    "G2OvVkFEKxEkx1FcCGwYnKbz64ZtraApmq8hvFmvCyZf2SIfWH4Dzeda1m6AjdeLGgZQFaNuFUF1i0blOKhbNC4EQt1m2EUwBvux"
    "ZRrOcruAp7ysFJBW7kaz7H00H2p42/DEddtrfRy/PLlQkLdiiKpaQq6sXU/FperrGcJGN6ibNlg5zlgtF2/SB49Gtj7O2KZO6qKO"
    "STa6PmaJ6H5N0JIKJ7H5Vpufpefqb3Qjm6td5zg2N7+rLngtiDXI3g702nW/zpQ2XXiuh6Du4nM1AEqywjlvHeIUdxg1MfQ2tqwi"
    "p40gLiNQ48IGALKKm3rfHBVLdLo+LNaaSW/hU7HYpDEVigabCE5M9xNuIwnrdXfSpo6uO7em+6kSjuZbSjTfdleJdlfaWKXGzfZW"
    "GdYm20sSW6MdtiGUkOh0TSyhNfNu6pkvV78xRVLtTWRH8/uE+4mBeN3NtLaXa02p6TYqQ9B8D1HbbTcQNbrS7sm3bLZ1CiA22TeM"
    "nBptmhC/TTRAMtXbftvwZs33DWvQmPpY9U1kxib5CbcOh/K6e2d9N9ebVdPdUwFD8+3DGm+7f1irK22gQtNmO6gIZZMtxAmrmWrX"
    "IHawFGkbggevE73b+HcvN2quHskmGxUhOfFPqeZlEF9b0dvY1fVn2FjZq4ZlC3VPdrC1widbXk3lKzdvqPRVQNxI7csIsNH+axAl"
    "ST0mXhMmaQ0WtnHkWGrTmGJli02EKef8CXdeBu51N97Gnq49vabbrhqS5rtOtt9208mGV9pz5dbNtlwFuE12XEZ2jTZcwb1jzWkt"
    "vfnGstLxKzU4rziDzZqc5z4jbP6UUw1C06PixofEDY6Hl7P1n8fWfupazopfuzYNsMVaQOel5djU/TZ4njVH9WwLbM+2Q/gVvyfM"
    "tv2kMNv6q8KmiUyPr0E50+PNlJMfYAvKgc4bUE6++y0oB7pvSjkVVWspp1B3I8KvRjnNgF/fYAPlbJzIVWLdrflCVRQ6uS9TFRuw"
    "KGEaj73u46SqW6z7gMhH337nSFlXectgDZLX6iR6A/iaKjIlvFTYtvjZdafkkSOIoxn38LHYYYkw34Y+F7fCYEkTAzpPzoNkstx0"
    "oaBiE4XBWbglBNQGILA6HIQo3haC//su/HiUBNBj7QyVXZzMZ0pS+Wqe+8Zdd4XHVK/wrLJrB/O6Pq3NfVrlPpvMjGGu2cyuBsX6"
    "mRWwxS6mXBWJq3/5DZxdFH0MiNtYioOLVkaO/p1UvoTT0bdFcfuib4uqh136zeKeLdRkmfl6M6yTd9Wglk+P1XLmqmF1gO+aiOf8"
    "xq5cDfza21i+qFpRh7tl8PMi12eP2v28nEc8z4XvhFxfCi/ilR6Nq6pQ33hJ//hE9cbwRFyZK7tjWP+G38dvp/6KhqRX0Ot8BRyJ"
    "Yvbqt7FbB/FQM5vX5moMR8/ZHKg23STMD3n9Z//i0f7JyfpH+xzBDV/tH540erV/ePIVvdo/zN+UPzspvdr/ePLlXu1/PMl419uT"
    "qlf7hyfrX+2/zR5m0NQ+16t96PzvfrX/QfKSEh85Pim92w9hoOUA3z7BNvXxee0RivoJvu6MZiFwcr5VgzSo2Ez8LAwXbqXPQMNK"
    "8+/sEaBwiFtqlz/ZPQLCXYbpK9a5+mwyNHhvQ4TLuIWgtTOAtJUuu9AUfwIEeW6HsBfBWV/sNTbrjs8zzLsIoNyNz/hv4bqEZ6e0"
    "uYCAjekcFj+kJ/qjjTWY8SH54pqH4LDb4L8L6Sml9t20zsRnqQKXquLdsJDcuVTdo+S6t7+5d8PycddgeaKyypfNWOXLr4lVvsyz"
    "yj3OaRgn4awRtM8l1EIOwXOOw/TZeSyYJRtnKZjKujrYTXr7djsZJsZRNAXsZHsolVOu7OH7cDmGBYVpEohGxpRX+LbUWJwuTwxQ"
    "kaYf27GeCJ7TirPJndP6irdQ6dDaTb8NxLsx/lZqN71zR0xfliFLpzdWo4vVQM3dTf9jjwBnDOB2rOG7RQNGeBCMT3Ize8VlEDTS"
    "QEpsmOGyUipFIeBP39QUoNAGKkzVANWLvU3YjwH7MAeBYEXSvSoL2gdfUNA+UATt95WC9uUGQft9Jmhffk5B+/LvF7TPcr4Q3uVS"
    "93KpPzGV+S5RnhjrT6pdKDytdaGQvatFBwpVLhPYU+wH9KSeKQLS7vB1tICCJHs2D+2z6/D4xHytS4NIiFX5gHkSnflrvSckc3z1"
    "A0IwAYOJO3ABhN+EPLBRE0S+yAc2P4vGUALMOPQr/C7wF+DCvwM+YhTjqyPnLUHlqXuxALoQzgDoyCqAbZXkfDDIXPlKm6T4HpAi"
    "HioNuFRfcUcGBYRYegVYlR4l8gASZGVHBRd5NxfcKUCVQwnVvQU5J2AOAUiV0zJ0VXklOKiHLqrxrKC+mGfOCDhOOSk1IBbu3aV2"
    "aFZewIpwqqEdIDT3Co4JhBE8Eu4+AABhk1evT2apIiiqryG+zJmbobxPI3TiEAE18Me1FSoI7wBZR8UkQazCfxcrDrVqLmuSNFTo"
    "ipigQk4k1Q5GpLWeuR6oc1Ihq/oCjZRaQxhKi4w6npxsdu/xiYaqIUQiiz9PyI3D8uBA8fyABe+gAH+w1LOiRw3uFkJbfZCPHJ+y"
    "R47PT4ZxeN56Gab6wxOwLzKu/Qh9FIBwunEexZP5uTFPxoHGBBIXRs8g5yW+609ab5NocgwCKVoucxJWaZuJ1cfY88OTy8s2Dmnq"
    "OJIxj7mF1w6H311kWi56G5gLJwHPT6TykkKtNPl4kSIZjoN0fHKBvtI0Js5enAyhmzbUDyYTqKG3teF3kJqE0zBFytX0v6gKjb2Y"
    "L1M5uqbfry55dmTM5hM6qAO9wx9dGIYR0pt29KiZpjDxpb8aQAe/Cy8VqJSA8FfR+pq0EvRekQ6ZKG6Hl5e+rxmQmMGQSbiYBuOw"
    "ffd//31Xx/wZTg6S++ZOP9g5Orjoru5GEsPpyP+3fwc3K8pBnPuPBL7o25gBV4kO6UPK4Un4IVyy0ZaLKZqQOg2waL8+0YQGzk/Y"
    "tAzmXxWYf8TfcnCuJn9r376NEzPkMNrlJWMg/r89z1N0qt9KfaE3BdmP0H1+FUX5CXBzbk5OHqbz+DhKTydRHEyF0oQes0An2DnG"
    "V4IgfdqW05mEx3oL3cr+OY9imHILpKjm7zIPIk7XvCuG59NCyRWNsy7wxBhxxBfVv3URrrC/b+IVdA2/2ukdS2MpQGc2yh1fU2b+"
    "Q0EdbikUHpM2BhroCHrHDfkoTqcG09EezhMgAdCzL2bBh2h2OnuYBNTj99ExnneA9ou7Aus8CdIT5tIMSXzVOvYHlBW8RVPru6EV"
    "OusHiOKKAWy9emA7Gzi8C13DgO9gRBggBweB4Y8Ycf5MxIkPY0BJC6aH7BqHVJDRgi0VkalVzAc5B/QaoOk14pdBMoJ9rxDZz/ib"
    "/GAn4QzUH9gVvIvd/Dqk2ToA9/nOlCwoVhaIZgboaJs6+wlrbZk8wWYc302/gSyQa+wgV0L1k9SDEQf+43naQlLyGaTRcP+AETyI"
    "wcM4uX3793aKjrMwgY7cIrJp24msoZGcmc8QB7w2TynVJR/gRQqD+Z/lnbvHut+SvAf7A90kCTLuy9IqD6ZxKPfwKAqnkyUIL+53"
    "p5W2oE3umIC110iSxLCE4+npBOxWMAJRPYzi05D2IWCE1SQrGth6Mvzp5bOnxiJIQNHgc4AJC06fcLK4fRt/+dlBS3JDAZWjAAgy"
    "XQ0A18lK2kStiO/T1v/3/1qq15vfaZGG3wdpaMTzc0CKdDW0ATUjnmNMkiic0NqT9TfMuXuhbJxhXDHDOJshw8rd/23/z+TCXWk7"
    "+NfO/t6FscKx0g6HupHkRmFUhZsdZwM414OhQqdtmuOvr/baEVr3D6HJ78A6Qceh9BNYnxORoA40bUc2uZPsWwd6sm8f7Fg6JBzQ"
    "Uu56XTfsSOGgbJWASeU30n0TEMYk+Xg4CT4uRyNTo81WzMy28x/Kdi64wzGSo2hymAbHS22kJIA74J/dnI8d0SjVRoyhwy4s+zQa"
    "hQPQPqDn02hyeQlsZwKyjFawKCAH+wc0rV/A7N3338Kmegfy9N8W/Q/M4X0fRAi67fq3F+D/Kev8JErxbPrfRy7+n/IS8uj177Dj"
    "eu6EcuYJRmeiah2vY7OmH8PpdH7OMid9M+BDhGGMeW436HU8ynvLHIj92wm7zoR1uDhN6NskwBK64bjLMsn9JAzcdyaezZqCfkfd"
    "eZNO4LylPBLAvl4UixxevcXBgR8MBvjBRoYfrI7mHyjnAbeEayOS/1z2fmcJCc6G22XLXdAqiMpTUVPI8H1Ld/TOgVhT2lIg30Ct"
    "YG6nQj28Y5OXj7t2pwNm/FDSJuhwMdD4UDJzlhEM28mdCKrr82GyE+nL4Rw0DnNkDuZ329aOFKr2N8GOxTZf8K1h2ZeX8AeUoeW3"
    "htMRYDLKoDrfGX0qlGWMHLAMci2ZTYRDsxsP8Rw3Bl1q1I5hz+3EsOe0u/P/dAeswKICGwtMLLhjD9r4cweLMO2KXTAetsffdM07"
    "oPJo/4F/9DFoBJ3bt8ffuvAvAO7aI04Ag/G3VufyEio4bmcEYPdGjFoGRKxQ7JojQaWQ6kGKkyc2xSQjTEgBykeMJDHRhyJOjAPW"
    "ZcZ7w2N23sZWlTRlWKvXeEpHCx9fXlayOFM4foN9bO2G3/Z2wztDW3AMSQ5xiRx2ZFlSKtuN7gzTb9KVys2W75O0HSnSIs1BnKkk"
    "l5dguiao4BJ1EawSRhSSiST7UTLYjzMSP5Cdsa53Yynq2tFQ+PaKv400yogzgUa8KD6WtofYDu0LYIf6ZMBhXWmSkZEmNuH9g0kw"
    "h9nJ1pOd1JgIx22mbtma6DA0lgpzTo7lISmYLP8zuSP8qKXSVZnUQYCXwhTEtrS03Sq8iZscMfl802M0gMIEND/4eQbG6zwZsZKQ"
    "vkghELpQiTKF6KDIrYW8R21n/nh+HiZ7AUheTVVKsoWNjoWyLtSTHIjL8wiNMpj2GDrxERx/wE9bma86btOpIzExskstxJyUViJr"
    "Q0uGAqWdipMNbaUGLJpLG6SkHCs6b7lwkHV5ik6TS71hblVHSr7Sx1GULNPDXE+Ib5E5Iq2DKUpqvqZ0MQ3KPci8fAcyW21PF5Fk"
    "2xjdDzN6HcWo/7DfrL44U1b4kOIhMDjODrtJ93oSLBgRBUMiqliPNJAq8Dul34I7B0Oxz+f8F0gbkTmyBjJ3xxoE385HyP39YDn2"
    "MQOyvlOzrAFkmhlU8+NMg+JASX4UIz/ipeEwVsyqaEIKrBEk45PoDL1e4+kHs9TAvufWUYk6bsgVLyr5KcMl0OTFGL+vD0w9nafB"
    "FEDdxVtZKfOIjyX4kgH+3rF4jcSgv3fKw2XfnlJigctjNK/4ZKtZC+h6pKylpc0DWcpPdUvqP+J+F9a9D3NAwaToJge87LK4A1VH"
    "oco6mDrzv4gBB+iIiK9HkFsPMF8Dbbd8VIAuHe8MQ2xvajovD9ZsY/SpeWdYroGDmwKFF4swQZ9TAzA/I7KCr2Dx6nKIQTSKWdY8"
    "iY7xnGaQjMT9pswbquS1qnbXUgTYuyieoH9YYOW+jkev/nLg38E9qVPmAD/6chorkneaQ+fyGJWJhNPaPmh7CafJ0Wj/QMfPsZxG"
    "qAhQkeB3Vo0pl+39EKtw6kqGWAkkjSo479y4gR9Ud/BPqMndncgTrlHNbBLQ2bIJYWo1EFUZtWLVUGeuwxIdOdhAfjaPhR6Nh6CZ"
    "C9eCFCviJsrhJsqrL8GQvhtKSTUKlf2QSeUB1eJSCerkd5QQ2YNICmvMlIIb1GvCfwD4p0P1gMd5CvhEwcbiyxXoeOI6F/n426Df"
    "enSwyi8bfQClVRNLE8PSMI/6fGQfo4xRc444UIPCXMYoX76TLx1wP9IFZYLdkdmbz/AiXjuuqqMpCzThylNBfmYcFNjst0NgtuF3"
    "w3Tk+4PwW1BKDdDT56cpKNCocBPTOzpGK8jwOrrR040O/HF1w4Y/pqebiu21OOa2VyhUyRvsEBCs44d4whYSe4ZhTLEPPW6KZbtf"
    "pwO1Kq37jiZNo6Pj/fBgJ9W+VXNizGHefTM/wHcsxb/s8RbHw0x7BM5TOsEtngL3TToEXnOS+x/lHPc/a05xTxQAQ3E2/2/lbP5/"
    "3l5mSQeSd48jwCg73LshAC2asPJAQnbN6gHJurCphMIsju39TBm/EwpgfW2Q1dT3SQU5GO6buq27jY1j2e+3Q8N0TbD+wruWbfTB"
    "qmyHdwwTqty16M8339iGK1fRsC27+018x+hZHfubBGr2bPubaJUts4GXtT6yvg2zq438SZCARakWgKEJ+VOUS774nnF8zI6McXPg"
    "Dl4kp8uAAmPg8YzInY/T+QLMjNTXD4+HFykyUUsPgFO4OiibFt4bHFgr/UwUmlRoYaFNhc5K/wi7yH/x69Onj57+ADL++YsHz++9"
    "eAC/Xj5+tMfz7v368oF/oL+FfnhNvHK3RPfmzM2ov9J5w0LBIgkXUMj7qi6k7nkReukQxfR7pT989PTRyx95+fydKJ1jjMOH9x49"
    "fvA9L3sbTEQh/lTvtX0omTansO+XOaMQ5Q5ZavgDLVjgD/Ek/PAMNqN2x8q+//CKPqLUH6F3x2ACFvIgKwEs+/TRwYBfuNuila8U"
    "w0KPFGOYKoJOx+vhbySQD2m2A18qGjaxsgSYmNQaInLZmoCq8fIEeD87UUeollkNAhLYDmcuCihKnXSXKe1r0ENzQ2We1TnkQUpE"
    "C7mDrZFaAT+QqOnLy0igJshheeXvSnDw23h7riPQyvW8DeKdqT7Ie4SI55IQv68Cq0BN44Y4RycZKy11KtN0PDonSb7Cc3JYGzxB"
    "3wWc0QypZ/lFNgFNLUF/lB8LBW289QNog78v0epJ9EAHpTfW8NN/iusF0LTphx7nlw8mq56apNRxO6waPgUBb7CrGoWBae7zYbbQ"
    "eP9iVBgpT5IgdgukLXfNIGaLITP0gCjp9u0bCZmNHIeRphWwGhE+QxWfc8SnoiUqtxMLFtvLMM3CyIgJEjFy8lSz8mgQH9TpW7hY"
    "Ybyzh+gnFvuKWCx9j2Cn4NERXsUTZ0FE6sehP0q/szxzkCqnPw+gK+Vjic7VhCQApQ+/KHHNxl+gui6iArSdrnaH6h1N57C+YD3Y"
    "/a6WK1du4WUHTDcOj/fTA2T76g77bujBeomFzfbfcj4L8/uVXbyR9/b46TF+x2dNdKZwpzohcMA+F9CYdGY2bdNB2Sqv8Z+BokMj"
    "HOzAT0Y3B2JJ2SUB6nwQr9hVu+OhE7r6u+OhFzr6m+GvaRuwNA7RwsZb7LT1UPHlRhMzoJbzU7DMuNkww4AoGCKGbmKgECF3NHvz"
    "CcZco5Jwcg/N60UyB8Dx9jMG8jwfPDsCFfX8cJnOx+8O+UmGfv6EGr6dow999Fs8QLChKvdhLCouV/oYPQsDkGD2ns5ilJ/jo2OE"
    "lWRvmCxfhGcY/uNkfv6c5bwK3uJtTbwn9yzGpvhrcAE2TXqKQuzoyJeNsSOU7Ajuiir+jOaRD8YOPnG5CGMWbg16mRHIwfIdb02W"
    "Aqv3dJ5GY0IEzP44CTFyKpuPuKZhiAJ8ZBOk5XLKpcibKX/eswgRvotTi1whgP7AQqMyY4IAn83nMQzN68fwi7JhXwzUDQLouHcM"
    "P+jiCIyJf1fKjsJCutnCODYZFC/TeYIvUsFSegQ2SJtRASjteBGFXZNgmhGh0WfnND5NQoq0UH47ZTuSkZmi2f5JHOcN9jkM6RNl"
    "buxl1dh6dvkmB8Ht27/ANIjcnxwPTf3pcSacxHjPVbM/1nKM/o1B+MsL3fAjHoFp2kN+lMwN/jt3nhzLgJe8HX33vYjAQNZpR4fs"
    "0VtKNnSsB6myJCtNZ+jj3gQF+uj9GfDwp8fExBOdX2ZSHnzgraKH+GEadjN+PScUgL2LJ6wbG14IYDM+FSGXStBAYr0CivzT+F1M"
    "3+R+aPts00Cze/HynO5xsgsZgxQmgR+P9WcIhyJGHipiJENqPHmEegaTmTQoXsT/bmjevi2BWpB1kOpgSoynYEwJ0GFW7MBEg1XN"
    "LlTRWj8iOZKbFw3Blo5kkGDFAk0K5T+WBAHzBmtXrMfAJ+7mg8rHx3lxPPyRcNi+QCUeMMMJz2AaGSiNSh7qdaThK3lC9rMSRQ2o"
    "qEMFeEMZhMKAM32lGmY/AyZ2gVweKI2tBuqYA7zm8YrueOCjhL8E1KC3vTGQuxmC8elvDOCj+otjdnQBle+LynOszDYrZL8W2eK4"
    "lu0qveZY941BLGxk4BNbPOGS2yxp0dltBHpxyMk0JPUl0UakpeAiJ0BRLYqYjvKQ9HH6BTvmRspr43EOncl/m/I2GHSQd8mLpDRk"
    "cjXUma/wFJ+L/ijXsgyssv/3wY5JQgwP6M+iD/TBfEnrcpB9wAkNtkE0cRim6b+K3t8Yp8xvGxMhSOgsg0kPZRNiH7mdjPqGzBTb"
    "Edbit6xvYrUGhissjKPpP2S1hJQfvTGkvMY+4/nhaQI65g/4QmwJCvf812RqsOlpgzeGlPSgYwpaEIdUog3GiXoYgKifyIa+P8h4"
    "xnkQoWh7DHUR9p/BfOXSjV//nIQpNJdJJhdzqQcfFrhDeN5Kfy+/NbZ/xsMe0i9TdteSZXDukGrKLv+JixmBDLwBCiuP4nWoitcb"
    "IcscGTITL87O343aCkaGIOVVbFJS6D+qYirwNuS2DVkPkMt0rKH8csXT6kcrVQ2T9Zg+ll0bAZ79RmSKUrrvzBUwKheJYZavZV1m"
    "itlxAnwsd3SPkzofluoordlp/iFX2QqAkYY3LFZC+PhP5VpT1oO8SAU9YO6wRi3USYPmuSsFJlQDD1FlpIik9B2W9UZ5SjlCQsty"
    "yBVLVov9HhbKYMvYI3sAgql4GUiwU401PzoeKnkZWCLrMAnPClhW1NhhvmJxWrzsENWlwuzy2u+w3ADJkSnEuKTw43D+DmYFOyFk"
    "7AP4CCo59BtsZU5IpLIKQqLEMMsnFOI2ZSDgryHPyYZjepk2yG0h7szy8vKHNl0gnMcG53JU7mu5HcZrw2JM8DMZ8p3DI2I8GJw2"
    "v43Uc+wsbyh2HVsmvi/V3UhmFhP1vx+TgQT4fYcflNAWAGUKf4ICrrCVN9xK5Px3CAno/fdjg7e8vITfvKmWK0GekZXh57i/QHdk"
    "jyKS8Ahwe4LiWwn7Ls/QSXnHC4jy/jdan9iUMnHVsYav8fsCrIxfGuAK+IAY4u5bQOS73LdoLg7LN95AOmo4Dv4QYuCCfGiwPHrs"
    "jDfg4M+Ksa2fj1lnuWMCIITSsIek62WDN25NWMd2igk25BQ8QoUQ0vQZVSVsE0mLNpCwVm7fvgUEqnbMtj6TTv7gZ1Q58Wfu3Adv"
    "DlJuHibq8jAksUVNFTFWaF/RMGtRHIttqgooxyd4IWriD6ooSK3O1HZgK0t88zMgWgqUi+3crPSRnmVqiNIPF17m0GcFplqtqA+0"
    "cjTQoxk8O6xLX0dhOn+n8/LdcLoMWw3trXxPivG1aYpoDh+yj5xAFcI4HqJRRh9u5+8GHCwyzUIeKhuPz3EC2EB8482BT1dccqjH"
    "C88DmjQ+rd9QG/mgz9xurJUF+RJiWops2CArthNMGv/A9gpRi/CBLUYD8gMQJv7Z72HKeTkXHFqdxGBzXimf2ZHzX2SCoCimMIdv"
    "xcyKf0Mcjn0GjlC6ZatOiFwxJn0LNEFQ+rJCtoH0RZhEc1jvQ7SyM16NaTri4Fb7+jMO1gleuPAd0+fHDfwQAzOU23jYL74u2mXG"
    "0YuT9h/HeUoNJh+RThnC9zPD/BFOGGyvdn4eGWnroPfw1CHqXRubAsN7h+2s0K2s/cux3gmd2o5yK1UyXWChbuQWqrwuulMzsDx7"
    "OFf0Y1ZdMBOqEuJplWR9JBdEHxo7yYwP80+BD/TkcHiReyQrQvsGO+wSw0qPoEqWm+AHbD3I8uan0c4MeDnkzmVnzIYpPLldzKd0"
    "lbo8xPIQg/yqkYxfUgf3YP2VeMaMCC5CdobKzxi45iO+vvEziIE8jNDxWIg7J9K5hYjvv7hHYowrKO29Cp4qDqJpMFSKRI5iVyYb"
    "OrghO0A2JXKyDnZloOYIbTMRmzXkwiDDvp9/GPqu/YMm7cUkPCaGv8peJieHOj7GRan9sP2UPVj8sx2zIws95EM9ar9rfwDLm25z"
    "sCs6ws9TKg7KV+rLbJyqHCM6pPFYyG8agZJg/YEpwzIwhHcej6Mc5JT3HPZq9AGM4FwRx5Eo1PBw6y+8E3rneyE870AKsyUQwSGM"
    "+K7985FGChUK6pReO2HrA01/AYU/wXSZVy2feX4Srr7YBz8GA1etwUzCZ5L43VC8tMVo2g+PNSZYlUjg4oE9r+gfaPh//XBgr3TL"
    "dGyoIoODH+DXHMv2NKwhsDmvXLHkk6zYX22JM4aIjWAdwKTiQ40ieVeH37bGvX5om0cUfnt8qPoRexQvTtPM+49S8mDC/ED8OJ9O"
    "8ExUcTQmHAKdLiZ41IHfDKaveXh1wsEO09j8A+GTLKtS5dtL+rth6Y31CMi1HsUiFvO7xrmZHC9asg8f9T7Q8CHeHj87YbXYO6xi"
    "Xzgk5g8uir7CLoqj3lqM8WlgbcFDfP5VKl3VuVeaHDK/HuSgR8WgvFPK/A4pS1CqCr2fo/zPL9QkDBf4jQnWcgJip+w/iQ89xPa5"
    "tVtTU7+FKH1KKxjNZuEkQhKqGYW8jOgx8wt1JHAzbIPFwH0pEcY0cemqjTd+kMUugbPz3BFDwoA7B0l17svolrK0Gl6dBaVOv5Vb"
    "778Hvgy6p3QdPw/c97k9shFCFfs36FtBO78gmui43KNVP+fd4gzFfQc6rCYsoG4QtvOT0ZjLJBWCKoDYtuP7QHHjha5pwiKFSUdK"
    "esLWgZ9qkkpX6Dvn5quCe+EXArVKjpnh9TxYwHYyzC83PrLfoypynflaJvqFuKD74Ayv/6Y626shKpL4vejpPH4wW4BEKPtjMAxD"
    "OkE6oI9L7V/zHslu4bfzvC81cY8vN28Y65ZgiEW/a7q4/nBDWak51QXkwHrSVBVIWc+8O/zCp5IBw4ekdrSmbh0peYLWw6yDup2S"
    "DjeQUqHLVHSpqSymzktbfpqyDyxjF2xLLILdvC1wiJrulSqiJwU/I7VcACthWQtyBousX8UWiou8mwOutJicTPQKSPnjcOq2uNj5"
    "dVZrLovLvZ9fuwMtx3NqabIC4CsTHJviJyQ3sbUydlO7dBHz04Jf9hRnX3gYI1mPhpftGle+fXtDZVUa+8Rr1gLIipHxCh+yG/ys"
    "Hk1Pa7Wr5p5Yt1KZ2IglrUhhh2LImlny4tGoXe2HMUJV+CU6h5WbtqrGa9YNkTDBVMcEsHA0unFDEhxmrECmLh+ua8d6xbWYljX1"
    "V+RTWKji40PuzPY3g2UJZ14EKPM/zCr4wnu4LCn62j8KZtH0Y0VQalYagqGXYGghdiBfV4957LeScFYZoEeOXhHSphBIJqtaHTKI"
    "u43feTudg61XaMILjY9VLVg097omH8oh1GFCiw+t5RwYbhG0mphEDQOjZx1tFRp9q2Y8CvwVW5dDq285eC64+oa2Gf6YBzriBYXA"
    "5xVB7UvLUY5kv23cg3y3dUGTZI2BuEBXCiqgIL/YK4+FtDa8UHkEiuXUcAQW96mORuvnWxsvSkHlmjY8asWaTlmw9PoKtRGb1Gjq"
    "lS3rQqgr+3yH64kNkchrN10o+M3lzA4TqmtiZSkzoKprA2PVj1BPfZvG2xyOq8GoJYrcNConyyajDsQJjRpIrSLMQv2YooMaKVK5"
    "5LLNxl05IJc/J3RCVh3pS0FgVrUJFQmDbZshBK1uMxSGcaoNu6PwwFl1SLG1YjiLqrWNJFZafVgH+PS4CeBVIZQ2Ap4FddoGcKXV"
    "WsBJwVNg55GALNP8z+4W8Tkiri6TE65isI5Mz1PCdfgUmINtQwyQwfV+jJyRoweeJEOKYm3EFbE2cguRa4HRN+JC9A3WgsiTRhb2"
    "/80iX6FSxU85yy2MSBhkMyBl+WCFh99r4zlI9blhRIfTw0Zuyk8PvyI35TRn5RXtYcnR9NHhl3M0fXSYUfvisMrR9OnhekfT1Io9"
    "caGpfS5H09D53+1oeiZtxQo7cXpYiukgz1TnMTUoHxpnh634PQo3cSo+cOWPIQPqs2zNvmZ2NnMgTf6Y0QlFTILzgisR6vFD9jmG"
    "nUrxFO7swoHr2sgIQLUXQniKQxLGa5i5rhjZeg6KMtNZ1cU/ACsev9Gf8W9e5KdG9wXE8JO+//JxFZezGXs5Psw771b8cqPfXfZV"
    "7rW89MBDCZU8Z/PjZHmERyTAnsJl6AwlLvmHacmIQ4mcy0tG4SWvurogkKLjYsVvMa9y+7b8yUMEBLo8wkaaCQyilcwp78mhtpod"
    "Ct+5x4dKQJ1m7Pfwa2K/h3n2e5ZxrxvtsCXEPb7X1LQSZ9kL4nietpAvAS8hUmkF8F9LAqh0/ZF3LaI0oNeB+Fv52j8W0RmSYbof"
    "H+wmShiIoZoANmrpiaFydrxtyzcGiIkEo1AYgtOTT5U6ufEBmChejtMwrIQSleew6N719m0EP0MlTKS205uy1k39IhM4Fnogz8b4"
    "oEial5WS5nCDpHmZrdXh55Q0h59X0kiXYkyo7B2q2z27Z9ZOS8E75FNzYAIydId1IOczUnNVxr3aBTonlSzkfD6chlhxmIpYPkuQ"
    "YsAeYgEkkcQ+Xavw30bx5OUYz98f83o+Z4rKGIx3Uy1c/+ek+i2HP47b6oDartgOIWyH8NvqVmKPoFOO6hr8yQZ98RNAtX1Wzc/P"
    "CZkim8dp3Ggm+LC+clDt08GehLP5Wbgd+JMQ7xJ9rMN91ezaheVm70DyKy6zyovHPiEcaCvo5zw7KJ8G8Tty/S6Vn72FotW/OlS4"
    "+btDcsryjP35nv15gJcqs3fYdKWyuLce8RMkkGbhbJFi2MblAi9B4mHlDskZDP4uOLbxr0dxi46PsOZbKOA1dKof4GXWFtvRS7ZT"
    "TzDYZNDaL0iug7bWYoqboXLz7zPmwy7Ql72vCkZxj1XlfOhiJd+GczYjHBN6+o6VuRhBleiZeLSSk3LM54yaQ7oH+rGBNk+CBfA/"
    "+vkyTP0Ru76LoTNhpAHl3xNsASre/d/2aPBrdPlIi1P45V1a3UvH1uDn3jSYLcKJxnoQnhBjSLP5yM9BEie0qAouGCa/9U9xBiW8"
    "3uCfAcN94Jsi1+fZWs7bLYc+G+mdGKlwOVlTca7U5yBfoFbPRk2/E25p8B5z5qQmY0jMo5lws4uimmR0AsIZhEl8UOHo4M+1Cuby"
    "7JjUS3b04Fuur/NYyPQbbyffn38Y+GbLbFluC/OY1xM8jff1D7NpvBz4J2m6GNy9e35+bpw7xjw5vmubpnkXO2fBGCJ0fg17juuO"
    "eOcQHc2DISAGVsYVQ4xPE9zie3hwBXY/Zu7wQ7+bAJHPb/Lt0O04jL5wLjXIPw+Jsp9IfrB3Eo7X8YOnKj94zDjAI/bnIfvzPMcP"
    "nv838IOHzfnBi6+MH7yo4wePvhg/eLyJH7zI84MXX4Yf/PWP4QdPc/xgEaB3jIvJwH/iGl7X6vdblmV0+q635xo9r2f1WNp2WpC2"
    "nG6X0j23A+mu2+mztGt3oX6n59ksbZk9KO9YvR7153Y7NqTdrmdTf67Ztx6bRq/j9L1Oq2d0YTxnzzS6nmN1e5jhen2rBRm20zO7"
    "kNHxeh3M6Him2bcxw+rYHWjScbpuz4MM17UBeMgwoU8LMpwuDE8Ztm1jht3r9Sxo4vYBbkhbfZwOVuhaHRzEMr0+tXC6posZpmOa"
    "Lg7S7fSdTqtr9DuWRXBZjgOAdg3Pw1TP7UGPkLJt04P6PRgbYOgava5r4RCe2cfynm32O5jsm67ThYxuv0Mg9Xtmv+dgRg9HRldk"
    "sBaY7jqAIcuwnH6XGvS6TmfPMmzbsai+53lY3zFtKocRcMkMp2fblO72+jbUd13Lw7QHM8Vyt98n8HvUuuNarsWm1+89loRgGnbH"
    "dB5bttF1oLqNmIN1gnTPdV1M27ByLUh7Xa8PaQASR7eNft+xsdwEQtmzHMOyelTf8mCWkLYd18F0D8eFtGMDumyj0+mZVN+1Othf"
    "FwbwsBzwi/V7nS70i+m+40Ha6wHWsH7HAgJ1DNN0rA6VA1ogbdl9Vt3uWS0ctdf1HndgVh1JhnuQhPX3JJl2DMuFRZFk3DHMnmda"
    "kswhbcEwyjYAMvKUXZLbRX9UitWSDH0iZehfTIbeV2XoWTKPv5+fx2sk6WtVkv7AZOdv7M+v7M+POUn643+DJP21uST9+SuTpD/X"
    "SdLfvpgk/WGTJP05L0l//jKS9P0/RpK+rpOkIDiA37nIQEHA7QFftYBR8iSKEQ8EDSVBcgGPtmzkWpB0en2oDbIDuSJw334PmXTH"
    "7qHYhbRDPNztuCbVt0C6PCbZQOLWc/sWcEOQWg7ITBelqumCtIExUQC6KOhQlgCXBAblGo7V73hY34YBIG05KEOgP7PbR24KpcBl"
    "QdaADOtCGoS329tD2QLiANLdfreD/XU6jonsFXi/C+wWhIPJyk3XRNnTR8EL6U7f7KJUsCycB5S7jodpu9vxXEj3gL+6jwXyPGD6"
    "Tt99DIy01+2L4j1I9i2Pugdh0UdhA6KTRsdZQxKgRN7fBd5voaxyAX80WgdEOMoyZM8OSkqURSjL+ljfcx3bw/ooVHD2AJVNsgwU"
    "DMSO7bksDauJ2DM7ODsHwcVy17O6rNxzEdldlvIAi7g2Vo/mBvqL59DaOba910Ntpc/W1rJRE3JBMhLhAM4wDUvSoXLHdrC+bfdR"
    "2EAaJS6oLLbrcsqCdnnCayh77kvZ857Jnp+k7HkZopP0NWLnd1Xs3GKC5hf25w/2501O7Lz5bxA7fzQXO+HZ1yV2+HzKYueXLyZ2"
    "bm0SOwijUp+D/LnFTnr2TxE7v1eJHXZOk5xO8Q1xeBbG8wne2hhPo0UpF0WUjZaEaaOaCpZDZw/4Y7dLSi1YFMivgKVbxFxdCy0D"
    "EwybrkjvoR1huX1Z3kNd1yEl2PM6yLsd20U+B8LBA67qAVM1UWaB8ADVu4+Cz6TqZgfMlD4M56DhgBYgMzj6yPMtlDmuRUwW+B+l"
    "SRWHdN+jdN92SeG3epTd74DhivYFQeOg6GPmBRhTlguSz6RWrgkC03LJ0uiBRaYUgWnQUVp2HZYtOu6R6p+NC2BaKlwAr6vC3Ucz"
    "EetZYAdiut/32DDMMhFpgIgMGZGG5tSPaE8Kg+ie0NN5zNDVI/Sh6EJsOoTcXs/huHZgLbxuv2eztQDgaW069h5bqx5bO1wMWkuX"
    "bETL6itpWPtOd0+kgTbsvscpBdWELgjiPickNMq6vU4PukcR1UF1oOt1ui6ABdK7T+oI6CsAj6ARsMeBRvok21zIN2Ep7K6JoMHQ"
    "YB96rR0Ql6CCWESYbtdBC9wCQ9brIt32PBe7dWAlyWYEYNEoB+nvgBqD2oODtIR/HTTOoaDb91hNp0ctYXxSSHqe5bC+QcizwUxr"
    "jw3P7G0TdBePwQjzIBENYLsWm0YHaEngFycKdmePzRwwQJjoM0Wv6xKo6hb84wnQaacDGhog2urg+Yvluij80ZrtMkPURhXHQM1F"
    "2ZQsjQjs0y7i5R7Yrw4pcKBg9mgFQEVCM7xroSIFYFikGYHxbJKO4Vkezrrn4NmBSMMwJhjEe1m63wFFFcs7aPj2kPY90klME9Do"
    "AUH0e94eDOehVd9HxEA9D/oFMqV6PQdPV4AumFbsApGjluwRzzGNHjucACx0SJfx+i5NHxRcggv0PjxuAjXZofYd3IywZ7gqZQJe"
    "cZY2ED5uh36356Ia2un1CAy7g7wDVC+TVCivZ5m4Oo6FdAxggNYM5G6gPunR9Pu4+WCdkbAADFAkka47ntdDirS6Hu/f8noEBqrz"
    "tgGz69FfF08h8ovbUDX7Sapm6RnTMc7kPSPQEeg6TuXr8YrSo0XdaxW6P0B1i69VRIlyW3Ix5y8rWkk4DfArdnY/k/tKG7ToVmfl"
    "DUzssrK34O1yPj1Nld7S+WLQ6ohLmfi/WZAcR/EOFYB+NW7vWK1vWm26Bgr98kumrbstW6u5ZCwmRHHUyxfd6ZY7F9zqBee/dsiD"
    "ucxTJiVRpM5wQP4hd8YnUQ53oMCGKb+9im49En6XHq9WGQyudTdYq4fCwE/rRwrFveyrjkN3xuJ52lbnxd+aVDY4T/AJSVJuU/cG"
    "Kn+zV+CG1rhdDzksvq217rQKBLDVjDL0afXwEAY/OTQDdDVqFG77anVbpXDFWoGh7nI4v9jcsLYg+4bV1+zF2tbqzmyGj+nxFfBR"
    "d+e8Gh91tWvwUVe9GT7yrfP4KF469xXU+JsvWAuOv/aCdfEiqmLKJ2sNHHK8AgZO+RIks0zkJVMwUPaftEPjFjnF1cVTWF87IIkW"
    "nwmJljCJFp3lbs7mzxqK7y/zpfUSTZBLFUplGUcpvrdls2IvZzdfY0cotsKyclsXb+AGwFKSPRqy7HeA+VDIrpiyNFY+yF2QD9bb"
    "o+TkR65XYOTHLa4Z2I90M/UkmkzCGGzFNDlFd1trlzKSSxmwpZyfDedjGH8pl/T5PEmDqS/QjEIhnrya81fJ+/xZMjsKOZDPk/23"
    "c/Rn1sA/TK1XlhlG2SOX+lBHJIrXonj+8OdxW1NvVPPnJTUPhAVU/JWymBPdEQ+nR35ulcbVq4QRUXCMURV62Z0uvJQfCRBH3KPR"
    "MmGFGD5wEMuxV7XrhP6W0jn6Kxrcb/s++qZcLeW6jdm6Tc+GxR10FiXpaTBl977wKtwYfWv9C5+h5Us4Q67TCvGF2xFGaGgFp+mc"
    "5XFSHLTwLG3Mn4DSm1BklPx5KDrm/KNtcuZ4jocbzA8INKOhd8SQfCDxLtLkL1ZBvpSh3aEL8HFagjqvfRITN9nvaXiUysQMOLxU"
    "D+V7IcwtPSLKgSxnVwcX7NdxBTIbgiVBWnwQgzNoRFqOv8O9PgOaeNvFnJzt7eDpULocrMUeeaAuQ7lEp4AfN8BYQlAej+sG3JkF"
    "y3d8VGliHE1DPrlgGh3TKfEMwMcwj2HCCv48BciOPopFzwqrBzsB3PyFtDltfdfaSDsFQKq7ZLu8tQUhoku3aFzTX6sGRcBEeUfK"
    "NsKFbN2IZugWNhAvrVUClgRQtY7MgCA7TmjjplqSV9RNBLhkPq4ln6p3o4UGzOM5hhBevtv8gHRd45pXmDW43FmvadYMpKj8lSrn"
    "Ns1U3bNpO1gAENinZ6rTites7UvJxhXVictk6Uek0tEIW1E6lch0JB6rkjWjQ/RCKyx/mbkw2WePpZj72EzMm9A9AfZjFjmZ5/xG"
    "aBMhVmGfkIuCakB9EDFAuKBm4PHJ7BV6VwXhMXmkAMkByEM5CXH/VlYA0JIQkft9fR0LKk2Dvz6u8V7XwMEdW83vN1cUoYnqsc6p"
    "d00f6Br3JUmaukomq/SYoFrTUxq8ZScidejjOtQaWNJwUduaKTbP4uk67KJGoVBZpXrI6Hd6tl6rL2yTdbq9/jYE9ho+oWjOJUdP"
    "0zPannsvX4IiNcdWmcMk7sxmjx7r5H0mjZeLksMkar7SVGVyctboUdbk7Ct6lDXJf+w7OlM8zg35syPQiJc8pirPOQ5TxR8TG2cp"
    "3vSsq4PdoId9ME+Fg1o55SygbWUP34fAu6IFTJNAVJ5pYZScmII38Xd5Mb6xEh+DlfeytL7iG2U6tHbTb4svfHZT8ThMef2Db3cZ"
    "+VysBmrubvofewQ4YwC3Yw0NAOn8WJ3ZjBsqGBQOLI8NM1xWPj/GkNKhvqkpQKENVJiqAap/37wJ+zFgX8vCpysPzcQklRfVJ2df"
    "7kX1yVn2zu34rOqd2+Rs/Tu34zN5M4E2xud65wad/90vqg+lIlOrxJyelQ5aCq5xS/oAxlfiT6n4D3ayL51M+ijSSRH0D0qHC+yB"
    "F/PAuLw/T9EnO5cidMg9CHnECqSNKfxZwS88YK4sWGDwv6oCgJqAfRS/jsJzik5U1zFDyvP5Emug7QXZaHVRhclhWR9iPhaL2VBV"
    "aA/sCRhLcO0ElA0M+cdsVPLQhm5BuQUj0iAa+VMyri5yo4sSeVAVRY+HX2NZTOXKZXFhzvRBUyS5wijTe2ysQi2eKytHyxe4xsxX"
    "KEVbxLVGVYc8DuKcGATiiZwK1bO3yzA5E3nc2yLkUz/ceW8Z2xWuYEuV0CmvQH7erSpbCoCRu23NeW/lTTIfqzwDPbgKBb3sP5a6"
    "RTexMopvm0XS5RnoipE5GI1S8UIQT7NP8TzmHle42hiSj3snVpT94vHahj5WOdW+2DhHMfktVyL0gh2xNRyqzbFt4/rTRbzz80hp"
    "vc2MdLn0kjyH5SzyS6wzVpcb/4YEnRMpdySbgQTN4jrA2WvRF7mtICah9DlEHVz6sRBdq739VHjgK2h1GYq9+WDalj6DsYbeBOe6"
    "6j+bVm34W2GkXBVGFsPH6+qoHET2loeqiqvITssTkFgy8w9t+VJUoXhFfKW0HtmBs0SfigiJoWcLip4j8rEa49hiy0bL19xUrjvb"
    "VnYkSmjFso6WP8rjsYats/M0ao+k3rAlhewV+/LVvMxG87jkKUPURxVCNqaQoBUOnMjGu/ILeh+NT19P8vtYj0Q6Q1abFKrk/+fu"
    "PbfcRppEwf/zFJJO3x7yI6rorbq6ht57T11dESRBEiQIkABopTpn32EfZv/vo+yTbDoACceqUqt7jGa+LiJtZGRkZGRkZMQz9wiD"
    "B1w9TieoPx+CUGAEfzB0LHFxDWUKRnqiB8koT5I+0D0zf1IMP/OBlMIIenYNMBPm+CTQ+WBDfTITTYPIGh6vg1SwxIVX+nptEV0h"
    "GOqeDJVwf2b3ZBOUbLgN0LgNOOI28DUV0COC//Hksc+PeSKIGAvGBrbR9RO901FOK7h/qT7xhVn9OhjB1P8k6ejDowj2O+L8AGaw"
    "DcjMjFuzJ14Csgb0U/7tSXYQ/k4wotsV/Oez/OxBEWVAgZ2HA8AxC/AfLy4LU4IwJQidPq88a883qAxVmD1MXj7Cfr0MTEUh1vaw"
    "+hKcF/bgyHp9su9bMAuMa04uv8x5sDGQeQTA4fbAB4t+/PiBu0UJ8Ic3BYAGwDELsGieEVzMXodn7k2tPEdGS3QHB7Tn4Z+PqbkX"
    "9glb1ziwSdZ7OjFXbfNBi+rpG9y5MfqxlO3k0R7zCIeJDtETHXKc6JDGI+DqJw3yFm7BunEL/l3cQtJXaQdd63ELNHZ4EQuYAWYi"
    "c/DrRA4TgEf8umWg/uVlIDovA9VYBjJcBscndGhUJXznMIWcjCTA+GjIDxg6GPPeOR40orwHBf35Ey6MZ8GjZUEa/JeJgcH14DHV"
    "DHotJcCqStENPCjoz5+w7u+/Cx5T6/bqoAO6fXvjOIIdGAIp9gCaxhO0fNLTrM1+ZsGwlkzAmxI8AWYJ6FprZaGjA64ZGht/PMH+"
    "fMH3IcTnghDUOoUP2HoQtG5Die8voQQZasHGfYTu9zpSfI5I2WtI2UOXYRgtlDcTIhqA9Q7jQVtXj/3Yb2YQhHjrrLp+XAoSVPr5"
    "PeqPH9A/GaPS+zd07qT5jdFkT8270+vCg8YktO1fAgzU2P4V/Qvu9nArUMlWwHkkxoZNvCdwHoWxTgOMz0RqksnWFAUWTQTeJ1A7"
    "ZFLdCsJMwKfg+wvA0JSUBR74pEV1q6wpiohahcIm0qboGwGj8bSUVhIXEKE6wibjvKLK0abNMgGiRdCR7whFvGmynk3SKfaNjE4Y"
    "D/IjPupZZtepAj5ogBr4iCjdocM5xws0GSpPDtsHXTIEzV6eNN2S5GEZ0SATycODT0ga4Kf6zKdArq7uclBRzRkXbZODzgPeezx/"
    "UcD6RWFfGfgLiQVfU+Cn10vPHjnWOE+eMWdkDkV66cmuwi6YKdmB7sB8yA5yMIV0ZMujbee2rS9Mb31hY+szJ+vyLSSiGqBXD5BO"
    "fR71D/k5lAp7/yUzPJo9VZ8YES87Hv9h6UkSsTzH4z8sZKnQyAfmIJOjz/pieSLL3j7sJ55x1U6xTkF7HPSqbg1op1H9VlETxHTd"
    "Ihgn9RTsO0ZlCo/1xfu4Y/ce+7HRsQZmOYDpOOW+eL0MpVFrgUxe4R5lTpGEE5CWHtU1J9I9cRYFjKbjfYRXl8+qWSjH0wAk85SI"
    "WRBaZzte9JDy+A84oXGIlSjPusYtgEwoCYIN9TNj6R9eaTA2dYjzssCTrl2QauFKKKXh66NHgXc1tYbh9NhYZ5yVUcooSVMxAElW"
    "r49dzkNsELWJQw5WvZBztTVfs1F5mmrmZbCMfu5HZYhZ2RN+UodtS5++DOcezlD51Oivr2C18/DAI4E/wa+fId9EwbutLSMjjif2"
    "D86kdHpmfdP9ZQrpwdAfwtiXdCFUxMvApmWnprGhx5NktI0x9CyZG8epVOs4gTT/M4i+h+Q7yIVWs0hagnwr9feeI5xO+qbQRHgh"
    "6StNfdaUcchUgpxRUSHIMakVl6KqG6kM54XKZPvO7uQC0LQ0uCdUCRuQohsRq1rwac/KClcACxCG2iavBqDQ5vVh+NmLx1QEnYQh"
    "UAG42Jxqd+AMu1WXUSapLzvWBwKkW2144iZ1ece6gAuo0s6t+gzn4hY0kQFJPGBPxrY+mqoDlUzxzCUF9kDmmpJ9/MsLXSNAagQY"
    "LACRGgFQI8BAM9kXhihEXViho+ztIjbYOJpJIMMGIXkiiRNZz7T4p799d5P5AAOgP1/AwtWkP/MSd25Dy5VN36gVs3Ri6AnMSxjd"
    "Rr98hjzu2SN5ppjzABi8DPhCLG4K5A5vypRHsKvrkV+RwuCCohQeogXLsiOW+TsCNftXJa9nOpVSLT5St5lP+5MH/P93uA1TyV5m"
    "hxLhhLxMGY9IX5T9CxAq5r7el88Ao6yBNdV28ALS2RWMRUezhUtBmc12LuYfL2Ay5GfXWuYqqHzKHQoEAp5NV+Zm0o1/tjA6TYgw"
    "TLPeN8cckIBspznW+TTD/Ut9ocn6L+8u4i9Q1tL33QbFmNNhwGTdAneqG7KHF57fvnNgsTIffvsuor8BL4xmjowxvODg5SHyu+1c"
    "zsAsJPXbTvNYOYJQA8R0D285X3+WnyVw0g/AFR1gFOQ2XRJ11Smae6wfdb8d0TzPM+/SVTiuZJeDKyCLP9Vn7gHI1egi9z1qlrlF"
    "3W95ZMH98cTDY+uz+CA/8GB/4R+gwSVdiVRhJEZh5ljm/eNJ0sxdAvh1xJO+yQE0PnN/iM9yinuQUtyf+FfoX5IXqif105wA2tLo"
    "Rvjz+Hx8YFMC1GA69ewlEygCfhL6F6szqD+fWCAvKr4n1heEEeu1xsFpFN6+P8GTn6EIYtGWzSypZHT/wxKN+t7xEmFnqNSZNbxQ"
    "WDno2NH1FYbym8uNwB9PC+b05HIj8MfTEjZh5R6m5zMwAYz2248fJy/u6kq0UYpn4abHUjxLJz3WjNSce67UwjGUjMZtPPXppuhy"
    "O9VCpv6NwAE7Mhavoe6kOjI+XRRl7h2BreAEGMWejErQRjX7ZwYnaIOb/c1jRFoLQJF4mEdtmPtfOiwyqKM2qP2vHQQawvppr11+"
    "WSbnx4+dKUcfz48fe+16zIJfWIXO0YHUDjemey6wfpElyQJbkiyJ1hstqAtghkuQ03VYp388Xd64RLtkK+aeFM/FuuHsnwQPxzFz"
    "+B9qkzd4jAtiXXHKdL2/rqHd0xECtv8LzXjh5JomCcwPPTVus3J5MSu091hHtLPapK3JnSS0kltR+/XdffrReVf3YBW7oQrFYwY7"
    "txU+sG0/KjS757WLRQIuUWnJL7pQaBcjPRI9V0+igeYn2ckAyqxXdLTFlEwKO4LZFqsDDm2Hye5JXxQgdZuhFCASCayXuRZgMVDv"
    "X3pJxuOoC/A+6CW8NpWe0Y1L8/qFFNL5yYxzFy+fPXajLow/QFQ6hTmUgeCgIvCHl+DGrkFUvE6GZAotCbpJ//bJmeoRItDDmWc6"
    "EgKx2fz997nAsTL5ciig387Tswj1YjYFpYvS2JXULTRNsAbR70g5Xq/dcFK31DKB/ARIXRsQbZn1aF6bcLWppgGYof+oolkAcGnG"
    "tbpdDgKFhiPIQF3DisMiJU1Z6HJRnwIvOCCasKKDAucXW5fd0w+b7G2d5s5UgCDHlOaCHMAlKrSm1VV/bCiLifbYcmh8h/oW3oWC"
    "JWFWv0K7BzoRa03AsnsGG+gcnK6VlAgGjjWzjra5DrdB5i4AI7M0/yQZKVa7QkOlbitjWBSaCmFjSHh0p9CPnqVBWddmRfj6fGsl"
    "NXNCc6q2o+BWkZkiKuZlzuCndHYIrYIbmDIOrd2pRZn8afzesQEqUbPBfhK584eOKcl8b6OB7/G+ODbwKOEfZsUgMoq9j1EHCH//"
    "/clDBukYueUt2HGs+FYEIZeKTqOEkDkNfsErgL5E+PiG1EY6b9s9q74hUDskrQJjLKqfZ4u46+MoVY+P0/TA+N2gCCRx+IROZYiI"
    "AdgheSsBf6oPQQa+SE+J/ysEM6TFAv78+AT1vfAojPiqHWSz7ZZxx6i9niKna6i7wXBwBA6RwMEZcMCfogYHZ8DBYTgYFeON4s8p"
    "t/t2rLrweLhnCklen5uc+a+I128IGT9+BLH1LrWBOfVE7Xgf9W0f9wd3E01OtWwpZpDwC1DKPttue0t40xNH9ljy/eNH3WxgzUy/"
    "4Fh28weFQ008fSJlP31FbmNwuQ63dDXwhW8jSB3HYjospoiIr/pYmdqefk8pPysoSqvzS/5P5OIIfTAOxaDl8oc9+vOAE7Uq2sb3"
    "6a7jgT31YW2A3htfvuqIefsgNacDU8cREvHjU8osFsGe8DJ6R0e4gns/xKfDpxQmVOy4hKxWvcPFHaMd+zWg7ZL72YE5oZLEJa/l"
    "bPscSN3XpVgsESgVpqaUh8/1SOOcuWWOVplwxike2io4zC4RWfVmddBT7xqFMQBv6ouO1Q7Ur7j5tjEjz/w4/dnMUkGTxmMxMlla"
    "H1nyWN3x3hRlvcMCCx46IbPxOkJKcGUBlbMAC68BLODT0Giz9mxRv9DI1JpkTXkIuy80ZKRJwpFQ4Gcl9b2758GWKyPXUfkdyDyd"
    "nr5MtWf0dGjSq8VlED6Jt4FEQLVhPBk1ootiJ0EFT4P4CHLzCsTQqQZLwARGrFMYbERIPjTfA+yjaXpfgAwei4BDiMfiJAz5L2Jk"
    "wLHZR4PLM86+qAxfAvC2Af8k7/Y5fHVpHFbvBkHFZXAUVPzbOQzqXXdlBj5Q11kKZI3Xktd1LE34UBCAPzSJhH00JCr9dR9vUK1d"
    "hkE1TEnGyzqOsj6E86J13SG2mE6TQ++bOvxwFuhnnDx932l+0cmbLrYY7SkQaMt0bDO2K5RjOr/BXRCl4tX9wtj3jppBNLIV0LkT"
    "7hUH4MiUevTJg5MKaBIe6OFyQE82Nx7zhDnemdOUAFFOfHGJaCqArCo5TK9HhJZZXiYYSnixZ7SvMLzpo+Fs49l5feDxTd2cQU31"
    "sVJzpA+VlPHqwXwpD1/MR87CD6EfBlodQVGiI3BBHfnU1q/3TXZ3iGUNXbAD0y7+TOGf+DMDU8Ab/Pf1CdCFCDwFkutC8YiMQWW/"
    "/w6NU7PI0BnL1s6GycacGXiz9g7Qg70Ifnei3Y5HgvhSAFdOTafu00l7FZqakAhSMTM3ZvHrC6YhAyr4CXYLcAT4pjtuu2LHbTO7"
    "4zYF8FsY4c/iigknUz6NdPdVxJGT4U4LuVU6ygr0q0Scg31+k/ffowJpF3WkuRFzc/SES7n4dJqh0A7Ie9kHRYJxIegqKNPuuRfd"
    "tWPQ9DRzz3QrRunHxVFGZ+x/J/5sTZ6l3lkHA/fwM1WJ/7qHn+v28qCs2YV0frWiFcsPMqDCo5JyQDHOoauYYCRO7bBNFN2sBoup"
    "TZxk98BFyAV64gVfmiTjTa2h40DaUxiFWVPDqKAjVbzaCfi9lOZH5S3doIKuxOcyaFwJRQMxj9/ksNC5ArL5+XevW3Nwdbvm2uDT"
    "Jg6bjrl1iXPd0AfdpUEfoaL6AD2Xc4s7fty0tlE5h1X+attvIIi7XRKq+AUdOxHJ3a4Jpbyla56EvXkD/ZGibyJ0CnyqaRLC1eTW"
    "3GUkWu03jOIBXRpYHeZhj4zQG6rZIaPFYx/pDjXh4pDd2Y+5Bqcs7cGqErXF4gKiVsxp9zNve66eJO96k9TdBIK2ABsAa2mrO0u0"
    "YtmRZ9pRoo/MhhDKoeBdLFDUhN5LQuS9i9mTyrDae6rasC9AZ2VOqKdiBKCBrQHesegLpQfoQZ5iYLobWeyh2Ix0QNPg/wwHs7S7"
    "USp6ADFdNo1Bc99+NTNTm3d8JGIASevBgIQTBH6v8MobpCYHmrdtIa8RiSYVBSyilc3xrYPXyqDM7e5ND/gEczLn1pJgdtBpB5wq"
    "9yoX0vjbz/emsb339KrzPncadFhwGsu72zpu6AHGKLvSrNWVOnWmGzA1iHyQ3wGP0BHR2LjAAnsFC+k9wTQopmTyzXtnLyC9vO5+"
    "1VLeQUa6I9XrvbgKWG7CqqWmEx9zlM20enbBzNGbs7MTZeJ9jOY6zk6fHSdwzVnc4ToxKIFXgJCLSmpcyZU6scNCqkHbMOwEzcPo"
    "F5o+zpGmDb5qJ0F0/n6AdLF3oF8zR8YBEkw05zRg3OYjatM64nt0Sld7M7HSlWxEhxjomfLE61QLRXPAhdy5BkAyhZ57iKBXKJwa"
    "JOg/IP+mFvbuSiwOOFuxe3s5kEiXcRGJkFCz4GV8g5f6gLWNd+nBgRJsO6IJtyJYI6zwRlHgngbCnRH/jMB3hzqd6NJlf3aluveL"
    "AP/ddRzv0FP8FeXIm7YNPAdvE2FxYe1oaOZ9+AueUH/+5EiAcTs53qUiXOm+1PJz8L/1yP3PQO8K+JsB1Cq8F0a93l8C893UoFf8"
    "KcRaaltAB/9x3slnAitube7vHc61bqLAfM3NbQ3cY9luh2YSTskeK007QMGOQKHt4wpG85IfURGHgEwuugNbfe41zBo17hMCOh08"
    "7DhFYVfcK9IdKvtIyr4u3wlHk7bIZVN7XepTdncOR5ZoB5oC1yUMmBYoDZ3mrTWo0/Vnl9BqblUurlgwAa/rdkgcsZ8eh12v8pY4"
    "aXeK2qXA1buR7hZrzB3poMZ7kU5VubwN+Hcj/Q0B2V4p6YB0p6IG3Ev4FB0f13nx3hnJhEsHRnMXnbiSlbfYqthju9mNLKGlL440"
    "gGyjUXQOZBQNI8JoxpPQ1opc5e0fdPOSD+aoi9jsStvHP6VEXbsBjc+ISuVTSn38jfxGNmkmNTjKJUnQyRpOncKCaEP5lJLxzqK1"
    "afROt4B/2ktYmkCv2vF5fMArPAzk/onaWGBAsjsFEFfE3cFfVA7gFJbgihAZkF6Q+3Fw5hCmVHFA45bYg3RxAT6EnSLjNEhVb5xB"
    "27zhlY+niNJqfUp9FB+5BfYfj/wzw2LQAJXWfdHAGpooS92PqnYTj7yuo8cFWmsADFQFA4EeI8Bfz4Y76AA2LYQqeWSrNHXQ9E8Z"
    "jQNQ2VrSlKFuzql80y243oClDy2ZlCJzThXQlF4U9cNI6yhaydSiWZky+3kBLXcqC69/ACQ4Amc1vQcNpkkhgstZsqfEFKEIFQA0"
    "bJQ2xFSmhgjGuaBGD0RGfy9fgA/riczHsOAnWVHYMMJOfLgkpj5nORUuJF7pki8P7/39d/FxDZivABlwU8Q5TowA94l86gE6YhkT"
    "D4KN4gKaSQpoGlIa7t4FQybcZKH8ZaEXm9SpFc5AQda5sCHjThm0GOpY/KJKmkQ4FCfyYgqr1CVGFloggvk3LZqSZqSC4/PQg9OC"
    "HRbIDH8luQMUWsItVw8M5FaAIrC7RbIwwq3MiQ6lTM7TnUMsBSMyt5u+MHj16KF28GfLYFBaRZxRk+aswJnT6tBVfl1acC49kaWn"
    "6J2hmKb3wh5pnE+HimKY90JbQeP0KrQsQtEI1tI5CxncnXhDaGso3w2XhYpgm8H7IS6p4iSAAiqOi1njOsHZvd8vKvL2flHxV/vd"
    "s+J7GiWs+dVmSbm3N4zgeLXZd8YWfT1YlrEHOiIev917Me9kd0tien69HGUZdr+gzCmcine4pljiF/fCbZnKvkbpJ3PEFc1E9R72"
    "j6qEixXgbvBK1C4Mx2slMTNuvtoi2n8AAiBh3YlrZtvE7pTVz/r3usX8jGwe92Lood4Aat5QFu083fdWKLwVFNN+d6fcq+Hd4NEA"
    "7zp3WtELgQ1sdr1TUovTNnslThuZt3uhlw07+u7boqV1/ydFS+uao6VlT1TPOfjx40ce/+nhP+eThyoPv77bQjyVyTU+q6qQfj6o"
    "0gdlLwMRG950PCCcgO33gyamPv5bWfyA9Oqw5AxkkBIMKs/CLfwDDiyl4IBRa/bEfWA/fLFg+avH+wHHF4GRo3Qge0YMLA4/KyHD"
    "N0JKaS9FmrgoCYf1/eVRlTD5kWhXXvLuI8E8BPUHFSgCBWZy1hkBZynxyZTyCIVC+JoZ1Kmze3CkQj+7nDqlnZpyXvSqcZrW3iGA"
    "gv7/43lO9fkfZa+ogl+JH8HYj3DIC36CrXG35xZe3MJv/keVQ14Fnsl4tA3AwAmaVAoXGJN/TI9wBDa8fiSxB7kv0//4Dy11SpK9"
    "dgerNEnltJ5wPq+gvyCNxjlVnoD8HYb8wr2qf3LkuIkevj/pX5+1yHfiEwyvgBsGsyf+oX4WfT6v/EX8+sSB/2gzJRvdbP8nxwVM"
    "/z1xAbdviQu4+WfjAm7/U+ICbuxxAev/YFzAOhUXsOEYF7D7SlzAhsETu39nXMDuf35cwJZ+Ereewi/u4QD16H5IVgR/Z8JRhn9Q"
    "MNcHePozvtZA/oDhAXEi+SJ6I3CmPqoKSMqCjWNrDhRHztEk5hoVO85cjJzVbNV36GQMTrNs03j5by6i6cNwO1AzhX5ZxHUCDRDx"
    "52tTMD2chBUOOIydAk/iAkqhwuJZwx4SAWwOYcYliMqH+klpf1IPQSIcU12Z1bew4uHIyVdqqJooSILp7XTI7DHZ7GA/QaldsnuK"
    "1/1g95HjclTvbtQ2W1lGD9dVs00cnVu/N30o4Jo9Thv2tWHCjO6txjZEzScOFbRGi2gjLjSFHTUNHq/ubccBXUEtknEfx4FziQLX"
    "dKB2bdT34sThPHeM4fxXcEZ74yHLSvdpYUoFvBkwDenqMXnDIIiFVTgBW5l76Azd+YUexE5/1GcNGka5oiSB9Ewrznh2nIIxyZA7"
    "ItgC5VejZrs0MMU/M8o8Z+BmaU31wvBWemOWZeHYGCpjawylmhvDYU+gJsxpvMRJEtaVUc2RFPJ83TxMKA36pt+mPhU7yOjRL2Ot"
    "LjvNsMOncTKDPDgAtq7pU1Mco3kN0fTU2rN5XVMNpHCNK+FV4aSVNgOLlwkUC4xI7aRZi64a7D0vyAWHOf2VKdDJwjoLOd3GBukV"
    "Sav4PuF+k4a6Fx5NqDT4iS4UqJmldMMOrVqBMkp7rW3oyuO3NqNVwC2lZZ5tSUoZvuVw8zdGU5sVHugeFq86xCIJJZGzG/TabhPJ"
    "Kdw9mtALZ1LzX5PivL4gjndv9yxCXJ/RAoKZrRB+DTYexo3e3OnwIfis7zaU2uxZ5+fIN0vBVtVD1pum835+CKbu7wFui4EBO02D"
    "OGz5TeaWpEwZaqShE0uTDsbqFtjkB82MKSQuQVdoVjRBp2ZEgsAfDoh5gOmUlAIjEaiPNjUnutKkJAx8btVG5DCcz85uykS4LQeQ"
    "szSsY7SH67WE3iQw65Nu3bs9/y1JwU2usJXUJAoy5USYRr6Y4ZXbUXZb3c74R6cRBhweDLy+izA0ykOyPOD/HvHJA/1cQpt7dG3k"
    "fcRgeTXdAznOyAx0kRcM4LkH21gO3mW/4gddN4yEl7DQJ5SawzpMD3HEDQoW50DqUs48EGuQF7cFaGrOKtw0w863yKB5qnns01NA"
    "9xoH1ebS+3kmc+z2M6qah1bJ0xT6Dc5Ce3aR4+b8jhX0plAJ1IxWUdOuOoCK+eILOQk+AtkH7uMwsshclQXw87MT/GlwqjtDLOmd"
    "6immjo3C/b25aH//2kBRMei1mgwWfaMgF+aWYJHX2ipJOwPV8ON1LC8ofC5eKw49aJnQoSXYsQFzKGTgT3uxrok6uj9HGSTFlS5w"
    "NWXO7o2u8Ke9WI+d6WXAb3uBv0DT3TW/VKmpRt9kqs0U/FH8/fffgIgBlXmGo1DHMxPcpMEJ4KOpWy0P8Q7NXwTH4PY0h7VwJ9Gc"
    "qIpA7uyBbcrs7JPsKfgGD24q5r3GSAdMCchPgCMSf2LahodcruYJUKiko60HdrePLXc+U5DrXO+j43CM2NqOzFM7dFHnWliHcUZm"
    "36O7lMUohaBnDZ89YEj3dkrdzRIvriBbIUNS2VWD3SFTqnKj1e9NqTwoI6qqzM+OKueZWrzGTb2wDjq+IaMNqt5ckBSoGnfyNKeV"
    "h77mtO1bPxHSX5o7IkhkuF1reYIZvCVDAQd6NkkZCAJfWixubb7xzoLuWV0QZp4MsxNHy02tEbrWIvIgyQWKByX03MUuxDSgM1Fk"
    "dM0temhs2iHIKiQ9l+emMTNT9CCAIPYBv6fBNj9wnp8+qfKR+/TVOyWIcJAh4Wnwl4DW+RtAwwuEXCg6+Y/8yaC/H41gn2bqMcX8"
    "NJ/k4SWHA01A356EVDWiezFAr0tgnddBHxboDS5ArsQ1Z3JI8+MgR3KMSggJUperp3En3kQTpMq48x+z1Egs8L7jV5SsgPyegiM+"
    "VqarLxpfclGykPFYci1BXQPUkJzkO+jtHvobhjG7JAVwKu/fK/WAuftroo6lARf5xlLKUaixlfnHhYgXY27Mhwaaeq00ZNTpv0eR"
    "il74NXEO3smamv2RlS1Lp0dMoaShB8TNHQgVLwTCXDjhhW7WidgwTcFdjGBN24BMaION0ORlo1cnpkILPk5yz71Vf193bAQXUt9w"
    "eiUbn+XU6nT8fP1EC4s0gBRGZ7kdSD+/gbfZD0E6qtHydGB2b44WZU5GnioBycE1Cw2xvS5gf4SI04mA3oq0eTGrur64tPPVy7hT"
    "PtozoCM659Mq5SX5fTMLN3WXWYNZ9+e1BWD5JfMqukmv9IpwmHl96glrNU3+T077fdkb9kg4tHVJ/2R/xpY8P8rQCArLT5+hjz8e"
    "jeoZaktU3Y4MRUaAmlJtD9dN0rrwvQsM0u1YXguI4DIwI6L6W9iMnSO8YQo/Oy9evJn9zehEi1nDqNcJQy74ZIiQpBu20AvOlPXZ"
    "qVUREvedjfCdeLet159Hu667sB9nTOrDgOPSY0xakleacFL4Y5zB46wbVajWiyxH0eDZ8w/xZU1shwvsFeHYJlq6DVLTDJkG+fGn"
    "ad8QRQw5D+FSk0xeQ6blhOIANfSFqkp7aDnDrlgsscEusDz4Kxiw83ldg4xVCtrZkMRuVTzeZ4/l9sNyjKZKNzXZzmlw7lP7z23y"
    "1FnMS3TxlCLu1+xwr7IMSgZGpOSmTucEyPJ0IXvKEGT8Bq2CuNMRmVcu+dXjDY3euKzvzgHevutvyaeaj6MpCgw8DUy1WB9mkd/h"
    "dkO7xWBVVcYzAk07OQiXoYayF2GmUy/jFg3IYtYOn/BpesU7ikJGdTBOYYI0MtNLUMOCUbIQXzPQgPn4fOyU42y4oYV8QheeFBg1"
    "jj1xrnOqRxBHbl7QOUkhgdiZd1mTOIN7z9LEjnhap+uoDP5FOl4TwrR7T2qVPJH3LqaZtONRt02BjJemXbttEnnigozkOGE5fT5b"
    "NGPakVSLC6XpO02lrKHgsxojBPVQSGPm4tYsCTnkNI/3Ag852czpPNsh74k2+NTkJvTgE7DGFgvdPAOaszIjzhjvR/GRF+fCcQEt"
    "TxHk1jSNrcBq+KT0wiwAAaGA2fZoRUQV4Aox1Kro8YNeQ49rK9BUSQfCMSjQW+DQzJrs6+neHJkMqn78QDGWst/oLVJ/FcuYgy3Z"
    "poHg08l+y5EnaXhzB9bJEMyhcWce8reEybqLgo/jucdEWT8VO+s/IR4VRTl22z0XnOmqKfoJOg6NYW1B2zR0Gkc2oNr+CkMXghpf"
    "lpL89Om370Yb5cULvMWBBviVuce467J3QE8LumBw0P2/trwdwIZqAzeLRqcYJ24j53525BwaOYdo6lW+4ND7C57Tu/aWr03vXftk"
    "bWaNQp6ph4pgBl3AyarM8qp3SpQ7Vvtf7Qbhbj/mdWdV7jq26zTddDy1++PSZ/7NuHu9Ud2I1Qaq89y+HVpnDCBBRFvbTschh3BA"
    "hZ+9c9MOFgHDsDF/Yecqwt8dk0leGcBXZrgGInXylsnZwNR4J0B2AluJ50dVwi/Qa9KZk7OsYjop4SwvuXOkbtnfVM0YHNL4KENe"
    "Xf9XGxp2iYVA8/zUINEoKdCdBthH4/nocbOb1SMim40wjabNtw/vwaHNABi2qX06NTRQtJCvSAfHOF3FajFuucMR9KfC+xwYuMZB"
    "f/mGwGQW/RVsBevgHKOImYeowqdKjIMC736/VcVJdca8q0PL5Yu7HSj3xz013bO70S7nC3qd0GG22zXP+Is39RDUH2n+CdoXfaAd"
    "aMvucLNwB+g/A8/OWKIsipmfBUkDx+FS7e8iGHNX1Dy63LM5w+F+FahHGvsjcPd+jzPI9W/q1H71xL0wJlso11CgdmMqG0/88WM6"
    "9frUz9hO4yHI8E8f9dnt24p70XPQN06bQUXio9O2iIiJkZ+wzvCvtWvsSKhV0CxRRXp4FONa6+Xe3Z8Bw90LW6Pt164jZM1EyvQu"
    "zTFgOF3AqZJL0GnRaionWqphdUw0AFDAQxcPzrC6mtNYlbvqPXNvd62jyavFu9TDX5mPKBAs3arzsmIcbrBNGt2Ao/lS4CtkZ+4q"
    "MrKa8OWwxddUeZGa/gZE8t/4xcs3cIR5mQI6q8MjGHynyEwF/gu/gIcbEZ9o5GdZR48qwaH8/rs1xfMdOzicimAeOeh4i7gv1BPg"
    "c1o3OyFoJ2jJgsen+3ZDLoNDhIEZq0Vf6/iAkLLjf/VNwP3l5Uoytm5IJFXscs+ZrtAx4D03D5DgtIeLltEaiwO+buaIHRvDmbWi"
    "2tHF3dYL7BkCeyf2NP04iMPRp2VucQTbNAUKekbGoZf0nu+0czaRQW+i4CNs/IBMfsHeIPgn9dH5jZNH1PceHgbKc3qDru/AqEdI"
    "FwzYiABsuncjx2jFml4YlIWLwlxGxyfMegKf+CGhzRmPY8uWMpZ4yObZdmUZzm+vMG0Yc0Q/0VI0PTP+gtOjWz9StoEa56gJ2kMt"
    "lWbr2MMXY61FJ+hewxj7KcWwt7Q+Y6MtLikQwb7+xfAh4TjBuCLnRiLqvRdntJoZUMZnmeLAPKaY9An+/3cYQhyGFtzg38SNidM7"
    "OupVvGN+CkWrVKZMFj7Qh5eAmgUBNXE85VtCEzqRPsDtCGY+gRHWYvN/+U55jjItohy1AdnL5JrS8VmpE+vi4KLjaLt625vxnwWP"
    "HBOhWPhOcIyzoxsy6Te6kC2n6Ee1mkxLXN+5NEG7xwNkbX0x/FXzUNXhlKOgEqdPPfiq1t5g32kw3md6BRr1AQNGM5cWBM/0e+Bl"
    "yrifArVHajYvVbAhiw8tF9jsQBCdgu3GWEAMgXAVvex06uQl615n9tKv9Ei8dpm6fb2CpQcdzrdC+I6uTJ1Y/ZHd68ha9lXUW4vr"
    "o+q+o1fHCm+bA6f+tTfjb+iZMLlnx8E7E/80OKWp3GmcL4xVVnYjcxdLTMQipuRmQBOxnSu8TLHjtS6notjRP6F0cHFvhAzmaTWe"
    "arylhqq3rOYwUXPy4UZTmq9NIqUSPovdT2mC7EK39v9IPyiyiUP2p/g6uE6SERnkC6NfZuYAz205gKrMPXBfJi6yibG35jDb7C5A"
    "d6+NZsP0zJZBPqlJbeyfmgSaxEl2H9vkFgPeyxm/4LEPbYz3oYUA095PHa0fNF/Q1i0YO7xEforM0+Q2Wt3xqqkXZ/iZKVocU8b5"
    "qtDqsJqG0+azWs+kvVZDDNGuOF+ZVlcsExn91epTeJ/FCg9Tn8k0wy0dXSGSMEon5AWe3+8B6o47LKgjT9YgGUkwiEHtvjEDi1+f"
    "byemhVpPKScGlUQ+QnnwMYePI4AkkBJPDNR3KChHWTPZNXeSATo0D6WZb0x3z4sicUSa3zF430JflW+M4WW5/o0xvCifvwH4C6en"
    "L1N+AVgevgaafmXKMAm6YwKJKAdNIfhLERb40vxJwqqEfMBPSPuaj2fqA3mL1FK4y54FNfXicN0CdCjaN4sQCoTtOcAzC72B43Sy"
    "UmlYa1ZYKaj+GVDQJ4UAHbQOBE3/uhE8f2Uy+q+Bjns7qNr+5tADyVfxnT/+RA+eQBr4Js/IsN927QteQerA0Y2TFMLajAS9v6+G"
    "983SSXPwwvAMi/ce6akte6YU+UF7OpSmkz1ImeNSOlWCJMEoRFKOOEUje5CyQCk6+YKUJUrRaRik7FGKZVmB9B1Kx2sLfK6fVN4z"
    "xSvU8MHW8sBo9oB+T1MY9l0G5/Ap5SgecHmk/SJx4IF4cgFtSBIcEnwJCl8bqV+Coa8/fjzZ+Qr7aH1i+/vv9jTiJpBldJ0d4Fif"
    "8Cx8SrGP5k2NhJrnNTC8zBfOcBfhIeNBPqjRiLbguBJg0LgMg4kpg5ytccjRJR4ksUyA+jXiEhudXVNT6LKHBLpIfcEIwHQKDWcN"
    "19gM92j4q/5KXL9+ISWQn2etBPr4SpRF7KP9mGfy9c2ZdjPdhS2n71jQRQY02ccZxrZmlEDaPciPBU4FA5KWyykDqISDM72bSTMJ"
    "8IpPxgL8BKrqTm7pDMQ3TLkohRQBR+69tD+CKZtCZQ/VqsZiPqV4W8ALE8+xF3hG1OebfkMhCoiLUFLLyplgbbKKn1mbHtdUVQ8X"
    "wmnBWH/8IAU0rynql4A7URPtpP7TkYSJ8xAVmXK7NARL4HbgL5dmwOEZhaVQv9xZZ+SJHm6MfLi0hx/qq1/C7q2Z3vTjNk1Jr61Z"
    "Q6wj61VfNNgciwnGwC4L7czJglUAiejrNfhz6/XXr9HXl9tb19GPHx7WRfh7xpSnYc37Dy850wr7W5fWJ9M+/onmUMaqi/yqVRf9"
    "Zasu9gtW3RvXxpc6NO9D5wZd6iT+WDndwsN1e3hhbFB+uXly7pQ3/d+XdGCqwfT8TM4zXibo/fri/QpXaQ2sUoZ9tB+En2lQDUcW"
    "DFrBIbIY8x68GvWwA3CQ6CPLCgIM/5dCAoHuUsJpCIhHlD0cDxvTGnqe8tPUVD8VAJh18UXvy8wRKBgYqqGvuiBjhYRMDl3v+yeL"
    "T45PKWrsLwZz+zJFfSP5EzU3/eqFOE1lPNDfScDL1Aypixau9IhDXh0AIwkJO0RpYMI/FZ2IzEDAMgNU/IUpPBLa0ay3jNDryJgD"
    "Fh5LtwlOR/yDAsTgKWNq6avGrJB1HcAXNKqbGqRvgkvDn7YzlD2SsSnQaDJ3DbtNTac/05M+U2R+aKxqiKfQGrSglT6du+CVJl+6"
    "+DPGbWpqOc1iUjYh2twLY27HGcE0x7GpEGyk5YYU4zTn1TiCl+l4dsx3PTIJp6sDXpjvmoOjtMeOh44njyYT+zneP7DifC3J3OJB"
    "fzRF3uuhhUi/uoKvm40HQ1SukQr9sqBHKFQuStDq2nKNVB0bRuBdiIu7g7EJqh7LSco4d7CPxvWpef1oA0dP8PS4NIxuem+VU4yY"
    "MUYZIqlQh7E7civtJQLvWXTKqxthMPhq06YN0Zz22r5IK6n0KdFRBFhfjeJGWEB8w/NG7aizhx6IiOmwM6MgczPVDYHZ+ZxT0Ox+"
    "sBsHTw3hkD40xO+ILxZoiSRjSXXCko4NDIRhWYEHTO1LdtA/QTOBTy4Wzp+Q83ad6TI089PCzdnED80hNWvRsUN7AaJnd1kNNAMn"
    "zRu7nJYAJrrjOTLfjyKieyjraz+ZPXL+B0trQfB0VQJs6RX2ozAa2eiP3qamQz4eKW+6rwfyjigtuDrxrI2njHLYohXQ/LfYC5g3"
    "DA1wOFCzIGeLO8YQPTq0BsK/GCekYPrG94PoCOBw3Mf0DhbhmwV+m5hPcQJjjGRpa1K3kQE/9aOmkYwdMTnMI9RsSfIui48lqe+i"
    "hM4OAIGQRF8wiSbAvqSpYs3zYiQQrE8ZfQczK20JJsEvDYGaBhFi547WUx8++p3BrvbJCGEvKtgjwdYovJVy4Zb7duqlVyYmFCKU"
    "OEtyRlSu+4IcXVJfiUaSo0Q2Z66cRxPKnCtRtaDUADjDt1T4Bc0fhXWEsruZjInlYzoHLBz6ZyWHZDBLgH/vJYFX73LwqY2HGlYE"
    "r/JPACI8RLlYHoDTUhxLRq9L96YAnVBwxQHgPu3YywOOBvwJ8VUXR+yPpqiG06mxM1gaRkx0r22UthaBJAJrOl8jMt+R2Y2Nv2vA"
    "kqjFZmCo6FoPQUMJ6ToWakGcrJprgG6e92B36aJpOYhGBA8EDJaXJBjQAxeGIpYCPtEImDn4teJUylE7IxhlsSB1JKXhtbIWWhRM"
    "3lHQxQwHayj2kZi6ecAGAV9oLCxc1XxMgkleRtYkOYGwbE1nY5pENHdgpUEiKngaeCFtPNRjB9q9PF7bDXw2YR/t7u9BadbqG15m"
    "5vCk8oW13HyLXp1ZCDzFKqjRTX2OrVlI4/h8RE+u9Zh+9BKgDL0gUhAmSATXF7RBfwMbAYpXp4mAdAWLigTnkeC0ml99kTYmIyaS"
    "jmA78U6a47iAXcPamlehrWlaHcg8HPzXe0yAejEfIWqXDFSOZkSPw4QE3zIhdtAp/JgNN1xw8+qkmqbOrPhkrVZloqbVNCLysvQz"
    "Jz3f0A6y9odXVCvo7g8WoqxCSKZ2E0jAoP30e5zXAkPdGDovd5stu4iORvrN4v1auldLUNFtNRoHuAQ8QlwUWggAi3UKvc3ALfGT"
    "5QoTbFBgmrXQjvBQYcGr+YKTUuVaYhs70tEny22oy7xY1gJqyxQhA/ChOSNrC5ZosnSoNb5DGFmAMCdqGM9E+Fg4nyYswZTvL06q"
    "mKMaSBN0ls6qJ0ss5vt9UcWcVU5MLELLDXbmRq9bPU6IdZJ/KZN7A39zZm3aWjdxsgFUIH/5sv76FQ8WMJZgKAHSTOcs6ARb+fED"
    "HIoV2gDGeUOiQaYtAe37CQHaUuhVac+0x6DKun9Xdx27szkmpUsH8/yRM2y29Z9G0BN67M+OrP8/YeivD9p1uBpZI0K4nYiwH3qB"
    "i59YR0GtLCc/E60g/poyS5EW+yh/KQRPnx2ORVpdPVy5iI8eEHHQkRLZuAALDQYiAbAIiXX5FO1zZiMefDSx6USWkqS+VyfyM1Nu"
    "vQ39lSef/DsJwmWW45bTzt9zTOuajVzfCq+DbSwCmbGpEAX2v5oGMemuQbR4HscKREviG/SH+lvWX6w+RKu8c6LXvXa4R5seUe8j"
    "tYmhuUefSA9vZOBPi3JAu2YgK5MpnLwvrdOjjI46T6UTegLV1wMp1nnxiK8G9ViK2T0VSXlIhxGu4MDBB/yniv8UTWGEi/8dwghX"
    "3x5GePw/LIzw2C2M8OEfCyNceS2M8NgcRnj8z4QRHlmsFs2mf8pphdjhGbpNS02DkSlDTnzo94nnzhnpAnbQD4EPwcgHmAaNulPE"
    "Ed5lJ4B9b7pW1X3K7z+fz4/n8KMkr/yhQCDgh41j7sPDh59gzRG7KiiC7ll1DfbSBVirwfBjCPz7EH+Mg3+JUgD9jSeygcdoPBhJ"
    "JrScD4HHcDwci8VBQiwZTURAQigUTwRiICEaSSZhlUAimIxEYGuRQCQYAoDHH0OBWCiJfgG4AsFs4EPsMZ4EbX0wysceo8lo0mgx"
    "9hiJBgLhrN5n7DEMGox/0KGKIbBhGxheLaFEBpQFfyOhRFQvCL5joVhYbwl8x+OhkN4V+E4GE0ENFIBwDUzwU4Md/cQD0sprQ9Xa"
    "05Ch9adhS4NHQ6cF8RNtconT4KwkAOon6nfAB6DwFPO+9HW2O8Jsd3J6Gj5iNqtd8KLDHbqPwHqE6b99AP8e9w9axofvKAX+0/1f"
    "fkCxM4C08FnPA1LZHvoN/ICfST8sBe5i5IJzrEyOwinIQqmKJxikGfCyB+RQKfVhJqmqtDPyMcF/WKief9dAekRp/+41CpGlYC6F"
    "E7ViL/9mHdkDMiijxgewqYBj1AfiStJoHu5prAx3Biv0Bko0l6BGHlJvPKBn5A/IHU7qQ8CaS7BlzybDDgYC/8s+THPqnl1AiwlT"
    "dXBcX/GiKUnas3NevZrSbg9YsvkQpModVfTQHaxC81hnaEcEZfeXD2CsgH+jm/g9C0nQWuxBZhc8kJTMU4LzHnHenZkx051OW2ai"
    "2oCNl19eHzQN9Ic5Z5k2SFEPWE1uy3w3mM4ocKo3h8vRVI2db6H2U1xYO9Iz6OK/iuThP8NYIqWnmUEyt2CUf1wcZSRF/7uXMVVF"
    "w3t3LYLvn618eVDW7AJIde+tSsj5zR3bFgKumXIjdg0wy0zgxHvMB5AtReMGLA8aLKl3QUugNFWBfdipcQnWywNUzDqVhumv0aJj"
    "QUd6tJW0IwL5dns0VJfe1JpVPDY2nVpDGxPvHS5BE5h1WcC6jqvTYWLQD27xcz2Ryu/nBHpFG0d4I4gWenInB9LRG9Hw66bntZGT"
    "SXLkiG/A+M/M8V8Y3HvRjcF7Ba63woOO9g9Eh/WTawK14U6nbnwNV0MHUDOLM4kOblXILubeJJRB7+Tb4NR4tLRcwgDPrhVx/q+j"
    "iF8xAxppuM+EHU7wk9jrf/jz53ol1d/eHzHFecBvhH9mheOa72Jtv6Tfn+Gpto7/8xmg46xo4FAd6AJ+8C31fgJQre7PM2mjhbdS"
    "nyu8P8OM9e5f2x+UHeOQdgdnTmKSsnuj1A4KvnpWtfRuGfF9kW73Dqlu9x7BbveKbPcgrBiHtHfiUVi9EY+g4Kt4tPT+HjyC5t+M"
    "R4ey7ni0FH75N3JFgd7qS5JztF5NVw29ij7uZWmv37ZNKeUN+Km98J8y3z/Z+d2nlKqtTuYTbUBgrBaYrr8XUx9/28+zpBFkEfNs"
    "T9KdVcDimt+KT1bOihqzO6FgPpnJfo8Z7BK+tQbfEDKILRSIYscKgrkCmF9TBWFFVxBgyKzpy9cXBkpbUzMZQhd/kJNPrbwdZEA/"
    "BFML3UxfXrxMW7/JyLAKl9W1adplxvwbgyYnRS4jkYpuxousfE1lJEngWBGZBaicvAOpKpf6jmydtTw9FnXwhYG3V9jDFC6D2tIL"
    "BF6YJSsod0qAJuCdhyQK1zu9yNzhyMvQd5s7INqNGC7SOO5mnKyXwL4uyXNPUgTfWTgVQcaBpNQXUgxfXXx1Kt7F1k6oOC5mKWV+"
    "gnmve73knUIvRC06OcFpPPELB88y3ynyR/5ImN+wmqBMlihKfHmhbrV+Q1cQn/5jBrv3rzlhz8nKh4cP+O7jk3Y78NvpyXQbAhcJ"
    "aWKqO/K2XI3AZYFSps9OfoTJRdOLkykUZ2nT3J3p0ggsJlwGpH/UfkM2pEqwiWcNhpTeIfOb+VYFR2lnRK13jwrG6lG9Xh7kPeOp"
    "fQRzAaR7GL2Lk1VcQVtHDCced/hWDl5+YodMR/0beoYkv6Gjzi/q1ydQxegetqYxUxG2rF+8GcgH0FDYVFOqbzo1WkC18CUeGtrH"
    "pym+Epz++PGR0+6SOHJzp19hqVJL5nc81J4jh4Wi7g3VsJrFV3vw2g83LlONaw3Ln223nP/xH1Tj+F5Su5b+sNfTcQzAqeaQD7kd"
    "1T384TVAVrTXNGHylSIV5YruXiX8h8V/+Ct9Ewu//svfxLLXN9/Ezq//s25iyXjsN7FoUv+Rm1jl+spN7PxqKk9A/ptuYmFp4apt"
    "5/atvH0CW9CaA4wFRmpTwE7IQE+zSuqL7msWO0MAf2f44Ql2X5sybfDTr6AZSBCp71a5KaU/LtEmhYE2HQ5bzuKbWWjAAQnoJFD3"
    "DD2Xpr6bS9r8t1qaeiJOqTDoZToLhbDdkSdWVt/DzuWJA983F8dLFMgDyDLVyTWv5o8XrgDkW4b481R3fEr75YXR+tC10AVgWVPt"
    "EDfhWNZ1QJ8FES6ux15wyG3XWPXmwDVWV3Ka/EW7h3eQqJ1SNSu2lCmOBHExiyXKZ6dx4ERDdqTRQLxsGmLjnbLE+5m1ddHdHe3H"
    "gQLXK3atBgMWiM9fvkKGN2dVD9hORC+DXYeiAl+9Kfrrs1Nvmn82K81+DJpcPzsuO8appubm+o1TQPmblhmOuF60JDo6odYCzyPr"
    "MdsSJIUJ8+AM/xg28mLEz3QNzGZAn4D1efSI2vIOOabyEs8ZXp1Z4p1KRD04LEDbIsURrHjsXcZjTTLzmydH9Jp8QaMHIA3IXd08"
    "YL5tFox2iG9DMGL4CR3r46Xu7IH3L6wzk9NK6xL4GEzRi5DTHBwa66ikxfxAaxaif+Hu5A9Ixi6uHx05mZs/yJ9z9Wh2CWjyyKeb"
    "6qX6Jxia6qr7jdOUCYZbNsvSs3lro/zPLa6adznt0Sjxk2c06uzCT+Ol6Cc+s7o70DM5rdO84n1lllfK+Z1xPttf3TzI0U7esP84"
    "w4LRzV2b3Sub/vZCe3eheWvTTTx19QxrqGeccAsfiljo0fDkY3sVQvnyoR1PoLf8+Om+4ZINGd5q+o9FyupwzTAcMr2iwxXMDp20"
    "F3UmF06abTZeEkjmYo2VrZO6MXzKy9NdN2q6ioPTd1tDpwHT8M+3+29ydbf238s/GZFY7ronw2WI+z/029lQ2Uq9ZNaNtzOLq+vj"
    "WkgzDgsAJev0byJL2rafvKe2k4dZoLMtCsv7fp689cFsWOvL4f2E3sGz1dON+YELT94Y2TBj9khEj+ueFxf7ALT+FedXJr+6f8o2"
    "HJlxL6/47/HqfRGuml3h/oqOwztwaiJG9cpi+oaHEC/MGlShsTiVjvwDkP5ZkLcieUGHvG9GV1TqyTH1SoG1f0DqIJA6A6nKXEI8"
    "TBJAwsWa0DUnaFBAC8use9bZ6E3+APoTjzuQ2nNMzd8Zfe76xK49Pdnz/ds3fBTt7iVJyIFcHvRItMkL9Jn6DjWUgFJhXLvvAqfC"
    "qwF4I/D0J6XIEJE2Z/rsgQo1WO0Z7PYr8fkZxpyqLh9xPtjxQt7U9P/7v/5vGD4HtACj8JZFVXjMAfKDLrwKQM4CkrseR1T7QZ5i"
    "PAqAYegc8DsUL7G2drrjFjwctxcJp6AJ2DRs1cP9K8iFvdrG6VEZ3vv0p8ktye4KnyERuLUfj3uZN+ILWd4lwodL0G55CoiFyXm2"
    "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"
    "4RGxd1TTm5XqQTN/0O5vXa55ZdO+LtnzTTu/4s42vaODx41KpVLNDY92zpq/DoZPJ9fD0dXPp5+52pFt/izOCoZxfqze6qCyPVem"
    "N72j7uXatDn/cfazXe2vuQc/r6qn19bgV/lo78DKn3jtojk8Pn40jipgjpY6t26pbzjTm/Fj1ds7OfxZq3pzfdZWT4rG2pbZLdxc"
    "Pw6MQe5w7+TpueSOfn6vHtVq3e3u1CoObnrVoVr5caWPm85193Fj+Gvl+eap9uw89vvd0k/XfrqtVtvm7dNk0h8db4I0OhlO1o4u"
    "3O/dzvh0c5gf5Sfz0d68c7lnDY8rveZKpXx8vvProNMdT6c51xhvtU62iyf718OqOR/uNC3T2DzIFZ4rJ2vjrW71uuQOWjtO8bm0"
    "4une7WTH2Gm3Vw53jXlrVt7bK1yvHO48docn/WrpenNTv1V//uzlAJmV8Y5aqxRxR8/zrOHl4+NhrfRsrT22x81afk2vTfLD5+eL"
    "x+5OUd8d9tr742Nvopeufl1PDPvpegpm7cFT1TjG1xhnI9UxbjdHhyvz2wv18PrJOKvk+8+T3IG6dnKc6x0Vvv88+uWZK3tXP47H"
    "1mj3/Gi2VjGGP59m+zu/bntze69UhLVPHYOaMt2ae547Lz8/e3ql0rYOZ+bTce52r9ar3D5S9MAP3BzYOj3ciEYP3NBL9ofWiVP2"
    "H4e52d/YA+Yyi5Wf+erz1ent+eFVbd7rn1256nHH3F/b7W3Nqt8nrZJdbs6tYalZ6M3XLstbZyf7K7d6f9w+vy3B1Ok1K79+9G5P"
    "B86gdlmunR/MJzf9C0efTEu7N2OjsjOY3BycdafDgrVSOp53r3anR08blTWzWjro/hiVrOHs7HqzdHmtO97o2vru2CeHzUGteHih"
    "Pu2e7/cLF07h/NdKq3NwvXZw2Tw+mF4Xno2aV/JmvwCpH8NxZX+zXdvIfX9yb3NN53lNfZptVAuV4axysvdz/8fp5PSyk6+MCrOj"
    "9oFbu+ivXLfOc7fDjWr54ubw5LT7s12xS1e2e/191N/c3t5tW+2ZZxYNmCbndrttFXZPrw/KxcvzWUe/vFr5nit29KPu5HpTP7jY"
    "23icgzp45ez+2Jqudfvn08fJuXN78nOnB0TIF/e2b4rW1Sh38Wvan01rI+dgVGuejorG4eV0v7JZ/GntrFRbzbPdi5N2rTNuHR8c"
    "GflaYbo/PatUj0+u1tZ+2SfHR9/1683LS5D1P47PS7a+0z36edrfOKmczR6/V3c3Jhu9jVrbq16PCt/XTqpHhwfPJxe19lHz6vzy"
    "8PnyvNbODVfKt/38RvnpvNpv17Z/FX+MvOZFfqV70VTPL1VzbawPnnN7BznTKowuaz/wIsrCcO3m8tfBjjmfzfe7B6dr+/lup3pa"
    "O6nsjvauDw9WwNw4ndfWJmbPHV21c+WZXZ6ejAY/h6389axvGL9mvcP84CD/tHMyfX4aHk+u1668iyu1s3XTaQ6rhRurOs/V1M2n"
    "g+Nm4fvNzilMJOC17Y215/ZsOFJ3z/o3tZ/HvZq7AdIS1pWN6sHayeHganD+3bksemeHpnp8ld+odtqbT51Te3/nGmyG7ePN4w4I"
    "Y+9Mvzw4NebNLbd/M3Fag43nrf3cyJrNDp6+V4eFvZ7+tHF4ZJndvcFg7XHrJGfcFM5nKyu9tcsLUM2/d84Obzab37cf8xfGZd/x"
    "nNHl9eNRoeuancvq9snI/vXTfO6PK6O8uns4O6ju9Ur7nZ/7+9b5FYisyX4FjNxp6fm22rto3tRcuza9PbD007Ofucfb3KR1dLBz"
    "unv5fbJburoZ/zL3N84f23vG4y/9OT97rly4u8e9/p6jXm0Vc+cqiM5eZeCOTlYu+xX16viXumJbG73m83xzenRzuH9zOvl1eLKd"
    "+3U4PRo97u+VW9Pd3m1OvTKLnn2xOTm43Jk/Tg76+6Bwf782nGvTO75qWtfT3PH35/lg/8f5oXfgdI63BmZtCiZXGQTLWutwzdzr"
    "VvSf3y/XzKl3eDrasL3xRmc0O3NQIflVXtsrtY7bo11Qmtdax/3RAUjz3V5tsPM8rxwZm1eXzsmPjeLxdxWIp4+O9KebXmflePdn"
    "334sA2KO66yNrHxufLZVNp9OqoXR9m3OWqs2W73K+Fq1nmqzrbUVq9Nbq5g/fqhD+6q3Nu32z7rHP+fGhnPSNqu75flaeXd/+Nip"
    "Xt5M8oX9qfPzsPBro1wqPLnV4x+17tNBc3TQ3rNzo18/87OccXp4cL1/6a3t7l3e9Dc3S73OuV66Ua/0UuXIHutDc2WrUtTnN48H"
    "+fnGj92ptWZefz+9cNv7A+P0cm10stWbFjfAKi3P1Qu9efPr6gK0lNbP862d6dz6nrtSb8fjw8JFs2d2Dg9yO+aaXZjsGivds+7m"
    "0Cvdtn48bYMpsNXqt8+urm4ue7un853yVD3dqbiXE/Vsd/Ood2tefv+pztu5i4ldqdz2nk52bo1edXq9Mbtul9fGU7CaH68Hg/PN"
    "s+fe6fE0N907Omz/ms72TvTt3bX5xbMzOnja8fYu26Nz4/Fk/tzyBs7j1vPZ5W5vZJzuHjcPr56/N29h6C8MVb/1Ns+sW3x/QO1t"
    "7hzvuJPTw9PhrtkZzN1e8+dN/rCb3yseD3eOWp3N8+u+1X0uPq4ZJ9W1Lf0sp5vtDfN2ctT64W6dtMZXT7ma6ziVg7a3f/KsHk7P"
    "9qzcxfH23si5aXa8FeN72Z7Pa7vbrn3+Pa/WOpfD7+3Hg0fV2jdPHVc/nOh7tcLBycHJ+Zq+8/2pdzlf2TnePpls3DaPuoXa9u2s"
    "dHpiYxD+/uF0Mtzafbw92DKK24+HP5uV7vh296x8Oi9v5Xs/jqsVdyO/s139fnhQvXlWz3dHQw+sUbvywzzrlp/ag529Sa23ffrY"
    "7l6cTbaP1tStYn/zfPq8v5sD5p13J+bzdHfveu156/LX93L5cudHeX5Ral3v5B6ves8X5U6hspHrb/+qtspna7nuSX5S7F+PTp21"
    "p855cbJ2uF87ylm/Dn4c/7oePB9On8sXR1fu8XVrMtgpFPulmTNWDwDKitM8/vlDX7s5MAsrbrv41DK2iiIq4GK+fkc7HqtD48kY"
    "avfKFaa4Tgd+7gY/D+br+iB97qRfHh4sfWTUtdbYtoc7Zn/iGJoyduyxW38Bc8Hy6i8LpefoHc+0Lfztms8G/IUfhjcZp43My9Dw"
    "Ut66oVjrx+2fRsfL6q5r9q30y5dsdg1+G5675iL4NUtd7djO2M7iTsyX+vFcSSrSM0WBx6QC+RCMjeQiAYyfSQUKIRhHyUUCGD+S"
    "ChRDME6SiwQwdpIKlEIw9pOLBDAOkwqUQzDOkosEMJ6TClRCMDaTiwQwLpMKVEMw9uaLjOKsG+u/WXdatOzXF2NB5YAVzfW9dDqz"
    "/tu4n/aygtEyGUXn6U5as76+mNknfTgxFqwNDfJtns9z/lptREoCulqmrmmZbw5wqmOlPcWC8umTdEbZSWvuWLc05aUzBMzqmtvT"
    "lC/BxPlS52AU15sPjfo5MPPqqttbRe7/Uk8bWfzRaJSLmRVtPIO6lEsT5kvdyNKP11ftTzUd/6cBLb7ojqmvDsxu17C+1DXPmRja"
    "Qrk7TGvmqC8jstq2u3NNgYla1zkS+tCDjihTs+sN6ppazmnKwDD7A49/dB2939fbgKjW04cuArYmw6FShekPlGJQGpGePxrzek4J"
    "mp2aVleL9nekw1hqE2eY/vrC4Swy0B0Zc8TU/rsx3Z1n7pViJlPfTAOApRx8qXkQaJnMAqh3d6c9PLgde2zsA5JMxD2tqoVcr9vt"
    "5LT7+4zyC8WbZ3pDA7jqe0zAHeK4bupOIN06JNt8ITe0pycsiVgAfxC0t4QdY78j3RtkR/osnVPYT9NKq7mc4mUBfqORy2RwGrCy"
    "A2Rxag8SBd97Wdbw0joSYnlZfP+WC37/FSA2xEcdy0lMrb/F1NvpO23Y1pQ7I0s9Uhw2SMvLmmdbxurXF56wgCoT69Gypxbybsdb"
    "XydkFkhWRgMjS38Vx8ahGzuGa1hgLcNUFUwcsPCwDXNvOJR4ibGDxVpb0f6sKW2989h37InVFbMFeYpYoQi0YSU5Gg3BEXXRzXaU"
    "faFJy/Y6A6nNodHzxCzGJiX4yFo54Jf3WKuotjulUi1PrHW7fuGlX8wukV4Z2V0DmRxA45+u4enmkLIWmW+/+mmNpWgKCL+X2ywW"
    "h56I1OXl26zZhQSjAX+Xl9O3WZazbmSgfm9ikQRM3cyR3fyy1/N0ph5eX28VRMl4F5+FDw8BvCQB+LBPAYxbwEnx1kGmxiERBIMA"
    "eOH6Srz7gtmfB+kXbz6GpmlheBCUA7SwmKg7sp8MLV6arRWawpUTbWh3iCVdTUb6lCH9smDUFE2nP4BmCCQU2zH7plW/zrIfSjab"
    "BW5VTmCkx4bVNS0QgrtpjdXLujwpozC4qxxuRsERyCyedCf1dU4M9WS6JorCJZXPMqC8Z8xIgsIMs4dPBhudjm51jOElsjIWNq3x"
    "xGNfGi4tRnv9xWDUVnBaENkVr71+4tgj0zWyHBhMHqu9jkLnZfFNd+dWJ+VTyWkjlTIvZi/9dS4qLC+bbfyU2s8oS0Y7awyZJDTW"
    "u3ZnMgJZkMVuPhnbQwO/vnGUDMIHOL0ztF3D9dLaHc2vHtRyVyHvXss0sn3D2/A8x2xPPCOthQtAfoP6s2ACL6VPdRNEcFuxjGmK"
    "dzBtQZfCHPl1rrzMDbf+ZJvdVE6xbPGrq1t9w/HJKJI7A9vs+OUXiqEEw5MLRiM0FJ48EkaWPhp8sW3gyMhsCJT0l4+Awt+Cn8SX"
    "CnzzdteRLdrrcjdRoMAIGrgcnZsjw554MGrlXA5aUqBpaGERGVe9naZBteCvwmi3bYV/Bk2+vgboZBi9vwHGwUh6i3Wj/S2R37Bg"
    "yloHngFKuE3bsmA0jG4DyNTwmeTXxHDmLWMIWbYTY4b1L19fmq1W1nA7+thIe5nFF+APAv8tbTVgmQURb7gg/ycerGBKiiiupFwC"
    "qKR0JXXn6W3QY4wZMpZVh0qRJj9XFZiSsAKSSkNowxDSKIlxTGb+5eXk9KX1oALqeI3kYqy/nMYeI/vfOYGMBYkdt436OM30JTWj"
    "dNrCWCRBBVrTEBoVCmGH6aELZRJKdKcdKLpQum1J2+qFioxgOYcS41CiZ48hbRROo+oLZQCpoeXcnpirI1gKUlCoO8GK/TBmZh/S"
    "HqLVIMfuQcYTz1ClDNBqIGfOc/JSTm+oI7R2uJuTNqTNomkonSG9FWt5vNoZmOOU3unACEKJpkyeqfxxLn9sc0DFCCCAsCWXO8YP"
    "E9UTsiKGepuM+0dM7tkO/NzgJe6Vn/iLhBB8HPEGClID08EcCdsDNoN2fiSgEC5xkkA0tqjBQqvsJLegcVXRBS1xguX224kuh6bu"
    "dH2VnPgQFW/TanmgIdbZAr0JqYZuvaeGe1mqG+jaXNnMgiaq46x6fQUFwFe6r7Nd0x0HRuZNWth7mjGDvj1MyWhhdibMmd0BzBlh"
    "jV322I+M4goblTeG/Xp93U2zlT9rTUZtwzGgf6Rn8UKo1sDki1R9ArXBdhocBGhYypCX+DVI86pQbcITbZEG4hrnG2gcHGco1OWF"
    "DuSaPZ7Y7b9ZVblGEwPKjnnZu46wGCQCMUxBrPBM0lY4RJDQBjDoMFRBJEKVaDm5LsgV23kYGLNQZUydOA8d0C6hvvYnbSVWHvox"
    "HuodI732b39aU4B0Wc++GI8Np6nDmpkhrQrYyO6lRNWuCVQGDEC1ZGOkhdoU2digbyT5lRap0UhDoIKMQu0MwRCJuAxFymFdqSTT"
    "PmHqZpaXAx5haip0+OuLxDjY7j3yNOCR5tMCxmvEx+u7P+DChFKOe1kw6x56pjHsumiR+Nw5tD1gTPi3DiY9ABlwILcy1/R5Itf2"
    "NvscF1hx0o6Pl7BGl7wsn7mgBaAi0AELz/tNbRjCFHiITzjTepi4OLjPMvAWLGdWwKrQBvlylCcO4FIUdqEHLlWRyyrzeENdx4S5"
    "mGncBB1ktrTS5oX3BqJTGTCZrb43ANwvgkSuHWaUmRA7jK+6wl4N2IknoRVPs+q3XIP+rvGMv4BJz1tvcWBDlrO0zi2U6+z0iNuO"
    "wMy0sCA/8mKLP2v1iRBEhuELNqqzJNVZXn4LywbwApv5WVg3lRfP9mBK2mleEJRKInnzY/zatjeIIodVvQAvF6ZxhwoT+410S4vz"
    "OxgoooZnCNnDbWBpeEEfj0goaTJ6D5bz+uqy79hkyf60TSutpVC0T33kOrrj+XR6SzzKw/tWmb8yEaqYxvpxmvVI939+O7AY0hbv"
    "m8K8A/cKKe3pO+Mepxp0OS2p52mTl47pslyHZSptoLSilSk5EmyQgS9oeyrbrHndh/fVGAZVcIa7gq6B24Jsb+QUWEUn2UCs1YMi"
    "1PWgDGjvoLRk6uIbZncXyd3xBw0saDRrWjBp8fe1D9ZV6JM4xIVVYowmTyA5M/eZ+IC6tuMB/srwDdxfX2+xv1kQKKN0BmcGjN8P"
    "GkgwVHZg9EBpZt9pVlKsJ6BuKVoWUM+ICm8V+G09l4la1BOkOxtHt51+YRa+oInugJoHyGWYwQ/JHdvqmc7Iz1FeSEtyhTwPKxAK"
    "2rZxYGDmEqjRyLayfXsTJLEGzLC8fDpPawFkoRTVHQlk1HLsvot/t5uEe7cbwTuKKVV7H0uC8SkMe4jh0JcT6SjTppcEySbqQxud"
    "ja+vb3WIasR7NLGGpvVI6yRfvKOredDDcJ0bw32rq74PIrfI8F5T81IrxGcgfyGP9Up56Tv6yK0nMyDACcxUMJ1BQzayaFEDLbbJ"
    "mgaeTxvZsWOA+uZtGT19MoRZo6BwyHDXCjmAAl8yiESzMzRC7mS3A5+cjwKGFAmL+wzfRKEJ/EXmWHISd80nDYzM4PcEfp+lD+YK"
    "32t8TF8NMv5yG+w7DsMOYfxHpK2ht502JatFfzPhTiN4QBwBQgPcBmLoaGlfXn5M32QC9cDpoQ72/i4JN/PAAKLS3G33mN7NCK2K"
    "pb94et+ti/bYkqOkcJwWina2s7+lAZLdtrzbkVEEUXoSgcbs96Cgge1MPyP7VmAgox7nu70lx3qEmG3b6YJOjFpzve3PzuRtKeGI"
    "f05vpV0BQAV1MHEradBWttIyETwb9LEBLJQgDOp9X18HXVCZgn4hUkjfQN4F0CFKTOVm9gH094wYCeEfpRHX3JGOGw0BMcwOunC/"
    "BFbyl/DoGEQEwOtX3TF8IiQMY3JBxt2e4XpAK1QaNMW2mkMTTFXvLnf/+orGYuBY5jBo2ZbALJSXLpuB9Q1/QfTu1CICoDF+wn21"
    "J9OYbtqzupZL5VL5IvxfsLFWlfbV4Dfut9Q1y7YMZAXHfoTGOxPHgblOAw4kYcmrBACQz2vv7Eh2TIfPfGi9BvSdQ4UcmGrQWraI"
    "LudoIUQisdRYB80Q+lvXjvKpwqAwzGeLKTWfzetqtpTC/8/R/9hXflDNluM5q2pWPcyrqepeGcDeK6tqBrdlHurqgia75BRRhM9E"
    "4ihF6JJxhlJBlew94C8QwRj6AJ913fg9bGbMYBJ0jS6IO6HWsQwoAzQful+YA0q3jOFq2Jp7m1G5f2XHduILKmNCKPGFJBIuXzIb"
    "qpwNQbrNM7JR9BbblYjtntPav/8f/11Lpq3oo3BAia5FHFLJ8iy0fqwyPTkFiIMyDZzL9fTI3OL+F8aOyLq4ydJHOdOSxBEgX0bk"
    "n9NoAiXKpgesI/LCggarV0T1ZmLtJ6zdTKzcS6ww90Vhz1+yNHuClhsbWPxd9y3wqRYVfko+o4TXpbbuiGVpP/19rsR8np6DWoWC"
    "+9l8TVTEajrqSwvAF2gP/aBf6jNejG10c0y5FIwstTJT8j3iQ6PngXov5wBUSlVeJCz8HVdajzu4GotVmWOCvyhOKXHWCv5pywvf"
    "DAk8Di2sqf/3/0oxOipPiYPSiq5PtnUy1D2UXeQ9qD8JhCNj/PB25IQa9dgmLCJDW4c5s49VprAaGvWHgDBhhEzrwjXixTJKTWnK"
    "WoJv5oJN9QDKputFtRg/A91JS1ENLakn+Tec2AkdAuA7CHvPGI61WCdErkZ4T0N4zz/Y0ZfwEY5kkheCuC9T3bEAl+uBL9IEzMwi"
    "KjyYo8fHP6lOiK+p/PEQ9bauPnd9tbXrzB8wYRFmdioekCDoWi4O9dwGAFpC/Y2+TdrRXGI9VTkHoikfDNp2lJtFOS2uSI0iDDyO"
    "cW8HAycMQSxeHrs1EmKjpmyFFdV79NJEADNBzyQTmKpvLnj+aku5bLk1DXmfhqfT5gEqsuPEVZI5I9iKH3Wuw1p4YMy7GM0yhq7c"
    "PaZvM9EoDIH4D470Au2QrTmukBS5QHXYb0mI8cpAgDOuQ7ggvhzTgw65BiyKXd2Zw1o88cACBAMJKEY4cqS5GUhbeVpGWrLz/pJ9"
    "C0u2psmCUyyt90oZo6P8zvik79nOKEEoObC4QBOtSXtkevWZm+4ZKIaZAQjw2NIqSAhAmGJjRUcsgOg6uC2Vdo2AMx7buFpJ5OWG"
    "t1CzRg+ZCFfEG8CqfEOdQEGW8sW2LsYwpYEj/dwvQKhCQCgquG4oI33G7Lm6VgYFeWi6HjUEprQbbYqM5oE9BK28Lroha3WWJhGe"
    "ttuC5nGtAti4iAVQaMGK91b9x/S2GO8tufxYsE7X6Jigl36mV1ANUs2u3yT3gi0J58m73Zb7i+56AoU9f3Pod9gmNKMXX2Q4RRKG"
    "BTgRauEqgfOREPmZ7oiOGIFHwh6zCB2CSKFGGHfh4/6zjdsYar6KAV5VZSO0AIkJyyN+aFYkzk5XJ0dQ13QxTLFb92kU1btBgMem"
    "Ke4dsXp/t5CgOJOQlCh9QkokDEngrBZeMHk5OApWE+asVTexyPser4ialMAGsQUemvrBmkrmwIaEA3m69jmfZerRHLb0Eg73SiGf"
    "CRqhVeiEfEp/gPLUAvNly2Qvh8nOCyTR/o+3OoksCJVwm5T9j22R+zuDJqvhJplDMjr0tDP9j0WEraluCJdaGBe+7CY2nKwshX1G"
    "f2A8rMCnLlnWOR+vUxqWoFQCatLCEHgbfj8qcURC4tpvTQk85YlKtoxH/o/gQa57gUM3GYe/gw3Y5qxMbTVMbV4iWejdBDp+Zv3D"
    "/hf+QP87Q0N3tuJY5sNYUrGHt3H9e2hkjw0r3Hgh3Dgr8Lvnp3B2fUJXtZPGnakC+31hkfghr/JCsxMsNNFI2agLpJhTjtvhkwA5"
    "pdN+P1zbaNdKaofCtQ+DwDaMRdDulTNMCXuy7pVnKbrLW3WnsJxvhpLIYw2pl6FUHt62F0pk4W0X4TQe3nYVStUd0syTna+7oaJh"
    "V9lCOQjlsiC4X7FQNI8FwX2PBcF5PAjuJtxvinS7DqWZnjHCmK3beMwWEjQUs0VlMWYLt3npgBgWAQPszUNiaQw+dPzALQJwl7t/"
    "I1Srg4cmqExGjtdiEVx/LFyLO0uyPELio4CLSHGMbTCj2/9C5kCFup2OZUsBX4kRGqICizAn7YjAvRGgES0uIjWGn++gH7GR0DsE"
    "JQLN7pIC1DDSSQyAHw4WLphl/JIcGibqfhAZtttLMxcA2zsCQcUYgW/gZeAbma6B5YjrhB+NpWeSgqXCPsM3TtEY/CiA7LlGSwbl"
    "q1CH0eskH5aCWe3i0S8ZwxXVd9cTfpgvpgezv3nshrBLxGcwFQeG3k3YaeC8LcSy7m8+8Zx14fpbSL7TZ3+3VZIizHf87u6ryrZB"
    "StXY/iqtLB9v30Z4LLSNG8kLtnMr+Q+2c/1+bZKPP8IbakYucin7kPfaoW2Fi8SNVe+zG6uf2kQNR4jK3rtwkKgRiEMWJxruxhX2"
    "lI9sQ/v3//Y/YbL++3/7v7Voud1wDw+wmryPq7NdItz46CT6uH9hjU7ixofO3FVYd5hY9zvWHSbVved7G4/p6wwXAR/sbnjy7kaE"
    "VRJ3Od7YcohuLDBMbxDTSYDpPTkOztoZZdNKi+2H63aSf4IPlO+e2E/vt7ljAs8MsUhmQ/liWmLqa7K7gEfcSw6LkppH5ebKFibN"
    "PWKjFkGbeVfxMQp6uVCskeJzmhSXDot1ajwMeVGHRrc9B4zGw9WBFvadj2ljZKF8lRQCciamsDAKo4VizNaRV1n1heLN3oiGR589"
    "dnq2nrhlkrIfIdeZ+Q2JsH9INYNUaAVlKyTqocTpAB0wdmJ1N1QSeSwyR5dyC6UTbsPAJoaJ4CazqB5E+0cnzFcd0XHEMk+UbGQR"
    "90bjDk1VX+Xhkav2yGDxbSxInrYKH7UMPze99m9/atzlVmv6au/+pbxYM7M4RGkWHU6R0EY88tmF5cBI55QyLH5/qlarWhAHaGIY"
    "IMOKHTUK4hQo8QEm5Mh06fCcHxCEyyLNVtab2Ap5KsWqfOWxKnkNOMRX9qkiOz3KN+ke03v9aJyNxyv0/Bq658Ecp0aoArcSrESR"
    "Y0XbY3SMyC2SeXFJP17to0rOZ+eq+gdNNNawY3QGBgV5ydtnoTzmv0pYu6MDImAtMgmORrFh+vtNO4aMGO0kRHleBFHzHSzY4gNm"
    "nhMdCbQvQL0xR7QVxxkpi9/IyGyJw7oTPPY5SxK1fL4okfi0ock9wZ60YciEBSAGKwdOEDazxG5HeOCh7JtLvJNmBwwmTkY+mOzD"
    "0GehBZbyUQeh/eTMCtMvVzAF5YXoI6trz6goypbouu3O8LR2IA74jnvcnyrtW4UPXw/QfR09eU0n06ljaToRM8To80z0IDb2mR1G"
    "SO651IplGN33W8ESD7AC+y1JwNhWltzvTpicvt798gVPE8Ey8qV+h6qCMZzj7oQ5QwMetP3OcNI13LQgGWhiUN5wHK5ocyq6A9vx"
    "NLbrbmRxEcMJnFEKEgZDNijM1Sh0gXywPmdkDeLt5biSL7U7uErictyVFhhcCHvxZcQwnB+0/8qtaRYAELKcQ7dXsCkEtdzsROVR"
    "OIHLczZI8HmaVs+OLvIAYHWiavGIIJ8ePkcTRmQSO6BI4akBPrsBRlakCSc9JbLobc2f2cLDC/RgozwZjUg48TakqtPB/FxaKZhI"
    "SSy2iYcTuX7Mw5U+NUB6r5zr6fk2DdA4GCD3CY8nzmSlp0NujgS1yX0ivWfA1SD6jO6T9mdR/QmKoSKyUB6CenRQLnxubqE8JVVl"
    "ZiyqKHMZ6VXoH/p02kmJs7gyg6CQFVsBDnzHPajNEhZKM4oHpE0T0s4T9D+Wsw05bGcZCO90kGhbCQCOpWJ0xhfSHmfSKcaNAFvK"
    "D9ObUe3nbD0SCEgf7Yk7x3OQSTooasYA0hiNvfh5xR+z9Xh4TLhGaE5R2qplr04cOjQ5ix+L/Lg6iC4bWWQnPHKUvMq3QRbKfgIN"
    "D2cJJ0k/ga6Fyv4Zr1z6XZUZS0L159l6PE6Qaw1A+02AnmwhX4a4to8yET2riTr4Rbgsm0pXiUV3w0WZBblQDmaJJ1DdS9OYxrT4"
    "Y9xgJW8lO8Xj+L9MnqfjXyIgeh3ht+/t09DVGEnoYILudshLxwBM4G+PuwFAqIkZTgc4oTF2QEY6yNND7DxnzleEFG7KDVue7eh9"
    "OjO3DwZpmrY/NBDtHZwovOiSulgcWOkJ3UiCEEJVXV41holiNABSXctpGQ4O5So/xMRNCQK5ZCwv20G8I7Mhl5fTIs0NXCVQ26Y6"
    "zAMqSvIS7A4UHIExKsTyQSEjduzxnh/98Y8/jtPxo0PCqdzwPYuZjMhNv/AQAq4eh89Bvg9Ndod+BDFyiBJ7dKSPv4HISxOzpexe"
    "SrTF+M9a/zrA67Bkj/g3C09UunjQEVRhduIx8/oK2pUqDLa7F/9ELmt/N63xwczqw2GT1DpU+UHvpROsdb+LzG22wPNXpwNB6vSd"
    "hyfSQGfS3bTHuwmJioXJorNe0BhTHLNfX7wFb8VS8E4hRNbDSP/7BZ2C6xMLmOLkzpJsDAs24rkZ4A5xHxBuPjP2EOdI73jQe3De"
    "VvIq+87p+7fGR6IPczTjzWR0nCY4aQpNoFxKgqtIU5xCL1HwUfTlA/8AKeT/Zsz+GVyQrzkqQSBKaGot8elHmIqzritLwuu7koLf"
    "3CW2ktaDqUnUauTqaoaK+F46cQJ2aUmYW/y83OsrB/n66ogfpvghqktCapYGGeUPl/BlMYeDI38EYyrciPCTDiG2wtMljE/Wsw/t"
    "qTjbDULY52DOsx6vqK+H5w939YvTncvLui8RlvzDpX4nMVue4lAk2v3lZZijOh4o5AmNJbW+hCD6oKyTIDN7vh9UtN5P66K/jJPd"
    "mDwwmDyI+o9C4gKdjG4mveTyqfn6isIJGO+vLp9sMG9ckhaAC8sSux1AGhSsOpef3KzW+/hDXBYn3MKKC6DTMdne4KVD/I+rG5Sv"
    "53CjbkGHkg15q04c9F5e9k96I/L8pDc/ty0OG6eD+KNdsQtkwdCL46eKv1HkZ3Nj+cjfVFLYCMZKXPItK3Q++CeUo5PE5262TTHp"
    "i5MH/sZi0z8l7x9aHgalgn5T2w8uChEkijxbHCPQOMRCJ05ff/OIPEam4YFZCmWwbN3DQAz4oYjT3B7NmSmSmgPq9DHfWn9rkxR0"
    "GS9553IXFx0/R7GCvdMVyBC7jX4NUA1S2kriHiVBEhVkQAt/0+0FT59w2SdtTFKIl9Zw6km7sV50CwmMBlhsQpuXX1+cBbpfpHS5"
    "j34iOSU0sLRNIyxwcDsRQxfFrmNkjVRe3AHGFrdCpwkX/uyCmevYIHkMN0t6O26yGhyjXQ6ZLtDz3B3Q52nnhwrWozUXmYUmJxI+"
    "IXC9MDzENVwaIeCZIT04iO8YHYMipa5ZK01OZMt+QNOlIX7Ur+kAwzaWoQUnRIWGxmyVqAbRCJOlwYJm8WzaAzPtuPWg4XVtOr8p"
    "zQ6wk5qMQj7okdswfc0PVmx4a6pRYDvfrsHuNQtcqI7RA6IMtISb2ohkPJ9f1SZKZxbffP1WtKIQ5P1+Oii1vIww3UmnY7huDCaF"
    "CEkgJZ3Z7x7TgZeXE8AywkpA9S5jlA3PZxUcU7kFWko6jAjSxXaG50EH0aUfyJwhnppOJAmerhZX10Ee/JVAQd6DYDP5XrPJ2+Ck"
    "m/Bi4DBhwS4d6Bph53fy5X446R78ow4K3tDnz7k0rlOBZ5idnJ3hZndvJg7VaNwtxY4l+hsYo5m/aTEIXNeW/hR3YyHU/izuSKbw"
    "gCceLaS8+C7IpSXmrQvP6ehhFRFktJXWA92XzZrXVznJn0ENcSEEcX4BmJ9HJv7TtjZk5kYDlk3cOo/5CjJCHRPJ/v6BayRsIAgh"
    "cP/3oIbMGYrZBsrv9jO40c6i0hj7yRsdfj2+ycEcFF3D7ThmO/DzkYMu1C1qy+/T0HgvBvyzuzTvd44h//s7B+m/u3MI671A0z/Q"
    "ObEFFY1hmbx5WNb3SYZw48bRqmf3+3ju2Gcrf/9sImJfJiL2JerexlCMeSjgXJhcDOqP8JmselIZkAgrGm3uTIJAjP+TAjH+pwjE"
    "eOP0rLRP9sCFTV8cRaMx48d+j3uoSYHgd2089AaFfFwiQxsSTk8zFvlO51CkgyZiAy35nInrnxgWdpuhCCFNTlvJNfwrfNokTB5e"
    "PJN0Xitc5pB4KRPlPe4i9lnunVMooVPHxH8nT+FOmx90WsTtmn6n2fESV1xYADUpQXREzACR/MQgcSf1e51mXhF0Akoe+ih780LA"
    "s0y2A8cKB8EitDMzf2cJov3MFx3slaVQgJrRkDc3+/7deFYX7WXPX2TA2MgCjIW46IoPRhmDmBjPv1+Xut+ITC3Z8+Rv2DAiUi/5"
    "z0g325/sZjwaT5woeQldMv1+twyGenijdsb2BK3QLlOcMznfRLnyPhRF1JoFgRJNPk+jLGt9wLKFSIxfwLKjP8ayqFOtUsQ6hie9"
    "M7WB1MKsdt+f4EFIZ5i9/fS35ndAxd87050PyCaO0Tkxsg3++WRjvoYPiCZiaMMk46l/F8Gkaximb3Cd/gH5xLEzPUa+h3+0oCRP"
    "SeLiwE4Cf0yKj7nF/qC74riXHevu0x/rLk8WehOeT/dVqPdWStvxktdJCmb4A5T4lPoZwqgTWB/o3IvKddzNimCNOmZEGfWzTIer"
    "o0zFjQIH/el/kBb1/2jxDgP5HFnlEwfkBJAYMEKkTh8SrRIuilHkY0TXmaR7CiPBZud8Ig3nQNAvdCJ31ex+CXa5lbZpAWGJnDQ6"
    "gif8uFf/uBq0s5R7gxdDZ6wkODz2mXdjO7Ba/YEJXQjwxq0sWzP5APhxHAq/cTrQMamnLEw52KnnqmKH3TIUKDg8l2kwQ+E6p5hE"
    "DEt8yyTxt/dta5+uZ3f9g4lil8DIerrTN7zQyeViTnmcRQKSP3EIMCk8Lug/CPimUN0C1qtF8NG0xMN/8WjjjTdpTPMCLQ81L2K+"
    "5YDgSRAQLJgUVqATFntzrrdjJ90mMxEelgl7O6RtcTQkVqeOnny/ApkZQyF+WD6wFMYO2UPT88U4hld8qYc8F9ygXyh3duzapcQA"
    "JQoTjkx5T6ejU0n2m2wHUTHhEyPKBA42Cjm0/Uu3yGhTZA+IfLXTO0fgHMMDVsm858ZICkFSkogSvi/jKGAIRm/hEGWRqxHnDzln"
    "Q/V/zPzL4UIxUgTMsi+cYSjuNiGaSirZ9gOqfArJxECPGB5/aQmXYkCQzhtnAkMdYE7NMP4n7+EfuD0TOrHDKCePd8gS3p8FZ8D/"
    "6JD+MZfN76dTjFLkHg9T6vA9SlGF90Y6tKq19VF7ojVi9Vl6yM3AM95njIhv8INZEuNq7tIM9fbsfb4+wiqf5GxW9oMuhCR+yNXW"
    "jpyzmr1/4wP2T75rTgQyk8grLzCWOeFai0A6s+Mj8K8Ssnf5NTgvsMgO9TEes+xK+6dUAS9B+tSJMoCWfKRsKQ4zOGkMxpMhGpLM"
    "8k2chvF6DTqTFDjEpGNYb4RNJxjfe9KJgNAhwMhBr2gI9YXsN7hCIFNxWCeT1M7uLBJCvS1XiG4gjsyuVo/n/7ZeyjW0Ad4MkZib"
    "z/GqGt35Fo2cTmgRnw4LhU2XSVTg+aTnWcizEPaN8DtXvKnN1kPgmcnIwjDoPGOReHw9aLL9jH+gKXpAK7p7LXHuD4ljFxi4/mha"
    "XV9z9q8BEgejcuJUFNtaSToNJRSY27Z/kQ4dLxbI0Rljuv2sizda6p1HfOLki0AhuMSGDjD7ITl+SWyDRZ/7566EkpXA//fhGPB6"
    "/LKrivI7iB9Wcahs4nhYcRnxn4TSxL4/Zygn34nQrhRzxVKJvbz2a7Z+lQXdzLC6aXYPpjZ27D4sNi6d6mITSfuXFPyXHa9KeakX"
    "SsT/kJGH+ryeag/tzuM3P31suya5HlOOMdTxCZ4gz4Y1vweTtZ5iQatBDr93NdX10v8qtZdl6f+aCUpK/sdY6SAvVINujF11QA+c"
    "uAmVKDvLskW9xb8k9J5ZihINRmAzmdDT3OfQY1MhjmRyYyRWpcbIGowDpWLs3Q650z3b8uhhzbdqYAF6cDNWa/rGWEj1pqFhSca/"
    "i+96jMBo94yP6ChGX83l/hwgw8R4Sk4KmEtvuyAHPIm5fIbESKOE5N7QmAXJ+tDsW+xOhnoK1wbDCTJ/TlzP7M1p/wzvS48VeJuR"
    "PUe3BI7UgZTqpgzdNfDaMtBv/yDFoszg98rEe9GN1aBzyaDxDa73h6Nebxs92zFCHMe7/6//+rkhkJnftAao4AeZpuUa3ipJCzy9"
    "63ihecNyeW/eymaVDQSfk/lkOFztDPD693oCHCWcBrUlLrDMEYuHS71Dr1UslspnYSQ7k7bZWW0bz6bhpHPZcklJ5bJVlf5UCvSn"
    "UCtloMkevYHw946J3oMS/zUkyUOySmfQEgdG5SNTxH+L8K8aHZNQWzD1aDapWbXkhsbsb7Ds9hxYI92POSQYptyfpY+3aLlaKEmi"
    "LVaKaBqWiAv/V/lTLYRrJ7ewWktuAev+E5tg//4NFpv2o+mt/heV/0lU/r1MzOfU7yVy/hMI/r1UrnxMgurfR+Q/1MIf5uT/IvXv"
    "JzX3uRhu/cWxba8uIiYx4htf4/TW8clYaMXqGDyO8U4LmzBjUOtGY9ARWWDhmyrYlzqGiPufypd3xhPLhhIW9wu+TaMlrOvCu6kl"
    "KHkaGnHfZ+vcMDvh+fTIOrPZoO8sbxPUysT83lgcfWY4MLcVe21JEd5/9qAxXXvL8tmZAT9fk7qDt38M7OmlBI2fGPOLL+XwfDVZ"
    "jr9m2PyTCZD98RFHrl++jjsSznVvYLrK17GOr2rs84GjxAUGkTOFBZ9hdfFxYRw40G669RdBthY1GG+F2Q4IR3ofXSjNGmrLFKQu"
    "D1kcSorqiztYQ4XxsdbPV41UBJP8JKGK20m/yEAJhMyBYXQpO8x0GSTajX9wlHpu0c0N5AYYa/fK9Uxc44dft6GvU/kriG3+OqNj"
    "KZbiKKai++jKfpvL9It4xF7yIzA3jpHtzNIazlZ/14sQA5y/4DFIOQ2QRW+IHMPIyuozKAvCRWxpjb/U9SwRcqEY2bE3MkUTGeVO"
    "l6kW9oIDovKpaoYbm5PCgahnQ8z1VoN+tQy6jvgjfuxGOP9zPUenC8XM+QQqw1BwQkKjvAA0epQ2sl/pagwYXjYJQZ4tlBhj0Qaf"
    "EcwDcu7iiy9qGRggfCVkGRgE9xPCjJWIuJpIw4+pRV4uaOg01vTNLLP4ji+PQtvO+tfZN5ToRuut65f6ydcv9ePXL/HxxGuVWvyW"
    "pT7dNmC14oe+nSANSvHj02Yr6Uy0noAbu1XSjpcHhP2blELN8reJO4lNDEUTC2XSit10wTv2/p1JuMd8bOHRD0GIrG01WLq4bMI/"
    "6WeIGll8b81tZO/Yr3sWQE9XX+MbIe1MXb5+SYJtdock9AYmvi4r3Unpvx3M2xG3Ds378qUjAJpuGTEy9aWldv9OSsErUc3wU8SN"
    "u/t6HHJCPR2jCwC83jdwF+A3tZpj11pyYtE9K72hbQOAtXLOP3jk4XWRft8G+CgArCvKqC5O2P0ZCmfHereFmk06r9DBbnqn0a+F"
    "lUZ1eqHExSbFmRuDjtoEgrYj3emJ2AN1oSMe7wRQUqYUT0aKWHT9DLtOxBhr0Ne7ex9/LNY3lpd5eTwgvrOxf7i9peFxzPHEHaR5"
    "Gbz6EZZHYAYphxKWl5fMEB0olYIreAmFnVATAJAAvWh5V/MbwOu4EKWh0fOE1EzzNnfTZiOoqbfZ4z4BKPYkTrdup1l9OnEo8R8a"
    "+e4AUfa7IaPepaPN7O4kN72F9ybBqpPOrDBofykbRXZUmRMMybqz/2O/tYePvmY9235MhIsZPl74wU5CJgIBAZcIg6HOzyRxDKn0"
    "X5BRovDEKPqDlADR9ezxmAP0B2tBZ0mR0YbrdDrcnykSng18S5dmBSy+6ZzCfppWGu+SZFXGHQ+PyuOlC+wNZKlZpCs7bP0t9BCi"
    "EzrJ5p/7FcfRYtu3Rss/SuTBzyBWJSA837MWoSjOGxDjTw+GHsMR1TAuYZ7WMw0WQlPH2+Pu6ZajWAmxKW498qCZYKMfkkhYZvAs"
    "UShULL415cR3r4PNMCZ9lWBBAsJr0sOPViu0+eu0aOsXRyd0KyaMh8tkfbC7H48CF7R4TLf7mZAEzXaGLqPCJCSjw/c9mXyEpAu6"
    "dDxrG79f6znt3+YVpyIpKOxlFolw/C3Az5zHSsA/JCHfeipJR+oNAWN2jZdK92lRcMMsI44QYDaPVuYBiGCYkBX1YasREyJsYXHt"
    "80W8QFgdg4mSFEXmMz7p2MwUlEdcC19txw1OinWMRbCyGA8bu42LT+ztr+AuzQS+NZOvkAt4VzPxtjiZf8Wtl/1V1BI0OezBbSmx"
    "qU2FIvzaSShn2SectRMvifP+mouIgWErxFvBhWSfue2qmi90O5Uev46sJSz17bmxTy8YCiu8OV5I98y0gmvHUn38eH0dsD8j9mfc"
    "SsvvzbbwzocBUusczG2Kxkpr/P2OFN7jOBqDomCn3DEGdeGmF+5mORg1kxIekOy/7Fsp2t7Ekm3I4CUUKq87jj5P2e2fIGzd1Gji"
    "eim86S6lp+5a81Ebn1DD8p7t3KczKVBIB3YX38X1kUTMYexfTLpFB/7lj33jc+gu6UeauKPhgRUlld5af1nAEsk0qGxHH+Kc4rds"
    "VnEC+9dK4Nw5JvxI7QTyAtgJPtQN+oK1Hkrh4011jvSx9vpKP1uGpzU2sKfZnmPjXT51St9w+hO8xsKFgmv/lm7UL8zX/Yzlwa/q"
    "q1p+LeQz8LM51EewfmYYhK9r7LpQK9Pg/eGHXxYBTWhQJVowSv5Vm2APYnRlys/rq3Gn/e1vIlXjyYJ2IeyDlvqiJZZvuvQXpZdE"
    "c6k8R/kl7a3zVr3fxDKJF8Kg1sm/6NoMNlQ50DsZYBg966/eN2tlJePcWffrBvwjRsoJmnlqvecuoFdYL0WMjqYWpTdX4XfoeVa1"
    "mMI0+R3W2Who4YWMnjeur61Np9PstJC1nf5aPpfLrSFwZnCa+Hg5zDm+aNwFj6Z+QXCrzmSIcbf4bpeNb2N/6QzNcSwVH1jNZXOl"
    "QqlYq6Uq2XwprxaauWw+Vy2VK5BQqqnlfCqfLeaKagFfYC2mKvSnqaqQWaqxNLWQrdSgN6ICfNeK5ZIPkb6rCDBfrKiUXcqV6bOQ"
    "K7LvPH3mciqVrhawtFou1MopApwDqVTjP3NUqpgqZ2tqhTeHFcrZaqGcKwl45WylLOBhc/BdKtcqKYENfudrAbbwXaxUq03RmzJ0"
    "uwrYiZ5my9gwEoD9avp04Tk+4agmoBvQVsDGFDVfUmt+65BSrBVz+YKPH6ZUfezhC8igSt3L+R3P+dTI+SQKygv6MXiCukF7gvwB"
    "Tnx8Yixxe1RBMuSbhWy5TBQBqmUrBRzCWh67DillaWworwwYYR6rlM9WOfn4r6aayxagmMjA933LRb8WfLIGOMg8b4G3x+oSJgy3"
    "26NStgT/qaka9Fut5psl5IpcFb6LxQqkw6hUS5UyfANY/LdZyZar1RrWKNUq1Vqqmi0Ua/BVyBfyVfgCegMf8L/NIJ2VYnVkGDUk"
    "WVP8Ctpj7Qf4EH4pjm8T4FfKKn6r+UoN2ytWcsCvRWDDIg5jrVYEtihigzUVkIahqlbhu5hTVWTzWq2iqvANaJWRjYq1fAWrF2EI"
    "S0SGahHzS6VcvoLNwmAXCHylhq2W1VJe/G36yaKUqCWgEFTRSjNoVWDBsAqwJKxFL5q8U6KPQZ8FDUJjeHtUzubhP0ivFkq1YhOa"
    "LQHXwne5mschreQLSFkc0RKNaKGSg7kMv3N5bLWSL5WweIV6AVhUceIAk6n5QgVInwek8DtfKRbLOLQ0qOVsOV8r0FCksBQyHvSW"
    "sYjKhr0Eg4o11HIxh6KuAv/VoGxOzQHC8Bf4GOkAvS9hh9VqpYj8DFOrUoJvbKDQRLg1IkChVivUiI7VIrWcR3piD8tVrF+oFHI1"
    "IgB0CNGo5VBK5HOlapHAlyo0e8B+LVFHASwMflUt5gm9WlElulRzNBwl6C8OczlfpnleKag4ZUqVfLVKs04tMTIyyZlno4XExe9i"
    "uZhn0POlAmFRLeIo1WpqjTFLrYISSx68W7HUhR4ZD8wa0DbVcmbRbQkP6VOL1Km5rIK2QNEevKOHtmU9dMo0zyb702J/ZiE9dPb/"
    "Bz209Xk99Pw/mR56/pYe2vwP00OnH+mh52E99Pw/Rg/d/t9GD23/I/RQ0sJI6wJNqZZnOmNBaGlMqQPRR99chyvXuJbENMxqnlSk"
    "GvYmSyoFCFPQX/xPkGqqCiui9A3LQYrXBXWpWiz5kEEklgvVMkKGFook0HOoBhayKgrmarZcAx0J9ZRyGSQvaAeFklpCRaWsgqSF"
    "VT9XITWmhJmgYBaqpC2XoC1QEXKlUhkLFyplLFwqovhGLadaRpWhBECpPCBM+eVKroLlQbEs8nwVFZ9apYDKTAmXYfyugpqJ7VVK"
    "RRW19Eq1QN9qqUr5AIYhm6vhZ7lULcBnvpBD3FGTrSF6ah4Gg1Tfag3zQaes0TfQAjWgWq4Eixd+q3mkTaVGdEd4RVwkYcmCetgc"
    "LLPwXcLFCHuDizOQEhbdMlGjSIpqqazWakzlU5kugZoLUqNEugYupRVS+kBzJY2Rqf/QefEJK2O5AK3RZ16lpbFSVUm/BC0Ylzpg"
    "BvibB+UZdEdYvCqVchnzawVUg3EpLJWrWL5WpsUOVIYygwfoQvlCpVbCfGilgIscruCo2Jag81X8BmKU0FoCJRoXx3y+lkN1twAc"
    "ikoKLJWIrVpEfgFwsNJicaBtFdU0jGBHTbpaLdeoeYBXRT27hqoMoAfGAX0Dq5Shu2qOWCZbhpFHXgdFrcrMFLUQUIe+qyoz2IAc"
    "/JtstmqZWzmwpkfm3+0RED9XKJB1QwhCP0pV5Dn4LsIEgH6jJgGfFbWCZC3n84Qe/Fc8xLFTcdqqQLYijX2hgN1RQSsu01gDxzAW"
    "LNQK8ncF1OSm9F0DnSTl10ceqpERyuDnUcdQGW9VWLFiiVUrlhnYCmP8Wsn/Js4tlCtyfhE1GKl+ocKaQ/CHwHpAXZoBQAW0BYpl"
    "PvtzxTyqgXlgZaoPw8iV8jzvZpWZigXxxQxFVJTIYC6UmMWVL5C9g5YYMxRztQKZPHmQR0VmKOaqFTKri3my9Iqgk5aoEsAtM1sR"
    "wJAwK5cA/wLadpWysUo6IShp0GgkLQd0bsppKDXzNTUVQAOxCtqo1CCKXZhl0CCYmsCmwJ1g3haQGwBXmKJF1E9LyBUlFY3oQhZM"
    "KLV2iOwB/SJuAZEHliJwtUqTSFWha8hcMD9w0pTVQpkxWx6ZDfRcMB+IGWs0a0o5ZpRXUHKAQMoTr4JuXqnRpMkj18FcrpWRK8Fc"
    "KGEz0IMaTRq1Vk5FWBzMXBDPBTL5QJYXK4eoLjO1GqZcrnYJfwEvVJOrZDVAawWc+SWYg6Q1l0uk/pZBAKGBDSxbKUBxkOXlKo12"
    "pYiSCNRmXH6qsESgoIKFpYw6PYiJUhVndg29CMBTaq5IBl0hV0KTAlkTywNSBbIBgB/QJAB7npAGwUNw8yid8RuWJFzJQp26PUJj"
    "vZCvcDlbJHO9RCaaqgIesOCBek9zADixFPAy+26iDV5mRjc6FqrYjSoK5xrKK7CrYSbQdxEsvUNstUxLXh7WwyrUrpZRmMOSpRaL"
    "hC3IhxqrV0M5BsxeRDglYJU8UkNF0wzLYy/RREGOAHjFalVldmtBJSu9VCP7lWYyGlCFHBqwRZRa0Gw1X0EruggTD78LOW6/lvLE"
    "4pU8IELF86RJAPuR1Q3iN0eWEDp7Dgs4/2FFLuIUruG8BjkDuTCNiF0rVQCHa02xViilIpT+pAU09y2gbWYBbbXiB5p0153aTjd+"
    "molnfOowxXsHmqSgfgFS+r2KR0QAqHxayLRW+ZmWID4zDgUjP0Ix/6GzUbxQlgp95nhUuMLnT0hF6n1wSCqEe+y0yvvne37v4Zl/"
    "BsZTQ3+UEH6TimDkkWWSxQrvH+UKNzAyAI/R72qCVfk9jbBd4N/VCKvyuUZ6w4mZOG8STx+Fa8kpdOeJBOczk4Lq1OurI3fVAbtI"
    "HyrvFaFD50mYBmfDEtqIT9mx3qVLOcPE4+WyPPdT00/USZ6A8tm+aI3Y0T7G2UCv8Szl2uiGSW6JTYCE6rNVd6B38fRaYkWW+Vn5"
    "EGnuw/nGTzC9z0Z0FhG+8IYiFglST7Fzv0F+Xx9HUOGgs5DzDgLswsnVke4+rppQRcIkHoSO8Hu2M8r2TGPYFSOenX00eAg4Tvr3"
    "Dmp5NnSnJMtHdrp0lTI6+rCTXlVTf2G/sC1qgh3gTK2l8plMTLJGSiWfto0VSBoznE5RYv3xzqyCseAYI4mCE8dFEo5tM3zO8u8e"
    "EKlofEjiPa3jOfX3mCXzriDj2IQQpvFKv402DGk+k1qJjsU/CsXEoYuT9Z+OZYDH/4YklJD7BHn/GfgXEP/Eqf2XYGpDT/7o+Reh"
    "oUqHX+A3IY/XVY0pmvNLOAXfoqK79bzsV/ZTiZWwOxMXC9APViC88LPa+AuPxIw7dAHZOV0MFaWipiCRce8ilBeT17LaIxI1ZWL9"
    "7tqsCq9PPBCrHnCGpvCVLpQvVIbQoSJxSFeLL3vQR9TUQlmUwjPocsLPjKr2htKNDzTQdyNeQlvheb76h+8n4xN9mBgbFFYJL/HC"
    "AHjiZzoRkcR7/NiNvyZgYLk9drPIJlb33KZrNYxhT2toworS/D0LDLU69jex6FSTb72JTazOgzjSBH9GY3aLY/LBJX6wibTnM6Nv"
    "zHixO14O0rZn4/vgoNO/pdPpxnr2L3f66vN9hv3cWL29z2Re4xm51ZqUQcXkDPp4KSuLDMb5k3L9SRwSMZBAE+AqA4zWxycp8GEx"
    "huSHxXqG0UXl9e3jX4oY7Ehf2caZ1Fe6OWqhsKl5BFPwLZjqQsFTBDQrE1HjHBQIjndLYdDmx6UkQfIhtCaKh3ew9y+9eruIfNHt"
    "O+R3jF8T0IXfg0RCdL/7HhQq0qRYzPfHSCrOjtix4qxYUqkTNjmpFLlrwmXo7vn3caMin8eNin+IG5X6ADcuw9/Hjhf6PH68wocY"
    "8nIf4Ihhu4f+Maf3EPVLvlto4tm0ZL/BTlRKHOfcan1wnFOoVe+d5QwiEB5pu/jL39qI5NrAGIIi4aZWU2yf+ovYyX1srYd2rmEB"
    "ESDwzIOc5W9j4yJDKVojvjilRFDAImHlShkRmOHmQhv8sJaxMpC+JH7jeufZCKIhcKj7DSqP4R3wDb41HbxDvP6zhc+LmYBIg7FJ"
    "FsYCVlzkC8Px5lSBh6BbimFNRiyCAgQv6hs9sz/xv6eO6fHfi0zduPPu16FK0PzPVqBYHCEqfpBEQHzARqKmV/dWQFXwIRwFARfU"
    "taV1jYVvaK+vS/67bAaPsvDDDTyM0x6ZuPrf4ztuFpCP3x5P6DjrFg/DwBANBtyRgAvAzrdYRMrf/iYBZzEk4mG21NhPZwc4NPG0"
    "I0Yg+BEiDTZT+DHpDA4Y4vTDV0ziSslxK3ZE2YCW3Pqdxi4/wZcLcZrB3/ZwgheJmyxyRruHmtinOs6gHdSP6y+R2Yfh5gkzjguM"
    "S9M1aYxVrlKyBwCtnk2KHH1xrRzLsFWNfi+EatAcGJ1Hpomw8kwViCU7Btoih6YLvRYNuR3HHg73dKs7FElCP6aPEd4rCM1J+PMD"
    "ywzBdfpiuhx+K+zAdBQvesCN/UxLJUilyrA6MaRjdSQ1LLNQ2DVHFxZhGMNvYrVNq3sW6nFatCT3eXl5PR1Pxbu6obV5mp1z5RU5"
    "ZbAK3tWFSkNazuCFSREf2HjA37aOWdY2OkRCAgsg4AuEGq8L3Mga+YpsbjxNSFaBPMg+71tdYxa00erAvApUdE24bTQFvTJaDl9x"
    "Ikh0NxZvX/QdqdKinkap8ja9vuowK1rG0GCBUvTOKk4Usw2tpuNFFHyKVPG7fmjoT8YbA5SMynuDx8mwzldd0cgGXrAUaYkRmQ0T"
    "SAFFpkcMn7iFM+2EBpfTwjF6yP2gKmW/GsNMPVQmSystHq+7QtfdepODiNZa0cYzTZl9pgHAG2PEWsLSi9uUuW/yXQWxacRCzPCl"
    "xPVCPXl2SkXydRG0RRFceOpm4d83LrdNkHCFMuhMfDp887hiCN5BQZr2xahBjLFDKksMGhdzeOk7++amCmJCXTM8IbuPDHrOlG5W"
    "eODPtMq05FJ1HY86yXhwKc7Q2ARR/g4WajIW0RbUcAtsfWANHBjzi3GoBYzjk4EGfoEQ9SwmVjs4RKLLggNgRVdwgaXVgk4Nk8fg"
    "mwBN6euOEhbTpoLyhF1jse129LGh8f6G+wOybUnlDLVIyH99XWc3hETGQp5PgMlSaGgkvGhReXcF+WYMXYPIYrxLhfDYAwUZQTCK"
    "kxFEatWLNGkp73Qtsb2EeUddsejPN3dqeh2OlDxdMXrypaO7Rkqt856izU8rpbX+EvhvMFVTeBRjoZAtFP6sLb61HUj+RvXzoj6b"
    "vXEILN2HUS5ny+UIjIKAwYREHIY4fiqiKXO5AILQauJLPqMB18X45dGe0GYWTHyQthSfbHzSCG2K5k18XZCZK2CMb/FlG4YQlYbm"
    "Q6LYla/UMJL4fpGkICQumeheeB/PJE0jAXjyMsiIEF4A3yNCWLN7fU0npK6/2/ulm04ag3aNBPm2AH6wuvYUX9fdfgKj0EdUY01o"
    "SkJ7GZ9Ib/cjoRoqV7w5xxgBMr+jRaF+8S6cGb04xwn9wUC+RKfVObmvEvQTpmivL4U+F3TvNz5+QZd/v7ciknx4WciqULyS/ZRl"
    "U4DjtdrBIpryIt4Hpu7XQTek9aHOZ80Q7wiS7lEiHkcz6q0rjAT+DY0cwVJgDfNCkrHxRl3fS/n6mqyh4mvUoPZgOWGTvAdPcmh+"
    "AJGVFL7N92BK3s8PYLKSCyUQYG/BlDzUH8AUxDyhGgvFdJtiG0LYd2/hLbyPXDrwHRqYkGyB445Hn6cvLPPXxNjvvgXvq9ld0R6E"
    "TbGgPQzdhMmx9c5tVbSvw1mL7fFk+GbCO7U2WumXhRIssg1/NyIxMRPMyw+BamPb8fQhbnTIqvlb6RkxF2jfBqyuYHNq9KCcUJ26"
    "+6TIx2rq85bCT3rXuy3lHIbVpQ93IDu5Tj7n5Dr5z+TkOgk7uXa4j4j5gLhT69GY4+vrqHTyFBBOx1NLuLlYO65wB71XBsF4sPKA"
    "ziqu/vG77PldToSwRS8kjT287AdQzAbuNLwaxaJrVJBLhvO0pTjCW5Sygs7t0/iK0ylg73zz/qqLkzzcEPrmrayI7vt56Ixjzx68"
    "LOpy6jfvz/kG0IwhnLYyeAkBGBXOtg4KotyzQ+49hEp409AHPXQT/Ykm3rWkfFQVsMjUZZySEXrbYfkR9UGfhknoE1jyUR7GXaRn"
    "/4Eu0jPJRfqc6CI9+cBF+hy4SE/+mS7Sk//1LtLNlnyL4CV+mV350sG9VuLFgheRE1oIy14/pfOFXBDjrXyU4gtafPGVUph8lgYk"
    "fEVdwuWDbDsDVnLpPsLgurrwipdwreBZ2qaLDkE7FM+2mficA993Y4+26VlfpeKXntwxHKTQB3zzIxtsxd37iAX7bWInht24aQiD"
    "VeG3vXzFQJIf8DvhBjwjG94sCt8hI+XGXqsxIzp87BXpaIGGr/XT9hUuIfJ31uy+vvpJ+/QRbMhh6eCLl+X7hK+vejaquLBZwHEa"
    "6O7YHk/G2CHhEwltpQKo4CvYPTWy4qfClBeojn+DnVrD152UJ2wKlegs/6Vwe5OGin4p9MSCQcE60q4aUFn89p1g0CP2y3dkYcoO"
    "L0M+JUzAH8wFNBlTAjmDJFuYwaHfC8FHRELlhXMzUmfVoKgVpE+wz66MsTN0HWOYHScWsSA9TsJ/LoKbGmE2Z5G5s8TQ3FcpMygd"
    "ec1GOFH6zoYYLRviqmxoPOVR84eKDZE/LmI0xBgQ8QOCCzIL4nKaZjlNA+plY9QC0vj917LueIgGVhYnv0zF5WUzMIukWzjFjyxm"
    "IbiGJn6B3YSBDCyOyL/4k4FsgjSnwAoc2MCwDEsPEZJAokN83PuXawbZmYT7P/mrNIaZDuo2NFOLHBjPBGLz3Vb9F6zCCCciI1jo"
    "TiPA+Jgqq0xP2Sykl/3CFF76gMQskxE5+A09QrsoRGb195A5iP3QMgF15dSP6BuU9Sn8BnFlqIpc8UMCh/H5PIlhbYrZlzJ1Ndry"
    "CFEvH7rk1Y+Ro2fX0ZkhEzVwb/iYShWSCHeWdmNkkaqECfER+PfoECJD8HBa2r/odZW947KqdzqGS4TREl/o9Jtm5TewOJXOSNI3"
    "CuoLaZnKVtr0PckZRa3g1XId5cWPmjJ8wzT0RmcS2bZJE+EnnVZ1qzOwQU6u+luCtsX2DZFu8kYiZLC9LimDEiBD2gmTcoNUv+vB"
    "KR0k+7uYxhSG5BuQUaXyF/wzo8f0qrjekKgYhGewIAFOqSCiSPGhhTSuOz+ZKV28Cn0EzMfP7sf9DhKZqCTewBlO4UakrviWXmYh"
    "65yyY0NhN2h3TX1o99/iPrA72f+9LBRZfcooYdUrIwbLp0f0ymh8sNDAhxlDAkBEqSbeI32YrF2LSplgXoqUjPJWJRb0GlTh3x9U"
    "EG9387sS2XaDyV1G/G+Wb0JoIUoHXqlwk4fiPm0hPvZadBl18OxpEh5MbQpDYmkJ05zAgQQKUboHVgV2mC6+vgxdR7jAZ28LCybL"
    "+EwmaUbTkH4Fs5IJN1aBHuPmIgTTEcJmK7P44Z+XvGDnJa+i91Z7nRR7IXWh7CZeQ32AFhy7afVe+RUU8Tqr9PLlQvkeSnSnHTCK"
    "F8qNXO86VMSz8dbr21Aav237NHQ/NhjyKcgbdzAO+Wuo/AgMNpTJzVh/VjFcGYNMeZYaz7J4Vj6e5fCsQjzLbEZv4T53YLbrGBfE"
    "I5RBQM7rL2yzU76Q2/Cvy/ayWCa4HJvfZk3HUyZOQ/uTthJOqtMj31rs/mvc6wAacJcS/sPu7KUTZulwIboFm9X2cwDjnjmkW0Mz"
    "QuFdg5+gjKczlKrYkRbptUO5wWuWRNcXd/H6bXE1Nth0GfQjss9Q/QyoeIb/pnqm0WDRMq5/nTgeCkNLn33fpPk7DopmzPSO98Ae"
    "oMPpNuRF7qQyyJIPT8DyNsyw5WWb3xWObkIdpXAjyzIb/pWpSrT2SIcZZqJ/YXlZYI42UGJhNkYPuE8ul39nNLV74bPkoZfRu1cn"
    "vFvEOsY67wI6fJairQtaoF/p9VX4Y/mgA+V5gaV1zSK/jfARado3xpcHuN0s3Ci7aY2VFzdtT+u7kB8Dp3Q4Epc99iOzIq4a8tb9"
    "phpaSlsJQNo9vNiargoHoAkwQE/DICD4n9KNjz11l722KQ3r3W6aPcGZZY3im5l4yT/Pz+K2hCI+cOMFVzUaRzEqeEWtQU9/TlRu"
    "l2p43zlOUp55oWqZD4cNcVd6giF1jp8ANHYMEAiAG9r1/AH1+u/F4twcfwKRyKXbogWS8WEd7KqV9Hgwu1+XGmbrQuQS3t1WuJBl"
    "ewP/kfX7xFddJQGsKbQi1Pmgv76KkHp/7f/VCn5/b6Hr7WAOdAMG9Oriuuyeo7OToab/9jXJJMEWJJtUkbuG15aTs6ZUlm5HJpAY"
    "pcmB4aXIvtTsmd3lZXq6N8yBmKFl3rtZXFyljesWleY9lkjGgCwU7Wxnf0sDZG7CdxL7+sd1eIRukfQCRSa+ZPkUHqfTFqkjIfpo"
    "mqCJ/xgINpfQT7xgOiOewf0+V2JrLHQE95xhZRYglfAYsV5HEOBXktOMnViPlj0FzQZEjbg9neUA0EMmgCTwoZutUSFQ/BHkSkYm"
    "bOgRBb8CBYfBA+LSoBlNvPCbyx687zuoPEms4GGFSWKFbmIFqxm85h2pkEBxLiIyaEkkQXMQmp4Ejb1ifdB67xHgvNrpGbpeo4ur"
    "9aZ4JojfBq7YTd9LT6EEgf2suM3gTZTHVdTDOs3E10qaEcUN0iZR5Sx4EOVxlW5TWyjdt8pAXi+mcLWQQU4AM9SLuc7FoofQKprR"
    "Axnn+qNhhU83gEImorN5BztD20XFlOtpygvm170FU9gsUNgwBMxcP06jYNfhL1NTbP+XG16mrazcfGPaT19nO71+po7RRS3DU7x1"
    "8eABKEWjdCbr2Yf21HCaumuk/TVY0qhIxlvrvy1ZvrZEqhMeU/UVK9CzMAZnyXt9vbMkLQfJpcgJQqsJJcq6EGSIFTJUhs5NPwyM"
    "2b1YZ7QI7tLLJGBrZl3b8dLiZngjghNTN1kMRNMe4YmRtJdURtzGmFPyuRwoBd8uHSL3tkV/xCTBwBYWf5mGtiMPquClkLjvLEcw"
    "ouKLt+t5W8x5kUZ7Gd/KQONZ7+vM7lWcNGeRDAUXpggUC6gBaHLrFAElGiGDDZ0WPGHDcezpFog5nNhu6HkKqpeASwhUA/BgHMsr"
    "3+XucczraV+z/TUxnLmIo05r7YnnkXum4ZNFSUAniuMF6BbcVrnLZrPJ0DeGw6CBRuPu/h7DTunBqNlxL92F9nAUs7igPhnbQwO/"
    "aKvS+muOq57f3uu0QAUUafjMNZJGue7dJb1N4nGyrqqKtZJO6HFDra+C2Mzc+4RZ+BudihV7xcCXeRr3zuDVHWMtuqVGP9imTRda"
    "qXcWqLI8pkcPGQX3Cx/Yawhsz5CcXfRixJDt7oml84ttXYy7+LRbkPmlbjHvE5hVYhk12E6j5hooEbTQthd/GIFkY5YXyCS+IhEp"
    "Ekj3X9HXs6jkKi8prb8BlrgMB0gkvTLByOmTYmi6nBK21DKlAuniT0248SdSOAeKV1JMvv/qpwdg8ZFv/9046MwXVtx3763/5s8v"
    "MlnlVymkVa9re+IyqfP0i3TRy2P6apCRZNzrKwbvCU2lKKljblMCzVXtuGyUtaCwRcNsGV/FG+nDIXQUdYI74y2BjtYn9TewfT6y"
    "PVWufvK3MppM16c+xqxAUmIe09cZstij5jlkX/Yy/EGXKmgYwXsiYTkYf5EFZtmkGWivfL1shLjXsmHmI/vWI8kWfzYEWi2peZQt"
    "oXVZaqPbDJ4TYbU9LLLnv5Qjv1FXzIHa9J6G1a6obT1n6KRhjZvrF176BcFi0AQ/SgWDgl8AEk264zFoKfhiS7BojZq4apHeAFP9"
    "eZBmSowmXmpDlYf9qn9vHf/IwuoJ6y/9ZGEaZo8u312w4IxBc50vwwCYoILQHKNKgXoDSEejgZE9dUteOPvNdIarNNv9QC8BCLgu"
    "EBTGkCwggYHlI0nvQBGCYo8YAxV+0ANUcsEVVTyTFitMO9Kkqd0viJBZQTegiEHdevC7NQB6kWB4AdQ4Qp5Qr4T6UMxlcLHDTJxA"
    "T7HaW31KyCjztwAzjHCjDv6KGQQlcNXAKB32EFm7iaLaJzUv5qHLz+xCKXwyacaawMCXj5rBoYJsE8qZMFZegxUiJzKGHfD95rFQ"
    "tVAvsRpO3cgs8P/lMW01RUQVDqyz7mNodQV+yA2gMnA/V1sftSdaBrtGSXhm5PUVH4Pz6EjItwjmxKai6LhuoaUJUMd8LEDLRtWz"
    "DjBYIXyKjrXBSrJ8UXoCnxwae0Fp4uo4Y0AtWLIaXhbzeVmcTDTQD3R7oJcNPhTQk8kvVzcbS2qd9Gb6fn1d4t3AUUuzn6+vJmho"
    "sSnHHHu0KaVwWIQwq01ONH39DWp+E+8vrosf2HJabwBh0MoT+OATdpgPKsS6ponAeTBMMPDJnnjp075SQB04uOC7yQLMAF1PmNYc"
    "75FtW9xPxrCm3+xcaf39Mp7CAshhqrIfIOtO+jBLYU1BD4/itwVTF2Gwc3Lk/KmLJEDbo8IoI8CcUii5DgsRk0nTwEwcTmDFP29G"
    "nuFMDSerOAEgb1suu9p3TNxs2Aoldowh7jUcR139kMXty8dEa3UjBIW39zOpvaNQIm45/GiuJ3t8cNvXQkAnSdB3kqDvRxH3ceRa"
    "J74mNsHnSw9jtvAh8MwFiorAEn5CMxinyvt7EFy+g8r8hK+HBban9Epo6NFQFDbLywbGbaEHa3k5/HAnexCuwTIZr8mvf0IrxGEP"
    "gBCCde2J06GpTckj3ZJ2NzhuwQlFrB5IRFi86EQcpqLfxOVmxcukbvGntaWFxQPwVErLLMgMycJ6TH7WgR8vmVwT8xffjJV19RuT"
    "mT4eD0MW3S8V1keuH4wogYtUoecaRV/YQgiYqCCyta8vziJFbyYuyAEuNmtg+eM6BBjwNg5KkJId46pA3uHMN92dW52ULyBsWMP1"
    "qW56KbcNEo1ccaFJe85eTlTwZEckB/cylRfeNdYHtnYqc8MNlwUAlo1JHXs0gsS+vYleQejB8jLIKIYcP2Hj44bR2y9BN9iZuKC0"
    "EYSfKp2oVTYFLdoJu8eklwWFsXGeoGszPY9QZ9Yp92t37vKffVrQQFIAdYRb9DH9PSMcoy6+DGl6czTNOrbV1R0MxZh4uHPYJY2P"
    "OELCQhCQGSdkka4CrC9MPLPbp+rAEkSVhebbLLZkhjEzi6ugPoiwJ/SM4xlHgJ2vzcRiQZeWdGGWJuOGIyejxooBWeUCAcYdZsbC"
    "0viYHjcz/sDrsrf+ZSzeu6T1gk5VxvoZQjSp35LFud0MGGILfnfuCokDzYW6tq0lDrLZFENMsk1kS8hhuhbb+Dhuvr25QuQPLJXA"
    "3npsxsvsGcOxv7mihHzD++kexy6vvD28toX+0rpL42G7BoyHyt0K4fFgx+MjRL8PO5rRrAODD1v4YXsG7pFIn1zzoXGULa3Y06vB"
    "KvfyBWaa4TjAdmFQ9iPq/5FFcCsdLuRRoEXomVX2eGhYOKiJngX/EUuPlPFwFe5gBWUT/QIrGmgwjiRiNnCkPOb9EWNIGT+bSU0h"
    "GOQTV0k7pNHHN8lMiTxCsVFemKyq822eYH8ZFxES/4hekIzrNCSbi/uQK+OoSd4GsWQ2tHNtJW2uqJk6/oPonxGjE4s7cd5Wfm/7"
    "kb2LH82EBz6tC9doDe0EWzsvvcrJxlN4DsT0Iz+43523V4ITuWG2VuMFLo6lD4O5RyV3JHHx8gdGQqO78ojsnbviZySNRPK3pQoS"
    "4z76Iq6yZEY8yUthscVm3X5k1MN0QO0AOHyPaUf1xEwcHjc+PojM/Xu+kJzRqXXLZbbbdBbebaIAce1eeY4p/uOxCCjabLJzJPfK"
    "ZYL2HhUKe+EydMcmJF8gkB4+ZaRcJZfYTdp6EpkHSZq5yPyVDPB70ORNNMIo6GRvQjbLdVD4NokWKERxG3ahnMaJIMH5Gg1YSihj"
    "TBMa4HaJF+SNx8IusaIVMDIqVBBZ2ZxGaATpI9N10QBcKPo0yfKyp4mdsWwKcnSnUSvnhLHkCcY7+obO+KMYq3FgfzDjOis8Z36o"
    "Elum0KT1g0X8YCQzXBcLuo3sXVDyvtFg+4Ks3NKSI+RCsOOtsWfA/Siqvh8IlQl2D4Wu9fpqi71dEfmEG4dHYPJEtwQBdzmAiswi"
    "SLuTY68Ug542FhFSSz7m49dX/0M4INCtwpPwKAV6OHw9Q2jbWb1vNBq5zG9qNYf2f+jp893Qu+f1F4AyEDE4fmFM/IE73HU5RfOd"
    "Qz5QHnylTCzH0EGNwbN6UWBS3g8KrEGvk9/HRdCGVDBeSuFyzi/Nv8GCuePjCAMtMkGvt/BGcubdCEMKorbkdQFvG+hOOoZw0Rkr"
    "HvfbMcGt5DJBsNPnKkbd9xIgEX00FBwlohVkvyxMPLNv0a4C3Q/WFeEaFJk18YOT5CrdLroZKI54nIisa48MNqWEec0DYkeJxRnO"
    "v61XM8rA307v4y8ptiXz7cASNrBwASvMzIWWXozQxF1eTvf5vJNhKMwG3sYN3UHCVmI40aVdzjSeOn8xR3iPAG7IYfx+4El94Mar"
    "75SOYCFnwXIJU+uhmQ5KKH0hABYos55ol4BvXpE7FL2n6NJkUwJ+kS9U05jzMezsJMwCIok9BSWJPPzULBv99JPCb5sMRzcGKMji"
    "IkDH1/Lok3IIPX90XbxIJBnZQEMUSUvrdH0K96LORegcP8UrkPEdMzQFEdFN5pteiPO+kn+Yl4Y1A1IOMSUoZXc8mzjaL3Xc8fjj"
    "8WhptDkCu+mnBM9zg7Xv34BRDwoFgHkhfWwegDVaF1KjS3bejMMPKnIHeCBeusYJbmglti9K+ddGDGRBSi1iUkZpRaZcIOTTicON"
    "YbpPPH7MMD5DBLzSgCj8LhWwFFJY0GHA7NhgKuE+k8S26/JvmXlxOQq+Aj+SZ+BcbIWmF+5GPC3wJjEZmqYtIv4xywjUhpm/LCsh"
    "MXVn3CtnYr5+S/CmCfnI7pwhEQlC1WJhRL5njY6fO6OkUmI3ry7LrMDP9j78RMeb0kWj3yHRwKRRyMs2DxELpVCELo6R7DgMo6K9"
    "1Tuuq0nuw8/0TPtjnWnLneECdSo28JaWguKg3khe00Q3qiwqpawJejNCKS4avQEPmwZtrDlxh+YsTGooxNUzB+Yoj2Hy42UiITx3"
    "Yb/W+hfhDJSmAfrf8B9v8eVek2J9gvmhG2yTKIrZ722crRmfbD0Ue+w7Adg7LiHnakfHJwnC8TT8FDtaEaHWNMmifwY7nbmtEpfg"
    "wDdLATj+GTMWe4JcuB+E4gzkUJz+u6E4nh+K0/dDcUb6bMgvQSv+f+y923bbSLIo+N5fQWm71UALpHkTby6abUuqsqtsy1WWXRe1"
    "tgCRkIQySbABUJRK4lrzBfMya87T+YxZa+ZpHuZT9pdMROQFmUCCpFx29d59du3eFpHXyMjIyIjMyIiqa7S04XSO/Yr3S6mp0EnC"
    "DuL2Y+smRvHpjI6NTlxuH4UHLyeuTysKfibspFotXcuXZlZup/SAkh6WJ+zcUzRfZMSjme2kZ5lXdWnDHYwMM6MofvwBz4mmSuTP"
    "4X6zdBtmZiCSHtrp5+rEZ+TxuVpv1y39x//831einSgExX7SJDOsKH3i19ROQyVZKcMsOImW6EIDl+f7tvq+FM9eLlJrXZi9WmfT"
    "iwYNg1nrGI7KOqAy1g+DVbypx8G0/QqrvdxpPxu1cefVDvaZgCWwtr/2dF67hIiFdrw1Md7e1LjVHA7gQVcpio5yTG9DNJghtZzQ"
    "NXc623tytq/3bZVHu1TSNpyAixckRXNR/QzQP8MrRAXMViGYdNlogvL3gvAi0SBoF0JAd6N5ANgqdmZGZKnkWXM+FcTDGx3GTiGM"
    "/JVm/jYje5aaxxoTO9bDI6UXAU/kF2KFLk4KF5o8tUXfLtn3JPwoEGn43fycrNRPajQ5bB8AOTi7ESj75Qt2rs3XKLqt6rkos+d2"
    "WHFOLvUsVCa6zvt9hqK314AjZbtkkn/hbtnlE8MVBChIJrBljApk6t8JZygixL1buQ1TgmDsYgAi+Zp15F6z7UuzWsURlGkERZud"
    "gAUfOrB+5d0h7+dHwxVyTnNTEEZPs5RvoFW85eCXDNIgWENgMCtEX60q8RfMAHuqna9Z56p165Vaq1OpVfaqvb1qtQp6l5rmkosa"
    "9HgHcjKqwxcXGxn0El5yIxf0yrH1TeGFu3KiJ59bFyKElStGSk0ihZXMICbXIyrEv2PYCpMwasMZJHy3Ggl4OLJy9FigeOx1OXYs"
    "lxm5O/HoQYwikbaaphk3LBSCy4ySDBLkCz0DS8ETBgNLORcSUNf5ljOSN++yA8e6xQNvyIGTL2qdkxi6TaMVbdWcbSUG2DbycQNK"
    "VES+43uXMm/YxTvvGiQau3fDj0fXs5X1Syhn9cwI5+d9JkuMb3OrI7VsLERWM10hsjSg7DyYwg6L41eRh5m5OVszMo1Jsqk3NqOv"
    "f4TlayjGtpSf9smUQZDTL/up9MRfN9A2p2+6/GwgRr8Hn0/64a0OMVzNWJMsanuaVqCeJRk6T89LVxsHCdFCV2sUVOVkCoBEiIK4"
    "0VftNRYaiFbQqr+nu19fUUDWEyBUe5S/L5/6CZpaSKP6Rt3W/ApxwV7ef22Fulbyal8IfeNr+TiUTBTNChZQBNM1cFyFmpCwrxC6"
    "0K+WdnbnWL7BpkM14PAXZvucm0spRzo+yGw/XLI3DKjAdTdV4FbSomnui4/6zBAp+quPF4VWZBsUMsUJUrrckoXJQIXbkzsWemM0"
    "mad4ijjKjW4lLqcLZeeLFmR1oF4EDdxDt5cmkZ41MA+s53GDlOSkXtsU3cFgxckBPfwWD2ZWHBbQGRvZo+BrBW+XPLsrL7dXlcvb"
    "yZlP7CL8x1OM+Yi/3OiqS+R4wim54mCJ7kYqlQrghWTDk98s9z/+5/9JpiRoZXGGOjR5gUlPJsTL6JyhnOYnTGUewc4O98uAjlvF"
    "K9PAlk/BX55LpkY24+bSCi0yM3PsJtC9DwSLYgM5yXvC5Gt8Z5W1k/MWhUU1c7m86llfr3qmdM5OPt3ckcnCgjkyzXrBUamc9hXk"
    "x6q+4hsrLsZeZhHp5ZMr/1BaMmXawtpvFPIsOIzXTkr4UDXCVI0D2ZilraZCr/Ne5MQ9b5knVzzqM41SPjTTibbYsNPRqVohXofD"
    "lbGHbDjb/NVXmd50bReeKXCAhJUkvrX0sUm8QxIGk5DoUaKZyb5Nn8zTm3JtSRVZsrFtOlwoHh1ok8uAB0ls991Fbyp65sdxgJF4"
    "Wb60kCjYvaVFh+tmUDDxpnNvnO7xeJj5w8qnbt36ue8PG8y8a7jIOhMYG+1+5mnqWJoZjYxFL7JmRVBB+KiaGWtMjKlXi/yTCXSl"
    "wm2JMuZD+mt+ZnvzBN18U3YpvJBv84WPgAQN/8kvDz1skhY56MElmM59/nJgKmyPtDcD+pu3oM94aIQmSKxvx+szZ8tAICgKoCGR"
    "97QP5DMghsBdMVeC+OsAsn0LloGHjLkfUFNh2tQTCoRkhZKXVHuyaWQWsNMBCKyMQw7k8CdaqvILHdx5/Io/BQ7vx5Z9yt6dnfhO"
    "corSAjtgFw/YaJtSC+sOAU6qpxKObrfb28UUu2wluQxMQVkHxZ2puNnzZRnI7T2L0KHKRRROrDuu+srH4Q0HAGHAkO95Wz5+zWDO"
    "toFNOuIZHVqOkS1LzgTnpHbKvP1WFSc73Jo3Z/Cbe7Wc3oKxZ8tkoJK5EBvnH5gTs6atEu9iqHlirPz2BPmCtjeO+d54wVUKfwQq"
    "7BzNHiKLS8e24L8mOZDLz3JuTVbRvrAu1jdvv2CvSk1u8aVLhsPRaXbp0d2uD5Pgaja5c6Ooym4XgSAMUupU4RiKlMowM1poMKJQ"
    "OhXSJq2YaaGYI/KNgo0GxsXiU5wqzRaaxgxzNg3fMWdXXJRZt5NMDC2oHH24kDWKGfuFV+92q7UqMfbLhYh++SO9SHzt3QQToH5y"
    "uirjYO7PlNAXZwsl4sQNftzfn7M/t+zP9cJSrqjx6y7nrJ77aC55SYLIKiVhKZ5FvjcqTcNpmWJhnI/9koiKXvnTy2kpjEZ+hCXP"
    "IYOXcKi8hxyixFzkx8z1/ZV37Ze80kkmusapZZdYFEb0gS+BRMi5N38ejY27WUud4wvP++9YUe7Y/25ZSUK2YrjffvEouYNSu3jg"
    "hlcBLrPPykbiQJudvpbCr0ypDjB29/6efr7zgaAVXuiD6sy8X3Dfo1Dw8b9bg9774P6lPU3gV+e+1roHZR5+7o+9yQxd8VELjx6z"
    "2H6wGvh4ZLR2iROaVAUXDJNfuXMcQQ6vW2R4cH/vn7h/+5tIdXmywJ0GfdrTjeiJ5Qcx/cVH7grOlfIc5Dt8GMt6TZ4KO3mb4hPK"
    "rycihse0XwWezxqG2Zt+lTyZ7u7a0cn0tO/DP2KmIuUF7kKPX6AHIoivL8l5qIiJ1nSdK3KLwH5fB/7ieXjTc6ulaqnWLGEaGcm5"
    "9CjIuZmMp8DDrpJk1nv8eLFYVBaNShhdPq5Xq9XH2DhzPxqgbxdYc9w4AfnODDY/fFRDh3LRHB0Qu3grFI5gmW8PQWLMpYLS87oN"
    "MLyo1Sqd/Vq90ug09giseqXbbNRKtUal3erU8W9jb68l/u7LdFGOqsja0NqHeqW+j78rrVprr562VKnutbpN2WK10mo2G629fdFU"
    "tVJv1NqdPdlgldorVV9Qi7y5qmxIlhctpU2mTYmypbQ+tPahvV8ttSu1vW6tAbWqrUYdIG5XGrVaGxuutffajRYkNOvNegub63Tq"
    "ex1I2Gu02l0o0WxWO234pnHgXyjUpuZYWhdbqssKAAe2JFusVWqULrqsVeoSHvrNsFhBtHUbzXYH/jaq0BaOo1NtYqlmt97pir/7"
    "abooJ+rVccT4V052lealQrPYqHVbaaV6Za/arqWN1iuAPaXTeqWTtowfiEzRLCWxtkU90b5ol/3dV9JFOVGvwyYdf71o77cqHUI0"
    "ZbQAik6dSndgxuB7D+aJ0Sz8gMJNnEiksGqn04B8orZ6s9oVv5v7/MceoLqkVGjDNKQNNiqderOxLztswJBbCACHBmgF/vnldbfS"
    "bneqezSttW59v1vpwFbaoGmHZoCymjXM3eu2Ox38JooAOReovgrLoKNl7lW73bRqq16X7cJnu9GsIblUu0jW8N3tEMV0mlQageti"
    "wx8AVqQxrNOptlol+K7uValOp9rF706rhYSD3/AXx9qBwdJ3G7/bbSBE3kcHv2t7bfoEpMBnq1Wn0u09bGwP/qtTbrUGn01Ybh0B"
    "Pqz0NrSxL8YGc9FiLdPQ4bMK/8fw0qjUEPwX7Qrwu2qdz3xXpPPJ71AbDTlXLeoD+uSTj/A1oRzNLbaD8EI7deW7TfhPv7t73Wqn"
    "JOo3K7VardWV7TcrdcBmfV/036w0YOU2SwI++Cb4ONzi+0UHsFmttl61CP42z8d+a9UasZJaDb6hnWqzXcPv+l4dlkL63eTlxfde"
    "s91Cohb1W91qFeEQ7Xd4+QYhtQ0sqNXE9pswJ0g6MJl1LL9H5TsSnvZes1FX8jvddrem1O+q7b/qVlo0zj2Yh06z9oGT3T6m12uS"
    "JOETprojKTazUn55XcN12HwB1LcPKG8jpeIyg74BhXv1vb0GLcNmF1He7uDQcdl22u39PUBJt03fjToQ4R6gAHkssoFqGyEjxvIB"
    "6WqfZ8LKrHcb3ZKo26002829umy7W6nXcNWIvjtAFtUG5jPYcDrrNaTZTolN7d4LGMI+MnZghzIfCL/dbLY6sgHYKmr1BvA+0QPs"
    "LnvVerspQQAuAVWhxY6Eskpr4gOOYl/JFiOUTQgMyE4EiiQYAocCToFjhn6cBtjX9mjFVvc6uDHVu60qrVHoFXeCRrOFnLrKqlRp"
    "xuD/9xpV/CT20gB6ERWQ/dSaddkgfLc73QZ9d4EOiVvVmm32g4+ReHhrr0HVWfE6MJRm2hp8Aivdl73BN/EqDgduDw2xbbB54XCz"
    "HYsPitWSY+aNwjcguC365BsjgVPTaIm+GPSyDh9WBo+/COFuOI8ikMX30Z+icn0BqlatZS8vF8JT+/6CFIhFVv8Kpuv0r2NV//rI"
    "NK4j9ueA/TnU9K/D/wr618Hm+tezfzH961mR/nX0h+lfH9fpX890/evZH6N//fqfRv86/hz6138rN/+t3PznVW7+S5wM/PIaxN0W"
    "km53D0X0ZrPWaJMo26ijKL0HkjDKnCihEopLnRcgY4Gw2iVqpP26hthpIxLaTEcD7KC4y2i5ivI+9tBmtAyrAwmfETP7aO7zH3WG"
    "QFmlyhDMm2zRRFLhGpuQDk2QAAa+UQDEv6A9VJudV6RGNZkKwnRAUk+qrFEQXNtMfekwBQwEPRSCgJZJ5QJ1jak/nS7B3Qa5GxU2"
    "0EoIdJCIGqg+dattGkC3i/JWHZRANoY9kubqNYaVWpfUPZBxq4SVapOUJ5BpgVgBbNAaqHoblQOU9plq1noFaAGpG+bnA4xjH7+a"
    "WJkYDOMTADMhqs35CGqgiKgWYzSkcjZIpWNMCL5pLuEvzTm2xdLq1E5avkYUn7ZHvFD215KQkJr3oU0rCNg98bZmG6YL1bEaqns4"
    "5Z1WndQzUr4aSG/VdmsP4QaxsYl5NdA1UAdqt6v02W6294iUQLWD4vU6aUQdUBVw0da7e8R2u/VGExUvSclMOxJqhqoiCTUjr6bo"
    "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"
)
# --- END GENERATED UI ---
