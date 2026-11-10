# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.9.1"
# ///

import asyncio
import base64
import ftplib
import hashlib
import html
import json
import logging
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
PLUGIN_VERSION = "0.9.1"
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
FONT_STACK = (
    'Roboto, -apple-system, BlinkMacSystemFont, "Segoe UI", "Noto Sans", "Helvetica Neue", '
    'Helvetica, Arial, "Apple Color Emoji", "Segoe UI Emoji", "Noto Color Emoji", sans-serif'
)
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
    }
    for path in (SETTINGS_FILE, OLD_SETTINGS):
        try:
            return {**defaults, **json.loads(path.read_text(encoding="utf-8"))}
        except (OSError, ValueError):
            continue
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


def plate_settings() -> tuple[bool, int]:
    settings = get_settings()
    return (parse_flag(settings.get("plate_check")),
            parse_margin(settings.get("plate_margin_percent")))


def save_settings(settings: dict) -> bool:
    try:
        SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
        SETTINGS_FILE.write_text(json.dumps(settings, indent=2), encoding="utf-8")
        return True
    except OSError:
        log.exception("Could not write %s", SETTINGS_FILE)
        return False


def get_spools(spoolman_url: str) -> dict:
    """Return ``{"ok": True, "spools": [...]}`` or ``{"ok": False, "error": "..."}``."""
    url = f"{spoolman_url.rstrip('/')}/api/v1/spool"
    try:
        with urllib.request.urlopen(url, timeout=TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except urllib.error.URLError as exc:
        error = f"Could not reach Spoolman at {spoolman_url} ({exc.reason})"
        _report("Spool list", error)
        return {"ok": False, "error": error}
    except Exception as exc:
        _report("Spool list", str(exc), exc_info=True)
        return {"ok": False, "error": str(exc)}
    _report("Spool list", None)
    _spool_cache.update(url=spoolman_url, time=time.monotonic(), spools=data)
    return {"ok": True, "spools": data}


def clean_url(url: str | None) -> str:
    return (url or "").strip().rstrip("/")


def ping(spoolman_url: str) -> dict:
    """Ask Spoolman for its version, which doubles as a connection test.

    Returns ``{"ok": True, "version": "..."}`` or ``{"ok": False, "error": "..."}``.
    """
    if not spoolman_url:
        return {"ok": False, "error": "No Spoolman URL configured yet"}
    url = f"{spoolman_url.rstrip('/')}/api/v1/info"
    try:
        with urllib.request.urlopen(url, timeout=TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8"))
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
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


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
    result = get_bambu_spools() if source() == "bambu" else get_spools(get_settings().get("spoolman_url", ""))
    for sp in result.get("spools") or []:
        sp["rfid_tags"] = sorted(spool_tags(sp))
    return result

# --- Filament profiles -------------------------------------------------------------------
# For each of your printers, one OrcaSlicer filament preset per Spoolman filament, written as a
# local preset bundle and hot-reloaded. Each one inherits the closest preset OrcaSlicer already
# has for that printer (so the printer's own tuning is kept), is limited to that printer, and
# carries the filament's colour, vendor, temperatures, density, diameter and cost. It shows up
# under "User presets" in the sidebar's filament dropdown.
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
})
# The one listed setting OrcaSlicer holds as text; every other is a number, a percentage or on/off.
TEXT_KEYS = frozenset({"filament_notes"})
PROFILE_RETRY = 300  # seconds before a refused set of presets is offered again
_profiles: dict = {"names": {}, "error": "", "count": 0, "failed": ("", 0.0)}
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


def profile_preset(filament: dict, name: str, parent: str, target: str) -> dict:
    """The preset JSON for one Spoolman filament on one printer. Values are lists of strings,
    as OrcaSlicer stores them; one value applies to every nozzle variant of the parent."""
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
    preset.update(orca_settings(filament, target))
    return preset


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
        files[f"{name}.json"] = profile_preset(filaments[fid], name, parent, target)
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
                "gen": _ui_snap.get("gen", 0) + 1}
    except Exception:
        log.exception("Could not read the presets")
        return None
    _ui_snap.clear()
    _ui_snap.update(snap)
    return snap


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{threading.get_ident()}.tmp")
    tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, path)


def profile_digest(files: dict) -> str:
    return hashlib.sha256(json.dumps(files, sort_keys=True).encode("utf-8")).hexdigest()


def synced_digest(target: Path) -> str:
    try:
        return str(json.loads((target / PROFILE_STATE).read_text(encoding="utf-8")).get("hash") or "")
    except (OSError, ValueError, AttributeError):
        return ""


def write_profiles(target: Path, files: dict) -> None:
    """Make target/filament hold exactly these presets."""
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


def _install_profiles(root: Path, snapshot: dict, files: dict, digest: str) -> None:
    """Write the bundle where OrcaSlicer reads it and reload it. Raises when it is refused."""
    last = None
    for folder in profile_folders(root, snapshot):
        target = root / "user" / folder / "_local" / PROFILE_BUNDLE
        if synced_digest(target) == digest:
            return
        fresh = not target.exists()
        write_profiles(target, files)
        try:
            orca.host.preset.bundles.reload_local(PROFILE_BUNDLE)
        except RuntimeError as exc:
            last = exc
            if "does not exist" not in str(exc):
                raise
            if fresh:
                shutil.rmtree(target, ignore_errors=True)
            continue  # Not the signed-in account's folder.
        # Only after OrcaSlicer accepted the bundle, so a refused one is tried again.
        _write_json(target / PROFILE_STATE, {"hash": digest})
        log.info("Synced %d filament profiles from Spoolman into %s", len(files), folder)
        return
    raise last or RuntimeError("No OrcaSlicer user folder accepted the presets")


def profile_sync(spools: list[dict], snapshot: dict | None) -> dict:
    """Write and hot-reload the Spoolman filament presets. Never raises."""
    if not snapshot:
        return dict(_profiles)
    with _profile_lock:
        root = _orca_data_dir()
        files, by_key = profile_files(spools, snapshot)
        digest = profile_digest(files)
        failed, when = _profiles["failed"]
        if digest == failed and time.monotonic() - when < PROFILE_RETRY:
            return dict(_profiles)
        try:
            if root is None:
                raise RuntimeError("OrcaSlicer's data folder was not found")
            _install_profiles(root, snapshot, files, digest)
            _profiles.update(names=by_key, count=len(files), error="", failed=("", 0.0))
            _report("Profile sync", None)
        except Exception as exc:
            _profiles.update(error=str(exc), failed=(digest, time.monotonic()))
            _report("Profile sync", str(exc), exc_info=True)
        return dict(_profiles)


def load_spools_synced(snapshot: dict | None) -> dict:
    """The spool list, after syncing the filament profiles from it. For worker threads."""
    result = load_spools()
    if result.get("ok") and snapshot:
        state = profile_sync(result["spools"], snapshot)
        result["profiles"] = {"count": state["count"], "error": state["error"]}
    return result


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


def spoolman_call(method: str, path: str, body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors."""
    url = f"{clean_url(get_settings().get('spoolman_url'))}/api/v1/{path}"
    data = None if body is None else json.dumps(body).encode("utf-8")
    request = urllib.request.Request(url, data=data, method=method, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8") or "null")


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


def send_changes(name: str, changes: dict, snapshot: dict) -> str:
    """Write a Spooler preset's changed settings into its filament's orca_settings field, in the
    section for the preset's printer, and rebuild the presets. Returns what happened, for the user.
    Runs on a worker thread."""
    fid, target = next((key for key, known in _profiles["names"].items() if known == name), (None, ""))
    if fid is None:
        raise RuntimeError(f"{name} is no longer a Spooler preset. Refresh, then send it again.")
    filament = spoolman_call("GET", f"filament/{int(fid)}")
    data = orca_settings_data(filament)
    if data is None:  # Never overwrite what can't be read back.
        raise RuntimeError(f"The {ORCA_SETTINGS_FIELD} field of {name}'s filament isn't a JSON object; "
                           "fix it in Spoolman, then send again.")
    # What Spoolman gives this printer now; a setting that differs from what the preset was made
    # from was changed in Spoolman meanwhile, and Spoolman's value is kept.
    now = profile_preset(filament, name, "", target)
    section, sent, kept, other = {}, [], [], []
    for key, (text, saved) in sorted(changes.items()):
        if key not in ORCA_SETTINGS_KEYS:
            other.append(key)
        elif key in now and not _same(now[key], orca_items(saved or "", key)):
            kept.append(key)
        else:
            items = orca_items(text, key)
            section[key] = items[0] if len(items) == 1 else items
            sent.append(key)
    if section:
        if ORCA_SETTINGS_FIELD not in {field["key"] for field in spoolman_call("GET", "field/filament")}:
            spoolman_call("POST", f"field/filament/{ORCA_SETTINGS_FIELD}",
                          {"name": "Orca settings", "field_type": "text"})
        # Last, so it beats any other section that matches the printer.
        data[target] = {**data.pop(target, {}), **section}
        # Every field goes back, as some Spoolman versions replace the whole extra map on a PATCH.
        extra = {**(filament.get("extra") or {}), ORCA_SETTINGS_FIELD: json.dumps(json.dumps(data))}
        spoolman_call("PATCH", f"filament/{int(fid)}", {"extra": extra})
    # Always, so the presets also take the values Spoolman kept. OrcaSlicer's reload keeps every
    # unsaved edit, so a kept setting's edit stays unsaved for the user to send again or discard.
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


def start_send(post) -> None:
    """Send the unsaved changes of the Spooler preset open in OrcaSlicer to Spoolman. Call it on the
    UI thread; post() gets {"type": "sent", "ok": ..., "text": ...} when it is done."""
    try:
        if source() != "spoolman":
            raise RuntimeError("Sending needs Spoolman as the source.")
        snapshot = refresh_snapshot()
        if snapshot is None:
            raise RuntimeError("Could not read OrcaSlicer's presets.")
        name, changes = edited_changes()
    except Exception as exc:
        log.warning("Send to Spoolman: %s", exc)
        post({"type": "sent", "ok": False, "text": str(exc)})
        return

    def worker():
        try:
            text, ok = send_changes(name, changes, snapshot), True
        except Exception as exc:
            log.exception("Sending %s to Spoolman failed", name)
            text, ok = _spoolman_error(exc), False
        post({"type": "sent", "ok": ok, "text": text})

    threading.Thread(target=worker, daemon=True).start()


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
    return {"printers": printers, "live_ok": live, "usage": usage_state(), "progress": progress_settings()}


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


def _mqtt_exact(sock, size: int) -> bytes:
    data = b""
    deadline = time.monotonic() + 15
    while len(data) < size:
        try:
            chunk = sock.recv(size - len(data))
        except socket.timeout:
            if time.monotonic() > deadline:
                raise
            continue
        if not chunk:
            raise ConnectionError("The printer closed the connection")
        data += chunk
    return data


def _mqtt_read(sock) -> tuple[int, bytes] | None:
    """Next packet as (type byte, body), or None on timeout."""
    try:
        first = sock.recv(1)
    except socket.timeout:
        return None
    if not first:
        raise ConnectionError("The printer closed the connection")
    size, shift = 0, 0
    while True:
        digit = _mqtt_exact(sock, 1)[0]
        size += (digit & 127) << shift
        shift += 7
        if not digit & 128 or shift > 21:
            break
    return first[0], _mqtt_exact(sock, size) if size else b""


def _int(value: object, default: int = -1) -> int:
    try:
        return int(str(value))
    except ValueError:
        return default


def live_apply(dev_id: str, name: str, doc: object, link: str = "") -> None:
    """Merge a printer report into the live state."""
    report = doc.get("print") if isinstance(doc, dict) else None
    if not isinstance(report, dict):
        return
    with _live_lock:
        state = _live["printers"].setdefault(dev_id, {"name": name, "units": {}, "ext": {}, "time": 0.0, "link": link})
        state["time"] = time.time()
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


def _live_prog(state: dict) -> dict | None:
    p = state.get("prog") or {}
    gs = str(p.get("gcode_state") or "").upper()
    if not gs:
        return None
    def num(key: str) -> int | None:
        value = _int(p.get(key))
        return value if value >= 0 else None

    tray = None
    t = _int(p.get("tray_now"))
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
                             "heads": bool(state.get("heads")), "unit_label": state.get("unit_label", "")})
        return {"links": dict(_live["links"]), "printers": printers}


CODES_FILE = DATA_DIR / "printer_codes.json"


def _code_key(pid: str) -> str:
    return f"{source()}:{pid}"


def read_codes() -> dict:
    try:
        data = json.loads(CODES_FILE.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except (OSError, ValueError):
        log.exception("Could not read %s", CODES_FILE)
        return {}
    return {str(k): str(v) for k, v in data.items()} if isinstance(data, dict) else {}


def write_codes(codes: dict) -> None:
    try:
        CODES_FILE.write_text(json.dumps(codes), encoding="utf-8")
        os.chmod(CODES_FILE, 0o600)
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
        packet = _mqtt_read(sock)
        now, clock = time.monotonic(), time.time()
        if (clock - wall) - (now - mark) > LIVE_JUMP:
            raise ConnectionError("The computer woke from sleep")
        mark, wall = now, clock
        if packet:
            heard = now
        elif now - heard > LIVE_DEAD:
            raise ConnectionError("The printer stopped answering")
        if packet and packet[0] >> 4 == 3:
            body = packet[1]
            size = struct.unpack("!H", body[:2])[0]
            topic = body[2:2 + size].decode("utf-8", "replace")
            dev_id = topic.split("/")[1] if topic.count("/") >= 2 else ""
            try:
                doc = json.loads(body[2 + size:])
            except ValueError:
                continue
            for reply_topic, payload in on_report(dev_id, doc) or []:
                sock.sendall(_mqtt_publish(reply_topic, payload))
        if time.monotonic() - ping > LIVE_PING:
            sock.sendall(b"\xc0\x00")
            ping = time.monotonic()


def _live_active() -> bool:
    return time.monotonic() - _live["seen"] < LIVE_IDLE or _live["keep"]


def _local_session(pid: str, link: dict, stop: threading.Event) -> None:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    serial = link["serial"]
    with socket.create_connection((link["ip"], LOCAL_PORT), timeout=8) as raw:
        with context.wrap_socket(raw, server_hostname=link["ip"]) as sock:
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
        except Exception as exc:
            fails = 0 if time.monotonic() - start > LIVE_DEAD else fails + 1
            _live["links"][pid] = "unreachable" if fails else "connecting"
            log.warning("Live link to a printer stopped: %s", exc)
            stop.wait(LIVE_RETRY[min(fails, len(LIVE_RETRY) - 1)])
    _live["links"].pop(pid, None)


def _local_sync() -> bool:
    """Match the local connections to the saved printers."""
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
        if entry and (entry["thread"].is_alive() or _live["links"].get(pid) in ("auth", "none")):
            continue
        stop = threading.Event()
        run = _moon_run if link.get("kind") == "moonraker" else _local_run
        thread = threading.Thread(target=run, args=(pid, link, stop), daemon=True)
        _local[pid] = {"link": link, "stop": stop, "thread": thread}
        thread.start()
    bambu = any(link.get("kind") != "moonraker" for link in wanted.values())
    _live["keep"] = bambu and usage_mode() != "off" and source() == "spoolman"
    return bool(wanted)


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
            "remain": _spool_remain(spool), "spool_id": spool.get("id"),
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


def slot_tray(slot: int, spool_id: object, uid: str, vendor: str, kind: str, rgba: str, label: str,
              spools: list[dict], target: str) -> dict:
    """A Bambu-shaped tray for one printer slot, matched to a Spoolman spool: by the spool id the
    printer reports, else by RFID tag, else by vendor, material and colour."""
    spool = _spool_by_id(spool_id, spools)
    if spool is None and uid:
        spool = match_spool({"tag_uid": uid}, spools)
    if spool is None and kind and rgba:
        found = match_spools({"preset": "", "vendor": vendor, "material": kind, "colour": rgba[:6]}, spools)
        spool = found[0] if found else None
    if spool is not None:
        tray = _spool_tray(slot, spool, target, tag_uid=uid)
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
                     label, spools, target)


def lane_units(lanes: dict, spools: list[dict], target: str) -> list[dict]:
    """Moonraker lane_data, as AFC, Happy Hare and other MMU integrations write it, as Bambu-shaped
    units of four trays. Each entry's "lane" is its 0-based slot; an empty material is an empty lane."""
    trays: dict = {}
    for entry in lanes.values():
        index = _int(entry.get("lane")) if isinstance(entry, dict) else -1
        if index < 0:
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
        heard = 0.0
        _live["links"][pid] = "waiting"
        while _live_active() and not stop.is_set():
            now = time.monotonic()
            if now - asked > KX_REQUEST_SECS:
                sock.sendall(_mqtt_publish(f"{command}/multiColorBox", kx_request("multiColorBox")))
                sock.sendall(_mqtt_publish(f"{command}/extfilbox", kx_request("extfilbox")))
                asked = now
            if now - ping > LIVE_PING:
                sock.sendall(b"\xc0\x00")
                ping = now
            packet = _mqtt_read(sock)
            if packet:
                heard = time.monotonic()
            elif heard and time.monotonic() - heard > LIVE_DEAD:
                raise ConnectionError("The printer stopped answering")
            if not packet or packet[0] >> 4 != 3:
                continue
            body = packet[1]
            size = struct.unpack("!H", body[:2])[0]
            try:
                doc = json.loads(body[2 + size:])
            except ValueError:
                continue
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
            live_apply(pid, link["name"], report, link=pid)
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
            live_apply(pid, link["name"], doc, link=pid)
            with _live_lock:
                if stop.is_set():
                    # Removed while this poll ran: don't leave it behind.
                    _live["printers"].pop(pid, None)
                elif pid in _live["printers"]:
                    _live["printers"][pid]["heads"] = heads
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
    except (OSError, ValueError):
        log.exception("Could not read %s", USAGE_FILE)
        data = {}
    data = data if isinstance(data, dict) else {}
    if "prints" not in data and isinstance(data.get("pending"), list):
        data["prints"] = [dict(e, state="pending") for e in data["pending"] if isinstance(e, dict)][:USAGE_PRINTS]
    return {key: data.get(key) if isinstance(data.get(key), kind) else kind()
            for key, kind in (("prints", list), ("active", dict), ("last", dict), ("done", list))}


def usage_save(data: dict) -> None:
    try:
        USAGE_FILE.write_text(json.dumps(data), encoding="utf-8")
    except OSError:
        log.exception("Could not write %s", USAGE_FILE)


def usage_state() -> dict:
    enabled = source() == "spoolman"
    with _usage_lock:
        data = usage_load()
    return {"enabled": enabled, "mode": usage_mode(), "prints": data["prints"] if enabled else []}


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
    t = _int(p.get("tray_now"))
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
                data = box.read(info)
    finally:
        try:
            ftp.quit()
        except (ftplib.Error, OSError):
            ftp.close()
    return parse_slice(data, job.get("file") or "")


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
        usage_save(data)


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
        threading.Thread(target=_job_fetch, args=(dev_id, data["id"]), daemon=True).start()
    elif kind == "last":
        _store(lambda d: d["last"].__setitem__(dev_id, data))
    elif kind == "end":
        threading.Thread(target=_end, args=(dev_id, data), daemon=True).start()
    elif kind == "missed":
        threading.Thread(target=_missed, args=(dev_id, data), daemon=True).start()


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
    url = clean_url(get_settings().get("spoolman_url"))
    spools = (plate_spools(url) if url else None) or []
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
                     "state": "open", "error": ""})
    late = bool(run.get("late")) or run["result"] == "unknown"
    entry = {"id": run["id"], "printer": run["printer"], "name": run["name"], "result": run["result"],
             "pct": run["pct"], "time": time.time(), "rows": rows, "late": late, "src": src, "state": "pending"}
    with _usage_lock:
        data = usage_load()
        if run["id"] in data["done"]:
            return
        data["done"] = [run["id"]] + data["done"][:USAGE_DONE - 1]
        if rows:
            data["prints"] = ([entry] + [e for e in data["prints"] if e.get("id") != entry["id"]])[:USAGE_PRINTS]
        usage_save(data)
    if not rows:
        return
    log.info("A print ended (%s, %d%%, grams from the %s): %d slots to book", run["result"], run["pct"],
             "job file" if src == "file" else "last slice", len(rows))
    if usage_mode() == "auto" and run["result"] == "finished" and not late:
        usage_book(entry["id"], None)


def spoolman_use(spool_id: int, grams: float) -> None:
    url = f"{clean_url(get_settings().get('spoolman_url'))}/api/v1/spool/{int(spool_id)}/use"
    request = urllib.request.Request(url, data=json.dumps({"use_weight": round(grams, 1)}).encode("utf-8"),
                                     method="PUT", headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=TIMEOUT):
        pass
    _spool_cache["time"] = 0.0


def spoolman_unuse(spool_id: int, grams: float) -> None:
    url = f"{clean_url(get_settings().get('spoolman_url'))}/api/v1/spool/{int(spool_id)}"
    with urllib.request.urlopen(url, timeout=TIMEOUT) as resp:
        used = float(json.loads(resp.read().decode("utf-8")).get("used_weight") or 0)
    body = json.dumps({"used_weight": round(max(0.0, used - grams), 1)}).encode("utf-8")
    request = urllib.request.Request(url, data=body, method="PATCH", headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=TIMEOUT):
        pass
    _spool_cache["time"] = 0.0


def _spoolman_error(exc: Exception) -> str:
    if isinstance(exc, urllib.error.HTTPError):
        return f"Spoolman refused it (HTTP {exc.code})"
    if isinstance(exc, urllib.error.URLError):
        return f"Could not reach Spoolman ({exc.reason})"
    return str(exc)


def usage_book(entry_id: str, chosen: list | None) -> None:
    """Book the open rows to their spools; chosen holds manual picks."""
    wanted = {}
    for item in chosen if isinstance(chosen, list) else []:
        if isinstance(item, dict):
            wanted[_int(item.get("slot"))] = item
    url = clean_url(get_settings().get("spoolman_url"))
    by_id = {sp.get("id"): sp for sp in (plate_spools(url) if url else None) or []}
    with _usage_lock:
        data = usage_load()
        entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
        if entry is None:
            return
        for row in entry["rows"]:
            if row["state"] == "booked":
                continue
            pick = wanted.get(row["slot"], {})
            spool = _int(pick.get("spool")) if pick.get("spool") not in (None, "") else row["spool"]
            try:
                grams = float(pick["grams"]) if "grams" in pick else row["grams"]
            except (TypeError, ValueError):
                grams = 0.0
            if spool in (None, -1) or not 0 < grams <= 5000:
                continue
            try:
                spoolman_use(spool, grams)
            except Exception as exc:
                row.update(state="error", error=_spoolman_error(exc))
                continue
            label = _spool_label(by_id[spool]) if spool in by_id else row.get("label") or f"spool {spool}"
            row.update(state="booked", error="", spool=spool, grams=round(grams, 1), label=label)
            log.info("Booked %.1f g to Spoolman spool %s", grams, spool)
        entry["state"] = "booked" if all(row["state"] == "booked" for row in entry["rows"]) else "pending"
        usage_save(data)


def usage_undo(entry_id: str) -> None:
    """Add a booked print's grams back to its spools."""
    with _usage_lock:
        data = usage_load()
        entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
        if entry is None or entry.get("state") != "booked":
            return
        for row in entry["rows"]:
            if row["state"] != "booked":
                continue
            try:
                spoolman_unuse(row["spool"], row["grams"])
            except Exception as exc:
                row["error"] = _spoolman_error(exc)
                continue
            row.update(state="undone", error="")
            log.info("Added %.1f g back to Spoolman spool %s", row["grams"], row["spool"])
        if not any(row["state"] == "booked" for row in entry["rows"]):
            entry["state"] = "undone"
        usage_save(data)


def usage_action(data: dict) -> dict:
    kind = data.get("type")
    if kind == "usage_mode":
        settings = get_settings()
        settings["book_usage"] = data.get("mode") if data.get("mode") in USAGE_MODES else "ask"
        save_settings(settings)
        _local_sync()
    elif kind == "usage_book":
        usage_book(str(data.get("run") or ""), data.get("rows"))
    elif kind == "usage_undo":
        usage_undo(str(data.get("run") or ""))
    return usage_state()


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
    return [spool for *_, spool in [item for item in pool if item[1]] or pool]


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
    return {**result, "status": status, "have": best, "worst": worst, "padded": padded,
            "name": name, "total": total, "spool_colour": (fullest.get("filament") or {}).get("color_hex")}


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


def plate_notice(results: list[dict]) -> tuple[str, str] | None:
    """The one notification for a slice: ``("warning" | "info", text)``."""
    label, grams = slot_label, fmt_grams
    where = " in the AMS" if any(r["ams"] for r in results) else ""
    short = [r for r in results if r["status"] == "short"]
    mixed = [r for r in results if r["status"] == "mixed"]
    barely = [r for r in results if r["status"] == "barely"]

    def short_part(r: dict) -> str:
        return _sentence(f"{label(r)} {_need(r)} but {_supply(r)}{_tracked(r)}")

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
    return kind, "Spooler: " + " ".join(parts)


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
    level = getattr(ui, level_name, None)
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
    age = time.monotonic() - _spool_cache["time"]
    if _spool_cache["url"] == url and age < CACHE_SECS:
        return _spool_cache["spools"]
    result = load_spools()
    return result["spools"] if result["ok"] else None


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
    return plate_notice(results), results


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

LOGO_IMG = f'<img class="logo" src="{LOGO_DATA_URI}" alt="">'

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


def _fill(template: str, **values: object) -> str:
    """Substitute ``__NAME__`` placeholders.

    Plain substitution rather than an f-string or str.format, so the CSS and
    JavaScript in the templates keep their normal single braces.
    """
    return re.sub(r"__([A-Z][A-Z_]*)__", lambda match: str(values[match.group(1)]), template)


# The pages and the tab set overscroll-behavior-x: none so a two-finger trackpad swipe
# can't navigate the embedded browser back or forward, which lands on a blank page.
MAIN_PAGE = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<link rel="icon" href="__LOGODATA__">
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
  * { font-family: __FONT__; }
  html { overscroll-behavior-x: none; }
  body { margin: 0; padding: 12px; font-size: 13px; }
  .header { display: flex; align-items: center; gap: 12px; margin-bottom: 8px; }
  .header .title { display: flex; align-items: center; gap: 12px; flex: 1; min-width: 0; }
  .header img.logo { width: 52px; height: 52px; flex-shrink: 0; }
  .header-actions { display: flex; gap: 6px; flex-shrink: 0; }
  h2 { font-size: 20px; font-weight: 700; margin: 0; color: var(--orca-fg); }
  #status { color: var(--orca-muted); margin-bottom: 8px; }
  #status.error { color: #d9534f; }
  button {
    padding: 4px 10px; cursor: pointer;
    border: 1px solid var(--orca-border); border-radius: 4px;
    background: transparent; color: var(--orca-fg);
  }
  button:hover { border-color: var(--orca-accent); }
  #settings-btn, #plate-recheck, #plate-dismiss, #filters-toggle, #send-btn {
    padding: 7px 16px; border-radius: 6px; font-size: 13px; font-weight: 700;
  }
  #send-btn { margin-left: auto; }
  #settings-btn, .sort-dir { background: var(--orca-accent); color: var(--orca-accent-fg); border-color: var(--orca-accent); }
  .filters { display: flex; gap: 6px; margin-bottom: 10px; flex-wrap: wrap; }
  .filters input, .filters select {
    flex: 1; min-width: 110px; padding: 4px 6px;
    border: 1px solid var(--orca-border); border-radius: 4px;
    background: var(--orca-bg); color: var(--orca-fg);
  }
  .filters select option {
    background: var(--orca-bg); color: var(--orca-fg);
  }
  .sort-dir { flex: 0 0 auto; min-width: 32px; }
  .empty { color: var(--orca-muted); padding: 12px 4px; }

  .spool-card {
    position: relative;
    background: var(--orca-border);
    background: color-mix(in srgb, var(--orca-fg) 5%, var(--orca-bg) 95%);
    border: 1px solid var(--orca-border);
    border-radius: 14px;
    padding: 13px 14px 11px;
    margin-bottom: 9px;
  }
  .spool-tag {
    position: absolute; top: -8px; left: 14px;
    display: flex; align-items: center; gap: 4px;
    max-width: calc(100% - 28px);
    padding: 2px 8px 2px 6px;
    border-radius: 4px 9px 9px 0;
    background: var(--orca-accent);
    background: linear-gradient(135deg, color-mix(in srgb, var(--orca-accent) 80%, black), var(--orca-accent));
    color: var(--orca-accent-fg);
    font-size: 10px; font-weight: 700; letter-spacing: 0.02em;
    box-shadow: 0 1px 3px rgba(0, 0, 0, 0.35);
  }
  .spool-tag span { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .spool-tag svg { width: 9px; height: 9px; flex-shrink: 0; }
  .spool-body { display: flex; gap: 11px; align-items: flex-start; }
  .spool-swatch-col {
    display: flex; flex-direction: column; align-items: center; gap: 4px;
    flex-shrink: 0; padding-top: 1px;
  }
  .spool-swatch {
    width: 42px; height: 42px; border-radius: 50%; flex-shrink: 0;
    border: 2px solid rgba(255, 255, 255, 0.1);
    box-shadow: inset 0 0 0 1px rgba(0, 0, 0, 0.2);
  }
  .spool-rfid {
    display: flex; align-items: center; gap: 3px; flex-shrink: 0;
    padding: 2px 5px; border-radius: 5px; color: #3a3d42;
    background: linear-gradient(135deg, #f4f5f7 0%, #cdd1d6 35%, #8b9099 55%, #cdd1d6 75%, #f4f5f7 100%);
    border: 1px solid rgba(0, 0, 0, 0.25);
    box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.55), inset 0 -1px 0 rgba(0, 0, 0, 0.15), 0 1px 2px rgba(0, 0, 0, 0.25);
  }
  .spool-rfid span { font-size: 8px; font-weight: 800; letter-spacing: 0.04em; }
  .spool-rfid svg { width: 11px; height: 11px; flex-shrink: 0; }
  .spool-main { flex: 1; min-width: 0; }
  .spool-top { display: flex; align-items: baseline; justify-content: space-between; gap: 8px; }
  .spool-title {
    font-size: 14px; font-weight: 700; color: var(--orca-fg);
    overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
  }
  .spool-weight { font-size: 13px; font-weight: 400; color: var(--orca-fg); flex-shrink: 0; display: flex; align-items: center; gap: 6px; }
  .spool-cart {
    display: inline-flex; align-items: center; justify-content: center;
    padding: 2px 4px; cursor: pointer; border-radius: 5px; line-height: 0;
    background: transparent; color: #e0a030; border: 1px solid currentColor;
  }
  .spool-cart:hover { background: rgba(224, 160, 48, 0.18); }
  .spool-cart svg { width: 13px; height: 13px; }
  .spool-bar-track {
    height: 5px; border-radius: 3px; margin: 6px 0 5px;
    background: rgba(127, 127, 127, 0.25); overflow: hidden;
  }
  .spool-bar-fill { height: 100%; border-radius: 3px; }
  .spool-pct { font-size: 12px; color: var(--orca-muted); }
  .spool-weight.low .spool-pct { color: inherit; opacity: 0.8; }
  .spool-dup {
    margin-left: 8px; padding: 1px 8px; border-radius: 99px; vertical-align: middle;
    border: 1px solid var(--orca-border); color: var(--orca-muted);
    font-size: 11px; font-weight: 700;
  }
  .spool-subtitle {
    display: flex; align-items: center; justify-content: space-between; gap: 8px;
    font-size: 12px; color: var(--orca-muted); font-style: italic;
  }
  .sub-text { min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .plate-chip {
    flex: none; margin: 5px 0 4px; padding: 3px 11px; border-radius: 99px;
    border: 1px solid var(--orca-accent); font-size: 11px; font-weight: 700; font-style: normal;
    background: color-mix(in srgb, var(--orca-accent) 25%, var(--orca-bg) 75%);
    color: color-mix(in srgb, var(--orca-accent) 55%, var(--orca-fg) 45%);
  }

  .plate { margin: 6px 0 2px; color: var(--orca-fg); }
  .divider { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 10px; margin: 8px 0 4px; }
  .divider .line { flex: 1; height: 1px; min-width: 12px; background: var(--orca-border); }
  .divider-title { font-weight: 700; color: color-mix(in srgb, var(--orca-accent) 75%, var(--orca-fg) 25%); }
  .divider-sub { color: var(--orca-muted); font-size: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; min-width: 0; }
  .plate-pill { padding: 2px 10px; border-radius: 99px; font-size: 12px; font-weight: 700; white-space: nowrap; }
  .plate-pill.attention { background: rgba(210, 153, 34, 0.22); color: #e0a030; }
  .plate-pill.fine { background: rgba(63, 185, 80, 0.18); color: #3fb950; }
  #plate-recheck { background: var(--orca-accent); color: var(--orca-accent-fg); border-color: var(--orca-accent); }
  .plate-row { display: flex; flex-wrap: wrap; gap: 6px 11px; align-items: center; padding: 8px 15px; }
  .plate-who { flex: 1 1 200px; min-width: 0; }
  .plate-who .plate-name, .plate-who .plate-meta { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .plate-rows .plate-row + .plate-row { border-top: 1px solid var(--orca-border); }
  .plate-dot {
    flex: none; width: 16px; height: 16px; margin: 0 13px; border-radius: 50%;
    border: 2px solid rgba(255, 255, 255, 0.15); box-shadow: inset 0 0 0 1px rgba(0, 0, 0, 0.2);
  }
  .plate-name { font-weight: 700; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .plate-meta { color: var(--orca-muted); font-size: 12px; margin-top: 1px; }
  .plate-result { flex: 1.4 1 190px; text-align: right; min-width: 0; }
  .plate-headline { font-weight: 700; }
  .plate-bar { flex: 3 1 120px; position: relative; height: 8px; border-radius: 4px; background: rgba(127, 127, 127, 0.25); overflow: hidden; }
  .plate-bar .have { position: absolute; top: 0; bottom: 0; left: 0; }
  .plate-bar .need {
    position: absolute; top: 0; bottom: 0; left: 0;
    background: repeating-linear-gradient(45deg, rgba(255, 255, 255, 0.38) 0, rgba(255, 255, 255, 0.38) 3px, rgba(0, 0, 0, 0.38) 3px, rgba(0, 0, 0, 0.38) 6px);
  }
  .listbar { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-bottom: 8px; }
  .listbar #status { margin-bottom: 0; }
  .st-ok .plate-headline { color: #3fb950; }
  .st-barely .plate-headline, .st-mixed .plate-headline { color: #e0a030; }
  .st-short .plate-headline { color: #d9534f; }
  .st-unknown .plate-headline { color: var(--orca-muted); }

  .group { margin-bottom: 4px; }
  .group-card {
    display: flex; align-items: center; gap: 10px; cursor: pointer;
    background: var(--orca-border);
    background: color-mix(in srgb, var(--orca-fg) 8%, var(--orca-bg) 92%);
    border: 1px solid var(--orca-border);
    border-radius: 10px; padding: 8px 12px; margin-bottom: 10px;
  }
  .group-card .arrow { width: 12px; flex-shrink: 0; color: var(--orca-muted); }
  .group-card .group-info { flex: 1; min-width: 0; }
  .group-card .group-name { font-weight: 700; font-size: 13px; }
  .group-card .group-meta { color: var(--orca-muted); font-size: 11px; margin-top: 1px; }
  .group-card .group-bar { width: 90px; flex-shrink: 0; }
  .group-card .group-bar-track { height: 5px; border-radius: 3px; background: rgba(127, 127, 127, 0.25); overflow: hidden; }
  .group-card .group-bar-fill { height: 100%; border-radius: 3px; }
  .group-card .group-bar-fill.high { background: #3fb950; }
  .group-card .group-bar-fill.mid { background: #d29922; }
  .group-card .group-bar-fill.low { background: #d9534f; }
  .group-items { padding-left: 4px; }
  .group.collapsed .group-items { display: none; }
  #list.cols-2, #list.cols-2 .group-items { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); column-gap: 10px; align-items: start; }
  #list.cols-2 > .group, #list.cols-2 > .empty { grid-column: 1 / -1; }
  #list.cols-2 .group.collapsed .group-items { display: none; }
  @media (max-width: 640px) { #list.cols-2, #list.cols-2 .group-items { grid-template-columns: minmax(0, 1fr); } }
  .tabs { display: inline-flex; margin: 0 0 12px; border: 1px solid var(--orca-border); border-radius: 8px; overflow: hidden; }
  .tabs[hidden], #page-spools[hidden], #page-printer[hidden] { display: none; }
  .tabs button { background: transparent; color: var(--orca-fg); border: 0; border-right: 1px solid var(--orca-border); border-radius: 0; padding: 7px 20px; font-weight: 600; cursor: pointer; }
  .tabs button:last-child { border-right: 0; }
  .tabs button.on { background: var(--orca-accent); color: var(--orca-accent-fg); }
  #tab-dot { display: inline-block; width: 8px; height: 8px; margin-left: 7px; border-radius: 50%; background: #e0a030; }
  #tab-dot[hidden] { display: none; }
  .ams { margin: 0 0 14px; border: 1px solid var(--orca-border); border-radius: 10px; background: color-mix(in srgb, var(--orca-fg) 4%, var(--orca-bg) 96%); }
  .ams-h { color: var(--orca-fg); display: flex; align-items: baseline; gap: 10px; padding: 10px 14px; font-weight: 700; }
  .ams-h .sub { font-weight: 400; color: var(--orca-muted); font-size: 12px; }
  .ams-body { padding: 2px 14px 14px; }
  .ams-unit { display: flex; align-items: center; margin-top: 12px; font-size: 12px; color: var(--orca-muted); }
  .ams-h { flex-wrap: wrap; }
  .ams-h .bar { display: flex; flex-wrap: wrap; gap: 8px; margin-left: auto; }
  .sbtn { background: transparent; color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; padding: 5px 10px; font-size: 12px; font-weight: 600; cursor: pointer; }
  .sbtn:hover { border-color: var(--orca-accent); }
  .sbtn.armed { border-color: #d9534f; color: #d9534f; }
  .sbtn.ghost { border-color: transparent; font-weight: 400; color: var(--orca-muted); }
  .ams-unit .sbtn { margin-left: auto; }
  .pname { background: transparent; border: 0; padding: 0; color: var(--orca-fg); font: inherit; font-weight: 700; cursor: pointer; }
  .pname-in { background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-accent); border-radius: 6px; padding: 3px 8px; font: inherit; font-weight: 700; width: 180px; }
  .addp { margin-top: 2px; }
  .ams-assign { cursor: pointer; opacity: 1; }
  .ams-assign:hover { border-color: var(--orca-accent); }
  .ams-x { position: absolute; top: -10px; right: 34px; z-index: 3; width: 18px; height: 18px; padding: 0; border: 0; border-radius: 50%; background: #555a5f; color: #fff; font-size: 10px; line-height: 18px; text-align: center; cursor: pointer; }
  .ams-x:hover { background: #d9534f; }
  .picker { position: absolute; z-index: 20; top: 100%; left: 0; margin-top: 6px; width: min(340px, 90vw); background: var(--orca-bg); border: 1px solid var(--orca-border); border-radius: 10px; box-shadow: 0 10px 30px rgba(0, 0, 0, 0.45); padding: 10px; }
  .ams-cell:nth-child(4n) .picker { left: auto; right: 0; }
  .picker input { width: 100%; box-sizing: border-box; margin-bottom: 6px; background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; padding: 8px 10px; font: inherit; font-size: 13px; }
  .picker input:focus { outline: none; border-color: var(--orca-accent); }
  .pick-list { max-height: 280px; overflow-y: auto; }
  .pi { display: flex; align-items: center; gap: 10px; padding: 7px 8px; border-radius: 6px; color: var(--orca-fg); font-size: 13px; cursor: pointer; }
  .pi:hover { background: color-mix(in srgb, var(--orca-accent) 35%, transparent); }
  .pi .d { width: 18px; height: 18px; border-radius: 50%; border: 2px solid rgba(255, 255, 255, 0.25); flex: none; }
  .pi .m { margin-left: auto; color: var(--orca-muted); font-size: 12px; white-space: nowrap; }
  .pi small { display: block; color: var(--orca-muted); font-size: 11px; }
  .pnote { padding: 8px; font-size: 12px; color: var(--orca-muted); }
  .ams-grid { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 22px 10px; margin-top: 20px; }
  .ams-cell { position: relative; display: flex; }
  .ams-cell .spool-card { flex: 1; margin: 0; box-sizing: border-box; min-width: 0; }
  .ams-n { position: absolute; top: -10px; right: 10px; z-index: 2; min-width: 18px; height: 18px; line-height: 18px; text-align: center; border-radius: 9px; background: var(--orca-accent); color: var(--orca-accent-fg); font-size: 11px; font-weight: 800; }
  .ams-empty { border-style: dashed; opacity: 0.7; }
  .ams-dash { background: transparent !important; border: 2px dashed var(--orca-border) !important; box-shadow: none !important; }
  .ams-note { margin-top: 12px; font-size: 12px; color: var(--orca-muted); }
  .plate.on-printer > .divider:last-child { display: none; }
  .live-dot { display: inline-block; width: 8px; height: 8px; margin-right: 6px; border-radius: 50%; background: #3fb950; }
  .live-dot.stale { background: #e0a030; }
  .usage { margin: 0 0 14px; border: 1px solid var(--orca-border); border-radius: 10px; background: color-mix(in srgb, var(--orca-fg) 4%, var(--orca-bg) 96%); }
  .usage-bar { display: flex; flex-wrap: wrap; align-items: center; gap: 8px 14px; padding: 10px 14px; color: var(--orca-fg); }
  .usage-bar b { font-weight: 700; }
  .usage-bar .sub { color: var(--orca-muted); font-size: 12px; margin-right: auto; }
  .usage select, .u-spool select { background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; padding: 5px 8px; font: inherit; font-size: 13px; max-width: 100%; }
  .u-card { border: 1px solid var(--orca-border); border-radius: 14px; background: color-mix(in srgb, var(--orca-fg) 5%, var(--orca-bg) 95%); padding: 12px 14px; }
  .u-h { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 10px; color: var(--orca-fg); margin-bottom: 6px; }
  .u-h .sub { color: var(--orca-muted); font-size: 12px; margin-right: auto; }
  .u-h .u-chip { margin-left: 0; }
  .u-row { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 12px; padding: 6px 0; color: var(--orca-fg); }
  .u-row .d { width: 14px; height: 14px; border-radius: 50%; border: 2px solid rgba(255, 255, 255, 0.15); flex: none; }
  .u-slot { color: var(--orca-muted); min-width: 110px; }
  .u-spool { flex: 1 1 220px; min-width: 0; }
  .u-g { width: 74px; background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; padding: 5px 8px; font: inherit; font-size: 13px; }
  .u-chip { margin-left: 8px; font-size: 11px; font-weight: 700; padding: 2px 8px; border-radius: 99px; background: rgba(63, 185, 80, 0.18); color: #3fb950; }
  .u-chip.warn { background: rgba(210, 153, 34, 0.22); color: #e0a030; }
  .u-chip.off { background: color-mix(in srgb, var(--orca-fg) 12%, transparent); color: var(--orca-muted); }
  .u-err { flex-basis: 100%; color: #d9534f; font-size: 12px; }
  .u-amt { color: var(--orca-muted); white-space: nowrap; }
  .u-card.undone .u-row { color: var(--orca-muted); }
  .u-card.undone .u-spool, .u-card.undone .u-amt { text-decoration: line-through; }
  .rb-h { display: flex; align-items: center; gap: 10px; padding: 10px 14px; border-top: 1px solid var(--orca-border); color: var(--orca-fg); cursor: pointer; user-select: none; }
  .rb-h .arrow { width: 12px; color: var(--orca-muted); }
  .rb-h .sub { color: var(--orca-muted); font-size: 12px; margin-right: auto; }
  .rb-h .u-chip { margin-left: 0; }
  .rb-list { display: flex; flex-direction: column; gap: 10px; padding: 0 14px 14px; }
  .rb-mask { position: fixed; inset: 0; z-index: 200; display: flex; align-items: center; justify-content: center; padding: 16px; background: rgba(0, 0, 0, 0.55); }
  .rb-pop { width: min(460px, 100%); box-sizing: border-box; background: var(--orca-bg); border: 1px solid var(--orca-border); border-radius: 10px; box-shadow: 0 10px 30px rgba(0, 0, 0, 0.45); padding: 16px; color: var(--orca-fg); font-size: 13px; }
  .rb-pop b.t { display: block; font-size: 15px; margin-bottom: 6px; }
  .rb-pop .sub { color: var(--orca-muted); font-size: 12px; }
  .rb-tbl { margin: 12px 0; border: 1px solid var(--orca-border); border-radius: 8px; }
  .rb-sp { padding: 8px 12px; }
  .rb-sp + .rb-sp { border-top: 1px solid var(--orca-border); }
  .rb-sp .n { display: flex; align-items: center; gap: 8px; font-weight: 700; margin-bottom: 4px; }
  .rb-sp .d { width: 12px; height: 12px; border-radius: 50%; border: 2px solid rgba(255, 255, 255, 0.15); flex: none; }
  .rb-sp .w { display: flex; gap: 6px; color: var(--orca-muted); font-size: 12px; padding-left: 22px; }
  .rb-sp .w b { color: #3fb950; }
  .rb-bar { display: flex; justify-content: flex-end; gap: 8px; margin-top: 14px; }
  #usage-slot:empty, #progress-slot:empty { display: none; }
  #usage-slot { margin-top: 14px; }
  .prog { margin: 0 0 14px; border: 1px solid var(--orca-border); border-radius: 10px; background: color-mix(in srgb, var(--orca-fg) 4%, var(--orca-bg) 96%); font-size: 11px; }
  .prog b, .pj-name { font-size: 13px; }
  .prog-h { display: flex; align-items: baseline; gap: 10px; padding: 10px 14px 0; color: var(--orca-fg); }
  .prog-h .sub, .pj-idle .sub { color: var(--orca-muted); }
  .pj { padding: 12px 14px 13px; color: var(--orca-fg); }
  .pj + .pj, .pj + .pj-idle, .pj-idle + .pj-idle { border-top: 1px solid var(--orca-border); }
  .pj-top { display: flex; align-items: center; gap: 10px; }
  .pj-name { font-weight: 700; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .pj-who { color: var(--orca-muted); white-space: nowrap; }
  .pj-chip { font-weight: 700; padding: 2px 8px; border-radius: 99px; white-space: nowrap; background: color-mix(in srgb, var(--orca-accent) 22%, transparent); color: #3cc9b9; }
  .pj-chip.warn { background: rgba(210, 153, 34, 0.22); color: #e0a030; }
  .pj-chip.ok { background: rgba(63, 185, 80, 0.18); color: #3fb950; }
  .pj-chip.bad { background: rgba(217, 83, 79, 0.2); color: #e5605c; }
  .pj-chip.idle { background: rgba(127, 127, 127, 0.2); color: var(--orca-muted); }
  .pj-pct { margin-left: auto; font-size: 18px; font-weight: 800; font-variant-numeric: tabular-nums; }
  .pj-track { height: 10px; margin: 9px 0 8px; border-radius: 5px; background: rgba(127, 127, 127, 0.25); overflow: hidden; }
  .pj-fill { height: 100%; border-radius: 5px; background: var(--orca-accent); }
  .pj-fill.warn { background: #d29922; }
  .pj-fill.ok { background: #3fb950; }
  .pj-fill.bad { background: #d9534f; }
  .pj-fill.prep { width: 30% !important; background: repeating-linear-gradient(-45deg, var(--orca-accent) 0 8px, color-mix(in srgb, var(--orca-accent) 55%, transparent) 8px 16px); animation: pj-prep 1.6s linear infinite; }
  @keyframes pj-prep { from { margin-left: -30%; } to { margin-left: 100%; } }
  .pj-meta { display: flex; flex-wrap: wrap; gap: 4px 16px; color: var(--orca-muted); }
  .pj-meta b { color: var(--orca-fg); font-weight: 600; font-size: 11px; }
  .pj-slot { display: inline-flex; align-items: center; gap: 6px; }
  .pj-slot .d { width: 10px; height: 10px; border-radius: 50%; border: 2px solid rgba(255, 255, 255, 0.18); }
  .pj-idle { display: flex; align-items: center; gap: 10px; padding: 10px 14px; color: var(--orca-fg); }
  .pj-idle .pj-who { margin-left: auto; }
  .ams-cell.active .spool-card { border-color: var(--orca-accent) !important; box-shadow: 0 0 0 1px var(--orca-accent); }
  .linkform { display: flex; flex-wrap: wrap; align-items: flex-end; gap: 10px 12px; padding: 12px 14px; border-bottom: 1px solid var(--orca-border); }
  .linkform label { display: flex; flex-direction: column; gap: 4px; flex: 1 1 180px; font-size: 12px; color: var(--orca-muted); }
  .linkform input { background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; padding: 8px 10px; font: inherit; font-size: 13px; }
  .linkform input:focus { outline: none; border-color: var(--orca-accent); }
  .linkform .bar { display: flex; gap: 8px; }
  .sbtn.primary, .sbtn.primary:hover { background: var(--orca-accent); color: var(--orca-accent-fg); border-color: var(--orca-accent); }
  @media (max-width: 760px) { .ams-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
</style>
</head>
<body>
  <!--header--><div class="header">
    <div class="title">__LOGO__<h2>__PLUGIN_NAME__</h2></div>
    <div class="header-actions">
      <button id="settings-btn" title="Settings &amp; about">Settings</button>
    </div>
  </div><!--/header-->
  <div id="tabs" class="tabs">
    <button data-tab="spools" class="on">Spools</button>
    <button data-tab="printer">Printer<span id="tab-dot" hidden></span></button>
  </div>
  <div id="page-spools">
  <div class="listbar">
    <div id="status">Loading...</div>
    <button id="send-btn" title="Send the unsaved changes of the Spooler preset open in OrcaSlicer's filament settings to Spoolman">Send to Spoolman</button>
    <button id="filters-toggle" aria-expanded="false">Filters &#9662;</button>
  </div>
  <div id="filters-panel" hidden>
  <div class="filters">
    <input id="search" type="text" placeholder="Filter by name...">
    <select id="material-filter"><option value="">All Materials</option></select>
    <select id="vendor-filter"><option value="">All Manufacturers</option></select>
  </div>
  <div class="filters">
    <select id="group-key">
      <option value="none">Group: None</option>
      <option value="location">Group: Location</option>
      <option value="material">Group: Material</option>
      <option value="vendor">Group: Manufacturer</option>
    </select>
    <select id="sort-key">
      <option value="name">Sort: Name</option>
      <option value="material">Sort: Material</option>
      <option value="vendor">Sort: Manufacturer</option>
      <option value="remaining" selected>Sort: Remaining Weight</option>
      <option value="used">Sort: Used Weight</option>
      <option value="first_used">Sort: First Used</option>
      <option value="last_used">Sort: Last Used</option>
      <option value="plate" disabled>Sort: On This Plate</option>
    </select>
    <button class="sort-dir" id="sort-dir" title="Toggle ascending/descending">&#9650;</button>
  </div>
  </div>

  <div id="plate" class="plate" hidden>
    <div class="divider">
      <span class="line"></span>
      <span class="divider-title">⚖️ This Plate</span>
      <span class="divider-sub" id="plate-sub"></span>
      <span class="line"></span>
      <span class="plate-pill" id="plate-pill"></span>
      <button id="plate-recheck" title="Check again against your spool source">Re-check</button>
      <button id="plate-dismiss" title="Hide until the next slice">Dismiss</button>
    </div>
    <div class="plate-rows" id="plate-rows"></div>
    <div class="divider"><span class="line"></span><span class="divider-title">All Spools</span><span class="line"></span></div>
  </div>

  <div id="list"></div>
  </div>
  <div id="page-printer" hidden>
    <div id="progress-slot"></div>
    <div id="ams-list"></div>
    <div id="plate-slot"></div>
    <div id="usage-slot"></div>
  </div>

  <script>
    const statusEl = document.getElementById("status");
    let profileNote = {};
    const listEl = document.getElementById("list");
    const searchEl = document.getElementById("search");
    const materialEl = document.getElementById("material-filter");
    const vendorEl = document.getElementById("vendor-filter");
    const groupKeyEl = document.getElementById("group-key");
    const sortKeyEl = document.getElementById("sort-key");
    const sortDirBtn = document.getElementById("sort-dir");
    const fToggle = document.getElementById("filters-toggle");
    const fPanel = document.getElementById("filters-panel");
    const plateEl = document.getElementById("plate");
    const plateList = document.getElementById("plate-rows");
    const plateSort = sortKeyEl.querySelector('option[value="plate"]');

    let allSpools = [];
    let lowStockGrams = __LOW_STOCK_DEFAULT__;
    let wMode = "both";
    let cart = false;
    let sortDir = "asc";
    let plate = null;
    let plateSlots = new Map();
    let plateOrder = new Map();
    let dupes = new Map();
    let lastSort = sortKeyEl.value;
    const tabsEl = document.getElementById("tabs");
    const tabDot = document.getElementById("tab-dot");
    const amsList = document.getElementById("ams-list");
    const plateSlot = document.getElementById("plate-slot");
    let tab = "spools";
    let linked = [];
    let cfg = [];
    let showTab = true;
    let armed = "";
    let renaming = "";
    let liveOn = false;
    let usage = { enabled: false, mode: "ask", prints: [] };
    let usageEdits = {};
    let usageBooking = false;
    let usageUndoing = false;
    let rbUndo = null;
    let rbOpen = false;
    try { rbOpen = localStorage.getItem("spooler.bookings") === "1"; } catch (err) {}
    let plateAttn = false;
    const usageSlot = document.getElementById("usage-slot");
    const progSlot = document.getElementById("progress-slot");
    let progress = { on: true, finish: true, slot: true, idle: "line" };
    let linkOpen = "";
    let liveData = { status: "off", printers: [] };
    let liveKey = "";
    let picking = null;
    const KINDS = { ams: 4, ht: 1, ext: 1 };
    const RANK = { ams: 0, ht: 1, ext: 2 };
    try { if (localStorage.getItem("spooler.tab") === "printer") tab = "printer"; } catch (err) {}

    function esc(v) {
      return String(v).replace(/[&<>"]/g, function (c) {
        return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c];
      });
    }

    function swatchHex(v) {
      const m = String(v || "").trim().replace(/^#/, "").match(/^[0-9a-f]{6}/i);
      return m ? "#" + m[0] : "";
    }

    function swatchCols(f) {
      return String(f.multi_color_hexes || "").split(",").map(swatchHex).filter(Boolean);
    }

    // One solid colour for the ring and bar; the first colour on multi-colour spools.
    function swatchMain(f) {
      const cs = swatchCols(f);
      return (cs.length < 2 && swatchHex(f.color_hex)) || cs[0] || "#888";
    }

    function swatch(f) {
      const cs = swatchCols(f);
      if (cs.length < 2) return swatchMain(f);
      if (f.multi_color_direction === "longitudinal") return "linear-gradient(135deg, " + cs.join(", ") + ")";
      const step = 360 / cs.length;
      return "conic-gradient(" + cs.map(function (c, i) {
        return c + " " + i * step + "deg " + (i + 1) * step + "deg";
      }).join(", ") + ")";
    }

    function savePrinters() {
      orca.postMessage({ type: "printers", printers: cfg });
    }

    function buildPrinters() {
      const byName = new Map();
      allSpools.forEach(function (s) {
        const a = s.ams;
        if (!a || s.archived) return;
        const name = a.printer || "Printer";
        if (!byName.has(name)) byName.set(name, new Map());
        const units = byName.get(name);
        const unit = Number(a.unit);
        const key = unit >= 128 ? "ext" : (Number.isFinite(unit) ? unit : 0);
        if (!units.has(key)) units.set(key, new Map());
        units.get(key).set(key === "ext" ? 0 : Number(a.slot), s);
      });
      linked = [...byName.entries()].map(function (e) {
        const units = [...e[1].entries()].sort(function (x, y) {
          return (x[0] === "ext" ? 999 : x[0]) - (y[0] === "ext" ? 999 : y[0]);
        });
        return { name: e[0], units: units };
      });
    }

    function plainCard(title, sub, attrs, cls) {
      return '<div class="spool-card ' + cls + '"' + attrs + '><div class="spool-body">' +
        '<div class="spool-swatch-col"><div class="spool-swatch ams-dash"></div></div>' +
        '<div class="spool-main"><div class="spool-top"><div class="spool-title">' + title + '</div></div>' +
        '<div class="spool-bar-track"></div>' +
        '<div class="spool-subtitle"><span class="sub-text">' + sub + '</span></div></div>' +
        '</div></div>';
    }

    function amsCellHtml(label, s) {
      const card = s ? spoolRowHtml(s) : plainCard("Empty", "No spool linked", "", "ams-empty");
      return '<div class="ams-cell"><div class="ams-n">' + label + '</div>' + card + '</div>';
    }

    function syncDot() {
      tabDot.hidden = !(plateAttn || (usage.enabled && usage.prints.some(function (p) { return p.state === "pending"; })));
    }

    function usageTime(t) {
      return new Date(t * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
    }

    function usageGrams(g) {
      return (Math.round(g * 10) / 10) + " g";
    }

    function spoolOptions(row) {
      const mat = String(row.material || "").toLowerCase();
      const list = allSpools.filter(function (s) { return !s.archived; }).sort(function (x, y) {
        const mx = String((x.filament || {}).material || "").toLowerCase() === mat ? 0 : 1;
        const my = String((y.filament || {}).material || "").toLowerCase() === mat ? 0 : 1;
        return mx - my || ((x.filament || {}).name || "").localeCompare((y.filament || {}).name || "");
      }).slice(0, 300);
      return '<option value="">Choose a Spool...</option>' + list.map(function (s) {
        const f = s.filament || {};
        const label = [(f.vendor || {}).name, f.name || "Spool " + s.id, "#" + s.id, formatWeight(s.remaining_weight)].filter(Boolean).join(" \u00b7 ");
        return '<option value="' + esc(s.id) + '">' + esc(label) + '</option>';
      }).join("");
    }

    function usageRow(e, r) {
      const edit = (usageEdits[e.id] || {})[r.slot] || {};
      const grams = edit.grams !== undefined ? edit.grams : r.grams;
      const colour = r.colour ? "#" + String(r.colour).replace(/^#/, "") : "#888";
      let who;
      if (r.state === "booked") {
        who = esc(r.label) + '<span class="u-chip">Booked ' + usageGrams(r.grams) + '</span>';
      } else if (r.spool) {
        who = esc(r.label) + (r.how === "rfid" ? '<span class="u-chip">Matched by RFID</span>' : "");
      } else {
        who = '<select data-usage="spool">' + spoolOptions(r).replace('value="' + esc(edit.spool || "") + '"', 'value="' + esc(edit.spool || "") + '" selected') + '</select>' +
          '<span class="u-chip warn">Not Identified</span>';
      }
      const input = r.state === "booked" ? "" : '<input class="u-g" data-usage="grams" type="number" min="0" step="0.1" value="' + esc(grams) + '"> g';
      return '<div class="u-row" data-slot="' + r.slot + '"><span class="d" style="background:' + esc(colour) + '"></span>' +
        '<span class="u-slot">Slot ' + r.slot + (r.material ? " \u00b7 " + esc(r.material) : "") + '</span>' +
        '<span class="u-spool">' + who + '</span>' + input +
        (r.error ? '<div class="u-err">' + esc(r.error) + '</div>' : "") + '</div>';
    }

    function rbWhen(t) {
      const d = new Date(t * 1000);
      const hm = usageTime(t);
      const days = Math.round((new Date(new Date().toDateString()) - new Date(d.toDateString())) / 864e5);
      return days === 0 ? "Today " + hm : days === 1 ? "Yesterday " + hm :
        d.getDate() + " " + d.toLocaleString("en-GB", { month: "short" }) + " " + hm;
    }

    function rbTotal(p) {
      return p.rows.reduce(function (a, r) { return a + r.grams; }, 0);
    }

    function rbCard(p) {
      const result = p.result === "finished" ? "Finished" : p.result === "unknown" ? "Result Unknown" : "Stopped at " + p.pct + "%";
      const chip = p.state === "booked" ? '<span class="u-chip">Booked ' + usageGrams(rbTotal(p)) + '</span>' :
        p.state === "undone" ? '<span class="u-chip off">Undone</span>' : '<span class="u-chip warn">Not Booked</span>';
      const busy = usageBooking || usageUndoing;
      const btn = p.state === "booked" ? '<button class="sbtn" data-usage="undo"' + (busy ? " disabled" : "") + '>Undo</button>' :
        '<button class="sbtn primary" data-usage="book"' + (busy ? " disabled" : "") + '>' + (usageBooking === p.id ? "Booking..." : "Book") + '</button>';
      const rows = p.state === "pending" ? p.rows.map(function (r) { return usageRow(p, r); }).join("") :
        p.rows.map(function (r) {
          const colour = r.colour ? "#" + String(r.colour).replace(/^#/, "") : "#888";
          return '<div class="u-row"><span class="d" style="background:' + esc(colour) + '"></span>' +
            '<span class="u-slot">Slot ' + r.slot + (r.material ? " · " + esc(r.material) : "") + '</span>' +
            '<span class="u-spool">' + esc(r.label) + '</span><span class="u-amt">' + usageGrams(r.grams) + '</span>' +
            (r.error ? '<div class="u-err">' + esc(r.error) + '</div>' : "") + '</div>';
        }).join("");
      const note = p.state !== "pending" ? "" :
        p.late ? "Spooler lost contact with the printer during this print, so check the grams before booking." :
        p.result === "finished" ? "" : "The print did not finish, so the grams are an estimate from its progress.";
      return '<div class="u-card' + (p.state === "undone" ? " undone" : "") + '" data-run="' + esc(p.id) + '"><div class="u-h"><b>' + esc(p.name) + '</b>' +
        '<span class="sub">' + esc(p.printer) + ' · ' + result + ' · ' + rbWhen(p.time) + '</span>' + chip + btn + '</div>' + rows +
        (note ? '<div class="ams-note" style="margin: 6px 0 0">' + note + '</div>' : "") + '</div>';
    }

    function rbPop() {
      const p = usage.prints.find(function (x) { return x.id === rbUndo; });
      if (!p) return "";
      const rows = p.rows.filter(function (r) { return r.state === "booked"; });
      const spools = rows.map(function (r) {
        const s = allSpools.find(function (x) { return x.id === r.spool; }) || {};
        const left = s.remaining_weight || 0;
        const colour = r.colour ? "#" + String(r.colour).replace(/^#/, "") : "#888";
        return '<div class="rb-sp"><div class="n"><span class="d" style="background:' + esc(colour) + '"></span>' + esc(r.label) + '</div>' +
          '<div class="w">' + usageGrams(left) + ' + ' + usageGrams(r.grams) + ' = <b>' + usageGrams(left + r.grams) + '</b></div></div>';
      }).join("");
      const many = rows.length > 1;
      return '<div class="rb-mask" data-usage="cancel"><div class="rb-pop"><b class="t">Undo This Booking?</b>' +
        '<div>' + esc(p.name) + ' used ' + usageGrams(rbTotal({ rows: rows })) + (many ? ' from ' + rows.length + ' spools' : '') +
        '. Spooler will add it back to ' + (many ? 'each spool' : 'the spool') + ' in Spoolman.</div>' +
        '<div class="rb-tbl">' + spools + '</div>' +
        '<div class="sub">The print stays in Recent Bookings, so you can book it again later.</div>' +
        '<div class="rb-bar"><button class="sbtn ghost" data-usage="cancel">Cancel</button><button class="sbtn primary" data-usage="unbook"' +
        (usageUndoing ? " disabled" : "") + '>' + (usageUndoing ? "Adding Back..." : "Add Back to Spoolman") + '</button></div></div></div>';
    }

    function renderUsage() {
      syncDot();
      if (!usage.enabled || (!liveOn && !usage.prints.length)) { usageSlot.innerHTML = ""; return; }
      const mode = '<label>When a Print Finishes <select data-usage="mode">' + [["ask", "Ask Me Before Booking"], ["auto", "Book Automatically"], ["off", "Do Not Track"]].map(function (m) {
        return '<option value="' + m[0] + '"' + (usage.mode === m[0] ? " selected" : "") + '>' + m[1] + '</option>';
      }).join("") + '</select></label>';
      const list = usage.prints.slice(0, 5);
      const todo = list.filter(function (p) { return p.state === "pending"; }).length;
      const head = list.length ? '<div class="rb-h" data-usage="toggle"><span class="arrow">' + (rbOpen ? "▾" : "▸") + '</span><b>Recent Bookings</b>' +
        '<span class="sub">Last ' + list.length + (list.length === 1 ? ' Print' : ' Prints') + '</span>' +
        (todo ? '<span class="u-chip warn">' + todo + ' To Book</span>' : "") + '</div>' : "";
      const body = list.length && rbOpen ? '<div class="rb-list">' + list.map(rbCard).join("") + '</div>' : "";
      usageSlot.innerHTML = '<div class="usage"><div class="usage-bar"><b>Filament Usage</b><span class="sub"></span>' + mode + '</div>' +
        head + body + '</div>' + (rbUndo ? rbPop() : "");
    }

    function setUsage(u, done) {
      usage = u;
      Object.keys(usageEdits).forEach(function (id) {
        if (!usage.prints.some(function (e) { return e.id === id && e.state === "pending"; })) delete usageEdits[id];
      });
      if (done && (usageBooking || usageUndoing)) {
        usageBooking = false;
        if (usageUndoing) { usageUndoing = false; rbUndo = null; }
        orca.postMessage({ type: "refresh" });
      }
      const at = document.activeElement;
      if (at && usageSlot.contains(at) && at.matches('[data-usage="spool"], [data-usage="grams"]')) syncDot(); else renderUsage();
    }

    usageSlot.addEventListener("change", function (e) {
      const kind = e.target.dataset.usage;
      const card = e.target.closest(".u-card");
      const row = e.target.closest(".u-row");
      if (kind === "mode") {
        usage.mode = e.target.value;
        orca.postMessage({ type: "usage_mode", mode: e.target.value });
      } else if (kind === "spool" && card && row) {
        const ed = usageEdits[card.dataset.run] = usageEdits[card.dataset.run] || {};
        (ed[row.dataset.slot] = ed[row.dataset.slot] || {}).spool = e.target.value;
      }
    });

    usageSlot.addEventListener("input", function (e) {
      const card = e.target.closest(".u-card");
      const row = e.target.closest(".u-row");
      if (e.target.dataset.usage === "grams" && card && row) {
        const ed = usageEdits[card.dataset.run] = usageEdits[card.dataset.run] || {};
        (ed[row.dataset.slot] = ed[row.dataset.slot] || {}).grams = e.target.value;
      }
    });

    usageSlot.addEventListener("click", function (e) {
      const btn = e.target.closest("[data-usage]");
      if (!btn || btn.disabled) return;
      const kind = btn.dataset.usage;
      const card = e.target.closest(".u-card");
      if (kind === "toggle") {
        rbOpen = !rbOpen;
        try { localStorage.setItem("spooler.bookings", rbOpen ? "1" : "0"); } catch (err) {}
      } else if (kind === "cancel") {
        if (e.target !== btn || usageUndoing) return;
        rbUndo = null;
      } else if (kind === "undo" && card) {
        rbUndo = card.dataset.run;
      } else if (kind === "unbook" && rbUndo && !usageUndoing) {
        usageUndoing = true;
        orca.postMessage({ type: "usage_undo", run: rbUndo });
      } else if (kind === "book" && card && !usageBooking) {
        const rows = [...card.querySelectorAll(".u-row")].map(function (row) {
          const sel = row.querySelector('select[data-usage="spool"]');
          const g = row.querySelector('input[data-usage="grams"]');
          if (!g) return null;
          const out = { slot: Number(row.dataset.slot), grams: Number(g.value) };
          if (sel && sel.value) out.spool = sel.value;
          return out;
        }).filter(Boolean);
        usageBooking = card.dataset.run;
        orca.postMessage({ type: "usage_book", run: card.dataset.run, rows: rows });
      } else {
        return;
      }
      renderUsage();
    });

    function liveByLink(id) {
      return liveData.printers.find(function (x) { return x.link === id; }) || null;
    }

    function linkStatus(p) {
      if (!p.ip || !p.has_code) return "";
      const lv = liveByLink(p.id);
      const st = (liveData.links || {})[p.id];
      if (lv && st === "live") {
        return '<span class="live-dot' + (lv.age > 180 ? " stale" : "") + '"></span>Live';
      }
      if (st === "auth") return "Wrong access code";
      if (st === "unreachable") return "Can't reach " + esc(p.ip) + " - is the printer on and in LAN mode?";
      if (st === "waiting") return "Connected, waiting for the printer to report";
      return "Connecting to " + esc(p.ip) + "...";
    }

    function linkForm(p) {
      return '<div class="linkform">' +
        '<label>IP Address<input data-f="ip" value="' + esc(p.ip || "") + '" placeholder="192.168.1.50" autocomplete="off"></label>' +
        '<label>Serial Number<input data-f="serial" value="' + esc(p.serial || "") + '" placeholder="Optional" autocomplete="off"></label>' +
        '<label>Access Code<input data-f="code" type="password" autocomplete="off" placeholder="' + (p.has_code ? "Saved - leave blank to keep" : "Shown on the printer") + '"></label>' +
        '<div class="bar"><button class="sbtn" data-act="link-save" data-p="' + esc(p.id) + '">Save</button>' +
        '<button class="sbtn ghost" data-act="link-cancel" data-p="' + esc(p.id) + '">Cancel</button>' +
        (p.ip ? '<button class="sbtn ghost" data-act="link-remove" data-p="' + esc(p.id) + '">Remove Link</button>' : "") + '</div>' +
        '<div class="ams-note" style="flex-basis: 100%; margin: 0">The IP address and access code are in the printer&#39;s network settings, with LAN mode on. ' +
        'Spooler keeps the access code on this computer and only reads from the printer.</div></div>';
    }

    function liveCard(t) {
      if (t.empty) return plainCard("Empty", "Nothing loaded", "", "ams-empty");
      const color = t.colour ? "#" + t.colour : "#888";
      const pct = t.remain === null ? null : Math.round(t.remain);
      const profile = (t.profile || "").split("/").pop();
      const sub = [t.type, t.colour ? "#" + t.colour : ""].filter(Boolean).join(" \u00b7 ");
      const rfid = t.rfid ? '<div class="spool-rfid" title="RFID spool"><span>RFID</span></div>' : "";
      const tip = profile ? ' title="OrcaSlicer preset: ' + esc(profile) + '"' : "";
      return '<div class="spool-card"' + tip + '><div class="spool-body">' +
        '<div class="spool-swatch-col"><div class="spool-swatch" style="background:' + color + '"></div>' + rfid + '</div>' +
        '<div class="spool-main"><div class="spool-top"><div class="spool-title">' + esc(t.name || t.type) + '</div>' +
        '<div class="spool-weight">' + (pct === null ? "" : pct + "%") + '</div></div>' +
        '<div class="spool-bar-track" title="' + (pct === null ? "Remaining unknown" : pct + "% remaining") + '">' +
        '<div class="spool-bar-fill" style="width:' + (pct === null ? 0 : pct) + '%;background:' + color + '"></div></div>' +
        '<div class="spool-subtitle"><span class="sub-text">' + esc(sub) + '</span></div></div></div></div>';
    }

    const PROG_STATES = {
      RUNNING: ["Printing", "", ""], PREPARE: ["Preparing", "", "prep"], SLICING: ["Preparing", "", "prep"],
      PAUSE: ["Paused", "warn", "warn"], FINISH: ["Finished", "ok", "ok"], FAILED: ["Failed", "bad", "bad"]
    };
    const PROG_LIVE = ["RUNNING", "PREPARE", "SLICING", "PAUSE"];

    function activeTray(lv) {
      const j = lv.job;
      return progress.on && progress.slot && j && j.tray && PROG_LIVE.indexOf(j.state) >= 0 ? j.tray : null;
    }

    function liveUnits(lv) {
      let ams = 0;
      const act = activeTray(lv);
      const unitHtml = function (label, trays, ext, uid) {
        return '<div class="ams-unit">' + label + '</div><div class="ams-grid">' + trays.map(function (t, i) {
          const on = act && act.unit === uid && act.slot === i;
          return '<div class="ams-cell' + (on ? " active" : "") + '"><div class="ams-n">' + (ext ? "E" : i + 1) + '</div>' + liveCard(t) + '</div>';
        }).join("") + '</div>';
      };
      if (lv.heads) {
        return lv.units.map(function (u) { return unitHtml("Toolheads", u.trays, false, u.id); }).join("") ||
          '<div class="pnote">Waiting for the printer to report its toolheads...</div>';
      }
      let units = lv.units.map(function (u) {
        if (u.kind === "ht") return unitHtml("AMS HT", u.trays, false, u.id);
        ams += 1;
        const name = lv.unit_label || "AMS";
        return unitHtml(lv.unit_label && lv.units.length === 1 ? name : name + " " + ams, u.trays, false, u.id);
      }).join("");
      if (lv.ext) units += unitHtml("External Spool", [lv.ext], true, "ext");
      return units || '<div class="pnote">Waiting for the printer to report its slots...</div>';
    }

    function linkedPanel(p) {
      let count = 0;
      const units = p.units.map(function (u) {
        const ext = u[0] === "ext";
        count += u[1].size;
        const top = Math.max(3, ...[...u[1].keys()].filter(Number.isFinite));
        const slots = ext ? [0] : Array.from({ length: top + 1 }, function (_, i) { return i; });
        return '<div class="ams-unit">' + (ext ? "External Spool" : "AMS " + (u[0] + 1)) + '</div>' +
          '<div class="ams-grid">' + slots.map(function (i) {
            return amsCellHtml(ext ? "E" : i + 1, u[1].get(i));
          }).join("") + '</div>';
      }).join("");
      return '<div class="ams"><div class="ams-h"><span>' + esc(p.name) + '</span>' +
        '<span class="sub">' + count + (count === 1 ? " spool" : " spools") + ' linked from Bambu Cloud</span></div>' +
        '<div class="ams-body">' + units +
        '<div class="ams-note">A representative view only, built from Bambu Cloud. ' +
        'It can differ from what is physically loaded.</div></div></div>';
    }

    function unitLabel(p, u) {
      const same = p.units.filter(function (x) { return x.kind === u.kind; });
      const n = same.indexOf(u) + 1;
      if (u.kind === "ams") return "AMS " + n;
      if (u.kind === "ht") return same.length > 1 ? "AMS HT " + n : "AMS HT";
      return "External Spool";
    }

    function manualCell(p, ui, si, byId) {
      const u = p.units[ui];
      const id = u.slots[si];
      const s = id ? byId.get(String(id)) : null;
      const where = ' data-p="' + esc(p.id) + '" data-u="' + ui + '" data-s="' + si + '"';
      let card;
      if (s) {
        card = spoolRowHtml(s);
      } else if (id) {
        card = plainCard("Spool not found", "It may have been deleted or archived", "", "ams-empty");
      } else {
        card = plainCard("+ Assign Spool", "No spool assigned", ' data-act="assign"' + where, "ams-empty ams-assign");
      }
      const x = id ? '<button class="ams-x" data-act="clear"' + where + ' title="Remove from slot">\u2715</button>' : "";
      const open = picking && picking.p === p.id && picking.u === ui && picking.s === si && !id;
      return '<div class="ams-cell"><div class="ams-n">' + (u.kind === "ext" ? "E" : si + 1) + '</div>' +
        x + card + (open ? pickerHtml() : "") + '</div>';
    }

    function takenIds() {
      const set = new Set();
      cfg.forEach(function (p) {
        p.units.forEach(function (u) { u.slots.forEach(function (id) { if (id) set.add(String(id)); }); });
      });
      return set;
    }

    function pickItems(query) {
      const taken = takenIds();
      const q = query.trim().toLowerCase();
      const items = allSpools.filter(function (s) {
        if (s.archived || taken.has(String(s.id))) return false;
        if (!q) return true;
        const f = s.filament || {};
        return [f.name, f.material, (f.vendor || {}).name, s.location, f.color_hex].join(" ").toLowerCase().includes(q);
      }).sort(function (x, y) {
        return ((x.filament || {}).name || "").localeCompare((y.filament || {}).name || "");
      }).slice(0, 200);
      if (!items.length) return '<div class="pnote">No spools left to assign.</div>';
      return items.map(function (s) {
        const f = s.filament || {};
        const sub = [(f.vendor || {}).name, typeof s.id === "number" ? "#" + s.id : "", s.location].filter(Boolean).join(" \u00b7 ");
        const color = swatch(f);
        return '<div class="pi" data-act="pick" data-id="' + esc(s.id) + '"><span class="d" style="background:' + esc(color) + '"></span>' +
          '<span>' + esc(f.name || "Spool " + s.id) + '<small>' + esc(sub) + '</small></span>' +
          '<span class="m">' + formatWeight(s.remaining_weight) + '</span></div>';
      }).join("");
    }

    function pickerHtml() {
      return '<div class="picker"><input type="text" placeholder="Search spools" autocomplete="off">' +
        '<div class="pick-list">' + pickItems("") + '</div>' +
        '<div class="pnote">Spools already in a slot are not listed.</div></div>';
    }

    function autoPanel(p) {
      const lvl = liveByLink(p.id);
      const st = (liveData.links || {})[p.id];
      const live = !!lvl && st === "live";
      const sub = live ? linkStatus(p) : st === "unreachable"
        ? "Can't reach " + esc(p.ip) + " - is the printer on?" : "Connecting to " + esc(p.ip) + "...";
      return '<div class="ams"><div class="ams-h"><span class="pname">' + esc(p.name) + '</span><span class="sub">' + sub + '</span></div>' +
        '<div class="ams-body">' + (live ? liveUnits(lvl) : "") +
        '<div class="ams-note">Found in your OrcaSlicer printer presets. Each Spoolman filament is listed under ' +
        'User presets in the sidebar&#39;s filament dropdown, already in its colour.</div></div></div>';
    }

    function manualPanel(p, byId) {
      if (p.auto) return autoPanel(p);
      let total = 0;
      let used = 0;
      const units = p.units.map(function (u, ui) {
        total += u.slots.length;
        used += u.slots.filter(Boolean).length;
        const label = unitLabel(p, u);
        const key = "u:" + p.id + ":" + ui;
        const rm = '<button class="sbtn ghost' + (armed === key ? " armed" : "") + '" data-act="remove-unit" data-p="' + esc(p.id) +
          '" data-u="' + ui + '">' + (armed === key ? "Click Again to Remove" : "Remove " + label) + '</button>';
        const cells = u.slots.map(function (_, si) { return manualCell(p, ui, si, byId); }).join("");
        return '<div class="ams-unit"><span>' + label + '</span>' + rm + '</div><div class="ams-grid">' + cells + '</div>';
      }).join("");
      const hasExt = p.units.some(function (u) { return u.kind === "ext"; });
      const pk = "p:" + p.id;
      const name = renaming === p.id
        ? '<input class="pname-in" data-p="' + esc(p.id) + '" value="' + esc(p.name) + '" maxlength="40">'
        : '<button class="pname" data-act="rename" data-p="' + esc(p.id) + '" title="Rename">' + esc(p.name) + ' \u270e</button>';
      const lvl = liveByLink(p.id);
      const live = !!lvl && (liveData.links || {})[p.id] === "live";
      let sub = total ? used + " of " + total + " slots assigned" : "Add an AMS or external spool to start";
      const ls = linkStatus(p);
      if (ls) sub = ls;
      const bar = '<div class="bar">' +
        (live ? "" : '<button class="sbtn primary" data-act="link" data-p="' + esc(p.id) + '">Live Link</button>') +
        (live ? "" : '<button class="sbtn" data-act="add-unit" data-kind="ams" data-p="' + esc(p.id) + '">+ AMS</button>' +
        '<button class="sbtn" data-act="add-unit" data-kind="ht" data-p="' + esc(p.id) + '">+ AMS HT</button>') +
        (hasExt || live ? "" : '<button class="sbtn" data-act="add-unit" data-kind="ext" data-p="' + esc(p.id) + '">+ External Spool</button>') +
        '<button class="sbtn' + (armed === pk ? " armed" : "") + '" data-act="remove-printer" data-p="' + esc(p.id) + '">' +
        (armed === pk ? "Click Again to Remove" : "Remove Printer") + '</button></div>';
      return '<div class="ams"><div class="ams-h">' + name + '<span class="sub">' + sub + '</span>' + bar + '</div>' +
        (linkOpen === p.id ? linkForm(p) : "") +
        '<div class="ams-body">' + (live ? liveUnits(lvl) : units) +
        (live ? '' : '<div class="ams-note">A representative view only: built from the spools you&#39;ve assigned. Use Live Link to read the printer itself.</div>') + '</div></div>';
    }

    function progDur(m) {
      const h = Math.floor(m / 60);
      return (h ? h + " h " : "") + String(m % 60).padStart(h ? 2 : 1, "0") + " min";
    }

    function progClock(ms) {
      return new Date(ms).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
    }

    function progTray(lv, t) {
      if (t.unit === "ext") return lv.ext ? { label: "External Spool", tray: lv.ext } : null;
      const u = lv.units.find(function (x) { return x.id === t.unit; });
      if (!u || !u.trays[t.slot]) return null;
      const label = u.kind === "ht" ? "AMS HT" : "AMS " + (lv.units.filter(function (x) { return x.kind === "ams"; }).indexOf(u) + 1) + " Slot " + (t.slot + 1);
      return { label: label, tray: u.trays[t.slot] };
    }

    function progRow(lv) {
      const j = lv.job;
      const s = PROG_STATES[j.state];
      const live = PROG_LIVE.indexOf(j.state) >= 0;
      const pct = j.state === "FINISH" ? 100 : Math.max(0, Math.min(100, j.pct || 0));
      const meta = [];
      if (j.stage && j.state !== "FAILED") meta.push('<span><b>' + esc(j.stage) + '</b></span>');
      if (j.layers) meta.push(j.layer && s[2] !== "prep" ? '<span>Layer <b>' + j.layer + '</b> / ' + j.layers + '</span>' : '<span>' + j.layers + ' layers</span>');
      if (live && j.left !== null && j.left !== undefined) {
        meta.push(s[2] === "prep" ? '<span>About ' + progDur(j.left) + '</span>' : '<span><b>' + progDur(j.left) + '</b> left</span>');
        if (progress.finish && s[2] !== "prep") meta.push('<span>Done around ' + progClock(Date.now() + j.left * 60000) + '</span>');
      }
      if (j.state === "FINISH" && j.took) meta.push('<span>Took <b>' + progDur(j.took) + '</b></span>');
      if (j.state === "FINISH" && j.end) meta.push('<span>Finished at ' + progClock(j.end * 1000) + '</span>');
      if (j.state === "FAILED" && j.layer) meta.push('<span>Stopped at Layer ' + j.layer + '</span>');
      const t = live && j.tray ? progTray(lv, j.tray) : null;
      if (t) {
        const colour = t.tray.colour ? "#" + t.tray.colour : "#888";
        meta.push('<span class="pj-slot"><span class="d" style="background:' + colour + '"></span>' + t.label + (t.tray.name ? ' \u00b7 ' + esc(t.tray.name) : "") + '</span>');
      }
      return '<div class="pj"><div class="pj-top"><span class="pj-name">' + esc(j.name || "Print") + '</span><span class="pj-chip ' + s[1] + '">' + s[0] + '</span>' +
        progWho(lv) + '<span class="pj-pct">' + (s[2] === "prep" ? "" : pct + "%") + '</span></div>' +
        '<div class="pj-track"><div class="pj-fill ' + s[2] + '" style="width:' + pct + '%"></div></div>' +
        '<div class="pj-meta">' + meta.join("") + '</div></div>';
    }

    function progWho(lv) {
      return '<span class="pj-who"><span class="live-dot' + (lv.age > 180 ? " stale" : "") + '"></span>' + esc(lv.name) + '</span>';
    }

    function renderProgress() {
      const list = liveOn && progress.on ? liveData.printers.filter(function (lv) {
        return (liveData.links || {})[lv.link] === "live" && lv.job;
      }) : [];
      const hide = progress.idle === "hide";
      const busy = list.filter(function (lv) { return hide ? PROG_LIVE.indexOf(lv.job.state) >= 0 : PROG_STATES[lv.job.state]; });
      const idle = hide ? [] : list.filter(function (lv) { return !PROG_STATES[lv.job.state]; });
      if (!busy.length && !idle.length) { progSlot.innerHTML = ""; return; }
      const idleRow = function (lv, title) {
        return '<div class="pj-idle">' + (title ? "<b>Print Progress</b>" : "") + '<span class="pj-chip idle">Idle</span>' +
          '<span class="sub">No print running</span>' + progWho(lv) + '</div>';
      };
      if (!busy.length) { progSlot.innerHTML = '<div class="prog">' + idle.map(function (lv, i) { return idleRow(lv, i === 0); }).join("") + '</div>'; return; }
      progSlot.innerHTML = '<div class="prog"><div class="prog-h"><b>Print Progress</b><span class="sub"><span class="live-dot' + (busy.every(function (lv) { return lv.age > 180; }) ? " stale" : "") + '"></span>Live</span></div>' +
        busy.map(progRow).join("") + idle.map(function (lv) { return idleRow(lv, false); }).join("") + '</div>';
    }

    function renderPrinters() {
      renderProgress();
      const byId = new Map();
      allSpools.forEach(function (s) { byId.set(String(s.id), s); });
      let html = cfg.map(function (p) { return manualPanel(p, byId); }).join("") + linked.map(linkedPanel).join("");
      if (!cfg.length && !linked.length) {
        html += '<div class="empty">No printers yet. Add your printer, then choose the spool in each slot.</div>';
      }
      html += '<button class="sbtn addp" data-act="add-printer">+ Add Printer</button>';
      amsList.innerHTML = html;
      const field = amsList.querySelector(".pname-in") || amsList.querySelector(".picker input");
      if (field) { field.focus(); if (field.classList.contains("pname-in")) field.select(); }
    }

    function pollLive() {
      if (liveOn && showTab && tab === "printer") orca.postMessage({ type: "live" });
    }
    setInterval(pollLive, 5000);
    setInterval(function () {
      if (liveOn && usage.enabled && tab !== "printer") orca.postMessage({ type: "live" });
    }, 30000);

    function updateTabs() {
      const onPrinter = showTab && tab === "printer";
      tabsEl.hidden = !showTab;
      document.getElementById("page-spools").hidden = onPrinter;
      document.getElementById("page-printer").hidden = !onPrinter;
      if (showTab) plateSlot.appendChild(plateEl); else listEl.parentNode.insertBefore(plateEl, listEl);
      plateEl.classList.toggle("on-printer", showTab);
      if (onPrinter) pollLive();
      tabsEl.querySelectorAll("button").forEach(function (b) {
        b.classList.toggle("on", b.dataset.tab === (onPrinter ? "printer" : "spools"));
      });
    }

    tabsEl.addEventListener("click", function (e) {
      const b = e.target.closest("button");
      if (!b) return;
      tab = b.dataset.tab;
      try { localStorage.setItem("spooler.tab", tab); } catch (err) {}
      updateTabs();
    });

    amsList.addEventListener("click", function (e) {
      const el = e.target.closest("[data-act]");
      if (!el) return;
      const act = el.dataset.act;
      const p = cfg.find(function (x) { return x.id === el.dataset.p; });
      const ui = Number(el.dataset.u);
      const si = Number(el.dataset.s);
      const before = armed;
      armed = "";
      let changed = false;
      if (act === "add-printer") {
        const id = "p" + Date.now().toString(36) + Math.floor(Math.random() * 1296).toString(36);
        cfg.push({ id: id, name: cfg.length ? "Printer " + (cfg.length + 1) : "Printer", units: [] });
        renaming = id;
        changed = true;
      } else if (p && act === "rename") {
        renaming = p.id;
      } else if (p && act === "add-unit") {
        const kind = el.dataset.kind;
        if (KINDS[kind] && !(kind === "ext" && p.units.some(function (u) { return u.kind === "ext"; }))) {
          p.units.push({ kind: kind, slots: new Array(KINDS[kind]).fill(null) });
          p.units.sort(function (x, y) { return RANK[x.kind] - RANK[y.kind]; });
          changed = true;
        }
      } else if (p && act === "remove-unit") {
        const key = "u:" + p.id + ":" + ui;
        if (before === key) { p.units.splice(ui, 1); picking = null; changed = true; } else { armed = key; }
      } else if (p && act === "remove-printer") {
        const key = "p:" + p.id;
        if (before === key) { cfg.splice(cfg.indexOf(p), 1); picking = null; changed = true; } else { armed = key; }
      } else if (p && act === "assign") {
        const same = picking && picking.p === p.id && picking.u === ui && picking.s === si;
        picking = same ? null : { p: p.id, u: ui, s: si };
      } else if (p && act === "clear") {
        p.units[ui].slots[si] = null;
        changed = true;
      } else if (p && act === "link") {
        linkOpen = linkOpen === p.id ? "" : p.id;
      } else if (p && act === "link-cancel") {
        linkOpen = "";
      } else if (p && (act === "link-save" || act === "link-remove")) {
        const form = amsList.querySelector(".linkform");
        const val = function (f) { const i = form && form.querySelector('[data-f="' + f + '"]'); return i ? i.value.trim() : ""; };
        const code = act === "link-save" ? val("code") : "";
        p.ip = act === "link-save" ? val("ip") : "";
        p.serial = act === "link-save" ? val("serial") : "";
        if (act === "link-remove") p.has_code = false;
        savePrinters();
        if (code || act === "link-remove") { orca.postMessage({ type: "printer_code", id: p.id, code: code }); if (code) p.has_code = true; }
        linkOpen = "";
        liveOn = liveOn || !!(p.ip && p.has_code);
        liveKey = "";
        setTimeout(pollLive, 300);
      } else if (act === "pick" && picking) {
        const target = cfg.find(function (x) { return x.id === picking.p; });
        if (target) {
          target.units[picking.u].slots[picking.s] = el.dataset.id;
          changed = true;
        }
        picking = null;
      }
      if (changed) savePrinters();
      renderPrinters();
    });

    amsList.addEventListener("input", function (e) {
      if (!e.target.matches(".picker input")) return;
      amsList.querySelector(".pick-list").innerHTML = pickItems(e.target.value);
    });

    function commitName(input, keep) {
      const p = cfg.find(function (x) { return x.id === input.dataset.p; });
      renaming = "";
      if (p && keep) {
        p.name = input.value.trim().slice(0, 40) || p.name;
        savePrinters();
      }
      renderPrinters();
    }

    amsList.addEventListener("keydown", function (e) {
      if (!e.target.matches(".pname-in")) return;
      if (e.key === "Enter") commitName(e.target, true);
      else if (e.key === "Escape") commitName(e.target, false);
    });

    amsList.addEventListener("focusout", function (e) {
      if (renaming && e.target.matches(".pname-in")) commitName(e.target, true);
    });

    document.addEventListener("click", function (e) {
      if (picking && !e.target.closest(".picker") && !e.target.closest('[data-act="assign"]')) {
        picking = null;
        renderPrinters();
      }
    });

    document.addEventListener("keydown", function (e) {
      if (e.key === "Escape" && picking) { picking = null; renderPrinters(); }
    });

    updateTabs();
    renderPrinters();

    function el(tag, className, text) {
      const node = document.createElement(tag);
      if (className) node.className = className;
      if (text !== undefined) node.textContent = text;
      return node;
    }

    function plateRowEl(row) {
      const node = el("div", "plate-row st-" + row.status);
      const dot = el("div", "plate-dot");
      dot.style.background = /^#?[0-9a-f]{6}/i.test(row.colour) ? "#" + row.colour.replace(/^#/, "").slice(0, 6) : "#888";
      const who = el("div", "plate-who");
      who.appendChild(el("div", "plate-name", row.slots + " \u00b7 " + row.name));
      who.appendChild(el("div", "plate-meta", row.meta));
      const bar = el("div", "plate-bar");
      if (row.status !== "unknown") {
        const have = el("i", "have");
        have.style.width = Math.round(row.fill * 100) + "%";
        have.style.background = "#" + String(row.spool_colour).replace(/^#/, "").slice(0, 6);
        bar.appendChild(have);
        const need = el("i", "need");
        need.style.width = Math.round(row.need_pct * 100) + "%";
        bar.appendChild(need);
      }
      const result = el("div", "plate-result");
      result.appendChild(el("div", "plate-headline", row.headline));
      result.appendChild(el("div", "plate-meta", row.detail));
      node.append(dot, who, bar, result);
      return node;
    }

    function setPlate(data) {
      plate = data && Array.isArray(data.rows) && data.rows.length ? data : null;
      plateSlots = new Map();
      plateOrder = new Map();
      plateList.innerHTML = "";
      if (plate) {
        plate.rows.forEach(function (row) {
          plateList.appendChild(plateRowEl(row));
          row.ids.forEach(function (id) {
            plateSlots.set(id, plateSlots.has(id) ? plateSlots.get(id) + ", " + row.slots : row.slots);
            if (!plateOrder.has(id) || row.first < plateOrder.get(id)) plateOrder.set(id, row.first);
          });
        });
        const attention = plate.rows.filter(function (r) {
          return r.status === "barely" || r.status === "mixed" || r.status === "short";
        }).length;
        const fine = plate.rows.some(function (r) { return r.status === "ok"; });
        const pill = document.getElementById("plate-pill");
        pill.className = "plate-pill " + (attention ? "attention" : "fine");
        pill.textContent = attention ? attention + (attention === 1 ? " needs" : " need") + " attention" : "Quantity OK";
        pill.hidden = !attention && !fine;
        plateAttn = attention;
        syncDot();
        document.getElementById("plate-sub").textContent =
          "Sliced " + (plate.time || "") + " \u00b7 striped = needed, solid = left \u00b7 clears on next slice";
      }
      plateEl.hidden = !plate;
      if (!plate) { plateAttn = false; syncDot(); }
      renderPrinters();
      plateSort.disabled = !plate;
      if (!plate && sortKeyEl.value === "plate") sortKeyEl.value = lastSort;
      applyFilters();
    }

    function computeDupes() {
      dupes = new Map();
      allSpools.forEach(function (s) {
        const id = (s.filament || {}).id;
        if (s.archived || id === undefined || typeof s.remaining_weight !== "number") return;
        const d = dupes.get(id) || { count: 0, total: 0 };
        d.count += 1;
        d.total += s.remaining_weight;
        dupes.set(id, d);
      });
    }

    function setFilters(open) {
      fPanel.hidden = !open;
      fToggle.setAttribute("aria-expanded", open ? "true" : "false");
      try { localStorage.setItem("spooler.filters", open ? "1" : "0"); } catch (err) {}
      filterLabel();
    }

    function filterLabel() {
      const active = (searchEl.value.trim() ? 1 : 0) + (materialEl.value ? 1 : 0) +
        (vendorEl.value ? 1 : 0) + (groupKeyEl.value !== "none" ? 1 : 0);
      fToggle.innerHTML = "Filters" + (active ? " (" + active + ")" : "") +
        (fPanel.hidden ? " &#9662;" : " &#9652;");
    }

    function populateFilterOptions() {
      const materials = new Set();
      const vendors = new Set();
      allSpools.forEach(function (s) {
        const filament = s.filament || {};
        const vendor = filament.vendor || {};
        if (filament.material) materials.add(filament.material);
        if (vendor.name) vendors.add(vendor.name);
      });
      function fillOptions(select, values, currentValue) {
        const placeholder = select.options[0];
        select.innerHTML = "";
        select.appendChild(placeholder);
        [...values].sort().forEach(function (value) {
          const option = document.createElement("option");
          option.value = value;
          option.textContent = value;
          select.appendChild(option);
        });
        select.value = values.has(currentValue) ? currentValue : "";
      }
      fillOptions(materialEl, materials, materialEl.value);
      fillOptions(vendorEl, vendors, vendorEl.value);
    }

    function progressClass(percent) {
      if (percent === null) return "mid";
      if (percent >= 50) return "high";
      if (percent >= 20) return "mid";
      return "low";
    }

    function formatWeight(grams) {
      if (typeof grams !== "number") return "?";
      return Math.abs(grams) >= 1000
        ? (grams / 1000).toFixed(2) + " kg"
        : Math.round(grams) + " g";
    }

    function lowTint(grams) {
      if (typeof grams !== "number" || lowStockGrams <= 0 || grams >= lowStockGrams) return "";
      const t = Math.max(0, Math.min(1, (lowStockGrams - grams) / (lowStockGrams * 0.8)));
      const amber = [224, 160, 48], red = [217, 83, 79];
      return "rgb(" + amber.map(function (v, i) { return Math.round(v + (red[i] - v) * t); }).join(",") + ")";
    }

    function tagUids(s) {
      const tags = Array.isArray(s.rfid_tags) ? s.rfid_tags : s.tags;
      if (!Array.isArray(tags)) return [];
      return tags.map(function (t) {
        return typeof t === "string" ? t : (t && (t.uid || t.id)) || null;
      }).filter(Boolean);
    }

    function sortValue(s, key) {
      const filament = s.filament || {};
      const vendor = filament.vendor || {};
      switch (key) {
        case "name": return (filament.name || "").toLowerCase() || null;
        case "material": return (filament.material || "").toLowerCase() || null;
        case "vendor": return (vendor.name || "").toLowerCase() || null;
        case "remaining": return (typeof s.remaining_weight === "number") ? s.remaining_weight : null;
        case "used": return (typeof s.used_weight === "number") ? s.used_weight : null;
        case "first_used": return s.first_used ? Date.parse(s.first_used) : null;
        case "last_used": return s.last_used ? Date.parse(s.last_used) : null;
        case "plate": return plateOrder.has(s.id) ? plateOrder.get(s.id) : null;
        default: return null;
      }
    }

    // A spool missing the field (e.g. never used) always sorts last, even descending.
    function compareSpools(a, b, key, dir) {
      const av = sortValue(a, key);
      const bv = sortValue(b, key);
      const aNull = av === null || av === undefined;
      const bNull = bv === null || bv === undefined;
      if (aNull && bNull) return 0;
      if (aNull) return 1;
      if (bNull) return -1;
      if (av < bv) return dir === "asc" ? -1 : 1;
      if (av > bv) return dir === "asc" ? 1 : -1;
      return 0;
    }

    function originalWeight(s) {
      const filament = s.filament || {};
      return (s.initial_weight !== undefined && s.initial_weight !== null)
        ? s.initial_weight : filament.weight;
    }

    function spoolRowHtml(s) {
      const filament = s.filament || {};
      const vendor = filament.vendor || {};
      const color = swatch(filament);
      const main = swatchMain(filament);
      const ring = swatchCols(filament).length > 1 ? ";border-color:" + main : "";
      const name = filament.name || ("Spool #" + s.id);
      const material = filament.material || "";
      const vendorName = vendor.name || "";
      const subtitleParts = [];
      if (material) subtitleParts.push(material);
      if (filament.color_hex) subtitleParts.push("#" + filament.color_hex.replace(/^#/, "").toUpperCase());
      if (typeof filament.diameter === "number") subtitleParts.push(filament.diameter + "mm");
      const subtitle = subtitleParts.join(" \\u00b7 ");
      const tags = tagUids(s);
      const original = originalWeight(s);
      const remaining = s.remaining_weight;
      let percent = null;
      if (typeof original === "number" && original > 0 && typeof remaining === "number") {
        percent = Math.max(0, Math.min(100, Math.round((remaining / original) * 100)));
      }
      const remainingLabel = formatWeight(remaining);
      const wHtml = percent === null || wMode === "grams" ? remainingLabel
        : wMode === "percent" ? percent + '%'
        : '<span class="spool-pct">' + percent + '% \u00b7</span>' + remainingLabel;
      const dupe = dupes.get(filament.id);
      const dupeHtml = dupe && dupe.count > 1
        ? '<span class="spool-dup">\u00d7' + dupe.count + ' \u00b7 ' + formatWeight(dupe.total) + ' together</span>'
        : '';
      const plateLabel = plateSlots.get(s.id);
      const chipHtml = plateLabel ? '<span class="plate-chip">On This Plate \u00b7 ' + plateLabel + '</span>' : '';
      const percentTitle = percent === null ? "Remaining unknown" : percent + "% remaining";
      const tagHtml = vendorName
        ? '<div class="spool-tag">' +
            '<svg viewBox="0 0 12 12" fill="currentColor">' +
              '<rect x="0" y="0" width="5" height="5" rx="1"></rect>' +
              '<rect x="7" y="0" width="5" height="5" rx="1"></rect>' +
              '<rect x="0" y="7" width="5" height="5" rx="1"></rect>' +
              '<rect x="7" y="7" width="5" height="5" rx="1"></rect>' +
            '</svg>' +
            '<span>' + vendorName + '</span>' +
          '</div>'
        : '';
      const tip = [name, vendorName, remainingLabel + (typeof original === "number" ? " of " + formatWeight(original) : "") + " left"].filter(Boolean).join(" \u00b7 ");
      const tint = lowTint(remaining);
      const searchQuery = [vendorName, s.lot_nr || name].filter(Boolean).join(" ");
      const cartHtml = (cart && typeof remaining === "number" && remaining < lowStockGrams)
        ? '<button class="spool-cart" data-q="' + encodeURIComponent(searchQuery) + '" ' +
            'title="Low stock - search online for ' + searchQuery.replace(/"/g, "") + '">' +
            '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">' +
              '<circle cx="9" cy="20" r="1.4"></circle><circle cx="18" cy="20" r="1.4"></circle>' +
              '<path d="M2 3h3l2.4 12.2a1.5 1.5 0 0 0 1.5 1.2h8.6a1.5 1.5 0 0 0 1.5-1.1L21 8H6"></path>' +
            '</svg></button>'
        : '';
      const rfidHtml = tags.length
        ? '<div class="spool-rfid" title="RFID: ' + tags.join(", ") + '">' +
            '<span>RFID</span>' +
            '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round">' +
              '<circle cx="5" cy="19" r="1.8" fill="currentColor" stroke="none"></circle>' +
              '<path d="M5,14 A5,5 0 0 1 10,19"></path>' +
              '<path d="M5,10.5 A8.5,8.5 0 0 1 13.5,19"></path>' +
              '<path d="M5,7 A12,12 0 0 1 17,19"></path>' +
            '</svg>' +
          '</div>'
        : '';
      return (
        '<div class="spool-card" title="' + tip.replace(/"/g, "&quot;") + '">' +
          tagHtml +
          '<div class="spool-body">' +
            '<div class="spool-swatch-col">' +
              '<div class="spool-swatch" style="background:' + color + ring + '"></div>' +
              rfidHtml +
            '</div>' +
            '<div class="spool-main">' +
              '<div class="spool-top">' +
                '<div class="spool-title">' + name + dupeHtml + '</div>' +
                '<div class="spool-weight' + (tint ? ' low" style="color:' + tint : '') + '">' + wHtml + cartHtml + '</div>' +
              '</div>' +
              '<div class="spool-bar-track" title="' + percentTitle + '">' +
                '<div class="spool-bar-fill" style="width:' + (percent === null ? 0 : percent) + '%;background:' + main + '"></div>' +
              '</div>' +
              '<div class="spool-subtitle"><span class="sub-text">' + subtitle + '</span>' + chipHtml + '</div>' +
            '</div>' +
          '</div>' +
        '</div>'
      );
    }

    function groupKeyFor(s, mode) {
      const filament = s.filament || {};
      const vendor = filament.vendor || {};
      if (mode === "material") {
        const label = filament.material || "Unknown material";
        return { key: label, label: label };
      }
      if (mode === "vendor") {
        const label = vendor.name || "Unknown manufacturer";
        return { key: label, label: label };
      }
      const label = s.location || "No location";
      return { key: label, label: label };
    }

    function groupRowHtml(group, collapsed) {
      let totalOriginal = 0, totalRemaining = 0, hasOriginal = false, hasRemaining = false;
      group.items.forEach(function (s) {
        const original = originalWeight(s);
        if (typeof original === "number") { totalOriginal += original; hasOriginal = true; }
        if (typeof s.remaining_weight === "number") { totalRemaining += s.remaining_weight; hasRemaining = true; }
      });
      const percent = (hasOriginal && hasRemaining && totalOriginal > 0)
        ? Math.max(0, Math.min(100, Math.round((totalRemaining / totalOriginal) * 100))) : null;
      const remainingLabel = hasRemaining ? formatWeight(totalRemaining) : "?";
      const percentLabel = percent === null ? "?" : percent + "%";
      const count = group.items.length + " spool" + (group.items.length === 1 ? "" : "s");
      const wLabel = wMode === "grams" ? remainingLabel
        : wMode === "percent" ? (percent === null ? remainingLabel : percentLabel)
        : remainingLabel + ' \\u00b7 ' + percentLabel;
      const subLabel = [group.sub, count].filter(Boolean).join(" \\u00b7 ");
      return (
        '<div class="group' + (collapsed ? " collapsed" : "") + '" data-key="' + group.key + '">' +
          '<div class="group-card">' +
            '<div class="arrow">' + (collapsed ? "\\u25b8" : "\\u25be") + '</div>' +
            '<div class="group-info"><div class="group-name">' + group.label + '</div><div class="group-meta">' + subLabel + '</div></div>' +
            '<div class="group-bar">' +
              '<div class="group-meta" style="text-align:right;margin-bottom:2px;">' + wLabel + '</div>' +
              '<div class="group-bar-track"><div class="group-bar-fill ' + progressClass(percent) +
                '" style="width:' + (percent === null ? 0 : percent) + '%"></div></div>' +
            '</div>' +
          '</div>' +
          '<div class="group-items">' + group.items.map(spoolRowHtml).join("") + '</div>' +
        '</div>'
      );
    }

    const collapsedGroups = new Set();

    function renderGrouped(spools, mode) {
      const groups = new Map();
      spools.forEach(function (s) {
        const info = groupKeyFor(s, mode);
        if (!groups.has(info.key)) groups.set(info.key, { key: info.key, label: info.label, sub: info.sub, items: [] });
        groups.get(info.key).items.push(s);
      });
      const ordered = [...groups.values()].sort(function (a, b) {
        if (mode === "location" && b.items.length !== a.items.length) {
          return b.items.length - a.items.length;
        }
        return a.label.toLowerCase().localeCompare(b.label.toLowerCase());
      });
      listEl.innerHTML = ordered.map(function (group) {
        return groupRowHtml(group, collapsedGroups.has(group.key));
      }).join("");
      listEl.querySelectorAll(".group-card").forEach(function (header) {
        header.addEventListener("click", function () {
          const groupEl = header.closest(".group");
          const key = groupEl.dataset.key;
          if (collapsedGroups.has(key)) collapsedGroups.delete(key); else collapsedGroups.add(key);
          groupEl.classList.toggle("collapsed");
          header.querySelector(".arrow").innerHTML = collapsedGroups.has(key) ? "&#9656;" : "&#9662;";
        });
      });
    }

    function applyFilters() {
      filterLabel();
      const query = searchEl.value.trim().toLowerCase();
      const material = materialEl.value;
      const vendor = vendorEl.value;
      const filtered = allSpools.filter(function (s) {
        const filament = s.filament || {};
        const vendorObj = filament.vendor || {};
        if (material && filament.material !== material) return false;
        if (vendor && vendorObj.name !== vendor) return false;
        if (query) {
          const haystack = [filament.name, filament.material, vendorObj.name]
            .filter(Boolean).join(" ").toLowerCase();
          if (!haystack.includes(query)) return false;
        }
        return true;
      });
      statusEl.className = profileNote.error ? "error" : "";
      statusEl.textContent = filtered.length + " of " + allSpools.length + " spool" +
        (allSpools.length === 1 ? "" : "s") + (profileNote.error
          ? " \u00b7 OrcaSlicer presets not updated: " + profileNote.error
          : profileNote.count ? " \u00b7 " + profileNote.count + " OrcaSlicer filament presets" : "");
      filtered.sort(function (a, b) {
        return compareSpools(a, b, sortKeyEl.value, sortDir) ||
          (sortKeyEl.value === "plate" ? compareSpools(a, b, "remaining", "asc") : 0);
      });
      if (filtered.length === 0) {
        listEl.innerHTML = '<div class="empty">No spools match this filter.</div>';
        return;
      }
      const groupMode = groupKeyEl.value;
      if (groupMode === "none") {
        listEl.innerHTML = filtered.map(spoolRowHtml).join("");
      } else {
        renderGrouped(filtered, groupMode);
      }
    }

    function render(payload) {
      if (!payload.ok) {
        statusEl.textContent = payload.error || "Unknown error";
        statusEl.className = "error";
        listEl.innerHTML = "";
        return;
      }
      allSpools = payload.spools || [];
      if (payload.profiles) profileNote = payload.profiles;
      computeDupes();
      if (typeof payload.low_stock_grams === "number") lowStockGrams = payload.low_stock_grams;
      if (typeof payload.weight_display === "string") wMode = payload.weight_display;
      if (typeof payload.show_cart === "boolean") cart = payload.show_cart;
      if (payload.spool_columns) listEl.classList.toggle("cols-2", payload.spool_columns === 2);
      if (Array.isArray(payload.printers)) cfg = payload.printers;
      if (typeof payload.show_printer_tab === "boolean") showTab = payload.show_printer_tab;
      liveOn = payload.live_ok === true;
      if (payload.usage) setUsage(payload.usage);
      if (payload.progress) progress = payload.progress;
      if (liveOn) pollLive();
      populateFilterOptions();
      buildPrinters();
      updateTabs();
      renderPrinters();
      applyFilters();
    }

    orca.onMessage(function (data) {
      if (data && data.type === "spools") {
        render(data);
      } else if (data && data.type === "plate") {
        setPlate(data);
      } else if (data && data.type === "plate_clear") {
        setPlate(null);
      } else if (data && data.type === "usage") {
        setUsage(data.usage, true);
      } else if (data && data.type === "sent") {
        statusEl.textContent = data.text;
        statusEl.className = data.ok ? "" : "error";
      } else if (data && data.type === "live") {
        const key = JSON.stringify(data.live);
        liveData = data.live;
        if (data.usage) setUsage(data.usage);
        if (key !== liveKey && !picking && !renaming && !linkOpen) { liveKey = key; renderPrinters(); }
        renderProgress();
      }
    });

    listEl.addEventListener("click", function (e) {
      const btn = e.target.closest(".spool-cart");
      if (btn) {
        orca.postMessage({ type: "order", query: decodeURIComponent(btn.dataset.q) });
      }
    });

    searchEl.addEventListener("input", applyFilters);
    materialEl.addEventListener("change", applyFilters);
    vendorEl.addEventListener("change", applyFilters);
    groupKeyEl.addEventListener("change", applyFilters);
    sortKeyEl.addEventListener("change", function () {
      if (sortKeyEl.value !== "plate") lastSort = sortKeyEl.value;
      applyFilters();
    });
    sortDirBtn.addEventListener("click", function () {
      sortDir = sortDir === "asc" ? "desc" : "asc";
      sortDirBtn.innerHTML = sortDir === "asc" ? "&#9650;" : "&#9660;";
      applyFilters();
    });

    document.getElementById("settings-btn").addEventListener("click", function () {
      orca.postMessage({ type: "settings" });
    });
    document.getElementById("send-btn").addEventListener("click", function () {
      statusEl.textContent = "Sending to Spoolman...";
      statusEl.className = "";
      orca.postMessage({ type: "send" });
    });
    fToggle.addEventListener("click", function () { setFilters(fPanel.hidden); });
    try { setFilters(localStorage.getItem("spooler.filters") === "1"); } catch (err) { setFilters(false); }
    document.getElementById("plate-recheck").addEventListener("click", function () {
      orca.postMessage({ type: "plate_recheck" });
    });
    document.getElementById("plate-dismiss").addEventListener("click", function () {
      setPlate(null);
      orca.postMessage({ type: "plate_dismiss" });
    });

    // Ask for data on load rather than relying on a push landing in time.
    orca.postMessage({ type: "ready" });

    setInterval(function () {
      orca.postMessage({ type: "refresh" });
    }, __REFRESH_MS__);
  </script>
</body>
</html>
"""

SETTINGS_PAGE = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<link rel="icon" href="__LOGODATA__">
<style>
  * { font-family: __FONT__; }
  html { overscroll-behavior-x: none; }
  html, body { height: 100%; }
  body {
    margin: 0; padding: 24px 28px; box-sizing: border-box; font-size: 13px;
    display: flex; flex-direction: column; line-height: 1.4;
    background: var(--orca-bg); color: var(--orca-fg);
  }
  .header {
    display: flex; align-items: center; gap: 12px;
    padding-bottom: 14px; margin-bottom: 18px;
    border-bottom: 1px solid var(--orca-border);
  }
  .header img.logo { width: 52px; height: 52px; flex-shrink: 0; }
  h2 { margin: 0; font-size: 20px; font-weight: 700; color: var(--orca-fg); }
  .step { display: flex; gap: 12px; margin-bottom: 16px; }
  .step-num {
    flex-shrink: 0; width: 22px; height: 22px; margin-top: 1px; border-radius: 50%;
    display: flex; align-items: center; justify-content: center;
    background: var(--orca-accent); color: var(--orca-accent-fg); font-size: 12px; font-weight: 700;
  }
  .step h4 { margin: 0 0 3px 0; font-size: 14px; font-weight: 700; color: var(--orca-accent); }
  .step p { margin: 0; color: var(--orca-muted); text-align: justify; }
  .step strong { color: var(--orca-fg); }
  .divider { border-top: 1px solid var(--orca-border); margin: 4px 0 16px 0; }
  h3 { margin: 0 0 8px 0; font-size: 14px; font-weight: 700; color: var(--orca-accent); }
  h3 .emoji { margin-right: 6px; font-size: 22px; vertical-align: -3px; display: inline-block; }
  label { display: block; margin-bottom: 8px; }
  input {
    width: 100%; box-sizing: border-box; padding: 10px 12px; font-size: 13px;
    background: var(--orca-bg); color: var(--orca-fg);
    border: 1px solid var(--orca-border); border-radius: 6px;
  }
  input:focus { outline: none; border-color: var(--orca-accent); }
  .status { margin-top: 8px; font-size: 12px; }
  .divider.spaced { margin-top: 18px; }
  .hint { margin-top: 6px; font-size: 12px; color: var(--orca-muted); }
  .check-row { display: flex; align-items: center; gap: 8px; margin: 0 0 12px 0; cursor: pointer; }
  .check-row input {
    -webkit-appearance: none; appearance: none; flex: none; width: 17px; height: 17px; margin: 0;
    border: 1.5px solid var(--orca-muted); border-radius: 4px; background: transparent; cursor: pointer;
  }
  .check-row input:hover { border-color: var(--orca-accent); }
  .check-row input:checked {
    border-color: #2fbfa8;
    background: transparent url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 16 16'%3E%3Cpath d='M3.5 8.5l3 3 6-7' fill='none' stroke='%232fbfa8' stroke-width='2.2' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E") center / 13px no-repeat;
  }
  .margin-row { display: flex; align-items: center; gap: 12px; }
  .margin-row label { margin: 0; }
  .margin-row input { width: 90px; }
  .seg { display: inline-flex; margin: 6px 0 14px; border: 1px solid var(--orca-border); border-radius: 6px; overflow: hidden; }
  .seg label { margin: 0; padding: 6px 18px; cursor: pointer; border-right: 1px solid var(--orca-border); }
  .seg label:last-child { border-right: 0; }
  .seg label.on { background: var(--orca-accent); color: var(--orca-accent-fg); font-weight: 700; }
  .seg input { position: absolute; opacity: 0; pointer-events: none; }
  .ws-card {
    display: flex; gap: 11px; align-items: flex-start; padding: 13px 14px 11px;
    border: 1px solid var(--orca-border); border-radius: 14px;
    background: var(--orca-border);
    background: color-mix(in srgb, var(--orca-fg) 5%, var(--orca-bg) 95%);
  }
  .ws-swatch {
    flex: none; width: 42px; height: 42px; border-radius: 50%; background: #1a1a1a;
    border: 2px solid rgba(255, 255, 255, 0.15); box-shadow: inset 0 0 0 1px rgba(0, 0, 0, 0.2);
  }
  .ws-main { flex: 1; min-width: 0; }
  .ws-top { display: flex; justify-content: space-between; align-items: baseline; gap: 8px; }
  .ws-name { font-weight: 700; }
  .ws-pct { color: var(--orca-muted); font-size: 12px; }
  .ws-bar { height: 5px; margin: 6px 0 5px; border-radius: 3px; background: rgba(127, 127, 127, 0.25); overflow: hidden; }
  .ws-bar i { display: block; height: 100%; width: 64%; background: #1a1a1a; }
  .ws-sub { font-size: 12px; color: var(--orca-muted); font-style: italic; }
  .lay-prev { display: grid; gap: 8px; }
  .lay-prev.two { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .lay-prev .ws-card { padding: 9px 11px 8px; gap: 9px; }
  .lay-prev .ws-swatch { width: 26px; height: 26px; }
  .lay-prev .ws-name { font-size: 12px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .lay-prev .ws-top span:last-child { font-size: 12px; flex: none; }
  .lay-prev .ws-bar { margin: 5px 0 0; }
  #prog-opts { padding-left: 25px; }
  .pp-card { padding: 12px 14px; border: 1px solid var(--orca-border); border-radius: 14px; background: var(--orca-border); background: color-mix(in srgb, var(--orca-fg) 5%, var(--orca-bg) 95%); }
  .pp-top { display: flex; align-items: center; gap: 10px; }
  .pp-name { font-weight: 700; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .pp-chip { font-size: 11px; font-weight: 700; padding: 2px 8px; border-radius: 99px; background: color-mix(in srgb, var(--orca-accent) 22%, transparent); color: #3cc9b9; }
  .pp-pct { margin-left: auto; font-size: 18px; font-weight: 800; }
  .pp-bar { height: 8px; margin: 8px 0 7px; border-radius: 4px; background: rgba(127, 127, 127, 0.25); overflow: hidden; }
  .pp-bar i { display: block; height: 100%; width: 37%; background: var(--orca-accent); }
  .pp-meta { display: flex; flex-wrap: wrap; gap: 4px 14px; font-size: 12px; color: var(--orca-muted); }
  .pp-meta b { color: var(--orca-fg); }
  #pp-slot { display: inline-flex; align-items: center; gap: 6px; }
  #pp-slot .d { width: 10px; height: 10px; border-radius: 50%; background: #ae835b; border: 2px solid rgba(255, 255, 255, 0.18); }
  .pp-off { display: none; color: var(--orca-muted); font-style: italic; }
  .prog-off #prog-opts, .prog-off #pp-card { display: none; }
  .prog-off .pp-off { display: block; }
  input[type="checkbox"] { width: 16px; height: 16px; padding: 0; margin: 0; accent-color: var(--orca-accent); }
  .status.ok { color: #3fb950; }
  .status.error { color: #d9534f; }
  .footer {
    margin-top: auto; padding-top: 14px; display: flex; align-items: center;
    gap: 10px; justify-content: flex-end; border-top: 1px solid var(--orca-border);
  }
  .about { margin-top: 16px; font-size: 11px; color: var(--orca-muted); line-height: 1.7; }
  .about .logpath { word-break: break-all; user-select: text; }
  .version-row { margin-right: auto; min-width: 0; font-size: 11px; line-height: 1.7; color: var(--orca-muted); }
  .header h2 { flex: 1; min-width: 0; }
  button {
    padding: 9px 18px; cursor: pointer; border-radius: 6px; font-size: 13px;
    font-weight: 700; border: 1px solid transparent;
    background: transparent; color: var(--orca-fg);
  }
  button.primary, button.test { background: var(--orca-accent); color: var(--orca-accent-fg); }
  button:disabled { opacity: 0.45; cursor: not-allowed; }
  .url-row { display: flex; gap: 8px; }
  .url-row input { flex: 1; min-width: 0; }
  button.test { white-space: nowrap; }
  .status.pending { color: var(--orca-muted); }
  .src-hidden { display: none; }
  .hint.warn { color: #e0a030; }
  #src-bambu .field-label { margin-top: 4px; }
  #bambu-resend { color: var(--orca-accent); }
  select { padding: 10px 12px; font-size: 13px; font-family: inherit; background: var(--orca-bg); color: var(--orca-fg); border: 1px solid var(--orca-border); border-radius: 6px; }
  select:focus { outline: none; border-color: var(--orca-accent); }
  select option { background: var(--orca-bg); color: var(--orca-fg); }
  button.primary:hover, button.test:hover { filter: brightness(1.08); }
  button.icon-btn { padding: 6px; line-height: 0; }
  button.link { padding: 0 0 0 6px; border: none; font-size: 11px; font-weight: 400; text-decoration: underline; }
  /* The host's own button:hover styling would otherwise repaint these; keep them static. */
  button.icon-btn, button.icon-btn:hover, button.icon-btn:focus, button.icon-btn:active {
    color: var(--orca-accent-fg) !important; background: var(--orca-accent) !important;
    border-color: var(--orca-accent) !important; box-shadow: none !important;
  }
  button.link, button.link:hover, button.link:focus, button.link:active {
    color: var(--orca-accent) !important; background: none !important; box-shadow: none !important;
  }
</style>
</head>
<body>
  <!--header--><div class="header">
    __LOGO__<h2>__PLUGIN_NAME__</h2>
    <button class="icon-btn" id="feedback" title="Send feedback or report a bug" aria-label="Send feedback">
      <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 11.5a8.38 8.38 0 0 1-.9 3.8 8.5 8.5 0 0 1-7.6 4.7 8.38 8.38 0 0 1-3.8-.9L3 21l1.9-5.7a8.38 8.38 0 0 1-.9-3.8 8.5 8.5 0 0 1 4.7-7.6 8.38 8.38 0 0 1 3.8-.9h.5a8.48 8.48 0 0 1 8 8v.5z"></path></svg>
    </button>
  </div><!--/header-->

  <!--steps--><div class="step">
    <div class="step-num">1</div>
    <div>
      <h4>Pick Your Source</h4>
      <p>Use your self-hosted Spoolman server, or Bambu Cloud.</p>
    </div>
  </div>
  <div class="step">
    <div class="step-num">2</div>
    <div>
      <h4>Browse Your Spools</h4>
      <p>Each card shows the filament color, remaining weight, and an RFID badge where a
      tag is linked. Filter, sort, or group the list by material, manufacturer, or location.</p>
    </div>
  </div><!--/steps-->
  <div class="divider"></div>

  <!--reorder--><h3><span class="emoji">🛒</span>Configure Filament Reorder</h3>
  <label class="check-row"><input id="show-cart" type="checkbox" __CART_CHECKED__>Show a Cart Button for Reordering Low-Stock Spools</label>
  <label for="low-stock" class="field-label">Low Stock Warning (Grams):</label>
  <input id="low-stock" type="number" min="0" step="10" value="__LOW_STOCK__">
  <div class="hint">Below this weight, a spool's remaining weight turns amber, then red as it runs out.</div><!--/reorder-->

  <div class="divider spaced"></div>

  <!--check--><h3><span class="emoji">\u26a0\ufe0f</span>Configure Filament Check</h3>
  <label class="check-row"><input id="plate-check" type="checkbox" __PLATE_CHECKED__>Show Filament Check Notifications</label>
  <div class="margin-row" title="Warns when a plate needs more than a spool has left, or would leave less than this margin spare.">
    <label for="plate-margin">Safety Margin (%):</label>
    <input id="plate-margin" type="number" min="0" max="50" step="5" value="__PLATE_MARGIN__">
  </div>
<!--/check-->
  <!--check-hint--><div class="hint">OrcaSlicer also has to run the check: switch on Spooler Filament Check in your process settings, under <span style="white-space: nowrap">Others &gt; Slicing Pipeline Plugin</span>.</div><!--/check-hint-->

  <div class="divider spaced"></div>

  <!--weights--><h3><span class="emoji">\u2696\ufe0f</span>Configure Spool Weights</h3>
  <div class="field-label">Show the remaining weight on spool cards as:</div>
  <div class="seg" id="weight-seg">
    <label><input type="radio" name="weight-display" value="grams">Grams</label>
    <label><input type="radio" name="weight-display" value="percent">Percentage</label>
    <label><input type="radio" name="weight-display" value="both">Both</label>
  </div><!--/weights-->
  <!--weights-preview--><div class="ws-card">
    <div class="ws-swatch"></div>
    <div class="ws-main">
      <div class="ws-top"><span class="ws-name">PLA Matte - Black</span><span id="weight-sample"></span></div>
      <div class="ws-bar"><i></i></div>
      <div class="ws-sub">PLA \u00b7 #1A1A1A \u00b7 1.75mm</div>
    </div>
  </div><!--/weights-preview-->

  <div class="divider spaced"></div>

  <!--layout--><h3><span class="emoji">\U0001f4cb</span>Configure Spool List</h3>
  <div class="field-label">Show spools on the Spools tab as:</div>
  <div class="seg" id="cols-seg">
    <label><input type="radio" name="spool-cols" value="1">Single Column</label>
    <label><input type="radio" name="spool-cols" value="2">Two Columns</label>
  </div>
  <div class="hint">In a narrow window, two columns fall back to a single column so names stay readable.</div><!--/layout-->
  <!--layout-preview--><div class="lay-prev" id="lay-prev">
    <div class="ws-card"><div class="ws-swatch" style="background:#1a1a1a"></div><div class="ws-main"><div class="ws-top"><span class="ws-name">PLA Matte - Black</span><span>640 g</span></div><div class="ws-bar"><i style="width:64%;background:#1a1a1a"></i></div></div></div>
    <div class="ws-card"><div class="ws-swatch" style="background:#C12E1F"></div><div class="ws-main"><div class="ws-top"><span class="ws-name">PLA Basic - Red</span><span>530 g</span></div><div class="ws-bar"><i style="width:53%;background:#C12E1F"></i></div></div></div>
    <div class="ws-card"><div class="ws-swatch" style="background:#2850A8"></div><div class="ws-main"><div class="ws-top"><span class="ws-name">PETG HF - Cobalt Blue</span><span>770 g</span></div><div class="ws-bar"><i style="width:77%;background:#2850A8"></i></div></div></div>
    <div class="ws-card"><div class="ws-swatch" style="background:#3F8E43"></div><div class="ws-main"><div class="ws-top"><span class="ws-name">PLA Basic - Bambu Green</span><span>700 g</span></div><div class="ws-bar"><i style="width:70%;background:#3F8E43"></i></div></div></div>
  </div><!--/layout-preview-->

  <div class="divider spaced"></div>

  <!--printer--><h3><span class="emoji">🧵</span>Configure Printer</h3>
  <label class="check-row"><input id="show-progress" type="checkbox">Show Print Progress on the Printer Tab</label>
  <div id="prog-opts">
    <label class="check-row"><input id="prog-finish" type="checkbox">Show the Estimated Finish Time</label>
    <label class="check-row"><input id="prog-slot" type="checkbox">Highlight the AMS Slot in Use</label>
    <div class="field-label">When no print is running:</div>
    <div class="seg" id="idle-seg">
      <label><input type="radio" name="progress-idle" value="line">Keep Print Progress Visible</label>
      <label><input type="radio" name="progress-idle" value="hide">Hide Print Progress</label>
    </div>
  </div>
  <div class="hint">Print progress requires a Live Link connection to the printer(s).</div><!--/printer-->
  <!--printer-preview--><div class="pp-card" id="pp-card">
    <div class="pp-top"><span class="pp-name">Desk_Organiser_Plate_1</span><span class="pp-chip">Printing</span><span class="pp-pct">37%</span></div>
    <div class="pp-bar"><i></i></div>
    <div class="pp-meta"><span>Layer <b>142</b> / 380</span><span><b>2 h 04 min</b> left</span><span id="pp-finish">Done around 11:24</span><span id="pp-slot"><span class="d"></span>AMS 1 Slot 2</span></div>
  </div>
  <div class="pp-card pp-off" id="pp-off">Print Progress is hidden. The Printer tab starts with your printers.</div><!--/printer-preview-->

  <div class="divider spaced"></div>

  <!--server--><h3><span class="emoji">\U0001F310</span>Choose Your Source</h3>
  <div class="field-label">Where should Spooler read your spools from?</div>
  <div class="seg" id="src-seg">
    <label><input type="radio" name="spool-source" value="spoolman">Spoolman</label>
    <label><input type="radio" name="spool-source" value="bambu">Bambu Cloud</label>
  </div>
  <div id="src-spoolman">
    <label for="url">Enter the URL of your self-hosted Spoolman server:</label>
    <div class="url-row">
      <input id="url" type="text" value="__URL__" placeholder="__DEFAULT_URL__">
      <button class="test" id="test">Test</button>
    </div>
    <div class="status __STATUS_CLASS__" id="conn-status">__STATUS_TEXT__</div>
  </div>
  <div id="src-bambu" class="src-hidden">
    <div id="bambu-in" class="src-hidden">
      <div class="field-label">Bambu Cloud Account</div>
      <div class="url-row">
        <input id="bambu-account" type="text" readonly value="__BAMBU_ACCOUNT__">
        <button class="test" id="bambu-test">Test Connection</button>
        <button class="test" id="bambu-out">Sign Out</button>
      </div>
    </div>
    <div id="bambu-login">
      <div class="field-label">Sign in with your Bambu Cloud account</div>
      <input id="bambu-email" type="text" placeholder="Email" autocomplete="off">
      <div class="url-row" style="margin-top: 8px">
        <input id="bambu-pass" type="password" placeholder="Password" autocomplete="off">
        <select id="bambu-region"><option value="global">Global</option><option value="china">China</option></select>
        <button class="test" id="bambu-signin">Sign In</button>
      </div>
    </div>
    <div id="bambu-code" class="src-hidden">
      <div class="field-label" id="bambu-code-label">Enter your Bambu Lab verification code</div>
      <div class="url-row">
        <input id="bambu-code-input" type="text" autocomplete="off" placeholder="Code">
        <button class="test" id="bambu-verify">Verify</button>
        <button class="test" id="bambu-back">Back</button>
      </div>
      <div class="hint"><a href="#" id="bambu-resend">Send a New Code</a></div>
    </div>
    <div class="status pending" id="bambu-status">__BAMBU_STATUS__</div>
    <div class="hint warn"><strong>!</strong> Experimental: this uses Bambu's unofficial cloud
    service, which Bambu can change at any time. Spooler never stores your password.</div>
  </div><!--/server-->

  <!--about--><div class="about">
    <div class="logpath">Log file: __LOG_PATH__</div>
  </div><!--/about-->

  <!--footer--><div class="footer">
    <div class="version-row">
      <span>Plugin version __VERSION__</span>
      <button class="link" id="check-update">Check for Updates</button>
      <span id="update-status"></span>
    </div>
    <button id="cancel">Cancel</button>
    <button class="primary" id="save" disabled>Save &amp; Close</button>
  </div><!--/footer-->
  <script>
    document.getElementById("cancel").addEventListener("click", function () {
      orca.postMessage({ type: "cancel" });
    });
    const urlEl = document.getElementById("url");
    const saveEl = document.getElementById("save");
    const statusEl = document.getElementById("conn-status");
    const norm = function (u) { return u.trim().replace(/\\/+$/, ""); };
    const srcRadios = document.querySelectorAll('input[name="spool-source"]');
    function srcPick() {
      const picked = document.querySelector('input[name="spool-source"]:checked');
      return picked ? picked.value : "spoolman";
    }
    let verifiedBambu = __VERIFIED_BAMBU__;

    // Save stays disabled until the URL passes a test. An already-connected saved URL
    // counts as passed, so other settings can be changed on their own.
    let verifiedUrl = __VERIFIED_URL__;
    let verifiedText = statusEl.textContent;

    function setStatus(text, cls) {
      statusEl.textContent = text;
      statusEl.className = "status " + cls;
    }
    function refreshSave() {
      if (srcPick() === "bambu") {
        saveEl.disabled = !verifiedBambu;
        return;
      }
      const url = norm(urlEl.value);
      saveEl.disabled = !(url && url === verifiedUrl);
    }

    urlEl.addEventListener("input", function () {
      if (norm(urlEl.value) === verifiedUrl) {
        setStatus(verifiedText, "ok");
      } else {
        setStatus("Press Test to check the connection before saving.", "pending");
      }
      refreshSave();
    });

    document.getElementById("test").addEventListener("click", function () {
      setStatus("Testing connection...", "pending");
      orca.postMessage({ type: "test", source: "spoolman", url: urlEl.value.trim() });
    });

    const bambuStatus = document.getElementById("bambu-status");
    const bambuAccount = document.getElementById("bambu-account");
    function setBambu(text, cls) {
      bambuStatus.textContent = text;
      bambuStatus.className = "status " + cls;
    }
    function checkBambu() {
      setBambu("Connecting to Bambu Cloud...", "pending");
      orca.postMessage({ type: "test", source: "bambu" });
    }
    document.getElementById("bambu-test").addEventListener("click", checkBambu);
    const bambuPanes = ["in", "login", "code"];
    function bambuPane(name) {
      bambuPanes.forEach(function (p) {
        document.getElementById(p === "in" ? "bambu-in" : "bambu-" + p).classList.toggle("src-hidden", p !== name);
      });
    }
    let bambuStep = "password";
    function bambuSend(action, extra) {
      setBambu({ password: "Signing in...", sign_out: "Signing out...", resend: "Sending a new code..." }[action] ||
               "Verifying your code...", "pending");
      orca.postMessage(Object.assign({ type: "bambu_auth", action: action }, extra || {}));
    }
    document.getElementById("bambu-signin").addEventListener("click", function () {
      const passEl = document.getElementById("bambu-pass");
      bambuSend("password", {
        account: document.getElementById("bambu-email").value,
        password: passEl.value,
        region: document.getElementById("bambu-region").value,
      });
      passEl.value = "";
    });
    document.getElementById("bambu-verify").addEventListener("click", function () {
      bambuSend(bambuStep, { code: document.getElementById("bambu-code-input").value });
    });
    document.getElementById("bambu-resend").addEventListener("click", function (e) {
      e.preventDefault();
      bambuSend("resend");
    });
    document.getElementById("bambu-back").addEventListener("click", function () {
      bambuPane("login");
      setBambu("Signed out", "pending");
    });
    document.getElementById("bambu-out").addEventListener("click", function () {
      verifiedBambu = false;
      bambuSend("sign_out");
    });
    function showSource(event) {
      const mode = srcPick();
      srcRadios.forEach(function (r) { r.parentNode.classList.toggle("on", r.checked); });
      document.getElementById("src-spoolman").classList.toggle("src-hidden", mode !== "spoolman");
      document.getElementById("src-bambu").classList.toggle("src-hidden", mode !== "bambu");
      if (mode === "bambu" && !verifiedBambu && event && event.isTrusted) checkBambu();
      refreshSave();
    }
    srcRadios.forEach(function (r) { r.addEventListener("change", showSource); });
    document.querySelector('input[name="spool-source"][value=' + __SOURCE__ + ']').checked = true;
    showSource();
    if (srcPick() === "bambu") checkBambu();

    document.getElementById("feedback").addEventListener("click", function () {
      orca.postMessage({ type: "feedback" });
    });
    const wRadios = document.querySelectorAll('input[name="weight-display"]');
    const wSample = document.getElementById("weight-sample");
    function wPick() {
      const picked = document.querySelector('input[name="weight-display"]:checked');
      return picked ? picked.value : "both";
    }
    function showWeight() {
      const mode = wPick();
      wRadios.forEach(function (r) { r.parentNode.classList.toggle("on", r.checked); });
      wSample.innerHTML = mode === "grams" ? "640 g"
        : mode === "percent" ? "64%"
        : '<span class="ws-pct">64% \u00b7</span> 640 g';
    }
    wRadios.forEach(function (r) { r.addEventListener("change", showWeight); });
    document.querySelector('input[name="weight-display"][value=' + __WEIGHT_MODE__ + ']').checked = true;
    showWeight();
    const cRadios = document.querySelectorAll('input[name="spool-cols"]');
    function cPick() {
      const picked = document.querySelector('input[name="spool-cols"]:checked');
      return picked ? Number(picked.value) : 1;
    }
    function showCols() {
      cRadios.forEach(function (r) { r.parentNode.classList.toggle("on", r.checked); });
      document.getElementById("lay-prev").classList.toggle("two", cPick() === 2);
    }
    cRadios.forEach(function (r) { r.addEventListener("change", showCols); });
    document.querySelector('input[name="spool-cols"][value="' + __COLUMNS__ + '"]').checked = true;
    showCols();
    const progOn = document.getElementById("show-progress");
    const progFinish = document.getElementById("prog-finish");
    const progSlot = document.getElementById("prog-slot");
    const idleRadios = document.querySelectorAll('input[name="progress-idle"]');
    function progPick() {
      const idle = document.querySelector('input[name="progress-idle"]:checked');
      return { on: progOn.checked, finish: progFinish.checked, slot: progSlot.checked, idle: idle ? idle.value : "line" };
    }
    function showProgress() {
      (progOn.closest(".srow") || document.body).classList.toggle("prog-off", !progOn.checked);
      document.getElementById("pp-finish").hidden = !progFinish.checked;
      document.getElementById("pp-slot").hidden = !progSlot.checked;
      idleRadios.forEach(function (r) { r.parentNode.classList.toggle("on", r.checked); });
    }
    [progOn, progFinish, progSlot].concat(Array.from(idleRadios)).forEach(function (el) {
      el.addEventListener("change", showProgress);
    });
    (function (p) {
      progOn.checked = p.on;
      progFinish.checked = p.finish;
      progSlot.checked = p.slot;
      document.querySelector('input[name="progress-idle"][value="' + p.idle + '"]').checked = true;
    })(__PROGRESS__);
    showProgress();
    const updateEl = document.getElementById("update-status");
    document.getElementById("check-update").addEventListener("click", function () {
      updateEl.textContent = "Checking...";
      orca.postMessage({ type: "check_update" });
    });
    function showUpdate(data) {
      updateEl.textContent = "";
      if (!data.ok) {
        updateEl.textContent = data.error;
      } else if (data.newer) {
        const link = document.createElement("button");
        link.className = "link";
        link.textContent = "Version " + data.version + " is available - view release";
        link.addEventListener("click", function () { orca.postMessage({ type: "release" }); });
        updateEl.appendChild(link);
      } else {
        updateEl.textContent = "You're up to date.";
      }
    }

    orca.onMessage(function (data) {
      if (data && data.type === "update_result") {
        showUpdate(data);
        return;
      }
      if (data && data.type === "bambu_auth_result") {
        if (!data.ok) {
          setBambu(data.error || "Sign in failed", "error");
        } else if (data.step === "done") {
          document.getElementById("bambu-code-input").value = "";
          checkBambu();
        } else if (data.step === "out") {
          bambuPane("login");
          bambuAccount.value = "Signed out";
          setBambu("Signed out", "pending");
          refreshSave();
        } else {
          bambuStep = data.step;
          document.getElementById("bambu-code-label").textContent = "Enter your Bambu Lab verification code";
          document.getElementById("bambu-resend").parentNode.classList.toggle("src-hidden", data.step === "tfa");
          bambuPane("code");
          setBambu("Enter your Bambu Lab verification code", "pending");
        }
        return;
      }
      if (!data || data.type !== "test_result") return;
      if (data.source === "bambu") {
        bambuAccount.value = data.account || "Signed out";
        verifiedBambu = !!data.ok;
        bambuPane(data.ok || !data.signin ? "in" : "login");
        if (data.ok) {
          setBambu("Connected to Bambu Cloud", "ok");
        } else {
          const why = data.error || "connection failed";
          setBambu("Not connected - " + why.charAt(0).toLowerCase() + why.slice(1), "error");
        }
        refreshSave();
        return;
      }
      if (data.ok) {
        verifiedUrl = norm(data.url || "");
        verifiedText = "Connected - Spoolman v" + data.version;
        if (norm(urlEl.value) === verifiedUrl) setStatus(verifiedText, "ok");
      } else {
        setStatus(data.error || "Connection failed", "error");
      }
      refreshSave();
    });

    // Confirms the message listener above is registered before Python sends
    // anything unprompted; see _on_settings's "ready" handler.
    orca.postMessage({ type: "ready" });

    saveEl.addEventListener("click", function () {
      const url = urlEl.value.trim();
      const lowStock = document.getElementById("low-stock").value;
      orca.postMessage({
        type: "save", source: srcPick(), url: url, low_stock: lowStock,
        plate_check: document.getElementById("plate-check").checked,
        plate_margin: document.getElementById("plate-margin").value,
        weight_display: wPick(),
        show_cart: document.getElementById("show-cart").checked,
        spool_columns: cPick(),
        progress: progPick(),
      });
    });
    refreshSave();
  </script>
</body>
</html>
"""


def main_html() -> str:
    return _fill(
        MAIN_PAGE,
        LOGO=LOGO_IMG,
        LOGODATA=LOGO_DATA_URI,
        FONT=FONT_STACK,
        PLUGIN_NAME="Spooler",
        LOW_STOCK_DEFAULT=LOW_DEFAULT,
        REFRESH_MS=REFRESH_SECS * 1000,
    )


def settings_html(current_url: str, spoolman_info: dict, low_stock_grams: float,
                  plate_check: bool = True, plate_margin: int = DEFAULT_MARGIN,
                  weight: str = "both", cart: bool = False, source: str = "spoolman",
                  progress: dict | None = None, columns: int = 1) -> str:
    """``spoolman_info`` describes the saved URL, not whatever is typed in the field."""
    verified_url = clean_url(current_url) if spoolman_info.get("ok") else ""
    if spoolman_info.get("ok"):
        status_text = f"Connected - Spoolman v{spoolman_info['version']}"
        status_class = "ok"
    elif spoolman_info.get("pending"):
        status_text = spoolman_info.get("error", "Checking connection...")
        status_class = "pending"
    else:
        status_text = spoolman_info.get("error", "Not connected")
        status_class = "error"
    return _fill(
        SETTINGS_PAGE,
        LOGO=LOGO_IMG,
        LOGODATA=LOGO_DATA_URI,
        FONT=FONT_STACK,
        PLUGIN_NAME="Spooler",
        VERSION=PLUGIN_VERSION,
        DEFAULT_URL=html.escape(DEFAULT_SPOOLMAN_URL),
        URL=html.escape(current_url or DEFAULT_SPOOLMAN_URL),
        LOW_STOCK=low_stock_grams,
        PLATE_CHECKED="checked" if plate_check else "",
        PLATE_MARGIN=plate_margin,
        WEIGHT_MODE=json.dumps(parse_weights(weight)),
        CART_CHECKED="checked" if cart else "",
        COLUMNS=parse_columns(columns),
        PROGRESS=json.dumps(parse_progress(progress)),
        LOG_PATH=html.escape(str(LOG_FILE)),
        STATUS_TEXT=html.escape(status_text),
        STATUS_CLASS=status_class,
        # "</" is escaped so a URL can't close the script tag.
        VERIFIED_URL=json.dumps(verified_url).replace("</", "<\\/"),
        SOURCE=json.dumps(parse_source(source)),
        VERIFIED_BAMBU="false",
        BAMBU_ACCOUNT="",
        BAMBU_STATUS="",
    )


def _split_page(page: str) -> tuple[str, str, str]:
    def between(start: str, end: str, begin: int = 0) -> str:
        a = page.index(start, begin) + len(start)
        return page[a:page.index(end, a)]

    body_start = page.index("<body>")
    return (
        between("<style>", "</style>"),
        between("<body>", "<script>"),
        between("<script>", "</script>", body_start),
    )


# The page templates wrap their sections in <!--name--> ... <!--/name--> markers, so the
# tab can pull them apart and rearrange them.
def _take_header(body: str) -> tuple[str, str]:
    start = body.index("<!--header-->")
    end = body.index("<!--/header-->") + len("<!--/header-->")
    return body[:start] + body[end:], body[start:end]


def _section(body: str, name: str) -> str:
    start = body.index(f"<!--{name}-->") + len(f"<!--{name}-->")
    return body[start:body.index(f"<!--/{name}-->")]


def _hidden(condition: bool) -> str:
    return "view-hidden" if condition else ""


def _button(header: str, button_id: str) -> str:
    return re.search(rf'<button[^>]*id="{button_id}".*?</button>', header, re.S).group(0)


def _scope_css(css: str, root: str) -> str:
    # Both pages style bare elements (body, button, h2...), so each page's rules are
    # prefixed with its view's id to stop them leaking into the other view.
    def scope(selector: str) -> str:
        selector = selector.strip()
        if selector == "*":
            return f"{root}, {root} *"
        if selector in ("html", "body"):
            return root
        for element in ("html ", "body "):
            if selector.startswith(element):
                return f"{root} {selector[len(element):]}"
        return f"{root} {selector}"

    def rule(match: re.Match) -> str:
        selectors = ", ".join(scope(sel) for sel in match.group(2).split(","))
        return f"{match.group(1)}{selectors} {{{match.group(3)}}}"

    return re.sub(r"(\s*)([^{}]+?)\s*\{([^{}]*)\}", rule, css)


# Pinned to the top and outside both views, so the logo and title never move when
# switching. !important stops OrcaSlicer's own button styling repainting the buttons.
TAB_HEADER_CSS = """
  #app-header, #app-header * { font-family: __FONT__; }
  #app-header {
    position: fixed; top: 0; left: 0; right: 0; z-index: 100; height: 76px; box-sizing: border-box;
    display: flex; align-items: center; gap: 12px; padding: 0 12px;
    background: var(--orca-bg); border-bottom: 1px solid var(--orca-border);
  }
  #app-header img.logo { width: 52px; height: 52px; flex-shrink: 0; }
  #app-header h2 {
    flex: 1; min-width: 0; margin: 0; font-size: 20px; font-weight: 700; color: var(--orca-fg);
    white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  }
  #app-header .header-actions { display: flex; flex-shrink: 0; }
  #app-header button, #app-header button:hover, #app-header button:focus, #app-header button:active {
    color: var(--orca-accent-fg) !important; background: var(--orca-accent) !important;
    border: 1px solid var(--orca-accent) !important; box-shadow: none !important;
    border-radius: 6px; cursor: pointer; font-size: 13px; font-weight: 700;
  }
  #app-header h2 { flex: 0 1 auto; }
  #app-header .header-actions { margin-left: auto; }
  #app-header .tabs { display: inline-flex; margin: 0 0 0 20px; border: 1px solid var(--orca-border); border-radius: 8px; overflow: hidden; }
  #app-header .tabs[hidden] { display: none; }
  #app-header .tabs button, #app-header .tabs button:hover, #app-header .tabs button:focus, #app-header .tabs button:active {
    color: var(--orca-fg) !important; background: transparent !important; border: 0 !important;
    border-right: 1px solid var(--orca-border) !important; border-radius: 0 !important;
    padding: 7px 20px; font-weight: 600;
  }
  #app-header .tabs button:last-child { border-right: 0 !important; }
  #app-header .tabs button.on, #app-header .tabs button.on:hover, #app-header .tabs button.on:focus, #app-header .tabs button.on:active {
    color: var(--orca-accent-fg) !important; background: var(--orca-accent) !important;
  }
  #app-header #tab-dot { display: inline-block; width: 8px; height: 8px; margin-left: 7px; border-radius: 50%; background: #e0a030; }
  #app-header #tab-dot[hidden] { display: none; }
  #app-header #settings-btn { padding: 7px 16px; }
  #app-header #feedback { padding: 6px; line-height: 0; }
"""


# Each topic is a card: the settings on the left, beside their preview or guide on the right.
# Narrow windows stack the two halves.
TAB_SETTINGS_CSS = """
  #view-settings { margin: 0 auto; }
  #view-settings .srow {
    margin: 0 0 14px; border: 1px solid var(--orca-border); border-radius: 12px;
    background: color-mix(in srgb, var(--orca-fg) 3%, var(--orca-bg) 97%);
  }
  #view-settings .srow > h3 {
    display: flex; align-items: center; margin: 0; padding: 14px 18px 0;
  }
  #view-settings .srow-body {
    display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 28px; padding: 12px 18px 16px;
  }
  #view-settings .srow-r .label {
    margin-bottom: 8px; font-size: 11px; font-weight: 700; letter-spacing: .06em; text-transform: uppercase;
    color: var(--orca-muted);
  }
  #view-settings .srow-r > .hint { margin-top: 0; }
  #view-settings .srow .step { margin-bottom: 10px; }
  #view-settings .srow .step:last-child { margin-bottom: 0; }
  #view-settings .srow .seg:last-child { margin-bottom: 0; }
  #view-settings .srow .check-row:last-child { margin-bottom: 0; }
  #view-settings .footer { border-top: none; padding-top: 6px; }
  #view-settings .foot-diag { margin-right: auto; min-width: 0; font-size: 11px; line-height: 1.6; color: var(--orca-muted); }
  #view-settings .foot-diag .version-row, #view-settings .foot-diag .about { margin: 0; }
  #view-settings .preview {
    padding: 14px 16px; border: 1px solid var(--orca-border); border-radius: 10px;
    background: var(--orca-border);
    background: color-mix(in srgb, var(--orca-fg) 5%, var(--orca-bg) 95%);
  }
  #view-settings .preview-count { font-weight: 700; }
  #view-settings .preview-list { list-style: none; margin: 8px 0 0; padding: 0; }
  #view-settings .preview-list li {
    display: flex; justify-content: space-between; gap: 12px;
    padding: 6px 0; border-top: 1px solid var(--orca-border);
  }
  #view-settings .preview-name { min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  #view-settings .preview-weight { flex-shrink: 0; color: #e0a030; }
  #view-settings .preview-note { color: var(--orca-muted); }
  #view-settings .preview-list:not(:empty) + .preview-note:not(:empty) { margin-top: 6px; }
  @media (max-width: 900px) {
    #view-settings .srow-body { grid-template-columns: minmax(0, 1fr); gap: 16px; }
  }
"""

TAB_PREVIEW_HTML = """
    <div class="preview" aria-live="polite">
      <div class="preview-count" id="preview-count"></div>
      <ul class="preview-list" id="preview-list"></ul>
      <div class="preview-note" id="preview-note"></div>
    </div>
"""

# Reads the spool list the main view already receives, so the preview needs no requests.
TAB_PREVIEW_JS = """
  var input = document.getElementById("low-stock");
  var countEl = document.getElementById("preview-count");
  var listEl = document.getElementById("preview-list");
  var noteEl = document.getElementById("preview-note");
  var MAX_LISTED = 5;
  var spools = null;

  function formatWeight(grams) {
    return Math.abs(grams) >= 1000 ? (grams / 1000).toFixed(2) + " kg" : Math.round(grams) + " g";
  }

  function update() {
    var grams = parseFloat(input.value);
    listEl.innerHTML = "";
    countEl.textContent = "";
    noteEl.textContent = "";
    if (spools === null) {
      noteEl.textContent = "Connect a spool source to preview which spools would trigger a reorder.";
      return;
    }
    if (!(grams >= 0)) {
      noteEl.textContent = "Enter a weight in grams to preview.";
      return;
    }
    // Same rule the spool cards use for the reorder cart.
    var low = spools.filter(function (s) {
      return typeof s.remaining_weight === "number" && s.remaining_weight < grams;
    }).sort(function (a, b) { return a.remaining_weight - b.remaining_weight; });
    countEl.textContent = (low.length || "No") + (low.length === 1 ? " spool is" : " spools are") +
      " under " + grams + " g";
    low.slice(0, MAX_LISTED).forEach(function (s) {
      var item = document.createElement("li");
      var name = document.createElement("span");
      var weight = document.createElement("span");
      name.className = "preview-name";
      name.textContent = (s.filament && s.filament.name) || ("Spool #" + s.id);
      weight.className = "preview-weight";
      weight.textContent = formatWeight(s.remaining_weight);
      item.appendChild(name);
      item.appendChild(weight);
      listEl.appendChild(item);
    });
    if (low.length > MAX_LISTED) noteEl.textContent = "+ " + (low.length - MAX_LISTED) + " more";
  }

  input.addEventListener("input", update);
  bridge.onMessage(function (data) {
    if (!data) return;
    if (data.type === "spools") {
      spools = data.ok ? (data.spools || []) : null;
      update();
    } else if (data.type === "show_view" && data.view === "settings") {
      update();
    }
  });
  update();
"""


# Loaded before either view's script. Each view gets its own `orca` object: the
# settings view tags what it sends (both views send "ready"), and a single real
# onMessage handler fans incoming messages out to both views.
TAB_BRIDGE = """
(function () {
  var host = window.orca;
  var handlers = [];
  host.onMessage(function (data) {
    handlers.forEach(function (handler) {
      try { handler(data); } catch (err) { console.error(err); }
    });
  });
  function bridge(tag) {
    return {
      postMessage: function (message) {
        host.postMessage(tag ? Object.assign({}, message, { view: tag }) : message);
      },
      onMessage: function (handler) { handlers.push(handler); },
    };
  }
  window.__spooler = { main: bridge(null), settings: bridge("settings") };

  handlers.push(function (data) {
    if (!data || data.type !== "show_view") return;
    var settings = data.view === "settings";
    document.getElementById("view-main").classList.toggle("view-hidden", settings);
    document.getElementById("view-settings").classList.toggle("view-hidden", !settings);
    document.getElementById("actions-main").classList.toggle("view-hidden", settings);
    document.getElementById("tabs-main").classList.toggle("view-hidden", settings);
    document.getElementById("actions-settings").classList.toggle("view-hidden", !settings);
    if (!settings) return;
    // Reset the form to the saved values each time Settings is opened, so
    // edits abandoned with Cancel don't linger.
    var url = document.getElementById("url");
    url.value = data.url || url.placeholder;
    url.dispatchEvent(new Event("input"));
    document.getElementById("low-stock").value = data.low_stock;
    document.getElementById("plate-check").checked = data.plate_check !== false;
    if (data.plate_margin !== undefined) document.getElementById("plate-margin").value = data.plate_margin;
    var src = document.querySelector('input[name="spool-source"][value="' + (data.source || "spoolman") + '"]');
    if (src) { src.checked = true; src.dispatchEvent(new Event("change")); }
    var mode = document.querySelector('input[name="weight-display"][value="' + (data.weight_display || "both") + '"]');
    if (mode) { mode.checked = true; mode.dispatchEvent(new Event("change")); }
    document.getElementById("show-cart").checked = data.show_cart === true;
    var cols = document.querySelector('input[name="spool-cols"][value="' + (data.spool_columns === 2 ? 2 : 1) + '"]');
    if (cols) { cols.checked = true; cols.dispatchEvent(new Event("change")); }
    var prog = data.progress || {};
    document.getElementById("prog-finish").checked = prog.finish !== false;
    document.getElementById("prog-slot").checked = prog.slot !== false;
    var idle = document.querySelector('input[name="progress-idle"][value="' + (prog.idle === "hide" ? "hide" : "line") + '"]');
    if (idle) idle.checked = true;
    var progOn = document.getElementById("show-progress");
    progOn.checked = prog.on !== false;
    progOn.dispatchEvent(new Event("change"));
    document.getElementById("update-status").textContent = "";
  });
})();
"""


def tab_html(initial_view: str, current_url: str, low_stock_grams: float,
             plate_check: bool = True, plate_margin: int = DEFAULT_MARGIN,
             weight: str = "both", cart: bool = False, source: str = "spoolman",
             progress: dict | None = None, columns: int = 1) -> str:
    """The spool list and Settings as two views of one page, under a shared header.

    Built from the standalone pages, which SpoolerWindow still shows as separate windows.
    """
    main_css, main_body, main_js = _split_page(main_html())
    settings_css, settings_body, settings_js = _split_page(settings_html(
        current_url, {"ok": False, "pending": True}, low_stock_grams, plate_check, plate_margin,
        weight, cart, source, progress, columns,
    ))
    main_body, main_header = _take_header(main_body)
    tabs_at = main_body.index('<div id="tabs"')
    tabs_end = main_body.index("</div>", tabs_at) + len("</div>")
    tabs_bar = main_body[tabs_at:tabs_end]
    main_body = main_body[:tabs_at] + main_body[tabs_end:]
    settings_body, settings_header = _take_header(settings_body)
    on_main = initial_view == "main"
    settings_button = _button(main_header, "settings-btn")
    feedback_button = _button(settings_header, "feedback")
    sec = {name: _section(settings_body, name) for name in (
        "steps", "reorder", "check", "check-hint", "server", "about", "weights", "weights-preview",
        "layout", "layout-preview", "printer", "printer-preview", "footer")}
    # The version, update check and log path sit beside the footer buttons.
    footer = sec["footer"]
    version_row = re.search(r'<div class="version-row">.*?</div>', footer, re.S).group(0)
    footer = footer.replace(version_row, f'<div class="foot-diag">{version_row}{sec["about"]}</div>')

    def card(left: str, label: str, right: str) -> str:
        title, rest = re.match(r"\s*(<h3>.*?</h3>)(.*)", left, re.S).groups()
        return (f'<div class="srow">{title}<div class="srow-body"><div class="srow-l">{rest}</div>'
                f'<div class="srow-r"><div class="label">{label}</div>{right}</div></div></div>')

    settings_view = "\n".join([
        card(sec["server"], "How It Works", sec["steps"]),
        card(sec["reorder"], "Preview", TAB_PREVIEW_HTML),
        card(sec["weights"], "Preview", sec["weights-preview"]),
        card(sec["layout"], "Preview", sec["layout-preview"]),
        card(sec["check"], "Before You Start", sec["check-hint"]),
        card(sec["printer"], "Preview", sec["printer-preview"]),
        footer,
    ])
    return f"""<!doctype html>
<html>
<head>
<meta charset="utf-8">
<link rel="icon" href="{LOGO_DATA_URI}">
<style>
  html, body {{ height: 100%; margin: 0; background: var(--orca-bg); overscroll-behavior-x: none; }}
  body {{ box-sizing: border-box; padding-top: 76px; }}
  .view-hidden {{ display: none !important; }}
  #view-settings {{ min-height: 100%; max-width: 1100px; }}
{_fill(TAB_HEADER_CSS, FONT=FONT_STACK)}
{_scope_css(main_css, "#view-main")}
{_scope_css(settings_css, "#view-settings")}
{TAB_SETTINGS_CSS}
</style>
</head>
<body>
<div id="app-header">
  {LOGO_IMG}<h2>Spooler</h2>
  <span id="tabs-main" class="{_hidden(not on_main)}">{tabs_bar}</span>
  <div class="header-actions">
    <span id="actions-main" class="{_hidden(not on_main)}">{settings_button}</span>
    <span id="actions-settings" class="{_hidden(on_main)}">{feedback_button}</span>
  </div>
</div>
<div id="view-main" class="view {_hidden(not on_main)}">{main_body}</div>
<div id="view-settings" class="view {_hidden(on_main)}">{settings_view}</div>
<script>{TAB_BRIDGE}</script>
<script>(function (orca) {{{main_js}}})(window.__spooler.main);</script>
<script>(function (orca) {{{settings_js}}})(window.__spooler.settings);</script>
<script>(function (bridge) {{{TAB_PREVIEW_JS}}})(window.__spooler.settings);</script>
</body>
</html>
"""


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
                       progress=None, columns=None):
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
        if save_settings(settings):
            log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                     url, settings["low_stock_grams"], settings["plate_check"],
                     settings["plate_margin_percent"])
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

        threading.Thread(target=worker, daemon=True).start()

    def _bambu_sign_in(self, data, window):
        if data.get("action") == "sign_out":
            self._verified_bambu = False

        def worker():
            result = bambu_sign_in(data)
            if window.is_open():
                window.post({"type": "bambu_auth_result", **result})

        threading.Thread(target=worker, daemon=True).start()

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
                                        data.get("spool_columns"))
            if saved:
                self._after_save()
                if self._settings_window is not None:
                    self._settings_window.close()
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

            threading.Thread(target=worker, daemon=True).start()
        elif msg_type == "release" and self._release_url.startswith("https://"):
            open_url(self._release_url)
        elif msg_type == "cancel" and self._settings_window is not None:
            self._settings_window.close()

    def _on_settings_close(self):
        self._settings_window = None

    def on_unload(self):
        # Without this, open windows would outlive OrcaSlicer's shutdown.
        log.info("Unloading")
        if self._panel is not None and self._panel.is_open():
            self._panel.close()
        if self._settings_window is not None and self._settings_window.is_open():
            self._settings_window.close()

    def on_message(self, data):
        msg_type = data.get("type") if isinstance(data, dict) else None
        if msg_type in ("ready", "refresh"):
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
        elif msg_type in ("usage_mode", "usage_book", "usage_undo"):
            threading.Thread(target=lambda: self._panel.post({"type": "usage", "usage": usage_action(data)}), daemon=True).start()
        elif msg_type == "send":
            start_send(self._panel.post)

    def _push_data(self):
        if self._panel is None or not self._panel.is_open():
            return
        url = self._spoolman_url()
        if source() == "spoolman" and not url:
            self._panel.post({
                "type": "spools",
                "ok": False,
                "error": "No Spoolman URL configured yet - click Settings to set one.",
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
            result = load_spools_synced(snapshot)
            self._refreshing = False
            if panel.is_open():
                panel.post({"type": "spools", "low_stock_grams": low_stock_grams,
                            "weight_display": weight_mode(), "show_cart": cart_on(),
                            "spool_columns": spool_columns(), **printer_state(), **result})

        threading.Thread(target=worker, daemon=True).start()

    def _on_panel_close(self):
        self._panel = None

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

    def on_load(self):
        log.info(
            "%s %s loaded (Python %s, %s)",
            PLUGIN_NAME,
            PLUGIN_VERSION,
            platform.python_version(),
            platform.platform(),
        )
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
                elif msg_type in ("usage_mode", "usage_book", "usage_undo"):
                    threading.Thread(target=lambda: self.post_message({"type": "usage", "usage": usage_action(data)}), daemon=True).start()
                elif msg_type == "plate_recheck":
                    threading.Thread(target=recheck, daemon=True).start()
                elif msg_type == "plate_dismiss":
                    _plate.update(payload=None, slots=[])
                elif msg_type == "send":
                    start_send(self.post_message)
            except Exception:
                log.exception("on_message() raised (arg0=%r)", arg0)

        def _spoolman_url(self):
            return get_settings().get("spoolman_url", "")

        def _push_data(self):
            url = self._spoolman_url()
            if source() == "spoolman" and not url:
                self.post_message({
                    "type": "spools",
                    "ok": False,
                    "error": "No Spoolman URL configured yet - click Settings to set one.",
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
                result = load_spools_synced(snapshot)
                self._refreshing = False
                self.post_message({"type": "spools", "low_stock_grams": low_stock_grams,
                                   "weight_display": weight_mode(), "show_cart": cart_on(),
                                   "spool_columns": spool_columns(), **printer_state(), **result})

            threading.Thread(target=worker, daemon=True).start()

        def _save_settings(self, url, low_stock, plate_check=True,
                           plate_margin=DEFAULT_MARGIN, weight="both", cart=False, src="spoolman",
                           progress=None, columns=None):
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
            if save_settings(settings):
                log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                         url, settings["low_stock_grams"], settings["plate_check"],
                         settings["plate_margin_percent"])
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
                "progress": progress_settings(),
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

            threading.Thread(target=worker, daemon=True).start()

        def _bambu_sign_in(self, data, window):
            if data.get("action") == "sign_out":
                self._verified_bambu = False

            def worker():
                result = bambu_sign_in(data)
                if window.is_open():
                    window.post({"type": "bambu_auth_result", **result})

            threading.Thread(target=worker, daemon=True).start()

        def _on_settings(self, data):
            msg_type = data.get("type")
            if msg_type == "ready":
                self._check_connection(self._spoolman_url(), self._settings_window)
            elif msg_type == "test":
                url = (data.get("url") or "").strip()
                self._check_connection(url, self._settings_window, data.get("source"))
            elif msg_type == "save":
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
                                            data.get("spool_columns"))
                if saved:
                    self._after_save()
                    self._settings_window.close()
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

                threading.Thread(target=worker, daemon=True).start()
            elif msg_type == "release" and self._release_url.startswith("https://"):
                open_url(self._release_url)
            elif msg_type == "cancel":
                self._settings_window.close()

        def on_load(self):
            log.info(
                "%s %s loaded as a native tab (Python %s, %s)",
                PLUGIN_NAME,
                PLUGIN_VERSION,
                platform.python_version(),
                platform.platform(),
            )

        def on_unload(self):
            log.info("Unloading")


if _SLICING:

    class SpoolerFilamentCheck(orca.slicing.SlicingPipelineCapabilityBase):
        """After each slice, checks the plate's filament against the spools in Spoolman."""

        def get_name(self):
            return "Spooler Filament Check"

        def execute(self, ctx):
            try:
                if ctx.step == getattr(orca.slicing.Step, "posSlice", None):
                    if _plate["payload"]:
                        threading.Thread(target=clear_plate, daemon=True).start()
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
    result = get_spools(get_settings().get("spoolman_url", ""))
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
        if held != name and (last is None or last[0] != spool or (system and gen > last[1])):
            changes.append((slot, name))
        seen[slot] = (spool, gen)
    return changes


SNAPSHOT_EVENTS = ("PresetSelected", "PresetSaved", "ProjectOpened", "NewProject")


class SpoolerLoadFilaments(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: put the filament each printer slot holds into the plate's filament slots."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Load Printer Filaments"

    def on_lifecycle_event(self, event, ctx):
        # Preset and project events arrive on the UI thread, where the presets may be read;
        # execute() runs on a worker thread, so it uses this snapshot.
        try:
            if any(event == getattr(orca.LifecycleEvent, name, None) for name in SNAPSHOT_EVENTS):
                refresh_snapshot()
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


class SpoolerKeepSlots(orca.script.ScriptPluginCapabilityBase):
    """Plugins > Run: keep the plate's filament slots on what each printer lane holds, until run
    again. OrcaSlicer only lets a running Plugins > Run action change slots, so this one stays."""

    def get_name(self):
        return f"{PLUGIN_NAME}: Keep Slots Synced"

    async def execute(self):
        if _keep["run"] is not None:
            _keep["run"] = None
            return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")
        try:
            names = sync_for(dict(_ui_snap))
        except Exception as exc:
            return orca.ExecutionResult.failure(orca.PluginResult.RecoverableError, str(exc))
        run = _keep["run"] = object()
        seen, synced = {}, time.monotonic()
        try:
            while _keep["run"] is run:
                snap = dict(_ui_snap)
                try:
                    if time.monotonic() - synced > REFRESH_SECS:
                        names, synced = sync_for(snap), time.monotonic()
                    trays = printer_trays(snap["host"])
                    for slot, name in keep_plan(trays, snap["slots"], names, snap.get("current") or [],
                                                snap.get("gen", 0), seen):
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
                await asyncio.sleep(MOON_POLL)
        finally:
            if _keep["run"] is run:
                _keep["run"] = None
        return orca.ExecutionResult.success("Stopped keeping the filament slots synced.")


@orca.plugin
class SpoolerPlugin(orca.base):
    def register_capabilities(self):
        if _PAGES:
            orca.register_capability(SpoolerPage)
        else:
            orca.register_capability(SpoolerWindow)
        if _SLICING:
            orca.register_capability(SpoolerFilamentCheck)
        orca.register_capability(SpoolerLoadFilaments)
        orca.register_capability(SpoolerKeepSlots)
