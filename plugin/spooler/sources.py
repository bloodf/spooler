# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Spool sources: the Spoolman server and the Bambu Cloud account (read-only)."""

import base64
import hashlib
import json
import math
import re
import socket
import time
import urllib.error
import urllib.parse
import urllib.request

from . import core as _core


class BadAddress(urllib.error.URLError):
    """An address Spooler won't open as Spoolman's; its reason is already a sentence for the page."""


def _spoolman_open(base: str, path: str, method: str = "GET", body: object = None) -> object:
    """One Spoolman API request with a JSON body and answer; raises urllib's errors. Only http(s):
    urllib would also read file:// and ftp:// addresses typed or synced in as Spoolman's."""
    url, auth = _core.split_auth(f"{base.rstrip('/')}/api/v1/{path}")
    if urllib.parse.urlsplit(url).scheme not in ("http", "https"):
        raise BadAddress(_i18n.tr("The Spoolman address must start with http:// or https://."))
    data = None if body is None else json.dumps(body).encode("utf-8")
    request = urllib.request.Request(url, data=data, method=method,
                                     headers={"Content-Type": "application/json", **auth})
    try:
        with urllib.request.urlopen(request, timeout=_core.TIMEOUT) as resp:
            return json.loads(resp.read().decode("utf-8") or "null")
    finally:
        if method != "GET":
            _core._own_write["at"] = time.monotonic()


def clean_url(url: str | None) -> str:
    return (url or "").strip().rstrip("/")


def _why(exc: OSError) -> str:
    """What kept a request from being answered: "refused", "timeout", "unknown" (no such host) or "other". The system's
    own words for it ("[Errno 61] Connection refused") go to the log: they say nothing to the person reading the page."""
    reason = getattr(exc, "reason", exc)
    if isinstance(reason, ConnectionRefusedError):
        return "refused"
    if isinstance(reason, TimeoutError) or "timed out" in str(reason):
        return "timeout"
    return "unknown" if isinstance(reason, socket.gaierror) else "other"


def unreachable(exc: OSError, url: str = "") -> str:
    """Why Spoolman (at url, else at the saved address) gave no answer, as a sentence for the page."""
    where = _core.split_auth(url or _core.get_settings().get("spoolman_url") or "")[0]
    _core.log.warning("Spoolman at %s gave no answer: %s", where, getattr(exc, "reason", exc))
    if isinstance(exc, BadAddress):
        return str(exc.reason)
    if isinstance(exc, urllib.error.HTTPError):
        return _i18n.tr("Spoolman at {url} answered with an error (HTTP {code}).", url=where, code=exc.code)
    why = _why(exc)
    if why == "refused":
        return _i18n.tr("Spoolman isn't answering at {url}. Is it running?", url=where)
    if why == "timeout":
        return _i18n.tr("Spoolman at {url} took too long to answer.", url=where)
    if why == "unknown":
        return _i18n.tr("{url} wasn't found on your network.", url=where)
    return _i18n.tr("Spooler couldn't reach Spoolman at {url}.", url=where)


def no_answer(exc: OSError, who: str) -> str:
    """Why another service (Bambu Cloud, GitHub) gave no answer: the service, then the cause in a few words."""
    _core.log.warning("%s gave no answer: %s", who, getattr(exc, "reason", exc))
    why = _why(exc)
    cause = (_i18n.tr("the connection was refused") if why == "refused" else _i18n.tr("it took too long to answer") if why == "timeout"
             else _i18n.tr("its address wasn't found") if why == "unknown" else _i18n.tr("no connection"))
    return _i18n.tr("Could not reach {who} ({reason})", who=who, reason=cause)


def ping(spoolman_url: str) -> dict:
    """Ask Spoolman for its version, which doubles as a connection test.

    Returns ``{"ok": True, "version": "..."}`` or ``{"ok": False, "error": "..."}``.
    """
    if not spoolman_url:
        return {"ok": False, "error": _i18n.tr("No Spoolman URL configured yet")}
    try:
        data = _spoolman_open(spoolman_url, "info")
        if not isinstance(data, dict):
            raise ValueError("not a JSON object")
    except OSError as exc:   # no answer (URLError), or one that broke off (a timeout while reading)
        return {"ok": False, "error": unreachable(exc, spoolman_url)}
    except ValueError:
        # Not JSON, or not an object: a web page or another service at that address. Raising here
        # would leave the page's Test Connection waiting, and every later test ignored.
        error = _i18n.tr("{url} answered, but not like Spoolman does", url=spoolman_url)
        _core.log.warning("Connection test failed: %s", error)
        return {"ok": False, "error": error}
    except Exception as exc:
        _core.log.exception("Connection test failed")
        return {"ok": False, "error": str(exc)}
    version = data.get("version", "unknown")
    _core.log.info("Connected to Spoolman %s at %s", version, spoolman_url)
    return {"ok": True, "version": version}


BAMBU_HOSTS = {"global": "https://api.bambulab.com", "china": "https://api.bambulab.cn"}
BAMBU_REGIONS = {"global": "Global", "china": "China"}
BAMBU_PATH = "/v1/design-user-service/my/filament/v2"
BAMBU_PAGE = 100
BAMBU_PAGES = 50
BAMBU_TIMEOUT = 10
BAMBU_KEY = "bambu"
BAMBU_UA = f"BBL-Slicer/v02.08.01.51 (OrcaSlicer; {_core.PLUGIN_NAME}/{_core.PLUGIN_VERSION})"
AUTH_FILE = _core.DATA_DIR / "bambu_auth.json"
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
    return parse_source(_core.get_settings().get("spool_source"))


def source_name() -> str:
    return "Bambu Cloud" if source() == "bambu" else "Spoolman"


def spool_key() -> str:
    return BAMBU_KEY if source() == "bambu" else _core.get_settings().get("spoolman_url", "")


def configured() -> bool:
    return bool(spool_key())


# What the spool source answered, per source key: {"fails": failed answers in a row, "error": the
# last failure, "good": what the last good answer said (Spoolman's version, the Bambu account) or
# None before any}. Written by the reads and connection tests that run anyway, so the Requirements
# row and auto-send never ask on their own.
_heard: dict = {}
FAILS_OFF = 2  # one failed background read can be a blip; two in a row turn the source off


def heard(key: str, ok: object, details: object = None, sure: bool = False) -> None:
    """Note an answer. details None keeps what the last good answer said. sure: a connection test
    the user sees (Settings, Check again) counts at once, not after FAILS_OFF reads."""
    key = clean_url(key)
    old = _heard.get(key) or {"fails": 0, "error": "", "good": None}
    if ok:
        good = (old["good"] or "") if details is None else str(details)
        _heard[key] = {"fails": 0, "error": "", "good": good}
    else:
        fails = max(old["fails"] + 1, FAILS_OFF if sure else 0)
        _heard[key] = {"fails": fails, "error": str(details or ""), "good": old["good"]}


def requirements() -> list[dict]:
    """The active spool source as a requirement: {id, status, details}. status: ok, missing (never
    reached: the install help applies), unreachable (reached earlier this session) or unknown (not
    heard from yet). No network: what the reads and connection tests already heard."""
    src, key = source(), clean_url(spool_key())
    if not key:
        return [{"id": src, "status": "missing", "details": _i18n.tr("No Spoolman URL configured yet")}]
    if src == "bambu":
        auth = read_auth()
        if not auth["ok"]:
            return [{"id": src, "status": "missing", "details": auth.get("error") or "", "signin": True}]
    entry = _heard.get(key)
    if entry is None or (entry["fails"] < FAILS_OFF and entry["good"] is None):
        return [{"id": src, "status": "unknown", "details": ""}]
    if entry["fails"] < FAILS_OFF:
        return [{"id": src, "status": "ok", "details": entry["good"]}]
    status = "missing" if entry["good"] is None else "unreachable"
    return [{"id": src, "status": status, "details": entry["error"]}]


def source_failing() -> bool:
    """The saved source failed FAILS_OFF answers in a row. No network: only what was heard."""
    return (_heard.get(clean_url(spool_key())) or {"fails": 0})["fails"] >= FAILS_OFF


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
    region = _i18n.tr(region)
    if auth.get("user"):
        return _i18n.tr("Signed in as {user} ({region})", user=auth["user"], region=region)
    return _i18n.tr("Signed in ({region})", region=region)


def read_auth() -> dict:
    """Sign-in result: ``{"ok": True, token, ...}`` or ``{"ok": False, "error", ...}``."""
    try:
        data = json.loads(AUTH_FILE.read_text(encoding="utf-8"))
        token = data["access_token"]
    except FileNotFoundError:
        return {"ok": False, "account": _i18n.tr("Signed out"), "signin": True, "error": _i18n.tr("Signed out")}
    except (OSError, ValueError, KeyError, TypeError):
        _core.log.exception("Could not read %s", AUTH_FILE)
        return {"ok": False, "account": _i18n.tr("Signed out"), "signin": True,
                "error": _i18n.tr("Your saved Bambu sign-in is unreadable")}
    auth = {"token": token, "region": parse_region(data.get("region")),
            "user": str(data.get("account") or "")}
    auth["account"] = account_text(auth)
    expiry = jwt_expiry(token)
    if expiry is not None and expiry < time.time():
        return {**auth, "ok": False, "account": _i18n.tr("Sign-in expired"), "signin": True,
                "error": _i18n.tr("Your Bambu sign-in has expired")}
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
    return _i18n.tr("Bambu blocked the request (HTTP 403)") if code == 403 else _i18n.tr("Bambu Cloud returned an error (HTTP {code})", code=code)


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
        _core.log.warning("Bambu Cloud %s answered HTTP %s: %s", path, exc.code, raw[:200])
        raise BambuError(_bambu_message(exc.code, raw)) from None
    except urllib.error.URLError as exc:
        raise BambuError(no_answer(exc, "Bambu Cloud")) from None
    try:
        data = json.loads(raw) if raw.strip() else {}
    except ValueError:
        raise BambuError(_i18n.tr("Bambu Cloud sent a reply Spooler doesn't understand")) from None
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
            _filament_profiles._write_json(AUTH_FILE, {"access_token": token, "region": region, "account": account}, mode=0o600)
        except OSError as exc:
            _core.log.warning("Could not save the Bambu sign-in: %s", exc)
            raise BambuError(_i18n.tr("Signed in, but Spooler could not save the sign-in to {folder}", folder=AUTH_FILE.parent)) from None
        _core._spool_cache.update(url="", time=0.0, spools=[])
        _core.log.info("Signed in to Bambu Cloud (%s)", region)
        return {"ok": True, "step": "done"}
    _pending.update(region=region, account=account)
    if reply.get("loginType") == "verifyCode":
        _send_code(region, account)
        return {"ok": True, "step": "code"}
    if reply.get("loginType") == "tfa" or reply.get("tfaKey"):
        _pending["tfa_key"] = str(reply.get("tfaKey") or "")
        return {"ok": True, "step": "tfa"}
    raise BambuError(_i18n.tr("Bambu Cloud didn't sign you in"))


def bambu_sign_in(data: dict) -> dict:
    """One sign-in step: password, then the 2FA code if asked."""
    action = data.get("action")
    try:
        if action == "sign_out":
            AUTH_FILE.unlink(missing_ok=True)
            _pending.clear()
            _core._spool_cache.update(url="", time=0.0, spools=[])
            return {"ok": True, "step": "out"}
        if action == "password":
            region = parse_region(data.get("region"))
            account = str(data.get("account") or "").strip()
            password = str(data.get("password") or "")
            if not account or not password:
                raise BambuError(_i18n.tr("Enter your Bambu email and password"))
            reply, cookies = _bambu_post(region, LOGIN_PATH, {"account": account, "password": password})
            return _after_login(region, account, reply, cookies)
        if not _pending:
            raise BambuError(_i18n.tr("Your sign-in timed out. Enter your email and password again"))
        region, account = _pending["region"], _pending["account"]
        if action == "resend":
            _send_code(region, account)
            return {"ok": True, "step": "code"}
        code = str(data.get("code") or "").strip()
        if not code:
            raise BambuError(_i18n.tr("Enter your Bambu Lab verification code"))
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
        raise ValueError(_i18n.tr("Bambu Cloud sent a reply Spooler doesn't understand"))
    return data


def fetch_bambu(auth: dict) -> list[dict]:
    hits: list[dict] = []
    offset = 0  # counts every item the cloud sent, so a skipped non-object never shifts the next page
    for _ in range(BAMBU_PAGES):
        data = _bambu_page(auth, offset)
        offset += len(data["hits"])
        page = [item for item in data["hits"] if isinstance(item, dict)]
        hits += page
        total = data.get("total")
        if not data["hits"] or not isinstance(total, int) or offset >= total:
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
            _i18n.tr("slot {n}", n=item["slotId"]) if item.get("slotId") not in (None, "") else "",
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
        _core.log.warning("Bambu Cloud answered HTTP %s: %s", exc.code, body)
        if exc.code == 401:
            return {"ok": False, "error": _i18n.tr("Bambu Cloud didn't accept your sign-in"),
                    "account": auth["account"], "signin": True}
        return {"ok": False, "error": _i18n.tr("Bambu Cloud returned an error (HTTP {code})", code=exc.code),
                "account": auth["account"]}
    except urllib.error.URLError as exc:
        return {"ok": False, "error": no_answer(exc, "Bambu Cloud"), "account": auth["account"]}
    except Exception as exc:
        _core.log.exception("Bambu Cloud request failed")
        return {"ok": False, "error": str(exc), "account": auth["account"]}
    spools = [spool for spool in map(map_bambu, hits) if spool]
    seen = sorted({(sp["ams"]["printer"], str(sp["ams"]["unit"]), str(sp["ams"]["slot"]))
                   for sp in spools if "ams" in sp})
    if seen != _ams_logged:
        _ams_logged[:] = seen
        _core.log.info("Spools in printers (printer, ams, slot): %s", seen)
    if len(spools) != len(hits):
        _core.log.info("Skipped %d Bambu Cloud spools with no remaining weight", len(hits) - len(spools))
    if hits and not spools:
        _core.log.warning("No Bambu Cloud spool had a netWeight (keys: %s)", ", ".join(sorted(hits[0])))
    return {"ok": True, "auth": auth, "spools": spools}


def get_bambu_spools() -> dict:
    result = bambu_fetch()
    if not result["ok"]:
        error = _i18n._sentences([result["error"] + _i18n.tr("."), _i18n.tr(SIGN_IN)]) if result.get("signin") else result["error"]
        _core._report("Spool list", error)
        heard(BAMBU_KEY, False, error)
        return {"ok": False, "error": error}
    _core._report("Spool list", None)
    heard(BAMBU_KEY, True, result["auth"]["account"])
    _core._spool_cache.update(url=BAMBU_KEY, time=time.monotonic(), spools=result["spools"])
    return {"ok": True, "spools": result["spools"]}


def bambu_ping() -> dict:
    """Bambu Cloud connection test result."""
    result = bambu_fetch()
    if not result["ok"]:
        _core.log.warning("Bambu Cloud test failed: %s", result["error"])
        return {"ok": False, "error": result["error"], "account": result.get("account", ""),
                "signin": bool(result.get("signin"))}
    _core.log.info("Connected to Bambu Cloud, %d spools", len(result["spools"]))
    return {"ok": True, "count": len(result["spools"]), "account": result["auth"]["account"]}


def load_spools() -> dict:
    with _spoolman_sync.pinned_origin() as origin:
        if origin[0] != BAMBU_KEY:
            _filament_profiles.ensure_fields()
        result = get_bambu_spools() if origin[0] == BAMBU_KEY else _core.get_spools(origin[0])
    for sp in result.get("spools") or []:
        sp["rfid_tags"] = sorted(_netprinters.spool_tags(sp))
        sp["u1_bound"] = _rfid.u1_bound(sp.get("location"))
    first = _core.use_first_id(result.get("spools") or [])
    for sp in result.get("spools") or []:
        sp["use_first"] = first.get((sp.get("filament") or {}).get("id")) == sp.get("id")
    table = _core.drying_settings()
    for sp in result.get("spools") or []:
        sp["dry_days"] = _core.drying_days((sp.get("filament") or {}).get("material"), table)
    return result


LIST_FILE = "spool-list.json"
# The last good spool list: served at once while Spoolman is read again (stale-while-revalidate), also after a restart.
# Memory first, <data folder>/spool-list.json after a restart. Keyed by a hash of the source and the archived setting,
# so a list never reaches another source (the address may hold a password: it is never written).
_listed: dict = {"key": "", "spools": None, "sig": "", "at": 0.0}  # at: when it was read (epoch s)


def list_key(origin_key: str) -> str:
    return hashlib.sha256(f"{origin_key}\n{_core.display_settings()['archived']}".encode("utf-8")).hexdigest()[:16]


def listed_put(origin_key: str, spools: list[dict]) -> None:
    """Keep a list just read, and write it down when it differs from the last one written. Never raises."""
    key = list_key(origin_key)
    sig = hashlib.sha256(json.dumps(spools, separators=(",", ":"), sort_keys=True).encode("utf-8")).hexdigest()
    changed = (_listed["key"], _listed["sig"]) != (key, sig)
    _listed.update(key=key, spools=spools, sig=sig, at=time.time())
    if changed:
        try:
            _filament_profiles._write_json(_core.DATA_DIR / LIST_FILE, {"key": key, "spools": spools}, indent=None)
        except OSError as exc:
            _core.log.warning("Could not write %s: %s", LIST_FILE, exc)


def listed_get(origin_key: str) -> list[dict] | None:
    """The last good list of this source, or None."""
    key = list_key(origin_key)
    if _listed["key"] != key or _listed["spools"] is None:
        path = _core.DATA_DIR / LIST_FILE
        try:
            doc, at = json.loads(path.read_text(encoding="utf-8")), path.stat().st_mtime
        except (OSError, ValueError):
            return None
        if not isinstance(doc, dict) or doc.get("key") != key or not isinstance(doc.get("spools"), list):
            return None
        _listed.update(key=key, spools=[s for s in doc["spools"] if isinstance(s, dict)], sig="", at=at)
    return _listed["spools"]


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
