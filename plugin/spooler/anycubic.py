# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Anycubic printers (Kobra X, Kobra S1)."""

import base64
import hashlib
import http.client
import json
import os
import re
import socket
import ssl
import threading
import time
import urllib.error
import urllib.parse
from pathlib import Path

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


KX_MAX_BODY = 1024 * 1024  # /info and /ctrl answer a few hundred bytes


def _kx_http(url: str, post: bool = False) -> object:
    """The JSON a printer answers at url, through http.client, not urllib.request: OrcaSlicer's plugin audit
    matches urllib.Request against the full URL, and the credentials request carries a fresh ts/nonce/sign query
    each time, so every call asked the user again. http.client's network events are matched by host, so one
    grant of the printer's address covers /info, the credentials and MQTT. Raises OSError (HTTPError for a
    non-200 answer) when the printer can't be read, ValueError when the answer isn't JSON."""
    parts = urllib.parse.urlsplit(url)
    if parts.scheme not in ("http", "https") or not parts.hostname:
        raise ValueError("The printer's LAN address isn't http")
    kind = http.client.HTTPSConnection if parts.scheme == "https" else http.client.HTTPConnection
    conn = kind(parts.hostname, parts.port, timeout=_core.TIMEOUT)
    try:
        conn.request("POST" if post else "GET", (parts.path or "/") + (f"?{parts.query}" if parts.query else ""),
                     body=b"" if post else None, headers={"Connection": "close"})
        resp = conn.getresponse()
        if resp.status != 200:
            raise urllib.error.HTTPError(f"{parts.scheme}://{parts.netloc}{parts.path}", resp.status, resp.reason,
                                         resp.headers, None)
        body = resp.read(KX_MAX_BODY + 1)
    except http.client.HTTPException as exc:  # garbled HTTP: something else answers there
        raise ValueError(f"not an Anycubic LAN-mode printer ({type(exc).__name__})") from None
    finally:
        conn.close()
    if len(body) > KX_MAX_BODY:
        raise ValueError("The printer's answer is too large")
    return json.loads(body.decode("utf-8"))


def kx_info(base: str) -> dict:
    """The printer's LAN-mode details, or raises."""
    info = _kx_http(f"http://{_host(base)}:{KX_INFO_PORT}/info")
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
    url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    return kx_decrypt_bundle(_kx_http(url, post=True), info["token"])


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
    _core.log.info("Kobra capture: type=%s topic=%s keys=%s data keys=%s sample=%s", kind,
             "/".join(topic.split("/")[7:]), sorted(doc) if isinstance(doc, dict) else [],
             sorted(data) if isinstance(data, dict) else type(data).__name__,
             json.dumps(kx_redact(doc))[:KX_CAPTURE_CHARS])


def _kx_colour(value: object) -> str:
    if isinstance(value, list) and len(value) >= 3 and all(isinstance(v, int) for v in value[:3]):
        return "".join(f"{max(0, min(255, v)):02X}" for v in value[:3])
    return ""


def spool_at_kx_slot(spools: list[dict], names: tuple, number: int) -> dict | None:
    """The spool Kobra Control bound to ACE slot S<number> (1-based, box * 4 + slot + 1): its Spoolman location
    is exactly "<printer name> S<n>". Between spools with that location the one used last wins, as there."""
    keys = {_moonraker._location_key(_moonraker.location_for(name, "S", number)) for name in names}
    found = [s for s in spools if not s.get("archived") and _moonraker._location_key(s.get("location")) in keys]
    return max(found, key=lambda s: str(s.get("last_used") or "")) if found else None


def kx_tray(slot: int, item: object, spools: list[dict], target: str, number: int = 0) -> dict:
    """A Bambu-shaped tray for one Anycubic slot, matched to a Spoolman spool: the one Kobra Control bound to
    slot S<number> (number > 0), else by material and colour. The ACE's consumables_percent is a printer
    percentage only for a slot with no Spoolman spool (Kobra Control draws a linked slot from Spoolman too) and
    below 100: the ACE answers 100 for every spool it can't measure, so 100 is no reading."""
    item = item if isinstance(item, dict) else {}
    kind = str(item.get("type") or "").strip()
    colour = _kx_colour(item.get("color"))
    if not kind or item.get("status") == 0:
        return {"id": str(slot)}
    percent = item.get("consumables_percent")
    remain = percent if isinstance(percent, (int, float)) and not isinstance(percent, bool) and 0 <= percent < 100 else None
    bound = spool_at_kx_slot(spools, _peers.location_names(target), number) if number > 0 else None
    if bound is not None:  # the bound spool's own colour: its name, id and swatch agree, whatever the ACE read
        return _moonraker._spool_tray(slot, bound, target, linked="kobracontrol")
    found = _plate_check.match_spools({"preset": "", "vendor": "", "material": kind, "colour": colour}, spools) if colour else []
    if found:
        return dict(_moonraker._spool_tray(slot, found[0], target), tray_color=colour + "FF")
    return {"id": str(slot), "tray_type": kind, "tray_color": colour + "FF" if colour else "",
            "tray_sub_brands": kind, "remain": remain, "spool_id": None, "profile": ""}


def _kx_box_id(box: object) -> int | None:
    """The firmware's box id: -1 the spool holder, >= 0 an ACE. A box without a readable id is neither."""
    raw = box.get("id") if isinstance(box, dict) else None
    return raw if isinstance(raw, int) and not isinstance(raw, bool) and raw >= -1 else None


def _kx_index(slot: object) -> int | None:
    raw = slot.get("index") if isinstance(slot, dict) else None
    return raw if isinstance(raw, int) and not isinstance(raw, bool) else None


def _kx_place(slots: list, size: int) -> list:
    """A box's slots by their own firmware "index" (0..size-1), so a shuffled report keeps each spool in its
    slot; a box whose slots carry no index at all is positional. With some indexed and some not, only the
    indexed ones count."""
    if all(isinstance(s, dict) and "index" not in s for s in slots):  # no index at all; a bad one is never a position
        return slots[:size]
    placed = {_kx_index(s): s for s in slots if _kx_index(s) is not None and 0 <= _kx_index(s) < size}
    return [placed.get(i) for i in range(max(placed, default=-1) + 1)]


def kx_merge_boxes(old: object, new: object) -> list:
    """The boxes after a report: one naming only some boxes updates those by id and keeps the rest, whatever
    its action (a partial getInfo too); only an empty list, the printer saying it has none, clears them."""
    new = [b for b in new if isinstance(b, dict)] if isinstance(new, list) else []
    if not new or not isinstance(old, list):
        return new
    keyed = {_kx_box_id(b): b for b in old if isinstance(b, dict)}
    for box in new:
        was = keyed.get(_kx_box_id(box), {})
        merged = {**was, **box}  # a report without slots (drying, feed state) keeps the box's slots
        a, b = was.get("slots"), box.get("slots")
        # A report naming only some slots (by their own index) changes those and keeps the box's others.
        if isinstance(a, list) and isinstance(b, list) and all(_kx_index(s) is not None for s in a + b):
            merged["slots"] = list({**{_kx_index(s): s for s in a}, **{_kx_index(s): s for s in b}}.values())
        keyed[_kx_box_id(box)] = merged
    return [b for k, b in keyed.items() if k is not None]


def kx_report(boxes: object, external: object, spools: list[dict], target: str = "") -> dict:
    """A Bambu-shaped report from multiColorBox and extfilbox replies, numbered as kobracontrol's ace.py does:
    an ACE (box id >= 0) is the unit of its id with 4 slots; the spool holder (box id -1) is the unit after the
    last ACE (0 alone), cut to 3 slots when an ACE is there. Each unit says its "source" ("ace" or "holder"),
    so none is made up for a box the printer didn't report, and report order doesn't matter."""
    # Slots only: no gcode_state or job keys, so live_apply never books an Anycubic print (Kobra Control
    # books it; tests/test_kobra.py NoKobraBookingTest). If Spooler ever books Anycubic prints, publish
    # "books": ["anycubic"] under "provides" in presence.json in the same change: Kobra Control then stops
    # booking in that Spoolman.
    aces: dict[int, list] = {}
    holder = None
    for box in boxes if isinstance(boxes, list) else []:
        if _kx_box_id(box) is None:
            continue
        # Every ACE counts for the holder's place, even one that has reported no slots yet.
        slots = box["slots"] if isinstance(box.get("slots"), list) else []
        if _kx_box_id(box) == -1:
            holder = slots
        else:
            aces[_kx_box_id(box)] = _kx_place(slots, 4)
    units = [{"id": str(n), "source": "ace", "box": n, "size": 4,
              "tray": [kx_tray(i, s, spools, target, n * 4 + i + 1) for i, s in enumerate(aces[n])]}
             for n in sorted(aces)]
    if holder is not None:
        pos, cap = max(aces, default=-1) + 1, 3 if aces else 4
        held = _kx_place(holder, cap)
        # With an ACE the holder is always its 3 positions; alone it is as many as the printer reported.
        units.append({"id": str(pos), "source": "holder", "box": -1, "size": 3 if aces else max(1, len(held)),
                      "tray": [kx_tray(i, s, spools, target, pos * 4 + i + 1) for i, s in enumerate(held)]})
    report: dict = {"ams": {"ams": units}}
    if isinstance(external, dict):
        report["vt_tray"] = dict(kx_tray(_moonraker.MOON_EXT, external, spools, target), id=str(_moonraker.MOON_EXT))
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
    files = (_core.DATA_DIR / f".kx-{_moonraker._slug(pid)}-1.pem", _core.DATA_DIR / f".kx-{_moonraker._slug(pid)}-2.pem")
    state = {"boxes": None, "external": None}
    command = f"{KX_TOPIC}/web/printer/{model}/{device}"
    capture, seen = _core.get_settings().get("kx_capture") is True, set()
    with _kx_socket(host, bundle, files) as sock:
        sock.settimeout(5)
        sock.sendall(_live_updates._mqtt_connect(bundle["username"], bundle["password"]))
        packet = _live_updates._mqtt_read(sock)
        if not packet or packet[0] >> 4 != 2 or len(packet[1]) < 2 or packet[1][1] != 0:
            raise ConnectionError("The printer refused the live connection")
        for number, topic in enumerate((f"{KX_TOPIC}/printer/+/{model}/{device}/#",
                                        f"{KX_TOPIC}/printer/public/{model}/{device}/#"), 1):
            sock.sendall(_live_updates._mqtt_subscribe(topic, number))
        # monotonic() counts from boot, so "never" must be -inf, not 0.
        asked = ping = float("-inf")
        # Silence counts from the connection: a printer that never reports is dropped and tried
        # again (with the usual backoff) like one that stops reporting.
        heard = time.monotonic()
        _live_updates._live["links"][pid] = "waiting"
        alive = lambda: _live_updates._live_active() and not stop.is_set()  # noqa: E731
        while alive():
            now = time.monotonic()
            if now - asked > KX_REQUEST_SECS:
                sock.sendall(_live_updates._mqtt_publish(f"{command}/multiColorBox", kx_request("multiColorBox")))
                sock.sendall(_live_updates._mqtt_publish(f"{command}/extfilbox", kx_request("extfilbox")))
                if capture:
                    # A read-only status query ({"type": "info", "action": "query"}, answered with the
                    # print "project" state and progress), as sent by
                    # https://github.com/HughKantsime/runsodin backend/modules/printers/adapters/anycubic_lan.py
                    sock.sendall(_live_updates._mqtt_publish(f"{command}/info", kx_request("info", "query")))
                asked = now
            if now - ping > _live_updates.LIVE_PING:
                sock.sendall(b"\xc0\x00")
                ping = now
            packet = _live_updates._mqtt_read(sock, alive)
            if packet:
                heard = time.monotonic()
            elif time.monotonic() - heard > _live_updates.LIVE_DEAD:
                raise ConnectionError("The printer stopped answering")
            message = _live_updates._mqtt_message(packet) if packet and packet[0] >> 4 == 3 else None
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
                state["boxes"] = kx_merge_boxes(state["boxes"], data["multi_color_box"])
            elif kind == "extfilbox" and isinstance(data, dict):
                state["external"] = data
            else:
                continue
            # Every slot is in each report (empty ones as {"id": n}), so nothing goes stale.
            report = kx_report(state["boxes"] or [], state["external"], _core._spool_cache["spools"] or [],
                               _peers.target_for_host(base))
            _live_updates.live_apply(pid, link["name"], report, link=pid, full=True)
            with _live_updates._live_lock:
                if pid in _live_updates._live["printers"]:
                    _live_updates._live["printers"][pid]["bind"] = "S"
            _live_updates._live["links"][pid] = "live"


def printer_kind(base: str) -> str:
    """'moonraker', 'anycubic' or 'none'. Raises URLError when nothing answers at all."""
    try:
        if _moonraker.is_moonraker(base):
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
    while _live_updates._live_active() and not stop.is_set():
        busy = False
        try:
            if kind is None:
                kind = printer_kind(link["ip"])
                if kind == "none":
                    _live_updates._live["links"][pid] = "none"
                    _core.log.info("%s is neither a Moonraker nor an Anycubic printer, not reading it", link["name"])
                    return
            if kind == "anycubic":
                _moonraker.moon_found(link["ip"], 1, True)  # its ACE units report their own spools
                _kx_session(pid, link, stop)
                continue
            # Every slot is reported each time (empty ones as {"id": n}), so nothing goes stale.
            doc, heads = _moonraker.moon_poll(link["ip"])
            if stop.is_set():
                break
            busy = doc["print"].get("gcode_state") in _rfid.LIVE_STATES
            if time.monotonic() - checked > 60 and not busy:
                # Re-checked while idle only, so a booking rule can't change in the middle of a print.
                checked = time.monotonic()
                try:
                    connected = _moonraker.moon_spoolman_connected(link["ip"])
                except (urllib.error.URLError, OSError, ValueError):
                    connected = True  # unknown: assume it books, never count twice
                with _live_updates._live_lock:
                    state = _live_updates._live["printers"].setdefault(pid, {"name": link["name"], "units": {}, "ext": {},
                                                               "time": 0.0, "link": pid})
                    # The Snapmaker U1 (toolheads) is booked by u1control; a Moonraker with Spoolman books itself.
                    state["book_ok"] = not doc.get("u1") and not doc.get("hh") and not connected
            _live_updates.live_apply(pid, link["name"], doc, link=pid, full=True)
            with _live_updates._live_lock:
                if stop.is_set():
                    # Removed while this poll ran: don't leave it behind.
                    _live_updates._live["printers"].pop(pid, None)
                else:
                    _moonraker.moon_mark(pid, doc, heads)
            _live_updates._live["links"][pid] = "live"
            fails = 0
            _core._report(f"Printer {link['name']}", None)
        except Exception as exc:
            fails += 1
            _live_updates._live["links"][pid] = "unreachable"
            # One message per kind of failure, so an offline printer logs once, not every retry.
            reason = "not reachable" if isinstance(exc, (urllib.error.URLError, OSError)) else str(exc)
            _core._report(f"Printer {link['name']}", reason)
        stop.wait((_moonraker.MOON_POLL if busy else _moonraker.MOON_IDLE) if not fails else _live_updates.LIVE_RETRY[min(fails - 1, len(_live_updates.LIVE_RETRY) - 1)])
    _live_updates._link_done(pid, stop)


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import core as _core  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import rfid as _rfid  # noqa: E402
