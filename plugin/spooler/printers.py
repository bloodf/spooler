# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""The printers Spooler knows: settings, slots and their saved state."""

import re
import threading

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
        return text if len(text) <= 64 and re.fullmatch(r"[A-Za-z0-9.\-]+", text) else ""  # never a cut-short host
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
    saved = (settings or _core.get_settings()).get("moon_slots")
    mine = saved.get(_sources.source()) if isinstance(saved, dict) else None
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
    # One extruder slot when Moonraker has no Spoolman integration to hold the active spool (found["solo"]).
    solo = bool(found.get("solo")) and count < 2 and not saved.get("gates")
    tools = (list(saved.get("tools") or []) + [None] * MOON_TOOLS)[:max(count, 1)] if count >= 2 or solo else []
    gates = [] if tools else list(saved.get("gates") or [])
    entry["units"] = [{"kind": "tool", "slots": [s]} for s in tools] + ([{"kind": "gate", "slots": gates}] if gates else [])
    return entry


def printers_cfg() -> list[dict]:
    """Saved printers, then the Moonraker printers found in OrcaSlicer's printer presets."""
    settings = _core.get_settings()
    saved = settings.get("printers")
    printers = parse_printers(saved.get(_sources.source())) if isinstance(saved, dict) else []
    moon = moon_saved(settings)
    return printers + [moon_entry(p, moon.get(p["id"])) for p in _moonraker._auto_printers]


def save_printers(value: object) -> None:
    """Save the printers from the page (or a slice fill): the ones added by hand, and the slots set by hand on
    Klipper printers found from the presets. A Klipper printer missing from value keeps what it had."""
    with _printers_lock:
        _save_printers(value)


def _save_printers(value: object) -> None:
    _core.update_settings(lambda settings: _printer_changes(settings, value))
    _live_updates.prune_codes()  # a printer removed takes its access code with it
    _live_updates._local_sync()


def _printer_changes(settings: dict, value: object) -> dict:
    """The printers and moon_slots keys after saving value over these settings."""
    saved = dict(settings["printers"]) if isinstance(settings.get("printers"), dict) else {}
    seen: set = set()
    saved[_sources.source()] = parse_printers(value, seen)
    moon = dict(settings["moon_slots"]) if isinstance(settings.get("moon_slots"), dict) else {}
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
    moon[_sources.source()] = {**kept, **new}
    return {"printers": saved, "moon_slots": moon}


_printers_rev = {"n": 0}  # bumped when Spooler itself changes the saved printers (slice fill)
# One writer of the saved printers at a time: the page, a slice fill and a pick answer run on different threads.
_printers_lock = threading.RLock()


def bump_printers_rev() -> None:
    with _printers_lock:
        _printers_rev["n"] += 1


def printer_state() -> dict:
    codes = _live_updates.read_codes()
    # Every printer stays listed, a preset's host that is neither Moonraker nor Anycubic too (link "none", said on
    # its card): hiding it made the printers found from the presets vanish once the first probe answered.
    printers = [dict(p, has_code=p.get("kind") == "moonraker" or bool(codes.get(_live_updates._code_key(p["id"]))))
                for p in printers_cfg()]
    live = any(p["ip"] and p["has_code"] for p in printers)
    return {"printers": printers, "live_ok": live, "usage": _netprinters.usage_state(), "progress": _core.progress_settings(),
            "stats": _core.stats_settings(), "printers_rev": _printers_rev["n"], "slice_picks": list(_netprinters._slice_picks),
            "slice_map": _netprinters.slice_map(), "printer_presets": list(_filament_profiles._ui_snap.get("presets") or [])}


def live_message() -> dict:
    """The Printer tab's poll reply: live state, the booking list, and the saved printers when
    Spooler changed them itself (a slice filled the toolheads), so the page doesn't save over it."""
    msg = {"type": "live", "live": _live_updates.live_poll(), "usage": _netprinters.usage_state(), "printers_rev": _printers_rev["n"],
           "slice_picks": list(_netprinters._slice_picks), "printer_presets": list(_filament_profiles._ui_snap.get("presets") or []), "rfid": _rfid.rfid_offers()}
    if _printers_rev["n"]:
        msg["printers"] = printer_state()["printers"]
    return msg


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import core as _core  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
