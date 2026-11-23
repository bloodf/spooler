# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Moonraker printers (Klipper, Snapmaker U1)."""

import json
import math
import re
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

from . import printers as _printers

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
    snapshot = _filament_profiles.profile_snapshot()
    if snapshot is not None:
        _auto_printers[:] = auto_printers(snapshot)
        _capabilities.auto_keep_check()  # the first snapshot is what the automatic Keep Slots Synced waits for
    return snapshot


def _moon_result(data: object) -> dict:
    """Moonraker's "result" object; {} for anything else, so callers can always .get() from it."""
    result = data.get("result") if isinstance(data, dict) else None
    return result if isinstance(result, dict) else {}


def _moon_get(base: str, path: str) -> dict:
    with urllib.request.urlopen(base + path, timeout=_core.TIMEOUT) as resp:
        return _moon_result(json.loads(resp.read().decode("utf-8")))


def _moon_post(base: str, path: str, body: dict) -> dict:
    req = urllib.request.Request(base + path, data=json.dumps(body).encode("utf-8"), method="POST",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=_core.TIMEOUT) as resp:
        return _moon_result(json.loads(resp.read().decode("utf-8")))


def _spool_tray(slot: int, spool: dict, target: str, **extra) -> dict:
    """A tray for a slot holding a Spoolman spool. "remain" is only what the printer itself reports (None here):
    Spoolman's weight is shown as Spoolman's, never as the printer's percentage."""
    filament = spool.get("filament") or {}
    colour = _filament_profiles.profile_colour(filament)
    return {"id": str(slot), "tray_type": str(filament.get("material") or ""),
            "tray_color": colour + "FF", "tray_sub_brands": str(filament.get("name") or _rfid._spool_label(spool)),
            "remain": None, "spool_id": spool.get("id"), "filament_id": filament.get("id"),
            "profile": _peers.profile_for_spool(spool, target), **extra}


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


def location_for(name: str, letter: str, number: int) -> str:
    """The Spoolman location that binds a slot: "<printer name> T<n>" (u1control) or "<printer name> S<n>"
    (Kobra Control), n 1-based."""
    return " ".join(f"{name} {letter}{number}".split())[:64]


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
        _core.log.warning("Spools %s all have the location of %s T%d; using %s, the last used",
                    ", ".join(str(s.get("id")) for s in found), (names or ("U1",))[0], number,
                    found[0].get("id"))
    return found[0] if found else None


def slot_tray(slot: int, spool_id: object, uid: str, vendor: str, kind: str, rgba: str, label: str,
              spools: list[dict], target: str, location: tuple | None = None, sub: str = "") -> dict:
    """A Bambu-shaped tray for one printer slot, matched to a Spoolman spool: by the spool id the
    printer reports, else (location = (printer label, toolhead number)) by the Spoolman location
    u1control binds it with, else by RFID tag, else by vendor, material and colour, with the
    printer's filament sub type breaking a tie."""
    spool = _spool_by_id(spool_id, spools)
    linked = "printer" if spool is not None else ""  # the printer itself says which spool: nothing to link here
    if spool is None and location:
        spool = spool_at_location(spools, *location)
        linked = "u1control" if spool is not None else ""
    if spool is None and uid:
        spool = _netprinters.match_spool({"tag_uid": uid}, spools)
    if spool is None and kind and rgba:
        found = _plate_check.match_spools({"preset": "", "vendor": vendor, "material": kind, "colour": rgba[:6],
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
                     label, spools, target, location=(_peers.location_names(target), index + 1), sub=sub)


LANE_MAX = 64  # more lanes than any filament changer has; a bad number can't build a huge list


def lane_units(lanes: dict, spools: list[dict], target: str) -> list[dict]:
    """Moonraker lane_data, as AFC, Happy Hare and other MMU integrations write it, as Bambu-shaped
    units of four trays. Each entry's "lane" is its 0-based slot; an empty material is an empty lane."""
    trays: dict = {}
    for entry in lanes.values():
        index = _live_updates._int(entry.get("lane")) if isinstance(entry, dict) else -1
        if not 0 <= index < LANE_MAX:
            continue
        trays[index] = {"id": str(index % 4)}
        kind = str(entry.get("material") or "").strip()
        if kind:
            colour = _sources._hex6(entry.get("color"))
            vendor = str(entry.get("vendor_name") or "").strip()
            label = " ".join(part for part in (vendor, str(entry.get("name") or "").strip() or kind) if part)
            trays[index] = slot_tray(index % 4, entry.get("spool_id"), "", vendor, kind,
                                     colour + "FF" if colour else "", label, spools, target)
    return [{"id": str(unit), "tray": [trays.get(unit * 4 + i, {"id": str(i)}) for i in range(4)]}
            for unit in range(max(trays, default=-1) // 4 + 1)]


MMU_KEYS = ("num_gates", "gate_status", "gate_material", "gate_color", "gate_spool_id", "gate_filament_name")


def mmu_present(mmu: object) -> bool:
    """Whether Klipper's "mmu" object is a Happy Hare MMU: it reports gates, or says it is enabled without saying
    how many. One that reports 0 gates (Happy Hare installed with no MMU attached) or nothing at all is no MMU."""
    if not isinstance(mmu, dict) or not mmu:
        return False
    if "num_gates" in mmu:
        return _live_updates._int(mmu.get("num_gates"), 0) > 0
    return mmu.get("enabled") is True or any(isinstance(mmu.get(k), list) and mmu[k] for k in MMU_KEYS[1:])



def mmu_units(mmu: dict, spools: list[dict], target: str) -> list[dict]:
    """Happy Hare's own gates (its "mmu" printer object) as Bambu-shaped units of four trays, read-only: the
    spool id it reports, else the gate's material and colour. A gate it reports empty (status 0) is empty."""
    def at(key: str, i: int) -> object:
        return _list_at(mmu.get(key), i)
    count = _live_updates._int(mmu.get("num_gates"), 0)
    count = count if count > 0 else max((len(mmu[k]) for k in MMU_KEYS[1:] if isinstance(mmu.get(k), list)), default=0)
    trays = []
    for i in range(min(count, LANE_MAX)):
        kind = str(at("gate_material", i) or "").strip()
        if at("gate_status", i) == 0 or not (kind or _live_updates._int(at("gate_spool_id", i), -1) > 0):
            trays.append({"id": str(i % 4)})
            continue
        colour = _sources._hex6(at("gate_color", i))
        trays.append(slot_tray(i % 4, at("gate_spool_id", i), "", "", kind, colour + "FF" if colour else "",
                               str(at("gate_filament_name", i) or kind).strip(), spools, target))
    return [{"id": str(unit), "tray": trays[unit * 4:unit * 4 + 4]} for unit in range((len(trays) + 3) // 4)]


def moon_report(status: dict, active_spool: object, spools: list[dict], target: str = "",
                lanes: dict | None = None) -> tuple[dict, bool]:
    """(Bambu-shaped report, has toolheads) from Moonraker's answers."""
    config = status.get("print_task_config")
    if isinstance(config, dict) and isinstance(config.get("filament_exist"), list):
        detect = status.get("filament_detect") if isinstance(status.get("filament_detect"), dict) else {}
        # A config longer than the extruders Klipper answered for (an SV06 reporting a template of 8 slots) is not
        # that many toolheads; with no extruder answered at all the config is all there is.
        heads = len(config["filament_exist"])
        heads = min(heads, moon_tool_count(status)) or heads
        trays = [head_tray(i, config, detect, spools, target) for i in range(heads)]
        ams: dict = {"ams": [{"id": "0", "tray": trays}]}
        # The toolhead holding the print: "extruder" is head 0, "extruderN" head N (what the page marks active).
        toolhead = status.get("toolhead")
        active = toolhead.get("extruder") if isinstance(toolhead, dict) else None
        if active in MOON_EXTRUDERS and MOON_EXTRUDERS.index(active) < heads:
            ams["tray_now"] = str(MOON_EXTRUDERS.index(active))
        return {"print": {"ams": ams}}, True
    if lanes:
        return {"print": {"ams": {"ams": lane_units(lanes, spools, target)}}}, False
    if mmu_present(status.get("mmu")):
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
            if isinstance(entry, dict) and _live_updates._int(entry.get("lane")) >= 0}


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


MOON_EXTRUDERS = ("extruder",) + tuple(f"extruder{n}" for n in range(1, _printers.MOON_TOOLS))


def moon_tool_count(status: dict) -> int:
    """How many extruders (toolheads) Klipper has: extruder, extruder1 ... extruder7 that answered."""
    # Klipper answers {"temperature": null} for an extruderN it doesn't have (SV06: extruder1..7), so a real extruder is one
    # reporting a number. An answer with no extruder at all counts 0: moon_found keeps what the last good poll found.
    def real(obj: object) -> bool:
        temp = obj.get("temperature") if isinstance(obj, dict) else None
        return isinstance(temp, (int, float)) and not isinstance(temp, bool) and math.isfinite(temp)
    return sum(1 for name in MOON_EXTRUDERS if real(status.get(name)))


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


def moon_found(base: str, tools: int, managed: bool, u1: bool = False, hh: bool = False, solo: bool = False) -> dict | None:
    """Note what a poll found on the Klipper printer at base, and return its Printer tab entry (None when no
    preset has that address). A change is sent to the page, whose slots to set by hand follow it."""
    printer = next((p for p in _auto_printers if p["ip"] == base), None)
    if printer is None:
        return None
    # No extruder in the answer (an empty or partial status) says nothing about the printer: keep what the last
    # good poll found. Once a printer reported its own spools (U1, lane_data, ACE) it stays read-only, so one odd
    # answer can't offer slots to set, fill it from a slice, or book a U1 next to u1control.
    last = _printers._moon_found.get(printer["id"]) or {}
    if not tools and last:
        managed = last["managed"]
    found = {"tools": tools or last.get("tools", 1), "managed": managed or bool(last.get("managed")),
             "u1": u1 or bool(last.get("u1")), "hh": hh or bool(last.get("hh")), "solo": solo}
    if _printers._moon_found.get(printer["id"]) != found:
        _printers._moon_found[printer["id"]] = found
        _printers.bump_printers_rev()
    return _printers.moon_entry(printer, _printers.moon_saved().get(printer["id"]))


def moon_poll(base: str) -> tuple[dict, bool]:
    status = _moon_get(base, "/printer/objects/query?print_task_config&filament_detect&print_stats&virtual_sdcard&toolhead=extruder&"
                       + "&".join(f"{name}=temperature" for name in MOON_EXTRUDERS) + "&mmu=" + ",".join(MMU_KEYS)
                       ).get("status")
    status = status if isinstance(status, dict) else {}
    active = lanes = None
    solo = False
    # Moonraker answers {} for an object the printer doesn't have (only the U1 has this one).
    if not status.get("print_task_config"):
        lanes = moon_lanes(base)
        if not lanes:
            try:
                active = _moon_get(base, "/server/spoolman/spool_id").get("spool_id")
            except urllib.error.HTTPError:
                active, solo = None, True  # Moonraker without its Spoolman integration: the spool is set here
    spools, target = _core._spool_cache["spools"] or [], _peers.target_for_host(base)
    doc, heads = moon_report(status, active, spools, target, lanes)
    # The Snapmaker U1's toolheads are booked by u1control, so its prints never are here (_moon_run).
    # Happy Hare ("mmu" object) reports its gates and books them through its own Spoolman integration:
    # read-only even with no gate reported, never filled or booked here.
    # The U1 (toolheads in print_task_config) is never Happy Hare, whatever its "mmu" object answers.
    doc["hh"] = not heads and mmu_present(status.get("mmu"))
    entry = moon_found(base, moon_tool_count(status), heads or "ams" in doc["print"] or doc["hh"], heads, doc["hh"],
                       solo and not doc["hh"])
    found = (_printers._moon_found.get(entry["id"]) or {}) if entry else {}
    doc["u1"] = heads or bool(found.get("u1"))
    doc["hh"] = doc["hh"] or bool(found.get("hh"))
    if entry is not None and not entry["managed"]:
        heads = moon_manual(doc, entry["units"], spools, target)
    elif entry is not None and "vt_tray" in doc["print"]:
        # It reported its own spools before (U1, lane_data, Happy Hare) and this answer was empty: show no
        # slots this time, never Moonraker's active spool, so the page can't offer to set one (spool_set).
        doc["print"].pop("vt_tray")
        doc["print"]["ams"] = {"ams": []}
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
    if pid in _live_updates._live["printers"]:
        _live_updates._live["printers"][pid]["heads"] = heads
        _live_updates._live["printers"][pid]["head_count"] = len(doc["print"]["ams"]["ams"][0]["tray"]) if heads else 0
        _live_updates._live["printers"][pid]["spool_set"] = "vt_tray" in doc["print"]
        _live_updates._live["printers"][pid]["hh"] = bool(doc.get("hh"))
        _live_updates._live["printers"][pid]["bind"] = "T" if heads and doc.get("u1") else ""
        if doc.get("hh"):
            _live_updates._live["printers"][pid]["unit_label"] = "MMU"


def moon_set_spool(pid: object, spool_id: object, confirmed: bool = False) -> dict:
    """Set the spool Moonraker books a single-extruder printer's usage to, or clear it (None).
    Refused for the Snapmaker U1 (u1control binds its toolheads through Spoolman locations) and
    for AFC / Happy Hare lanes (they manage their own spools), checked here against the printer
    itself, not only hidden on the page. While the printer prints (or is paused) the rest of that
    print would be booked to the new spool, so it is only changed once the page confirmed that
    ({"confirm": true} in the answer asks for it)."""
    if _sources.source() != "spoolman":
        return {"ok": False, "text": _i18n.tr("Setting a printer's spool needs Spoolman as the spool source.")}
    if spool_id is not None:
        number = spool_id if isinstance(spool_id, int) and not isinstance(spool_id, bool) else -1
        if number <= 0 or _spool_by_id(number, _core._spool_cache["spools"] or []) is None:
            return {"ok": False, "text": _i18n.tr("That spool isn't in Spoolman, or it is archived.")}
    entry = _live_updates._local.get(str(pid))
    link = entry["link"] if entry else None
    with _live_updates._live_lock:
        state = _live_updates._live["printers"].get(str(pid)) or {}
        single = bool(state.get("spool_set"))
    if not link or link.get("kind") != "moonraker" or not single:
        return {"ok": False, "text": _i18n.tr("Spooler can only set the spool on a single-extruder Klipper printer.")}
    base = link["ip"]
    try:
        doc, heads = moon_poll(base)  # read again: the printer decides, not the page
        # A printer that once reported its own spools (U1, lane_data, Happy Hare) keeps them, even when one
        # answer comes back empty: never set Moonraker's active spool on it.
        if heads or "vt_tray" not in doc["print"] or (_printers._moon_found.get(str(pid)) or {}).get("managed"):
            with _live_updates._live_lock:
                moon_mark(str(pid), doc, heads)
            return {"ok": False, "text": _i18n.tr("{printer} manages its own spools; Spooler only reads them.", printer=link["name"])}
        busy = str(doc["print"].get("gcode_state") or "").upper()
        if busy in _rfid.LIVE_STATES and not confirmed:
            return {"ok": False, "confirm": True, "state": busy,
                    "text": _i18n.tr("{printer} is paused in a print: Moonraker would book the rest of this print to the "
                               "new spool. Confirm to change it anyway." if busy == "PAUSE" else
                               "{printer} is running a print: Moonraker would book the rest of this print to the "
                               "new spool. Confirm to change it anyway.", printer=link["name"])}
        # Body per https://moonraker.readthedocs.io/en/latest/external_api/integrations/#set-active-spool
        # {"spool_id": <id>} sets the active spool; {"spool_id": null} clears it and stops tracking.
        _moon_post(base, "/server/spoolman/spool_id", {"spool_id": spool_id})
        doc, heads = moon_poll(base)
    except Exception as exc:  # the page waits for an answer: any failure is one
        _core.log.warning("Could not set the spool on %s: %s", link["name"], exc)
        return {"ok": False, "text": _i18n.tr("Could not set the spool on {printer}: {error}", printer=link["name"], error=exc)}
    _live_updates.live_apply(str(pid), link["name"], doc, link=str(pid), full=True)
    with _live_updates._live_lock:
        moon_mark(str(pid), doc, heads)
    if spool_id is None:
        return {"ok": True, "text": _i18n.tr("{printer}: no active spool, Moonraker stopped booking usage.", printer=link["name"])}
    return {"ok": True, "text": _i18n.tr("{printer} now books its usage to spool #{id}.", printer=link["name"], id=spool_id)}


def start_moon_spool(data: object, post) -> None:
    """Run moon_set_spool off the UI thread, then post the result and the refreshed live state."""
    data = data if isinstance(data, dict) else {}

    def work():
        result = {"ok": False, "text": _i18n.tr(_editor.STALE_LIST)} if data.get("spool") is not None and _editor.stale_list(data) \
            else moon_set_spool(data.get("id"), data.get("spool"), data.get("confirm") is True)
        post({"type": "moon_spool", "id": data.get("id"), "spool": data.get("spool"), **result})
        post({"type": "live", "live": _live_updates.live_snapshot(), "usage": _netprinters.usage_state()})
    _filament_profiles.spawn(work)


def is_moonraker(base: str) -> bool:
    """True when the host answers like Moonraker. Raises URLError when it can't be reached."""
    try:
        info = _moon_get(base, "/server/info")
    except (urllib.error.HTTPError, ValueError):
        return False
    return "klippy_state" in info or "moonraker_version" in info


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import capabilities as _capabilities  # noqa: E402
from . import core as _core  # noqa: E402
from . import editor as _editor  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
