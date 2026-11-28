# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Card actions on the Spools tab and the spool editor (Add Spool, Edit Spool)."""

import datetime
import json
import math
import re
import urllib.error
import urllib.parse

from . import core as _core
from . import filament_profiles as _filament_profiles

# --- Card actions on the Spools tab --------------------------------------------------------
# One message from either UI host: {"type": "spool_action", "action": ..., "id": ...}. The page is
# untrusted input, so everything is checked here before it reaches Spoolman.
SPOOL_ACTIONS = ("weigh", "use", "archive", "unarchive", "move", "add", "open", "dried", "clear_dried",
                 "comment", "remaining", "bind", "unbind")
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
    if not math.isfinite(grams):
        return None
    grams = round(grams, 1)  # what Spoolman is sent: 0.04 g is 0.0 g, never a "Used 0.0 g" that changed nothing
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
    version = _spoolman_sync.spoolman_version(fresh=True)
    if version is None:
        return _i18n.tr(DRIED_NO_VERSION)
    if version >= _spoolman_sync.SPOOLMAN_EXTRA_MERGE or (version >= _spoolman_sync.SPOOLMAN_EXTRA_PARTIAL and value is not None):
        return {_core.DRIED_FIELD: value}
    if version >= _spoolman_sync.SPOOLMAN_EXTRA_PARTIAL:
        return _i18n.tr(DRIED_NO_CLEAR)
    spool = _spoolman_sync.spoolman_call("GET", f"spool/{sid}")
    extra = spool.get("extra") if isinstance(spool, dict) else None
    if not isinstance(extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in extra.items()):
        return _i18n.tr(DRIED_NO_EXTRA)
    kept = {k: v for k, v in extra.items() if k != _core.DRIED_FIELD}
    return {**kept, _core.DRIED_FIELD: value} if value is not None else kept


def _binds(location: object, letter: str, names: tuple, number: int) -> bool:
    """Whether a Spoolman location is the peer plugin's binding of slot <letter><number> on this printer."""
    if letter == "T":
        return _moonraker._bound_here(location, names, number) > 0
    return _moonraker._location_key(location) in {_moonraker._location_key(_moonraker.location_for(name, "S", number)) for name in names}


def slot_bind(sid: int, pid: object, slot: object, on: bool) -> dict:
    """Link spool sid to a live printer's slot, or unlink it, the way the plugin that owns the printer reads
    the link: the spool's Spoolman location "<printer name> T<n>" for a Snapmaker U1 toolhead (U1 Control) and
    "<printer name> S<n>" for an Anycubic Kobra ACE or spool holder slot (Kobra Control; n = unit id * 4 + slot + 1). Linking clears that location from any other
    spool that holds it, so one spool is in each slot. Nothing is sent to the printer. Refused for every other
    printer: their slots are the printer's own (Bambu, Happy Hare, AFC) or set on the printer's card."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    number = slot + 1 if isinstance(slot, int) and not isinstance(slot, bool) and 0 <= slot < _moonraker.LANE_MAX else 0
    printer = next((p for p in _moonraker._auto_printers if p["id"] == str(pid)), None)
    with _live_updates._live_lock:
        letter = (_live_updates._live["printers"].get(str(pid)) or {}).get("bind") or ""
    if printer is None or letter not in ("T", "S") or not number or (letter == "T" and number > _printers.MOON_TOOLS):
        return no(_i18n.tr("Spooler can only link a spool to a Snapmaker U1 toolhead or an Anycubic Kobra ACE or spool holder slot."))
    names = _peers.location_names(_peers.target_for_host(printer["ip"])) or (printer["name"],)
    location = _moonraker.location_for(names[-1], letter, number)
    spools = _core._spool_cache["spools"] or []
    spool = _moonraker._spool_by_id(sid, spools)
    if spool is None:
        return no(_i18n.tr("That spool isn't in Spoolman, or it is archived."))
    if not on:
        if not _binds(spool.get("location"), letter, names, number):
            return no(_i18n.tr("Spool #{id} isn't linked to {slot}.", id=sid, slot=location))
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"location": None})
        spool["location"] = None   # the page's next list is the cached one, already right
        _peers.links_changed()
        return {"ok": True, "patched": True, "text": _i18n.tr("Spool #{id} is no longer linked to {slot}.", id=sid, slot=location)}
    _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"location": location})
    spool["location"] = location
    for other in spools:
        if other.get("id") != sid and not other.get("archived") and _binds(other.get("location"), letter, names, number):
            _spoolman_sync.spoolman_call("PATCH", f"spool/{other['id']}", {"location": None})
            other["location"] = None
    _peers.links_changed()
    return {"ok": True, "patched": True, "text": _i18n.tr("Spool #{id} linked to {slot}.", id=sid, slot=location)}


def _spool_write(action: str, sid: int, data: dict) -> dict:
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    if action in ("weigh", "use"):
        grams = _action_grams(data.get("grams"))
        if grams is None:
            return no(_i18n.tr("Enter a weight between 0 and {max} g.", max=_i18n.fmt_num(MAX_GRAMS, group=True)))
        if action == "use":
            _rfid.spoolman_use(sid, grams)
            return {"ok": True, "text": _i18n.tr("Used {grams} g of spool #{id}.", grams=_i18n.fmt_num(grams, 1, group=True), id=sid)}
        _spoolman_sync.spoolman_call("PUT", f"spool/{sid}/measure", {"weight": round(grams, 1)})
        return {"ok": True, "text": _i18n.tr("Spool #{id} set from a scale weight of {grams} g.", id=sid, grams=_i18n.fmt_num(grams, 1, group=True))}
    if action in ("archive", "unarchive"):
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"archived": action == "archive"})
        return {"ok": True, "text": _i18n.tr("Spool #{id} archived." if action == "archive" else "Spool #{id} unarchived.", id=sid)}
    if action == "move":
        location = data.get("location")
        if not isinstance(location, str) or len(location.strip()) > LOCATION_MAX:
            return no(_i18n.tr("A location is text of at most {max} characters.", max=LOCATION_MAX))
        location = " ".join(location.split())
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"location": location or None})
        held = _moonraker._spool_by_id(sid, _core._spool_cache["spools"] or [])
        if held is not None:
            held["location"] = location or None   # the page's next list is the cached one, already right
        _peers.links_changed()   # a location typed here may link or unlink a slot of U1 Control or Kobra Control
        return {"ok": True, "patched": True, "text": _i18n.tr("Spool #{id} moved to {location}.", id=sid, location=location) if location
                else _i18n.tr("Spool #{id} has no location now.", id=sid)}
    if action in ("bind", "unbind"):
        return slot_bind(sid, data.get("printer"), data.get("slot"), action == "bind")
    if action in ("dried", "clear_dried"):
        _filament_profiles.ensure_fields()
        value = json.dumps(f"{today().isoformat()}T00:00:00+00:00") if action == "dried" else None
        extra = _dried_extra(sid, value)
        if isinstance(extra, str):
            return no(extra)
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"extra": extra})
        return {"ok": True, "text": _i18n.tr("Spool #{id} marked as dried today." if action == "dried"
                                       else "Spool #{id} has no dried date now.", id=sid)}
    if action == "remaining":
        grams = _action_grams(data.get("grams"), zero=True)
        if grams is None:
            return no(_i18n.tr("Enter the grams left, from 0 to {max} g.", max=_i18n.fmt_num(MAX_GRAMS, group=True)))
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"remaining_weight": round(grams, 1)})
        return {"ok": True, "text": _i18n.tr("Spool #{id} now has {grams} g left.", id=sid, grams=_i18n.fmt_num(grams, 1, group=True))}
    if action == "comment":
        text = data.get("comment")
        if not isinstance(text, str) or len(text.strip()) > COMMENT_MAX:
            return no(_i18n.tr("A note is text of at most {max} characters.", max=COMMENT_MAX))
        text = text.strip()
        _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", {"comment": text or None})
        return {"ok": True, "text": _i18n.tr("Saved the note on spool #{id}." if text else "Spool #{id} has no note now.", id=sid)}
    if action == "add":
        fid = _pos_int(data.get("filament"))
        if fid is None:
            return no(_i18n.tr("That spool has no filament to copy."))
        count = data.get("count", 1)
        if _pos_int(count) is None or count > ADD_MAX:
            return no(_i18n.tr("Add 1 to {max} spools at a time.", max=ADD_MAX))
        made: list[str] = []
        for _ in range(count):
            try:
                made.append(f"#{(_spoolman_sync.spoolman_call('POST', 'spool', {'filament_id': fid}) or {}).get('id', '?')}")
            except Exception as exc:
                if not made:
                    raise
                # Each POST is its own spool: say which ones exist, so none is added twice by a retry.
                _core.log.warning("Adding spool %d of %d failed: %s", len(made) + 1, count, exc)
                return no(_i18n.tr("Added spool {spools}, then Spoolman refused the next one: {error}",
                             spools=_plate_check._join(made), error=_rfid._spoolman_error(exc)))
        if count == 1:
            return {"ok": True, "text": _i18n.tr("Added spool {spool} of the same filament.", spool=made[0])}
        return {"ok": True, "text": _i18n.tr("Added {count} spools of the same filament: {spools}.", count=count, spools=_plate_check._join(made))}
    url = getattr(_spoolman_sync._op, "origin", None)[0] if getattr(_spoolman_sync._op, "origin", None) else _sources.clean_url(_core.get_settings().get("spoolman_url"))
    # Only a web address: a file:// or other scheme synced in as Spoolman's would launch whatever it names.
    if urllib.parse.urlsplit(url).scheme in ("http", "https") and _plate_check.open_url(f"{url}/spool/show/{sid}"):
        return {"ok": True, "text": _i18n.tr("Opened spool #{id} in Spoolman.", id=sid)}
    return no(_i18n.tr("Could not open {url}.", url=f"{url}/spool/show/{sid}"))


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
EDITOR_OWN = {"tag", _filament_profiles.ORCA_SETTINGS_FIELD, _core.DRIED_FIELD, _filament_profiles.USE_WITH_FIELD, _filament_profiles.PRESET_LINK_FIELD, *_filament_profiles.CALIBRATION_FIELDS}  # Spooler's own fields: never from the editor
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
        return _i18n.tr(EDITOR_INVALID, field="form")
    known = {f.get("key"): f for f in fields or [] if isinstance(f, dict)}
    out: dict = {}
    for key, value in values.items():
        if key == "extra":
            if not isinstance(value, dict):
                return _i18n.tr(EDITOR_INVALID, field=key)
            extra = {}
            for name, raw in value.items():
                text = _extra_value(known[name], raw) if name in known and name not in EDITOR_OWN else _BAD
                if text is _BAD:
                    return _i18n.tr(EDITOR_INVALID, field=name)
                extra[name] = text
            out["extra"] = extra
            continue
        clean = _form_value(form[key], value) if key in form else _BAD
        if clean is _BAD:
            return _i18n.tr(EDITOR_INVALID, field=key)
        out[key] = clean
    return out


def _vendor_id(name: str | None) -> int | None:
    """The Spoolman vendor of that name (case and spacing ignored), added when there is none."""
    if not name:
        return None
    for vendor in _spoolman_sync.spoolman_call("GET", "vendor") or []:
        if isinstance(vendor, dict) and _plate_check._norm(vendor.get("name")) == _plate_check._norm(name) and _pos_int(vendor.get("id")):
            return vendor["id"]
    return _spoolman_sync.spoolman_call("POST", "vendor", {"name": name})["id"]


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
    return {kind: [f for f in _spoolman_sync.spoolman_call("GET", f"field/{kind}") or [] if isinstance(f, dict)]
            for kind in ("spool", "filament")}


def _error_text(exc: Exception) -> str:
    """Spoolman's refusal with the reason it gives, when it gives one."""
    detail = ""
    if isinstance(exc, urllib.error.HTTPError):
        try:
            detail = json.loads(exc.read().decode("utf-8")).get("message") or ""
        except Exception:
            detail = ""
    error = _rfid._spoolman_error(exc)
    return _i18n.tr("{text}: {detail}", text=error, detail=detail) if isinstance(detail, str) and detail else error


def editor_data(sid: int | None) -> dict:
    """What the editor needs: Spoolman's extra-field definitions, its filaments and vendors, and the
    spool being edited as Spoolman has it now."""
    filaments = [f for f in _spoolman_sync.spoolman_call("GET", "filament") or [] if isinstance(f, dict)]
    vendors = sorted({str(v.get("name")) for v in _spoolman_sync.spoolman_call("GET", "vendor") or [] if isinstance(v, dict) and v.get("name")},
                     key=str.casefold)
    spool = _spoolman_sync.spoolman_call("GET", f"spool/{sid}") if sid else None
    printers = [{"target": p["target"], "label": p["label"]} for p in _filament_profiles._ui_snap.get("printers") or []]
    # Use with: shown while presets are made per spool, or once the spool has a value.
    chosen = _filament_profiles.use_with(spool, printers) if isinstance(spool, dict) else None
    # OrcaSlicer preset: your own filament presets, as the last snapshot read them on the UI thread.
    link = {"presets": list(_filament_profiles._ui_snap.get("user_filaments") or []),
            "spool": _filament_profiles._link_text(spool), "filament": _filament_profiles._link_text((spool or {}).get("filament") if isinstance(spool, dict) else None)}
    return {"fields": _editor_fields(), "filaments": filaments, "vendors": vendors, "spool": spool,
            "use_with": {"on": _filament_profiles.presets_settings()["per_spool"], "printers": printers, "value": chosen},
            "preset_link": link,
            # Add Spool > Look up in OFD runs at once when the user already agreed to contact the Open Filament Database.
            "ofd_consent": _filament_profiles.presets_settings()["ofd"],
            # Preset: the parent Spooler's presets of this filament copy, per printer, and the other candidates.
            "preset_match": _filament_profiles.preset_match((spool or {}).get("filament") if isinstance(spool, dict) else None,
                                                            _filament_profiles._ui_snap)}


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
        raise RuntimeError(_i18n.tr(EDITOR_NO_VERSION))
    if version >= _spoolman_sync.SPOOLMAN_EXTRA_MERGE:
        return extra
    if version >= _spoolman_sync.SPOOLMAN_EXTRA_PARTIAL:
        cleared = sorted(k for k, v in extra.items() if v is None)
        if cleared:
            raise RuntimeError(_i18n.tr(EDITOR_NO_CLEAR, fields=", ".join(cleared)))
        return extra
    now_extra = now.get("extra") or {}
    if not isinstance(now_extra, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in now_extra.items()):
        raise RuntimeError(_i18n.tr(EDITOR_NO_EXTRA))
    return {k: v for k, v in {**now_extra, **extra}.items() if v is not None}


def _use_with_text(chosen: object) -> str | None:
    """The Use with field as Spoolman keeps it (JSON text of a JSON list of printer presets; an empty
    text for the default, so Spoolman 0.22 to 0.25, which can't empty a field, take it too), or None
    when the page sent something else."""
    if chosen is None or chosen == []:
        return json.dumps("")
    if not isinstance(chosen, list) or len(chosen) > _filament_profiles.USE_WITH_MAX or \
            not all(isinstance(x, str) and x.strip() and len(x) <= 2 * _filament_profiles.PARENT_MAX for x in chosen):
        return None
    return json.dumps(json.dumps(list(dict.fromkeys(" ".join(x.split()) for x in chosen))))


def editor_save(sid: int, data: dict) -> dict:
    """Edit Spool: the spool's changed fields, and its filament's (shared by its other spools)."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    spool_data = data.get("spool") or {}
    spool_data = dict(spool_data) if isinstance(spool_data, dict) else spool_data
    chosen = spool_data.pop("use_with", _spoolman_sync._MISSING) if isinstance(spool_data, dict) else _spoolman_sync._MISSING
    fil_data = data.get("filament") or {}
    fil_data = dict(fil_data) if isinstance(fil_data, dict) else fil_data
    # The OrcaSlicer preset linked to the spool, and to its filament: None or "" unlinks.
    links = {kind: part.pop("preset_link", _spoolman_sync._MISSING) if isinstance(part, dict) else _spoolman_sync._MISSING
             for kind, part in (("spool", spool_data), ("filament", fil_data))}
    fields = _editor_fields()
    wanted = ([("spool", _filament_profiles.USE_WITH_FIELD, _filament_profiles.USE_WITH_DEF)] if chosen is not _spoolman_sync._MISSING else []) + \
        [(kind, _filament_profiles.PRESET_LINK_FIELD, _filament_profiles.PRESET_LINK_DEF) for kind, link in links.items() if link is not _spoolman_sync._MISSING]
    missing = [w for w in wanted if w[1] not in {f.get("key") for f in fields[w[0]]}]
    for kind, key, body in missing:
        try:  # Spoolman takes only extra keys it has a field for
            _spoolman_sync.spoolman_call("POST", f"field/{kind}/{key}", body)
            _core.log.info("Added the %s field to Spoolman", key)
        except _spoolman_sync.NotSent:
            raise
        except Exception as exc:
            return no(_i18n.tr(_filament_profiles.USE_WITH_NO_FIELD if key == _filament_profiles.USE_WITH_FIELD else _filament_profiles.PRESET_LINK_NO_FIELD, error=_error_text(exc)))
    if missing:
        fields = _editor_fields()
    spool_changes = _clean_form(SPOOL_FORM, spool_data, fields["spool"])
    fil_changes = _clean_form(FILAMENT_FORM, fil_data, fields["filament"])
    for found in (spool_changes, fil_changes):
        if isinstance(found, str):
            return no(found)
    was = data.get("was") if isinstance(data.get("was"), dict) else {}
    was_spool = was.get("spool") if isinstance(was.get("spool"), dict) else {}
    if chosen is not _spoolman_sync._MISSING:
        text = _use_with_text(chosen)
        if text is None:
            return no(_i18n.tr(EDITOR_INVALID, field=_filament_profiles.USE_WITH_FIELD))
        spool_changes["extra"] = {**(spool_changes.get("extra") or {}), _filament_profiles.USE_WITH_FIELD: text}
        old = was_spool.get(_filament_profiles.USE_WITH_FIELD)
        was_spool = {**was_spool, "extra": {**(was_spool.get("extra") or {}), _filament_profiles.USE_WITH_FIELD: old if isinstance(old, str) else None}}
    was_fil = was.get("filament") if isinstance(was.get("filament"), dict) else {}
    for kind, link in links.items():
        if link is _spoolman_sync._MISSING:
            continue
        text = _filament_profiles._link_value(link)
        if text is None:
            return no(_i18n.tr(EDITOR_INVALID, field=_filament_profiles.PRESET_LINK_FIELD))
        part = spool_changes if kind == "spool" else fil_changes
        part["extra"] = {**(part.get("extra") or {}), _filament_profiles.PRESET_LINK_FIELD: text}
        had = was_spool if kind == "spool" else was_fil
        old = had.get("preset_link")  # the page sends the link as Spoolman stored it, under this key
        had = {**had, "extra": {**(had.get("extra") or {}), _filament_profiles.PRESET_LINK_FIELD: old if isinstance(old, str) else None}}
        was_spool, was_fil = (had, was_fil) if kind == "spool" else (was_spool, had)
    now = _spoolman_sync.spoolman_call("GET", f"spool/{sid}")
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
        version = _spoolman_sync.spoolman_version(fresh=True)
        if s_extra:
            s_patch["extra"] = _extra_patch(s_extra, now, version)
        if f_extra:
            f_patch["extra"] = _extra_patch(f_extra, filament, version)
    if f_patch:
        _spoolman_sync.spoolman_call("PATCH", f"filament/{fid}", _for_spoolman(f_patch, filament))
    if s_patch:
        try:
            _spoolman_sync.spoolman_call("PATCH", f"spool/{sid}", s_patch)
        except Exception as exc:
            if not f_patch:
                raise
            _core.log.warning("Saving spool #%s after its filament failed: %s", sid, exc)
            return no(_i18n.tr("Saved the filament of spool #{id}, but Spoolman refused the spool: {error}", id=sid, error=_error_text(exc)))
    names = {f.get("key"): f.get("name") or f.get("key") for f in fields["spool"] + fields["filament"]}
    notes = []
    if f_patch:
        notes.append(_i18n.tr("Saved spool #{id} and its filament.", id=sid))
    elif s_patch:
        notes.append(_i18n.tr("Saved spool #{id}.", id=sid))
    elif not kept:
        notes.append(_i18n.tr("Spool #{id} had no changes to save.", id=sid))
    if kept:
        notes.append(_i18n.tr("Kept Spoolman's newer value for {fields}: it changed there while you were editing.",
                        fields=", ".join(str(names.get(key, key)) for key in kept)))
    return {"ok": True, "text": _i18n._sentences(notes)}


def _rfid_tag_extra(value: object, spool_fields: list) -> dict | str:
    """{"tag": <JSON text>} for a new spool's RFID tag, or why it can't be stored. Spoolman takes
    only extra fields it knows, so a missing text field "tag" is added first; a spool that already
    carries the tag stops it, as two would leave the tray matching neither."""
    tags = _netprinters._tag_ids(value) if isinstance(value, str) else set()
    if len(tags) != 1:
        return _i18n.tr(EDITOR_INVALID, field=_rfid.TAG_FIELD)
    tag = min(tags)
    # Archived spools too: one still carrying the tag would make two, and the tray would match neither.
    holder = next((s for s in _spoolman_sync.spoolman_call("GET", "spool?allow_archived=true") or [] if isinstance(s, dict) and tag in _netprinters.spool_tags(s)), None)
    if holder is not None and holder.get("archived"):
        return _i18n.tr("Archived spool #{id} carries this RFID tag; unarchive it instead. Nothing was written.", id=holder.get("id", "?"))
    if holder is not None:
        return _i18n.tr("Spool #{id} already carries this RFID tag; nothing was written.", id=holder.get("id", "?"))
    field = next((f for f in spool_fields if f.get("key") == _rfid.TAG_FIELD), None)
    if field is None:
        _spoolman_sync.spoolman_call("POST", f"field/spool/{_rfid.TAG_FIELD}", {"name": "RFID tag", "field_type": "text", "order": 101})
        _core.log.info("Added the %s field to Spoolman", _rfid.TAG_FIELD)
    elif field.get("field_type") != "text":
        return _i18n.tr("Spoolman's spool field \"tag\" isn't a text field, so the RFID tag can't be stored; nothing was written.")
    return {_rfid.TAG_FIELD: json.dumps(tag)}


def editor_create(data: dict) -> dict:
    """Add Spool: a spool of an existing filament (stock), or of a new filament made first."""
    no = lambda text: {"ok": False, "text": text}  # noqa: E731
    fields = _editor_fields()
    spool = _clean_form(SPOOL_FORM, data.get("spool") or {}, fields["spool"])
    if isinstance(spool, str):
        return no(spool)
    first, left = spool.get("initial_weight"), spool.get("remaining_weight")
    if first is not None and left is not None and left > first:
        return no(_i18n.tr(EDITOR_INVALID, field="remaining_weight"))
    if data.get("tag") is not None:  # a new RFID spool from the Printer tab
        tag = _rfid_tag_extra(data["tag"], fields["spool"])
        if isinstance(tag, str):
            return no(tag)
        spool["extra"] = {**(spool.get("extra") or {}), **tag}
    fid, made = _pos_int(data.get("filament_id")), None
    if fid is None:
        new = _clean_form(FILAMENT_FORM, data.get("filament"), fields["filament"])
        if isinstance(new, str):
            return no(new)
        for key in ("density", "diameter"):  # Spoolman needs both for a filament
            if new.get(key) is None:
                return no(_i18n.tr(EDITOR_INVALID, field=key))
        fid = made = _spoolman_sync.spoolman_call("POST", "filament", _create_body(_for_spoolman(new)))["id"]
    try:
        added = _spoolman_sync.spoolman_call("POST", "spool", {"filament_id": fid, **_create_body(spool)})
    except Exception as exc:
        if made is None:
            raise
        _core.log.warning("Adding a spool of new filament #%s failed: %s", made, exc)
        # The filament exists now: the page offers it as the existing filament, so a retry adds no second one.
        return {**no(_i18n.tr("Created filament #{filament}, but Spoolman refused the spool: {error}",
                        filament=made, error=_error_text(exc))), "filament": made}
    sid = (added or {}).get("id", "?") if isinstance(added, dict) else "?"
    text = (_i18n.tr("Added spool #{id} with the new filament #{filament}.", id=sid, filament=made) if made is not None
            else _i18n.tr("Added spool #{id}.", id=sid))
    if isinstance(data.get("ofd"), str):   # Look up in OFD: the preset picked there, for the filament on every printer it fits
        text += " " + _ofd_after_create(fid, data["ofd"])
    return {"ok": True, "text": text, "spool": sid}


def _ofd_after_create(fid: int, ofd: str) -> str:
    """Remember the OFD preset picked in Add Spool for the spool's filament; what to add to the result text."""
    try:
        filament = _spoolman_sync.spoolman_call("GET", f"filament/{fid}")
        done = _filament_profiles.remember_ofd(filament, ofd) if isinstance(filament, dict) else []
    except Exception as exc:   # the spool is added; only the preset choice is lost
        _core.log.warning("Remembering OFD preset %s for filament #%s failed: %s", ofd, fid, exc)
        done = []
    if done:
        return _i18n.tr("Its presets use the Open Filament Database preset on {printers}.", printers=", ".join(done))
    return _i18n.tr("The Open Filament Database preset fits none of your printers, so Spooler picks the preset itself.")


STALE_LIST = "The spool source changed since this list was read; nothing was written. Refresh and try again."


def stale_list(data: dict) -> bool:
    """Whether a page message carries the origin of a list read from a source the settings left.
    No origin (null) means the page has no list yet, so nothing in it was picked from an old one."""
    origin = data.get("origin")
    return isinstance(origin, int) and not isinstance(origin, bool) and origin != _spoolman_sync.current_origin()[1]


def spool_action(data: object) -> dict:
    """Run one card action; {"ok": bool, "text": str} (plus "locations" for that action). Never raises."""
    data = data if isinstance(data, dict) else {}
    action = data.get("action")
    if action == "show_archived":
        _core.save_display({**_core.display_settings(), "archived": data.get("on") is True})
        return {"ok": True, "text": ""}
    if action not in ("locations", "editor", "create", "save", "match_parent", "ofd_suggest") and action not in SPOOL_ACTIONS:
        return {"ok": False, "text": _i18n.tr("Unknown spool action.")}
    if _sources.source() != "spoolman":
        return {"ok": False, "text": _i18n.tr("Spool actions need Spoolman as the source.")}
    sid = _pos_int(data.get("id"))
    if sid is None and action not in ("locations", "editor", "create", "match_parent", "ofd_suggest"):
        return {"ok": False, "text": _i18n.tr("No spool chosen.")}
    if action not in ("locations", "editor", "ofd_suggest") and stale_list(data):
        return {"ok": False, "text": _i18n.tr(STALE_LIST)}
    try:
        with _spoolman_sync.pinned_origin():
            if action == "locations":
                found = _spoolman_sync.spoolman_call("GET", "location")
                return {"ok": True, "text": "",
                        "locations": [x for x in found if isinstance(x, str)] if isinstance(found, list) else []}
            if action == "editor":
                return {"ok": True, "text": "", "editor": editor_data(sid)}
            if action == "create":
                return editor_create(data)
            if action == "save":
                return editor_save(sid, data)
            if action == "ofd_suggest":   # Add Spool > Look up in OFD
                key = data.get("key") if isinstance(data.get("key"), str) else ""   # the page's lookup, sent back
                return {**_filament_profiles.ofd_suggest(data.get("vendor"), data.get("material"), data.get("name")), "key": key}
            if action == "match_parent":
                fid = _pos_int(data.get("filament"))
                filament = _spoolman_sync.spoolman_call("GET", f"filament/{fid}") if fid else None
                ofd = data.get("ofd") if isinstance(data.get("ofd"), str) else None
                return _filament_profiles.pick_parent(filament, data.get("target"), data.get("name"), ofd)
            return _spool_write(action, sid, data)
    except Exception as exc:
        _core.log.warning("Spool action %s on #%s failed: %s", action, sid, exc)
        return {"ok": False, "text": _error_text(exc)}


def start_spool_action(data: object, post) -> None:
    """Run a card action off the UI thread and post {"type": "action_result", ...}. The page asks
    for a refresh when it gets it, so the list is re-read on the UI thread."""
    action = data.get("action") if isinstance(data, dict) else None
    if action == "ofd_suggest" and data.get("consent") is True and not _filament_profiles.presets_settings()["ofd"]:
        # The user's click on Look up in OFD is the consent: kept, and OFD's address declared, here on the UI thread.
        _filament_profiles.set_ofd_consent(True)
        _capabilities.request_permissions()

    def work():
        result = spool_action(data)
        if action not in ("locations", "editor", "ofd_suggest"):
            _core._spool_cache["time"] = 0.0
            _rfid._archived_tags["time"] = 0.0  # an archive or unarchive changes them
        ref = data.get("ref") if isinstance(data, dict) else None  # the editor's own count: its answer finds the right editor
        post({"type": "action_result", "action": action, **result,
              **({"ref": ref} if isinstance(ref, int) and not isinstance(ref, bool) else {})})
    _filament_profiles.spawn(work)


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
        _netprinters.usage_save(data)
    except OSError:
        row.update(before)
        raise
    try:
        request()
    except Exception as exc:
        if _rfid.maybe_applied(exc):
            row.update(state="unknown", error=_i18n.tr("{text} ({detail})", text=_i18n.tr(_netprinters.UNKNOWN_TEXT), detail=_rfid._spoolman_error(exc)))
        else:
            row.update(state=before["state"], error=_rfid._spoolman_error(exc))
        _core.log.warning("Usage %s for spool %s failed: %s", op, row.get("spool"), exc)
        _netprinters.usage_save(data)
        return False
    return True


def usage_book(entry_id: str, chosen: list | None) -> str:
    """Book the open rows to their spools; chosen holds manual picks. Returns a notice for the
    page, "" when there is none. Raises OSError when the booking state can't be saved."""
    wanted = {}
    for item in chosen if isinstance(chosen, list) else []:
        if isinstance(item, dict):
            wanted[_live_updates._int(item.get("slot"))] = item
    with _spoolman_sync.pinned_origin() as origin:
        url = origin[0]
        by_id = {sp.get("id"): sp for sp in (_plate_check.plate_spools(url) if url and url != _sources.BAMBU_KEY else None) or []}
        with _netprinters._usage_lock:
            data = _netprinters.usage_load()
            entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
            if entry is None or entry.get("state") == "unknown":
                return ""
            if not url or entry.get("origin") != url:
                return _i18n.tr(ORIGIN_TEXT)
            for row in entry["rows"]:
                if row["state"] in ("booked", "unknown", "sending"):
                    continue
                pick = wanted.get(row["slot"], {})
                spool = _live_updates._int(pick.get("spool")) if pick.get("spool") not in (None, "") else row["spool"]
                try:
                    grams = float(pick["grams"]) if "grams" in pick else row["grams"]
                except (TypeError, ValueError, OverflowError):
                    continue  # An unreadable weight books nothing; 0 would mark the row booked.
                if not (math.isfinite(grams) and 0 <= grams <= 5000):
                    continue
                if grams == 0:
                    # Set to 0 g on the page: nothing was used from this slot, so nothing is sent.
                    row.update(grams=0.0, state="booked", error="")
                    _netprinters.usage_save(data)
                    continue
                if spool in (None, -1):
                    continue
                row.update(spool=spool, grams=round(grams, 1))
                if not _send_row(data, row, "book", lambda: _rfid.spoolman_use(spool, grams)):
                    continue
                label = _rfid._spool_label(by_id[spool]) if spool in by_id else row.get("label") or _i18n.tr("spool {id}", id=spool)
                row.update(state="booked", error="", label=label)
                _core.log.info("Booked %.1f g to Spoolman spool %s", grams, spool)
                _netprinters.usage_save(data)
            entry["state"] = _book_state(entry, "booked", "pending")
            _netprinters.usage_save(data)
            return _hist_after(entry, by_id)


def _hist_after(entry: dict, by_id: dict) -> str:
    try:
        _stats.hist_note(entry, by_id)
    except OSError:
        _core.log.exception("Could not write %s", _stats.HISTORY_FILE)
        return _i18n.tr("Spoolman has the change, but Spooler could not update its history file.")
    return ""


def usage_undo(entry_id: str) -> str:
    """Add a booked print's grams back to its spools. Returns a notice, "" when there is none."""
    with _spoolman_sync.pinned_origin() as origin:
        with _netprinters._usage_lock:
            entry = next((e for e in _netprinters.usage_load()["prints"] if e.get("id") == entry_id), None)
        if entry is None or entry.get("state") != "booked":
            return ""
        if entry.get("origin") != origin[0]:
            return _i18n.tr(ORIGIN_TEXT)
        if not _spoolman_sync.spoolman_at_least(_spoolman_sync.SPOOLMAN_ATOMIC_USE):
            return _i18n.tr("Undo needs Spoolman 0.18 or newer, which adds grams back in one step without losing use "
                      "booked meanwhile. Spooler couldn't confirm this Spoolman's version, so nothing changed; "
                      "adjust the spools in Spoolman by hand.")
        with _netprinters._usage_lock:
            data = _netprinters.usage_load()
            entry = next((e for e in data["prints"] if e.get("id") == entry_id), None)
            if entry is None or entry.get("state") != "booked":
                return ""
            for row in entry["rows"]:
                if row["state"] != "booked":
                    continue
                if not row.get("grams"):   # 0 g: nothing was booked, nothing to add back
                    row.update(state="undone", error="")
                    continue
                if not _send_row(data, row, "undo", lambda: _rfid.spoolman_unuse(row["spool"], row["grams"])):
                    continue
                row.update(state="undone", error="")
                _core.log.info("Added %.1f g back to Spoolman spool %s", row["grams"], row["spool"])
                _netprinters.usage_save(data)
            entry["state"] = _book_state(entry, "undone", "booked")
            _netprinters.usage_save(data)
            return _hist_after(entry, {})


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import capabilities as _capabilities  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import printers as _printers  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
from . import stats as _stats  # noqa: E402
