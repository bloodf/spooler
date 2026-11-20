# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Sending preset edits and calibrations back to Spoolman, on the server they belong to."""

import json
import re
import threading

import orca

from . import filament_profiles as _filament_profiles

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


class VersionUnknown(RuntimeError):
    """Spoolman's version couldn't be read, so how it stores extra fields is unknown."""


class OriginChanged(NotSent):
    def __init__(self):
        super().__init__(_i18n.tr("The spool source changed in Settings while this ran, so Spooler stopped "
                            "before writing anything more. Try again."))


_origin: dict = {"key": None, "gen": 0}
_origin_lock = threading.Lock()
_op = threading.local()


def _origin_key(settings: dict) -> str:
    if _sources.parse_source(settings.get("spool_source")) == "bambu":
        return _sources.BAMBU_KEY
    return _sources.clean_url(settings.get("spoolman_url"))


def current_origin() -> tuple[str, int]:
    """(source key, generation): the Spoolman address (or "bambu") in the settings now, and a
    number that changes whenever it does. A change also drops what was read from the old one."""
    key = _origin_key(_core.get_settings())
    with _origin_lock:
        if key != _origin["key"]:
            if _origin["key"] is not None:
                _core.log.info("The spool source changed; dropping what was read from the old one")
                _core._spool_cache.update(url="", time=0.0, spools=[])
                _filament_profiles._profiles.update(names={}, gen=None)
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
        return _sources._spoolman_open(_sources.clean_url(_core.get_settings().get("spoolman_url")), path, method, body)
    if not origin_live(pinned):
        raise OriginChanged()
    if pinned[0] in ("", _sources.BAMBU_KEY):
        raise NotSent(_i18n.tr("Spoolman is not the spool source."))
    return _sources._spoolman_open(pinned[0], path, method, body)


def orca_items(text: str, key: str) -> list[str]:
    """A setting's values as config_value() writes them: numbers comma separated, text semicolon
    separated and, when it holds spaces or special characters, quoted with C escapes."""
    if key not in _filament_profiles.TEXT_KEYS:
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
    number = _filament_profiles._number(text)
    return None if number is None else f"{number:.6g}"


def edited_changes() -> tuple[str, dict]:
    """(preset name, {setting: (edited text, saved text)}) for the Spooler preset open in
    OrcaSlicer's filament settings. Call it on the UI thread; raises RuntimeError saying what to do."""
    filaments = orca.host.preset_bundle().filaments
    edited = filaments.get_edited_preset()
    if not edited.name.startswith(_filament_profiles.PROFILE_PREFIX) or _saved_of(filaments, edited.name) is None:
        raise RuntimeError(_i18n.tr("Open a Spooler preset in OrcaSlicer's filament settings and change it first."))
    name = edited.name[len(_filament_profiles.PROFILE_PREFIX):]
    changes = unsaved_changes(filaments, edited.name)
    if not changes:
        raise RuntimeError(_i18n.tr("{name} has no unsaved changes to send.", name=name))
    return name, changes


def _saved_of(filaments, name: str):
    """The saved preset behind the one open in the filament settings, when that is name; else None.
    find_preset() can't give it: for the selected preset it answers the edited copy, so a comparison
    with it never shows a change. The selected preset is the saved one the edited copy was made from."""
    saved = filaments.get_selected_preset()
    return saved if saved is not None and saved.name == name == filaments.get_edited_preset().name else None


def unsaved_changes(filaments, name: str) -> dict:
    """{setting: (edited text, saved text)} for preset name's unsaved edits; {} when it isn't the
    preset open in the filament settings or has none. UI thread."""
    saved = _saved_of(filaments, name)
    if saved is None:
        return {}
    edited = filaments.get_edited_preset()
    return {key: (edited.config_value(key), saved.config_value(key)) for key in edited.config_keys()
            if edited.config_value(key) != saved.config_value(key)}


def _orca_text(items: list, key: str) -> str:
    """Values as config_value() writes them (orca_items reads them back)."""
    if key not in _filament_profiles.TEXT_KEYS:
        return ",".join(items)
    escape = lambda v: v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r")  # noqa: E731
    return ";".join(f'"{escape(v)}"' for v in items)


def spool_presets(spool: dict | None) -> list[dict]:
    """The OrcaSlicer presets a spool goes by, for Send to Spoolman: your own linked one first, then Spooler's
    preset of it for each printer the link doesn't fit. Each {"name", "label" (the printer), "linked", "where": (filament id,
    printer preset)}; a linked preset (when it fits the selected printer) is offered for that printer, and "own" says the
    link is the spool's own rather than its filament's. The one to pick first leads: the preset open in
    the filament settings, else the selected printer's."""
    filament = (spool or {}).get("filament") if isinstance(spool, dict) else None
    fid = filament.get("id") if isinstance(filament, dict) else None
    if fid is None:
        return []
    target = _filament_profiles._ui_snap.get("selected") or ""
    linked = _filament_profiles.spool_link(spool, target, _filament_profiles._ui_snap)
    first = [{"name": linked, "label": _peers.label_for_target(target), "linked": True, "where": (fid, target),
              "own": bool(_filament_profiles._link_text(spool))}] if linked else []
    out = []
    for key, name in _filament_profiles._profiles["names"].items():
        if key[0] == fid and (len(key) < 3 or key[2] == spool.get("id")):
            out.append({"name": _filament_profiles.PROFILE_PREFIX + name, "label": _peers.label_for_target(key[1]), "linked": False,
                        "where": (fid, key[1])})
    edited, selected = _filament_profiles._ui_snap.get("edited"), _filament_profiles._ui_snap.get("selected")
    # Spooler's presets for the printers the link doesn't fit follow the linked one.
    return first + sorted(out, key=lambda p: (p["name"] != edited, p["where"][1] != selected, p["name"].casefold()))


def chosen_changes(data: object) -> tuple[str, dict, tuple]:
    """(name, {setting: (value, base)}, (filament id, printer preset) for a linked preset, else None) for Send to Spoolman on the preset
    picked in a spool's detail: its unsaved edits when it is the preset open in OrcaSlicer's filament
    settings and has some; else, for your own linked preset, its saved settings that differ from the
    preset Spooler would make (a Spooler preset's saved settings come from Spoolman: {}). UI thread."""
    data = data if isinstance(data, dict) else {}
    full = data.get("preset") if isinstance(data.get("preset"), str) else ""
    spool = _moonraker._spool_by_id(data.get("spool"), _core._spool_cache.get("spools") or [])
    pick = next((p for p in spool_presets(spool) if p["name"] == full), None) if full else None
    if pick is None:
        raise RuntimeError(_i18n.tr("That preset is no longer one of this spool's. Refresh, then send it again."))
    if pick.get("own"):
        # Spoolman keeps settings on the filament, shared by every spool of it: a link of this spool
        # alone must not change the others' presets.
        raise RuntimeError(_i18n.tr("{name} is linked to this spool only, and Spoolman keeps settings on the filament every "
                              "spool of it shares; nothing was sent. Save your changes in the preset itself, or link "
                              "the filament instead.", name=full))
    name = full[len(_filament_profiles.PROFILE_PREFIX):] if full.startswith(_filament_profiles.PROFILE_PREFIX) else full
    filaments = orca.host.preset_bundle().filaments
    changes = unsaved_changes(filaments, full)
    if not pick["linked"]:
        return name, changes, None  # a Spooler preset: send_changes finds its filament and printer by name
    if changes:
        return name, changes, pick["where"]
    if not pick["where"][1]:
        raise RuntimeError(_i18n.tr("Select a printer in OrcaSlicer first, then send again."))
    preset = filaments.find_preset(full)
    base = _filament_profiles.build_preset(spool["filament"], name, pick["where"], _filament_profiles._ui_snap, _filament_profiles.presets_settings(),
                        _core._spool_cache.get("spools") or []) if preset is not None else None
    if base is None:
        raise RuntimeError(_i18n.tr("{name} can't be compared with a Spooler preset for this printer; nothing was sent.", name=name))
    for key in sorted(_filament_profiles.ORCA_SETTINGS_KEYS & set(base)):
        value, was = preset.config_value(key), base[key]
        was = was if isinstance(was, list) else orca_items(str(was), key)
        if value is not None and not _same(orca_items(value, key), was):
            changes[key] = (value, _orca_text(was, key))
    return name, changes, pick["where"]


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
        _core.log.info("Could not read Spoolman's version: %s", exc)
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


def send_changes(name: str, changes: dict, snapshot: dict, where: tuple | None = None) -> str:
    """Write a Spooler preset's changed settings into its filament's orca_settings field, in the
    section for the preset's printer, and rebuild the presets. Returns what happened, for the user.
    where, (filament id, printer preset), is for a preset that isn't Spooler's (one linked to a spool).
    Runs on a worker thread. Every request goes to the Spoolman the presets were built from."""
    with pinned_origin() as origin:
        if _filament_profiles._profiles.get("gen") not in (None, origin[1]):
            raise OriginChanged()
        return _send_changes(name, changes, snapshot, where)


def _send_changes(name: str, changes: dict, snapshot: dict, where: tuple | None = None) -> str:
    fid, target = where or next((key[:2] for key, known in _filament_profiles._profiles["names"].items() if known == name), (None, ""))
    if fid is None:
        raise RuntimeError(_i18n.tr("{name} is no longer a Spooler preset. Refresh, then send it again.", name=name))
    filament = spoolman_call("GET", f"filament/{int(fid)}")
    base = _filament_profiles.orca_settings_data(filament)
    data = _filament_profiles.orca_settings_data(filament)
    if data is None:  # Never overwrite what can't be read back.
        raise RuntimeError(_i18n.tr("The {field} field of {name}'s filament isn't a JSON object; "
                              "fix it in Spoolman, then send again.", field=_filament_profiles.ORCA_SETTINGS_FIELD, name=name))
    # What Spoolman gives this printer now; a setting that differs from what the preset was made
    # from was changed in Spoolman meanwhile, and Spoolman's value is kept.
    now = _filament_profiles.profile_preset(filament, name, "", target)
    section, native, sent, kept, other = {}, {}, [], [], []
    for key, (text, saved) in sorted(changes.items()):
        if key not in _filament_profiles.ORCA_SETTINGS_KEYS:
            other.append(key)
        elif where is None and key in now and not _same(now[key], orca_items(saved or "", key)):
            # A Spooler preset's saved value is what Spoolman gave it: another value means Spoolman
            # changed since. Your own linked preset's saved value is yours, so it says nothing of that.
            kept.append(key)
        elif key in _filament_profiles.NATIVE_KEYS and native_value(key, text, filament) is not None:
            native[_filament_profiles.NATIVE_KEYS[key]] = native_value(key, text, filament)
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
                for key in _filament_profiles.NATIVE_KEYS:
                    if _filament_profiles.NATIVE_KEYS[key] in native:
                        values.pop(key, None)
    if section or (native and _filament_profiles.orca_settings_data(filament) != data):
        if _filament_profiles.ORCA_SETTINGS_FIELD not in {field["key"] for field in spoolman_call("GET", "field/filament")}:
            spoolman_call("POST", f"field/filament/{_filament_profiles.ORCA_SETTINGS_FIELD}",
                          {"name": "Orca settings", "field_type": "text"})
        if section:  # Last, so it beats any other section that matches the printer.
            data[target] = {**data.pop(target, {}), **section}
        # Read again just before writing and merge: a setting or field changed in Spoolman since
        # the first read is kept. This narrows the window but isn't atomic: Spoolman has no
        # precondition for a PATCH, so a change landing between this read and the PATCH can
        # still be overwritten (only orca_settings itself on a Spoolman that merges extra).
        fresh = spoolman_call("GET", f"filament/{int(fid)}")
        remote = _filament_profiles.orca_settings_data(fresh) if isinstance(fresh, dict) else None
        if remote is None:
            raise RuntimeError(_i18n.tr("The {field} field of {name}'s filament changed in Spoolman "
                                  "and isn't a JSON object now; fix it in Spoolman, then send again.",
                                  field=_filament_profiles.ORCA_SETTINGS_FIELD, name=name))
        data, clashes = merge_settings(base, data, remote, target)
        for key in clashes:
            if key in sent:
                sent.remove(key)
                kept.append(key)
                native.pop(_filament_profiles.NATIVE_KEYS.get(key), None)
                patch.pop(_filament_profiles.NATIVE_KEYS.get(key), None)
        kept.sort()
        value = json.dumps(json.dumps(data))
        version = spoolman_version(fresh=True)
        if version is None:
            # Unknown, it could replace the whole map or merge it: write nothing rather than guess.
            raise VersionUnknown(_i18n.tr(_editor.EDITOR_NO_VERSION))
        if version >= SPOOLMAN_EXTRA_PARTIAL:
            # Spoolman merges extra key by key (from 0.22): send only the one field this changes.
            patch["extra"] = {_filament_profiles.ORCA_SETTINGS_FIELD: value}
        else:
            # Older Spoolman replaces the whole extra map, so every field goes back, as just read.
            patch["extra"] = {**(fresh.get("extra") or {}), _filament_profiles.ORCA_SETTINGS_FIELD: value}
    if patch:
        spoolman_call("PATCH", f"filament/{int(fid)}", patch)
    # Always, so the presets also take the values Spoolman kept. OrcaSlicer's reload keeps every
    # unsaved edit, so a kept setting's edit stays unsaved for the user to send again or discard.
    _auto["kept"][name] = set(kept)
    result = _peers.load_spools_synced(snapshot) or {}
    rebuild_error = (result.get("profiles") or {}).get("error") if result.get("ok") else result.get("error")
    notes = []
    if sent:
        notes.append(_i18n.tr("Sent {settings} to Spoolman for {name}.", settings=", ".join(sent), name=name))
    if kept and where is not None:  # your own preset isn't rebuilt from Spoolman: it keeps your value
        notes.append(_i18n.tr("Kept Spoolman's newer value for {fields}: it changed there while you were editing.",
                        fields=", ".join(kept)))
    elif kept:
        notes.append(_i18n.tr("Kept Spoolman's newer value for {settings}: the preset now has it, and your "
                        "change stays unsaved; send again to use yours, or discard it.", settings=", ".join(kept)))
    if other:
        notes.append(_i18n.tr("Not sent: {settings}. Spoolman's {field} field holds only "
                        "calibration settings; colour, vendor, material and name come from its own fields.",
                        settings=", ".join(other), field=_filament_profiles.ORCA_SETTINGS_FIELD))
    if rebuild_error:
        notes.append(_i18n.tr("The presets were not rebuilt: {error}", error=rebuild_error))
    return _i18n._sentences(notes)


def native_value(key: str, text: str, filament: dict) -> float | None:
    """The Spoolman field value for an OrcaSlicer setting kept in one: cost is per kg in
    OrcaSlicer and per spool in Spoolman."""
    items = orca_items(text, key)
    number = _filament_profiles._number(items[0]) if len(set(items)) == 1 else None
    if number is None or number <= 0:
        return None
    if key != "filament_cost":
        return number
    weight = _filament_profiles._num(filament.get("weight"))
    return round(number * weight / 1000, 6) if weight else None


# Edits made in OrcaSlicer reach Spoolman by themselves: every tick the open Spooler preset's
# unsaved calibration changes are read, and once they have stayed the same for a tick (so a value
# being typed isn't sent half done) they are sent. The same changes are never sent twice, so a
# setting Spoolman kept its own value for doesn't loop. "auto_send": false in the settings file
# turns it off; Send to Spoolman still works.
_auto: dict = {"seen": None, "sent": None, "busy": False, "kept": {}}


def auto_send(post) -> None:
    """Send settled preset edits to Spoolman. Call it on the UI thread."""
    if _auto["busy"] or _sources.source() != "spoolman" or not _core.parse_flag(_core.get_settings().get("auto_send"), True):
        return
    if _sources.source_failing():  # unreachable: wait for the next good read rather than report every tick
        return
    try:
        name, changes = edited_changes()
    except Exception:
        _auto["seen"] = None
        return
    # A setting Spoolman kept its own value for is only sent again by hand.
    kept = _auto["kept"].get(name, set())
    changes = {key: value for key, value in changes.items() if key in _filament_profiles.ORCA_SETTINGS_KEYS and key not in kept}
    mark = (name, tuple(sorted((key, value[0]) for key, value in changes.items())))
    if not changes or mark == _auto["sent"] or mark != _auto["seen"]:
        _auto["seen"] = mark
        return
    _auto["sent"] = mark
    # Calibrated values follow "Save calibrated values to Spoolman": asked about (Ask), left
    # unsent (Never) or sent with the rest (Automatically). Sending only the other settings leaves
    # the calibrated ones in orca_settings as Spoolman has them: the send merges key by key.
    mode = calibration_mode()
    calibrated = {key: value for key, value in changes.items() if key in CALIBRATION_KEYS}
    if calibrated and mode != "auto":
        changes = {key: value for key, value in changes.items() if key not in CALIBRATION_KEYS}
        if mode == "ask":
            offer_calibration(name, calibrated)
    if not changes:
        return
    _core.log.info("Sending %s's edits to Spoolman", name)
    start_send(post, (name, changes), auto=True)


# Save on a Spooler preset makes a separate user copy (OrcaSlicer can't save over a plugin's
# preset). When that copy was made from a Spooler preset, its changed calibration settings are
# offered for Spoolman too (or sent, or left, as "save_calibration" says), so the next rebuild of
# the Spooler preset has them. The copy itself is left as it is.
_recent_filaments: list = []  # the filament presets picked last, newest last


def note_filament_selected(name: str) -> None:
    if name:
        _recent_filaments[:] = [n for n in _recent_filaments if n != name][-4:] + [name]


def saved_copy_changes(name: str) -> tuple[str, dict] | None:
    """(Spooler preset name, {setting: (copy's text, Spooler preset's text)}) for a user preset
    just saved from a Spooler preset, or None when it wasn't one or nothing calibrated changed.
    Call it on the UI thread."""
    if not name or name.startswith(_filament_profiles.PROFILE_PREFIX):
        return None
    filaments = orca.host.preset_bundle().filaments
    copy = filaments.find_preset(name)
    # The filament picked just before the save, not counting the copy (OrcaSlicer picks it
    # after saving): the preset that was being edited. Only a Spooler preset counts.
    before = [n for n in _recent_filaments if n != name]
    origin = before[-1] if before and before[-1].startswith(_filament_profiles.PROFILE_PREFIX) else ""
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
    for key in sorted(_filament_profiles.ORCA_SETTINGS_KEYS):
        mine, theirs = copy.config_value(key), spooler.config_value(key)
        if mine is not None and mine != theirs:
            changes[key] = (mine, theirs or "")
    return (origin[len(_filament_profiles.PROFILE_PREFIX):], changes) if changes else None


CALIBRATION_MODES = ("ask", "auto", "never")
# Units of the calibration values Spooler has its own Spoolman fields for, shown beside them.
# The calibrated values "Save calibrated values to Spoolman" holds back from unsaved edits.
# One read-modify-write of the waiting prompts and skips at a time: the UI thread adds prompts
# while a send's worker thread puts a failed one back.
_calib_lock = threading.Lock()
CALIBRATION_KEYS = frozenset(key for key, _label, _unit in _filament_profiles.CALIBRATION_FIELDS.values())
# Units shown beside the values in a prompt (OrcaSlicer's own units for these settings).
CALIBRATION_UNITS = {
    **{key: unit for key, _label, unit in _filament_profiles.CALIBRATION_FIELDS.values() if unit},
    **dict.fromkeys((*_filament_profiles.BED_TEMP_KEYS, "nozzle_temperature", "nozzle_temperature_initial_layer",
                     "nozzle_temperature_range_low", "nozzle_temperature_range_high", "chamber_temperature",
                     "temperature_vitrification"), "°C"),
    **dict.fromkeys(("filament_retraction_speed", "filament_deretraction_speed", "filament_ironing_speed",
                     "slow_down_min_speed"), "mm/s"),
    **dict.fromkeys(("filament_retraction_length", "filament_z_hop", "filament_ironing_spacing",
                     "filament_ironing_inset", "filament_diameter"), "mm"),
    **dict.fromkeys(("fan_min_speed", "fan_max_speed", "overhang_fan_speed", "additional_cooling_fan_speed"), "%"),
    "filament_density": "g/cm³", "slow_down_layer_time": "s", "filament_minimal_purge_on_wipe_tower": "mm³",
}


def parse_calibration_mode(value: object) -> str:
    return value if value in CALIBRATION_MODES else "ask"


def calibration_mode() -> str:
    """Save calibrated values to Spoolman: ask (the default), auto or never."""
    return parse_calibration_mode(_core.get_settings().get("save_calibration"))


def save_calibration_mode(value: object) -> None:
    if value in CALIBRATION_MODES:
        _core.update_settings({"save_calibration": value})


def _asks() -> dict:
    """Change sets waiting for Save or Skip, kept in the settings file so a restart doesn't lose
    them: {Spooler preset name: {setting: (new, old)}}, oldest first."""
    saved = _core.get_settings().get("calibration_asks")
    asks = {}
    for name, changes in (saved.items() if isinstance(saved, dict) else ()):
        if isinstance(changes, dict):
            asks[str(name)] = {str(key): (str(pair[0]), str(pair[1])) for key, pair in changes.items()
                               if isinstance(pair, (list, tuple)) and len(pair) == 2 and key in _filament_profiles.ORCA_SETTINGS_KEYS}
    return {name: changes for name, changes in asks.items() if changes}


def _save_asks(asks: dict) -> None:
    _core.update_settings({"calibration_asks": {
        name: {key: list(pair) for key, pair in changes.items()} for name, changes in asks.items()}})


def calibration_asks() -> list[dict]:
    """The change sets waiting on the page, oldest first."""
    return [{"name": name, "changes": [{"key": key, "old": old, "new": new, "unit": CALIBRATION_UNITS.get(key, "")}
                                       for key, (new, old) in sorted(changes.items())]}
            for name, changes in _asks().items()]


def _calib_mark(changes: dict) -> dict:
    return {key: new for key, (new, _old) in changes.items()}


def _post_asks() -> None:
    _plate_check.send_plate_message({"type": "calibration", "asks": calibration_asks()})


def offer_calibration(target: str, changes: dict) -> None:
    """Put a change set up for Save or Skip on the page, unless it was skipped or is already
    waiting as it is."""
    with _calib_lock:
        # Skipped values aren't asked about again until they change.
        if (_core.get_settings().get("calibration_skipped") or {}).get(target) == _calib_mark(changes):
            return
        asks = _asks()
        if asks.get(target) == changes:
            return
        asks.pop(target, None)
        _save_asks({**asks, target: changes})
    _plate_check.push_notice("info", _i18n.tr("Spooler: {name} has new calibrated values. Open Spooler to save them to "
                           "Spoolman or skip them.", name=target))
    _post_asks()


def send_saved_copy(name: str) -> None:
    """On PresetSaved: offer a saved copy's calibration changes for Spoolman, or send them when
    the setting says so. Never raises."""
    try:
        mode = calibration_mode()
        if _sources.source() != "spoolman" or mode == "never":
            return
        edits = saved_copy_changes(name)
        if edits is None:
            return
        if mode == "ask":
            _core.log.info("%s was saved from %s; asking before sending its changes to Spoolman", name, edits[0])
            offer_calibration(*edits)
            return
        _core.log.info("%s was saved from %s; sending its changes to Spoolman", name, edits[0])

        def done(result: dict) -> None:
            _plate_check.push_notice("info" if result.get("ok") else "warning", _i18n.tr("Spooler: {text}", text=result.get("text")))

        start_send(done, edits)
    except Exception:
        _core.log.exception("Could not send the saved copy %s to Spoolman", name)


def answer_calibration(data: dict, post) -> None:
    """The page's Save or Skip for one waiting change set. Save sends it the usual way (read again
    and merged just before writing); Skip remembers the values so the same ones aren't asked again."""
    name = str(data.get("name") or "")
    skip = data.get("type") == "calibration_skip"
    with _calib_lock:
        asks = _asks()
        changes = asks.pop(name, None)
        if changes is not None:
            _save_asks(asks)
            if skip:
                _core.update_settings(lambda now: {"calibration_skipped": {
                    **(now.get("calibration_skipped") or {}), name: _calib_mark(changes)}})
    if changes is None or skip:
        post({"type": "calibration", "asks": calibration_asks()})
        return

    def done(result: dict) -> None:
        # On the worker thread, while the UI thread may be adding a prompt: hence the lock.
        with _calib_lock:
            if not result.get("ok"):
                asks = _asks()
                if name not in asks:  # not written: still waiting, unless a newer set replaced it
                    _save_asks({**asks, name: changes})
            elif name in (_core.get_settings().get("calibration_skipped") or {}):
                _core.update_settings(lambda now: {"calibration_skipped": {
                    k: v for k, v in (now.get("calibration_skipped") or {}).items() if k != name}})
        post(result)
        post({"type": "calibration", "asks": calibration_asks()})

    start_send(done, (name, changes))


def start_send(post, edits: tuple | None = None, auto: bool = False, chosen: dict | None = None) -> None:
    """Send preset changes to Spoolman: edits (name, changes), else those of the preset picked on the
    page (chosen: {"spool", "preset"}), else the unsaved changes of the Spooler preset open in
    OrcaSlicer. Call it on the UI thread, where the presets are read; post() gets {"type": "sent",
    "ok": ..., "text": ...} when it is done."""
    where = None
    try:
        if _auto["busy"]:
            raise RuntimeError(_i18n.tr("Already sending to Spoolman; try again in a moment."))
        if _sources.source() != "spoolman":
            raise RuntimeError(_i18n.tr("Sending needs Spoolman as the source."))
        snapshot = _moonraker.refresh_snapshot()
        if snapshot is None:
            raise RuntimeError(_i18n.tr("Could not read OrcaSlicer's presets."))
        if chosen is not None:
            name, changes, where = chosen_changes(chosen)
            if not changes:
                text = _i18n.tr("{name} has no unsaved changes, and its saved settings match Spoolman: nothing to send.", name=name) \
                    if where else _i18n.tr("{name} has no unsaved changes to send.", name=name)
                post({"type": "sent", "ok": True, "text": text})
                return
        else:
            name, changes = edits or edited_changes()
    except Exception as exc:
        _core.log.warning("Send to Spoolman: %s", exc)
        if auto:
            _auto["sent"] = None  # so the next tick tries again
        post({"type": "sent", "ok": False, "text": str(exc)})
        return
    if not auto:
        _auto["kept"].pop(name, None)

    def worker():
        try:
            text, ok = send_changes(name, changes, snapshot, where), True
        except Exception as exc:
            _core.log.exception("Sending %s to Spoolman failed", name)
            text, ok = _rfid._spoolman_error(exc), False
            # The next tick tries again, but not after an unreadable version: that would fail and
            # report every 10 s. The same edits are then sent again only by hand or once they change.
            if auto and not isinstance(exc, VersionUnknown):
                _auto["sent"] = None
        finally:
            _auto["busy"] = False
        post({"type": "sent", "ok": ok, "text": text})

    _auto["busy"] = True

    _filament_profiles.spawn(worker)


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import core as _core  # noqa: E402
from . import editor as _editor  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
