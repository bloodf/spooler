# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""OrcaSlicer filament profiles made from spools, and the preset options of Settings > Presets."""

import hashlib
import json
import math
import os
import re
import shutil
import threading
import time
import unicodedata
import urllib.parse
from pathlib import Path

import orca

# Material names and the parent preset choice (best_parent) are shared with U1 Control and Kobra Control.
from .filmatch import (  # noqa: F401  (MATERIAL_ALIASES, OFD_ORIGIN: used by other modules)
    MATCHES_FILE,
    MATERIAL_ALIASES,
    OFD_DIR,
    OFD_ORIGIN,
    PARENT_MARGIN,
    best_parent,
    confident,
    load_matches,
    ofd_index,
    ofd_preset,
    ofd_values,
    parent_score,
    rank_ofd,
    rank_parents,
    recall,
    remember,
)
from .filmatch import material_key as _material_key

# --- Filament profiles -------------------------------------------------------------------
# For each of your printers, one OrcaSlicer filament preset per Spoolman filament, written as a
# local preset bundle and hot-reloaded. Each one is a standalone copy of the closest preset
# OrcaSlicer already has for that printer (so the printer's own tuning is kept), refreshed on every
# rewrite and on Sync Presets, with a filament_id of its own (see flat_preset), is limited to that printer, and
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
# Every bed plate type's temperature keys (OrcaSlicer's PrintConfig.cpp; 0 means "can't print on it").
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
_parent_cache: dict = {"key": None, "parents": [], "configs": {}}


def _first(value: object) -> str:
    items = _plate_check.split_list(value)
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
        printers = [p for p in _plate_check.split_list(preset.config_value("compatible_printers")) if p]
        condition = str(preset.config_value("compatible_printers_condition") or "").strip()
        if not printers and condition:
            continue  # Can't evaluate the condition here, so don't guess.
        found.append({"name": preset.name, "vendor": _first(preset.config_value("filament_vendor")),
                      "type": _first(preset.config_value("filament_type")), "printers": printers})
    return found


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
    if material and _plate_check._norm(material) not in _plate_check._norm(name):
        name = f"{material} {name}".strip()
    if vendor and _plate_check._norm(vendor) not in _plate_check._norm(name):
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
    return _sources._hex6(filament.get("color_hex")) or _sources._hex6(multi[0].strip()) or "FFFFFF"


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


def bed_temps(bed: float, parent_config: dict | None) -> dict:
    """Spoolman's bed temperature on the plates where the parent uses its Smooth PEI / High Temp plate
    temperature (hot_plate_temp, OrcaSlicer's default plate), per layer. A plate the parent sets
    differently (Cool Plate, SuperTack, or 0 for a plate it can't print on) keeps the parent's value.
    Without the parent's values, only the hot plate keys are set."""
    config = parent_config or {}
    temps = {}
    for key in BED_TEMP_KEYS:
        ref = "hot_plate_temp" + ("_initial_layer" if key.endswith("_initial_layer") else "")
        if key == ref or (config.get(ref) is not None and config.get(key) == config.get(ref)):
            temps[key] = [_fmt(bed)]
    return temps


def profile_preset(filament: dict, name: str, parent: str, target: str,
                   spool_cost: float | None = None, tune: dict | None = None,
                   parent_config: dict | None = None) -> dict:
    """The preset JSON for one Spoolman filament on one printer. Values are lists of strings,
    as OrcaSlicer stores them; one value applies to every nozzle variant of the parent.
    spool_cost is the price per kg from the filament's spools, used when the filament has none.
    tune is the material's Advanced tuning row; the filament's own Spoolman values win over it.
    parent_config is the parent's settings ({key: serialized text}), when read, for bed_temps."""
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
        preset.update(bed_temps(bed, parent_config))
    for key, field in (("filament_density", "density"), ("filament_diameter", "diameter")):
        value = _num(filament.get(field))
        if value:
            preset[key] = [_fmt(value)]
    price, weight = _num(filament.get("price")), _num(filament.get("weight"))
    if price and weight:
        preset["filament_cost"] = [_fmt(round(price / weight * 1000, 2))]
    elif spool_cost:
        preset["filament_cost"] = [_fmt(round(spool_cost, 2))]
    for key in TUNING_KEYS:
        if (tune or {}).get(key) is not None:
            preset[key] = [_fmt(tune[key])]
            if key == "pressure_advance":
                preset["enable_pressure_advance"] = ["1"]
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
    pinned = getattr(_spoolman_sync._op, "origin", None)
    url = pinned[0] if pinned else _sources.clean_url(_core.get_settings().get("spoolman_url"))
    if not url or url == _sources.BAMBU_KEY or url in _fields_ready or time.monotonic() - _fields_failed.get(url, -PROFILE_RETRY) < PROFILE_RETRY:
        return
    try:
        have = {field.get("key") for field in _spoolman_sync.spoolman_call("GET", "field/filament") or []}
        for order, (field, (_key, label, unit)) in enumerate(CALIBRATION_FIELDS.items(), start=100):
            if field not in have:
                body = {"name": label, "field_type": "float", "order": order}
                if unit:
                    body["unit"] = unit
                _spoolman_sync.spoolman_call("POST", f"field/filament/{field}", body)
                _core.log.info("Added the %s field to Spoolman", field)
        have = {field.get("key") for field in _spoolman_sync.spoolman_call("GET", "field/spool") or []}
        own = [(_core.DRIED_FIELD, {"name": "Dried", "field_type": "datetime", "order": 100})]
        if presets_settings()["per_spool"]:  # only once someone uses it; Edit Spool adds it too
            own.append((USE_WITH_FIELD, USE_WITH_DEF))
        for field, body in own:
            if field not in have:
                _spoolman_sync.spoolman_call("POST", f"field/spool/{field}", body)
                _core.log.info("Added the %s field to Spoolman", field)
        _fields_ready.add(url)
    except Exception as exc:
        _core.log.warning("Could not add Spooler's fields to Spoolman: %s", exc)
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
                _core.log.warning("orca_settings of filament %s: %s is not a setting Spooler applies; ignored",
                            filament.get("id"), key)
    return out


# --- Preset options (Settings > Presets) -------------------------------------------------------
# Presets are made per filament (one per filament and printer) or, when "per_spool" is on, per
# spool: "<filament> #<spool id> @<printer>", made for the printers in the spool's "Use with" field,
# else the printer it is loaded on (a Printer tab slot or a Live Link report), else every printer.
# Advanced tuning ("tuning" on) sets, per material, the base preset to inherit and values over it;
# a filament's own Spoolman values (calibration fields, orca_settings) still win over those.
USE_WITH_FIELD = "use_with"  # Spoolman spool extra field (text): a JSON list of printer presets
USE_WITH_MAX = 16
USE_WITH_DEF = {"name": "Use with", "field_type": "text", "order": 101}
USE_WITH_NO_FIELD = "Spoolman refused to add the Use with field ({error}); nothing was written."
# Your own OrcaSlicer filament preset for a spool, by name, in this text field of the spool or, for every
# spool of a filament, of the filament (the spool's wins). A linked spool gets no preset of Spooler's:
# wherever Spooler would pick its own preset it picks yours. U1 Control and Kobra Control read it too.
PRESET_LINK_FIELD = "orca_filament_preset"
PRESET_LINK_DEF = {"name": "OrcaSlicer preset", "field_type": "text", "order": 102}
PRESET_LINK_MAX = 256  # characters of a preset name
PRESET_LINK_LIST = 500  # user presets offered in the editor
PRESET_LINK_NO_FIELD = "Spoolman refused to add the OrcaSlicer preset field ({error}); nothing was written."


def _link_text(holder: object) -> str:
    """The preset named in a spool's or filament's orca_filament_preset field (JSON text in Spoolman,
    or typed by hand), or ''."""
    raw = (holder.get("extra") or {}).get(PRESET_LINK_FIELD) if isinstance(holder, dict) else None
    try:
        text = json.loads(raw) if isinstance(raw, str) else raw
    except ValueError:
        text = raw
    return text.strip()[:PRESET_LINK_MAX] if isinstance(text, str) else ""


def linked_preset(spool: object) -> str:
    """Your own OrcaSlicer preset for this spool: its own field, else its filament's; '' for none."""
    return _link_text(spool) or _link_text(spool.get("filament") if isinstance(spool, dict) else None)


def link_fits(name: str, target: str, snap: dict) -> bool:
    """Whether your linked preset name is one of your own presets OrcaSlicer would take on printer target:
    for the selected printer, OrcaSlicer's own compatibility check; for another, the preset's compatible
    printers (none listed and no condition: every printer). Elsewhere Spooler's own preset is used."""
    info = (snap.get("user_compat") or {}).get(name)
    if not name or name.startswith("_local/") or info is None:
        return False
    if target == snap.get("selected"):
        return bool(info["now"])
    return target in info["printers"] if info["printers"] else not info["cond"]


def spool_link(spool: object, target: str, snap: dict) -> str:
    """The spool's linked preset when it fits printer target, else ''."""
    name = linked_preset(spool)
    return name if link_fits(name, target, snap) else ""


def _link_value(name: object) -> str | None:
    """The orca_filament_preset field as Spoolman keeps it (JSON text; an empty text clears it, which
    Spoolman 0.22 to 0.25 take too), or None when the page sent something else."""
    if name is None or name == "":
        return json.dumps("")
    if not isinstance(name, str) or not name.strip() or len(name.strip()) > PRESET_LINK_MAX or \
            any(ord(c) < 32 for c in name) or name.strip().startswith("_local/"):
        return None  # a plugin's preset (Spooler's own too): Sync would stop making it, and the link dangle
    return json.dumps(name.strip())


TUNING_KEYS = {  # OrcaSlicer filament keys (all in ORCA_SETTINGS_KEYS) and the range taken for each
    "filament_flow_ratio": (0.01, 2.0), "pressure_advance": (0.0, 2.0),
    "filament_retraction_length": (0.0, 50.0), "filament_retraction_speed": (1.0, 500.0),
    "filament_max_volumetric_speed": (0.1, 200.0), "fan_min_speed": (0.0, 100.0), "fan_max_speed": (0.0, 100.0),
}
TUNING_ROWS_MAX = 40
PARENT_MAX = 120


def _tune_number(value: object, low: float, high: float) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        return None
    return round(float(value), 4) if low <= value <= high else None


def parse_presets(value: object) -> dict:
    """{"per_spool": bool, "tuning": bool, "materials": {MATERIAL: {"parent": base name, key: number}}};
    rows with nothing set and values out of range are dropped."""
    value = value if isinstance(value, dict) else {}
    rows = value.get("materials") if isinstance(value.get("materials"), dict) else {}
    table: dict = {}
    for key, row in list(rows.items())[:TUNING_ROWS_MAX]:
        name = " ".join(str(key).split()).upper()[:24]
        if not name or not isinstance(row, dict):
            continue
        clean: dict = {}
        parent = row.get("parent")
        if isinstance(parent, str) and parent.strip():
            clean["parent"] = " ".join(parent.split())[:PARENT_MAX]
        for setting, (low, high) in TUNING_KEYS.items():
            number = _tune_number(row.get(setting), low, high)
            if number is not None:
                clean[setting] = number
        if clean:
            table[name] = clean
    return {"per_spool": _core.parse_flag(value.get("per_spool"), False), "tuning": _core.parse_flag(value.get("tuning"), False),
            "materials": table, "ofd": _core.parse_flag(value.get("ofd"), False)}


def presets_settings() -> dict:
    return parse_presets(_core.get_settings().get("presets"))


def save_presets(value: object) -> None:
    """Save Settings > Presets on its own, like the display flags. The OFD consent ("ofd") is kept as stored: it is
    given in Add Spool and revoked in Settings by their own messages (set_ofd_consent), never by a form saved later."""
    if isinstance(value, dict):
        _core.update_settings({"presets": {**parse_presets(value), "ofd": presets_settings()["ofd"]}})


def set_ofd_consent(on: bool) -> None:
    """The user's consent to contact the Open Filament Database (Add Spool > Look up, Settings > Presets > Revoke).
    Kept as presets["ofd"], the key of the 0.33 Settings toggle, so a toggle that was on counts as consent."""
    _core.update_settings({"presets": {**presets_settings(), "ofd": bool(on)}})


def tuning_for(filament: dict, opts: dict) -> dict:
    """The tuning row for a filament's material (the longest row name it starts with, or its
    OrcaSlicer material's), {} when tuning is off or no row fits."""
    table = (opts.get("materials") or {}) if opts.get("tuning") else {}
    material = filament.get("material")
    for name in dict.fromkeys((_tune_name(material), _tune_name(MATERIAL_ALIASES.get(_material_key(material), "")))):
        best = max((k for k in table if _tune_fits(name, _tune_name(k))), key=lambda k: len(_tune_name(k)), default=None)
        if best:
            return table[best]
    return {}


def _tune_name(text: object) -> str:
    return " ".join(re.sub(r"[-_]", " ", str(text or "")).upper().split())


def _tune_fits(name: str, row: str) -> bool:
    """A row covers its material and variants written after a separator or "+" (PLA: PLA+, PLA-CF,
    PLA Silk), not another material that starts the same (PC: not PCTG; PP: not PPA)."""
    return bool(row) and (name == row or (name.startswith(row) and name[len(row)] in " +"))


def tuned_parent(base: str, target: str, parents: list[dict]) -> str:
    """The system preset named base ("Generic PLA", the part before "@") made for this printer, or
    for every printer; '' when the printer has none."""
    want = " ".join(base.split()).casefold()
    found = [c for c in parents if c["name"].split("@")[0].strip().casefold() == want
             and (not c["printers"] or target in c["printers"])]
    return min(found, key=lambda c: (target not in c["printers"], len(c["name"])))["name"] if found else ""


def parent_bases(parents: list[dict]) -> list[dict]:
    """The base presets Advanced tuning offers: [{"name": "Generic PLA", "type": "PLA"}], sorted."""
    seen = {c["name"].split("@")[0].strip(): c.get("type") or "" for c in parents if c["name"].split("@")[0].strip()}
    return [{"name": name, "type": seen[name]} for name in sorted(seen, key=str.casefold)]


def use_with(spool: dict, printers: list[dict]) -> list[str] | None:
    """The printer presets a spool's Use with field names (by preset or label, case ignored), in
    printer order; None when it is empty, unreadable or names none of them (the default applies)."""
    raw = (spool.get("extra") or {}).get(USE_WITH_FIELD) if isinstance(spool, dict) else None
    try:
        text = json.loads(raw) if isinstance(raw, str) else raw  # Spoolman stores text as JSON
    except ValueError:
        text = raw
    try:
        items = json.loads(text) if isinstance(text, str) and text.strip().startswith("[") else text
    except ValueError:
        items = None
    if isinstance(items, str):
        items = re.split(r"[;,\n]", items)  # typed by hand in Spoolman's form
    if not isinstance(items, list):
        return None
    key = lambda text: " ".join(str(text or "").split()).casefold()  # noqa: E731
    wanted = {key(i) for i in items if isinstance(i, str) and i.strip()}
    found = [p["target"] for p in printers if key(p["target"]) in wanted or key(p.get("label")) in wanted]
    return found or None


def _host_name(address: object) -> str:
    text = str(address or "").strip()
    try:
        return (urllib.parse.urlsplit(text if "://" in text else "http://" + text).hostname or "").lower()
    except ValueError:
        return ""


def loaded_targets(printers: list[dict]) -> dict:
    """{spool id as text: {printer presets}} for the spools in a Printer tab slot or reported by a
    Live Link printer. A printer is matched to its OrcaSlicer presets as the Printer tab chose them
    (slice_map), else by address; with one preset only, every printer is that one."""
    by_host = {_host_name(h): p["target"] for p in printers for h in p.get("hosts") or [] if _host_name(h)}
    only = printers[0]["target"] if len(printers) == 1 else ""
    known = {p["target"] for p in printers}
    picked: dict = {}
    for preset, pid in _netprinters.slice_map().items():
        if preset in known:
            picked.setdefault(pid, set()).add(preset)
    live = {p["id"]: p for p in _live_updates.live_snapshot()["printers"]}
    out: dict = {}
    for printer in _printers.printers_cfg():
        targets = picked.get(printer.get("id")) or {by_host.get(_host_name(printer.get("ip")), only)} - {""}
        if not targets:
            continue
        ids = [s for unit in printer.get("units") or [] for s in unit.get("slots") or []]
        now = live.get(printer.get("id")) or {}
        trays = [t for unit in now.get("units") or [] for t in unit.get("trays") or []] + [now.get("ext") or {}]
        ids += [t.get("spool") for t in trays]
        for sid in ids:
            if sid not in (None, ""):
                out.setdefault(str(sid), set()).update(targets)
    return out


def spool_targets(spool: dict, printers: list[dict], loaded: dict) -> list[str]:
    """The printer presets a spool's own preset is made for: its Use with field, else the printer it
    is loaded on, else every printer."""
    chosen = use_with(spool, printers)
    if chosen is not None:
        return chosen
    here = loaded.get(str(spool.get("id"))) or set()
    return [p["target"] for p in printers if p["target"] in here] or [p["target"] for p in printers]


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


def spool_profile_names(spools: list[dict], printers: list[dict], loaded: dict) -> dict:
    """{(filament id, printer preset, spool id): preset name} for each spool not archived, on the
    printers spool_targets() gives it. The spool id keeps names unique and the same across syncs."""
    labels = {p["target"]: _safe_name(p["label"])[:LABEL_MAX].strip() for p in printers}
    by_key: dict = {}
    for spool in sorted(_core.active_spools(spools or []), key=lambda s: str(s.get("id")).zfill(12)):
        filament = spool.get("filament")
        if not isinstance(filament, dict) or filament.get("id") is None or spool.get("id") is None:
            continue
        for target in spool_targets(spool, printers, loaded):
            by_key[(filament["id"], target, spool["id"])] = f"{profile_name(filament)} #{spool['id']} @{labels[target]}"
    return by_key


# OrcaSlicer refuses the whole bundle over one key it doesn't know or one value of the wrong shape,
# so every preset is checked before it is written: these keys only, each a list of text (but
# compatible_printers_condition, text), number settings one number, percentage or "nil" each.
PRESET_META = frozenset({"type", "name", "from", "instantiation", "inherits", "version", "filament_id",
                         "description"})
PRESET_KEYS = frozenset({"compatible_printers", "compatible_printers_condition", "filament_settings_id",
                         "default_filament_colour", "filament_vendor", *ORCA_SETTINGS_KEYS})
PRESET_TEXT = frozenset({"compatible_printers", "filament_settings_id", "default_filament_colour",
                         "filament_vendor", *TEXT_KEYS})


def _finite_text(text: str) -> bool:
    number = None if "," in text else _number(text)
    return number is not None and math.isfinite(number)


def preset_problem(preset: dict) -> str:
    """Why OrcaSlicer would refuse this preset, or '' when it is fine."""
    for key, value in preset.items():
        if key in PRESET_META or key == "compatible_printers_condition":
            if not isinstance(value, str):
                return f"{key} is not text"
        elif isinstance(value, str) and preset.get("inherits") == "":
            continue  # a standalone copy: the parent's own setting, as OrcaSlicer itself serialized it
        elif key not in PRESET_KEYS:
            return f"{key} is not a filament setting"
        elif not isinstance(value, list) or not value or not all(isinstance(v, str) for v in value):
            return f"{key} is not a list of text"
        elif key not in PRESET_TEXT and not all(v == "nil" or _finite_text(v) for v in value):
            return f"{key} is not a number"
    return ""


# A preset that inherits a system preset can't be loaded by OrcaSlicer's "sync from AMS": it only
# loads base presets (PresetCollection::get_preset_base(), which is the preset itself for a user
# preset whose "inherits" is empty), matched by filament_id (PresetBundle::sync_ams_list). So each
# preset is written flat: the parent's whole config, then Spooler's values, "inherits" empty, and a
# filament_id of its own that printer agents report for a tray holding that spool.
FLAT_SKIP = frozenset({"inherits", "compatible_printers", "compatible_printers_condition",
                       "filament_settings_id", "filament_id", "name", "version", "from", "instantiation",
                       "type", "setting_id", "description", "url", "is_custom_defined", "renamed_from",
                       "includes"})
FILAMENT_ID_PREFIX = "SPL"  # no OrcaSlicer system preset id starts with it (theirs: OF..., GF..., ...)


def spooler_filament_id(key: tuple) -> str:
    """The filament_id of the preset for a (filament id, printer preset[, spool id]) key: stable across
    rewrites, different for every key."""
    return FILAMENT_ID_PREFIX + hashlib.sha256("|".join(map(str, key)).encode("utf-8")).hexdigest()[:10].upper()


def flat_preset(preset: dict, parent_config: dict, key: tuple) -> dict:
    """preset (profile_preset's, which inherits its parent) as a root preset: the parent's settings
    (parent_config: {key: OrcaSlicer's serialized text}) under Spooler's own. A Spooler value of one item
    is repeated for every nozzle variant the parent has, as OrcaSlicer does for a preset that inherits."""
    flat = {k: v for k, v in parent_config.items() if k not in FLAT_SKIP and isinstance(v, str)}
    for k, v in preset.items():
        parent = flat.get(k)
        if isinstance(v, list) and len(v) == 1 and k not in PRESET_TEXT and isinstance(parent, str):
            v = v * max(1, len(parent.split(",")))
        flat[k] = v
    flat.update(inherits="", filament_id=spooler_filament_id(key),
                description=f"Spooler: standalone copy of {preset['inherits']}, refreshed on Sync Presets")
    return flat


def parent_configs(filaments, parents: list[dict], targets: set, cache: dict) -> dict:
    """{parent name: {key: serialized text}} for the parent candidates usable on these printers, read
    once per name into cache (system presets don't change while OrcaSlicer runs). UI thread."""
    for candidate in parents:
        name = candidate["name"]
        if name in cache or (candidate["printers"] and not targets & set(candidate["printers"])):
            continue
        # find_preset() answers the edited copy for the selected preset: read the saved one then.
        selected = filaments.get_selected_preset()
        preset = selected if getattr(selected, "name", None) == name else filaments.find_preset(name)
        if preset is None:
            continue
        values = {}
        for key in preset.config_keys():
            value = preset.config_value(key)
            if value is not None:
                values[str(key)] = str(value)
        cache[name] = values
    return dict(cache)


# --- Parent picked by hand (Edit Spool > Preset) ---------------------------------------------------
# The parent a filament's presets copy, picked by hand, is kept per printer in matches.json (filmatch) under
# "filament:<id>", next to the matches U1 Control and Kobra Control remember. It wins over Advanced tuning's parent and
# the scored pick while it is still one of the printer's system presets for the filament's material.
MATCH_CHOICES = 5  # candidates Edit Spool offers per printer
MATCH_REFUSED = "That preset can't be used for this filament on this printer."


def matches_path() -> Path:
    return _peers.bridge_dir() / MATCHES_FILE


def filament_key(filament_id: object) -> str:
    return f"filament:{filament_id}"


OFD_PICK = "ofd:"  # a remembered "ofd:<OFD id>": that OFD preset's values, over its parent, under Spoolman's
OFD_REFUSED = "The Open Filament Database preset can't be used: {why}"


def _ofd_layer(name: str, filament: dict, target: str, usable: dict) -> tuple[str, dict] | None:
    """For a remembered "ofd:<id>": (its parent, the OFD preset) while the preset kept in the OFD folder is still
    valid and its parent is a system preset this printer has for the filament's material; else None. No network."""
    if not name.startswith(OFD_PICK):
        return None
    folder = str(ofd_folder())
    profile = next((p for p in ofd_index(folder, offline=True)["profiles"] if p["id"] == name[len(OFD_PICK):]), None)
    if profile is None or profile["inherits"] not in usable:
        return None
    preset, problem = ofd_preset(folder, profile, parents=set(usable), offline=True)
    if problem or parent_score(usable[profile["inherits"]], filament, target) is None:
        return None
    return profile["inherits"], preset


def remembered_parent(filament: dict, target: str, parents: list[dict], store: dict) -> tuple[str, dict | None]:
    """(parent, OFD preset or None) picked by hand for this filament on this printer, while it still fits; else
    ("", None). An OFD pick is its preset's parent with the preset's values (see build_preset)."""
    usable = {c["name"]: c for c in parents}
    for name in recall([store], [filament_key(filament.get("id"))], target):
        layer = _ofd_layer(name, filament, target, usable)
        if layer:
            return layer
        if name in usable and parent_score(usable[name], filament, target) is not None:
            return name, None
    return "", None


def choose_parent(filament: dict, target: str, parents: list[dict], opts: dict, store: dict | None) -> tuple[str, str, dict | None]:
    """(parent, why, OFD preset or None): picked by hand ("remembered", or "ofd" for an Open Filament Database preset),
    Advanced tuning's ("tuned"), else the best score ("auto")."""
    remembered, ofd = remembered_parent(filament, target, parents, store) if store else ("", None)
    if remembered:
        return remembered, "ofd" if ofd else "remembered", ofd
    tune = tuning_for(filament, opts)
    tuned = tune.get("parent") and tuned_parent(tune["parent"], target, parents)
    return (tuned, "tuned", None) if tuned else (best_parent(filament, target, parents), "auto", None)


def with_ofd(preset: dict, ofd: dict | None) -> dict:
    """profile_preset's preset with an OFD preset's values under it: Spoolman's values and calibration still win."""
    if not ofd:
        return preset
    layered = dict(preset)
    for key, value in ofd_values(ofd).items():
        if key in PRESET_KEYS and key not in layered:
            layered[key] = value
    return layered


# --- Open Filament Database (Add Spool > Look up in OFD; nothing is contacted before the user's consent) ---------
# Add Spool lists the OFD presets of the new spool's manufacturer and material (filmatch.rank_ofd) once the user asked,
# from OFD's index kept a day in <data folder>/spooler/ofd/. A preset picked from it keeps resolving from that folder
# offline (_ofd_layer); listing, refreshing, editing and printing never fetch.
OFD_RETRY = 15 * 60   # s after a failed index fetch before Spooler asks OFD again (unless the user asks: Try again in Add Spool)
_ofd_fail: dict = {"at": None, "error": ""}

def ofd_folder() -> Path:
    return _peers.bridge_dir() / OFD_DIR


def ofd_lookup(force: bool = False, now: float | None = None) -> dict:
    """filmatch.ofd_index for a lookup the user asked for (consent given). filmatch fetches again whenever no index is
    kept, so without network every call would wait for the timeout: after a failed fetch this reads only what is kept
    for OFD_RETRY, unless force (Read again). Worker thread."""
    now = time.time() if now is None else now
    at = _ofd_fail["at"]
    backoff = not force and isinstance(at, (int, float)) and 0 <= now - at < OFD_RETRY
    found = ofd_index(str(ofd_folder()), force=force, now=now, offline=backoff)
    if backoff:
        return {**found, "error": found["error"] or _ofd_fail["error"]}
    _ofd_fail.update(at=now if found["error"] else None, error=found["error"])
    return found


def ofd_status(refresh: bool = False) -> dict:
    """Settings > Presets' OFD line: {"on"} (consent) and, with it, {"fetched", "version", "count", "stale", "error"}
    of the kept index; refresh (Read again) asks OFD now. Worker thread."""
    if not presets_settings()["ofd"]:
        return {"on": False}
    found = ofd_lookup(force=True) if refresh else ofd_index(str(ofd_folder()), offline=True)
    return {"on": True, "count": len(found["profiles"]), **{k: found[k] for k in ("fetched", "version", "stale", "error")}}


def ofd_suggest(vendor: object, material: object, name: object = "", retry: bool = False) -> dict:
    """Add Spool > Look up in OFD: the OFD presets of this manufacturer and material, best first. Only with the
    user's consent (the page sends it with the first click). retry: the user's Try again after a failed lookup, which
    asks OFD now instead of waiting out OFD_RETRY. Worker thread."""
    if not presets_settings()["ofd"]:
        return {"ok": False, "text": "", "consent": False}
    found = ofd_lookup(force=retry)
    text = lambda v: v.strip() if isinstance(v, str) else ""  # noqa: E731
    ofd = rank_ofd(found["profiles"], text(vendor), text(material), text(name), MATCH_CHOICES)
    return {"ok": True, "text": "", "consent": True, "ofd": ofd, "ofd_error": "" if found["profiles"] else found["error"]}


def preset_match(filament: object, snap: dict, store: dict | None = None) -> list[dict]:
    """Edit Spool's Preset rows, one per printer: the parent this filament's preset copies there, why, its score and
    reasons (filmatch codes), whether the pick is clear and the best candidates. Never contacts OFD: an OFD preset
    picked in Add Spool shows from the kept folder."""
    if not isinstance(filament, dict) or filament.get("id") is None:
        return []
    parents = snap.get("parents") or []
    store = load_matches(matches_path()) if store is None else store
    opts = presets_settings()
    rows = []
    for printer in snap.get("printers") or []:
        target = printer["target"]
        ranked = rank_parents(filament, target, parents)
        name, source, picked = choose_parent(filament, target, parents, opts, store)
        row = next((r for r in ranked if r["name"] == name), {})
        if picked:   # an Open Filament Database preset: shown by its name
            row, name = {"score": None, "reasons": []}, picked["name"]
        rows.append({"target": target, "label": printer.get("label") or target, "name": name, "source": source,
                     "score": row.get("score"), "reasons": row.get("reasons") or [],
                     "confident": source != "auto" or confident(ranked, PARENT_MARGIN), "candidates": ranked[:MATCH_CHOICES]})
    return rows


def pick_parent(filament: object, target: object, name: object, ofd: object = None) -> dict:
    """Edit Spool > Preset > Change: remember name as the parent of the filament's presets on printer target ("" or
    None: forget it, back to the automatic pick). Refused unless it is one of that printer's presets for the material.
    ofd: an Open Filament Database proposal's id instead (see ofd_pick_name)."""
    snap = _ui_snap
    refused = {"ok": False, "text": _i18n.tr(MATCH_REFUSED)}
    if not isinstance(filament, dict) or filament.get("id") is None or \
            target not in {p["target"] for p in snap.get("printers") or []}:
        return refused
    if ofd is not None:
        name = ofd_pick_name(filament, target, ofd, snap)
        if isinstance(name, dict):
            return name
    elif name:
        found = next((c for c in snap.get("parents") or [] if c["name"] == name), None)
        if found is None or parent_score(found, filament, target) is None:
            return refused
    elif name not in (None, ""):
        return refused
    store = remember(matches_path(), {filament_key(filament["id"]): name or ""}, target)
    return {"ok": True, "text": "", "match": preset_match(filament, snap, store)}


def ofd_pick_name(filament: dict, target: str, ofd: object, snap: dict) -> str | dict:
    """The remembered name ("ofd:<id>") for an OFD proposal on printer target, or the refusal: consent given, the id in
    the kept index (Look up in OFD read it), the same manufacturer and material, and a parent this printer has for
    the material. The preset is fetched once, checked and kept in the OFD folder; its values go into Spooler's preset
    over its parent (build_preset)."""
    refused = {"ok": False, "text": _i18n.tr(MATCH_REFUSED)}
    if not presets_settings()["ofd"] or not isinstance(ofd, str):
        return refused
    folder = str(ofd_folder())
    profiles = ofd_index(folder, offline=True)["profiles"]
    vendor = str((filament.get("vendor") or {}).get("name") or "")
    proposal = next((r for r in rank_ofd(profiles, vendor, str(filament.get("material") or ""), "", 0) if r["id"] == ofd), None)
    usable = {c["name"]: c for c in snap.get("parents") or []}
    if proposal is None or proposal["inherits"] not in usable or parent_score(usable[proposal["inherits"]], filament, target) is None:
        return refused
    profile = next(p for p in profiles if p["id"] == ofd)
    _preset, problem = ofd_preset(folder, profile, parents=set(usable))
    if problem:
        return {"ok": False, "text": _i18n.tr(OFD_REFUSED, why=problem)}
    return OFD_PICK + ofd


def remember_ofd(filament: dict, ofd: object) -> list[str]:
    """Add Spool: remember an OFD proposal as the parent of the new spool's filament on every printer it fits, as
    Edit Spool's Change did per printer. Returns the printers' labels it was remembered for."""
    snap = _ui_snap
    done = []
    for printer in snap.get("printers") or []:
        name = ofd_pick_name(filament, printer["target"], ofd, snap)
        if isinstance(name, str):
            remember(matches_path(), {filament_key(filament["id"]): name}, printer["target"])
            done.append(printer.get("label") or printer["target"])
    return done


def build_preset(filament: dict, name: str, key: tuple, snapshot: dict, opts: dict, spools: list[dict],
                 store: dict | None = None) -> dict | None:
    """Spooler's preset for a filament on the printer key[1] names: a standalone copy of its parent when the
    parent's settings were read, else one that inherits it; None when the printer has no usable parent.
    store: the remembered matches (a parent picked by hand wins)."""
    target, parents = key[1], snapshot.get("parents") or []
    tune = tuning_for(filament, opts)
    parent, _why, ofd = choose_parent(filament, target, parents, opts, store)
    if not parent:
        return None
    config = (snapshot.get("configs") or {}).get(parent)
    preset = with_ofd(profile_preset(filament, name, parent, target, spool_cost_per_kg(filament["id"], spools), tune, config), ofd)
    if config:
        flat = flat_preset(preset, config, key)
        if ofd:
            flat["description"] += f", with the values of {ofd['name']} from the Open Filament Database (untuned)"
        return flat
    # Its settings weren't read: still a valid preset, but sync from AMS loads its parent.
    _core._report(f"Preset {name} parent", f"settings of {parent} not read; it inherits them")
    return preset


def profile_files(spools: list[dict], snapshot: dict, opts: dict | None = None,
                  loaded: dict | None = None) -> tuple[dict, dict]:
    """({file name: preset dict}, {(filament id, printer preset[, spool id]): preset name}): one preset
    per filament and printer, or per spool when opts (Settings > Presets) says so. A filament with no
    usable parent on a printer is left out for that printer, and so is a preset that fails the check."""
    opts = presets_settings() if opts is None else opts
    files: dict = {}
    by_key: dict = {}
    filaments = {f["id"]: f for f in stocked_filaments(spools)}
    printers = {p["target"]: p for p in snapshot.get("printers") or []}
    if opts.get("per_spool"):
        loaded = loaded_targets(list(printers.values())) if loaded is None else loaded
        names = spool_profile_names(spools, list(printers.values()), loaded)
    else:
        names = profile_names(spools, list(printers.values()))
    by_spool = {s.get("id"): s for s in spools or [] if isinstance(s, dict)}
    store = load_matches(matches_path())
    for key, name in names.items():
        holder = by_spool.get(key[2]) if len(key) > 2 else {"filament": filaments[key[0]]}
        if spool_link(holder, key[1], snapshot):
            continue  # linked to your own preset that fits this printer (orca_filament_preset): Spooler makes none
        preset = build_preset(filaments[key[0]], name, key, snapshot, opts, spools, store)
        if preset is None:
            continue
        problem = preset_problem(preset)
        _core._report(f"Preset {name}", problem or None)  # logged once, not on every sync
        if problem:
            continue
        files[f"{name}.json"] = preset
        by_key[key] = name
    return files, by_key


def _orca_data_dir() -> Path | None:
    for parent in _core.PLUGIN_DIR.parents:
        if parent.name == "orca_plugins":
            return parent.parent
    return _core.DATA_DIR.parent if _core.DATA_DIR.parent.name == "OrcaSlicer" else None


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
        host = _moonraker.moon_base(preset.config_value("print_host"))
        if host and preset.is_visible:
            add(preset, host)
    add(printers.selected_preset())
    models = [e.get("model") for e in found.values()]
    for entry in found.values():
        model = entry.get("model") or entry["target"]
        clash = models.count(entry.get("model")) > 1 and entry.get("nozzle")
        entry["label"] = _safe_name(f"{model} {entry['nozzle']}" if clash else model) or "Printer"
    return list(found.values())


def user_filament_compat(filaments) -> dict:
    """{your preset name: {"now": compatible with the selected printer, "printers": its compatible printers,
    "cond": its compatibility condition}}, for link_fits(). UI thread; never raises."""
    out = {}
    try:
        for index in range(filaments.size()):
            preset = filaments.preset(index)
            is_user = getattr(preset, "is_user", None)
            if callable(is_user) and is_user() and not str(preset.name).startswith("_local/"):
                out[str(preset.name)] = {
                    "now": bool(getattr(preset, "is_compatible", True)),
                    "printers": [p for p in _plate_check.split_list(preset.config_value("compatible_printers")) if p],
                    "cond": str(preset.config_value("compatible_printers_condition") or "").strip()}
    except Exception as exc:
        _core._report("Your filament presets' printers", f"could not be read: {exc}")
        return {}
    _core._report("Your filament presets' printers", None)
    return out


def user_filament_presets(filaments) -> list[str]:
    """Your own filament presets, the ones a spool can be linked to: not system presets, nor a plugin's
    bundle (Spooler's own included). UI thread. Never raises: a failure here only empties the editor's
    list, it doesn't stop the rest of the snapshot."""
    names = set()
    try:
        for index in range(filaments.size()):
            preset = filaments.preset(index)
            is_user = getattr(preset, "is_user", None)
            if callable(is_user) and is_user() and preset.is_visible and not str(preset.name).startswith("_local/"):
                names.add(str(preset.name))
    except Exception as exc:
        _core._report("Your filament presets", f"could not be listed: {exc}")  # logged once, not on every snapshot
        return []
    _core._report("Your filament presets", None)
    return sorted(names, key=str.casefold)[:PRESET_LINK_LIST]


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
        configs = parent_configs(filaments, _parent_cache["parents"], {p["target"] for p in printers},
                                 _parent_cache["configs"])
        snap = {"names": set(filaments.preset_names()), "parents": _parent_cache["parents"],
                "configs": configs, "printers": printers, "selected": selected,
                "folder": profile_user_folder(bundle, _orca_data_dir()),
                "host": _moonraker.moon_base(bundle.full_config_value("print_host")),
                # The printer presets, for the Printer tab's "which preset is which printer" choice.
                "preset": str(getattr(bundle.printers.selected_preset(), "name", "") or ""),
                # Your own presets first: they are the ones a printer is chosen for, and the list is capped.
                "presets": [str(p.name) for p in sorted((bundle.printers.preset(i) for i in range(bundle.printers.size())),
                                                        key=lambda p: bool(p.is_system)) if p.is_visible][:128],
                "slots": len(current),
                # Each slot's preset and whether it is a system one, as OrcaSlicer's own sync picks.
                "current": [(name, bool(getattr(filaments.find_preset(name), "is_system", False)))
                            for name in current],
                "user_filaments": user_filament_presets(filaments),
                "user_compat": user_filament_compat(filaments),
                # The preset open in the filament settings: Send to Spoolman offers it first.
                "edited": str(getattr(filaments.get_edited_preset(), "name", "") or ""),
                "gen": _ui_snap.get("gen", 0) + 1, "project": _project["n"]}
    except Exception:
        _core.log.exception("Could not read the presets")
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
        _core.log.exception("Could not read %s, and could not keep it aside", path)
        return None
    _core.log.warning("Could not read %s; kept it as %s and started a new one", path.name, bad.name)
    return bad


def spawn(fn, *args, name: str = "") -> threading.Thread:
    """Run fn(*args) on a daemon thread; an exception goes to spooler.log instead of a stderr nobody sees."""
    name = name or f"spooler-{getattr(fn, '__name__', 'task')}"

    def run():
        try:
            fn(*args)
        except Exception:
            _core.log.exception("Background task %s failed", name)
    thread = threading.Thread(target=run, name=name, daemon=True)
    thread.start()
    return thread


def _write_json(path: Path, value: object, mode: int | None = None, indent: int | None = 2) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{threading.get_ident()}.tmp")
    try:
        # Created with its mode, not chmod-ed after the write: a token is never readable by others, even briefly.
        fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o666 if mode is None else mode)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(value, indent=indent, ensure_ascii=False, **({} if indent else {"separators": (",", ":")})))
        if mode is not None:
            os.chmod(tmp, mode)  # a leftover temp file from a crash keeps its old mode through O_CREAT
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
    _core.log.info("Put back the last filament presets OrcaSlicer accepted")


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
                {"id": PROFILE_BUNDLE, "name": f"{_core.PLUGIN_NAME} (Spoolman)", "version": _core.PLUGIN_VERSION})


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
            _core.log.info("OrcaSlicer did not take the bundle in %s: %s (bundles it offers: %s)",
                     folder, exc, offered_bundles())
            if "does not exist" not in str(exc):
                raise
            continue  # Not the signed-in account's folder.
        # Only after OrcaSlicer accepted the bundle, so a refused one is tried again.
        _write_json(target / PROFILE_STATE, {"hash": digest})
        _core.log.info("Synced %d filament profiles from Spoolman into %s", len(files), folder)
        return
    raise last or RuntimeError(_i18n.tr("No OrcaSlicer user folder accepted the presets"))


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import core as _core  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import printers as _printers  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
