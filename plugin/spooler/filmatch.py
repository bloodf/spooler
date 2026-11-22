"""Filament matching shared by the Orca plugins (Spooler, U1 Control, Kobra Control).

Standard library only, and no `orca` import, so it runs and tests anywhere. It ships in
@orca-plugins/ui-foundation as python/filmatch.py; each plugin's build copies it into its own package
and commits the copy. Edit it here, release a tag, then bump the plugins.

What it holds: colour parsing and distance, material names (Spoolman spellings, OrcaFilamentLibrary
families and their generic filament_id), Spooler's choice of a parent system preset and U1 Control's
choice of a filament preset for a toolhead, each also as a ranked list with the reasons for every score, and the
remembered matches (matches.json) the user confirmed.
"""

import json
import os
import re
import threading
import time

# --- Colours -------------------------------------------------------------------------------------


def norm_colour(value):
    """'#ff0000', 'FF0000FF', 'ff0000' -> '#FF0000'; anything else -> None."""
    m = re.fullmatch(r"#?([0-9a-fA-F]{6})([0-9a-fA-F]{2})?", str(value or "").strip())
    return "#" + m.group(1).upper() if m else None


def colour_distance(a, b):
    """Weighted RGB distance ('redmean'); unknown colours are far apart."""
    a, b = norm_colour(a), norm_colour(b)
    if not a or not b:
        return 765.0
    r1, g1, b1 = (int(a[i:i + 2], 16) for i in (1, 3, 5))
    r2, g2, b2 = (int(b[i:i + 2], 16) for i in (1, 3, 5))
    rm = (r1 + r2) / 2
    return ((2 + rm / 256) * (r1 - r2) ** 2 + 4 * (g1 - g2) ** 2 + (2 + (255 - rm) / 256) * (b1 - b2) ** 2) ** 0.5


def colour_diff(first, second):
    """Plain RGB distance between two hex colours (the first six digits), None when one is not a colour."""
    def rgb(value):
        digits = (value or "").strip().lstrip("#")[:6]
        if not re.fullmatch(r"[0-9a-fA-F]{6}", digits):
            return None
        return tuple(int(digits[i:i + 2], 16) for i in (0, 2, 4))

    a, b = rgb(first), rgb(second)
    return None if a is None or b is None else sum((x - y) ** 2 for x, y in zip(a, b)) ** 0.5


# --- Materials -----------------------------------------------------------------------------------

# Spoolman material spellings to the material names OrcaSlicer's presets use.
MATERIAL_ALIASES = {
    "PLA+": "PLA", "PLAPLUS": "PLA", "PLAPRO": "PLA", "HSPLA": "PLA", "PLAHS": "PLA",
    "SILKPLA": "PLA", "PLASILK": "PLA", "MATTEPLA": "PLA", "PLAMATTE": "PLA", "PETG+": "PETG",
    "HSPETG": "PETG", "PETGHS": "PETG", "PETGHF": "PETG", "ABS+": "ABS", "NYLON": "PA",
}

# Material -> OrcaFilamentLibrary family (MRA map_filament_type_to_generic_id).
FILAMENT_FAMILIES = {
    "PLA": "PLA", "PLA-CF": "PLA-CF", "PLA SILK": "PLA Silk", "PLA-SILK": "PLA Silk", "PLA MATTE": "PLA Matte",
    "PLA HIGH SPEED": "PLA High Speed", "PLA-HS": "PLA High Speed", "PLA HS": "PLA High Speed",
    "ABS": "ABS", "ASA": "ASA", "PETG": "PETG", "PET": "PETG", "PCTG": "PCTG",
    "PA": "PA", "NYLON": "PA", "PA-CF": "PA-CF", "PPA": "PPA-CF", "PPA-CF": "PPA-CF", "PPA-GF": "PPA-GF",
    "PC": "PC", "PE": "PE", "PP": "PP", "PVA": "PVA", "HIPS": "HIPS", "BVOH": "BVOH", "TPU": "TPU",
    "EVA": "EVA", "PHA": "PHA", "COPE": "CoPE", "SBS": "SBS",
}
# filament_id of each "Generic <family> @System" preset in OrcaSlicer's OrcaFilamentLibrary (resources/profiles/
# OrcaFilamentLibrary/filament, resolved through "inherits", OrcaSlicer main 32f6db87; python/generic_ids.py checks
# them). OrcaSlicer's plugin API doesn't show a preset's filament_id, so they are listed here. An id OrcaSlicer
# doesn't know still works: its sync from AMS then takes "Generic <tray_type>" (PresetBundle::sync_ams_list); only
# an empty one becomes "Generic PLA".
GENERIC_IDS = {
    "ABS": "OFY9muEs", "ASA": "OFLPAxz3", "BVOH": "OFo2UF2C", "CoPE": "OFjt9en1", "EVA": "OFCD8qiU",
    "HIPS": "OFsFon5l", "PA": "OFg8ndtj", "PA-CF": "OFQLcbps", "PC": "OFLakOUI", "PCTG": "OFu1evlr",
    "PE": "OFPklMI1", "PETG": "OFYPdQJh", "PHA": "OF74KeQR", "PLA": "OFDSrzZ8", "PLA High Speed": "OFmpMwxS",
    "PLA Matte": "OFmY0l6t", "PLA Silk": "OFesA6rF", "PLA-CF": "OFWbdGsC", "PP": "OF1UNk9P", "PPA-CF": "OF8tPByX",
    "PPA-GF": "OF8Tlg47", "PVA": "OFDvXujf", "SBS": "OFhQfUQY", "TPU": "OFgbpcy9",
}


def material_base(ftype):
    """'PLA-CF' / 'PLA Matte' / 'PLA+' -> 'PLA': the leading letters, upper case."""
    m = re.match(r"[A-Za-z]+", (ftype or "").strip())
    return m.group(0).upper() if m else ""


def material_key(material):
    """Upper case, letters, digits and '+' only: 'pla+ silk' -> 'PLA+SILK' (the MATERIAL_ALIASES keys)."""
    return re.sub(r"[^A-Z0-9+]", "", str(material or "").upper())


def generic_family(material, families=FILAMENT_FAMILIES):
    """OrcaFilamentLibrary family of a material, or None: the table, else the longest family named in it as a
    whole word."""
    text = " ".join(str(material or "").split()).upper()
    return families.get(text) or next(
        (families[k] for k in sorted(families, key=len, reverse=True)
         if re.search(r"(?<![A-Z0-9])%s(?![A-Z0-9])" % re.escape(k), text)), None)


def generic_filament_id(material, families=FILAMENT_FAMILIES):
    """filament_id of the material's "Generic <family> @System" preset, or ""."""
    return GENERIC_IDS.get(generic_family(material, families), "")


# --- Parent system preset (Spooler) --------------------------------------------------------------


def _norm(text):
    return re.sub(r"[^a-z0-9+]", "", str(text or "").lower())


def _name_words(text):
    return {w for w in re.split(r"[^a-z0-9+]+", str(text or "").lower()) if w}


def type_score(candidate, material):
    """How well a preset's filament_type fits a material: 6 same, 1 a variant, -1 another material."""
    want = {material_key(material), material_key(MATERIAL_ALIASES.get(material_key(material), material))}
    have = material_key(candidate)
    if have in want:
        return 6
    return 1 if have and any(w.startswith(have) or have.startswith(w) for w in want if w) else -1


# A reason is [code, value], for the page to word in its own language. Codes: "material" (the same material),
# "variant" (a variant of it), "vendor" (the same vendor), "generic" (a Generic preset), "other_vendor", "word" (a
# word of the preset's name the filament has too), "extra_word" (one it lacks), "printer" (made for this printer),
# "other_printer" (made for another one), "nozzle" (a 0.4 nozzle preset).
PARENT_MARGIN = 3     # points the best parent needs over the next one to count as a confident pick
PRESET_MARGIN = 10    # the same for a toolhead's filament preset


def parent_reasons(candidate, filament, target):
    """(score, reasons) of a system preset for a filament on one printer; (None, []) when it can't be used.
    candidate: {"name", "vendor", "type", "printers"}; filament: Spoolman's ({"name", "material", "vendor": {"name"}});
    target: the printer preset's name."""
    specific = target in candidate["printers"]
    if candidate["printers"] and not specific:
        return None, []
    material = str(filament.get("material") or "")
    score = type_score(candidate["type"], material)
    if score < 0:
        return None, []
    reasons = [["material" if score == 6 else "variant", candidate["type"]]]
    vendor = _norm((filament.get("vendor") or {}).get("name"))
    theirs = _norm(candidate["vendor"])
    if vendor and theirs == vendor:
        score += 5
        reasons.append(["vendor", candidate["vendor"]])
    elif theirs == "generic":
        score += 1
        reasons.append(["generic", ""])
    elif theirs:
        score -= 2
        reasons.append(["other_vendor", candidate["vendor"]])
    base = candidate["name"].split("@")[0]
    extra = _name_words(base) - _name_words(candidate["vendor"]) - _name_words(candidate["type"]) - {"generic"}
    named = _name_words(filament.get("name")) | _name_words(material)
    for word in sorted(extra):
        score += 2 if word in named else -3
        reasons.append(["word" if word in named else "extra_word", word])
    if specific:
        score += 3
        reasons.append(["printer", ""])
    return score, reasons


def parent_score(candidate, filament, target):
    """How well a system preset fits a filament on one printer; None when it can't be used (parent_reasons)."""
    return parent_reasons(candidate, filament, target)[0]


def rank_parents(filament, target, parents, limit=None):
    """The usable system presets for a filament on one printer, best first: [{"name", "score", "reasons"}].
    Ties go to the shorter name, then to the earlier one in parents."""
    ranked = []
    for candidate in parents:
        score, reasons = parent_reasons(candidate, filament, target)
        if score is not None:
            ranked.append({"name": candidate["name"], "score": score, "reasons": reasons})
    ranked.sort(key=lambda r: (-r["score"], len(r["name"])))
    return ranked[:limit] if limit else ranked


def best_parent(filament, target, parents):
    """The best-fitting system preset for a filament on one printer, or ''. Ties go to the shorter name."""
    ranked = rank_parents(filament, target, parents, 1)
    return ranked[0]["name"] if ranked else ""


def confident(ranked, margin):
    """Whether the first of a ranked list is a clear pick: alone, or `margin` points ahead of the next one."""
    return bool(ranked) and (len(ranked) < 2 or ranked[0]["score"] - ranked[1]["score"] >= margin)


# --- Filament preset for a toolhead (U1 Control) -------------------------------------------------

SUB_TYPE_WORDS = {"matte", "silk", "snapspeed", "hf", "cf", "gf", "basic", "pro", "lite", "tough", "galaxy",
                  "marble", "glow", "sparkle", "wood", "metal", "high", "speed", "rapid"}


def _words(text):
    return set(re.findall(r"[a-z0-9]+", (text or "").lower()))


def override_name(names, head, tag, overrides):
    """User-pinned preset: UID: first, then SKU:, then "Vendor|TYPE|SubType". Only if it exists."""
    pins = {str(k).strip().lower(): v for k, v in (overrides or {}).items()}
    tag = tag or {}
    vendor = tag.get("vendor") or tag.get("manufacturer") or head.get("vendor") or ""
    ftype = tag.get("type") or head.get("type") or ""
    sub = tag.get("sub_type") or head.get("sub_type") or ""
    keys = ["uid:" + str(tag.get("uid") or ""), "sku:" + str(tag.get("sku") or ""),
            "%s|%s|%s" % (vendor, ftype, sub), "%s|%s|" % (vendor, ftype)]
    for key in keys:
        name = pins.get(key.lower())
        if name in names:
            return name
    return ""


def _preset_scorer(head, tag, printer_hint):
    """score(name) -> (points, reasons), or (None, []) for a preset of another material, for one toolhead."""
    ftype = (tag.get("type") or head.get("type") or "").upper()
    family = material_base(ftype)
    vendor = (tag.get("vendor") or tag.get("manufacturer") or head.get("vendor") or "").lower()
    sub = _words(tag.get("sub_type") or head.get("sub_type")) - {"basic"}
    on_printer = re.compile(r"@\s*(snapmaker\s*)?%s\b" % re.escape(printer_hint), re.I)

    def score(name):
        n, up = name.lower(), name.upper()
        if not family or not re.search(r"\b%s" % re.escape(family), up):
            return None, []
        exact = re.search(r"(?<![A-Z0-9])%s(?![A-Z0-9+])" % re.escape(ftype), up.replace(" ", "-"))
        s, reasons = (20, [["material", ftype]]) if exact else (5, [["variant", family]])
        if vendor and vendor in n:
            s += 30
            reasons.append(["vendor", tag.get("vendor") or tag.get("manufacturer") or head.get("vendor")])
        elif "generic" in n:
            s += 5
            reasons.append(["generic", ""])
        if on_printer.search(name):
            s += 10
            reasons.append(["printer", ""])
        elif "@" in name:
            s -= 10
            reasons.append(["other_printer", ""])
        if "0.4" in name:
            s += 1
            reasons.append(["nozzle", "0.4"])
        extra = (_words(name) & SUB_TYPE_WORDS) - {"basic"}
        s += 8 * len(sub & extra) - 6 * len(extra - sub)
        reasons += [["word", w] for w in sorted(sub & extra)] + [["extra_word", w] for w in sorted(extra - sub)]
        return s, reasons
    return score


def rank_filament_presets(names, head, tag=None, printer_hint="U1", colours=None, limit=None):
    """The filament presets of a toolhead's material, best first: [{"name", "score", "reasons"}]. Equal scores go
    to the nearest colour (colours: preset name -> "#RRGGBB"), then the shorter name, then by name."""
    tag = tag or {}
    score = _preset_scorer(head, tag, printer_hint)
    want = tag.get("colour") or head.get("colour")

    def far(name):
        return colour_distance(want, colours.get(name)) if colours and want else 0

    ranked = []
    for name in names:
        points, reasons = score(name)
        if points is not None:
            ranked.append((-points, far(name), len(name), name, reasons))
    ranked.sort(key=lambda r: r[:4])
    out = [{"name": r[3], "score": -r[0], "reasons": r[4]} for r in ranked]
    return out[:limit] if limit else out


def pick_filament_preset(names, head, tag=None, overrides=None, printer_hint="U1", preference=None, colours=None):
    """Best Orca filament preset name for what a toolhead (and its RFID tag) holds, or "".
    preference(names, head, tag) -> name or None is consulted after overrides, before scoring.
    colours: preset name -> "#RRGGBB"; the nearest colour wins between equally scored presets."""
    tag = tag or {}
    pinned = override_name(names, head, tag, overrides)
    if pinned:
        return pinned
    if preference:
        chosen = preference(names, head, tag)
        if chosen in names:
            return chosen
    ranked = rank_filament_presets(names, head, tag, printer_hint, colours, 1)
    return ranked[0]["name"] if ranked else ""


# --- Remembered matches (matches.json) -----------------------------------------------------------
# The preset the user confirmed for a spool, tag or kind of filament, kept so the next match starts from it:
#   {"version": 1, "entries": {"<key>": {"default": "<preset>", "printers": {"<printer>": "<preset>"},
#                                        "updated": <unix s>}}}
# Spooler keeps it in <OrcaSlicer data folder>/spooler/matches.json, which U1 Control and Kobra Control read first;
# without Spooler each keeps its own in its data folder. Keys, most specific first (observation_keys):
#   spool:<Spoolman spool id>, tag:<RFID uid>, sku:<SKU>, mat:<vendor>|<material>|<subtype>, mat:<vendor>|<material>|
# and filament:<Spoolman filament id>, Spooler's own: the parent system preset of its presets for that filament.
# A remembered preset is used only while it still exists and still fits what is loaded (the caller checks).
MATCHES_FILE = "matches.json"
MATCHES_VERSION = 1


def observation_keys(spool_id=None, uid="", sku="", vendor="", material="", sub_type=""):
    """The keys a remembered match may be stored under for what a slot holds, most specific first."""
    keys = ["spool:%s" % spool_id] if spool_id not in (None, "") else []
    keys += ["%s:%s" % (k, str(v).strip().lower()) for k, v in (("tag", uid), ("sku", sku)) if str(v or "").strip()]
    if str(material or "").strip():
        kind = "%s|%s|" % (vendor or "", material)
        keys += ["mat:" + (kind + (sub_type or "")).lower()] + (["mat:" + kind.lower()] if sub_type else [])
    return keys


def toolhead_keys(head, tag=None, spool_id=None):
    """observation_keys of a toolhead and its RFID tag: the same vendor, material and subtype pick_filament_preset
    and override_name read."""
    tag = tag or {}
    return observation_keys(spool_id, tag.get("uid") or "", tag.get("sku") or "",
                            tag.get("vendor") or tag.get("manufacturer") or head.get("vendor") or "",
                            tag.get("type") or head.get("type") or "", tag.get("sub_type") or head.get("sub_type") or "")


def overrides_as_matches(overrides):
    """U1 Control's old profile_overrides ({"uid:..", "sku:..", "vendor|type|sub": preset}) as matches.json keys."""
    out = {}
    for key, name in (overrides or {}).items():
        key = str(key).strip().lower()
        if not isinstance(name, str) or not name.strip():
            continue
        if key.startswith("uid:") and key[4:]:
            out["tag:" + key[4:]] = name.strip()
        elif key.startswith("sku:") and key[4:]:
            out[key] = name.strip()
        elif "|" in key:
            out["mat:" + key] = name.strip()
    return out


def load_matches(path):
    """The remembered matches in path; an empty store when it is missing, unreadable or of another version."""
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError, TypeError):
        data = None
    if not isinstance(data, dict) or data.get("version") != MATCHES_VERSION or not isinstance(data.get("entries"), dict):
        return {"version": MATCHES_VERSION, "entries": {}}
    return data


def recall(stores, keys, printer=""):
    """The remembered preset names for keys, best first: per key, most specific first, each store in turn (the
    printer's choice, then the default). The caller takes the first one that still exists and fits."""
    out = []
    for key in keys:
        for store in stores:
            entry = ((store or {}).get("entries") or {}).get(key)
            if not isinstance(entry, dict):
                continue
            printers = entry.get("printers") if isinstance(entry.get("printers"), dict) else {}
            for name in (printers.get(printer) if printer else None, entry.get("default")):
                if isinstance(name, str) and name and name not in out:
                    out.append(name)
    return out


def remember(path, choices, printer="", now=None):
    """Store choices ({key: preset name}, "" forgets) for printer, or as the default when printer is "", in path
    (read again first, written in one step). Returns the store as written."""
    store = load_matches(path)
    entries = store["entries"]
    for key, name in choices.items():
        entry = dict(entries.get(key) or {}) if isinstance(entries.get(key), dict) else {}
        printers = dict(entry.get("printers") or {}) if isinstance(entry.get("printers"), dict) else {}
        if printer:
            printers[printer] = name
            printers = {k: v for k, v in printers.items() if isinstance(v, str) and v}
        else:
            entry["default"] = name
        entry = {**{k: v for k, v in entry.items() if k != "default" or v}, "printers": printers,
                 "updated": int(time.time() if now is None else now)}
        if printers or entry.get("default"):
            entries[key] = entry
        else:
            entries.pop(key, None)
    folder = os.path.dirname(path)
    if folder:
        os.makedirs(folder, exist_ok=True)
    tmp = os.path.join(folder, ".%s.%d.tmp" % (os.path.basename(path), threading.get_ident()))
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(store, f, indent=1, sort_keys=True, ensure_ascii=False)
        os.replace(tmp, path)
    except OSError:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise
    return store
