"""Filament matching shared by the Orca plugins (Spooler, U1 Control, Kobra Control).

Standard library only, and no `orca` import, so it runs and tests anywhere. It ships in
@orca-plugins/ui-foundation as python/filmatch.py; each plugin's build copies it into its own package
and commits the copy. Edit it here, release a tag, then bump the plugins.

What it holds: colour parsing and distance, material names (Spoolman spellings, OrcaFilamentLibrary
families and their generic filament_id), Spooler's choice of a parent system preset and U1 Control's
choice of a filament preset for a toolhead.
"""

import re

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


def parent_score(candidate, filament, target):
    """How well a system preset fits a filament on one printer; None when it can't be used.
    candidate: {"name", "vendor", "type", "printers"}; filament: Spoolman's ({"name", "material", "vendor": {"name"}});
    target: the printer preset's name."""
    specific = target in candidate["printers"]
    if candidate["printers"] and not specific:
        return None
    material = str(filament.get("material") or "")
    score = type_score(candidate["type"], material)
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
    extra = _name_words(base) - _name_words(candidate["vendor"]) - _name_words(candidate["type"]) - {"generic"}
    named = _name_words(filament.get("name")) | _name_words(material)
    score += sum(2 if w in named else -3 for w in extra)
    return score + (3 if specific else 0)


def best_parent(filament, target, parents):
    """The best-fitting system preset for a filament on one printer, or ''. Ties go to the shorter name."""
    best = None
    for candidate in parents:
        score = parent_score(candidate, filament, target)
        if score is not None and (best is None or (score, -len(candidate["name"])) > best[0]):
            best = ((score, -len(candidate["name"])), candidate["name"])
    return best[1] if best else ""


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
    ftype = (tag.get("type") or head.get("type") or "").upper()
    family = material_base(ftype)
    vendor = (tag.get("vendor") or tag.get("manufacturer") or head.get("vendor") or "").lower()
    sub = _words(tag.get("sub_type") or head.get("sub_type")) - {"basic"}
    on_printer = re.compile(r"@\s*(snapmaker\s*)?%s\b" % re.escape(printer_hint), re.I)

    def score(name):
        n, up = name.lower(), name.upper()
        if not family or not re.search(r"\b%s" % re.escape(family), up):
            return None
        s = 20 if re.search(r"(?<![A-Z0-9])%s(?![A-Z0-9+])" % re.escape(ftype), up.replace(" ", "-")) else 5
        if vendor and vendor in n:
            s += 30
        elif "generic" in n:
            s += 5
        if on_printer.search(name):
            s += 10
        elif "@" in name:
            s -= 10
        if "0.4" in name:
            s += 1
        extra = (_words(name) & SUB_TYPE_WORDS) - {"basic"}
        s += 8 * len(sub & extra) - 6 * len(extra - sub)
        return s

    want = tag.get("colour") or head.get("colour")

    def far(name):
        return colour_distance(want, colours.get(name)) if colours and want else 0

    ranked = sorted(((-r, far(n), len(n), n) for r, n in ((score(n), n) for n in names) if r is not None))
    return ranked[0][3] if ranked else ""
