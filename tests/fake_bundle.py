"""A stand-in for orca.host.preset_bundle() that answers like the real bindings: config_value()
returns OrcaSlicer's serialized text (lists as "a";"b"), or None for a key the preset lacks."""

import json
from pathlib import Path

FIXTURES = Path(__file__).resolve().parent / "fixtures"
U1 = "Snapmaker U1 (0.4 nozzle)"
SV06 = "Sovol SV06 0.4 nozzle"


def _serialize(value):
    if isinstance(value, list):
        return ";".join(f'"{v}"' for v in value)
    return value


class Preset:
    def __init__(self, name, config, system=False, file="", visible=True):
        self.name = name
        self.alias = name
        self.file = file
        self.is_system = system
        self.is_default = False
        self.is_visible = visible
        self._config = config

    def config_value(self, key):
        return _serialize(self._config[key]) if key in self._config else None

    def config_keys(self):
        return list(self._config)

    def label(self, no_alias=False):
        return self.name


class Collection:
    def __init__(self, presets, selected=0):
        self._presets = presets
        self._selected = selected

    def size(self):
        return len(self._presets)

    def preset(self, index):
        return self._presets[index]

    def preset_names(self):
        return [p.name for p in self._presets]

    def find_preset(self, name):
        return next((p for p in self._presets if p.name == name), None)

    def selected_preset(self):
        return self._presets[self._selected]


class Bundle:
    def __init__(self, data_dir, account="4242", selected=0, filament_slots=4):
        rows = json.loads((FIXTURES / "orca_parents.json").read_text(encoding="utf-8"))
        filaments = [Preset(r["name"], {"filament_vendor": [r["vendor"]], "filament_type": [r["type"]],
                                        "compatible_printers": r["printers"],
                                        "compatible_printers_condition": r["condition"]}, system=True)
                     for r in rows]
        filaments.append(Preset("My TPU", {"filament_vendor": ["Acme"], "filament_type": ["TPU"]},
                                file=str(Path(data_dir) / "user" / account / "filament" / "My TPU.json")))
        self.filaments = Collection(filaments)
        self.prints = Collection([Preset("0.20mm Standard @Snapmaker U1", {}, system=True)])
        user = Path(data_dir) / "user" / account / "machine"
        self.printers = Collection([
            Preset(U1, {"printer_model": "Snapmaker U1", "nozzle_diameter": "0.4,0.4,0.4,0.4"}, system=True),
            Preset(SV06, {"printer_model": "Sovol SV06", "nozzle_diameter": "0.4"}, system=True),
            Preset("Snapmaker U1 (0.4 nozzle) Balanced", {"inherits": U1, "print_host": "http://10.25.1.83"},
                   file=str(user / "a.json")),
            Preset("Snapmaker U1 (0.4 nozzle) - Copy", {"inherits": U1, "print_host": "10.25.1.83"},
                   file=str(user / "b.json")),
            Preset("Sovol SV06 0.4 nozzle - Klipper", {"inherits": SV06, "print_host": "http://10.25.1.234"},
                   file=str(user / "c.json")),
            Preset("Bambu Lab X1 Carbon 0.4 nozzle", {"printer_model": "Bambu Lab X1 Carbon"}, system=True),
        ], selected)
        self._slots = filament_slots
        self._host = self.printers.selected_preset().config_value("print_host")

    def full_config_value(self, key):
        return self._host if key == "print_host" else None

    def current_filament_preset_names(self):
        return ["Generic PLA @System"] * self._slots
