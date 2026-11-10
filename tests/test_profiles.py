import json
import re
import tempfile
import unittest
from pathlib import Path

from fake_bundle import FIXTURES, SV06, U1, Bundle
from plugin_loader import load

sp, orca = load()

PARENTS = json.loads((FIXTURES / "orca_parents.json").read_text(encoding="utf-8"))
SPOOLS = json.loads((FIXTURES / "spoolman_spools.json").read_text(encoding="utf-8"))
# Every key a generated preset may carry: OrcaSlicer meta keys, plus options checked to exist in
# PrintConfig.cpp. Any other key makes OrcaSlicer refuse the whole bundle.
META_KEYS = {"type", "name", "from", "instantiation", "inherits", "version"}
PLATE_KEYS = {f"{p}_plate_temp{l}" for p in ("cool", "eng", "hot", "supertack", "textured_cool", "textured")
              for l in ("", "_initial_layer")}
CONFIG_KEYS = {"compatible_printers", "compatible_printers_condition", "filament_settings_id",
               "default_filament_colour", "filament_vendor", "nozzle_temperature",
               "nozzle_temperature_initial_layer", "filament_density",
               "filament_diameter", "filament_cost", *PLATE_KEYS}
# Keys the orca_settings extra field may set, all checked against OrcaSlicer 2.5.0 PrintConfig.cpp.
ORCA_KEYS = PLATE_KEYS | {
    "nozzle_temperature", "nozzle_temperature_initial_layer", "filament_flow_ratio",
    "filament_max_volumetric_speed", "pressure_advance", "enable_pressure_advance",
    "filament_retraction_length", "filament_retraction_speed", "filament_deretraction_speed",
    "filament_z_hop", "filament_ironing_flow", "filament_ironing_speed", "filament_ironing_spacing",
    "filament_ironing_inset", "fan_min_speed", "fan_max_speed", "slow_down_layer_time",
    "slow_down_min_speed", "filament_shrink", "temperature_vitrification", "filament_density",
    "filament_diameter", "filament_cost", "filament_shrinkage_compensation_z", "filament_notes"}


def spool(spool_id, filament, archived=False):
    return {"id": spool_id, "archived": archived, "remaining_weight": 500, "filament": filament}


def filament(fid, name, material, vendor="SUNLU", colour="1A2B3C", **extra):
    return {"id": fid, "name": name, "material": material, "vendor": {"name": vendor},
            "color_hex": colour, **extra}


def snapshot(printers=(U1, SV06)):
    labels = {U1: "Snapmaker U1", SV06: "Sovol SV06"}
    return {"names": {p["name"] for p in PARENTS}, "parents": PARENTS, "folder": "4242",
            "printers": [{"target": t, "label": labels[t], "hosts": []} for t in printers]}


class ParentTest(unittest.TestCase):
    def pick(self, f, target):
        return sp.best_parent(f, target, PARENTS)

    def test_vendor_line_on_its_printer(self):
        f = filament(1, "PLA SnapSpeed Yellow", "PLA", vendor="Snapmaker")
        self.assertEqual(self.pick(f, U1), "Snapmaker PLA SnapSpeed @U1")

    def test_printer_tuned_generic(self):
        self.assertEqual(self.pick(filament(1, "Preto", "PLA", vendor="3D Procer"), U1),
                         "Generic PLA @U1 0.4 nozzle")
        self.assertEqual(self.pick(filament(1, "Preto", "PETG", vendor="MasterPrint"), U1),
                         "Generic PETG @U1 0.4 nozzle")

    def test_universal_when_printer_has_none(self):
        self.assertEqual(self.pick(filament(1, "Preto", "PLA", vendor="3D Procer"), SV06), "Generic PLA @System")

    def test_variant_words(self):
        self.assertEqual(self.pick(filament(1, "Ouro silk", "PLA", vendor="3D Procer"), U1),
                         "Generic PLA Silk @U1 0.4 nozzle")

    def test_never_a_preset_for_another_printer(self):
        for f in sp.stocked_filaments(SPOOLS):
            parent = self.pick(f, SV06)
            self.assertNotIn("@U1", parent)

    def test_every_real_filament_gets_a_parent(self):
        for f in sp.stocked_filaments(SPOOLS):
            for target in (U1, SV06):
                self.assertTrue(self.pick(f, target), (f["name"], target))

    def test_unknown_material_has_no_parent(self):
        self.assertEqual(self.pick(filament(1, "x", "Unobtainium"), U1), "")


class NameTest(unittest.TestCase):
    def test_adds_vendor_and_material(self):
        self.assertEqual(sp.profile_name(filament(1, "Black", "PETG")), "SUNLU PETG Black")

    def test_keeps_name_that_has_both(self):
        self.assertEqual(sp.profile_name(filament(1, "SUNLU PLA+ Red", "PLA+")), "SUNLU PLA+ Red")

    def test_strips_path_characters_and_at(self):
        self.assertEqual(sp.profile_name(filament(1, "Red/Blue: d@l", "PLA")), "SUNLU PLA Red Blue d l")

    def test_control_characters_and_reserved_names(self):
        self.assertEqual(sp._safe_name("a\x00b\nc"), "a b c")
        self.assertEqual(sp._safe_name("CON"), "_CON")
        self.assertEqual(sp._safe_name("nul.txt"), "_nul.txt")

    def test_words_orca_blocks_in_paths_are_split(self):
        # OrcaSlicer denies plugin writes to any path containing secret, cert or conf.
        for text in ("Silk Confetti PLA", "Certified PETG", "SECRET blend", "Concert"):
            name = sp._safe_name(text)
            self.assertNotRegex(name, r"(?i)secret|cert|conf")
            self.assertEqual(name.replace("\u200b", ""), text)

    def test_long_names_fit_windows_paths(self):
        f = filament(1, "x" * 200, "PLA", vendor="v" * 200)
        names = sp.profile_names([spool(1, f)], [{"target": U1, "label": "y" * 200}])
        name = names[(1, U1)]
        root = "C:\\Users\\someone.long\\AppData\\Roaming\\OrcaSlicer\\user\\" + "a" * 36
        self.assertLess(len(root + "\\_local\\spooler\\filament\\" + name + ".json"), 260)

    def test_unicode_is_kept(self):
        self.assertEqual(sp._safe_name("Pérola"), "Pérola")


class PresetTest(unittest.TestCase):
    def test_fields(self):
        f = filament(7, "Black", "PETG", colour="#0a0b0c", settings_extruder_temp=235,
                     settings_bed_temp=80, density=1.27, diameter=1.75, price=20, weight=1000)
        p = sp.profile_preset(f, "SUNLU PETG Black @Snapmaker U1", "Generic PETG @U1 0.4 nozzle", U1)
        self.assertEqual(p["default_filament_colour"], ["#0A0B0C"])
        self.assertEqual(p["inherits"], "Generic PETG @U1 0.4 nozzle")
        self.assertEqual(p["compatible_printers"], [U1])
        self.assertEqual(p["nozzle_temperature"], ["235"])
        self.assertEqual(p["hot_plate_temp"], ["80"])
        self.assertEqual(p["filament_density"], ["1.27"])
        self.assertEqual(p["filament_cost"], ["20"])
        self.assertEqual(p["filament_vendor"], ["SUNLU"])

    def test_missing_values_are_left_to_parent(self):
        p = sp.profile_preset(filament(1, "x", "PLA", colour=None), "x", "Generic PLA @System", U1)
        self.assertNotIn("nozzle_temperature", p)
        self.assertNotIn("filament_cost", p)
        self.assertEqual(p["default_filament_colour"], ["#FFFFFF"])

    def test_bed_temperature_on_every_plate(self):
        p = sp.profile_preset(filament(1, "x", "PLA", settings_bed_temp=65), "x", "Generic PLA @System", U1)
        self.assertEqual({k: v for k, v in p.items() if k in PLATE_KEYS}, {k: ["65"] for k in PLATE_KEYS})

    def test_orca_settings_field(self):
        field = {"*": {"filament_ironing_flow": "15%", "nozzle_temperature": 230},
                 "Snapmaker U1": {"filament_max_volumetric_speed": 20, "filament_retraction_length": "1"},
                 "Sovol SV06": {"pressure_advance": 0.04},
                 "sneaky": {"machine_start_gcode": "G28"}}
        # Spoolman returns a text extra field as a JSON string of the text.
        f = filament(1, "x", "PLA", settings_extruder_temp=205, extra={"orca_settings": json.dumps(json.dumps(field))})
        u1 = sp.profile_preset(f, "x", "Generic PLA @System", "_local/cortexos-u1/Snapmaker U1 (0.4 nozzle) Balanced")
        self.assertEqual(u1["filament_ironing_flow"], ["15%"])
        self.assertEqual(u1["nozzle_temperature"], ["230"])  # the field wins over settings_extruder_temp
        self.assertEqual(u1["filament_max_volumetric_speed"], ["20"])
        self.assertEqual(u1["filament_retraction_length"], ["1"])
        self.assertNotIn("pressure_advance", u1)
        sv06 = sp.profile_preset(f, "x", "Generic PLA @System", SV06)
        self.assertEqual(sv06["pressure_advance"], ["0.04"])
        self.assertNotIn("filament_max_volumetric_speed", sv06)
        for p in (u1, sv06):
            self.assertEqual(set(p) - META_KEYS - CONFIG_KEYS - ORCA_KEYS, set())

    def test_orca_settings_number_text_must_be_one_number(self):
        field = {"*": {"filament_flow_ratio": "0,95", "pressure_advance": "0.032", "filament_notes": "65C,4h",
                       "filament_retraction_length": "nil", "filament_cost": "22.99",
                       "filament_shrinkage_compensation_z": "99.5%"}}
        f = filament(1, "x", "PLA", price=10, weight=1000, extra={"orca_settings": json.dumps(json.dumps(field))})
        p = sp.profile_preset(f, "x", "Generic PLA @System", U1)
        # "0,95" would reach OrcaSlicer as the two values 0 and 95.
        self.assertNotIn("filament_flow_ratio", p)
        self.assertEqual(p["pressure_advance"], ["0.032"])
        self.assertEqual(p["filament_notes"], ["65C,4h"])
        self.assertEqual(p["filament_retraction_length"], ["nil"])
        self.assertEqual(p["filament_cost"], ["22.99"])
        self.assertEqual(p["filament_shrinkage_compensation_z"], ["99.5%"])

    def test_orca_settings_flat_and_broken(self):
        flat = filament(1, "x", "PLA", extra={"orca_settings": json.dumps('{"filament_flow_ratio": "0.98"}')})
        self.assertEqual(sp.orca_settings(flat, U1), {"filament_flow_ratio": ["0.98"]})
        for raw in ('"not json', json.dumps("[1, 2]"), json.dumps('{"filament_flow_ratio": true}')):
            self.assertEqual(sp.orca_settings(filament(1, "x", "PLA", extra={"orca_settings": raw}), U1), {})

    def test_multi_colour_uses_first(self):
        f = filament(1, "x", "PLA", colour=None, multi_color_hexes="ff0000,00ff00")
        self.assertEqual(sp.profile_colour(f), "FF0000")

    def test_real_presets_only_use_known_keys_and_valid_values(self):
        files, _ = sp.profile_files(SPOOLS, snapshot())
        self.assertGreater(len(files), 0)
        names = {p["name"] for p in PARENTS}
        for file_name, preset in files.items():
            self.assertEqual(set(preset) - META_KEYS - CONFIG_KEYS - ORCA_KEYS, set(), file_name)
            self.assertEqual(file_name, preset["name"] + ".json")
            self.assertIn(preset["inherits"], names)
            self.assertEqual(preset["version"], "1.0.0")
            for key in CONFIG_KEYS & set(preset):
                if key != "compatible_printers_condition":
                    self.assertIsInstance(preset[key], list, key)
                    self.assertTrue(all(isinstance(v, str) for v in preset[key]), key)
            self.assertRegex(preset["default_filament_colour"][0], r"^#[0-9A-F]{6}$")
            self.assertNotRegex(file_name, r'[\\/:*?"<>|;\x00-\x1f]')


class FilesTest(unittest.TestCase):
    def test_one_preset_per_filament_per_printer(self):
        files, by_key = sp.profile_files(SPOOLS, snapshot())
        filaments = len(sp.stocked_filaments(SPOOLS))
        self.assertEqual(len(files), filaments * 2)
        self.assertEqual(by_key[(13, U1)], "3D Procer PLA Pérola @Snapmaker U1")
        self.assertEqual(by_key[(13, SV06)], "3D Procer PLA Pérola @Sovol SV06")

    def test_archived_spools_drop_their_filament(self):
        spools = [spool(1, filament(1, "Gone", "PLA"), archived=True)]
        self.assertEqual(sp.profile_files(spools, snapshot()), ({}, {}))

    def test_case_only_names_do_not_collide(self):
        spools = [spool(1, filament(1, "black", "PETG")), spool(2, filament(2, "Black", "PETG"))]
        names = sp.profile_names(spools, snapshot((U1,))["printers"])
        self.assertEqual(sorted(names.values()),
                         ["SUNLU PETG Black #2 @Snapmaker U1", "SUNLU PETG black @Snapmaker U1"])

    def test_filament_without_parent_is_left_out(self):
        files, by_key = sp.profile_files([spool(1, filament(1, "x", "Unobtainium"))], snapshot())
        self.assertEqual((files, by_key), ({}, {}))


class SnapshotTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        sp._orca_data_dir = lambda: self.root
        sp._parent_cache.update(key=None, parents=[])

    def tearDown(self):
        self.tmp.cleanup()

    def test_snapshot_from_the_preset_bundle(self):
        orca.host.preset_bundle = lambda: Bundle(self.root, selected=2)
        snap = sp.profile_snapshot()
        self.assertEqual(snap["folder"], "4242")
        self.assertEqual(snap["host"], "http://10.25.1.83")
        self.assertEqual(snap["selected"], U1)
        self.assertEqual(snap["slots"], 4)
        printers = {p["target"]: p for p in snap["printers"]}
        self.assertEqual(set(printers), {U1, SV06})
        self.assertEqual(printers[U1]["label"], "Snapmaker U1")
        self.assertEqual(printers[U1]["hosts"], ["http://10.25.1.83"])
        self.assertEqual(printers[SV06]["hosts"], ["http://10.25.1.234"])
        parent = next(p for p in snap["parents"] if p["name"] == "Snapmaker PLA SnapSpeed @U1")
        self.assertEqual((parent["vendor"], parent["type"], parent["printers"]), ("Snapmaker", "PLA", [U1]))
        self.assertFalse(any(re.search(r"@base| base$", p["name"]) for p in snap["parents"]))
        self.assertEqual(sp._ui_snap["host"], "http://10.25.1.83")
        self.assertEqual(snap["current"], [("Generic PLA @System", True)] * 4)
        self.assertEqual(sp.profile_snapshot()["gen"], snap["gen"] + 1)

    def test_selected_printer_without_host_is_a_target(self):
        orca.host.preset_bundle = lambda: Bundle(self.root, selected=5)
        snap = sp.profile_snapshot()
        self.assertIn("Bambu Lab X1 Carbon 0.4 nozzle", [p["target"] for p in snap["printers"]])
        self.assertEqual(snap["host"], "")

    def test_auto_printers_one_per_host(self):
        orca.host.preset_bundle = lambda: Bundle(self.root, selected=2)
        sp.refresh_snapshot()
        found = {p["ip"]: p["name"] for p in sp._auto_printers}
        self.assertEqual(found, {"http://10.25.1.83": "Snapmaker U1", "http://10.25.1.234": "Sovol SV06"})
        self.assertEqual(sp.target_for_host("http://10.25.1.234"), SV06)
        sp._auto_printers.clear()


class SyncTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        sp._orca_data_dir = lambda: self.root
        sp._profiles.update(failed=("", 0.0))
        orca.reloads.clear()

    def tearDown(self):
        self.tmp.cleanup()

    def bundle_dir(self, account="4242"):
        return self.root / "user" / account / "_local" / "spooler"

    def test_writes_reloads_and_skips_when_unchanged(self):
        spools = [spool(1, filament(1, "Black", "PETG"))]
        state = sp.profile_sync(spools, snapshot())
        self.assertEqual((state["count"], state["error"]), (2, ""))
        self.assertEqual(orca.reloads, ["spooler"])
        preset = json.loads((self.bundle_dir() / "filament" / "SUNLU PETG Black @Snapmaker U1.json").read_text())
        # The vendor's own preset beats a generic one, even one tuned for the printer.
        self.assertEqual(preset["inherits"], "SUNLU PETG @System")
        meta = json.loads((self.bundle_dir() / "bundle_metadata.json").read_text())
        self.assertEqual(meta["id"], "spooler")
        sp.profile_sync(spools, snapshot())
        self.assertEqual(orca.reloads, ["spooler"])
        self.assertEqual(sp.profile_for_spool(spools[0], U1), "_local/spooler/SUNLU PETG Black @Snapmaker U1")
        self.assertEqual(sp.profile_for_spool(spools[0], "Other"), "")

    def test_removes_stale_presets(self):
        sp.profile_sync([spool(1, filament(1, "Black", "PETG"))], snapshot((U1,)))
        sp.profile_sync([spool(2, filament(2, "White", "PLA"))], snapshot((U1,)))
        names = [p.name for p in (self.bundle_dir() / "filament").glob("*.json")]
        self.assertEqual(names, ["SUNLU PLA White @Snapmaker U1.json"])

    def test_case_only_rename_keeps_new_file(self):
        target = self.root / "bundle"
        sp.write_profiles(target, {"a.json": {}})
        sp.write_profiles(target, {"A.json": {}})
        self.assertEqual(len(list((target / "filament").glob("*.json"))), 1)

    def test_refused_presets_back_off_then_retry(self):
        spools = [spool(1, filament(1, "Black", "PETG"))]
        original = orca.host.preset.bundles.reload_local

        def refuse(bundle_id):
            raise RuntimeError("Local bundle contains an invalid preset")

        orca.host.preset.bundles.reload_local = refuse
        try:
            state = sp.profile_sync(spools, snapshot())
        finally:
            orca.host.preset.bundles.reload_local = original
        self.assertIn("invalid preset", state["error"])
        sp.profile_sync(spools, snapshot())
        self.assertEqual(orca.reloads, [])
        sp._profiles["failed"] = (sp._profiles["failed"][0], -sp.PROFILE_RETRY)
        state = sp.profile_sync(spools, snapshot())
        self.assertEqual((orca.reloads, state["error"]), (["spooler"], ""))

    def test_finds_account_folder_without_user_presets(self):
        (self.root / "user" / "default").mkdir(parents=True)
        (self.root / "user" / "4242").mkdir(parents=True)
        original = orca.host.preset.bundles.reload_local

        def only_account(bundle_id):
            if not self.bundle_dir("4242").exists():
                raise RuntimeError("Local bundle directory does not exist")
            orca.reloads.append(bundle_id)

        orca.host.preset.bundles.reload_local = only_account
        try:
            state = sp.profile_sync([spool(1, filament(1, "Black", "PETG"))], dict(snapshot(), folder=""))
        finally:
            orca.host.preset.bundles.reload_local = original
        self.assertEqual(state["error"], "")
        self.assertTrue((self.bundle_dir("4242") / "filament").is_dir())
        self.assertFalse(self.bundle_dir("default").exists())


if __name__ == "__main__":
    unittest.main()
