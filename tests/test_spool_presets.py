"""Settings > Presets: one preset per spool (names, Use with, orphans), Advanced tuning merged into the
presets, the check every preset passes before a bundle is written, and Use with in the spool editor.
Everything runs against stand-ins: no OrcaSlicer, Spoolman or printer is reached."""

import copy
import json
import math
import tempfile
import threading
import types
import unittest
from pathlib import Path
from unittest import mock

import spoolman_rules as rules
from fake_bundle import SV06, U1
from test_profiles import (
    CONFIG_KEYS,
    META_KEYS,
    ORCA_KEYS,
    PARENTS,
    SPOOLS,
    filament,
    snapshot,
    sp,
    spool,
)
from test_spool_actions import Settings
from test_spool_actions import sp as asp
from test_spool_editor import SPOOL, Spoolman

SPOOL_MODE = sp.parse_presets({"per_spool": True})
OFF = sp.parse_presets(None)
TUNED = sp.parse_presets({"tuning": True, "materials": {"pla": {
    "parent": "Generic PLA", "filament_flow_ratio": 0.95, "pressure_advance": 0.035, "filament_retraction_length": 0.8,
    "filament_retraction_speed": 40, "filament_max_volumetric_speed": 18.5, "fan_min_speed": 60, "fan_max_speed": 100}}})
NUMBER_KEYS = ORCA_KEYS - {"filament_notes"}


def use_with(*names) -> dict:
    return {"use_with": json.dumps(json.dumps(list(names)))}


def check_bundle(test: unittest.TestCase, files: dict) -> None:
    """Every preset as OrcaSlicer loads it: known keys only, each a list of text, numbers one number."""
    names = {p["name"] for p in PARENTS}
    for file_name, preset in files.items():
        test.assertEqual(set(preset) - META_KEYS - CONFIG_KEYS - ORCA_KEYS, set(), file_name)
        test.assertEqual(file_name, preset["name"] + ".json")
        test.assertIn(preset["inherits"], names)
        for key in set(preset) - META_KEYS - {"compatible_printers_condition"}:
            test.assertIsInstance(preset[key], list, key)
            test.assertTrue(preset[key] and all(isinstance(v, str) for v in preset[key]), key)
            if key in NUMBER_KEYS:
                for value in preset[key]:
                    test.assertNotIn(",", value, key)
                    test.assertTrue(value == "nil" or math.isfinite(float(value.rstrip("%"))), (key, value))
        test.assertEqual(preset["compatible_printers_condition"], "")
        test.assertNotRegex(file_name, r'[\\/:*?"<>|;\x00-\x1f]')
        test.assertEqual(sp.preset_problem(preset), "", file_name)


class ParseTest(unittest.TestCase):
    def test_off_by_default(self):
        self.assertEqual(OFF, {"per_spool": False, "tuning": False, "materials": {}})

    def test_rows_are_cleaned(self):
        opts = sp.parse_presets({"per_spool": "on", "tuning": True, "materials": {
            " petg  hf ": {"filament_flow_ratio": 3, "pressure_advance": 0.04, "fan_max_speed": True, "parent": "  Generic   PETG "},
            "ABS": {"filament_flow_ratio": None}, "ASA": "not a row", "": {"pressure_advance": 0.1},
            "TPU": {"filament_retraction_length": float("nan"), "machine_start_gcode": "G28"}}})
        self.assertTrue(opts["per_spool"])
        self.assertEqual(opts["materials"], {"PETG HF": {"parent": "Generic PETG", "pressure_advance": 0.04}})

    def test_ranges_match_the_page(self):
        # ui/tests/unit/presets.test.ts holds the same table for the page's boxes.
        self.assertEqual({k: list(v) for k, v in sp.TUNING_KEYS.items()}, {
            "filament_flow_ratio": [0.01, 2.0], "pressure_advance": [0.0, 2.0], "filament_retraction_length": [0.0, 50.0],
            "filament_retraction_speed": [1.0, 500.0], "filament_max_volumetric_speed": [0.1, 200.0],
            "fan_min_speed": [0.0, 100.0], "fan_max_speed": [0.0, 100.0]})
        self.assertLessEqual(set(sp.TUNING_KEYS), ORCA_KEYS)

    def test_saved_on_its_own(self):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(sp, "SETTINGS_FILE", Path(tmp) / "s.json"), mock.patch.object(sp, "OLD_SETTINGS", Path(tmp) / "x"):
            sp.save_settings({"spoolman_url": "http://spoolman:7912"})
            sp.save_presets({"per_spool": True, "materials": {"pla": {"pressure_advance": 0.03}}})
            sp.save_presets("not a dict")
            self.assertEqual(sp.presets_settings(), {"per_spool": True, "tuning": False,
                                                     "materials": {"PLA": {"pressure_advance": 0.03}}})
            self.assertEqual(sp.get_settings()["spoolman_url"], "http://spoolman:7912")


    def test_concurrent_updates_keep_each_other(self):

        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(sp, "SETTINGS_FILE", Path(tmp) / "s.json"), mock.patch.object(sp, "OLD_SETTINGS", Path(tmp) / "x"):
            sp.save_settings({})
            threads = [threading.Thread(target=sp.update_settings, args=({f"k{i}": i},)) for i in range(20)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            self.assertEqual({k: v for k, v in sp.get_settings().items() if k.startswith("k")}, {f"k{i}": i for i in range(20)})


    def test_settings_save_racing_a_calibration_ask_keeps_both(self):
        """A Settings Save (the window's _save_settings) and a calibration prompt written from a worker
        at the same time: the save writes only the keys its form owns, so the prompt survives."""
        real_get = sp.get_settings

        def slow_get():  # widens the read-to-write window, as a busy disk would
            value = real_get()
            sp.time.sleep(0.002)
            return value

        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(sp, "SETTINGS_FILE", Path(tmp) / "s.json"), mock.patch.object(sp, "OLD_SETTINGS", Path(tmp) / "x"), \
                mock.patch.object(sp, "get_settings", slow_get):
            sp.save_settings({"spoolman_url": "http://spoolman:7912"})
            window = types.SimpleNamespace()  # no plugin-manager config: sync_config does nothing
            names = [f"Preset {i}" for i in range(15)]

            def saves():
                for grams in range(15):
                    sp.SpoolerWindow._save_settings(window, "http://spoolman:7912", 100 + grams)

            def asks():
                for name in names:
                    with sp._calib_lock:
                        sp._save_asks({**sp._asks(), name: {"filament_flow_ratio": ("0.95", "0.98")}})

            threads = [threading.Thread(target=saves), threading.Thread(target=asks)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join()
            self.assertEqual(list(sp._asks()), names)
            self.assertEqual(real_get()["low_stock_grams"], 114)


class OffIsTodayTest(unittest.TestCase):
    def test_off_makes_exactly_the_presets_of_before(self):
        before = sp.profile_files(SPOOLS, snapshot(), OFF)
        # Tuning rows saved while tuning is off change nothing.
        rows_off = sp.parse_presets({"tuning": False, "materials": TUNED["materials"]})
        self.assertEqual(sp.profile_files(SPOOLS, snapshot(), rows_off), before)
        with mock.patch.object(sp, "presets_settings", return_value=OFF):
            self.assertEqual(sp.profile_files(SPOOLS, snapshot()), before)
        self.assertEqual(sp.profile_digest(before[0]), sp.profile_digest(sp.profile_files(SPOOLS, snapshot(), OFF)[0]))
        self.assertTrue(all(len(key) == 2 for key in before[1]))


class SpoolNameTest(unittest.TestCase):
    def files(self, spools, printers=(U1, SV06), loaded=None):
        return sp.profile_files(spools, snapshot(printers), SPOOL_MODE, loaded or {})

    def test_one_preset_per_spool_named_with_its_number(self):
        f = filament(1, "Black", "PETG")
        files, by_key = self.files([spool(3, f), spool(12, f)])
        self.assertEqual(sorted(by_key.values()), ["SUNLU PETG Black #12 @Snapmaker U1", "SUNLU PETG Black #12 @Sovol SV06",
                                                   "SUNLU PETG Black #3 @Snapmaker U1", "SUNLU PETG Black #3 @Sovol SV06"])
        self.assertEqual(by_key[(1, U1, 12)], "SUNLU PETG Black #12 @Snapmaker U1")
        self.assertEqual(files["SUNLU PETG Black #3 @Sovol SV06.json"]["compatible_printers"], [SV06])

    def test_names_are_unique_and_the_same_on_every_sync(self):
        first = self.files(SPOOLS)
        self.assertEqual(self.files(list(reversed(SPOOLS))), first)
        names = [n.casefold() for n in first[1].values()]
        self.assertEqual(len(names), len(set(names)))
        active = [s for s in SPOOLS if not s.get("archived")]
        self.assertEqual(len(first[0]), len(active) * 2)
        check_bundle(self, first[0])

    def test_archived_spools_have_no_preset(self):
        f = filament(1, "Black", "PETG")
        _, by_key = self.files([spool(3, f, archived=True), spool(4, f)], (U1,))
        self.assertEqual(list(by_key.values()), ["SUNLU PETG Black #4 @Snapmaker U1"])

    def test_long_names_fit_windows_paths(self):
        f = filament(1, "x" * 200, "PLA", vendor="v" * 200)
        _, by_key = sp.profile_files([spool(123456, f)], {**snapshot((U1,)), "printers": [{"target": U1, "label": "y" * 200, "hosts": []}]},
                                     SPOOL_MODE, {})
        root = "C:\\Users\\someone.long\\AppData\\Roaming\\OrcaSlicer\\user\\" + "a" * 36
        self.assertLess(len(root + "\\_local\\spooler\\filament\\" + by_key[(1, U1, 123456)] + ".json"), 260)


class UseWithTest(unittest.TestCase):
    PRINTERS = [{"target": U1, "label": "Snapmaker U1", "hosts": ["http://10.25.1.83"]},
                {"target": SV06, "label": "Sovol SV06", "hosts": ["http://10.25.1.234:7125"]}]

    def targets(self, s, loaded=None):
        return sp.spool_targets(s, self.PRINTERS, loaded or {})

    def test_a_shelf_spool_goes_to_every_printer(self):
        self.assertEqual(self.targets(spool(5, filament(1, "x", "PLA"))), [U1, SV06])

    def test_a_loaded_spool_goes_to_its_printer_only(self):
        self.assertEqual(self.targets(spool(5, filament(1, "x", "PLA")), {"5": {SV06}}), [SV06])

    def test_the_field_wins_by_preset_or_label(self):
        s = {**spool(5, filament(1, "x", "PLA")), "extra": use_with(U1)}
        self.assertEqual(self.targets(s, {"5": {SV06}}), [U1])
        typed = {**s, "extra": {"use_with": json.dumps("sovol sv06; Snapmaker U1")}}  # typed in Spoolman's form
        self.assertEqual(self.targets(typed), [U1, SV06])

    def test_an_empty_or_unknown_field_is_the_default(self):
        for extra in ({"use_with": json.dumps("")}, use_with(), use_with("Gone printer"), {"use_with": "{broken"}, {"use_with": "5"}):
            self.assertEqual(self.targets({**spool(5, filament(1, "x", "PLA")), "extra": extra}, {"5": {SV06}}), [SV06], extra)

    def test_loaded_from_printer_tab_slots_and_live_link(self):
        cfg = [{"id": "p1", "ip": "10.25.1.234", "units": [{"kind": "ams", "slots": ["5", None, "6", None]}]},
               {"id": "auto-u1", "ip": "http://10.25.1.83", "units": []},
               {"id": "p3", "ip": "10.9.9.9", "units": [{"kind": "ams", "slots": ["9", None, None, None]}]}]
        live = {"printers": [{"id": "auto-u1", "units": [{"trays": [{"spool": 7}, {"spool": None}]}], "ext": {"spool": 8}},
                             {"id": "p1", "units": [], "ext": None}]}
        with mock.patch.object(sp, "printers_cfg", return_value=cfg), mock.patch.object(sp, "live_snapshot", return_value=live):
            loaded = sp.loaded_targets(self.PRINTERS)
            self.assertEqual(loaded, {"5": {SV06}, "6": {SV06}, "7": {U1}, "8": {U1}})  # p3 matches no preset
            only = sp.loaded_targets(self.PRINTERS[:1])
        self.assertEqual(only["9"], {U1}, "with one printer preset, every printer is that one")
        with mock.patch.object(sp, "printers_cfg", return_value=cfg), mock.patch.object(sp, "live_snapshot", return_value=live), \
                mock.patch.object(sp, "slice_map", return_value={U1: "p3", "My U1 copy": "p1"}):
            picked = sp.loaded_targets(self.PRINTERS)
        self.assertEqual(picked["9"], {U1}, "a printer preset chosen on the Printer tab wins over the address")
        self.assertEqual(picked["5"], {SV06}, "a chosen preset that isn't a target leaves the address match")

    def test_moving_a_spool_moves_its_preset_and_leaves_no_orphan(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = root / "user" / "4242" / "_local" / "spooler" / "filament"
            s = spool(5, filament(1, "Black", "PETG"))
            with mock.patch.object(sp, "_orca_data_dir", return_value=root), \
                    mock.patch.object(sp, "presets_settings", return_value=SPOOL_MODE), \
                    mock.patch.object(sp, "bridge_dir", return_value=root / "bridge"):
                sp._profiles.update(failed=("", 0.0))
                with mock.patch.object(sp, "loaded_targets", return_value={}):
                    sp.profile_sync([s], snapshot())
                self.assertEqual(len(list(folder.glob("*.json"))), 2)
                with mock.patch.object(sp, "loaded_targets", return_value={"5": {U1}}):
                    state = sp.profile_sync([s], snapshot())
                self.assertEqual(state["error"], "")
                self.assertEqual([p.name for p in folder.glob("*.json")], ["SUNLU PETG Black #5 @Snapmaker U1.json"])
                self.assertEqual(sp.profile_for_spool(s, U1), "_local/spooler/SUNLU PETG Black #5 @Snapmaker U1")
                renamed = spool(5, filament(1, "Onyx", "PETG"))
                with mock.patch.object(sp, "loaded_targets", return_value={"5": {U1}}):
                    sp.profile_sync([renamed], snapshot())
                self.assertEqual([p.name for p in folder.glob("*.json")], ["SUNLU PETG Onyx #5 @Snapmaker U1.json"])
                with mock.patch.object(sp, "presets_settings", return_value=OFF):
                    sp.profile_sync([renamed], snapshot())
                self.assertEqual(sorted(p.name for p in folder.glob("*.json")),
                                 ["SUNLU PETG Onyx @Snapmaker U1.json", "SUNLU PETG Onyx @Sovol SV06.json"])
            sp._profiles.update(names={})


class NamesUseTest(unittest.TestCase):
    def setUp(self):
        f = filament(1, "Black", "PETG")
        self.spools = [spool(3, f), {**spool(12, f), "extra": use_with(SV06)}]
        _, self.by_key = sp.profile_files(self.spools, snapshot(), SPOOL_MODE, {"3": {U1}})
        sp._profiles["names"] = self.by_key

    def tearDown(self):
        sp._profiles["names"] = {}

    def test_each_spool_finds_its_own_preset(self):
        self.assertEqual(sp.profile_for_spool(self.spools[0], U1), "_local/spooler/SUNLU PETG Black #3 @Snapmaker U1")
        self.assertEqual(sp.profile_for_spool(self.spools[1], SV06), "_local/spooler/SUNLU PETG Black #12 @Sovol SV06")
        # Use with leaves that printer out: no preset there, not another spool's.
        self.assertEqual(sp.profile_for_spool(self.spools[1], U1), "")
        self.assertEqual(sp.profile_for_spool(spool(99, filament(2, "x", "PLA")), U1), "")

    def test_profiles_json_and_slot_checks_still_work_by_filament(self):
        printers = snapshot()["printers"]
        self.assertEqual(sp.profile_map(self.by_key, printers), {"1": {
            "Snapmaker U1": "_local/spooler/SUNLU PETG Black #3 @Snapmaker U1",
            "Sovol SV06": "_local/spooler/SUNLU PETG Black #12 @Sovol SV06"}})
        self.assertTrue(sp.same_filament("_local/spooler/SUNLU PETG Black #12 @Sovol SV06", 1))
        self.assertFalse(sp.same_filament("_local/spooler/SUNLU PETG Black #12 @Sovol SV06", 2))


class TuningTest(unittest.TestCase):
    def test_overrides_reach_the_preset(self):
        files, by_key = sp.profile_files([spool(1, filament(1, "Preto", "PLA", vendor="3D Procer"))], snapshot(), TUNED)
        u1 = files[by_key[(1, U1)] + ".json"]
        self.assertEqual(u1["inherits"], "Generic PLA @U1 0.4 nozzle")
        self.assertEqual(files[by_key[(1, SV06)] + ".json"]["inherits"], "Generic PLA @System")
        self.assertEqual({k: u1[k] for k in sp.TUNING_KEYS}, {
            "filament_flow_ratio": ["0.95"], "pressure_advance": ["0.035"], "filament_retraction_length": ["0.8"],
            "filament_retraction_speed": ["40"], "filament_max_volumetric_speed": ["18.5"], "fan_min_speed": ["60"],
            "fan_max_speed": ["100"]})
        self.assertEqual(u1["enable_pressure_advance"], ["1"])
        check_bundle(self, files)

    def test_variants_use_their_material_row(self):
        opts = sp.parse_presets({"tuning": True, "materials": {"PLA": {"pressure_advance": 0.03}, "PLA SILK": {"pressure_advance": 0.05}}})
        self.assertEqual(sp.tuning_for(filament(1, "x", "PLA Silk"), opts), {"pressure_advance": 0.05})
        self.assertEqual(sp.tuning_for(filament(1, "x", "PLA+"), opts), {"pressure_advance": 0.03})
        self.assertEqual(sp.tuning_for(filament(1, "x", "SilkPLA"), opts), {"pressure_advance": 0.03})  # an OrcaSlicer alias
        self.assertEqual(sp.tuning_for(filament(1, "x", "PETG"), opts), {})

    def test_spoolman_values_win_over_tuning(self):
        field = {"*": {"filament_retraction_length": "1.2"}}
        f = filament(1, "Preto", "PLA", vendor="3D Procer", extra={"orca_flow_ratio": "0.91", "orca_settings": json.dumps(json.dumps(field))})
        files, by_key = sp.profile_files([spool(1, f)], snapshot((U1,)), TUNED)
        preset = files[by_key[(1, U1)] + ".json"]
        self.assertEqual(preset["filament_flow_ratio"], ["0.91"])
        self.assertEqual(preset["filament_retraction_length"], ["1.2"])
        self.assertEqual(preset["pressure_advance"], ["0.035"])

    def test_a_base_the_printer_lacks_falls_back_to_the_closest(self):
        opts = sp.parse_presets({"tuning": True, "materials": {"PLA": {"parent": "No Such Preset"}}})
        files, by_key = sp.profile_files([spool(1, filament(1, "Preto", "PLA", vendor="3D Procer"))], snapshot((U1,)), opts)
        self.assertEqual(files[by_key[(1, U1)] + ".json"]["inherits"], "Generic PLA @U1 0.4 nozzle")
        self.assertEqual(sp.tuned_parent("generic  pla", SV06, PARENTS), "Generic PLA @System")

    def test_bases_offered_by_name(self):
        bases = sp.parent_bases(PARENTS)
        self.assertIn({"name": "Generic PLA", "type": "PLA"}, bases)
        self.assertEqual(len({b["name"] for b in bases}), len(bases))


class BundleCheckTest(unittest.TestCase):
    def test_every_mode_writes_only_presets_orcaslicer_takes(self):
        loaded = {str(s["id"]): {U1} for s in SPOOLS[::3]}
        for opts in (OFF, SPOOL_MODE, TUNED, {**TUNED, "per_spool": True}):
            files, _ = sp.profile_files(SPOOLS, snapshot(), opts, loaded)
            self.assertGreater(len(files), 0)
            check_bundle(self, files)

    def test_problems_are_found(self):
        good = sp.profile_preset(filament(1, "x", "PLA"), "x", "Generic PLA @System", U1)
        self.assertEqual(sp.preset_problem(good), "")
        for bad in ({"machine_start_gcode": ["G28"]}, {"filament_flow_ratio": "0.9"}, {"filament_flow_ratio": [0.9]},
                    {"filament_flow_ratio": ["0,9"]}, {"pressure_advance": ["nan"]}, {"fan_max_speed": ["inf"]},
                    {"filament_flow_ratio": []}, {"inherits": ["x"]}, {"compatible_printers_condition": []}):
            self.assertNotEqual(sp.preset_problem({**good, **bad}), "", bad)
        self.assertEqual(sp.preset_problem({**good, "filament_notes": ["65C,4h"], "filament_retraction_length": ["nil"],
                                            "filament_shrink": ["99.5%"]}), "")

    def test_a_preset_that_fails_the_check_is_left_out(self):
        bad = filament(1, "Bad", "PLA", extra={"orca_settings": json.dumps(json.dumps({"*": {"pressure_advance": "nan"}}))})
        good = filament(2, "Good", "PLA")
        with self.assertLogs(sp.log, "WARNING"):
            files, by_key = sp.profile_files([spool(1, bad), spool(2, good)], snapshot((U1,)), OFF)
        self.assertEqual(list(by_key), [(2, U1)])
        check_bundle(self, files)


class EditorUseWithTest(Settings):
    """Runs on the plugin instance Settings points at a temporary settings file (each test module loads its own)."""

    def setUp(self):
        super().setUp()
        self.ensured = []
        patches = [mock.patch.object(asp, "ensure_fields", lambda: self.ensured.append(1)),
                   mock.patch.dict(asp._ui_snap, {"printers": [{"target": U1, "label": "Snapmaker U1", "hosts": []},
                                                              {"target": SV06, "label": "Sovol SV06", "hosts": []}]})]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def save(self, use, was=None, spool=None, version="0.26.0"):
        server = Spoolman(spool, version=version)
        with mock.patch.object(asp, "spoolman_call", server):
            result = asp.spool_action({"action": "save", "id": 7, "spool": {"use_with": use},
                                      "was": {"spool": {"use_with": was}}})
        return result, server

    def test_editor_offers_the_printers_and_the_value(self):
        stored = copy.deepcopy(SPOOL)
        stored["extra"]["use_with"] = use_with(SV06)["use_with"]
        asp.save_presets({"per_spool": True})
        with mock.patch.object(asp, "spoolman_call", Spoolman(stored)):
            result = asp.spool_action({"action": "editor", "id": 7})
        self.assertEqual(result["editor"]["use_with"], {"on": True, "value": [SV06], "printers": [
            {"target": U1, "label": "Snapmaker U1"}, {"target": SV06, "label": "Sovol SV06"}]})

    def test_saves_only_its_field_from_0_22(self):
        for version in ("0.26.0", "0.22.0"):
            result, server = self.save([SV06], version=version)
            self.assertTrue(result["ok"], result)
            self.assertEqual(server.writes, [("PATCH", "spool/7", {"extra": use_with(SV06)})])
            self.assertEqual(server.spool["extra"]["dryer"], '"Box 1"')
        self.assertTrue(self.ensured)

    def test_back_to_automatic_writes_empty_text_even_where_null_is_refused(self):
        stored = copy.deepcopy(SPOOL)
        stored["extra"]["use_with"] = use_with(U1)["use_with"]
        result, server = self.save(None, was=stored["extra"]["use_with"], spool=stored, version="0.22.0")
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes, [("PATCH", "spool/7", {"extra": {"use_with": json.dumps("")}})])
        self.assertIsNone(asp.use_with(server.spool, [{"target": U1, "label": "Snapmaker U1"}]))

    def test_older_spoolman_gets_the_whole_map_back(self):
        result, server = self.save([U1], version="0.21.0")
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes[0][2]["extra"], {**SPOOL["extra"], **use_with(U1)})
        self.assertEqual(rules.merge_extra(SPOOL["extra"], server.writes[0][2]["extra"], "0.21.0")["dryer"], '"Box 1"')

    def test_a_change_made_in_spoolman_meanwhile_is_kept(self):
        stored = copy.deepcopy(SPOOL)
        stored["extra"]["use_with"] = use_with(SV06)["use_with"]
        result, server = self.save([U1], was=None, spool=stored)
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes, [])
        self.assertIn("use_with", result["text"])

    def test_bad_values_write_nothing(self):
        for bad in ("Snapmaker U1", [1], [""], ["x"] * 17):
            result, server = self.save(bad)
            self.assertFalse(result["ok"], bad)
            self.assertEqual(server.writes, [])

    def test_the_generic_extra_path_cannot_write_it(self):
        server = Spoolman()
        with mock.patch.object(asp, "spoolman_call", server):
            result = asp.spool_action({"action": "save", "id": 7, "spool": {"extra": {"use_with": "x"}}, "was": {"spool": {}}})
        self.assertFalse(result["ok"])
        self.assertEqual(server.writes, [])


if __name__ == "__main__":
    unittest.main()
