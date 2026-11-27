"""Installing an Open Filament Database preset through Spooler's own presets: picked in Add Spool, it is fetched once,
checked and kept; Spooler's preset of the filament then copies the OFD preset's parent with OFD's values over it and
Spoolman's over those, flattened with Spooler's own filament_id. The network is never reached here."""

import json
import shutil
import tempfile
from pathlib import Path
from unittest import mock

from fake_bundle import FIXTURES, SV06, U1
from test_profiles import filament, snapshot, sp, spool
from test_spool_actions import Settings

OFD_ID = "ee9fe2c2-7660-54ef-acc4-bfcee250584b"   # Polymaker Dual Panchroma Matte PLA (OFD), in fixtures/ofd_index.json


class OfdInstallTest(Settings):
    def setUp(self):
        super().setUp()
        self.dir = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir, True)
        for name, target in (("matches_path", self.dir / "matches.json"), ("ofd_folder", self.dir / "ofd")):
            patch = mock.patch.object(sp, name, lambda target=target: target)
            patch.start()
            self.addCleanup(patch.stop)
        index = json.loads((FIXTURES / "ofd_index.json").read_text(encoding="utf-8"))
        self.profile = next(p for p in index["profiles"] if p["id"] == OFD_ID)
        self.preset = {"name": self.profile["profile_name"], "inherits": self.profile["inherits"], "from": "User", "version": "2.0.2.0",
                       "is_custom_defined": "0", "filament_settings_id": [self.profile["profile_name"]], "filament_type": ["PLA"],
                       "filament_vendor": ["Polymaker"], "nozzle_temperature": ["215"], "nozzle_temperature_initial_layer": ["220"],
                       "filament_density": ["1.31"], "fan_max_speed": ["90"], "filament_notes": ["Generated from the Open Filament Database."]}
        self.calls = []
        fetch = mock.patch.object(sp.filmatch, "_ofd_get", self.get)
        fetch.start()
        self.addCleanup(fetch.stop)
        for name in ("SETTINGS_FILE", "OLD_SETTINGS"):   # this file's plugin copy (test_profiles'), not only Settings'
            patch = mock.patch.object(sp, name, self.dir / (name + ".json"))
            patch.start()
            self.addCleanup(patch.stop)
        sp.set_ofd_consent(True)
        self.assertTrue(sp.ofd_suggest("Polymaker", "PLA")["ofd"])   # Look up in OFD: the index is kept from here on
        snap = snapshot()
        configs = {name: {"nozzle_temperature": "200,200", "filament_flow_ratio": "0.98,0.98", "fan_max_speed": "100,100",
                          "filament_density": "1.24,1.24", "filament_id": "OFmY0l6t", "inherits": ""}
                   for name in ("Generic PLA Matte @System", "Generic PLA @System")}
        self.snap = {**snap, "configs": configs}
        patch = mock.patch.dict(sp._ui_snap, self.snap, clear=True)
        patch.start()
        self.addCleanup(patch.stop)

    def get(self, url, headers=None):
        self.calls.append(url)
        if url.endswith(sp.filmatch.OFD_INDEX):
            return 200, (FIXTURES / "ofd_index.json").read_bytes(), {}
        return 200, json.dumps(self.preset).encode("utf-8"), {}

    def test_pick_then_build(self):
        f = filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker", settings_bed_temp=60)
        result = sp.pick_parent(f, U1, None, OFD_ID)
        self.assertTrue(result["ok"], result)
        self.assertEqual(self.calls[-1], sp.filmatch.OFD_BASE + self.profile["path"])   # fetched once, then kept
        self.assertTrue((self.dir / "ofd" / sp.filmatch.OFD_PRESETS / (OFD_ID + ".json")).exists())
        row = next(r for r in result["match"] if r["target"] == U1)
        self.assertEqual((row["name"], row["source"]), (self.profile["profile_name"], "ofd"))
        calls = len(self.calls)
        files, by_key = sp.profile_files([spool(5, f)], self.snap)
        self.assertEqual(len(self.calls), calls)   # building reads only what is kept
        u1 = next(p for p in files.values() if p["compatible_printers"] == [U1])
        sv = next(p for p in files.values() if p["compatible_printers"] == [SV06])
        self.assertEqual((u1["inherits"], u1["filament_id"][:3]), ("", "SPL"))   # standalone, Spooler's own id
        self.assertIn("Generic PLA Matte @System", u1["description"])
        self.assertIn("Open Filament Database", u1["description"])
        self.assertEqual(u1["nozzle_temperature"], ["215", "215"])   # OFD's, for each nozzle variant of the parent
        self.assertEqual(u1["fan_max_speed"], ["90", "90"])
        self.assertEqual(u1["filament_flow_ratio"], "0.98,0.98")   # the parent's: OFD has none
        self.assertEqual(u1["filament_density"], ["1.31", "1.31"])
        self.assertEqual(sp.preset_problem(u1), "")
        self.assertNotIn("fan_max_speed", sv if isinstance(sv.get("fan_max_speed"), list) else {})   # the other printer keeps its pick
        # Spoolman's own values still win over OFD's
        f2 = filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker", settings_extruder_temp=205)
        u1 = next(p for p in sp.profile_files([spool(5, f2)], self.snap)[0].values() if p["compatible_printers"] == [U1])
        self.assertEqual(u1["nozzle_temperature"], ["205", "205"])
        # Automatic forgets it
        self.assertTrue(sp.pick_parent(f, U1, None)["ok"])
        u1 = next(p for p in sp.profile_files([spool(5, f)], self.snap)[0].values() if p["compatible_printers"] == [U1])
        self.assertNotIn("Open Filament Database", u1.get("description", ""))

    def test_refusals(self):
        f = filament(1, "Red", "PLA", vendor="Polymaker")
        self.assertFalse(sp.pick_parent(f, U1, None, "not-an-id")["ok"])
        self.assertFalse(sp.pick_parent(filament(1, "Red", "PETG", vendor="Polymaker"), U1, None, OFD_ID)["ok"])   # another material
        self.preset["post_process"] = ["evil"]
        result = sp.pick_parent(f, U1, None, OFD_ID)
        self.assertFalse(result["ok"])
        self.assertIn("post_process", result["text"])
        self.assertFalse((self.dir / "matches.json").exists())
        sp.set_ofd_consent(False)   # consent revoked: nothing picked
        self.assertFalse(sp.pick_parent(f, U1, None, OFD_ID)["ok"])

    def test_a_kept_preset_that_is_gone_falls_back(self):
        f = filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker")
        self.assertTrue(sp.pick_parent(f, U1, None, OFD_ID)["ok"])
        (self.dir / "ofd" / sp.filmatch.OFD_PRESETS / (OFD_ID + ".json")).unlink()
        u1 = next(p for p in sp.profile_files([spool(5, f)], self.snap)[0].values() if p["compatible_printers"] == [U1])
        self.assertNotIn("Open Filament Database", u1.get("description", ""))   # the usual pick, never a fetch while building

    def test_add_spool_remembers_the_pick_for_every_printer_it_fits(self):
        f = filament(9, "Panchroma Matte Red", "PLA", vendor="Polymaker")
        calls = []

        def spoolman(method, path, body=None):
            calls.append((method, path))
            return {"id": 44} if path == "spool" else f if path == "filament/9" else []
        with mock.patch.object(sp, "spoolman_call", spoolman):
            result = sp.editor_create({"filament_id": 9, "spool": {"remaining_weight": 750}, "ofd": OFD_ID})
        self.assertTrue(result["ok"], result)
        self.assertIn("Open Filament Database preset on Snapmaker U1", result["text"])
        self.assertIn(("GET", "filament/9"), calls)
        u1 = next(p for p in sp.profile_files([spool(44, f)], self.snap)[0].values() if p["compatible_printers"] == [U1])
        self.assertIn("Open Filament Database", u1["description"])
        with mock.patch.object(sp, "spoolman_call", spoolman):   # an id OFD does not list: the spool is added all the same
            result = sp.editor_create({"filament_id": 9, "spool": {}, "ofd": "not-an-id"})
        self.assertTrue(result["ok"])
        self.assertIn("fits none of your printers", result["text"])
