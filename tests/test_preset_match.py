"""Edit Spool > Based on: the parent picked by hand is remembered in matches.json, wins over the automatic pick
while it still fits, and the editor shows each printer's pick with its score, reasons and candidates."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from fake_bundle import SV06, U1
from test_profiles import PARENTS, filament, snapshot, sp, spool
from test_spool_actions import Settings


class PresetMatchTest(Settings):
    def setUp(self):
        super().setUp()
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name) / "spooler" / "matches.json"
        patch = mock.patch.object(sp, "matches_path", lambda: self.path)
        patch.start()
        self.addCleanup(patch.stop)
        self.addCleanup(self.dir.cleanup)
        self.snap = snapshot()
        snap = mock.patch.dict(sp._ui_snap, self.snap, clear=True)
        snap.start()
        self.addCleanup(snap.stop)

    def test_picked_parent_wins_while_it_fits(self):
        f = filament(1, "Preto", "PLA", vendor="3D Procer")
        self.assertEqual(sp.best_parent(f, U1, PARENTS), "Generic PLA @U1 0.4 nozzle")
        result = sp.pick_parent(f, U1, "Generic PLA Silk @U1 0.4 nozzle")
        self.assertTrue(result["ok"], result)
        self.assertEqual(json.loads(self.path.read_text())["entries"]["filament:1"]["printers"], {U1: "Generic PLA Silk @U1 0.4 nozzle"})
        files, _ = sp.profile_files([spool(5, f)], self.snap)
        u1 = next(p for p in files.values() if p["compatible_printers"] == [U1])
        sv = next(p for p in files.values() if p["compatible_printers"] == [SV06])
        self.assertEqual(u1["inherits"], "Generic PLA Silk @U1 0.4 nozzle")
        self.assertEqual(sv["inherits"], "Generic PLA @System")   # the other printer keeps its own pick
        row = next(r for r in result["match"] if r["target"] == U1)
        self.assertEqual((row["name"], row["source"], row["confident"]), ("Generic PLA Silk @U1 0.4 nozzle", "remembered", True))
        self.assertIn(["extra_word", "silk"], row["reasons"])
        # A parent that no longer fits the material (the filament became PETG) is ignored, not used.
        files, _ = sp.profile_files([spool(5, filament(1, "Preto", "PETG", vendor="3D Procer"))], self.snap)
        self.assertEqual(next(p for p in files.values() if p["compatible_printers"] == [U1])["inherits"], "Generic PETG @U1 0.4 nozzle")
        # Automatic forgets it.
        self.assertTrue(sp.pick_parent(f, U1, None)["ok"])
        self.assertNotIn("filament:1", json.loads(self.path.read_text())["entries"])

    def test_refusals(self):
        f = filament(1, "Preto", "PLA", vendor="3D Procer")
        for target, name in ((U1, "Generic PETG @U1 0.4 nozzle"), (U1, "Nope"), ("Other printer", "Generic PLA @System"), (U1, 5)):
            self.assertFalse(sp.pick_parent(f, target, name)["ok"], (target, name))
        self.assertFalse(sp.pick_parent(None, U1, "Generic PLA @System")["ok"])
        self.assertFalse(self.path.exists())

    def test_editor_rows(self):
        f = filament(1, "PLA SnapSpeed Yellow", "PLA", vendor="Snapmaker")
        rows = sp.preset_match(f, self.snap)
        self.assertEqual([r["label"] for r in rows], ["Snapmaker U1", "Sovol SV06"])
        u1 = rows[0]
        self.assertEqual((u1["name"], u1["source"]), ("Snapmaker PLA SnapSpeed @U1", "auto"))
        self.assertEqual(u1["name"], u1["candidates"][0]["name"])
        self.assertLessEqual(len(u1["candidates"]), sp.MATCH_CHOICES)
        self.assertEqual(sp.preset_match(None, self.snap), [])

    def test_action_reads_the_filament_from_spoolman(self):
        f = filament(9, "Preto", "PLA", vendor="3D Procer")
        with mock.patch.object(sp, "spoolman_call", return_value=f) as call:
            result = sp.spool_action({"action": "match_parent", "filament": 9, "target": U1, "name": "Generic PLA @System"})
        self.assertTrue(result["ok"], result)
        call.assert_called_once_with("GET", "filament/9")
        self.assertEqual(json.loads(self.path.read_text())["entries"]["filament:9"]["printers"][U1], "Generic PLA @System")


if __name__ == "__main__":
    unittest.main()
