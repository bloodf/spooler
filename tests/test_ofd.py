"""Open Filament Database proposals (Settings > Presets, off by default): nothing is read while off; while on, Edit
Spool lists OFD presets of the filament's manufacturer and material from the index kept in Spooler's folder, which is
fetched again only when a day old. The network is never reached here."""

import json
import shutil
import tempfile
import time
from pathlib import Path
from unittest import mock

from fake_bundle import FIXTURES, U1
from test_profiles import filament, snapshot, sp
from test_spool_actions import Settings


class OfdTest(Settings):
    def setUp(self):
        super().setUp()
        self.dir = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir, True)
        for name, target in (("matches_path", self.dir / "matches.json"), ("ofd_folder", self.dir / "ofd")):
            patch = mock.patch.object(sp, name, lambda target=target: target)
            patch.start()
            self.addCleanup(patch.stop)
        self.calls = []
        fetch = mock.patch.object(sp.filmatch, "_ofd_get", self.get)
        fetch.start()
        self.addCleanup(fetch.stop)

    def get(self, url, headers=None):
        self.calls.append(url)
        return 200, (FIXTURES / "ofd_index.json").read_bytes(), {}

    def turn_on(self):
        sp.save_presets({**sp.presets_settings(), "ofd": True})

    def test_off_by_default_and_never_fetched(self):
        self.assertFalse(sp.presets_settings()["ofd"])
        self.assertEqual(sp.ofd_status(refresh=True), {"on": False})
        rows = sp.preset_match(filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker"), snapshot())
        self.assertEqual([r["ofd"] for r in rows], [[], []])
        self.assertEqual(self.calls, [])
        self.assertNotIn(sp.filmatch.OFD_ORIGIN, sp.permission_targets()["network_http"])

    def test_on_proposes_and_reads_once_a_day(self):
        self.turn_on()
        self.assertIn(sp.filmatch.OFD_ORIGIN, sp.permission_targets()["network_http"])
        state = sp.ofd_status()
        self.assertEqual((state["on"], state["error"], state["stale"]), (True, "", False))
        self.assertGreater(state["count"], 10)
        rows = sp.preset_match(filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker"), snapshot())
        u1 = next(r for r in rows if r["target"] == U1)
        self.assertEqual(u1["ofd"][0]["name"], "Polymaker Dual Panchroma Matte PLA (OFD)")
        self.assertTrue(all(c["source"] == "ofd" for c in u1["ofd"]))
        self.assertEqual(len(self.calls), 1)   # the kept index serves the editor
        sp.ofd_status(refresh=True)
        self.assertEqual(len(self.calls), 2)   # Read again
        meta = json.loads((self.dir / "ofd" / "index.meta.json").read_text())
        meta["fetched"] = time.time() - sp.filmatch.OFD_TTL - 5
        (self.dir / "ofd" / "index.meta.json").write_text(json.dumps(meta))
        with mock.patch.object(sp.filmatch, "_ofd_get", side_effect=OSError("offline")):
            state = sp.ofd_status()
        self.assertEqual((state["stale"], state["error"]), (True, "offline"))
        self.assertEqual(sp.preset_match(filament(1, "Red", "PLA", vendor="Polymaker"), snapshot())[0]["ofd"][0]["source"], "ofd")
        self.assertEqual(sp.preset_match(filament(1, "Red", "PLA", vendor="Nobody"), snapshot())[0]["ofd"], [])
