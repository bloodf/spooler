"""Open Filament Database: contacted only after the user's consent, given with Add Spool > Look up in OFD (the 0.33
Settings toggle, when it was on, counts as consent). Edit Spool, the list, a refresh and printing never reach it; a
lookup that failed is not tried again for OFD_RETRY. The network is never reached here."""

import json
import shutil
import tempfile
import time
from pathlib import Path
from unittest import mock

from fake_bundle import FIXTURES
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
        for name in ("SETTINGS_FILE", "OLD_SETTINGS"):   # this file's plugin copy (test_profiles'), not only Settings'
            patch = mock.patch.object(sp, name, self.dir / (name + ".json"))
            patch.start()
            self.addCleanup(patch.stop)
        self.calls = []
        fetch = mock.patch.object(sp.filmatch, "_ofd_get", self.get)
        fetch.start()
        self.addCleanup(fetch.stop)
        for state in (mock.patch.dict(sp._ofd_fail, {"at": None, "error": ""}), mock.patch.dict(sp._spool_cache)):
            state.start()
            self.addCleanup(state.stop)

    def get(self, url, headers=None):
        self.calls.append(url)
        return 200, (FIXTURES / "ofd_index.json").read_bytes(), {}

    def test_no_consent_by_default_and_never_fetched(self):
        self.assertFalse(sp.presets_settings()["ofd"])
        self.assertEqual(sp.ofd_status(refresh=True), {"on": False})
        self.assertEqual(sp.ofd_suggest("Polymaker", "PLA"), {"ok": False, "text": "", "consent": False})
        self.assertEqual(self.calls, [])
        self.assertNotIn(sp.filmatch.OFD_ORIGIN, sp.permission_targets()["network_http"])

    def test_the_old_toggle_counts_as_consent(self):
        sp.update_settings({"presets": {"per_spool": False, "tuning": False, "materials": {}, "ofd": True}})   # 0.33/0.34 saved it so
        self.assertTrue(sp.presets_settings()["ofd"])
        self.assertIn(sp.filmatch.OFD_ORIGIN, sp.permission_targets()["network_http"])
        self.assertTrue(sp.ofd_suggest("Polymaker", "PLA")["ok"])

    def test_consent_is_kept_and_a_settings_save_never_changes_it(self):
        sp.set_ofd_consent(True)
        sp.save_presets({"per_spool": True, "tuning": False, "materials": {}, "ofd": False})   # a Settings form read before
        self.assertEqual((sp.presets_settings()["ofd"], sp.presets_settings()["per_spool"]), (True, True))
        sp.set_ofd_consent(False)   # Settings > Presets > Revoke
        sp.save_presets({"per_spool": True, "tuning": False, "materials": {}, "ofd": True})
        self.assertFalse(sp.presets_settings()["ofd"])

    def test_edit_spool_never_reaches_ofd(self):
        sp.set_ofd_consent(True)
        rows = sp.preset_match(filament(1, "Panchroma Matte Red", "PLA", vendor="Polymaker"), snapshot())
        self.assertEqual(len(rows), 2)
        self.assertTrue(all("ofd" not in r for r in rows))
        self.assertEqual(self.calls, [])
        with mock.patch.object(sp, "spoolman_call", return_value={"id": 3, "filament": filament(1, "Red", "PLA", vendor="Polymaker")}), \
                mock.patch.dict(sp._ui_snap, snapshot(), clear=True):
            editor = sp.editor_data(3)
        self.assertTrue(editor["ofd_consent"])
        self.assertEqual(self.calls, [])

    def test_suggest_after_consent_reads_once_a_day(self):
        sp.set_ofd_consent(True)
        found = sp.ofd_suggest("Polymaker", "PLA", "Panchroma Matte Red")
        self.assertEqual(found["ofd"][0]["name"], "Polymaker Dual Panchroma Matte PLA (OFD)")
        self.assertTrue(all(c["source"] == "ofd" for c in found["ofd"]))
        self.assertEqual(sp.ofd_suggest("Nobody", "PLA")["ofd"], [])
        self.assertEqual(len(self.calls), 1)   # the kept index serves the next lookup
        state = sp.ofd_status()
        self.assertEqual((state["on"], state["error"], state["stale"]), (True, "", False))
        self.assertGreater(state["count"], 10)
        self.assertEqual(len(self.calls), 1)   # opening Settings reads only what is kept
        sp.ofd_status(refresh=True)
        self.assertEqual(len(self.calls), 2)   # Read again
        meta = json.loads((self.dir / "ofd" / "index.meta.json").read_text())
        meta["fetched"] = time.time() - sp.filmatch.OFD_TTL - 5
        (self.dir / "ofd" / "index.meta.json").write_text(json.dumps(meta))
        with mock.patch.object(sp.filmatch, "_ofd_get", side_effect=OSError("offline")):
            found = sp.ofd_suggest("Polymaker", "PLA")
        self.assertEqual((found["ofd"][0]["source"], found["ofd_error"]), ("ofd", ""))   # the kept index still proposes

    def test_a_failed_fetch_is_not_retried_for_a_while(self):
        sp.set_ofd_consent(True)
        offline = mock.Mock(side_effect=OSError("offline"))
        with mock.patch.object(sp.filmatch, "_ofd_get", offline):
            now = time.time()
            self.assertEqual(sp.ofd_lookup(now=now)["error"], "offline")
            for later in (1, 60, sp.OFD_RETRY - 1):   # no index kept: filmatch alone would wait for the timeout each time
                found = sp.ofd_lookup(now=now + later)
                self.assertEqual((found["profiles"], found["error"]), ([], "offline"))
            self.assertEqual(offline.call_count, 1)
            self.assertEqual(sp.ofd_suggest("Polymaker", "PLA")["ofd_error"], "offline")
            self.assertEqual(offline.call_count, 1)
            sp.ofd_lookup(now=now + 5, force=True)   # Read again asks at once
            self.assertEqual(offline.call_count, 2)
            sp.ofd_lookup(now=now + 5 + sp.OFD_RETRY)   # and after the pause, a lookup asks again
            self.assertEqual(offline.call_count, 3)
        self.assertTrue(sp.ofd_lookup(now=now + 6 + 2 * sp.OFD_RETRY)["profiles"])
        self.assertIsNone(sp._ofd_fail["at"])   # a good read clears the pause

    def test_the_page_action_runs_off_the_list_and_gives_consent_on_the_ui_thread(self):
        posted, spawned, asked = [], [], []
        with mock.patch.object(sp, "spawn", spawned.append), mock.patch.object(sp, "request_permissions", lambda: asked.append(1)):
            sp.start_spool_action({"action": "ofd_suggest", "vendor": "Polymaker", "material": "PLA", "key": "polymaker|pla", "ref": 4}, posted.append)
            self.assertFalse(sp.presets_settings()["ofd"])   # no consent sent: none taken
            spawned.pop()()
            self.assertEqual((posted[-1]["ok"], posted[-1]["consent"], posted[-1]["key"]), (False, False, "polymaker|pla"))
            self.assertEqual((self.calls, asked), ([], []))
            sp._spool_cache["time"] = 123.0
            sp.start_spool_action({"action": "ofd_suggest", "vendor": "Polymaker", "material": "PLA", "consent": True, "key": "polymaker|pla", "ref": 5}, posted.append)
            self.assertTrue(sp.presets_settings()["ofd"])   # the click is the consent, kept before any fetch
            self.assertEqual((asked, self.calls), ([1], []))   # OFD's address declared with it
            spawned.pop()()
        self.assertEqual((posted[-1]["type"], posted[-1]["action"], posted[-1]["ok"], posted[-1]["ref"]), ("action_result", "ofd_suggest", True, 5))
        self.assertEqual(posted[-1]["ofd"][0]["brand"], "Polymaker")
        self.assertEqual(sp._spool_cache["time"], 123.0)   # a lookup leaves the spool list as it is
        self.assertEqual(len(self.calls), 1)

    def test_settings_revokes_in_both_hosts_and_answers_off(self):
        for host in (sp.SpoolerWindow(), sp.SpoolerPage()):
            sp.set_ofd_consent(True)
            host._settings_window = mock.Mock()
            with mock.patch.object(sp, "spawn", lambda work: work()):
                host._on_settings({"type": "ofd", "revoke": True, "refresh": False})
            self.assertFalse(sp.presets_settings()["ofd"])
            self.assertEqual(host._settings_window.post.call_args[0][0], {"type": "ofd_state", "on": False})
        self.assertEqual(self.calls, [])
