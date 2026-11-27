"""Selecting a spool is fast: the last spool list is kept (memory, and a file so a restart has it too) and shown at
once while Spoolman is read again; a slot link is applied to that list instead of waiting for a full re-read; the
presets are not rebuilt for a list that changed only in a location or a weight; Spooler's own write is not read
again when Spoolman echoes it. No Spoolman is contacted: its answers are fakes."""

import json
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load
from test_live_updates import FakeWs, event, frame

sp, orca = load()

URL = "http://alice:secret@spoolman.test:7912"
PRINTERS = [{"target": "Snapmaker U1 (0.4 nozzle)", "label": "Snapmaker U1", "model": "Snapmaker U1", "hosts": ["http://u1.example"]}]
AUTO = [{"id": "auto-u1", "name": "Snapmaker U1", "ip": "http://u1.example", "units": [], "kind": "moonraker", "auto": True}]


def spool(sid, location="", colour="FF0000", used=0):
    return {"id": sid, "archived": False, "remaining_weight": 500 - used, "initial_weight": 1000, "location": location,
            "filament": {"id": sid, "name": f"F{sid}", "material": "PLA", "color_hex": colour, "weight": 1000}}


class Case(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        settings = {"spool_source": "spoolman", "spoolman_url": URL}
        for patch in (mock.patch.object(sp, "DATA_DIR", Path(self.tmp.name)), mock.patch.object(sp, "get_settings", lambda: settings),
                      mock.patch.dict(sp._listed, key="", spools=None, sig="", at=0.0),
                      mock.patch.dict(sp._spool_cache, url="", time=0.0, spools=[]),
                      mock.patch.dict(sp._synced, sig=None)):
            patch.start()
            self.addCleanup(patch.stop)
        self.settings = settings


class ListFileTest(Case):
    def test_the_list_survives_a_restart_for_the_same_source_only(self):
        spools = [spool(1), spool(2, "Shelf")]
        sp.listed_put(URL, spools)
        sp._listed.update(key="", spools=None, sig="", at=0.0)   # a restart: memory is empty
        self.assertEqual(sp.listed_get(URL), spools)
        self.assertGreater(sp._listed["at"], 0)
        sp._listed.update(key="", spools=None, sig="", at=0.0)
        self.assertIsNone(sp.listed_get("http://other.test:7912"), "another Spoolman never gets this list")
        self.assertIsNone(sp.listed_get(sp.BAMBU_KEY))

    def test_the_address_and_its_password_are_not_written(self):
        sp.listed_put(URL, [spool(1)])
        text = (Path(self.tmp.name) / sp.LIST_FILE).read_text(encoding="utf-8")
        self.assertNotIn("secret", text)
        self.assertNotIn("spoolman.test", text)

    def test_an_unchanged_list_is_not_written_again_and_a_broken_file_is_no_list(self):
        sp.listed_put(URL, [spool(1)])
        with mock.patch.object(sp, "_write_json") as write:
            sp.listed_put(URL, [spool(1)])
            write.assert_not_called()
            sp.listed_put(URL, [spool(1, "Shelf")])
            write.assert_called_once()
        sp._listed.update(key="", spools=None, sig="")
        (Path(self.tmp.name) / sp.LIST_FILE).write_text("{not json", encoding="utf-8")
        self.assertIsNone(sp.listed_get(URL))

    def test_the_archived_setting_names_another_list(self):
        sp.listed_put(URL, [spool(1)])
        with mock.patch.object(sp, "display_settings", lambda: {"archived": True}):
            self.assertIsNone(sp.listed_get(URL))


class FreshReadKeepsTheListTest(Case):
    def test_a_good_read_is_kept_and_a_failed_one_is_not(self):
        spools = [spool(1)]
        with mock.patch.object(sp, "load_spools_synced", return_value={"ok": True, "spools": spools}):
            result = sp.fresh_spools(None)
        self.assertTrue(result["ok"])
        self.assertEqual(sp.cached_spools()["spools"], spools)
        with mock.patch.object(sp, "load_spools_synced", return_value={"ok": False, "error": "down"}):
            sp.fresh_spools(None)
        self.assertEqual(sp.cached_spools()["spools"], spools, "the last good list stays")

    def test_the_cached_message_says_it_is_cached_with_the_origin_and_read_time(self):
        self.assertIsNone(sp.cached_spools())
        sp.listed_put(URL, [spool(1)])
        message = sp.cached_spools()
        self.assertEqual((message["type"], message["ok"], message["cached"], message["origin"]),
                         ("spools", True, True, sp.current_origin()[1]))
        self.assertAlmostEqual(message["read_at"], time.time(), delta=5)


class PushTest(Case):
    """A page that opens, or asks after a card action, gets the kept list first and the read after it."""

    def host(self):
        posted = []
        window = sp.SpoolerWindow()
        window._panel = mock.Mock(is_open=lambda: True, post=posted.append)
        page = sp.SpoolerPage()
        return window, page, posted

    def push(self, host, fresh, **kwargs):
        def run(fn, *a, **k):
            fn(*a)
            return mock.Mock()
        with mock.patch.object(sp, "ws_sync", lambda post: None), mock.patch.object(sp, "source", lambda: "spoolman"), \
             mock.patch.object(sp, "refresh_snapshot", lambda: None), mock.patch.object(sp, "_local_sync", lambda: None), \
             mock.patch.object(sp, "fresh_spools", fresh), mock.patch.object(sp, "spawn", run):
            host._push_data(**kwargs)

    def test_fast_shows_the_kept_list_before_the_read_and_a_plain_refresh_does_not(self):
        sp.listed_put(URL, [spool(1)])
        window, page, posted = self.host()
        for host in (window, page):
            for fast in (True, False):
                order = []
                fresh = mock.Mock(side_effect=lambda snapshot: order.append("read") or {"ok": True, "spools": [spool(1)], "origin": 1})
                self.push(host, fresh, fast=fast)
                got = [m for m in posted + getattr(page, "posted", []) if m.get("type") == "spools"]
                kinds = [bool(m.get("cached")) for m in got]
                self.assertEqual(kinds, [True, False] if fast else [False], (host, fast))
                posted.clear()
                page.posted = []

    def test_a_write_during_a_read_makes_it_read_again_without_showing_the_older_one(self):
        window, page, posted = self.host()
        for host in (window, page):
            calls = []

            def fresh(snapshot, host=host):
                calls.append(1)
                if len(calls) == 1:
                    host._push_data(fast=True)   # the card action's refresh arrives while this read runs
                    return {"ok": True, "spools": [spool(1)], "origin": 1}
                return {"ok": True, "spools": [spool(1, "Snapmaker U1 T1")], "origin": 1}
            self.push(host, fresh)
            shown = [m for m in posted + getattr(page, "posted", []) if m.get("type") == "spools"]
            self.assertEqual(len(calls), 2, host)
            self.assertEqual([m["spools"][0]["location"] for m in shown], ["Snapmaker U1 T1"], host)
            self.assertFalse(host._again)
            posted.clear()
            page.posted = []


class SelectTest(Case):
    def setUp(self):
        super().setUp()
        sp._ui_snap.clear()
        sp._ui_snap.update(printers=PRINTERS)
        sp._auto_printers[:] = [dict(p) for p in AUTO]
        with sp._live_lock:
            sp._live["printers"]["auto-u1"] = {"name": "Snapmaker U1", "units": {}, "ext": {}, "time": 0.0, "bind": "T"}
        self.spools = [spool(1), spool(2, "Snapmaker U1 T1"), spool(3, "Shelf")]
        sp.listed_put(URL, self.spools)
        sp._spool_cache.update(url=URL, spools=self.spools)
        self.calls = []
        call = mock.patch.object(sp, "spoolman_call", side_effect=lambda *a: self.calls.append(a) or {})
        call.start()
        self.addCleanup(call.stop)
        self.addCleanup(sp._auto_printers.clear)
        self.addCleanup(sp._ui_snap.clear)
        self.addCleanup(lambda: sp._live["printers"].pop("auto-u1", None))

    def location(self, sid):
        return next(s for s in sp.cached_spools()["spools"] if s["id"] == sid)["location"]

    def test_a_slot_link_is_in_the_kept_list_without_reading_spoolman(self):
        result = sp.slot_bind(1, "auto-u1", 0, True)
        self.assertEqual((result["ok"], result["patched"]), (True, True))
        self.assertEqual((self.location(1), self.location(2)), ("Snapmaker U1 T1", None))
        self.assertEqual([c[0] for c in self.calls], ["PATCH", "PATCH"], "no list was read")

    def test_unlink_and_move_are_in_the_kept_list_too(self):
        self.assertTrue(sp.slot_bind(2, "auto-u1", 0, False)["patched"])
        self.assertIsNone(self.location(2))
        with mock.patch.object(sp, "source", return_value="spoolman"), mock.patch.object(sp, "stale_list", return_value=False):
            result = sp.spool_action({"action": "move", "id": 3, "location": "Dry box", "origin": 1})
        self.assertEqual((result["ok"], result["patched"], self.location(3)), (True, True, "Dry box"))

    def test_a_refused_link_changes_nothing(self):
        self.assertFalse(sp.slot_bind(99, "auto-u1", 0, True)["ok"])
        self.assertEqual(self.location(2), "Snapmaker U1 T1")


class PresetsOnlyWhenTheyCanChangeTest(Case):
    def setUp(self):
        super().setUp()
        self.syncs = []

        def profile_sync(spools, snapshot, force=False):
            self.syncs.append(force)
            sp._profiles.update(count=len(spools), error=self.error)
            return dict(sp._profiles)
        self.error = ""
        self.read = [spool(1), spool(2)]
        for patch in (mock.patch.object(sp, "profile_sync", profile_sync), mock.patch.dict(sp._profiles),
                      mock.patch.object(sp, "load_spools", lambda: {"ok": True, "spools": json.loads(json.dumps(self.read))}),
                      mock.patch.object(sp, "load_matches", lambda path: {"version": 1, "entries": {}}),
                      mock.patch.object(sp, "presets_settings", lambda: {"ofd": False})):
            patch.start()
            self.addCleanup(patch.stop)
        self.snapshot = {"printers": PRINTERS, "parents": [], "gen": 1, "project": 1}

    def sync(self, force=False):
        self.snapshot = {**self.snapshot, "gen": self.snapshot["gen"] + 1}   # every read of the presets counts up
        return sp.load_spools_synced(self.snapshot, force)

    def test_a_location_or_weight_moving_does_not_rebuild_the_presets(self):
        self.sync()
        self.read = [spool(1, "Snapmaker U1 T1", used=50), spool(2)]
        result = self.sync()
        self.assertEqual(self.syncs, [False])
        self.assertEqual(result["profiles"], {"count": 2, "error": ""})

    def test_a_filament_a_new_spool_force_or_an_error_does(self):
        self.sync()
        self.read = [spool(1, colour="00FF00"), spool(2)]
        self.sync()
        self.read = self.read + [spool(3)]
        self.sync()
        self.sync(force=True)
        self.assertEqual(self.syncs, [False, False, False, True])
        self.error = "refused"
        self.read = self.read + [spool(4)]
        self.sync()
        self.sync()
        self.assertEqual(len(self.syncs), 6, "a failed build is tried again")

    def test_the_printer_presets_changing_rebuilds(self):
        self.sync()
        self.snapshot = {**self.snapshot, "printers": []}
        self.sync()
        self.assertEqual(len(self.syncs), 2)


class OwnWriteEchoTest(Case):
    def run_session(self, own_write_at):
        stop = threading.Event()
        sock = FakeWs(frame(1, event("updated")), stop)
        posts = []
        with mock.patch.dict(sp._ws, post=posts.append), mock.patch.object(sp, "WS_DEBOUNCE", 0.05), \
             mock.patch.dict(sp._own_write, at=own_write_at):
            sp._ws_handshake(sock, "ws://spoolman:7912/api/v1/spool")
            sp._ws_listen(sock, stop)
        return posts

    def test_the_echo_of_our_own_write_is_not_read_again(self):
        self.assertEqual(self.run_session(time.monotonic()), [])

    def test_a_change_made_elsewhere_still_is(self):
        self.assertEqual(self.run_session(time.monotonic() - 60), [{"type": "spool_changed"}])

    def test_a_write_marks_the_time_and_a_read_does_not(self):
        before = sp._own_write["at"]
        fake = mock.MagicMock()
        fake.__enter__.return_value.read.return_value = b"{}"
        with mock.patch("urllib.request.urlopen", return_value=fake):
            sp._spoolman_open("http://spoolman.test:7912", "spool", "GET")
            self.assertEqual(sp._own_write["at"], before)
            sp._spoolman_open("http://spoolman.test:7912", "spool/1", "PATCH", {"location": None})
        self.assertGreater(sp._own_write["at"], before)


if __name__ == "__main__":
    unittest.main()
