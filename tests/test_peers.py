"""Presence and stock files for u1control: Spooler says it runs, and publishes its stock only while
u1control runs in this OrcaSlicer and its tab shows the stock. Read-only towards Spoolman."""

import json
import os
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()

SPOOLS = [
    {"id": 7, "archived": False, "remaining_weight": 500.0, "initial_weight": 1000.0, "location": "Shelf A",
     "first_used": "2026-01-01T00:00:00",
     "filament": {"id": 70, "name": "Matte Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
    {"id": 8, "archived": False, "remaining_weight": 40.0, "initial_weight": 1000.0, "location": "Snapmaker U1 T2",
     "filament": {"id": 70, "name": "Matte Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
    {"id": 9, "archived": True, "remaining_weight": 0, "filament": {"id": 71, "name": "Old"}},
]


class PeerCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        settings = {"spool_source": "spoolman", "spoolman_url": "http://alice:secret@Box:7912/", "low_stock_grams": 100}
        for patch in (mock.patch.object(sp, "_orca_data_dir", lambda: self.root),
                      mock.patch.object(sp, "get_settings", lambda: settings)):
            patch.start()
            self.addCleanup(patch.stop)
        self.settings = settings
        self.requests = []

        def spoolman(base, path, method="GET", body=None):
            self.requests.append((method, path))
            return [dict(s) for s in SPOOLS] if path.startswith("spool") else {"version": "0.26.0"}
        patch = mock.patch.object(sp, "_spoolman_open", spoolman)
        patch.start()
        self.addCleanup(patch.stop)
        sp._peer.update(session="sess1", started=time.time(), seq=0, stock_at=0.0, served=None)
        self.addCleanup(sp._peer.update, session="", users=0, thread=None, stop=None)

    def u1control(self, ts=None, state="active", pid=None, until=None, request=0):
        now = time.time()
        doc = {"schema": "orca-plugin-presence", "version": 1, "plugin": "u1control", "session": "u1s",
               "pid": os.getpid() if pid is None else pid, "ts": now if ts is None else ts, "state": state,
               "wants": {"stock_until": now + 10 if until is None else until, "stock_request": request}}
        folder = self.root / "u1control"
        folder.mkdir(exist_ok=True)
        (folder / "presence.json").write_text(json.dumps(doc), encoding="utf-8")

    def stock(self):
        path = self.root / "spooler" / "stock.json"
        return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None

    def presence(self):
        return json.loads((self.root / "spooler" / "presence.json").read_text(encoding="utf-8"))


class PresenceTest(PeerCase):
    def test_presence_names_spooler_without_credentials(self):
        self.assertTrue(sp.publish_presence())
        doc = self.presence()
        self.assertEqual((doc["plugin"], doc["state"], doc["pid"], doc["session"], doc["provides"]),
                         ("spooler", "active", os.getpid(), "sess1", {"stock": 1}))
        self.assertEqual(doc["spoolman"], {"source": "spoolman", "origin": "http://box:7912"})
        self.assertNotIn("secret", json.dumps(doc))

    def test_public_url(self):
        self.assertEqual(sp.public_url("https://u:p@[::1]:7912/x/"), "https://[::1]:7912/x")
        self.assertEqual(sp.public_url("http://box"), "http://box")

    def test_start_and_stop_count_capabilities_and_say_stopped(self):
        sp._peer.update(session="", users=0)
        with mock.patch.object(sp, "PEER_BEAT", 0.05):
            sp.start_presence()
            sp.start_presence()
            first = self.presence()
            self.assertEqual(first["state"], "active")
            sp.stop_presence()
            self.assertEqual(self.presence()["state"], "active")     # another capability still loaded
            sp.stop_presence()
        last = self.presence()
        self.assertEqual((last["state"], last["session"]), ("stopped", first["session"]))
        sp.start_presence()                                           # a reload is a new session
        self.addCleanup(sp.stop_presence)
        self.assertNotEqual(self.presence()["session"], first["session"])

    def test_alive_only_for_fresh_active_file_of_this_process(self):
        now = time.time()
        good = {"schema": "orca-plugin-presence", "version": 1, "plugin": "u1control", "session": "x",
                "pid": os.getpid(), "ts": now, "state": "active"}
        self.assertTrue(sp.peer_alive(good, "u1control", now))
        for bad in ({**good, "pid": os.getpid() + 1}, {**good, "state": "stopped"}, {**good, "ts": now - 60},
                    {**good, "ts": now + 60}, {**good, "version": 2}, {**good, "session": ""}, {**good, "plugin": "x"},
                    {**good, "ts": True}, None, []):
            self.assertFalse(sp.peer_alive(bad, "u1control", now), bad)


class StockTest(PeerCase):
    def test_no_stock_file_without_a_running_u1control_that_asks(self):
        for setup in (lambda: None, lambda: self.u1control(pid=os.getpid() + 1), lambda: self.u1control(state="stopped"),
                      lambda: self.u1control(ts=time.time() - 120), lambda: self.u1control(until=time.time() - 1)):
            setup()
            sp.peer_tick()
            self.assertIsNone(self.stock())
        self.assertEqual(self.requests, [])

    def test_shown_stock_is_published_read_only(self):
        self.u1control(request=3)
        sp.peer_tick()
        doc = self.stock()
        self.assertEqual((doc["schema"], doc["version"], doc["session"], doc["request"]), ("spooler-stock", 1, "sess1", 3))
        self.assertEqual(doc["origin"]["url"], "http://box:7912")
        self.assertEqual(doc["origin"]["gen"], sp.current_origin()[1])
        self.assertEqual([r["id"] for r in doc["spools"]], [7, 8])           # archived left out
        r7, r8 = doc["spools"]
        self.assertEqual((r7["filament_id"], r7["vendor"], r7["colour"], r7["low"], r7["location"]), (70, "Acme", "111111", False, "Shelf A"))
        self.assertEqual((r8["low"], r8["u1_bound"]), (True, True))
        self.assertTrue(r7["use_first"] or r8["use_first"])
        self.assertEqual({m for m, _ in self.requests}, {"GET"})               # nothing written to Spoolman
        self.assertNotIn("secret", json.dumps(doc))

    def test_stock_row_full_weight_falls_back_to_the_filament(self):
        # U1 Control draws each spool's fill from remaining / full: the spool's initial weight, else the filament's.
        def row(spool):
            return sp.stock_row(spool, 100, {})
        self.assertEqual(row({"id": 1, "remaining_weight": 300, "initial_weight": 750, "filament": {"weight": 1000}})["initial"], 750)
        self.assertEqual(row({"id": 1, "remaining_weight": 300, "filament": {"weight": 1000}})["initial"], 1000)
        self.assertIsNone(row({"id": 1, "remaining_weight": 300, "filament": {}})["initial"])

    def test_refresh_follows_requests_and_otherwise_waits(self):
        self.u1control(request=1)
        sp.peer_tick()
        sp.peer_tick()
        self.assertEqual(len(self.requests), 1)                                # not before STOCK_EVERY
        self.u1control(request=2)
        sp.peer_tick()
        self.assertEqual((len(self.requests), self.stock()["request"]), (2, 2))

    def test_page_reads_publish_while_u1control_asks(self):
        with sp.pinned_origin() as origin:
            sp.get_spools(origin[0])                  # Spooler's own refresh, nobody asking
        self.assertIsNone(self.stock())
        self.u1control()
        with sp.pinned_origin() as origin:
            sp.get_spools(origin[0])
        self.assertEqual(len(self.stock()["spools"]), 2)

    def test_read_from_a_source_the_settings_left_is_not_published(self):
        self.u1control()
        old = sp.current_origin()[0]
        self.settings["spoolman_url"] = "http://other:7912"
        self.assertFalse(sp.publish_stock(old, SPOOLS))
        self.assertIsNone(self.stock())

    def test_spoolman_error_is_published_as_such(self):
        self.u1control()
        with mock.patch.object(sp, "_spoolman_open", side_effect=OSError("refused")):
            sp.peer_tick()
        doc = self.stock()
        self.assertEqual(doc["spools"], [])
        self.assertIn("refused", doc["error"])

    def test_bambu_source_says_there_is_no_spoolman_stock(self):
        self.settings["spool_source"] = "bambu"
        self.u1control()
        sp.peer_tick()
        doc = self.stock()
        self.assertEqual((doc["origin"]["source"], doc["spools"]), ("bambu", []))
        self.assertEqual(self.requests, [])
        self.assertEqual(self.presence()["spoolman"], {"source": "bambu", "origin": ""})

    def test_tick_never_raises(self):
        with mock.patch.object(sp, "publish_presence", side_effect=RuntimeError("boom")):
            sp.peer_tick()


if __name__ == "__main__":
    unittest.main()


class PeerHintTest(PeerCase):
    """The page's hint about U1 Control: only a running, fresh U1 Control in this process counts."""

    def test_hint_follows_u1control_presence(self):
        self.assertEqual(sp.peer_context(), {"peers": {"u1control": False}})          # not installed / never ran
        self.u1control()
        self.assertEqual(sp.peer_context(), {"peers": {"u1control": True}})
        self.u1control(state="stopped")
        self.assertFalse(sp.peer_context()["peers"]["u1control"])
        self.u1control(pid=os.getpid() + 1)                                          # another OrcaSlicer
        self.assertFalse(sp.peer_context()["peers"]["u1control"])
        self.u1control(ts=time.time() - 120)                                          # stopped answering
        self.assertFalse(sp.peer_context()["peers"]["u1control"])

    def test_hint_reads_files_only(self):
        self.u1control()
        self.requests.clear()
        sp.peer_context()
        self.assertEqual(self.requests, [])   # no Spoolman call, and nothing sent anywhere

    def test_message_extras_code_failed_reads(self):
        self.assertEqual(sp.spools_message_extras({"ok": False, "error": "x"})["error_code"], "read_failed")
        self.assertNotIn("error_code", sp.spools_message_extras({"ok": True, "spools": []}))
        self.assertEqual(sp.spools_message_extras({"ok": False, "error_code": "other"}).get("error_code"), None)


class SpoolsMessageTest(PeerCase):
    def test_no_url_message_has_a_code_and_the_peer_hint_in_both_hosts(self):
        self.settings["spoolman_url"] = ""
        self.u1control()
        posted = []
        window = sp.SpoolerWindow()
        window._panel = mock.Mock(is_open=lambda: True, post=posted.append)
        page = sp.SpoolerPage()
        with mock.patch.object(sp, "ws_sync", lambda post: None), mock.patch.object(sp, "source", lambda: "spoolman"):
            window._push_data()
            page._push_data()
        msgs = [m for m in posted + page.posted if m.get("type") == "spools"]
        self.assertEqual(len(msgs), 2)
        for m in msgs:
            self.assertEqual((m["ok"], m["error_code"], m["peers"]), (False, "no_url", {"u1control": True}))
        self.assertEqual(self.requests, [])


class RefreshRecoversTest(PeerCase):
    def test_a_failed_read_does_not_stop_later_refreshes(self):
        self.settings["spoolman_url"] = "http://spoolman.test:7912"
        posted = []
        window = sp.SpoolerWindow()
        window._panel = mock.Mock(is_open=lambda: True, post=posted.append)
        page = sp.SpoolerPage()
        boom = mock.Mock(side_effect=RuntimeError("Spoolman said 500"))

        def sync(fn, *a, **k):
            fn(*a)
            return mock.Mock()
        with mock.patch.object(sp, "ws_sync", lambda post: None), mock.patch.object(sp, "source", lambda: "spoolman"), \
             mock.patch.object(sp, "refresh_snapshot", lambda: None), mock.patch.object(sp, "_local_sync", lambda: None), \
             mock.patch.object(sp, "fresh_spools", boom), mock.patch.object(sp, "spawn", sync), \
             self.assertLogs(sp.log, "ERROR"):
            for host in (window, page):
                host._push_data()
                host._push_data()
                self.assertFalse(host._refreshing)
        self.assertEqual(boom.call_count, 4)
        msgs = [m for m in posted + page.posted if m.get("type") == "spools"]
        self.assertTrue(all(m["ok"] is False and "Spoolman said 500" in m["error"] for m in msgs))
