"""Items left open by the first audit pass: printing-state confirmation for a Moonraker spool change,
a fresh Spoolman version before writes that depend on it, link status ownership on restart, the
legacy window's replies after it closed, and history scoped to the Spoolman it was booked on."""

import json
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()
DAY = 86400


def ext_doc(state: str) -> dict:
    return {"print": {"vt_tray": {"id": "254", "spool_id": 5}, "gcode_state": state}}


class FreshVersionTest(unittest.TestCase):
    """A Spoolman downgraded below 0.26 while OrcaSlicer runs: the write that depends on the version
    reads it again, so a one-key extra PATCH can't wipe the spool's other fields."""

    def setUp(self):
        sp._versions.clear()
        self.addCleanup(sp._versions.clear)

    def test_dried_date_reads_the_version_each_time(self):
        versions = iter(["0.26.0", "0.25.3"])
        calls = []

        def call(method, path, body=None):
            calls.append((method, path))
            if path == "info":
                return {"version": next(versions)}
            return {"extra": {"dryer": '"Box 2"', "dried": '"old"'}}
        with mock.patch.object(sp, "spoolman_call", side_effect=call), \
                mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)):
            first = sp._dried_extra(3, '"2026-11-14"')
            second = sp._dried_extra(3, '"2026-11-14"')
        self.assertEqual(first, {"dried": '"2026-11-14"'})
        self.assertEqual(second, {"dryer": '"Box 2"', "dried": '"2026-11-14"'}, "old Spoolman: whole map sent back")
        self.assertEqual(calls.count(("GET", "info")), 2)

    def test_reads_that_dont_write_still_use_the_cache(self):
        with mock.patch.object(sp, "spoolman_call", return_value={"version": "0.26.0"}) as call, \
                mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)):
            sp.spoolman_version()
            sp.spoolman_version()
        self.assertEqual(call.call_count, 1)

    def test_send_changes_checks_the_version_fresh(self):
        src = Path(sp.__file__).read_text(encoding="utf-8")
        body = src[src.index("def _send_changes"):src.index("def native_value")]
        self.assertIn("spoolman_at_least(SPOOLMAN_EXTRA_MERGE, fresh=True)", body)


class LinkStatusOwnerTest(unittest.TestCase):
    """A link restarted by _local_sync: the old thread ending must not erase the new one's status."""

    def check(self, run, link):
        old, new = threading.Event(), threading.Event()
        old.set()   # the old thread was stopped: its loop doesn't run again
        with mock.patch.dict(sp._local, {"p1": {"link": link, "stop": new, "thread": None}}), \
                mock.patch.dict(sp._live["links"], {"p1": "live"}):
            run("p1", link, old)
            self.assertEqual(sp._live["links"].get("p1"), "live", run.__name__)
            stray = threading.Event()
            stray.set()
            run("p1", link, stray)
            self.assertEqual(sp._live["links"].get("p1"), "live", "a thread never registered owns nothing")
            new.set()
            run("p1", link, new)
            self.assertNotIn("p1", sp._live["links"], "its own entry is removed")

    def test_every_link_runner(self):
        with mock.patch.object(sp, "_live_active", return_value=True):
            self.check(sp._local_run, {"ip": "127.0.0.1", "serial": "", "code": "x", "name": "B"})
            self.check(sp._moon_run, {"ip": "http://127.0.0.1:1", "name": "K", "kind": "moonraker"})
            self.check(sp._net_run, {"ip": "127.0.0.1:1", "name": "N", "kind": "octoprint", "code": "k"})

    def test_removed_printer_entry_goes(self):
        stop = threading.Event()
        stop.set()
        with mock.patch.dict(sp._local, {}, clear=True), mock.patch.dict(sp._live["links"], {"p2": "live"}):
            sp._net_run("p2", {"ip": "127.0.0.1:1", "name": "N", "kind": "octoprint"}, stop)
            self.assertNotIn("p2", sp._live["links"])


class LegacyWindowAfterCloseTest(unittest.TestCase):
    """The window build (no orca.pages): a booking still runs when the window closed meanwhile."""

    def setUp(self):
        self.win = sp.SpoolerWindow()
        self.win._panel = None

    def test_booking_runs_and_nothing_raises(self):
        done = threading.Event()

        def act(data):
            done.set()
            return {"prints": [], "notice": ""}
        with mock.patch.object(sp, "usage_action", side_effect=act), \
                mock.patch.object(sp.log, "exception") as logged:
            self.win.on_message({"type": "usage_book", "run": "r1", "rows": []})
            self.assertTrue(done.wait(5))
            time.sleep(0.1)
        logged.assert_not_called()

    def test_every_reply_survives_a_closed_window(self):
        with mock.patch.object(sp, "stats_data", return_value={}), mock.patch.object(sp, "spool_detail", return_value={}), \
                mock.patch.object(sp, "export_history", return_value={"ok": True}), \
                mock.patch.object(sp, "live_message", return_value={"type": "live"}), \
                mock.patch.object(sp, "start_send") as send, mock.patch.object(sp, "start_preset_sync"), \
                mock.patch.object(sp, "start_spool_action"), mock.patch.object(sp, "start_moon_spool"), \
                mock.patch.object(sp, "auto_send"), mock.patch.object(sp.log, "exception") as logged:
            for kind in ("live", "stats", "stats_export", "spool_detail", "send", "sync_presets", "spool_action",
                         "moon_spool", "tick"):
                self.win.on_message({"type": kind})
            time.sleep(0.2)
            post = send.call_args[0][0]
            post({"type": "sent", "ok": True, "text": ""})   # the worker's reply after the close
        logged.assert_not_called()

    def test_open_window_still_gets_the_reply(self):
        got = []
        self.win._panel = mock.Mock(is_open=lambda: True, post=got.append)
        self.win._post({"type": "x"})
        self.assertEqual(got, [{"type": "x"}])


if __name__ == "__main__":
    unittest.main()
