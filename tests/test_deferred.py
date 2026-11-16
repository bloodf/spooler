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


class MoonSpoolWhilePrintingTest(unittest.TestCase):
    def setUp(self):
        sp._local["sv"] = {"link": {"kind": "moonraker", "ip": "http://127.0.0.1:1", "name": "SV06"},
                           "stop": threading.Event(), "thread": None}
        self.addCleanup(sp._local.pop, "sv", None)
        patches = [mock.patch.object(sp, "source", return_value="spoolman"),
                   mock.patch.dict(sp._live["printers"], {"sv": {"spool_set": True}}),
                   mock.patch.dict(sp._spool_cache, {"spools": [{"id": 7, "filament": {"id": 1}}]}),
                   mock.patch.object(sp, "live_apply")]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def run_set(self, state: str, spool, confirmed=False):
        posted = []
        with mock.patch.object(sp, "moon_poll", return_value=(ext_doc(state), False)), \
                mock.patch.object(sp, "_moon_post", side_effect=lambda *a: posted.append(a) or {}):
            return sp.moon_set_spool("sv", spool, confirmed), posted

    def test_printing_or_paused_asks_first_and_changes_nothing(self):
        for state in ("RUNNING", "PAUSE", "PREPARE"):
            result, posted = self.run_set(state, 7)
            self.assertFalse(result["ok"])
            self.assertTrue(result["confirm"])
            self.assertIn("rest of this print", result["text"])
            self.assertEqual(posted, [])
            result, posted = self.run_set(state, None)
            self.assertTrue(result["confirm"], "clearing moves the print's use away too")
            self.assertEqual(posted, [])

    def test_confirmed_change_while_printing_is_sent(self):
        result, posted = self.run_set("RUNNING", 7, confirmed=True)
        self.assertTrue(result["ok"])
        self.assertEqual(posted, [("http://127.0.0.1:1", "/server/spoolman/spool_id", {"spool_id": 7})])

    def test_idle_needs_no_confirmation(self):
        for state in ("IDLE", "FINISH", "FAILED", None):
            doc = ext_doc(state) if state else {"print": {"vt_tray": {"id": "254"}}}
            posted = []
            with mock.patch.object(sp, "moon_poll", return_value=(doc, False)), \
                    mock.patch.object(sp, "_moon_post", side_effect=lambda *a: posted.append(a) or {}):
                result = sp.moon_set_spool("sv", 7)
            self.assertTrue(result["ok"], state)
            self.assertNotIn("confirm", result)
            self.assertEqual(len(posted), 1)

    def test_page_confirmation_flag_reaches_the_check(self):
        got = []
        with mock.patch.object(sp, "moon_set_spool", side_effect=lambda *a: got.append(a) or {"ok": True, "text": ""}), \
                mock.patch.object(sp, "stale_list", return_value=False), \
                mock.patch.object(sp, "live_snapshot", return_value={}), mock.patch.object(sp, "usage_state", return_value={}), \
                mock.patch.object(sp, "spawn", side_effect=lambda fn, *a, **k: fn(*a)):
            sp.start_moon_spool({"id": "sv", "spool": 7, "confirm": True}, lambda msg: None)
            sp.start_moon_spool({"id": "sv", "spool": 7, "confirm": "yes"}, lambda msg: None)
        self.assertEqual(got, [("sv", 7, True), ("sv", 7, False)])


class FreshVersionTest(unittest.TestCase):
    """A Spoolman downgraded below 0.22 (where a PATCH replaces the whole extra map) while OrcaSlicer runs: the write that depends on the version
    reads it again, so a one-key extra PATCH can't wipe the spool's other fields."""

    def setUp(self):
        sp._versions.clear()
        self.addCleanup(sp._versions.clear)

    def test_dried_date_reads_the_version_each_time(self):
        versions = iter(["0.26.0", "0.21.0"])
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
        self.assertIn("spoolman_at_least(SPOOLMAN_EXTRA_PARTIAL, fresh=True)", body)


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


class HistoryOriginTest(unittest.TestCase):
    """Spool ids are only unique inside one Spoolman: history booked on another isn't counted here.
    Entries from before Spooler noted the Spoolman (no origin) are kept and still shown."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        patches = [mock.patch.object(sp, "HISTORY_FILE", Path(self.dir.name) / "history.json"),
                   mock.patch.object(sp, "get_settings", lambda: {"stats": {"on": True, "cur": "gbp"},
                                                                  "spoolman_url": "http://a:7912/", "low_stock_grams": 0}),
                   mock.patch.object(sp, "plate_spools", return_value=[])]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        now = time.time()
        self.entries = [
            {"id": "old", "time": now - 2 * DAY, "name": "legacy", "printer": "P", "result": "finished", "pct": 100,
             "rows": [{"spool": 1, "grams": 10.0, "label": "L", "material": "PLA", "colour": "", "cost": None}]},
            {"id": "a", "time": now - 1 * DAY, "name": "on A", "printer": "P", "result": "finished", "pct": 100,
             "origin": "http://a:7912",
             "rows": [{"spool": 1, "grams": 20.0, "label": "A1", "material": "PLA", "colour": "", "cost": None}]},
            {"id": "b", "time": now - 1 * DAY, "name": "on B", "printer": "P", "result": "finished", "pct": 100,
             "origin": "http://b:7912",
             "rows": [{"spool": 1, "grams": 500.0, "label": "B1", "material": "PETG", "colour": "", "cost": None}]},
        ]
        sp.HISTORY_FILE.write_text(json.dumps(self.entries), encoding="utf-8")

    def test_stats_count_this_spoolman_and_legacy_only(self):
        out = sp.stats_data("30")
        self.assertEqual(out["grams"], 30.0)
        self.assertEqual({h["name"] for h in out["history"]}, {"legacy", "on A"})

    def test_spool_detail_doesnt_mix_servers(self):
        out = sp.spool_detail(1)
        self.assertEqual(out["grams"], 30.0)
        self.assertEqual([p["name"] for p in out["prints"]], ["on A", "legacy"])

    def test_export_is_scoped_too(self):
        with mock.patch.object(sp, "DATA_DIR", Path(self.dir.name)), mock.patch.object(sp, "open_url"):
            out = sp.export_history("all")
        text = Path(out["path"]).read_text(encoding="utf-8-sig")
        self.assertIn("on A", text)
        self.assertIn("legacy", text)
        self.assertNotIn("on B", text)

    def test_file_is_not_rewritten_by_reading(self):
        before = sp.HISTORY_FILE.read_bytes()
        sp.stats_data("all")
        sp.spool_detail(1)
        self.assertEqual(sp.HISTORY_FILE.read_bytes(), before)

    def test_new_bookings_are_tagged_and_other_servers_kept(self):
        entry = {"id": "n", "time": time.time(), "name": "new", "printer": "P", "result": "finished", "pct": 100,
                 "origin": "http://a:7912", "rows": [{"spool": 2, "grams": 5.0, "state": "booked", "label": "x"}]}
        sp.hist_note(entry, {})
        saved = json.loads(sp.HISTORY_FILE.read_text(encoding="utf-8"))
        self.assertEqual({e["id"] for e in saved}, {"old", "a", "b", "n"})
        self.assertEqual(next(e for e in saved if e["id"] == "n")["origin"], "http://a:7912")
        self.assertNotIn("origin", next(e for e in saved if e["id"] == "old"))


class WeeklyRateTest(unittest.TestCase):
    def test_short_history_is_not_spread_over_four_weeks(self):
        now = time.time()
        hist = [{"time": now - 3 * DAY, "rows": [{"spool": 1, "grams": 40.0}]}]
        self.assertEqual(sp.weekly_rates(hist, now), {1: 40.0})

    def test_two_weeks_of_history(self):
        now = time.time()
        hist = [{"time": now - 14 * DAY, "rows": [{"spool": 1, "grams": 30.0}]},
                {"time": now - 1 * DAY, "rows": [{"spool": 1, "grams": 10.0}]}]
        self.assertAlmostEqual(sp.weekly_rates(hist, now)[1], 20.0, places=3)


if __name__ == "__main__":
    unittest.main()
