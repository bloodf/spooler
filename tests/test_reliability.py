"""The UI thread never waits on a booking, and background failures are logged, not lost."""
import threading
import time
import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()


class UsageStateDoesNotWaitTest(unittest.TestCase):
    def test_answers_with_last_list_while_a_booking_holds_the_lock(self):
        with mock.patch.object(sp, "usage_load", return_value={"prints": [{"id": "a"}]}), \
             mock.patch.object(sp, "source", return_value="spoolman"):
            self.assertEqual(sp.usage_state()["prints"], [{"id": "a"}])
            held, release = threading.Event(), threading.Event()

            def booking():
                with sp._usage_lock:
                    held.set()
                    release.wait(5)
            t = threading.Thread(target=booking)
            t.start()
            held.wait(5)
            try:
                with mock.patch.object(sp, "usage_load", side_effect=AssertionError("must not read under a held lock")):
                    start = time.monotonic()
                    state = sp.usage_state()
                    self.assertLess(time.monotonic() - start, 0.5)
                    self.assertEqual(state["prints"], [{"id": "a"}])
            finally:
                release.set()
                t.join(5)

    def test_same_thread_reenters(self):
        with mock.patch.object(sp, "usage_load", return_value={"prints": [{"id": "b"}]}), \
             mock.patch.object(sp, "source", return_value="spoolman"):
            with sp._usage_lock:
                self.assertEqual(sp.usage_state()["prints"], [{"id": "b"}])


class SpawnTest(unittest.TestCase):
    def test_exception_is_logged_with_the_task_name(self):
        def broken():
            raise ValueError("boom")
        with self.assertLogs(sp.log, "ERROR") as logs:
            sp.spawn(broken).join(5)
        self.assertIn("spooler-broken", logs.output[0])

    def test_args_pass_through(self):
        got = []
        sp.spawn(lambda a, b: got.append((a, b)), 1, "x").join(5)
        self.assertEqual(got, [(1, "x")])


class OneConnectionPerPrinterTest(unittest.TestCase):
    def test_concurrent_syncs_start_one_thread(self):
        started = []
        gate = threading.Barrier(8)

        def fake_run(pid, link, stop):
            started.append(pid)
            stop.wait(5)
        cfg = [{"id": "p1", "kind": "moonraker", "ip": "10.0.0.2", "name": "K1"}]
        with mock.patch.object(sp, "printers_cfg", return_value=cfg), mock.patch.object(sp, "read_codes", return_value={}), \
             mock.patch.object(sp, "_moon_run", fake_run), mock.patch.dict(sp._local, clear=True):
            def call():
                gate.wait(5)
                sp._local_sync()
            threads = [threading.Thread(target=call) for _ in range(8)]
            for t in threads:
                t.start()
            for t in threads:
                t.join(5)
            time.sleep(0.1)
            self.assertEqual(started, ["p1"])
            sp._local["p1"]["stop"].set()
