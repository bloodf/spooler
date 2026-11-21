"""Regressions for the 0.32.5 review: each test fails before its fix. Nothing here reaches a network."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class TestPressedDuringACheckTest(unittest.TestCase):
    def test_the_pressed_address_is_tested_next(self):
        for host in (sp.SpoolerWindow(), sp.SpoolerPage()):
            window = mock.Mock(is_open=lambda: True)
            pinged = []

            def ping(url, host=host, window=window, pinged=pinged):
                pinged.append(url)
                if url == "http://a.invalid":  # Test pressed while the ready-time check still runs
                    host._check_connection("http://b.invalid", window, "spoolman")
                return {"ok": True, "version": "0.22.1"}
            with mock.patch.object(sp, "spawn", lambda fn, *a, **k: fn(*a)), mock.patch.object(sp, "ping", ping), \
                    mock.patch.object(sp, "heard"), mock.patch.object(sp, "requirements", return_value=[]):
                host._check_connection("http://a.invalid", window, "spoolman")
            self.assertEqual(pinged, ["http://a.invalid", "http://b.invalid"])
            self.assertEqual(window.post.call_args.args[0]["url"], "http://b.invalid")
            self.assertEqual(host._verified_url, sp.clean_url("http://b.invalid"))
            self.assertFalse(host._testing)


class HistoryWasteShapeTest(unittest.TestCase):
    def test_support_without_purge_is_dropped(self):
        folder = Path(tempfile.mkdtemp())
        hist = [{"id": "a", "time": 1, "rows": [{"spool": 1, "grams": 4.0, "ws": 0.5}, {"spool": 2, "grams": 2.0, "ws": 0.1, "wp": 0.2}]}]
        (folder / "history.json").write_text(json.dumps(hist))
        with mock.patch.object(sp, "HISTORY_FILE", folder / "history.json"):
            rows = sp.hist_load()[0]["rows"]
        self.assertNotIn("ws", rows[0])
        self.assertEqual((rows[1]["ws"], rows[1]["wp"]), (0.1, 0.2))


if __name__ == "__main__":
    unittest.main()
