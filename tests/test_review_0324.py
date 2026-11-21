"""Regressions for the 0.32.4 review: each test fails before its fix. Nothing here reaches a network."""

import json
import os
import stat
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class LowStockNumberTest(unittest.TestCase):
    def test_non_finite_values_fall_back_to_the_default(self):
        for value in ("nan", "inf", "1e999", float("inf"), float("nan")):
            self.assertEqual(sp.parse_low(value), sp.LOW_DEFAULT, value)
        self.assertEqual(sp.settings_form("", "inf")["low_stock_grams"], sp.LOW_DEFAULT)
        self.assertEqual(sp.parse_low("150"), 150)


class OpenInSpoolmanTest(unittest.TestCase):
    def test_only_a_web_address_is_opened(self):
        with mock.patch.object(sp, "get_settings", lambda: {"spoolman_url": "file:///C:/Windows/System32/calc.exe#"}), \
                mock.patch.object(sp, "open_url") as opener:
            result = sp._spool_write("open", 5, {})
        opener.assert_not_called()
        self.assertFalse(result["ok"])


class ReachErrorTest(unittest.TestCase):
    def test_the_password_never_shows(self):
        result = sp.ping("http://alice:secret@127.0.0.1:9/")
        self.assertFalse(result["ok"])
        self.assertNotIn("secret", result["error"])
        with mock.patch.object(sp, "publish_stock"), mock.patch.object(sp, "low_stock_crossed", return_value=[]):
            result = sp.get_spools("http://alice:secret@127.0.0.1:9")
        self.assertFalse(result["ok"])
        self.assertNotIn("secret", result["error"])


class PrivateFileTest(unittest.TestCase):
    @unittest.skipIf(os.name == "nt", "Windows keeps only the read-only bit of a mode")
    def test_the_temp_file_is_private_from_creation(self):
        target = Path(tempfile.mkdtemp()) / "auth.json"
        modes = []
        real_replace = os.replace

        def replace(src, dst):
            modes.append(stat.S_IMODE(os.stat(src).st_mode))
            return real_replace(src, dst)
        with mock.patch.object(sp.os, "chmod", lambda *a: None), mock.patch.object(sp.os, "replace", replace):
            sp._write_json(target, {"access_token": "tok"}, mode=0o600)
        self.assertEqual(modes, [0o600])
        self.assertEqual(json.loads(target.read_text())["access_token"], "tok")


class HistoryShapeTest(unittest.TestCase):
    def test_malformed_entries_do_not_break_the_stats(self):
        folder = Path(tempfile.mkdtemp())
        hist = [{"id": "a", "time": 1}, {"id": "b", "time": 2, "rows": [{"grams": 3}, "x", {"spool": 1, "grams": 2.5}]}, 7]
        (folder / "history.json").write_text(json.dumps(hist))
        with mock.patch.object(sp, "HISTORY_FILE", folder / "history.json"):
            loaded = sp.hist_load()
        self.assertEqual(loaded, [{"id": "b", "time": 2, "rows": [{"label": "", "colour": "", "spool": 1, "grams": 2.5}]}])
        self.assertEqual(sp.weekly_rates(loaded, 3), {1: 2.5})


class BambuPagingTest(unittest.TestCase):
    def test_the_offset_counts_every_item_sent(self):
        offsets = []
        pages = {0: [{"id": 1}, "junk"], 2: [{"id": 2}]}

        def page(auth, offset):
            offsets.append(offset)
            return {"hits": pages.get(offset, []), "total": 3}
        with mock.patch.object(sp, "_bambu_page", page):
            hits = sp.fetch_bambu({})
        self.assertEqual(offsets, [0, 2])
        self.assertEqual([h["id"] for h in hits], [1, 2])


class SliceGramsTest(unittest.TestCase):
    def test_infinite_grams_book_nothing(self):
        xml = (b'<config><plate><metadata key="index" value="1"/>'
               b'<filament id="1" used_g="inf"/><filament id="2" used_g="nan"/><filament id="3" used_g="4.5"/></plate></config>')
        rows = sp.parse_slice(xml)
        self.assertEqual([r["n"] for r in rows], [3])


class WebSocketHostTest(unittest.TestCase):
    def test_a_non_ascii_host_goes_as_dns_writes_it(self):
        sent = []

        class Sock:
            def sendall(self, data):
                sent.append(data)

            def recv(self, n):
                raise ConnectionError("done")
        with self.assertRaises(ConnectionError):
            sp._ws_handshake(Sock(), "ws://spöolman.lan:7912/api/v1/spool")
        self.assertIn(b"Host: xn--spolman-b1a.lan:7912\r\n", sent[0])


class PrinterHostTest(unittest.TestCase):
    def test_a_long_host_is_refused_not_cut_short(self):
        self.assertEqual(sp.clean_host("a" * 70), "")
        self.assertEqual(sp.clean_host("printer.lan"), "printer.lan")


class TinyGramsTest(unittest.TestCase):
    def test_grams_that_round_to_nothing_are_refused(self):
        self.assertIsNone(sp._action_grams("0.04"))
        self.assertEqual(sp._action_grams("0.04", zero=True), 0.0)
        self.assertEqual(sp._action_grams("12,34"), 12.3)
        with mock.patch.object(sp, "spoolman_use") as use:
            result = sp._spool_write("use", 5, {"grams": 0.04})
        use.assert_not_called()
        self.assertFalse(result["ok"])


if __name__ == "__main__":
    unittest.main()
