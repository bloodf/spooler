"""Settings > Display: what the Spools and Printer tabs show, saved with the Settings page and
sent to the pages; the page script for grouped spools, loaded spools and full slot cards."""

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class ParseTest(unittest.TestCase):
    def test_defaults_and_cleaning(self):
        self.assertEqual(sp.parse_display(None), sp.DISPLAY_DEFAULTS)
        parsed = sp.parse_display({"group_same": False, "spool_id": "yes", "unknown": True, "bar": "no"})
        self.assertFalse(parsed["group_same"])
        self.assertTrue(parsed["spool_id"])
        self.assertFalse(parsed["bar"])
        self.assertNotIn("unknown", parsed)
        self.assertEqual(set(parsed), set(sp.DISPLAY_DEFAULTS))


class SaveTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patches = [mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                        mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json")]
        for patch in self.patches:
            patch.start()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        self.tmp.cleanup()

    def test_saved_with_the_settings_page_even_when_save_is_refused(self):
        window = sp.SpoolerWindow()
        window._settings_window = mock.Mock()
        window._verified_url = ""
        window._on_settings({"type": "save", "url": "http://unverified", "display": {"group_same": False}})
        self.assertFalse(sp.display_settings()["group_same"])
        self.assertTrue(sp.display_settings()["vendor"])

    def test_other_settings_are_kept(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912", "low_stock_grams": 80})
        sp.save_display({"head_preset": False})
        settings = sp.get_settings()
        self.assertEqual((settings["spoolman_url"], settings["low_stock_grams"]), ("http://spoolman:7912", 80))
        self.assertFalse(settings["display"]["head_preset"])

    def test_not_a_dict_changes_nothing(self):
        sp.save_display("nonsense")
        self.assertEqual(sp.display_settings(), sp.DISPLAY_DEFAULTS)








if __name__ == "__main__":
    unittest.main()
