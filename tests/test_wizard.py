"""First-run setup guide in Settings: the saved "done" flag, when it opens by itself, and the
page script's open / next / back / skip."""

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class FlagTest(unittest.TestCase):
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

    def test_opens_for_a_new_install(self):
        self.assertTrue(sp.wizard_pending())

    def test_not_for_someone_with_a_source_already(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912"})
        self.assertFalse(sp.wizard_pending())

    def test_not_again_once_done(self):
        sp.save_wizard_done()
        self.assertFalse(sp.wizard_pending())
        self.assertTrue(sp.get_settings()["wizard_done"])

    def test_done_survives_a_settings_save(self):
        sp.save_wizard_done()
        window = sp.SpoolerWindow()
        window._save_settings("http://spoolman:7912", 100)
        self.assertTrue(sp.get_settings()["wizard_done"])

    def test_window_and_tab_both_save_done(self):
        for host in (sp.SpoolerWindow(), sp.SpoolerPage()):
            sp.save_settings({})
            host._on_settings({"type": "wizard", "done": False})
            self.assertTrue(sp.wizard_pending())
            host._on_settings({"type": "wizard", "done": True})
            self.assertFalse(sp.wizard_pending())

    def test_tab_sends_the_flag_when_settings_open(self):
        page = sp.SpoolerPage()
        page._check_connection = lambda *a, **k: None
        page._open_settings()
        self.assertTrue(page.posted[-1]["wizard"])
        sp.save_wizard_done()
        page._open_settings()
        self.assertFalse(page.posted[-1]["wizard"])





if __name__ == "__main__":
    unittest.main()
