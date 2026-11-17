"""Settings > Requirements: the active spool source as a requirement, read from what the reads and
connection tests already heard (no probe of its own), Check again, and auto-send held off while
the source is missing."""

import tempfile
import unittest
import urllib.error
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class RequirementsTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patches = [mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                        mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json"),
                        mock.patch.object(sp, "AUTH_FILE", Path(self.tmp.name) / "auth.json"),
                        mock.patch.object(sp, "spawn", lambda fn, *a, **k: fn(*a))]
        for patch in self.patches:
            patch.start()
        sp._heard.clear()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        sp._heard.clear()
        self.tmp.cleanup()

    def status(self):
        return sp.requirements()[0]

    def test_no_address_is_missing_without_any_request(self):
        with mock.patch.object(sp, "_spoolman_open", side_effect=AssertionError("no probe")):
            self.assertEqual(self.status()["status"], "missing")
            self.assertEqual(self.status()["id"], "spoolman")

    def test_not_heard_yet_is_unknown_without_any_request(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912"})
        with mock.patch.object(sp, "_spoolman_open", side_effect=AssertionError("no probe")):
            self.assertEqual(self.status()["status"], "unknown")

    def test_found_after_a_good_ping_with_its_version(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912/"})
        window = sp.SpoolerWindow()
        settings = mock.Mock(is_open=lambda: True)
        window._settings_window = settings
        with mock.patch.object(sp, "_spoolman_open", return_value={"version": "0.22.1"}):
            window._on_settings({"type": "ready"})
        self.assertEqual(self.status(), {"id": "spoolman", "status": "ok", "details": "0.22.1"})
        posted = settings.post.call_args[0][0]
        self.assertEqual(posted["requirements"], [self.status()])

    def test_missing_after_a_failed_read_until_a_good_one(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912"})
        with mock.patch.object(sp, "_spoolman_open", side_effect=urllib.error.URLError("refused")):
            sp.get_spools("http://spoolman:7912")
        self.assertEqual(self.status()["status"], "missing")
        self.assertIn("Could not reach Spoolman", self.status()["details"])
        with mock.patch.object(sp, "_spoolman_open", return_value=[]), \
                mock.patch.object(sp, "publish_stock"), mock.patch.object(sp, "rfid_known", return_value={}):
            sp.get_spools("http://spoolman:7912")
        self.assertEqual(self.status()["status"], "ok")

    def test_check_again_forgets_and_asks_again(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912"})
        sp.heard("http://spoolman:7912", False, "old failure")
        for host in (sp.SpoolerWindow(), sp.SpoolerPage()):
            asked = []
            host._check_connection = lambda url, window, src=None: asked.append(url)
            if isinstance(host, sp.SpoolerWindow):
                host._settings_window = mock.Mock()
            host._on_settings({"type": "requirements"})
            self.assertEqual(asked, ["http://spoolman:7912"])
            self.assertEqual(self.status()["status"], "unknown")

    def test_bambu_signed_out_is_missing_signed_in_is_found(self):
        sp.save_settings({"spool_source": "bambu"})
        self.assertEqual(self.status()["id"], "bambu")
        self.assertEqual(self.status()["status"], "missing")
        sp.AUTH_FILE.write_text('{"access_token": "x", "account": "me@example.com"}', encoding="utf-8")
        self.assertEqual(self.status()["status"], "unknown")
        sp.heard(sp.BAMBU_KEY, True, "me@example.com")
        self.assertEqual(self.status()["status"], "ok")

    def test_auto_send_waits_while_the_source_is_missing(self):
        sp.save_settings({"spoolman_url": "http://spoolman:7912"})
        sp.heard("http://spoolman:7912", False, "Could not reach Spoolman")
        with mock.patch.object(sp, "edited_changes", side_effect=AssertionError("not while missing")):
            sp.auto_send(lambda msg: self.fail(f"posted {msg}"))
        sp.heard("http://spoolman:7912", True)
        with mock.patch.object(sp, "edited_changes", return_value=("", {})) as edited:
            sp.auto_send(lambda msg: None)
        edited.assert_called_once()

    def test_install_link_opens_spoolman_page(self):
        window = sp.SpoolerWindow()
        with mock.patch.object(sp, "open_url") as opened:
            window._on_settings({"type": "spoolman_help"})
            sp.SpoolerPage()._on_settings({"type": "spoolman_help"})
        self.assertEqual([c.args[0] for c in opened.call_args_list], [sp.SPOOLMAN_HELP] * 2)


class NothingAtImportTest(unittest.TestCase):
    def test_import_and_register_make_no_request_and_hear_nothing(self):
        with mock.patch("urllib.request.urlopen", side_effect=AssertionError("network at import")):
            module, _ = load()
            module.SpoolerPage()
        self.assertEqual(module._heard, {})


if __name__ == "__main__":
    unittest.main()
