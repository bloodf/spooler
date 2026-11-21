"""The Spooler tab is never an empty grey panel (Orca Cloud report on 0.32.3, Windows: "Es bleibt einfach alles Grau").

OrcaSlicer shows nothing at all when get_ui() raises, and its sandbox checks every file a plugin opens during a
capability call such as get_ui(). 0.32.1 moved the page out of the code into app.html and read it there, so a refused
or failed read left the tab blank. The page is now read while the package imports (not checked), and any failure
building the page shows a page that says so, with the error and a Copy diagnostics button.
"""

import os
import sys
import sysconfig
import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()

_sandbox = {"on": False, "opened": []}
_STDLIB = tuple(os.path.realpath(p) for p in {sysconfig.get_paths()["stdlib"], sysconfig.get_paths()["platstdlib"]})


def _orca_like_audit(event, args):
    """OrcaSlicer's file rule inside a capability call, for these tests: the data folder and the standard library only."""
    if not _sandbox["on"] or event != "open" or not isinstance(args[0], (str, bytes, os.PathLike)):
        return
    path = os.path.realpath(os.fsdecode(args[0]))
    if path.startswith(os.path.realpath(sp.DATA_DIR)) or path.startswith(_STDLIB):
        return
    _sandbox["opened"].append(path)
    raise PermissionError('Plugin attempted audited operation "open" without permission: audit permission required')


sys.addaudithook(_orca_like_audit)   # cannot be removed; only active while _sandbox["on"]


class Sandboxed:
    def __enter__(self):
        _sandbox.update(on=True, opened=[])
        return _sandbox["opened"]

    def __exit__(self, *exc):
        _sandbox["on"] = False


class PageUnderSandbox(unittest.TestCase):
    def test_get_ui_opens_no_file_outside_the_data_folder(self):
        with mock.patch.object(sp, "sync_config", lambda *a, **k: None), Sandboxed() as opened:
            page = sp.SpoolerPage().get_ui()
        # A refused settings read is skipped (get_settings); nothing else may be opened, the page least of all.
        self.assertEqual([path for path in opened if not path.endswith(sp.SETTINGS_FILENAME)], [])
        self.assertIn('id="spooler-js"', page)          # the real page, not the error page
        self.assertNotIn("<pre id=\"d\">", page)

    def test_the_page_is_read_once_at_import(self):
        with mock.patch("pkgutil.get_data", side_effect=AssertionError("read again")):
            self.assertIn('id="spooler-js"', sp.main_html())


class NeverBlank(unittest.TestCase):
    def assertErrorPage(self, page, error):
        self.assertIn("Spooler could not open its page.", page)
        self.assertIn("Copy diagnostics", page)
        self.assertIn(error, page)
        self.assertIn(sp.PLUGIN_VERSION, page)
        self.assertIn(str(sp.LOG_FILE), page)

    def test_get_ui_shows_an_error_page_instead_of_raising(self):
        with mock.patch.object(sp, "tab_html", side_effect=ValueError("bad settings")), self.assertLogs("spooler", "ERROR"):
            page = sp.SpoolerPage().get_ui()
        self.assertErrorPage(page, "ValueError: bad settings")

    def test_a_page_that_cannot_be_built_is_an_error_page_on_every_surface(self):
        with mock.patch.object(sp, "_PAGE_ERROR", "PermissionError: denied"), self.assertLogs("spooler", "ERROR"):
            for page in (sp.main_html(), sp.page_html("settings", "settings"), sp.tab_html("main", "", 100.0)):
                self.assertErrorPage(page, "PermissionError: denied")

    def test_the_error_page_is_escaped_and_redacted(self):
        page = sp.error_page(RuntimeError("<script>x</script> http://user:pw@host/"))
        self.assertNotIn("<script>x</script>", page)
        self.assertNotIn("user:pw", page)

    def test_the_error_page_itself_never_raises(self):
        class Unprintable(Exception):
            def __str__(self):
                raise RuntimeError("no text")
        with self.assertLogs("spooler", "ERROR"):
            self.assertIn("Spooler could not open its page.", sp.error_page(Unprintable()))

    def test_the_error_page_follows_the_language(self):
        with mock.patch.object(sp, "text_language", lambda fresh=False: "de"):
            page = sp.error_page("x")
        self.assertIn("Spooler konnte seine Seite nicht öffnen.", page)
        self.assertIn("Diagnose kopieren", page)


class PageReport(unittest.TestCase):
    def test_a_page_that_could_not_start_is_logged(self):
        report = {"type": "page_error", "errors": ["TypeError: x is undefined"], "agent": "Edg/120"}
        with self.assertLogs("spooler", "ERROR") as logs:
            sp.SpoolerPage().on_message(report)
        self.assertIn("TypeError: x is undefined", "\n".join(logs.output))


if __name__ == "__main__":
    unittest.main()
