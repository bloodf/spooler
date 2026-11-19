"""Every page Spooler shows fits OrcaSlicer's WebView2 on Windows (2 MiB once base64-encoded, 1.5 MiB of UTF-8):
a bigger page stays blank. Over the limit, the embedded web fonts go first."""

import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()


def size(html: str) -> int:
    return len(html.encode("utf-8"))


class WebViewLimit(unittest.TestCase):
    def test_every_surface_fits_with_its_fonts(self):
        # 10% headroom, as scripts/embed_ui.py demands at build time: the fallback above is for emergencies only.
        for html in (sp.tab_html("main", "http://spoolman.local:7912", 100.0), sp.main_html(),
                     sp.page_html("settings", "settings")):
            self.assertLessEqual(size(html), sp.WEBVIEW_PAGE_LIMIT * 0.9)
            self.assertRegex(html, sp._FONT_DATA)

    def test_a_page_that_fits_is_left_alone(self):
        self.assertEqual(sp.fit_webview("<p>x</p>"), "<p>x</p>")

    def test_over_the_limit_the_fonts_go_first(self):
        page = sp.ui_page()
        self.assertRegex(page, sp._FONT_DATA)
        with mock.patch.object(sp, "WEBVIEW_PAGE_LIMIT", size(page) - 1):
            lighter = sp.fit_webview(page)
        self.assertNotRegex(lighter, sp._FONT_DATA)
        self.assertIn('local("Manrope")', lighter)
        self.assertNotIn('local("Manrope")format', lighter)   # local() with format() would void the whole src
        self.assertLess(size(lighter), size(page))
        self.assertEqual(lighter.count("<script"), page.count("<script"))   # only the font data changed

    def test_still_too_big_is_logged(self):
        with mock.patch.object(sp, "WEBVIEW_PAGE_LIMIT", 10), self.assertLogs("spooler", "WARNING"):
            sp.fit_webview(sp.ui_page())


if __name__ == "__main__":
    unittest.main()
