"""First-run setup guide in Settings: the saved "done" flag, when it opens by itself, and the
page script's open / next / back / skip."""

import json
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()
NODE = shutil.which("node")


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

    def test_pages_carry_the_flag(self):
        self.assertIn("if (true) wizOpen();", sp.settings_html("", {"ok": False}, 100, wizard=True))
        self.assertIn("if (false) wizOpen();", sp.settings_html("", {"ok": False}, 100))
        self.assertIn("if (true) wizOpen();", sp.tab_html("settings", "", 100, wizard=True))
        tab = sp.tab_html("main", "", 100)
        self.assertIn('id="wiz"', tab)
        self.assertIn("window.__spoolerWizard.open()", tab)


@unittest.skipUnless(NODE, "node is needed to run the page script")
class PageScriptTest(unittest.TestCase):
    HARNESS = """
function stub() {
  const fn = function () { return stub(); };
  return new Proxy(fn, {
    get(t, k) {
      if (k === Symbol.iterator) return function* () {};
      if (k === Symbol.toPrimitive) return () => "";
      if (k === "length") return 0;
      if (!(k in t)) t[k] = stub();
      return t[k];
    },
    set(t, k, v) { t[k] = v; return true; },
    apply() { return stub(); },
  });
}
globalThis.document = stub();
globalThis.window = globalThis;
const handlers = [], posts = [];
globalThis.orca = { postMessage(m) { posts.push(m); }, onMessage(h) { handlers.push(h); } };
const tested = { ok: true, source: "spoolman", url: "http://spoolman:7912", version: "0.9" };
const guide = () => window.__spoolerWizard;
(function () {\n"""

    def run_page(self, scenario, **kwargs):
        page = sp.settings_html("http://spoolman:7912", {"ok": False, "pending": True}, 100, **kwargs)
        script = re.findall(r"<script>(.*?)</script>", page, re.S)[-1]
        path = Path(tempfile.mkdtemp()) / "page.js"
        path.write_text(self.HARNESS + script + "\n" + scenario + "\n})();", encoding="utf-8")
        out = subprocess.run([NODE, str(path)], capture_output=True, text=True, encoding="utf-8", timeout=30)
        self.assertEqual(out.returncode, 0, out.stderr[-2000:])
        return json.loads(out.stdout.strip().splitlines()[-1])

    def test_open_next_back_skip(self):
        got = self.run_page("""
          const seen = [guide().state()];
          guide().open();
          seen.push(guide().state().step);
          guide().next();
          seen.push(guide().state().step);
          guide().next();                       // blocked: the address is not tested yet
          seen.push(guide().state().step, guide().state().canNext);
          urlEl.value = "http://spoolman:7912";
          handlers.forEach(function (h) { h(Object.assign({ type: "test_result" }, tested)); });
          seen.push(guide().state().canNext);
          guide().next();
          seen.push(guide().state().step);
          guide().back();
          seen.push(guide().state().step);
          guide().skip();
          seen.push(guide().state());
          console.log(JSON.stringify({ seen, posts }));
        """)
        self.assertEqual(got["seen"], [None, 0, 1, 1, False, True, 2, 1, None])
        self.assertEqual(got["posts"].count({"type": "wizard", "done": True}), 1)

    def test_back_stops_at_the_first_step(self):
        got = self.run_page("""
          guide().open(); guide().back();
          console.log(JSON.stringify(guide().state()));
        """)
        self.assertEqual(got["step"], 0)

    def test_opens_by_itself_when_asked(self):
        self.assertEqual(self.run_page("console.log(JSON.stringify(guide().state()));", wizard=True)["step"], 0)
        self.assertIsNone(self.run_page("console.log(JSON.stringify(guide().state()));"))

    def test_finish_saves_and_marks_done(self):
        got = self.run_page("""
          urlEl.value = "http://spoolman:7912";
          handlers.forEach(function (h) { h(Object.assign({ type: "test_result" }, tested)); });
          saveEl.disabled = false;
          saveEl.click = function () { posts.push("save"); };
          guide().open();
          for (let i = 0; i < 5; i++) guide().next();
          const last = guide().state().step;
          guide().next();
          console.log(JSON.stringify({ last, after: guide().state(), posts }));
        """)
        self.assertEqual((got["last"], got["after"]), (5, None))
        self.assertEqual(got["posts"], [{"type": "ready"}, {"type": "wizard", "done": True}, "save"])


if __name__ == "__main__":
    unittest.main()
