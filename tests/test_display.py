"""Settings > Display: what the Spools and Printer tabs show, saved with the Settings page and
sent to the pages; the page script for grouped spools, loaded spools and full slot cards."""

import json
import os
import re
import shutil
import subprocess
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


class PagesTest(unittest.TestCase):
    def test_settings_page_has_one_switch_per_option(self):
        page = sp.settings_html("http://x", {"ok": False}, 100.0)
        labels = re.findall(r'\["(\w+)", "', page[page.index("DISPLAY_LABELS"):page.index("function setDisplay")])
        self.assertEqual(sorted(labels), sorted(sp.DISPLAY_DEFAULTS))
        self.assertIn("display: dispPick()", page)

    def test_native_tab_keeps_the_display_card_and_defaults(self):
        page = sp.tab_html("main", "http://x", 100.0)
        self.assertIn('id="disp-spools"', page)
        self.assertIn('id="disp-heads"', page)
        self.assertIn(json.dumps(sp.DISPLAY_DEFAULTS), page)
        self.assertIn("window.__spoolerSetDisplay(data.display)", page)


NODE = shutil.which("node")
if os.environ.get("CI") and not NODE:
    raise RuntimeError("CI needs node to run the page script tests")


@unittest.skipUnless(NODE, "node is needed to run the page script")
class PageScriptTest(unittest.TestCase):
    """Runs the Spools tab's own functions in node against a tiny DOM stand-in."""

    def run_page(self, scenario):
        script = re.findall(r"<script>(.*?)</script>", sp.main_html(), re.S)[-1]
        harness = """
// Any element, property or call answers with another stand-in, so the page's start-up runs.
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
globalThis.localStorage = { getItem() { return null; }, setItem() {} };
globalThis.setInterval = () => 0; globalThis.setTimeout = () => 0;
const handlers = [];
globalThis.orca = { postMessage() {}, onMessage(h) { handlers.push(h); } };
(function () {\n""" + script + "\n" + scenario + "\n})();"
        path = Path(tempfile.mkdtemp()) / "page.js"
        path.write_text(harness, encoding="utf-8")
        out = subprocess.run([NODE, str(path)], capture_output=True, text=True, encoding="utf-8", timeout=30)
        self.assertEqual(out.returncode, 0, out.stderr[-2000:])
        return json.loads(out.stdout.strip().splitlines()[-1])

    SPOOLS = [
        {"id": 1, "remaining_weight": 400, "initial_weight": 1000, "location": "Shelf A",
         "filament": {"id": 5, "name": "Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
        {"id": 2, "remaining_weight": 980, "initial_weight": 1000, "location": "Shelf B",
         "filament": {"id": 5, "name": "Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
    ]
    LIVE = {"links": {}, "printers": [{"id": "auto-u1", "name": "U1", "heads": True, "ext": None, "units": [
        {"id": 0, "kind": "ams", "trays": [{"slot": 0, "empty": False, "type": "PLA", "name": "Black", "colour": "111111",
                                            "remain": 98, "rfid": False, "spool": 2, "profile": "_local/spooler/Acme PLA Black @U1",
                                            "linked": "u1control"}]}]}]}

    def scenario(self, display):
        return f"""
allSpools = {json.dumps(self.SPOOLS)};
disp = Object.assign({{}}, DISPLAY_DEFAULTS, {json.dumps(display)});
liveData = {json.dumps(self.LIVE)};
computeInUse();
const list = listHtml(allSpools);
const card = liveCard(liveData.printers[0].units[0].trays[0]);
console.log(JSON.stringify({{list, card}}));
"""

    def test_grouped_spools_show_full_totals_and_the_loaded_one_first(self):
        out = self.run_page(self.scenario({}))
        self.assertIn("1,380 g of 2,000 g", out["list"])
        self.assertIn("1 in use", out["list"])
        self.assertIn("In Use · U1 · T1", out["list"])
        self.assertLess(out["list"].index("980 g"), out["list"].index("400 g"))  # spool 2 is loaded: first

    def test_groups_and_single_spools_share_one_card(self):
        out = self.run_page(self.scenario({}))["list"]
        self.assertNotIn("spool-tag", out)  # no manufacturer badge on top of the card
        self.assertIn('class="spool-card stack-head"', out)
        self.assertEqual(out.count('<span class="spool-vendor">Acme</span>'), 3)  # group and both spools
        self.assertIn('<span class="stack-count">2</span>', out)

    def test_slot_card_has_the_spools_details(self):
        card = self.run_page(self.scenario({}))["card"]
        for text in ("Acme", "PLA", "#111111", "980 g of 1,000 g left", "Spool #2", "Shelf B",
                     "linked by u1control", "Acme PLA Black @U1"):
            self.assertIn(text, card)

    def test_every_switch_hides_its_part(self):
        off = {key: False for key in sp.DISPLAY_DEFAULTS}
        out = self.run_page(self.scenario(off))
        self.assertNotIn("group stack", out["list"])        # no grouping
        self.assertNotIn("In Use", out["list"])
        self.assertNotIn("spool-bar-track", out["list"])
        self.assertNotIn("Shelf", out["list"])
        self.assertIn("980 g", out["list"])
        # The hover text still names the preset, and the swatch is still the colour.
        visible = re.sub(r' (title|style)="[^"]*"', "", out["card"])
        for text in ("Acme", "#111111", "of 1,000 g", "Spool #2", "@U1", "spool-bar-track"):
            self.assertNotIn(text, visible)

    def test_group_card_follows_the_switches(self):
        out = self.run_page(self.scenario({"vendor": False, "material": False, "in_use": False}))
        self.assertIn("group stack", out["list"])
        visible = re.sub(r' (title|style)="[^"]*"', "", out["list"])
        for text in ("Acme", "PLA", "in use", "In Use"):
            self.assertNotIn(text, visible)
        self.assertLess(visible.index("400 g"), visible.index("980 g"))  # list order kept

    def test_slot_names_match_the_printer_panel(self):
        out = self.run_page("""
const one = {name: "X1", unit_label: "AMS 2 Pro", units: [{id: 0, kind: "ams", trays: []}]};
const two = {name: "X1", units: [{id: 0, kind: "ams"}, {id: 1, kind: "ams"}]};
console.log(JSON.stringify({one: slotName(one, one.units[0], 0, false), two: slotName(two, two.units[1], 2, false)}));
""")
        self.assertEqual(out, {"one": "AMS 2 Pro Slot 1", "two": "AMS 2 Slot 3"})

    def test_manual_slot_names_match_the_manual_panel(self):
        out = self.run_page("""
liveData = {printers: []};
cfg = [{name: "P1", units: [{kind: "ams", slots: ["1"]}, {kind: "ht", slots: ["2"]},
                            {kind: "ams", slots: [null, "3"]}, {kind: "ext", slots: ["4"]}]}];
computeInUse();
console.log(JSON.stringify(Object.fromEntries(inUse)));
""")
        self.assertEqual(out, {"1": "P1 · AMS 1 Slot 1", "2": "P1 · AMS HT", "3": "P1 · AMS 2 Slot 2", "4": "P1 · External"})

    def test_kilograms_when_exact_weights_are_off(self):
        out = self.run_page(self.scenario({"exact_weight": False}))
        self.assertIn("1.38 kg of 2.00 kg", out["list"])


if __name__ == "__main__":
    unittest.main()
