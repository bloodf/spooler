"""The compiled Vue page (ui/ -> embedded in spooler_any.py) and the logic it runs.

* The embedded block matches ui/dist/spooler-ui.html (when built) and decompresses to the recorded hash.
* The page as shipped (decompressed from the plugin, boot filled like page_html does) runs its behaviour
  scenarios in an owned headless Chrome under a host-like CSP (ui/tests/page/run.mjs).
* Pure page rules (ui/src/logic/*.ts) run in Node and are compared with the plugin's Python where both exist.
Ports of the former page-script tests of test_display, test_drying, test_notices, test_review_fixes (F10-F12),
test_printer_control, test_detail_export, test_stats, test_send, test_wizard and test_u1control.
Needs Node.js 22.6+ (`node` on PATH or NODE=...) and Chrome/Chromium (found automatically or CHROME=...)."""

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from plugin_loader import load

sp, orca = load()
ROOT = Path(__file__).resolve().parents[1]
UI = ROOT / "ui"
NODE = os.environ.get("NODE") or shutil.which("node")


def need_node(case):
    if not NODE:
        case.fail("Node.js is needed for the page tests: put node on PATH or set NODE")


def run_logic(case, body: str):
    """Run `body` (an ES module using the page's logic modules) in Node; it prints one JSON line."""
    need_node(case)
    script = ("import * as L from %s;\nimport * as P from %s;\n" % (
        json.dumps((UI / "src" / "logic" / "spools.ts").as_uri()), json.dumps((UI / "src" / "logic" / "printers.ts").as_uri()))) + body
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "probe.mjs"
        path.write_text(script, encoding="utf-8")
        out = subprocess.run([NODE, "--no-warnings", str(path)], capture_output=True, text=True, encoding="utf-8", timeout=60)
    case.assertEqual(out.returncode, 0, out.stderr[-3000:])
    return json.loads(out.stdout.strip().splitlines()[-1])


class Embedded(unittest.TestCase):
    def test_block_decompresses_to_the_recorded_page(self):
        page = sp.ui_page()
        self.assertEqual(hashlib.sha256(page.encode("utf-8")).hexdigest(), sp.UI_PAGE_SHA256)
        self.assertEqual(len(page.encode("utf-8")), sp.UI_PAGE_BYTES)
        info = json.loads((UI / "build.json").read_text(encoding="utf-8"))
        self.assertEqual(info["sha256"], sp.UI_PAGE_SHA256, "ui/build.json and the embedded page differ: rebuild and run scripts/embed_ui.py")
        self.assertEqual(page.count("__BOOT__"), 1)
        self.assertNotRegex(page, r"<script[^>]+src=|<link[^>]+href=\"https?:|@import|url\(https?:")
        self.assertNotRegex(page, r"\bnew Function\b|\beval\(")
        self.assertIn("__VUE_OPTIONS_API__: true", (UI / "vite.config.ts").read_text(encoding="utf-8"))

    def test_block_matches_the_build_when_present(self):
        built = UI / "dist" / "spooler-ui.html"
        if not built.exists():   # a fresh checkout without `npm run build`: the hash test above still applies
            return
        out = subprocess.run(["python3", str(ROOT / "scripts" / "embed_ui.py"), "--check"], capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)

    def test_surfaces_carry_their_boot(self):
        def boot(page):
            start = page.index('<script type="application/json" id="spooler-boot">') + len('<script type="application/json" id="spooler-boot">')
            return json.loads(page[start:page.index("</script>", start)])
        tab = boot(sp.tab_html("main", "http://x", 100.0))
        self.assertEqual((tab["mode"], tab["view"]), ("tab", "main"))
        self.assertEqual(tab["display_defaults"], sp.DISPLAY_DEFAULTS)
        self.assertEqual(boot(sp.tab_html("settings", "", 100, wizard=True))["settings"]["wizard"], True)   # was test_pages_carry_the_flag
        self.assertEqual(boot(sp.settings_html("", {"ok": False}, 100))["settings"]["wizard"], False)
        self.assertEqual(boot(sp.settings_html("http://s:7912/", {"ok": True}, 100))["settings"]["verified_url"], "http://s:7912")
        self.assertEqual(boot(sp.main_html())["mode"], "main")
        self.assertIn("orca_settings", tab["own_fields"])
        self.assertNotIn("</script", sp.tab_html("main", "http://x</script><b>", 100.0).split("spooler-boot")[1].split("</script>")[0])

    def test_settings_lists_one_switch_per_display_option(self):
        source = (UI / "src" / "settings" / "SettingsView.vue").read_text(encoding="utf-8")
        keys = []
        for name in ("SPOOL_KEYS", "HEAD_KEYS"):
            line = source[source.index("const %s = [" % name):]
            keys += json.loads(line[line.index("["):line.index("]") + 1].replace("'", '"').replace("\n", ""))
        self.assertEqual(sorted(keys), sorted(sp.DISPLAY_DEFAULTS))
        messages = (UI / "src" / "core" / "messages.ts").read_text(encoding="utf-8")
        for key in sp.DISPLAY_DEFAULTS:
            self.assertEqual(messages.count("'disp.%s':" % key), 2, key)   # English and Portuguese labels

    def test_stats_settings_come_last_and_group_weight_is_not_squeezed(self):
        settings = (UI / "src" / "settings" / "SettingsView.vue").read_text(encoding="utf-8")
        self.assertGreater(settings.index('id="s-stats"'), settings.index('id="s-printer"'))   # was test_stats_settings_come_last
        self.assertGreater(settings.index('id="s-stats"'), settings.index('id="s-src"'))
        spools = (UI / "src" / "components" / "SpoolsView.vue").read_text(encoding="utf-8")
        rule = spools[spools.index(".sv-gbar {"):]
        rule = rule[:rule.index("}")]
        self.assertIn("min-width: 90px", rule)   # was test_group_header_weight_is_never_squeezed_into_a_fixed_width
        self.assertIn("white-space: nowrap", rule)
        self.assertNotRegex(rule, r"(?<![-\w])width:")

    def test_language_choice_is_saved_and_validated(self):
        settings = sp.get_settings()
        try:
            sp.save_ui_language("pt-BR")
            self.assertEqual(sp.ui_language(), "pt-BR")
            sp.save_ui_language("xx")
            self.assertEqual(sp.ui_language(), "pt-BR")
        finally:
            sp.save_settings(settings)


class Logic(unittest.TestCase):
    def test_colour_ranking_matches_python(self):
        target = "#c8501e"
        cols = ["c85032", "ff0000", "00ff00", "112233", "c8501e", "zzzzzz"]
        py = sorted((c for c in cols if sp.colour_diff(c, target) is not None), key=lambda c: sp.colour_diff(c, target))
        spools = [{"id": i, "filament": {"color_hex": c}} for i, c in enumerate(cols)]
        spools.append({"id": 9, "filament": {"color_hex": "000000", "multi_color_hexes": "ffffff,c85033"}})
        out = run_logic(self, "console.log(JSON.stringify({r: L.closestSpools(%s, %r).map(s => s.id), d: %s.map(c => L.colourDiff(c, %r))}));"
                        % (json.dumps(spools), target, json.dumps(cols), target))
        order = [i for i in out["r"] if i != 9]
        self.assertEqual(order, [cols.index(c) for c in py])
        self.assertLess(out["r"].index(9), out["r"].index(1))
        for c, d in zip(cols, out["d"]):
            py_d = sp.colour_diff(c, target)
            self.assertTrue((py_d is None and d is None) or abs(py_d - d) < 1e-9)

    W = "const w = {ams: 'AMS', ht: 'AMS HT', ext: 'External spool', externalShort: 'External', slot: (u, n) => u + ' Slot ' + n, head: n => 'T' + n};\n"

    def test_slot_names_match_the_printer_panel(self):
        out = run_logic(self, self.W + """
const one = {name: 'X1', unit_label: 'AMS 2 Pro', units: [{id: 0, kind: 'ams', trays: []}]};
const two = {name: 'X1', units: [{id: 0, kind: 'ams'}, {id: 1, kind: 'ams'}]};
console.log(JSON.stringify({one: P.slotName(one, one.units[0], 0, false, w), two: P.slotName(two, two.units[1], 2, false, w)}));""")
        self.assertEqual(out, {"one": "AMS 2 Pro Slot 1", "two": "AMS 2 Slot 3"})

    def test_manual_slot_names_match_the_manual_panel(self):
        out = run_logic(self, self.W + """
const cfg = [{name: 'P1', units: [{kind: 'ams', slots: ['1']}, {kind: 'ht', slots: ['2']}, {kind: 'ams', slots: [null, '3']}, {kind: 'ext', slots: ['4']}]}];
console.log(JSON.stringify(Object.fromEntries(P.computeInUse([], cfg, w))));""")
        self.assertEqual(out, {"1": "P1 · AMS 1 Slot 1", "2": "P1 · AMS HT", "3": "P1 · AMS 2 Slot 2", "4": "P1 · External"})

    def test_dried_age_and_reminder_threshold(self):
        rows = [
            {"extra": {"dried": '"2026-11-11T00:00:00+00:00"'}, "dry_days": 30}, {"extra": {"dried": '"2026-11-10T00:00:00+00:00"'}, "dry_days": 30},
            {"extra": {"dried": '"2026-10-30T00:00:00+00:00"'}, "dry_days": 30}, {"extra": {"dried": '"2026-10-12T00:00:00+00:00"'}, "dry_days": 30},
            {"extra": {"dried": '"2026-10-11T00:00:00+00:00"'}, "dry_days": 30}, {"extra": {"dried": '"2025-01-01"'}, "dry_days": 0},
            {"extra": {"dried": '"2026-12-01"'}, "dry_days": 7}, {"extra": {}, "dry_days": 30}, {"dry_days": 30}, {"extra": {"dried": "garbage"}},
        ]
        out = run_logic(self, "const now = new Date(2026, 10, 11, 12).getTime(); console.log(JSON.stringify(%s.map(s => { const a = L.driedDays(s, now); "
                        "return a === null ? null : [a, L.driedOld(s, a)]; })));" % json.dumps(rows))
        self.assertEqual(out, [[0, False], [1, False], [12, False], [30, False], [31, True], [679, False], [0, False], None, None, None])

    def test_live_age_only_matters_once_stale(self):
        out = run_logic(self, "const s = (age, spool) => P.liveSig({links: {}, printers: [{id: 'p', age, units: [{trays: [{spool}]}]}]});"
                        "console.log(JSON.stringify([s(1, 1) === s(11, 1), s(11, 1) === s(200, 1), s(200, 1) === s(205, 1), s(205, 1) === s(206, 2)]));")
        self.assertEqual(out, [True, False, True, False])

    def test_search_and_weights(self):
        out = run_logic(self, """
const s = [{id: 1, location: 'Shelf A', filament: {name: 'Black'}}, {id: 7, lot_nr: 'L-42', comment: 'textured plate', filament: {name: 'Red'}}];
const f = q => s.filter(x => L.spoolMatches(x, q)).map(x => x.id);
console.log(JSON.stringify({a: f('shelf a'), b: f('l-42'), c: f('#7'), d: f('#70'), kg: L.formatWeight(1380, false, 'en'), g: L.formatWeight(1380, true, 'en'),
  pt: L.formatWeight(1380, true, 'pt-BR'), low: [L.lowLevel(90, 100), L.lowLevel(10, 100), L.lowLevel(150, 100), L.lowLevel(null, 100)]}));""")
        self.assertEqual(out, {"a": [1], "b": [7], "c": [7], "d": [], "kg": "1.38 kg", "g": "1,380 g", "pt": "1.380 g", "low": ["low", "out", "", ""]})


class BuiltPage(unittest.TestCase):
    def test_page_scenarios_in_headless_chrome(self):
        need_node(self)
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "spooler-ui.html"
            page.write_text(sp.ui_page(), encoding="utf-8")   # exactly what the plugin serves
            results = Path(tmp) / "results.json"
            proc = subprocess.run([NODE, str(UI / "tests" / "page" / "run.mjs")], capture_output=True, text=True, timeout=900,
                                  env={**os.environ, "PAGE": str(page), "RESULTS": str(results)}, cwd=str(UI))
            self.assertEqual(proc.returncode, 0, proc.stdout[-6000:] + proc.stderr)
            done = json.loads(results.read_text(encoding="utf-8"))
            self.assertGreaterEqual(len(done), 37)
            self.assertTrue(all(r["ok"] for r in done))


if __name__ == "__main__":
    unittest.main()
