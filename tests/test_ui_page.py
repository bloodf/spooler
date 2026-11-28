"""The compiled Vue page (ui/ -> plugin/spooler/app.html, shipped next to the code) and the logic it runs.

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
import re
import shutil
import subprocess
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

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
    def test_app_html_is_the_recorded_page(self):
        page = sp.ui_page()
        self.assertEqual(hashlib.sha256(page.encode("utf-8")).hexdigest(), sp.UI_PAGE_SHA256)
        self.assertEqual(len(page.encode("utf-8")), sp.UI_PAGE_BYTES)
        info = json.loads((UI / "build.json").read_text(encoding="utf-8"))
        self.assertEqual(info["sha256"], sp.UI_PAGE_SHA256, "ui/build.json and the embedded page differ: rebuild and run scripts/embed_ui.py")
        self.assertEqual(page.count("__BOOT__"), 1)
        self.assertNotRegex(page, r"<script[^>]+src=|<link[^>]+href=\"https?:|@import\s*(?:url\(|[\"'])|url\(https?:")
        self.assertNotRegex(page, r"\bnew Function\b|\beval\(")
        self.assertIn("__VUE_OPTIONS_API__: true", (UI / "vite.config.ts").read_text(encoding="utf-8"))

    def test_licences_of_the_bundled_code_ship_in_the_plugin_file(self):
        # OrcaSlicer installs the package, not its dist-info; the page bundles Vue, PrimeVue (PrimeUIX), Lucide icons (ISC) and the
        # Manrope font (SIL OFL 1.1), whose licences ask for their notice in every copy.
        notices = sp.UI_LICENSES
        for name, marker in (("Vue.txt", "Yuxi (Evan) You"), ("PrimeVue.txt", "PrimeTek"), ("PrimeUIX.txt", "PrimeUI License"),
                             ("Lucide.txt", "ISC License"), ("Manrope.txt", "SIL OPEN FONT LICENSE")):
            text = (UI / "node_modules" / "@orca-plugins" / "ui-foundation" / "licenses" / name).read_text(encoding="utf-8").replace("\r\n", "\n").rstrip("\n")
            self.assertIn(f"===== {name} =====\n" + text, notices, name)
            self.assertIn(marker, notices, name)

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
        # The Settings window opens at the page a link asked for; anything but a page id is dropped.
        self.assertEqual(boot(sp.settings_html("", {"ok": False}, 100, page="s-src"))["page"], "s-src")
        self.assertEqual(boot(sp.settings_html("", {"ok": False}, 100))["page"], "")
        for bad in ("s-src</script>", "../x", 7, None):
            self.assertEqual(boot(sp.settings_html("", {"ok": False}, 100, page=bad))["page"], "")

    def test_spool_window_link_opens_its_settings_page(self):
        """Open Settings from the spool window names a page; the Settings window boots at it."""
        made = []
        with mock.patch.object(sp.orca.host, "ui", types.SimpleNamespace(create_window=lambda **k: made.append(k) or mock.Mock()), create=True):
            window = sp.SpoolerWindow()
            window._check_connection = lambda *a, **k: None
            window.on_message({"type": "settings", "page": "s-src"})
        page = made[-1]["html"]
        start = page.index('id="spooler-boot">') + len('id="spooler-boot">')
        self.assertEqual(json.loads(page[start:page.index("</script>", start)])["page"], "s-src")

    def test_settings_lists_one_switch_per_display_option(self):
        source = (UI / "src" / "settings" / "SettingsView.vue").read_text(encoding="utf-8")
        groups = source[source.index("const DISPLAY_GROUPS = ["):]
        keys = re.findall(r"'([a-z_]+)'", groups[:groups.index("] as const;")])   # the group titles (set.display...) have a dot
        # Archived spools are shown from the list's own Filters, not from Display.
        self.assertEqual(sorted(keys), sorted(key for key in sp.DISPLAY_DEFAULTS if key != "archived"))
        messages = (UI / "src" / "core" / "messages.ts").read_text(encoding="utf-8")
        for key in sp.DISPLAY_DEFAULTS:
            self.assertEqual(messages.count("'disp.%s':" % key), 2, key)   # English and Portuguese labels

    def test_stats_settings_come_last_and_group_weight_is_not_squeezed(self):
        settings = (UI / "src" / "settings" / "SettingsView.vue").read_text(encoding="utf-8")
        self.assertGreater(settings.index('id="s-stats"'), settings.index('id="s-printer"'))   # was test_stats_settings_come_last
        self.assertGreater(settings.index('id="s-stats"'), settings.index('id="s-src"'))
        spools = (UI / "src" / "components" / "SpoolTable.vue").read_text(encoding="utf-8")
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
            self.assertEqual(sp.text_language(), "pt-BR")   # Python's own texts follow the choice at once
        finally:
            sp.save_settings(settings)
            sp.text_language(fresh=True)


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

    def test_spool_paint_uses_every_colour(self):
        # The drawn spool (OuiSpool) and the swatch: one colour, every colour of a multi-colour filament, or none (unknown).
        out = run_logic(self, "console.log(JSON.stringify([L.spoolPaint({color_hex: 'c8501e'}), L.spoolPaint({color_hex: '000000', multi_color_hexes: '#ff0000,00ff00'}), "
                              "L.spoolPaint({multi_color_hexes: 'ff0000'}), L.spoolPaint({})]));")
        self.assertEqual(out, [{"color": "#c8501e", "colors": None}, {"color": "#ff0000", "colors": ["#ff0000", "#00ff00"]},
                               {"color": "#ff0000", "colors": None}, {"color": None, "colors": None}])

    def test_level_tone_follows_low_stock(self):
        out = run_logic(self, "console.log(JSON.stringify([[500, 100], [80, 100], [20, 100], [0, 100], [null, 100]].map(([g, low]) => L.levelTone(L.lowLevel(g, low)))));")
        self.assertEqual(out, ["normal", "low", "critical", "critical", "normal"])

    def test_left_label_follows_the_weight_setting(self):
        out = run_logic(self, "console.log(JSON.stringify([L.leftLabel(640, 64, 'grams', true, 'en'), L.leftLabel(640, 64, 'percent', true, 'en'), "
                              "L.leftLabel(640, 64, 'both', true, 'en'), L.leftLabel(null, 64, 'grams', true, 'en'), L.leftLabel(null, null, 'both', true, 'en'), "
                              "L.leftLabel(1380, null, 'percent', false, 'en')]));")
        # unknown grams show the percentage, never 0; nothing known is a dash
        self.assertEqual(out, ["640 g", "64%", "640 g", "64%", "\u2014", "1.38 kg"])

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

    def test_toolhead_units(self):
        out = run_logic(self, self.W + """
let p = {id: 'n', name: 'MK4', type: 'prusalink', units: [{kind: 'ext', slots: [null]}]};
p = P.addUnit(P.addUnit(p, 'tool'), 'tool');
const kinds = p.units.map(u => u.kind);
let full = p; for (let i = 0; i < 10; i++) full = P.addUnit(full, 'tool');
const cfg = [{name: 'MK4', units: [{kind: 'tool', slots: ['1']}, {kind: 'tool', slots: ['2']}]}];
console.log(JSON.stringify({kinds, max: full.units.length, net: [P.isNet(p), P.isNet({type: 'bambu'}), P.isNet({})],
  where: Object.fromEntries(P.computeInUse([], cfg, w))}));""")
        self.assertEqual(out, {"kinds": ["tool", "tool", "ext"], "max": 8, "net": [True, False, False],
                               "where": {"1": "MK4 · T1", "2": "MK4 · T2"}})

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


class UnitTests(unittest.TestCase):
    def test_ui_unit_tests_pass(self):
        """ui/tests/unit (npm run test:unit): every string in both languages and the locale rules."""
        need_node(self)
        files = sorted(str(p) for p in (UI / "tests" / "unit").glob("*.test.ts"))
        self.assertTrue(files, "ui/tests/unit has no tests")
        out = subprocess.run([NODE, "--no-warnings", "--test", *files], capture_output=True, text=True,
                             encoding="utf-8", timeout=120, cwd=UI)
        self.assertEqual(out.returncode, 0, out.stdout[-3000:] + out.stderr[-2000:])
        self.assertRegex(out.stdout, r"(?m)^\S* ?pass [1-9]")


class BuiltPage(unittest.TestCase):
    def test_page_scenarios_in_headless_chrome(self):
        need_node(self)
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "spooler-ui.html"
            page.write_text(sp.ui_page(), encoding="utf-8")   # exactly what the plugin serves
            results = Path(tmp) / "results.json"
            try:
                proc = subprocess.run([NODE, str(UI / "tests" / "page" / "run.mjs")], capture_output=True, text=True, timeout=900,
                                      env={**os.environ, "PAGE": str(page), "RESULTS": str(results)}, cwd=str(UI))
            except subprocess.TimeoutExpired as exc:
                def output(value):
                    return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else (value or "")
                self.fail(f"Page runner timed out after {exc.timeout}s\n{output(exc.stdout)}\n{output(exc.stderr)}")
            failed = [r for r in json.loads(results.read_text(encoding="utf-8")) if not r.get("ok")] if results.exists() else []
            self.assertEqual(proc.returncode, 0, "FAILED RESULTS: " + json.dumps(failed, indent=1)[-4000:] + "\n" + proc.stdout[-6000:] + proc.stderr)
            done = json.loads(results.read_text(encoding="utf-8"))
            self.assertGreaterEqual(len(done), 37)
            self.assertTrue(all(r["ok"] for r in done))


if __name__ == "__main__":
    unittest.main()
