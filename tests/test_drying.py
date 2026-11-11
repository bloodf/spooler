"""0.18: drying tracker (the dried date on a spool, its card chip and menu actions) and the
drying reminder in the after-slice notice, with days per material saved in Settings."""

import datetime
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load
from test_display import PageScriptTest as DisplayPage

sp, orca = load()
TODAY = datetime.date(2026, 11, 11)


def spool(sid, material="PETG", dried=None, left=900, **extra):
    row = {"id": sid, "remaining_weight": left, "initial_weight": 1000, "location": "", "extra": {},
           "filament": {"id": 5, "name": "Black", "material": material, "color_hex": "111111", "vendor": {"name": "Acme"}},
           **extra}
    if dried:
        row["extra"]["dried"] = json.dumps(dried)
    return row


class Store(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        for patch in (mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                      mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json"),
                      mock.patch.object(sp, "today", lambda: TODAY)):
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.tmp.cleanup)
        sp.save_settings({"spoolman_url": "http://spoolman:7912", "spool_source": "spoolman"})


class MaterialTest(Store):
    def test_defaults_and_prefix_matching_ignores_case(self):
        days = sp.drying_days
        self.assertEqual((days("PETG"), days("petg hf"), days("PA-CF"), days("pa"), days("TPU 95A")), (30, 30, 7, 7, 14))
        self.assertEqual((days("ABS"), days("PLA Matte"), days("Unknown"), days(None)), (0, 0, 0, 0))

    def test_longest_name_wins(self):
        self.assertEqual(sp.drying_days("PETG", {"PET": 5, "PETG": 20}), 20)

    def test_parse_cleans_the_table(self):
        self.assertEqual(sp.parse_drying(None), sp.DRYING_DEFAULTS)
        self.assertEqual(sp.parse_drying({" hips ": "10", "": 3, "X": "abc", "Y": -4, "Z": 99999, "B": True}),
                         {"HIPS": 10, "X": 0, "Y": 0, "Z": sp.DRYING_MAX_DAYS})

    def test_saved_by_both_hosts_even_when_save_is_refused(self):
        for host in (sp.SpoolerWindow(), sp.SpoolerPage()):
            host._settings_window = mock.Mock()
            host._verified_url = ""
            host._on_settings({"type": "save", "url": "http://unverified", "drying": {"nylon": 12, "petg": 0}})
            self.assertEqual(sp.drying_settings(), {"NYLON": 12, "PETG": 0})
            sp.save_drying("nonsense")
            self.assertEqual(sp.drying_settings(), {"NYLON": 12, "PETG": 0})
            sp.save_settings({})

    def test_tab_reseeds_the_table_when_settings_open(self):
        sp.save_drying({"HIPS": 9})
        page = sp.SpoolerPage()
        page._check_connection = lambda *a, **k: None
        page._open_settings()
        self.assertEqual(page.posted[-1]["drying"], {"HIPS": 9})
        tab = sp.tab_html("main", "http://x", 100.0)
        self.assertIn("window.__spoolerSetDrying(data.drying)", tab)
        self.assertIn('id="dry-body"', tab)
        self.assertIn("drying: dryPick()", sp.settings_html("http://x", {"ok": False}, 100.0))

    def test_spools_carry_their_reminder_days(self):
        with mock.patch.object(sp, "get_spools", return_value={"ok": True, "spools": [spool(1), spool(2, "PLA")]}), \
             mock.patch.object(sp, "ensure_fields"):
            got = sp.load_spools()["spools"]
        self.assertEqual([s["dry_days"] for s in got], [30, 0])


class FieldAndActionTest(Store):
    def test_field_is_created_on_demand_with_a_datetime_type(self):
        calls = []

        def fake(method, path, body=None):
            calls.append((method, path, body))
            return [] if method == "GET" else {}

        sp._fields_ready.clear()
        with mock.patch.object(sp, "spoolman_call", fake):
            sp.ensure_fields()
        self.assertIn(("POST", "field/spool/dried", {"name": "Dried", "field_type": "datetime", "order": 100}), calls)

    def test_existing_field_is_left_alone(self):
        calls = []
        sp._fields_ready.clear()
        with mock.patch.object(sp, "spoolman_call",
                               lambda m, p, b=None: calls.append((m, p, b)) or [{"key": "dried"}, {"key": "orca_flow_ratio"},
                                                                                {"key": "orca_pressure_advance"},
                                                                                {"key": "orca_max_volumetric_speed"}]):
            sp.ensure_fields()
        self.assertEqual([c for c in calls if c[0] == "POST"], [])

    def act(self, action, current):
        calls = []

        def fake(method, path, body=None):
            calls.append((method, path, body))
            return current if (method, path) == ("GET", "spool/7") else {}

        with mock.patch.object(sp, "spoolman_call", fake), mock.patch.object(sp, "ensure_fields"):
            result = sp.spool_action({"action": action, "id": 7})
        return result, [c for c in calls if c[0] == "PATCH"]

    def test_mark_dried_keeps_other_extra_fields(self):
        result, patches = self.act("dried", {"id": 7, "extra": {"tag": '"04A1"', "dried": '"2025-01-01T00:00:00+00:00"'}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {"tag": '"04A1"', "dried": '"2026-11-11T00:00:00+00:00"'}})])

    def test_clear_dried_removes_only_its_field(self):
        result, patches = self.act("clear_dried", {"id": 7, "extra": {"tag": '"04A1"', "dried": '"2025-01-01"'}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {"tag": '"04A1"'}})])

    def test_needs_spoolman_and_a_spool(self):
        self.assertFalse(sp.spool_action({"action": "dried"})["ok"])
        with mock.patch.object(sp, "source", lambda: "bambu"):
            self.assertFalse(sp.spool_action({"action": "dried", "id": 7})["ok"])


class PlateNoticeTest(Store):
    SLOT = {"preset": "", "vendor": "Acme", "material": "PETG", "colour": "111111", "sub_type": "", "n": 2,
            "grams": 100, "ams": True}

    def check(self, spools, slot=None):
        slot = slot or self.SLOT
        return sp.check_group({"slot": slot, "pool": 1, "used": [slot]}, spools, 10)

    def test_old_and_unmarked_spools_get_a_sentence_and_stay_info(self):
        old = self.check([spool(1, dried="2026-10-01T00:00:00+00:00")])  # 41 days
        self.assertEqual(old["dry"], {"days": 41})
        kind, text = sp.plate_notice([old])
        self.assertEqual(kind, "info")
        self.assertIn("Black (slot 2) was last dried 41 days ago.", text)
        never = self.check([spool(1)])
        self.assertEqual(sp.plate_notice([never])[0], "info")
        self.assertIn("Black (slot 2) has no drying date.", sp.plate_notice([never])[1])

    def test_fresh_dry_off_and_unknown_dates_stay_quiet(self):
        self.assertIsNone(self.check([spool(1, dried="2026-11-01T00:00:00+00:00")])["dry"])  # 10 d <= 30
        self.assertIsNone(self.check([spool(1, "PLA")], {**self.SLOT, "material": "PLA"})["dry"])
        text = sp.plate_notice([self.check([spool(1, dried="2026-11-01T00:00:00+00:00")])])[1]
        self.assertNotIn("dried", text)

    def test_order_after_stock_sentences_before_cost_and_never_a_warning_alone(self):
        r = self.check([spool(1, left=20)])
        self.assertEqual(r["status"], "short")
        kind, text = sp.plate_notice([r], "About €1.00 of filament.")
        self.assertEqual(kind, "warning")
        self.assertLess(text.index("not enough"), text.index("has no drying date"))
        self.assertLess(text.index("has no drying date"), text.index("About"))
        self.assertTrue(text.endswith("About €1.00 of filament."))
        fits = sp.fit_text(text, text.index(" About") + len(" (+1 more, see the log)"))  # room for all but the cost
        self.assertIn("has no drying date", fits)
        self.assertNotIn("About", fits)

    def test_cost_matches_nothing_to_do_with_dry(self):
        ok = self.check([spool(1, "PETG", dried="2026-11-10T00:00:00+00:00")])
        kind, text = sp.plate_notice([ok])
        self.assertEqual(kind, "info")
        self.assertIn("quantity OK", text)


class ChipTest(DisplayPage):
    """The card chip and menu, run in node. 2026-11-11 is the page's "today" (noon, local time)."""
    NOW = "new Date(2026, 10, 11, 12).getTime()"
    run_page = DisplayPage.run_page

    def chips(self, spools, flags="{}"):
        return self.run_page(f"""
disp = Object.assign({{}}, DISPLAY_DEFAULTS, {flags});
const now = {self.NOW};
const out = {{ chips: {json.dumps(spools)}.map(function (s) {{ return driedChip(s, now); }}) }};
console.log(JSON.stringify(out));
""")["chips"]

    def test_age_text_and_colour_threshold(self):
        rows = [
            {"extra": {"dried": '"2026-11-11T00:00:00+00:00"'}, "dry_days": 30},   # today
            {"extra": {"dried": '"2026-11-10T00:00:00+00:00"'}, "dry_days": 30},   # 1 d
            {"extra": {"dried": '"2026-10-30T00:00:00+00:00"'}, "dry_days": 30},   # 12 d, fresh
            {"extra": {"dried": '"2026-10-12T00:00:00+00:00"'}, "dry_days": 30},   # 30 d, exactly at the limit
            {"extra": {"dried": '"2026-10-11T00:00:00+00:00"'}, "dry_days": 30},   # 31 d, over
            {"extra": {"dried": '"2025-01-01"'}, "dry_days": 0},                    # old but no reminder
            {"extra": {"dried": '"2026-12-01"'}, "dry_days": 7},                    # future date
            {"extra": {}, "dry_days": 30}, {"dry_days": 30}, {"extra": {"dried": "garbage"}},
        ]
        chips = self.chips(rows)
        self.assertIn("Dried today", chips[0])
        self.assertIn("Dried 1 d ago", chips[1])
        self.assertIn("Dried 12 d ago", chips[2])
        self.assertNotIn(" old", chips[2])
        self.assertNotIn(" old", chips[3])
        self.assertIn(" old", chips[4])
        self.assertNotIn(" old", chips[5])
        self.assertIn("Dried today", chips[6])
        self.assertEqual(chips[7:], ["", "", ""])

    def test_flag_hides_it_and_the_card_shows_it(self):
        self.assertEqual(self.chips([{"extra": {"dried": '"2026-11-10"'}}], "{dried: false}"), [""])
        out = self.run_page(f"""
allSpools = {json.dumps([{**spool(1), "extra": {"dried": '"2026-11-10"', "dryer": '"Box 2"'}, "dry_days": 30}])};
disp = Object.assign({{}}, DISPLAY_DEFAULTS, {{group_same: false, extra_fields: true}});
spoolSource = "spoolman";
const out = {{ card: listHtml(allSpools) }};
console.log(JSON.stringify(out));
""")["card"]
        self.assertIn("dry-chip", out)
        self.assertNotIn("dried:", out)  # Spooler's own field never shows in the extra-fields line
        self.assertIn("dryer: Box 2", out)

    def test_menu_has_mark_and_only_then_clear(self):
        out = self.run_page(f"""
const marked = Object.assign({json.dumps(spool(1))}, {{ extra: {{ dried: '"2026-11-10"' }} }});
disp = Object.assign({{}}, DISPLAY_DEFAULTS, {{group_same: false}});
spoolSource = "spoolman";
allSpools = [marked, {json.dumps(spool(2))}];
const sent = [];
orca.postMessage = function (m) {{ sent.push(m); }};
menu = {{id: 1, mode: "", armed: "", val: ""}};
const a = spoolMenuHtml(marked);
menu = {{id: 2, mode: "", armed: "", val: ""}};
const b = spoolMenuHtml(allSpools[1]);
menu = {{id: 1, mode: "", armed: "", val: ""}};
spoolAct({{dataset: {{act: "sp-dried", id: "1"}}}});
menu = {{id: 1, mode: "", armed: "", val: ""}};
spoolAct({{dataset: {{act: "sp-clear-dried", id: "1"}}}});
console.log(JSON.stringify({{a: a, b: b, sent: sent.map(function (m) {{ return m.action; }})}}));
""")
        self.assertIn("Mark Dried Today", out["a"])
        self.assertIn("Clear Dried Date", out["a"])
        self.assertIn("Mark Dried Today", out["b"])
        self.assertNotIn("Clear Dried Date", out["b"])
        self.assertEqual(out["sent"], ["dried", "clear_dried"])


if __name__ == "__main__":
    unittest.main()
