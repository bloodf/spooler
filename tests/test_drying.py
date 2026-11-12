"""0.18: drying tracker (the dried date on a spool, its card chip and menu actions) and the
drying reminder in the after-slice notice, with days per material saved in Settings."""

import datetime
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

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
        # The page reseeding its table from show_view, and sending drying with save, is a page scenario now
        # (ui/tests/page/run.mjs, "settings: one switch per Display option, drying table…").

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

    def act(self, action, current, version=(0, 26, 0)):
        calls = []

        def fake(method, path, body=None):
            calls.append((method, path, body))
            return current if (method, path) == ("GET", "spool/7") else {}

        with mock.patch.object(sp, "spoolman_call", fake), mock.patch.object(sp, "ensure_fields"), \
                mock.patch.object(sp, "spoolman_version", lambda: version), \
                mock.patch.object(sp, "today", lambda: datetime.date(2026, 11, 11)):
            result = sp.spool_action({"action": action, "id": 7})
        return result, [c for c in calls if c[0] == "PATCH"]

    # From Spoolman 0.26.0 a PATCH's extra is merged into the spool's: only the keys sent change, and
    # a key sent as null is removed. So each action sends its own field only, and never re-sends the others.
    def test_mark_dried_sends_only_its_field(self):
        result, patches = self.act("dried", {"id": 7, "extra": {"tag": '"04A1"', "dried": '"2025-01-01T00:00:00+00:00"'}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {"dried": '"2026-11-11T00:00:00+00:00"'}})])

    def test_clear_dried_sends_null_to_remove_the_field(self):
        result, patches = self.act("clear_dried", {"id": 7, "extra": {"tag": '"04A1"', "dried": '"2025-01-01"'}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {"dried": None}})])

    # Before 0.26.0 a PATCH's extra replaced the whole map: the other fields are read again and sent back.
    def test_older_spoolman_keeps_the_other_extra_fields(self):
        current = {"id": 7, "extra": {"tag": '"04A1"', "orca_flow_ratio": "0.98", "dried": '"2025-01-01T00:00:00+00:00"'}}
        result, patches = self.act("dried", current, version=(0, 25, 0))
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {
            "tag": '"04A1"', "orca_flow_ratio": "0.98", "dried": '"2026-11-11T00:00:00+00:00"'}})])
        result, patches = self.act("clear_dried", current, version=(0, 23, 1))
        self.assertTrue(result["ok"], result)
        self.assertEqual(patches, [("PATCH", "spool/7", {"extra": {"tag": '"04A1"', "orca_flow_ratio": "0.98"}})])

    def test_unknown_version_or_unreadable_extras_write_nothing(self):
        result, patches = self.act("dried", {"id": 7, "extra": {"tag": '"04A1"'}}, version=None)
        self.assertEqual((result["ok"], patches), (False, []))
        self.assertIn("Nothing was written", result["text"])
        for bad in ({"id": 7}, {"id": 7, "extra": ["x"]}, {"id": 7, "extra": {"tag": 5}}, None):
            result, patches = self.act("clear_dried", bad, version=(0, 25, 0))
            self.assertEqual((result["ok"], patches), (False, []), bad)

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




if __name__ == "__main__":
    unittest.main()
