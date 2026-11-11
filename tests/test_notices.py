"""0.17: low-stock notification, cost and swap suggestion in the plate notice, Use First choice."""

import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()


def spool(sid, left, fid=5, **extra):
    return {"id": sid, "remaining_weight": left, "initial_weight": 1000, "price": 25, "location": extra.pop("location", ""),
            "filament": {"id": fid, "name": "Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}},
            **extra}


SETTINGS = {"low_stock_grams": 100, "spoolman_url": "http://fake", "stats": {"on": True, "cur": "eur"}}


class LowStockTest(unittest.TestCase):
    def setUp(self):
        sp._low_seen.update(url=None, ids=set())
        for p in (mock.patch.object(sp, "get_settings", lambda: dict(SETTINGS)),
                  mock.patch.object(sp, "display_settings", lambda: dict(sp.DISPLAY_DEFAULTS))):
            p.start()
            self.addCleanup(p.stop)

    def test_first_load_only_seeds(self):
        self.assertEqual(sp.low_stock_crossed("u", [spool(1, 50)]), [])
        self.assertEqual(sp.low_stock_crossed("u", [spool(1, 50)]), [])

    def test_crossing_notifies_once_then_rearms(self):
        sp.low_stock_crossed("u", [spool(1, 500), spool(2, 50)])
        out = sp.low_stock_crossed("u", [spool(1, 90.4), spool(2, 50)])
        self.assertEqual(out, ["Spooler: Acme Black is down to 90 g"])
        self.assertEqual(sp.low_stock_crossed("u", [spool(1, 80), spool(2, 50)]), [])
        sp.low_stock_crossed("u", [spool(1, 900), spool(2, 50)])  # refilled
        self.assertEqual(len(sp.low_stock_crossed("u", [spool(1, 60), spool(2, 50)])), 1)

    def test_flag_off_stays_quiet_and_unknown_weight_ignored(self):
        sp.low_stock_crossed("u", [spool(1, 500)])
        with mock.patch.object(sp, "display_settings", lambda: {**sp.DISPLAY_DEFAULTS, "low_notice": False}):
            self.assertEqual(sp.low_stock_crossed("u", [spool(1, 10)]), [])
        self.assertEqual(sp.low_stock_crossed("u", [spool(1, 10)]), [])  # already known low
        self.assertEqual(sp.low_stock_crossed("u", [{"id": 3, "filament": {}}]), [])

    def test_get_spools_hooks_cache_update_and_skips_archived(self):
        with mock.patch.object(sp, "_spoolman_open", return_value=[spool(1, 50, archived=True)]), \
             mock.patch.object(sp, "push_notice") as push:
            sp.get_spools("http://fake")
            sp.get_spools("http://fake")
        push.assert_not_called()
        self.assertEqual(sp._low_seen["ids"], set())


class UseFirstTest(unittest.TestCase):
    def test_earliest_first_used_wins(self):
        pick = sp.use_first_id([spool(1, 500, first_used="2026-03-01T00:00:00"), spool(2, 900),
                                spool(3, 400, first_used="2026-01-01T00:00:00")])
        self.assertEqual(pick, {5: 3})

    def test_falls_back_to_registered_then_id(self):
        a = spool(7, 500, used_weight=10, registered="2026-02-01T00:00:00")
        b = spool(4, 500, used_weight=10, registered="2026-01-01T00:00:00")
        self.assertEqual(sp.use_first_id([a, b]), {5: 4})
        self.assertEqual(sp.use_first_id([spool(9, 1, used_weight=1), spool(2, 1, used_weight=1)]), {5: 2})

    def test_needs_two_live_spools_and_one_opened(self):
        self.assertEqual(sp.use_first_id([spool(1, 500, first_used="2026-01-01")]), {})
        self.assertEqual(sp.use_first_id([spool(1, 500), spool(2, 500)]), {})
        self.assertEqual(sp.use_first_id([spool(1, 500, first_used="2026-01-01"),
                                          spool(2, 500, archived=True)]), {})


class PlateNoticeTest(unittest.TestCase):
    SLOT = {"preset": "", "vendor": "Acme", "material": "PLA", "colour": "111111", "sub_type": "", "n": 1,
            "grams": 300, "ams": True}

    def setUp(self):
        for p in (mock.patch.object(sp, "get_settings", lambda: dict(SETTINGS)),
                  mock.patch.object(sp, "loaded_spool_ids", lambda: {"1"})):
            p.start()
            self.addCleanup(p.stop)

    def check(self, spools):
        group = {"slot": self.SLOT, "pool": 1, "used": [self.SLOT]}
        return sp.check_group(group, spools, 10)

    def test_swap_prefers_use_first_then_least_that_suffices(self):
        # Spool 1 is loaded and short; 2 and 3 are not loaded but only match through the filament id.
        r = sp.check_group({"slot": self.SLOT, "pool": 1, "used": [self.SLOT]}, [spool(1, 100)], 10)
        self.assertEqual(r["status"], "short")
        self.assertIsNone(r["swap"])
        spools = [spool(1, 100), spool(2, 900, location="Shelf A", first_used="2026-01-01"),
                  spool(3, 400), spool(4, 330, first_used="2026-02-01")]
        self.assertEqual(sp.swap_spool([spools[0]], spools, 330)["id"], 2)
        no_first = [spool(1, 100), spool(3, 900, location="Shelf A"), spool(4, 340), spool(5, 200)]
        self.assertEqual(sp.swap_spool([no_first[0]], no_first, 330)["id"], 4)
        self.assertIsNone(sp.swap_spool([no_first[0]], no_first, 5000))

    def test_swap_sentence_and_cost_dropped_first(self):
        r = {"slot": self.SLOT, "slots": [1], "need": 300, "margin": 10, "pool": 1, "matches": 1, "status": "short",
             "ams": True, "have": 100, "swap": spool(12, 640, location="Shelf A"), "name": "Black"}
        kind, text = sp.plate_notice([r], "About €1.23 of filament.")
        self.assertIn("Swap in spool #12 (Shelf A, 640 g).", text)
        self.assertTrue(text.endswith("About €1.23 of filament."))
        self.assertNotIn("About", sp.fit_text(text, len(text) - 5))

    def test_cost_present_and_absent(self):
        ok = self.check([spool(2, 900)])
        self.assertEqual(ok["status"], "ok")
        self.assertAlmostEqual(ok["cost"], 7.5)
        self.assertEqual(sp.cost_sentence([ok], "EUR"), "About €7.50 of filament.")
        self.assertEqual(sp.cost_sentence([ok], "SEK"), "About SEK 7.50 of filament.")
        unpriced = self.check([{**spool(2, 900), "price": None}])
        self.assertIsNone(unpriced["cost"])
        self.assertEqual(sp.cost_sentence([unpriced], "EUR"), "")
        self.assertIn("About €7.50", sp.plate_notice([ok], "About €7.50 of filament.")[1])
        self.assertNotIn("About", sp.plate_notice([unpriced])[1])

    def test_check_plate_adds_cost(self):
        with mock.patch.object(sp, "spool_key", return_value="k"), \
             mock.patch.object(sp, "plate_spools", return_value=[spool(2, 900)]):
            notice, _ = sp.check_plate([self.SLOT], 10)
        self.assertIn("About €7.50 of filament.", notice[1])


class PageChipTest(unittest.TestCase):
    def test_chip_follows_payload_and_flag(self):
        from test_display import PageScriptTest
        t = PageScriptTest("run_page")
        scenario = """
const base = %s;
disp = Object.assign({}, DISPLAY_DEFAULTS);
const on = listHtml([base[0], base[1]]);
disp = Object.assign({}, DISPLAY_DEFAULTS, {use_first: false, group_same: false});
const off = listHtml([base[0], base[1]]);
console.log(JSON.stringify({on, off, flag: DISPLAY_DEFAULTS.use_first}));
""" % __import__("json").dumps([{**spool(1, 400), "use_first": True}, {**spool(2, 900), "use_first": False}])
        out = t.run_page(scenario)
        self.assertEqual(out["on"].count("Use First"), 1)
        self.assertNotIn("Use First", out["off"])
        self.assertTrue(out["flag"])


if __name__ == "__main__":
    unittest.main()
