import csv
import time
import unittest
from pathlib import Path
from unittest import mock

from test_stats import StatsBase, entry, row, sp


class RateAndDetailTest(StatsBase):
    def test_weekly_rates_use_the_last_four_weeks(self):
        hist = [entry("a", 3, [row(1, 40.0)]), entry("b", 20, [row(1, 40.0), row(2, 8.0)]), entry("c", 40, [row(1, 99.0)])]
        self.assertEqual(sp.weekly_rates(hist, time.time()), {1: 20.0, 2: 2.0})

    def test_detail_payload(self):
        self.save([entry("b", 20, [row(1, 40.0, cost=1.5), row(2, 8.0)]), entry("a", 3, [row(1, 40.0, cost=1.0)])])
        out = sp.spool_detail(1)
        self.assertEqual([p["grams"] for p in out["prints"]], [40.0, 40.0])
        self.assertEqual((out["grams"], out["cost"], out["rate"], out["weeks"]), (80.0, 2.5, 20.0, None))
        self.assertEqual(out["prints"][0]["name"], "print a")

    def test_weeks_left_from_remaining_weight(self):
        self.save([entry("a", 3, [row(1, 40.0)])])
        sp.get_settings = lambda: {"stats": {"on": True, "cur": "gbp"}, "spoolman_url": "http://x", "low_stock_grams": 100}
        with mock.patch.object(sp, "plate_spools", return_value=[{"id": 1, "remaining_weight": 100}]):
            self.assertEqual(sp.spool_detail(1)["weeks"], 10.0)

    def test_no_history_and_bad_id(self):
        out = sp.spool_detail(5)
        self.assertEqual((out["prints"], out["rate"], out["weeks"], out["cost"]), ([], None, None, None))
        self.assertEqual(sp.spool_detail("x")["prints"], [])


class ExportTest(StatsBase):
    def setUp(self):
        super().setUp()
        self.data = Path(self.dir.name)
        patcher = mock.patch.object(sp, "DATA_DIR", self.data)
        patcher.start()
        self.addCleanup(patcher.stop)
        opener = mock.patch.object(sp, "open_url", return_value=True)
        self.opened = opener.start()
        self.addCleanup(opener.stop)

    def read(self, result):
        with open(result["path"], encoding="utf-8-sig", newline="") as fh:
            return list(csv.reader(fh))

    def test_rows_bom_and_open(self):
        e = entry("a", 1, [{**row(1, 10.0, cost=0.5), "ws": 0.1, "wp": 0.2}, row(2, 5.0, "PETG")], "cancelled")
        e["pct"] = 40
        self.save([e])
        res = sp.export_history("30")
        self.assertTrue(res["ok"])
        self.assertTrue(Path(res["path"]).read_bytes().startswith(b"\xef\xbb\xbf"))
        self.assertRegex(Path(res["path"]).name, r"^history-\d{8}-\d{4}\.csv$")
        rows = self.read(res)
        self.assertEqual(len(rows), 3)
        self.assertEqual(rows[1][1:], ["print a", "P1", "cancelled", "40", "1", "Spool 1", "PLA", "ff0000", "10.0", "0.5", "1.0", "2.0"])
        self.assertEqual(rows[2][-3:], ["", "", ""])
        self.opened.assert_called_once_with((self.data / "exports").as_uri())
        self.assertIn(res["path"], res["text"])

    def test_period_respected(self):
        self.save([entry("old", 200, [row(1, 1.0)]), entry("new", 1, [row(2, 2.0)])])
        self.assertEqual(len(self.read(sp.export_history("30"))), 2)
        self.assertEqual(len(self.read(sp.export_history("all"))), 3)

    def test_formula_cells_escaped(self):
        e = entry("a", 1, [{**row(1, 1.0), "label": "=SUM(A1)", "material": "@x"}])
        e["name"] = "-cmd"
        self.save([e])
        rows = self.read(sp.export_history("30"))
        self.assertEqual((rows[1][1], rows[1][6], rows[1][7]), ("'-cmd", "'=SUM(A1)", "'@x"))


class TotalsTest(StatsBase):
    def test_failed_totals_in_period(self):
        self.save([entry("f", 1, [row(1, 10.0, cost=0.5)], "cancelled"), entry("ok", 1, [row(1, 99.0)]),
                   entry("old", 200, [row(1, 50.0)], "cancelled")])
        self.assertEqual(sp.stats_data("30")["failed"], {"prints": 1, "g": 10.0, "cost": 0.5})
        self.assertEqual(sp.stats_data("all")["failed"]["prints"], 2)
        self.assertIsNone(sp.stats_data("30")["shelf"])

    def test_inventory_value(self):
        sp.get_settings = lambda: {"stats": {"on": True, "cur": "gbp"}, "spoolman_url": "http://x", "low_stock_grams": 100}
        spools = [
            {"id": 1, "remaining_weight": 500, "initial_weight": 1000, "price": 20.0, "filament": {"material": "PLA"}},
            {"id": 2, "remaining_weight": 250, "initial_weight": 1000, "price": 40.0, "filament": {"material": "PETG"}},
            {"id": 3, "remaining_weight": 100, "filament": {"material": "PLA"}},
            {"id": 4, "remaining_weight": 900, "initial_weight": 1000, "price": 20.0, "archived": True, "filament": {"material": "PLA"}},
        ]
        with mock.patch.object(sp, "plate_spools", return_value=spools):
            shelf = sp.stats_data("30")["shelf"]
        self.assertEqual((shelf["g"], shelf["value"], shelf["unpriced"]), (850.0, 20.0, 1))
        self.assertEqual(shelf["mats"], [{"name": "PLA", "g": 600.0, "value": 10.0}, {"name": "PETG", "g": 250.0, "value": 10.0}])


# Borrows the page runner only; subclassing PageScriptTest would run all its tests again here.


if __name__ == "__main__":
    unittest.main()
