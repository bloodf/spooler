import json
import tempfile
import time
import unittest
from pathlib import Path

from plugin_loader import load

sp, orca = load()

DAY = 86400


def row(spool, grams, material="PLA", cost=None):
    return {"spool": spool, "grams": grams, "label": f"Spool {spool}", "material": material,
            "colour": "ff0000", "cost": cost}


def entry(eid, age_days, rows, result="finished"):
    return {"id": eid, "time": time.time() - age_days * DAY, "name": f"print {eid}", "printer": "P1",
            "result": result, "pct": 100, "rows": rows}


class StatsBase(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.old_file, self.old_settings = sp.HISTORY_FILE, sp.get_settings
        sp.HISTORY_FILE = Path(self.dir.name) / "history.json"
        sp.get_settings = lambda: {"stats": {"on": True, "cur": "gbp"}, "spoolman_url": "", "low_stock_grams": 100}
        self.addCleanup(self.restore)

    def restore(self):
        sp.HISTORY_FILE, sp.get_settings = self.old_file, self.old_settings

    def save(self, entries):
        sp.HISTORY_FILE.write_text(json.dumps(entries), encoding="utf-8")


class ParseStatsTest(unittest.TestCase):
    def test_defaults_and_validation(self):
        self.assertEqual(sp.parse_stats(None), {"on": sp.parse_flag(None), "cur": "spoolman"})
        self.assertEqual(sp.parse_stats({"on": False, "cur": "usd"}), {"on": False, "cur": "usd"})
        self.assertEqual(sp.parse_stats({"cur": "jpy"})["cur"], "spoolman")


class StatsDataTest(StatsBase):
    def test_empty_history(self):
        data = sp.stats_data("30")
        self.assertEqual((data["grams"], data["prints"], data["cost"]), (0, 0, None))
        self.assertEqual(data["code"], "GBP")
        self.assertEqual(data["sign"], "£")
        self.assertIsNone(data["since"])
        self.assertEqual(len(data["weeks"]), 8)

    def test_period_filter_and_totals(self):
        self.save([entry("old", 200, [row(1, 50.0, cost=1.0)]),
                   entry("mid", 60, [row(2, 20.0, "PETG", cost=0.5)]),
                   entry("new", 1, [row(1, 10.0, cost=0.2), row(3, 5.0, "PETG")])])
        month, quarter, everything = sp.stats_data("30"), sp.stats_data("90"), sp.stats_data("all")
        self.assertEqual((month["prints"], month["grams"], month["cost"]), (1, 15.0, 0.2))
        self.assertEqual((quarter["prints"], quarter["grams"], quarter["cost"]), (2, 35.0, 0.7))
        self.assertEqual((everything["prints"], everything["grams"], everything["cost"]), (3, 85.0, 1.7))
        self.assertEqual([m["name"] for m in everything["mats"]], ["PLA", "PETG"])
        self.assertEqual(everything["top"][0]["g"], 60.0)
        self.assertEqual([h["name"] for h in everything["history"]], ["print new", "print mid", "print old"])

    def test_this_week_bar(self):
        self.save([entry("new", 0, [row(1, 10.0)])])
        weeks = sp.stats_data("30")["weeks"]
        self.assertTrue(weeks[-1]["now"])
        self.assertEqual(weeks[-1]["parts"][0]["g"], 10.0)

    def test_unknown_period_falls_back_to_30_days(self):
        self.save([entry("old", 60, [row(1, 20.0)])])
        self.assertEqual(sp.stats_data("bogus")["prints"], 0)


class HistNoteTest(StatsBase):
    def booked(self, state="booked", grams=12.0):
        return {"id": "e1", "time": 1000.0, "name": "Benchy", "printer": "P1", "result": "finished", "pct": 100,
                "rows": [{"slot": 0, "spool": 7, "grams": grams, "label": "PLA Red", "material": "PLA",
                          "colour": "ff0000", "state": state}]}

    def test_booked_rows_are_recorded(self):
        sp.hist_note(self.booked(), {})
        saved = sp.hist_load()
        self.assertEqual(len(saved), 1)
        self.assertEqual(saved[0]["rows"][0]["grams"], 12.0)
        self.assertEqual(saved[0]["rows"][0]["spool"], 7)

    def test_rebooking_replaces_and_undo_removes(self):
        sp.hist_note(self.booked(grams=12.0), {})
        sp.hist_note(self.booked(grams=20.0), {})
        self.assertEqual([r["grams"] for r in sp.hist_load()[0]["rows"]], [20.0])
        sp.hist_note(self.booked(state="open"), {})
        self.assertEqual(sp.hist_load(), [])

    def test_unbooked_entry_writes_nothing(self):
        sp.hist_note(self.booked(state="open"), {})
        self.assertFalse(sp.HISTORY_FILE.exists())

    def test_cost_uses_spool_price(self):
        spool = {"id": 7, "price": 25.0, "initial_weight": 1000, "filament": {"material": "PLA", "color_hex": "00ff00"}}
        sp.hist_note(self.booked(grams=100.0), {7: spool})
        saved = sp.hist_load()[0]["rows"][0]
        self.assertEqual(saved["cost"], 2.5)
        self.assertEqual(saved["colour"].lower(), "00ff00")

    def test_unreadable_history_is_empty(self):
        sp.HISTORY_FILE.write_text("not json", encoding="utf-8")
        self.assertEqual(sp.hist_load(), [])


if __name__ == "__main__":
    unittest.main()
