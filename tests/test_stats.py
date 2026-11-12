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


GCODE = """M83
T0
;TYPE:Outer wall
G1 X1 Y1 E6
;TYPE:Support
G1 X2 E2
; FLUSH_START
G1 E1.5
; FLUSH_END
;TYPE:Prime tower
G1 X3 E0.5
T1
;TYPE:Inner wall
G1 X4 E5 ; a comment
G1 X5 E-0.8
G1 X6
M82
G92 E0
;TYPE:Support interface
G1 X7 E5
T255
"""


class WasteTest(StatsBase):
    def test_support_and_purge_share_per_filament(self):
        # T0: 6 model, 2 support, 1.5 flush + 0.5 tower. T1: 5 model, then 5 support (absolute).
        self.assertEqual(sp.parse_waste(GCODE.splitlines()), {1: (0.2, 0.2), 2: (0.5, 0.0)})

    def test_bytes_lines_and_nothing_extruded(self):
        self.assertEqual(sp.parse_waste([b";TYPE:Support\n", b"M83\n", b"G1 E4\n"]), {1: (1.0, 0.0)})
        self.assertEqual(sp.parse_waste(["G1 X1 Y1", "T1"]), {})

    def test_added_to_the_job_items_from_the_plate_gcode(self):
        import io
        import zipfile
        blob = io.BytesIO()
        with zipfile.ZipFile(blob, "w") as box:
            box.writestr("Metadata/plate_1.gcode", "M83\nG1 E1\n")
            box.writestr("Metadata/plate_2.gcode", GCODE)
        items = [{"n": 1}, {"n": 2}, {"n": 3}]
        with zipfile.ZipFile(blob) as box:
            sp.add_waste(items, box, "/cache/plate_2.gcode.3mf")
            self.assertEqual(items, [{"n": 1, "ws": 0.2, "wp": 0.2}, {"n": 2, "ws": 0.5, "wp": 0.0}, {"n": 3}])
            # Two plates and no hint in the file name: which one printed is unknown, so nothing is guessed.
            unknown = [{"n": 1}]
            sp.add_waste(unknown, box, "Benchy.3mf")
            self.assertEqual(unknown, [{"n": 1}])

    def test_history_keeps_the_shares_of_booked_rows(self):
        entry_ = {"id": "e1", "time": 1000.0, "name": "Benchy", "printer": "P1", "result": "finished", "pct": 100,
                  "rows": [{"slot": 0, "spool": 7, "grams": 10.0, "state": "booked", "ws": 0.2, "wp": 0.1},
                           {"slot": 1, "spool": 8, "grams": 5.0, "state": "booked"}]}
        sp.hist_note(entry_, {})
        rows = sp.hist_load()[0]["rows"]
        self.assertEqual((rows[0]["ws"], rows[0]["wp"]), (0.2, 0.1))
        self.assertNotIn("ws", rows[1])

    def test_totals_and_the_most_wasteful_prints(self):
        self.save([entry("a", 1, [dict(row(1, 100.0, cost=2.0), ws=0.2, wp=0.1)]),
                   entry("b", 2, [dict(row(2, 50.0, cost=1.0), ws=0.0, wp=0.5), row(3, 10.0)]),
                   entry("c", 3, [row(1, 40.0, cost=1.0)])])
        data = sp.stats_data("30")
        waste = data["waste"]
        self.assertEqual((waste["support"], waste["purge"], waste["model"]), (20.0, 35.0, 95.0))
        self.assertEqual((waste["scost"], waste["pcost"], waste["mcost"], waste["cost"]), (0.4, 0.7, 1.9, 1.1))
        self.assertEqual(waste["prints"], 2)
        self.assertEqual([(w["name"], w["g"], w["cost"], w["kind"]) for w in data["worst"]],
                         [("print a", 30.0, 0.6, "support"), ("print b", 25.0, 0.5, "purge")])

    def test_history_from_before_the_estimate_has_no_waste(self):
        self.save([entry("a", 1, [row(1, 100.0, cost=2.0)])])
        data = sp.stats_data("30")
        self.assertIsNone(data["waste"])
        self.assertEqual(data["worst"], [])




if __name__ == "__main__":
    unittest.main()
