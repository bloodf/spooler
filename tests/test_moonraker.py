import asyncio
import json
import types
import unittest

from fake_bundle import FIXTURES, SV06, U1
from plugin_loader import load

sp, orca = load()

SPOOLS = json.loads((FIXTURES / "spoolman_spools.json").read_text(encoding="utf-8"))
# Captured from a Snapmaker U1: all four heads hold Snapmaker SnapSpeed PLA with RFID tags,
# and the firmware reports the Spoolman spool in each head (filament_spool_id).
U1_STATUS = json.loads((FIXTURES / "u1_status.json").read_text(encoding="utf-8"))


def u1_status(**changes):
    status = json.loads(json.dumps(U1_STATUS))
    status["print_task_config"].update(changes)
    return status


def names():
    found = {}
    for f in sp.stocked_filaments(SPOOLS):
        found[(f["id"], U1)] = f"{sp.profile_name(f)} @Snapmaker U1"
        found[(f["id"], SV06)] = f"{sp.profile_name(f)} @Sovol SV06"
    return found


class BaseTest(unittest.TestCase):
    def test_moon_base(self):
        self.assertEqual(sp.moon_base("10.25.1.83"), "http://10.25.1.83")
        self.assertEqual(sp.moon_base("u1.lan:7125/"), "http://u1.lan:7125")
        self.assertEqual(sp.moon_base("https://p.example/path"), "https://p.example")
        self.assertEqual(sp.moon_base(""), "")
        self.assertEqual(sp.moon_base("ftp://x"), "")
        self.assertEqual(sp.moon_base("bad host"), "")
        self.assertEqual(sp.moon_base("user:pw@host"), "")

    def test_auto_printers_are_never_saved(self):
        self.assertEqual(sp.parse_printers([{"id": "auto-x", "auto": True, "name": "U1"}]), [])


class U1Test(unittest.TestCase):
    def setUp(self):
        sp._profiles["names"] = names()

    def trays(self, status, spools=SPOOLS):
        doc, heads = sp.moon_report(status, None, spools, U1)
        self.assertTrue(heads)
        return doc["print"]["ams"]["ams"][0]["tray"]

    def test_heads_use_the_spool_id_the_printer_reports(self):
        trays = self.trays(U1_STATUS)
        self.assertEqual([t["spool_id"] for t in trays], [3, 4, 6, 5])
        self.assertEqual(trays[0]["profile"], "_local/spooler/Snapmaker PLA SnapSpeed Yellow @Snapmaker U1")
        self.assertEqual(trays[0]["tray_color"], "F4C032FF")
        self.assertEqual(trays[0]["tag_uid"], "60827A6A")
        spool = next(s for s in SPOOLS if s["id"] == 3)
        self.assertAlmostEqual(trays[0]["remain"], spool["remaining_weight"] / spool["initial_weight"] * 100)

    def test_rfid_tag_when_no_spool_id(self):
        trays = self.trays(u1_status(filament_spool_id=[0, 0, 0, 0]))
        self.assertEqual([t["spool_id"] for t in trays], [3, 4, 6, 5])

    def test_colour_when_no_id_or_tag(self):
        status = u1_status(filament_spool_id=[0, 0, 0, 0])
        status["filament_detect"] = {"info": [{}, {}, {}, {}]}
        trays = self.trays(status)
        # Yellow F4C032 only matches the yellow SnapSpeed spool.
        self.assertEqual(trays[0]["spool_id"], 3)

    def test_unknown_spool_id_falls_back(self):
        trays = self.trays(u1_status(filament_spool_id=[999, 4, 6, 5]))
        self.assertEqual(trays[0]["spool_id"], 3)

    def test_empty_head(self):
        trays = self.trays(u1_status(filament_exist=[True, False, True, True]))
        self.assertEqual(trays[1], {"id": "1"})

    def test_nothing_in_spoolman(self):
        status = u1_status(filament_spool_id=[0, 0, 0, 0])
        status["filament_detect"] = {"info": [{}, {}, {}, {}]}
        trays = self.trays(status, spools=[])
        self.assertIsNone(trays[3]["spool_id"])
        self.assertEqual(trays[3]["tray_sub_brands"], "Snapmaker PLA SnapSpeed")
        self.assertEqual(trays[3]["profile"], "")

    def test_live_state_shows_heads(self):
        doc, heads = sp.moon_report(U1_STATUS, None, SPOOLS, U1)
        sp._live["printers"].clear()
        sp.live_apply("auto-u1", "U1", doc, link="auto-u1")
        sp._live["printers"]["auto-u1"]["heads"] = heads
        snap = sp.live_snapshot()["printers"][0]
        self.assertTrue(snap["heads"])
        trays = snap["units"][0]["trays"]
        self.assertEqual([t["spool"] for t in trays], [3, 4, 6, 5])
        self.assertTrue(trays[0]["rfid"])
        self.assertTrue(trays[0]["profile"].endswith("@Snapmaker U1"))
        # A head emptied later is cleared, not left stale.
        doc, _ = sp.moon_report(u1_status(filament_exist=[False, True, True, True]), None, SPOOLS, U1)
        sp.live_apply("auto-u1", "U1", doc, link="auto-u1")
        self.assertTrue(sp.live_snapshot()["printers"][0]["units"][0]["trays"][0]["empty"])
        sp._live["printers"].clear()


class SingleTest(unittest.TestCase):
    def setUp(self):
        sp._profiles["names"] = names()

    def test_active_spool(self):
        doc, heads = sp.moon_report({}, 6, SPOOLS, SV06)
        self.assertFalse(heads)
        ext = doc["print"]["vt_tray"]
        self.assertEqual(ext["spool_id"], 6)
        self.assertEqual(ext["tray_color"], "E2DEDBFF")
        self.assertEqual(ext["profile"], "_local/spooler/Snapmaker PLA SnapSpeed White @Sovol SV06")

    def test_no_active_spool(self):
        doc, _ = sp.moon_report({}, None, SPOOLS, SV06)
        self.assertEqual(doc["print"]["vt_tray"], {"id": "254"})


def lane(index, spool_id=None, material="PLA", colour="", vendor="", name=""):
    """One lane_data entry, shaped like the ones AFC writes."""
    return {"color": colour, "material": material, "vendor_name": vendor, "name": name, "bed_temp": 60,
            "nozzle_temp": 220, "scan_time": "", "td": "", "lane": str(index), "extruder_index": 0,
            "spool_id": spool_id, "weight": 500.0, "initial_weight": 1000.0}


# T2 is empty; T3 reports no spool id, so it is matched by vendor, material and colour.
LANES = {"T0": lane(0, 3, colour="#F4C032", vendor="Snapmaker", name="PLA SnapSpeed Yellow"),
         "T1": lane(1, 4, colour="#E72F1D", vendor="Snapmaker", name="PLA SnapSpeed Red"),
         "T2": lane(2, material=""),
         "T3": lane(3, colour="#E2DEDB", vendor="Snapmaker", name="PLA SnapSpeed White")}


class LaneTest(unittest.TestCase):
    def setUp(self):
        sp._profiles["names"] = names()

    def units(self, lanes):
        doc, heads = sp.moon_report({}, 18, SPOOLS, U1, lanes)
        self.assertFalse(heads)
        self.assertNotIn("vt_tray", doc["print"])
        return doc["print"]["ams"]["ams"]

    def test_lanes_use_the_spool_id_each_lane_reports(self):
        units = self.units(LANES)
        self.assertEqual(len(units), 1)
        trays = units[0]["tray"]
        self.assertEqual([t.get("spool_id") for t in trays], [3, 4, None, 6])
        self.assertEqual(trays[2], {"id": "2"})
        self.assertEqual(trays[0]["tray_color"], "F4C032FF")
        self.assertEqual(trays[0]["profile"], "_local/spooler/Snapmaker PLA SnapSpeed Yellow @Snapmaker U1")

    def test_unknown_spool_id_matches_by_colour(self):
        trays = self.units({"T0": lane(0, 999, colour="#F4C032", vendor="Snapmaker")})[0]["tray"]
        self.assertEqual(trays[0]["spool_id"], 3)

    def test_unmatched_lane_keeps_what_the_printer_says(self):
        trays = self.units({"T0": lane(0, material="TPU", colour="#123456", vendor="Acme")})[0]["tray"]
        self.assertEqual((trays[0]["spool_id"], trays[0]["profile"]), (None, ""))
        self.assertEqual((trays[0]["tray_type"], trays[0]["tray_color"]), ("TPU", "123456FF"))
        self.assertEqual(trays[0]["tray_sub_brands"], "Acme TPU")

    def test_four_lanes_per_unit(self):
        units = self.units({"T5": lane(5, 34, colour="#FFFF00", vendor="3D Procer")})
        self.assertEqual([u["id"] for u in units], ["0", "1"])
        self.assertEqual(units[0]["tray"], [{"id": str(i)} for i in range(4)])
        self.assertEqual(units[1]["tray"][1]["id"], "1")
        self.assertEqual(units[1]["tray"][1]["spool_id"], 34)

    def test_live_state_shows_lanes(self):
        doc, _ = sp.moon_report({}, None, SPOOLS, U1, LANES)
        sp._live["printers"].clear()
        sp.live_apply("auto-cc", "Centauri", doc, link="auto-cc")
        snap = sp.live_snapshot()["printers"][0]
        sp._live["printers"].clear()
        self.assertFalse(snap["heads"])
        trays = snap["units"][0]["trays"]
        self.assertEqual([t["spool"] for t in trays], [3, 4, None, 6])
        self.assertTrue(trays[2]["empty"])


class LanePollTest(unittest.TestCase):
    def setUp(self):
        self.original = sp._moon_get
        sp._spool_cache["spools"] = SPOOLS

    def tearDown(self):
        sp._moon_get = self.original
        sp._spool_cache["spools"] = []

    def answer(self, lanes, status=None):
        # Current Moonraker answers {} for objects the printer doesn't have, older ones leave them out.
        status = {"print_task_config": {}, "filament_detect": {}} if status is None else status

        def get(base, path):
            if "lane_data" in path:
                if lanes is None:
                    raise sp.urllib.error.HTTPError(base + path, 404, "Namespace 'lane_data' not found", {}, None)
                return {"namespace": "lane_data", "key": None, "value": lanes}
            if path == "/server/spoolman/spool_id":
                return {"spool_id": 6}
            return {"status": status}

        sp._moon_get = get

    def test_lanes_before_moonrakers_active_spool(self):
        self.answer(LANES)
        doc, heads = sp.moon_poll("http://cc")
        self.assertFalse(heads)
        self.assertEqual([t.get("spool_id") for t in doc["print"]["ams"]["ams"][0]["tray"]], [3, 4, None, 6])

    def test_no_lane_data_uses_the_active_spool(self):
        for status in (None, {}):
            self.answer(None, status)
            doc, _ = sp.moon_poll("http://sv06")
            self.assertEqual(doc["print"]["vt_tray"]["spool_id"], 6)

    def test_lane_data_without_lanes_uses_the_active_spool(self):
        self.answer({"x": {"material": "PLA", "color": "#FFFFFF"}})
        doc, _ = sp.moon_poll("http://cc")
        self.assertEqual(doc["print"]["vt_tray"]["spool_id"], 6)
        self.assertEqual([t.get("spool_id") for t in sp.printer_trays("http://cc")], [6])

    def test_printer_trays_in_slot_order_across_units(self):
        self.answer({"a": lane(0, 3, colour="#F4C032"), "b": lane(5, 34, colour="#FFFF00")})
        trays = sp.printer_trays("http://cc")
        self.assertEqual(len(trays), 8)
        self.assertEqual((trays[0]["spool_id"], trays[5]["spool_id"]), (3, 34))


class ProbeTest(unittest.TestCase):
    def test_is_moonraker(self):
        original = sp._moon_get
        try:
            sp._moon_get = lambda base, path: {"klippy_state": "ready"}
            self.assertTrue(sp.is_moonraker("http://x"))
            sp._moon_get = lambda base, path: {"name": "PrusaLink"}
            self.assertFalse(sp.is_moonraker("http://x"))

            def missing(base, path):
                raise sp.urllib.error.HTTPError(base + path, 404, "Not Found", {}, None)

            sp._moon_get = missing
            self.assertFalse(sp.is_moonraker("http://x"))
        finally:
            sp._moon_get = original

    def test_not_moonraker_printers_are_hidden(self):
        sp._auto_printers[:] = [{"id": "auto-a", "name": "A", "units": [], "ip": "http://a",
                                 "serial": "", "kind": "moonraker", "auto": True}]
        sp._live["links"]["auto-a"] = "none"
        try:
            self.assertEqual(sp.printer_state()["printers"], [])
        finally:
            sp._live["links"].pop("auto-a")
            sp._auto_printers.clear()


class LoadTest(unittest.TestCase):
    def setUp(self):
        self.originals = (sp.get_spools, sp.profile_sync, sp.moon_poll)
        sp._ui_snap.clear()
        sp._ui_snap.update(printers=[{"target": U1, "label": "Snapmaker U1", "hosts": ["http://u1"]}])

    def tearDown(self):
        sp.get_spools, sp.profile_sync, sp.moon_poll = self.originals
        sp._ui_snap.clear()

    def test_load_selects_profiles(self):
        calls = []

        class Tx:
            def __init__(self, slot, name):
                calls.append((slot, name))

            def commit(self):
                if calls[-1][0] == 2:
                    raise ValueError("bad")

        orca.host.preset.filament = types.SimpleNamespace(begin_update=Tx)
        sp.get_spools = lambda url: {"ok": True, "spools": SPOOLS}
        sp.profile_sync = lambda spools, snap: {"error": "", "names": names()}
        sp._profiles["names"] = names()
        status = u1_status(filament_exist=[True, True, True, False])
        sp.moon_poll = lambda base: sp.moon_report(status, None, SPOOLS, U1)
        text = sp.load_printer_filaments({"host": "http://u1", "slots": 4, "names": set()})
        self.assertEqual([c[0] for c in calls], [1, 2, 3])
        self.assertTrue(calls[0][1].endswith("Snapmaker PLA SnapSpeed Yellow @Snapmaker U1"))
        self.assertIn("Loaded 2 filament", text)
        self.assertIn("Could not change slot(s) 2", text)

    def test_needs_snapshot_and_host(self):
        with self.assertRaises(RuntimeError):
            sp.load_printer_filaments({})
        with self.assertRaises(RuntimeError):
            sp.load_printer_filaments({"host": "", "slots": 1, "names": set()})


TRAYS = [{"profile": "_local/spooler/A", "tray_type": "PLA", "spool_id": 3},
         {"profile": "_local/spooler/B", "tray_type": "PLA", "spool_id": 4},
         {"id": "2"},
         {"profile": "_local/spooler/C", "tray_type": "PLA", "spool_id": 6}]
NAMES = {"_local/spooler/A", "_local/spooler/B", "_local/spooler/C", "_local/spooler/D"}
GENERIC = ("Generic PLA @System", True)
IN_SYNC = [("_local/spooler/A", False), ("_local/spooler/B", False), GENERIC, ("_local/spooler/C", False)]


class KeepPlanTest(unittest.TestCase):
    def setUp(self):
        self.seen = {}

    def plan(self, current, gen=1, trays=TRAYS):
        return sp.keep_plan(trays, 4, NAMES, current, gen, self.seen)

    def test_first_pass_assigns_every_lane(self):
        self.assertEqual(self.plan([GENERIC] * 4),
                         [(1, "_local/spooler/A"), (2, "_local/spooler/B"), (4, "_local/spooler/C")])

    def test_slots_already_right_are_left_alone(self):
        self.assertEqual(self.plan(IN_SYNC), [])
        self.assertEqual(self.plan(IN_SYNC, gen=2), [])

    def test_lane_change_reassigns_even_a_user_preset(self):
        self.plan(IN_SYNC)
        trays = [dict(TRAYS[0]), dict(TRAYS[1], spool_id=5, profile="_local/spooler/D"), TRAYS[2], TRAYS[3]]
        current = [IN_SYNC[0], ("My PLA", False), IN_SYNC[2], IN_SYNC[3]]
        self.assertEqual(self.plan(current, gen=2, trays=trays), [(2, "_local/spooler/D")])

    def test_generic_preset_from_orca_sync_is_replaced_once(self):
        self.plan(IN_SYNC)
        current = [GENERIC] + IN_SYNC[1:]
        self.assertEqual(self.plan(current, gen=2), [(1, "_local/spooler/A")])
        # The same snapshot again (OrcaSlicer hasn't reported the change): no second try.
        self.assertEqual(self.plan(current, gen=2), [])

    def test_user_preset_is_kept(self):
        self.plan(IN_SYNC)
        self.assertEqual(self.plan([("My PLA", False)] + IN_SYNC[1:], gen=2), [])


class KeepRunTest(unittest.TestCase):
    def setUp(self):
        self.originals = (sp.sync_for, sp.printer_trays, sp.MOON_POLL)
        self.calls = []
        self.slots = [GENERIC] * 4
        test = self

        class Tx:
            def __init__(self, slot, name):
                test.calls.append((slot, name))
                self.slot, self.name = slot, name
                # OrcaSlicer fires PresetSelected, refreshing the snapshot, before this slot changes.
                sp._ui_snap.update(current=list(test.slots), gen=sp._ui_snap["gen"] + 1)

            def commit(self):
                test.slots[self.slot - 1] = (self.name, False)

        orca.host.preset.filament = types.SimpleNamespace(begin_update=Tx)
        sp.sync_for = lambda snap: NAMES
        sp.printer_trays = lambda base: TRAYS
        sp.MOON_POLL = 0.01
        sp._ui_snap.clear()
        sp._ui_snap.update(host="http://cc", slots=4, names=set(), current=[GENERIC] * 4, gen=1)

    def tearDown(self):
        sp.sync_for, sp.printer_trays, sp.MOON_POLL = self.originals
        sp._ui_snap.clear()

    def test_running_it_again_stops_it(self):
        async def scenario():
            first = asyncio.ensure_future(sp.SpoolerKeepSlots().execute())
            await asyncio.sleep(0.1)
            stopped = await sp.SpoolerKeepSlots().execute()
            return stopped, await asyncio.wait_for(first, 1)

        stopped, ended = asyncio.run(scenario())
        # Several passes ran, but each lane was assigned once.
        self.assertEqual(self.calls, [(1, "_local/spooler/A"), (2, "_local/spooler/B"), (4, "_local/spooler/C")])
        self.assertEqual(stopped[0], "success")
        self.assertEqual(ended[0], "success")

    def test_not_ready_fails_at_once(self):
        def not_ready(snap):
            raise RuntimeError("The selected printer preset has no host address.")

        sp.sync_for = not_ready
        result = asyncio.run(sp.SpoolerKeepSlots().execute())
        self.assertEqual(result[0], "failure")
        self.assertIsNone(sp._keep["run"])


class PlanTest(unittest.TestCase):
    def test_plan(self):
        trays = [{"profile": "_local/spooler/A", "tray_type": "PLA"},
                 {"profile": "", "tray_type": "PLA"},
                 {"id": "2"},
                 {"profile": "_local/spooler/B", "tray_type": "PLA"}]
        plan, missing = sp.slot_plan(trays, 3, {"_local/spooler/A", "B"})
        self.assertEqual(plan, [(1, "_local/spooler/A")])
        self.assertEqual(missing, [2])
        plan, _ = sp.slot_plan(trays, 4, {"_local/spooler/A", "B"})
        self.assertEqual(plan[-1], (4, "B"))


if __name__ == "__main__":
    unittest.main()
