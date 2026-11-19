"""Klipper printers found from the presets: toolheads (extruder ... extruder7) and MMU gates set by hand,
slice fill for them, the pick when a filament matches several spools, and the preset-to-printer choice.
Moonraker is mocked; nothing here talks to a printer."""

import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()


def spool(sid, material, colour, name):
    return {"id": sid, "remaining_weight": 500.0, "initial_weight": 1000.0,
            "filament": {"id": 100 + sid, "name": name, "material": material, "color_hex": colour, "vendor": {"name": "Acme"}}}


SPOOLS = [spool(1, "PLA", "FF0000", "Red PLA"), spool(2, "PETG", "0000FF", "Blue PETG"),
          spool(3, "PETG", "0000FF", "Blue PETG"), spool(4, "ABS", "00FF00", "Green ABS")]
BASE = "http://10.0.0.9"
PID = "auto-10-0-0-9"
AUTO = {"id": PID, "name": "Voron", "units": [], "ip": BASE, "serial": "", "kind": "moonraker", "auto": True}


def extruders(n):
    return {name: ({"temperature": 25.0} if i < n else {}) for i, name in enumerate(sp.MOON_EXTRUDERS)}


class KlipperCase(unittest.TestCase):
    """A Klipper printer at BASE found from a preset, settings in memory, Spoolman as the source."""

    def store(self, settings: dict) -> bool:
        self.settings = settings  # what was written is what is read next
        return True

    def setUp(self):
        self.settings = {"printers": {"spoolman": []}}
        self.paths = []
        patches = [mock.patch.object(sp, "get_settings", lambda: self.settings),
                   mock.patch.object(sp, "save_settings", self.store),
                   mock.patch.object(sp, "source", return_value="spoolman"),
                   mock.patch.object(sp, "prune_codes"), mock.patch.object(sp, "_local_sync")]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)
        sp._auto_printers[:] = [dict(AUTO)]
        sp._moon_found.clear()
        sp._slice_picks.clear()
        sp._spool_cache["spools"] = SPOOLS
        self.addCleanup(sp._auto_printers.clear)
        self.addCleanup(sp._moon_found.clear)
        self.addCleanup(sp._slice_picks.clear)
        self.addCleanup(sp._spool_cache.__setitem__, "spools", [])

    def moonraker(self, status, lanes=None, active=None):
        """Mock Moonraker: printer objects status, the lane_data namespace (None: absent), the active spool."""
        def get(base, path):
            self.paths.append(path)
            if "lane_data" in path:
                if lanes is None:
                    raise sp.urllib.error.HTTPError(base + path, 404, "Namespace 'lane_data' not found", {}, None)
                return {"namespace": "lane_data", "key": None, "value": lanes}
            if path == "/server/spoolman/spool_id":
                return {"spool_id": active}
            return {"status": status}
        patch = mock.patch.object(sp, "_moon_get", get)
        patch.start()
        self.addCleanup(patch.stop)

    def assign(self, tools=(), gates=(), slice_fill=True):
        self.settings["moon_slots"] = {"spoolman": {PID: {"tools": list(tools), "gates": list(gates), "slice_fill": slice_fill}}}

    def entry(self):
        return next(p for p in sp.printers_cfg() if p["id"] == PID)


class PollTest(KlipperCase):
    def test_query_asks_for_every_extruder_and_nothing_else_is_sent(self):
        self.moonraker(extruders(1), active=None)
        sp.moon_poll(BASE)
        query = self.paths[0]
        self.assertTrue(query.startswith("/printer/objects/query?"))
        for name in ("extruder=temperature", "extruder1=temperature", "extruder7=temperature"):
            self.assertIn(name, query)
        self.assertNotIn("gcode", query.lower())

    def test_single_extruder_keeps_moonrakers_active_spool(self):
        self.moonraker(extruders(1), active=4)
        doc, heads = sp.moon_poll(BASE)
        self.assertFalse(heads)
        self.assertEqual(doc["print"]["vt_tray"]["spool_id"], 4)
        self.assertEqual(sp._moon_found[PID], {"tools": 1, "managed": False, "u1": False, "hh": False, "solo": False})
        self.assertEqual(self.entry()["units"], [])

    def moonraker_without_spoolman(self, status):
        """Moonraker with no [spoolman] section: its active-spool endpoint answers 404."""
        def get(base, path):
            if "lane_data" in path or path == "/server/spoolman/spool_id":
                raise sp.urllib.error.HTTPError(base + path, 404, "Not Found", {}, None)
            return {"status": status}
        patch = mock.patch.object(sp, "_moon_get", get)
        patch.start()
        self.addCleanup(patch.stop)

    def test_single_extruder_without_moonraker_spoolman_gets_one_extruder_slot_set_by_hand(self):
        # A Sovol SV06: one extruder, no MMU, no Spoolman in Moonraker. One slot to assign, never a wait for slots.
        self.moonraker_without_spoolman(extruders(1))
        sp.moon_poll(BASE)
        self.assertEqual(self.entry()["units"], [{"kind": "tool", "slots": [None]}])
        self.assign(tools=[4])
        doc, heads = sp.moon_poll(BASE)
        self.assertTrue(heads)
        self.assertNotIn("vt_tray", doc["print"])
        self.assertEqual([t.get("spool_id") for t in doc["print"]["ams"]["ams"][0]["tray"]], [4])
        self.assertFalse(doc["hh"])
        # Gates set by hand replace the extruder slot.
        self.assign(gates=[None, None])
        self.assertEqual(self.entry()["units"], [{"kind": "gate", "slots": [None, None]}])

    def test_happy_hare_installed_with_no_gates_is_no_mmu(self):
        self.moonraker_without_spoolman({**extruders(1), "mmu": {"enabled": False, "num_gates": 0}})
        doc, _ = sp.moon_poll(BASE)
        self.assertFalse(doc["hh"])
        self.assertFalse(self.entry()["managed"])
        self.assertEqual(self.entry()["units"], [{"kind": "tool", "slots": [None]}])
        self.assertFalse(sp.mmu_present({}))
        self.assertTrue(sp.mmu_present({"num_gates": 4}))
        self.assertTrue(sp.mmu_present({"enabled": True}))

    def test_four_extruders_show_toolheads_set_by_hand(self):
        self.assign(tools=["1", None, "4"])
        self.moonraker(extruders(4), active=2)
        doc, heads = sp.moon_poll(BASE)
        self.assertTrue(heads)
        self.assertNotIn("vt_tray", doc["print"])  # the toolheads stand in for the active spool
        trays = doc["print"]["ams"]["ams"][0]["tray"]
        self.assertEqual([t.get("spool_id") for t in trays], [1, None, 4, None])
        self.assertFalse(doc["u1"])  # booked like any Klipper printer, not left to u1control
        self.assertEqual([u["kind"] for u in self.entry()["units"]], ["tool"] * 4)

    def test_eight_extruders_at_most(self):
        self.moonraker(extruders(8))
        sp.moon_poll(BASE)
        self.assertEqual(len(self.entry()["units"]), 8)

    def test_gates_set_by_hand_in_units_of_four(self):
        self.assign(gates=["1", None, None, None, "3", None])
        self.moonraker(extruders(1), active=4)
        doc, heads = sp.moon_poll(BASE)
        self.assertFalse(heads)
        self.assertNotIn("vt_tray", doc["print"])
        units = doc["print"]["ams"]["ams"]
        self.assertEqual([[t.get("spool_id") for t in u["tray"]] for u in units], [[1, None, None, None], [3, None]])

    def test_happy_hare_lane_data_wins_over_gates_set_by_hand(self):
        self.assign(gates=["1", "2"])
        lanes = {"lane0": {"lane": 0, "material": "PETG", "color": "#0000FF", "spool_id": 3}}
        self.moonraker(extruders(1), lanes=lanes)
        doc, _ = sp.moon_poll(BASE)
        self.assertEqual(doc["print"]["ams"]["ams"][0]["tray"][0]["spool_id"], 3)
        self.assertTrue(sp._moon_found[PID]["managed"])
        self.assertEqual(self.entry()["units"], [])  # read-only: nothing to set by hand
        self.assertTrue(self.entry()["managed"])

    def test_u1_unchanged(self):
        self.assign(tools=["1", "2", "3", "4"])
        status = {"print_task_config": {"filament_exist": [True, False], "filament_type": ["PLA", ""],
                                        "filament_color_rgba": ["FF0000FF", ""], "filament_spool_id": [4, 0]},
                  **extruders(2)}
        self.moonraker(status)
        doc, heads = sp.moon_poll(BASE)
        self.assertTrue(heads and doc["u1"])
        self.assertEqual([t.get("spool_id") for t in doc["print"]["ams"]["ams"][0]["tray"]], [4, None])

    def test_u1_stays_read_only_after_an_empty_answer(self):
        self.assign(tools=["1", "2", "3", "4"])
        u1 = {"print_task_config": {"filament_exist": [True] * 4, "filament_type": ["PLA"] * 4,
                                    "filament_color_rgba": ["FF0000FF"] * 4}, **extruders(4)}
        self.moonraker(u1)
        sp.moon_poll(BASE)
        patch = mock.patch.object(sp, "_moon_get", lambda base, path: {"status": {}} if "objects" in path else {})
        patch.start()
        self.addCleanup(patch.stop)
        doc, _ = sp.moon_poll(BASE)
        self.assertTrue(doc["u1"])  # book_ok stays off: u1control books the U1
        self.assertTrue(self.entry()["managed"])
        self.assertEqual(self.entry()["units"], [])
        self.assertEqual(sp.fill_printers(sp.printers_cfg()), [])

    def test_lane_data_printer_stays_read_only_when_lanes_go_missing(self):
        self.assign(gates=["1"])
        self.moonraker(extruders(1), lanes={"l": {"lane": 0, "material": "PLA", "color": "#FF0000"}})
        sp.moon_poll(BASE)
        patch = mock.patch.object(sp, "moon_lanes", return_value={})
        patch.start()
        self.addCleanup(patch.stop)
        sp.moon_poll(BASE)
        self.assertTrue(self.entry()["managed"])

    def test_happy_hare_mmu_object_is_read_only_without_lane_data(self):
        self.assign(gates=["1", "2"])
        mmu = {"num_gates": 5, "gate_status": [1, 0, 1, -1, 1], "gate_material": ["PETG", "", "ABS", "PLA", ""],
               "gate_color": ["0000FF", "", "00ff00", "FF0000", ""], "gate_spool_id": [3, -1, -1, -1, -1],
               "gate_filament_name": ["Blue PETG", "", "", "", ""]}
        self.moonraker({**extruders(1), "mmu": mmu}, lanes=None, active=4)
        doc, heads = sp.moon_poll(BASE)
        self.assertIn("mmu=num_gates,gate_status", self.paths[0])
        self.assertFalse(heads)
        self.assertTrue(doc["hh"])
        self.assertNotIn("vt_tray", doc["print"])
        units = doc["print"]["ams"]["ams"]
        self.assertEqual([[t.get("spool_id") for t in u["tray"]] for u in units], [[3, None, 4, 1], [None]])
        self.assertEqual(units[0]["tray"][1], {"id": "1"})  # reported empty
        entry = self.entry()
        self.assertTrue(entry["managed"])
        self.assertEqual(entry["units"], [])  # no hand-set gates
        self.assertEqual(sp.fill_printers(sp.printers_cfg()), [])  # never filled from a slice
        with sp._live_lock:
            sp.moon_mark(PID, doc, heads)

    def test_happy_hare_without_gate_data_still_read_only(self):
        self.moonraker({**extruders(1), "mmu": {"enabled": True}})
        doc, _ = sp.moon_poll(BASE)
        self.assertTrue(doc["hh"] and self.entry()["managed"])
        self.assertEqual(doc["print"]["ams"]["ams"], [])
        # A later empty answer doesn't turn it into a printer to book here.
        patch = mock.patch.object(sp, "_moon_get", lambda base, path: {"status": {}} if "objects" in path else {})
        patch.start()
        self.addCleanup(patch.stop)
        doc, _ = sp.moon_poll(BASE)
        self.assertTrue(doc["hh"])

    def test_managed_printer_never_shows_the_active_spool(self):
        self.moonraker({**extruders(1), "mmu": {"num_gates": 1, "gate_status": [1], "gate_material": ["PLA"]}}, active=4)
        sp.moon_poll(BASE)
        self.moonraker({}, active=4)  # one empty answer
        doc, heads = sp.moon_poll(BASE)
        self.assertNotIn("vt_tray", doc["print"])
        sp.live_apply(PID, "Voron", doc, link=PID, full=True)
        with sp._live_lock:
            sp.moon_mark(PID, doc, heads)
        self.addCleanup(sp._live["printers"].pop, PID, None)
        self.assertFalse(next(p for p in sp.live_snapshot()["printers"] if p["id"] == PID)["spool_set"])

    def test_no_active_spool_post_to_a_managed_printer_on_an_empty_poll(self):
        sp._local[PID] = {"link": {"kind": "moonraker", "ip": BASE, "name": "Voron"}, "stop": None, "thread": None}
        self.addCleanup(sp._local.pop, PID, None)
        self.addCleanup(sp._live["printers"].pop, PID, None)
        for found in ({"tools": 4, "managed": True, "u1": True, "hh": False},     # Snapmaker U1
                      {"tools": 1, "managed": True, "u1": False, "hh": False},    # lane_data
                      {"tools": 1, "managed": True, "u1": False, "hh": True}):    # Happy Hare
            sp._moon_found[PID] = found
            sp._live["printers"][PID] = {"spool_set": True}  # the page saw a single-extruder card
            self.moonraker({}, lanes=None, active=None)  # one empty answer: it looks single-extruder
            posted = []
            with mock.patch.object(sp, "_moon_post", side_effect=lambda *a: posted.append(a) or {}), \
                 mock.patch.object(sp, "live_apply"):
                result = sp.moon_set_spool(PID, 1)
            self.assertFalse(result["ok"], found)
            self.assertEqual(posted, [], found)

    def test_found_change_reaches_the_page(self):
        self.moonraker(extruders(2))
        before = sp._printers_rev["n"]
        sp.moon_poll(BASE)
        sp.moon_poll(BASE)
        self.assertEqual(sp._printers_rev["n"], before + 1)

    def test_live_state_sizes_the_toolheads(self):
        self.assign(tools=["1", "2"])
        self.moonraker(extruders(2))
        doc, heads = sp.moon_poll(BASE)
        sp.live_apply(PID, "Voron", doc, link=PID, full=True)
        with sp._live_lock:
            sp.moon_mark(PID, doc, heads)
        self.addCleanup(sp._live["printers"].pop, PID, None)
        live = next(p for p in sp.live_snapshot()["printers"] if p["id"] == PID)
        self.assertTrue(live["heads"])
        self.assertEqual(len(live["units"][0]["trays"]), 2)
        self.assertFalse(live["spool_set"])


class SaveTest(KlipperCase):
    def test_page_saves_klipper_slots_beside_manual_printers(self):
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        page = [{"id": "mk4", "name": "MK4", "type": "prusalink", "ip": "10.0.0.5", "units": [{"kind": "tool", "slots": ["1"]}]},
                dict(AUTO, units=[{"kind": "tool", "slots": ["1"]}, {"kind": "tool", "slots": ["2"]}], slice_fill=False)]
        sp.save_printers(page)
        saved = self.settings["moon_slots"]["spoolman"][PID]
        self.assertEqual(saved["tools"], [None, "2"])  # spool 1 already sits on the MK4
        self.assertFalse(saved["slice_fill"])
        self.assertEqual([p["id"] for p in self.settings["printers"]["spoolman"]], ["mk4"])

    def test_gate_count_is_capped(self):
        sp.save_printers([dict(AUTO, units=[{"kind": "gate", "slots": [None] * 40}])])
        self.assertEqual(len(self.settings["moon_slots"]["spoolman"][PID]["gates"]), sp.MOON_GATES)

    def test_printer_missing_from_the_save_keeps_its_slots(self):
        self.assign(gates=["2", "3"])
        sp._auto_printers.clear()
        sp.save_printers([{"id": "mk4", "name": "MK4", "type": "prusalink", "ip": "10.0.0.5",
                           "units": [{"kind": "tool", "slots": ["3"]}]}])
        self.assertEqual(self.settings["moon_slots"]["spoolman"][PID]["gates"], ["2", None])

    def test_hidden_slots_survive_a_save(self):
        self.assign(tools=["1", "2", "3", "4"], gates=["4"])
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        entry = self.entry()
        self.assertEqual(len(entry["units"]), 2)
        sp.save_printers([entry])
        saved = self.settings["moon_slots"]["spoolman"][PID]
        self.assertEqual(saved["tools"], ["1", "2", "3", "4"])  # T3, T4 hidden, not dropped
        self.assertEqual(saved["gates"], [None])  # spool 4 already on T4

    def test_unpolled_or_managed_printer_keeps_its_slots(self):
        self.assign(gates=["1", "2"])
        entry = self.entry()  # never polled
        self.assertTrue(entry["managed"])
        self.assertEqual(sp.fill_printers([entry]), [])
        sp.save_printers([entry])
        self.assertEqual(self.settings["moon_slots"]["spoolman"][PID]["gates"], ["1", "2"])

    def test_empty_status_keeps_the_toolhead_count(self):
        sp._moon_found[PID] = {"tools": 4, "managed": False}
        self.moonraker({})
        sp.moon_poll(BASE)
        self.assertEqual(sp._moon_found[PID]["tools"], 4)

    def test_bad_units_do_not_stop_the_save(self):
        sp.save_printers([dict(AUTO, units=["x", None, {"kind": "gate", "slots": ["1"]}])])
        self.assertEqual(self.settings["moon_slots"]["spoolman"][PID]["gates"], ["1"])

    def test_only_preset_printers_take_slots(self):
        self.assertEqual(sp.parse_moon_slots([{"id": "p1", "units": [{"kind": "gate", "slots": ["1"]}]}], set()), {})


class SliceFillTest(KlipperCase):
    def slot(self, n, material, colour):
        return {"n": n, "grams": 5.0, "preset": "", "colour": colour, "material": material, "vendor": ""}

    def saved(self):
        return self.settings["moon_slots"]["spoolman"][PID]

    def test_klipper_toolheads_filled(self):
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        self.assertTrue(sp.slice_fill([self.slot(2, "PLA", "#FF0000")], BASE, SPOOLS))
        self.assertEqual(self.saved()["tools"], [None, "1"])

    def test_klipper_gates_filled_and_spool_moved_off_another_printer(self):
        self.settings["printers"]["spoolman"] = [{"id": "x1", "name": "X1", "type": "bambu", "ip": "10.0.0.7",
                                                  "units": [{"kind": "ams", "slots": ["4", None, None, None]}]}]
        self.assign(gates=[None, None, None])
        sp._moon_found[PID] = {"tools": 1, "managed": False}
        self.assertTrue(sp.slice_fill([self.slot(3, "ABS", "#00FF00")], BASE, SPOOLS))
        self.assertEqual(self.saved()["gates"], [None, None, "4"])
        self.assertEqual(self.settings["printers"]["spoolman"][0]["units"][0]["slots"], [None, None, None, None])

    def test_several_matches_ask_and_the_answer_is_set(self):
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        self.assertFalse(sp.slice_fill([self.slot(1, "PETG", "#0000FF")], BASE, SPOOLS))
        self.assertEqual(len(sp._slice_picks), 1)
        pick = sp._slice_picks[0]
        self.assertEqual((pick["printer"], pick["n"], sorted(pick["spools"])), (PID, 1, [2, 3]))
        self.assertIn("slice_picks", sp.printer_state())
        self.assertFalse(sp.slice_pick({"printer": PID, "n": 1, "slice": pick["slice"], "spool": 4}))  # not a match
        self.assertEqual(sp._slice_picks, [])
        sp.slice_fill([self.slot(1, "PETG", "#0000FF")], BASE, SPOOLS)
        # An answer to the earlier slice's question doesn't settle this one.
        self.assertFalse(sp.slice_pick({"printer": PID, "n": 1, "slice": pick["slice"], "spool": 3}))
        self.assertEqual(len(sp._slice_picks), 1)
        self.assertTrue(sp.slice_pick({"printer": PID, "n": 1, "slice": sp._slice_picks[0]["slice"], "spool": 3}))
        self.assertEqual(self.saved()["tools"], ["3", None])
        self.assertEqual(sp._slice_picks, [])

    def test_slot_already_holding_a_match_is_not_asked(self):
        self.assign(tools=["2", None])
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        sp.slice_fill([self.slot(1, "PETG", "#0000FF")], BASE, SPOOLS)
        self.assertEqual(sp._slice_picks, [])

    def test_new_slice_voids_the_last_questions(self):
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        sp.slice_fill([self.slot(1, "PETG", "#0000FF")], BASE, SPOOLS)
        self.assign(tools=[None, None], slice_fill=False)
        sp.slice_fill([self.slot(1, "PLA", "#FF0000")], BASE, SPOOLS)
        self.assertEqual(sp._slice_picks, [])

    def test_leave_as_it_is(self):
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        sp.slice_fill([self.slot(1, "PETG", "#0000FF")], BASE, SPOOLS)
        self.assertFalse(sp.slice_pick({"printer": PID, "n": 1, "slice": sp._slice_picks[0]["slice"], "spool": None}))
        self.assertEqual(sp._slice_picks, [])

    def test_net_printers_ask_too(self):
        self.settings["printers"]["spoolman"] = [{"id": "mk4", "name": "MK4", "type": "prusalink", "ip": "10.0.0.5",
                                                  "units": [{"kind": "tool", "slots": [None]}]}]
        sp.slice_fill([self.slot(1, "PETG", "#0000FF")], "http://10.0.0.5", SPOOLS)
        self.assertEqual(sp._slice_picks[0]["printer"], "mk4")
        self.assertTrue(sp.slice_pick({"printer": "mk4", "n": 1, "slice": sp._slice_picks[0]["slice"], "spool": 2}))
        self.assertEqual(self.settings["printers"]["spoolman"][0]["units"][0]["slots"], ["2"])

    def test_printer_reporting_its_own_gates_is_left_alone(self):
        sp._moon_found[PID] = {"tools": 1, "managed": True}
        self.assign(gates=[None, None])
        self.assertFalse(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], BASE, SPOOLS))
        self.assertEqual(sp._slice_picks, [])

    def test_switch_off(self):
        self.assign(tools=[None, None], slice_fill=False)
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        self.assertFalse(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], BASE, SPOOLS))

    def test_preset_chosen_for_a_printer_beats_the_address(self):
        self.settings["printers"]["spoolman"] = [{"id": "mk4", "name": "MK4", "type": "prusalink", "ip": "10.0.0.5",
                                                  "units": [{"kind": "tool", "slots": [None]}]}]
        sp._moon_found[PID] = {"tools": 2, "managed": False}
        sp.save_slice_map({"My MK4": "mk4", "": "x", "bad": 3})
        self.assertEqual(self.settings["slice_map"], {"My MK4": "mk4"})
        self.assertTrue(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], BASE, SPOOLS, preset="My MK4"))
        self.assertEqual(self.settings["printers"]["spoolman"][0]["units"][0]["slots"], ["1"])
        # Another preset still goes by its address.
        self.assertTrue(sp.slice_fill([self.slot(2, "ABS", "#00FF00")], BASE, SPOOLS, preset="Voron preset"))
        self.assertEqual(self.saved()["tools"], [None, "4"])

    def test_ctx_passes_the_preset(self):
        ctx = mock.Mock()
        ctx.config_value.side_effect = lambda key: {"print_host": "", "printer_settings_id": "My MK4"}.get(key)
        with mock.patch.object(sp, "spawn") as spawn:
            sp.slice_fill_ctx(ctx, [self.slot(1, "PLA", "#FF0000")])
        self.assertEqual(spawn.call_args.args[4], "My MK4")


if __name__ == "__main__":
    unittest.main()
