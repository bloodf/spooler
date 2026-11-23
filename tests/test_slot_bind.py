"""Assign spool on the Printer tab for printers another plugin owns: the link is the Spoolman location that
plugin reads ("<printer> T<n>" for U1 Control, "<printer> S<n>" for Kobra Control), read back the same way,
and refused for every other printer. No printer and no Spoolman is contacted: spoolman_call is a fake."""

import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()

U1, KOBRA = "Snapmaker U1 (0.4 nozzle)", "Anycubic Kobra X 0.4 nozzle"
PRINTERS = [{"target": U1, "label": "Snapmaker U1", "model": "Snapmaker U1", "hosts": ["http://u1.example"]},
            {"target": KOBRA, "label": "Anycubic Kobra X", "model": "Anycubic Kobra X", "hosts": ["http://kx.example"]}]
AUTO = [{"id": "auto-u1", "name": "Snapmaker U1", "ip": "http://u1.example", "units": [], "kind": "moonraker", "auto": True},
        {"id": "auto-kx", "name": "Anycubic Kobra X", "ip": "http://kx.example", "units": [], "kind": "moonraker", "auto": True}]


def spool(sid, location="", material="PLA", colour="FF0000", used=""):
    return {"id": sid, "archived": False, "remaining_weight": 500, "initial_weight": 1000, "location": location, "last_used": used,
            "filament": {"id": sid, "name": f"F{sid}", "material": material, "color_hex": colour, "weight": 1000}}


class Base(unittest.TestCase):
    def setUp(self):
        sp._ui_snap.clear()
        sp._ui_snap.update(printers=PRINTERS)
        sp._auto_printers[:] = [dict(p) for p in AUTO]
        with sp._live_lock:
            sp._live["printers"]["auto-u1"] = {"name": "Snapmaker U1", "units": {}, "ext": {}, "time": 0.0, "bind": "T"}
            sp._live["printers"]["auto-kx"] = {"name": "Anycubic Kobra X", "units": {}, "ext": {}, "time": 0.0, "bind": "S"}
        self.spools = [spool(1), spool(2, "Anycubic Kobra X S2"), spool(3, "Snapmaker U1 T1"), spool(4, "Shelf")]
        patch = mock.patch.dict(sp._spool_cache, {"spools": self.spools})
        patch.start()
        self.addCleanup(patch.stop)
        self.calls = []
        call = mock.patch.object(sp, "spoolman_call", side_effect=lambda *a: self.calls.append(a) or {})
        call.start()
        self.addCleanup(call.stop)

    def tearDown(self):
        sp._ui_snap.clear()
        sp._auto_printers.clear()
        with sp._live_lock:
            sp._live["printers"].pop("auto-u1", None)
            sp._live["printers"].pop("auto-kx", None)


class BindTest(Base):
    def test_kobra_slot_takes_kobra_controls_location_and_frees_the_old_spool(self):
        result = sp.slot_bind(1, "auto-kx", 1, True)
        self.assertTrue(result["ok"], result)
        self.assertEqual(self.calls, [("PATCH", "spool/1", {"location": "Anycubic Kobra X S2"}),
                                      ("PATCH", "spool/2", {"location": None})])

    def test_u1_toolhead_takes_u1_controls_location(self):
        self.assertTrue(sp.slot_bind(1, "auto-u1", 0, True)["ok"])
        self.assertEqual(self.calls, [("PATCH", "spool/1", {"location": "Snapmaker U1 T1"}),
                                      ("PATCH", "spool/3", {"location": None})])

    def test_unbind_clears_only_a_spool_linked_to_that_slot(self):
        self.assertTrue(sp.slot_bind(3, "auto-u1", 0, False)["ok"])
        self.assertEqual(self.calls, [("PATCH", "spool/3", {"location": None})])
        self.calls.clear()
        self.assertFalse(sp.slot_bind(4, "auto-u1", 0, False)["ok"])
        self.assertEqual(self.calls, [])

    def test_refused_for_other_printers_and_bad_slots(self):
        with sp._live_lock:
            sp._live["printers"]["auto-kx"]["bind"] = ""
        for pid, slot in (("auto-kx", 0), ("auto-u1", -1), ("auto-u1", True), ("auto-u1", 8), ("nope", 0)):
            self.assertFalse(sp.slot_bind(1, pid, slot, True)["ok"], (pid, slot))
        self.assertFalse(sp.slot_bind(99, "auto-u1", 0, True)["ok"])  # not in Spoolman
        self.assertEqual(self.calls, [])

    def test_bind_goes_through_the_card_action_with_the_list_origin(self):
        with mock.patch.object(sp, "source", return_value="spoolman"), mock.patch.object(sp, "stale_list", return_value=False):
            result = sp.spool_action({"action": "bind", "id": 1, "printer": "auto-kx", "slot": 1, "origin": 1})
        self.assertTrue(result["ok"], result)
        self.assertEqual(self.calls[0], ("PATCH", "spool/1", {"location": "Anycubic Kobra X S2"}))


class ReadTest(Base):
    BOX = [{"id": 0, "slots": [{"type": "PLA", "color": [0, 0, 255], "status": 5},
                      {"type": "PLA", "color": [255, 0, 0], "status": 5, "consumables_percent": 70}]}]

    def test_kobra_reads_kobra_controls_binding_before_the_colour(self):
        trays = sp.kx_report(self.BOX, None, self.spools, KOBRA)["print"]["ams"]["ams"][0]["tray"]
        self.assertIsNone(trays[0]["spool_id"])  # blue: no spool of that colour, no binding
        self.assertEqual((trays[1]["spool_id"], trays[1]["linked"], trays[1]["remain"]), (2, "kobracontrol", None))  # Spoolman wins over the ACE's reading

    def test_live_snapshot_says_which_slots_take_a_link(self):
        binds = {p["id"]: p["bind"] for p in sp.live_snapshot()["printers"]}
        self.assertEqual((binds["auto-u1"], binds["auto-kx"]), ("T", "S"))

    def test_u1_is_never_happy_hare(self):
        status = {"print_task_config": {"filament_exist": [True]}, "mmu": {"num_gates": 0}}
        self.addCleanup(sp._moon_found.pop, "auto-u1", None)
        with mock.patch.object(sp, "_moon_get", return_value={"status": status}):
            doc, heads = sp.moon_poll("http://u1.example")
        self.assertTrue(heads)
        self.assertFalse(doc["hh"])


if __name__ == "__main__":
    unittest.main()
