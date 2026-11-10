"""The contract with u1control (github.com/bloodf/u1control), the other plugin on the same U1:
toolhead bindings through Spoolman locations, profiles.json, keep_slots.json, the sub type
tie-break, no U1 usage booking by Spooler, and no slot flip-flop between the two plugins."""

import asyncio
import json
import re
import tempfile
import time
import types
import unittest
from pathlib import Path
from unittest import mock

from fake_bundle import FIXTURES, SV06, U1
from plugin_loader import PLUGIN, load

sp, orca = load()

U1_STATUS = json.loads((FIXTURES / "u1_status.json").read_text(encoding="utf-8"))
# Stock firmware: no filament_spool_id, no RFID card; u1control's sub type in head 4.
STOCK = json.loads((FIXTURES / "u1_stock_status.json").read_text(encoding="utf-8"))
SPOOLS = json.loads((FIXTURES / "u1control_spools.json").read_text(encoding="utf-8"))
PRINTERS = [{"target": U1, "label": "Snapmaker U1", "hosts": ["http://u1"]},
            {"target": SV06, "label": "Sovol SV06", "hosts": []}]


def copy(value):
    return json.loads(json.dumps(value))


class Snapshot(unittest.TestCase):
    """Printers known from OrcaSlicer, as the Spooler tab's snapshot holds them."""

    def setUp(self):
        sp._ui_snap.clear()
        sp._ui_snap.update(printers=PRINTERS, selected=U1)
        sp._profiles["names"] = {(f, t): f"F{f} @{label}" for f in (51, 52, 53, 54, 55)
                                 for t, label in ((U1, "Snapmaker U1"), (SV06, "Sovol SV06"))}

    def tearDown(self):
        sp._ui_snap.clear()
        sp._profiles["names"] = {}

    def trays(self, status, spools=SPOOLS):
        doc, heads = sp.moon_report(status, None, spools, U1)
        self.assertTrue(heads)
        return doc["print"]["ams"]["ams"][0]["tray"]


class LocationTest(Snapshot):
    def test_stock_firmware_heads_follow_u1controls_locations(self):
        with self.assertLogs("spooler", "WARNING") as logs:
            trays = self.trays(STOCK)
        # T1: two spools claim it, the last used wins (and that is logged). T2: the older
        # "U1 T2" form. T3: only an archived spool has the location, so nothing matches it.
        # T4: no location, two black PLAs tie, the sub type u1control wrote picks the silk one.
        self.assertEqual([t.get("spool_id") for t in trays], [101, 103, None, 106])
        self.assertIn("101, 102", logs.output[0])
        self.assertEqual([t.get("linked", "") for t in trays], ["u1control", "u1control", "", ""])
        self.assertEqual(trays[0]["profile"], "_local/spooler/F51 @Snapmaker U1")

    def test_spool_id_from_the_printer_comes_first(self):
        status = copy(STOCK)
        status["print_task_config"]["filament_spool_id"] = [105, 0, 0, 0]
        trays = self.trays(status)
        self.assertEqual(trays[0]["spool_id"], 105)
        self.assertNotIn("linked", trays[0])
        self.assertEqual(trays[1]["spool_id"], 103)  # no id for T2: its location still counts

    def test_location_comes_before_rfid_and_colour(self):
        tagged = copy(SPOOLS) + [{"id": 120, "archived": False, "remaining_weight": 500.0, "location": "",
                                  "extra": {"tag": json.dumps("60827A6A")},
                                  "filament": copy(SPOOLS[0]["filament"])}]
        status = copy(STOCK)
        status["filament_detect"]["info"][0] = {"CARD_UID": "60827A6A"}
        self.assertEqual(sp.spool_at_location(tagged, "Snapmaker U1", 1)["id"], 101)
        self.assertEqual(self.trays(status, tagged)[0]["spool_id"], 101)

    def test_matching_ignores_case_and_spaces(self):
        spools = [dict(SPOOLS[2], location="  u1   t2 "), dict(SPOOLS[4], location="SNAPMAKER U1 T3")]
        self.assertEqual(sp.spool_at_location(spools, "Snapmaker U1", 2)["id"], 103)
        self.assertEqual(sp.spool_at_location(spools, "Snapmaker U1", 3)["id"], 105)
        self.assertIsNone(sp.spool_at_location(spools, "Snapmaker U1", 4))
        self.assertIsNone(sp.spool_at_location(spools, "Snapmaker U1", 1))
        self.assertIsNone(sp.spool_at_location([dict(SPOOLS[0], location="Snapmaker U1 T10")], "Snapmaker U1", 1))

    def test_without_a_known_label_only_the_old_form_counts(self):
        sp._ui_snap["printers"] = []
        trays = self.trays(STOCK)
        self.assertEqual(trays[1]["spool_id"], 103)
        self.assertNotEqual(trays[0].get("linked"), "u1control")

    def test_archived_spools_never_match(self):
        archived = [dict(s, archived=True) for s in SPOOLS]
        self.assertEqual([t.get("spool_id") for t in self.trays(STOCK, archived)], [None] * 4)

    def test_tooltip_says_linked_by_u1control(self):
        self.assertEqual(sp._live_tray(0, self.trays(STOCK)[0])["linked"], "u1control")
        self.assertIn("Spool linked by u1control", sp.main_html())

    def test_spooler_never_writes_a_spool_location(self):
        source = PLUGIN.read_text(encoding="utf-8")
        # Every Spoolman write is a filament PATCH or a spool use/unuse PUT.
        writes = re.findall(r'"(PATCH|POST|PUT|DELETE)",\s*f?"([^"]+)"', source)
        self.assertTrue(writes)
        for method, path in writes:
            self.assertFalse(method == "PATCH" and path.startswith("spool"), (method, path))
        calls = [line for line in source.splitlines() if "spoolman_call(" in line or "urlopen(" in line]
        self.assertFalse([line for line in calls if "location" in line])


class SubTypeTest(unittest.TestCase):
    def pick(self, sub):
        slot = {"preset": "", "vendor": "Snapmaker", "material": "PLA", "colour": "080A0D", "sub_type": sub}
        return [s["id"] for s in sp.match_spools(slot, SPOOLS)]

    def test_breaks_a_tie_on_the_filament_name(self):
        self.assertEqual(self.pick("PLA_Silk_Black"), [106])
        self.assertEqual(self.pick("pla basic black"), [105])

    def test_no_or_unknown_sub_type_keeps_every_tied_spool(self):
        self.assertEqual(self.pick(""), [105, 106])
        self.assertEqual(self.pick("Basic"), [105, 106])

    def test_long_names_are_cut_like_u1control_does(self):
        long = dict(SPOOLS[5], id=107, filament=dict(SPOOLS[5]["filament"], name="PLA Silk Black " + "x" * 40))
        word = re.sub(r"[\s;=\"']+", "_", long["filament"]["name"])[:32]
        slot = {"preset": "", "vendor": "Snapmaker", "material": "PLA", "colour": "080A0D", "sub_type": word}
        self.assertEqual([s["id"] for s in sp.match_spools(slot, SPOOLS + [long])], [107])


class BridgeFolder(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.original = sp._orca_data_dir
        sp._orca_data_dir = lambda: self.root
        sp._bridge["profiles"] = None

    def tearDown(self):
        sp._orca_data_dir = self.original
        self.tmp.cleanup()

    def read(self, name):
        return json.loads((self.root / "spooler" / name).read_text(encoding="utf-8"))


PARENTS = json.loads((FIXTURES / "orca_parents.json").read_text(encoding="utf-8"))


def stocked(*filaments):
    return [{"id": 900 + f["id"], "archived": False, "remaining_weight": 500.0, "filament": f} for f in filaments]


class ProfilesJsonTest(BridgeFolder):
    def snapshot(self):
        return {"names": {p["name"] for p in PARENTS}, "parents": PARENTS, "folder": "4242", "printers": PRINTERS}

    def setUp(self):
        super().setUp()
        sp._profiles.update(failed=("", 0.0))
        self.original_reload = orca.host.preset.bundles.reload_local
        orca.host.preset.bundles.reload_local = lambda bundle: None

    def tearDown(self):
        orca.host.preset.bundles.reload_local = self.original_reload
        sp._profiles["names"] = {}
        super().tearDown()

    def test_lists_every_preset_including_clash_names(self):
        a = {"id": 7, "name": "Black", "material": "PLA", "vendor": {"name": "Acme"}, "color_hex": "000000"}
        b = dict(a, id=8)  # the same name: its presets get " #8"
        state = sp.profile_sync(stocked(a, b), self.snapshot())
        self.assertEqual(state["error"], "")
        data = self.read("profiles.json")
        self.assertEqual(data["version"], 1)
        self.assertLessEqual(abs(data["updated"] - time.time()), 5)
        self.assertEqual(data["filaments"], {
            "7": {"Snapmaker U1": "_local/spooler/Acme PLA Black @Snapmaker U1",
                  "Sovol SV06": "_local/spooler/Acme PLA Black @Sovol SV06"},
            "8": {"Snapmaker U1": "_local/spooler/Acme PLA Black #8 @Snapmaker U1",
                  "Sovol SV06": "_local/spooler/Acme PLA Black #8 @Sovol SV06"}})
        # Every preset in the bundle is listed, and nothing extra went into the presets.
        bundle = self.root / "user" / "4242" / "_local" / "spooler" / "filament"
        listed = {name for entry in data["filaments"].values() for name in entry.values()}
        self.assertEqual(listed, {"_local/spooler/" + p.stem for p in bundle.glob("*.json")})
        for preset in bundle.glob("*.json"):
            self.assertFalse({"filament_id", "spool_id", "spoolman_id"} & set(json.loads(preset.read_text())))

    def test_deleted_presets_leave_the_file(self):
        a = {"id": 7, "name": "Black", "material": "PLA", "vendor": {"name": "Acme"}}
        b = {"id": 8, "name": "White", "material": "PLA", "vendor": {"name": "Acme"}}
        sp.profile_sync(stocked(a, b), self.snapshot())
        self.assertEqual(sorted(self.read("profiles.json")["filaments"]), ["7", "8"])
        sp.profile_sync(stocked(a), self.snapshot())
        self.assertEqual(sorted(self.read("profiles.json")["filaments"]), ["7"])

    def test_written_atomically(self):
        replaced = []
        real = sp.os.replace

        def spy(src, dst):
            replaced.append((Path(src), Path(dst), Path(src).exists()))
            real(src, dst)

        with mock.patch.object(sp.os, "replace", spy):
            sp.publish_profiles({(7, U1): "X @Snapmaker U1"}, PRINTERS)
        (src, dst, existed), = replaced
        self.assertEqual(dst, self.root / "spooler" / "profiles.json")
        self.assertEqual(src.parent, dst.parent)
        self.assertTrue(existed)
        self.assertEqual(sorted(p.name for p in dst.parent.iterdir()), ["profiles.json"])

    def test_unchanged_presets_are_not_rewritten(self):
        sp.publish_profiles({(7, U1): "X @Snapmaker U1"}, PRINTERS)
        with mock.patch.object(sp, "_write_json") as write:
            sp.publish_profiles({(7, U1): "X @Snapmaker U1"}, PRINTERS)
        write.assert_not_called()


class KeepSlotsMarkerTest(BridgeFolder):
    TRAYS = [{"profile": "_local/spooler/F51 @Snapmaker U1", "tray_type": "PLA", "spool_id": 101, "filament_id": 51}]

    def setUp(self):
        super().setUp()
        self.originals = (sp.sync_for, sp.printer_trays, sp.MOON_POLL)
        orca.host.preset.filament = types.SimpleNamespace(
            begin_update=lambda slot, name: types.SimpleNamespace(commit=lambda: None))
        sp.sync_for = lambda snap: {"_local/spooler/F51 @Snapmaker U1"}
        sp.printer_trays = lambda base: self.TRAYS
        sp.MOON_POLL = 0.02
        sp._ui_snap.clear()
        sp._ui_snap.update(host="http://u1", slots=1, names=set(), current=[("Generic PLA", True)], gen=1,
                           printers=PRINTERS, selected=U1)

    def tearDown(self):
        sp.sync_for, sp.printer_trays, sp.MOON_POLL = self.originals
        sp._ui_snap.clear()
        sp._keep["run"] = None
        super().tearDown()

    def test_start_refresh_stop(self):
        async def scenario():
            run = asyncio.ensure_future(sp.SpoolerKeepSlots().execute())
            await asyncio.sleep(0.05)
            first = self.read("keep_slots.json")
            stamps = set()
            with mock.patch.object(sp.time, "time", side_effect=lambda: 1_000_000 + len(stamps)):
                for _ in range(3):
                    await asyncio.sleep(sp.MOON_POLL * 1.5)
                    stamps.add(self.read("keep_slots.json")["ts"])
            await sp.SpoolerKeepSlots().execute()  # running it again stops it
            await asyncio.wait_for(run, 1)
            return first, stamps

        first, stamps = asyncio.run(scenario())
        self.assertEqual((first["active"], first["printer"]), (True, "Snapmaker U1"))
        self.assertLessEqual(abs(first["ts"] - time.time()), 5)
        self.assertGreater(len(stamps), 1)  # refreshed on every pass
        last = self.read("keep_slots.json")
        self.assertFalse(last["active"])
        self.assertLessEqual(abs(last["ts"] - time.time()), 5)

    def test_unload_marks_it_stopped(self):
        async def scenario():
            capability = sp.SpoolerKeepSlots()
            run = asyncio.ensure_future(capability.execute())
            await asyncio.sleep(0.05)
            self.assertTrue(self.read("keep_slots.json")["active"])
            capability.on_unload()
            self.assertFalse(self.read("keep_slots.json")["active"])
            return await asyncio.wait_for(run, 1)

        self.assertEqual(asyncio.run(scenario())[0], "success")
        self.assertFalse(self.read("keep_slots.json")["active"])
        self.assertIsNone(sp._keep["run"])

    def test_unload_when_not_running_writes_nothing(self):
        sp.SpoolerKeepSlots().on_unload()
        self.assertFalse((self.root / "spooler" / "keep_slots.json").exists())


class NoU1BookingTest(unittest.TestCase):
    def test_moonraker_printers_are_never_booked(self):
        state = {"link": "auto-u1", "job": {"gcode_state": "FINISH", "mc_percent": 100}}
        with mock.patch.object(sp, "source", return_value="spoolman"), \
                mock.patch.object(sp, "usage_mode", return_value="auto"):
            self.assertEqual(sp.usage_track("auto-u1", state, True), [])
            self.assertNotIn("run", state)

    def test_a_u1_report_books_nothing(self):
        doc, _ = sp.moon_report(U1_STATUS, None, [], U1)
        doc["print"].update(gcode_state="RUNNING", mc_percent=50)
        events = []
        with mock.patch.object(sp, "source", return_value="spoolman"), \
                mock.patch.object(sp, "usage_mode", return_value="auto"), \
                mock.patch.object(sp, "usage_event", side_effect=lambda *e: events.append(e)):
            sp.live_apply("auto-u1", "U1", doc, link="auto-u1")
            doc["print"].update(gcode_state="FINISH", mc_percent=100)
            sp.live_apply("auto-u1", "U1", doc, link="auto-u1")
        sp._live["printers"].clear()
        self.assertEqual(events, [])


class NoFlipFlopTest(Snapshot):
    """Both plugins fill the same plate slot for the U1's T1 spool (filament 51)."""

    def u1control_pick(self, profiles, filament_id, label):
        # What u1control's spooler_bridge.profile_lookup() does with profiles.json.
        return (profiles["filaments"].get(str(filament_id)) or {}).get(label)

    def test_same_filament_preset_from_u1control_is_left_alone(self):
        tray = sp.moon_report(STOCK, None, SPOOLS, U1)[0]["print"]["ams"]["ams"][0]["tray"][0]
        names = {sp.PROFILE_PREFIX + n for n in sp._profiles["names"].values()}
        seen = {}
        # u1control picked the same filament's preset made for another printer.
        current = [("_local/spooler/F51 @Sovol SV06", False)]
        for gen in (1, 2):
            self.assertEqual(sp.keep_plan([tray], 1, names, current, gen, seen), [])

    def test_two_plugins_settle_on_one_preset(self):
        profiles = {"filaments": sp.profile_map(sp._profiles["names"], PRINTERS)}
        tray = sp.moon_report(STOCK, None, SPOOLS, U1)[0]["print"]["ams"]["ams"][0]["tray"][0]
        names = {sp.PROFILE_PREFIX + n for n in sp._profiles["names"].values()}
        seen, slot, history = {}, ["Generic PLA @System"], []
        for gen in (1, 2, 3):
            for _, name in sp.keep_plan([tray], 1, names, [(slot[0], slot[0].startswith("Generic"))], gen, seen):
                slot[0] = name  # Spooler's pass
            slot[0] = self.u1control_pick(profiles, tray["filament_id"], "Snapmaker U1") or slot[0]  # u1control's
            history.append(slot[0])
        self.assertEqual(history, ["_local/spooler/F51 @Snapmaker U1"] * 3)

    def test_another_filaments_preset_is_still_replaced(self):
        tray = sp.moon_report(STOCK, None, SPOOLS, U1)[0]["print"]["ams"]["ams"][0]["tray"][0]
        names = {sp.PROFILE_PREFIX + n for n in sp._profiles["names"].values()}
        self.assertEqual(sp.keep_plan([tray], 1, names, [("_local/spooler/F52 @Snapmaker U1", False)], 1, {}),
                         [(1, "_local/spooler/F51 @Snapmaker U1")])


if __name__ == "__main__":
    unittest.main()
