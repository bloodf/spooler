"""A spool or filament linked to your own OrcaSlicer preset (the orca_filament_preset Spoolman field), and
Send to Spoolman acting on the preset picked on the page (issue #38). Everything runs against stand-ins."""

import copy
import json
import threading
import types
import unittest
from unittest import mock

import test_send
from fake_bundle import SV06, U1, Bundle, Preset
from test_profiles import SPOOLS, filament, snapshot, sp, spool
from test_send import Filaments
from test_spool_actions import Settings
from test_spool_actions import sp as asp
from test_spool_editor import SPOOL, Spoolman
from test_spool_presets import OFF, SPOOL_MODE

MINE = "My PETG @Snapmaker U1"


# MINE as OrcaSlicer sees it: one of your presets, compatible with the selected U1 and made for it only.
COMPAT = {MINE: {"now": True, "printers": [U1], "cond": ""}}


def linked_snapshot(printers=(U1,), compat=None):
    return {**snapshot(printers), "selected": U1, "user_compat": COMPAT if compat is None else compat}


def linked(holder, name):
    """holder with the field as Spoolman stores it: JSON text."""
    return {**holder, "extra": {**(holder.get("extra") or {}), "orca_filament_preset": json.dumps(name)}}


class FieldTest(unittest.TestCase):
    def test_spool_first_then_filament(self):
        f = linked(filament(1, "PETG", "PETG"), "Filament preset")
        self.assertEqual(sp.linked_preset(spool(1, f)), "Filament preset")
        self.assertEqual(sp.linked_preset(linked(spool(1, f), MINE)), MINE)
        self.assertEqual(sp.linked_preset(linked(spool(1, f), "  ")), "Filament preset", "a blank spool field falls back")
        self.assertEqual(sp.linked_preset(spool(1, filament(1, "PETG", "PETG"))), "")

    def test_typed_by_hand_and_odd_values(self):
        self.assertEqual(sp.linked_preset({"extra": {"orca_filament_preset": "  " + MINE + " "}}), MINE)
        for raw in (json.dumps(3), json.dumps(None), json.dumps(""), None, "null", "true", "false", "[\"x\"]",
                    '{"a": "b"}', json.dumps(["x"]), json.dumps({"a": "b"}), True, ["x"], {"a": "b"}):
            self.assertEqual(sp.linked_preset({"extra": {"orca_filament_preset": raw}}), "", raw)
        self.assertEqual(sp.linked_preset(None), "")

    def test_value_written(self):
        self.assertEqual(sp._link_value(" " + MINE), json.dumps(MINE))
        self.assertEqual(sp._link_value(None), json.dumps(""))
        self.assertEqual(sp._link_value(""), json.dumps(""))
        for bad in (3, "  ", "a\nb", "x" * 300, ["x"], "_local/spooler/Foo @Snapmaker U1", " _local/other/x"):
            self.assertIsNone(sp._link_value(bad), bad)


class SyncTest(unittest.TestCase):
    """Sync Presets makes no preset for a linked spool; the linked preset stands in for it."""

    def test_per_filament_a_linked_filament_gets_none(self):
        pla, petg = filament(1, "Preto", "PLA", vendor="3D Procer"), linked(filament(2, "Branco", "PETG", vendor="MasterPrint"), MINE)
        _, by_key = sp.profile_files([spool(1, pla), spool(2, petg)], linked_snapshot(), OFF)
        self.assertEqual(list(by_key), [(1, U1)])

    def test_per_spool_only_the_linked_spool_gets_none(self):
        pla = filament(1, "Preto", "PLA", vendor="3D Procer")
        _, by_key = sp.profile_files([spool(1, pla), linked(spool(2, pla), MINE)], linked_snapshot(), SPOOL_MODE)
        self.assertEqual(list(by_key), [(1, U1, 1)])

    def test_a_printer_the_link_doesnt_fit_keeps_spoolers_preset(self):
        # The #38 reporter's case: a U1 and a Voron, the link made for one of them.
        pla = filament(1, "Preto", "PLA", vendor="3D Procer")
        _, by_key = sp.profile_files([linked(spool(1, pla), MINE)], linked_snapshot((U1, SV06)), SPOOL_MODE)
        self.assertEqual(list(by_key), [(1, SV06, 1)])

    def test_a_link_that_isnt_your_preset_keeps_spoolers_preset(self):
        pla = filament(1, "Preto", "PLA", vendor="3D Procer")
        _, by_key = sp.profile_files([linked(spool(1, pla), "Typo")], linked_snapshot(), SPOOL_MODE)
        self.assertEqual(list(by_key), [(1, U1, 1)])

    def test_where_a_link_fits(self):
        snap = {"selected": U1, "user_compat": {
            "A": {"now": True, "printers": [], "cond": "nozzle_diameter[0]==0.4"},
            "B": {"now": False, "printers": [U1], "cond": ""},
            "C": {"now": True, "printers": [], "cond": ""}}}
        self.assertTrue(sp.link_fits("A", U1, snap), "the selected printer: OrcaSlicer's own check")
        self.assertFalse(sp.link_fits("B", U1, snap))
        self.assertFalse(sp.link_fits("A", SV06, snap), "a condition can't be judged for another printer")
        self.assertTrue(sp.link_fits("C", SV06, snap), "no printers, no condition: every printer")
        self.assertFalse(sp.link_fits("Unknown", U1, snap))
        self.assertFalse(sp.link_fits("", U1, snap))

    def test_real_spools_unchanged_without_links(self):
        self.assertEqual(sp.profile_files(SPOOLS, snapshot())[1], sp.profile_files(copy.deepcopy(SPOOLS), snapshot())[1])

    def test_the_linked_preset_is_the_spools_preset_where_it_fits(self):
        pla = filament(1, "Preto", "PLA")
        with mock.patch.dict(sp._profiles, names={(1, U1): "Preto @Snapmaker U1", (1, SV06, 1): "Preto #1 @Sovol SV06"}), \
                mock.patch.dict(sp._ui_snap, linked_snapshot()):
            self.assertEqual(sp.profile_for_spool(spool(1, pla), U1), sp.PROFILE_PREFIX + "Preto @Snapmaker U1")
            self.assertEqual(sp.profile_for_spool(linked(spool(1, pla), MINE), U1), MINE)
            self.assertEqual(sp.profile_for_spool(linked(spool(1, pla), MINE), SV06), sp.PROFILE_PREFIX + "Preto #1 @Sovol SV06",
                             "not on a printer it doesn't fit")
            tray = sp._spool_tray(1, linked(spool(1, pla), MINE), U1)
        self.assertEqual(tray["profile"], MINE)
        # Load Printer Filaments and Keep Slots Synced take it like any other preset OrcaSlicer has.
        self.assertEqual(sp.slot_plan([tray], 1, {MINE}), ([(1, MINE)], []))


class UserPresetsTest(unittest.TestCase):
    def test_only_your_own_presets_are_offered(self):
        bundle = Bundle("/data")
        bundle.filaments._presets += [Preset("_local/spooler/X @Snapmaker U1", {}), Preset("Hidden", {}, visible=False),
                                      Preset("a tuned PLA", {})]
        self.assertEqual(sp.user_filament_presets(bundle.filaments), ["a tuned PLA", "My TPU"])

    def test_parent_settings_are_the_saved_ones_not_unsaved_edits(self):
        saved = Preset("Generic PLA @System", {"pressure_advance": "0.02"}, system=True)
        edited = Preset("Generic PLA @System", {"pressure_advance": "0.09"}, system=True)
        bundle = chosen_bundle(edited, saved)
        configs = sp.parent_configs(bundle.filaments, [{"name": "Generic PLA @System", "printers": []}], {U1}, {})
        self.assertEqual(configs["Generic PLA @System"]["pressure_advance"], "0.02")

    def test_your_presets_printers_are_read(self):
        bundle = Bundle("/data")
        bundle.filaments._presets += [Preset("For U1", {"compatible_printers": [U1], "compatible_printers_condition": ""})]
        compat = sp.user_filament_compat(bundle.filaments)
        self.assertEqual(compat["For U1"], {"now": True, "printers": [U1], "cond": ""})
        self.assertNotIn("Generic PLA @System", compat)

    def test_a_failure_lists_none_and_keeps_the_snapshot(self):
        broken = types.SimpleNamespace(size=lambda: 2, preset=lambda i: 1 / 0)
        with self.assertLogs(sp.log, "WARNING"):
            self.assertEqual(sp.user_filament_presets(broken), [])


def chosen_bundle(edited, saved, others=()):
    return types.SimpleNamespace(filaments=Filaments(edited, saved, others))


class ChosenTest(unittest.TestCase):
    """Send to Spoolman acts on the preset picked on the page, never on the one last opened."""

    def setUp(self):
        self.pla = filament(1, "Preto", "PLA", vendor="3D Procer")
        self.spools = [spool(1, self.pla), linked(spool(2, self.pla), MINE)]
        patches = [mock.patch.dict(sp._spool_cache, spools=self.spools),
                   mock.patch.dict(sp._profiles, names={(1, U1): "Preto @Snapmaker U1", (1, SV06): "Preto @Sovol SV06"}),
                   mock.patch.dict(sp._ui_snap, linked_snapshot((U1, SV06))),
                   mock.patch.object(sp, "presets_settings", lambda: OFF)]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(setattr, sp.orca.host, "preset_bundle", None)

    def use(self, edited, saved, others=()):
        sp.orca.host.preset_bundle = lambda: chosen_bundle(edited, saved, others)

    def test_a_spools_presets(self):
        self.assertEqual([(p["name"], p["label"], p["linked"]) for p in sp.spool_presets(self.spools[0])], [
            ("_local/spooler/Preto @Snapmaker U1", "Snapmaker U1", False), ("_local/spooler/Preto @Sovol SV06", "Sovol SV06", False)])
        self.assertEqual(sp.spool_presets(self.spools[1]), [
            {"name": MINE, "label": "Snapmaker U1", "linked": True, "where": (1, U1), "own": True},
            {"name": "_local/spooler/Preto @Snapmaker U1", "label": "Snapmaker U1", "linked": False, "where": (1, U1)},
            {"name": "_local/spooler/Preto @Sovol SV06", "label": "Sovol SV06", "linked": False, "where": (1, SV06)}])

    def test_the_preset_to_pick_leads(self):
        names = lambda: [p["name"] for p in sp.spool_presets(self.spools[0])]  # noqa: E731
        sp._ui_snap["selected"] = SV06
        self.assertEqual(names()[0], "_local/spooler/Preto @Sovol SV06", "the selected printer's")
        sp._ui_snap["edited"] = "_local/spooler/Preto @Snapmaker U1"
        self.assertEqual(names()[0], "_local/spooler/Preto @Snapmaker U1", "the one open in the filament settings")

    def test_the_picked_presets_unsaved_edits(self):
        name = "_local/spooler/Preto @Snapmaker U1"
        saved = Preset(name, {"filament_flow_ratio": "0.98"})
        self.use(Preset(name, {"filament_flow_ratio": "0.95"}), saved)
        self.assertEqual(sp.chosen_changes({"spool": 1, "preset": name}),
                         ("Preto @Snapmaker U1", {"filament_flow_ratio": ("0.95", "0.98")}, None))

    def test_another_preset_open_with_edits_is_left_alone(self):
        # The reporter's case: the preset last opened had edits, the one picked had none.
        other = "_local/spooler/Preto @Sovol SV06"
        self.use(Preset(other, {"filament_flow_ratio": "0.9"}), Preset(other, {"filament_flow_ratio": "0.98"}))
        self.assertEqual(sp.chosen_changes({"spool": 1, "preset": "_local/spooler/Preto @Snapmaker U1"}),
                         ("Preto @Snapmaker U1", {}, None))

    def test_a_preset_not_of_this_spool_is_refused(self):
        self.use(Preset("x", {}), Preset("x", {}))
        for data in ({"spool": 1, "preset": "Generic PLA"}, {"spool": 99, "preset": "_local/spooler/Preto @Snapmaker U1"}, {}):
            with self.assertRaisesRegex(RuntimeError, "no longer one of this spool"):
                sp.chosen_changes(data)

    def test_a_spools_own_link_never_writes_the_shared_filament(self):
        self.use(Preset(MINE, {"pressure_advance": "0.05"}), Preset(MINE, {"pressure_advance": "0.04"}))
        with self.assertRaisesRegex(RuntimeError, "linked to this spool only"):
            sp.chosen_changes({"spool": 2, "preset": MINE})

    def test_a_filament_link_sends_its_unsaved_edits_to_the_filament(self):
        self.spools[1] = spool(2, linked(self.pla, MINE))
        sp._spool_cache["spools"] = self.spools
        self.use(Preset(MINE, {"pressure_advance": "0.05"}), Preset(MINE, {"pressure_advance": "0.04"}))
        self.assertEqual(sp.chosen_changes({"spool": 2, "preset": MINE}),
                         (MINE, {"pressure_advance": ("0.05", "0.04")}, (1, U1)))

    def test_a_linked_presets_saved_settings_that_differ(self):
        self.spools[1] = spool(2, linked(self.pla, MINE))  # linked through the filament
        sp._spool_cache["spools"] = self.spools
        # The parent's settings as the snapshot read them: the base the linked preset is compared with.
        parent = sp.best_parent(self.pla, U1, sp._ui_snap["parents"])
        sp._ui_snap["configs"] = {parent: {"pressure_advance": "0.02", "fan_max_speed": "100", "filament_start_gcode": "G1"}}
        base = sp.build_preset(self.pla, MINE, (1, U1), sp._ui_snap, OFF, self.spools)
        self.assertEqual(base["pressure_advance"], "0.02")
        tuned = {k: (v if isinstance(v, str) else ",".join(v)) for k, v in base.items()}
        tuned.update(pressure_advance="0.041", filament_flow_ratio=tuned.get("filament_flow_ratio", "1"))
        self.use(Preset("Other", {}), Preset("Other", {}), [Preset(MINE, tuned)])
        name, changes, where = sp.chosen_changes({"spool": 2, "preset": MINE})
        self.assertEqual((name, where), (MINE, (1, U1)))
        self.assertEqual(list(changes), ["pressure_advance"])
        self.assertEqual(changes["pressure_advance"][0], "0.041")

    def test_nothing_to_send_is_said_not_refused(self):
        name = "_local/spooler/Preto @Snapmaker U1"
        self.use(Preset(name, {"filament_flow_ratio": "0.98"}), Preset(name, {"filament_flow_ratio": "0.98"}))
        posted = []
        with mock.patch.object(sp, "source", lambda: "spoolman"), mock.patch.object(sp, "refresh_snapshot", lambda: {}):
            sp.start_send(posted.append, chosen={"spool": 1, "preset": name})
        self.assertEqual(posted, [{"type": "sent", "ok": True, "text": "Preto @Snapmaker U1 has no unsaved changes to send."}])

    def test_nothing_to_send_on_a_linked_preset_says_why(self):
        self.spools[1] = spool(2, linked(self.pla, MINE))
        sp._spool_cache["spools"] = self.spools
        base = sp.build_preset(self.pla, MINE, (1, U1), sp._ui_snap, OFF, self.spools)
        same = {k: (v if isinstance(v, str) else ",".join(v)) for k, v in base.items()}
        self.use(Preset("Other", {}), Preset("Other", {}), [Preset(MINE, same)])
        posted = []
        with mock.patch.object(sp, "source", lambda: "spoolman"), mock.patch.object(sp, "refresh_snapshot", lambda: {}):
            sp.start_send(posted.append, chosen={"spool": 2, "preset": MINE})
        self.assertEqual(posted[0]["text"], f"{MINE} has no unsaved changes, and its saved settings match Spoolman: nothing to send.")

    def test_presets_read_on_the_ui_thread_and_sent_off_it(self):
        name = "_local/spooler/Preto @Snapmaker U1"
        self.use(Preset(name, {"filament_flow_ratio": "0.95"}), Preset(name, {"filament_flow_ratio": "0.98"}))
        main, reads, posted, done = threading.current_thread(), [], [], threading.Event()
        bundle = sp.orca.host.preset_bundle
        sp.orca.host.preset_bundle = lambda: reads.append(threading.current_thread()) or bundle()

        def send(name, changes, snapshot, where=None):
            return f"{where} {threading.current_thread() is not main}"

        with mock.patch.object(sp, "source", lambda: "spoolman"), mock.patch.object(sp, "refresh_snapshot", lambda: {}), \
                mock.patch.object(sp, "send_changes", send):
            sp.start_send(lambda data: (posted.append(data), done.set()), chosen={"spool": 1, "preset": name})
            self.assertTrue(done.wait(5))
        self.assertEqual(posted, [{"type": "sent", "ok": True, "text": "None True"}])
        self.assertEqual(set(reads), {main})

    def test_detail_lists_the_presets(self):
        with mock.patch.object(sp, "hist_load", lambda: []), mock.patch.object(sp, "plate_spools", lambda url: []):
            detail = sp.spool_detail(2)
        self.assertEqual(detail["presets"][0], {"name": MINE, "label": "Snapmaker U1", "linked": True, "own": True})
        self.assertEqual(detail["presets"][-1], {"name": "_local/spooler/Preto @Sovol SV06", "label": "Sovol SV06", "linked": False})


class LinkedSendTest(unittest.TestCase):
    """Sending your own linked preset: its saved value is yours, not a sign Spoolman changed since."""

    setUp, tearDown, call, written = (test_send.SendTest.setUp, test_send.SendTest.tearDown,
                                      test_send.SendTest.call, test_send.SendTest.written)

    def test_a_linked_presets_saved_value_is_not_a_conflict(self):
        # Spoolman holds pressure_advance 0.04 for this printer; your preset saved 0.032 and now has 0.035.
        text = test_send.sp.send_changes(MINE, {"pressure_advance": ("0.035", "0.032")}, {"snapshot": True}, (7, U1))
        self.assertEqual(self.written()[0][U1], {"pressure_advance": "0.035"})
        self.assertIn("Sent pressure_advance", text)
        self.assertNotIn("Kept", text)

    def test_a_clash_with_spoolman_is_worded_for_your_preset(self):
        calls = 0
        original = self.call

        def changing(method, path, body=None):
            nonlocal calls
            if (method, path) == ("GET", "filament/7"):
                calls += 1
                if calls == 2:  # changed in Spoolman between the first read and the write
                    self.filament["extra"]["orca_settings"] = json.dumps(json.dumps({U1: {"pressure_advance": "0.05"}}))
            return original(method, path, body)

        test_send.sp.spoolman_call = changing
        text = test_send.sp.send_changes(MINE, {"pressure_advance": ("0.035", "0.032")}, {"snapshot": True}, (7, U1))
        self.assertIn("Kept Spoolman's newer value for pressure_advance: it changed there while you were editing.", text)
        self.assertNotIn("the preset now has it", text)


class LinkSpoolman(Spoolman):
    """The editor's stand-in Spoolman without the orca_filament_preset field until it is added."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.added = set()

    def __call__(self, method, path, body=None):
        kind = path[6:].split("/")[0] if path.startswith("field/") else ""
        if method == "POST" and path.endswith("/orca_filament_preset"):
            self.writes.append((method, path, body))
            self.added.add(kind)
            return []
        if method == "GET" and kind:
            return super().__call__(method, path, body) + (
                [{"key": "orca_filament_preset", "field_type": "text"}] if kind in self.added else [])
        return super().__call__(method, path, body)


class EditorLinkTest(Settings):
    def save(self, spool_link, fil_link, server=None):
        server = server or LinkSpoolman()
        with mock.patch.object(asp, "spoolman_call", server):
            result = asp.spool_action({"action": "save", "id": 7, "spool": {"preset_link": spool_link},
                                      "filament": {"preset_link": fil_link},
                                      "was": {"spool": {"preset_link": None}, "filament": {"id": 9, "preset_link": None}}})
        return result, server

    def test_editor_offers_your_presets_and_the_values(self):
        stored = linked(copy.deepcopy(SPOOL), MINE)
        with mock.patch.object(asp, "spoolman_call", Spoolman(stored)), \
                mock.patch.dict(asp._ui_snap, {"user_filaments": [MINE, "Other"]}):
            result = asp.spool_action({"action": "editor", "id": 7})
        self.assertEqual(result["editor"]["preset_link"], {"presets": [MINE, "Other"], "spool": MINE, "filament": ""})

    def test_adds_the_field_then_saves_both(self):
        result, server = self.save(MINE, "Filament wide")
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes[:2], [("POST", "field/spool/orca_filament_preset", asp.PRESET_LINK_DEF),
                                             ("POST", "field/filament/orca_filament_preset", asp.PRESET_LINK_DEF)])
        self.assertIn(("PATCH", "spool/7", {"extra": {"orca_filament_preset": json.dumps(MINE)}}), server.writes)
        self.assertIn(("PATCH", "filament/9", {"extra": {"orca_filament_preset": json.dumps("Filament wide")}}), server.writes)
        self.assertEqual(asp.linked_preset(server.spool), MINE)

    def test_unlinking_writes_empty_text(self):
        result, server = self.save(None, None)
        self.assertTrue(result["ok"], result)
        self.assertIn(("PATCH", "spool/7", {"extra": {"orca_filament_preset": json.dumps("")}}), server.writes)
        self.assertEqual(asp.linked_preset(server.spool), "")

    def test_a_bad_name_writes_nothing(self):
        result, server = self.save("a\nb", None)
        self.assertFalse(result["ok"])
        self.assertEqual([w for w in server.writes if w[0] == "PATCH"], [])

    def change(self, stored_spool, stored_fil, spool_link, fil_link):
        """Edit Spool on a spool whose links Spoolman already holds, sent the way the page sends them."""
        start = copy.deepcopy(SPOOL)
        if stored_spool is not None:
            start = linked(start, stored_spool)
        if stored_fil is not None:
            start["filament"] = linked(start["filament"], stored_fil)
        server = LinkSpoolman(start)
        server.added = {"spool", "filament"}
        was = lambda holder: holder.get("extra", {}).get("orca_filament_preset")  # noqa: E731
        with mock.patch.object(asp, "spoolman_call", server):
            result = asp.spool_action({"action": "save", "id": 7, "spool": {"preset_link": spool_link},
                                      "filament": {"preset_link": fil_link},
                                      "was": {"spool": {"preset_link": was(start)},
                                              "filament": {"id": 9, "preset_link": was(start["filament"])}}})
        return result, server

    def test_changing_an_existing_link(self):
        result, server = self.change(MINE, "Old filament preset", "Other", "New filament preset")
        self.assertTrue(result["ok"], result)
        self.assertNotIn("Kept Spoolman", result["text"])
        self.assertEqual(asp.linked_preset(server.spool), "Other")
        self.assertEqual(asp._link_text(server.spool["filament"]), "New filament preset")

    def test_clearing_an_existing_link(self):
        result, server = self.change(MINE, "Old filament preset", None, None)
        self.assertTrue(result["ok"], result)
        self.assertNotIn("Kept Spoolman", result["text"])
        self.assertEqual(asp.linked_preset(server.spool), "")

    def test_a_link_changed_in_spoolman_meanwhile_is_kept(self):
        result, server = self.change(MINE, None, "Other", None)
        server_before = asp.linked_preset(server.spool)
        self.assertEqual(server_before, "Other")
        start = linked(copy.deepcopy(SPOOL), "Changed in Spoolman")
        server = LinkSpoolman(start)
        server.added = {"spool", "filament"}
        with mock.patch.object(asp, "spoolman_call", server):
            result = asp.spool_action({"action": "save", "id": 7, "spool": {"preset_link": "Mine"},
                                      "was": {"spool": {"preset_link": json.dumps(MINE)}}})
        self.assertIn("Kept Spoolman", result["text"])
        self.assertEqual(asp.linked_preset(server.spool), "Changed in Spoolman")

    def test_the_field_is_spoolers_own(self):
        self.assertIn("orca_filament_preset", asp.EDITOR_OWN)


if __name__ == "__main__":
    unittest.main()
