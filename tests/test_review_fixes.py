"""Regressions for the 2026-11-11 review (F01-F12): each test fails on 0.20.1 as reviewed and
states the behaviour that must hold. Transports, clocks and the host are stand-ins; nothing here
reaches a network, a printer or OrcaSlicer."""

import asyncio
import copy
import io
import json
import logging
import socket
import tempfile
import threading
import types
import unittest
import urllib.error
from pathlib import Path
from unittest import mock

from fake_bundle import U1
from plugin_loader import load

sp, orca = load()

FIELD = {"key": "orca_settings", "field_type": "text"}


def stored(data):
    return json.dumps(json.dumps(data))


def no_network(*args, **kwargs):
    raise AssertionError("network forbidden in these tests")


sp.urllib.request.urlopen = no_network
sp.socket.create_connection = no_network


class Settings:
    """A settings dict get_settings() answers from; switching the address is one assignment."""

    def __init__(self, url="http://store-a.invalid", source="spoolman"):
        self.data = {"spoolman_url": url, "spool_source": source}

    def __call__(self):
        return dict(self.data)


# --- F01: weights read from a source accept 0; action amounts stay positive -----------------


class WeightReadTest(unittest.TestCase):
    def test_reader_keeps_zero_and_rejects_junk(self):
        self.assertEqual(sp._grams(0), 0.0)
        self.assertEqual(sp._grams(12.5), 12.5)
        self.assertEqual(sp._grams(-3), -3.0)  # left to each caller's own limits
        for junk in (None, "12", True, float("nan"), float("inf"), [], {}):
            self.assertIsNone(sp._grams(junk), junk)

    def test_empty_bambu_spool_is_listed_at_zero(self):
        spool = sp.map_bambu({"id": 1, "netWeight": 0, "totalNetWeight": 1000, "filamentType": "PLA"})
        self.assertIsNotNone(spool)
        self.assertEqual((spool["remaining_weight"], spool["used_weight"], spool["initial_weight"]), (0.0, 1000.0, 1000.0))
        for unknown in (None, "0", False, float("nan")):
            self.assertIsNone(sp.map_bambu({"id": 2, "netWeight": unknown}))

    def test_bambu_fetch_keeps_the_empty_spool(self):
        with mock.patch.object(sp, "read_auth", return_value={"ok": True, "account": "a"}), \
                mock.patch.object(sp, "fetch_bambu", return_value=[{"id": 1, "netWeight": 0}, {"id": 2, "netWeight": 300}]):
            result = sp.bambu_fetch()
        self.assertEqual([s["id"] for s in result["spools"]], [1, 2])

    def test_moonraker_percentage_of_an_empty_spool_is_zero(self):
        self.assertEqual(sp._spool_remain({"remaining_weight": 0, "initial_weight": 1000}), 0.0)
        self.assertEqual(sp._spool_remain({"remaining_weight": -5, "initial_weight": 1000}), 0.0)
        self.assertEqual(sp._spool_remain({"remaining_weight": 0, "filament": {"weight": 500}}), 0.0)
        self.assertIsNone(sp._spool_remain({"remaining_weight": float("nan"), "initial_weight": 1000}))
        self.assertIsNone(sp._spool_remain({"remaining_weight": 100, "initial_weight": 0}))

    def test_card_actions_still_need_a_positive_finite_amount(self):
        with mock.patch.object(sp, "source", return_value="spoolman"), \
                mock.patch.object(sp, "spoolman_call", return_value={}) as call:
            for bad in (0, "0", -1, "nan", "inf", True, None, sp.MAX_GRAMS + 1):
                self.assertFalse(sp.spool_action({"action": "use", "id": 7, "grams": bad})["ok"], bad)
            call.assert_not_called()
            self.assertTrue(sp.spool_action({"action": "use", "id": 7, "grams": "12.5"})["ok"])


# --- F02: an operation stays on the server it started with -----------------------------------


class OriginTest(unittest.TestCase):
    def setUp(self):
        self.settings = Settings()
        self.patch = mock.patch.object(sp, "get_settings", self.settings)
        self.patch.start()
        sp.current_origin()
        self.names = dict(sp._profiles["names"])

    def tearDown(self):
        self.patch.stop()
        sp._profiles.update(names=self.names, gen=None)

    def test_send_never_writes_server_a_data_to_server_b(self):
        sp._profiles.update(names={(7, U1): "X @Snapmaker U1"}, gen=None)
        filament = {"id": 7, "material": "PLA", "extra": {"orca_settings": stored({"*": {"filament_flow_ratio": "0.98"}})}}
        calls = []

        def server(base, path, method="GET", body=None):
            calls.append((base, method, path))
            if (method, path) == ("GET", "filament/7"):
                self.settings.data["spoolman_url"] = "http://store-b.invalid"  # switched mid-send
                return copy.deepcopy(filament)
            return [FIELD] if path == "field/filament" else {}

        with mock.patch.object(sp, "_spoolman_open", server), \
                mock.patch.object(sp, "load_spools_synced", return_value={"ok": True}):
            with self.assertRaises(sp.OriginChanged):
                sp.send_changes("X @Snapmaker U1", {"filament_flow_ratio": ("0.95", "0.98")}, {})
        self.assertEqual(calls, [("http://store-a.invalid", "GET", "filament/7")])

    def test_names_from_an_old_source_are_dropped(self):
        sp._profiles.update(names={(7, U1): "X @Snapmaker U1"}, gen=None)
        self.settings.data["spoolman_url"] = "http://store-b.invalid"
        sp.current_origin()
        self.assertEqual(sp._profiles["names"], {})
        self.assertEqual(sp._spool_cache["spools"], [])

    def test_card_action_from_a_list_of_the_old_source_is_refused(self):
        old = sp.current_origin()[1]
        self.settings.data["spoolman_url"] = "http://store-b.invalid"
        with mock.patch.object(sp, "_spoolman_open") as server:
            result = sp.spool_action({"action": "archive", "id": 3, "origin": old})
        self.assertFalse(result["ok"])
        self.assertIn("changed", result["text"])
        server.assert_not_called()
        with mock.patch.object(sp, "_spoolman_open", return_value={}) as server:
            self.assertTrue(sp.spool_action({"action": "archive", "id": 3, "origin": sp.current_origin()[1]})["ok"])
        self.assertEqual(server.call_args[0][:3], ("http://store-b.invalid", "spool/3", "PATCH"))

    def test_change_spool_from_an_old_list_is_refused(self):
        old = sp.current_origin()[1]
        self.settings.data["spoolman_url"] = "http://store-b.invalid"
        posts, done = [], threading.Event()
        with mock.patch.object(sp, "moon_set_spool") as setter:
            sp.start_moon_spool({"id": "auto-x", "spool": 4, "origin": old},
                                lambda m: posts.append(m) or (m["type"] == "live" and done.set()))
            self.assertTrue(done.wait(5))
        setter.assert_not_called()
        self.assertFalse(posts[0]["ok"])

    def test_page_list_comes_from_the_source_in_settings_at_the_end(self):
        bases = []

        def server(base, path, method="GET", body=None):
            bases.append(base)
            if len(bases) == 1:
                self.settings.data["spoolman_url"] = "http://store-b.invalid"
                return [{"id": 1, "filament": {"id": 1}}]
            return [{"id": 2, "filament": {"id": 2}}]

        with mock.patch.object(sp, "_spoolman_open", server), mock.patch.object(sp, "ensure_fields"):
            result = sp.fresh_spools(None)
        self.assertEqual(bases, ["http://store-a.invalid", "http://store-b.invalid"])
        self.assertEqual([s["id"] for s in result["spools"]], [2])
        self.assertEqual(result["origin"], sp.current_origin()[1])
        self.assertEqual(sp._spool_cache["url"], "http://store-b.invalid")

    def test_presets_built_from_an_old_source_are_not_adopted_or_published(self):
        def install(*args, **kwargs):
            self.settings.data["spoolman_url"] = "http://store-b.invalid"

        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(sp, "_orca_data_dir", lambda: Path(tmp)), \
                mock.patch.object(sp, "profile_files", lambda spools, snap: ({"a.json": {}}, {(1, U1): "A"})), \
                mock.patch.object(sp, "_install_profiles", install), \
                mock.patch.object(sp, "publish_profiles") as publish:
            sp._profiles.update(names={}, failed=("", 0.0))
            with sp.pinned_origin():
                state = sp.profile_sync([], {"printers": []})
        self.assertEqual(sp._profiles["names"], {})
        self.assertTrue(state["error"])
        publish.assert_not_called()


# --- F03: sending a preset keeps what changed in Spoolman meanwhile --------------------------


class Server:
    """A Spoolman filament endpoint whose data can change between the requests of one send."""

    def __init__(self, version, merge):
        self.version, self.merge, self.gets, self.hooks, self.patches = version, merge, 0, {}, []
        self.filament = {"id": 7, "name": "X", "material": "PLA", "extra": {
            "orca_settings": stored({"*": {"filament_flow_ratio": "0.98", "pressure_advance": "0.04"}}),
            "other": json.dumps("old")}}

    def call(self, method, path, body=None):
        if path == "info":
            return {"version": self.version}
        if path == "field/filament":
            return [FIELD]
        if (method, path) == ("GET", "filament/7"):
            self.gets += 1
            answer = copy.deepcopy(self.filament)
            if self.gets in self.hooks:
                self.hooks[self.gets](self.filament)
            return answer
        if (method, path) == ("PATCH", "filament/7"):
            self.patches.append(copy.deepcopy(body))
            extra = body.pop("extra", None)
            if extra is not None:
                self.filament["extra"] = {**self.filament["extra"], **extra} if self.merge else dict(extra)
            self.filament.update(body)
        return {}

    def settings(self):
        return json.loads(json.loads(self.filament["extra"]["orca_settings"]))


class SendMergeTest(unittest.TestCase):
    def setUp(self):
        sp._versions.clear()
        sp.current_origin()  # settle the source first, as a refresh would
        sp._profiles.update(names={(7, U1): "X @Snapmaker U1"}, gen=None)

    def tearDown(self):
        sp._profiles["names"] = {}

    def send(self, server, **changes):
        with mock.patch.object(sp, "spoolman_call", server.call), \
                mock.patch.object(sp, "load_spools_synced", return_value={"ok": True}):
            return sp.send_changes("X @Snapmaker U1", changes, {})

    def test_merging_spoolman_gets_only_orca_settings(self):
        server = Server("0.27.1", merge=True)
        server.hooks[2] = lambda f: f["extra"].update(other=json.dumps("concurrent-new"))  # after the last read
        self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(list(server.patches[0]["extra"]), ["orca_settings"])
        self.assertEqual(json.loads(server.filament["extra"]["other"]), "concurrent-new")
        self.assertEqual(server.settings()[U1], {"filament_flow_ratio": "0.95"})

    def test_older_spoolman_gets_the_fields_as_read_just_before(self):
        server = Server("0.25.0", merge=False)
        server.hooks[1] = lambda f: f["extra"].update(other=json.dumps("concurrent-new"))  # between the reads
        self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(json.loads(server.filament["extra"]["other"]), "concurrent-new")
        self.assertIn("other", server.patches[0]["extra"])

    def test_unknown_version_is_treated_as_replacing(self):
        server = Server("dev", merge=False)
        self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertIn("other", server.patches[0]["extra"])

    def test_same_setting_changed_in_spoolman_meanwhile_is_kept(self):
        server = Server("0.27.1", merge=True)

        def spoolman_edit(f):
            data = json.loads(json.loads(f["extra"]["orca_settings"]))
            data[U1] = {"filament_flow_ratio": "0.97"}
            f["extra"]["orca_settings"] = stored(data)

        server.hooks[1] = spoolman_edit
        text = self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(server.settings()[U1], {"filament_flow_ratio": "0.97"})
        self.assertIn("Kept Spoolman's newer value for filament_flow_ratio", text)
        self.assertNotIn("Sent", text)

    def test_removal_in_spoolman_meanwhile_is_kept(self):
        server = Server("0.27.1", merge=True)

        def spoolman_removes(f):
            data = json.loads(json.loads(f["extra"]["orca_settings"]))
            del data["*"]["pressure_advance"]
            f["extra"]["orca_settings"] = stored(data)

        server.hooks[1] = spoolman_removes
        self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertNotIn("pressure_advance", server.settings()["*"])

    def test_field_made_unreadable_meanwhile_is_not_overwritten(self):
        server = Server("0.27.1", merge=True)
        server.hooks[1] = lambda f: f["extra"].update(orca_settings=json.dumps("not json {"))
        with self.assertRaisesRegex(RuntimeError, "isn't a JSON object"):
            self.send(server, filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(server.patches, [])

    def test_merge_settings_applies_removals_and_reports_clashes(self):
        base = {"*": {"a": "1", "b": "2"}, "P": {"c": "3"}}
        local = {"*": {"a": "1"}, "P": {"c": "4"}}  # removes b, changes c
        merged, clash = sp.merge_settings(base, local, {"*": {"a": "9", "b": "2"}, "P": {"c": "3"}, "Q": {}}, "P")
        self.assertEqual((merged, clash), ({"*": {"a": "9"}, "Q": {}, "P": {"c": "4"}}, set()))
        merged, clash = sp.merge_settings(base, local, {"*": {"a": "1", "b": "5"}, "P": {"c": "7"}}, "P")
        self.assertEqual(merged, {"*": {"a": "1", "b": "5"}, "P": {"c": "7"}})
        self.assertEqual(clash, {"b", "c"})


# --- F05: booking is recoverable, never repeated blindly --------------------------------------


class UsageTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.settings = Settings("http://a.invalid")
        self.ledger, self.saves, self.failing = [], 0, set()
        real = sp._write_json

        def flaky(path, value):
            if path == sp.USAGE_FILE:
                self.saves += 1
                if self.saves in self.failing:
                    raise OSError("synthetic disk full")
            return real(path, value)

        self.patches = [mock.patch.object(sp, "USAGE_FILE", root / "usage.json"),
                        mock.patch.object(sp, "HISTORY_FILE", root / "history.json"),
                        mock.patch.object(sp, "get_settings", self.settings),
                        mock.patch.object(sp, "plate_spools", lambda url: []),
                        mock.patch.object(sp, "_write_json", flaky)]
        for patch in self.patches:
            patch.start()
        sp._versions.clear()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        self.tmp.cleanup()

    def entry(self, state="pending", row_state="open", origin="http://a.invalid"):
        entry = {"id": "job", "state": state, "rows": [{"state": row_state, "slot": 1, "spool": 1, "grams": 10.0, "label": "x"}]}
        if origin is not None:
            entry["origin"] = origin
        sp.USAGE_FILE.write_text(json.dumps({"prints": [entry]}), encoding="utf-8")

    def use(self, error=None):
        def use(spool, grams):
            if error is not None:
                raise error
            self.ledger.append((spool, grams))
        return mock.patch.object(sp, "spoolman_use", use)

    def stored_entry(self):
        with sp._usage_lock:
            return sp.usage_load()["prints"][0]

    def test_answer_saved_late_is_never_booked_twice(self):
        self.entry()
        self.failing = {2}  # the intent is saved, the "booked" state after Spoolman's answer is not
        with self.use():
            notice = sp.usage_action({"type": "usage_book", "run": "job"})["notice"]
            self.assertIn("could not save", notice)
            self.assertEqual(self.stored_entry()["rows"][0]["state"], "unknown")
            self.assertEqual(self.stored_entry()["state"], "unknown")
            sp.usage_action({"type": "usage_book", "run": "job"})
        self.assertEqual(self.ledger, [(1, 10.0)])

    def test_intent_not_saved_means_nothing_sent(self):
        self.entry()
        self.failing = {1}
        with self.use():
            sp.usage_action({"type": "usage_book", "run": "job"})
        self.assertEqual(self.ledger, [])
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "open")

    def test_timeout_leaves_the_row_unknown_and_unretried(self):
        self.entry()
        with self.use(urllib.error.URLError(socket.timeout("timed out"))):
            sp.usage_book("job", None)
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "unknown")
        with self.use():
            sp.usage_book("job", None)
        self.assertEqual(self.ledger, [])

    def test_server_error_is_unknown_and_refusal_can_be_retried(self):
        self.entry()
        with self.use(urllib.error.HTTPError("u", 503, "busy", {}, None)):
            sp.usage_book("job", None)
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "unknown")
        self.entry()
        with self.use(urllib.error.HTTPError("u", 400, "bad", {}, None)):
            sp.usage_book("job", None)
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "open")
        with self.use(urllib.error.URLError(ConnectionRefusedError())):
            sp.usage_book("job", None)
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "open")
        with self.use():
            sp.usage_book("job", None)
        self.assertEqual((self.ledger, self.stored_entry()["state"]), ([(1, 10.0)], "booked"))

    def test_user_settles_an_unknown_row(self):
        self.entry(state="unknown", row_state="unknown")
        sp.usage_action({"type": "usage_resolve", "run": "job", "slot": 1, "outcome": "not_applied"})
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "open")
        with self.use():
            sp.usage_book("job", None)
        self.assertEqual(self.ledger, [(1, 10.0)])
        self.entry(state="unknown", row_state="unknown")
        sp.usage_action({"type": "usage_resolve", "run": "job", "slot": 1, "outcome": "applied"})
        self.assertEqual(self.stored_entry()["state"], "booked")

    def test_crash_while_sending_reads_back_as_unknown(self):
        self.entry(row_state="sending")
        self.assertEqual(self.stored_entry()["rows"][0]["state"], "unknown")

    def test_print_of_another_or_unknown_source_is_not_booked(self):
        for origin in ("http://b.invalid", None):
            self.entry(origin=origin)
            with self.use():
                self.assertIn("another spool source", sp.usage_book("job", None))
        self.assertEqual(self.ledger, [])

    def test_list_read_before_a_source_change_is_refused(self):
        self.entry()
        old = sp.current_origin()[1]
        self.settings.data["spoolman_url"] = "http://b.invalid"
        with self.use():
            notice = sp.usage_action({"type": "usage_book", "run": "job", "origin": old})["notice"]
        self.assertIn("changed", notice)
        self.assertEqual(self.ledger, [])

    def undo(self, version):
        self.entry(state="booked", row_state="booked")
        calls = []

        def call(method, path, body=None):
            calls.append((method, path, body))
            if path == "info":
                if version is None:
                    raise urllib.error.URLError("unreachable")
                return {"version": version}
            return {}

        with mock.patch.object(sp, "spoolman_call", call):
            notice = sp.usage_undo("job")
        return notice, [c for c in calls if c[1] != "info"]

    def test_undo_adds_back_in_one_request(self):
        notice, writes = self.undo("0.27.1")
        self.assertEqual((notice, writes), ("", [("PUT", "spool/1/use", {"use_weight": -10.0})]))
        self.assertEqual(self.stored_entry()["state"], "undone")

    def test_undo_is_refused_without_a_supported_version(self):
        for version in (None, "0.17.9"):
            sp._versions.clear()
            notice, writes = self.undo(version)
            self.assertIn("0.18", notice)
            self.assertEqual(writes, [])
            self.assertEqual(self.stored_entry()["state"], "booked")

    def test_u1_and_other_auto_printers_are_never_booked_here(self):
        state = {"job": {"gcode_state": "RUNNING"}, "link": "auto-u1", "name": "U1"}
        self.assertEqual(sp.usage_track("auto-u1", state, True), [])


# --- F04: Keep Slots Synced stops where it should ---------------------------------------------


class KeepSlotsTest(unittest.TestCase):
    NAME = "PLA @Snapmaker U1"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.calls = []
        sp._ui_snap.clear()
        sp._ui_snap.update(host="http://printer.invalid", selected=U1, slots=2, project=0,
                           current=[("Generic PLA", True), ("Generic PLA", True)], gen=1)
        sp._keep["run"] = None
        self.action = sp.SpoolerKeepSlots()

    def tearDown(self):
        sp._keep["run"] = None
        self.tmp.cleanup()

    def marker(self):
        return json.loads((Path(self.tmp.name) / "spooler" / "keep_slots.json").read_text())

    def run_with(self, read, tx_hook=None):
        calls = self.calls

        class Tx:
            def __init__(self, *args):
                calls.append(("begin_update", *args))
                if tx_hook:
                    tx_hook()

            def commit(self):
                calls.append(("commit",))

        async def no_wait(*args):
            return None

        profile = sp.PROFILE_PREFIX + self.NAME
        with mock.patch.object(sp, "sync_for", lambda snap: {profile}), \
                mock.patch.object(sp, "printer_trays", read), \
                mock.patch.object(sp, "_orca_data_dir", lambda: Path(self.tmp.name)), \
                mock.patch.object(sp.asyncio, "sleep", no_wait), \
                mock.patch.object(orca.host.preset, "filament", types.SimpleNamespace(begin_update=Tx), create=True):
            asyncio.run(self.action.execute())

    def trays(self):
        profile = sp.PROFILE_PREFIX + self.NAME
        return [{"profile": profile, "spool_id": 1, "filament_id": 7}, {"profile": profile, "spool_id": 2, "filament_id": 7}]

    def test_cancel_during_the_printer_read_selects_nothing(self):
        def read(base):
            self.action.on_cancelled()
            self.calls.append(("cancelled",))
            return self.trays()

        self.run_with(read)
        self.assertEqual(self.calls, [("cancelled",)])
        self.assertFalse(self.marker()["active"])

    def test_cancel_between_slots_stops_the_next_one(self):
        self.run_with(lambda base: self.trays(), tx_hook=self.action.on_cancelled)
        self.assertEqual([c[0] for c in self.calls], ["begin_update", "commit"])

    def test_project_change_during_the_read_drops_the_old_plan(self):
        reads = []

        def read(base):
            reads.append(base)
            if len(reads) == 1:
                sp._ui_snap["project"] = 1  # a project was opened meanwhile
            else:
                self.action.on_cancelled()
            return self.trays()

        self.run_with(read)
        self.assertEqual(self.calls, [])
        self.assertEqual(len(reads), 2)

    def test_an_old_run_leaves_a_newer_runs_marker(self):
        newer = object()

        def read(base):
            self.action.on_cancelled()
            sp._keep["run"] = newer  # Keep Slots started again before the old run woke up
            sp.mark_keep_slots(True, "Snapmaker U1")
            return self.trays()

        self.run_with(read)
        self.assertIs(sp._keep["run"], newer)
        self.assertTrue(self.marker()["active"])
        self.assertEqual(self.calls, [])


class UnloadTest(unittest.TestCase):
    def test_unload_stops_every_own_worker(self):
        stops = [threading.Event(), threading.Event()]
        threads = [threading.Thread(target=stop.wait, args=(10,), daemon=True) for stop in stops]
        for thread in threads:
            thread.start()
        sp._local.update({f"p{i}": {"link": {}, "stop": stops[i], "thread": threads[i]} for i in range(2)})
        sp._live["keep"] = True
        sp._ws["post"] = lambda m: None
        sp.stop_workers()
        for thread in threads:
            thread.join(2)
            self.assertFalse(thread.is_alive())
        self.assertEqual((sp._local, sp._live["keep"], sp._ws["post"]), ({}, False, None))


# --- F06: a refused bundle never replaces the accepted one on disk ---------------------------


class BundleTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.dst = self.root / "user" / "default" / "_local" / "spooler"
        sp.write_profiles(self.dst, {"old.json": {"name": "old"}})
        sp._write_json(self.dst / sp.PROFILE_STATE, {"hash": "old-hash"})
        self.before = sp.bundle_files(self.dst)

    def tearDown(self):
        self.tmp.cleanup()

    def test_refused_reload_puts_the_accepted_bundle_back(self):
        with mock.patch.object(orca.host.preset.bundles, "reload_local", side_effect=RuntimeError("synthetic invalid preset")):
            with self.assertRaises(RuntimeError):
                sp._install_profiles(self.root, {"folder": "default"}, {"new.json": {"name": "new"}}, "new-hash")
        self.assertEqual(sp.bundle_files(self.dst), self.before)
        self.assertEqual(sp.synced_digest(self.dst), "old-hash")

    def test_write_failing_halfway_puts_the_accepted_bundle_back(self):
        real, count = sp._write_json, [0]

        def fail_second(path, value):
            count[0] += 1
            if count[0] == 2:
                raise OSError("synthetic disk full")
            return real(path, value)

        with mock.patch.object(sp, "_write_json", fail_second):
            with self.assertRaises(OSError):
                sp._install_profiles(self.root, {"folder": "default"}, {"a.json": {}, "b.json": {}}, "new-hash")
        self.assertEqual(sp.bundle_files(self.dst), self.before)

    def test_accepted_bundle_replaces_and_records_its_digest(self):
        sp._install_profiles(self.root, {"folder": "default"}, {"new.json": {"name": "new"}}, "new-hash")
        self.assertEqual(sorted(p.name for p in (self.dst / "filament").iterdir()), ["new.json"])
        self.assertEqual(sp.synced_digest(self.dst), "new-hash")

    def test_refused_bundle_does_not_reach_profiles_json(self):
        with tempfile.TemporaryDirectory() as data, \
                mock.patch.object(sp, "_orca_data_dir", lambda: self.root), \
                mock.patch.object(sp, "bridge_dir", lambda: Path(data)), \
                mock.patch.object(sp, "profile_files", lambda spools, snap: ({"n.json": {}}, {(1, U1): "N"})), \
                mock.patch.object(orca.host.preset.bundles, "reload_local", side_effect=RuntimeError("refused")):
            sp._profiles.update(names={}, failed=("", 0.0))
            sp.profile_sync([], {"folder": "default", "printers": []}, force=True)
            self.assertFalse((Path(data) / sp.BRIDGE_PROFILES).exists())


# --- F07: secrets never reach the log ---------------------------------------------------------


class LogTest(unittest.TestCase):
    def capture(self):
        buf = io.StringIO()
        handler = logging.StreamHandler(buf)
        handler.setFormatter(logging.Formatter("%(message)s"))
        sp.log.addHandler(handler)
        self.addCleanup(sp.log.removeHandler, handler)
        return buf

    def test_failed_page_message_logs_no_password_or_code(self):
        buf = self.capture()
        page_class = getattr(sp, "SpoolerPage", None)
        if page_class is None:
            self.skipTest("this build has no Pages host")
        page = page_class()
        with mock.patch.object(page, "_on_settings", side_effect=RuntimeError("synthetic dispatch failure")):
            page.on_message({"view": "settings", "type": "bambu_auth", "action": "password",
                             "account": "someone@example.invalid", "password": "SYNTHETIC-SECRET-ONLY"})
            page.on_message(json.dumps({"view": "settings", "type": "bambu_auth", "action": "tfa", "code": "424242"}))
        text = buf.getvalue()
        for secret in ("SYNTHETIC-SECRET-ONLY", "someone@example.invalid", "424242"):
            self.assertNotIn(secret, text)
        self.assertIn("type=bambu_auth", text)
        self.assertIn("synthetic dispatch failure", text)

    def test_addresses_and_secret_values_are_masked_in_any_line(self):
        buf = self.capture()
        sp.log.warning("Could not reach %s", "http://user:hunter2@spoolman.invalid:7912/x?token=abc123&page=2")
        try:
            raise RuntimeError('answer {"accessToken": "eyJ.secret.sig", "message": "fine"}')
        except RuntimeError:
            sp.log.exception("Sign-in failed")
        text = buf.getvalue()
        for secret in ("hunter2", "abc123", "eyJ.secret.sig"):
            self.assertNotIn(secret, text)
        for kept in ("spoolman.invalid:7912", "page=2", '"message": "fine"', "Sign-in failed"):
            self.assertIn(kept, text)


# --- F08: MQTT size and time limits; Anycubic silence -----------------------------------------


class Sock:
    def __init__(self, data=b"", chunk=1 << 20):
        self.data, self.chunk, self.asked = bytearray(data), chunk, []

    def recv(self, size):
        self.asked.append(size)
        out = bytes(self.data[:min(size, self.chunk)])
        del self.data[:len(out)]
        if not out:
            raise socket.timeout()
        return out

    def settimeout(self, *a):
        pass

    def sendall(self, *a):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


class MqttTest(unittest.TestCase):
    def test_oversized_packet_is_refused_before_its_body(self):
        for length in (sp._mqtt_len(sp.MQTT_MAX + 1), b"\xff\xff\xff\x7f"):
            sock = Sock(b"\x30" + length + b"x" * 64)
            with self.assertRaisesRegex(ConnectionError, "byte packet"):
                sp._mqtt_read(sock)
            self.assertLessEqual(max(sock.asked), 1)

    def test_length_longer_than_four_bytes_is_refused(self):
        with self.assertRaisesRegex(ConnectionError, "malformed"):
            sp._mqtt_read(Sock(b"\x30\xff\xff\xff\xff\x01"))

    def test_trickled_packet_times_out(self):
        clock = [0.0]

        def tick():
            clock[0] += 1.0
            return clock[0]

        sock = Sock(b"\x30" + sp._mqtt_len(100) + b"x" * 100, chunk=1)
        with mock.patch.object(sp.time, "monotonic", tick), self.assertRaises(TimeoutError):
            sp._mqtt_read(sock)
        self.assertGreater(len(sock.data), 0)

    def test_stopped_link_ends_a_read(self):
        sock = Sock(b"\x30" + sp._mqtt_len(10) + b"xx", chunk=1)
        with self.assertRaisesRegex(ConnectionError, "stopped"):
            sp._mqtt_read(sock, alive=lambda: len(sock.data) > 5)

    def test_valid_packets_still_parse(self):
        packet = sp._mqtt_read(Sock(sp._mqtt_publish("device/x/report", '{"a": 1}')))
        self.assertEqual(sp._mqtt_message(packet), ("device/x/report", b'{"a": 1}'))
        qos1 = (0x32, sp._mqtt_str("t") + b"\x00\x07" + b"{}")
        self.assertEqual(sp._mqtt_message(qos1), ("t", b"{}"))
        self.assertIsNone(sp._mqtt_message((0x30, b"\x00")))
        self.assertIsNone(sp._mqtt_message((0x30, b"\x00\x10ab")))

    def test_anycubic_silent_from_the_start_is_dropped(self):
        clock, reads = [0.0], [0]

        def tick():
            clock[0] += 10.0
            return clock[0]

        def read(sock, alive=None):
            reads[0] += 1
            if reads[0] > 50:
                raise AssertionError("the silent printer was never dropped")
            return (0x20, b"\x00\x00") if reads[0] == 1 else None

        with mock.patch.object(sp, "kx_credentials", lambda base: {"modelId": "m", "deviceId": "d", "username": "u", "password": "p"}), \
                mock.patch.object(sp, "_kx_socket", lambda *a: Sock()), mock.patch.object(sp, "_mqtt_read", read), \
                mock.patch.object(sp, "_live_active", lambda: True), mock.patch.object(sp.time, "monotonic", tick), \
                mock.patch.object(sp, "get_settings", lambda: {}):
            with self.assertRaisesRegex(ConnectionError, "stopped answering"):
                sp._kx_session("auto-test", {"ip": "http://printer.invalid", "name": "test"}, threading.Event())
        self.assertLess(reads[0], 10)


# --- F09: full reports replace, Bambu deltas merge --------------------------------------------


def ams(*ids):
    return {"print": {"ams": {"ams": [{"id": str(i), "tray": [{"id": "0", "tray_type": "PLA"}]} for i in ids]}}}


class FullReportTest(unittest.TestCase):
    def setUp(self):
        sp._live["printers"].clear()

    def units(self):
        printer = sp.live_snapshot()["printers"][0]
        return [u["id"] for u in printer["units"]], printer["ext"]

    def test_full_report_drops_a_removed_unit(self):
        sp.live_apply("auto-x", "x", ams(0, 1), link="auto-x", full=True)
        sp.live_apply("auto-x", "x", ams(0), link="auto-x", full=True)
        self.assertEqual(self.units()[0], [0])
        sp.live_apply("auto-x", "x", {"print": {"ams": {"ams": []}}}, link="auto-x", full=True)
        self.assertEqual(self.units()[0], [])

    def test_full_report_switches_between_external_spool_and_mmu(self):
        sp.live_apply("auto-x", "x", {"print": {"vt_tray": {"id": "254", "tray_type": "PETG"}}}, full=True)
        self.assertIsNotNone(self.units()[1])
        sp.live_apply("auto-x", "x", ams(0), full=True)
        self.assertEqual(self.units(), ([0], None))

    def test_bambu_delta_keeps_units_it_does_not_mention(self):
        sp.live_apply("bambu", "x", ams(0, 1))
        sp.live_apply("bambu", "x", ams(0))
        self.assertEqual(self.units()[0], [0, 1])


# --- Contracts shared with u1control and the calculator stay as they were -------------------


class ContractTest(unittest.TestCase):
    def test_profiles_json_and_keep_slots_json_keep_their_shape(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(sp, "bridge_dir", lambda: Path(tmp)):
            sp._bridge["profiles"] = None
            sp.publish_profiles({(7, U1): "PLA @U1"}, [{"target": U1, "label": "Snapmaker U1"}])
            data = json.loads((Path(tmp) / sp.BRIDGE_PROFILES).read_text())
            self.assertEqual(set(data), {"version", "updated", "filaments"})
            self.assertEqual((data["version"], data["filaments"]), (1, {"7": {"Snapmaker U1": "_local/spooler/PLA @U1"}}))
            sp.mark_keep_slots(True, "Snapmaker U1")
            self.assertEqual(set(json.loads((Path(tmp) / sp.BRIDGE_KEEP).read_text())), {"active", "printer", "ts"})
            sp.mark_keep_slots(False)
            self.assertEqual(set(json.loads((Path(tmp) / sp.BRIDGE_KEEP).read_text())), {"active", "ts"})


# --- F10, F11, F12: the page script ---------------------------------------------------------







if __name__ == "__main__":
    unittest.main()
