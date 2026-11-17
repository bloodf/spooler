"""Calibrated values from a saved copy are asked about before they reach Spoolman (Ask), sent at once
(Automatically) or left alone (Never). Nothing here touches a network: Spoolman is a mock."""

import json
import threading
import time
import types
import unittest
from unittest import mock

from fake_bundle import Preset
from plugin_loader import load
from test_send import bundle

sp, orca = load()

SPOOLER = "_local/spooler/Acme PLA Black @Snapmaker U1"
NAME = "Acme PLA Black @Snapmaker U1"


class Filaments:
    def __init__(self, presets):
        self.presets = {p.name: p for p in presets}

    def find_preset(self, name):
        return self.presets.get(name)


class AskTest(unittest.TestCase):
    def setUp(self):
        base = {"inherits": "Generic PLA @U1", "filament_flow_ratio": "0.98", "pressure_advance": "0.04",
                "filament_settings_id": "x", "filament_vendor": "Acme", "default_filament_colour": "#000000"}
        self.base = base
        self.copy(filament_flow_ratio="0.95", pressure_advance="0.035")
        sp._recent_filaments.clear()
        self.settings = {}
        self.sent, self.notices, self.page = [], [], []
        self.reply = {"type": "sent", "ok": True, "text": "Sent."}

        def start_send(post, edits=None, auto=False):
            self.sent.append(edits)
            post(dict(self.reply))

        self.patches = [
            mock.patch.object(sp, "start_send", start_send),
            mock.patch.object(sp, "source", return_value="spoolman"),
            mock.patch.object(sp, "get_settings", lambda: dict(self.settings)),
            mock.patch.object(sp, "save_settings", lambda s: self.settings.update(s) or True),
            mock.patch.object(sp, "push_notice", lambda kind, text: self.notices.append(text)),
            mock.patch.object(sp, "send_plate_message", self.page.append),
        ]
        for patch in self.patches:
            patch.start()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        orca.host.preset_bundle = None

    def copy(self, **values):
        presets = [Preset(SPOOLER, self.base), Preset("My Black", dict(self.base, filament_settings_id="y", **values))]
        orca.host.preset_bundle = lambda: types.SimpleNamespace(filaments=Filaments(presets))

    def save_copy(self):
        events = types.SimpleNamespace(PresetSelected="sel", PresetSaved="saved")
        with mock.patch.object(orca, "LifecycleEvent", events, create=True), \
                mock.patch.object(sp, "refresh_snapshot", lambda: None):
            plugin = sp.SpoolerLoadFilaments()
            plugin.on_lifecycle_event("sel", types.SimpleNamespace(name=SPOOLER, msg="filament"))
            plugin.on_lifecycle_event("sel", types.SimpleNamespace(name="My Black", msg="filament"))
            plugin.on_lifecycle_event("saved", types.SimpleNamespace(name="My Black", msg="new"))

    def answer(self, kind):
        posted = []
        sp.answer_calibration({"type": kind, "name": NAME}, posted.append)
        return posted

    def test_ask_is_the_default_and_writes_nothing(self):
        self.save_copy()
        self.assertEqual(self.sent, [])
        self.assertEqual(len(self.notices), 1)
        self.assertIn(NAME, self.notices[0])
        asks = [{"name": NAME, "changes": [
            {"key": "filament_flow_ratio", "old": "0.98", "new": "0.95", "unit": ""},
            {"key": "pressure_advance", "old": "0.04", "new": "0.035", "unit": ""}]}]
        self.assertEqual(sp.calibration_asks(), asks)
        self.assertEqual(self.page, [{"type": "calibration", "asks": asks}])

    def test_save_sends_the_change_set(self):
        self.save_copy()
        posted = self.answer("calibration_save")
        self.assertEqual(self.sent, [(NAME, {"filament_flow_ratio": ("0.95", "0.98"),
                                             "pressure_advance": ("0.035", "0.04")})])
        self.assertEqual(posted, [self.reply, {"type": "calibration", "asks": []}])
        self.assertEqual(sp.calibration_asks(), [])

    def test_a_failed_save_keeps_asking(self):
        self.reply = {"type": "sent", "ok": False, "text": "Spoolman is not reachable."}
        self.save_copy()
        posted = self.answer("calibration_save")
        self.assertEqual(len(self.sent), 1)
        self.assertEqual([ask["name"] for ask in posted[-1]["asks"]], [NAME])

    def test_skip_writes_nothing_and_is_not_asked_again_for_the_same_values(self):
        self.save_copy()
        posted = self.answer("calibration_skip")
        self.assertEqual(self.sent, [])
        self.assertEqual(posted, [{"type": "calibration", "asks": []}])
        self.assertEqual(self.settings["calibration_skipped"],
                         {NAME: {"filament_flow_ratio": "0.95", "pressure_advance": "0.035"}})
        self.notices.clear()
        self.save_copy()  # the same values saved again
        self.assertEqual((sp.calibration_asks(), self.notices), ([], []))
        self.copy(filament_flow_ratio="0.93", pressure_advance="0.035")  # one value changed again
        self.save_copy()
        self.assertEqual(sp.calibration_asks()[0]["changes"][0], {"key": "filament_flow_ratio", "old": "0.98", "new": "0.93", "unit": ""})
        self.assertEqual(len(self.notices), 1)

    def test_a_save_forgets_an_earlier_skip(self):
        self.save_copy()
        self.answer("calibration_skip")
        self.copy(filament_flow_ratio="0.93")
        self.save_copy()
        self.answer("calibration_save")
        self.assertEqual(self.settings["calibration_skipped"], {})

    def test_a_waiting_change_set_outlasts_a_restart(self):
        self.save_copy()
        self.assertEqual(self.settings["calibration_asks"],
                         {NAME: {"filament_flow_ratio": ["0.95", "0.98"], "pressure_advance": ["0.035", "0.04"]}})
        self.settings = json.loads(json.dumps(self.settings))  # as read back from the file
        self.assertEqual([ask["name"] for ask in sp.calibration_asks()], [NAME])
        self.answer("calibration_save")
        self.assertEqual(self.sent[0][1]["filament_flow_ratio"], ("0.95", "0.98"))
        self.assertEqual(self.settings["calibration_asks"], {})

    def test_units_and_unreadable_entries(self):
        self.settings["calibration_asks"] = {NAME: {"filament_max_volumetric_speed": ["21", "18"], "rm -rf": ["1", "2"],
                                                    "pressure_advance": "bad"}, "Other": "bad"}
        self.assertEqual(sp.calibration_asks(), [{"name": NAME, "changes": [
            {"key": "filament_max_volumetric_speed", "old": "18", "new": "21", "unit": "mm³/s"}]}])

    def test_an_unknown_change_set_does_nothing(self):
        posted = self.answer("calibration_save")
        self.assertEqual((self.sent, posted), ([], [{"type": "calibration", "asks": []}]))

    def test_automatically_sends_without_asking(self):
        self.settings["save_calibration"] = "auto"
        self.save_copy()
        self.assertEqual([edits[0] for edits in self.sent], [NAME])
        self.assertEqual(sp.calibration_asks(), [])

    def test_never_neither_asks_nor_sends(self):
        self.settings["save_calibration"] = "never"
        self.save_copy()
        self.assertEqual((self.sent, self.notices, sp.calibration_asks()), ([], [], []))


class UnsavedEditsTest(unittest.TestCase):
    """The 10 s tick that sends unsaved edits holds calibrated values back unless Automatically."""

    def setUp(self):
        self.settings, self.started, self.notices, self.page = {}, [], [], []
        orca.host.preset_bundle = lambda: bundle({"filament_flow_ratio": "0.95", "filament_notes": '"dry 4 h"'})
        self.patches = [
            mock.patch.object(sp, "start_send", lambda post, edits=None, auto=False: self.started.append(edits)),
            mock.patch.object(sp, "source", return_value="spoolman"),
            mock.patch.object(sp, "get_settings", lambda: dict(self.settings)),
            mock.patch.object(sp, "save_settings", lambda s: self.settings.update(s) or True),
            mock.patch.object(sp, "push_notice", lambda kind, text: self.notices.append(text)),
            mock.patch.object(sp, "send_plate_message", self.page.append),
            mock.patch.dict(sp._auto, {"seen": None, "sent": None, "busy": False, "kept": {}}),
        ]
        for patch in self.patches:
            patch.start()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        orca.host.preset_bundle = None

    def tick(self, times=4):
        for _ in range(times):
            sp.auto_send(None)

    def test_ask_sends_the_rest_and_asks_about_the_calibrated_value(self):
        self.tick()
        self.assertEqual(self.started, [("X @Snapmaker U1", {"filament_notes": ('"dry 4 h"', '""')})])
        self.assertEqual(sp.calibration_asks(), [{"name": "X @Snapmaker U1", "changes": [
            {"key": "filament_flow_ratio", "old": "0.98", "new": "0.95", "unit": ""}]}])
        self.assertEqual(len(self.notices), 1, "asked once, not every tick")

    def test_only_a_calibrated_value_sends_nothing(self):
        orca.host.preset_bundle = lambda: bundle({"filament_flow_ratio": "0.95"})
        self.tick()
        self.assertEqual(self.started, [])
        self.assertEqual(len(sp.calibration_asks()), 1)

    def test_skipped_values_are_not_asked_again(self):
        self.tick()
        sp.answer_calibration({"type": "calibration_skip", "name": "X @Snapmaker U1"}, lambda _: None)
        sp._auto.update(seen=None, sent=None)  # as after a send that failed and is tried again
        self.notices.clear()
        self.tick()
        self.assertEqual((sp.calibration_asks(), self.notices), ([], []))

    def test_never_sends_the_rest_only(self):
        self.settings["save_calibration"] = "never"
        self.tick()
        self.assertEqual(self.started, [("X @Snapmaker U1", {"filament_notes": ('"dry 4 h"', '""')})])
        self.assertEqual((sp.calibration_asks(), self.notices), ([], []))

    def test_automatically_sends_everything(self):
        self.settings["save_calibration"] = "auto"
        self.tick()
        self.assertEqual(self.started, [("X @Snapmaker U1", {"filament_flow_ratio": ("0.95", "0.98"),
                                                             "filament_notes": ('"dry 4 h"', '""')})])
        self.assertEqual(sp.calibration_asks(), [])


class LockTest(unittest.TestCase):
    def test_a_prompt_added_while_another_is_put_back_is_not_lost(self):
        # A failed Save's worker puts its set back while the UI thread adds another: without the
        # lock both read the same prompts and the later write drops the other one.
        settings = {"calibration_asks": {"A": {"filament_flow_ratio": ["0.95", "0.98"]}}}
        started = threading.Barrier(2)

        def get():
            return json.loads(json.dumps(settings))

        def put(new):
            time.sleep(0.05)  # widen the window between reading and writing
            settings.clear()
            settings.update(new)
            return True

        def start_send(post, edits=None, auto=False):
            started.wait()
            post({"type": "sent", "ok": False, "text": "refused"})

        with mock.patch.object(sp, "get_settings", get), mock.patch.object(sp, "save_settings", put), \
                mock.patch.object(sp, "start_send", start_send), mock.patch.object(sp, "push_notice"), \
                mock.patch.object(sp, "send_plate_message"):
            worker = threading.Thread(target=sp.answer_calibration, args=({"type": "calibration_save", "name": "A"}, lambda _: None))
            worker.start()
            started.wait()
            sp.offer_calibration("B", {"pressure_advance": ("0.035", "0.04")})
            worker.join()
            self.assertEqual(sorted(ask["name"] for ask in sp.calibration_asks()), ["A", "B"])


class UnknownVersionTest(unittest.TestCase):
    def ticks(self, error):
        calls, posted = [], []

        def send(name, changes, snapshot):
            calls.append(changes)
            raise error

        orca.host.preset_bundle = lambda: bundle({"filament_notes": '"dry 4 h"'})
        try:
            with mock.patch.object(sp, "source", return_value="spoolman"), \
                    mock.patch.object(sp, "get_settings", return_value={"save_calibration": "auto"}), \
                    mock.patch.object(sp, "refresh_snapshot", return_value={}), \
                    mock.patch.object(sp, "spawn", lambda work, **_: work()), \
                    mock.patch.object(sp, "send_changes", send), mock.patch.object(sp.log, "exception"), \
                    mock.patch.dict(sp._auto, {"seen": None, "sent": None, "busy": False, "kept": {}}):
                for _ in range(6):
                    sp.auto_send(posted.append)
        finally:
            orca.host.preset_bundle = None
        return len(calls), len(posted)

    def test_an_unreadable_version_is_reported_once_not_every_tick(self):
        self.assertEqual(self.ticks(sp.VersionUnknown("no version")), (1, 1))

    def test_other_failures_are_still_tried_again(self):
        self.assertGreater(self.ticks(RuntimeError("timed out"))[0], 1)


class ConfigImportTest(unittest.TestCase):
    def test_an_older_config_that_turned_saved_copies_off_means_never(self):
        settings = {"spoolman_url": "http://sm:7912"}

        class Capability:
            stored = json.dumps({"send_saved_copies": False, "spoolman_url": "http://sm:7912"})

            def get_config(self):
                return self.stored

            def save_config(self, text):
                Capability.stored = text
                return True

        with mock.patch.object(sp, "get_settings", lambda: dict(settings)), \
                mock.patch.object(sp, "save_settings", lambda s: settings.update(s) or True), \
                mock.patch.object(sp, "auto_keep_check"), mock.patch.dict(sp._config, {"last": None}):
            sp.sync_config(Capability())
        self.assertEqual(settings["save_calibration"], "never")


class ModeSettingTest(unittest.TestCase):
    def read(self, saved):
        with mock.patch.object(sp, "SETTINGS_FILE") as path:
            path.read_text.return_value = json.dumps(saved)
            return sp.get_settings()["save_calibration"]

    def test_default_and_older_setting(self):
        self.assertEqual(self.read({}), "ask")
        self.assertEqual(self.read({"send_saved_copies": False}), "never")
        self.assertEqual(self.read({"send_saved_copies": True}), "ask")
        self.assertEqual(self.read({"send_saved_copies": False, "save_calibration": "auto"}), "auto")

    def test_only_known_modes(self):
        self.assertEqual(sp.parse_calibration_mode("auto"), "auto")
        self.assertEqual(sp.parse_calibration_mode("yes"), "ask")
        self.assertEqual(sp.CONFIG_KEYS["save_calibration"]("never"), "never")


if __name__ == "__main__":
    unittest.main()
