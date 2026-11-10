"""OrcaSlicer plugin API use: native notifications, links on Windows, Keep Slots cancel, the
plugin manager's settings copy, saved copies of Spooler presets, and the all-OS wheel."""

import base64
import hashlib
import importlib
import json
import subprocess
import sys
import tempfile
import types
import unittest
import zipfile
from pathlib import Path
from unittest import mock

from fake_bundle import Preset
from plugin_loader import load

sp, orca = load()
ROOT = Path(__file__).resolve().parent.parent


class NotificationTest(unittest.TestCase):
    def setUp(self):
        self.calls = []
        self.original = orca.host.ui

    def tearDown(self):
        orca.host.ui = self.original

    def ui(self, **attrs):
        orca.host.ui = types.SimpleNamespace(push_notification=lambda *a, **k: self.calls.append(a), **attrs)

    def test_levels_from_notification_level(self):
        # OrcaSlicer 2.5: orca.host.ui.NotificationLevel.WarningNotificationLevel
        self.ui(NotificationLevel=types.SimpleNamespace(WarningNotificationLevel="W", RegularNotificationLevel="R"))
        self.assertTrue(sp.push_notice("warning", "low"))
        self.assertTrue(sp.push_notice("info", "ok"))
        self.assertEqual(self.calls, [("W", "low"), ("R", "ok")])

    def test_older_builds_with_levels_on_ui(self):
        self.ui(WarningNotificationLevel="W", RegularNotificationLevel="R")
        self.assertTrue(sp.push_notice("warning", "low"))
        self.assertEqual(self.calls, [("W", "low")])

    def test_no_notifications_at_all(self):
        orca.host.ui = types.SimpleNamespace()
        self.assertFalse(sp.push_notice("warning", "low"))


class OpenUrlTest(unittest.TestCase):
    def test_windows_uses_startfile(self):
        with mock.patch.object(sp.sys, "platform", "win32"), \
                mock.patch.object(sp.os, "startfile", create=True) as startfile, \
                mock.patch.object(sp.webbrowser, "open") as browser:
            self.assertTrue(sp.open_url("https://example.com"))
        startfile.assert_called_once_with("https://example.com")
        browser.assert_not_called()

    def test_windows_falls_back_to_webbrowser(self):
        with mock.patch.object(sp.sys, "platform", "win32"), \
                mock.patch.object(sp.os, "startfile", create=True, side_effect=OSError("no")), \
                mock.patch.object(sp.webbrowser, "open", return_value=True) as browser:
            self.assertTrue(sp.open_url("https://example.com"))
        browser.assert_called_once()

    def test_other_systems_use_webbrowser(self):
        with mock.patch.object(sp.sys, "platform", "darwin"), \
                mock.patch.object(sp.webbrowser, "open", return_value=True) as browser:
            self.assertTrue(sp.open_url("https://example.com"))
        browser.assert_called_once_with("https://example.com")


class CancelTest(unittest.TestCase):
    def test_cancel_stops_keep_slots_and_clears_the_marker(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(sp, "_orca_data_dir", lambda: Path(tmp)):
            sp._keep["run"] = object()
            sp.SpoolerKeepSlots().on_cancelled()
            self.assertIsNone(sp._keep["run"])
            self.assertFalse(json.loads((Path(tmp) / "spooler" / "keep_slots.json").read_text())["active"])

    def test_reload_failure_logs_the_offered_bundles(self):
        orca.host.preset.bundles.list_ids = lambda: ["other"]
        try:
            self.assertEqual(sp.offered_bundles(), ["other"])
        finally:
            del orca.host.preset.bundles.list_ids
        self.assertIsNone(sp.offered_bundles())


class Capability:
    """A capability's config as OrcaSlicer's plugin manager keeps it."""

    def __init__(self, stored=None, accept=True):
        self.stored, self.accept, self.saved = json.dumps(stored or {}), accept, []

    def get_config(self):
        return self.stored

    def save_config(self, text):
        self.saved.append(json.loads(text))
        if self.accept:
            self.stored = text
        return self.accept


class ConfigTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.file = Path(self.tmp.name) / "spooler_settings.json"
        self.patches = [mock.patch.object(sp, "SETTINGS_FILE", self.file),
                        mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json")]
        for patch in self.patches:
            patch.start()
        sp._config["last"] = None
        self.file.write_text(json.dumps({"spoolman_url": "http://spoolman:7912", "low_stock_grams": 150}))

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        self.tmp.cleanup()

    def test_first_sync_copies_the_file_to_the_plugin_manager(self):
        cap = Capability()
        sp.sync_config(cap)
        self.assertEqual(cap.saved[-1]["spoolman_url"], "http://spoolman:7912")
        self.assertEqual(cap.saved[-1]["low_stock_grams"], 150)
        self.assertNotIn("progress", cap.saved[-1])  # only the simple settings are shown there

    def test_an_edit_in_the_plugin_manager_reaches_the_file(self):
        cap = Capability()
        sp.sync_config(cap)
        cap.stored = json.dumps({**json.loads(cap.stored), "low_stock_grams": "250", "spool_columns": 9})
        sp.sync_config(cap)
        settings = sp.get_settings()
        self.assertEqual(settings["low_stock_grams"], 250.0)  # checked like the Settings page does
        self.assertEqual(settings["spool_columns"], sp.parse_columns(9))
        self.assertEqual(settings["spoolman_url"], "http://spoolman:7912")

    def test_an_edit_in_spooler_reaches_the_plugin_manager_without_ping_pong(self):
        cap = Capability()
        sp.sync_config(cap)
        sp.save_settings({**sp.get_settings(), "low_stock_grams": 75})
        sp.sync_config(cap)
        self.assertEqual(json.loads(cap.stored)["low_stock_grams"], 75)
        self.assertEqual(sp.get_settings()["low_stock_grams"], 75)
        before = len(cap.saved)
        sp.sync_config(cap)
        self.assertEqual(len(cap.saved), before)  # nothing left to copy either way

    def test_bad_values_are_cleaned(self):
        cap = Capability({"spoolman_url": "spoolman:7912/ ", "weight_display": "nonsense", "plate_check": "no"})
        sp.sync_config(cap)
        settings = sp.get_settings()
        self.assertEqual(settings["spoolman_url"], sp.clean_url("spoolman:7912/ "))
        self.assertEqual(settings["weight_display"], sp.parse_weights("nonsense"))
        self.assertEqual(settings["plate_check"], sp.parse_flag("no"))

    def test_builds_without_the_config_api_are_left_alone(self):
        sp.sync_config(object())
        sp.sync_config(Capability(accept=False))
        self.assertEqual(sp.get_settings()["low_stock_grams"], 150)

    def test_restore_defaults_keeps_the_spoolman_address(self):
        defaults = sp.default_config()
        self.assertEqual(defaults["spoolman_url"], "http://spoolman:7912")
        self.assertEqual(defaults["low_stock_grams"], sp.LOW_DEFAULT)
        self.assertTrue(defaults["auto_send"])
        self.assertEqual(sp.SpoolerWindow().get_default_config(), defaults)


SPOOLER = "_local/spooler/Acme PLA Black @Snapmaker U1"


class Filaments:
    def __init__(self, presets):
        self.presets = {p.name: p for p in presets}

    def find_preset(self, name):
        return self.presets.get(name)


class SavedCopyTest(unittest.TestCase):
    def setUp(self):
        base = {"inherits": "Generic PLA @U1", "filament_flow_ratio": "0.98", "pressure_advance": "0.04",
                "filament_settings_id": "x"}
        self.presets = [Preset(SPOOLER, base),
                        Preset("My Black", dict(base, filament_flow_ratio="0.95", filament_settings_id="y")),
                        Preset("Unrelated", dict(base, inherits="Generic PETG", filament_flow_ratio="0.9"))]
        orca.host.preset_bundle = lambda: types.SimpleNamespace(filaments=Filaments(self.presets))
        sp._recent_filaments.clear()
        self.sent = []
        self.patches = [mock.patch.object(sp, "start_send", lambda post, edits=None, auto=False: self.sent.append(edits)),
                        mock.patch.object(sp, "source", return_value="spoolman"),
                        mock.patch.object(sp, "get_settings", return_value={})]
        for patch in self.patches:
            patch.start()

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        orca.host.preset_bundle = None

    def event(self, kind, name, msg):
        events = types.SimpleNamespace(PresetSelected="sel", PresetSaved="saved")
        with mock.patch.object(orca, "LifecycleEvent", events, create=True), \
                mock.patch.object(sp, "refresh_snapshot", lambda: None):
            sp.SpoolerLoadFilaments().on_lifecycle_event(getattr(events, kind), types.SimpleNamespace(name=name, msg=msg))

    def test_a_saved_copy_sends_its_calibration_changes(self):
        self.event("PresetSelected", SPOOLER, "filament")
        self.event("PresetSelected", "My Black", "filament")  # OrcaSlicer picks the new copy
        self.event("PresetSaved", "My Black", "new")
        self.assertEqual(self.sent, [("Acme PLA Black @Snapmaker U1", {"filament_flow_ratio": ("0.95", "0.98")})])

    def test_not_from_a_spooler_preset(self):
        self.event("PresetSelected", "Generic PLA @U1", "filament")
        self.event("PresetSaved", "My Black", "new")
        self.event("PresetSelected", SPOOLER, "filament")
        self.event("PresetSaved", "Unrelated", "new")  # inherits something else
        self.assertEqual(self.sent, [])

    def test_overwrites_and_other_preset_types_are_ignored(self):
        self.event("PresetSelected", SPOOLER, "filament")
        self.event("PresetSaved", "My Black", "overwrite")
        self.event("PresetSelected", "Some process", "print")
        self.assertEqual(self.sent, [])
        self.assertEqual(sp._recent_filaments, [SPOOLER])

    def test_nothing_changed_sends_nothing(self):
        self.presets[1] = Preset("My Black", dict(self.presets[0]._config, filament_settings_id="y"))
        orca.host.preset_bundle = lambda: types.SimpleNamespace(filaments=Filaments(self.presets))
        self.event("PresetSelected", SPOOLER, "filament")
        self.event("PresetSaved", "My Black", "new")
        self.assertEqual(self.sent, [])

    def test_turned_off_in_settings(self):
        with mock.patch.object(sp, "get_settings", return_value={"send_saved_copies": False}):
            self.event("PresetSelected", SPOOLER, "filament")
            self.event("PresetSaved", "My Black", "new")
        self.assertEqual(self.sent, [])


class WheelTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        subprocess.run([sys.executable, str(ROOT / "scripts" / "build.py")], check=True, capture_output=True)
        version = sp.PLUGIN_VERSION
        cls.path = ROOT / "dist" / f"spooler-{version}-py3-none-any.whl"
        cls.info = f"spooler-{version}.dist-info"

    def test_one_dist_info_with_name_version_and_pure_tag(self):
        with zipfile.ZipFile(self.path) as wheel:
            names = wheel.namelist()
            self.assertEqual({n.split("/")[0] for n in names if ".dist-info/" in n}, {self.info})
            metadata = wheel.read(f"{self.info}/METADATA").decode()
            self.assertIn("Name: Spooler\n", metadata)
            self.assertIn(f"Version: {sp.PLUGIN_VERSION}\n", metadata)
            self.assertIn("Tag: py3-none-any\n", wheel.read(f"{self.info}/WHEEL").decode())
            self.assertEqual(wheel.read("spooler/__init__.py"), (ROOT / "plugin" / "spooler" / "spooler_any.py").read_bytes())

    def test_record_hashes_match(self):
        with zipfile.ZipFile(self.path) as wheel:
            for line in wheel.read(f"{self.info}/RECORD").decode().splitlines():
                name, digest, size = line.split(",")
                if not digest:
                    continue
                data = wheel.read(name)
                expected = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
                self.assertEqual((digest, int(size)), (f"sha256={expected}", len(data)), name)

    def test_the_package_imports_and_marks_the_plugin_class(self):
        sys.path.insert(0, str(self.path))
        host = sys.modules["orca"]  # the stub the package will import: the last one any test made
        decorated = list(host.decorated)
        try:
            module = importlib.import_module("spooler")
            self.assertEqual(Path(module.__file__).name, "__init__.py")
            new = [cls for cls in host.decorated if cls not in decorated]
            self.assertEqual([cls.__name__ for cls in new], ["SpoolerPlugin"])
        finally:
            sys.path.remove(str(self.path))
            sys.modules.pop("spooler", None)


if __name__ == "__main__":
    unittest.main()
