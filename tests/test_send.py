import json
import threading
import types
import unittest

from fake_bundle import U1, Preset
from plugin_loader import load

sp, orca = load()

FIELD = {"key": "orca_settings", "field_type": "text"}


def stored(data):
    """An orca_settings value as Spoolman returns it: the JSON text, JSON-encoded."""
    return json.dumps(json.dumps(data))


class ItemsTest(unittest.TestCase):
    def test_numbers(self):
        self.assertEqual(sp.orca_items("0.95,0.97", "filament_flow_ratio"), ["0.95", "0.97"])
        self.assertEqual(sp.orca_items("30%", "filament_shrink"), ["30%"])
        self.assertEqual(sp.orca_items("nil", "filament_retraction_length"), ["nil"])

    def test_text(self):
        # OrcaSlicer only quotes text with spaces or special characters, and text lists split on ";".
        self.assertEqual(sp.orca_items("65C,4h", "filament_notes"), ["65C,4h"])
        self.assertEqual(sp.orca_items('"a b";c', "filament_notes"), ["a b", "c"])
        self.assertEqual(sp.orca_items('"x\\ny \\"q\\" \\\\"', "filament_notes"), ['x\ny "q" \\'])
        self.assertEqual(sp.orca_items('""', "filament_notes"), [""])


class Filaments:
    def __init__(self, edited, saved):
        self.edited, self.saved = edited, saved

    def get_edited_preset(self):
        return self.edited

    def find_preset(self, name):
        return self.saved if name == self.saved.name else None


def bundle(edited_config, name="_local/spooler/X @Snapmaker U1"):
    saved = Preset(name, {"filament_flow_ratio": "0.98", "filament_notes": '""'})
    edited = Preset(name, dict(saved._config, **edited_config))
    return types.SimpleNamespace(filaments=Filaments(edited, saved))


class EditedTest(unittest.TestCase):
    def tearDown(self):
        orca.host.preset_bundle = None

    def test_lists_changed_settings(self):
        orca.host.preset_bundle = lambda: bundle({"filament_flow_ratio": "0.95"})
        name, changes = sp.edited_changes()
        self.assertEqual(name, "X @Snapmaker U1")
        self.assertEqual(changes, {"filament_flow_ratio": ("0.95", "0.98")})

    def test_needs_a_spooler_preset(self):
        orca.host.preset_bundle = lambda: bundle({"filament_flow_ratio": "0.95"}, name="Generic PLA")
        with self.assertRaisesRegex(RuntimeError, "Spooler preset"):
            sp.edited_changes()

    def test_needs_a_change(self):
        orca.host.preset_bundle = lambda: bundle({})
        with self.assertRaisesRegex(RuntimeError, "no unsaved changes"):
            sp.edited_changes()


class SendTest(unittest.TestCase):
    def setUp(self):
        self.calls, self.synced, self.fields = [], [], [FIELD]
        self.filament = {"id": 7, "name": "X", "material": "PLA", "extra": {"orca_settings": stored(
            {"*": {"filament_flow_ratio": "0.98", "pressure_advance": "0.04"}})}}
        self.originals = (sp.spoolman_call, sp.load_spools_synced)
        sp.spoolman_call = self.call
        sp.load_spools_synced = lambda snapshot: self.synced.append(snapshot) or {"ok": True}
        sp._profiles["names"] = {(7, U1): "X @Snapmaker U1"}

    def tearDown(self):
        sp.spoolman_call, sp.load_spools_synced = self.originals
        sp._profiles["names"] = {}

    def call(self, method, path, body=None):
        self.calls.append((method, path, body))
        if (method, path) == ("GET", "filament/7"):
            return self.filament
        return self.fields if (method, path) == ("GET", "field/filament") else {}

    def send(self, **changes):
        return sp.send_changes("X @Snapmaker U1", changes, {"snapshot": True})

    def written(self):
        """The orca_settings objects written, decoded."""
        return [json.loads(json.loads(body["extra"]["orca_settings"]))
                for method, path, body in self.calls if method == "PATCH" and path == "filament/7"]

    def test_sends_into_the_printers_section(self):
        text = self.send(filament_flow_ratio=("0.95", "0.98"), enable_pressure_advance=("1", "0"),
                         filament_shrink=("98%", "100%"))
        self.assertEqual(self.written(), [{
            "*": {"filament_flow_ratio": "0.98", "pressure_advance": "0.04"},
            U1: {"enable_pressure_advance": "1", "filament_flow_ratio": "0.95", "filament_shrink": "98%"}}])
        self.assertEqual(self.synced, [{"snapshot": True}])
        self.assertIn("Sent enable_pressure_advance, filament_flow_ratio, filament_shrink", text)

    def test_the_printers_section_goes_last_and_wins(self):
        self.filament["extra"]["orca_settings"] = stored(
            {"*": {"filament_flow_ratio": "0.98"}, U1: {"fan_max_speed": "80"}, "Snapmaker": {"filament_flow_ratio": "0.9"}})
        self.send(filament_flow_ratio=("0.95", "0.9"))
        data = self.written()[0]
        self.assertEqual(list(data), ["*", "Snapmaker", U1])
        self.assertEqual(data[U1], {"fan_max_speed": "80", "filament_flow_ratio": "0.95"})
        self.filament["extra"]["orca_settings"] = json.dumps(json.dumps(data))
        self.assertEqual(sp.orca_settings(self.filament, U1)["filament_flow_ratio"], ["0.95"])

    def test_creates_the_field_when_missing(self):
        self.fields = []
        del self.filament["extra"]["orca_settings"]
        self.send(filament_flow_ratio=("0.95", "0.98"))
        self.assertIn(("POST", "field/filament/orca_settings", {"name": "Orca settings", "field_type": "text"}),
                      self.calls)
        self.assertEqual(self.written(), [{U1: {"filament_flow_ratio": "0.95"}}])

    def test_variants_and_nil(self):
        self.send(filament_flow_ratio=("0.95,0.97", "0.98,0.98"), filament_retraction_length=("nil", "0.4"))
        self.assertEqual(self.written()[0][U1], {"filament_flow_ratio": ["0.95", "0.97"],
                                                 "filament_retraction_length": "nil"})

    def test_notes_stay_whole(self):
        self.send(filament_notes=('"Dry 4 h\\nthen \\"print\\", 65C,4h"', '""'))
        self.assertEqual(self.written()[0][U1], {"filament_notes": 'Dry 4 h\nthen "print", 65C,4h'})

    def test_all_conflicts_still_rebuild_the_presets(self):
        # Spoolman's newer value must reach the preset even when nothing is written.
        text = self.send(pressure_advance=("0.035", "0.032"))
        self.assertEqual(self.written(), [])
        self.assertEqual(self.synced, [{"snapshot": True}])
        self.assertIn("Kept Spoolman's newer value for pressure_advance", text)
        self.assertIn("your change stays unsaved", text)

    def test_settings_outside_the_list_are_not_sent(self):
        text = self.send(default_filament_colour=('"#FF0000"', '"#000000"'), filament_start_gcode=("G28", ""))
        self.assertEqual(self.written(), [])
        self.assertEqual(len(self.synced), 1)
        self.assertIn("Not sent: default_filament_colour, filament_start_gcode", text)

    def test_unreadable_field_is_not_overwritten(self):
        self.filament["extra"]["orca_settings"] = json.dumps("{not json")
        with self.assertRaisesRegex(RuntimeError, "isn't a JSON object"):
            self.send(filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(self.written(), [])

    def test_unknown_preset(self):
        sp._profiles["names"] = {}
        with self.assertRaisesRegex(RuntimeError, "no longer a Spooler preset"):
            self.send(filament_flow_ratio=("0.95", "0.98"))

    def test_other_extra_fields_go_back_unchanged(self):
        # Some Spoolman versions replace the whole extra map on a PATCH.
        self.filament["extra"]["start_gcode"] = json.dumps("M117 hi")
        self.send(filament_flow_ratio=("0.95", "0.98"))
        extras = [body["extra"] for method, _, body in self.calls if method == "PATCH"]
        self.assertEqual(extras[0]["start_gcode"], json.dumps("M117 hi"))

    def test_blank_field_is_empty(self):
        self.filament["extra"]["orca_settings"] = json.dumps("")
        self.assertEqual(sp.orca_settings_data(self.filament), {})
        self.send(filament_flow_ratio=("0.95", "0.98"))
        self.assertEqual(self.written(), [{U1: {"filament_flow_ratio": "0.95"}}])

    def test_failed_rebuild_is_reported(self):
        sp.load_spools_synced = lambda snapshot: {"ok": True, "profiles": {"count": 0, "error": "refused"}}
        text = self.send(filament_flow_ratio=("0.95", "0.98"))
        self.assertIn("Sent filament_flow_ratio", text)
        self.assertIn("The presets were not rebuilt: refused", text)
        sp.load_spools_synced = lambda snapshot: {"ok": False, "error": "Could not reach Spoolman"}
        self.assertIn("The presets were not rebuilt: Could not reach Spoolman",
                      self.send(filament_flow_ratio=("0.95", "0.98")))

    def test_more_digits_than_orcaslicer_keeps_is_not_a_conflict(self):
        # OrcaSlicer keeps 6 significant digits, so the preset holds 0.0325679 for 0.03256789.
        self.filament["extra"]["orca_settings"] = stored({"*": {"pressure_advance": "0.03256789"}})
        text = self.send(pressure_advance=("0.035", "0.0325679"))
        self.assertIn("Sent pressure_advance", text)


class StartTest(unittest.TestCase):
    def setUp(self):
        self.originals = (sp.refresh_snapshot, sp.send_changes, getattr(orca.host, "preset_bundle", None))
        sp.refresh_snapshot = lambda: {"snapshot": True}

    def tearDown(self):
        sp.refresh_snapshot, sp.send_changes, orca.host.preset_bundle = self.originals

    def test_problems_are_reported_at_once(self):
        orca.host.preset_bundle = lambda: bundle({})
        posted = []
        sp.start_send(posted.append)
        self.assertEqual(posted, [{"type": "sent", "ok": False, "text": "X @Snapmaker U1 has no unsaved changes to send."}])

    def test_sending_runs_off_the_ui_thread(self):
        orca.host.preset_bundle = lambda: bundle({"filament_flow_ratio": "0.95"})
        sent = threading.Event()
        posted = []
        sp.send_changes = lambda name, changes, snapshot: f"{name}: {sorted(changes)} {threading.current_thread() is not main}"
        main = threading.current_thread()
        sp.start_send(lambda data: (posted.append(data), sent.set()))
        self.assertTrue(sent.wait(5))
        self.assertEqual(posted, [{"type": "sent", "ok": True, "text": "X @Snapmaker U1: ['filament_flow_ratio'] True"}])


class ButtonTest(unittest.TestCase):
    def setUp(self):
        self.original = sp.start_send
        self.started = []
        sp.start_send = self.started.append

    def tearDown(self):
        sp.start_send = self.original

    def test_tab_and_window_send(self):
        page = sp.SpoolerPage()
        page.on_message({"type": "send"})
        window = sp.SpoolerWindow()
        window._panel = types.SimpleNamespace(post=lambda data: None)
        window.on_message({"type": "send"})
        self.assertEqual(self.started, [page.post_message, window._panel.post])

    def test_the_tab_has_the_button(self):
        page = sp.tab_html("main", "", 100)
        self.assertTrue('id="send-btn"' in page and 'type: "send"' in page, "no Send to Spoolman button")


if __name__ == "__main__":
    unittest.main()
