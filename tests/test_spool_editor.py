"""Add Spool and Edit Spool: what the editor sends to Spoolman. Spoolman is a scripted stand-in;
nothing reaches the network. Only checked values go out, an edit sends only what changed, and a
field changed in Spoolman meanwhile keeps Spoolman's value."""

import json
import unittest
from unittest import mock

import spoolman_rules as rules
from test_spool_actions import Settings, sp

FIELDS = {
    "spool": [{"key": "dryer", "name": "Dryer", "field_type": "text"},
              {"key": "sealed", "name": "Sealed", "field_type": "boolean"},
              {"key": "dried", "name": "Dried", "field_type": "datetime"}],
    "filament": [{"key": "grade", "name": "Grade", "field_type": "choice", "choices": ["A", "B"]},
                 {"key": "tags", "name": "Tags", "field_type": "choice", "choices": ["x", "y"], "multi_choice": True},
                 {"key": "shrink", "name": "Shrink", "field_type": "float", "unit": "%"},
                 {"key": "layers", "name": "Layers", "field_type": "integer_range"},
                 {"key": "spools", "name": "Spools per box", "field_type": "integer"},
                 {"key": "orca_settings", "name": "Orca settings", "field_type": "text"}],
}
FILAMENT = {"id": 9, "name": "Black", "material": "PLA", "color_hex": "111111", "density": 1.24, "diameter": 1.75,
            "vendor": {"id": 2, "name": "Acme"}, "extra": {"grade": '"A"', "orca_settings": '"{}"'}}
SPOOL = {"id": 7, "remaining_weight": 500.0, "initial_weight": 1000.0, "location": "Shelf A", "comment": None,
         "extra": {"dryer": '"Box 1"', "dried": '"2026-11-10"'}, "filament": FILAMENT}


class Spoolman:
    """A stand-in Spoolman: answers GETs from its state, records every write and applies it the way
    Spoolman does (tests/spoolman_rules.py), refusing what Spoolman refuses."""

    def __init__(self, spool=None, version="0.26.0", fail=None):
        self.spool = json.loads(json.dumps(spool or SPOOL))
        self.version, self.fail, self.writes = version, fail, []

    def __call__(self, method, path, body=None):
        if method != "GET":
            self.writes.append((method, path, body))
            if self.fail and path == self.fail:
                raise rules.refuse(422, "remaining_weight can only be used if initial_weight is set")
            if path == "filament":
                rules.check_filament_body(body)
            elif path == f"filament/{self.spool['filament']['id']}":
                rules.patch_filament(self.spool["filament"], body, self.version)
            elif path == "spool/7":
                rules.patch_spool(self.spool, body, self.version)
            return {"id": {"vendor": 3, "filament": 21, "spool": 44}.get(path, 0)}
        if path.startswith("field/"):
            return FIELDS[path[6:]]
        return json.loads(json.dumps({"info": {"version": self.version}, "vendor": [{"id": 2, "name": "Acme"}, {"id": 4, "name": "Polymaker"}],
                                      "filament": [FILAMENT], "spool/7": self.spool}[path]))


class EditorTest(Settings):
    def run_action(self, data, server=None):
        server = server or Spoolman()
        with mock.patch.object(sp, "spoolman_call", server):
            return sp.spool_action(data), server.writes

    def test_editor_reads_fields_filaments_vendors_and_the_spool(self):
        result, writes = self.run_action({"action": "editor", "id": 7})
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [])
        self.assertEqual(result["editor"]["fields"], FIELDS)
        self.assertEqual(result["editor"]["vendors"], ["Acme", "Polymaker"])
        self.assertEqual(result["editor"]["spool"]["id"], 7)
        result, _ = self.run_action({"action": "editor"})
        self.assertIsNone(result["editor"]["spool"], "Add Spool reads no spool")

    def test_add_a_spool_of_an_existing_filament(self):
        result, writes = self.run_action({"action": "create", "filament_id": 9, "spool": {
            "initial_weight": "1000", "remaining_weight": 750.5, "location": "  Shelf   B ", "lot_nr": "", "price": "19,99",
            "comment": "", "archived": False, "extra": {"dryer": "Box 2", "sealed": True}}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("POST", "spool", {
            "filament_id": 9, "initial_weight": 1000.0, "remaining_weight": 750.5, "location": "Shelf B", "price": 19.99,
            "archived": False, "extra": {"dryer": '"Box 2"', "sealed": "true"}})])
        self.assertIn("#44", result["text"])

    def test_add_a_spool_of_a_new_filament_with_a_new_vendor(self):
        result, writes = self.run_action({"action": "create", "spool": {"remaining_weight": 1000}, "filament": {
            "vendor": "Fiberlab", "name": "Silk Rainbow", "material": "PLA", "multi_color_hexes": "ff0000,#00ff00",
            "multi_color_direction": "coaxial", "diameter": 1.75, "density": "1,24", "settings_extruder_temp": 215,
            "settings_bed_temp": 60, "weight": 1000, "spool_weight": 180,
            "extra": {"grade": "B", "tags": ["x", "y"], "shrink": 0.4, "layers": [2, None]}}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes[0], ("POST", "vendor", {"name": "Fiberlab"}))
        self.assertEqual(writes[1], ("POST", "filament", {
            "name": "Silk Rainbow", "material": "PLA", "multi_color_hexes": "FF0000,00FF00", "multi_color_direction": "coaxial",
            "diameter": 1.75, "density": 1.24, "settings_extruder_temp": 215, "settings_bed_temp": 60, "weight": 1000.0,
            "spool_weight": 180.0, "vendor_id": 3,
            "extra": {"grade": '"B"', "tags": '["x", "y"]', "shrink": "0.4", "layers": "[2, null]"}}))
        self.assertEqual(writes[2], ("POST", "spool", {"filament_id": 21, "remaining_weight": 1000.0}))
        self.assertIn("#44", result["text"])
        self.assertIn("#21", result["text"])

    def test_an_existing_vendor_is_reused_whatever_its_case(self):
        _, writes = self.run_action({"action": "create", "spool": {}, "filament": {
            "vendor": " acme ", "color_hex": "#aabbcc", "density": 1.2, "diameter": 1.75}})
        self.assertEqual(writes[0][2], {"color_hex": "AABBCC", "density": 1.2, "diameter": 1.75, "vendor_id": 2})

    def test_a_refused_spool_after_a_new_filament_says_the_filament_exists(self):
        result, writes = self.run_action({"action": "create", "spool": {}, "filament": {"density": 1.2, "diameter": 1.75}},
                                         Spoolman(fail="spool"))
        self.assertFalse(result["ok"])
        self.assertIn("#21", result["text"])
        self.assertIn("422", result["text"])
        self.assertEqual([w[1] for w in writes], ["filament", "spool"])
        self.assertEqual(result["filament"], 21, "the page offers the new filament, so a retry adds no second one")

    def test_edit_sends_only_the_changed_fields(self):
        result, writes = self.run_action({"action": "save", "id": 7,
                                          "spool": {"location": "Dry box", "extra": {"dryer": "Box 2", "sealed": True}},
                                          "was": {"spool": {"location": "Shelf A", "extra": {"dryer": '"Box 1"'}}}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "spool/7", {"location": "Dry box", "extra": {"dryer": '"Box 2"', "sealed": "true"}})])

    def test_edit_saves_filament_properties_to_the_filament(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {},
                                          "filament": {"color_hex": "FF8800", "settings_extruder_temp": 220, "vendor": "Polymaker"},
                                          "was": {"filament": {"id": 9, "color_hex": "111111", "settings_extruder_temp": None, "vendor": "Acme"}}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "filament/9", {"color_hex": "FF8800", "settings_extruder_temp": 220, "vendor_id": 4,
                                                           "multi_color_hexes": None, "multi_color_direction": None})])
        self.assertIn("filament", result["text"])

    def test_a_field_changed_in_spoolman_meanwhile_keeps_spoolmans_value(self):
        server = Spoolman(spool={**SPOOL, "location": "Someone else's shelf"})
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"location": "Dry box", "comment": "new"},
                                          "was": {"spool": {"location": "Shelf A", "comment": None}}}, server)
        self.assertEqual(writes, [("PATCH", "spool/7", {"comment": "new"})])
        self.assertIn("location", result["text"])

    def test_spoolman_before_0_22_gets_the_whole_extra_map_back(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"extra": {"dryer": None, "sealed": False}},
                                          "was": {"spool": {"extra": {"dryer": '"Box 1"'}}}}, Spoolman(version="0.21.0"))
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "spool/7", {"extra": {"dried": '"2026-11-10"', "sealed": "false"}})],
                         "the dried date stays; the cleared field goes")

    def test_new_spoolman_removes_a_cleared_extra_field_with_null(self):
        _, writes = self.run_action({"action": "save", "id": 7, "spool": {"extra": {"dryer": None}},
                                     "was": {"spool": {"extra": {"dryer": '"Box 1"'}}}})
        self.assertEqual(writes, [("PATCH", "spool/7", {"extra": {"dryer": None}})])

    def test_spoolman_0_22_to_0_25_gets_only_the_changed_keys_and_cant_empty_one(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"extra": {"sealed": True}},
                                          "was": {"spool": {"extra": {}}}}, Spoolman(version="0.25.3"))
        self.assertEqual(writes, [("PATCH", "spool/7", {"extra": {"sealed": "true"}})])
        server = Spoolman(version="0.25.3")
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"location": "B", "extra": {"dryer": None}},
                                          "was": {"spool": {"location": "Shelf A", "extra": {"dryer": '"Box 1"'}}}}, server)
        self.assertIn("dryer", server.spool["extra"], "this Spoolman can't remove it")
        self.assertFalse(result["ok"])
        self.assertIn("0.26", result["text"])
        self.assertEqual(writes, [], "nothing, not even the location")

    def test_unknown_version_writes_no_extra_field(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"extra": {"sealed": True}},
                                          "was": {"spool": {"extra": {}}}}, Spoolman(version="?"))
        self.assertFalse(result["ok"])
        self.assertEqual(writes, [])

    def test_colour_changes_send_the_whole_colour_group(self):
        multi = {**SPOOL, "filament": {**FILAMENT, "color_hex": None, "multi_color_hexes": "FF0000,00FF00",
                                       "multi_color_direction": "longitudinal"}}
        result, writes = self.run_action({"action": "save", "id": 7, "filament": {"multi_color_hexes": "FF0000,0000FF"},
                                          "was": {"filament": {"id": 9, "multi_color_hexes": "FF0000,00FF00"}}}, Spoolman(spool=multi))
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "filament/9", {"multi_color_hexes": "FF0000,0000FF", "color_hex": None,
                                                           "multi_color_direction": "longitudinal"})])
        result, writes = self.run_action({"action": "save", "id": 7, "filament": {"multi_color_direction": "coaxial"},
                                          "was": {"filament": {"id": 9, "multi_color_direction": "longitudinal"}}}, Spoolman(spool=multi))
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "filament/9", {"multi_color_direction": "coaxial", "color_hex": None,
                                                           "multi_color_hexes": "FF0000,00FF00"})])

    def test_grams_left_and_starting_weight_cant_be_emptied(self):
        for key in ("remaining_weight", "initial_weight"):
            result, writes = self.run_action({"action": "save", "id": 7, "spool": {key: None}, "was": {"spool": {key: 500.0}}})
            self.assertFalse(result["ok"], key)
            self.assertEqual(writes, [])

    def test_a_new_starting_weight_keeps_the_grams_left_shown(self):
        server = Spoolman()
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"initial_weight": 1200, "remaining_weight": 500},
                                     "was": {"spool": {"initial_weight": 1000.0, "remaining_weight": 500.0}}}, server)
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "spool/7", {"initial_weight": 1200.0, "remaining_weight": 500.0})])
        self.assertEqual(server.spool["remaining_weight"], 500.0, "Spoolman still has the grams left the form showed")

    def test_a_new_starting_weight_keeps_use_booked_meanwhile(self):
        # The editor read 500 g left; a print then used 30 g in Spoolman. The new starting weight
        # must not bring the 30 g back, nor claim a kept value the user never changed.
        server = Spoolman(spool={**SPOOL, "remaining_weight": 470.0})
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"initial_weight": 1200, "remaining_weight": 500},
                                          "was": {"spool": {"initial_weight": 1000.0, "remaining_weight": 500.0}}}, server)
        self.assertTrue(result["ok"], result)
        self.assertEqual(writes, [("PATCH", "spool/7", {"initial_weight": 1200.0, "remaining_weight": 470.0})])
        self.assertEqual(server.spool["remaining_weight"], 470.0)
        self.assertNotIn("Kept", result["text"])

    def test_filament_changes_never_land_on_a_filament_the_spool_moved_to(self):
        moved = {**SPOOL, "filament": {**FILAMENT, "id": 12}}
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"location": "B"},
                                          "filament": {"settings_extruder_temp": 230},
                                          "was": {"spool": {"location": "Shelf A"}, "filament": {"id": 9, "settings_extruder_temp": None}}},
                                         Spoolman(spool=moved))
        self.assertEqual(writes, [("PATCH", "spool/7", {"location": "B"})])
        self.assertIn("settings_extruder_temp", result["text"])

    def test_a_refused_spool_after_its_filament_says_the_filament_was_saved(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"location": "B"}, "filament": {"name": "Jet"},
                                          "was": {"spool": {"location": "Shelf A"}, "filament": {"id": 9, "name": "Black"}}},
                                         Spoolman(fail="spool/7"))
        self.assertFalse(result["ok"])
        self.assertIn("filament", result["text"])
        self.assertEqual([w[1] for w in writes], ["filament/9", "spool/7"])

    def test_whole_numbers_go_as_integers(self):
        _, writes = self.run_action({"action": "create", "spool": {}, "filament": {"density": 1.2, "diameter": 1.75,
                                                                                 "extra": {"spools": 3.0, "layers": [1.0, None]}}})
        self.assertEqual(writes[0][2]["extra"], {"spools": "3", "layers": "[1, null]"})

    def test_nothing_changed_writes_nothing(self):
        result, writes = self.run_action({"action": "save", "id": 7, "spool": {"location": "Shelf A"},
                                          "was": {"spool": {"location": "Shelf A"}}})
        self.assertTrue(result["ok"])
        self.assertEqual(writes, [])

    def test_bad_input_never_reaches_spoolman(self):
        bad_spool = [{"remaining_weight": -1}, {"remaining_weight": "nan"}, {"initial_weight": 1e9}, {"location": "x" * 65},
                     {"archived": "yes"}, {"archived": None}, {"price": True}, {"filament_id": 3}, {"extra": "x"},
                     {"extra": {"unknown": "x"}}, {"extra": {"dried": "2026-01-01"}}, {"extra": {"sealed": "true"}},
                     {"initial_weight": 500, "remaining_weight": 600}]
        for spool in bad_spool:
            for data in ({"action": "create", "filament_id": 9, "spool": spool}, {"action": "save", "id": 7, "spool": spool}):
                if data["action"] == "save" and "initial_weight" in spool and "remaining_weight" in spool:
                    continue  # only a new spool is checked for more left than it started with
                result, writes = self.run_action(data)
                self.assertFalse(result["ok"], data)
                self.assertEqual(writes, [], data)
        bad_filament = [{"diameter": 1.75}, {"density": 1.2}, {"density": 0, "diameter": 1.75}, {"density": 1.2, "diameter": None},
                        {"density": 1.2, "diameter": 1.75, "color_hex": "red"}, {"density": 1.2, "diameter": 1.75, "multi_color_hexes": "ff0000"},
                        {"density": 1.2, "diameter": 1.75, "multi_color_direction": "spiral"},
                        {"density": 1.2, "diameter": 1.75, "settings_bed_temp": 60.5},
                        {"density": 1.2, "diameter": 1.75, "extra": {"grade": "C"}},
                        {"density": 1.2, "diameter": 1.75, "extra": {"tags": ["z"]}},
                        {"density": 1.2, "diameter": 1.75, "extra": {"layers": [1.5, 2]}},
                        {"density": 1.2, "diameter": 1.75, "extra": {"orca_settings": "{}"}},
                        {"density": 1.2, "diameter": 1.75, "id": 3}, {"density": 1.2, "diameter": 1.75, "weight": 0}, "PLA"]
        for filament in bad_filament:
            result, writes = self.run_action({"action": "create", "spool": {}, "filament": filament})
            self.assertFalse(result["ok"], filament)
            self.assertEqual(writes, [], filament)
        for data in ({"action": "save", "spool": {}}, {"action": "save", "id": "7", "spool": {}}):
            result, writes = self.run_action(data)
            self.assertFalse(result["ok"], data)
            self.assertEqual(writes, [])

    def test_a_stale_list_writes_nothing(self):
        result, writes = self.run_action({"action": "create", "filament_id": 9, "spool": {}, "origin": 99999})
        self.assertFalse(result["ok"])
        self.assertEqual(writes, [])

    def test_spoolman_refusing_an_edit_is_the_visible_result(self):
        result, _ = self.run_action({"action": "save", "id": 7, "spool": {"location": "B"}, "was": {"spool": {"location": "Shelf A"}}},
                                    Spoolman(fail="spool/7"))
        self.assertFalse(result["ok"])
        self.assertIn("422", result["text"])


if __name__ == "__main__":
    unittest.main()
