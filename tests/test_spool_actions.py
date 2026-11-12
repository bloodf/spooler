"""Card actions on the Spools tab: adjust, archive, move, add and open a spool in Spoolman, the
one Spoolman opener under them, and the "Show archived" filter that must not leak archived
spools into profiles, the plate check or live matching."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class Settings(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patches = [mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                        mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json")]
        for patch in self.patches:
            patch.start()
        sp.save_settings({"spoolman_url": "http://spoolman:7912", "spool_source": "spoolman"})

    def tearDown(self):
        for patch in self.patches:
            patch.stop()
        self.tmp.cleanup()


class ActionTest(Settings):
    def act(self, data, answer=None):
        with mock.patch.object(sp, "spoolman_call", return_value=answer) as call:
            result = sp.spool_action(data)
        return result, call

    def test_weigh_sends_the_gross_weight_to_measure(self):
        result, call = self.act({"action": "weigh", "id": 7, "grams": "1234.56"})
        self.assertTrue(result["ok"], result)
        call.assert_called_once_with("PUT", "spool/7/measure", {"weight": 1234.6})

    def test_use_books_grams_on_the_spool(self):
        result, call = self.act({"action": "use", "id": 7, "grams": 12.5})
        self.assertTrue(result["ok"], result)
        call.assert_called_once_with("PUT", "spool/7/use", {"use_weight": 12.5})

    def test_archive_and_unarchive(self):
        result, call = self.act({"action": "archive", "id": 3})
        self.assertTrue(result["ok"])
        call.assert_called_once_with("PATCH", "spool/3", {"archived": True})
        result, call = self.act({"action": "unarchive", "id": 3})
        call.assert_called_once_with("PATCH", "spool/3", {"archived": False})

    def test_move_sets_or_clears_the_location(self):
        result, call = self.act({"action": "move", "id": 3, "location": "  Shelf  B "})
        self.assertTrue(result["ok"])
        call.assert_called_once_with("PATCH", "spool/3", {"location": "Shelf B"})
        result, call = self.act({"action": "move", "id": 3, "location": ""})
        call.assert_called_once_with("PATCH", "spool/3", {"location": None})

    def test_add_spool_of_the_filament(self):
        result, call = self.act({"action": "add", "id": 3, "filament": 9}, answer={"id": 44})
        self.assertTrue(result["ok"])
        self.assertIn("#44", result["text"])
        call.assert_called_once_with("POST", "spool", {"filament_id": 9})

    def test_locations_lists_spoolmans_locations(self):
        result, call = self.act({"action": "locations"}, answer=["Shelf A", 5, "Shelf B"])
        call.assert_called_once_with("GET", "location")
        self.assertEqual(result["locations"], ["Shelf A", "Shelf B"])

    def test_open_in_spoolman(self):
        with mock.patch.object(sp, "open_url", return_value=True) as opened:
            result = sp.spool_action({"action": "open", "id": 12})
        self.assertTrue(result["ok"])
        opened.assert_called_once_with("http://spoolman:7912/spool/show/12")

    def test_bad_input_never_reaches_spoolman(self):
        bad = [
            None, "archive", {"action": "nuke", "id": 1},
            {"action": "archive"}, {"action": "archive", "id": "3"}, {"action": "archive", "id": True},
            {"action": "archive", "id": 2.5}, {"action": "archive", "id": 0}, {"action": "archive", "id": -4},
            {"action": "weigh", "id": 1, "grams": "nan"}, {"action": "weigh", "id": 1, "grams": "inf"},
            {"action": "weigh", "id": 1, "grams": -5}, {"action": "weigh", "id": 1, "grams": 1e9},
            {"action": "weigh", "id": 1, "grams": True}, {"action": "use", "id": 1, "grams": 0},
            {"action": "use", "id": 1}, {"action": "move", "id": 1, "location": "x" * 65},
            {"action": "move", "id": 1, "location": 5}, {"action": "add", "id": 1, "filament": "9"},
            {"action": "add", "id": 1},
        ]
        for data in bad:
            result, call = self.act(data)
            self.assertFalse(result["ok"], data)
            self.assertTrue(result["text"], data)
            call.assert_not_called()

    def test_bambu_source_gets_no_write_actions(self):
        sp.save_settings({**sp.get_settings(), "spool_source": "bambu"})
        result, call = self.act({"action": "archive", "id": 3})
        self.assertFalse(result["ok"])
        call.assert_not_called()

    def test_spoolman_errors_become_the_result_text(self):
        error = sp.urllib.error.HTTPError("u", 400, "Bad", {}, None)
        error.read = lambda: json.dumps({"message": "Initial weight is not set."}).encode()
        with mock.patch.object(sp, "spoolman_call", side_effect=error):
            result = sp.spool_action({"action": "weigh", "id": 1, "grams": 900})
        self.assertFalse(result["ok"])
        self.assertIn("HTTP 400", result["text"])
        self.assertIn("Initial weight is not set.", result["text"])

    def test_show_archived_is_a_display_flag(self):
        self.assertFalse(sp.display_settings()["archived"])
        result, call = self.act({"action": "show_archived", "on": True})
        self.assertTrue(result["ok"])
        self.assertTrue(sp.display_settings()["archived"])
        call.assert_not_called()


class Response:
    def __init__(self, body):
        self.body = json.dumps(body).encode()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False

    def read(self):
        return self.body


SPOOLS = [{"id": 1, "remaining_weight": 500, "filament": {"id": 5}},
          {"id": 2, "remaining_weight": 800, "archived": True, "filament": {"id": 6}}]


class OpenerTest(Settings):
    def fetch(self, body=SPOOLS):
        seen = []

        def urlopen(request, timeout):
            seen.append(request)
            return Response(body)
        with mock.patch.object(sp.urllib.request, "urlopen", urlopen):
            result = sp.get_spools("http://spoolman:7912/")
        return result, seen

    def test_archived_spools_are_fetched_only_when_shown(self):
        _, seen = self.fetch()
        self.assertEqual(seen[0].full_url, "http://spoolman:7912/api/v1/spool")
        sp.spool_action({"action": "show_archived", "on": True})
        _, seen = self.fetch()
        self.assertEqual(seen[0].full_url, "http://spoolman:7912/api/v1/spool?allow_archived=true")

    def test_the_cache_holds_only_active_spools(self):
        result, _ = self.fetch()
        self.assertEqual([s["id"] for s in result["spools"]], [1, 2])  # the page shows both
        self.assertEqual([s["id"] for s in sp._spool_cache["spools"]], [1])  # the rest of Spooler: active only
        self.assertEqual([s["id"] for s in sp.plate_spools("http://spoolman:7912/")], [1])

    def test_spoolman_call_sends_method_path_and_body(self):
        seen = []

        def urlopen(request, timeout):
            seen.append(request)
            return Response({"id": 3})
        with mock.patch.object(sp.urllib.request, "urlopen", urlopen):
            self.assertEqual(sp.spoolman_call("PATCH", "spool/3", {"archived": True}), {"id": 3})
        self.assertEqual((seen[0].get_method(), seen[0].full_url), ("PATCH", "http://spoolman:7912/api/v1/spool/3"))
        self.assertEqual(json.loads(seen[0].data), {"archived": True})


class ArchivedStayOutTest(Settings):
    def test_profiles_and_plate_ignore_archived_spools(self):
        with mock.patch.object(sp, "load_spools", return_value={"ok": True, "spools": SPOOLS}), \
                mock.patch.object(sp, "profile_sync", return_value={"count": 1, "error": ""}) as sync:
            result = sp.load_spools_synced({"printers": []})
        self.assertEqual([s["id"] for s in result["spools"]], [1, 2])
        self.assertEqual([s["id"] for s in sync.call_args[0][0]], [1])
        slot = {"preset": "", "vendor": "", "material": "", "colour": "", "sub_type": ""}
        self.assertNotIn(2, [s["id"] for s in sp.match_spools(slot, SPOOLS)])
        self.assertIsNone(sp._spool_by_id(2, SPOOLS))

    def test_u1_binding_flag(self):
        self.assertTrue(sp.u1_bound("Snapmaker U1 T2"))
        self.assertTrue(sp.u1_bound("U1 T0"))
        self.assertFalse(sp.u1_bound("Shelf T2"))
        self.assertFalse(sp.u1_bound(None))


if __name__ == "__main__":
    unittest.main()
