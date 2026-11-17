"""New RFID spools: a Bambu RFID spool in an AMS slot or the external holder that no Spoolman spool
carries is offered on the Printer tab, Skip remembers it per printer, and Add Spool stores the tag
where Spooler matches RFID spools. The printer report is a mock in Bambu's push_status shape
(tests/fixtures/bambu_rfid_report.json); Spoolman is a stand-in; nothing reaches the network."""

import json
import unittest
from pathlib import Path
from unittest import mock

import spoolman_rules as rules
from test_spool_actions import Settings, sp

REPORT = json.loads((Path(__file__).parent / "fixtures" / "bambu_rfid_report.json").read_text(encoding="utf-8"))
TRAYS = {tray["id"]: tray for tray in REPORT["print"]["ams"]["ams"][0]["tray"]}
MATTE = "7A1F3B9C2D4E4F60A1B2C3D4E5F60718"   # slot 1: the RFID spool no Spoolman spool carries
BASIC = "11223344556677889900AABBCCDDEEFF"   # slot 4: already a Spoolman spool
SILK = "CAFE0000BEEF11112222333344445555"    # the external holder: a multi-colour RFID spool
LINKED = {"id": 3, "remaining_weight": 450, "extra": {"tag": json.dumps(BASIC)},
          "filament": {"id": 1, "name": "PLA Basic White", "material": "PLA", "vendor": {"name": "Bambu Lab"}}}


class OfferTest(unittest.TestCase):
    def test_an_rfid_tray_offers_what_the_printer_reports(self):
        offer = sp.rfid_offer(TRAYS["0"], set())
        self.assertEqual(offer, {"tag": MATTE, "type": "PLA", "name": "PLA Matte", "colours": ["3C3C3C"], "remain": 80.0,
                                 "weight": 1000.0, "diameter": 1.75, "nozzle": [190, 230]})

    def test_a_multi_colour_spool_reports_every_colour(self):
        offer = sp.rfid_offer(REPORT["print"]["vt_tray"], set())
        self.assertEqual(offer["colours"], ["EC984C", "6CD4BC", "A66EB9"])
        self.assertEqual(offer["weight"], 250.0)

    def test_no_offer_for_a_non_rfid_an_empty_or_an_unknown_tray(self):
        self.assertIsNone(sp.rfid_offer(TRAYS["1"], set()), "third-party spool: the tags are all zeros")
        self.assertIsNone(sp.rfid_offer(TRAYS["2"], set()), "empty slot")
        self.assertIsNone(sp.rfid_offer({**TRAYS["0"], "tray_type": ""}, set()), "no material: nothing loaded")
        self.assertIsNone(sp.rfid_offer(None, set()))
        self.assertIsNone(sp.rfid_offer("tray", set()))
        # Other printers' trays (Snapmaker U1, Klipper lanes) carry a tag_uid but none of Bambu's fields.
        self.assertIsNone(sp.rfid_offer({"tray_type": "PLA", "tag_uid": "60827A6A", "spool_id": None}, set()))
        self.assertIsNone(sp.rfid_offer({**TRAYS["0"], "spool_id": 12}, set()), "the tray names its spool itself")

    def test_the_tag_is_the_tray_uuid_else_the_chip_uid(self):
        self.assertEqual(sp.tray_tag(TRAYS["0"]), MATTE)
        self.assertEqual(sp.tray_tag({**TRAYS["0"], "tray_uuid": "0" * 32}), "5E2A41C900000100")
        self.assertEqual(sp.tray_tag(TRAYS["1"]), "")

    def test_values_the_printer_doesnt_know_stay_empty(self):
        tray = {**TRAYS["0"], "remain": -1, "tray_weight": "abc", "tray_diameter": "0.00", "nozzle_temp_min": "240",
                "nozzle_temp_max": "200", "tray_color": "", "cols": "x"}
        offer = sp.rfid_offer(tray, set())
        self.assertEqual({k: offer[k] for k in ("remain", "weight", "diameter", "nozzle", "colours")},
                         {"remain": None, "weight": None, "diameter": None, "nozzle": None, "colours": []})
        self.assertEqual(sp.rfid_offer({**TRAYS["0"], "remain": True, "tray_weight": 1e9}, set())["weight"], None)

    def test_no_offer_when_a_spool_already_carries_the_tag(self):
        self.assertIsNone(sp.rfid_offer(TRAYS["0"], {MATTE}))
        self.assertIsNone(sp.rfid_offer(TRAYS["0"], {"5E2A41C900000100"}), "a spool tagged with the chip uid")


class OffersTest(Settings):
    def setUp(self):
        super().setUp()
        self.live = mock.patch.dict(sp._live["printers"], clear=True)
        self.live.start()
        sp.live_apply("p1", "X1C", REPORT, link="p1")
        self.cache(spools=[LINKED])

    def tearDown(self):
        self.live.stop()
        super().tearDown()

    def cache(self, **values):
        patch = mock.patch.dict(sp._spool_cache, {"url": sp.current_origin()[0], "time": 1.0, **values})
        patch.start()
        self.addCleanup(patch.stop)

    def tags(self):
        return [(o["printer"], o["unit"], o["slot"], o["tag"]) for o in sp.rfid_offers()]

    def test_offers_the_new_rfid_spools_with_their_slot(self):
        self.assertEqual(self.tags(), [("p1", 0, 0, MATTE), ("p1", "ext", 0, SILK)])

    def test_a_tag_stored_by_another_tool_is_known_too(self):
        self.cache(spools=[LINKED, {"id": 4, "extra": {"rfid": json.dumps("5E2A41C900000100")}}])
        self.assertEqual(self.tags(), [("p1", "ext", 0, SILK)])

    def test_nothing_is_offered_before_the_spool_list_was_read_again(self):
        self.cache(time=0.0)   # a spool was just added: its tag isn't in the list read before
        self.assertEqual(sp.rfid_offers(), [])
        self.cache(url="http://other:7912")
        self.assertEqual(sp.rfid_offers(), [])

    def test_nothing_is_offered_with_bambu_cloud_as_the_source(self):
        sp.save_settings({**sp.get_settings(), "spool_source": "bambu"})
        self.assertEqual(sp.rfid_offers(), [])

    def test_skip_is_remembered_per_printer_and_settings_can_ask_again(self):
        sp.live_apply("p2", "P1S", {"print": {"ams": {"ams": [{"id": "0", "tray": [TRAYS["0"]]}]}}}, link="p2")
        self.assertTrue(sp.rfid_skip("p1", MATTE.lower()))
        self.assertEqual(self.tags(), [("p1", "ext", 0, SILK), ("p2", 0, 0, MATTE)], "still asked in the other printer")
        self.assertTrue(sp.rfid_skip("p1", MATTE))
        self.assertEqual(sp.rfid_skipped_count(), 1, "skipped once")
        self.assertEqual(sp.get_settings()["spoolman_url"], "http://spoolman:7912", "the other settings stay")
        self.assertTrue(sp.rfid_unskip())
        self.assertEqual(sp.rfid_skipped_count(), 0)
        self.assertIn(("p1", 0, 0, MATTE), self.tags())

    def test_a_skip_by_the_chip_uid_holds_once_the_tray_uuid_shows(self):
        sp._live["printers"]["p1"]["units"][0][0]["tray_uuid"] = "0" * 32   # the first report: only the chip uid
        self.assertEqual(sp.rfid_offers()[0]["tag"], "5E2A41C900000100")
        self.assertTrue(sp.rfid_skip("p1", "5E2A41C900000100"))
        sp._live["printers"]["p1"]["units"][0][0]["tray_uuid"] = MATTE
        self.assertEqual(self.tags(), [("p1", "ext", 0, SILK)])

    def test_skip_refuses_what_isnt_a_printer_and_a_tag(self):
        for pid, tag in ((None, MATTE), ("", MATTE), ("x" * 65, MATTE), ("p1", "nope"), ("p1", None), ("p1", ["A" * 16])):
            self.assertFalse(sp.rfid_skip(pid, tag), (pid, tag))
        self.assertEqual(sp.rfid_skipped_count(), 0)

    def test_a_damaged_skip_list_reads_as_empty(self):
        sp.save_settings({**sp.get_settings(), sp.RFID_SKIP: ["bad"]})
        self.assertEqual(sp.rfid_skipped_count(), 0)
        sp.save_settings({**sp.get_settings(), sp.RFID_SKIP: {"p1": "bad", "p2": [MATTE, 3]}})
        self.assertEqual(sp.rfid_skipped_count(), 1)

    def test_the_live_poll_carries_the_offers(self):
        with mock.patch.object(sp, "_local_sync"):
            self.assertEqual([o["tag"] for o in sp.live_message()["rfid"]], [MATTE, SILK])

    def test_the_printer_gets_nothing(self):
        with mock.patch.object(sp, "spoolman_call") as call:
            sp.rfid_offers()
        call.assert_not_called()


SPOOL_FIELDS = [{"key": "dryer", "name": "Dryer", "field_type": "text"}]


class Spoolman:
    """A stand-in Spoolman for Add Spool with a tag: its spools, its spool fields, and every write."""

    def __init__(self, spools=(), fields=SPOOL_FIELDS):
        self.spools, self.fields, self.writes = [json.loads(json.dumps(s)) for s in spools], list(fields), []

    def __call__(self, method, path, body=None):
        if method == "GET":
            return json.loads(json.dumps({"field/spool": self.fields, "field/filament": [], "spool?allow_archived=true": self.spools, "vendor": []}[path]))
        self.writes.append((method, path, body))
        if path.startswith("field/spool/"):
            self.fields.append({"key": path.rsplit("/", 1)[1], **body})
        elif path == "vendor":
            return {"id": 3}
        elif path == "filament":
            rules.check_filament_body(body)
            return {"id": 21}
        elif path == "spool":
            known = {f["key"] for f in self.fields}
            if set(body.get("extra") or {}) - known:
                raise rules.refuse(400, "Unknown extra field")
            self.spools.append({"id": 44, **body})
            return {"id": 44}
        return {}


class CreateTest(Settings):
    def create(self, data, server=None):
        server = server or Spoolman()
        with mock.patch.object(sp, "spoolman_call", server):
            return sp.spool_action({"action": "create", **data}), server

    def test_add_stores_the_tag_so_the_tray_matches_the_new_spool(self):
        result, server = self.create({"filament_id": 9, "tag": MATTE, "spool": {"initial_weight": 1000, "remaining_weight": 800,
                                                                                  "extra": {"dryer": "Box 1"}}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes, [
            ("POST", "field/spool/tag", {"name": "RFID tag", "field_type": "text", "order": 101}),
            ("POST", "spool", {"filament_id": 9, "initial_weight": 1000.0, "remaining_weight": 800.0,
                               "extra": {"dryer": '"Box 1"', "tag": json.dumps(MATTE)}})])
        self.assertEqual(sp.match_spool(TRAYS["0"], server.spools)["id"], 44, "recognised from now on, and booked")

    def test_add_with_a_new_filament_checks_the_tag_before_writing_anything(self):
        server = Spoolman(fields=SPOOL_FIELDS + [{"key": "tag", "name": "Tag", "field_type": "text"}])
        result, server = self.create({"tag": MATTE.lower(), "spool": {}, "filament": {
            "vendor": "Bambu Lab", "material": "PLA", "color_hex": "3C3C3C", "density": 1.24, "diameter": 1.75}}, server)
        self.assertTrue(result["ok"], result)
        self.assertEqual([w[1] for w in server.writes], ["vendor", "filament", "spool"], "the field is there already")
        self.assertEqual(server.writes[-1][2]["extra"], {"tag": json.dumps(MATTE)})

    def test_a_tag_on_another_spool_stops_the_add(self):
        result, server = self.create({"filament_id": 9, "tag": BASIC, "spool": {}}, Spoolman(spools=[LINKED]))
        self.assertFalse(result["ok"])
        self.assertIn("#3", result["text"])
        self.assertEqual(server.writes, [])

    def test_an_archived_spool_with_the_tag_stops_the_add(self):
        result, server = self.create({"filament_id": 9, "tag": BASIC, "spool": {}}, Spoolman(spools=[{**LINKED, "archived": True}]))
        self.assertFalse(result["ok"])
        self.assertIn("#3", result["text"])
        self.assertIn("unarchive", result["text"])
        self.assertEqual(server.writes, [])

    def test_a_tag_field_of_another_type_stops_the_add(self):
        result, server = self.create({"filament_id": 9, "tag": MATTE, "spool": {}},
                                     Spoolman(fields=[{"key": "tag", "name": "Tag", "field_type": "integer"}]))
        self.assertFalse(result["ok"])
        self.assertIn("tag", result["text"])
        self.assertEqual(server.writes, [])

    def test_a_tag_that_isnt_one_is_refused(self):
        for tag in ("", "xyz", "0" * 32, 123, ["A" * 16], {"uid": "A" * 16}):
            result, server = self.create({"filament_id": 9, "tag": tag, "spool": {}})
            self.assertFalse(result["ok"], tag)
            self.assertEqual(server.writes, [], tag)

    def test_the_page_still_cant_write_the_tag_as_an_extra_field(self):
        result, server = self.create({"filament_id": 9, "spool": {"extra": {"tag": MATTE}}},
                                     Spoolman(fields=[{"key": "tag", "name": "Tag", "field_type": "text"}]))
        self.assertFalse(result["ok"])
        self.assertEqual(server.writes, [])

    def test_add_without_a_tag_is_unchanged(self):
        result, server = self.create({"filament_id": 9, "spool": {"remaining_weight": 500}})
        self.assertTrue(result["ok"], result)
        self.assertEqual(server.writes, [("POST", "spool", {"filament_id": 9, "remaining_weight": 500.0})])


if __name__ == "__main__":
    unittest.main()
