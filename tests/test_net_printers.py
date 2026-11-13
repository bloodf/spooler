"""PrusaLink and OctoPrint printers, Klipper progress and booking, and filling toolheads from a slice."""
import io
import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()

SPOOLS = [
    {"id": 5, "remaining_weight": 800, "filament": {"id": 1, "name": "PLA Red", "material": "PLA", "color_hex": "FF0000",
                                                    "vendor": {"name": "Acme"}}},
    {"id": 6, "remaining_weight": 500, "filament": {"id": 2, "name": "PETG Blue", "material": "PETG", "color_hex": "0000FF",
                                                    "vendor": {"name": "Acme"}}},
    {"id": 7, "remaining_weight": 400, "filament": {"id": 3, "name": "PETG Blue 2", "material": "PETG", "color_hex": "0000FF",
                                                    "vendor": {"name": "Other"}}},
]


class ParsePrintersTest(unittest.TestCase):
    def test_network_types_hosts_and_toolheads(self):
        out = sp.parse_printers([
            {"id": "a", "name": "MK4", "type": "prusalink", "user": "maker", "ip": "http://10.0.0.5:8080/", "serial": "X1",
             "units": [{"kind": "tool", "slots": ["5"]}, {"kind": "tool", "slots": [None]}]},
            {"id": "b", "type": "octoprint", "ip": "https://octo.local", "user": "ignored", "slice_fill": False},
            {"id": "c", "type": "weird", "ip": "10.0.0.9:80", "user": "x"},
        ])
        a, b, c = out
        self.assertEqual((a["type"], a["user"], a["ip"], a["serial"]), ("prusalink", "maker", "10.0.0.5:8080", ""))
        self.assertEqual([u["kind"] for u in a["units"]], ["tool", "tool"])
        self.assertEqual(a["units"][0]["slots"], ["5"])
        self.assertTrue(a["slice_fill"])
        self.assertEqual((b["type"], b["user"], b["ip"], b["slice_fill"]), ("octoprint", "", "https://octo.local", False))
        # unknown type is Bambu, whose address can't carry a port
        self.assertEqual((c["type"], c["ip"], c["user"]), ("bambu", "", ""))

    def test_bad_hosts(self):
        for ip in ("ftp://x", "a b", "x:999999", "x/../y"):
            self.assertEqual(sp.clean_host(ip, port=True), "", ip)
        self.assertEqual(sp.clean_host("printer.lan:5000", port=True), "printer.lan:5000")


class CodesTest(unittest.TestCase):
    def test_long_api_key_kept_for_network_printers(self):
        saved = {}
        cfg = [{"id": "o", "type": "octoprint"}, {"id": "b", "type": "bambu"}]
        with mock.patch.object(sp, "printers_cfg", return_value=cfg), mock.patch.object(sp, "read_codes", return_value={}), \
             mock.patch.object(sp, "write_codes", side_effect=saved.update), mock.patch.object(sp, "source", return_value="spoolman"):
            sp.save_printer_code("o", "A" * 40 + " ")
            sp.save_printer_code("b", "1234 5678" + "9" * 40)
        self.assertEqual(saved["spoolman:o"], "A" * 40)
        self.assertEqual(saved["spoolman:b"], ("12345678" + "9" * 40)[:32])


class StateMappingTest(unittest.TestCase):
    def test_prusalink(self):
        job = {"id": 42, "progress": 37.6, "time_remaining": 1800,
               "file": {"name": "BENCHY~1.GCO", "display_name": "benchy_0.4n.gcode", "path": "/usb",
                        "refs": {"download": "/usb/BENCHY~1.GCO"}}}
        out = sp.prusalink_job({"printer": {"state": "PRINTING"}, "job": {"id": 42}}, job)
        self.assertEqual(out, {"gcode_state": "RUNNING", "mc_percent": 38, "subtask_name": "benchy_0.4n",
                               "gcode_file": "/usb/BENCHY~1.GCO", "task_id": "42", "mc_remaining_time": 30,
                               "download": "/usb/BENCHY~1.GCO"})
        states = {k: sp.prusalink_job({"printer": {"state": k}, "job": {"id": 1}}, {"id": 1})["gcode_state"]
                  for k in ("PAUSED", "ATTENTION", "BUSY", "FINISHED", "STOPPED", "ERROR", "IDLE", "READY", "??")}
        self.assertEqual(states, {"PAUSED": "PAUSE", "ATTENTION": "PAUSE", "BUSY": "PREPARE", "FINISHED": "FINISH",
                                  "STOPPED": "FAILED", "ERROR": "FAILED", "IDLE": "IDLE", "READY": "IDLE", "??": "IDLE"})
        # busy without a job (homing from the menu) is not a print starting
        self.assertEqual(sp.prusalink_job({"printer": {"state": "BUSY"}}, {})["gcode_state"], "IDLE")

    def test_octoprint_states(self):
        cases = [("Printing", 10, True, "RUNNING"), ("Printing from SD", 10, True, "RUNNING"), ("Finishing", 99, True, "RUNNING"),
                 ("Resuming", 50, True, "RUNNING"), ("Starting print from SD", 0, True, "PREPARE"), ("Starting", 0, True, "PREPARE"),
                 ("Pausing", 5, True, "PAUSE"), ("Paused", 5, True, "PAUSE"), ("Cancelling", 5, True, "FAILED"),
                 ("Error: thermal runaway", 5, True, "FAILED"), ("Offline after error", None, False, "FAILED"),
                 ("Operational", 100.0, True, "FINISH"), ("Operational", 40.0, True, "IDLE"), ("Operational", None, False, "IDLE"),
                 ("Offline", None, False, "IDLE")]
        for text, pct, has, want in cases:
            self.assertEqual(sp.octoprint_state(text, pct, has), want, text)

    def test_octoprint_job(self):
        out = sp.octoprint_job({"state": "Printing", "progress": {"completion": 12.4, "printTimeLeft": 3600},
                                "job": {"file": {"name": "cube.gcode", "path": "parts/cube.gcode", "origin": "local", "date": 1700}}})
        self.assertEqual(out, {"gcode_state": "RUNNING", "mc_percent": 12, "subtask_name": "cube", "gcode_file": "parts/cube.gcode",
                               "task_id": "parts/cube.gcode@1700", "mc_remaining_time": 60,
                               "download": "/downloads/files/local/parts/cube.gcode"})
        sd = sp.octoprint_job({"state": "Printing from SD", "job": {"file": {"name": "a.gco", "path": "a.gco", "origin": "sdcard"}}})
        self.assertNotIn("download", sd)


class NetDocTest(unittest.TestCase):
    def test_toolheads_from_assigned_spools(self):
        printer = {"units": [{"kind": "tool", "slots": ["5"]}, {"kind": "tool", "slots": [None]}, {"kind": "ext", "slots": ["6"]}]}
        doc, heads = sp.net_doc({"gcode_state": "RUNNING", "download": "/x"}, printer, SPOOLS)
        self.assertTrue(heads)
        trays = doc["print"]["ams"]["ams"][0]["tray"]
        self.assertEqual([t.get("spool_id") for t in trays], [5, None])
        self.assertNotIn("tray_now", doc["print"]["ams"])   # two toolheads: which one prints is unknown
        self.assertEqual(doc["print"]["vt_tray"]["spool_id"], 6)
        self.assertNotIn("download", doc["print"])

    def test_single_toolhead_is_the_active_one(self):
        doc, heads = sp.net_doc({"gcode_state": "IDLE"}, {"units": [{"kind": "tool", "slots": ["5"]}]}, SPOOLS)
        self.assertEqual(doc["print"]["ams"]["tray_now"], "0")

    def test_live_snapshot_shows_one_toolhead(self):
        doc, heads = sp.net_doc({"gcode_state": "IDLE"}, {"units": [{"kind": "tool", "slots": ["5"]}]}, SPOOLS)
        with mock.patch.dict(sp._live["printers"], clear=True):
            sp.live_apply("pnet", "MK4", doc, link="pnet", full=True)
            sp._live["printers"]["pnet"].update(heads=True, head_count=1)
            snap = [p for p in sp.live_snapshot()["printers"] if p["id"] == "pnet"][0]
        self.assertTrue(snap["heads"])
        self.assertEqual(len(snap["units"][0]["trays"]), 1)
        self.assertEqual(snap["units"][0]["trays"][0]["spool"], 5)


class FakeResp(io.BytesIO):
    def __init__(self, data, status):
        super().__init__(data)
        self.status = status


class TailTest(unittest.TestCase):
    FOOTER = ("; filament used [mm] = 100.0, 0.0, 20.0\n"
              "; filament used [g] = 12.5, 0.00, 3.25\n"
              "; CONFIG_BLOCK_START\n"
              "; filament_colour = #FF0000;#00FF00;#0000ff\n"
              "; filament_settings_id = \"Acme PLA\";\"x\";\"Acme PETG\"\n"
              "; filament_type = PLA;PLA;PETG\n"
              "; CONFIG_BLOCK_END\n")

    def test_parse(self):
        items = sp.parse_gcode_tail(("G1 X1\n" + self.FOOTER).splitlines())
        self.assertEqual(items, [{"n": 1, "grams": 12.5, "preset": "Acme PLA", "colour": "FF0000", "material": "PLA"},
                                 {"n": 3, "grams": 3.25, "preset": "Acme PETG", "colour": "0000FF", "material": "PETG"}])
        self.assertIsNone(sp.parse_gcode_tail(["G1 X1", "; generated by Cura"]))

    def test_range_answer_and_ignored_range(self):
        data = b"x" * 3000 + b"TAIL"
        self.assertEqual(sp.read_http_tail(FakeResp(data[-100:], 206), size=100), data[-100:])
        self.assertEqual(sp.read_http_tail(FakeResp(data, 200), size=100), data[-100:])
        self.assertIsNone(sp.read_http_tail(FakeResp(data, 200), size=100, cap=1000))

    def test_fetch_reads_the_tail_and_skips_binary(self):
        seen = []

        def opener(link, path, headers=None):
            seen.append((path, headers))
            return FakeResp(self.FOOTER.encode(), 206)
        items = sp._gcode_tail_items({"kind": "octoprint"}, "/downloads/files/local/a.gcode", opener)
        self.assertEqual([i["grams"] for i in items], [12.5, 3.25])
        self.assertEqual(seen[0][1], {"Range": f"bytes=-{sp.NET_TAIL}"})
        self.assertIsNone(sp._gcode_tail_items({}, "/usb/A.BGCODE", opener))
        self.assertIsNone(sp._gcode_tail_items({}, "/x.gcode", lambda *a, **k: FakeResp(b"GCDE\x01binary", 206)))

    def test_request_stays_on_the_printer(self):
        for bad in ("//evil.example/x", "http://evil.example/x", "x"):
            with self.assertRaises(ValueError):
                sp._net_request({"kind": "octoprint", "ip": "10.0.0.2"}, bad)


class AuthTest(unittest.TestCase):
    def test_401_is_an_auth_error(self):
        def refuse(self_, req, timeout=None):
            raise sp.urllib.error.HTTPError(req.full_url, 401, "Unauthorized", {}, None)
        with mock.patch.object(sp.urllib.request.OpenerDirector, "open", refuse):
            with self.assertRaises(sp.NetAuthError):
                sp.net_json({"kind": "octoprint", "ip": "10.0.0.2", "code": "k"}, "/api/job")

    def test_api_key_header_and_digest(self):
        reqs = []

        def capture(self_, req, timeout=None):
            reqs.append((req, [type(h).__name__ for h in self_.handlers]))
            return FakeResp(b'{"state": "Operational"}', 200)
        with mock.patch.object(sp.urllib.request.OpenerDirector, "open", capture):
            sp.net_json({"kind": "octoprint", "ip": "10.0.0.2:5000", "code": "KEY"}, "/api/job")
            sp.net_json({"kind": "prusalink", "ip": "10.0.0.3", "user": "maker", "code": "pw"}, "/api/v1/status")
        self.assertEqual(reqs[0][0].full_url, "http://10.0.0.2:5000/api/job")
        self.assertEqual(reqs[0][0].get_header("X-api-key"), "KEY")
        self.assertIsNone(reqs[1][0].get_header("X-api-key"))
        self.assertIn("HTTPDigestAuthHandler", reqs[1][1])


class MoonrakerTest(unittest.TestCase):
    def test_progress(self):
        out = sp.moon_progress({"print_stats": {"state": "printing", "filename": "parts/cube.gcode", "print_duration": 600},
                                "virtual_sdcard": {"progress": 0.25}})
        self.assertEqual(out, {"gcode_state": "RUNNING", "gcode_file": "parts/cube.gcode", "subtask_name": "cube",
                               "mc_percent": 25, "mc_remaining_time": 30})
        self.assertEqual({k: sp.moon_progress({"print_stats": {"state": k}})["gcode_state"]
                          for k in ("standby", "paused", "complete", "cancelled", "error")},
                         {"standby": "IDLE", "paused": "PAUSE", "complete": "FINISH", "cancelled": "FAILED", "error": "FAILED"})
        self.assertEqual(sp.moon_progress({}), {})

    def test_metadata_items(self):
        items = sp.moon_items({"filament_weights": [10.0, 0, 4.5], "filament_type": "PLA;PLA;PETG",
                               "filament_colors": ["#FF0000", "#000000", "#0000FF"], "filament_name": "Red;Black;Blue"})
        self.assertEqual(items, [{"n": 1, "grams": 10.0, "preset": "Red", "colour": "FF0000", "material": "PLA"},
                                 {"n": 3, "grams": 4.5, "preset": "Blue", "colour": "0000FF", "material": "PETG"}])
        self.assertEqual(sp.moon_items({"filament_weight_total": 7.0, "filament_type": "PLA"})[0]["grams"], 7.0)
        self.assertIsNone(sp.moon_items({}))

    def test_spoolman_status(self):
        with mock.patch.object(sp, "_moon_get", return_value={"spoolman_connected": True}):
            self.assertTrue(sp.moon_spoolman_connected("http://k"))
        err = sp.urllib.error.HTTPError("u", 404, "nf", {}, None)
        with mock.patch.object(sp, "_moon_get", side_effect=err):
            self.assertFalse(sp.moon_spoolman_connected("http://k"))

    def test_klipper_booked_only_when_allowed(self):
        def state(book_ok):
            return {"name": "K1", "link": "auto-k", "units": {}, "ext": {}, "book_ok": book_ok,
                    "job": {"gcode_state": "RUNNING", "mc_percent": 1, "subtask_name": "cube", "gcode_file": "cube.gcode"}}
        store = {"prints": [], "active": {}, "last": {}, "done": []}
        with mock.patch.object(sp, "source", return_value="spoolman"), mock.patch.object(sp, "usage_mode", return_value="auto"), \
             mock.patch.object(sp, "usage_load", return_value=store):
            self.assertEqual(sp.usage_track("auto-k", state(False), True), [])
            events = sp.usage_track("auto-k", state(True), True)
        start = [e for e in events if e[0] == "start"]
        self.assertEqual(len(start), 1)
        self.assertTrue(start[0][2]["ask"])


class NeverAutoBookTest(unittest.TestCase):
    def test_ask_only_kinds(self):
        items = [{"n": 1, "grams": 10.0, "preset": "", "material": "PLA", "colour": "FF0000"}]
        for dev, ask in (("auto-k", False), ("pnet", True)):
            booked = []
            run = {"id": f"r-{dev}", "file": items, "plan": None, "job": {}, "pct": 100, "result": "finished", "printer": "P",
                   "name": "x", "late": False, "trays": [{"key": 0, "spool_id": 5}], "ask": ask}
            store = {"prints": [], "active": {}, "last": {}, "done": []}
            with mock.patch.object(sp, "usage_load", return_value=store), mock.patch.object(sp, "usage_save"), \
                 mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)), \
                 mock.patch.object(sp, "plate_spools", return_value=SPOOLS), mock.patch.object(sp, "usage_mode", return_value="auto"), \
                 mock.patch.object(sp, "usage_book", side_effect=lambda *a: booked.append(a) or ""):
                sp.usage_finish(run, dev)
            self.assertEqual(booked, [], dev)
            self.assertEqual(store["prints"][0]["rows"][0]["spool"], 5)   # matched from the toolhead's spool

    def test_bambu_still_auto_books(self):
        booked = []
        run = {"id": "r-b", "file": [{"n": 1, "grams": 10.0, "preset": "", "material": "PLA", "colour": "FF0000"}], "plan": None,
               "job": {}, "pct": 100, "result": "finished", "printer": "X1", "name": "x", "late": False, "trays": []}
        store = {"prints": [], "active": {}, "last": {}, "done": []}
        with mock.patch.object(sp, "usage_load", return_value=store), mock.patch.object(sp, "usage_save"), \
             mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)), \
             mock.patch.object(sp, "plate_spools", return_value=SPOOLS), mock.patch.object(sp, "usage_mode", return_value="auto"), \
             mock.patch.object(sp, "usage_book", side_effect=lambda *a: booked.append(a) or ""):
            sp.usage_finish(run, "p1")
        self.assertEqual(len(booked), 1)


class SliceFillTest(unittest.TestCase):
    def setUp(self):
        self.settings = {"printers": {"spoolman": [
            {"id": "mk4", "name": "MK4", "type": "prusalink", "ip": "10.0.0.5", "units": [
                {"kind": "tool", "slots": [None]}, {"kind": "tool", "slots": [None]}]},
            {"id": "x1", "name": "X1", "type": "bambu", "ip": "10.0.0.7", "units": [{"kind": "ams", "slots": ["5", None, None, None]}]},
        ]}}
        self.saved = []
        patches = [mock.patch.object(sp, "get_settings", lambda: self.settings), mock.patch.object(sp, "source", return_value="spoolman"),
                   mock.patch.object(sp, "save_printers", side_effect=self.saved.append)]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def slot(self, n, material, colour, grams=5.0):
        return {"n": n, "grams": grams, "preset": "", "colour": colour, "material": material, "vendor": ""}

    def test_unique_match_moves_the_spool(self):
        changed = sp.slice_fill([self.slot(1, "PLA", "#FF0000")], "http://10.0.0.5", SPOOLS)
        self.assertTrue(changed)
        saved = {p["id"]: p for p in self.saved[0]}
        self.assertEqual(saved["mk4"]["units"][0]["slots"], ["5"])
        self.assertEqual(saved["x1"]["units"][0]["slots"], [None, None, None, None])   # moved off the AMS

    def test_ambiguous_left_alone(self):
        self.assertFalse(sp.slice_fill([self.slot(1, "PETG", "#0000FF")], "http://10.0.0.5", SPOOLS))
        self.assertEqual(self.saved, [])

    def test_bambu_and_unknown_hosts_untouched(self):
        self.assertFalse(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], "http://10.0.0.7", SPOOLS))
        self.assertFalse(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], "http://10.9.9.9", SPOOLS))
        self.assertEqual(self.saved, [])

    def test_more_filaments_than_toolheads(self):
        self.assertFalse(sp.slice_fill([self.slot(3, "PLA", "#FF0000")], "http://10.0.0.5", SPOOLS))

    def test_opt_out(self):
        self.settings["printers"]["spoolman"][0]["slice_fill"] = False
        self.assertFalse(sp.slice_fill([self.slot(1, "PLA", "#FF0000")], "http://10.0.0.5", SPOOLS))


class SyncStartsNetLinksTest(unittest.TestCase):
    def test_net_printer_with_code_gets_a_link(self):
        started = []
        cfg = [{"id": "o", "type": "octoprint", "kind": None, "ip": "10.0.0.2:5000", "user": "", "name": "Octo", "units": []},
               {"id": "n", "type": "prusalink", "ip": "10.0.0.3", "user": "maker", "name": "NoCode", "units": []}]

        def fake(pid, link, stop):
            started.append((pid, link))
        with mock.patch.object(sp, "printers_cfg", return_value=cfg), \
             mock.patch.object(sp, "read_codes", return_value={sp._code_key("o"): "KEY"}), \
             mock.patch.object(sp, "_net_run", fake), mock.patch.dict(sp._local, clear=True):
            sp._local_sync()
            for e in sp._local.values():
                e["thread"].join(2)
        self.assertEqual(started, [("o", {"kind": "octoprint", "ip": "10.0.0.2:5000", "user": "", "code": "KEY", "name": "Octo"})])
