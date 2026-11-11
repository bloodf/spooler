import io
import json
import threading
import unittest
import urllib.error
from unittest import mock

import test_display
from plugin_loader import load
from test_kobra import FakeSocket

sp, orca = load()

SPOOLS = [
    {"id": 7, "archived": False, "remaining_weight": 500, "initial_weight": 1000,
     "filament": {"id": 3, "name": "Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
    {"id": 8, "archived": True, "remaining_weight": 0, "initial_weight": 1000,
     "filament": {"id": 3, "name": "Black", "material": "PLA", "color_hex": "111111", "vendor": {"name": "Acme"}}},
]
BASE = "http://10.0.0.5"
SV06 = {"ip": BASE, "name": "SV06", "kind": "moonraker"}


class Reply(io.BytesIO):
    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


class MoonPostTest(unittest.TestCase):
    def test_request_shape(self):
        seen = []

        def urlopen(req, timeout):
            seen.append((req, timeout))
            return Reply(b'{"result": {"spool_id": 7}}')
        with mock.patch.object(sp.urllib.request, "urlopen", urlopen):
            self.assertEqual(sp._moon_post(BASE, "/server/spoolman/spool_id", {"spool_id": 7}), {"spool_id": 7})
        req, timeout = seen[0]
        self.assertEqual(req.get_method(), "POST")
        self.assertEqual(req.full_url, BASE + "/server/spoolman/spool_id")
        self.assertEqual(req.get_header("Content-type"), "application/json")
        self.assertEqual(json.loads(req.data), {"spool_id": 7})
        self.assertEqual(timeout, sp.TIMEOUT)

    def test_errors_raise(self):
        def refused(req, timeout):
            raise urllib.error.HTTPError(req.full_url, 404, "Not Found", {}, None)
        with mock.patch.object(sp.urllib.request, "urlopen", refused):
            with self.assertRaises(urllib.error.HTTPError) as caught:
                sp._moon_post(BASE, "/server/spoolman/spool_id", {"spool_id": 7})
        caught.exception.close()


class MoonSpoolTest(unittest.TestCase):
    def setUp(self):
        sp._spool_cache["spools"] = SPOOLS
        sp._local["auto-sv"] = {"link": dict(SV06), "stop": threading.Event(), "thread": None}
        sp._live["printers"]["auto-sv"] = {"name": "SV06", "units": {}, "ext": {}, "time": 0.0, "link": "auto-sv",
                                          "spool_set": True}
        self.posts = []
        self.status = {}
        self.lanes = {}
        self.active = None
        patches = [
            mock.patch.object(sp, "source", lambda: "spoolman"),
            mock.patch.object(sp, "_moon_post", self.post),
            mock.patch.object(sp, "_moon_get", self.get),
            mock.patch.object(sp, "moon_lanes", lambda base: self.lanes),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def tearDown(self):
        sp._local.pop("auto-sv", None)
        sp._live["printers"].pop("auto-sv", None)

    def post(self, base, path, body):
        self.posts.append((base, path, body))
        self.active = body["spool_id"]
        return {"spool_id": body["spool_id"]}

    def get(self, base, path):
        if path.startswith("/printer/objects/query"):
            return {"status": self.status}
        return {"spool_id": self.active}

    def test_sets_and_refreshes(self):
        result = sp.moon_set_spool("auto-sv", 7)
        self.assertTrue(result["ok"], result)
        self.assertEqual(self.posts, [(BASE, "/server/spoolman/spool_id", {"spool_id": 7})])
        self.assertEqual(sp._live["printers"]["auto-sv"]["ext"]["spool_id"], 7)

    def test_clear_posts_null(self):
        result = sp.moon_set_spool("auto-sv", None)
        self.assertTrue(result["ok"], result)
        self.assertEqual(self.posts[0][2], {"spool_id": None})

    def test_refuses_bad_and_archived_ids(self):
        for bad in ("x", -1, 0, True, 1.5, "7; drop", 8, 999):
            result = sp.moon_set_spool("auto-sv", bad)
            self.assertFalse(result["ok"], bad)
        self.assertEqual(self.posts, [])

    def test_refuses_u1(self):
        self.status = {"print_task_config": {"filament_exist": [True, True, True, True]}}
        self.assertFalse(sp.moon_set_spool("auto-sv", 7)["ok"])
        self.assertEqual(self.posts, [])

    def test_refuses_lanes(self):
        self.lanes = {"lane1": {"lane": 0, "material": "PLA"}}
        self.assertFalse(sp.moon_set_spool("auto-sv", 7)["ok"])
        self.assertEqual(self.posts, [])

    def test_refuses_printers_without_the_single_extruder_card(self):
        sp._live["printers"]["auto-sv"]["spool_set"] = False  # e.g. an Anycubic printer
        self.assertFalse(sp.moon_set_spool("auto-sv", 7)["ok"])
        self.assertFalse(sp.moon_set_spool("unknown", 7)["ok"])
        self.assertEqual(self.posts, [])

    def test_refuses_bambu_source(self):
        with mock.patch.object(sp, "source", lambda: "bambu"):
            self.assertFalse(sp.moon_set_spool("auto-sv", 7)["ok"])
        self.assertEqual(self.posts, [])

    def test_printer_error_is_reported(self):
        def fail(base, path, body):
            raise urllib.error.URLError("down")
        with mock.patch.object(sp, "_moon_post", fail):
            result = sp.moon_set_spool("auto-sv", 7)
        self.assertFalse(result["ok"])

    def test_both_hosts_run_it_off_the_ui_thread(self):
        started = []
        with mock.patch.object(sp, "start_moon_spool", lambda data, post: started.append(data)):
            window = sp.SpoolerWindow.__new__(sp.SpoolerWindow)
            window._panel = mock.Mock()
            window.on_message({"type": "moon_spool", "id": "auto-sv", "spool": 7})
            page = sp.SpoolerPage.__new__(sp.SpoolerPage)
            page.on_message({"type": "moon_spool", "id": "auto-sv", "spool": 7})
        self.assertEqual(len(started), 2)

    def test_snapshot_flags_only_the_single_extruder_card(self):
        doc, heads = sp.moon_report({}, 7, SPOOLS)
        sp.live_apply("auto-x", "X", doc, link="auto-x")
        with sp._live_lock:
            sp.moon_mark("auto-x", doc, heads)
        try:
            flags = {p["id"]: p["spool_set"] for p in sp.live_snapshot()["printers"]}
            self.assertTrue(flags["auto-x"])
            self.assertTrue(flags["auto-sv"])
        finally:
            sp._live["printers"].pop("auto-x", None)
        lanes_doc, heads = sp.moon_report({}, None, SPOOLS, lanes={"a": {"lane": 0, "material": "PLA"}})
        sp.live_apply("auto-y", "Y", lanes_doc, link="auto-y")
        with sp._live_lock:
            sp.moon_mark("auto-y", lanes_doc, heads)
        try:
            self.assertFalse(next(p for p in sp.live_snapshot()["printers"] if p["id"] == "auto-y")["spool_set"])
        finally:
            sp._live["printers"].pop("auto-y", None)


class CaptureTest(unittest.TestCase):
    def test_logs_each_type_once_redacted(self):
        seen = set()
        doc = {"type": "info", "msgid": "abc", "data": {"state": "printing", "progress": 12,
                                                        "ip": "192.168.1.20", "device_sn": "ABC123",
                                                        "token": "s3cr3t", "url": "http://10.0.0.9/x",
                                                        "note": "from 10.1.2.3"}}
        with self.assertLogs(sp.log, "INFO") as logs:
            sp.kx_capture(doc, seen)
            sp.kx_capture(dict(doc, data={"progress": 50}), seen)
            sp.kx_capture({"type": "Print", "data": {"progress": 3}}, seen)
        self.assertEqual(len(logs.output), 2)
        text = "\n".join(logs.output)
        self.assertIn("printing", text)
        self.assertIn("progress", text)
        for secret in ("192.168.1.20", "ABC123", "s3cr3t", "10.0.0.9", "10.1.2.3"):
            self.assertNotIn(secret, text)

    def test_redact_long_ids(self):
        out = sp.kx_redact({"data": {"x": "0123456789abcdef0123", "list": [{"password": "p"}]}})
        self.assertNotIn("0123456789abcdef0123", json.dumps(out))
        self.assertNotIn('"p"', json.dumps(out))


class CaptureSessionTest(unittest.TestCase):
    def session(self, capture):
        stop = threading.Event()
        fake = FakeSocket(stop)
        sp._spool_cache["spools"] = SPOOLS
        with mock.patch.object(sp, "kx_credentials", lambda base: {
                "deviceId": "X1", "modelId": 20030, "username": "u", "password": "p",
                "devicecrt": "C", "devicepk": "K"}), \
                mock.patch.object(sp, "_kx_socket", lambda host, bundle, files: fake), \
                mock.patch.object(sp, "_live_active", lambda: True), \
                mock.patch.object(sp, "get_settings", lambda: {"kx_capture": capture}), \
                mock.patch.object(sp, "kx_capture", wraps=sp.kx_capture) as cap:
            sp._kx_session("auto-kx", {"ip": "http://10.0.0.9", "name": "Kobra X"}, stop)
        sp._live["printers"].pop("auto-kx", None)
        sp._live["links"].pop("auto-kx", None)
        return b"".join(fake.sent), cap.call_count

    def test_flag_off_no_capture_and_no_extra_request(self):
        sent, calls = self.session(False)
        self.assertEqual(calls, 0)
        self.assertNotIn(b"/web/printer/20030/X1/info", sent)

    def test_flag_on_captures_and_asks_for_info(self):
        with self.assertLogs(sp.log, "INFO"):
            sent, calls = self.session(True)
        self.assertEqual(calls, 1)
        self.assertIn(b"/web/printer/20030/X1/info", sent)


@unittest.skipUnless(test_display.NODE, "node is needed to run the page script")
class PrinterCardTest(unittest.TestCase):
    def render(self, printer, source="spoolman", before=""):
        runner = test_display.PageScriptTest("run_page")
        cfg = [{"id": printer["id"], "name": printer["name"], "auto": True, "ip": BASE, "units": [], "kind": "moonraker"}]
        live = {"links": {printer["id"]: "live"}, "printers": [printer]}
        return runner.run_page(f"""
allSpools = {json.dumps(SPOOLS)};
spoolSource = {json.dumps(source)};
cfg = {json.dumps(cfg)};
liveData = {json.dumps(live)};
{before}
console.log(JSON.stringify(autoPanel(cfg[0])));
""")

    TRAY = {"slot": 0, "empty": False, "type": "PLA", "name": "Black", "colour": "111111", "remain": 50,
            "rfid": False, "spool": 7, "profile": ""}

    def test_single_extruder_card_has_change_spool(self):
        html = self.render({"id": "auto-sv", "link": "auto-sv", "name": "SV06", "heads": False, "units": [],
                            "ext": self.TRAY, "spool_set": True, "age": 0})
        self.assertIn("Change Spool", html)
        self.assertIn('data-act="moon-clear"', html)

    def test_no_active_spool_still_offers_change(self):
        html = self.render({"id": "auto-sv", "link": "auto-sv", "name": "SV06", "heads": False, "units": [],
                            "ext": None, "spool_set": True, "age": 0})
        self.assertIn("Change Spool", html)
        self.assertNotIn('data-act="moon-clear"', html)

    def test_result_shows_on_the_card(self):
        sv = {"id": "auto-sv", "link": "auto-sv", "name": "SV06", "heads": False, "units": [],
              "ext": self.TRAY, "spool_set": True, "age": 0}
        reply = {"type": "moon_spool", "id": "auto-sv", "ok": False, "text": "SV06 refused <x>"}
        html = self.render(sv, before=f"handlers.forEach(function (h) {{ h({json.dumps(reply)}); }});")
        self.assertIn('pnote error">SV06 refused &lt;x&gt;', html)

    def test_hidden_for_u1_lanes_and_bambu_source(self):
        u1 = {"id": "auto-u1", "link": "auto-u1", "name": "U1", "heads": True, "ext": None, "spool_set": False,
              "age": 0, "units": [{"id": 0, "kind": "ams", "trays": [self.TRAY]}]}
        lanes = dict(u1, id="auto-afc", link="auto-afc", heads=False)
        self.assertNotIn("Change Spool", self.render(u1))
        self.assertNotIn("Change Spool", self.render(lanes))
        sv = {"id": "auto-sv", "link": "auto-sv", "name": "SV06", "heads": False, "units": [],
              "ext": self.TRAY, "spool_set": True, "age": 0}
        self.assertNotIn("Change Spool", self.render(sv, source="bambu"))


if __name__ == "__main__":
    unittest.main()
