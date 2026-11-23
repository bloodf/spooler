import base64
import hashlib
import json
import socket
import struct
import threading
import unittest

from plugin_loader import load

sp, orca = load()

KOBRA = "Anycubic Kobra X 0.4 nozzle"
# Encrypted with: openssl enc -aes-128-cbc -K <"abcdefghijklmnop"> -iv <"0123456789ABCDEF"> -base64
OPENSSL_INFO = ("OmhT1+8x0pFLDRsu6ztKL7Pc3WBsqUHxdpHCavkOZFiq4eE6S3RJ3Drq9T0aJ9o2Ly3teLEdt2PG56qZlwDJ3W7A8lH4cg50"
                "15kA6EONB8J3pbjvDZYsIiCWfO7DMZwB")
TOKEN = "0123456789abcdefabcdefghijklmnop"  # the key is token[16:32]

SPOOLS = [
    {"id": 21, "archived": False, "remaining_weight": 600, "initial_weight": 1000,
     "filament": {"id": 7, "name": "Red", "material": "PLA", "color_hex": "FF0000", "vendor": {"name": "Anycubic"}, "weight": 1000}},
    {"id": 22, "archived": False, "remaining_weight": 300, "initial_weight": 1000,
     "filament": {"id": 8, "name": "Blue", "material": "PETG", "color_hex": "0000FF", "vendor": {"name": "SUNLU"}, "weight": 1000}},
]
BOX_REPLY = {"type": "multiColorBox", "action": "getInfo", "state": "done", "data": {"multi_color_box": [{
    "id": 0, "model_id": 40001, "temp": 26, "loaded_slot": 1,
    "slots": [{"index": 0, "type": "PLA", "color": [254, 2, 1], "status": 5},
              {"index": 1, "type": "PETG", "color": [0, 0, 250], "status": 5},
              {"index": 2, "type": "", "color": [0, 0, 0], "status": 0},
              {"index": 3, "type": "TPU", "color": [10, 200, 10], "status": 5, "consumables_percent": 40}]}]}}


class AesTest(unittest.TestCase):
    def test_fips_197_vector(self):
        keys = sp._round_keys(bytes(range(16)))
        plain = sp.aes128_decrypt_block(keys, bytes.fromhex("69c4e0d86a7b0430d8cdb78070b4c55a"))
        self.assertEqual(plain.hex(), "00112233445566778899aabbccddeeff")

    def test_cbc_matches_openssl(self):
        plain = sp.aes128_cbc_decrypt(b"abcdefghijklmnop", b"0123456789ABCDEF", base64.b64decode(OPENSSL_INFO))
        self.assertEqual(json.loads(plain)["deviceId"], "X1")

    def test_bad_padding(self):
        with self.assertRaises(ValueError):
            sp.aes128_cbc_decrypt(b"abcdefghijklmnop", b"0123456789ABCDEF", bytes(16))


class CredentialsTest(unittest.TestCase):
    def test_signed_params(self):
        params = sp.kx_signed_params(TOKEN, 1700000000000, "aB3dE5", "DID")
        inner = hashlib.md5(TOKEN[:16].encode()).hexdigest()
        self.assertEqual(params["sign"], hashlib.md5((inner + "1700000000000aB3dE5").encode()).hexdigest())
        self.assertEqual((params["ts"], params["nonce"], params["did"]), ("1700000000000", "aB3dE5", "DID"))

    def test_decrypt_bundle(self):
        reply = {"code": 200, "data": {"info": OPENSSL_INFO, "token": "0123456789ABCDEF"}}
        bundle = sp.kx_decrypt_bundle(reply, TOKEN)
        self.assertEqual((bundle["deviceId"], bundle["modelId"], bundle["username"]), ("X1", 20030, "u"))

    def test_refused(self):
        with self.assertRaises(ValueError):
            sp.kx_decrypt_bundle({"code": 401}, TOKEN)


class ReportTest(unittest.TestCase):
    def setUp(self):
        sp._profiles["names"] = {(7, KOBRA): "Anycubic PLA Red @Anycubic Kobra X"}

    def test_slots(self):
        doc = sp.kx_report(BOX_REPLY["data"]["multi_color_box"], {"type": "PLA", "color": [255, 0, 0]},
                           SPOOLS, KOBRA)
        trays = doc["print"]["ams"]["ams"][0]["tray"]
        self.assertEqual(trays[0]["spool_id"], 21)
        self.assertEqual(trays[0]["tray_color"], "FE0201FF")  # matched by colour: the printer's reading
        self.assertEqual(trays[0]["profile"], "_local/spooler/Anycubic PLA Red @Anycubic Kobra X")
        self.assertEqual(trays[1]["spool_id"], 22)
        self.assertEqual(trays[2], {"id": "2"})
        self.assertIsNone(trays[3]["spool_id"])
        self.assertEqual((trays[3]["tray_type"], trays[3]["remain"]), ("TPU", 40))
        self.assertEqual(doc["print"]["vt_tray"]["id"], "254")
        self.assertEqual(doc["print"]["vt_tray"]["spool_id"], 21)

    def test_ace_100_percent_is_no_reading_and_spoolman_wins(self):
        # The ACE answers 100 for every spool it can't measure; Kobra Control draws a linked slot from Spoolman.
        box = [{"id": 0, "slots": [{"type": "PLA", "color": [254, 2, 1], "status": 5, "consumables_percent": 100},
                          {"type": "ABS", "color": [9, 9, 9], "status": 5, "consumables_percent": 100},
                          {"type": "ABS", "color": [9, 9, 9], "status": 5, "consumables_percent": 55},
                          {"type": "PLA", "color": [254, 2, 1], "status": 5, "consumables_percent": 55}]}]
        trays = sp.kx_report(box, None, SPOOLS, KOBRA)["print"]["ams"]["ams"][0]["tray"]
        self.assertEqual([t["remain"] for t in trays], [None, None, 55, None])
        self.assertEqual([t["spool_id"] for t in trays], [21, None, None, 21])

    def test_no_box(self):
        self.assertEqual(sp.kx_report([], None, SPOOLS), {"print": {"ams": {"ams": []}}})


def slot(i, kind="PLA", rgb=(1, 2, 3)):
    return {"index": i, "type": kind, "color": list(rgb), "status": 5}


HOLDER = {"id": -1, "slots": [slot(0, "PLA", (1, 1, 1)), slot(1, "PETG", (2, 2, 2)), slot(2, "ABS", (3, 3, 3))]}
ACE0 = {"id": 0, "slots": [slot(i, "PLA", (10 + i, 0, 0)) for i in range(4)]}


class SourceTest(unittest.TestCase):
    """Every filament source reaches the page with its own source, in ace.py's numbering."""
    PID = "src-test"

    def snap(self, boxes, merged=None):
        if merged is not None:
            boxes = sp.kx_merge_boxes(boxes, merged)
        sp.live_apply(self.PID, "Kobra X", sp.kx_report(boxes, None, []), link=self.PID, full=True)
        try:
            return next(p for p in sp.live_snapshot()["printers"] if p["id"] == self.PID)
        finally:
            with sp._live_lock:
                sp._live["printers"].pop(self.PID, None)

    def shape(self, live):
        return [(u["id"], u["source"], len(u["trays"])) for u in live["units"]]

    def test_holder_and_ace_in_any_order(self):
        for boxes in ([ACE0, HOLDER], [HOLDER, ACE0]):
            live = self.snap(boxes)
            self.assertEqual(self.shape(live), [(0, "ace", 4), (1, "holder", 3)])
            self.assertEqual(sum(not t["empty"] for u in live["units"] for t in u["trays"]), 7)
            self.assertNotEqual(live.get("unit_label"), "ACE")

    def test_holder_only_keeps_its_own_slots_and_ace_only_has_no_holder(self):
        four = {"id": -1, "slots": HOLDER["slots"] + [slot(3, "TPU")]}
        self.assertEqual(self.shape(self.snap([four])), [(0, "holder", 4)])
        self.assertEqual(self.shape(self.snap([ACE0])), [(0, "ace", 4)])

    def test_multi_ace_holder_after_the_highest_id_and_gaps_kept(self):
        ace2 = {"id": 2, "slots": ACE0["slots"]}
        live = self.snap([HOLDER, ace2, ACE0])
        self.assertEqual(self.shape(live), [(0, "ace", 4), (2, "ace", 4), (3, "holder", 3)])
        self.assertEqual([u["box"] for u in live["units"]], [0, 2, -1])

    def test_no_made_up_source_and_unreadable_ids_skipped(self):
        self.assertEqual(self.shape(self.snap([ACE0])), [(0, "ace", 4)])
        self.assertEqual(self.snap([{"slots": ACE0["slots"]}, {"id": "x", "slots": []}])["units"], [])

    def test_shuffled_slots_keep_their_index(self):
        kinds = ["PLA", "PETG", "ABS", "TPU"]
        shuffled = {"id": 0, "slots": [slot(i, kinds[i]) for i in (3, 1, 0, 2)]}
        trays = self.snap([shuffled])["units"][0]["trays"]
        self.assertEqual([t["type"] for t in trays], kinds)

    def test_bind_numbers(self):
        # The page links unit id * 4 + slot: the holder after ACE 0 is S5-S7, after ACE 0 and 2 it is S13-S15.
        ids = lambda boxes: [u["id"] for u in self.snap(boxes)["units"]]  # noqa: E731
        self.assertEqual(ids([HOLDER, ACE0]), [0, 1])
        self.assertEqual(ids([HOLDER, ACE0, {"id": 2, "slots": ACE0["slots"]}]), [0, 2, 3])

    def test_shuffled_full_then_one_slot_report_keeps_all_seven(self):
        holder = {"id": -1, "slots": [HOLDER["slots"][i] for i in (2, 0, 1)]}
        ace = {"id": 0, "slots": [ACE0["slots"][i] for i in (3, 1, 0, 2)]}
        live = self.snap([holder, ace], [{"id": -1, "slots": [slot(0, "TPU", (9, 9, 9))]}])
        self.assertEqual(self.shape(live), [(0, "ace", 4), (1, "holder", 3)])
        self.assertEqual([t["type"] for t in live["units"][1]["trays"]], ["TPU", "PETG", "ABS"])
        self.assertEqual([t["colour"] for t in live["units"][0]["trays"]], ["0A0000", "0B0000", "0C0000", "0D0000"])

    def test_report_without_slots_keeps_slots_and_a_slotless_ace_still_places_the_holder(self):
        live = self.snap([ACE0, HOLDER], [{"id": 0, "drying_status": {"status": 1}}])
        self.assertEqual(sum(not t["empty"] for u in live["units"] for t in u["trays"]), 7)
        early = self.snap([{"id": 0, "drying_status": {}}, HOLDER])
        self.assertEqual([(u["id"], u["source"]) for u in early["units"]], [(0, "ace"), (1, "holder")])

    def test_bad_index_is_not_a_position(self):
        bad = {"id": 0, "slots": [dict(slot(0, "PLA"), index="x"), slot(2, "ABS")]}
        self.assertEqual([t["type"] for t in self.snap([bad])["units"][0]["trays"]], ["", "", "ABS", ""])

    def test_partial_reports_keep_the_rest(self):
        edit = [{"id": -1, "slots": [slot(1, "TPU", (9, 9, 9))]}]
        live = self.snap([ACE0, HOLDER], edit)
        self.assertEqual(self.shape(live), [(0, "ace", 4), (1, "holder", 3)])
        self.assertEqual([t["type"] for t in live["units"][1]["trays"]], ["PLA", "TPU", "ABS"])
        only_ace = self.snap([ACE0, HOLDER], [{"id": 0, "slots": [slot(2, "ABS")]}])
        self.assertEqual([t["type"] for t in only_ace["units"][0]["trays"]], ["PLA", "PLA", "ABS", "PLA"])
        self.assertEqual(len(only_ace["units"]), 2)


class NoKobraBookingTest(unittest.TestCase):
    """Spooler never books the filament of an Anycubic Kobra print: Kobra Control books it. Should that
    change, presence.json must publish "books": ["anycubic"] under "provides" in the same change."""

    PID = "kobra-test"
    # Every key live_apply turns into a job, and so into a usage_track call.
    JOB = ("gcode_state", "mc_percent", "subtask_name", "gcode_file") + sp.JOB_KEYS

    def reports(self):
        box = BOX_REPLY["data"]["multi_color_box"]
        return [sp.kx_report(box, {"type": "PLA", "color": [255, 0, 0]}, SPOOLS, KOBRA),
                sp.kx_report(box, None, SPOOLS), sp.kx_report([], None, [])]

    def keys(self, value):
        if isinstance(value, dict):
            for key, inner in value.items():
                yield key
                yield from self.keys(inner)
        elif isinstance(value, list):
            for inner in value:
                yield from self.keys(inner)

    def test_report_carries_no_print_state(self):
        for report in self.reports():
            self.assertFalse(set(self.keys(report)) & set(self.JOB), report)

    def test_live_apply_never_tracks_usage(self):
        calls = []
        original = sp.usage_track
        sp.usage_track = lambda *args, **kwargs: calls.append(args) or []
        try:
            for report in self.reports():
                sp.live_apply(self.PID, "Kobra X", report, link=self.PID, full=True)
        finally:
            sp.usage_track = original
            with sp._live_lock:
                sp._live["printers"].pop(self.PID, None)
        self.assertEqual(calls, [])

    def test_presence_does_not_claim_kobra_booking(self):
        self.assertNotIn("books", sp.presence_doc()["provides"])


class KindTest(unittest.TestCase):
    def setUp(self):
        self.originals = (sp.is_moonraker, sp.kx_info)

    def tearDown(self):
        sp.is_moonraker, sp.kx_info = self.originals

    def test_moonraker_first(self):
        sp.is_moonraker = lambda base: True
        self.assertEqual(sp.printer_kind("http://h"), "moonraker")

    def test_anycubic_when_port_80_is_closed(self):
        def closed(base):
            raise sp.urllib.error.URLError("refused")

        sp.is_moonraker = closed
        sp.kx_info = lambda base: {"token": TOKEN}
        self.assertEqual(sp.printer_kind("http://h"), "anycubic")

    def test_something_else(self):
        sp.is_moonraker = lambda base: False

        def nope(base):
            raise ValueError("not anycubic")

        sp.kx_info = nope
        self.assertEqual(sp.printer_kind("http://h"), "none")

    def test_nothing_answers(self):
        def closed(base):
            raise sp.urllib.error.URLError("down")

        sp.is_moonraker = sp.kx_info = closed
        with self.assertRaises(sp.urllib.error.URLError):
            sp.printer_kind("http://h")


class FakeSocket:
    """Plays a printer's MQTT side: a CONNACK, then the box report, then silence."""

    def __init__(self, stop):
        reply = json.dumps(BOX_REPLY).encode()
        topic = sp._mqtt_str("anycubic/anycubicCloud/v1/printer/public/20030/X1/multiColorBox")
        self.incoming = bytearray(b"\x20\x02\x00\x00" + sp._mqtt_packet(0x30, topic + reply))
        self.sent = []
        self.stop = stop

    def settimeout(self, value):
        pass

    def sendall(self, data):
        self.sent.append(bytes(data))

    def recv(self, size):
        if not self.incoming:
            self.stop.set()
            raise socket.timeout()
        chunk, self.incoming = bytes(self.incoming[:size]), self.incoming[size:]
        return chunk

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


class SessionTest(unittest.TestCase):
    def test_session_reads_the_box(self):
        stop = threading.Event()
        fake = FakeSocket(stop)
        originals = (sp.kx_credentials, sp._kx_socket, sp._live_active)
        sp.kx_credentials = lambda base: {"deviceId": "X1", "modelId": 20030, "username": "u", "password": "p",
                                          "devicecrt": "C", "devicepk": "K"}
        sp._kx_socket = lambda host, bundle, files: fake
        sp._live_active = lambda: True
        sp._spool_cache["spools"] = SPOOLS
        sp._live["printers"].clear()
        try:
            sp._kx_session("auto-kx", {"ip": "http://10.0.0.9", "name": "Kobra X"}, stop)
        finally:
            sp.kx_credentials, sp._kx_socket, sp._live_active = originals
        connect = fake.sent[0]
        self.assertEqual(connect[0], 0x10)
        self.assertIn(b"anycubic/anycubicCloud/v1/printer/+/20030/X1/#", b"".join(fake.sent))
        requested = [s for s in fake.sent if s[0] == 0x30]
        self.assertIn(b"anycubic/anycubicCloud/v1/web/printer/20030/X1/multiColorBox", requested[0])
        packet, at = requested[0], 1
        while packet[at] & 0x80:  # remaining length is a variable-length integer
            at += 1
        body = packet[at + 1:]
        size = struct.unpack("!H", body[:2])[0]
        self.assertEqual(json.loads(body[2 + size:])["action"], "getInfo")
        live = sp.live_snapshot()["printers"][0]
        self.assertEqual((live["units"][0]["source"], live["unit_label"]), ("ace", ""))
        self.assertEqual([t["spool"] for t in live["units"][0]["trays"]][:2], [21, 22])
        self.assertEqual(sp._live["links"]["auto-kx"], "live")
        sp._live["printers"].clear()
        sp._live["links"].pop("auto-kx", None)


class KeyFileTest(unittest.TestCase):
    def test_key_files_avoid_words_orca_blocks(self):
        # The key pair is written to disk briefly; OrcaSlicer blocks plugin paths containing "cert".
        import inspect
        source = inspect.getsource(sp._kx_session)
        self.assertIn('.kx-', source)
        self.assertNotRegex(source.split("files = ")[1].split("\n")[0], r"(?i)cert|conf|secret")


if __name__ == "__main__":
    unittest.main()
