"""One MQTT connection per printer: while Kobra Control holds an Anycubic printer, Spooler reads its slots from
Kobra Control's presence and never logs in itself. Fakes only: no printer or network is contacted."""

import json
import os
import socket
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load
from test_kobra import BOX_REPLY, SPOOLS, FakeSocket

sp, orca = load()

ACE = BOX_REPLY["data"]["multi_color_box"]
LINK = {"ip": "http://10.0.0.9", "name": "Kobra X"}


def wait(predicate, timeout=5.0):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline and not predicate():
        time.sleep(0.02)
    return predicate()


class KobraCase(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        patch = mock.patch.object(sp, "_orca_data_dir", lambda: self.root)
        patch.start()
        self.addCleanup(patch.stop)

    def kobra(self, printers, ts=None, pid=None, state="active"):
        doc = {"schema": "orca-plugin-presence", "version": 1, "plugin": "kobracontrol", "session": "kxs",
               "pid": os.getpid() if pid is None else pid, "ts": time.time() if ts is None else ts, "state": state,
               "printers": printers}
        (self.root / "kobracontrol").mkdir(exist_ok=True)
        (self.root / "kobracontrol" / "presence.json").write_text(json.dumps(doc), encoding="utf-8")


class KobraHoldsTest(KobraCase):
    def test_a_printer_kobra_control_holds_is_matched_by_its_address(self):
        self.kobra([{"host": "10.0.0.9", "device": "X1", "connected": True, "boxes": ACE}])
        for address in ("http://10.0.0.9", "10.0.0.9", "HTTP://10.0.0.9:80/", " 10.0.0.9 "):
            self.assertEqual(sp.kobra_holds(address), {"connected": True, "device": "X1", "boxes": ACE}, address)
        self.assertIsNone(sp.kobra_holds("http://10.0.0.10"))
        self.assertIsNone(sp.kobra_holds(""))

    def test_still_connecting_holds_the_printer_without_slots(self):
        self.kobra([{"host": "10.0.0.9", "connected": False, "boxes": ACE}])
        self.assertEqual(sp.kobra_holds("http://10.0.0.9"), {"connected": False, "device": "", "boxes": []})

    def test_no_fresh_running_kobra_control_holds_nothing(self):
        held = [{"host": "10.0.0.9", "connected": True, "boxes": ACE}]
        for kwargs in ({"ts": time.time() - 120}, {"pid": os.getpid() + 1}, {"state": "stopped"}):
            self.kobra(held, **kwargs)
            self.assertIsNone(sp.kobra_holds("http://10.0.0.9"), kwargs)
        self.kobra("not a list")
        self.assertIsNone(sp.kobra_holds("http://10.0.0.9"))
        (self.root / "kobracontrol" / "presence.json").unlink()
        self.assertIsNone(sp.kobra_holds("http://10.0.0.9"))

    def test_boxes_are_capped(self):
        self.kobra([{"host": "10.0.0.9", "connected": True, "boxes": [{"id": n} for n in range(100)]}])
        self.assertEqual(len(sp.kobra_holds("10.0.0.9")["boxes"]), sp.KOBRA_BOXES)


class DeferTest(KobraCase):
    def setUp(self):
        super().setUp()
        self.logins = []

        def login(*args, **kwargs):
            self.logins.append(args)
            raise AssertionError("Spooler contacted a printer Kobra Control holds")
        for name, value in (("kx_credentials", login), ("_kx_socket", login), ("printer_kind", login),
                            ("kx_info", login), ("_live_active", lambda: True), ("moon_found", lambda *a, **k: None),
                            ("KX_KOBRA_SECS", 0.05)):
            patch = mock.patch.object(sp, name, value)
            patch.start()
            self.addCleanup(patch.stop)
        sp._spool_cache["spools"] = SPOOLS
        sp._live["printers"].clear()
        self.addCleanup(sp._live["printers"].clear)
        self.addCleanup(sp._live["links"].pop, "auto-kx", None)

    def run_link(self, until):
        stop = threading.Event()
        thread = threading.Thread(target=sp._moon_run, args=("auto-kx", LINK, stop), daemon=True)
        thread.start()
        try:
            self.assertTrue(wait(until))
        finally:
            stop.set()
            thread.join(5)
        self.assertFalse(thread.is_alive())

    def test_slots_come_from_kobra_control_and_the_printer_is_never_contacted(self):
        self.kobra([{"host": "10.0.0.9", "device": "X1", "connected": True, "boxes": ACE}])
        self.run_link(lambda: sp._live["links"].get("auto-kx") == "live")
        self.assertEqual(self.logins, [])
        live = sp.live_snapshot()["printers"][0]
        self.assertEqual((live["via"], live["bind"], live["units"][0]["source"]), ("kobracontrol", "S", "ace"))
        self.assertEqual([t["spool"] for t in live["units"][0]["trays"]][:2], [21, 22])

    def test_while_kobra_control_connects_spooler_waits_for_it(self):
        self.kobra([{"host": "10.0.0.9", "connected": False, "boxes": []}])
        self.run_link(lambda: sp._live["links"].get("auto-kx") == "kobra_wait")
        self.assertEqual(self.logins, [])


class EndlessSocket(FakeSocket):
    """The box report, then a printer that keeps the session open."""

    def recv(self, size):
        if not self.incoming:
            time.sleep(0.01)
            raise socket.timeout()
        return super().recv(size)


class TakeOverTest(KobraCase):
    def test_own_session_disconnects_once_kobra_control_holds_the_printer(self):
        stop = threading.Event()
        fake = EndlessSocket(stop)
        bundle = {"deviceId": "X1", "modelId": 20030, "username": "u", "password": "p", "devicecrt": "C", "devicepk": "K"}
        for name, value in (("kx_credentials", lambda base: bundle), ("_kx_socket", lambda host, b, files: fake),
                            ("_live_active", lambda: True), ("KX_KOBRA_SECS", 0.05)):
            patch = mock.patch.object(sp, name, value)
            patch.start()
            self.addCleanup(patch.stop)
        sp._spool_cache["spools"] = SPOOLS
        self.addCleanup(sp._live["printers"].clear)
        self.addCleanup(sp._live["links"].pop, "auto-kx", None)
        done = threading.Thread(target=sp._kx_session, args=("auto-kx", LINK, stop), daemon=True)
        done.start()
        self.assertTrue(wait(lambda: sp._live["links"].get("auto-kx") == "live"))
        self.assertEqual(sp.live_snapshot()["printers"][0]["via"], "")
        self.kobra([{"host": "10.0.0.9", "connected": False, "boxes": []}])
        done.join(5)
        self.assertFalse(done.is_alive())
        self.assertFalse(stop.is_set())
        self.assertEqual(fake.sent[-1], b"\xe0\x00")   # MQTT DISCONNECT before the socket closes


if __name__ == "__main__":
    unittest.main()
