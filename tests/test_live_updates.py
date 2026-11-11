"""Live spool updates: the small WebSocket client that listens to Spoolman, played against a fake
socket, and the thread that follows the Spoolman source and address."""

import base64
import hashlib
import json
import socket
import struct
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()

GUID = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


def frame(op: int, payload: bytes, fin: bool = True) -> bytes:
    """A server frame (unmasked)."""
    size = len(payload)
    head = bytes([(0x80 if fin else 0) | op])
    if size < 126:
        head += bytes([size])
    elif size < 65536:
        head += bytes([126]) + struct.pack("!H", size)
    else:
        head += bytes([127]) + struct.pack("!Q", size)
    return head + payload


def unframe(data: bytes) -> tuple[int, bool, bytes]:
    """A client frame as (opcode, masked, payload)."""
    op, second = data[0] & 15, data[1]
    size, at = second & 127, 2
    if size == 126:
        size, at = struct.unpack("!H", data[2:4])[0], 4
    elif size == 127:
        size, at = struct.unpack("!Q", data[2:10])[0], 10
    masked = bool(second & 128)
    mask = data[at:at + 4] if masked else b"\0\0\0\0"
    body = data[at + 4 if masked else at:][:size]
    return op, masked, bytes(b ^ mask[i % 4] for i, b in enumerate(body))


def event(kind: str = "updated", resource: str = "spool") -> bytes:
    return json.dumps({"type": kind, "resource": resource, "date": "2026-11-11T10:00:00",
                       "payload": {"id": 3}}).encode()


class FakeWs:
    """Plays Spoolman: answers the upgrade request, then sends the given frames, then goes quiet
    and stops the session after a short while."""

    def __init__(self, frames: bytes, stop: threading.Event, accept: str | None = None, quiet: float = 0.3):
        self.frames, self.stop, self.accept, self.quiet = frames, stop, accept, quiet
        self.incoming = bytearray()
        self.sent: list[bytes] = []
        self.quiet_since = 0.0

    def settimeout(self, value):
        pass

    def sendall(self, data):
        data = bytes(data)
        self.sent.append(data)
        if data.startswith(b"GET "):
            key = [line.split(b":", 1)[1].strip() for line in data.split(b"\r\n")
                   if line.lower().startswith(b"sec-websocket-key:")][0]
            accept = self.accept or base64.b64encode(hashlib.sha1(key + GUID).digest()).decode()
            self.incoming += (b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                              b"Sec-WebSocket-Accept: " + accept.encode() + b"\r\n\r\n") + self.frames

    def recv(self, size):
        if not self.incoming:
            self.quiet_since = self.quiet_since or time.monotonic()
            if time.monotonic() - self.quiet_since > self.quiet:
                self.stop.set()
            time.sleep(0.01)
            raise socket.timeout()
        chunk, self.incoming = bytes(self.incoming[:size]), self.incoming[size:]
        return chunk

    def frames_sent(self):
        return [unframe(data) for data in self.sent if not data.startswith(b"GET ")]


class UrlTest(unittest.TestCase):
    def test_address_follows_the_spoolman_url(self):
        cases = {
            "http://spoolman:7912": "ws://spoolman:7912/api/v1/spool",
            "http://spoolman:7912/": "ws://spoolman:7912/api/v1/spool",
            "https://home.example/spoolman/": "wss://home.example/spoolman/api/v1/spool",
            "https://home.example/a/b": "wss://home.example/a/b/api/v1/spool",
            " http://10.0.0.5 ": "ws://10.0.0.5/api/v1/spool",
            "": "",
            "spoolman:7912": "",
            "ftp://spoolman": "",
        }
        for url, want in cases.items():
            self.assertEqual(sp.ws_url(url), want, url)


class FrameTest(unittest.TestCase):
    def test_client_frames_are_masked_at_every_length(self):
        for size in (0, 5, 125, 126, 200, 65535, 65536, 70000):
            payload = bytes(i % 251 for i in range(size))
            op, masked, body = unframe(sp._ws_frame(1, payload))
            self.assertEqual((op, masked, body), (1, True, payload), size)

    def test_reads_every_length_encoding(self):
        for size in (5, 200, 70000):
            payload = b"x" * size
            sock = FakeWs(b"", threading.Event())
            sock.incoming += frame(1, payload)
            self.assertEqual(sp._ws_read(sock), (True, 1, payload))

    def test_oversized_frame_is_refused(self):
        sock = FakeWs(b"", threading.Event())
        sock.incoming += bytes([0x81, 127]) + struct.pack("!Q", sp.WS_MAX + 1)
        with self.assertRaises(ConnectionError):
            sp._ws_read(sock)


class SessionTest(unittest.TestCase):
    def run_session(self, frames: bytes, accept: str | None = None):
        stop = threading.Event()
        sock = FakeWs(frames, stop, accept)
        posts: list = []
        with mock.patch.dict(sp._ws, post=posts.append), mock.patch.object(sp, "WS_DEBOUNCE", 0.05):
            sp._spool_cache["time"] = 99.0
            sp._ws_handshake(sock, "ws://spoolman:7912/sub/api/v1/spool")
            sp._ws_listen(sock, stop)
        return sock, posts

    def test_handshake_asks_for_the_path_and_checks_the_answer(self):
        sock, _ = self.run_session(b"")
        request = sock.sent[0].decode()
        self.assertTrue(request.startswith("GET /sub/api/v1/spool HTTP/1.1\r\n"), request)
        self.assertIn("Host: spoolman:7912\r\n", request)
        self.assertIn("Upgrade: websocket\r\n", request)
        self.assertIn("Sec-WebSocket-Version: 13\r\n", request)

    def test_wrong_accept_is_refused(self):
        with self.assertRaises(ConnectionError):
            self.run_session(b"", accept="bm90IHRoZSByaWdodCBrZXk=")

    def test_ping_gets_a_masked_pong(self):
        sock, _ = self.run_session(frame(9, b"hi"))
        self.assertIn((10, True, b"hi"), sock.frames_sent())

    def test_a_burst_of_events_refreshes_once(self):
        frames = frame(1, event("added")) + frame(1, event("updated")) + frame(1, event("deleted"))
        _, posts = self.run_session(frames)
        self.assertEqual(posts, [{"type": "spool_changed"}])
        self.assertEqual(sp._spool_cache["time"], 0.0)

    def test_fragmented_and_long_events_are_joined(self):
        text = event()
        frames = frame(1, text[:10], fin=False) + frame(0, text[10:20], fin=False) + frame(0, text[20:])
        _, posts = self.run_session(frames)
        self.assertEqual(posts, [{"type": "spool_changed"}])
        long = json.dumps({"type": "updated", "resource": "spool", "payload": {"comment": "x" * 70000}}).encode()
        _, posts = self.run_session(frame(1, long))
        self.assertEqual(posts, [{"type": "spool_changed"}])

    def test_keepalive_answers_and_other_messages_do_not_refresh(self):
        frames = frame(1, b'{"status": "healthy"}') + frame(1, event(resource="filament")) + frame(1, b"not json")
        _, posts = self.run_session(frames)
        self.assertEqual(posts, [])
        self.assertEqual(sp._spool_cache["time"], 99.0)

    def test_close_is_answered_and_ends_the_session(self):
        sock, posts = self.run_session(frame(8, b"\x03\xe8") + frame(1, event()))
        self.assertEqual(sock.frames_sent()[-1][0], 8)
        self.assertEqual(posts, [])

    def test_keepalive_frame_is_sent_and_silence_ends_the_session(self):
        stop = threading.Event()
        sock = FakeWs(b"", stop, quiet=5.0)
        with mock.patch.object(sp, "WS_KEEP", 0.0), mock.patch.object(sp, "WS_DEAD", 0.1):
            sp._ws_handshake(sock, "ws://spoolman:7912/api/v1/spool")
            with self.assertRaises(ConnectionError):
                sp._ws_listen(sock, stop)
        self.assertEqual(sock.frames_sent()[0][:2], (1, True))

    def test_a_closed_page_does_not_break_the_listener(self):
        def gone(_data):
            raise RuntimeError("window closed")
        stop = threading.Event()
        sock = FakeWs(frame(1, event()), stop)
        with mock.patch.dict(sp._ws, post=gone), mock.patch.object(sp, "WS_DEBOUNCE", 0.0):
            sp._ws_handshake(sock, "ws://spoolman:7912/api/v1/spool")
            sp._ws_listen(sock, stop)  # no exception


class SyncTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.patches = [mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                        mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json"),
                        mock.patch.object(sp, "_ws_run", side_effect=lambda url, stop: stop.wait()),
                        mock.patch.dict(sp._ws, url="", stop=None, post=None)]
        for patch in self.patches:
            patch.start()

    def tearDown(self):
        sp.ws_sync(None)
        for patch in reversed(self.patches):
            patch.stop()
        self.tmp.cleanup()

    def test_thread_follows_source_and_address(self):
        sp.save_settings({"spoolman_url": "http://a:7912", "spool_source": "spoolman"})
        sp.ws_sync(print)
        first = sp._ws["stop"]
        self.assertEqual(sp._ws["url"], "ws://a:7912/api/v1/spool")
        sp.ws_sync(print)
        self.assertIs(sp._ws["stop"], first)  # same address: the running socket stays
        sp.save_settings({"spoolman_url": "https://b/spoolman", "spool_source": "spoolman"})
        sp.ws_sync(print)
        self.assertTrue(first.is_set())
        self.assertEqual(sp._ws["url"], "wss://b/spoolman/api/v1/spool")
        second = sp._ws["stop"]
        sp.save_settings({"spoolman_url": "https://b/spoolman", "spool_source": "bambu"})
        sp.ws_sync(print)
        self.assertTrue(second.is_set())
        self.assertEqual((sp._ws["url"], sp._ws["stop"]), ("", None))

    def test_closing_the_window_stops_it(self):
        sp.save_settings({"spoolman_url": "http://a:7912", "spool_source": "spoolman"})
        sp.ws_sync(print)
        stop = sp._ws["stop"]
        sp.ws_sync(None)
        self.assertTrue(stop.is_set())
        self.assertIsNone(sp._ws["post"])


if __name__ == "__main__":
    unittest.main()
