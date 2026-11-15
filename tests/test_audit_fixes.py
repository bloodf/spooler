"""Fixes from the 2026-11 audit, each played against a local fake server on 127.0.0.1 or a mock."""

import base64
import http.server
import importlib.util
import json
import os
import stat
import tempfile
import threading
import types
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


def _fresh_socket():
    """socket's own create_connection: test_review_fixes swaps the module's for a guard that
    refuses all network, and these tests talk to a fake server on 127.0.0.1 only."""
    spec = importlib.util.find_spec("socket")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # Its code, run against the real socket module (a re-executed copy can't build every enum).
    fresh = module.create_connection
    real = types.FunctionType(fresh.__code__, sp.socket.__dict__, fresh.__name__, fresh.__defaults__)
    real.__kwdefaults__ = fresh.__kwdefaults__
    return real


_LOOPBACK = {"create_connection": _fresh_socket(),
             "urlopen": lambda url, data=None, timeout=10, **kw: sp.urllib.request.build_opener().open(url, data, timeout)}


class FakeServer:
    """A one-route-table HTTP server on 127.0.0.1: {path: (status, headers, body)}; records requests."""

    def __init__(self, routes: dict):
        self.routes, self.requests = routes, []
        outer = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def _answer(self):
                size = int(self.headers.get("Content-Length") or 0)
                outer.requests.append({"path": self.path, "method": self.command, "headers": dict(self.headers),
                                       "body": self.rfile.read(size) if size else b""})
                status, headers, body = outer.routes.get(self.path, (404, {}, b"{}"))
                self.send_response(status)
                for key, value in headers.items():
                    self.send_header(key, value)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            do_GET = do_POST = do_PUT = do_PATCH = _answer

            def log_message(self, *args):
                pass

        self.httpd = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)

    def __enter__(self):
        self.patches = [mock.patch.object(sp.socket, "create_connection", _LOOPBACK["create_connection"]),
                        mock.patch.object(sp.urllib.request, "urlopen", _LOOPBACK["urlopen"])]
        for patch in self.patches:
            patch.start()
        self.thread.start()
        return self

    def __exit__(self, *exc):
        for patch in self.patches:
            patch.stop()
        self.httpd.shutdown()
        self.httpd.server_close()


class PingMalformedTest(unittest.TestCase):
    """Test Connection must answer even when the address isn't a Spoolman: an exception there left
    _testing set for good, so every later test (and with it Save) did nothing until a restart."""

    def check(self, body: bytes) -> dict:
        with FakeServer({"/api/v1/info": (200, {"Content-Type": "application/json"}, body)}) as server:
            return sp.ping(f"http://127.0.0.1:{server.port}")

    def test_empty_body(self):
        result = self.check(b"")
        self.assertFalse(result["ok"])
        self.assertIn("Spoolman", result["error"])

    def test_json_list(self):
        self.assertFalse(self.check(b"[1, 2]")["ok"])

    def test_html_page(self):
        self.assertFalse(self.check(b"<html>router login</html>")["ok"])

    def test_real_answer(self):
        self.assertEqual(self.check(b'{"version": "0.22.1"}'), {"ok": True, "version": "0.22.1"})


class SpoolListMalformedTest(unittest.TestCase):
    """A spool list that isn't a list of objects is a failed read, not a crash in load_spools."""

    def read(self, body: bytes) -> dict:
        with FakeServer({"/api/v1/spool": (200, {}, body)}) as server, \
                mock.patch.object(sp, "publish_stock"), mock.patch.object(sp, "low_stock_crossed", return_value=[]):
            return sp.get_spools(f"http://127.0.0.1:{server.port}")

    def test_object_instead_of_list(self):
        result = self.read(b'{"detail": "maintenance"}')
        self.assertFalse(result["ok"])

    def test_non_objects_in_the_list_are_dropped(self):
        result = self.read(b'[{"id": 1, "filament": {"id": 2}}, "junk", null]')
        self.assertTrue(result["ok"])
        self.assertEqual([s["id"] for s in result["spools"]], [1])


class ReleaseMalformedTest(unittest.TestCase):
    def test_non_object_answer_is_an_error_not_an_exception(self):
        resp = mock.MagicMock()
        resp.__enter__.return_value.read.return_value = b"[]"
        with mock.patch.object(sp.urllib.request, "urlopen", return_value=resp):
            self.assertFalse(sp.get_release()["ok"])


class SpoolmanAddressTest(unittest.TestCase):
    def test_user_and_password_go_as_basic_auth(self):
        with FakeServer({"/api/v1/info": (200, {}, b'{"version": "0.22.1"}')}) as server:
            result = sp.ping(f"http://alice:s%3Acret@127.0.0.1:{server.port}")
        self.assertTrue(result["ok"], result)
        auth = server.requests[0]["headers"].get("Authorization", "")
        self.assertEqual(auth, "Basic " + base64.b64encode(b"alice:s:cret").decode())

    def test_only_http_and_https(self):
        folder = Path(tempfile.mkdtemp())
        (folder / "api" / "v1").mkdir(parents=True)
        (folder / "api" / "v1" / "info").write_text('{"version": "1.0.0"}')
        result = sp.ping(folder.as_uri())
        self.assertFalse(result["ok"])
        self.assertIn("http", result["error"])

    def test_websocket_handshake_carries_the_credentials(self):
        sent = []

        class Sock:
            def sendall(self, data):
                sent.append(data)

            def recv(self, n):
                raise ConnectionError("done")
        with self.assertRaises(ConnectionError):
            sp._ws_handshake(Sock(), "ws://bob:pw@127.0.0.1:7912/api/v1/spool")
        head = sent[0].decode()
        self.assertIn("Host: 127.0.0.1:7912\r\n", head)
        self.assertIn("Authorization: Basic " + base64.b64encode(b"bob:pw").decode(), head)

    def test_websocket_handshake_without_credentials_has_no_auth(self):
        sent = []

        class Sock:
            def sendall(self, data):
                sent.append(data)

            def recv(self, n):
                raise ConnectionError("done")
        with self.assertRaises(ConnectionError):
            sp._ws_handshake(Sock(), "ws://127.0.0.1:7912/api/v1/spool")
        self.assertNotIn("Authorization", sent[0].decode())


if __name__ == "__main__":
    unittest.main()
