"""Items left open by the first audit pass: printing-state confirmation for a Moonraker spool change,
a fresh Spoolman version before writes that depend on it, link status ownership on restart, the
legacy window's replies after it closed, and history scoped to the Spoolman it was booked on."""

import json
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()
DAY = 86400


def ext_doc(state: str) -> dict:
    return {"print": {"vt_tray": {"id": "254", "spool_id": 5}, "gcode_state": state}}


class FreshVersionTest(unittest.TestCase):
    """A Spoolman downgraded below 0.26 while OrcaSlicer runs: the write that depends on the version
    reads it again, so a one-key extra PATCH can't wipe the spool's other fields."""

    def setUp(self):
        sp._versions.clear()
        self.addCleanup(sp._versions.clear)

    def test_dried_date_reads_the_version_each_time(self):
        versions = iter(["0.26.0", "0.25.3"])
        calls = []

        def call(method, path, body=None):
            calls.append((method, path))
            if path == "info":
                return {"version": next(versions)}
            return {"extra": {"dryer": '"Box 2"', "dried": '"old"'}}
        with mock.patch.object(sp, "spoolman_call", side_effect=call), \
                mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)):
            first = sp._dried_extra(3, '"2026-11-14"')
            second = sp._dried_extra(3, '"2026-11-14"')
        self.assertEqual(first, {"dried": '"2026-11-14"'})
        self.assertEqual(second, {"dryer": '"Box 2"', "dried": '"2026-11-14"'}, "old Spoolman: whole map sent back")
        self.assertEqual(calls.count(("GET", "info")), 2)

    def test_reads_that_dont_write_still_use_the_cache(self):
        with mock.patch.object(sp, "spoolman_call", return_value={"version": "0.26.0"}) as call, \
                mock.patch.object(sp, "current_origin", return_value=("http://sm", 1)):
            sp.spoolman_version()
            sp.spoolman_version()
        self.assertEqual(call.call_count, 1)

    def test_send_changes_checks_the_version_fresh(self):
        src = Path(sp.__file__).read_text(encoding="utf-8")
        body = src[src.index("def _send_changes"):src.index("def native_value")]
        self.assertIn("spoolman_at_least(SPOOLMAN_EXTRA_MERGE, fresh=True)", body)


if __name__ == "__main__":
    unittest.main()
