"""Spooler's data folder follows the data folder OrcaSlicer actually runs with (GUI test 2026-11-20).

With `--datadir <X>`, Spooler kept reading $HOME/Library/Application Support/OrcaSlicer/spooler/spooler_settings.json
every 5 s, which the sandbox refuses ([AUDIT] block), and took the Spoolman address of the default install from it.
OrcaSlicer installs plugins under <data folder>/orca_plugins, so that is where the data folder is read from.
"""

import json
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import load

sp, orca = load()


class DataDirTest(unittest.TestCase):
    def test_the_folder_above_orca_plugins_is_the_data_folder(self):
        plugin = Path("/work/orca-test-data/orca_plugins/cloud/u1/__whl_extracted__/spooler")
        self.assertEqual(sp._data_dir(plugin), Path("/work/orca-test-data/spooler"))
        default = Path("/example/user/Library/Application Support/OrcaSlicer/orca_plugins/__whl_extracted__/spooler")
        self.assertEqual(sp._data_dir(default), Path("/example/user/Library/Application Support/OrcaSlicer/spooler"))

    def test_the_default_location_is_only_a_fallback(self):
        with mock.patch.object(sp, "_config_root", lambda: Path("/example/user/.config")):
            self.assertEqual(sp._data_dir(Path("/src/plugin/spooler")), Path("/example/user/.config/OrcaSlicer/spooler"))

    def test_a_settings_file_the_sandbox_refuses_is_read_once(self):
        reads = []

        def refused(self, *a, **k):
            reads.append(self)
            raise PermissionError('Plugin attempted audited operation "open" without permission')
        with mock.patch.object(sp, "_denied_reads", set()), mock.patch.object(Path, "read_text", refused):
            for _ in range(3):   # the 5 s refresh
                self.assertEqual(sp.get_settings()["spoolman_url"], "")
        self.assertEqual(reads, [sp.SETTINGS_FILE, sp.OLD_SETTINGS])

    def test_a_readable_settings_file_is_read_every_time(self):
        reads = []

        def readable(self, *a, **k):
            reads.append(self)
            return json.dumps({"spoolman_url": "http://127.0.0.1:7912"})
        with mock.patch.object(sp, "_denied_reads", set()), mock.patch.object(Path, "read_text", readable):
            for _ in range(2):
                self.assertEqual(sp.get_settings()["spoolman_url"], "http://127.0.0.1:7912")
        self.assertEqual(len(reads), 2)


if __name__ == "__main__":
    unittest.main()
