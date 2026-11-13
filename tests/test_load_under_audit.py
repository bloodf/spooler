"""on_load must work under OrcaSlicer's audit sandbox.

OrcaSlicer 2.5 blocks a plugin's file access outside the folders it requested. platform.platform() reads
/System/Library/CoreServices/SystemVersion.plist and opens /dev/null on macOS, so calling it from on_load made
Spooler fail to load ("Plugin on_load failed: PermissionError ... audited operation open").
"""

import builtins
import os
import platform
import unittest
from unittest import mock

from plugin_loader import load

sp, orca = load()


def _audited_open(real_open, allowed):
    def guarded(file, *args, **kwargs):
        path = os.path.abspath(os.fspath(file)) if isinstance(file, (str, bytes, os.PathLike)) else None
        if path is not None and not path.startswith(allowed):
            raise PermissionError('Plugin attempted audited operation "open" without permission: ' + path)
        return real_open(file, *args, **kwargs)
    return guarded


class LoadUnderAuditTest(unittest.TestCase):
    def setUp(self):
        for cache in ("_platform_cache", "_uname_cache"):
            if isinstance(getattr(platform, cache, None), dict):
                getattr(platform, cache).clear()
        allowed = os.path.abspath(str(sp.DATA_DIR))
        patches = [
            mock.patch.object(builtins, "open", _audited_open(builtins.open, allowed)),
            mock.patch.object(sp, "sync_config", lambda *a, **k: None),
            mock.patch.object(sp, "start_presence", lambda *a, **k: None),
        ]
        for p in patches:
            p.start()
            self.addCleanup(p.stop)

    def test_page_on_load_reads_nothing_outside_the_data_folder(self):
        sp.SpoolerPage().on_load()

    def test_window_on_load_reads_nothing_outside_the_data_folder(self):
        window = sp.SpoolerWindow()
        with mock.patch.object(window, "_open", lambda: None):
            window.on_load()


if __name__ == "__main__":
    unittest.main()
