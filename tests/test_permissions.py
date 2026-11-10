import unittest

from plugin_loader import load

sp, orca = load()


class PermissionsTest(unittest.TestCase):
    def test_declares_data_folder_threads_and_fixed_urls(self):
        calls = []
        orca.request_permissions = lambda **kw: calls.append(kw)
        try:
            sp.request_permissions()
        finally:
            del orca.request_permissions
        self.assertEqual(len(calls), 1)
        targets = calls[0]
        self.assertTrue(targets["threading"])
        self.assertIn(sp.RELEASE_API, targets["network_http"])
        self.assertIn(str(sp.DATA_DIR), targets["fs_readwrite"])
        # OrcaSlicer raises ValueError on an empty target string.
        self.assertTrue(all(targets["network_http"]) and all(targets["fs_readwrite"]))

    def test_older_orcaslicer_without_the_call(self):
        self.assertFalse(hasattr(orca, "request_permissions"))
        sp.request_permissions()


if __name__ == "__main__":
    unittest.main()
