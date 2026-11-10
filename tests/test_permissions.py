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


class RegistrationTest(unittest.TestCase):
    def test_only_the_plugin_class_is_decorated(self):
        # @orca.plugin must sit on the plugin class: OrcaSlicer loads the one class it marks.
        self.assertEqual(orca.decorated, [sp.SpoolerPlugin])
        self.assertTrue(isinstance(sp.SpoolerPlugin, type) and issubclass(sp.SpoolerPlugin, orca.base))


if __name__ == "__main__":
    unittest.main()
