import unittest

from plugin_loader import load

sp, orca = load()


class TrayKeyTest(unittest.TestCase):
    def test_tray_now_fallback(self):
        self.assertEqual(sp.tray_key({"tray_now": "5"}), 5)
        self.assertEqual(sp.tray_key({"tray_now": "254"}), 254)
        self.assertEqual(sp.tray_key({"tray_now": "255"}), -1)
        self.assertEqual(sp.tray_key({}), -1)

    def test_h2_snow_follows_active_extruder(self):
        snow = {0: 1 << 8 | 2, 1: 128 << 8}
        self.assertEqual(sp.tray_key({"snow": snow, "ex_now": 0}), 6)
        self.assertEqual(sp.tray_key({"snow": snow, "ex_now": 1}), 128)

    def test_h2_external_and_none(self):
        self.assertEqual(sp.tray_key({"snow": {0: 254 << 8}}), 254)
        self.assertEqual(sp.tray_key({"snow": {0: 255 << 8 | 255}}), -1)
        self.assertEqual(sp.tray_key({"snow": {0: -1}}), -1)

    def test_h2_snow_wins_over_tray_now(self):
        self.assertEqual(sp.tray_key({"snow": {0: 0}, "tray_now": "255"}), 0)


if __name__ == "__main__":
    unittest.main()
