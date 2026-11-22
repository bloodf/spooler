"""filmatch (the shared matcher from @orca-plugins/ui-foundation) keeps Spooler's picks, and the committed copy is the
foundation's."""

import json
import unittest

from fake_bundle import FIXTURES
from plugin_loader import PACKAGE, load

sp, orca = load()
ROOT = PACKAGE.parent.parent
SHARED = ROOT / "ui" / "node_modules" / "@orca-plugins" / "ui-foundation" / "python" / "filmatch.py"


class FilmatchParityTest(unittest.TestCase):
    def test_best_parent_picks_unchanged(self):
        """fixtures/filmatch_parity.json: best_parent's picks before it moved to filmatch, for every filament in
        spoolman_spools.json and a grid of materials, vendors and names, on a printer with its own presets and one
        without."""
        parents = json.loads((FIXTURES / "orca_parents.json").read_text(encoding="utf-8"))
        cases = json.loads((FIXTURES / "filmatch_parity.json").read_text(encoding="utf-8"))["cases"]
        self.assertGreater(len(cases), 2000)
        changed = [(name, material, vendor, target, want, got) for name, material, vendor, target, want in cases
                   if (got := sp.best_parent({"name": name, "material": material, "vendor": {"name": vendor} if vendor else None},
                                             target, parents)) != want]
        self.assertEqual(changed, [])

    def test_committed_copy_is_the_foundations(self):
        self.assertTrue(SHARED.exists(), "run npm ci in ui/")
        self.assertEqual((PACKAGE / "filmatch.py").read_bytes(), SHARED.read_bytes(),
                         "plugin/spooler/filmatch.py differs from ui-foundation's; run `npm run build` in ui/")


if __name__ == "__main__":
    unittest.main()
