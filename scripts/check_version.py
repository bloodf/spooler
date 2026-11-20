#!/usr/bin/env python3
"""Fail if the plugin's two version numbers disagree, or don't match a release tag.

The PEP 723 block is in plugin/spooler/__init__.py, PLUGIN_VERSION in plugin/spooler/core.py.

    python scripts/check_version.py            # consistency only
    python scripts/check_version.py v0.2.0     # also require the tag to match
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKAGE = ROOT / "plugin" / "spooler"
PLUGIN = PACKAGE / "__init__.py"   # the PEP 723 block: name, version, description
CORE = PACKAGE / "core.py"         # PLUGIN_VERSION, which the plugin reports


def read_versions(text, core_text):
    meta = re.search(r'^# version = "([^"]+)"', text, re.M)
    const = re.search(r'^PLUGIN_VERSION = "([^"]+)"', core_text, re.M)
    return (meta.group(1) if meta else None, const.group(1) if const else None)


def main(argv):
    meta, const = read_versions(PLUGIN.read_text(encoding="utf-8"), CORE.read_text(encoding="utf-8"))
    if not meta or not const:
        sys.exit("error: could not find both the PEP 723 version and PLUGIN_VERSION")
    if meta != const:
        sys.exit(f"error: metadata says {meta}, PLUGIN_VERSION says {const}")
    if len(argv) > 1 and argv[1].lstrip("v") != meta:
        sys.exit(f"error: tag {argv[1]!r} does not match plugin version {meta!r}")
    print(f"version {meta} ok")


if __name__ == "__main__":
    main(sys.argv)
