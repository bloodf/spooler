#!/usr/bin/env python3
"""Build the plugin Orca Cloud publishes into dist/: one pure-Python wheel, spooler_any.whl.

The wheel holds the package `spooler`: the plugin code (plugin/spooler/spooler_any.py as spooler/__init__.py) and the
compiled page as a plain file (plugin/spooler/app.html as spooler/app.html, written by scripts/embed_ui.py). It runs on
every OS, so the release is one universal file ("any" is Orca Cloud's suffix for every platform). OrcaSlicer takes the
name and version from METADATA. Zip timestamps are fixed, so equal sources give equal bytes.

    python scripts/build.py
"""

import base64
import hashlib
import re
import shutil
import sys
import zipfile
from pathlib import Path

import check_version

ROOT = Path(__file__).resolve().parent.parent
DIST = ROOT / "dist"
PAGE = ROOT / "plugin" / "spooler" / "app.html"
MARKER = 'BUILD_TARGET = "any"\n'


def build():
    check_version.main(["build.py"])
    text = check_version.PLUGIN.read_text(encoding="utf-8")
    if text.count(MARKER) != 1:
        sys.exit(f"error: expected exactly one {MARKER.strip()!r} line in the plugin")
    if not PAGE.exists():
        sys.exit(f"error: {PAGE.relative_to(ROOT)} missing; run `npm ci && npm run build` in ui/")
    if DIST.exists():
        shutil.rmtree(DIST)
    DIST.mkdir()
    out = build_wheel(text, PAGE.read_bytes())
    print(f"built {out.relative_to(ROOT)}")


def _header(text, key):
    found = re.search(rf'^# {key} = "([^"]*)"', text, re.M)
    return found.group(1) if found else ""


def _record_line(name, data):
    digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
    return f"{name},sha256={digest},{len(data)}"


def build_wheel(text, page):
    """One pure-Python wheel (py3-none-any) for every OS: the plugin file as a package, and its page next to it."""
    version = _header(text, "version")
    dist_info = f"spooler-{version}.dist-info"
    files = {
        "spooler/__init__.py": text.encode("utf-8"),
        "spooler/app.html": page,
        f"{dist_info}/METADATA": (
            "Metadata-Version: 2.1\n"
            f"Name: {_header(text, 'name')}\n"
            f"Version: {version}\n"
            f"Summary: {_header(text, 'description')}\n"
            f"Author: {_header(text, 'author')}\n"
            "License: GPL-3.0-only\n"
            "Requires-Python: >=3.12\n"
        ).encode("utf-8"),
        f"{dist_info}/WHEEL": (
            "Wheel-Version: 1.0\nGenerator: spooler build.py\nRoot-Is-Purelib: true\nTag: py3-none-any\n"
        ).encode("utf-8"),
        f"{dist_info}/top_level.txt": b"spooler\n",
    }
    record = [_record_line(name, data) for name, data in files.items()] + [f"{dist_info}/RECORD,,"]
    files[f"{dist_info}/RECORD"] = ("\n".join(record) + "\n").encode("utf-8")
    out = DIST / "spooler_any.whl"
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as wheel:
        for name, data in files.items():
            info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))  # same bytes on every build
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16  # rw-r--r--, or some tools unpack it unreadable
            wheel.writestr(info, data)
    return out


if __name__ == "__main__":
    build()
