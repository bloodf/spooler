#!/usr/bin/env python3
"""Build the plugin file Orca Cloud publishes into dist/.

The plugin is a single pure-Python source file that runs on every OS, so the release is one
universal file, spooler_any.py ("any" is Orca Cloud's suffix for every platform). Uploading six
identical per-OS copies made Orca Cloud's automated permission review fail with
SECURITY_SCAN_UNAVAILABLE; one file is what the other plugins publish. A per-OS copy can still be
built by hand; it differs only in its filename suffix and the BUILD_TARGET it reports in the log.

    python scripts/build.py                        # spooler_any.py and the wheel
    python scripts/build.py --target linux_arm64   # one per-OS copy instead
"""

import argparse
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
MARKER = 'BUILD_TARGET = "any"\n'
DEFAULT_TARGETS = ("any",)
TARGETS = (
    "any",
    "win_x86_64",
    "win_arm64",
    "linux_x86_64",
    "linux_arm64",
    "macosx_arm64",
    "macosx_x86_64",
)


def build(targets):
    check_version.main(["build.py"])
    text = check_version.PLUGIN.read_text(encoding="utf-8")
    if text.count(MARKER) != 1:
        sys.exit(f"error: expected exactly one {MARKER.strip()!r} line in the plugin")
    if DIST.exists():
        shutil.rmtree(DIST)
    DIST.mkdir()
    for target in targets:
        out = DIST / f"spooler_{target}.py"
        stamped = text.replace(MARKER, f'BUILD_TARGET = "{target}"\n')
        out.write_text(stamped, encoding="utf-8", newline="\n")
        print(f"built {out.relative_to(ROOT)}")
    out = build_wheel(text)
    print(f"built {out.relative_to(ROOT)}")


def _header(text, key):
    found = re.search(rf'^# {key} = "([^"]*)"', text, re.M)
    return found.group(1) if found else ""


def _record_line(name, data):
    digest = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
    return f"{name},sha256={digest},{len(data)}"


def build_wheel(text):
    """One pure-Python wheel (py3-none-any) for every OS, holding the same plugin file as a
    package. OrcaSlicer takes its name and version from METADATA instead of the PEP 723 block.
    Not published yet: the per-OS .py files stay the release until it is tried in OrcaSlicer."""
    version = _header(text, "version")
    dist_info = f"spooler-{version}.dist-info"
    files = {
        "spooler/__init__.py": text.encode("utf-8"),
        f"{dist_info}/METADATA": (
            "Metadata-Version: 2.1\n"
            f"Name: {_header(text, 'name')}\n"
            f"Version: {version}\n"
            f"Summary: {_header(text, 'description')}\n"
            f"Author: {_header(text, 'author')}\n"
            "License: MIT\n"
            "Requires-Python: >=3.12\n"
        ).encode("utf-8"),
        f"{dist_info}/WHEEL": (
            "Wheel-Version: 1.0\nGenerator: spooler build.py\nRoot-Is-Purelib: true\nTag: py3-none-any\n"
        ).encode("utf-8"),
        f"{dist_info}/top_level.txt": b"spooler\n",
    }
    record = [_record_line(name, data) for name, data in files.items()] + [f"{dist_info}/RECORD,,"]
    files[f"{dist_info}/RECORD"] = ("\n".join(record) + "\n").encode("utf-8")
    out = DIST / f"spooler-{version}-py3-none-any.whl"
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as wheel:
        for name, data in files.items():
            info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))  # same bytes on every build
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16  # rw-r--r--, or some tools unpack it unreadable
            wheel.writestr(info, data)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--target", action="append", choices=TARGETS, help="build only this target")
    args = parser.parse_args()
    build(tuple(args.target) if args.target else DEFAULT_TARGETS)


if __name__ == "__main__":
    main()
