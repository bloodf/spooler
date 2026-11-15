#!/usr/bin/env python3
"""Embed the compiled Vue page (ui/ -> ui/dist/spooler-ui.html, `npm run build`) into the single-file plugin.

The plugin ships as one .py file, so the page lives in it as a generated block: zlib (level 9) + base64, between
the BEGIN/END markers, with its SHA-256, and the licence texts of what the page bundles (ui/shared/licenses: Vue,
PrimeVue, PrimeUIX, the Lucide icons and the Manrope font) as UI_LICENSES, because the release is this one file
and those licences ask for their notice in every copy. Same input, same bytes. `--check` fails when the block is missing or
differs from the built page (CI and tests use it).

    python scripts/embed_ui.py            # write the block
    python scripts/embed_ui.py --check    # verify only
"""

import argparse
import base64
import hashlib
import re
import sys
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLUGIN = ROOT / "plugin" / "spooler" / "spooler_any.py"
PAGE = ROOT / "ui" / "dist" / "spooler-ui.html"
LICENSES = ROOT / "ui" / "shared" / "licenses"
BEGIN = "# --- BEGIN GENERATED UI: scripts/embed_ui.py from ui/ (npm run build); do not edit ---\n"
END = "# --- END GENERATED UI ---\n"
WIDTH = 100


def licenses() -> str:
    """Every bundled licence text, one after the other, each under its file name."""
    texts = [f"===== {f.name} =====\n" + f.read_text(encoding="utf-8").replace("\r\n", "\n").rstrip("\n") + "\n"
             for f in sorted(LICENSES.glob("*.txt"))]
    if not texts:
        sys.exit(f"error: no licence texts in {LICENSES.relative_to(ROOT)}")
    lines = "".join(f"    {line!r}\n" for line in "\n".join(texts).splitlines(keepends=True))
    return f"# Third-party licences of the embedded page (Vue, PrimeVue, PrimeUIX, Lucide icons, Manrope font).\nUI_LICENSES = (\n{lines})\n"


def block(html: str) -> str:
    data = html.encode("utf-8")
    packed = base64.b64encode(zlib.compress(data, 9)).decode("ascii")
    lines = "".join(f'    "{packed[i:i + WIDTH]}"\n' for i in range(0, len(packed), WIDTH))
    return (BEGIN + f'UI_PAGE_SHA256 = "{hashlib.sha256(data).hexdigest()}"\n'
            + f"UI_PAGE_BYTES = {len(data)}\nUI_PAGE_Z64 = (\n{lines})\n" + licenses() + END)


def current(text: str) -> str | None:
    found = re.search(re.escape(BEGIN) + r".*?" + re.escape(END), text, re.S)
    return found.group(0) if found else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not PAGE.exists():
        print(f"error: {PAGE.relative_to(ROOT)} missing; run `npm ci && npm run build` in ui/", file=sys.stderr)
        return 1
    text = PLUGIN.read_text(encoding="utf-8")
    want = block(PAGE.read_text(encoding="utf-8"))
    have = current(text)
    if args.check:
        if have != want:
            print("error: the UI block in spooler_any.py doesn't match ui/dist/spooler-ui.html; run scripts/embed_ui.py", file=sys.stderr)
            return 1
        print("UI block matches the built page")
        return 0
    if have is None:
        sys.exit("error: no UI block markers in spooler_any.py")
    PLUGIN.write_text(text.replace(have, want), encoding="utf-8", newline="\n")
    print(f"embedded {PAGE.relative_to(ROOT)} ({PAGE.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
