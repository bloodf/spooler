#!/usr/bin/env python3
"""Write the compiled Vue page (ui/ -> ui/dist/spooler-ui.html, `npm run build`) next to the plugin, as it is served.

The served page goes to plugin/spooler/app.html, a plain file the wheel ships next to the code (spooler/app.html) and
ui_page() reads. plugin/spooler/ui_build.py keeps a generated block between the BEGIN/END markers: the page's SHA-256 and size,
and the licence texts of what the page bundles (ui/node_modules/@orca-plugins/ui-foundation/licenses: Vue, PrimeVue, PrimeUIX, the Lucide icons and the
Manrope font) as UI_LICENSES, since those licences ask for their notice in every copy. Same input, same bytes.
`--check` fails when the block or app.html is missing or differs from the built page (CI and tests use it).

The page's script goes in deflated and base64-encoded, run by scripts/page_loader.js: OrcaSlicer on Windows shows a page
through WebView2, which takes at most 2 MiB once base64-encoded (1.5 MiB of UTF-8), and a bigger page stays blank.
Both modes fail when the served page is over 90% of that, before the boot JSON is filled in. ui/build.json records the
served page.

    python scripts/embed_ui.py            # write the block
    python scripts/embed_ui.py --check    # verify only
"""

import argparse
import base64
import gzip
import hashlib
import json
import re
import sys
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLUGIN = ROOT / "plugin" / "spooler" / "ui_build.py"
SERVED = ROOT / "plugin" / "spooler" / "app.html"
PAGE = ROOT / "ui" / "dist" / "spooler-ui.html"
LICENSES = ROOT / "ui" / "node_modules" / "@orca-plugins" / "ui-foundation" / "licenses"
LOADER = ROOT / "scripts" / "page_loader.js"
BUILD_INFO = ROOT / "ui" / "build.json"
WEBVIEW_PAGE_LIMIT = 1_572_864   # bytes of UTF-8: WebView2's 2 MiB of base64
PAGE_BUDGET = WEBVIEW_PAGE_LIMIT * 9 // 10
MODULE = re.compile(r'<script type="module"[^>]*>(.*?)</script>', re.S)
BEGIN = "# --- BEGIN GENERATED UI: scripts/embed_ui.py from ui/ (npm run build); do not edit ---\n"
END = "# --- END GENERATED UI ---\n"


def licenses() -> str:
    """Every bundled licence text, one after the other, each under its file name."""
    texts = [f"===== {f.name} =====\n" + f.read_text(encoding="utf-8").replace("\r\n", "\n").rstrip("\n") + "\n"
             for f in sorted(LICENSES.glob("*.txt"))]
    if not texts:
        sys.exit(f"error: no licence texts in {LICENSES.relative_to(ROOT)}")
    lines = "".join(f"    {line!r}\n" for line in "\n".join(texts).splitlines(keepends=True))
    return f"# Third-party licences of the embedded page (Vue, PrimeVue, PrimeUIX, Lucide icons, Manrope font).\nUI_LICENSES = (\n{lines})\n"


def served(html: str) -> str:
    """The built page with its one module script deflated into #spooler-js and run by the loader."""
    found = list(MODULE.finditer(html))
    if len(found) != 1 or "</body>" not in html:
        sys.exit(f"error: {PAGE.relative_to(ROOT)} must have one module script and a </body>")
    match = found[0]
    packer = zlib.compressobj(9, zlib.DEFLATED, -15)
    data = base64.b64encode(packer.compress(match.group(1).encode("utf-8")) + packer.flush()).decode("ascii")
    page = html[:match.start()] + f'<script type="text/plain" id="spooler-js">{data}</script>' + html[match.end():]
    loader = LOADER.read_text(encoding="utf-8").replace("\r\n", "\n")
    return page.replace("</body>", f'<script type="module">\n{loader}</script>\n</body>', 1)


def over_budget(html: str) -> str | None:
    size = len(html.encode("utf-8"))
    if size <= PAGE_BUDGET:
        return None
    return (f"error: the page is {size} bytes, over {PAGE_BUDGET} (90% of the {WEBVIEW_PAGE_LIMIT} OrcaSlicer's WebView2 "
            "shows on Windows); a bigger page stays blank there")


def build_info(html: str) -> str:
    data = html.encode("utf-8")
    info = {"file": "ui/dist/spooler-ui.html, served as plugin/spooler/app.html", "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data), "gzip": len(gzip.compress(data, 9, mtime=0))}
    return json.dumps(info, indent=2) + "\n"


def block(html: str) -> str:
    data = html.encode("utf-8")
    return (BEGIN + f'UI_PAGE_SHA256 = "{hashlib.sha256(data).hexdigest()}"\n'
            + f"UI_PAGE_BYTES = {len(data)}\n" + licenses() + END)


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
    page = served(PAGE.read_text(encoding="utf-8"))
    if problem := over_budget(page):
        print(problem, file=sys.stderr)
        return 1
    want = block(page)
    have = current(text)
    if args.check:
        if have != want or not SERVED.exists() or SERVED.read_bytes() != page.encode("utf-8"):
            print("error: plugin/spooler/app.html or the UI block in ui_build.py doesn't match ui/dist/spooler-ui.html; "
                  "run scripts/embed_ui.py", file=sys.stderr)
            return 1
        print("UI block matches the built page")
        return 0
    if have is None:
        sys.exit("error: no UI block markers in plugin/spooler/ui_build.py")
    PLUGIN.write_text(text.replace(have, want), encoding="utf-8", newline="\n")
    SERVED.write_bytes(page.encode("utf-8"))
    BUILD_INFO.write_text(build_info(page), encoding="utf-8", newline="\n")
    print(f"wrote {SERVED.relative_to(ROOT)} from {PAGE.relative_to(ROOT)} ({PAGE.stat().st_size} bytes, served as {len(page.encode('utf-8'))})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
