#!/usr/bin/env python3
"""Finish the listing and README artwork from the source images in assets/marketing/source/.

Every source image has an empty rounded square. This script renders the plugin's real page with demo
data (demo_spools.json, a Snapmaker U1 and a Sovol SV06) in headless Chrome, puts that screenshot into
the square, exports the listing sizes and writes assets/marketing/asset-manifest.json:

    python scripts/store_images/render.py [--chrome PATH] [--out PATH]

Needs Node 24+, Google Chrome or Chromium, and Pillow (`pip install pillow`). Re-run it after changing
the plugin's interface so the images stay true to it. Nothing outside the square is redrawn.
"""

import argparse
import datetime
import hashlib
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SOURCE = ROOT / "assets" / "marketing" / "source"
MANIFEST = "assets/marketing/asset-manifest.json"
sys.path.insert(0, str(ROOT / "tests"))

from plugin_loader import load  # noqa: E402

U1 = "Snapmaker U1 (0.4 nozzle)"
SV06 = "Sovol SV06 0.4 nozzle"
CHROME_PATHS = (
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "google-chrome", "google-chrome-stable", "chromium", "chromium-browser",
)
# OrcaSlicer's dark theme, which the host injects into plugin pages.
ORCA_THEME = """
:root { --orca-bg: #2b2c30; --orca-fg: #eceef1; --orca-muted: #a0a3aa; --orca-border: #43454c;
        --orca-accent: #009688; --orca-accent-fg: #ffffff; }
html, body { background: var(--orca-bg); color: var(--orca-fg); margin: 0; }
::-webkit-scrollbar { display: none; }
"""
NO_SCROLLBAR = "::-webkit-scrollbar { display: none; }"

# What the square of each image shows: the tab, the messages the plugin would send after the list, and
# the steps taken on the page before the capture.
SHOWN = 12    # the spool whose detail the "what is left" screen opens
SCENES = {
    # "Know what is left": one spool's detail, with what is left and how long it lasts
    "left": {"view": "spools", "script": f"""
        document.querySelector('tr[data-spool="{SHOWN}"]').click();
        await until(function () {{ return document.querySelector('[data-detail="{SHOWN}"] .sd-history'); }});
        // End the panel at the usage chart: the print history below it would be cut by the square's edge.
        var heading = document.querySelector('[data-detail="{SHOWN}"] .sd-h');
        if (heading) {{ heading.nextElementSibling.remove(); heading.remove(); }}
        document.body.style.paddingBottom = '800px';   // room to scroll the panel to the top, so no list row shows above it
        top(document.querySelector('[data-detail="{SHOWN}"]'));
        document.activeElement.blur();"""},
    # README screenshots: the list with a spool's detail beside it, and the setup guide asking for the address
    "wide": {"view": "spools", "script": f"""
        document.querySelector('tr[data-spool="{SHOWN}"]').click();
        await until(function () {{ return document.querySelector('[data-detail="{SHOWN}"] .sd-history'); }});
        document.activeElement.blur();"""},
    "setup": {"view": "settings", "wizard_step": 1, "script": ""},
    # "See every spool at a glance": the spool list alone
    "stock": {"view": "spools", "script": """
        var close = document.querySelector('[data-test="detail-close"]');   // the detail opens by itself only when there is room
        if (close) close.click();
        document.activeElement.blur();"""},
    # "Turn stock into filament presets": the setup guide's step about the presets
    "presets": {"view": "settings", "wizard_step": 3, "script": ""},
    # "See what each slot holds": the printers and their toolheads
    "slots": {"view": "printer", "display": {"head_rfid": False}, "script": """
        // Show the first printer's toolheads only: its note and the next printer would be cut by the square's edge.
        var note = document.querySelector('.pp-note');
        if (note) {
          var panel = note.closest('.oui-panel');
          while (panel.nextElementSibling) panel.nextElementSibling.remove();
          note.remove();
        }"""},
    # "Check filament before a print": the last slice's check
    "check": {"view": "printer", "plate": True, "script": """
        await until(function () { return document.querySelector('[data-test="plate"]'); });
        top(document.querySelector('[data-test="plate"]'));
        // The check is the last thing on the page, so what is above it shows too: do not cut a line of it in half.
        var bar = document.querySelector('.oui-appbar').getBoundingClientRect().bottom, hidden = 0;
        document.querySelectorAll('.pv *').forEach(function (el) {
          var r = el.getBoundingClientRect();
          if (!el.children.length && r.height && r.top < bar && r.bottom > bar + 2) hidden = Math.max(hidden, bar - r.top);
        });
        if (hidden) scrollBy(0, -hidden - 6);"""},
}

LANGS = {"en": "en", "pt-BR": "pt_BR"}     # file suffix -> what OrcaSlicer reports as its language


def exports() -> list[dict]:
    """Every export: its source in assets/marketing/source/, where it goes, its size and what its square shows."""
    rows = [{"source": "spooler-workshop-tile.png", "file": "assets/orca-cloud/spooler-tile.png", "size": (512, 512),
             "use": "Orca Cloud store tile"}]
    for lang in LANGS:
        main = "cover-en" if lang == "en" else f"main-{lang}"
        rows.append({"source": f"spooler-workshop-{main}.png", "file": f"assets/orca-cloud/spooler-main-{lang}.png",
                     "size": (1600, 900), "scene": "left", "theme": "dark", "lang": lang, "use": "Orca Cloud main image"})
        rows.append({"source": f"spooler-workshop-main-square-{lang}.png", "file": f"assets/orca-cloud/spooler-main-square-{lang}.png",
                     "size": (900, 900), "scene": "left", "theme": "dark", "lang": lang, "page_scale": 1.8,
                     "use": "Orca Cloud square image"})
        for name, scene in (("01-stock", "stock"), ("02-presets", "presets"), ("03-slots", "slots"), ("04-check", "check")):
            rows.append({"source": f"spooler-workshop-feature-{name}-{lang}.png",
                         "file": f"assets/orca-cloud/spooler-feature-{name}-{lang}.png",
                         "size": (1600, 900), "scene": scene, "theme": "dark", "lang": lang, "use": "Orca Cloud gallery image"})
        rows.append({"source": f"spooler-workshop-social-preview-{lang}.png", "file": f"assets/social/spooler-social-preview-{lang}.png",
                     "size": (1280, 640), "scene": "left", "theme": "dark", "lang": lang, "page_scale": 1.5,
                     "use": "GitHub social preview"})
        for theme in ("dark", "light"):
            rows.append({"source": f"spooler-workshop-hero-{theme}-{lang}.png", "file": f"assets/readme/spooler-hero-{theme}-{lang}.png",
                         "size": (1600, 900), "scene": "left", "theme": theme, "lang": lang, "use": "README hero"})
    # Plain screenshots for the README: the Spools tab and the setup guide's address step.
    for lang in LANGS:
        for theme in ("dark", "light"):
            for name, scene in (("spools", "wide"), ("setup", "setup")):
                rows.append({"file": f"assets/readme/spooler-screen-{name}-{theme}-{lang}.png", "size": (1280, 720),
                             "scene": scene, "theme": theme, "lang": lang, "use": "README screenshot"})
    return rows


def demo_state(sp):
    """(spool list payload, live payload) for the plugin page."""
    spools = json.loads((HERE / "demo_spools.json").read_text(encoding="utf-8"))
    for spool in spools:
        spool["rfid_tags"] = sorted(sp.spool_tags(spool))
    printers = [{"target": U1, "label": "Snapmaker U1"}, {"target": SV06, "label": "Sovol SV06"}]
    sp._profiles["names"] = sp.profile_names(spools, printers)
    by_id = {s["id"]: s for s in spools}
    heads = [3, 4, 6, 5]
    u1 = {"print_task_config": {
        "filament_exist": [True] * 4,
        "filament_type": [by_id[i]["filament"]["material"] for i in heads],
        "filament_sub_type": ["SnapSpeed"] * 4,
        "filament_vendor": ["Snapmaker"] * 4,
        "filament_color_rgba": [by_id[i]["filament"]["color_hex"] + "FF" for i in heads],
        "filament_spool_id": heads,
    }, "filament_detect": {"info": [{"CARD_UID": [0x60, 0x82, 0x7A, 0x6A]}] * 4}}
    sp._live["printers"].clear()
    for pid, name, doc in (("auto-u1", "Snapmaker U1", sp.moon_report(u1, None, spools, U1)),
                           ("auto-sv06", "Sovol SV06", sp.moon_report({}, 11, spools, SV06))):
        sp.live_apply(pid, name, doc[0], link=pid)
        with sp._live_lock:
            sp.moon_mark(pid, doc[0], doc[1])
        sp._live["links"][pid] = "live"
    cfg = [{"id": "auto-u1", "name": "Snapmaker U1", "units": [], "ip": "http://192.168.1.40", "serial": "",
            "kind": "moonraker", "auto": True, "has_code": True},
           {"id": "auto-sv06", "name": "Sovol SV06", "units": [], "ip": "http://192.168.1.41", "serial": "",
            "kind": "moonraker", "auto": True, "has_code": True}]
    spools_msg = {"type": "spools", "ok": True, "spools": spools, "low_stock_grams": 100,
                  "show_printer_tab": True,
                  "weight_display": "both", "show_cart": False, "spool_columns": 2,
                  "printers": cfg, "live_ok": True, "usage": {"mode": "off", "runs": []},
                  "progress": sp.progress_settings(), "profiles": {"count": 24, "error": ""}}
    live_msg = {"type": "live", "live": sp.live_snapshot(), "usage": {"mode": "off", "runs": []}}
    return spools_msg, live_msg


def demo_plate(sp, spools_msg: dict) -> dict:
    """The filament check of a demo slice, worded by the plugin itself (plate_rows)."""
    by_id = {s["id"]: s for s in spools_msg["spools"]}

    def result(number: int, spool_id: int, need: float, status: str) -> dict:
        spool, filament = by_id[spool_id], by_id[spool_id]["filament"]
        return {"slot": {"preset": f'{filament["vendor"]["name"]} {filament["name"]} @Snapmaker U1',
                         "vendor": filament["vendor"]["name"], "material": filament["material"], "colour": filament["color_hex"]},
                "slots": [number], "status": status, "need": need, "have": spool["remaining_weight"],
                "total": spool["initial_weight"], "pool": 1, "matches": 1, "worst": spool["remaining_weight"], "ids": [spool_id]}

    rows = sp.plate_rows([result(1, 3, 86, "ok"), result(2, 4, 143, "ok"), result(4, 5, 128, "short")])
    return {"type": "plate", "time": "10:42", "rows": rows}


def demo_detail(sp) -> dict:
    """What the plugin answers when the page asks for a spool's history (spool_detail); the page fills in the id."""
    now = time.time()
    prints = [("Desk_Organiser_Plate_1", 96.0), ("Headphone_Stand", 94.3), ("Cable_Clip_x12", 31.5), ("Drawer_Divider_Set", 125.7)]
    return {"type": "spool_detail", "detail": {
        "sign": "€", "grams": 360, "cost": 7.2, "rate": 90, "weeks": 7.1,
        "prints": [{"time": now - i * 5 * 86400 - 3600, "name": name, "grams": grams, "cost": grams * 0.02}
                   for i, (name, grams) in enumerate(prints)]}}


@contextmanager
def host_language(sp, lang: str | None):
    """Serve the page as OrcaSlicer would in ``lang`` (None: leave the plugin's own answer)."""
    if lang is None:
        yield
        return
    was = sp.host_language
    sp.host_language = lambda: lang
    try:
        yield
    finally:
        sp.host_language = was


def plugin_page(sp, view: str, spools_msg: dict, live_msg: dict, wizard_step: int | None = None, *,
                lang: str | None = None, host_theme: bool = True, after: tuple = (), replies: dict | None = None,
                script: str = "") -> str:
    """The plugin's page with a scripted bridge. ``wizard_step`` opens the setup guide on that step (0-5) over
    the Settings view; ``after`` are messages sent once the list is in, ``replies`` answers by message type and
    ``script`` runs on the page before it is captured."""
    with host_language(sp, lang):
        page = sp.tab_html(initial_view="settings" if view == "settings" else "main",
                           current_url="http://spoolman.local:7912", low_stock_grams=100,
                           columns=2, progress=sp.progress_settings(), wizard=wizard_step is not None)
    bridge = f"""<style>{ORCA_THEME if host_theme else NO_SCROLLBAR}</style><script>
(function () {{
  window.addEventListener('error', function(e) {{ document.documentElement.dataset.renderError = e.message; }});
  window.addEventListener('unhandledrejection', function(e) {{ document.documentElement.dataset.renderError = String(e.reason); }});
  var handlers = [];
  var spools = {json.dumps(spools_msg)};
  var live = {json.dumps(live_msg)};
  var after = {json.dumps(list(after))};
  var replies = {json.dumps(replies or {})};
  function send(data) {{ setTimeout(function () {{ handlers.forEach(function (h) {{ h(data); }}); }}, 20); }}
  window.orca = {{
    onMessage: function (cb) {{ handlers.push(cb); }},
    postMessage: function (m) {{
      if (!m) return;
      if (m.view === "settings") {{
        if (m.type === "ready" || m.type === "test")
          send({{view: "settings", type: "test_result", source: "spoolman", ok: true,
                url: "http://spoolman.local:7912", version: "0.27.1"}});
        return;
      }}
      if (m.type === "ready" || m.type === "refresh") send(spools);
      if (m.type === "ready") after.forEach(send);
      if (m.type === "live") send(live);
      var reply = replies[m.type];
      if (reply && reply.detail) reply = Object.assign({{}}, reply, {{detail: Object.assign({{id: m.id}}, reply.detail)}});
      if (reply) send(reply);
    }}
  }};
  function sleep(ms) {{ return new Promise(function (r) {{ setTimeout(r, ms); }}); }}
  async function until(test) {{
    for (var end = Date.now() + 4000; !test();) {{ if (Date.now() > end) throw Error('Timed out: ' + test); await sleep(30); }}
  }}
  // Scroll ``el`` to just under the page's sticky bar.
  function top(el) {{
    var bar = document.querySelector('.oui-appbar');
    scrollBy(0, el.getBoundingClientRect().top - (bar ? bar.getBoundingClientRect().bottom : 0) - 12);
  }}
  window.addEventListener("load", function () {{
    var steps = sleep(200).then(async function () {{
      var tab = document.querySelector('[data-tab="{'printer' if view == 'printer' else 'spools'}"]');
      if ({json.dumps(view != 'settings')}) {{
        if (!tab) throw Error('Requested tab is not available');
        tab.click();
      }}
      for (var remaining = {wizard_step or 0}; remaining; remaining--) {{
        var next = document.querySelector('[data-test="wiz-next"]');
        if (!next || next.disabled) throw Error('Wizard step is not available');
        next.click(); await sleep(100);
      }}
      await sleep(300);
      {script}
    }});
    Promise.all([steps, sleep(1200)]).then(async function () {{
      if (!document.querySelector('#app .p-button')) throw Error('Vue did not mount');
      await sleep(300);
      document.documentElement.dataset.renderReady = 'true';
    }});
  }});
}})();
</script>"""
    return page.replace("<head>", "<head>" + bridge, 1) if "<head>" in page else bridge + page


def find_chrome(given: str | None) -> str:
    for candidate in ([given] if given else []) + list(CHROME_PATHS):
        found = shutil.which(candidate) or (candidate if Path(candidate).exists() else None)
        if found:
            return found
    sys.exit("Google Chrome or Chromium was not found; pass --chrome PATH")


# ------------------------------------------------------------------ the empty square

def find_square(im, tolerance: int = 26) -> tuple[tuple[int, int, int, int], int]:
    """(inner rectangle, corner radius) of the image's empty square, read from its pixels: the largest flat
    patch gives a point inside it, and its plain fill is followed out to the frame on every side."""
    from PIL import ImageFilter

    width, height = im.size
    flat = im.convert("L").filter(ImageFilter.FIND_EDGES).filter(ImageFilter.BoxBlur(min(width, height) // 12))
    margin = min(width, height) // 8      # the blur is not meaningful near the border
    inner = flat.crop((margin, margin, width - margin, height - margin))
    low = inner.getextrema()[0]
    box = inner.point(lambda v: 255 if v <= low else 0).getbbox()
    sx, sy = margin + (box[0] + box[2]) // 2, margin + (box[1] + box[3]) // 2
    px = im.load()
    fill = px[sx, sy]

    def same(x: int, y: int) -> bool:
        return 0 <= x < width and 0 <= y < height and sum(abs(a - b) for a, b in zip(px[x, y], fill)) <= tolerance

    def run(x: int, y: int, dx: int, dy: int) -> int:
        steps = 0
        while same(x + dx * (steps + 1), y + dy * (steps + 1)):
            steps += 1
        return steps

    def middle(values: list[int]) -> int:
        return sorted(values)[len(values) // 2]

    # A few parallel lines each way, so a speck of noise on one of them does not move the edge.
    offsets = [-80, -40, 0, 40, 80]
    x0 = sx - middle([run(sx, sy + o, -1, 0) for o in offsets])
    x1 = sx + middle([run(sx, sy + o, 1, 0) for o in offsets]) + 1
    y0 = sy - middle([run(sx + o, sy, 0, -1) for o in offsets])
    y1 = sy + middle([run(sx + o, sy, 0, 1) for o in offsets]) + 1
    if not (0.85 < (x1 - x0) / (y1 - y0) < 1.2 and (y1 - y0) > height / 4):
        raise SystemExit(f"no empty square found (got {x0},{y0} - {x1},{y1})")
    # A corner of radius r first meets its own diagonal r * (1 - 1/sqrt 2) in from the corner.
    corners = []
    for cx, cy, dx, dy in ((x0, y0, 1, 1), (x1 - 1, y0, -1, 1), (x0, y1 - 1, 1, -1), (x1 - 1, y1 - 1, -1, -1)):
        d = next((d for d in range(40) if same(cx + dx * d, cy + dy * d)), 0)
        corners.append(d / (1 - math.sqrt(0.5)))
    return (x0, y0, x1, y1), max(4, min(24, round(middle(corners))))


def fit(im, size: tuple[int, int]):
    """``im`` at ``size``: scaled, after a centred crop when the shapes differ by more than rounding."""
    from PIL import Image

    width, height = im.size
    want = size[0] / size[1]
    crop = (0, 0, width, height)
    if abs(width / height - want) > 0.005:
        if width / height > want:
            w = round(height * want)
            crop = ((width - w) // 2, 0, (width - w) // 2 + w, height)
        else:
            h = round(width / want)
            crop = (0, (height - h) // 2, width, (height - h) // 2 + h)
    return im.crop(crop).resize(size, Image.LANCZOS), crop


def place(art, shot, rect: tuple[int, int, int, int], radius: float):
    """Paste ``shot`` over ``rect`` of ``art``, clipped to the square's rounded corners."""
    from PIL import Image, ImageDraw

    w, h = rect[2] - rect[0], rect[3] - rect[1]
    over = 4
    mask = Image.new("L", (w * over, h * over), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, w * over - 1, h * over - 1), radius=radius * over, fill=255)
    art.paste(shot.convert("RGB").resize((w, h), Image.LANCZOS), rect[:2], mask.resize((w, h), Image.LANCZOS))


def capture(command: list[str], chrome: str) -> None:
    """Run one capture; a busy machine can stall headless Chrome, so a stalled one is tried again."""
    for attempt in range(3):
        try:
            subprocess.run(command, env={**os.environ, "CHROME": chrome}, check=True, timeout=60)
            return
        except subprocess.TimeoutExpired:
            if attempt == 2:
                raise
            print("capture stalled, trying again")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--chrome", help="path to Google Chrome or Chromium")
    parser.add_argument("--out", type=Path, default=ROOT,
                        help="write under this folder instead of the repository (to preview without replacing the artwork)")
    args = parser.parse_args()
    try:
        from PIL import Image
    except ImportError:
        sys.exit("Pillow is needed to composite the images: pip install pillow")
    chrome = find_chrome(args.chrome)
    out_root = args.out.resolve()
    sp, _ = load()
    spools_msg, live_msg = demo_state(sp)
    plate, detail = demo_plate(sp, spools_msg), demo_detail(sp)
    today = datetime.date.today().isoformat()
    sources, records = {}, []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)

        def shoot(row: dict, width: int, height: int):
            """The page of ``row`` (scene, theme, language) at ``width`` x ``height``, captured twice as dense."""
            scene, stem = SCENES[row["scene"]], Path(row["file"]).stem
            shown = {**spools_msg, "display": {**sp.DISPLAY_DEFAULTS, **scene.get("display", {})}}
            page = plugin_page(sp, scene["view"], shown, live_msg, scene.get("wizard_step"),
                               lang=LANGS[row["lang"]], host_theme=False, after=(plate,) if scene.get("plate") else (),
                               replies={"spool_detail": detail}, script=scene["script"])
            (work / f"{stem}.html").write_text(page, encoding="utf-8")
            # The test launcher supplies --use-mock-keychain --password-store=basic.
            capture(["node", str(ROOT / "scripts/render_page.mjs"),
                     (work / f"{stem}.html").as_uri() + "?theme=" + row["theme"], str(work / f"{stem}.png"),
                     str(width), str(height), "2", "true", str(out_root / "render-failures")], chrome)
            return Image.open(work / f"{stem}.png").convert("RGB")

        for row in exports():
            record = {"file": row["file"], "use": row["use"]}
            if "scene" in row:
                record.update({"screen": row["scene"], "theme": row["theme"], "language": row["lang"]})
            if "source" not in row:     # a plain screenshot
                art = shoot(row, *row["size"])
                operation = [f"page screenshot ({row['scene']}, {row['theme']}, {row['lang']}, "
                             f"{row['size'][0]}x{row['size'][1]} at 2x)"]
            else:
                src = SOURCE / row["source"]
                native = Image.open(src).convert("RGB")
                sources[row["source"]] = {"file": f"assets/marketing/source/{row['source']}", "width": native.width,
                                          "height": native.height, "bytes": src.stat().st_size, "sha256": sha256(src)}
                record["source"] = sources[row["source"]]["file"]
                art, crop = fit(native, row["size"])
                operation = ["scaled" if crop == (0, 0, *native.size) else f"cropped to {crop}, scaled"]
            if "source" in row and "scene" in row:
                (nx0, ny0, nx1, ny1), nradius = find_square(native)
                sx, sy = row["size"][0] / (crop[2] - crop[0]), row["size"][1] / (crop[3] - crop[1])
                # Inside the frame at the export size: rounded inwards, so the frame stays whole.
                rect = (math.ceil((nx0 - crop[0]) * sx), math.ceil((ny0 - crop[1]) * sy),
                        math.floor((nx1 - crop[0]) * sx), math.floor((ny1 - crop[1]) * sy))
                # The page is laid out at the square's own size, so its text lands sharp; a small square gets a
                # larger page (page_scale) scaled down, or it would show the app bar and little else.
                zoom = row.get("page_scale", 1)
                width, height = round((rect[2] - rect[0]) * zoom), round((rect[3] - rect[1]) * zoom)
                place(art, shoot(row, width, height), rect, nradius * sx)
                operation.append(f"page screenshot ({row['scene']}, {row['theme']}, {row['lang']}, {width}x{height} at 2x) "
                                 f"placed in the empty square, corners rounded {round(nradius * sx, 1)} px")
                record.update({"square_in_source": [nx0, ny0, nx1, ny1], "square": list(rect)})
            out = out_root / row["file"]
            out.parent.mkdir(parents=True, exist_ok=True)
            art.save(out, optimize=True)
            if out.stat().st_size >= 2_000_000:
                sys.exit(f"{out} is {out.stat().st_size} bytes; the listing takes images under 2 MB")
            record.update({"operation": "; ".join(operation), "width": art.width, "height": art.height,
                           "bytes": out.stat().st_size, "sha256": sha256(out), "date": today})
            records.append(record)
            print("exported MOCK", out)
    manifest = {
        "note": "Written by scripts/store_images/render.py. Sources are the generated artwork at its native size; "
                "exports carry a screenshot of the plugin's page with demo data in the source's empty square. "
                "Exports without a source are plain screenshots of that page.",
        "sources": sorted(sources.values(), key=lambda s: s["file"]),
        "exports": records,
    }
    path = out_root / MANIFEST
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("wrote", path)


if __name__ == "__main__":
    main()
