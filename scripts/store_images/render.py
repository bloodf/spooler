#!/usr/bin/env python3
"""Render the Orca Cloud store images (1920x1080) into assets/orca-cloud/.

The plugin's real page is rendered with demo data (demo_spools.json, a Snapmaker U1 and a
Sovol SV06), framed in the brand layout and captured with headless Google Chrome:

    python scripts/store_images/render.py [--chrome PATH] [--out PATH]

Re-run it after changing the plugin's interface so the images stay true to it.
"""

import argparse
import html
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = ROOT / "assets" / "orca-cloud"
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

SYMBOL = (ROOT / "assets" / "spooler-icon.svg").read_text(encoding="utf-8")
SYMBOL = SYMBOL[SYMBOL.index("<g "):SYMBOL.rindex("</svg>")]
WORDMARK = (ROOT / "assets" / "spooler-wordmark.svg").as_uri()

SCREENS = [
    {
        "file": "spooler-store-image-spool-list.png",
        "title": 'Every spool,<br><em>already in OrcaSlicer</em>',
        "points": [
            "Colour, remaining weight and RFID tags for every Spoolman spool",
            "Each filament becomes an OrcaSlicer preset in its real colour",
            "Filter, sort and group by material, vendor or location",
            "Low-stock warnings before a spool runs out",
        ],
        "page": "spools",
        "height": 690,
    },
    {
        "file": "spooler-store-image-printer.png",
        "title": 'Every toolhead,<br><em>read live</em>',
        "points": [
            "Printers come from your OrcaSlicer printer presets, nothing to add",
            "Snapmaker U1 toolheads matched to the exact Spoolman spool",
            "Klipper printers show Moonraker's active spool",
            "Remaining filament per slot, with its OrcaSlicer preset on hover",
        ],
        "page": "printer",
        "height": 600,
    },
    {
        "file": "spooler-store-image-settings.png",
        "title": 'One address.<br><em>The rest is automatic.</em>',
        "points": [
            "Enter your Spoolman server once",
            "Filament presets are created and kept in sync for every printer",
            "Tuned per printer, from the closest preset OrcaSlicer already has",
            "Runs on Windows, macOS and Linux",
        ],
        "page": "settings",
        "height": 780,
    },
    {
        "file": "spooler-store-image-wizard.png",
        "title": 'Set up in a minute,<br><em>step by step</em>',
        "points": [
            "A short guide opens the first time you use Spooler",
            "Connect Spoolman or Bambu Cloud and test it right there",
            "Learn where presets appear and how printers are found",
            "Skip any time, reopen it from Settings",
        ],
        "page": "wizard",
        "height": 780,
    },
    {
        "file": "spooler-store-image-presets.png",
        "title": 'Pick a filament,<br><em>the colour comes with it</em>',
        "points": [
            "Your Spoolman filaments, listed under User presets",
            "One preset per printer, so each keeps its own tuning",
            "Temperatures, density and cost straight from Spoolman",
            "New spools appear on their own, used-up ones disappear",
        ],
        "page": "presets",
        "height": 560,
    },
]


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


def plugin_page(sp, view: str, spools_msg: dict, live_msg: dict, wizard_step: int | None = None) -> str:
    """``wizard_step`` opens the setup guide on that step (0-5) over the Settings view."""
    page = sp.tab_html(initial_view="settings" if view == "settings" else "main",
                       current_url="http://spoolman.local:7912", low_stock_grams=100,
                       columns=2, progress=sp.progress_settings(), wizard=wizard_step is not None)
    bridge = f"""<style>{ORCA_THEME}</style><script>
(function () {{
  window.addEventListener('error', function(e) {{ document.documentElement.dataset.renderError = e.message; }});
  window.addEventListener('unhandledrejection', function(e) {{ document.documentElement.dataset.renderError = String(e.reason); }});
  var handlers = [];
  var spools = {json.dumps(spools_msg)};
  var live = {json.dumps(live_msg)};
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
      if (m.type === "live") send(live);
    }}
  }};
  window.addEventListener("load", function () {{
    setTimeout(function () {{
      var tab = document.querySelector('[data-tab="{'printer' if view == 'printer' else 'spools'}"]');
      if ({json.dumps(view != 'settings')}) {{
        if (!tab) throw Error('Requested tab is not available');
        tab.click();
      }}
      if ({json.dumps(wizard_step is not None)}) {{
        var remaining = {wizard_step or 0};
        function advance() {{
          if (!remaining) return;
          var next = document.querySelector('[data-test="wiz-next"]');
          if (!next || next.disabled) throw Error('Wizard step is not available');
          next.click(); remaining--; setTimeout(advance, 100);
        }}
        advance();
      }}
    }}, 200);
    setTimeout(function () {{
      if (!document.querySelector('#app .p-button')) throw Error('Vue did not mount');
      document.documentElement.dataset.renderReady = 'true';
    }}, 1200);
  }});
}})();
</script>"""
    return page.replace("<head>", "<head>" + bridge, 1) if "<head>" in page else bridge + page


def presets_mock(sp, spools_msg: dict) -> str:
    """A filament slot dropdown showing the presets Spooler adds (an illustration)."""
    spools = spools_msg["spools"]
    names = sp.profile_names(spools, [{"target": U1, "label": "Snapmaker U1"}])
    colour = {s["filament"]["id"]: s["filament"]["color_hex"] for s in spools}
    items = "".join(
        f'<div class="item{" on" if fid == 1 else ""}"><span class="sw" style="background:#{colour[fid]}"></span>'
        f'{html.escape(name)}</div>' for (fid, _), name in list(names.items())[:9])
    slots = "".join(
        f'<div class="slot"><span class="n" style="background:#{c}">{i}</span>'
        f'<span class="combo">{html.escape(n)}<b>&#8964;</b></span></div>'
        for i, (c, n) in enumerate([("F4C032", "Snapmaker PLA SnapSpeed Yellow @Snapmaker U1"),
                                     ("E72F1D", "Snapmaker PLA SnapSpeed Red @Snapmaker U1"),
                                     ("E2DEDB", "Snapmaker PLA SnapSpeed White @Snapmaker U1"),
                                     ("080A0D", "Snapmaker PLA SnapSpeed Black @Snapmaker U1")], 1))
    return f"""<!doctype html><html><head><meta charset="utf-8"><style>{ORCA_THEME}
body {{ font: 14px/1.4 -apple-system, "Segoe UI", Roboto, sans-serif; padding: 22px; }}
h3 {{ margin: 0 0 16px; font-size: 16px; font-weight: 600; }}
.slot {{ display: flex; align-items: center; gap: 12px; margin-bottom: 12px; }}
.n {{ width: 30px; height: 30px; border-radius: 4px; display: grid; place-items: center; font-weight: 700;
      color: #14181F; flex: none; box-shadow: inset 0 0 0 1px rgba(255,255,255,.25); }}
.slot:nth-child(5) .n {{ color: #fff; }}
.combo {{ flex: 1; border: 1px solid var(--orca-border); border-radius: 4px; padding: 7px 12px;
          display: flex; justify-content: space-between; }}
.combo b {{ color: var(--orca-muted); font-weight: 400; }}
.menu {{ position: absolute; left: 64px; top: 110px; width: 470px; background: #34353a;
         border: 1px solid #55575e; border-radius: 6px; padding: 8px 0; box-shadow: 0 18px 40px rgba(0,0,0,.45); }}
.group {{ color: var(--orca-muted); font-size: 12px; padding: 6px 16px; display: flex; gap: 10px; align-items: center; }}
.group:after {{ content: ""; flex: 1; border-top: 1px solid #55575e; }}
.item {{ display: flex; gap: 10px; align-items: center; padding: 7px 16px; }}
.item.on {{ background: color-mix(in srgb, var(--orca-accent) 30%, transparent); }}
.sw {{ width: 14px; height: 14px; border-radius: 3px; flex: none; box-shadow: inset 0 0 0 1px rgba(255,255,255,.3); }}
.sys {{ color: var(--orca-fg); padding: 7px 16px; display: flex; justify-content: space-between; }}
</style></head><body><h3>Filament</h3>{slots}
<div class="menu"><div class="group">User presets &middot; Spooler (Spoolman)</div>{items}
<div class="group">System presets</div><div class="sys">Generic <span>&rsaquo;</span></div>
<div class="sys">Snapmaker <span>&rsaquo;</span></div></div></body></html>"""


def frame(screen: dict, inner: str, inner_height: int) -> str:
    points = "".join(f"<li>{html.escape(p)}</li>" for p in screen["points"])
    return f"""<!doctype html><html><head><meta charset="utf-8">
<style>
* {{ box-sizing: border-box; }}
html, body {{ margin: 0; width: 1920px; height: 1080px; overflow: hidden; }}
body {{ font-family: "Space Grotesk", sans-serif; color: #F6F7FB; background:
  radial-gradient(900px 600px at 8% 0%, rgba(169,155,255,.22), transparent 70%),
  radial-gradient(700px 500px at 100% 100%, rgba(120,207,213,.14), transparent 70%), #14181F; }}
.left {{ position: absolute; left: 90px; top: 72px; bottom: 110px; width: 680px; display: flex; flex-direction: column; }}
.brand {{ display: flex; align-items: center; gap: 18px; }}
.brand svg {{ width: 72px; height: 72px; }}
.brand img {{ height: 64px; }}
h1 {{ margin: 0; flex: 1; display: flex; flex-direction: column; justify-content: center; font-size: 72px;
      line-height: 1.04; font-weight: 600; letter-spacing: -1.5px; }}
h1 em {{ font-style: normal; color: #A99BFF; }}
h1 span {{ display: block; }}
ul {{ margin: 0 0 10px; padding: 0; list-style: none; }}
li {{ position: relative; padding-left: 52px; margin-bottom: 26px; font-size: 27px; line-height: 1.3; color: #DADCE5; }}
li:before {{ content: ""; position: absolute; left: 0; top: 2px; width: 32px; height: 32px; border-radius: 50%;
             background: #A99BFF url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cpath d='M6 12.5l4 4 8-9' fill='none' stroke='%2314181F' stroke-width='2.6' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E") center/20px no-repeat; }}
.window {{ position: absolute; right: 90px; top: {(1080 - inner_height) // 2 - 20}px; width: 1040px; height: {inner_height}px; border-radius: 14px;
           overflow: hidden; border: 1px solid #3a3f4b; box-shadow: 0 40px 90px rgba(0,0,0,.55), 0 0 0 6px rgba(169,155,255,.06); }}
.window iframe {{ width: 100%; height: 100%; border: 0; display: block; }}
footer {{ position: absolute; left: 90px; bottom: 54px; font-size: 19px; color: #8B90A0; }}
</style></head><body>
<div class="left"><div class="brand"><svg viewBox="0 0 256 256">{SYMBOL}</svg><img src="{WORDMARK}" alt="Spooler"></div>
<h1><span>{screen["title"]}</span></h1><ul>{points}</ul></div>
<div class="window"><iframe src="{inner}"></iframe></div>
<footer>MOCK preview · Independent community project, based on Spoolio. Not affiliated with OrcaSlicer or printer manufacturers.</footer>
<script>
setTimeout(function () {{
  const inner = document.querySelector('iframe').contentDocument;
  const ok = inner && !inner.documentElement.dataset.renderError &&
    ({str(screen['page'] == 'presets').lower()} || inner.documentElement.dataset.renderReady === 'true');
  document.documentElement.dataset.renderReady = String(!!ok);
  if (!ok) document.documentElement.dataset.renderError = inner?.documentElement.dataset.renderError || 'Vue preview did not finish';
}}, 2500);
</script>
</body></html>"""


def find_chrome(given: str | None) -> str:
    for candidate in ([given] if given else []) + list(CHROME_PATHS):
        found = shutil.which(candidate) or (candidate if Path(candidate).exists() else None)
        if found:
            return found
    sys.exit("Google Chrome or Chromium was not found; pass --chrome PATH")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--chrome", help="path to Google Chrome or Chromium")
    parser.add_argument("--out", type=Path, default=OUT, help="output folder (use a temporary folder to preserve published artwork)")
    args = parser.parse_args()
    chrome = find_chrome(args.chrome)
    sp, _ = load()
    spools_msg, live_msg = demo_state(sp)
    args.out.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for screen in SCREENS:
            stem = Path(screen["file"]).stem
            height = screen["height"]
            if screen["page"] == "presets":
                inner = presets_mock(sp, spools_msg)
            else:
                inner = plugin_page(sp, "settings" if screen["page"] == "wizard" else screen["page"],
                                    spools_msg, live_msg, 1 if screen["page"] == "wizard" else None)
            (work / f"{stem}-inner.html").write_text(inner, encoding="utf-8")
            (work / f"{stem}.html").write_text(frame(screen, f"{stem}-inner.html", height), encoding="utf-8")
            out = args.out.resolve() / screen["file"]
            # The test launcher supplies --use-mock-keychain --password-store=basic.
            subprocess.run(["node", str(ROOT / "scripts/render_page.mjs"), (work / f"{stem}.html").as_uri(),
                            str(out), "1920", "1080", "1", "true", str(args.out.resolve())],
                           env={**os.environ, "CHROME": chrome}, check=True, timeout=90)
            print("rendered MOCK", out)


if __name__ == "__main__":
    main()
