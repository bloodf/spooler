#!/usr/bin/env python3
"""Render the install guide illustrations (1600x900) into assets/orca-cloud/install/.

Drawn mock-ups in OrcaSlicer's dark theme, simplified and illustrative, not screenshots:

    python scripts/store_images/install_guide.py [--chrome PATH]
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from render import ORCA_THEME, ROOT, demo_state, find_chrome, load, plugin_page  # noqa: E402

OUT = ROOT / "assets" / "orca-cloud" / "install"
MONO = "font-family:ui-monospace,Menlo,monospace"

CSS = ORCA_THEME + """
* { box-sizing: border-box; }
html, body { width: 1600px; height: 900px; overflow: hidden; }
body { font: 24px/1.4 -apple-system, "Segoe UI", Roboto, sans-serif; position: relative; }
.win { position: absolute; left: 120px; right: 120px; top: 110px; bottom: 110px; background: #34353a;
       border: 1px solid #55575e; border-radius: 12px; box-shadow: 0 24px 60px rgba(0,0,0,.5); }
.title { padding: 16px 24px; border-bottom: 1px solid var(--orca-border); font-weight: 600; font-size: 26px; }
.cap { position: absolute; left: 120px; right: 120px; top: 36px; font-size: 30px; font-weight: 600; }
.cap small { color: var(--orca-muted); font-weight: 400; font-size: 22px; margin-left: 14px; }
.note { position: absolute; left: 120px; right: 120px; bottom: 36px; color: var(--orca-muted); font-size: 22px; }
.btn { display: inline-block; padding: 8px 22px; border: 1px solid #55575e; border-radius: 6px; background: #3d3e44; position: relative; }
.hl { outline: 3px solid var(--orca-accent); outline-offset: 4px; border-radius: 6px; position: relative; }
.badge { position: absolute; width: 40px; height: 40px; border-radius: 50%; background: var(--orca-accent);
         color: #fff; font-weight: 700; font-size: 24px; display: grid; place-items: center;
         box-shadow: 0 0 0 4px var(--orca-bg); }
.accent { background: var(--orca-accent); border-color: var(--orca-accent); color: #fff; }
.muted { color: var(--orca-muted); }
.input { padding: 10px 16px; background: #2b2c30; border: 1px solid var(--orca-border); border-radius: 6px; }
.box { width: 26px; height: 26px; border: 2px solid #7b7e86; border-radius: 4px; display: inline-grid; place-items: center;
       vertical-align: middle; }
.box.on { background: var(--orca-accent); border-color: var(--orca-accent); color: #fff; font-size: 20px; }
"""

SPOOL = ('<svg width="{s}" height="{s}" viewBox="0 0 64 64"><circle cx="32" cy="32" r="28" fill="#009688"/>'
         '<circle cx="32" cy="32" r="18" fill="#2b2c30"/><circle cx="32" cy="32" r="7" fill="#009688"/></svg>')


def page(body: str) -> str:
    return f'<!doctype html><html><head><meta charset="utf-8"><style>{CSS}</style></head><body>{body}</body></html>'


def hub_card(name: str, sub: str, selected: bool = False) -> str:
    border = "var(--orca-accent)" if selected else "var(--orca-border)"
    button = ('<span class="btn accent hl">Subscribe<span class="badge" style="left:-30px;top:-30px">1</span></span>'
              if selected else '<span class="btn">Subscribe</span>')
    return (f'<div style="width:420px;padding:22px;border:1px solid {border};border-radius:10px;background:#2f3034">'
            f'<div style="display:flex;gap:16px;align-items:center">{SPOOL.format(s=64)}<div>'
            f'<div style="font-size:28px;font-weight:600">{name}</div>'
            f'<div class="muted" style="font-size:20px">{sub}</div></div></div>'
            '<div class="muted" style="font-size:20px;margin:16px 0 22px">Illustrative description text.</div>'
            f'{button}</div>')


def plugin_hub() -> str:
    return page(f"""<div class="cap">Orca Cloud Plugin Hub<small>find Spooler and subscribe</small></div>
<div class="win"><div class="title">Plugin Hub</div>
<div style="padding:34px;display:flex;gap:28px;flex-wrap:wrap">
{hub_card("Spooler", "Spoolman filament presets", True)}{hub_card("Example plugin", "Another plugin")}{hub_card("Example plugin", "Another plugin")}
</div></div>
<div class="note">Click Subscribe on the Spooler card. Updates arrive through the same subscription.</div>""")


def dialog_row(name: str, active: bool = False) -> str:
    bg = "background:color-mix(in srgb,var(--orca-accent) 18%,transparent)" if active else ""
    icon = SPOOL.format(s=40) if active else ""
    box = ('<span class="hl" style="padding:2px 12px 2px 4px"><span class="box on">&#10003;</span> Activate'
           '<span class="badge" style="left:-34px;top:-34px">2</span></span>' if active
           else '<span><span class="box"></span> Activate</span>')
    return (f'<div style="display:flex;align-items:center;gap:20px;padding:18px 28px;'
            f'border-bottom:1px solid var(--orca-border);{bg}">{icon}'
            f'<div style="flex:1;font-size:26px">{name}</div>{box}</div>')


def plugins_dialog() -> str:
    return page(f"""<div class="cap">File &rsaquo; Plugins<small>refresh the list, then activate Spooler</small></div>
<div class="win"><div class="title" style="display:flex;justify-content:space-between;align-items:center">Plugins
<span class="btn hl">Refresh<span class="badge" style="left:-30px;top:-30px">1</span></span></div>
{dialog_row("Example plugin")}{dialog_row("Spooler", True)}{dialog_row("Example plugin")}</div>
<div class="note">Rows and labels are simplified. Tick Activate for Spooler once it appears in the list.</div>""")


def permission() -> str:
    return page(f"""<div class="cap">Permission prompt<small>OrcaSlicer asks before a plugin does anything sensitive</small></div>
<div class="win" style="left:260px;right:260px;top:130px;bottom:230px">
<div class="title">Permission request</div>
<div style="padding:30px 34px;font-size:26px"><b>Spooler</b> wants to reach a network address:
<div class="input" style="margin:22px 0;{MONO}">http://192.168.1.20:7912</div>
<div style="display:flex;gap:28px;justify-content:flex-end;margin-top:40px">
<span class="btn">Deny</span><span class="btn accent hl">Allow<span class="badge" style="left:-30px;top:-30px">1</span></span></div></div></div>
<div style="position:absolute;left:120px;right:120px;top:730px;font-size:24px;display:flex;gap:16px;align-items:center">
<span class="accent" style="flex:none;width:36px;height:36px;border-radius:50%;display:grid;place-items:center;font-weight:700">i</span>
<span>Granting full access in the permission dialog avoids repeated prompts. Otherwise each new address is approved once and remembered.</span></div>""")


def tab(name: str, active: bool = False) -> str:
    style = "background:var(--orca-accent);color:#fff;border-radius:6px" if active else "color:var(--orca-muted)"
    return f'<span style="padding:10px 26px;font-size:26px;{style}">{name}</span>'


WIZARD_PAGE = "wizard-address.html"  # the real setup guide, rendered by main() beside the shots


def spooler_tab() -> str:
    return page(f"""<div class="cap">OrcaSlicer top bar<small>the Spooler tab sits next to the built-in tabs</small></div>
<div class="win" style="top:130px;bottom:auto;height:120px;overflow:visible">
<div style="display:flex;gap:22px;align-items:center;justify-content:center;height:100%">
{tab("Prepare")}{tab("Preview")}{tab("Device")}
<span class="hl">{tab("Spooler", True)}<span class="badge" style="right:-24px;top:-36px">1</span></span></div></div>
<div class="muted" style="position:absolute;left:120px;right:120px;top:286px;font-size:26px">On first run the setup guide opens. Enter your Spoolman address and click Test:</div>
<div style="position:absolute;left:420px;top:336px;width:760px;height:470px;border:1px solid #55575e;border-radius:12px;overflow:hidden">
<iframe src="{WIZARD_PAGE}" style="width:760px;height:470px;border:0;display:block"></iframe>
<span class="badge" style="left:604px;top:200px">2</span></div>
<div class="note">The guide is the real Spooler setup guide. Next unlocks once Test succeeds. The top bar is an illustration.</div>""")


def manual_install() -> str:
    paths = (("Windows", r"%APPDATA%\OrcaSlicer\orca_plugins\ "),
             ("macOS", "~/Library/Application Support/OrcaSlicer/orca_plugins/"),
             ("Linux", "~/.config/OrcaSlicer/orca_plugins/"))
    rows = "".join(
        f'<div style="display:flex;gap:20px;padding:6px 0"><span style="width:110px" class="muted">{os_}</span>'
        f'<span style="{MONO};font-size:22px">{path.strip()}</span></div>' for os_, path in paths)
    return page(f"""<div class="cap">Manual install<small>one Spooler file per folder</small></div>
<div class="win" style="bottom:auto;height:400px;top:100px">
<div class="title">orca_plugins</div>
<div style="padding:22px 30px 22px 30px;font-size:26px;{MONO}">
<div style="padding:6px 0">&#128193; orca_plugins</div>
<div class="hl" style="margin:8px 0 8px 76px;padding:2px 12px;width:max-content">&#128193; spooler
<span class="badge" style="left:-66px;top:-4px">1</span></div>
<div class="hl" style="margin:8px 0 0 116px;padding:2px 12px;width:max-content">&#128196; spooler_any.py
<span class="badge" style="left:-66px;top:-4px">2</span></div>
<div class="muted" style="margin:14px 0 0 116px;font-size:20px">the same file on Windows, macOS and Linux</div>
</div></div>
<div style="position:absolute;left:120px;right:120px;top:540px;font-size:24px">
<div style="font-weight:600;margin-bottom:10px">Plugin directory</div>{rows}</div>
<div class="note">Restart OrcaSlicer, then tick Activate for Spooler.</div>""")


SHOTS = {"01-plugin-hub": plugin_hub, "02-plugins-dialog": plugins_dialog, "03-permission": permission,
         "04-spooler-tab": spooler_tab, "05-manual-install": manual_install}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--chrome", help="path to Google Chrome or Chromium")
    chrome = find_chrome(parser.parse_args().chrome)
    OUT.mkdir(parents=True, exist_ok=True)
    sp, _ = load()
    spools_msg, live_msg = demo_state(sp)
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        (work / WIZARD_PAGE).write_text(plugin_page(sp, "settings", spools_msg, live_msg, wizard_step=1),
                                        encoding="utf-8")
        for stem, make in SHOTS.items():
            src, out = work / f"{stem}.html", OUT / f"{stem}.png"
            src.write_text(make(), encoding="utf-8")
            run = subprocess.run([chrome, "--headless=new", "--disable-gpu", "--hide-scrollbars",
                                  f"--user-data-dir={work / 'profile'}", "--no-first-run",
                                  "--force-device-scale-factor=1", "--allow-file-access-from-files", "--window-size=1600,900", "--virtual-time-budget=3000",
                                  f"--screenshot={out}", src.as_uri()],
                                 capture_output=True, text=True, timeout=90)
            if not out.exists() or "bytes written" not in run.stdout + run.stderr:
                sys.exit(f"Chrome could not render {out.name}:\n{run.stderr[-2000:]}")
            print("rendered", out.relative_to(ROOT))


if __name__ == "__main__":
    main()
