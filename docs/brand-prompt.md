# Brand asset prompt

Paste the prompt below into ChatGPT (a model with image generation). Ask for the assets one at a
time if it tries to cram everything into a single image; ask for SVG code for the mark, wordmark
and tab icon so they stay sharp.

Where each asset goes in this repo:

| Asset | File |
|---|---|
| Symbol / app icon | `assets/spooler-icon.svg`, `assets/spooler-icon.png` (also rendered to the 512 px Orca Cloud store image by the release workflow) |
| README banner | `assets/spooler-banner.svg`, `assets/spooler-banner.png` |
| Tab icon | the store tile at 40x40, `assets/spooler-plugin-icon.png`, embedded as `TAB_ICON_PNG` in `plugin/spooler/tab.py` |
| GitHub social preview | Repository Settings > Social preview |

---

```text
You are a senior brand designer. Create a complete, original brand identity for "Spooler",
an open-source plugin for OrcaSlicer (a 3D-printing slicer).

WHAT IT DOES
Spooler connects a self-hosted Spoolman filament inventory to OrcaSlicer. The user enters the
Spoolman address once; everything else is automatic. Every filament spool they own appears in
the slicer's filament dropdown already in its real colour, with the right temperatures and
printer-specific tuning, and the plugin reads which spool is loaded in each toolhead of their
printers (Snapmaker U1, Sovol SV06, Anycubic Kobra X, Bambu Lab). Core idea: "your real spools,
already in the slicer" - inventory and slicer in sync, zero manual setup.

AUDIENCE AND PERSONALITY
Hobbyist and prosumer 3D-printing makers who self-host tools. Personality: precise, calm,
helpful, a little playful, "it just works". Not corporate, not toy-like.

CONCEPT DIRECTION
Build the symbol around a filament spool seen from the front (hub + flange + wound filament),
combined with an idea of sync or flow - for example the filament strand leaving the spool and
curving into a loop or arrow, or concentric wound rings that suggest a sync cycle. Multicolour
filament is part of the story: the symbol may use 3-4 colour bands like differently coloured
spools, but must also work in one colour.

HARD CONSTRAINTS
- Fully original. Do not imitate or reference the logos, colours or icons of OrcaSlicer,
  Spoolman, Spoolio, Bambu Lab, Snapmaker, Sovol, Anycubic or any other brand.
- Flat vector style, no photorealism, no gradients that break when printed in one colour
  (subtle gradients allowed only on the full-colour app icon).
- The symbol must stay recognisable at 16x16 px and 20x20 px.
- Must look right on both dark (#14181F) and light (#FFFFFF) backgrounds.
- Text in images must be spelled exactly "Spooler". No other words unless asked.
- Fonts must be free and open (Google Fonts), name them.

DELIVERABLES (produce each as its own image, exact sizes, transparent background unless stated)
1. Brand sheet (1600x1000): symbol, wordmark, horizontal lockup, palette swatches with hex codes,
   typography sample, and a do/don't row. Dark background #14181F.
2. Symbol / app icon, full colour, 1024x1024, centred on a rounded-square tile (corner radius
   about 22%), tile colour from the palette. Also give it as clean SVG code (viewBox 0 0 256 256,
   no embedded raster, no external fonts).
3. Symbol, single colour white on transparent, 1024x1024, plus SVG code.
4. Tab icon for the slicer's top tab bar: monochrome white (#FFFFFF) line icon on transparent,
   designed on a 24x24 grid with 1.5 px strokes, round caps and joins, no fills thicker than the
   stroke, readable at 20 px. Give it as SVG code (width="24" height="24" viewBox="0 0 24 24",
   stroke="#FFFFFF", fill="none").
5. Horizontal lockup (symbol + "Spooler" wordmark) for the README header: 1200x320, background
   #14181F with rx 32 rounded corners, symbol on the left about 220 px tall, wordmark to its
   right, optional short tagline under it: "Your Spoolman spools, already in OrcaSlicer".
   Also as SVG code with the wordmark converted to paths.
6. GitHub social preview, 1280x640, dark background, lockup centred, tagline below, subtle
   pattern of concentric spool rings in the background at low contrast; keep a 40 px safe margin.
7. Plugin store tile, 512x512, the app icon with generous padding on a palette background.

PALETTE
Define 1 primary, 1 secondary, 2-3 filament accent colours (used for the coloured spool bands),
plus a dark neutral and a light neutral. Give hex codes and say what each is for. Check that
text-on-background pairs reach WCAG AA contrast.

OUTPUT FORMAT
For every deliverable: the image, then (where asked) the SVG code in a code block, then one line
on how it is meant to be used. Finish with a short brand guide: clear space (use the hub
diameter as the unit), minimum sizes, colour usage, and three things never to do with the logo.
```
