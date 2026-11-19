# Orca plugin family — visual system 5

One system for Kobra Control, U1 Control, Spooler, Print Calculator, Organizer and Embedder. Vue 3 + PrimeVue 5, one preset on `aura-compat`, one palette, one icon set, and shared components for the structures the six pages have in common. Each plugin keeps its own name and mark.

5.0 replaces the 4.x direction. 4.x gave every plugin a coloured page: a solid accent app bar, accent-tinted surfaces, coloured module header strips and a filled hero. Inside OrcaSlicer that read as a different application in every tab. 5.0 is OrcaSlicer's own interface, continued.

## Direction

A plugin page is a part of OrcaSlicer. It uses OrcaSlicer's greys for every surface, OrcaSlicer's teal for the primary action, and OrcaSlicer's button and field shapes. Squint at it next to the Prepare tab and it is the same program.

- The page, panels, app bar and module headers are neutral. Nothing is tinted by the plugin.
- The primary action, focus, selection and progress are OrcaSlicer's teal, in all six plugins.
- The plugin's own hue appears in two places: its mark tile in the app bar and the line under the open tab. Nowhere else.
- Colour is information, and only information: an icon's domain (heat, filament, motion), a state (chip, banner, toast), a level (green, amber, red), a heater's phase, a filament's own colour in its drawn spool and in the thin strip on its slot card, a toolhead's identity badge. If a colour does not answer "what is this" or "what state is it in", it is grey.
- Structure comes from layout, not colour: one page grammar (below), aligned 40 px module headers, a 12 px gap, hairlines, and the jump between a small label and its value.

Not allowed: tinted pages or panels, coloured header strips, a filled hero, solid coloured icon tiles, gradients, glass, glow, emoji, a helper paragraph under a module, a hue used with no meaning behind it.

## Colour

### OrcaSlicer reference

Read from the OrcaSlicer source (main at `7932cd2`, 2026-11-19): `src/slic3r/GUI/Widgets/StateColor.cpp` (the light to dark map every widget uses), `Button.cpp` (`btn_regular`, `btn_confirm`, `btn_alert`), `TextInput.cpp`, `ComboBox.cpp`, `SwitchButton.cpp`, and `resources/web/include/global.css` (the same roles as CSS variables for its own web views). The gallery screen `?screen=tokens` shows the two side by side.

| OrcaSlicer role | OrcaSlicer light / dark | Token | Token light / dark |
|---|---|---|---|
| Page behind panels (`--bg-color-alt`, side tab bar) | `#F0F0F0` / `#242428` | `background` | same |
| Window, panel, field (`--bg-color`) | `#FFFFFF` / `#2D2D31` | `surface` | same |
| Title bars, table heads (`--bg-color-secondary`) | `#F4F4F4` / `#36363B` | `raised` | same |
| Separator, switch track | `#EEEEEE` / `#27272A` | `inset` | same |
| Regular button (`btn_regular`) | `#DFDFDF` / `#3E3E45` | `control` | same |
| Regular button, hover | `#D4D4D4` / `#4D4D54` | `controlHover` | same |
| Border (`--border-color`) | `#DBDBDB` / `#4A4A51` | `border` | same |
| Text (`--fg-color-text`) | `#262E30` / `#EFEFF0` | `text` | same |
| Label, dimmed text | `#6B6B6B` / `#B2B3B5` | `muted` | **`#5C5F61`** / same |
| Icon grey, disabled text | `#7C8282` / `#818183` | `controlBorder` | same values, used as the field outline |
| Teal (`--main-color-fixed`) | `#009688` / `#009688` | `primaryMark` | same |
| Confirm button (`btn_confirm`) | `#009688` / `#00675B` | `primary` | **`#008172`** / same |
| Confirm button, hover | `#26A69A` / `#008172` | `primaryHover` | **`#00675B`** / same |
| Checked item | `#BFE1DE` / `#223C3C` | `primarySoft` | same |
| Teal text, links | `#009688` / `#5EEAD4` | `primaryText` | **`#00675B`** / same |
| Alert (`--button-bg-alert`) | `#E14747` / `#E14747` | `dangerSolid` | **`#C4281C`** / **`#DE3428`** |

Six values differ from OrcaSlicer, all for the same reason: the contrast check. White on `#009688` is 3.7:1 and `#009688` text on white is 3.7:1, so in light the confirm fill is OrcaSlicer's own darker teal `#008172` (4.8:1) and teal text is `#00675B` (6.8:1); `#009688` itself stays for everything that is a mark, not text. `#6B6B6B` labels fall under 4.5:1 on tints, so `muted` is one step darker. White on `#E14747` is 4.0:1, so the solid red keeps the 4.x reds. OrcaSlicer outlines its fields with the 1.5:1 hairline; ours use its icon grey, which is 3:1 on every surface. If the owner prefers the literal `#009688` confirm button in light, it is one value in `palette.json` and one waived pair in the check.

### Tokens

Colours live in `src/palette.json` (light and dark, 62 roles each) and reach the page as `--oui-<role>` through `applyOrcaTheme()`. `scripts/check.mjs` measures 131 foreground/background pairs per theme; text pairs are at least 4.5:1, control boundaries, the focus ring and other marks at least 3:1. Surfaces are the same for every plugin, so each pair is measured once (4.x measured 475, one set per accent). Add a role to both themes and to the check, or do not add it.

| Role | Use |
|---|---|
| `background` | the page |
| `surface` | panels, the app bar, dialogs, and the inside of fields |
| `raised` | things that sit on a panel: object cards, table headers, hovered rows, neutral chips, icon tiles, the file browser's rail |
| `inset` | things cut into a panel: wells, the track behind media and thumbnails |
| `control`, `controlHover` | the everyday button's fill; hovered list items |
| `border` | hairlines and tracks. Decorative: never the only sign of a control |
| `controlBorder` | field outlines and other boundaries that must be found (3:1) |
| `text`, `muted` | body text; secondary text and labels (both 4.5:1 on all four surfaces and on every tint) |
| `primary`, `primaryHover`, `onPrimary` | the solid teal of the one primary action and of the chosen option in a toggle group |
| `primaryMark` | teal that is not text: focus ring, checked box and switch, progress, the frame of the selected card, the mark on the open section |
| `primarySoft` | the selected row or option |
| `primaryText` | teal text: links, a text button that is the primary action |
| `accent`, `accentSoft`, `onAccent`, `accentSolid`, `onSolid` | the plugin's identity hue. Written by `applyOrcaTheme()` from the hue chosen in `installOrcaUI()`. `accentSolid` with `onSolid` is the mark tile (the same in both themes); `accent` is the line under the open tab |
| `teal`, `sky`, `cobalt`, `violet`, `magenta`, `lime`, `orange` | the seven hues, for icons and chips. Each has `…Soft` (its tint), `on…` (text on the solid hue) and `…Solid` (its fill under white) |
| `danger`, `warning`, `success`, `info` + `…Bg` | state text and marks, and their tints |
| `dangerSolid`, `dangerSolidHover`, `onDangerSolid` | the one solid red: confirming a destructive action, emergency stop |
| `tool1`…`tool4`, `onTool` | toolhead identity (T1 coral, T2 amber, T3 violet, T4 teal). Fixed in both themes; always carries its label |

Filament colour is data, not a token: it appears only in `OuiSpool`, `OuiSwatch` and the 4 px strip across the top of an `OuiSlot` card, each of which rings it so black, white and clear stay visible. The 40 px colour sample of 4.x is that strip now: enough to match a card to a spool at a glance, not enough to colour the page.

Removed in 5.0: the per-accent surface sets (`violetBackground`, `violetSurface`, …), `band`, `onBand`, `band<State>`, `<hue>Hover`, `<hue>Band` (now `<hue>Solid`), and the classes `.oui-on-band` and the filled `.oui-hero`.

### Where colour is allowed

| Colour | Where | How |
|---|---|---|
| Plugin hue | the mark tile; the 2 px line under the open app-bar tab | `OuiAppBar` does both. `tone="accent"` exists for one more highlight per plugin, if it earns it |
| OrcaSlicer teal | the primary button; focus; checked, selected, progress | the preset |
| Domain hue | the 16 px icon in a module header; the icon in a control row | `tone` on `OuiPanel`, `OuiControlRow`, `OuiIcon` |
| State | `OuiStatus` chips, warning, error and success banners, toasts, level bars (green, amber when low, red when almost empty), a figure that is incomplete | the state tokens |
| Heat | a heater's reading and its small chart: orange heating, green at target, blue cooling. Off is grey | `OuiSetpoint` |
| Filament | the drawn spool, the swatch, the 4 px strip on a slot card | `OuiSpool`, `OuiSwatch`, `OuiSlot` |
| Toolhead | the T1…T4 badge | `.oui-slot-badge[data-tool]` |

Plugin hues: Kobra Control `violet`, U1 Control `cobalt`, Spooler `magenta`, Print Calculator `lime`, Organizer `sky`, Embedder `teal`.

Domain hues, the same in every plugin: `orange` heat (nozzle, bed, drying) · `cobalt` motion and mechanics · `sky` camera, air, humidity · `magenta` filament (spools, slots, toolheads) · `lime` stock, money, light · `teal` trust (certificate, licence). Anything else is grey: no `tone`, or `neutral`.

Changed from 4.x: an information banner is grey with a blue mark (it is not an alarm); a material chip is grey (`materialTone()` returns `neutral`); an icon tile is a grey square with a toned icon; a state chip is tinted, not solid.

## Type, space, shape

In `src/base.css`:

- Type: Manrope, embedded (see below), with the system UI font as fallback; mono only for paths, addresses and identifiers. Scale 11 label (600, caps, tracked) · 12 meta · 13 body and controls · 15 object name and page title (700) · 20 / 28 / 40 readouts (700, tabular, tight).
- Space: 4 px grid, `--oui-s1`…`--oui-s8` (4, 8, 12, 16, 20, 24, 32). 12 between modules and inside them; a module's title, body and footer all start on the same 12 px.
- Radius, OrcaSlicer's: 3 chips · 4 controls and object cards · 6 panels · 8 dialogs.
- Size: controls 32 px, small 26 px (in tables, cards, toolbars and module headers). Module header 40 px. App bar 44 px.
- Elevation: surfaces step by grey (inset, page, panel, raised). Panels have a hairline, plus a 1 px shadow in light. Only overlays cast a real shadow.
- Motion: 120 ms for colour, 180 ms for disclosure, linear width for progress. Loops (connecting, busy halo, indeterminate bar, loading pulse) stop under `prefers-reduced-motion`.
- Data marks: a level is a 6 px bar (green, amber when low, red when almost empty); a job is an 8 px teal bar; a series is a 28 px `OuiSpark`. The number is always in text beside the mark.

The typeface is Manrope (SIL Open Font License 1.1, `licenses/Manrope.txt`; the face in Embedder's brand kit), embedded in `base.css` from `src/fonts/Manrope.woff2`: a subset with Basic Latin, Latin-1 (all of English and pt-BR), dashes, quotes, bullet, ellipsis, euro, the four arrows, minus, ≤ ≥ ≠ and ×, as one variable file for weights 400 to 700, with tabular figures. 21,476 B on disk, about 28.7 kB once inlined in a page. Every page policy must allow `font-src data:`; under a policy that does not, the browser reports a violation and the page falls back to the system font, which the layout is also tested with. The subset is rebuilt with fonttools (the command is in README.md); it is not part of `npm run build`.

Theme-dependent CSS that you write uses the `--oui-*` variables, or `.orca-dark` for anything else, never `light-dark()`: the build target rewrites `light-dark()` in authored CSS into a form that follows only a `color-scheme` declared in CSS, and the host theme is applied from script. The preset itself reads the `--oui-*` variables, so `applyOrcaTheme()` must run before the app mounts (it always did).

## Icons

One set, one grid: 24 px, 2 px stroke, round caps and joins, no fills. `src/icons.ts` is generated by `scripts/icons.mjs`: 86 icons copied from Lucide (ISC, `licenses/Lucide.txt`) and 11 drawn for the family on the same grid, because no set has them: `spool`, `spoolman`, `nozzle`, `toolhead`, `bed`, `ace`, `slot`, `insert`, `plate`, `arrange`, `printer`. Each icon is its own export, so a page bundles only the ones it imports (about 0.2 kB each); consumers need no icon package. To add one, add its name to `scripts/icons.mjs` and rebuild. Replace the plugins' own mixed icon files with this set; a plugin keeps only its identity mark.

```ts
import { thermometer, spool } from '../shared/src/icons';
// <OuiIcon :icon="thermometer" tone="orange" />   <OuiPanel :icon="spool" tone="magenta" … />
```

| Treatment | How | Where |
|---|---|---|
| Mono | `<OuiIcon :icon>` | inside buttons and tabs, table cells, inline with text. Takes the text colour |
| Toned | `tone="orange"` | a mark that carries its domain without a box: every module header, a reading in a line of text |
| Tile | `tile` (+ `tone`) | the icon, in its tone, in a neutral rounded square: readouts, control and setting rows, list objects, empty states. The square is always grey; only the mark has a colour |

Sizes: 14 in controls, tabs and small tiles; 16 default; 20–22 in large tiles and empty states. A tile is the icon plus 6 px each side, radius 6.

Where icons go: every app-bar tab, every module and settings section header (toned, no tile), every readout that is not a plain row of three, every state (`OuiStatus` has them built in), every empty state, the primary action and any action with a consequence (stop, cancel, archive, emergency, save, link, refresh). Not on every button in a row of five, and not in table column headers: there the icon belongs in the cell, on the thing (the spool, the material chip, the location pin).

## Imagery

Three kinds, in this order of preference:

1. Drawn objects that take data. `OuiSpool` is the spool: a product render of the reel whose winding is tinted to the filament colour and is as deep as the filament left. The printer drawings in the gallery (`gallery/art/`) show the Kobra with its four-spool box and the U1 with four toolheads; the spools and heads take the real colours and the print grows with the job. They are vector, follow the theme through the palette, contain no text and cost under 2 kB each. A plugin's own drawings live in that plugin.
2. Icon tiles, for empty states and section identity.
3. One raster illustration per plugin for its empty or first-run state (`OuiEmpty image`), and listing or README art. Nowhere else in a page: the pages are single files with a size budget, and a picture cannot follow the theme or the language. The six that exist are in `assets/illustrations/` (320 px WebP with transparency, 2.4 to 18.2 kB each, 43.6 kB together); they use white, two greys and a mid tone of the plugin's accent, and sit on the neutral page in both themes.

Style for anything drawn or generated for the family, so it stays one hand: flat shapes on the palette's neutrals with one accent hue; 1.5 px outlines in `controlBorder`; rounded corners in the 2–7 px range; straight-on or simple isometric view; no gradients, no shadows, no texture, no perspective tricks; generic geometry, never a real product's shape or logo; no text or digits in the image.

Prompt to reuse when an image is generated (replace the bracketed part only): "Flat vector-style illustration of [subject], straight-on view, simple geometric shapes, 1.5 px dark-grey outlines, solid fills in dark graphite and mid grey with one [accent hue] highlight, rounded corners, no gradients, no shadows, no texture, no text, no letters, no logos, no brand names, transparent background, centred with generous margin, 1024 × 1024."

Every generated or raster asset is recorded in `assets/manifest.json` (file, source, tool, exact prompt, date, bytes, review note, where it is used) and looked at at full size before it is kept. The assets are not part of the shared snapshot: a plugin copies the one illustration it uses. The Organizer and Spooler marks are generated proposals redrawn by hand as vector; marks are always vector.

## Actions

OrcaSlicer's three buttons, plus the quiet one:

| Rank | PrimeVue | Looks like | Use |
|---|---|---|---|
| Primary | `<Button>` | OrcaSlicer's confirm button: solid teal | the one thing the view is for; at most one per view (Print, Save, Add spool) |
| Everyday | `severity="secondary"` | OrcaSlicer's regular button: grey fill, text colour | the default for everything else |
| Quiet | `severity="secondary" text` | label only | repeated per row or card, and less likely actions |
| Destructive | `severity="danger" outlined` | red outline | stop or cancel a print, delete, archive. Always confirmed with `OuiConfirm`, whose confirm button is the solid red |
| Emergency | solid `severity="danger"` in the app bar's action slot | solid red | always reachable, never inside a panel. The only solid red on a page that has no dialog open |

One button per choice: where two actions are each other's opposite and only one applies (Pause and Resume), show the one that applies, not both with one disabled. Icon-only buttons carry an `aria-label`. A redesign never removes a confirmation.

## States

`OuiStatus` is the only way to show a state: a chip tinted in the state's colour with a mark and a word (or `variant="plain"`, coloured text, inside a sentence). Nine states, each with its own mark so it reads without colour:

`ok` dot · `busy` dot with halo · `connecting` turning arc · `pending` clock, info · `stale` clock, warning · `warn` triangle · `error` crossed circle · `offline` crossed signal · `idle` ring.

Rules (unchanged from 4.x, restated):

1. One page, one connection state. It is in the app bar, on the right; nothing else on the page may contradict it.
2. A reason is said once. If the page is offline, busy or incomplete, one `OuiBanner` under the page header says why and offers the way out; disabled controls point at it with `aria-describedby` and say nothing themselves. Every banner can be closed, is bound to its condition and never timed. News about something that just happened is a toast.
3. Stale data shows its source and age and loses its colour (`OuiJob stale`, `OuiSetpoint stale`, `OuiReadout stale`).
4. An uncertain outcome is `pending` or `warn`, never `ok`, until the printer or Spoolman confirms it.
5. Unknown is a dash or the word "unknown", never 0, and never an empty cell.
6. What a module needs explained is behind its (i) (`OuiPanel hint`, `OuiHint`), never a paragraph under it. More than two sentences: link to the documentation from inside the hint ("Learn more").

## Page grammar

Every main page, in every plugin, is the same four things in the same order:

1. **App bar** (`OuiAppBar`, 44 px, neutral, sticky): mark tile, name, tabs; then on the right the page's one state and the page-wide actions (emergency stop).
2. **Page header** (`OuiPageHeader`, one line): what this page shows (the printer's name, "Stock", "Files", "Spools"), one line of facts about it (address and firmware; count, source and age), and the page's own actions on the right, at most one primary. An explanation of the page is an `OuiHint` here.
3. **Banner**, only when there is a reason to give (States, rule 2).
4. **Content**, in one of three layouts, all children of `.oui-page`:
   - `.oui-dash` (dashboards): a full-width block on top, then a main column (two thirds) and a side column. One column under 1000 px.
   - `.oui-split` (a list with a rail and/or a detail): `data-rail` adds a 260 px column on the left, `data-detail` a 320 px one on the right; they stack under 900 px.
   - `OuiSettings` (settings).

A module is always an `OuiPanel`: a 40 px header (toned icon, title, one line of meta, an (i) when it needs one, actions at the right in small controls), a 12 px body (or `flush` for tables and media), an optional footer. Modules never nest.

### The dashboard standard (Kobra Control, U1 Control)

```
App bar        mark · name · Dashboard | Stock | Files | (Console) | Settings          state · emergency stop
Page header    Printer name   address · firmware                                        page actions
Banner         (the one reason, when busy / offline)
.oui-dash-top  Status block: picture 72 · state, file, layer · 77 % ▬▬▬▬ · elapsed, left, finishes · Pause, Cancel
.oui-dash-main                                              .oui-dash-side
  Filament module (toolheads / ACE slots: 4, 2 or 1 across)   Camera module (16:9)
  Controls module (Temperature | Machine)                      Move module (Kobra)
                                                               Printer module (facts, print assist)
```

The main column is what you work on, the side column what you watch. The order under 1000 px is the reading order above.

- **Status block** (`OuiJob` in a header-less `OuiPanel`, `.oui-dash-top`): one row from 1100 px, two from 640, stacked below. The picture (`#thumb`: the model's thumbnail when the printer gives one, else the printer drawing) is a fixed 72 px box; in 4.x it was the tallest thing on the page. State chip, file name on up to two lines, one line of detail; the percentage at 28 px beside an 8 px teal bar; elapsed, left and finish time as small readouts; the job's actions. The whole block is about 96 px high at full width.
- **Filament module**: `OuiSlot` cards in `.oui-cards` (4, 2 or 1 across, never 3 + 1). A slot card is neutral: a 4 px strip of the filament's colour across the top, identity badge and state chip on the first line, the drawn spool with name and material, the amount with its level, then the slot's own controls and actions. The spool chooser in the card is how a slot is linked without leaving the dashboard; the full stock is its own tab.
- **Controls module**: one `OuiPanel` holding `.oui-controls` with one `.oui-controls-group` per task (Temperature, Machine). Groups sit side by side when the module is wide enough, and stack when not. In a group: an 11 px label, then rows separated by hairlines. A heater is an `OuiSetpoint` (icon, reading in its phase colour, target, small chart, input, Set, Off); anything else is an `OuiControlRow` (icon, label, what it reads now, the control). Both use the same columns and a 44 px row, so everything lines up.
- **Camera module**: `OuiPanel flush` with the rate, snapshot and on/off as small controls in its header, and `OuiCamera` as its body: a 16:9 box that keeps its size whether the camera is live, off, starting or failed, so turning it on does not move the page. The rate and "Live" are chips over the picture. What the rate means is the header's (i).
- **Empty and loading**: a module that cannot show anything is one row (`OuiEmpty compact`, with `state="offline"`, `"error"` or `"empty"`), never a reserved hole and never hidden: the page keeps its shape. While the first read is under way, each module shows `.oui-skeleton` bars the size of its content. A page with nothing to show at all (no printer chosen) is one `OuiPanel` with `OuiEmpty` and its illustration and the way out.

### Stock tab (Kobra Control, U1 Control)

Stock is no longer on the dashboard. It is the second tab, with the spool count on it.

```
Page header    Stock   57 spools · Spoolman through the printer · read 11 s ago        (i) · Open Spooler · Refresh
.oui-split data-rail
  Rail: "Link to" — a radio list of the places a spool can go      List: toolbar (search, material, "same material as T1", count)
        (T1…T4, or ACE slots), each with its badge, the spool            table: spool · material · loaded in · left · [Link to T1]
        that is in it and what is left
```

Choose the place once, on the left; every row then has one action, named with that place ("Link to T1"). A spool already in the chosen place shows `Linked` instead. The explanations that sat under the 4.x stock module (how Spoolman is reached, who records use, why there are two tabs) are the page header's (i), with the link.

### Files tab (Kobra Control, U1 Control): `OuiFileBrowser`

One surface, three panes: the folder tree, the open folder as a table, and what is selected.

- **Tree** (`role="tree"`): folders with counts; the open one has the teal mark. Arrows move, Right and Left open and close, Enter opens the folder.
- **Table** (`role="grid"`, multi-selectable): checkbox, thumbnail and name with a kind chip, size, changed. Sort by any column.
- **Selecting**: click selects one; Cmd/Ctrl-click and the checkbox add or remove one; Shift-click and Shift with the arrows select a range; the header checkbox (with its indeterminate state) and Cmd/Ctrl+A select all; Escape clears. Space toggles, Enter opens, Delete asks to delete.
- **The bar over the table** is always there, so selecting does not move anything: the file count, or "3 selected" with Clear, "Move to…" and Delete.
- **Moving**: drag the selection onto a folder in the tree (folders that can take it are outlined while dragging, the one under the pointer is filled), or choose the folder in "Move to…", which is the same action from the keyboard.
- **Deleting** always asks first (`OuiConfirm`), with the count and the first four names.
- **Detail**: one file selected shows its picture, name, facts and the page's actions for it (Print is the page's primary); several show the count and their names; none says so in one line.
- Under 980 px the detail goes under the table; under 620 px the tree goes above it.

The page owns the data: it passes the folders, the open folder's files and the labels (both languages), and does the work on `move`, `delete` and `open`. `readonly` turns moving and deleting off while the printer is busy.

### Lists elsewhere

- Spooler (tabs Spools, Printer, Stats, Settings): the Spools page is `.oui-split data-detail`: spool cards (the drawn spool at 64 px, name, maker, amount with its level, where it is loaded) in a grid that fills the width, and the selected spool on the right. The cards are neutral; the spools are the colour on the page. The same list as a table (the Stock tab's) is the dense view.
- Tables: `DataTable size="small"`, name and one meta line in the first column, numbers right-aligned with `oui-num`, the row action last. The first cell holds an `OuiSpool` or an `OuiThumb`.
- Settings: `OuiSettings`, one `OuiFormSection` per section. The open section is marked with a grey fill and the teal mark.
- The dock shows one thing at a time (form, running job, or result); `OuiJob compact` is the status block at dock size.
- Lay pages out with `@container oui-page (min-width: …)`, not media queries: the same page runs in a 280 px dock and a 1900 px tab.

## Components

Import each from `shared/src/components` (or its own `.vue` file).

| Component | What it is |
|---|---|
| `OuiAppBar` | the neutral bar: mark on a tile in the plugin's hue, name, tabs (`data-tab`, arrow keys; the open one has a 2 px line in the plugin's hue; `count`, `attention`), then the page's state and actions on the right. Sticky; tabs drop to a second line when narrow |
| `OuiPageHeader` | **new.** Title, one line of meta, page actions |
| `OuiBanner` | a page-level state with its action: `info` (grey), `warn`, `error`, `success`, `neutral`; `dismissible` with a `dismissKey` |
| `OuiPanel` | a module: 40 px neutral header with a toned icon, title, meta, `hint`, actions; body; optional footer. `flush`, `fill` |
| `OuiHint` | **new.** The (i): opens on hover and focus, closes on Escape, and is the button's description for a screen reader |
| `OuiStatus` | a state, as a tinted chip (default) or `plain` coloured text |
| `OuiJob` | the compact status block: picture, state, name, percentage or count, bar, stats, actions. `compact` for the dock; `stale` is grey. `hero` is accepted and ignored |
| `OuiSetpoint` | a controlled value: reading in its phase colour, target, chart, input, Set, Off |
| `OuiControlRow` | **new.** A line of a controls module: icon, label, current value, control. With `.oui-controls` and `.oui-controls-group` |
| `OuiCamera` | **new.** The 16:9 picture box with its live, off, loading and error states |
| `OuiSlot` | a toolhead or slot as a neutral card: a 4 px strip of the filament's colour, badge and state, drawn spool, filament, amount with its level, extra rows, actions; `active` |
| `OuiFileBrowser` | **new.** The Files tab (above) |
| `OuiSpool`, `OuiSwatch`, `OuiLevel` | unchanged |
| `OuiReadout`, `OuiSpark`, `OuiThumb`, `OuiKeyValue`, `OuiToolbar`, `OuiEmpty`, `OuiToastHost`, `OuiRequirement`, `OuiSettings`, `OuiFormSection`, `OuiFormRow`, `OuiConfirm`, `OuiIcon` | as in 4.x, neutral |

Classes: `.oui-page`, `.oui-dash` (`-top`, `-main`, `-side`, `-pair`), `.oui-split`, `.oui-controls`, `.oui-cards`, `.oui-skeleton`, `.oui-slot-badge`, `.oui-hero` (a neutral block for the one value a page is about), `.oui-stack`, `.oui-row`, `.oui-spacer`, `.oui-field`, `.oui-chip`, `.oui-label`, `.oui-meta`, `.oui-num`, `.oui-mono`, `.oui-truncate`, `.oui-well`, `.oui-divider`, `.oui-sr`.

Use PrimeVue directly for controls (Button, InputText, InputNumber, Select, Checkbox, ToggleSwitch, SelectButton, Dialog, DataTable, ProgressBar). Do not wrap them, and do not restyle them locally: change the preset.

## Do and do not

- Do squint at the page as a thumbnail beside an OrcaSlicer tab: it should read as OrcaSlicer, grey with teal, and the coloured things on it should be exactly the things that are telling you something.
- Do give every view one primary action, or none.
- Do put the number first: 77 %, 221.0 °C, 891 g. The label is 11 px above it.
- Do group by task, and label the group. A module answers one question.
- Do give the same thing the same icon and hue everywhere. Heat is orange with a thermometer, nozzle or bed in all six plugins.
- Do not put a sentence under a module or a control. If it is a reason, it is the banner; if it is an explanation, it is the (i).
- Do not use the plugin's hue for anything but its mark and the open tab.
- Do not stretch controls to fill a row.
- Do not add a palette, a font or a component style in a plugin. If the family needs it, it goes here and ships as one release.
- Do not remove a control, a confirmation or the explanation of a disabled action to make a screen cleaner.

## Acceptance

Compare real built pages across all six plugins, dark and light, at 1900×1000, 1280×720 and narrow (720; 280×360 for the Organizer dock), at 200 % zoom, in English and pt-BR, in every state the page has: connecting, offline, busy, empty, loading, error, stale, pending, incomplete. Check computed fonts, radii and colours, not only imports. `scripts/shots.mjs` does this for the reference screens (MOCK data), and drives `OuiFileBrowser` through its selection, keyboard, drag and delete paths. OrcaSlicer's own web views (WKWebView, WebView2) and real devices remain to be checked by the owner; drag and drop inside OrcaSlicer's web view in particular has only been run in headless Chrome.
