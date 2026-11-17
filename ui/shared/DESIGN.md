# Orca plugin family — visual system 4

One system for Kobra Control, U1 Control, Spooler, Print Calculator, Organizer and Embedder. Vue 3 + PrimeVue 5, one preset on `aura-compat`, one palette, one icon set, and a small set of shared components for the structures the six pages really have in common. Each plugin keeps its own name, mark, accent colour and domain layout.

## Direction

A bench instrument with a product's finish, in colour. Colour is structure here, not decoration:

- Each plugin owns a hue. Its app bar is a solid band of it, and its page, panels, raised parts and wells are all tinted by it, at four clearly different levels. Six tabs, six colours, recognisable at thumbnail size.
- Each module's header is a strip in the hue of its subject (heat orange, motion cobalt, filament magenta, stock lime, camera sky) with a solid icon tile.
- Each page has one hero: a block filled with the accent that holds the thing the page is for (the print with its percentage, the price, the selected spool, the plan), in white type.
- Physical things show their own colour at size: a slot or toolhead card opens with a sample of its filament, a spool is drawn wound in it.
- State is a solid chip with a mark and a word. Readings take the colour of what they are doing (heating, at target, cold).

Inside a module the value is large and its label small; density is high where the work is and nowhere else.

The discipline that keeps this professional: every colour is a role from the palette and every pairing it can form is measured (`scripts/check.mjs`); colour is never the only carrier of a meaning (there is always an icon, a mark or a word); filament and toolhead colours always sit in a neutral frame and never double as interface colour; stale or incomplete values lose their colour.

Not allowed, because they make the pages read as a template or a toy: gradients, glass, glow, emoji, coloured side stripes, more than one hero per page, a helper sentence under every control, and a hue used with no meaning behind it.

## Tokens

Colours live in `src/palette.json` (light and dark) and reach the page as `--oui-<role>` through `applyOrcaTheme()`. `scripts/check.mjs` measures 475 foreground/background pairs per theme (everything on each accent's four surfaces); text pairs are at least 4.5:1, control boundaries and solid fills at least 3:1. Add a role to both themes and to the check, or do not add it.

| Role | Use |
|---|---|
| `background` | the page, tinted by the accent |
| `surface` | panels and dialogs (white in light, a deep tint in dark) |
| `raised` | things that sit on a panel: object cards, table headers, hovered rows, neutral chips |
| `inset` | things cut into a panel: fields, wells, tracks behind media |
| `border` | hairlines and tracks. Decorative: never the only sign of a control |
| `controlBorder` | field outlines and other boundaries that must be found (3:1) |
| `text`, `muted` | body text; secondary text and labels (both 4.5:1 on all four surfaces of every accent) |
| `band`, `onBand` | the solid accent block of the app bar and the hero, and the white on it. The same in both themes. `bandSuccess`, `bandWarning`, `bandDanger`, `bandInfo`, `bandMuted` colour the white state pills that sit on a band |
| `onState` | text and marks on a solid state chip or tile |
| `teal`, `sky`, `cobalt`, `violet`, `magenta`, `lime`, `orange` | the seven hues. Each has `…Soft` (its tint, behind its own colour or behind text), `…Hover` and `on…` (text on the solid hue) |
| `primary`, `primaryHover`, `onPrimary`, `primarySoft`, and the six surface roles above | not stored under these names: the file holds them per hue (`violetBackground`, `violetSurface`, …) and `applyOrcaTheme()` writes the plugin accent's set. The primary action, selection, progress, links |
| `danger`, `warning`, `success`, `info` + `…Bg` | state text and marks, and their tinted fills |
| `dangerSolid`, `dangerSolidHover`, `onDangerSolid` | the one solid red: confirming a destructive action, emergency stop. The same saturated red in both themes |
| `tool1`…`tool4`, `onTool` | toolhead identity (T1 coral, T2 amber, T3 violet, T4 teal). Fixed in both themes; always carries its label |

Filament colour is data, not a token: it appears only in `OuiSpool`, `OuiSwatch` and drawings of spools, which ring it so black, white and clear stay visible. It is always a round shape; UI colour is never a plain round dot next to one.

### Accent: one per plugin

`installOrcaUI(app, locale, accent)` (or `setOrcaAccent`) picks the hue that becomes `primary` for that page. It fills the app bar, tints every surface and fills the hero, so a tab is recognised before it is read. Money is not a separate colour role: the Calculator's accent is the colour of value, and its one hero price is drawn in it, which keeps amber for warnings only.

| Plugin | Accent |
|---|---|
| Kobra Control | `violet` |
| U1 Control | `cobalt` |
| Spooler | `magenta` |
| Print Calculator | `lime` |
| Organizer | `sky` |
| Embedder | `teal` (its brand kit) |

`orange` is not an accent: it is heat.

### Hue by domain

A section's icon tile, its readouts and its chart take the hue of what the section is about, the same in every plugin. Put `tone="…"` on `OuiPanel`, `OuiReadout`, `OuiSetpoint`, `OuiIcon`, `OuiSpark`, `OuiEmpty`, or `data-tone` on a chip.

| Tone | Means |
|---|---|
| `accent` | the job and the plugin's own subject: the print, the quote, the pockets |
| `orange` | heat: nozzle, bed, drying, energy |
| `cobalt` | motion and mechanics: move, speed, plates, shipping |
| `sky` | camera, air and light sensors: camera, fan, humidity, labour time |
| `magenta` | filament: spools, slots, toolhead loading, Spoolman |
| `lime` | stock and money: inventory, price, profit |
| `teal` | trust: certificate, licence, verified |
| `violet` | extras and accessories |
| `neutral` | interface and about |
| `success`, `info`, `warn`, `danger` | states only. Never a section colour |

Material chips use `materialTone()`: PLA teal, PETG cobalt, ABS orange, ASA violet, TPU magenta, nylon and PC sky, anything else neutral. A chip is a labelled rectangle, so it cannot be mistaken for a filament swatch. Toolhead badges keep `tool1`…`tool4`.

Where a plugin's accent is also a domain hue (Spooler and filament, the Calculator and money), that is the point: the plugin is about that thing.

Everything else is in `src/base.css`:

- Type: Manrope, embedded (see below), with the system UI font as fallback; mono only for paths, addresses and identifiers. Scale 11 label (600, caps, tracked) · 12 meta · 13 body and controls · 15 object name and page title (650) · 20 / 28 / 40 readouts (600, tabular, tight). Hierarchy comes from the jump between label and value, not from more weights.
- Space: 4 px grid, `--oui-s1`…`--oui-s8` (4, 8, 12, 16, 20, 24, 32). 12 between panels, 16 inside them.
- Radius: 4 chips and badges · 6 controls and object cards · 8 panels · 12 dialogs.
- Size: controls 32 px, small 26 px (in tables, cards and toolbars).
- Elevation: surfaces step by tint (inset, page, panel, raised). Panels have a hairline, plus a soft shadow in light. The app bar and overlays cast a shadow.
- Motion: 120 ms for colour, 180 ms for disclosure, linear width for progress. Three loops exist (connecting, busy halo, indeterminate bar); all stop under `prefers-reduced-motion`.
- Data marks: a level is a 6 px bar (green, amber when low, red when almost empty); a job is an 8 px bar in the accent, 12 px and white in the hero; a series is a 28 px `OuiSpark` (filled line with a dashed target, or bars with the latest one solid); a composition is one 10 px segmented bar with a legend of squares. The number is always in text beside the mark.

The typeface is Manrope (SIL Open Font License 1.1, `licenses/Manrope.txt`; the face in Embedder's brand kit), embedded in `base.css` from `src/fonts/Manrope.woff2`: a subset with Basic Latin, Latin-1 (all of English and pt-BR), dashes, quotes, bullet, ellipsis, euro, the four arrows, minus, ≤ ≥ ≠ and ×, as one variable file for weights 400 to 700, with tabular figures. 21,476 B on disk, about 28.7 kB once inlined in a page. Every page policy must allow `font-src data:`; under a policy that does not, the browser reports a violation and the page falls back to the system font, which the layout is also tested with. The subset is rebuilt with fonttools (the command is in README.md); it is not part of `npm run build`.

Theme-dependent CSS that you write uses the `--oui-*` variables, or `.orca-dark` for anything else, never `light-dark()`: the build target rewrites `light-dark()` in authored CSS into a form that follows only a `color-scheme` declared in CSS, and the host theme is applied from script. The preset itself reads the `--oui-*` variables, so `applyOrcaTheme()` must run before the app mounts (it always did). A value derived from `--oui-primary` is resolved once at the root: to show another accent inside a page, restyle that element, do not expect PrimeVue's own variables to follow.

## Icons

One set, one grid: 24 px, 2 px stroke, round caps and joins, no fills. `src/icons.ts` is generated by `scripts/icons.mjs`: 86 icons copied from Lucide (ISC, `licenses/Lucide.txt`) and 11 drawn for the family on the same grid, because no set has them: `spool`, `spoolman`, `nozzle`, `toolhead`, `bed`, `ace`, `slot`, `insert`, `plate`, `arrange`, `printer`. Each icon is its own export, so a page bundles only the ones it imports (about 0.2 kB each); consumers need no icon package. To add one, add its name to `scripts/icons.mjs` and rebuild. Replace the plugins' own mixed icon files with this set; a plugin keeps only its identity mark.

```ts
import { thermometer, spool } from '../shared/src/icons';
// <OuiIcon :icon="thermometer" />   <OuiPanel :icon="spool" tone="magenta" … />
```

| Treatment | How | Where |
|---|---|---|
| Mono | `<OuiIcon :icon>` | inside buttons and tabs, table cells, inline with text. Takes the text colour |
| Toned | `tone="orange"` | a small mark that should carry its domain without a box: a reading in a line of text |
| Tile | `tile` (+ `tone`) | the icon in a solid rounded square of its tone, in the on-colour: every panel header, readouts, setting rows, list objects, banners, empty states. `soft` gives the tinted version |

Sizes: 14 in controls, tabs and small tiles; 16 default; 20–22 in large tiles and empty states. A tile is the icon plus 6 px each side, radius 6.

Where icons go: every app-bar tab, every panel and settings section header (as a tile), every readout that is not a plain row of three, every state (`OuiStatus` has them built in), every empty state, the primary action and any action with a consequence (stop, cancel, archive, emergency, save, link, refresh). Not on every button in a row of five, and not in table column headers: there the icon belongs in the cell, on the thing (the spool, the material chip, the location pin).

## Imagery

Three kinds, in this order of preference:

1. Drawn objects that take data. `OuiSpool` is the spool: a product render of the reel whose winding is tinted to the filament colour and is as deep as the filament left. The printer drawings in the gallery (`gallery/art/`) show the Kobra with its four-spool box and the U1 with four toolheads; the spools and heads take the real colours and the print grows with the job. They are vector, follow the theme through the palette, contain no text and cost under 2 kB each. A plugin's own drawings live in that plugin.
2. Icon tiles, for empty states and section identity.
3. One raster illustration per plugin for its empty or first-run state (`OuiEmpty image`), and listing or README art. Nowhere else in a page: the pages are single files with a size budget, and a picture cannot follow the theme or the language. The six that exist are in `assets/illustrations/` (320 px WebP with transparency, 2.4 to 18.2 kB each, 43.6 kB together); they use white, two greys and a mid tone of the plugin's accent chosen to hold on both its dark and its light page.

Style for anything drawn or generated for the family, so it stays one hand: flat shapes on the palette's neutrals with one accent hue; 1.5 px outlines in `controlBorder`; rounded corners in the 2–7 px range; straight-on or simple isometric view; no gradients, no shadows, no texture, no perspective tricks; generic geometry, never a real product's shape or logo; no text or digits in the image.

Prompt to reuse when an image is generated (replace the bracketed part only): "Flat vector-style illustration of [subject], straight-on view, simple geometric shapes, 1.5 px dark-grey outlines, solid fills in dark graphite and mid grey with one [accent hue] highlight, rounded corners, no gradients, no shadows, no texture, no text, no letters, no logos, no brand names, transparent background, centred with generous margin, 1024 × 1024."

Every generated or raster asset is recorded in `assets/manifest.json` (file, source, tool, exact prompt, date, bytes, review note, where it is used) and looked at at full size before it is kept. The assets are not part of the shared snapshot: a plugin copies the one illustration it uses. The Organizer and Spooler marks are generated proposals redrawn by hand as vector; marks are always vector.

## Actions

| Rank | PrimeVue | Use |
|---|---|---|
| Primary | `<Button>` | solid accent. The one thing the view is for; at most one per view (Apply, Save, Arrange) |
| Everyday | `severity="secondary"` | tinted with the accent, accent label. The default for everything else |
| Quiet | `severity="secondary" text` | accent label only: repeated per row or card, and less likely actions |
| Destructive | `severity="danger"` | solid red: stop or cancel a print, delete. Always confirmed with `OuiConfirm`. A reversible removal (archive) is `outlined` |
| Emergency | solid `severity="danger"` in the app bar's action slot (it gets a white ring on the band) | always reachable, never inside a panel |

On a band only the app bar's own actions are allowed (secondary, quiet and the emergency button); a hero block holds no buttons, its actions sit under it.

Icon-only buttons carry an `aria-label`. A destructive or irreversible action goes through `OuiConfirm`; a redesign never removes a confirmation.

## States

`OuiStatus` is the only way to show a state: a solid chip in the state's colour (or `variant="plain"`, coloured text, inside a sentence). On a band it is a white pill with the state's colour. Nine states, each with its own mark so it reads without colour:

`ok` dot · `busy` dot with halo · `connecting` turning arc · `pending` clock, info · `stale` clock, warning · `warn` triangle · `error` crossed circle · `offline` crossed signal · `idle` ring.

Rules:

1. One page, one connection state. It is in the app bar; nothing else on the page may contradict it.
2. A reason is said once. If the page is offline, busy or incomplete, one `OuiBanner` under the app bar says why and offers the way out; disabled controls point at it with `aria-describedby` and say nothing themselves. A reason that concerns one panel goes in that panel's footer, once.
3. Stale data shows its source and age (`stale`, "Spooler 0.20.1 · read 5 min ago", "Last known · 4 min ago") and loses its colour: a stale hero is grey, not the accent, and stale readings (`OuiSetpoint stale`, `OuiReadout stale`) are grey with no phase. It never keeps a live-looking state.
4. An uncertain outcome is `pending` or `warn`, never `ok`, until the printer or Spoolman confirms it.
5. Unknown is a dash or the words "unknown", never 0, and never an empty cell. A figure built from partial data is `incomplete`: grey, dashed underline, in a warning-tinted block in place of the accent hero, and the gaps named where they occur.
6. Empty, loading and failed areas use `OuiEmpty` with one sentence and, when there is one, the action.

## Components

Import each from `shared/src/components` (or its own `.vue` file). They are not re-exported from `shared/src`, so a page pays only for what it imports.

| Component | What it is |
|---|---|
| `OuiAppBar` | the band in the plugin's accent: mark on a white tile, name, the page's state as a white pill, task tabs as pills (`data-tab`, arrow keys; the active one filled white; a tab can show a `count`, an `attention` dot with an accessible name, and carry extra `attrs`), page actions. Sticky; the state text gives way first, and tabs drop to a second line when narrow |
| `OuiBanner` | a page-level state with its action: `info`, `warn`, `error`, `success`, `neutral` |
| `OuiPanel` | a module: header strip tinted in its `tone` with a solid icon tile, title, one line of meta, actions; body; optional footer. `flush` for tables, media and a hero; `fill` to scroll inside a grid cell |
| `OuiStatus` | a state, as a solid chip (default) or `plain` coloured text |
| `OuiReadout` | label + large tabular value + unit + sub line, with an optional icon tile; with a `tone` the value takes that colour. `sm`, `md`, `lg`, `hero`; `incomplete`, `stale`; blank is a dash |
| `OuiSetpoint` | a controlled value: icon tile, reading, target, its `phase` in colour and words (heating orange, at target green, cooling or off blue; `phaseLabel`), its recent `history` as a filled line with the target dashed, input, Set, Off. `stale` draws it grey. Emits `set` and `off`; sets `data-heater-row`, `data-set`, `data-off` |
| `OuiSpark` | one series over time, as a filled line (with an optional dashed `target`) or bars, in a tone. Shape only: the value is in text beside it and `label` describes it |
| `OuiJob` | a running job: state, name, percentage or count, bar, stats, actions. `hero` fills it with the accent (56 px figure, 12 px white bar) with the actions under the block; `compact` for the dock; `stale` is grey; unknown progress is indeterminate, not 0 % |
| `OuiSlot` | a toolhead or slot: a sample of the filament colour across the top (framed by the card, hatched when empty) carrying the identity badge and the state chip; then the drawn spool, filament, amount left with its level (or whatever `#amount` provides), extra rows, actions; `active` |
| `OuiSpool` | the photo spool: eight renders of the reel, the winding tinted to the filament colour (or colours, side by side, coaxial or longitudinal) and as deep as the filament left; unknown and empty show the bare reel |
| `OuiSwatch`, `OuiLevel` | a filament colour dot; an amount bar: green, amber `low`, red `critical`, unknown hatched. The swatch carries the filament's colour, the bar carries amount and state |
| `OuiThumb` | a picture in a fixed pixel box, fitted, never stretching its row |
| `OuiKeyValue` | facts about one object, as an aligned list or `inline` columns |
| `OuiToolbar` | search and filters, a result count, then the list's actions |
| `OuiEmpty` | empty, loading, error, offline, with a solid icon tile or an `image`; `compact` for a one-row version |
| `OuiSettings`, `OuiFormSection`, `OuiFormRow` | the settings page: section tabs (side list wide, strip narrow), one section at a time scrolling inside, rows with a shared label column, one save bar always on screen |
| `OuiConfirm` | the confirmation dialog: action named on the button, focus on the way back when destructive |
| `OuiIcon` | an icon from `src/icons.ts`: mono, toned, or in a tinted tile (see Icons) |

Classes for what does not need a component: `.oui-hero` (the page's one strongly coloured block; add `.oui-on-band` to fill it with the accent, or `data-tone="warn"` when its value is incomplete), `.oui-on-band` (everything inside is white on the accent), `.oui-page` (page padding and the `oui-page` container), `.oui-stack`, `.oui-row`, `.oui-spacer`, `.oui-cards` (object cards 4, 2 or 1 across, never 3 + 1), `.oui-field`, `.oui-chip` (a fact: neutral, tinted with `data-tone`, solid with `data-solid`), `.oui-label`, `.oui-meta`, `.oui-num`, `.oui-mono`, `.oui-truncate`, `.oui-well`, `.oui-divider`, `.oui-sr`.

Use PrimeVue directly for controls (Button, InputText, InputNumber, Select, Checkbox, ToggleSwitch, SelectButton, Dialog, DataTable, ProgressBar, Message for a message inside a form). Do not wrap them, and do not restyle them locally: change the preset.

## Layout

- Lay the page out in a grid on `.oui-page` with `@container oui-page (min-width: …)`, not media queries: the same page runs in a 280 px dock and a 1900 px tab. A container query cannot restyle its own container, so the grid is always a child of `.oui-page`.
- Dashboards: stacks of panels in columns. Three columns from about 1500 px, two from 900, one below. Put the long list (stock) in its own column with `fill`, so the machine stays on one screen.
- A panel that has nothing to show yet is one row (`OuiEmpty compact`), not a reserved hole. A camera that is off must not push the printer's state down.
- Lists of things with a detail: list and detail side by side from about 1160 px, detail under the list below that.
- Tables: `DataTable size="small"`, fixed layout, name and one meta line in the first column, numbers right-aligned with `oui-num`, the row action last and quiet. The first cell holds an `OuiSpool` or an `OuiThumb`.
- Settings: `OuiSettings`, one `OuiFormSection` per tab, in reading order. A hint is at most one short line; what a whole section needs explained goes in its description, once.
- The dock shows one thing at a time (form, running job, or result); the same parts sit side by side in a tab.
- Text is short and plain, in both languages. Buttons do not wrap; labels and names truncate with a `title`; nothing relies on a fixed text width.

## Do and do not

- Do give every view one primary action, or none, and every page one hero, or none. Three solid buttons means none of them is primary; two accent blocks means neither is the hero.
- Do squint at the page as a thumbnail: it should read as that plugin's colour with its modules distinguishable. If it reads grey, colour is missing where it carries structure; if it reads as confetti, colour is being used without meaning.
- Do put the number first: 37 %, 219.6 °C, R$ 92.10, 70 g. The label is 11 px above it.
- Do keep filament and toolhead colours for filament and toolheads. Never use them, the accent or a hue as decoration: a colour on the page answers "what is this" or "what state is it in".
- Do give the same thing the same hue and icon everywhere. Heat is orange with a thermometer, nozzle or bed in all six plugins.
- Do not repeat a sentence under several cards. Say it once where it applies (States, rule 2).
- Do not stretch controls to fill a row. A 260 px wide "Set" is not easier to hit, it is harder to read.
- Do not add a palette, a font or a component style in a plugin. If the family needs it, it goes here and ships as one release.
- Do not remove a control, a confirmation or an explanation of a disabled action to make a screen cleaner.

## Acceptance

Compare real built pages across all six plugins, dark and light, at 1900×1000, 1280×720 and narrow (720; 280×360 for the Organizer dock), at 200 % zoom, in English and pt-BR, in every state the page has: connecting, offline, busy, empty, loading, error, stale, pending, incomplete. Check computed fonts, radii and colours, not only imports. `scripts/shots.mjs` and `scripts/verify-gallery.mjs` do this for the reference screens (MOCK data); OrcaSlicer's own web views and real devices remain to be checked by the owner.
