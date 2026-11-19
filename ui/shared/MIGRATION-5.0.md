# Migrating a plugin to Orca UI foundation 5.0.0

For the agent rolling 5.0.0 out to one plugin. `DESIGN.md` is the specification (what a page should look like and why); this file is the procedure. The reference screen for each page is in `ui-foundation/gallery/screens/` and its screenshots in `ui-foundation/evidence-5.0.0/after/`: build the plugin's page until it matches its reference, with the plugin's real data.

5.0.0 is a breaking release. A 4.2.2 page compiles against it (no export or prop was removed), but it will look wrong until the steps in section 4 are done, because classes and variables it styles itself with are gone.

One rule above the others: **do not patch the vendored copy.** `ui/shared/` must stay byte-identical to the release (its check fails otherwise). If the foundation is wrong or lacks something, report it to the session lead; a fix ships as 5.0.1 for all six plugins.

## 1. Vendor the snapshot

Replace the contents of the plugin's `ui/shared/` with the files listed in `ui-foundation/manifest.json`, plus `manifest.json` itself. Empty the folder first (`git rm -r -q ui/shared` in the plugin, so nothing from 4.x is left behind), then from the workspace root:

```sh
cd ui-foundation
node -e "console.log(Object.keys(require('./manifest.json').files).join('\n'))" > /tmp/oui-files.txt
mkdir -p ../<plugin>/ui/shared
rsync -a --files-from=/tmp/oui-files.txt ./ ../<plugin>/ui/shared/
cp manifest.json ../<plugin>/ui/shared/manifest.json
cd ../<plugin>/ui && node shared/scripts/check.mjs
```

The check must print `Shared sources verified (65 files); 131 palette pairs per theme…`. New files since 4.2.2: `src/components/OuiCamera.vue`, `OuiControlRow.vue`, `OuiFileBrowser.vue`, `OuiHint.vue`, `OuiPageHeader.vue` and this file; `MIGRATION-4.0.md` is no longer in the snapshot. Do not copy `gallery/`, `assets/`, `evidence-*`, `dist/` or `node_modules/`.

Dependencies do not change (Vue 3.5.45, PrimeVue 5.0.5, @primeuix/themes 3.1.1): no install, no lockfile change. Update any text that names the foundation version.

## 2. Start-up

Nothing changes. Keep `installOrcaUI(app, locale, accent)` with the plugin's hue and keep calling `applyOrcaTheme()` before the app mounts:

| Plugin | Accent |
|---|---|
| Kobra Control | `violet` |
| U1 Control | `cobalt` |
| Spooler | `magenta` |
| Print Calculator | `lime` |
| Organizer | `sky` |
| Embedder | `teal` |

The accent now colours two things only: the mark tile in `OuiAppBar` and the line under the open tab. Give the mark through `#mark` as before, in `currentColor`: it is drawn white on a tile of the hue (4.x drew it in the hue on a white tile).

## 3. What changes without touching your code

- Every surface is a neutral grey from OrcaSlicer (page `#F0F0F0` / `#242428`, panel `#FFFFFF` / `#2D2D31`), the same in all six plugins.
- The app bar is a 44 px neutral bar (was a 52 px band in the accent). Its tabs are plain text with a 2 px line under the open one. The `#status` slot is now on the right, before `#actions`.
- `<Button>` is OrcaSlicer's teal; `severity="secondary"` is OrcaSlicer's grey button with the text colour (was tinted with the accent); `severity="secondary" text` is the text colour (was the accent).
- Fields are the panel colour inside an outline that turns teal on hover and focus. The focus ring, checked boxes and switches, progress bars and selected rows are teal.
- Radii: 3 chips, 4 controls and cards, 6 panels, 8 dialogs (were 4, 6, 8, 12).
- `OuiPanel`: a 40 px neutral header with a hairline under it (was a 44 px strip tinted in its tone); its icon is a plain 16 px icon in the tone (was a solid tile), and with no `tone` it is grey (was the accent). Body padding is 12 px (was 16).
- `OuiIcon tile`: a grey square with the icon in its tone (was a solid square of the tone). With no `tone` it is grey. `soft` is accepted and ignored.
- `OuiStatus`: a chip tinted in the state's colour with coloured text (was solid).
- `OuiBanner tone="info"`: grey with a blue mark. The banner is 36 px high (was 44) and its icon has no tile.
- `OuiJob`: a compact block (section 5). `hero` is accepted and ignored. It no longer pads itself (the hero block did): put it in an `OuiPanel`, or give its container 12 px of padding.
- `OuiSlot`: a neutral card with a 4 px strip of the filament's colour across its top (was a 40 px sample holding the badge). Badge and state chip are on the first line under the strip.
- `OuiSetpoint`: a heater that is off reads in the text colour (was blue).
- `OuiEmpty`: its icon tile is grey unless you give a `tone`.
- `OuiSpark`: with no `tone` it is teal (was the accent).
- `OuiSettings`: the open section has a grey fill and a teal mark (was a solid accent block).
- `materialTone()` returns `'neutral'` for every material: material chips are grey.
- `OuiLevel` is unchanged: green, amber when `low`, red when `critical`.

## 4. What you must change

### Removed, with its replacement

| Removed | Use |
|---|---|
| `.oui-on-band` | nothing: delete the class. There is no accent-filled block |
| `.oui-hero.oui-on-band` | `.oui-hero` alone: a neutral block. `data-tone="warn"` still tints it for an incomplete value |
| `--oui-band`, `--oui-on-band`, `--oui-band-success` (and the other `band-*`) | `--oui-accent-solid` with `--oui-on-solid` for a mark tile; nothing else should be filled with the plugin's hue |
| `--oui-<hue>-hover`, `--oui-<hue>-band` | `--oui-<hue>-solid` (with `--oui-on-solid`) |
| `--oui-<hue>-background`, `-surface`, `-raised`, `-inset`, `-border`, `-control-border` (palette roles `violetBackground` …) | `--oui-background`, `--oui-surface`, `--oui-raised`, `--oui-inset`, `--oui-border`, `--oui-control-border` |
| `.oui-slot-sample` | `.oui-slot-strip` (the colour) and `.oui-slot-head` (badge and state) |
| `.oui-job-head`, `.oui-job[data-hero]` | `.oui-job-block`; the parts keep their classes (`.oui-job-id`, `.oui-job-figure`, `.oui-job-bar`, `.oui-job-stats`, `.oui-job-actions`) |
| `.oui-tile[data-soft]` | `.oui-tile` |
| `.oui-status` on a band (white pill) | `.oui-status` |

Search the plugin's own CSS and tests for each name in the left column.

### `--oui-primary` is no longer a text colour

`--oui-primary` is now the fill of the teal button (`#008172` light, `#00675B` dark), with `--oui-on-primary` (white) on it. In dark it does not hold 4.5:1 as text or 3:1 as a mark. In the plugin's own CSS:

| 4.x use of `var(--oui-primary)` | 5.0 |
|---|---|
| `color:` of text or a link | `var(--oui-primary-text)` |
| a border, outline, bar, dot, stroke or fill that marks selection, focus or progress | `var(--oui-primary-mark)` |
| `background:` of a solid block with `--oui-on-primary` text | unchanged |
| "this is the plugin's colour" | `var(--oui-accent)`, and only for identity (section 3 of `DESIGN.md`) |

`--oui-primary-soft` is still the selected row. `--oui-primary-hover` is still the button's hover.

### `tone="accent"`

`accent` now means the plugin's own hue and is for identity. Replace every `tone="accent"` (and `data-tone="accent"`) on a panel, icon, readout, chip or chart with the domain hue of what it is about (`orange` heat, `cobalt` motion, `sky` camera and air, `magenta` filament, `lime` stock and money, `teal` trust), or remove it for grey. Use `tone="primary"` where the colour should be OrcaSlicer's teal.

### Buttons

- A destructive action in the page (stop or cancel a print, delete, archive) is `severity="danger" outlined`. The solid red is for the emergency stop in the app bar and for the confirm button of `OuiConfirm`. Every confirmation stays.
- Where two actions are opposites and only one applies (Pause and Resume), show the one that applies.
- A page has at most one `<Button>` without a severity.

### Helper paragraphs

Remove every paragraph under a module or control. A reason a control is off goes in the page's one `OuiBanner`; an explanation goes behind an (i): `hint` and `hint-label` on `OuiPanel`, or an `OuiHint` in an `OuiPageHeader` or beside a group label. Keep the text; move it. A "learn more" link goes inside the hint.

## 5. Page grammar

Every main page is, in this order: `OuiAppBar`, then inside `<main class="oui-page">` an `OuiPageHeader`, at most one `OuiBanner`, and the content in `.oui-dash`, `.oui-split` or `OuiSettings`. Lay out with `@container oui-page`, as before.

```vue
<OuiAppBar v-model="tab" name="U1 Control" :tabs="tabs">
  <template #mark>…</template>
  <template #status><OuiStatus state="busy">Printing</OuiStatus></template>
  <template #actions><!-- emergency stop --></template>
</OuiAppBar>
<main class="oui-page" role="tabpanel" aria-labelledby="oui-tab-dashboard">
  <OuiPageHeader title="Snapmaker U1" meta="10.25.1.83 · firmware …"><template #actions>…</template></OuiPageHeader>
  <OuiBanner … />
  <div class="oui-dash">
    <OuiPanel class="oui-dash-top"><OuiJob …/></OuiPanel>
    <div class="oui-dash-main">…modules…</div>
    <div class="oui-dash-side">…modules…</div>
  </div>
</main>
```

The app bar's `#status` holds the state chip only. The printer's name, address and firmware, which 4.x put beside it, are the page header's `title` and `meta`.

### Kobra Control and U1 Control: dashboard

Reference: `gallery/screens/KobraDash.vue`, `U1Dash.vue`.

- **Status block**: `OuiJob` in an `OuiPanel` with no title, class `oui-dash-top`. Put the picture in `#thumb`: it is shown in a fixed 72 px box, so pass the model thumbnail or the printer picture at any size and do not size it yourself. `#status`, the default slot (small `OuiReadout size="sm"` for elapsed, left, finishes) and `#actions` are as before; the actions are now inside the block, at its right.
- **Main column** (`.oui-dash-main`): the filament module (toolheads or ACE slots as `OuiSlot` in `.oui-cards`), then one Controls module.
- **Controls module**: one `OuiPanel` with `.oui-controls` inside, and one `.oui-controls-group` per task, each starting with `<p class="oui-label">`. Heaters stay `OuiSetpoint`; fan, speed, light, cover and mode rows become `OuiControlRow` (`label`, `icon`, `tone`, `value`, and the control in its slot). This replaces "Bed and chamber" and "Temperature and air": U1's bed goes under Temperature, speed, top cover and light under Machine; Kobra's nozzle and bed under Temperature, fan, speed mode and light under Machine.
- **Side column** (`.oui-dash-side`): Camera, then Move (Kobra), then Printer.
- **Camera module**: `OuiPanel flush` with the rate, save and on/off controls in `#actions` (small), and `OuiCamera` as the body: `src`, `alt`, `state` (`live`, `off`, `loading`, `error`), `title` and `text` for the states without a picture, `#overlay` for chips over the picture, `#actions` for the way out. The paragraph about the frame rate becomes the panel's `hint`.
- **Empty and loading**: a module with nothing to show keeps its header and shows one `OuiEmpty compact` row (`state="offline"` when the printer is away). While the first read is under way, show `.oui-skeleton` bars. Do not hide modules.
- **Stock leaves the dashboard.** Remove the stock module and its link controls from the dashboard. The spool chooser inside each slot card stays.

### Kobra Control and U1 Control: Stock tab

Reference: `gallery/screens/PrinterStock.vue` (`?screen=u1-stock`, `kobra-stock`).

Add a `stock` tab after `dashboard` (`{ value: 'stock', label, icon: spool, count }`). The page is an `OuiPageHeader` (title, count, source and age in `meta`; Refresh and the (i) in `#actions`) and `<div class="oui-split" data-rail>` with two panels:

- Rail: an `OuiPanel` holding the link target as a `role="radiogroup"` list of the places a spool can go (T1…T4, or the ACE slots), each with `.oui-slot-badge` (`data-tool="1"`…`"4"` for toolheads), a 32 px `OuiSpool` and what is loaded. This replaces the "Link target" select.
- List: an `OuiPanel flush` with `OuiToolbar` (search, material, "same material as …", count) over a `DataTable size="small"`: spool, material, loaded in, left, and one action per row named with the chosen place. A spool already there shows `OuiStatus state="ok"` instead.

The sentences that sat under the 4.x stock module (how Spoolman is reached, who records filament use, why there are two tabs) go into the page header's `OuiHint`. Every link still checks and confirms as it does now; only where the controls sit changes.

### Kobra Control and U1 Control: Files tab

Reference: `gallery/screens/PrinterFiles.vue` (`?screen=kobra-files`, `u1-files`; `&state=multi|loading|empty`).

Replace the plugin's own file list with `OuiFileBrowser`. The page owns the data and the work:

```vue
<OuiFileBrowser v-model:folder="folder" v-model:selected="selected" :folders="folders" :files="files" :labels="labels"
  :loading="loading" :readonly="printerBusy" :describedby="busyBannerId" @move="onMove" @delete="onDelete" @open="onOpen">
  <template #toolbar><!-- search --></template>
  <template #rail><!-- free space --></template>
  <template #actions="{ file }"><!-- Print, Download, Rename for one file --></template>
  <template #selection="{ files }"><!-- actions for several, if any --></template>
  <template #bulk="{ ids }"><!-- more bulk actions in the bar, if any --></template>
  <template #empty><!-- Upload --></template>
</OuiFileBrowser>
```

- `folders`: `{ id, name, parent?, count?, locked? }[]`, flat; a missing `parent` is a root. `locked` folders cannot receive files.
- `files`: the open folder's files, `{ id, name, size?, sizeText?, modified?, modifiedText?, kind?, thumb?, facts? }[]`. `size` and `modified` are numbers for sorting; the texts are what is shown; `facts` fill the detail panel.
- `labels`: every string, in the page's language (`OuiFileBrowserLabels`; several are functions of a count).
- `@move` gives `{ ids, to }`, from a drop on a folder or from "Move to…". `@delete` gives the ids after the user confirmed in the component's own `OuiConfirm`: do not confirm again. `@open` is Enter or a double click.
- When the folder changes, load its files and pass them; the component clears the selection.
- Set its height: `--oui-files-height` on a parent (the reference uses the window less the bars above). Without it the component is as tall as its content, at least 360 px.
- Test hooks: `[data-folder="<id>"]` on tree items, `[data-file="<id>"]` on rows, `aria-selected` on both, `[data-dlg="confirm"]` and `[data-dlg="cancel"]` in the confirmation.

If the printer has no folders, pass its storage roots as the folders; a single root is fine. If the printer cannot move files, pass `readonly` and say why once, or leave `@move` unhandled and lock every folder.

### Spooler

Reference: `gallery/screens/SpoolerSpools.vue`. Tabs stay Spools, Printer, Stats, Settings. The Spools page is an `OuiPageHeader` (count and totals in `meta`; Sync and Add in `#actions`, Add being the primary) and `.oui-split data-detail`: the spools as neutral cards with a 64 px `OuiSpool`, and the selected spool in an `OuiPanel` on the right. Remove the accent-filled detail block: the 128 px spool on an `.oui-well` is the picture, and the amount is a 28 px figure with its `OuiLevel`. The printer tab's slot cards follow the dashboard's filament module.

### Print Calculator, Organizer, Embedder

References: `CalcQuote.vue`, `OrganizerDock.vue`, `EmbedderMain.vue`. These keep their layouts.

- Print Calculator: the price block is `.oui-hero` alone (neutral), with the price in the text colour at its large size; `data-tone="warn"` when incomplete, as before. The Price panel's icon is `tone="lime"`.
- Organizer: `OuiJob compact` without `hero`, in a container with 12 px of padding (the job no longer pads itself). The dock at 280 px shows the same stacked block.
- Embedder: the plan block is a neutral block on `--oui-raised` with a hairline; the stage behind the drawing is `--oui-inset`; the ghost and cross-hair strokes use `--oui-primary-mark`.

## 6. Do not change

Python services, bridge messages, job identity, cancellation, the emergency route, every confirmation, every control, the page's CSP, and the test hooks the components already set (`data-tab`, `data-heater-row`, `data-set`, `data-off`, `data-dlg`, `data-section`, `data-toast-id`, `data-spool` where the page sets it). Moving stock to its own tab moves controls; it removes none.

## 7. Sizes

Built size of each shared component (`node scripts/sizes.mjs`): one minified build per component at the plugins' target, Vue and PrimeVue left out. A figure includes what the component imports from this package, so they overlap and do not add up to a page. The core is `index.ts`, `base.css` and the preset, with the embedded font.

| Component | 5.0.0 raw kB | 5.0.0 gzip kB | 4.2.2 raw kB | 4.2.2 gzip kB |
|---|--:|--:|--:|--:|
| (core) index.ts + base.css + preset | 52.9 | 28.8 | 54.1 | 29.3 |
| OuiAppBar | 6.9 | 2.5 | 6.8 | 2.5 |
| OuiBanner | 5.7 | 2.1 | 5.7 | 2.1 |
| OuiCamera | 6.9 | 2.5 | new | new |
| OuiConfirm | 1.7 | 0.8 | 1.7 | 0.8 |
| OuiControlRow | 3.6 | 1.4 | new | new |
| OuiEmpty | 5.1 | 1.9 | 5.2 | 1.9 |
| OuiFileBrowser | 33.9 | 9.4 | new | new |
| OuiFormRow | 2.0 | 0.9 | 2.0 | 0.9 |
| OuiFormSection | 8.0 | 2.7 | 5.8 | 1.9 |
| OuiHint | 4.3 | 1.7 | new | new |
| OuiIcon | 1.9 | 0.8 | 2.0 | 0.8 |
| OuiJob | 5.7 | 1.9 | 4.8 | 1.7 |
| OuiKeyValue | 1.3 | 0.7 | 1.3 | 0.7 |
| OuiLevel | 1.4 | 0.7 | 1.5 | 0.8 |
| OuiPageHeader | 1.6 | 0.7 | new | new |
| OuiPanel | 6.9 | 2.4 | 4.6 | 1.6 |
| OuiReadout | 4.9 | 1.7 | 5.0 | 1.8 |
| OuiRequirement | 8.4 | 2.9 | 8.7 | 3.0 |
| OuiSetpoint | 10.2 | 3.3 | 10.2 | 3.3 |
| OuiSettings | 11.8 | 4.1 | 11.9 | 4.1 |
| OuiSlot | 105.1 | 74.8 | 105.7 | 74.9 |
| OuiSpark | 3.8 | 1.5 | 3.8 | 1.5 |
| OuiSpool | 99.0 | 72.7 | 99.0 | 72.7 |
| OuiStatus | 4.9 | 1.8 | 5.3 | 1.9 |
| OuiSwatch | 1.2 | 0.7 | 1.2 | 0.7 |
| OuiThumb | 3.3 | 1.3 | 3.4 | 1.3 |
| OuiToastHost | 8.1 | 3.0 | 8.1 | 3.1 |
| OuiToolbar | 1.2 | 0.6 | 1.2 | 0.6 |

What a 4.2.2 page gains by updating: `OuiPanel` now carries `OuiHint` (about 2.3 kB raw, once per page). A printer plugin that adopts the Files tab adds `OuiFileBrowser`, 33.9 kB raw including `OuiConfirm`, `OuiEmpty`, `OuiKeyValue`, `OuiThumb` and `OuiIcon`, which those pages already have; it uses PrimeVue's Button, Select and Dialog, which they also already import. `OuiSpool` and `OuiSlot` are the eight spool renders (about 72 kB), unchanged. Measure the plugin's real page against its limit (90 % of 1,572,864 bytes) after migrating; these figures are not a substitute.

## 8. Known limits

- The reference screens were rendered in headless Chrome with mock data. Nothing here was run inside OrcaSlicer's web views (WKWebView, WebView2).
- `OuiFileBrowser`'s drag and drop was exercised with synthetic drag events in headless Chrome. HTML drag and drop inside OrcaSlicer's web view is not verified; "Move to…" does the same without dragging and must stay available.
- `OuiHint`'s bubble is positioned inside its parent: a scrolling ancestor can clip it. Use `end` for an (i) near the right edge.
- `scripts/verify-gallery.mjs` and `scripts/contact-sheet.mjs` are the 4.0.0 evidence tools and were not updated.
- Light theme: the teal button is `#008172`, not OrcaSlicer's `#009688`, and teal text is `#00675B`, to keep 4.5:1. `DESIGN.md` lists every value that differs from OrcaSlicer and why.
