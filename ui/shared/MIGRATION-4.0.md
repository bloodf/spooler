# Migrating a plugin to Orca UI foundation 4.0.0

For the agent rolling 4.0.0 out to one plugin. `DESIGN.md` is the specification (what a page should look like and why); this file is the procedure. The reference screen for each plugin is in `ui-foundation/gallery/screens/` and its screenshots in `ui-foundation/evidence-4.0.0/after/`: build the plugin's page to match its reference, with the plugin's real data and every control it has today.

Current release: **4.1.0** (4.0.1 with the photo spool back in `OuiSpool`, see README; 4.0.1 was 4.0.0 plus `OuiSlot #amount`, page-language number formatting in `OuiSlot`, and `attrs`/`attention` on `OuiTab`; nothing removed). Vendor the latest snapshot; the check prints its version's file count and passes only on an unmodified copy.

One rule above the others: **do not patch the vendored copy.** `ui/shared/` must stay byte-identical to the release (its check fails otherwise). If the foundation is wrong or lacks something, report it to the session lead; a fix ships as 4.0.1 for all six plugins.

## 1. Vendor the snapshot

Replace the contents of the plugin's `ui/shared/` with the files listed in `ui-foundation/manifest.json`, plus `manifest.json` itself. Empty the folder first (`git rm -r -q ui/shared` in the plugin, so nothing from 3.1.0 is left behind), then from the workspace root:

```sh
cd ui-foundation
node -e "console.log(Object.keys(require('./manifest.json').files).join('\n'))" > /tmp/oui-files.txt
mkdir -p ../<plugin>/ui/shared
rsync -a --files-from=/tmp/oui-files.txt ./ ../<plugin>/ui/shared/
cp manifest.json ../<plugin>/ui/shared/manifest.json
cd ../<plugin>/ui && node shared/scripts/check.mjs
```

That is 43 files, about 380 kB. New since 3.1.0: `src/icons.ts`, `src/components/*`, `src/fonts/Manrope.woff2`, `licenses/Lucide.txt`, `licenses/Manrope.txt`, `MIGRATION-4.0.md`. Do not copy `gallery/`, `assets/`, `evidence-*`, `dist/` or `node_modules/`.

The check must print `Shared sources verified (42 files); 475 palette pairs per theme…`. Dependencies do not change (Vue 3.5.45, PrimeVue 5.0.5, @primeuix/themes 3.1.1): no install, no lockfile change. Update any text that names the foundation version (`ui/package.json` description, READMEs). Ship the two new licence texts wherever the plugin ships the others.

## 2. Start-up: accent and theme

Pass the plugin's accent as the third argument, and keep applying the theme before the app mounts (every plugin already does):

```ts
installOrcaUI(app, locale, 'violet');
```

| Plugin | Accent | Where `installOrcaUI` is called |
|---|---|---|
| Kobra Control | `violet` | `ui/src/main.ts` |
| U1 Control | `cobalt` | `ui/src/main.ts` |
| Spooler | `magenta` | `ui/src/main.ts` |
| Print Calculator | `lime` | `ui/src/orcaUi.ts` |
| Organizer | `sky` | `ui/src/main.ts` |
| Embedder | `teal` | `ui/src/main.ts` |

The accent fills the app bar, tints every surface and becomes `--oui-primary`. `applyOrcaTheme(theme)` is unchanged and is still called from the plugin's host-theme code (`ui/src/core/theme.ts`; `main.ts` in the Organizer; `orcaUi.ts` in the Calculator).

## 3. Font and page policy

Manrope is embedded by `base.css`; nothing to import. Vite inlines it as a `data:` font, so every page policy must allow it. Add `font-src data:` (replace `font-src 'none'` where present):

| Plugin | File |
|---|---|
| Kobra Control, U1 Control, Spooler, Embedder | `ui/tests/page/cdp.mjs` (the `CSP` constant) |
| Print Calculator | `ui/vite.config.ts` (the `CSP` constant: this one ships in the page) and the exact-string assertion in `ui/tests/build.test.ts` |
| Organizer | `ui/scripts/verify-browser.mjs` (the `CSP` constant) |

Without it the page tests see a CSP violation and the page falls back to the system font. The `emit.mjs` guards (no external URL, no eval) are not affected: the font is a `data:` URL.

## 4. Icons

Replace the plugin's own icon files and loader with named imports from the shared set:

```ts
import { thermometer, spool } from '../../shared/src/icons';
import { OuiIcon } from '../../shared/src/components';
// <OuiIcon :icon="thermometer" />   <OuiPanel :icon="spool" tone="magenta" …>
```

- Kobra Control, U1 Control, Embedder: delete `ui/src/components/Icon.vue`, `ui/src/core/icons.ts`, the `__ICONS__` injection in `plugin.py` and `ui/scripts/emit.mjs`, and the SVG files under `src/<package>/ui/icons/`, once nothing uses them. Keep the identity mark (`icon.svg`) and U1's toolhead badges if the Python side uses them.
- Spooler: `Logo.vue` stays as the mark; other icons move to the shared set.
- Calculator: its tab and inline SVGs move to the shared set; `icon.svg` stays as the mark.
- 97 icons exist (`shared/src/icons.ts`). If one is missing, ask for it: it is added in `ui-foundation/scripts/icons.mjs` and released, not drawn locally.

Where icons go, their three treatments and sizes are in DESIGN.md, Icons.

## 5. Components: what replaces what

Import from `shared/src/components` (not from `shared/src`). Controls stay plain PrimeVue. Delete the local CSS each replacement makes dead; domain layout (the grid of a page) stays local, on `.oui-page` with `@container oui-page (…)`.

**All plugins**

| Today | 4.0.0 |
|---|---|
| header + tabs in `App.vue` | `OuiAppBar` (mark slot, status slot with one `OuiStatus`, `tabs`, actions slot). Tabs keep `data-tab`; other hooks go in the tab's `attrs`, an attention mark in `attention`; give each view `role="tabpanel"` and `aria-labelledby="oui-tab-<value>"` |
| card classes (`.kc-card`, `.sp-*`, `.em-*`, `.oui-panel`) | `OuiPanel` with `icon` and `tone` |
| state pills and text | `OuiStatus` |
| warning/notice strips, `TargetBanner`, `StatusArea`, `PanelNotices`, `PeerNote`, `SpoolerHint`, `InlineAlert` | `OuiBanner`, said once (DESIGN.md, States) |
| `ConfirmDialog.vue` | `OuiConfirm` (keeps `data-dlg`, `data-dlg="confirm"`, `data-dlg="cancel"`) |
| `SpoolFigure.vue` + `assets/spool/*.webp` + `spool-level.ts` picture logic | `OuiSpool` (the same photo spool since 4.1.0; the layers live in the foundation). Delete the 15 WebP files |
| `LevelBar.vue` | `OuiLevel` |
| `SettingsView.vue` | `OuiSettings` + `OuiFormSection` + `OuiFormRow`, one save bar |
| empty/loading/error blocks | `OuiEmpty` (the plugin's illustration for first run: copy its one file from `ui-foundation/assets/illustrations/`) |

**Kobra Control** (reference: `KobraDash.vue` with `state=offline` and `state=setup`, `KobraSettings.vue`)

| Today | 4.0.0 |
|---|---|
| `StatusCard` | `OuiPanel flush` with `OuiJob hero` (job, percentage, elapsed/left/finishes as `OuiReadout`, Pause/Resume/Stop under it); temperatures as `OuiSetpoint` rows; fan, speed, light as rows in a "Temperature and air" panel |
| `MotionPanel` | `OuiPanel tone="cobalt"`; pad layout stays local |
| `CameraCard` | `OuiPanel tone="sky"`; `OuiEmpty compact` while off, the stream when on |
| `AceCard`, `SlotTile`, `AceUnitControls` | `OuiPanel tone="magenta"`, `.oui-cards` of `OuiSlot`, drying strip above |
| `SpoolmanCard` (per-slot selects) | folded into each `OuiSlot` (its Edit action / default slot). Every select it had must remain reachable |
| `StockCard` | `OuiPanel tone="lime" flush fill` + `OuiToolbar` + `DataTable` with `OuiSpool`/`OuiThumb`, `OuiLevel` |
| `UsageCard` | one `OuiBanner tone="warn"` with Review; the table and "I checked it in Spoolman" stay, behind Review |
| `FilesView` | `OuiPanel` + `DataTable` + `OuiThumb` |
| `CertFinder`, `FirstRun` | `OuiFormSection` rows |
| no printer found yet / searching | the bar's state is `connecting` ("Searching"); the page is one `OuiPanel` with `OuiEmpty :image` (kobra-connect), Open settings primary and Search again secondary |

**U1 Control** (reference: `U1Dash.vue`, including `state=setup`): as Kobra Control, plus

| Today | 4.0.0 |
|---|---|
| `ToolheadsCard`, `HeadCard` | `OuiPanel tone="magenta"`, `.oui-cards` of `OuiSlot :tool="n"`; the head's heater, tag and feeder lines in its default slot; Load/Unload/Edit/RFID in `#actions` |
| toolhead heater rows in `StatusCard` | inside each toolhead card (approved behaviour change); bed stays an `OuiSetpoint` |
| Emergency stop | solid `severity="danger"` in the app bar's `#actions`, on every tab |
| `ScreenCard`, `ConsoleView`, `FirmwareCard` | `OuiPanel`; content stays |
| `Thumb.vue` | `OuiThumb` |
| `setup/SetupApp.vue` | `OuiPanel` + `OuiFormRow`; same page build, same boot mode |

**Spooler** (reference: `SpoolerStock.vue`)

| Today | 4.0.0 |
|---|---|
| `SpoolsView`, `StackCard`, `SpoolCard` | `OuiPanel flush` + `OuiToolbar` + `DataTable` rows; a stack is a row with a `×n` chip that still expands to its spools |
| `SpoolDetail`, the action row in `SpoolCard` | the detail panel beside the list (under it when narrow): `.oui-hero.oui-on-band` with `OuiSpool`, `OuiReadout`; one primary action, the rest secondary, Archive apart. All twelve actions stay |
| `PrinterView`, `PrinterPanel`, `LiveUnits`, `TrayCard` | `OuiPanel` + `OuiSlot` |
| `ProgressPanel` | `OuiJob` |
| `PlatePanel`, `LinkedPanel`, `UsagePanel` | `OuiPanel` with rows and `OuiStatus` |
| `StatsView` (10 hard-coded colours) | `OuiReadout`, `OuiSpark`, tones |
| `settings/SettingsView`, `SetupWizard`, `SourceBlock` | `OuiSettings`, `OuiFormSection` |
| Settings button in the header | a tab |

The 380 px dock mode uses the narrow layout: check it separately.

**Print Calculator** (reference: `CalcQuote.vue`)

| Today | 4.0.0 |
|---|---|
| `AppHeader`, `PrinterChip`, `SpoolmanStatus` | `OuiAppBar` with the product name; project and printer in the status slot |
| `PlatesArea` | `OuiPanel tone="cobalt" flush`, plate rows with `OuiSwatch` |
| `SectionsArea` | `OuiPanel tone="orange" flush`, one row per section with its tile and amount |
| `PriceAside` | `OuiPanel` with `.oui-hero.oui-on-band` (`OuiReadout size="hero"`); `data-tone="warn"` and `incomplete` when information is missing |
| `components/base/Badge`, `EmptyState`, `InlineAlert`, `Section` | `OuiStatus`/`.oui-chip`, `OuiEmpty`, `OuiBanner`, `OuiPanel` |
| `theme.css` (`--opc-*` aliases) | deleted; use `--oui-*` |
| `brand/` (teal, amber price) | lime accent; the price is the hero in the accent. Update `BRAND.md` and the logo colours |

**Organizer** (reference: `OrganizerDock.vue`)

| Today | 4.0.0 |
|---|---|
| `PanelHeader` | `OuiAppBar` (no tabs) |
| `ArrangeForm` | same fields; Arrange primary, Fill secondary, the rest behind Advanced |
| `JobProgress` | `OuiJob compact hero`, Cancel under it |
| `StatusBlock`, `ResultCard` | `OuiBanner` (success, warn) and the saved-copy card with its primary action |

In the dock (280 x 360) show one thing at a time: form, running job, or result.

**Embedder** (reference: `EmbedderMain.vue`)

| Today | 4.0.0 |
|---|---|
| `EmbedView` | three columns: form, viewer, list (two, then one, when narrow) |
| `PocketForm` + `PlanCard` | one `OuiPanel`; the plan is an `.oui-on-band` block in it; Add pocket in the footer |
| `Viewer`, `PlaceFallback` | `OuiPanel tone="sky" flush`; the viewer fills the panel's height |
| `PocketList` | `OuiPanel tone="lime" flush`: rows, what to have ready, pauses, Apply in the footer |
| `ResultCard` | `OuiBanner tone="success"` + panel with the pause instruction as its main line |

Use the brand kit's micro mark in the app bar and its magnet and NFC colours for the two kinds of insert.

## 6. Renamed and removed

| 3.1.0 | 4.0.0 |
|---|---|
| `--oui-danger-hover`, `--oui-on-danger` | `--oui-danger-solid-hover`, `--oui-on-danger-solid` (solid red is `--oui-danger-solid`) |
| `.oui-header` | `OuiAppBar` |
| `.oui-result` | `OuiReadout` |
| `.oui-section` | removed; use `.oui-stack` or a panel |
| `.oui-panel`, `.oui-toolbar`, `.oui-empty` | now the classes of the components: use `OuiPanel`, `OuiToolbar`, `OuiEmpty` |
| `.oui-number` | still works; `.oui-num` is the name |
| `OuiStatus variant="badge"` | the default; `variant="plain"` is coloured text |

Unchanged: `installOrcaUI`, `applyOrcaTheme`, `primeVueOptions`, `OrcaPreset`, `UI_VERSION`, the licence key handling, `.oui-meta`, `.oui-muted`, `.oui-field`, `.oui-table-wrap`, `.oui-error-detail`, and the variables `--oui-background`, `--oui-surface`, `--oui-text`, `--oui-muted`, `--oui-border`, `--oui-control-border`, `--oui-primary`, `--oui-on-primary`, `--oui-danger`, `--oui-warning`, `--oui-success` and their `-bg`. `--p-primary-color` still resolves to the accent.

Changed without touching your code: body text 13 px (was 14), controls 32 px high (were 38), small 26, panel radius 8, tinted surfaces, `severity="secondary"` is accent-tinted, text buttons take the accent colour, solid `danger` is a saturated red. Any test that asserts a pixel size, a radius or a computed colour changes.

Never write `light-dark()` in plugin CSS (the build rewrites it and it stops following the host theme): use `--oui-*`, or `.orca-dark` for anything else.

## 7. What must not change

- Element ids and test hooks. Keep every `id`, `data-test`, `data-tab`, `data-dlg`, `data-slot`, `data-t`, `data-feed`, `data-retract`, `data-edit`, `data-load`, `data-unload`, `data-stock`, `data-set`, `data-off`, `data-heater-row`, `data-spool`, `data-stack`, `data-act`, `data-pick`, `data-focus-key`, … on an element that does the same thing. The shared components set `data-tab`, `data-dlg`, `data-heater-row`, `data-set`, `data-off` themselves; put the rest on the controls you pass in. The Organizer's ids (`#spacing`, `#go`, `#fill`, `#adv`, `#cancel`, `#result`) and its tab order (spacing, go, fill, adv) are asserted.
- Controls. A redesign removes no control. Where the reference folds things (slot pickers into slot cards, the usage table behind Review, heaters into toolhead cards), every control is still reachable and does the same thing.
- Safety. Every confirmation that exists today stays, with the same wording of what will happen; emergency stop stays one action away on every tab; an uncertain printer or Spoolman outcome is `pending` or `warn`, never `ok`.
- Disabled reasons. Still explained, once: a page-level `OuiBanner` (or a panel footer) that disabled controls reference with `aria-describedby`. Not removed, and not repeated per card.
- Truthfulness of data. Unknown is a dash or "unknown", never 0. Stale data shows its source and age and loses its colour (`stale` on `OuiJob`, `OuiSetpoint`, `OuiReadout`).
- Bridge messages, Python services, protocol validation: untouched. This is a UI migration.
- Both languages. Every new string goes into the plugin's message files in English and pt-BR; check the longest labels at the narrow width.

## 8. Per-repository risks

| Plugin | Risk |
|---|---|
| Kobra Control | 69 page scenarios and 188 `data-test` references in `ui/tests/page/run.mjs` (the Python gate needs at least 40); about 67 class selectors and 12 `.p-*` selectors in tests. CI "UI build is reproducible": `git diff --exit-code -- src/kobracontrol/ui/app.html ui/build.json`, so commit the rebuilt page and `build.json`. Its `shots.mjs` stock fake lacks `available: true` and no longer shows the Stock card |
| U1 Control | 40 scenarios, 80 `data-test`, about 38 class and 21 `.p-*` selectors. Same reproducible-build check on `src/u1control/ui/app.html`. `SetupApp` is a second mode of the same page |
| Spooler | 42 scenarios (gate 37), 74 `data-test`. The page is embedded compressed in `plugin/spooler/spooler_any.py`: run `scripts/embed_ui.py`; `tests/test_ui_page.py` asserts `UI_PAGE_SHA256` and `UI_PAGE_BYTES`; CI diffs `spooler_any.py` and `ui/build.json`. `.sc-body { height: 100% }` (SpoolCard.vue:174) draws the action panel outside its card today; the new list/detail layout removes it |
| Print Calculator | Hard size limit 960,000 B in `.github/workflows/ci.yml`, `publish-orcacloud.yml` and `ui/tests/build.test.ts`; the page is 938,770 B today and the snapshot alone adds about 41,800 B. Proposed new limit: 1,010,000 B (owner's decision), coming back down as about 43 kB of local CSS is deleted. 60 vitest files with about 325 class-selector uses (`.chip`, `.toast`, `.mrow`, `.sec-btn`, `.pp-card`, …): move tests to roles and `data-*` before deleting classes. Coverage gates 80 % branches, 85 % lines. `build.test.ts` requires `data-v-` scope ids and asserts the exact CSP string. Uses pnpm |
| Organizer | The page is embedded in `shape_arrange.py`: `npm run check:embedded` rebuilds and fails if it is stale; `PANEL_HTML_SHA256` must match. `tests/test_plugin.py` greps the page for `role: status`, `aria-live: polite`, `<html lang="en">` and "up to 300". About 161 id uses in tests. `ui/README.md` still names PrimeVue 4.5.5 and foundation 2.0.3 |
| Embedder | About 60 `data-test`, 20 scenarios. Reproducible-build check on `src/embedder/ui/app.html`; `tests/test_ui_assets.py` checks the page hash. The three.js viewer must take its height from the new grid |

For all: measure the built page before and after (`ui/build.json`), and report the delta. Expect about +42 kB from the snapshot, up to +48 kB for components, about 0.2 kB per icon, minus the deleted local CSS and, for Kobra Control, U1 Control and Spooler, about 97 kB of inlined spool WebPs.

## 9. Known limits of 4.0.0: report, do not patch

1. PrimeVue's own variables are resolved once at the page root. A PrimeVue control inside `.oui-on-band` does not turn white by itself: only the app bar's secondary, text and danger buttons are restyled for the band. Keep other controls off bands (a hero holds no buttons).
2. PrimeVue components the preset does not style explicitly (Toast, Popover, Drawer, Menu, Tabs used inside a page, Paginator, DatePicker, Tooltip beyond colours) fall back to Aura's neutral grey ramp and will look untinted. Report which one you need.
3. `OuiAppBar` renders the tabs only. It does not render or switch the views, and does not scroll the active tab into view on a narrow bar.
4. `OuiSetpoint` holds its own draft value and emits `set`/`off`; it has no v-model and does not validate beyond `min`/`max`.
5. `OuiSpool` paints the filament's colours side by side, coaxial or longitudinal; it shows no per-spool picture. A spool photo goes in `OuiThumb`.
6. `OuiSlot` has one layout. A slot with more than two lines of extra content gets tall; keep extras short or put them behind Edit. Its amount block can be replaced with `#amount` (since 4.0.1); the sample band, badge and spool cannot.
7. `OuiSettings` (4.1.0) shows one section at a time and sizes itself to the window under what sits above it. Inside a nested scrolling container of fixed height, give the container the height instead; the settings still fill what they are given.
8. `OuiConfirm` has two buttons. A dialog with a field or a third choice stays a plain PrimeVue `Dialog`.
9. The icon set has 97 icons. Missing ones are added in the foundation.
10. The illustrations are not in the snapshot; a plugin copies its one file. They were generated; the three marked with reservations in `assets/manifest.json` may be replaced.
11. The reference screens are English and pt-BR mock data in Chrome. WebKit (macOS), WebView2 and WebKitGTK have not rendered them: check container queries, `color-mix()` and the variable font in the real host, and report differences.
12. `scripts/verify-gallery.mjs` and plugin page tests can see headless Chrome stop producing frames on a busy machine (a transition never ends; `requestAnimationFrame` does not fire). That is the environment, not the page; the foundation probe names and retries it.

## 10. Done means

- `node shared/scripts/check.mjs` passes and `ui/shared/` is unmodified.
- The plugin's own build, unit tests, page tests and Python tests pass; no test was skipped or weakened to get there; changed assertions are listed in the report.
- Screenshots of every screen, dark and light, at 1900x1000, 1280x720 and the plugin's narrow width, in English and pt-BR, compared with the reference.
- Bundle size before and after, and any limit or policy changed, named in the report.
- Embedded pages and hashes regenerated where the repository has them.
