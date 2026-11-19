# Orca UI foundation 5.0.3 — Vue and PrimeVue

Version 5.0.3 takes in what the Kobra Control and U1 Control migrations found. It is additive: no prop, slot or event is removed, and a component given none of the new props behaves as in 5.0.2, apart from the fixes.

Fixes:

- `OuiFileBrowser`, detail pane: when its content was taller than the browser, the picture's row shrank to nothing and the picture was drawn over the name and facts. Rows are now as tall as their content and the pane scrolls.
- `OuiFileBrowser`, Delete key: on a focused row with nothing selected, the first press selected the row and asked nothing. It now asks at once.
- `OuiFileBrowser`, focus: after a delete or a move, focus stays in the list (the first row, or the list when it is empty) instead of falling to the page.
- `OuiFileBrowser`, the last column is 168 px (was 132): a short date and time fits in English and pt-BR.
- `OuiConfirm`: once closed, focus goes back to what had it when the dialog opened, if that is still on the page; then it emits the new `closed` event.
- `OuiSetpoint`: `describedby` now reaches the number field itself (PrimeVue was putting it on the field's wrapper).

New, all optional:

- `OuiSetpoint`: `inputId` (an id for the field, and a real `<label>`), `error` (a line under the row, from the page), `validate` (asked before every `set`; it can refuse a value, with a reason shown in that line, and may be async; with it the field no longer clamps to `min`..`max`), `offAlways` (Off stays enabled with no target).
- `OuiFileBrowser`: `sort` (the order the list opens in, e.g. `{ key: 'modified', down: true }`); a `#folder` slot beside the path for what can be done to the open folder (rename, move, delete, new folder); `readonly` on a folder (its files can be looked at, not moved, deleted or added to).
- `OuiCamera`: a `frame` event each time the built-in picture has loaded; `fit="contain"` to show a picture that is not 16:9 whole; a `#picture` slot for a page's own player (`<video>`, canvas).
- `OuiPanel`: `hintId`, the id of the hint's text, for a control's `aria-describedby` (`OuiHint` takes `id`).

To update from 5.0.2, replace `ui/shared/` with the 5.0.3 snapshot and rebuild. Then remove what a plugin added to work around these: its own heater row, CSS on `.oui-files-detail`, `.oui-files-move` or the date column, a click on a column header at mount, folder actions in `#toolbar`, a `<video>` laid over `OuiCamera`, a captured `load` listener on the camera, and focus moved by hand after a delete.

## 5.0.2

Version 5.0.2 fixes `OuiHint` (and so every `OuiPanel` with a `hint`); nothing else changes:

- A closed bubble was only invisible, and still counted toward the page's width: an (i) near the right edge gave the page a horizontal scrollbar, and its open bubble was cut off by the window. Closed, the bubble is now `display: none` (it is still the button's `aria-describedby` text).
- Each time it opens, the bubble is placed against the window: under the button and starting at it when that fits, moved left as far as it must, and above the button when there is no room below. No prop is needed for an (i) near an edge. `end` still exists and is now only a preference.

To update from 5.0.1, replace `ui/shared/` with the 5.0.2 snapshot and rebuild. Remove any CSS a plugin added to move or hide `.oui-hint-bubble`, and any `end` added only to avoid the overflow.

## 5.0.1

Version 5.0.1 makes the Files tab one component for both printer plugins; nothing that 5.0.0 pages rely on changes:

- `useFileBackend(backend, options)` (new, `src/components/fileBackend.ts`) turns a storage adapter (`OuiFileBackend`: `folders()`, `list()`, `remove()`, `move()`) into the props and handlers of `OuiFileBrowser`: reading, the failure state with its retry, running a move or delete and reading again afterwards.
- `OuiFileBrowser` works over a storage with no folders (`folders` omitted or empty): no tree, no path, no "Move to", no dragging; the table takes the rail's place and multi-select, delete and the detail panel are unchanged. `movable` false keeps the tree and drops moving. New props `error`, `busy`, `movable`; new event `retry`; new optional labels `loadFailed`, `retry`. `folders` and `folder` are now optional.

To update from 5.0.0, replace `ui/shared/` with the 5.0.1 snapshot (one more file) and rebuild. `MIGRATION-5.0.md` has the adapter's contract.

## 5.0.0

Version 5.0.0 is a redesign and a breaking release: the pages take OrcaSlicer's own colours. `DESIGN.md` is the specification, `MIGRATION-5.0.md` the procedure for a plugin. In short:

- Every surface is one of OrcaSlicer's neutral greys, the same in all six plugins. Nothing is tinted by the plugin any more.
- The primary action, focus, selection and progress are OrcaSlicer's teal. The everyday button is its grey regular button.
- The plugin's hue (`installOrcaUI(app, locale, accent)`, unchanged) is only its mark tile and the line under the open app-bar tab.
- One page grammar: `OuiAppBar`, `OuiPageHeader`, at most one `OuiBanner`, then `.oui-dash`, `.oui-split` or `OuiSettings`. Modules are `OuiPanel` with a 40 px neutral header; what a module needs explained is its `hint`, not a paragraph under it.
- New components: `OuiPageHeader`, `OuiHint`, `OuiControlRow`, `OuiCamera`, `OuiFileBrowser`. `OuiJob` is now a compact status block with a 72 px picture.
- Removed: the per-accent surface roles, `--oui-band`, `--oui-on-band`, `.oui-on-band`, the filled `.oui-hero`, the solid icon tile and the solid state chip. `--oui-primary` is now the teal button fill: text and marks in the primary colour use `--oui-primary-text` and `--oui-primary-mark`.

To update from 4.2.2, follow `MIGRATION-5.0.md`. Dependencies do not change.

## 4.2.2

Version 4.2.2 draws a loaded spool whose amount is unknown as loaded, not as empty:

- `OuiSpool` with a `color` (or `colors`) and `fraction` null draws the full reel in that colour with a small "?" badge in its top-right corner, in the page's surface and text colours, and sets `data-unknown` (with `data-level="1"`). With no colour, `fraction` null is still the bare reel (`data-level="8"`), as is a fraction of 0. A known fraction draws as before. The spool stays `aria-hidden`: keep saying "weight unknown" in the text next to it.
- `OuiSlot` passes an unknown amount through as null instead of drawing a made-up 60 % level; an empty slot is still the bare reel. A slot with `#amount` still draws its spool from `remaining` and `initial`: a percent-only tray passes `:remaining="64" :initial="100"` alongside its `#amount`, or the spool shows the unknown badge next to a known percentage.

Plugins that passed `remaining` 0 of `initial` 1 (or a fraction of 0) to avoid the 60 % level should pass the real fraction, or null when unknown. To update from 4.2.1, replace `ui/shared/` with the 4.2.2 snapshot and rebuild.

## 4.2.1

Version 4.2.1 fixes the 4.2.0 notices; nothing is removed:

- When the stack is full, the toast that leaves is the oldest that is neither an error nor carries an action; only when every toast is one of those does the oldest leave.
- A toast's action runs, and the toast closes even if the action throws. A toast with an action stays 8 s by default.
- Toasts count down only while the page is visible and has focus (`document.visibilityState === 'visible'` and `document.hasFocus()`): switching to another OrcaSlicer tab or app holds every timer, and coming back resumes each with the time it had left. Hover and focus still hold a toast. Errors never leave by themselves, whatever timeout is passed. Pages tested in jsdom or headless Chrome must report focus (`document.hasFocus`) for timed toasts to leave.
- `OuiBanner` takes `show` (default true): pass the banner's condition there instead of `v-if`. When it turns false, or the `dismissKey` changes, the stored dismissal is forgotten, so the same problem coming back later shows again.
- Closing a toast that holds focus (its X, its action, from code, or the stack making room) puts focus back where it came from at that moment, not after the leave animation. A plugin's own focus workaround can go.
- A toast's title and body are separated by a space in the text, so they read as two sentences to screen readers and tests.
- `OuiRequirement` takes `disabled` (Check again off, for example while there is nothing to check against yet).
- `OuiSettings` lifts the toast stack above its save bar itself while the bar is on screen (`--oui-toast-bottom` on the root) and gives the space back when Settings is hidden or unmounted. Delete a plugin's own `--oui-toast-bottom` for Settings.

To update from 4.2.0, replace `ui/shared/` with the 4.2.1 snapshot and rebuild.

## 4.2.0

Version 4.2.0 adds notices that never stay on screen for good, and a row for what a feature needs:

- `OuiToastHost` and `useToast()` (`src/components/toast.ts`): one toast stack per page, bottom-left, newest at the bottom, at most four. `useToast().show({ tone, title, body?, action?, timeout?, key? })`; tones `info`, `success`, `warn`, `error`. Every toast has a close button (`closeLabel` on the host, default "Close"); info and success leave after 5 s, warnings after 8 s, errors stay until closed; hover or focus holds the timer; errors are `role="alert"`, the rest `role="status"`; a `key` replaces the toast with the same key instead of stacking a copy; motion follows `prefers-reduced-motion`. Mount `<OuiToastHost :close-label="…" :label="…" />` once at the end of the app root. A page with a bar along the bottom edge sets `--oui-toast-bottom`.
- `OuiBanner` takes `dismissible`, `dismissKey` and `closeLabel`, and emits `dismiss`. With `dismissKey` the dismissal is remembered for the session (`sessionStorage`); put what the banner is about in the key (`spoolman-down:<url>`, `unconfirmed:<count>`) so it comes back when that changes, not on every poll.
- `OuiRequirement`: one row for "this feature needs X" in a Settings section: `name`, `why`, `status` (`found`, `missing`, `checking`, `unknown`) with `statusLabel`, `detail` (where it was found), `installText`, `installUrl`, `installLabel`, `checkLabel`, `checking`; emits `check` ("Check again") and `open` (the install link; without an `open` listener it is a plain link).

Nothing that 4.1.0 pages rely on changes. To update, replace `ui/shared/` with the 4.2.0 snapshot and rebuild.

## 4.1.0

Version 4.1.0 draws the spool with the photo spool again: `OuiSpool` shows the product render of the reel (eight fill levels, `src/assets/spool/*.webp`, 72 kB) with the winding tinted to the filament colour or colours, as Spooler, Kobra Control and U1 Control drew it before 4.0.0. Its props are unchanged, plus an optional `direction` (`coaxial` or `longitudinal`) for how a multi-colour filament's colours run; without it they sit side by side. It also fixes the page height and turns settings into tabs:

- The page fills the whole tab at every height and follows it when the window is resized. `html` and `body` carry the page colour (OrcaSlicer's grey no longer shows under a short page), `body` is at least the viewport (`100dvh`, `100vh` where the web view lacks it) and `#app` and its root grow to fill it. The document keeps its one scrollbar. A plugin's own `html, body, #app { min-height }` or shell `min-height: 100vh` is no longer needed; delete it.
- `OuiSettings` shows one section at a time, picked from tabs: a side list when wide, a scrolling strip when narrow (`role="tablist"`/`tab`/`tabpanel`, arrow keys, Home and End). `.oui-stack` wrappers in its slot are flattened, so there are no columns left. It is as tall as the window under what sits above it, so the selected section scrolls inside and the save bar is always on screen, also after the window is made shorter: the height is CSS (`dvh`) and the offset is measured again on every resize. It remembers the last tab per page, opens `#<section id>` from the address, and `select(id)` (template ref) opens one from code. Section ids, props, slots and the `.oui-settings-link` / `.oui-settings-foot` classes are unchanged.

To update from 4.0.1, replace `ui/shared/` with the 4.1.0 snapshot (now including `src/assets/spool/`), delete any root height rules of your own and rebuild. Page tests that fill a field in a section other than the first must pick its tab first (`.oui-settings-link[data-section="<id>"]`).

Version 4.0.1 adds three things the Spooler migration needed, and changes nothing that 4.0.0 pages rely on: `OuiSlot` takes an `#amount` slot that replaces its weight line and level bar (percent-only trays, hidden weight or bar, other units), and its built-in line formats numbers in the page language instead of the browser's; an `OuiTab` can carry `attrs` (test hooks on the tab button) and `attention` (a dot with an accessible name). To update from 4.0.0, replace `ui/shared/` with the 4.0.1 snapshot and rebuild.

Version 4.0.0 is a redesign, not a patch: a colour system (one accent per plugin, seven hues, state colours), one icon set (`src/icons.ts`: 86 Lucide icons and 11 drawn for the family), a real type scale, denser controls, and for the first time shared Vue components (`src/components/`) for the structures the six plugin pages have in common. `DESIGN.md` is the specification. Runtime dependencies are unchanged (Vue 3.5.45, PrimeVue 5.0.5, @primeuix/themes 3.1.1); the icons are copied in at build time from the dev dependency `lucide-static` 1.73.0 (ISC, `licenses/Lucide.txt`), so consumers install nothing new. The typeface is Manrope, embedded as a 21,476 B subset (`src/fonts/Manrope.woff2`, SIL OFL 1.1, `licenses/Manrope.txt`). No image was added. Reference screens for all six plugins, with before/after pairs, are in `evidence-4.0.0/index.html` (MOCK data).

## Migrating a plugin from 3.1.0

`MIGRATION-4.0.md` is the full procedure for a roll-out (vendoring, accent, policy, icons, the component mapping per plugin, what must not change, per-repository risks, known limits). In short:

1. Replace `ui/shared/` with the 4.0.0 snapshot (every file in `manifest.json`, now including `src/components/*`) and run `node shared/scripts/check.mjs`.
2. Nothing else is required for the page to build: `installOrcaUI`, `applyOrcaTheme`, `primeVueOptions`, `OrcaPreset`, `UI_VERSION` and the licence handling are unchanged, and every 3.1.0 colour variable still exists (`--oui-background`, `--oui-surface`, `--oui-text`, `--oui-muted`, `--oui-border`, `--oui-control-border`, `--oui-primary`, `--oui-on-primary`, the three state pairs). Measured on a minimal page, this step alone adds 41.8 kB (26.1 kB gzip), of which 28.7 kB is the embedded font. The preset now reads the `--oui-*` variables, so `applyOrcaTheme()` has to run before the app mounts, as every plugin already does. Pass the plugin's accent as the third argument of `installOrcaUI` (Kobra Control `violet`, U1 Control `cobalt`, Spooler `magenta`, Print Calculator `lime`, Organizer `sky`, Embedder `teal`); without it the accent is teal, as in 3.1.0.
3. What changes without touching your code: body text is 13 px (was 14), controls are 32 px high (were 38) and small ones 26, panels have an 8 px radius, the default `secondary` button is a quiet raised key instead of an outlined one, status-coloured buttons are tinted, and solid `danger` is a saturated red in both themes. Re-take every screenshot and re-check any test that asserts a pixel size, a radius or a computed colour.
4. Removed: `--oui-danger-hover` and `--oui-on-danger` (use `--oui-danger-solid-hover`, `--oui-on-danger-solid`); the classes `.oui-header` (use `OuiAppBar`), `.oui-result` (`OuiReadout`), `.oui-section` and `.oui-empty` (`OuiEmpty`). `.oui-panel` and `.oui-toolbar` are now the classes of `OuiPanel` and `OuiToolbar`: use the components. `.oui-number` still works; `.oui-num` is the new name. `.oui-meta`, `.oui-muted`, `.oui-field`, `.oui-table-wrap` and `.oui-error-detail` are unchanged.
5. New variables: `--oui-raised`, `--oui-inset`, `--oui-primary-soft`, `--oui-band`, `--oui-on-band`, `--oui-on-state`, `--oui-info`, `--oui-info-bg`, `--oui-danger-solid` (+ hover, on), `--oui-tool1`…`4`, `--oui-on-tool`, and the seven hues `teal`, `sky`, `cobalt`, `violet`, `magenta`, `lime`, `orange`, each with `-soft`, `-hover` and `--oui-on-…`. The surface variables now differ per accent.
6. Then move the page onto the shared components and delete the local CSS they replace. Import them from `../shared/src/components` (they are not re-exported from `../shared/src`, so unused ones cost nothing): all twenty-one together add 48 kB (13 kB gzip). Import icons by name from `../shared/src/icons` (about 0.2 kB each) and delete the plugin's own icon files and its icon loader, keeping only the identity mark. `OuiSpool` draws the spool from the fifteen WebP layers Kobra Control, U1 Control and Spooler used to carry each; delete the plugin's own copies.
7. Do not write `light-dark()` in plugin CSS: the build rewrites it and it stops following the host theme. Use the `--oui-*` variables, or `.orca-dark` for anything else.
8. Every page policy must allow `font-src data:` for the embedded typeface: change `font-src 'none'` to `font-src data:` in `ui/tests/page/cdp.mjs` of Kobra Control, U1 Control, Spooler and Embedder, and add `font-src data:` to the Calculator's policy (`ui/vite.config.ts`) and the Organizer's (`ui/scripts/verify-browser.mjs`). Without it the browser reports a violation (which those tests fail on) and the page falls back to the system font. The Calculator's 960,000 B limit (`.github/workflows/ci.yml`, `publish-orcacloud.yml`, `ui/tests/build.test.ts`) does not hold the drop-in step (938,770 + about 41,800): raise it to 1,010,000 B and bring the page back down as its local CSS is deleted.
9. Surfaces are tinted by the accent, the app bar is a solid band, the default `OuiStatus` is a solid chip and `severity="danger"` is the standard destructive button: re-take every screenshot.

To rebuild the font subset (not part of the build; needs uv):

```sh
uvx --from fonttools --with brotli fonttools varLib.instancer Manrope.ttf wght=400:700 -o Manrope-400-700.ttf
uvx --from fonttools --with brotli pyftsubset Manrope-400-700.ttf --output-file=src/fonts/Manrope.woff2 --flavor=woff2 \
  --unicodes="U+0020-007E,U+00A0-00FF,U+0152,U+0153,U+2013,U+2014,U+2018,U+2019,U+201C,U+201D,U+2022,U+2026,U+2030,U+2032,U+2033,U+20AC,U+2190-2193,U+2212,U+2260,U+2264,U+2265,U+00D7" \
  --layout-features="kern,liga,tnum,lnum,case,ccmp,locl,mark,mkmk,calt" --no-hinting --desubroutinize
``` Keep `--use-mock-keychain --password-store=basic` on every headless Chrome.

## Earlier versions

Version 3.1.0 moves the build tools to TypeScript 7.0.2 (the native compiler). TypeScript 7 has no JS API and vue-tsc 3.3 needs one, so `scripts/vue-tsc.mjs` runs vue-tsc on the TypeScript 6 compiler from Microsoft's `@typescript/typescript6` package. Consumers add `typescript` 7.0.2 and `@typescript/typescript6` 6.0.2 as dev dependencies and type-check with `node shared/scripts/vue-tsc.mjs --noEmit`. The runtime, preset and palette are unchanged.

Version 3.0.2 restores the 4.x text metrics: the preset sets `typography.lineHeight: inherit` (aura-compat's `normal` reached whole views through Tabs and shrank fields from 38px to 35px), and `base.css` keeps the button label weight on `.p-button-label` instead of the `.p-button` root, so slot content is not bold.

Version 3.0.1 works around a PrimeVue 5.0.5 Tabs bug: `Tab` reads `$refs.tabs` from `TabList`, which 5.x renamed to `content`, so Home, End and arrow wrap-around threw. `installOrcaUI()` registers a global mixin that aliases the ref. Remove it once PrimeVue fixes `Tab`.

Version 3.0.0 moves to **PrimeVue 5.0.5 + @primeuix/themes 3.1.1** with the `aura-compat` base (Aura with the 4.x sizes, so layouts keep their measures). PrimeVue 5 is no longer MIT: it is under the PrimeUI License and needs a key. The Community License key lives in `src/license.ts` and is passed by `primeVueOptions()`; it is verified offline. It expires on 2027-11-13 (30 days grace): renew it, release a new foundation version and rebuild all six plugins, or every plugin page shows PrimeVue's "Invalid PrimeUI License" banner. PrimeVue 5 colours use CSS `light-dark()` with `color-scheme`, which `applyOrcaTheme()` sets: hosts need WebKit 17.5+ (macOS), WebView2 (Windows) or WebKitGTK 2.44+ (Linux).

Version 2.0.3 updates the build tools only (Vite 8.3.8, @vitejs/plugin-vue 6.0.11); the runtime, preset and palette are unchanged.

Version 2.0.2 omits the locale option for English so PrimeVue retains its built-in labels. Passing an explicit undefined locale erased those defaults and broke Tabs. Consumers should use installOrcaUI directly instead of filtering this option locally.

Version 2.0.1 fixes focus-ring contrast for secondary/info/success/warn buttons and ensures reduced-motion preferences override runtime-injected component styles. Remove equivalent temporary per-app motion overrides after updating the shared snapshot.

All six plugin frontends use **Vue 3.5.45 + PrimeVue 5.0.5**, with the same custom preset on `@primeuix/themes/aura-compat` from **@primeuix/themes 3.1.1**. Vue is MIT; PrimeVue and PrimeUIX are under the PrimeUI License (Community tier); all three license texts are in `licenses/`. Documentation: https://primevue.org/vite/ and the PrimeVue 5.0.5 source. Bootstrap is not part of this foundation or an accepted implementation.

## Shared source and builds

The workspace root is not a Git repository. Keep a versioned identical snapshot of all files listed in `manifest.json`, plus that manifest, in each repository at `ui/shared/`. The authoritative working source lives here; vendored snapshots keep each plugin independently reproducible. Do not copy node_modules, gallery, evidence or dist. The `package.json` in the snapshot describes the release; consumers install the three pinned runtime dependencies into their own `ui/package.json` and retain their lockfile.

`node ui/shared/scripts/check.mjs` checks shared file hashes and exact palette contrast without npm dependencies. All six consumers must use the same manifest version and hashes. Changes to the preset go through one shared release, not individual patches in a consumer. Local domain layout is allowed; separate palettes/component styles are not. Shared components live in `src/components/` and are imported per component.

This source project's `npm ci --ignore-scripts && npm run build && npm run check` builds the offline reference gallery (`?screen=tokens|kit|kobra-dash|u1-dash|kobra-stock|u1-stock|kobra-files|u1-files|kobra-settings|spooler-spools|calc-quote|organizer-dock|embedder-main|notices`, `&state=`, `&theme=dark|light`, `&lang=en|pt-BR`) and the manifest. `node scripts/shots.mjs` screenshots every reference screen into `evidence-5.0.0/after/`, fails on overflow, clipped labels, console errors or a licence banner, and drives `OuiFileBrowser` through its selection, keyboard, drag and delete paths; `node scripts/sizes.mjs` prints the built size of each shared component. `scripts/verify-gallery.mjs` and `scripts/contact-sheet.mjs` are the 4.0.0 evidence tools, kept for the record and not updated for 5.0. Applications compile the shared TypeScript with their own Vue components using Vite and `vite-plugin-singlefile`, or an equivalent self-contained build already used by the plugin. No CDN, runtime npm, remote font, iframe or sibling-plugin dependency. Include licenses in the plugin distribution.

## Application integration

```ts
import { createApp } from 'vue';
import App from './App.vue';
import { installOrcaUI, applyOrcaTheme } from '../shared/src';
// in components: import { OuiAppBar, OuiPanel, OuiStatus } from '../shared/src/components';

document.body.classList.add('orca-ui');
applyOrcaTheme('light'); // use the resolved host theme; keep it synchronized
const app = createApp(App);
installOrcaUI(app, 'pt-BR', 'violet'); // the plugin's identity hue: its mark tile and the open tab's line
app.mount('#app');
```

PrimeVue uses Vue's Options API internally. **Keep `__VUE_OPTIONS_API__: true` in Vite** even when application components use `<script setup>`. Import only components actually used: `primevue/button`, `inputtext`, `inputnumber`, `select`, `checkbox`, `dialog`, `message`, `datatable`, `column`, `tabs`, `progressbar`, etc. No global all-component barrel, PrimeFlex, Tailwind or paid add-on is needed.

`applyOrcaTheme()` applies `.orca-dark` and family tokens to the document root. The plugin's host adapter owns detecting the supported host theme changes and calling it; do not infer a private Orca API. This covers teleported dialogs as well. Update the PrimeVue locale configuration when the app's language changes. The shared pt-BR strings cover common component labels, not all application text or all optional PrimeVue components: validate labels for each component used.

## Migration acceptance

The UI is genuinely Vue: SFC templates, reactive state, keyed lists, component handlers and lifecycle cleanup. Mounting Vue beside the old UI, injecting legacy HTML with `v-html`, or retaining the old imperative renderer as the main implementation does not satisfy the user's instruction. Migrate every user-facing surface: primary tabs, settings, setup dialogs, wizard and Organizer dock. Shared compiled applications can serve more than one capability via an explicit mode/initial-state payload.

Preserve Python services, protocol validation, existing message contracts where feasible, source/target generation, job identity, cancellation, single consumption owner and emergency routing. A UI migration is not permission to remove controls. Port behavioral tests from legacy fake-DOM harnesses to Vue/component or built-page tests before deleting obsolete renderer tests. Old code may only be removed once its callers and features are migrated.

Use the same bridge transport supplied by Orca. Keep CSP and permissions; Vue templates must be compiled ahead of time and must not need unsafe-eval. Test the actual single-file production artifact under its CSP, including runtime-injected PrimeVue styles and dialogs. Measure bundle changes; do not inflate a budget blindly or disable coverage gates to finish.

Every headless Chrome invocation includes `--use-mock-keychain --password-store=basic`.
