# Orca UI foundation 4.0.1 — Vue and PrimeVue

Version 4.0.1 adds three things the Spooler migration needed, and changes nothing that 4.0.0 pages rely on: `OuiSlot` takes an `#amount` slot that replaces its weight line and level bar (percent-only trays, hidden weight or bar, other units), and its built-in line formats numbers in the page language instead of the browser's; an `OuiTab` can carry `attrs` (test hooks on the tab button) and `attention` (a dot with an accessible name). To update from 4.0.0, replace `ui/shared/` with the 4.0.1 snapshot and rebuild.

Version 4.0.0 is a redesign, not a patch: a colour system (one accent per plugin, seven hues, state colours), one icon set (`src/icons.ts`: 86 Lucide icons and 11 drawn for the family), a real type scale, denser controls, and for the first time shared Vue components (`src/components/`) for the structures the six plugin pages have in common. `DESIGN.md` is the specification. Runtime dependencies are unchanged (Vue 3.5.45, PrimeVue 5.0.5, @primeuix/themes 3.1.1); the icons are copied in at build time from the dev dependency `lucide-static` 1.73.0 (ISC, `licenses/Lucide.txt`), so consumers install nothing new. The typeface is Manrope, embedded as a 21,476 B subset (`src/fonts/Manrope.woff2`, SIL OFL 1.1, `licenses/Manrope.txt`). No image was added. Reference screens for all six plugins, with before/after pairs, are in `evidence-4.0.0/index.html` (MOCK data).

## Migrating a plugin from 3.1.0

`MIGRATION-4.0.md` is the full procedure for a roll-out (vendoring, accent, policy, icons, the component mapping per plugin, what must not change, per-repository risks, known limits). In short:

1. Replace `ui/shared/` with the 4.0.0 snapshot (every file in `manifest.json`, now including `src/components/*`) and run `node shared/scripts/check.mjs`.
2. Nothing else is required for the page to build: `installOrcaUI`, `applyOrcaTheme`, `primeVueOptions`, `OrcaPreset`, `UI_VERSION` and the licence handling are unchanged, and every 3.1.0 colour variable still exists (`--oui-background`, `--oui-surface`, `--oui-text`, `--oui-muted`, `--oui-border`, `--oui-control-border`, `--oui-primary`, `--oui-on-primary`, the three state pairs). Measured on a minimal page, this step alone adds 41.8 kB (26.1 kB gzip), of which 28.7 kB is the embedded font. The preset now reads the `--oui-*` variables, so `applyOrcaTheme()` has to run before the app mounts, as every plugin already does. Pass the plugin's accent as the third argument of `installOrcaUI` (Kobra Control `violet`, U1 Control `cobalt`, Spooler `magenta`, Print Calculator `lime`, Organizer `sky`, Embedder `teal`); without it the accent is teal, as in 3.1.0.
3. What changes without touching your code: body text is 13 px (was 14), controls are 32 px high (were 38) and small ones 26, panels have an 8 px radius, the default `secondary` button is a quiet raised key instead of an outlined one, status-coloured buttons are tinted, and solid `danger` is a saturated red in both themes. Re-take every screenshot and re-check any test that asserts a pixel size, a radius or a computed colour.
4. Removed: `--oui-danger-hover` and `--oui-on-danger` (use `--oui-danger-solid-hover`, `--oui-on-danger-solid`); the classes `.oui-header` (use `OuiAppBar`), `.oui-result` (`OuiReadout`), `.oui-section` and `.oui-empty` (`OuiEmpty`). `.oui-panel` and `.oui-toolbar` are now the classes of `OuiPanel` and `OuiToolbar`: use the components. `.oui-number` still works; `.oui-num` is the new name. `.oui-meta`, `.oui-muted`, `.oui-field`, `.oui-table-wrap` and `.oui-error-detail` are unchanged.
5. New variables: `--oui-raised`, `--oui-inset`, `--oui-primary-soft`, `--oui-band`, `--oui-on-band`, `--oui-on-state`, `--oui-info`, `--oui-info-bg`, `--oui-danger-solid` (+ hover, on), `--oui-tool1`…`4`, `--oui-on-tool`, and the seven hues `teal`, `sky`, `cobalt`, `violet`, `magenta`, `lime`, `orange`, each with `-soft`, `-hover` and `--oui-on-…`. The surface variables now differ per accent.
6. Then move the page onto the shared components and delete the local CSS they replace. Import them from `../shared/src/components` (they are not re-exported from `../shared/src`, so unused ones cost nothing): all twenty-one together add 48 kB (13 kB gzip). Import icons by name from `../shared/src/icons` (about 0.2 kB each) and delete the plugin's own icon files and its icon loader, keeping only the identity mark. The vector `OuiSpool` replaces the fifteen spool WebP layers that Kobra Control, U1 Control and Spooler each embed (72 kB of files, about 97 kB once inlined).
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

This source project's `npm ci --ignore-scripts && npm run build && npm run check` builds the offline reference gallery (`?screen=kit|kobra-dash|kobra-settings|u1-dash|spooler-stock|calc-quote|organizer-dock|embedder-main`, `&state=`, `&theme=dark|light`, `&lang=en|pt-BR`) and the manifest. `node scripts/shots.mjs` screenshots every reference screen and fails on overflow, clipped labels, console errors or a licence banner; `node scripts/verify-gallery.mjs` checks focus rings, reduced motion and the dialog flow; `node scripts/contact-sheet.mjs` rebuilds `evidence-4.0.0/index.html`. Applications compile the shared TypeScript with their own Vue components using Vite and `vite-plugin-singlefile`, or an equivalent self-contained build already used by the plugin. No CDN, runtime npm, remote font, iframe or sibling-plugin dependency. Include licenses in the plugin distribution.

## Application integration

```ts
import { createApp } from 'vue';
import App from './App.vue';
import { installOrcaUI, applyOrcaTheme } from '../shared/src';
// in components: import { OuiAppBar, OuiPanel, OuiStatus } from '../shared/src/components';

document.body.classList.add('orca-ui');
applyOrcaTheme('light'); // use the resolved host theme; keep it synchronized
const app = createApp(App);
installOrcaUI(app, 'pt-BR');
app.mount('#app');
```

PrimeVue uses Vue's Options API internally. **Keep `__VUE_OPTIONS_API__: true` in Vite** even when application components use `<script setup>`. Import only components actually used: `primevue/button`, `inputtext`, `inputnumber`, `select`, `checkbox`, `dialog`, `message`, `datatable`, `column`, `tabs`, `progressbar`, etc. No global all-component barrel, PrimeFlex, Tailwind or paid add-on is needed.

`applyOrcaTheme()` applies `.orca-dark` and family tokens to the document root. The plugin's host adapter owns detecting the supported host theme changes and calling it; do not infer a private Orca API. This covers teleported dialogs as well. Update the PrimeVue locale configuration when the app's language changes. The shared pt-BR strings cover common component labels, not all application text or all optional PrimeVue components: validate labels for each component used.

## Migration acceptance

The UI is genuinely Vue: SFC templates, reactive state, keyed lists, component handlers and lifecycle cleanup. Mounting Vue beside the old UI, injecting legacy HTML with `v-html`, or retaining the old imperative renderer as the main implementation does not satisfy the user's instruction. Migrate every user-facing surface: primary tabs, settings, setup dialogs, wizard and Organizer dock. Shared compiled applications can serve more than one capability via an explicit mode/initial-state payload.

Preserve Python services, protocol validation, existing message contracts where feasible, source/target generation, job identity, cancellation, single consumption owner and emergency routing. A UI migration is not permission to remove controls. Port behavioral tests from legacy fake-DOM harnesses to Vue/component or built-page tests before deleting obsolete renderer tests. Old code may only be removed once its callers and features are migrated.

Use the same bridge transport supplied by Orca. Keep CSP and permissions; Vue templates must be compiled ahead of time and must not need unsafe-eval. Test the actual single-file production artifact under its CSP, including runtime-injected PrimeVue styles and dialogs. Measure bundle changes; do not inflate a budget blindly or disable coverage gates to finish.

Every headless Chrome invocation includes `--use-mock-keychain --password-store=basic`.
