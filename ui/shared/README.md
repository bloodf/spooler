# Orca UI foundation 3.1.0 — Vue and PrimeVue

Version 3.1.0 moves the build tools to TypeScript 7.0.2 (the native compiler). TypeScript 7 has no JS API and vue-tsc 3.3 needs one, so `scripts/vue-tsc.mjs` runs vue-tsc on the TypeScript 6 compiler from Microsoft's `@typescript/typescript6` package. Consumers add `typescript` 7.0.2 and `@typescript/typescript6` 6.0.2 as dev dependencies and type-check with `node shared/scripts/vue-tsc.mjs --noEmit`. The runtime, preset and palette are unchanged.

Version 3.0.2 restores the 4.x text metrics: the preset sets `typography.lineHeight: inherit` (aura-compat's `normal` reached whole views through Tabs and shrank fields from 38px to 35px), and `base.css` keeps the button label weight on `.p-button-label` instead of the `.p-button` root, so slot content is not bold.

Version 3.0.1 works around a PrimeVue 5.0.5 Tabs bug: `Tab` reads `$refs.tabs` from `TabList`, which 5.x renamed to `content`, so Home, End and arrow wrap-around threw. `installOrcaUI()` registers a global mixin that aliases the ref. Remove it once PrimeVue fixes `Tab`.

Version 3.0.0 moves to **PrimeVue 5.0.5 + @primeuix/themes 3.1.1** with the `aura-compat` base (Aura with the 4.x sizes, so layouts keep their measures). PrimeVue 5 is no longer MIT: it is under the PrimeUI License and needs a key. The Community License key lives in `src/license.ts` and is passed by `primeVueOptions()`; it is verified offline. It expires on 2027-11-13 (30 days grace): renew it, release a new foundation version and rebuild all four plugins, or every plugin page shows PrimeVue's "Invalid PrimeUI License" banner. PrimeVue 5 colours use CSS `light-dark()` with `color-scheme`, which `applyOrcaTheme()` sets: hosts need WebKit 17.5+ (macOS), WebView2 (Windows) or WebKitGTK 2.44+ (Linux).

Version 2.0.3 updates the build tools only (Vite 8.3.8, @vitejs/plugin-vue 6.0.11); the runtime, preset and palette are unchanged.

Version 2.0.2 omits the locale option for English so PrimeVue retains its built-in labels. Passing an explicit undefined locale erased those defaults and broke Tabs. Consumers should use installOrcaUI directly instead of filtering this option locally.

Version 2.0.1 fixes focus-ring contrast for secondary/info/success/warn buttons and ensures reduced-motion preferences override runtime-injected component styles. Remove equivalent temporary per-app motion overrides after updating the shared snapshot.

All four plugin frontends use **Vue 3.5.45 + PrimeVue 5.0.5**, with the same custom preset on `@primeuix/themes/aura-compat` from **@primeuix/themes 3.1.1**. Vue is MIT; PrimeVue and PrimeUIX are under the PrimeUI License (Community tier); all three license texts are in `licenses/`. Documentation: https://primevue.org/vite/ and the PrimeVue 5.0.5 source. Bootstrap is not part of this foundation or an accepted implementation.

## Shared source and builds

The workspace root is not a Git repository. Keep a versioned identical snapshot of all files listed in `manifest.json`, plus that manifest, in each repository at `ui/shared/`. The authoritative working source lives here; vendored snapshots keep each plugin independently reproducible. Do not copy node_modules, gallery, evidence or dist. The `package.json` in the snapshot describes the release; consumers install the three pinned runtime dependencies into their own `ui/package.json` and retain their lockfile.

`node ui/shared/scripts/check.mjs` checks shared file hashes and exact palette contrast without npm dependencies. All four consumers must use the same manifest version and hashes. Changes to the preset go through one shared release, not individual patches in a consumer. Local domain layout is allowed; separate palettes/component styles are not.

This source project's `npm ci --ignore-scripts && npm run build && npm run check` builds an offline reference gallery and its manifest. Applications compile the shared TypeScript with their own Vue components using Vite and `vite-plugin-singlefile`, or an equivalent self-contained build already used by the plugin. No CDN, runtime npm, remote font, iframe or sibling-plugin dependency. Include licenses in the plugin distribution.

## Application integration

```ts
import { createApp } from 'vue';
import App from './App.vue';
import { installOrcaUI, applyOrcaTheme } from '../shared/src';

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
