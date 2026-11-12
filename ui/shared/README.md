# Orca UI foundation 2.0.2 — Vue and PrimeVue

Version 2.0.2 omits the locale option for English so PrimeVue retains its built-in labels. Passing an explicit undefined locale erased those defaults and broke Tabs. Consumers should use installOrcaUI directly instead of filtering this option locally.

Version 2.0.1 fixes focus-ring contrast for secondary/info/success/warn buttons and ensures reduced-motion preferences override runtime-injected component styles. Remove equivalent temporary per-app motion overrides after updating the shared snapshot.

All four plugin frontends use **Vue 3.5.45 + PrimeVue 4.5.5**, with the same custom Aura preset from **@primeuix/themes 1.2.5**. These pinned packages have MIT licenses included in `licenses/`. Documentation: https://v4.primevue.org/vite/ and the PrimeVue 4.5.5 source. Do not follow PrimeVue 5 documentation for this release. Bootstrap is not part of this foundation or an accepted implementation.

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
