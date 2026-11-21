import { createApp, watch } from 'vue';
import { installOrcaUI } from '@orca-plugins/ui-foundation/src';
import { boot } from './core/boot';
import { locale, setHostLanguage } from './core/i18n';
import { primeLabels } from './core/prime-locale';
import { followHostTheme } from './core/theme';
import { primeVueOptions } from '@orca-plugins/ui-foundation/src';
import App from './App.vue';

document.body.classList.add('orca-ui');
setHostLanguage(boot.lang);
followHostTheme();
const app = createApp(App);
installOrcaUI(app, 'en', 'magenta');
// An error before or during mount reaches scripts/page_loader.js, which shows it instead of a blank page.
app.config.errorHandler = err => {
  console.error(err);
  (window as { __spoolerError?: (e: unknown) => void }).__spoolerError?.(err);
};
// PrimeVue's own labels (dialog close, select filter…) follow the page language too.
const prime = app.config.globalProperties.$primevue;
const english = { ...prime.config.locale };
watch(locale, l => {
  document.documentElement.lang = l;
  const own = l === 'pt-BR' ? primeVueOptions(l).locale : primeLabels[l];
  prime.config.locale = { ...english, ...(own ?? {}), aria: { ...english.aria, ...((own?.aria as object | undefined) ?? {}) } } as NonNullable<typeof prime.config.locale>;
}, { immediate: true });
app.mount('#app');
document.getElementById('spooler-failed')?.remove();   // an error before the app ran, which started after all
