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
// PrimeVue's own labels (dialog close, select filter…) follow the page language too.
const prime = app.config.globalProperties.$primevue;
const english = { ...prime.config.locale };
watch(locale, l => {
  document.documentElement.lang = l;
  const own = l === 'pt-BR' ? primeVueOptions(l).locale : primeLabels[l];
  prime.config.locale = { ...english, ...(own ?? {}), aria: { ...english.aria, ...((own?.aria as object | undefined) ?? {}) } } as NonNullable<typeof prime.config.locale>;
}, { immediate: true });
app.mount('#app');
