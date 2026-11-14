import type { App } from 'vue';
import PrimeVue, { type PrimeVueConfiguration } from 'primevue/config';
import { OrcaPreset, palette } from './theme';
import { PRIMEUI_LICENSE } from './license';
import './base.css';

export type OrcaLocale = 'en' | 'pt-BR';
export type OrcaTheme = 'light' | 'dark';
export const UI_VERSION = '3.0.2';
export { PRIMEUI_LICENSE_EXPIRES } from './license';
export { OrcaPreset };

export function primeVueOptions(locale: OrcaLocale): PrimeVueConfiguration {
  return {
    ripple: false,
    license: PRIMEUI_LICENSE,
    theme: { preset: OrcaPreset, options: { darkModeSelector: '.orca-dark', cssLayer: false } },
    ...(locale === 'pt-BR' ? { locale: {
      accept: 'Confirmar', reject: 'Voltar', choose: 'Selecionar', upload: 'Enviar', cancel: 'Cancelar',
      emptyMessage: 'Nenhum item encontrado', emptyFilterMessage: 'Nenhum resultado para estes filtros',
      emptySearchMessage: 'Nenhum resultado encontrado', searchMessage: '{0} resultados encontrados',
      selectionMessage: '{0} itens selecionados', emptySelectionMessage: 'Nenhum item selecionado',
      fileSizeTypes: ['B', 'KB', 'MB', 'GB', 'TB', 'PB', 'EB', 'ZB', 'YB'],
      dayNames: ['domingo', 'segunda-feira', 'terça-feira', 'quarta-feira', 'quinta-feira', 'sexta-feira', 'sábado'],
      dayNamesShort: ['dom', 'seg', 'ter', 'qua', 'qui', 'sex', 'sáb'],
      dayNamesMin: ['D', 'S', 'T', 'Q', 'Q', 'S', 'S'],
      monthNames: ['janeiro', 'fevereiro', 'março', 'abril', 'maio', 'junho', 'julho', 'agosto', 'setembro', 'outubro', 'novembro', 'dezembro'],
      monthNamesShort: ['jan', 'fev', 'mar', 'abr', 'mai', 'jun', 'jul', 'ago', 'set', 'out', 'nov', 'dez'],
      dateFormat: 'dd/mm/yy', firstDayOfWeek: 0,
      aria: { close: 'Fechar', previous: 'Anterior', next: 'Próximo',
        firstPageLabel: 'Primeira página', lastPageLabel: 'Última página',
        nextPageLabel: 'Próxima página', prevPageLabel: 'Página anterior',
        selectRow: 'Selecionar linha', unselectRow: 'Desmarcar linha' },
    } } : {}),
  };
}

// PrimeVue 5.0.5 bug: Tab's Home/End and arrow wrap-around read `$pcTabList.$refs.tabs`, but TabList 5
// renamed that element ref to `content`, so those keys throw. Alias it until PrimeVue fixes Tab.
const tabListRefsAlias = {
  mounted(this: { $options: { name?: string }; $refs: Record<string, unknown> }) {
    if (this.$options.name !== 'TabList' || 'tabs' in this.$refs) return;
    const refs = this.$refs;
    Object.defineProperty(refs, 'tabs', { configurable: true, enumerable: false, get: () => refs.content });
  },
};

export function installOrcaUI(app: App, locale: OrcaLocale): void {
  app.use(PrimeVue, primeVueOptions(locale));
  app.mixin(tabListRefsAlias);
}

// The host adapter owns detecting theme changes; this function applies its resolved mode.
export function applyOrcaTheme(theme: OrcaTheme, root: HTMLElement = document.documentElement): void {
  root.classList.toggle('orca-dark', theme === 'dark');
  root.dataset.orcaUiTheme = theme;
  root.style.colorScheme = theme;
  for (const [name, color] of Object.entries(palette[theme])) {
    root.style.setProperty(`--oui-${name.replace(/[A-Z]/g, c => '-' + c.toLowerCase())}`, color);
  }
}
