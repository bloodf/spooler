import type { App } from 'vue';
import PrimeVue, { type PrimeVueConfiguration } from 'primevue/config';
import { OrcaPreset, palette } from './theme';
import './base.css';

export type OrcaLocale = 'en' | 'pt-BR';
export type OrcaTheme = 'light' | 'dark';
export const UI_VERSION = '2.0.2';
export { OrcaPreset };

export function primeVueOptions(locale: OrcaLocale): PrimeVueConfiguration {
  return {
    ripple: false,
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

export function installOrcaUI(app: App, locale: OrcaLocale): void {
  app.use(PrimeVue, primeVueOptions(locale));
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
