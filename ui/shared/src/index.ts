import type { App } from 'vue';
import PrimeVue, { type PrimeVueConfiguration } from 'primevue/config';
import { OrcaPreset, palette } from './theme';
import { PRIMEUI_LICENSE } from './license';
import './base.css';

export type OrcaLocale = 'en' | 'pt-BR';
export type OrcaTheme = 'light' | 'dark';
export const UI_VERSION = '5.0.0';
export { PRIMEUI_LICENSE_EXPIRES } from './license';
// Shared components are a separate entry (./components) so a page only pays for the ones it imports.
export { OrcaPreset, palette };

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

export function installOrcaUI(app: App, locale: OrcaLocale, pluginAccent?: OrcaAccent): void {
  if (pluginAccent) setOrcaAccent(pluginAccent);
  app.use(PrimeVue, primeVueOptions(locale));
  app.mixin(tabListRefsAlias);
}

/** The family's hues. Each plugin takes one as its identity accent (its mark, the active tab); all seven are available as icon and chip colours. */
export type OrcaAccent = 'teal' | 'sky' | 'cobalt' | 'violet' | 'magenta' | 'lime' | 'orange';
let accent: OrcaAccent = 'teal';

/** Sets the plugin's identity accent (once, at start-up) and re-applies the current theme if there is one. */
export function setOrcaAccent(next: OrcaAccent, root: HTMLElement = document.documentElement): void {
  accent = next;
  const theme = root.dataset.orcaUiTheme;
  if (theme === 'light' || theme === 'dark') applyOrcaTheme(theme, root);
}

// The host adapter owns detecting theme changes; this function applies its resolved mode.
// Every palette role becomes --oui-<role>. Surfaces are OrcaSlicer's neutral greys and the primary action is OrcaSlicer's
// teal, the same in every plugin. The plugin's accent only supplies --oui-accent (lines and text), --oui-accent-soft,
// --oui-on-accent and --oui-accent-solid (the mark tile, with --oui-on-solid on it). The preset reads these variables.
export function applyOrcaTheme(theme: OrcaTheme, root: HTMLElement = document.documentElement): void {
  root.classList.toggle('orca-dark', theme === 'dark');
  root.dataset.orcaUiTheme = theme;
  root.dataset.orcaUiAccent = accent;
  root.style.colorScheme = theme;
  const roles: Record<string, string> = palette[theme];
  const all: Record<string, string> = { ...roles, accent: roles[accent], accentSoft: roles[accent + 'Soft'], accentSolid: roles[accent + 'Solid'],
    onAccent: roles['on' + accent[0].toUpperCase() + accent.slice(1)] };
  for (const [name, color] of Object.entries(all)) root.style.setProperty(`--oui-${name.replace(/[A-Z]/g, c => '-' + c.toLowerCase())}`, color);
}
