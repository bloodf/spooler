import { definePreset } from '@primeuix/themes';
import Aura from '@primeuix/themes/aura-compat';
import palette from './palette.json';

type Role = keyof typeof palette.light | 'primary' | 'primaryHover' | 'primarySoft' | 'onPrimary' | 'background' | 'surface' | 'raised' | 'inset' | 'border' | 'controlBorder';
// Colours are the --oui-* variables that applyOrcaTheme() writes, so one preset serves both themes and every accent.
const c = (role: Role) => `var(--oui-${role.replace(/[A-Z]/g, ch => '-' + ch.toLowerCase())})`;
const mix = (role: Role, percent: number) => `color-mix(in srgb, ${c(role)} ${percent}%, transparent)`;

// Aura derives every un-overridden component colour from this ramp, so it follows the family neutrals.
const ramp = {
  light: ['#ffffff', '#f6f7f9', '#f2f4f7', '#dfe3e9', '#c3cad3', '#9aa5b3', '#7b8898', '#515d6c', '#36404c', '#252c36', '#1a2029', '#11151b'],
  dark: ['#ffffff', '#e9edf2', '#cfd6de', '#a6b0bd', '#8792a0', '#717d8c', '#4a535f', '#363d47', '#2d333c', '#242930', '#1a1e24', '#0e1114'],
};
const surface = Object.fromEntries([0, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 950]
  .map((step, i) => [step, `light-dark(${ramp.light[i]}, ${ramp.dark[i]})`]));

const filled = (bg: Role, fg: Role, hover: Role) => ({
  background: c(bg), borderColor: c(bg), color: c(fg),
  hoverBackground: c(hover), hoverBorderColor: c(hover), hoverColor: c(fg),
  activeBackground: c(hover), activeBorderColor: c(hover), activeColor: c(fg),
  focusRing: { color: c('primary'), shadow: 'none' },
});
// Status-coloured buttons are tinted, never solid: only the primary and the destructive action are solid.
const tinted = (fg: Role, bg: Role) => ({
  background: c(bg), borderColor: mix(fg, 32), color: c(fg),
  hoverBackground: c(bg), hoverBorderColor: c(fg), hoverColor: c(fg),
  activeBackground: c(bg), activeBorderColor: c(fg), activeColor: c(fg),
  focusRing: { color: c('primary'), shadow: 'none' },
});
// The everyday button: tinted with the plugin's accent, so it belongs to the page without competing with the solid primary.
const tonal = {
  background: c('primarySoft'), borderColor: mix('primary', 28), color: c('primary'),
  hoverBackground: c('primarySoft'), hoverBorderColor: c('primary'), hoverColor: c('primary'),
  activeBackground: c('primarySoft'), activeBorderColor: c('primary'), activeColor: c('primary'),
  focusRing: { color: c('primary'), shadow: 'none' },
};
const status = (fg: Role, bg: Role) => ({
  background: c(bg), borderColor: mix(fg, 32), color: c('text'), shadow: 'none',
  closeButton: { hoverBackground: mix(fg, 16), focusRing: { color: c('primary'), shadow: 'none' } },
  outlined: { color: c(fg), borderColor: c(fg) }, simple: { color: c(fg) },
});
const overlayShadow = 'light-dark(0 12px 32px rgb(16 24 40 / .16), 0 12px 32px rgb(0 0 0 / .5))';

export const OrcaPreset = definePreset(Aura, {
  semantic: {
    // aura-compat sets line-height: normal on every .p-component; PrimeVue 5 applies it through Tabs to whole views.
    typography: { fontFamily: 'inherit', lineHeight: 'inherit', fontSize: '13px' },
    transitionDuration: '0.12s',
    disabledOpacity: '0.45',
    iconSize: '14px',
    focusRing: { width: '2px', style: 'solid', color: c('primary'), offset: '2px', shadow: 'none' },
    surface,
    primary: { color: c('primary'), contrastColor: c('onPrimary'), hoverColor: c('primaryHover'), activeColor: c('primaryHover') },
    highlight: { background: c('primarySoft'), focusBackground: c('primarySoft'), color: c('text'), focusColor: c('text') },
    text: { color: c('text'), hoverColor: c('text'), mutedColor: c('muted'), hoverMutedColor: c('text') },
    content: { borderRadius: '8px', background: c('surface'), hoverBackground: c('raised'), borderColor: c('border'), color: c('text'), hoverColor: c('text') },
    formField: {
      paddingX: '10px', paddingY: '6px', borderRadius: '6px', fontSize: '13px',
      sm: { fontSize: '12px', paddingX: '8px', paddingY: '3px' },
      focusRing: { width: '2px', style: 'solid', color: c('primary'), offset: '1px', shadow: 'none' },
      background: c('inset'), disabledBackground: c('raised'), filledBackground: c('inset'),
      filledHoverBackground: c('inset'), filledFocusBackground: c('inset'),
      borderColor: c('controlBorder'), hoverBorderColor: c('text'), focusBorderColor: c('primary'),
      invalidBorderColor: c('danger'), color: c('text'), disabledColor: c('muted'),
      placeholderColor: c('muted'), invalidPlaceholderColor: c('danger'), iconColor: c('muted'), shadow: 'none',
    },
    list: { padding: '4px', gap: '1px', option: { padding: '6px 8px', borderRadius: '4px', focusBackground: c('border'),
      selectedBackground: c('primarySoft'), selectedFocusBackground: c('primarySoft'), color: c('text'), focusColor: c('text'),
      selectedColor: c('text'), selectedFocusColor: c('text') } },
    overlay: {
      select: { borderRadius: '8px', shadow: overlayShadow, background: c('raised'), borderColor: c('border'), color: c('text') },
      popover: { borderRadius: '8px', padding: '12px', shadow: overlayShadow, background: c('raised'), borderColor: c('border'), color: c('text') },
      modal: { borderRadius: '12px', padding: '20px', shadow: overlayShadow, background: c('surface'), borderColor: c('border'), color: c('text') },
    },
    mask: { background: 'light-dark(rgb(16 24 40 / .36), rgb(0 0 0 / .6))', color: c('text') },
  },
  components: {
    button: {
      root: { borderRadius: '6px', gap: '6px', paddingX: '12px', paddingY: '6px', iconOnlyWidth: '32px', fontSize: '13px',
        sm: { fontSize: '12px', paddingX: '8px', paddingY: '3px', iconOnlyWidth: '26px' },
        label: { fontWeight: '600' },
        primary: filled('primary', 'onPrimary', 'primaryHover'), danger: filled('dangerSolid', 'onDangerSolid', 'dangerSolidHover'),
        secondary: tonal, info: tinted('info', 'infoBg'), success: tinted('success', 'successBg'), warn: tinted('warning', 'warningBg') },
      outlined: {
        primary: { color: c('primary'), borderColor: mix('primary', 56), hoverBackground: c('primarySoft'), activeBackground: c('primarySoft') },
        danger: { color: c('danger'), borderColor: mix('danger', 56), hoverBackground: c('dangerBg'), activeBackground: c('dangerBg') },
        secondary: { color: c('text'), borderColor: c('controlBorder'), hoverBackground: c('raised'), activeBackground: c('raised') },
      },
      text: {
        primary: { color: c('primary'), hoverBackground: c('primarySoft'), activeBackground: c('primarySoft') },
        secondary: { color: c('primary'), hoverBackground: c('primarySoft'), activeBackground: c('primarySoft') },
        danger: { color: c('danger'), hoverBackground: c('dangerBg'), activeBackground: c('dangerBg') },
      },
    },
    message: { root: { borderWidth: '1px', borderRadius: '6px' }, content: { padding: '6px 10px', gap: '8px' },
      text: { fontSize: '13px', fontWeight: '500' }, icon: { size: '14px' },
      error: status('danger', 'dangerBg'), warn: status('warning', 'warningBg'), success: status('success', 'successBg'),
      info: status('info', 'infoBg'), secondary: status('muted', 'raised') },
    dialog: { root: { borderRadius: '12px' }, header: { padding: '16px 20px 12px' }, title: { fontSize: '15px', fontWeight: '600' },
      content: { padding: '0 20px 20px' }, footer: { padding: '0 20px 16px', gap: '8px' } },
    datatable: {
      root: { borderColor: c('border') },
      headerCell: { background: c('raised'), hoverBackground: c('raised'), selectedBackground: c('raised'), color: c('muted'),
        hoverColor: c('text'), selectedColor: c('text'), padding: '8px 12px', sm: { padding: '6px 12px' }, gap: '4px' },
      columnTitle: { fontWeight: '600', fontSize: '11px' },
      row: { background: 'transparent', hoverBackground: c('raised'), selectedBackground: c('primarySoft'), selectedColor: c('text') },
      bodyCell: { padding: '8px 12px', sm: { padding: '5px 12px' }, selectedBorderColor: c('border'), fontSize: '13px', fontWeight: 'inherit' },
      sortIcon: { size: '12px' },
    },
    tabs: { tablist: { background: 'transparent', borderWidth: '0' },
      tab: { padding: '0 12px', fontWeight: '600', borderWidth: '0', margin: '0', gap: '6px', color: c('muted'), hoverColor: c('text'), activeColor: c('text') },
      tabpanel: { background: 'transparent', padding: '0' }, activeBar: { height: '2px', background: c('primary') },
      navButton: { background: c('surface'), shadow: 'none' } },
    progressbar: { root: { background: c('border'), borderRadius: '4px', height: '8px' } },
    toggleswitch: { root: { width: '32px', height: '18px', background: c('controlBorder'), hoverBackground: c('muted'), shadow: 'none' },
      handle: { size: '12px', background: c('surface'), hoverBackground: c('surface'), checkedBackground: c('onPrimary'), checkedHoverBackground: c('onPrimary') } },
    checkbox: { root: { width: '16px', height: '16px', borderRadius: '4px' }, icon: { size: '11px' } },
    togglebutton: { root: { padding: '2px', borderRadius: '6px', fontWeight: '600', background: c('inset'), checkedBackground: c('inset'),
      hoverBackground: c('inset'), borderColor: c('border'), checkedBorderColor: c('border'), color: c('muted'), hoverColor: c('text'), checkedColor: c('onPrimary') },
      content: { padding: '3px 10px', borderRadius: '4px', checkedBackground: c('primary'), checkedShadow: 'none' } },
    select: { dropdown: { width: '28px' } },
    inputnumber: { button: { width: '26px' } },
    tooltip: { root: { background: c('text'), color: c('background'), fontSize: '12px', padding: '4px 8px' } },
  },
});

export { palette };
