import { definePreset } from '@primeuix/themes';
import Aura from '@primeuix/themes/aura-compat';
import palette from './palette.json';

type Role = keyof typeof palette.light;
// Colours are the --oui-* variables that applyOrcaTheme() writes, so one preset serves both themes.
const c = (role: Role) => `var(--oui-${role.replace(/[A-Z]/g, ch => '-' + ch.toLowerCase())})`;
const mix = (role: Role, percent: number) => `color-mix(in srgb, ${c(role)} ${percent}%, transparent)`;

// Aura derives every un-overridden component colour from this ramp: OrcaSlicer's own greys (StateColor.cpp), light and dark.
const ramp = {
  light: ['#ffffff', '#f8f8f8', '#f4f4f4', '#eeeeee', '#dbdbdb', '#acacac', '#7c8282', '#5c5f61', '#363636', '#2c2c2e', '#262e30', '#1a1a1c'],
  dark: ['#ffffff', '#efeff0', '#e5e5e6', '#b2b3b5', '#909090', '#818183', '#65656a', '#4a4a51', '#3e3e45', '#36363b', '#2d2d31', '#242428'],
};
const surface = Object.fromEntries([0, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 950]
  .map((step, i) => [step, `light-dark(${ramp.light[i]}, ${ramp.dark[i]})`]));

const filled = (bg: Role, fg: Role, hover: Role) => ({
  background: c(bg), borderColor: c(bg), color: c(fg),
  hoverBackground: c(hover), hoverBorderColor: c(hover), hoverColor: c(fg),
  activeBackground: c(hover), activeBorderColor: c(hover), activeColor: c(fg),
  focusRing: { color: c('primaryMark'), shadow: 'none' },
});
// Status-coloured buttons are tinted, never solid: only the primary and the destructive action are solid.
const tinted = (fg: Role, bg: Role) => ({
  background: c(bg), borderColor: mix(fg, 32), color: c(fg),
  hoverBackground: c(bg), hoverBorderColor: c(fg), hoverColor: c(fg),
  activeBackground: c(bg), activeBorderColor: c(fg), activeColor: c(fg),
  focusRing: { color: c('primaryMark'), shadow: 'none' },
});
// The everyday button is OrcaSlicer's regular button: a neutral grey fill with the text colour.
const neutral = {
  background: c('control'), borderColor: c('control'), color: c('text'),
  hoverBackground: c('controlHover'), hoverBorderColor: c('controlHover'), hoverColor: c('text'),
  activeBackground: c('controlHover'), activeBorderColor: c('controlHover'), activeColor: c('text'),
  focusRing: { color: c('primaryMark'), shadow: 'none' },
};
const status = (fg: Role, bg: Role) => ({
  background: c(bg), borderColor: mix(fg, 32), color: c('text'), shadow: 'none',
  closeButton: { hoverBackground: mix(fg, 16), focusRing: { color: c('primaryMark'), shadow: 'none' } },
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
    focusRing: { width: '2px', style: 'solid', color: c('primaryMark'), offset: '2px', shadow: 'none' },
    surface,
    primary: { color: c('primary'), contrastColor: c('onPrimary'), hoverColor: c('primaryHover'), activeColor: c('primaryHover') },
    highlight: { background: c('primarySoft'), focusBackground: c('primarySoft'), color: c('text'), focusColor: c('text') },
    text: { color: c('text'), hoverColor: c('text'), mutedColor: c('muted'), hoverMutedColor: c('text') },
    content: { borderRadius: '6px', background: c('surface'), hoverBackground: c('raised'), borderColor: c('border'), color: c('text'), hoverColor: c('text') },
    formField: {
      paddingX: '10px', paddingY: '6px', borderRadius: '4px', fontSize: '13px',
      sm: { fontSize: '12px', paddingX: '8px', paddingY: '3px' },
      focusRing: { width: '2px', style: 'solid', color: c('primaryMark'), offset: '1px', shadow: 'none' },
      // OrcaSlicer's field: the window colour inside a border that turns teal on hover and focus.
      background: c('surface'), disabledBackground: c('raised'), filledBackground: c('surface'),
      filledHoverBackground: c('surface'), filledFocusBackground: c('surface'),
      borderColor: c('controlBorder'), hoverBorderColor: c('primaryMark'), focusBorderColor: c('primaryMark'),
      invalidBorderColor: c('danger'), color: c('text'), disabledColor: c('muted'),
      placeholderColor: c('muted'), invalidPlaceholderColor: c('danger'), iconColor: c('muted'), shadow: 'none',
    },
    list: { padding: '4px', gap: '1px', option: { padding: '6px 8px', borderRadius: '4px', focusBackground: c('control'),
      selectedBackground: c('primarySoft'), selectedFocusBackground: c('primarySoft'), color: c('text'), focusColor: c('text'),
      selectedColor: c('text'), selectedFocusColor: c('text') } },
    overlay: {
      select: { borderRadius: '6px', shadow: overlayShadow, background: c('surface'), borderColor: c('border'), color: c('text') },
      popover: { borderRadius: '6px', padding: '12px', shadow: overlayShadow, background: c('surface'), borderColor: c('border'), color: c('text') },
      modal: { borderRadius: '8px', padding: '20px', shadow: overlayShadow, background: c('surface'), borderColor: c('border'), color: c('text') },
    },
    mask: { background: 'light-dark(rgb(16 24 40 / .36), rgb(0 0 0 / .6))', color: c('text') },
  },
  components: {
    button: {
      root: { borderRadius: '4px', gap: '6px', paddingX: '12px', paddingY: '6px', iconOnlyWidth: '32px', fontSize: '13px',
        sm: { fontSize: '12px', paddingX: '8px', paddingY: '3px', iconOnlyWidth: '26px' },
        label: { fontWeight: '600' },
        primary: filled('primary', 'onPrimary', 'primaryHover'), danger: filled('dangerSolid', 'onDangerSolid', 'dangerSolidHover'),
        secondary: neutral, info: tinted('info', 'infoBg'), success: tinted('success', 'successBg'), warn: tinted('warning', 'warningBg') },
      outlined: {
        primary: { color: c('primaryText'), borderColor: mix('primaryText', 56), hoverBackground: c('primarySoft'), activeBackground: c('primarySoft') },
        danger: { color: c('danger'), borderColor: mix('danger', 56), hoverBackground: c('dangerBg'), activeBackground: c('dangerBg') },
        secondary: { color: c('text'), borderColor: c('controlBorder'), hoverBackground: c('raised'), activeBackground: c('raised') },
      },
      text: {
        primary: { color: c('primaryText'), hoverBackground: c('primarySoft'), activeBackground: c('primarySoft') },
        secondary: { color: c('text'), hoverBackground: c('control'), activeBackground: c('controlHover') },
        danger: { color: c('danger'), hoverBackground: c('dangerBg'), activeBackground: c('dangerBg') },
      },
    },
    message: { root: { borderWidth: '1px', borderRadius: '4px' }, content: { padding: '6px 10px', gap: '8px' },
      text: { fontSize: '13px', fontWeight: '500' }, icon: { size: '14px' },
      error: status('danger', 'dangerBg'), warn: status('warning', 'warningBg'), success: status('success', 'successBg'),
      info: status('info', 'infoBg'), secondary: status('muted', 'raised') },
    dialog: { root: { borderRadius: '8px' }, header: { padding: '16px 20px 12px' }, title: { fontSize: '15px', fontWeight: '600' },
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
      tabpanel: { background: 'transparent', padding: '0' }, activeBar: { height: '2px', background: c('primaryMark') },
      navButton: { background: c('surface'), shadow: 'none' } },
    progressbar: { root: { background: c('border'), borderRadius: '4px', height: '8px' }, value: { background: c('primaryMark') } },
    toggleswitch: { root: { width: '32px', height: '18px', background: c('controlBorder'), hoverBackground: c('muted'), shadow: 'none',
        checkedBackground: c('primaryMark'), checkedHoverBackground: c('primaryMark') },
      handle: { size: '12px', background: c('surface'), hoverBackground: c('surface'), checkedBackground: c('onPrimary'), checkedHoverBackground: c('onPrimary') } },
    checkbox: { root: { width: '16px', height: '16px', borderRadius: '4px', checkedBackground: c('primaryMark'), checkedHoverBackground: c('primaryMark'),
        checkedBorderColor: c('primaryMark'), checkedHoverBorderColor: c('primaryMark'), checkedFocusBorderColor: c('primaryMark') }, icon: { size: '11px' } },
    togglebutton: { root: { padding: '2px', borderRadius: '4px', fontWeight: '600', background: c('inset'), checkedBackground: c('inset'),
      hoverBackground: c('inset'), borderColor: c('border'), checkedBorderColor: c('border'), color: c('muted'), hoverColor: c('text'), checkedColor: c('onPrimary') },
      content: { padding: '3px 10px', borderRadius: '3px', checkedBackground: c('primary'), checkedShadow: 'none' } },
    select: { dropdown: { width: '28px' } },
    inputnumber: { button: { width: '26px' } },
    tooltip: { root: { background: c('text'), color: c('background'), fontSize: '12px', padding: '4px 8px' } },
  },
});

export { palette };
