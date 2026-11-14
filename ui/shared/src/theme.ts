import { definePreset } from '@primeuix/themes';
import Aura from '@primeuix/themes/aura-compat';
import palette from './palette.json';

function scheme(p: typeof palette.light) {
  return {
    primary: { color: p.primary, contrastColor: p.onPrimary, hoverColor: p.primaryHover, activeColor: p.primaryHover },
    text: { color: p.text, hoverColor: p.text, mutedColor: p.muted, hoverMutedColor: p.muted },
    content: { background: p.surface, hoverBackground: p.background, borderColor: p.border, color: p.text, hoverColor: p.text },
    formField: {
      background: p.surface, disabledBackground: p.background, filledBackground: p.background,
      filledHoverBackground: p.background, filledFocusBackground: p.surface,
      borderColor: p.controlBorder, hoverBorderColor: p.primary, focusBorderColor: p.primary,
      invalidBorderColor: p.danger, color: p.text, disabledColor: p.muted,
      placeholderColor: p.muted, invalidPlaceholderColor: p.danger,
      iconColor: p.muted, shadow: 'none',
    },
    overlay: {
      select: { background: p.surface, borderColor: p.border, color: p.text },
      popover: { background: p.surface, borderColor: p.border, color: p.text },
      modal: { background: p.surface, borderColor: p.border, color: p.text },
    },
  };
}
function solid(background: string, color: string, hoverBackground = background, focusColor = background) {
  return { background, borderColor: background, color, hoverBackground,
    hoverBorderColor: hoverBackground, hoverColor: color, activeBackground: hoverBackground,
    activeBorderColor: hoverBackground, activeColor: color,
    focusRing: { color: focusColor, shadow: 'none' } };
}
function buttonScheme(p: typeof palette.light) {
  return {
    root: {
      primary: solid(p.primary, p.onPrimary, p.primaryHover),
      secondary: solid(p.background, p.text, p.surface, p.primary),
      danger: solid(p.danger, p.onDanger, p.dangerHover),
      success: solid(p.successBg, p.success, p.successBg, p.success),
      warn: solid(p.warningBg, p.warning, p.warningBg, p.warning),
      info: solid(p.background, p.text, p.background, p.primary),
    },
    outlined: {
      primary: { color: p.primary, borderColor: p.primary, hoverBackground: p.background, activeBackground: p.background },
      danger: { color: p.danger, borderColor: p.danger, hoverBackground: p.dangerBg, activeBackground: p.dangerBg },
      secondary: { color: p.text, borderColor: p.controlBorder, hoverBackground: p.background, activeBackground: p.background },
    },
    text: {
      primary: { color: p.primary, hoverBackground: p.background, activeBackground: p.background },
      secondary: { color: p.text, hoverBackground: p.background, activeBackground: p.background },
      danger: { color: p.danger, hoverBackground: p.dangerBg, activeBackground: p.dangerBg },
    },
  };
}
function messageScheme(p: typeof palette.light) {
  const status = (color: string, background: string) => ({ color, background, borderColor: color, shadow: 'none' });
  return {
    error: status(p.danger, p.dangerBg), warn: status(p.warning, p.warningBg),
    success: status(p.success, p.successBg), info: status(p.text, p.background),
    secondary: status(p.muted, p.background),
  };
}

export const OrcaPreset = definePreset(Aura, {
  semantic: {
    // aura-compat sets line-height: normal on every .p-component; PrimeVue 5 applies it through Tabs to whole views.
    typography: { fontFamily: 'inherit', lineHeight: 'inherit' },
    transitionDuration: '0.15s',
    focusRing: { width: '2px', style: 'solid', color: '{primary.color}', offset: '3px', shadow: 'none' },
    formField: { paddingX: '12px', paddingY: '8px', borderRadius: '6px',
      sm: { fontSize: '12px', paddingX: '10px', paddingY: '6px' },
      focusRing: { width: '2px', style: 'solid', color: '{primary.color}', offset: '2px', shadow: 'none' } },
    content: { borderRadius: '12px' },
    colorScheme: { light: scheme(palette.light), dark: scheme(palette.dark) },
  },
  components: {
    button: { root: { borderRadius: '6px', label: { fontWeight: '600' } },
      colorScheme: { light: buttonScheme(palette.light), dark: buttonScheme(palette.dark) } },
    message: { root: { borderWidth: '1px', borderRadius: '6px' },
      colorScheme: { light: messageScheme(palette.light), dark: messageScheme(palette.dark) } },
    dialog: { root: { borderRadius: '12px' }, header: { padding: '20px' }, content: { padding: '0 20px 20px' }, footer: { padding: '0 20px 20px' } },
  },
});

export { palette };
