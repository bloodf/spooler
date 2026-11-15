/** A colour pair from the palette: the plugin accent, one of the seven hues, or a state colour. See base.css [data-tone]. */
export type OuiTone = 'accent' | 'neutral' | 'teal' | 'sky' | 'cobalt' | 'violet' | 'magenta' | 'lime' | 'orange' | 'success' | 'warn' | 'danger' | 'info';

// One hue per material family, the same in every plugin, so "PETG" is recognised before it is read.
// It tints the material chip only; the filament's own colour stays in the spool and the swatch.
const MATERIAL_TONES: [RegExp, OuiTone][] = [[/^PLA/i, 'teal'], [/^PETG|^PCTG/i, 'cobalt'], [/^ABS/i, 'orange'], [/^ASA/i, 'violet'], [/^TPU|^TPE/i, 'magenta'], [/^PA|^NYLON|^PC/i, 'sky']];
export function materialTone(material: string | null | undefined): OuiTone {
  return MATERIAL_TONES.find(([test]) => test.test(material ?? ''))?.[1] ?? 'neutral';
}
