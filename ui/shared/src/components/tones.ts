/** A colour from the palette: grey (`neutral`, the default everywhere), OrcaSlicer's teal (`primary`), the plugin's identity hue
 * (`accent`: the mark and the active tab only), one of the seven hues, or a state colour. See base.css [data-tone]. */
export type OuiTone = 'accent' | 'primary' | 'neutral' | 'teal' | 'sky' | 'cobalt' | 'violet' | 'magenta' | 'lime' | 'orange' | 'success' | 'warn' | 'danger' | 'info';

// 5.0: material chips are neutral (the filament's own colour is in the spool and the swatch; a second colour per row
// competed with it). Kept so 4.x pages compile; pass no tone to a material chip and drop the call.
const MATERIAL_TONES: [RegExp, OuiTone][] = [[/^PLA/i, 'teal'], [/^PETG|^PCTG/i, 'cobalt'], [/^ABS/i, 'orange'], [/^ASA/i, 'violet'], [/^TPU|^TPE/i, 'magenta'], [/^PA|^NYLON|^PC/i, 'sky']];
export function materialTone(material: string | null | undefined): OuiTone {
  void material; void MATERIAL_TONES;
  return 'neutral';
}
