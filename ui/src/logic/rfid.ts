// A Bambu RFID spool no Spoolman spool carries (plugin/spooler/rfid.py rfid_offers): the editor it opens, pre-filled from what the
// printer reported, and the Spoolman filament it restocks when one matches. No DOM, no Vue: the unit tests import this file.
import { densityFor, type Raw } from './editor.ts';

export interface RfidOffer {
  tag: string; printer: string; unit: number | 'ext'; slot: number; type: string; name: string; colours: string[];
  remain: number | null; weight: number | null; diameter: number | null; nozzle: [number, number] | null;
}
export interface RfidPrefill { tag: string; filament: Raw; spool: Raw }

export const BAMBU = 'Bambu Lab';
const norm = (v: unknown) => String(v ?? '').trim().toLowerCase();
const cols = (f: Raw): string[] => {
  const multi = String(f.multi_color_hexes || '').split(',').map(norm).filter(Boolean);
  return multi.length > 1 ? multi : [norm(f.color_hex) || multi[0] || ''];
};

/** Grams left: the printer's percentage of the spool's weight, to the gram. */
export const leftGrams = (o: RfidOffer): number | null => (o.weight !== null && o.remain !== null ? Math.round((o.weight * o.remain) / 100) : null);

/** The editor's starting values: a Bambu Lab filament as the tray reports it (nozzle at the middle of its range), and the spool's weights. */
export function rfidPrefill(o: RfidOffer): RfidPrefill {
  const [first, ...rest] = o.colours;
  const filament: Raw = { vendor: { name: BAMBU }, name: o.name, material: o.type, diameter: o.diameter ?? 1.75, density: densityFor(o.type),
    settings_extruder_temp: o.nozzle ? Math.round((o.nozzle[0] + o.nozzle[1]) / 2) : null, weight: o.weight,
    ...(rest.length ? { multi_color_hexes: o.colours.join(','), multi_color_direction: 'coaxial' } : { color_hex: first ?? null }) };
  return { tag: o.tag, filament, spool: { initial_weight: o.weight, remaining_weight: leftGrams(o) } };
}

/** The Spoolman filament this spool restocks: Bambu Lab, the same material and the same colours, and only when that is one filament,
 * or one of them is named like the tray. Bambu lines share colours (Basic and Matte black), so several unnamed fits pick none. */
export function matchFilament(filaments: Raw[] | undefined, o: RfidOffer): number | null {
  const want = o.colours.map(norm).join(',');
  const fits = (filaments ?? []).filter(f => typeof f.id === 'number' && norm(f.vendor?.name) === norm(BAMBU)
    && norm(f.material) === norm(o.type) && want !== '' && cols(f).join(',') === want);
  const named = fits.filter(f => norm(f.name).includes(norm(o.name)));
  const one = named.length === 1 ? named : fits.length === 1 ? fits : [];
  return one[0]?.id ?? null;
}
