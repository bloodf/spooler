// Pure rules of the spool editor (Add Spool, Edit Spool): the form a Spoolman spool or filament opens as, what a form
// sends, what changed, and what is missing. No DOM, no Vue: the unit tests import this file directly. The plugin checks
// everything again (plugin/spooler/editor.py SPOOL_FORM / FILAMENT_FORM) before Spoolman sees it.

/** A Spoolman extra field, as GET field/spool and field/filament list them. */
export interface FieldDef {
  key: string; name?: string; field_type?: string; unit?: string | null; order?: number;
  choices?: string[] | null; multi_choice?: boolean | null;
}
export type Raw = Record<string, any>;
export type Extra = Record<string, unknown>;

export interface SpoolForm {
  initial_weight: number | null; remaining_weight: number | null; location: string; lot_nr: string;
  price: number | null; comment: string; archived: boolean; extra: Extra;
}
export interface FilamentForm {
  vendor: string; name: string; material: string; colors: string[]; direction: 'coaxial' | 'longitudinal';
  diameter: number | null; density: number | null; settings_extruder_temp: number | null; settings_bed_temp: number | null;
  weight: number | null; spool_weight: number | null; extra: Extra;
}

/** Usual densities (g/cm³), offered for a new filament until the user types one. */
export const DENSITY: Record<string, number> = { PLA: 1.24, PETG: 1.27, ABS: 1.04, ASA: 1.07, TPU: 1.21, PA: 1.14, PC: 1.2, PVA: 1.23, HIPS: 1.04 };
export function densityFor(material: string): number | null {
  const name = material.trim().toUpperCase();
  const key = Object.keys(DENSITY).filter(k => name.startsWith(k)).sort((a, b) => b.length - a.length)[0];
  return key ? DENSITY[key] : null;
}

const num = (v: unknown): number | null => (typeof v === 'number' && Number.isFinite(v) ? v : null);
const str = (v: unknown): string => (typeof v === 'string' ? v : '');
const hex = (v: unknown): string => { const m = /^#?([0-9a-f]{6})/i.exec(str(v).trim()); return m ? '#' + m[1].toLowerCase() : ''; };

/** The extra fields the editor shows: the user's own, in Spoolman's order; Spooler's own fields stay out. */
export const editable = (defs: FieldDef[] | undefined, own: string[]): FieldDef[] =>
  (defs ?? []).filter(d => d && typeof d.key === 'string' && !own.includes(d.key)).sort((a, b) => (a.order ?? 0) - (b.order ?? 0));

/** An extra field's stored JSON text as the value its input edits; null when unset or unreadable. */
export function decodeExtra(raw: unknown, def: FieldDef): unknown {
  if (typeof raw !== 'string' || raw === '') return null;
  let v: unknown;
  try { v = JSON.parse(raw); } catch { return def.field_type === 'text' ? raw : null; }
  switch (def.field_type) {
    case 'boolean': return typeof v === 'boolean' ? v : null;
    case 'integer': case 'float': return num(v);
    case 'integer_range': case 'float_range': return Array.isArray(v) && v.length === 2 ? [num(v[0]), num(v[1])] : null;
    case 'choice': return def.multi_choice ? (Array.isArray(v) ? v.filter(x => typeof x === 'string') : null) : typeof v === 'string' ? v : null;
    default: return typeof v === 'string' ? v : v === null ? null : String(v);
  }
}
/** An edited value as the plugin takes it: null (or an empty text, list or range) leaves the field unset. */
export function encodeExtra(v: unknown, def: FieldDef): unknown {
  if (v === null || v === undefined || v === '' || (Array.isArray(v) && !v.length)) return null;
  if ((def.field_type === 'integer_range' || def.field_type === 'float_range') && Array.isArray(v) && v.every(x => x === null)) return null;
  if (typeof v === 'string' && def.field_type !== 'choice') return v.trim() || null;
  return v;
}
const extrasOf = (raw: Raw | undefined, defs: FieldDef[]): Extra =>
  Object.fromEntries(defs.map(d => [d.key, decodeExtra(raw?.extra?.[d.key], d)]));

export function spoolForm(raw: Raw | undefined, defs: FieldDef[]): SpoolForm {
  return { initial_weight: num(raw?.initial_weight), remaining_weight: num(raw?.remaining_weight), location: str(raw?.location),
    lot_nr: str(raw?.lot_nr), price: num(raw?.price), comment: str(raw?.comment), archived: raw?.archived === true, extra: extrasOf(raw, defs) };
}
export function filamentForm(raw: Raw | undefined, defs: FieldDef[]): FilamentForm {
  const multi = str(raw?.multi_color_hexes).split(',').map(hex).filter(Boolean);
  const colors = multi.length > 1 ? multi : [hex(raw?.color_hex) || multi[0] || ''];
  return { vendor: str(raw?.vendor?.name), name: str(raw?.name), material: str(raw?.material), colors,
    direction: raw?.multi_color_direction === 'longitudinal' ? 'longitudinal' : 'coaxial',
    diameter: raw ? num(raw.diameter) : 1.75, density: raw ? num(raw.density) : null,
    settings_extruder_temp: num(raw?.settings_extruder_temp), settings_bed_temp: num(raw?.settings_bed_temp),
    weight: num(raw?.weight), spool_weight: num(raw?.spool_weight), extra: extrasOf(raw, defs) };
}

const encodeAll = (extra: Extra, defs: FieldDef[]): Extra => Object.fromEntries(defs.map(d => [d.key, encodeExtra(extra[d.key], d)]));
const text = (v: string) => v.trim() || null;

/** What a spool form sends: every field, empties as null (the plugin leaves those out of a new spool). */
export function spoolPayload(f: SpoolForm, defs: FieldDef[]): Raw {
  return { initial_weight: f.initial_weight, remaining_weight: f.remaining_weight, location: text(f.location), lot_nr: text(f.lot_nr),
    price: f.price, comment: text(f.comment), archived: f.archived, extra: encodeAll(f.extra, defs) };
}
/** What a filament form sends: one colour as color_hex, several as multi_color_hexes with their direction. */
export function filamentPayload(f: FilamentForm, defs: FieldDef[]): Raw {
  const colors = f.colors.map(hex).filter(Boolean).map(c => c.slice(1).toUpperCase());
  const paint = colors.length > 1 ? { color_hex: null, multi_color_hexes: colors.join(','), multi_color_direction: f.direction }
    : { color_hex: colors[0] ?? null, multi_color_hexes: null, multi_color_direction: null };
  return { vendor: text(f.vendor), name: text(f.name), material: text(f.material), ...paint, diameter: f.diameter, density: f.density,
    settings_extruder_temp: f.settings_extruder_temp, settings_bed_temp: f.settings_bed_temp, weight: f.weight, spool_weight: f.spool_weight,
    extra: encodeAll(f.extra, defs) };
}
/** A new spool or filament sends no empty field: Spoolman's defaults stand for them. */
export function filled(p: Raw): Raw {
  const out: Raw = {};
  for (const [k, v] of Object.entries(p)) {
    if (k === 'extra') { const e = Object.fromEntries(Object.entries(v as Extra).filter(([, x]) => x !== null)); if (Object.keys(e).length) out.extra = e; }
    else if (v !== null) out[k] = v;
  }
  return out;
}

const same = (a: unknown, b: unknown) => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);
/** The fields of now that differ from base (extra key by key); {} when nothing changed. */
export function changed(now: Raw, base: Raw): Raw {
  const out: Raw = {};
  for (const [k, v] of Object.entries(now)) {
    if (k !== 'extra') { if (!same(v, base[k])) out[k] = v; continue; }
    const e = Object.fromEntries(Object.entries(v as Extra).filter(([x, y]) => !same(y, base.extra?.[x])));
    if (Object.keys(e).length) out.extra = e;
  }
  return out;
}
/** What Spoolman held for the changed fields when the editor read it: the plugin keeps Spoolman's value for a field
 * that differs from this by the time it writes (someone changed it meanwhile). */
export function wasOf(raw: Raw | undefined, changes: Raw): Raw {
  const out: Raw = {};
  for (const k of Object.keys(changes)) {
    if (k === 'extra') out.extra = Object.fromEntries(Object.keys(changes.extra).map(x => [x, raw?.extra?.[x] ?? null]));
    else out[k] = k === 'vendor' ? (raw?.vendor?.name ?? null) : (raw?.[k] ?? null);
  }
  return out;
}

export type Problem = 'required' | 'tooMuch' | 'date';
/** What stops a save, by field: density and diameter are required for a filament; a new spool can't start with less
 * than is left; a date field holds a date. */
export function problems(spool: SpoolForm, filament: FilamentForm | null, defs: { spool: FieldDef[]; filament: FieldDef[] }, adding: boolean,
  base?: SpoolForm): Record<string, Problem> {
  const out: Record<string, Problem> = {};
  // Spoolman works with a spool's weights: one it has can be changed, not emptied.
  for (const k of ['initial_weight', 'remaining_weight'] as const) if (!adding && base && base[k] !== null && spool[k] === null) out[k] = 'required';
  if (filament) for (const k of ['diameter', 'density'] as const) if (!(typeof filament[k] === 'number' && (filament[k] as number) > 0)) out[k] = 'required';
  if (adding && spool.initial_weight !== null && spool.remaining_weight !== null && spool.remaining_weight > spool.initial_weight) out.remaining_weight = 'tooMuch';
  const dates = (extra: Extra, list: FieldDef[], prefix: string) => {
    for (const d of list) {
      const v = extra[d.key];
      // ISO only (2026-11-16, optionally with a time): what Spoolman and the plugin read.
      if (d.field_type === 'datetime' && typeof v === 'string' && v.trim() && !(/^\d{4}-\d{2}-\d{2}([T ]\S+)?$/.test(v.trim()) && !Number.isNaN(Date.parse(v.trim())))) out[prefix + d.key] = 'date';
    }
  };
  dates(spool.extra, defs.spool, 'spool.');
  if (filament) dates(filament.extra, defs.filament, 'filament.');
  return out;
}

/** The filament as the preview card and swatch draw it. */
export const previewFilament = (f: FilamentForm) => {
  const p = filamentPayload(f, []);
  return { name: f.name.trim(), material: f.material.trim(), vendor: { name: f.vendor.trim() }, diameter: f.diameter ?? undefined,
    color_hex: p.color_hex ?? undefined, multi_color_hexes: p.multi_color_hexes ?? undefined, weight: f.weight ?? undefined };
};
