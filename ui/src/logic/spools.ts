// Pure rules of the spool list, ported from the previous page script (spooler_any.py MAIN_PAGE). No DOM, no Vue:
// the unit tests import this file directly. Formatting takes the locale explicitly.
export interface Vendor { name?: string }
export interface Filament {
  id?: number; name?: string; material?: string; color_hex?: string; multi_color_hexes?: string; multi_color_direction?: string;
  vendor?: Vendor; diameter?: number; weight?: number;
}
export interface Spool {
  id: number; filament?: Filament; remaining_weight?: number | null; used_weight?: number | null; initial_weight?: number | null;
  location?: string; lot_nr?: string; comment?: string; extra?: Record<string, unknown>; archived?: boolean;
  first_used?: string; last_used?: string; rfid_tags?: unknown[]; tags?: unknown[]; use_first?: boolean; dry_days?: number;
  u1_bound?: boolean; ams?: { printer?: string; unit?: number; slot?: number };
}
export type Display = Record<string, boolean>;
export const shown = (disp: Display, key: string) => disp[key] !== false;

export function swatchHex(v: unknown): string {
  const m = String(v || '').trim().replace(/^#/, '').match(/^[0-9a-f]{6}/i);
  return m ? '#' + m[0] : '';
}
export const swatchCols = (f: Filament): string[] => String(f.multi_color_hexes || '').split(',').map(swatchHex).filter(Boolean);
/** One solid colour for the ring and bar; the first colour on multi-colour spools. */
export function swatchMain(f: Filament): string {
  const cs = swatchCols(f);
  return (cs.length < 2 && swatchHex(f.color_hex)) || cs[0] || '#888';
}
export function swatch(f: Filament): string {
  const cs = swatchCols(f);
  if (cs.length < 2) return swatchMain(f);
  if (f.multi_color_direction === 'longitudinal') return `linear-gradient(135deg, ${cs.join(', ')})`;
  const step = 360 / cs.length;
  return 'conic-gradient(' + cs.map((c, i) => `${c} ${i * step}deg ${(i + 1) * step}deg`).join(', ') + ')';
}

export function formatWeight(grams: unknown, exact: boolean, locale: string): string {
  if (typeof grams !== 'number') return '?';
  if (exact) return `${new Intl.NumberFormat(locale, { maximumFractionDigits: 0 }).format(Math.round(grams))} g`;
  return Math.abs(grams) >= 1000
    ? `${new Intl.NumberFormat(locale, { minimumFractionDigits: 2, maximumFractionDigits: 2 }).format(grams / 1000)} kg`
    : `${Math.round(grams)} g`;
}

export const originalWeight = (s: Spool): number | undefined | null =>
  s.initial_weight !== undefined && s.initial_weight !== null ? s.initial_weight : s.filament?.weight;

export function percentLeft(s: Spool): number | null {
  const o = originalWeight(s), r = s.remaining_weight;
  return typeof o === 'number' && o > 0 && typeof r === 'number' ? Math.max(0, Math.min(100, Math.round((r / o) * 100))) : null;
}

/** Lot number, comment and the user's own extra fields; Spooler's own fields never show. */
export function noteText(s: Spool, disp: Display, ownFields: string[], lot = (v: string) => `Lot ${v}`): string {
  const parts: string[] = [];
  if (s.lot_nr && shown(disp, 'lot_nr')) parts.push(lot(s.lot_nr));
  if (s.comment && shown(disp, 'comment')) parts.push(String(s.comment).replace(/\s+/g, ' ').trim());
  if (s.extra && typeof s.extra === 'object' && shown(disp, 'extra_fields')) {
    for (const key of Object.keys(s.extra)) {
      if (ownFields.includes(key)) continue;
      let value: unknown = s.extra[key];
      try { value = JSON.parse(String(value)); } catch { /* plain text */ }
      if (value === null || value === '' || typeof value === 'object') continue;
      parts.push(`${key}: ${value}`);
    }
  }
  return parts.join(' · ');
}

/** Whole days since the spool was marked dried (extra.dried, JSON text holding an ISO date), or null. */
export function driedDays(s: Spool, now = Date.now()): number | null {
  let v: unknown = s.extra && typeof s.extra === 'object' ? s.extra.dried : null;
  if (v === null || v === undefined) return null;
  try { v = JSON.parse(String(v)); } catch { /* plain text */ }
  const m = /^(\d{4})-(\d{2})-(\d{2})/.exec(String(v));
  if (!m) return null;
  const t = new Date(now);
  const days = Math.round((Date.UTC(t.getFullYear(), t.getMonth(), t.getDate()) - Date.UTC(+m[1], +m[2] - 1, +m[3])) / 86400000);
  return Math.max(0, days);
}
export const driedOld = (s: Spool, age: number) => (s.dry_days ?? 0) > 0 && age > (s.dry_days ?? 0);

export function tagUids(s: Spool): string[] {
  const tags = Array.isArray(s.rfid_tags) ? s.rfid_tags : s.tags;
  if (!Array.isArray(tags)) return [];
  return tags.map(t => (typeof t === 'string' ? t : (t && ((t as any).uid || (t as any).id)) || null)).filter(Boolean) as string[];
}

/** Colour family for the colour filter: spools match by family, not exact hex. */
export const COLOR_FAMILIES: [string, string][] = [
  ['black', '#111111'], ['gray', '#8a8a8a'], ['white', '#f4f4f4'], ['red', '#e5484d'], ['orange', '#f5852a'],
  ['yellow', '#f5d90a'], ['green', '#46a758'], ['blue', '#3e63dd'], ['purple', '#8e4ec6'], ['pink', '#e93d82'],
  ['brown', '#8d5a3b'], ['multi', 'conic-gradient(#e5484d, #f5d90a, #46a758, #3e63dd, #e5484d)'],
];
export function colorFamily(f: Filament): string {
  if (swatchCols(f).length > 1) return 'multi';
  const hex = swatchHex(f.color_hex);
  if (!hex) return '';
  const rgb = [1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16) / 255);
  const max = Math.max(...rgb), min = Math.min(...rgb);
  const l = (max + min) / 2, d = max - min;
  const sat = d === 0 ? 0 : d / (1 - Math.abs(2 * l - 1));
  if (l < 0.12 || (l < 0.2 && sat < 0.35)) return 'black';
  if (l > 0.9 && sat < 0.5) return 'white';
  if (sat < 0.15) return 'gray';
  let h = max === rgb[0] ? ((rgb[1] - rgb[2]) / d) % 6 : max === rgb[1] ? (rgb[2] - rgb[0]) / d + 2 : (rgb[0] - rgb[1]) / d + 4;
  h = (h * 60 + 360) % 360;
  if (h >= 15 && h < 45 && l < 0.42) return 'brown';
  if (h < 15 || h >= 345) return l > 0.7 ? 'pink' : 'red';
  if (h < 40) return 'orange';
  if (h < 70) return 'yellow';
  if (h < 170) return 'green';
  if (h < 255) return 'blue';
  if (h < 290) return 'purple';
  return 'pink';
}

/** Same metric as the plate check's colour_diff: straight-line distance in RGB. */
export function colourDiff(a: unknown, b: unknown): number | null {
  const x = swatchHex(a), y = swatchHex(b);
  if (!x || !y) return null;
  let sum = 0;
  for (let i = 1; i < 7; i += 2) { const d = parseInt(x.slice(i, i + 2), 16) - parseInt(y.slice(i, i + 2), 16); sum += d * d; }
  return Math.sqrt(sum);
}
export function spoolDistance(s: Spool, hex: string): number | null {
  const f = s.filament || {};
  const cs = swatchCols(f);
  let best: number | null = null;
  for (const c of cs.length > 1 ? cs : [f.color_hex]) {
    const d = colourDiff(c, hex);
    if (d !== null && (best === null || d < best)) best = d;
  }
  return best;
}
export const MATCH_TOP = 12;
export const closestSpools = (spools: Spool[], hex: string): Spool[] => spools
  .map(s => ({ s, d: spoolDistance(s, hex) })).filter(x => x.d !== null).sort((a, b) => (a.d as number) - (b.d as number))
  .slice(0, MATCH_TOP).map(x => x.s);

/** "#12" finds spool 12 only; other text looks in name, material, manufacturer, location, lot and comment. */
export function spoolMatches(s: Spool, query: string): boolean {
  if (/^#\d+$/.test(query)) return String(s.id) === query.slice(1);
  const f = s.filament || {};
  return [f.name, f.material, f.vendor?.name, s.location, s.lot_nr, s.comment].filter(Boolean).join(' ').toLowerCase().includes(query);
}

export type SortKey = 'name' | 'material' | 'vendor' | 'remaining' | 'used' | 'first_used' | 'last_used' | 'plate';
export function sortValue(s: Spool, key: SortKey, plateOrder: Map<number, number>): string | number | null {
  const f = s.filament || {};
  switch (key) {
    case 'name': return (f.name || '').toLowerCase() || null;
    case 'material': return (f.material || '').toLowerCase() || null;
    case 'vendor': return (f.vendor?.name || '').toLowerCase() || null;
    case 'remaining': return typeof s.remaining_weight === 'number' ? s.remaining_weight : null;
    case 'used': return typeof s.used_weight === 'number' ? s.used_weight : null;
    case 'first_used': return s.first_used ? Date.parse(s.first_used) : null;
    case 'last_used': return s.last_used ? Date.parse(s.last_used) : null;
    case 'plate': return plateOrder.has(s.id) ? (plateOrder.get(s.id) as number) : null;
    default: return null;
  }
}
/** A spool missing the field (e.g. never used) always sorts last, even descending. */
export function compareSpools(a: Spool, b: Spool, key: SortKey, dir: 'asc' | 'desc', plateOrder = new Map<number, number>()): number {
  const av = sortValue(a, key, plateOrder), bv = sortValue(b, key, plateOrder);
  if (av === null && bv === null) return 0;
  if (av === null) return 1;
  if (bv === null) return -1;
  if (av < bv) return dir === 'asc' ? -1 : 1;
  if (av > bv) return dir === 'asc' ? 1 : -1;
  return 0;
}

export function computeDupes(spools: Spool[]): Map<number, { count: number; total: number }> {
  const out = new Map<number, { count: number; total: number }>();
  for (const s of spools) {
    const id = s.filament?.id;
    if (s.archived || id === undefined || typeof s.remaining_weight !== 'number') continue;
    const d = out.get(id) || { count: 0, total: 0 };
    out.set(id, { count: d.count + 1, total: d.total + s.remaining_weight });
  }
  return out;
}

export const stackKey = (s: Spool) => {
  const f = s.filament || {};
  return ['stack', f.vendor?.name || '', f.name || '', f.material || '', swatchCols(f).join(',') || swatchHex(f.color_hex)].join('|').toLowerCase();
};

export interface Totals { percent: number | null; remaining: number | null; original: number | null }
export function totals(items: Spool[]): Totals {
  let o = 0, r = 0, hasO = false, hasR = false;
  for (const s of items) {
    const ow = originalWeight(s);
    if (typeof ow === 'number') { o += ow; hasO = true; }
    if (typeof s.remaining_weight === 'number') { r += s.remaining_weight; hasR = true; }
  }
  return { percent: hasO && hasR && o > 0 ? Math.max(0, Math.min(100, Math.round((r / o) * 100))) : null,
    remaining: hasR ? r : null, original: hasO ? o : null };
}

export type Entry = { kind: 'spool'; key: string; spool: Spool } | { kind: 'stack'; key: string; items: Spool[]; used: number };
/** Spools of the same filament fold into one stack (loaded ones first); order follows each stack's first spool. */
export function stackEntries(spools: Spool[], grouping: boolean, loaded: (s: Spool) => boolean): Entry[] {
  if (!grouping) return spools.map(s => ({ kind: 'spool', key: 's:' + s.id, spool: s }));
  const stacks = new Map<string, Spool[]>();
  for (const s of spools) { const k = stackKey(s); stacks.set(k, [...(stacks.get(k) ?? []), s]); }
  return [...stacks.entries()].map(([key, list]) => {
    const items = [...list].sort((a, b) => (loaded(b) ? 1 : 0) - (loaded(a) ? 1 : 0));
    return items.length < 2 ? { kind: 'spool', key: 's:' + items[0].id, spool: items[0] } as Entry
      : { kind: 'stack', key, items, used: items.filter(loaded).length } as Entry;
  });
}

export interface Group { key: string; label: string; items: Spool[] }
export function groupSpools(spools: Spool[], mode: 'location' | 'material' | 'vendor', unknown: Record<string, string>): Group[] {
  const groups = new Map<string, Group>();
  for (const s of spools) {
    const f = s.filament || {};
    const label = mode === 'material' ? f.material || unknown.material : mode === 'vendor' ? f.vendor?.name || unknown.vendor : s.location || unknown.location;
    const g = groups.get(label) ?? { key: label, label, items: [] };
    groups.set(label, { ...g, items: [...g.items, s] });
  }
  return [...groups.values()].sort((a, b) => (mode === 'location' && b.items.length !== a.items.length
    ? b.items.length - a.items.length : a.label.toLowerCase().localeCompare(b.label.toLowerCase())));
}

/** Low stock level (B-22): the previous amber→red text tint measured 2.05:1; the page now uses the palette's
 * warning / danger tokens. "out" once the spool is in the last fifth of the low-stock grams. */
export function lowLevel(grams: unknown, low: number): '' | 'low' | 'out' {
  if (typeof grams !== 'number' || low <= 0 || grams >= low) return '';
  return grams <= low * 0.2 ? 'out' : 'low';
}

/**
 * The spool picture: eight renders of the same spool, from full (1) to an empty reel (8), tinted with the
 * filament colour on the page. These are how much each render shows wound on the reel.
 */
export const SPOOL_LEVEL_FILL = [1, 0.85, 0.7, 0.55, 0.4, 0.25, 0.08, 0] as const;
export type SpoolLevel = 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8;

/**
 * The render closest to `fraction` (0..1). Any filament left, however little, is still level 7 ("almost
 * empty"): the bare reel (8) is only for a spool with nothing on it or an unknown amount, because drawing an
 * empty reel for a spool that still has filament would be wrong.
 */
export function spoolLevel(fraction: number | null | undefined): SpoolLevel {
  if (fraction == null || !Number.isFinite(fraction) || fraction <= 0) return 8;
  const f = Math.min(1, fraction);
  let best = 0;
  for (let n = 1; n < 7; n++) if (Math.abs(SPOOL_LEVEL_FILL[n] - f) < Math.abs(SPOOL_LEVEL_FILL[best] - f)) best = n;
  return (best + 1) as SpoolLevel;
}

/** The bar's fill as CSS: the filament's own colours, side by side for multi-colour spools. */
export function barFill(f: Filament): string {
  const cs = swatchCols(f);
  if (cs.length < 2) return swatchMain(f);
  const step = 100 / cs.length;
  return 'linear-gradient(90deg, ' + cs.map((c, i) => `${c} ${i * step}% ${(i + 1) * step}%`).join(', ') + ')';
}
