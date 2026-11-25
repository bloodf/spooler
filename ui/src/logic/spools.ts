// Pure rules of the spool list, ported from the previous page script (the plugin's MAIN_PAGE, before the Vue page). No DOM, no Vue:
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

/** How full the drawn spool is, 0..1: Spoolman's remaining of initial weight, else the printer's percentage, else null
 *  (unknown: the full reel with the unknown badge when there is a colour, else the bare reel). Never a made-up level. */
export function spoolFraction(s?: Spool | null, printerPct?: number | null): number | null {
  const o = s ? originalWeight(s) : null, r = s?.remaining_weight;
  if (typeof o === 'number' && o > 0 && typeof r === 'number') return Math.max(0, Math.min(1, r / o));
  return typeof printerPct === 'number' && Number.isFinite(printerPct) ? Math.max(0, Math.min(1, printerPct / 100)) : null;
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

/** Grams typed on a card (decimal comma allowed) that the plugin accepts: more than 0, up to max. */
export function gramsValid(text: string, min0 = false, max = 100000): boolean {
  if (!text.trim()) return false;
  const n = Number(text.trim().replace(',', '.'));
  return Number.isFinite(n) && (min0 ? n >= 0 : n > 0) && n <= max;
}

const fold = (v: unknown) => String(v ?? '').normalize('NFD').replace(/\p{M}/gu, '').toLowerCase();
const WORDS = /[\s_\-.,/]+/g;
/** The typed letters appear in order inside one word, the first at the word's start. */
const inOrder = (token: string, word: string) => {
  if (word[0] !== token[0]) return false;
  let at = 0;
  for (const c of token) { at = word.indexOf(c, at) + 1; if (!at) return false; }
  return true;
};

// A search box asks about every spool on each keystroke: fold a spool's text once (per spool object; a refresh brings new ones).
const searched = new WeakMap<Spool, { text: string; words: string[]; joined: string }>();
function searchText(s: Spool) {
  let known = searched.get(s);
  if (!known) {
    const f = s.filament || {};
    const text = fold([f.name, f.material, f.vendor?.name, s.location, s.lot_nr, s.comment, f.color_hex].filter(Boolean).join(' '));
    const words = text.split(WORDS).filter(Boolean);
    known = { text, words, joined: words.join('') };  // joined: separators do not matter, "shelf-a" finds "Shelf A"
    searched.set(s, known);
  }
  return known;
}

/** "#12" and a plain number find spool 12 exactly (never fuzzy: 12 is not 13). Other text: every typed word has to be in the
 * name, material, manufacturer, location, lot, comment or colour, in any order, ignoring case and accents, as typed or, for 3+
 * letters, with letters missing ("plmk" finds Polymaker, "blck" Black). No typo correction beyond missing letters. */
export function spoolMatches(s: Spool, query: string): boolean {
  const typed = fold(query).trim();
  if (/^#\d+$/.test(typed)) return String(s.id) === typed.slice(1);
  if (/^\d+$/.test(typed)) return String(s.id) === typed;  // a bare number is an id, not text in a lot or colour
  const { text, words, joined } = searchText(s);
  if (text.includes(typed) || joined.includes(typed.replace(WORDS, ''))) return true;
  // Word by word, in any order. A number is an id ("red 7" is red AND spool 7, never a 7 inside the text). A word of 1-2 letters
  // is a whole word ("b" is not the b of "black": "shelf b" stays Shelf B); longer ones are found anywhere, or with letters missing.
  return typed.split(/\s+/).filter(Boolean).every(t => {
    if (/^\d+$/.test(t)) return String(s.id) === t;
    if (t.length < 3) return words.includes(t);
    return text.includes(t) || joined.includes(t.replace(WORDS, '')) || (/^\p{L}+$/u.test(t) && words.some(w => inOrder(t, w)));
  });
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
 * warning / danger tokens. "out" once the spool is in the last fifth of the low-stock grams, "empty" at 0 g. */
export type Level = '' | 'low' | 'out' | 'empty';
export function lowLevel(grams: unknown, low: number): Level {
  if (typeof grams === 'number' && grams <= 0) return 'empty';
  if (typeof grams !== 'number' || low <= 0 || grams >= low) return '';
  return grams <= low * 0.2 ? 'out' : 'low';
}

/** Tone of the level bar for a low-stock level: fine, low, or almost empty. */
export const levelTone = (level: Level): 'normal' | 'low' | 'critical' => (level === 'low' ? 'low' : level ? 'critical' : 'normal');
/** The chip text of a level. */
export const LEVEL_KEY: Record<Level, 'spool.low' | 'spool.out' | 'spool.empty'> = { '': 'spool.low', low: 'spool.low', out: 'spool.out', empty: 'spool.empty' };
/** The spool a stack shows when one must be shown: the one in use, else the one with the most left (never an empty one first). */
const leftRank = (s: Spool) => (typeof s.remaining_weight !== 'number' ? -1 : s.remaining_weight <= 0 ? -2 : s.remaining_weight);
export const stackLead = (items: Spool[], loaded: (s: Spool) => boolean): Spool => items.find(loaded)
  ?? [...items].sort((a, b) => leftRank(b) - leftRank(a))[0];
export const emptyCount = (items: Spool[]) => items.filter(s => typeof s.remaining_weight === 'number' && s.remaining_weight <= 0).length;

/** What the drawn spool and the swatch are painted with: one colour, or every colour of a multi-colour filament. */
export function spoolPaint(f: Filament): { color: string | null; colors: string[] | null } {
  const cs = swatchCols(f);
  return cs.length > 1 ? { color: cs[0], colors: cs } : { color: swatchHex(f.color_hex) || cs[0] || null, colors: null };
}

/** How the drawn spool lays out a multi-colour filament's colours: around the spool unless Spoolman says along it. */
export const spoolDirection = (f: Filament): 'coaxial' | 'longitudinal' => (f.multi_color_direction === 'longitudinal' ? 'longitudinal' : 'coaxial');

/** Remaining weight as it shows in a list: grams, percent, or both, following Settings. */
export function leftLabel(grams: unknown, percent: number | null, mode: 'grams' | 'percent' | 'both', exact: boolean, locale: string): string {
  const w = formatWeight(grams, exact, locale);
  if (typeof grams !== 'number') return percent === null ? '—' : `${percent}%`;
  return mode === 'percent' && percent !== null ? `${percent}%` : w;
}
