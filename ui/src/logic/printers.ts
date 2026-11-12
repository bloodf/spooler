// Printer-panel rules ported from the previous page: slot names, where each spool is loaded, manual units.
export interface Tray { slot?: number; empty?: boolean; type?: string; name?: string; colour?: string; remain?: number | null; rfid?: boolean;
  spool?: number | string | null; profile?: string; linked?: string }
export interface LiveUnit { id: number | string; kind: string; trays: Tray[] }
export interface LivePrinter { id?: string; link?: string; name: string; heads?: boolean; unit_label?: string; units: LiveUnit[]; ext?: Tray | null;
  age?: number; spool_set?: boolean; job?: Job | null }
export interface Job { state: string; name?: string; pct?: number; stage?: string; layer?: number; layers?: number; left?: number | null;
  took?: number; end?: number; tray?: { unit: number | string; slot: number } | null }
export interface ManualUnit { kind: 'ams' | 'ht' | 'ext'; slots: (string | number | null)[] }
export interface ManualPrinter { id: string; name: string; auto?: boolean; ip?: string; serial?: string; has_code?: boolean; units: ManualUnit[] }

export const KINDS: Record<string, number> = { ams: 4, ht: 1, ext: 1 };
export const RANK: Record<string, number> = { ams: 0, ht: 1, ext: 2 };
export const LIVE_STALE = 180;
export const PROG_LIVE = ['RUNNING', 'PREPARE', 'SLICING', 'PAUSE'];
export const PROG_STATES: Record<string, { cls: string; fill: string }> = {
  RUNNING: { cls: '', fill: '' }, PREPARE: { cls: '', fill: 'prep' }, SLICING: { cls: '', fill: 'prep' },
  PAUSE: { cls: 'warn', fill: 'warn' }, FINISH: { cls: 'ok', fill: 'ok' }, FAILED: { cls: 'bad', fill: 'bad' },
};

export interface Words { ams: string; ht: string; ext: string; slot: (unit: string, n: number) => string; head: (n: number) => string; externalShort: string }

export function unitLabel(p: ManualPrinter, u: ManualUnit, w: Words): string {
  const same = p.units.filter(x => x.kind === u.kind);
  const n = same.indexOf(u) + 1;
  if (u.kind === 'ams') return `${w.ams} ${n}`;
  if (u.kind === 'ht') return same.length > 1 ? `${w.ht} ${n}` : w.ht;
  return w.ext;
}

export function slotName(lv: LivePrinter, u: LiveUnit | null, i: number, ext: boolean, w: Words): string {
  if (ext || !u) return w.externalShort;
  if (lv.heads) return w.head(i + 1);
  if (u.kind === 'ht') return w.ht;
  const ams = lv.units.filter(x => x.kind === 'ams');
  const unit = lv.unit_label && lv.units.length === 1 ? lv.unit_label : `${lv.unit_label || w.ams} ${ams.indexOf(u) + 1}`;
  return w.slot(unit, i + 1);
}

/** spool id -> "Printer · slot", from the live printers first, then the manually assigned slots. */
export function computeInUse(live: LivePrinter[], cfg: ManualPrinter[], w: Words): Map<string, string> {
  const found = new Map<string, string>();
  for (const lv of live || []) {
    const add = (t: Tray | null | undefined, label: string) => { if (t && t.spool != null) found.set(String(t.spool), `${lv.name} · ${label}`); };
    (lv.units || []).forEach(u => (u.trays || []).forEach((t, i) => add(t, slotName(lv, u, i, false, w))));
    if (lv.ext) add(lv.ext, w.externalShort);
  }
  for (const p of cfg || []) {
    (p.units || []).forEach(u => u.slots.forEach((id, si) => {
      const where = u.kind === 'ext' ? w.externalShort : u.kind === 'ht' ? unitLabel(p, u, w) : w.slot(unitLabel(p, u, w), si + 1);
      if (id && !found.has(String(id))) found.set(String(id), `${p.name} · ${where}`);
    }));
  }
  return found;
}

export function takenIds(cfg: ManualPrinter[]): Set<string> {
  const set = new Set<string>();
  cfg.forEach(p => p.units.forEach(u => u.slots.forEach(id => { if (id) set.add(String(id)); })));
  return set;
}

/** The live state as it shows: age only matters once it crosses into stale (F12). */
export const liveSig = (live: unknown) => JSON.stringify(live, (k, v) => (k === 'age' ? v > LIVE_STALE : v));

export function newPrinterId(now = Date.now(), rand = Math.random()): string {
  return 'p' + now.toString(36) + Math.floor(rand * 1296).toString(36);
}
export function addUnit(p: ManualPrinter, kind: 'ams' | 'ht' | 'ext'): ManualPrinter {
  if (!KINDS[kind] || (kind === 'ext' && p.units.some(u => u.kind === 'ext'))) return p;
  const units = [...p.units, { kind, slots: new Array(KINDS[kind]).fill(null) }].sort((x, y) => RANK[x.kind] - RANK[y.kind]);
  return { ...p, units };
}
