// Printer-panel rules ported from the previous page: slot names, where each spool is loaded, manual units.
export interface Tray { slot?: number; empty?: boolean; type?: string; name?: string; colour?: string; remain?: number | null; rfid?: boolean;
  spool?: number | string | null; profile?: string; linked?: string }
/** source: what feeds an Anycubic unit ('ace' unit of firmware box id `box`, 'holder' the spool holder, box -1); none for other printers. */
export interface LiveUnit { id: number | string; kind: string; trays: Tray[]; source?: 'ace' | 'holder' | ''; box?: number }
export interface LivePrinter { id?: string; link?: string; name: string; heads?: boolean; unit_label?: string; units: LiveUnit[]; ext?: Tray | null;
  age?: number; spool_set?: boolean; hh?: boolean; job?: Job | null;
  /** The slots the page may link a spool to: 'T' U1 toolheads (U1 Control's location), 'S' Anycubic Kobra ACE and spool holder slots (Kobra Control's). */
  bind?: '' | 'T' | 'S';
  /** 'kobracontrol': the slots come from Kobra Control, which holds the printer (Spooler doesn't connect to it). */
  via?: '' | 'kobracontrol' }
export interface Job { state: string; name?: string; pct?: number; stage?: string; layer?: number; layers?: number; left?: number | null;
  took?: number; end?: number; tray?: { unit: number | string; slot: number } | null }
export type UnitKind = 'ams' | 'ht' | 'ext' | 'tool' | 'gate';
export type PrinterType = 'bambu' | 'prusalink' | 'octoprint';
export interface ManualUnit { kind: UnitKind; slots: (string | number | null)[] }
export interface ManualPrinter { id: string; name: string; auto?: boolean; kind?: string; ip?: string; serial?: string; has_code?: boolean; units: ManualUnit[];
  type?: PrinterType; user?: string; slice_fill?: boolean; managed?: boolean }
/** A filament of the last slice that matches several spools: which one goes on the printer's slot. */
export interface SlicePick { printer: string; name: string; n: number; slice: number; unit: number; slot: number; material: string; colour: string; spools: number[] }

/** PrusaLink and OctoPrint printers: read over HTTP, toolheads assigned by hand, prints always asked before booking. */
export const isNet = (p: ManualPrinter) => p.type === 'prusalink' || p.type === 'octoprint';
export const MAX_UNITS = 8;
export const MAX_GATES = 16;

/** A Klipper printer found from the presets whose toolheads or MMU gates are set by hand (it reports neither). */
export const isKlipperManual = (p: ManualPrinter) => !!p.auto && p.kind === 'moonraker' && !p.managed;
/** The printers a slice can fill: PrusaLink and OctoPrint printers with an address, and those Klipper printers. */
export const fillable = (cfg: ManualPrinter[]) => cfg.filter(p => (isNet(p) && !!p.ip) || isKlipperManual(p));
/** The printer with its MMU gates resized to n (0 removes them); the spools on the gates that stay are kept. */
export function withGates(p: ManualPrinter, n: number): ManualPrinter {
  const count = Math.max(0, Math.min(MAX_GATES, Math.floor(n) || 0));
  const old = p.units.find(u => u.kind === 'gate')?.slots ?? [];
  const rest = p.units.filter(u => u.kind !== 'gate');
  return { ...p, units: count ? [...rest, { kind: 'gate', slots: Array.from({ length: count }, (_, i) => old[i] ?? null) }] : rest };
}
/** {preset: printer id} with the presets given to printer id (and taken off any other printer). */
export function mapPresets(map: Record<string, string>, id: string, presets: string[]): Record<string, string> {
  const next = Object.fromEntries(Object.entries(map).filter(([, v]) => v !== id));
  for (const name of presets) next[name] = id;
  return next;
}

export const KINDS: Record<string, number> = { tool: 1, ams: 4, ht: 1, ext: 1 };
export const RANK: Record<string, number> = { tool: 0, ams: 1, ht: 2, ext: 3 };
export const LIVE_STALE = 180;
/** How long a live printer may take to report its first slots before the page says it may not. */
export const WAIT_SLOTS_MS = 45_000;
export const PROG_LIVE = ['RUNNING', 'PREPARE', 'SLICING', 'PAUSE'];
export const PROG_STATES: Record<string, { cls: string; fill: string }> = {
  RUNNING: { cls: '', fill: '' }, PREPARE: { cls: '', fill: 'prep' }, SLICING: { cls: '', fill: 'prep' },
  PAUSE: { cls: 'warn', fill: 'warn' }, FINISH: { cls: 'ok', fill: 'ok' }, FAILED: { cls: 'bad', fill: 'bad' },
};

export interface Words { ace: string; holder: string; ams: string; ht: string; ext: string; gate: string; gateN: (n: number) => string; slot: (unit: string, n: number) => string; head: (n: number) => string; externalShort: string }

export function unitLabel(p: ManualPrinter, u: ManualUnit, w: Words): string {
  const same = p.units.filter(x => x.kind === u.kind);
  const n = same.indexOf(u) + 1;
  if (u.kind === 'tool') return w.head(n);
  if (u.kind === 'ams') return `${w.ams} ${n}`;
  if (u.kind === 'ht') return same.length > 1 ? `${w.ht} ${n}` : w.ht;
  if (u.kind === 'gate') return w.gate;
  return w.ext;
}

/** The heading of a live AMS-like unit: an Anycubic unit by its own source (ACE n by firmware box id, or the spool holder), else by the printer's label. */
export function liveUnitName(lv: LivePrinter, u: LiveUnit, w: Words): string {
  if (u.source === 'holder') return w.holder;
  if (u.source === 'ace') return `${w.ace} ${(u.box ?? Number(u.id)) + 1}`;
  const ams = lv.units.filter(x => x.kind === 'ams');
  return lv.unit_label && lv.units.length === 1 ? lv.unit_label : `${lv.unit_label || w.ams} ${ams.indexOf(u) + 1}`;
}

/** The 0-based slot a spool link names: Kobra Control's unit id * 4 + slot (ACE 0-3, the holder after the last ACE), U1 Control's toolhead number. */
export const linkSlot = (lv: LivePrinter, u: LiveUnit, i: number) => (lv.bind === 'S' ? Number(u.id) * 4 + i : i);

export function slotName(lv: LivePrinter, u: LiveUnit | null, i: number, ext: boolean, w: Words): string {
  if (ext || !u) return w.externalShort;
  if (lv.heads) return w.head(i + 1);
  if (u.kind === 'ht') return w.ht;
  return w.slot(liveUnitName(lv, u, w), i + 1);
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
      const where = u.kind === 'ext' ? w.externalShort : u.kind === 'gate' ? w.gateN(si + 1) : u.kind === 'ht' || u.kind === 'tool' ? unitLabel(p, u, w) : w.slot(unitLabel(p, u, w), si + 1);
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
export function addUnit(p: ManualPrinter, kind: UnitKind): ManualPrinter {
  if (!KINDS[kind] || p.units.length >= MAX_UNITS || (kind === 'ext' && p.units.some(u => u.kind === 'ext'))) return p;
  const units = [...p.units, { kind, slots: new Array(KINDS[kind]).fill(null) }].sort((x, y) => RANK[x.kind] - RANK[y.kind]);
  return { ...p, units };
}
