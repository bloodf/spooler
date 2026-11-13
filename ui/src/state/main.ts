import { computed, reactive } from 'vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { t } from '../core/i18n';
import { computeDupes, type Spool } from '../logic/spools';
import { computeInUse, liveSig, type LivePrinter, type ManualPrinter, type Words } from '../logic/printers';

export interface UsageRow { slot: number; grams: number; colour?: string; material?: string; label?: string; spool?: number | null;
  how?: string; state?: string; error?: string; op?: string }
export interface UsagePrint { id: string; name: string; printer: string; result: string; pct?: number; time: number; state: string;
  late?: boolean; rows: UsageRow[] }
export interface Usage { enabled: boolean; mode: 'ask' | 'auto' | 'off'; prints: UsagePrint[]; notice?: string }
export interface PlateRow { status: string; colour: string; slots: string; name: string; meta: string; fill: number; spool_colour: string;
  need_pct: number; headline: string; detail: string; ids: number[]; first: number }
export interface Note { id: number; kind: 'error' | 'unknown' | 'success' | 'info' | 'pending'; text: string; key?: string; at: number }

export const PENDING_TIMEOUT_MS = 30_000;
export const SUCCESS_MS = 8_000;

export const m = reactive({
  received: false,
  spools: [] as Spool[],
  origin: null as number | null,
  source: 'spoolman' as string,
  loadError: '',
  errorCode: '',
  loadedAt: 0,
  profiles: {} as { count?: number; error?: string },
  low: boot.low_stock_default,
  wMode: 'both' as 'grams' | 'percent' | 'both',
  disp: { ...boot.display_defaults } as Record<string, boolean>,
  cart: false,
  columns: 1 as 1 | 2,
  cfg: [] as ManualPrinter[],
  printersRev: 0,
  showPrinterTab: true,
  liveOn: false,
  live: { status: 'off', printers: [] as LivePrinter[], links: {} as Record<string, string> },
  liveKey: '',
  usage: { enabled: false, mode: 'ask', prints: [] } as Usage,
  usageNotice: '',
  progress: { ...boot.settings.progress },
  stats: { ...boot.settings.stats },
  plate: null as null | { rows: PlateRow[]; time?: string },
  peers: { u1control: false },
  locations: [] as string[],
  moonNote: null as null | { id: string; ok: boolean; text: string },
  notes: [] as Note[],
  now: Date.now(),
  tab: readTab(),
  view: boot.view as 'main' | 'settings',
});

function readTab(): 'spools' | 'printer' | 'stats' {
  try { const v = localStorage.getItem('spooler.tab'); if (v === 'printer' || v === 'stats') return v; } catch { /* per viewer */ }
  return 'spools';
}
export function setTab(v: 'spools' | 'printer' | 'stats'): void {
  m.tab = v;
  try { localStorage.setItem('spooler.tab', v); } catch { /* per viewer */ }
  if (v === 'printer') pollLive();
}

// ------------------------------------------------------------------ status region (B-20)
let nextNote = 0;
const timers = new Map<number, number>();
export function note(kind: Note['kind'], text: string, key?: string): number {
  if (key) for (const n of m.notes.filter(n => n.key === key)) dismiss(n.id);   // one note per action
  const id = ++nextNote;
  m.notes.push({ id, kind, text, key, at: Date.now() });
  if (kind === 'success' || kind === 'info') timers.set(id, window.setTimeout(() => dismiss(id), SUCCESS_MS));
  if (kind === 'pending') timers.set(id, window.setTimeout(() => {
    if (m.notes.some(n => n.id === id)) { dismiss(id); note('unknown', t('status.noAnswer', { action: text }), key); }
  }, PENDING_TIMEOUT_MS));
  return id;
}
export function dismiss(id: number): void {
  const i = m.notes.findIndex(n => n.id === id);
  if (i >= 0) m.notes.splice(i, 1);
  clearTimeout(timers.get(id));
  timers.delete(id);
}
export const pending = (key: string) => m.notes.some(n => n.key === key && n.kind === 'pending');
/** A reply for an action: replaces its pending note; errors stay until dismissed. */
export function settle(key: string, ok: boolean, text: string): void {
  note(ok ? 'success' : 'error', text, key);
}

// ------------------------------------------------------------------ derived
export const words = computed<Words>(() => ({
  ams: t('printer.ams'), ht: t('printer.ht'), ext: t('printer.external'), externalShort: t('printer.externalShort'),
  slot: (unit, n) => t('printer.slotOf', { unit, n }), head: n => `T${n}`,
}));
export const inUse = computed(() => computeInUse(m.live.printers, m.cfg, words.value));
export const dupes = computed(() => computeDupes(m.spools));
export const plateSlots = computed(() => {
  const slots = new Map<number, string>(), order = new Map<number, number>();
  for (const row of m.plate?.rows ?? []) for (const id of row.ids) {
    slots.set(id, slots.has(id) ? `${slots.get(id)}, ${row.slots}` : row.slots);
    if (!order.has(id) || row.first < (order.get(id) as number)) order.set(id, row.first);
  }
  return { slots, order };
});
export const plateAttention = computed(() => (m.plate?.rows ?? []).filter(r => ['barely', 'mixed', 'short'].includes(r.status)).length);
export const usageAttention = computed(() => m.usage.enabled && m.usage.prints.some(p => p.state === 'pending' || p.state === 'unknown'));
export const statsOn = computed(() => m.stats.on && m.usage.enabled);
/** S02: why actions that need the spool source are off ('' when they can run). */
export const sourceOff = computed(() => {
  if (!m.received) return t('status.waitingList');
  if (m.errorCode === 'no_url') return t('list.noUrl.short');
  if (m.loadError && !m.spools.length) return t('list.readFailed.short');
  return '';
});

// ------------------------------------------------------------------ messages
const listeners = { plate: new Set<() => void>(), detail: new Set<(d: any) => void>(), stats: new Set<(d: any) => void>(),
  statsExport: new Set<(d: any) => void>() };
export const on = <K extends keyof typeof listeners>(k: K, h: Parameters<(typeof listeners)[K]['add']>[0]) => {
  (listeners[k] as Set<any>).add(h); return () => (listeners[k] as Set<any>).delete(h);
};

function render(p: any): void {
  m.received = true;
  m.peers = { u1control: !!p.peers?.u1control };
  if (!p.ok) {
    m.loadError = p.error || t('common.unknownError');
    m.errorCode = p.error_code || 'read_failed';
    // The last list stays, marked as old, only when it came from the same spool source (F10).
    if (typeof p.origin !== 'number' || p.origin !== m.origin) { m.spools = []; m.origin = null; }
    return;
  }
  m.loadError = ''; m.errorCode = '';
  m.loadedAt = Date.now();
  m.spools = p.spools || [];
  m.origin = typeof p.origin === 'number' ? p.origin : null;
  if (typeof p.source === 'string') m.source = p.source;
  if (p.profiles) m.profiles = p.profiles;
  if (typeof p.low_stock_grams === 'number') m.low = p.low_stock_grams;
  if (typeof p.weight_display === 'string') m.wMode = p.weight_display;
  if (p.display && typeof p.display === 'object') m.disp = { ...boot.display_defaults, ...p.display };
  if (typeof p.show_cart === 'boolean') m.cart = p.show_cart;
  if (p.spool_columns) m.columns = p.spool_columns === 2 ? 2 : 1;
  if (Array.isArray(p.printers)) m.cfg = p.printers;
  if (typeof p.printers_rev === 'number') m.printersRev = p.printers_rev;
  if (typeof p.show_printer_tab === 'boolean') m.showPrinterTab = p.show_printer_tab;
  m.liveOn = p.live_ok === true;
  if (p.usage) setUsage(p.usage, false);
  if (p.progress) m.progress = p.progress;
  if (p.stats) m.stats = p.stats;
  if (m.liveOn) pollLive();
}

let usageBusy = '';
export const usageState = reactive({ booking: '' as string, undoing: false });
export function setUsage(u: Usage, done: boolean): void {
  m.usage = u;
  if (done && (usageState.booking || usageState.undoing)) {
    usageState.booking = ''; usageState.undoing = false; usageBusy = '';
    bridge.postMain({ type: 'refresh' });
  }
}

function onMessage(d: any): void {
  if (d.view === 'settings' || d.type === 'show_view') return;   // the Settings view's own messages
  switch (d.type) {
    case 'spools': render(d); break;
    case 'plate': m.plate = Array.isArray(d.rows) && d.rows.length ? { rows: d.rows, time: d.time } : null; listeners.plate.forEach(h => h()); break;
    case 'plate_clear': m.plate = null; listeners.plate.forEach(h => h()); break;
    case 'usage': m.usageNotice = d.usage?.notice || ''; setUsage(d.usage, true); if (m.tab === 'stats') askStats(); break;
    case 'spool_detail': listeners.detail.forEach(h => h(d.detail)); break;
    case 'stats_export': listeners.statsExport.forEach(h => h(d)); break;
    case 'stats': listeners.stats.forEach(h => h(d.stats)); break;
    case 'spool_changed': bridge.postMain({ type: 'refresh' }); break;
    case 'action_result':
      if (d.action === 'locations') { m.locations = d.ok ? d.locations || [] : []; return; }
      if (d.text) settle('spool-action', !!d.ok, d.text); else for (const n of m.notes.filter(n => n.key === 'spool-action')) dismiss(n.id);
      bridge.postMain({ type: 'refresh' });
      break;
    case 'moon_spool':
      m.moonNote = { id: d.id, ok: !!d.ok, text: d.text || '' };
      settle('moon:' + d.id, !!d.ok, d.text || '');
      break;
    case 'sent': settle('send', !!d.ok, d.text || ''); break;
    case 'live': {
      // Spooler changed the saved printers itself (a slice filled the toolheads): take them, or the next edit saves over it.
      if (typeof d.printers_rev === 'number' && d.printers_rev !== m.printersRev) { m.printersRev = d.printers_rev; if (Array.isArray(d.printers)) m.cfg = d.printers; }
      const key = liveSig(d.live);
      if (key !== m.liveKey) { m.liveKey = key; m.live = d.live; }
      if (d.usage) setUsage(d.usage, false);
      break;
    }
  }
}

export function pollLive(): void {
  if (m.liveOn && m.showPrinterTab && m.tab === 'printer' && m.view === 'main') bridge.postMain({ type: 'live' });
}
export const askStats = () => bridge.postMain({ type: 'stats', period: statsPeriod() });
export function statsPeriod(): string {
  try { return localStorage.getItem('spooler.period') || '30'; } catch { return '30'; }
}

export function start(): () => void {
  bridge.attach();
  const off = bridge.onMessage(onMessage);
  bridge.postMain({ type: 'ready' });
  const ids = [
    window.setInterval(() => bridge.postMain({ type: 'refresh' }), boot.refresh_ms),
    // Lets the plugin send preset edits made in OrcaSlicer to Spoolman soon after they are made.
    window.setInterval(() => bridge.postMain({ type: 'tick' }), 10_000),
    window.setInterval(pollLive, 5000),
    window.setInterval(() => { if (m.liveOn && m.usage.enabled && m.tab !== 'printer') bridge.postMain({ type: 'live' }); }, 30_000),
    window.setInterval(() => { m.now = Date.now(); }, 30_000),
  ];
  return () => { off(); ids.forEach(clearInterval); };
}
export { usageBusy };
