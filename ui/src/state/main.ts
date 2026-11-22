import { computed, reactive, ref } from 'vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { t } from '../core/i18n';
import { autoRefresh, cleanEvery, userBusy } from '../core/autorefresh';
import { useToast } from '@orca-plugins/ui-foundation/src/components';
import { computeDupes, type Spool } from '../logic/spools';
import { computeInUse, liveSig, type LivePrinter, type ManualPrinter, type SlicePick, type Words } from '../logic/printers';
import type { RfidOffer } from '../logic/rfid';

export interface UsageRow { slot: number; grams: number; colour?: string; material?: string; label?: string; spool?: number | null;
  how?: string; state?: string; error?: string; op?: string }
export interface UsagePrint { id: string; name: string; printer: string; result: string; pct?: number; time: number; state: string;
  late?: boolean; rows: UsageRow[] }
export interface Usage { enabled: boolean; mode: 'ask' | 'auto' | 'off'; prints: UsagePrint[]; notice?: string }
export interface PlateRow { status: string; colour: string; slots: string; name: string; meta: string; fill: number; spool_colour: string;
  need_pct: number; headline: string; detail: string; ids: number[]; first: number }
export interface CalibChange { key: string; old: string; new: string; unit?: string }
export interface CalibAsk { name: string; changes: CalibChange[] }
export type NoteKind = 'error' | 'unknown' | 'success' | 'info' | 'pending';

export const PENDING_TIMEOUT_MS = 30_000;

export const m = reactive({
  received: false,
  spools: [] as Spool[],
  origin: null as number | null,
  source: 'spoolman' as string,
  loadError: '',
  errorCode: '',
  readFails: 0,   // failed reads in a row: one can be a blip, so a shown list keeps its actions until the second
  loadedAt: 0,
  profiles: {} as { count?: number; error?: string },
  low: boot.low_stock_default,
  wMode: 'both' as 'grams' | 'percent' | 'both',
  disp: { ...boot.display_defaults } as Record<string, boolean>,
  cart: false,
  columns: 1 as 1 | 2,
  listView: null as null | 'table' | 'cards',   // Settings > Spool list default (null until the plugin says)
  viewPick: readView(),                         // this viewer's own pick on the list (localStorage)
  cfg: [] as ManualPrinter[],
  printersRev: 0,
  slicePicks: [] as SlicePick[],
  sliceMap: {} as Record<string, string>,
  printerPresets: [] as string[],
  showPrinterTab: true,
  liveOn: false,
  live: { status: 'off', printers: [] as LivePrinter[], links: {} as Record<string, string> },
  liveKey: '',
  rfid: [] as RfidOffer[],   // Bambu RFID spools no Spoolman spool carries (RfidPanel)
  usage: { enabled: false, mode: 'ask', prints: [] } as Usage,
  progress: { ...boot.settings.progress },
  stats: { ...boot.settings.stats },
  plate: null as null | { rows: PlateRow[]; time?: string },
  calibration: [] as CalibAsk[],
  peers: { u1control: false },
  locations: [] as string[],
  now: Date.now(),
  tab: readTab(),
  view: boot.view as 'main' | 'settings',
  refreshS: cleanEvery(boot.settings.refresh_s),   // Settings > Refresh Spoolman every (0 = off)
  retrying: false,                                // the timed re-reads failed: "Spoolman unreachable, retrying"
});

function readTab(): 'spools' | 'printer' | 'stats' {
  try { const v = localStorage.getItem('spooler.tab'); if (v === 'printer' || v === 'stats') return v; } catch { /* per viewer */ }
  return 'spools';
}
function readView(): 'table' | 'cards' | null {
  try { const v = localStorage.getItem('spooler.view'); return v === 'table' || v === 'cards' ? v : null; } catch { return null; }
}
export function setListView(v: 'table' | 'cards' | null): void {
  m.viewPick = v;
  try { if (v) localStorage.setItem('spooler.view', v); else localStorage.removeItem('spooler.view'); } catch { /* per viewer */ }
}
export function setTab(v: 'spools' | 'printer' | 'stats'): void {
  m.tab = v;
  try { localStorage.setItem('spooler.tab', v); } catch { /* per viewer */ }
  if (v === 'printer') pollLive();
}

// ------------------------------------------------------------------ toasts (B-20)
// Every action result is a toast in the page's one host (App.vue). An action waiting for its answer keeps its key in
// `waits` (its buttons show busy); the answer replaces the waiting toast, or after 30 s a "result unknown" one does.
const toast = useToast();
const waits = reactive(new Map<string, number>());
const TONE = { error: 'error', unknown: 'warn', success: 'success', info: 'info', pending: 'info' } as const;
function stopWait(key: string): void { clearTimeout(waits.get(key)); waits.delete(key); }
export function note(kind: NoteKind, text: string, key?: string): void {
  if (key) stopWait(key);
  if (kind === 'pending' && key) waits.set(key, window.setTimeout(() => { waits.delete(key); note('unknown', t('status.noAnswer', { action: text }), key); }, PENDING_TIMEOUT_MS));
  const said = kind === 'error' ? t('status.errorPrefix') : kind === 'unknown' ? t('status.unknownPrefix') : '';
  // An unknown outcome stays until closed, like an error: the user has to check Spoolman before trying again. A waiting
  // toast stays until its answer (or the "result unknown" one) replaces it, however long that takes.
  const stays = kind === 'unknown' || (kind === 'pending' && !!key);
  toast.show({ tone: TONE[kind], title: said || text, ...(said ? { body: text } : {}), ...(key ? { key } : {}), ...(stays ? { timeout: 0 } : {}) });
}
/** Forgets an action's waiting state and its toast (the plugin answered without a result to show). */
export function quiet(key: string): void {
  stopWait(key);
  for (const x of toast.list.list.filter(x => x.key === key)) toast.dismiss(x.id);
}
export const pending = (key: string) => waits.has(key);
/** A reply for an action: replaces its waiting toast; errors stay until closed. */
export function settle(key: string, ok: boolean, text: string): void {
  note(ok ? 'success' : 'error', text, key);
}

// ------------------------------------------------------------------ derived
export const words = computed<Words>(() => ({
  ams: t('printer.ams'), ht: t('printer.ht'), ext: t('printer.external'), gate: t('printer.gates'), gateN: n => t('printer.gateN', { n }), externalShort: t('printer.externalShort'),
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
/** S02: why actions that need the spool source are off ('' when they can run). A source that failed two reads in a
 * row turns them off too, even with the old list still shown; the next good read turns them back on. */
export const sourceOff = computed(() => {
  if (!m.received) return t('status.waitingList');
  if (m.errorCode === 'no_url') return t('list.noUrl.short');
  if (m.loadError && (!m.spools.length || m.readFails >= 2)) return t('list.readFailed.short');
  return '';
});

// ------------------------------------------------------------------ messages
const listeners = { actionOk: new Set<() => void>(), plate: new Set<() => void>(), detail: new Set<(d: any) => void>(), stats: new Set<(d: any) => void>(),
  statsExport: new Set<(d: any) => void>(), moonConfirm: new Set<(d: any) => void>(), editor: new Set<(d: any) => void>() };
export const on = <K extends keyof typeof listeners>(k: K, h: Parameters<(typeof listeners)[K]['add']>[0]) => {
  (listeners[k] as Set<any>).add(h); return () => (listeners[k] as Set<any>).delete(h);
};

function render(p: any): void {
  m.received = true;
  if (p.refresh_s !== undefined && cleanEvery(p.refresh_s) !== m.refreshS) { m.refreshS = cleanEvery(p.refresh_s); auto?.restart(); }
  answered?.(!!p.ok || p.error_code === 'no_url');   // no address yet is not Spoolman being unreachable
  m.peers = { u1control: !!p.peers?.u1control };
  m.readFails = p.ok ? 0 : m.readFails + 1;
  if (!p.ok) {
    m.loadError = p.error || t('common.unknownError');
    m.errorCode = p.error_code || 'read_failed';
    // Settled here, not by watching loadError: the same error twice in a row would never settle the toast.
    if (pending('refresh')) note('error', t('list.readFailedAt', { error: m.loadError }), 'refresh');
    // The last list stays, marked as old, only when it came from the same spool source (F10).
    if (typeof p.origin !== 'number' || p.origin !== m.origin) { m.spools = []; m.origin = null; }
    return;
  }
  m.loadError = ''; m.errorCode = '';
  m.loadedAt = Date.now();
  if (pending('refresh')) note('success', t('list.refreshed'), 'refresh');
  m.spools = p.spools || [];
  m.origin = typeof p.origin === 'number' ? p.origin : null;
  if (typeof p.source === 'string') m.source = p.source;
  if (p.profiles) m.profiles = p.profiles;
  if (typeof p.low_stock_grams === 'number') m.low = p.low_stock_grams;
  if (typeof p.weight_display === 'string') m.wMode = p.weight_display;
  if (p.display && typeof p.display === 'object') m.disp = { ...boot.display_defaults, ...p.display };
  if (typeof p.show_cart === 'boolean') m.cart = p.show_cart;
  if (p.spool_columns) m.columns = p.spool_columns === 2 ? 2 : 1;
  if (p.spool_view) {
    const v = p.spool_view === 'cards' ? 'cards' : 'table';
    if (m.listView && v !== m.listView) setListView(null);   // a new default in Settings wins over the old pick
    m.listView = v;
  }
  if (Array.isArray(p.printers)) m.cfg = p.printers;
  if (typeof p.printers_rev === 'number') m.printersRev = p.printers_rev;
  if (Array.isArray(p.slice_picks)) m.slicePicks = p.slice_picks;
  if (p.slice_map && typeof p.slice_map === 'object') m.sliceMap = p.slice_map;
  if (Array.isArray(p.printer_presets)) m.printerPresets = p.printer_presets;
  if (typeof p.show_printer_tab === 'boolean') m.showPrinterTab = p.show_printer_tab;
  m.liveOn = p.live_ok === true;
  if (p.usage) setUsage(p.usage, false);
  if (Array.isArray(p.calibration)) setCalibration(p.calibration);
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
    case 'calibration': setCalibration(Array.isArray(d.asks) ? d.asks : []); break;
    case 'plate_clear': m.plate = null; listeners.plate.forEach(h => h()); break;
    case 'usage': if (d.usage?.notice) note('error', d.usage.notice, 'usage'); setUsage(d.usage, true); if (m.tab === 'stats') askStats(); break;
    case 'spool_detail': listeners.detail.forEach(h => h(d.detail)); break;
    case 'stats_export': listeners.statsExport.forEach(h => h(d)); break;
    case 'stats': listeners.stats.forEach(h => h(d.stats)); break;
    case 'spool_changed': bridge.postMain({ type: 'refresh' }); break;
    case 'action_result':
      if (d.action === 'locations') { m.locations = d.ok ? d.locations || [] : []; return; }
      if (d.action === 'editor' || d.action === 'create' || d.action === 'save' || d.action === 'match_parent') listeners.editor.forEach(h => h(d));
      if (d.action === 'editor') return;
      if (d.text) settle('spool-action', !!d.ok, d.text); else quiet('spool-action');
      if (d.ok) listeners.actionOk.forEach(h => h());
      bridge.postMain({ type: 'refresh' });
      break;
    case 'moon_spool':
      // The printer is printing: the plugin changed nothing and asks first (state/printers.ts).
      if (d.confirm) { quiet('moon:' + d.id); listeners.moonConfirm.forEach(h => h(d)); break; }
      settle('moon:' + d.id, !!d.ok, d.text || '');
      break;
    case 'sent': settle('send', !!d.ok, d.text || ''); break;
    case 'live': {
      // Spooler changed the saved printers itself (a slice filled the toolheads): take them, or the next edit saves over it.
      if (typeof d.printers_rev === 'number' && d.printers_rev !== m.printersRev) { m.printersRev = d.printers_rev; if (Array.isArray(d.printers)) m.cfg = d.printers; }
      if (Array.isArray(d.slice_picks)) m.slicePicks = d.slice_picks;
      if (Array.isArray(d.printer_presets)) m.printerPresets = d.printer_presets;
      const key = liveSig(d.live);
      if (key !== m.liveKey) { m.liveKey = key; m.live = d.live; }
      m.rfid = Array.isArray(d.rfid) ? d.rfid : [];
      if (d.usage) setUsage(d.usage, false);
      break;
    }
  }
}

// ------------------------------------------------------------------ page actions (app bar and list toolbar)
export function refresh(): void { bridge.postMain({ type: 'refresh' }); note('pending', t('list.refreshing'), 'refresh'); }
export function syncPresets(): void { note('pending', t('list.syncing'), 'send'); bridge.postMain({ type: 'sync_presets' }); }
/** Send to Spoolman for one of a spool's OrcaSlicer presets (picked in its detail), never the one last opened in OrcaSlicer. */
export function sendEdits(spool: number, preset: string): void { note('pending', t('list.sending'), 'send'); bridge.postMain({ type: 'send', spool, preset }); }
/** Waiting calibrated values; a new one is also announced in the status region (the panel itself isn't a live region). */
function setCalibration(asks: CalibAsk[]): void {
  const known = new Set(m.calibration.map(a => a.name));
  if (asks.some(a => !known.has(a.name))) note('info', t('cal.announce'));
  m.calibration = asks;
}
/** Save or Skip one waiting set of calibrated values (only Save writes to Spoolman). */
export function answerCalibration(name: string, save: boolean): void {
  if (save) note('pending', t('cal.saving'), 'send');
  else m.calibration = m.calibration.filter(a => a.name !== name);
  bridge.postMain({ type: save ? 'calibration_save' : 'calibration_skip', name });
}
/** The settings page a link asked for (s-src, ...), opened once Settings shows; '' = the remembered page. */
export const settingsPage = ref('');
export const openSettings = (page = ''): void => { settingsPage.value = page; bridge.postMain({ type: 'settings', ...(page ? { page } : {}) }); };

// Timed re-reads of the spool list (and with it the Printer tab's links and Stats): one at a time, answered by the
// next spools message, paused while hidden (core/autorefresh.ts). The Spoolman WebSocket and the peers' link
// signal still refresh at once.
let auto: ReturnType<typeof autoRefresh> | null = null;
let answered: ((ok: boolean) => void) | null = null;
function timedRead(): Promise<boolean> {
  return new Promise(resolve => {
    const timer = window.setTimeout(() => { answered = null; resolve(false); }, PENDING_TIMEOUT_MS);
    answered = ok => { window.clearTimeout(timer); answered = null; if (ok && m.tab === 'stats') askStats(); resolve(ok); };
    bridge.postMain({ type: 'refresh' });
  });
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
  auto = autoRefresh({ load: timedRead, every: () => m.refreshS, held: () => m.view !== 'main' || userBusy(), onFailing: f => { m.retrying = f; } });
  const ids = [
    // Lets the plugin send preset edits made in OrcaSlicer to Spoolman soon after they are made.
    window.setInterval(() => bridge.postMain({ type: 'tick' }), 10_000),
    window.setInterval(pollLive, 5000),
    window.setInterval(() => { if (m.liveOn && m.usage.enabled && m.tab !== 'printer') bridge.postMain({ type: 'live' }); }, 30_000),
    window.setInterval(() => { m.now = Date.now(); }, 30_000),
  ];
  return () => { off(); auto?.stop(); auto = null; ids.forEach(clearInterval); };
}
export { usageBusy };
