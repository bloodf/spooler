import { reactive, watch } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, on, setTab } from './main';
import { t } from '../core/i18n';

// The spool whose detail is open beside the list, and the action form open in it (Spoolman only). `id` is the
// spool the user picked; with none picked the list shows its first spool until the user closes the detail.
// Every action is sent with the list origin it was chosen from, so the plugin refuses it if the source changed.
export type MenuMode = '' | 'weigh' | 'use' | 'remain' | 'note' | 'move';
export const menu = reactive({ id: null as number | null, picks: 0, auto: true, shown: null as number | null, from: '', mode: '' as MenuMode, val: '', detail: null as any });
on('detail', d => { if (d && menu.shown === d.id) menu.detail = d; });

export function pickSpool(id: number): void {
  Object.assign(menu, { id, auto: true, picks: menu.picks + 1 });
  if (waiting === id) askDetail(id);   // already shown as the first row, its request still waiting: send it now
}
export function closeDetail(): void { Object.assign(menu, { id: null, auto: false, mode: '', val: '' }); }
/** From another tab: open the Spools tab on this spool. */
export function showSpool(id: number): void { pickSpool(id); setTab('spools'); }
/**
 * The detail now shows this spool (or none): its print history is asked from the plugin, which only has it for
 * Spoolman. A spool the user picked is asked at once; the list's first row, which changes with every search
 * keystroke, sort or filter, only once the list settled (DETAIL_SETTLE_MS) and only if it is still the one shown.
 */
export const DETAIL_SETTLE_MS = 300;
let settle: ReturnType<typeof setTimeout> | undefined;
let waiting: number | null = null;
function askDetail(id: number): void {
  clearTimeout(settle);
  waiting = null;
  // Still the spool shown, from the source it was shown for, and that source has a history (Spoolman only).
  if (menu.shown === id && menu.from === m.source && m.source === 'spoolman') bridge.postMain({ type: 'spool_detail', id });
}
/**
 * The shown spool changed in Spoolman (an action of ours settled, or a newer list arrived): ask its history and
 * "Lasts about" again. The old answer stays on screen until the new one comes, and a burst (an action's result,
 * then the list it refreshes) makes one request.
 */
export function refreshDetail(): void {
  const id = menu.shown;
  if (id == null || menu.from !== m.source || m.source !== 'spoolman') return;
  clearTimeout(settle);
  waiting = id;
  settle = setTimeout(() => askDetail(id), DETAIL_SETTLE_MS);
}
on('actionOk', refreshDetail);
watch(() => m.loadedAt, refreshDetail);
/** Ids are only unique within one source: a spool shown for another source is a different spool. */
export function shownSpool(id: number | null): void {
  if (menu.shown === id && menu.from === m.source) return;
  Object.assign(menu, { shown: id, from: m.source, mode: '', val: '', detail: null });
  clearTimeout(settle);
  waiting = null;
  if (id == null || m.source !== 'spoolman') return;
  if (menu.id === id) { askDetail(id); return; }
  waiting = id;
  settle = setTimeout(() => askDetail(id), DETAIL_SETTLE_MS);
}
export function setMode(mode: MenuMode, val = ''): void {
  Object.assign(menu, { mode, val });
  if (mode === 'move') bridge.postMain({ type: 'spool_action', action: 'locations' });
}
export function sendAction(action: string, extra: Record<string, unknown> = {}): void {
  if (menu.shown == null) return;
  bridge.postMain({ type: 'spool_action', action, id: menu.shown, origin: m.origin, ...extra });
  note('pending', t('action.sending'), 'spool-action');
  Object.assign(menu, { mode: '', val: '' });
}
