import { reactive, watch } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, on, setTab } from './main';
import { t } from '../core/i18n';
import type { RfidOffer } from '../logic/rfid';

// The spool whose detail is open beside the list, and the action form open in it (Spoolman only). `id` is the
// spool the user picked; with none picked the list shows its first spool until the user closes the detail.
// Every action is sent with the list origin it was chosen from, so the plugin refuses it if the source changed.
// `stack`: the spools of a stack (×n) whose list is open in the detail; a spool picked from it keeps it for "Back".
export type MenuMode = '' | 'weigh' | 'use' | 'remain' | 'note' | 'move';
export const menu = reactive({ stack: null as number[] | null, id: null as number | null, picks: 0, auto: true, shown: null as number | null, from: '', mode: '' as MenuMode, val: '', detail: null as any });
on('detail', d => { if (d && menu.shown === d.id) menu.detail = d; });

export function pickSpool(id: number, fromStack = false): void {
  Object.assign(menu, { id, auto: true, picks: menu.picks + 1, ...(fromStack ? {} : { stack: null }) });
  if (waiting === id) askDetail(id);   // already shown as the first row, its request still waiting: send it now
}
export function pickStack(ids: number[]): void { Object.assign(menu, { stack: ids, id: null, auto: false, picks: menu.picks + 1, mode: '', val: '' }); }
export function closeDetail(): void { Object.assign(menu, { stack: null, id: null, auto: false, mode: '', val: '' }); }
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

// ------------------------------------------------------------------ spool editor (Add Spool, Edit Spool)
// The plugin answers "editor" with Spoolman's extra-field definitions, filaments, vendors and (for an edit) the spool as
// Spoolman has it now; a save or create answers like any card action. The editor stays open on a refusal, showing why.
export const editor = reactive({ open: false, id: null as number | null, data: null as any, busy: false, error: '', made: null as number | null, ref: 0,
  rfid: null as null | { offer: RfidOffer; where: string } });
// Each editor opened gets its own ref, which the plugin sends back: an answer for an editor closed since never touches the next one.
// rfid: Add Spool for a new RFID spool in a printer slot, pre-filled from the printer; its tag goes with the create.
export function openEditor(id: number | null, rfid: { offer: RfidOffer; where: string } | null = null): void {
  Object.assign(editor, { open: true, id, data: null, busy: false, error: '', made: null, ref: editor.ref + 1, rfid: id == null ? rfid : null });
  bridge.postMain({ type: 'spool_action', action: 'editor', ...(id == null ? {} : { id }), origin: m.origin, ref: editor.ref });
}
export function submitEditor(message: Record<string, unknown>): void {
  Object.assign(editor, { busy: true, error: '' });
  bridge.postMain({ type: 'spool_action', origin: m.origin, ...(editor.id == null ? {} : { id: editor.id }), ...message, ref: editor.ref });
  note('pending', t('action.sending'), 'spool-action');
}
// Edit Spool > Based on > Change: the plugin remembers the parent preset for the filament on that printer (null forgets it)
// and answers with the rows again; the presets are rebuilt on the refresh that follows every spool action.
export function pickParent(filament: number | null, target: string, name: string | null, ofd?: string): void {
  if (filament == null) return;
  Object.assign(editor, { busy: true, error: '' });
  bridge.postMain({ type: 'spool_action', action: 'match_parent', filament, target, name, ...(ofd ? { ofd } : {}), origin: m.origin, ref: editor.ref });
}
on('editor', d => {
  if (!editor.open || d.ref !== editor.ref) return;
  if (d.action === 'match_parent') { editor.busy = false; if (d.ok && editor.data) editor.data.preset_match = d.match; else if (!d.ok) editor.error = d.text || t('common.unknownError'); return; }
  if (d.action === 'editor') { if (d.ok) editor.data = d.editor; else editor.error = d.text || t('common.unknownError'); return; }
  editor.busy = false;
  if (d.ok) { editor.open = false; return; }
  editor.error = d.text || t('common.unknownError');
  // A new filament was made but the spool refused: it is the existing filament now, so a retry makes no second one.
  if (typeof d.filament === 'number') editor.made = d.filament;
});
