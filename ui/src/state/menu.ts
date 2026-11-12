import { reactive } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, on } from './main';
import { t } from '../core/i18n';

// One spool's action panel open at a time (Spoolman only). Every action is sent with the list origin it was
// chosen from, so the plugin refuses it if the spool source changed meanwhile.
export const menu = reactive({ id: null as number | null, mode: '' as '' | 'weigh' | 'use' | 'move' | 'detail', val: '', detail: null as any });
on('detail', d => { if (menu.mode === 'detail' && menu.id === d?.id) menu.detail = d; });

export function openMenu(id: number): void {
  if (menu.id === id) { closeMenu(); return; }
  Object.assign(menu, { id, mode: '', val: '', detail: null });
}
export function closeMenu(): void { Object.assign(menu, { id: null, mode: '', val: '', detail: null }); }
export function setMode(mode: typeof menu.mode, val = ''): void {
  Object.assign(menu, { mode, val, detail: null });
  if (mode === 'detail' && menu.id != null) bridge.postMain({ type: 'spool_detail', id: menu.id });
  if (mode === 'move') bridge.postMain({ type: 'spool_action', action: 'locations' });
}
export function sendAction(action: string, extra: Record<string, unknown> = {}): void {
  if (menu.id == null) return;
  bridge.postMain({ type: 'spool_action', action, id: menu.id, origin: m.origin, ...extra });
  note('pending', t('action.sending'), 'spool-action');
  closeMenu();
}
