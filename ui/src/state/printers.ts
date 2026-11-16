import { reactive } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, on, pollLive } from './main';
import { t } from '../core/i18n';
import { ask } from '../core/dialog';
import { addUnit, mapPresets, newPrinterId, withGates, type ManualPrinter, type PrinterType, type SlicePick, type UnitKind } from '../logic/printers';

// Manual printers are edited as new arrays (never in place) and saved whole, as the previous page did.
export const ui = reactive({ picking: null as null | { p: string; u?: number; s?: number; moon?: boolean }, renaming: '', linkOpen: '' });

export function savePrinters(next: ManualPrinter[]): void {
  m.cfg = next;
  bridge.postMain({ type: 'printers', printers: JSON.parse(JSON.stringify(next)) });
}
const update = (id: string, fn: (p: ManualPrinter) => ManualPrinter) => savePrinters(m.cfg.map(p => (p.id === id ? fn(p) : p)));

export function addPrinter(): string {
  const id = newPrinterId();
  savePrinters([...m.cfg, { id, name: m.cfg.length ? t('printer.defaultNameN', { n: m.cfg.length + 1 }) : t('printer.defaultName'), units: [] }]);
  ui.renaming = id;
  return id;
}
export const rename = (id: string, name: string) => update(id, p => ({ ...p, name: name.trim().slice(0, 40) || p.name }));
export const addUnitTo = (id: string, kind: UnitKind) => update(id, p => addUnit(p, kind));
export const removeUnit = (id: string, ui_: number) => update(id, p => ({ ...p, units: p.units.filter((_, i) => i !== ui_) }));
export const removePrinter = (id: string) => savePrinters(m.cfg.filter(p => p.id !== id));
export const setSlot = (id: string, u: number, s: number, spool: string | null) => update(id, p => ({
  ...p, units: p.units.map((x, i) => (i === u ? { ...x, slots: x.slots.map((v, j) => (j === s ? spool : v)) } : x)) }));

export const setGates = (id: string, n: number) => update(id, p => withGates(p, n));
export const setSliceFill = (id: string, on: boolean) => update(id, p => ({ ...p, slice_fill: on }));
/** Which OrcaSlicer printer presets a slice fills this printer for. */
export function setPresets(id: string, presets: string[]): void {
  m.sliceMap = mapPresets(m.sliceMap, id, presets);
  bridge.postMain({ type: 'slice_map', map: { ...m.sliceMap } });
}
/** The answer to a slice pick: a spool for the slot, or null to leave it as it is. */
export function answerPick(pick: SlicePick, spool: number | null): void {
  m.slicePicks = m.slicePicks.filter(x => x !== pick);
  bridge.postMain({ type: 'slice_pick', printer: pick.printer, n: pick.n, spool });
}

export interface LinkForm { type: PrinterType; ip: string; serial: string; user: string; code: string; slice_fill: boolean }

export function saveLink(id: string, f: LinkForm, remove: boolean): void {
  const before = m.cfg.find(x => x.id === id);
  // A code saved for another kind of printer is not this one's: it is cleared unless a new one is typed.
  const changedType = (before?.type || 'bambu') !== f.type;
  const clear = remove || (changedType && !f.code);
  update(id, p => ({ ...p, type: f.type, ip: remove ? '' : f.ip.trim(), serial: remove || f.type !== 'bambu' ? '' : f.serial.trim(),
    user: f.type === 'prusalink' && !remove ? f.user.trim() : '', slice_fill: f.slice_fill,
    has_code: clear ? false : p.has_code || !!f.code }));
  if (f.code || clear) bridge.postMain({ type: 'printer_code', id, code: clear ? '' : f.code });
  const p = m.cfg.find(x => x.id === id);
  m.liveOn = m.liveOn || !!(p?.ip && p.has_code);
  m.liveKey = '';
  window.setTimeout(pollLive, 300);
}

export function moonSet(link: string, spool: number | null, confirm = false): void {
  const msg: Record<string, unknown> = spool === null ? { type: 'moon_spool', id: link, spool: null } : { type: 'moon_spool', id: link, spool, origin: m.origin };
  bridge.postMain(confirm ? { ...msg, confirm: true } : msg);
  note('pending', spool === null ? t('moon.clearing') : t('moon.setting', { id: spool }), 'moon:' + link);
}

// Changing the active spool while the printer prints books the rest of that print to the new spool: the plugin
// refuses it until this second, explicit answer.
on('moonConfirm', async d => {
  const printer = m.live.printers.find(p => p.id === d.id)?.name || String(d.id);
  const spool = typeof d.spool === 'number' ? d.spool : null;
  const yes = await ask({ title: t('moon.busyTitle', { printer }), text: t(d.state === 'PAUSE' ? 'moon.busyPaused' : 'moon.busyText', { printer }),
    yes: spool === null ? t('moon.busyClear') : t('moon.busyChange', { id: spool }), no: t('common.goBack'), danger: true });
  if (yes) moonSet(String(d.id), spool, true);
});
