import { reactive } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, pollLive } from './main';
import { t } from '../core/i18n';
import { addUnit, newPrinterId, type ManualPrinter, type PrinterType, type UnitKind } from '../logic/printers';

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

export function moonSet(link: string, spool: number | null): void {
  bridge.postMain(spool === null ? { type: 'moon_spool', id: link, spool: null } : { type: 'moon_spool', id: link, spool, origin: m.origin });
  note('pending', spool === null ? t('moon.clearing') : t('moon.setting', { id: spool }), 'moon:' + link);
}
