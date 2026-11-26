import { reactive } from 'vue';
import * as bridge from '../core/bridge';
import { m, note, on, pollLive } from './main';
import { t } from '../core/i18n';
import { ask } from '../core/dialog';
import { addUnit, linkSlot, mapPresets, newPrinterId, withGates, type LivePrinter, type ManualPrinter, type PrinterType, type SlicePick, type Tray, type UnitKind } from '../logic/printers';

// Manual printers are edited as new arrays (never in place) and saved whole, as the previous page did.
export const ui = reactive({ picking: null as null | { p: string; u?: number; s?: number; moon?: boolean; bind?: boolean }, renaming: '', linkOpen: '' });

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
export function removePrinter(id: string): void {
  savePrinters(m.cfg.filter(p => p.id !== id));
  if (Object.values(m.sliceMap).includes(id)) setPresets(id, []);
}
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
  bridge.postMain({ type: 'slice_pick', printer: pick.printer, n: pick.n, slice: pick.slice, spool });
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

/** Link a spool to a U1 toolhead or an Anycubic Kobra ACE or spool holder slot (on), or unlink it: the plugin writes the spool's Spoolman location. */
export function bindSlot(link: string, slot: number, spool: number, on: boolean): void {
  showBound(link, slot, spool, on);
  bridge.postMain({ type: 'spool_action', action: on ? 'bind' : 'unbind', id: spool, printer: link, slot, origin: m.origin });
  note('pending', t('action.sending'), 'spool-action');
}

// Optimistic: the slot shows the spool the moment it is picked; the plugin's answer keeps it or, when the write failed, puts back
// what the slot showed. A live message that carries the new link replaces it as before.
let undoBind: LivePrinter[] | null = null;
function showBound(link: string, slot: number, spool: number, on: boolean): void {
  const found = on ? m.spools.find(s => s.id === spool) : null;
  if (on && !found) return;
  const before = m.live.printers;
  const tray = (lv: LivePrinter, tr: Tray): Tray => (on && found
    ? { ...tr, empty: false, spool, linked: lv.bind === 'S' ? 'kobracontrol' : 'u1control', name: found.filament?.name || tr.name, type: found.filament?.material || tr.type,
        colour: found.filament?.color_hex || tr.colour }
    : { ...tr, spool: null, linked: '' });
  const next = before.map(lv => (lv.link !== link ? lv : { ...lv, units: lv.units.map(u => ({ ...u, trays: u.trays.map((tr, i) => (linkSlot(lv, u, i) === slot ? tray(lv, tr) : tr)) })) }));
  undoBind = before;
  m.live = { ...m.live, printers: next };
}
on('actionDone', d => {
  if ((d.action === 'bind' || d.action === 'unbind') && undoBind) {
    if (!d.ok) { m.live = { ...m.live, printers: undoBind }; m.liveKey = ''; }
    undoBind = null;
  }
});

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
