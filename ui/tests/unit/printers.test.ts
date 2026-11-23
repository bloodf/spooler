// Klipper printers' hand-set gates, the printers a slice can fill, and the preset-to-printer choice.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { fillable, linkSlot, liveUnitName, mapPresets, slotName, withGates, type LivePrinter, type ManualPrinter, type Words } from '../../src/logic/printers.ts';

const voron: ManualPrinter = { id: 'auto-v', name: 'Voron', auto: true, kind: 'moonraker', ip: 'http://v', units: [] };

test('gates: resized keeping the spools that stay, capped at 16, 0 removes them', () => {
  const four = withGates(voron, 4);
  assert.deepEqual(four.units, [{ kind: 'gate', slots: [null, null, null, null] }]);
  const set = { ...four, units: [{ kind: 'gate' as const, slots: ['1', null, '3', '4'] }] };
  assert.deepEqual(withGates(set, 2).units[0].slots, ['1', null]);
  assert.deepEqual(withGates(set, 6).units[0].slots, ['1', null, '3', '4', null, null]);
  assert.equal(withGates(set, 40).units[0].slots.length, 16);
  assert.deepEqual(withGates(set, 0).units, []);
  assert.deepEqual(voron.units, [], 'the printer itself is not changed');
});

test('fillable: network printers with an address and hand-set Klipper printers; never Bambu or printer-reported', () => {
  const cfg: ManualPrinter[] = [voron, { ...voron, id: 'auto-u1', managed: true }, { id: 'mk4', name: 'MK4', type: 'prusalink', ip: '10.0.0.5', units: [] },
    { id: 'o', name: 'Octo', type: 'octoprint', units: [] }, { id: 'x1', name: 'X1', type: 'bambu', ip: '10.0.0.7', units: [] }];
  assert.deepEqual(fillable(cfg).map(p => p.id), ['auto-v', 'mk4']);
});

test('live units: an Anycubic unit is named by its own source, other printers by their label', () => {
  const w: Words = { ace: 'ACE', holder: 'Spool holder', ams: 'AMS', ht: 'HT', ext: 'Ext', gate: 'Gate', gateN: n => `Gate ${n}`,
    slot: (u, n) => `${u} slot ${n}`, head: n => `T${n}`, externalShort: 'External' };
  const trays = [{}, {}, {}, {}];
  const kobra: LivePrinter = { name: 'Kobra', unit_label: '', bind: 'S', units: [
    { id: 0, kind: 'ams', source: 'ace', box: 0, trays }, { id: 2, kind: 'ams', source: 'ace', box: 2, trays }, { id: 3, kind: 'ams', source: 'holder', box: -1, trays: trays.slice(0, 3) }] };
  assert.deepEqual(kobra.units.map(u => liveUnitName(kobra, u, w)), ['ACE 1', 'ACE 3', 'Spool holder']);
  assert.equal(slotName(kobra, kobra.units[2], 1, false, w), 'Spool holder slot 2');
  const bambu: LivePrinter = { name: 'X1', unit_label: 'AMS 2 Pro', units: [{ id: 0, kind: 'ams', trays }] };
  assert.equal(slotName(bambu, bambu.units[0], 0, false, w), 'AMS 2 Pro slot 1');
  const two: LivePrinter = { name: 'P1', units: [{ id: 0, kind: 'ams', trays }, { id: 1, kind: 'ams', trays }] };
  assert.equal(liveUnitName(two, two.units[1], w), 'AMS 2');
});

test('link slots: holder after the ACE is S5, after ACE 2 it is S15, alone S1', () => {
  const trays = [{}, {}, {}, {}];
  const hub: LivePrinter = { name: 'K', bind: 'S', units: [{ id: 0, kind: 'ams', source: 'ace', box: 0, trays }, { id: 1, kind: 'ams', source: 'holder', box: -1, trays }] };
  assert.deepEqual([linkSlot(hub, hub.units[0], 0), linkSlot(hub, hub.units[1], 0), linkSlot(hub, hub.units[1], 2)], [0, 4, 6]);
  const multi: LivePrinter = { name: 'K', bind: 'S', units: [{ id: 3, kind: 'ams', source: 'holder', box: -1, trays }] };
  assert.equal(linkSlot(multi, multi.units[0], 2) + 1, 15);
  const alone: LivePrinter = { name: 'K', bind: 'S', units: [{ id: 0, kind: 'ams', source: 'holder', box: -1, trays }] };
  assert.equal(linkSlot(alone, alone.units[0], 0) + 1, 1);
  assert.equal(linkSlot({ name: 'U1', bind: 'T', units: [] }, { id: 0, kind: 'ams', trays }, 2), 2);
});

test('presets: given to one printer, taken off another', () => {
  const map = { 'MK4 preset': 'mk4', 'Voron 0.4': 'auto-v' };
  assert.deepEqual(mapPresets(map, 'mk4', ['Voron 0.4']), { 'Voron 0.4': 'mk4' });
  assert.deepEqual(mapPresets(map, 'auto-v', []), { 'MK4 preset': 'mk4' });
});
