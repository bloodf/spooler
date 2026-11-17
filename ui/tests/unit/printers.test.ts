// Klipper printers' hand-set gates, the printers a slice can fill, and the preset-to-printer choice.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { fillable, mapPresets, withGates, type ManualPrinter } from '../../src/logic/printers.ts';

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

test('presets: given to one printer, taken off another', () => {
  const map = { 'MK4 preset': 'mk4', 'Voron 0.4': 'auto-v' };
  assert.deepEqual(mapPresets(map, 'mk4', ['Voron 0.4']), { 'Voron 0.4': 'mk4' });
  assert.deepEqual(mapPresets(map, 'auto-v', []), { 'MK4 preset': 'mk4' });
});
