// Settings > Presets and the editor's Use with: the tuning table, the base presets offered, and what Use with sends.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { TUNE_FIELDS, TUNE_MATERIALS, basesFor, matName, setTune, tuneMaterials, useWithChanged, useWithPayload } from '../../src/logic/presets.ts';

test('a tuning value is set, cleared, and an emptied row is dropped', () => {
  const one = setTune({}, 'PLA', 'filament_flow_ratio', 0.98);
  assert.deepEqual(one, { PLA: { filament_flow_ratio: 0.98 } });
  const two = setTune(one, 'PLA', 'parent', 'Generic PLA');
  assert.deepEqual(two, { PLA: { filament_flow_ratio: 0.98, parent: 'Generic PLA' } });
  assert.deepEqual(one, { PLA: { filament_flow_ratio: 0.98 } }, 'the table it came from is not changed');
  assert.deepEqual(setTune(two, 'PLA', 'filament_flow_ratio', null), { PLA: { parent: 'Generic PLA' } });
  assert.deepEqual(setTune(setTune(two, 'PLA', 'parent', ''), 'PLA', 'filament_flow_ratio', null), {});
  assert.deepEqual(setTune(one, 'PETG', 'fan_max_speed', Number.NaN), one);
});

test('the material picker lists the usual materials, then any other tuned one', () => {
  assert.deepEqual(tuneMaterials({}), TUNE_MATERIALS);
  assert.deepEqual(tuneMaterials({ PLA: { pressure_advance: 0.03 }, 'PA-CF': { fan_max_speed: 30 } }), [...TUNE_MATERIALS, 'PA-CF']);
  assert.equal(matName('  pla   silk '), 'PLA SILK');
});

test('base presets offered are those of the material and its variants, else all', () => {
  const parents = [{ name: 'Generic PLA', type: 'PLA' }, { name: 'Generic PLA Silk', type: 'PLA-Silk' }, { name: 'Generic PETG', type: 'PETG' }];
  assert.deepEqual(basesFor(parents, 'PLA').map(p => p.name), ['Generic PLA', 'Generic PLA Silk']);
  assert.deepEqual(basesFor(parents, 'petg').map(p => p.name), ['Generic PETG']);
  assert.deepEqual(basesFor(parents, 'PEEK'), parents);
});

test('the tuning boxes match the ranges the plugin takes', () => {
  const range = Object.fromEntries(TUNE_FIELDS.map(f => [f.key, [f.min, f.max]]));
  assert.deepEqual(range, {
    filament_flow_ratio: [0.01, 2], pressure_advance: [0, 2], filament_retraction_length: [0, 50], filament_retraction_speed: [1, 500],
    filament_max_volumetric_speed: [0.1, 200], fan_min_speed: [0, 100], fan_max_speed: [0, 100],
  });
});

test('Use with sends the printers picked, or null for automatic, and only when it changed', () => {
  assert.deepEqual(useWithPayload(['A', 'B']), ['A', 'B']);
  assert.equal(useWithPayload([]), null);
  assert.equal(useWithPayload(null), null);
  assert.equal(useWithChanged(['B', 'A'], ['A', 'B']), false);
  assert.equal(useWithChanged([], null), false);
  assert.equal(useWithChanged(['A'], null), true);
  assert.equal(useWithChanged([], ['A']), true);
});
