// Card input rules shared by the spool menu, checked against the limits the plugin enforces (MAX_GRAMS).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { emptyCount, gramsValid, levelTone, lowLevel, pickSpools, spoolFraction, spoolMatches, stackLead } from '../../src/logic/spools.ts';

test('drawn spool fill: Spoolman weight, else printer percent, else unknown', () => {
  assert.equal(spoolFraction({ id: 1, remaining_weight: 250, initial_weight: 1000 }, 90), 0.25);
  assert.equal(spoolFraction({ id: 1, remaining_weight: 300, filament: { weight: 750 } }), 0.4);
  assert.equal(spoolFraction({ id: 1, remaining_weight: 1200, initial_weight: 1000 }), 1);
  assert.equal(spoolFraction({ id: 1, remaining_weight: -5, initial_weight: 1000 }), 0);
  assert.equal(spoolFraction({ id: 1, remaining_weight: 0, initial_weight: 1000 }), 0);
  assert.equal(spoolFraction({ id: 1, remaining_weight: null, initial_weight: 1000 }, 64), 0.64);
  assert.equal(spoolFraction({ id: 1, remaining_weight: 100, initial_weight: 0 }, 30), 0.3);
  assert.equal(spoolFraction(null, 64), 0.64);
  assert.equal(spoolFraction(null, 140), 1);
  assert.equal(spoolFraction(null, null), null);
  assert.equal(spoolFraction(undefined, NaN), null);
  assert.equal(spoolFraction({ id: 1 }), null);
});

test('weights and uses: above 0, up to 100,000 g, decimal comma allowed', () => {
  for (const ok of ['1', '12,5', '0.1', '100000', ' 7 ']) assert.ok(gramsValid(ok), ok);
  for (const bad of ['', ' ', '0', '-1', '100000.1', 'abc', '1e9', 'NaN', 'Infinity']) assert.ok(!gramsValid(bad), bad);
});

test('remaining weight may be 0 (an empty spool)', () => {
  assert.ok(gramsValid('0', true));
  assert.ok(!gramsValid('-0.5', true));
  assert.ok(!gramsValid('', true));
});

test('0 g is empty, not almost empty', () => {
  assert.equal(lowLevel(0, 100), 'empty');
  assert.equal(lowLevel(-3, 100), 'empty');
  assert.equal(lowLevel(10, 100), 'out');
  assert.equal(lowLevel(0, 0), 'empty');
  assert.equal(levelTone('empty'), 'critical');
});

test('a stack shows the spool in use, else the one with the most left, never an empty one first', () => {
  const empty = { id: 1, remaining_weight: 0 }, half = { id: 2, remaining_weight: 480 }, full = { id: 3, remaining_weight: 990 }, unknown = { id: 4 };
  assert.equal(stackLead([empty, half], () => false).id, 2);
  assert.equal(stackLead([empty, half, full], () => false).id, 3);
  assert.equal(stackLead([empty, half, full], s => s.id === 2).id, 2);
  assert.equal(stackLead([empty, unknown], () => false).id, 4);
  assert.equal(emptyCount([empty, half, unknown]), 1);
});

test('spool search: words in any order, case and accents ignored, letters may be missing; ids exact, never fuzzy', () => {
  const s = [
    { id: 12, location: 'Prateleira', filament: { name: 'Preto Fosco', material: 'PLA', vendor: { name: 'Polymaker' } } },
    { id: 13, filament: { name: 'Black', material: 'PETG', vendor: { name: 'Acme' } } },
    { id: 120, lot_nr: 'L-12', filament: { name: 'Café Brown', material: 'ABS', vendor: { name: 'Acme' } } },
  ];
  const f = (q: string) => s.filter(x => spoolMatches(x, q)).map(x => x.id);
  assert.deepEqual(f('polymaker preto'), [12]);        // vendor + name, either order
  assert.deepEqual(f('FOSCO pla'), [12]);
  assert.deepEqual(f('plmk'), [12]);                   // letters missing
  assert.deepEqual(f('blck'), [13]);
  assert.deepEqual(f('cafe'), [120]);                  // accents
  assert.deepEqual(f('#12'), [12]);                    // exact id: not 120, not 13
  assert.deepEqual(f('12'), [12]);
  assert.deepEqual(f('13'), [13]);
  assert.deepEqual(f('#14'), []);
  assert.deepEqual(f('prate-leira'), [12]);            // separators do not matter
  assert.deepEqual(f('cafe-brown'), [120]);
  assert.deepEqual(f('l-12'), [120]);                  // a lot code, whole
  assert.deepEqual(f('preto 12'), [12]);               // a number among words is an id
  assert.deepEqual(f('preto 13'), []);
  assert.deepEqual(f('petg shelf'), []);               // every word must match
  assert.deepEqual(f('prateleira'), [12]);             // location kept
});

test('slot picker spools: archived and taken left out; colour, weights and low as the colour-first picker takes them', () => {
  const spools = [
    { id: 1, remaining_weight: 400, initial_weight: 1000, location: 'Shelf A', filament: { name: 'Black', material: 'PLA', color_hex: '111111', vendor: { name: 'Acme' } } },
    { id: 2, remaining_weight: 50, filament: { weight: 750, name: 'Rainbow', material: 'PLA', multi_color_hexes: 'ff0000,00ff00', vendor: { name: 'Acme' } } },
    { id: 3, remaining_weight: 900, archived: true, filament: { name: 'Old' } },
    { id: 4, remaining_weight: 900, filament: { name: 'Taken', color_hex: '222222' } },
    { id: 5, remaining_weight: null, filament: {} },
  ];
  const out = pickSpools(spools, new Set(['4']), 100);
  assert.deepEqual(out.map(s => s.id), [1, 2, 5]);
  assert.deepEqual(out[0], { id: 1, name: 'Black', vendor: 'Acme', material: 'PLA', colour: '#111111', colours: null, remaining: 400, initial: 1000, location: 'Shelf A', low: false });
  assert.deepEqual([out[1].colours, out[1].initial, out[1].low], [['#ff0000', '#00ff00'], 750, true]);
  assert.deepEqual([out[2].name, out[2].colour, out[2].remaining, out[2].initial, out[2].low], [null, null, null, null, false]);
  assert.deepEqual(pickSpools(spools).map(s => s.id), [1, 2, 4, 5], 'nothing taken: every spool not archived');
});
