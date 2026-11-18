// Card input rules shared by the spool menu, checked against the limits the plugin enforces (MAX_GRAMS).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { gramsValid, spoolFraction } from '../../src/logic/spools.ts';

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
