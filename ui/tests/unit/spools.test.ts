// Card input rules shared by the spool menu, checked against the limits the plugin enforces (MAX_GRAMS).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { gramsValid } from '../../src/logic/spools.ts';

test('weights and uses: above 0, up to 100,000 g, decimal comma allowed', () => {
  for (const ok of ['1', '12,5', '0.1', '100000', ' 7 ']) assert.ok(gramsValid(ok), ok);
  for (const bad of ['', ' ', '0', '-1', '100000.1', 'abc', '1e9', 'NaN', 'Infinity']) assert.ok(!gramsValid(bad), bad);
});

test('remaining weight may be 0 (an empty spool)', () => {
  assert.ok(gramsValid('0', true));
  assert.ok(!gramsValid('-0.5', true));
  assert.ok(!gramsValid('', true));
});
