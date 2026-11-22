import { test } from 'node:test';
import assert from 'node:assert/strict';
import { reasonTexts } from '../../src/logic/match.ts';

test('reasons are worded in order; unknown codes and shapes are dropped', () => {
  const word = (code: string, value: string) => `${code}:${value}`;
  assert.deepEqual(reasonTexts([['material', 'PLA'], ['vendor', 'eSUN'], ['nope', 'x'], 'bad', ['printer', null]], word),
    ['material:PLA', 'vendor:eSUN', 'printer:']);
  assert.deepEqual(reasonTexts(null, word), []);
});
