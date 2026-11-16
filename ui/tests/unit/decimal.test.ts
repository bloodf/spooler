// "." and the language's own decimal sign both mean the decimal in a decimal InputNumber.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { decimalSign, pastedDecimal, typedDecimal } from '../../src/core/decimal.ts';

test('the decimal sign follows the language', () => {
  for (const [l, sign] of [['en', '.'], ['zh-CN', '.'], ['de', ','], ['es', ','], ['pt-BR', ',']]) assert.equal(decimalSign(l), sign, l);
});

test('a typed "." becomes the language sign once, and only where it differs', () => {
  assert.equal(typedDecimal('.', '2', ','), ',');
  assert.equal(typedDecimal('.', '2,5', ','), null, 'already has a decimal');
  assert.equal(typedDecimal('.', '2', '.'), null, 'English types it as is');
  assert.equal(typedDecimal('5', '2', ','), null);
});

test('pasted "2.5" keeps its decimal in every language; "," only where it is the decimal', () => {
  assert.equal(pastedDecimal(' 2.5 ', '.'), '2.5');
  assert.equal(pastedDecimal('2.5', ','), '2,5');
  assert.equal(pastedDecimal('2,5', ','), '2,5');
  assert.equal(pastedDecimal('1,500', '.'), null, 'English grouping is left to InputNumber');
  assert.equal(pastedDecimal('25', ','), null);
  assert.equal(pastedDecimal('2.5.1', ','), null);
});
