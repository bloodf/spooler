// The page's strings and locale rules, run directly in Node (node --test, type stripping). The page tests
// drive the built page in English; these cover every key in both languages, which they never show.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { en, ptBR } from '../../src/core/messages.ts';
import { interpolate, normalizeLocale, resolveLocale } from '../../src/core/i18n-core.ts';

const params = (text: string) => [...text.matchAll(/\{(\w+)\}/g)].map(m => m[1]).sort();

test('every key has a Portuguese text, and no extra ones', () => {
  assert.deepEqual(Object.keys(ptBR).sort(), Object.keys(en).sort());
});

test('both languages fill the same placeholders', () => {
  const wrong = Object.keys(en).filter(k => params(en[k as keyof typeof en]).join() !== params(ptBR[k as keyof typeof en]).join());
  assert.deepEqual(wrong, []);
});

test('no text is empty or left untranslated by accident', () => {
  for (const [k, v] of Object.entries(en)) assert.ok(v.trim(), `en ${k} is empty`);
  for (const [k, v] of Object.entries(ptBR)) assert.ok(v.trim(), `pt-BR ${k} is empty`);
});

test('locale tags', () => {
  assert.equal(normalizeLocale('pt_BR'), 'pt-BR');
  assert.equal(normalizeLocale('PT'), 'pt-BR');
  assert.equal(normalizeLocale('en-GB'), 'en');
  assert.equal(normalizeLocale('de_DE'), null);
  assert.equal(normalizeLocale(''), null);
  assert.equal(normalizeLocale(42), null);
});

test('explicit choice, then host, then browser, then English', () => {
  assert.equal(resolveLocale('en', 'pt_BR', ['pt-BR']), 'en');
  assert.equal(resolveLocale('auto', 'pt_BR', ['en-US']), 'pt-BR');
  assert.equal(resolveLocale('auto', 'de', ['fr', 'pt-PT']), 'pt-BR');
  assert.equal(resolveLocale('auto', null, ['fr']), 'en');
});

test('interpolate fills known names and leaves unknown ones visible', () => {
  assert.equal(interpolate('Spool #{id} on {printer}', { id: 7 }), 'Spool #7 on {printer}');
  assert.equal(interpolate('no params'), 'no params');
  assert.equal(interpolate('{a}{a}', { a: '<b>' }), '<b><b>');
});
