// The page's strings and locale rules, run directly in Node (node --test, type stripping). The page tests
// drive the built page in each language for a few scenarios; these cover every key in all five.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { en, ptBR } from '../../src/core/messages.ts';
import { es } from '../../src/core/messages-es.ts';
import { de } from '../../src/core/messages-de.ts';
import { zhCN } from '../../src/core/messages-zh.ts';
import { LOCALES, formatMoney, interpolate, isLocale, normalizeLocale, resolveLocale } from '../../src/core/i18n-core.ts';
import { formatWeight } from '../../src/logic/spools.ts';

const dicts: Record<string, Record<string, string>> = { 'pt-BR': ptBR, es, de, 'zh-CN': zhCN };
const params = (text: string) => [...text.matchAll(/\{(\w+)\}/g)].map(m => m[1]).sort();
const english = en as Record<string, string>;

test('every language the page offers has a dictionary', () => {
  assert.deepEqual(['en', ...Object.keys(dicts)].sort(), [...LOCALES].sort());
});

for (const [lang, dict] of Object.entries(dicts)) {
  test(`${lang}: every key has a text, and no extra ones`, () => {
    assert.deepEqual(Object.keys(dict).sort(), Object.keys(en).sort());
  });
  test(`${lang}: the same placeholders as English`, () => {
    assert.deepEqual(Object.keys(en).filter(k => params(english[k]).join() !== params(dict[k]).join()), []);
  });
  test(`${lang}: no text is empty`, () => {
    for (const [k, v] of Object.entries(dict)) assert.ok(v.trim(), `${lang} ${k} is empty`);
  });
}

test('no English text is empty', () => {
  for (const [k, v] of Object.entries(en)) assert.ok(v.trim(), `en ${k} is empty`);
});

// Product, protocol and unit names, and words the language shares with English. Anything else that equals the
// English text was left untranslated by accident.
const NAMES = ['lang.en', 'lang.pt-BR', 'lang.es', 'lang.de', 'lang.zh-CN', 'printer.ams', 'printer.ht', 'printer.addAms', 'printer.addHt', 'link.button'];
const SAME: Record<string, string[]> = {
  es: [...NAMES, 'common.ok', 'status.errorPrefix', 'filters.material', 'disp.material', 'disp.head_material', 'spool.rfid', 'progress.hm', 'progress.m', 'stats.materialsN_one'],
  de: [...NAMES, 'common.ok', 'filters.material', 'disp.material', 'disp.head_material', 'spool.rfid', 'progress.hm', 'progress.m',
    'colour.orange', 'bambu.region', 'link.live', 'usage.slot'],
  'zh-CN': NAMES,
};
for (const [lang, allowed] of Object.entries(SAME)) {
  test(`${lang}: nothing is left in English`, () => {
    assert.deepEqual(Object.keys(en).filter(k => dicts[lang][k] === english[k]).sort(), [...allowed].sort());
  });
}

test('zh-CN: Chinese text with Chinese punctuation', () => {
  const han = /[一-鿿]/;
  for (const [k, v] of Object.entries(zhCN)) {
    // "at 10:42" is just the time, "640 g of 1,000 g" is "640 g / 1,000 g" and RFID is RFID.
    if (NAMES.includes(k) || ['age.at', 'weight.of', 'spool.rfid'].includes(k)) continue;
    assert.ok(han.test(v), `zh-CN ${k} has no Chinese text: ${v}`);
    // A Latin comma, colon, semicolon, question mark or sentence full stop right after a Chinese character.
    assert.ok(!/[一-鿿][,:;?!]|[一-鿿]\.(\s|$)/.test(v), `zh-CN ${k} has Latin punctuation: ${v}`);
  }
});

test('the language names are written in their own language everywhere', () => {
  for (const dict of [english, ...Object.values(dicts)]) {
    assert.deepEqual([dict['lang.en'], dict['lang.pt-BR'], dict['lang.es'], dict['lang.de'], dict['lang.zh-CN']],
      ['English', 'Português (Brasil)', 'Español', 'Deutsch', '简体中文']);
  }
});

test('locale tags', () => {
  assert.equal(normalizeLocale('pt_BR'), 'pt-BR');
  assert.equal(normalizeLocale('PT'), 'pt-BR');
  assert.equal(normalizeLocale('en-GB'), 'en');
  assert.equal(normalizeLocale('es'), 'es');
  assert.equal(normalizeLocale('es_ES'), 'es');
  assert.equal(normalizeLocale('es-MX'), 'es');
  assert.equal(normalizeLocale('de'), 'de');
  assert.equal(normalizeLocale('de_DE'), 'de');
  assert.equal(normalizeLocale('de-AT'), 'de');
  assert.equal(normalizeLocale('zh_CN'), 'zh-CN');
  assert.equal(normalizeLocale('zh-Hans-CN'), 'zh-CN');
  assert.equal(normalizeLocale('zh'), 'zh-CN');
  assert.equal(normalizeLocale('zh_TW'), 'zh-CN', 'Traditional Chinese takes the Simplified page, not English');
  assert.equal(normalizeLocale('fr_FR'), null);
  assert.equal(normalizeLocale('ja'), null);
  assert.equal(normalizeLocale('desktop'), null, 'only the language subtag counts, not a prefix');
  assert.equal(normalizeLocale(''), null);
  assert.equal(normalizeLocale(42), null);
});

test('explicit choice, then host, then browser, then English', () => {
  assert.equal(resolveLocale('en', 'pt_BR', ['pt-BR']), 'en');
  assert.equal(resolveLocale('auto', 'pt_BR', ['en-US']), 'pt-BR');
  assert.equal(resolveLocale('auto', 'fr', ['it', 'pt-PT']), 'pt-BR');
  assert.equal(resolveLocale('auto', null, ['fr']), 'en');
  assert.equal(resolveLocale('auto', 'es', ['en-US']), 'es');
  assert.equal(resolveLocale('auto', 'de', ['en-US']), 'de');
  assert.equal(resolveLocale('auto', 'zh_CN', ['en-US']), 'zh-CN');
  assert.equal(resolveLocale('auto', 'zh_TW', ['en-US']), 'zh-CN');
  assert.equal(resolveLocale('auto', 'ko', ['ja', 'de-CH', 'es']), 'de', 'the first browser language the page has');
  assert.equal(resolveLocale('auto', 'xx', []), 'en');
  for (const pref of ['es', 'de', 'zh-CN'] as const) assert.equal(resolveLocale(pref, 'pt_BR', ['en-US']), pref, 'the manual choice wins');
});

test('a saved choice is only taken when the page has that language', () => {
  for (const l of LOCALES) assert.ok(isLocale(l));
  for (const bad of ['auto', 'fr', 'zh_CN', 'ES', '', null, 7]) assert.ok(!isLocale(bad), String(bad));
});

test('interpolate fills known names and leaves unknown ones visible', () => {
  assert.equal(interpolate('Spool #{id} on {printer}', { id: 7 }), 'Spool #7 on {printer}');
  assert.equal(interpolate('no params'), 'no params');
  assert.equal(interpolate('{a}{a}', { a: '<b>' }), '<b><b>');
});

test('weights follow the language', () => {
  assert.equal(formatWeight(1380, true, 'en'), '1,380 g');
  assert.equal(formatWeight(1380, true, 'pt-BR'), '1.380 g');
  assert.equal(formatWeight(1380, true, 'de'), '1.380 g');
  assert.equal(formatWeight(12380, true, 'es'), '12.380 g');
  assert.equal(formatWeight(1380, true, 'zh-CN'), '1,380 g');
  assert.equal(formatWeight(1380, false, 'en'), '1.38 kg');
  assert.equal(formatWeight(1380, false, 'de'), '1,38 kg');
  assert.equal(formatWeight(1380, false, 'es'), '1,38 kg');
  assert.equal(formatWeight(1380, false, 'zh-CN'), '1.38 kg');
});

test('numbers and dates follow the language', () => {
  const n = (l: string) => new Intl.NumberFormat(l, { minimumFractionDigits: 2, maximumFractionDigits: 2 }).format(41.2);
  assert.deepEqual(LOCALES.map(n), ['41.20', '41,20', '41,20', '41,20', '41.20']);
  const day = (l: string) => new Intl.DateTimeFormat(l, { dateStyle: 'medium', timeZone: 'UTC' }).format(new Date(Date.UTC(2026, 10, 16)));
  assert.equal(day('en'), 'Nov 16, 2026');
  assert.equal(day('de'), '16.11.2026');
  assert.equal(day('es'), '16 nov 2026');
  assert.equal(day('zh-CN'), '2026年11月16日');
  assert.match(day('pt-BR'), /^16 de nov\. de 2026$/);
});

test('money: the sign where the language puts it', () => {
  assert.equal(formatMoney('€', '41.20', 'en'), '€41.20');
  assert.equal(formatMoney('€', '41,20', 'pt-BR'), '€41,20');
  assert.equal(formatMoney('€', '41.20', 'zh-CN'), '€41.20');
  assert.equal(formatMoney('€', '41,20', 'de'), '41,20 €');
  assert.equal(formatMoney('CHF ', '41,20', 'de'), '41,20 CHF');
  assert.equal(formatMoney('$', '41,20', 'es'), '41,20 $');
  assert.equal(formatMoney('', '41,20', 'de'), '41,20', 'no sign, no dangling space');
});

test('plurals: one and other are all the page needs in these languages', () => {
  const pick = (l: string, n: number) => (new Intl.PluralRules(l).select(n) === 'one' ? 'one' : 'other');
  for (const l of ['en', 'es', 'de']) assert.deepEqual([0, 1, 2, 21].map(n => pick(l, n)), ['other', 'one', 'other', 'other'], l);
  assert.deepEqual([0, 1, 2].map(n => pick('zh-CN', n)), ['other', 'other', 'other']);
  // A _one text never shows a number other than 1, so it may spell the 1 out; an _other text must take {n}.
  for (const [lang, dict] of Object.entries({ en: english, ...dicts })) {
    for (const k of Object.keys(en).filter(k => k.endsWith('_other') && params(english[k]).includes('n'))) {
      assert.ok(dict[k].includes('{n}'), `${lang} ${k} drops the count`);
    }
  }
});
