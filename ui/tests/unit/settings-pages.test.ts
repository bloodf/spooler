// Settings as pages: every link that opens a settings page names a page that exists, every page has an id and a label
// in each language, and the narrow layout's Back and the list's "needs fixing" label are translated.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const SRC = fileURLToPath(new URL('../../src/', import.meta.url));
const files = (dir: string): string[] => readdirSync(dir).flatMap(n => (statSync(join(dir, n)).isDirectory() ? files(join(dir, n)) : [join(dir, n)]));
const view = readFileSync(join(SRC, 'settings/SettingsView.vue'), 'utf8');
const pages = [...view.matchAll(/\{ id: '([a-z-]+)', label: t\('([^']+)'\)/g)].map(m => ({ id: m[1], label: m[2] }));
const sectionIds = new Set([...files(SRC).filter(f => f.endsWith('.vue')).flatMap(f => [...readFileSync(f, 'utf8').matchAll(/<(?:Oui(?:FormSection|Panel)[^>]*\s|div )id="([a-z-]+)"/g)].map(m => m[1]))]);
const locales = files(SRC).filter(f => /core[\/\\]messages(-[a-z]+)?\.ts$/.test(f));

// A page is one section, or a wrapper (<div id class="set-page">) around the few sections that belong together.
test('each settings page is listed once and drawn by one section or one group of sections', () => {
  assert.equal(pages.length, 6, 'pages found: ' + pages.map(p => p.id).join(', '));
  assert.equal(new Set(pages.map(p => p.id)).size, pages.length, 'unique ids');
  for (const p of pages) assert.ok(sectionIds.has(p.id), 'a section for ' + p.id);
});

test('every link into Settings opens a page that exists', () => {
  const links = files(SRC).flatMap(f => [...readFileSync(f, 'utf8').matchAll(/openSettings\('([a-z-]+)'\)/g)].map(m => ({ f, id: m[1] })));
  assert.ok(links.length >= 2, 'links found: ' + links.length);
  for (const l of links) assert.ok(pages.some(p => p.id === l.id), l.f + ' opens ' + l.id + ', which is not a page');
});

test('page names, Back and the error label are translated in every language', () => {
  assert.ok(locales.length >= 5, 'locale files: ' + locales.length);
  const keys = [...new Set([...pages.map(p => p.label), 'wiz.back', 'set.hasError'])];
  for (const f of locales) {
    const text = readFileSync(f, 'utf8');
    for (const k of keys) {
      const n = text.split("'" + k + "':").length - 1;
      assert.ok(n >= (/[\/\\]messages\.ts$/.test(f) ? 2 : 1), f + ' lacks ' + k);
    }
  }
});
