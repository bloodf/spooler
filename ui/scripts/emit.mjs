// Check the single-file build and copy it to the path scripts/embed_ui.py embeds from (it records the served page's
// hash in ui/build.json). Usage: node scripts/emit.mjs (after vite build).
import { readFile, writeFile } from 'node:fs/promises';

const html = await readFile(new URL('../dist/index.html', import.meta.url), 'utf8');
for (const marker of ['__BOOT__']) {
  if (html.split(marker).length !== 2) throw new Error(`built page must contain ${marker} exactly once`);
}
// `@import` followed by a URL or quoted path: PrimeVue 5's style sanitizer carries the bare word in a regex.
if (/<script[^>]+src=|<link[^>]+href="http|@import\s*(?:url\(|["'])|url\(http/i.test(html)) throw new Error('built page references an external resource');
if (/\bnew Function\b|\beval\(/.test(html)) throw new Error('built page uses eval / new Function');
const out = new URL('../dist/spooler-ui.html', import.meta.url);
await writeFile(out, html);
console.log(`built ui/dist/spooler-ui.html (${Buffer.byteLength(html)} bytes)`);
