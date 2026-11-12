// Copy the single-file build to the plugin's asset path and record its hash, so tests can tell the committed
// page from a stale or hand-edited one. Usage: node scripts/emit.mjs (after vite build).
import { createHash } from 'node:crypto';
import { readFile, writeFile } from 'node:fs/promises';
import { gzipSync } from 'node:zlib';

const html = await readFile(new URL('../dist/index.html', import.meta.url), 'utf8');
for (const marker of ['__BOOT__']) {
  if (html.split(marker).length !== 2) throw new Error(`built page must contain ${marker} exactly once`);
}
if (/<script[^>]+src=|<link[^>]+href="http|@import|url\(http/i.test(html)) throw new Error('built page references an external resource');
if (/\bnew Function\b|\beval\(/.test(html)) throw new Error('built page uses eval / new Function');
const out = new URL('../dist/spooler-ui.html', import.meta.url);
await writeFile(out, html);
const sha256 = createHash('sha256').update(html).digest('hex');
const info = { file: 'ui/dist/spooler-ui.html (embedded in plugin/spooler/spooler_any.py)', sha256, bytes: Buffer.byteLength(html), gzip: gzipSync(html, { level: 9 }).length };
await writeFile(new URL('../build.json', import.meta.url), JSON.stringify(info, null, 2) + '\n');
console.log(JSON.stringify(info));
