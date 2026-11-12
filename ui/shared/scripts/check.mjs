import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import assert from 'node:assert/strict';
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const manifest = JSON.parse(await readFile(resolve(root, 'manifest.json'), 'utf8'));
const packageInfo = JSON.parse(await readFile(resolve(root, 'package.json'), 'utf8'));
assert.equal(packageInfo.version, manifest.version, 'Shared package version drift');
const indexSource = await readFile(resolve(root, 'src/index.ts'), 'utf8');
assert.equal(/export const UI_VERSION = '([^']+)';/.exec(indexSource)?.[1], manifest.version, 'Shared runtime version drift');
for (const [file, expected] of Object.entries(manifest.files)) {
  const actual = createHash('sha256').update(await readFile(resolve(root, file))).digest('hex');
  assert.equal(actual, expected, `Shared UI drift: ${file}`);
}
const palettes = JSON.parse(await readFile(resolve(root, 'src/palette.json'), 'utf8'));
function luminance(hex) {
  const rgb = hex.slice(1).match(/../g).map(x => parseInt(x, 16) / 255)
    .map(x => x <= .04045 ? x / 12.92 : ((x + .055) / 1.055) ** 2.4);
  return rgb[0] * .2126 + rgb[1] * .7152 + rgb[2] * .0722;
}
for (const [theme, p] of Object.entries(palettes)) {
  const pairs = [['text', 'surface', 4.5], ['muted', 'surface', 4.5], ['muted', 'background', 4.5],
    ['onPrimary', 'primary', 4.5], ['onPrimary', 'primaryHover', 4.5],
    ['onDanger', 'danger', 4.5], ['onDanger', 'dangerHover', 4.5],
    ['danger', 'dangerBg', 4.5], ['warning', 'warningBg', 4.5],
    ['success', 'successBg', 4.5], ['primary', 'surface', 3], ['controlBorder', 'surface', 3]];
  for (const [fg, bg, minimum] of pairs) {
    const l = [luminance(p[fg]), luminance(p[bg])].sort((a, b) => b - a);
    const ratio = (l[0] + .05) / (l[1] + .05);
    assert(ratio >= minimum, `${theme}: ${fg}/${bg} ${ratio.toFixed(2)} < ${minimum}`);
    console.log(`${theme}: ${fg}/${bg} ${ratio.toFixed(2)}:1`);
  }
}
console.log('Shared sources and defined palette pairs verified. This is not proof of native Orca rendering or full accessibility compliance.');
