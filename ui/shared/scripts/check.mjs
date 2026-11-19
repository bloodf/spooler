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
// Every foreground/background pair the preset, base.css and the shared components put together.
// 4.5 = text (WCAG AA), 3 = control boundaries, focus ring and other non-text marks.
// Since 5.0 the surfaces are neutral (OrcaSlicer's own greys) and the same for every plugin, so each pair is checked once.
const HUES = ['teal', 'sky', 'cobalt', 'violet', 'magenta', 'lime', 'orange'];
const STATES = ['danger', 'warning', 'success', 'info'];
const SURFACES = ['background', 'surface', 'raised', 'inset'];
const cap = name => name[0].toUpperCase() + name.slice(1);
const pairs = [
  ...SURFACES.flatMap(bg => [['text', bg, 4.5], ['muted', bg, 4.5], ['primaryText', bg, 4.5], ['controlBorder', bg, 3], ['primaryMark', bg, 3],
    ...STATES.map(state => [state, bg, 4.5]), ...HUES.map(hue => [hue, bg, 4.5]),
    // The solid red button always has a label; its fill is held to 3:1 on the page and on panels.
    ...(bg === 'background' || bg === 'surface' ? [['dangerSolid', bg, 3]] : [])]),
  // The neutral button (OrcaSlicer's regular button) and its label; the teal primary and its label; the tick on a checked mark.
  ['text', 'control', 4.5], ['text', 'controlHover', 4.5], ['onPrimary', 'primary', 4.5], ['onPrimary', 'primaryHover', 4.5], ['onPrimary', 'primaryMark', 3],
  // Selection: text on the teal tint.
  ['text', 'primarySoft', 4.5], ['muted', 'primarySoft', 4.5], ['primaryText', 'primarySoft', 4.5],
  // Each hue as a solid chip with its on-colour, as a tint behind text or its own colour, and as the plugin's mark tile.
  ...HUES.flatMap(hue => [['on' + cap(hue), hue, 4.5], [hue, hue + 'Soft', 4.5], ['text', hue + 'Soft', 4.5], ['muted', hue + 'Soft', 4.5], ['onSolid', hue + 'Solid', 4.5]]),
  ['onDangerSolid', 'dangerSolid', 4.5], ['onDangerSolid', 'dangerSolidHover', 4.5],
  // States: text on its tint (the state chip, banners), body text on its tint, and the solid chip.
  ...STATES.flatMap(state => [[state, state + 'Bg', 4.5], ['text', state + 'Bg', 4.5], ['muted', state + 'Bg', 4.5], ['onState', state, 4.5]]),
  ...[1, 2, 3, 4].map(n => ['onTool', 'tool' + n, 4.5]),
];
let lowest = Infinity;
for (const [theme, p] of Object.entries(palettes)) {
  for (const [fg, bg, minimum] of pairs) {
    assert(p[fg] && p[bg], `${theme}: missing ${fg} or ${bg}`);
    const l = [luminance(p[fg]), luminance(p[bg])].sort((a, b) => b - a);
    const ratio = (l[0] + .05) / (l[1] + .05);
    if (process.argv.includes('--verbose')) console.log(`${theme}: ${fg}/${bg} ${ratio.toFixed(2)}:1 (min ${minimum})`);
    assert(ratio >= minimum, `${theme}: ${fg}/${bg} ${ratio.toFixed(2)} < ${minimum}`);
    lowest = Math.min(lowest, ratio / minimum);
  }
}
assert.deepEqual(Object.keys(palettes.light), Object.keys(palettes.dark), 'Light and dark palettes define different roles');
console.log(`Shared sources verified (${Object.keys(manifest.files).length} files); ${pairs.length} palette pairs per theme meet their minimum (tightest margin ${lowest.toFixed(2)}x). This is not proof of native Orca rendering or full accessibility compliance.`);
