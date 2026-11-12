// MOCK evidence for the built Spooler page: light/dark, en/pt-BR, 1280/720/380 px and 200 % zoom, with overflow
// and DOM measurements. Scripted bridge only; not OrcaSlicer.   OUT=<dir> PAGE=<page> node tests/page/shots.mjs
import { writeFile, mkdtemp, rm, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { launch, MOCK_HOST, HELPERS, preparePage } from './cdp.mjs';

const OUT = process.env.OUT; const page = await readFile(process.env.PAGE, 'utf8');
const DISPLAY = { group_same: true, in_use: true, vendor: true, material: true, colour_code: false, diameter: false, rfid: true, bar: true, location: true,
  spool_id: false, comment: true, lot_nr: false, extra_fields: false, exact_weight: true, archived: false, dried: true, use_first: true, low_notice: true,
  head_vendor: true, head_material: true, head_colour_code: true, head_weight: true, head_bar: true, head_spool: true, head_preset: true, head_rfid: true };
const SETTINGS = { url: 'http://192.168.1.10:7912', verified_url: '', default_url: 'http://localhost:7912', source: 'spoolman', low_stock: 100, plate_check: true,
  plate_margin: 10, weight_display: 'both', show_cart: true, spool_columns: 1, progress: { on: true, finish: true, slot: true, idle: 'line' },
  stats: { on: true, cur: 'spoolman' }, display: DISPLAY, drying: { PETG: 30, TPU: 14, PLA: 0 }, cur_code: 'EUR', wizard: false, log_path: '/Users/me/Library/Application Support/OrcaSlicer/spooler/spooler.log' };
const STATE = `
const now = Date.now() / 1000;
const f = (id, name, mat, hex, vendor, fid) => ({id: fid, name, material: mat, color_hex: hex, vendor: {name: vendor}});
const SPOOLS = [
  {id: 1, remaining_weight: 640, initial_weight: 1000, location: 'Shelf A', use_first: true, comment: 'Opened in March', filament: f(1, 'PLA Matte - Black', 'PLA', '1a1a1a', 'Acme', 5)},
  {id: 2, remaining_weight: 980, initial_weight: 1000, location: 'Shelf A', filament: f(2, 'PLA Matte - Black', 'PLA', '1a1a1a', 'Acme', 5)},
  {id: 3, remaining_weight: 70, initial_weight: 1000, location: 'Dry box', extra: {dried: '"2026-09-01"'}, dry_days: 30, filament: f(3, 'PETG HF - Cobalt Blue', 'PETG', '2850a8', 'Bambu Lab', 6)},
  {id: 4, remaining_weight: 15, initial_weight: 750, location: 'Dry box', filament: f(4, 'TPU 95A - Red with an unusually long colour name', 'TPU', 'c12e1f', 'Very Long Manufacturer Name Ltda.', 7)},
  {id: 5, remaining_weight: 530, initial_weight: 1000, location: 'Shelf B', rfid_tags: ['04AB'], filament: f(5, 'PLA Basic - Bambu Green', 'PLA', '3f8e43', 'Bambu Lab', 8)}];
const TRAY = (slot, sp, name, col, type) => ({slot, empty: !sp, type, name, colour: col, remain: sp ? 64 : null, rfid: slot === 1, spool: sp, profile: '_local/spooler/' + name + ' @X1'});
const usage = {enabled: true, mode: 'ask', prints: [
  {id: 'a', name: 'Desk_Organiser_Plate_1', printer: 'X1C', result: 'finished', time: now - 600, state: 'pending', rows: [{slot: 1, grams: 42.3, label: '', spool: null, material: 'PLA', colour: '1a1a1a'}]},
  {id: 'b', name: 'Headphone_Stand', printer: 'X1C', result: 'finished', time: now - 90000, state: 'unknown', rows: [{slot: 2, grams: 94.3, label: 'Acme PLA Black', state: 'unknown', op: 'book', error: 'Spoolman timed out', colour: '1a1a1a'}]}]};
const payload = SCN === 'nourl' ? {type: 'spools', ok: false, error: 'No Spoolman URL configured yet - click Settings to set one.', error_code: 'no_url', peers: {u1control: false}}
  : {type: 'spools', ok: true, origin: 1, source: 'spoolman', spools: SCN === 'empty' ? [] : SPOOLS, low_stock_grams: 100, weight_display: 'both', display: ${JSON.stringify(DISPLAY)},
    show_cart: true, spool_columns: 1, show_printer_tab: true, live_ok: true, profiles: {count: 12}, peers: {u1control: SCN !== 'empty'}, usage, stats: {on: true, cur: 'spoolman'},
    printers: [{id: 'p1', name: 'X1C', ip: '192.168.1.50', has_code: true, units: []}, {id: 'p2', name: 'Workshop Prusa', units: [{kind: 'ams', slots: ['5', null, null, null]}, {kind: 'ext', slots: [null]}]}]};
await until(() => __t.handler);
__t.handler(payload);
__t.handler({type: 'live', live: {links: {p1: 'live'}, printers: [{id: 'p1', link: 'p1', name: 'X1C', age: 4, heads: false, ext: null, units: [{id: 0, kind: 'ams', trays: [TRAY(0, 1, 'PLA Matte - Black', '1a1a1a', 'PLA'), TRAY(1, 3, 'PETG HF - Cobalt Blue', '2850a8', 'PETG'), TRAY(2, null, '', '', ''), TRAY(3, 5, 'PLA Basic - Bambu Green', '3f8e43', 'PLA')]}],
  job: {state: 'RUNNING', name: 'Desk_Organiser_Plate_1', pct: 37, layer: 142, layers: 380, left: 124, tray: {unit: 0, slot: 1}}}]}});
__t.handler({type: 'plate', time: '10:42', rows: [{status: 'short', colour: '2850a8', slots: 'Slot 2', name: 'PETG HF - Cobalt Blue', meta: 'Bambu Lab · Dry box', fill: .07, spool_colour: '2850a8', need_pct: .2, headline: 'Not enough: 130 g short', detail: 'Needs 200 g, 70 g left', ids: [3], first: 1},
  {status: 'ok', colour: '1a1a1a', slots: 'Slot 1', name: 'PLA Matte - Black', meta: 'Acme · Shelf A', fill: .64, spool_colour: '1a1a1a', need_pct: .1, headline: 'Enough', detail: 'Needs 96 g, 640 g left', ids: [1], first: 0}]});
await settle();
if (SCN === 'error') __t.handler({type: 'sent', ok: false, text: 'Spoolman refused the filament: 422 Unprocessable Entity'});
if (SCN === 'printer' || SCN === 'stats') { document.querySelector('[data-tab="' + SCN + '"]').click(); await sleep(300); }
if (SCN === 'printer') { const t = document.querySelector('.us-toggle'); if (t && t.getAttribute('aria-expanded') !== 'true') t.click(); }
if (SCN === 'stats') { const s = [...__t.sent].reverse().find(m => m.type === 'stats');
  __t.handler({type: 'stats', stats: {period: s.period, since: now - 86400 * 60, sign: '€', grams: 2380, prints: 14, cost: 41.2, low: 2,
    mats: [{name: 'PLA', g: 1500}, {name: 'PETG', g: 700}, {name: 'TPU', g: 180}], top: [{label: 'Acme PLA Matte - Black', colour: '1a1a1a', g: 900}, {label: 'Bambu PETG HF - Cobalt Blue', colour: '2850a8', g: 700}],
    weeks: Array.from({length: 8}, (_, i) => ({start: now - (7 - i) * 604800, now: i === 7, parts: [{g: 80 + i * 20, colour: '1a1a1a', label: 'PLA'}, {g: 40, colour: '2850a8', label: 'PETG'}]})),
    soon: [{label: 'PETG HF - Cobalt Blue', colour: '2850a8', weeks: 0.5, low: true, pct: 7, left: 70}], waste: {model: 2000, support: 230, purge: 150, mcost: 34, scost: 4, pcost: 3, cost: 7, prints: 12},
    worst: [{kind: 'purge', name: 'Multicolour_Logo', g: 60, cost: 1.1}], failed: {prints: 1, g: 35, cost: .6}, shelf: {g: 2235, value: 38.5, unpriced: 1, mats: [{name: 'PLA', g: 2150, value: 36}]},
    history: [{time: now - 3600, name: 'Desk_Organiser_Plate_1', printer: 'X1C', result: 'finished', rows: [{label: 'Acme PLA', colour: '1a1a1a', material: 'PLA', grams: 96, cost: 1.9, ws: .08, wp: .05}]}]}});
  const h = document.querySelector('.stv-hh'); if (h) h.click(); }
if (SCN === 'menu') { const b = document.querySelector('[data-stack] .st-head'); b.click(); await settle(); document.querySelector('[data-spool="1"] [data-act="sp-menu"]').click(); }
await sleep(500);
`;
const SCENES = [
  ['spools', 'tab', 'light', 'en', 1280, 1], ['spools', 'tab', 'dark', 'pt_BR', 1280, 1], ['spools', 'tab', 'light', 'pt_BR', 720, 1], ['spools', 'tab', 'dark', 'en', 640, 2],
  ['spools', 'main', 'light', 'pt_BR', 380, 1], ['menu', 'tab', 'dark', 'en', 720, 1], ['empty', 'tab', 'light', 'pt_BR', 1280, 1], ['nourl', 'tab', 'dark', 'en', 720, 1],
  ['error', 'tab', 'light', 'en', 1280, 1], ['printer', 'tab', 'light', 'en', 1280, 1], ['printer', 'tab', 'dark', 'pt_BR', 720, 1], ['printer', 'tab', 'light', 'en', 640, 2],
  ['stats', 'tab', 'dark', 'en', 1280, 1], ['stats', 'tab', 'light', 'pt_BR', 720, 1], ['settings', 'settings', 'light', 'en', 1280, 1], ['settings', 'settings', 'dark', 'pt_BR', 720, 1],
  ['settings', 'settings', 'light', 'pt_BR', 640, 2], ['wizard', 'settings', 'dark', 'en', 720, 1], ['wizard', 'settings', 'light', 'pt_BR', 1280, 1],
];
const dir = await mkdtemp(join(tmpdir(), 'spooler-shots-'));
const browser = await launch();
const metrics = [];
try {
  for (const [scn, mode, theme, lang, width, scale] of SCENES) {
    const boot = { mode, view: mode === 'settings' ? 'settings' : 'main', version: '0.20.1', lang, pref: 'auto', low_stock_default: 100, refresh_ms: 600000,
      display_defaults: DISPLAY, own_fields: ['tag', 'orca_settings', 'dried'], settings: { ...SETTINGS, wizard: scn === 'wizard' } };
    const file = join(dir, `${scn}.html`);
    await writeFile(file, preparePage(page, boot));
    const p = await browser.newPage();
    await p.size(width, 900, scale);
    await p.init(MOCK_HOST);
    await p.goto(pathToFileURL(file).href + '?theme=' + theme);
    const m = await p.evaluate(`(async () => { ${HELPERS} const SCN = ${JSON.stringify(scn)};
      await until(() => document.querySelector('#app > *'));
      ${mode === 'settings' ? 'await sleep(400);' : STATE}
      const over = [...document.querySelectorAll('body *')].filter(e => { const r = e.getBoundingClientRect(); return r.width && r.right > innerWidth + 1 && getComputedStyle(e).position !== 'fixed'; })
        .slice(0, 5).map(e => e.tagName + '.' + String(e.className).slice(0, 40));
      const b = document.querySelector('.p-button'); const cs = b ? getComputedStyle(b) : null;
      return { overflowX: document.documentElement.scrollWidth > innerWidth, scrollWidth: document.documentElement.scrollWidth, innerWidth, overflowing: over,
        dom: document.getElementsByTagName('*').length, lang: document.documentElement.lang, dark: document.documentElement.classList.contains('orca-dark'),
        bodyFont: getComputedStyle(document.body).fontSize, buttonRadius: cs && cs.borderRadius, buttonFont: cs && cs.fontSize,
        violations: __t.violations, errors: __t.errors, rejections: __t.rejections }; })()`);
    const name = `MOCK-spooler-${scn}-${mode}-${theme}-${lang}-${width}${scale > 1 ? '-zoom200' : ''}.png`;
    await writeFile(join(OUT, name), await p.screenshot());
    metrics.push({ name, ...m });
    console.log(name, JSON.stringify({ overflowX: m.overflowX, over: m.overflowing, dom: m.dom, lang: m.lang, dark: m.dark }));
    await p.close();
  }
} finally { await browser.close(); await rm(dir, { recursive: true, force: true }); }
await writeFile(join(OUT, 'metrics-spooler.json'), JSON.stringify(metrics, null, 2));
if (metrics.some(m => m.overflowX || m.violations.length || m.errors.length || m.rejections.length)) { console.log('PROBLEMS'); process.exit(1); }
console.log('OK');
