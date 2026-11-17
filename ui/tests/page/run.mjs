// Behaviour tests of the built Spooler page (ui/dist/spooler-ui.html, the page embedded in spooler_any.py), in an
// owned headless Chrome under a host-like CSP with a scripted OrcaSlicer bridge. Ported from the former page-script
// tests (tests/test_display.py, test_drying, test_notices, test_review_fixes F10-F12, test_printer_control,
// test_detail_export, test_stats, test_send, test_wizard, test_u1control) and extended for S01-S05, B-20..B-24, X01/X04/X05.
//   node tests/page/run.mjs [name-filter]        PAGE=<built page> optional (default ui/dist/spooler-ui.html)
import { readFile, writeFile, mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { launch, MOCK_HOST, HELPERS, preparePage } from './cdp.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const PAGE = process.env.PAGE || resolve(here, '../../dist/spooler-ui.html');
const DISPLAY_DEFAULTS = { group_same: true, in_use: true, vendor: true, material: true, colour_code: false, diameter: false, rfid: true, bar: true,
  location: true, spool_id: false, comment: true, lot_nr: false, extra_fields: false, exact_weight: true, archived: false, dried: true, use_first: true,
  low_notice: true, head_vendor: true, head_material: true, head_colour_code: true, head_weight: true, head_bar: true, head_spool: true, head_preset: true, head_rfid: true };
const SETTINGS = { url: 'http://spoolman:7912', verified_url: '', default_url: 'http://localhost:7912', source: 'spoolman', low_stock: 100, plate_check: true,
  plate_margin: 10, weight_display: 'both', show_cart: false, spool_columns: 1, progress: { on: true, finish: true, slot: true, idle: 'line' },
  stats: { on: true, cur: 'spoolman' }, display: DISPLAY_DEFAULTS, drying: { PETG: 30, PLA: 0 }, cur_code: 'GBP', wizard: false, log_path: '/tmp/spooler.log' };

const PRELUDE = `
const SPOOLS = [
  {id: 1, remaining_weight: 400, initial_weight: 1000, location: 'Shelf A', filament: {id: 5, name: 'Black', material: 'PLA', color_hex: '111111', vendor: {name: 'Acme'}}},
  {id: 2, remaining_weight: 980, initial_weight: 1000, location: 'Shelf B', filament: {id: 5, name: 'Black', material: 'PLA', color_hex: '111111', vendor: {name: 'Acme'}}}];
const TRAY = {slot: 0, empty: false, type: 'PLA', name: 'Black', colour: '111111', remain: 98, rfid: false, spool: 2, profile: '_local/spooler/Acme PLA Black @U1', linked: 'u1control'};
const LIVE = {links: {}, printers: [{id: 'auto-u1', link: 'auto-u1', name: 'U1', heads: true, ext: null, units: [{id: 0, kind: 'ams', trays: [TRAY]}]}]};
const NOTED = [{id: 7, remaining_weight: 500, initial_weight: 1000, location: 'Dry box', lot_nr: 'L-42',
  comment: 'Opened in March, dried twice, prints best at 215 degrees with the textured plate '.repeat(3),
  extra: {tag: '"04a1b2c3"', orca_flow_ratio: '0.95', orca_settings: '"{}"', dryer: '"Box 2"', bought: '2026', empty: '""', dried: '"2026-11-10"'},
  filament: {id: 9, name: 'Red', material: 'PETG', vendor: {name: 'Acme'}}}];
const DEFAULTS = ${JSON.stringify(DISPLAY_DEFAULTS)};
const spools = (list, extra) => post({type: 'spools', ok: true, origin: 3, source: 'spoolman', spools: list, low_stock_grams: 100, weight_display: 'both',
  display: DEFAULTS, show_cart: false, spool_columns: 1, printers: [], show_printer_tab: true, live_ok: false, profiles: {count: 2}, peers: {u1control: false}, ...(extra || {})});
const vis = el => (el ? el.innerText.replace(/\\s+/g, ' ').trim() : '');
async function tab(name) { await click(q('[data-tab="' + name + '"]')); await sleep(50); }
async function pick(root, label) {
  assert(root, 'select to open'); await reveal(root); root.click(); await until(() => q('.p-select-overlay') && !q('.p-select-overlay[class*="enter-active"]'), 'select overlay open');
  const opt = qa('.p-select-overlay [role=option]').find(o => text(o) === label);
  assert(opt, 'option ' + label + ' in ' + qa('.p-select-overlay [role=option]').map(text).join('|'));
  await mouse(opt); await until(() => !q('.p-select-overlay'), 'overlay closed'); await settle();
}
const sentOf = type => __t.sent.filter(m => m.type === type);
const lastOf = type => [...__t.sent].reverse().find(m => m.type === type);
const card = id => q('[data-spool="' + id + '"]');
const alerts = () => qa('[role=alert] .oui-banner').map(text).join(' | ');
// The list is a table of rows; the picked spool's detail, with its actions, sits beside it.
const row = id => q('tr[data-spool="' + id + '"]');
const panel = id => q('[data-detail="' + id + '"]');
async function open(id) { await click(row(id)); await until(() => panel(id), 'detail of spool ' + id); }
const FIELDS = {spool: [{key: 'dryer', name: 'Dryer', field_type: 'text', order: 1}, {key: 'sealed', name: 'Sealed', field_type: 'boolean', order: 2}, {key: 'dried', name: 'Dried', field_type: 'datetime'}],
  filament: [{key: 'grade', name: 'Grade', field_type: 'choice', choices: ['A', 'B'], order: 1}, {key: 'shrink', name: 'Shrink', field_type: 'float', unit: '%', order: 2}, {key: 'orca_settings', name: 'Orca settings', field_type: 'text'}]};
const FILS = [{id: 5, name: 'Black', material: 'PLA', color_hex: '111111', density: 1.24, diameter: 1.75, weight: 1000, vendor: {id: 1, name: 'Acme'}, extra: {grade: '"A"'}},
  {id: 8, name: 'Blue', material: 'PETG', color_hex: '2850a8', density: 1.27, diameter: 1.75, vendor: {id: 1, name: 'Acme'}}];
const editorRef = () => lastOf('spool_action').ref;
const editorData = (spool, ref) => ({type: 'action_result', action: 'editor', ok: true, text: '', ref: ref ?? editorRef(), editor: {fields: FIELDS, filaments: FILS, vendors: ['Acme', 'Polymaker'], spool: spool || null}});
// The editor's answer, then its open transition: the dialog moves the focus inside once it has entered, which would take
// keys typed before that away from their field.
async function loaded(spool) {
  await post(editorData(spool));
  await until(() => dialogEl() && !/enter|leave/.test(dialogEl().className) && dialogEl().contains(document.activeElement), 'editor open and focused');
}
const RAW1 = {...SPOOLS[0], remaining_weight: 734.5678, extra: {dryer: '"Box 1"', dried: '"2026-11-10"'}, filament: FILS[0]};
const stackText = () => [q('[data-stack]'), ...qa('tr.sp-child')].map(vis).join(' ');
`;

const scenarios = [];
const test = (name, body, opts = {}) => scenarios.push({ name, body, ...opts });

// ------------------------------------------------------------------ list (test_display.py PageScriptTest)
test('grouped spools show full totals and the loaded one first', `
  await spools(SPOOLS);
  await post({type: 'live', live: LIVE});
  const head = q('[data-stack]');
  assert(text(head).includes('1,380 g of 2,000 g'), 'totals: ' + text(head));
  assert(text(head).includes('1 in use'), 'in use count');
  await click(q('[data-stack] .st-head'));
  const items = qa('tr.sp-child');
  eq(items.map(c => c.dataset.spool), ['2', '1'], 'spool 2 is loaded: first');
  assert(text(items[0]).includes('In use · U1 · T1'), 'where it is loaded');
`);
test('groups and single spools share one card; stack shows its count', `
  await spools(SPOOLS);
  assert(text(q('.st-count')) === '×2', 'count on the stack row');
  await click(q('[data-stack] .st-head'));
  eq(qa('.st-sub, .sc-subtext').filter(e => e.textContent.includes('Acme')).length, 3, 'group and both spools name the manufacturer');
`);
test('an open stack stays in its column', `
  await spools([...SPOOLS, {...SPOOLS[0], id: 5, filament: {...SPOOLS[0].filament, id: 8, name: 'Blue'}}], {spool_columns: 2});
  eq(qa('.sp-col').length, 2, 'two columns');
  await click(q('[data-stack] .st-head'));
  const col = q('[data-stack]').closest('.sp-col');
  eq(qa('tr.sp-child').map(r => r.closest('.sp-col') === col), [true, true], 'its spools open under it, in its column');
`);
test('every Display switch hides its part', `
  const off = Object.fromEntries(Object.keys(DEFAULTS).map(k => [k, false]));
  await spools(SPOOLS, {display: off});
  await post({type: 'live', live: LIVE});
  assert(!q('[data-stack]'), 'no grouping');
  const list = vis(byTest('list'));
  assert(!list.includes('In use') && !list.includes('Shelf') && !q('.sc-track'), 'no in-use, location or bar: ' + list);
  assert(list.includes('980 g'), 'weight stays');
`);
test('group card follows the switches and keeps the list order', `
  await spools(SPOOLS, {display: {...DEFAULTS, vendor: false, material: false, in_use: false}});
  await post({type: 'live', live: LIVE});
  assert(q('[data-stack]'), 'still grouped');
  await click(q('[data-stack] .st-head'));
  const v = stackText();
  for (const s of ['Acme', 'PLA', 'in use', 'In use']) assert(!v.includes(s), 'hidden: ' + s + ' in ' + v);
  assert(v.indexOf('400 g') < v.indexOf('980 g'), 'list order kept');
`);
test('kilograms when exact weights are off', `
  await spools(SPOOLS, {display: {...DEFAULTS, exact_weight: false}});
  assert(text(q('[data-stack]')).includes('1.38 kg of 2.00 kg'), text(q('[data-stack]')));
`);
test('comment on by default; lot and extra fields off; Spooler fields never shown', `
  await spools(NOTED);
  const note = q('.sc-note');
  assert(note && note.textContent.includes('Opened in March'), 'comment line');
  assert(!note.textContent.includes('L-42') && !note.textContent.includes('dryer'), 'lot and extra off');
  await spools(NOTED, {display: {...DEFAULTS, comment: false}});
  assert(!q('.sc-note'), 'no note line');
  await spools(NOTED, {display: {...DEFAULTS, lot_nr: true, extra_fields: true}});
  const title = q('.sc-note').getAttribute('title');
  for (const s of ['Lot L-42', 'dryer: Box 2', 'bought: 2026', 'Opened in March']) assert(title.includes(s), s);
  eq(title.split('textured plate').length - 1, 3, 'the full comment in the tooltip');
  for (const own of ['tag', '04a1b2c3', 'orca_flow_ratio', 'orca_settings', 'empty:', 'dried:']) assert(!title.includes(own), 'own field ' + own);
`);
test('search covers location, lot, comment and spool number', `
  await spools([...SPOOLS, ...NOTED], {display: {...DEFAULTS, group_same: false}});
  const ids = () => qa('[data-spool]').map(c => +c.dataset.spool).sort();
  const find = async v => { await type(byTest('search'), v); return ids(); };
  eq(await find('shelf b'), [2], 'location');
  eq(await find('l-42'), [7], 'lot');
  eq(await find('textured'), [7], 'comment');
  eq(await find('#7'), [7], 'number');
  eq(await find('#1'), [1], 'exact number');
  eq(await find('black'), [1, 2], 'name');
  eq(await find('#70'), [], 'none');
  assert(byTest('empty-filter') && btn('Clear filters'), 'filtered-empty state with an action (S01)');
  await click(btn('Clear filters'));
  eq(ids().length, 3, 'filters cleared');
`);
test('a Spoolman change asks for a refresh', `
  await spools(SPOOLS);
  const before = sentOf('refresh').length;
  await post({type: 'spool_changed'});
  eq(sentOf('refresh').length, before + 1, 'refresh asked');
`);
test('card actions only for Spoolman; archived spool; move that unlinks a U1 toolhead confirms', `
  const list = [...SPOOLS, {...SPOOLS[0], id: 3, archived: true, location: 'Snapmaker U1 T0', u1_bound: true}];
  await spools(list, {display: {...DEFAULTS, group_same: false}});
  eq(qa('tr[data-spool]').length, 3, 'one row per spool');
  await open(3);
  const actions = vis(panel(3));
  for (const s of ['Set weight from scale', 'Use filament', 'Move', 'Unarchive', 'Add a spool of this filament', 'Open in Spoolman', 'Archived'])
    assert(actions.includes(s), 'detail has ' + s);
  assert(!btn('Archive', panel(3)), 'no Archive on an archived spool');
  eq(row(3).getAttribute('aria-selected'), 'true', 'its row is the selected one');
  await click(btn('Move', panel(3)));
  await until(() => sentOf('spool_action').some(m => m.action === 'locations'), 'locations asked');
  assert(vis(panel(3)).includes('unlinks that toolhead'), 'warns before');
  await type(q('#sc-in-3'), 'Shelf');
  await click(q('[data-detail="3"] [data-act="sp-go"]'));
  assert(dialogOpen() && dialogText().includes('unlinks that toolhead'), 'second step is a confirmation');
  await yes();
  const mv = sentOf('spool_action').find(m => m.action === 'move');
  eq([mv.id, mv.location, mv.origin], [3, 'Shelf', 3], 'moves with the list origin');
  assert(text(q('.sa')).includes('Sending to Spoolman'), 'pending shown');
  await open(1);
  await click(btn('Archive', panel(1)));
  assert(dialogText().includes('Archive Black'), 'archive asks');
  await no();
  assert(!sentOf('spool_action').some(m => m.action === 'archive'), 'declined: nothing sent');
  await spools(list, {source: 'bambu', display: {...DEFAULTS, group_same: false}});
  assert(panel(1) && !btn('Set weight from scale', panel(1)) && !btn('Archive', panel(1)) && !btn('Open in Spoolman', panel(1)), 'no actions for Bambu Cloud');
`);
test('use first chip follows the payload and its switch', `
  await spools([{...SPOOLS[0], use_first: true}, {...SPOOLS[1], id: 9, filament: {...SPOOLS[1].filament, id: 6}}], {display: {...DEFAULTS, group_same: false}});
  eq(qa('tr[data-spool]').filter(r => r.querySelector('[data-chip="use-first"]')).length, 1, 'one chip');
  await spools([{...SPOOLS[0], use_first: true}], {display: {...DEFAULTS, use_first: false, group_same: false}});
  assert(!document.body.textContent.includes('Use first'), 'switch hides it');
`);
test('dried chip and menu: mark, then clear only when marked', `
  const marked = {...SPOOLS[0], extra: {dried: '"' + new Date().toISOString().slice(0, 10) + '"', dryer: '"Box 2"'}, dry_days: 30};
  await spools([marked, {...SPOOLS[1], filament: {...SPOOLS[1].filament, id: 6}}], {display: {...DEFAULTS, group_same: false, extra_fields: true}});
  assert(text(card(1)).includes('Dried today') && byTest('dried'), 'chip');
  assert(!text(card(1)).includes('dried:') && text(card(1)).includes('dryer: Box 2'), 'own field hidden, user field shown');
  await open(1);
  assert(btn('Mark dried today', panel(1)) && btn('Clear dried date', panel(1)), 'both');
  await click(btn('Mark dried today', panel(1)));
  await open(2);
  assert(btn('Mark dried today', panel(2)) && !btn('Clear dried date', panel(2)), 'clear only when marked');
  await open(1);
  await click(btn('Clear dried date', panel(1)));
  eq(sentOf('spool_action').map(m => m.action).filter(a => a !== 'locations'), ['dried', 'clear_dried'], 'actions');
  await spools([marked], {display: {...DEFAULTS, dried: false}});
  assert(!byTest('dried'), 'switch hides it');
`);
test('details panel renders the history as text', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  eq(lastOf('spool_detail').id, 1, 'asked');
  await post({type: 'spool_detail', detail: {id: 1, sign: '£', grams: 80, cost: 2.5, rate: 20, weeks: 5, prints: [{time: 1700000000, name: '<b>Benchy</b>', grams: 40, cost: 1}]}});
  const d = text(panel(1));
  for (const s of ['1 print', '20 g a week on average', 'at 20 g per week', '£2.50', '<b>Benchy</b>']) assert(d.includes(s), 'detail has ' + s + ': ' + d);
  assert(/Lasts about\\s*5\\s*weeks/.test(d), 'lasts about 5 weeks: ' + d);
  assert(!panel(1).querySelector('b b, td b'), 'markup is text, not HTML');
`);
test('weights and grams fields validate before sending (no blank grams)', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  await click(btn('Use filament', panel(1)));
  assert(q('[data-detail="1"] [data-act="sp-go"]').disabled, 'Save waits for grams');
  await type(q('#sc-in-1'), 'abc');
  assert(q('[data-detail="1"] [data-act="sp-go"]').disabled && text(panel(1)).includes('Enter a number of grams'), 'invalid explained');
  await type(q('#sc-in-1'), '12,5');
  await press('Enter');
  const use = sentOf('spool_action').find(m => m.action === 'use');
  eq(use.grams, '12.5', 'decimal comma accepted');
  await open(1);
  await click(btn('Use filament', panel(1)));
  for (const bad of ['0', '-3', '100001']) {
    await type(q('#sc-in-1'), bad);
    assert(q('[data-detail="1"] [data-act="sp-go"]').disabled && text(panel(1)).includes('above 0'), bad + ' refused before sending');
  }
  eq(sentOf('spool_action').filter(m => m.action === 'use').length, 1, 'nothing more sent');
`);

test('grams left: set from the card, 0 allowed for an empty spool', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  await click(btn('Set grams left', panel(1)));
  assert(text(panel(1)).includes('0 for an empty spool'), 'explains');
  await type(q('#sc-in-1'), '-2');
  assert(q('[data-detail="1"] [data-act="sp-go"]').disabled && text(panel(1)).includes('from 0 to 100,000'), 'negative refused');
  await type(q('#sc-in-1'), '0');
  await press('Enter');
  const left = sentOf('spool_action').find(m => m.action === 'remaining');
  eq([left.id, left.grams, left.origin], [1, '0', 3], 'sent with the list origin');
  await open(1);
  await click(btn('Set grams left', panel(1)));
  await type(q('#sc-in-1'), '412,5');
  await press('Enter');
  eq(lastOf('spool_action').grams, '412.5', 'decimal comma');
`);
test('a note is added, edited and removed from the card', `
  await spools([{...SPOOLS[0], comment: ''}, {...SPOOLS[1], comment: 'tangled <b>once</b>'}], {display: {...DEFAULTS, group_same: false}});
  await open(1);
  assert(btn('Add a note', panel(1)) && !btn('Edit note', panel(1)), 'no note yet: add');
  await click(btn('Add a note', panel(1)));
  await type(q('#sc-in-1'), 'Dry before use');
  await click(q('[data-detail="1"] [data-act="sp-go"]'));
  eq(lastOf('spool_action'), {type: 'spool_action', action: 'comment', id: 1, origin: 3, comment: 'Dry before use'}, 'saved');
  await open(2);
  await click(btn('Edit note', panel(2)));
  eq(q('#sc-in-2').value, 'tangled <b>once</b>', 'starts from the current note');
  assert(!q('[data-detail="2"] [data-act="sp-go"]').disabled, 'clearing is allowed');
  await type(q('#sc-in-2'), '');
  await click(q('[data-detail="2"] [data-act="sp-go"]'));
  eq(lastOf('spool_action').comment, '', 'empty removes it');
`);
test('add several spools of a filament at once', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  await click(btn('Add a spool of this filament', panel(1)));
  await until(() => dialogOpen());
  assert(dialogText().includes('Each one starts full'), 'says what is added');
  eq(q('#dlg-input').value, '1', 'one by default');
  await yes();
  const one = lastOf('spool_action');
  eq([one.action, one.filament, 'count' in one], ['add', SPOOLS[0].filament.id, false], 'one spool: no count sent');
  await open(1);
  await click(btn('Add a spool of this filament', panel(1)));
  await until(() => dialogOpen());
  await type(q('#dlg-input'), '4');
  await yes();
  eq(lastOf('spool_action').count, 4, 'four');
  const before = sentOf('spool_action').length;
  await open(1);
  await click(btn('Add a spool of this filament', panel(1)));
  await until(() => dialogOpen());
  await type(q('#dlg-input'), '25');
  await yes();
  eq(sentOf('spool_action').length, before, 'too many: nothing sent');
  assert(alerts().includes('1 to 20'), 'and why: ' + alerts());
`);

test('the detail asks for history once the list settles; a pick asks at once; rows control the detail', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await until(() => sentOf('spool_detail').length === 1, 'first row asked after the list settled');
  const before = sentOf('spool_detail').length;
  for (const v of ['shelf b', 'shelf a', 'shelf b']) { const el = byTest('search'); el.value = v; el.dispatchEvent(new Event('input')); await sleep(60); }
  await until(() => sentOf('spool_detail').length > before, 'asked after typing stopped');
  await sleep(400);
  eq(sentOf('spool_detail').slice(before).map(m => m.id), [2], 'one request, for the row shown once typing stopped');
  const el = byTest('search'); el.value = ''; el.dispatchEvent(new Event('input')); await settle();
  // Spool 1 is the top row again and its request is due after the settle time; pick spool 2, which is not the top
  // row, so the request the pick sends can't be confused with that one, whenever it fires.
  const of2 = () => sentOf('spool_detail').filter(m => m.id === 2).length;
  const n = of2();
  await open(2);
  eq([of2(), lastOf('spool_detail').id], [n + 1, 2], 'a pick asks at once');
  eq(row(2).getAttribute('aria-controls'), 'sp-detail', 'the row controls the detail');
  assert(q('#sp-detail') === panel(2), 'and the detail is that element');
`);
test('N1: the shown spool is asked again when an action settles and when a newer list arrives', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  await post({type: 'spool_detail', detail: {id: 1, sign: '£', grams: 40, cost: 1, rate: 20, weeks: 20, prints: [{time: 1700000000, name: 'Benchy', grams: 40, cost: 1}]}});
  const asked = () => sentOf('spool_detail').filter(m => m.id === 1).length;
  let n = asked();
  await click(btn('Mark dried today', panel(1)));
  // The result and the list it refreshes, delivered together: they make one request. (Arriving more than the settle
  // time apart, they would make two; the page only coalesces a burst.)
  const result = post({type: 'action_result', ok: true, action: 'dried', text: 'Spool #1 updated'});
  await Promise.all([result, spools(SPOOLS, {display: {...DEFAULTS, group_same: false}})]);
  await until(() => asked() > n, 'asked again after the action');
  await sleep(400);
  eq(asked(), n + 1, 'a result and its list arriving together make one request');
  assert(text(panel(1)).includes('Benchy'), 'the old history stays until the new one arrives');
  n = asked();
  await spools([{...SPOOLS[0], remaining_weight: 300}, SPOOLS[1]], {display: {...DEFAULTS, group_same: false}});
  await until(() => asked() > n, 'asked again for a newer list');
  await post({type: 'action_result', ok: false, action: 'dried', text: 'refused'});
  await sleep(400);
  eq(asked(), n + 1, 'a refused action asks nothing');
`);
test('N2: the same id from another source is another spool; only Spoolman is asked', `
  await spools([SPOOLS[0]], {display: {...DEFAULTS, group_same: false}});
  await open(1);
  const n = sentOf('spool_detail').length;
  await spools([SPOOLS[0]], {source: 'bambu', display: {...DEFAULTS, group_same: false}});
  await sleep(400);
  eq(sentOf('spool_detail').length, n, 'Bambu Cloud has no history: nothing asked');
  assert(!/Loading/.test(text(panel(1))), 'no Loading stuck on the Bambu spool: ' + text(panel(1)));
  await spools([SPOOLS[0]], {source: 'spoolman', display: {...DEFAULTS, group_same: false}});
  await until(() => sentOf('spool_detail').length > n, 'back on Spoolman: asked afresh for the same id');
  await post({type: 'spool_detail', detail: {id: 1, sign: '£', grams: 0, cost: 0, rate: null, weeks: null, prints: []}});
  assert(!/Loading/.test(text(panel(1))), 'the answer shows: ' + text(panel(1)));
`);
test('detail facts follow the Display switches', `
  await spools([{...SPOOLS[0], extra: {dried: '"2026-11-01"'}, rfid_tags: ['04AB']}], {display: {...DEFAULTS, group_same: false, location: false, dried: false, rfid: false}});
  await open(1);
  const facts = vis(q('.oui-kv', panel(1)) || panel(1));
  for (const k of ['LOCATION', 'DRIED', 'RFID TAG']) assert(!facts.toUpperCase().includes(k), 'hidden: ' + k + ' in ' + facts);
  assert(facts.toUpperCase().includes('PRICE'), 'price has no switch and stays');
`);
test('narrow: a pick moves focus to the detail under the list', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(2);
  await until(() => document.activeElement && document.activeElement.matches('#sp-detail .oui-panel-title'), 'focus on the detail heading');
`, { width: 720 });
test('380 px dock: every tab is reachable, icons only, named', `
  await spools(SPOOLS, {stats: {on: true, cur: 'spoolman'}});
  const tabs = qa('[role=tab]');
  assert(tabs.length >= 2, 'tabs: ' + tabs.length);
  for (const b of tabs) {
    const r = b.getBoundingClientRect();
    assert(r.left >= 0 && r.right <= innerWidth, 'inside the bar: ' + b.dataset.tab + ' ' + r.left + '..' + r.right);
    assert(b.title && text(b).startsWith(b.title), 'named and with a tooltip: ' + b.dataset.tab);
  }
`, { width: 380, mode: 'main' });

// ------------------------------------------------------------------ status, errors, empty states (F10, S01, S02, B-20)
test('F10: a read error keeps the old list of the same source, marked; another source drops it', `
  await spools([{id: 1, remaining_weight: 100, filament: {id: 1, name: 'OldSpool', material: 'PLA'}}]);
  await post({type: 'spools', ok: false, origin: 3, error: 'SYNTHETIC OFFLINE', error_code: 'read_failed'});
  assert(text(byTest('stale')).includes('SYNTHETIC OFFLINE') && text(byTest('stale')).includes('may be out of date'), 'marked old');
  assert(card(1), 'old list kept');
  await type(byTest('search'), 'old');
  assert(card(1) && byTest('stale'), 'survives filtering');
  await post({type: 'spools', ok: false, error: 'No Spoolman URL configured yet', error_code: 'no_url'});
  assert(!card(1) && byTest('empty-no-url'), 'another source: list dropped, first-use state');
  assert(btn('Open Settings', byTest('empty-no-url')), 'next step offered (S02)');
  assert(byTest('sync').disabled && byTest('send').disabled, 'actions that need Spoolman are off (S02)');
  assert(document.body.textContent.includes('no Spoolman address set'), 'with the reason');
  await post({type: 'spools', ok: true, origin: 4, source: 'spoolman', spools: [], peers: {u1control: false}});
  assert(byTest('empty-none') && !byTest('stale') && !byTest('empty-no-url'), 'empty stock is not an error (S01)');
  assert(!byTest('sync').disabled, 'actions back');
`);
test('S02: a failed first read offers retry and Settings', `
  await post({type: 'spools', ok: false, error: 'Connection refused', error_code: 'read_failed'});
  assert(byTest('empty-error') && btn('Try again', byTest('empty-error')) && btn('Open Settings', byTest('empty-error')), 'actions');
  const before = sentOf('refresh').length;
  await click(btn('Try again', byTest('empty-error')));
  eq(sentOf('refresh').length, before + 1, 'retry asks for a read');
  await click(btn('Open Settings', byTest('empty-error')));
  eq(lastOf('settings').type, 'settings', 'settings asked');
`);
test('B-20: action errors stay until dismissed and are announced; successes clear', `
  await spools(SPOOLS);
  await click(byTest('sync'));
  assert(text(q('.sa [role=status]')).includes('Syncing presets'), 'pending announced');
  await post({type: 'sent', ok: false, text: 'Spoolman refused the filament'});
  assert(alerts().includes('Error:') && alerts().includes('Spoolman refused the filament'), 'error in role=alert: ' + alerts());
  await sleep(9000);
  assert(alerts().includes('Spoolman refused'), 'still there after 9 s');
  await click(btn('Dismiss', q('.sa')));
  assert(!alerts(), 'dismissed');
  await post({type: 'action_result', ok: true, text: 'Spool #1 updated'});
  assert(text(q('.sa [role=status]')).includes('Spool #1 updated'), 'success shown');
  await sleep(8500);
  assert(!text(q('.sa')).includes('Spool #1 updated'), 'success clears');
`, { slow: true });
test('S03: Send is named for what it does and explains itself', `
  await spools(SPOOLS);
  eq(text(byTest('send')), 'Send Preset Edits to Spoolman', 'label');
  assert(byTest('send').getAttribute('aria-describedby') && text(q('#sv-why')).includes('unsaved edits of the Spooler preset'), 'description');
  await click(byTest('send'));
  eq(lastOf('send').type, 'send', 'sent');
`);
test('X01/X05: with U1 Control running, each tab says where the U1 lives and why two tabs', `
  await spools(SPOOLS, {peers: {u1control: true}});
  assert(text(byTest('peer-u1')).includes('U1 Control tab'), 'spools tab line');
  assert(!document.body.textContent.includes('u1control'), 'named U1 Control, never u1control');
  await click(q('[data-test="peer-u1"] summary'));
  assert(text(byTest('peer-u1')).includes('no way to hide a tab'), 'honest about the host limit');
  await spools(SPOOLS, {peers: {u1control: false}});
  assert(!byTest('peer-u1'), 'solo: nothing');
`);

// ------------------------------------------------------------------ printer tab (F11, F12, test_printer_control, X05)
test('slot card shows the spool details and says it was linked by U1 Control', `
  await spools(SPOOLS, {printers: [{id: 'auto-u1', name: 'U1', auto: true, ip: '10.0.0.5', units: []}], live_ok: true});
  await tab('printer');
  await post({type: 'live', live: {...LIVE, links: {'auto-u1': 'live'}}});
  const c = q('.tc');
  for (const s of ['Acme', 'PLA', '#111111', '980 g of 1,000 g left', 'Spool #2', 'Shelf B', 'linked by U1 Control', 'Acme PLA Black @U1'])
    assert(text(c).includes(s), 'slot card has ' + s + ': ' + text(c));
  assert(c.getAttribute('title').includes('Spool linked by U1 Control'), 'tooltip names U1 Control (X05)');
  assert(text(q('[data-source="printer"]', c)) === '98% on the printer' && text(q('[data-source="spoolman"]', c)).endsWith('· Spoolman'), 'each amount names its source');
`);
test('F11: assign and picker are keyboard controls; focus returns to the slot', `
  await spools([{id: 7, remaining_weight: 100, filament: {id: 1, name: 'PLA Black'}}], {printers: [{id: 'p1', name: 'P', units: [{kind: 'ams', slots: [null, null, null, null]}]}]});
  await tab('printer');
  const a = q('[data-focus-key="assign:p1:0:2"]');
  eq(a.getAttribute('aria-label'), 'Assign a spool to slot 3 of P', 'named control');
  a.focus(); await press('Enter');
  await until(() => document.activeElement && document.activeElement.matches('[data-test="picker-search"]'), 'search focused');
  await press('ArrowDown');
  assert(document.activeElement.dataset.pick === '7', 'Down moves into the list');
  await press('Escape');
  await until(() => document.activeElement === q('[data-focus-key="assign:p1:0:2"]'), 'Escape returns to the slot');
  await press('Enter');
  await until(() => document.activeElement && document.activeElement.matches('[data-test="picker-search"]'));
  await press('Enter');
  eq(lastOf('printers').printers[0].units[0].slots[2], '7', 'Enter takes the first spool');
  await until(() => document.activeElement === q('[data-focus-key="clear:p1:0:2"]'), 'focus on the slot\\'s remove button');
`);
test('F12: age alone does not redraw a slot; going stale is shown', `
  await spools(SPOOLS, {printers: [{id: 'p', name: 'X1', auto: true, ip: '10.0.0.9', units: []}], live_ok: true});
  await tab('printer');
  const live = (age, spool) => post({type: 'live', live: {links: {p: 'live'}, printers: [{id: 'p', link: 'p', name: 'X1', age, units: [{id: 0, kind: 'ams', trays: [{...TRAY, spool}]}]}]}});
  await live(1, 1);
  const node = q('.tc');
  await live(6, 1); await live(11, 1);
  assert(q('.tc') === node, 'same element after age-only updates');
  await live(200, 1);
  assert(text(q('.pp')).includes('Not updated for 3 min'), 'stale shown');
  await live(206, 2);
  assert(text(q('.tc')).includes('Spool #2'), 'a real change redraws');
`);
test('single-extruder Klipper card: change spool, clear only with a spool, result on the card', `
  const sv = ext => ({id: 'auto-sv', link: 'auto-sv', name: 'SV06', heads: false, units: [], ext, spool_set: true, age: 0});
  await spools([{id: 7, remaining_weight: 100, filament: {id: 1, name: 'PLA Black'}}], {printers: [{id: 'auto-sv', name: 'SV06', auto: true, ip: '10.0.0.7', units: []}], live_ok: true});
  await tab('printer');
  await post({type: 'live', live: {links: {'auto-sv': 'live'}, printers: [sv({...TRAY, spool: 7})]}});
  assert(btn('Change spool') && btn('Clear'), 'change and clear');
  await click(btn('Clear'));
  assert(dialogText().includes('SV06'), 'clear asks');
  await yes();
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: null}, 'clear sent');
  await post({type: 'moon_spool', id: 'auto-sv', ok: false, text: 'SV06 refused <x>'});
  assert(text(q('.lu')).includes('SV06 refused <x>') && q('.lu [data-test="moon-note"] [data-state="error"]'), 'result as text on the card');
  assert(alerts().includes('SV06 refused'), 'and persists in the status area');
  await post({type: 'live', live: {links: {'auto-sv': 'live'}, printers: [sv(null)]}});
  assert(btn('Change spool') && !btn('Clear'), 'no active spool: change only');
  await click(btn('Change spool'));
  await until(() => q('[data-pick="7"]'));
  await click(q('[data-pick="7"]'));
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: 7, origin: 3}, 'set with the list origin');
`);
test('changing the active spool while printing asks again, naming the consequence', `
  const sv = {id: 'auto-sv', link: 'auto-sv', name: 'SV06', heads: false, units: [], ext: {...TRAY, spool: 7}, spool_set: true, age: 0};
  await spools([{id: 7, remaining_weight: 100, filament: {id: 1, name: 'PLA Black'}}, {id: 8, remaining_weight: 900, filament: {id: 2, name: 'PETG Red'}}],
    {printers: [{id: 'auto-sv', name: 'SV06', auto: true, ip: '10.0.0.7', units: []}], live_ok: true});
  await tab('printer');
  await post({type: 'live', live: {links: {'auto-sv': 'live'}, printers: [sv]}});
  await click(btn('Change spool'));
  await until(() => q('[data-pick="8"]'));
  await click(q('[data-pick="8"]'));
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: 8, origin: 3}, 'first try has no confirmation');
  await post({type: 'moon_spool', id: 'auto-sv', spool: 8, ok: false, confirm: true, state: 'RUNNING', text: 'SV06 is running a print'});
  await until(() => dialogOpen(), 'asks');
  assert(dialogText().includes('SV06 is printing') && dialogText().includes('rest of this print'), 'names the consequence: ' + dialogText());
  assert(!alerts().includes('SV06 is running'), 'not shown as a failure');
  await no();
  eq(sentOf('moon_spool').length, 1, 'go back: nothing more sent');
  await post({type: 'moon_spool', id: 'auto-sv', spool: 8, ok: false, confirm: true, state: 'PAUSE', text: 'paused'});
  await until(() => dialogOpen(), 'asks again');
  assert(dialogText().includes('paused'), 'paused wording');
  assert(btn('Change to spool #8 anyway'), 'answer names the spool');
  await yes();
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: 8, origin: 3, confirm: true}, 'confirmed resend');
  await post({type: 'moon_spool', id: 'auto-sv', spool: null, ok: false, confirm: true, state: 'RUNNING', text: 'x'});
  await until(() => dialogOpen());
  assert(btn('Clear it anyway'), 'clear wording');
  await yes();
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: null, confirm: true}, 'confirmed clear');
`);
test('change spool is hidden for the U1, filament changers and Bambu Cloud', `
  const u1 = {id: 'auto-u1', link: 'auto-u1', name: 'U1', heads: true, ext: null, spool_set: false, age: 0, units: [{id: 0, kind: 'ams', trays: [TRAY]}]};
  await spools(SPOOLS, {printers: [{id: 'auto-u1', name: 'U1', auto: true, ip: '1.1.1.1', units: []}, {id: 'auto-afc', name: 'AFC', auto: true, ip: '1.1.1.2', units: []}], live_ok: true});
  await tab('printer');
  await post({type: 'live', live: {links: {'auto-u1': 'live', 'auto-afc': 'live'}, printers: [u1, {...u1, id: 'auto-afc', link: 'auto-afc', name: 'AFC', heads: false}]}});
  assert(!btn('Change spool'), 'not for U1 or lanes');
  await spools(SPOOLS, {source: 'bambu', printers: [{id: 'auto-sv', name: 'SV06', auto: true, ip: '1', units: []}], live_ok: true});
  await post({type: 'live', live: {links: {'auto-sv': 'live'}, printers: [{id: 'auto-sv', link: 'auto-sv', name: 'SV06', heads: false, units: [], ext: TRAY, spool_set: true, age: 0}]}});
  assert(!btn('Change spool'), 'not for Bambu Cloud');
`);
test('manual printer editing: add, rename, units, remove with confirmation', `
  await spools(SPOOLS);
  await tab('printer');
  assert(text(q('.pv')).includes('No printers yet'), 'empty state');
  await click(byTest('add-printer'));
  const p = lastOf('printers').printers[0];
  eq(p.name, 'Printer', 'default name');
  await until(() => document.activeElement && document.activeElement.matches('input'), 'name field focused');
  await type(document.activeElement, 'Bench');
  await press('Enter');
  eq(lastOf('printers').printers[0].name, 'Bench', 'renamed');
  await click(btn('+ AMS')); await click(btn('+ External spool'));
  eq(lastOf('printers').printers[0].units.map(u => [u.kind, u.slots.length]), [['ams', 4], ['ext', 1]], 'units sorted');
  assert(!btn('+ External spool'), 'one external spool only');
  await click(btn('Remove printer'));
  await no();
  eq(lastOf('printers').printers.length, 1, 'declined');
  await click(btn('Remove printer')); await yes();
  eq(lastOf('printers').printers.length, 0, 'removed');
`);
test('network printer: PrusaLink link form, toolheads, and a slice-filled toolhead taken from the live poll', `
  await spools(SPOOLS);
  await tab('printer');
  await click(byTest('add-printer'));
  await press('Enter');
  const id = lastOf('printers').printers[0].id;
  await click(btn('+ Toolhead')); await click(btn('+ Toolhead'));
  eq(lastOf('printers').printers[0].units.map(u => u.kind), ['tool', 'tool'], 'two toolheads');
  await click(q('[data-act="link"]'));
  assert(vis(q('.pp-link')).includes('Serial number'), 'Bambu asks for the serial');
  await pick(q('[data-test="link-type"]'), 'PrusaLink');
  assert(!vis(q('.pp-link')).includes('Serial number'), 'no serial for PrusaLink');
  assert(vis(q('.pp-link')).includes('Password') && vis(q('.pp-link')).includes('always asked'), 'password label and the asking note');
  await type(q('.pp-link input[placeholder="192.168.1.50"]'), '10.0.0.5');
  await type(byTest('link-user'), 'maker');
  await type(q('.pp-link input[type="password"]'), 'secret');
  await click(btn('Save'));
  const saved = lastOf('printers').printers[0];
  eq([saved.type, saved.ip, saved.user, saved.slice_fill, saved.serial], ['prusalink', '10.0.0.5', 'maker', true, ''], 'saved as PrusaLink');
  eq(lastOf('printer_code'), {type: 'printer_code', id, code: 'secret'}, 'password sent once');
  const filled = {...saved, has_code: true, units: [{kind: 'tool', slots: ['1']}, {kind: 'tool', slots: [null]}]};
  post({type: 'live', live: {links: {}, printers: []}, usage: {enabled: true, mode: 'ask', prints: []}, printers_rev: 1, printers: [filled]});
  await settle();
  assert(q('.pp [data-spool="1"]'), 'the toolhead shows the spool the slice put on it');
  assert(vis(q('.pp')).includes('T1'), 'toolheads are named T1, T2');
`);
test('Klipper printer: hand-set gates, toolheads, slice fill switch and presets per printer', `
  const voron = {id: 'auto-v', name: 'Voron', auto: true, kind: 'moonraker', ip: 'http://10.0.0.9', units: [], has_code: true};
  const mk4 = {id: 'mk4', name: 'MK4', type: 'prusalink', ip: '10.0.0.5', has_code: true, units: [{kind: 'tool', slots: [null]}]};
  await spools(SPOOLS, {printers: [voron, mk4], printer_presets: ['Voron 0.4', 'MK4 0.4'], slice_map: {}});
  await tab('printer');
  const kc = () => q('.pp:has([data-test="klipper-slots"])');
  assert(kc(), 'Klipper printer offers hand-set slots');
  await pick(q('[data-test="gate-count"]'), '6');
  const saved = lastOf('printers').printers.find(p => p.id === 'auto-v');
  eq(saved.units, [{kind: 'gate', slots: [null, null, null, null, null, null]}], 'six gates saved');
  assert(vis(kc()).includes('MMU gates') && qa('[data-act="assign"]', kc()).length === 6, 'gates shown to assign');
  await click(qa('[data-act="assign"]', kc())[1]);
  await until(() => q('[data-pick="2"]'));
  await click(q('[data-pick="2"]'));
  eq(lastOf('printers').printers.find(p => p.id === 'auto-v').units[0].slots[1], '2', 'spool on gate 2');
  await click(q('[data-test="klipper-fill"] input') || q('[data-test="klipper-fill"]'));
  eq(lastOf('printers').printers.find(p => p.id === 'auto-v').slice_fill, false, 'slice fill off');
  assert(qa('[data-test="presets"]').length === 2, 'two fillable printers: each asks for its presets');
  q('.p-multiselect', kc()).click();
  await until(() => qa('.p-multiselect-overlay [role=option]').length === 2, 'presets listed');
  await mouse(qa('.p-multiselect-overlay [role=option]').find(o => text(o).includes('Voron 0.4')));
  eq(lastOf('slice_map'), {type: 'slice_map', map: {'Voron 0.4': 'auto-v'}}, 'preset given to the Voron');
  await press('Escape'); await settle();
  await post({type: 'live', live: {links: {}, printers: []}, printers_rev: 5, printers: [{...voron, units: [{kind: 'tool', slots: ['1']}, {kind: 'tool', slots: [null]}]}, mk4]});
  assert(vis(kc()).includes('T2') && !q('[data-test="gate-count"]'), 'two extruders: toolheads, no gate count');
  await spools(SPOOLS, {printers: [{...voron, managed: true}], printer_presets: []});
  assert(!q('[data-test="klipper-slots"]') && !q('[data-test="presets"]'), 'printer reporting its own gates: read-only, nothing to set');
`);
test('Happy Hare gates are shown read-only with their note', `
  const hh = {id: 'auto-hh', name: 'Trident HH', auto: true, kind: 'moonraker', ip: 'http://10.0.0.11', units: [], managed: true};
  await spools(SPOOLS, {printers: [hh], live_ok: true});
  await tab('printer');
  await post({type: 'live', live: {links: {'auto-hh': 'live'}, printers: [{id: 'auto-hh', link: 'auto-hh', name: 'Trident HH', heads: false, hh: true, unit_label: 'MMU', age: 0,
    spool_set: false, ext: null, units: [{id: 0, kind: 'ams', trays: [TRAY, {slot: 1, empty: true}]}]}]}});
  const hv = vis(q('.pp'));
  assert(hv.includes('MMU') && hv.includes('Happy Hare reports these gates'), 'gates and note: ' + hv);
  assert(!q('[data-test="klipper-slots"]') && !q('[data-act="assign"]') && !btn('Change spool'), 'nothing to set by hand');
`);
test('slice pick: several matching spools ask which one, answer or leave it', `
  const voron = {id: 'auto-v', name: 'Voron', auto: true, kind: 'moonraker', ip: 'http://10.0.0.9', units: [{kind: 'gate', slots: [null, null, null]}]};
  const pk = n => ({printer: 'auto-v', name: 'Voron', n, slice: 7, unit: 0, slot: n - 1, material: 'PLA', colour: '111111', spools: [1, 2]});
  await spools(SPOOLS, {printers: [voron], slice_picks: [pk(1), pk(3)]});
  await until(() => q('[data-test="slice-pick"]'), 'asks');
  const d = () => vis(q('[data-test="slice-pick"]'));
  assert(d().includes('Gate 1') && d().includes('Filament 1') && d().includes('Voron'), 'names the slot: ' + d());
  assert(q('[data-test="slice-pick"] [data-pick="1"]') && q('[data-test="slice-pick"] [data-pick="2"]'), 'both spools offered');
  await click(q('[data-test="slice-pick"] [data-pick="2"]'));
  eq(lastOf('slice_pick'), {type: 'slice_pick', printer: 'auto-v', n: 1, slice: 7, spool: 2}, 'answer sent');
  await until(() => d().includes('Filament 3'), 'next pick');
  await click(byTest('pick-leave'));
  eq(lastOf('slice_pick'), {type: 'slice_pick', printer: 'auto-v', n: 3, slice: 7, spool: null}, 'left as it is');
  await until(() => !q('[data-test="slice-pick"]'), 'closed');
  await post({type: 'live', live: {links: {}, printers: []}, slice_picks: [{...pk(2), spools: [99]}]});
  await until(() => lastOf('slice_pick').n === 2, 'no spool left to choose: left as it is without asking');
  eq(lastOf('slice_pick').spool, null, 'answered null');
`);
test('unknown booking asks the user instead of offering Book; resolve sends the answer', `
  await spools(SPOOLS, {usage: {enabled: true, mode: 'ask', prints: [{id: 'job', name: 'Benchy', printer: 'X1', result: 'finished', pct: 100, time: Date.now() / 1000, state: 'unknown',
    rows: [{slot: 1, grams: 10, label: 'PLA', state: 'unknown', op: 'book', error: 'check'}]}]}});
  await tab('printer');
  if (!q('#us-list')) await click(q('.us-toggle'));
  const c = q('[data-run="job"]');
  assert(text(c).includes('Check Spoolman') && btn('It was booked', c) && btn('It wasn’t booked', c), 'asks');
  assert(!q('[data-usage="book"]', c), 'no Book');
  await click(btn('It wasn’t booked', c));
  eq(lastOf('usage_resolve'), {type: 'usage_resolve', run: 'job', slot: 1, outcome: 'not_applied'}, 'answer sent');
`);
test('booking: grams editable and required, chosen spool sent with origin; undo adds back after confirming', `
  const now = Date.now() / 1000;
  const usage = {enabled: true, mode: 'ask', prints: [
    {id: 'a', name: 'Benchy', printer: 'X1', result: 'finished', time: now, state: 'pending', rows: [{slot: 1, grams: 12.3, label: '', spool: null, material: 'PLA'}]},
    {id: 'b', name: 'Cube', printer: 'X1', result: 'finished', time: now, state: 'booked', rows: [{slot: 2, grams: 5, label: 'Acme Black', spool: 1, state: 'booked'}]}]};
  await spools(SPOOLS, {usage});
  await tab('printer');
  if (!q('#us-list')) await click(q('.us-toggle'));
  const a = q('[data-run="a"]');
  assert(text(a).includes('Not identified'), 'unidentified spool flagged');
  await type(q('[data-run="a"] .us-g input'), '');
  assert(q('[data-run="a"] [data-usage="book"]').disabled && text(a).includes('needs grams'), 'blank grams never book');
  await type(q('[data-run="a"] .us-g input'), '15');
  await pick(q('[data-run="a"] .us-sel'), 'Acme · Black · #1 · 400 g');
  await click(q('[data-run="a"] [data-usage="book"]'));
  eq(lastOf('usage_book'), {type: 'usage_book', run: 'a', rows: [{slot: 1, grams: 15, spool: '1'}], origin: 3}, 'booked as edited');
  assert(q('[data-run="b"] [data-usage="undo"]').disabled, 'no undo while a booking is in flight');
  await post({type: 'usage', usage});
  await click(q('[data-run="b"] [data-usage="undo"]'));
  await until(dialogOpen, 'undo dialog'); assert(dialogText().includes('400 g + 5') && dialogText().includes('405'), 'shows what goes back: ' + dialogText());
  await click(q('[data-usage="unbook"]'));
  eq(lastOf('usage_undo'), {type: 'usage_undo', run: 'b'}, 'undo sent');
`);
for (const [host, shown, pasted] of [['en', '2.5 g', '7.5 g'], ['de', '2,5 g', '7,5 g'], ['es', '2,5 g', '7,5 g'], ['pt_BR', '2,5 g', '7,5 g']]) {
  test(`usage grams: "2.5" typed and "7.5" pasted keep their decimal in ${host}`, `
  const usage = {enabled: true, mode: 'ask', prints: [{id: 'a', name: 'Benchy', printer: 'X1', result: 'finished', time: Date.now() / 1000, state: 'pending',
    rows: [{slot: 1, grams: 12.3, label: 'Acme Black', spool: 1, material: 'PLA'}]}]};
  await spools(SPOOLS, {usage});
  await tab('printer');
  if (!q('#us-list')) await click(q('.us-toggle'));
  const input = () => q('[data-run="a"] .us-g input');
  await type(input(), '2.5');
  input().blur(); await settle();
  eq(input().value, ${JSON.stringify(shown)}, 'typed');
  await click(q('[data-run="a"] [data-usage="book"]'));
  eq(lastOf('usage_book').rows[0].grams, 2.5, 'typed value booked');
  await post({type: 'usage', usage});
  const data = new DataTransfer(); data.setData('text', '7.5');
  input().focus(); input().select();
  input().dispatchEvent(new ClipboardEvent('paste', {clipboardData: data, bubbles: true, cancelable: true}));
  input().blur(); await settle();
  eq(input().value, ${JSON.stringify(pasted)}, 'pasted');
  `, { lang: host });
}
test('plate check: rows, attention pill, recheck and dismiss', `
  await spools(SPOOLS);
  await post({type: 'plate', time: '10:00', rows: [{status: 'short', colour: '111111', slots: 'T1', name: 'Black', meta: 'Acme', fill: .4, spool_colour: '111111', need_pct: .6,
    headline: 'Not enough', detail: 'needs 600 g', ids: [1], first: 0}]});
  await tab('printer');
  assert(text(byTest('plate')).includes('1 needs attention') && text(byTest('plate')).includes('Not enough'), 'plate shown');
  assert(q('[data-tab="printer"] .oui-appbar-attention'), 'attention dot on the tab');
  await click(btn('Check again'));
  eq(lastOf('plate_recheck').type, 'plate_recheck', 'recheck');
  await tab('spools');
  assert(text(card(1) || q('[data-stack]')).length, 'list');
  await tab('printer');
  await click(btn('Dismiss', byTest('plate')));
  assert(!byTest('plate') && lastOf('plate_dismiss'), 'dismissed');
`);

// ------------------------------------------------------------------ stats (test_detail_export / test_stats)
test('weekly use is split by filament, each part named', `
  await spools(SPOOLS, {usage: {enabled: true, mode: 'ask', prints: []}, stats: {on: true, cur: 'spoolman'}});
  await tab('stats');
  await until(() => lastOf('stats'), 'stats asked');
  const now = Date.now() / 1000;
  await post({type: 'stats', stats: {period: lastOf('stats').period, since: now - 86400 * 30, code: 'GBP', sign: '£', grams: 40, prints: 1, cost: 1, low: 0, mats: [], top: [], soon: [],
    weeks: [{start: now - 86400, now: true, parts: [{g: 30, colour: 'ff0000', label: 'PLA Red'}, {g: 10, colour: '0000ff', label: 'PETG Blue'}]}],
    failed: {prints: 0, g: 0, cost: 0}, history: []}});
  const parts = qa('.stv-bar > i');
  eq(parts.map(i => i.getAttribute('title')), ['PLA Red: 30 g', 'PETG Blue: 10 g'], 'one part per filament');
  eq(parts.map(i => getComputedStyle(i).backgroundColor), ['rgb(255, 0, 0)', 'rgb(0, 0, 255)'], 'in the filament colours');
  assert(q('.stv-weeks').getAttribute('aria-label').includes('PETG Blue: 10 g'), 'read out too');
`);
test('stats tiles, shelf, waste, failed marker, history and export', `
  await spools(SPOOLS, {usage: {enabled: true, mode: 'ask', prints: []}, stats: {on: true, cur: 'spoolman'}});
  await tab('stats');
  await until(() => lastOf('stats'), 'stats asked');
  const d = {period: lastOf('stats').period, since: 1700000000, code: 'GBP', sign: '£', grams: 10, prints: 1, cost: 0.5, low: 0, mats: [{name: 'PLA', g: 10}], top: [], weeks: [], soon: [],
    waste: {model: 8, support: 1, purge: 1, mcost: .4, scost: .05, pcost: .05, cost: .1, prints: 1}, worst: [{kind: 'purge', name: 'x', g: 1, cost: .05}],
    failed: {prints: 1, g: 10, cost: 0.5}, shelf: {g: 850, value: 20, unpriced: 1, mats: [{name: 'PLA', g: 600, value: 10}]},
    history: [{time: 1700000000, name: 'x', printer: 'P', result: 'cancelled', pct: 40, rows: [{spool: 1, grams: 10, label: 'a', material: 'PLA', colour: 'ff0000', cost: 0.5}]}]};
  await post({type: 'stats', stats: d});
  const s = text(q('.stv'));
  for (const k of ['On the shelf', 'Lost to failed prints', 'Wasted filament', 'Usage ratios', 'Most wasteful prints', '1 without a price', 'On the shelf by material'])
    assert(s.includes(k), 'stats has ' + k);
  if (q('.stv-hh').getAttribute('aria-expanded') !== 'true') await click(q('.stv-hh'));
  assert(text(byTest('history')).includes('lost 10.0 g') && qa('th').some(th => text(th) === 'Waste'), 'failed marker and waste column');
  await click(byTest('export'));
  eq(lastOf('stats_export').period, d.period, 'export asked');
  await post({type: 'stats_export', ok: true, text: 'Saved to ~/x.csv'});
  assert(text(byTest('history')).includes('Saved to ~/x.csv'), 'result shown');
`);

// ------------------------------------------------------------------ settings and wizard (test_wizard, test_display, test_drying)
test('calibrated values from a saved copy wait for Save or Skip', `
  const ASK = {name: 'Acme PLA Black @U1', changes: [{key: 'filament_flow_ratio', old: '0.98', new: '0.95'}, {key: 'filament_ironing_flow', old: '', new: '15%'},
    {key: 'filament_max_volumetric_speed', old: '18', new: '21.5', unit: 'mm³/s'}]};
  await spools(SPOOLS, {calibration: [ASK]});
  const box = () => byTest('calibration');
  await until(box, 'prompt shown');
  assert(text(q('.sa [role=status]')).includes('calibrated values to review'), 'announced politely');
  assert(text(box()).includes('Acme PLA Black @U1') && text(box()).includes('Nothing is written to Spoolman until you save'), 'names the filament: ' + text(box()));
  eq(qa('[data-test=calibration] tbody tr').map(r => vis(r)), ['Flow ratio 0.98 0.95', 'Ironing flow — 15%', 'Max volumetric speed 18 mm³/s 21.5 mm³/s'], 'each setting: old and new');
  eq(sentOf('calibration_save').length + sentOf('calibration_skip').length, 0, 'nothing sent before an answer');
  await click(byTest('cal-skip'));
  eq(lastOf('calibration_skip'), {type: 'calibration_skip', name: 'Acme PLA Black @U1'}, 'skip names the change set');
  assert(!box(), 'skipped: gone');
  await post({type: 'calibration', asks: [ASK]});
  await click(byTest('cal-save'));
  eq(lastOf('calibration_save'), {type: 'calibration_save', name: 'Acme PLA Black @U1'}, 'save names the change set');
  assert(text(q('.sa [role=status]')).includes('Saving calibrated values'), 'saving announced');
  assert(byTest('cal-save').disabled, 'no second save while one runs');
  await post({type: 'sent', ok: true, text: 'Sent filament_flow_ratio to Spoolman.'});
  await post({type: 'calibration', asks: []});
  assert(!box() && text(q('.sa [role=status]')).includes('Sent filament_flow_ratio'), 'saved: gone, result shown');
  await spools(SPOOLS);
  assert(!box(), 'a list without asks shows none');
`);
test('calibrated values: plate and ironing labels, units, notes kept whole', `
  await spools(SPOOLS, {calibration: [{name: 'Acme PLA', changes: [
    {key: 'filament_ironing_speed', old: '30', new: '25', unit: 'mm/s'}, {key: 'filament_notes', old: '', new: 'dry 4 h, 65C'},
    {key: 'hot_plate_temp_initial_layer', old: '60', new: '65', unit: '°C'}, {key: 'fan_max_speed', old: '80', new: '100', unit: '%'}]}]});
  await until(() => byTest('calibration'), 'prompt shown');
  eq(qa('[data-test=calibration] tbody tr').map(r => vis(r)), ['Ironing speed 30 mm/s 25 mm/s', 'Filament notes — dry 4 h, 65C',
    'Bed temperature, High Temp Plate, first layer 60 °C 65 °C', 'Maximum fan speed 80 % 100 %'], 'labels, units, notes whole');
`);
test('calibrated values follow the page language', `
  await spools(SPOOLS, {calibration: [{name: 'Acme PLA', changes: [{key: 'filament_flow_ratio', old: '0.98', new: '0.95,0.97'}, {key: 'nozzle_temperature', old: '215', new: '220'}]}]});
  await until(() => byTest('calibration'), 'prompt shown');
  eq(qa('[data-test=calibration] tbody tr').map(r => vis(r)), ['Flussrate 0,98 0,95 / 0,97', 'Düsentemperatur 215 220'], 'German labels and decimals');
`, { lang: 'de' });
test('settings: one switch per Display option, drying table, save waits for a passing test', `
  await until(() => byTest('settings-btn'));
  await click(byTest('settings-btn'));
  eq(lastOf('settings').type, 'settings', 'asked the plugin');
  await post({type: 'show_view', view: 'settings', url: 'http://spoolman:7912', source: 'spoolman', low_stock: 100, plate_check: true, plate_margin: 10,
    weight_display: 'both', show_cart: false, spool_columns: 1, display: DEFAULTS, drying: {HIPS: 9}, progress: {on: true}, stats: {on: true, cur: 'spoolman'}, cur_code: 'GBP', wizard: false});
  eq(qa('[data-disp]').map(e => e.dataset.disp).sort(), Object.keys(DEFAULTS).sort(), 'one checkbox per Display option');
  assert(q('#dry-HIPS') && q('#dry-HIPS').value === '9 days', 'drying reseeded from show_view: ' + (q('#dry-HIPS') || {}).value);
  assert(byTest('save').disabled && text(q('#save-why')).includes('passing Test'), 'save waits, with the reason');
  await click(byTest('test'));
  eq(lastOf('test'), {type: 'test', source: 'spoolman', url: 'http://spoolman:7912', view: 'settings'}, 'test tagged for the Settings view');
  await post({type: 'test_result', source: 'spoolman', ok: true, url: 'http://spoolman:7912', version: '0.22', view: 'settings'});
  assert(text(byTest('conn-status')).includes('Spoolman v0.22') && !byTest('save').disabled, 'tested: save on');
  await type(q('[aria-label="Material to add"]'), ' nylon  cf');
  await press('Enter');
  assert(q('#dry-NYLON\\\\ CF'), 'material normalised');
  await click(q('#d-diameter'));
  assert(!q('#auto-keep').checked, 'automatic Keep Slots Synced is off by default');
  await click(q('#auto-keep'));
  assert(q('#cal-ask').checked, 'calibrated values: ask first by default');
  await click(q('#cal-auto'));
  await click(byTest('save'));
  const s = lastOf('save');
  eq([s.view, s.display.diameter, s.drying['NYLON CF'], s.drying.HIPS, s.url, s.auto_keep_slots, s.save_calibration],
    ['settings', true, 0, 9, 'http://spoolman:7912', true, 'auto'], 'saved');
`);
test('settings: leaving with unsaved edits asks; going back keeps them', `
  await post({type: 'show_view', view: 'settings', url: 'http://s:7912', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {}});
  await click(q('#show-cart'));
  assert(document.body.textContent.includes('Unsaved changes'), 'marked');
  await click(byTest('cancel'));
  assert(dialogText().includes('aren’t saved'), 'asks');
  await no();
  assert(q('#show-cart').checked && !lastOf('cancel'), 'kept');
  await click(byTest('cancel')); await yes();
  eq(lastOf('cancel').view, 'settings', 'cancel sent');
`);
test('wizard: open, next, blocked until tested, back, skip posts done once', `
  await until(() => byTest('open-guide'));
  await click(byTest('open-guide'));
  await until(dialogOpen, 'guide open');
  assert(text(byTest('wiz-count')).includes('Step 1 of 6'), 'step 1');
  await click(byTest('wiz-next'));
  assert(text(byTest('wiz-count')).includes('Step 2 of 6') && byTest('wiz-next').disabled, 'blocked until tested');
  assert(q('.p-dialog #url'), 'the real source controls are in the guide');
  await post({type: 'test_result', source: 'spoolman', ok: true, url: 'http://spoolman:7912', version: '0.9'});
  assert(!byTest('wiz-next').disabled, 'unlocked');
  await click(byTest('wiz-next'));
  assert(text(byTest('wiz-count')).includes('Step 3'), 'step 3');
  await click(byTest('wiz-back'));
  assert(text(byTest('wiz-count')).includes('Step 2'), 'back');
  await click(byTest('wiz-skip'));
  await until(() => !dialogOpen(), 'closed');
  eq(sentOf('wizard').length, 1, 'done posted once');
  await until(() => document.activeElement === byTest('open-guide'), 'focus back on the opener');
`, { mode: 'settings' });
test('wizard: back stops at the first step; opens by itself; finish saves and marks done', `
  await until(dialogOpen, 'opened by itself');
  await click(byTest('wiz-back'));
  assert(text(byTest('wiz-count')).includes('Step 1'), 'stays at step 1');
  await click(byTest('wiz-next'));
  await post({type: 'test_result', source: 'spoolman', ok: true, url: 'http://spoolman:7912', version: '0.9'});
  for (let i = 0; i < 4; i++) await click(byTest('wiz-next'));
  eq(text(byTest('wiz-next')), 'Save & finish', 'last step');
  await click(byTest('wiz-next'));
  await until(() => !dialogOpen());
  eq([sentOf('wizard').length, !!lastOf('save')], [1, true], 'saved and done');
`, { mode: 'settings', wizard: true });
test('low-stock preview lists the spools under the typed weight', `
  await spools([{...SPOOLS[0], remaining_weight: 50}, SPOOLS[1]]);
  await post({type: 'show_view', view: 'settings', url: 'x', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {}});
  assert(text(q('#s-reorder').closest('section')).includes('1 spool is under 100 g'), 'preview');
`);

// ------------------------------------------------------------------ language, theme, layout
test('X04: pt-BR from the host: tabs, empty states, weights and dialogs in Portuguese', `
  await spools(SPOOLS);
  eq(document.documentElement.lang, 'pt-BR', 'lang');
  assert(text(q('[data-tab="spools"]')).startsWith('Bobinas'), 'nav');
  assert(text(q('[data-stack]')).includes('1.380 g de 2.000 g'), 'weights in pt-BR: ' + text(q('[data-stack]')));
  await post({type: 'spools', ok: false, error: 'x', error_code: 'no_url'});
  assert(text(byTest('empty-no-url')).includes('O Spoolman ainda não foi configurado'), 'empty state');
`, { lang: 'pt_BR' });
for (const [host, lang, nav, weights, empty] of [
  ['es', 'es', 'Carretes', '1380 g de 2000 g', 'Spoolman aún no está configurado'],
  ['de', 'de', 'Spulen', '1.380 g von 2.000 g', 'Spoolman ist noch nicht eingerichtet'],
  ['zh_CN', 'zh-CN', '料盘', '1,380 g / 2,000 g', 'Spoolman 尚未设置'],
  ['zh_TW', 'zh-CN', '料盘', '1,380 g / 2,000 g', 'Spoolman 尚未设置'],
  ['fr_FR', 'en', 'Spools', '1,380 g of 2,000 g', 'Spoolman isn’t set up yet']]) {
  test(`X04: ${host} from the host: page in ${lang}`, `
  await spools(SPOOLS);
  eq(document.documentElement.lang, ${JSON.stringify(lang)}, 'lang');
  assert(text(q('[data-tab="spools"]')).startsWith(${JSON.stringify(nav)}), 'nav: ' + text(q('[data-tab="spools"]')));
  assert(text(q('[data-stack]')).includes(${JSON.stringify(weights)}), 'weights: ' + text(q('[data-stack]')));
  await post({type: 'spools', ok: false, error: 'x', error_code: 'no_url'});
  assert(text(byTest('empty-no-url')).includes(${JSON.stringify(empty)}), 'empty state: ' + text(byTest('empty-no-url')));
`, { lang: host });
}
test('X04: Español, Deutsch and 简体中文 can be chosen over the host', `
  await until(() => q('[data-tab="spools"]'));
  await click(byTest('settings-btn'));
  await post({type: 'show_view', view: 'settings', url: '', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {}});
  await pick(byTest('lang'), 'Deutsch');
  eq(lastOf('ui_language'), {type: 'ui_language', value: 'de', view: 'settings'}, 'saved through the plugin');
  assert(text(q('#s-lang .oui-panel-title')) === 'Sprache', 'switched to German');
  await pick(byTest('lang'), '简体中文');
  assert(text(q('#s-lang .oui-panel-title')) === '语言', 'switched to Chinese');
  eq(document.documentElement.lang, 'zh-CN', 'lang');
  await pick(byTest('lang'), 'Español');
  assert(text(q('#s-lang .oui-panel-title')) === 'Idioma', 'switched to Spanish');
  eq(lastOf('ui_language'), {type: 'ui_language', value: 'es', view: 'settings'}, 'last choice saved');
`, { lang: 'en' });
test('X04: the saved explicit language wins over the host', `
  await until(() => q('[data-tab="spools"]'));
  assert(text(q('[data-tab="spools"]')).startsWith('Spools'), 'English kept');
  await click(byTest('settings-btn'));
  await post({type: 'show_view', view: 'settings', url: '', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {}});
  await pick(byTest('lang'), 'Português (Brasil)');
  eq(lastOf('ui_language'), {type: 'ui_language', value: 'pt-BR', view: 'settings'}, 'saved through the plugin');
  assert(text(q('#s-lang .oui-panel-title')) === 'Idioma', 'switched');
`, { lang: 'pt_BR', pref: 'en' });
test('B-21/B-24: focus ring on group heads is visible; reduced motion honoured', `
  await spools(SPOOLS);
  const head = q('[data-stack] .st-head');
  head.focus(); await press('Tab', true); await press('Tab');
  const cs = getComputedStyle(document.activeElement);
  assert(document.activeElement === head && cs.outlineStyle !== 'none' && parseFloat(cs.outlineWidth) >= 2, 'visible 2px ring: ' + cs.outlineStyle + ' ' + cs.outlineWidth);
`);

// ------------------------------------------------------------------ spool editor (Add Spool, Edit Spool)
test('editor: add a spool of an existing filament, with typed extra fields and a live preview', `
  await spools(SPOOLS);
  await click(byTest('add-spool'));
  eq(lastOf('spool_action'), {type: 'spool_action', action: 'editor', origin: 3, ref: 1}, 'the editor asks the plugin for Spoolman\\'s fields');
  assert(dialogOpen() && text(dialogEl()).includes('Loading'), 'loading until the answer');
  await loaded();
  assert(text(dialogEl()).includes('Step 1 of 2'), 'guided: step 1');
  await click(byTest('editor-next'));
  assert(text(dialogEl()).includes('Choose a filament') && byTest('editor-pick'), 'a filament is needed first');
  await pick(byTest('editor-pick'), 'Acme · Black · PLA');
  eq(text(byTest('preview-name')), 'Black', 'the preview shows the filament');
  await click(byTest('editor-next'));
  assert(text(dialogEl()).includes('Step 2 of 2') && !byTest('editor-filament'), 'step 2: the spool');
  await type(q('#se-left'), '750');
  assert(text(byTest('preview-weight')).includes('750 g of 1,000 g'), 'preview weight: ' + text(byTest('preview-weight')));
  await type(q('#se-loc'), 'Shelf C');
  assert(q('#se-sx-dryer') && q('#se-sx-sealed') && !q('#se-sx-dried'), 'the user\\'s fields with their inputs; Spooler\\'s own stay out');
  await click(q('#se-sx-sealed'));
  await type(q('#se-sx-dryer'), 'Box 3');
  await click(byTest('editor-save'));
  eq(lastOf('spool_action'), {type: 'spool_action', origin: 3, action: 'create', filament_id: 5,
    spool: {remaining_weight: 750, location: 'Shelf C', archived: false, extra: {dryer: 'Box 3', sealed: true}}, ref: 1}, 'create: only filled fields');
  await post({type: 'action_result', action: 'create', ok: true, text: 'Added spool #44.', ref: editorRef()});
  await until(() => !dialogOpen(), 'the editor closes');
  assert(text(document.body).includes('Added spool #44.'), 'the result is shown');
`);
test('editor: a new filament in German, decimals typed with a point, two colours and a choice field', `
  await spools(SPOOLS);
  await click(byTest('add-spool'));
  await loaded();
  await click(btn('Neues Filament'));
  assert(byTest('editor-filament'), 'new filament fields');
  await type(q('#se-vendor'), 'Polymaker');
  await type(q('#se-name'), 'Galaxy');
  await type(q('#se-mat'), 'PETG');
  eq(q('#se-den').value, '1,27 g/cm³', 'the material\\'s usual density');
  await type(q('#se-dia'), '2.85');
  eq(q('#se-dia').value, '2,85 mm', 'a typed point is the decimal');
  const first = q('.se-col input[type=color]');
  first.value = '#ff0000'; first.dispatchEvent(new Event('input', {bubbles: true})); await settle();
  await click(byTest('editor-add-colour'));
  eq(qa('.se-col input[type=color]').length, 2, 'two colours');
  assert(q('#se-dir'), 'their direction');
  await pick(q('#se-fx-grade').closest('.p-select'), 'B');
  await type(q('#se-fx-shrink'), '0.4');
  eq(q('#se-fx-shrink').value, '0,4 %', 'unit and decimal');
  assert(!q('#se-fx-orca_settings'), 'Spooler\\'s own filament field stays out');
  eq(text(byTest('preview-name')), 'Galaxy', 'live preview');
  await click(byTest('editor-next'));
  await type(q('#se-initial'), '1000');
  await type(q('#se-left'), '1200');
  assert(text(dialogEl()).includes('Mehr als das Anfangsgewicht'), 'more left than at the start is refused');
  await click(byTest('editor-save'));
  assert(!sentOf('spool_action').some(m => m.action === 'create'), 'nothing sent while invalid');
  await type(q('#se-left'), '1000');
  await click(byTest('editor-save'));
  eq(lastOf('spool_action'), {type: 'spool_action', origin: 3, action: 'create', spool: {initial_weight: 1000, remaining_weight: 1000, archived: false},
    filament: {vendor: 'Polymaker', name: 'Galaxy', material: 'PETG', multi_color_hexes: 'FF0000,FF0000', multi_color_direction: 'coaxial', diameter: 2.85, density: 1.27,
      extra: {grade: 'B', shrink: 0.4}}, ref: 1}, 'create with a new filament');
  await post({type: 'action_result', action: 'create', ok: false, text: 'Filament #21 angelegt, aber Spoolman hat die Spule abgelehnt', filament: 21, ref: 1});
  assert(dialogOpen() && text(byTest('editor-error')).includes('#21'), 'the refusal stays visible');
  await click(byTest('editor-save'));
  const retry = lastOf('spool_action');
  eq([retry.action, retry.filament_id, 'filament' in retry], ['create', 21, false], 'the retry uses the filament made, not a second one');
`, { lang: 'de' });
test('editor: edit sends only changes, says the filament is shared, and keeps a refusal visible', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await open(1);
  assert(byTest('detail-edit'), 'a pencil beside the name in the detail');
  await click(q('[data-edit="1"]'));
  eq(lastOf('spool_action'), {type: 'spool_action', action: 'editor', id: 1, origin: 3, ref: 1}, 'the editor reads the spool again');
  await post(editorData({...RAW1, id: 2}, editorRef() - 1));
  assert(!q('#se-loc'), 'an answer for an editor opened before is ignored');
  await loaded(RAW1);
  assert(text(byTest('editor-shared')).includes('1 other spool'), 'shared filament note: ' + text(byTest('editor-shared')));
  eq(q('#se-loc').value, 'Shelf A', 'the form opens with Spoolman\\'s values');
  eq(q('#se-sx-dryer').value, 'Box 1', 'extra text decoded');
  await type(q('#se-loc'), 'Dry box');
  await type(q('#se-noz'), '215');
  await click(byTest('editor-save'));
  eq(lastOf('spool_action'), {type: 'spool_action', origin: 3, id: 1, action: 'save', spool: {location: 'Dry box'}, filament: {settings_extruder_temp: 215},
    was: {spool: {location: 'Shelf A'}, filament: {settings_extruder_temp: null, id: 5}}, ref: 1}, 'only what changed, with what Spoolman held');
  await post({type: 'action_result', action: 'save', ok: false, text: 'Spoolman refused it (HTTP 422): density', ref: editorRef()});
  assert(dialogOpen() && text(byTest('editor-error')).includes('HTTP 422'), 'the refusal stays visible in the editor');
  await click(byTest('editor-cancel'));
  await until(() => !dialogOpen(), 'closed');
  await click(q('[data-edit="1"]'));
  await loaded(RAW1);
  const before = sentOf('spool_action').length;
  q('#se-left').focus(); await settle(); q('#se-left').blur(); await settle();
  await click(byTest('editor-save'));
  eq(sentOf('spool_action').length, before, 'no change (734.5678 g shown as 734.6 and left) : nothing sent');
  await until(() => !dialogOpen(), 'closed');
  assert(text(document.body).includes('Nothing changed'), 'and it says so');
`);
test('editor: a new location for a spool linked to a U1 toolhead asks first', `
  const bound = {...SPOOLS[0], id: 3, location: 'Snapmaker U1 T0', u1_bound: true};
  await spools([...SPOOLS, bound], {display: {...DEFAULTS, group_same: false}});
  await click(q('[data-edit="3"]'));
  await loaded({...bound, filament: FILS[0]});
  await type(q('#se-loc'), 'Shelf C');
  await click(byTest('editor-save'));
  await until(() => q('[data-dlg="cancel"]'), 'unlink confirmation');
  await click(q('[data-dlg="cancel"]'));
  await until(() => !q('[data-dlg="cancel"]'), 'confirmation closed');
  assert(!sentOf('spool_action').some(m => m.action === 'save'), 'going back sends nothing');
  await click(byTest('editor-save'));
  await until(() => q('[data-dlg="confirm"]'), 'asked again');
  await click(q('[data-dlg="confirm"]'));
  await until(() => sentOf('spool_action').some(m => m.action === 'save'), 'sent after yes');
  eq(lastOf('spool_action').spool, {location: 'Shelf C'}, 'the new location');
`);
test('editor: pt-BR wording and the empty list offers Add Spool', `
  await spools([]);
  await click(btn('Adicionar bobina'));
  await loaded();
  assert(text(dialogEl()).includes('Etapa 1 de 2') && text(dialogEl()).includes('Filamento existente'), 'Portuguese: ' + text(dialogEl()).slice(0, 80));
`, { lang: 'pt_BR' });

// ------------------------------------------------------------------ new RFID spools (Printer tab)
const RFID_PRELUDE = `
  const TAG = '7A1F3B9C2D4E4F60A1B2C3D4E5F60718';
  const OFFER = {tag: TAG, printer: 'p1', unit: 0, slot: 2, type: 'PLA', name: 'PLA Matte', colours: ['3C3C3C'], remain: 80, weight: 1000, diameter: 1.75, nozzle: [190, 230]};
  const X1 = {id: 'p1', link: 'p1', name: 'X1C', age: 0, units: [{id: 0, kind: 'ams', trays: [0, 1, 2, 3].map(i => ({slot: i, empty: i !== 2, type: i === 2 ? 'PLA' : '', name: 'PLA Matte', colour: '3C3C3C', remain: 80, rfid: i === 2}))}], ext: null};
  const MATTE = {id: 12, name: 'PLA Matte Charcoal', material: 'PLA', color_hex: '3C3C3C', density: 1.31, diameter: 1.75, weight: 1000, vendor: {id: 6, name: 'Bambu Lab'}};
  async function offered(rfid) {
    await spools(SPOOLS, {printers: [{id: 'p1', name: 'X1C', ip: '10.0.0.9', has_code: true, units: []}], live_ok: true});
    await tab('printer');
    assert(byTest('rfid-live') && !byTest('rfid'), 'the live region is there before any offer');
    await post({type: 'live', live: {links: {p1: 'live'}, printers: [X1]}, rfid: rfid || [OFFER]});
    await until(() => byTest('rfid'), 'the offer');
  }
  async function editorWith(filaments) {
    await post({...editorData(), editor: {...editorData().editor, filaments}});
    await until(() => dialogEl() && !/enter|leave/.test(dialogEl().className) && dialogEl().contains(document.activeElement), 'editor open and focused');
  }
`;
test('rfid: a new RFID spool is offered; Add opens the editor on the matching filament and sends the tag', RFID_PRELUDE + `
  await offered();
  eq(text(byTest('rfid-live')), 'New RFID spool', 'announced by a live region that was there before the offer');
  const o = byTest('rfid-offer');
  for (const s of ['New RFID spool in X1C · AMS 1 slot 3', 'Bambu Lab PLA Matte', '~80% left, about 800 g'])
    assert(text(o).includes(s), 'offer says ' + s + ': ' + text(o));
  await click(byTest('rfid-add'));
  eq(lastOf('spool_action'), {type: 'spool_action', action: 'editor', origin: 3, ref: 1}, 'Add Spool, as from the list');
  await editorWith([...FILS, MATTE]);
  assert(text(byTest('editor-rfid')).includes('RFID spool in X1C · AMS 1 slot 3'), 'the editor says where the spool is');
  eq(text(byTest('preview-name')), 'PLA Matte Charcoal', 'the matching Bambu Lab filament is picked');
  await click(byTest('editor-next'));
  assert(text(byTest('preview-weight')).includes('800 g of 1,000 g'), 'weights from the tray: ' + text(byTest('preview-weight')));
  await click(byTest('editor-save'));
  eq(lastOf('spool_action'), {type: 'spool_action', origin: 3, action: 'create', filament_id: 12,
    spool: {initial_weight: 1000, remaining_weight: 800, archived: false}, tag: TAG, ref: 1}, 'create with the tag');
  await post({type: 'action_result', action: 'create', ok: true, text: 'Added spool #44.', ref: editorRef()});
  await until(() => !dialogOpen(), 'the editor closes');
  await post({type: 'live', live: {links: {p1: 'live'}, printers: [X1]}, rfid: []});
  assert(!byTest('rfid'), 'known from now on: no offer');
`);
test('rfid: with no matching filament, Add fills in a new Bambu Lab filament from the tray', RFID_PRELUDE + `
  await offered([{...OFFER, colours: ['FF0000', '00FF00'], nozzle: [200, 230]}]);
  assert(text(byTest('rfid-offer')).includes('Bambu Lab PLA Matte'), 'offer');
  await click(byTest('rfid-add'));
  await editorWith(FILS);
  assert(byTest('editor-filament'), 'a new filament');
  eq([q('#se-vendor').value, q('#se-name').value, q('#se-mat').value, q('#se-col-0').value, q('#se-col-1').value],
    ['Bambu Lab', 'PLA Matte', 'PLA', '#ff0000', '#00ff00'], 'vendor, name, material and both colours');
  await click(byTest('editor-next'));
  await click(byTest('editor-save'));
  const made = lastOf('spool_action');
  eq([made.action, made.tag, made.filament.vendor, made.filament.multi_color_hexes, made.filament.density, made.filament.diameter, made.filament.settings_extruder_temp, made.filament.weight],
    ['create', TAG, 'Bambu Lab', 'FF0000,00FF00', 1.24, 1.75, 215, 1000], 'the new filament as the tray reports it');
  eq(made.spool, {initial_weight: 1000, remaining_weight: 800, archived: false}, 'the spool weights');
`);
test('rfid: Skip remembers the spool for that printer; Settings asks again', RFID_PRELUDE + `
  await offered();
  await click(byTest('rfid-skip'));
  eq(lastOf('rfid_skip'), {type: 'rfid_skip', printer: 'p1', tag: TAG}, 'skip names the printer and the tag');
  assert(!byTest('rfid'), 'the offer goes');
  await click(byTest('settings-btn'));
  await post({type: 'show_view', view: 'settings', url: 'http://spoolman:7912', source: 'spoolman', low_stock: 100, plate_check: true, plate_margin: 10,
    weight_display: 'both', show_cart: false, spool_columns: 1, display: DEFAULTS, drying: {}, progress: {on: true}, stats: {on: true, cur: 'spoolman'}, cur_code: 'GBP',
    wizard: false, rfid_skipped: 1});
  await until(() => byTest('rfid-skipped'), 'the skipped row');
  eq(text(byTest('rfid-skipped')), '1 spool skipped', 'the count');
  await click(byTest('rfid-unskip'));
  eq(lastOf('rfid_unskip'), {type: 'rfid_unskip', view: 'settings'}, 'ask again');
  eq(text(byTest('rfid-skipped')), 'None', 'none skipped now');
`);
test('rfid: pt-BR wording', RFID_PRELUDE + `
  await offered();
  assert(text(byTest('rfid')).includes('Nova bobina RFID em X1C') && btn('Adicionar') && btn('Ignorar'), 'Portuguese: ' + text(byTest('rfid')));
`, { lang: 'pt_BR' });
// ------------------------------------------------------------------ presets per spool, Use with and Advanced tuning
const PRINTERS = "[{target: 'Snapmaker U1 (0.4 nozzle)', label: 'Snapmaker U1'}, {target: 'Sovol SV06 0.4 nozzle', label: 'Sovol SV06'}]";
test('editor: Use with picks the printers of a spool preset, and sends only a change', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await click(q('[data-edit="1"]'));
  await post({...editorData(RAW1), editor: {...editorData(RAW1).editor, use_with: {on: true, printers: ${PRINTERS}, value: null}}});
  await until(() => byTest('editor-usewith'), 'Use with shows while presets are per spool');
  assert(text(q('#se-usewith').closest('.oui-formrow') || q('#se-usewith').parentElement.parentElement).includes('Automatic'), 'empty means automatic');
  await click(byTest('editor-usewith'));
  await until(() => q('.p-multiselect-overlay') && !q('.p-multiselect-overlay[class*="enter-active"]'), 'printer list open');
  const opt = qa('.p-multiselect-overlay [role=option]').find(o => text(o) === 'Sovol SV06');
  assert(opt, 'the printers are offered by name');
  await mouse(opt); await settle();
  await press('Escape'); await until(() => !q('.p-multiselect-overlay'), 'list closed');
  await click(byTest('editor-save'));
  eq(lastOf('spool_action').spool, {use_with: ['Sovol SV06 0.4 nozzle']}, 'the printer preset picked');
  eq(lastOf('spool_action').was.spool, {use_with: null}, 'with what Spoolman held');
  await post({type: 'action_result', action: 'save', ok: true, text: 'Saved spool #1.', ref: editorRef()});
  await until(() => !dialogOpen(), 'closed');
  await click(q('[data-edit="1"]'));
  await post({...editorData(RAW1), editor: {...editorData(RAW1).editor, use_with: {on: false, printers: ${PRINTERS}, value: null}}});
  await until(() => q('#se-loc'), 'editor open');
  assert(!byTest('editor-usewith'), 'hidden while presets are per filament and the spool has none');
`);
test('settings: presets per spool and Advanced tuning, off by default, saved with decimals typed with a point', `
  await post({type: 'show_view', view: 'settings', url: 'http://spoolman:7912', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {},
    presets: {per_spool: false, tuning: false, materials: {}}, parents: [{name: 'Generic PLA', type: 'PLA'}, {name: 'Generic PLA Silk', type: 'PLA'}, {name: 'Generic PETG', type: 'PETG'}]});
  await until(() => byTest('preset-mode-filament'), 'Presets section');
  assert(q('#pm-filament').checked && !q('#pm-spool').checked, 'one per filament by default');
  assert(!byTest('preset-unsaved'), 'nothing to say while the mode stays');
  assert(!q('#tune-on').checked && !byTest('tune-mat'), 'Advanced tuning off by default, its fields hidden');
  await click(q('#pm-spool'));
  await until(() => byTest('preset-unsaved'), 'switching: the rename note');
  assert(text(byTest('preset-unsaved')).includes('ungespeicherte'), 'says unsaved preset edits hold the reload');
  assert(text(byTest('preset-mode-help')).includes('#12'), 'per-spool names explained: ' + text(byTest('preset-mode-help')));
  await click(q('#tune-on'));
  await until(() => byTest('tune-base'), 'tuning fields');
  await pick(byTest('tune-base'), 'Generic PLA Silk');
  assert(!qa('.p-select-overlay [role=option]').length, 'closed');
  await type(q('#tune-filament_flow_ratio'), '0.95');
  await type(q('#tune-pressure_advance'), '0.035');
  await type(q('#tune-fan_max_speed'), '80');
  q('#tune-fan_max_speed').blur(); await settle();
  await post({type: 'test_result', source: 'spoolman', ok: true, url: 'http://spoolman:7912', version: '0.26', view: 'settings'});
  await click(byTest('save'));
  eq(lastOf('save').presets, {per_spool: true, tuning: true, materials: {PLA: {parent: 'Generic PLA Silk', filament_flow_ratio: 0.95,
    pressure_advance: 0.035, fan_max_speed: 80}}}, 'saved');
`, { lang: 'de' });

// ------------------------------------------------------------------ runner
async function bounded(work, stage, ms = 30000) {
  let timer;
  try {
    return await Promise.race([work, new Promise((_, reject) => {
      timer = setTimeout(() => reject(Object.assign(new Error(`Page runner stalled: ${stage} (${ms}ms)`), { code: 'PAGE_TIMEOUT' })), ms);
    })]);
  } finally { clearTimeout(timer); }
}

const workers = Number(process.env.WORKERS ?? 4);
if (!Number.isSafeInteger(workers) || workers < 1) throw new Error('WORKERS must be a positive integer');
const filter = process.argv[2];
const chosen = scenarios.filter(s => !filter || s.name.includes(filter));
const page = await readFile(PAGE, 'utf8');
const dir = await mkdtemp(join(tmpdir(), 'spooler-page-'));
const browser = await launch();
let failed = 0;
const results = [];
try {
  await Promise.all(Array.from({ length: Math.min(workers, chosen.length) }, async (_, worker) => {
    for (let k = worker; k < chosen.length; k += workers) {
      const sc = chosen[k];
      console.log(`START ${sc.name}`);
      const mode = sc.mode || 'tab';
      const boot = { mode, view: mode === 'settings' ? 'settings' : 'main', version: 'test', lang: sc.lang ?? 'en', pref: sc.pref ?? 'auto',
        low_stock_default: 100, refresh_ms: 600000, display_defaults: DISPLAY_DEFAULTS, own_fields: ['tag', 'orca_settings', 'dried', 'orca_flow_ratio'],
        settings: { ...SETTINGS, wizard: !!sc.wizard } };
      const file = join(dir, `p${k}.html`);
      await writeFile(file, preparePage(page, boot));
      const p = await bounded(browser.newPage(), 'open page / initialize DevTools');
      const started = Date.now();
      try {
        await bounded(p.size(sc.width ?? 1280, 900), 'set viewport');
        await bounded(p.init(MOCK_HOST + 'try { localStorage.clear(); } catch {}'), 'install mock host');
        await bounded(p.goto(pathToFileURL(file).href), 'navigate / load event');
        const body = `(async () => { ${HELPERS} ${PRELUDE}
          await until(() => document.querySelector('#app > *'), 'app mounted');
          ${sc.body}
          await settle();
          return { violations: __t.violations, rejections: __t.rejections, errors: __t.errors };
        })()`;
        const probe = await bounded(p.evaluate(body), `evaluate ${sc.name}`);
        if (probe.violations.length || probe.rejections.length || probe.errors.length) throw new Error('page problems: ' + JSON.stringify(probe));
        results.push({ name: sc.name, ok: true, ms: Date.now() - started });
        console.log(`ok   ${sc.name}`);
      } catch (e) {
        failed++;
        results.push({ name: sc.name, ok: false, error: String(e.message || e) });
        console.log(`FAIL ${sc.name}\n     ${String(e.message || e).split('\n')[0]}`);
        if (e.code === 'PAGE_TIMEOUT') {
          try {
            console.log('Page at timeout:', await bounded(p.evaluate(`({ ready: document.readyState, visibility: document.visibilityState,
              focus: document.hasFocus(), mounted: !!document.querySelector('#app > *'),
              messages: window.__t?.sent, errors: window.__t?.errors, rejections: window.__t?.rejections })`), 'timeout diagnostics', 2000));
          } catch (diagnostic) { console.log(String(diagnostic)); }
          throw e;
        }
      } finally {
        await bounded(p.close(), 'close page');
      }
    }
  }));
} finally {
  console.log('Closing page-test browser');
  await browser.close();
  console.log('Page-test browser closed');
  await rm(dir, { recursive: true, force: true, maxRetries: 10, retryDelay: 100 });
}
if (process.env.RESULTS) await writeFile(process.env.RESULTS, JSON.stringify(results, null, 2));
console.log(`${chosen.length - failed}/${chosen.length} page scenarios passed`);
if (failed || !chosen.length) process.exit(1);
console.log('PASS');
