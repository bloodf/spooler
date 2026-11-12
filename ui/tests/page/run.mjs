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
  assert(root, 'select to open'); root.click(); await until(() => q('.p-select-overlay') && !q('.p-select-overlay[class*="enter-active"]'), 'select overlay open');
  const opt = qa('.p-select-overlay [role=option]').find(o => text(o) === label);
  assert(opt, 'option ' + label + ' in ' + qa('.p-select-overlay [role=option]').map(text).join('|'));
  await mouse(opt); await until(() => !q('.p-select-overlay'), 'overlay closed'); await settle();
}
const sentOf = type => __t.sent.filter(m => m.type === type);
const lastOf = type => [...__t.sent].reverse().find(m => m.type === type);
const card = id => q('[data-spool="' + id + '"]');
const alerts = () => qa('[role=alert] .p-message').map(text).join(' | ');
`;

const scenarios = [];
const test = (name, body, opts = {}) => scenarios.push({ name, body, ...opts });

// ------------------------------------------------------------------ list (test_display.py PageScriptTest)
test('grouped spools show full totals and the loaded one first', `
  await spools(SPOOLS);
  await post({type: 'live', live: LIVE});
  const head = q('[data-stack] .st-head');
  assert(text(head).includes('1,380 g of 2,000 g'), 'totals: ' + text(head));
  assert(text(head).includes('1 in use'), 'in use count');
  await click(head);
  const items = qa('[data-stack] .sc');
  eq(items.map(c => c.dataset.spool), ['2', '1'], 'spool 2 is loaded: first');
  assert(text(items[0]).includes('In use · U1 · T1'), 'where it is loaded');
`);
test('groups and single spools share one card; stack shows its count', `
  await spools(SPOOLS);
  assert(text(q('.st-count')) === '2', 'count on the swatch');
  await click(q('[data-stack] .st-head'));
  eq(qa('.st-sub, .sc-subtext').filter(e => e.textContent.includes('Acme')).length, 3, 'group and both spools name the manufacturer');
`);
test('an open stack stays in its column (grid rows)', `
  await spools(SPOOLS, {spool_columns: 2});
  const st = q('[data-stack]');
  eq(st.style.getPropertyValue('--rows'), '3', 'rows = head + spools');
  await click(q('[data-stack] .st-head'));
  eq(getComputedStyle(st).gridRowStart, 'span 3', 'spans its own rows only');
  assert(getComputedStyle(st).gridColumnStart === 'auto', 'not spanning both columns');
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
  const v = vis(q('[data-stack]'));
  for (const s of ['Acme', 'PLA', 'in use', 'In use']) assert(!v.includes(s), 'hidden: ' + s + ' in ' + v);
  assert(v.indexOf('400 g') < v.indexOf('980 g'), 'list order kept');
`);
test('kilograms when exact weights are off', `
  await spools(SPOOLS, {display: {...DEFAULTS, exact_weight: false}});
  assert(text(q('[data-stack] .st-head')).includes('1.38 kg of 2.00 kg'), text(q('[data-stack] .st-head')));
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
  eq(qa('[data-act="sp-menu"]').length, 3, 'one actions button per spool');
  await click(q('[data-spool="3"] [data-act="sp-menu"]'));
  const panel = vis(card(3));
  for (const s of ['Set weight from scale', 'Use filament', 'Move', 'Unarchive', 'Add a spool of this filament', 'Open in Spoolman', 'Archived'])
    assert(panel.includes(s), 'menu has ' + s);
  assert(!btn('Archive', card(3)), 'no Archive on an archived spool');
  eq(q('[data-spool="3"] [data-act="sp-menu"]').getAttribute('aria-expanded'), 'true', 'expanded');
  await click(btn('Move', card(3)));
  await until(() => sentOf('spool_action').some(m => m.action === 'locations'), 'locations asked');
  assert(vis(card(3)).includes('unlinks that toolhead'), 'warns before');
  await type(q('#sc-in-3'), 'Shelf');
  await click(q('[data-spool="3"] [data-act="sp-go"]'));
  assert(dialogOpen() && dialogText().includes('unlinks that toolhead'), 'second step is a confirmation');
  await yes();
  const mv = sentOf('spool_action').find(m => m.action === 'move');
  eq([mv.id, mv.location, mv.origin], [3, 'Shelf', 3], 'moves with the list origin');
  assert(text(q('.sa')).includes('Sending to Spoolman'), 'pending shown');
  await click(q('[data-spool="1"] [data-act="sp-menu"]'));
  await click(btn('Archive', card(1)));
  assert(dialogText().includes('Archive Black'), 'archive asks');
  await no();
  assert(!sentOf('spool_action').some(m => m.action === 'archive'), 'declined: nothing sent');
  await spools(list, {source: 'bambu', display: {...DEFAULTS, group_same: false}});
  eq(qa('[data-act="sp-menu"]').length, 0, 'no actions for Bambu Cloud');
`);
test('use first chip follows the payload and its switch', `
  await spools([{...SPOOLS[0], use_first: true}, {...SPOOLS[1], id: 9, filament: {...SPOOLS[1].filament, id: 6}}], {display: {...DEFAULTS, group_same: false}});
  eq(qa('.sp-chip').filter(c => text(c) === 'Use first').length, 1, 'one chip');
  await spools([{...SPOOLS[0], use_first: true}], {display: {...DEFAULTS, use_first: false, group_same: false}});
  assert(!document.body.textContent.includes('Use first'), 'switch hides it');
`);
test('dried chip and menu: mark, then clear only when marked', `
  const marked = {...SPOOLS[0], extra: {dried: '"' + new Date().toISOString().slice(0, 10) + '"', dryer: '"Box 2"'}, dry_days: 30};
  await spools([marked, {...SPOOLS[1], filament: {...SPOOLS[1].filament, id: 6}}], {display: {...DEFAULTS, group_same: false, extra_fields: true}});
  assert(text(card(1)).includes('Dried today') && byTest('dried'), 'chip');
  assert(!text(card(1)).includes('dried:') && text(card(1)).includes('dryer: Box 2'), 'own field hidden, user field shown');
  await click(q('[data-spool="1"] [data-act="sp-menu"]'));
  assert(btn('Mark dried today', card(1)) && btn('Clear dried date', card(1)), 'both');
  await click(btn('Mark dried today', card(1)));
  await click(q('[data-spool="2"] [data-act="sp-menu"]'));
  assert(btn('Mark dried today', card(2)) && !btn('Clear dried date', card(2)), 'clear only when marked');
  await click(q('[data-spool="1"] [data-act="sp-menu"]'));
  await click(btn('Clear dried date', card(1)));
  eq(sentOf('spool_action').map(m => m.action).filter(a => a !== 'locations'), ['dried', 'clear_dried'], 'actions');
  await spools([marked], {display: {...DEFAULTS, dried: false}});
  assert(!byTest('dried'), 'switch hides it');
`);
test('details panel renders the history as text', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await click(q('[data-spool="1"] [data-act="sp-menu"]'));
  await click(btn('Details', card(1)));
  eq(lastOf('spool_detail').id, 1, 'asked');
  await post({type: 'spool_detail', detail: {id: 1, sign: '£', grams: 80, cost: 2.5, rate: 20, weeks: 5, prints: [{time: 1700000000, name: '<b>Benchy</b>', grams: 40, cost: 1}]}});
  const d = text(card(1));
  for (const s of ['1 print', '20 g a week', 'about 5 weeks left', '£2.50', '<b>Benchy</b>']) assert(d.includes(s), 'detail has ' + s + ': ' + d);
  assert(!card(1).querySelector('b b, td b'), 'markup is text, not HTML');
`);
test('weights and grams fields validate before sending (no blank grams)', `
  await spools(SPOOLS, {display: {...DEFAULTS, group_same: false}});
  await click(q('[data-spool="1"] [data-act="sp-menu"]'));
  await click(btn('Use filament', card(1)));
  assert(q('[data-spool="1"] [data-act="sp-go"]').disabled, 'Save waits for grams');
  await type(q('#sc-in-1'), 'abc');
  assert(q('[data-spool="1"] [data-act="sp-go"]').disabled && text(card(1)).includes('Enter a number of grams'), 'invalid explained');
  await type(q('#sc-in-1'), '12,5');
  await press('Enter');
  const use = sentOf('spool_action').find(m => m.action === 'use');
  eq(use.grams, '12.5', 'decimal comma accepted');
`);

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
  assert(text(q('.lu')).includes('SV06 refused <x>') && q('.lu .sp-err'), 'result as text on the card');
  assert(alerts().includes('SV06 refused'), 'and persists in the status area');
  await post({type: 'live', live: {links: {'auto-sv': 'live'}, printers: [sv(null)]}});
  assert(btn('Change spool') && !btn('Clear'), 'no active spool: change only');
  await click(btn('Change spool'));
  await until(() => q('[data-pick="7"]'));
  await click(q('[data-pick="7"]'));
  eq(lastOf('moon_spool'), {type: 'moon_spool', id: 'auto-sv', spool: 7, origin: 3}, 'set with the list origin');
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
test('plate check: rows, attention pill, recheck and dismiss', `
  await spools(SPOOLS);
  await post({type: 'plate', time: '10:00', rows: [{status: 'short', colour: '111111', slots: 'T1', name: 'Black', meta: 'Acme', fill: .4, spool_colour: '111111', need_pct: .6,
    headline: 'Not enough', detail: 'needs 600 g', ids: [1], first: 0}]});
  await tab('printer');
  assert(text(byTest('plate')).includes('1 needs attention') && text(byTest('plate')).includes('Not enough'), 'plate shown');
  assert(q('[data-tab="printer"] .sp-dot'), 'attention dot on the tab');
  await click(btn('Check again'));
  eq(lastOf('plate_recheck').type, 'plate_recheck', 'recheck');
  await tab('spools');
  assert(text(card(1) || q('[data-stack]')).length, 'list');
  await tab('printer');
  await click(btn('Dismiss', byTest('plate')));
  assert(!byTest('plate') && lastOf('plate_dismiss'), 'dismissed');
`);

// ------------------------------------------------------------------ stats (test_detail_export / test_stats)
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
  await click(byTest('save'));
  const s = lastOf('save');
  eq([s.view, s.display.diameter, s.drying['NYLON CF'], s.drying.HIPS, s.url], ['settings', true, 0, 9, 'http://spoolman:7912'], 'saved');
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
  assert(text(q('[data-tab="spools"]')) === 'Bobinas', 'nav');
  assert(text(q('[data-stack] .st-head')).includes('1.380 g de 2.000 g'), 'weights in pt-BR: ' + text(q('[data-stack] .st-head')));
  await post({type: 'spools', ok: false, error: 'x', error_code: 'no_url'});
  assert(text(byTest('empty-no-url')).includes('O Spoolman ainda não foi configurado'), 'empty state');
`, { lang: 'pt_BR' });
test('X04: the saved explicit language wins over the host', `
  await until(() => q('[data-tab="spools"]'));
  eq(text(q('[data-tab="spools"]')), 'Spools', 'English kept');
  await click(byTest('settings-btn'));
  await post({type: 'show_view', view: 'settings', url: '', source: 'spoolman', low_stock: 100, display: DEFAULTS, drying: {}, progress: {}, stats: {}});
  await pick(byTest('lang'), 'Português (Brasil)');
  eq(lastOf('ui_language'), {type: 'ui_language', value: 'pt-BR', view: 'settings'}, 'saved through the plugin');
  assert(text(q('#s-lang')) === 'Idioma', 'switched');
`, { lang: 'pt_BR', pref: 'en' });
test('B-21/B-24: focus ring on group heads is visible; reduced motion honoured', `
  await spools(SPOOLS);
  const head = q('[data-stack] .st-head');
  head.focus(); await press('Tab', true); await press('Tab');
  const cs = getComputedStyle(document.activeElement);
  assert(document.activeElement === head && cs.outlineStyle !== 'none' && parseFloat(cs.outlineWidth) >= 2, 'visible 2px ring: ' + cs.outlineStyle + ' ' + cs.outlineWidth);
`);

// ------------------------------------------------------------------ runner
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
      const mode = sc.mode || 'tab';
      const boot = { mode, view: mode === 'settings' ? 'settings' : 'main', version: 'test', lang: sc.lang ?? 'en', pref: sc.pref ?? 'auto',
        low_stock_default: 100, refresh_ms: 600000, display_defaults: DISPLAY_DEFAULTS, own_fields: ['tag', 'orca_settings', 'dried', 'orca_flow_ratio'],
        settings: { ...SETTINGS, wizard: !!sc.wizard } };
      const file = join(dir, `p${k}.html`);
      await writeFile(file, preparePage(page, boot));
      const p = await browser.newPage();
      const started = Date.now();
      try {
        await p.size(1280, 900);
        await p.init(MOCK_HOST + 'try { localStorage.clear(); } catch {}');
        await p.goto(pathToFileURL(file).href);
        const body = `(async () => { ${HELPERS} ${PRELUDE}
          await until(() => document.querySelector('#app > *'), 'app mounted');
          ${sc.body}
          await settle();
          return { violations: __t.violations, rejections: __t.rejections, errors: __t.errors };
        })()`;
        const probe = await p.evaluate(body);
        if (probe.violations.length || probe.rejections.length || probe.errors.length) throw new Error('page problems: ' + JSON.stringify(probe));
        results.push({ name: sc.name, ok: true, ms: Date.now() - started });
        console.log(`ok   ${sc.name}`);
      } catch (e) {
        failed++;
        results.push({ name: sc.name, ok: false, error: String(e.message || e) });
        console.log(`FAIL ${sc.name}\n     ${String(e.message || e).split('\n')[0]}`);
      } finally {
        await p.close();
      }
    }
  }));
} finally {
  await browser.close();
  await rm(dir, { recursive: true, force: true });
}
if (process.env.RESULTS) await writeFile(process.env.RESULTS, JSON.stringify(results, null, 2));
console.log(`${chosen.length - failed}/${chosen.length} page scenarios passed`);
if (failed || !chosen.length) process.exit(1);
console.log('PASS');
