// The spool editor's rules: the form a Spoolman spool or filament opens as, what a form sends, what an edit changed.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { changed, decodeExtra, densityFor, editable, encodeExtra, filamentForm, filamentPayload, filled, problems, spoolForm, spoolPayload, wasOf,
  type FieldDef } from '../../src/logic/editor.ts';

const DEFS: FieldDef[] = [
  { key: 'sealed', field_type: 'boolean', order: 2 }, { key: 'grade', field_type: 'choice', choices: ['A', 'B'], order: 1 },
  { key: 'tags', field_type: 'choice', choices: ['x', 'y'], multi_choice: true }, { key: 'shrink', field_type: 'float', unit: '%' },
  { key: 'layers', field_type: 'integer_range' }, { key: 'bought', field_type: 'datetime' }, { key: 'dryer', field_type: 'text' },
  { key: 'orca_settings', field_type: 'text' }];
const def = (k: string) => DEFS.find(d => d.key === k)!;
const FIL = { id: 9, name: 'Black', material: 'PLA', color_hex: 'aabbcc', density: 1.24, diameter: 1.75, vendor: { name: 'Acme' },
  extra: { grade: '"A"', shrink: '0.4', orca_settings: '"{}"' } };

test('the editor shows the user’s extra fields in Spoolman’s order, never Spooler’s own', () => {
  assert.deepEqual(editable(DEFS, ['orca_settings']).map(d => d.key), ['tags', 'shrink', 'layers', 'bought', 'dryer', 'grade', 'sealed']);
});

test('extra values decode from Spoolman’s JSON text by type and encode back as typed values', () => {
  assert.equal(decodeExtra('true', def('sealed')), true);
  assert.equal(decodeExtra('"A"', def('grade')), 'A');
  assert.deepEqual(decodeExtra('["x"]', def('tags')), ['x']);
  assert.equal(decodeExtra('0.4', def('shrink')), 0.4);
  assert.deepEqual(decodeExtra('[2, null]', def('layers')), [2, null]);
  assert.equal(decodeExtra('"Box 1"', def('dryer')), 'Box 1');
  assert.equal(decodeExtra('Box 1', def('dryer')), 'Box 1', 'plain text kept');
  assert.equal(decodeExtra('nope', def('shrink')), null);
  assert.equal(decodeExtra(undefined, def('sealed')), null);
  assert.equal(encodeExtra('  ', def('dryer')), null, 'empty text unsets');
  assert.equal(encodeExtra([], def('tags')), null);
  assert.equal(encodeExtra([null, null], def('layers')), null);
  assert.equal(encodeExtra(false, def('sealed')), false, 'false is a value');
});

test('a filament opens as a form and sends one colour, or several with their direction', () => {
  const f = filamentForm(FIL, DEFS);
  assert.deepEqual([f.vendor, f.colors, f.extra.grade, f.extra.shrink], ['Acme', ['#aabbcc'], 'A', 0.4]);
  assert.deepEqual(filamentPayload(f, []).color_hex, 'AABBCC');
  const multi = filamentPayload({ ...f, colors: ['#ff0000', '#00ff00'], direction: 'longitudinal' }, []);
  assert.deepEqual([multi.color_hex, multi.multi_color_hexes, multi.multi_color_direction], [null, 'FF0000,00FF00', 'longitudinal']);
  const fresh = filamentForm(undefined, []);
  assert.deepEqual([fresh.diameter, fresh.density, fresh.colors], [1.75, null, ['']]);
  assert.equal(filamentPayload(fresh, []).color_hex, null, 'no colour picked: none sent');
});

test('a new spool or filament sends no empty field', () => {
  const p = filled(spoolPayload({ ...spoolForm(undefined, []), remaining_weight: 750, location: '  ' }, []));
  assert.deepEqual(p, { remaining_weight: 750, archived: false });
  assert.deepEqual(filled({ a: null, extra: { x: null, y: 'v' } }), { extra: { y: 'v' } });
});

test('an edit sends only what changed, with what Spoolman held for those fields', () => {
  const spool = { id: 7, location: 'Shelf A', remaining_weight: 500, extra: { dryer: '"Box 1"' }, filament: FIL };
  const defs = [def('dryer'), def('sealed')];
  const base = spoolPayload(spoolForm(spool, defs), defs);
  const now = spoolPayload({ ...spoolForm(spool, defs), location: 'Dry box', extra: { dryer: 'Box 1', sealed: true } }, defs);
  const diff = changed(now, base);
  assert.deepEqual(diff, { location: 'Dry box', extra: { sealed: true } });
  assert.deepEqual(wasOf(spool, diff), { location: 'Shelf A', extra: { sealed: null } });
  assert.deepEqual(changed(base, base), {});
  const fBase = filamentPayload(filamentForm(FIL, []), []);
  const fDiff = changed(filamentPayload({ ...filamentForm(FIL, []), vendor: 'Polymaker', colors: ['#AABBCC'] }, []), fBase);
  assert.deepEqual(fDiff, { vendor: 'Polymaker' }, 'the same colour in another case is no change');
  assert.deepEqual(wasOf(FIL, fDiff), { vendor: 'Acme' });
});

test('problems: density and diameter required, no more left than at the start, ISO dates', () => {
  const s = spoolForm(undefined, []), f = filamentForm(undefined, []);
  assert.deepEqual(problems(s, f, { spool: [], filament: [] }, true), { density: 'required' });
  assert.deepEqual(problems({ ...s, initial_weight: 500, remaining_weight: 600 }, null, { spool: [], filament: [] }, true), { remaining_weight: 'tooMuch' });
  assert.deepEqual(problems({ ...s, initial_weight: 500, remaining_weight: 600 }, null, { spool: [], filament: [] }, false), {}, 'an edit may');
  const withDate = { ...s, extra: { bought: '16/11/2026' } };
  assert.deepEqual(problems(withDate, null, { spool: [def('bought')], filament: [] }, false), { 'spool.bought': 'date' });
  assert.deepEqual(problems({ ...s, extra: { bought: '2026-11-16' } }, null, { spool: [def('bought')], filament: [] }, false), {});
});

test('a new filament gets its material’s usual density', () => {
  assert.equal(densityFor('PETG HF'), 1.27);
  assert.equal(densityFor('pla+'), 1.24);
  assert.equal(densityFor('PA-CF'), 1.14);
  assert.equal(densityFor('Wood'), null);
});
