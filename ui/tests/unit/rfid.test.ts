// A new RFID spool's Add Spool: the editor pre-filled from the printer's tray, and the Spoolman filament it restocks.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { filamentForm, filamentPayload, spoolForm } from '../../src/logic/editor.ts';
import { leftGrams, matchFilament, rfidPrefill, type RfidOffer } from '../../src/logic/rfid.ts';

const OFFER: RfidOffer = { tag: 'A1B2C3D4E5F60718293A4B5C6D7E8F90', printer: 'p1', unit: 0, slot: 2, type: 'PLA', name: 'PLA Matte',
  colours: ['3C3C3C'], remain: 80, weight: 1000, diameter: 1.75, nozzle: [190, 230] };

test('the editor opens as a Bambu Lab filament with the tray’s material, colour, diameter, middle nozzle temperature and weight', () => {
  const pre = rfidPrefill(OFFER);
  const f = filamentForm(pre.filament, []);
  assert.equal(f.vendor, 'Bambu Lab');
  assert.equal(f.name, 'PLA Matte');
  assert.equal(f.material, 'PLA');
  assert.deepEqual(f.colors, ['#3c3c3c']);
  assert.equal(f.diameter, 1.75);
  assert.equal(f.density, 1.24, 'the usual PLA density');
  assert.equal(f.settings_extruder_temp, 210);
  assert.equal(f.weight, 1000);
  const s = spoolForm(pre.spool, []);
  assert.equal(s.initial_weight, 1000);
  assert.equal(s.remaining_weight, 800, '80% of 1000 g');
  assert.equal(pre.tag, OFFER.tag);
});

test('a multi-colour tray opens as a multi-colour filament', () => {
  const f = filamentForm(rfidPrefill({ ...OFFER, colours: ['FF0000', '00FF00', '0000FF'] }).filament, []);
  assert.deepEqual(f.colors, ['#ff0000', '#00ff00', '#0000ff']);
  assert.equal(filamentPayload(f, []).multi_color_hexes, 'FF0000,00FF00,0000FF');
});

test('what the tray doesn’t report stays empty', () => {
  const pre = rfidPrefill({ ...OFFER, remain: null, weight: null, nozzle: null, diameter: null });
  assert.equal(leftGrams({ ...OFFER, remain: null }), null);
  assert.equal(pre.spool.initial_weight, null);
  assert.equal(pre.spool.remaining_weight, null);
  assert.equal(pre.filament.settings_extruder_temp, null);
  assert.equal(pre.filament.diameter, 1.75, 'the usual diameter');
});

test('an existing Bambu Lab filament of the same material and colour is picked; one named like the tray wins', () => {
  const fils = [
    { id: 1, name: 'PLA Basic Charcoal', material: 'PLA', color_hex: '3C3C3C', vendor: { name: 'Bambu Lab' } },
    { id: 2, name: 'PLA Matte Charcoal', material: 'pla', color_hex: '3c3c3c', vendor: { name: ' bambu lab ' } },
    { id: 3, name: 'PLA Matte Charcoal', material: 'PLA', color_hex: '3C3C3C', vendor: { name: 'Acme' } },
  ];
  assert.equal(matchFilament(fils, OFFER), 2);
  assert.equal(matchFilament(fils.slice(0, 1), OFFER), 1);
  assert.equal(matchFilament(fils.slice(2), OFFER), null, 'another vendor');
  assert.equal(matchFilament(fils, { ...OFFER, colours: ['FFFFFF'] }), null, 'another colour');
  assert.equal(matchFilament(fils, { ...OFFER, type: 'PETG' }), null, 'another material');
  assert.equal(matchFilament(fils, { ...OFFER, colours: [] }), null, 'no colour reported');
  assert.equal(matchFilament(undefined, OFFER), null);
  const plain = [{ ...fils[0], id: 6, name: 'Charcoal' }, { ...fils[0], id: 7, name: 'Black' }];
  assert.equal(matchFilament(plain, OFFER), null, 'two fits, neither named like the tray: none picked');
  assert.equal(matchFilament([fils[1], { ...fils[1], id: 9 }], OFFER), null, 'two named alike: none picked');
});

test('a multi-colour filament matches only the same colours in the same order', () => {
  const fil = { id: 5, name: 'PLA Silk Multi', material: 'PLA', multi_color_hexes: 'FF0000,00FF00', vendor: { name: 'Bambu Lab' } };
  assert.equal(matchFilament([fil], { ...OFFER, colours: ['FF0000', '00FF00'] }), 5);
  assert.equal(matchFilament([fil], { ...OFFER, colours: ['00FF00', 'FF0000'] }), null);
});
