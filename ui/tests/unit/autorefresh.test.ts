// The Spoolman re-read timer: interval, paused while hidden, one read at a time, backoff, never while the user edits.
import { test, mock } from 'node:test';
import assert from 'node:assert/strict';
import { autoRefresh, cleanEvery, nextDelayS } from '../../src/core/autorefresh.ts';

function fakeDoc() {
  const fns = new Set<() => void>();
  return {
    hidden: false,
    addEventListener: (_: string, f: () => void) => { fns.add(f); },
    removeEventListener: (_: string, f: () => void) => { fns.delete(f); },
    show(hidden: boolean) { this.hidden = hidden; fns.forEach(f => f()); },
  };
}
const flush = async () => { for (let i = 0; i < 5; i++) await Promise.resolve(); };

function setup(opts: { every?: number; ok?: () => boolean; held?: () => boolean; slow?: boolean } = {}) {
  mock.timers.enable({ apis: ['setTimeout'] });
  const doc = fakeDoc();
  let reads = 0, release: (() => void) | null = null;
  const failing: boolean[] = [];
  const auto = autoRefresh({
    doc, every: () => opts.every ?? 30, held: opts.held, onFailing: f => failing.push(f),
    load: () => { reads++; if (opts.slow) return new Promise(r => { release = () => r(true); }); return Promise.resolve(opts.ok ? opts.ok() : true); },
  });
  const tick = async (s: number) => { mock.timers.tick(s * 1000); await flush(); };
  return { doc, auto, tick, failing, reads: () => reads, release: () => release?.() };
}

test('reads every 30 s by default', async (t) => {
  const r = setup(); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  await r.tick(29); assert.equal(r.reads(), 0);
  await r.tick(1); assert.equal(r.reads(), 1);
  await r.tick(30); assert.equal(r.reads(), 2);
});

test('paused while hidden, reads at once when shown again', async (t) => {
  const r = setup(); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  r.doc.show(true);
  await r.tick(120); assert.equal(r.reads(), 0);
  r.doc.show(false); await flush(); assert.equal(r.reads(), 1);
  await r.tick(30); assert.equal(r.reads(), 2);
});

test('no overlapping reads', async (t) => {
  const r = setup({ slow: true }); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  await r.tick(30); assert.equal(r.reads(), 1);
  r.doc.show(false); await flush();          // a visibility event during the read starts no second one
  await r.tick(120); assert.equal(r.reads(), 1);
  r.release(); await flush();
  await r.tick(30); assert.equal(r.reads(), 2);
});

test('backs off 30, 60, 120 … up to 5 min on errors, and recovers', async (t) => {
  let ok = false;
  const r = setup({ ok: () => ok }); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  await r.tick(30); assert.equal(r.reads(), 1); assert.deepEqual(r.failing, [true]);
  await r.tick(30); assert.equal(r.reads(), 2);              // after 1 failure: 30 s
  await r.tick(59); assert.equal(r.reads(), 2); await r.tick(1); assert.equal(r.reads(), 3);   // 60 s
  await r.tick(119); assert.equal(r.reads(), 3); await r.tick(1); assert.equal(r.reads(), 4);  // 120 s
  assert.deepEqual([nextDelayS(30, 4), nextDelayS(30, 5), nextDelayS(30, 9)], [240, 300, 300]);
  ok = true;
  await r.tick(240); assert.equal(r.reads(), 5); assert.deepEqual(r.failing, [true, false]);
  await r.tick(30); assert.equal(r.reads(), 6);
});

test('waits while the user edits, then reads', async (t) => {
  let held = true;
  const r = setup({ held: () => held }); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  await r.tick(90); assert.equal(r.reads(), 0);
  held = false; await r.tick(1); assert.equal(r.reads(), 1);
});

test('off reads nothing; the setting is 0 or 10–300 s', async (t) => {
  const r = setup({ every: 0 }); t.after(() => { r.auto.stop(); mock.timers.reset(); });
  await r.tick(600); assert.equal(r.reads(), 0);
  assert.deepEqual([0, 10, 300, 45, 9, 301, '30', null, 2.5].map(cleanEvery), [0, 10, 300, 45, 30, 30, 30, 30, 30]);
});
