// Owned headless Chrome over the DevTools protocol (no Puppeteer/Playwright, no npm dependency). Real time, real
// input events (Input.insertText / dispatchKeyEvent) and a CSP meta like the host's. Chrome always gets
// --use-mock-keychain --password-store=basic (Heitor's rule for every headless Chrome).
import { spawn, execFileSync } from 'node:child_process';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

export const CSP = "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src data:; connect-src 'none'; font-src 'none'";

export function findChrome() {
  const env = process.env.CHROME;
  if (env) return env;
  for (const p of ['/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', 'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe', '/usr/bin/google-chrome', '/usr/bin/google-chrome-stable', '/usr/bin/chromium', '/usr/bin/chromium-browser']) {
    if (existsSync(p)) return p;
  }
  for (const name of ['google-chrome', 'chromium', 'chromium-browser']) {
    try { return execFileSync('which', [name], { encoding: 'utf8' }).trim(); } catch { /* next */ }
  }
  throw new Error('Chrome/Chromium is needed for the page tests: install it or set CHROME=/path/to/chrome');
}

const delay = ms => new Promise(r => setTimeout(r, ms));

export async function launch() {
  const profile = await mkdtemp(join(tmpdir(), 'orca-page-test-'));
  const proc = spawn(findChrome(), ['--headless=new', '--disable-extensions', '--disable-component-extensions-with-background-pages', '--use-mock-keychain', '--password-store=basic', '--disable-gpu',
    '--disable-background-networking', '--no-first-run', '--no-default-browser-check', '--remote-debugging-port=0',
    '--allow-file-access-from-files', `--user-data-dir=${profile}`, 'about:blank'], { stdio: ['ignore', 'ignore', 'pipe'] });
  let log = '';
  proc.stderr.on('data', c => { log += c; });
  let port;
  for (let i = 0; i < 300 && !port; i++) {
    try { port = (await readFile(join(profile, 'DevToolsActivePort'), 'utf8')).split('\n')[0]; } catch { await delay(20); }
  }
  if (!port) { proc.kill('SIGKILL'); throw new Error('headless Chrome did not start:\n' + log); }
  return {
    port,
    async newPage() { return openPage(port); },
    async close() {
      proc.kill('SIGTERM');
      await new Promise(r => (proc.exitCode !== null ? r() : proc.once('exit', r)));
      await rm(profile, { recursive: true, force: true });
    },
  };
}

async function openPage(port) {
  const target = await (await fetch(`http://127.0.0.1:${port}/json/new?about:blank`, { method: 'PUT' })).json();
  const ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((res, rej) => { ws.onopen = res; ws.onerror = rej; });
  let next = 0;
  const waiting = new Map();
  const events = [];
  const handlers = new Set();
  ws.onmessage = ({ data }) => {
    const m = JSON.parse(data);
    if (m.id && waiting.has(m.id)) { const w = waiting.get(m.id); waiting.delete(m.id); m.error ? w.rej(new Error(JSON.stringify(m.error))) : w.res(m.result); return; }
    if (m.method) { events.push(m); handlers.forEach(h => h(m)); }
  };
  const call = (method, params = {}) => new Promise((res, rej) => { const id = ++next; waiting.set(id, { res, rej }); ws.send(JSON.stringify({ id, method, params })); });
  await call('Page.enable');
  await call('Runtime.enable');
  await call('Runtime.addBinding', { name: '__cdp' });
  await call('Emulation.setFocusEmulationEnabled', { enabled: true });
  // Page-side helpers ask for trusted input through the binding; we answer by marking the request done.
  handlers.add(async m => {
    if (m.method !== 'Runtime.bindingCalled' || m.params.name !== '__cdp') return;
    const req = JSON.parse(m.params.payload);
    try {
      if (req.op === 'insert') await call('Input.insertText', { text: req.text });
      if (req.op === 'type') {   // real key events per character, like a keyboard (keydown/keypress/input)
        for (const ch of req.text) {
          await call('Input.dispatchKeyEvent', { type: 'keyDown', key: ch, text: ch, unmodifiedText: ch });
          await call('Input.dispatchKeyEvent', { type: 'keyUp', key: ch });
        }
      }
      if (req.op === 'key') {
        const k = KEYS[req.key] ?? { key: req.key, code: req.key, keyCode: 0 };
        const modifiers = req.shift ? 8 : 0;
        await call('Input.dispatchKeyEvent', { type: k.text ? 'keyDown' : 'rawKeyDown', modifiers, windowsVirtualKeyCode: k.keyCode, key: k.key, code: k.code,
          ...(k.text ? { text: k.text, unmodifiedText: k.text } : {}) });
        await call('Input.dispatchKeyEvent', { type: 'keyUp', modifiers, windowsVirtualKeyCode: k.keyCode, key: k.key, code: k.code });
      }
      if (req.op === 'clickAt') {
        for (const type of ['mousePressed', 'mouseReleased']) await call('Input.dispatchMouseEvent', { type, x: req.x, y: req.y, button: 'left', clickCount: 1 });
      }
    } finally {
      await call('Runtime.evaluate', { expression: `window.__t.acks.add(${JSON.stringify(req.id)})` });
    }
  });
  return {
    call,
    events,
    async init(script) { await call('Page.addScriptToEvaluateOnNewDocument', { source: script }); },
    async goto(url) {
      const loaded = new Promise(r => { const h = m => { if (m.method === 'Page.loadEventFired') { handlers.delete(h); r(); } }; handlers.add(h); });
      await call('Page.navigate', { url });
      await loaded;
    },
    async evaluate(expression) {
      const r = await call('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
      if (r.exceptionDetails) {
        const d = r.exceptionDetails;
        throw new Error((d.exception && (d.exception.description || d.exception.value)) || d.text);
      }
      return r.result.value;
    },
    async size(width, height, scale = 1) { await call('Emulation.setDeviceMetricsOverride', { width, height, deviceScaleFactor: scale, mobile: false }); },
    async screenshot() { return Buffer.from((await call('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false })).data, 'base64'); },
    async close() { ws.close(); await fetch(`http://127.0.0.1:${port}/json/close/${target.id}`).catch(() => {}); },
  };
}

const KEYS = {
  Tab: { key: 'Tab', code: 'Tab', keyCode: 9 }, Escape: { key: 'Escape', code: 'Escape', keyCode: 27 },
  Enter: { key: 'Enter', code: 'Enter', keyCode: 13, text: '\r' }, ArrowDown: { key: 'ArrowDown', code: 'ArrowDown', keyCode: 40 },
  ArrowUp: { key: 'ArrowUp', code: 'ArrowUp', keyCode: 38 }, Space: { key: ' ', code: 'Space', keyCode: 32, text: ' ' },
  Backspace: { key: 'Backspace', code: 'Backspace', keyCode: 8 },
};

/** Installed before the page's own scripts: a scripted OrcaSlicer bridge plus probes for CSP, errors and rejections. */
export const MOCK_HOST = `
window.__t = { sent: [], handler: null, submits: [], violations: [], rejections: [], errors: [], acks: new Set(), seq: 0 };
window.orca = {
  postMessage(m) { __t.sent.push(JSON.parse(JSON.stringify(m))); },
  onMessage(h) { __t.handler = h; },
  submit(r) { __t.submits.push(JSON.parse(JSON.stringify(r))); },
};
document.addEventListener('securitypolicyviolation', e => __t.violations.push(e.violatedDirective + ' ' + e.blockedURI));
window.addEventListener('unhandledrejection', e => __t.rejections.push(String(e.reason && e.reason.message || e.reason)));
window.addEventListener('error', e => __t.errors.push(String(e.message)));
`;

/** Scenario helpers, evaluated in the page before each scenario body. */
export const HELPERS = `
const doc = document;
const sleep = ms => new Promise(r => setTimeout(r, ms));
const frame = () => new Promise(r => requestAnimationFrame(() => r()));
async function settle() { await sleep(0); await frame(); await frame(); await sleep(30); }
async function until(test, what, ms = 4000) { const end = performance.now() + ms; while (!test()) { if (performance.now() > end) throw new Error('timed out: ' + (what || test)); await sleep(20); } }
function assert(c, what) { if (!c) throw new Error('assertion failed: ' + what); }
function eq(a, b, what) { const x = JSON.stringify(a), y = JSON.stringify(b); if (x !== y) throw new Error(what + ': ' + x + ' !== ' + y); }
const sent = () => __t.sent;
const last = (type, cmd) => [...__t.sent].reverse().find(m => m.type === type && (cmd === undefined || m.cmd === cmd));
const cmds = name => __t.sent.filter(m => m.type === 'cmd' && m.cmd === name);
async function post(m) { if (!__t.handler) await until(() => __t.handler, 'bridge handler'); __t.handler(JSON.parse(JSON.stringify(m))); await settle(); }
const reply = (msg, result) => post({ type: 'reply', id: msg.id, result });
const fail = (msg, error, extra) => post({ type: 'reply', id: msg.id, error, ...(extra || {}) });
const q = (sel, root = document) => root.querySelector(sel);
const qa = (sel, root = document) => [...root.querySelectorAll(sel)];
const byTest = name => document.querySelector('[data-test="' + name + '"]');
const text = el => (el ? el.textContent.replace(/\\s+/g, ' ').trim() : '');
const btn = (label, root = document) => qa('button', root).find(b => text(b) === label || b.getAttribute('aria-label') === label);
const dialogEl = () => document.querySelector('.p-dialog');
const dialogOpen = () => !!dialogEl();
async function click(el) { assert(el, 'element to click'); el.click(); await settle(); }
let __n = 0;
async function cdp(req) { const id = 'r' + (++__n); __cdp(JSON.stringify({ ...req, id })); await until(() => __t.acks.has(id), 'cdp ' + req.op); await settle(); }
async function type(el, value) { assert(el, 'element to type into'); el.focus(); if (el.select) el.select(); await cdp({ op: 'key', key: 'Backspace' }); if (value !== '') await cdp({ op: 'type', text: value }); }
const press = (key, shift) => cdp({ op: 'key', key, shift: !!shift });
async function mouse(el) { assert(el, 'element for a real click'); el.scrollIntoView({ block: 'center' }); await settle(); const r = el.getBoundingClientRect(); await cdp({ op: 'clickAt', x: r.left + r.width / 2, y: r.top + r.height / 2 }); }
async function answer(which) { await until(dialogOpen, 'dialog'); const el = dialogEl(); await click(q('[data-dlg="' + which + '"]', el)); await until(() => dialogEl() !== el, 'dialog closed'); }
const yes = () => answer('yes');
const no = () => answer('no');
const dialogText = () => text(dialogEl());
`;

/** Fill the boot JSON the way the plugin does (json_for_html) and add the CSP meta. */
export function preparePage(html, boot) {
  const json = JSON.stringify(boot).replace(/</g, '\\u003c').replace(/>/g, '\\u003e').replace(/&/g, '\\u0026');
  if (!html.includes('__BOOT__')) throw new Error('page has no __BOOT__ slot');
  return html.replace('__BOOT__', () => json).replace('<head>', `<head><meta http-equiv="Content-Security-Policy" content="${CSP}">`);
}
