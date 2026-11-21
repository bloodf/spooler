// Runs the page's script, which scripts/embed_ui.py stores deflated and base64-encoded in #spooler-js: the page
// then fits OrcaSlicer's WebView2 on Windows (2 MiB once base64-encoded, 1.5 MiB of UTF-8). Raw DEFLATE
// (RFC 1951) after zlib's puff.c, so it needs no DecompressionStream (Safari 14).
const LBASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEXT = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DBASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DEXT = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

function inflate(src) {
  let out = new Uint8Array(src.length * 4), n = 0, pos = 0, bit = 0;
  const room = k => { if (n + k > out.length) { const o = new Uint8Array(Math.max(out.length * 2, n + k)); o.set(out); out = o; } };
  const bits = k => {
    let v = 0;
    for (let i = 0; i < k; i++) {
      if (pos >= src.length) throw new Error('inflate: data ends early');
      v |= ((src[pos] >> bit) & 1) << i;
      if (++bit === 8) { bit = 0; pos++; }
    }
    return v;
  };
  const table = lengths => {
    const count = new Uint16Array(16), offs = new Uint16Array(16), symbol = new Uint16Array(lengths.length);
    for (const l of lengths) count[l]++;
    count[0] = 0;
    for (let i = 1; i < 16; i++) offs[i] = offs[i - 1] + count[i - 1];
    lengths.forEach((l, s) => { if (l) symbol[offs[l]++] = s; });
    return { count, symbol };
  };
  const decode = h => {
    let code = 0, first = 0, index = 0;
    for (let len = 1; len < 16; len++) {
      code |= bits(1);
      const c = h.count[len];
      if (code - c < first) return h.symbol[index + code - first];
      index += c; first = (first + c) << 1; code <<= 1;
    }
    throw new Error('inflate: bad code');
  };
  let last;
  do {
    last = bits(1);
    const type = bits(2);
    if (type === 0) {
      if (bit) { bit = 0; pos++; }
      const len = src[pos] | (src[pos + 1] << 8);
      pos += 4;
      if (pos + len > src.length) throw new Error('inflate: data ends early');
      room(len); out.set(src.subarray(pos, pos + len), n); n += len; pos += len;
      continue;
    }
    let lit, dist;
    if (type === 1) {
      lit = table(Array.from({ length: 288 }, (_, i) => (i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8)));
      dist = table(new Array(30).fill(5));
    } else if (type === 2) {
      const nlen = bits(5) + 257, ndist = bits(5) + 1, ncode = bits(4) + 4;
      const cl = new Array(19).fill(0);
      for (let i = 0; i < ncode; i++) cl[ORDER[i]] = bits(3);
      const ch = table(cl), lens = [];
      while (lens.length < nlen + ndist) {
        const s = decode(ch);
        if (s < 16) { lens.push(s); continue; }
        if (s === 16 && !lens.length) throw new Error('inflate: bad repeat');
        const v = s === 16 ? lens[lens.length - 1] : 0;
        for (let r = s === 16 ? 3 + bits(2) : s === 17 ? 3 + bits(3) : 11 + bits(7); r > 0; r--) lens.push(v);
      }
      lit = table(lens.slice(0, nlen)); dist = table(lens.slice(nlen, nlen + ndist));
    } else throw new Error('inflate: bad block');
    for (;;) {
      let s = decode(lit);
      if (s < 256) { room(1); out[n++] = s; continue; }
      if (s === 256) break;
      s -= 257;
      if (s >= 29) throw new Error('inflate: bad length');
      const len = LBASE[s] + bits(LEXT[s]), d = decode(dist);
      if (d >= 30) throw new Error('inflate: bad distance');
      const back = DBASE[d] + bits(DEXT[d]);
      if (back > n) throw new Error('inflate: distance too far');
      room(len);
      for (let i = 0; i < len; i++, n++) out[n] = out[n - back];
    }
  } while (!last);
  return out.subarray(0, n);
}

// The page never stays a blank grey panel: an error before the app mounts (window errors, rejections and the app's
// errorHandler report through window.__spoolerError), or nothing mounted after START_MS, shows what failed with a
// Copy diagnostics button, and tells the plugin so the errors reach spooler.log.
const START_MS = window.__spoolerStartMs || 10000;   // tests shorten it
const startErrors = [];
const FAIL_TEXT = {
  en: ['Spooler could not open its page.', 'Copy diagnostics', 'The log is at'],
  pt: ['O Spooler não conseguiu abrir a página.', 'Copiar diagnóstico', 'O log está em'],
  es: ['Spooler no pudo abrir su página.', 'Copiar diagnóstico', 'El registro está en'],
  de: ['Spooler konnte seine Seite nicht öffnen.', 'Diagnose kopieren', 'Das Protokoll liegt unter'],
  zh: ['Spooler 无法打开页面。', '复制诊断信息', '日志位于'],
  pl: ['Spooler nie mógł otworzyć swojej strony.', 'Kopiuj diagnostykę', 'Dziennik jest w'],
};

function showFailure() {
  const app = document.getElementById('app');
  if ((app && app.children.length) || document.getElementById('spooler-failed')) return;
  let boot = {};
  try { boot = JSON.parse(document.getElementById('spooler-boot').textContent); } catch { /* no boot: defaults */ }
  const lang = String((boot.pref && boot.pref !== 'auto' ? boot.pref : boot.lang) || navigator.language || 'en').slice(0, 2).toLowerCase();
  const [title, copy, logAt] = FAIL_TEXT[lang] || FAIL_TEXT.en;
  const errors = startErrors.length ? startErrors : ['Nothing started within ' + START_MS / 1000 + ' s, and no error was reported.'];
  const logPath = (boot.settings && boot.settings.log_path) || '';
  const diag = ['Spooler ' + (boot.version || '?') + ' (' + (boot.mode || '?') + ')', navigator.userAgent,
    'Language: ' + (boot.lang || navigator.language), ...errors].join('\n');
  try { window.orca.postMessage({ type: 'page_error', errors, agent: navigator.userAgent }); } catch { /* no bridge: on screen only */ }
  const box = document.createElement('div');
  box.id = 'spooler-failed';
  box.style.cssText = 'font:14px system-ui,sans-serif;margin:24px;color:inherit';
  const h = document.createElement('h1');
  h.style.fontSize = '16px';
  h.textContent = title;
  const p = document.createElement('p');
  p.textContent = logPath ? logAt + ' ' + logPath : '';
  const pre = document.createElement('pre');
  pre.style.cssText = 'white-space:pre-wrap;user-select:text;padding:8px;border:1px solid #8884';
  pre.textContent = diag;
  const button = document.createElement('button');
  button.textContent = copy;
  button.onclick = () => {
    const range = document.createRange();
    range.selectNodeContents(pre);
    getSelection().removeAllRanges();
    getSelection().addRange(range);
    try { document.execCommand('copy'); } catch { /* the text stays selected to copy by hand */ }
  };
  box.append(h, p, pre, button);
  document.body.append(box);
}

window.__spoolerError = e => {
  if (startErrors.length < 20) startErrors.push(String((e && (e.stack || e.message)) || e).slice(0, 2000));
  setTimeout(showFailure, 0);
};
addEventListener('error', e => window.__spoolerError(e.error || e.message));
addEventListener('unhandledrejection', e => window.__spoolerError(e.reason));
setTimeout(showFailure, START_MS);

try {
  const packed = Uint8Array.from(atob(document.getElementById('spooler-js').textContent.trim()), c => c.charCodeAt(0));
  const script = document.createElement('script');
  script.type = 'module';
  script.textContent = new TextDecoder().decode(inflate(packed));
  document.head.append(script);
} catch (e) {
  window.__spoolerError(e);
}
