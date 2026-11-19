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

try {
  const packed = Uint8Array.from(atob(document.getElementById('spooler-js').textContent.trim()), c => c.charCodeAt(0));
  const script = document.createElement('script');
  script.type = 'module';
  script.textContent = new TextDecoder().decode(inflate(packed));
  document.head.append(script);
} catch (e) {
  document.body.textContent = 'Spooler could not start its page: ' + e;
}
