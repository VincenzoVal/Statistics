"use strict";

/* =====================================================================
   HMWK 2 - From wallet seed to Ethereum address
   Libraries (loaded in index.html):
     - ethers v6  -> global "ethers"  (word list, PBKDF2, HMAC, secp256k1, Keccak-256, SHA-2)
     - js-sha3    -> global "sha3_256" (standard SHA3-256, which ethers does not provide)
   ===================================================================== */

const HARDENED = 0x80000000;
const TEST_VECTORS = [
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about",
  "test test test test test test test test test test test junk",
];

const $ = (id) => document.getElementById(id);

/* ---------------------------------------------------------------------
   1. Small helpers
   --------------------------------------------------------------------- */

const strip0x = (h) => (h.startsWith("0x") ? h.slice(2) : h);
const hexToBytes = (h) => ethers.getBytes(h.startsWith("0x") ? h : "0x" + h);
const bytesToHex = (b) => strip0x(ethers.hexlify(b));
const mono = (s) => `<code class="hex">${s}</code>`;
const tick = () => new Promise((r) => setTimeout(r, 0));

const POP = new Uint8Array(256).map((_, i) => { let c = 0, v = i; while (v) { c += v & 1; v >>= 1; } return c; });
const hamming = (a, b) => { let d = 0; for (let i = 0; i < a.length; i++) d += POP[a[i] ^ b[i]]; return d; };
const randomBytes = (n) => { const b = new Uint8Array(n); crypto.getRandomValues(b); return b; };
const mean = (a) => a.reduce((s, v) => s + v, 0) / a.length;
const stdev = (a) => { const m = mean(a); return Math.sqrt(a.reduce((s, v) => s + (v - m) ** 2, 0) / (a.length - 1)); };
const f2 = (v) => (Number.isFinite(v) ? v.toFixed(2) : "n/a");

function pearson(a, b) {
  const ma = mean(a), mb = mean(b);
  let cov = 0, va = 0, vb = 0;
  for (let i = 0; i < a.length; i++) {
    cov += (a[i] - ma) * (b[i] - mb);
    va += (a[i] - ma) ** 2;
    vb += (b[i] - mb) ** 2;
  }
  return va === 0 || vb === 0 ? NaN : cov / Math.sqrt(va * vb);
}

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");

function readInt(id, min, max, label, errId) {
  const v = Number($(id).value);
  if (!Number.isInteger(v) || v < min || v > max) {
    showMsg(errId, `${label} must be an integer between ${min} and ${max}.`);
    return null;
  }
  hideMsg(errId);
  return v;
}

/* Hash functions compared on this page (all return a Uint8Array) */
const HASHES = [
  { name: "Keccak-256", bits: 256, fn: (m) => hexToBytes(ethers.keccak256(m)) },
  { name: "SHA3-256",   bits: 256, fn: (m) => new Uint8Array(sha3_256.array(m)) },
  { name: "SHA-256",    bits: 256, fn: (m) => hexToBytes(ethers.sha256(m)) },
  { name: "SHA-512",    bits: 512, fn: (m) => hexToBytes(ethers.sha512(m)) },
];

/* ---------------------------------------------------------------------
   2. EIP-55 checksum
   --------------------------------------------------------------------- */

// Input: 40 lowercase hex characters (no 0x). A letter becomes upper-case when
// the matching hex digit of keccak256(address as ASCII text) is >= 8.
function eip55(lower) {
  const hash = strip0x(ethers.keccak256(ethers.toUtf8Bytes(lower)));
  let out = "";
  for (let i = 0; i < 40; i++) {
    const c = lower[i];
    out += c >= "a" && parseInt(hash[i], 16) >= 8 ? c.toUpperCase() : c;
  }
  return { checksummed: out, hash };
}

function checkAddress(input) {
  const s = input.trim();
  if (!/^0x[0-9a-fA-F]{40}$/.test(s)) {
    return { status: "format", msg: "This is not an address: it must be 0x followed by 40 hexadecimal characters." };
  }
  const body = s.slice(2);
  if (body === body.toLowerCase() || body === body.toUpperCase()) {
    return { status: "nocase", msg: "Valid format, but all letters have the same case, so there is no checksum to verify." };
  }
  const expected = "0x" + eip55(body.toLowerCase()).checksummed;
  return expected === s
    ? { status: "valid", msg: "Valid EIP-55 checksum." }
    : { status: "invalid", msg: `Invalid checksum: the capitalisation does not match. The correct form would be ${expected}` };
}

function renderAddrStatus(res) {
  const cls = { valid: "success", nocase: "secondary", invalid: "danger", format: "warning" }[res.status];
  $("addrStatus").innerHTML = `<div class="alert alert-${cls} py-2 mb-0">${res.msg.replace(/&/g, "&amp;").replace(/</g, "&lt;")}</div>`;
}

/* ---------------------------------------------------------------------
   3. BIP-39 details, paths and the full pipeline
   --------------------------------------------------------------------- */

const normalizePhrase = (s) => s.trim().toLowerCase().split(/\s+/).join(" ");

function bip39Rows(mn) {
  const ent = ethers.getBytes(mn.entropy);
  const entBits = ent.length * 8;
  const csBits = entBits / 32;
  const shaHex = strip0x(ethers.sha256(ent));
  let bits = "";
  for (const b of ent) bits += b.toString(2).padStart(8, "0");
  const csFull = parseInt(shaHex.slice(0, 2), 16).toString(2).padStart(8, "0");
  const cs = csFull.slice(0, csBits);
  const all = bits + cs;
  const words = mn.phrase.split(" ");
  const rows = words.map((w, i) => {
    const chunk = all.slice(i * 11, (i + 1) * 11);
    const idx = parseInt(chunk, 2);
    const isLast = i === words.length - 1;
    const shown = isLast
      ? chunk.slice(0, 11 - csBits) + `<span class="cs">${chunk.slice(11 - csBits)}</span>`
      : chunk;
    const ok = ethers.wordlists.en.getWordIndex(w) === idx;
    return [i + 1, mono(shown), idx, `<strong>${w}</strong>`, ok ? "&#10003;" : "&#10007;"];
  });
  return { entHex: strip0x(mn.entropy), entBits, csBits, shaHex, cs, rows };
}

function parsePath(p) {
  const parts = p.trim().split("/");
  if (parts[0] !== "m") throw new Error("The path must start with \"m\", for example m/44'/60'/0'/0/0");
  const rest = parts.slice(1);
  if (rest.length === 0) throw new Error("The path needs at least one level after \"m\".");
  if (rest.length > 10) throw new Error("The path can have at most 10 levels in this demo.");
  return rest.map((s) => {
    const m = /^(\d+)(['hH])?$/.exec(s);
    if (!m) throw new Error(`Invalid path level "${s}": use a number, optionally followed by ' for hardened derivation.`);
    const n = Number(m[1]);
    if (!Number.isSafeInteger(n) || n >= HARDENED) throw new Error(`Path level ${s} is out of range (maximum 2147483647).`);
    const hardened = Boolean(m[2]);
    return { text: m[1] + (hardened ? "'" : ""), n, hardened, index: hardened ? n + HARDENED : n };
  });
}

const state = { seed: null, addrBytes: null, checksummed: null };

function runDemo() {
  hideMsg("demoError");
  try {
    const phrase = normalizePhrase($("mnemonic").value);
    $("mnemonic").value = phrase;
    if (!ethers.Mnemonic.isValidMnemonic(phrase)) {
      throw new Error("Invalid mnemonic: it must have 12, 15, 18, 21 or 24 words from the BIP-39 English list, with a correct checksum.");
    }
    const passphrase = $("passphrase").value;
    const comps = parsePath($("pathInput").value);
    const pathStr = "m/" + comps.map((c) => c.text).join("/");

    const mn = ethers.Mnemonic.fromPhrase(phrase, passphrase);
    const seed = mn.computeSeed();
    const master = ethers.HDNodeWallet.fromSeed(seed);

    /* Step 1: BIP-39 entropy, checksum, words */
    const d = bip39Rows(mn);
    $("out1").innerHTML =
      `<p class="mb-2">Entropy (${d.entBits} bits): ${mono(d.entHex)}<br>` +
      `SHA-256 of the entropy: ${mono(d.shaHex)}<br>` +
      `Checksum = first ${d.csBits} bits of that hash: <span class="cs font-monospace">${d.cs}</span></p>` +
      `<p class="small text-muted">The entropy bits followed by the checksum bits (${d.entBits + d.csBits} bits) are cut into groups of 11 bits. ` +
      `Each group is a number from 0 to 2047, the index of a word in the list. The checksum sits at the end of the last word (highlighted). ` +
      `The check mark confirms that the index matches the word in the official list.</p>` +
      table(["#", "11-bit group", "Index", "Word", "List"], d.rows, "compact");

    /* Step 2: seed */
    $("out2").innerHTML =
      `<p class="mb-2">Seed = PBKDF2-HMAC-SHA512(password = mnemonic sentence, salt = ${mono('"mnemonic" + passphrase')}, 2048 iterations, 64 bytes)</p>` +
      `<p class="mb-2">Salt used: ${mono(JSON.stringify("mnemonic" + passphrase).replace(/</g, "&lt;"))}</p>` +
      `<p class="mb-0">Seed (512 bits): ${mono(strip0x(seed))}</p>` +
      `<p class="small text-muted mt-2 mb-0">PBKDF2 repeats HMAC-SHA512 2048 times. This stretching makes guessing a weak mnemonic slower, and the passphrase changes the whole seed.</p>`;

    /* Step 3: BIP-32 master key and path */
    const m44 = /^m\/44'\/(\d+)'\/(\d+)'\/(\d+)\/(\d+)$/.exec(pathStr);
    $("outPath").innerHTML = m44
      ? `<p class="mb-1">This path follows the BIP-44 structure <code>m / purpose' / coin_type' / account' / change / address_index</code>:</p>` +
        table(["Level", "Value", "Meaning"], [
          ["purpose", "44'", "BIP-44 (hardened)"],
          ["coin_type", `${m44[1]}'`, m44[1] === "60" ? "Ethereum (registered coin type 60)" : "Coin type from the SLIP-44 registry (Ethereum is 60)"],
          ["account", `${m44[2]}'`, "Account number (hardened)"],
          ["change", m44[3], m44[3] === "0" ? "External chain (0), the one Ethereum wallets use" : "Internal / change chain (1 in Bitcoin-style wallets)"],
          ["address_index", m44[4], "Index of the address within the account"],
        ], "compact")
      : `<p class="mb-0">This path does not have the five BIP-44 levels, but it is still a valid BIP-32 path.</p>`;

    const levels = [{ label: "m (master)", kind: "master", node: master }];
    let node = master;
    for (const c of comps) {
      node = node.deriveChild(c.index);
      levels.push({ label: c.text, kind: c.hardened ? "hardened" : "normal", node, index: c.index });
    }
    let pathAcc = "m";
    $("out3").innerHTML =
      `<p class="mb-2">Master key and chain code = the two halves of HMAC-SHA512(key = ${mono('"Bitcoin seed"')}, data = seed). ` +
      `Each child key is computed from HMAC-SHA512(parent chain code, parent key or public key, child index). ` +
      `A hardened index is the number plus 2<sup>31</sup> (2147483648).</p>` +
      table(["Level", "Path so far", "Type", "Index used", "Private key", "Chain code"],
        levels.map((l, i) => {
          if (i > 0) pathAcc += "/" + l.label;
          return [l.label, mono(pathAcc), l.kind, i === 0 ? "-" : l.index, mono(strip0x(l.node.privateKey)), mono(strip0x(l.node.chainCode))];
        }), "compact");

    /* Step 4: secp256k1 */
    const priv = node.privateKey;
    const unc = ethers.SigningKey.computePublicKey(priv, false);
    const comp = ethers.SigningKey.computePublicKey(priv, true);
    const X = unc.slice(4, 68), Y = unc.slice(68);
    $("out4").innerHTML =
      `<p class="mb-2">Private key k (256 bits): ${mono(strip0x(priv))}</p>` +
      `<p class="mb-2">Public key Q = kG on secp256k1 (same operation as Homework 1, with 256-bit numbers):</p>` +
      `<p class="mb-1">x = ${mono(X)}</p><p class="mb-1">y = ${mono(Y)}</p>` +
      `<p class="small text-muted mb-0">Uncompressed form: 04 &#8214; x &#8214; y (65 bytes). Compressed form: ${mono(strip0x(comp))} ` +
      `(prefix 02 or 03 shows the parity of y, followed by x). Ethereum hashes only x &#8214; y, without the 04 prefix.</p>`;

    /* Step 5: Keccak-256 */
    const digest = strip0x(ethers.keccak256(hexToBytes(X + Y)));
    const addrLower = digest.slice(-40);
    $("out5").innerHTML =
      `<p class="mb-2">Keccak-256(x &#8214; y), 64 bytes in, 32 bytes out:</p>` +
      `<p class="mb-2"><code class="hex"><span class="muted-hex">${digest.slice(0, 24)}</span><span class="kept">${digest.slice(24)}</span></code></p>` +
      `<p class="small text-muted mb-2">The first 12 bytes (grey) are discarded; the last 20 bytes (green) are the address.</p>` +
      `<p class="mb-0">Address (lower case, no checksum): ${mono("0x" + addrLower)}</p>`;

    /* Step 6: EIP-55 */
    const e = eip55(addrLower);
    let rule = "", res = "";
    for (let i = 0; i < 40; i++) {
      const c = addrLower[i];
      const isLetter = c >= "a";
      const up = isLetter && parseInt(e.hash[i], 16) >= 8;
      rule += !isLetter ? "-" : up ? "U" : "l";
      res += up ? `<span class="up">${c.toUpperCase()}</span>` : c;
    }
    const finalAddr = "0x" + e.checksummed;
    const ethersAddr = node.address;
    $("out6").innerHTML =
      `<pre class="align">address (lowercase) : ${addrLower}\n` +
      `keccak256(address)   : ${e.hash.slice(0, 40)}   (first 40 hex digits)\n` +
      `rule                 : ${rule}\n` +
      `checksummed          : ${res}</pre>` +
      `<p class="small text-muted">Rule: <b>U</b> = letter made upper-case because the hash digit is 8 or more; <b>l</b> = letter stays lower-case; <b>-</b> = a digit, which has no case.</p>` +
      `<p class="mb-1">Checksummed Ethereum address:</p><div class="final-address mb-2">${finalAddr}</div>` +
      (finalAddr === ethersAddr
        ? `<div class="small text-success">&#10003; Identical to the address computed by ethers.js for the same mnemonic and path.</div>`
        : `<div class="small text-danger">&#10007; Different from the address computed by ethers.js (${ethersAddr}): something is wrong.</div>`);

    /* Five addresses of the standard account */
    const acct = master.derivePath("44'/60'/0'/0");
    const many = [];
    for (let i = 0; i < 5; i++) many.push([i, mono(`m/44'/60'/0'/0/${i}`), mono(acct.deriveChild(i).address)]);
    $("outMany").innerHTML = table(["address_index", "Path", "Address"], many, "compact");

    state.seed = seed;
    state.addrBytes = hexToBytes(addrLower);
    state.checksummed = finalAddr;
    $("addrInput").value = finalAddr;
    renderAddrStatus(checkAddress(finalAddr));
  } catch (err) {
    showMsg("demoError", err.message);
  }
}

function generateMnemonic(bytesLen) {
  $("mnemonic").value = ethers.Mnemonic.fromEntropy(ethers.randomBytes(bytesLen)).phrase;
  runDemo();
}

function loadVector(i) {
  $("mnemonic").value = TEST_VECTORS[i];
  $("passphrase").value = "";
  $("pathInput").value = "m/44'/60'/0'/0/0";
  runDemo();
}

function introduceTypo() {
  const base = state.checksummed || $("addrInput").value.trim();
  if (!/^0x[0-9a-fA-F]{40}$/.test(base)) { renderAddrStatus(checkAddress(base)); return; }
  const pool = "0123456789abcdefABCDEF";
  const pos = 2 + Math.floor(Math.random() * 40);
  let c;
  do { c = pool[Math.floor(Math.random() * pool.length)]; } while (c === base[pos]);
  const typo = base.slice(0, pos) + c + base.slice(pos + 1);
  $("addrInput").value = typo;
  const r = checkAddress(typo);
  renderAddrStatus(r);
}

/* ---------------------------------------------------------------------
   4. Hash comparison widget
   --------------------------------------------------------------------- */

function runHashCompare() {
  hideMsg("hashErr");
  let bytes;
  try {
    bytes = $("hashHex").checked ? hexToBytes($("hashInput").value.trim()) : ethers.toUtf8Bytes($("hashInput").value);
  } catch (e) {
    showMsg("hashErr", "Invalid hexadecimal input (use an even number of hex digits).");
    return;
  }
  const out = HASHES.map((h) => [h.name, h.bits, mono(bytesToHex(h.fn(bytes)))]);
  const dist = hamming(HASHES[0].fn(bytes), HASHES[1].fn(bytes));
  $("hashOut").innerHTML = table(["Function", "Bits", "Digest"], out, "compact") +
    `<p class="small text-muted mt-2 mb-0">Keccak-256 and SHA3-256 differ in ${dist} of 256 bits for this input ` +
    `(about half is expected for unrelated outputs), even though they use the same permutation.</p>`;
}

/* ---------------------------------------------------------------------
   5. Charts (canvas)
   --------------------------------------------------------------------- */

function drawBars(canvas, values, o = {}) {
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
  const L = 52, R = 14, T = 34, B = 44;
  const pw = W - L - R, ph = H - T - B;
  const ymin = o.ymin ?? 0;
  const ymax = o.ymax ?? Math.max(1e-9, ...values, ...(o.curve || [])) * 1.12;
  const y = (v) => T + ph - ((v - ymin) / (ymax - ymin)) * ph;
  const bw = pw / values.length;
  const fmt = o.fmt || ((v) => String(Math.round(v * 100) / 100));

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, W, H);

  ctx.fillStyle = "#212529";
  ctx.font = "bold 13px sans-serif";
  ctx.textAlign = "left";
  ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);

  // axes and y ticks
  ctx.strokeStyle = "#adb5bd";
  ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + ph); ctx.lineTo(W - R, T + ph); ctx.stroke();
  ctx.font = "10px sans-serif";
  ctx.fillStyle = "#6c757d";
  ctx.textAlign = "right";
  for (let i = 0; i <= 4; i++) {
    const v = ymin + ((ymax - ymin) * i) / 4;
    ctx.fillText(fmt(v), L - 5, y(v) + 3);
    if (i > 0) { ctx.strokeStyle = "#f1f3f5"; ctx.beginPath(); ctx.moveTo(L, y(v)); ctx.lineTo(W - R, y(v)); ctx.stroke(); }
  }

  // bars
  ctx.fillStyle = o.color || "#2c3e50";
  values.forEach((v, i) => {
    const top = y(Math.max(v, ymin)), base = y(ymin);
    ctx.fillRect(L + i * bw + bw * 0.1, top, Math.max(1, bw * 0.8), Math.max(0, base - top));
  });

  // expected curve
  if (o.curve) {
    ctx.strokeStyle = "#e74c3c";
    ctx.lineWidth = 2;
    ctx.beginPath();
    o.curve.forEach((v, i) => {
      const px = L + i * bw + bw / 2;
      i === 0 ? ctx.moveTo(px, y(v)) : ctx.lineTo(px, y(v));
    });
    ctx.stroke();
  }

  // reference lines
  const dashed = (v, color) => {
    ctx.strokeStyle = color; ctx.lineWidth = 1.5; ctx.setLineDash([5, 4]);
    ctx.beginPath(); ctx.moveTo(L, y(v)); ctx.lineTo(W - R, y(v)); ctx.stroke(); ctx.setLineDash([]);
  };
  if (o.hline !== undefined) dashed(o.hline, "#e74c3c");
  if (o.band !== undefined) { dashed(o.hline + o.band, "#f39c12"); dashed(o.hline - o.band, "#f39c12"); }

  // x labels
  ctx.fillStyle = "#6c757d";
  ctx.textAlign = "center";
  const every = o.labelEvery || 1;
  for (let i = 0; i < values.length; i += every) {
    ctx.fillText(String((o.xStart || 0) + i), L + i * bw + bw / 2, T + ph + 14);
  }
  if (o.xTitle) ctx.fillText(o.xTitle, L + pw / 2, H - 8);
}

const normalPdf = (x, mu, s) => Math.exp(-0.5 * ((x - mu) / s) ** 2) / (s * Math.sqrt(2 * Math.PI));

const logFact = [0];
for (let i = 1; i <= 200; i++) logFact[i] = logFact[i - 1] + Math.log(i);
const binomPmf = (n, k, p) =>
  Math.exp(logFact[n] - logFact[k] - logFact[n - k] + k * Math.log(p) + (n - k) * Math.log(1 - p));

/* Bit-balance statistics for a set of equally long byte arrays */
function bitStats(samples, nBits) {
  const ones = new Float64Array(nBits);
  const byteCnt = new Float64Array(256);
  for (const d of samples) {
    for (let j = 0; j < d.length; j++) {
      byteCnt[d[j]]++;
      for (let b = 0; b < 8; b++) ones[j * 8 + b] += (d[j] >> b) & 1;
    }
  }
  const N = samples.length;
  const p = Array.from(ones, (c) => c / N);
  const sigma = 0.5 / Math.sqrt(N);
  const worstZ = Math.max(...p.map((v) => Math.abs(v - 0.5) / sigma));
  const E = (N * (nBits / 8)) / 256;
  let chi = 0;
  for (const c of byteCnt) chi += (c - E) ** 2 / E;
  return { p, sigma, worstZ, chi };
}

/* ---------------------------------------------------------------------
   6. Experiment A: hash functions
   --------------------------------------------------------------------- */

const hashRes = { results: [], M: 0 };

async function runHashStats() {
  const M = readInt("hashTrials", 100, 20000, "The number of messages", "hashStatErr");
  if (M === null) return;
  $("btnHashStats").disabled = true;
  $("hashProgress").textContent = "Running...";
  await tick();

  const results = [];
  for (const h of HASHES) {
    // Avalanche on random 32-byte messages
    const dist = new Array(M);
    for (let t = 0; t < M; t++) {
      const m = randomBytes(32);
      const m2 = m.slice();
      const bit = Math.floor(Math.random() * 256);
      m2[bit >> 3] ^= 1 << (bit & 7);
      dist[t] = hamming(h.fn(m), h.fn(m2));
    }
    // Uniformity on the structured inputs 0, 1, 2, ...
    const samples = [], firstByte = [], idx = [];
    for (let i = 0; i < M; i++) {
      const msg = new Uint8Array(8);
      new DataView(msg.buffer).setUint32(4, i);
      const d = h.fn(msg);
      samples.push(d); firstByte.push(d[0]); idx.push(i);
    }
    const bs = bitStats(samples, h.bits);
    const r = pearson(idx, firstByte);
    results.push({ name: h.name, bits: h.bits, dist, bs, r });
    $("hashProgress").textContent = `Done: ${h.name}`;
    await tick();
  }
  hashRes.results = results;
  hashRes.M = M;

  $("hashTable").innerHTML = table(
    ["Function", "Digest bits", "Avalanche: mean changed bits", "Expected", "Std dev (observed / expected)", "Worst bit (z)", "Byte chi-square (df = 255)", "Correlation r(i, byte 0)"],
    results.map((x) => [
      `<strong>${x.name}</strong>`, x.bits,
      `${f2(mean(x.dist))} (${(100 * mean(x.dist) / x.bits).toFixed(1)} %)`,
      f2(x.bits / 2),
      `${f2(stdev(x.dist))} / ${f2(Math.sqrt(x.bits) / 2)}`,
      f2(x.bs.worstZ), f2(x.bs.chi), f2(x.r),
    ]), "compact");

  const sel = $("hashFnSelect");
  if (!sel.options.length) {
    sel.innerHTML = HASHES.map((h) => `<option>${h.name}</option>`).join("");
  }
  renderHashCharts();
  $("hashProgress").textContent = `Finished (${M} messages per function).`;
  $("btnHashStats").disabled = false;
}

function renderHashCharts() {
  const x = hashRes.results.find((r) => r.name === $("hashFnSelect").value) || hashRes.results[0];
  if (!x) return;
  const mu = x.bits / 2, s = Math.sqrt(x.bits) / 2;
  const lo = Math.floor(mu - 5 * s), hi = Math.ceil(mu + 5 * s);
  const bins = new Array(hi - lo + 1).fill(0);
  for (const d of x.dist) { const k = d - lo; if (k >= 0 && k < bins.length) bins[k]++; }
  drawBars($("cvHist"), bins, {
    title: `${x.name}: changed bits after a 1-bit input change`,
    xStart: lo, labelEvery: Math.ceil(bins.length / 10), xTitle: "number of changed output bits", fmt: (v) => String(Math.round(v)),
    curve: bins.map((_, i) => hashRes.M * normalPdf(lo + i, mu, s)),
  });
  drawBars($("cvBits"), x.bs.p, {
    title: `${x.name}: fraction of 1s per output bit (inputs 0, 1, 2, ...)`,
    ymin: 0.4, ymax: 0.6, hline: 0.5, band: 3 * x.bs.sigma, color: "#2c3e50",
    labelEvery: x.bits === 512 ? 64 : 32, xTitle: "output bit position", fmt: (v) => v.toFixed(2),
  });
}

/* ---------------------------------------------------------------------
   7. Experiment B: the whole pipeline
   --------------------------------------------------------------------- */

function pipelineFromEntropy(entropy) {
  const mn = ethers.Mnemonic.fromEntropy(entropy);
  const seed = mn.computeSeed();
  const addr = ethers.HDNodeWallet.fromSeed(seed).derivePath("44'/60'/0'/0/0").address;
  return { words: mn.phrase.split(" "), seed: hexToBytes(seed), addr: hexToBytes(addr) };
}

async function runPipelineStats() {
  const N = readInt("idxTrials", 50, 5000, "The number of indices", "pipeStatErr");
  const T = N === null ? null : readInt("pipeTrials", 5, 200, "The number of entropy flips", "pipeStatErr");
  if (N === null || T === null) return;
  $("btnPipeStats").disabled = true;
  await tick();

  // B1: sequential indices with the seed of the demo
  const seed = state.seed || ethers.Mnemonic.fromPhrase(TEST_VECTORS[0]).computeSeed();
  const acct = ethers.HDNodeWallet.fromSeed(seed).derivePath("44'/60'/0'/0");
  const addrs = [], dists = [];
  for (let i = 0; i < N; i++) {
    const a = hexToBytes(acct.deriveChild(i).address);
    if (i > 0) dists.push(hamming(addrs[i - 1], a));
    addrs.push(a);
    if (i % 25 === 24) { $("pipeProgress").textContent = `Indices: ${i + 1} / ${N}`; await tick(); }
  }
  const bs = bitStats(addrs, 160);
  $("pipeTable1").innerHTML = table(
    ["Experiment", "Result", "Expected for a random function"],
    [
      [`Consecutive addresses (i and i+1), ${N} addresses`, `${f2(mean(dists))} changed bits (${(100 * mean(dists) / 160).toFixed(1)} %), std dev ${f2(stdev(dists))}`, "80 changed bits (50 %), std dev 6.32"],
      ["Worst of the 160 address bits (z)", f2(bs.worstZ), "up to about 3.5"],
      ["Byte frequencies, chi-square (df = 255)", f2(bs.chi), "about 255 (std dev 22.6)"],
    ], "compact");
  const lo = 80 - 30, hi = 80 + 30;
  const bins = new Array(hi - lo + 1).fill(0);
  for (const d of dists) { const k = d - lo; if (k >= 0 && k < bins.length) bins[k]++; }
  drawBars($("cvPipeDist"), bins, {
    title: "Consecutive addresses: changed bits (of 160)", xStart: lo, labelEvery: 6, xTitle: "number of changed address bits", fmt: (v) => String(Math.round(v)),
    curve: bins.map((_, i) => dists.length * normalPdf(lo + i, 80, Math.sqrt(160) / 2)),
  });
  drawBars($("cvPipeBits"), bs.p, {
    title: "Address bits: fraction of 1s (sequential indices)", ymin: 0.4, ymax: 0.6, hline: 0.5, band: 3 * bs.sigma,
    labelEvery: 20, xTitle: "address bit position", fmt: (v) => v.toFixed(2),
  });

  // B2: avalanche from the entropy
  const wordCh = [], seedCh = [], addrCh = [];
  for (let t = 0; t < T; t++) {
    const e1 = randomBytes(16);
    const e2 = e1.slice();
    const bit = Math.floor(Math.random() * 128);
    e2[bit >> 3] ^= 1 << (bit & 7);
    const a = pipelineFromEntropy(e1), b = pipelineFromEntropy(e2);
    wordCh.push(a.words.filter((w, i) => w !== b.words[i]).length);
    seedCh.push(hamming(a.seed, b.seed));
    addrCh.push(hamming(a.addr, b.addr));
    $("pipeProgress").textContent = `Entropy flips: ${t + 1} / ${T}`;
    await tick();
  }
  $("pipeTable2").innerHTML = table(
    ["After flipping 1 bit of a 128-bit entropy", "Mean changed (observed)", "Std dev (observed)", "Expected for a random function"],
    [
      ["Words of the 12-word mnemonic (encoding)", f2(mean(wordCh)), f2(stdev(wordCh)), "12 words (almost all)"],
      ["Bits of the 512-bit seed (PBKDF2)", f2(mean(seedCh)), f2(stdev(seedCh)), "256 bits, std dev 11.3"],
      ["Bits of the 160-bit address (full pipeline)", f2(mean(addrCh)), f2(stdev(addrCh)), "80 bits, std dev 6.3"],
    ], "compact");
  $("pipeProgress").textContent = "Finished.";
  $("btnPipeStats").disabled = false;
}

/* ---------------------------------------------------------------------
   8. Experiment C: EIP-55 checksum
   --------------------------------------------------------------------- */

async function runChecksumStats() {
  const N = readInt("csTrials", 1000, 200000, "The number of addresses", "csStatErr");
  if (N === null) return;
  $("btnCsStats").disabled = true;
  await tick();

  const letterCount = new Array(41).fill(0);
  let letters = 0, upper = 0, passed = 0, unchecked = 0, crossOk = true;
  const pool = "0123456789abcdefABCDEF";
  for (let i = 0; i < N; i++) {
    const lower = bytesToHex(randomBytes(20));
    const e = eip55(lower);
    if (i < 30 && "0x" + e.checksummed !== ethers.getAddress("0x" + lower)) crossOk = false;
    const L = (lower.match(/[a-f]/g) || []).length;
    letterCount[L]++;
    letters += L;
    upper += (e.checksummed.match(/[A-F]/g) || []).length;

    // one random wrong character
    const pos = Math.floor(Math.random() * 40);
    let c;
    do { c = pool[Math.floor(Math.random() * pool.length)]; } while (c === e.checksummed[pos]);
    const typed = "0x" + e.checksummed.slice(0, pos) + c + e.checksummed.slice(pos + 1);
    const st = checkAddress(typed).status;
    if (st === "valid") passed++;
    else if (st === "nocase") unchecked++;

    if (i % 4000 === 3999) { $("csProgress").textContent = `${i + 1} / ${N}`; await tick(); }
  }
  const expRate = Math.pow(13 / 16, 40);
  drawBars($("cvLetters"), letterCount, {
    title: "Number of letters (check bits) per address", xStart: 0, labelEvery: 4, xTitle: "letters among the 40 hex characters", fmt: (v) => String(Math.round(v)),
    curve: letterCount.map((_, k) => N * binomPmf(40, k, 6 / 16)),
  });
  $("csTable").innerHTML = table(
    ["Measurement", "Result", "Expected"],
    [
      ["Mean letters (check bits) per address", f2(letters / N), "15.00"],
      ["Share of letters that are upper-case", `${(100 * upper / letters).toFixed(1)} %`, "50 %"],
      [`Typos that still pass the checksum (out of ${N})`, `${passed} (${(100 * passed / N).toFixed(3)} %)`, `about ${(N * expRate).toFixed(1)} (${(100 * expRate).toFixed(4)} %)`],
      ["Typos that give an all-lower-case or all-upper-case address (nothing to check)", `${unchecked} (${(100 * unchecked / N).toFixed(3)} %)`, "about 0.04 %"],
      ["Own EIP-55 code equals ethers.js on 30 addresses", crossOk ? "yes" : "NO", "yes"],
    ], "compact");
  $("csProgress").textContent = "Finished.";
  $("btnCsStats").disabled = false;
}

/* ---------------------------------------------------------------------
   9. Start-up
   --------------------------------------------------------------------- */

async function init() {
  if (typeof ethers === "undefined" || typeof sha3_256 === "undefined") {
    showMsg("jsError", "The cryptographic libraries (ethers.js, js-sha3) could not be loaded from the CDN. Check your internet connection and reload the page.");
    return;
  }
  $("btnDerive").addEventListener("click", runDemo);
  $("btnGen12").addEventListener("click", () => generateMnemonic(16));
  $("btnGen24").addEventListener("click", () => generateMnemonic(32));
  $("btnVec1").addEventListener("click", () => loadVector(0));
  $("btnVec2").addEventListener("click", () => loadVector(1));
  $("btnCheck").addEventListener("click", () => renderAddrStatus(checkAddress($("addrInput").value)));
  $("btnTypo").addEventListener("click", introduceTypo);
  $("hashInput").addEventListener("input", runHashCompare);
  $("hashHex").addEventListener("change", runHashCompare);
  $("btnHashStats").addEventListener("click", runHashStats);
  $("hashFnSelect").addEventListener("change", renderHashCharts);
  $("btnPipeStats").addEventListener("click", runPipelineStats);
  $("btnCsStats").addEventListener("click", runChecksumStats);

  loadVector(0);
  runHashCompare();
  try {
    await runHashStats();
    await runPipelineStats();
    await runChecksumStats();
  } catch (err) {
    showMsg("jsError", "Error while running the experiments: " + err.message);
  }
}

document.addEventListener("DOMContentLoaded", init);
