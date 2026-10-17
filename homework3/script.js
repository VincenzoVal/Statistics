"use strict";

/* =====================================================================
   HMWK 3 - Caesar cipher and toy elliptic-curve encryption (EC ElGamal)
   Pure JavaScript, no external libraries (BigInt for the 256-bit arithmetic).
   ===================================================================== */

const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");
const f1 = (v) => (Number.isFinite(v) ? v.toFixed(1) : "n/a");
const f3 = (v) => (Number.isFinite(v) ? v.toFixed(3) : "n/a");
const f4 = (v) => (Number.isFinite(v) ? v.toFixed(4) : "n/a");
const sum = (a) => a.reduce((s, v) => s + v, 0);

function readInt(id, min, max, label, errId) {
  const v = Number($(id).value);
  if (!Number.isInteger(v) || v < min || v > max) { showMsg(errId, `${label} must be an integer between ${min} and ${max}.`); return null; }
  hideMsg(errId);
  return v;
}

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

/* ---------------------------------------------------------------------
   1. secp256k1 arithmetic with BigInt
   Affine points are {x, y}; the point at infinity is null.
   Jacobian points are {X, Y, Z} (Z = 0 is the point at infinity); they avoid
   one modular inversion per addition, which makes long computations fast.
   --------------------------------------------------------------------- */

const P = 2n ** 256n - 2n ** 32n - 977n;
const N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
const G = {
  x: 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n,
  y: 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8n,
};
const INF_J = () => ({ X: 0n, Y: 1n, Z: 0n });

const mod = (a) => { const r = a % P; return r >= 0n ? r : r + P; };

function inv(a) { // extended Euclid
  let t = 0n, newT = 1n, r = P, newR = mod(a);
  while (newR !== 0n) {
    const q = r / newR;
    [t, newT] = [newT, t - q * newT];
    [r, newR] = [newR, r - q * newR];
  }
  return t < 0n ? t + P : t;
}

function addAffine(A, B) {
  if (A === null) return B;
  if (B === null) return A;
  if (A.x === B.x) {
    if (mod(A.y + B.y) === 0n) return null;                       // A = -B
    const l = mod(3n * A.x * A.x * inv(2n * A.y));                // doubling
    const x = mod(l * l - 2n * A.x);
    return { x, y: mod(l * (A.x - x) - A.y) };
  }
  const l = mod((B.y - A.y) * inv(B.x - A.x));
  const x = mod(l * l - A.x - B.x);
  return { x, y: mod(l * (A.x - x) - A.y) };
}
const negAffine = (A) => (A === null ? null : { x: A.x, y: mod(-A.y) });
const samePt = (A, B) => (A === null || B === null ? A === B : A.x === B.x && A.y === B.y);

function dblJ(A) {
  if (A.Z === 0n || A.Y === 0n) return INF_J();
  const Y2 = mod(A.Y * A.Y), S = mod(4n * A.X * Y2), M = mod(3n * A.X * A.X);
  const X3 = mod(M * M - 2n * S);
  return { X: X3, Y: mod(M * (S - X3) - 8n * Y2 * Y2), Z: mod(2n * A.Y * A.Z) };
}

function addMixed(A, B) { // Jacobian + affine (B not null)
  if (A.Z === 0n) return { X: B.x, Y: B.y, Z: 1n };
  const Z2 = mod(A.Z * A.Z), U2 = mod(B.x * Z2), S2 = mod(B.y * Z2 * A.Z);
  const H = mod(U2 - A.X), R = mod(S2 - A.Y);
  if (H === 0n) return R === 0n ? dblJ(A) : INF_J();
  const H2 = mod(H * H), H3 = mod(H * H2), V = mod(A.X * H2);
  const X3 = mod(R * R - H3 - 2n * V);
  return { X: X3, Y: mod(R * (V - X3) - A.Y * H3), Z: mod(A.Z * H) };
}

function toAffine(A) {
  if (A.Z === 0n) return null;
  const zi = inv(A.Z), zi2 = mod(zi * zi);
  return { x: mod(A.X * zi2), y: mod(A.Y * zi2 * zi) };
}

// Does the Jacobian point A equal the affine point Q? (no inversion needed)
function equalsJ(A, Q) {
  if (A.Z === 0n) return false;
  const Z2 = mod(A.Z * A.Z);
  return A.X === mod(Q.x * Z2) && A.Y === mod(Q.y * Z2 * A.Z);
}

// kB by double-and-add (k is a BigInt)
function mulBasic(k, B) {
  let R = INF_J();
  for (let i = k.toString(2).length - 1; i >= 0; i--) {
    R = dblJ(R);
    if ((k >> BigInt(i)) & 1n) R = addMixed(R, B);
  }
  return toAffine(R);
}

// Table of 2^i * B (i = 0..255): then kB needs only additions
function pointTable(B) {
  const t = [];
  let c = B;
  for (let i = 0; i < 256; i++) { t.push(c); c = addAffine(c, c); }
  return t;
}
function mulTable(t, k) {
  let R = INF_J();
  for (let i = 0; k > 0n; i++, k >>= 1n) if (k & 1n) R = addMixed(R, t[i]);
  return toAffine(R);
}

/* ---------------------------------------------------------------------
   2. Display helpers for big numbers and points
   --------------------------------------------------------------------- */

const hex64 = (b) => b.toString(16).padStart(64, "0");
const pt = (b) => (b === null ? "O" : `<span class="pt" title="0x${hex64(b)}">0x${hex64(b).slice(0, 8)}&hellip;${hex64(b).slice(-6)}</span>`);
const ptx = (A) => (A === null ? "O" : pt(A.x));

function randScalar() { // random integer in [1, n - 1]
  const b = new Uint8Array(32);
  crypto.getRandomValues(b);
  let v = 0n;
  for (const x of b) v = (v << 8n) | BigInt(x);
  return (v % (N - 1n)) + 1n;
}
function randKey(bits) {
  const v = crypto.getRandomValues(new Uint32Array(1))[0];
  const k = bits === 32 ? v : v % 2 ** bits;
  return k === 0 ? 1 : k;
}

/* ---------------------------------------------------------------------
   3. Part A: toy EC ElGamal
   --------------------------------------------------------------------- */

const st = { bits: 16, k: 1n, Q: null, tblG: null, tblQ: null, tblM: [], lookup: new Map(), cipher: null, caesarCt: "", stop: false, rates: null };

function initCurveTables() {
  st.tblG = pointTable(G);
  st.tblM = [null];
  for (let m = 1; m < 256; m++) st.tblM[m] = addAffine(st.tblM[m - 1], G);   // M_m = mG
  st.lookup = new Map();
  for (let m = 1; m < 256; m++) st.lookup.set(st.tblM[m].x, [m, st.tblM[m].y]);
}

function lookupPoint(M) { // returns m with mG = M, or -1
  if (M === null) return 0;
  const e = st.lookup.get(M.x);
  return e && e[1] === M.y ? e[0] : -1;
}

function setKey(k) {
  st.k = BigInt(k);
  st.Q = mulTable(st.tblG, st.k);
  st.tblQ = pointTable(st.Q);
  st.cipher = null;
  $("kInput").value = String(k);
  $("keyInfo").innerHTML = table(["Parameter", "Value"], [
    ["p (field prime)", `<code class="hex">0x${hex64(P)}</code>`],
    ["n (order of G)", `<code class="hex">0x${hex64(N)}</code>`],
    ["G (base point), x", `<code class="hex">0x${hex64(G.x)}</code>`],
    ["G (base point), y", `<code class="hex">0x${hex64(G.y)}</code>`],
    [`Private key k (secret), range 1 to 2<sup>${st.bits}</sup> &minus; 1`, `<code class="hex">${k}</code> (0x${k.toString(16)})`],
    ["Public key Q = kG, x", `<code class="hex">0x${hex64(st.Q.x)}</code>`],
    ["Public key Q = kG, y", `<code class="hex">0x${hex64(st.Q.y)}</code>`],
  ], "compact");
  $("eccEncOut").innerHTML = "";
  $("eccDecOut").innerHTML = "";
  $("attackOut").innerHTML = "";
  $("reuseOut").innerHTML = "";
  $("attackProgress").textContent = "";
}

function generateKeys() {
  st.bits = Number($("keyBits").value);
  hideMsg("eccError");
  setKey(randKey(st.bits));
}

function onKeyEdited() {
  const bits = Number($("keyBits").value);
  const k = Number($("kInput").value);
  if (!Number.isInteger(k) || k < 1 || k >= 2 ** bits) {
    showMsg("eccError", `The private key must be an integer between 1 and 2^${bits} - 1 (the range selected above).`);
    return;
  }
  hideMsg("eccError");
  st.bits = bits;
  setKey(k);
}

function readMessage() {
  const msg = $("message").value;
  if (msg.length === 0 || msg.length > 64) { showMsg("eccError", "The message must have between 1 and 64 characters."); return null; }
  for (const ch of msg.split("")) {
    if (ch.charCodeAt(0) > 255) { showMsg("eccError", `The character "${ch}" has a code above 255: the toy scheme encodes one byte per character.`); return null; }
  }
  hideMsg("eccError");
  return msg;
}

function encryptEcc() {
  const msg = readMessage();
  if (msg === null) return;
  const reuse = $("reuseR").checked;
  const r0 = randScalar();
  const items = [];
  for (const ch of msg.split("")) {
    const m = ch.charCodeAt(0);
    const r = reuse ? r0 : randScalar();
    const R = mulTable(st.tblG, r);          // R = rG
    const S = mulTable(st.tblQ, r);          // S = rQ (shared secret)
    const C = addAffine(st.tblM[m], S);      // C = mG + rQ
    items.push({ ch, m, r, R, C });
  }
  st.cipher = { items, reuse, msg };
  $("eccEncOut").innerHTML =
    `<p class="small text-muted mb-2">Each character c has code m; M = mG; a ${reuse ? "<strong>single</strong> r is used for all characters (insecure)" : "fresh random r is chosen for each character"}; R = rG; C = M + rQ. The ciphertext of each character is the pair (R, C). Only x coordinates are shown (hover for the full value).</p>` +
    table(["#", "Char", "m", "M = mG", "r", "R = rG", "C = M + rQ"],
      items.map((it, i) => [i + 1, `<span class="pt">${it.ch === " " ? "&#9251;" : esc(it.ch)}</span>`, it.m, ptx(st.tblM[it.m]), pt(it.r), ptx(it.R), ptx(it.C)]), "compact") +
    `<p class="small text-muted mt-2 mb-0">Ciphertext size: ${items.length} characters become ${items.length * 2} points (about ${items.length * 128} bytes uncompressed).</p>`;
  $("eccDecOut").innerHTML = "";
}

function decryptWith(k, items) {
  const out = [];
  for (const it of items) {
    const S = mulBasic(k, it.R);                    // S = kR = rQ
    const M = addAffine(it.C, negAffine(S));        // M = C - S
    out.push({ S, M, m: lookupPoint(M) });
  }
  return out;
}

function decryptEcc() {
  if (!st.cipher) { showMsg("eccError", "Encrypt a message first."); return; }
  hideMsg("eccError");
  const { items, msg } = st.cipher;
  const dec = decryptWith(st.k, items);
  const text = dec.map((d) => (d.m >= 0 ? String.fromCharCode(d.m) : "?")).join("");
  $("eccDecOut").innerHTML =
    `<p class="small text-muted mb-2">The receiver computes S = kR (equal to rQ), M = C &minus; S, and looks up m such that mG = M in the table of the 256 points 0G, 1G, ..., 255G.</p>` +
    table(["#", "S = kR", "M = C &minus; S", "m", "Char"],
      dec.map((d, i) => [i + 1, ptx(d.S), ptx(d.M), d.m, `<span class="pt">${d.m === 32 ? "&#9251;" : d.m >= 0 ? esc(String.fromCharCode(d.m)) : "?"}</span>`]), "compact") +
    `<p class="mt-2 mb-1">Recovered message:</p><pre class="out">${esc(text)}</pre>` +
    (text === msg ? `<div class="small text-success">&#10003; Identical to the original message.</div>` : `<div class="small text-danger">&#10007; Different from the original message.</div>`);
}

/* ---------------------------------------------------------------------
   4. Part B: Caesar cipher
   --------------------------------------------------------------------- */

function caesar(text, shift) {
  return text.replace(/[A-Za-z]/g, (c) => {
    const base = c <= "Z" ? 65 : 97;
    return String.fromCharCode((((c.charCodeAt(0) - base + shift) % 26) + 26) % 26 + base);
  });
}
const lettersOnly = (s) => s.toUpperCase().replace(/[^A-Z]/g, "");
const shiftLetters = (letters, s) => {
  let out = "";
  for (let i = 0; i < letters.length; i++) out += String.fromCharCode(((letters.charCodeAt(i) - 65 + s + 26) % 26) + 65);
  return out;
};

function runCaesar() {
  const msg = $("message").value;
  const s = Number($("caesarKey").value);
  const enc = caesar(msg, s), dec = caesar(enc, -s);
  st.caesarCt = enc;
  const A = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  const shifted = A.slice(s) + A.slice(0, s);
  $("caesarOut").innerHTML =
    `<p class="small text-muted mb-1">Alphabet mapping for s = ${s}:</p>` +
    `<div class="mapping mb-3">Plain : ${A.split("").join(" ")}\nCipher: ${shifted.split("").join(" ")}</div>` +
    table(["Step", "Text"], [
      ["Plaintext", `<pre class="out mb-0">${esc(msg)}</pre>`],
      [`Encryption (shift by +${s})`, `<pre class="out mb-0">${esc(enc)}</pre>`],
      [`Decryption (shift by &minus;${s})`, `<pre class="out mb-0">${esc(dec)}</pre>`],
    ]) +
    (dec === msg ? `<div class="small text-success mt-2">&#10003; Decryption gives back the original message.</div>` : `<div class="small text-danger mt-2">&#10007; Mismatch.</div>`);
}

/* ---------------------------------------------------------------------
   5. Charts
   --------------------------------------------------------------------- */

function drawBars(canvas, values, o = {}) {
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
  const L = 46, R = 12, T = 34, B = 40;
  const pw = W - L - R, ph = H - T - B;
  const ymax = o.ymax ?? Math.max(1e-9, ...values, ...(o.curve || []), o.hline || 0) * 1.12;
  const y = (v) => T + ph - (v / ymax) * ph;
  const bw = pw / values.length;
  const fmt = o.fmt || ((v) => String(Math.round(v * 10) / 10));

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = "#212529"; ctx.font = "bold 13px sans-serif"; ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);

  ctx.strokeStyle = "#adb5bd"; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + ph); ctx.lineTo(W - R, T + ph); ctx.stroke();
  ctx.font = "10px sans-serif"; ctx.fillStyle = "#6c757d"; ctx.textAlign = "right";
  for (let i = 0; i <= 4; i++) {
    const v = (ymax * i) / 4;
    ctx.fillText(fmt(v), L - 5, y(v) + 3);
    if (i > 0) { ctx.strokeStyle = "#f1f3f5"; ctx.beginPath(); ctx.moveTo(L, y(v)); ctx.lineTo(W - R, y(v)); ctx.stroke(); }
  }
  ctx.fillStyle = o.color || "#2c3e50";
  values.forEach((v, i) => ctx.fillRect(L + i * bw + bw * 0.12, y(v), Math.max(1, bw * 0.76), T + ph - y(v)));

  if (o.curve) {
    ctx.strokeStyle = "#e74c3c"; ctx.lineWidth = 2; ctx.beginPath();
    o.curve.forEach((v, i) => { const px = L + i * bw + bw / 2; i === 0 ? ctx.moveTo(px, y(v)) : ctx.lineTo(px, y(v)); });
    ctx.stroke();
  }
  if (o.hline !== undefined) {
    ctx.strokeStyle = "#e74c3c"; ctx.lineWidth = 1.5; ctx.setLineDash([5, 4]);
    ctx.beginPath(); ctx.moveTo(L, y(o.hline)); ctx.lineTo(W - R, y(o.hline)); ctx.stroke(); ctx.setLineDash([]);
  }
  ctx.fillStyle = "#6c757d"; ctx.textAlign = "center"; ctx.font = "10px sans-serif";
  values.forEach((_, i) => { if (!o.labels || i % (o.labelEvery || 1) === 0) ctx.fillText(o.labels ? o.labels[i] : String(i), L + i * bw + bw / 2, T + ph + 14); });
  if (o.xTitle) ctx.fillText(o.xTitle, L + pw / 2, H - 8);
}

function drawLines(canvas, labels, series, o = {}) {
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
  const L = 50, R = 20, T = 34, B = 74;
  const pw = W - L - R, ph = H - T - B;
  const x = (i) => L + (i / (labels.length - 1)) * pw;
  const y = (v) => T + ph - (v / 100) * ph;
  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = "#212529"; ctx.font = "bold 13px sans-serif"; ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);
  ctx.font = "10px sans-serif"; ctx.textAlign = "right";
  for (let v = 0; v <= 100; v += 20) {
    ctx.strokeStyle = v === 0 ? "#adb5bd" : "#f1f3f5"; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(L, y(v)); ctx.lineTo(W - R, y(v)); ctx.stroke();
    ctx.fillStyle = "#6c757d"; ctx.fillText(v + " %", L - 5, y(v) + 3);
  }
  ctx.textAlign = "center";
  labels.forEach((l, i) => { ctx.fillStyle = "#6c757d"; ctx.fillText(String(l), x(i), T + ph + 14); });
  ctx.fillText(o.xTitle || "", L + pw / 2, T + ph + 30);
  for (const s of series) {
    ctx.strokeStyle = s.color; ctx.fillStyle = s.color; ctx.lineWidth = 2;
    ctx.beginPath();
    s.values.forEach((v, i) => (i === 0 ? ctx.moveTo(x(i), y(v)) : ctx.lineTo(x(i), y(v))));
    ctx.stroke();
    s.values.forEach((v, i) => { ctx.beginPath(); ctx.arc(x(i), y(v), 3, 0, Math.PI * 2); ctx.fill(); });
  }
  let lx = L;
  ctx.textAlign = "left"; ctx.font = "11px sans-serif";
  for (const s of series) {
    ctx.fillStyle = s.color; ctx.fillRect(lx, H - 22, 10, 10);
    ctx.fillStyle = "#212529"; ctx.fillText(s.name, lx + 14, H - 13);
    lx += 14 + ctx.measureText(s.name).width + 18;
  }
}

/* ---------------------------------------------------------------------
   6. Corpus and language model
   --------------------------------------------------------------------- */

const CORPUS = [
  "The old town sits where the river bends toward the sea, and for most of its history it lived by what the water brought. Merchants arrived in flat boats loaded with grain, salt and timber, and the families who kept the warehouses grew rich enough to build tall houses along the quay. In the morning the market opened before the sun had cleared the hills, and by noon the narrow streets were so crowded that a person could hardly cross from one side to the other. Children ran between the stalls, dogs followed the butchers, and the smell of fresh bread mixed with the smoke from a hundred chimneys. Visitors who came in the summer often said that nothing there had changed in centuries, though the locals knew better.",
  "Weather is the result of heat moving through the air and the sea. When the sun warms the ground, the air above it rises, and cooler air flows in to take its place. This simple movement, repeated over thousands of kilometres, creates the winds that carry clouds from one region to another. A storm forms when warm moist air meets a cold front, and the water vapour in it turns into drops that fall as rain. Scientists have measured these changes for more than a hundred years, and with modern satellites they can follow a single storm from the moment it begins until it fades over the land. Even so, small differences in the starting conditions can lead to very different results, which is why forecasts become less reliable after about a week.",
  "Good cooking begins with patience rather than with expensive equipment. A pot of soup needs time for the onions to soften and for the flavour of the herbs to spread through the broth. Most beginners make the mistake of turning up the heat to save a few minutes, and they end up with food that is burnt outside and raw within. An experienced cook tastes often, adds salt in small amounts and keeps a spoon beside the stove at all times. The same rule applies to baking, where the temperature of the oven matters more than almost anything else. When the bread comes out golden and the kitchen fills with its warm smell, everyone in the house finds a reason to wander in and ask how long it will be until dinner.",
  "The train left the station a little after seven and climbed slowly into the mountains. Through the window the passengers watched villages appear and disappear between the pine trees, and a thin mist lay over the valleys like a sheet of white paper. An old man across the aisle told his granddaughter the names of the peaks as they passed, though she was more interested in the sandwiches her mother had packed. At the highest point of the line the track entered a long tunnel, and for several minutes there was nothing to see but the reflection of faces in the dark glass. When the train came out into the light again, the whole plain lay below them, green and gold, with a river shining in the middle of it.",
  "Libraries have always been more than places to store books. In the ancient world they were centres of learning where scholars copied texts, compared translations and argued about the meaning of difficult passages. Many works that we read today survived only because someone took the trouble to write them out by hand, again and again, over hundreds of years. The invention of printing made books cheaper and ideas travelled faster than ever before, but it also created new problems, because governments and churches wanted to decide what people should be allowed to read. Today a library may hold millions of volumes and also offer quiet rooms, public computers and classes for children, and its most important task is still the same: to give anyone who asks a fair chance to learn.",
  "Few things bring a city together like a football match on a cold Saturday afternoon. Long before the game begins the streets near the stadium fill with supporters wearing scarves and singing songs that their grandparents once sang. Inside, the noise grows with every pass, and when the home team scores, the whole crowd rises as one body and the ground seems to shake. The players themselves speak of the pressure that such a moment brings, and many of them say that the hardest part of the season is not the training but the waiting. After the final whistle the fans leave slowly, discussing every mistake and every lucky escape, and by the evening the same arguments are continuing in every cafe and kitchen across the district.",
  "Sleep is not a luxury but a necessity, and most adults need between seven and nine hours each night to stay healthy. During sleep the brain sorts the events of the day, stores important memories and removes waste that builds up while we are awake. People who sleep too little find it harder to concentrate, make more mistakes at work and are more likely to fall ill. Doctors often advise going to bed at the same time every evening, avoiding bright screens late at night and keeping the bedroom cool and quiet. These habits seem simple, yet many people ignore them for years, because the effects of tired days are slow and easy to blame on something else.",
  "A market works because many people make small decisions at the same time. A farmer decides how much wheat to plant, a baker decides how much flour to buy, and a family decides how much bread to eat, and none of them needs to know the whole plan. When wheat becomes scarce, its price rises, and buyers look for other foods while farmers are encouraged to grow more. Economists have studied this process for centuries, and they warn that it does not always produce fair results, since some people have far more money than others. Even so, the idea that prices carry information is one of the most useful discoveries in the history of the subject, and it helps to explain why shops are usually full without any single person being in charge.",
  "The ocean covers most of the planet, yet people have explored only a small part of it. Beneath the surface there are mountains taller than any on land, valleys deeper than the highest cliff and forests of weed where thousands of animals live. Currents carry warm water from the equator toward the poles, and this slow movement shapes the climate of whole continents. Fishermen have always understood the sea better than scientists, because their lives depended on knowing where the fish would be and when a storm was coming. Today researchers use robots and sensors to follow the changes that humans have caused, and many of them believe that the next few decades will decide whether the great fisheries can recover.",
  "Communication has changed more in the last two hundred years than in the previous two thousand. A letter once took weeks to cross an ocean, and a message that arrived late could change the fate of a nation. The telegraph reduced that delay to minutes, the telephone put a voice in every home, and the internet now allows anyone to send a picture to the other side of the world in a second. With each step people have asked whether the new tool would bring them closer together or only make them more distracted. The honest answer is that it depends on how we use it, and that every generation has to learn again how to listen as well as to speak.",
  "In spring the garden behind the house woke slowly. The first green shoots pushed through the dark soil, and the apple tree, which had looked dead all winter, covered itself with pale flowers. Anna spent every free hour outside, pulling weeds, planting beans and talking to the neighbour across the fence about the price of seeds and the habits of snails. Her grandfather, who had planted the tree fifty years before, used to say that a garden teaches patience more gently than any teacher. She remembered his words when a late frost threatened the blossoms, and she spent a long night covering the branches with old sheets, then slept soundly until the sun reached her window.",
].join(" ");

// Published relative frequencies of letters in English text, in percent (A to Z)
const PUBLISHED = [8.167, 1.492, 2.782, 4.253, 12.702, 2.228, 2.015, 6.094, 6.966, 0.153, 0.772, 4.025, 2.406,
                   6.749, 7.507, 1.929, 0.095, 5.987, 6.327, 9.056, 2.758, 0.978, 2.360, 0.150, 1.974, 0.074];
const ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".split("");

const WORDS = ["THE", "AND", "THAT", "HAVE", "FOR", "NOT", "WITH", "YOU", "THIS", "BUT", "HIS", "FROM", "THEY", "HER", "SHE", "WILL",
  "ONE", "ALL", "WOULD", "THERE", "THEIR", "WHAT", "OUT", "ABOUT", "WHO", "WHICH", "WHEN", "MAKE", "CAN", "LIKE", "TIME", "JUST", "HIM",
  "KNOW", "TAKE", "PEOPLE", "INTO", "YEAR", "YOUR", "GOOD", "SOME", "COULD", "THEM", "SEE", "OTHER", "THAN", "THEN", "NOW", "LOOK", "ONLY",
  "COME", "OVER", "THINK", "ALSO", "BACK", "AFTER", "USE", "TWO", "HOW", "OUR", "WORK", "FIRST", "WELL", "WAY", "EVEN", "NEW", "WANT",
  "BECAUSE", "ANY", "THESE", "GIVE", "DAY", "MOST", "WAS", "ARE", "WERE", "HAD", "HAS", "BEEN"];

const cm = { trainLetters: "", testLetters: "", testRaw: "", model: null };

function buildModel(letters) {
  const n = letters.length;
  const cnt = new Array(26).fill(0);
  const pair = Array.from({ length: 26 }, () => new Array(26).fill(0));
  for (let i = 0; i < n; i++) {
    const c = letters.charCodeAt(i) - 65;
    cnt[c]++;
    if (i > 0) pair[letters.charCodeAt(i - 1) - 65][c]++;
  }
  const freq = cnt.map((c) => (c + 0.5) / (n + 13));
  const lp = pair.map((row) => { const tot = sum(row); return row.map((c) => Math.log((c + 1) / (tot + 26))); });
  return { n, freq, lp, peak: cnt.indexOf(Math.max(...cnt)) };
}

function setupCorpus() {
  const text = $("corpus").value;
  let cut = Math.floor(text.length * 0.7);
  while (cut < text.length && text[cut] !== " ") cut++;
  const trainRaw = text.slice(0, cut);
  cm.testRaw = text.slice(cut).trim();
  cm.trainLetters = lettersOnly(trainRaw);
  cm.testLetters = lettersOnly(cm.testRaw);
  if (cm.trainLetters.length < 500 || cm.testLetters.length < 300) {
    cm.model = null;
    $("corpusInfo").textContent = `The corpus is too short (${lettersOnly(text).length} letters). At least about 1500 letters are needed.`;
    return false;
  }
  cm.model = buildModel(cm.trainLetters);
  $("corpusInfo").innerHTML = `Corpus: ${lettersOnly(text).length} letters in total: ${cm.trainLetters.length} for training the model and ${cm.testLetters.length} kept as test text. ` +
    `Most frequent letter in the training text: <strong>${ALPHA[cm.model.peak]}</strong>.`;
  drawBars($("cvCorpus"), cm.model.freq.map((f) => f * 100), {
    title: "Letter frequencies (%): training corpus (bars) and published English frequencies (red line)",
    labels: ALPHA, curve: PUBLISHED, fmt: (v) => v.toFixed(0),
  });
  return true;
}

/* ---------------------------------------------------------------------
   7. Part D: attack methods against the Caesar cipher
   A guess s means: the ciphertext letter c was produced as (p + s) mod 26.
   --------------------------------------------------------------------- */

function cipherStats(letters) {
  const cnt = new Array(26).fill(0);
  const pair = Array.from({ length: 26 }, () => new Array(26).fill(0));
  for (let i = 0; i < letters.length; i++) {
    const c = letters.charCodeAt(i) - 65;
    cnt[c]++;
    if (i > 0) pair[letters.charCodeAt(i - 1) - 65][c]++;
  }
  return { cnt, pair, L: letters.length };
}

const chiScore = (cs, model, s) => { let x = 0; for (let i = 0; i < 26; i++) { const E = cs.L * model.freq[i], O = cs.cnt[(i + s) % 26]; x += (O - E) ** 2 / E; } return x; };
const bigramScore = (cs, model, s) => { let x = 0; for (let a = 0; a < 26; a++) for (let b = 0; b < 26; b++) if (cs.pair[a][b]) x += cs.pair[a][b] * model.lp[(a - s + 26) % 26][(b - s + 26) % 26]; return x; };
function wordScore(letters, s) {
  const str = shiftLetters(letters, -s);
  let sc = 0;
  for (const w of WORDS) { let i = str.indexOf(w); while (i !== -1) { sc += w.length; i = str.indexOf(w, i + 1); } }
  return sc;
}
const argmin = (a) => a.indexOf(Math.min(...a));
const argmax = (a) => a.indexOf(Math.max(...a));
const range26 = Array.from({ length: 26 }, (_, i) => i);

const METHODS = [
  { id: "chi", name: "Letter frequency (chi-square)", color: "#2c3e50", guess: (l, cs, m) => argmin(range26.map((s) => chiScore(cs, m, s))) },
  { id: "peak", name: "Most frequent letter = E", color: "#e74c3c", guess: (l, cs, m) => (cs.cnt.indexOf(Math.max(...cs.cnt)) - m.peak + 26) % 26 },
  { id: "bigram", name: "Bigram scoring", color: "#18bc9c", guess: (l, cs, m) => argmax(range26.map((s) => bigramScore(cs, m, s))) },
  { id: "words", name: "Exhaustive search + dictionary", color: "#f39c12", guess: (l) => argmax(range26.map((s) => wordScore(l, s))) },
];

function analyseCt() {
  const text = $("ctInput").value;
  const letters = lettersOnly(text);
  if (!cm.model) { $("ctOut").innerHTML = `<div class="text-danger small">The corpus is too short to build a model.</div>`; return; }
  if (letters.length < 5) { $("ctOut").innerHTML = `<div class="text-danger small">Enter a ciphertext with at least 5 letters.</div>`; return; }
  const cs = cipherStats(letters);
  const chi = range26.map((s) => chiScore(cs, cm.model, s));
  const big = range26.map((s) => bigramScore(cs, cm.model, s));
  const wds = range26.map((s) => wordScore(letters, s));
  const bChi = argmin(chi), bBig = argmax(big), bWds = argmax(wds);
  const mark = (txt, isBest) => (isBest ? `<span class="best px-1">${txt}</span>` : txt);
  const rows = range26.map((s) => [
    s, `<span class="pt">${esc(caesar(text, -s).slice(0, 48))}</span>`,
    mark(f1(chi[s]), s === bChi), mark(f1(big[s]), s === bBig), mark(wds[s], s === bWds),
  ]);
  const peakGuess = METHODS[1].guess(letters, cs, cm.model);
  $("ctOut").innerHTML =
    `<p class="mb-2">Guesses: chi-square <strong>s = ${bChi}</strong>; most frequent letter <strong>s = ${peakGuess}</strong>; bigram <strong>s = ${bBig}</strong>; dictionary <strong>s = ${bWds}</strong>.</p>` +
    `<p class="mb-1">Decryption with the chi-square guess:</p><pre class="out">${esc(caesar(text, -bChi))}</pre>` +
    table(["Key s", "Decryption (first 48 characters)", "Chi-square (smaller is better)", "Bigram log-likelihood (larger is better)", "Dictionary score (larger is better)"], rows, "compact");
}

async function runCaesarExperiment() {
  if (!cm.model) { showMsg("caesarErr", "The corpus is too short to build a model."); return; }
  const T = readInt("caesarTrials", 50, 2000, "The number of trials", "caesarErr");
  if (T === null) return;
  $("btnCaesarExp").disabled = true;
  const test = cm.testLetters;
  const lengths = [5, 10, 20, 30, 40, 60, 80, 120, 200].filter((L) => L <= test.length);
  const rate = Object.fromEntries(METHODS.map((m) => [m.id, []]));

  for (const L of lengths) {
    const ok = Object.fromEntries(METHODS.map((m) => [m.id, 0]));
    for (let t = 0; t < T; t++) {
      const start = Math.floor(Math.random() * (test.length - L + 1));
      const s = 1 + Math.floor(Math.random() * 25);
      const ct = shiftLetters(test.substr(start, L), s);
      const cs = cipherStats(ct);
      for (const m of METHODS) if (m.guess(ct, cs, cm.model) === s) ok[m.id]++;
    }
    for (const m of METHODS) rate[m.id].push((100 * ok[m.id]) / T);
    $("caesarProgress").textContent = `Length ${L} done`;
    await tick();
  }
  drawLines($("cvSuccess"), lengths, METHODS.map((m) => ({ name: m.name, color: m.color, values: rate[m.id] })),
    { title: `Success rate of the key recovery (${T} trials per length)`, xTitle: "ciphertext length (letters)" });
  $("caesarTable").innerHTML = table(["Ciphertext length (letters)", ...METHODS.map((m) => m.name)],
    lengths.map((L, i) => [L, ...METHODS.map((m) => `${rate[m.id][i].toFixed(1)} %`)]), "compact");

  // D.5: effect of the corpus size
  const sizes = [200, 500, 1000, 2000, 4000, cm.trainLetters.length].filter((v, i, a) => v <= cm.trainLetters.length && a.indexOf(v) === i);
  const L40 = Math.min(40, test.length);
  const rows = [];
  for (const size of sizes) {
    const model = buildModel(cm.trainLetters.slice(0, size));
    const ok = { chi: 0, peak: 0, bigram: 0 };
    for (let t = 0; t < T; t++) {
      const start = Math.floor(Math.random() * (test.length - L40 + 1));
      const s = 1 + Math.floor(Math.random() * 25);
      const ct = shiftLetters(test.substr(start, L40), s);
      const cs = cipherStats(ct);
      for (const m of METHODS.slice(0, 3)) if (m.guess(ct, cs, model) === s) ok[m.id]++;
    }
    rows.push([`${size}${size === cm.trainLetters.length ? " (all)" : ""}`, ...["chi", "peak", "bigram"].map((id) => `${((100 * ok[id]) / T).toFixed(1)} %`)]);
    await tick();
  }
  $("sizeTable").innerHTML = table(["Training corpus (letters)", METHODS[0].name, METHODS[1].name, METHODS[2].name], rows, "compact");
  $("caesarProgress").textContent = "Finished.";
  $("btnCaesarExp").disabled = false;
}

/* ---------------------------------------------------------------------
   8. Part C: measured statistical properties
   --------------------------------------------------------------------- */

const ic = (counts) => { const n = sum(counts); return n > 1 ? sum(counts.map((c) => c * (c - 1))) / (n * (n - 1)) : NaN; };
const letterCounts = (letters) => { const c = new Array(26).fill(0); for (let i = 0; i < letters.length; i++) c[letters.charCodeAt(i) - 65]++; return c; };

function equalPairFraction(keys, chars) { // among pairs of positions with the same plaintext char, how many have the same ciphertext key?
  const groups = new Map();
  chars.forEach((ch, i) => { if (!groups.has(ch)) groups.set(ch, []); groups.get(ch).push(keys[i]); });
  let pairs = 0, equal = 0;
  for (const ks of groups.values()) {
    const cnt = new Map();
    for (const k of ks) cnt.set(k, (cnt.get(k) || 0) + 1);
    pairs += (ks.length * (ks.length - 1)) / 2;
    for (const c of cnt.values()) equal += (c * (c - 1)) / 2;
  }
  return pairs ? equal / pairs : NaN;
}

async function runStats() {
  if (!cm.model) { showMsg("statErr", "The corpus is too short to build a sample."); return; }
  const n = readInt("statN", 50, 600, "The sample length", "statErr");
  if (n === null) return;
  $("btnStats").disabled = true;
  const sample = cm.testRaw.slice(0, n).split("").map((c) => (c.charCodeAt(0) > 255 ? " " : c)).join("");
  const chars = sample.split("");
  const s = Number($("caesarKey").value);

  const plainL = lettersOnly(sample);
  const caesarCt = caesar(sample, s), caesarL = lettersOnly(caesarCt);
  const pc = letterCounts(plainL), cc = letterCounts(caesarL);

  // ECC, fresh r for every character
  const symFresh = [], keysFresh = [];
  for (let i = 0; i < chars.length; i++) {
    const m = chars[i].charCodeAt(0);
    const r = randScalar();
    const R = mulTable(st.tblG, r), S = mulTable(st.tblQ, r);
    const C = addAffine(st.tblM[m], S);
    symFresh.push(C === null ? 0 : Number(C.x & 255n));
    keysFresh.push(`${R.x}|${C === null ? "O" : C.x}`);
    if (i % 50 === 49) { $("statProgress").textContent = `Encrypting ${i + 1} / ${chars.length}`; await tick(); }
  }
  // ECC, same r for every character
  const r0 = randScalar(), S0 = mulTable(st.tblQ, r0);
  const symReuse = [], keysReuse = [];
  for (const ch of chars) {
    const C = addAffine(st.tblM[ch.charCodeAt(0)], S0);
    symReuse.push(C === null ? 0 : Number(C.x & 255n));
    keysReuse.push(C === null ? "O" : String(C.x));
  }
  const byteIC = (syms) => { const c = new Array(256).fill(0); syms.forEach((v) => c[v]++); return ic(c); };
  const bins = new Array(16).fill(0);
  symFresh.forEach((v) => bins[v >> 4]++);
  const E = chars.length / 16;
  const chi15 = sum(bins.map((o) => (o - E) ** 2 / E));

  drawBars($("cvFreqPlain"), pc.map((c) => (100 * c) / plainL.length), { title: "Plaintext letters (%)", labels: ALPHA, fmt: (v) => v.toFixed(0), ymax: 16 });
  drawBars($("cvFreqCaesar"), cc.map((c) => (100 * c) / caesarL.length), { title: `Caesar ciphertext letters (%), s = ${s}`, labels: ALPHA, fmt: (v) => v.toFixed(0), color: "#e67e22", ymax: 16 });
  drawBars($("cvEccSym"), bins, { title: "ECC ciphertext: lowest byte of C.x, 16 bins", labels: bins.map((_, i) => (i * 16).toString(16)), hline: E, fmt: (v) => v.toFixed(0), color: "#18bc9c", ymax: Math.max(E * 2.2, Math.max(...bins) * 1.2), xTitle: "byte value / 16 (hex), dashed line = uniform expectation" });

  const caesarKeys = caesarCt.split("");
  const fCaesar = equalPairFraction(caesarKeys, chars);
  $("statTable").innerHTML = table(["Symbols", "Index of coincidence", "Equal plaintext characters give equal ciphertext (share of pairs)", "Comment"], [
    ["Plaintext letters", f4(ic(pc)), "-", "English-like"],
    [`Caesar ciphertext letters (s = ${s})`, f4(ic(cc)), `${(100 * fCaesar).toFixed(0)} %`, "Same IC as the plaintext: the statistics are only relabelled"],
    ["ECC ciphertext, fresh r per character (low byte of C.x)", f4(byteIC(symFresh)), `${(100 * equalPairFraction(keysFresh, chars)).toFixed(0)} %`, `Close to 1/256 = 0.0039; chi-square of the 16 bins = ${chi15.toFixed(1)} (about 15 expected)`],
    ["ECC ciphertext, the same r for all characters", f4(byteIC(symReuse)), `${(100 * equalPairFraction(keysReuse, chars)).toFixed(0)} %`, "A substitution cipher on bytes: the statistics survive, so reusing r destroys the security"],
    ["Reference: uniform letters / uniform bytes", `${f4(1 / 26)} / ${f4(1 / 256)}`, "-", "What an ideal cipher would show"],
  ], "compact");
  $("statProgress").textContent = `Finished (${chars.length} characters).`;
  $("btnStats").disabled = false;
}

/* ---------------------------------------------------------------------
   9. Part E: attacks on the restricted private key
   --------------------------------------------------------------------- */

const fmtTime = (s) => {
  if (s < 1e-3) return "&lt; 1 ms";
  if (s < 1) return `${(s * 1000).toFixed(0)} ms`;
  if (s < 60) return `${s.toFixed(1)} s`;
  if (s < 3600) return `${(s / 60).toFixed(1)} min`;
  if (s < 86400) return `${(s / 3600).toFixed(1)} hours`;
  if (s < 86400 * 365) return `${(s / 86400).toFixed(1)} days`;
  const y = s / (86400 * 365.25);
  if (y < 1e6) return `${y.toFixed(0)} years`;
  const [m, e] = y.toExponential(1).split("e+");
  return `${m} &times; 10<sup>${e}</sup> years`;
};

function benchRates() {
  let A = { X: G.x, Y: G.y, Z: 1n };
  let t0 = performance.now();
  for (let i = 0; i < 20000; i++) A = addMixed(A, G);
  const bf = 20000 / ((performance.now() - t0) / 1000);
  let Q = G;
  t0 = performance.now();
  for (let i = 0; i < 2000; i++) Q = addAffine(Q, G);
  const bs = 2000 / ((performance.now() - t0) / 1000);
  st.rates = { bf, bs };
  $("rateInfo").textContent = `${Math.round(bf / 1000)} thousand point additions per second (exhaustive search) and ${Math.round(bs / 1000)} thousand (baby-step giant-step, which needs affine additions)`;
}

function renderCost() {
  const rows = [16, 24, 32, 48, 64, 80, 128, 256].map((b) => {
    const bf = Math.pow(2, b - 1), bs = Math.pow(2, b / 2 + 1);
    return [b, `2<sup>${b - 1}</sup>`, fmtTime(bf / st.rates.bf), `2<sup>${b / 2 + 1}</sup>`, `2<sup>${b / 2}</sup>`, fmtTime(bs / st.rates.bs)];
  });
  $("costTable").innerHTML = table(
    ["Key bits b", "Exhaustive search: average additions", "Estimated time", "Baby-step giant-step: operations", "Table entries needed", "Estimated time"], rows, "compact") +
    `<p class="small text-muted mt-2 mb-0">For b = 256 (a proper key) both attacks are hopeless: the times are many orders of magnitude longer than the age of the universe (about 1.4 &times; 10<sup>10</sup> years), and a table of 2<sup>128</sup> points could never be stored.</p>`;
}

function setAttackBusy(busy) {
  $("btnBrute").disabled = busy; $("btnBsgs").disabled = busy; $("btnStop").disabled = !busy;
  $("btnGenKeys").disabled = busy;
}

function finishAttack(method, k, steps, ms) {
  const ok = k > 0 && samePt(mulTable(st.tblG, BigInt(k)), st.Q);
  let html = table(["Method", "Recovered k", "Correct", "Steps", "Time", "Speed"], [[
    method, ok ? `<code class="hex">${k}</code>` : "not found", ok ? "&#10003; kG = Q" : "&#10007;", steps.toLocaleString("en-US"), `${(ms / 1000).toFixed(2)} s`, `${Math.round(steps / (ms / 1000)).toLocaleString("en-US")} steps/s`,
  ]], "compact");
  if (ok && st.cipher) {
    const text = decryptWith(BigInt(k), st.cipher.items).map((d) => (d.m >= 0 ? String.fromCharCode(d.m) : "?")).join("");
    html += `<p class="mt-3 mb-1">The attacker decrypts the current ciphertext with the recovered key:</p><pre class="out">${esc(text)}</pre>` +
      (text === st.cipher.msg ? `<div class="small text-success">&#10003; This is the original message.</div>` : "");
  } else if (ok) {
    html += `<p class="small text-muted mt-2 mb-0">Encrypt a message in Part A to see the attacker decrypt it with the recovered key.</p>`;
  } else {
    html += `<p class="small text-muted mt-2 mb-0">The key was not found within the allowed number of steps.</p>`;
  }
  $("attackOut").innerHTML = html;
}

async function bruteForce() {
  st.stop = false; setAttackBusy(true);
  const cap = 2 ** 22;
  const maxK = Math.min(2 ** st.bits - 1, cap);
  const t0 = performance.now();
  let A = { X: G.x, Y: G.y, Z: 1n }, found = 0, k = 1;
  for (; k <= maxK; k++) {
    if (equalsJ(A, st.Q)) { found = k; break; }
    A = addMixed(A, G);
    if (k % 20000 === 0) {
      $("attackProgress").textContent = `Exhaustive search: ${k.toLocaleString("en-US")} of ${maxK.toLocaleString("en-US")} candidates tried...`;
      await tick();
      if (st.stop) break;
    }
  }
  $("attackProgress").textContent = st.stop ? "Stopped." : (st.bits > 22 && !found ? "Exhaustive search is capped at 2^22 steps in the browser: use baby-step giant-step for larger ranges." : "");
  finishAttack("Exhaustive search", found, found || k - 1, performance.now() - t0);
  setAttackBusy(false);
}

async function bsgs() {
  st.stop = false; setAttackBusy(true);
  const K = 2 ** st.bits - 1;
  const m = Math.ceil(Math.sqrt(K + 1));
  const t0 = performance.now();
  const baby = new Map();                   // x -> [j, y] for the points jG, j = 1..m-1
  let cur = G, steps = 0, found = 0, aborted = false;
  for (let j = 1; j < m; j++) {
    baby.set(cur.x, [j, cur.y]);
    cur = addAffine(cur, G); steps++;
    if (j % 5000 === 0) { $("attackProgress").textContent = `Baby steps: ${j.toLocaleString("en-US")} of ${m.toLocaleString("en-US")}`; await tick(); if (st.stop) { aborted = true; break; } }
  }
  if (!aborted) {
    const giant = negAffine(cur);           // cur = mG after the loop, giant = -mG
    let R = st.Q;                           // R = Q - i*mG
    for (let i = 0; i <= m; i++) {
      if (R === null) { found = i * m; break; }
      const e = baby.get(R.x);
      if (e && e[1] === R.y) { found = i * m + e[0]; break; }
      R = addAffine(R, giant); steps++;
      if (i % 5000 === 4999) { $("attackProgress").textContent = `Giant steps: ${(i + 1).toLocaleString("en-US")} of at most ${m.toLocaleString("en-US")}`; await tick(); if (st.stop) { aborted = true; break; } }
    }
  }
  $("attackProgress").textContent = aborted ? "Stopped." : `Table of ${baby.size.toLocaleString("en-US")} baby steps (m = ${m.toLocaleString("en-US")}).`;
  finishAttack("Baby-step giant-step", found, steps, performance.now() - t0);
  setAttackBusy(false);
}

// Attack on a ciphertext produced with a reused ephemeral key r (no private key needed)
function reuseAttack() {
  const c = st.cipher;
  if (!c) { $("reuseOut").innerHTML = `<div class="text-danger small">Encrypt a message in Part A first.</div>`; return; }
  if (c.items.length < 2) { $("reuseOut").innerHTML = `<div class="text-danger small">Use a message with at least 2 characters.</div>`; return; }
  const diffMap = new Map();
  for (let d = 1; d < 256; d++) diffMap.set(st.tblM[d].x, [d, st.tblM[d].y]);
  const diffs = [0];
  let failed = 0;
  const C0neg = negAffine(c.items[0].C);
  for (let i = 1; i < c.items.length; i++) {
    const D = addAffine(c.items[i].C, C0neg);              // = (m_i - m_0) G when r is reused
    if (D === null) { diffs.push(0); continue; }
    const e = diffMap.get(D.x);
    if (!e) { failed++; diffs.push(null); continue; }
    diffs.push(e[1] === D.y ? e[0] : -e[0]);
  }
  if (failed > 0) {
    $("reuseOut").innerHTML = `<div class="alert alert-secondary py-2 mb-0">The attack fails: ${failed} of ${c.items.length - 1} differences C<sub>i</sub> &minus; C<sub>0</sub> are not small multiples of G. This ciphertext was encrypted with a fresh r for each character, as it should be.</div>`;
    return;
  }
  const cands = [];
  for (let m0 = 0; m0 < 256; m0++) {
    const codes = diffs.map((d) => m0 + d);
    if (codes.some((v) => v < 0 || v > 255)) continue;
    const text = codes.map((v) => String.fromCharCode(v)).join("");
    const score = (text.match(/[A-Za-z ]/g) || []).length + 0.5 * (text.match(/[.,'!?]/g) || []).length;
    cands.push({ m0, text, score });
  }
  cands.sort((a, b) => b.score - a.score);
  const top = cands.slice(0, 3);
  const printable = (t) => t.replace(/[^\x20-\x7E]/g, "?");
  $("reuseOut").innerHTML =
    `<p class="small text-muted mb-2">All differences C<sub>i</sub> &minus; C<sub>0</sub> were found in the table of 511 small multiples of G. Each of the 256 possible values of the first character gives a candidate message; the one made mostly of letters and spaces wins (the same idea as the statistical tests of Part D).</p>` +
    table(["Rank", "Guess for the first character", "Candidate message", "Score (letters and spaces 1, punctuation 0.5)"],
      top.map((t, i) => [i + 1, `${t.m0} (${esc(printable(String.fromCharCode(t.m0)))})`, `<span class="pt">${esc(printable(t.text))}</span>`, `${t.score} out of ${t.text.length}`]), "compact") +
    (top[0] && top[0].text === c.msg ? `<div class="small text-success mt-2">&#10003; The best candidate is the original message, recovered without the private key.</div>` : `<div class="small text-muted mt-2">The best candidate is not the original message: with so few characters several candidates look plausible.</div>`);
}

/* ---------------------------------------------------------------------
   10. Start-up
   --------------------------------------------------------------------- */

async function init() {
  const sel = $("caesarKey");
  sel.innerHTML = range26.map((s) => `<option value="${s}"${s === 3 ? " selected" : ""}>${s}</option>`).join("");
  $("corpus").value = CORPUS;

  initCurveTables();
  generateKeys();
  setupCorpus();

  $("btnGenKeys").addEventListener("click", generateKeys);
  $("keyBits").addEventListener("change", generateKeys);
  $("kInput").addEventListener("change", onKeyEdited);
  $("btnEnc").addEventListener("click", encryptEcc);
  $("btnDec").addEventListener("click", decryptEcc);
  $("btnCaesar").addEventListener("click", runCaesar);
  $("caesarKey").addEventListener("change", runCaesar);
  $("btnStats").addEventListener("click", runStats);
  let timer = null;
  $("corpus").addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(setupCorpus, 300); });
  $("btnCtRun").addEventListener("click", analyseCt);
  $("btnCtFromB").addEventListener("click", () => { runCaesar(); $("ctInput").value = st.caesarCt; analyseCt(); });
  $("btnCaesarExp").addEventListener("click", runCaesarExperiment);
  $("btnBrute").addEventListener("click", bruteForce);
  $("btnBsgs").addEventListener("click", bsgs);
  $("btnStop").addEventListener("click", () => { st.stop = true; });
  $("btnReuse").addEventListener("click", reuseAttack);

  encryptEcc();
  decryptEcc();
  runCaesar();
  $("ctInput").value = caesar("The attack will begin at dawn, and every soldier must be ready before the sun rises over the eastern hills.", 7);
  analyseCt();
  benchRates();
  renderCost();
  try {
    await runStats();
    await runCaesarExperiment();
    await bruteForce();
    await bsgs();
  } catch (err) {
    showMsg("jsError", "Error while running the experiments: " + err.message);
  }
}

document.addEventListener("DOMContentLoaded", init);
