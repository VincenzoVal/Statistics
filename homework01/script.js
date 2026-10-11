"use strict";

/* =====================================================================
   HMWK 1 - Toy elliptic curve: private key -> public key
   Curve: y^2 = x^3 + a*x + b (mod p), with a = 0, b = 7, p = 17.
   The point at infinity O (neutral element) is represented by null.
   ===================================================================== */

const CURVE = { p: 17, a: 0, b: 7 };
const DEFAULT_G = { x: 1, y: 5 };
const MAX_K = 100000;
const MAX_TABLE_ROWS = 40;      // rows shown in the repeated-addition table
const MAX_VIZ_STEPS = 60;       // steps animated in "repeated addition" mode
const COORD_BITS = Math.ceil(Math.log2(CURVE.p)); // 5 bits per coordinate

const $ = (id) => document.getElementById(id);

/* ---------------------------------------------------------------------
   1. Modular arithmetic and point operations
   --------------------------------------------------------------------- */

const mod = (n, m = CURVE.p) => ((n % m) + m) % m;

function modPow(base, exp, m = CURVE.p) {
  let result = 1;
  base = mod(base, m);
  while (exp > 0) {
    if (exp & 1) result = (result * base) % m;
    base = (base * base) % m;
    exp >>= 1;
  }
  return result;
}

// Inverse modulo a prime p, using Fermat's little theorem: n^(p-2) = n^(-1) (mod p)
const modInverse = (n) => modPow(n, CURVE.p - 2);

const samePoint = (P, Q) =>
  (P === null && Q === null) ||
  (P !== null && Q !== null && P.x === Q.x && P.y === Q.y);

const isOnCurve = (P) =>
  P === null || mod(P.y * P.y) === mod(P.x ** 3 + CURVE.a * P.x + CURVE.b);

const fmt = (P) => (P === null ? "O" : `(${P.x}, ${P.y})`);

// Elliptic-curve point addition (also handles doubling and the point at infinity)
function pointAdd(P, Q) {
  if (P === null) return Q;
  if (Q === null) return P;
  if (P.x === Q.x && mod(P.y + Q.y) === 0) return null; // P + (-P) = O

  let lambda;
  if (P.x === Q.x) {
    // P = Q: tangent line
    lambda = mod((3 * P.x * P.x + CURVE.a) * modInverse(2 * P.y));
  } else {
    // P != Q: chord through the two points
    lambda = mod((Q.y - P.y) * modInverse(Q.x - P.x));
  }
  const x3 = mod(lambda * lambda - P.x - Q.x);
  const y3 = mod(lambda * (P.x - x3) - P.y);
  return { x: x3, y: y3 };
}

// Same operation as pointAdd, but also returns a step-by-step explanation
function describeAdd(P, Q) {
  const R = pointAdd(P, Q);
  const p = CURVE.p;
  const lines = [];

  if (P === null) {
    lines.push(`O + ${fmt(Q)} = ${fmt(Q)} (O is the neutral element)`);
  } else if (Q === null) {
    lines.push(`${fmt(P)} + O = ${fmt(P)} (O is the neutral element)`);
  } else if (P.x === Q.x && mod(P.y + Q.y) === 0) {
    lines.push(`${fmt(P)} + ${fmt(Q)}: same x, opposite y, so the line is vertical and the result is O (point at infinity)`);
  } else {
    let num, den;
    if (P.x === Q.x) {
      lines.push("Point doubling (P = Q): slope of the tangent, λ = (3x² + a) / (2y)");
      num = 3 * P.x * P.x + CURVE.a;
      den = 2 * P.y;
    } else {
      lines.push("Point addition (P ≠ Q): slope of the chord, λ = (y₂ − y₁) / (x₂ − x₁)");
      num = Q.y - P.y;
      den = Q.x - P.x;
    }
    const nm = mod(num), dm = mod(den), inv = modInverse(den);
    const lambda = mod(nm * inv);
    lines.push(`λ = ${nm} · ${dm}⁻¹ = ${nm} · ${inv} ≡ ${lambda} (mod ${p})`);
    lines.push(`x₃ = λ² − x₁ − x₂ = ${lambda}² − ${P.x} − ${Q.x} ≡ ${R.x} (mod ${p})`);
    lines.push(`y₃ = λ(x₁ − x₃) − y₁ = ${lambda}·(${P.x} − ${R.x}) − ${P.y} ≡ ${R.y} (mod ${p})`);
    lines.push(`Result: ${fmt(P)} + ${fmt(Q)} = ${fmt(R)}`);
  }
  return { R, lines };
}

// Double-and-add, scanning the bits of k from the most significant one.
// With record = true it also returns every intermediate step (used for tables and animation).
function doubleAndAdd(k, G, record = false) {
  const bits = k.toString(2);
  let R = null;
  let scalar = 0;
  const steps = [];

  if (record) {
    steps.push({ title: "Start", R, prev: null, scalar, lines: ["R = O (point at infinity), the neutral element."] });
  }
  for (let i = 0; i < bits.length; i++) {
    // Doubling
    const before = R;
    R = pointAdd(R, R);
    scalar *= 2;
    if (record) {
      const lines = before === null ? ["2·O = O"] : describeAdd(before, before).lines;
      steps.push({ title: `Bit ${i + 1} of ${bits.length} is ${bits[i]}: double, R ← 2R`, R, prev: before, scalar, lines });
    }
    // Addition (only when the bit is 1)
    if (bits[i] === "1") {
      const beforeAdd = R;
      R = pointAdd(R, G);
      scalar += 1;
      if (record) {
        steps.push({ title: `Bit ${i + 1} of ${bits.length} is 1: add G, R ← R + G`, R, prev: beforeAdd, scalar, lines: describeAdd(beforeAdd, G).lines });
      }
    }
  }
  return { result: R, bits, steps };
}

// Order of G: smallest n > 0 such that nG = O
function orderOf(G) {
  let R = G;
  let n = 1;
  while (R !== null) {
    R = pointAdd(R, G);
    n++;
  }
  return n;
}

// All affine points of the curve (O is not included)
function allCurvePoints() {
  const pts = [];
  for (let x = 0; x < CURVE.p; x++) {
    for (let y = 0; y < CURVE.p; y++) {
      if (isOnCurve({ x, y })) pts.push({ x, y });
    }
  }
  return pts;
}
const CURVE_POINTS = allCurvePoints();

/* ---------------------------------------------------------------------
   2. Small helpers for the page
   --------------------------------------------------------------------- */

const state = { G: DEFAULT_G, k: 6, Q: null, n: 0 };

function table(headers, rows) {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

const mono = (s) => `<span class="font-monospace">${s}</span>`;
const showError = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideError = (id) => $(id).classList.add("d-none");

function currentBase() {
  const [x, y] = $("baseSelect").value.split(",").map(Number);
  return { x, y };
}

function fillBaseSelect() {
  const sel = $("baseSelect");
  sel.innerHTML = CURVE_POINTS.map((P) => {
    const selected = P.x === DEFAULT_G.x && P.y === DEFAULT_G.y ? " selected" : "";
    return `<option value="${P.x},${P.y}"${selected}>(${P.x}, ${P.y})  -  order ${orderOf(P)}</option>`;
  }).join("");
}

/* ---------------------------------------------------------------------
   3. Main computation: tables and public key
   --------------------------------------------------------------------- */

function compute() {
  const G = currentBase();
  const k = Number($("kInput").value);
  if (!Number.isInteger(k) || k < 1 || k > MAX_K) {
    showError("kError", `The private key k must be an integer between 1 and ${MAX_K}.`);
    return;
  }
  hideError("kError");

  const n = orderOf(G);
  state.G = G; state.k = k; state.n = n;

  $("baseInfo").innerHTML =
    `The point G = ${fmt(G)} satisfies the curve equation: ${isOnCurve(G) ? "yes" : "no"}. ` +
    `Its order is n = ${n}, which means nG = O (the point at infinity). ` +
    `The curve has ${CURVE_POINTS.length + 1} points in total, counting O.`;

  // 2. Repeated addition: G, 2G, ..., kG
  const multiples = [];
  let R = G;
  multiples.push(R);
  for (let i = 2; i <= k; i++) {
    R = pointAdd(R, G);
    multiples.push(R);
  }
  const row = (i) => [i, mono(`${i}G`), mono(fmt(multiples[i - 1])), i === 1 ? "start: G" : mono(`${i - 1}G + G`)];
  const rows = [];
  for (let i = 1; i <= Math.min(k, MAX_TABLE_ROWS); i++) rows.push(row(i));
  if (k > MAX_TABLE_ROWS) {
    rows.push(["...", "...", "...", `(${k - MAX_TABLE_ROWS} rows hidden)`]);
    rows.push(row(k));
  }
  $("seqTable").innerHTML = table(["Step", "Multiple", "Point", "How it is obtained"], rows);

  // 3. Double-and-add
  const dna = doubleAndAdd(k, G, true);
  $("dblBits").innerHTML = `k = ${k} in binary: ${dna.bits} (${dna.bits.length} bits)`;
  $("dblTable").innerHTML = table(
    ["#", "Operation", "Multiple of G reached", "R"],
    dna.steps.map((s, i) => [i, s.title, mono(`${s.scalar}G`), mono(fmt(s.R))])
  );

  // Public key
  const Q = multiples[k - 1];
  const agree = samePoint(Q, dna.result);
  state.Q = Q;
  if (Q === null) {
    $("result").innerHTML =
      `<div class="alert alert-warning mb-0">` +
      `<div class="small text-uppercase fw-bold">Toy public key</div>` +
      `<div class="result-key">Q = ${k}·G = O</div>` +
      `<div>k = ${k} is a multiple of the order n = ${n}, so kG is the point at infinity. ` +
      `This is not a valid public key: a private key must satisfy 1 &le; k &lt; n.</div></div>`;
  } else {
    $("result").innerHTML =
      `<div class="alert alert-success mb-0">` +
      `<div class="small text-uppercase fw-bold">Toy public key</div>` +
      `<div class="result-key">Q = ${k}·G = ${fmt(Q)}</div>` +
      `<div>Private key k = ${k} &middot; base point G = ${fmt(G)} &middot; ` +
      `repeated addition and double-and-add ${agree ? "give the same point" : "DISAGREE (bug!)"}.` +
      (k >= n ? ` Note that k &ge; n = ${n}, so the same Q is produced by k mod n = ${k % n}.` : "") +
      `</div></div>`;
  }
  $("bruteOut").innerHTML = "";

  // 4. Visualisation
  vizPause();
  buildVizSteps();
  renderViz();
}

// "Attack" on the toy key: try k = 1, 2, 3, ... until kG = Q
function bruteForce() {
  const { G, Q, n } = state;
  if (Q === null) {
    $("bruteOut").textContent = "Q is the point at infinity: there is nothing meaningful to recover.";
    return;
  }
  let R = null;
  for (let j = 1; j <= n; j++) {
    R = pointAdd(R, G);
    if (samePoint(R, Q)) {
      $("bruteOut").innerHTML =
        `Found k = ${j} after ${j} attempt${j > 1 ? "s" : ""} (at most ${n} are ever needed). ` +
        `On secp256k1 the order is about 2<sup>256</sup> &asymp; 1.2 &times; 10<sup>77</sup>, so this search is impossible.`;
      return;
    }
  }
}

/* ---------------------------------------------------------------------
   4. Slowed-down visualisation (canvas)
   --------------------------------------------------------------------- */

const viz = { steps: [], idx: 0, timer: null, truncated: false };

function buildVizSteps() {
  const { G, k } = state;
  viz.truncated = false;
  if ($("vizMode").value === "repeated") {
    const limit = Math.min(k, MAX_VIZ_STEPS);
    const steps = [{ title: "Start: 1·G = G", R: G, prev: null, scalar: 1,
                     lines: ["The first multiple is the base point itself."] }];
    let R = G;
    for (let i = 2; i <= limit; i++) {
      const prev = R;
      const d = describeAdd(prev, G);
      R = d.R;
      steps.push({ title: `${i}G = ${i - 1}G + G`, R, prev, scalar: i, lines: d.lines });
    }
    viz.truncated = k > limit;
    viz.steps = steps;
  } else {
    viz.steps = doubleAndAdd(k, G, true).steps;
  }
  viz.idx = 0;
}

function drawArrow(ctx, x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const len = Math.hypot(dx, dy);
  if (len < 1) return;
  const ux = dx / len, uy = dy / len;
  const ex = x2 - ux * 8, ey = y2 - uy * 8; // stop before the target dot
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(ex, ey);
  ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(ex, ey);
  ctx.lineTo(ex - ux * 8 - uy * 4, ey - uy * 8 + ux * 4);
  ctx.lineTo(ex - ux * 8 + uy * 4, ey - uy * 8 - ux * 4);
  ctx.closePath();
  ctx.fill();
}

function renderViz() {
  const canvas = $("vizCanvas");
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
  const M = 36, C = 30;
  const px = (x) => M + x * C;
  const py = (y) => H - M - y * C;
  const last = CURVE.p - 1;

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, W, H);

  // Grid and axis labels
  ctx.lineWidth = 1;
  ctx.strokeStyle = "#e9ecef";
  ctx.fillStyle = "#6c757d";
  ctx.font = "11px sans-serif";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  for (let i = 0; i <= last; i++) {
    ctx.beginPath(); ctx.moveTo(px(i), py(0)); ctx.lineTo(px(i), py(last)); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(px(0), py(i)); ctx.lineTo(px(last), py(i)); ctx.stroke();
    ctx.fillText(String(i), px(i), py(0) + 16);
    ctx.fillText(String(i), px(0) - 16, py(i));
  }
  ctx.font = "bold 12px sans-serif";
  ctx.fillText("x", px(last) + 20, py(0) + 16);
  ctx.fillText("y", px(0) - 16, py(last) - 18);

  // All points of the curve
  ctx.fillStyle = "#9fb3c8";
  for (const P of CURVE_POINTS) {
    ctx.beginPath(); ctx.arc(px(P.x), py(P.y), 5, 0, Math.PI * 2); ctx.fill();
  }

  const upto = viz.steps.slice(0, viz.idx + 1);
  const cur = viz.steps[viz.idx];

  // Arrows between consecutive points
  ctx.strokeStyle = "rgba(230,126,34,0.8)";
  ctx.fillStyle = "rgba(230,126,34,0.8)";
  ctx.lineWidth = 1.5;
  for (const s of upto) {
    if (s.prev && s.R && !samePoint(s.prev, s.R)) {
      drawArrow(ctx, px(s.prev.x), py(s.prev.y), px(s.R.x), py(s.R.y));
    }
  }

  // Visited points with labels
  ctx.font = "11px sans-serif";
  ctx.textAlign = "left";
  for (const s of upto.slice(0, -1)) {
    if (!s.R) continue;
    ctx.fillStyle = "#f39c12";
    ctx.beginPath(); ctx.arc(px(s.R.x), py(s.R.y), 6, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = "#b9770e";
    ctx.fillText(`${s.scalar}G`, px(s.R.x) + 8, py(s.R.y) - 8);
  }

  // Base point G
  ctx.strokeStyle = "#18bc9c";
  ctx.lineWidth = 3;
  ctx.beginPath(); ctx.arc(px(state.G.x), py(state.G.y), 10, 0, Math.PI * 2); ctx.stroke();

  // Current point
  if (cur.R) {
    ctx.fillStyle = "#e74c3c";
    ctx.beginPath(); ctx.arc(px(cur.R.x), py(cur.R.y), 8, 0, Math.PI * 2); ctx.fill();
    ctx.font = "bold 13px sans-serif";
    ctx.fillStyle = "#c0392b";
    ctx.fillText(`${cur.scalar}G`, px(cur.R.x) + 10, py(cur.R.y) - 10);
  } else {
    ctx.font = "bold 13px sans-serif";
    ctx.fillStyle = "#c0392b";
    ctx.textAlign = "left";
    ctx.fillText("R = O (point at infinity: it has no position on the grid)", M, 14);
  }

  // Text panel
  const finished = viz.idx === viz.steps.length - 1;
  let html = `<div class="fw-bold mb-1">Step ${viz.idx + 1} of ${viz.steps.length}: ${cur.title}</div>` +
             `<div class="mb-2">Current value: ${mono(`${cur.scalar}·G = ${fmt(cur.R)}`)}</div>` +
             `<ul>${cur.lines.map((l) => `<li>${l}</li>`).join("")}</ul>`;
  if (finished && !viz.truncated) {
    html += `<div class="alert alert-success mt-3 mb-0">Done: ${state.k}·G = ${fmt(cur.R)} is the toy public key.</div>`;
  }
  $("vizLog").innerHTML = html;
  $("vizNote").textContent = viz.truncated
    ? `The animation is limited to the first ${MAX_VIZ_STEPS} steps because k = ${state.k} is large. Use double-and-add to see the whole computation.`
    : "";
}

function vizPause() {
  if (viz.timer !== null) clearTimeout(viz.timer);
  viz.timer = null;
  $("vizPlay").textContent = "Play";
}

function vizTick() {
  if (viz.idx < viz.steps.length - 1) { viz.idx++; renderViz(); }
  if (viz.idx < viz.steps.length - 1) {
    viz.timer = setTimeout(vizTick, Number($("vizSpeed").value));
  } else {
    vizPause();
  }
}

function vizPlay() {
  if (viz.timer !== null) { vizPause(); return; }
  if (viz.idx >= viz.steps.length - 1) { viz.idx = 0; renderViz(); }
  $("vizPlay").textContent = "Pause";
  viz.timer = setTimeout(vizTick, Number($("vizSpeed").value));
}

function vizStep() {
  vizPause();
  if (viz.idx < viz.steps.length - 1) viz.idx++;
  renderViz();
}

function vizReset() {
  vizPause();
  viz.idx = 0;
  renderViz();
}

/* ---------------------------------------------------------------------
   5. Statistical exploration
   --------------------------------------------------------------------- */

const popcount = (v) => { let c = 0; while (v) { c += v & 1; v >>= 1; } return c; };
const num = (v) => (Number.isNaN(v) ? "n/a" : v.toFixed(3));

function pearson(a, b) {
  const n = a.length;
  if (n < 2) return NaN;
  const ma = a.reduce((s, v) => s + v, 0) / n;
  const mb = b.reduce((s, v) => s + v, 0) / n;
  let cov = 0, va = 0, vb = 0;
  for (let i = 0; i < n; i++) {
    cov += (a[i] - ma) * (b[i] - mb);
    va += (a[i] - ma) ** 2;
    vb += (b[i] - mb) ** 2;
  }
  return va === 0 || vb === 0 ? NaN : cov / Math.sqrt(va * vb);
}

function drawBars(canvas, counts, title) {
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
  const left = 38, right = 10, top = 34, bottom = 28;
  const plotW = W - left - right, plotH = H - top - bottom;
  const max = Math.max(1, ...counts);
  const bw = plotW / counts.length;

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, W, H);

  ctx.fillStyle = "#212529";
  ctx.font = "bold 13px sans-serif";
  ctx.textAlign = "left";
  ctx.textBaseline = "alphabetic";
  ctx.fillText(title, left, 20);

  ctx.strokeStyle = "#adb5bd";
  ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(left, top); ctx.lineTo(left, top + plotH); ctx.lineTo(W - right, top + plotH); ctx.stroke();

  ctx.font = "10px sans-serif";
  ctx.fillStyle = "#6c757d";
  ctx.textAlign = "right";
  ctx.fillText(String(max), left - 4, top + 8);
  ctx.fillText("0", left - 4, top + plotH);

  ctx.textAlign = "center";
  counts.forEach((c, i) => {
    const h = (c / max) * plotH;
    const x = left + i * bw;
    ctx.fillStyle = "#2c3e50";
    ctx.fillRect(x + 2, top + plotH - h, bw - 4, h);
    ctx.fillStyle = "#6c757d";
    ctx.fillText(String(i), x + bw / 2, top + plotH + 14);
    if (c > 0) {
      ctx.fillStyle = "#212529";
      ctx.fillText(String(c), x + bw / 2, top + plotH - h - 3);
    }
  });
}

function runStats() {
  const G = currentBase();
  const K = Number($("statK").value);
  if (!Number.isInteger(K) || K < 2 || K > 5000) {
    showError("statError", "K must be an integer between 2 and 5000.");
    return;
  }
  hideError("statError");

  const n = orderOf(G);
  const P = CURVE.p;
  const mulCache = new Map();
  const mul = (k) => {
    if (!mulCache.has(k)) mulCache.set(k, doubleAndAdd(k, G).result);
    return mulCache.get(k);
  };

  // Public keys for k = 1..K
  const xCounts = Array(P).fill(0), yCounts = Array(P).fill(0);
  const freq = new Map();
  const ks = [], xs = [], ys = [];
  let infCount = 0;
  for (let k = 1; k <= K; k++) {
    const Q = mul(k);
    const key = fmt(Q);
    if (!freq.has(key)) freq.set(key, { Q, count: 0 });
    freq.get(key).count++;
    if (Q === null) { infCount++; continue; }
    xCounts[Q.x]++; yCounts[Q.y]++;
    ks.push(k); xs.push(Q.x); ys.push(Q.y);
  }

  const distinct = [...freq.values()].filter((e) => e.Q !== null).length;
  const xReached = xCounts.filter((c) => c > 0).length;
  const yReached = yCounts.filter((c) => c > 0).length;

  $("statSummary").innerHTML =
    `Base point G = ${fmt(G)}, order n = ${n}. Public keys computed for k = 1, ..., ${K}: ` +
    `${distinct} distinct points other than O, and O itself ${infCount} time${infCount === 1 ? "" : "s"} ` +
    `(whenever k is a multiple of ${n}). ` +
    `The x coordinate takes ${xReached} of the ${P} possible values, the y coordinate ${yReached} of ${P}.`;

  // 5.1 Histograms
  drawBars($("histX"), xCounts, "Frequency of each x value");
  drawBars($("histY"), yCounts, "Frequency of each y value");

  // 5.2 Frequency of individual points
  const entries = [...freq.values()].sort((a, b) => {
    if (a.Q === null) return 1;
    if (b.Q === null) return -1;
    return a.Q.x - b.Q.x || a.Q.y - b.Q.y;
  });
  $("freqTable").innerHTML = table(
    ["Point", "Count", "Share of the K keys"],
    entries.map((e) => [mono(fmt(e.Q)), e.count, `${((100 * e.count) / K).toFixed(1)} %`])
  ) + `<p class="small text-muted mt-2 mb-0">The counts differ by at most one because k &rarr; kG cycles through the n = ${n} multiples of G in a fixed order. ` +
      `In the histograms, only the x and y values that actually occur on the subgroup generated by G can appear.</p>`;

  // 5.3 Bit distribution
  const bitRows = [];
  for (let b = COORD_BITS - 1; b >= 0; b--) {
    const ox = xs.filter((v) => (v >> b) & 1).length / Math.max(1, xs.length);
    const oy = ys.filter((v) => (v >> b) & 1).length / Math.max(1, ys.length);
    bitRows.push([`bit ${b}`, num(ox), num(oy)]);
  }
  $("bitTable").innerHTML = table(["Bit position", "Fraction of 1s in x", "Fraction of 1s in y"], bitRows) +
    `<p class="small text-muted mt-2 mb-0">An unbiased bit would give about 0.5. The top bit is rarely 1 because the values only go up to ${P - 1}.</p>`;

  // 5.4 Correlations
  $("corrOut").innerHTML = table(
    ["Pair", "Pearson correlation r"],
    [["k and x", num(pearson(ks, xs))], ["k and y", num(pearson(ks, ys))], ["x and y", num(pearson(xs, ys))]]
  ) + `<p class="small text-muted mt-2 mb-0">Values close to 0 mean no linear relation. In this toy group the result depends on n and on the order in which the multiples appear, so it is not a reliable test of security.</p>`;

  // 5.5 Avalanche: flip one bit of k and compare the outputs (x and y as 10 bits)
  const B = K.toString(2).length;
  const sum = Array(B).fill(0), cnt = Array(B).fill(0);
  for (let k = 1; k <= K; k++) {
    const Q1 = mul(k);
    if (Q1 === null) continue;
    for (let b = 0; b < B; b++) {
      const k2 = k ^ (1 << b);
      if (k2 < 1) continue;
      const Q2 = mul(k2);
      if (Q2 === null) continue;
      sum[b] += popcount(Q1.x ^ Q2.x) + popcount(Q1.y ^ Q2.y);
      cnt[b]++;
    }
  }
  const totalSum = sum.reduce((s, v) => s + v, 0);
  const totalCnt = cnt.reduce((s, v) => s + v, 0);
  const outBits = 2 * COORD_BITS;
  const avg = totalCnt ? totalSum / totalCnt : NaN;
  $("avalOut").innerHTML = Number.isNaN(avg)
    ? "Not enough data."
    : `On average ${avg.toFixed(2)} of the ${outBits} output bits change when one input bit is flipped ` +
      `(${(100 * avg / outBits).toFixed(1)} %). An ideal hash function would give about 50 %.`;
  $("avalTable").innerHTML = table(
    ["Flipped bit of k", "Average changed output bits (out of " + outBits + ")", "Pairs used"],
    sum.map((s, b) => [`bit ${b}`, cnt[b] ? (s / cnt[b]).toFixed(2) : "n/a", cnt[b]])
  );

  // 5.6 Algebraic structure
  let stepOk = 0;
  for (let k = 1; k <= K; k++) if (samePoint(pointAdd(mul(k), G), mul(k + 1))) stepOk++;
  let addOk = 0;
  const trials = 300;
  for (let t = 0; t < trials; t++) {
    const a = 1 + Math.floor(Math.random() * K);
    const b = 1 + Math.floor(Math.random() * K);
    if (samePoint(pointAdd(mul(a), mul(b)), mul(a + b))) addOk++;
  }
  let perOk = 0;
  for (let k = 1; k <= K; k++) if (samePoint(mul(k), mul(k + n))) perOk++;
  $("linearOut").innerHTML = table(
    ["Property", "Cases that hold"],
    [
      [`(k + 1)G = kG + G, for k = 1..${K}`, `${stepOk} / ${K}`],
      [`(a + b)G = aG + bG, for ${trials} random pairs`, `${addOk} / ${trials}`],
      [`kG = (k + n)G (periodicity, n = ${n}), for k = 1..${K}`, `${perOk} / ${K}`],
    ]
  ) + `<p class="small text-muted mt-2 mb-0">A cryptographic hash function should not satisfy relations like these. Here they hold for every tested value.</p>`;
}

/* ---------------------------------------------------------------------
   6. Start-up
   --------------------------------------------------------------------- */

function init() {
  fillBaseSelect();
  $("computeBtn").addEventListener("click", compute);
  $("kInput").addEventListener("keydown", (e) => { if (e.key === "Enter") compute(); });
  $("baseSelect").addEventListener("change", () => { compute(); runStats(); });
  $("bruteBtn").addEventListener("click", bruteForce);
  $("vizMode").addEventListener("change", () => { vizPause(); buildVizSteps(); renderViz(); });
  $("vizPlay").addEventListener("click", vizPlay);
  $("vizStep").addEventListener("click", vizStep);
  $("vizReset").addEventListener("click", vizReset);
  $("vizSpeed").addEventListener("input", () => { $("vizSpeedLabel").textContent = $("vizSpeed").value; });
  $("statBtn").addEventListener("click", runStats);
  compute();
  runStats();
}

document.addEventListener("DOMContentLoaded", init);
