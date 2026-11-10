"use strict";

/* =====================================================================
   HMWK 5 - Riemann vs Lebesgue integration, and the numerical normal CDF.
   Exercise 1: sums from a partition of the domain (Riemann) and of the range (Lebesgue).
   Exercise 2: normal CDF from the error function (series, continued fraction), quadrature, approximations.
   Pure JavaScript, no external libraries.
   ===================================================================== */

const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");
const fmtInt = (v) => Math.round(v).toLocaleString("en-US");

// Number with about d significant digits, in plain or exponential notation
const g = (v, d = 4) => {
  if (v === null || Number.isNaN(v)) return "n/a";
  if (!Number.isFinite(v)) return v > 0 ? "&infin;" : "&minus;&infin;";
  if (v === 0) return "0";
  const a = Math.abs(v);
  return a >= 1e5 || a < 1e-3 ? v.toExponential(d > 4 ? d - 1 : 2) : String(Number(v.toPrecision(d)));
};
const ge = (v) => (v === null || !Number.isFinite(v) ? "n/a" : v === 0 ? "0" : v.toExponential(2)); // errors

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

/* ---------------------------------------------------------------------
   1. Mathematical helpers
   --------------------------------------------------------------------- */

// Seeded pseudo-random generator, uniform in [0, 1)
function mulberry32(seed) {
  let a = seed | 0;
  return () => {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function timeIt(fn, reps) {
  let best = Infinity, res;
  for (let i = 0; i < reps; i++) { const t0 = performance.now(); res = fn(); best = Math.min(best, performance.now() - t0); }
  return { ms: best, res };
}

const SQRT_PI = Math.sqrt(Math.PI), SQRT2 = Math.SQRT2, INV_SQRT_2PI = 1 / Math.sqrt(2 * Math.PI);
const T_SWITCH = 2;                                  // series for t = |x|/sqrt(2) below this value, continued fraction above
const phiPdf = (u) => INV_SQRT_2PI * Math.exp(-0.5 * u * u);

// erf(t) = 2/sqrt(pi) e^(-t^2) sum 2^n t^(2n+1) / (1*3*...*(2n+1)): all terms positive, no cancellation
function erfSeries(t) {
  const t2 = t * t;
  let term = t, sum = t, n = 0;
  while (n < 1000) { n++; term *= (2 * t2) / (2 * n + 1); sum += term; if (term < 1e-17 * sum) break; }
  return { value: (2 / SQRT_PI) * Math.exp(-t2) * sum, terms: n + 1 };
}
// The same series cut after N terms
function erfSeriesN(t, N) {
  let term = t, sum = t;
  for (let n = 1; n < N; n++) { term *= (2 * t * t) / (2 * n + 1); sum += term; }
  return (2 / SQRT_PI) * Math.exp(-t * t) * sum;
}
// Textbook Maclaurin series of erf, alternating signs
function erfAlternating(t, N) {
  let term = t, sum = t;
  for (let n = 1; n < N; n++) { term *= -(t * t) / n; sum += term / (2 * n + 1); }
  return (2 / SQRT_PI) * sum;
}
// erfc(t), t > 0, by the continued fraction DLMF 7.9.2 and the modified Lentz method:
// sqrt(pi) e^(t^2) erfc(t) = 2t / (2t^2+1 - 1*2/(2t^2+5 - 3*4/(2t^2+9 - ...)))
function erfcCF(t, maxIter = 500, tol = 1e-16) {
  const z2 = t * t, tiny = 1e-300;
  let f = 2 * z2 + 1, C = f, D = 0, k;
  for (k = 1; k <= maxIter; k++) {
    const a = -(2 * k - 1) * (2 * k), b = 2 * z2 + 1 + 4 * k;
    D = b + a * D; if (D === 0) D = tiny; D = 1 / D;
    C = b + a / C; if (C === 0) C = tiny;
    const delta = C * D; f *= delta;
    if (Math.abs(delta - 1) < tol) break;
  }
  return { value: ((Math.exp(-z2) / SQRT_PI) * 2 * t) / f, iters: Math.min(k, maxIter) };
}

const work = { terms: 0, iters: 0 };                 // work done by the last call of normCdf
function upperTail(x) {                              // 1 - Phi(x) for x >= 0, that is erfc(x/sqrt(2))/2
  const t = x / SQRT2;
  if (t < T_SWITCH) { const s = erfSeries(t); work.terms = s.terms; return 0.5 - 0.5 * s.value; }
  const c = erfcCF(t); work.iters = c.iters; return 0.5 * c.value;
}
function normCdf(x) {
  if (Number.isNaN(x)) return NaN;
  if (!Number.isFinite(x)) return x > 0 ? 1 : 0;
  const q = upperTail(Math.abs(x));
  return x >= 0 ? 1 - q : q;
}

function trapz(f, a, b, n) { const h = (b - a) / n; let s = 0.5 * (f(a) + f(b)); for (let i = 1; i < n; i++) s += f(a + i * h); return s * h; }
function simpson(f, a, b, n) { const h = (b - a) / n; let s = f(a) + f(b); for (let i = 1; i < n; i++) s += f(a + i * h) * (i % 2 ? 4 : 2); return (s * h) / 3; }

// Abramowitz & Stegun 7.1.26: erf with absolute error below 1.5e-7, used here for Phi
function cdfAS(x) {
  const t0 = Math.abs(x) / SQRT2, t = 1 / (1 + 0.3275911 * t0);
  const poly = ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t;
  const e = 1 - poly * Math.exp(-t0 * t0);
  return x >= 0 ? 0.5 * (1 + e) : 0.5 * (1 - e);
}

// Reference values: NIST table (area from 0 to x, 5 decimals, plus 0.5) and mpmath values computed offline (40 digits)
const REFS = [
  { x: 0.5, nist: 0.69146, hp: 0.6914624612740131 },
  { x: 1, nist: 0.84134, hp: 0.84134474606854295 },
  { x: 1.5, nist: 0.93319, hp: 0.93319279873114193 },
  { x: 1.53, nist: 0.93699, hp: 0.93699163553602158 },
  { x: 1.96, nist: 0.975, hp: 0.97500210485177956 },
  { x: 2, nist: 0.97725, hp: 0.97724986805182079 },
  { x: 2.5, nist: 0.99379, hp: 0.99379033467422386 },
  { x: 3, nist: 0.99865, hp: 0.99865010196836991 },
  { x: 3.5, nist: 0.99977, hp: 0.99976737092096447 },
  { x: 4, nist: 0.99997, hp: 0.99996832875816688 },
  { x: -1, nist: 0.15866, hp: 0.15865525393145705 },
  { x: -1.53, nist: 0.06301, hp: 0.063008364463978422 },
  { x: -4, nist: null, hp: 3.1671241833119921e-5 },
  { x: -5, nist: null, hp: 2.8665157187919391e-7 },
  { x: 8, nist: null, hp: 0.99999999999999938 },
  { x: -8, nist: null, hp: 6.2209605742717841e-16 },
];
const TAILS = [                                       // Q(x) = 1 - Phi(x)
  { x: 3, q: 0.0013498980316300946 }, { x: 4, q: 3.1671241833119921e-5 }, { x: 5, q: 2.8665157187919391e-7 },
  { x: 6, q: 9.8658764503769814e-10 }, { x: 8, q: 6.2209605742717841e-16 },
];
const hpPhi = (x) => REFS.find((r) => r.x === x).hp;
const tailQ = (x) => TAILS.find((r) => r.x === x).q;

// Number-theoretic helpers for the pathological functions
function thomaeUpper(n) {                             // exact upper Darboux sum of Thomae's function on n equal subintervals
  let s = 0;
  for (let i = 0; i < n; i++) {
    let q = 1;                                        // smallest q such that some p/q lies in [i/n, (i+1)/n]
    while (q < n && Math.floor((q * i + n - 1) / n) > Math.floor((q * (i + 1)) / n)) q++;
    s += 1 / q;
  }
  return s / n;
}
function totients(n) {
  const phi = Array.from({ length: n + 1 }, (_, i) => i);
  for (let p = 2; p <= n; p++) if (phi[p] === p) for (let k = p; k <= n; k += p) phi[k] -= phi[k] / p;
  return phi;
}

/* ---------------------------------------------------------------------
   2. Generic chart: lines, markers, bars, vertical lines, log axes
   --------------------------------------------------------------------- */

function niceStep(range, target) {
  const raw = range / target, p = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / p;
  return (f < 1.5 ? 1 : f < 3 ? 2 : f < 7 ? 5 : 10) * p;
}
function linTicks(lo, hi) {
  const st = niceStep(hi - lo, 5), out = [];
  for (let v = Math.ceil(lo / st - 1e-9) * st; v <= hi + st * 1e-9; v += st) out.push(Math.abs(v) < st * 1e-9 ? 0 : v);
  return out;
}
function logTicks(lo, hi) {
  const e0 = Math.ceil(Math.log10(lo) - 1e-9), e1 = Math.floor(Math.log10(hi) + 1e-9), out = [];
  for (let e = e0; e <= e1; e++) out.push(Math.pow(10, e));
  return out;
}
const tickLabel = (v) => {
  if (v === 0) return "0";
  const a = Math.abs(v);
  return a >= 1e5 || a < 1e-3 ? v.toExponential(0) : String(Number(v.toPrecision(3)));
};

function plot(canvas, o) {
  const W = Number(canvas.dataset.w || canvas.width), H = Number(canvas.dataset.h || canvas.height);
  canvas.dataset.w = W; canvas.dataset.h = H;
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const okv = (v, lg) => Number.isFinite(v) && (!lg || v > 0);
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  const touch = (x, y) => {
    if (!okv(x, o.xlog) || !okv(y, o.ylog)) return;
    if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
  };
  for (const s of o.series) {
    if (s.pts) for (const p of s.pts) touch(p[0], p[1]);
    if (s.bars) for (const b of s.bars) { touch(b[0], b[2]); touch(b[1], 0); }
  }
  if (o.xmin !== undefined) x0 = o.xmin;
  if (o.xmax !== undefined) x1 = o.xmax;
  if (o.ymin !== undefined) y0 = o.ymin;
  if (o.ymax !== undefined) y1 = o.ymax;
  if (!(x1 > x0)) { if (o.xlog) { x0 /= 2; x1 *= 2; } else { x0 -= 1; x1 += 1; } }
  if (!(y1 > y0)) { if (o.ylog) { y0 /= 2; y1 *= 2; } else { y0 -= 1; y1 += 1; } }
  if (o.ymin === undefined) { if (o.ylog) y0 /= 1.5; else y0 -= (y1 - y0) * 0.06; }
  if (o.ymax === undefined) { if (o.ylog) y1 *= 1.5; else y1 += (y1 - y0) * 0.06; }

  // legend layout
  ctx.font = "11px sans-serif";
  const items = o.series.filter((s) => s.name);
  const rows = [[]];
  let rowW = 0;
  for (const s of items) {
    const w = 26 + ctx.measureText(s.name).width + 14;
    if (rowW + w > W - 24 && rows[rows.length - 1].length) { rows.push([]); rowW = 0; }
    rows[rows.length - 1].push([s, w]); rowW += w;
  }
  const L = 68, R = 38, T = 34, B = 46 + rows.length * 17;   // symmetric enough to keep the plot centred in the canvas
  const pw = W - L - R, ph = H - T - B;
  const tx = o.xlog ? Math.log10 : (v) => v, ty = o.ylog ? Math.log10 : (v) => v;
  const X = (v) => L + ((tx(v) - tx(x0)) / (tx(x1) - tx(x0))) * pw;
  const Y = (v) => T + ph - ((ty(v) - ty(y0)) / (ty(y1) - ty(y0))) * ph;

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = "#212529"; ctx.font = "bold 13px sans-serif"; ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);

  // grid and tick labels
  ctx.font = "10px sans-serif";
  const xt = o.xlog ? logTicks(x0, x1) : linTicks(x0, x1), yt = o.ylog ? logTicks(y0, y1) : linTicks(y0, y1);
  ctx.lineWidth = 1;
  ctx.textAlign = "center";
  for (const v of xt) {
    ctx.strokeStyle = "#f1f3f5"; ctx.beginPath(); ctx.moveTo(X(v), T); ctx.lineTo(X(v), T + ph); ctx.stroke();
    ctx.fillStyle = "#6c757d"; ctx.fillText(tickLabel(v), X(v), T + ph + 14);
  }
  ctx.textAlign = "right";
  for (const v of yt) {
    ctx.strokeStyle = "#f1f3f5"; ctx.beginPath(); ctx.moveTo(L, Y(v)); ctx.lineTo(L + pw, Y(v)); ctx.stroke();
    ctx.fillStyle = "#6c757d"; ctx.fillText(tickLabel(v), L - 6, Y(v) + 3);
  }
  ctx.strokeStyle = "#adb5bd";
  ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + ph); ctx.lineTo(L + pw, T + ph); ctx.stroke();
  ctx.fillStyle = "#495057"; ctx.font = "11px sans-serif"; ctx.textAlign = "center";
  if (o.xlabel) ctx.fillText(o.xlabel, L + pw / 2, T + ph + 32);
  if (o.ylabel) { ctx.save(); ctx.translate(14, T + ph / 2); ctx.rotate(-Math.PI / 2); ctx.fillText(o.ylabel, 0, 0); ctx.restore(); }

  // data (clipped to the plot area)
  ctx.save();
  ctx.beginPath(); ctx.rect(L, T, pw, ph); ctx.clip();
  for (const s of o.series) {
    ctx.globalAlpha = s.alpha ?? 1;
    if (s.pts) {
      ctx.strokeStyle = s.color; ctx.fillStyle = s.color; ctx.lineWidth = s.width ?? 1.5;
      ctx.setLineDash(s.dash ? [6, 4] : []);
      if (s.line !== false) {
        ctx.beginPath();
        let pen = false;
        for (const p of s.pts) {
          if (!okv(p[0], o.xlog) || !okv(p[1], o.ylog)) { pen = false; continue; }
          if (pen) ctx.lineTo(X(p[0]), Y(p[1])); else { ctx.moveTo(X(p[0]), Y(p[1])); pen = true; }
        }
        ctx.stroke();
      }
      ctx.setLineDash([]);
      if (s.markers) for (const p of s.pts) if (okv(p[0], o.xlog) && okv(p[1], o.ylog)) { ctx.beginPath(); ctx.arc(X(p[0]), Y(p[1]), 3, 0, Math.PI * 2); ctx.fill(); }
    }
  }
  ctx.globalAlpha = 1;
  ctx.restore();

  // legend
  ctx.font = "11px sans-serif"; ctx.textAlign = "left";
  rows.forEach((row, ri) => {
    let lx = L, ly = H - 8 - (rows.length - 1 - ri) * 17;
    for (const [s, w] of row) {
      ctx.strokeStyle = s.color; ctx.fillStyle = s.color; ctx.lineWidth = 2;
      ctx.setLineDash(s.dash ? [5, 3] : []);
      ctx.beginPath(); ctx.moveTo(lx, ly - 4); ctx.lineTo(lx + 18, ly - 4); ctx.stroke();
      ctx.setLineDash([]);
      if (s.markers) { ctx.beginPath(); ctx.arc(lx + 9, ly - 4, 3, 0, Math.PI * 2); ctx.fill(); }
      ctx.fillStyle = "#212529"; ctx.fillText(s.name, lx + 24, ly);
      lx += w;
    }
  });
}

const fnColor = (j) => `hsl(${(j * 47) % 360}, 60%, 42%)`;
const PAL = { main: "#2c3e50", green: "#18bc9c", red: "#e74c3c", orange: "#e67e22", blue: "#7fb3d5" };

/* ---------------------------------------------------------------------
   3. Exercise 1: test functions, Riemann sums, Lebesgue sums
   --------------------------------------------------------------------- */

const FUNCS = [
  { id: "f1", name: "sin(x)", dom: "[0, &pi;]", a: 0, b: Math.PI, f: (x) => Math.sin(x), exact: 2, exactTxt: "2", note: "smooth" },
  { id: "f2", name: "x&sup2;", dom: "[0, 1]", a: 0, b: 1, f: (x) => x * x, exact: 1 / 3, exactTxt: "1/3", note: "smooth" },
  { id: "f3", name: "1 if x &lt; 0.5, 3 if x &ge; 0.5", dom: "[0, 1]", a: 0, b: 1, f: (x) => (x < 0.5 ? 1 : 3), exact: 2, exactTxt: "2", note: "jump at x = 0.5" },
  { id: "f4", name: "|x &minus; 0.5|", dom: "[0, 1]", a: 0, b: 1, f: (x) => Math.abs(x - 0.5), exact: 0.25, exactTxt: "1/4", note: "kink at x = 0.5" },
  { id: "f5", name: "1/&radic;x", dom: "(0, 1]", a: 0, b: 1, f: (x) => 1 / Math.sqrt(x), exact: 2, exactTxt: "2 (improper)", note: "unbounded at 0: improper Riemann integral" },
  { id: "f6", name: "1 if x &lt; 0.5, 0 if x &ge; 0.5", dom: "[0, 1]", a: 0, b: 1, f: (x) => (x < 0.5 ? 1 : 0), exact: 0.5, exactTxt: "1/2", note: "jump at x = 0.5" },
  { id: "f7", name: "sin(x)/x, f(0) = 1", dom: "[0, &pi;]", a: 0, b: Math.PI, f: (x) => (x === 0 ? 1 : Math.sin(x) / x), exact: 1.8519370519824662, exactTxt: "Si(&pi;) &asymp; 1.8519370520", note: "removable singularity at 0" },
];
const NS = [1, 1.5, 2, 2.5, 3, 3.5, 4, 4.5, 5].map((e) => 2 * Math.floor(Math.pow(10, e) / 2) + 1);   // odd sizes
const IA = 4, IB = 8, IC = 6;                         // N = 1001, 100001 (observed order) and 10001 (error table)

// Riemann-type sums: partition of the domain into n equal subintervals
function riemannMid(F, n) {
  const h = (F.b - F.a) / n; let s = 0;
  for (let i = 0; i < n; i++) s += F.f(F.a + (i + 0.5) * h);
  return s * h;
}
function riemannRight(F, n) {
  const h = (F.b - F.a) / n; let s = 0;
  for (let i = 1; i <= n; i++) s += F.f(i === n ? F.b : F.a + i * h);
  return s * h;
}
// Left, right, midpoint, and approximate lower/upper Darboux sums (min and max of 3 samples per subinterval)
function riemann(F, n) {
  const h = (F.b - F.a) / n;
  let L = 0, R = 0, M = 0, lo = 0, up = 0, f0 = F.f(F.a);
  for (let i = 0; i < n; i++) {
    const f1 = F.f(i === n - 1 ? F.b : F.a + (i + 1) * h), fm = F.f(F.a + (i + 0.5) * h);
    L += f0; R += f1; M += fm;
    lo += Math.min(f0, fm, f1); up += Math.max(f0, fm, f1);
    f0 = f1;
  }
  return { left: L * h, right: R * h, mid: M * h, lower: lo * h, upper: up * h };
}

// Lebesgue-type sums: partition of the range [m, M] into K levels; the measure of each preimage is estimated
// from N sample points (grid midpoints, or uniform random points when rng is given)
function lebesgueGrid(F, N, K, rng) {
  const len = F.b - F.a, v = new Float64Array(N);
  let mn = Infinity, mx = -Infinity, s = 0, s2 = 0;
  for (let i = 0; i < N; i++) {
    const y = F.f(rng ? F.a + rng() * len : F.a + ((i + 0.5) * len) / N);
    v[i] = y; s += y; s2 += y * y;
    if (y < mn) mn = y; if (y > mx) mx = y;
  }
  const sd = Math.sqrt(Math.max(0, s2 / N - (s / N) * (s / N)));
  if (mx === mn) { const t = mn * len; return { lower: t, upper: t, mid: t, sd: 0 }; }
  const d = (mx - mn) / K, cnt = new Uint32Array(K);
  for (let i = 0; i < N; i++) { let k = Math.floor((v[i] - mn) / d); if (k >= K) k = K - 1; cnt[k]++; }
  let lo = 0, up = 0;
  for (let k = 0; k < K; k++) if (cnt[k]) { const y = mn + k * d; lo += y * cnt[k]; up += Math.min(y + d, mx) * cnt[k]; }
  lo *= len / N; up *= len / N;
  return { lower: lo, upper: up, mid: (lo + up) / 2, sd };
}
// Lebesgue lower/upper sums with preimage measures known in closed form (no grid, no sampling)
function lebesgueExact(F, K) {
  if (F.id === "f3" || F.id === "f6") return { lower: F.exact, upper: F.exact };   // two level sets, each of measure 1/2
  if (F.id === "f7") return null;
  let lo = 0, up = 0;
  if (F.id === "f5") {   // levels from 1 to sqrt(K); mu{y_k <= f < y_k+1} = y_k^-2 - y_k+1^-2; tail bin [sqrt(K), inf) has measure 1/K
    const M = Math.sqrt(K), d = (M - 1) / K;
    for (let k = 0; k < K; k++) { const a = 1 + k * d, b = 1 + (k + 1) * d; lo += a * (1 / (a * a) - 1 / (b * b)); }
    return { lower: lo + M / (M * M), upper: NaN };
  }
  const d = (F.id === "f4" ? 0.5 : 1) / K;
  for (let k = 0; k < K; k++) {
    const a = k * d, b = (k + 1) * d;
    const mu = F.id === "f1" ? 2 * (Math.asin(Math.min(b, 1)) - Math.asin(a)) : F.id === "f2" ? Math.sqrt(b) - Math.sqrt(a) : 2 * (b - a);
    lo += a * mu; up += b * mu;
  }
  return { lower: lo, upper: up };
}

// Observed convergence order between N = 1001 and N = 100001
function orderOf(e) {
  const a = e[IA], b = e[IB];
  if (a === null || b === null) return "n/a";
  if (a === 0 || b === 0) return "exact";
  if (b < 1e-12) return "&asymp; roundoff";
  return (Math.log10(a / b) / Math.log10(NS[IB] / NS[IA])).toFixed(2);
}

/* ---------------------------------------------------------------------
   4. Rendering of Exercise 1
   --------------------------------------------------------------------- */

function renderFunctions() {
  $("fnTable").innerHTML = table(["", "f(x)", "Interval", "Exact integral", "Note"],
    FUNCS.map((F) => [F.id, `<code>${F.name}</code>`, F.dom, F.exactTxt, F.note]), "compact");
}

function renderSums() {
  const N = Number($("nSel").value);
  $("riemannTable").innerHTML = table(["", "Left", "Right", "Midpoint", "Lower (Darboux)", "Upper (Darboux)", "Exact"],
    FUNCS.map((F) => { const r = riemann(F, N); return [F.id, g(r.left, 8), g(r.right, 8), g(r.mid, 8), g(r.lower, 8), g(r.upper, 8), g(F.exact, 8)]; }), "compact");
  $("lebTable").innerHTML = table(["", "Lower (grid)", "Upper (grid)", "Midpoint of bounds", "Lower (exact preimages)", "Upper (exact preimages)", "Exact"],
    FUNCS.map((F) => {
      const l = lebesgueGrid(F, N, N), x = lebesgueExact(F, N);
      return [F.id, g(l.lower, 8), g(l.upper, 8), g(l.mid, 8), x ? g(x.lower, 8) : "n/a", x ? g(x.upper, 8) : "n/a", g(F.exact, 8)];
    }), "compact");
  $("sumsN").textContent = fmtInt(N);
}

async function renderExercise1(cfg) {
  renderFunctions();
  renderSums();
  await tick();

  // errors against N for every method
  const D = FUNCS.map(() => ({ R: [], Rr: [], L: [], X: [], M: [] }));
  for (let j = 0; j < FUNCS.length; j++) {
    const F = FUNCS[j];
    NS.forEach((N, i) => {
      D[j].R.push(Math.abs(riemannMid(F, N) - F.exact));
      D[j].Rr.push(Math.abs(riemannRight(F, N) - F.exact));
      D[j].L.push(Math.abs(lebesgueGrid(F, N, N).mid - F.exact));
      const x = lebesgueExact(F, N);
      D[j].X.push(x ? Math.abs(x.lower - F.exact) : null);
      D[j].M.push(Math.abs(lebesgueGrid(F, N, N, mulberry32(cfg.seed + 101 * j + i)).mid - F.exact));
    });
    await tick();
  }
  const pts = (arr) => arr.map((e, i) => [NS[i], e]);
  const base = { xlog: true, ylog: true, ylabel: "|error|" };
  plot($("cvRiemann"), { ...base, title: "Riemann midpoint sums, f1 to f7", xlabel: "n (subintervals)",
    series: FUNCS.map((F, j) => ({ name: F.id, color: fnColor(j), markers: true, pts: pts(D[j].R) })) });
  plot($("cvLeb"), { ...base, title: "Lebesgue grid sums, f1 to f7", xlabel: "N (points and levels)",
    series: FUNCS.map((F, j) => ({ name: F.id, color: fnColor(j), markers: true, pts: pts(D[j].L) })) });
  plot($("cvF1"), { ...base, title: "f1 = sin(x) on [0, \u03c0]", xlabel: "N",
    series: [
      { name: "Riemann midpoint", color: PAL.main, markers: true, pts: pts(D[0].R) },
      { name: "Lebesgue grid", color: PAL.green, markers: true, pts: pts(D[0].L) },
      { name: "Lebesgue exact preimages (lower)", color: PAL.red, markers: true, pts: pts(D[0].X) },
      { name: "Lebesgue Monte Carlo", color: PAL.orange, dash: true, pts: pts(D[0].M) }] });
  plot($("cvF5"), { ...base, title: "f5 = 1/\u221ax on (0, 1]", xlabel: "N",
    series: [
      { name: "Riemann midpoint", color: PAL.main, markers: true, pts: pts(D[4].R) },
      { name: "Riemann right", color: PAL.blue, markers: true, pts: pts(D[4].Rr) },
      { name: "Lebesgue grid", color: PAL.green, markers: true, pts: pts(D[4].L) },
      { name: "Lebesgue exact preimages (lower)", color: PAL.red, markers: true, pts: pts(D[4].X) },
      { name: "Lebesgue Monte Carlo", color: PAL.orange, dash: true, pts: pts(D[4].M) }] });

  // comparison at N = 10001
  $("convTable").innerHTML = table(["", "|R &minus; exact|", "|L grid &minus; exact|", "|L exact &minus; exact|", "order R", "order L grid", "order L exact", "|R &minus; L grid|"],
    FUNCS.map((F, j) => [F.id, ge(D[j].R[IC]), ge(D[j].L[IC]), ge(D[j].X[IC]), orderOf(D[j].R), orderOf(D[j].L), orderOf(D[j].X),
      ge(Math.abs(riemannMid(F, NS[IC]) - lebesgueGrid(F, NS[IC], NS[IC]).mid))]), "compact");

  // Monte Carlo version
  const mc = [];
  FUNCS.forEach((F, j) => {
    [NS[IC], NS[IB]].forEach((N, k) => {
      const r = lebesgueGrid(F, N, N, mulberry32(cfg.seed + 977 * j + k));
      mc.push([F.id, fmtInt(N), g(r.mid, 8), ge(Math.abs(r.mid - F.exact)), F.id === "f5" ? "&infin; (infinite variance)" : ge((r.sd * (F.b - F.a)) / Math.sqrt(N))]);
    });
  });
  $("mcTable").innerHTML = table(["", "N", "Estimate", "|error|", "Expected noise &sigma;(b &minus; a)/&radic;N"], mc, "compact");
  await tick();

  // cost for f1 at N = K = 10^6
  const NT = 1000000, F1 = FUNCS[0];
  const tR = timeIt(() => riemannMid(F1, NT), 3), tL = timeIt(() => lebesgueGrid(F1, NT, NT), 3);
  const tX = timeIt(() => lebesgueExact(F1, NT), 3), tM = timeIt(() => lebesgueGrid(F1, NT, NT, mulberry32(cfg.seed)), 3);
  $("effTable").innerHTML = table(["Method", "Evaluations of f", "Other work", "Time (ms, best of 3)", "|error|"], [
    ["Riemann midpoint", fmtInt(NT), "none", g(tR.ms, 3), ge(Math.abs(tR.res - F1.exact))],
    ["Lebesgue grid", fmtInt(NT), "array of N values, histogram with K bins", g(tL.ms, 3), ge(Math.abs(tL.res.mid - F1.exact))],
    ["Lebesgue exact preimages", "0", `${fmtInt(NT)} evaluations of arcsin`, g(tX.ms, 3), ge(Math.abs(tX.res.lower - F1.exact))],
    ["Lebesgue Monte Carlo", fmtInt(NT), "N random draws, array, histogram", g(tM.ms, 3), ge(Math.abs(tM.res.mid - F1.exact))],
  ], "compact");

  // Dirichlet and Thomae
  $("dirTable").innerHTML = table(["n", "Upper sum U<sub>n</sub>", "Lower sum L<sub>n</sub>", "Lebesgue sum"],
    [10, 100, 1000].map((n) => { let up = 0; for (let i = 0; i < n; i++) up += 1 / n; return [fmtInt(n), g(up), "0", "0"]; }), "compact");
  const rng = mulberry32(cfg.seed);
  let dyadic = 0;
  for (let i = 0; i < 1000; i++) if (Number.isInteger(rng() * 4294967296)) dyadic++;
  $("dyadic").textContent = fmtInt(dyadic);
  $("thomaeTable").innerHTML = table(["n", "Upper sum U<sub>n</sub>", "Lower sum L<sub>n</sub>"],
    [10, 100, 1000, 10000].map((n) => [fmtInt(n), g(thomaeUpper(n)), "0"]), "compact");
  const phi = totients(1000);
  $("thomaeLevels").innerHTML = table(["k", "Level set {f &ge; 1/k}", "Number of points", "Measure"],
    [1, 2, 5, 10, 100, 1000].map((k) => {
      let c = 1; for (let q = 1; q <= k; q++) c += phi[q];
      return [k, "rationals p/q in [0, 1] with q &le; k", fmtInt(c), "0"];
    }), "compact");
}

/* ---------------------------------------------------------------------
   5. Rendering of Exercise 2
   --------------------------------------------------------------------- */

async function renderExercise2() {
  // comparison with the reference values
  $("refTable").innerHTML = table(["x", "&Phi;(x), this implementation", "NIST table (5 decimals)", "|&Phi; &minus; NIST|", "within 5&middot;10<sup>&minus;6</sup>", "High-precision reference", "Relative error"],
    REFS.map((r) => {
      const v = normCdf(r.x), dn = r.nist === null ? null : Math.abs(v - r.nist);
      return [r.x, v.toPrecision(16), r.nist === null ? "&mdash;" : r.nist.toFixed(5), dn === null ? "&mdash;" : ge(dn),
        dn === null ? "&mdash;" : (dn <= 5e-6 ? "yes" : "NO"), r.hp.toPrecision(17), ge(Math.abs(v - r.hp) / r.hp)];
    }), "compact");
  await tick();

  // series terms and continued-fraction iterations
  const X3 = [1, 2, 3], TX = [3, 4, 5, 8];
  $("serTable").innerHTML = table(["Terms N", "|error| at x = 1", "|error| at x = 2", "|error| at x = 3"],
    [2, 5, 10, 15, 20, 30, 40].map((N) => [N, ...X3.map((x) => ge(Math.abs(0.5 + 0.5 * erfSeriesN(x / SQRT2, N) - hpPhi(x))))]), "compact");
  $("cfTable").innerHTML = table(["Iterations K", "rel. error at x = 3", "rel. error at x = 4", "rel. error at x = 5", "rel. error at x = 8"],
    [1, 2, 4, 8, 16, 32].map((K) => [K, ...TX.map((x) => ge(Math.abs(0.5 * erfcCF(x / SQRT2, K, 0).value - tailQ(x)) / tailQ(x)))]), "compact");
  const base = { xlog: true, ylog: true, ylabel: "error" };
  const cols = [PAL.main, PAL.green, PAL.red];
  plot($("cvSer"), { ...base, title: "Series terms and continued-fraction iterations", xlabel: "number of terms or iterations",
    series: [
      ...X3.map((x, i) => ({ name: `series, x = ${x} (abs.)`, color: cols[i], pts: Array.from({ length: 40 }, (_, k) => [k + 1, Math.abs(0.5 + 0.5 * erfSeriesN(x / SQRT2, k + 1) - hpPhi(x))]) })),
      ...[3, 5].map((x, i) => ({ name: `continued fraction, x = ${x} (rel.)`, color: [PAL.orange, PAL.blue][i], dash: true,
        pts: Array.from({ length: 40 }, (_, k) => [k + 1, Math.abs(0.5 * erfcCF(x / SQRT2, k + 1, 0).value - tailQ(x)) / tailQ(x)]) }))] });
  const nl = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], sq = [];
  [1, 3].forEach((x, i) => {
    sq.push({ name: `trapezoid, x = ${x}`, color: [PAL.main, PAL.red][i], markers: true, pts: nl.map((n) => [n, Math.abs(0.5 + trapz(phiPdf, 0, x, n) - hpPhi(x))]) });
    sq.push({ name: `Simpson, x = ${x}`, color: [PAL.green, PAL.orange][i], markers: true, dash: true, pts: nl.map((n) => [n, Math.abs(0.5 + simpson(phiPdf, 0, x, n) - hpPhi(x))]) });
  });
  plot($("cvTrap"), { ...base, title: "Quadrature of the density", xlabel: "n (subintervals)", ylabel: "|error|", series: sq });
  await tick();

  // cost per evaluation and consistency checks
  const M = 200000, grid = Array.from({ length: M }, (_, i) => -6 + (12 * i) / (M - 1));
  let maxTerms = 0, maxIters = 0;
  for (const x of grid) { work.terms = 0; work.iters = 0; normCdf(x); maxTerms = Math.max(maxTerms, work.terms); maxIters = Math.max(maxIters, work.iters); }
  const ns = (ms, cnt) => g((ms * 1e6) / cnt, 3);
  const tH = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) s += normCdf(grid[i]); return s; }, 3);
  const tS = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) { const v = erfSeries(Math.abs(grid[i]) / SQRT2).value; s += grid[i] >= 0 ? 0.5 + 0.5 * v : 0.5 - 0.5 * v; } return s; }, 3);
  const tA = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) s += cdfAS(grid[i]); return s; }, 3);
  const MQ = 5000, up = (i) => (grid[i * 40] > 0 ? grid[i * 40] : 1);
  const tT = timeIt(() => { let s = 0; for (let i = 0; i < MQ; i++) s += 0.5 + trapz(phiPdf, 0, up(i), 100); return s; }, 3);
  const tP = timeIt(() => { let s = 0; for (let i = 0; i < MQ; i++) s += 0.5 + simpson(phiPdf, 0, up(i), 100); return s; }, 3);
  $("costTable").innerHTML = table(["Method", "Work per evaluation", "Time per evaluation (ns)"], [
    ["Hybrid: series for |x| &lt; 2&radic;2, continued fraction beyond", `series &le; ${maxTerms} terms; CF &le; ${maxIters} iterations`, ns(tH.ms, M)],
    ["Series only (no continued fraction)", `up to ${maxTerms}+ terms`, ns(tS.ms, M)],
    ["Trapezoid, n = 100", "101 evaluations of the density", ns(tT.ms, MQ)],
    ["Simpson, n = 100", "101 evaluations of the density", ns(tP.ms, MQ)],
    ["Abramowitz&ndash;Stegun 7.1.26 (fixed polynomial approximation of erf)", "5 multiplications, one exp", ns(tA.ms, M)],
  ], "compact");
  let sym = 0, mono = true, prev = -1;
  for (let i = 0; i <= 2000; i++) {
    const x = -8 + (16 * i) / 2000, v = normCdf(x);
    sym = Math.max(sym, Math.abs(v + normCdf(-x) - 1)); if (v < prev) mono = false; prev = v;
  }
  let ov = 0;
  for (let i = 0; i <= 120; i++) { const t = 1.5 + (1.5 * i) / 120, b = erfcCF(t).value; ov = Math.max(ov, Math.abs(1 - erfSeries(t).value - b) / b); }
  $("checkOut").textContent = `Checks: max |Phi(x) + Phi(-x) - 1| over 2001 points in [-8, 8] is ${ge(sym)}; Phi is monotone non-decreasing on these points: ${mono ? "yes" : "NO"}; ` +
    `max relative difference between 1 - erf (series) and erfc (continued fraction) for t in [1.5, 3] is ${ge(ov)}.`;
  await tick();

  // the three approaches compared, and the tail
  const X6 = [0.5, 1, 2, 4, 8], w = { s: 0, c: 0 };
  for (const x of X6) { work.terms = 0; work.iters = 0; normCdf(x); w.s = Math.max(w.s, work.terms); w.c = Math.max(w.c, work.iters); }
  const err = (fn) => X6.map((x) => ge(Math.abs(fn(x) - hpPhi(x))));
  $("cmpTable").innerHTML = table(["Method", "x = 0.5", "x = 1", "x = 2", "x = 4", "x = 8", "Work"], [
    ["Trapezoid, n = 100", ...err((x) => 0.5 + trapz(phiPdf, 0, x, 100)), "101 evaluations"],
    ["Trapezoid, n = 1000", ...err((x) => 0.5 + trapz(phiPdf, 0, x, 1000)), "1001 evaluations"],
    ["Simpson, n = 100", ...err((x) => 0.5 + simpson(phiPdf, 0, x, 100)), "101 evaluations"],
    ["Simpson, n = 1000", ...err((x) => 0.5 + simpson(phiPdf, 0, x, 1000)), "1001 evaluations"],
    ["Maclaurin series, alternating form, 150 terms", ...err((x) => 0.5 + 0.5 * erfAlternating(x / SQRT2, 150)), "150 terms"],
    ["Maclaurin series, positive-term form (converged)", ...err((x) => 0.5 + 0.5 * erfSeries(x / SQRT2).value), `up to ${erfSeries(8 / SQRT2).terms} terms`],
    ["erf-based hybrid (this implementation)", ...err(normCdf), `series &le; ${w.s} terms; CF &le; ${w.c} iterations`],
    ["Abramowitz&ndash;Stegun 7.1.26 (fixed polynomial approximation of erf)", ...err(cdfAS), "constant"],
  ], "compact");
  $("tailTable").innerHTML = table(["x", "1 &minus; &Phi;(x) by subtraction", "erfc(x/&radic;2)/2 by continued fraction", "Reference Q(x)", "rel. error (subtraction)", "rel. error (continued fraction)"],
    TAILS.map((t) => {
      const sub = 1 - normCdf(t.x), cf = 0.5 * erfcCF(t.x / SQRT2).value;
      return [t.x, sub.toExponential(7), cf.toExponential(7), t.q.toExponential(7), ge(Math.abs(sub - t.q) / t.q), ge(Math.abs(cf - t.q) / t.q)];
    }), "compact");
}

/* ---------------------------------------------------------------------
   6. Controls
   --------------------------------------------------------------------- */

function parseConfig() {
  const raw = String($("seedInput").value).trim(), seed = Number(raw);
  if (raw === "" || !Number.isInteger(seed) || seed < 0 || seed > 4294967295) return "The seed must be an integer between 0 and 4294967295.";
  return { seed };
}

let running = false;
async function run() {
  if (running) return;
  const cfg = parseConfig();
  if (typeof cfg === "string") { showMsg("simError", cfg); return; }
  hideMsg("simError");
  running = true;
  $("btnRun").disabled = true; $("btnSeed").disabled = true;
  $("simStatus").textContent = "Computing...";
  const t0 = performance.now();
  try {
    await renderExercise1(cfg);
    await renderExercise2();
    $("simStatus").textContent = `Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    showMsg("jsError", "Error during the computation: " + err.message);
  }
  running = false;
  $("btnRun").disabled = false; $("btnSeed").disabled = false;
}

function init() {
  $("btnRun").addEventListener("click", run);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = String(crypto.getRandomValues(new Uint32Array(1))[0] >>> 1); run(); });
  $("nSel").addEventListener("change", renderSums);
  run();
}

document.addEventListener("DOMContentLoaded", init);
