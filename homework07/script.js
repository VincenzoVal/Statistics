"use strict";

/* =====================================================================
   HMWK 7 - Modes of Convergence and Bayesian Inference.
   Exercise 1: sample mean of exponential data under the four modes of convergence,
               counterexamples between the modes, scaling by sqrt(n).
   Exercise 2: Bayes' theorem on a detection problem and Beta-Binomial updating.
   Pure JavaScript, no external libraries.
   ===================================================================== */


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

// Standard normal generator (Box-Muller, the second value of each pair is cached)
function normalGen(rng) {
  let spare = null;
  return () => {
    if (spare !== null) { const s = spare; spare = null; return s; }
    let u = rng(); while (u === 0) u = rng();
    const v = rng(), r = Math.sqrt(-2 * Math.log(u)), ang = 2 * Math.PI * v;
    spare = r * Math.sin(ang);
    return r * Math.cos(ang);
  };
}

// Sample standard deviation (divisor m - 1)
function sampleSd(arr) {
  const m = arr.length;
  let mu = 0;
  for (let i = 0; i < m; i++) mu += arr[i];
  mu /= m;
  let ss = 0;
  for (let i = 0; i < m; i++) ss += (arr[i] - mu) * (arr[i] - mu);
  return Math.sqrt(ss / (m - 1));
}

// log Gamma (Lanczos approximation, g = 7)
function lgamma(x) {
  const c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313,
             -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
  if (x < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * x))) - lgamma(1 - x);
  x -= 1;
  let a = c[0];
  const t = x + 7.5;
  for (let i = 1; i < 9; i++) a += c[i] / (x + i);
  return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
}

// Error function: Maclaurin series for |x| < 3, asymptotic expansion of erfc beyond (error below 1e-7)
function erf(x) {
  const ax = Math.abs(x);
  let r;
  if (ax < 3) {
    let term = ax, sum = ax;
    for (let k = 1; k < 200; k++) {
      term *= -ax * ax / k;
      sum += term / (2 * k + 1);
      if (Math.abs(term) < 1e-17) break;
    }
    r = 2 / Math.sqrt(Math.PI) * sum;
  } else {
    const y = 1 / (ax * ax);
    r = 1 - Math.exp(-ax * ax) / (ax * Math.sqrt(Math.PI)) * (1 - y / 2 + 3 * y * y / 4 - 15 * y * y * y / 8);
  }
  return x < 0 ? -r : r;
}
const Phi = (x) => 0.5 * (1 + erf(x / Math.SQRT2));

// Regularised lower incomplete gamma P(a, x): series for x < a + 1, continued fraction (modified Lentz) otherwise
function gammaP(a, x) {
  if (x <= 0) return 0;
  const lg = lgamma(a), tiny = 1e-300;
  if (x < a + 1) {
    let ap = a, del = 1 / a, sum = del;
    for (let i = 0; i < 100000; i++) {
      ap += 1; del *= x / ap; sum += del;
      if (Math.abs(del) < Math.abs(sum) * 1e-15) break;
    }
    return sum * Math.exp(-x + a * Math.log(x) - lg);
  }
  let b = x + 1 - a, c = 1 / tiny, d = 1 / b, h = d;
  for (let i = 1; i < 100000; i++) {
    const an = -i * (i - a);
    b += 2;
    d = an * d + b; if (Math.abs(d) < tiny) d = tiny;
    c = b + an / c; if (Math.abs(c) < tiny) c = tiny;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-15) break;
  }
  return 1 - Math.exp(-x + a * Math.log(x) - lg) * h;
}

// Regularised incomplete beta I_x(a, b) (continued fraction, modified Lentz) and Beta quantile by bisection
function betaCF(x, a, b) {
  const tiny = 1e-300, qab = a + b, qap = a + 1, qam = a - 1;
  let c = 1, d = 1 - qab * x / qap;
  if (Math.abs(d) < tiny) d = tiny;
  d = 1 / d;
  let h = d;
  for (let m = 1; m < 100000; m++) {
    const m2 = 2 * m;
    let aa = m * (b - m) * x / ((qam + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < tiny) d = tiny;
    c = 1 + aa / c; if (Math.abs(c) < tiny) c = tiny;
    d = 1 / d; h *= d * c;
    aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2));
    d = 1 + aa * d; if (Math.abs(d) < tiny) d = tiny;
    c = 1 + aa / c; if (Math.abs(c) < tiny) c = tiny;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-15) break;
  }
  return h;
}
function betaI(x, a, b) {
  if (x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? bt * betaCF(x, a, b) / a : 1 - bt * betaCF(1 - x, b, a) / b;
}
function betaQuantile(p, a, b) {
  let lo = 0, hi = 1;
  for (let i = 0; i < 80; i++) { const mid = (lo + hi) / 2; if (betaI(mid, a, b) < p) lo = mid; else hi = mid; }
  return (lo + hi) / 2;
}
const betaPdf = (x, a, b) => Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + (a - 1) * Math.log(x) + (b - 1) * Math.log(1 - x));

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
const fp = (v) => v.toFixed(3);                                                                    // probabilities
const pct = (v) => (100 * v).toFixed(v < 0.001 ? 3 : v < 0.1 ? 2 : 1) + "%";

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

/* ---------------------------------------------------------------------
   3. Computations
   --------------------------------------------------------------------- */

/* ---- Exercise 1 ---- */

const CP_ALL = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000];
function checkpoints(N) {
  const c = CP_ALL.filter((n) => n <= N);
  if (c[c.length - 1] !== N) c.push(N);
  return c;
}

// Exact sup_z |P(Z_n <= z) - Phi(z)| for Z_n = (S_n - n)/sqrt(n), S_n ~ Gamma(n, 1) (sum of n Exp(1) variables); grid of step 0.01
function ksExactExp(n) {
  let best = 0;
  for (let i = -500; i <= 500; i++) {
    const z = i / 100, x = n + z * Math.sqrt(n);
    const G = x > 0 ? gammaP(n, x) : 0;
    best = Math.max(best, Math.abs(G - Phi(z)));
  }
  return best;
}

// X_i ~ Exp(1): mu = 1, sigma = 1. m independent runs of length N, statistics at the checkpoints.
function runConvergence(cfg) {
  const { seed, m, N, eps } = cfg;
  const rng = mulberry32(seed), cps = checkpoints(N), K = cps.length;
  const slot = new Int32Array(N + 1).fill(-1);
  cps.forEach((n, i) => { slot[n] = i; });
  const xbar = cps.map(() => new Float64Array(m));
  const tailCount = new Float64Array(K);
  const mean = new Float64Array(N);
  let path = null;
  for (let r = 0; r < m; r++) {
    let s = 0;
    for (let k = 1; k <= N; k++) {
      s -= Math.log(1 - rng());
      mean[k - 1] = s / k;
      if (slot[k] >= 0) xbar[slot[k]][r] = s / k;
    }
    if (r === 0) path = Float64Array.from(mean);
    let mx = 0;
    for (let k = N; k >= 1; k--) {              // running maximum of |mean_k - mu| over k >= n
      const d = Math.abs(mean[k - 1] - 1);
      if (d > mx) mx = d;
      if (slot[k] >= 0 && mx > eps) tailCount[slot[k]]++;
    }
  }
  const rows = cps.map((n, i) => {
    const x = xbar[i];
    let pc = 0, se = 0;
    for (let r = 0; r < m; r++) { const d = x[r] - 1; if (Math.abs(d) > eps) pc++; se += d * d; }
    const z = Float64Array.from(x, (v) => (v - 1) * Math.sqrt(n)).sort();
    let ks = 0;
    for (let r = 0; r < m; r++) { const F = Phi(z[r]); ks = Math.max(ks, (r + 1) / m - F, F - r / m); }
    return { n, pProb: pc / m, pTail: tailCount[i] / m, mse: se / m, ks, ksExact: ksExactExp(n), sdXbar: sampleSd(x) };
  });
  return { cps, rows, path };
}

// Equicorrelated Gaussian variables: X_i = sqrt(rho) W + sqrt(1 - rho) e_i, so Xbar_n = sqrt(rho) W + sqrt((1 - rho)/n) G exactly
function runDependence(cfg, cps) {
  const { seed, m, rho } = cfg, nrm = normalGen(mulberry32(seed + 3));
  return cps.map((n) => {
    const v = new Float64Array(m);
    for (let r = 0; r < m; r++) { const w = nrm(), gg = nrm(); v[r] = Math.sqrt(rho) * w + Math.sqrt((1 - rho) / n) * gg; }
    const sd = sampleSd(v);
    return { n, sdXbar: sd, sdRoot: Math.sqrt(n) * sd, theoryRoot: Math.sqrt(n * rho + 1 - rho), limit: Math.sqrt(rho) };
  });
}

// Typewriter sequence on [0, 1]: block k holds the indicators of the 2^k dyadic intervals of length 2^-k
function runTypewriter(seed, K = 12) {
  const omega = mulberry32(seed + 1)();
  const rows = [];
  for (let k = 1; k <= K; k++) {
    const first = Math.pow(2, k);
    rows.push({ k, first, last: 2 * first - 1, p: 1 / first, hit: first + Math.floor(omega * first) });
  }
  return { omega, rows };
}

// Y_n = -X with X ~ N(0, 1): Y_n has the law of X for every n, but |Y_n - X| = 2|X| does not shrink
function runDistOnly(cfg) {
  const nrm = normalGen(mulberry32(cfg.seed + 2));
  let c = 0;
  for (let r = 0; r < cfg.m; r++) if (Math.abs(2 * nrm()) > cfg.eps) c++;
  return { sim: c / cfg.m, exact: 2 * (1 - Phi(cfg.eps / 2)) };
}

/* ---- Exercise 2 ---- */

// Posterior probability of an attack after k independent alerts (conditional independence given the state)
function posteriorAttack(prior, tpr, fpr, k) {
  let p = prior;
  for (let i = 0; i < k; i++) { const num = tpr * p; p = num / (num + fpr * (1 - p)); }
  return p;
}
const logSpace = (lo, hi, n) => Array.from({ length: n }, (_, i) => lo * Math.pow(hi / lo, i / (n - 1)));

const PRIORS = [
  { name: "Uniform, Beta(1, 1)", short: "uniform", a: 1, b: 1, color: PAL.main },
  { name: "Jeffreys, Beta(0.5, 0.5)", short: "Jeffreys", a: 0.5, b: 0.5, color: PAL.green },
  { name: "Informative, mean 0.30, Beta(6, 14)", short: "mean 0.30", a: 6, b: 14, color: PAL.orange },
  { name: "Informative, mean 0.70, Beta(14, 6)", short: "mean 0.70", a: 14, b: 6, color: PAL.red },
];
const BCP = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000];

// Bernoulli(theta) data, conjugate Beta posteriors for every prior, at n = 10, at n and at the checkpoints
function runBeta(cfg) {
  const { seed, theta, n } = cfg, rng = mulberry32(seed);
  const cum = new Uint32Array(n + 1);
  for (let i = 1; i <= n; i++) cum[i] = cum[i - 1] + (rng() < theta ? 1 : 0);
  const nSmall = 10;
  const cps = BCP.filter((v) => v <= n);
  if (cps[cps.length - 1] !== n) cps.push(n);
  const post = (pr, m) => {
    const a = pr.a + cum[m], b = pr.b + m - cum[m];
    const lo = betaQuantile(0.025, a, b), hi = betaQuantile(0.975, a, b);
    return { a, b, k: cum[m], n: m, mean: a / (a + b), lo, hi, width: hi - lo };
  };
  return {
    nSmall, cps, cum,
    small: PRIORS.map((pr) => post(pr, nSmall)),
    full: PRIORS.map((pr) => post(pr, n)),
    seq: PRIORS.map((pr) => cps.map((m) => post(pr, m))),
  };
}
function betaCurve(a, b) {
  const pts = [];
  for (let i = 0; i < 400; i++) { const x = (i + 0.5) / 400; pts.push([x, betaPdf(x, a, b)]); }
  return pts;
}

/* ---------------------------------------------------------------------
   4. Rendering
   --------------------------------------------------------------------- */

function renderConvergence(res, cfg) {
  const { rows, path } = res;
  $("convTable").innerHTML = table(
    ["n", "P(|X&#772;<sub>n</sub> &minus; &mu;| &gt; &epsilon;)", "P(sup<sub>k&ge;n</sub> |X&#772;<sub>k</sub> &minus; &mu;| &gt; &epsilon;)",
     "E(X&#772;<sub>n</sub> &minus; &mu;)&sup2;", "&sigma;&sup2;/n", "KS distance, simulated", "KS distance, exact"],
    rows.map((r) => [fmtInt(r.n), fp(r.pProb), fp(r.pTail), ge(r.mse), ge(1 / r.n), fp(r.ks), ge(r.ksExact)]), "compact");
  $("convNote").textContent =
    `Each row uses the same ${fmtInt(cfg.m)} runs. A simulated probability has Monte Carlo standard error at most ${(0.5 / Math.sqrt(cfg.m)).toFixed(3)}; ` +
    `the simulated KS distance has noise of order ${(0.87 / Math.sqrt(cfg.m)).toFixed(3)} even when the limit is exact, so only the exact column shows the true rate.`;

  plot($("cvProb"), {
    title: "Probability and a.s. proxy", xlabel: "n (log scale)", ylabel: "probability", xlog: true, ymin: 0, ymax: 1,
    series: [
      { name: "single n (in probability)", color: PAL.main, width: 2, markers: true, pts: rows.map((r) => [r.n, r.pProb]) },
      { name: "all k \u2265 n (a.s. proxy)", color: PAL.red, width: 2, markers: true, pts: rows.map((r) => [r.n, r.pTail]) },
    ],
  });
  plot($("cvMse"), {
    title: "Mean-square error", xlabel: "n (log scale)", ylabel: "E(mean \u2212 \u03bc)\u00b2", xlog: true, ylog: true,
    series: [
      { name: "simulated", color: PAL.main, width: 2, markers: true, pts: rows.map((r) => [r.n, r.mse]) },
      { name: "\u03c3\u00b2 / n", color: PAL.red, width: 1.5, dash: true, pts: rows.map((r) => [r.n, 1 / r.n]) },
    ],
  });
  plot($("cvKs"), {
    title: "Distance of Z\u2099 from N(0, 1)", xlabel: "n (log scale)", ylabel: "KS distance", xlog: true, ylog: true,
    series: [
      { name: "simulated", color: PAL.main, width: 2, markers: true, pts: rows.map((r) => [r.n, r.ks]) },
      { name: "exact (Gamma law)", color: PAL.green, width: 2, markers: true, pts: rows.map((r) => [r.n, r.ksExact]) },
      { name: "Monte Carlo noise level", color: PAL.orange, width: 1.5, dash: true, pts: rows.map((r) => [r.n, 0.87 / Math.sqrt(cfg.m)]) },
    ],
  });
  const N = path.length, idx = [];
  for (const v of logSpace(1, N, 300)) { const k = Math.round(v); if (idx[idx.length - 1] !== k) idx.push(k); }
  plot($("cvPath"), {
    title: "One sample path of the sample mean", xlabel: "k (log scale)", ylabel: "mean of first k samples", xlog: true,
    ymin: 1 - 4 * cfg.eps, ymax: 1 + 4 * cfg.eps,
    series: [
      { name: "run 1", color: PAL.main, width: 1.5, pts: idx.map((k) => [k, path[k - 1]]) },
      { name: "\u03bc", color: PAL.green, width: 1.5, dash: true, pts: [[1, 1], [N, 1]] },
      { name: "\u03bc \u00b1 \u03b5", color: PAL.red, width: 1.5, dash: true, pts: [[1, 1 + cfg.eps], [N, 1 + cfg.eps]] },
      { color: PAL.red, width: 1.5, dash: true, pts: [[1, 1 - cfg.eps], [N, 1 - cfg.eps]] },
    ],
  });
}

function renderCounterexamples(tw, dist, cfg) {
  $("twTable").innerHTML = table(
    ["Block k", "Indices n", "P(X<sub>n</sub> = 1)", "Index n with X<sub>n</sub>(&omega;) = 1"],
    tw.rows.map((r) => [r.k, `${fmtInt(r.first)} &ndash; ${fmtInt(r.last)}`, g(r.p, 3), fmtInt(r.hit)]), "compact");
  $("twOmega").textContent = tw.omega.toFixed(6);
  $("distTable").innerHTML = table(
    ["&epsilon;", "P(|Y<sub>n</sub> &minus; X| &gt; &epsilon;), simulated", "P(|Y<sub>n</sub> &minus; X| &gt; &epsilon;), exact 2(1 &minus; &Phi;(&epsilon;/2))", "Depends on n?"],
    [[g(cfg.eps), fp(dist.sim), fp(dist.exact), "no"]], "compact");
}

function renderScaling(res, dep, cfg) {
  const { rows } = res;
  $("scaleTable").innerHTML = table(
    ["n", "sd(S<sub>n</sub>) (theory &sigma;&radic;n)", "sd(S<sub>n</sub>/&radic;n) (theory &sigma;)", "sd(S<sub>n</sub>/n) (theory &sigma;/&radic;n)"],
    rows.map((r) => [fmtInt(r.n), `${g(r.n * r.sdXbar)} (${g(Math.sqrt(r.n))})`, `${g(Math.sqrt(r.n) * r.sdXbar)} (1)`, `${g(r.sdXbar)} (${g(1 / Math.sqrt(r.n))})`]), "compact");
  $("depTable").innerHTML = table(
    ["n", "independent: sd(&radic;n&middot;X&#772;<sub>n</sub>) (theory 1)", "equicorrelated: sd(&radic;n&middot;X&#772;<sub>n</sub>) (theory &radic;(n&rho; + 1 &minus; &rho;))", "equicorrelated: sd(X&#772;<sub>n</sub>) (limit &radic;&rho;)"],
    rows.map((r, i) => [fmtInt(r.n), g(Math.sqrt(r.n) * r.sdXbar), `${g(dep[i].sdRoot)} (${g(dep[i].theoryRoot)})`, `${g(dep[i].sdXbar)} (${g(dep[i].limit)})`]), "compact");

  plot($("cvScale"), {
    title: "Standard deviation of S\u2099 / n\u1D43, independent data", xlabel: "n (log scale)", ylabel: "standard deviation", xlog: true, ylog: true,
    series: [
      { name: "a = 0", color: PAL.red, width: 2, markers: true, pts: rows.map((r) => [r.n, r.n * r.sdXbar]) },
      { color: PAL.red, width: 1, dash: true, pts: rows.map((r) => [r.n, Math.sqrt(r.n)]) },
      { name: "a = 1/2", color: PAL.green, width: 2, markers: true, pts: rows.map((r) => [r.n, Math.sqrt(r.n) * r.sdXbar]) },
      { color: PAL.green, width: 1, dash: true, pts: rows.map((r) => [r.n, 1]) },
      { name: "a = 1", color: PAL.main, width: 2, markers: true, pts: rows.map((r) => [r.n, r.sdXbar]) },
      { color: PAL.main, width: 1, dash: true, pts: rows.map((r) => [r.n, 1 / Math.sqrt(r.n)]) },
    ],
  });
  plot($("cvDep"), {
    title: "Standard deviation of \u221an\u00b7(mean), two dependence structures", xlabel: "n (log scale)", ylabel: "standard deviation", xlog: true, ylog: true,
    series: [
      { name: "independent", color: PAL.green, width: 2, markers: true, pts: rows.map((r) => [r.n, Math.sqrt(r.n) * r.sdXbar]) },
      { name: "equicorrelated", color: PAL.red, width: 2, markers: true, pts: dep.map((d) => [d.n, d.sdRoot]) },
      { name: "theory, equicorrelated", color: PAL.red, width: 1, dash: true, pts: dep.map((d) => [d.n, d.theoryRoot]) },
    ],
  });
}

function renderAttack(cfg) {
  const { prior, tpr, fpr } = cfg;
  const set = [prior, 0.0001, 0.001, 0.01, 0.1, 0.5].filter((v, i, arr) => arr.indexOf(v) === i);
  $("attackTable").innerHTML = table(
    ["Prior P(attack)", "Evidence P(alert)", "Posterior after 1 alert", "Posterior after 2 alerts", "Posterior after 3 alerts"],
    set.map((p, i) => [`${pct(p)}${i === 0 ? " (input)" : ""}`, fp(tpr * p + fpr * (1 - p)),
      pct(posteriorAttack(p, tpr, fpr, 1)), pct(posteriorAttack(p, tpr, fpr, 2)), pct(posteriorAttack(p, tpr, fpr, 3))]), "compact");

  const px = logSpace(1e-4, 0.99, 80);
  plot($("cvAttackPrior"), {
    title: "Posterior against prior", xlabel: "prior P(attack) (log scale)", ylabel: "posterior P(attack | alerts)", xlog: true, ymin: 0, ymax: 1,
    series: [
      { name: "after 1 alert", color: PAL.main, width: 2, pts: px.map((p) => [p, posteriorAttack(p, tpr, fpr, 1)]) },
      { name: "after 2 alerts", color: PAL.green, width: 2, pts: px.map((p) => [p, posteriorAttack(p, tpr, fpr, 2)]) },
      { name: "no update (posterior = prior)", color: PAL.red, width: 1.5, dash: true, pts: px.map((p) => [p, p]) },
    ],
  });
  const fx = logSpace(1e-3, 0.5, 80), pri = [0.001, 0.01, 0.1];
  if (!pri.includes(prior)) pri.push(prior);
  plot($("cvAttackFpr"), {
    title: "Posterior against false-positive rate", xlabel: "P(alert | no attack) (log scale)", ylabel: "P(attack | 1 alert)", xlog: true, ymin: 0, ymax: 1,
    series: pri.map((p, j) => ({ name: `prior ${pct(p)}`, color: fnColor(j * 3 + 2), width: 2, pts: fx.map((f) => [f, posteriorAttack(p, tpr, f, 1)]) })),
  });
  $("dPrior").textContent = pct(prior);
  $("dTpr").textContent = pct(tpr);
  $("dFpr").textContent = pct(fpr);
  $("dPost").textContent = pct(posteriorAttack(prior, tpr, fpr, 1));
}

function renderBeta(res, cfg) {
  const { small, full, seq, cps, nSmall, cum } = res, n = cfg.n;
  const row = (pr, p) => [pr.name, fmtInt(p.n), p.k, fp(p.k / p.n), `Beta(${g(p.a)}, ${g(p.b)})`, fp(p.mean), `[${fp(p.lo)}, ${fp(p.hi)}]`, fp(p.width)];
  $("betaTable").innerHTML = table(
    ["Prior", "n", "k", "MLE k/n", "Posterior", "Posterior mean", "95% credible interval", "Width"],
    [...PRIORS.map((pr, i) => row(pr, small[i])), ...PRIORS.map((pr, i) => row(pr, full[i]))], "compact");

  const trueLine = (ymax) => ({ name: "true \u03b8", color: PAL.blue, width: 1.5, dash: true, pts: [[cfg.theta, 0], [cfg.theta, ymax]] });
  const dens = (list, title, id) => {
    const curves = list.map((p) => betaCurve(p.a, p.b));
    const ymax = Math.max(...curves.map((c) => Math.max(...c.map((q) => q[1]))));
    plot($(id), {
      title, xlabel: "\u03b8", ylabel: "posterior density", xmin: 0, xmax: 1, ymin: 0, ymax: ymax * 1.05,
      series: [...PRIORS.map((pr, i) => ({ name: pr.short, color: pr.color, width: 2, pts: curves[i] })), trueLine(ymax * 1.05)],
    });
  };
  dens(small, `Posterior densities, n = ${nSmall}`, "cvBetaSmall");
  dens(full, `Posterior densities, n = ${fmtInt(n)}`, "cvBetaFull");

  plot($("cvBetaMean"), {
    title: "Posterior mean as data accumulate", xlabel: "n (log scale)", ylabel: "estimate of \u03b8", xlog: true, ymin: 0, ymax: 1,
    series: [
      ...PRIORS.map((pr, i) => ({ name: pr.short, color: pr.color, width: 2, markers: true, pts: seq[i].map((p) => [p.n, p.mean]) })),
      { name: "MLE k/n", color: PAL.blue, width: 1.5, dash: true, pts: cps.map((m) => [m, cum[m] / m]) },
      { name: "true \u03b8", color: "#adb5bd", width: 1.5, dash: true, pts: [[1, cfg.theta], [n, cfg.theta]] },
    ],
  });
  plot($("cvBetaWidth"), {
    title: "Width of the 95% credible interval", xlabel: "n (log scale)", ylabel: "width", xlog: true, ylog: true,
    series: [
      ...PRIORS.map((pr, i) => ({ name: pr.short, color: pr.color, width: 2, markers: true, pts: seq[i].map((p) => [p.n, p.width]) })),
      { name: "1 / \u221an", color: "#adb5bd", width: 1.5, dash: true, pts: cps.map((m) => [m, 1 / Math.sqrt(m)]) },
    ],
  });
}

/* ---------------------------------------------------------------------
   5. Controls
   --------------------------------------------------------------------- */

function readNumber(id) {
  const raw = String($(id).value).trim();
  return raw === "" ? NaN : Number(raw);
}
function validSeed(id) {
  const seed = readNumber(id);
  return Number.isInteger(seed) && seed >= 0 && seed <= 4294967295 ? seed : null;
}

function parseConfig() {
  const seed = validSeed("seedInput"), m = readNumber("mInput"), N = readNumber("nInput"), eps = readNumber("epsInput"), rho = readNumber("rhoInput");
  if (seed === null) return "The seed must be an integer between 0 and 4294967295.";
  if (!Number.isInteger(m) || m < 100 || m > 20000) return "The number of runs m must be an integer between 100 and 20000.";
  if (!Number.isInteger(N) || N < 10 || N > 100000) return "The maximum sample size n must be an integer between 10 and 100000.";
  if (m * N > 1e8) return "The product m \u00d7 n must not exceed 100,000,000.";
  if (!(eps >= 0.01 && eps <= 1)) return "The tolerance \u03b5 must be a number between 0.01 and 1.";
  if (!(rho >= 0 && rho <= 0.99)) return "The correlation \u03c1 must be a number between 0 and 0.99.";
  return { seed, m, N, eps, rho };
}

function parseBayesConfig() {
  const seed = validSeed("bayesSeed"), prior = readNumber("priorInput"), tpr = readNumber("tprInput"), fpr = readNumber("fprInput");
  const theta = readNumber("thetaInput"), n = readNumber("obsInput");
  if (seed === null) return "The seed must be an integer between 0 and 4294967295.";
  if (!(prior > 0 && prior < 1)) return "The prior P(attack) must be a number strictly between 0 and 1.";
  if (!(tpr > 0 && tpr <= 1)) return "The detection rate P(alert | attack) must be a number in (0, 1].";
  if (!(fpr >= 0 && fpr <= 1)) return "The false-positive rate P(alert | no attack) must be a number in [0, 1].";
  if (!(theta > 0 && theta < 1)) return "The true success probability \u03b8 must be a number strictly between 0 and 1.";
  if (!Number.isInteger(n) || n < 20 || n > 5000) return "The number of observations n must be an integer between 20 and 5000.";
  return { seed, prior, tpr, fpr, theta, n };
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
  await tick();
  const t0 = performance.now();
  try {
    const res = runConvergence(cfg);
    renderConvergence(res, cfg);
    await tick();
    renderCounterexamples(runTypewriter(cfg.seed), runDistOnly(cfg), cfg);
    renderScaling(res, runDependence(cfg, res.cps), cfg);
    $("simStatus").textContent = `Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    showMsg("jsError", "Error during the computation: " + err.message);
  }
  running = false;
  $("btnRun").disabled = false; $("btnSeed").disabled = false;
}

let runningBayes = false;
async function runBayes() {
  if (runningBayes) return;
  const cfg = parseBayesConfig();
  if (typeof cfg === "string") { showMsg("bayesError", cfg); return; }
  hideMsg("bayesError");
  runningBayes = true;
  $("btnBayes").disabled = true; $("btnBayesSeed").disabled = true;
  $("bayesStatus").textContent = "Computing...";
  await tick();
  const t0 = performance.now();
  try {
    renderAttack(cfg);
    renderBeta(runBeta(cfg), cfg);
    $("bayesStatus").textContent = `Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    showMsg("jsError", "Error during the computation: " + err.message);
  }
  runningBayes = false;
  $("btnBayes").disabled = false; $("btnBayesSeed").disabled = false;
}

const randomSeed = () => String(crypto.getRandomValues(new Uint32Array(1))[0] >>> 1);

function init() {
  $("btnRun").addEventListener("click", run);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = randomSeed(); run(); });
  $("btnBayes").addEventListener("click", runBayes);
  $("btnBayesSeed").addEventListener("click", () => { $("bayesSeed").value = randomSeed(); runBayes(); });
  run();
  runBayes();
}

document.addEventListener("DOMContentLoaded", init);
