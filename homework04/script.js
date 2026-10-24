"use strict";

/* =====================================================================
   HMWK 4 - n systems, m attackers: Law of Large Numbers and Central Limit
   Theorem by simulation (Bernoulli and Rademacher scores).
   Pure JavaScript, no external libraries.
   ===================================================================== */

const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");
const sum = (a) => a.reduce((s, v) => s + v, 0);
const fmtInt = (v) => Math.round(v).toLocaleString("en-US");

// Number with about d significant digits, in plain or exponential notation
const g = (v, d = 4) => {
  if (!Number.isFinite(v)) return "n/a";
  if (v === 0) return "0";
  const a = Math.abs(v);
  return a >= 1e5 || a < 1e-3 ? v.toExponential(2) : String(Number(v.toPrecision(d)));
};

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

/* ---------------------------------------------------------------------
   1. Mathematical helpers
   --------------------------------------------------------------------- */

// Error function, Abramowitz & Stegun formula 7.1.26 (absolute error below 1.5e-7)
function erf(x) {
  const a = Math.abs(x);
  const t = 1 / (1 + 0.3275911 * a);
  const poly = ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t;
  return Math.sign(x) * (1 - poly * Math.exp(-a * a));
}
const normCdf = (x) => 0.5 * (1 + erf(x / Math.SQRT2));
const normPdf = (x) => Math.exp(-0.5 * x * x) / Math.sqrt(2 * Math.PI);
function normInv(p) { // bisection on the normal CDF, p in (0, 1)
  let lo = -12, hi = 12;
  for (let i = 0; i < 80; i++) { const mid = (lo + hi) / 2; if (normCdf(mid) < p) lo = mid; else hi = mid; }
  return (lo + hi) / 2;
}

function moments(a) {
  const n = a.length;
  let m1 = 0;
  for (let i = 0; i < n; i++) m1 += a[i];
  m1 /= n;
  let m2 = 0, m3 = 0, m4 = 0;
  for (let i = 0; i < n; i++) { const d = a[i] - m1, d2 = d * d; m2 += d2; m3 += d2 * d; m4 += d2 * d2; }
  m2 /= n; m3 /= n; m4 /= n;
  return { mean: m1, varU: (m2 * n) / (n - 1), skew: m2 > 0 ? m3 / Math.pow(m2, 1.5) : NaN, kurt: m2 > 0 ? m4 / (m2 * m2) - 3 : NaN };
}

// Exact Kolmogorov-Smirnov distance between the standardised Binomial(n, p) and N(0, 1)
function exactKS(n, p) {
  const s = Math.sqrt(n * p * (1 - p)), mu = n * p, lr = Math.log(p / (1 - p));
  let logp = n * Math.log(1 - p), F = 0, D = 0;
  for (let k = 0; k <= n; k++) {
    const prevF = F;
    F += Math.exp(logp);
    const ph = normCdf((k - mu) / s);
    D = Math.max(D, Math.abs(F - ph), Math.abs(prevF - ph));
    logp += Math.log((n - k) / (k + 1)) + lr;
  }
  return D;
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
  const ctx = canvas.getContext("2d");
  const W = canvas.width, H = canvas.height;
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
  const L = 68, R = 18, T = 34, B = 46 + rows.length * 17;
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
    if (s.bars) {
      ctx.fillStyle = s.color;
      for (const b of s.bars) ctx.fillRect(X(b[0]), Y(b[2]), Math.max(1, X(b[1]) - X(b[0]) - 1), Y(0) - Y(b[2]));
    }
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
      if (s.markers) for (const p of s.pts) if (okv(p[0], o.xlog) && okv(p[1], o.ylog)) { ctx.beginPath(); ctx.arc(X(p[0]), Y(p[1]), 3.5, 0, Math.PI * 2); ctx.fill(); }
    }
  }
  ctx.globalAlpha = 1;
  for (const v of o.vlines || []) {
    ctx.strokeStyle = v.color || "#000"; ctx.lineWidth = 1.5; ctx.setLineDash(v.dash ? [6, 4] : []);
    ctx.beginPath(); ctx.moveTo(X(v.x), T); ctx.lineTo(X(v.x), T + ph); ctx.stroke(); ctx.setLineDash([]);
  }
  ctx.restore();

  // legend
  ctx.font = "11px sans-serif"; ctx.textAlign = "left";
  rows.forEach((row, ri) => {
    let lx = L, ly = H - 8 - (rows.length - 1 - ri) * 17;
    for (const [s, w] of row) {
      ctx.strokeStyle = s.color; ctx.fillStyle = s.color; ctx.lineWidth = 2;
      ctx.setLineDash(s.dash ? [5, 3] : []);
      if (s.bars) ctx.fillRect(lx, ly - 9, 18, 9);
      else { ctx.beginPath(); ctx.moveTo(lx, ly - 4); ctx.lineTo(lx + 18, ly - 4); ctx.stroke(); }
      ctx.setLineDash([]);
      if (s.markers) { ctx.beginPath(); ctx.arc(lx + 9, ly - 4, 3.5, 0, Math.PI * 2); ctx.fill(); }
      ctx.fillStyle = "#212529"; ctx.fillText(s.name, lx + 24, ly);
      lx += w;
    }
  });
}

const seqColor = (i, len) => `hsl(210, 75%, ${78 - 52 * (len > 1 ? i / (len - 1) : 1)}%)`;
const pathColor = (j) => `hsl(${(j * 47) % 360}, 60%, 42%)`;

/* ---------------------------------------------------------------------
   3. Simulation
   m attackers; attacker j has i.i.d. scores X_1, X_2, ... and the partial sums are
   recorded at the chosen sizes n and, for the first nPaths attackers, along the path.
   --------------------------------------------------------------------- */

async function simulate(cfg, progress) {
  const { model, p, m, ns, seed, nPaths } = cfg;
  const nmax = ns[ns.length - 1];
  const thr = model === "rad" ? 2147483648 : Math.floor(p * 4294967296);   // P(X = 1) = thr / 2^32
  const down = model === "rad" ? -1 : 0;                                    // value of X when it is not +1

  const K = Math.min(nmax, 400);
  const pathSet = new Set();
  for (let i = 1; i <= K; i++) pathSet.add(Math.max(1, Math.round((i * nmax) / K)));
  const pathKs = [...pathSet].sort((a, b) => a - b);
  const stops = [...new Set([...ns, ...pathKs])].sort((a, b) => a - b);
  const nsIndex = new Map(ns.map((n, i) => [n, i]));
  const pathIndex = new Map(pathKs.map((k, i) => [k, i]));

  const S = ns.map(() => new Float64Array(m));
  const paths = [];
  let a = seed | 0;                                    // state of the mulberry32 generator
  const chunk = Math.max(1, Math.floor(4e6 / nmax));
  for (let j0 = 0; j0 < m; j0 += chunk) {
    const j1 = Math.min(m, j0 + chunk);
    for (let j = j0; j < j1; j++) {
      let s = 0, prev = 0;
      if (j < nPaths) {
        const rec = new Float64Array(pathKs.length);
        for (const stop of stops) {
          for (let k = prev; k < stop; k++) {
            a = (a + 0x6D2B79F5) | 0;
            let t = Math.imul(a ^ (a >>> 15), 1 | a);
            t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
            s += ((t ^ (t >>> 14)) >>> 0) < thr ? 1 : down;
          }
          prev = stop;
          const ci = nsIndex.get(stop); if (ci !== undefined) S[ci][j] = s;
          const pi = pathIndex.get(stop); if (pi !== undefined) rec[pi] = s;
        }
        paths.push(rec);
      } else {
        for (let c = 0; c < ns.length; c++) {
          const end = ns[c];
          for (let k = prev; k < end; k++) {
            a = (a + 0x6D2B79F5) | 0;
            let t = Math.imul(a ^ (a >>> 15), 1 | a);
            t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
            s += ((t ^ (t >>> 14)) >>> 0) < thr ? 1 : down;
          }
          prev = end;
          S[c][j] = s;
        }
      }
    }
    progress(j1 / m);
    await tick();
  }
  const mu = model === "rad" ? 0 : p, sigma2 = model === "rad" ? 1 : p * (1 - p);
  return { ...cfg, S, pathKs, paths, mu, sigma2, sigma: Math.sqrt(sigma2), pEff: model === "rad" ? 0.5 : p, hStep: model === "rad" ? 2 : 1 };
}

function analyse(sim) {
  const { ns, S, m, mu, sigma } = sim;
  return ns.map((n, c) => {
    const sorted = Float64Array.from(S[c]).sort();
    const Z = Float64Array.from(sorted, (v) => (v - n * mu) / (sigma * Math.sqrt(n)));
    const ms = moments(S[c]), mz = moments(Z);
    let D = 0;
    for (let i = 0; i < m; i++) { const ph = normCdf(Z[i]); D = Math.max(D, Math.abs((i + 1) / m - ph), Math.abs(i / m - ph)); }
    return { n, sorted, Z, meanS: ms.mean, varS: ms.varU, mz, ks: D };
  });
}

/* ---------------------------------------------------------------------
   4. Rendering of the sections
   --------------------------------------------------------------------- */

let SIM = null, AN = null;
const modelName = () => (SIM.model === "rad" ? "Rademacher" : `Bernoulli(${SIM.p})`);

function renderPaths() {
  const { pathKs, paths, mu, sigma } = SIM;
  const sets = paths.map((rec, j) => ({ color: pathColor(j), width: 1, alpha: 0.75, name: j === 0 ? `${paths.length} attackers` : undefined, rec }));
  const make = (f) => sets.map((s) => ({ ...s, pts: pathKs.map((k, i) => [k, f(s.rec[i], k)]) }));
  const theory = (fm, fs) => [
    { color: "#000000", width: 2, name: "theoretical mean", pts: pathKs.map((k) => [k, fm(k)]) },
    { color: "#e74c3c", width: 1.5, dash: true, name: "mean \u00b1 2 standard deviations", pts: pathKs.map((k) => [k, fm(k) + 2 * fs(k)]) },
    { color: "#e74c3c", width: 1.5, dash: true, pts: pathKs.map((k) => [k, fm(k) - 2 * fs(k)]) },
  ];
  plot($("cvPath1"), { title: `${modelName()}: total score S_k along the path of each attacker`, xlabel: "step k (number of systems attacked)", ylabel: "S_k",
    series: [...make((v) => v), ...theory((k) => k * mu, (k) => sigma * Math.sqrt(k))] });
  plot($("cvPath4"), { title: `${modelName()}: centred total score S_k - k\u00b5`, xlabel: "step k", ylabel: "S_k - k\u00b5",
    series: [...make((v, k) => v - k * mu), ...theory(() => 0, (k) => sigma * Math.sqrt(k))] });
  plot($("cvPath2"), { title: `${modelName()}: average score S_k / k`, xlabel: "step k", ylabel: "S_k / k",
    series: [...make((v, k) => v / k), ...theory(() => mu, (k) => sigma / Math.sqrt(k))] });
  plot($("cvPath3"), { title: `${modelName()}: normalised score S_k / \u221ak`, xlabel: "step k", ylabel: "S_k / \u221ak",
    series: [...make((v, k) => v / Math.sqrt(k)), ...theory((k) => mu * Math.sqrt(k), () => sigma)] });
}

function ecdfPts(sorted, f) {
  const m = sorted.length, step = Math.max(1, Math.floor(m / 300)), pts = [];
  for (let i = 0; i < m; i += step) pts.push([f(sorted[i]), (i + 1) / m]);
  pts.push([f(sorted[m - 1]), 1]);
  return pts;
}

function renderEcdfs() {
  const { ns, mu, sigma } = SIM;
  const len = ns.length;
  const build = (f) => AN.map((a, i) => ({ name: `n = ${fmtInt(a.n)}`, color: seqColor(i, len), width: 1.8, pts: ecdfPts(a.sorted, (v) => f(v, a.n)) }));
  const range = (f) => {
    let lo = Infinity, hi = -Infinity;
    for (const a of AN) { lo = Math.min(lo, f(a.sorted[0], a.n)); hi = Math.max(hi, f(a.sorted[a.sorted.length - 1], a.n)); }
    const pad = (hi - lo) * 0.03 || 1;
    return [lo - pad, hi + pad];
  };
  const phi = { name: "standard normal CDF", color: "#000000", width: 2, dash: true, pts: Array.from({ length: 181 }, (_, i) => [-4.5 + i * 0.05, normCdf(-4.5 + i * 0.05)]) };
  const fS = (v) => v, fAvg = (v, n) => v / n, fNorm = (v, n) => v / Math.sqrt(n), fZ = (v, n) => (v - n * mu) / (sigma * Math.sqrt(n));
  const base = { ymin: 0, ymax: 1, ylabel: "cumulative probability" };
  let r = range(fS);
  plot($("cvEcdfS"), { ...base, title: "ECDF of the total score S_n", xlabel: "S_n", xmin: r[0], xmax: r[1], series: build(fS) });
  r = range(fAvg);
  plot($("cvEcdfAvg"), { ...base, title: "ECDF of the average score S_n / n", xlabel: "S_n / n", xmin: r[0], xmax: r[1], series: build(fAvg), vlines: [{ x: mu, dash: true, color: "#000" }] });
  r = range(fNorm);
  const normSeries = build(fNorm);
  if (SIM.model === "rad") { normSeries.push(phi); r = [Math.min(r[0], -4.5), Math.max(r[1], 4.5)]; }
  plot($("cvEcdfNorm"), { ...base, title: "ECDF of the normalised score S_n / \u221an", xlabel: "S_n / \u221an", xmin: r[0], xmax: r[1], series: normSeries });
  $("normNote").innerHTML = SIM.model === "rad"
    ? "<strong>Normalised score, Rademacher case.</strong> Here &mu; = 0 and &sigma; = 1, so S<sub>n</sub>/&radic;n is already standardised. The curves have a constant spread and approach the standard normal CDF (black dashed line)."
    : `<strong>Normalised score, Bernoulli case.</strong> The spread is constant (standard deviation &sigma; = ${g(sigma, 3)}), but the centre &mu;&radic;n = ${g(mu, 3)}&radic;n moves to the right as n grows, so S<sub>n</sub>/&radic;n has no limit distribution. It has to be centred first, as in the next plot.`;
  plot($("cvEcdfZ"), { ...base, title: "ECDF of the standardised score Z_n = (S_n - n\u00b5) / (\u03c3\u221an)", xlabel: "Z_n", xmin: -4.5, xmax: 4.5, series: [...build(fZ), phi] });
}

function renderNSelect() {
  const sel = $("nSel");
  const prev = sel.value;
  sel.innerHTML = SIM.ns.map((n, i) => `<option value="${i}">n = ${fmtInt(n)}</option>`).join("");
  sel.value = prev !== "" && Number(prev) < SIM.ns.length ? prev : String(SIM.ns.length - 1);
}

function renderHist() {
  const c = Number($("nSel").value), a = AN[c], Z = a.Z, m = Z.length;
  const step = SIM.hStep / (SIM.sigma * Math.sqrt(a.n));                   // spacing of the values of Z_n
  const w = step * Math.ceil(0.25 / step - 1e-9);                           // bin width: a whole number of lattice steps
  const e0 = Z[0] - step / 2;
  const nb = Math.floor((Z[m - 1] - e0) / w + 1e-9) + 1;
  const cnt = new Array(nb).fill(0);
  for (let i = 0; i < m; i++) cnt[Math.min(nb - 1, Math.floor((Z[i] - e0) / w + 1e-9))]++;
  const bars = cnt.map((q, i) => [e0 + i * w, e0 + (i + 1) * w, q / (m * w)]);
  const curve = Array.from({ length: 181 }, (_, i) => [-4.5 + i * 0.05, normPdf(-4.5 + i * 0.05)]);
  plot($("cvHistZ"), {
    title: `Histogram of Z_n for n = ${fmtInt(a.n)} (${fmtInt(m)} attackers)`, xlabel: "Z_n", ylabel: "density", xmin: -4.5, xmax: 4.5, ymin: 0,
    series: [{ name: "simulated density", color: "#7fb3d5", bars }, { name: "standard normal density", color: "#e74c3c", width: 2, pts: curve }],
  });
  $("histNote").textContent = `Z_n takes values on a lattice of spacing ${g(step, 3)}; the bins have width ${g(w, 3)} and contain a whole number of lattice points. ` +
    `For small n the histogram is visibly discrete and, for Bernoulli with p far from 1/2, asymmetric; for large n it follows the bell curve.`;
}

function renderLLN() {
  const eps = Number($("epsInput").value);
  if (!(eps >= 0.005 && eps <= 0.9)) { $("llnTable").innerHTML = `<div class="text-danger small">The tolerance must be between 0.005 and 0.9.</div>`; return; }
  const { ns, S, m, mu, sigma, sigma2 } = SIM;
  const rows = [], emp = [], cheb = [], nrm = [];
  ns.forEach((n, c) => {
    let cntBad = 0;
    for (let j = 0; j < m; j++) if (Math.abs(S[c][j] / n - mu) > eps) cntBad++;
    const e = cntBad / m, ch = Math.min(1, sigma2 / (n * eps * eps)), nr = 2 * (1 - normCdf((eps * Math.sqrt(n)) / sigma));
    emp.push([n, e]); cheb.push([n, ch]); nrm.push([n, nr]);
    rows.push([fmtInt(n), g(e), g(ch), g(nr), g(sigma / Math.sqrt(n), 3)]);
  });
  plot($("cvLLN"), {
    title: `${modelName()}: P(|S_n/n - \u00b5| > ${eps}) as a function of n`, xlabel: "n (log scale)", ylabel: "probability", xlog: true, ymin: 0, ymax: 1,
    series: [
      { name: "simulated", color: "#2c3e50", width: 2, markers: true, pts: emp },
      { name: "Chebyshev bound \u03c3\u00b2 / (n\u03b5\u00b2)", color: "#e74c3c", dash: true, pts: cheb },
      { name: "normal approximation", color: "#18bc9c", dash: true, pts: nrm },
    ],
  });
  $("llnTable").innerHTML = table(["n", "Simulated P(|S<sub>n</sub>/n &minus; &mu;| &gt; &epsilon;)", "Chebyshev bound", "Normal approximation", "Standard deviation of S<sub>n</sub>/n"], rows, "compact");
  const delta = 0.05, z = normInv(1 - delta / 2);
  $("llnNote").innerHTML =
    `The simulated probability goes to 0 as n grows, which is convergence in probability. Its Monte Carlo error is at most ${g(0.5 / Math.sqrt(m), 2)}, so very small values are only meaningful as &ldquo;close to 0&rdquo;. ` +
    `To make this probability at most ${delta}, Chebyshev&rsquo;s inequality guarantees it for n &ge; ${fmtInt(Math.ceil(sigma2 / (delta * eps * eps)))}, whereas the normal approximation already suggests n &ge; ${fmtInt(Math.ceil(Math.pow((z * sigma) / eps, 2)))}: ` +
    `the bound is rigorous but very conservative.`;
}

function renderVar() {
  const { ns, sigma2 } = SIM;
  const rows = [], eS = [], eA = [], eN = [], tS = [], tA = [], tN = [];
  AN.forEach((a) => {
    const n = a.n;
    const vS = a.varS, vA = a.varS / (n * n), vN = a.varS / n;
    eS.push([n, vS]); eA.push([n, vA]); eN.push([n, vN]);
    tS.push([n, n * sigma2]); tA.push([n, sigma2 / n]); tN.push([n, sigma2]);
    rows.push([fmtInt(n), g(vS), g(n * sigma2), g(vA), g(sigma2 / n), g(vN), g(sigma2)]);
  });
  plot($("cvVar"), {
    title: `${modelName()}: variance of the three quantities (log-log scale)`, xlabel: "n", ylabel: "variance", xlog: true, ylog: true,
    series: [
      { name: "S_n, theory n\u03c3\u00b2", color: "#e74c3c", width: 1.5, dash: true, pts: tS },
      { name: "S_n, simulated", color: "#e74c3c", markers: true, line: false, pts: eS },
      { name: "S_n/n, theory \u03c3\u00b2/n", color: "#18bc9c", width: 1.5, dash: true, pts: tA },
      { name: "S_n/n, simulated", color: "#18bc9c", markers: true, line: false, pts: eA },
      { name: "S_n/\u221an, theory \u03c3\u00b2", color: "#2c3e50", width: 1.5, dash: true, pts: tN },
      { name: "S_n/\u221an, simulated", color: "#2c3e50", markers: true, line: false, pts: eN },
    ],
  });
  $("varTable").innerHTML = table(
    ["n", "Var(S<sub>n</sub>) simulated", "theory n&sigma;&sup2;", "Var(S<sub>n</sub>/n) simulated", "theory &sigma;&sup2;/n", "Var(S<sub>n</sub>/&radic;n) simulated", "theory &sigma;&sup2;"], rows, "compact") +
    `<p class="small text-muted mt-2 mb-0">Here &sigma;&sup2; = ${g(sigma2)}. The relative Monte Carlo error of a variance estimate is about &radic;(2/m) = ${g(Math.sqrt(2 / SIM.m) * 100, 2)} %.</p>`;
}

function renderCLT() {
  const { m, pEff } = SIM;
  const noise = 1.36 / Math.sqrt(m);
  const rows = AN.map((a) => {
    const n = a.n, v = n * pEff * (1 - pEff);
    const skewT = (1 - 2 * pEff) / Math.sqrt(v), kurtT = (1 - 6 * pEff * (1 - pEff)) / v;
    const ex = exactKS(n, pEff);
    return [fmtInt(n), `${g(a.mz.skew, 3)} / ${g(skewT, 3)}`, `${g(a.mz.kurt, 3)} / ${g(kurtT, 3)}`, g(a.ks, 3), g(ex, 3), g(ex * Math.sqrt(n), 3), g(noise, 3)];
  });
  $("cltTable").innerHTML = table(
    ["n", "Skewness: simulated / theory", "Excess kurtosis: simulated / theory", "KS distance, simulated", "KS distance, exact", "exact KS &times; &radic;n", "Sampling noise (95 %)"], rows, "compact");
  const first = AN[0], last = AN[AN.length - 1];
  const be = (pEff * pEff + (1 - pEff) * (1 - pEff)) / Math.sqrt(pEff * (1 - pEff));   // E|X - mu|^3 / sigma^3
  $("cltNote").innerHTML =
    `The KS distance falls from ${g(first.ks, 2)} at n = ${fmtInt(first.n)} to ${g(last.ks, 2)} at n = ${fmtInt(last.n)}: the distribution of Z<sub>n</sub> approaches the standard normal. ` +
    `The exact distance decreases like 1/&radic;n (the column exact KS &times; &radic;n is roughly constant), as predicted by the Berry&ndash;Esseen theorem, which guarantees KS &le; C&rho;/(&sigma;&sup3;&radic;n) with &rho; = E|X &minus; &mu;|&sup3; and C &lt; 0.4748: here exact KS &times; &radic;n &le; ${g(0.4748 * be, 3)}. ` +
    `Once the exact distance is below the sampling noise (${g(noise, 2)} with m = ${fmtInt(m)}), the simulation can no longer tell Z<sub>n</sub> from a normal variable; simulated skewness and kurtosis also carry a noise of about &radic;(6/m) = ${g(Math.sqrt(6 / m), 2)} and &radic;(24/m) = ${g(Math.sqrt(24 / m), 2)}. ` +
    (SIM.model === "rad"
      ? `In the Rademacher case Z<sub>n</sub> = S<sub>n</sub>/&radic;n, and the skewness is exactly 0 for every n.`
      : `In the Bernoulli case the skewness (1 &minus; 2p)/&radic;(np(1 &minus; p)) is not zero for p &ne; 1/2, which is why convergence is slower than in the symmetric case.`);
}

function renderAgg() {
  const c = Number($("nSel").value), n = SIM.ns[c], { S, m, mu, sigma } = SIM;
  const list = [...new Set([1, 10, 100, 1000, 10000, m].filter((v) => v <= m))].sort((a, b) => a - b);
  const rows = list.map((mp) => {
    let T = 0, best = -Infinity;
    for (let j = 0; j < mp; j++) { T += S[c][j]; if (S[c][j] > best) best = S[c][j]; }
    const E = mp * n * mu, SD = sigma * Math.sqrt(mp * n);
    const typical = n * mu + sigma * Math.sqrt(n) * normInv(Math.pow(0.5, 1 / mp));
    return [fmtInt(mp), fmtInt(T), fmtInt(E), g(SD, 4), g((T - E) / SD, 3), g(T / (mp * n), 4), fmtInt(best), g(typical, 4)];
  });
  $("aggTable").innerHTML = `<p class="small text-muted mb-2">Model: ${modelName()}, n = ${fmtInt(n)} systems per attacker.</p>` + table(
    ["Attackers m&prime;", "Aggregate score T", "Expected T = m&prime;n&mu;", "Std. dev. of T = &sigma;&radic;(m&prime;n)", "(T &minus; E[T]) / std. dev.", "Grand average T/(m&prime;n) (&mu; = " + g(mu, 3) + ")", "Best attacker (max S<sub>n</sub>)", "Typical best (normal approx.)"], rows, "compact");
}

function renderAll() {
  $("modelInfo").innerHTML = `Simulated: ${modelName()}, m = ${fmtInt(SIM.m)} attackers, n up to ${fmtInt(SIM.ns[SIM.ns.length - 1])}, seed ${SIM.seed}. ` +
    `&mu; = ${g(SIM.mu)}, &sigma;&sup2; = ${g(SIM.sigma2)}.`;
  renderPaths(); renderEcdfs(); renderNSelect(); renderHist(); renderLLN(); renderVar(); renderCLT(); renderAgg();
}

/* ---------------------------------------------------------------------
   5. Controls
   --------------------------------------------------------------------- */

function parseConfig() {
  const model = $("model").value;
  const p = Number($("pInput").value), m = Number($("mInput").value), seed = Number($("seedInput").value);
  const ns = String($("nList").value).split(/[\s,;]+/).filter(Boolean).map(Number);
  if (model === "bern" && !(p >= 0.01 && p <= 0.99)) return "p must be between 0.01 and 0.99.";
  if (!Number.isInteger(m) || m < 50 || m > 20000) return "The number of attackers m must be an integer between 50 and 20000.";
  if (!Number.isInteger(seed)) return "The seed must be an integer.";
  if (ns.some((v) => !Number.isInteger(v) || v < 1 || v > 100000)) return "Every n must be an integer between 1 and 100000.";
  const sorted = [...new Set(ns)].sort((a, b) => a - b);
  if (sorted.length < 2 || sorted.length > 8) return "Give between 2 and 8 different values of n.";
  if (m * sorted[sorted.length - 1] > 1e8) return "m times the largest n must be at most 100 million, to keep the simulation fast.";
  return { model, p, m, ns: sorted, seed, nPaths: Math.min(20, m) };
}

let running = false;
async function run() {
  if (running) return;
  const cfg = parseConfig();
  if (typeof cfg === "string") { showMsg("simError", cfg); return; }
  hideMsg("simError");
  running = true;
  $("btnRun").disabled = true; $("btnSeed").disabled = true;
  const t0 = performance.now();
  try {
    SIM = await simulate(cfg, (f) => { $("simStatus").textContent = `Simulating... ${Math.round(f * 100)} %`; });
    AN = analyse(SIM);
    renderAll();
    $("simStatus").textContent = `Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    showMsg("jsError", "Error during the simulation: " + err.message);
  }
  running = false;
  $("btnRun").disabled = false; $("btnSeed").disabled = false;
}

function init() {
  $("model").addEventListener("change", () => { $("pInput").disabled = $("model").value === "rad"; run(); });
  $("btnRun").addEventListener("click", run);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = String(crypto.getRandomValues(new Uint32Array(1))[0] >>> 1); run(); });
  $("btnEps").addEventListener("click", () => { if (SIM) renderLLN(); });
  $("nSel").addEventListener("change", () => { if (SIM) { renderHist(); renderAgg(); } });
  run();
}

document.addEventListener("DOMContentLoaded", init);
