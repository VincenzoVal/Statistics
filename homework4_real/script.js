"use strict";

/* =====================================================================
   HMWK 4 - Welford's recurrences and the sampling mean / variance of the
   scores of m hackers. Pure JavaScript, no external libraries.
   ===================================================================== */

const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");
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

const meanOf = (a) => { let s = 0; for (let i = 0; i < a.length; i++) s += a[i]; return s / a.length; };
const sdOf = (a) => { const m = meanOf(a); let s = 0; for (let i = 0; i < a.length; i++) s += (a[i] - m) ** 2; return Math.sqrt(s / (a.length - 1)); };
const normPdf = (x, mu, s) => Math.exp(-0.5 * ((x - mu) / s) ** 2) / (s * Math.sqrt(2 * Math.PI));

/* ---------------------------------------------------------------------
   1. Chart helper (lines, markers, bars, vertical lines, log axes)
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
  // Logical size = the width/height attributes of the canvas; the real bitmap is scaled by the
  // device pixel ratio so that lines and text stay sharp on any screen
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
  const L = 68, R = 18, T = 34, B = 46 + rows.length * 17;
  const pw = W - L - R, ph = H - T - B;
  const tx = o.xlog ? Math.log10 : (v) => v, ty = o.ylog ? Math.log10 : (v) => v;
  const X = (v) => L + ((tx(v) - tx(x0)) / (tx(x1) - tx(x0))) * pw;
  const Y = (v) => T + ph - ((ty(v) - ty(y0)) / (ty(y1) - ty(y0))) * ph;

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = "#212529"; ctx.font = "bold 13px sans-serif"; ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);

  ctx.font = "10px sans-serif";
  const xt = o.xlog ? logTicks(x0, x1) : (o.xticks || linTicks(x0, x1)), yt = o.ylog ? logTicks(y0, y1) : linTicks(y0, y1);
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

/* ---------------------------------------------------------------------
   2. Exercise 1: Welford's recurrences
   --------------------------------------------------------------------- */

// The algorithm of section 1.4; every step is recorded to fill the table of section 1.5
function welfordSteps(data) {
  let n = 0, mean = 0, ss = 0;
  const rows = [];
  for (const x of data) {
    n += 1;
    const d = x - mean;           // delta_k = x_k - M_(k-1)
    mean += d / n;                // M_k = M_(k-1) + delta_k / k
    ss += d * (x - mean);         // SS_k = SS_(k-1) + (x_k - M_(k-1)) (x_k - M_k)
    rows.push({ k: n, x, d, mean, dev: x - mean, ss, s2: n > 1 ? ss / (n - 1) : NaN });
  }
  return rows;
}

function renderSteps() {
  hideMsg("stepsErr");
  const data = $("stepData").value.split(/[\s,;]+/).filter(Boolean).map(Number);
  if (data.length < 2 || data.length > 60 || data.some((v) => !Number.isFinite(v))) {
    showMsg("stepsErr", "Enter between 2 and 60 numbers.");
    return;
  }
  const rows = welfordSteps(data);
  let allOk = true;
  const out = rows.map((r, i) => {
    const part = data.slice(0, i + 1);
    const m = meanOf(part);
    const ssDirect = part.reduce((s, v) => s + (v - m) ** 2, 0);
    const ok = Math.abs(r.mean - m) <= 1e-9 * Math.max(1, Math.abs(m)) && Math.abs(r.ss - ssDirect) <= 1e-9 * Math.max(1, ssDirect);
    if (!ok) allOk = false;
    return [r.k, r.x, g(r.d), g(r.mean), g(r.dev), g(r.ss), r.k > 1 ? g(r.s2) : "-", g(m), g(ssDirect), ok ? `<span class="ok">&#10003;</span>` : `<span class="bad">&#10007;</span>`];
  });
  $("stepsOut").innerHTML = table(
    ["k", "x<sub>k</sub>", "&delta;<sub>k</sub> = x<sub>k</sub> &minus; M<sub>k&minus;1</sub>", "M<sub>k</sub> (Welford)", "x<sub>k</sub> &minus; M<sub>k</sub>", "SS<sub>k</sub> (Welford)", "s<sub>k</sub>&sup2; = SS<sub>k</sub>/(k &minus; 1)", "M<sub>k</sub> (direct)", "SS<sub>k</sub> (direct)", "Same?"],
    out, "compact") +
    `<p class="small mt-2 mb-0 ${allOk ? "text-success" : "text-danger"}">${allOk ? "All the values computed by the recurrence agree with the direct definitions." : "Some values differ: check the data."}</p>`;
}

// 1000 integer scores 0..10 with a fixed seed, shifted by a large offset, to compare three algorithms
function runStability() {
  const off = Number($("offsetSel").value);
  let a = 12345;
  const scores = Array.from({ length: 1000 }, () => {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return Math.floor((((t ^ (t >>> 14)) >>> 0) / 4294967296) * 11);
  });
  const data = scores.map((s) => off + s), n = data.length;

  // exact reference: n * sum(x^2) - (sum x)^2 with integers of any size
  let S = 0n, Q = 0n;
  for (const s of scores) { const x = BigInt(off) + BigInt(s); S += x; Q += x * x; }
  const nb = BigInt(n);
  const exact = Number(nb * Q - S * S) / Number(nb * (nb - 1n));

  let s1 = 0, q1 = 0;
  for (const x of data) { s1 += x; q1 += x * x; }
  const naive = (q1 - (s1 * s1) / n) / (n - 1);
  const m2 = meanOf(data);
  let ss2 = 0;
  for (const x of data) ss2 += (x - m2) * (x - m2);
  const twoPass = ss2 / (n - 1);
  const w = welfordSteps(data), welford = w[w.length - 1].s2;

  const row = (name, v) => {
    const rel = Math.abs(v - exact) / exact;
    return [name, v < 0 ? `<span class="bad">${g(v)}</span>` : g(v, 8), rel === 0 ? "0" : rel.toExponential(1)];
  };
  $("stabOut").innerHTML = table(["Method", "Computed sample variance", "Relative error"], [
    ["Exact (integer arithmetic)", g(exact, 8), "-"],
    row("Raw-sums formula (&sum;x&sup2; &minus; (&sum;x)&sup2;/n)/(n &minus; 1)", naive),
    row("Two-pass (mean first, then deviations; needs all the data in memory)", twoPass),
    row("Welford (one pass, three numbers of memory)", welford),
  ], "compact") +
    `<p class="small text-muted mt-2 mb-0">The true variance of the 1000 values does not depend on the offset. The raw-sums formula breaks down once the offset is about 10<sup>9</sup>: it loses all its digits, and for larger offsets it can return a negative variance.
    Welford keeps many correct digits at the same offsets, using a single pass. The two-pass method is comparable (it can even be a little more accurate for moderate offsets) but it needs the whole data set twice, so it cannot be used on a stream.
    With these 1000 values and the extreme offset 10<sup>15</sup>, for example, the two-pass result is wrong by a factor of about 3 while Welford is still within 0.2 %, and the raw-sums formula is meaningless.</p>`;
}

/* ---------------------------------------------------------------------
   3. Exercise 2: score distribution, simulation, statistics
   --------------------------------------------------------------------- */

const BINOM10 = [1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1];

function buildDistribution() {
  const kind = $("distSel").value;
  let pmf, label;
  if (kind === "bin") {
    const p = Number($("binP").value);
    if (!(p >= 0.01 && p <= 0.99)) return "p must be between 0.01 and 0.99.";
    pmf = BINOM10.map((c, k) => c * Math.pow(p, k) * Math.pow(1 - p, 10 - k));
    label = `Binomial(10, ${p})`;
  } else if (kind === "uni") {
    pmf = new Array(11).fill(1 / 11);
    label = "Discrete uniform on 0..10";
  } else {
    const w = $("cusW").value.split(/[\s,;]+/).filter(Boolean).map(Number);
    if (w.length !== 11 || w.some((v) => !Number.isFinite(v) || v < 0) || !(w.reduce((s, v) => s + v, 0) > 0)) return "Give exactly 11 non-negative weights, not all zero.";
    const tot = w.reduce((s, v) => s + v, 0);
    pmf = w.map((v) => v / tot);
    label = "Custom distribution";
  }
  const mu = pmf.reduce((s, p, k) => s + k * p, 0);
  const sigma2 = pmf.reduce((s, p, k) => s + (k - mu) ** 2 * p, 0);
  const mu4 = pmf.reduce((s, p, k) => s + (k - mu) ** 4 * p, 0);
  const cdf = [];
  let acc = 0;
  pmf.forEach((p, k) => { acc += p; cdf[k] = k === 10 ? 1 : acc; });
  return { pmf, cdf, label, mu, sigma2, mu4 };
}

function parseConfig() {
  const dist = buildDistribution();
  if (typeof dist === "string") return dist;
  const m = Number($("mInput").value), seed = Number($("seedInput").value);
  const ns = String($("nList").value).split(/[\s,;]+/).filter(Boolean).map(Number);
  if (!Number.isInteger(m) || m < 50 || m > 20000) return "The number of hackers m must be an integer between 50 and 20000.";
  if (!Number.isInteger(seed)) return "The seed must be an integer.";
  if (ns.some((v) => !Number.isInteger(v) || v < 2 || v > 5000)) return "Every n must be an integer between 2 and 5000.";
  const sorted = [...new Set(ns)].sort((a, b) => a - b);
  if (sorted.length < 2 || sorted.length > 8) return "Give between 2 and 8 different values of n.";
  if (m * sorted[sorted.length - 1] > 1e8) return "m times the largest n must be at most 100 million.";
  return { dist, m, ns: sorted, seed };
}

// Every hacker walks through n_max systems; Welford's three lines update the statistics after each score,
// and the state is read at the chosen values of n.
async function simulate(cfg, progress) {
  const { dist, m, ns, seed } = cfg, cdf = dist.cdf;
  const nmax = ns[ns.length - 1];
  const means = ns.map(() => new Float64Array(m)), vars = ns.map(() => new Float64Array(m)), biased = ns.map(() => new Float64Array(m));
  let a = seed | 0;
  const chunk = Math.max(1, Math.floor(4e6 / nmax));
  for (let j0 = 0; j0 < m; j0 += chunk) {
    const j1 = Math.min(m, j0 + chunk);
    for (let j = j0; j < j1; j++) {
      let k = 0, mean = 0, ss = 0;
      for (let c = 0; c < ns.length; c++) {
        const end = ns[c];
        for (; k < end; k++) {
          a = (a + 0x6D2B79F5) | 0;
          let t = Math.imul(a ^ (a >>> 15), 1 | a);
          t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
          const u = ((t ^ (t >>> 14)) >>> 0) / 4294967296;
          let x = 0;
          while (u >= cdf[x]) x++;                 // score of this attempt, drawn from the distribution
          const d = x - mean;                      // Welford (three lines)
          mean += d / (k + 1);
          ss += d * (x - mean);
        }
        means[c][j] = mean; vars[c][j] = ss / (end - 1); biased[c][j] = ss / end;
      }
    }
    progress(j1 / m);
    await tick();
  }
  return { ...cfg, means, vars, biased };
}

let SIM = null, ST = null;

function analyse(sim) {
  const { ns, m, means, vars, biased, dist } = sim;
  return ns.map((n, c) => {
    const avgMean = meanOf(means[c]), sdMean = sdOf(means[c]);
    const avgVar = meanOf(vars[c]), sdVar = sdOf(vars[c]), avgBiased = meanOf(biased[c]);
    const seTheory = Math.sqrt(dist.sigma2 / n);
    const sdVarTheory = Math.sqrt(Math.max(0, (dist.mu4 - ((n - 3) / (n - 1)) * dist.sigma2 * dist.sigma2) / n));
    return { n, avgMean, sdMean, avgVar, sdVar, avgBiased, seTheory, sdVarTheory,
      zMean: (avgMean - dist.mu) / (sdMean / Math.sqrt(m)), zVar: (avgVar - dist.sigma2) / (sdVar / Math.sqrt(m)) };
  });
}

function renderDistribution() {
  const { dist } = SIM;
  plot($("cvPmf"), {
    title: `Score distribution: ${dist.label}`, xlabel: "score", ylabel: "probability", xmin: -0.5, xmax: 10.5, ymin: 0, xticks: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    series: [{ name: "probability of each score", color: "#2c3e50", bars: dist.pmf.map((p, k) => [k - 0.4, k + 0.4, p]) }],
    vlines: [{ x: dist.mu, dash: true, color: "#e74c3c" }],
  });
  $("distInfo").innerHTML =
    `<p class="mb-2">Theoretical mean <strong>&mu; = ${g(dist.mu)}</strong>, variance <strong>&sigma;&sup2; = ${g(dist.sigma2)}</strong> (&sigma; = ${g(Math.sqrt(dist.sigma2))}), fourth central moment &mu;<sub>4</sub> = ${g(dist.mu4)}.
     The dashed line in the plot marks &mu;.</p>` +
    table(["Score", ...dist.pmf.map((_, k) => String(k))], [["Probability", ...dist.pmf.map((p) => g(p, 3))]], "compact");
}

function renderTables() {
  const { dist, m } = SIM;
  $("meanTable").innerHTML = `<h4 class="h6">Sample mean (average over ${fmtInt(m)} hackers)</h4>` + table(
    ["n", "Average of the sample means", "Theoretical &mu;", "z-score", "Std. dev. of the sample means", "Theory &sigma;/&radic;n"],
    ST.map((r) => [fmtInt(r.n), g(r.avgMean, 5), g(dist.mu, 5), g(r.zMean, 2), g(r.sdMean), g(r.seTheory)]), "compact");
  $("varTable").innerHTML = `<h4 class="h6">Sample variance (average over ${fmtInt(m)} hackers)</h4>` + table(
    ["n", "Average of s&sup2; = SS/(n &minus; 1)", "Theoretical &sigma;&sup2;", "z-score", "Average of SS/n", "Theory (n &minus; 1)&sigma;&sup2;/n", "Std. dev. of s&sup2;", "Theory std. dev. of s&sup2;"],
    ST.map((r) => [fmtInt(r.n), g(r.avgVar, 5), g(dist.sigma2, 5), g(r.zVar, 2), g(r.avgBiased, 5), g(((r.n - 1) / r.n) * dist.sigma2, 5), g(r.sdVar), g(r.sdVarTheory)]), "compact");
  const f = ST[0], l = ST[ST.length - 1];
  $("biasNote").innerHTML =
    `At n = ${fmtInt(f.n)} the uncorrected variance SS/n averages ${g(f.avgBiased)}, which is ${g(100 * (1 - f.avgBiased / dist.sigma2), 2)} % below &sigma;&sup2; = ${g(dist.sigma2)} (theory: ${g(100 / f.n, 2)} %), while the corrected sample variance averages ${g(f.avgVar)}. ` +
    `At n = ${fmtInt(l.n)} the gap of the uncorrected version has shrunk to ${g(100 * (1 - l.avgBiased / dist.sigma2), 2)} %. ` +
    `The z-scores of the averages of M<sub>n</sub> and s&sup2; are all of the order of 1, as expected if both estimators are unbiased. A z-score of 2 or 3 now and then is normal when many are computed.`;
}

function renderCharts() {
  const { dist, m } = SIM;
  const pt = (f) => ST.map((r) => [r.n, f(r)]);
  plot($("cvAvgMean"), {
    title: "Average of the sample means against n", xlabel: "n (log scale)", ylabel: "average of M_n", xlog: true,
    series: [
      { name: "average over the hackers", color: "#2c3e50", markers: true, width: 2, pts: pt((r) => r.avgMean) },
      { name: "theoretical \u00b5", color: "#e74c3c", dash: true, pts: pt(() => dist.mu) },
      { name: "\u00b5 \u00b1 2 Monte Carlo standard errors", color: "#adb5bd", dash: true, pts: pt((r) => dist.mu + 2 * r.sdMean / Math.sqrt(m)) },
      { color: "#adb5bd", dash: true, pts: pt((r) => dist.mu - 2 * r.sdMean / Math.sqrt(m)) },
    ],
  });
  plot($("cvAvgVar"), {
    title: "Average of the sample variances against n", xlabel: "n (log scale)", ylabel: "average variance", xlog: true, ymin: 0,
    series: [
      { name: "average of s\u00b2 (divide by n \u2212 1)", color: "#18bc9c", markers: true, width: 2, pts: pt((r) => r.avgVar) },
      { name: "average of SS/n (divide by n)", color: "#e67e22", markers: true, width: 2, pts: pt((r) => r.avgBiased) },
      { name: "theoretical \u03c3\u00b2", color: "#e74c3c", dash: true, pts: pt(() => dist.sigma2) },
      { name: "theory (n \u2212 1)\u03c3\u00b2/n", color: "#6c757d", dash: true, pts: pt((r) => ((r.n - 1) / r.n) * dist.sigma2) },
    ],
  });
  plot($("cvSdMean"), {
    title: "Variability of the sample mean", xlabel: "n (log scale)", ylabel: "std. dev. of M_n over the hackers", xlog: true, ylog: true,
    series: [
      { name: "simulated", color: "#2c3e50", markers: true, line: false, pts: pt((r) => r.sdMean) },
      { name: "theory \u03c3/\u221an", color: "#e74c3c", dash: true, pts: pt((r) => r.seTheory) },
    ],
  });
  plot($("cvSdVar"), {
    title: "Variability of the sample variance", xlabel: "n (log scale)", ylabel: "std. dev. of s\u00b2 over the hackers", xlog: true, ylog: true,
    series: [
      { name: "simulated", color: "#2c3e50", markers: true, line: false, pts: pt((r) => r.sdVar) },
      { name: "theory \u221a[(\u00b5\u2084 \u2212 (n\u22123)/(n\u22121)\u00b7\u03c3\u2074)/n]", color: "#e74c3c", dash: true, pts: pt((r) => r.sdVarTheory) },
    ],
  });
}

function renderNSelect() {
  const sel = $("nSel"), prev = sel.value;
  sel.innerHTML = SIM.ns.map((n, i) => `<option value="${i}">n = ${fmtInt(n)}</option>`).join("");
  sel.value = prev !== "" && Number(prev) < SIM.ns.length ? prev : String(SIM.ns.length - 1);
}

function histBars(vals, spacing) { // density bars; bin width = a whole number of lattice spacings when spacing is given
  const m = vals.length;
  let lo = Infinity, hi = -Infinity;
  for (let i = 0; i < m; i++) { if (vals[i] < lo) lo = vals[i]; if (vals[i] > hi) hi = vals[i]; }
  let w, e0;
  if (spacing) { w = spacing * Math.max(1, Math.ceil((hi - lo) / spacing / 30)); e0 = lo - spacing / 2; }
  else { w = (hi - lo) / 30 || 1; e0 = lo; }
  const nb = Math.floor((hi - e0) / w + 1e-9) + 1, cnt = new Array(nb).fill(0);
  for (let i = 0; i < m; i++) cnt[Math.min(nb - 1, Math.floor((vals[i] - e0) / w + 1e-9))]++;
  return { bars: cnt.map((q, i) => [e0 + i * w, e0 + (i + 1) * w, q / (m * w)]), lo: e0, hi: e0 + nb * w };
}

function renderHist() {
  const c = Number($("nSel").value), n = SIM.ns[c], { dist } = SIM, r = ST[c];
  const curve = (mu, s, lo, hi) => { const a = Math.min(lo, mu - 4 * s), b = Math.max(hi, mu + 4 * s); return Array.from({ length: 161 }, (_, i) => [a + ((b - a) * i) / 160, normPdf(a + ((b - a) * i) / 160, mu, s)]); };
  const hm = histBars(SIM.means[c], 1 / n);
  plot($("cvHistMean"), {
    title: `Sample means, n = ${fmtInt(n)}`, xlabel: "sample mean M_n", ylabel: "density", ymin: 0,
    series: [{ name: "simulated", color: "#7fb3d5", bars: hm.bars }, { name: "normal N(\u00b5, \u03c3\u00b2/n)", color: "#e74c3c", width: 2, pts: curve(dist.mu, r.seTheory, hm.lo, hm.hi) }],
    vlines: [{ x: dist.mu, dash: true, color: "#000" }],
  });
  const hv = histBars(SIM.vars[c], 0);
  plot($("cvHistVar"), {
    title: `Sample variances, n = ${fmtInt(n)}`, xlabel: "sample variance s\u00b2", ylabel: "density", ymin: 0,
    series: [{ name: "simulated", color: "#7fb3d5", bars: hv.bars }, { name: "normal with the theoretical mean and std. dev.", color: "#e74c3c", width: 2, pts: curve(dist.sigma2, r.sdVarTheory || 1, hv.lo, hv.hi) }],
    vlines: [{ x: dist.sigma2, dash: true, color: "#000" }],
  });
  $("histNote").textContent = "The dashed vertical lines mark the true values (\u00b5 and \u03c3\u00b2): both histograms are centred on them. " +
    "The sample means look like a bell curve already for moderate n (Central Limit Theorem). The sample variances are skewed to the right for small n, because a variance cannot be negative and a few unusual samples give large values, and become more symmetric as n grows.";
}

function renderAll() {
  renderDistribution(); renderTables(); renderCharts(); renderNSelect(); renderHist();
}

/* ---------------------------------------------------------------------
   4. Controls
   --------------------------------------------------------------------- */

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
    ST = analyse(SIM);
    renderAll();
    $("simStatus").textContent = `${SIM.dist.label}, m = ${fmtInt(SIM.m)} hackers, seed ${SIM.seed}. Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    showMsg("jsError", "Error during the simulation: " + err.message);
  }
  running = false;
  $("btnRun").disabled = false; $("btnSeed").disabled = false;
}

function init() {
  $("btnSteps").addEventListener("click", renderSteps);
  $("btnStab").addEventListener("click", runStability);
  $("offsetSel").addEventListener("change", runStability);
  $("distSel").addEventListener("change", () => {
    $("binBox").classList.toggle("d-none", $("distSel").value !== "bin");
    $("cusBox").classList.toggle("d-none", $("distSel").value !== "cus");
    run();
  });
  $("btnRun").addEventListener("click", run);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = String(crypto.getRandomValues(new Uint32Array(1))[0] >>> 1); run(); });
  $("nSel").addEventListener("change", () => { if (SIM) renderHist(); });
  renderSteps();
  runStability();
  run();
}

document.addEventListener("DOMContentLoaded", init);
