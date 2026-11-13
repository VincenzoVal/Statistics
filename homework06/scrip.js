"use strict";

/* =====================================================================
   HMWK 6 - Contingency tables and the chi-square test of independence.
   For a bivariate categorical dataset (X, F): contingency table, marginal
   and conditional frequencies, expected counts under independence,
   Pearson chi-square statistic, p-value (optional part) and Cramer's V (extra).
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

// log Gamma(z) for z > 0 (Lanczos approximation, g = 7, 9 coefficients)
const LANCZOS = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313,
  -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
function lnGamma(z) {
  if (z < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * z))) - lnGamma(1 - z);
  z -= 1;
  let s = LANCZOS[0];
  const t = z + 7.5;
  for (let i = 1; i < 9; i++) s += LANCZOS[i] / (z + i);
  return 0.5 * Math.log(2 * Math.PI) + (z + 0.5) * Math.log(t) - t + Math.log(s);
}

// Regularized upper incomplete gamma function Q(a, x) = Gamma(a, x) / Gamma(a):
// series for x < a + 1, continued fraction (modified Lentz) otherwise
function gammaQ(a, x) {
  if (!(x > 0)) return 1;
  const pre = Math.exp(-x + a * Math.log(x) - lnGamma(a));
  if (x < a + 1) {
    let ap = a, del = 1 / a, sum = del;
    for (let i = 0; i < 10000; i++) {
      ap += 1; del *= x / ap; sum += del;
      if (Math.abs(del) < Math.abs(sum) * 1e-15) break;
    }
    return Math.max(0, 1 - sum * pre);
  }
  const TINY = 1e-300;
  let b = x + 1 - a, c = 1 / TINY, d = 1 / b, h = d;
  for (let i = 1; i < 10000; i++) {
    const an = -i * (i - a);
    b += 2;
    d = an * d + b; if (Math.abs(d) < TINY) d = TINY;
    c = b + an / c; if (Math.abs(c) < TINY) c = TINY;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-15) break;
  }
  return pre * h;
}

const chi2Sf = (x, df) => gammaQ(df / 2, x / 2);   // P(chi2_df >= x)
const chi2Pdf = (x, df) => Math.exp((df / 2 - 1) * Math.log(x) - x / 2 - (df / 2) * Math.LN2 - lnGamma(df / 2));

// Critical value: the x with P(chi2_df >= x) = alpha (bisection)
function chi2Crit(alpha, df) {
  let lo = 0, hi = df + 10;
  while (chi2Sf(hi, df) > alpha) hi *= 2;
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2;
    if (chi2Sf(mid, df) > alpha) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
}


/* ---------------------------------------------------------------------
   2. Generic chart: lines, markers, vertical lines, log axes
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

// 100% stacked bars: o.bars = [{ label, values }] with values summing to 1, o.segments = names of the segments
function drawStacked(canvas, o) {
  const W = Number(canvas.dataset.w || canvas.width), H = Number(canvas.dataset.h || canvas.height);
  canvas.dataset.w = W; canvas.dataset.h = H;
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  ctx.font = "11px sans-serif";
  const rows = [[]];
  let rowW = 0;
  o.segments.forEach((name, j) => {
    const w = 20 + ctx.measureText(name).width + 14;
    if (rowW + w > W - 24 && rows[rows.length - 1].length) { rows.push([]); rowW = 0; }
    rows[rows.length - 1].push([name, j, w]); rowW += w;
  });
  const nb = o.bars.length, rot = nb > 5;
  const L = 56, R = 20, T = 34, B = (rot ? 82 : 46) + rows.length * 17;
  const pw = W - L - R, ph = H - T - B;
  const Y = (v) => T + ph - v * ph;

  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = "#ffffff"; ctx.fillRect(0, 0, W, H);
  ctx.fillStyle = "#212529"; ctx.font = "bold 13px sans-serif"; ctx.textAlign = "left"; ctx.textBaseline = "alphabetic";
  ctx.fillText(o.title || "", L, 20);

  ctx.font = "10px sans-serif"; ctx.lineWidth = 1; ctx.textAlign = "right";
  for (const v of [0, 0.25, 0.5, 0.75, 1]) {
    ctx.strokeStyle = "#f1f3f5"; ctx.beginPath(); ctx.moveTo(L, Y(v)); ctx.lineTo(L + pw, Y(v)); ctx.stroke();
    ctx.fillStyle = "#6c757d"; ctx.fillText(Math.round(v * 100) + "%", L - 6, Y(v) + 3);
  }

  const slot = pw / nb, bw = slot * 0.62;
  o.bars.forEach((bar, b) => {
    const cx = L + (b + 0.5) * slot;
    let acc = 0;
    bar.values.forEach((v, j) => {
      ctx.fillStyle = fnColor(j);
      ctx.fillRect(cx - bw / 2, Y(acc + v), bw, Math.max(0, Y(acc) - Y(acc + v)));
      if (v * ph > 14) {
        ctx.fillStyle = "#ffffff"; ctx.font = "bold 10px sans-serif"; ctx.textAlign = "center";
        ctx.fillText(Math.round(v * 100) + "%", cx, Y(acc + v / 2) + 3);
      }
      acc += v;
    });
    const lab = bar.label.length > 10 ? bar.label.slice(0, 9) + "\u2026" : bar.label;
    ctx.fillStyle = "#6c757d"; ctx.font = "10px sans-serif";
    if (rot) {
      ctx.save(); ctx.translate(cx + 3, T + ph + 12); ctx.rotate(-Math.PI / 4); ctx.textAlign = "right"; ctx.fillText(lab, 0, 0); ctx.restore();
    } else {
      ctx.textAlign = "center"; ctx.fillText(lab, cx, T + ph + 14);
    }
  });

  // separator before the last bar (marginal distribution)
  ctx.strokeStyle = "#adb5bd"; ctx.setLineDash([4, 3]);
  ctx.beginPath(); ctx.moveTo(L + (nb - 1) * slot, T); ctx.lineTo(L + (nb - 1) * slot, T + ph); ctx.stroke();
  ctx.setLineDash([]);
  ctx.beginPath(); ctx.moveTo(L, T); ctx.lineTo(L, T + ph); ctx.lineTo(L + pw, T + ph); ctx.stroke();

  ctx.fillStyle = "#495057"; ctx.font = "11px sans-serif"; ctx.textAlign = "center";
  if (o.xlabel) ctx.fillText(o.xlabel, L + pw / 2, T + ph + (rot ? 70 : 34));
  if (o.ylabel) { ctx.save(); ctx.translate(14, T + ph / 2); ctx.rotate(-Math.PI / 2); ctx.fillText(o.ylabel, 0, 0); ctx.restore(); }

  ctx.textAlign = "left";
  rows.forEach((row, ri) => {
    let lx = L, ly = H - 8 - (rows.length - 1 - ri) * 17;
    for (const [name, j, w] of row) {
      ctx.fillStyle = fnColor(j); ctx.fillRect(lx, ly - 9, 12, 10);
      ctx.fillStyle = "#212529"; ctx.fillText(name, lx + 18, ly);
      lx += w;
    }
  });
}


/* ---------------------------------------------------------------------
   3. Datasets and computations
   --------------------------------------------------------------------- */

const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
const showMsg = (id, msg) => { const e = $(id); e.textContent = msg; e.classList.remove("d-none"); };
const hideMsg = (id) => $(id).classList.add("d-none");
const fmtInt = (v) => Math.round(v).toLocaleString("en-US");
const f4 = (v) => v.toFixed(4);
const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

// Number with about d significant digits, in plain or exponential notation
const g = (v, d = 4) => {
  if (v === null || Number.isNaN(v)) return "n/a";
  if (!Number.isFinite(v)) return v > 0 ? "&infin;" : "&minus;&infin;";
  if (v === 0) return "0";
  const a = Math.abs(v);
  return a >= 1e5 || a < 1e-3 ? v.toExponential(d > 4 ? d - 1 : 2) : String(Number(v.toPrecision(d)));
};
const ge = (v) => (v === null || !Number.isFinite(v) ? "n/a" : v === 0 ? "0" : v.toExponential(2)); // errors and p-values

function table(headers, rows, cls = "") {
  const head = headers.map((h) => `<th>${h}</th>`).join("");
  const body = rows.map((r) => `<tr>${r.map((c) => `<td>${c}</td>`).join("")}</tr>`).join("");
  return `<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 ${cls}">` +
         `<thead><tr>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

class InputError extends Error {}

const MAX_CATEGORIES = 12;

// Synthetic datasets: both variables are categorical
const PRESETS = {
  dependent: {
    xName: "Attack type", fName: "Detection outcome",
    xs: ["Phishing", "Malware", "DoS", "SQL injection"], px: [0.40, 0.25, 0.20, 0.15],
    fs: ["Detected", "Missed"],
    pfGivenX: [[0.50, 0.50], [0.65, 0.35], [0.75, 0.25], [0.55, 0.45]],
    info: "X is drawn with probabilities 0.40, 0.25, 0.20, 0.15; F is then drawn with P(Detected | X) = 0.50, 0.65, 0.75, 0.55, so F depends on X by construction.",
  },
  independent: {
    xName: "System tier", fName: "Alert severity",
    xs: ["Web", "Database", "Endpoint"], px: [0.50, 0.30, 0.20],
    fs: ["Low", "Medium", "High"], pf: [0.50, 0.30, 0.20],
    info: "X is drawn with probabilities 0.50, 0.30, 0.20 and F is drawn independently with probabilities 0.50, 0.30, 0.20, so X and F are independent by construction.",
  },
};

// Index drawn from a discrete distribution
function pick(rng, probs) {
  const u = rng();
  let acc = 0;
  for (let i = 0; i < probs.length - 1; i++) { acc += probs[i]; if (u < acc) return i; }
  return probs.length - 1;
}

// List of observations [x, f, weight]
function simulatePairs(key, seed, n) {
  const P = PRESETS[key], rng = mulberry32(seed), out = [];
  for (let k = 0; k < n; k++) {
    const i = pick(rng, P.px);
    const j = pick(rng, P.pfGivenX ? P.pfGivenX[i] : P.pf);
    out.push([P.xs[i], P.fs[j], 1]);
  }
  return out;
}

// Custom text: "x,f" or "x,f,count" per line
function parsePairs(text) {
  const out = [];
  const lines = String(text).split(/\r?\n/);
  for (let k = 0; k < lines.length; k++) {
    const line = lines[k].trim();
    if (line === "" || line.startsWith("#")) continue;
    const parts = line.split(/[,;\t]/).map((s) => s.trim());
    if (parts.length < 2 || parts.length > 3 || parts[0] === "" || parts[1] === "")
      throw new InputError(`Line ${k + 1}: expected "x,f" or "x,f,count".`);
    let w = 1;
    if (parts.length === 3) {
      w = Number(parts[2]);
      if (parts[2] === "" || !Number.isInteger(w) || w < 1 || w > 1e6)
        throw new InputError(`Line ${k + 1}: the count must be an integer between 1 and 1000000.`);
    }
    if (parts[0].length > 30 || parts[1].length > 30) throw new InputError(`Line ${k + 1}: category names are limited to 30 characters.`);
    out.push([parts[0], parts[1], w]);
  }
  if (!out.length) throw new InputError("No data: paste at least one observation.");
  return out;
}

// Contingency table from a list of observations; order = preset order, or sorted for custom data
function tabulate(entries, orderX, orderF) {
  const usedX = new Set(entries.map((e) => e[0])), usedF = new Set(entries.map((e) => e[1]));
  const sorter = (a, b) => a.localeCompare(b, "en", { numeric: true });
  const xs = orderX ? orderX.filter((v) => usedX.has(v)) : [...usedX].sort(sorter);
  const fs = orderF ? orderF.filter((v) => usedF.has(v)) : [...usedF].sort(sorter);
  if (xs.length < 2 || fs.length < 2) throw new InputError("Both variables need at least two distinct categories.");
  if (xs.length > MAX_CATEGORIES || fs.length > MAX_CATEGORIES) throw new InputError(`Each variable can have at most ${MAX_CATEGORIES} categories.`);
  const ix = new Map(xs.map((v, i) => [v, i])), jf = new Map(fs.map((v, j) => [v, j]));
  const O = xs.map(() => fs.map(() => 0));
  for (const [x, f, w] of entries) O[ix.get(x)][jf.get(f)] += w;
  return { xs, fs, O };
}

function buildDataset(cfg) {
  if (cfg.source === "custom") {
    const t = tabulate(parsePairs(cfg.text));
    return { ...t, xName: "X", fName: "F", info: "Custom data, read from the text box." };
  }
  const P = PRESETS[cfg.source];
  const t = tabulate(simulatePairs(cfg.source, cfg.seed, cfg.n), P.xs, P.fs);
  return { ...t, xName: P.xName, fName: P.fName, info: `Synthetic data (n = ${fmtInt(cfg.n)}, seed ${cfg.seed}). ${P.info}` };
}

// All the quantities of the test for a table of counts
function analyse(t, alpha) {
  const R = t.xs.length, C = t.fs.length, O = t.O;
  const r = O.map((row) => row.reduce((s, v) => s + v, 0));
  const c = t.fs.map((_, j) => O.reduce((s, row) => s + row[j], 0));
  const n = r.reduce((s, v) => s + v, 0);
  const E = O.map((row, i) => row.map((_, j) => (r[i] * c[j]) / n));
  const K = O.map((row, i) => row.map((o, j) => ((o - E[i][j]) ** 2) / E[i][j]));
  let chi2 = 0, kmax = 0, imax = 0, jmax = 0, minE = Infinity, lowE = 0;
  for (let i = 0; i < R; i++) for (let j = 0; j < C; j++) {
    chi2 += K[i][j];
    if (K[i][j] > kmax) { kmax = K[i][j]; imax = i; jmax = j; }
    if (E[i][j] < minE) minE = E[i][j];
    if (E[i][j] < 5) lowE++;
  }
  const df = (R - 1) * (C - 1);
  return {
    R, C, O, r, c, n, E, K, chi2, df, alpha, imax, jmax, minE, lowE,
    p: chi2Sf(chi2, df), crit: chi2Crit(alpha, df), V: Math.sqrt(chi2 / (n * Math.min(R - 1, C - 1))),
  };
}


/* ---------------------------------------------------------------------
   4. Rendering
   --------------------------------------------------------------------- */

const pFmt = (p) => (p === 0 ? "&lt; 1e-300" : p < 1e-3 ? p.toExponential(2) : String(Number(p.toPrecision(3))));

function renderAll(ds, alpha) {
  const a = analyse(ds, alpha);
  const xs = ds.xs.map(esc), fs = ds.fs.map(esc);
  const corner = `${esc(ds.xName)} \\ ${esc(ds.fName)}`;
  const b = (s) => `<strong>${s}</strong>`;

  $("dataInfo").textContent = `${ds.xName} (rows, ${a.R} categories) and ${ds.fName} (columns, ${a.C} categories). ${ds.info}`;

  // 2. observed counts and joint relative frequencies, with marginals
  $("tblObs").innerHTML = table([corner, ...fs, "Total r<sub>i</sub>"],
    [...a.O.map((row, i) => [b(xs[i]), ...row.map(fmtInt), b(fmtInt(a.r[i]))]),
     [b("Total c<sub>j</sub>"), ...a.c.map((v) => b(fmtInt(v))), b(fmtInt(a.n))]], "compact");
  $("tblJoint").innerHTML = table([corner, ...fs, "f<sub>i+</sub>"],
    [...a.O.map((row, i) => [b(xs[i]), ...row.map((v) => f4(v / a.n)), b(f4(a.r[i] / a.n))]),
     [b("f<sub>+j</sub>"), ...a.c.map((v) => b(f4(v / a.n))), b(f4(1))]], "compact");

  // 3. conditional frequencies
  $("tblCondF").innerHTML = table([corner, ...fs, "Sum"],
    [...a.O.map((row, i) => [b(xs[i]), ...row.map((v) => f4(v / a.r[i])), f4(1)]),
     [b("All (marginal of F)"), ...a.c.map((v) => b(f4(v / a.n))), f4(1)]], "compact");
  $("tblCondX").innerHTML = table([corner, ...fs, "All (marginal of X)"],
    [...a.O.map((row, i) => [b(xs[i]), ...row.map((v, j) => f4(v / a.c[j])), b(f4(a.r[i] / a.n))]),
     [b("Sum"), ...a.c.map(() => f4(1)), f4(1)]], "compact");

  // 4. expected counts
  $("tblExp").innerHTML = table([corner, ...fs, "Total"],
    [...a.E.map((row, i) => [b(xs[i]), ...row.map((v) => v.toFixed(2)), b(a.r[i].toFixed(2))]),
     [b("Total"), ...a.c.map((v) => b(v.toFixed(2))), b(a.n.toFixed(2))]], "compact");

  // 5. contributions and summary
  $("tblContrib").innerHTML = table([corner, ...fs, "Row sum"],
    [...a.K.map((row, i) => [b(xs[i]),
        ...row.map((v, j) => (i === a.imax && j === a.jmax ? `<span class="best">${v.toFixed(3)}</span>` : v.toFixed(3))),
        b(row.reduce((s, v) => s + v, 0).toFixed(3))]),
     [b("Total &chi;&sup2;"), ...a.K[0].map((_, j) => b(a.K.reduce((s, row) => s + row[j], 0).toFixed(3))), b(g(a.chi2))]], "compact");

  const reject = a.chi2 > a.crit;
  const summary = [
    ["Observations n", fmtInt(a.n)],
    ["Table size R &times; C", `${a.R} &times; ${a.C}`],
    ["Degrees of freedom (R &minus; 1)(C &minus; 1)", String(a.df)],
    ["Statistic &chi;&sup2;", g(a.chi2)],
    ["Significance level &alpha;", String(alpha)],
    ["Critical value &chi;&sup2;<sub>&alpha;</sub>", g(a.crit)],
    ["p-value (optional part)", pFmt(a.p)],
    ["Decision", reject ? "reject H<sub>0</sub> (dependence)" : "do not reject H<sub>0</sub>"],
    ["Smallest expected count", g(a.minE)],
    ["Cells with expected count &lt; 5", `${a.lowE} of ${a.R * a.C}`],
    ["Cramer&rsquo;s V (extra)", g(a.V)],
  ];
  $("tblSummary").innerHTML = table(["Quantity", "Value"], summary, "compact");

  // charts
  drawStacked($("cvCond"), {
    title: `Distribution of F given each category of X`, xlabel: ds.xName, ylabel: "conditional frequency",
    segments: ds.fs,
    bars: [...ds.xs.map((x, i) => ({ label: x, values: a.O[i].map((v) => v / a.r[i]) })),
           { label: "all", values: a.c.map((v) => v / a.n) }],
  });
  const xmax = Math.max(a.crit * 1.8, Math.min(a.chi2 * 1.15, a.crit * 6));
  const pts = [];
  for (let k = 0; k <= 240; k++) { const x = 0.02 + (xmax - 0.02) * (k / 240); pts.push([x, chi2Pdf(x, a.df)]); }
  const top = Math.max(...pts.map((p) => p[1]));
  const beyond = a.chi2 > xmax, xo = beyond ? xmax * 0.98 : a.chi2;
  plot($("cvChi"), {
    title: `Chi-square distribution, df = ${a.df}`, xlabel: "\u03c7\u00b2 value", ylabel: "density",
    xmin: 0, xmax, ymin: 0,
    series: [
      { name: `density (df = ${a.df})`, color: PAL.main, width: 2, pts },
      { name: `critical value (\u03b1 = ${alpha}): ${g(a.crit)}`, color: PAL.red, width: 1.5, dash: true, pts: [[a.crit, 0], [a.crit, top]] },
      { name: `observed \u03c7\u00b2 = ${g(a.chi2).replace(/&[^;]+;/g, "")}${beyond ? " (beyond the range)" : ""}`, color: PAL.green, width: 2, pts: [[xo, 0], [xo, top]] },
    ],
  });

  // verdict (Discussion)
  const warn = a.minE < 1 || a.lowE / (a.R * a.C) > 0.2
    ? " Some expected counts are small, so the chi-square approximation may be unreliable." : "";
  const pTxt = a.p === 0 ? "p &lt; 1e-300" : `p = ${pFmt(a.p)}`;
  const box = $("verdict");
  box.className = "alert alert-info";
  box.innerHTML = reject
    ? `At &alpha; = ${alpha}, &chi;&sup2; = ${g(a.chi2)} exceeds the critical value ${g(a.crit)} (df = ${a.df}, ${pTxt}): H<sub>0</sub> is rejected. ` +
      `The data provide evidence that ${esc(ds.xName)} and ${esc(ds.fName)} are statistically dependent. Cramer&rsquo;s V = ${g(a.V)}.${warn}`
    : `At &alpha; = ${alpha}, &chi;&sup2; = ${g(a.chi2)} does not exceed the critical value ${g(a.crit)} (df = ${a.df}, ${pTxt}): H<sub>0</sub> is not rejected. ` +
      `The data are compatible with independence of ${esc(ds.xName)} and ${esc(ds.fName)}; this is not a proof of independence. Cramer&rsquo;s V = ${g(a.V)}.${warn}`;
}


/* ---------------------------------------------------------------------
   5. Controls
   --------------------------------------------------------------------- */

function parseConfig() {
  const source = $("dataSelect").value, alpha = Number($("alphaSelect").value);
  if (source === "custom") return { source, alpha, text: $("customData").value };
  const rawSeed = String($("seedInput").value).trim(), seed = Number(rawSeed);
  if (rawSeed === "" || !Number.isInteger(seed) || seed < 0 || seed > 4294967295) return "The seed must be an integer between 0 and 4294967295.";
  const rawN = String($("nInput").value).trim(), n = Number(rawN);
  if (rawN === "" || !Number.isInteger(n) || n < 10 || n > 100000) return "The sample size n must be an integer between 10 and 100000.";
  return { source, seed, n, alpha };
}

function syncControls() {
  const custom = $("dataSelect").value === "custom";
  $("customBox").classList.toggle("d-none", !custom);
  $("seedInput").disabled = custom; $("nInput").disabled = custom; $("btnSeed").disabled = custom;
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
    renderAll(buildDataset(cfg), cfg.alpha);
    await tick();
    $("simStatus").textContent = `Done in ${((performance.now() - t0) / 1000).toFixed(1)} s.`;
  } catch (err) {
    if (err instanceof InputError) { showMsg("simError", err.message); $("simStatus").textContent = ""; }
    else showMsg("jsError", "Error during the computation: " + err.message);
  }
  running = false;
  $("btnRun").disabled = false;
  syncControls();
}

function init() {
  $("btnRun").addEventListener("click", run);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = String(crypto.getRandomValues(new Uint32Array(1))[0] >>> 1); run(); });
  $("dataSelect").addEventListener("change", () => { syncControls(); run(); });
  $("alphaSelect").addEventListener("change", run);
  syncControls();
  run();
}

document.addEventListener("DOMContentLoaded", init);
