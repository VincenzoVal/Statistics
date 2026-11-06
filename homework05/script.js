"use strict";
/* HMWK 6 — Riemann vs Lebesgue Integration and the Numerical Normal CDF
   Part 1: Riemann-type (domain partition) and Lebesgue-type (range partition) sums.
   Part 2: standard normal CDF via erf (series, continued fraction), quadrature and approximations. */

/* ---------- helpers ---------- */
const $ = (id) => document.getElementById(id);
const tick = () => new Promise((r) => setTimeout(r, 0));
function showMsg(id, text) { const e = $(id); if (e) { e.textContent = text; e.classList.remove("d-none"); } }
function hideMsg(id) { const e = $(id); if (e) { e.textContent = ""; e.classList.add("d-none"); } }
const fmtInt = (n) => n.toLocaleString("en-US");
function g(x, d) { // d significant digits
  d = d || 6;
  if (x === null || x === undefined || Number.isNaN(x)) return "n/a";
  if (!Number.isFinite(x)) return x > 0 ? "∞" : "−∞";
  if (x === 0) return "0";
  const a = Math.abs(x);
  if (a >= 1e-4 && a < 1e6) return String(Number(x.toPrecision(d)));
  return x.toExponential(d - 1);
}
const ge = (x) => (x === null || Number.isNaN(x) ? "n/a" : x === 0 ? "0" : x.toExponential(2));
function table(head, rows) {
  const th = head.map((h) => "<th>" + h + "</th>").join("");
  const tr = rows.map((r) => "<tr>" + r.map((c) => "<td>" + c + "</td>").join("") + "</tr>").join("");
  return '<div class="table-responsive"><table class="table table-sm table-striped align-middle mb-0 compact"><thead><tr>' +
    th + "</tr></thead><tbody>" + tr + "</tbody></table></div>";
}
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function timeIt(fn, reps) {
  let best = Infinity, res;
  for (let i = 0; i < reps; i++) { const t = performance.now(); res = fn(); best = Math.min(best, performance.now() - t); }
  return { ms: best, res: res };
}

/* ---------- log-log plot on a canvas (sharp on high-density screens) ---------- */
const COLORS = ["#2c3e50", "#18bc9c", "#e74c3c", "#e67e22", "#7fb3d5", "#9b59b6", "#f39c12"];
function plot(cv, cfg) {
  const dpr = window.devicePixelRatio || 1, W = 600, H = 360;
  cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
  const c = cv.getContext("2d");
  c.setTransform(dpr, 0, 0, dpr, 0, 0);
  c.fillStyle = "#fff"; c.fillRect(0, 0, W, H);
  const m = { l: 62, r: 14, t: 30, b: 46 }, pw = W - m.l - m.r, ph = H - m.t - m.b;
  const xs = [], ys = [];
  cfg.series.forEach((s) => s.pts.forEach((p) => {
    if (p[1] !== null && p[1] > 0 && Number.isFinite(p[1])) { xs.push(p[0]); ys.push(p[1]); }
  }));
  c.font = "12px sans-serif"; c.textAlign = "center";
  c.fillStyle = "#212529"; c.fillText(cfg.title, W / 2, 18);
  if (!xs.length) { c.fillStyle = "#6c757d"; c.fillText("no positive values to plot", W / 2, H / 2); return; }
  const x0 = Math.floor(Math.log10(Math.min.apply(null, xs))), x1 = Math.max(x0 + 1, Math.ceil(Math.log10(Math.max.apply(null, xs))));
  const y0 = Math.floor(Math.log10(Math.min.apply(null, ys))), y1 = Math.max(y0 + 1, Math.ceil(Math.log10(Math.max.apply(null, ys))));
  const X = (v) => m.l + ((Math.log10(v) - x0) / (x1 - x0)) * pw;
  const Y = (v) => m.t + ph - ((Math.log10(v) - y0) / (y1 - y0)) * ph;
  const stepY = Math.ceil((y1 - y0) / 8);
  c.strokeStyle = "#f1f3f5"; c.fillStyle = "#495057"; c.lineWidth = 1;
  for (let k = x0; k <= x1; k++) {
    const px = X(Math.pow(10, k)); c.beginPath(); c.moveTo(px, m.t); c.lineTo(px, m.t + ph); c.stroke();
    c.textAlign = "center"; c.fillText("1e" + k, px, m.t + ph + 15);
  }
  for (let k = y0; k <= y1; k += stepY) {
    const py = Y(Math.pow(10, k)); c.beginPath(); c.moveTo(m.l, py); c.lineTo(m.l + pw, py); c.stroke();
    c.textAlign = "right"; c.fillText("1e" + k, m.l - 5, py + 4);
  }
  c.strokeStyle = "#adb5bd"; c.strokeRect(m.l, m.t, pw, ph);
  c.textAlign = "center"; c.fillStyle = "#495057";
  c.fillText(cfg.xlabel, m.l + pw / 2, H - 8);
  c.save(); c.translate(13, m.t + ph / 2); c.rotate(-Math.PI / 2); c.fillText(cfg.ylabel, 0, 0); c.restore();
  cfg.series.forEach((s, i) => {
    const col = s.color || COLORS[i % COLORS.length];
    c.strokeStyle = col; c.fillStyle = col; c.lineWidth = 1.6;
    c.setLineDash(s.dash ? [5, 4] : []);
    c.beginPath(); let pen = false;
    s.pts.forEach((p) => {
      if (p[1] === null || !(p[1] > 0) || !Number.isFinite(p[1])) { pen = false; return; }
      if (!pen) { c.moveTo(X(p[0]), Y(p[1])); pen = true; } else c.lineTo(X(p[0]), Y(p[1]));
    });
    c.stroke(); c.setLineDash([]);
    s.pts.forEach((p) => {
      if (p[1] !== null && p[1] > 0 && Number.isFinite(p[1])) { c.beginPath(); c.arc(X(p[0]), Y(p[1]), 2.2, 0, 2 * Math.PI); c.fill(); }
    });
  });
}
function legend(id, series) {
  $(id).innerHTML = series.map((s, i) =>
    '<span><span class="dot" style="background:' + (s.color || COLORS[i % COLORS.length]) + '"></span>' + s.name + "</span>").join("");
}

/* ---------- Part 1: test functions ---------- */
const FUNCS = [
  { id: "f1", name: "sin(x)", dom: "[0, π]", a: 0, b: Math.PI, f: (x) => Math.sin(x), exact: 2, exactTxt: "2" },
  { id: "f2", name: "x²", dom: "[0, 1]", a: 0, b: 1, f: (x) => x * x, exact: 1 / 3, exactTxt: "1/3" },
  { id: "f3", name: "1 if x &lt; 0.5, 3 if x ≥ 0.5", dom: "[0, 1]", a: 0, b: 1, f: (x) => (x < 0.5 ? 1 : 3), exact: 2, exactTxt: "2" },
  { id: "f4", name: "|x − 0.5|", dom: "[0, 1]", a: 0, b: 1, f: (x) => Math.abs(x - 0.5), exact: 0.25, exactTxt: "1/4" },
  { id: "f5", name: "1/√x", dom: "(0, 1]", a: 0, b: 1, f: (x) => 1 / Math.sqrt(x), exact: 2, exactTxt: "2 (improper)" },
  { id: "f6", name: "1 if x &lt; 0.5, 0 if x ≥ 0.5", dom: "[0, 1]", a: 0, b: 1, f: (x) => (x < 0.5 ? 1 : 0), exact: 0.5, exactTxt: "1/2" },
  { id: "f7", name: "sin(x)/x, f(0) = 1", dom: "[0, π]", a: 0, b: Math.PI, f: (x) => (x === 0 ? 1 : Math.sin(x) / x), exact: 1.8519370519824662, exactTxt: "Si(π) ≈ 1.8519370520" }
];
const NS = [1, 1.5, 2, 2.5, 3, 3.5, 4, 4.5, 5].map((e) => 2 * Math.floor(Math.pow(10, e) / 2) + 1); // odd sizes
const IDX_A = 4, IDX_B = 8; // N = 1001 and N = 100001 for the observed order

/* Riemann-type sums: partition of the domain into n equal subintervals */
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
function riemann(F, n) { // left, right, midpoint, approximate lower/upper Darboux sums (3 samples per subinterval)
  const h = (F.b - F.a) / n; let L = 0, R = 0, M = 0, lo = 0, up = 0, f0 = F.f(F.a);
  for (let i = 0; i < n; i++) {
    const f1 = F.f(i === n - 1 ? F.b : F.a + (i + 1) * h), fm = F.f(F.a + (i + 0.5) * h);
    L += f0; R += f1; M += fm;
    lo += Math.min(f0, fm, f1); up += Math.max(f0, fm, f1);
    f0 = f1;
  }
  return { left: L * h, right: R * h, mid: M * h, lower: lo * h, upper: up * h };
}

/* Lebesgue-type sums: partition of the range [m, M] into K levels; the measure of each preimage
   is estimated from N sample points (grid midpoints, or random points when rng is given) */
function lebesgueGrid(F, N, K, rng) {
  const len = F.b - F.a, v = new Float64Array(N);
  let mn = Infinity, mx = -Infinity, s = 0, s2 = 0;
  for (let i = 0; i < N; i++) {
    const x = rng ? F.a + rng() * len : F.a + ((i + 0.5) * len) / N;
    const y = F.f(x); v[i] = y; s += y; s2 += y * y;
    if (y < mn) mn = y; if (y > mx) mx = y;
  }
  const sd = Math.sqrt(Math.max(0, s2 / N - (s / N) * (s / N)));
  if (mx === mn) { const t = mn * len; return { lower: t, upper: t, mid: t, sd: 0 }; }
  const d = (mx - mn) / K, cnt = new Uint32Array(K);
  for (let i = 0; i < N; i++) { let k = Math.floor((v[i] - mn) / d); if (k >= K) k = K - 1; cnt[k]++; }
  let lo = 0, up = 0;
  for (let k = 0; k < K; k++) if (cnt[k]) { const y = mn + k * d; lo += y * cnt[k]; up += Math.min(y + d, mx) * cnt[k]; }
  lo *= len / N; up *= len / N;
  return { lower: lo, upper: up, mid: (lo + up) / 2, sd: sd };
}
/* Lebesgue lower/upper sums with preimage measures known in closed form (no grid, no sampling) */
function lebesgueExact(F, K) {
  if (F.id === "f3" || F.id === "f6") { const v = F.exact; return { lower: v, upper: v, evals: 2 }; } // two level sets of measure 1/2
  if (F.id === "f7") return null;
  let lo = 0, up = 0;
  if (F.id === "f5") { // levels 1 = y_0 < ... < y_K = sqrt(K); mu{y_k <= f < y_(k+1)} = y_k^-2 - y_(k+1)^-2; tail bin [sqrt(K), ∞) has measure 1/K
    const M = Math.sqrt(K), d = (M - 1) / K;
    for (let k = 0; k < K; k++) { const a = 1 + k * d, b = 1 + (k + 1) * d; lo += a * (1 / (a * a) - 1 / (b * b)); }
    lo += M * (1 / (M * M));
    return { lower: lo, upper: NaN, evals: K };
  }
  const d = (F.id === "f4" ? 0.5 : 1) / K;
  for (let k = 0; k < K; k++) {
    const a = k * d, b = (k + 1) * d;
    const mu = F.id === "f1" ? 2 * (Math.asin(Math.min(b, 1)) - Math.asin(a)) : F.id === "f2" ? Math.sqrt(b) - Math.sqrt(a) : 2 * (b - a);
    lo += a * mu; up += b * mu;
  }
  return { lower: lo, upper: up, evals: K };
}

/* ---------- Part 1 rendering ---------- */
function renderFunctionTable() {
  $("fnTable").innerHTML = table(["", "f(x)", "Interval", "Exact integral", "Note"], FUNCS.map((F) => [
    F.id, "<code>" + F.name + "</code>", F.dom, F.exactTxt,
    F.id === "f5" ? "unbounded at 0: improper Riemann integral" : F.id === "f7" ? "removable singularity at 0" :
      (F.id === "f3" || F.id === "f6") ? "jump at x = 0.5" : F.id === "f4" ? "kink at x = 0.5" : "smooth"]));
}
function renderSums() {
  const N = parseInt($("nSel").value, 10);
  $("riemannTable").innerHTML = table(["", "Left", "Right", "Midpoint", "Lower (Darboux)", "Upper (Darboux)", "Exact"],
    FUNCS.map((F) => { const r = riemann(F, N); return [F.id, g(r.left, 8), g(r.right, 8), g(r.mid, 8), g(r.lower, 8), g(r.upper, 8), g(F.exact, 8)]; }));
  $("lebTable").innerHTML = table(["", "Lower (grid)", "Upper (grid)", "Midpoint of bounds", "Lower (exact preimages)", "Upper (exact preimages)", "Exact"],
    FUNCS.map((F) => {
      const l = lebesgueGrid(F, N, N), x = lebesgueExact(F, N);
      return [F.id, g(l.lower, 8), g(l.upper, 8), g(l.mid, 8), x ? g(x.lower, 8) : "n/a", x ? g(x.upper, 8) : "n/a", g(F.exact, 8)];
    }));
  $("sumsN").textContent = fmtInt(N);
}

/* number-theoretic helpers for the pathological functions */
function thomaeUpper(n) { // upper Darboux sum of Thomae's function on n equal subintervals (exact)
  let s = 0;
  for (let i = 0; i < n; i++) {
    let q = 1;
    while (q < n && Math.floor((q * i + n - 1) / n) > Math.floor((q * (i + 1)) / n)) q++;
    s += 1 / q;
  }
  return s / n;
}
function totients(n) {
  const phi = new Array(n + 1); for (let i = 0; i <= n; i++) phi[i] = i;
  for (let p = 2; p <= n; p++) if (phi[p] === p) for (let k = p; k <= n; k += p) phi[k] -= phi[k] / p;
  return phi;
}

function orderOf(e) {
  const a = e[IDX_A], b = e[IDX_B];
  if (a === null || b === null) return "n/a";
  if (a === 0 || b === 0) return "exact";
  if (b < 1e-12) return "≈ roundoff";
  return (Math.log10(a / b) / Math.log10(NS[IDX_B] / NS[IDX_A])).toFixed(2);
}

async function computeEs1(cfg, stopped) {
  renderFunctionTable();
  renderSums();
  await tick();
  /* convergence data: errors against N */
  const D = FUNCS.map(() => ({ R: [], Rr: [], L: [], X: [], M: [] }));
  for (let j = 0; j < FUNCS.length; j++) {
    const F = FUNCS[j];
    for (let i = 0; i < NS.length; i++) {
      const N = NS[i];
      D[j].R.push(Math.abs(riemannMid(F, N) - F.exact));
      D[j].Rr.push(Math.abs(riemannRight(F, N) - F.exact));
      D[j].L.push(Math.abs(lebesgueGrid(F, N, N).mid - F.exact));
      const x = lebesgueExact(F, N);
      D[j].X.push(x ? Math.abs(x.lower - F.exact) : null);
      D[j].M.push(Math.abs(lebesgueGrid(F, N, N, mulberry32(cfg.seed + 101 * j + i)).mid - F.exact));
    }
    if (stopped()) return;
    await tick();
  }
  const pts = (arr) => arr.map((e, i) => [NS[i], e]);
  const sA = FUNCS.map((F, j) => ({ name: F.id + ": " + F.name, pts: pts(D[j].R) }));
  const sB = FUNCS.map((F, j) => ({ name: F.id + ": " + F.name, pts: pts(D[j].L) }));
  plot($("cvRiemann"), { title: "Riemann midpoint sums: |error| vs n", xlabel: "n (subintervals)", ylabel: "|error|", series: sA });
  plot($("cvLeb"), { title: "Lebesgue grid sums: |error| vs N", xlabel: "N (points = levels)", ylabel: "|error|", series: sB });
  legend("lgRiemann", sA); legend("lgLeb", sB);
  const j1 = 0, j5 = 4;
  const s1 = [{ name: "Riemann midpoint", pts: pts(D[j1].R) }, { name: "Lebesgue grid", pts: pts(D[j1].L) },
    { name: "Lebesgue exact preimages (lower)", pts: pts(D[j1].X) }, { name: "Lebesgue Monte Carlo", pts: pts(D[j1].M), dash: true }];
  const s5 = [{ name: "Riemann midpoint", pts: pts(D[j5].R) }, { name: "Riemann right", pts: pts(D[j5].Rr) },
    { name: "Lebesgue grid", pts: pts(D[j5].L) }, { name: "Lebesgue exact preimages (lower)", pts: pts(D[j5].X) },
    { name: "Lebesgue Monte Carlo", pts: pts(D[j5].M), dash: true }];
  plot($("cvF1"), { title: "f1 = sin(x) on [0, π]", xlabel: "N", ylabel: "|error|", series: s1 });
  plot($("cvF5"), { title: "f5 = 1/√x on (0, 1]", xlabel: "N", ylabel: "|error|", series: s5 });
  legend("lgF1", s1); legend("lgF5", s5);
  /* comparison table at N = 10001 (index 6) */
  $("convTable").innerHTML = table(["", "|R − exact|", "|L grid − exact|", "|L exact − exact|", "order R", "order L grid", "order L exact", "|R − L grid|"],
    FUNCS.map((F, j) => {
      const R = riemannMid(F, NS[6]), L = lebesgueGrid(F, NS[6], NS[6]).mid;
      return [F.id, ge(D[j].R[6]), ge(D[j].L[6]), D[j].X[6] === null ? "n/a" : ge(D[j].X[6]), orderOf(D[j].R), orderOf(D[j].L), orderOf(D[j].X), ge(Math.abs(R - L))];
    }));
  /* Monte Carlo table */
  const mcRows = [];
  FUNCS.forEach((F, j) => {
    [NS[6], NS[8]].forEach((N, k) => {
      const r = lebesgueGrid(F, N, N, mulberry32(cfg.seed + 977 * j + k));
      const noise = F.id === "f5" ? "∞ (infinite variance)" : ge((r.sd * (F.b - F.a)) / Math.sqrt(N));
      mcRows.push([F.id, fmtInt(N), g(r.mid, 8), ge(Math.abs(r.mid - F.exact)), noise]);
    });
  });
  $("mcTable").innerHTML = table(["", "N", "Estimate", "|error|", "Expected noise σ(b−a)/√N"], mcRows);
  await tick();
  /* efficiency at N = K = 10^6 for f1 */
  const NT = 1000000, F1 = FUNCS[0];
  const tR = timeIt(() => riemannMid(F1, NT), 3), tL = timeIt(() => lebesgueGrid(F1, NT, NT), 3);
  const tX = timeIt(() => lebesgueExact(F1, NT), 3), tM = timeIt(() => lebesgueGrid(F1, NT, NT, mulberry32(cfg.seed)), 3);
  $("effTable").innerHTML = table(["Method", "Evaluations of f", "Other work", "Time (ms, best of 3)", "|error|"], [
    ["Riemann midpoint", fmtInt(NT), "none", g(tR.ms, 3), ge(Math.abs(tR.res - F1.exact))],
    ["Lebesgue grid", fmtInt(NT), "array of N values, histogram with K bins", g(tL.ms, 3), ge(Math.abs(tL.res.mid - F1.exact))],
    ["Lebesgue exact preimages", "0", fmtInt(NT) + " evaluations of asin", g(tX.ms, 3), ge(Math.abs(tX.res.lower - F1.exact))],
    ["Lebesgue Monte Carlo", fmtInt(NT), "N random draws, array, histogram", g(tM.ms, 3), ge(Math.abs(tM.res.mid - F1.exact))]]);
  /* pathological functions */
  const rows = [10, 100, 1000].map((n) => { let up = 0; for (let i = 0; i < n; i++) up += 1 / n; return [fmtInt(n), g(up, 6), "0", "0"]; });
  const rng = mulberry32(cfg.seed); let dy = 0; for (let i = 0; i < 1000; i++) if (Number.isInteger(rng() * 4294967296)) dy++;
  $("dirTable").innerHTML = table(["n", "Upper sum U<sub>n</sub>", "Lower sum L<sub>n</sub>", "Lebesgue sum"], rows);
  $("dyadic").textContent = fmtInt(dy);
  const tn = [10, 100, 1000, 10000];
  $("thomaeTable").innerHTML = table(["n", "Upper sum U<sub>n</sub>", "Lower sum L<sub>n</sub>"], tn.map((n) => [fmtInt(n), g(thomaeUpper(n), 6), "0"]));
  const phi = totients(1000), lv = [1, 2, 5, 10, 100, 1000];
  $("thomaeLevels").innerHTML = table(["k", "Level set {f ≥ 1/k}", "Number of points", "Measure"], lv.map((k) => {
    let c = 1; for (let q = 1; q <= k; q++) c += phi[q];
    return [k, "rationals p/q in [0, 1] with q ≤ k", fmtInt(c), "0"];
  }));
}

/* ---------- Part 2: normal CDF ---------- */
const SQRT_PI = Math.sqrt(Math.PI), SQRT2 = Math.SQRT2, INV_SQRT_2PI = 1 / Math.sqrt(2 * Math.PI);
const T_SWITCH = 2; // switch from series to continued fraction at t = |x|/√2
const phiPdf = (u) => INV_SQRT_2PI * Math.exp(-0.5 * u * u);

/* erf(t) = (2/√π) e^(−t²) Σ 2^n t^(2n+1) / (1·3·…·(2n+1)); all terms positive (no cancellation) */
function erfSeries(t) {
  const t2 = t * t; let term = t, sum = t, n = 0;
  while (n < 1000) { n++; term *= (2 * t2) / (2 * n + 1); sum += term; if (term < 1e-17 * sum) break; }
  return { value: (2 / SQRT_PI) * Math.exp(-t2) * sum, terms: n + 1 };
}
function erfSeriesN(t, N) { // first N terms of the same series
  let term = t, sum = t;
  for (let n = 1; n < N; n++) { term *= (2 * t * t) / (2 * n + 1); sum += term; }
  return (2 / SQRT_PI) * Math.exp(-t * t) * sum;
}
function erfAlternating(t, N) { // textbook Maclaurin series, alternating signs
  let term = t, sum = t;
  for (let n = 1; n < N; n++) { term *= -(t * t) / n; sum += term / (2 * n + 1); }
  return (2 / SQRT_PI) * sum;
}
/* erfc(t) for t > 0 by the continued fraction DLMF 7.9.2, evaluated with the modified Lentz method:
   √π e^(t²) erfc(t) = 2t / (2t²+1 − 1·2/(2t²+5 − 3·4/(2t²+9 − …))) */
function erfcCF(t, maxIter, tol) {
  maxIter = maxIter || 500; tol = tol === undefined ? 1e-16 : tol;
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
let lastWork = { terms: 0, iters: 0 };
function upperTail(x) { // 1 − Φ(x) for x ≥ 0, i.e. erfc(x/√2)/2
  const t = x / SQRT2;
  if (t < T_SWITCH) { const s = erfSeries(t); lastWork.terms = s.terms; return 0.5 - 0.5 * s.value; }
  const c = erfcCF(t); lastWork.iters = c.iters; return 0.5 * c.value;
}
function normCdf(x) {
  if (Number.isNaN(x)) return NaN;
  if (!Number.isFinite(x)) return x > 0 ? 1 : 0;
  const q = upperTail(Math.abs(x));
  return x >= 0 ? 1 - q : q;
}
function trapz(f, a, b, n) { const h = (b - a) / n; let s = 0.5 * (f(a) + f(b)); for (let i = 1; i < n; i++) s += f(a + i * h); return s * h; }
function simpson(f, a, b, n) { const h = (b - a) / n; let s = f(a) + f(b); for (let i = 1; i < n; i++) s += f(a + i * h) * (i % 2 ? 4 : 2); return (s * h) / 3; }
function cdfAS(x) { // erf approximation, Abramowitz & Stegun 7.1.26 (|error of erf| ≤ 1.5e-7)
  const t0 = Math.abs(x) / SQRT2, t = 1 / (1 + 0.3275911 * t0);
  const poly = ((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t;
  const e = 1 - poly * Math.exp(-t0 * t0);
  return x >= 0 ? 0.5 * (1 + e) : 0.5 * (1 - e);
}

/* reference values: NIST Handbook table (5 decimals, area 0→x plus 0.5) and 40-digit mpmath values (computed offline) */
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
  { x: -8, nist: null, hp: 6.2209605742717841e-16 }
];
const TAILS = [ // Q(x) = 1 − Φ(x)
  { x: 3, q: 0.0013498980316300946 }, { x: 4, q: 3.1671241833119921e-5 }, { x: 5, q: 2.8665157187919391e-7 },
  { x: 6, q: 9.8658764503769814e-10 }, { x: 8, q: 6.2209605742717841e-16 }
];
const hpPhi = (x) => REFS.find((r) => r.x === x).hp;

async function computeEs2() {
  /* 2.2 reference comparison */
  $("refTable").innerHTML = table(["x", "Φ(x), this implementation", "NIST table (5 decimals)", "|Φ − NIST|", "within 5·10⁻⁶", "High-precision reference", "Relative error"],
    REFS.map((r) => {
      const v = normCdf(r.x);
      return [r.x, v.toPrecision(16), r.nist === null ? "—" : r.nist.toFixed(5), r.nist === null ? "—" : ge(Math.abs(v - r.nist)),
        r.nist === null ? "—" : (Math.abs(v - r.nist) <= 5e-6 ? "yes" : "NO"), r.hp.toPrecision(17), ge(Math.abs(v - r.hp) / r.hp)];
    }));
  await tick();
  /* 2.3 accuracy: series terms, CF iterations, cost, consistency */
  const xs3 = [1, 2, 3], termsList = [2, 5, 10, 15, 20, 30, 40];
  $("serTable").innerHTML = table(["Terms N", "|error| at x = 1", "|error| at x = 2", "|error| at x = 3"],
    termsList.map((N) => [N].concat(xs3.map((x) => ge(Math.abs(0.5 + 0.5 * erfSeriesN(x / SQRT2, N) - hpPhi(x)))))));
  const itList = [1, 2, 4, 8, 16, 32], tx = [3, 4, 5, 8];
  $("cfTable").innerHTML = table(["Iterations K", "rel. error at x = 3", "rel. error at x = 4", "rel. error at x = 5", "rel. error at x = 8"],
    itList.map((K) => [K].concat(tx.map((x) => { const q = TAILS.find((t) => t.x === x).q; return ge(Math.abs(0.5 * erfcCF(x / SQRT2, K, 0).value - q) / q); }))));
  const sSer = xs3.map((x) => ({ name: "series, x = " + x + " (abs.)", pts: Array.from({ length: 40 }, (_, i) => [i + 1, Math.abs(0.5 + 0.5 * erfSeriesN(x / SQRT2, i + 1) - hpPhi(x))]) }));
  const sCf = [3, 5].map((x) => ({ name: "continued fraction, x = " + x + " (rel.)", dash: true, pts: Array.from({ length: 40 }, (_, i) => { const q = TAILS.find((t) => t.x === x).q; return [i + 1, Math.abs(0.5 * erfcCF(x / SQRT2, i + 1, 0).value - q) / q]; }) }));
  const sA = sSer.concat(sCf);
  plot($("cvSer"), { title: "Series terms and continued-fraction iterations", xlabel: "number of terms / iterations", ylabel: "error", series: sA });
  legend("lgSer", sA);
  const nl = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048], sQ = [];
  [1, 3].forEach((x) => {
    sQ.push({ name: "trapezoid, x = " + x, pts: nl.map((n) => [n, Math.abs(0.5 + trapz(phiPdf, 0, x, n) - hpPhi(x))]) });
    sQ.push({ name: "Simpson, x = " + x, dash: true, pts: nl.map((n) => [n, Math.abs(0.5 + simpson(phiPdf, 0, x, n) - hpPhi(x))]) });
  });
  plot($("cvTrap"), { title: "Quadrature of the density: |error| vs n", xlabel: "n (subintervals)", ylabel: "|error|", series: sQ });
  legend("lgTrap", sQ);
  await tick();
  /* cost and consistency over a grid */
  const M = 200000, grid = Array.from({ length: M }, (_, i) => -6 + (12 * i) / (M - 1));
  let maxTerms = 0, maxIters = 0;
  grid.forEach((x) => { lastWork.terms = 0; lastWork.iters = 0; normCdf(x); maxTerms = Math.max(maxTerms, lastWork.terms); maxIters = Math.max(maxIters, lastWork.iters); });
  const per = (ms, cnt) => g((ms * 1e6) / cnt, 3);
  const tH = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) s += normCdf(grid[i]); return s; }, 3);
  const tS = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) { const x = grid[i], v = erfSeries(Math.abs(x) / SQRT2).value; s += x >= 0 ? 0.5 + 0.5 * v : 0.5 - 0.5 * v; } return s; }, 3);
  const tA = timeIt(() => { let s = 0; for (let i = 0; i < M; i++) s += cdfAS(grid[i]); return s; }, 3);
  const MQ = 5000, tT = timeIt(() => { let s = 0; for (let i = 0; i < MQ; i++) s += 0.5 + trapz(phiPdf, 0, grid[i * 40] > 0 ? grid[i * 40] : 1, 100); return s; }, 3);
  const tP = timeIt(() => { let s = 0; for (let i = 0; i < MQ; i++) s += 0.5 + simpson(phiPdf, 0, grid[i * 40] > 0 ? grid[i * 40] : 1, 100); return s; }, 3);
  $("costTable").innerHTML = table(["Method", "Work per evaluation", "Time per evaluation (ns)"], [
    ["Hybrid: series for |x| < 2√2, continued fraction beyond", "series ≤ " + maxTerms + " terms; CF ≤ " + maxIters + " iterations", per(tH.ms, M)],
    ["Series only (no continued fraction)", "up to " + maxTerms + "+ terms", per(tS.ms, M)],
    ["Trapezoid, n = 100", "101 evaluations of the density", per(tT.ms, MQ)],
    ["Simpson, n = 100", "101 evaluations of the density", per(tP.ms, MQ)],
    ["A&amp;S 7.1.26 approximation", "5 multiplications, one exp", per(tA.ms, M)]]);
  let sym = 0, mono = true, prev = -1;
  for (let i = 0; i <= 2000; i++) { const x = -8 + (16 * i) / 2000, v = normCdf(x); sym = Math.max(sym, Math.abs(v + normCdf(-x) - 1)); if (v < prev) mono = false; prev = v; }
  let ov = 0;
  for (let i = 0; i <= 120; i++) { const t = 1.5 + (1.5 * i) / 120, a = 1 - erfSeries(t).value, b = erfcCF(t).value; ov = Math.max(ov, Math.abs(a - b) / b); }
  $("checkOut").textContent = "max |Φ(x) + Φ(−x) − 1| over 2001 points in [−8, 8]: " + ge(sym) + "; monotone non-decreasing: " + (mono ? "yes" : "NO") +
    "; max relative difference between 1 − erf (series) and erfc (continued fraction) for t in [1.5, 3]: " + ge(ov) + ".";
  await tick();
  /* 2.6 approaches compared */
  const X6 = [0.5, 1, 2, 4, 8], w = { s: 0, c: 0 };
  X6.forEach((x) => { lastWork.terms = 0; lastWork.iters = 0; normCdf(x); w.s = Math.max(w.s, lastWork.terms); w.c = Math.max(w.c, lastWork.iters); });
  const err = (fn) => X6.map((x) => ge(Math.abs(fn(x) - hpPhi(x))));
  $("cmpTable").innerHTML = table(["Method", "x = 0.5", "x = 1", "x = 2", "x = 4", "x = 8", "Work"], [
    ["Trapezoid, n = 100"].concat(err((x) => 0.5 + trapz(phiPdf, 0, x, 100)), ["101 evaluations"]),
    ["Trapezoid, n = 1000"].concat(err((x) => 0.5 + trapz(phiPdf, 0, x, 1000)), ["1001 evaluations"]),
    ["Simpson, n = 100"].concat(err((x) => 0.5 + simpson(phiPdf, 0, x, 100)), ["101 evaluations"]),
    ["Simpson, n = 1000"].concat(err((x) => 0.5 + simpson(phiPdf, 0, x, 1000)), ["1001 evaluations"]),
    ["Maclaurin series, alternating form, 150 terms"].concat(err((x) => 0.5 + 0.5 * erfAlternating(x / SQRT2, 150)), ["150 terms"]),
    ["Maclaurin series, positive-term form (converged)"].concat(err((x) => 0.5 + 0.5 * erfSeries(x / SQRT2).value), ["up to " + erfSeries(8 / SQRT2).terms + " terms"]),
    ["erf-based hybrid (this implementation)"].concat(err(normCdf), ["series ≤ " + w.s + " terms; CF ≤ " + w.c + " iterations"]),
    ["A&amp;S 7.1.26 approximation of erf"].concat(err(cdfAS), ["constant"])]);
  $("tailTable").innerHTML = table(["x", "1 − Φ(x) by subtraction", "erfc(x/√2)/2 by continued fraction", "Reference Q(x)", "rel. error (subtraction)", "rel. error (continued fraction)"],
    TAILS.map((t) => {
      const sub = 1 - normCdf(t.x), cf = 0.5 * erfcCF(t.x / SQRT2).value;
      return [t.x, g(sub, 8), g(cf, 8), g(t.q, 8), ge(Math.abs(sub - t.q) / t.q), ge(Math.abs(cf - t.q) / t.q)];
    }));
}

/* ---------- configuration and control flow ---------- */
let stopFlag = false, running = false;
function parseConfig() {
  const s = String($("seedInput").value).trim();
  if (!/^\d+$/.test(s)) return "The seed must be a non-negative integer.";
  const seed = parseInt(s, 10);
  if (seed > 4294967295) return "The seed must be at most 4294967295.";
  return { seed: seed };
}
async function runAll() {
  if (running) return;
  hideMsg("simError");
  const cfg = parseConfig();
  if (typeof cfg === "string") { showMsg("simError", cfg); return; }
  running = true; stopFlag = false; $("simStatus").textContent = "Running…";
  try {
    await computeEs1(cfg, () => stopFlag);
    if (stopFlag) { $("simStatus").textContent = "Stopped."; return; }
    await computeEs2();
    $("simStatus").textContent = "Done (seed " + cfg.seed + ").";
  } catch (e) {
    showMsg("simError", "Error: " + (e && e.message ? e.message : e)); $("simStatus").textContent = "Failed.";
  } finally { running = false; }
}
function init() {
  $("btnRun").addEventListener("click", runAll);
  $("btnSeed").addEventListener("click", () => { $("seedInput").value = Math.floor(Math.random() * 1e9); runAll(); });
  $("btnStop").addEventListener("click", () => { stopFlag = true; });
  $("nSel").addEventListener("change", () => { try { renderSums(); } catch (e) { showMsg("simError", "Error: " + e.message); } });
  runAll();
}
document.addEventListener("DOMContentLoaded", init);
