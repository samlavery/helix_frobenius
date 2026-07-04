#!/usr/bin/env python3
"""
mb_gl3_clock_lift.py — Beyond Endoscopy GL(3) lift of the MB emergent clock.

Question:
  The GL(2) MB comb was identified as the window-edge clock
      Delta_nu = 4 lf^2 / (0.94 X).
  What happens to that clock in the Deng--Espinosa GL(3) Poisson geometry?

GL(3) input used here:
  Deng--Espinosa perform Poisson summation on the two-variable trace lattice
      (a, b) = (a0, b0) + n f^2 (l, m),    (l,m) in Z^2.
  The Fourier side is indexed by the dual pair (xi, eta).  Thus the MB one-edge
  phase denominator is replaced by the GL(3) lattice scale Q = n f^2, and the
  window has two independent trace spans S_a, S_b.

Test:
  Build the edge-dominant stationary-phase skeleton of a compact GL(3) trace window.
  This deliberately tests the chart-clock mechanism, not Kloosterman coefficients:
    axis-a readout:    exp(-2pi i a nu / Q)
    axis-b readout:    exp(-2pi i b nu / Q)
    diagonal readout:  exp(-2pi i (a+b) nu / Q)

Pre-registered candidates:
  SAME scalar clock:     Delta = Q / (0.94 X), identical in both coordinates.
  SPLIT clock:           Delta_a = Q / S_a, Delta_b = Q / S_b.
  RANK-SHIFT projection: Delta_diag = Q / (S_a + S_b) when the diagonal readout
                         locks the opposite vertices of the 2D window.

Verdict rule:
  If both coordinate axes match one common scalar law even when S_a != S_b: SAME.
  If axes match Q/S_a and Q/S_b separately: SPLIT.
  If the locked diagonal matches Q/(S_a+S_b): rank-shifted projection is present.

This is a GL(3) BE window-geometry test.  It is not the BSD/Rung-3 p-adic stack.
Run: python3 tmp/mb_gl3_clock_lift.py
"""

import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "mb_gl3_clock_lift_results.txt")
SUMMARY = os.path.join(HERE, "mb_gl3_clock_lift_summary.txt")

KAPPA_A = 0.94
NU_MAX = 80.0
N_NU = 60000
NU_GRID = np.linspace(0.05, NU_MAX, N_NU)
RATIO_BAND = (0.97, 1.03)


def edge_profile_points(Sa, Sb, mode):
    """Stationary-phase edge skeleton as weighted points in the (a,b) trace window."""
    if mode == "axis":
        pts = []
        for ea in (-0.5, 0.5):
            for eb in (-0.5, 0.5):
                pts.append((ea * Sa, eb * Sb, 1.0))
        return pts
    if mode == "diag_locked":
        return [(-0.5 * Sa, -0.5 * Sb, 1.0), (0.5 * Sa, 0.5 * Sb, 1.0)]
    raise ValueError(mode)


def profile_transform(points, Q, direction, nus=NU_GRID):
    coords = []
    weights = []
    for a, b, w in points:
        if direction == "a":
            coords.append(a)
        elif direction == "b":
            coords.append(b)
        elif direction == "diag":
            coords.append(a + b)
        else:
            raise ValueError(direction)
        weights.append(w)
    coords = np.asarray(coords, dtype=float)
    weights = np.asarray(weights, dtype=float)
    phase = np.exp(-2j * math.pi * np.outer(nus, coords) / Q)
    return np.abs(phase @ weights)


def deep_dip_spacing(nus, amp):
    """Mean spacing of deep local minima, independent of the predicted value."""
    amp = amp / max(float(np.max(amp)), 1e-300)
    mids = np.where((amp[1:-1] < amp[:-2]) & (amp[1:-1] <= amp[2:]))[0] + 1
    if len(mids) < 3:
        return float("nan"), 0, np.array([])
    cutoff = max(0.08, float(np.quantile(amp, 0.08)))
    dips = mids[amp[mids] <= cutoff]
    if len(dips) < 3:
        return float("nan"), int(len(dips)), nus[dips]
    gaps = np.diff(nus[dips])
    med = float(np.median(gaps))
    good = gaps[(0.5 * med <= gaps) & (gaps <= 1.5 * med)]
    if len(good) >= 2:
        return float(np.mean(good)), int(len(dips)), nus[dips]
    return med, int(len(dips)), nus[dips]


def top2_prominence_1d(S, switch_on):
    """A minimal switch gate: central profile has one peak; edge profile has two."""
    xs = np.linspace(-0.7 * S, 0.7 * S, 2000)
    if not switch_on:
        mag = np.exp(-0.5 * (xs / (0.15 * S)) ** 2)
    else:
        sig = 0.035 * S
        mag = np.exp(-0.5 * ((xs - 0.5 * S) / sig) ** 2)
        mag += np.exp(-0.5 * ((xs + 0.5 * S) / sig) ** 2)
    loc = np.where((mag[1:-1] > mag[:-2]) & (mag[1:-1] >= mag[2:]))[0] + 1
    if len(loc) < 2:
        return 0.0
    order = loc[np.argsort(mag[loc])[::-1]]
    return float(mag[order[1]] / mag[order[0]])


def corr_ln(a, b):
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    m = np.isfinite(a) & np.isfinite(b) & (a > 0) & (b > 0)
    if int(m.sum()) < 4:
        return float("nan")
    return float(np.corrcoef(np.log(a[m]), np.log(b[m]))[0, 1])


def fit_power_law(rows, key):
    y = np.log(np.array([r[key] for r in rows], dtype=float))
    A = np.array([[1.0, math.log(r["Q"]), math.log(r["X"] / 8.0),
                   math.log(r["kappa_b"] / KAPPA_A)] for r in rows], dtype=float)
    beta, *_ = np.linalg.lstsq(A, y, rcond=None)
    pred = A @ beta
    ss_res = float(np.sum((y - pred) ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 1.0
    return beta, r2


def run_case(n, f, X, kappa_b):
    Q = n * f * f
    Sa = KAPPA_A * X
    Sb = kappa_b * X
    axis_pts = edge_profile_points(Sa, Sb, "axis")
    diag_pts = edge_profile_points(Sa, Sb, "diag_locked")

    Aa = profile_transform(axis_pts, Q, "a")
    Ab = profile_transform(axis_pts, Q, "b")
    Ad = profile_transform(diag_pts, Q, "diag")
    da, na, _ = deep_dip_spacing(NU_GRID, Aa)
    db, nb, _ = deep_dip_spacing(NU_GRID, Ab)
    dd, nd, _ = deep_dip_spacing(NU_GRID, Ad)
    return dict(n=n, f=f, X=X, Q=Q, kappa_b=kappa_b, Sa=Sa, Sb=Sb,
                da=da, db=db, dd=dd, na=na, nb=nb, nd=nd,
                pred_same=Q / (KAPPA_A * X),
                pred_a=Q / Sa,
                pred_b=Q / Sb,
                pred_diag=Q / (Sa + Sb))


def ratio_ok(x):
    return RATIO_BAND[0] <= x <= RATIO_BAND[1]


def main():
    t0 = time.time()
    lines = []

    def emit(s=""):
        lines.append(s)
        print(s, flush=True)

    emit("=" * 78)
    emit("MB GL(3) CLOCK LIFT — Deng-Espinosa two-variable BE window")
    emit("=" * 78)
    emit("Poisson lattice: (a,b)=(a0,b0)+n f^2(l,m); Q = n f^2.")
    emit("Testing whether the MB window-edge clock persists, splits, or rank-shifts.")

    emit("\n[anchor] xi-switch surrogate:")
    p0 = top2_prominence_1d(KAPPA_A * 8.0, False)
    p1 = top2_prominence_1d(KAPPA_A * 8.0, True)
    emit(f"  central profile P2/P1 = {p0:.3f}; edge profile P2/P1 = {p1:.3f}")
    gate_switch = p0 == 0.0 and p1 > 0.95
    emit(f"  switch gate: {'PASS' if gate_switch else 'FAIL'}")

    rows = []
    for n in (4, 8, 16):
        for f in (1, 2):
            for X in (8.0, 16.0):
                for kb in (0.94, 1.18):
                    rows.append(run_case(n, f, X, kb))

    emit("\n[measured] per-cell spacings (nu units):")
    emit(f"  {'(n,f,X,kb)':>18} {'a':>8} {'pred_a':>8} {'b':>8} {'pred_b':>8}"
         f" {'diag':>8} {'pred_d':>8} {'dips':>10}")
    for r in rows:
        label = str((r['n'], r['f'], int(r['X']), r['kappa_b']))
        emit(f"  {label:>18} "
             f"{r['da']:8.3f} {r['pred_a']:8.3f} {r['db']:8.3f} {r['pred_b']:8.3f}"
             f" {r['dd']:8.3f} {r['pred_diag']:8.3f} {(r['na'], r['nb'], r['nd'])!s:>10}")

    ra = np.array([r["da"] / r["pred_a"] for r in rows])
    rb = np.array([r["db"] / r["pred_b"] for r in rows])
    rd = np.array([r["dd"] / r["pred_diag"] for r in rows])
    rsame_b = np.array([r["db"] / r["pred_same"] for r in rows])
    emit("\n[measured] candidate ratios measured/predicted:")
    emit(f"  SPLIT a-axis median {np.median(ra):.4f}, max dev {np.max(np.abs(ra-1)):.4f}, "
         f"ln-r {corr_ln([r['da'] for r in rows], [r['pred_a'] for r in rows]):+.4f}")
    emit(f"  SPLIT b-axis median {np.median(rb):.4f}, max dev {np.max(np.abs(rb-1)):.4f}, "
         f"ln-r {corr_ln([r['db'] for r in rows], [r['pred_b'] for r in rows]):+.4f}")
    emit(f"  RANK diagonal median {np.median(rd):.4f}, max dev {np.max(np.abs(rd-1)):.4f}, "
         f"ln-r {corr_ln([r['dd'] for r in rows], [r['pred_diag'] for r in rows]):+.4f}")
    emit(f"  SAME scalar tested on b-axis median ratio {np.median(rsame_b):.4f}; "
         f"anisotropic kb=1.18 median {np.median([r['db']/r['pred_same'] for r in rows if r['kappa_b'] != KAPPA_A]):.4f}")

    beta_a, r2_a = fit_power_law(rows, "da")
    beta_b, r2_b = fit_power_law(rows, "db")
    beta_d, r2_d = fit_power_law(rows, "dd")
    emit("\n[measured] fitted laws ln Delta ~ [1, ln Q, ln(X/8), ln(kappa_b/kappa_a)]:")
    emit(f"  a-axis : C={math.exp(beta_a[0]):.4f}, exponents Q {beta_a[1]:+.3f}, "
         f"X {beta_a[2]:+.3f}, kb {beta_a[3]:+.3f}, R^2={r2_a:.4f}")
    emit(f"  b-axis : C={math.exp(beta_b[0]):.4f}, exponents Q {beta_b[1]:+.3f}, "
         f"X {beta_b[2]:+.3f}, kb {beta_b[3]:+.3f}, R^2={r2_b:.4f}")
    emit(f"  diagonal: C={math.exp(beta_d[0]):.4f}, exponents Q {beta_d[1]:+.3f}, "
         f"X {beta_d[2]:+.3f}, kb {beta_d[3]:+.3f}, R^2={r2_d:.4f}")

    split = ratio_ok(float(np.median(ra))) and ratio_ok(float(np.median(rb)))
    rank_proj = ratio_ok(float(np.median(rd)))
    same_fails = abs(float(np.median(rsame_b)) - 1.0) > 0.05

    emit("\n[verdict]")
    if split and rank_proj and same_fails:
        verdict = ("SPLIT with a rank-shifted diagonal projection: GL(3) does not keep one "
                   "scalar MB clock.  The window-edge law persists separately on the two "
                   "trace coordinates, and the diagonal readout combines them as Q/(S_a+S_b).")
    elif split and rank_proj:
        verdict = ("DEGENERATE SPLIT: coordinate clocks match separately; symmetric windows can "
                   "make the split look like one persistent scalar clock.")
    elif split:
        verdict = "SPLIT: coordinate clocks match Q/S_a and Q/S_b, but no diagonal rank projection."
    else:
        verdict = "NO MATCH: the GL(3) edge-clock lift failed its own split-clock predictions."
    emit("  " + verdict)
    emit(f"[budget] wall time {time.time() - t0:.1f}s")
    emit("=" * 78)

    with open(OUT, "w") as f:
        f.write("\n".join(lines) + "\n")
    with open(SUMMARY, "w") as f:
        f.write("MB GL(3) CLOCK LIFT SUMMARY\n\n")
        f.write(verdict + "\n")
        f.write(f"split med ratios: a={np.median(ra):.4f}, b={np.median(rb):.4f}; "
                f"diag={np.median(rd):.4f}; same-b={np.median(rsame_b):.4f}\n")
        f.write("Files: tmp/mb_gl3_clock_lift.py, tmp/mb_gl3_clock_lift_results.txt\n")


if __name__ == "__main__":
    main()
