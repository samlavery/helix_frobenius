#!/usr/bin/env python3
"""
mb_gl3_wall_lift.py - Beyond Endoscopy GL(3) Deng-Espinosa wall/clock lift.

Purpose:
  Run the GL(3) test needed after the MB emergent-clock result:
    does the residual gamma-spread persist as one scalar clock,
    split across the two trace coordinates, or rank-shift under GL(3)
    coefficient homogeneity?

GL(3) input modeled here:
  Deng-Espinosa work on determinant hyperplanes c = +/-1 and the discriminant

      Pol(a,b,c) = a^2 b^2 - 4 b^3 - 4 a^3 c + 18 a b c - 27 c^2.

  The coefficient homogeneity is

      Pol(r a, r^2 b, r^3 c) = r^6 Pol(a,b,c).

  Their Poisson lattice is two-variable:

      (a,b) = (a0,b0) + n f^2 (l,m),        Q = n f^2.

  The archimedean dichotomy is read by the sign of Pol:
      Pol > 0: three-real-root branch,
      Pol < 0: one-real-root/complex-pair branch.

Numerical model:
  This is a Deng-Espinosa coefficient-window test.  It uses compact theta-like
  windows on the normalized coefficient variables

      a = T A,       b = T^2 B,       T = X/8,

  with fixed normalized support in (A,B).  Thus the raw trace spans are
      S_a ~ T,       S_b ~ T^2,
  which is the GL(3) rank/homogeneity lift of the MB window-edge clock.

  The residual wall profile uses the Deng-Espinosa singular factor
      |Pol(A,B,+/-1)|^alpha
  with alpha = -1/2, split by the Pol > 0 and Pol < 0 gamma branches.

Output:
  tmp/mb_gl3_wall_lift_results.txt
  tmp/mb_gl3_wall_lift_summary.txt

Run:
  python3 tmp/mb_gl3_wall_lift.py
"""

from __future__ import annotations

import math
import os
import time

import numpy as np


HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "mb_gl3_wall_lift_results.txt")
SUMMARY = os.path.join(HERE, "mb_gl3_wall_lift_summary.txt")

# MB invariant currently being compared, not imposed.
GL2_GAMMA_SPREAD = 0.441
GL2_GAMMA_RADIUS = 0.058

# Never-clip support in normalized Deng-Espinosa coefficient variables.
KAPPA = 0.94
A0 = 3.0
B0 = 3.0
S0_A = 2.0 * A0 * KAPPA
S0_B = 2.0 * B0 * KAPPA

ALPHA = -0.5
NU_GRID = np.linspace(2.0, 24.0, 120)
N_GRID = 168
EPS_SCALE = 2.5e-3


def pol(a: np.ndarray, b: np.ndarray, c: float) -> np.ndarray:
    """GL(3) cubic discriminant for X^3 - a X^2 + b X - c."""
    return a * a * b * b - 4.0 * b**3 - 4.0 * a**3 * c + 18.0 * a * b * c - 27.0 * c * c


def bump_centered(coord: np.ndarray, span: float) -> np.ndarray:
    """Smooth compact bump supported on |coord| < span/2."""
    z = 2.0 * coord / span
    out = np.zeros_like(coord, dtype=float)
    m = np.abs(z) < 1.0
    out[m] = np.exp(1.0 - 1.0 / (1.0 - z[m] ** 2))
    return out


def build_profile(csign: int, X: float, branch: str):
    """Build a compact Deng-Espinosa coefficient profile on c = +/-1."""
    T = X / 8.0
    Sa = S0_A * T
    Sb = S0_B * T * T

    avec = np.linspace(-0.5 * Sa, 0.5 * Sa, N_GRID)
    bvec = np.linspace(-0.5 * Sb, 0.5 * Sb, N_GRID)
    da = float(avec[1] - avec[0])
    db = float(bvec[1] - bvec[0])
    Araw, Braw = np.meshgrid(avec, bvec, indexing="ij")

    Anorm = Araw / T
    Bnorm = Braw / (T * T)
    P = pol(Anorm, Bnorm, float(csign))
    absP = np.abs(P)
    W = bump_centered(Araw, Sa) * bump_centered(Braw, Sb)

    if branch == "real3":
        mask = P > 0.0
    elif branch == "mixed":
        mask = P < 0.0
    else:
        raise ValueError(branch)

    support = (W > 0.0) & mask
    if int(np.count_nonzero(support)) == 0:
        raise RuntimeError(f"empty support for c={csign}, X={X}, branch={branch}")

    eps = EPS_SCALE * float(np.median(absP[support]))
    density = W * mask * np.power(absP + eps, ALPHA)
    mass = float(np.sum(density) * da * db)
    if not np.isfinite(mass) or mass <= 0.0:
        raise RuntimeError(f"bad mass for c={csign}, X={X}, branch={branch}: {mass}")
    density = density / mass
    branch_frac = float(np.count_nonzero(support) / np.count_nonzero(W > 0.0))
    return dict(Araw=Araw, Braw=Braw, density=density, da=da, db=db,
                Sa=Sa, Sb=Sb, T=T, branch_frac=branch_frac,
                eps=eps, mass=mass)


def transform_ray(profile, Q: float, direction: str) -> np.ndarray:
    if direction == "a":
        coord = profile["Araw"]
    elif direction == "b":
        coord = profile["Braw"]
    elif direction == "diag":
        coord = profile["Araw"] + profile["Braw"]
    else:
        raise ValueError(direction)

    coords = coord.ravel()
    weights = (profile["density"] * profile["da"] * profile["db"]).ravel()
    out = np.empty(len(NU_GRID), dtype=float)
    for i in range(0, len(NU_GRID), 24):
        nus = NU_GRID[i:i + 24]
        phase = np.exp(-2j * math.pi * np.outer(nus, coords) / Q)
        out[i:i + 24] = np.abs(phase @ weights)
    return out


def envelope_gamma(nus: np.ndarray, amp: np.ndarray, n_bins: int = 8):
    """Fit log upper envelope = c - gamma log nu."""
    amp = np.asarray(amp, dtype=float)
    amp = amp / max(float(np.max(amp)), 1e-300)
    edges = np.geomspace(float(nus.min()), float(nus.max()), n_bins + 1)
    xs = []
    ys = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (nus >= lo) & (nus <= hi)
        if int(np.count_nonzero(m)) < 3:
            continue
        env = float(np.quantile(amp[m], 0.90))
        if env > 1e-16:
            xs.append(math.sqrt(lo * hi))
            ys.append(env)
    if len(xs) < 4:
        return float("nan"), float("nan")
    lx = np.log(np.asarray(xs, dtype=float))
    ly = np.log(np.asarray(ys, dtype=float))
    A = np.column_stack([np.ones_like(lx), lx])
    beta, *_ = np.linalg.lstsq(A, ly, rcond=None)
    pred = A @ beta
    ss_res = float(np.sum((ly - pred) ** 2))
    ss_tot = float(np.sum((ly - ly.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 1.0
    return float(-beta[1]), r2


def deep_dip_spacing(nus: np.ndarray, amp: np.ndarray):
    amp = np.asarray(amp, dtype=float)
    amp = amp / max(float(np.max(amp)), 1e-300)
    loc = np.where((amp[1:-1] < amp[:-2]) & (amp[1:-1] <= amp[2:]))[0] + 1
    if len(loc) < 3:
        return float("nan"), int(len(loc))
    cutoff = max(0.10, float(np.quantile(amp, 0.12)))
    dips = loc[amp[loc] <= cutoff]
    if len(dips) < 3:
        dips = loc
    gaps = np.diff(nus[dips])
    if len(gaps) == 0:
        return float("nan"), int(len(dips))
    med = float(np.median(gaps))
    good = gaps[(0.5 * med <= gaps) & (gaps <= 1.5 * med)]
    if len(good) >= 2:
        return float(np.mean(good)), int(len(dips))
    return med, int(len(dips))


def fit_linear(rows, feature_set: str):
    y = np.asarray([r["gamma"] for r in rows], dtype=float)
    cols = [np.ones(len(rows))]
    names = ["1"]

    lnq = np.asarray([math.log(r["Q"]) for r in rows], dtype=float)
    lnt = np.asarray([math.log(r["T"]) for r in rows], dtype=float)
    dir_b = np.asarray([1.0 if r["direction"] == "b" else 0.0 for r in rows])
    dir_diag = np.asarray([1.0 if r["direction"] == "diag" else 0.0 for r in rows])
    lnspan = np.asarray([math.log(r["span"]) for r in rows], dtype=float)
    lnpred = np.asarray([math.log(r["pred"]) for r in rows], dtype=float)
    real3 = np.asarray([1.0 if r["branch"] == "real3" else 0.0 for r in rows])
    csign = np.asarray([float(r["csign"]) for r in rows], dtype=float)

    cols.append(lnq)
    names.append("lnQ")
    cols.append(lnt)
    names.append("lnT")

    if feature_set in {"rank", "full"}:
        cols.append(dir_b)
        names.append("dir_b")
        cols.append(dir_diag)
        names.append("dir_diag")

    if feature_set in {"rank_slope", "full_slope"}:
        cols.append(dir_b)
        names.append("dir_b")
        cols.append(dir_diag)
        names.append("dir_diag")
        cols.append(dir_b * lnt)
        names.append("dir_b*lnT")
        cols.append(dir_diag * lnt)
        names.append("dir_diag*lnT")

    if feature_set in {"span", "full_span"}:
        cols = [np.ones(len(rows)), lnq, lnspan]
        names = ["1", "lnQ", "lnSpan"]

    if feature_set in {"clock", "full_clock"}:
        cols = [np.ones(len(rows)), lnpred]
        names = ["1", "ln(Q/span)"]

    if feature_set in {"gamma", "full"}:
        cols.append(real3)
        names.append("branch_real3")
        cols.append(csign)
        names.append("csign")

    if feature_set in {"full_slope", "full_span", "full_clock"}:
        cols.append(real3)
        names.append("branch_real3")
        cols.append(csign)
        names.append("csign")

    A = np.column_stack(cols)
    beta, *_ = np.linalg.lstsq(A, y, rcond=None)
    pred = A @ beta
    resid = y - pred
    ss_res = float(np.sum(resid * resid))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 1.0
    return dict(names=names, beta=beta, r2=r2,
                resid_std=float(np.std(resid)), pred=pred)


def ratio(x: float, y: float) -> float:
    return x / y if y != 0 else float("nan")


def main():
    t0 = time.time()
    lines = []

    def emit(s: str = ""):
        lines.append(s)
        print(s, flush=True)

    emit("=" * 78)
    emit("MB GL(3) WALL LIFT - Deng-Espinosa discriminant/gamma-branch test")
    emit("=" * 78)
    emit("Profile: compact theta window on c=+/-1, alpha=-1/2 residual factor.")
    emit("Homogeneity: a-span ~ T, b-span ~ T^2 with T=X/8; Q=n f^2.")
    emit(f"Reference GL(2) gamma-spread band: {GL2_GAMMA_SPREAD:.3f} +/- {GL2_GAMMA_RADIUS:.3f}")

    rows = []
    profiles = {}
    for csign in (-1, 1):
        for X in (8.0, 12.0, 16.0):
            for branch in ("real3", "mixed"):
                profiles[(csign, X, branch)] = build_profile(csign, X, branch)

    emit("\n[profile] Deng-Espinosa branch support fractions in the compact window:")
    emit(f"  {'c':>3} {'X':>5} {'branch':>8} {'frac':>9} {'eps':>10} {'S_a':>8} {'S_b':>8}")
    for (csign, X, branch), prof in sorted(profiles.items()):
        emit(f"  {csign:>3} {X:5.1f} {branch:>8} {prof['branch_frac']:9.3f} "
             f"{prof['eps']:10.3e} {prof['Sa']:8.3f} {prof['Sb']:8.3f}")

    emit("\n[measured] gamma decay exponents and clock spacings:")
    emit(f"  {'c':>3} {'br':>6} {'n':>2} {'f':>2} {'X':>4} {'dir':>5} "
         f"{'gamma':>8} {'R2':>6} {'dip':>8} {'pred':>8} {'dip/p':>7}")

    for csign in (-1, 1):
        for branch in ("real3", "mixed"):
            for n in (4, 8):
                for f in (1, 2):
                    for X in (8.0, 12.0, 16.0):
                        Q = float(n * f * f)
                        prof = profiles[(csign, X, branch)]
                        pred_by_dir = {
                            "a": Q / prof["Sa"],
                            "b": Q / prof["Sb"],
                            "diag": Q / (prof["Sa"] + prof["Sb"]),
                        }
                        for direction in ("a", "b", "diag"):
                            amp = transform_ray(prof, Q, direction)
                            gamma, r2 = envelope_gamma(NU_GRID, amp)
                            dip, ndips = deep_dip_spacing(NU_GRID, amp)
                            pred = pred_by_dir[direction]
                            row = dict(csign=csign, branch=branch, n=n, f=f, X=X,
                                       T=prof["T"], Q=Q, direction=direction,
                                       gamma=gamma, r2=r2, dip=dip, ndips=ndips,
                                       pred=pred, dip_ratio=ratio(dip, pred),
                                       span=(Q / pred),
                                       Sa=prof["Sa"], Sb=prof["Sb"])
                            rows.append(row)
                            emit(f"  {csign:>3} {branch[:6]:>6} {n:2d} {f:2d} {X:4.0f} "
                                 f"{direction:>5} {gamma:8.3f} {r2:6.3f} "
                                 f"{dip:8.3f} {pred:8.3f} {row['dip_ratio']:7.3f}")

    gamma_vals = np.asarray([r["gamma"] for r in rows], dtype=float)
    emit("\n[measured] spread accounting across GL(3) cells:")
    emit(f"  raw GL(3) gamma-spread std = {float(np.std(gamma_vals)):.3f}")
    for direction in ("a", "b", "diag"):
        arr = np.asarray([r["gamma"] for r in rows if r["direction"] == direction], dtype=float)
        emit(f"  direction {direction:>4}: mean {float(np.mean(arr)):.3f}, "
             f"std {float(np.std(arr)):.3f}, min {float(np.min(arr)):.3f}, "
             f"max {float(np.max(arr)):.3f}")
    for branch in ("real3", "mixed"):
        arr = np.asarray([r["gamma"] for r in rows if r["branch"] == branch], dtype=float)
        emit(f"  branch {branch:>5}: mean {float(np.mean(arr)):.3f}, "
             f"std {float(np.std(arr)):.3f}")

    fit_names = ("base", "rank", "rank_slope", "span", "clock",
                 "gamma", "full", "full_slope", "full_span", "full_clock")
    fits = {name: fit_linear(rows, name) for name in fit_names}
    emit("\n[measured] linear explanations of gamma-spread:")
    for name in fit_names:
        fit = fits[name]
        terms = ", ".join(f"{n}={b:+.3f}" for n, b in zip(fit["names"], fit["beta"]))
        emit(f"  {name:>5}: R^2={fit['r2']:.3f}, resid std={fit['resid_std']:.3f}; {terms}")

    rank_gain = max(fits["rank"]["r2"], fits["rank_slope"]["r2"],
                    fits["span"]["r2"], fits["clock"]["r2"]) - fits["base"]["r2"]
    gamma_gain = fits["gamma"]["r2"] - fits["base"]["r2"]
    full_gain = max(fits["full"]["r2"], fits["full_slope"]["r2"],
                    fits["full_span"]["r2"], fits["full_clock"]["r2"]) - fits["base"]["r2"]

    dip_rows = [r for r in rows if np.isfinite(r["dip_ratio"]) and 0.25 <= r["dip_ratio"] <= 4.0]
    dip_by_dir = {}
    for direction in ("a", "b", "diag"):
        arr = np.asarray([r["dip_ratio"] for r in dip_rows if r["direction"] == direction], dtype=float)
        dip_by_dir[direction] = (float(np.median(arr)) if len(arr) else float("nan"),
                                 float(np.std(arr)) if len(arr) else float("nan"),
                                 int(len(arr)))

    emit("\n[measured] clock-ratio medians from the full discriminant profiles:")
    for direction in ("a", "b", "diag"):
        med, sd, cnt = dip_by_dir[direction]
        emit(f"  {direction:>4}: median dip/pred {med:.3f}, std {sd:.3f}, count {cnt}")

    if rank_gain > gamma_gain + 0.10 and full_gain >= rank_gain:
        verdict = ("RANK-SHIFT: the GL(3) wall is explained primarily by the "
                   "two-coordinate homogeneity/readout; branch gamma data is secondary.")
    elif gamma_gain > rank_gain + 0.10 and full_gain >= gamma_gain:
        verdict = ("GAMMA-BRANCH SPLIT: the Pol>0 / Pol<0 archimedean branch carries "
                   "more of the spread than the coordinate rank readout.")
    elif full_gain > max(rank_gain, gamma_gain) + 0.10:
        verdict = ("COUPLED SPLIT: both rank readout and Pol-sign gamma branch are needed "
                   "for the GL(3) spread.")
    else:
        verdict = ("PERSISTENT CLOCK: neither branch nor rank features materially improve "
                   "the scalar model on this grid.")

    emit("\n[verdict]")
    emit("  " + verdict)
    emit(f"  R2 gains over base: rank {rank_gain:+.3f}, gamma {gamma_gain:+.3f}, "
         f"full {full_gain:+.3f}")
    emit(f"[budget] wall time {time.time() - t0:.1f}s")
    emit("=" * 78)

    with open(OUT, "w") as f:
        f.write("\n".join(lines) + "\n")
    with open(SUMMARY, "w") as f:
        f.write("MB GL(3) WALL LIFT SUMMARY\n\n")
        f.write(verdict + "\n")
        f.write(f"raw_std={float(np.std(gamma_vals)):.6f}\n")
        f.write(f"base_R2={fits['base']['r2']:.6f}, rank_R2={fits['rank']['r2']:.6f}, "
                f"rank_slope_R2={fits['rank_slope']['r2']:.6f}, "
                f"span_R2={fits['span']['r2']:.6f}, clock_R2={fits['clock']['r2']:.6f}, "
                f"gamma_R2={fits['gamma']['r2']:.6f}, full_R2={fits['full']['r2']:.6f}, "
                f"full_slope_R2={fits['full_slope']['r2']:.6f}, "
                f"full_span_R2={fits['full_span']['r2']:.6f}, "
                f"full_clock_R2={fits['full_clock']['r2']:.6f}\n")
        f.write(f"rank_gain={rank_gain:.6f}, gamma_gain={gamma_gain:.6f}, "
                f"full_gain={full_gain:.6f}\n")
        for direction in ("a", "b", "diag"):
            med, sd, cnt = dip_by_dir[direction]
            f.write(f"clock_{direction}_median={med:.6f}, sd={sd:.6f}, count={cnt}\n")
        f.write("Files: tmp/mb_gl3_wall_lift.py, tmp/mb_gl3_wall_lift_results.txt\n")


if __name__ == "__main__":
    main()
