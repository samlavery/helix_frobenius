#!/usr/bin/env python3
"""
height_warp_test.py -- is Altug's emergent comb / Prop 5.2 difficulty SELF-INFLICTED by a
two-edged height cutoff, and does a calibrated one-sided carrier warp remove it?

Altug's J_{l,f}(xi,nu,X) = INT G(y/X) y Psi(y) e(-y nu/2lf^2) dy, with G_altug a COMPACT bump
on (0.25X, 1.25X): TWO edges.  The paper already names the emergent clock as "the interference
of the two edges of the fixed cutoff."  Hypothesis (owner): the comb -- and the o(X) uniformity
difficulty it forces -- is manufactured by truncating height at both ends.  The carrier's growth
window is ONE-sided (grows from 0 at the head, no top truncation), so it should have no two-edge
interference and no comb.

Test: compute |J(nu)| over the comb band for
  (G)  Altug's two-edged bump               -- expect a deep comb (dips ~1e-1..1e-3)
  (W)  one-sided calibrated carrier warp     -- same lower growth edge, NO sharp top: raised-cosine
       growth to 1, then a long smooth decay (scale >> growth) out to 6X.  Expect NO comb.
Report comb depth = min|J|/max|J| over the band (deep = strong comb; ~1 = no comb) and the
peak-to-trough contrast, for a sweep of top-edge width (sharp bump -> diffuse warp).

Live output: tmp/height_warp_results.txt
Run: python3 tmp/height_warp_test.py
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import be_prop52_certify as BP

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "height_warp_results.txt")


def raised_cos_grow(u, a, w):
    """0 below a, raised-cosine growth to 1 over [a, a+w]."""
    z = (u - a) / w
    return np.where(z <= 0, 0.0, np.where(z >= 1, 1.0, 0.5 - 0.5 * np.cos(math.pi * z)))


def window_two_edge(u):
    """Altug's compact bump on (0.25,1.25): two edges."""
    return BP.G_altug(u)


def window_one_sided(u, top_scale):
    """Calibrated carrier warp: grows from 0.25 (raised cosine, width 0.5 to reach 1 at 0.75),
    then decays smoothly exp(-(u-0.75)/top_scale).  top_scale large => diffuse top => one edge."""
    grow = raised_cos_grow(u, 0.25, 0.5)
    decay = np.where(u > 0.75, np.exp(-(u - 0.75) / top_scale), 1.0)
    return grow * decay


def J_of(nu, window_vals, ys, yPsi, lf2):
    phase = np.exp(-2j * math.pi * np.outer(nu, ys) / (2.0 * lf2))
    integ = window_vals * ys * yPsi
    return np.abs(phase @ integ) * (ys[1] - ys[0])


def comb_depth(nus, Jabs):
    return float(np.min(Jabs) / np.max(Jabs)) if np.max(Jabs) > 0 else float("nan")


def main():
    f = open(OUT, "w")

    def emit(s=""):
        print(s, flush=True)
        f.write(s + "\n")
        f.flush()

    l, ff, X, xi = 1, 1, 16.0, 1
    lf2 = l * ff * ff
    # y-range wide enough for the one-sided tail
    ys = np.linspace(0.1 * X, 6.0 * X, 3000)
    u = ys / X
    Psi = np.array([BP.Psi(float(y), xi, l, ff) for y in ys], dtype=complex)
    yPsi = Psi                                   # J integrand carries an extra y; fold below
    # comb band: Delta_nu ~ 4 lf^2/(0.94 X); scan a few periods
    dnu = 4.0 * lf2 / (0.94 * X)
    nus = np.linspace(0.3 * dnu, 8.0 * dnu, 800)

    emit("Height-truncation vs calibrated carrier warp: does the emergent comb dissolve?")
    emit(f"l={l} f={ff} X={X} xi={xi}; comb spacing Delta_nu~{dnu:.3f}; band [{nus[0]:.2f},{nus[-1]:.2f}]")
    emit("=" * 74)
    emit(f"{'window':>34} {'comb depth min/max':>20} {'contrast (max-min)/max':>24}")

    # (G) two-edged Altug bump
    wG = window_two_edge(u)
    JG = J_of(nus, wG, ys, yPsi, lf2)
    dG = comb_depth(nus, JG)
    emit(f"{'(G) Altug two-edged bump':>34} {dG:>20.3e} {1-dG:>24.3f}")

    # (W) one-sided carrier warp, sweep top_scale from sharp -> diffuse
    for ts in (0.15, 0.3, 0.6, 1.2, 2.5, 5.0):
        wW = window_one_sided(u, ts)
        JW = J_of(nus, wW, ys, yPsi, lf2)
        dW = comb_depth(nus, JW)
        tag = "sharp top~bump" if ts <= 0.15 else ("diffuse (carrier-like)" if ts >= 2.5 else "")
        emit(f"{'(W) one-sided warp top_scale='+format(ts,'.2f'):>34} {dW:>20.3e} {1-dW:>24.3f}  {tag}")

    # ISOLATION: fully smooth NO-EDGE windows -- if the comb dies here it is edge-induced
    # (calibrated warp can fix it); if it persists it is intrinsic to Psi (hypothesis wrong).
    emit("")
    emit("  -- isolation: fully smooth windows (no lower cutoff / no edges) --")
    wGauss = np.exp(-((u - 1.5) / 0.7) ** 2)                       # broad Gaussian, no edges
    JGa = J_of(nus, wGauss, ys, yPsi, lf2)
    emit(f"{'(S) broad Gaussian (no edges)':>34} {comb_depth(nus,JGa):>20.3e} {1-comb_depth(nus,JGa):>24.3f}")
    wFrom0 = raised_cos_grow(u, 0.0, 1.5) * np.exp(-np.maximum(u - 1.5, 0) / 3.0)  # grow from y=0
    JF0 = J_of(nus, wFrom0, ys, yPsi, lf2)
    emit(f"{'(S) grow-from-0, long tail':>34} {comb_depth(nus,JF0):>20.3e} {1-comb_depth(nus,JF0):>24.3f}")
    # also: is the comb in Psi itself?  |Psi(y)| oscillation over the band
    emit("")
    emit(f"  |Psi(y)| relative oscillation over y-band (is the comb already IN the integrand?): "
         f"{(np.max(np.abs(Psi))-np.min(np.abs(Psi)))/np.max(np.abs(Psi)):.3f}")
    emit("")
    emit("[read] comb dies with smooth no-edge window => EDGE-induced (calibrated warp fixes it).")
    emit("[read] comb persists => intrinsic to Psi (the orbital transform), not the truncation.")
    f.close()


if __name__ == "__main__":
    main()
