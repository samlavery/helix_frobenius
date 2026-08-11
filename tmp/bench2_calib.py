#!/usr/bin/env python3
"""Calibration of the regulated contour evaluator against exact ground truth.

Level 1: Lambda(Delta) -- degree 2, gamma = GammaC(s+11/2), kernel
2u^{11/2}e^{-2pi u}, so the reflection-split weight is EXACTLY the upper
incomplete gamma:  Phi(s,a) = 2(2pi)^{-(s+11/2)} Gamma(s+11/2, 2pi a).
The reference evaluator is therefore exact to working precision, and the
contour evaluator's error is measured directly, over a grid of
(h, T0, q, N).  This pins the aliasing/window/rolloff budget before any
degree-10 run.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from adapter_sym_probe import tau_coeffs
from containment_bench2 import Precise

mp.mp.dps = 40

KM1H = mp.mpf(11) / 2  # (k-1)/2 for Delta


def lam_delta(N, tau):
    lam = [mp.mpf(0)] * (N + 1)
    for n in range(1, N + 1):
        lam[n] = mp.mpf(tau[n]) / mp.mpf(n) ** KM1H
    return lam


def lambda_delta_exact(s, lam, N):
    """Reflection-split with exact incomplete-gamma weights; eps(Delta)=+1."""
    tot = mp.mpc(0)
    for n in range(1, N + 1):
        if lam[n] == 0:
            continue
        a = 2 * mp.power(2 * mp.pi, -(s + KM1H)) * mp.gammainc(s + KM1H, 2 * mp.pi * n)
        b = 2 * mp.power(2 * mp.pi, -((1 - s) + KM1H)) * mp.gammainc((1 - s) + KM1H, 2 * mp.pi * n)
        tot += lam[n] * (mp.power(n, -s) * a + mp.power(n, -(1 - s)) * b)
    return tot


def main():
    N = 60  # degree-2 conductor scale ~ sqrt(6.5*7.5)/(2pi) ~ 1: 60 is lavish
    tau = tau_coeffs(N)
    lam = lam_delta(N, tau)
    heights = [mp.mpf("1.3"), mp.mpf("4.1558"), mp.mpf("8.1118")]
    refs = [lambda_delta_exact(mp.mpc(0.5, t), lam, N) for t in heights]
    for t, r in zip(heights, refs):
        print(f"# reference |Lambda_Delta(1/2+{float(t)}i)| = {float(abs(r)):.6e}")
    print("# contour-evaluator error vs (h, T0, q):")
    for q in (0.0, 0.3, 1.2):
        for h in (0.06, 0.03, 0.015):
            for T0 in (23.0, 40.0):
                if q == 0.0 and T0 < 40:
                    continue  # unregulated needs the wide window
                t0 = time.time()
                ev = Precise([KM1H, KM1H + 1], lam, N, mp.mpf(1), h=h, T0=T0, q=q)
                errs = []
                for t, r in zip(heights, refs):
                    v = ev.value(mp.mpc(0.5, t))
                    errs.append(abs(v - r) / abs(r))
                print(f"#   q={q:4.1f} h={h:5.3f} T0={T0:4.1f}: rel-err = "
                      + "  ".join(f"{float(e):.2e}" for e in errs)
                      + f"   ({time.time()-t0:.1f}s)")


if __name__ == '__main__':
    main()
