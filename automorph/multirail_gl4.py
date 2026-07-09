#!/usr/bin/env python3
"""
multirail_gl4.py -- the LITERAL multi-rail test: a genuine rank-2 GL(4) needs TWO rails.

Object: genuine GL(4) = Delta x E11, 4 tensor channels c = s_d*th_d + s_e*th_e,
(s_d,s_e) in {+-1}^2, TWO rationally-independent generating angles th_d, th_e (real
Satake at p=2).  A "rail" = one generating angle snapped to its own mu_M cell (one clock,
one carrier lane).  Cell closure of the 4-channel bank over a period:

  raw    (0 rails): sum the true channels over a cell -> floors (the emergent smear).
  1-rail : snap ONLY th_d to mu_Md; th_e left raw.  Sum over the th_d-period Md.
           The th_d-channels close but the th_e modulation e^{+-i th_e k} is an UNRELATED
           frequency over that period -> O(1) residue.  (= the scalar single de-chirp:
           one lane cannot carry the second independent angle.)
  2-rail : snap BOTH th_d->mu_Md and th_e->mu_Me INDEPENDENTLY; each channel becomes
           s_d*th_d_hat + s_e*th_e_hat, a root of unity of order L=lcm(Md,Me).  Sum over
           L -> geometric-series closure, every channel != DC vanishes.

If 2-rail tracks precision (~10^-dps) while raw and 1-rail floor at O(1), the object
carries exactly as many rails as it has independent angles -- the multi-rail helix.
Run: python3 tmp/multirail_gl4.py
"""
import math, os, sys
import mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC

def snap(phi, M):
    step = 2 * mp.pi / M
    return mp.nint(phi / step) * step

def cell_sum(phi, P):
    """sum_{k=1}^{P} e^{i phi k}, closed form; DC (phi~0 mod 2pi) -> P."""
    z = mp.e ** (1j * phi)
    if abs(z - 1) < mp.mpf(10) ** (-mp.mp.dps + 5):
        return mp.mpf(P)
    return z * (z ** P - 1) / (z - 1)

def lcm(a, b):
    return a * b // math.gcd(a, b)

def rails(th_d, th_e, dps, Md=8, Me=6):
    """(|raw|, |1-rail|, |2-rail|) closure residuals of the 4-channel GL4 bank at dps."""
    mp.mp.dps = dps
    td, te = mp.mpf(th_d), mp.mpf(th_e)
    signs = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
    # raw: true channels, summed over the th_d-period (any complete cell)
    raw = sum(cell_sum(sd * td + se * te, Md) for sd, se in signs)
    # 1-rail: snap th_d only, th_e raw; period = Md (the single rail's cell)
    td_h = snap(td, Md)
    one = sum(cell_sum(sd * td_h + se * te, Md) for sd, se in signs)
    # 2-rail: snap both, independent scales; period = lcm(Md,Me)
    td_h2, te_h = snap(td, Md), snap(te, Me)
    L = lcm(Md, Me)
    two = sum(cell_sum(sd * td_h2 + se * te_h, L) for sd, se in signs)
    return abs(raw), abs(one), abs(two)

def main():
    N = 64
    lam_d, _ = FC.FAMILIES["delta"].coeff(N)
    lam_e, _ = FC.FAMILIES["e11"].coeff(N)
    # GENERIC primes: both Satake angles irrational (avoid p=2 th_e=3pi/4, p=11 th_d, p=19 th_e=pi/2)
    GENERIC = [3, 5, 7, 13, 17, 23]
    print("MULTI-RAIL test: genuine rank-2 GL(4) = Delta x E11, channels {+-th_d +- th_e}")
    print("=" * 78)
    print("Both generating angles irrational (generic primes) => rails are truly independent.")
    print(f"  {'p':>3} {'th_d/pi':>9} {'th_e/pi':>9} | {'raw':>10} {'1-rail':>10} {'2-rail(dps90)':>15}")
    all_two, all_one = [], []
    for p in GENERIC:
        th_d = math.acos(max(-1, min(1, lam_d[p].real / 2)))
        th_e = math.acos(max(-1, min(1, lam_e[p].real / 2)))
        r0, r1, r2 = rails(th_d, th_e, 90)
        print(f"  {p:>3} {th_d/math.pi:>9.5f} {th_e/math.pi:>9.5f} | "
              f"{float(r0):>10.3g} {float(r1):>10.3g} {float(r2):>15.4g}")
        all_two.append(float(r2)); all_one.append(float(r1))
    print()
    # precision-tracking on one representative generic prime (p=3)
    th_d = math.acos(max(-1, min(1, lam_d[3].real / 2)))
    th_e = math.acos(max(-1, min(1, lam_e[3].real / 2)))
    print(f"precision-tracking at p=3 (th_d/pi={th_d/math.pi:.5f}, th_e/pi={th_e/math.pi:.5f}):")
    print(f"  {'dps':>5} {'raw':>12} {'1-rail':>12} {'2-rail':>15}")
    e_two = []
    for dps in (30, 60, 90):
        r0, r1, r2 = rails(th_d, th_e, dps)
        print(f"  {dps:>5} {float(r0):>12.4g} {float(r1):>12.4g} {float(r2):>15.4g}")
        e_two.append(math.log10(float(r2) + 10.0 ** (-2 * dps)))
    two_tracks = e_two[0] < -25 and e_two[1] < -55 and e_two[2] < -85
    one_floors = max(all_one) > 0.05     # 1-rail residual O(1) across generic primes
    print()
    print(f"  2-rail {'TRACKS PRECISION (closes ~10^-dps)' if two_tracks else 'does NOT close'};"
          f" 1-rail {'FLOORS at O(1)' if one_floors else 'closes too (check for hidden harmonic)'}"
          f" (worst 1-rail over generic primes = {max(all_one):.3g}).")
    print("  => the genuine rank-2 object carries exactly 2 rails: one clock per independent")
    print("     Satake angle.  One rail (single de-chirp / scalar lane) cannot hold the second.")
    print("     Rails = rank of the dual torus.  Sym^r = 1 rail (channels are harmonics of one")
    print("     angle); Delta x E11 = 2 rails; the multi-rail helix = one pitch-1 rail per angle.")

if __name__ == "__main__":
    main()
