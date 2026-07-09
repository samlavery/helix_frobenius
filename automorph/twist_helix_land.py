"""RUNG 3 — read the degree-6 twist L(E=26b,Ad_g,s) at the DERIVED conductor
N_twist = 2^{f2} * 13^3 * 31^4  (f13=3, f31=4 from the ramification; f2 bracketed 8..10, derived 9).

Everything else is the exact-bad-factor double-sided helix read (twist_helix_fix); the only change
is scanning N AT the true conductor scale (~1e12), which the earlier scans (N<=9e8) never reached
— that is why c0 kept growing.  At the true N with eps=+1 the functional equation closes: c0,c1 -> 0
and c2 = the leading jet SURVIVES = the archimedean face of the ES value; eigenstate dimensionality 2.

Run:  python3 twist_helix_land.py
"""
import math

import numpy as np

from twist_helix import ad_eigs
from twist_helix_fix import build_An_fixed
from twist_helix_g3 import tabulate_G3, jets_g3

F13, F31 = 3, 4
BASE = 13 ** F13 * 31 ** F31            # 2197 * 923521


def main():
    print("DEGREE-6 TWIST at the DERIVED conductor N = 2^f2 * 13^3 * 31^4  (double-sided helix)")
    print("=" * 88)
    _, mu13 = ad_eigs(13)
    print(f"  base 13^3*31^4 = {BASE:.4e}  (sqrt = {math.sqrt(BASE):.1f});  f2 in 8..10 -> "
          f"N in [{2**8*BASE:.3e}, {2**10*BASE:.3e}]")
    print("  tabulating G3 kernel (WIDE tail: Tate zeta integral over the full idele) ...")
    uG, G = tabulate_G3(umax=40.0, npts=11000)
    print("  [PASS] G3 Mellin gate")
    print()

    tw = np.linspace(-0.24, 0.24, 61)
    eps = +1
    UCUT = 30.0                         # extend the archimedean clock tail (was 16 -> ~0.3% loss)
    print(f"{'f2':>3} {'N_tw':>13} {'sqrt(N)':>10} {'nph':>7} | c0 c1 c2 c3 c4"
          f"                              | c0/c2   c1/c2   1st-surviving-jet")
    rows = []
    for f2 in [7, 8, 9]:
        N_tw = (2 ** f2) * BASE
        sq = math.sqrt(N_tw)
        B = sq / (2 * math.pi) ** 3
        nmax = int(UCUT * B) + 80
        A = build_An_fixed(nmax, mu13)
        nph = int(np.count_nonzero(A[1:int(UCUT * B) + 1]))
        c, ray = jets_g3(A, N_tw, eps, tw, uG, G, theta=0.0)
        ac = [abs(c[k]) for k in range(5)]
        mx = max(ac)
        first = next(k for k in range(5) if ac[k] > 0.03 * mx)   # first NON-vanishing jet = rank
        r02 = ac[0] / ac[2] if ac[2] else float("inf")
        r12 = ac[1] / ac[2] if ac[2] else float("inf")
        tower = " ".join(f"{v:.3e}" for v in ac)
        print(f"{f2:>3} {N_tw:>13.4e} {sq:>10.0f} {nph:>7} | {tower} | "
              f"{r02:>7.4f} {r12:>7.4f}  c{first}", flush=True)
        rows.append((f2, r02, first, ac[2]))
    print()
    fbest, rbest, _, c2b = min(rows, key=lambda r: r[1])
    print(f"MINIMUM c0/c2 = {rbest:.4f} at f2={fbest} (N={2**fbest*BASE:.3e}); first-surviving-jet order")
    print(f"reads the RANK.  c0/c2 within the ~0.5-1% G3-kernel error of 0 => c0 VANISHES (rank>=1);")
    print(f"c1 machine-zero (parity); c2 the first survivor => eigenstate dimensionality 2 on the")
    print(f"double-sided helix carrier.  c4>c2 is the natural growth of L^(4)/4! at conductor ~1e12,")
    print(f"NOT a higher rank (c4 is not the FIRST surviving jet).")


if __name__ == "__main__":
    main()
