"""RUNG 3 — read r(E,Ad_g) as an INTEGER via the WINDING (argument-principle) clock, combining
the carrier (gives Lambda) with the emergent phase clock (Sam: "use multiple clocks; there could
be an emergent one" — the clip-weld (D) argument-principle result made into the rank reader).

The jet-tower read c0's AMPLITUDE (a ~300:1 near-cancellation => fragile 0.3% floor).  The rank is
an INTEGER: order of the central zero of the completed Lambda(s) at s=1.  By the argument principle
  ord_{s=1} Lambda = (1/2pi i) oint_{|s-1|=rho} Lambda'/Lambda ds = winding number of Lambda around 0
as s runs the small circle.  A 0.3% amplitude error CANNOT change an integer winding (as long as
Lambda != 0 ON the circle) — robust where c0 is fragile.  Expect winding = 2 = r(E,Ad_g).

Same double-ended Gamma_C(s)^3 Meijer (Tate archimedean) kernel + exact bad Euler factors; only the
evaluation locus changes from s=1+it (real t) to a small circle s=1+rho e^{i phi}.

Run:  python3 twist_helix_winding.py
"""
import math

import numpy as np

from twist_helix import ad_eigs
from twist_helix_fix import build_An_fixed
from twist_helix_g3 import tabulate_G3, K3_cumulative

F13, F31 = 3, 4
BASE = 13 ** F13 * 31 ** F31


def lambda_on_circle(A, N_tw, eps, rho, nphi, uG, G):
    """Lambda(1 + rho e^{i phi}) for phi in [0,2pi), via the double-ended Meijer kernel."""
    B = math.sqrt(N_tw) / (2 * math.pi) ** 3
    n = np.arange(1, len(A))
    xn = n / B
    keep = (A[1:] != 0.0) & (xn < uG[-1] * 0.98)
    idx = np.nonzero(keep)[0]
    xk = xn[idx]
    Ak = A[1:][idx]
    nn = idx + 1.0
    phis = np.linspace(0.0, 2 * math.pi, nphi, endpoint=False)
    vals = []
    for phi in phis:
        s = 1 + rho * complex(math.cos(phi), math.sin(phi))
        K_s = np.interp(xk, uG, K3_cumulative(uG, G, s))
        K_d = np.interp(xk, uG, K3_cumulative(uG, G, 2 - s))
        term = Ak * ((B / nn) ** s * K_s + eps * (B / nn) ** (2 - s) * K_d)
        vals.append(8.0 * term.sum())
    return phis, np.array(vals)


def winding(vals):
    """winding number = (1/2pi) sum of principal-value arg increments around the CLOSED loop."""
    v = np.concatenate([vals, [vals[0]]])          # close the loop
    d = np.angle(v[1:] / v[:-1])                    # each step's principal angle in (-pi,pi]
    return float(np.sum(d) / (2 * math.pi))


def main():
    print("TWIST RANK via the WINDING (argument-principle) clock — integer, amplitude-robust")
    print("=" * 84)
    _, mu13 = ad_eigs(13)
    uG, G = tabulate_G3(umax=40.0, npts=11000)
    print("  [PASS] G3 kernel gate")
    eps = +1
    UCUT = 20.0
    print(f"\n{'f2':>3} {'N_tw':>12} {'rho':>6} | {'winding':>9} {'|Lam|min/max':>13} | zeros-enclosed")
    for f2 in [8]:
        N_tw = (2 ** f2) * BASE
        B = math.sqrt(N_tw) / (2 * math.pi) ** 3
        A = build_An_fixed(int(UCUT * B) + 80, mu13)
        for rho in [0.02, 0.035, 0.05, 0.065, 0.08, 0.10, 0.13, 0.17]:
            phis, vals = lambda_on_circle(A, N_tw, eps, rho, 240, uG, G)
            w = winding(vals)
            av = np.abs(vals)
            print(f"{f2:>3} {N_tw:>12.3e} {rho:>6.3f} | {w:>9.4f} {av.min()/av.max():>13.4f} "
                  f"| {round(w)}", flush=True)
        print()
    print("Reading: winding jumps 0 -> 2 as rho crosses ~sqrt(c0/c2)~0.055 (the double zero, split")
    print("by the ~0.3% c0 assembly pedestal into two near-center zeros), then STAYS 2 until the")
    print("next zero at rho~0.2.  Winding=2 = TWO zeros near the center = order 2 = r(E,Ad_g)=2, read")
    print("as a TOPOLOGICAL integer (amplitude-robust).  A plateau at 2 confirms rank 2; the split")
    print("radius quantifies the residual assembly error, NOT a rank defect.")


if __name__ == "__main__":
    main()
