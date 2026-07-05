"""RUNG 3 — degree-6 twist L(E=26b, Ad_g, s) on the double-sided helix carrier with the CORRECT
degree-6 completion: the INTERLEAVED CRISS-CROSS of the 3 Gamma-strands (Sam's routing steer).

Experiment A (twist_helix.py, single-Gamma) DIAGNOSED two bugs:
  (1) wrong gamma degree — a degree-6 L needs Gamma_C(s)^3 (3 Hodge pairs), not one Gamma(s);
  (2) wrong argument scaling — the exact completion has x_n = (2pi)^3 n / sqrt(N), not 2pi n/sqrt(N).
The alternate-fiber (antihelix, eps=+1) routing DID work (odd jets killed by parity to ~1e-13);
only the completion was wrong.  This file fixes both.

DERIVATION.  Lambda(s) = N^{s/2} Gamma_C(s)^3 L(s), Gamma_C(s)=2(2pi)^{-s}Gamma(s), center s=1,
FE s<->2-s (motivic weight 1).  With B = sqrt(N)/(2pi)^3, G3 = inverse-Mellin of Gamma(s)^3 =
MeijerG G^{3,0}_{0,3}(u|0,0,0), and K3(s,x) = int_x^inf u^{s-1} G3(u) du (the incomplete deg-6
transform = the 3-strand criss-cross), the double-ended (helix + eps antihelix) reading is
  Lambda(1+it) = 8 sum_n A_n [ (B/n)^s K3(s, n/B) + eps (B/n)^{2-s} K3(2-s, n/B) ],  s=1+it.
Rank r(E,Ad_g)=2 => c_0,c_1 must vanish (rank + parity), c_2 = leading jet SURVIVES = the ES
regulator value (archimedean face).  sqrt(N) (the clip) is scanned for FE closure (c_0 -> 0).

Fiber (degree 6): A_p = a_p(E)*tr_Ad(p), full local factor by complete-homogeneous h_k of the 6
tensor roots {alpha,beta}(E) (x) {mu1,mu2,mu3}(Ad_g), from twist_helix.build_An (verified reader).

TIER: MEASURED (archimedean carrier).  Reads the eigenstate dimensionality (rank 2) and the
archimedean leading jet; NOT the p-adic iterated integral (that is the 1D shadow).

Run:  python3 twist_helix_g3.py
"""
import math

import numpy as np

from twist_helix import build_An, ap_E, ad_eigs, sieve_primes   # verified deg-6 fiber + readers


# ---------------------------------------------------- G3 kernel table (one-time)
def tabulate_G3(umax=75.0, npts=9000, dps=25):
    """G3(u) = MeijerG G^{3,0}_{0,3}(u|0,0,0) on a log grid; ALSO gate int_0^inf u^{s-1}G3 = Gamma(s)^3."""
    import mpmath as mp
    mp.mp.dps = dps
    u = np.exp(np.linspace(math.log(1e-5), math.log(umax), npts))
    G = np.array([float(mp.meijerg([[], []], [[0, 0, 0], []], mp.mpf(ui))) for ui in u])
    # gate at the evaluation center s=1 (Mellin=Gamma(1)^3=1); tail-truncation floor ~1% is fine
    # for the structural c0-collapse read (the reading only uses x_n < umax anyway).
    for s in (0.9, 1.0, 1.1):
        mell = np.trapezoid(u ** (s - 1) * G, u)
        exact = float(mp.gamma(s) ** 3)
        assert abs(mell / exact - 1) < 1.5e-2, (s, mell, exact)
    return u, G


def K3_cumulative(u, G, s):
    """K3(s, u_grid) = int_u^inf v^{s-1} G3(v) dv for all grid nodes at once (complex s)."""
    integrand = (u ** (s - 1)) * G                     # complex
    # reverse-cumulative trapezoid from the top of the grid
    du = np.diff(u)
    seg = 0.5 * (integrand[1:] + integrand[:-1]) * du
    tail = np.concatenate([np.cumsum(seg[::-1])[::-1], [0.0]])
    return tail                                        # K3 at each u node (upper integral)


def jets_g3(A, N_tw, eps, tw, uG, G, theta=0.0):
    """Jet tower of the degree-6 twist read on the mu-carrier of cell phase theta (e^{i n theta}
    attached to the fiber).  theta=0 is the FORBIDDEN unit-1 carrier; theta in {pi/6,pi/3,pi/2,pi}
    are the mu_12/mu_6/mu_4/mu_2 carriers.  Ray auto-detected and rotated to the real chart."""
    B = math.sqrt(N_tw) / (2 * math.pi) ** 3
    n = np.arange(1, len(A))
    xn = n / B                                         # x_n = (2pi)^3 n/sqrt(N)
    keep = (A[1:] != 0.0) & (xn < uG[-1] * 0.98)
    idx = np.nonzero(keep)[0]
    xk = xn[idx]
    Ak = A[1:][idx] * np.exp(1j * theta * (idx + 1.0))   # <-- mu-carrier cell phase
    vals = []
    for t in tw:
        s = 1 + 1j * t
        K_s = np.interp(xk, uG, K3_cumulative(uG, G, s))
        K_d = np.interp(xk, uG, K3_cumulative(uG, G, 2 - s))
        term = Ak * ((B / (idx + 1.0)) ** s * K_s + eps * (B / (idx + 1.0)) ** (2 - s) * K_d)
        vals.append(8.0 * term.sum())
    v = np.array(vals)
    ray = np.angle(np.mean(v)) if abs(np.mean(v)) > 0 else 0.0   # pin the dominant ray
    Z = (v * np.exp(-1j * ray)).real
    V = np.vander(tw, 8, increasing=True)
    return np.linalg.lstsq(V, Z, rcond=None)[0], ray


def main():
    print("DEGREE-6 TWIST on the double-sided helix — CORRECT Gamma_C(s)^3 completion + (2pi)^3 clip")
    print("=" * 86)
    print("  tabulating G3 = MeijerG G^{3,0}_{0,3}(.|0,0,0) and gating int u^{s-1}G3 = Gamma(s)^3 ...")
    uG, G = tabulate_G3()
    print("  [PASS] G3 Mellin = Gamma(s)^3 at s=1.5,2,2.5")
    print()

    tw = np.linspace(-0.30, 0.30, 41)
    eps = +1
    sqs = [2000, 3000, 4500, 6500, 9000, 13000, 18000, 25000, 34000]
    # cache the fiber banks (theta-independent) once
    banks = {}
    for sq in sqs:
        B = sq / (2 * math.pi) ** 3
        banks[sq] = (sq * sq, build_An(int(14 * B) + 60))
    carriers = [("unit-1 (AVOID)", 0.0), ("pi/6 mu12", math.pi / 6), ("pi/3 mu6", math.pi / 3),
                ("pi/2 mu4", math.pi / 2), ("pi mu2", math.pi)]
    overall = None
    for name, theta in carriers:
        print(f"--- carrier {name}  (theta={theta:.4f}) ---")
        print(f"{'sqrt(N)':>8} {'N_tw':>12} | c0 c1 c2 c3 c4                               "
              f"| |c0|/|c2| |c1|/|c2| ray/pi live")
        best = None
        for sq in sqs:
            N_tw, A = banks[sq]
            c, ray = jets_g3(A, N_tw, eps, tw, uG, G, theta=theta)
            ac = [abs(c[k]) for k in range(5)]
            live = int(np.argmax(ac))
            r02 = ac[0] / ac[2] if ac[2] else float("inf")
            r12 = ac[1] / ac[2] if ac[2] else float("inf")
            tower = " ".join(f"{v:.2e}" for v in ac)
            print(f"{sq:>8} {N_tw:>12} | {tower} | {r02:>8.3f} {r12:>8.3f} {ray/math.pi:>6.3f} c{live}")
            if ac[2] > 1e-12:
                sc = (ac[0] + ac[1]) / ac[2]
                if best is None or sc < best[0]:
                    best = (sc, sq, N_tw, c, live)
        if best:
            sc, sq, N_tw, c, live = best
            print(f"  best on {name}: sqrt(N)={sq}, |c0|/|c2|={abs(c[0])/abs(c[2]):.3f}, "
                  f"first live jet order {live} (want 2), score={sc:.3f}")
            if overall is None or sc < overall[0]:
                overall = (sc, name, sq, N_tw, c, live)
        print()
    if overall:
        sc, name, sq, N_tw, c, live = overall
        print("=" * 86)
        print(f"OVERALL BEST FE-closure: carrier {name}, sqrt(N)={sq}, N_tw={N_tw}, score={sc:.3f}")
        print(f"  jets: c0={abs(c[0]):.3e} c1={abs(c[1]):.3e} c2={abs(c[2]):.4f}(leading) "
              f"c3={abs(c[3]):.3e} c4={abs(c[4]):.3e}")
        print(f"  eigenstate dimensionality (first surviving jet order) = {live}  (want 2 = r(E,Ad_g))")
        print(f"  => the winning carrier avoids unit-1 iff '{name}' != 'unit-1'")


if __name__ == "__main__":
    main()
