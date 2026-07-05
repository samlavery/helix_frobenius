"""RUNG 3 — degree-6 twist L(E=26b, Ad_g, s) with the EXACT bad-prime Euler factors (2,13,31),
derived from the ramification (LMFDB: E split-mult@2 a2=+1, nonsplit-mult@13 a13=-1, good@31
a31=-3; g=124.1.i.a ramified@2,31 unramified@13).

Exact twist local factors (Ad^0 inertia-invariant line has Frob=1 wherever rho_g|D_p is
reducible-with-unramified-line, i.e. at 2 and 31):
  L_2(s)  = (1 - 2^{-s})^{-1}                          [E's deg-1 factor;  A_{2^k}=1]
  L_13(s) = prod_i (1 + mu_i 13^{-s})^{-1}             [E@13 deg1 (x) Ad UNRAMIFIED deg3;
                                                        roots {a13(E)*mu_i}={-mu_i}]
  L_31(s) = (1 + 3*31^{-s} + 31*31^{-2s})^{-1}         [E's deg-2 factor; Ad trivial line]
Good primes p!∈{2,13,31}: full degree-6 (6 tensor roots), as before.

Reuses the verified deg-6 fiber (twist_helix.local_hk for good p) and the Gamma^3 double-sided
helix kernel (twist_helix_g3).  Only the 3 bad local factors change.

Run:  python3 twist_helix_fix.py
"""
import math

import numpy as np

from twist_helix import ap_E, ad_eigs, sieve_primes, local_hk, BAD_E
from twist_helix_g3 import tabulate_G3, jets_g3

A13E, A2E, A31E = -1, +1, -3          # LMFDB, isogeny-invariant


def newton_h(power_sums, kmax):
    """complete-homogeneous h_0..h_kmax from power sums P_1..P_kmax (P_0 unused)."""
    P = [0.0] + list(power_sums)
    h = [1.0]
    for k in range(1, kmax + 1):
        h.append(sum(P[i] * h[k - i] for i in range(1, k + 1)) / k)
    return h


def local_hk_fixed(p, kmax, mu13):
    """EXACT twist local A_{p^k} at the three bad primes; else the good deg-6 factor."""
    if p == 2:
        return [1.0] * (kmax + 1)                       # L_2 = (1-2^{-s})^{-1}
    if p == 13:
        roots = [-m for m in mu13]                      # {a13(E)*mu_i} = {-mu_i}
        Ps = [float(np.real(sum(r ** i for r in roots))) for i in range(1, kmax + 1)]
        return newton_h(Ps, kmax)
    if p == 31:
        s = [2.0, float(A31E)]                           # alpha^i+beta^i, x^2 - a31 x + 31
        for i in range(2, kmax + 1):
            s.append(A31E * s[i - 1] - 31 * s[i - 2])
        return newton_h(s[1:kmax + 1], kmax)
    return local_hk(p, kmax)                             # good prime: deg-6


def build_An_fixed(nmax, mu13):
    primes = sieve_primes(nmax)
    A = np.zeros(nmax + 1)
    A[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    hloc = {}
    for p in primes:
        kmax, pk = 0, int(p)
        while pk <= nmax:
            kmax += 1
            pk *= p
        hloc[int(p)] = local_hk_fixed(int(p), kmax, mu13)
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        pk = n // m
        A[n] = (A[m] * A[pk]) if m > 1 else hloc[p][k]
    return A


def main():
    print("DEGREE-6 TWIST L(E=26b,Ad_g,s) — EXACT bad Euler factors at 2,13,31 — helix clip scan")
    print("=" * 86)
    trad, mu13 = ad_eigs(13)
    cls = {3: "identity", 0: "order-3", -1: "order-2"}[trad]
    print(f"  Frob_13 A4 class (quartic mod 13): {cls}, tr_Ad(13)={trad}, mu_i={[complex(m) for m in mu13]}")
    print(f"  bad factors: L_2=(1-2^-s)^-1 [A_2^k=1]; L_13 roots={[-complex(m) for m in mu13]} "
          f"(={{-mu_i}}); L_31 = E deg-2 (a31={A31E})")
    # sanity: A_2=1, A_4=1, A_8=1 (E split mult @2); A_31 = a31(E) = -3
    At = build_An_fixed(64, mu13)
    print(f"  check  A_2={At[2]:.3f}(=1) A_4={At[4]:.3f}(=1) A_8={At[8]:.3f}(=1) "
          f"A_13={At[13]:.3f} A_31={At[31]:.3f}(=a31=-3) A_3={At[3]:.3f}(=a3(E)*trAd(3))")
    print()

    print("  tabulating G3 kernel + gate ...")
    uG, G = tabulate_G3()
    print("  [PASS] G3 Mellin gate")
    print()

    tw = np.linspace(-0.30, 0.30, 41)
    eps = +1
    print(f"{'sqrt(N)':>8} {'N_tw':>12} | c0 c1 c2 c3 c4                               "
          f"| |c0|/|c2| |c1|/|c2| live")
    best = None
    for sq in [800, 1200, 1800, 2700, 4000, 6000, 9000, 13000, 20000, 30000]:
        N_tw = sq * sq
        B = sq / (2 * math.pi) ** 3
        nmax = int(14 * B) + 80
        A = build_An_fixed(nmax, mu13)
        c, ray = jets_g3(A, N_tw, eps, tw, uG, G, theta=0.0)
        ac = [abs(c[k]) for k in range(5)]
        live = int(np.argmax(ac))
        r02 = ac[0] / ac[2] if ac[2] else float("inf")
        r12 = ac[1] / ac[2] if ac[2] else float("inf")
        tower = " ".join(f"{v:.2e}" for v in ac)
        print(f"{sq:>8} {N_tw:>12} | {tower} | {r02:>8.3f} {r12:>8.3f}  c{live}")
        if ac[2] > 1e-12 and (best is None or (ac[0] + ac[1]) / ac[2] < best[0]):
            best = ((ac[0] + ac[1]) / ac[2], sq, N_tw, c, live)
    print()
    if best:
        sc, sq, N_tw, c, live = best
        print(f"BEST FE-closure: sqrt(N)={sq}, N_tw={N_tw}, |c0|/|c2|={abs(c[0])/abs(c[2]):.4f}, "
              f"first live jet order {live} (want 2)")
        print(f"  jets: c0={abs(c[0]):.3e} c1={abs(c[1]):.3e} c2={abs(c[2]):.5f}(leading) "
              f"c3={abs(c[3]):.3e} c4={abs(c[4]):.3e}")
    print()
    print("With EXACT bad factors: does c0 now collapse and c2 survive at some sqrt(N)?  If yes, the")
    print("double-sided helix reads r(E,Ad_g)=2 on the twist.  If c0 still grows, the residual is the")
    print("joint (N_twist, eps) pin and/or the deg-6 normalization — report honestly.")


if __name__ == "__main__":
    main()
