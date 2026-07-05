"""RUNG 3 — the ES value as the LEADING JET of the degree-6 twist L(E, Ad_g, s), read on the
DOUBLE-SIDED HELIX CARRIER (Sam's steer 2026-07-04: "you're working over CURVES not infinite
helix; use the clip + alternate/criss-cross fiber routing the clip-weld agent identified; the
fiber rides ONE carrier").

The p-adic overconvergent iterated integral (rung3_lhs) is the 1D SHADOW; the genuine article is
the leading jet of L(E,Ad_g,s) at the center, read via the clipped double-ended kernel (helix
strand + eps*antihelix strand), exactly as jet_census/bsd_rank_ladder read L^(r)(E,1)/r! for a
plain curve.  r(E,Ad_g)=2 (proven, rung3_dimension_lift) so the eigenstate dimensionality is 2:
c_0=L(center) and c_1 must VANISH, c_2 = the leading jet = the ES regulator value SURVIVES.

CARRIER (one carrier for all): the pitch-1 archimedean helix, single-Gamma kernel
  Lambda(s) = sum_n A_n [ r_n^s Gamma(s,x_n) + eps r_n^{2-s} Gamma(2-s,x_n) ],
  x_n = 2 pi n / sqrt(N_tw),  r_n = sqrt(N_tw)/(2 pi n),  eps=+1 (rank 2 even; ES Hyp A).
FIBER (degree 6): A_p = a_p(E)*tr_Ad(p); full local factor by complete-homogeneous h_k of the 6
tensor roots {alpha,beta}(E) (x) {mu1,mu2,mu3}(Ad_g).  E by point count (26b); Ad_g class by the
quartic w^4+7w^2-2w+14 mod p root count (4->id tr3, 1->ord3 tr0, 0->ord2 tr-1) [verified reader].
CLIP: sqrt(N_tw) SCANNED for functional-equation closure (c_0 -> 0 with c_2 surviving) — the
clip-weld agent PROVED n_eff = 0.733*sqrt(N), so sqrt(N_tw) is the one free knob; scan it.

TIER: MEASURED (archimedean carrier reading).  The leading jet is the ARCHIMEDEAN twisted-L
value L''(E,Ad_g,center)/2! (a regulator), NOT the p-adic iterated integral — the two are the
BSD/ES two faces (archimedean vs p-adic regulator).  This reads the EIGENSTATE DIMENSIONALITY
(rank 2) on the carrier and its archimedean leading value; it does not claim the p-adic ES match.

Run:  python3 twist_helix.py
"""
import cmath
import math

import numpy as np


# ----------------------------------------------------------- E point count (26b)
AINV_E = (1, -1, 1, -3, 3)          # 26b, conductor 26 = 2*13
COND_E = 26
BAD_E = {2, 13}


def ap_E(p):
    """a_p(E) = p - #affine points of the full Weierstrass model over F_p (good & mult bad)."""
    a1, a2, a3, a4, a6 = AINV_E
    if p == 2:
        naff = sum(1 for x in range(2) for y in range(2)
                   if (y * y + a1 * x * y + a3 * y - (x ** 3 + a2 * x * x + a4 * x + a6)) % 2 == 0)
        return 2 - naff
    x = np.arange(p, dtype=np.int64)
    B = (a1 * x + a3) % p
    f = (x ** 3 + a2 * x * x + a4 * x + a6) % p
    D = (B * B + 4 * f) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(D == 0, 0, np.where(isq[D], 1, -1))
    return int(-chi.sum())


# ------------------------------------------------- Ad_g class via the quartic mod p
QUARTIC = [14, -2, 7, 0, 1]         # 14 - 2w + 7w^2 + w^4  =  w^4+7w^2-2w+14  (M_2652)


def ad_eigs(p):
    """(tr_Ad, [mu1,mu2,mu3]) from #roots of the quartic mod p.  A4 Frobenius: 4 roots=identity
    (tr 3, {1,1,1}); 1 root=order-3 (tr 0, {1,zeta3,zeta3^2}); 0 roots=order-2 (tr -1,{1,-1,-1})."""
    w = np.arange(p, dtype=np.int64)
    val = (QUARTIC[0] + QUARTIC[1] * w + QUARTIC[2] * (w * w) % p + QUARTIC[4] * (w ** 4)) % p
    nroots = int(np.count_nonzero(val % p == 0))
    z3 = cmath.exp(2j * math.pi / 3)
    if nroots >= 4:
        return 3, [1.0, 1.0, 1.0]
    if nroots == 1:
        return 0, [1.0, z3, z3.conjugate()]
    return -1, [1.0, -1.0, -1.0]    # 0 roots


# --------------------------------------------- degree-6 twist coefficients A_n
def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def local_hk(p, kmax):
    """complete-homogeneous h_0..h_kmax of the 6 tensor roots at p = the local Euler coeffs
    A_{p^k}.  Newton: k*h_k = sum_{i=1..k} P_i h_{k-i}, P_i = s_i(E)*t_i(Ad) power sums."""
    aE = ap_E(p)
    trad, mus = ad_eigs(p)
    # E power sums s_i = alpha^i+beta^i (Newton on x^2 - aE x + p); degree drops to 1 at mult bad
    s = [2.0]
    if p in BAD_E:                      # multiplicative: single root a_p=+-1, s_i = aE^i
        for i in range(1, kmax + 1):
            s.append(float(aE) ** i)
    else:
        s.append(float(aE))
        for i in range(2, kmax + 1):
            s.append(aE * s[i - 1] - p * s[i - 2])
    # Ad power sums t_i = mu1^i+mu2^i+mu3^i (exact by class)
    def t_i(i):
        if trad == 3:
            return 3.0
        if trad == 0:
            return 3.0 if i % 3 == 0 else 0.0
        return 3.0 if i % 2 == 0 else -1.0   # order-2 {1,-1,-1}
    P = [0.0] + [s[i] * t_i(i) for i in range(1, kmax + 1)]
    h = [1.0]
    for k in range(1, kmax + 1):
        h.append(sum(P[i] * h[k - i] for i in range(1, k + 1)) / k)
    return h


def build_An(nmax):
    """multiplicative degree-6 twist coefficients A_1..A_nmax (real; self-dual)."""
    primes = sieve_primes(nmax)
    A = np.zeros(nmax + 1)
    A[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    # per-prime local h_k up to the max power that fits
    hloc = {}
    for p in primes:
        kmax = 0
        pk = p
        while pk <= nmax:
            kmax += 1
            pk *= p
        hloc[int(p)] = local_hk(int(p), kmax)
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        pk = n // m
        A[n] = (A[m] * A[pk]) if m > 1 else hloc[p][k]
    return A


# --------------------------------------------- double-ended single-Gamma kernel
def jet_tower(A, N_tw, eps, tw, dps=18, xcut=40):
    """c_0..c_7 of Lambda(1+it) via the double-ended incomplete-Gamma kernel (one carrier)."""
    import mpmath as mp
    mp.mp.dps = dps
    sq = math.sqrt(N_tw)
    vals = []
    for t in tw:
        s = mp.mpf(1) + 1j * mp.mpf(float(t))
        tot = mp.mpc(0)
        for n in range(1, len(A)):
            if A[n] == 0.0:
                continue
            x = 2 * math.pi * n / sq
            if x > xcut:
                break
            r = sq / (2 * math.pi * n)
            tot += A[n] * (r ** s * mp.gammainc(s, x, mp.inf)
                           + eps * r ** (2 - s) * mp.gammainc(2 - s, x, mp.inf))
        vals.append(complex(tot))
    Z = np.array(vals).real                    # eps=+1 => even in t, already real-rotated (ray 0)
    V = np.vander(tw, 8, increasing=True)
    return np.linalg.lstsq(V, Z, rcond=None)[0]


def main():
    print("DEGREE-6 TWIST L(E=26b, Ad_g, s) on the DOUBLE-SIDED HELIX CARRIER — sqrt(N) clip scan")
    print("=" * 82)
    # verify the class reader against a_p(E) sanity + Ad density
    ncheck = [p for p in sieve_primes(200) if p not in (2, 13, 31)]
    dens = {3: 0, 0: 0, -1: 0}
    for p in ncheck:
        dens[ad_eigs(p)[0]] += 1
    tot = len(ncheck)
    print(f"  Ad class densities (primes<200): id(tr3)={dens[3]/tot:.3f} (exp .083), "
          f"ord3(tr0)={dens[0]/tot:.3f} (exp .333), ord2(tr-1)={dens[-1]/tot:.3f} (exp .5)")
    print(f"  a_2(E)={ap_E(2)}, a_3(E)={ap_E(3)}, a_5(E)={ap_E(5)}, a_7(E)={ap_E(7)}  (26b)")
    print()

    tw = np.linspace(-0.35, 0.35, 41)
    eps = +1                                   # rank 2 even; ES Hypothesis A (all local w=+1)
    # sqrt(N) clip scan: n_eff ~ 0.73 sqrt(N); scan sqrt(N) in [15, 900] (N in [~2e2, ~8e5])
    print(f"{'sqrt(N)':>8} {'N_tw':>10} {'nph':>5} | jet tower |c0| |c1| |c2| |c3| |c4|"
          f"          | |c0|/|c2| |c1|/|c2| live")
    best = None
    for sq in [15, 20, 26, 35, 46, 60, 80, 105, 140, 185, 245, 320, 420, 560, 740, 900]:
        N_tw = sq * sq
        nmax = int(1.7 * sq) + 40
        A = build_An(nmax)
        nph = int(np.count_nonzero(A[1:int(0.735 * sq) + 1]))
        c = jet_tower(A, N_tw, eps, tw)
        ac = [abs(c[k]) for k in range(5)]
        live = int(np.argmax(ac))
        r02 = ac[0] / ac[2] if ac[2] else float("inf")
        r12 = ac[1] / ac[2] if ac[2] else float("inf")
        tower = " ".join(f"{v:.2e}" for v in ac)
        print(f"{sq:>8} {N_tw:>10} {nph:>5} | {tower} | {r02:>8.3f} {r12:>8.3f}  c{live}")
        score = ac[0] + ac[1]                  # want BOTH sub-rank jets small vs c2
        if ac[2] > 1e-9 and (best is None or (score / ac[2]) < best[0]):
            best = (score / ac[2], sq, N_tw, c)
    print()
    if best:
        _, sq, N_tw, c = best
        print(f"BEST FE-closure: sqrt(N)={sq}, N_tw={N_tw} — |c0|+|c1| minimized relative to c2")
        print(f"  jets: c0={abs(c[0]):.3e}  c1={abs(c[1]):.3e}  c2={abs(c[2]):.4f} (leading)  "
              f"c3={abs(c[3]):.3e}  c4={abs(c[4]):.3e}")
        print(f"  eigenstate dimensionality read = order of first surviving jet = "
              f"{int(np.argmax([abs(c[k]) for k in range(5)]))}  (want 2 = r(E,Ad_g))")
    print()
    print("Reading: if c0,c1 -> 0 and c2 survives at some sqrt(N), the double-sided helix carrier")
    print("reads r(E,Ad_g)=2 on the twist (single-Gamma 'one carrier').  If c0 never dips, the")
    print("degree-6 GAMMA (Gamma(s)^3 Meijer) or the criss-cross routing is needed — report which.")


if __name__ == "__main__":
    main()
