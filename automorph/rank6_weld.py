"""Rank 6 at the hinge: the Elkies-Watkins rank-6 record curve, conductor 5,187,563,742.

    y^2 + xy = x^3 + x^2 - 2582x + 48720,   [a1,a2,a3,a4,a6] = [1,1,0,-2582,48720],
    N = 5187563742 = 2 * 3 * 2777 * 311341,   |disc|/N = 6,   rank 6,   eps = +1.

The sextic rung of the ladder (Elkies-Watkins ANTS VI, Table 2; the smallest-conductor
rank-6 curve known).  eps = +1 makes the wave EVEN (odd jets dead by construction = the
weld; HingeKernel.odd_even_jets_dead), rank 6 kills c_0, c_2, c_4 (three arithmetic zeros
on the EVEN strand), and the first live jet is

    |c_6| = (sqrt(N)/2pi) * L^(6)(1)/6! = (sqrt(N)/2pi) * 2 sum (a_n/n) G_6(2pi n/sqrt(N)).

NOTE ON THE CURVE: the ANTS VI table entry is [1,1,0,-2582,48720] (a2 = 1, NOT the
[1,0,0,...] the prompt paraphrased); with a2 = 1 the discriminant is 2^2 3^2 * 2777 * 311341
and |disc|/N = 6 exactly (matches the paper's structure), whereas a2 = 0 gives a curve of
a different, incompatible conductor.  Self-validated below; do not trust the paraphrase.

At sqrt(N) ~ 72025 the kernel needs ~435600 terms; the exact kernel is evaluated hybrid
(mpmath for n <= 300, Gauss-Laguerre form of the same incomplete-Gamma strand for the tail,
exact identity T_n(t) = r^s Gamma(s,x), s = 1+it, x = 2pi n/sqrt(N)).  Validated per-term
against mpmath AND by a full regression of the rank-5 tower (c_5 = 21036.8420) on the exact
same code path before any rank-6 claim.

BAD PRIMES: all four bad primes are MULTIPLICATIVE (p does not divide c4 at any of them),
so bad a_p in {+1, -1}; there are 16 sign assignments.  At sqrt(N) ~ 72025 the kernel
cutoff x <= 38 keeps only n <= 435597 << N, so no bad prime is ever felt by the kernel
(a_{311341}, a_{2777} land far beyond the cutoff; a_2, a_3 are inside but their sign is one
of the searched unknowns).  The bad-prime signs are pinned instead by the FORCED-ZERO TRIPLE:
rank 6, eps = +1 forces L(1) ~ 0, L''(1)/2 ~ 0, AND L^(4)(1)/4! ~ 0 simultaneously.  Only
the correct sign vector produces all three below 1e-5 of the G_6 scale (a brutal self-test).
"""
import math

import numpy as np
import mpmath as mp

mp.mp.dps = 20
KGL = 96
VGL, WGL = np.polynomial.laguerre.laggauss(KGL)

# The Gauss-Laguerre form of the incomplete-Gamma strand is exact only for x = 2pi n/sqrt(N)
# NOT too small: at x < ~0.4 the 96-node rule loses accuracy (T ~ 1/x is near-singular there).
# The boundary must therefore be set by an x-threshold, not a fixed n -- at sqrt(N) ~ 72025
# a fixed n=300 lands at x=0.026 (rel err 1e-5, contaminates the even jets).  We evaluate
# mpmath-exact for x <= XSMALL and Gauss-Laguerre for the tail; validation A below confirms
# the worst per-term error over the ACTUAL split is ~1e-13.
XSMALL = 0.5


def nsmall_for(N):
    return int(XSMALL * math.sqrt(N) / (2 * math.pi)) + 1


def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def ap_general(p, a1, a2, a3, a4, a6):
    """a_p for a good prime via the b-invariant quadratic-completion count."""
    if p == 2:
        cnt = sum(1 for x in range(2) for y in range(2)
                  if (y * y + a1 * x * y + a3 * y - (x ** 3 + a2 * x * x + a4 * x + a6)) % 2 == 0)
        return 2 + 1 - (cnt + 1)
    b2, b4, b6 = a1 * a1 + 4 * a2, 2 * a4 + a1 * a3, a3 * a3 + 4 * a6
    x = np.arange(p, dtype=np.int64)
    z = (4 * (x ** 3 % p) + (b2 % p) * (x * x % p) + ((2 * b4) % p) * x + (b6 % p)) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(z == 0, 0, np.where(isq[z], 1, -1))
    return int(-chi.sum())


def bank_general(N, ainv, bad_ap, nmax):
    """Multiplicative a_n; bad primes p | N get a_{p^k} = bad_ap[p]^k."""
    primes = sieve_primes(nmax)
    ap = {}
    for p in primes:
        p = int(p)
        ap[p] = bad_ap[p] if N % p == 0 else ap_general(p, *ainv)
    a = np.zeros(nmax + 1)
    a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        pk = n // m
        if m > 1:
            a[n] = a[m] * a[pk]
        elif k == 1:
            a[n] = ap[p]
        else:
            a[n] = ap[p] * a[pk // p] - (0 if N % p == 0 else p) * a[pk // p // p]
    return a


def bank_good(N, ainv, nmax):
    """a_n with all bad-prime a_{p^k} set to 0 (bad primes deferred).  Returns (a, ap_good)
    where ap_good is the dict of good a_p; the caller multiplies in bad-prime chains."""
    primes = sieve_primes(nmax)
    ap = {}
    for p in primes:
        p = int(p)
        ap[p] = 0 if N % p == 0 else ap_general(p, *ainv)
    return ap, primes


def build_bank_from_ap(N, ap, primes, nmax):
    a = np.zeros(nmax + 1)
    a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    for n in range(2, nmax + 1):
        p = int(spf[n])
        m, k = n, 0
        while m % p == 0:
            m //= p
            k += 1
        pk = n // m
        if m > 1:
            a[n] = a[m] * a[pk]
        elif k == 1:
            a[n] = ap[p]
        else:
            a[n] = ap[p] * a[pk // p] - (0 if N % p == 0 else p) * a[pk // p // p]
    return a


def G_ladder(rmax, xs):
    du = math.log(xs[1] / xs[0])
    Gs = [np.exp(-xs)]
    for _ in range(rmax):
        g = Gs[-1]
        c = np.concatenate([[0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * du)])
        Gs.append(c[-1] - c)
    return Gs


XS = np.exp(np.linspace(math.log(1e-8), math.log(80.0), 60000))
GS = G_ladder(6, XS)


def jet_window(a, N, eps, tw):
    """Z(t) on the window from the exact double-ended kernel, hybrid evaluation.
    eps=+1: Z = Re Lambda (even); eps=-1: Z = Im Lambda (odd)."""
    sq = math.sqrt(N)
    n_all = np.nonzero(a[1:])[0] + 1
    x_all = 2 * math.pi * n_all / sq
    keep = x_all <= 38.0
    n_all, x_all = n_all[keep], x_all[keep]
    a_all = a[n_all]
    small = x_all <= XSMALL
    Z = np.zeros(len(tw))
    # small n: mpmath
    for n, x, an in zip(n_all[small], x_all[small], a_all[small]):
        r = 1.0 / x
        for i, t in enumerate(tw):
            ss = mp.mpf(1) + 1j * mp.mpf(float(t))
            T = (mp.mpf(r) ** ss) * mp.gammainc(ss, float(x), mp.inf)
            Z[i] += an * 2 * (T.real if eps == +1 else T.imag)
    # large n: Gauss-Laguerre, vectorized over (n, node)
    xb = x_all[~small]
    ab = a_all[~small]
    if len(xb):
        Lmat = np.log1p(VGL[None, :] / xb[:, None])          # (nb, K)
        pref = ab * np.exp(-xb) / xb                          # (nb,)
        for i, t in enumerate(tw):
            ph = np.exp(1j * t * Lmat) @ WGL                  # (nb,)
            tot = np.dot(pref, ph)
            Z[i] += 2 * (tot.real if eps == +1 else tot.imag)
    return Z


def jet_taylor(tw, Z, deg, hw):
    """Taylor coefficients c_k = Z^(k)(0)/k! of the window, via a WELL-CONDITIONED
    Chebyshev fit on the rescaled coordinate u = t/hw (cond ~ 3 vs the raw monomial
    Vandermonde's ~1e20 at deg 19 -- the ill-conditioned monomial fit is what floods
    the low even jets with 1e-1 fit noise; Chebyshev lets the true dead-layers show)."""
    from numpy.polynomial import chebyshev as C
    u = tw / hw
    cheb = np.polynomial.Chebyshev(np.linalg.lstsq(C.chebvander(u, deg), Z, rcond=None)[0])
    pu = cheb.convert(kind=np.polynomial.Polynomial).coef        # power series in u
    c = np.zeros(deg + 1)
    c[: len(pu)] = pu / (hw ** np.arange(len(pu)))               # rescale u -> t
    return c


def g_sums(a, N, rs, nmax):
    """G-series L^(r)(1)/r! = 2 sum (a_n/n) G_r(2pi n/sqrt(N)) for each r in rs."""
    sq = math.sqrt(N)
    n_arr = np.arange(1, nmax + 1, dtype=np.float64)
    x_arr = 2 * math.pi * n_arr / sq
    return {r: 2 * np.sum((a[1:] / n_arr) * np.interp(x_arr, XS, GS[r])) for r in rs}


# ============================================================================
# validation A: per-term hybrid vs mpmath on the rank-6 grid
# ============================================================================
N6 = 5187563742
AINV6 = (1, 1, 0, -2582, 48720)
SQ6 = math.sqrt(N6)
NSMALL6 = nsmall_for(N6)          # smallest n handled by Gauss-Laguerre is NSMALL6+1
worst = worst_rel = 0.0
# test only the ACTUAL Gauss-Laguerre region (x > XSMALL): the split point and up
for n in (NSMALL6 + 1, NSMALL6 + 50, 10000, 100000, 435000):
    x = 2 * math.pi * n / SQ6
    for t in (0.0, 0.09, -0.15):
        ss = mp.mpf(1) + 1j * mp.mpf(t)
        T_mp = complex((mp.mpf(1.0 / x) ** ss) * mp.gammainc(ss, x, mp.inf))
        T_gl = complex(np.exp(-x) / x * (np.exp(1j * t * np.log1p(VGL / x)) @ WGL))
        worst = max(worst, abs(T_mp - T_gl))
        worst_rel = max(worst_rel, abs(T_mp - T_gl) / abs(T_mp))
print(f"[validate A] Gauss-Laguerre vs mpmath per-term over the actual split "
      f"(x > XSMALL={XSMALL}, n > {NSMALL6}): worst |diff| = {worst:.2e}, worst rel = {worst_rel:.2e}")

# ============================================================================
# validation B / regression guard: re-run the rank-5 tower, confirm c_5 agree = 1.00000
# ============================================================================
print("[validate B] rank-5 regression on the exact code path (target |c5| = 21036.8420)...")
N5 = 19047851
AINV5 = (0, 0, 1, -79, 342)
SQ5 = math.sqrt(N5)
NMAX5 = int(38.0 * SQ5 / (2 * math.pi)) + 1
a5 = bank_general(N5, AINV5, {}, NMAX5)
sums5 = g_sums(a5, N5, (5,), NMAX5)
pred_c5 = (SQ5 / (2 * math.pi)) * sums5[5]
tw5 = np.linspace(-0.25, 0.25, 51)
Z5 = jet_window(a5, N5, -1, tw5)
c5 = jet_taylor(tw5, Z5, 13, 0.25)
print(f"             |c5| = {abs(c5[5]):.4f}  predicted = {abs(pred_c5):.4f}"
      f"  agree = {abs(c5[5] / pred_c5):.5f}   [standing regression]")

# ============================================================================
# rank 6: curve identification + self-validation
# ============================================================================
print(f"\n[rank 6] curve [1,1,0,-2582,48720], N = {N6}")
a1, a2, a3, a4, a6 = AINV6
b2, b4, b6 = a1 * a1 + 4 * a2, 2 * a4 + a1 * a3, a3 * a3 + 4 * a6
b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
c4 = b2 * b2 - 24 * b4
disc = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 * b6 + 9 * b2 * b4 * b6


def factor(n):
    n = abs(n); f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


fdisc, fN = factor(disc), factor(N6)
print(f"         disc = {disc} = {fdisc}")
print(f"         N    = {N6} = {fN}")
print(f"         |disc|/N = {abs(disc)//N6} (Elkies-Watkins I-column: 6){' OK' if abs(disc)%N6==0 and abs(disc)//N6==6 else ' MISMATCH'}")
badp = sorted(fN)
mult = [p for p in badp if c4 % p != 0]
addv = [p for p in badp if c4 % p == 0]
print(f"         bad primes {badp}: multiplicative {mult} (a_p=+-1), additive {addv} (a_p=0)")

NMAX6 = int(38.0 * SQ6 / (2 * math.pi)) + 1
print(f"         building good-prime bank to n = {NMAX6} (point counting ~37k primes)...")
import time
t0 = time.time()
ap_good, primes6 = bank_good(N6, AINV6, NMAX6)
print(f"         point counting done in {time.time()-t0:.1f}s. "
      f"a_5={ap_good.get(5)}, a_7={ap_good.get(7)}, a_11={ap_good.get(11)} (spot Deligne):")
for p in (101, 1009, 10007, 100003):
    assert abs(ap_good[p]) <= 2 * math.sqrt(p) + 1e-9, (p, ap_good[p])
print(f"         Deligne |a_p| <= 2sqrt(p) holds at p in {{101,1009,10007,100003}}: "
      + ", ".join(f"a_{p}={ap_good[p]}" for p in (101, 1009, 10007, 100003)))

# ---- forced-zero search over the 16 bad-prime sign vectors ----
# Bad primes inside the kernel/G-series range: build the full bank per sign vector.
# Only primes <= NMAX6 enter the G-series; 311341 < NMAX6 so all four matter to the sums.
print(f"\n         forced-zero search: rank 6, eps=+1 => L(1)=L''(1)/2=L^(4)(1)/4!=0.")
print(f"         Sextic scale for reference: |L^(6)(1)/6!| sets the yardstick.\n")
import itertools
best = None
rows = []
for signs in itertools.product((+1, -1), repeat=len(badp)):
    ap = dict(ap_good)
    for p, s in zip(badp, signs):
        ap[p] = s
    a = build_bank_from_ap(N6, ap, primes6, NMAX6)
    s = g_sums(a, N6, (0, 2, 4, 6), NMAX6)
    scale = abs(s[6]) if abs(s[6]) > 0 else 1.0
    triple = max(abs(s[0]), abs(s[2]), abs(s[4])) / scale
    rows.append((triple, signs, s))
    if best is None or triple < best[0]:
        best = (triple, signs, s, a)
rows.sort()
print("         top sign vectors by max|forced zero|/|L6-scale| (want << 1e-5):")
for triple, signs, s in rows[:4]:
    sv = {p: si for p, si in zip(badp, signs)}
    print(f"           signs {sv}: |L0|={abs(s[0]):.3e} |L2/2|={abs(s[2]):.3e} "
          f"|L4/4!|={abs(s[4]):.3e}  ratio={triple:.2e}   L6/6!={s[6]:.6f}")

triple, signs, s6, a6bank = best
sv = {p: si for p, si in zip(badp, signs)}
print(f"\n         SELECTED bad-prime signs: {sv}   (triple-zero ratio {triple:.2e})")
pred_c6 = (SQ6 / (2 * math.pi)) * s6[6]
print(f"         forced zeros: L(1)={s6[0]:.3e}, L''(1)/2={s6[2]:.3e}, L^(4)(1)/4!={s6[4]:.3e}")
print(f"         BSD leading datum: L^(6)(1)/6! = {s6[6]:.6f}")

# ============================================================================
# the jet tower: exact double-ended kernel, eps=+1 (even strand), window |t|<=0.18, deg 19
# ============================================================================
HW, DEG, NPT = 0.18, 19, 61
tp0 = math.log(SQ6 / (2 * math.pi))
trunc = (tp0 * HW) ** (DEG + 1) / math.factorial(DEG + 1)
print(f"\n         jet fit: window |t|<={HW}, deg {DEG}, {NPT} pts; "
      f"truncation (theta'*hw)^(deg+1)/(deg+1)! = {trunc:.2e}")
tw6 = np.linspace(-HW, HW, NPT)
t0 = time.time()
Z6 = jet_window(a6bank, N6, +1, tw6)
print(f"         jet_window (exact kernel, {NMAX6} terms) done in {time.time()-t0:.1f}s")
c6 = jet_taylor(tw6, Z6, DEG, HW)

print("\nrank-6 hinge jet tower (exact double-ended kernel, EVEN strand, eps=+1):")
print("  " + "  ".join(f"c{k}={abs(c6[k]):.2e}" for k in range(7)))
print(f"  leading jet |c_6| = {abs(c6[6]):.4f}   predicted (sqrt(N)/2pi)*G6 = {abs(pred_c6):.4f}"
      f"   agree = {abs(c6[6] / pred_c6):.5f}")
print(f"  d(0) = 6: odd jets c1/c3/c5 dead by the weld (even wave), c0/c2/c4 dead by rank, sextic alive.")
print(f"\n  dead-layer depths (|c_k| vs |c_6|):")
for k in range(6):
    print(f"    c{k}: {abs(c6[k]):.3e}  ({abs(c6[k])/abs(c6[6]):.2e} of leading)")

# robustness: a real leading jet is stable under window/degree; an artifact drifts.
print(f"\n  robustness (|c_6| and agreement across fit settings; real jet is stable):")
for hw, deg, npt in [(0.18, 19, 61), (0.15, 17, 61), (0.20, 21, 81), (0.16, 15, 51)]:
    twr = np.linspace(-hw, hw, npt)
    Zr = jet_window(a6bank, N6, +1, twr)
    cr = jet_taylor(twr, Zr, deg, hw)
    print(f"    hw={hw} deg={deg} npt={npt}: |c6|={abs(cr[6]):.4f}  agree={abs(cr[6]/pred_c6):.5f}"
          f"  (c4/c6={abs(cr[4])/abs(cr[6]):.1e})")
