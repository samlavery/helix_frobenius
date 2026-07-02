"""Rank 5 at the hinge: the Brumer-McGuinness curve, conductor 19,047,851.

    y^2 + y = x^3 - 79x + 342,   N = 19047851 (prime),   rank 5,   eps = -1.

The quintic rung of the ladder.  eps = -1 makes the wave ODD (even jets dead by
construction = the weld; HingeKernel.odd_even_jets_dead), rank kills c_1 and c_3
(arithmetic zeros), and the first live jet is

    |c_5| = (sqrt(N)/2pi) * L^(5)(1)/5! = (sqrt(N)/2pi) * 2 sum (a_n/n) G_5(2pi n/sqrt(N)).

At sqrt(N) = 4364 the kernel needs ~26k terms; mpmath per-term is too slow, so the
exact kernel is evaluated hybrid: mpmath for n <= 300, and for the tail the Gauss-
Laguerre form of the same incomplete-Gamma strand (exact identity, x = 2pi n/sqrt(N)):

    T_n(t) = r^s Gamma(s, x) = (e^-x / x) * int_0^inf (1 + v/x)^{it} e^-v dv,  s = 1+it,

which vectorizes over (n, node, t).  The hybrid is validated two ways before use:
per-term against mpmath, and a full regression of the rank-4 tower (c_4 = 689.2248).
Series side, the same coefficients must produce TWO forced zeros (L'(1), L'''(1)/3!).
"""
import math

import numpy as np
import mpmath as mp

mp.mp.dps = 20
NSMALL = 300
KGL = 96
VGL, WGL = np.polynomial.laguerre.laggauss(KGL)


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


def G_ladder(rmax, xs):
    du = math.log(xs[1] / xs[0])
    Gs = [np.exp(-xs)]
    for _ in range(rmax):
        g = Gs[-1]
        c = np.concatenate([[0.0], np.cumsum(0.5 * (g[1:] + g[:-1]) * du)])
        Gs.append(c[-1] - c)
    return Gs


XS = np.exp(np.linspace(math.log(1e-8), math.log(80.0), 60000))
GS = G_ladder(5, XS)


def jet_window(a, N, eps, tw):
    """Z(t) on the window from the exact double-ended kernel, hybrid evaluation.
    eps=+1: Z = Re Lambda (even); eps=-1: Z = Im Lambda (odd)."""
    sq = math.sqrt(N)
    n_all = np.nonzero(a[1:])[0] + 1
    x_all = 2 * math.pi * n_all / sq
    keep = x_all <= 38.0
    n_all, x_all = n_all[keep], x_all[keep]
    a_all = a[n_all]
    small = n_all <= NSMALL
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


# ---- validation A: per-term hybrid vs mpmath on the rank-5 grid
N5 = 19047851
AINV5 = (0, 0, 1, -79, 342)
SQ5 = math.sqrt(N5)
worst = 0.0
for n in (301, 500, 2000, 11000, 26000):
    x = 2 * math.pi * n / SQ5
    for t in (0.0, 0.13, -0.25):
        ss = mp.mpf(1) + 1j * mp.mpf(t)
        T_mp = complex((mp.mpf(1.0 / x) ** ss) * mp.gammainc(ss, x, mp.inf))
        T_gl = complex(np.exp(-x) / x * (np.exp(1j * t * np.log1p(VGL / x)) @ WGL))
        worst = max(worst, abs(T_mp - T_gl))
print(f"[validate A] Gauss-Laguerre vs mpmath per-term: worst |diff| = {worst:.2e}")

# ---- validation B: rank-4 regression (must reproduce c_4 = 689.2248)
print("[validate B] rank-4 regression (234446.a, exact tower target c4 = 689.22477)...")
NMAX4 = int(38.0 * math.sqrt(234446) / (2 * math.pi)) + 1
a4bank = bank_general(234446, (1, -1, 0, -79, 289), {2: -1, 117223: 0}, NMAX4)
tw4 = np.linspace(-0.4, 0.4, 41)
Z4 = jet_window(a4bank, 234446, +1, tw4)
c4 = np.linalg.lstsq(np.vander(tw4, 11, increasing=True), Z4, rcond=None)[0]
print(f"             tower: " + " ".join(f"c{k}={abs(c4[k]):.2e}" for k in range(5))
      + f"   [c4 agree vs mpmath run: {abs(c4[4])/689.22477:.6f}]")

# ---- rank 5
print(f"[rank 5] N = {N5} = ", end="")
pr = sieve_primes(int(N5 ** 0.5) + 1)
divs = [int(p) for p in pr if N5 % p == 0]
print("prime" if not divs else f"COMPOSITE {divs}!")
NMAX5 = int(38.0 * SQ5 / (2 * math.pi)) + 1
print(f"         bank to n = {NMAX5} (point counting)...")
a5 = bank_general(N5, AINV5, {}, NMAX5)
for p in (101, 1009, 10007):
    assert abs(a5[p]) <= 2 * math.sqrt(p), p                  # Deligne
print(f"         a_2 = {a5[2]:+.0f}, a_3 = {a5[3]:+.0f}, a_5 = {a5[5]:+.0f} (point counts)")

n_arr = np.arange(1, NMAX5 + 1, dtype=np.float64)
x_arr = 2 * math.pi * n_arr / SQ5
sums = {r: 2 * np.sum((a5[1:] / n_arr) * np.interp(x_arr, XS, GS[r])) for r in (1, 3, 5)}
print(f"         G-series (eps=-1): L'(1) = {sums[1]:.3e}, L'''(1)/3! = {sums[3]:.3e}  <- rank forces both to 0")
print(f"                            L^(5)(1)/5! = {sums[5]:.6f}  <- the BSD leading datum")
pred_c5 = (SQ5 / (2 * math.pi)) * sums[5]

tw5 = np.linspace(-0.25, 0.25, 51)
Z5 = jet_window(a5, N5, -1, tw5)
c5 = np.linalg.lstsq(np.vander(tw5, 14, increasing=True), Z5, rcond=None)[0]
print()
print("rank-5 hinge jet tower (exact double-ended kernel, odd strand):")
print("  " + "  ".join(f"c{k}={abs(c5[k]):.2e}" for k in range(6)))
print(f"  leading jet |c_5| = {abs(c5[5]):.4f}   predicted (sqrt(N)/2pi)*G5 = {abs(pred_c5):.4f}"
      f"   agree = {abs(c5[5] / pred_c5):.5f}")
print(f"  d(0) = 5: even jets dead by the weld (odd wave), c1/c3 dead by rank, quintic alive.")
