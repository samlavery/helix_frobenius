"""Rank 4 at the hinge: 234446.a1 (Elkies), the smallest-conductor rank-4 curve.

    y^2 + xy = x^3 - x^2 - 79x + 289,   N = 234446 = 2 * 117223,   eps = +1.

The dimension principle predicts the hinge jet tower c_0..c_4 dies four deep:
c_1, c_3 dead by PARITY (weld, eps=+1), c_0, c_2 dead by RANK, and the first live jet

    |c_4| = (sqrt(N)/2pi) * L''''(1)/4! = (sqrt(N)/2pi) * 2 sum (a_n/n) G_4(2pi n/sqrt(N)).

At sqrt(N) = 484 only the exact double-ended kernel can read the hinge (the single-strand
tapered bank floors at ~1e-2 already by N=5077 — the antihelix zone).  Series-side the
same coefficients must produce THREE numerical zeros: G_0 sum = L(1) = 0, G_2 sum =
L''(1)/2 = 0 (rank), with G_4 giving the leading datum.  The bad prime a_2 (multiplicative,
+-1) is determined two independent ways: nonsingular point count mod 2, and the dead-layer
test (the wrong sign revives L(1)).

Kernel with the conjugate-strand trick (eps real, a_n real, x_n = 1/r_n):
    Lambda(1/2+it) = sum a_n [T_n(t) + eps conj T_n(t)],  T_n = r^s Gamma(s, x_n), s = 1+it.
"""
import math

import numpy as np
import mpmath as mp

mp.mp.dps = 20

A1, A2_, A3, A4_, A6_ = 1, -1, 0, -79, 289
N = 234446
B2, B4, B6 = A1 * A1 + 4 * A2_, 2 * A4_ + A1 * A3, A3 * A3 + 4 * A6_
SQ = math.sqrt(N)
XCUT = 38.0
NMAX = int(XCUT * SQ / (2 * math.pi)) + 1


def sieve_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def ap_general(p):
    """a_p for good odd p via (2y + a1 x + a3)^2 = 4x^3 + b2 x^2 + 2 b4 x + b6."""
    x = np.arange(p, dtype=np.int64)
    z = (4 * (x ** 3 % p) + (B2 % p) * (x * x % p) + ((2 * B4) % p) * x + (B6 % p)) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(z == 0, 0, np.where(isq[z], 1, -1))
    return int(-chi.sum())


def a2_from_count():
    """Nonsingular points mod 2 (multiplicative reduction): #ns incl inf = 2 - a_2."""
    pts, sing = [], []
    for x in range(2):
        for y in range(2):
            F = (y * y + A1 * x * y + A3 * y - (x ** 3 + A2_ * x * x + A4_ * x + A6_)) % 2
            if F == 0:
                Fx = (A1 * y - (3 * x * x + 2 * A2_ * x + A4_)) % 2
                Fy = (2 * y + A1 * x + A3) % 2
                (sing if (Fx == 0 and Fy == 0) else pts).append((x, y))
    return 2 - (len(pts) + 1)      # +1 for infinity


def an_bank2(a2, nmax):
    primes = sieve_primes(nmax)
    ap = {}
    for p in primes:
        p = int(p)
        if p == 2:
            ap[p] = a2
        elif N % p == 0:
            ap[p] = 0          # only 117223 > nmax; placeholder
        else:
            ap[p] = ap_general(p)
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
            bad = (N % p == 0)
            a[n] = ap[p] * a[pk // p] - (0 if bad else p) * a[pk // p // p]
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
GS = G_ladder(4, XS)

a2_count = a2_from_count()
print(f"a_2 from nonsingular count mod 2: {a2_count:+d}")

print(f"coefficient bank to n = {NMAX} (point counting)...")
banks = {s: an_bank2(s, NMAX) for s in (+1, -1)}

n_arr = np.arange(1, NMAX + 1, dtype=np.float64)
x_arr = 2 * math.pi * n_arr / SQ
print(f"{'a_2':>4} | {'L(1) [G0]':>12} {'L\"(1)/2 [G2]':>13} {'L4(1)/4! [G4]':>13}   (rank 4: first two must vanish)")
for s in (+1, -1):
    a = banks[s]
    sums = [2 * np.sum((a[1:] / n_arr) * np.interp(x_arr, XS, GS[r])) for r in (0, 2, 4)]
    print(f"{s:+4d} | {sums[0]:>12.3e} {sums[1]:>13.3e} {sums[2]:>13.6f}")

a2 = a2_count
a = banks[a2]
G4sum = 2 * np.sum((a[1:] / n_arr) * np.interp(x_arr, XS, GS[4]))
pred_c4 = (SQ / (2 * math.pi)) * G4sum

# exact double-ended kernel on the hinge window (conjugate-strand trick, eps = +1)
print(f"exact kernel window (n_eff = {NMAX}, mpmath dps 20)...")
nz = [(int(n), float(a[n]), 2 * math.pi * n / SQ, SQ / (2 * math.pi * n))
      for n in range(1, NMAX + 1) if a[n] != 0.0]
tw = np.linspace(-0.4, 0.4, 41)


def Lam_exact(t):
    ss = mp.mpf(1) + 1j * mp.mpf(float(t))
    tot = mp.mpf(0)
    for n, an, x, r in nz:
        T = (mp.mpf(r) ** ss) * mp.gammainc(ss, x, mp.inf)
        tot += an * 2 * T.real          # T + conj(T), eps = +1
    return float(tot)

Z = np.array([Lam_exact(t) for t in tw])
V = np.vander(tw, 11, increasing=True)
c = np.linalg.lstsq(V, Z, rcond=None)[0]

print()
print("hinge jet tower (exact kernel):")
print("  " + "  ".join(f"c{k}={abs(c[k]):.2e}" for k in range(5)))
print(f"  leading jet |c_4| = {abs(c[4]):.5f}   predicted (sqrt(N)/2pi)*G4 = {abs(pred_c4):.5f}"
      f"   agree = {abs(c[4] / pred_c4):.5f}")
print(f"  d(0) = 4: c0..c3 dead (parity kills 1,3; rank kills 0,2), quartic jet alive.")
print(f"  [L''''(1)/4! = {G4sum:.6f} from our own coefficients — reference value for the record]")
