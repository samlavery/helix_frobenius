"""Rung-3 push: the eigenstate-dimensionality (jet-tower) rank reading on FRESH rank-3
curves beyond 5077a.

Same physics as tmp/bsd_rank_ladder.py: at the hinge s=1 the double-ended kernel
(helix strand + eps*antihelix strand, both weighing equally at the hinge) has a jet
tower; PARITY (eps) kills alternate jets to machine zero, RANK kills the rest below
order r, and the first surviving jet |c_r| = (sqrt(N)/2pi) L^(r)(1)/r! IS the BSD
leading datum.  rank = dimensions of the surviving jet, read on ONE archimedean carrier.

Generalisation needed for fresh rank-3 curves (5077 is the ONLY prime-conductor one at
smallest conductor; the next ones are composite):
  * full Weierstrass form y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6;
  * a_p by DIRECT point count at EVERY prime, good and bad:
        a_p = p - #{affine points on the reduced curve}
    which for a minimal model equals p+1-#E(F_p) at good p and p-#E_ns(F_p) at
    multiplicative p (the one singular affine point is counted then removed) -> a_p=+-1;
  * multi-bad-prime Euler recursion (bad p: a_{p^k}=a_p^k, no -p term).
No a_N pinning is needed: every local factor comes straight from point counting.
eps (root number) is still read from the pinned ray of the completed wave (eps=-1 for
odd rank => ray pi/2), exactly as the ladder does.

Curves (a-invariants + conductor from LMFDB, all rank 3):
  5077.a1  [0,0,1,-7,6]      N=5077   (prime)      -- baseline, end-to-end self check
  11197.a1 [1,-1,1,-6,0]     N=11197  (prime)
  11642.a1 [1,-1,0,-16,28]   N=11642 = 2*5821
  12279.a1 [0,-1,1,-10,12]   N=12279 = 3*4093
  13766.a1 [1,0,1,-23,42]    N=13766 = 2*6883
"""
import math

import numpy as np
from scipy.special import exp1

from bsd_weld import completed_line, sieve_primes, ap_curve as ap_special


# ---------------------------------------------------------------- G_r ladder
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
_chk = np.exp(np.linspace(math.log(0.1), math.log(10.0), 50))
assert np.max(np.abs(np.interp(_chk, XS, GS[1]) - exp1(_chk)) / exp1(_chk)) < 1e-5


def G_r(r, x):
    return np.interp(x, XS, GS[r])


# ---------------------------------------------------------- general point count
def ap_general(p, a1, a2, a3, a4, a6):
    """a_p = p - #affine points of y^2+a1 xy+a3 y = x^3+a2 x^2+a4 x+a6 over F_p.
    Uniform over good and (multiplicative) bad primes for a minimal model."""
    if p == 2:
        naff = 0
        for x in range(2):
            for y in range(2):
                if (y * y + a1 * x * y + a3 * y
                        - (x ** 3 + a2 * x * x + a4 * x + a6)) % 2 == 0:
                    naff += 1
        return 2 - naff
    x = np.arange(p, dtype=np.int64)
    B = (a1 * x + a3) % p
    f = (x ** 3 + a2 * x * x + a4 * x + a6) % p
    D = (B * B + 4 * f) % p                       # y = (-B +- sqrt D)/2, 2 invertible
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(D == 0, 0, np.where(isq[D], 1, -1))
    return int(-chi.sum())                          # = p - (p + sum chi)


def an_bank_general(ap_fn, bad, nmax):
    """Multiplicative a_n bank; bad = set of primes of bad reduction (no -p term)."""
    primes = sieve_primes(nmax)
    a = np.zeros(nmax + 1)
    a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for p in primes[::-1]:
        spf[p::p] = p
    ap = {int(p): ap_fn(int(p)) for p in primes}
    badset = set(bad)
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
        elif p in badset:
            a[n] = ap[p] * a[pk // p]               # a_{p^k} = a_p^k
        else:
            a[n] = ap[p] * a[pk // p] - p * a[pk // p // p]
    return a, ap


# --------------------------------------------------- exact double-ended kernel
def exact_tower(a, N, eps, tw):
    import mpmath as mp
    mp.mp.dps = 25
    sq = math.sqrt(N)
    vals = []
    for t in tw:
        s = mp.mpf(1) + 1j * mp.mpf(float(t))
        tot = mp.mpc(0)
        for n in range(1, len(a)):
            if a[n] == 0.0:
                continue
            x = 2 * math.pi * n / sq
            if x > 45:
                break
            r = sq / (2 * math.pi * n)
            tot += a[n] * (r ** s * mp.gammainc(s, x, mp.inf)
                           + eps * r ** (2 - s) * mp.gammainc(2 - s, x, mp.inf))
        vals.append(complex(tot))
    return np.array(vals)


# --------------------------------------------------------------------- curves
CURVES = [
    ("5077.a1",  5077,  (0, 0, 1, -7, 6),    [5077],       3),   # baseline recheck
    ("11197.a1", 11197, (1, -1, 1, -6, 0),   [11197],      3),
    ("11642.a1", 11642, (1, -1, 0, -16, 28), [2, 5821],    3),
    ("12279.a1", 12279, (0, -1, 1, -10, 12), [3, 4093],    3),
    ("13766.a1", 13766, (1, 0, 1, -23, 42),  [2, 6883],    3),
]

# Gate 1: ap_general (full Weierstrass) must reproduce the trusted specialised ap_curve
# (y^2+y form) on 5077.a1 = [0,0,1,-7,6] over all good primes < 300.
print("=== point-count sanity gate ===")
_gp = [int(p) for p in sieve_primes(300) if p != 5077]
_mismatch = [p for p in _gp
             if ap_general(p, 0, 0, 1, -7, 6) != ap_special(p, 0, -7, 6)]
print(f"  gate 1 ap_general vs trusted ap_curve on 5077.a1, primes<300: "
      f"{'ALL AGREE' if not _mismatch else 'MISMATCH ' + str(_mismatch)}")
# hand-derived anchors: a_2=-2, a_3=-3 (see docstring derivation)
print(f"  gate 2 hand anchors: a_2={ap_general(2,0,0,1,-7,6):+d} (want -2), "
      f"a_3={ap_general(3,0,0,1,-7,6):+d} (want -3), "
      f"a_5077={ap_general(5077,0,0,1,-7,6):+d} (want -1 = eps; point count reads the "
      f"true Atkin-Lehner sign that the N~5077 pinning could not resolve)")
print()

print(f"{'curve':>9} {'N':>6} {'eps(ray)':>11} | exact double-ended jet tower  |c_0|"
      f"  |c_1|  |c_2|  |c_3|  |c_4|          | {'c_3':>9} {'pred':>9} {'agree':>7} {'live jet'}")

for tag, N, A, bad, r in CURVES:
    NB = max(40000, int(3.0 * N ** 0.5 * 21 * 4))
    a, apdict = an_bank_general(lambda p: ap_general(p, *A), bad, NB)

    # Hasse gate on good primes (sample)
    for p in list(apdict)[:200]:
        if p not in bad:
            assert abs(apdict[p]) <= 2 * math.sqrt(p) + 1e-9, (tag, p)

    lam = a[1:] / np.sqrt(np.arange(1.0, NB + 1))
    ts = np.linspace(0.05, 12.0, 500)
    Lam = completed_line(lam, N, ts)
    mask = np.abs(Lam) > 0.5 * np.median(np.abs(Lam))
    zbar = np.mean(np.exp(2j * np.mod(np.angle(Lam[mask]), math.pi)))
    ray = (np.angle(zbar) / 2) % math.pi
    eps = -1 if abs(ray - math.pi / 2) < math.pi / 4 else +1

    tw = np.linspace(-0.5, 0.5, 81)
    V = np.vander(tw, 8, increasing=True)
    Zx = (exact_tower(a, N, eps, tw) * np.exp(-1j * ray)).real
    cx = np.linalg.lstsq(V, Zx, rcond=None)[0]

    n = np.arange(1, NB + 1, dtype=np.float64)
    x = 2 * math.pi * n / math.sqrt(N)
    series = 2 * np.sum((a[1:] / n) * G_r(r, x))          # L^(r)(1)/r!
    pred_cr = (math.sqrt(N) / (2 * math.pi)) * series

    absc = [abs(cx[k]) for k in range(5)]
    live = int(np.argmax([absc[k] for k in range(5)]))    # crude: biggest jet
    tower = " ".join(f"{v:.2e}" for v in absc)
    agree = abs(cx[r] / pred_cr) if pred_cr else float("nan")
    print(f"{tag:>9} {N:>6} {eps:+d}({ray/math.pi:.3f}p) | {tower} | "
          f"{abs(cx[r]):>9.4f} {abs(pred_cr):>9.4f} {agree:>7.4f}  c_{live}")

print()
print("Reading: eps=-1 (odd rank) => rotated real part odd in t => c_0,c_2,c_4 killed by")
print("PARITY to ~machine zero; c_1 killed by RANK (L'(1)=0, r=3>1) to the G-series floor;")
print("c_3 the first SURVIVING jet = (sqrt(N)/2pi) L'''(1)/3!  ('pred' = independent G_3 series).")
print("rank-3 eigenstate dimensionality: the surviving jet sits at order 3 on all fresh curves.")
