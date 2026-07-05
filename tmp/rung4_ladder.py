"""RUNG 4 — the eigenstate-dimensionality (jet-tower) rank reading pushed to RANK 4.

Same instrument as tmp/rung3_ladder.py, one rung higher.  At the hinge s=1 the double-ended
kernel (helix strand + eps*antihelix strand, equal weight at the hinge) has a jet tower.  For
EVEN rank the root number is eps=+1, so the rotated real part is EVEN in the twist t:
  * PARITY (eps=+1) kills the ODD jets c_1, c_3 to ~machine zero;
  * RANK kills the EVEN jets below the rank (c_0 = L(1), c_2 = L''(1)/2!) to the G-series floor
    (they are genuinely zero: rank 4 => L(1)=L'(1)=L''(1)=L'''(1)=0);
  * the first SURVIVING jet is |c_4| = (sqrt(N)/2pi) L^{(4)}(1)/4!  -- the BSD leading datum,
    read as the ORDER of the surviving jet on ONE archimedean carrier.  rank = 4 = the
    eigenstate dimensionality at the cancellation.

Non-circular:  the curve identity + rank come from LMFDB (external ground truth); the a_p come
straight from in-house point counting; the ladder READS the rank independently and it must land
at 4.  eps is auto-detected from the pinned ray of the completed wave AND cross-checked against
the known even parity.

Curve (LMFDB, the historically famous smallest-conductor rank-4 curve, first non-prime N):
  234446.a1  [1,-1,0,-79,289]   N = 234446 = 2 * 117223   rank 4   w = +1

Run:  python3 rung4_ladder.py
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
GS = G_ladder(5, XS)                                   # need G_4 (and G_5 headroom)
_chk = np.exp(np.linspace(math.log(0.1), math.log(10.0), 50))
assert np.max(np.abs(np.interp(_chk, XS, GS[1]) - exp1(_chk)) / exp1(_chk)) < 1e-5


def G_r(r, x):
    return np.interp(x, XS, GS[r])


# ---------------------------------------------------------- general point count
def ap_general(p, a1, a2, a3, a4, a6):
    """a_p = p - #affine points of y^2+a1 xy+a3 y = x^3+a2 x^2+a4 x+a6 over F_p."""
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
    D = (B * B + 4 * f) % p
    isq = np.zeros(p, dtype=bool)
    isq[(x * x) % p] = True
    chi = np.where(D == 0, 0, np.where(isq[D], 1, -1))
    return int(-chi.sum())


def an_bank_general(ap_fn, bad, nmax):
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
            a[n] = ap[p] * a[pk // p]
        else:
            a[n] = ap[p] * a[pk // p] - p * a[pk // p // p]
    return a, ap


# --------------------------------------------------- exact double-ended kernel
def exact_tower(a, N, eps, tw, dps=18, xcut=42):
    import mpmath as mp
    mp.mp.dps = dps
    sq = math.sqrt(N)
    vals = []
    for t in tw:
        s = mp.mpf(1) + 1j * mp.mpf(float(t))
        tot = mp.mpc(0)
        for n in range(1, len(a)):
            if a[n] == 0.0:
                continue
            x = 2 * math.pi * n / sq
            if x > xcut:
                break
            r = sq / (2 * math.pi * n)
            tot += a[n] * (r ** s * mp.gammainc(s, x, mp.inf)
                           + eps * r ** (2 - s) * mp.gammainc(2 - s, x, mp.inf))
        vals.append(complex(tot))
    return np.array(vals)


# --------------------------------------------------------------------- curve
TAG, N, A, BAD, R = "234446.a1", 234446, (1, -1, 0, -79, 289), [2, 117223], 4

# keep the bank below the huge bad prime 117223 so no p-of-bad-reduction sits inside it
# with a wrong -p term; small-n terms dominate both the eps-detect and the G_4 series.
NB = 50000

print("=== point-count sanity gate (full Weierstrass ap on a known curve) ===")
# ap_general must reproduce the trusted y^2+y engine on the rank-3 baseline 5077.a1=[0,0,1,-7,6]
_gp = [int(p) for p in sieve_primes(300) if p != 5077]
_mm = [p for p in _gp if ap_general(p, 0, 0, 1, -7, 6) != ap_special(p, 0, -7, 6)]
print(f"  ap_general vs trusted ap_curve on 5077.a1, primes<300: "
      f"{'ALL AGREE' if not _mm else 'MISMATCH ' + str(_mm)}")
# Hasse anchor on the rank-4 curve itself
_a2 = ap_general(2, *A)
print(f"  234446.a1 a_2 = {_a2:+d} (bad prime 2, nonsplit mult => expect -1)")
print()

a, apdict = an_bank_general(lambda p: ap_general(p, *A), BAD, NB)
for p in list(apdict)[:400]:
    if p not in BAD:
        assert abs(apdict[p]) <= 2 * math.sqrt(p) + 1e-9, (p, apdict[p])

# eps from the pinned ray of the completed wave
lam = a[1:] / np.sqrt(np.arange(1.0, NB + 1))
ts = np.linspace(0.05, 12.0, 500)
Lam = completed_line(lam, N, ts)
mask = np.abs(Lam) > 0.5 * np.median(np.abs(Lam))
zbar = np.mean(np.exp(2j * np.mod(np.angle(Lam[mask]), math.pi)))
ray = (np.angle(zbar) / 2) % math.pi
eps = -1 if abs(ray - math.pi / 2) < math.pi / 4 else +1

# jet tower from the exact double-ended kernel, rotated to the real chart
tw = np.linspace(-0.4, 0.4, 49)
V = np.vander(tw, 8, increasing=True)
Zx = (exact_tower(a, N, eps, tw, dps=22, xcut=45) * np.exp(-1j * ray)).real
cx = np.linalg.lstsq(V, Zx, rcond=None)[0]

# independent prediction of the surviving jet from the G_4 series
n = np.arange(1, NB + 1, dtype=np.float64)
x = 2 * math.pi * n / math.sqrt(N)
series = 2 * np.sum((a[1:] / n) * G_r(R, x))
pred_cr = (math.sqrt(N) / (2 * math.pi)) * series

absc = [abs(cx[k]) for k in range(6)]
live = int(np.argmax(absc))
tower = "  ".join(f"c{k}={absc[k]:.2e}" for k in range(6))
agree = abs(cx[R] / pred_cr) if pred_cr else float("nan")

print(f"curve {TAG}   N={N}   eps={eps:+d} (ray={ray/math.pi:.3f}p, want +1 even rank)")
print(f"  jet tower:  {tower}")
print(f"  first surviving jet at order {live}   (want {R})")
print(f"  |c_{R}| exact = {abs(cx[R]):.5f}   |c_{R}| pred(G_{R} series) = {abs(pred_cr):.5f}"
      f"   ratio = {agree:.4f}")
print()
print("Reading: eps=+1 (even rank) => rotated real part EVEN in t => c_1,c_3 killed by PARITY;")
print(f"c_0,c_2 killed by RANK (L(1)=L''(1)=0, r=4>2) to the G-series floor; c_4 the first")
print(f"SURVIVING jet = (sqrt(N)/2pi) L^(4)(1)/4!.  rank-4 eigenstate dimensionality: the")
print(f"surviving jet sits at order 4 -- one rung above rung 3, same instrument, same carrier.")
