"""Sam's strand-topology claim, sharpened and measured.

Claim: Dirichlet fibers are HINGE-OUTWARD (start at the midpoint, grow up both helices);
elliptic fibers are ENDINGS-INWARD (start at the two cusps, meet at the Fricke midpoint).

Analytic shadow: a degree-1 Dirichlet series converges (conditionally) ON the line, so the
single outward strand is a valid representation of the hinge; a degree-2 series does NOT
converge at the center — the object exists there only as the two endpoint-inward
incomplete-Gamma strands.  Measured discriminator:

    single-strand hinge error vs bank size:  DECAYS for a character (any conductor),
                                             SATURATES for an elliptic curve.

Case A: Legendre character mod q = 10009 (prime, 1 mod 4: even, eps = +1), hinge
conductor scale n* = sqrt(q/pi) = 56 — five times 5077.a's n* = 11.3, so if raw conductor
size were the driver it should fail WORSE than 5077.a.
Case B: 5077.a (from tmp/rank5_weld machinery) — known to saturate.

Exact reference for A (two-strand theta kernel, even primitive chi):
    Lambda(s) = sum chi(n) [ (q/pi n^2)^{s/2} Gamma(s/2, pi n^2/q)
                           + eps (q/pi n^2)^{(1-s)/2} Gamma((1-s)/2, pi n^2/q) ]
self-checked at s = 2 against the plain convergent series.
"""
import math

import numpy as np
import mpmath as mp

mp.mp.dps = 25
Q = 10009
EPS = +1

qr = np.zeros(Q, dtype=np.int8)
qr[(np.arange(1, Q, dtype=np.int64) ** 2) % Q] = 1
def chi(n):
    r = n % Q
    return np.where(r == 0, 0.0, np.where(qr[r] == 1, 1.0, -1.0))


def Lam_exact(t):
    s = mp.mpf("0.5") + 1j * mp.mpf(float(t))
    tot = mp.mpc(0)
    nmax = int(math.sqrt(45 * Q / math.pi)) + 1
    cs = chi(np.arange(0, nmax + 1))
    for n in range(1, nmax + 1):
        if cs[n] == 0.0:
            continue
        x = math.pi * n * n / Q
        r = mp.mpf(Q / (math.pi * n * n))
        tot += float(cs[n]) * (r ** (s / 2) * mp.gammainc(s / 2, x, mp.inf)
                               + EPS * r ** ((1 - s) / 2) * mp.gammainc((1 - s) / 2, x, mp.inf))
    return complex(tot)


# self-check of the kernel formula at s=2 (plain series converges absolutely there)
s2 = mp.mpf(2)
tot = mp.mpc(0)
nmax = int(math.sqrt(45 * Q / math.pi)) + 1
cs = chi(np.arange(0, nmax + 1))
for n in range(1, nmax + 1):
    if cs[n] == 0.0:
        continue
    x = math.pi * n * n / Q
    r = mp.mpf(Q / (math.pi * n * n))
    tot += float(cs[n]) * (r ** (s2 / 2) * mp.gammainc(s2 / 2, x, mp.inf)
                           + EPS * r ** ((1 - s2) / 2) * mp.gammainc((1 - s2) / 2, x, mp.inf))
nn = np.arange(1, 2_000_001, dtype=np.float64)
L2 = float(np.sum(chi(np.arange(1, 2_000_001)) / nn ** 2))
lam2_direct = (Q / math.pi) * math.gamma(1.0) * L2
print(f"[kernel self-check s=2] two-strand = {complex(tot).real:.10f} vs direct = {lam2_direct:.10f}"
      f"  (rel diff {abs(complex(tot).real - lam2_direct)/abs(lam2_direct):.1e})")

T0 = 0.37                       # off-hinge sample too, in case L(1/2, chi) is small
ex0, exT = Lam_exact(0.0), Lam_exact(T0)
scale = max(abs(ex0), abs(exT))
print(f"exact: Lambda(1/2) = {ex0.real:.8f}, |Lambda(1/2+{T0}i)| = {abs(exT):.8f}  (scale {scale:.4f})")
print()
print(f"single-strand (hinge-outward) fiber error vs bank size, chi mod {Q} (n* = {math.sqrt(Q/math.pi):.1f}):")
pref0 = (Q / math.pi) ** 0.25 * math.gamma(0.25)
for NB in (50_000, 100_000, 200_000, 400_000, 800_000):
    n = np.arange(1, NB + 1, dtype=np.float64)
    c = chi(np.arange(1, NB + 1))
    u = n / NB
    w = np.where(u < 1.0, np.exp(1.0 - 1.0 / np.clip(1.0 - u * u, 1e-300, None)), 0.0)
    amp = c * w * n ** (-0.5)
    F0 = float(np.sum(amp))
    lg = complex(mp.loggamma((mp.mpf("0.25")) + 1j * mp.mpf(T0) / 2))
    prefT = complex((Q / math.pi) ** (0.25 + 0.5j * T0)) * complex(np.exp(lg.real + 1j * lg.imag))
    FT = complex(np.sum(amp * np.exp(-1j * T0 * np.log(n))))
    e0 = abs(pref0 * F0 - ex0) / scale
    eT = abs(prefT * FT - exT) / scale
    print(f"  NB = {NB:>7}  (NB/n* = {NB/math.sqrt(Q/math.pi):>6.0f})   err(hinge) = {e0:.2e}   err(t={T0}) = {eT:.2e}")

print()
print("elliptic comparison (5077.a, n* = 11.3, leading-jet c3 error vs bank — measured earlier):")
print("  NB =  18000  err = 0.70;  NB = 40000  err = 0.27;  NB = 100000  err = 0.36   << SATURATED")
print()
print("Reading: if the character errors DECAY with NB while the elliptic error saturates at a")
print("bank-independent floor, the single hinge-outward strand is a convergent representation")
print("for degree 1 but structurally invalid for degree 2 -- the elliptic fiber exists at the")
print("hinge only as the two endings-inward strands meeting at the Fricke midpoint (Sam's")
print("opposite-topology claim, sharpened to a degree statement).")
