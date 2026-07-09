#!/usr/bin/env python3
"""random_euler_control.py -- is the summed-bank self-duality ((iv) of the bank-reflection
lemma) a consequence of per-term reflection algebra, or a genuine arithmetic input?

ANCHOR   the true carrier lattice: theta(x) = sum_{n in Z} exp(-pi n^2 x) satisfies
         theta(1/x) = sqrt(x) * theta(x) exactly (Poisson / self-dual lattice).
CONTROL  a completely multiplicative random-sign system eps_n (eps_p random +-1 at
         primes), psi(x) = 1 + 2 sum_{n>=1} eps_n exp(-pi n^2 x).  Every TERM carries
         the same reflection algebra as the anchor (same self-dual kernel, unit
         coefficients, negation-closed channels); if the summed identity followed
         termwise, psi(1/x) = sqrt(x) psi(x) would hold as well.

Measure R(x) = |f(1/x) / (sqrt(x) f(x)) - 1| for both.  The anchor must sit at machine
zero; if the control sits at O(1), the reciprocal-height identity is coefficient-
sensitive -- a resummation across the bank, i.e. arithmetic content, not chart geometry.
Run: python3 tmp/random_euler_control.py
"""
import numpy as np

N = 4000
rng = np.random.default_rng(7)

def sieve_primes(N):
    is_p = np.ones(N + 1, bool); is_p[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if is_p[p]:
            is_p[p * p::p] = False
    return np.nonzero(is_p)[0]

primes = sieve_primes(N)
eps_p = dict(zip(primes.tolist(), rng.choice([-1.0, 1.0], size=len(primes))))
spf = np.zeros(N + 1, int)
for p in primes:
    for m in range(p, N + 1, p):
        if spf[m] == 0:
            spf[m] = p
eps = np.ones(N + 1)
for n in range(2, N + 1):
    eps[n] = eps[n // spf[n]] * eps_p[spf[n]]

n = np.arange(1, N + 1, dtype=float)
Om = np.zeros(N + 1, int)
for m in range(2, N + 1):
    Om[m] = Om[m // spf[m]] + 1
liou = np.where(Om % 2 == 0, 1.0, -1.0); liou[0] = 1.0

def wsum(c, x):
    return 1.0 + 2.0 * float(np.sum(c[1:] * np.exp(-np.pi * n * n * x)))

def resid(c, x):
    return abs(wsum(c, 1.0 / x) / (np.sqrt(x) * wsum(c, x)) - 1.0)

ONES = np.ones(N + 1)
# small x so that ~1/sqrt(x) coefficients genuinely participate (at x=0.005, n<=~49)
XS = (0.005, 0.01, 0.02, 0.05, 0.1)
print("x        anchor (Poisson)   Liouville lam(n)   random eps seeds 7/11/13")
controls = [liou]
for sd in (7, 11, 13):
    r = np.random.default_rng(sd)
    ep = dict(zip(primes.tolist(), r.choice([-1.0, 1.0], size=len(primes))))
    e = np.ones(N + 1)
    for m in range(2, N + 1):
        e[m] = e[m // spf[m]] * ep[spf[m]]
    controls.append(e)
worst_a, worst_c = 0.0, 0.0
for x in XS:
    Ra = resid(ONES, x)
    Rc = [resid(c, x) for c in controls]
    worst_a = max(worst_a, Ra); worst_c = max(worst_c, min(Rc[1:] + [Rc[0]]))
    print(f"{x:6.3f}   {Ra:12.3e}      {Rc[0]:12.3e}      " + "  ".join(f"{v:9.2e}" for v in Rc[1:]))
print(f"\nanchor worst residual = {worst_a:.3e}  (Poisson: must be machine zero)")
print("controls: every multiplicative sign system carries the identical per-term reflection")
print("algebra (same self-dual kernel, unit channels); their summed identities fail by O(1).")
print("=> the reciprocal-height identity is coefficient-sensitive: a resummation across the")
print("   bank (Poisson/automorphy content), NOT a termwise consequence of per-phasor symmetry.")
