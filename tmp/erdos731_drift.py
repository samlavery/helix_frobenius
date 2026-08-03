"""Drift check: is log L(n) ~ c * sqrt(log n) (balanced-prime channel heuristic,
c ~ sqrt(log 2) ~ 0.8326) rather than (1/2) log n?  Per-dyadic statistics."""

import numpy as np
from sympy import primerange
from math import log, sqrt

N = 400_000
ns = np.arange(N + 1)
primes = np.array(list(primerange(2, 1400)))

logL = np.full(N + 1, np.inf)
via_bal = np.zeros(N + 1, dtype=bool)
for p in primes:
    q = ns.copy()
    carry = np.zeros(N + 1, dtype=np.int64)
    v = np.zeros(N + 1, dtype=np.int64)
    while q.max() > 0 or carry.max() > 0:
        d = q % p
        c2 = (2 * d + carry) >= p
        v += c2
        carry = c2.astype(np.int64)
        q //= p
    cand = (v + 1) * log(p)
    upd = cand < logL
    logL[upd] = cand[upd]
    via_bal[upd] = (v[upd] == 0)

print(" range              mean exp   mean logL/sqrt(ln n)   bal-channel share")
for a in [1000, 4000, 16000, 64000, 256000]:
    b = min(2 * a, N)
    sl = slice(a, b)
    lg = np.log(ns[sl])
    e = (logL[sl] / lg).mean()
    c = (logL[sl] / np.sqrt(lg)).mean()
    print(f" [{a:7d},{b:7d})   {e:.4f}     {c:.4f}                 {via_bal[sl].mean():.4f}")
print(f"\nsqrt(log 2) = {sqrt(log(2)):.4f}")
