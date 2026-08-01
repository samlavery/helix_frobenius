"""Erdos #377 house probe: the multi-rail digit-clock frame.

f(n) = sum of 1/p over primes p <= n with p not dividing C(2n,n)
     = sum of 1/p over rails where n is p-BALANCED (every base-p digit < p/2,
       i.e. the p-clock reading stays in the lower half-cell at every position
       — Kummer: no carries doubling n).

Question (EGRS 1975): is f(n) uniformly bounded?  Known: mean gamma0, a.a.
gamma0 + o(1), max <= c loglog n (c < 1).  House frame: rails at multiplicatively
independent rates should decorrelate; the enemy is cross-rail alignment.

Measured here:
  1. f(n) for all n <= N: max, champions, envelope vs loglog n, mean vs gamma0
  2. champions' rail structure: which primes are balanced (small-prime conspiracies?)
  3. cross-rail alignment ledger: P(bal_p & bal_q) / (P(bal_p) P(bal_q)) for small
     prime pairs — the correlation that must stay tame for boundedness
  4. the k-band decomposition: contribution to f from p in (n^{1/(k+1)}, n^{1/k}]
     vs the 2^{-k}/k heuristic budget
"""

import numpy as np
from sympy import primerange
from math import log

N = 200_000
ns = np.arange(N + 1)

primes = np.array(list(primerange(2, N + 1)))
print(f"N = {N}, primes up to N: {len(primes)}")

# balanced mask per prime, vectorized digit extraction
f = np.zeros(N + 1)
bal_small = {}   # keep masks for small primes for the alignment ledger
SMALL = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
for p in primes:
    m = np.ones(N + 1, dtype=bool)
    q = ns.copy()
    half = (p - 1) // 2  # digit d balanced iff d <= (p-1)/2 i.e. d < p/2
    while q.max() > 0:
        m &= (q % p) <= half
        q //= p
    m &= ns >= p          # sum restricted to p <= n
    f += m / p
    if p in SMALL:
        bal_small[p] = m.copy()

f[0] = f[1] = 0.0

# 1. envelope and mean
gamma0 = sum(log(k) / 2**k for k in range(2, 200))
print(f"\ngamma0 = {gamma0:.6f}   empirical mean f(n), n in [N/2, N]: "
      f"{f[N//2:].mean():.6f}")
kmax = int(np.argmax(f))
print(f"max f(n) = {f.max():.5f} at n = {kmax}")
print(f"loglog N = {log(log(N)):.4f};  max f / loglog n = "
      f"{f.max()/log(log(kmax)):.4f}  (EGRS: c < 1)")
# running record envelope
rec_n, rec_f = [], []
best = -1
for n in range(2, N + 1):
    if f[n] > best:
        best = f[n]; rec_n.append(n); rec_f.append(best)
print("record-setters (last 12):")
for n, v in list(zip(rec_n, rec_f))[-12:]:
    print(f"  n = {n:7d}   f = {v:.5f}   f/loglog n = {v/log(log(n)):.4f}")

# 2. champions' rail structure
def balanced_primes(n, upto=60):
    out = []
    for p in primerange(2, min(upto, n) + 1):
        q, ok = n, True
        while q > 0:
            if q % p > (p - 1) // 2: ok = False; break
            q //= p
        if ok: out.append(p)
    return out

print("\nchampions' small balanced rails (p <= 60):")
for n in rec_n[-6:]:
    print(f"  n = {n:7d}: {balanced_primes(n)}")

# 3. cross-rail alignment ledger (n in [1000, N] to avoid small-n artifacts)
lo = 1000
print("\ncross-rail alignment  r = P(bal_p & bal_q)/(P_p P_q)  (n >= 1000):")
Ps = {p: bal_small[p][lo:].mean() for p in SMALL if p in bal_small}
print("  marginals:", {p: round(Ps[p], 4) for p in list(Ps)[:8]})
hdr = "      " + "".join(f"{q:>7d}" for q in SMALL[:8])
print(hdr)
for i, p in enumerate(SMALL[:8]):
    row = f"  p={p:2d}"
    for q in SMALL[:8]:
        if q <= p:
            row += "       "
        else:
            joint = (bal_small[p][lo:] & bal_small[q][lo:]).mean()
            r = joint / (Ps[p] * Ps[q]) if Ps[p] * Ps[q] > 0 else float('nan')
            row += f"{r:7.3f}"
    print(row)

# 4. k-band decomposition at a few heights
print("\nk-band contributions (p in (n^{1/(k+1)}, n^{1/k}]) at n = argmax:")
n0 = kmax
contrib = {}
for p in primes[primes <= n0]:
    k = int(log(n0) / log(p))  # p^k <= n0 < p^{k+1}
    q, ok = n0, True
    while q > 0:
        if q % p > (p - 1) // 2: ok = False; break
        q //= p
    if ok:
        contrib[k] = contrib.get(k, 0.0) + 1.0 / p
for k in sorted(contrib):
    budget = log((k + 1) / k) if k >= 1 else float('inf')
    print(f"  k = {k:2d}: contribution {contrib[k]:.5f}   band 1/p-budget "
          f"{budget:.4f}   heuristic 2^-k * budget {budget * 2**-k:.5f}")
print("\ndone.")
