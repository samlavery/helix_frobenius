"""Entropy-budget probe for the #377 atomic wall.

Claim under test (the MDHNT transversality law): for every n, the set of
small primes p on which n is p-balanced (all base-p digits < p/2, i.e.
p does not divide C(2n,n)) satisfies  sum beta_p <= 1 + o(1),
where beta_p = log(2p/(p+1))/log p is the per-rail freeze cost.

We count only decidedly-small rails: p^3 <= n (depth >= 3), the atomic side.
Readouts: max_n sum(beta_p), max_n sum(1/p), the champions, and the
{3,5,7} joint-freeze census.
"""
import numpy as np, math

N = 10**7
PMAX = 300

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

P = [p for p in primes_to(PMAX) if p >= 3]      # p=2 never balanced (v2 = s2(n))
beta = {p: math.log(2*p/(p+1)) / math.log(p) for p in P}

n = np.arange(N + 1, dtype=np.int64)
S_beta = np.zeros(N + 1)
S_recip = np.zeros(N + 1)
bal357 = np.ones(N + 1, dtype=bool)

for p in P:
    half = (p - 1) // 2
    bal = np.ones(N + 1, dtype=bool)
    q = n.copy()
    while q.max() > 0:
        bal &= (q % p) <= half
        q //= p
    bal[:p**3] = False                    # only count depth-3+ rails: p^3 <= n
    S_beta += np.where(bal, beta[p], 0.0)
    S_recip += np.where(bal, 1.0 / p, 0.0)
    if p in (3, 5, 7):
        b = np.ones(N + 1, dtype=bool)
        q = n.copy()
        while q.max() > 0:
            b &= (q % p) <= half
            q //= p
        bal357 &= b

lo = 10**4                                 # ignore tiny n (budget not yet binding)
sb, sr = S_beta[lo:], S_recip[lo:]
top = np.argsort(sb)[-12:][::-1] + lo
print(f"n in [{lo}, {N}], rails 3 <= p <= {PMAX} with p^3 <= n")
print(f"max sum(beta_p) = {sb.max():.4f}   (budget law predicts <= ~1)")
print(f"max sum(1/p)    = {sr.max():.4f}   (the atomic-budget readout)")
print(f"mean sum(beta_p) = {sb.mean():.4f}")
print("champions (n, sum_beta, sum_recip, balanced rails):")
for m in top:
    rails = []
    for p in P:
        if p**3 > m: continue
        q, ok = int(m), True
        while q:
            if q % p > (p - 1) // 2: ok = False; break
            q //= p
        if ok: rails.append(p)
    print(f"  n={m:9d}  Sb={S_beta[m]:.4f}  Sr={S_recip[m]:.4f}  rails={rails}")
b357 = np.nonzero(bal357[343:])[0] + 343   # 7^3=343 threshold irrelevant here: full balance
print(f"\nn balanced simultaneously in bases 3,5,7 (any n >= 343): count={len(b357)}")
print("  members:", list(b357[:25]), "..." if len(b357) > 25 else "")
print(f"  largest: {b357.max() if len(b357) else None}   "
      f"(beta_3+beta_5+beta_7 = {beta[3]+beta[5]+beta[7]:.4f})")
