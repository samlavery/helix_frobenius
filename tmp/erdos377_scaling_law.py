"""Equal-volume scaling law: max balanced mass in fixed-length windows at growing height.
Budget law prediction: M*(N, L) depends on L only — flat in N.  Growth in N => disproof lead."""
import numpy as np

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

P = [p for p in primes_to(3163) if p != 2]
L = 3_000_000
print(f"window length L = {L:.0e}, rails 3..3163 (depth >= 2)")
for N in [10**7, 10**9, 10**11, 10**13, 10**15, 10**17, 8 * 10**18]:
    lo = N
    n = np.arange(lo, lo + L, dtype=np.int64)
    M = np.zeros(L)
    for p in P:
        if p * p > lo + L - 1: continue
        half = (p - 1) // 2
        bal = np.ones(L, dtype=bool)
        q = n.copy()
        while q.max() > 0:
            bal &= (q % p) <= half
            q //= p
        M += np.where(bal, 1.0 / p, 0.0)
    i = int(np.argmax(M))
    print(f"  N = {N:8.0e}:  max M = {M[i]:.4f}  at n = {int(n[i])}"
          f"   (mean {M.mean():.4f})")
