"""Corrected clock-error test: actual primes in top-level gap sub-bands vs the EXACT
hyperbola-measure prediction (density 1/log t on each interval).  z ~ O(1) => no real error."""
import numpy as np
from math import log

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0].astype(np.int64)

P = primes_to(1_200_000)
rng = np.random.default_rng(377)
NS = [int(x) for x in rng.integers(10**11, 10**12, 40)] + [3**25, 5**17]

from collections import defaultdict
acc = defaultdict(lambda: [0.0, 0.0])

for n in NS:
    for k in range(2, 9):
        lo, hi = n ** (1.0 / (k + 1)), n ** (1.0 / k)
        band = P[(P > lo) & (P <= hi)]
        if len(band) < 30: continue
        # actual: top-level carry-free primes
        r = np.array([n % int(p) ** k for p in band], dtype=float)
        q = np.array([float(int(p) ** k) for p in band])
        actual = int((2 * r < q).sum())
        # exact prediction: sum over gap intervals (2n/(2m+1), n/m] in p^k-space,
        # mapped to p-space by k-th root, prime density 1/log p
        exp_cnt = 0.0
        m = max(1, int(n / hi ** k))
        while True:
            gap_lo, gap_hi = (2 * n / (2 * m + 1)) ** (1.0 / k), (n / m) ** (1.0 / k)
            a, b = max(gap_lo, lo), min(gap_hi, hi)
            if b > a and b > 2:
                exp_cnt += (b - a) / log((a + b) / 2)
            if gap_hi < lo: break
            m += 1
            if m > n / lo ** k + 2: break
        acc[(k,)][0] += actual; acc[(k,)][1] += exp_cnt

print(f"{'k':>2} {'actual':>9} {'hyperbola-pred':>14} {'ratio':>8} {'z':>7}")
for (k,), (a, e) in sorted(acc.items()):
    z = (a - e) / e ** 0.5
    print(f"{k:>2} {a:>9.0f} {e:>14.1f} {a/e:>8.4f} {z:>+7.2f}")
