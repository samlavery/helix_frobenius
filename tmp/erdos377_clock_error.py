"""Is the theta-clock error real?  Top-J carry-free counts per band vs 2^-J density law.
Systematic bias => real analytic obstruction.  z ~ N(0,1) noise => chart artifact."""
import numpy as np

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0].astype(np.int64)

P = primes_to(1_200_000)
rng = np.random.default_rng(377)
NS = [int(x) for x in rng.integers(10**11, 10**12, 40)] + \
     [3**25, 5**17, 2 * 3**24, int(4.78e11)]

# per (k, J): accumulate actual and expected over all n
from collections import defaultdict
acc = defaultdict(lambda: [0.0, 0.0, 0.0])   # actual, expected, var

for n in NS:
    for k in range(2, 9):
        lo, hi = n ** (1.0 / (k + 1)), n ** (1.0 / k)
        band = P[(P > lo) & (P <= hi)]
        if len(band) < 30: continue
        for J in (1, 2, 3):
            if J > k: continue
            ok = np.ones(len(band), dtype=bool)
            for j in range(k - J + 1, k + 1):
                pj = band.astype(object) ** j          # exact big ints
                r = np.array([n % int(q) for q in pj], dtype=float)
                ok &= (2 * r < np.array([float(q) for q in pj]))
            a = int(ok.sum()); e = len(band) * 2.0 ** (-J)
            v = len(band) * 2.0 ** (-J) * (1 - 2.0 ** (-J))
            acc[(k, J)][0] += a; acc[(k, J)][1] += e; acc[(k, J)][2] += v

print(f"{'k':>2} {'J':>2} {'actual':>9} {'expected':>10} {'ratio':>7} {'z':>7}")
worst = 0.0
for (k, J), (a, e, v) in sorted(acc.items()):
    z = (a - e) / v ** 0.5
    worst = max(worst, abs(z))
    print(f"{k:>2} {J:>2} {a:>9.0f} {e:>10.1f} {a/e:>7.4f} {z:>+7.2f}")
print(f"\nmax |z| over all (k,J) cells: {worst:.2f}   "
      f"({len(NS)} values of n aggregated per cell)")
