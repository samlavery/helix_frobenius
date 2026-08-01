"""Pinning signature: in defect cells, event clock-phases must compensate to keep the
clock residue capped.  Quantify exactly how pinned they are.

  s=+1, k=1:  A~ = 3/2 - tau      -> cap |A~| <= c forces tau >= 3/2 - c
  s=-1, k=2:  A~ = 1/2 - t1 - t2  -> cap forces t1 + t2 <= 1/2 + c
  s= 0, k=2:  A~ = 3/2 - t1 - t2  -> forces t1 + t2 >= 3/2 - c   (pair late)
  s= 0, k=0:  A~ = -1/2 exactly (no freedom) -- the k=0 cell is the floor of the cap
"""

import bisect
import numpy as np
from scipy.special import loggamma

ZC = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GC = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"
zeros = [float(x) for x in open(ZC).read().split()]
gram = [float(x) for x in open(GC).read().split()][0::2]

def theta(t):
    t = np.asarray(t, dtype=float)
    return np.imag(loggamma(0.25 + 0.5j * t)) - 0.5 * t * np.log(np.pi)

M = max(n for n in range(len(gram) - 1) if gram[n + 1] <= zeros[-1] - 5.0)
zarr = np.array(zeros)
zin = zarr[(zarr > gram[0]) & (zarr <= gram[M])]
ph = theta(zin) / np.pi
cell = np.floor(ph).astype(int)
tau = ph - cell
s = np.array([bisect.bisect_right(zeros, gram[n]) - 1 - n for n in range(M + 1)])
k = np.bincount(cell, minlength=M)
sum1mtau = np.zeros(M)
np.add.at(sum1mtau, cell, 1.0 - tau)
At = s[:-1] + sum1mtau - 0.5

def taus_of(n):
    return np.sort(tau[cell == n])

print("type (s,k) census and pinning:")
for sv, kv in [(1, 0), (1, 1), (0, 1), (0, 2), (-1, 1), (-1, 2), (-1, 3), (0, 0)]:
    m = (s[:-1] == sv) & (k == kv)
    cnt = int(m.sum())
    if cnt == 0:
        print("  (s=%+d,k=%d): 0 cells" % (sv, kv))
        continue
    a = At[m]
    print("  (s=%+d,k=%d): %4d cells   A~ in [%+.4f, %+.4f]  mean %+.4f" %
          (sv, kv, cnt, a.min(), a.max(), a.mean()))
    if kv >= 1:
        tsum = np.array([taus_of(n).sum() for n in np.nonzero(m)[0]])
        print("      sum tau: [%.4f, %.4f]  mean %.4f  (free range [0,%d])" %
              (tsum.min(), tsum.max(), tsum.mean(), kv))

# the cap: distribution of |A~| exceedances over 1/2
exc = np.abs(At) - 0.5
print("\ncells with |A~| > 1/2: %d / %d  (%.4f)" % ((exc > 0).sum(), M, (exc > 0).mean()))
print("exceedance quantiles (over cap cells): 50%%: %.4f  90%%: %.4f  max: %.4f"
      % tuple(np.percentile(exc[exc > 0], [50, 90]).tolist() + [exc.max()]))
# where do exceedances live
for sv, kv in [(1, 1), (-1, 2), (0, 1), (0, 2), (-1, 1)]:
    m = (s[:-1] == sv) & (k == kv) & (exc > 0)
    print("  exceedances at (s=%+d,k=%d): %d" % (sv, kv, int(m.sum())))

# neighbour compensation: A~ correlation with next cell
c0 = np.corrcoef(At[:-1], At[1:])[0, 1]
c1 = np.corrcoef(At[:-2], At[2:])[0, 1]
print("\nlag correlations of A~: lag1 %+.4f  lag2 %+.4f" % (c0, c1))
# defect-cell + successor pair sums (does the NEXT cell absorb the residue?)
for sv, kv in [(1, 0), (-1, 2), (1, 1)]:
    m = np.nonzero((s[:-2] == sv) & (k[:-1] == kv))[0]
    if m.size:
        pair = At[m] + At[m + 1]
        print("  pair-sum (cell+next) at (s=%+d,k=%d): mean %+.4f  RMS %.4f  vs cell RMS %.4f"
              % (sv, kv, pair.mean(), np.sqrt((pair**2).mean()), np.sqrt((At[m]**2).mean())))
print("\ndone.")
