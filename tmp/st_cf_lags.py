"""CF-lag test: quasi-periodic (frame-native) observable for the S(t) registration frame.

PRE-REGISTERED (2026-07-14): the unit-1 lattice nearly registers with the Gram/pi lattice at
Gram-index lags equal to the denominators of pi's continued-fraction convergents
(pi ~ 22/7, 333/106, 355/113 => lags {7, 106, 113}).  If the arithmetic defect sequence couples
to the unit-chart registration, its autocorrelation should be elevated at exactly those lags.
Statistic: mean |autocorr| at {7,106,113} vs (a) the percentile among all lags 1..300, and
(b) circular-shift null of the 3-lag mean.  A null bounds unit-lattice coupling in the Gram
chart; the deterministic-layer theorems (RegistrationGaps.lean) are untouched either way.
DISCUSSION GATE (Sam's protocol) before any recorded verdict.
"""

import bisect
import random

ZC = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
GC = "/Users/samuellavery/work/helix_frobenius/tmp/gram_cache.txt"
gam = [float(x) for x in open(ZC).read().split()]
gz = [float(x) for x in open(GC).read().split()]
g = gz[0::2]
N = len(g) - 1
Ncount = [bisect.bisect_right(gam, gp) for gp in g]
D = [Ncount[n] - (n + 1) for n in range(N + 1)]
mu = sum(D) / len(D)
Dc = [d - mu for d in D]
var = sum(d * d for d in Dc) / len(Dc)

def autocorr(seq, lag):
    L = len(seq)
    s = sum(seq[i] * seq[(i + lag) % L] for i in range(L))
    return s / (L * var)

MAXLAG = 300
rho = [autocorr(Dc, l) for l in range(1, MAXLAG + 1)]
CF = [7, 106, 113]
stat = sum(abs(rho[l - 1]) for l in CF) / 3
allabs = sorted(abs(r) for r in rho)
pct = sum(1 for r in allabs if r <= stat) / len(allabs)

# circular-shift null for the 3-lag mean: shift the lag TEMPLATE, i.e. compare against
# mean |rho| over random 3-lag sets drawn without the CF lags
random.seed(777)
null_stats = []
pool = [l for l in range(1, MAXLAG + 1) if l not in CF]
for _ in range(4000):
    pick = random.sample(pool, 3)
    null_stats.append(sum(abs(rho[l - 1]) for l in pick) / 3)
null_stats.sort()
p_null = (1 + sum(1 for s in null_stats if s >= stat)) / (1 + len(null_stats))

lines = []
lines.append("== CF-lag test (N=%d gram ticks, defect autocorrelation) ==" % N)
lines.append("CF lags {7,106,113}: |rho| = %.4f, %.4f, %.4f"
             % (abs(rho[6]), abs(rho[105]), abs(rho[112])))
lines.append("3-lag mean |rho|: %.4f   percentile among lags 1..%d: %.3f" % (stat, MAXLAG, pct))
lines.append("random-3-lag null p: %.4f  (4000 draws)" % p_null)
top = sorted(range(1, MAXLAG + 1), key=lambda l: -abs(rho[l - 1]))[:10]
lines.append("top-10 |rho| lags: " + ", ".join("%d(%.3f)" % (l, rho[l - 1]) for l in top))
lines.append("nearby controls: lag6 %.4f  lag8 %.4f  lag105 %.4f  lag107 %.4f  lag112 %.4f  lag114 %.4f"
             % (rho[5], rho[7], rho[104], rho[106], rho[111], rho[113]))
out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/st_cf_lags_results.txt", "w").write(out + "\n")
