"""Test 4 (redesigned): zeros' phases measured IN the carrier's own cells.

DESIGN FIX (2026-07-14, Sam's diagnosis: test-design issue — confirmed): tests 1-3 sampled the
census only AT Gram points (theta = n*pi), i.e., at the chart's own ticks, where every sample sits
at a carrier-cell BOUNDARY: the pi/3 subdivision (3 carrier arcs between consecutive Gram ticks)
was never observed, and the unit-1 ledger was never computed.  Chart-tick sampling can only see
chart structure — the previous nulls are statements about the aliased observable, not the carrier.

THIS TEST samples the carrier coordinate directly: for each zero gamma_j, the position
x_j = frac(theta(gamma_j)/pi) within its pi phase-cell, and the pi/3 subdivision (thirds of the
cell = carrier arcs).  PRE-REGISTERED statistic: density kinks at the carrier subdivision points
x = 1/3, 2/3 versus matched control breakpoints (0.2, 0.4, 0.6, 0.8) — a kink at exactly the
carrier's subdivision, beyond controls, is carrier structure in zero placement; smooth passage is
the null.  DISCUSSION GATE before any recorded verdict (Sam's protocol).
"""

from mpmath import mp, siegeltheta, pi as mppi
import math

mp.dps = 15
ZC = "/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"
gam = [float(x) for x in open(ZC).read().split()]
print("zeros: %d  (heights %.2f .. %.2f)" % (len(gam), gam[0], gam[-1]))

xs = []
for j, gv in enumerate(gam):
    th = float(siegeltheta(gv))
    x = (th / math.pi) % 1.0
    xs.append(x)
    if (j + 1) % 1000 == 0:
        print("  theta at zero %d" % (j + 1))

n = len(xs)

def kink(xlist, b, w=0.05):
    lo = sum(1 for x in xlist if b - w <= x < b)
    hi = sum(1 for x in xlist if b <= x < b + w)
    return (hi - lo) / max(1, hi + lo)

CARRIER = [1.0 / 3.0, 2.0 / 3.0]
CONTROL = [0.2, 0.4, 0.6, 0.8]
k_car = [kink(xs, b) for b in CARRIER]
k_con = [kink(xs, b) for b in CONTROL]

lines = []
lines.append("== test 4: zero phases in the carrier cell (n=%d) ==" % n)
hist = [0] * 20
for x in xs:
    hist[min(19, int(20 * x))] += 1
lines.append("x = frac(theta/pi) histogram (20 bins):")
lines.append("  " + " ".join("%4d" % h for h in hist))
mean_x = sum(xs) / n
lines.append("mean x: %.4f   (S(gamma) mod 1 concentration: classical expectation near 0/1 wrap)")
lines.append("thirds occupancy (carrier arcs within the cell): %d / %d / %d"
             % (sum(1 for x in xs if x < 1/3), sum(1 for x in xs if 1/3 <= x < 2/3),
                sum(1 for x in xs if x >= 2/3)))
lines.append("kink at carrier breakpoints 1/3, 2/3: %.4f, %.4f" % (k_car[0], k_car[1]))
lines.append("kink at controls 0.2,0.4,0.6,0.8: " + ", ".join("%.4f" % k for k in k_con))
mean_car = sum(abs(k) for k in k_car) / 2
mean_con = sum(abs(k) for k in k_con) / 4
lines.append("mean |kink|: carrier %.4f  vs control %.4f" % (mean_car, mean_con))
lines.append("")
lines.append("mean x fills in: %.4f" % mean_x)
lines.append("VERDICT INPUTS (gate applies): carrier-vs-control kink ratio %.2f"
             % (mean_car / max(1e-9, mean_con)))
out = "\n".join(lines)
print(out)
open("/Users/samuellavery/work/helix_frobenius/tmp/st_cell_phase_results.txt", "w").write(out + "\n")
