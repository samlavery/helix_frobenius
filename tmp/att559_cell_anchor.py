# CARRIER-SCALE CONTOUR ANCHORS: does the pi/3 cell give a lower bound the flat one doesn't?
# After dividing the Gamma-envelope out, min|Xi| on the contour = |Z(t)| (Riemann-Siegel Z).
# Cell anchors: theta(t) = k*pi/3   (mu6 cells, house scale)
# Flat anchors:  theta(t) = k*pi    (Gram points, unit/classical scale)
# PRE-REGISTERED: for each mu6 cycle (6 consecutive pi/3 cells) record max|Z|; if that
# max is bounded below by c>0 uniformly in height, the cell anchoring supplies the needed
# contour lower bound.  Compare with per-Gram-pair max|Z| (flat).  Also record the WORST
# single-cell |Z| (what you'd get with a bad anchor choice).
from mpmath import mp, mpf, siegelz, siegeltheta, findroot, pi
mp.dps = 15
def t_of_theta(target, t0):
    return findroot(lambda t: siegeltheta(t) - target, t0)
print(f"{'height':>9} {'min over cycles of max|Z| (pi/3)':>32} {'same (Gram)':>13} {'worst single cell':>18}")
for T0 in [100, 1000, 10000, 100000]:
    th0 = siegeltheta(mpf(T0))
    k0 = int(th0/(pi/3)) + 1
    cellmax, grammax, worst = [], [], mpf('inf')
    ts = []
    for k in range(k0, k0 + 72):            # 12 mu6 cycles
        t = t_of_theta(k*pi/3, mpf(T0) + (k-k0)*mpf(T0)/500 + 1)
        z = abs(siegelz(t)); ts.append((k, t, z))
        worst = min(worst, z)
    for c in range(12):
        cyc = [ts[6*c+j][2] for j in range(6)]
        cellmax.append(max(cyc))
        gram = [ts[6*c+j][2] for j in range(6) if ts[6*c+j][0] % 3 == 0]   # theta = k*pi
        if gram: grammax.append(max(gram))
    print(f"{T0:>9} {float(min(cellmax)):>32.4f} {float(min(grammax)):>13.4f} {float(worst):>18.6f}")
