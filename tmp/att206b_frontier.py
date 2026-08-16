"""att206b: the resolution frontier -- first inertia event of the pole-subtracted
pencil as a function of (n, s0). At low n the smooth part dominates (att206: (0,n)
throughout); prime atoms enter the density with NEGATIVE sign, so at the n where
they resolve the definiteness must break. Locate it."""
import numpy as np
from mpmath import mp, zeta, diff, mpf

mp.dps = 50
f_reg = lambda s: -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)

jc = {}
def jets(s0, K):
    key = (round(s0, 6))
    have = jc.get(key, [])
    while len(have) <= K:
        k = len(have)
        have.append(float(((-1) ** k) * diff(f_reg, mpf(s0), k)))
        jc[key] = have
    return np.array(have[:K + 1])

print(" n \\ s0 :   1.30        0.999       0.80        0.60")
for n in [4, 6, 8, 10]:
    row = []
    for s0 in [1.3, 0.999, 0.8, 0.6]:
        m = jets(s0, 2 * n)
        G0 = np.array([[m[j + k] for k in range(n)] for j in range(n)])
        ev = np.linalg.eigvalsh(G0)
        npos = int(np.sum(ev > 1e-13 * np.max(np.abs(ev))))
        nneg = int(np.sum(ev < -1e-13 * np.max(np.abs(ev))))
        row.append("(%d,%d)" % (npos, nneg))
    print("  %2d    :   %-10s  %-10s  %-10s  %-10s" % (n, *row))
