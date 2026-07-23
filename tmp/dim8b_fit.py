"""Dim-8 re-roll verdict: node-corrected Prym char poly at p = 7.

C'-corrections: +2 at every k (FE-EXACT, established).  C-corrections: the two
missing C'-points per level each carry n_t: clean node (x=2 mod 7): y = 5, cube in
F_{7^k} iff 3 | k  =>  n_t = 3*[3|k]; degenerate node (x=4): hypothesis space.
Scan c_k(C) = u*[3|k] + v*[6|k] + w over small grids; filter by e-integrality and
purity of the FE-completed degree-16 P_Prym.  Purity of 16 roots is a sharp filter.
"""
import cmath
import sys
from fractions import Fraction

import numpy as np

p = 7
# raw counts from tmp/dim8b_lpoly.log (k = 1..8): fill k=8 from the log when done
NCp_raw = [15, 77, 309, 2333, 16860, 117755, 821724, None]
NC_raw = [12, 84, 387, 2196, 16467, 119391, 821448, None]
if len(sys.argv) == 3:
    NCp_raw[7] = int(sys.argv[1])
    NC_raw[7] = int(sys.argv[2])
assert None not in NCp_raw, "pass k=8 counts: python3 dim8b_fit.py <#C'> <#C>"


def newton_e(t, g):
    e = [Fraction(1)] + [Fraction(0)] * g
    for k in range(1, g + 1):
        acc = Fraction(0)
        for i in range(1, k + 1):
            acc += (-1) ** (i - 1) * e[k - i] * t[i - 1]
        e[k] = acc / k
    return e


def fe_poly(s, g):
    e = newton_e(s, g)
    if any(x.denominator != 1 for x in e):
        return None
    c = [(-1) ** j * e[j] for j in range(g + 1)] + [0] * g
    for j in range(g):
        c[2 * g - j] = p ** (g - j) * c[j]
    return [int(x) for x in c]


def purity(coeffs):
    r = np.roots(list(reversed(coeffs)))
    return max(abs(abs(z) ** 2 * p - 1) for z in r)


results = []
for u in (0, 3, 6):
    for v in (0, 3, -3):
        for w in (0, 1, 2, 3):
            corr = [u * (1 if (k % 3 == 0) else 0) + v * (1 if (k % 6 == 0) else 0)
                    + w for k in range(1, 9)]
            s = [(NCp_raw[i] + 2) - (NC_raw[i] + corr[i]) for i in range(8)]
            co = fe_poly(s, 8)
            if co is None:
                continue
            pur = purity(co)
            results.append((pur, (u, v, w), co, s))

results.sort()
print("top hypotheses by purity defect:")
for pur, (u, v, w), co, s in results[:6]:
    print(f"  c_k(C) = {u}*[3|k] + {v}*[6|k] + {w}: purity defect {pur:.3e}  "
          f"s = {s}")
best = results[0]
if best[0] < 1e-6:
    pur, (u, v, w), co, s = best
    print("\n*** PURITY-EXACT correction found:", (u, v, w))
    print("P_Prym coefficients (ascending):", co)
    others = [r for r in results[1:] if r[0] < 1e-6]
    print("uniqueness:", "UNIQUE" if not others else
          f"AMBIGUOUS ({len(others)} others) -- need 13^8 counter")
else:
    print("\nno purity-exact hypothesis -- widen space or build the 13^8 counter")
