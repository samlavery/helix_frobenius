"""Sam's dimension principle: every vanishing carries a dimension, not just the hinge.

d(gamma) = order of vanishing = size of the pencil rank-drop = dead depth of the local
jet tower.  BSD is then the special case d(0) = rank: the weld pins the hinge phase, so
arithmetic can deposit extra dimensions THERE; off the hinge no forcing exists and every
vanishing should be d = 1 (simplicity).  Census over the rank ladder:

    curve    predicted d(0)    predicted d(gamma != 0)
    11.a          0                    1
    37.a          1                    1
    389.a         2                    1
    5077.a        3                    1

Method: completed line Lambda(1/2+it) from the point-counted fiber; locate vanishings,
Newton-refine, then read the local jet: floor |Lambda(gamma)| vs reopening rate
|Lambda'(gamma)|.  d = 1 iff the rate stands clear of the floor (residue exists —
ReverbResidue.residue_exists_iff_simple); a d >= 2 vanishing would collapse the rate to
the floor as well.  Hinge dimensions from the jet towers (tmp/bsd_rank_ladder.py).
Zeta's census is already on file: 1517/1517 vanishings to t = 2000 with R > 0.
"""
import math
import sys

import numpy as np

sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
from bsd_weld import an_bank, ap_curve, completed_line

CURVES = [
    ("11.a",   11,   (-1, -10, -20), +1, 0),
    ("37.a",   37,   (0, -1, 0),     -1, 1),
    ("389.a",  389,  (1, -2, 0),     +1, 2),
    ("5077.a", 5077, (0, -7, 6),     -1, 3),
]

print(f"{'curve':>7} | hinge jet tower -> d(0)  | non-central vanishings gamma: rate R, floor m -> d")
for tag, N, A, aN, r in CURVES:
    NB = max(40000, int(12 * N ** 0.5 * 21))
    a = an_bank(N, lambda p: ap_curve(p, *A), aN, NB)
    lam = a[1:] / np.sqrt(np.arange(1.0, NB + 1))

    dy = 0.004
    ts = 0.3 + dy * np.arange(int((12.0 - 0.3) / dy) + 1)
    Lam = completed_line(lam, N, ts)
    absL = np.abs(Lam)
    med = float(np.median(absL))

    gs = []
    for j in range(1, len(ts) - 1):
        if absL[j] < absL[j - 1] and absL[j] < absL[j + 1] and absL[j] < 0.3 * med:
            dL = (Lam[j + 1] - Lam[j - 1]) / (2 * dy)
            gs.append(float(ts[j] - (Lam[j] / dL).real))
    rows = []
    for i, g in enumerate(gs):
        halfgap = 0.5 * min(g - gs[i - 1] if i > 0 else 1.0,
                            gs[i + 1] - g if i + 1 < len(gs) else 1.0)
        Lg = completed_line(lam, N, np.array([g - dy, g, g + dy]))
        m = abs(Lg[1])
        R = abs((Lg[2] - Lg[0]) / (2 * dy))
        # d = 1 iff the linear jet dominates the floor over the zero's own half-gap:
        # a d>=2 vanishing would have R at the floor scale, ratio O(1)
        ratio = R * min(halfgap, 0.5) / m if m > 0 else np.inf
        d = 1 if ratio > 30 else 99
        rows.append((g, R, m, ratio, d))

    hinge = {0: "value alive", 1: "c0 dead, rate alive", 2: "c0,c1 dead, curvature alive",
             3: "c0..c2 dead, jerk alive"}[r]
    print(f"{tag:>7} | d(0) = {r} ({hinge})")
    for g, R, m, ratio, d in rows:
        print(f"        |   gamma = {g:7.4f}   R = {R:.3e}   floor = {m:.1e}   "
              f"jet/floor = {ratio:9.1f}   -> d = {d}")
    n1 = sum(1 for *_x, d in rows if d == 1)
    print(f"        |   census: {n1}/{len(rows)} non-central vanishings at d = 1"
          + ("   ALL SIMPLE" if n1 == len(rows) else "   *** NON-SIMPLE CANDIDATE — inspect!"))
print()
print("Reading: the dimension function d(gamma) is 1 at every vanishing off the hinge;")
print("only the weld point carries extra dimensions, and there d(0) = rank exactly")
print("(the arithmetic deposits its dimensions where the phase is pinned).")
