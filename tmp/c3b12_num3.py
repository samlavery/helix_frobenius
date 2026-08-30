#!/usr/bin/env python3
"""C3 batch 12 numerics, part 3 — OpenAI adjudication items (2) and (5).

NONRIGOROUS CONTROLS ONLY.  Nothing here is a proof.

(2)  The batch-12 ledger proposed  0 <= c0*c2  (c0 = cosMom Phi, c2 = cosMom kM2)
     as a "smallest sub-fibre" of the u^2 sub-leaf.  It is FALSE.  In readout
     coordinates c0 = Xi(x) and c2 = -Xi''(x), so c0*c2 = -Xi(x)Xi''(x), and this
     changes sign.  Scanned here at high precision; failures recorded.

(5)  P4 reported min L1 = 1.246110e-194 at x = 300 computed at 30 dps.  A value of
     size 1e-194 evaluated at 30 significant digits is NOT certified by that
     computation: the working precision must exceed the dynamic range.  Recomputed
     here at 80 and 120 dps, and reported SCALE-NORMALISED (L1/Xi^2), which is the
     only figure with a meaningful number of correct digits.  Labelled
     NON-CERTIFIED regardless of agreement.
"""
import mpmath as mp


def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(x):
    return mp.re(2 * xi(mp.mpf(1) / 2 + 1j * mp.mpf(x)))


def moms(x):
    """c0 = Xi(x), s1 = -Xi'(x), c2 = -Xi''(x)  (the compiled dictionary)."""
    return Xi(x), -mp.diff(Xi, x, 1), -mp.diff(Xi, x, 2)


print("=" * 78)
print("(2)  IS  c0*c2 >= 0 ?   c0 = cosMom Phi x = Xi(x),  c2 = cosMom kM2 x = -Xi''(x)")
print("     the batch-12 ledger proposed this as an OPEN sub-fibre; it is FALSE")
print("=" * 78)
mp.mp.dps = 40
print("  spot check at the value the ledger's own P2 table already contained:")
c0, s1, c2 = moms(7.0)
print(f"    x=7:  c0 = {mp.nstr(c0, 12)}  c2 = {mp.nstr(c2, 12)}"
      f"  c0*c2 = {mp.nstr(c0 * c2, 12)}   <-- NEGATIVE")
print(f"          s1^2 = {mp.nstr(s1**2, 12)},  c0*c2 + s1^2 = {mp.nstr(c0*c2 + s1**2, 12)} > 0")
print()

neg = 0
tot = 0
first = []
runs = []
prev_sign = None
run_start = None
N = 1201
for i in range(N):
    x = mp.mpf(i) * 60 / (N - 1)          # x in [0,60], step 0.05
    c0, s1, c2 = moms(x)
    p = c0 * c2
    tot += 1
    sgn = 1 if p >= 0 else -1
    if p < 0:
        neg += 1
        if len(first) < 8:
            first.append((float(x), p, s1 ** 2))
    if prev_sign is None:
        prev_sign = sgn
        run_start = x
    elif sgn != prev_sign:
        runs.append((prev_sign, float(run_start), float(x)))
        prev_sign = sgn
        run_start = x
runs.append((prev_sign, float(run_start), 60.0))

print(f"  scanned {tot} points, x in [0,60] step 0.05, mpmath 40 dps")
print(f"  c0*c2 < 0 at {neg}/{tot} points  ({100.0*neg/tot:.1f}% of the grid)")
print("  first failures:")
for (x, p, s) in first:
    print(f"    x={x:8.4f}  c0*c2 = {mp.nstr(p, 10):>16}   s1^2 = {mp.nstr(s, 10):>16}"
          f"   sum = {mp.nstr(p + s, 10)}")
print("  sign runs of c0*c2 on [0,60]  (+ = nonneg, - = negative):")
for (sgn, a, b) in runs[:24]:
    print(f"    {'+' if sgn > 0 else '-'}  [{a:7.3f}, {b:7.3f})")
print()
print("  VERDICT: the proposed sub-fibre  0 <= c0*c2  is FALSE on a set of positive")
print("  measure.  It is moved to FAILED.  The OPEN statement stays the full edge")
print("      0 <= c0*c2 + s1^2 ,")
print("  and the genuinely smallest useful decomposition is the SIGN SPLIT:")
print("    - on {c0*c2 >= 0}: already compiled (C3B12.momentTwo_nonneg_of_cos);")
print("    - on {c0*c2 <  0}: the whole content is  |c0*c2| <= s1^2 ,")
print("      i.e. square domination, reduced by C3B12.momentTwo_nonneg_of_square_dominates.")
print("  Margin of the surviving inequality on the negative region:")
worst = (mp.inf, None)
for i in range(N):
    x = mp.mpf(i) * 60 / (N - 1)
    c0, s1, c2 = moms(x)
    p = c0 * c2
    if p < 0:
        r = (p + s1 ** 2) / (s1 ** 2) if s1 != 0 else mp.inf
        if r < worst[0]:
            worst = (r, x)
print(f"    min over {{c0*c2<0}} of (c0*c2 + s1^2)/s1^2 = {mp.nstr(worst[0], 10)}"
      f"  at x = {float(worst[1]):.4f}")
print("    (a scale-free margin: 1 would mean c0*c2 = 0, 0 would mean equality/failure)")

print()
print("=" * 78)
print("(5)  P4's x = 300 tail value: precision cross-check at 80 and 120 dps")
print("=" * 78)


def L1_at(x, dps):
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        v = Xi(x)
        d1 = mp.diff(Xi, x, 1)
        d2 = mp.diff(Xi, x, 2)
        return d1 ** 2 - v * d2, v
    finally:
        mp.mp.dps = old


print(f"  {'x':>6} {'dps':>5} {'L1':>26} {'Xi':>26} {'L1/Xi^2 (scale-free)':>24}")
for x in [100.0, 200.0, 300.0]:
    row = {}
    for dps in (30, 80, 120):
        v, X = L1_at(x, dps)
        row[dps] = (v, X)
        r = v / X ** 2 if X != 0 else mp.nan
        print(f"  {x:6.1f} {dps:5d} {mp.nstr(v, 12):>26} {mp.nstr(X, 12):>26}"
              f" {mp.nstr(r, 12):>24}")
    v30, _ = row[30]
    v80, X80 = row[80]
    v120, X120 = row[120]
    rel_30_120 = abs(v30 - v120) / abs(v120) if v120 != 0 else mp.nan
    rel_80_120 = abs(v80 - v120) / abs(v120) if v120 != 0 else mp.nan
    r80 = v80 / X80 ** 2
    r120 = v120 / X120 ** 2
    rel_r = abs(r80 - r120) / abs(r120)
    print(f"         rel(30 vs 120) = {mp.nstr(rel_30_120, 6)}   "
          f"rel(80 vs 120) = {mp.nstr(rel_80_120, 6)}   "
          f"rel scale-free(80 vs 120) = {mp.nstr(rel_r, 6)}")
    print()
print("  LABEL: NON-CERTIFIED.  Even where the 80- and 120-dps values agree, these are")
print("  floating-point evaluations of mp.diff on a function of enormous dynamic range;")
print("  they are consistency checks, not interval arithmetic, and no claim in the")
print("  batch-12 ledger rests on them.  The scale-free ratio L1/Xi^2 is the only figure")
print("  reported with a meaningful number of correct digits, and the raw 1e-194 value")
print("  quoted in P4 at 30 dps is withdrawn as a certified figure.")
