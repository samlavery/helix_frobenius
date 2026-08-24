"""
att522b — THE CONTROL att522 should have had.

att522 measured lambda_min/lambda_max ~ 0.18^n for the window Hankel built from
zeta zero ordinates, and I reported the near-universality of 0.18 as a finding.

CONTROL QUESTION: is 0.18 a fact about ZETA, or a generic fact about the Hankel
matrix of any smooth point set on an interval?

Same pipeline, three node sets on the same window, same count:
  (Z) actual zeta zero ordinates
  (U) exactly equispaced points
  (R) uniform random points
  (C) Chebyshev points (arcsine-distributed, deliberately NOT uniform)

DECISION RULE (pre-registered):
  NULL      : all four give the same decay -> the measurement carries no
              arithmetic information and att522's "finding" is generic.
  INFORMATIVE: zeros differ measurably from U and R.

Classical prediction for the constant: the Hilbert matrix (moments of Lebesgue
on [0,1]) has lambda_min ~ (sqrt2-1)^{4n}.  A SYMMETRIC measure on [-1,1] has
vanishing odd moments, so the Hankel decouples into even/odd blocks in w^2,
giving per-step (sqrt2-1)^2 = 3-2sqrt2 = 0.17157.  If the measured rate matches
that, the result is pure conditioning, not arithmetic.
"""
import random
import mpmath as mp

mp.mp.dps = 60


def decay_table(nodes, nmax):
    r = len(nodes)
    rows = []
    for n in range(1, min(nmax, r) + 1):
        H = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                H[i, j] = mp.fsum(w ** (i + j) for w in nodes) / r
        ev = mp.eigsy(H, eigvals_only=True)
        rows.append((n, min(ev), max(ev)))
    return rows


def load_zeros():
    with open("tmp/att522_zeros.txt") as fh:
        return [mp.mpf(s.strip()) for s in fh if s.strip()]


if __name__ == "__main__":
    a, b = mp.mpf(300), mp.mpf(700)
    c, h = (a + b) / 2, (b - a) / 2
    ZS = load_zeros()
    zn = [(g - c) / h for g in ZS if a < g < b]
    r = len(zn)
    print("window (300,700), r = %d nodes\n" % r)

    random.seed(20260824)
    sets = {
        "Z zeta zeros": zn,
        "U equispaced": [mp.mpf(-1) + 2 * mp.mpf(i) / (r - 1) for i in range(r)],
        "R random unif": sorted(mp.mpf(random.uniform(-1, 1)) for _ in range(r)),
        "C chebyshev  ": [mp.cos(mp.pi * (2 * i + 1) / (2 * r)) for i in range(r)],
    }

    tabs = {k: decay_table(v, 12) for k, v in sets.items()}
    print("  n |" + "".join("  %-14s" % k for k in sets))
    print("    |" + "".join("  %-14s" % "lmin/lmax" for _ in sets))
    for idx in range(12):
        line = " %2d |" % (idx + 1)
        for k in sets:
            n, lo, hi = tabs[k][idx]
            line += "  %-14s" % mp.nstr(lo / hi, 6)
        print(line)

    print("\n  per-step decay factor (n=11 -> 12):")
    for k in sets:
        _, lo1, hi1 = tabs[k][10]
        _, lo2, hi2 = tabs[k][11]
        print("    %-14s  %s" % (k, mp.nstr((lo2 / hi2) / (lo1 / hi1), 6)))
    print("\n  classical (3-2*sqrt2) = %s" % mp.nstr(3 - 2 * mp.sqrt(2), 8))
