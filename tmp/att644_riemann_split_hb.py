# att644 — the Riemann-split strand chirality: xi(s) = F(s) + F(1-s), F(s) = 1/4 + (1/2) s(s-1) I(s),
# I(s) = int_1^inf psi(x) x^{s/2-1} dx = sum_n (pi n^2)^{-s/2} Gamma(s/2, pi n^2).
# HB for E(z) = 2F(1/2+iz) <=> one strand dominates pointwise off the line. Measure R(s) = |F(s)|/|F(1-s)|
# on Re s > 1/2. PRE-REGISTERED: if R < 1 everywhere on the grid (or > 1 everywhere), the split is a
# chirality candidate; if R crosses 1 on the grid, this E is not HB (an off-line zero of A would not follow,
# but the de Branges route on THIS split is dead) — reported either way.
from mpmath import mp, mpf, mpc, pi, gammainc, exp, fabs, log
mp.dps = 30
def I(s):
    tot = mpc(0); n = 1
    while True:
        a = pi * n * n
        term = a ** (-s / 2) * gammainc(s / 2, a)
        tot += term
        if fabs(term) < mpf(10) ** (-28): break
        n += 1
    return tot
def F(s): return mpf(1) / 4 + s * (s - 1) / 2 * I(s)
# sanity: xi(s) = F(s) + F(1-s) at s = 1/2 + 14.134725 i should be ~0
from mpmath import zeta, gamma
def xi(s): return s * (s - 1) / 2 * pi ** (-s / 2) * gamma(s / 2) * zeta(s)
for s in (mpc(2, 0), mpc(0.5, 14.134725141734693), mpc(1, 20), mpc(3, 7)):
    print("check s=%s: F(s)+F(1-s) = %s   xi(s) = %s" % (s, F(s) + F(1 - s), xi(s)))
print("R(s) = |F(s)|/|F(1-s)| on Re s > 1/2  (HB for E = 2F(1/2+iz) needs one-sided R everywhere)")
print("   Im s \\ Re s : " + "  ".join("%6.2f" % sg for sg in (0.55, 0.6, 0.75, 1.0, 1.5, 2.0, 3.0)))
lo = 1e9; hi = 0
for t in (0, 2, 5, 10, 14.1, 17, 21.02, 25, 30.4, 40, 50, 60, 80, 100):
    row = []
    for sg in (0.55, 0.6, 0.75, 1.0, 1.5, 2.0, 3.0):
        s = mpc(sg, t); r = fabs(F(s)) / fabs(F(1 - s)); row.append(float(r)); lo = min(lo, float(r)); hi = max(hi, float(r))
    print("   %6.2f       : " % t + "  ".join("%6.3f" % r for r in row))
print("min R = %.4f  max R = %.4f  -> %s" % (lo, hi, "one-sided (chirality candidate)" if (hi < 1 or lo > 1) else "R crosses 1: this split is NOT Hermite-Biehler"))
print("log R(s) = log|F(s)| - log|F(1-s)| at height (the chirality margin):")
for t in (21.02, 40, 60, 100, 150):
    print("   t=%6.2f : " % t + "  ".join("sigma=%.2f: %+.2e" % (sg, float(log(fabs(F(mpc(sg, t))) / fabs(F(mpc(1 - sg, t)))))) for sg in (0.6, 1.0, 2.0, 3.0)))
