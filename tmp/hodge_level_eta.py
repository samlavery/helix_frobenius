"""
Sam: "grade 2 might need eta -- the trivial Dirichlet character needs special treatment."
Concrete mechanism: for EVEN m, eps^m = trivial (psi^m has trivial finite conductor), so
theta_{psi^m} may have level 7 (|disc K|), NOT 49.  m=2 -> the weight-3 CM newform 7.3.b.a.
I computed EVERY grade at N=49.  If the true level is 7 for (some) even m, the 49/7 = eta^2
mismatch is an extra eta that can flip the sign.

Test: for each low m, run the split-vs-direct functional-equation certificate at BOTH N=7 and
N=49; the TRUE conductor is the one with the decisive low residual.  Report the sign at each N.
If m=2 is clean (eps=+1, matching the period-4 law) at N=7 while N=49 gave the anomalous -1,
then m=2 was a LEVEL error, not an arithmetic anomaly -> the clean law is EXACT, no exceptions.
"""
import importlib.util, sys
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass
mp.dps = 30

def both_res(G, lam, s0=2.5, T=60):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

CLEAN = {1:+1, 2:+1, 3:-1, 4:-1, 5:+1, 6:+1}   # pure period-4 law (m==1,2 mod4 -> +1)
print(" m  wt  parity   N=7:  res+   res-   sgn dec |  N=49: res+   res-   sgn dec | clean")
for m in range(1, 7):
    nmax = 3000 + 800 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    out = {}
    for N in (7, 49):
        G = cl.make_G(N, [('C', m / 2.0)])
        rp, rm = both_res(G, lam)
        sgn = +1 if rp < rm else -1
        dec = min(rp, rm) / max(rp, rm)
        out[N] = (rp, rm, sgn, dec)
    p7, m7, s7, d7 = out[7]; p49, m49, s49, d49 = out[49]
    par = "even" if m % 2 == 0 else "odd "
    print(" %d  %2d  %s  %.1e %.1e %+d %.3f | %.1e %.1e %+d %.3f | %+d"
          % (m, m + 1, par, p7, m7, s7, d7, p49, m49, s49, d49, CLEAN[m]))

print("\nRead: for each m the TRUE level is the N with the SMALLER residuals (decisive, dec<<1).")
print("If even m are decisive at N=7 and m=2 reads +1 there -> the period-4 law is EXACT,")
print("m=2 was a wrong-conductor artifact (the eta Sam flagged), a clean NEW finding.")
