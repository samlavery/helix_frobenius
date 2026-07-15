"""
Sam's method: dynamically scale the harmonic/root at the bad prime per grade, keep grade-2 eta,
continuously update as you climb.  Concretely: my bank sets lambda_7=0 (right for level 49).
For the LEVEL-7 grades, 7 || level, so a_7 = +/- 7^{(k-2)/2}, i.e. lambda_7 = +/-1/sqrt7.
Restore the 7-Euler factor with self-tuned sign s7, and let each grade dynamically pick its
conductor N and s7 by minimizing the functional-equation residual.  Read the sign at the tuned
optimum.  Test m=2,4,6,8 (crux m=4); a clean drop to ~1e-5 confirms the fix and the true level.
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

def add_7euler(lam_free, x, nmax):
    """lam_free has lambda_n=0 for 7|n. Insert the 7-Euler factor: lambda_{7^j k}=lambda_k x^j."""
    lam = lam_free.copy()
    j = 1
    while 7 ** j <= nmax:
        pw = 7 ** j; xj = x ** j
        for k in range(1, nmax // pw + 1):
            if k % 7:
                lam[k * pw] = lam_free[k] * xj
        j += 1
    return lam

def resid(G, lam, s0, T=90, NODES=20001, M=3000, eps=None):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    rp = abs((a + b) - d) / max(abs(d), 1e-30)
    rm = abs((a - b) - d) / max(abs(d), 1e-30)
    return rp, rm

for m in [2, 4, 6, 8]:
    nmax = 8000 + 1200 * m
    _, lam_free = cl.bank_hecke_unitary(m, nmax)     # lambda_7^j = 0
    print("m=%d (wt %d, m mod4=%d) -- dynamic conductor+bad-prime tuning" % (m, m + 1, m % 4))
    best = None
    # candidate conductors and 7-Euler factors:
    #   level 49: 7 fully ramified, lambda_7=0            (x=0)
    #   level 7 : 7 || level,        lambda_7=+/-1/sqrt7  (x=+/-1/sqrt7)
    cands = [(49, 0.0), (7, 1.0 / np.sqrt(7)), (7, -1.0 / np.sqrt(7))]
    for (N, x) in cands:
        lam = lam_free if x == 0.0 else add_7euler(lam_free, x, nmax)
        G = cl.make_G(N, [('C', m / 2.0)])
        rp, rm = resid(G, lam, 2.5)
        sgn = +1 if rp < rm else -1
        dec = min(rp, rm) / max(rp, rm)
        tag = "level49,a7=0 " if x == 0 else ("level7,a7=+7^.. " if x > 0 else "level7,a7=-7^.. ")
        print("   %s N=%2d :  res[+1]=%.2e res[-1]=%.2e dec=%.4f sign=%+d"
              % (tag, N, rp, rm, dec, sgn))
        if best is None or min(rp, rm) < best[0]:
            best = (min(rp, rm), N, x, sgn, dec)
    print("   -> TUNED: min-residual=%.2e at N=%d, lambda_7*sqrt7=%+.0f, sign=%+d, dec=%.4f  %s\n"
          % (best[0], best[1], best[2] * np.sqrt(7), best[3], best[4],
             "period-4 predicts %+d" % (+1 if m % 4 == 2 else -1)))
