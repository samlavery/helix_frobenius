"""
Resolve the m=18 sign: genuine period-4 break, or numerical artifact?
For m=15..18, at growing (nmax, T), print BOTH sign residuals res[+1], res[-1] and
their decisiveness ratio, plus the central value FORCED under each sign.  A real eps=-1
has res[-1] << res[+1] robustly AND a sensible eps=+1 forced-value blow-up/incoherence;
an artifact shows res[+1] ~ res[-1] (ambiguous) and/or drifts with resolution.
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass
mp.dps = 30

def both_residuals(G, lam, s0, T):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    resp = abs((a + b) - d) / max(abs(d), 1e-30)
    resm = abs((a - b) - d) / max(abs(d), 1e-30)
    return resp, resm

def central_forced(G, lam, eps, T):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    H1 = cl._kernels(G, mp.mpf("0.5"), ys, T=T)
    lam_val = (1.0 + eps) * (lam[1:][keep] * H1).sum()
    return complex(lam_val) / complex(G(mp.mpf("0.5")))

print(" m   nmax    T    res[+1]    res[-1]   ratio(-/+)  pick   L|eps=+1")
for m in [15, 16, 17, 18]:
    for (nmax, T) in [(6000 + 2500 * m, 60), (12000 + 4000 * m, 100)]:
        _, lam = cl.bank_hecke_unitary(m, nmax)
        G = cl.make_G(49, [('C', m / 2.0)])
        rp, rm = both_residuals(G, lam, 2.5, T)
        pick = "+1" if rp < rm else "-1"
        ratio = (rp / rm) if rp < rm else (rm / rp)  # decisiveness: winner/loser, <1 is decisive
        Lplus = central_forced(G, lam, +1, T).real
        print("%2d  %6d  %3d  %.2e  %.2e   %8.4f   %s   %+.5f"
              % (m, nmax, T, rp, rm, (min(rp, rm) / max(rp, rm)), pick, Lplus))
    print()
