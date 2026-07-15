"""
Diagnose the level-7 residual floor at m=2 (weight 3, 7.3.b.a, LMFDB a_7=-7 => lambda_7=-1).
Scan lambda_7 over real values at N=7, two resolutions, and find the residual-minimizing value.
If min is at lambda_7=-1 with res ~1e-4 -> fix works, earlier run had a resolution issue.
If min is elsewhere or floors ~1e-3 for all lambda_7 -> the certify has a separate issue
(nebentypus in the FE reflection), independent of the bad-prime coefficient.
Also print a few reconstructed lambda_n vs the CM prediction as a bank sanity check.
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

def add_7euler(lam_free, lam7, nmax):
    lam = lam_free.copy(); j = 1
    while 7 ** j <= nmax:
        pw = 7 ** j; xj = lam7 ** j
        for k in range(1, nmax // pw + 1):
            if k % 7:
                lam[k * pw] = lam_free[k] * xj
        j += 1
    return lam

def both_res(G, lam, T, NODES, M, s0=2.5):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

m = 2; nmax = 9000
_, lam_free = cl.bank_hecke_unitary(m, nmax)
G = cl.make_G(7, [('C', m / 2.0)])
print("m=2 bank sanity (7-free lambda_n, n coprime to 7): lambda_2=%.4f lambda_3=%.4f lambda_11=%.4f"
      % (lam_free[2], lam_free[3], lam_free[11]))
print("  (CM: lambda_p = a_p/p ; a_p^(2)=t_2 from 49a a_p)")

for (T, NODES, M) in [(90, 20001, 3000), (140, 48001, 8000)]:
    print("\n-- resolution T=%d NODES=%d M=%d --" % (T, NODES, M))
    for lam7 in [-1.0, -0.5, -1/np.sqrt(7), 0.0, 1/np.sqrt(7), 0.5, 1.0]:
        lam = lam_free if lam7 == 0.0 else add_7euler(lam_free, lam7, nmax)
        rp, rm = both_res(G, lam, T, NODES, M)
        print("   lambda_7=%+.4f :  res[+1]=%.3e  res[-1]=%.3e  min=%.3e"
              % (lam7, rp, rm, min(rp, rm)))
