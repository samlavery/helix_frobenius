"""
High-precision level+sign for the low even grades m=2,4,6,8 (crux: is m=4 level 7 or 49?).
Certify at BOTH N=7 and N=49 with strong AFE settings; the true level = decisive N.
Also read the central value L(1/2) at the true level as an independent sign check
(eps=-1 => L(1/2)=0 forced; eps=+1 => L(1/2) != 0).
Prediction under test: m==2 mod4 -> level 7, eps=+1 ; m==0 mod4 -> level 49, eps=-1
(=> pure period-4, NO exception).
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

def both_res(G, lam, s0=2.5, T=110, NODES=36001, M=7000):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

def cval(G, lam, eps, T=110, NODES=36001, M=7000):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float)
    H1 = cl._kernels(G, mp.mpf("0.5"), ys, T=T, NODES=NODES, M=M)
    v = (1.0 + eps) * (lam[1:][keep] * H1).sum()
    return (complex(v) / complex(G(mp.mpf("0.5")))).real

for m in [2, 4, 6, 8]:
    nmax = 9000 + 1500 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    print("m=%d (wt %d), m mod4 = %d  -- predicted level %s, eps %s"
          % (m, m + 1, m % 4, "7" if m % 4 == 2 else "49", "+1" if m % 4 == 2 else "-1"))
    for N in (7, 49):
        G = cl.make_G(N, [('C', m / 2.0)])
        rp, rm = both_res(G, lam)
        sgn = +1 if rp < rm else -1
        dec = min(rp, rm) / max(rp, rm)
        Lc = cval(G, lam, sgn)
        print("   N=%2d :  res[+1]=%.2e  res[-1]=%.2e  dec=%.4f  sign=%+d  L(1/2)|sign=%+.4f"
              % (N, rp, rm, dec, sgn, Lc))
    print()
