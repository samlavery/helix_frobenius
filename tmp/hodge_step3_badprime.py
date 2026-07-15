"""
Step 3: fix the bad-prime Euler factor to the PRIMITIVE-LOCAL coefficient and drive the
level-7 functional-equation residual from ~1e-3 to machine zero.

Derivation (not a fit): at the ramified prime, a_7 = psi^m(p_7) = (sqrt-7)^m = (i*sqrt7)^m,
so unitary lambda_7 = a_7 / 7^{(k-1)/2} = (i*sqrt7)^m / 7^{m/2} = i^m.  For even m this is
REAL: lambda_7 = (-1)^{m/2}  (= -1 at m=2 <-> LMFDB a_7(7.3.b.a) = -7; +1 at m=4; -1 at m=6).
The 7-Euler factor is degree 1 (7 || level 7): a_{7^j} = a_7^j, so lambda_{7^j} = lambda_7^j.

Rebuild each even-m bank at N=7 with this lambda_7 and certify.  Expect residual -> ~1e-5
(machine-clean) and sign = period-4.  This also settles the level: if ALL even m now certify
decisively at N=7, the level is period-2 (every even m level 7), confirming the derivation and
killing the earlier "m=4,8 look level 49" reading as the wrong-lambda_7 artifact.
Old (wrong) lambda_7=+/-1/sqrt7 shown alongside for contrast.
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
    lam = lam_free.copy()
    j = 1
    while 7 ** j <= nmax:
        pw = 7 ** j; xj = lam7 ** j
        for k in range(1, nmax // pw + 1):
            if k % 7:
                lam[k * pw] = lam_free[k] * xj
        j += 1
    return lam

def both_res(G, lam, s0=2.5, T=90, NODES=20001, M=3000):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

print(" m  wt  lam_7=i^m   N=7 (correct lam_7):  res[+1]  res[-1]  dec   sign | old lam_7=+/-1/sqrt7 best dec | period-4")
for m in [2, 4, 6, 8, 10, 12]:
    nmax = 7000 + 1400 * m
    _, lam_free = cl.bank_hecke_unitary(m, nmax)
    lam7 = float(np.real((1j) ** m))            # i^m, real for even m
    lam = add_7euler(lam_free, lam7, nmax)
    G = cl.make_G(7, [('C', m / 2.0)])
    rp, rm = both_res(G, lam)
    sgn = +1 if rp < rm else -1
    dec = min(rp, rm) / max(rp, rm)
    # old wrong model, best over +/-1/sqrt7, for contrast
    olddec = 1.0
    for x in (1.0 / np.sqrt(7), -1.0 / np.sqrt(7)):
        lo = add_7euler(lam_free, x, nmax)
        rp2, rm2 = both_res(G, lo)
        olddec = min(olddec, min(rp2, rm2) / max(rp2, rm2))
    p4 = +1 if (m % 4 in (1, 2)) else -1
    print(" %2d  %2d   %+d       res+=%.2e res-=%.2e dec=%.4f sgn=%+d |  old best dec=%.3f  | %+d %s"
          % (m, m + 1, int(lam7), rp, rm, dec, sgn, olddec, p4, "OK" if sgn == p4 else "MISMATCH"))
