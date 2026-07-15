"""
NEW FINDING under test: even-m grades (eps^m trivial) are level 7, odd-m are level 49.
Recompute EVERY grade at its TRUE conductor (whichever N in {7,49} gives the decisive FE),
and read the corrected sign.  My earlier signs were all at N=49 -> even-m ones may be wrong.
Report the corrected sequence and compare to candidate laws.
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

def both_res(G, lam, s0=2.5, T=80):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=16001, M=2400)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=16001, M=2400)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

OLD = {1:+1,2:-1,3:-1,4:-1,5:+1,6:+1,7:-1,8:-1,9:+1,10:+1,11:-1,12:-1,13:+1,14:+1,15:-1,16:-1,17:+1}
true_sign, true_lvl = {}, {}
print(" m  wt  par   trueN  dec@7   dec@49   sign@trueN  old(N=49)  changed")
for m in range(1, 18):
    nmax = 5000 + 900 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    res = {}
    for N in (7, 49):
        G = cl.make_G(N, [('C', m / 2.0)])
        rp, rm = both_res(G, lam)
        res[N] = (rp, rm, (+1 if rp < rm else -1), min(rp, rm) / max(rp, rm))
    d7, d49 = res[7][3], res[49][3]
    N = 7 if d7 < d49 else 49
    s = res[N][2]
    true_sign[m], true_lvl[m] = s, N
    ch = "" if s == OLD[m] else "  <-- FLIPPED"
    print(" %2d  %2d  %s  %3d   %.3f   %.3f     %+d          %+d      %s"
          % (m, m + 1, "ev" if m % 2 == 0 else "od", N, d7, d49, s, OLD[m], ch))

seq = "".join("+" if true_sign[m] > 0 else "-" for m in range(1, 18))
print("\ncorrected signs m=1..17 :  %s" % " ".join(seq))
print("levels m=1..17          :  %s" % " ".join(str(true_lvl[m]) for m in range(1, 18)))
# candidate: pure period-4 with NO exception  (eps=+1 iff m==1,2 mod4)
p4 = "".join("+" if (m % 4 in (1, 2)) else "-" for m in range(1, 18))
print("pure period-4 (no exc)  :  %s   match=%s"
      % (" ".join(p4), sum(seq[i] == p4[i] for i in range(17))))
