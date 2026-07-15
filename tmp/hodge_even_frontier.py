"""
Sam's doubt: "I doubt there's just one exception at grade 2, and that's the real frontier."
Structural read of the measured signs m=1..17  (+,-,-,-,+,+,-,-,+,+,-,-,+,+,-,-,+):

  ODD m  (EVEN weight k=m+1): m=1,3,5,7,9,11,13,15,17 -> +,-,+,-,+,-,+,-,+
         CLEAN alternation: eps = +1 iff m == 1 (mod 4).  This is -i^{m+1} with a
         constant finite root number w_f=-1 -- a genuine congruence.
  EVEN m (ODD weight): m=2,4,6,8,10,12,14,16 -> -,-,+,-,+,-,+,-
         i^{m+1} is imaginary, so eps is fixed by a GAUSS-SUM root number, not a congruence.
         m=4..16 happen to alternate (m==2 mod4 -> +), but m=2 does NOT -> this is where
         a Gauss-sum mechanism (which need NOT be a congruence) first shows.  THE FRONTIER.

Test: push the AFE resolution (NODES, M) hard on the even frontier m=18 (control: m=16, known
clean -1) to see whether m=18 resolves, and which sign -- i.e. whether the even sequence keeps
matching the naive congruence or deviates (Sam's predicted extra exceptions).
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

def both_res(G, lam, s0, T, NODES, M):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T, NODES=NODES, M=M)
    a, b = complex((lk * H1).sum()), complex((lk * H2).sum())
    d = complex(G(mp.mpf(s0))) * float((lam[1:] * n ** (-float(s0))).sum())
    return abs((a + b) - d) / max(abs(d), 1e-30), abs((a - b) - d) / max(abs(d), 1e-30)

print(" m   NODES     M    T    res[+1]    res[-1]   decisiveness  pick   predict(cong)")
for m in [16, 18]:
    pred = "+1" if (m % 4) in (1, 2) else "-1"
    if m == 2:
        pred = "-1(exc)"
    for (NODES, M, T, nm) in [(24001, 3200, 90, 8000 + 3000 * m),
                              (60001, 8000, 140, 16000 + 5000 * m)]:
        _, lam = cl.bank_hecke_unitary(m, nm)
        G = cl.make_G(49, [('C', m / 2.0)])
        rp, rm = both_res(G, lam, 2.5, T, NODES, M)
        pick = "+1" if rp < rm else "-1"
        dec = min(rp, rm) / max(rp, rm)
        flag = "" if pick == pred else "  <-- DEVIATES"
        print("%2d  %6d  %5d  %3d  %.2e  %.2e    %7.4f      %s     %s%s"
              % (m, NODES, M, T, rp, rm, dec, pick, pred, flag))
    print()
