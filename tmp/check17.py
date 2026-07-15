"""
Is d=17's NO-FIRE (eps=+1, against the naive -sign(d)=FIRE) a genuine arithmetic subtlety
or an artifact?  Check the suspects vs d=13 (clean FIRE control):
 (1) Kronecker char valid (multiplicative, period |d|, chi(-1)=sign d).
 (2) certify DECISIVE: both residuals res[+1],res[-1]; is the sign pick robust?
 (3) RESOLUTION-stable: bump nmax and T.
 (4) central value under BOTH signs (eps=+1 gives L; eps=-1 forces L=0 -> is L(+1) sensible?).
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try: spec.loader.exec_module(cl)
except SystemExit: pass
mp.dps = 30
exec(open("/Users/samuellavery/work/helix_frobenius/tmp/nofire_fire.py").read().split("m = 3")[0])  # kronecker, chi_d_arr

# (1) character validity
print("== (1) Kronecker char validity ==")
for d in (13, 17):
    vals = [kronecker(d, n) for n in range(1, abs(d)+1)]
    chi_m1 = kronecker(d, -1)
    mult_ok = all(kronecker(d, a*b) == kronecker(d, a)*kronecker(d, b)
                  for a in range(1, 12) for b in range(1, 12) if math.gcd(a*b, d) == 1)
    per_ok = all(kronecker(d, n) == kronecker(d, n+abs(d)) for n in range(1, 30))
    print("  d=%d: chi(-1)=%+d (expect %+d), multiplicative=%s, period-%d=%s, nonzero count/%d=%d"
          % (d, chi_m1, 1 if d > 0 else -1, mult_ok, abs(d), per_ok, abs(d),
             sum(1 for v in vals if v != 0)))

def both_res(G, lam, s0=2.5, T=60):
    n = np.arange(1, len(lam)); keep = np.abs(lam[1:]) > 0
    ys = n[keep].astype(float); lk = lam[1:][keep]
    H1 = cl._kernels(G, mp.mpf(s0), ys, T=T)
    H2 = cl._kernels(G, 1 - mp.mpf(s0), ys, T=T)
    a, b = complex((lk*H1).sum()), complex((lk*H2).sum())
    d_ = complex(G(mp.mpf(s0))) * float((lam[1:]*n**(-float(s0))).sum())
    return abs((a+b)-d_)/max(abs(d_),1e-30), abs((a-b)-d_)/max(abs(d_),1e-30)

print("\n== (2)-(4) certify decisiveness + resolution + both-sign central value ==")
print(" d   nmax    T   res[+1]   res[-1]  decisive  pick | L|eps=+1   L|eps=-1(forced0) L'|eps=-1")
for d in (13, 17):
    for (nm_mult, T) in [(700, 60), (1400, 100)]:
        nmax = 2000 + nm_mult*abs(d)
        _, lam0 = cl.bank_hecke_unitary(3, nmax)
        lam = lam0 * chi_d_arr(d, nmax)
        G = cl.make_G(49*d*d, [('C', 1.5)])
        rp, rm = both_res(G, lam, 2.5, T)
        pick = +1 if rp < rm else -1
        dec = min(rp, rm)/max(rp, rm)
        Lp = cl.central_value(G, lam, +1).real
        Lm = cl.central_value(G, lam, -1).real
        Ld = cl.central_deriv(G, lam, -1).real
        print(" %2d  %6d  %3d  %.2e  %.2e   %.4f    %+d | %+.4f    %+.4f          %+.4f"
              % (d, nmax, T, rp, rm, dec, pick, Lp, Lm, Ld))
