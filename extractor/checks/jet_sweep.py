"""Conditioning of the ratio enclosure as a function of kappa.

Pre-registered: the geometric law err_m ~ C kappa^m should hold whenever the nearest
ordinate is DOMINANT.  Criterion: measured contraction within 5% of kappa.
Predicted: holds for kappa below ~0.5, degrades as kappa -> 1.  A failure at SMALL
kappa would refute the law; failure near kappa = 1 is the expected loss of a
dominant pole, not a refutation.
"""
from mpmath import mp, mpf, zetazero

mp.dps = 50
K = 60
gam = [zetazero(k).imag for k in range(1, K + 1)]

def contraction(y0):
    d = [y0 - g for g in gam]
    dist = sorted((abs(x), x) for x in d)
    kappa = dist[0][0] / dist[1][0]
    d1 = dist[0][1]
    errs = []
    for m in range(1, 16):
        A  = sum(x**(-m)     for x in d)
        A1 = sum(x**(-(m+1)) for x in d)
        errs.append(abs(A / A1 - d1))
    rs = [errs[m] / errs[m-1] for m in range(5, 15) if errs[m-1] != 0]
    return kappa, sum(rs) / len(rs)

# sweep offsets to the LEFT of gamma_1 (isolated: nearest is gamma_1, next is gamma_2)
print(" offset from g1     kappa      measured contraction    rel. agreement   verdict")
rows = []
for off in ['0.10','0.20','0.30','0.50','0.80','1.20','1.80','2.50','3.20','3.59']:
    y0 = gam[0] - mpf(off)
    k, c = contraction(y0)
    rel = abs(c - k) / k
    v = "CONFIRMED" if rel < mpf('0.05') else "degraded"
    rows.append((k, c, rel, v))
    print(f"   -{off:>5}      {mp.nstr(k,6):>9}      {mp.nstr(c,6):>12}          "
          f"{mp.nstr(rel*100,4):>7}%      {v}")

print()
ok = [r for r in rows if r[3] == "CONFIRMED"]
print(f"geometric law confirmed at {len(ok)}/{len(rows)} offsets;")
if ok:
    print(f"  largest kappa at which it held: {mp.nstr(max(r[0] for r in ok),6)}")
bad = [r for r in rows if r[3] != "CONFIRMED"]
if bad:
    print(f"  smallest kappa at which it degraded: {mp.nstr(min(r[0] for r in bad),6)}")
