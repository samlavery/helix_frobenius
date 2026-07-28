# locus-ledger 2026-07-29 — m-census calibration v2: inert-prime reading
# via PLAIN point counts (valid at every p, no character machinery).
# s_k(anti) = tr(Frob^k|H1 C) - tr(Frob^k|H1 C'), k=1..4; the degree-8
# anti-invariant Weil polynomial completed by the functional equation
# c_{8-i} = p^{4-i} c_i. Gates: |alpha|=sqrt(p) all roots; split control
# must reproduce the (order 1, mult 18) Tate cluster.
# QUESTION: at inert p, does the address-1 fusion SPLIT (Theta^2 at +1 vs
# Weil-type lines elsewhere, e.g. order 2)?
import sys
sys.path.insert(0, '.')
from schoen_explicit import counts_and_rail
from sage.all import PolynomialRing, QQ, ComplexField, CDF
from itertools import combinations

CONTROL = [7, 31]
INERT = [5, 11, 17, 23]

def anti_poly(p):
    s = [None]
    for k in range(1, 5):
        nCp, nC, _, _, _ = counts_and_rail(p, k)
        q = p**k
        trC = q + 1 - nC
        trCp = q + 1 - nCp
        s.append(QQ(trC - trCp))
    # Newton: c_k = -(s_k + sum_{i<k} c_i s_{k-i})/k  for monic T^8+c1T^7+...
    c = [QQ(1)]
    for k in range(1, 5):
        acc = s[k]
        for i in range(1, k):
            acc += c[i]*s[k-i]
        c.append(-acc/k)
    # complete degree 8 by FE: c_{8-i} = p^{4-i} c_i
    full = c + [QQ(0)]*4
    for i in range(0, 4):
        full[8-i] = QQ(p)**(4-i) * c[i]
    # c_4 stays c[4]
    R = PolynomialRing(QQ, 'T'); T = R.gen()
    P = sum(full[j]*T**(8-j) for j in range(9))
    return P

def report(p):
    P = anti_poly(p)
    C100 = ComplexField(100)
    rts = []
    for r, m in P.change_ring(C100).roots():
        rts += [CDF(r)]*m
    if len(rts) != 8:
        print(f"p={p}: ROOT COUNT {len(rts)} != 8 — escalate"); return
    bad = [abs(abs(r) - float(p)**0.5) for r in rts]
    weil_ok = max(bad) < 1e-8
    q2 = CDF(p)**2
    def order_of(z, kmax=24):
        for j in range(1, kmax+1):
            if abs(z**j - 1) < 1e-6: return j
        return 0
    clusters = {}
    for idx in combinations(range(8), 4):
        v = CDF(1)
        for i in idx: v *= rts[i]
        key = (round((v/q2).real(), 7), round((v/q2).imag(), 7))
        clusters.setdefault(key, 0)
        clusters[key] += 1
    tate = sorted((order_of(CDF(k[0],k[1])), m, k[0], k[1])
                  for k, m in clusters.items()
                  if order_of(CDF(k[0],k[1])) > 0)
    kind = "SPLIT" if p % 3 == 1 else "INERT"
    print(f"p={p:>3} ({kind}) weil_gate={'OK' if weil_ok else 'FAIL'}"
          f"  rootsofunity clusters (order,mult,val): {tate}", flush=True)

for p in CONTROL + INERT:
    try:
        report(p)
    except Exception as ex:
        print(f"p={p} ERROR {ex}", flush=True)
print("V2 DONE", flush=True)
