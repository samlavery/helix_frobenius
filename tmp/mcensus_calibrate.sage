# locus-ledger 2026-07-29 — m-census CALIBRATION v1 (projector level).
# DESIGN FACT under test: at split p (1 mod 3) the Weil block and the
# Lefschetz block share the Frobenius address (both Tate: normalized
# eigenvalue 1) -> the split-prime census CANNOT separate them (multW=18
# = whole Tate block). At INERT p (2 mod 3) Frobenius swaps the zeta3
# eigenspaces: W-type products should acquire a sign/character twist
# separating them from Theta-powers. If addresses split at inert p, the
# Weil projector pi_W is constructible from two-prime data.
import sys, json
sys.path.insert(0, '.')
from schoen_explicit import counts_and_rail, newton_e, Z3, emb, KMAX
from sage.all import PolynomialRing, CDF, ComplexField
from itertools import combinations

SPLIT = [7, 31]
INERT = [5, 11, 17, 23]   # good (bad: 2,3,13,19), p = 2 mod 3

def frob_eigs(p):
    sW = []
    for k in range(1, KMAX + 1):
        _, _, s, _, _ = counts_and_rail(p, k)
        sW.append(s)
    e = newton_e([Z3(0)] + sW, KMAX, Z3)
    R = PolynomialRing(Z3, 'T'); T = R.gen()
    chi = T**4 - e[1]*T**3 + e[2]*T**2 - e[3]*T + e[4]
    C100 = ComplexField(100)
    Rh = PolynomialRing(C100, 'T')
    chih = Rh([C100(emb(c)) for c in chi.list()])
    rts = []
    for r, m in chih.roots():
        rts += [CDF(r)]*m
    return rts + [r.conjugate() for r in rts], [str(x) for x in sW]

def addresses(p):
    eigs, sW = frob_eigs(p)
    q2 = CDF(p)**2
    def order_of(z, kmax=24):
        for j in range(1, kmax + 1):
            if abs(z**j - 1) < 1e-6: return j
        return 0
    clusters = {}
    for idx in combinations(range(8), 4):
        v = CDF(1)
        for i in idx: v *= eigs[i]
        key = (round((v/q2).real(), 7), round((v/q2).imag(), 7))
        clusters.setdefault(key, []).append(idx)
    rows = []
    for key, members in clusters.items():
        z = CDF(key[0], key[1])
        o = order_of(z)
        rows.append((o, len(members), round(z.real(),4), round(z.imag(),4)))
    tate = [(o,m,re,im) for o,m,re,im in rows if o > 0]
    kind = "SPLIT" if p % 3 == 1 else "INERT"
    print(f"p={p:>3} ({kind}): rootsofunity clusters (order, mult, value):",
          sorted(tate), f"| s_odd(W)={sW[0]},{sW[2]}", flush=True)

for p in SPLIT + INERT:
    try:
        addresses(p)
    except Exception as ex:
        print(f"p={p} ERROR {ex}", flush=True)
print("CALIBRATION V1 DONE", flush=True)
