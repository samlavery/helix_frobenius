# recognition-queue 2026-07-29 — k-POWER CENSUS: the flat-13 poke.
# Base-change probe: over F_{p^k} the H^4 spectrum is the k-th powers, so
# per (p,k) recluster (val/p^2)^k and measure:
#   multW_k  multiplicity of the mu6-addressed channel (Weil block);
#            STABLE AT 18 = signature survives base change;
#            JUMP ABOVE 18 = impostors merge in = descent shape breaks.
#   D_k      distinct-eigenvalue count (collisions expected to shrink it)
#   gapW_k   distance from the Weil cluster to the nearest other cluster
import sys, json
sys.path.insert(0, '.')
from schoen_explicit import counts_and_rail, newton_e, Z3, emb, KMAX
from sage.all import PolynomialRing, CDF, ComplexField
from itertools import combinations

PRIMES_CENSUS = [7, 31, 37, 43, 61, 67, 73, 79, 97]
KPOWERS = [1, 2, 3, 4, 6, 12]
OUT = "wall_kpower_census.jsonl"

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
    return rts + [r.conjugate() for r in rts]

def kcensus(p):
    eigs = frob_eigs(p)
    q2 = CDF(p)**2
    base = []
    for idx in combinations(range(8), 4):
        v = CDF(1)
        for i in idx: v *= eigs[i]
        base.append(v / q2)
    rows = []
    for k in KPOWERS:
        vals = [v**k for v in base]
        clusters = {}
        for v in vals:
            clusters.setdefault((round(v.real(), 8), round(v.imag(), 8)),
                                []).append(v)
        reps = {kk: sum(c)/len(c) for kk, c in clusters.items()}
        def order_of(z, kmax=60):
            for j in range(1, kmax + 1):
                if abs(z**j - 1) < 1e-6: return j
            return 0
        weil_keys = [kk for kk, z in reps.items()
                     if order_of(z) in (1, 2, 3, 6)]
        multW = sum(len(clusters[kk]) for kk in weil_keys)
        gaps = []
        for kk in weil_keys:
            for kk2, z2 in reps.items():
                if kk2 not in weil_keys:
                    gaps.append(abs(reps[kk] - z2))
        gapW = min(gaps) if gaps else float('inf')
        rows.append({"p": int(p), "k": int(k), "D": len(reps),
                     "multW": int(multW), "gapW": float(gapW)})
    return rows

with open(OUT, "w") as fh:
    for p in PRIMES_CENSUS:
        try:
            for r in kcensus(p):
                fh.write(json.dumps(r, default=float) + "\n")
            fh.flush()
            print(f"p={p} done", flush=True)
        except Exception as ex:
            print(f"p={p} ERROR {ex}", flush=True)
print("KPOWER CENSUS DONE", flush=True)
