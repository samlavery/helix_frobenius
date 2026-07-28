# recognition-queue 2026-07-28, session 18a3f704 — THE NUMBER ON THE WALL
# Degree/height census of the collective (Weil) channel's Frobenius
# projector on the explicit Schoen fourfold (config A of schoen_explicit).
# Diversity = one algebraic correspondence per p (polynomial in Frob_p);
# commonality = the mu6 Weil channel, constant across p (freeze law).
# Census per split good prime p:
#   D_p     interpolation degree = #distinct normalized H^4 eigenvalues
#   multW   multiplicity of the Weil channel (normalized value in mu6)
#   N_p     lcm of root-of-unity orders in the spectrum (Tate-power stage)
#   D2_p    #distinct after Frob^{N_p} (two-stage projector degree)
#   delta_p min angular gap (Lagrange coefficient-height proxy:
#           height ~ (D_p - 1) * log(1/delta_p))
import sys
sys.path.insert(0, '.')
from schoen_explicit import counts_and_rail, newton_e, Z3, emb, KMAX
from sage.all import PolynomialRing
import json
from itertools import combinations
from sage.all import CDF, lcm

PRIMES_CENSUS = [7, 31, 37, 43, 61, 67, 73, 79, 97]
OUT = "wall_degree_census.jsonl"

def frob_eigs(p):
    sW = []
    for k in range(1, KMAX + 1):
        _, _, s, _, _ = counts_and_rail(p, k)
        sW.append(s)
    e = newton_e([Z3(0)] + sW, KMAX, Z3)
    R = PolynomialRing(Z3, 'T'); T = R.gen()
    chi = T**4 - e[1]*T**3 + e[2]*T**2 - e[3]*T + e[4]
    Rc = PolynomialRing(CDF, 'T')
    chic = Rc([CDF(emb(c)) for c in chi.list()])
    rts = []
    for r, mmult in chic.roots():
        rts += [r]*mmult
    if len(rts) < 4:  # CDF merged close roots: high-precision fallback
        from sage.all import ComplexField
        C100 = ComplexField(100)
        Rh = PolynomialRing(C100, 'T')
        chih = Rh([C100(emb(c)) for c in chi.list()])
        rts = []
        for r, mmult in chih.roots():
            rts += [CDF(r)]*mmult
    # resume: skip primes already recorded
    return rts + [r.conjugate() for r in rts]

def census(p):
    eigs = frob_eigs(p)
    q2 = CDF(p)**2
    vals = []
    for idx in combinations(range(8), 4):
        v = CDF(1)
        for i in idx: v *= eigs[i]
        vals.append(v / q2)
    # cluster by angle (all |.| = 1 up to numerics)
    def key(z, digits=8):
        return round(z.real(), digits), round(z.imag(), digits)
    clusters = {}
    for v in vals:
        clusters.setdefault(key(v), []).append(v)
    reps = [sum(c)/len(c) for c in clusters.values()]
    D = len(reps)
    def order_of(z, kmax=60):
        for k in range(1, kmax + 1):
            if abs(z**k - 1) < 1e-6: return k
        return 0
    orders = [order_of(z) for z in reps]
    multW = sum(len(c) for (kk, c), o in zip(clusters.items(), orders)
                if o != 0 and 6 % o == 0 or o == 6)
    finite = [o for o in orders if o > 0]
    N = int(lcm(finite)) if finite else 1
    powed = {}
    for v in vals:
        powed.setdefault(key(v**N), []).append(v)
    D2 = len(powed)
    gaps = []
    for i in range(D):
        for j in range(i + 1, D):
            gaps.append(abs(reps[i] - reps[j]))
    delta = min(gaps) if gaps else float('inf')
    import math
    height = (D - 1) * math.log10(1/delta) if gaps else 0.0
    return {"p": int(p), "D": D, "multW": int(multW), "N": N, "D2": D2,
            "delta": float(delta), "height_proxy": round(height, 2),
            "n_rootsofunity_clusters": len(finite)}

import os
done = set()
if os.path.exists(OUT):
    for line in open(OUT):
        try: done.add(json.loads(line)["p"])
        except Exception: pass
with open(OUT, "a") as fh:
    for p in PRIMES_CENSUS:
        if p in done:
            continue
        try:
            r = census(p)
            fh.write(json.dumps(r, default=float) + "\n"); fh.flush()
            print(r, flush=True)
        except Exception as ex:
            print(f"p={p} ERROR {ex}", flush=True)
print("CENSUS DONE", flush=True)
