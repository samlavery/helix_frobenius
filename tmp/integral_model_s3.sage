# beyond-playbook direction 2 (2026-07-28): the NON-ABELIAN cut-glue integral
# model. H1 of an etale G-cover of a genus-g curve = Z[G]^{2(g-1)} (+) Z^2 with
# the standard G-symplectic form (same skeleton the cyclic model used and
# validated against Lange-Ortega). Compute the rho(x)omega isotypic lattice for
# G = S3 x Z/3 (the 2-dim irrep packet - OUTSIDE Patel-Zhang), restrict to a
# transposition-invariant half (= the Prym of the degree-3 non-Galois quotient
# tower, multiplicity-1 copy of B), and read the polarization type / Pfaffian.
# THE QUESTION: does the 2-dim irrep break the uniform-rescale law? Odd
# 2-valuation of the Pfaffian => det has odd valuation at the K-inert prime 2
# => disc not a norm => NON-SPLIT => the first beyond-playbook specimen CLASS.
# GATE first: G = Z/3 must reproduce the Lange-Ortega type (1^{g-1}, 3^{g-1}).
from sage.all import (matrix, identity_matrix, ZZ, QQ, block_matrix, vector)
import itertools, json

def s3_elements():
    # permutations of (0,1,2) as tuples; id first
    return [(0,1,2),(1,0,2),(2,1,0),(0,2,1),(1,2,0),(2,0,1)]

def s3_mul(p, q):  # (p*q)(i) = p(q(i))
    return tuple(p[q[i]] for i in range(3))

def s3_chi_rho(p):
    fix = sum(1 for i in range(3) if p[i] == i)
    return {3: 2, 1: 0, 0: -1}[fix]   # id:2, transposition:0, 3-cycle:-1

def build_group(kind):
    """returns (elements, mul, inv, psi) for the rational packet character."""
    if kind == "Z3":
        els = [0, 1, 2]
        mul = lambda a, b: (a + b) % 3
        inv = lambda a: (-a) % 3
        psi = lambda a: 2 if a == 0 else -1        # omega + omegabar packet
        dimchi = 1
    elif kind == "Z6":
        els = list(range(6))
        mul = lambda a, b: (a + b) % 6
        inv = lambda a: (-a) % 6
        psi = lambda a: [2, 1, -1, -2, -1, 1][a]   # primitive zeta6 packet
        dimchi = 1
    else:  # S3 x Z3
        S = s3_elements()
        els = [(s, j) for s in S for j in range(3)]
        mul = lambda a, b: (s3_mul(a[0], b[0]), (a[1] + b[1]) % 3)
        inv = lambda a: (tuple(sorted(range(3), key=lambda i: a[0][i])), (-a[1]) % 3)
        psi = lambda a: s3_chi_rho(a[0]) * (2 if a[1] == 0 else -1)
        dimchi = 2
    return els, mul, inv, psi, dimchi

def model(kind, g):
    els, mul, inv, psi, dimchi = build_group(kind)
    n = len(els)
    idx = {e: i for i, e in enumerate(els)}
    H = g - 1                      # handle blocks
    N = 2 * H * n + 2              # + central (atilde, beta)
    # basis: for h in range(H): e-block [h*2n .. h*2n+n), f-block [.. +2n)
    E = matrix(ZZ, N, N)
    for h in range(H):
        base = 2 * n * h
        for i in range(n):
            E[base + i, base + n + i] = 1
            E[base + n + i, base + i] = -1
    E[N-2, N-1] = 1; E[N-1, N-2] = -1
    assert abs(E.det()) == 1, "unimodularity gate FAIL"
    def act(k):
        M = matrix(ZZ, N, N)
        for h in range(H):
            base = 2 * n * h
            for gi, ge in enumerate(els):
                t = idx[mul(k, ge)]
                M[base + t, base + gi] = 1
                M[base + n + t, base + n + gi] = 1
        M[N-2, N-2] = 1; M[N-1, N-1] = 1
        return M
    # G-invariance spot check
    k0 = els[1]
    A0 = act(k0)
    assert A0.T * E * A0 == E, "G-symplectic gate FAIL"
    # packet projector P = (dimchi/|G|) sum psi(k^{-1}) act(k); psi(k^{-1})=psi(k)
    Pnum = sum(psi(k) * act(k) for k in els)   # = (|G|/dimchi) P, integer matrix
    scale = n // dimchi                        # P = Pnum/scale... check: e = (dim/|G|) sum
    # e_packet = (dimchi/n) * sum psi(k^{-1}) k  => P = (dimchi/n) Pnum
    M_iso = scale * identity_matrix(ZZ, N) - Pnum   # kernel = isotypic lattice (saturated)
    Lam = M_iso.right_kernel().basis_matrix()
    r_iso = Lam.nrows()
    out = {"kind": kind, "g": int(g), "rank_iso": int(r_iso)}
    if kind in ("Z3", "Z6"):
        B = Lam
        expect = 4 * (g - 1)
    else:
        # multiplicity-1 copy: intersect with ker(act(tau) - 1), tau = transposition
        tau = ((1, 0, 2), 0)
        Mtau = act(tau) - identity_matrix(ZZ, N)
        stack = block_matrix(ZZ, [[M_iso], [Mtau]])
        B = stack.right_kernel().basis_matrix()
        out["rank_tauinv"] = int(B.nrows())
        expect = 8 * (g - 1)
    Gram = B * E * B.T
    eds = [d for d in Gram.elementary_divisors() if d != 0]
    # alternating: divisors in pairs
    pairs = eds[::2]
    assert eds[1::2] == pairs, f"SNF pairing anomaly: {eds}"
    pf = 1
    for d in pairs:
        pf *= d
    out.update({"rank_used": int(B.nrows()), "expected": int(expect),
                "type": [int(d) for d in pairs], "Pf": int(pf),
                "v2": int(ZZ(pf).valuation(2)) if pf != 0 else None,
                "v3": int(ZZ(pf).valuation(3)) if pf != 0 else None})
    return out

results = []
# GATE: cyclic law (1^{g-1}, 3^{g-1}) at base genus 4 (house-verified) and 2
for g in (2, 4):
    r = model("Z3", g)
    r["gate_LO"] = (r["type"] == [1]*(g-1) + [3]*(g-1))
    results.append(r)
    print(r, flush=True)
# GATE 2: Z6 primitive packet at base genus 4 must reproduce the house mu6
# verdict (2,2,2,6,6,6)
r = model("Z6", 4)
r["gate_mu6"] = (r["type"] == [2,2,2,6,6,6])
results.append(r); print(r, flush=True)
# THE VERDICT: S3 x Z3, base genus 2 (fourfold) and 3 (eightfold)
for g in (2, 3):
    r = model("S3xZ3", g)
    results.append(r)
    print(r, flush=True)
with open("integral_model_s3.json", "w") as fh:
    json.dump(results, fh, default=int)
print("S3 MODEL DONE", flush=True)
