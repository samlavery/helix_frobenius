# cable instruments v1 (2026-07-27, session 18a3f704): BOTH instruments on the
# explicit Schoen fourfold (schoen_explicit config A).
#
# INSTRUMENT 1 — the squeeze census (TransportRigidity):
#   upper side: Frobenius-commutant dimensions per prime (split AND inert),
#     on H^1 (truth-gate level: Faltings pins the true answer = dim End^0(B))
#     and on H^4 = wedge^4 H^1 (the discovery level);
#   formal split-torus model from the proven relations (a*abar=b*bbar=p,
#     multiplicity 2): predicted profile {18,8x4,4x4,1x4}, D=13, Sum m^2=648;
#   lower side: seed-orbit dimension of Theta^2 under the divisor-transport
#     (Lefschetz block) algebra — on the DECOMPOSABLE fourfold the Weil plane
#     is divisor-generated (classical), so the orbit must fill the Tate block:
#     deficit 0 = truth gate; on the sixfold (queued) predicted deficit 2.
#
# INSTRUMENT 2 — the complexity census (BoundedLift):
#   separator/mixer live test on the 18-dim Tate block: random block-algebra
#   element -> distinct-eigenvalue count (separator exists?); second random
#   element -> transition graph e_j B e_i -> strong connectivity (mixer works?);
#   degree ledger: all fourfold realizers descend from char 0, so Hilbert data
#   is p-independent BY DESCENT (the tautological gate, stated); the
#   non-tautological run needs the sixfold (realizers without char-0 parents).
import sys
sys.path.insert(0, '.')
from schoen_explicit import counts_and_rail
from sage.all import PolynomialRing, QQ, ComplexField, CDF
from itertools import combinations
import json, math, random

SPLIT = [7, 31, 37, 43]
INERT = [5, 11, 17, 23]
OUT = "cable_instruments.jsonl"

# ---------- shared data path: degree-8 Frobenius poly on H^1(B) ----------
def anti_poly(p):
    s = [None]
    for k in range(1, 5):
        nCp, nC, _, _, _ = counts_and_rail(p, k)
        q = p**k
        s.append(QQ((q + 1 - nC) - (q + 1 - nCp)))
    c = [QQ(1)]
    for k in range(1, 5):
        acc = s[k]
        for i in range(1, k):
            acc += c[i]*s[k-i]
        c.append(-acc/k)
    full = c + [QQ(0)]*4
    for i in range(0, 4):
        full[8-i] = QQ(p)**(4-i) * c[i]
    R = PolynomialRing(QQ, 'T'); T = R.gen()
    return sum(full[j]*T**(8-j) for j in range(9))

def h1_roots(p):
    P = anti_poly(p)
    C100 = ComplexField(100)
    rts = []
    for r, m in P.change_ring(C100).roots():
        rts += [CDF(r)]*m
    assert len(rts) == 8, f"root count {len(rts)}"
    assert max(abs(abs(r) - float(p)**0.5) for r in rts) < 1e-7, "Weil gate"
    return rts

# ---------- profiles and commutant dimensions ----------
def cluster_profile(vals, digits=7):
    clusters = {}
    for v in vals:
        key = (round(v.real(), digits), round(v.imag(), digits))
        clusters[key] = clusters.get(key, 0) + 1
    prof = sorted(clusters.values(), reverse=True)
    tate = 0
    for k, m in clusters.items():
        if abs(CDF(k[0], k[1]) - 1) < 1e-6:
            tate = m
    return prof, sum(m*m for m in prof), tate

def census_level(p, rts):
    q = CDF(p)
    # H^1 level (truth-gate: Faltings)
    prof1, comm1, _ = cluster_profile([r/q**0.5 for r in rts])
    # H^4 level (normalized by q^2)
    vals4 = []
    for idx in combinations(range(8), 4):
        v = CDF(1)
        for i in idx:
            v *= rts[i]
        vals4.append(v/q**2)
    prof4, comm4, tate4 = cluster_profile(vals4)
    return prof1, comm1, prof4, comm4, tate4

# formal split model: {(0,0):18,(pm1,pm1):8x4,(pm2,0)/(0,pm2):4x4,(pm2,pm2):1x4}
FORMAL_PROFILE4 = sorted([18] + [8]*4 + [4]*4 + [1]*4, reverse=True)
FORMAL_COMM4 = sum(m*m for m in FORMAL_PROFILE4)   # 648
FORMAL_PROFILE1 = [2, 2, 2, 2]
FORMAL_COMM1 = 16

# ---------- the eigen-frame numerics (built at a reference split prime) ----------
def eigenframe(p):
    """basis 0..7 = (r, c): r in 4 distinct eigenvalues, c in {0=W,1=Wbar};
    the two copies of each Frobenius eigenvalue are sigma-graded (measured:
    the W-rail carries each eigenvalue once)."""
    rts = h1_roots(p)
    distinct = []
    for r in rts:
        if not any(abs(r - d) < 1e-6 for d in distinct):
            distinct.append(r)
    assert len(distinct) == 4, f"expected 4 distinct H^1 eigenvalues, got {len(distinct)}"
    # order: a, abar, b, bbar (conjugate pairs adjacent)
    a = distinct[0]
    abar = next(d for d in distinct if abs(d - a.conjugate()) < 1e-6)
    rest = [d for d in distinct if abs(d - a) > 1e-6 and abs(d - abar) > 1e-6]
    b, bbar = rest[0], next(d for d in rest if abs(d - rest[0].conjugate()) < 1e-6)
    return [a, abar, b, bbar]

SUBS = list(combinations(range(8), 4))   # H^4 basis: 4-subsets of the 8 lines
IDX = {S: n for n, S in enumerate(SUBS)}

def wedge4(g):
    """70x70 matrix of Lambda^4(g) for an 8x8 (list-of-lists CDF) g."""
    M = [[CDF(0)]*70 for _ in range(70)]
    for tn, T in enumerate(SUBS):
        cols = list(T)
        for sn, S in enumerate(SUBS):
            rows = list(S)
            # det of 4x4 submatrix g[rows, cols]
            m = [[g[rows[i]][cols[j]] for j in range(4)] for i in range(4)]
            det = (m[0][0]*(m[1][1]*(m[2][2]*m[3][3]-m[2][3]*m[3][2])
                            - m[1][2]*(m[2][1]*m[3][3]-m[2][3]*m[3][1])
                            + m[1][3]*(m[2][1]*m[3][2]-m[2][2]*m[3][1]))
                 - m[0][1]*(m[1][0]*(m[2][2]*m[3][3]-m[2][3]*m[3][2])
                            - m[1][2]*(m[2][0]*m[3][3]-m[2][3]*m[3][0])
                            + m[1][3]*(m[2][0]*m[3][2]-m[2][2]*m[3][0]))
                 + m[0][2]*(m[1][0]*(m[2][1]*m[3][3]-m[2][3]*m[3][1])
                            - m[1][1]*(m[2][0]*m[3][3]-m[2][3]*m[3][0])
                            + m[1][3]*(m[2][0]*m[3][1]-m[2][1]*m[3][0]))
                 - m[0][3]*(m[1][0]*(m[2][1]*m[3][2]-m[2][2]*m[3][1])
                            - m[1][1]*(m[2][0]*m[3][2]-m[2][2]*m[3][0])
                            + m[1][2]*(m[2][0]*m[3][1]-m[2][1]*m[3][0])))
            M[sn][tn] = det
    return M

def line(r, c):
    return 2*r + c   # basis index of eigenvalue r, copy c

def rand_block(rng):
    """random element of the divisor-transport (Lefschetz block) algebra:
    per-eigenvalue arbitrary 2x2 on the copy index (dim 16, the maximal
    Frobenius-equivariant H^1 algebra; algebraic on the decomposable
    fourfold via NS(BxB) — the truth-gate register)."""
    g = [[CDF(0)]*8 for _ in range(8)]
    for r in range(4):
        for c1 in range(2):
            for c2 in range(2):
                g[line(r, c1)][line(r, c2)] = CDF(rng.gauss(0, 1), rng.gauss(0, 1))
    return g

def sigma_mat():
    z3 = CDF(math.cos(2*math.pi/3), math.sin(2*math.pi/3))
    g = [[CDF(0)]*8 for _ in range(8)]
    for r in range(4):
        g[line(r, 0)][line(r, 0)] = z3
        g[line(r, 1)][line(r, 1)] = z3**2
    return g

def mat_vec(M, v):
    return [sum(M[i][j]*v[j] for j in range(70)) for i in range(70)]

def rank_of(vectors, tol=1e-7):
    """numerical rank via Gram-Schmidt."""
    basis = []
    for v in vectors:
        w = list(v)
        for u in basis:
            coef = sum(w[i]*u[i].conjugate() for i in range(70))
            w = [w[i] - coef*u[i] for i in range(70)]
        n = math.sqrt(sum(abs(x)**2 for x in w))
        if n > tol:
            basis.append([x/n for x in w])
    return len(basis), basis

def seed_vector():
    """omega wedge omega, omega = sum_r e_(r,0) ^ e_(rbar,1) pairing model
    (a<->abar, b<->bbar; copy-crossing so the form is sigma-invariant:
    zeta3*zeta3^2 = 1)."""
    pairs = [(line(0, 0), line(1, 1)), (line(1, 0), line(0, 1)),
             (line(2, 0), line(3, 1)), (line(3, 0), line(2, 1))]
    v = [CDF(0)]*70
    for (i1, j1), (i2, j2) in combinations(pairs, 2):
        S = tuple(sorted([i1, j1, i2, j2]))
        if len(set(S)) == 4:
            # wedge sign of (i1 j1 i2 j2) -> sorted
            perm = [i1, j1, i2, j2]
            sign = 1
            for x in range(4):
                for y in range(x+1, 4):
                    if perm[x] > perm[y]:
                        sign = -sign
            v[IDX[S]] += CDF(2*sign)   # omega^2 coefficient (x2 from expansion)
    return v

def tate_block_indices(frame):
    """indices of H^4 basis monomials in the (0,0) formal class (value q^2)."""
    out = []
    for n, S in enumerate(SUBS):
        cnt = [0, 0, 0, 0]
        for i in S:
            cnt[i//2] += 1
        if cnt[0] == cnt[1] and cnt[2] == cnt[3]:
            out.append(n)
    return out

def strong_connect(adj, m):
    """simple reachability closure; True iff strongly connected."""
    for s in range(m):
        seen = {s}
        stack = [s]
        while stack:
            x = stack.pop()
            for y in range(m):
                if adj[x][y] and y not in seen:
                    seen.add(y)
                    stack.append(y)
        if len(seen) != m:
            return False
    return True

def run():
    fh = open(OUT, "a")
    print("== INSTRUMENT 1: squeeze census ==", flush=True)
    print(f"formal split-torus model: H^4 profile {FORMAL_PROFILE4}, D=13,"
          f" commutant={FORMAL_COMM4}, Tate=18 | H^1 profile {FORMAL_PROFILE1},"
          f" commutant={FORMAL_COMM1}", flush=True)
    comm4_all, comm1_all = {}, {}
    for p in SPLIT + INERT:
        try:
            rts = h1_roots(p)
            prof1, comm1, prof4, comm4, tate4 = census_level(p, rts)
            kind = "SPLIT" if p % 3 == 1 else "INERT"
            gate = (prof4 == FORMAL_PROFILE4 and comm4 == FORMAL_COMM4
                    and tate4 == 18) if kind == "SPLIT" else None
            rec = {"instrument": "squeeze", "p": int(p), "kind": kind,
                   "H1_profile": prof1, "H1_commutant": int(comm1),
                   "H4_profile": prof4, "H4_commutant": int(comm4),
                   "H4_tate": int(tate4),
                   "split_formal_gate": gate}
            comm4_all[p], comm1_all[p] = comm4, comm1
            print(rec, flush=True)
            fh.write(json.dumps(rec, default=float) + "\n"); fh.flush()
        except Exception as ex:
            print(f"p={p} ERROR {ex}", flush=True)
    if comm4_all:
        up4 = min(comm4_all.values()); up1 = min(comm1_all.values())
        print(f"census upper bounds: dim C(H^1) <= {up1} (Faltings truth-gate"
              f" level: true value = dim End^0(B));"
              f" dim C(H^4) <= {up4}", flush=True)

    print("== lower side: seed-orbit under the divisor-transport algebra ==",
          flush=True)
    ref = 7
    frame = eigenframe(ref)
    rng = random.Random(20260727)
    seed = seed_vector()
    tate_idx = tate_block_indices(frame)
    print(f"Tate block dim (formal) = {len(tate_idx)}", flush=True)
    orbit_vecs = [seed]
    for _ in range(160):
        g = rand_block(rng)
        orbit_vecs.append(mat_vec(wedge4(g), seed))
    orbit_dim, _ = rank_of(orbit_vecs)
    # sigma-only comparison orbit
    sig = wedge4(sigma_mat())
    sig_orbit = [seed]
    v = seed
    for _ in range(3):
        v = mat_vec(sig, v)
        sig_orbit.append(v)
    sig_dim, _ = rank_of(sig_orbit)
    rec = {"instrument": "squeeze-lower", "ref_prime": ref,
           "tate_block_dim": len(tate_idx),
           "seed_orbit_dim_blockalgebra": int(orbit_dim),
           "seed_orbit_deficit": int(len(tate_idx) - orbit_dim),
           "seed_orbit_dim_sigma_only": int(sig_dim)}
    print(rec, flush=True)
    fh.write(json.dumps(rec, default=float) + "\n"); fh.flush()

    print("== INSTRUMENT 2: separator/mixer live test on the Tate block ==",
          flush=True)
    # project the block algebra to the Tate monomial subspace and test the
    # two-operator criterion with random algebra elements
    m = len(tate_idx)
    best = None
    for trial in range(6):
        gA = rand_block(rng)
        A4 = wedge4(gA)
        Ablk = [[A4[tate_idx[i]][tate_idx[j]] for j in range(m)]
                for i in range(m)]
        # eigenvalues of the m x m block
        from sage.all import matrix as sage_matrix
        MA = sage_matrix(CDF, Ablk)
        evals = MA.eigenvalues()
        distinct = []
        for e in evals:
            if not any(abs(e - d) < 1e-6 for d in distinct):
                distinct.append(e)
        nsep = len(distinct)
        # mixer: second random element, transition graph via eigenvectors
        gB = rand_block(rng)
        B4 = wedge4(gB)
        Bblk = sage_matrix(CDF, [[B4[tate_idx[i]][tate_idx[j]]
                                  for j in range(m)] for i in range(m)])
        connected = None
        if nsep == m:
            D, P = MA.eigenmatrix_right()
            Pi = P.inverse()
            Bt = Pi * Bblk * P
            adj = [[abs(Bt[i][j]) > 1e-7 for j in range(m)] for i in range(m)]
            connected = strong_connect(adj, m)
        rec = {"instrument": "sepmix", "trial": trial,
               "block_dim": m, "separator_distinct_eigs": int(nsep),
               "separator_simple": bool(nsep == m),
               "mixer_strongly_connected": connected}
        print(rec, flush=True)
        fh.write(json.dumps(rec, default=float) + "\n"); fh.flush()
        if nsep == m and connected:
            best = rec
            break
    print("== degree ledger (Instrument 2, char-0 descent register) ==",
          flush=True)
    ledger = {"instrument": "degree-ledger",
              "sigma": "automorphism graph, Hilbert data constant in p (descent)",
              "block_units": "NS(BxB) divisor correspondences, Theta-bounded, "
                             "constant in p (descent)",
              "weil_realizers_fourfold": "zeta-eigen divisor products "
                             "(classical decomposable construction), constant "
                             "in p (descent)",
              "bounded_recurrence_gate": "PASS by descent (tautological on "
                             "the fourfold); non-tautological run = sixfold, "
                             "queued behind step-0",
              "criterion_instantiated": bool(best is not None)}
    print(ledger, flush=True)
    fh.write(json.dumps(ledger) + "\n"); fh.flush()
    fh.close()
    print("CABLE INSTRUMENTS DONE", flush=True)

run()
