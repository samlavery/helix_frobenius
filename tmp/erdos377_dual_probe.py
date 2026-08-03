"""Dual-search probe: can multiplier-family conservation ledgers certify the atomic budget?

Relaxed adversary: for each small rail p <= P, choose a distribution over deep states
s = n mod p^{d_p} (all CRT-free).  Constraints: for every law (a,b) in the family, the
Lambda-weighted deep carry total  sum_p log p * #{2<=j<=d_p : (a*s mod p^j)+(b*s mod p^j) >= p^j}
must EQUAL the value realized by the actual n (the family's exact coupling).  Objective:
maximize  sum_p (1/p) * P[state balanced-through-d_p]  (carry-free at levels 1..d_p under (1,1)).

Readout: LP max vs the actual n's balanced mass vs the trivial cap, as the family grows:
  F1 = {(1,1)};  F2 = F1 + threshold laws;  F3 = F2 + rail-steering shifts (p^s, 1).
Point-mass on the actual n's states is always feasible => LP max >= actual (self-check).
"""
import numpy as np
from scipy.optimize import linprog

X = 3000                      # deep-scale cutoff: levels j with p^j <= X
P = 47                        # small-rail cutoff
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

F1 = [(1, 1)]
F2 = F1 + [(1, 2), (1, 3), (2, 3), (1, 4), (3, 4), (1, 5), (2, 5), (3, 5),
           (1, 6), (1, 7), (2, 7), (4, 5)]
F3 = F2 + [(3, 1), (9, 1), (5, 1), (25, 1), (7, 1), (49, 1), (11, 1), (13, 1)]

def rail_depth(p):
    d = 0
    while p ** (d + 1) <= X:
        d += 1
    return d

RAILS = [(p, rail_depth(p)) for p in PRIMES if rail_depth(p) >= 2]

def deep_carries(p, d, a, b):
    """Vector over states s in [0, p^d): deep carry count for law (a,b)."""
    S = np.arange(p ** d, dtype=np.int64)
    c = np.zeros(p ** d, dtype=np.int64)
    for j in range(2, d + 1):
        Q = p ** j
        c += ((a * S) % Q + (b * S) % Q >= Q)
    return c

def balanced_vec(p, d):
    """Balanced-through-d indicator: no (1,1) carry at any level 1..d."""
    S = np.arange(p ** d, dtype=np.int64)
    ok = np.ones(p ** d, dtype=bool)
    for j in range(1, d + 1):
        Q = p ** j
        ok &= (2 * (S % Q) < Q)
    return ok

print(f"X={X}, rails: {[(p, d) for p, d in RAILS]}")
CARRY = {}
for p, d in RAILS:
    for (a, b) in F3:
        CARRY[(p, a, b)] = deep_carries(p, d, a, b)
BAL = {p: balanced_vec(p, d) for p, d in RAILS}
LOGP = {p: np.log(p) for p, _ in RAILS}

nvar = sum(p ** d for p, d in RAILS)
offsets, off = {}, 0
for p, d in RAILS:
    offsets[p] = off
    off += p ** d

def lp_max_balanced(n, fam):
    # required deep totals from the actual n
    req = []
    for (a, b) in fam:
        tot = 0.0
        for p, d in RAILS:
            s = n % (p ** d)
            tot += LOGP[p] * CARRY[(p, a, b)][s]
        req.append(tot)
    # objective: maximize balanced mass  ->  minimize negative
    cobj = np.zeros(nvar)
    for p, d in RAILS:
        cobj[offsets[p]:offsets[p] + p ** d] = -(1.0 / p) * BAL[p]
    # equality constraints: per-rail normalization + per-law deep totals
    rows, cols, vals, beq = [], [], [], []
    r = 0
    for p, d in RAILS:
        for s in range(p ** d):
            rows.append(r); cols.append(offsets[p] + s); vals.append(1.0)
        beq.append(1.0); r += 1
    for i, (a, b) in enumerate(fam):
        for p, d in RAILS:
            cc = CARRY[(p, a, b)]
            nz = np.nonzero(cc)[0]
            for s in nz:
                rows.append(r); cols.append(offsets[p] + s)
                vals.append(LOGP[p] * cc[s])
        beq.append(req[i]); r += 1
    from scipy.sparse import csr_matrix
    A = csr_matrix((vals, (rows, cols)), shape=(r, nvar))
    res = linprog(cobj, A_eq=A, b_eq=np.array(beq),
                  bounds=(0, None), method="highs")
    return (-res.fun if res.status == 0 else None), res.status

def actual_balanced_mass(n):
    return sum(1.0 / p for p, d in RAILS if BAL[p][n % (p ** d)])

TRIV = sum(1.0 / p for p, _ in RAILS)
rng_ns = [7640977, 6437406, 3 ** 14, 9979200, 5000011, 8675309, 9999991]
print(f"trivial cap sum(1/p) = {TRIV:.4f}\n")
print(f"{'n':>10} {'actual':>7} {'LP(F1)':>8} {'LP(F2)':>8} {'LP(F3)':>8}")
for n in rng_ns:
    act = actual_balanced_mass(n)
    row = [n, f"{act:.4f}"]
    for fam in (F1, F2, F3):
        m, st = lp_max_balanced(n, fam)
        row.append(f"{m:.4f}" if m is not None else f"inf({st})")
    print(f"{row[0]:>10} {row[1]:>7} {row[2]:>8} {row[3]:>8} {row[4]:>8}")
