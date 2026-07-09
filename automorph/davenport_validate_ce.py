#!/usr/bin/env python3
"""
STRONGEST validation: reproduce the KNOWN rank-5 counterexample of
Geroldinger-Liebmann-Philipp (arXiv:1009.5835, proof of Thm 3.1, case i=1)
for G = C_2 (+) C_{2n}^4, n>=3 odd.

Their sequence U (length 8n-1 = d*(G)+2) is a MINIMAL zero-sum sequence, so
S* = g12^{-1} U is zero-sum-free of length d*(G)+1  ==>  d(G) >= d*(G)+1 > d*(G).

Basis (e1,...,e5): ord(e1)=2, ord(e2)=...=ord(e5)=2n.
We encode G = C_2 (+) C_{2n} (+) C_{2n} (+) C_{2n} (+) C_{2n} directly (rank 5),
using the Group class from davenport_rank3. |G| = 2 * (2n)^4.

If our tester declares S* zero-sum-free, the tester can detect a real
counterexample -- the ultimate validation before any hunt.
"""
import sys
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from davenport_rank3 import Group, is_zero_sum_free, zero_sum_free_prefix_len


def build_GLP(n):
    assert n % 2 == 1 and n >= 3
    m = 2 * n
    G = Group((2, m, m, m, m))  # e1 order 2, e2..e5 order 2n
    G.build_add_tables()

    def E(a1, a2, a3, a4, a5):
        return G.idx((a1 % 2, a2 % m, a3 % m, a4 % m, a5 % m))

    # generators from the paper (coeffs of e2..e5 are half-integers times ...,
    # all the (3n+-1)/2 etc are integers since n is odd)
    h = lambda x: x // 1  # coeffs already integer-valued below
    g1  = E(1, 1, 0, 0, 0)
    g2  = E(1, 0, 1, 0, 0)
    g3  = E(1, 0, 0, 1, 0)
    g4  = E(1, 0, 0, 0, 1)
    g5  = E(0, (3*n-1)//2, (3*n+1)//2, (3*n+1)//2, (3*n+1)//2)
    g6  = E(0, (3*n-1)//2, (3*n+1)//2, (3*n-1)//2, (n+1)//2)
    g7  = E(0, (3*n+3)//2, (n+1)//2,  (n-1)//2,  (n+1)//2)
    g8  = E(0, (n-1)//2,   (n+1)//2,  (3*n+1)//2,(n-1)//2)
    g9  = E(0, (n-1)//2,   (n+1)//2,  (n+1)//2,  (n+1)//2)
    g10 = E(0, (3*n+1)//2, (3*n+1)//2,(n+1)//2,  (3*n+1)//2)
    g11 = E(0, (n+3)//2,   (3*n+1)//2,(3*n+1)//2,(3*n-1)//2)
    g12 = E(1, (n+1)//2,   (n-1)//2,  (n+1)//2,  (3*n+1)//2)
    gens = [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12]

    # U = g1^{2n-2} g2^{2n-3} g3^{2n-2} g4^{2n-2} g5 g6 ... g12
    mult = [2*n-2, 2*n-3, 2*n-2, 2*n-2] + [1]*8
    U = []
    for gi, mi in zip(gens, mult):
        U += [gi]*mi
    return G, gens, U, mult


def group_sum(G, seq):
    s = 0
    for g in seq:
        s = G.add_idx(s, g)
    return s


def check(n):
    G, gens, U, mult = build_GLP(n)
    m = 2 * n
    d_star = G.d_star()  # 1 + 4*(2n-1) = 8n-3
    print(f"n={n}: G = C_2 (+) C_{m}^4, |G|={G.order}, d*(G)={d_star}")
    print(f"  |U| = {len(U)}  (expected 8n-1 = {8*n-1} = d*(G)+2)")

    # 1) U sums to zero (zero-sum sequence)
    su = group_sum(G, U)
    print(f"  sigma(U) = index {su}  -> {'ZERO' if su==0 else 'NONZERO (FAIL)'}")

    # 2) S* = U with one g12 removed, should be zero-sum-free of length d*(G)+1
    g12 = gens[11]
    Sstar = list(U)
    Sstar.remove(g12)   # remove exactly one copy of g12
    print(f"  |S*| = {len(Sstar)}  (expected d*(G)+1 = {d_star+1})")
    zsf = is_zero_sum_free(Sstar, G)
    print(f"  S* zero-sum-free? {zsf}  -> {'CONFIRMS d(G)>=d*+1 (COUNTEREXAMPLE DETECTED)' if zsf else 'FAIL: tester missed known counterexample'}")

    # 3) U itself must NOT be zero-sum-free (it is a zero-sum sequence)
    zsf_U = is_zero_sum_free(U, G)
    print(f"  U zero-sum-free? {zsf_U}  (must be False)  -> {'OK' if not zsf_U else 'FAIL'}")

    # 4) U is MINIMAL zero-sum: every proper nonempty subsequence is nonzero.
    #    Sufficient check here: removing any single element leaves it zero-sum-free.
    #    (full minimality is stronger; the paper proves it. We spot-check the
    #     removal-of-one-element property which is what we rely on.)
    print(f"  (removing one g12 gives zero-sum-free: {zsf})")
    ok = (su == 0) and zsf and (not zsf_U) and (len(Sstar) == d_star+1)
    print(f"  RESULT: {'PASS' if ok else 'FAIL'}")
    print()
    return ok


if __name__ == "__main__":
    allok = True
    for n in [3, 5, 7]:
        allok &= check(n)
    print("=" * 60)
    print("COUNTEREXAMPLE-DETECTION VALIDATION:", "PASSED" if allok else "FAILED")
