"""Test the lattice reduction of the cross-mode sum.

Claim (K=2):  cross-mode error splits as
   m != 0  (off-resonance)  ->  << P1 log M          [proven, unconditional]
   m == 0  (resonance line) ->  <= P1^2 * T(P1,P2)
with T = sum_{a=1}^{P1/2} 1/(a^2 |a P2 mod^pm P1|)   -- a pure Diophantine defect.

Generic T ~ log P1 / P1  (=> additive).  T >= 2/P1 always.
Anomalous pairs: P2 = 1 mod P1 gives T >= 1, so the bound degrades to P1^2.

Question: is the degradation REAL (observed) or an artifact of my chain?
"""
import math
from sympy import isprime

def Dset(p): return (p - 1) // 2

def X(n, p, d):
    P = p**d
    m = n % P
    for _ in range(d):
        if m % p > Dset(p): return 0
        m //= p
    return 1

def rho(p, d): return ((p + 1) / (2 * p))**d

def joint_err(N, rails):
    cnt = 0
    for n in range(N):
        ok = True
        for (p, d) in rails:
            if not X(n, p, d): ok = False; break
        if ok: cnt += 1
    main = N
    for (p, d) in rails: main *= rho(p, d)
    return cnt - main

def sgn_res(x, P):
    r = x % P
    return r - P if r > P // 2 else r

def T_defect(P1, P2):
    """T = sum_a 1/(a^2 |a P2 mod^pm P1|)"""
    tot = 0.0
    for a in range(1, P1 // 2 + 1):
        r = abs(sgn_res(a * P2, P1))
        if r == 0: continue
        tot += 1.0 / (a * a * r)
    return 2 * tot  # +- a

def shortest(P1, P2):
    """the vector (a,r) minimising a^2|r| -- the invariant nu"""
    best = (None, None, float('inf'))
    for a in range(1, P1 // 2 + 1):
        r = abs(sgn_res(a * P2, P1))
        if r == 0: continue
        if a * a * r < best[2]: best = (a, r, a * a * r)
    return best

# ---- pairs: two resonant (P2 = 1 mod P1), several generic ----
cases = [
    # (p1,d1, p2,d2, label)
    (3, 3, 109, 1, "RESONANT 109 = 1 mod 27"),
    (3, 5, 487, 1, "RESONANT 487 = 1 mod 243"),
    (5, 3, 251, 1, "RESONANT 251 = 1 mod 125"),
    (3, 3, 5, 2, "generic"),
    (3, 5, 5, 3, "generic"),
    (3, 3, 7, 2, "generic"),
    (5, 2, 7, 2, "generic"),
    (7, 2, 11, 2, "generic"),
    (11, 2, 13, 2, "generic"),
    (101, 1, 103, 1, "generic (worst in sweep)"),
    (3, 5, 241, 1, "241 = 241-243 = -2 mod 243"),
]

N = 20000
print(f"N = {N}\n")
print(f"{'pair':<22} {'label':<28} {'M/N':>9} {'|err|':>9} {'P1+P2':>8} {'ratio':>7} "
      f"{'T*P1':>7} {'nu':>10} {'nu/P1':>7} {'P1^2 T':>10}")
print("-" * 130)
for (p1, d1, p2, d2, lab) in cases:
    P1, P2 = p1**d1, p2**d2
    if P1 > P2: P1, P2 = P2, P1; p1, d1, p2, d2 = p2, d2, p1, d1
    M = P1 * P2
    err = joint_err(N, [(p1, d1), (p2, d2)])
    T = T_defect(P1, P2)
    a, r, nu = shortest(P1, P2)
    add = P1 + P2
    print(f"({P1:>5},{P2:>6})       {lab:<28} {M/N:>9.2f} {abs(err):>9.1f} {add:>8} "
          f"{abs(err)/add:>7.3f} {T*P1:>7.3f} {nu:>10} {nu/P1:>7.3f} {P1*P1*T:>10.1f}")
