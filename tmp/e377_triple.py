"""Is the budget PAIRWISE?  If modes with support >= 3 never beat the pair modes,
the law is

   |err| << sum_i P_i + sum_{i<j} min(N, R(P_i,P_j)),      R(P,Q) <= PQ

i.e. each PAIR's product must fit under N -- not the K-fold product.  That is the
whole gain: K rails cost K^2 pairs, not N^K.

Test: 3-rail configs, sup over N <= M of the exact error, against
   pair prediction   = sum_i P_i + sum_{i<j} R_ij / pi^3
   triple resonance  = R_123 / pi^3     (support-3 modes only)
"""
import math, itertools

P3 = math.pi ** 3

def rho(p): return (p + 1) / (2 * p)

def sup_err(ps):
    M = 1
    for p in ps: M *= p
    Ds = [(p - 1) // 2 for p in ps]
    dens = 1.0
    for p in ps: dens *= rho(p)
    c = 0.0; r = [0] * len(ps); best = 0.0
    for n in range(M):
        ok = True
        for i in range(len(ps)):
            if r[i] > Ds[i]: ok = False; break
        if ok: c += 1
        for i in range(len(ps)):
            r[i] += 1
            if r[i] == ps[i]: r[i] = 0
        e = abs(c - (n + 1) * dens)
        if e > best: best = e
    return best

def R_support(ps, support, R=25):
    """max over modes whose support is exactly `support` of
       1 / (prod|alpha_i| * ||sum alpha_i/P_i||)."""
    M = 1
    for p in ps: M *= p
    best = 0.0; arg = None
    rngs = []
    for i in range(len(ps)):
        if i in support:
            lim = min(R, (ps[i] - 1) // 2)
            rngs.append([a for a in range(-lim, lim + 1) if a != 0])
        else:
            rngs.append([0])
    for combo in itertools.product(*rngs):
        A = 0; w = 1
        for i, a in enumerate(combo):
            if a == 0: continue
            A += a * (M // ps[i]); w *= abs(a)
        A %= M
        Aabs = min(A, M - A)
        if Aabs == 0: continue
        v = M / (w * Aabs)
        if v > best: best, arg = v, combo
    return best, arg

triples = [
    (11, 13, 17), (11, 13, 19), (13, 17, 19), (17, 19, 23), (19, 23, 29),
    (23, 29, 31), (29, 31, 37), (31, 37, 41), (11, 31, 41), (13, 41, 43),
    (11, 13, 23), (37, 41, 43), (11, 41, 43), (13, 19, 47),
]
print(f"{'triple':>16} {'M':>9} {'sup|err|':>9} {'sum P_i':>8} {'pairs/pi^3':>11} "
      f"{'pred':>9} {'sup/pred':>9} {'R_123/pi^3':>11} {'triple arg':>13}")
print("-" * 106)
for t in triples:
    M = t[0] * t[1] * t[2]
    s = sup_err(t)
    pairsum = 0.0
    for (i, j) in itertools.combinations(range(3), 2):
        Rv, _ = R_support(t, {i, j})
        # R_support returns M/(w*|A|) on the FULL modulus; rescale to the pair modulus
        pairsum += Rv / P3
    R3, arg3 = R_support(t, {0, 1, 2})
    pred = sum(t) + pairsum
    print(f"{str(t):>16} {M:>9} {s:>9.1f} {sum(t):>8} {pairsum:>11.1f} "
          f"{pred:>9.1f} {s/pred:>9.3f} {R3/P3:>11.1f} {str(arg3):>13}")
