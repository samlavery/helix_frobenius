"""REGISTRATION CONTRACTS.  Register one rail at a time, last rail last.

  X_K = rho_K + (1/2) tau_K,   tau_K mean-zero square wave (Lemma: c = 1/2(1+sigma))

  T_K - N prod rho  =  rho_K ( T_{K-1} - N prod_{i<K} rho )  +  (1/2) R_K
        R_K = sum_{n<=N} (prod_{i<K} X_i) tau_K

So  E_K <= rho_K E_{K-1} + (1/2)|R_K|  with rho_K ~ 1/2:  the accumulated defect is
MULTIPLIED BY ~1/2 by each new rail and one fresh correlation is added.  Hence

        E_K <= sum_m 2^{-(K-m)} |R_m| <= max_m |R_m|.

The defect does not compound across rails -- it CONTRACTS.  No product, no lattice,
no Diophantine input.  Test the recursion and the conclusion exactly.
"""
import math, itertools

def rho(p, d): return ((p + 1) / (2 * p)) ** d

def X(n, p, d):
    D = (p - 1) // 2
    m = n % p ** d
    for _ in range(d):
        if m % p > D: return 0
        m //= p
    return 1

def run(N, rails):
    K = len(rails)
    # E_K for every prefix, and R_m for every m
    E = []
    for k in range(1, K + 1):
        c = 0
        dens = 1.0
        for (p, d) in rails[:k]: dens *= rho(p, d)
        for n in range(N):
            ok = True
            for (p, d) in rails[:k]:
                if not X(n, p, d): ok = False; break
            if ok: c += 1
        E.append(abs(c - N * dens))
    R = []
    for m in range(1, K + 1):
        pm, dm = rails[m - 1]
        tot = 0.0
        for n in range(N):
            pref = 1
            for (p, d) in rails[:m - 1]:
                if not X(n, p, d): pref = 0; break
            if pref:
                tot += (2 * X(n, pm, dm) - 1) - (2 * rho(pm, dm) - 1)
        R.append(abs(tot))
    return E, R

configs = [
    [(3, 2), (5, 2), (7, 1)],
    [(3, 3), (5, 2), (7, 2), (11, 1)],
    [(5, 2), (7, 2), (11, 2)],
    [(101, 1), (103, 1)],
    [(11, 1), (13, 1), (17, 1), (19, 1), (23, 1)],
    [(3, 5), (5, 3), (7, 2), (11, 2), (13, 1)],
    [(419, 1), (421, 1)],
    [(31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1)],
]
N = 60000
print(f"N = {N}\n")
print(f"{'rails':<44} {'E_K':>9} {'max|R_m|':>9} {'E_K/max|R|':>11} {'sum P_i':>9} {'E_K/sumP':>9}")
print("-" * 100)
for rails in configs:
    E, R = run(N, rails)
    sp = sum(p ** d for (p, d) in rails)
    mx = max(R)
    lab = " ".join(f"{p}^{d}" for (p, d) in rails)
    print(f"{lab:<44} {E[-1]:>9.1f} {mx:>9.1f} {E[-1]/mx:>11.3f} {sp:>9} {E[-1]/sp:>9.3f}")
    print(f"{'   E_k ladder:':<44} " + "  ".join(f"{e:.1f}" for e in E))
    print(f"{'   |R_m| ladder:':<44} " + "  ".join(f"{r:.1f}" for r in R))
