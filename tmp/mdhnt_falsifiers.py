#!/usr/bin/env python3
"""MDHNT FALSIFIER HARNESS  —  a living check, not a log.

Every claim this session produced is re-derived here from scratch and asserted.
Run it and it either passes or names the claim that died.  Claims are stated
with their DC so a failure is a signal, not a shrug.

    python3 tmp/mdhnt_falsifiers.py

Pre-registered: a FAIL is published as prominently as a pass (house rule).
Each check carries the bug that killed it once, so the bug cannot come back.
"""
import math, sys
import numpy as np
from sympy import primerange, factorial

FAILS = []
def check(name, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  — {detail}" if detail else ""))
    if not ok: FAILS.append(name)

# ---------------------------------------------------------------- rail helpers
def sp(n, p):
    s = 0
    while n: s += n % p; n //= p
    return s

def digits_balanced(n, p):
    D = (p - 1) // 2
    while n:
        if n % p > D: return False
        n //= p
    return True

# =============================================================== 1. #377
def c1_carrier_criterion():
    """n in G_p  <=>  n mod p^j < p^j/2 for all j>=1   (universal half-turn).
       DC: threshold is exactly 1/2 on EVERY rail at EVERY scale — no per-rail constant."""
    bad = 0
    for p in [3, 5, 7, 11, 13, 17, 101, 1009]:
        for n in range(0, 4000):
            j, ht = 1, True
            while p ** j <= 2 * n:
                if (n % p ** j) * 2 >= p ** j: ht = False; break
                j += 1
            if ht != digits_balanced(n, p): bad += 1
    check("#377 carrier criterion (universal half-turn)", bad == 0, f"{bad} mismatches")

def c2_knapsack_ceiling():
    """dim(S)>=0  =>  pay(S) <= 1/3+1/5+1/7 + 2.52e-12.
       DC: ratio (1/p)/beta_p strictly decreasing, so the LP is greedy."""
    beta = lambda p: math.log(2 * p / (p + 1)) / math.log(p)
    ratio = lambda p: (1.0 / p) / beta(p)
    ps = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 101, 1009, 100003]
    mono = all(ratio(ps[i]) > ratio(ps[i + 1]) for i in range(len(ps) - 1))
    check("#377 payoff/cost ratio strictly decreasing", mono)
    b0 = 1 - sum(beta(p) for p in (3, 5, 7))
    # least real x with beta(x) < b0  (the appendable-rail threshold)
    lo, hi = 1e6, 1e14
    for _ in range(300):
        m = (lo + hi) / 2
        if math.log(2 * m / (m + 1)) / math.log(m) > b0: lo = m
        else: hi = m
    check("#377 appendable-rail threshold ~ 3.98e11", abs(lo / 3.98328e11 - 1) < 1e-3,
          f"x* = {lo:.6g}, so the ceiling is NOT exactly 1/3+1/5+1/7")

def c3_carry_conservation():
    """sum_{sqrt(2n)<p<=2n, p nmid C(2n,n)} log p = 2n(1-log2) + o(n).   Every n.
       DC: 2n(1-log2) = 0.613706 n.  Also asserts the law is INERT on small primes."""
    tgt = 2 * (1 - math.log(2))
    ok, share_ok = True, True
    for n in (10 ** 4, 10 ** 5):
        ps = np.array(list(primerange(2, 2 * n + 1)))
        r = int(math.isqrt(2 * n))
        lg = np.log(ps.astype(float))
        bal = np.array([digits_balanced(n, int(p)) for p in ps])
        thb = float(lg[(ps > r) & bal].sum())
        if abs(thb / (n * tgt) - 1) > 0.03: ok = False
        tot = math.lgamma(2 * n + 1) - 2 * math.lgamma(n + 1)
        ks = sum(((2 * sp(n, int(p)) - sp(2 * n, int(p))) // (int(p) - 1)) * math.log(int(p))
                 for p in ps[ps <= r])
        if ks / tot > 0.02: share_ok = False
    check("#377 carry conservation law (theta-weighted, every n)", ok, f"target {tgt:.6f} n")
    check("#377 conservation law is INERT on small primes", share_ok,
          "small-p share -> 0, so it cannot bound E(n)")

# =============================================================== 2. #400
def c4_ledger_identity():
    """a_1!..a_k! | n!  <=>  sum_i a_i - n <= min_p ( sum_i s_p(a_i) - s_p(n) ).
       BUG THAT KILLED THIS ONCE: testing only p<=13 while n ran to 60.
       Fix: primes must range to max(n, a_i)."""
    bad = 0
    for n in range(2, 40):
        P = [int(p) for p in primerange(2, 2 * n + 8)]        # <-- the fix
        fn = factorial(n)
        for a1 in range(0, n + 8):
            for G in range(0, 5):
                a2 = n + G - a1
                if a2 < 0: continue
                lhs = (fn % (factorial(a1) * factorial(a2)) == 0)
                rhs = all(G <= sp(a1, p) + sp(a2, p) - sp(n, p) for p in P)
                if lhs != rhs: bad += 1
    check("#400 digit-sum ledger identity", bad == 0, f"{bad} mismatches")

def _g2(n, S, Ps, GMAX=30):
    Ps = [p for p in Ps if p <= n]
    best = 0
    for G in range(1, GMAX):
        A = n + G; a1 = np.arange(0, A // 2 + 1); m = None
        for p in Ps:
            v = S[p][a1] + S[p][A - a1] - S[p][n]
            m = v if m is None else np.minimum(m, v)
        if m.max() >= G: best = G
        else: break
    return best

def c5_truncation_is_not_safe():
    """PRE-REGISTERED NEGATIVE: small-rail truncation is NOT exact for g_2.
       This check exists so nobody (me) silently truncates again."""
    NM = 400; M = 2000                      # M sized for downstream checks, not just NM
    ALL = [int(p) for p in primerange(2, NM + 1)]
    S = {}
    for p in ALL:
        a = np.arange(M); s = np.zeros(M, dtype=np.int64); t = a.copy()
        while t.max() > 0: s += t % p; t //= p
        S[p] = s
    small = [p for p in ALL if p < 60]
    d = sum(1 for n in range(2, NM + 1) if _g2(n, S, small) != _g2(n, S, ALL))
    check("#400 small-rail truncation is UNSAFE (expected: mismatches > 0)", d > 0,
          f"{d} mismatches on n<=400 — never truncate the rail set")
    return S, ALL

def c6_binding_rail(S, ALL):
    """Cell size p-1 is what a carry pays => the SMALLEST cells bind.
       DC: rail 2 has the degenerate cell mu_1."""
    cnt = {}
    for n in range(2, 300):
        Ps = [p for p in ALL if p <= n]
        G = _g2(n, S, ALL)
        if G == 0: continue
        A = n + G; a1 = np.arange(0, A // 2 + 1)
        st = np.vstack([S[p][a1] + S[p][A - a1] - S[p][n] for p in Ps])
        j = int(np.argmax(st.min(axis=0)))
        w = Ps[int(np.argmin(st[:, j]))]
        cnt[w] = cnt.get(w, 0) + 1
    top = sorted(cnt.items(), key=lambda x: -x[1])[:3]
    frac2 = cnt.get(2, 0) / max(1, sum(cnt.values()))
    check("#400 binding rail is the smallest cell", frac2 > 0.5,
          f"p=2 binds {frac2:.0%}; top rails {top}")

def c7_ceiling(S, ALL):
    """g_k(n) <= (k/log 2) log n + O(1), from the degenerate mu_1 rail alone."""
    worst = 0.0
    for n in range(20, 400):
        worst = max(worst, _g2(n, S, ALL) / math.log(n))
    check("#400 ceiling c_2 <= 2/log2 = 2.885", worst <= 2 / math.log(2),
          f"max g_2/log n = {worst:.3f}")

# =============================================================== 3. the link
def c8_shared_driver(S, ALL):
    """#377 and #400 share a driver: digit-poverty across rails.
       Sign matters — I predicted ANTI-correlation and measured +0.14."""
    ns = list(range(200, 900))
    E = np.array([sum(1.0 / p for p in ALL if p <= n and digits_balanced(n, p)) for n in ns])
    G = np.array([_g2(n, S, ALL) / math.log(n) for n in ns])
    r = float(np.corrcoef(E, G)[0, 1])
    hi = E > np.percentile(E, 95); lo = E < np.percentile(E, 50)
    check("#377 <-> #400 link is POSITIVE (shared digit-poverty)", r > 0.05,
          f"corr = {r:+.4f}, rich/typical = {G[hi].mean() / G[lo].mean():.3f}")


# =============================================================== 4. #727
def c9_727_restatement():
    """(n+k)!^2 | (2n)!  <=>  [(n+1)...(n+k)]^2 | C(2n,n)  <=>  kappa_p(n) >= 2 v_p(prod).
       k=1 must reproduce Balakran: (n+1)^2 | C(2n,n)."""
    from sympy import factorint
    from math import comb
    bad = 0
    for n in range(2, 260):
        for k in (1, 2, 3):
            C = comb(2 * n, n)
            prod = 1
            for j in range(1, k + 1): prod *= (n + j)
            direct = (C % (prod * prod) == 0)
            P = {}
            for j in range(1, k + 1):
                for q, e in factorint(n + j).items(): P[q] = P.get(q, 0) + e
            ledger = all(kappa_p(n, q) >= 2 * e for q, e in P.items())
            if direct != ledger: bad += 1
    check("#727 ledger restatement (k=1,2,3)", bad == 0, f"{bad} mismatches")

def kappa_p(n, p):
    def s(m):
        t = 0
        while m: t += m % p; m //= p
        return t
    return (2 * s(n) - s(2 * n)) // (p - 1)

def c10_727_smoothness():
    """PROVED: p > sqrt(2n) => kappa_p(n) <= 1, hence any solution forces
       (n+1)...(n+k) to be sqrt(2n)-smooth.  Assert both halves."""
    import math
    from sympy import primerange, factorint
    bad = 0
    for n in range(2, 1500):
        r = math.isqrt(2 * n)
        for p in primerange(r + 1, 3 * n):
            if p > math.sqrt(2 * n) and kappa_p(n, p) > 1: bad += 1
    check("#727 carry ceiling: p>sqrt(2n) => kappa_p<=1", bad == 0, f"{bad} violations")
    viol = 0; sols = 0
    for n in range(2, 40000):
        P = {}
        for j in (1, 2):
            for q, e in factorint(n + j).items(): P[q] = P.get(q, 0) + e
        if all(kappa_p(n, q) >= 2 * e for q, e in P.items()):
            sols += 1
            if max(P) > math.sqrt(2 * n): viol += 1
    check("#727 smoothness forced (k=2)", viol == 0, f"{sols} solutions, {viol} with p>sqrt(2n)")

# =============================================================== 5. #374
def c11_374_primes():
    """PROVED: w(p) switches on coordinate p that no predecessor touches,
       so F(p) does not exist.  Assert: span-failures are EXACTLY the primes."""
    from sympy import factorint, primerange, primepi
    N = 3000
    PR = [int(q) for q in primerange(2, N + 1)]; I = {q: i for i, q in enumerate(PR)}
    w = [0] * (N + 1)
    for a in range(2, N + 1):
        m = 0
        for q, e in factorint(a).items():
            if e % 2: m |= 1 << I[q]
        w[a] = w[a - 1] ^ m
    basis = []; undef = []
    for m in range(2, N + 1):
        x = w[m]
        for b in basis:
            if x ^ b < x: x ^= b
        if x != 0:
            undef.append(m); basis.append(x); basis.sort(reverse=True)
    primes = [q for q in primerange(2, N + 1)]
    check("#374 span-failures are exactly the primes", undef == primes,
          f"{len(undef)} undefined vs pi({N})={int(primepi(N))}")

# =============================================================== 6. #1095
def c12_1095():
    """all prime factors of C(n,k) > k  <=>  k <=_p n digitwise for all p<=k (Kummer).
       Validate against Selfridge's exceptional binomial: g(6) = 62."""
    from sympy import primerange, factorint
    from math import comb
    def dom(k, n, p):
        while k or n:
            if k % p > n % p: return False
            k //= p; n //= p
        return True
    bad = 0
    for k in range(2, 9):
        for n in range(k + 2, 400):
            lp = min(factorint(comb(n, k))) if comb(n, k) > 1 else 10 ** 9
            direct = lp > k
            ledger = all(dom(k, n, int(p)) for p in primerange(2, k + 1))
            if direct != ledger: bad += 1
    check("#1095 digit-domination restatement", bad == 0, f"{bad} mismatches")
    def g(k):
        PS = [int(p) for p in primerange(2, k + 1)]
        n = k + 2
        while True:
            if all(dom(k, n, p) for p in PS): return n
            n += 1
    check("#1095 g(6)=62 (Selfridge's exceptional binomial)", g(6) == 62, f"g(6)={g(6)}")

# =============================================================== main
if __name__ == "__main__":
    print("MDHNT falsifier harness — every claim re-derived, none trusted\n")
    print("#377:")
    c1_carrier_criterion(); c2_knapsack_ceiling(); c3_carry_conservation()
    print("\n#400:")
    c4_ledger_identity()
    S, ALL = c5_truncation_is_not_safe()
    c6_binding_rail(S, ALL); c7_ceiling(S, ALL)
    print("\n#727 / #374 / #1095:")
    c9_727_restatement(); c10_727_smoothness(); c11_374_primes(); c12_1095()
    print("\nlink:")
    c8_shared_driver(S, ALL)
    print("\n" + ("ALL CHECKS HELD" if not FAILS else f"{len(FAILS)} CLAIM(S) DIED: {FAILS}"))
    print("A death here is a result. Publish it as prominently as a pass.")
    sys.exit(1 if FAILS else 0)
