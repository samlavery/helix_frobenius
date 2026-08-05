"""TEST B: does the contraction law hold in the DEEP regime M >> N?
   (the regime where CRT is vacuous and atomic_core_theorem invokes Corso-Shmerkin)

TEST C: does the mu6 address rule (P mod 6) predict the beat, or was that wrong?
   Prediction under test: same mu6 address => beat.  Twins p,p+2 have p=5, p+2=1
   mod 6 -- DIFFERENT addresses -- so if twins beat, the mu6 rule as I stated it
   is FALSE.  Compare against |P_i - P_j| (the beat denominator).

TEST A': do DEEP twin configs also beat, or is the beat a shallow-only artifact?
"""
import math

def rho(p, d): return ((p + 1) / (2 * p)) ** d

def X(n, p, d):
    D = (p - 1) // 2
    m = n % p ** d
    for _ in range(d):
        if m % p > D: return 0
        m //= p
    return 1

def contraction(N, rails):
    K = len(rails)
    E = []
    for k in range(1, K + 1):
        c = 0; dens = 1.0
        for (p, d) in rails[:k]: dens *= rho(p, d)
        for n in range(N):
            ok = True
            for (p, d) in rails[:k]:
                if not X(n, p, d): ok = False; break
            if ok: c += 1
        E.append(abs(c - N * dens))
    R = []
    for m in range(1, K + 1):
        pm, dm = rails[m - 1]; tot = 0.0
        for n in range(N):
            pref = 1
            for (p, d) in rails[:m - 1]:
                if not X(n, p, d): pref = 0; break
            if pref: tot += 2 * (X(n, pm, dm) - rho(pm, dm))
        R.append(abs(tot))
    return E, R

print("=" * 96)
print("TEST B: contraction in the DEEP regime (M >> N)")
print("=" * 96)
N = 30000
cfgs = [
    [(3, 6), (5, 4), (7, 3)],
    [(3, 7), (5, 5), (7, 4)],
    [(3, 5), (5, 4), (7, 3), (11, 2)],
    [(3, 6), (5, 5), (7, 4), (11, 3)],
    [(3, 8), (5, 6), (7, 4), (11, 3), (13, 2)],
]
print(f"{'rails':<36} {'M/N':>13} {'E_K':>8} {'max|R_m|':>9} {'E_K/max|R|':>11} {'sum P':>8}")
print("-" * 96)
for rails in cfgs:
    M = 1
    for (p, d) in rails: M *= p ** d
    E, R = contraction(N, rails)
    mx = max(R)
    print(f"{str(rails):<36} {M/N:>13.3g} {E[-1]:>8.2f} {mx:>9.2f} "
          f"{E[-1]/mx if mx else 0:>11.3f} {sum(p**d for p,d in rails):>8}")

print()
print("=" * 96)
print("TEST C: does mu6 address (P mod 6) predict the beat?  vs |P_i - P_j|")
print("=" * 96)

def sup_err(p, q):
    M = p * q
    Dp, Dq = (p - 1) // 2, (q - 1) // 2
    dens = rho(p, 1) * rho(q, 1)
    c = 0.0; rp = rq = 0; best = 0.0
    for n in range(M):
        if rp <= Dp and rq <= Dq: c += 1
        rp += 1
        if rp == p: rp = 0
        rq += 1
        if rq == q: rq = 0
        e = abs(c - (n + 1) * dens)
        if e > best: best = e
    return best

pairs = [(101, 103), (191, 193), (419, 421),      # twins: 5,1 mod 6 (DIFFERENT)
         (151, 157), (211, 223), (307, 313),      # gap 6: SAME mod 6
         (101, 107), (191, 197), (419, 431),      # gap 6/12: SAME mod 6
         (89, 127), (181, 233), (401, 439)]       # far
print(f"{'(p,q)':>13} {'p%6':>4} {'q%6':>4} {'same?':>6} {'gap':>5} {'sup|err|':>9} "
      f"{'p+q':>6} {'ratio':>7} {'M/(8*gap)':>10}")
print("-" * 96)
for (p, q) in pairs:
    s = sup_err(p, q)
    same = "YES" if p % 6 == q % 6 else "no"
    print(f"{'('+str(p)+','+str(q)+')':>13} {p%6:>4} {q%6:>4} {same:>6} {q-p:>5} "
          f"{s:>9.1f} {p+q:>6} {s/(p+q):>7.3f} {p*q/(8*(q-p)):>10.1f}")
