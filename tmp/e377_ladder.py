"""Is the (1,-1) beat the whole story, or does the full resonance ladder matter?

Candidate laws for the two-rail sup error:
   B1 = (1/pi^3) * M/|q-p|                                     first beat only
   B* = (1/pi^3) * max_{alpha,beta != 0} 1/(|alpha beta| * ||alpha/p + beta/q||)
                                                               full resonance ladder
Both capped at N (here N = M, the full period).

Pairs chosen to include ones where a LATER convergent of p/q dominates the first,
i.e. |a q - b p| tiny for small a,b > 1 while |q-p| is large.
"""
import math
from fractions import Fraction

def rho(p): return (p + 1) / (2 * p)

def sup_err(p, q):
    M = p * q
    Dp, Dq = (p - 1) // 2, (q - 1) // 2
    dens = rho(p) * rho(q)
    c = 0.0; rp = rq = 0; best = 0.0; bestN = 0
    for n in range(M):
        if rp <= Dp and rq <= Dq: c += 1
        rp += 1
        if rp == p: rp = 0
        rq += 1
        if rq == q: rq = 0
        e = abs(c - (n + 1) * dens)
        if e > best: best, bestN = e, n + 1
    return best, bestN

def resonance(p, q, R=60):
    """max over small (alpha,beta) of 1/(|alpha beta| * ||alpha/p + beta/q||),
       and the argmax."""
    M = p * q
    best = 0.0; arg = None
    for a in range(-R, R + 1):
        if a == 0: continue
        for b in range(-R, R + 1):
            if b == 0: continue
            A = a * q + b * p
            A %= M
            Aabs = min(A, M - A)
            if Aabs == 0: continue
            v = M / (abs(a * b) * Aabs)
            if v > best: best, arg = v, (a, b, Aabs)
    return best, arg

pairs = [
    (101, 103), (191, 193), (419, 421), (1019, 1021), (1451, 1453),
    (89, 127), (181, 233), (401, 439), (1009, 1103),
    # ladder cases: |q-p| large but a later convergent is very sharp
    (167, 251),    # 3q - ... ; q/p ~ 3/2
    (211, 317),    # ~3/2
    (149, 373),    # ~5/2
    (127, 317),    # ~5/2
    (163, 653),    # ~4
    (241, 1447),   # ~6
]

P3 = math.pi ** 3
print(f"{'(p,q)':>13} {'g=q-p':>6} {'sup|err|':>10} {'B1':>10} {'sup/B1':>8} "
      f"{'B*':>10} {'sup/B*':>8} {'argmax (a,b,|A|)':>20}")
print("-" * 100)
for (p, q) in pairs:
    M = p * q
    s, _ = sup_err(p, q)
    B1 = M / (P3 * abs(q - p))
    Rv, arg = resonance(p, q)
    Bs = Rv / P3
    print(f"{'('+str(p)+','+str(q)+')':>13} {q-p:>6} {s:>10.1f} {B1:>10.1f} {s/B1:>8.3f} "
          f"{Bs:>10.1f} {s/Bs:>8.3f} {str(arg):>20}")
