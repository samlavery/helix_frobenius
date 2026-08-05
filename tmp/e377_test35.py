"""TEST 3 (freeze / Parseval-over-non-annihilator-support)
   Claim: digit 0 is FROZEN (variance ~ 0 across n -- the free half), digits >=1
   are NOT frozen and their fluctuation is Parseval over the live channels:
        Var_n( sum_p (1/p) X_p^(j)(n) )  ==  sum_p (1/p^2) rho^(j)(1-rho^(j)),
   the cross terms vanishing by exact CRT (coprime moduli), which is the
   annihilator being trivial for distinct primes.

TEST 5 (#731 upper bound via contraction)
   erdos731_note Conj 4.1 needs pairwise decorrelation at THRESHOLD depth, and
   flags the CRT window route -- which fails because p^D q^D ~ N^2 >> N.
   Measure the actual decorrelation ratio there, and the contraction bound.
"""
import math
from sympy import primerange

def rho(p, j): return ((p + 1) / (2 * p)) ** j

def low(n, p, j):
    D = (p - 1) // 2; m = n
    for _ in range(j):
        if m % p > D: return 0
        m //= p
    return 1

# ---------------------------------------------------------------- TEST 3
print("=" * 104)
print("TEST 3: is digit 0 frozen, and do digits >=1 obey Parseval over live channels?")
print("=" * 104)
N = 10 ** 7
SAMPLES = 4000
import random
random.seed(11)
ns = [random.randrange(N // 2, N) for _ in range(SAMPLES)]

print(f"N = {N},  {SAMPLES} sampled n\n")
print(f"{'band k':>7} {'range':>18} {'j':>3} {'mean':>9} {'Var measured':>13} "
      f"{'Var Parseval':>13} {'ratio':>8} {'verdict':>9}")
print("-" * 104)
for k in [1, 2, 3, 4]:
    lo, hi = int(N ** (1.0 / (k + 1))), int(N ** (1.0 / k))
    ps = [p for p in primerange(max(lo + 1, 3), hi + 1)]
    if k == 1: ps = ps[:4000]          # cap band 1 for speed
    if len(ps) < 3: continue
    for j in [1, 2, 3]:
        if j > k + 1: continue
        vals = []
        for n in ns[:800]:
            vals.append(sum(1.0 / p for p in ps if low(n, p, j)))
        m = sum(vals) / len(vals)
        var = sum((v - m) ** 2 for v in vals) / (len(vals) - 1)
        pars = sum(rho(p, j) * (1 - rho(p, j)) / p ** 2 for p in ps)
        r = var / pars if pars else 0
        verdict = "FROZEN" if r < 0.2 else ("live" if 0.5 < r < 2.0 else "?")
        print(f"{k:>7} {'('+str(lo)+','+str(hi)+']':>18} {j:>3} {m:>9.5f} {var:>13.3e} "
              f"{pars:>13.3e} {r:>8.3f} {verdict:>9}")

# ---------------------------------------------------------------- TEST 5
print()
print("=" * 104)
print("TEST 5: #731 pairwise decorrelation at THRESHOLD depth (budget p^D q^D >> N)")
print("=" * 104)
for N5 in [10 ** 6, 10 ** 7]:
    a = math.log(2) * math.log(N5)
    T = math.exp(math.sqrt(a))
    cands = [p for p in primerange(3, int(3 * T)) if p > T / 2]
    print(f"\nN = {N5}   threshold e^sqrt(a) = {T:.1f}   candidate primes {cands[:6]}")
    print(f"{'(p,q)':>11} {'D_p':>4} {'D_q':>4} {'p^D q^D / N':>13} {'|Gp|':>8} {'|Gq|':>8} "
          f"{'|Gp^Gq|':>9} {'indep pred':>11} {'ratio':>7}")
    print("-" * 104)
    for i in range(len(cands) - 1):
        for jj in range(i + 1, min(i + 3, len(cands))):
            p, q = cands[i], cands[jj]
            Dp = int(math.log(N5) / math.log(p))
            Dq = int(math.log(N5) / math.log(q))
            cp = cq = cpq = 0
            for n in range(1, N5):
                bp = low(n, p, Dp + 1); bq = low(n, q, Dq + 1)
                cp += bp; cq += bq; cpq += bp & bq
            pred = cp * cq / N5
            print(f"{'('+str(p)+','+str(q)+')':>11} {Dp+1:>4} {Dq+1:>4} "
                  f"{p**(Dp+1)*q**(Dq+1)/N5:>13.4g} {cp:>8} {cq:>8} {cpq:>9} "
                  f"{pred:>11.1f} {cpq/pred if pred else 0:>7.3f}")
