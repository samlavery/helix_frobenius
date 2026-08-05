"""NO DISCARD.  The bottom-digit condition is deterministic in p, not random.

  n mod p <= (p-1)/2   <==>   p in  U_m ( n/(m+1/2), n/m ]

an explicit union of intervals.  Mertens integrates it exactly:  with log m = u log n,
the reciprocal mass over u in [u1,u2] is  (1/2) log((1-u1)/(1-u2)).

  band k  =  p in (n^{1/(k+1)}, n^{1/k}]   <==>  u in [1-1/k, 1-1/(k+1))
  => mass of carry-at-bottom-digit primes in band k  =  (1/2) log((k+1)/k)
     = EXACTLY HALF the band's full Mertens mass, for EVERY n.

  band 1 has only 2 digits and the top one is automatic for p > sqrt(2n), so band 1 is
  fully evaluated: E_band1(n) = (log 2)/2 = 0.346574, no discard.

Test all of it directly.
"""
import math
from sympy import primerange

def bottom_ok(n, p): return n % p <= (p - 1) // 2

def carryfree(n, p):
    m = n
    D = (p - 1) // 2
    while m:
        if m % p > D: return False
        m //= p
    return True

print("=" * 96)
print("1. BAND 1 fully evaluated:  sum_{sqrt(n)<p<=n} 1/p [n carry-free at p]  ->  (log2)/2")
print("=" * 96)
print(f"{'n':>12} {'band-1 carry-free mass':>24} {'(log2)/2':>10} {'diff':>10} {'full band1 mass':>16}")
target = math.log(2) / 2
for n in [10**4, 3 * 10**4, 10**5, 3 * 10**5, 10**6, 3 * 10**6, 10**7]:
    lo = int(math.isqrt(n))
    s = fu = 0.0
    for p in primerange(lo + 1, n + 1):
        fu += 1.0 / p
        if carryfree(n, p): s += 1.0 / p
    print(f"{n:>12} {s:>24.6f} {target:>10.6f} {s-target:>+10.6f} {fu:>16.6f}")

print("\n" + "=" * 96)
print("2. HALF OF EVERY BAND:  bottom-digit condition alone, band k, vs (1/2)log((k+1)/k)")
print("=" * 96)
n = 10**7
print(f"n = {n}")
print(f"{'k':>4} {'range':>26} {'bottom-ok mass':>15} {'(1/2)log((k+1)/k)':>18} {'full mass':>11} {'ratio':>7}")
for k in range(1, 9):
    lo = int(n ** (1.0 / (k + 1)))
    hi = int(n ** (1.0 / k))
    if hi <= lo: continue
    s = fu = 0.0
    for p in primerange(max(lo + 1, 3), hi + 1):
        fu += 1.0 / p
        if bottom_ok(n, p): s += 1.0 / p
    pred = 0.5 * math.log((k + 1) / k)
    print(f"{k:>4} {'('+str(lo)+','+str(hi)+']':>26} {s:>15.6f} {pred:>18.6f} {fu:>11.6f} "
          f"{s/fu if fu else 0:>7.4f}")

print("\n" + "=" * 96)
print("3. Is the half-selection uniform in n?  (band 1, many n)")
print("=" * 96)
n0 = 10**6
vals = []
for n in range(n0, n0 + 40):
    lo = int(math.isqrt(n))
    s = sum(1.0 / p for p in primerange(lo + 1, n + 1) if carryfree(n, p))
    vals.append(s)
print(f"  n in [{n0}, {n0+39}]:  min {min(vals):.6f}   mean {sum(vals)/len(vals):.6f}   "
      f"max {max(vals):.6f}   target {target:.6f}")
print(f"  spread {max(vals)-min(vals):.6f}   (1/log n = {1/math.log(n0):.6f})")
