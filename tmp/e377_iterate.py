"""DOES THE FREE HALF ITERATE?

Every digit condition is an explicit union of intervals in p: digit j of n base p is
floor(n/p^j) - p*floor(n/p^{j+1}), and every floor(n/p^i) is monotone in p.  So

   { p : n carry-free at p }

is an explicit union of intervals -- no randomness anywhere.  The bottom digit cuts
each band's Mertens mass exactly in half (verified).  Question: does digit j cut
another half INSIDE the previous cut?

If yes:  E_band_k(n) = 2^{-(k+1)} log((k+1)/k)  deterministically, for every n,
         and sum_k of that is O(1) -- #377, with no rails and no equidistribution.

Measure mass_j(k) = sum over band-k primes with bottom j digits low of 1/p,
against 2^{-j} * (full band mass).
"""
import math
from sympy import primerange

def low_digits(n, p, j):
    """are the bottom j base-p digits of n all <= (p-1)/2 ?"""
    D = (p - 1) // 2
    m = n
    for _ in range(j):
        if m % p > D: return False
        m //= p
    return True

def ndigits(n, p):
    c = 0
    while n: c += 1; n //= p
    return c

for n in [10**7, 10**8, 10**9]:
    print("=" * 100)
    print(f"n = {n}")
    print("=" * 100)
    print(f"{'k':>3} {'band':>22} {'full':>9} " + "".join(f"{'j='+str(j):>10}" for j in range(1, 6)))
    print(f"{'':>3} {'':>22} {'':>9} " + "".join(f"{'ratio':>10}" for j in range(1, 6)))
    for k in range(1, 6):
        lo, hi = int(n ** (1.0 / (k + 1))), int(n ** (1.0 / k))
        if hi <= lo + 2: continue
        ps = [p for p in primerange(max(lo + 1, 3), hi + 1)]
        if not ps: continue
        full = sum(1.0 / p for p in ps)
        row = []
        for j in range(1, 6):
            s = sum(1.0 / p for p in ps if low_digits(n, p, j))
            row.append(s / full if full else 0.0)
        print(f"{k:>3} {'('+str(lo)+','+str(hi)+']':>22} {full:>9.5f} "
              + "".join(f"{r:>10.4f}" for r in row))
    print(f"{'':>3} {'ideal 2^-j':>22} {'':>9} "
          + "".join(f"{2.0**-j:>10.4f}" for j in range(1, 6)))
    print()

# averaged over many n, band 2 -- is the ratio stable in n or does it fluctuate?
print("=" * 100)
print("stability in n: band-2 ratios for 30 consecutive n at n ~ 10^7")
print("=" * 100)
n0 = 10**7
lo, hi = int(n0 ** (1 / 3)), int(n0 ** (1 / 2))
ps = list(primerange(lo + 1, hi + 1))
full = sum(1.0 / p for p in ps)
for j in [1, 2, 3]:
    vals = []
    for n in range(n0, n0 + 30):
        s = sum(1.0 / p for p in ps if low_digits(n, p, j))
        vals.append(s / full)
    print(f"  j={j}:  min {min(vals):.4f}  mean {sum(vals)/len(vals):.4f}  max {max(vals):.4f}"
          f"   ideal {2.0**-j:.4f}   spread {max(vals)-min(vals):.4f}")
