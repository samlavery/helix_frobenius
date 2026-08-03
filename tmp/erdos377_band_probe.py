"""Numeric probe of Tao's band mechanism for Erdos #377 (all-n partial).

Criterion (Kummer, exact): v_p(C(2n,n)) = #{ j >= 1 : 2*(n mod p^j) >= p^j }.
So p does NOT divide C(2n,n)  <=>  {n/p^j} < 1/2 for every j with p^j <= 2n.

Bands: k(p) = the k with p^k <= n < p^{k+1}, i.e. p in (n^{1/(k+1)}, n^{1/k}].

Checks:
  1. Band mass: sum_{p in band k} 1/p  vs  Mertens log(1+1/k).
  2. Non-dividing mass: sum_{p not| C, band k} 1/p  vs  EGRS (6): 2^{-k} log(1+1/k).
  3. TAO'S LEMMA (empirical): using only the TOP J conditions
     ({n/p^j} < 1/2 for j in (k-J, k]) the surviving fraction of band-k primes
     should be ~ 2^{-J}, uniformly in k.  This is the entire analytic content.
"""
import numpy as np, math
from collections import defaultdict

def sieve(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]

def analyze(n, primes, Js=(1, 2, 3, 4)):
    mass_all = defaultdict(float); mass_nodiv = defaultdict(float)
    cnt_all = defaultdict(int); cnt_nodiv = defaultdict(int)
    cnt_topJ = {J: defaultdict(int) for J in Js}
    for p in primes:
        p = int(p)
        if p > n:
            break
        # band index: largest k with p^k <= n
        k = int(math.log(n) / math.log(p))
        while p**(k + 1) <= n: k += 1
        while p**k > n: k -= 1
        mass_all[k] += 1.0 / p; cnt_all[k] += 1
        # conditions {n/p^j} < 1/2 for j = 1, 2, ... while p^j <= 2n
        conds = []
        m = p
        while m <= 2 * n:
            conds.append(2 * (n % m) < m)
            m *= p
        if all(conds):
            mass_nodiv[k] += 1.0 / p; cnt_nodiv[k] += 1
        top = conds[:k]                      # j = 1..k
        for J in Js:
            if all(top[max(0, k - J):k]):    # j in (k-J, k]
                cnt_topJ[J][k] += 1
    return mass_all, mass_nodiv, cnt_all, cnt_nodiv, cnt_topJ

def report(n, primes):
    ma, mn, ca, cn, ct = analyze(n, primes)
    lln = math.log(math.log(n))
    print(f"\n===== n = {n}  (loglog n = {lln:.4f}) =====")
    print(" k  #primes   mass      Mertens   nodiv-mass  EGRS-pred  "
          "ratio(2^-k)  |  top-J surviving fraction vs 2^-J")
    tot_div_mass = 0.0
    for k in sorted(ca):
        mert = math.log(1 + 1 / k)
        egrs = 2.0**(-k) * mert
        ratio = mn[k] / ma[k] if ma[k] > 0 else float('nan')
        tj = "  ".join(
            f"J{J}:{ct[J][k]/ca[k]:.3f}/{2.0**-J:.3f}" for J in (1, 2, 3, 4)
            if k >= 1)
        print(f"{k:3d} {ca[k]:8d}  {ma[k]:8.5f}  {mert:8.5f}  "
              f"{mn[k]:9.6f}  {egrs:9.6f}  {ratio:8.5f}/{2.0**-k:8.5f}  | {tj}")
        tot_div_mass += ma[k] - mn[k]
    print(f"  sum_(p|C) 1/p = {tot_div_mass:.5f}   vs  loglog n = {lln:.5f}"
          f"   ratio = {tot_div_mass/lln:.4f}")

if __name__ == "__main__":
    NMAX = 10**8
    print("sieving to", NMAX, "...")
    P = sieve(NMAX)
    print(len(P), "primes")
    for n in (10_000_019,            # prime
              9_979_200,             # 2^6·3^4·5^2·7·11 highly composite
              99_999_989):           # prime, near 1e8
        report(n, P)
