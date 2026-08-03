"""Erdos #731 house probe: the uniform carry law and the least non-divisor.

Theorem (A) target: alpha_p(n) := v_p(C(2n,n)) * log p / log n -> 1/2 for a.a. n,
uniformly for p <= 2 log n  (Pomerance rev2 p.3 flags this as doable, unwritten;
Kummer: v_p = number of carries doubling n in base p; stationary carry rate = 1/2).

Theorem (B) target: least non-divisor L(n) = min_p p^{v_p(n)+1} = n^{1/2+o(1)} a.a.
Two channels can achieve the min:
  (i) small-p valuation channel: p^{v_p+1} with v_p ~ (1/2) log_p n
  (ii) balanced-prime channel: least p with v_p = 0 (n p-balanced), typically ~ c*sqrt(n)
Probe measures both, plus the concentration/uniformity that the proof must control.
"""

import numpy as np
from sympy import primerange
from math import log, sqrt

N = 200_000
ns = np.arange(N + 1)
PMAX = 1000            # covers the balanced-prime channel up to sqrt(2N) ~ 632
primes = np.array(list(primerange(2, PMAX + 1)))
print(f"N = {N}, primes to {PMAX}: {len(primes)}")

# v_p(C(2n,n)) = carries doubling n base p, vectorized carry chain per prime
V = {}
for p in primes:
    q = ns.copy()
    carry = np.zeros(N + 1, dtype=np.int64)
    v = np.zeros(N + 1, dtype=np.int64)
    while q.max() > 0 or carry.max() > 0:
        d = q % p
        c2 = (2 * d + carry) >= p
        v += c2
        carry = c2.astype(np.int64)
        q //= p
    V[p] = v

# sanity: v_2(C(2n,n)) = s_2(n)  (Kummer classic)
s2 = np.zeros(N + 1, dtype=np.int64)
q = ns.copy()
while q.max() > 0:
    s2 += q % 2
    q //= 2
assert np.all(V[2][2:] == s2[2:]), "Kummer sanity FAILED"
print("anchor: v_2 = s_2(n) exact for all n")

# ---- Theorem (A): alpha_p concentration and uniformity ----
lo = N // 2
lg = np.log(ns[lo:])
print("\nalpha_p = v_p * log p / log n  over n in [N/2, N]:")
print("  p     mean     sd      P(|a-1/2|>0.1)   digits D~log n/log p")
for p in [2, 3, 5, 7, 11, 13, 17, 23, 31, 43, 61, 89, 127, 181, 251, 367, 499, 631, 997]:
    if p not in V: continue
    a = V[p][lo:] * log(p) / lg
    D = log(N) / log(p)
    print(f"  {p:4d}  {a.mean():.4f}  {a.std():.4f}     {(np.abs(a-0.5)>0.1).mean():.4f}          {D:.1f}")

print(f"\nPomerance checks: mean alpha_2 = {(V[2][lo:]*log(2)/lg).mean():.4f} (his 1/2);"
      f"  mean alpha_3 = {(V[3][lo:]*log(3)/lg).mean():.4f} (his lower bd 34/81 = {34/81:.4f})")

# ---- Theorem (B): least non-divisor, channel census ----
# L(n) = min over p of p^{v_p+1}; log-scale to avoid overflow
logL = np.full(N + 1, np.inf)
argp = np.zeros(N + 1, dtype=np.int64)
for p in primes:
    cand = (V[p] + 1) * log(p)
    upd = cand < logL
    logL[upd] = cand[upd]
    argp[upd] = p
# exclude n where the min might lie beyond PMAX (balanced prime > PMAX):
# for n <= N, the valuation channel at p=2 gives 2^{s2+1}; log2(2sqrt n) ~ safe; the
# balanced channel needs p up to ~ sqrt(2n) < PMAX for n <= PMAX^2/2 = 500k ✓ covered.
ok = ns >= 100
ratio = logL[ok] / np.log(ns[ok])
print(f"\nleast non-divisor exponent  log L / log n  (n >= 100):")
print(f"  mean {ratio.mean():.4f}   sd {ratio.std():.4f}   "
      f"quantiles 1/25/50/75/99%: {np.percentile(ratio, [1,25,50,75,99]).round(4)}")

# channel census: was the min achieved with v_p = 0 (balanced prime) or v_p >= 1?
vmin = np.array([V[argp[n]][n] for n in range(100, N + 1)])
bal = (vmin == 0)
print(f"  min achieved via balanced prime (v=0): {bal.mean():.4f};  "
      f"via valuation channel: {(~bal).mean():.4f}")
pm = argp[100:]
print(f"  argmin prime census: p=2: {(pm==2).mean():.4f}, p=3: {(pm==3).mean():.4f}, "
      f"p=5: {(pm==5).mean():.4f}, p>10: {(pm>10).mean():.4f}, p>100: {(pm>100).mean():.4f}")

# second-order: spread of log L - (1/2) log n against sqrt(log n) scaling
dev = (logL[ok] - 0.5*np.log(ns[ok])) / np.sqrt(np.log(ns[ok]))
print(f"  normalized deviation (logL - .5 log n)/sqrt(log n): mean {dev.mean():.4f} sd {dev.std():.4f}")

# direct verification on small n: L(n) by brute force vs formula
from math import comb
bad = 0
for n in range(100, 400):
    c = comb(2*n, n)
    d = 2
    while c % d == 0: d += 1
    if abs(log(d) - logL[n]) > 1e-9: bad += 1
print(f"\ndirect check n in [100,400): mismatches = {bad}")
print("done.")
