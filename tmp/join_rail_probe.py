"""Join-rail probe: is the #377 transversality deficit visible as a rail-15 quantity?

G_p = {n : every base-p digit < p/2}.  beta_3 = 1 - log2/log3, beta_5 = 1 - log3/log5.
Independence predicts |G_3 ∩ G_5 ∩ [1,N]| ~ N^s, s = 1 - beta_3 - beta_5 = 0.3135.

Rail-carry reading (Sam): rails 3 and 5 carry-create rail 15; the joint constraint
lives on the join rail's cells with carry-mediated memory.  Measured here:
  1. counting exponent AND its multiplicative wobble across scales 3^m
     (uniform-constant transversality dies by log-periodic blowup, so measure it)
  2. independence ratio  R(X) = |G3∩G5∩[0,X)| * X / (|G3∩[0,X)| * |G5∩[0,X)|)
     — flat R ⟺ uniform constant plausible; growing R = the enemy
  3. base-15 block entropies H_1, H_2/2 of the member process vs target rate
     s*log15 = 0.849 nats/digit — the gap = carry-memory depth on the join rail
  4. rail-105 census below 10^7 (verify cold-solver's count of G3∩G5∩G7)
"""

import numpy as np
from math import log

b3 = 1 - log(2)/log(3); b5 = 1 - log(3)/log(5); s = 1 - b3 - b5
print(f"beta_3={b3:.4f} beta_5={b5:.4f}  s=1-b3-b5={s:.4f}  target rate {s*log(15):.4f} nats/digit")

# ---- enumerate G_3 below 3^22 (digits in {0,1}) and filter 5-balanced ----
M3 = 22
pows = 3 ** np.arange(M3, dtype=np.int64)
bits = np.arange(2 ** M3, dtype=np.int64)
G3 = np.zeros(2 ** M3, dtype=np.int64)
for i in range(M3):
    G3 += ((bits >> i) & 1) * pows[i]
# 5-balanced filter
q = G3.copy()
ok = np.ones(G3.shape, dtype=bool)
while q.max() > 0:
    ok &= (q % 5) <= 2
    q //= 5
members = np.sort(G3[ok & (G3 > 0)])
print(f"|G3 ∩ [1,3^{M3})| = {2**M3 - 1};  |G3∩G5| members found: {len(members)}")

# exact count of 5-balanced integers < X by digit DP
def count_bal(X, p):
    digs = []
    x = X
    while x > 0:
        digs.append(x % p); x //= p
    digs = digs[::-1]
    half = (p - 1) // 2
    total, tight = 0, True
    full = half + 1  # allowed digit values 0..half
    for i, d in enumerate(digs):
        rem = len(digs) - i - 1
        lim = min(d, full)
        total += lim * (full ** rem) if tight else 0
        if d > half:
            tight = False
            break
        # d <= half: continue tight
    return total + (1 if tight else 0)  # count includes X itself iff balanced; close enough

# ---- 1+2: exponent, wobble, independence ratio across scales ----
print("\n  m    |G3∩G5<3^m|   count/3^(m*s)    R(X) independence ratio")
for m in range(10, M3 + 1):
    X = 3 ** m
    c = int(np.searchsorted(members, X))
    g3c = 2 ** m - 1
    g5c = count_bal(X, 5)
    R = c * X / (g3c * g5c) if c else 0.0
    print(f"  {m:2d}   {c:8d}      {c / X**s:8.4f}         {R:8.4f}")

# fit exponent on top decade
ms = np.arange(14, M3 + 1)
cs = np.array([np.searchsorted(members, 3 ** m) for m in ms], dtype=float)
fit = np.polyfit(ms * log(3), np.log(cs), 1)[0]
print(f"\nfitted exponent (m=14..{M3}): {fit:.4f}   vs s = {s:.4f}")

# ---- 3: base-15 block entropies of the member process ----
def base_digits(arr, b, ndig):
    out = np.zeros((len(arr), ndig), dtype=np.int64)
    q = arr.copy()
    for i in range(ndig):
        out[:, i] = q % b
        q //= b
    return out

ND = 8
D = base_digits(members, 15, ND)
flat = D.flatten()
def H(counts):
    pr = counts / counts.sum()
    pr = pr[pr > 0]
    return float(-(pr * np.log(pr)).sum())
H1 = H(np.bincount(flat, minlength=15))
pairs = D[:, :-1] * 15 + D[:, 1:]
H2 = H(np.bincount(pairs.flatten(), minlength=225))
print(f"\nbase-15 entropies of member digit process ({len(members)} members, {ND} digits):")
print(f"  H1 = {H1:.4f}   H2/2 = {H2/2:.4f}   H2-H1 (rate est) = {H2-H1:.4f}")
print(f"  target rate s*log15 = {s*log(15):.4f}   log15 = {log(15):.4f}")
d0 = np.bincount(D[:, 0], minlength=15)
print(f"  position-0 marginal (CRT-allowed residues): {np.nonzero(d0)[0].tolist()}")
print(f"  position-0 counts: {d0[d0>0].tolist()}")

# ---- 4: rail-105 census below 10^7 ----
N7 = 10_000_000
ns = np.arange(N7 + 1, dtype=np.int64)
mask = np.ones(N7 + 1, dtype=bool)
for p in (3, 5, 7):
    q = ns.copy()
    half = (p - 1) // 2
    m_ = np.ones(N7 + 1, dtype=bool)
    while q.max() > 0:
        m_ &= (q % p) <= half
        q //= p
    mask &= m_
tri = ns[mask & (ns > 0)]
print(f"\nrail-105: |G3∩G5∩G7 ∩ [1,10^7]| = {len(tri)}  members: {tri.tolist()}")
print("done.")
