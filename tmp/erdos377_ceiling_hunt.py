"""Ceiling hunt: prove-or-disprove instrument for full Erdos 377.

Constructor (from the census): champions are p-adically near smooth numbers.
Build S = prod p^{a_p} near target N, scan n = S + r over r in [0, R):
stage 1 scores tiny rails vectorized; stage 2 full mass (p <= 1e4) on finalists.
Readout: best M per decade 1e6 .. ~5e18.
  FLAT ceiling  -> budget law holds at all scales (prove-side evidence + constant).
  CLIMBING      -> disproof lead: constructible sequences with unbounded mass.
Validation: decade 1e6 must roughly reproduce the full-scan champion (0.8257).
"""
import numpy as np
from itertools import product as iproduct

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

SMALL = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]        # stage-1 scoring rails
PFULL = [p for p in primes_to(10_000) if p != 2]
R = 300_000

def stage1_scores(S, R):
    r = np.arange(R, dtype=np.int64)
    M = np.zeros(R)
    for p in SMALL:
        half = (p - 1) // 2
        bal = np.ones(R, dtype=bool)
        q = (S + r)
        while q.max() > 0:
            bal &= (q % p) <= half
            q //= p
        M += np.where(bal, 1.0 / p, 0.0)
    return M

def full_mass(n):
    tot = 0.0
    for p in PFULL:
        if p * p > n: break
        q, ok = n, True
        while q:
            if q % p > (p - 1) // 2: ok = False; break
            q //= p
        if ok: tot += 1.0 / p
    return tot

def smooth_candidates(N, count=40, seed=377):
    """Random smooth S in [N/4, N], exponents biased toward LP-ish allocation."""
    rng = np.random.default_rng(seed + int(np.log10(N)))
    out = set()
    base = [3, 5, 7, 11, 13, 17, 19, 23]
    tries = 0
    while len(out) < count and tries < 4000:
        tries += 1
        S = 1
        for p in rng.permutation(base):
            # keep multiplying by p while it fits, with decreasing probability
            while S * p <= N and rng.random() < 0.62:
                S *= p
        if N // 4 <= S <= N:
            out.add(int(S))
    return sorted(out)

print(f"{'target':>8} {'best n':>22} {'stage1':>7} {'fullM':>7}  rails(p<=31)")
for N in [10**6, 10**9, 10**12, 10**15, 5 * 10**18]:
    cands = smooth_candidates(N)
    finals = []
    for S in cands:
        M = stage1_scores(S, R)
        top = np.argpartition(M, -8)[-8:]
        for i in top:
            finals.append((float(M[i]), S + int(i)))
    finals.sort(reverse=True)
    best = (0.0, 0)
    seen = set()
    for s1, n in finals[:120]:
        if n in seen: continue
        seen.add(n)
        fm = full_mass(n)
        if fm > best[0]: best = (fm, n, s1)
    fm, n, s1 = best
    rails = [p for p in SMALL if all(
        d <= (p - 1) // 2 for d in
        (lambda x, pp: [x // pp**k % pp for k in range(0, 64) if pp**k <= x])(n, p))]
    print(f"{N:>8.0e} {n:>22d} {s1:>7.4f} {fm:>7.4f}  {rails}")
