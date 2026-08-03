"""Threading probe: instrument the position curve x -> balanced configuration.

A. Decade growth: max over x of M(x) = sum 1/p over rails p (odd, p^2 <= x) with x
   p-balanced to full depth.  Full scan to 1e7; sampled windows in the 1e8 decade.
   Question: does the champion mass saturate (~LP value 0.69-0.73) or creep?
B. Fragility: at each decade champion, the band-arrangement cell = maximal x-interval
   on which the champion's balanced rail set persists.  Cell length vs mass.
C. Clearance: per balanced rail, margins (1/2 - {x/p^j}) over the ladder - the
   renormalization data (boundary-hugging = fragile loans from the gap set).
"""
import numpy as np

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

def mass_scan(lo, hi, primes):
    """M(x) for x in [lo, hi): sum 1/p over odd p, p*p <= x, x p-balanced full depth."""
    n = np.arange(lo, hi, dtype=np.int64)
    M = np.zeros(hi - lo)
    for p in primes:
        if p == 2 or p * p > hi - 1: continue
        half = (p - 1) // 2
        bal = np.ones(hi - lo, dtype=bool)
        q = n.copy()
        while q.max() > 0:
            bal &= (q % p) <= half
            q //= p
        bal &= (n >= p * p)
        M += np.where(bal, 1.0 / p, 0.0)
    return n, M

def balanced_rails(x, primes):
    out = []
    for p in primes:
        if p == 2 or p * p > x: continue
        q, ok = x, True
        while q:
            if q % p > (p - 1) // 2: ok = False; break
            q //= p
        if ok: out.append(p)
    return out

def cell_and_margins(x, rails):
    """Maximal interval around x preserving all digit conditions of the rail set,
    plus per-rail clearance margins."""
    up, down = np.inf, np.inf
    margins = {}
    for p in rails:
        Q, ms = p, []
        while Q <= x:
            half = (Q - (Q // 2))          # ceil(Q/2): first upper-half residue
            r = x % Q
            up = min(up, half - r)          # steps until r hits upper half
            down = min(down, r + 1)         # steps until wrap below 0 -> top digit change
            ms.append(0.5 - r / Q)
            Q *= p
        margins[p] = ms
    return up, down, margins

P = primes_to(2000)
print("=== A. decade growth of champion mass (odd rails, depth >= 2) ===")
champions = []
for lo, hi in [(10**4, 10**5), (10**5, 10**6), (10**6, 10**7)]:
    n, M = mass_scan(lo, hi, P)
    i = int(np.argmax(M))
    champions.append((int(n[i]), float(M[i])))
    print(f"  decade [{lo:.0e},{hi:.0e}): max M = {M[i]:.4f} at n = {n[i]}")
best8 = (0, 0.0)
rng = np.random.default_rng(377)
windows = [int(w) for w in rng.integers(10**8, 9*10**8, 12)]
windows += [3**17, 2 * 3**16, 9699690 * 41, 9699690 * 83]
for w in windows:
    n, M = mass_scan(w, w + 10**6, P)
    i = int(np.argmax(M))
    if M[i] > best8[1]: best8 = (int(n[i]), float(M[i]))
print(f"  decade 1e8-1e9 (16 sampled 1e6-windows): max M = {best8[1]:.4f} at n = {best8[0]}")
champions.append(best8)

print("\n=== B/C. fragility + clearance at champions ===")
for x, M in champions:
    rails = balanced_rails(x, P)
    up, down, margins = cell_and_margins(x, rails)
    cell = up + down - 1
    mmin = min((min(ms) for ms in margins.values()), default=float('nan'))
    print(f"n = {x:10d}  M = {M:.4f}  rails = {rails}")
    print(f"   cell length = {int(cell)}  (up {int(up)}, down {int(down)});"
          f"  min clearance = {mmin:.5f}")
    for p in rails[:6]:
        ms = ", ".join(f"{m:.3f}" for m in margins[p])
        print(f"   p={p:5d} margins by level: [{ms}]")
