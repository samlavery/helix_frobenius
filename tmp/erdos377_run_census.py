"""Run-length / hugging census: champions vs balanced base rate.

H1 (pricing frame): champions show EXCESS boundary-hugging per rail
    (longest max-digit runs, fragility functional Phi = sum -log2(2*margin))
    beyond random balanced ladders at matched depth.
H2 (base rate): per-rail structure is typical; only the NUMBER of
    simultaneously balanced rails is exceptional (pure CRT coincidence).
"""
import numpy as np

LO, HI = 10**6, 10**7
TOPK = 2000

def primes_to(m):
    s = np.ones(m + 1, dtype=bool); s[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]

P = primes_to(int(HI**0.5) + 1)

print("scanning decade ...")
n = np.arange(LO, HI, dtype=np.int64)
M = np.zeros(HI - LO)
for p in P:
    if p == 2: continue
    half = (p - 1) // 2
    bal = np.ones(HI - LO, dtype=bool)
    q = n.copy()
    while q.max() > 0:
        bal &= (q % p) <= half
        q //= p
    bal &= (n >= p * p)
    M += np.where(bal, 1.0 / p, 0.0)
idx = np.argpartition(M, -TOPK)[-TOPK:]
champs = [(int(n[i]), float(M[i])) for i in idx]
champs.sort(key=lambda t: -t[1])
print(f"champion population: top {TOPK}, M range [{champs[-1][1]:.3f}, {champs[0][1]:.3f}]")

def ladder_stats(digs, p):
    """(longest max-digit run, Phi, depth) for a lower-half digit ladder."""
    mx = (p - 1) // 2
    run = best = 0
    for d in digs:
        run = run + 1 if d == mx else 0
        best = max(best, run)
    # margins from digits: t_j = frac(n / p^j) built from low digits
    t = 0.0
    phi = 0.0
    for d in digs:                       # j = 1, 2, ... (low to high)
        t = (t + d) / p
        m = 0.5 - t
        phi += -np.log2(max(2 * m, 1e-12))
    return best, phi, len(digs)

def digits(x, p):
    out = []
    while x:
        out.append(x % p)
        x //= p
    return out

RAILS = [3, 5, 7, 11, 13]
champ_stats = {p: [] for p in RAILS}
rail_counts, small_mass, all_mass = [], [], []
for x, m in champs:
    cnt = 0; sm = 0.0
    for p in P:
        if p == 2 or p * p > x: continue
        digs = digits(x, p)
        if all(d <= (p - 1) // 2 for d in digs):
            cnt += 1
            if p <= 13: sm += 1.0 / p
            if p in RAILS:
                champ_stats[p].append(ladder_stats(digs, p))
    rail_counts.append(cnt); small_mass.append(sm); all_mass.append(m)

rng = np.random.default_rng(377)
def control_stats(p, depth, m=5000):
    mx = (p - 1) // 2
    out = []
    for _ in range(m):
        digs = list(rng.integers(0, mx + 1, depth))
        out.append(ladder_stats(digs, p))
    return out

print(f"\nchampion rail-count: mean {np.mean(rail_counts):.1f}, max {max(rail_counts)}")
print(f"small-rail (p<=13) mass share: mean {np.mean(small_mass):.3f} of "
      f"mean M {np.mean(all_mass):.3f}")
print(f"\n{'p':>3} {'n_ch':>5} | champions: run/Phi-per-rung | controls: run/Phi-per-rung | excess")
for p in RAILS:
    cs = champ_stats[p]
    if not cs: continue
    depth = int(round(np.mean([d for _, _, d in cs])))
    ct = control_stats(p, depth)
    r_c = np.mean([r for r, _, _ in cs]);  f_c = np.mean([f / d for _, f, d in cs])
    r_0 = np.mean([r for r, _, _ in ct]);  f_0 = np.mean([f / d for _, f, d in ct])
    sd_r = np.std([r for r, _, _ in ct]) / np.sqrt(len(cs))
    z = (r_c - r_0) / max(sd_r, 1e-9)
    print(f"{p:>3} {len(cs):>5} |   {r_c:5.2f} / {f_c:5.2f}          |   "
          f"{r_0:5.2f} / {f_0:5.2f}          | run z = {z:+6.1f}")

# rail-count base rate: expected simultaneous balanced count for random n
print("\nrail-count base rate (random n, same decade, 200k sample):")
sample = rng.integers(LO, HI, 200_000)
cnts = np.zeros(len(sample), dtype=np.int64)
for p in P:
    if p == 2: continue
    half = (p - 1) // 2
    bal = np.ones(len(sample), dtype=bool)
    q = sample.copy()
    while q.max() > 0:
        bal &= (q % p) <= half
        q //= p
    bal &= (sample >= p * p)
    cnts += bal
print(f"  random: mean {cnts.mean():.2f}, max {cnts.max()};  "
      f"champions: mean {np.mean(rail_counts):.1f}")
