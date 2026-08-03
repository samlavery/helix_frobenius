"""Unit-scan bank: read joint-balance survivors on ambient spin buckets mod 2k.

Unit pi/k  <->  ambient carrier buckets  n mod 2k.
For each rail set S and each unit k: total-variation distance of the survivor
distribution mod 2k from uniform, versus the SAME statistic for the level-0
CRT model (only n mod p < p/2 imposed).  excess = obs - crt  is deep-digit
structure visible only at that unit.  Method law: scan, never lock one k.
"""
import numpy as np
from math import gcd

N = 10**7
UNITS = [1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 21, 35, 105]   # k; buckets = 2k

n = np.arange(N + 1, dtype=np.int64)

def balanced(p):
    half = (p - 1) // 2
    ok = np.ones(N + 1, dtype=bool)
    q = n.copy()
    while q.max() > 0:
        ok &= (q % p) <= half
        q //= p
    ok[0] = False
    return ok

bal = {p: balanced(p) for p in (3, 5, 7)}

def tv_mod(sample, m):
    h = np.bincount(sample % m, minlength=m).astype(float)
    h /= h.sum()
    return 0.5 * np.abs(h - 1.0 / m).sum()

def crt_tv(S, m):
    # level-0 model: uniform on residues r mod L with r mod p <= (p-1)/2 all p in S
    L = m
    for p in S:
        L = L * p // gcd(L, p)
    r = np.arange(L)
    ok = np.ones(L, dtype=bool)
    for p in S:
        ok &= (r % p) <= (p - 1) // 2
    h = np.bincount(r[ok] % m, minlength=m).astype(float)
    h /= h.sum()
    return 0.5 * np.abs(h - 1.0 / m).sum()

SETS = [(3,), (5,), (7,), (3, 5), (3, 7), (5, 7), (3, 5, 7)]
print(f"N = {N};  units k -> buckets 2k;  entries: TVobs/TVcrt/excess")
hdr = "S \\ k   " + "".join(f"{k:>7d}" for k in UNITS)
print(hdr)
for S in SETS:
    ok = np.ones(N + 1, dtype=bool)
    for p in S:
        ok &= bal[p]
    surv = n[ok]
    row_o, row_c = [], []
    for k in UNITS:
        m = 2 * k
        row_o.append(tv_mod(surv, m))
        row_c.append(crt_tv(S, m))
    label = "x".join(map(str, S))
    print(f"{label:<8s}" + "".join(f"{o:7.3f}" for o in row_o) + f"   | n={len(surv)}")
    print(f"  crt   " + "".join(f"{c:7.3f}" for c in row_c))
    print(f"  exc   " + "".join(f"{o-c:+7.3f}" for o, c in zip(row_o, row_c)))
