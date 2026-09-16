"""How does max|S_x - S| behave with height, at the cutoff the implementation uses (x=100)?
Rounding the count needs |S_x - S| < 1/2, not < 1.
"""
import sys, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import numpy as np, mpmath as mp
from helix_extractor import Clocks, winding
mp.mp.dps = 25
clocks = Clocks(100)

def S_true(t, zs, base):
    N = base + int(np.searchsorted(zs, t, side='right'))
    return N - winding(t)/math.pi - 1.0

print(f"{'window':>18} {'height':>12} {'median':>9} {'max |Sx-S|':>12}  >1/2?")
for k0, k1 in [(50,70), (500,520), (1000,1015), (3000,3015), (8000,8015)]:
    jlo = max(1, k0-3)
    zs = np.array([float(mp.im(mp.zetazero(j))) for j in range(jlo, k1+4)])
    base = jlo-1
    lo, hi = zs[3], zs[-4]
    ts = np.linspace(lo+1e-6, hi-1e-6, 1500)
    err = np.array([abs(clocks.S(t) - S_true(t, zs, base)) for t in ts])
    print(f"{f'gamma_{k0}-{k1}':>18} {lo:>12.1f} {np.median(err):>9.3f} {err.max():>12.3f}"
          f"  {'YES' if err.max() > 0.5 else 'no'}")
