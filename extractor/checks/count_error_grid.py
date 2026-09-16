"""att809 -- obligation 1, step 0: how much room does the prime-clock count actually have?

797 measured |S_x - S| ONLY AT THE ORDINATES and found 1e-4..1e-2.  805 measured the ROUNDING
MARGIN at the exclusion endpoints y0 +- D and found 0.245..0.423.  If the margin equals the error
(it does, when N is an integer: v = N + (S_x - S)), those two are inconsistent by four orders.
One of them is being misread.  This resolves it by measuring |S_x - S| ON A FINE GRID.

S(t) = N(t) - theta(t)/pi - 1, with N the true counting function from the zero list, taken in the
convention that S is right-continuous away from ordinates.  Both sides use the same theta.
"""
import sys, os
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from helix_extractor import Clocks, winding as theta, mean_spacing as spacing
mp.mp.dps = 25

clocks = Clocks(100)
print(f"Selberg x = 100, {clocks.terms:,} prime powers\n")

def S_true_grid(ts, zs, base):
    """S(t) = N(t) - theta(t)/pi - 1.  base = number of zeros BELOW zs[0]; without it
    searchsorted returns a count relative to the local list and S comes out off by base."""
    zs = np.sort(zs)
    out = np.empty(len(ts))
    for i, t in enumerate(ts):
        Nt = base + int(np.searchsorted(zs, t, side='right'))
        out[i] = Nt - theta(t)/np.pi - 1.0
    return out

for k0, k1 in [(50, 70), (1000, 1015)]:
    jlo = max(1, k0-3)
    zs = np.array([float(mp.im(mp.zetazero(j))) for j in range(jlo, k1+4)])
    base = jlo - 1
    lo, hi = zs[3], zs[-4]
    ts = np.linspace(lo+1e-6, hi-1e-6, 3000)
    St = S_true_grid(ts, zs, base)
    Sx = np.array([clocks.S(t) for t in ts])
    err = np.abs(Sx - St)
    # distance to the nearest ordinate, in spacings
    d = np.min(np.abs(ts[:, None] - zs[None, :]), axis=1)/np.array([spacing(t) for t in ts])
    print(f"=== zeros {k0}..{k1}   (ordinates {lo:.3f} .. {hi:.3f}, {len(ts)} grid points) ===")
    print(f"    |S_x - S| over the whole grid: median {np.median(err):.3f}, "
          f"90th pct {np.percentile(err,90):.3f}, MAX {err.max():.3f}")
    print(f"    fraction of the grid with |S_x - S| > 1/2 : {100*np.mean(err > 0.5):.1f}%")
    print("     distance to nearest ordinate (spacings)   median err   max err   frac > 1/2")
    for a, b in [(0.0, 0.02), (0.02, 0.05), (0.05, 0.1), (0.1, 0.2), (0.2, 0.35), (0.35, 0.5)]:
        m = (d >= a) & (d < b)
        if m.sum() == 0: continue
        print(f"        [{a:.2f}, {b:.2f})   n={m.sum():>5}              {np.median(err[m]):.3f}"
              f"       {err[m].max():.3f}      {100*np.mean(err[m] > 0.5):5.1f}%")
    print()
    sys.stdout.flush()

print("=== the same, at the exact ordinates only (797's measurement, for comparison) ===")
for k in [50, 60, 1000, 1005]:
    g = float(mp.im(mp.zetazero(k)))
    Strue_mid = k - 1.5 - theta(g)/np.pi          # symmetric convention AT the ordinate
    print(f"    k = {k:>5}: |S_x(gamma) - S_mid(gamma)| = {abs(clocks.S(g) - Strue_mid):.3e}")
print("    -> 797 measured the SYMMETRIC (midpoint) value AT an ordinate, where S jumps by 1.")
print("       That is the one place the comparison is easy, and it is NOT representative.")

print("\n=== so what does the rounding margin actually track? ===")
zs = np.array([float(mp.im(mp.zetazero(j))) for j in range(995, 1012)])
print("      t - gamma_1000 (spacings)   S_x - S    margin |v - round v|   round(v) - N")
g = float(mp.im(mp.zetazero(1000))); sp = spacing(g)
for off in [-0.45, -0.2, -0.05, 0.05, 0.2, 0.45]:
    t = g + off*sp
    Nt = int(np.searchsorted(np.sort(zs), t, side='right')) + 994
    v = theta(t)/np.pi + 1.0 + clocks.S(t)
    print(f"        {off:+6.2f}                 {v - Nt:+.4f}      {abs(v-np.rint(v)):.4f}"
          f"              {int(np.rint(v)) - Nt:+d}")
