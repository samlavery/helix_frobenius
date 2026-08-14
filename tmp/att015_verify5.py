"""part 5: (a) radius stability of MY Y; (b) sensitivity of the 'threshold' to the detrend basis;
   (c) zero-count sanity for their census."""
import math, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from att015_verify import taylor_coeffs, h_arith, prime_powers, line_prediction
from mpmath import mp
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
Y = np.load(os.path.join(HERE, 'att015_verify_Y8000.npy'))

P("(a) RADIUS STABILITY: recompute lambda_n^arith at r = 0.995 (different contour, different dps)")
cz = taylor_coeffs(h_arith, '0.995', 8192, 90)
Y2 = np.array([float(cz[n-1].real) for n in range(1, 3001)])
P(f"    r=0.99 vs r=0.995, n<=3000: max |diff| = {np.abs(Y[:3000]-Y2).max():.3e}  "
  f"(rms Y = {Y[199:3000].std():.4f})")

P("\n(b) DETREND-BASIS SENSITIVITY of the dyadic R2 (M=32).")
ms32, lm32 = prime_powers(32)
O32 = line_prediction(8000, ms32, lm32, 32)
def mk(name, ns):
    if name == 'orig {1,log n,sqrt n,n}':
        return np.column_stack([np.ones_like(ns), np.log(ns), np.sqrt(ns), ns])
    if name == 'poly3 in sqrt(n)':
        v = np.sqrt(ns); return np.column_stack([np.ones_like(v), v, v**2, v**3])
    if name == 'n log n basis':
        return np.column_stack([np.ones_like(ns), ns, ns*np.log(ns)])
    if name == '{1, n}':
        return np.column_stack([np.ones_like(ns), ns])
    if name == 'poly5 in sqrt(n)':
        v = np.sqrt(ns); return np.column_stack([v**k for k in range(6)])
def sc(ns, Yv, Ov, name):
    X = mk(name, ns)
    def d(y):
        c, *_ = np.linalg.lstsq(X, y, rcond=None); return y - X@c
    Yd, Od = d(Yv), d(Ov)
    return 1 - np.sum((Yd-Od)**2)/np.sum(Yd**2), Yd.std()
wins = ((10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(200,3000))
names = ['orig {1,log n,sqrt n,n}', '{1, n}', 'n log n basis', 'poly3 in sqrt(n)', 'poly5 in sqrt(n)']
P(f"  {'window':>14}" + "".join(f"{n[:16]:>18}" for n in names))
for lo, hi in wins:
    ns = np.arange(lo, hi+1, dtype=float)
    row = f"  [{lo:>5},{hi:>5}]"
    for nm in names:
        R2, _ = sc(ns, Y[lo-1:hi], O32[lo-1:hi], nm)
        row += f"{R2:>18.4f}"
    P(row)
P("\n  same, but the detrended AMPLITUDE rms(Yd)/n^{1/4} (their 'n^{1/4} law switching on'):")
P(f"  {'window':>14}" + "".join(f"{n[:16]:>18}" for n in names))
for lo, hi in wins:
    ns = np.arange(lo, hi+1, dtype=float)
    row = f"  [{lo:>5},{hi:>5}]"
    for nm in names:
        _, a = sc(ns, Y[lo-1:hi], O32[lo-1:hi], nm)
        row += f"{a/(0.5*(lo+hi))**0.25:>18.4f}"
    P(row)

P("\n(c) census sanity: Riemann-von Mangoldt N(T) at T=30000")
T = 30000.0
NT = T/(2*math.pi)*math.log(T/(2*math.pi)) - T/(2*math.pi) + 7/8
P(f"    N(30000) ~ {NT:.1f}   their census: 35673 zeros")
g = np.load(os.path.join(HERE, 'att015_zeros_to_30000.npy'))
P(f"    stored zeros: {len(g)}, first {g[0]:.6f} (true 14.134725), last {g[-1]:.4f}")
P(f"    max consecutive gap {np.diff(g).max():.4f}, min gap {np.diff(g).min():.5f}")
