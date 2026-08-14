"""part 6: rigorous version of the discriminator -- envelope of the EXACT single-line Laguerre
term vs its Szego tone, measured on windows containing exactly 2 full cycles."""
import math, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from att015_verify import laguerre_alpha1_table
def P(*a): print(*a); sys.stdout.flush()
NB = 4000
ms = [2,3,4,5,7,9,11,13,17,23,31]
xs = np.array([math.log(m) for m in ms])
T = laguerre_alpha1_table(xs, NB)
nn = np.arange(1, NB+1, dtype=float)
P("  exact e^{-x/2}L_{n-1}^{(1)}(x) vs Szego tone n^{1/4}x^{-3/4}cos(2sqrt(nx)-3pi/4)/sqrt(pi)")
P("  window = exactly 2 cycles.  onset = first n where L2 envelope ratio is within 10% and stays.")
P(f"  {'m':>4}{'log m':>8}{'onset n*':>10}{'ratio@n*':>10}{'ratio@n=50':>12}{'ratio@n=200':>13}"
  f"{'gamma1^2 log m':>16}")
for i, m in enumerate(ms):
    x = xs[i]
    ex = np.exp(-x/2)*T[:, i]
    asy = nn**0.25*x**-0.75*np.cos(2*np.sqrt(nn*x) - 3*math.pi/4)/math.sqrt(math.pi)
    def ratio(lo):
        # hi such that 2 sqrt(hi x) - 2 sqrt(lo x) = 4 pi
        hi = int(((2*math.sqrt(lo*x)+4*math.pi)/2)**2/x)+1
        if hi >= NB: return None
        a = np.sqrt(np.mean(ex[lo-1:hi]**2)); b = np.sqrt(np.mean(asy[lo-1:hi]**2))
        return a/b
    onset, ron = None, None
    for lo in range(3, 1500):
        r0 = ratio(lo)
        if r0 is None: break
        if abs(r0-1) < 0.10:
            if all((ratio(l2) is None or abs(ratio(l2)-1) < 0.12)
                   for l2 in (int(lo*1.5), int(lo*2.5), int(lo*4))):
                onset, ron = lo, r0; break
    r50, r200 = ratio(50), ratio(200)
    P(f"  {m:>4}{x:>8.4f}{(onset if onset else -1):>10}{(ron if ron else float('nan')):>10.3f}"
      f"{r50:>12.3f}{r200:>13.3f}{199.8*x:>16.1f}")
