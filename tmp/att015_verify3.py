"""part 3: is the 'resonance threshold n > gamma_1^2 log m' the controlling scale, or is it
   (i) the M=32 truncation and (ii) the onset of Szego's own asymptotic?

   DISCRIMINATOR.  The two stories have OPPOSITE m-dependence:
     gamma_1 story : threshold n_* = gamma_1^2 log m  = 199.8 log m   -> INCREASES with m
     Szego onset   : L_{n-1}^{(1)}(x) ~ n^{1/4}x^{-3/4}cos(2 sqrt(nx)+..)/sqrt(pi) needs
                     enough oscillation, i.e. 2 sqrt(n x) >~ const              -> DECREASES with m
   Measure, per single line m, the smallest n where the EXACT Laguerre term and its Szego
   asymptotic agree to 10% in envelope over a sliding window.  NO zeros enter this at all.
"""
import math, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from att015_verify import laguerre_alpha1_table, prime_powers, score, detrend
from mpmath import mp
def P(*a): print(*a); sys.stdout.flush()

NB = 8000
ms = [2,3,4,5,7,8,9,11,13,17,19,23,31]
xs = np.array([math.log(m) for m in ms])
T = laguerre_alpha1_table(xs, NB)                  # T[k] = L_k^{(1)}(x), k=0..NB-1
nn = np.arange(1, NB+1, dtype=float)
P(" per-line onset of the Szego asymptotic (exact Laguerre vs Szego), NO zeros involved")
P(f"  {'m':>4}{'log m':>8}{'gamma1^2 log m':>16}{'measured onset n*':>19}{'Szego 1/log m fit':>20}")
for i, m in enumerate(ms):
    x = xs[i]
    ex = np.exp(-x/2)*T[:, i]                              # e^{-x/2} L_{n-1}^{(1)}(x)
    asy = nn**0.25 * x**-0.75 * np.cos(2*np.sqrt(nn*x) + math.pi/4)/math.sqrt(math.pi)
    # envelope comparison over a sliding half-decade window
    onset = None
    for lo in range(5, NB//2):
        hi = int(lo*1.5)+2
        if hi >= NB: break
        a = ex[lo-1:hi].std(); b = asy[lo-1:hi].std()
        rel = abs(a-b)/b
        if rel < 0.10:
            # require it to STAY under 10% for the next 3 windows
            ok = True
            for lo2 in (int(lo*1.3), int(lo*1.7), int(lo*2.2)):
                hi2 = int(lo2*1.5)+2
                if hi2 >= NB: continue
                if abs(ex[lo2-1:hi2].std()-asy[lo2-1:hi2].std())/asy[lo2-1:hi2].std() > 0.10:
                    ok = False; break
            if ok:
                onset = lo; break
    P(f"  {m:>4}{x:>8.4f}{199.8*x:>16.1f}{(onset if onset else -1):>19}"
      f"{57.5/x:>20.1f}")

P("\n sanity: mpmath check of the two Laguerre values used in the M=1e6 R2 test")
mp.dps = 40
for (k, x) in ((39, math.log(1e6)),):
    P(f"  L_{k}^(1)({x:.4f}): recurrence {laguerre_alpha1_table([x], k+1)[k,0]:.10g}  "
      f"mpmath {float(mp.laguerre(k,1,x)):.10g}")
    P(f"  L_40({x:.4f}): mpmath {float(mp.laguerre(40,0,x)):.10g}")

P("\n Y vs O(M=1000) at n=1..40 (the window the record says must FAIL)")
Y = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'att015_verify_Y8000.npy'))
from att015_verify import line_prediction
for M in (32, 1000):
    msM, lmM = prime_powers(M)
    O = line_prediction(40, msM, lmM, M)
    ns = np.arange(1, 41, dtype=float)
    R2, r, Yd, Od = score(ns, Y[:40], O)
    P(f"  M={M:>6}  R2={R2:+.4f}  r={r:+.4f}   rms(Yd)={Yd.std():.5f} rms(Od)={Od.std():.5f}")
    if M == 1000:
        P("    n     Y_n^arith      O_n(1000)      Yd          Od")
        for n in (1,5,10,15,20,25,30,35,40):
            P(f"   {n:>3}  {Y[n-1]:>12.6f}  {O[n-1]:>12.6f}  {Yd[n-1]:>10.6f}  {Od[n-1]:>10.6f}")
