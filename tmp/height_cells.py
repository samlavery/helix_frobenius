"""HEIGHT-CELL TEST.  The ordinate is log(height): kClimb p y = exp y / p, height z = e^y.
Integers sit at height n (pitch 1); the carrier spins pi/3 per integer, so the cell index
at height Z is Z mod 6 and the carrier phase is Z*(pi/3) mod 2pi.

HYPOTHESIS: a vanishing sits at a harmonized CELL EDGE in HEIGHT.
  -> frac(Z) concentrates near 0 (a step/integer edge), and/or
  -> Z mod 6 concentrates near the wall class 3.
Precision: frac(e^g) needs absolute accuracy <<1 in e^g, i.e. relative <<e^-g.
Every value is recomputed at two precisions and rejected unless they agree.
"""
import mpmath as mp

def heights(K, dps):
    mp.mp.dps = dps
    out=[]
    for k in range(1, K+1):
        g = mp.im(mp.zetazero(k))
        Z = mp.e**g
        out.append((k, g, Z))
    return out

K = 40
A = heights(K, 120); B = heights(K, 200)   # two precisions
good=[]
for (k,g,Za),(k2,g2,Zb) in zip(A,B):
    fa, fb = mp.frac(Za), mp.frac(Zb)
    if abs(fa-fb) < mp.mpf(10)**(-20):     # fractional part is trustworthy
        good.append((k, float(g), Za, fb))
print(f"zeros with trustworthy frac(e^gamma): {len(good)}/{K}  (max gamma={float(good[-1][1]):.2f})")

print(f"\n{'k':>3} {'gamma':>10} {'frac(Z)':>12} {'Z mod 6':>12} {'cellphase/2pi':>14}")
fr=[]; c6=[]
for k,g,Z,f in good:
    m6 = mp.frac(Z/6)*6
    ph = mp.frac(Z/6)          # carrier phase Z*(pi/3) mod 2pi, normalised
    fr.append(float(f)); c6.append(float(m6))
    print(f"{k:>3} {g:>10.4f} {float(f):>12.6f} {float(m6):>12.6f} {float(ph):>14.6f}")

import numpy as np
fr=np.array(fr); c6=np.array(c6)
print("\n--- uniformity of frac(Z) on [0,1) ---")
print(f"  mean={fr.mean():.4f} (unif 0.5)   KS-ish max|F-U| = {np.abs(np.sort(fr)-np.linspace(0,1,len(fr))).max():.4f}")
print(f"  |mean e^{{2pi i frac}}| = {abs(np.exp(2j*np.pi*fr).mean()):.4f}   (0 = uniform, 1/sqrt(n)={1/np.sqrt(len(fr)):.4f})")
print("--- uniformity of Z mod 6 ---")
h,_=np.histogram(c6, bins=6, range=(0,6))
print(f"  counts per cell {h}   (expected {len(c6)/6:.1f})")
print(f"  |mean e^{{2pi i Z/6}}| = {abs(np.exp(2j*np.pi*c6/6).mean()):.4f}   (noise floor {1/np.sqrt(len(c6)):.4f})")
