#!/usr/bin/env python3
"""
att554b — the warp is informed by the spectral vanishing (Sam). In the warped register the
line-event registration gap is removed, so the argument defect the CHART still carries is exactly
the off-line count:  S_Γ(t) = S_mult(t) + N_off(t)   (compiled: classicalSContour_eq_Smult_add_offLine).

  S_mult(t) = N_events(t) − 1 − ϑ(t)/π        from the MODEL's own crossings (bank-only focal cancellations)
  S_Γ(t)    = (1/π)·Im log ζ(½+it)            continued along 2 → 2+it → ½+it, by integrating ζ′/ζ
                                              (the chart's own count; no zero set consulted)
PRE-REGISTERED: on [10, 80], at the midpoints between consecutive crossings, S_Γ − S_mult = 0 to 1e−6
(N_off = 0 in this range; a nonzero even integer would be the falsification-register hit).
"""
import math, sys
import numpy as np, mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window
mp.mp.dps = 20
DELTA = math.pi/3; N = 100_000
n = np.arange(1, N + 1, dtype=float); lx = np.log(DELTA*n); mag = growth_window(n/N)*(DELTA*n)**-0.5
odd = (np.arange(1, N + 1) % 2 == 1)
def Fabs(y):
    ph = mag*np.exp(-1j*y*lx); return abs(ph[odd].sum() - ph[~odd].sum())
def golden(f, a, b, it=60):
    g = (math.sqrt(5) - 1)/2; c, d = b - g*(b - a), a + g*(b - a); fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd: b, d, fd = d, c, fc; c = b - g*(b - a); fc = f(c)
        else: a, c, fc = c, d, fd; d = a + g*(b - a); fd = f(d)
    return (a + b)/2
# crossings from the bank (same detector as att554)
ys = np.arange(10, 80.0001, 0.02); Fg = np.array([Fabs(y) for y in ys])
cross = []
for i in range(1, len(ys) - 1):
    if Fg[i] < Fg[i-1] and Fg[i] <= Fg[i+1]:
        yz = golden(Fabs, ys[i-1], ys[i+1])
        if Fabs(yz) < 1e-6: cross.append(yz)
cross = np.array(cross)
print("crossings from the bank: %d" % len(cross))

def S_gamma(t):
    """(1/π) Im log ζ(½+it), continued along 2 → 2+it → ½+it (log ζ(2) real)."""
    f = lambda s: mp.zeta(s, derivative=1)/mp.zeta(s)
    v = mp.quad(lambda u: f(mp.mpc(2, u))*1j, list(np.arange(0, t, 1.0)) + [t])   # vertical leg, ds = i du
    h = mp.quad(lambda x: f(mp.mpc(2 - x, t))*(-1), [0, 0.5, 1.0, 1.25, 1.5])   # horizontal leg s = 2 − x, ds = −dx
    return float(mp.im(v + h))/math.pi
def S_mult(t):
    Nev = int((cross < t).sum()); return Nev - 1 - float(mp.siegeltheta(t))/math.pi

print("   t (between crossings)   S_mult (model)   S_Γ (chart contour)   S_Γ − S_mult = N_off")
worst = 0.0
pts = [(cross[j] + cross[j+1])/2 for j in range(len(cross) - 1)] + [12.0, 79.9]
for t in sorted(pts):
    sm, sg = S_mult(t), S_gamma(t); worst = max(worst, abs(sg - sm))
    print("   %8.4f              %+9.5f        %+9.5f          %+.2e" % (t, sm, sg, sg - sm))
print("max |S_Γ − S_mult| = %.2e  →  N_off = 0 on [10, 80]: %s" % (worst, "CONFIRMED" if worst < 1e-6 else "DIED"))
