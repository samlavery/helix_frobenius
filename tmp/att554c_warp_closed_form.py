#!/usr/bin/env python3
"""
att554c — THE CLOSED FORM OF THE WARP (Sam: "there should be a closed form for the warp").

The warp is discrete: cell k (left edge g_k, ϑ(g_k) = kπ) ↦ crossing γ_{k+2}. Its exact closed form is
the displacement in cell units,
        u_j := (ϑ(γ_j) − ϑ(g_{j−2}))/π = 1 − S(γ_j⁺),          S(γ⁺) = N(γ⁺) − 1 − ϑ(γ)/π,
so a closed form for the warp is a closed form for S. Three registers, all exact:
  (R1) registration (compiled `carrier_scale_compensation_S`):  S(t) = N_{π/3}(e^t) − N_1(e^t).
  (R2) the conducted bank on the channel: S(t) = (1/π)[arg η(½+it) − arg(1 − 2^{½−it})], arg continuous,
       η(½+it) = lim Σ (−1)^{n+1} n^{−½−it} (the closed-cell bank, convergent on the channel).
  (R3) the Euler product (F6): log ζ(s) = Σ_{p,k} p^{−ks}/k  ⟹
       S(t) = −(1/π) Σ_{p,k} sin(k t log p) / (k p^{k/2})   =  −(1/π) Σ_n Λ(n) sin(t log n)/(√n log n),
       THE PRIME CLOCKS' SINES with balanced amplitudes p^{−k/2} and frequencies k log p; DC = 0
       (no n = 1 term). Exact as the boundary value of the absolutely convergent σ > 1 expression;
       on the channel it is conditionally convergent at best, so it is used with Selberg's weights
       Λ_x(n) = Λ(n) (n ≤ x), Λ(n)·log(x²/n)/log x (x < n ≤ x²).
The pitch modulation is the derivative: φ′ − 1 ∝ S′(t) = −(1/π) Re[ζ′/ζ(½+it)] — the multiplicative
face's real part on the channel (DC-divergent as a raw prime sum; finite as the conducted bank's
log-derivative). PRE-REGISTERED: (R2) reproduces the model's S at 22 midpoints to 1e−6 once anchored
at one point; (R3) with x = 10, 30, 100, 300 reproduces S at the 21 crossings (right limit − ½) and the
22 midpoints with RMS error decreasing in x, below 0.05 at x = 300. If (R3)'s RMS does NOT decrease
with x the prime-clock closed form is not converging on the channel at these heights.
"""
import math, sys
import numpy as np, mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window
mp.mp.dps = 20
DELTA = math.pi/3; N = 100_000
n = np.arange(1, N + 1, dtype=float); lx = np.log(DELTA*n); mag = growth_window(n/N)*(DELTA*n)**-0.5
odd = (np.arange(1, N + 1) % 2 == 1)
def F(y):
    ph = mag*np.exp(-1j*y*lx); return ph[odd].sum() - ph[~odd].sum()
def golden(f, a, b, it=60):
    g = (math.sqrt(5) - 1)/2; c, d = b - g*(b - a), a + g*(b - a); fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd: b, d, fd = d, c, fc; c = b - g*(b - a); fc = f(c)
        else: a, c, fc = c, d, fd; d = a + g*(b - a); fd = f(d)
    return (a + b)/2
ys = np.arange(10, 80.0001, 0.02); Fg = np.array([abs(F(y)) for y in ys])
cross = []
for i in range(1, len(ys) - 1):
    if Fg[i] < Fg[i-1] and Fg[i] <= Fg[i+1]:
        yz = golden(lambda y: abs(F(y)), ys[i-1], ys[i+1])
        if abs(F(yz)) < 1e-6: cross.append(yz)
cross = np.array(cross); J = len(cross)
theta = lambda t: float(mp.siegeltheta(t))
def S_mult(t):  return int((cross < t).sum()) - 1 - theta(t)/math.pi
S_right = np.array([j - theta(cross[j-1])/math.pi for j in range(1, J + 1)])   # S(γ_j⁺) = j − 1 − ϑ/π ... j−1
S_right = S_right - 1
mids = np.array([(cross[j] + cross[j+1])/2 for j in range(J - 1)])
S_mid = np.array([S_mult(t) for t in mids])
print("crossings: %d ; warp in cell units u_j = 1 − S(γ_j⁺): first five %s" % (J, np.round(1 - S_right[:5], 4)))

# (R2) the conducted bank's continuous argument, anchored at t0 = mids[0]
def eta_bank(y):   # Δ^{s} F(y) = η_N(½+iy)
    s = 0.5 + 1j*y; return DELTA**s*F(y)
tt = np.union1d(np.arange(mids[0], mids[-1] + 1e-9, 0.005), mids)   # grid contains the midpoints exactly
ph = np.unwrap(np.angle([eta_bank(t)/(1 - 2**(0.5 - 1j*t)) for t in tt]))
S_R2 = ph/math.pi
S_R2 += S_mid[0] - S_R2[0]                    # one anchor constant (the branch at t0)
err_R2 = max(abs(np.interp(m, tt, S_R2) - s) for m, s in zip(mids, S_mid))
print("(R2) conducted-bank argument vs model S at %d midpoints: max |Δ| = %.2e" % (len(mids), err_R2))

# (R3) the prime clocks' sines with Selberg weights
def lam_table(M):
    lam = np.zeros(M + 1)
    for p in range(2, M + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= M: lam[pk] = math.log(p); pk *= p
    return lam
def S_prime(t, x):
    M = int(x*x); lam = lam_table(M); nn = np.arange(2, M + 1, dtype=float)
    w = np.where(nn <= x, 1.0, np.log(x*x/nn)/np.log(x))
    return -(1/math.pi)*np.sum(lam[2:]*w*np.sin(t*np.log(nn))/(np.sqrt(nn)*np.log(nn)))
print("(R3) prime-clock closed form S_x(t) vs model:  RMS / max over 22 midpoints ; RMS at 21 crossings (right limit − ½)")
for x in (10, 30, 100, 300):
    dm = np.array([S_prime(t, x) - s for t, s in zip(mids, S_mid)])
    dc = np.array([S_prime(g, x) - (s - 0.5) for g, s in zip(cross, S_right)])
    print("   x=%4d (n ≤ %6d):  midpoints RMS %.4f max %.4f ;  crossings RMS %.4f" %
          (x, x*x, np.sqrt((dm**2).mean()), np.abs(dm).max(), np.sqrt((dc**2).mean())))
print("   model S at midpoints: RMS %.4f max %.4f (for scale)" % (np.sqrt((S_mid**2).mean()), np.abs(S_mid).max()))
# the warp itself from (R3): u_j ≈ 1 − (S_x(γ_j) + ½)
x = 300
u_model = 1 - S_right
u_R3 = np.array([1 - (S_prime(g, x) + 0.5) for g in cross])
print("warp per cell, model vs prime-clock closed form (x=300): RMS %.4f ; first five model %s R3 %s"
      % (np.sqrt(((u_model - u_R3)**2).mean()), np.round(u_model[:5], 3), np.round(u_R3[:5], 3)))
