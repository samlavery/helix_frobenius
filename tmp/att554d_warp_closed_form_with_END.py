#!/usr/bin/env python3
"""
att554d — the warp's bank closed form WITH THE END TERM CARRIED (Sam: "euler ends via the warp too?").

Selberg's exact identity (Titchmarsh 14.20), Λ_x(n) = Λ(n) (n ≤ x), Λ(n) log(x²/n)/log x (x < n ≤ x²):
  ζ′/ζ(s) = −Σ_{n≤x²} Λ_x(n) n^{−s} + (x^{2(1−s)} − x^{1−s})/((1−s)² log x)
            + (1/log x) Σ_ρ (x^{ρ−s} − x^{2(ρ−s)})/(s−ρ)² + (1/log x) Σ_q (x^{−2q−s} − x^{2(−2q−s)})/(s+2q)².
Integrate along σ from ½ to ∞ at fixed t:  log ζ(½+it) = −∫_{½}^{∞} ζ′/ζ(σ+it) dσ, so
  S(t) = (1/π) Im log ζ(½+it) = S_clock(t;x) + S_END(t;x) + S_triv(t;x) + S_zero(t;x),
  S_clock = −(1/π) Σ Λ_x(n) sin(t log n)/(√n log n)                                  (554c's form)
  S_END   = −(1/π) Im ∫_{½}^{∞} (x^{2(1−s)} − x^{1−s})/((1−s)² log x) dσ           (the POLE read at the cutoff)
  S_triv  = −(1/π) Im ∫_{½}^{∞} (1/log x) Σ_q (x^{−2q−s} − x^{2(−2q−s)})/(s+2q)² dσ  (anti-end; tiny)
PRE-REGISTERED: adding S_END (+S_triv) to 554c's form lowers the RMS residual against the model's S
at every x ∈ {10, 30, 100, 300, 1000}; the corrected residual DECREASES with x (the zero-side term
carries the 1/log x); the uncorrected floor ≈ 0.002 was the END term.  Decision: if the residual does
not drop, the floor is zero-side and the END attribution dies.
"""
import math, sys, numpy as np, mpmath as mp
sys.path.insert(0, ".")
from focal_closure import growth_window
mp.mp.dps = 25
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
S_mult = lambda t: int((cross < t).sum()) - 1 - theta(t)/math.pi
mids = np.array([(cross[j] + cross[j+1])/2 for j in range(J - 1)])
S_mid = np.array([S_mult(t) for t in mids])
S_right = np.array([j - 1 - theta(cross[j-1])/math.pi for j in range(1, J + 1)])
pts = list(mids) + list(cross)                       # 20 midpoints + 21 crossings
S_true = list(S_mid) + list(S_right - 0.5)           # at a crossing the series gives the mean of the limits

def lam_table(M):
    lam = np.zeros(M + 1)
    for p in range(2, M + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= M: lam[pk] = math.log(p); pk *= p
    return lam
def S_clock(t, x):
    M = int(x*x); lam = lam_table(M); nn = np.arange(2, M + 1, dtype=float)
    w = np.where(nn <= x, 1.0, np.log(x*x/nn)/np.log(x))
    return -(1/math.pi)*np.sum(lam[2:]*w*np.sin(t*np.log(nn))/(np.sqrt(nn)*np.log(nn)))
def S_END(t, x):
    L = mp.log(x)
    f = lambda sg: (mp.power(x, 2*(1 - mp.mpc(sg, t))) - mp.power(x, 1 - mp.mpc(sg, t)))/((1 - mp.mpc(sg, t))**2*L)
    v = mp.quad(f, [0.5, 1, 2, 4, 8, mp.inf])
    return -float(mp.im(v))/math.pi
def S_triv(t, x, Q=6):
    L = mp.log(x)
    f = lambda sg: mp.fsum((mp.power(x, -2*q - mp.mpc(sg, t)) - mp.power(x, 2*(-2*q - mp.mpc(sg, t))))/((mp.mpc(sg, t) + 2*q)**2*L) for q in range(1, Q + 1))
    v = mp.quad(f, [0.5, 1, 2, 4, 8, mp.inf])
    return -float(mp.im(v))/math.pi

print("crossings: %d ; points: %d (20 midpoints + 21 crossings) ; S RMS = %.4f" % (J, len(pts), np.sqrt(np.mean(np.array(S_true)**2))))
print("   x     RMS(clock only)   RMS(clock+END)   RMS(clock+END+triv)   max|END| over points")
for x in (10, 30, 100, 300, 1000):
    e0, e1, e2, emax = [], [], [], 0.0
    for t, s in zip(pts, S_true):
        c = S_clock(t, x); e = S_END(t, x); tr = S_triv(t, x)
        e0.append(c - s); e1.append(c + e - s); e2.append(c + e + tr - s); emax = max(emax, abs(e))
    r = lambda v: np.sqrt(np.mean(np.array(v)**2))
    print(" %5d      %.5f          %.5f            %.5f              %.2e" % (x, r(e0), r(e1), r(e2), emax))
