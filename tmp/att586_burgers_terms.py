#!/usr/bin/env python3
"""
att586 — THE THREE TERMS OF THE BURGERS BOUNDARY LAW along the flow, at the first zeros (2026-09-03).
  v := Im q at the moving zero (= −H′/S = θ′), q = F′/F, F_t = ∫₀^∞ e^{tu²}Φ e^{izu}.
  d(v²)/dt = 2(Im q_x)² − 2 v Im q_xx − 4 v² Re q_x   [verified 572]
  A barrier v(0)² > 0 from v(t₀)² > 0 needs ∫₀^{t₀} d(v²)/dt < v(t₀)²: report the three terms and v² at
  t ∈ {0, .1, .22, .35, .5} for zeros 1..12, and the ratio K := ∫ kinetic / v(t₀)².
PRE-REGISTERED: P1 v² is increasing in t at every zero (transversality grows forward); P2 the kinetic term
  2(Im q_x)² dominates |indefinite terms| at t = 0 for most zeros; P3 K > 1 for the closest pairs
  (the kinetic integral alone would over-close: the barrier must come from the indefinite terms).
"""
import mpmath as mp, math
mp.mp.dps = 40
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u)
    return mp.fsum((2*PI**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*PI*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-PI*n*n*e2) for n in range(1, 16))
nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf("2.6"), 7, mp.mp.prec)
U = [x for x, w in nodes]; PW = [Phi(x)*w for x, w in nodes]
def Fm(z, t, m=0): return mp.fsum(pw*mp.exp(t*u*u)*(1j*u)**m*mp.exp(1j*z*u) for u, pw in zip(U, PW))
def zero_at(x0, t):
    x = mp.mpf(x0)
    for _ in range(50): x -= Fm(x, t).real/Fm(x, t, 1).real
    return x
def terms(xk, t):
    F0, F1, F2, F3 = Fm(xk, t), Fm(xk, t, 1), Fm(xk, t, 2), Fm(xk, t, 3)
    q = F1/F0; qx = F2/F0 - q*q; qxx = F3/F0 - 3*q*qx - q**3
    v = q.imag
    return v, 2*qx.imag**2, -2*v*qxx.imag, -4*v*v*qx.real
z0 = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832, 52.970321, 56.446248]
ts = [mp.mpf(s) for s in ("0", "0.1", "0.22", "0.35", "0.5")]
print("zero  t     x_k(t)     v=Im q       v²        kinetic 2(Im q_x)²   −2v Im q_xx   −4v² Re q_x   d(v²)/dt")
for k, x0 in enumerate(z0):
    xk = mp.mpf(x0); rows = []
    for t in ts:
        xk = zero_at(xk, t)
        v, kin, t2, t3 = terms(xk, t)
        rows.append((t, xk, v, kin, t2, t3))
        print("%3d  %.2f  %9.5f  %+.4e  %.4e   %+.4e   %+.4e   %+.4e   %+.4e" % (k+1, t, xk, v, v*v, kin, t2, t3, kin+t2+t3))
    # crude integrals over [0, 0.5] by trapezoid on the 5 samples
    def trap(idx):
        s = 0
        for i in range(len(rows)-1):
            s += (rows[i+1][0]-rows[i][0])*(rows[i][idx]+rows[i+1][idx])/2
        return s
    v0sq = rows[0][2]**2; vTsq = rows[-1][2]**2
    print("      integrals on [0,0.5]: kinetic %.3e  indef1 %+.3e  indef2 %+.3e ; v(0.5)² − v(0)² = %.3e (check %.3e) ; K = ∫kin / v(0.5)² = %.3f ; v² monotone up: %s" % (
        trap(3), trap(4), trap(5), vTsq - v0sq, trap(3)+trap(4)+trap(5), trap(3)/vTsq, all(rows[i][2]**2 < rows[i+1][2]**2 for i in range(len(rows)-1))))
