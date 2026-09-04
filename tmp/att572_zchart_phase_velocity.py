#!/usr/bin/env python3
"""
att572 — Z-CHART DECOMPOSITION of the one-ended phase velocity and of the flow velocity (2026-09-03).
  H_0(x) = ξ(½+ix)/4 = −A(x)·Z(x),  A(x) = (x²+¼)π^{−1/4}|Γ(¼+ix/2)|/8 > 0,  Z = Hardy's function.
  (1) θ′_0(x_k) = A(x_k) Z′(γ_k)/S_0(x_k)   [exact; S_0 from the one-ended integral]
  (2) ẋ_k = 2(A′/A)(x_k) + Z″/Z′(γ_k)        [DC = clock drift, AC = Z-chart curvature]
  (3) t_c = inf_{u>0} −(log Φ)′(u)/(2u): fine grid to u = 4, mp precision.
  (4) B-form: ξ(½+ix) = ½ − (x²+¼) Re Σ_n g_n(x), g_n = (πn²)^{−s/2}Γ(s/2, πn²); Im g_n(x) > 0 per source; −B′(0) = ½.
PRE-REGISTERED: (1) rel err < 1e-8 (quadrature-limited); (2) rel err < 1e-8; (3) ratio increasing on (0,4], t_c = 9.3634525 ± 1e-6;
  (4) identity to 1e-12 at x = 20, 40; Im g_n > 0 for n ≤ 6 on a grid; −B′(0) = ½ to 1e-15.
"""
import math, time, numpy as np, mpmath as mp
mp.mp.dps = 30
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
    return mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 16))
xi = lambda s: mp.mpf(1)/2*s*(s-1)*PI**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
A  = lambda x: (x*x + mp.mpf(1)/4)*PI**(-mp.mpf(1)/4)*abs(mp.gamma(mp.mpf(1)/4 + 1j*x/2))/8
Z  = lambda x: mp.siegelz(x)
S0 = lambda x: mp.quad(lambda u: Phi(u)*mp.sin(x*u), [0, 1, 2, 3])
print("(1)(2) k   x_k      theta'(x_k) direct     A Z'/S_0        rel      |  xdot (i xi''/xi')   2A'/A + Z''/Z'   rel")
for k in range(1, 13):
    x = mp.zetazero(k).imag; rho = mp.mpc(0.5, x)
    Hp = 1j*mp.diff(xi, rho, 1)/4          # H'(x) = i ξ'(ρ)/4
    th_direct = -(Hp/S0(x)).real
    Zp = mp.diff(Z, x, 1); Zpp = mp.diff(Z, x, 2)
    th_chart = A(x)*Zp/S0(x)
    xd = (1j*mp.diff(xi, rho, 2)/mp.diff(xi, rho, 1)).real
    dlogA = mp.diff(lambda y: mp.log(A(y)), x, 1)
    xd_chart = 2*dlogA + Zpp/Zp
    print("  %2d %9.4f   %+.10f   %+.10f   %.1e  |  %+.8f   %+.8f   %.1e" % (k, x, th_direct, th_chart, abs(th_direct-th_chart)/abs(th_chart), xd, xd_chart, abs(xd-xd_chart)/abs(xd)))
# (3) t_c
us = [mp.mpf(k)/1000 for k in range(1, 4001)]
r = [float(-mp.diff(lambda v: mp.log(Phi(v)), u, 1)/(2*u)) for u in us[::10]]   # every 0.01
inc = all(r[i] < r[i+1] for i in range(len(r)-1))
tc0 = -mp.diff(Phi, 0, 2)/(2*Phi(0))
print("(3) ratio -(logPhi)'/(2u) on (0,4] step 0.01: increasing = %s ; r(0.01) = %.7f ; limit u->0: %s ; r(4) = %.1f" % (inc, r[0], mp.nstr(tc0, 9), r[-1]))
# (4) B-form
def g(n, s): return (PI*n*n)**(-s/2)*mp.gammainc(s/2, PI*n*n)
for x in (20, 40):
    s = mp.mpc(0.5, x); G = mp.fsum(g(n, s) for n in range(1, 12))
    lhs = xi(s); rhs = mp.mpf(1)/2 - (x*x + mp.mpf(1)/4)*G.real
    print("(4) x=%d: xi = %s ; ½ − (x²+¼)Re G = %s ; |diff| = %.1e ; Im g_n(x) for n=1..6: %s" % (x, mp.nstr(lhs.real, 12), mp.nstr(rhs, 12), abs(lhs.real - rhs), [mp.nstr(g(n, s).imag, 4) for n in range(1, 7)]))
grid_ok = all(g(n, mp.mpc(0.5, x)).imag > 0 for n in range(1, 7) for x in np.arange(0.5, 60, 0.7))
B = lambda u: 2*mp.exp(u/2)*mp.fsum(mp.exp(-PI*n*n*mp.exp(2*u)) for n in range(1, 30))
print("(4) Im g_n > 0 on grid n≤6, x∈(0.5,60): %s ; −B'(0) = %s (½ expected)" % (grid_ok, mp.nstr(-mp.diff(B, 0, 1), 15)))
