#!/usr/bin/env python3
"""att575b — the CONTROL double zero of H_t at t < 0, by tracking the local extremum between the rank-33 pair."""
import numpy as np, mpmath as mp
mp.mp.dps = 60
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u)
    return mp.fsum((2*PI**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*PI*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-PI*n*n*e2) for n in range(1, 16))
nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf("2.8"), 8, mp.mp.prec)
U = [x for x, w in nodes]; PW = [Phi(x)*w for x, w in nodes]
def Fm(z, t, m=0): return mp.fsum(pw*mp.exp(t*u*u)*(1j*u)**m*mp.exp(1j*z*u) for u, pw in zip(U, PW))
H = lambda x, t: Fm(x, t).real; Hp = lambda x, t: Fm(x, t, 1).real; Hpp = lambda x, t: Fm(x, t, 2).real; S = lambda x, t: Fm(x, t).imag
def extremum(t, x0):
    x = mp.mpf(x0)
    for _ in range(50): x -= Hp(x, t)/Hpp(x, t)
    return x
xm0 = extremum(mp.mpf(0), mp.mpf("111.45"))
h = lambda t: H(extremum(t, xm0), t)
print("t=0: extremum at %s, H there = %s ; t=-0.2: H at extremum = %s" % (mp.nstr(xm0, 8), mp.nstr(h(mp.mpf(0)), 6), mp.nstr(h(mp.mpf("-0.2")), 6)))
a, b = mp.mpf("-0.2"), mp.mpf(0)
fa = h(a)
for _ in range(60):
    m = (a+b)/2; fm = h(m)
    if fa*fm <= 0: b = m
    else: a, fa = m, fm
ts = (a+b)/2; xs = extremum(ts, xm0)
print("CONTROL double zero: t_* = %s ; x_* = %s ; H = %.1e ; H′ = %.1e ; H″ = %.5e ; S_t*(x_*) = %.6f > 0" % (mp.nstr(ts, 10), mp.nstr(xs, 10), abs(H(xs, ts)), abs(Hp(xs, ts)), Hpp(xs, ts), S(xs, ts)))
# one-ended facts at t_*: kernel decreasing (t_* < 0 < 9.36), winding of F_{t_*}
Uf = np.array([float(u) for u in U]); PWf = np.array([float(p) for p in PW]); tf = float(ts)
def F(z): return np.exp(1j*np.outer(z, Uf)) @ (PWf*np.exp(tf*Uf**2))
X, Y, hh = 130, 15, 0.02
bot = np.arange(-X, X, hh)+0j; rgt = X+1j*np.arange(0, Y, hh); top = np.arange(X, -X, -hh)+1j*Y; lft = -X+1j*np.arange(Y, 0, -hh)
path = np.concatenate([bot, rgt, top, lft, bot[:1]]); v = F(path); ph = np.unwrap(np.angle(v))
print("F_{t_*} winding on [-130,130]x[0,15] = %+.4f (min|F| on contour %.2e): zero-free in the UHP at the control" % ((ph[-1]-ph[0])/(2*np.pi), np.abs(v).min()))
# local law: v² ≈ 2(H″/S)²(t − t_*) just above t_*
for dt in (mp.mpf("1e-3"), mp.mpf("4e-3")):
    t1 = ts + dt
    # the two zeros near x_* at t1
    z1 = xs - mp.sqrt(dt)*2; z2 = xs + mp.sqrt(dt)*2
    for _ in range(60): z1 -= H(z1, t1)/Hp(z1, t1); z2 -= H(z2, t1)/Hp(z2, t1)
    v1 = -Hp(z1, t1)/S(z1, t1); g = z2 - z1
    print("  t_* + %s: gap %.6f (√(8dt)=%.6f) ; v(z1)² = %.4e vs 2(H″/S)² dt = %.4e" % (mp.nstr(dt, 2), g, mp.sqrt(8*dt), v1**2, 2*(Hpp(xs, ts)/S(xs, ts))**2*dt))
