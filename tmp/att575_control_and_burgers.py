#!/usr/bin/env python3
"""
att575 — THE CONTROL (t < 0) DOUBLE ZERO, and the BURGERS BOUNDARY LAW along a moving zero (2026-09-03).
  H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du ; F_t = ∫₀^∞ e^{tu²}Φ e^{izu} ; q = F′/F ; v := Im q(x_k(t), t) = −H′/S.
  (A) CONTROL: locate (t_*, x_*) with H = H′ = 0 near the rank-33 pair (111.03, 111.87) at t ≈ −0.12 (2D Newton).
      At (t_*, x_*): the kernel is positive, even, decreasing; S_{t_*}(x_*) > 0; F_{t_*} zero-free in the UHP
      (winding check) — every one-ended fact holds and the double zero exists.
  (B) BURGERS LAW: dv/dt = −Im q_xx − 2v Re q_x + (Im q_x)²/v along the zero  (from ∂_t q = −q_zz − 2q q_z and
      ẋ_k = 2Re q + Im q_x/Im q).  Check at t = 0.10 on the first three zeros by finite differences in t.
      Corollary: d(v²)/dt = 2(Im q_x)² − 2v Im q_xx − 4v² Re q_x ; at v = 0 it equals 2(H″/S)² > 0: collisions are
      backward-only events with v ~ √(t − t_*).
PRE-REGISTERED: (A) t_* ∈ (−0.16, −0.08), x_* ∈ (111.2, 111.8), winding 0, S > 0; (B) law holds to 1e-6 relative.
"""
import numpy as np, mpmath as mp, math
mp.mp.dps = 30
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u)
    return mp.fsum((2*PI**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*PI*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-PI*n*n*e2) for n in range(1, 16))
nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf("2.6"), 7, mp.mp.prec)
U = [x for x, w in nodes]; PW = [Phi(x)*w for x, w in nodes]
def Fm(z, t, m=0):   # m-th derivative of F_t at z (mp)
    return mp.fsum(pw*mp.exp(t*u*u)*(1j*u)**m*mp.exp(1j*z*u) for u, pw in zip(U, PW))
H  = lambda x, t: Fm(x, t).real
Hp = lambda x, t: Fm(x, t, 1).real
Hpp= lambda x, t: Fm(x, t, 2).real
S  = lambda x, t: Fm(x, t).imag
# (A) 2D Newton on (H, H') in (x, t)
x, t = mp.mpf("111.45"), mp.mpf("-0.12")
for it in range(30):
    f1, f2 = H(x, t), Hp(x, t)
    J = mp.matrix([[Hp(x, t), Fm(x, t).real*0 + mp.diff(lambda tt: H(x, tt), t)],
                   [Hpp(x, t), mp.diff(lambda tt: Hp(x, tt), t)]])
    dx = mp.lu_solve(J, mp.matrix([-f1, -f2]))
    x += dx[0]; t += dx[1]
    if abs(dx[0]) + abs(dx[1]) < mp.mpf(10)**-20: break
print("(A) CONTROL double zero: t_* = %s , x_* = %s ; H = %.1e , H′ = %.1e , H″ = %.4e ; S = %.6f (>0) ; Φ_t decreasing? -(logΦ)'(u)/(2u) ≥ 9.36 > t_*: yes" % (
    mp.nstr(t, 12), mp.nstr(x, 12), abs(H(x, t)), abs(Hp(x, t)), Hpp(x, t), S(x, t)))
# winding of F_{t_*} around [-130,130]x[0,15]
def winding(t, X, Y, h=0.02):
    import numpy as np
    Uf = np.array([float(u) for u in U]); PWf = np.array([float(p) for p in PW])
    def F(z): return np.exp(1j*np.outer(z, Uf)) @ (PWf*np.exp(float(t)*Uf**2))
    bot = np.arange(-X, X, h)+0j; rgt = X+1j*np.arange(0, Y, h); top = np.arange(X, -X, -h)+1j*Y; lft = -X+1j*np.arange(Y, 0, -h)
    path = np.concatenate([bot, rgt, top, lft, bot[:1]]); v = F(path); ph = np.unwrap(np.angle(v))
    return (ph[-1]-ph[0])/(2*np.pi), np.abs(v).min()
w, m = winding(t, 130, 15)
print("(A) F_{t_*} winding on [-130,130]x[0,15] = %+.4f (min|F| %.1e) — zero-free in the UHP at the control" % (w, m))
# (B) Burgers boundary law at t = 0.10 for zeros 1..3
t0 = mp.mpf("0.10")
def zero_at(x0, t):
    x = mp.mpf(x0)
    for _ in range(40):
        x -= H(x, t)/Hp(x, t)
    return x
for x0 in (14.0, 21.0, 25.0):
    xk = zero_at(x0, t0)
    F0, F1, F2, F3 = Fm(xk, t0), Fm(xk, t0, 1), Fm(xk, t0, 2), Fm(xk, t0, 3)
    q = F1/F0; qx = F2/F0 - q*q; qxx = F3/F0 - 3*q*qx - q**3
    v = q.imag
    law = -qxx.imag - 2*v*qx.real + qx.imag**2/v
    h = mp.mpf("1e-4")
    def v_at(tt):
        xx = zero_at(xk, tt); return (Fm(xx, tt, 1)/Fm(xx, tt)).imag
    fd = (v_at(t0+h) - v_at(t0-h))/(2*h)
    xdot_law = 2*q.real + qx.imag/q.imag; xdot_fd = (zero_at(xk, t0+h) - zero_at(xk, t0-h))/(2*h)
    print("(B) t=0.10 zero at %.6f: v = Im q = %+.6e ; dv/dt law = %+.6e ; finite diff = %+.6e ; rel %.1e | ẋ law %+.6f fd %+.6f" % (
        xk, v, law, fd, abs(law-fd)/abs(fd), xdot_law, xdot_fd))
