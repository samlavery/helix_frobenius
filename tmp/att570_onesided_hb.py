#!/usr/bin/env python3
"""
att570 — THE ONE-SIDED BANK F_t(z) = ∫₀^∞ e^{tu²}Φ(u) e^{izu} du and the first-collision problem (Sam, 2026-09-03).
  H_t = Re F_t (cos lane), S_t = Im F_t (sin lane, the other end).  At a real zero x of H_t: H′_t(x) = −θ′_t(x)·S_t(x).
  (A) t_c := sup{t : e^{tu²}Φ(u) decreasing on (0,∞)} = inf_u −(log Φ)′(u)/(2u).  For t ≤ t_c, F_t has NO real zeros
      (Re[(i/x)⁻¹ F_t(x)] = ∫(−Φ_t′)(1 − cos xu) du > 0), so zeros of F_t cannot cross the axis along the flow.
  (B) Winding number of F_t around upper-half-plane boxes = number of UHP zeros.  HB(F_{t₁}) for one t₁ ≤ t_c ⟹ RH.
  (C) Interlacing of the zeros of H_t and S_t on the axis (necessary for HB).
PRE-REGISTERED: P1 t_c > 0.22 (so Polymath's stage lies in the decreasing range) — prediction: t_c ≈ 0.4–0.6 (Gaussian-like
core, ⟨u²⟩ ≈ 1);  P2 winding of F_0 on [−80,80]×[0,20] = 0 (HB) — prediction 50/50, this is the test;  P3 if P2 holds,
S_0 and H_0 interlace on [0,80].  DECISION: winding > 0 at t = 0 kills the one-sided-HB route for this partner.
"""
import math, time, numpy as np, mpmath as mp
mp.mp.dps = 30
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u); e9 = mp.exp(mp.mpf(9)/2*u); e5 = mp.exp(mp.mpf(5)/2*u)
    return mp.fsum((2*PI**2*n**4*e9 - 3*PI*n**2*e5)*mp.exp(-PI*n*n*e2) for n in range(1, 16))
# (A) t_c
Phi0 = Phi(0); Phi2 = mp.diff(Phi, 0, 2)
tc0 = -Phi2/(2*Phi0)
print("Phi(0) = %s   Phi''(0) = %s   -Phi''(0)/(2 Phi(0)) = %s" % (mp.nstr(Phi0, 10), mp.nstr(Phi2, 10), mp.nstr(tc0, 10)))
us = [0.05*k for k in range(1, 41)]
ratio = [float(-mp.diff(lambda v: mp.log(Phi(v)), u, 1)/(2*u)) for u in us]
print("-(log Phi)'(u)/(2u) at u = 0.05..2.0:", ", ".join("%.4f" % r for r in ratio[:12]), "...", "%.3f (u=2)" % ratio[-1])
tc = min(min(ratio), float(tc0)); print("t_c = inf_u = %.6f  (attained at u -> 0: %s)" % (tc, "yes" if abs(tc - float(tc0)) < 1e-6 else "NO"))
# fixed Gauss-Legendre rule on [0, 2.6]
nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf("2.6"), 7, mp.mp.prec)
U = np.array([float(x) for x, w in nodes]); PW = np.array([float(Phi(x)*w) for x, w in nodes])
print("GL nodes: %d" % len(U))
def F(z, t):
    z = np.asarray(z, dtype=complex)
    E = PW*np.exp(t*U**2)
    return np.exp(1j*np.outer(z, U)) @ E
# sanity: H_0(z) vs xi(1/2+iz)/4 (house Phi = 4x Titchmarsh)
xi = lambda s: mp.mpf(1)/2*s*(s-1)*PI**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
for z in (20.0, 60.0):
    a = F(np.array([z]), 0.0)[0].real; b = float(xi(mp.mpf(1)/2 + 1j*z).real)/4
    print("   sanity z=%g: Re F_0 = %.12g  xi/4 = %.12g  rel %.1e" % (z, a, b, abs(a-b)/abs(b)))
def winding(t, X, Y, h=0.005):
    # boundary of [-X,X]x[0,Y], counterclockwise: bottom (y=0, x:-X->X), right, top, left
    bot = np.arange(-X, X, h) + 0j
    rgt = X + 1j*np.arange(0, Y, h)
    top = np.arange(X, -X, -h) + 1j*Y
    lft = -X + 1j*np.arange(Y, 0, -h)
    path = np.concatenate([bot, rgt, top, lft, bot[:1]])
    vals = F(path, t)
    ph = np.unwrap(np.angle(vals))
    minabs = np.abs(vals).min()
    return (ph[-1] - ph[0])/(2*np.pi), minabs
for t in (0.0, 0.1, 0.22, 0.35, 0.5):
    t0 = time.time()
    for X, Y in ((40, 10), (80, 20)):
        w, m = winding(t, X, Y)
        print("t = %.2f  box [-%d,%d]x[0,%d]: winding = %+.4f  (min|F| on contour %.2e)   [%.0fs]" % (t, X, X, Y, w, m, time.time() - t0))
# (C) interlacing on [0, 80] at t = 0 and 0.22
def real_zeros(g, a, b, h=0.01):
    xs = np.arange(a, b, h); v = g(xs); zs = []
    for i in range(len(xs)-1):
        if v[i]*v[i+1] < 0:
            lo, hi = xs[i], xs[i+1]; flo = v[i]
            for _ in range(40):
                mid = (lo+hi)/2; fm = g(np.array([mid]))[0]
                if flo*fm <= 0: hi = mid
                else: lo, flo = mid, fm
            zs.append((lo+hi)/2)
    return np.array(zs)
for t in (0.0, 0.22):
    zH = real_zeros(lambda x: F(x, t).real, 0.5, 80.0); zS = real_zeros(lambda x: F(x, t).imag, 0.5, 80.0)
    allz = sorted([(z, 'H') for z in zH] + [(z, 'S') for z in zS])
    labels = "".join(l for _, l in allz)
    alt = all(labels[i] != labels[i+1] for i in range(len(labels)-1))
    print("t = %.2f: zeros of H on (0.5,80): %d ; zeros of S: %d ; strictly alternating: %s ; pattern head: %s" % (t, len(zH), len(zS), alt, labels[:40]))

# (D) phase velocity theta'(x) = Im(F'/F) on the axis: sign changes?
for t in (0.0, 0.22):
    xs = np.arange(0.5, 80.0, 0.01); v = F(xs, t)
    E = PW*np.exp(t*U**2); dv = (np.exp(1j*np.outer(xs, U))*(1j*U)) @ E
    thp = np.imag(dv/v)
    zH = real_zeros(lambda x: F(x, t).real, 0.5, 80.0)
    thz = np.imag(F(zH + 1e-7, t)*0 + (np.exp(1j*np.outer(zH, U))*(1j*U)) @ E) / np.imag(F(zH, t))  # H'=-theta' S: theta'(x_k) = -H'/S
    print("t = %.2f: theta' on (0.5,80): min %+.4f max %+.4f ; sign changes: %d ; |theta'| at the %d H-zeros: min %.4f" % (t, thp.min(), thp.max(), int(np.sum(np.diff(np.sign(thp)) != 0)), len(zH), np.abs(thz).min()))
