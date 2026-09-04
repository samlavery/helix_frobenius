#!/usr/bin/env python3
"""
att582 — THE NEAREST NON-REAL ZERO OF THE NATIVE θ-STAGE Ξ_U(z) = ∫_0^U Φ(u) cos(zu) du, versus the front U.
  R_off(U) := min{ Re z : Ξ_U(z) = 0, Im z ≥ 0.3 } (upper half-plane; Ξ_U even and real on ℝ), with its Im.
  Method: winding number on cells [x, x+5]×[0.3, 40] scanned upward in x; bisection in x to width 0.2; then
  mp.findroot from the cell centre.  PRE-REGISTERED: R_off(U) = C·e^{2U} with C ≈ 4 (remainder crossover
  e^{−πe^{2U}} ≈ e^{−πt/4}); fitted exponent d log R_off / dU ∈ [1.7, 2.3]; Im displacement O(1–10).
"""
import numpy as np, mpmath as mp, math, time
mp.mp.dps = 30
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u)
    return mp.fsum((2*PI**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*PI*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-PI*n*n*e2) for n in range(1, 16))
def stage(U):
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf(U), 7, mp.mp.prec)
    Uv = [x for x, w in nodes]; PW = [Phi(x)*w for x, w in nodes]
    return lambda z: mp.fsum(pw*mp.cos(z*u) for u, pw in zip(Uv, PW))
def winding(F, x0, x1, y0, y1, h=0.25):
    pts = [mp.mpc(x, y0) for x in np.arange(x0, x1, h)] + [mp.mpc(x1, y) for y in np.arange(y0, y1, h)] \
        + [mp.mpc(x, y1) for x in np.arange(x1, x0, -h)] + [mp.mpc(x0, y) for y in np.arange(y1, y0, -h)]
    pts.append(pts[0])
    ph = np.unwrap(np.array([float(mp.arg(F(z))) for z in pts]))
    return int(round((ph[-1]-ph[0])/(2*np.pi)))
t0 = time.time(); rows = []
for U in (0.6, 0.8, 1.0, 1.2, 1.4, 1.6):
    F = stage(U); x = 0.0; found = None
    while x < 20*math.exp(2*U):
        if winding(F, x, x+5, 0.3, 40) != 0:
            a, b = x, x+5
            while b - a > 0.2:
                m = (a+b)/2
                if winding(F, a, m, 0.3, 40, h=0.1) != 0: b = m
                else: a = m
            # refine: findroot from several starts in the strip
            best = None
            for y in (2, 5, 10, 20, 30):
                try:
                    z = mp.findroot(F, mp.mpc((a+b)/2, y), tol=1e-20, maxsteps=60)
                    if abs(z.imag) > 0.05 and a-1 <= z.real <= b+1 and (best is None or z.real < best.real): best = z
                except Exception: pass
            found = best if best is not None else mp.mpc((a+b)/2, 0)
            break
        x += 5
    if found is None:
        print("U = %.1f : no non-real zero below Re = %.0f  [%.0fs]" % (U, 20*math.exp(2*U), time.time()-t0), flush=True); continue
    rows.append((U, float(found.real), float(found.imag)))
    print("U = %.1f : nearest non-real zero z = %.3f + %.3f i ; R_off/e^{2U} = %.3f ; 4e^{2U} = %.1f   [%.0fs]" % (
        U, found.real, found.imag, float(found.real)/math.exp(2*U), 4*math.exp(2*U), time.time()-t0), flush=True)
if len(rows) >= 3:
    Us = np.array([r[0] for r in rows]); R = np.array([r[1] for r in rows])
    slope, icpt = np.polyfit(Us, np.log(R), 1)
    print("fit log R_off = %.3f·U + %.3f  →  R_off ≈ %.2f·e^{%.2f U}   (pre-registered exponent 2, C ≈ 4)" % (slope, icpt, math.exp(icpt), slope))
