#!/usr/bin/env python3
"""
att581 — THE HYBRID CASCADE Ξ_{U,t}(z) = ∫_0^U e^{tu²} Φ(u) cos(zu) du: front U (growth window), warp t.
  Diagonal U→∞, t(U)→0 converges to ξ/4. Source-labelled iff every stage is real-rooted.
  t*(U) := minimal warp with NO non-real zeros of Ξ_{U,t} in the box [0,40]×[0.05,12] (argument principle).
PRE-REGISTERED: P1 at t = 0 every U shows non-real zeros (the escort ladder, ledger 557);
  P2 (prediction = block): t*(U) is NON-decreasing in U — the diagonal cannot reach t = 0.
  A decreasing t*(U) refutes P2 and is a lead.
"""
import numpy as np, mpmath as mp, time
mp.mp.dps = 25
PI = mp.pi
def Phi(u):
    u = mp.mpf(u); e2 = mp.exp(2*u)
    return mp.fsum((2*PI**2*n**4*mp.exp(mp.mpf(9)/2*u) - 3*PI*n**2*mp.exp(mp.mpf(5)/2*u))*mp.exp(-PI*n*n*e2) for n in range(1, 16))
def stage_nodes(U, taper=False):
    nodes = mp.calculus.quadrature.GaussLegendre(mp.mp).get_nodes(mp.mpf(0), mp.mpf(U), 7, mp.mp.prec)
    return [x for x, w in nodes], [Phi(x)*w*((1 - x/U) if taper else 1) for x, w in nodes]
def winding(Uv, PWv, t, X=40.0, Y=12.0, y0=0.5, h=0.2):
    # rectangle [0,X]×[y0,Y] counterclockwise; Ξ is even so Re>0 suffices; y0>0 avoids real zeros
    pts = []
    xs = np.arange(0, X, h); ys = np.arange(y0, Y, h)
    pts += [mp.mpc(x, y0) for x in xs]; pts += [mp.mpc(X, y) for y in ys]
    pts += [mp.mpc(x, Y) for x in xs[::-1]]; pts += [mp.mpc(0, y) for y in ys[::-1]]; pts.append(pts[0])
    E = [pw*mp.exp(t*u*u) for u, pw in zip(Uv, PWv)]
    vals = [mp.fsum(e*mp.cos(z*u) for u, e in zip(Uv, E)) for z in pts]
    ph = np.unwrap(np.array([float(mp.arg(v)) for v in vals]))
    return (ph[-1]-ph[0])/(2*np.pi), min(float(abs(v)) for v in vals)
t0 = time.time()
import math
for U in (0.8, 1.0, 1.2, 1.4):
    Uv, PWv = stage_nodes(U, taper=True)
    X = 10*math.exp(2*U); Y = 40.0
    row = []
    for t in (0.0, 0.1, 0.22, 0.5, 1.0, 2.0, 4.0):
        w, m = winding(Uv, PWv, t, X=X, Y=Y)
        row.append((t, round(w), m))
    tstar = next((t for t, w, m in row if w == 0), None)
    print("RIESZ-TAPERED U = %.1f (box [0,%.0f]x[0.5,40]): non-real zeros by warp t: %s ; t*(U) = %s   [%.0fs]" % (U, X, ", ".join("t=%.2f→%d" % (t, w) for t, w, m in row), tstar, time.time()-t0), flush=True)
