#!/usr/bin/env python3
"""
Attempt 029 — what does an unconditional S(t)-second-moment tail row buy?

Row: int_1^inf F(alpha)/alpha^2 dalpha <= C_row   (Goldston-1987 level; = 1+o(1) on PCC;
unconditional version = the open target, house bridge = the vehicle).

Certificate class (inertia route, NO dip, all walls bypassed):
  window w >= 0 on [-1,1] (x-units), int w = 1  =>  ghat = w*w >= 0, supp [-2,2],
  Frobenius bound:  ||A||_F^2 <= N[ ghat(0) + 2 int_0^1 ghat(x) x dx + t*C_row ],
  where t := sup_{1<x<=2} ghat(x) x^2  (since int_{(1,2]} ghat F <= t * row, F >= 0).
  s1 >= (2 - Z_eff)N,   Z_eff = ghat(0) + 2 int_0^1 ghat x dx + t*C_row.

Anchors: C_row -> inf: supp w subset [-1/2,1/2] forced => Montgomery-Taylor 1.3274993.
         C_row = 1: the PCC-anchored value (prize if the row lands with C=1).
Also: doubly-nonnegative convex relaxation (g>=0 via Toeplitz-PSD, ghat>=0, same rows)
      = lower bound on the achievable Z_eff (how much realizability costs).
"""
import numpy as np
from scipy.optimize import minimize
import cvxpy as cp
import time

# ---------------- direct optimization in w ----------------
def direct(C_row, m=80, starts=6, seed0=1):
    delta = 1.0/m
    xg = np.arange(0, 2*m+1)*delta          # ghat grid on [0,2]
    band = xg <= 1.0+1e-12
    out = (xg > 1.0+1e-12)
    x2out = xg[out]**2

    def ghat_of(w):
        # even w: atoms w_j at +-j*delta (j>=1), w_0 at 0.  full vector on [-1,1]:
        full = np.concatenate([w[:0:-1], w])          # length 2m+1
        g = np.convolve(full, full)[2*m:]             # ghat at x = 0..2, atoms
        return g / delta                              # density

    def obj(w):
        g = ghat_of(w)
        z0 = g[0]                                     # ghat(0) density
        zx = 2*np.trapezoid(g[band]*xg[band], dx=delta)
        t = np.max(g[out]*x2out)
        return z0 + zx + C_row*t

    best = None
    rng = np.random.default_rng(seed0)
    for s in range(starts):
        if s == 0:
            w0 = np.cos(np.arange(m+1)*delta*np.pi/2/1.0)**2  # MT-ish on [-1,1]... start wide
        elif s == 1:
            w0 = np.where(np.arange(m+1)*delta <= 0.5, 1.0, 0.0)  # MT-support start
        else:
            w0 = rng.random(m+1)
        w0 = np.maximum(w0, 0)
        # normalize int w = 1 (atoms: w0*delta, even: 2*sum-w0[0])
        def norm(w):
            tot = (2*w.sum() - w[0])*delta
            return w/tot
        w0 = norm(w0)
        cons = [{'type': 'eq', 'fun': lambda w: (2*w.sum()-w[0])*delta - 1.0}]
        res = minimize(obj, w0, method='SLSQP', bounds=[(0, None)]*(m+1),
                       constraints=cons, options={'maxiter': 800, 'ftol': 1e-12})
        if res.success or res.fun < 10:
            if best is None or res.fun < best.fun:
                best = res
    return best.fun if best is not None else np.nan

# ---------------- doubly-nonnegative relaxation ----------------
def relax(C_row, Delta=0.02, S=2.0):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    Q = cp.Variable((n+1, n+1), PSD=True)
    c = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n+1)])
    t = cp.Variable(nonneg=True)
    cons = [c >= 0]
    cons.append(c[0] + 2*cp.sum(c[1:]) == 1)
    for j in range(1, n+1):
        if xs[j] > 1.0+1e-12:
            cons.append(c[j]/Delta*xs[j]**2 <= t)
    Z = c[0]/Delta + 2*cp.sum(cp.multiply(np.where((xs<=1.0+1e-12)&(np.arange(n+1)>=1), xs, 0.0), c)) + C_row*t
    prob = cp.Problem(cp.Minimize(Z), cons)
    try:
        val = prob.solve(solver="CLARABEL")
    except cp.error.SolverError:
        val = prob.solve(solver="SCS")
    return val

if __name__ == "__main__":
    print("anchors: M-T = 1.3274993 (C_row -> inf); CGdL-class Z*(2)=1.3212 (sign-only, unrealizable)", flush=True)
    print(f"{'C_row':>8} {'Z_direct (realizable)':>24} {'2-Z':>10} {'Z_relax (lower bd)':>20}", flush=True)
    for C in [0.0, 0.25, 0.5, 1.0, 2.0, 4.0, 1e6]:
        t0 = time.time()
        zd = direct(C)
        zr = relax(C)
        print(f"{C:8.2f} {zd:24.7f} {2-zd:10.7f} {zr:20.7f}   [{time.time()-t0:.0f}s]", flush=True)
