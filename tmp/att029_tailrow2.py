#!/usr/bin/env python3
"""
Attempt 029 v2 — Z_eff(C_row), realizable class, fixed conventions.

w = window-square profile, density samples w_j >= 0 at xi_j = j/m on [0,1] (even).
ghat = w * w (autocorrelation, density) on [0,2]:  ghat = conv(F,F)*delta, F = mirrored w.
Z_eff = ghat(0) + 2 int_0^1 ghat(x) x dx + C_row * t,   t >= ghat(x) x^2 on (1,2].
normalization: int w = delta*(w_0 + 2 sum_{j>=1} w_j) = 1.

GATE: Montgomery-Taylor window w(xi) = cos(sqrt2 * xi) on [0,1/2] must give
Z_eff = 1.3274993 with t = 0 (its ghat is supported in [-1,1]).
"""
import numpy as np
from scipy.optimize import minimize
import time

m = 60
delta = 1.0/m
xg = np.arange(0, 2*m+1)*delta            # [0,2]
band = xg <= 1.0+1e-12
outi = np.where(xg > 1.0+1e-12)[0]
x2out = xg[outi]**2
xw = np.where(band, xg, 0.0)

def ghat_of(w):
    F = np.concatenate([w[:0:-1], w])     # density on [-1,1], length 2m+1
    return np.convolve(F, F)[2*m:] * delta  # density on [0,2]

def zparts(w):
    g = ghat_of(w)
    z0 = g[0]
    zx = 2*np.trapezoid(g*xw, dx=delta)
    tmin = np.max(g[outi]*x2out) if len(outi) else 0.0
    return z0, zx, tmin

def intw(w):
    return delta*(2*w.sum() - w[0])

# ---- GATE ----
wmt = np.where(np.arange(m+1)*delta <= 0.5+1e-12, np.cos(np.sqrt(2)*np.arange(m+1)*delta), 0.0)
wmt = np.maximum(wmt, 0);  wmt /= intw(wmt)
z0, zx, t = zparts(wmt)
print(f"GATE M-T window: Z = {z0+zx:.7f} (expect 1.3274993), tail t = {t:.2e} (expect ~0)", flush=True)

def solve(C_row, starts=8, seed0=3):
    best = None
    rng = np.random.default_rng(seed0)
    nv = m+2                                  # w_0..w_m, t
    def obj(v):
        w, t = v[:-1], v[-1]
        z0, zx, _ = zparts(w)
        return z0 + zx + C_row*t
    cons = [{'type': 'eq', 'fun': lambda v: intw(v[:-1]) - 1.0}]
    def outcon(v):
        w, t = v[:-1], v[-1]
        g = ghat_of(w)
        return t - g[outi]*x2out              # >= 0
    cons.append({'type': 'ineq', 'fun': outcon})
    bounds = [(0, None)]*(m+1) + [(0, None)]
    inits = []
    inits.append(np.concatenate([wmt, [0.0]]))
    w1 = np.ones(m+1); w1 /= intw(w1); inits.append(np.concatenate([w1, [zparts(w1)[2]]]))
    for s in range(starts-2):
        wr = rng.random(m+1); wr /= intw(wr)
        inits.append(np.concatenate([wr, [zparts(wr)[2]]]))
    for v0 in inits:
        res = minimize(obj, v0, method='SLSQP', bounds=bounds, constraints=cons,
                       options={'maxiter': 500, 'ftol': 1e-11})
        if res.fun is not None and np.isfinite(res.fun):
            # feasibility check
            w, t = res.x[:-1], res.x[-1]
            viol = max(abs(intw(w)-1.0), float(-np.min(outcon(res.x)) if len(outi) else 0), 0.0)
            if viol < 1e-6 and (best is None or res.fun < best):
                best = res.fun
    return best

if __name__ == "__main__":
    print(f"{'C_row':>8} {'Z_eff':>12} {'2-Z_eff':>12}   (M-T anchor 1.3274993 / 0.6725007)", flush=True)
    for C in [1e6, 4.0, 2.0, 1.0, 0.5, 0.25, 0.0]:
        t0 = time.time()
        z = solve(C)
        if z is None:
            print(f"{C:8.2f}  no feasible optimum found", flush=True)
        else:
            print(f"{C:8.2f} {z:12.7f} {2-z:12.7f}   [{time.time()-t0:.0f}s]", flush=True)
