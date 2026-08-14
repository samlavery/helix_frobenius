#!/usr/bin/env python3
"""
Attempt 028b (fast curve) — Z(theta_max) with strip slices as v-grid linear constraints.
w=0 slice exact (Toeplitz-PSD); w>0 slices sampled on a fine v-grid + post-verified.
"""
import numpy as np
import cvxpy as cp
import time

def solve(th_max, Delta=0.04, S=2.0, nw=6, nv=600, dip=True, solver="CLARABEL"):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    t0 = time.time()
    Q = cp.Variable((n+1, n+1), PSD=True)
    c = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n+1)])
    cons = []
    # w>0 slices on the circle theta in [0, pi] (even poly): grid
    thv = np.linspace(0, np.pi, nv)
    CO = np.cos(np.outer(thv, np.arange(n+1)))     # (nv, n+1); term j has weight 2 for j>=1
    wts = np.ones(n+1); wts[1:] = 2.0
    ws = np.linspace(0, th_max, nw)[1:] if th_max > 0 else []
    for w in ws:
        ch = np.cosh(xs*w)
        cons.append(CO @ cp.multiply(wts*ch, c) >= 0)
    Z = c[0]/Delta + 2*cp.sum(cp.multiply(np.where((xs <= 1.0+1e-12) & (np.arange(n+1) >= 1), xs, 0.0), c))
    cons.append(cp.sum(cp.multiply(wts, c)) == 1)
    if dip:
        for j in range(1, n+1):
            if xs[j] >= 1.0 - 1e-12:
                cons.append(c[j] <= 0)
    prob = cp.Problem(cp.Minimize(Z), cons)
    try:
        val = prob.solve(solver=solver)
    except cp.error.SolverError:
        val = prob.solve(solver="SCS")
    if Q.value is None:
        print(f"  th={th_max:5.2f} dip={dip}: FAILED ({prob.status})", flush=True)
        return None
    cv = np.array([float(np.sum(np.diag(Q.value, j))) for j in range(n+1)])
    # post-verify on fine (v,w)
    thf = np.linspace(0, np.pi, 20001)
    COf = np.cos(np.outer(thf, np.arange(n+1)))
    worst = 0.0
    for w in np.linspace(0, max(th_max, 1e-9), 61):
        gw = COf @ (wts*np.cosh(xs*w)*cv)
        worst = min(worst, gw.min())
    print(f"  th={th_max:5.2f} dip={dip}: Z = {val:.7f}  2-Z = {2-val:.7f}  "
          f"min strip g = {worst:+.2e}  [{time.time()-t0:.0f}s]", flush=True)
    return val

if __name__ == "__main__":
    print("anchors: Z(0)~1.3208 at Delta=0.04; M-T=1.3274993; box ~ th=1", flush=True)
    print("--- with dip ---", flush=True)
    for th in [0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]:
        solve(th, dip=True)
    print("--- dip forbidden (box-M-T baseline) ---", flush=True)
    for th in [1.0, 4.0]:
        solve(th, dip=False)
