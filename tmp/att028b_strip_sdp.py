#!/usr/bin/env python3
"""
Attempt 028b — Z(theta_max): the dip-LP with strip-positivity constraints.

Z(th) := min  c0/Delta + 2 sum_{x_j<=1} x_j c_j
 s.t.  g_w(v) = sum_j c_j cosh(x_j w) cos-poly  >= 0 on R,  for w in [0, th]   (strip)
       g_0(0) = 1;   c_j <= 0 for x_j in [1, 2]                                (dip)

Each w-slice is an exact Toeplitz-PSD condition on atoms c_j*cosh(x_j*w).
w-sampling: geometric-ish grid on [0, th]; post-verify on a fine w-grid.

Anchors: Z(0) = 1.3211658 (attempt 028, S=2);  Z(inf) -> 1.3274993 (M-T).
Box hypothesis (GS25: |beta-1/2| < 1/(2 log T)) corresponds to th = 1
(pair self-terms theta = 2yl <= 1; cross terms <= 1 as well).
"""
import numpy as np
import cvxpy as cp
import time

def solve(th_max, Delta=0.02, S=2.0, nw=7, solver="CLARABEL", verbose=False):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    t0 = time.time()
    # PSD block per w-sample; w=0 always included
    if th_max > 0:
        ws = np.unique(np.concatenate([[0.0], np.linspace(0, th_max, nw)[1:]]))
    else:
        ws = np.array([0.0])
    Qs = [cp.Variable((n+1, n+1), PSD=True) for _ in ws]
    # atoms of slice i:  b_j^{(i)} = c_j * cosh(x_j w_i);  slice-0 defines c_j.
    c = [cp.sum(cp.diag(Qs[0], j)) for j in range(n+1)]
    cons = []
    for i, w in enumerate(ws[1:], start=1):
        ch = np.cosh(xs*w)
        for j in range(n+1):
            cons.append(cp.sum(cp.diag(Qs[i], j)) == c[j]*ch[j])
    Z = c[0]/Delta + 2*cp.sum(cp.hstack([c[j]*xs[j] for j in range(1, n+1) if xs[j] <= 1.0+1e-12]))
    cons.append(c[0] + 2*cp.sum(cp.hstack([c[j] for j in range(1, n+1)])) == 1)
    for j in range(1, n+1):
        if xs[j] >= 1.0 - 1e-12:
            cons.append(c[j] <= 0)
    prob = cp.Problem(cp.Minimize(Z), cons)
    try:
        val = prob.solve(solver=solver, verbose=verbose)
    except cp.error.SolverError:
        val = prob.solve(solver="SCS", verbose=verbose)
    if Qs[0].value is None:
        print(f"  th={th_max:5.2f}: FAILED ({prob.status})", flush=True)
        return None, None, None
    cv = np.array([float(np.sum(np.diag(Qs[0].value, j))) for j in range(n+1)])
    # post-verify: min over fine (v,w) grid of the cosh-weighted trig poly
    thv = np.linspace(0, 2*np.pi, 20001)
    worst = 0.0
    for w in np.linspace(0, th_max, 41) if th_max > 0 else [0.0]:
        bw = cv*np.cosh(xs*w)
        gw = bw[0] + 2*(np.cos(np.outer(thv[::5], np.arange(1, n+1)))*bw[1:]).sum(axis=1)
        worst = min(worst, gw.min())
    print(f"  th={th_max:5.2f}: Z = {val:.7f}   2-Z = {2-val:.7f}   "
          f"min strip g = {worst:+.2e}   [{time.time()-t0:.0f}s]", flush=True)
    return val, cv, xs

if __name__ == "__main__":
    print("anchors: Z(0)=1.3211658 (028); M-T=1.3274993; box hypothesis ~ th=1", flush=True)
    for th in [0.0, 0.5, 1.0, 2.0, 4.0, 8.0]:
        solve(th)
