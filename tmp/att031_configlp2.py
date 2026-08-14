#!/usr/bin/env python3
"""
Attempt 031 v2 — config LP, corrected decomposition.

F(alpha) = mu2 + M(alpha):
  mu2  = diagonal floor (Sigma m^2 / N), CONSTANT in alpha;
  M    = off-diagonal pair-measure transform: POSITIVE-DEFINITE (Bochner - counting
         measure >= 0), atomized -> Toeplitz-PSD;
  band pin (zeta's evaluated data): M-0-cell = 1 (the DC spike mass), and
         M-density = alpha - mu2 on (0,1];
  damped row:  int_1^S (mu2 + M) alpha^{-2} d alpha * (both sides) + 2*mu2/S <= C.

v*(C) = 2 - mu2max(C).   Anchor: C = inf -> mu2max = 1.3274993 (one-delta / M-T).
"""
import numpy as np
import cvxpy as cp
import time

def solve(C_row, S=6.0, Delta=0.04, solver="SCS", verbose=False):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    t0 = time.time()
    Q = cp.Variable((n+1, n+1), PSD=True)
    m = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n+1)])   # M-atoms (one-sided)
    mu2 = cp.Variable(nonneg=True)
    band = (xs > 1e-12) & (xs <= 1.0 + 1e-12)
    tail = xs > 1.0 + 1e-12
    cons = [m[0] == 1.0]
    # band pin: atoms = (x_j - mu2)*Delta
    idxb = np.where(band)[0]
    cons.append(m[idxb] == cp.multiply(np.full(len(idxb), Delta),
                                       (xs[idxb] - mu2*np.ones(len(idxb)))))
    # row
    if C_row is not None:
        idxt = np.where(tail)[0]
        w = 2.0/xs[idxt]**2
        cons.append(cp.sum(cp.multiply(w, m[idxt])) + mu2*(2*Delta*np.sum(1.0/xs[idxt]**2))
                    + 2*mu2/S <= C_row)
    prob = cp.Problem(cp.Maximize(mu2), cons)
    try:
        val = prob.solve(solver=solver, verbose=verbose)
    except cp.error.SolverError:
        val = prob.solve(solver="CLARABEL", verbose=verbose)
    if mu2.value is None:
        print(f"  C={C_row}: FAILED ({prob.status})", flush=True)
        return None
    print(f"  C={'inf' if C_row is None else f'{C_row:5.2f}'}:  mu2max = {val:.7f}   "
          f"v* = {2-val:.7f}   [{time.time()-t0:.0f}s]", flush=True)
    return val

if __name__ == "__main__":
    print("anchor: C=inf -> mu2max = 1.3274993 (M-T)", flush=True)
    solve(None)
    for C in [2.0, 1.9, 1.5, 1.33, 1.2, 1.05]:
        solve(C)
    print("sensitivity S=10:", flush=True)
    solve(None, S=10.0, Delta=0.05)
    solve(1.33, S=10.0, Delta=0.05)
