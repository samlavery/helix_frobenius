#!/usr/bin/env python3
"""
Attempt 061 — joint configuration LP: zeta23's F-band data + our Theorem-3 R(s)-curve.

Base model = att031 (anchored: mu2max = 1.3274993 = M-T at C=inf).
Added: member-cap constraints. The Toeplitz-PSD certificate's gap-side density is
  f(x) = m0 + 2 sum_j m_j cos(2 pi alpha_j x)   (period X = 1/Delta),
and the Theorem-3 floor holds at every member of a gap<=s cluster INCLUDING
multiplicities, so (pairs-only extremal, justified by m/m^2 doubles-optimality):
  (mu2 - 1) + int_0^s f dx <= B(s) + eps_alias,
  B(s) = 1/(1 + lambda(s)^2),  lambda(s) = [2 sinc^2(pi s/2) - 4/3]/0.4714   (theta->1).
Question: does the joint LP push mu2max below 1.3274993? v* = 2 - mu2max.
"""
import numpy as np
import cvxpy as cp
import time

def B_curve(s):
    sc = np.sinc(s/2.0)          # np.sinc(x) = sin(pi x)/(pi x): sinc(pi s/2)-arg -> s/2
    num = 2*sc**2 - 4.0/3.0
    if num <= 0: return None
    lam = num/0.4714
    return 1.0/(1.0 + lam**2)

def solve(with_caps, C_row=None, S=6.0, Delta=0.04, eps_alias=0.02, verbose=False):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    t0 = time.time()
    Q = cp.Variable((n+1, n+1), PSD=True)
    m = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n+1)])
    mu2 = cp.Variable(nonneg=True)
    band = (xs > 1e-12) & (xs <= 1.0 + 1e-12)
    cons = [m[0] == 1.0]
    idxb = np.where(band)[0]
    cons.append(m[idxb] == cp.multiply(np.full(len(idxb), Delta),
                                       (xs[idxb] - mu2*np.ones(len(idxb)))))
    if C_row is not None:
        idxt = np.where(xs > 1.0 + 1e-12)[0]
        w = 2.0/xs[idxt]**2
        cons.append(cp.sum(cp.multiply(w, m[idxt])) + mu2*(2*Delta*np.sum(1.0/xs[idxt]**2))
                    + 2*mu2/S <= C_row)
    caps_used = []
    if with_caps:
        for s in [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35]:
            B = B_curve(s)
            if B is None: continue
            # int_0^s f = m0*s + sum_j m_j sin(2 pi a_j s)/(pi a_j)
            coef = np.zeros(n+1); coef[0] = s
            for j in range(1, n+1):
                coef[j] = np.sin(2*np.pi*xs[j]*s)/(np.pi*xs[j])
            cons.append((mu2 - 1.0) + cp.sum(cp.multiply(coef, m)) <= B + eps_alias)
            caps_used.append((s, B))
    prob = cp.Problem(cp.Maximize(mu2), cons)
    try:
        val = prob.solve(solver="SCS", verbose=verbose)
    except cp.error.SolverError:
        val = prob.solve(solver="CLARABEL", verbose=verbose)
    tag = "JOINT" if with_caps else "base "
    if mu2.value is None:
        print(f"  {tag}: FAILED ({prob.status})", flush=True)
        return None
    print(f"  {tag} C={'inf' if C_row is None else C_row}: mu2max = {val:.7f}   "
          f"N0s/N >= {2-val:.7f}   [{time.time()-t0:.0f}s]", flush=True)
    if with_caps and mu2.value is not None:
        # report which caps bind
        mv = np.array([float(cp.sum(cp.diag(Q, j)).value) for j in range(n+1)])
        for s, B in caps_used:
            coef = np.zeros(n+1); coef[0] = s
            for j in range(1, n+1):
                coef[j] = np.sin(2*np.pi*xs[j]*s)/(np.pi*xs[j])
            lhs = (val - 1.0) + float(coef @ mv)
            print(f"    cap s={s:.2f}: members = {lhs:.4f}  vs  B+eps = {B+0.02:.4f}  "
                  f"{'BINDING' if lhs > B + 0.02 - 1e-3 else ''}", flush=True)
    return val

if __name__ == "__main__":
    print("anchor check (must be 1.3274993):", flush=True)
    solve(False)
    print("joint LP (their band + our R(s)-curve):", flush=True)
    solve(True)
    print("discretization check Delta=0.03, S=8:", flush=True)
    solve(True, S=8.0, Delta=0.03)
