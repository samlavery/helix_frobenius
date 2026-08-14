#!/usr/bin/env python3
"""
Attempt 031 — the config-side LP with the damped-tail row:
    v*(C) = 2 - mu2max(C),
    mu2max(C) = max mu2  s.t.  exists pair-density rho >= 0 (off-diagonal, even) with
        rhohat(alpha) = alpha + (1 - mu2)*spike(alpha)   on the band (0,1]   [zeta's data]
        int_1^inf [mu2*spike + rhohat](alpha) * alpha^{-2} dalpha  <=  C     [damped row]
        (spike = diagonal atom; on the tail the spike contributes ~0 mass — atom at 0)

Realizability: rho >= 0 as a function  <=>  rhohat positive-definite  <=>  (atom grid)
Toeplitz-PSD (Fejér–Riesz on the circle) — same machinery as att027_sdp.

Model conventions (asymptotic, T -> inf):
 - alpha grid atoms at j*Delta, j = 0..n, period S = n*Delta (periodization; rho >= 0 on
   the circle == on R for the atomized model).
 - Diagonal = atom at alpha=0 of mass mu2 (per side ... even measure handled one-sided
   with weight-2 bookkeeping as in att027).
 - Band pin: rhohat has DENSITY alpha on (0,1] plus atom (1-mu2) at 0
   (so total F-band = mu2*atom + rhohat-band = 1*atom + ramp = zeta's data). Atoms:
   c_0 = (1-mu2)  (the 0-cell of rho),  c_j = x_j*Delta for x_j in (0,1].
 - Tail: c_j free for x_j in (1, S], POSITIVE-DEFINITE jointly with the band (PSD).
 - Row: F-tail = mu2-atom (none on tail) + rhohat-tail:
       sum_{x_j>1} 2*c_j / x_j^2  +  (beyond-S estimate: F -> mu2 flat => mu2*2*(1/S))
       <= C.        (factor 2: both sides +-x_j; kernel alpha^{-2}.)
 - Anchors: C = inf  =>  mu2max = 1.3274993 (Montgomery–Taylor / one-delta value).
   Extremal check: mu2 = 4/3 with F-tail == mu2 flat gives row = 4/3(1 - ...) ~ 1.333.
"""
import numpy as np
import cvxpy as cp
import time

def solve(C_row, S=6.0, Delta=0.02, solver="CLARABEL", verbose=False):
    n = int(round(S/Delta))
    xs = np.arange(n+1)*Delta
    t0 = time.time()
    Q = cp.Variable((n+1, n+1), PSD=True)
    c = cp.hstack([cp.sum(cp.diag(Q, j)) for j in range(n+1)])
    mu2 = cp.Variable(nonneg=True)
    cons = []
    # band pin: c_0 = (1 - mu2) may be NEGATIVE if mu2 > 1 -> but c_0 = sum diag Q >= 0!
    # RESOLUTION: the 0-cell of rho at finite resolution is (1-mu2) only in the idealized
    # atom picture; the physical object is F = mu2-atom + rhohat >= 0 with F-band pinned.
    # Implement F directly: F_j = mu2*delta_{j0} + c_j with c = rhohat-atoms (pos-def),
    # pin: mu2 + c_0 = 1 (the 0-cell of F equals the spike mass 1)
    #      c_j = x_j*Delta for 0 < x_j <= 1 (the ramp)
    cons.append(mu2 + c[0] == 1.0)
    for j in range(1, n+1):
        if xs[j] <= 1.0 + 1e-12:
            cons.append(c[j] == xs[j]*Delta)
    # damped row: tail of F = c_j for x_j > 1 (mu2-atom sits at 0), kernel 1/x^2, both sides;
    # beyond the period: F ~ mu2 flat: contribution 2*mu2*int_S^inf dx/x^2 = 2*mu2/S
    tail_terms = [2*c[j]/xs[j]**2 for j in range(1, n+1) if xs[j] > 1.0 + 1e-12]
    if C_row is not None:
        cons.append(cp.sum(cp.hstack(tail_terms)) + 2*mu2/S <= C_row)
    prob = cp.Problem(cp.Maximize(mu2), cons)
    try:
        val = prob.solve(solver=solver, verbose=verbose)
    except cp.error.SolverError:
        val = prob.solve(solver="SCS", verbose=verbose)
    if mu2.value is None:
        print(f"  C={C_row}: FAILED ({prob.status})", flush=True)
        return None
    print(f"  C={'inf' if C_row is None else f'{C_row:5.2f}'}:  mu2max = {val:.7f}   "
          f"v* = 2-mu2 = {2-val:.7f}   [{time.time()-t0:.0f}s]", flush=True)
    return val

if __name__ == "__main__":
    print("anchor: C=inf must give mu2max = 1.3274993 (M-T / one-delta)", flush=True)
    print("=== no row (anchor) ===", flush=True)
    solve(None)
    print("=== with damped row ===", flush=True)
    for C in [2.0, 1.9, 1.5, 1.33, 1.2, 1.1, 1.05]:
        solve(C)
    print("=== sensitivity: S=10 ===", flush=True)
    solve(None, S=10.0, Delta=0.04)
    solve(1.33, S=10.0, Delta=0.04)
    solve(1.05, S=10.0, Delta=0.04)
