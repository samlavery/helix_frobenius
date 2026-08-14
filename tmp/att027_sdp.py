#!/usr/bin/env python3
"""
Attempt 027 — band-limited CGdL constant Z* via the exact Fejér–Riesz (Toeplitz) SDP.

Variables: atoms c_j >= represent the even measure  c_0 δ_0 + Σ_{j>=1} c_j (δ_{x_j}+δ_{-x_j}),
x_j = j*Delta on [0, S].  Then g(u) = c_0 + 2 Σ c_j cos(x_j u), periodic with period 2π/Δ,
and  g >= 0 on R  <=>  c_j = Σ_k Q_{k,k+j}, Q PSD  (Fejér–Riesz on the circle — EXACT).

Continuum dictionary: c_0 ≈ ghat(0)*Delta, c_j ≈ ghat(x_j)*Delta.

    Z = ghat(0) + 2∫_0^1 ghat(x) x dx  ≈  c_0/Delta + 2 Σ_{x_j<=1} x_j c_j
    normalization g(0) = c_0 + 2 Σ c_j = 1
    dip: c_j <= 0 for x_j in [dip_from, S]

Controls:
    S=1  ->  Montgomery–Taylor 1.3274992   (POSITIVE CONTROL — must reproduce)
    S->large -> CGdL(RH) 1.3208
    Fejér feasible: Z = 4/3.
"""
import numpy as np
import cvxpy as cp
import time

def solve(S=2.0, Delta=0.01, dip_from=1.0, solver="CLARABEL", verbose=False):
    n = int(round(S / Delta))
    t0 = time.time()
    Q = cp.Variable((n + 1, n + 1), PSD=True)
    c = [cp.sum(cp.diag(Q, j)) for j in range(n + 1)]
    xs = np.arange(n + 1) * Delta

    Z = c[0] / Delta + 2 * cp.sum(cp.hstack(
        [c[j] * xs[j] for j in range(1, n + 1) if xs[j] <= 1.0 + 1e-12]))
    cons = [c[0] + 2 * cp.sum(cp.hstack([c[j] for j in range(1, n + 1)])) == 1]
    for j in range(1, n + 1):
        if xs[j] >= dip_from - 1e-12:
            cons.append(c[j] <= 0)

    prob = cp.Problem(cp.Minimize(Z), cons)
    val = prob.solve(solver=solver, verbose=verbose)
    if Q.value is None:
        print(f"  S={S:4.1f} Delta={Delta:.4f}: SOLVE FAILED ({prob.status})", flush=True)
        return None, None, None
    cv = np.array([float(np.sum(np.diag(Q.value, j))) for j in range(n + 1)])
    # audit: g on a fine incommensurate u-grid over one period
    period = 2 * np.pi / Delta
    u = np.arange(0.0, period, 0.0137)
    g = cv[0] + 2 * (np.cos(np.outer(u, xs[1:])) * cv[1:]).sum(axis=1)
    print(f"  S={S:4.1f} Delta={Delta:.4f} (n={n:4d}): Z* = {val:.7f}  2-Z = {2-val:.7f}"
          f"  min g = {g.min():+.1e}  [{time.time()-t0:.1f}s]", flush=True)
    return val, cv, xs

if __name__ == "__main__":
    mt = 0.5 + (1.0/np.sqrt(2.0)) / np.tan(1.0/np.sqrt(2.0))
    print(f"anchors: Fejér 4/3=1.3333333; M–T={mt:.7f}; CGdL(RH)=1.3208", flush=True)

    print("=== POSITIVE CONTROL S=1 ===", flush=True)
    for D in [0.04, 0.02, 0.01]:
        solve(S=1.0, Delta=D)

    print("=== S=2 (transplant class) ===", flush=True)
    out = {}
    for D in [0.04, 0.02, 0.01]:
        out[D] = solve(S=2.0, Delta=D)

    print("=== S=1.5, 3 (dip-band width dependence) ===", flush=True)
    solve(S=1.5, Delta=0.01)
    solve(S=3.0, Delta=0.02)

    if out.get(0.01, (None,))[0] is not None:
        val, cv, xs = out[0.01]
        np.save("/Users/samuellavery/work/helix_frobenius/tmp/att027_c_S2.npy", np.vstack([xs, cv]))
        print(f"\nS=2, Delta=0.01: 2-Z = {2-val:.7f}  (M–T gives 0.6725007; CGdL-RH 0.6792)", flush=True)
