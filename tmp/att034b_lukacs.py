#!/usr/bin/env python3
r"""
Implementation B, second positivity certificate: LUKACS on [-1,1] in the
Chebyshev basis, instead of Fejer-Riesz/Toeplitz on the circle.

p(theta) = b_0 + 2 sum_{j>=1} b_j cos(j theta) = P(x), x = cos theta,
P = sum_k t_k T_k(x) with t_0 = b_0, t_k = 2 b_k.
Lukacs:  P >= 0 on [-1,1]  <=>  P = sigma_0 + (1-x^2) sigma_1, sigma_i SOS
         (deg sigma_0 <= 2*floor(n/2), deg (1-x^2)sigma_1 <= n).
Two PSD blocks of size ~n/2 instead of one of size n+1: different SDP shape,
different conditioning, same mathematical content.  A disagreement with the
Toeplitz value is a solver/formulation bug; agreement is evidence.
"""
import numpy as np
import cvxpy as cp

MT = 0.5 + (1 / np.sqrt(2)) / np.tan(1 / np.sqrt(2))


def cheb_mul_table(d, N):
    """M[i,j,k] : coefficient of T_k in T_i*T_j, for i,j<=d, k<=N."""
    M = np.zeros((d + 1, d + 1, N + 1))
    for i in range(d + 1):
        for j in range(d + 1):
            for k, w in ((i + j, 0.5), (abs(i - j), 0.5)):
                if k <= N:
                    M[i, j, k] += w
    return M


def solve_lukacs(W, Delta=0.05, S=2.0, dip=True, solver="CLARABEL"):
    n = int(round(S / Delta))
    xs = np.arange(n + 1) * Delta
    sh = 1.0 / np.cosh(xs * W)
    d0 = n // 2
    d1 = (n - 2) // 2
    G0 = cp.Variable((d0 + 1, d0 + 1), PSD=True)
    G1 = cp.Variable((d1 + 1, d1 + 1), PSD=True)
    M0 = cheb_mul_table(d0, n)
    M1 = cheb_mul_table(d1, n + 2)

    t = [cp.sum(cp.multiply(G0, M0[:, :, k])) for k in range(n + 1)]
    # multiply sigma1 series by (1-x^2) = (T_0 - T_2)/2
    s1 = [cp.sum(cp.multiply(G1, M1[:, :, k])) for k in range(n + 3)]
    for k in range(n + 1):
        e = 0.5 * s1[k]
        t[k] = t[k] + e
    for k in range(n + 3):
        for m, w in ((k + 2, -0.25), (abs(k - 2), -0.25)):
            if m <= n:
                t[m] = t[m] + w * s1[k]
    # degrees n+1, n+2 of (1-x^2)sigma1 must vanish
    cons = []
    for k in (n + 1, n + 2):
        e = 0
        if k <= n + 2:
            e = 0.5 * s1[k]
        for kk in range(n + 3):
            for m, w in ((kk + 2, -0.25), (abs(kk - 2), -0.25)):
                if m == k:
                    e = e + w * s1[kk]
        cons.append(e == 0)

    b = [t[0]] + [t[k] / 2.0 for k in range(1, n + 1)]
    obj = b[0] / Delta + sum(2.0 * xs[j] * sh[j] * b[j]
                             for j in range(1, n + 1) if xs[j] <= 1 + 1e-12)
    cons.append(b[0] + sum(2.0 * sh[j] * b[j] for j in range(1, n + 1)) == 1)
    for j in range(1, n + 1):
        if dip and S > 1.0 and 1.0 - 1e-12 <= xs[j] and j < n:
            cons.append(b[j] <= 0)
        if (not dip or S <= 1.0) and xs[j] > 1 + 1e-12:
            cons.append(b[j] == 0)
    cons.append(b[n] == 0)
    prob = cp.Problem(cp.Minimize(obj), cons)
    try:
        val = prob.solve(solver=solver)
    except Exception:
        val = prob.solve(solver="SCS", eps=1e-9, max_iters=200000)
    return val, prob.status


if __name__ == "__main__":
    import sys
    sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
    from att034b_stripB import solveB
    print("  A     S   dip     Lukacs-SOS      Toeplitz-FR       |diff|")
    for (A, S, dip, D) in [(0.0, 1.0, False, 0.05), (0.0, 2.0, True, 0.05),
                           (0.10, 2.0, True, 0.05), (0.25, 2.0, True, 0.05),
                           (0.50, 2.0, True, 0.05), (1.00, 2.0, True, 0.05)]:
        v1, s1 = solve_lukacs(2 * A, Delta=D, S=S, dip=dip)
        v2, cv, xs, s2 = solveB(2 * A, Delta=D, S=S, dip=dip)
        print(f"{A:5.2f} {S:4.1f} {str(dip):>5}   {v1:.7f}[{s1[:7]}]   "
              f"{v2:.7f}   {abs(v1-v2):.2e}", flush=True)
