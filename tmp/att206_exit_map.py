"""att206: map of the exit segment -- the pole-subtracted pencil through s0 = 1
into the strip (GOAL_HP_UNCONDITIONAL: boundary scalar through the continuation).

f_reg(s) = -zeta'/zeta(s) - 1/(s-1)   (analytic at s=1; real on (0,1) since zeta
has no real zeros in (0,1) -- classical, unconditional).

m^reg_k(s0) = (-1)^k f_reg^{(k)}(s0).  Zeros-side reading (Hadamard):
m^reg = -(zero-resolvent Laplace moments) - (trivial part) + const, so the
regularized pencil is EXPECTED indefinite; its inertia profile vs s0 is the
information: how many zero-directions the dimension-n pencil sees as s0 descends
toward the critical line, where the Mobius images 1/(s0-rho) sharpen.

Report along the sweep: eigs/inertia of G0^reg, generalized spectrum of
(G1^reg, G0^reg) (real vs complex), h_n-analogue (quadrature error of x^{2n}).
"""
import numpy as np
from mpmath import mp, zeta, diff, mpf

mp.dps = 40
N = 4
KMAX = 2 * N


def f_reg(s):
    return -zeta(s, derivative=1) / zeta(s) - 1 / (s - 1)


def jets(s0):
    return np.array([float(((-1) ** k) * diff(f_reg, mpf(s0), k))
                     for k in range(KMAX + 1)])


print(" s0      m0_reg      inertia(G0)   gen-spectrum of (G1,G0)                    h_n-analogue")
for s0 in [1.5, 1.3, 1.1, 1.02, 1.001, 0.999, 0.98, 0.9, 0.8, 0.7, 0.6, 0.55]:
    m = jets(s0)
    G0 = np.array([[m[j + k] for k in range(N)] for j in range(N)])
    G1 = np.array([[m[j + k + 1] for k in range(N)] for j in range(N)])
    ev0 = np.linalg.eigvalsh(G0)
    n_plus = int(np.sum(ev0 > 1e-12))
    n_minus = int(np.sum(ev0 < -1e-12))
    # generalized spectrum via QZ-free route: eig of G0^{-1} G1 (G0 invertible off events)
    try:
        gen = np.linalg.eigvals(np.linalg.solve(G0, G1))
        gen = np.sort_complex(gen)
        nreal = int(np.sum(np.abs(gen.imag) < 1e-8 * (1 + np.abs(gen.real))))
        gs = " ".join(("%.3f" % g.real) if abs(g.imag) < 1e-8 * (1 + abs(g.real))
                      else ("%.2f%+.2fi" % (g.real, g.imag)) for g in gen)
    except np.linalg.LinAlgError:
        nreal, gs = -1, "G0 singular"
    # h_n analogue: match moments 0..2N-1 by the generalized eigen-data if all real
    if nreal == N:
        lam = np.sort(gen.real)
        V = np.vander(lam, N, increasing=True).T
        try:
            w = np.linalg.solve(V, m[:N])
            h = m[2 * N] - np.sum(w * lam ** (2 * N))
            hs = "%+.3e" % h
        except np.linalg.LinAlgError:
            hs = "vander singular"
    else:
        hs = "(complex nodes)"
    print(" %5.3f  %+.4e   (%d,%d)        %-42s %s"
          % (s0, m[0], n_plus, n_minus, gs, hs))
