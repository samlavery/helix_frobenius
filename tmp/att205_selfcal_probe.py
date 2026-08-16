"""att205: is the warp self-calibrating? Test the internal (Toda) drift law.

Anchor flow sigma_dot = -x sigma  (s0 increasing)  =>  m_k' = -m_{k+1}: the moment
flow is the pencil's own shift. Classical quadrature-deformation law predicts the
node motion is INTERNAL to the pencil's quadrature data plus ONE scalar:

    d lambda_a / d s0  =  - h_n / ( w_a * Pn'(lambda_a)^2 ),

with (lambda_a, w_a) the Gauss data, Pn the monic node polynomial, and
h_n = m_{2n} - sum_a w_a lambda_a^{2n}  (the quadrature error of x^{2n} -- the single
datum beyond the pencil: the tail/boundary coupling).

Test at s0 = 1.5, N = 4 against the direct perturbation drifts (att201 formula).
"""
import numpy as np
from mpmath import mp, zeta, diff

mp.dps = 25
N = 4
S0 = 1.5
KMAX = 2 * N  # need m_0..m_8

_f = lambda s: -zeta(s, derivative=1) / zeta(s)
m = np.array([float(((-1) ** k) * diff(_f, mp.mpf(S0), k)) for k in range(KMAX + 1)])

G0 = np.array([[m[j + k] for k in range(N)] for j in range(N)])
G1 = np.array([[m[j + k + 1] for k in range(N)] for j in range(N)])
G0d = np.array([[-m[j + k + 1] for k in range(N)] for j in range(N)])   # d/ds0
G1d = np.array([[-m[j + k + 2] for k in range(N)] for j in range(N)])

L = np.linalg.cholesky(G0)
Linv = np.linalg.inv(L)
lam, Y = np.linalg.eigh(Linv @ G1 @ Linv.T)
Wv = Linv.T @ Y

# direct perturbation drifts d lambda / d s0 (att201 formula, path = s0 itself)
drift_direct = np.array([Wv[:, a] @ (G1d - lam[a] * G0d) @ Wv[:, a] for a in range(N)])

# Gauss weights: w_a = 1 / sum_k p_k(lam_a)^2 -- easiest via Vandermonde moment match
V = np.vander(lam, N, increasing=True).T          # V[k,a] = lam_a^k
w = np.linalg.solve(V, m[:N])                     # sum_a w_a lam_a^k = m_k, k<N
print("nodes   :", np.round(lam, 6))
print("weights :", np.round(w, 6))

# monic node polynomial and its derivative at the nodes
Pn = np.poly(lam)                                  # descending coeffs, monic
Pn_prime = np.array([np.polyval(np.polyder(Pn), x) for x in lam])

# quadrature error of x^{2n}: h_n = m_{2n} - sum w lam^{2n}
h_n = m[2 * N] - np.sum(w * lam ** (2 * N))
print("h_n (tail coupling) = %.8e" % h_n)

drift_internal = -h_n / (w * Pn_prime ** 2)

print("\n a   direct dl/ds0     internal law      ratio")
for a in range(N):
    print(" %d   %+.8e   %+.8e   %.10f"
          % (a, drift_direct[a], drift_internal[a], drift_direct[a] / drift_internal[a]))

err = np.max(np.abs(drift_direct / drift_internal - 1))
print("\nmax |ratio - 1| = %.2e" % err)
print("VERDICT:", "PASS - the warp velocity is INTERNAL up to the single scalar h_n"
      if err < 1e-6 else "FAIL")
