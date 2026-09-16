"""harmonic_pencil.py -- the 3D harmonic pencil: eigenvalues and rank drop from the carrier's own
moment vector.

THE POINT.  The log-jets at a REAL anchor y0 are power sums over ALL singularities of log G,
G(y) = F(1/2 + iy):
      A_m = sum_j d_j^m,      d_j = 1/(y0 - y_j).
And a zero of zeta at rho = beta + i gamma sits at
      y_j = gamma - i(beta - 1/2),
so  Im y_j = 0  <=>  beta = 1/2.  **An off-line zero appears as a COMPLEX node.**  The pencil's
eigenvalues therefore report not only WHERE the events are but whether they are ON the line --
which is the radial (off-line) information, read from data already computed on the line.

POSITIVE CONTROL built in: the fiber carries the lane factor 1 - 2^{1-s}, whose zeros sit at
Re s = 1, i.e. Im y = -1/2, spaced 2 pi / log 2 = 9.0647 apart in Re y.  A working pencil must
place them there.  If it does not, the pencil is not resolving what it claims to.

METHOD.  Matrix-pencil (Hua-Sarkar) rather than raw Hankel GEVP: build the Hankel data matrix,
take its SVD, keep the K dominant directions, and read the eigenvalues off the shifted pair.  The
singular-value profile IS the rank-drop detector: the number of singular values above the noise is
the number of events the window resolves.
"""
import math
import numpy as np
import mpmath as mp

def jets_from_moments(M, mmax):
    """moments M_r = l(H^r v) -> log-derivative jets A_m (the Bell/cumulant recursion)."""
    f = [((-1j)**k)*M[k]/M[0] for k in range(mmax+1)]
    L = [mp.mpc(0)]*(mmax+1)
    for m in range(1, mmax+1):
        acc = f[m]
        for j in range(1, m):
            acc -= mp.binomial(m-1, j-1)*L[j]*f[m-j]
        L[m] = acc
    return [None] + [((-1)**(m-1)/mp.factorial(m-1))*L[m] for m in range(1, mmax+1)]

def pencil(A, K, scale, m0=1):
    """matrix pencil on the power sums A_{m0}..A_{2K+m0-1}; returns (nodes d_j, singular values).

    `scale` rescales the power sums to O(1): A_m ~ d^{-m} spans many orders otherwise.  The
    eigenvalues come back divided by `scale`, so they are undone at the end."""
    # Hua-Sarkar: the data matrix must be (N-L) x (L+1) so that deleting the first/last ROW of the
    # right singular vectors gives a conformable shifted pair.  Building it (N-L) x L instead makes
    # the pencil meaningless -- caught by the planted-node control at 840b.
    N = 2*K + 1
    a = np.array([complex(A[m0+k])*scale**(m0+k) for k in range(N)], dtype=complex)
    L = K
    Y = np.array([[a[i+j] for j in range(L+1)] for i in range(N-L)], dtype=complex)
    U, S, Vh = np.linalg.svd(Y)
    Kr = min(K, np.sum(S > S[0]*1e-12))
    # the ROW space of Y is spanned by the rows of Vh, i.e. by conj(v_k) -- so the shift pair is
    # built from Vh.T, NOT Vh.conj().T.  Using the latter returns the CONJUGATE nodes, which
    # inverts precisely the off-line information the pencil exists to read (caught by the planted
    # control at 840b: a node planted at Im = -0.30 came back at +0.30).
    V = Vh.T[:, :Kr]
    Y1, Y2 = V[:-1, :], V[1:, :]
    Z = np.linalg.pinv(Y1) @ Y2
    ev = np.linalg.eigvals(Z)
    return ev/scale, S

def nodes_to_y(ev, y0):
    """d = 1/(y0 - y)  =>  y = y0 - 1/d."""
    out = []
    for d in ev:
        if abs(d) > 1e-300: out.append(y0 - 1.0/d)
    return out
