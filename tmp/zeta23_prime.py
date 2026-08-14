"""Prime side of the Zeta23 Gram matrix, and the D / O_1 decomposition of section 5.

KEY IDENTITY (derived, validated in zeta23_prime_validate.py).  With
    phihat(z) = int phi(x) e^{izx} dx,   tau_k = T + k h,
    delta = tau_k - tau_l,   mbar = (tau_k + tau_l)/2,   u = log n,
    R(u, delta) := int phi(t-u/2) phi(t+u/2) e^{-i delta t} dt      (ambiguity function)
we have exactly

    int phihat(tau - tau_k) phihat(tau - tau_l) cos(tau u) dtau = 2 pi R(u, delta) cos(mbar u)

and -- the simplification that makes this cheap -- for 0 <= u <= L - 2w the product
phi(t-u/2) phi(t+u/2) is the SAME taper with half-width (L-u)/2, so

    R(u, delta) = phihat(delta ; L - u, w).

Hence the prime part of the matrix is, with a_n = Lambda(n)/sqrt(n),

    P_kl := int phihat(tau-tau_k) phihat(tau-tau_l) P_X(tau) dtau
          = -2 sum_{n<=X} a_n phihat(delta_kl ; L - log n, w) cos(mbar_kl log n).
"""

import numpy as np
from scipy.special import digamma

from zeta23_bench import phihat, phi


# ---------------------------------------------------------------- nu_X = mu + Pi_X + P_X

def mu_dens(tau):
    """(2.3)  mu(tau) = (1/2pi) Re Gamma'/Gamma(1/4 + i tau/2) - log pi / 2pi."""
    return np.real(digamma(0.25 + 0.5j * np.asarray(tau, dtype=np.complex128))) / (2 * np.pi) \
        - np.log(np.pi) / (2 * np.pi)


def Pi_dens(tau, X):
    """(2.4)  Pi_X(tau) = 1/(2pi(1/4+tau^2)) + (1/pi) Re (X^s - 1)/s,  s = 1/2 + i tau."""
    tau = np.asarray(tau, dtype=np.float64)
    s = 0.5 + 1j * tau
    return 1.0 / (2 * np.pi * (0.25 + tau**2)) + np.real((X**s - 1.0) / s) / np.pi


def prime_powers(X):
    """(Lambda(n), log n) for prime powers 2 <= n <= X, as float64 arrays."""
    X = int(np.floor(X))
    if X < 2:
        return np.zeros(0), np.zeros(0)
    sieve = np.ones(X + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(X**0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.flatnonzero(sieve)
    ns, lam = [], []
    for p in primes:
        q, lp = int(p), np.log(float(p))
        while q <= X:
            ns.append(q)
            lam.append(lp)
            q *= int(p)
    ns = np.array(ns, dtype=np.float64)
    lam = np.array(lam, dtype=np.float64)
    o = np.argsort(ns)
    return lam[o], np.log(ns[o])


def P_dens(tau, lam, u):
    """(2.5)  P_X(tau) = -(1/pi) sum_{n<=X} Lambda(n) n^{-1/2} cos(tau log n)."""
    a = lam * np.exp(-0.5 * u)
    tau = np.atleast_1d(np.asarray(tau, dtype=np.float64))
    out = np.zeros(tau.size)
    step = max(1, int(4e7 // max(u.size, 1)))
    for i in range(0, tau.size, step):
        out[i:i+step] = np.cos(np.outer(tau[i:i+step], u)) @ a
    return -out / np.pi


# ---------------------------------------------------------------- the exact prime matrix

_GL = {}


def _gl(n):
    if n not in _GL:
        _GL[n] = np.polynomial.legendre.leggauss(n)
    return _GL[n]


def R_amb(u, delta, L, w):
    """R(u,delta) = int phi(t-u/2) phi(t+u/2) e^{-i delta t} dt, the ambiguity function.

    Three regimes:
      u >= L        : zero (band limit, n > X)
      w <= u <= L-2w: the two ramps do not overlap, so phi(.-u/2)phi(.+u/2) is the SAME
                      taper profile with half-width (L-u)/2  =>  R = phihat(delta; L-u, w)
      otherwise     : ramps overlap (u < w, or u > L-2w i.e. n near X).  The support is
                      short, so Gauss-Legendre on [-(L-u)/2, (L-u)/2] is exact and cheap.
    Assumes u >= w for the prime sum, which holds iff eta*L <= 2 log 2 (asserted by callers).
    """
    delta = np.asarray(delta, dtype=np.float64)
    M = L - u
    if M <= 0:
        return np.zeros_like(delta)
    if w <= u <= L - 2 * w:
        return phihat(delta, M, w)
    c = M / 2.0
    A = L / 2 - w
    brk = [-c, c]
    for cand in (u / 2 - A, A - u / 2, -u / 2 + A, -u / 2 - A, u / 2 - L / 2, L / 2 - u / 2):
        if -c < cand < c:
            brk.append(cand)
    brk = np.unique(np.round(brk, 14))
    dmax = float(np.abs(delta).max())
    T_, W_ = [], []
    for lo, hi in zip(brk[:-1], brk[1:]):
        half = (hi - lo) / 2.0
        nq = min(4000, max(48, 8 * int(np.ceil(dmax * half / np.pi)) + 48))
        x, wt = _gl(nq)
        tt = lo + half * (x + 1.0)
        T_.append(tt)
        W_.append(phi(tt - u / 2, L, w) * phi(tt + u / 2, L, w) * (half * wt))
    t = np.concatenate(T_)
    Wt = np.concatenate(W_)
    return np.cos(np.outer(delta, t)) @ Wt


def R_amb_row(u, delta, L, w):
    """R at a whole vector of delta; same contract as R_amb."""
    return R_amb(u, delta, L, w)


def P_matrix(T, L, w, c, lam, u, chunk=256):
    """P_kl = -2 sum_n a_n R(u_n, delta_kl) cos(mbar_kl u_n), exact.  Returns (d, P)."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    a = lam * np.exp(-0.5 * u)
    keep = u < L                      # band limit: only n <= X = e^L contribute
    a, u = a[keep], u[keep]
    P = np.zeros((d, d))
    for i0 in range(0, u.size, chunk):
        uu, aa = u[i0:i0+chunk], a[i0:i0+chunk]
        for j, (un, an) in enumerate(zip(uu, aa)):
            Rv = phihat(np.arange(-(d-1), d) * h, L - un, w)      # R at every delta
            Rm = Rv[(np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)]
            ang = tau * (un / 2)
            cs, sn = np.cos(ang), np.sin(ang)
            P -= 2 * an * Rm * (np.outer(cs, cs) - np.outer(sn, sn))
    return d, P


def P_matrix_fast(T, L, w, c, lam, u):
    """Same as P_matrix but batched over n with BLAS (memory ~ d^2 + d*N)."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    u = u[keep]
    idx = (np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)
    P = np.zeros((d, d))
    B = 64
    for i0 in range(0, u.size, B):
        uu, aa = u[i0:i0+B], a[i0:i0+B]
        ang = np.outer(tau, uu / 2)
        cs, sn = np.cos(ang), np.sin(ang)            # (d, B)
        for j in range(uu.size):
            Rv = phihat(np.arange(-(d-1), d) * h, L - uu[j], w)
            P -= 2 * aa[j] * Rv[idx] * (np.outer(cs[:, j], cs[:, j])
                                        - np.outer(sn[:, j], sn[:, j]))
    return d, P


def D_diagonal(T, L, w, c, lam, u):
    """The n = m part of sum_{k,l} P_kl^2, computed as a single sum over n."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    u = u[keep]
    idx = (np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)
    tot = 0.0
    for j in range(u.size):
        Rv = phihat(np.arange(-(d-1), d) * h, L - u[j], w)
        ang = tau * (u[j] / 2)
        cs, sn = np.cos(ang), np.sin(ang)
        Cm = np.outer(cs, cs) - np.outer(sn, sn)
        tot += 4 * a[j]**2 * float(np.einsum('kl,kl->', (Rv[idx] * Cm)**2,
                                             np.ones((d, d))))
    return tot


def D_diagonal_fast(T, L, w, c, lam, u):
    """Same, but the (k,l) contraction done without forming d x d twice."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    u = u[keep]
    idx = (np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)
    tot = 0.0
    for j in range(u.size):
        Rv = phihat(np.arange(-(d-1), d) * h, L - u[j], w)
        ang = tau * (u[j] / 2)
        cs, sn = np.cos(ang), np.sin(ang)
        Cm = np.outer(cs, cs) - np.outer(sn, sn)
        tot += 4 * a[j]**2 * float(np.sum((Rv[idx] * Cm)**2))
    return tot


def O1_main(T, L, l1):
    """The predicted common mode of the off-diagonal: -(T/6pi) (L - l1)_+^3."""
    return -(T / (6 * np.pi)) * max(L - l1, 0.0)**3
