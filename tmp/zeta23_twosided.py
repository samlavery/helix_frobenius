"""TASK 1 & 2 -- prime side vs zero side, at lambda <= 1 (their section 8(1) check) and above.

G^zero_kl = sum_rho phihat(gamma-tau_k) phihat(gamma-tau_l)          (both signs of gamma)
G^prime_kl = int phihat(tau-tau_k) phihat(tau-tau_l) nu_X(tau) dtau,  nu_X = mu + Pi_X + P_X

The mu and Pi parts by trapezoid quadrature (the integrand is band-limited in the phihat
factors, so a step below pi/(2L) is aliasing-free); the P part by the exact identity.
"""
import sys
import time
import numpy as np

from zeta23_bench import phihat, load_zeros
from zeta23_prime import mu_dens, Pi_dens, prime_powers, R_amb

GAM = load_zeros()


def G_zero(T, L, w, c, gam=None, zmax=None):
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    g = GAM if gam is None else gam
    if zmax is not None:
        g = g[g <= zmax]
    g = np.concatenate([-g[::-1], g])          # both signs of gamma
    G = np.zeros((d, d))
    for i0 in range(0, g.size, 4096):
        M = phihat(g[i0:i0+4096][None, :] - tau[:, None], L, w)
        G += M @ M.T
    return d, G


def G_smooth(T, L, w, c, X, rng=20000.0, M=16):
    """The mu + Pi_X part by trapezoid quadrature.

    The phihat factors are band-limited (support [-L,L] in tau-frequency) and Pi_X carries
    the single frequency L, so a step below pi/(2L) is aliasing-free.  Taking step = h/M
    makes t_i - tau_k depend only on (i - kM), so all phihat values come from ONE 1D array.
    """
    h = c * 2 * np.pi / L
    step = h / M
    assert step < np.pi / (2 * L), "quadrature step above the aliasing-free bound"
    d = int(np.floor(T / h))
    lo = T - rng
    ngrid = int((2 * T + rng - lo) / step) + 1
    # phihat at every needed shift lo + i*step - (T + k*h) = (lo-T) + (i - k*M)*step
    smin, smax = -(d - 1) * M, ngrid - 1
    F = phihat((lo - T) + np.arange(smin, smax + 1) * step, L, w)
    G = np.zeros((d, d))
    CH = 100000
    for i0 in range(0, ngrid, CH):
        i1 = min(i0 + CH, ngrid)
        ii = np.arange(i0, i1)
        t = lo + ii * step
        wq = np.full(t.size, step)
        if i0 == 0:
            wq[0] *= 0.5
        if i1 == ngrid:
            wq[-1] *= 0.5
        v = (mu_dens(t) + Pi_dens(t, X)) * wq
        Phi = F[(ii[None, :] - np.arange(d)[:, None] * M) - smin]
        G += (Phi * v[None, :]) @ Phi.T
    return d, G


def G_prime_P(T, L, w, c, lam, u):
    """The P_X part, exact:  P_kl = -2 sum_n a_n R(u_n, delta) cos(mbar u_n)."""
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    tau = T + np.arange(d) * h
    keep = u < L
    a = (lam * np.exp(-0.5 * u))[keep]
    uu = u[keep]
    deltas = np.arange(-(d - 1), d) * h
    idx = (np.arange(d)[:, None] - np.arange(d)[None, :]) + (d - 1)
    P = np.zeros((d, d))
    for j in range(uu.size):
        Rv = R_amb(uu[j], deltas, L, w)
        ang = tau * (uu[j] / 2)
        cs, sn = np.cos(ang), np.sin(ang)
        P -= 2 * a[j] * Rv[idx] * (np.outer(cs, cs) - np.outer(sn, sn))
    return d, P


if __name__ == "__main__":
    print(f"{'T':>6} {'lam':>5} {'eta':>5} {'L':>8} {'X':>10} {'d':>5} {'Npp':>6} "
          f"{'max|Gp-Gz|/max|G|':>18} {'trG rel':>10} {'trG2 rel':>10}  [s]")
    for (T, lam, eta, zmax) in [(600., 0.7, 0.05, 5540.), (600., 1.0, 0.05, 5540.),
                                (600., 1.0, 0.10, 5540.), (1000., 1.0, 0.05, 5540.),
                                (600., 1.5, 0.05, 5540.), (600., 2.0, 0.05, 5540.),
                                (1000., 1.5, 0.05, 5540.)]:
        t0 = time.time()
        l = np.log(T / (2 * np.pi))
        L = lam * l
        w = eta * L / 2
        assert eta * L <= 2 * np.log(2), "taper too wide: R closed form needs w <= log 2"
        X = np.exp(L)
        lamv, u = prime_powers(X)
        d, Gz = G_zero(T, L, w, 1.0, zmax=zmax)
        _, Gs = G_smooth(T, L, w, 1.0, X)
        _, P = G_prime_P(T, L, w, 1.0, lamv, u)
        Gp = Gs + P
        rel = np.abs(Gp - Gz).max() / np.abs(Gz).max()
        print(f"{T:6.0f} {lam:5.2f} {eta:5.2f} {L:8.4f} {X:10.1f} {d:5d} {u.size:6d} "
              f"{rel:18.2e} {abs(np.trace(Gp)/np.trace(Gz)-1):10.2e} "
              f"{abs((Gp**2).sum()/(Gz**2).sum()-1):10.2e}  [{time.time()-t0:.0f}]")
