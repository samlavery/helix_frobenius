"""
Zeta23 harmonization bench.

Reproduces the zero-side Gram matrix G_kl = sum_rho phihat(gamma-tau_k) phihat(gamma-tau_l)
of "More than two thirds of the zeta zeros on the critical line" (Table 3, p.26),
then rescans the SAMPLING SPACING h' = c * h with h = 2pi/L, everything else fixed.

Conventions (paper 1.8, 2.2):
  fhat(z) = int f(u) e^{+izu} du
  phi(u)  = rho((L/2-|u|)/w),  rho(x) = x - sin(2 pi x)/(2 pi) on [0,1], 0 below, 1 above
  w = eta*L/2      (paper p.25: "ramps of width w = eta L / 2")
  a = (1/L) int phi^2      (paper: a = 1 - 0.603 eta)
  l = log(T/2pi), L = lambda*l, h = 2pi/L, d = floor(T/h), tau_k = T + k h
  C = (tr R)^2 / tr R^2    (scale invariant, so C_G = C_Gtilde)
"""

import numpy as np

# ---------------------------------------------------------------- taper / transform

RHO_L2 = 1.0 / 3.0 + 5.0 / (8.0 * np.pi**2)     # int_0^1 rho(x)^2 dx


def rho(x):
    x = np.clip(x, 0.0, 1.0)
    return x - np.sin(2 * np.pi * x) / (2 * np.pi)


def phi(u, L, w):
    return rho((L / 2 - np.abs(u)) / w)


def a_const(L, w):
    """a = (1/L) int phi^2, closed form."""
    return 1.0 - 2.0 * (w / L) * (1.0 - RHO_L2)


def b_const(L, w):
    """b = (1/L) int phi^4, closed form via numerical int_0^1 rho^4."""
    x = np.linspace(0, 1, 200001)
    r4 = np.trapezoid(rho(x) ** 4, x)
    return 1.0 - 2.0 * (w / L) * (1.0 - r4)


def phihat(r, L, w):
    """
    phihat(r) = int phi(u) e^{iru} du = 2 int_0^{L/2} phi(u) cos(ru) du.
    Closed form; all removable singularities (r=0, rw=2pi) written via np.sinc.
    A = L/2 - w (flat part), B = L/2, s = r w, theta = r B.
    """
    r = np.abs(np.asarray(r, dtype=np.float64))
    A = L / 2 - w
    B = L / 2
    s = r * w
    theta = r * B

    flat = 2.0 * A * np.sinc(r * A / np.pi)          # 2 sin(rA)/r

    sp = s / (2 * np.pi)
    # Cc = sin s / s + (cos s - 1)/s^2 + (cos s - 1)/(4pi^2 - s^2)
    Cc = (np.sinc(s / np.pi)
          - 0.5 * np.sinc(sp) ** 2
          + 0.5 * np.sinc(sp + 1.0) * np.sinc(sp - 1.0))
    # Cs = -cos s / s + sin s / s^2 + sin s /(4pi^2 - s^2)
    with np.errstate(divide='ignore', invalid='ignore'):
        Cs_main = np.where(s > 1e-8,
                           -np.cos(s) / np.where(s > 1e-8, s, 1.0)
                           + np.sin(s) / np.where(s > 1e-8, s, 1.0) ** 2,
                           s / 3.0)          # -cos s/s + sin s/s^2 -> s/3 as s->0
    Cs = Cs_main - np.sinc((s - 2 * np.pi) / np.pi) / (s + 2 * np.pi)

    ramp = 2.0 * w * (np.cos(theta) * Cc + np.sin(theta) * Cs)
    return flat + ramp


# ---------------------------------------------------------------- zeros

def load_zeros(path="/Users/samuellavery/work/helix_frobenius/tmp/zeta_zeros_cache.txt"):
    return np.loadtxt(path, dtype=np.float64)


# ---------------------------------------------------------------- the Gram traces

def traces(gam, T, L, w, c, chunk=4096):
    """
    tau_k = T + k h', h' = c*2pi/L, k = 0..d-1, d = floor(T/h').
    Returns d, tr G, tr G^2 with G = M M^T, M[k,i] = phihat(gam_i - tau_k).
    Computed on the N x N side: K = M^T M, tr G = tr K, tr G^2 = ||K||_F^2.
    """
    h = c * 2 * np.pi / L
    d = int(np.floor(T / h))
    N = gam.size
    K = np.zeros((N, N), dtype=np.float64)
    trG = 0.0
    for k0 in range(0, d, chunk):
        k = np.arange(k0, min(k0 + chunk, d), dtype=np.float64)
        tau = T + k * h
        M = phihat(gam[None, :] - tau[:, None], L, w)   # (nk, N)
        trG += float(np.einsum('ki,ki->', M, M))
        K += M.T @ M
    trG2 = float(np.einsum('ij,ij->', K, K))
    return d, trG, trG2, K


def rvm(t):
    """Riemann-von Mangoldt main term N(t) = (t/2pi) log(t/2pi e)."""
    return (t / (2 * np.pi)) * (np.log(t / (2 * np.pi)) - 1.0)
