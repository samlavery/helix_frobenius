#!/usr/bin/env python3
"""
att537b — same experiment as att537 (Weil form Gram matrices on the phasor bank vs support
length), vectorised: Gauss–Legendre for the profile transforms, trapezoid on a fine grid for the
Archimedean line integrals, scipy's complex digamma. Same pre-registration (ledger 537, P1–P3).
"""
import numpy as np
from scipy.special import digamma
import mpmath as mp
import sys, time, os

def bump(x, c, w):
    u = (x - c) / w
    out = np.zeros_like(x, dtype=float)
    m = np.abs(u) < 1
    out[m] = np.exp(-1.0 / (1.0 - u[m] ** 2))
    return out

# Gauss–Legendre nodes on [c-w, c+w]
GLN = 240
gl_x, gl_w = np.polynomial.legendre.leggauss(GLN)

def nodes(c, w):
    return c + w * gl_x, w * gl_w

def F_on(c, w, s):
    """F_g(s) = ∫ g(x) e^{(s-1/2)x} dx for an array of complex s. The number of Gauss–Legendre
    nodes is adapted to the oscillation count 2w·max|Im s|/(2π) (att537b L=1.8 failure: 240 nodes
    cannot resolve e^{iγx} on a length-0.9 interval for γ ≈ 1400)."""
    tmax = float(np.max(np.abs(np.imag(s)))) if np.size(s) else 0.0
    n = int(max(GLN, 12 * (2 * w * tmax / (2 * np.pi)) + 60))
    xg, wg = np.polynomial.legendre.leggauss(n)
    x = c + w * xg; wt = w * wg
    gx = bump(x, c, w)
    out = np.empty(len(s), dtype=complex)
    # chunk over s to bound memory
    step = max(1, 4_000_000 // n)
    for i in range(0, len(s), step):
        ex = np.exp(np.outer(s[i:i + step] - 0.5, x))
        out[i:i + step] = ex @ (gx * wt)
    return out

def G_pair(cj, ck, w, x0):
    """G_{jk}(x0) = ∫ g_j(y) g_k(y - x0) dy  (real bumps)."""
    lo = max(cj - w, ck - w + x0); hi = min(cj + w, ck + w + x0)
    if hi <= lo:
        return 0.0
    y = 0.5 * (hi + lo) + 0.5 * (hi - lo) * gl_x
    wt = 0.5 * (hi - lo) * gl_w
    return float(np.sum(bump(y, cj, w) * bump(y - x0, ck, w) * wt))

def E(s):
    return 1 / s + 1 / (s - 1) - np.log(np.pi) / 2 + digamma(s / 2) / 2

def primes_upto(N):
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return np.nonzero(sieve)[0]

def vonmangoldt_terms(xmax):
    N = int(np.exp(xmax)) + 1
    out = []
    for p in primes_upto(N):
        pk = int(p)
        while pk <= N:
            out.append((pk, np.log(float(p))))
            pk *= int(p)
    return out

def zeros(N, cache="tmp/zeta_zeros_%d.npy"):
    fn = cache % N
    if os.path.exists(fn):
        return np.load(fn)
    mp.mp.dps = 15
    z = np.array([float(mp.zetazero(i).imag) for i in range(1, N + 1)])
    np.save(fn, z)
    return z

def gram_prime_side(centres, w, L, a=-0.5, b=1.5, T=250.0, dt=0.01):
    n = len(centres)
    t = np.arange(-T, T + dt / 2, dt)
    sb = b + 1j * t
    sa = a + 1j * t
    Fb = [F_on(c, w, sb) for c in centres]                      # F_j(b+it)
    Fb_refl = [np.conj(F_on(c, w, 1 - np.conj(sb))) for c in centres]  # conj F_k(1 - conj(b+it))
    Fa = [F_on(c, w, sa) for c in centres]
    Fa_refl = [np.conj(F_on(c, w, 1 - np.conj(sa))) for c in centres]
    Eb = E(sb); Ea = E(1 - sa)
    terms = vonmangoldt_terms(2 * L + 1e-9)
    M = np.zeros((n, n), dtype=complex)
    for j in range(n):
        for k in range(n):
            FGb = Fb[j] * Fb_refl[k]
            FGa = Fa[j] * Fa_refl[k]
            arch = (np.trapz(FGb * Eb, t) + np.trapz(FGa * Ea, t)) / (2 * np.pi)
            prime = 0.0
            for (nn, lam) in terms:
                x0 = np.log(nn)
                prime += lam / np.sqrt(nn) * (G_pair(centres[j], centres[k], w, x0)
                                              + G_pair(centres[j], centres[k], w, -x0))
            M[j, k] = arch - prime
    return M, len(terms)

def gram_zero_side(centres, w, zs):
    """Σ over ALL nontrivial zeros ρ of F_j(ρ) conj F_k(1 - conj ρ). `zs` holds the zeros with
    γ > 0 only; the conjugate zero 1/2 - iγ contributes the complex conjugate of the γ-term
    (att537c diagnosis: omitting it halves the real part and keeps a spurious imaginary part)."""
    s = 0.5 + 1j * zs
    F = [F_on(c, w, s) for c in centres]
    n = len(centres)
    M = np.zeros((n, n), dtype=complex)
    for j in range(n):
        for k in range(n):
            term = np.sum(F[j] * np.conj(F[k]))      # F_j(ρ) conj F_k(ρ) on the line
            M[j, k] = term + np.conj(term)            # + the conjugate zero
    return M

if __name__ == "__main__":
    Ls = [0.30, 0.34, 0.5, 0.8, 1.2, 1.8, 2.5, 3.5]
    nb = 4
    N = 1000
    print("loading %d zeros ..." % N); sys.stdout.flush()
    zs = zeros(N)
    print("att537b: L, w, #primepowers(n<=e^{2L}), lam_min(prime), lam_max(prime), lam_min(zero side), relFrob")
    for L in Ls:
        w = L / nb
        centres = [-L + w + 2 * w * i for i in range(nb)]
        t0 = time.time()
        Mp, nt = gram_prime_side(centres, w, L)
        Mz = gram_zero_side(centres, w, zs)
        Hp = (Mp + Mp.conj().T) / 2; Hz = (Mz + Mz.conj().T) / 2
        ep = np.linalg.eigvalsh(Hp); ez = np.linalg.eigvalsh(Hz)
        rel = np.linalg.norm(Mp - Mz) / np.linalg.norm(Mz)
        print("L=%.2f w=%.3f n_pp=%2d  lam_min=%.4e lam_max=%.4e | zero-side lam_min=%.4e | relFrob=%.2e  (%.1fs)"
              % (L, w, nt, ep[0], ep[-1], ez[0], rel, time.time() - t0))
        sys.stdout.flush()
