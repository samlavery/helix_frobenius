"""
att523c — the decisive number: mu_min at n = r (the certification degree).

Certifying a window needs H_n >= 0 at n >= m = r (thm:inertia).  att523b measured
mu_min = lambda_min(H_DC^{-1} H) only to n = 12 on a window with r = 276, which
cannot see the approach to the rank wall at n = r+1.

KEY OBSERVATION driving this probe: if the r zeros in the window were exactly the
GAUSS QUADRATURE NODES of the DC density rho, they would reproduce every moment
through degree 2r-1, giving H_Z = H_DC for all n <= r, hence mu_min(n=r) = 1
EXACTLY.  Gauss nodes of a positive measure are automatically real and simple.
So mu_min(n=r) measures the deviation of the zeros from the Gauss nodes of their
own RvM density -- and that deviation is the whole arithmetic content.

CONTROLS: same r, same window: Poisson, jitter, and GAUSS (the exact Gauss nodes
of rho on the window, which must return mu_min = 1 and validates the pipeline).

PRE-REGISTERED DECISION RULE:
  BOUNDED  : mu_min(n=r) stays O(1) (say > 0.1) as r grows -> the zeros are a
             bounded perturbation of the Gauss nodes; a slack-carrying bound is
             viable and this is a real handle.
  DECAYING : mu_min(n=r) falls geometrically in r -> no slack at the required
             degree; only an exact identity can work.
PREDICTION: DECAYING.  (Recorded before running.  Note att523b already refuted
one prediction of mine in this direction, so this one is made with low confidence.)
"""
import random
import mpmath as mp

mp.mp.dps = 120


def dens_raw(g):
    return mp.log(g / (2 * mp.pi)) / (2 * mp.pi)


def build(a, b, nodes_gamma, NM):
    c = (a + b) / 2
    h = (b - a) / 2
    mass = mp.quad(dens_raw, [a, b])
    mus_dc = [mp.quad(lambda g: ((g - c) / h) ** k * dens_raw(g), [a, b]) / mass
              for k in range(2 * NM)]
    r = len(nodes_gamma)
    mus_z = [mp.fsum(((g - c) / h) ** k for g in nodes_gamma) / r
             for k in range(2 * NM)]
    return mus_dc, mus_z


def mat(mus, n):
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = mus[i + j]
    return M


def gen_min(mus_num, mus_dc, n):
    L = mp.cholesky(mat(mus_dc, n))
    Li = mp.inverse(L)
    M = Li * mat(mus_num, n) * Li.T
    return min(mp.eigsy((M + M.T) / 2, eigvals_only=True))


def gauss_nodes(a, b, r):
    """Gauss nodes of dens_raw on [a,b]: roots of the degree-r orthogonal poly,
    obtained from the Jacobi matrix built by Stieltjes/Chebyshev from moments."""
    c, h = (a + b) / 2, (b - a) / 2
    mass = mp.quad(dens_raw, [a, b])
    mu = [mp.quad(lambda g: ((g - c) / h) ** k * dens_raw(g), [a, b]) / mass
          for k in range(2 * r + 1)]
    # Stieltjes via Hankel determinants is unstable; use the moment-matrix
    # Cholesky to get the orthonormal polynomial recurrence.
    H = mat(mu, r + 1)
    L = mp.cholesky(H)          # H = L L^T
    Li = mp.inverse(L)
    # Jacobi matrix J from the orthonormal basis: J = Li * S * Li^T with
    # S the shifted moment matrix (mu_{i+j+1}).
    S = mp.matrix(r, r)
    for i in range(r):
        for j in range(r):
            S[i, j] = mu[i + j + 1]
    Lr = mp.cholesky(mat(mu, r))
    Lri = mp.inverse(Lr)
    J = Lri * S * Lri.T
    ev = mp.eigsy((J + J.T) / 2, eigvals_only=True)
    return [c + h * t for t in ev]


if __name__ == "__main__":
    with open("tmp/att522_zeros.txt") as fh:
        ZS = [mp.mpf(s.strip()) for s in fh if s.strip()]
    ZS = [g for g in ZS if g > 100]

    rng = random.Random(20260824)
    print("  r | mu_min ZEROS    mu_min GAUSS    mu_min POISSON  mu_min JITTER",
          flush=True)
    for r in (4, 6, 8, 10, 12, 14):
        i0 = 40
        sel = ZS[i0:i0 + r]
        a = (ZS[i0 - 1] + sel[0]) / 2
        b = (sel[-1] + ZS[i0 + r]) / 2
        mus_dc, mus_z = build(a, b, sel, r)
        mz = gen_min(mus_z, mus_dc, r)

        gn = gauss_nodes(a, b, r)
        _, mus_g = build(a, b, gn, r)
        mg = gen_min(mus_g, mus_dc, r)

        span = b - a
        pois, jit = [], []
        for _ in range(4):
            ps = sorted(a + span * mp.mpf(rng.random()) for _ in range(r))
            _, mp_ = build(a, b, ps, r)
            pois.append(gen_min(mp_, mus_dc, r))
            js = sorted(a + span * (mp.mpf(j) + mp.mpf(0.5)
                        + mp.mpf(rng.uniform(-0.5, 0.5))) / r for j in range(r))
            _, mj_ = build(a, b, js, r)
            jit.append(gen_min(mj_, mus_dc, r))
        print(" %2d | %-15s %-15s %-15s %-15s"
              % (r, mp.nstr(mz, 6), mp.nstr(mg, 6),
                 mp.nstr(mp.fsum(pois) / len(pois), 6),
                 mp.nstr(mp.fsum(jit) / len(jit), 6)), flush=True)
