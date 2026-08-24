"""
att523b — the route-around: measure the DC/AC split in the BASIS-INVARIANT form.

att523 measured ||H_AC|| / lambda_min(H_DC) in the MONOMIAL basis and found the
perturbation wins from n=5.  But lambda_min(H_DC) ~ 0.17^n is an artifact of the
monomial basis; positivity is basis-independent.  In the DC measure's own
orthogonal-polynomial basis H_DC is the identity.

The basis-invariant quantity is the generalized eigenvalue
    mu_min(n) := lambda_min( H_DC^{-1} H_Z )  =  1 + lambda_min(whitened AC).
H_Z >= 0 holds automatically for real nodes, so mu_min >= 0 always; the QUESTION
is HOW MUCH ROOM there is.  mu_min bounded away from 0 => a bound on the S
fluctuation carrying slack could close the window.  mu_min -> 0 => no slack, and
only an exact identity can work.

CONTROLS retained: Poisson and jittered-equispaced with the same DC density.

PRE-REGISTERED DECISION RULE (fixed before running):
  ROOM    : mu_min for the zeros stays above ~1e-2 through n = 12, and above the
            Poisson control -> slack-carrying bounds are viable; pursue.
  NO ROOM : mu_min decays geometrically toward 0 -> no slack exists at any n
            beyond a handful, and only an exact identity can close.
PREDICTION: NO ROOM, decaying geometrically, with the zeros between Poisson and
jitter as in att523.
"""
import random
import mpmath as mp

mp.mp.dps = 90

A, B = mp.mpf(300), mp.mpf(700)
C = (A + B) / 2
Hh = (B - A) / 2
NMAX = 12


def dens(g):
    return mp.log(g / (2 * mp.pi)) / (2 * mp.pi)


def w_of(g):
    return (g - C) / Hh


def moments_nodes(nodes):
    r = len(nodes)
    return [mp.fsum(w ** k for w in nodes) / r for k in range(2 * NMAX)]


def moments_dc():
    mass = mp.quad(dens, [A, B])
    return [mp.quad(lambda g: w_of(g) ** k * dens(g), [A, B]) / mass
            for k in range(2 * NMAX)]


def mat(mus, n):
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = mus[i + j]
    return M


def gen_min(mus_num, mus_dc, n):
    """lambda_min(H_DC^{-1} H_num) via Cholesky whitening."""
    D = mat(mus_dc, n)
    N = mat(mus_num, n)
    L = mp.cholesky(D)
    Li = mp.inverse(L)
    M = Li * N * Li.T
    M = (M + M.T) / 2
    return min(mp.eigsy(M, eigvals_only=True))


def grid_cdf():
    G = 4000
    xs = [A + (B - A) * mp.mpf(i) / G for i in range(G + 1)]
    cdf = [mp.mpf(0)]
    for i in range(G):
        cdf.append(cdf[-1] + dens((xs[i] + xs[i + 1]) / 2) * (xs[i + 1] - xs[i]))
    return xs, cdf, cdf[-1]


def draw(u, xs, cdf):
    lo, hi = 0, len(xs) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if cdf[mid] < u:
            lo = mid
        else:
            hi = mid
    return xs[lo]


if __name__ == "__main__":
    with open("tmp/att522_zeros.txt") as fh:
        ZS = [mp.mpf(s.strip()) for s in fh if s.strip()]
    gz = [g for g in ZS if A < g < B]
    r = len(gz)
    mus_dc = moments_dc()
    mus_z = moments_nodes([w_of(g) for g in gz])

    xs, cdf, tot = grid_cdf()
    rng = random.Random(20260824)
    reps = 5
    mus_p = [moments_nodes([w_of(draw(mp.mpf(rng.random()) * tot, xs, cdf))
                            for _ in range(r)]) for _ in range(reps)]
    mus_j = [moments_nodes(
        [w_of(draw(tot * min(mp.mpf(1), max(mp.mpf(0),
              (mp.mpf(j) + mp.mpf(0.5) + mp.mpf(rng.uniform(-0.5, 0.5))) / r)),
              xs, cdf)) for j in range(r)]) for _ in range(reps)]

    print("window (%d,%d), r = %d;  mu_min = lambda_min(H_DC^-1 H)  [>=0 always]"
          % (A, B, r), flush=True)
    print("\n  n | mu_min zeros     mu_min poisson   mu_min jitter    Z decay",
          flush=True)
    prev = None
    for n in range(1, NMAX + 1):
        mz = gen_min(mus_z, mus_dc, n)
        mpo = mp.fsum(gen_min(m, mus_dc, n) for m in mus_p) / reps
        mj = mp.fsum(gen_min(m, mus_dc, n) for m in mus_j) / reps
        dec = "" if prev is None else "  x%.4g" % float(mz / prev)
        print(" %2d | %-16s %-16s %-16s%s"
              % (n, mp.nstr(mz, 6), mp.nstr(mpo, 6), mp.nstr(mj, 6), dec),
              flush=True)
        prev = mz
