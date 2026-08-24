"""
att523 — DC/AC decomposition of the window moments, WITH CONTROLS.

OBJECT (hp_pencil.tex def:moments):  mu_k(W) = sum_{rho in W} w_rho^k,
w_rho = (gamma_rho - c)/h the affine map of the window onto [-1,1].

DECOMPOSITION (house method: evaluate the common mode EXACTLY first).
Riemann-von Mangoldt:  N(T) = theta(T)/pi + 1 + S(T), so the zero-counting
measure is  rho(gamma) d gamma + dS  with the smooth density

    rho(gamma) = log(gamma / 2pi) / 2pi        [> 0 for gamma > 2pi]

  mu_k^DC = int w^k rho dgamma      -- Hankel of a MANIFESTLY POSITIVE kernel
  mu_k^AC = mu_k - mu_k^DC = int w^k dS

H^DC is positive definite for free (positive density on an interval).  The whole
question is whether the AC part can overturn it:  is ||H^AC|| < lambda_min(H^DC)?

CONTROLS (designed in from the start; att522's failure was having none).
Same DC density, generic fluctuation:
  (P) Poisson  -- r points drawn from rho by inverse-transform sampling
  (J) jittered equispaced -- quantile points + uniform jitter of one mean spacing
Zeros are far more rigid than Poisson (S = O(log T) vs sqrt(N)), so if the
decomposition carries arithmetic information the zeros must separate from these.

PRE-REGISTERED DECISION RULE (fixed before running):
  INFORMATIVE : zeros' ||H^AC||/lambda_min(H^DC) is substantially below the
                Poisson control's, and stays < 1 to larger n.
  NULL        : zeros track the controls.
  Record n* = largest n where the ratio is still < 1.
PREDICTION: INFORMATIVE on the rigidity comparison (zeros << Poisson), but
n* small (3-6), since lambda_min(H^DC) ~ 0.17^n while ||H^AC|| does not decay.

All matrices normalized by their own mu_0 so the comparison is scale-free.
"""
import random
import mpmath as mp

mp.mp.dps = 40

A, B = mp.mpf(300), mp.mpf(700)
C = (A + B) / 2
Hh = (B - A) / 2
NMAX = 12


def dens(g):
    return mp.log(g / (2 * mp.pi)) / (2 * mp.pi)


def w_of(g):
    return (g - C) / Hh


def hankel(mus, n):
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = mus[i + j]
        # normalized outside
    return M


def moments_from_nodes(nodes):
    r = len(nodes)
    return [mp.fsum(w ** k for w in nodes) / r for k in range(2 * NMAX)]


def moments_dc():
    mass = mp.quad(dens, [A, B])
    return [mp.quad(lambda g: w_of(g) ** k * dens(g), [A, B]) / mass
            for k in range(2 * NMAX)], mass


def spec(M):
    return mp.eigsy(M, eigvals_only=True)


def sample_poisson(r, rng):
    """inverse-transform sample of r points from dens on [A,B] via a grid CDF"""
    G = 4000
    xs = [A + (B - A) * mp.mpf(i) / G for i in range(G + 1)]
    cdf = [mp.mpf(0)]
    for i in range(G):
        cdf.append(cdf[-1] + dens((xs[i] + xs[i + 1]) / 2) * (xs[i + 1] - xs[i]))
    tot = cdf[-1]
    out = []
    for _ in range(r):
        u = mp.mpf(rng.random()) * tot
        lo, hi = 0, G
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if cdf[mid] < u:
                lo = mid
            else:
                hi = mid
        out.append(xs[lo])
    return sorted(out)


def sample_jitter(r, rng):
    G = 4000
    xs = [A + (B - A) * mp.mpf(i) / G for i in range(G + 1)]
    cdf = [mp.mpf(0)]
    for i in range(G):
        cdf.append(cdf[-1] + dens((xs[i] + xs[i + 1]) / 2) * (xs[i + 1] - xs[i]))
    tot = cdf[-1]
    out = []
    for j in range(r):
        u = tot * (mp.mpf(j) + mp.mpf(0.5) + mp.mpf(rng.uniform(-0.5, 0.5))) / r
        u = max(mp.mpf(0), min(tot, u))
        lo, hi = 0, G
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if cdf[mid] < u:
                lo = mid
            else:
                hi = mid
        out.append(xs[lo])
    return sorted(out)


if __name__ == "__main__":
    with open("tmp/att522_zeros.txt") as fh:
        ZS = [mp.mpf(s.strip()) for s in fh if s.strip()]
    gz = [g for g in ZS if A < g < B]
    r = len(gz)
    mus_dc, mass = moments_dc()
    print("window (%d,%d): r = %d actual zeros;  RvM predicted mass = %s"
          % (A, B, r, mp.nstr(mass, 8)), flush=True)

    mus_z = moments_from_nodes([w_of(g) for g in gz])

    rng = random.Random(20260824)
    reps = 5
    mus_p = [moments_from_nodes([w_of(g) for g in sample_poisson(r, rng)])
             for _ in range(reps)]
    mus_j = [moments_from_nodes([w_of(g) for g in sample_jitter(r, rng)])
             for _ in range(reps)]

    print("\n  n | lmin(H_DC)   ||H_AC|| zeros   ratio Z    ratio Poisson  ratio Jitter",
          flush=True)
    nstar = {"Z": 0, "P": 0, "J": 0}
    for n in range(1, NMAX + 1):
        Hdc = hankel(mus_dc, n)
        lmin = min(spec(Hdc))

        def acnorm(mus):
            D = mp.matrix(n, n)
            for i in range(n):
                for j in range(n):
                    D[i, j] = mus[i + j] - mus_dc[i + j]
            return max(abs(e) for e in spec(D))

        az = acnorm(mus_z)
        ap = mp.fsum(acnorm(m) for m in mus_p) / reps
        aj = mp.fsum(acnorm(m) for m in mus_j) / reps
        rz, rp, rj = az / lmin, ap / lmin, aj / lmin
        if rz < 1:
            nstar["Z"] = n
        if rp < 1:
            nstar["P"] = n
        if rj < 1:
            nstar["J"] = n
        print(" %2d | %-12s %-16s %-10s %-14s %s"
              % (n, mp.nstr(lmin, 6), mp.nstr(az, 6), mp.nstr(rz, 5),
                 mp.nstr(rp, 5), mp.nstr(rj, 5)), flush=True)

    print("\n  n* (largest n with ratio < 1):  zeros=%d  poisson=%d  jitter=%d"
          % (nstar["Z"], nstar["P"], nstar["J"]))
    print("  rigidity separation at n=6: zeros/poisson ratio-of-ratios printed above")
