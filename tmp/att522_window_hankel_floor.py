"""
att522 — Phase 2(b) probe: how marginal is the positivity of the window Hankel?

OBJECT (hp_pencil.tex def:moments, read at source):
    A(z)    = xi(1/2 + i z)            [real on the real z-axis]
    mu_k(W) = (1/2 pi i) oint_{dR_W} z^k A'(z)/A(z) dz
    H_n(W)  = (mu_{a+b})_{a,b=0}^{n-1}
Inertia (thm:inertia): inertia H_n = (r+q, q, n-r-2q); H_n >= 0 <=> q = 0.

DESIGN CORRECTION made before running: since
    mu_k = sum_i a_i x_i^k + sum_j b_j (z_j^k + conj z_j^k),
H_n = sum_i a_i v(x_i) v(x_i)^T has RANK <= m = r + 2q.  So lambda_min = 0
identically for n > m -- those are the inertia theorem's n-r-2q zero
eigenvalues, NOT ill-conditioning.  Meaningful regime is n <= r, and the
meaningful quantity is lambda_min / lambda_max there.

PRE-REGISTERED DECISION RULE (fixed before running):
  SUPPORTED : lambda_min/lambda_max has a floor bounded away from 0, uniformly
              in n up to 12 and across windows.
  WEAKENED  : lambda_min/lambda_max decays geometrically in n.
  REFUTED   : lambda_min < 0 beyond tolerance (all these windows have q = 0).
PREDICTION: WEAKENED.  H_n = V^T diag(a) V with V Vandermonde in real nodes;
Vandermonde conditioning on real nodes grows exponentially in n.

METHOD: moments from zero ordinates (mp.zetazero), equal to the contour
integrals by the argument principle; cross-validated against a direct contour
computation of mu_0, mu_1 on one window.  Nodes affinely mapped to [-1,1] and
H normalized by the zero count, so the ratio is scale-free.
"""
import sys
import mpmath as mp

DPS_ZEROS = 30
DPS_LIN = 60


def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def A(z):
    return xi(mp.mpf(1) / 2 + 1j * z)


def dlogA(z):
    return mp.diff(A, z) / A(z)


def mu_contour(k, a, b, Y, c, h):
    def f(z):
        return ((z - c) / h) ** k * dlogA(z)
    tot = mp.quad(lambda t: f(t - 1j * Y), [a, b])
    tot += mp.quad(lambda t: f(b + 1j * t) * 1j, [-Y, Y])
    tot -= mp.quad(lambda t: f(t + 1j * Y), [a, b])
    tot -= mp.quad(lambda t: f(a + 1j * t) * 1j, [-Y, Y])
    return tot / (2j * mp.pi)


def load_zeros(count):
    """Compute ordinates once, cache to disk."""
    import os
    path = "tmp/att522_zeros.txt"
    have = []
    if os.path.exists(path):
        with open(path) as fh:
            have = [line.strip() for line in fh if line.strip()]
    if len(have) < count:
        mp.mp.dps = DPS_ZEROS
        for n in range(len(have) + 1, count + 1):
            have.append(mp.nstr(mp.im(mp.zetazero(n)), 25))
            if n % 50 == 0:
                print("   ... zero %d" % n, flush=True)
        with open(path, "w") as fh:
            fh.write("\n".join(have) + "\n")
    mp.mp.dps = DPS_LIN
    return [mp.mpf(s) for s in have[:count]]


def spectrum(ZS, a, b, nmax):
    gs = [g for g in ZS if a < g < b]
    r = len(gs)
    if r == 0:
        return 0, []
    c = (mp.mpf(a) + b) / 2
    h = (mp.mpf(b) - a) / 2
    nodes = [(g - c) / h for g in gs]
    rows = []
    for n in range(1, min(nmax, r) + 1):
        H = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                H[i, j] = mp.fsum(w ** (i + j) for w in nodes) / r
        ev = mp.eigsy(H, eigvals_only=True)
        rows.append((n, min(ev), max(ev)))
    return r, rows


if __name__ == "__main__":
    print("### building zero cache", flush=True)
    ZS = load_zeros(520)
    print("    have %d ordinates, last = %s" % (len(ZS), mp.nstr(ZS[-1], 12)),
          flush=True)

    print("\n### CROSS-VALIDATION: contour vs zero-ordinate moments, W=(10,35)",
          flush=True)
    mp.mp.dps = 25
    a, b, Y = mp.mpf(10), mp.mpf(35), mp.mpf(2)
    c, h = (a + b) / 2, (b - a) / 2
    gs = [g for g in ZS if a < g < b]
    print("  zeros in W: %d ->" % len(gs), [mp.nstr(g, 9) for g in gs],
          flush=True)
    for k in (0, 1):
        mc = mp.re(mu_contour(k, a, b, Y, c, h))
        mz = mp.fsum(((g - c) / h) ** k for g in gs)
        print("  mu_%d  contour = %-14s  zeros = %-14s  |diff| = %s"
              % (k, mp.nstr(mc, 10), mp.nstr(mz, 10), mp.nstr(abs(mc - mz), 4)),
              flush=True)
    mp.mp.dps = DPS_LIN

    for (a, b) in [(10, 100), (10, 300), (100, 400), (300, 700)]:
        print("=" * 66, flush=True)
        r, rows = spectrum(ZS, a, b, 12)
        print("W = (%d,%d):  r = %d zeros in window" % (a, b, r), flush=True)
        print("   n   lambda_min          lambda_max        lmin/lmax     decay",
              flush=True)
        prev = None
        for n, lo, hi in rows:
            ratio = lo / hi
            fac = "" if prev is None else "  x%.4g" % float(ratio / prev)
            print("  %2d   %-18s  %-16s  %-12s%s"
                  % (n, mp.nstr(lo, 8), mp.nstr(hi, 8), mp.nstr(ratio, 6), fac),
                  flush=True)
            prev = ratio
