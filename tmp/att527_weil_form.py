"""
att527 — the Guinand-Weil explicit formula, implemented and VALIDATED, then the
Weil quadratic form's least eigenvalue as a function of support width L.

STEP 1 (validation, must pass before anything else means anything).
For even real g with h(r) = int g(u) e^{iru} du:

  sum_rho h(gamma)  =  ARCH + POLE - PRIME
  ARCH  = (1/2pi) int h(r) [ Re psi(1/4 + i r/2) - log pi ] dr
  POLE  = h(i/2) + h(-i/2) = 2 int g(u) cosh(u/2) du
  PRIME = 2 sum_{n>=2} Lambda(n) n^{-1/2} g(log n)

Test g(u) = exp(-u^2/(2 s^2)), h(r) = s sqrt(2pi) exp(-s^2 r^2/2).
With s = 0.5, h decays by |r| ~ 20 so the cached zero list suffices, and
g(log 2) = 0.38 so the primes contribute materially.  If the two sides do not
agree the normalization is wrong and everything after it is void.

STEP 2.  Weil form on band-limited tests.  For g supported in [-L,L],
W(g) = ARCH + POLE - PRIME is a quadratic form in g.  Discretize g on N nodes;
W(g) = c^T M c for an explicit symmetric M.  Weil: M(L) >= 0 for every L <=> RH.
Report lambda_min(M(L)) vs L.

PRE-REGISTERED:
  step 1 relative agreement  < 1e-6                  (else STOP, normalization wrong)
  step 2 lambda_min(M(L)) >= 0 for all tested L      (consistent with RH)
  and the informative quantity is HOW lambda_min behaves as L grows.
NO CLAIM is attached to step 2 in advance; it is a measurement.
"""
import mpmath as mp

mp.mp.dps = 25


def mangoldt_pairs(umax):
    """[(Lambda(n), log n)] for 2 <= n, log n <= umax."""
    nmax = int(mp.floor(mp.e ** umax)) + 1
    out = []
    for n in range(2, nmax + 1):
        m, p, k = n, None, 0
        x = n
        d = 2
        fac = {}
        while d * d <= x:
            while x % d == 0:
                fac[d] = fac.get(d, 0) + 1
                x //= d
            d += 1
        if x > 1:
            fac[x] = fac.get(x, 0) + 1
        if len(fac) == 1:
            p = list(fac)[0]
            out.append((mp.log(p), mp.log(n)))
    return out


def arch(h):
    f = lambda r: h(r) * (mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * r / 2)) - mp.log(mp.pi))
    return mp.quad(f, [-mp.inf, 0, mp.inf]) / (2 * mp.pi)


if __name__ == "__main__":
    s = mp.mpf('0.5')
    g = lambda u: mp.e ** (-u ** 2 / (2 * s ** 2))
    h = lambda r: s * mp.sqrt(2 * mp.pi) * mp.e ** (-s ** 2 * r ** 2 / 2)

    print("### STEP 1 — validation of the explicit formula (s = %s)" % s)
    ZS = [mp.mpf(x.strip()) for x in open('tmp/att522_zeros.txt') if x.strip()]
    zero_side = 2 * mp.fsum(h(gm) for gm in ZS)          # +-gamma
    A = arch(h)
    P = 2 * mp.quad(lambda u: g(u) * mp.cosh(u / 2), [-mp.inf, 0, mp.inf])
    pr = mangoldt_pairs(mp.mpf(12))
    PR = 2 * mp.fsum(L * mp.e ** (-ln / 2) * g(ln) for (L, ln) in pr)
    rhs = A + P - PR
    print("   zero side  sum_rho h(gamma) = %s   (%d ordinates)" % (mp.nstr(zero_side, 14), len(ZS)))
    print("   ARCH  = %s" % mp.nstr(A, 14))
    print("   POLE  = %s" % mp.nstr(P, 14))
    print("   PRIME = %s   (%d prime powers)" % (mp.nstr(PR, 14), len(pr)))
    print("   RHS   = %s" % mp.nstr(rhs, 14))
    rel = abs(zero_side - rhs) / abs(rhs)
    print("   relative agreement = %s   -> %s"
          % (mp.nstr(rel, 6), "PASS" if rel < mp.mpf('1e-6') else "FAIL"))

# ---------------- STEP 2: the Weil form as an explicit matrix ----------------
def weil_matrix(nodes, b, umax):
    N = len(nodes)
    pr = mangoldt_pairs(umax)
    sq = mp.sqrt(mp.pi)
    M = mp.matrix(N, N)
    for j in range(N):
        for k in range(N):
            d = nodes[j] - nodes[k]
            A = b**2 * mp.quad(lambda r: mp.e**(-b**2*r**2) * mp.cos(r*d) *
                    (mp.re(mp.digamma(mp.mpf(1)/4 + 1j*r/2)) - mp.log(mp.pi)),
                    [-mp.inf, 0, mp.inf])
            P = 4*mp.pi*b**2 * mp.e**(b**2/4) * mp.cosh(d/2)
            PR = 2*mp.fsum(L_*mp.e**(-ln/2) * b*sq*mp.e**(-(ln-d)**2/(4*b**2))
                           for (L_, ln) in pr)
            M[j, k] = A + P - PR
    return M

if True:
    b = mp.mpf('0.15')
    print("\n### STEP 2 — Weil form M(L), Gaussian bumps b = %s, N = 7 nodes" % b)
    print("   validation: c^T M c  vs  zero-side sum for a fixed c")
    ZS = [mp.mpf(x.strip()) for x in open('tmp/att522_zeros.txt') if x.strip()]
    for Lh in ('1.0', '2.0'):
        Lh = mp.mpf(Lh); nodes = [(-Lh + 2*Lh*i/6) for i in range(7)]
        M = weil_matrix(nodes, b, 2*Lh + 6*b)
        c = [mp.mpf(1)/(1+i) for i in range(7)]
        quad = mp.fsum(c[j]*c[k]*M[j, k] for j in range(7) for k in range(7))
        hfun = lambda r: 2*mp.pi*b**2*mp.e**(-b**2*r**2) * \
            abs(mp.fsum(c[j]*mp.e**(1j*r*nodes[j]) for j in range(7)))**2
        zs = 2*mp.fsum(hfun(gm) for gm in ZS)
        rel = abs(quad-zs)/abs(zs)
        ev = mp.eigsy(M, eigvals_only=True)
        print("   L=%-4s  cMc=%-14s zeros=%-14s rel=%-10s  lambda_min=%s"
              % (mp.nstr(2*Lh,3), mp.nstr(quad,10), mp.nstr(zs,10),
                 mp.nstr(rel,4), mp.nstr(min(ev),8)))
