"""Weighted TWO-CLOCK test: does pairing the archimedean clocks into EXACT Bessel-K (the two-clock
closed form) kill the FE error rate recorded by the grid convolution (sym_r_fe2.py)?

Pairwise Mellin convolution of two Gamma_C inverse-Mellins is exact:
   (2x^{mu_a}e^{-2pi x}) *_M (2x^{mu_b}e^{-2pi x}) = 8 x^{(mu_a+mu_b)/2} K_{mu_b-mu_a}(4 pi sqrt x).
So gamma(Sym^r) = prod Gamma_C(s+mu_i) => g = convolution of ceil(kappa/2) EXACT Bessel-K clocks
(+ one leftover single clock if kappa odd).  Sym^1: 1 clock (elementary).  Sym^3: ONE Bessel (fully
closed form, NO grid).  Sym^5: one Bessel *_M one clock (1 clean quad).  Test phi(1/t)=eps t phi(t).

Run:  python3 sym_r_fe_2clock.py
"""
import mpmath as mp
from math import comb

mp.mp.dps = 30
TWO_PI = 2 * mp.pi
HALF = mp.mpf(11) / 2


def tau_upto(M):
    N = M + 1
    coef = [0] * (N + 1); coef[0] = 1
    for n in range(1, N + 1):
        upd = [0] * (N + 1)
        for a in range(N + 1):
            if coef[a]:
                for j in range(0, min(24, N // n) + 1):
                    idx = a + n * j
                    if idx > N: break
                    upd[idx] += coef[a] * comb(24, j) * (-1) ** j
        coef = upd
    return [0] + [coef[n - 1] for n in range(1, M + 1)]


def primes_upto(M):
    s = [True] * (M + 1); s[0] = s[1] = False
    for i in range(2, int(M ** .5) + 1):
        if s[i]:
            for j in range(i * i, M + 1, i): s[j] = False
    return [i for i in range(2, M + 1) if s[i]]


def sym_r_lambda(r, M, tau):
    primes = primes_upto(M)
    theta = {}
    for p in primes:
        c = mp.mpf(tau[p]) / (2 * mp.power(p, HALF))
        theta[p] = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), c)))
    lam = [mp.mpf(0)] * (M + 1); lam[1] = mp.mpf(1)
    spf = [0] * (M + 1)
    for p in primes:
        for j in range(p, M + 1, p):
            if spf[j] == 0: spf[j] = p
    hc = {}
    def local_h(p, jm):
        th = theta[p]; P = [mp.mpf(0)]
        for k in range(1, jm + 1):
            sk = mp.sin(k * th)
            P.append(mp.sin((r + 1) * k * th) / sk if abs(sk) > mp.mpf(10) ** -20 else mp.mpf(r + 1))
        h = [mp.mpf(1)]
        for j in range(1, jm + 1):
            h.append(sum(P[i] * h[j - i] for i in range(1, j + 1)) / j)
        return h
    for n in range(2, M + 1):
        p = spf[n]; m, e = n, 0
        while m % p == 0: m //= p; e += 1
        pe = n // m
        if m > 1:
            lam[n] = lam[m] * lam[pe]
        else:
            if p not in hc:
                jm = 0; pk = p
                while pk <= M: jm += 1; pk *= p
                hc[p] = local_h(p, jm)
            lam[n] = hc[p][e]
    return lam


def one_clock(mu):
    return lambda x: 2 * mp.power(x, mu) * mp.e ** (-TWO_PI * x)


def two_clock(mu_a, mu_b):
    """EXACT Bessel-K for the pairwise Mellin convolution of two clocks."""
    a = (mu_a + mu_b) / 2
    nu = mu_b - mu_a
    return lambda x: 8 * mp.power(x, a) * mp.besselk(nu, 4 * mp.pi * mp.sqrt(x))


def mellin_convolve(f, h):
    """(f *_M h)(x) = int_0^inf f(x/u) h(u) du/u, by mpmath quad split at u=1."""
    def g(x):
        return mp.quad(lambda u: f(x / u) * h(u) / u, [0, 1, mp.inf])
    return g


def build_g(r):
    """g = convolution of Bessel-K two-clocks (+ leftover one-clock if kappa odd)."""
    kappa = (r + 1) // 2
    mus = [(2 * i - 1) * HALF for i in range(1, kappa + 1)]
    clocks = []
    i = 0
    while i + 1 < len(mus):
        clocks.append(two_clock(mus[i], mus[i + 1])); i += 2
    if i < len(mus):
        clocks.append(one_clock(mus[i]))
    g = clocks[0]
    for c in clocks[1:]:
        g = mellin_convolve(g, c)
    return g, mus, len(clocks)


def main():
    print("WEIGHTED TWO-CLOCK (exact Bessel-K) FE test — does it kill the grid error rate?")
    print("=" * 82)
    M = 160
    tau = tau_upto(M)
    for r in (1, 3, 5):
        g, mus, ncl = build_g(r)
        lam = sym_r_lambda(r, M, tau)

        def phi(t):
            tot = mp.mpf(0)
            for n in range(1, M + 1):
                gv = g(n * t)
                tot += lam[n] * gv
                if n > 5 and abs(gv) < mp.mpf(10) ** -34:
                    break
            return tot
        ratios = [phi(1 / t) / (t * phi(t)) for t in (mp.mpf('0.7'), mp.mpf('0.9'),
                                                       mp.mpf('1.1'), mp.mpf('1.35'))]
        rm = sum(ratios) / len(ratios)
        spread = max(abs(x - rm) for x in ratios)
        eps = 1 if mp.re(rm) > 0 else -1
        clk = "1 elem" if r == 1 else ("1 Bessel (closed form)" if r == 3 else f"{ncl} clocks (Bessel + conv)")
        print(f"Sym^{r} GL({r+1})  [{clk}]:  eps={eps:+d}  ||mean|-1|={float(abs(abs(rm)-1)):.2e}  "
              f"spread={float(spread):.2e}", flush=True)
    print()
    print("Compare grid (sym_r_fe2): Sym^1 2e-7, Sym^3 1e-8, Sym^5 6e-6.  If the Bessel two-clock")
    print("drops these to ~mpmath precision, the two-clock KILLS the error -> sweep beyond Sym^5.")


if __name__ == "__main__":
    main()
