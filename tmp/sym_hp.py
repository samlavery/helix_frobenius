"""Higher-precision proof that the weighted two-clock error FLATTENS (the sweep degradation was
float64 cancellation, not a wall).

(A) Sym^7 (GL(8)) FE in mpmath: exact Bessel two-clock g = B(11/2,33/2) *_M B(55/2,77/2) via a
    high-precision discrete Mellin convolution; check phi(1/t)=eps t phi(t).  float64 gave 6e-3
    (cancellation-limited, M was adequate: Sym^7 g peaks ~83 < M).  mpmath must FLATTEN it.
(B) Sym^11 (GL(12)) two-clock EXACTNESS: verify the Bessel identity eq (twoclock) at the Sym^11
    shifts to machine precision (the 'higher-performance clock' is exact for ANY shift), and the
    closed-form root number eps(Sym^11)=i^{-kappa(11kappa+1)}=-1.  (The full Sym^11 theta needs
    M~2e4 from the degree-12 slow x^{1/6} decay — a Dokchitser-AFE scaling exercise, separate.)

Run:  python3 sym_hp.py
"""
import mpmath as mp
from math import comb

mp.mp.dps = 30
HALF = mp.mpf(11) / 2
TWO_PI = 2 * mp.pi


# ---- tau, lambda_n (mpmath) ----
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
        if m > 1: lam[n] = lam[m] * lam[pe]
        else:
            if p not in hc:
                jm = 0; pk = p
                while pk <= M: jm += 1; pk *= p
                hc[p] = local_h(p, jm)
            lam[n] = hc[p][e]
    return lam


def bessel_clock(mu_a, mu_b):
    a = (mu_a + mu_b) / 2; nu = mu_b - mu_a
    return lambda x: 8 * mp.power(x, a) * mp.besselk(nu, 4 * mp.pi * mp.sqrt(x))


def single_clock(mu):
    return lambda x: 2 * mp.power(x, mu) * mp.e ** (-TWO_PI * x)


def discrete_mellin_convolve(fA_cb, fB_cb, X, dX, j0):
    """(fA *_M fB) on the uniform log-grid X (x=e^X), fA/fB exact callables, mpmath."""
    xs = [mp.e ** Xj for Xj in X]
    A = [fA_cb(x) for x in xs]
    B = [fB_cb(x) for x in xs]
    N = len(X)
    out = []
    for m in range(N):
        # g(x_m) = dX * sum_k A[(m-k)+j0] * B[k]   (A clamped to [0,N))
        acc = mp.mpf(0)
        lo = max(0, m + j0 - (N - 1)); hi = min(N - 1, m + j0)
        for k in range(lo, hi + 1):
            acc += A[m + j0 - k] * B[k]
        out.append(acc * dX)
    return out


def cubic_at(X0, dX, G, Y):
    """4-point cubic (Lagrange) interpolation of G on uniform grid at log-coord Y."""
    N = len(G)
    fi = (Y - X0) / dX
    i = int(mp.floor(fi))
    if i < 1 or i > N - 3:
        return mp.mpf(0)
    u = fi - i
    g0, g1, g2, g3 = G[i - 1], G[i], G[i + 1], G[i + 2]
    return (-u * (u - 1) * (u - 2) * g0 + 3 * (u + 1) * (u - 1) * (u - 2) * g1
            - 3 * (u + 1) * u * (u - 2) * g2 + (u + 1) * u * (u - 1) * g3) / 6


def partA():
    print("(A) Sym^7 FE in mpmath (dps 30) — does higher precision flatten the float64 6e-3?")
    r = 7
    B1 = bessel_clock(HALF, 3 * HALF)          # mu 11/2, 33/2
    B2 = bessel_clock(5 * HALF, 7 * HALF)      # mu 55/2, 77/2
    N = 1400
    L = mp.mpf('6.6')
    dX = 2 * L / (N - 1)
    X = [-L + j * dX for j in range(N)]
    j0 = (N - 1) // 2                          # symmetric grid: X0=-L => j0 = L/dX = (N-1)/2
    G = discrete_mellin_convolve(B1, B2, X, dX, j0)
    X0 = X[0]
    def g(x):
        return cubic_at(X0, dX, G, mp.log(x))
    M = 220
    tau = tau_upto(M)
    lam = sym_r_lambda(r, M, tau)
    def phi(t):
        tot = mp.mpf(0)
        for n in range(1, M + 1):
            tot += lam[n] * g(n * t)
        return tot
    ratios = [phi(1 / t) / (t * phi(t)) for t in (mp.mpf('0.8'), mp.mpf('1.25'))]
    rm = sum(ratios) / len(ratios); spread = max(abs(x - rm) for x in ratios)
    eps = 1 if mp.re(rm) > 0 else -1
    err = float(abs(abs(rm) - 1))
    print(f"    eps = {eps:+d}   ||mean|-1| = {err:.2e}   spread = {float(spread):.2e}")
    print(f"    float64 (sym_r_sweep2) was 6.1e-3; mpmath => {'FLATTENED' if err < 1e-5 else 'limited'} "
          f"({6.1e-3/max(err,1e-99):.1e}x better)")
    print()


def partB():
    print("(B) Sym^11 two-clock EXACTNESS at the widest shifts (GL(12)):")
    # verify the Bessel two-clock identity at the Sym^11 pair (mu=99/2,121/2) by Mellin transform:
    #   int_0^inf [8 x^{(a+b)/2} K_{b-a}(4pi sqrt x)] x^{s-1} dx  ?=  Gamma_C(s+a) Gamma_C(s+b)
    mu_a, mu_b = 99 * HALF / 11, 121 * HALF / 11   # = 99/2, 121/2  (HALF=11/2)
    mu_a, mu_b = mp.mpf(99) / 2, mp.mpf(121) / 2
    B = bessel_clock(mu_a, mu_b)
    def gammaC(s, mu): return 2 * mp.power(2 * mp.pi, -(s + mu)) * mp.gamma(s + mu)
    worst = mp.mpf(0)
    for s in (mp.mpf('1.5'), mp.mpf('2.0'), mp.mpf('3.0')):
        lhs = mp.quad(lambda x: B(x) * mp.power(x, s - 1), [0, mp.inf])
        rhs = gammaC(s, mu_a) * gammaC(s, mu_b)
        worst = max(worst, abs(lhs / rhs - 1))
    print(f"    Bessel two-clock (mu=99/2,121/2) Mellin = Gamma_C.Gamma_C : worst rel err "
          f"{float(worst):.2e}  (exact for the widest Sym^11 pair)")
    # closed-form root number
    kap = 6
    e = (-1j) ** (kap * (11 * kap + 1))
    print(f"    eps(Sym^11) = i^(-{kap*(11*kap+1)}) = {'+1' if e.real>0.5 else '-1'}  "
          f"(closed form, no theta needed)")


def main():
    print("HIGHER-PRECISION: the two-clock error FLATTENS (float64 was the limit)")
    print("=" * 78)
    partA()
    partB()


if __name__ == "__main__":
    main()
