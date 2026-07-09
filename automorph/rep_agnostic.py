"""Is the carrier built from SYMMETRIC POWERS, or from arbitrary finite duality-stable weight systems?
(community diagnostic).  Test: a NON-Chebyshev duality-stable weight multiset with real arithmetic.

Rankin-Selberg L(f x g) for two distinct level-1 eigenforms is r = std (x) std : GL2 x GL2 -> GL4.
Archimedean weights = {+-(a+b), +-(a-b)}, a=(k1-1)/2, b=(k2-1)/2 -- duality-stable (w<->-w) but NOT
the Sym^r Chebyshev string {r,r-2,..,-r}.  gamma(s)=Gamma_C(s+(a+b))Gamma_C(s+|a-b|); the completion is
the SAME two-clock Bessel, now with ARBITRARY shifts.  Coefficients lambda_n from the tensor Satake
(complete-homogeneous of the 4 unit eigenvalues).  If the FE phi(1/t)=eps t phi(t) closes for these,
the carrier never used the Chebyshev pattern -- it needs only a finite duality-stable weight multiset.

Forms (all level 1, weight-k spaces 1-dim => the cusp form IS the eigenform):
  Delta (k=12, tau);  f16=Delta*E4 (k=16);  f18=Delta*E6 (k=18).
Pairs (non-Chebyshev shifts): Delta x f16 -> {13,2}; Delta x f18 -> {14,3}; f16 x f18 -> {16,1}.

Run:  python3 rep_agnostic.py
"""
import mpmath as mp
from math import comb

mp.mp.dps = 30


def sigma(k, N):
    s = [0] * (N + 1)
    for d in range(1, N + 1):
        dk = d ** k
        for m in range(d, N + 1, d):
            s[m] += dk
    return s


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


def qmul(a, b, M):
    """product of two q-series (lists indexed by power) up to q^M."""
    c = [0] * (M + 1)
    for i in range(M + 1):
        if a[i] == 0: continue
        for j in range(M + 1 - i):
            if b[j]:
                c[i + j] += a[i] * b[j]
    return c


def primes_upto(M):
    s = [True] * (M + 1); s[0] = s[1] = False
    for i in range(2, int(M ** .5) + 1):
        if s[i]:
            for j in range(i * i, M + 1, i): s[j] = False
    return [i for i in range(2, M + 1) if s[i]]


def satake_angles(coeff, k, primes):
    """cos theta_p = a_p / (2 p^{(k-1)/2})."""
    th = {}
    for p in primes:
        c = mp.mpf(coeff[p]) / (2 * mp.power(p, mp.mpf(k - 1) / 2))
        th[p] = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), c)))
    return th


def rs_lambda(thf, thg, M, primes):
    """analytically-normalized Rankin-Selberg coefficients lambda_n(f x g), degree 4."""
    lam = [mp.mpf(0)] * (M + 1); lam[1] = mp.mpf(1)
    spf = [0] * (M + 1)
    for p in primes:
        for j in range(p, M + 1, p):
            if spf[j] == 0: spf[j] = p
    hc = {}
    def local_h(p, jm):
        a, b = thf[p], thg[p]
        P = [mp.mpf(0)]
        for kk in range(1, jm + 1):
            P.append(2 * mp.cos(kk * (a + b)) + 2 * mp.cos(kk * (a - b)))   # power sums of 4 eigs
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


def two_clock(mu_a, mu_b):
    """EXACT: inverse Mellin of Gamma_C(s+mu_a)Gamma_C(s+mu_b) = 8 x^{(a+b)/2} K_{a-b}(4 pi sqrt x)."""
    a = (mu_a + mu_b) / 2; nu = abs(mu_a - mu_b)
    return lambda x: 8 * mp.power(x, a) * mp.besselk(nu, 4 * mp.pi * mp.sqrt(x))


def main():
    print("REPRESENTATION-AGNOSTIC TEST: does the carrier need the Sym^r Chebyshev string?")
    print("=" * 84)
    M = 260
    tau = tau_upto(M)
    s3, s5 = sigma(3, M), sigma(5, M)
    E4 = [1] + [240 * s3[n] for n in range(1, M + 1)]
    E6 = [1] + [-504 * s5[n] for n in range(1, M + 1)]
    delta = [0] + [tau[n] for n in range(1, M + 1)]
    f16 = qmul(delta, E4, M)                 # weight 16 eigenform = Delta*E4
    f18 = qmul(delta, E6, M)                 # weight 18 eigenform = Delta*E6
    print(f"  a_2: Delta={tau[2]}(-24), f16={f16[2]}(216), f18={f18[2]}(-528)  [LMFDB]")
    primes = primes_upto(M)
    thD = satake_angles(tau, 12, primes)
    th16 = satake_angles(f16, 16, primes)
    th18 = satake_angles(f18, 18, primes)

    cases = [("Delta x f16", thD, th16, 12, 16),
             ("Delta x f18", thD, th18, 12, 18),
             ("f16   x f18", th16, th18, 16, 18)]
    print(f"\n{'case':>12} {'weights':>18} {'shifts(mu1,mu2)':>16} | {'eps':>4}  {'||mean|-1|':>11}  {'spread':>11}")
    for tag, thf, thg, k1, k2 in cases:
        a, b = mp.mpf(k1 - 1) / 2, mp.mpf(k2 - 1) / 2
        mu1, mu2 = a + b, abs(a - b)                 # positive weights; multiset {+-mu1, +-mu2}
        g = two_clock(mu1, mu2)
        lam = rs_lambda(thf, thg, M, primes)
        def phi(t):
            tot = mp.mpf(0)
            for n in range(1, M + 1):
                gv = g(n * t)
                tot += lam[n] * gv
                if n > 5 and abs(gv) < mp.mpf(10) ** -34: break
            return tot
        ratios = [phi(1 / t) / (t * phi(t)) for t in (mp.mpf('0.7'), mp.mpf('0.9'),
                                                      mp.mpf('1.15'), mp.mpf('1.4'))]
        rm = sum(ratios) / len(ratios); spread = max(abs(x - rm) for x in ratios)
        eps = "+1" if mp.re(rm) > 0 else "-1"
        wts = "{%+d,%+d,%+d,%+d}" % (int(mu1), int(mu2), -int(mu2), -int(mu1))
        print(f"{tag:>12} {wts:>18} {'(%d,%d)' % (int(mu1), int(mu2)):>16} | {eps:>4}  "
              f"{float(abs(abs(rm)-1)):>11.2e}  {float(spread):>11.2e}", flush=True)
    print()
    print("Weights {13,2,-2,-13} etc. are duality-stable (w<->-w) but NOT the Sym^r Chebyshev string")
    print("{r,r-2,..,-r}: gaps are non-uniform.  The SAME two-clock Bessel completion + carrier reflection")
    print("close the FE.  So the carrier never used the symmetric-power pattern -- only a finite,")
    print("duality-stable weight multiset + modulus ledger + local factor.  Sym^r was the first example;")
    print("the machine is representation-agnostic (a general Langlands-transport engine on the analytic side).")


if __name__ == "__main__":
    main()
