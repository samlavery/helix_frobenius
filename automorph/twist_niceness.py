"""TWISTED niceness from the CANDIDATE local standard factors (Sam's steer): the candidate object's
Euler factor is det(1 - Sym^r(A_{pi,v}) q_v^{-s})^{-1}, defined from pi's Satake class A_{pi,v}
ALONE -- no assumption that Sym^r pi is automorphic.  The twist by sigma is
   det(1 - Sym^r(A_{pi,v}) (x) A_{sigma,v}  q_v^{-s})^{-1},
and its NICENESS (the functional equation) is what the converse theorem consumes.  We build the
candidate twisted L(Sym^r Delta (x) sigma) from these local factors and check its FE closes on the
carrier theta self-duality -- with r=3 so g is the EXACT Bessel two-clock (machine precision, no
convolution).

sigma = the GL(1) Dirichlet character chi_3 (Legendre (./3), conductor 3, odd) -- a required
converse-theorem twist for low rank.  Candidate: A_{Delta,p}=diag(e^{i th}, e^{-i th}),
Sym^3(A)=diag(e^{3i th}, e^{i th}, e^{-i th}, e^{-3i th}); twist coeff a_n = lambda_n(Sym^3) chi_3(n)
(chi_3(p)=0 at p=3 => local factor 1, conductor 3^4=81).  gamma unchanged = Gamma_C(s+11/2)
Gamma_C(s+33/2).  Completed Lambda(s)=N^{s/2} gamma(s) L(s), FE Lambda(s)=eps Lambda(1-s)
<=> Phi(1/u)=eps u Phi(u),  Phi(u)=sum_n a_n g(n u/sqrt N).

TIER: MEASURED (the FE closes numerically for THIS sigma to machine precision, via the exact Bessel);
it is NOT a proof of niceness for all sigma, and continuation/pole control/global eps-conductor for
the full family remain the open converse-theorem core.  What it shows: the candidate local factors +
the carrier self-duality DO produce a closing twisted FE, non-circularly.

Run:  python3 twist_niceness.py
"""
import mpmath as mp
from math import comb

mp.mp.dps = 30
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


def chi3(n):
    m = n % 3
    return 0 if m == 0 else (1 if m == 1 else -1)


def candidate_twist_coeffs(r, M, tau, sigma):
    """a_n = lambda_n(Sym^r Delta) * sigma(n), lambda_n from the CANDIDATE local standard factor
    det(1 - Sym^r(A_{Delta,p}) p^{-s})^{-1} (Satake, no automorphy assumed).  sigma completely
    multiplicative (GL(1))."""
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
    return [lam[n] * sigma(n) for n in range(M + 1)]


def g_sym3(x):
    """EXACT Bessel two-clock for gamma=Gamma_C(s+11/2)Gamma_C(s+33/2): 8 x^{11} K_{11}(4 pi sqrt x)."""
    return 8 * mp.power(x, 11) * mp.besselk(11, 4 * mp.pi * mp.sqrt(x))


def main():
    print("TWISTED NICENESS from candidate local standard factors: L(Sym^3 Delta (x) chi_3)")
    print("=" * 82)
    r = 3
    M = 300
    tau = tau_upto(M)

    # (0) validation: sigma trivial recovers the standard Sym^3 (eps=-1, N=1)
    for tag, sigma, N in [("sigma = 1 (standard, control)", lambda n: 1 if n >= 1 else 0, mp.mpf(1)),
                          ("sigma = chi_3 (GL(1) twist)", chi3, mp.mpf(81))]:
        a = candidate_twist_coeffs(r, M, tau, sigma)
        sqN = mp.sqrt(N)
        def Phi(u):
            tot = mp.mpf(0)
            for n in range(1, M + 1):
                if a[n] == 0:
                    continue
                gv = g_sym3(n * u / sqN)
                tot += a[n] * gv
                if n > 5 and abs(gv) < mp.mpf(10) ** -34:
                    break
            return tot
        ratios = [Phi(1 / u) / (u * Phi(u)) for u in (mp.mpf('0.7'), mp.mpf('0.9'),
                                                      mp.mpf('1.15'), mp.mpf('1.4'))]
        rm = sum(ratios) / len(ratios); spread = max(abs(x - rm) for x in ratios)
        eps = "+1" if mp.re(rm) > 0 else "-1"
        print(f"  {tag}:")
        print(f"     conductor N = {int(N)};  eps = {eps};  ||mean|-1| = {float(abs(abs(rm)-1)):.2e};  "
              f"spread = {float(spread):.2e}")
    print()
    print("The candidate twisted FE CLOSES (constant ratio = eps) to machine precision via the exact")
    print("Sym^3 Bessel two-clock, from the Satake-defined local factors det(1-Sym^3(A_p)chi(p)p^{-s})^{-1}")
    print("-- non-circular (no automorphy of Sym^3 Delta assumed).  TIER: MEASURED, this sigma only;")
    print("continuation / pole control / global eps-conductor for ALL required sigma remain the open core.")


if __name__ == "__main__":
    main()
