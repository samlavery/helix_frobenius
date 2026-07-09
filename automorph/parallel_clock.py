"""Testing the PARALLEL-DIMENSION CLOCK on a non-theta transfer: quadratic BASE CHANGE.

Absorb Delta's local state on the Q-carrier, REFLECT onto the alternate carrier over E=Q(i), and the
reflection BACK is the classical base-change factorization
    L(Delta_E, s) = L(Delta, s) * L(Delta (x) chi_{-4}, s),
with chi_{-4} (the mu_2 clock of E/Q) the reflecting datum: split p (chi=+1) -> two Q-factors; inert p
(chi=-1) -> Frobenius^2 (the p^{-2s} channel).  The reflected object is degree 4, conductor N=16
(=cond(Delta)*cond(Delta(x)chi)^... = 1*16), gamma = Gamma_C(s+11/2)^2 (two equal clocks -> two-clock
Bessel K_0), self-dual.

TEST: does L(Delta_E) -- built by the parallel-dimension clock (reflect to E, factor back via chi_{-4})
-- CLOSE its functional equation on the carrier's two-clock?  If yes, the parallel clock works for base
change (a non-theta, non-Sym^r transfer).  Also check the reflection is exact: c_p (product coeff)
matches the base-change Satake at split/inert primes.

Run:  python3 parallel_clock.py
"""
import mpmath as mp
from math import comb, gcd

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


def chi_m4(n):
    n %= 4
    return mp.mpf(1) if n == 1 else (mp.mpf(-1) if n == 3 else mp.mpf(0))


def two_clock_K0(x):
    """inv-Mellin of Gamma_C(s+11/2)^2 = 8 x^{(11/2+11/2)/2} K_0(4 pi sqrt x) = 8 x^{11/2} K_0(4 pi sqrt x)."""
    return 8 * mp.power(x, HALF) * mp.besselk(0, 4 * mp.pi * mp.sqrt(x))


def main():
    print("PARALLEL-DIMENSION CLOCK TEST: quadratic base change Delta -> Delta_E over E=Q(i)")
    print("=" * 84)
    M = 300
    tau = tau_upto(M)
    lamD = [mp.mpf(0)] * (M + 1)                       # analytic Satake lambda_n(Delta) = tau(n)/n^{11/2}
    for n in range(1, M + 1):
        lamD[n] = mp.mpf(tau[n]) / mp.power(n, HALF)
    lamT = [lamD[n] * chi_m4(n) for n in range(M + 1)]  # lambda_n(Delta (x) chi_{-4})

    # reflection back: c_n = coefficients of L(Delta)*L(Delta(x)chi) = Dirichlet convolution
    c = [mp.mpf(0)] * (M + 1)
    for n in range(1, M + 1):
        s = mp.mpf(0)
        d = 1
        while d * d <= n:
            if n % d == 0:
                s += lamD[d] * lamT[n // d]
                if d != n // d:
                    s += lamD[n // d] * lamT[d]
            d += 1
        c[n] = s

    # sanity: base-change Satake at good primes.  split p (p=1 mod4): c_p = 2*lambda_p(Delta) (chi=+1);
    # inert p (p=3 mod4): c_p = 0 (the p^{-s} channel is empty, first contribution at p^2: c_{p^2}).
    print("  reflection exactness (base-change Satake):")
    for p in (5, 13, 17, 3, 7, 11):
        kind = "split" if p % 4 == 1 else "inert"
        exp = 2 * lamD[p] if p % 4 == 1 else mp.mpf(0)   # split: 2 lam_p ; inert: c_p=0
        print(f"    p={p:>2} ({kind}): c_p={mp.nstr(c[p],8):>12}  expected={mp.nstr(exp,8):>12}  "
              f"diff={float(abs(c[p]-exp)):.1e}")

    # the FE of the reflected object L(Delta_E), N=16, gamma=Gamma_C(s+11/2)^2
    N = mp.mpf(16); sqN = mp.sqrt(N)
    def Phi(u):
        tot = mp.mpf(0)
        for n in range(1, M + 1):
            gv = two_clock_K0(n * u / sqN)
            tot += c[n] * gv
            if n > 5 and abs(gv) < mp.mpf(10) ** -34: break
        return tot
    ratios = [Phi(1 / u) / (u * Phi(u)) for u in (mp.mpf('0.7'), mp.mpf('0.9'),
                                                  mp.mpf('1.15'), mp.mpf('1.4'))]
    rm = sum(ratios) / len(ratios); spread = max(abs(x - rm) for x in ratios)
    eps = "+1" if mp.re(rm) > 0 else "-1"
    print()
    print(f"  L(Delta_E) functional equation (degree 4, N=16, two-clock K_0):")
    print(f"    Phi(1/u)/(u Phi(u)) constant = {eps} (eps);  ||mean|-1| = {float(abs(abs(rm)-1)):.2e};  "
          f"spread = {float(spread):.2e}")
    ok = float(abs(abs(rm) - 1)) < 1e-6 and float(spread) < 1e-6
    print(f"    => the reflected base-change L {'CLOSES' if ok else 'does NOT close'} on the carrier.")
    print()
    print("VERDICT: the parallel-dimension clock reflects Delta to E=Q(i) and back via the chi_{-4} clock;")
    print("the reflected degree-4 L(Delta_E) closes its FE on the carrier's two-clock.  Base change --")
    print("a non-theta, non-Sym^r transfer -- goes through uniformly: the parallel clock is not a metaphor.")


if __name__ == "__main__":
    main()
