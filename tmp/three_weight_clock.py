"""Three-weight uniformity clock, or a second two-weight clock?  They are the SAME object.

The degree-2n completion is n Gamma_C-clocks Mellin-convolved.  The two-clock (Bessel K) pairs two
exactly.  For THREE weights {mu1,mu2,mu3}:
  (a) three-weight clock  = the 3-fold convolution = MeijerG G^{3,0}_{0,3} (one object);
  (b) second two-weight clock = (Bessel two-clock of mu1,mu2)  *_M  (single clock mu3).
Claim: (b) = (a), EXACT -- so building a three-weight clock IS composing two-weight clocks, and its
Mellin is Gamma_C(s+mu1)Gamma_C(s+mu2)Gamma_C(s+mu3).  Verify on ARBITRARY (non-Chebyshev) shifts.

Uniformity is additive: the multi-clock trace bound clockTraceN <= n is the SUM of the two-clock
bounds (each conjugate pair <= its own), so uniformity also composes from the two-clock unit -- no new
fundamental object is needed, only a second copy.

Run:  python3 three_weight_clock.py
"""
import mpmath as mp

mp.mp.dps = 25
TWO_PI = 2 * mp.pi


def clock(mu):
    """inverse Mellin of Gamma_C(s+mu) = 2 x^mu e^{-2 pi x}."""
    return lambda x: 2 * mp.power(x, mu) * mp.e ** (-TWO_PI * x)


def two_clock(mu_a, mu_b):
    """EXACT: inverse Mellin of Gamma_C(s+mu_a)Gamma_C(s+mu_b) = 8 x^{(a+b)/2} K_{a-b}(4 pi sqrt x)."""
    a = (mu_a + mu_b) / 2
    nu = mu_a - mu_b
    return lambda x: 8 * mp.power(x, a) * mp.besselk(nu, 4 * mp.pi * mp.sqrt(x))


def mellin_convolve(f, h):
    """(f *_M h)(x) = int_0^inf f(x/u) h(u) du/u."""
    return lambda x: mp.quad(lambda u: f(x / u) * h(u) / u, [0, x, mp.inf])


def gammaC(s, mu):
    return 2 * mp.power(TWO_PI, -(s + mu)) * mp.gamma(s + mu)


def main():
    print("THREE-WEIGHT CLOCK = SECOND TWO-WEIGHT CLOCK COMPOSED (exact)")
    print("=" * 74)
    for mus in [(mp.mpf(2), mp.mpf(5), mp.mpf(9)),          # arbitrary non-Chebyshev
                (mp.mpf('5.5'), mp.mpf('16.5'), mp.mpf('27.5'))]:   # = Sym^5 shifts, for reference
        m1, m2, m3 = mus
        # (b) second two-weight clock: Bessel(m1,m2) *_M clock(m3)
        g = mellin_convolve(two_clock(m1, m2), clock(m3))
        # gate: Mellin of the composed clock must be Gamma_C(s+m1)Gamma_C(s+m2)Gamma_C(s+m3)
        worst = mp.mpf(0)
        for s in (mp.mpf('2'), mp.mpf('3'), mp.mpf('4')):
            lhs = mp.quad(lambda x: g(x) * mp.power(x, s - 1), [0, mp.inf])
            rhs = gammaC(s, m1) * gammaC(s, m2) * gammaC(s, m3)
            worst = max(worst, abs(lhs / rhs - 1))
        tag = "Sym^5 shifts" if m1 == mp.mpf('5.5') else "arbitrary"
        print(f"  shifts ({float(m1)},{float(m2)},{float(m3)})  [{tag}]:  "
              f"Mellin(Bessel(m1,m2) *_M clock(m3)) = Gamma_C^3 to  {float(worst):.2e}")
    print()
    print("So the three-weight clock is the two-clock Bessel composed with one more clock -- exact.")
    print("Any degree-2n completion is n clocks paired into two-clock Bessels (+ one leftover if n odd);")
    print("the uniformity bound clockTraceN <= n is the sum of the two-clock bounds.  You never need a")
    print("NEW fundamental clock -- a SECOND two-weight clock (and the trace additivity) handle any")
    print("finite duality-stable weight system.  The two-clock is the unit; everything composes from it.")


if __name__ == "__main__":
    main()
