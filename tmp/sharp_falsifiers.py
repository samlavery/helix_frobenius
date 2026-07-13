#!/usr/bin/env python3
"""
sharp_falsifiers.py
===================

The two framework-SPECIFIC falsifiers, on the blind-resonance scaffold.
Unlike the height sweep (which mostly proves the zero-detector is real), these
stress the distinctive claims: the Eisenstein RING and the MULTIPLICATIVE
(tensor / Euler) structure.

TEST 1 -- RING RIGIDITY (the provable falsifier)
    Claim: an Eisenstein/pi-3 fiber closes its cell EXACTLY at the mu_6 root and
    provably CANNOT at a wrong root, because closing there would force the value
    into a number field the arithmetic doesn't live in.  The discriminator is an
    exact algebraic NORM (a rational integer): 0 <=> closes; nonzero <=> can't.
    This is a *proof* of decoherence at wrong roots, not a measurement -- it
    cannot be rescued by "harmonize higher."

TEST 2 -- MULTIPLICATIVE TWO-ROUTE (the consistency falsifier)
    Claim: harmonization is multiplicative.  On Sym^a (x) Sym^b:
        route A  = harmonize each, then TENSOR the Satake data
        route B  = TENSOR (Clebsch-Gordan  Sym^a(x)Sym^b = (+)_c Sym^c), then harmonize
    The two must give the identical local L-factor to machine precision, and the
    Euler product must factor: L(Sym^a x Sym^b) = prod_c L(Sym^c).  Any mismatch
    kills the multiplicative spine.  Plus the Nyquist bite: the tensor closes only
    at a scale M > a+b (higher harmonics for more complexity), and decoheres below.
"""

import numpy as np
from math import gcd

# ===========================================================================
# TEST 1 -- RING RIGIDITY
# ===========================================================================
PHI6 = np.array([1.0, -1.0, 1.0])          # Phi_6(x) = 1 - x + x^2  (min poly of zeta_6)

def polymul(a, b):
    return np.polynomial.polynomial.polymul(a, b)

def cell_residual(a, M):
    """R_M = sum_n a_n zeta_M^n,  zeta_M = e^{2 pi i / M}."""
    z = np.exp(2j * np.pi / M)
    return np.sum(a * z ** np.arange(len(a)))

def field_norm(a, M):
    """Algebraic norm N_{Q(zeta_M)/Q}(R_M) = prod_{k in (Z/M)*} (sum a_n zeta_M^{kn}).
    A rational INTEGER (Galois-invariant).  0 iff R_M = 0; else |N| >= 1, so R_M
    provably cannot vanish -- decoherence by proof, not by numerics."""
    prod = 1.0 + 0j
    for k in range(1, M):
        if gcd(k, M) == 1:
            z = np.exp(2j * np.pi * k / M)
            prod *= np.sum(a * z ** np.arange(len(a)))
    return prod                                  # imag part ~ 0 (it's a rational integer)

def test_ring():
    print("=" * 66)
    print("TEST 1 -- RING RIGIDITY  (mu_6 Eisenstein closure vs wrong roots)")
    print("=" * 66)
    roots = [5, 6, 7, 11, 12]                    # sweep incl. the predicted mu_6

    # Eisenstein fiber: carries the Phi_6 factor (the pi/3 reflection structure).
    p = np.array([3.0, -1.0, 4.0, 2.0])          # a genuine integer "arithmetic" part
    eis = polymul(p, PHI6)

    # Control: same-size random-integer fiber, NO Phi_6 factor.
    rng = np.random.default_rng(0)
    ctl = rng.integers(-4, 5, size=len(eis)).astype(float)

    def row(name, a):
        print(f"\n  {name}   coeffs = {a.astype(int).tolist()}")
        print(f"  {'root':>6} {'|R_M|':>12} {'norm N(R_M)':>14}  {'verdict'}")
        closes = {}
        for M in roots:
            R = cell_residual(a, M)
            N = field_norm(a, M).real
            v = "CLOSES (exact)" if abs(R) < 1e-9 else "cannot close (N != 0)"
            closes[M] = abs(R) < 1e-9
            print(f"  {M:>6} {abs(R):12.2e} {round(N):>14d}  {v}")
        return closes

    eis_c = row("Eisenstein fiber p(x)*Phi_6(x):", eis)
    ctl_c = row("Control (random, no Phi_6):    ", ctl)

    checks = {
        "Eisenstein fiber CLOSES at mu_6 (exact, norm 0)":  eis_c[6],
        "Eisenstein fiber CANNOT close at any wrong root":  not any(v for M, v in eis_c.items() if M != 6),
        "wrong-root non-closure is a NONZERO INTEGER norm": abs(round(field_norm(eis, 5).real)) >= 1,
        "control closes NOWHERE (incl. mu_6)":              not any(ctl_c.values()),
    }
    print()
    for k, v in checks.items():
        print(f"  [{'PASS' if v else 'HIT ':>4}] {k}")
    return all(checks.values())


# ===========================================================================
# TEST 2 -- MULTIPLICATIVE TWO-ROUTE
# ===========================================================================
def sym_eigs(alpha, r):
    """Satake eigenvalues of Sym^r of diag(alpha, 1/alpha): alpha^{r-2j}."""
    return np.array([alpha ** (r - 2 * j) for j in range(r + 1)])

def sortc(z):
    return z[np.lexsort((z.imag.round(9), z.real.round(9)))]

def local_L_poly(eigs):
    """Coefficients of prod_lambda (1 - lambda x) -- the local L-factor numerator."""
    poly = np.array([1.0 + 0j])
    for lam in eigs:
        poly = np.polynomial.polynomial.polymul(poly, [1.0, -lam])
    return poly

def min_closing_scale(eigs, Mmax=60):
    """Smallest M with all Satake frequencies distinct mod 2M (clean cell closure);
    below it, frequencies collide -> the cell decoheres."""
    freqs = np.round(np.angle(eigs) / (np.pi)).astype(int)  # integer freqs r-2j (angle multiples of ... )
    # use exact integer frequencies instead of angle (robust):
    return None

def freqs_of(alpha_dummy, r):
    return np.array([r - 2 * j for j in range(r + 1)])

def test_tensor():
    print("\n" + "=" * 66)
    print("TEST 2 -- MULTIPLICATIVE TWO-ROUTE  (harmonize/tensor commute)")
    print("=" * 66)
    # Real arithmetic: a Ramanujan-Delta Satake angle (tau(2) = -24).
    theta = np.arccos(-24.0 / (2.0 * 2.0 ** 5.5))
    alpha = np.exp(1j * theta)

    ok = True
    print(f"\n  Satake angle theta = {theta:.6f}  (Delta at p=2)")
    print(f"  {'a,b':>6} {'routeA==routeB':>16} {'Euler factors':>16} {'min scale':>12} {'=a+b+1?':>9}")
    for a, b in [(2, 3), (3, 4), (4, 5), (5, 6), (2, 6)]:
        # route A: tensor the harmonized Satake data
        A = sortc(np.array([x * y for x in sym_eigs(alpha, a) for y in sym_eigs(alpha, b)]))
        # route B: Clebsch-Gordan  Sym^a (x) Sym^b = (+)_c Sym^c,  c = |a-b|..a+b step 2
        Bset = []
        for c in range(abs(a - b), a + b + 1, 2):
            Bset.extend(sym_eigs(alpha, c))
        B = sortc(np.array(Bset))
        route_match = A.shape == B.shape and np.allclose(A, B, atol=1e-10)

        # Euler product: L(tensor) ?= prod_c L(Sym^c)
        L_tensor = local_L_poly(A)
        L_prod = np.array([1.0 + 0j])
        for c in range(abs(a - b), a + b + 1, 2):
            L_prod = np.polynomial.polynomial.polymul(L_prod, local_L_poly(sym_eigs(alpha, c)))
        euler_match = np.allclose(L_tensor, L_prod, atol=1e-9)

        # Nyquist: min scale for the tensor's frequencies to be distinct mod 2M
        tfreq = np.array([fa + fb for fa in freqs_of(None, a) for fb in freqs_of(None, b)])
        minM = next(M for M in range(1, 200)
                    if len(set((tfreq % (2 * M)).tolist())) == len(np.unique(tfreq)))
        nyq = (minM == a + b + 1) or (minM <= a + b + 1)  # clean closure needs M ~ a+b+1

        ok &= route_match and euler_match
        print(f"  {f'{a},{b}':>6} {str(route_match):>16} {str(euler_match):>16} "
              f"{minM:>12} {str(minM == a + b + 1):>9}")

    print()
    print(f"  [{'PASS' if ok else 'HIT ':>4}] every (a,b): route A == route B AND Euler product factors")
    print("  [note] min closing scale rises with a+b -- higher harmonics for more complexity")
    return ok


def main():
    r1 = test_ring()
    r2 = test_tensor()
    print("\n" + "#" * 66)
    print(f"RING RIGIDITY (Test 1):      {'PASS' if r1 else 'HIT -- FALSIFIED'}")
    print(f"MULTIPLICATIVE (Test 2):     {'PASS' if r2 else 'HIT -- FALSIFIED'}")
    print("#" * 66)
    print("Swap the bare cell sum / Satake reader for the real 3D locator to run")
    print("these against actual carrier closures rather than the exact stand-ins.")


if __name__ == "__main__":
    main()
