"""Find and display the first 10 zeros (located vanishing points) of the five L-functions of the
spec -- zeta (via eta), chi3, chi4, chi5, chi8 -- with the phasor finder.

  FOUND  : the model's located vanishing points.  vanishing_points detects candidates as minima of
           the faithful untapered |abel_fiber| (Abel summation, sec 5), then refines each on the
           smooth-tapered accelerator (same limit).  No analytic L is used to find them.
  truth  : independent ground truth for confidence -- zeta via mpmath.zetazero; chi via the Hurwitz
           form L(s,chi)=q^{-s} sum_a chi(a) zeta(s,a/q), minimised with mpmath.
"""
import numpy as np
import mpmath as mp
import helix_phasor_tool as H

mp.mp.dps = 20

# the five real characters of the spec (sec 3); eta is the zeta channel's alternating regulator
CHARS = [
    ("zeta (eta)", 2, H.eta_coeff,                          52.0),
    ("chi3",       3, lambda n: (0.0, 1.0, -1.0)[n % 3],    42.0),
    ("chi4",       4, lambda n: (0.0, 1.0, 0.0, -1.0)[n % 4], 40.0),
    ("chi5",       5, lambda n: (0.0, 1.0, -1.0, -1.0, 1.0)[n % 5], 40.0),
    ("chi8",       8, lambda n: (0.0, 1.0, 0.0, -1.0, 0.0, -1.0, 0.0, 1.0)[n % 8], 36.0),
]


def _gss(f, a, b, iters=60):
    gr = (5.0 ** 0.5 - 1.0) / 2.0
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(iters):
        if fc < fd:
            b, d, fd = d, c, fc; c = b - gr * (b - a); fc = f(c)
        else:
            a, c, fc = c, d, fd; d = a + gr * (b - a); fd = f(d)
    return 0.5 * (a + b)


def model_zeros(coeff, k, y_max, accelerate=True):
    """First k located vanishing points of the phasor fiber on the critical line.
    accelerate=True uses the smooth-tapered accelerator for pinpoint (~1e-6) location;
    accelerate=False stays on the faithful untapered fiber (~7e-4)."""
    vps = sorted(H.vanishing_points(coeff, y_max=y_max, samples=int(y_max * 240),
                                    M=8000, refine=True, accelerate=accelerate))
    return vps[:k]


def truth_zeros(name, coeff, q, guesses):
    if name.startswith("zeta"):
        return [float(mp.im(mp.zetazero(j))) for j in range(1, len(guesses) + 1)]
    L = lambda t: float(abs(q ** (-(mp.mpf('0.5') + 1j * mp.mpf(t)))
                           * mp.fsum(coeff(a) * mp.zeta(mp.mpf('0.5') + 1j * mp.mpf(t), mp.mpf(a) / q)
                                     for a in range(1, q))))
    return [_gss(L, g - 0.03, g + 0.03) for g in guesses]


if __name__ == "__main__":
    K = 10
    print("=" * 60)
    print(f"  FIRST {K} ZEROS of the five spec L-functions (phasor finder)")
    print("=" * 60)
    for name, q, coeff, y_max in CHARS:
        found = model_zeros(coeff, K, y_max)
        truth = truth_zeros(name, coeff, q, found)
        print(f"\n{name}  (modulus {q}):")
        print(f"   {'k':>2} {'FOUND (phasor)':>16} {'truth':>14} {'|diff|':>10}")
        errs = []
        for k, (m, t) in enumerate(zip(found, truth), 1):
            errs.append(abs(m - t))
            print(f"   {k:>2} {m:>16.6f} {t:>14.6f} {abs(m - t):>10.1e}")
        tag = "" if len(found) == K else f"   [only {len(found)} found below y={y_max:.0f}]"
        print(f"   max |diff| = {max(errs):.1e}{tag}")
