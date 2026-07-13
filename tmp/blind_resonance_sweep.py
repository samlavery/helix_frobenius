#!/usr/bin/env python3
"""
blind_resonance_sweep.py
========================

Falsification harness for the harmonic-closure claim of the carrier framework.

CLAIM UNDER TEST
    An arithmetic fiber's bank closes (residual -> 0) at its PREDICTED harmonic
    roots and DECOHERES (residual stays O(1)) at every wrong root.  Closure that
    only appears when you *search* for the root, or that a scrambled control also
    shows, is an overfit, not a signal.

WHY THIS IS A REAL FALSIFIER (not a confirmation machine)
    * The right roots are FIXED IN ADVANCE from independent arithmetic (here the
      known nontrivial zeros of zeta), blind to the sweep -- no root hunting.
    * A phase-SCRAMBLED control fiber must show NO resonance at those roots; if it
      dips there, the "signal" was fittable noise and the test has FAILED.
    * The discriminator is the depth of the residual dip (deep+sharp at the right
      root = coherent closure; shallow/flat = decohered).

HITS (to be published as loudly as passes)
    - the signal does NOT dip at a predicted root, or
    - it dips as deep at a WRONG root (a non-zero) as at a real one, or
    - the scrambled control dips at the predicted roots too, or
    - the roots can only be located by peeking at the answer.

The closure model here is a transparent, self-contained stand-in (a smoothed
truncated eta-readout of the bank on the critical line).  Swap in the real 3D
locator at close_bank() to run the same protocol on the actual carrier.
"""

import numpy as np

# ---------------------------------------------------------------------------
# Independently-known "right roots": the first nontrivial zeros of zeta.
# Fixed here in advance; the sweep never gets to choose them.
# ---------------------------------------------------------------------------
ZETA_ZEROS = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])

# "Wrong roots": heights in the WIDE gaps between consecutive zeros, kept well
# clear of every zero (>= 1.5 away) so the control is genuinely empty.
# (zeros near here: 14.13 21.02 25.01 30.42 32.94 37.59 40.92 43.33)
WRONG_ROOTS = np.array([17.5, 23.0, 27.7, 35.2, 39.2])


# ---------------------------------------------------------------------------
# The bank + its closure readout.
#   coeffs[n] are the fiber coefficients (n = 1..N).  The bank readout on the
#   critical line at height h is  sum_n coeffs[n] n^{-1/2 - i h}, smoothed by a
#   Hann taper (the stand-in for the growth window).  |readout| DIPS where the
#   bank focally closes -- i.e. at the represented function's zeros.
# ---------------------------------------------------------------------------
def bank_readout(coeffs, h, taper):
    n = np.arange(1, len(coeffs) + 1)
    return np.sum(coeffs * taper * n ** (-0.5) * np.exp(-1j * h * np.log(n)))


def close_bank(coeffs, h, taper):
    """Residual of the bank at probe root h.  DEMO STAND-IN for the real 3D
    focal-closure locator: return |readout|.  Small = closes; O(1) = decoheres."""
    return abs(bank_readout(coeffs, h, taper))


def sweep(coeffs, heights, taper):
    return np.array([close_bank(coeffs, h, taper) for h in heights])


# ---------------------------------------------------------------------------
# Fibers.
# ---------------------------------------------------------------------------
def eta_coeffs(N):
    """The genuine arithmetic fiber: alternating zeta (eta), same critical zeros
    as zeta, but a convergent bank.  coeffs[n-1] = (-1)^{n-1}."""
    return np.array([(-1.0) ** (k) for k in range(N)])  # +,-,+,-,...


def scrambled_coeffs(N, seed=0):
    """Control fiber: same |coeffs| but RANDOM signs -- a structureless impostor.
    Must show no resonance at the predicted roots."""
    rng = np.random.default_rng(seed)
    return rng.choice([-1.0, 1.0], size=N)


def hann(N):
    k = np.arange(1, N + 1)
    return 0.5 * (1.0 + np.cos(np.pi * (k - 1) / N))


# ---------------------------------------------------------------------------
# Verdict logic.
# ---------------------------------------------------------------------------
def coherence(coeffs, root, taper, bg_halfwidth=3.0):
    """Coherence ratio at `root`: (median background residual) / (residual AT the
    root).  >>1 means the bank closes there; ~1 means it decoheres.  Uses the
    median over a +/-3 window as background -- robust to the narrow dips of any
    other zeros that happen to fall in the window."""
    res = close_bank(coeffs, root, taper)
    hs = np.linspace(root - bg_halfwidth, root + bg_halfwidth, 121)
    bg = np.median(sweep(coeffs, hs, taper))
    return bg / max(res, 1e-12)


def report(name, coeffs, taper):
    print(f"\n=== {name} ===")
    print(f"{'root':>10} {'kind':>10} {'residual':>12} {'coherence':>11}")
    right, wrong = [], []
    for r in ZETA_ZEROS:
        c = coherence(coeffs, r, taper)
        right.append(c)
        print(f"{r:10.4f} {'ZERO':>10} {close_bank(coeffs,r,taper):12.6f} {c:11.1f}")
    for r in WRONG_ROOTS:
        c = coherence(coeffs, r, taper)
        wrong.append(c)
        print(f"{r:10.4f} {'non-zero':>10} {close_bank(coeffs,r,taper):12.6f} {c:11.1f}")
    return np.array(right), np.array(wrong)


def main():
    N = 4000
    taper = hann(N)
    COH = 50.0  # a genuine closure has coherence >= 50x; the random floor is ~few

    print("BLIND RESONANCE SWEEP  --  harmonic closure falsification harness")
    print("Predicted right roots (fixed from arithmetic, blind to the sweep):")
    print("  zeta zeros:", np.round(ZETA_ZEROS, 4))
    print("Wrong-root controls (kept clear of every zero):", np.round(WRONG_ROOTS, 4))
    print(f"Closure threshold: coherence >= {COH:.0f}x background")

    sig_right, sig_wrong = report("SIGNAL fiber  (eta = arithmetic)", eta_coeffs(N), taper)

    # Scrambled control, worst case over 10 seeds (conservative for the control).
    scr_right = np.zeros(len(ZETA_ZEROS))
    for seed in range(10):
        c = np.array([coherence(scrambled_coeffs(N, seed), r, taper) for r in ZETA_ZEROS])
        scr_right = np.maximum(scr_right, c)
    print("\n=== SCRAMBLED control  (random signs, worst of 10 seeds) ===")
    for r, c in zip(ZETA_ZEROS, scr_right):
        print(f"{r:10.4f} {'ZERO':>10} {'':>12} {c:11.1f}")

    # ---- pass/hit adjudication -------------------------------------------
    print("\n" + "=" * 62)
    checks = {
        "signal CLOSES at every predicted root (coh >= 50)": np.all(sig_right >= COH),
        "signal DECOHERES at every wrong root (coh < 50)":   np.all(sig_wrong < COH),
        "scrambled DECOHERES at every predicted root":       np.all(scr_right < COH),
        "signal beats scrambled by >= 100x at the zeros":    sig_right.min() > 100 * scr_right.max(),
    }
    for k, v in checks.items():
        print(f"  [{'PASS' if v else 'HIT ':>4}] {k}")
    ok = all(checks.values())
    print("=" * 62)
    tag = ("PASS -- resonance is selective (right roots only), blind "
           "(roots fixed from arithmetic), and control-clean (scramble is flat)")
    print("VERDICT:", tag if ok else "HIT -- falsified (see failed checks above)")
    print("(Swap close_bank() for the real 3D locator to run this on the carrier.)")


if __name__ == "__main__":
    main()
