#!/usr/bin/env python3
"""
stress_real.py -- point the REAL locator at REAL data with a fair negative
control, on a test that can actually FAIL (unlike the synthetic passes).

Uses focal_closure.closure() unchanged.  The only thing added is a SCRAMBLED
fiber: identical coefficient magnitudes, random signs -- a structureless impostor
with the same "size" but no arithmetic.  Then:

  (overfit test)       does the real closure dip at the true zeta zero while the
                       scrambled fibers do NOT?  If scrambled dips as deep, the
                       locator is finding structure that isn't there -> HIT.
  (false-positive)     over a window with exactly ONE zero, does the real fiber
                       close ONLY at the zero and stay flat elsewhere?  A deep
                       closure away from the zero -> HIT.
  (specificity)        does the real dip beat the scrambled floor by a wide,
                       unambiguous margin?

This can say NO.  That is the point.
"""

import numpy as np
import focal_closure as fc

Z1 = 14.134725           # first nontrivial zero of zeta (= eta's first critical zero)


def scrambled(base_name, seed):
    """Same |coeffs| as `base_name`, random signs; lane_key = sign.  Fair impostor."""
    base = fc.FAMILIES[base_name]
    def make(N):
        coeffs, _ = base.make(N)
        rng = np.random.default_rng(seed)
        signs = rng.choice([-1.0, 1.0], size=len(coeffs))
        c = np.abs(coeffs) * signs
        return c.astype(np.complex128), signs.astype(np.int64)
    return fc.Family(f"{base_name}~scr{seed}", base.kind, make, max_N=base.max_N)


def main():
    print("=" * 68)
    print("STRESS: real locator, real data, fair scrambled control (can FAIL)")
    print("=" * 68)

    real = fc.FAMILIES["eta"]
    scrs = [scrambled("eta", s) for s in range(5)]

    # ---- (1) depth AT the true zero -------------------------------------
    print(f"\nclosure() AT the first zeta zero  y = {Z1}  (smaller = deeper closure)")
    real_at = fc.closure(real, Z1)
    scr_at = [fc.closure(f, Z1) for f in scrs]
    print(f"  eta (real):        {real_at:.6f}")
    for i, v in enumerate(scr_at):
        print(f"  eta scrambled #{i}: {v:.6f}")
    scr_floor_at = min(scr_at)   # best (deepest) impostor -- conservative

    # ---- (2) window sweep: exactly one zero in [12.5, 15.5] -------------
    print(f"\nsweep y in [12.5, 15.5] (one zero, at {Z1}); depth = closure minimum")
    ys = np.linspace(12.5, 15.5, 46)
    rv = np.array([fc.closure(real, y) for y in ys])
    imin = rv.argmin()
    print(f"  real  min closure = {rv.min():.5f} at y = {ys[imin]:.4f}   "
          f"(true zero {Z1}; off by {abs(ys[imin]-Z1):.4f})")
    # deepest scrambled minimum over the same window (worst case for the control)
    scr_min = min(np.array([fc.closure(f, y) for y in ys]).min() for f in scrs)
    print(f"  scrambled min closure over the window (best of 5 impostors) = {scr_min:.5f}")

    # false positive: any deep real closure NOT near the zero?
    away = np.abs(ys - Z1) > 0.4
    real_bg = rv[away].min()
    print(f"  real closure minimum AWAY from the zero (|y-zero|>0.4) = {real_bg:.5f}")

    # ---- verdict ---------------------------------------------------------
    print("\n" + "=" * 68)
    checks = {
        "real CLOSES at the zero (closure < 0.05)":        real_at < 0.05,
        "scrambled does NOT close at the zero (> 0.3)":    scr_floor_at > 0.30,
        "real dip beats scrambled floor by >= 10x":        scr_floor_at > 10 * real_at,
        "real is FLAT away from the zero (bg > 0.3)":      real_bg > 0.30,
        "located min sits on the true zero (< 0.1 off)":   abs(ys[imin] - Z1) < 0.1,
    }
    for k, v in checks.items():
        print(f"  [{'PASS' if v else 'HIT ':>4}] {k}")
    ok = all(checks.values())
    print("=" * 68)
    if ok:
        print("HOLDS: real zero found, deep; impostors flat; no false positive.")
        print("  (A genuine test that could have said NO, and didn't.)")
    else:
        print("HIT -- the theory was stressed and something gave. See failed checks.")
        print("  Report this as loudly as any confirmation.")


if __name__ == "__main__":
    main()
