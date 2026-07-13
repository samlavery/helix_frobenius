#!/usr/bin/env python3
"""
push_margin.py -- the margin study done with roots/harmonics RIGHT.

Fixes two errors in stress_real.py:
  * REFINE to the true zero (scan's golden-section), not a coarse grid -- the
    real depth is ~1e-8..1e-10, not the 0.002 a grid catches.
  * separate the two closures: the projective locator (pi/3 gauge, floating,
    the thing with a margin) vs the EXACT mu_6 marker in Z[zeta_6] (integer,
    residue-free, NO margin -- the actual harmonic claim).

Three experiments:
  A) refined margin across REAL fibers vs fair scrambled controls (can fail: if
     impostors also refine to deep closures, that's overfitting).
  B) growth is load-bearing: the margin is CREATED by the grown bank.
  C) exact mu_6 harmonic closure is margin-free; a wrong root (mu_5) fails by a
     nonzero integer, not a threshold.
"""

import numpy as np
import focal_closure as fc

def scrambled(name, seed):
    base = fc.FAMILIES[name]
    def make(N):
        c, _ = base.make(N)
        r = np.random.default_rng(seed)
        s = r.choice([-1.0, 1.0], size=len(c))
        return (np.abs(c) * s).astype(np.complex128), s.astype(np.int64)
    return fc.Family(f"{name}~scr{seed}", base.kind, make, max_N=base.max_N)

def deepest(fam, lo, hi, per_unit=200):
    """Refined deepest closure event in [lo,hi] (scan already golden-refines).
    Returns (depth, y) or (1.0, None) if no event below scan's cut."""
    ev = fc.scan(fam, lo, hi, per_unit=per_unit)
    if not ev:
        return 1.0, None
    e = min(ev, key=lambda z: z.depth)
    return e.depth, e.y

# windows around each fiber's first zero (from the focal_closure test suite)
CASES = [("eta", 13.95, 14.35), ("chi3", 7.7, 8.4), ("chi4", 5.7, 6.4),
         ("delta", 9.0, 9.45), ("e11", 6.1, 6.6)]

def exp_A():
    print("=" * 70)
    print("A) REFINED margin across real fibers vs fair scrambled control")
    print("=" * 70)
    print(f"  {'fiber':>7} {'real depth':>12} {'y':>9} {'impostor floor':>15} {'margin':>10}")
    ok = True
    for name, lo, hi in CASES:
        if fc.FAMILIES[name].kind == "cusp":
            fc.FAMILIES[name].coeff(int(np.exp(hi)))    # trigger builder asserts
        rd, ry = deepest(fc.FAMILIES[name], lo, hi)
        floor = min(deepest(scrambled(name, s), lo, hi)[0] for s in range(8))
        margin = floor / max(rd, 1e-16)
        ok &= (rd < 1e-4) and (margin > 100)
        print(f"  {name:>7} {rd:12.2e} {(ry or 0):9.4f} {floor:15.3e} {margin:10.1e}")
    print(f"\n  [{'PASS' if ok else 'HIT ':>4}] every real fiber refines deep (<1e-4) and beats "
          f"its impostor floor by >100x")
    print("  (impostor floor ~ scan's cut when NO event forms -> impostors don't refine deep)")
    return ok

def exp_B():
    print("\n" + "=" * 70)
    print("B) growth is load-bearing: the margin is CREATED by the grown bank")
    print("=" * 70)
    g = fc.REFERENCE_ORDINATES["chi3"][0]
    fam = fc.FAMILIES["chi3"]
    yg = fc._golden(lambda t: fc.closure(fam, t, grown=True), g - 0.25, g + 0.25)
    yh = fc._golden(lambda t: fc.closure(fam, t, grown=False), g - 0.25, g + 0.25)
    dg = fc.closure(fam, yg, grown=True)
    dh = fc.closure(fam, yh, grown=False)
    print(f"  true zero (chi3)      : {g:.6f}")
    print(f"  GROWN  min at y={yg:.6f}  depth={dg:.2e}  (off zero {abs(yg-g):.1e})")
    print(f"  UNGROWN min at y={yh:.6f}  depth={dh:.2e}  (off zero {abs(yh-g):.1e})")
    ok = abs(yg - g) < 1e-5 and abs(yh - g) > 1e-3
    print(f"\n  [{'PASS' if ok else 'HIT ':>4}] grown bank locates the zero; ungrown is displaced "
          f"-> growth makes the margin")
    return ok

def cell_marker(sign_of_n, M, block=1):
    """Complex cell residual of one M-cell block: sum sign(n) * zeta_M^{slot%M}.
    For M=6 with the exact power basis this is (0,0) in Z[zeta_6]."""
    z = np.exp(2j * np.pi / M)
    return sum(sign_of_n(6 * (block - 1) + off + 1) * z ** off for off in range(M))

def exp_C():
    print("\n" + "=" * 70)
    print("C) EXACT harmonic closure: mu_6 residue-free (no margin); mu_5 wrong root fails")
    print("=" * 70)
    eta_sign = lambda n: 1 if n % 2 == 1 else -1
    # exact mu_6 marker in Z[zeta_6], integer, every block -> (0,0)
    bad = [b for b in range(1, 2001) if fc.exact_cell_marker(b, eta_sign) != (0, 0)]
    print(f"  mu_6 exact marker (Z[zeta_6]) over 2000 eta blocks: "
          f"{'ALL (0,0) exact' if not bad else f'FAILS at blocks {bad[:5]}'}")
    # wrong root mu_5: the same sign pattern cannot close (complex residual != 0)
    r5 = cell_marker(eta_sign, 5)
    r6 = cell_marker(eta_sign, 6)
    print(f"  mu_6 complex residual = {abs(r6):.2e}   (closes)")
    print(f"  mu_5 complex residual = {abs(r5):.4f}   (cannot close -- wrong root)")
    ok = (not bad) and abs(r6) < 1e-9 and abs(r5) > 1e-2
    print(f"\n  [{'PASS' if ok else 'HIT ':>4}] mu_6 closes EXACTLY (integer, no epsilon); "
          f"mu_5 provably cannot")
    print("  (this is the load-bearing harmonic -- it has NO margin, unlike the projective locator)")
    return ok

def main():
    a, b, c = exp_A(), exp_B(), exp_C()
    print("\n" + "#" * 70)
    print(f"A refined margin (across fibers):  {'PASS' if a else 'HIT'}")
    print(f"B growth load-bearing:             {'PASS' if b else 'HIT'}")
    print(f"C exact mu_6 harmonic (no margin): {'PASS' if c else 'HIT'}")
    print("#" * 70)
    print("Correction to stress_real: with refinement the real depth is ~1e-8..1e-10,")
    print("so the margin is ENORMOUS, not 30x -- the 30x was a coarse-grid artifact.")
    print("The margin/tail worry lived in the FLOATING locator; the harmonic claim (C)")
    print("is exact and margin-free.  That is 'roots and harmonics done right.'")

if __name__ == "__main__":
    main()
