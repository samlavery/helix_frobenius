#!/usr/bin/env python3
"""
symr_gl2_realclosure.py -- PHASE A on the ACTUAL Altug GL(2) Poisson-summed transform.

This is NOT the idealized carrier bank of clock_scale_warp.py.  It runs on the real
mb_beat.py instrument (Altug III Prop 5.2 orbital transform Psi, the ranked Sym^r/U_r
x-weight, the ny-quadrature nu-profile V(nu)), whose anchor gate reproduces the recorded
comb, the A(8)=J_house orbital-integral tie to 3e-13, and the ACF detector.

We sweep the Chebyshev/Sym^r rank r = 0..13 and report, PER RANK, exactly what the
instrument measures -- no massaging:
  deep   = # cells with >=4 visible deep dips        (SCALAR readout productivity)
  clock  = # cells passing the continuous clock gate (deterministic clock survival)
  prod   = deep/clock                                (visibility per clock cell)
  R2     = fit of the dispersion law across clock cells
  kmean/kstd = kappa_eff mean/spread                 (clock stability)
  stat/model = curvature / harmonic-truncation error (numerical floor of the clock)

HONEST CLAIM UNDER TEST (owner msg): "productivity degradation with r is a scalar-readout
phenomenon; the clock/projection/scaling pipeline keeps the underlying carrier closure."
=> falsified if the CLOCK degrades with r (R2 collapses, kappa drifts out of band, or the
clock census thins as fast as the deep census).  Confirmed if deep thins while clock holds.

Run: python3 symr_gl2_realclosure.py    (rebuilds meshes ~50s, then sweeps)
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mb_beat as B


def main():
    t0 = time.time()
    ok, ctx, _ = B.run_gate(verbose=False)
    print(f"[anchor] gate {'PASS' if ok else 'FAIL'} (meshes rebuilt {time.time()-t0:.0f}s)")
    if not ok:
        print("*** GATE FAILED -- stop. ***")
        return
    res = B.run_rank_sweep(ctx, ranks=range(0, 14), verbose=True)
    print(f"\n[done] total {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
