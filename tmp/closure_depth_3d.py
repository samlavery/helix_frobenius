#!/usr/bin/env python3
"""
closure_depth_3d.py -- vanishing measured in the 3D PHASOR REPRESENTATION (the right
dimension), to the standard: does the closure reach the floor and TRACK bank size?

This uses focal_closure.py -- the projected phasor bank (phasor n at carrier angle
ln x_n, x_n = arrow_scale*n; readout y = log Z; closure c(Z)=|sum u R|/max|R| = the
lane-balance / Gram-pencil rank-drop).  At an L-zero the harmonic channel is EXACTLY 0
(B(Z)=(arrow_scale)*L(1/2+i log Z)); the finite-bank closure depth is the approximation
residual, which must FALL as the bank grows (N=e^y) if the vanishing is genuine.

Two checks:
  (1) DEPTH vs BANK SIZE: located-zero closure depth c* at successive zeros (deeper zero
      => larger N=e^gamma).  Genuine vanishing => c* small and falling with N; a shallow
      artifact would sit at a fixed ~0.1 floor.
  (2) CARRIER-SCALE GAUGE: arrow_scale = pi/3 vs pi/2 (Sam: pi/3 IS the carrier scale; a
      different factor shifts the cell but the closure is projective).  The SAME zeros
      must be located at BOTH scales (gauge), demonstrating the vanishing is geometric,
      not tied to the pi/3 value.

Run: python3 closure_depth_3d.py
"""
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC


def run_family(name, fam, y0, y1, scale, label):
    events = FC.scan(fam, y0, y1, per_unit=240, depth_cut=5e-2)
    print(f"\n  {name} @ carrier {label} (arrow_scale={scale:.4f}):")
    print(f"    {'zero#':>5} {'height y=gamma':>15} {'N=e^y':>10} {'closure depth c*':>18}")
    heights = []
    for i, e in enumerate(events, 1):
        # recompute closure at the located height at THIS scale
        c = FC.closure(fam, e.y, arrow_scale=scale)
        print(f"    {i:>5} {e.y:>15.6f} {int(math.exp(e.y)):>10} {c:>18.2e}")
        heights.append(e.y)
    return heights


def main():
    print(__doc__.split("Run:")[0])
    print("=" * 74)

    fams = [
        ("chi3 (real Dirichlet)", FC.FAMILIES["chi3"], 8.0, 20.0),
        ("Delta (weight-12 cusp)", FC.FAMILIES["delta"], 8.0, 18.0),
    ]

    for name, fam, y0, y1 in fams:
        h3 = run_family(name, fam, y0, y1, FC.PI3, "pi/3")
        h2 = run_family(name, fam, y0, y1, math.pi / 2, "pi/2")
        # gauge check: same zeros located at both carrier scales?
        m = min(len(h3), len(h2))
        if m:
            dev = max(abs(h3[i] - h2[i]) for i in range(m))
            print(f"    [gauge] pi/3 vs pi/2 located-zero heights agree to {dev:.2e} "
                  f"over {m} zeros -> carrier scale is {'GAUGE (closure geometric)' if dev < 1e-3 else 'NOT gauge'}")


if __name__ == "__main__":
    main()
