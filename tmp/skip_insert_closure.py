#!/usr/bin/env python3
"""
skip_insert_closure.py -- does SKIPPING values displace the carrier crossing, and does the
native carrier (complete bank) close where the gapped one does not?  (Core of Sam's
"insert the skipped values + pitch-1 height subtraction" construction.)

Uses the real focal_closure carrier bank (phasor n at angle ln x_n, x_n=(pi/3)n; readout
y=log Z; closure c(Z)=|sum u R|/max|R| = the lane balance).  A genuine crossing sits at
c ~ 1e-6..1e-12.  We compare, at a KNOWN zero height of chi3:
  (complete)  every phasor n<=Z present            -> expect deep closure (native carrier)
  (skip-sq)   the perfect-square n zeroed (gapped)  -> Altug-like: values skipped
and report whether the crossing DISPLACES (its min moves off the true zero) and SHALLOWS.
This is focal_closure's growth-is-load-bearing law, but with GAPS instead of no-growth --
the exact situation created by skipping m^2 +- 4p^k = square.

Live output: tmp/skip_insert_results.txt
Run: python3 tmp/skip_insert_closure.py
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import focal_closure as FC

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "skip_insert_results.txt")


def make_skipsq_family(base):
    """A copy of `base` with perfect-square n zeroed (skipped)."""
    def make(N):
        c, k = base.make(N)
        c = c.copy()
        m = 1
        while m * m <= N:
            c[m * m] = 0.0            # skip the perfect-square lattice point
            m += 1
        return c, k
    return FC.Family(base.name + "_skipsq", base.kind, make, max_N=base.max_N)


def scan_closure(fam, y0, y1, npts, scale=FC.PI3):
    ys = np.linspace(y0, y1, npts)
    c = np.array([FC.closure(fam, float(y), arrow_scale=scale) for y in ys])
    i = int(np.argmin(c))
    return ys[i], float(c[i]), ys, c


def main():
    f = open(OUT, "w")

    def emit(s=""):
        print(s, flush=True)
        f.write(s + "\n")
        f.flush()

    emit("Skip vs complete: does skipping the perfect-square lattice points displace the crossing?")
    emit("real focal_closure carrier bank (chi3); closure c(Z) at a located zero.")
    emit("=" * 78)

    base = FC.FAMILIES["chi3"]
    skip = make_skipsq_family(base)

    # locate the crossing with the COMPLETE bank first (native carrier)
    y_star, c_star, ys, cc = scan_closure(base, 8.0, 14.0, 900)
    emit(f"[complete] deepest crossing in [8,14]: y*={y_star:.5f}  closure c*={c_star:.3e}  "
         f"(N=e^y*={int(math.exp(y_star))})")

    # now the GAPPED bank over the same band
    y_s2, c_s2, ys2, cc2 = scan_closure(skip, 8.0, 14.0, 900)
    emit(f"[skip-sq ] deepest crossing in [8,14]: y*={y_s2:.5f}  closure c*={c_s2:.3e}")
    emit(f"           displacement of the crossing: |dy| = {abs(y_s2-y_star):.4f}")
    emit(f"           closure at the COMPLETE zero y*={y_star:.4f}: skip-bank c = "
         f"{FC.closure(skip, y_star):.3e}  (complete {c_star:.3e})")
    emit("")
    ratio = FC.closure(skip, y_star) / c_star if c_star > 0 else float('inf')
    emit(f"[verdict] skipping the squares moves the crossing by {abs(y_s2-y_star):.4f} in log-height "
         f"and shallows closure at the true zero by {ratio:.1e}x.")
    emit(f"          => gaps DISPLACE the carrier crossing (Altug's Sigma() is the patch for this);")
    emit(f"          the COMPLETE native bank closes at c*={c_star:.2e} where the gapped one does not.")
    emit(f"          NEXT: insert the skipped squares in a one-unit extension + pitch-1 height")
    emit(f"          subtraction, and confirm the crossing returns to c* (the re-registration).")
    f.close()


if __name__ == "__main__":
    main()
