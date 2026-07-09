"""(B) ORIGIN <-> s NORMALIZATION: where do the two elliptic legs actually meet?

The weld is the FIXED POINT of the functional-equation involution.  Its numeric coordinate
is pure GAUGE (UnitMidpoint.lean: 'criticality is midpointness; the coordinate is the chart').
UNIT/2 for every unit c (affine_reflection_fixed_iff: c - x = x  <=>  x = c/2):

    chart                      involution            unit c     fixed point (weld)
    centered / Riemann  t      t |-> -t                 0        t = 0     <-- Sam's instinct
    analytic  s                s |-> 1 - s              1        s = 1/2
    arithmetic / motivic  s    s |-> 2 - s              2        s = 1
    Fricke cusp   u = log y    u |-> -log N - u      -log N      u = -(log N)/2

This script (1) shows the two strands are EQUAL term-by-term exactly at the arithmetic weld
s = 1 (AntihelixWindow.strand_swap_fixed_iff, weld_kills/weld_doubles); (2) verifies the
centered-chart translation t = -i(s - c/2) is real <=> Re s = c/2 (UnitMidpoint.centered_chart);
(3) separates the WELD (t=0, readout head Z=e^0=1) from the SPIRAL ARCLENGTH ORIGIN N=0
(Z=0, y -> -infinity) — they are NOT the same point.
"""
import math
import cmath
import numpy as np

print("=" * 78)
print("(B) the weld is a fixed point of the FE involution; its coordinate is gauge")
print("=" * 78)

# ---- (1) the two strands are equal term-by-term exactly at the arithmetic weld s=1 ----
from scipy.special import gammaincc, gamma  # regularized upper incomplete Gamma Q(a,x)


def upperGamma(a, x):
    """Gamma(a, x) = Q(a,x)*Gamma(a), the AntihelixWindow.upperGamma, for a>0."""
    return gammaincc(a, x) * gamma(a)


def strand_helix(r, x, s):
    return r ** s * upperGamma(s, x)


def strand_anti(r, x, s):
    return r ** (2 - s) * upperGamma(2 - s, x)


print("\n(1) helix strand  r^s Gamma(s,x)   vs   antihelix strand  r^{2-s} Gamma(2-s,x)")
print("    difference along the real s-axis (r=1.7, x=0.4): zero exactly at the weld s=1")
r, x = 1.7, 0.4
for s in (0.6, 0.8, 0.95, 1.0, 1.05, 1.2, 1.4):
    d = strand_helix(r, x, s) - strand_anti(r, x, s)
    mark = "  <-- WELD (strands equal: eps=-1 kills, eps=+1 doubles)" if abs(s - 1) < 1e-9 else ""
    print(f"    s={s:.2f}: helix-anti = {d:+.6e}{mark}")

# at the weld, term = r * e^{-x} (upperGamma_one: Gamma(1,x)=e^-x); eps=-1 -> 0, eps=+1 -> 2 r e^-x
weld_term = r * math.exp(-x)
print(f"    at s=1: each strand = r*e^-x = {weld_term:.6f};  eps=-1 => {weld_term - weld_term:.1e} (kill), "
      f"eps=+1 => {2 * weld_term:.6f} (double)")

# ---- (2) centered chart: t = -i(s - c/2) real  <=>  Re s = c/2, for every unit c ----
print("\n(2) centered-chart translation  t = -i(s - c/2)  is REAL  <=>  Re s = c/2")
for c in (0.0, 1.0, 2.0):
    for sre in (c / 2 - 0.3, c / 2, c / 2 + 0.3):
        s = complex(sre, 0.37)
        t = -1j * (s - c / 2)
        print(f"    unit c={c}: Re s={sre:+.2f} (weld at c/2={c/2:.2f}): Im(t)={t.imag:+.4f} "
              f"{'REAL=on weld axis' if abs(t.imag) < 1e-12 else ''}")

# ---- (3) WELD (t=0) is NOT the SPIRAL ARCLENGTH ORIGIN (N=0) ----
print("\n(3) the weld (t=0) vs the spiral arclength origin (N=0) — DIFFERENT points")
# ClosedForm: climber k(y)=e^y/p, arclength S(k) ~ 0 as k->0 (y->-inf, Z=e^y->0); N=S/Delta.
p, rr = 1.0, 1.0
def speed(k):
    return math.sqrt(p ** 2 + rr ** 2 + (2 * math.pi * rr * k) ** 2)
def arclength(k, steps=4000):
    ts = np.linspace(0, k, steps)
    return float(np.trapezoid([speed(t) for t in ts], ts))
Delta = math.pi / 3
print("    readout head Z = e^y (y = Im s = t = the ordinate):")
for y in (-6.0, -2.0, 0.0, 2.0):
    Z = math.exp(y)
    N = arclength(Z / p) / Delta if Z > 0 else 0.0   # k = Z/p
    tag = "  <-- WELD t=0: head at Z=1, ONE phasor, N~O(1)" if abs(y) < 1e-9 else ""
    tag = "  <-- spiral base: Z->0, N->0 (y->-inf)" if y <= -6 else tag
    print(f"      y={y:+.1f}: Z={Z:8.4f}  N(arclength/Delta)={N:8.4f}{tag}")
print("    => N=0 (spiral arclength origin) sits at Z=0, y->-infinity — NOT the weld.")
print("       The weld is the ORDINATE origin t=0 (readout head Z=1), = s=1/2 analytic = s=1 arith.")

print("\n" + "=" * 78)
print("VERDICT (B): the meeting point is the FE involution's fixed point.")
print("  Sam's instinct is RIGHT in the centered/Riemann chart (unit 0): weld = t = 0,")
print("  the '1/2-free' native RH axis (roots real).  Gauge translations: t=0 <=> s=1/2")
print("  (analytic, unit 1) <=> s=1 (arithmetic, unit 2) <=> u=-(logN)/2 (Fricke cusp).")
print("  It is NOT the geometric spiral arclength origin N=0 (that is Z=0, y->-inf), and NOT")
print("  s=0 in the standard analytic/arithmetic s-plane (that is the strip edge, not center).")
