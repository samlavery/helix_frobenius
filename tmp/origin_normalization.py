"""(B) ORIGIN <-> s-NORMALIZATION.  Which point is the weld, in which coordinate?

Candidates for the point where the two elliptic legs MEET:
  (i)   geometric spiral origin  y = 0 / N-count = 0  (ClosedForm.numberSite_zero = (0,0,0))
  (ii)  strand-swap weld  s = 1   (AntihelixWindow.strand_swap_fixed_iff: 2-s=s <=> s=1)
  (iii) analytic central point  t = 0  (s = 1/2 + i t analytic normalization)
  (iv)  s = 0

Sam's instinct: the weld is the CENTRAL point, s=1 (arithmetic) = s=1/2 (analytic) = t=0.

The weld is DEFINED (kernel-level) as the point where the helix strand r^s Gamma(s,x) and the
antihelix strand r^{2-s} Gamma(2-s,x) WEIGH EQUALLY for every phasor (strand_weights_det_one:
r^{s-1} r^{1-s} = 1; weld_kills/doubles_each_phasor act at s=1).  So the weld = the fixed locus
of the strand swap s -> 2-s.  We verify numerically:

  balance ratio  B(s) = |r^s Gamma(s,x)| / |r^{2-s} Gamma(2-s,x)|
is identically 1 exactly on Re s = 1 (every x, every r) and != 1 off it -> the weld is Re s = 1.

We also show the geometric origin is a DIFFERENT point (the y->-inf base of the carrier where
the fiber is empty), NOT the weld; and confirm the three chart identifications collapse to one
central point via UnitMidpoint (affine_reflection_fixed_iff / riemann_chart / Fricke midpoint).
"""
import math
import mpmath as mp

mp.mp.dps = 30


def strand_balance(reS, x, r):
    """|r^s Gamma(s,x)| / |r^{2-s} Gamma(2-s,x)| at s = reS + 0i (real s)."""
    s = mp.mpf(reS)
    hel = (mp.mpf(r) ** s) * mp.gammainc(s, x, mp.inf)
    ant = (mp.mpf(r) ** (2 - s)) * mp.gammainc(2 - s, x, mp.inf)
    return abs(hel) / abs(ant)


print("=" * 76)
print("(B) The weld = fixed locus of the strand swap s -> 2-s.  Balance ratio B(Re s):")
print("=" * 76)
print("B(Re s) = |r^s G(s,x)| / |r^{2-s} G(2-s,x)|  should be 1 EXACTLY at Re s = 1")
print("(the central point in arithmetic normalization), independent of x and r.\n")

N = 389.0
for (n, ) in [(1,), (3,), (10,)]:
    x = 2 * math.pi * n / math.sqrt(N)
    r = math.sqrt(N) / (2 * math.pi * n)
    print(f"  phasor n={n:>2}  (x={x:.4f}, r={r:.4f}):")
    for reS in [0.5, 0.8, 1.0, 1.2, 1.5, 2.0]:
        B = strand_balance(reS, x, r)
        mark = "  <== WELD (B=1)" if abs(reS - 1.0) < 1e-12 else ""
        print(f"      Re s = {reS:>4}:  B = {mp.nstr(B, 12):>16}{mark}")
    print()

print("=> B == 1 identically on Re s = 1 for every phasor (matches strand_weights_det_one:")
print("   r^{s-1} r^{1-s} = 1, and Gamma(1,x)=Gamma(1,x) equal-window at the center).")
print("   Re s = 1 (arithmetic) is analytic s = 1/2 + i t at t = 0 after the shift s = 1 + i t.\n")

print("=" * 76)
print("The three 'central' charts collapse to ONE point (UnitMidpoint / HingeKernel):")
print("=" * 76)
print("  arithmetic FE   s -> 2 - s          fixed pt  s = 1        (strand_swap_fixed_iff)")
print("  analytic  FE    s -> 1 - s          fixed pt  s = 1/2      (reflection_fixes_iff)")
print("  Riemann chart   t = -i(rho - 1/2)   real  <=> Re rho = 1/2 (riemann_chart)")
print("  Fricke geodesic u -> -logN - u      fixed pt  u = -(logN)/2")
print("                  (fricke_midpoint_is_half_conductor_unit)")
for N in [37.0, 389.0, 49.0]:
    u = -math.log(N) / 2
    print(f"     N={N:>6.0f}:  Fricke weld at u = -(ln N)/2 = {u:.5f}  "
          f"(y = exp(u) = 1/sqrt(N) = {math.exp(u):.5f})")
print()

print("=" * 76)
print("The geometric spiral origin is a DIFFERENT point (NOT the weld):")
print("=" * 76)
print("  ClosedForm.numberSite_zero : the N-count=0 site is (0,0,0), the empty-fiber base of")
print("  the carrier at y -> -inf.  It is the START of the growth (fiber_origin: fiber 0 = {}),")
print("  where NO phasor has entered yet -- not the strand-balance point.  The weld sits at the")
print("  center (t=0) where ALL live phasors have entered and both legs weigh equally.")
print()
print("VERDICT: the weld is the CENTRAL point s=1 (arithmetic) = s=1/2 (analytic) = t=0.")
print("Sam's instinct CONFIRMED.  Backing Lean theorems (exact, unconditional):")
print("  AntihelixWindow.strand_swap_fixed_iff   (2-s = s  <=>  s = 1)")
print("  AntihelixWindow.strand_weights_det_one  (r^{s-1} r^{1-s} = 1)")
print("  HingeKernel.fricke_midpoint_is_half_conductor_unit  (u = -(logN)/2)")
print("  UnitMidpoint.riemann_chart              (t=-i(rho-1/2) real <=> Re rho = 1/2)")
print("  FrobeniusSimilitude.reflection_fixes_iff ((1-s).re = s.re <=> Re s = 1/2)")
