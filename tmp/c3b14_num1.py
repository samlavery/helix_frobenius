#!/usr/bin/env python3
"""
C3 batch 14 -- numerical block 1.  FACTOR AUDIT, run BEFORE any Lean is written.

Two identities are to be formalised.  Every constant in them is checked here by direct
quadrature against closed forms, on functions with NO symmetry, so that all four moment
slots (cosMom A, sinMom A, cosMom B, sinMom B) are exercised.

  (I)  carrier_conv_pairing
       int_v [ int_p A(v+p) B(v-p) dp ] cos(x v) dv
         = (1/2) [ cosMom A (x/2) cosMom B (x/2) - sinMom A (x/2) sinMom B (x/2) ]

  (II) cosMom_Rker,  R(v) := int_p p^2 Phi(v+p) Phi(v-p) dp
       cosMom R (2x) = (1/4) ( cosMom Phi x * cosMom kM2 x + sinMom kM1 x ^ 2 )

Sign convention note: cosMom f y = int f(t) cos(y t) dt, sinMom f y = int f(t) sin(y t) dt,
matching C3B10.  The MINUS sign in (I) is the point of the audit: the naive guess has a plus.
"""
import numpy as np

# ------------------------------------------------------------------ grids
def simp_w(n):
    w = np.ones(n + 1); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0
    return w

def simp(y, h):
    return (h / 3.0) * np.dot(simp_w(len(y) - 1), y)

# ================================================================= PART I
print("=" * 78)
print("PART I -- carrier_conv_pairing, on ASYMMETRIC test functions")
print("=" * 78)
print("  A(t) = exp(-(t-1)^2)   [neither even nor odd]")
print("  B(t) = exp(-2 t^2 + t) [neither even nor odd]")
print()
A = lambda t: np.exp(-(t - 1.0) ** 2)
B = lambda t: np.exp(-2.0 * t ** 2 + t)

TL = 9.0; NT = 24000
tg = np.linspace(-TL, TL, NT + 1); ht = 2 * TL / NT

def cosMom(f, y):  return simp(f(tg) * np.cos(y * tg), ht)
def sinMom(f, y):  return simp(f(tg) * np.sin(y * tg), ht)

# closed forms: int exp(-a(t-m)^2) cos(y t) dt = sqrt(pi/a) exp(-y^2/(4a)) cos(y m)
#               int exp(-a(t-m)^2) sin(y t) dt = sqrt(pi/a) exp(-y^2/(4a)) sin(y m)
def cm_closed(a, m, y): return np.sqrt(np.pi / a) * np.exp(-y * y / (4 * a)) * np.cos(y * m)
def sm_closed(a, m, y): return np.sqrt(np.pi / a) * np.exp(-y * y / (4 * a)) * np.sin(y * m)

# B(t) = exp(-2t^2 + t) = exp(-2(t - 1/4)^2 + 1/8)
print("  moment controls (quadrature vs closed form):")
print(f"{'y':>6} {'cosMom A':>18} {'closed':>18} {'sinMom B':>18} {'closed':>18}")
for y in [0.0, 0.5, 1.5, 3.0]:
    ca = cosMom(A, y); ca_c = cm_closed(1.0, 1.0, y)
    sb = sinMom(B, y); sb_c = np.exp(0.125) * sm_closed(2.0, 0.25, y)
    print(f"{y:>6.2f} {ca:>18.12f} {ca_c:>18.12f} {sb:>18.12f} {sb_c:>18.12f}")
print()

# LHS: nested. inner over p on a grid, outer over v.
VL = 7.0; NV = 4000
vg = np.linspace(-VL, VL, NV + 1); hv = 2 * VL / NV
PL = 9.0; NP = 6000
pg = np.linspace(-PL, PL, NP + 1); hp = 2 * PL / NP
wp = simp_w(NP)
inner = np.empty(NV + 1)
for i, v in enumerate(vg):
    inner[i] = (hp / 3.0) * np.dot(wp, A(v + pg) * B(v - pg))

print("  the identity, and the SIGN of the second term:")
print(f"{'x':>6} {'LHS (nested quad)':>22} {'RHS with MINUS':>22} {'RHS with PLUS':>22}")
worst = 0.0
for x in [0.0, 0.7, 1.3, 2.5, 4.0]:
    lhs = simp(inner * np.cos(x * vg), hv)
    ca = cosMom(A, x / 2); sa = sinMom(A, x / 2)
    cb = cosMom(B, x / 2); sb = sinMom(B, x / 2)
    rhs_m = 0.5 * (ca * cb - sa * sb)
    rhs_p = 0.5 * (ca * cb + sa * sb)
    worst = max(worst, abs(lhs - rhs_m) / max(abs(rhs_m), 1e-300))
    print(f"{x:>6.2f} {lhs:>22.14f} {rhs_m:>22.14f} {rhs_p:>22.14f}")
print()
print(f"  worst relative error of the MINUS form = {worst:.3e}")
print("  => the identity carries a MINUS, and the overall constant is 1/2.")
print("     (the PLUS column is visibly wrong, which is the point of printing it)")

# ================================================================= PART II
print()
print("=" * 78)
print("PART II -- cosMom_Rker at the actual Riemann theta kernel")
print("=" * 78)

NMAX = 14
NN = np.arange(1, NMAX + 1, dtype=np.float64)
def Phi(t):
    """Repo kernel 4*sum_n(...), evaluated at |t| (Phi is even: riemannXiKernel_neg)."""
    t = np.abs(np.asarray(t, dtype=np.float64))
    e2 = np.exp(2 * t); out = np.zeros_like(t)
    for n in NN:
        expo = -np.pi * n * n * e2
        term = (2 * np.pi ** 2 * n ** 4 * np.exp(4.5 * t)
                - 3 * np.pi * n ** 2 * np.exp(2.5 * t))
        out += np.where(expo > -700.0, term * np.exp(np.maximum(expo, -700.0)), 0.0)
    return 4 * out

TL2 = 3.2; NT2 = 20000
tg2 = np.linspace(-TL2, TL2, NT2 + 1); ht2 = 2 * TL2 / NT2
Pg = Phi(tg2)
def c0(x):  return simp(Pg * np.cos(x * tg2), ht2)
def s1(x):  return simp(tg2 * Pg * np.sin(x * tg2), ht2)
def c2(x):  return simp(tg2 ** 2 * Pg * np.cos(x * tg2), ht2)

# R(v) = int p^2 Phi(v+p) Phi(v-p) dp   -- integrand >= 0, no cancellation
VL2 = 3.4; NV2 = 3400
vg2 = np.linspace(-VL2, VL2, NV2 + 1); hv2 = 2 * VL2 / NV2
PL2 = 6.6; NP2 = 13200
pg2 = np.linspace(-PL2, PL2, NP2 + 1); hp2 = 2 * PL2 / NP2
wp2 = simp_w(NP2)
Rv = np.empty(NV2 + 1)
for i, v in enumerate(vg2):
    Rv[i] = (hp2 / 3.0) * np.dot(wp2, pg2 ** 2 * Phi(v + pg2) * Phi(v - pg2))

print(f"  R >= 0 everywhere on the grid: {bool(np.all(Rv >= 0.0))}   min R = {Rv.min():.6e}")
print(f"  R even (max |R(v)-R(-v)|)    : {np.max(np.abs(Rv - Rv[::-1])):.3e}")
print()
print("  the identity  cosMom R (2x) = (1/4)( c0(x) c2(x) + s1(x)^2 ),")
print("  with the competing constants printed so the factor is AUDITED, not assumed:")
print(f"{'x':>6} {'cosMom R (2x)':>20} {'(1/4)(c0c2+s1^2)':>20} {'(1/2)(...)':>20} {'(1/8)(...)':>20}")
worst2 = 0.0
for x in [0.0, 0.4, 0.9, 1.6, 2.5, 4.0]:
    lhs = simp(Rv * np.cos(2 * x * vg2), hv2)
    br = c0(x) * c2(x) + s1(x) ** 2
    worst2 = max(worst2, abs(lhs - 0.25 * br) / max(abs(0.25 * br), 1e-300))
    print(f"{x:>6.2f} {lhs:>20.14f} {0.25*br:>20.14f} {0.5*br:>20.14f} {0.125*br:>20.14f}")
print()
print(f"  worst relative error of the 1/4 form = {worst2:.3e}")
print("  => the constant is 1/4.  The 1/2 and 1/8 columns are wrong by exactly 2x and 2x.")
print()
print("  CROSS-CHECK against batch 12's COMPILED momentTwo_eq:")
print("    int_{Ioi 0} u^2 C(x,u) du = (1/8)(c0 c2 + s1^2),  so  cosMom R (2x) = 2 * that.")
for x in [0.0, 0.9, 2.5]:
    lhs = simp(Rv * np.cos(2 * x * vg2), hv2)
    br = c0(x) * c2(x) + s1(x) ** 2
    print(f"    x={x:<5.2f} cosMom R (2x) = {lhs:.14f}   2*(1/8)(c0c2+s1^2) = {2*0.125*br:.14f}")
print("=" * 78)
