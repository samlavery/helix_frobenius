#!/usr/bin/env python3
"""C3 batch 12 numerics, part 2 — RETRACTION AND REPAIR OF P5.

P5 in tmp/c3b12_num.py evaluated L1_c for the counterexample kernel
Phi_c(t) = e^{-t^2}(2 + cos 2t) by central finite differences with h = 1e-4 on a quantity
that decays like e^{-x^2/2}.  Its "106/401 negatives, min -1.17e-16" is ENTIRELY roundoff:
at x = 10.6 the true scale of L1_c is ~1e-25, twelve orders below the reported figure.
Same failure mode as batch 11's first hostile scan.  Redone here in closed form.

  Xi_c(x) = M_c(ix) = sqrt(pi) e^{-x^2/4} ( 2 + e^{-1} cosh x )   [exact]
  L1_c    = Xi_c'^2 - Xi_c Xi_c'' = Xi_c^2 * ( 1/2 - (log g)'' ),  g = 2 + e^{-1} cosh x
  (log g)'' = e^{-1}(2 cosh x + e^{-1}) / (2 + e^{-1} cosh x)^2      [exact, by cosh^2-sinh^2=1]
"""
import mpmath as mp

mp.mp.dps = 40
a = mp.e ** (-1)


def Xic(x):
    return mp.sqrt(mp.pi) * mp.e ** (-mp.mpf(x) ** 2 / 4) * (2 + a * mp.cosh(x))


def loggpp(x):
    c = mp.cosh(x)
    return a * (2 * c + a) / (2 + a * c) ** 2


def L1c_closed(x):
    return Xic(x) ** 2 * (mp.mpf(1) / 2 - loggpp(x))


def L1c_symbolic(x):
    """independent route: mpmath's own high-order differentiation of the closed form"""
    d1 = mp.diff(Xic, x, 1)
    d2 = mp.diff(Xic, x, 2)
    return d1 ** 2 - Xic(x) * d2


print("=" * 78)
print("P5'  the counterexample kernel Phi_c and the u^2 SUB-LEAF  L1_c(x)")
print("=" * 78)
print(f"  {'x':>8} {'L1_c (closed)':>24} {'L1_c (mp.diff)':>24} {'rel err':>10}")
for x in [0.0, 0.5, 1.0, 2.0, 3.0, 5.0, 7.0, 10.6, 15.0]:
    v1 = L1c_closed(x)
    v2 = L1c_symbolic(x)
    rel = abs(v1 - v2) / abs(v1) if v1 != 0 else abs(v1 - v2)
    print(f"  {x:8.3f} {mp.nstr(v1, 15):>24} {mp.nstr(v2, 15):>24} {float(rel):10.2e}")

neg = 0
mn = (mp.inf, None)
mnr = (mp.inf, None)
N = 2001
for i in range(N):
    x = mp.mpf(i) * 30 / (N - 1)
    v = L1c_closed(x)
    r = mp.mpf(1) / 2 - loggpp(x)          # scale-free: L1_c / Xi_c^2
    if v < 0:
        neg += 1
    if v < mn[0]:
        mn = (v, x)
    if r < mnr[0]:
        mnr = (r, x)
print()
print(f"  scanned {N} points on x in [0,30]:  negatives = {neg}")
print(f"  min L1_c        = {mp.nstr(mn[0], 10)} at x = {float(mn[1]):.4f}")
print(f"  min L1_c/Xi_c^2 = {mp.nstr(mnr[0], 10)} at x = {float(mnr[1]):.4f}   (scale-free)")
print()
print("  EXACT ARGUMENT (pencil, not numerics).  With c = cosh x >= 1 and a = 1/e,")
print("    h(c) := (log g)'' = a(2c + a)/(2 + ac)^2,")
print("    h'(c) = 2a(2 - ac - a^2)/(2 + ac)^3, so h is maximised at c* = (2 - a^2)/a,")
print("    where ac* = 2 - a^2, 2 + ac* = 4 - a^2, 2c* + a = (4 - a^2)/a, hence")
print(f"    max h = 1/(4 - a^2) = {mp.nstr(1/(4-a**2), 12)}, and 1/(4-a^2) < 1/2 iff a^2 < 2.")
print("    Since a = 1/e < 1 this holds, so L1_c = Xi_c^2 (1/2 - h) > 0 for EVERY real x.")
print(f"    CHECK against the scan above: 1/2 - 1/(4-a^2) = {mp.nstr(mp.mpf(1)/2 - 1/(4-a**2), 10)}")
print("    (An earlier draft of this file said the max was at c = 1, value a/(2+a).")
print("     That was wrong; h increases to c* first.  The conclusion is unchanged.)")
print()
print("  CONSEQUENCE, and it is the batch's most useful negative-turned-positive:")
print("  Phi_c REFUTES the full four-moment leaf (batch 11 F1) but SATISFIES the u^2")
print("  sub-leaf.  The sub-leaf is therefore STRICTLY WEAKER, and the batch-11")
print("  counterexample does NOT obstruct an unconditional proof of it.")
print()
print("=" * 78)
print("P6  the same question for the two-Gaussian kernel Phi_g = e^{-t^2} + e^{-4t^2}")
print("    M_g(z) = sqrt(pi) e^{z^2/4} + (sqrt(pi)/2) e^{z^2/16};  Xi_g(x) = M_g(ix)")
print("=" * 78)


def Xig(x):
    return mp.sqrt(mp.pi) * mp.e ** (-mp.mpf(x) ** 2 / 4) \
        + mp.sqrt(mp.pi) / 2 * mp.e ** (-mp.mpf(x) ** 2 / 16)


def L1g(x):
    d1 = mp.diff(Xig, x, 1)
    d2 = mp.diff(Xig, x, 2)
    return d1 ** 2 - Xig(x) * d2


negg = 0
mng = (mp.inf, None)
for i in range(1201):
    x = mp.mpf(i) * 30 / 1200
    v = L1g(x)
    if v < 0:
        negg += 1
    if v < mng[0]:
        mng = (v, x)
print(f"  scanned 1201 points on [0,30]: negatives = {negg};"
      f"  min L1_g = {mp.nstr(mng[0], 10)} at x = {float(mng[1]):.4f}")
print("  Xi_g > 0 everywhere (a positive mixture of two Gaussians), so Phi_g has no real")
print("  zeros -- yet it VIOLATES the u^2 sub-leaf.  So the two counterexample kernels")
print("  SEPARATE the two statements:")
print("     Phi_c : violates the FULL leaf,  satisfies the u^2 sub-leaf")
print("     Phi_g : violates the FULL leaf,  violates  the u^2 sub-leaf")
print("  Consequences, both load-bearing: (1) the sub-leaf is STRICTLY WEAKER than the")
print("  full leaf, so batch 11's Phi_c counterexample does NOT obstruct proving it;")
print("  (2) the sub-leaf is nevertheless NOT implied by evenness + positivity alone,")
print("  since Phi_g is even and positive and fails it.  Any proof of the sub-leaf must")
print("  use a property of Phi_Xi beyond positivity.")
