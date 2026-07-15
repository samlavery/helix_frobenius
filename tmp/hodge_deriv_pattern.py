"""
What is the pattern of the central derivatives 0.650 -> 0.830 -> 1.804
(the eps=-1 grades m=2,3,4 of psi^m / K=Q(sqrt-7))?

Hypothesis to test: the RAW growth is the CARRIER SCALING -- each grade sits on a
different harmonic (its archimedean Gamma-factor), so L'(1/2) is inflated by 1/G(1/2)
as the grade climbs.  Divide the carrier scaling out (look at the COMPLETED derivative
Lambda'(1/2) = G(1/2) L'(1/2)) and the true arithmetic regulator sequence is exposed.
Print raw, completed, and several normalizations; eyeball for the clean law.
Also: confirm the sign law period by reading eps for m=7..12 (certify only).
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try:
    spec.loader.exec_module(cl)
except SystemExit:
    pass

mp.dps = 30
print("== derivative pattern: eps=-1 grades m=2,3,4 (high precision) ==")
print(" m  wt   L'(1/2)     G(1/2)     Lambda'(1/2)   GammaC(1/2+m/2)   L'*(2pi)^((m+1)/2)")
rows = []
for m in [2, 3, 4]:
    nmax = 4000 + 1600 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    G = cl.make_G(49, [('C', m / 2.0)])
    e, r, _ = cl.certify(G, lam, 2.5)
    Ld = cl.central_deriv(G, lam, e).real
    Ghalf = float(complex(G(mp.mpf("0.5"))).real)
    Lamd = Ghalf * Ld
    # pure archimedean GammaC at center for this grade
    sh = m / 2.0
    gammaC = float(2 * (2 * math.pi) ** (-(0.5 + sh)) * math.gamma(0.5 + sh))
    twopi_scaled = Ld * (2 * math.pi) ** ((m + 1) / 2.0)
    rows.append((m, Ld, Ghalf, Lamd, gammaC))
    print(" %d   %d  %9.5f  %9.6f  %11.6f   %11.6f     %9.5f"
          % (m, m + 1, Ld, Ghalf, Lamd, gammaC, twopi_scaled))

print("\n-- ratios up the grades --")
for i in range(1, len(rows)):
    m0, Ld0, Gh0, Ld0c, gc0 = rows[i - 1]
    m1, Ld1, Gh1, Ld1c, gc1 = rows[i]
    print("  m=%d->%d :  L'ratio=%.4f   Lambda'ratio=%.4f   G(1/2)ratio=%.4f   GammaCratio=%.4f"
          % (m0, m1, Ld1 / Ld0, Ld1c / Ld0c, Gh1 / Gh0, gc1 / gc0))
    print("            compare: sqrt2=%.4f sqrt3=%.4f 2=%.1f e=%.4f pi/2=%.4f"
          % (math.sqrt(2), math.sqrt(3), 2.0, math.e, math.pi / 2))

print("\n-- completed regulator sequence Lambda'(1/2), normalized to grade 2 --")
base = rows[0][3]
for (m, Ld, Gh, Lamd, gc) in rows:
    print("  m=%d :  Lambda'=%.6f   /base=%.5f   *2^(m-2)=%.5f   *(m-1)!=%.5f"
          % (m, Lamd, Lamd / base, Lamd * 2 ** (m - 2), Lamd * math.factorial(m - 1)))

print("\n== sign law period check: eps(psi^m), m=7..12 (certify only) ==")
for m in range(7, 13):
    nmax = 1500 + 700 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    G = cl.make_G(49, [('C', m / 2.0)])
    e, r, _ = cl.certify(G, lam, 2.5)
    print("  m=%2d  wt=%2d  eps=%+d   (match residual %.2e)" % (m, m + 1, e, r))
