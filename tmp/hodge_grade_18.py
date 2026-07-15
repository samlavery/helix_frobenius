"""
Extend the grade ladder through m=18 (two full period-4 cycles).
Tests, per Sam's corrected forecast:
  (i)  sign law eps(psi^m): m=13..18 predicted  + + - - + +   (hidden grades 15,16;
       eps_17=eps_18=+1 closes two cycles).  Period-4: m=1,2 mod4 -> +1 ; m=3,0 mod4 -> -1
       (with the single m=2 exception).
  (ii) magnitude law in COMPLETED space: Lambda'_m(1/2) ~ 0.14 (level, geomean of m=2,3,4),
       so raw  L'_m(1/2) ~ 0.14 / G_m(1/2)  -- NOT the factorial recurrence.
       Decisive sub-test: G_m(1/2) is non-monotone (min near m~12, then rises), so the
       raw derivative at 15,16 should be ~O(10), not ~1e10.
Prints G_m(1/2) for all m=7..18 (cheap), and eps / L / (if hidden) L', Lambda', 0.14/G_m.
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
LEVEL = 0.14  # geomean of completed Lambda'(1/2) at m=2,3,4

def Ghalf(m):
    G = cl.make_G(49, [('C', m / 2.0)])
    return float(complex(G(mp.mpf("0.5"))).real)

print("== G_m(1/2) shape, m=7..18 (archimedean carrier factor; watch for the turnaround) ==")
for m in range(7, 19):
    print("  m=%2d  arg=%.1f  G(1/2)=%.6f   0.14/G=%.4f" % (m, 0.5 + m / 2.0, Ghalf(m), LEVEL / Ghalf(m)))

print("\n== signs + derivatives, m=13..18 ==")
print(" m   eps  (res)      L(1/2)       L'(1/2)      Lambda'      0.14/G_m    ratio")
signs = {}
for m in range(13, 19):
    nmax = 5000 + 2000 * m
    _, lam = cl.bank_hecke_unitary(m, nmax)
    G = cl.make_G(49, [('C', m / 2.0)])
    e, r, _ = cl.certify(G, lam, 2.5)
    signs[m] = e
    L = cl.central_value(G, lam, e).real
    Gh = float(complex(G(mp.mpf("0.5"))).real)
    if e < 0 and abs(L) < 1e-2:
        Ld = cl.central_deriv(G, lam, e).real
        Lam = Gh * Ld
        pred = LEVEL / Gh
        print(" %2d   %+d  %.1e  %+.4e  %9.4f   %9.6f   %9.4f  %.3f"
              % (m, e, r, L, Ld, Lam, pred, Ld / pred))
    else:
        print(" %2d   %+d  %.1e  %+.4e     (no forced fire)" % (m, e, r, L))

print("\n-- verdicts --")
seq = "".join("+" if signs[m] > 0 else "-" for m in range(13, 19))
print("  measured eps(psi^m), m=13..18:  %s   (period-4 predicts: ++--++)" % seq)
print("  eps_17=%+d, eps_18=%+d   (two-cycle close predicts +1,+1)" % (signs[17], signs[18]))
print("  hidden-cycle grades in 13..18 (eps=-1): %s   (predicts [15,16])"
      % [m for m in range(13, 19) if signs[m] < 0])
