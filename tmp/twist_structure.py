"""
d=17 confirmed genuine (not artifact).  Find the ALTERNATING STRUCTURE: the true twist-sign law
of the Ceresa channel that the naive -sign(d) misses at 17.  Compute eps(f (x) chi_d) via certify
for a range of fundamental discriminants d coprime to 7, tabulate with candidate correlates, and
read off which character/structure governs the fire/no-fire alternation.
"""
import importlib.util, sys, math
import numpy as np
from mpmath import mp
spec = importlib.util.spec_from_file_location("cl", "/Users/samuellavery/work/helix_frobenius/tmp/ceresa_lside.py")
cl = importlib.util.module_from_spec(spec); sys.modules["cl"] = cl
try: spec.loader.exec_module(cl)
except SystemExit: pass
mp.dps = 30
exec(open("/Users/samuellavery/work/helix_frobenius/tmp/nofire_fire.py").read().split("m = 3")[0])

def is_fundamental(d):
    if d == 1: return False
    if d % 4 == 1: return all(d % (p*p) for p in range(2, int(abs(d)**0.5)+1))   # squarefree
    if d % 4 == 0:
        m = d // 4
        return (m % 4 in (2, 3)) and all(m % (p*p) for p in range(2, int(abs(m)**0.5)+1))
    return False

DISCS = [d for d in range(-40, 40) if d != 0 and is_fundamental(d) and d % 7 != 0 and d != -7][:24]
print("== twist-sign structure of the Ceresa channel psi^3 / Q(sqrt-7) ==")
print("  d   eps  |  -sign(d)  chi_-7(d)  (d/7)  d%8  match(-sgn)  correlate?")
rows = []
for d in DISCS:
    nmax = 1500 + 600*abs(d)
    _, lam0 = cl.bank_hecke_unitary(3, nmax)
    lam = lam0 * chi_d_arr(d, nmax)
    G = cl.make_G(49*d*d, [('C', 1.5)])
    eps, r, ro = cl.certify(G, lam, 2.5)
    naive = -1 if d > 0 else 1
    chi7 = kronecker(-7, d)                 # chi_{-7}(d)
    d7 = kronecker(d, 7)                     # (d/7)
    rows.append((d, eps, naive, chi7, d7, d % 8, r))
    print("  %+3d  %+d  |   %+d       %+d       %+d    %d    %-5s      "
          % (d, eps, naive, chi7, d7, d % 8, "yes" if eps == naive else "NO"))

print("\n-- pattern hunt: eps(d) vs candidate characters --")
def score(f):
    return sum(1 for (d, eps, na, c7, d7, d8, r) in rows if eps == f(d, eps, na, c7, d7, d8))
print("  eps == -sign(d)                 : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: na), len(rows)))
print("  eps == -sign(d)*chi_-7(d)        : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: na*c7), len(rows)))
print("  eps == -sign(d)*(d/7)            : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: na*d7), len(rows)))
print("  eps == -sign(d)*chi_-7(d)*(d/7)  : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: na*c7*d7), len(rows)))
print("  eps == chi_-7(d)                 : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: c7), len(rows)))
print("  eps == -(d/7)                    : %d/%d" % (score(lambda d,eps,na,c7,d7,d8: -d7), len(rows)))
# print the mismatches of the naive law for inspection
miss = [(d, eps) for (d, eps, na, c7, d7, d8, r) in rows if eps != na]
print("  naive -sign(d) MISSES at d =", miss)
