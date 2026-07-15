"""
Close order 1: the no-orphan OCCUPANCY on the GENERAL (non-Jacobi) sixfold family y^3=f g^2.
weil_rails proved it on the Jacobi family (22 = 20 div + 2 coll + 0 orphan) and argued it
analytically for the whole cyclic-cover family (collective rail always freezes, ord|m).  Here we
VERIFY on the general family: feed the general sixfold's char-poly eigenvalue ANGLES into
weil_rails.no_orphan_decomposition and confirm ORPHAN = 0.
"""
import sys, importlib.util, math, cmath
import numpy as np
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
def load(mod, path):
    spec = importlib.util.spec_from_file_location(mod, path)
    m = importlib.util.module_from_spec(spec); sys.modules[mod] = m
    try: spec.loader.exec_module(m)
    except SystemExit: pass
    return m
wsc = load("wsc", "/Users/samuellavery/work/helix_frobenius/tmp/weil_sixfold_count.py")
wr  = load("wr",  "/Users/samuellavery/work/helix_frobenius/tmp/weil_rails.py")

fr, gr = [0,1,2,3], [4,5,6]                 # order-1 general sixfold, g=6, (3,3)
hc = wsc.h_member(fr, gr); allroots = fr + gr
primes = [7, 13, 19]
rows = []
kept = []
for p in primes:
    if (p-1) % 3 or len({r % p for r in allroots}) != len(allroots): continue
    Ts = {k: wsc.Tk(p, k, hc) for k in range(1, 7)}
    cpoly = wsc.rail_charpoly(Ts, 6)
    val = wsc.validate_rail(cpoly, 6 if False else p, 6)
    if not val["weil"]:
        print("p=%d: not Weil (skip)" % p); continue
    angs = sorted(cmath.phase(r) for r in val["roots"])       # 6 eigenvalue angles
    rows.append(angs); kept.append(p)
    print("p=%2d  freeze det/p^3 = %s   angles/pi = %s"
          % (p, ("%.3f%+.3fi" % (val['freeze'].real, val['freeze'].imag)),
             [round(a/math.pi, 3) for a in angs]))

PH = np.array(rows)                                            # (n_primes, 6)
print("\nPH shape:", PH.shape, " primes:", kept)
occ, ndiv, ncoll1, ncollhi, hiord = wr.no_orphan_decomposition(PH, m_max=6)
print("\n== NO-ORPHAN OCCUPANCY, general family y^3=f g^2 ==")
print("  occupancy = %d  =  divisor rails %d + collective(order1) %d   (+ collective order>1: %d, ord %s)"
      % (occ, ndiv, ncoll1, ncollhi, hiord))
print("  ORPHAN = occupancy - (divisor + collective) = %d" % (occ - ndiv - ncoll1))
print("  Jacobi-family reference (weil_rails S1): 22 = 20 + 2 + 0")
print("  => order 1 %s on the general family" % ("CLOSED (no orphan)" if (occ - ndiv - ncoll1)==0 else "ORPHAN FOUND"))
