"""
Order-1 sixfold, FIXED observable (Sam's debug: wrong harmonic + no rail decomposition).
Bug in ggk_sixfold.py: M_k = |W|^2/p^k is the 2nd moment = dim End(W) (reads automorphisms,
NOT the Weil class) and averages away the collective rails.  CORRECT observable = the g-th
harmonic ^6 W / p^3 (the collective top rail), read via the count machinery's rail char poly.

Run it over the family gr = [4,5,s] (fr = [0,1,2,3] fixed), generic members, primes feasible
for k=6 (7,13,19).  A root-of-unity freeze at every prime = Weil class present (collective
freeze).  This is the corrected order-1 reading: does the ^6 W rail-freeze fire on GENERIC
simple sixfolds of a general (non-Jacobi) family?
"""
import sys, importlib.util, cmath, math
sys.path.insert(0, "/Users/samuellavery/work/helix_frobenius/tmp")
spec = importlib.util.spec_from_file_location("wsc", "/Users/samuellavery/work/helix_frobenius/tmp/weil_sixfold_count.py")
wsc = importlib.util.module_from_spec(spec); sys.modules["wsc"] = wsc
spec.loader.exec_module(wsc)   # main is guarded -> no side run

def order_of(z):
    if z is None: return None
    for o in (1, 2, 3, 4, 6, 12):
        if abs(z ** o - 1) < 1e-3:
            return o
    return None

fr = [0, 1, 2, 3]
primes = [7, 13, 19]
svals = [6, 7, 8, 9, 10, 11]      # generic simple members (distinct roots)
print("== SIXFOLD  ^6 W / p^3 rail-freeze over the family gr=[4,5,s]  (CORRECT observable) ==")
print("f=x(x-1)(x-2)(x-3); primes k=6 feasible:", primes)
print(" s    p     Weil?   ^6W/p^3            order   6 W-rail angles (arg/pi)")
for s in svals:
    gr = [4, 5, s]; hc = wsc.h_member(fr, gr); allroots = fr + gr
    for p in primes:
        if (p - 1) % 3 or len({r % p for r in allroots}) != len(allroots):
            continue
        Ts = {k: wsc.Tk(p, k, hc) for k in range(1, 7)}
        cpoly = wsc.rail_charpoly(Ts, 6)
        val = wsc.validate_rail(cpoly, p, 6)
        frz = val["freeze"]; o = order_of(frz)
        angs = sorted(round(cmath.phase(r) / math.pi, 3) for r in val["roots"]) if len(val["roots"]) else []
        fs = "%+.3f%+.3fi" % (frz.real, frz.imag) if frz is not None else "-"
        print(" %2d  %3d   %-4s  %-18s  %-5s  %s"
              % (s, p, "YES" if val["weil"] else "NO", fs, str(o), angs))
    print()
