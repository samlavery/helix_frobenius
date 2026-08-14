#!/usr/bin/env python3
"""
att034_verifyA6.py -- robust headline sweep (CLARABEL with SCS fallback).
"""
import sys, time
import numpy as np
from scipy.optimize import brentq
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att034_verifyA4 import solve, MT

def rsolve(S, A, D, bmode='outside'):
    for sv in ['CLARABEL', 'SCS']:
        v, cv, x, st = solve(S, A, D, bmode=bmode, solver=sv)
        if v is not None and np.isfinite(v):
            return v, st + "/" + sv
    return np.nan, "FAIL"

def rich(v1, d1, v2, d2, o=2.0):
    r = (d1/d2)**o
    return (r*v2 - v1)/(r - 1.0)

print("MT target %.10f" % MT)
print("\n" + "="*84)
print("O1  S=2, A=0, both conventions, Delta ladder")
print("="*84)
tab = {}
for bm in ['outside', 'inside']:
    row = []
    for D in [0.08, 0.05, 0.04, 0.025, 0.02, 0.0125, 0.01]:
        t = time.time(); v, st = rsolve(2.0, 0.0, D, bm)
        row.append((D, v))
        print("  %-8s Delta=%.4f  Z=%.8f  [%s] %.0fs" % (bm, D, v, st, time.time()-t))
    tab[bm] = row
    print("    Rich1(.02,.01)=%.7f  Rich2(.02,.01)=%.7f  Rich1(.04,.02)=%.7f  Rich2(.04,.02)=%.7f"
          % (rich(row[4][1], .02, row[6][1], .01, 1.0), rich(row[4][1], .02, row[6][1], .01, 2.0),
             rich(row[2][1], .04, row[4][1], .02, 1.0), rich(row[2][1], .04, row[4][1], .02, 2.0)))

print("\n" + "="*84)
print("O2  Z(A) sweep, S=2, SOUND convention, Delta=0.04/0.02, Richardson2")
print("="*84)
ZA = {}
for A in [0.0, 0.05, 0.1, 0.15, 0.2, 0.208, 0.25, 0.3, 0.4, 0.5, 0.75, 1.0]:
    r = [rsolve(2.0, A, D)[0] for D in (0.04, 0.02)]
    z = rich(r[0], .04, r[1], .02)
    ZA[A] = z
    print("  A=%-6.3f  Z(.04)=%.7f  Z(.02)=%.7f  Rich2=%.7f  Rich1=%.7f  2-Rich2=%.7f"
          % (A, r[0], r[1], z, rich(r[0], .04, r[1], .02, 1.0), 2-z))
ks = sorted(ZA); zs = [ZA[k] for k in ks]
Astar = brentq(lambda a: np.interp(a, ks, zs) - MT, 0.0, 0.5)
print("\n  A* (Z(A)=MT) = %.4f   [reported 0.2080 / implA 0.216 / implB 0.213]" % Astar)
print("  prize 2-Z(0)-0.6725007 = %.7f   [reported 0.0063273]" % (2-ZA[0.0]-(2-MT)))
print("  2-Z(0.5) = %.6f  [reported byproduct 0.649744]" % (2-ZA[0.5]))

print("\n" + "="*84)
print("O3  band sweep at A=0 (CGdL publish 1.3208)")
print("="*84)
for S in [1.0, 1.25, 1.5, 2.0, 3.0]:
    r = [rsolve(S, 0.0, D)[0] for D in (0.04, 0.02)]
    print("  S=%.2f  Z(.04)=%.7f  Z(.02)=%.7f  Rich2=%.7f  2-Z=%.7f"
          % (S, r[0], r[1], rich(r[0], .04, r[1], .02), 2-rich(r[0], .04, r[1], .02)))

print("\n" + "="*84)
print("O4  Tsang class at A=0.5, S=1 (BGSTB feasible: Fejer 1.3913871, MT 1.3825162)")
print("="*84)
r = []
for D in [0.04, 0.02, 0.01]:
    v, st = rsolve(1.0, 0.5, D)
    r.append((D, v)); print("  Delta=%.3f  Z=%.7f [%s]" % (D, v, st))
print("  Rich2 -> %.7f  [reported whole-class optimum 1.382229]"
      % rich(r[-2][1], r[-2][0], r[-1][1], r[-1][0]))
