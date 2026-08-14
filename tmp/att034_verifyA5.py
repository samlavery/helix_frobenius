#!/usr/bin/env python3
"""
att034_verifyA5.py -- headline reproduction with the SOUND boundary convention.

RESOLUTION of my own earlier disagreement: the atom that lands exactly on alpha = 1
must be forced <= 0 and NOT credited in the objective ('outside').  Reason: in the
continuum rhat is continuous and rhat <= 0 on (1,S] forces rhat(1) <= 0; a scheme that
exempts the boundary cell lets rhat be POSITIVE on (1, 1+Delta/2), where only F >= 0
is known, so the discarded piece int_{|a|>1} F rhat is no longer <= 0 -- inadmissible.
'outside' is conservative (it throws away a nonpositive contribution), hence SOUND.

NULLS: (a) Z(0,S=2) = 1.321172;  (b) Z(0.5,S=2) = 1.350256;  (c) A* = 0.208;
       (d) convergence at S=2 is order 2 so Richardson-2 is legitimate.
"""
import sys, time
import numpy as np
from scipy.optimize import brentq
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att034_verifyA4 import solve, MT

def rich(v1, d1, v2, d2, o=2.0):
    r = (d1/d2)**o
    return (r*v2 - v1)/(r - 1.0)

print("Montgomery-Taylor target 1/c*_1 = %.10f" % MT)

print("\n" + "="*82)
print("O1  convergence ORDER at S=2, A=0, sound convention")
print("="*82)
vals = []
for D in [0.08, 0.04, 0.02, 0.01]:
    t = time.time(); v, cv, x, st = solve(2.0, 0.0, D, bmode='outside')
    vals.append((D, v)); print("  Delta=%.4f  Z=%.8f  [%s]  %.0fs" % (D, v, st, time.time()-t))
for i in range(len(vals)-2):
    d1 = vals[i+1][1]-vals[i][1]; d2 = vals[i+2][1]-vals[i+1][1]
    print("    incr %.3e -> %.3e   ratio %.3f  => order %.3f" % (d1, d2, d1/d2, np.log2(abs(d1/d2))))
print("  Richardson2(.04,.02) = %.7f   (reported 1.321172)" % rich(vals[1][1], .04, vals[2][1], .02))
print("  Richardson2(.02,.01) = %.7f" % rich(vals[2][1], .02, vals[3][1], .01))

print("\n" + "="*82)
print("O2  Z(A) sweep at S=2, sound convention, Delta = 0.04 / 0.02 + Richardson2")
print("="*82)
ZA = {}
for A in [0.0, 0.05, 0.1, 0.15, 0.2, 0.208, 0.25, 0.3, 0.4, 0.5, 0.75, 1.0]:
    r = []
    for D in [0.04, 0.02]:
        v, cv, x, st = solve(2.0, A, D, bmode='outside')
        r.append(v if v is not None else np.nan)
    z = rich(r[0], .04, r[1], .02)
    ZA[A] = z
    print("  A=%-6.3f  Z(.04)=%.7f  Z(.02)=%.7f  Rich=%.7f   2-Z=%.7f" % (A, r[0], r[1], z, 2-z))

ks = sorted(ZA); zs = [ZA[k] for k in ks]
Astar = brentq(lambda a: np.interp(a, ks, zs) - MT, 0.0, 0.5)
print("\n  crossing A* with Z(A)=%.7f :  A* = %.4f   (reported 0.2080)" % (MT, Astar))
print("  prize at A=0 : 2 - Z(0) - 0.6725007 = %.7f" % (2 - ZA[0.0] - (2-MT)))

print("\n" + "="*82)
print("O3  band sweep at A=0 (is S=2 saturated?  CGdL publish 1.3208)")
print("="*82)
for S in [1.0, 1.25, 1.5, 2.0, 3.0]:
    r = []
    for D in [0.04, 0.02]:
        v, cv, x, st = solve(S, 0.0, D, bmode='outside')
        r.append(v if v is not None else np.nan)
    print("  S=%.2f  Z(.04)=%.7f  Z(.02)=%.7f  Rich=%.7f  2-Z=%.7f"
          % (S, r[0], r[1], rich(r[0], .04, r[1], .02), 2-rich(r[0], .04, r[1], .02)))

print("\n" + "="*82)
print("O4  Tsang-class check at A=0.5, S=1 (BGSTB feasible pts: Fejer 1.3913871, MT 1.3825162)")
print("="*82)
r = []
for D in [0.04, 0.02, 0.01]:
    v, cv, x, st = solve(1.0, 0.5, D, bmode='outside')
    r.append((D, v)); print("  Delta=%.3f  Z=%.7f [%s]" % (D, v, st))
print("  Richardson2 -> %.7f   (reported whole-class optimum 1.382229)"
      % rich(r[-2][1], r[-2][0], r[-1][1], r[-1][0]))
