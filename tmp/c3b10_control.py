#!/usr/bin/env python3
"""POSITIVE CONTROL on C3B10.cellDensity_Ioi_eq (compiled, exit 0):
      int_{(0,inf)} C(x,u) du  =  (1/4)( cosMom(Phi,x)^2 + sinMom(Phi,x)^2 ).
Phi is even so sinMom = 0 and the right side is Xi(x)^2/4 with Xi(x)=int_R Phi(t)cos(xt)dt.
A violation would mean the Lean statement does not mean what it is claimed to mean.
NONRIG (adaptive quadrature, no interval arithmetic).  Numerics may falsify only."""
import sys
from mpmath import mp, mpf, pi, exp, cos, quad, inf, nstr
mp.dps = 25

def Phi(t):
    s = mpf(0)
    for n in range(1, 12):
        r = mpf(n)
        s += (2*pi**2*r**4*exp(mpf(9)*t/2) - 3*pi*r**2*exp(mpf(5)*t/2))*exp(-pi*r**2*exp(2*t))
    return 4*s

def Xi(x):
    return 2*quad(lambda t: Phi(t)*cos(x*t), [0, 0.5, 1, 2, 4])

def C(x, u):
    return quad(lambda p: Phi(u+p)*Phi(u-p)*cos(2*x*p), [-4, -1, 0, 1, 4])

def IC(x):
    return quad(lambda u: C(x, u), [0, 0.5, 1, 2, 4])

print("="*90)
print("CONTROL on C3B10.cellDensity_Ioi_eq :  int_{(0,inf)} C(x,u)du  vs  Xi(x)^2/4")
print("="*90)
worst = mpf(0)
for xv in [0, 1, 10, 14.134725, 21.022, 25, 30]:
    x = mpf(xv)
    lhs, rhs = IC(x), Xi(x)**2/4
    den = max(abs(lhs), abs(rhs), mpf('1e-30'))
    rel = abs(lhs-rhs)/den
    worst = max(worst, rel)
    print(f"  x={str(xv):>11}  LHS={nstr(lhs,12):>16}  Xi^2/4={nstr(rhs,12):>16}  rel={nstr(rel,4)}")
    sys.stdout.flush()
print(f"\n  worst relative discrepancy: {nstr(worst,4)}")
print("  (x=14.134725 and 21.022 are zeta zero ordinates: Xi ~ 0, so both sides ~ 0)")
