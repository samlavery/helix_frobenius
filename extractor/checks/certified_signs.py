"""(O1) CERTIFIED sign evaluations for the product theorem's hypotheses.

The product theorem needs: Xi(a), Xi(b) != 0, and a sign change u(c)u(d) < 0.  The sign of
the readout equals the sign of Hardy's Z, since u = |w| |Gamma_R| Z with both factors > 0.
Z(t) = e^{i theta(t)} zeta(1/2+it), theta = arg Gamma_R(1/2+it), and Z is real.

Certified: |Z_computed - Z_true| <= rad_zeta + |zeta| * (theta rounding).  If |Z| exceeds
that radius, the SIGN IS PROVED (under the stated arithmetic model).
"""
import sys, math
import os
_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(_here))
from certified_zeta import zeta_enclosure
from mpmath import mp, mpf, mpc, fabs, re as mre, im as mim
from helix_extractor import Bank, Clocks, calibrate, height
mp.dps = 60

def theta(t):
    """arg Gamma_R(1/2+it), continuous branch, via loggamma."""
    t = mpf(t)
    return mim(mp.loggamma(mpf(1)/4 + mpc(0,1)*t/2)) - (t/2)*mp.log(mp.pi)

def Z_enclosure(t):
    s = mpf(1)/2 + mpc(0,1)*mpf(t)
    zv, zr = zeta_enclosure(s)
    th = theta(t)
    rot = mp.exp(mpc(0,1)*th)
    Z = mre(rot*zv)
    # theta carries relative rounding ~10^{-dps}; it moves Z by at most |zeta|*|dtheta|
    dth = fabs(th)*mpf(10)**(-mp.dps) + mpf(10)**(-mp.dps)
    rad = zr + fabs(zv)*dth
    return Z, rad

bank  = Bank(delta=math.pi/3, tol=1e-16)
cbank = Bank(delta=math.pi/3, tol=1e-6)
clocks = Clocks(100); anchor = calibrate(bank, clocks)

print(f"{'i':>6} {'point':>6} {'|Z|':>14} {'radius':>14} {'margin=|Z|/rad':>16}  sign")
allok = True
for i in (1, 10, 100, 1000, 10000):
    r0 = height(i, bank, cbank, clocks, anchor, mm=9)
    pts = [('a', r0['a']), ('b', r0['b']), ('c', r0['lo']), ('d', r0['hi'])]
    Zs = {}
    for name, t in pts:
        Z, rad = Z_enclosure(t)
        ok = fabs(Z) > rad
        allok &= bool(ok)
        Zs[name] = Z
        print(f"{i:>6} {name:>6} {mp.nstr(fabs(Z),6):>14} {mp.nstr(rad,6):>14} "
              f"{mp.nstr(fabs(Z)/rad,6):>16}  {'PROVED '+('+' if Z>0 else '-') if ok else 'UNDECIDED'}")
    sc = Zs['c']*Zs['d'] < 0
    print(f"{'':>6} {'->':>6} sign change on [c,d]: {'PROVED' if sc else 'NO'}"
          f"   endpoints nonzero: {'PROVED' if fabs(Zs['a'])>0 and fabs(Zs['b'])>0 else '?'}")
print()
print("ALL SIGN HYPOTHESES CERTIFIED:" , allok)
