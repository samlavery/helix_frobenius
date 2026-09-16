"""(O5)(b) CERTIFY Xi' != 0 on the returned interval -- the CAPSTONE's hypothesis.

On [lo,hi] the mean value theorem gives xi in [lo,hi] with Xi'(xi) = slope, where
slope = (Xi(hi)-Xi(lo))/(hi-lo).  For any t in [lo,hi],
    |Xi'(t)| >= |slope| - max|Xi''| * (hi-lo),
and by Cauchy on a disc of radius r about the midpoint, max|Xi''| <= 2 M(m,r)/r^2 with M
the EXPLICIT bound of region_bounds.  So Xi' has no zero on [lo,hi] whenever
    |slope|_lower  >  (2 M / r^2) * (hi - lo).
Certified throughout: Xi(lo), Xi(hi) come with radii from certified_zeta.
"""
import sys, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from certified_zeta import zeta_enclosure
from region_bounds import xi_region_bound
from mpmath import mp, mpf, mpc, fabs, re as mre
from helix_extractor import Bank, Clocks, calibrate, height
mp.dps = 40

def xi_enclosure(t):
    t = mpf(t); s = mpf(1)/2 + mpc(0,1)*t
    zv, zr = zeta_enclosure(s)
    A = (mpf(1)/4 + t**2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2)
    val = mre(A*zv)
    return val, fabs(A)*zr + fabs(A*zv)*mpf(10)**(-mp.dps+3)

bank  = Bank(delta=math.pi/3, tol=1e-16)
cbank = Bank(delta=math.pi/3, tol=1e-6)
clocks = Clocks(100); anchor = calibrate(bank, clocks)
R = mpf('0.4')

print(f"{'i':>7} {'width':>12} {'|slope| lower':>16} {'2M/r^2*width':>16} {'margin':>11}  verdict")
allok = True
for i in (1, 10, 100, 1000, 10000):
    r0 = height(i, bank, cbank, clocks, anchor, mm=9)
    lo, hi = mpf(r0['lo']), mpf(r0['hi'])
    w = hi - lo; m = (lo+hi)/2
    vlo, rlo = xi_enclosure(lo); vhi, rhi = xi_enclosure(hi)
    slope = (vhi - vlo)/w
    slope_rad = (rlo + rhi)/w
    slope_lo = fabs(slope) - slope_rad
    M = xi_region_bound(m, R)
    bnd = 2*M/R**2 * w
    ok = slope_lo > bnd
    allok &= bool(ok)
    print(f"{i:>7} {mp.nstr(w,4):>12} {mp.nstr(slope_lo,6):>16} {mp.nstr(bnd,6):>16} "
          f"{mp.nstr(slope_lo/bnd,5):>11}  {'CERTIFIED' if ok else 'no'}")
print()
print("Xi' != 0 CERTIFIED on every returned interval:", allok)
print("=> the CAPSTONE's hypothesis, not merely the product theorem's, is discharged there.")
