"""(O5)(a) A SOUND certified count, using the explicit region bound.

A step p->q of length L is sound when |Xi(p)| > L * M', with M' a bound on |Xi'| along it.
Then Xi stays inside the disc about Xi(p) of radius < |Xi(p)|, hence in an open half-plane
through 0: the argument increment is determined AND no full turn can hide inside the step.
By Cauchy, M' <= M / (R_disc - L/2) with M = xi_region_bound on a disc of radius R_disc
about the step's midpoint.  Refine until the test passes.
"""
import sys, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from certified_zeta import zeta_enclosure
from region_bounds import xi_region_bound
from mpmath import mp, mpf, mpc, fabs, re as mre, im as mim, arg as marg
mp.dps = 30

def xi_enc(z):
    z = mp.mpmathify(z); s = mpf(1)/2 + mpc(0,1)*z
    zv, zr = zeta_enclosure(s)
    A = (mpf(1)/4 + z**2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2)
    val = A*zv
    return val, fabs(A)*zr + fabs(val)*mpf(10)**(-mp.dps+3)

RD = mpf('0.18')      # disc radius for the Cauchy bound

def step_sound(p, q):
    """certified: does Xi stay in the half-plane through Xi(p) along [p,q]?"""
    L = fabs(q - p)
    if L >= 2*RD: return None, None
    mid = (p+q)/2
    M = xi_region_bound(mre(mid), RD, h=mim(mid))
    Mp = M/(RD - L/2)
    vp, rp = xi_enc(p)
    if fabs(vp) - rp > L*Mp: return True, vp
    return False, vp

def count(a, b, H, maxdepth=26):
    corners = [mpc(a,-H), mpc(b,-H), mpc(b,H), mpc(a,H), mpc(a,-H)]
    total = mpf(0); nev = 0
    for k in range(4):
        z0, z1 = corners[k], corners[k+1]
        segs = [(z0, z1, 0)]
        while segs:
            p, q, d = segs.pop()
            ok, vp = step_sound(p, q); nev += 1
            if ok:
                vq, _ = xi_enc(q); nev += 1
                total += marg(vq*mp.conj(vp))
            else:
                if d >= maxdepth: return None, nev
                m = (p+q)/2
                segs.append((m, q, d+1)); segs.append((p, m, d+1))
    return total/(2*mp.pi), nev

H = mpf('0.25')     # band half-height; H + RD = 0.43 < 1/2 as Stirling requires
print(f"band |Im z| <= {H}, Cauchy disc radius {RD}  (sum {H+RD} < 1/2)")
print(f"{'a':>8} {'b':>8} {'certified count':>18} {'evals':>8}  expected")
for a, b, exp_ in [(10,16,1), (10,23,2), (16,23,1), (10,26,3), (26,29,0), (23,26,1)]:
    N, nev = count(mpf(a), mpf(b), H)
    if N is None:
        print(f"{a:>8} {b:>8} {'UNDETERMINED':>18} {nev:>8}  {exp_}")
    else:
        got = int(mp.nint(N))
        print(f"{a:>8} {b:>8} {mp.nstr(N,8):>18} {nev:>8}  {exp_}  "
              f"{'OK' if got==exp_ else '*** MISMATCH ***'}")
