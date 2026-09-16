"""Validate (O5): is xi_region_bound a genuine UPPER bound, and how loose?"""
import sys, math
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from region_bounds import xi_region_bound, zeta_region_bound
from mpmath import mp, mpf, mpc, fabs
mp.dps = 40

def xi(z):
    z = mp.mpmathify(z); s = mpf(1)/2 + mpc(0,1)*z
    return (mpf(1)/4 + z**2) * mp.power(mp.pi, -s/2) * mp.gamma(s/2) * mp.zeta(s)

print(f"{'m':>9} {'r':>7} {'M (bound)':>14} {'max|Xi| sampled':>18} {'M/max':>10}  valid")
for m, r in [(14.1347,0.1),(14.1347,0.4),(20.0,0.25),(49.77,0.2),
             (236.52,0.1),(236.52,0.4),(1419.42,0.1)]:
    M = xi_region_bound(m, r)
    obs = mpf(0)
    for k in range(200):
        z = mpf(m) + mpf(r)*mp.exp(mpc(0,1)*2*mp.pi*k/200)
        obs = max(obs, fabs(xi(z)))
    for k in range(40):           # interior too
        for j in range(8):
            z = mpf(m) + mpf(r)*mpf(k)/40*mp.exp(mpc(0,1)*2*mp.pi*j/8)
            obs = max(obs, fabs(xi(z)))
    ok = M >= obs
    print(f"{m:>9.4f} {r:>7.2f} {mp.nstr(M,6):>14} {mp.nstr(obs,6):>18} "
          f"{mp.nstr(M/obs,5):>10}  {'YES' if ok else '*** NO ***'}")
