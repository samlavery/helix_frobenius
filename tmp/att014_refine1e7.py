"""ATTEMPT 014 -- census repair at T=1e7: the dsig=0.08/dt=0.4 seed lattice was too coarse at
that height (winding certificates showed Newton missing ~1-3%).  Re-run with dsig=0.06/dt=0.22
and re-certify.  NULL for the repair: the count does NOT move toward the winding certificate."""
import numpy as np, math, sys, time, os
from att014_afe import theta
from att014_zprime_roots import newton_zprime, dedupe, winding_zprime

def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi
T, cache = 1e7, "att010_zeros_1e+07.npy"
g = np.load(cache); t0, t1 = float(g[0]), float(g[-1]); tc = (t0+t1)/2
L = math.log(tc/TWOPI); rho = math.log(tc/(4*math.pi))/L
mids = (g[:-1]+g[1:])/2
seeds = [0.5+off + 1j*mids for off in (0.3/L, 0.8/L, 1.6/L, 3.0/L, 6.0/L)]
sg = np.arange(0.52, 3.0, 0.06); tg = np.arange(t0, t1, 0.22)
S, TT = np.meshgrid(sg, tg); seeds.append((S + 1j*TT).ravel())
seeds = np.concatenate(seeds)
t_ = time.time()
r = dedupe(newton_zprime(seeds, t0, t1)); r = r[(r.imag >= t0) & (r.imag <= t1)]
P(f"T=1e7  seeds {len(seeds)} -> {len(r)} zeta' zeros  ({time.time()-t_:.0f}s)")
np.save("att014_zpz_1e+07.npy", r)
u = theta(np.sort(r.imag))/np.pi; U = u[-1]-u[0]
P(f"  n/U = {len(r)/U:.5f}   predicted rho = {rho:.5f}   [NULL 1.0]   Berndt count "
  f"{(t1-t0)/TWOPI*math.log(tc/(4*math.pi)):.1f}")
for (tA, tB) in ((t0+50, t0+250), (tc-100, tc+100), (t1-250, t1-50)):
    w, mx = winding_zprime(0.30, 3.60, tA, tB, 0.01, 0.001)
    P(f"  winding t({tA:.0f},{tB:.0f}): {w:.3f}   Newton {int(((r.imag>tA)&(r.imag<tB)).sum())}")
