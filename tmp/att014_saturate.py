"""ATTEMPT 014 -- seeding saturation test on a winding-certified sub-box.
The argument principle gives the EXACT number of zeta' zeros in the box; densify the Newton
seed set until the found count equals it.  Also: mpmath refinement of a random sample, and a
check on every apparent beta' < 1/2 (which, if real, would refute RH -- so it must be checked).
"""
import numpy as np, math, sys, time
import mpmath as mp
from att014_afe import zeta_afe
from att014_zprime_roots import newton_zprime, dedupe, winding_zprime

def P(*a): print(*a); sys.stdout.flush()
TWOPI = 2*math.pi

def seed_set(tA, tB, mids, Lc, dsig, dt, sig_hi=3.0):
    seeds = [0.5+off + 1j*mids for off in (0.4/Lc, 1.2/Lc, 3.0/Lc, 7.0/Lc)]
    sg = np.arange(0.52, sig_hi, dsig)
    tg = np.arange(tA, tB, dt)
    S, TT = np.meshgrid(sg, tg)
    seeds.append((S + 1j*TT).ravel())
    return np.concatenate(seeds)

if __name__ == "__main__":
    mp.mp.dps = 30
    for T, cache in ((1e6, "att010_zeros_1e+06.npy"),):
        g = np.load(cache); t0 = float(g[0])
        tA, tB = t0+50.0, t0+250.0
        Lc = math.log(((tA+tB)/2)/TWOPI)
        w, mx = winding_zprime(0.30, 3.60, tA, tB, 0.01, 0.001)
        P(f"T={T:.0e}  box sigma(0.30,3.60) t({tA:.1f},{tB:.1f})  CERTIFIED count = {w:.3f}")
        mids = (g[:-1]+g[1:])/2; mids = mids[(mids > tA-2) & (mids < tB+2)]
        for dsig, dt in ((0.30, 1.5), (0.15, 0.8), (0.08, 0.4), (0.05, 0.25), (0.04, 0.15)):
            sd = seed_set(tA, tB, mids, Lc, dsig, dt)
            t_ = time.time()
            r = dedupe(newton_zprime(sd, tA, tB))
            r = r[(r.imag >= tA) & (r.imag <= tB)]
            P(f"   dsig={dsig:<5} dt={dt:<5} seeds={len(sd):>7}  found={len(r):>4}   "
              f"({len(r)/w*100:5.1f}% of certified)   {time.time()-t_:.1f}s")
        # keep the densest
        P("")
        P("  mpmath refinement of 25 random roots (2D Newton on mp.zeta derivative=1):")
        idx = np.random.default_rng(7).choice(len(r), 25, replace=False)
        dmax = 0.0; dtmax = 0.0
        for i in idx:
            z = mp.mpc(complex(r[i]))
            for _ in range(6):
                z = z - mp.zeta(z, derivative=1)/mp.zeta(z, derivative=2)
            d = abs(complex(z) - r[i]); dmax = max(dmax, d); dtmax = max(dtmax, abs(complex(z).imag - r[i].imag))
        P(f"    max |s_AFE - s_mpmath| = {dmax:.3e}   max |delta t| = {dtmax:.3e}")
        P(f"    (tape needs |delta t| << 2pi/L = {TWOPI/Lc:.3f}; phase error at tau=0.06 is "
          f"{0.06*Lc*dtmax:.2e} rad)")
        P("")
        neg = r[r.real < 0.5]
        P(f"  apparent beta' < 1/2 in box: {len(neg)}")
        for z in neg:
            zz = mp.mpc(complex(z))
            for _ in range(8):
                zz = zz - mp.zeta(zz, derivative=1)/mp.zeta(zz, derivative=2)
            P(f"    AFE {complex(z):.8f}  ->  mpmath {complex(zz):.8f}   "
              f"|zeta'| = {abs(complex(mp.zeta(zz,derivative=1))):.2e}")
