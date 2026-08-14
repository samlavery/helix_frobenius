"""ATTEMPT 030, stage 6 -- the MARGIN question (brief item 4), computed not asserted.

lambda_n = lambda_n^arch + lambda_n^arith.  Li 1997: RH <=> lambda_n >= 0 for all n >= 1.
Attempt 015 reported |arith|/arch <= 1.13e-2 on n = 200..3000 and asked what unconditional
bound on the prime side would suffice.  Here: the actual margin to n = 8000, and the exact
statement of what such a bound is worth.

STATED NULL: none needed -- this is an evaluation, not a test.  What IS pre-registered is the
classification (rule 2): if the sufficient bound turns out to be equivalent to RH rather than
weaker, say so.
"""
import sys, os, math, time
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att030_zeta import taylor_coeffs
def P(*a): print(*a); sys.stdout.flush()

def h_arch(z):
    s = 1/(1-z)
    return (1/s - mp.log(mp.pi)/2 + mp.digamma(s/2)/2) * s**2

if __name__ == "__main__":
    t0 = time.time(); P(__doc__); P("="*104)
    NMAX = 8000
    cache = os.path.join(HERE, 'att030_arch.npy')
    if not os.path.exists(cache):
        cz = taylor_coeffs(h_arch, '0.997', 16384, 50, NMAX)
        np.save(cache, np.array([float(c.real) for c in cz]))
    A = np.load(cache); Y = np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))
    lam = A + Y
    n = np.arange(1, NMAX+1, dtype=float)
    P(f"  lambda_1 = {lam[0]:.16f}   (literature 0.0230957089661210)")
    P(f"  lambda_2 = {lam[1]:.16f}   (literature 0.0923457352880)")
    P(f"  lambda_3 = {lam[2]:.16f}   lambda_4 = {lam[3]:.16f}")
    P(f"  lambda_n^arch, closed-form growth check:  arch_n / (n/2 * log n) at n = 100, 1000, "
      f"8000: {A[99]/(50*math.log(100)):.5f}, {A[999]/(500*math.log(1000)):.5f}, "
      f"{A[7999]/(4000*math.log(8000)):.5f}")
    P(f"  min lambda_n over n <= {NMAX}: {lam.min():.6f} at n = {int(np.argmin(lam))+1}  "
      f"(Li: RH <=> all >= 0)")
    for lo, hi in ((200,3000),(3000,8000),(1,8000)):
        sl = slice(lo-1, hi)
        P(f"  n in [{lo},{hi}]:  max |arith| = {np.abs(Y[sl]).max():.4f} at n = "
          f"{lo+int(np.argmax(np.abs(Y[sl])))},   max |arith|/arch = "
          f"{np.abs(Y[sl]/A[sl]).max():.4e},   max |arith|/n^(1/4) = "
          f"{np.abs(Y[sl]/n[sl]**0.25).max():.4f}")
    # growth exponent of the arithmetic part
    k = (n >= 200)
    p_, c_ = np.polyfit(np.log(n[k]), np.log(np.maximum(np.abs(Y[k]), 1e-12)), 1)
    P(f"  crude growth exponent of |lambda_n^arith| over n = 200..8000: {p_:+.3f} "
      f"(the n^{{1/4}} envelope is 0.25; running maxima below)")
    for lo, hi in ((200,400),(400,800),(800,1600),(1600,3200),(3200,8000)):
        sl = slice(lo-1, hi)
        P(f"     [{lo:>5},{hi:>5}]  max|arith| = {np.abs(Y[sl]).max():>8.4f}   "
          f"/ n^(1/4) = {np.abs(Y[sl]).max()/(0.5*(lo+hi))**0.25:>7.4f}   "
          f"/ (n^(1/2) log n) = {np.abs(Y[sl]).max()/((0.5*(lo+hi))**0.5*math.log(0.5*(lo+hi))):>8.5f}")
    P(f"\n[{time.time()-t0:.0f}s] stage 6 done")
