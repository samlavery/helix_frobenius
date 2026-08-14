"""ATTEMPT 029, stage 7 -- VERIFICATION of stage 5b, and the sensitivity deliverable.

V-A  INDEPENDENT ZERO GATE.  Re-evaluate a sample of the 137 located off-line DH zeros with
     mpmath's Hurwitz zeta (a completely different evaluator from the Euler-Maclaurin one used
     to find them).  |f| must be at the evaluator's noise level.
V-B  Lambda_f GATE.  sum_{n<=N} Lambda_f(n) n^{-3} must equal -f'/f(3) computed directly.
V-C  DEAD-LINE GATE (positive control that fails by MISSING STRUCTURE): the SAME pipeline run
     on the n = 0 mod 5 lines, where Lambda_f is identically zero, must return nothing.
V-D  THE COMPOSITE-LINE DETECTOR, and its sensitivity for zeta.
     Landau is EXACT at composite non-prime-power n for zeta: Lambda(n) = 0, so
          a_on(n) + (2pi/W) sum_{off-line} n^{beta-1/2} n^{i gamma} = 0.
     Hence any coherent Landau line at composite n in the ON-LINE zero set is, identically,
     the off-line zeros' signature -- and it needs NO total census, no N(T), no Turing.
     Measured for zeta over [14,20000]; calibrated against DH where the off-line set is known.
"""
import numpy as np, math, sys, mpmath as mp
from math import log, sqrt, pi
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att029_dh_offline import lam_f_dh, theta_f, vonm, T0, T1
from att014_dh_winding import dh, XI, AV

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'

if __name__ == "__main__":
    P(__doc__); mp.mp.dps = 30
    on = np.load(TMP+'att029_dh_on.npy'); r = np.load(TMP+'att029_dh_off.npy')
    right = r[r.real > 0.5]; W = T1-T0
    rng = np.random.default_rng(7)
    samp = right[rng.choice(len(right), 12, replace=False)]
    P("V-A  independent mpmath gate on 12 of the 137 located off-line zeros:")
    P(f"  {'beta':>12}{'gamma':>14}{'|f| mpmath':>14}{'|f| EM':>12}")
    for z in samp:
        s = mp.mpc(float(z.real), float(z.imag))
        v = mp.mpf(5)**(-s)*sum(mp.mpf(AV[k-1])*mp.zeta(s, mp.mpf(k)/5) for k in range(1,6))
        P(f"  {z.real:>12.7f}{z.imag:>14.6f}{float(abs(v)):>14.3e}{abs(dh(np.array([z]))[0][0]):>12.3e}")
    # mirror check
    mir = np.array([complex(1-z.real, z.imag) for z in samp])
    mv = [float(abs(mp.mpf(5)**(-mp.mpc(float(w.real),float(w.imag)))*
          sum(mp.mpf(AV[k-1])*mp.zeta(mp.mpc(float(w.real),float(w.imag)), mp.mpf(k)/5)
              for k in range(1,6)))) for w in mir]
    P(f"  FE mirror (1-beta, same gamma): max |f| = {max(mv):.3e}  -> the partners are real zeros")

    P("\nV-B  Lambda_f recursion gate.")
    LF = lam_f_dh(4000)
    nn = np.arange(len(LF), dtype=float); nn[0] = 1
    lhs = (LF[1:]*nn[1:]**(-3.0)).sum()
    s = mp.mpf(3)
    f0 = mp.mpf(5)**(-s)*sum(mp.mpf(AV[k-1])*mp.zeta(s, mp.mpf(k)/5) for k in range(1,6))
    h = mp.mpf(10)**-12
    fp = (mp.mpf(5)**(-(s+h))*sum(mp.mpf(AV[k-1])*mp.zeta(s+h, mp.mpf(k)/5) for k in range(1,6)) - f0)/h
    P(f"  sum_{{n<=4000}} Lambda_f(n) n^-3 = {lhs:.10f}   -f'/f(3) = {float(-fp/f0):.10f}"
      f"   diff {abs(lhs-float(-fp/f0)):.2e}")

    P("\nV-C  DEAD-LINE control, n = 0 mod 5 (Lambda_f identically 0 -- must return nothing):")
    gam_p = right.imag; d_p = right.real-0.5; k = 2*pi/W
    for n in (5, 10, 15, 20, 25, 30, 35, 40, 45, 50):
        ln = log(n)
        a_on = k*np.exp(1j*on*ln).sum(); a_oB = k*(2*np.cosh(d_p*ln)*np.exp(1j*gam_p*ln)).sum()
        P(f"    n={n:>3}  Lambda_f = {LF[n]:+.2e}   |a_on| = {abs(a_on):.4f}"
          f"   |a_beta| = {abs(a_on+a_oB):.4f}")

    # ------------------------------------------------------------------ V-D
    P("\nV-D  THE COMPOSITE-LINE DETECTOR.")
    g = np.load(TMP+'att019_zeros_to20k.npy'); Wz = g[-1]-g[0]; Nz = len(g)
    COMP = [n for n in range(6, 200) if vonm(n) == 0]
    ADM = [n for n in COMP if 2*pi*n*log(log(n)) < 0.10*Wz*10]     # V1 with Lambda -> O(log n)
    az = np.array([abs(np.exp(1j*g*log(n)).sum()/(Wz/(2*pi))) for n in COMP])
    P(f"  zeta, {Nz} zeros, W={Wz:.0f}: composite-line moduli over n in [6,199], {len(COMP)} values")
    P(f"    median {np.median(az):.5f}  90th {np.percentile(az,90):.5f}  max {az.max():.5f}"
      f"  (at n={COMP[int(np.argmax(az))]})")
    P(f"    Poisson floor (2pi/W)sqrt(N) = {(2*pi/Wz)*sqrt(Nz):.5f} -- the zeros are RIGID, so the")
    P(f"    observed floor is {(2*pi/Wz)*sqrt(Nz)/np.median(az):.1f}x below Poisson.")
    # DH calibration: coherent composite amplitude per off-line zero
    Noff = 2*len(right)
    dhc = []
    for n in (6, 14, 21, 26, 36, 42, 51, 46, 34, 39):
        ln = log(n); a_oO = k*2*np.exp(1j*gam_p*ln).sum(); dhc.append(abs(a_oO))
    c_per = np.median(dhc)*W/(2*pi*Noff)
    P(f"\n  DH calibration: |a_off| at composite n median {np.median(dhc):.4f} over {Noff}"
      f" off-line zeros in W={W:.0f}  =>  coherent amplitude per off-line zero c = {c_per:.4f}")
    thr = 3*np.percentile(az, 84)                       # 3 * (1-sigma of the observed floor)
    f_min = thr*Wz/(2*pi*Nz*c_per)
    P(f"  zeta 3-sigma threshold on |a_on(composite)| = {thr:.5f}")
    P(f"  => off-line fraction detectable at 3 sigma IF off-line zeros of zeta were as")
    P(f"     arithmetically coherent as DH's:   f_min = {f_min:.5f}  ({100*f_min:.3f} %)")
    P(f"     i.e. {f_min*Nz:.1f} off-line zeros out of {Nz} in [14,20000].")
    inc = 3*np.percentile(az,84)*Wz/(2*pi)
    P(f"  INCOHERENT worst case (off-line zeros arithmetically inert, |sum| ~ sqrt(N_off)):")
    P(f"     N_off detectable = {inc**2:.1f} zeros, i.e. f_min = {inc**2/Nz:.5f}"
      f" ({100*inc**2/Nz:.3f} %)")
    P(f"\n  COMPARISON, stated plainly: Turing's method plus a certified sign-change count")
    P(f"  determines the off-line count EXACTLY (f_off = 0 is a certificate, not a 3-sigma")
    P(f"  bound) over the same range, and localises each zero.  The composite-line detector is")
    P(f"  strictly weaker as a census; its only distinct feature is that it needs no N(T).")
