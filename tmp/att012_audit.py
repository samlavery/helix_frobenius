"""ATTEMPT 012, stage 2 -- noise audit, positive/negative controls, cutoff scan.

Everything here was specified in att012_svar.py's pre-registration block BEFORE stage 1 ran.

CONTROLS (rule 3: a control must fail by MISSING STRUCTURE, never by more cancellation)
 (b) WRONG-FREQUENCY: alpha_n = log n -> 1.07 log n, amplitudes untouched.  The lines are now
     at frequencies S does not contain.  NULL for the control: |C_wrong|/C_true > 0.10.
 (c) PERFECT LATTICE: replace the zeros by theta(g_k)/pi = k exactly.  S is then an exact unit
     sawtooth, Var must be 1/12 = 0.0833333, and C must be ~0.  This validates the quadrature
     AND shows the residual observable is discriminating: a rigid lattice puts 1/12 in the
     post-Heisenberg band, GUE puts 1/(2 pi^2) = 0.050661 there -- a 64% separation.
 (d) NON-PRIME-POWER: alpha_n = log m with m running over the integers that are NOT prime
     powers, same amplitude multiset.  NULL for the control: |C|/C_true > 0.10.

CUTOFF SCAN.  Split the tape spectrum at tau = c instead of tau = 1:
     total(c) = V_line(c*T/(2 pi))  +  (1/(2 pi^2)) * (1/c)
 (diagonal K = tau below the split, K = 1 above it).  Because K is continuous at tau = 1,
 d/dc[log c + 1/c] = 1/c - 1/c^2 vanishes at c = 1: the split is STATIONARY at the Heisenberg
 edge.  PRE-REGISTERED: the ratio measured/total(c) is flat near c = 1 and degrades away from
 it, with the best c consistent with 1 at every height.  NULL: best c is not near 1, or the
 curve has no stationary point there -- then "Heisenberg edge" is a story, not a measurement.
"""
import numpy as np, math, os, sys
from math import log, pi, sqrt
import mpmath as mp
np.seterr(all='raise')
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
TWOPI2 = 2.0*pi*pi

_src = open(os.path.join(HERE, 'att012_svar.py')).read()
_helpers = _src[_src.index('def theta(t):'):_src.index('# =====')]
exec(_helpers)                                    # theta, thetap, prime_powers, var_S, mean_h,
                                                  # I_lines, mean_lines_terms, VL_direct

HEIGHTS = ['1e+03', '1e+04', '1e+05', '1e+06', '1e+07']
XMAX = int(1e7/(2*pi)) + 10
NS, AL, AM = prime_powers(XMAX)
A2 = AM*AM; CUM_A2 = np.cumsum(A2)
def V_line(X):
    j = np.searchsorted(NS, X, side='right')
    return (CUM_A2[j-1] if j > 0 else 0.0)/TWOPI2

def setup(tag):
    gam = np.load(os.path.join(HERE, f'att010_zeros_{tag}.npy'))
    c0 = float(np.round(-mean_h(gam)))
    return gam, c0

P("="*96)
P("ATTEMPT 012 stage 2 -- audit")
P("="*96)

# ---------------------------------------------------------------- (c) lattice positive control
P("\n(c) QUADRATURE POSITIVE CONTROL: perfect lattice theta(g_k)/pi = k.  target Var = 1/12 = 0.0833333")
for tag in ('1e+03', '1e+05', '1e+07'):
    gam, _ = setup(tag)
    # solve theta(t) = k*pi by Newton, k covering the same range
    k0 = math.ceil(theta(np.array([gam[0]]))[0]/pi); k1 = math.floor(theta(np.array([gam[-1]]))[0]/pi)
    ks = np.arange(k0, k1+1, dtype=float)
    t = gam[0] + (gam[-1]-gam[0])*(ks-k0)/max(k1-k0, 1)
    for _ in range(80):
        t = t - (theta(t) - ks*pi)/thetap(t)
    lat = t
    c0l = float(np.round(-mean_h(lat)))
    mL, msL = var_S(lat, c0l)
    P(f"    T={tag}  M={len(lat)}   Var(lattice) = {msL-mL**2:.7f}   "
      f"deviation from 1/12: {(msL-mL**2)/(1/12.)-1:+.3%}   |resid theta-k pi| max "
      f"{np.abs(theta(lat)-np.arange(k0,k1+1)*pi).max():.2e}")

# ---------------------------------------------------------------- noise audit: quad order + subwindows
P("\nNOISE AUDIT 1 -- Gauss-Legendre order (Var S must be order-independent):")
P(f"  {'T':>8}" + "".join(f"{'m='+str(m):>14}" for m in (3, 6, 10, 16)))
for tag in HEIGHTS:
    gam, c0 = setup(tag); row = f"  {float(tag):>8.0e}"
    for m in (3, 6, 10, 16):
        mS, msS = var_S(gam, c0, m=m); row += f"{msS-mS**2:>14.8f}"
    P(row)

P("\nNOISE AUDIT 2 -- sub-window scatter (window split into 1,2,4,8 pieces; Var of each piece):")
P(f"  {'T':>8}{'full':>11}{'2-piece mean+-sd':>22}{'4-piece mean+-sd':>22}{'8-piece mean+-sd':>22}")
for tag in HEIGHTS:
    gam, c0 = setup(tag); mS, msS = var_S(gam, c0); row = f"  {float(tag):>8.0e}{msS-mS**2:>11.6f}"
    for q in (2, 4, 8):
        vs = []
        for i in range(q):
            sl = gam[i*len(gam)//q:(i+1)*len(gam)//q+1]
            m1, m2 = var_S(sl, c0 + i*len(gam)//q)
            vs.append(m2-m1**2)
        vs = np.array(vs); row += f"{vs.mean():>13.6f}+-{vs.std():<8.6f}"
    P(row)

# ---------------------------------------------------------------- V_L direct-vs-diagonal
P("\nNOISE AUDIT 3 -- Var(S_lines): closed-form diagonal vs direct evaluation on a fine grid")
P("  (checks that the neglected off-diagonal / window-edge terms are small)")
for tag in ('1e+03', '1e+04', '1e+05'):
    gam, c0 = setup(tag); T = float(tag); tc = 0.5*(gam[0]+gam[-1])
    X = tc/(2*pi); j = np.searchsorted(NS, X, side='right')
    vd, npts = VL_direct(gam, AL[:j], AM[:j], 0.02)
    P(f"    T={tag}  lines={j}  diagonal {CUM_A2[j-1]/TWOPI2:.6f}   direct(grid h=0.02, {npts} pts) "
      f"{vd:.6f}   ratio {vd/(CUM_A2[j-1]/TWOPI2):.4f}")

# ---------------------------------------------------------------- controls (b) and (d)
P("\n(b),(d) CONTROLS -- covariance of S with MIS-PLACED lines")
P(f"  {'T':>8}{'C_true':>11}{'V_L':>11}{'C/V_L':>8}{'C_dilate1.07':>14}{'ratio':>9}"
  f"{'C_nonPP':>11}{'ratio':>9}{'C_dilate1.003':>15}{'ratio':>9}")
# non-prime-power integers, same count as the line set
def nonpp(count, cap):
    sieve = np.ones(cap+1, bool); sieve[:2] = False
    for p in range(2, int(cap**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    pr = np.nonzero(sieve)[0]
    ispp = np.zeros(cap+1, bool)
    for p in pr:
        v = int(p)
        while v <= cap: ispp[v] = True; v *= int(p)
    cand = np.nonzero(~ispp)[0]; cand = cand[cand >= 2]
    return cand[:count].astype(float)

for tag in HEIGHTS:
    gam, c0 = setup(tag); tc = 0.5*(gam[0]+gam[-1]); Wp = gam[-1]-gam[0]
    X = tc/(2*pi); j = np.searchsorted(NS, X, side='right')
    al, am = AL[:j], AM[:j]; Vl = CUM_A2[j-1]/TWOPI2
    mS, msS = var_S(gam, c0)
    def cov(alpha):
        In = I_lines(gam, c0, alpha)
        meanL = -(am*mean_lines_terms(gam, alpha)).sum()/(pi*Wp)
        return -(am*In).sum()/(pi*Wp) - mS*meanL
    Ct = cov(al)
    Cd = cov(al*1.07)
    Cd2 = cov(al*1.003)
    npp = nonpp(j, 6*int(X)+100)
    Cn = cov(np.log(npp))
    P(f"  {float(tag):>8.0e}{Ct:>11.6f}{Vl:>11.6f}{Ct/Vl:>8.4f}{Cd:>14.6f}{Cd/Ct:>9.4f}"
      f"{Cn:>11.6f}{Cn/Ct:>9.4f}{Cd2:>15.6f}{Cd2/Ct:>9.4f}")

# ---------------------------------------------------------------- cutoff scan
P("\nCUTOFF SCAN -- split the tape spectrum at tau = c;  total(c) = V_line(c T/2pi) + 1/(2 pi^2 c)")
P("  pre-registered: stationary and best at c = 1 (the Heisenberg edge).  ratio = measured/total(c)")
CS = (0.125, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 4.0, 8.0)
P(f"  {'T':>8}" + "".join(f"{'c='+str(c):>10}" for c in CS))
allr = []
for tag in HEIGHTS:
    gam, c0 = setup(tag); tc = 0.5*(gam[0]+gam[-1]); mS, msS = var_S(gam, c0); vS = msS-mS**2
    row = f"  {float(tag):>8.0e}"; rr = []
    for c in CS:
        tot = V_line(c*tc/(2*pi)) + 1/(TWOPI2*c)
        rr.append(vS/tot); row += f"{vS/tot:>10.4f}"
    allr.append(rr); P(row)
allr = np.array(allr)
P(f"  {'rms|r-1|':>8}" + "".join(f"{np.sqrt(((allr[:,i]-1)**2).mean()):>10.4f}" for i in range(len(CS))))
P(f"\n  best c by rms deviation from 1: c = {CS[int(np.argmin([np.sqrt(((allr[:,i]-1)**2).mean()) for i in range(len(CS))]))]}")

# also: plain fixed cutoffs
P("\n  for reference, plain line sums at other classical cutoffs (no granularity term):")
P(f"  {'T':>8}{'V_line(sqrt T)':>16}{'ratio':>8}{'V_line(T/2pi)':>15}{'ratio':>8}{'V_line(T)':>12}{'ratio':>8}")
for tag in HEIGHTS:
    gam, c0 = setup(tag); mS, msS = var_S(gam, c0); vS = msS-mS**2; T = float(tag)
    v1, v2, v3 = V_line(sqrt(T)), V_line(T/(2*pi)), V_line(T)
    P(f"  {T:>8.0e}{v1:>16.6f}{vS/v1:>8.4f}{v2:>15.6f}{vS/v2:>8.4f}{v3:>12.6f}{vS/v3:>8.4f}")
P("\n(stage 2 done)")
