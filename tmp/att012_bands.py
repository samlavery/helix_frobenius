"""ATTEMPT 012, stage 3 -- WHERE the residual lives, and the recalibrated asymptotic.

Stage 1 measured a residual Var(S - S_lines) = 0.0504..0.0516 at five heights, flat, equal to
the PRE-REGISTERED post-Heisenberg constant 1/(2 pi^2) = 0.0506606.  That was a size match.
This stage checks the LOCATION, which is what makes it an explanation rather than a coincidence:

  on the tape S(u) = c_k - u on (u_k, u_{k+1}),  u = theta/pi,  a piecewise-linear function.
  Its exact Fourier series on the window [0, U] gives  Var_u(S) = sum_{j != 0} |s_j|^2  with
  tau_j = j/U.  PRE-REGISTERED SPLIT:
        sum over tau_j < 1  =  (1/(2 pi^2)) sum_{n <= T/2pi} Lambda(n)^2/(n log^2 n)   (the lines)
        sum over tau_j > 1  =  1/(2 pi^2) = 0.0506606                                  (granularity)
  NULL: the tau > 1 band does not carry the residual (i.e. it is not ~0.05, or the tau < 1 band
  is not ~V_line).  Then the "Heisenberg edge" account is a story fitted to a total.

  CAVEAT stated up front: this decomposition is in the u-measure, and Var_u = Var_t only when
  dt/du = 2 pi / log(t/2pi) is near-constant across the window.  The window is 5197 wide at
  T = 1e3 (dt/du varies 29%) and 1849 wide at T = 1e7 (varies 0.02%).  Both are reported and
  the u-vs-t discrepancy is shown explicitly, so the low heights are read with that in mind.
"""
import numpy as np, math, os, sys
from math import log, pi, sqrt
np.seterr(all='raise')
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
TWOPI2 = 2.0*pi*pi
_src = open(os.path.join(HERE, 'att012_svar.py')).read()
exec(_src[_src.index('def theta(t):'):_src.index('# =====')])

HEIGHTS = ['1e+03', '1e+04', '1e+05', '1e+06', '1e+07']
XMAX = int(1e7/(2*pi)) + 10
NS, AL, AM = prime_powers(XMAX); A2 = AM*AM; CUM_A2 = np.cumsum(A2)
def V_line(X):
    j = np.searchsorted(NS, X, side='right'); return (CUM_A2[j-1] if j > 0 else 0.0)/TWOPI2

MERT_CPP = 0.400967852458951465558504511546      # M + sum_{k>=2} P(k)/k^2, from mpmath dps=30

P("="*96)
P("ATTEMPT 012 stage 3 -- band split on the tape, and the recalibrated Selberg asymptotic")
P("="*96)

# ---------------------------------------------------------------- band split
P("\nEXACT TAPE FOURIER SPLIT of Var(S) at the Heisenberg edge tau = 1")
P(f"  {'T':>8}{'Var_u total':>13}{'tau<1 band':>12}{'V_line pred':>13}{'ratio':>8}"
  f"{'t>1 meas':>10}{'tail':>9}{'t>1 tot':>10}{'/pred':>8}{'Var_t':>10}")
for tag in HEIGHTS:
    gam = np.load(os.path.join(HERE, f'att010_zeros_{tag}.npy'))
    c0 = float(np.round(-mean_h(gam)))
    mS, msS = var_S(gam, c0); vt = msS - mS**2
    u = theta(gam)/pi; u = u - u[0]; U = u[-1]; M = len(u)
    # on (u_k, u_{k+1}):  S(u) = v_k - (u - u_k),  v_k = (c0+k) - theta(gam_k)/pi.
    # v_k is O(1) and is formed as a difference of two ~1e7 numbers -> abs error ~2e-9. No
    # constant is ever squared, which is what broke the first version at T = 1e7.
    v = (c0 + np.arange(1, M)) - theta(gam[:-1])/pi
    s = np.diff(u)
    m1 = (v*s - 0.5*s*s).sum()/U
    m2 = ((v**3 - (v-s)**3)/3.0).sum()/U
    vu = m2 - m1**2
    # exact Fourier coefficients  s_j = (1/U) int_0^U S(u) e^{-2 pi i j u / U} du
    #   int over interval k = (P_k - P_{k+1})(v_k/(i om) + 1/om^2) - (i/om) s_k P_{k+1},
    #   P_k = e^{-i om u_k}.
    TAUMAX = 20.0
    J = int(TAUMAX*U); jj = np.arange(1, J+1); om = 2*pi*jj/U
    S_ = np.zeros(J, complex); CH = 256
    for i in range(0, J, CH):
        oc = om[i:i+CH][:, None]
        ph = oc*u[None, :]
        Pk = np.cos(ph) - 1j*np.sin(ph)
        d = Pk[:, :-1] - Pk[:, 1:]
        S_[i:i+CH] = ((d*(v[None, :]/(1j*oc) + 1/oc**2)).sum(axis=1)
                      - (1j/oc[:, 0])*(s[None, :]*Pk[:, 1:]).sum(axis=1))/U
    pw = 2*np.abs(S_)**2                          # +j and -j
    tau = jj/U
    lo_band = pw[tau < 1].sum(); hi_meas = pw[tau >= 1].sum()
    tail = (1/TWOPI2)/TAUMAX                      # assumed K=1 continuation beyond tau=20
    T = float(tag); tc = 0.5*(gam[0]+gam[-1]); vl = V_line(tc/(2*pi))
    P(f"  {T:>8.0e}{vu:>13.6f}{lo_band:>12.6f}{vl:>13.6f}{lo_band/vl:>8.4f}"
      f"{hi_meas:>10.6f}{tail:>9.6f}{hi_meas+tail:>10.6f}{(hi_meas+tail)/(1/TWOPI2):>8.4f}{vt:>10.6f}")
P("  ('tau>1 meas' is the honestly measured band 1 <= tau <= 20; 'tail' is the only assumed part,")
P("   the K=1 continuation beyond tau=20, worth 1/(2 pi^2 * 20) = 0.002533 = ~5% of the band.)")

# ---------------------------------------------------------------- residual, both definitions
P("\nRESIDUAL, two definitions (t-measure, from stage 1 quantities recomputed here):")
P(f"  {'T':>8}{'Var S':>11}{'V_L exact':>12}{'Var S - V_L':>13}{'/(1/2pi^2)':>12}")
rs = []
for tag in HEIGHTS:
    gam = np.load(os.path.join(HERE, f'att010_zeros_{tag}.npy'))
    c0 = float(np.round(-mean_h(gam))); mS, msS = var_S(gam, c0); vS = msS-mS**2
    tc = 0.5*(gam[0]+gam[-1]); vl = V_line(tc/(2*pi))
    r = vS - vl; rs.append(r)
    P(f"  {float(tag):>8.0e}{vS:>11.6f}{vl:>12.6f}{r:>13.6f}{r/(1/TWOPI2):>12.4f}")
rs = np.array(rs)
P(f"  --> mean {rs.mean():.6f}  sd {rs.std(ddof=1):.6f}  vs 1/(2pi^2) = {1/TWOPI2:.6f}"
  f"   mean/pred = {rs.mean()/(1/TWOPI2):.4f}   no trend with T (range {rs.min():.6f}..{rs.max():.6f})")

# ---------------------------------------------------------------- recalibrated item 4
P("\n" + "-"*96)
P("ITEM 4 (recalibrated).  The exact finite-height variance is now")
P("      V(T) = (1/(2 pi^2)) [ log L + M + C_pp + 1 + eps(T) ],   L = log(T/2 pi),  M+C_pp = 0.4009679")
P("  so the classical asymptotic (1/(2 pi^2)) log log T carries a relative deficit")
P("      (1 + M + C_pp + log(1 - log(2pi)/log T)) / log log T   ->   1.4009679 / log log T.")
P("-"*96)
P(f"  {'T':>10}{'measured Var':>14}{'exact V(T)':>12}{'asymptotic':>12}{'asym/exact':>12}{'asym/meas':>11}")
for tag in HEIGHTS:
    gam = np.load(os.path.join(HERE, f'att010_zeros_{tag}.npy'))
    c0 = float(np.round(-mean_h(gam))); mS, msS = var_S(gam, c0); vS = msS-mS**2
    T = float(tag); tc = 0.5*(gam[0]+gam[-1])
    ex = V_line(tc/(2*pi)) + 1/TWOPI2; asy = log(log(T))/TWOPI2
    P(f"  {T:>10.0e}{vS:>14.6f}{ex:>12.6f}{asy:>12.6f}{asy/ex:>12.4f}{asy/vS:>11.4f}")
P("")
for tol in (0.10, 0.05, 0.01):
    def f(x):
        corr = math.log(1 - math.log(2*pi)/math.exp(x)) if x < 50 else 0.0
        return (1 + MERT_CPP + corr)/x - tol
    lo, hi = 2.0, 1e4
    for _ in range(300):
        mid = 0.5*(lo+hi)
        if f(mid) > 0: lo = mid
        else: hi = mid
    llT = 0.5*(lo+hi); lT = math.exp(llT)
    P(f"  Selberg's log log T asymptotic reaches {tol:>5.0%} accuracy only at "
      f"log log T = {llT:.4f},  log T = {lT:.6g},  T = 10^{lT/math.log(10):.6g}")
P("\n  (for contrast, the line-sum-only calibration of stage 1, which OMITS the +1/(2pi^2):")
for tol in (0.10, 0.05, 0.01):
    def f(x):
        corr = math.log(1 - math.log(2*pi)/math.exp(x)) if x < 50 else 0.0
        return (MERT_CPP + corr)/x - tol
    lo, hi = 2.0, 1e4
    for _ in range(300):
        mid = 0.5*(lo+hi)
        if f(mid) > 0: lo = mid
        else: hi = mid
    llT = 0.5*(lo+hi); lT = math.exp(llT)
    P(f"     {tol:>5.0%}: log T = {lT:.6g}, T = 10^{lT/math.log(10):.6g})")
P("\n(stage 3 done)")
