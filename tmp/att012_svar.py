"""ATTEMPT 012 -- DC-first on the variance of S(t).

HOUSE      : the theta-tape line amplitude  K(tau_n) = U Lambda(n)^2 / (L^2 n)   (attempt 010).
CLASSICAL  : Selberg's central limit theorem,  Var S(t) ~ (1/(2 pi^2)) log log T.

MECHANISM (worked out before any run; this is the composition, not decoration).
On the tape u = theta(t)/pi the zero density is 1 + S'(u).  The form factor of the zero
point process is  K(tau) = |sum_k e^{2 pi i tau u_k}|^2 / U.  Integrating the density
fluctuation to recover S contributes a Jacobian 1/(2 pi i tau), so

    |hat S(tau)|^2 = K(tau) / ( (2 pi tau)^2 U ),      Var S = sum_tau 2 |hat S(tau)|^2 .

Substituting the MEASURED house law K(tau_n) = U Lambda(n)^2/(L^2 n) at tau_n = log n / L:

    Var S = sum_n  2 * [U Lambda(n)^2/(L^2 n)] / (4 pi^2 tau_n^2 U)
          = (1/(2 pi^2)) sum_n Lambda(n)^2 / (n log^2 n).                        (*)

So the house instrument's per-line amplitude law integrates EXACTLY to the classical
Selberg variance.  That identity is the pairing.  Everything below is about the two things
the identity does NOT fix: (i) the CUTOFF on n, (ii) what is left over.

The cutoff is forced by the tape: lines exist at tau_n = log n / L and the tape's Nyquist /
Heisenberg edge is tau = 1, i.e.  n <= e^L = T/(2 pi).

RESTATEMENT CHECK (rule 2).  (*) IS the classical Selberg/Goldston prime sum -- Var on the
tape and Var in t are the same number, and the classical literature derives (*) from
essentially this computation.  NOTHING in (*) is claimed as new.  The deliverables are
numerical: the exact finite-height value, where the log log T asymptotic becomes valid, the
measured effective cutoff, and the size of the residual.

================================ PRE-REGISTERED NULLS =================================
Written before any number was produced.

PRIMARY H : Var S(t) measured over a window at height T equals
              V_line(X) = (1/(2 pi^2)) sum_{n <= X} Lambda(n)^2/(n log^2 n),  X = T/(2 pi).
PRIMARY NULL : ratio measured/V_line outside [0.80, 1.25] at any of the five heights,
              OR the residual fraction Var(S - S_lines)/Var(S) fails to decrease with T.
              Either way the line decomposition does not account for S.

NAMED ALTERNATIVE (also pre-registered, so a hit on it is not a post-hoc story).
Beyond the Heisenberg edge tau > 1 the form factor is K(tau) -> 1 (GUE / Berry-Keating),
not the diagonal K(tau) = tau.  That tail contributes, through the same Jacobian,
      (1/(2 pi^2)) * int_1^inf dtau/tau^2  =  1/(2 pi^2)  =  0.0506606   EXACTLY.
So if S = arithmetic lines + post-Heisenberg granularity, the ratio measured/V_line is
      1 + 0.0506606 / V_line(T/2pi),
predicted numerically = 1.494 (T=1e3), 1.451, 1.421, 1.399, 1.382 (T=1e7).  These five
numbers are pre-registered predictions of the ALTERNATIVE, computed from theory alone.

SECONDARY, on the house law itself:
 (a) C(X) := Cov(S, S_lines(X)) should equal V_L(X) := Var(S_lines(X)) if the measured line
     amplitudes are the predicted ones.  NULL: |C/V_L - 1| > 0.25.
 (b) WRONG-FREQUENCY CONTROL (must fail by missing structure, never by more cancellation):
     dilate alpha_n = log n -> 1.07 log n, same amplitudes.  Then the lines are at
     frequencies where S has none.  NULL for the control: |C_wrong| / C_true > 0.10.
 (c) QUADRATURE POSITIVE CONTROL: feed the pipeline a perfect lattice of zeros
     (theta(gamma_k)/pi = k exactly).  Then S is an exact unit sawtooth and Var must be
     1/12 = 0.0833333.  If the pipeline does not return 1/12 the measurement is broken.
 (d) NON-PRIME-POWER CONTROL: put the lines at log n for n NOT a prime power (same 1/sqrt n
     weights).  NULL for the control: |C| comparable to C_true.
=======================================================================================

SAMPLING (stated exactly, because Gram-point sampling is a known aliasing trap here).
S is NOT sampled at Gram points, and it is not sampled on a uniform grid either.  Between
consecutive zeros gamma_k, gamma_{k+1} it is exactly  S(t) = (c0 + k) - theta(t)/pi  with c0
an integer constant, i.e. a smooth function.  Var S is therefore computed as an EXACT
piecewise Gauss-Legendre quadrature of S and S^2 over every inter-zero interval of the
window, summed.  Quadrature order is varied (3,6,10) as part of the noise audit.
The unknown integer c0 is fixed by rounding -mean(k - theta/pi); the rounding residual is
reported and is the Turing check (|int S| <= 2.30 + 0.128 log(t/2pi) forces |mean S| < 0.003).
Var is c0-independent in any case.
"""
import numpy as np, math, os, sys
from math import log, pi, sqrt
import mpmath as mp

np.seterr(all='raise')
def P(*a): print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
TWOPI2 = 2.0 * pi * pi

# ------------------------------------------------------------------ theta and friends
def theta(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def thetap(t):
    t = np.asarray(t, float)
    return 0.5*np.log(t/(2*np.pi)) - 1/(48*t**2) - 21/(5760*t**4)

# ------------------------------------------------------------------ prime powers
def prime_powers(X):
    """returns (n, alpha=log n, a = Lambda(n)/(sqrt(n) log n) = 1/(k p^{k/2})) sorted by n."""
    X = int(X)
    if X < 2: return np.zeros(0), np.zeros(0), np.zeros(0)
    sieve = np.ones(X+1, bool); sieve[:2] = False
    for p in range(2, int(X**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    primes = np.nonzero(sieve)[0]
    ns, aa = [], []
    for p in primes:
        v, k = int(p), 1
        while v <= X:
            ns.append(v); aa.append(1.0/(k*float(p)**(k/2.0)))
            v *= int(p); k += 1
    ns = np.array(ns, float); aa = np.array(aa, float)
    o = np.argsort(ns)
    ns, aa = ns[o], aa[o]
    return ns, np.log(ns), aa

# ------------------------------------------------------------------ exact Var S
def var_S(gam, c0, m=6):
    """exact piecewise Gauss-Legendre of S and S^2 over [gam[0], gam[-1]]."""
    x, w = np.polynomial.legendre.leggauss(m)
    lo, hi = gam[:-1], gam[1:]
    mid = 0.5*(lo+hi); half = 0.5*(hi-lo)
    t = mid[:, None] + half[:, None]*x[None, :]
    kk = (c0 + np.arange(1, len(gam)))[:, None].astype(float)
    S = kk - theta(t)/np.pi
    Wp = gam[-1]-gam[0]
    I1 = (half[:, None]*w[None, :]*S).sum()
    I2 = (half[:, None]*w[None, :]*S*S).sum()
    return I1/Wp, I2/Wp                       # mean, mean-square

def mean_h(gam, m=6):
    x, w = np.polynomial.legendre.leggauss(m)
    lo, hi = gam[:-1], gam[1:]
    mid = 0.5*(lo+hi); half = 0.5*(hi-lo)
    t = mid[:, None] + half[:, None]*x[None, :]
    kk = np.arange(1, len(gam))[:, None].astype(float)
    h = kk - theta(t)/np.pi
    return (half[:, None]*w[None, :]*h).sum()/(gam[-1]-gam[0])

# ------------------------------------------------------------------ I_n = int S sin(alpha t) dt
def I_lines(gam, c0, alpha, block=800):
    """EXACT closed form (no cancellation: every term is O(1) except the zero sum).

        int_a^b S sin(a t) dt = (1/al)[ S(a+)cos(al a) - S(b-)cos(al b) + sum_{k=2}^{M-1} cos(al g_k) ]
                                + (1/(pi al^2))[ theta'(a) sin(al a) - theta'(b) sin(al b) ]  + O(log(b/a)/(2 al^2))
    derived by telescoping the piecewise-constant part and integrating theta by parts twice.
    """
    a, b = gam[0], gam[-1]; M = len(gam)
    Sa = c0 + 1 - theta(a)/pi                 # S just right of the first zero
    Sb = c0 + M - 1 - theta(b)/pi             # S just left  of the last  zero
    inner = gam[1:-1]                          # k = 2 .. M-1
    out = np.empty(len(alpha))
    for i in range(0, len(alpha), block):
        al = alpha[i:i+block][:, None]
        Z = np.cos(al*inner[None, :]).sum(axis=1)
        al1 = alpha[i:i+block]
        out[i:i+block] = (Sa*np.cos(al1*a) - Sb*np.cos(al1*b) + Z)/al1 \
            + (thetap(np.array([a]))[0]*np.sin(al1*a) - thetap(np.array([b]))[0]*np.sin(al1*b))/(pi*al1**2)
    return out

def mean_lines_terms(gam, alpha):
    a, b = gam[0], gam[-1]
    return (np.cos(alpha*a) - np.cos(alpha*b))/alpha     # int sin(alpha t) dt

# ------------------------------------------------------------------ V_L direct on a grid
def VL_direct(gam, alpha, amp, h):
    a, b = gam[0], gam[-1]
    t = np.arange(a, b, h)
    s = np.zeros(len(t))
    for i in range(0, len(alpha), 400):
        s += (amp[i:i+400][:, None]*np.sin(np.outer(alpha[i:i+400], t))).sum(axis=0)
    s *= -1.0/pi
    return s.var(), len(t)

# =====================================================================================
P(__doc__.split("SAMPLING")[0][-1400:] if False else "")
P("="*94)
P("ATTEMPT 012 -- DC-first on Var S(t).   house: theta-tape line amplitude   x   classical: Selberg CLT")
P("="*94)

HEIGHTS = ['1e+03', '1e+04', '1e+05', '1e+06', '1e+07']
DATA = {}
for tag in HEIGHTS:
    g = np.load(os.path.join(HERE, f'att010_zeros_{tag}.npy'))
    DATA[tag] = g

# ---------- exact constants
mp.mp.dps = 30
MERTENS = float(mp.mpf('0.26149721284764278375542683860869585905'))
CPP = float(mp.nsum(lambda k: mp.primezeta(k)/k**2, [2, mp.inf]))
P(f"\nexact constants:  Mertens M = {MERTENS:.15f}   C_pp = sum_{{k>=2}} P(k)/k^2 = {CPP:.15f}")
P(f"                  M + C_pp  = {MERTENS+CPP:.15f}     1/(2 pi^2) = {1/TWOPI2:.15f}")

# ---------- sieve once, to the largest cutoff we will need
XMAX = int(1e7/(2*pi)) + 10
P(f"\nsieving prime powers to X = {XMAX} ...")
NS, AL, AM = prime_powers(XMAX)
A2 = AM*AM
CUM_A2 = np.cumsum(A2)
P(f"  {len(NS)} prime powers,  sum a_n^2 (full) = {CUM_A2[-1]:.6f}")

def V_line(X):
    """(1/(2pi^2)) sum_{n<=X} Lambda(n)^2/(n log^2 n)  -- EXACT, evaluated not estimated."""
    j = np.searchsorted(NS, X, side='right')
    return (CUM_A2[j-1] if j > 0 else 0.0)/TWOPI2

# ---------- item 4: calibration of Selberg's log log T asymptotic  (pure computation)
P("\n" + "-"*94)
P("ITEM 4.  Calibration of the classical asymptotic  Var S ~ (1/(2 pi^2)) log log T")
P("-"*94)
P("  exact finite-height value uses cutoff X = T/(2 pi) (the tape's Heisenberg edge tau = 1):")
P("     V_line(T/2pi) = (1/(2pi^2)) [ log L + M + C_pp + eps(T) ],   L = log(T/2pi)")
P("  so the RELATIVE deficit of the asymptotic is  (log L - log log T + M + C_pp)/log log T.\n")
P(f"  {'T':>10}{'log log T':>12}{'exact V_line':>14}{'asymptotic':>12}{'asym/exact':>12}{'deficit':>10}")
for tag in HEIGHTS:
    T = float(tag); L = log(T/(2*pi))
    ex = V_line(T/(2*pi)); asy = log(log(T))/TWOPI2
    P(f"  {T:>10.0e}{log(log(T)):>12.4f}{ex:>14.6f}{asy:>12.6f}{asy/ex:>12.4f}{1-asy/ex:>10.2%}")
P("")
for tol in (0.10, 0.05, 0.01):
    # asymptotic within tol  <=>  (M + C_pp + log(L/log T)) / log log T <= tol ; solve numerically
    def f(x):
        corr = math.log(1 - math.log(2*pi)/math.exp(x)) if x < 50 else 0.0
        return (MERTENS + CPP + corr)/x - tol
    lo, hi = 2.0, 1e4
    for _ in range(300):
        mid = 0.5*(lo+hi)
        if f(mid) > 0: lo = mid
        else: hi = mid
    llT = 0.5*(lo+hi); lT = math.exp(llT) if llT < 700 else float('inf')
    P(f"  asymptotic accurate to {tol:>5.0%}:  log log T = {llT:.4f}  =>  log T = {lT:.6g}"
      f"  =>  T = exp({lT:.6g})" + (f" = 10^{lT/math.log(10):.6g}" if lT < 1e6 else ""))

# ---------- items 1,2,3,5
P("\n" + "-"*94)
P("ITEMS 1-3,5.  measured Var S   vs   exact line prediction   vs   residual")
P("-"*94)

RES = {}
for tag in HEIGHTS:
    gam = DATA[tag]; T = float(tag); M_ = len(gam)
    a, b = gam[0], gam[-1]; Wp = b-a
    tc = 0.5*(a+b)
    Lc = log(tc/(2*pi))                      # L at the window CENTRE (house rule)
    mh = mean_h(gam)
    c0 = float(np.round(-mh))
    turing = mh + c0
    meanS, msS = var_S(gam, c0)
    varS = msS - meanS**2

    X = tc/(2*pi)                             # Heisenberg cutoff
    j = np.searchsorted(NS, X, side='right')
    alpha, amp = AL[:j], AM[:j]
    Vl = CUM_A2[j-1]/TWOPI2

    In = I_lines(gam, c0, alpha)
    ml_terms = mean_lines_terms(gam, alpha)
    meanL = -(amp*ml_terms).sum()/(pi*Wp)
    Craw = -(amp*In).sum()/(pi*Wp)
    C = Craw - meanS*meanL
    varR = varS - 2*C + Vl

    RES[tag] = dict(T=T, M=M_, Wp=Wp, L=Lc, X=X, nlines=j, c0=c0, turing=turing,
                    meanS=meanS, varS=varS, Vl=Vl, C=C, varR=varR, alpha=alpha, amp=amp, In=In,
                    gam=gam, meanL=meanL)

    P(f"\n  T = {T:.0e}   zeros M = {M_}   window W' = {Wp:.1f}   L(centre) = {Lc:.4f}   "
      f"Heisenberg cutoff X = T/2pi = {X:.0f}  ({j} lines)")
    P(f"     Turing check   : mean(S) = {meanS:.6f}   (integer rounding residual {turing:+.6f}; "
      f"bound from |int S| <= 2.30+0.128 L is {(2.30+0.128*Lc)/Wp:.5f})")
    P(f"     MEASURED       : Var S = {varS:.6f}    sigma = {sqrt(varS):.6f}   (mean-square {msS:.6f})")
    P(f"     EXACT line sum : V_line(T/2pi) = {Vl:.6f}      measured/V_line = {varS/Vl:.4f}")
    P(f"     + granularity  : V_line + 1/(2pi^2) = {Vl+1/TWOPI2:.6f}   measured/that = {varS/(Vl+1/TWOPI2):.4f}")
    P(f"     Cov(S,S_lines) = {C:.6f}     Var(S_lines) = {Vl:.6f}     C/V_L = {C/Vl:.4f}")
    P(f"     RESIDUAL       : Var(S - S_lines) = {varR:.6f}    fraction of Var S = {varR/varS:.4f}"
      f"    ( 1/(2pi^2) = {1/TWOPI2:.6f} )")

# ---------- summary table
P("\n" + "="*94)
P("SUMMARY")
P("="*94)
P(f"  {'T':>8}{'Var S meas':>12}{'V_line':>11}{'ratio':>8}{'V_line+1/2pi^2':>16}{'ratio':>8}"
  f"{'C/V_L':>8}{'Var resid':>11}{'resid/tot':>10}")
for tag in HEIGHTS:
    r = RES[tag]
    P(f"  {r['T']:>8.0e}{r['varS']:>12.6f}{r['Vl']:>11.6f}{r['varS']/r['Vl']:>8.4f}"
      f"{r['Vl']+1/TWOPI2:>16.6f}{r['varS']/(r['Vl']+1/TWOPI2):>8.4f}"
      f"{r['C']/r['Vl']:>8.4f}{r['varR']:>11.6f}{r['varR']/r['varS']:>10.4f}")

# effective cutoff: solve V_line(X*) = Var S
P("\n  EFFECTIVE CUTOFF  X* solving V_line(X*) = measured Var S:")
P(f"  {'T':>8}{'X*':>16}{'log X*':>10}{'L=log(T/2pi)':>14}{'log X*/L':>10}{'X*/T':>12}")
for tag in HEIGHTS:
    r = RES[tag]; target = r['varS']*TWOPI2
    j = int(np.searchsorted(CUM_A2, target))
    if j >= len(NS):
        P(f"  {r['T']:>8.0e}   beyond sieve X={XMAX}  (cum sum max {CUM_A2[-1]:.4f} < target {target:.4f})")
    else:
        Xs = NS[j]
        P(f"  {r['T']:>8.0e}{Xs:>16.0f}{log(Xs):>10.4f}{r['L']:>14.4f}{log(Xs)/r['L']:>10.4f}{Xs/r['T']:>12.4g}")
np.save(os.path.join(HERE, 'att012_res.npy'),
        np.array([[RES[t]['T'], RES[t]['varS'], RES[t]['Vl'], RES[t]['C'], RES[t]['varR']] for t in HEIGHTS]))
P("\n(stage 1 done)")
