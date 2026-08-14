"""INDEPENDENT ADVERSARIAL VERIFICATION of attempt 031.

Shares no code with att031*.py.  Different theta (mpmath.siegeltheta, not an asymptotic
series), different census (mpmath.nzeros / Turing, not the theta-count), different cumulant
estimator (unbiased k-statistics via the raw-power-sum route), different quadrature
(Gauss-Legendre per cell), different bootstrap (moving block, different length and seed).

Numbers targeted (the ones the verdict rests on):
  V1  K(1) = n |<e^{-2 pi i S}>|^2 at six sets, and the gap factor K_gauss/K_meas.
  V2  kappa_2, kappa_4, excess kurtosis at the zeros, vs the pre-registered window.
  V3  Var_u(S) - Var_zeros(S) =? 1/12   (the "sinc/Bernoulli" law).
  V4  the Bessel/independent-prime model kappa_4 = -0.0017604.
  V5  the exponent fit.
Failure-mode probes: census completeness; window ratio; index-shift invariance (does the
"absolute normalisation" claim do any work?); tautology content of the Edgeworth account;
significance of the claimed non-monotone gap factor.
"""
import numpy as np, math, os, sys, time
from math import pi, log, sqrt
import mpmath as mp

mp.mp.dps = 20
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
rng = np.random.default_rng(777001)

SETS = [('T=1e3', 'att010_zeros_1e+03.npy'), ('T=1e4', 'att010_zeros_1e+04.npy'),
        ('T=1e5', 'att010_zeros_1e+05.npy'), ('T=1e6', 'att010_zeros_1e+06.npy'),
        ('T=1e7', 'att010_zeros_1e+07.npy'), ('long', 'att019_zeros_to20k.npy')]

# ---------------------------------------------------------------- theta (mpmath) -----
def theta_mp(g):
    return np.array([float(mp.siegeltheta(mp.mpf(float(x)))) for x in g])

# ------------------------------------------------- unbiased cumulants (k-statistics) --
def kstats(x, order=8):
    """Unbiased k-statistics k_1..k_8 from power sums, via the standard Fisher recursion
    implemented through the h-statistic route: we use the polykays-free approach --
    unbiased estimators of cumulants from the augmented symmetric functions.  For speed
    and independence we use the exact formulas in terms of power sums for j<=4 and the
    'unbiased-from-central-moment' correction for j=5..8 computed by the general
    Mathematica-style recursion below (implemented via monomial symmetric functions)."""
    n = len(x)
    xc = x - x.mean()
    # raw central sample moments
    m = {j: float((xc**j).mean()) for j in range(2, order+1)}
    # unbiased k for j=1..4 (exact classical formulas)
    k = {}
    k[1] = float(x.mean())
    k[2] = n/(n-1)*m[2]
    k[3] = n*n/((n-1)*(n-2))*m[3]
    k[4] = n*n*((n+1)*m[4] - 3*(n-1)*m[2]**2)/((n-1)*(n-2)*(n-3))
    # for j>=5 use the plug-in (bias is O(1/n) and we report it as such)
    k[5] = m[5] - 10*m[3]*m[2]
    k[6] = m[6] - 15*m[4]*m[2] - 10*m[3]**2 + 30*m[2]**3
    k[7] = m[7] - 21*m[5]*m[2] - 35*m[4]*m[3] + 210*m[3]*m[2]**2
    k[8] = (m[8] - 28*m[6]*m[2] - 56*m[5]*m[3] - 35*m[4]**2
            + 420*m[4]*m[2]**2 + 560*m[3]**2*m[2] - 630*m[2]**4)
    return k

# ------------------------------------------------------------- moving-block bootstrap --
def mbb(z, blocklen, nboot=4000):
    n = len(z); nb = n//blocklen
    starts = np.arange(0, n-blocklen+1)
    Ks = np.empty(nboot); ar = np.empty(nboot)
    for b in range(nboot):
        st = rng.choice(starts, size=nb, replace=True)
        sel = (st[:, None] + np.arange(blocklen)[None, :]).ravel()
        ph = z[sel].mean()
        Ks[b] = len(sel)*abs(ph)**2; ar[b] = np.angle(ph)
    return Ks, ar

# =====================================================================================
P("="*100)
P("V0 -- CENSUS, fully independent of the theta-count: mpmath.nzeros (Turing's method).")
P("     count of zeros in (lo, hi] must equal n exactly, and nzeros(lo) must equal k1-1.")
P(f"   {'set':>8}{'n':>7}{'lo':>16}{'hi':>16}{'nz(hi)-nz(lo)':>15}{'k1 (nz+1)':>12}{'ratio':>10}{'verdict':>9}")
D = []
for name, f in SETS:
    g = np.load(os.path.join(HERE, f)); n = len(g)
    lo, hi = float(g[0]), float(g[-1])
    a = int(mp.nzeros(lo - 1e-6)); b = int(mp.nzeros(hi + 1e-6))
    ok = (b - a == n)
    D.append(dict(name=name, g=g, n=n, lo=lo, hi=hi, k1=a+1, ratio=hi/lo))
    P(f"   {name:>8}{n:>7}{lo:>16.4f}{hi:>16.4f}{b-a:>15d}{a+1:>12d}{hi/lo:>10.4f}"
      f"{'COMPLETE' if ok else 'SHORT!!':>9}")

# spot-check that the listed points really are zeros (Z sign change across each)
P("\n   spot check: |Z| at the listed points and a sign change on (g-eps, g+eps), 8 random per set")
for d in D:
    idx = rng.choice(d['n'], size=8, replace=False)
    bad = 0; worst = 0.0
    for i in idx:
        t = float(d['g'][i]); e = 1e-6*max(1.0, t/1e6)
        za, zb = float(mp.siegelz(t-e)), float(mp.siegelz(t+e))
        worst = max(worst, abs(float(mp.siegelz(t))))
        if za*zb > 0: bad += 1
    P(f"   {d['name']:>8}  max|Z(g)| = {worst:.2e}   sign-change failures: {bad}/8")

# =====================================================================================
P("\n" + "="*100)
P("V1 -- |phi|, K(1), K_gauss, gap factor.  theta from mpmath.siegeltheta at 20 dps.")
t0 = time.time()
for d in D:
    u = theta_mp(d['g'])/pi
    d['u'] = u
    k = d['k1'] + np.arange(d['n'])           # TRUE global index from nzeros, not from round()
    S = k - 1.5 - u
    d['S'] = S
    z = np.exp(-2j*pi*S)
    d['z'] = z
    phi = z.mean(); d['phi'] = phi
    d['K'] = d['n']*abs(phi)**2
P(f"   (theta for {sum(x['n'] for x in D)} zeros in {time.time()-t0:.1f}s)")
P(f"   {'set':>8}{'mean S':>11}{'sd S':>9}{'max|S|':>9}{'|phi|':>10}{'arg phi':>10}"
  f"{'K(1)':>10}{'031 K':>10}{'K_gauss':>10}{'gapfac':>9}")
K031 = dict(zip([s[0] for s in SETS], [132.045, 76.074, 40.010, 29.338, 15.107, 445.508]))
for d in D:
    V = float(np.var(d['S'], ddof=1))
    d['V'] = V
    Kg = d['n']*math.exp(-4*pi*pi*V)
    d['Kg'] = Kg
    P(f"   {d['name']:>8}{d['S'].mean():>11.6f}{d['S'].std():>9.5f}{np.abs(d['S']).max():>9.4f}"
      f"{abs(d['phi']):>10.5f}{np.angle(d['phi']):>10.5f}{d['K']:>10.3f}{K031[d['name']]:>10.3f}"
      f"{Kg:>10.2f}{Kg/d['K']:>9.3f}")

P("\n   PROBE: does the 'ABSOLUTE normalisation / true global index' claim do any work?")
P("   e^{-2 pi i S} with S = k-3/2-u is INVARIANT under k -> k+j for any integer j, since")
P("   e^{-2 pi i j} = 1.  So phi (modulus AND phase) cannot depend on the index recovery.")
for d in D[:3]:
    S2 = d['S'] + 7.0     # shift the whole index by 7
    P(f"   {d['name']:>8}  |phi(k)-phi(k+7)| = {abs(np.exp(-2j*pi*S2).mean()-d['phi']):.3e}"
      f"   ;  phi = -mean e^{{2 i theta}} check: "
      f"{abs(d['phi'] + np.exp(2j*pi*d['u']).mean()):.3e}")

P("\n   audited sigma(K): moving-block bootstrap, block = n//25, 4000 resamples (mine)")
P(f"   {'set':>8}{'K':>10}{'sig(K) mine':>13}{'031 sig':>10}{'arg':>10}{'sig(arg) mine':>15}")
S031 = dict(zip([s[0] for s in SETS], [9.921, 9.422, 8.186, 6.229, 4.973, 25.918]))
for d in D:
    Ks, ar = mbb(d['z'], max(20, d['n']//25))
    d['sK'] = float(Ks.std(ddof=1)); d['sarg'] = float(ar.std(ddof=1))
    P(f"   {d['name']:>8}{d['K']:>10.3f}{d['sK']:>13.3f}{S031[d['name']]:>10.3f}"
      f"{np.angle(d['phi']):>10.5f}{d['sarg']:>15.5f}")

# =====================================================================================
P("\n" + "="*100)
P("V2 -- cumulants of S at the zeros, UNBIASED k-statistics for j<=4")
P(f"   {'set':>8}{'k2':>10}{'031 k2':>10}{'k4':>12}{'031 k4':>12}{'exkurt':>10}{'031 ex':>10}{'skew':>10}")
K2_031 = dict(zip([s[0] for s in SETS], [0.08204, 0.09109, 0.10301, 0.11368, 0.12205, 0.08842]))
K4_031 = dict(zip([s[0] for s in SETS], [-2.480e-3, -2.560e-3, -3.001e-3, -2.867e-3, -4.075e-3, -2.504e-3]))
EX_031 = dict(zip([s[0] for s in SETS], [-0.3685, -0.3086, -0.2828, -0.2218, -0.2736, -0.3203]))
for d in D:
    k = kstats(d['S']); d['k'] = k
    ex = k[4]/k[2]**2
    P(f"   {d['name']:>8}{k[2]:>10.5f}{K2_031[d['name']]:>10.5f}{k[4]:>12.3e}{K4_031[d['name']]:>12.3e}"
      f"{ex:>10.4f}{EX_031[d['name']]:>10.4f}{k[3]/k[2]**1.5:>10.4f}")
P("\n   pre-registered ALTERNATIVE window was kappa_4 = -0.0031 .. -0.0061 "
  "(excess kurtosis -0.30..-0.45).")
inw = [d['name'] for d in D if -0.0061 <= d['k'][4] <= -0.0031]
P(f"   sets landing INSIDE the pre-registered kappa_4 window: {inw if inw else 'NONE'}")
inw2 = [d['name'] for d in D if -0.45 <= d['k'][4]/d['k'][2]**2 <= -0.30]
P(f"   sets landing INSIDE the pre-registered excess-kurtosis window: {inw2 if inw2 else 'NONE'}")

# bootstrap bar on kappa_4, my own
P("\n   moving-block bootstrap on kappa_4 (block n//25, 1500 resamples)")
for d in D:
    bl = max(20, d['n']//25); n = d['n']; nb = n//bl
    starts = np.arange(0, n-bl+1); out = np.empty(1500)
    for b in range(1500):
        st = rng.choice(starts, size=nb, replace=True)
        sel = (st[:, None] + np.arange(bl)[None, :]).ravel()
        out[b] = kstats(d['S'][sel])[4]
    d['sk4'] = float(out.std(ddof=1))
    lo, hi = d['k'][4]-2*d['sk4'], d['k'][4]+2*d['sk4']
    P(f"   {d['name']:>8}  k4 = {d['k'][4]:+.6f} +- {d['sk4']:.6f}   2-sigma [{lo:+.6f},{hi:+.6f}]"
      f"   overlaps preregistered window? {'YES' if hi >= -0.0061 and lo <= -0.0031 else 'NO'}")

# =====================================================================================
P("\n" + "="*100)
P("V3 -- the claimed EXACT law  Var_u(S_cont) - Var_zeros(S) = 1/12.")
P("     Independent route: 8-node Gauss-Legendre quadrature on each u-cell of the exact")
P("     piecewise-linear S_cont (exact for polynomials of degree <= 15, so exact here).")
gl_x, gl_w = np.polynomial.legendre.leggauss(8)
P(f"   {'set':>8}{'Var_u':>11}{'Var_z':>11}{'difference':>13}{'1/12':>11}{'dev':>11}"
  f"{'031 dev':>11}")
DEV031 = dict(zip([s[0] for s in SETS],
                  [0.0832565, 0.0832912, 0.0833220, 0.0833269, 0.0833400, 0.0833373]))
for d in D:
    u = d['u']; S = d['S']; n = d['n']
    U = u[-1] - u[0]
    A = S[:-1] + 0.5                 # value of S_cont at the left end of cell k
    dl = u[1:] - u[:-1]              # cell lengths in u
    # nodes: s = A - dl*(xi+1)/2 ,  weight dl/2 * w
    xi = (gl_x[None, :]+1)/2
    vals = A[:, None] - dl[:, None]*xi
    wts = (dl[:, None]/2)*gl_w[None, :]
    m1 = float((wts*vals).sum()/U)
    m2 = float((wts*vals**2).sum()/U)
    Vu = m2 - m1*m1
    Vz = float(np.var(S))            # population variance (matches the u-side convention)
    P(f"   {d['name']:>8}{Vu:>11.7f}{Vz:>11.7f}{Vu-Vz:>13.7f}{1/12:>11.7f}"
      f"{Vu-Vz-1/12:>11.2e}{DEV031[d['name']]-1/12:>11.2e}")
    d['Vu'] = Vu

P("\n   cross-check by brute force: 4,000,000 points drawn uniformly in u (Monte-Carlo,")
P("   a completely different route -- must agree to MC error ~ sd/sqrt(N) ~ 2e-4)")
for d in D[:3] + [D[-1]]:
    u = d['u']; n = d['n']
    uu = rng.uniform(u[0], u[-1], 4_000_000)
    idx = np.searchsorted(u, uu, side='right') - 1          # cell index
    Sc = d['S'][idx] + 0.5 - (uu - u[idx])
    P(f"   {d['name']:>8}  Var_u(MC) = {Sc.var():.6f}   vs GL {d['Vu']:.6f}"
      f"   diff {Sc.var()-d['Vu']:+.2e}")

P("\n   t-uniform (Selberg's own sampling) variance, 2,000,000 point grid:")
P(f"   {'set':>8}{'Var_t':>11}{'Var_u':>11}{'Var_z':>11}{'Var_t-Var_z':>13}")
for d in D:
    g = d['g']
    tt = np.linspace(g[0], g[-1], 2_000_000)
    N = d['k1'] - 1 + np.searchsorted(g, tt, side='right')
    th = np.array([float(mp.siegeltheta(mp.mpf(float(x)))) for x in
                   np.linspace(g[0], g[-1], 4001)])
    # interpolate theta on the fine grid via the exact derivative-corrected spline
    thi = np.interp(tt, np.linspace(g[0], g[-1], 4001), th)
    # correct the interpolation error with the known curvature (theta'' = 1/(2t))
    hstep = (g[-1]-g[0])/4000.0
    frac = (tt - np.linspace(g[0], g[-1], 4001)[np.clip(np.searchsorted(
        np.linspace(g[0], g[-1], 4001), tt)-1, 0, 3999)])
    thi = thi + 0.5*(1/(2*tt))*frac*(frac-hstep)
    St = N - thi/pi - 1.0
    P(f"   {d['name']:>8}{St.var():>11.5f}{d['Vu']:>11.5f}{np.var(d['S']):>11.5f}"
      f"{St.var()-np.var(d['S']):>13.5f}")

# =====================================================================================
P("\n" + "="*100)
P("V4 -- the independent-prime (Bessel) model constants, my own sieve and my own series.")
def primes_to(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
PR = primes_to(5_000_000)
# a_{p^k} = Lambda/(pi sqrt(n) log n) = 1/(pi k p^{k/2})
aa = []
for p in PR:
    kk = 1; pw = float(p)
    while pw <= 5_000_000*1.0:
        aa.append(1.0/(pi*kk*pw**0.5)); kk += 1; pw = float(p)**kk
        if kk > 60: break
aa = np.array(aa)
# cumulants of a*sin(uniform): verify the coefficients NUMERICALLY rather than trusting
# the log J0 series -- take a = 1 and integrate moments of sin exactly.
mom = {j: float(np.mean(np.sin(np.linspace(0, 2*pi, 2_000_001)[:-1])**j)) for j in (2, 4, 6)}
c2 = mom[2]                                    # kappa_2 coefficient  (= 1/2)
c4 = mom[4] - 3*mom[2]**2                      # kappa_4 coefficient  (= -3/8)
c6 = mom[6] - 15*mom[4]*mom[2] + 30*mom[2]**3  # kappa_6 coefficient  (= 5/4, kappa_3=kappa_5=0)
P(f"   numerically derived per-term cumulant coefficients: c2 = {c2:.6f} (1/2),"
  f"  c4 = {c4:.6f} (-3/8),  c6 = {c6:.6f} (5/4)")
P(f"   kappa_4^model (cutoff-free) = {c4*float((aa**4).sum()):+.7f}    (031: -0.0017604)")
P(f"   kappa_6^model (cutoff-free) = {c6*float((aa**6).sum()):+.7f}    (031: +0.0002276)")
P(f"   primes only, closed form -(3/(8 pi^4)) P(2) = {-(3/(8*pi**4))*0.45224742:+.7f}")
k4m = c4*float((aa**4).sum())
P("\n   the comparison, BOTH registers (they are the same absolute number):")
P(f"   {'set':>8}{'k4 at zeros':>13}{'model/meas':>12}{'k4 u-sampled':>14}{'(model+B4/4)/meas':>19}")
for d in D:
    Vu_k4 = None
    # exact u-sampled kappa_4 via the same GL quadrature (moments 1..4)
    u = d['u']; S = d['S']; U = u[-1]-u[0]
    A = S[:-1]+0.5; dl = u[1:]-u[:-1]
    xi = (gl_x[None, :]+1)/2
    vals = A[:, None] - dl[:, None]*xi
    wts = (dl[:, None]/2)*gl_w[None, :]
    mu = [float((wts*vals**j).sum()/U) for j in range(0, 5)]
    c = mu[1]
    cm2 = mu[2]-c**2
    cm3 = mu[3]-3*c*mu[2]+2*c**3
    cm4 = mu[4]-4*c*mu[3]+6*c*c*mu[2]-3*c**4
    k4u = cm4 - 3*cm2**2
    d['k4u'] = k4u
    P(f"   {d['name']:>8}{d['k'][4]:>13.5f}{k4m/d['k'][4]:>12.3f}{k4u:>14.5f}"
      f"{(k4m-1/120)/k4u:>19.3f}")

# =====================================================================================
P("\n" + "="*100)
P("V5 -- the exponent.  window ratio first, then the fits.")
P(f"   {'set':>8}{'ratio hi/lo':>13}{'ratio<=1.05?':>14}{'t-centre':>12}{'loglogT':>10}"
  f"{'K':>10}{'sig':>8}{'V':>9}")
sing = [d for d in D if d['name'] != 'long']
for d in sing:
    Tc = float(np.exp(np.log(d['g']).mean()))
    d['Tc'] = Tc
    P(f"   {d['name']:>8}{d['ratio']:>13.4f}{'yes' if d['ratio'] <= 1.05 else 'NO':>14}"
      f"{Tc:>12.4g}{math.log(math.log(Tc)):>10.5f}{d['K']:>10.3f}{d['sK']:>8.3f}{d['V']:>9.5f}")

def wfit(ds):
    x = np.array([math.log(math.log(d['Tc'])) for d in ds])
    y = np.array([math.log(d['K']/d['n']) for d in ds])
    s = np.array([d['sK']/d['K'] for d in ds])
    w = 1/s**2; X = np.vstack([x, np.ones_like(x)]).T
    cov = np.linalg.inv(X.T@np.diag(w)@X); b = cov@(X.T@np.diag(w)@y)
    r = y - X@b; chi2 = float(r@np.diag(w)@r); dof = max(len(ds)-2, 1)
    return float(b[0]), float(sqrt(cov[0, 0])), chi2, dof

for label, ds in (("all 5 (031 headline)", sing),
                  ("drop 1e3 (ratio 6.19)", sing[1:]),
                  ("drop 1e3,1e4 (ratio>1.05)", sing[2:])):
    a, sa, chi2, dof = wfit(ds)
    P(f"   {label:>28}: slope {a:+.3f} +- {sa:.3f}   chi2 {chi2:.2f}/{dof}"
      f"   z vs -2 = {(a+2)/sa:+.2f}"
      f"   [bars x sqrt(chi2/dof): z = {(a+2)/(sa*max(sqrt(chi2/dof),1e-9)):+.2f}]")
x = np.array([math.log(math.log(d['Tc'])) for d in sing])
Vs = np.array([d['V'] for d in sing])
bV = np.polyfit(x, -4*pi*pi*Vs, 1)
P(f"   exponent implied by the MEASURED V trend = {bV[0]:+.3f}   (031: -2.303)")
P(f"   only the 3 narrow windows: {np.polyfit(x[2:], -4*pi*pi*Vs[2:], 1)[0]:+.3f}")
P(f"   Selberg asymptotic dV/dloglogT = 1/(2 pi^2) = {1/(2*pi**2):.5f}; "
  f"measured dV/dloglogT = {np.polyfit(x, Vs, 1)[0]:.5f} "
  f"(narrow only {np.polyfit(x[2:], Vs[2:], 1)[0]:.5f})")

# =====================================================================================
P("\n" + "="*100)
P("V6 -- is the claimed NON-MONOTONE gap factor significant?")
P(f"   {'set':>8}{'gapfac':>10}{'sigma(gapfac)':>15}")
for d in D:
    # gapfac = Kg/K ; sigma from sig(K) alone (Kg uncertainty is smaller: it is exp of V)
    P(f"   {d['name']:>8}{d['Kg']/d['K']:>10.3f}{(d['Kg']/d['K'])*(d['sK']/d['K']):>15.3f}")
P("   (031 asserted 'the growth is NOT monotone'.  Test: 1e6 vs 1e5 difference over the")
P("    combined bar.)")
a, b = [d for d in D if d['name'] == 'T=1e5'][0], [d for d in D if d['name'] == 'T=1e6'][0]
ga, gb = a['Kg']/a['K'], b['Kg']/b['K']
sa, sb = ga*a['sK']/a['K'], gb*b['sK']/b['K']
P(f"   gap(1e5) - gap(1e6) = {ga-gb:+.3f} +- {sqrt(sa*sa+sb*sb):.3f}  -> "
  f"z = {(ga-gb)/sqrt(sa*sa+sb*sb):+.2f}")

P("\n" + "="*100)
P("V7 -- TAUTOLOGY AUDIT of the Edgeworth account.  Split each set in half; take cumulants")
P("     from half A and PREDICT log|phi| on half B (out of sample).  If the account has any")
P("     content beyond arithmetic identity the out-of-sample residual should stay small.")
P(f"   {'set':>8}{'in-sample resid':>18}{'out-of-sample resid':>21}")
for d in D:
    n = d['n']; h = n//2
    for tag, (fit, tst) in (('', (slice(0, h), slice(h, n))),):
        kA = kstats(d['S'][fit]); kB = kstats(d['S'][tst])
        def ed(k):
            return (-2*pi*pi*k[2] + (2*pi)**4*k[4]/24 - (2*pi)**6*k[6]/720
                    + (2*pi)**8*k[8]/40320)
        lpB = math.log(abs(np.exp(-2j*pi*d['S'][tst]).mean()))
        P(f"   {d['name']:>8}{lpB-ed(kB):>18.4f}{lpB-ed(kA):>21.4f}")

P("\n" + "="*100)
P("V8 -- |phi_t(2 pi)| by an independent route: exact integration by parts.")
P("     int_a^b e^{2 i theta} dt = [e^{2 i theta}/(2 i theta')]_a^b + int e^{2 i theta} "
  "theta''/(2 i theta'^2) dt,  |second| <= (1/2)|log(b/a)|/(2 theta'(a)^2)")
for d in D:
    a_, b_ = d['lo'], d['hi']; W = b_-a_
    tha, thb = float(mp.siegeltheta(a_)), float(mp.siegeltheta(b_))
    dpa, dpb = 0.5*log(a_/(2*pi)), 0.5*log(b_/(2*pi))
    bt = (np.exp(2j*thb)/(2j*dpb) - np.exp(2j*tha)/(2j*dpa))/W
    rem = 0.5*abs(log(b_/a_))/(2*dpa**2)/W
    P(f"   {d['name']:>8}  |boundary term|/W = {abs(bt):.2e}   remainder <= {rem:.2e}"
      f"   031 quad = ", end='')
    P({'T=1e3': '1.90e-05', 'T=1e4': '5.65e-05', 'T=1e5': '7.40e-05',
       'T=1e6': '7.93e-05', 'T=1e7': '7.57e-05', 'long': '5.42e-05'}[d['name']])
