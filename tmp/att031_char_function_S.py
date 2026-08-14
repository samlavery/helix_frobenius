"""ATTEMPT 031 -- the tau = 1 point mass read as the CHARACTERISTIC FUNCTION of S at 2 pi.

PAIRING
  house    : the exact integer-frequency identity  K(m) = n |<e^{-2 pi i m S(gamma)}>|^2 ,
             which converts a form-factor measurement into a characteristic-function
             measurement of S (attempts 016/022).
  classical: Selberg's central limit theorem for S(t) and its non-Gaussian corrections read
             through the cumulant (Edgeworth) expansion  <e^{i x S}> = exp(sum_j kappa_j (ix)^j/j!).
  mechanism: the identity says the tau=1 line IS phi_S(-2 pi).  Its deviation from the Gaussian
             value exp(-2 pi^2 V) is therefore the NON-GAUSSIANITY of S at one exactly specified
             argument -- no binning, no histogram error bars.  DC first: the common mode of
             log|phi| is -2 pi^2 kappa_2, computed exactly, and only the remainder is in question.

WHAT IS BEING EXPLAINED.  022 measured K(1) = 132.045, 76.074, 40.010, 29.338, 15.107 at
T = 1e3..1e7 against the Gaussian prediction n exp(-4 pi^2 V) = 202.6, 118.4, 71.3, 45.0, 34.0,
i.e. measured is BELOW Gaussian by a factor 1.5 to 2.2 that GROWS with height.

============================ STATED NULL (pre-registered, before running) =====================
The attempt is a NEGATIVE if ANY of the following holds.

 N1  GATE.  The zero sets are not complete -- max |S| >= 1.5, or S drifts by a full unit across
     a set, or the census |n - (theta(g_last)-theta(g_first))/pi - 1| > 2.  (The algebraic
     identity e^{2 pi i m u_k} = (-1)^m e^{-2 pi i m S_k} is a TAUTOLOGY once S := k-3/2-u, so
     it is NOT the gate; the gate with content is completeness of the zero list.  Stated here
     rather than discovered later.)

 N2  The truncated cumulant series does NOT close the gap: the prediction
        log|phi| = -2 pi^2 k2 + (2pi)^4 k4/24 - (2pi)^6 k6/720 + (2pi)^8 k8/40320
     misses the measured log|phi| by more than +-0.05 (i.e. more than 10% in K) at three or
     more of the five single-height sets, OR the successive terms fail to decrease in modulus
     (series not usably convergent at x = 2 pi).

 N3  The exponent of K(1)/n vs log T is NOT distinguishable from the Selberg/Gaussian value:
     |slope + 2| < 2 sigma_slope with AUDITED (block-bootstrap, not nominal) error bars.
     Equally reportable: the slope is not distinguishable from the exponent implied by the
     MEASURED V trend, d(-4 pi^2 V)/d log log T.

 N4  PHASE.  arg <e^{-2 pi i S}> is not consistent with 0 (mod the exact kappa_1, kappa_3
     prediction -2 pi k1 + (2pi)^3 k3/6) within the audited bar.

PRE-REGISTERED ALTERNATIVE, with its own numbers: K is BELOW Gaussian because S at the zeros is
platykurtic, kappa_4 < 0; closing a factor 1.5-2.2 in K needs
    (2 pi)^4 kappa_4/24 = -0.203 .. -0.394,  i.e.  kappa_4 = -0.0031 .. -0.0061,
i.e. standardised excess kurtosis kappa_4/kappa_2^2 = -0.30 .. -0.45 at V ~ 0.10.

============================ VALIDITY CRITERION, COMPUTED BEFORE RUNNING ======================
phi_hat is an average of n unit phasors; write phi_hat = phi + eps.  Then
    E[n |phi_hat|^2] = K_true + Cbar,   Cbar := sum_l Cov(z_k, conj(z_{k+l}))
and Cbar is exactly the local form-factor background near tau = 1, measured in 016/023 to be
~1.  Hence
    K_meas is biased HIGH by ~Cbar ~ 1, and  sigma(K) ~ sqrt(Cbar^2 + 2 K Cbar) ~ sqrt(1+2K).
At K = 15 (T=1e7) that is sigma ~ 5.6, i.e. 37 PERCENT.  So:
  * the +-1 additive bias must be removed before any power-law fit;
  * a five-point exponent fit carries a slope error of order
        sigma_slope ~ sqrt( sum_i (sigma_i/K_i)^2 x_i^2 ) / sum x_i^2  ~ 0.4 ,
    which is COMPARABLE TO THE 0.75 SEPARATION between -2 and -2.75.  This is computed here,
    before running, precisely so that a "distinguishable" verdict cannot be manufactured after.
  * the T=1e3 set spans a ratio 6.19 in t and the long set 1414, so NEITHER is a single height;
    they are reported but excluded from the exponent fit.
  * MIXTURE CHECK (direction, computed in advance): pooling heights averages phi over V, and by
    Jensen <exp(-2 pi^2 V)> >= exp(-2 pi^2 <V>), so mixing pushes K UP.  The observed gap is
    DOWNWARD.  Mixture cannot be the explanation, in either the 1e3 set or the long set.

NOISE AUDIT / POSITIVE CONTROL that fails by MISSING STRUCTURE (not by more cancellation):
  surrogate S~ built by Fourier phase randomisation of the measured S -- SAME variance, SAME
  autocovariance, Gaussianised marginal, arithmetic shape DESTROYED.  If the pipeline is sound
  the surrogate must land ON the Gaussian law n exp(-4 pi^2 V) while the real data does not.
  Second control: iid Gaussian S of matched variance.
"""
import numpy as np, math, sys, os
from math import pi, log, sqrt

def P(*a): print(*a); sys.stdout.flush()
rng = np.random.default_rng(20260812)
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- theta ------
def theta(t):
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
            + 31/(80640*t**5) + 127/(430080*t**7))

SETS = [('T=1e3', 'att010_zeros_1e+03.npy', True),
        ('T=1e4', 'att010_zeros_1e+04.npy', True),
        ('T=1e5', 'att010_zeros_1e+05.npy', True),
        ('T=1e6', 'att010_zeros_1e+06.npy', True),
        ('T=1e7', 'att010_zeros_1e+07.npy', True),
        ('long[14,2e4]', 'att019_zeros_to20k.npy', False)]

# ------------------------------------------------------- cumulants -----------
def cumulants(x, order=8):
    """central-moment -> cumulant conversion, kappa_1..kappa_order."""
    m1 = x.mean(); c = x - m1
    mu = {j: float((c**j).mean()) for j in range(2, order+1)}
    k = {1: float(m1)}
    k[2] = mu[2]
    if order >= 3: k[3] = mu[3]
    if order >= 4: k[4] = mu[4] - 3*mu[2]**2
    if order >= 5: k[5] = mu[5] - 10*mu[3]*mu[2]
    if order >= 6: k[6] = mu[6] - 15*mu[4]*mu[2] - 10*mu[3]**2 + 30*mu[2]**3
    if order >= 7: k[7] = mu[7] - 21*mu[5]*mu[2] - 35*mu[4]*mu[3] + 210*mu[3]*mu[2]**2
    if order >= 8: k[8] = (mu[8] - 28*mu[6]*mu[2] - 56*mu[5]*mu[3] - 35*mu[4]**2
                           + 420*mu[4]*mu[2]**2 + 560*mu[3]**2*mu[2] - 630*mu[2]**4)
    return k

def logphi_from_cumulants(k, x=-2*pi, order=8):
    """log phi(x) = sum_j kappa_j (i x)^j / j! ; returns list of complex terms j=1..order."""
    terms = []
    f = 1.0
    for j in range(1, order+1):
        f *= j
        terms.append(k[j]*((1j*x)**j)/f)
    return terms

# --------------------------------------------------- long-run variance -------
def Cbar(z, phi, maxlag=400):
    """sum_l Cov(z_k, conj(z_{k+l})) with a Bartlett taper -- the K noise floor."""
    n = len(z); w = z - phi
    tot = float((np.abs(w)**2).mean())          # l = 0
    for l in range(1, maxlag+1):
        c = np.vdot(w[l:], w[:-l])/n            # sum_k conj(w[l+k]) w[k] / n
        tap = 1.0 - l/(maxlag+1.0)
        tot += 2*tap*float(c.real)
    return tot

def block_boot_K(z, nblk=40, nboot=3000):
    n = len(z); L = n//nblk
    idx0 = np.arange(0, n-L+1)
    Ks = np.empty(nboot); mods = np.empty(nboot); args = np.empty(nboot)
    for b in range(nboot):
        st = rng.choice(idx0, size=nblk, replace=True)
        sel = (st[:, None] + np.arange(L)[None, :]).ravel()
        ph = z[sel].mean()
        mods[b] = abs(ph); args[b] = np.angle(ph); Ks[b] = n*abs(ph)**2
    return Ks, mods, args

def boot_cum(x, nblk=40, nboot=1500, order=8):
    n = len(x); L = n//nblk; idx0 = np.arange(0, n-L+1)
    out = {j: np.empty(nboot) for j in range(1, order+1)}
    for b in range(nboot):
        st = rng.choice(idx0, size=nblk, replace=True)
        sel = (st[:, None] + np.arange(L)[None, :]).ravel()
        k = cumulants(x[sel], order)
        for j in range(1, order+1): out[j][b] = k[j]
    return {j: (out[j].mean(), out[j].std(ddof=1)) for j in out}

# =============================================================================
P(__doc__)
P("="*100)
P("STAGE 0 -- theta cross-check against mpmath.siegeltheta")
try:
    import mpmath as mp
    for t in (14.134725, 1000.0, 1e5, 1e7):
        a = float(theta(np.array([t]))[0]); b = float(mp.siegeltheta(t))
        P(f"   t = {t:>12.4f}   asymptotic {a:.12f}   mpmath {b:.12f}   diff {a-b:+.2e}")
except Exception as e:
    P("   mpmath unavailable:", e)

P("\n" + "="*100)
P("STAGE 1 -- GATE: completeness of the zero lists, and the (tautological) identity")
DATA = []
for name, f, single in SETS:
    p = os.path.join(HERE, f)
    if not os.path.exists(p):
        P(f"   MISSING {f}"); continue
    g = np.load(p); n = len(g)
    u = theta(g)/pi
    k1 = int(round(u[0] + 1.5))
    k = k1 + np.arange(n)
    S = k - 1.5 - u
    shift = int(round(S.mean()))
    if shift != 0:
        k1 -= shift; k = k1 + np.arange(n); S = k - 1.5 - u
    census = (theta(np.array([g[-1]]))[0] - theta(np.array([g[0]]))[0])/pi
    drift = float(np.polyfit(np.arange(n), S, 1)[0])*n
    Tc = float(np.exp(np.log(g).mean()))
    ok = (np.abs(S).max() < 1.5) and abs(census - (n-1)) < 2.5 and abs(drift) < 0.5
    P(f"   {name:>14} n={n:5d}  k1={k1:7d}  mean S={S.mean():+.5f}  sd S={S.std():.5f} "
      f" max|S|={np.abs(S).max():.3f}  census {census:.2f} vs {n-1}  drift {drift:+.3f}  "
      f"{'PASS' if ok else '*** FAIL ***'}")
    DATA.append(dict(name=name, single=single, g=g, u=u, S=S, n=n, Tc=Tc,
                     lo=float(g[0]), hi=float(g[-1])))

P("\n   identity  sum_k e^{2 pi i m u_k}  ==  (-1)^m sum_k e^{-2 pi i m S_k}   (complex, all m):")
for d in DATA:
    worst = 0.0
    for m in (1, 2, 3, 6):
        A = np.exp(2j*pi*m*d['u']).sum()
        B = ((-1)**m)*np.exp(-2j*pi*m*d['S']).sum()
        worst = max(worst, abs(A-B)/max(abs(A), 1.0))
    P(f"   {d['name']:>14}  max relative complex mismatch over m in 1,2,3,6 = {worst:.3e}")
P("   NOTE (rule 2, applied to my own gate): this identity is ALGEBRAIC -- S was defined as")
P("   k-3/2-u, so it cannot fail.  The line above is a floating-point check only.  The gate")
P("   with mathematical content is the completeness table above it.")

# =============================================================================
P("\n" + "="*100)
P("STAGE 2 -- phi = <e^{-2 pi i S}> : MODULUS and PHASE, with the noise floor removed")
P(f"   {'set':>14}{'n':>6}{'|phi|':>9}{'arg phi':>10}{'K_meas':>10}{'Cbar':>8}"
  f"{'K_deb':>9}{'sig(K)':>9}{'K/n':>10}")
for d in DATA:
    z = np.exp(-2j*pi*d['S'])
    phi = z.mean(); n = d['n']
    K = n*abs(phi)**2
    cb = Cbar(z, phi)
    Ks, mods, args = block_boot_K(z)
    sK = float(Ks.std(ddof=1))
    d.update(phi=phi, K=K, cb=cb, Kdeb=K-cb, sK=sK, z=z,
             s_mod=float(mods.std(ddof=1)), s_arg=float(args.std(ddof=1)))
    P(f"   {d['name']:>14}{n:>6}{abs(phi):>9.5f}{np.angle(phi):>10.5f}{K:>10.3f}{cb:>8.3f}"
      f"{K-cb:>9.3f}{sK:>9.3f}{(K-cb)/n:>10.6f}")
P("   (sig(K) = block bootstrap, 40 blocks x 3000 resamples -- AUDITED, not nominal.)")
P("   (Cbar = Bartlett-tapered long-run variance of z = the local form-factor background;")
P("    016/023 measured that background at 1.00 near tau=1, so Cbar~1 is a consistency check.)")

# =============================================================================
P("\n" + "="*100)
P("STAGE 3 -- CUMULANTS of S at the zeros, and the Edgeworth account of log|phi|")
P(f"   {'set':>14}" + "".join(f"{'k'+str(j):>12}" for j in range(1, 9)))
for d in DATA:
    k = cumulants(d['S'], 8); d['k'] = k
    P(f"   {d['name']:>14}" + "".join(f"{k[j]:>12.3e}" for j in range(1, 9)))
P(f"\n   standardised:  k3/k2^1.5 (skew), k4/k2^2 (excess kurt), k6/k2^3, k8/k2^4")
for d in DATA:
    k = d['k']
    P(f"   {d['name']:>14}   skew {k[3]/k[2]**1.5:+8.4f}   exkurt {k[4]/k[2]**2:+8.4f}"
      f"   k6/k2^3 {k[6]/k[2]**3:+9.4f}   k8/k2^4 {k[8]/k[2]**4:+10.3f}")

P("\n   bootstrap bars on kappa_2, kappa_3, kappa_4, kappa_6 (40 blocks x 1500):")
for d in DATA:
    bc = boot_cum(d['S']); d['bc'] = bc
    P(f"   {d['name']:>14}  k2 {bc[2][0]:.5f}+-{bc[2][1]:.5f}   k3 {bc[3][0]:+.5f}+-{bc[3][1]:.5f}"
      f"   k4 {bc[4][0]:+.6f}+-{bc[4][1]:.6f}   k6 {bc[6][0]:+.6f}+-{bc[6][1]:.6f}")

P("\n   log|phi| accounted term by term.  x = -2 pi.  Re parts: j=2 -2pi^2 k2, j=4 +(2pi)^4k4/24,")
P("   j=6 -(2pi)^6k6/720, j=8 +(2pi)^8k8/40320.")
P(f"   {'set':>14}{'meas':>10}{'j=2':>10}{'+j=4':>10}{'+j=6':>10}{'+j=8':>10}{'resid8':>10}{'K_gauss':>10}{'gapfac':>8}")
for d in DATA:
    tm = logphi_from_cumulants(d['k'])
    meas = math.log(abs(d['phi']))
    part = 0.0; cum = []
    for j in (2, 4, 6, 8):
        part += tm[j-1].real; cum.append(part)
    Kg = d['n']*math.exp(-4*pi*pi*d['k'][2])
    d['Kg'] = Kg; d['edge'] = cum; d['meas_lp'] = meas
    P(f"   {d['name']:>14}{meas:>10.4f}{cum[0]:>10.4f}{cum[1]:>10.4f}{cum[2]:>10.4f}"
      f"{cum[3]:>10.4f}{meas-cum[3]:>10.4f}{Kg:>10.2f}{Kg/max(d['K'],1e-12):>8.3f}")
P("   (gapfac = K_gauss/K_meas -- 022 reported 1.5 to 2.2 growing with height.)")

P("\n   term moduli (is the series usably convergent at x = 2 pi?):")
for d in DATA:
    tm = logphi_from_cumulants(d['k'])
    P(f"   {d['name']:>14}  " + "  ".join(f"j={j}:{abs(tm[j-1]):.4f}" for j in range(2, 9)))

P("\n   PHASE test.  predicted arg phi = -2 pi k1 + (2pi)^3 k3/6 - (2pi)^5 k5/120 + (2pi)^7k7/5040")
P(f"   {'set':>14}{'arg meas':>11}{'sig(arg)':>10}{'j=1':>10}{'+j=3':>10}{'+j=5':>10}{'+j=7':>10}")
for d in DATA:
    tm = logphi_from_cumulants(d['k'])
    part = 0.0; cum = []
    for j in (1, 3, 5, 7):
        part += tm[j-1].imag; cum.append(part)
    P(f"   {d['name']:>14}{np.angle(d['phi']):>11.5f}{d['s_arg']:>10.5f}"
      + "".join(f"{c:>10.5f}" for c in cum))

# =============================================================================
P("\n" + "="*100)
P("STAGE 4 -- the whole characteristic function: where does the Gaussian break?")
P("   D(x) := log|phi(x)| + x^2 k2/2   (== 0 for an exact Gaussian).  Compare with the pure")
P("   kappa_4 term x^4 k4/24.")
XS = [1.0, 2.0, 3.0, 4.0, 5.0, 2*pi, 7.0, 8.0]
P(f"   {'set':>14}" + "".join(f"{'x='+f'{x:.2f}':>13}" for x in XS))
for d in DATA:
    row = []
    for x in XS:
        ph = np.exp(1j*x*d['S']).mean()
        row.append(math.log(abs(ph)) + x*x*d['k'][2]/2)
    d['Dcurve'] = row
    P(f"   {d['name']:>14}" + "".join(f"{v:>13.4f}" for v in row))
P(f"   {'k4 term':>14}" + "".join(f"{'':>13}" for x in XS))
for d in DATA:
    P(f"   {d['name']:>14}" + "".join(f"{x**4*d['k'][4]/24:>13.4f}" for x in XS))

# =============================================================================
P("\n" + "="*100)
P("STAGE 5 -- POSITIVE CONTROL that must fail by MISSING STRUCTURE")
P("   (a) Fourier-phase-randomised surrogate: identical variance AND autocovariance,")
P("       Gaussianised marginal, arithmetic shape destroyed.  Must land ON n exp(-4 pi^2 V).")
P("   (b) iid Gaussian of matched variance.")
P(f"   {'set':>14}{'K_meas':>10}{'K_gauss':>10}{'K_surrFPR':>18}{'K_iidG':>18}")
for d in DATA:
    n = d['n']; S = d['S'] - d['S'].mean()
    F = np.fft.rfft(S)
    Ka, Kb = [], []
    for _ in range(60):
        ph = rng.uniform(0, 2*pi, len(F)); ph[0] = 0.0
        if len(S) % 2 == 0: ph[-1] = 0.0
        Ss = np.fft.irfft(np.abs(F)*np.exp(1j*ph), n=n)
        Ss = Ss*(S.std()/Ss.std()) + d['S'].mean()
        Ka.append(n*abs(np.exp(-2j*pi*Ss).mean())**2)
        Sg = rng.normal(d['S'].mean(), S.std(), n)
        Kb.append(n*abs(np.exp(-2j*pi*Sg).mean())**2)
    Ka = np.array(Ka); Kb = np.array(Kb)
    P(f"   {d['name']:>14}{d['K']:>10.2f}{d['Kg']:>10.2f}"
      f"{Ka.mean():>12.2f}+-{Ka.std(ddof=1):<5.2f}{Kb.mean():>12.2f}+-{Kb.std(ddof=1):<5.2f}")

# =============================================================================
P("\n" + "="*100)
P("STAGE 6 -- the exponent.  K/n vs log T, AUDITED bars, single-height sets only.")
sing = [d for d in DATA if d['single']]
x = np.array([math.log(math.log(d['Tc'])) for d in sing])
yK = np.array([d['Kdeb'] for d in sing])
sK = np.array([d['sK'] for d in sing])
y = np.log(yK/np.array([d['n'] for d in sing]))
sy = sK/yK
P(f"   {'set':>14}{'t-centre':>12}{'ratio hi/lo':>13}{'loglog T':>10}{'K_deb':>10}{'sig':>8}{'K/n':>11}{'rel sig':>9}")
for d, xi in zip(sing, x):
    P(f"   {d['name']:>14}{d['Tc']:>12.4g}{d['hi']/d['lo']:>13.4f}{xi:>10.5f}{d['Kdeb']:>10.3f}"
      f"{d['sK']:>8.3f}{d['Kdeb']/d['n']:>11.6f}{d['sK']/d['Kdeb']:>9.3f}")

w = 1.0/sy**2
X = np.vstack([x, np.ones_like(x)]).T
W = np.diag(w)
cov = np.linalg.inv(X.T @ W @ X)
beta = cov @ (X.T @ W @ y)
resid = y - X @ beta
chi2 = float(resid @ W @ resid)
slope, sslope = float(beta[0]), float(sqrt(cov[0, 0]))
P(f"\n   weighted fit  log(K/n) = a * loglog T + b :  a = {slope:+.3f} +- {sslope:.3f}"
  f"   (chi2 = {chi2:.2f} on {len(x)-2} dof)")
P(f"   z vs the Selberg/Gaussian exponent -2 :  {(slope+2)/sslope:+.2f} sigma")

# exponent implied by the MEASURED V trend
Vs = np.array([d['k'][2] for d in sing])
bV = np.polyfit(x, -4*pi*pi*Vs, 1)
P(f"   exponent implied by measured V trend d(-4 pi^2 V)/d loglog T = {bV[0]:+.3f}"
  f"   (V = {', '.join(f'{v:.4f}' for v in Vs)})")
P(f"   z vs that                                :  {(slope-bV[0])/sslope:+.2f} sigma")
# unweighted, for comparison
bu = np.polyfit(x, y, 1)
P(f"   unweighted OLS slope (what 022 would have reported) = {bu[0]:+.3f}")
P(f"   raw (un-debiased) unweighted slope                   = "
  f"{np.polyfit(x, np.log(np.array([d['K'] for d in sing])/np.array([d['n'] for d in sing])), 1)[0]:+.3f}")

# Monte-Carlo the slope error honestly: resample K within its audited bar
mc = []
for _ in range(20000):
    yy = np.log(np.maximum(yK + rng.normal(0, sK), 1e-3)/np.array([d['n'] for d in sing]))
    mc.append(np.polyfit(x, yy, 1)[0])
mc = np.array(mc)
P(f"   Monte-Carlo slope distribution (unweighted OLS, K perturbed by its audited sigma):")
P(f"      mean {mc.mean():+.3f}   sd {mc.std(ddof=1):.3f}   16/50/84 pct "
  f"{np.percentile(mc,16):+.3f} / {np.percentile(mc,50):+.3f} / {np.percentile(mc,84):+.3f}")
P(f"      P(slope > -2) = {(mc > -2).mean():.4f}    P(slope < -2.746) = {(mc < -2.746).mean():.4f}")

P("\n" + "="*100)
P("STAGE 7 -- gap factor vs height, and what the cumulants buy")
P(f"   {'set':>14}{'K_gauss/K_meas':>16}{'K_gauss/K_deb':>15}{'K_edge/K_deb':>14}{'exkurt':>9}")
for d in DATA:
    Ke = d['n']*math.exp(2*d['edge'][3])
    d['Ke'] = Ke
    P(f"   {d['name']:>14}{d['Kg']/d['K']:>16.3f}{d['Kg']/max(d['Kdeb'],1e-9):>15.3f}"
      f"{Ke/max(d['Kdeb'],1e-9):>14.3f}{d['k'][4]/d['k'][2]**2:>9.4f}")
P("\n   K_edge uses the 4-term Edgeworth log|phi|; a value near 1.000 means the cumulants")
P("   through kappa_8 fully account for the deviation from Gaussian.")
