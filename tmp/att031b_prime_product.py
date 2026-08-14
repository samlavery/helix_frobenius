"""ATTEMPT 031, part B -- the DC-FIRST step that part A was missing, plus the restatement check.

RULE-2 SELF-AUDIT OF PART A.  "The cumulant series accounts for the gap" is very nearly a
TAUTOLOGY: the cumulants are computed from the same sample as |phi|, so a convergent Edgeworth
series MUST reproduce it.  The only non-trivial content of part A stage 3 is (i) that the series
CONVERGES at x = 2 pi (term moduli 1.62, 0.16, 0.037, 0.011) so a low-order description suffices,
and (ii) that ONE number, kappa_4 < 0, carries ~80% of the deviation.  That is a description,
not a prediction.  Part B supplies the prediction.

DC FIRST, EXACTLY.  Under Selberg's own prime-sum representation
        S(t) = -(1/pi) sum_{n=p^k} Lambda(n) sin(t log n)/(sqrt(n) log n) ,  a_n := Lambda(n)/(pi sqrt(n) log n)
with the phases t*log n taken independent and uniform (the standard random model), each summand
is an ARCSINE variable a_n sin(theta), whose characteristic function is exactly J_0(a_n x).
Therefore the ENTIRE characteristic function has a closed form -- no estimation, no expansion:

        log |phi_S(x)|  =  sum_n log J_0(a_n x) ,       and at x = 2 pi,  a_n x = 2/(k p^{k/2}).

Its cumulants are likewise exact:  kappa_2 = sum a^2/2,  kappa_4 = -(3/8) sum a^4,
kappa_6 = (5/4) sum a^6  (from log J_0(z) = -z^2/4 - z^4/64 - z^6/576 - ...).
Note kappa_2 DIVERGES like (1/2pi^2) loglog X while kappa_4 CONVERGES:
        kappa_4 -> -(3/(8 pi^4)) sum_p p^{-2} = -(3/(8 pi^4)) * 0.4522474 = -0.0017413 ,
essentially independent of the cutoff.  So the model has exactly ONE free parameter (the cutoff
X, fixed by matching the measured kappa_2 -- the DC mode) and then PREDICTS kappa_4, kappa_6 and
log|phi(2 pi)| with nothing left to tune.

============================== PRE-REGISTERED, BEFORE RUNNING =================================
B1.  THE t-SAMPLED CHARACTERISTIC FUNCTION AT x = 2 pi IS ZERO, EXACTLY AND FOR A TRIVIAL REASON.
     S(t) = N(t) - theta(t)/pi - 1 with N INTEGER, so
         e^{-2 pi i S(t)} = e^{2 i theta(t)}   identically,
     and (1/W) int e^{2i theta} dt has NO stationary point (2 theta' = log(t/2pi) > 0), so by one
     integration by parts   |phi_t(2 pi)| <= 1/(W theta'(T)).
     PRE-COMPUTED: 6.1e-5 (T=1e3 set), ..., 7.6e-5 (T=1e7 set) -- against the AT-ZEROS
     |phi| = 0.160 .. 0.060.  NULL for B1: |phi_t(2 pi)| > 0.01 anywhere, i.e. the point mass is
     a property of S itself rather than of sampling S at its own jump points.
B2.  THE RANDOM MODEL, calibrated on kappa_2 alone, predicts kappa_4 and log|phi(2 pi)|.
     I have already computed kappa_4^model = -0.001741 by hand against part A's measured
     -0.00248 .. -0.00408, so I EXPECT THIS NULL TO HOLD (model too small by ~1.5-2.3x) and say
     so in advance.  NULL for B2: |kappa_4^model / kappa_4^meas - 1| > 0.30 at a majority of sets.
B3.  EXPONENT DECOMPOSITION.  d log(K/n)/d loglog T splits as 2*d/dloglogT of the j=2, 4, 6, 8
     Edgeworth terms.  If the j>=4 part is a NON-VANISHING fraction of the total, the -2.75
     exponent is not asymptotic and the (log T)^{-2} law is a statement about the j=2 term only.
     NULL for B3: the j>=4 slope contribution is < 5% of the total (then -2 is the whole story).
"""
import numpy as np, math, os, sys
from math import pi, log, sqrt
from scipy.special import j0

def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
rng = np.random.default_rng(31031)

def theta(t):
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
            + 31/(80640*t**5) + 127/(430080*t**7))
def dtheta(t):
    t = np.asarray(t, float)
    return 0.5*np.log(t/(2*pi)) - 1/(48*t**2) - 21/(5760*t**4)

SETS = [('T=1e3', 'att010_zeros_1e+03.npy'), ('T=1e4', 'att010_zeros_1e+04.npy'),
        ('T=1e5', 'att010_zeros_1e+05.npy'), ('T=1e6', 'att010_zeros_1e+06.npy'),
        ('T=1e7', 'att010_zeros_1e+07.npy'), ('long[14,2e4]', 'att019_zeros_to20k.npy')]

def cumulants(x, order=8):
    m1 = x.mean(); c = x - m1
    mu = {j: float((c**j).mean()) for j in range(2, order+1)}
    k = {1: float(m1), 2: mu[2], 3: mu[3], 4: mu[4]-3*mu[2]**2,
         5: mu[5]-10*mu[3]*mu[2],
         6: mu[6]-15*mu[4]*mu[2]-10*mu[3]**2+30*mu[2]**3,
         7: mu[7]-21*mu[5]*mu[2]-35*mu[4]*mu[3]+210*mu[3]*mu[2]**2,
         8: (mu[8]-28*mu[6]*mu[2]-56*mu[5]*mu[3]-35*mu[4]**2+420*mu[4]*mu[2]**2
             +560*mu[3]**2*mu[2]-630*mu[2]**4)}
    return k

# ---------------------------------------------------------------- primes -----
def primes_to(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

PR = primes_to(2_000_000)
def a_list(X):
    """a_n = Lambda(n)/(pi sqrt n log n) for prime powers n = p^k <= X."""
    out = []
    for p in PR:
        if p > X: break
        k = 1; n = int(p)
        while n <= X:
            out.append(1.0/(pi*k*p**(k/2.0)))
            k += 1; n = p**k
    return np.array(out)

def model_from_kappa2(k2_target, lo=3.0, hi=1e12):
    """choose cutoff X so that sum a^2/2 = k2_target (the DC mode), by bisection."""
    def f(X):
        a = a_list(X); return (a*a).sum()/2 - k2_target
    for _ in range(80):
        mid = math.sqrt(lo*hi)
        if f(mid) < 0: lo = mid
        else: hi = mid
    X = math.sqrt(lo*hi); a = a_list(X)
    return X, a

P(__doc__)
P("="*100)
P("B0 -- the model's cutoff-free constants")
aFull = a_list(2_000_000)
P(f"   sum_p p^-2 (all p)          = {float((1.0/PR.astype(float)**2).sum()):.7f}  (prime zeta P(2) = 0.4522474)")
P(f"   kappa_4^model (X -> inf)    = {-(3/8)*float((aFull**4).sum()):+.7f}")
P(f"   kappa_6^model (X -> inf)    = {(5/4)*float((aFull**6).sum()):+.7f}")

# ============================================================================
P("\n" + "="*100)
P("B1 -- the t-SAMPLED characteristic function at x = 2 pi  (exact identity e^{-2piiS}=e^{2i theta})")
P(f"   {'set':>14}{'W':>10}{'bound':>12}{'|phi_t| quad':>15}{'|phi_z|':>13}{'ratio':>10}")
ROWS = []
for name, f in SETS:
    p = os.path.join(HERE, f)
    g = np.load(p); n = len(g)
    u = theta(g)/pi
    k1 = int(round(u[0]+1.5)); k = k1+np.arange(n); S = k-1.5-u
    sh = int(round(S.mean()));  k1 -= sh; k = k1+np.arange(n); S = k-1.5-u
    phi_z = np.exp(-2j*pi*S).mean()
    T0, T1 = float(g[0]), float(g[-1]); W = T1-T0
    # exact oscillatory mean by fine trapezoid (step << period pi/theta')
    step = min(0.005, 0.02*pi/float(dtheta(np.array([T1]))[0]))
    M = int(W/step)+1
    tt = np.linspace(T0, T1, M)
    val = np.trapezoid(np.exp(2j*theta(tt)), tt)/W
    bnd = 1.0/(W*float(dtheta(np.array([T0]))[0]))
    P(f"   {name:>14}{W:>10.1f}{bnd:>18.2e}{abs(val):>15.2e}{abs(phi_z):>13.5f}{abs(phi_z)/abs(val):>10.3g}")
    ROWS.append(dict(name=name, g=g, S=S, k1=k1, u=u, n=n, phi_z=phi_z, T0=T0, T1=T1,
                     Tc=float(np.exp(np.log(g).mean()))))
P("   B1 verdict: |phi_t(2 pi)| is 3-4 orders below |phi_zeros|.  The tau=1 point mass is created")
P("   ENTIRELY by sampling S at its own jump points; the t-marginal of S has nothing at x=2 pi.")

# ============================================================================
P("\n" + "="*100)
P("B1b -- t-sampled cumulants of S (uniform grid in t = Selberg's sampling measure)")
P(f"   {'set':>14}{'k2_t':>9}{'k2_zeros':>10}{'ratio':>8}{'exkurt_t':>10}{'exkurt_z':>10}{'skew_t':>9}")
for d in ROWS:
    g = d['g']; T0, T1 = d['T0'], d['T1']
    M = 400000
    tt = np.linspace(T0, T1, M)
    N = d['k1'] - 1 + np.searchsorted(g, tt, side='right')
    St = N - theta(tt)/pi - 1.0
    kt = cumulants(St, 8); kz = cumulants(d['S'], 8)
    d['kt'] = kt; d['kz'] = kz
    P(f"   {d['name']:>14}{kt[2]:>9.5f}{kz[2]:>10.5f}{kz[2]/kt[2]:>8.4f}"
      f"{kt[4]/kt[2]**2:>10.4f}{kz[4]/kz[2]**2:>10.4f}{kt[3]/kt[2]**1.5:>9.4f}")

# ============================================================================
P("\n" + "="*100)
P("B2 -- the random (Bessel-product) model, cutoff calibrated on kappa_2 ONLY, then PREDICTING")
P(f"   {'set':>14}{'k2 used':>9}{'X eff':>11}{'k4 model':>11}{'k4 meas':>11}{'ratio':>7}"
  f"{'k6 model':>11}{'k6 meas':>11}{'ratio':>7}")
for tag, key in (('AT ZEROS', 'kz'), ('t-SAMPLED', 'kt')):
    P(f"   --- {tag} ---")
    for d in ROWS:
        k = d[key]
        X, a = model_from_kappa2(k[2])
        k4m = -(3/8)*float((a**4).sum()); k6m = (5/4)*float((a**6).sum())
        lp_m = float(np.log(j0(2*pi*a)).sum())
        d[key+'_model'] = (X, k4m, k6m, lp_m)
        P(f"   {d['name']:>14}{k[2]:>9.5f}{X:>11.3g}{k4m:>11.2e}{k[4]:>11.2e}{k4m/k[4]:>7.3f}"
          f"{k6m:>11.2e}{k[6]:>11.2e}{k6m/k[6]:>7.3f}")

P("\n   and the model's own log|phi(2 pi)| = sum_n log J_0(2 pi a_n), against the measurement:")
P(f"   {'set':>14}{'log|phi| meas':>15}{'model (zeros-cal)':>19}{'gauss part':>12}{'model K/n':>12}{'meas K/n':>11}")
for d in ROWS:
    X, k4m, k6m, lp_m = d['kz_model']
    meas = math.log(abs(d['phi_z']))
    P(f"   {d['name']:>14}{meas:>15.4f}{lp_m:>19.4f}{-2*pi*pi*d['kz'][2]:>12.4f}"
      f"{math.exp(2*lp_m):>12.6f}{abs(d['phi_z'])**2:>11.6f}")

# ============================================================================
P("\n" + "="*100)
P("B3 -- exponent decomposition: which Edgeworth term carries the -2.7 slope?")
sing = [d for d in ROWS if d['name'] != 'long[14,2e4]']
x = np.array([math.log(math.log(d['Tc'])) for d in sing])
COEF = {2: -2*pi**2, 4: (2*pi)**4/24, 6: -(2*pi)**6/720, 8: (2*pi)**8/40320}
tot = np.zeros(len(sing))
P(f"   {'term':>8}{'values across the 5 heights':>52}{'slope d/dloglogT':>20}{'x2 (K)':>10}")
for j in (2, 4, 6, 8):
    v = np.array([COEF[j]*d['kz'][j] for d in sing]); tot = tot + v
    s = np.polyfit(x, v, 1)[0]
    P(f"   j={j:<6}" + "".join(f"{q:>10.4f}" for q in v) + f"{s:>12.4f}{2*s:>10.4f}")
s = np.polyfit(x, tot, 1)[0]
P(f"   {'TOTAL':>8}" + "".join(f"{q:>10.4f}" for q in tot) + f"{s:>12.4f}{2*s:>10.4f}")
meas = np.array([math.log(abs(d['phi_z'])) for d in sing])
P(f"   {'meas':>8}" + "".join(f"{q:>10.4f}" for q in meas)
  + f"{np.polyfit(x, meas, 1)[0]:>12.4f}{2*np.polyfit(x, meas, 1)[0]:>10.4f}")
sj2 = np.polyfit(x, np.array([COEF[2]*d['kz'][2] for d in sing]), 1)[0]
sall = np.polyfit(x, tot, 1)[0]
P(f"\n   fraction of the slope carried by j >= 4 :  {(sall-sj2)/sall:.3f}")

# ============================================================================
P("\n" + "="*100)
P("B4 -- exponent fit robustness: drop the wide-ratio T=1e3 set (hi/lo = 6.19)")
import itertools
Kd = {'T=1e3': (131.858, 9.921, 5168), 'T=1e4': (75.797, 9.422, 4318),
      'T=1e5': (39.397, 8.186, 4162), 'T=1e6': (28.868, 6.229, 4003),
      'T=1e7': (13.931, 4.973, 4204)}
names = [d['name'] for d in sing]
for drop in ([], ['T=1e3'], ['T=1e3', 'T=1e4']):
    idx = [i for i, nm in enumerate(names) if nm not in drop]
    xx = x[idx]
    yy = np.array([math.log(Kd[names[i]][0]/Kd[names[i]][2]) for i in idx])
    ss = np.array([Kd[names[i]][1]/Kd[names[i]][0] for i in idx])
    w = 1/ss**2; X2 = np.vstack([xx, np.ones_like(xx)]).T
    cov = np.linalg.inv(X2.T @ np.diag(w) @ X2); b = cov @ (X2.T @ np.diag(w) @ yy)
    P(f"   drop {str(drop):>22}  n={len(idx)}  slope {b[0]:+.3f} +- {sqrt(cov[0,0]):.3f}"
      f"   z vs -2 = {(b[0]+2)/sqrt(cov[0,0]):+.2f}")
