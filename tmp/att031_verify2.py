"""att031 verification, part 2: census with correct margins, zero-list ACCURACY,
the noise floor by an independent route, the tautology audit done fairly, and the
question the record never asks -- can the independent-prime model match the DC mode
(kappa_2) at ANY cutoff in the continuous register?
"""
import numpy as np, math, os, sys
from math import pi, log, sqrt
import mpmath as mp
mp.mp.dps = 25
def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))
rng = np.random.default_rng(90210)

SETS = [('T=1e3', 'att010_zeros_1e+03.npy'), ('T=1e4', 'att010_zeros_1e+04.npy'),
        ('T=1e5', 'att010_zeros_1e+05.npy'), ('T=1e6', 'att010_zeros_1e+06.npy'),
        ('T=1e7', 'att010_zeros_1e+07.npy'), ('long', 'att019_zeros_to20k.npy')]

P("="*100)
P("W1 -- CENSUS with half-gap margins (the naive lo-eps/hi+eps test mis-scores a list whose")
P("      endpoint zero is slightly displaced).  count in [lo-d/2, hi+d/2] must equal n.")
P(f"   {'set':>8}{'n':>7}{'nz in window':>14}{'k1 implied':>12}{'mean S at that k1':>19}{'verdict':>10}")
D = []
for name, f in SETS:
    g = np.load(os.path.join(HERE, f)); n = len(g)
    d0 = float(g[1]-g[0]); d1 = float(g[-1]-g[-2])
    lo = float(g[0]) - d0/2; hi = float(g[-1]) + d1/2
    a = int(mp.nzeros(lo)); b = int(mp.nzeros(hi))
    u = np.array([float(mp.siegeltheta(mp.mpf(float(x)))) for x in g])/pi
    S = (a+1+np.arange(n)) - 1.5 - u
    P(f"   {name:>8}{n:>7}{b-a:>14d}{a+1:>12d}{S.mean():>19.6f}"
      f"{'COMPLETE' if b-a == n else 'MISMATCH':>10}")
    D.append(dict(name=name, g=g, n=n, u=u, S=S, k1=a+1))

P("\nW2 -- ACCURACY of the cached zero lists vs mpmath.zetazero (the ground truth).")
P(f"   {'set':>8}{'idx tested':>28}{'max |dt|':>12}{'max |du|':>14}")
for d in D:
    n = d['n']
    idx = sorted(rng.choice(n, size=6, replace=False).tolist() + [0, n-1])
    dts = []
    for i in idx:
        true = float(mp.zetazero(d['k1']+i).imag)
        dts.append(abs(true - float(d['g'][i])))
    dts = np.array(dts)
    dudt = np.log(d['g'][idx]/(2*pi))/(2*pi)
    P(f"   {d['name']:>8}{str(idx[:4])+'...':>28}{dts.max():>12.2e}{float((dts*dudt).max()):>28.2e}")

P("\n   worst-case effect on |phi|: a u-error du shifts each phasor by 2 pi du;")
P("   |phi| is depressed by ~ (2 pi du)^2/2 in relative terms.")
for d in D:
    n = d['n']
    idx = sorted(rng.choice(n, size=6, replace=False).tolist() + [0, n-1])
    dts = np.array([abs(float(mp.zetazero(d['k1']+i).imag) - float(d['g'][i])) for i in idx])
    du = float((dts*np.log(d['g'][idx]/(2*pi))/(2*pi)).max())
    P(f"   {d['name']:>8}  max du = {du:.2e}  ->  relative depression of |phi| <= "
      f"{(2*pi*du)**2/2:.2e}")

# =====================================================================================
P("\n" + "="*100)
P("W3 -- the noise floor Cbar by an INDEPENDENT route (batch means, 25 batches),")
P("      against the record's Bartlett-tapered long-run variance (0.187..1.176).")
CB031 = dict(zip([s[0] for s in SETS], [0.187, 0.277, 0.613, 0.469, 1.176, 0.472]))
P(f"   {'set':>8}{'Cbar batch':>13}{'031 Cbar':>11}{'K':>10}{'K-Cbar':>10}{'bias %':>9}")
for d in D:
    z = np.exp(-2j*pi*d['S']); n = d['n']; d['z'] = z
    phi = z.mean(); K = n*abs(phi)**2; d['K'] = K; d['phi'] = phi
    nb = 25; L = n//nb
    bm = np.array([z[i*L:(i+1)*L].mean() for i in range(nb)])
    # Var of the batch mean about the grand mean, times L = long-run variance estimate
    cb = float(L*np.mean(np.abs(bm - phi)**2)*nb/(nb-1))
    P(f"   {d['name']:>8}{cb:>13.3f}{CB031[d['name']]:>11.3f}{K:>10.3f}{K-cb:>10.3f}"
      f"{100*cb/K:>9.2f}")

# =====================================================================================
P("\n" + "="*100)
P("W4 -- TAUTOLOGY AUDIT, done fairly.  Split each set in half.  Predict log|phi| on")
P("      half B using half B's OWN kappa_2 (the DC mode, which genuinely differs between")
P("      halves) but half A's kappa_4..kappa_8.  This isolates whether the NON-GAUSSIAN")
P("      part is transferable, i.e. whether it is a property of S or of the sample.")
def cums(x):
    m1 = x.mean(); c = x-m1
    mu = {j: float((c**j).mean()) for j in range(2, 9)}
    k = {1: float(m1), 2: mu[2], 3: mu[3], 4: mu[4]-3*mu[2]**2,
         5: mu[5]-10*mu[3]*mu[2], 6: mu[6]-15*mu[4]*mu[2]-10*mu[3]**2+30*mu[2]**3,
         7: mu[7]-21*mu[5]*mu[2]-35*mu[4]*mu[3]+210*mu[3]*mu[2]**2,
         8: mu[8]-28*mu[6]*mu[2]-56*mu[5]*mu[3]-35*mu[4]**2+420*mu[4]*mu[2]**2
            + 560*mu[3]**2*mu[2]-630*mu[2]**4}
    return k
def edge(k2, k4, k6, k8):
    return -2*pi*pi*k2 + (2*pi)**4*k4/24 - (2*pi)**6*k6/720 + (2*pi)**8*k8/40320
P(f"   {'set':>8}{'full-sample resid':>19}{'031 resid':>11}{'gap in K':>10}"
  f"{'transplanted resid':>20}{'in K':>8}")
R031 = dict(zip([s[0] for s in SETS],
                [-0.0053, -0.0090, -0.0124, 0.0098, -0.0281, -0.0063]))
for d in D:
    k = cums(d['S'])
    lp = math.log(abs(d['phi']))
    r = lp - edge(k[2], k[4], k[6], k[8])
    n = d['n']; h = n//2
    kA = cums(d['S'][:h]); kB = cums(d['S'][h:])
    lpB = math.log(abs(np.exp(-2j*pi*d['S'][h:]).mean()))
    rt = lpB - edge(kB[2], kA[4], kA[6], kA[8])
    P(f"   {d['name']:>8}{r:>19.4f}{R031[d['name']]:>11.4f}{math.exp(-2*r):>10.4f}"
      f"{rt:>20.4f}{math.exp(-2*rt):>8.3f}")
P("   ('gap in K' = the factor in K still unaccounted after the j<=8 series -- the record's")
P("    '1.1%..5.5%' claim.  The transplanted column keeps kappa_2 local and imports only the")
P("    non-Gaussian shape.)")

# =====================================================================================
P("\n" + "="*100)
P("W5 -- CAN the independent-prime model match the DC mode at all?  kappa_2^model(X) is")
P("      monotone in X; we report the cutoff needed for the AT-ZEROS and the CONTINUOUS")
P("      variance, and whether it is physically sensible (the model's own scale is X ~ t).")
def primes_to(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
PR = primes_to(3_000_000)
invp = 1.0/PR.astype(float)
cum_invp = np.cumsum(invp)
def k2_model(X):
    """sum a^2/2 over prime powers p^k <= X, a = 1/(pi k p^{k/2})."""
    if X < 2: return 0.0
    if X <= 3_000_000:
        i = np.searchsorted(PR, X, side='right')
        s = float(cum_invp[i-1]) if i > 0 else 0.0
    else:  # Mertens for the tail
        s = math.log(math.log(X)) + 0.2614972128
    tot = s/(pi*pi)
    for kk in range(2, 61):                      # prime powers
        lim = X**(1.0/kk)
        if lim < 2: break
        i = np.searchsorted(PR, lim, side='right')
        if i == 0: continue
        tot += float((invp[:i]**kk).sum())/(pi*pi*kk*kk)
    return tot/2
def solve_X(target):
    lo, hi = 2.0, 1e40
    for _ in range(200):
        mid = math.sqrt(lo*hi)
        if k2_model(mid) < target: lo = mid
        else: hi = mid
    return math.sqrt(lo*hi)
V_Z = {'T=1e3': 0.0820403, 'T=1e4': 0.0910907, 'T=1e5': 0.1030111,
       'T=1e6': 0.1136827, 'T=1e7': 0.1220489, 'long': 0.0884243}
V_U = {'T=1e3': 0.1652969, 'T=1e4': 0.1743819, 'T=1e5': 0.1863331,
       'T=1e6': 0.1970096, 'T=1e7': 0.2053890, 'long': 0.1717617}
TC = {'T=1e3': 3365., 'T=1e4': 11770., 'T=1e5': 1.013e5, 'T=1e6': 1.001e6,
      'T=1e7': 1e7, 'long': 1000.}
P(f"   {'set':>8}{'t-centre':>11}{'X (at zeros)':>14}{'logX/logt':>11}"
  f"{'X (continuous)':>17}{'logX/logt':>11}{'k2_model(X=t)':>15}{'V_u meas':>10}")
for d in D:
    nm = d['name']; t = TC[nm]
    Xz = solve_X(V_Z[nm]); Xu = solve_X(V_U[nm])
    P(f"   {nm:>8}{t:>11.4g}{Xz:>14.4g}{math.log(Xz)/math.log(t):>11.3f}"
      f"{Xu:>17.4g}{math.log(Xu)/math.log(t):>11.3f}{k2_model(t):>15.5f}{V_U[nm]:>10.5f}")
P("\n   NOTE: the record's part B bisected on [3, 1e12] and printed 'X eff = 1e12' for every")
P("   set in its t-SAMPLED block -- that is the bisection SATURATING its upper bound, i.e.")
P("   the calibration silently FAILED there.  Above we let X run to 1e40 to find the truth.")

# =====================================================================================
P("\n" + "="*100)
P("W6 -- what the SAWTOOTH alone predicts, i.e. is 'the at-zeros Gaussian law' a sane")
P("      reference?  If S_continuous were EXACTLY Gaussian, the exact telescoping law forces")
P("      kappa_4(zeros) = -B_4/4 = +1/120 > 0, i.e. K ABOVE n exp(-4 pi^2 V_z), by:")
P(f"      exp(-2*(2 pi)^4*(1/120)/24) = {math.exp(-2*(2*pi)**4*(1/120)/24):.4f}"
  f"   (K would be {math.exp(2*(2*pi)**4*(1/120)/24):.2f} x the 'Gaussian law')")
P("      So the measured DEFICIT of 1.5-2.2 is not 'S at the zeros is platykurtic' arriving")
P("      from nowhere: it is the CONTINUOUS platykurtosis (kappa_4(u) ~ -0.011) overcoming")
P("      the sawtooth's +1/120.  Decomposition of the j=4 factor in K:")
P(f"   {'set':>8}{'k4(u)':>11}{'sawtooth':>11}{'k4(z)':>11}{'K factor from k4(u)':>21}"
  f"{'from sawtooth':>15}{'net':>8}")
for d in D:
    nm = d['name']
    k4z = cums(d['S'])[4]; k4u = k4z - 1/120
    f_u = math.exp(2*(2*pi)**4*k4u/24); f_s = math.exp(2*(2*pi)**4*(1/120)/24)
    P(f"   {nm:>8}{k4u:>11.5f}{-1/120:>11.5f}{k4z:>11.5f}{f_u:>21.4f}{f_s:>15.4f}"
      f"{f_u*f_s:>8.4f}")

# =====================================================================================
P("\n" + "="*100)
P("W7 -- |phi_t(2 pi)| by exact integration by parts (independent of the record's trapezoid)")
Q031 = {'T=1e3': 1.90e-5, 'T=1e4': 5.65e-5, 'T=1e5': 7.40e-5, 'T=1e6': 7.93e-5,
        'T=1e7': 7.57e-5, 'long': 5.42e-5}
for d in D:
    a_, b_ = float(d['g'][0]), float(d['g'][-1]); W = b_-a_
    tha, thb = float(mp.siegeltheta(a_)), float(mp.siegeltheta(b_))
    dpa, dpb = 0.5*log(a_/(2*pi)), 0.5*log(b_/(2*pi))
    bt = abs((np.exp(2j*thb)/(2j*dpb) - np.exp(2j*tha)/(2j*dpa))/W)
    rem = 0.5*abs(log(b_/a_))/(2*dpa**2)/W
    P(f"   {d['name']:>8}  |boundary|/W = {bt:.2e}   remainder <= {rem:.2e}"
      f"   031 quadrature = {Q031[d['name']]:.2e}   |phi_z| = {abs(d['phi']):.4f}")
