"""ATTEMPT 011 -- GATE stage.

Builds a generic Hardy-Z evaluator for a Dirichlet series with PERIODIC coefficients
mod q, parity a, root number +1:

    Lambda(s) = (q/pi)^{(s+a)/2} Gamma((s+a)/2) f(s),   Lambda(s) = Lambda(1-s)
    theta_f(t) = arg Gamma((1/2+a+it)/2) + (t/2) log(q/pi)
    Z_f(t)     = e^{i theta_f(t)} f(1/2+it)   is REAL
    Z_f(t)    ~= 2 sum_{n <= sqrt(q t / 2pi)} c_n n^{-1/2} cos(theta_f(t) - t log n)   [AFE main sum]

Three specimens:
    zeta      q=1, a=0, c_n = 1
    L(chi_-3) q=3, a=1, c_n = chi_{-3}(n)          (Euler product, character kills 3^k)
    DH        q=5, a=1, c_n = [1, XI, -XI, -1, 0]  (functional equation, NO Euler product)

GATES RUN HERE, each with its stated null:
  G1 FE gate.  |Lambda(s) - Lambda(1-s)| / |Lambda(s)| at random s.
     NULL if the assumed (q,a,eps) is WRONG: ratio O(1), not O(1e-15).
  G2 reality gate.  |Im Z_f(t)| / |Z_f(t)| on the critical line.
     NULL if theta_f is wrong: O(1).
  G3 main-sum gate.  max |Z_main - Z_exact| at t ~ 1e5, against mpmath Hurwitz zeta.
     NULL if the AFE truncation xy = q t / 2pi is wrong: error O(1) not O(t^{-1/4}).
"""
import numpy as np, mpmath as mp, math, time, sys
mp.mp.dps = 25
def P(*a): print(*a); sys.stdout.flush()

# ---------- specimens -------------------------------------------------------
A_DH = (4/np.sqrt(5))*np.sin(2*np.pi/5)
B_DH = (4/np.sqrt(5))*np.sin(4*np.pi/5)
XI   = (np.sqrt(A_DH**2 + B_DH**2) - A_DH)/B_DH
mpA = (4/mp.sqrt(5))*mp.sin(2*mp.pi/5); mpB = (4/mp.sqrt(5))*mp.sin(4*mp.pi/5)
mpXI = (mp.sqrt(mpA**2+mpB**2)-mpA)/mpB
P(f"XI = {XI:.15f}   (literature 0.284079043840...)   mp {mp.nstr(mpXI,18)}")

SPEC = {
  'zeta':  dict(q=1, a=0, coef=[1.0]),                      # coef[n mod q]
  'chi-3': dict(q=3, a=1, coef=[0.0, 1.0, -1.0]),           # n%3 -> 0,1,2
  'DH':    dict(q=5, a=1, coef=[0.0, 1.0, XI, -XI, -1.0]),  # n%5 -> 0,1,2,3,4
}
def cvec(name, nmax):
    s = SPEC[name]; q = s['q']; c = np.array(s['coef'], float)
    n = np.arange(1, nmax+1)
    return c[n % q] if q > 1 else np.ones(nmax)

def f_exact(name, s):
    """f(s) by Hurwitz zeta, mpmath."""
    sp = SPEC[name]; q = sp['q']
    if name == 'zeta': return mp.zeta(s)
    tot = mp.mpf(0)
    for r in range(1, q+1):
        c = sp['coef'][r % q]
        if c == 0: continue
        cc = mpXI if abs(abs(c)-XI) < 1e-12 else mp.mpf(int(round(c)))
        if c < 0: cc = -abs(cc)
        else:     cc = abs(cc)
        tot += cc * mp.zeta(s, mp.mpf(r)/q)
    return mp.power(q, -s) * tot

def Lambda_exact(name, s):
    sp = SPEC[name]; q, a = sp['q'], sp['a']
    return mp.power(mp.mpf(q)/mp.pi, (s+a)/2) * mp.gamma((s+a)/2) * f_exact(name, s)

# ---------- fast theta (Stirling) and main-sum Z ----------------------------
_B = [1/6, -1/30, 1/42, -1/30, 5/66]      # B_2k, k=1..5
def logGamma_asym(z):
    z = np.asarray(z, complex)
    out = (z-0.5)*np.log(z) - z + 0.5*np.log(2*np.pi)
    zp = z.copy()
    for k in range(1, 6):
        out += _B[k-1]/(2*k*(2*k-1)*zp)
        zp = zp*z*z
    return out
def theta_f(t, q, a):
    t = np.asarray(t, float)
    return np.imag(logGamma_asym((0.5+a+1j*t)/2)) + (t/2)*math.log(q/np.pi)

def Zmain(t, name, cs=None):
    """AFE main sum, sharp cutoff N = floor(sqrt(q t / 2pi)).  No RS correction."""
    sp = SPEC[name]; q, a = sp['q'], sp['a']
    t = np.atleast_1d(np.asarray(t, float))
    Nn = np.floor(np.sqrt(q*t/(2*np.pi))).astype(np.int64)
    th = theta_f(t, q, a); Nmax = int(Nn.max())
    if cs is None or len(cs) < Nmax: cs = cvec(name, Nmax)
    s = np.zeros_like(t)
    for n in range(1, Nmax+1):
        c = cs[n-1]
        if c == 0.0: continue
        m = Nn >= n
        s[m] += c*np.cos(th[m] - t[m]*math.log(n))/math.sqrt(n)
    return 2*s

def Zexact(t, name):
    sp = SPEC[name]; q, a = sp['q'], sp['a']
    tm = mp.mpf(float(t)); s = mp.mpf(0.5)+1j*tm
    th = mp.im(mp.loggamma((mp.mpf(0.5)+a+1j*tm)/2)) + (tm/2)*mp.log(mp.mpf(q)/mp.pi)
    return mp.exp(1j*th)*f_exact(name, s)

# ---------- G1 : functional equation ---------------------------------------
P("\nG1  FUNCTIONAL EQUATION  |Lambda(s)-Lambda(1-s)|/|Lambda(s)|.  NULL (wrong q,a,eps): O(1).")
rng = np.random.default_rng(11)
for name in ('zeta','chi-3','DH'):
    worst = 0.0
    for _ in range(4):
        s = mp.mpf(float(rng.uniform(0.3,0.9))) + 1j*mp.mpf(float(rng.uniform(5,25)))
        L1, L2 = Lambda_exact(name, s), Lambda_exact(name, 1-s)
        worst = max(worst, float(abs(L1-L2)/abs(L1)))
    P(f"   {name:>6}  q={SPEC[name]['q']} a={SPEC[name]['a']}   worst rel |Lam(s)-Lam(1-s)| = {worst:.3e}")

# ---------- DH literature off-line zero -------------------------------------
z = mp.mpf('0.80851718') + 1j*mp.mpf('85.69934849')
P(f"\n   DH at the literature off-line zero 0.80851718+85.69934849i : |f| = {float(abs(f_exact('DH', z))):.3e}")

# ---------- G2 : reality of Z on the line -----------------------------------
P("\nG2  REALITY OF Z ON THE LINE  |Im Z|/|Z|.  NULL (wrong theta): O(1).")
for name in ('zeta','chi-3','DH'):
    w = 0.0
    for t in (37.7, 101.3, 1000.55):
        v = Zexact(t, name); w = max(w, float(abs(mp.im(v))/abs(v)))
    P(f"   {name:>6}  worst |Im Z|/|Z| = {w:.3e}")

# ---------- G3 : main-sum accuracy at t ~ 1e5 -------------------------------
P("\nG3  MAIN-SUM GATE at t ~ 1e5 (32 random points).  Reference: mpmath Hurwitz.")
P("    NULL (wrong AFE length): error O(1).  Expected if right: O(t^{-1/4}) ~ 0.056.")
for name in ('zeta','chi-3','DH'):
    ts = rng.uniform(1e5, 1e5+300, 32)
    t0 = time.time()
    ex = np.array([float(mp.re(Zexact(float(t), name))) for t in ts])
    ap = Zmain(ts, name)
    err = np.abs(ap-ex)
    P(f"   {name:>6}  max|dZ| = {err.max():.4f}   rms = {err.std():.4f}   "
      f"rms|Z| = {ex.std():.3f}   rel = {err.max()/np.abs(ex).max():.3f}   ({time.time()-t0:.0f}s)")

# ---------- Lambda_f(n) for each specimen -----------------------------------
P("\nCOEFFICIENTS of -f'/f :  a_n log n = sum_{d|n} Lambda_f(d) a_{n/d},  a_1 = 1.")
def Lam_f(name, NM=40):
    c = cvec(name, NM); L = np.zeros(NM+1)
    for n in range(2, NM+1):
        v = c[n-1]*math.log(n)
        for d in range(2, n):
            if n % d == 0: v -= L[d]*c[n//d-1]
        L[n] = v
    return L
LAMS = {nm: Lam_f(nm) for nm in ('zeta','chi-3','DH')}
P(f"   {'n':>3} {'zeta':>10} {'chi-3':>10} {'DH':>10}   type")
for n in range(2, 33):
    k = n; typ = 'prime power' if any(abs(LAMS['zeta'][n]) > 1e-12 for _ in [0]) else 'composite'
    P(f"   {n:>3} {LAMS['zeta'][n]:>10.5f} {LAMS['chi-3'][n]:>10.5f} {LAMS['DH'][n]:>10.5f}   {typ}")
np.save('/Users/samuellavery/work/helix_frobenius/tmp/att011_lamf.npy',
        np.array([LAMS['zeta'], LAMS['chi-3'], LAMS['DH']]))
P("\nsaved att011_lamf.npy")
