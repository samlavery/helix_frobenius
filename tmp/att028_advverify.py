"""ADVERSARIAL INDEPENDENT VERIFICATION of attempt 028.

Written from scratch.  Shares NO code with att028_engine.py / att028_*.py:
  * coefficients built three independent ways (binary-form counting, the eta product
    eta(z)eta(23z), and the divisor sum sum_{d|n} chi_{-23}(d)) and cross-checked;
  * Lambda_1 built by Dirichlet inversion (Dirichlet inverse of a_1 convolved with
    a_1 log n), NOT by their subtractive recursion;
  * Lambda(s) evaluated by the *unrotated* incomplete-gamma AFE at arbitrary mpmath
    precision -- i.e. exactly attempt 020's route, which 028 claims is "silently wrong"
    because mpmath.gammainc is broken.  That claim is tested here directly.

NOTE.  The task asked for tmp/att028_verify.py, but that path is attempt 028's own
stage-6 script (listed in its `scripts`); overwriting it would destroy evidence.
"""
import numpy as np, math, sys, time
from math import pi, log, sqrt

TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
def P(*a): print(*a); sys.stdout.flush()

D = 23
CC = 2*pi/sqrt(D)


# ---------------------------------------------------------------- 1. coefficients
def form_counts(a, b, c, N):
    """r_Q(n), n<=N, by brute force over a box -- own implementation."""
    r = np.zeros(N + 1, dtype=np.int64)
    disc = 4*a*c - b*b                      # > 0
    # a x^2 + b xy + c y^2 = ((2ax+by)^2 + disc y^2)/(4a) <= N  ->  |y| <= sqrt(4aN/disc)
    ymax = int(math.floor(math.sqrt(4*a*N/disc))) + 1
    xmax = int(math.floor(math.sqrt(4*c*N/disc))) + 1
    for y in range(-ymax, ymax + 1):
        for x in range(-xmax, xmax + 1):
            v = a*x*x + b*x*y + c*y*y
            if 1 <= v <= N:
                r[v] += 1
    return r


def eta_product(N):
    """b(n) = coefficients of eta(z)eta(23z) = q prod (1-q^k)(1-q^{23k}) -- pure power series."""
    S = np.zeros(N + 1, dtype=np.int64); S[0] = 1
    for k in list(range(1, N + 1)) + [23*k for k in range(1, N//23 + 1)]:
        if k > N: continue
        T = S.copy()
        T[k:] -= S[:N + 1 - k]
        S = T
    b = np.zeros(N + 1, dtype=np.int64)
    b[1:] = S[:N]                            # multiply by q
    return b


def kron23(n):
    """chi_{-23}(n): -23 = 1 mod 4 so this is the Legendre symbol (n|23)."""
    n %= 23
    if n == 0: return 0
    return 1 if pow(n, 11, 23) == 1 else -1


def divisor_chi(N):
    d = np.zeros(N + 1, dtype=np.int64)
    for k in range(1, N + 1):
        c = kron23(k)
        if c:
            d[k::k] += c
    return d


# ---------------------------------------------------------------- 2. Lambda_1 by inversion
def dirichlet_inverse(a, N):
    """g with (a*g)(n) = [n==1]; a(1) must be 1."""
    g = np.zeros(N + 1)
    g[1] = 1.0
    for n in range(2, N + 1):
        s = 0.0
        for d in range(1, n):
            if n % d == 0:
                s += g[d]*a[n//d]
        g[n] = -s
    return g


def lambda_by_inversion(a, N):
    """Lambda_1 = a^{-1} * (a log).  Independent of 028's subtractive recursion."""
    g = dirichlet_inverse(a, N)
    al = np.array([a[n]*math.log(n) if n >= 1 else 0.0 for n in range(N + 1)])
    L = np.zeros(N + 1)
    for n in range(2, N + 1):
        s = 0.0
        for d in range(1, n + 1):
            if n % d == 0:
                s += g[d]*al[n//d]
        L[n] = s
    return L


# ---------------------------------------------------------------- 3. independent Lambda(s)
def make_lambda_evaluator(coef, K0):
    """Lambda(s) = sum_n a(n)[(cn)^{-s}Gamma(s,cn) + (cn)^{s-1}Gamma(1-s,cn)]
                   + (K0/2)(1/(s-1) - 1/s).

    Derivation (own):  Lambda(s) = int_0^inf phi(y)y^{s-1}dy, phi = sum a(n)e^{-cny};
    Theta = K0 + 2phi obeys Theta(1/y) = y Theta(y); splitting at y=1 gives
    Lambda(s) = int_1^inf phi(y)(y^{s-1}+y^{-s})dy + (K0/2)(1/(s-1)-1/s).
    Residue at s=1 is K0/2, which for K0=3 (Dedekind) equals 3/2 -- matches
    (sqrt23/2pi)*Res zeta_K = (sqrt23/2pi)(2pi*3/(2 sqrt23)) = 3/2.  Gate.
    """
    import mpmath as mp

    def Lam(sigma, t, dps=None, extra=25):
        if dps is None:
            dps = int(pi*abs(t)/2/math.log(10)) + 30 + extra
        mp.mp.dps = dps
        c = 2*mp.pi/mp.sqrt(23)
        s = mp.mpf(sigma) + 1j*mp.mpf(t)
        nmax = int(math.ceil((dps + 10)*math.log(10)/float(c))) + 5
        nmax = min(nmax, len(coef) - 1)
        tot = mp.mpc(0)
        for n in range(1, nmax + 1):
            an = coef[n]
            if an == 0: continue
            x = c*n
            tot += an*(x**(-s)*mp.gammainc(s, x) + x**(s - 1)*mp.gammainc(1 - s, x))
        tot += mp.mpf(K0)/2*(1/(s - 1) - 1/s)
        return tot, mp.mp.dps

    return Lam


def theta_Q(t):
    import mpmath as mp
    old = mp.mp.dps; mp.mp.dps = 50
    v = float(mp.mpf(t)*mp.log(mp.sqrt(23)/(2*mp.pi)) + mp.im(mp.loggamma(mp.mpf(0.5) + 1j*mp.mpf(t))))
    mp.mp.dps = old
    return v


# ================================================================== RUN
if __name__ == '__main__':
    N = 4000
    P("=" * 100)
    P("STEP 1  coefficients, three independent routes")
    r0 = form_counts(1, 1, 6, N)
    r1 = form_counts(2, 1, 3, N)
    a1 = r0/2.0
    aC = r1/2.0
    b_form = a1 - aC
    dK_form = a1 + 2*aC
    b_eta = eta_product(N).astype(float)
    dK_div = divisor_chi(N).astype(float)
    P(f"  a_1(1..12)      = {a1[1:13].astype(int)}")
    P(f"  b  (forms)      = {b_form[1:13].astype(int)}")
    P(f"  b  (eta product)= {b_eta[1:13].astype(int)}   "
      f"max|diff| over n<={N}: {np.abs(b_form-b_eta).max():.3g}")
    P(f"  d_K(forms)      = {dK_form[1:13].astype(int)}")
    P(f"  d_K(div-sum chi)= {dK_div[1:13].astype(int)}   "
      f"max|diff| over n<={N}: {np.abs(dK_form-dK_div).max():.3g}")
    P(f"  class-split identity  a_1 == (d_K + 2b)/3 : max|diff| = "
      f"{np.abs(a1 - (dK_form + 2*b_form)/3).max():.3g}")

    P("\nSTEP 2  Lambda_1 by Dirichlet inversion (independent of 028's recursion)")
    NL = 64
    LF = lambda_by_inversion(a1, NL)
    Lf = lambda_by_inversion(b_form, NL)
    LK = lambda_by_inversion(dK_form, NL)
    sys.path.insert(0, TMP)
    from att028_engine import vonmangoldt_like
    LF_t = vonmangoldt_like(a1, NL)
    P(f"  max |Lambda_1(mine) - Lambda_1(028)| over n<=64 = {np.abs(LF-LF_t).max():.3g}")

    def isppow(n):
        m, p = n, 2
        while p*p <= m:
            if m % p == 0:
                while m % p == 0: m //= p
                return m == 1
            p += 1
        return True
    LINES = [n for n in range(2, NL + 1) if abs(LF[n]) > 1e-9]
    NPP = [n for n in LINES if not isppow(n)]
    SILENT = [n for n in range(2, NL + 1)
              if abs(LF[n]) < 1e-9 and abs(LK[n]) < 1e-9 and abs(Lf[n]) < 1e-9]
    P(f"  LINES ({len(LINES)}): {LINES}")
    P(f"  NON-PRIME-POWER lines ({len(NPP)}): {NPP}")
    P(f"  all-silent n ({len(SILENT)}): {SILENT}")
    P(f"  Lambda_1(6)={LF[6]:.6f} (2log6={2*log(6):.6f});  Lambda_1(48)={LF[48]:.6f} "
      f"(-2log48={-2*log(48):.6f});  Lambda_1(2)={LF[2]:.3g}  Lambda_1(3)={LF[3]:.3g}")

    P("\nSTEP 3  Landau statistics recomputed from 028's saved zero lists")
    on = np.load(TMP + 'att028_zeros_F.npy')
    off = np.load(TMP + 'att028_offline_F600.npy')
    T0, T1 = 10.0, 600.0
    W = T1 - T0
    ong = on[(on > T0) & (on < T1)]
    P(f"  on-line zeros in ({T0},{T1}): {len(ong)};  off-line pairs: {len(off)}")

    def a_ord(n):
        return np.exp(1j*ong*log(n)).sum()/(W/(2*pi))

    def a_beta(n):
        ln = log(n)
        v = np.exp(1j*ong*ln).sum()
        v += np.sum((n**(off[:, 0] - 0.5) + n**(0.5 - off[:, 0]))*np.exp(1j*off[:, 1]*ln))
        return v/(W/(2*pi))

    r_ord, r_bet, rows = [], [], []
    for n in LINES:
        pred = -LF[n]/sqrt(n)
        ao, ab = a_ord(n), a_beta(n)
        r_ord.append(ao.real/pred); r_bet.append(ab.real/pred)
        rows.append((n, isppow(n), pred, ao, ab))
    r_ord, r_bet = np.array(r_ord), np.array(r_bet)
    mnpp = np.array([not isppow(n) for n in LINES])
    P(f"  {'n':>4}{'ppow':>6}{'pred':>10}{'ord.Re':>10}{'o/p':>9}{'beta.Re':>10}{'o/p':>9}{'arg/pi':>9}")
    for (n, ip, pred, ao, ab), q1, q2 in zip(rows, r_ord, r_bet):
        P(f"  {n:>4}{('y' if ip else 'NO'):>6}{pred:>10.5f}{ao.real:>10.5f}{q1:>9.3f}"
          f"{ab.real:>10.5f}{q2:>9.4f}{math.atan2(ab.imag,ab.real)/pi:>9.4f}")
    P(f"  ORDINATE-ONLY  median o/p all {len(r_ord)} lines = {np.median(r_ord):.4f};  "
      f"NPP-only = {np.median(r_ord[mnpp]):.4f}")
    P(f"  BETA-WEIGHTED  median o/p all {len(r_bet)} lines = {np.median(r_bet):.4f}  "
      f"IQR {np.percentile(r_bet,25):.4f}-{np.percentile(r_bet,75):.4f};  "
      f"NPP-only = {np.median(r_bet[mnpp]):.4f}  range {r_bet[mnpp].min():.4f}-{r_bet[mnpp].max():.4f}")
    P(f"  ordinate-only a(2) = {a_ord(2).real:+.4f}  a(3) = {a_ord(3).real:+.4f}   "
      f"beta-weighted a(2) = {a_beta(2).real:+.4f}  a(3) = {a_beta(3).real:+.4f}")
    nf = [abs(a_beta(n)) for n in SILENT]
    P(f"  noise floor over {len(SILENT)} silent n: median {np.median(nf):.4f} max {max(nf):.4f}")
    P(f"  n=48: pred {-LF[48]/sqrt(48):+.5f}  measured {a_beta(48).real:+.5f}{a_beta(48).imag:+.5f}i"
      f"  arg/pi {math.atan2(a_beta(48).imag,a_beta(48).real)/pi:+.4f}  "
      f"o/p {a_beta(48).real/(-LF[48]/sqrt(48)):.4f}")


# =============================== appended stage: /tmp/adv4.py
import sys, time, math
import numpy as np
sys.path.insert(0,'/Users/samuellavery/work/helix_frobenius/tmp')
from att028_advverify import form_counts, make_lambda_evaluator, theta_Q
import mpmath as mp
from math import pi, log, sqrt
def P(*a): print(*a); sys.stdout.flush()
N=4000
r0=form_counts(1,1,6,N); r1=form_counts(2,1,3,N)
a1=r0/2.0; aC=r1/2.0; dK=a1+2*aC; bf=a1-aC
LamF=make_lambda_evaluator(a1,1); LamK=make_lambda_evaluator(dK,3); Lamf=make_lambda_evaluator(bf,0)

# GATE 0: my zeta_K evaluator vs mpmath zeta(s)*L(s,chi) -- fully independent of any theta stuff
def chi(n):
    n%=23
    return 0 if n==0 else (1 if pow(n,11,23)==1 else -1)
def LamK_direct(sigma,t,dps):
    mp.mp.dps=dps
    s=mp.mpf(sigma)+1j*mp.mpf(t)
    L=mp.mpf(23)**(-s)*sum(chi(r)*mp.zeta(s,mp.mpf(r)/23) for r in range(1,23) if chi(r))
    return (mp.sqrt(23)/(2*mp.pi))**s*mp.gamma(s)*mp.zeta(s)*L
P("GATE 0  my (unrotated, gammainc) Lambda_K  vs  mpmath zeta(s)*L(s,chi_-23)*Gamma factor")
for sg,t in ((0.5,5.0),(0.5,30.0),(0.5,60.0),(0.8,25.0),(1.3,40.0),(-0.4,18.0),(0.5,120.0)):
    t0=time.time()
    v,dps=LamF and LamK(sg,t)
    ref=LamK_direct(sg,t,dps+20)
    rel=abs(v-ref)/abs(ref)
    P(f"   sigma={sg:+.1f} t={t:7.1f} dps={dps:4d}  rel={mp.nstr(rel,4):>12}   [{time.time()-t0:.1f}s]")


# =============================== appended stage: /tmp/adv5.py
import sys, time, math
import numpy as np
sys.path.insert(0,'/Users/samuellavery/work/helix_frobenius/tmp')
from att028_advverify import form_counts, make_lambda_evaluator
import mpmath as mp
from math import pi, log, sqrt
def P(*a): print(*a); sys.stdout.flush()
N=4000
r0=form_counts(1,1,6,N); r1=form_counts(2,1,3,N)
a1=r0/2.0; aC=r1/2.0; dK=a1+2*aC; bf=a1-aC
MyF=make_lambda_evaluator(a1,1); MyK=make_lambda_evaluator(dK,3); Myf=make_lambda_evaluator(bf,0)

from att028_offline import GEngine
from att028_engine import Engine
engF = GEngine(a1, 0.5, delta=0.012)
P("GATE A  028's rotated engine (on the line) vs my unrotated gammainc AFE, specimen F")
for t in (12.0, 37.4, 100.0, 151.9, 200.0, 300.0):
    v,dps = MyF(0.5, t)
    mp.mp.dps=dps
    ref = float(mp.re(v*mp.e**(mp.pi*mp.mpf(t)/2)))
    got = engF.lam_scaled(t)
    P(f"   t={t:7.1f}  engine {got:>22.14g}   mine {ref:>22.14g}   rel {abs(got-ref)/abs(ref):.3e}")

P("\nGATE B  028's lam_gen OFF the critical line vs my AFE, specimen F")
for sg,t in ((0.8,25.0),(1.3,40.0),(-0.4,18.0),(0.95326047,16.29021572),(0.7,120.0)):
    v,dps = MyF(sg, t)
    mp.mp.dps=dps+10
    ref = complex(mp.mpc(v)*mp.e**(mp.pi*mp.mpf(t)/2))
    got = engF.lam_gen(sg, t)
    P(f"   s={sg:+.6f}+{t:.5f}i  engine {got:.10g}  mine {ref:.10g}  rel {abs(got-ref)/abs(ref):.3e}")

P("\nGATE C  |F(rho)| at 028's claimed off-line zeros, MY evaluator (F = Lambda/((sqrt23/2pi)^s Gamma(s)))")
off = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F600.npy')
sel = list(range(0,10))+[20,40,60,80,102]
for i in sel:
    b,g = off[i]
    v,dps = MyF(float(b), float(g))
    mp.mp.dps = dps+10
    s = mp.mpf(float(b))+1j*mp.mpf(float(g))
    Fv = v/((mp.sqrt(23)/(2*mp.pi))**s*mp.gamma(s))
    # scale: |F| relative to a nearby typical |F| value
    v2,_ = MyF(float(b), float(g)+0.25)
    mp.mp.dps = dps+10
    s2 = mp.mpf(float(b))+1j*mp.mpf(float(g)+0.25)
    Fv2 = v2/((mp.sqrt(23)/(2*mp.pi))**s2*mp.gamma(s2))
    P(f"   rho = {b:.8f} + {g:.8f}i :  |F(rho)| = {mp.nstr(abs(Fv),5):>12}   "
      f"|F(rho+0.25i)| = {mp.nstr(abs(Fv2),5):>10}   ratio {mp.nstr(abs(Fv)/abs(Fv2),4)}")


# =============================== appended stage: /tmp/adv6.py
"""Grid-resolution stress test of 028's ON-LINE census, with zeta_K as the ground-truth control
(zeta_K = zeta * L(chi_-23): every zero is on the line, so ANY deficit is a missed close pair)."""
import sys, time, math
import numpy as np
sys.path.insert(0,'/Users/samuellavery/work/helix_frobenius/tmp')
from att028_advverify import form_counts, theta_Q
from att028_engine import Engine
from math import pi
def P(*a): print(*a); sys.stdout.flush()
N=6000
r0=form_counts(1,1,6,N); r1=form_counts(2,1,3,N)
a1=r0/2.0; aC=r1/2.0; dK=a1+2*aC; bf=a1-aC
eng={'F':Engine(a1,0.5,delta=0.012),'zetaK':Engine(dK,1.5,delta=0.012),'Lf':Engine(bf,0.0,delta=0.012)}
T0,T1=10.0,600.0
exp_n=(theta_Q(T1)-theta_Q(T0))/pi
P(f"theta_Q count [{T0},{T1}] = {exp_n:.4f}")
for nm in ('zetaK','Lf','F'):
    e=eng[nm]
    for st in (0.04,0.01,0.004,0.001):
        t0=time.time()
        ts=np.arange(T0,T1+st,st)
        vals=np.array([e.lam_scaled(float(t)) for t in ts])
        c=int(np.sum(np.signbit(vals[:-1])!=np.signbit(vals[1:])))
        P(f"  {nm:>6} step {st:<6} sign changes {c:5d}   deficit {exp_n-c:+7.2f}   [{time.time()-t0:.0f}s]")


# =============================== appended stage: /tmp/adv8.py
import sys, time, numpy as np, math
sys.path.insert(0,'/Users/samuellavery/work/helix_frobenius/tmp')
from att028_advverify import form_counts, theta_Q
from att028_offline import GEngine, winding
from math import pi
def P(*a): print(*a); sys.stdout.flush()
r0=form_counts(1,1,6,6000); r1=form_counts(2,1,3,6000)
a1=r0/2.0; aC=r1/2.0; bf=a1-aC
engF=GEngine(a1,0.5,delta=0.012); engf=GEngine(bf,0.0,delta=0.012)
on=np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
off=np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F600.npy')
for (T0,T1) in ((10.,300.),(10.,600.),(300.,600.)):
    exp_n=(theta_Q(T1)-theta_Q(T0))/pi
    nl=int(((on>T0)&(on<T1)).sum()); nof=int(((off[:,1]>T0)&(off[:,1]<T1)).sum())
    for nv,nh in ((16000,600),(30000,1000),(48000,1600)):
        t0=time.time(); N,j=winding(engF,-1.0,2.0,T0,T1,nv,nh)
        P(f"  F [{T0},{T1}] nv={nv:6d} N={N:.4f} (theta {exp_n:.2f}) maxstep {j:.3f}  on-line {nl} + 2*{nof} = {nl+2*nof}  [{time.time()-t0:.0f}s]")
