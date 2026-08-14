"""ADVERSARIAL VERIFICATION of attempt 012 (Selberg CLT x theta-tape line amplitudes).

Independent of tmp/att012_*.py:
  * own Riemann-Siegel Z (analytic Psi''' via sympy, 2 correction terms), gated vs mpmath.siegelz
  * own zero finder, own windows (DIFFERENT windows from theirs at the same heights)
  * own prime-power sieve and V_line, cross-checked against mpmath prime zeta
  * own Var S: (i) piecewise Gauss-Legendre order 24 in t, (ii) EXACT closed form in the
    tape variable u (piecewise-linear sawtooth) -- two structurally different computations
  * the cutoff-scan mapping tau = c  <->  n <= X^c   vs   their code's  n <= c*X

usage:  python3 att012_verify.py [A|B|C|D|ALL]
"""
import sys, os, math, time
import numpy as np
from math import log, pi, sqrt
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
TWOPI2 = 2.0*pi*pi
def P(*a): print(*a); sys.stdout.flush()

# ----------------------------------------------------------------- theta (own, more terms)
def theta(t):
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8
            + 1/(48*t) + 7/(5760*t**3) + 31/(80640*t**5))
def thetap(t):
    t = np.asarray(t, float)
    return 0.5*np.log(t/(2*np.pi)) - 1/(48*t**2) - 21/(5760*t**4) - 155/(80640*t**6)

# ----------------------------------------------------------------- Psi and Psi'''
# NOTE: the closed-form symbolic 3rd derivative of Psi carries 1/cos(2 pi p)^4 and is
# catastrophically ill-conditioned when a grid point lands within ~1e-5 of p = 1/4 or 3/4
# (removable singularities of Psi).  That produced SPURIOUS sign changes in a first run of
# this script.  A wide-stencil finite difference (h = 0.05) is well conditioned and its
# O(h^2) truncation error enters Z only through the C1 term (prefactor ~4e-5 at t=1e6).
def _psi_f(p):
    return np.cos(2*np.pi*(p*p - p - 1/16.0))/np.cos(2*np.pi*p)

def _psi3_f(p, h=0.05):
    return (_psi_f(p+2*h) - 2*_psi_f(p+h) + 2*_psi_f(p-h) - _psi_f(p-2*h))/(2*h**3)

def Zmine(t):
    """Riemann-Siegel Z, main sum + C0 + C1 (analytic third derivative)."""
    t = np.asarray(t, float)
    tau = np.sqrt(t/(2*np.pi))
    N = np.floor(tau).astype(np.int64)
    th = theta(t)
    s = np.zeros_like(t)
    Nmax = int(N.max())
    for n in range(1, Nmax+1):
        m = N >= n
        s[m] += np.cos(th[m] - t[m]*np.log(n))/np.sqrt(n)
    p = tau - N
    C0 = _psi_f(p)
    C1 = -_psi3_f(p)/(96*np.pi**2)
    corr = (2*np.pi/t)**0.25*(C0 + C1*np.sqrt(2*np.pi/t))
    return 2*s + ((-1)**(N-1))*corr

def gate(pts, tol=1e-7):
    mp.mp.dps = 20
    ref = np.array([float(mp.siegelz(x)) for x in pts])
    got = Zmine(np.array(pts, float))
    e = float(np.max(np.abs(ref-got)))
    P(f"    GATE own Z vs mpmath.siegelz over {len(pts)} pts: max|dZ| = {e:.2e}  "
      f"({'OK' if e < tol else 'FAIL'})")
    return e

def zeros_in(T, W, h, refine=40):
    g = np.arange(T, T+W, h)
    z = Zmine(g)
    sb = np.signbit(z)
    idx = np.nonzero(sb[:-1] != sb[1:])[0]
    a, b = g[idx].copy(), g[idx+1].copy()
    za = z[idx].copy()
    for _ in range(refine):
        m = 0.5*(a+b)
        zm = Zmine(m)
        left = np.signbit(za) != np.signbit(zm)
        b = np.where(left, m, b)
        a = np.where(left, a, m)
        za = np.where(left, za, zm)
    return 0.5*(a+b)

# ----------------------------------------------------------------- prime powers / V_line
def prime_powers(X):
    X = int(X)
    sieve = np.ones(X+1, bool); sieve[:2] = False
    for p in range(2, int(X**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    primes = np.nonzero(sieve)[0]
    ns, a2 = [], []
    for p in primes:
        v, k = int(p), 1
        while v <= X:
            ns.append(v); a2.append(1.0/(k*k*float(p)**k))   # Lambda(n)^2/(n log^2 n)
            v *= int(p); k += 1
    ns = np.array(ns, float); a2 = np.array(a2, float)
    o = np.argsort(ns)
    return ns[o], a2[o]

# ----------------------------------------------------------------- Var S, two ways
def varS_gl(gam, m=24):
    """piecewise Gauss-Legendre in t of S = c0 + k - theta/pi.  c0 MUST be included: without
    it S ~ -2e7 at T=1e7 and Var = <S^2> - <S>^2 loses 15 digits to cancellation."""
    x, w = np.polynomial.legendre.leggauss(m)
    lo, hi = gam[:-1], gam[1:]
    mid = 0.5*(lo+hi); half = 0.5*(hi-lo)
    t = mid[:, None] + half[:, None]*x[None, :]
    c0 = float(np.round(theta(np.array([gam[0]]))[0]/np.pi))
    kk = (np.arange(1, len(gam)) - c0)[:, None].astype(float)
    S = kk - (theta(t)/np.pi - c0)
    Wp = gam[-1]-gam[0]
    I1 = (half[:, None]*w[None, :]*S).sum()/Wp
    I2 = (half[:, None]*w[None, :]*S*S).sum()/Wp
    return I1, I2 - I1*I1

def varS_u_exact(gam):
    """EXACT closed form in the tape coordinate u = theta/pi (no quadrature at all)."""
    u = theta(gam)/pi
    u = u - u[0]
    U = u[-1]
    v = np.arange(1, len(gam)) - u[:-1]          # S at u_k^+ (c0 dropped)
    s = np.diff(u)
    m1 = (v*s - 0.5*s*s).sum()/U
    m2 = ((v**3 - (v-s)**3)/3.0).sum()/U
    return m1, m2 - m1*m1

# =====================================================================================
WHAT = (sys.argv[1] if len(sys.argv) > 1 else 'ALL').upper()

if WHAT in ('A', 'ALL'):
    P("="*92)
    P("A.  INDEPENDENT V_line(X) = (1/2pi^2) sum_{p^k <= X} 1/(k^2 p^k)")
    P("="*92)
    NS, A2 = prime_powers(1700000)
    CUM = np.cumsum(A2)
    def V_line(X):
        j = np.searchsorted(NS, X, side='right')
        return (CUM[j-1] if j > 0 else 0.0)/TWOPI2
    # their five window centres
    centres = [3600.0009, 11799.8889, 101349.8110, 1001050.0319, 10000924.7686]
    theirs = [0.114097, 0.122747, 0.135399, 0.146115, 0.155014]
    P(f"  {'centre':>14}{'X=tc/2pi':>12}{'lines':>8}{'mine V_line':>14}{'theirs':>11}{'diff':>12}")
    for tc, th in zip(centres, theirs):
        X = tc/(2*pi); j = np.searchsorted(NS, X, side='right')
        v = V_line(X)
        P(f"  {tc:>14.1f}{X:>12.0f}{j:>8d}{v:>14.6f}{th:>11.6f}{v-th:>12.2e}")
    # mpmath cross-check of the asymptotic constant
    mp.mp.dps = 25
    Cpp = mp.nsum(lambda k: mp.primezeta(k)/k**2, [2, mp.inf])
    Mert = mp.euler - mp.nsum(lambda k: mp.primezeta(k)/k, [2, mp.inf])
    P(f"\n  asymptote check: V_line(X) ~ (1/2pi^2)[log log X + M + C_pp],  M+C_pp = {float(Mert+Cpp):.10f}")
    for X in (1e4, 1e5, 1e6, 1.5e6):
        P(f"    X={X:>9.0e}  exact {V_line(X):.6f}   asympt {(math.log(math.log(X))+float(Mert+Cpp))/TWOPI2:.6f}")
    np.save(os.path.join(HERE, 'att012_verify_NS.npy'), NS)
    np.save(os.path.join(HERE, 'att012_verify_CUM.npy'), CUM)

if WHAT in ('C', 'ALL'):
    P("\n" + "="*92)
    P("C.  THE CUTOFF SCAN: their map tau=c -> n <= c*X   vs   the correct n <= X^c")
    P("="*92)
    NS = np.load(os.path.join(HERE, 'att012_verify_NS.npy'))
    CUM = np.load(os.path.join(HERE, 'att012_verify_CUM.npy'))
    def V_line(X):
        j = np.searchsorted(NS, X, side='right')
        return (CUM[j-1] if j > 0 else 0.0)/TWOPI2
    MCPP = 0.4009678524589514655585
    def V_asym(X):                    # needed for X^c beyond the sieve
        return (math.log(math.log(X)) + MCPP)/TWOPI2
    centres = [3600.0009, 11799.8889, 101349.8110, 1001050.0319, 10000924.7686]
    meas = [0.165003, 0.174374, 0.186333, 0.197010, 0.205389]
    CS = (0.125, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 4.0, 8.0)
    for name, mapper in (("THEIRS  n<=c*X (as coded)", lambda X, c: V_line(c*X)),
                         ("CORRECT n<=X^c  (tau=c)", lambda X, c: V_asym(X**c))):
        P(f"\n  {name}:   total(c) = V(cutoff) + 1/(2 pi^2 c)")
        rows = []
        for tc, ms in zip(centres, meas):
            X = tc/(2*pi)
            rows.append([ms/(mapper(X, c) + 1/(TWOPI2*c)) for c in CS])
        rows = np.array(rows)
        P("   " + "".join(f"{'c='+str(c):>10}" for c in CS))
        for r in rows: P("   " + "".join(f"{x:>10.4f}" for x in r))
        rms = np.sqrt(((rows-1)**2).mean(axis=0))
        P("   rms " + "".join(f"{x:>10.4f}" for x in rms))
    # is total(c) stationary at c=1 under each map?
    P("\n  d/dc of the MODEL total at c=1 (relative, per unit c), X = 1.59e6, L = 14.28:")
    X = 10000924.7686/(2*pi); L = math.log(X)
    for name, f in (("theirs  V_line(cX)", lambda c: V_line(c*X) + 1/(TWOPI2*c)),
                    ("correct V(X^c)   ", lambda c: V_asym(X**c) + 1/(TWOPI2*c))):
        d = (f(1.001) - f(0.999))/0.002
        P(f"    {name}:  total(1) = {f(1.0):.6f}   d total/dc = {d:+.6f}   "
          f"(stationary? {'YES' if abs(d) < 1e-3 else 'NO'})")

if WHAT in ('B', 'ALL'):
    P("\n" + "="*92)
    P("B.  INDEPENDENT Var S  in NEW windows (theirs are a subset, marked *)")
    P("="*92)
    NS = np.load(os.path.join(HERE, 'att012_verify_NS.npy'))
    CUM = np.load(os.path.join(HERE, 'att012_verify_CUM.npy'))
    def V_line(X):
        j = np.searchsorted(NS, X, side='right')
        return (CUM[j-1] if j > 0 else 0.0)/TWOPI2

    RUNS = []
    for i in range(6):                              # T ~ 1e6, six disjoint windows
        RUNS.append((1.0e6 + i*4000.0, 2100.0, 0.012, f'1e6 w{i}' + (' *' if i == 0 else '')))
    RUNS.append((1.02e6, 8400.0, 0.012, '1e6 WIDE x4'))
    for i in range(4):                              # T ~ 1e5
        RUNS.append((1.0e5 + i*4000.0, 2700.0, 0.025, f'1e5 w{i}' + (' *' if i == 0 else '')))
    for i in range(6):
        RUNS.append((1.0e7 + i*4000.0, 1850.0, 0.009, f'1e7 w{i}' + (' *' if i == 0 else '')))

    gate([1.0e6+0.31, 1.00105e6+0.7, 1.0e5+0.13, 1.0e7+0.77, 1.0002e7+0.4])
    P(f"\n  {'label':>13}{'T0':>13}{'W':>8}{'M':>7}{'M(h/2)':>8}{'meanS':>10}{'VarS(GL24)':>12}"
      f"{'VarS(u,exact)':>14}{'V_line':>10}{'resid':>10}{'resid/pred':>11}")
    OUT = []
    for T0, W, h, lab in RUNS:
        t0 = time.time()
        g = zeros_in(T0, W, h)
        g2 = zeros_in(T0, W, h/2)
        m1, vt = varS_gl(g)
        mu, vu = varS_u_exact(g)
        meanS = m1 - np.round(m1)
        tc = 0.5*(g[0]+g[-1])
        vl = V_line(tc/(2*pi))
        r = vu - vl
        OUT.append((lab, T0, len(g), meanS, vt, vu, vl, r))
        P(f"  {lab:>13}{T0:>13.6g}{W:>8.0f}{len(g):>7d}{len(g2):>8d}{meanS:>10.5f}"
          f"{vt:>12.6f}{vu:>14.6f}{vl:>10.6f}{r:>10.6f}{r*TWOPI2:>11.4f}"
          + ("" if len(g) == len(g2) else "   <-- GRID MISSED ZEROS"))
    P("")
    for tagsel in ('1e5', '1e6', '1e7'):
        rs = np.array([o[7] for o in OUT if o[0].startswith(tagsel) and 'WIDE' not in o[0]])
        if len(rs):
            P(f"  residual at {tagsel}: n={len(rs)}  mean {rs.mean():.6f}  sd {rs.std(ddof=1):.6f}  "
              f"min {rs.min():.6f}  max {rs.max():.6f}   (pred 1/(2pi^2) = {1/TWOPI2:.6f}, "
              f"mean/pred = {rs.mean()/(1/TWOPI2):.4f})")
    allr = np.array([o[7] for o in OUT if 'WIDE' not in o[0]])
    P(f"  ALL windows: n={len(allr)} mean {allr.mean():.6f} sd {allr.std(ddof=1):.6f}  "
      f"sem {allr.std(ddof=1)/sqrt(len(allr)):.6f}   mean/pred {allr.mean()/(1/TWOPI2):.4f}")
    np.save(os.path.join(HERE, 'att012_verify_B.npy'),
            np.array([[o[1], o[4], o[5], o[6], o[7]] for o in OUT]))

if WHAT in ('D', 'ALL'):
    P("\n" + "="*92)
    P("D.  Var(S_lines) diagonal vs DIRECT, at T=1e6 and 1e7 (they only checked <= 1e5)")
    P("="*92)
    NS = np.load(os.path.join(HERE, 'att012_verify_NS.npy'))
    CUM = np.load(os.path.join(HERE, 'att012_verify_CUM.npy'))
    for tc, W, h in ((1001050.03, 2098.9, 0.02), (10000924.77, 1849.1, 0.02)):
        X = tc/(2*pi)
        j = int(np.searchsorted(NS, X, side='right'))
        n = NS[:j]; a = np.sqrt(CUM[:j] - np.concatenate(([0.0], CUM[:j-1])))
        al = np.log(n)
        a, al = np.sqrt(np.diff(np.concatenate(([0.0], CUM[:j])))), np.log(n)
        t = np.arange(tc-W/2, tc+W/2, h)
        s = np.zeros(len(t))
        B = 2000
        for i in range(0, j, B):
            s += (a[i:i+B][:, None]*np.sin(np.outer(al[i:i+B], t))).sum(axis=0)
        s *= -1.0/pi
        vd = s.var()
        vdiag = CUM[j-1]/TWOPI2
        P(f"  tc={tc:.4g}  lines={j}  grid pts={len(t)}   diagonal {vdiag:.6f}   "
          f"direct {vd:.6f}   ratio {vd/vdiag:.4f}   abs diff {vd-vdiag:+.6f} "
          f"({(vd-vdiag)*TWOPI2:+.4f} in units of 1/2pi^2)")
P("\n(done)")
