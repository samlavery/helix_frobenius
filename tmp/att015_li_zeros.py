"""ATTEMPT 015, stage 1b -- ROUTE (ii): lambda_n straight off the zeros.

    lambda_n = sum_{gamma>0} 4 sin^2( n arctan(1/(2 gamma)) )   +   TAIL(T)

Tail, with N(t) = theta(t)/pi + 1 + S(t) and f_n(t) = 4 sin^2(n arctan(1/(2t))):
    TAIL(T) = int_T^inf f_n(t) theta'(t)/pi dt   -   f_n(T) S(T)   -   int_T^inf f_n'(t) S(t) dt
The first two are computed EXACTLY (theta' = (1/2)Re psi(1/4+it/2) - (1/2)log pi; S(T) from the
gated zero census).  The third is bounded by  max|S| * TotalVar(f_n on [T,inf)) = max|S| f_n(T)
using Trudgian 2014,  |S(t)| <= 0.111 log t + 0.275 log log t + 2.450.
=> that bound IS the reported error bar of route (ii).

Census rule (campaign law): the zero count is gated by grid refinement h vs h/2, NEVER by
agreement with theta/pi (that difference is S and is signal).

STATED NULL: route (ii) disagrees with routes (i)/(i-b) by more than the stated error bar.
"""
import sys, time, math, os, json
import numpy as np
from mpmath import mp, mpf

def P(*a):
    print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
T_TOP  = 30000.0
T_SPLIT = 300.0          # below: mpmath zeros; above: Riemann-Siegel scan
NMAX = 40

# ---------------------------------------------------------------- RS machinery (attempt 010)
def theta_f(t):
    t = np.asarray(t, float)
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def Psi(p):  return np.cos(2*np.pi*(p*p - p - 1/16))/np.cos(2*np.pi*p)
def d3Psi(p, h=1e-3): return (Psi(p+2*h)-2*Psi(p+h)+2*Psi(p-h)-Psi(p-2*h))/(2*h**3)
def Zrs(t):
    t = np.asarray(t, float); tau = np.sqrt(t/(2*np.pi))
    N = np.floor(tau).astype(np.int64); th = theta_f(t); s = np.zeros_like(t)
    for n in range(1, int(N.max())+1):
        m = N >= n; s[m] += np.cos(th[m] - t[m]*np.log(n))/np.sqrt(n)
    p = tau - N
    return 2*s + ((-1)**(N-1))*(2*np.pi/t)**0.25*(Psi(p) + (-d3Psi(p)/(96*np.pi**2))*np.sqrt(2*np.pi/t))

def sign_changes(a, b, h, block=400000):
    """brackets of sign changes of Zrs on [a,b] with step h"""
    out_a, out_b = [], []
    x = a
    prev = None
    while x < b:
        x2 = min(x + block*h, b)
        g = np.arange(x, x2 + h/2, h)
        z = Zrs(g)
        s = np.signbit(z)
        if prev is not None and prev != s[0]:
            out_a.append(xprev); out_b.append(g[0])
        idx = np.nonzero(s[:-1] != s[1:])[0]
        out_a.append(g[idx]); out_b.append(g[idx+1])
        prev = s[-1]; xprev = g[-1]
        x = x2 + h
        if isinstance(out_a[-1], np.ndarray):
            pass
    A = np.concatenate([np.atleast_1d(u) for u in out_a])
    B = np.concatenate([np.atleast_1d(u) for u in out_b])
    return A, B

def bisect(A, B, iters=52):
    a, b = A.copy(), B.copy()
    for _ in range(iters):
        m = (a+b)/2
        left = np.signbit(Zrs(a)) != np.signbit(Zrs(m))
        b = np.where(left, m, b); a = np.where(left, a, m)
    return (a+b)/2

# ---------------------------------------------------------------- get the zeros
def get_zeros():
    cache = os.path.join(HERE, f"att015_zeros_to_{int(T_TOP)}.npy")
    if os.path.exists(cache):
        g = np.load(cache)
        P(f"  loaded {len(g)} zeros from cache, last gamma = {g[-1]:.6f}")
        return g
    t0 = time.time()
    mp.dps = 30
    low = []
    k = 1
    while True:
        z = float(mp.zetazero(k).imag)
        if z >= T_SPLIT: break
        low.append(z); k += 1
    P(f"  mpmath zeros below t={T_SPLIT}: {len(low)}   (last {low[-1]:.9f})   [{time.time()-t0:.1f}s]")

    for h in (0.020, 0.010):
        t1 = time.time()
        A, B = sign_changes(T_SPLIT, T_TOP, h)
        P(f"  RS scan h={h}: {len(A)} sign changes on [{T_SPLIT},{T_TOP}]  [{time.time()-t1:.1f}s]")
        if h == 0.020: n_coarse = len(A); Ak, Bk = A, B
        else: n_fine = len(A)
    if n_coarse != n_fine:
        P(f"  *** CENSUS GATE FAILED: {n_coarse} vs {n_fine}.  ABORT.")
        sys.exit(1)
    P(f"  CENSUS GATE PASSED (h vs h/2 agree at {n_coarse} zeros)")
    hi = bisect(Ak, Bk)
    g = np.concatenate([np.array(low), hi])
    np.save(cache, g)
    P(f"  total zeros = {len(g)}   [{time.time()-t0:.1f}s]")
    return g

# ---------------------------------------------------------------- main
if __name__ == "__main__":
    P(__doc__); P("="*100)
    g = get_zeros()
    T = float(g[-1])
    NT = len(g)

    # --- accuracy audit of the RS positions against mpmath
    mp.dps = 30
    P("\n  RS position audit vs mpmath.zetazero (index found by counting):")
    errs = []
    for probe in (500.0, 2000.0, 9000.0, 25000.0):
        i = int(np.searchsorted(g, probe))
        exact = float(mp.zetazero(i+1).imag)
        errs.append(abs(exact - g[i]))
        P(f"    zero #{i+1:>6}   RS {g[i]:.12f}   mpmath {exact:.12f}   |err| {abs(exact-g[i]):.2e}")
    P(f"    -> max position error {max(errs):.2e}")

    # --- S(T) from the census
    mp.dps = 40
    def theta_mp(t):
        # loggamma is the ANALYTIC continuation, so Im(loggamma) is the UNWRAPPED arg.
        # arg(gamma(.)) would wrap into (-pi,pi] and destroy S(T).  (bug caught 2026-08-12)
        t = mpf(t)
        return mp.im(mp.loggamma(mpf(1)/4 + 1j*t/2)) - t/2*mp.log(mp.pi)
    thT = theta_mp(T)
    ST = NT - 1 - thT/mp.pi
    P(f"\n  census N(T) = {NT} at T = {T:.6f};  theta(T)/pi = {mp.nstr(thT/mp.pi,16)};  "
      f"S(T) = {mp.nstr(ST,8)}")
    Sbound = 0.111*math.log(T) + 0.275*math.log(math.log(T)) + 2.450
    P(f"  Trudgian 2014 bound at T:  |S| <= {Sbound:.4f}")

    # --- the sum
    mp.dps = 40
    gm = mp.mpf  # noqa
    def theta_prime(t):
        return (mp.re(mp.digamma(mpf(1)/4 + 1j*mpf(t)/2)) - mp.log(mp.pi))/2

    lam_ii, tail_lo, err_bar = [], [], []
    ga = np.asarray(g, dtype=np.float64)
    at = np.arctan(1.0/(2*ga))
    t1 = time.time()
    for n in range(1, NMAX+1):
        core = float(np.sum(4*np.sin(n*at)**2))
        f = lambda t, n=n: 4*mp.sin(n*mp.atan(1/(2*mpf(t))))**2
        smooth = mp.quad(lambda t: f(t)*theta_prime(t)/mp.pi, [T, 2*T, 10*T, 100*T, mp.inf])
        fT = float(f(T))
        tail = float(smooth) - fT*float(ST)
        lam_ii.append(core + tail)
        tail_lo.append(tail)
        err_bar.append(Sbound*fT)
    P(f"  zero sum + tail done  [{time.time()-t1:.1f}s]")

    # --- compare with the exact routes
    with open(os.path.join(HERE, 'att015_lambda_exact.json')) as fh:
        ex = json.load(fh)
    mp.dps = 50
    lam_ex = [mpf(x) for x in ex['lam']]

    P("\n  n |   lambda_n (exact, route i-b) |  route (ii) zeros+tail |   tail    |  |diff|  | errbar")
    dig = []
    for n in range(1, NMAX+1):
        d = abs(float(lam_ex[n-1]) - lam_ii[n-1])
        rel = d/abs(float(lam_ex[n-1]))
        dig.append(-math.log10(rel) if rel > 0 else 99)
        if n <= 8 or n % 5 == 0:
            P(f"  {n:>2} | {float(lam_ex[n-1]):>28.16f} | {lam_ii[n-1]:>22.16f} | "
              f"{tail_lo[n-1]:>9.2e} | {d:>8.2e} | {err_bar[n-1]:.1e}")
    P(f"\n  AGREEMENT route (i-b) vs route (ii): min {min(dig):.2f} significant digits, "
      f"median {np.median(dig):.2f}, max {max(dig):.2f}")
    inside = sum(1 for n in range(NMAX)
                 if abs(float(lam_ex[n]) - lam_ii[n]) <= err_bar[n])
    P(f"  inside the stated error bar: {inside}/{NMAX}")

    json.dump({'lam_ii': lam_ii, 'tail': tail_lo, 'errbar': err_bar,
               'T': T, 'NT': NT, 'S_T': float(ST)},
              open(os.path.join(HERE, 'att015_lambda_zeros.json'), 'w'), indent=1)
    P("  wrote att015_lambda_zeros.json")
