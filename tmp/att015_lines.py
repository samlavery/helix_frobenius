"""ATTEMPT 015, stage 2/3 -- does the THETA-TAPE LINE SET explain the oscillation of lambda_n?

THE EXACT SPLIT (stage 1, verified to 51 digits between two routes and 12 digits against the
zeros):   lambda_n = lambda_n^arch + lambda_n^arith.

DC FIRST -- the archimedean common mode in CLOSED FORM, no quadrature, no estimate.
Weierstrass for 1/Gamma inside A(z) = -log2 - log(1-z) - (log pi)/(2(1-z)) + logGamma(1/(2(1-z)))
collapses to

    lambda_n^arch = -(log pi + gamma) n/2  +  sum_{k>=1} [ n/(2k) - 1 + (2k/(2k+1))^n ]     (ARCH)

(bracket = n(n+1)/(8k^2) + O(k^-3), so it converges).  Checked against the Cauchy DFT of A.

THE LINE INSTRUMENT.  The tape's density decomposition is
    dS/du = -(2/L) sum_m (Lambda(m)/sqrt m) cos(2 pi u log m / L)
i.e. in t-coordinates the arithmetic part of the zero density is
    d_arith(t) = -(1/pi) sum_m (Lambda(m)/sqrt m) cos(t log m).
Feeding f_n(t) = 4 sin^2(n arctan(1/(2t))) = 2 - 2 Re[((t+i/2)/(t-i/2))^n] through it needs the
Fourier transform of f_n, which we do EXACTLY by residues at t = -i/2 (order-n pole):

    (1/pi) int_0^inf f_n(t) cos(t x) dt  =  e^{-x/2} P_n(x),
    P_n(x) = sum_{k=1..n} (-1)^{k-1} C(n,k) x^{k-1}/(k-1)!  =  L_{n-1}^{(1)}(x)   [Laguerre]

so the line at log m contributes  -Lambda(m) L_{n-1}^{(1)}(log m) / m.  The DC of that sum is
the PNT mean int_0^X P_n = 1 - L_n(X), evaluated EXACTLY, giving the LINE PREDICTION

    O_n(M) = -[ sum_{m<=M} Lambda(m) L_{n-1}^{(1)}(log m)/m  -  (1 - L_n(log M)) ]        (LINE)

RESTATEMENT CHECK (rule 2).  (LINE) with M = infinity is IDENTICALLY the Bombieri-Lagarias
arithmetic term sum_k C(n,k) eta_{k-1}: P_n's coefficients are C(n,k)(-1)^{k-1}/(k-1)! and
eta_{k-1} = (-1)^k/(k-1)! * reg-lim of sum Lambda(m)(log m)^{k-1}/m.  So NOTHING is claimed as
new about the identity.  What is measured is only this: HOW MUCH of lambda_n^arith the FIRST
FEW LINES (m <= M, the ones the tape actually resolves, m <= 32) reproduce.

Asymptotically (Szego 8.22.1 on L^{(1)}), (LINE) is
    O_n(M) ~ 1 + pi^{-1/2} n^{1/4} sum_{m<=M} (Lambda(m)/sqrt m)(log m)^{-3/4} cos(2 sqrt(n log m) + pi/4),
which is the stationary-phase evaluation of the same integral -- the stationary point sits at
    t_0(n,m) = sqrt( n / log m ).
*** This is the load-bearing scale.  t_0 must lie ABOVE the first zero 14.134 for the line to
    resonate with anything; that needs n > gamma_1^2 log m = 199.8 log m, i.e. n > 138 for m=2.
    The brief's window n <= 40 is BELOW that threshold for every prime.  Pre-registered
    consequence: the n<=40 test should FAIL and the n>>138 test should PASS. ***

PRE-REGISTERED NULL (fixed before running):
  detrend both Y_n = lambda_n^arith and O_n(M) by least squares against B = {1, log n, sqrt n, n};
  R2 = 1 - sum (Yd - Od)^2 / sum Yd^2   (ZERO free parameters -- no fitted amplitude);
  r  = corr(Yd, Od).
  NULL = "the lines explain less than half the variance": R2 < 0.5 AND r^2 < 0.5.
CONTROLS (must fail by MISSING STRUCTURE, never by more cancellation):
  (a) frequencies log m replaced by random log-uniform draws in the same range, amplitudes kept;
  (b) amplitudes Lambda(m)/m permuted across the true frequencies.
NOISE AUDIT: M swept 2..10^6; zero-side truncation T swept 10^4/2x10^4/3x10^4 (matched
truncation -- the failure mode that killed attempt 002); n-range swept.
"""
import sys, os, math, json, time
import numpy as np
from mpmath import mp, mpf

def P(*a):
    print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
NBIG = 3000

# ------------------------------------------------------------------ ARCH, closed form
def lambda_arch(nmax, K=100_000, JMAX=40):
    """lambda_n^arch = -(log pi + gamma) n/2 + sum_{k>=1} [ n/(2k) - 1 + (1-u_k)^n ], u_k=1/(2k+1).
       Regroup exactly:  term_k = [(1-u_k)^n - 1 + n u_k] + n/(2k(2k+1)),
       and sum_k n/(2k(2k+1)) = n(1 - log 2)  EXACTLY.
       Head k<=K summed directly; tail k>K by the binomial series with Hurwitz zeta:
           sum_{k>K}[(1-u)^n-1+nu] = sum_{j>=2} (-1)^j C(n,j) 2^{-j} zeta(j, K+3/2).
       No estimate anywhere; the tail series converges like (n/2K)^j/j!."""
    n = np.arange(1, nmax+1, dtype=np.float64)
    acc = np.zeros(nmax)
    B = 2000
    for a in range(1, K+1, B):
        kk = np.arange(a, min(a+B, K+1), dtype=np.float64)
        u = 1.0/(2*kk+1)
        r = np.log1p(-u)
        acc += (np.exp(n[:, None]*r) - 1.0 + n[:, None]*u).sum(axis=1)
    mp.dps = 30
    tail = np.zeros(nmax)
    logC = np.zeros(nmax)
    for j in range(2, JMAX+1):
        Zj = float(mp.zeta(j, mpf(K) + mpf(3)/2)) / 2.0**j
        Cnj = np.array([float(mp.binomial(int(x), j)) if x >= j else 0.0 for x in n])
        tail += ((-1)**j) * Cnj * Zj
    return (-(math.log(math.pi)+np.euler_gamma)*n/2 + n*(1-math.log(2))
            + acc + tail)

# ------------------------------------------------------------------ zeros + route (ii)
def theta_prime_np(t):
    z = 0.25 + 0.5j*t
    psi = np.log(z) - 1/(2*z) - 1/(12*z**2) + 1/(120*z**4) - 1/(252*z**6)
    return (psi.real - math.log(math.pi))/2

def gauss_legendre(a, b, N):
    x, w = np.polynomial.legendre.leggauss(N)
    return 0.5*(b-a)*x + 0.5*(a+b), 0.5*(b-a)*w

def lambda_from_zeros(g, nmax, ST):
    """core sum + smooth tail (float64 Gauss-Legendre in v, t = T e^v) - f_n(T) S(T)"""
    T = float(g[-1])
    at = np.arctan(1.0/(2*np.asarray(g, float)))
    v, wv = gauss_legendre(0.0, 45.0, 3000)
    t = T*np.exp(v); jac = wv*T*np.exp(v)*theta_prime_np(t)/math.pi
    att = np.arctan(1.0/(2*t))
    aT = math.atan(1.0/(2*T))
    out = np.empty(nmax)
    for n in range(1, nmax+1):
        core = np.sum(4*np.sin(n*at)**2)
        smooth = np.sum(4*np.sin(n*att)**2 * jac)
        fT = 4*math.sin(n*aT)**2
        out[n-1] = core + smooth - fT*ST
    return out

# ------------------------------------------------------------------ Laguerre line prediction
def prime_powers(M):
    M = int(M)
    sieve = np.ones(M+1, dtype=bool); sieve[:2] = False
    for p in range(2, int(M**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    ms, lam = [], []
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= M:
            ms.append(q); lam.append(math.log(p)); q *= int(p)
    o = np.argsort(ms)
    return np.array(ms, float)[o], np.array(lam, float)[o]

def line_prediction(nmax, xs, amps, X_dc):
    """O_n = -[ sum_j amps_j L_{n-1}^{(1)}(xs_j) - (1 - L_n(X_dc)) ]  for n=1..nmax
       amps_j = Lambda(m_j)/m_j ; xs_j = log m_j ; X_dc = log M."""
    xs = np.asarray(xs, float); amps = np.asarray(amps, float)
    out = np.empty(nmax)
    # rolling pairs: alpha=1 recurrence for L_k^{(1)}(xs), alpha=0 recurrence for L_k(X_dc)
    Am, A0 = None, np.ones_like(xs)            # A0 = L_0^{(1)}
    Bm, B0 = None, 1.0                          # B0 = L_0
    for n in range(1, nmax+1):
        # here A0 = L_{n-1}^{(1)}(xs), B0 = L_{n-1}(X_dc); advance B once to get L_n
        k = n-1
        Bn = ((2*k+1-X_dc)*B0 - (k*Bm if Bm is not None else 0.0))/(k+1)
        out[n-1] = -(float(np.dot(amps, A0)) - (1.0 - Bn))
        Bm, B0 = B0, Bn
        An = ((2*k+2-xs)*A0 - ((k+1)*Am if Am is not None else 0.0))/(k+1)
        Am, A0 = A0, An
    return out

# ------------------------------------------------------------------ the pre-registered test
BASIS = ('1', 'log n', 'sqrt n', 'n')
def detrend(ns, y):
    X = np.column_stack([np.ones_like(ns), np.log(ns), np.sqrt(ns), ns])
    c, *_ = np.linalg.lstsq(X, y, rcond=None)
    return y - X @ c

def score(ns, Y, O):
    Yd, Od = detrend(ns, Y), detrend(ns, O)
    R2 = 1 - np.sum((Yd-Od)**2)/np.sum(Yd**2)
    r = np.corrcoef(Yd, Od)[0, 1]
    return R2, r, Yd, Od

# ================================================================== main
if __name__ == "__main__":
    P(__doc__); P("="*100)
    t0 = time.time()

    # ---- exact lambda_n^arith for n<=40 from stage 1
    ex = json.load(open(os.path.join(HERE, 'att015_lambda_exact.json')))
    mp.dps = 50
    lam40      = np.array([float(mpf(x)) for x in ex['lam']])
    arith40_ex = np.array([float(mpf(x)) for x in ex['lam_arith']])
    arch40_ex  = np.array([float(mpf(x)) for x in ex['lam_arch']])

    # ---- closed-form arch, all n
    arch = lambda_arch(NBIG)
    P(f"CHECK (ARCH) closed form vs stage-1 Cauchy DFT, n=1..40: "
      f"max |diff| = {np.abs(arch[:40]-arch40_ex).max():.3e}   "
      f"max rel = {np.abs((arch[:40]-arch40_ex)/arch40_ex).max():.3e}    [{time.time()-t0:.1f}s]")

    # ---- lambda_n from the zeros, all n, and the matched-truncation audit
    g_all = np.load(os.path.join(HERE, 'att015_zeros_to_30000.npy'))
    P(f"\nMATCHED-TRUNCATION AUDIT on the ZERO side (the attempt-002 failure mode):")
    Yv = {}
    for Tcut in (10000.0, 20000.0, 30000.0):
        g = g_all[g_all < Tcut]
        # S(T) from the census, unwrapped theta
        mp.dps = 40
        Tl = float(g[-1])
        th = mp.im(mp.loggamma(mpf(1)/4 + 1j*mpf(Tl)/2)) - mpf(Tl)/2*mp.log(mp.pi)
        ST = float(len(g) - 1 - th/mp.pi)
        lam = lambda_from_zeros(g, NBIG, ST)
        Yv[Tcut] = lam - arch
        P(f"  T={Tcut:>7.0f}  zeros={len(g):>6}  S(T)={ST:+.5f}   "
          f"|lam_n - exact(BL)| for n<=40: max {np.abs(lam[:40]-lam40).max():.2e}")
    ref = Yv[30000.0]
    for Tcut in (10000.0, 20000.0):
        P(f"  Y_n(T={Tcut:.0e}) vs Y_n(T=3e4):  max |diff| over n<=40 "
          f"{np.abs(Yv[Tcut][:40]-ref[:40]).max():.2e}   over n<=3000 "
          f"{np.abs(Yv[Tcut]-ref).max():.2e}   (rms Y over n=200..3000 = "
          f"{ref[199:].std():.4f})")
    Y = ref.copy()
    P(f"  Y_n (zeros) vs Y_n (exact BL) for n<=40:  max |diff| = "
      f"{np.abs(Y[:40]-arith40_ex).max():.3e}")
    Y[:40] = arith40_ex          # use the exact values where we have them

    # ---- the line prediction
    P(f"\n[{time.time()-t0:.1f}s]  building line predictions ...")
    ms32, lam32 = prime_powers(32)
    P(f"  tape line set m <= 32: {list(map(int, ms32))}")

    # =========== PRIMARY, pre-registered: n = 1..40, M = 32
    P("\n" + "="*100)
    P("PRIMARY TEST (the brief's window):  n = 1..40,  M = 32  (the lines attempt 010 resolves)")
    ns40 = np.arange(1, 41, dtype=float)
    O40 = line_prediction(40, np.log(ms32), lam32/ms32, math.log(32))
    R2, r, Yd, Od = score(ns40, arith40_ex, O40)
    P(f"  R2 = {R2:+.4f}    r = {r:+.4f}   r^2 = {r*r:.4f}     "
      f"[NULL = R2<0.5 and r^2<0.5]  -> {'NULL HOLDS' if (R2<0.5 and r*r<0.5) else 'NULL REJECTED'}")
    P(f"  rms(Y detrended) = {Yd.std():.4f}   rms(O detrended) = {Od.std():.4f}")
    P("\n   n   lambda_n^arith(exact)    O_n(M=32)     Y-detr     O-detr    t0(n,m=2)=sqrt(n/log2)")
    for n in range(1, 41):
        P(f"  {n:>3}  {arith40_ex[n-1]:>20.10f}  {O40[n-1]:>12.6f} "
          f"{Yd[n-1]:>10.5f} {Od[n-1]:>10.5f}      {math.sqrt(n/math.log(2)):>8.3f}")

    # =========== SECONDARY: the resonant window n >> gamma_1^2 log 2 = 138
    P("\n" + "="*100)
    P("SECONDARY: the same test in the RESONANT window.  t0 = sqrt(n/log m) must exceed 14.134.")
    for lo, hi in ((1, 40), (1, 200), (200, 1000), (1000, 3000), (1, 3000)):
        ns = np.arange(lo, hi+1, dtype=float)
        O = line_prediction(hi, np.log(ms32), lam32/ms32, math.log(32))[lo-1:hi]
        R2, r, Yd, Od = score(ns, Y[lo-1:hi], O)
        P(f"  n in [{lo:>5},{hi:>5}]   t0(m=2) in [{math.sqrt(lo/math.log(2)):>6.1f},"
          f"{math.sqrt(hi/math.log(2)):>6.1f}]   R2 = {R2:+8.4f}   r = {r:+.4f}   "
          f"r^2 = {r*r:.4f}   rmsY = {Yd.std():.4f}  rmsO = {Od.std():.4f}")

    # =========== NOISE AUDIT: sweep M (prime-side truncation)
    P("\n" + "="*100)
    P("NOISE AUDIT -- prime-side truncation M (matched against the zero-side sweep above).")
    P(f"  {'M':>9}{'#lines':>8}   {'R2 n=1..40':>12}{'r n=1..40':>11}   "
      f"{'R2 n=200..3000':>16}{'r':>9}   {'R2 n=1..3000':>14}{'r':>9}")
    for M in (2, 3, 4, 5, 8, 16, 32, 100, 1000, 10000, 100000, 1000000):
        ms, lm = prime_powers(M)
        Ofull = line_prediction(NBIG, np.log(ms), lm/ms, math.log(M))
        row = f"  {M:>9}{len(ms):>8}   "
        for lo, hi in ((1, 40), (200, 3000), (1, 3000)):
            ns = np.arange(lo, hi+1, dtype=float)
            R2, r, _, _ = score(ns, Y[lo-1:hi], Ofull[lo-1:hi])
            row += f"{R2:>12.4f}{r:>11.4f}   " if hi == 40 else f"{R2:>16.4f}{r:>9.4f}   "
        P(row)

    # =========== CONTROLS
    P("\n" + "="*100)
    P("CONTROLS (must fail by MISSING STRUCTURE).  n = 200..3000, M = 32, 200 draws.")
    lo, hi = 200, 3000
    ns = np.arange(lo, hi+1, dtype=float)
    Otrue = line_prediction(hi, np.log(ms32), lam32/ms32, math.log(32))[lo-1:hi]
    R2t, rt, _, _ = score(ns, Y[lo-1:hi], Otrue)
    rng = np.random.default_rng(20260812)
    for name in ('random frequencies (amps kept)', 'permuted amplitudes (freqs kept)'):
        R2s, rs = [], []
        for _ in range(200):
            if name.startswith('random'):
                xs = rng.uniform(math.log(2), math.log(32), size=len(ms32))
                am = lam32/ms32
            else:
                xs = np.log(ms32); am = rng.permutation(lam32/ms32)
            Oc = line_prediction(hi, xs, am, math.log(32))[lo-1:hi]
            a, b, _, _ = score(ns, Y[lo-1:hi], Oc)
            R2s.append(a); rs.append(b)
        R2s, rs = np.array(R2s), np.array(rs)
        P(f"  {name:<34}  R2 median {np.median(R2s):+8.4f}  99th pct {np.percentile(R2s,99):+8.4f}"
          f"   |r| median {np.median(np.abs(rs)):.4f}  99th pct {np.percentile(np.abs(rs),99):.4f}")
    P(f"  {'TRUE line set':<34}  R2        {R2t:+8.4f}                       "
      f"   |r|        {abs(rt):.4f}")

    np.savez(os.path.join(HERE, 'att015_lines_out.npz'),
             Y=Y, arch=arch, O32=line_prediction(NBIG, np.log(ms32), lam32/ms32, math.log(32)))
    P(f"\n[{time.time()-t0:.1f}s] wrote att015_lines_out.npz")
