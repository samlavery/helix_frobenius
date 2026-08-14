"""ATTEMPT 030, stage 1.  lambda_n^arith for ZETA by two routes that share nothing,
then the pre-registered dyadic R^2 statistic pushed as high as it will go.

WHAT IS BEING COMPUTED
----------------------
Li's map  s = 1/(1-z),  z = 1 - 1/s.  Critical line <-> |z| = 1.

    sum_{n>=1} lambda_n z^{n-1} = d/dz log xi(1/(1-z)) = (xi'/xi)(s) * s^2

EXACT split xi = A * Z with A(s) = (1/2) s pi^{-s/2} Gamma(s/2), Z(s) = (s-1) zeta(s):

    lambda_n^arch  = [z^{n-1}] ( 1/s - (log pi)/2 + psi(s/2)/2 ) s^2      (DC, closed form)
    lambda_n^arith = [z^{n-1}] ( 1/(s-1) + zeta'/zeta(s) ) s^2           (AC, the object)

ROUTE A  (contour).  Cauchy DFT of the LOG-DERIVATIVE on |z| = r.  Single valued, no branch.
   UNCONDITIONALITY OF THE RADIUS, computed BEFORE running (rule 7):
   for rho = beta + i gamma,  |1 - 1/rho|^2 = 1 - (2 beta - 1)/(beta^2 + gamma^2).
   The image of a zero lies inside |z| < r iff (2beta-1)/(beta^2+gamma^2) > 1 - r^2.
   Since 2beta-1 < 1, this needs beta^2 + gamma^2 < 1/(1-r^2).
      r = 0.990 -> |gamma| < 7.09       r = 0.997 -> |gamma| < 12.92
   zeta has NO zero in the strip with |gamma| < 14.1347.  So BOTH radii are unconditional;
   nothing about RH is used.

ROUTE B  (Bombieri-Lagarias / Stieltjes).  (s-1)zeta(s) = 1 + sum_{k>=1} (-1)^{k-1} g_{k-1}
   (s-1)^k/(k-1)!  with g_j the Stieltjes constants (mpmath's own algorithm -- shares no code
   with route A).  b = log of that series;  eta_j = (j+1) b_{j+1};
   lambda_n^arith = sum_{k=1..n} C(n,k) eta_{k-1}.   Pure series algebra, no contour, no zeros.

THE STATISTIC (attempt 015's, unchanged, ZERO free parameters):
   O_n(M) = 1 - L_n(log M) - sum_{m <= M} Lambda(m)/m * L_{n-1}^{(1)}(log m)
   detrend both Y = lambda_n^arith and O against the FIXED basis {1, log n, sqrt n, n}
   R^2 = 1 - sum (Yd - Od)^2 / sum Yd^2.

STATED NULL (pre-registered, before any run)
--------------------------------------------
 N1  R^2 falls back below 0.5 on [320,640] / [640,1280] / [1280,2560] -- i.e. attempt 015's
     +0.9501 on [160,320] was a one-window accident.
 N3  the threshold is an artifact of holding M = 32: with M = 10^6 the small-n windows also
     score R^2 > 0.5, so nothing "switches on" at n = 138.
 N4  the threshold is an artifact of the DYADIC window shape / the 4-parameter detrend:
     changing the window ratio (1.5, 2, 3, 4) or the basis moves the crossing point by more
     than a factor 1.5.
COMPETING MECHANISM, also pre-registered with its own number.  Stationary phase on
   L_{n-1}^{(1)}(x) e^{-x/2} ~ n^{1/4} x^{-3/4} cos(2 sqrt(nx) - 3pi/4)/sqrt(pi) against the
   prime fluctuation e^{-x/2} sum_gamma e^{i gamma x} gives the resonance condition
       n = gamma^2 log m .
   So prime power m appears in lambda_n^arith only once some zero satisfies gamma^2 log m <= n,
   i.e. only for n >= gamma_1^2 log m.  For zeta, m=2: n >= 199.79*0.69315 = 138.5.
   The RIVAL is the detrend-absorption count: the m=2 tone completes
   c(n) = (sqrt(ratio)-1) sqrt(n) * 2 sqrt(log 2) / (2 pi) cycles per window; c = 1 at n = 83
   for ratio 2.  Both land near 100-160 on zeta, which is why stage 2 (Dirichlet L) is the
   real test: the resonance law moves with gamma_1, the absorption count does not.

POSITIVE CONTROL that must fail by MISSING STRUCTURE: replace the true frequencies log m by
   random frequencies in the same band, amplitudes kept.  R^2 must collapse.
"""
import sys, os, math, time, json
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
def P(*a):
    print(*a); sys.stdout.flush()

# ---------------------------------------------------------------- mpmath radix-2 FFT
def mpfft(a):
    N = len(a); assert N & (N-1) == 0
    out = list(a); j = 0
    for i in range(1, N):
        bit = N >> 1
        while j & bit:
            j ^= bit; bit >>= 1
        j |= bit
        if i < j: out[i], out[j] = out[j], out[i]
    length = 2
    while length <= N:
        ang = -2*mp.pi/length
        wl = mpc(mp.cos(ang), mp.sin(ang))
        half = length >> 1
        tw = [mpc(1)]
        for _ in range(half-1): tw.append(tw[-1]*wl)
        for i in range(0, N, length):
            for k in range(half):
                u = out[i+k]; v = out[i+k+half]*tw[k]
                out[i+k] = u+v; out[i+k+half] = u-v
        length <<= 1
    return out

def taylor_coeffs(fun, r, N, dps, nkeep):
    mp.dps = dps
    r = mpf(r); vals = [None]*N; half = N//2
    t0 = time.time()
    for j in range(half+1):
        z = r*mpc(mp.cos(2*mp.pi*j/N), mp.sin(2*mp.pi*j/N))
        vals[j] = fun(z)
        if j and j % 2000 == 0:
            P(f"      ... {j}/{half} [{time.time()-t0:.0f}s]")
    for j in range(half+1, N):
        vals[j] = mp.conj(vals[N-j])
    A = mpfft(vals)
    return [A[k]/(N*r**k) for k in range(nkeep)]

def h_arith_zeta(z):
    s = 1/(1-z)
    return (1/(s-1) + mp.zeta(s, 1, 1)/mp.zeta(s)) * s**2

# ---------------------------------------------------------------- Laguerre + lines
def laguerre1_dot(xs, amps, nmax):
    """S_n = sum_i amps_i * L_{n-1}^{(1)}(xs_i), n = 1..nmax, by the recurrence, chunked."""
    xs = np.asarray(xs, float); amps = np.asarray(amps, float)
    S = np.zeros(nmax)
    CH = 20000
    for a0 in range(0, xs.size, CH):
        x = xs[a0:a0+CH]; am = amps[a0:a0+CH]
        Lm = np.zeros_like(x); L0 = np.ones_like(x)
        for k in range(nmax):
            S[k] += L0 @ am
            Ln = ((2*k+2-x)*L0 - (k+1)*Lm)/(k+1)
            Lm, L0 = L0, Ln
    return S

def laguerre0(x, nmax):
    out = np.empty(nmax+1); Lm, L0 = 0.0, 1.0; out[0] = 1.0
    for k in range(nmax):
        Ln = ((2*k+1-x)*L0 - k*Lm)/(k+1); Lm, L0 = L0, Ln; out[k+1] = Ln
    return out

def prime_powers(M):
    M = int(M)
    sieve = np.ones(M+1, dtype=bool); sieve[:2] = False
    for p in range(2, int(M**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    ms, lam = [], []
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= M:
            ms.append(q); lam.append(math.log(int(p))); q *= int(p)
    o = np.argsort(ms)
    return np.array(ms, float)[o], np.array(lam, float)[o]

def line_prediction_zeta(nmax, M):
    ms, lam = prime_powers(M)
    S = laguerre1_dot(np.log(ms), lam/ms, nmax)
    L0t = laguerre0(math.log(M), nmax)
    return 1.0 - L0t[1:nmax+1] - S

# ---------------------------------------------------------------- statistic
def detrend(ns, y, basis='orig'):
    if basis == 'orig':   X = np.column_stack([np.ones_like(ns), np.log(ns), np.sqrt(ns), ns])
    elif basis == 'lin':  X = np.column_stack([np.ones_like(ns), ns])
    elif basis == 'p3':   v = np.sqrt(ns); X = np.column_stack([v**k for k in range(4)])
    elif basis == 'p6':   v = np.sqrt(ns); X = np.column_stack([v**k for k in range(7)])
    c, *_ = np.linalg.lstsq(X, y, rcond=None)
    return y - X @ c

def score(ns, Y, O, basis='orig'):
    Yd, Od = detrend(ns, Y, basis), detrend(ns, O, basis)
    R2 = 1 - np.sum((Yd-Od)**2)/np.sum(Yd**2)
    r = np.corrcoef(Yd, Od)[0, 1]
    return R2, r, Yd.std(), Od.std()

# ================================================================== main
if __name__ == "__main__":
    t0 = time.time()
    P(__doc__); P("="*104)
    NMAX = 8000
    cacheA = os.path.join(HERE, 'att030_Yzeta_r997.npy')
    cacheA2 = os.path.join(HERE, 'att030_Yzeta_r990.npy')

    P("ROUTE A  contour DFT of (1/(s-1) + zeta'/zeta) s^2")
    for rr, cache in (('0.997', cacheA), ('0.990', cacheA2)):
        if os.path.exists(cache): P(f"   r={rr}: cached"); continue
        P(f"   r={rr}, N=16384, dps=50 ...")
        cz = taylor_coeffs(h_arith_zeta, rr, 16384, 50, NMAX)
        np.save(cache, np.array([float(c.real) for c in cz]))
        P(f"   r={rr}: max |Im c| = {float(max(abs(c.imag) for c in cz[:NMAX])):.3e}  "
          f"[{time.time()-t0:.0f}s]")
    YA = np.load(cacheA); YA2 = np.load(cacheA2)
    P(f"   RADIUS STABILITY  r=0.997 vs r=0.990: max|diff| n<=3000 = "
      f"{np.abs(YA[:3000]-YA2[:3000]).max():.3e},  n<=8000 = {np.abs(YA-YA2).max():.3e}")
    P(f"   lambda_1^arith = {YA[0]:.12f}   (must be gamma_E = {np.euler_gamma:.12f})")
    P(f"   rms(Y) 200..3000 = {YA[199:3000].std():.4f}   max|Y| n<=3000 = "
      f"{np.abs(YA[:3000]).max():.4f} at n={int(np.argmax(np.abs(YA[:3000])))+1}")

    P("\nROUTE B  Stieltjes -> eta_j -> binomial sum (no contour, no zeros)")
    JB = 260
    mp.dps = 260
    a = [mpf(1)]
    for k in range(1, JB+2):
        a.append((-1)**(k-1) * mp.stieltjes(k-1) / mp.factorial(k-1))
    b = [mpf(0)]*(JB+2)
    for n in range(1, JB+2):
        acc = a[n]
        for k in range(1, n):
            acc -= mpf(k)*b[k]*a[n-k]/mpf(n)
        b[n] = acc
    eta = [mpf(i+1)*b[i+1] for i in range(JB+1)]
    P(f"   eta_0 = {mp.nstr(eta[0],20)}   gamma_E = {mp.nstr(mp.euler,20)}   "
      f"diff {mp.nstr(abs(eta[0]-mp.euler),3)}")
    NB = 250
    YB = np.zeros(NB)
    for n in range(1, NB+1):
        acc = mpf(0)
        for k in range(1, n+1):
            acc += mp.binomial(n, k)*eta[k-1]
        YB[n-1] = float(acc)
    rel = np.abs(YA[:NB]-YB)/np.maximum(np.abs(YB), 1.0)
    P(f"   ROUTE A vs ROUTE B, n=1..{NB}: max ABS diff = {np.abs(YA[:NB]-YB).max():.3e},  "
      f"max REL = {rel.max():.3e}   [{time.time()-t0:.0f}s]")

    P("\n   third opinion: attempt 015's 35673-zero census route (different data entirely)")
    try:
        npz = np.load(os.path.join(HERE, 'att015_lines_out.npz'))
        P(f"   census Y vs MY route A, n=200..3000: max|diff| = "
          f"{np.abs(npz['Y'][199:]-YA[199:3000]).max():.3e}")
    except Exception as e:
        P(f"   (unavailable: {e})")

    # ------------------------------------------------------------ the statistic
    P("\n" + "="*104)
    P("N1  dyadic R^2, M = 32, basis {1, log n, sqrt n, n}, ZERO free parameters")
    O32 = line_prediction_zeta(NMAX, 32)
    P(f"  {'window':>16}{'R2':>11}{'r':>9}{'rmsYd':>10}{'rmsOd':>10}{'rmsYd/n^.25':>13}"
      f"{'cycles(m=2)':>13}")
    wins = [(10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(640,1280),(1280,2560),
            (2560,5120),(4000,8000)]
    for lo, hi in wins:
        ns = np.arange(lo, hi+1, dtype=float)
        R2, r_, sy, so = score(ns, YA[lo-1:hi], O32[lo-1:hi])
        cyc = (math.sqrt(hi)-math.sqrt(lo))*2*math.sqrt(math.log(2))/(2*math.pi)
        P(f"  [{lo:>5},{hi:>5}]{R2:>11.4f}{r_:>9.4f}{sy:>10.4f}{so:>10.4f}"
          f"{sy/(0.5*(lo+hi))**0.25:>13.4f}{cyc:>13.2f}")

    P("\nN3  the M-artifact test: same windows, M = 2, 32, 10^3, 10^6")
    Os = {M: line_prediction_zeta(NMAX, M) for M in (2, 32, 1000, 1000000)}
    P(f"  {'window':>16}" + "".join(f"{'R2 M='+str(M):>14}" for M in (2,32,1000,1000000)))
    for lo, hi in wins:
        ns = np.arange(lo, hi+1, dtype=float)
        row = f"  [{lo:>5},{hi:>5}]"
        for M in (2,32,1000,1000000):
            R2, *_ = score(ns, YA[lo-1:hi], Os[M][lo-1:hi]); row += f"{R2:>14.4f}"
        P(row)

    P("\nN4  window-shape and basis sensitivity of the crossing point R^2 = 0.5")
    P("    windows [n, ratio*n]; report the smallest n on a log grid with R^2 >= 0.5 "
      "and staying >= 0.5")
    grid = np.unique(np.round(np.exp(np.linspace(math.log(12), math.log(3000), 160))).astype(int))
    for basis in ('orig','lin','p3','p6'):
        row = f"    basis {basis:>5}: "
        for ratio in (1.5, 2.0, 3.0, 4.0):
            cross = None
            for n0 in grid:
                n1 = int(n0*ratio)
                if n1 > NMAX or n1-n0 < 8: continue
                ns = np.arange(n0, n1+1, dtype=float)
                R2, *_ = score(ns, YA[n0-1:n1], O32[n0-1:n1], basis)
                if R2 >= 0.5:
                    ok = True
                    for m in (1.3, 1.8, 2.6):
                        n2 = int(n0*m); n3 = int(n2*ratio)
                        if n3 > NMAX: continue
                        ns2 = np.arange(n2, n3+1, dtype=float)
                        R22, *_ = score(ns2, YA[n2-1:n3], O32[n2-1:n3], basis)
                        if R22 < 0.5: ok = False; break
                    if ok: cross = n0; break
            row += f"  ratio {ratio}: n*={cross}"
        P(row)

    P("\nPOSITIVE CONTROL (must fail by MISSING structure): random frequencies, amps kept")
    rng = np.random.default_rng(30)
    ms32, lm32 = prime_powers(32)
    for lo, hi in ((160,320),(320,640),(1280,2560)):
        ns = np.arange(lo, hi+1, dtype=float)
        R2t, *_ = score(ns, YA[lo-1:hi], O32[lo-1:hi])
        R2s = []
        for _ in range(120):
            xs = rng.uniform(math.log(2), math.log(32), size=ms32.size)
            Sc = laguerre1_dot(xs, lm32/np.exp(xs), hi)
            Oc = 1.0 - laguerre0(math.log(32), hi)[1:hi+1] - Sc
            a_, *_ = score(ns, YA[lo-1:hi], Oc[lo-1:hi]); R2s.append(a_)
        R2s = np.array(R2s)
        P(f"  [{lo},{hi}]  TRUE R2 = {R2t:+.4f}   control median {np.median(R2s):+.4f}  "
          f"99th {np.percentile(R2s,99):+.4f}  max {R2s.max():+.4f}")

    np.savez(os.path.join(HERE, 'att030_zeta_out.npz'), Y=YA, O32=O32)
    P(f"\n[{time.time()-t0:.0f}s] stage 1 done")
