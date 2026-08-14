"""ADVERSARIAL INDEPENDENT VERIFICATION of attempt 015.

Everything here is computed from scratch.  In particular NOTHING uses their zero census
(att015_zeros_to_30000.npy) and NOTHING uses log xi (so no branch-unwrapping risk):
lambda_n is extracted from the LOGARITHMIC DERIVATIVE, which is single valued.

    s = 1/(1-z),   z = 1 - 1/s        (Li's map; critical line <-> |z| = 1 exactly)
    sum_{n>=1} lambda_n z^{n-1} = d/dz log xi(1/(1-z)) = (xi'/xi)(s) * s^2

with the EXACT split  xi = A * Z,   A(s) = (1/2) s pi^{-s/2} Gamma(s/2),  Z(s) = (s-1) zeta(s):

    A'/A (s) = 1/s - (log pi)/2 + psi(s/2)/2
    Z'/Z (s) = 1/(s-1) + zeta'/zeta (s)

    lambda_n^arch  = [z^{n-1}] (A'/A)(s) s^2
    lambda_n^arith = [z^{n-1}] (Z'/Z)(s) s^2      <-- equals sum_k C(n,k) eta_{k-1} (Bombieri-Lagarias)

Coefficients by Cauchy DFT on |z| = r using an mpmath radix-2 FFT (so no double-precision
cancellation: at r=0.99, n=3000 the extraction divides by r^n ~ 8e-14).

Two radii:
  r = 0.6 / 0.8  ->  s-disk with |Im s| <= 0.94 / 2.23 : PROVABLY zero free (first zero 14.134).
                     Unconditional.  Gives n up to ~400 at dps=110.
  r = 0.99       ->  s-disk with |Im s| <= 49.75 ; on-line zeros have |1-1/s| = 1 > 0.99 so they
                     are OUTSIDE; needs only "no off-line zero below height 50".  n up to 3000.
"""
import sys, os, math, json, time
import numpy as np
from mpmath import mp, mpf, mpc

HERE = os.path.dirname(os.path.abspath(__file__))
def P(*a):
    print(*a); sys.stdout.flush()

# ------------------------------------------------------------------ mpmath radix-2 FFT
def mpfft(a):
    """forward DFT  A_k = sum_j a_j exp(-2 pi i j k / N),  N a power of two, a list of mpc."""
    N = len(a)
    assert N & (N-1) == 0
    # bit reversal
    out = list(a)
    j = 0
    for i in range(1, N):
        bit = N >> 1
        while j & bit:
            j ^= bit; bit >>= 1
        j |= bit
        if i < j:
            out[i], out[j] = out[j], out[i]
    length = 2
    while length <= N:
        # w = exp(-2 pi i / length)
        ang = -2*mp.pi/length
        wl = mpc(mp.cos(ang), mp.sin(ang))
        half = length >> 1
        # precompute twiddles
        tw = [mpc(1)]
        for _ in range(half-1):
            tw.append(tw[-1]*wl)
        for i in range(0, N, length):
            for k in range(half):
                u = out[i+k]; v = out[i+k+half]*tw[k]
                out[i+k] = u+v; out[i+k+half] = u-v
        length <<= 1
    return out

def taylor_coeffs(fun, r, N, dps, use_conj=True):
    """c_k = [z^k] fun, k = 0..N-1, by DFT on |z| = r.  fun must be analytic in |z|<=r
       and have REAL Taylor coefficients (so f(conj z) = conj f(z))."""
    mp.dps = dps
    r = mpf(r)
    vals = [None]*N
    half = N//2
    for j in range(half+1):
        z = r*mpc(mp.cos(2*mp.pi*j/N), mp.sin(2*mp.pi*j/N))
        vals[j] = fun(z)
    if use_conj:
        for j in range(half+1, N):
            vals[j] = mp.conj(vals[N-j])
    else:
        for j in range(half+1, N):
            z = r*mpc(mp.cos(2*mp.pi*j/N), mp.sin(2*mp.pi*j/N))
            vals[j] = fun(z)
    A = mpfft(vals)
    return [A[k]/(N*r**k) for k in range(N)]

# ------------------------------------------------------------------ the integrands
def h_arch(z):
    s = 1/(1-z)
    return (1/s - mp.log(mp.pi)/2 + mp.digamma(s/2)/2) * s**2

def h_arith(z):
    s = 1/(1-z)
    return (1/(s-1) + mp.zeta(s, derivative=1)/mp.zeta(s)) * s**2

# ------------------------------------------------------------------ closed form arch (rederived)
# d/ds log A = -(log pi + gamma)/2 + sum_k [ 1/(2k) - 1/(2k+s) ]      (Weierstrass on 1/Gamma)
# [z^{n-1}] of that composed with s(z), /(1-z)^2:
#   lambda_n^arch = -(log pi + gamma) n/2 + sum_{k>=1} [ n/(2k) - 1 + (2k/(2k+1))^n ]
# regroup: n/(2k) = n/(2k+1) + n/(2k(2k+1)),  sum_k n/(2k(2k+1)) = n(1-log 2)
def lambda_arch_closed(nmax, K=300_000, JMAX=60):
    n = np.arange(1, nmax+1, dtype=np.float64)
    acc = np.zeros(nmax)
    B = 4000
    for a in range(1, K+1, B):
        kk = np.arange(a, min(a+B, K+1), dtype=np.float64)
        u = 1.0/(2*kk+1)
        lg = np.log1p(-u)
        acc += (np.exp(np.outer(n, lg)) - 1.0 + np.outer(n, u)).sum(axis=1)
    mp.dps = 40
    tail = np.zeros(nmax)
    for j in range(2, JMAX+1):
        Zj = float(mp.zeta(j, mpf(K) + mpf(3)/2)) / 2.0**j
        Cnj = np.array([float(mp.binomial(int(x), j)) if x >= j else 0.0 for x in n])
        tail += ((-1)**j) * Cnj * Zj
    return (-(math.log(math.pi)+np.euler_gamma)*n/2 + n*(1-math.log(2)) + acc + tail)

# ------------------------------------------------------------------ line prediction
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

def laguerre_alpha1_table(xs, nmax):
    """L_k^{(1)}(x) for k = 0..nmax-1, shape (nmax, len(xs)).  (k+1)L_{k+1}=(2k+2-x)L_k-(k+1)L_{k-1}"""
    xs = np.asarray(xs, float)
    T = np.empty((nmax, xs.size))
    Lm = np.zeros_like(xs); L0 = np.ones_like(xs)
    for k in range(nmax):
        T[k] = L0
        Ln = ((2*k+2-xs)*L0 - (k+1)*Lm)/(k+1)
        Lm, L0 = L0, Ln
    return T

def laguerre_alpha0(x, nmax):
    """L_k(x), k=0..nmax"""
    out = np.empty(nmax+1)
    Lm, L0 = 0.0, 1.0
    out[0] = 1.0
    for k in range(nmax):
        Ln = ((2*k+1-x)*L0 - k*Lm)/(k+1)
        Lm, L0 = L0, Ln
        out[k+1] = Ln
    return out

def line_prediction(nmax, ms, lam, M):
    xs = np.log(ms); amps = lam/ms
    T = laguerre_alpha1_table(xs, nmax)          # rows k=0..nmax-1 -> L_{n-1}^{(1)}
    S = T @ amps
    L0tab = laguerre_alpha0(math.log(M), nmax)   # L_n(log M), n=1..nmax
    return -(S - (1.0 - L0tab[1:nmax+1]))

# ------------------------------------------------------------------ the pre-registered statistic
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
    t0 = time.time()
    P(__doc__); P("="*100)

    # ---------------- STEP 1: small n, UNCONDITIONAL radii, two of them
    P("STEP 1  lambda_n, n = 1..40, by my own Cauchy DFT of the LOG-DERIVATIVE (no log, no unwrap)")
    res = {}
    for r, N, dps in (('0.6', 256, 90), ('0.8', 512, 110)):
        ca = taylor_coeffs(h_arch,  r, N, dps)
        cz = taylor_coeffs(h_arith, r, N, dps)
        arch = [ca[n-1].real for n in range(1, 41)]
        arith = [cz[n-1].real for n in range(1, 41)]
        res[r] = (arch, arith)
        mi = max(abs(cz[n-1].imag) for n in range(1, 41))
        P(f"  r={r} N={N} dps={dps}: max |Im c| over n<=40 = {mp.nstr(mi,3)}   [{time.time()-t0:.0f}s]")
    mp.dps = 50
    a6, t6 = res['0.6']; a8, t8 = res['0.8']
    warch = max(abs(a6[i]-a8[i])/abs(a8[i]) for i in range(40))
    warit = max(abs(t6[i]-t8[i])/max(abs(t8[i]), mpf(1)) for i in range(40))
    P(f"  MY r=0.6 vs r=0.8: worst rel disagreement arch {mp.nstr(warch,3)}  arith {mp.nstr(warit,3)}")

    lam_mine = [a8[i]+t8[i] for i in range(40)]
    LIT = {1: '0.0230957089661210', 2: '0.0923457352880', 3: '0.207639', 4: '0.368790'}
    for k, v in LIT.items():
        P(f"  lambda_{k} = {mp.nstr(lam_mine[k-1], 18)}   literature {v}")

    # arch closed form (my own rederivation) vs my contour
    archcf = lambda_arch_closed(3000)
    d = max(abs(float(a8[i]) - archcf[i]) for i in range(40))
    P(f"  CLOSED-FORM arch (my rederivation) vs my contour, n<=40: max |diff| = {d:.3e}")

    # compare with THEIR stored exact values
    ex = json.load(open(os.path.join(HERE, 'att015_lambda_exact.json')))
    mp.dps = 50
    their_lam   = [mpf(x) for x in ex['lam']]
    their_arith = [mpf(x) for x in ex['lam_arith']]
    their_arch  = [mpf(x) for x in ex['lam_arch']]
    dl = max(abs(lam_mine[i]-their_lam[i])/abs(their_lam[i]) for i in range(40))
    da = max(abs(t8[i]-their_arith[i])/max(abs(their_arith[i]), mpf(1)) for i in range(40))
    P(f"  MINE vs THEIRS (n<=40): lambda_n worst rel {mp.nstr(dl,3)}   arith worst rel {mp.nstr(da,3)}")

    # ---------------- STEP 2: unconditional radius r=0.8 pushed to n=400
    P(f"\nSTEP 2  lambda_n^arith to n = 400 at r = 0.8 (|Im s| < 2.23, PROVABLY zero-free) "
      f"[{time.time()-t0:.0f}s]")
    cz400 = taylor_coeffs(h_arith, '0.8', 1024, 200)
    Y400 = np.array([float(cz400[n-1].real) for n in range(1, 401)])
    mi = max(abs(cz400[n-1].imag) for n in range(1, 401))
    P(f"  max |Im c| over n<=400 = {mp.nstr(mi,3)}  (must be ~0)")

    # ---------------- STEP 3: r = 0.99 contour to n = 3000, INDEPENDENT of any zero census
    P(f"\nSTEP 3  lambda_n^arith to n = 3000 at r = 0.99 by mpmath FFT [{time.time()-t0:.0f}s]")
    czbig = taylor_coeffs(h_arith, '0.99', 4096, 60)
    Ybig = np.array([float(czbig[n-1].real) for n in range(1, 3001)])
    mi = max(abs(czbig[n-1].imag) for n in range(1, 3001))
    P(f"  max |Im c| over n<=3000 = {mp.nstr(mi,3)}   [{time.time()-t0:.0f}s]")
    P(f"  r=0.8 (n<=400) vs r=0.99: max |diff| = {np.abs(Y400-Ybig[:400]).max():.3e}  "
      f"(rms Y over 200..400 = {Ybig[199:400].std():.4f})")

    # their Y (from the 35673-zero census)
    npz = np.load(os.path.join(HERE, 'att015_lines_out.npz'))
    Ythem = npz['Y']; O32them = npz['O32']; archthem = npz['arch']
    P(f"  THEIR Y (zero census) vs MINE (contour): max |diff| n<=3000 = "
      f"{np.abs(Ythem-Ybig).max():.3e}, n in 200..3000 = {np.abs(Ythem[199:]-Ybig[199:]).max():.3e}")
    P(f"  THEIR arch vs MY closed form: max |diff| = {np.abs(archthem-archcf).max():.3e}")
    P(f"  MY  max|lambda_n^arith| over n<=3000 = {np.abs(Ybig).max():.4f} at n = "
      f"{int(np.argmax(np.abs(Ybig)))+1}")
    P(f"  MY  rms(Y) over n=200..3000 = {Ybig[199:].std():.4f}   "
      f"max |arith|/|arch| over 200..3000 = {np.abs(Ybig[199:]/archcf[199:]).max():.3e}")
    P(f"  MY  lambda_3000 = {archcf[2999]+Ybig[2999]:.4f}")

    Y = Ybig   # everything below uses MY numbers

    # ---------------- STEP 4: the pre-registered R2 statistic
    P("\n" + "="*100)
    P("STEP 4  the pre-registered statistic, MY Y, MY Laguerre.  R2 = 1 - sum(Yd-Od)^2/sum(Yd^2)")
    ms32, lm32 = prime_powers(32)
    O32 = line_prediction(3000, ms32, lm32, 32)
    P(f"  MY O_n(M=32) vs THEIRS: max |diff| = {np.abs(O32-O32them).max():.3e}")
    # spot-check Laguerre against mpmath
    mp.dps = 40
    for (n, x) in ((40, math.log(2)), (1000, math.log(3)), (3000, math.log(13))):
        mine = laguerre_alpha1_table([x], n)[n-1, 0]
        ref = float(mp.laguerre(n-1, 1, x))
        P(f"  Laguerre check L_{{{n-1}}}^(1)({x:.4f}): recurrence {mine:.10g}  mpmath {ref:.10g}  "
          f"rel {abs(mine-ref)/abs(ref):.2e}")

    ns40 = np.arange(1, 41, dtype=float)
    R2, r_, Yd, Od = score(ns40, Y[:40], O32[:40])
    P(f"\n  PRIMARY n=1..40, M=32:  R2 = {R2:+.4f}   r = {r_:+.4f}   r^2 = {r_*r_:.4f}   "
      f"rms(Yd) = {Yd.std():.4f}")

    P("\n  dyadic windows, M=32 (their headline: the threshold at n = gamma_1^2 log 2 = 138):")
    P(f"  {'window':>16}{'R2':>12}{'r':>9}{'rmsYd':>10}{'rmsYd/n^0.25':>14}")
    for lo, hi in ((10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(640,1280),
                   (1280,2560),(2560,3000)):
        ns = np.arange(lo, hi+1, dtype=float)
        R2, r_, Yd, Od = score(ns, Y[lo-1:hi], O32[lo-1:hi])
        P(f"  [{lo:>5},{hi:>5}]{R2:>12.4f}{r_:>9.4f}{Yd.std():>10.4f}"
          f"{Yd.std()/ (0.5*(lo+hi))**0.25:>14.4f}")

    P("\n  ADVERSARIAL: the SAME dyadic windows with M = 10^6 instead of 32.")
    P("  (O_n(M) -> lambda_n^arith identically as M->inf -- Bombieri-Lagarias.  If R2 goes to 1")
    P("   at SMALL n too, the 'gamma_1 resonance threshold' is an artifact of holding M=32.)")
    msB, lmB = prime_powers(1000000)
    OB = line_prediction(3000, msB, lmB, 1000000)
    P(f"  {'window':>16}{'R2(M=32)':>12}{'R2(M=1e6)':>12}{'r(M=1e6)':>10}")
    for lo, hi in ((1,40),(10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(200,3000)):
        ns = np.arange(lo, hi+1, dtype=float)
        R2a, _, _, _ = score(ns, Y[lo-1:hi], O32[lo-1:hi])
        R2b, rb, _, _ = score(ns, Y[lo-1:hi], OB[lo-1:hi])
        P(f"  [{lo:>5},{hi:>5}]{R2a:>12.4f}{R2b:>12.4f}{rb:>10.4f}")

    P("\n  M sweep at n = 200..3000 (their table) and at n = 1..40:")
    ns = np.arange(200, 3001, dtype=float)
    ns40 = np.arange(1, 41, dtype=float)
    P(f"  {'M':>9}{'#lines':>8}{'R2 200..3000':>15}{'r':>9}{'R2 1..40':>11}{'r':>9}")
    for M in (2,3,4,5,8,16,32,100,1000,10000,100000,1000000):
        msM, lmM = prime_powers(M)
        OM = line_prediction(3000, msM, lmM, M)
        R2a, ra, _, _ = score(ns, Y[199:3000], OM[199:3000])
        R2b, rb, _, _ = score(ns40, Y[:40], OM[:40])
        P(f"  {M:>9}{len(msM):>8}{R2a:>15.4f}{ra:>9.4f}{R2b:>11.4f}{rb:>9.4f}")

    # ---------------- STEP 5: controls
    P("\n" + "="*100)
    P("STEP 5  controls at n=200..3000, M=32, 200 draws (my own RNG seed)")
    lo, hi = 200, 3000
    ns = np.arange(lo, hi+1, dtype=float)
    R2t, rt, _, _ = score(ns, Y[lo-1:hi], O32[lo-1:hi])
    rng = np.random.default_rng(7)
    for name in ('random freqs (amps kept)', 'permuted amps (freqs kept)'):
        R2s, rs = [], []
        for _ in range(200):
            if name.startswith('random'):
                xs = np.exp(rng.uniform(math.log(2), math.log(32), size=len(ms32)))
                am = lm32
            else:
                xs = ms32.copy(); am = rng.permutation(lm32)
            Oc = line_prediction(hi, xs, am, 32)
            a, b, _, _ = score(ns, Y[lo-1:hi], Oc[lo-1:hi])
            R2s.append(a); rs.append(b)
        R2s, rs = np.array(R2s), np.array(rs)
        P(f"  {name:<28} R2 med {np.median(R2s):+8.4f} 99th {np.percentile(R2s,99):+8.4f}  "
          f"|r| med {np.median(np.abs(rs)):.4f} 99th {np.percentile(np.abs(rs),99):.4f}")
    P(f"  {'TRUE':<28} R2     {R2t:+8.4f}                    |r|     {abs(rt):.4f}")

    # ---------------- STEP 6: the closed-form spectral law
    P("\n" + "="*100)
    P("STEP 6  spectral law:  Y_n/n^{1/4} = DC + sum_m a_m cos(omega_m sqrt n + pi/4),")
    P("        omega_m = 2 sqrt(log m),  a_m = Lambda(m)/(sqrt(pi) sqrt(m) (log m)^{3/4})")
    def spectrum(nsv, gt, omegas):
        v = np.sqrt(nsv); V = v[-1]-v[0]
        w = 1.0/(2*np.sqrt(nsv))
        E = np.exp(-1j*np.outer(np.asarray(omegas, float), v))
        return (2.0/V)*(E*(gt*w)).sum(axis=1)
    def detrend_poly(v, y, deg=3):
        X = np.vander(v - v.mean(), deg+1)
        c, *_ = np.linalg.lstsq(X, y, rcond=None)
        return y - X @ c
    for (lo, hi) in ((200, 3000), (500, 3000), (1000, 3000)):
        nsv = np.arange(lo, hi+1, dtype=float)
        g = Y[lo-1:hi]/nsv**0.25
        gt = detrend_poly(np.sqrt(nsv), g, 3)
        V = math.sqrt(hi)-math.sqrt(lo)
        ray = 2*math.pi/V
        mlist = [2,3,4,5,7,8,9,11,13]
        oms = [2*math.sqrt(math.log(m)) for m in mlist]
        A = spectrum(nsv, gt, oms)
        preds = [ (math.log(p) if True else 0) for p in mlist]
        rows = []
        for i, m in enumerate(mlist):
            Lam = math.log(2) if m in (2,4,8) else (math.log(3) if m in (3,9) else math.log(m))
            a_m = Lam/(math.sqrt(math.pi)*math.sqrt(m)*math.log(m)**0.75)
            rows.append((m, abs(A[i]), a_m, abs(A[i])/a_m,
                         (np.angle(A[i])-math.pi/4+math.pi) % (2*math.pi) - math.pi))
        ratios = np.array([x[3] for x in rows])
        phases = np.array([x[4] for x in rows])
        P(f"\n  window n = {lo}..{hi}   Rayleigh bin = {ray:.4f}")
        P("   m   |A|      a_m      obs/pred   arg-pi/4")
        for m, aa, ap, rr, ph in rows:
            P(f"  {m:>3} {aa:8.4f} {ap:8.4f} {rr:9.3f} {ph:+9.3f}")
        P(f"   median obs/pred = {np.median(ratios):.3f}   median |arg-pi/4| = "
          f"{np.median(np.abs(phases)):.3f} rad")
        # noise floors
        rng2 = np.random.default_rng(11)
        band = rng2.uniform(1.70, 4.20, 4000)
        keep = np.array([min(abs(w-o) for o in
                             [2*math.sqrt(math.log(mm)) for mm in
                              [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32]]) > 1.5*ray
                         for w in band])
        band = band[keep]
        Ab = np.abs(spectrum(nsv, gt, band))
        lf = np.linspace(0.40, 1.60, 400)
        Al = np.abs(spectrum(nsv, gt, lf))
        w6 = 2*math.sqrt(math.log(6))
        A6 = abs(spectrum(nsv, gt, [w6])[0])
        P(f"   floors: line-free [0.4,1.6] med {np.median(Al):.4f} 99th {np.percentile(Al,99):.4f}"
          f" | in-band random ({keep.sum()}) med {np.median(Ab):.4f} 99th {np.percentile(Ab,99):.4f}"
          f" | m=6 (Lambda=0) {A6:.4f}")
        P(f"   lines |A| range {min(x[1] for x in rows):.4f}..{max(x[1] for x in rows):.4f}")

    P(f"\n[{time.time()-t0:.0f}s] done")
