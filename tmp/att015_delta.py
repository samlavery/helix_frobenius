"""ATTEMPT 015, stage 6 -- the clean version: difference against the rigid zero set.

Stage 5 showed the rigid surrogate gamma~_k = theta^{-1}(pi(k-1)) is a BAD control on its own:
its first zero sits at 17.850 instead of 14.135, and f_n(t) = 4 sin^2(n arctan(1/(2t))) is a
CHIRP in n at fixed t, so displacing a low zero injects broadband power in the v = sqrt(n)
spectrum -- the control fails by ADDING structure, which the campaign design law forbids.

The fix is to DIFFERENCE, which is also the correct DC-first move:

    Delta_n := sum_k [ f_n(gamma_k) - f_n(gamma~_k) ]  -  f_n(T) S(T)      =   int f_n dS

Both sets have identical count and identical smooth density, so the entire archimedean common
mode -- and the chirp -- cancels EXACTLY, with no model subtracted.  Delta_n is precisely the
zero-density fluctuation integrated against the Li kernel, and the line prediction is unchanged:

    Delta_n / n^{1/4} = smooth + sum_m a_m cos(omega_m sqrt n + pi/4),
    omega_m = 2 sqrt(log m),   a_m = Lambda(m)/(sqrt(pi) sqrt(m) (log m)^{3/4}).

CONTROLS
  C1  omega = 2 sqrt(log m), m composite non-prime-power: a_m = 0 EXACTLY.
  C2  omega in [0.40, 1.60]: below the m=2 line, provably line-free.
  C3  BLOCK SHUFFLE.  Permute the displacement sequence delta_k = gamma_k - gamma~_k in blocks
      of 200 consecutive zeros.  Local spacing statistics are preserved exactly; the coherence
      between a fluctuation and the HEIGHT that produced it is destroyed.  Fails by MISSING
      structure.  PRE-REGISTERED: the lines must collapse into the floor.
"""
import sys, os, math, time
import numpy as np

def P(*a):
    print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
NBIG = 8000

def prime_powers(M):
    M = int(M); sieve = np.ones(M+1, bool); sieve[:2] = False
    for p in range(2, int(M**0.5)+1):
        if sieve[p]: sieve[p*p::p] = False
    ms, lam = [], []
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= M: ms.append(q); lam.append(math.log(p)); q *= int(p)
    o = np.argsort(ms); return np.array(ms, float)[o], np.array(lam, float)[o]

def theta_f(t):  return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def theta_p(t):  return 0.5*np.log(t/(2*np.pi)) - 1/(48*t**2) - 21/(5760*t**4)

def delta_series(gam, tld, ST, nmax):
    a1 = np.arctan(1.0/(2*gam)); a2 = np.arctan(1.0/(2*tld))
    T = float(gam[-1]); aT = math.atan(1.0/(2*T))
    out = np.empty(nmax)
    for n in range(1, nmax+1):
        out[n-1] = (np.sum(4*np.sin(n*a1)**2 - 4*np.sin(n*a2)**2)
                    - 4*math.sin(n*aT)**2*ST)
    return out

def spectrum(ns, gt, omegas):
    v = np.sqrt(ns); V = v[-1]-v[0]; w = 1.0/(2*np.sqrt(ns))
    E = np.exp(-1j*np.outer(np.asarray(omegas, float), v))
    return (2.0/V)*(E*(gt*w)).sum(axis=1)

def detrend_poly(v, y, deg=3):
    X = np.vander(v - v.mean(), deg+1)
    c, *_ = np.linalg.lstsq(X, y, rcond=None); return y - X @ c

if __name__ == "__main__":
    P(__doc__); P("="*100)
    t0 = time.time()
    gam = np.load(os.path.join(HERE, 'att015_zeros_to_30000.npy')); K = len(gam)
    y = np.pi*np.arange(0, K, dtype=float)
    tld = np.full(K, 30.0)
    for _ in range(200): tld = np.clip(tld - (theta_f(tld)-y)/theta_p(tld), 17.85, 1e6)
    ST = 0.75761045
    P(f"  {K} true zeros, {K} rigid zeros;  max |theta(g~)/pi - (k-1)| = "
      f"{np.abs(theta_f(tld)/np.pi - np.arange(K)).max():.1e}")
    P(f"  displacement delta_k = gamma_k - gamma~_k :  mean {np.mean(gam-tld):+.4f}   "
      f"rms {np.std(gam-tld):.4f}   max|.| {np.abs(gam-tld).max():.4f}")

    D = delta_series(gam, tld, ST, NBIG)
    P(f"[{time.time()-t0:.0f}s]  Delta_n built.  rms(Delta) over n=200..8000 = {D[199:].std():.4f}")

    NLO = 200
    ns = np.arange(NLO, NBIG+1, dtype=float); v = np.sqrt(ns); V = v[-1]-v[0]; bin_ = 2*math.pi/V
    gt = detrend_poly(v, D[NLO-1:NBIG]/ns**0.25, deg=3)

    ms, lms = prime_powers(64)
    om = 2*np.sqrt(np.log(ms))
    a_pred = lms/(math.sqrt(math.pi)*np.sqrt(ms)*np.log(ms)**0.75)
    A = spectrum(ns, gt, om)
    rng = np.random.default_rng(99)
    Afloor = np.abs(spectrum(ns, gt, rng.uniform(0.40, 1.60, 3000)))
    msall, _ = prime_powers(4000); omall = 2*np.sqrt(np.log(msall))
    comp = np.array([m for m in range(6, 41) if m not in set(msall.astype(int))], float)
    omc = 2*np.sqrt(np.log(comp))
    kc = np.min(np.abs(omc[:, None]-omall[None, :]), axis=1) > 1.0*bin_
    Ac = np.abs(spectrum(ns, gt, omc[kc]))

    P(f"\n  window n={NLO}..{NBIG},  V={V:.2f},  Rayleigh bin {bin_:.4f} rad")
    P(f"  C2 FLOOR (line-free band omega in [0.40,1.60]): median {np.median(Afloor):.4f}  "
      f"90th {np.percentile(Afloor,90):.4f}  99th {np.percentile(Afloor,99):.4f}  "
      f"max {Afloor.max():.4f}")
    P(f"  C1 CONTROL (omega = 2 sqrt(log m), m = {[int(x) for x in comp[kc]]}, a_m = 0 EXACTLY): "
      f"{', '.join(f'{x:.4f}' for x in Ac)}")

    sep = np.array([min(abs(o-o2) for o2 in omall if abs(o2-o) > 1e-12) for o in om])
    P(f"\n  {'m':>4}{'Lam(m)':>9}{'omega_m':>10}{'sep/bin':>9}{'a_m pred':>11}{'|A| obs':>10}"
      f"{'obs/pred':>10}{'arg A':>9}{'arg-pi/4':>10}{'A/floor90':>11}")
    rat, phs = [], []
    fl = np.percentile(Afloor, 90)
    for i, m in enumerate(ms):
        if m > 32: continue
        ph = math.atan2(A[i].imag, A[i].real)
        d = (ph - math.pi/4 + math.pi) % (2*math.pi) - math.pi
        if m <= 13: rat.append(abs(A[i])/a_pred[i]); phs.append(d)
        P(f"  {int(m):>4}{lms[i]:>9.4f}{om[i]:>10.4f}{sep[i]/bin_:>9.2f}{a_pred[i]:>11.4f}"
          f"{abs(A[i]):>10.4f}{abs(A[i])/a_pred[i]:>10.3f}{ph:>9.3f}{d:>+10.3f}"
          f"{abs(A[i])/fl:>11.1f}")
    rat, phs = np.array(rat), np.array(phs)
    P(f"\n  first 9 prime powers:  obs/pred median {np.median(rat):.3f}  mean {rat.mean():.3f}"
      f"  IQR [{np.percentile(rat,25):.3f},{np.percentile(rat,75):.3f}]  "
      f"range [{rat.min():.3f},{rat.max():.3f}]")
    P(f"                         arg - pi/4: median {np.median(phs):+.4f} rad  "
      f"max|.| {np.abs(phs).max():.4f} rad")

    # ---- C3 block shuffle
    P(f"\n  C3 BLOCK SHUFFLE (blocks of 200 zeros, 24 draws):")
    dl = gam - tld
    res, resph = [], []
    for it in range(24):
        idx = np.arange(K); nb = K//200
        blocks = np.array_split(idx[:nb*200], nb)
        order = rng.permutation(nb)
        newidx = np.concatenate([blocks[j] for j in order] + [idx[nb*200:]])
        gsh = tld + dl[newidx]
        Dsh = delta_series(gsh, tld, ST, NBIG)
        gsh_t = detrend_poly(v, Dsh[NLO-1:NBIG]/ns**0.25, deg=3)
        Ash = np.abs(spectrum(ns, gsh_t, om))
        res.append([Ash[i]/a_pred[i] for i in range(len(ms)) if ms[i] <= 13])
    res = np.array(res)
    P(f"    obs/pred at the 9 lines: median {np.median(res):.3f}   90th pct "
      f"{np.percentile(res,90):.3f}   99th pct {np.percentile(res,99):.3f}   "
      f"max {res.max():.3f}")
    P(f"    TRUE zeros, same 9 lines: median {np.median(rat):.3f}   min {rat.min():.3f}")
    P(f"    every true line above the shuffle 99th pct? "
      f"{bool((rat > np.percentile(res,99)).all())}")

    # ---- dense scan: are the peaks AT omega_m?
    P(f"\n  DENSE SCAN: local maxima of |A(omega)| on [1.5,3.3], step {bin_/8:.4f}")
    grid = np.arange(1.5, 3.30, bin_/8)
    Ag = np.abs(spectrum(ns, gt, grid))
    loc = [i for i in range(1, len(grid)-1) if Ag[i] > Ag[i-1] and Ag[i] > Ag[i+1]
           and Ag[i] > 3*fl]
    P(f"  {'peak omega':>12}{'|A|':>9}   nearest 2 sqrt(log m):   m,  offset (bins)")
    for i in loc:
        j = int(np.argmin(np.abs(omall - grid[i])))
        P(f"  {grid[i]:>12.4f}{Ag[i]:>9.4f}      {omall[j]:>10.4f}   "
          f"m={int(msall[j]):>4}   {(grid[i]-omall[j])/bin_:+.2f}")
    P(f"\n[{time.time()-t0:.0f}s] done")
