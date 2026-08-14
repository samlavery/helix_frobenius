"""ATTEMPT 015, stage 4 -- the tape-line law transported into Li space, with NO free parameter.

From stage 2 the arithmetic Li coefficient is exactly
    Y_n := lambda_n^arith = -[ sum_m Lambda(m) L_{n-1}^{(1)}(log m)/m - (1 - L_n(log M)) ]_{M->inf}
and Szego 8.22.1 turns each prime-power line into a pure tone IN THE VARIABLE  v = sqrt(n):

    Y_n / n^{1/4}  =  DC(n)  +  sum_m  a_m cos( omega_m v + pi/4 ),
        omega_m = 2 sqrt(log m)          [POSITION, no free parameter]
        a_m     = Lambda(m) / ( sqrt(pi) sqrt(m) (log m)^{3/4} )   [AMPLITUDE, no free parameter]

This is the exact Li-space counterpart of the attempt-010 tape law K(tau_n)=U Lambda(n)^2/(L^2 n):
same lines, same Lambda(m)/sqrt m weights, different transform.  Measured statistic (a Riemann
sum for the v-Fourier integral over the window, dv_n = 1/(2 sqrt n)):

    A(omega) = (2/V) * sum_n gtilde_n exp(-i omega sqrt n) / (2 sqrt n),   V = v_max - v_min

so that  |A(omega_m)| = a_m  and  arg A(omega_m) = +pi/4  if the law holds.
gtilde = Y_n/n^{1/4} minus a degree-3 polynomial in v (the lines sit at >10 cycles per window,
so the detrend cannot reach them).

CAMPAIGN RULE (attempt 010): evaluate AT the predicted omega.  Never take a max over a band.

PRE-REGISTERED NULLS (fixed before running):
  N1  |A(omega_m)|/a_m is not ~1 (median outside [0.5, 2.0]) for the resolved lines m=2,3,4,5.
  N2  arg A(omega_m) is not near +pi/4 (median |arg - pi/4| > pi/4).
  N3  the value at the predicted omega_m is inside the noise floor (below its 90th percentile).
CONTROLS (fail by MISSING STRUCTURE):
  C1  omega = 2 sqrt(log m) for m NOT a prime power (Lambda(m)=0): predicted amplitude is
      EXACTLY ZERO there, so those abscissas must sit in the floor.
  C2  2000 random omega in the same band.
NOISE AUDIT: window [n_lo, 8000] swept; zero-side truncation T swept; the whole Y_n vector
re-derived at three T and spot-checked at large n against an independent Cauchy contour.
"""
import sys, os, math, json, time
import numpy as np
from mpmath import mp, mpf, mpc

def P(*a):
    print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
NBIG = 8000
src = open(os.path.join(HERE, 'att015_lines.py')).read().split(
    '# ================================================================== main')[0]
_g = {'__file__': os.path.join(HERE, 'att015_lines.py')}
exec(src, _g)
lambda_arch      = _g['lambda_arch']
lambda_from_zeros= _g['lambda_from_zeros']
prime_powers     = _g['prime_powers']
line_prediction  = _g['line_prediction']
score            = _g['score']

# ---------------------------------------------------------------- independent large-n check
def lambda_by_contour(ns, r='0.99', N=8192, dps=60):
    """lambda_n = n [z^n] log xi(1/(1-z)) by Cauchy DFT on |z|=r.
       |z|<r maps to the s-disk |s - 1/(1-r^2)| < r/(1-r^2), tangent to Re s = 1/2 at s=1/2,
       with |Im s| < r/(1-r^2) = 49.75 for r=0.99.  All zeros with |Im s| < 49.78 are the first
       ten and lie ON the line (10 sign changes of Z + Riemann-von Mangoldt count), hence none
       is interior: the contour is legitimate without assuming anything."""
    mp.dps = dps
    r = mpf(r)
    vals = []
    for j in range(N):
        z = mpc(r)*mp.expjpi(mpf(2*j)/N)
        s = 1/(1-z)
        vals.append(-mp.log(2) - mp.log(1-z) + mp.log((s-1)*mp.zeta(s))
                    - s*mp.log(mp.pi)/2 + mp.loggamma(s/2))
    out = {}
    for n in ns:
        acc = mpc(0)
        for j in range(N):
            acc += vals[j]*mp.expjpi(mpf(-2*j*n)/N)
        out[n] = float(mpf(n)*(acc/N).real / r**n)
    return out

# ---------------------------------------------------------------- the v-spectrum
def spectrum(ns, gt, omegas):
    v = np.sqrt(ns); V = v[-1]-v[0]
    w = 1.0/(2*np.sqrt(ns))
    E = np.exp(-1j*np.outer(np.asarray(omegas, float), v))
    return (2.0/V)*(E*(gt*w)).sum(axis=1)

def detrend_poly(v, y, deg=3):
    X = np.vander(v - v.mean(), deg+1)
    c, *_ = np.linalg.lstsq(X, y, rcond=None)
    return y - X @ c

# ================================================================== main
if __name__ == "__main__":
    P(__doc__); P("="*100)
    t0 = time.time()

    arch = lambda_arch(NBIG, K=100_000)
    P(f"[{time.time()-t0:.0f}s] arch closed form to n={NBIG}")
    g_all = np.load(os.path.join(HERE, 'att015_zeros_to_30000.npy'))
    Yv = {}
    for Tcut in (20000.0, 30000.0):
        g = g_all[g_all < Tcut]
        mp.dps = 40; Tl = float(g[-1])
        th = mp.im(mp.loggamma(mpf(1)/4 + 1j*mpf(Tl)/2)) - mpf(Tl)/2*mp.log(mp.pi)
        ST = float(len(g) - 1 - th/mp.pi)
        Yv[Tcut] = lambda_from_zeros(g, NBIG, ST) - arch
        P(f"[{time.time()-t0:.0f}s] Y_n from zeros, T={Tcut:.0e}, {len(g)} zeros, S(T)={ST:+.5f}")
    Y = Yv[30000.0]
    P(f"  ZERO-SIDE TRUNCATION AUDIT: max |Y(T=2e4) - Y(T=3e4)| over n<=8000 = "
      f"{np.abs(Yv[20000.0]-Yv[30000.0]).max():.3e}   (rms Y over n=200..8000 = "
      f"{Y[199:].std():.4f})")

    ex = json.load(open(os.path.join(HERE, 'att015_lambda_exact.json')))
    mp.dps = 50
    arith40 = np.array([float(mpf(x)) for x in ex['lam_arith']])
    P(f"  vs exact Bombieri-Lagarias, n<=40: max |diff| = {np.abs(Y[:40]-arith40).max():.3e}")

    # independent contour check at large n
    P(f"\n[{time.time()-t0:.0f}s] INDEPENDENT LARGE-n CHECK: Cauchy contour |z|=0.99 vs zeros ...")
    spot = [500, 1000, 2000, 4000, 8000]
    con = lambda_by_contour(spot)
    P(f"  {'n':>6}{'lambda_n contour':>22}{'lambda_n zeros':>22}{'rel diff':>12}"
      f"{'|diff|/rms(Y)':>15}")
    for n in spot:
        lz = Y[n-1] + arch[n-1]
        P(f"  {n:>6}{con[n]:>22.10f}{lz:>22.10f}{abs(con[n]-lz)/abs(con[n]):>12.2e}"
          f"{abs(con[n]-lz)/Y[199:].std():>15.2e}")

    # ---------------------------------------------------------------- resonance onset
    P("\n" + "="*100)
    P("RESONANCE ONSET.  Line m is predicted to engage only once its stationary point")
    P("t0 = sqrt(n/log m) clears the first zero gamma_1 = 14.134, i.e. n > 199.8 log m")
    P("(n>138 for m=2, n>220 for m=3, n>693 for m=32).  Sliding dyadic windows, M=32, R2 with")
    P("ZERO free parameters, plus the amplitude of the oscillation itself.")
    ms32, lm32 = prime_powers(32)
    O32 = line_prediction(NBIG, np.log(ms32), lm32/ms32, math.log(32))
    P(f"  {'window':>16}{'t0(m=2)':>18}{'R2':>10}{'r':>9}{'rms Yd':>10}{'rms Yd / n^0.25':>18}")
    for n0 in (10, 20, 40, 80, 160, 320, 640, 1280, 2560):
        lo, hi = n0, min(2*n0, NBIG)
        ns = np.arange(lo, hi+1, dtype=float)
        R2, r, Yd, Od = score(ns, Y[lo-1:hi], O32[lo-1:hi])
        P(f"  [{lo:>5},{hi:>5}]  [{math.sqrt(lo/math.log(2)):>6.1f},"
          f"{math.sqrt(hi/math.log(2)):>6.1f}] {R2:>10.4f}{r:>9.4f}{Yd.std():>10.4f}"
          f"{Yd.std()/np.mean(ns)**0.25:>18.4f}")

    # ---------------------------------------------------------------- the spectrum
    P("\n" + "="*100)
    for NLO in (200, 500, 1000):
        ns = np.arange(NLO, NBIG+1, dtype=float)
        v = np.sqrt(ns)
        gt = detrend_poly(v, Y[NLO-1:NBIG]/ns**0.25, deg=3)
        V = v[-1]-v[0]
        P(f"\nWINDOW n = {NLO}..{NBIG}   v = [{v[0]:.3f},{v[-1]:.3f}]  V = {V:.2f}  "
          f"Rayleigh resolution 2pi/V = {2*math.pi/V:.4f} rad")
        ms, lms = prime_powers(64)
        om = 2*np.sqrt(np.log(ms))
        a_pred = lms/(math.sqrt(math.pi)*np.sqrt(ms)*np.log(ms)**0.75)
        A = spectrum(ns, gt, om)
        msall, _ = prime_powers(4000)                 # every line that can fall in the band
        omall = 2*np.sqrt(np.log(msall))
        bin_ = 2*math.pi/V
        # C2 floor: omega < 2 sqrt(log 2) = 1.6651 is line-free BY CONSTRUCTION (no prime
        # power below 2), so this band carries no arithmetic content at all.
        rng = np.random.default_rng(1234)
        Ar = np.abs(spectrum(ns, gt, rng.uniform(0.40, 1.60, 3000)))
        # C2b: random omega inside the band but >=1.5 Rayleigh bins from EVERY line
        omr = rng.uniform(1.70, 4.20, 20000)
        keep = np.min(np.abs(omr[:, None]-omall[None, :]), axis=1) > 1.5*bin_
        Ar2 = np.abs(spectrum(ns, gt, omr[keep]))
        # C1: composite (Lambda = 0) abscissas, kept only if >=1.5 bins from every real line
        comp = np.array([m for m in range(6, 41)
                         if m not in set(msall.astype(int))], dtype=float)
        omc = 2*np.sqrt(np.log(comp))
        sepc = np.min(np.abs(omc[:, None]-omall[None, :]), axis=1)
        kc = sepc > 1.0*bin_
        Ac = np.abs(spectrum(ns, gt, omc[kc]))
        P(f"  C2  FLOOR, line-free band omega in [0.40,1.60] (below the m=2 line, provably no "
          f"arithmetic content): median {np.median(Ar):.4f}  90th {np.percentile(Ar,90):.4f}  "
          f"99th {np.percentile(Ar,99):.4f}  max {Ar.max():.4f}")
        P(f"  C2b FLOOR, {keep.sum()} random omega in [1.70,4.20] >=1.5 bins from every prime-power "
          f"line: median {np.median(Ar2):.4f}  90th {np.percentile(Ar2,90):.4f}  "
          f"99th {np.percentile(Ar2,99):.4f}  max {Ar2.max():.4f}")
        P(f"  C1  CONTROL, omega = 2 sqrt(log m) for {kc.sum()} composite non-prime-powers "
          f"(Lambda(m)=0 => a_m EXACTLY 0, m={[int(x) for x in comp[kc]]}): "
          f"median {np.median(Ac):.4f}  90th {np.percentile(Ac,90):.4f}  max {Ac.max():.4f}")
        sep = np.array([min(abs(o-o2) for o2 in omall if abs(o2-o) > 1e-12) for o in om])
        P(f"\n  {'m':>4}{'Lam(m)':>9}{'omega_m':>10}{'sep/bin':>9}{'a_m pred':>11}"
          f"{'|A| obs':>10}{'obs/pred':>10}{'arg A':>10}{'arg-pi/4':>10}{'floor90':>9}")
        rat, phs = [], []
        for i, m in enumerate(ms):
            if m > 32: continue
            s = sep[i]/(2*math.pi/V)
            ph = math.atan2(A[i].imag, A[i].real)
            d = (ph - math.pi/4 + math.pi) % (2*math.pi) - math.pi
            tag = '  <- resolved' if s > 2 else ''
            if s > 2:
                rat.append(abs(A[i])/a_pred[i]); phs.append(d)
            P(f"  {int(m):>4}{lms[i]:>9.4f}{om[i]:>10.4f}{s:>9.2f}{a_pred[i]:>11.4f}"
              f"{abs(A[i]):>10.4f}{abs(A[i])/a_pred[i]:>10.3f}{ph:>10.3f}{d:>+10.3f}"
              f"{np.percentile(Ar2,90):>9.4f}{tag}")
        rat, phs = np.array(rat), np.array(phs)
        P(f"  RESOLVED LINES (sep > 2 Rayleigh bins), {len(rat)} of them:")
        P(f"    obs/pred   median {np.median(rat):.3f}   mean {rat.mean():.3f}   "
          f"range [{rat.min():.3f},{rat.max():.3f}]      [N1 null: median outside 0.5-2.0]")
        P(f"    arg-pi/4   median {np.median(phs):+.3f} rad  max|.| {np.abs(phs).max():.3f}"
          f"      [N2 null: median |.| > pi/4 = 0.785]")
        fl = max(np.percentile(Ar,90), np.percentile(Ar2,90), np.percentile(Ac,90))
        P(f"    all resolved lines above the 90th-pct of ALL THREE floors ({fl:.4f})? "
          f"{all(abs(A[i])>fl for i in range(len(ms)) if ms[i]<=32 and sep[i]/(2*math.pi/V)>2)}"
          f"      [N3 null: any inside the floor]")
    P(f"\n[{time.time()-t0:.0f}s] done")
