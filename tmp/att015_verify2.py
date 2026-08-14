"""ADVERSARIAL VERIFICATION part 2 of attempt 015.

(1) push MY contour lambda_n^arith to n = 8000 so the spectral window matches theirs exactly
(2) test whether "the pre-registered threshold fires" (R2 sign flip at n ~ 138, the n^{1/4} law
    'switching on') is an artifact of (a) fixing M = 32 and (b) a 4-parameter detrend applied to
    a window that contains less than one oscillation cycle.
    CONTROL MODEL: A_n = n^{1/4} sum_{m<=32} a_m cos(2 sqrt(n log m) + pi/4)  -- the n^{1/4} law
    is TRUE AT EVERY n by construction.  If the same per-window detrend makes A_n's amplitude
    "switch on" at the same place, the switch-on measures the window, not the zeros.
(3) per-line noise-floor comparison (their claim: "lines sit at 0.36-0.38, 4-9x above all floors")
"""
import sys, os, math, json, time
import numpy as np
from mpmath import mp, mpf, mpc
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att015_verify import (taylor_coeffs, h_arith, lambda_arch_closed, prime_powers,
                           line_prediction, detrend, score)
def P(*a):
    print(*a); sys.stdout.flush()

t0 = time.time()
NB = 8000
cache = os.path.join(HERE, 'att015_verify_Y8000.npy')
if os.path.exists(cache):
    Y = np.load(cache)
else:
    P("computing lambda_n^arith to n=8000 by mpmath-FFT Cauchy at |z|=0.99, dps=70 ...")
    cz = taylor_coeffs(h_arith, '0.99', 8192, 70)
    Y = np.array([float(cz[n-1].real) for n in range(1, NB+1)])
    P(f"  max |Im c| n<=8000 = {mp.nstr(max(abs(cz[n-1].imag) for n in range(1,NB+1)),3)}"
      f"   [{time.time()-t0:.0f}s]")
    np.save(cache, Y)
P(f"[{time.time()-t0:.0f}s] Y ready.  rms(Y) over 200..8000 = {Y[199:].std():.4f}   "
  f"max|Y| = {np.abs(Y).max():.4f} at n={int(np.argmax(np.abs(Y)))+1}")

# cross-check against my n<=3000 run and against THEIR zero-census Y
npz = np.load(os.path.join(HERE, 'att015_lines_out.npz'))
P(f"  vs THEIR zero-census Y (n<=3000): max|diff| = {np.abs(npz['Y']-Y[:3000]).max():.3e}")

# ---------------------------------------------------------------- (2) switch-on artifact
P("\n" + "="*100)
P("(2)  IS THE 'THRESHOLD' REAL?   per-window rms(detrended)/n^{1/4}")
ms32, lm32 = prime_powers(32)
a_m = lm32/(math.sqrt(math.pi)*np.sqrt(ms32)*np.log(ms32)**0.75)
nn = np.arange(1, NB+1, dtype=float)
Asym = nn**0.25 * (np.cos(2*np.sqrt(np.outer(nn, np.log(ms32))) + math.pi/4) @ a_m)
O32 = line_prediction(NB, ms32, lm32, 32)
msB, lmB = prime_powers(1000000)
OB = line_prediction(NB, msB, lmB, 1000000)

P(f"  {'window':>16}{'R2 M=32':>11}{'R2 M=1e6':>11}{'ampY':>10}{'ampAsym':>10}{'ratio':>8}"
  f"{'cycles(m=2)':>13}")
for lo, hi in ((10,20),(20,40),(40,80),(80,160),(160,320),(320,640),(640,1280),(1280,2560),
               (2560,5120),(5120,8000)):
    ns = np.arange(lo, hi+1, dtype=float)
    R2a, _, Yd, _ = score(ns, Y[lo-1:hi], O32[lo-1:hi])
    R2b, _, _, _ = score(ns, Y[lo-1:hi], OB[lo-1:hi])
    Ad = detrend(ns, Asym[lo-1:hi])
    c = 0.5**0.25
    nc = (2*math.sqrt(hi*math.log(2)) - 2*math.sqrt(lo*math.log(2)))/(2*math.pi)
    ampY = Yd.std()/(0.5*(lo+hi))**0.25
    ampA = Ad.std()/(0.5*(lo+hi))**0.25
    P(f"  [{lo:>5},{hi:>5}]{R2a:>11.4f}{R2b:>11.4f}{ampY:>10.4f}{ampA:>10.4f}"
      f"{(ampY/ampA if ampA>0 else float('nan')):>8.2f}{nc:>13.2f}")
P("  ampAsym = the SAME statistic on a model whose n^{1/4} law holds identically at every n.")

# ---------------------------------------------------------------- (2b) small n, larger M
P("\n" + "="*100)
P("(2b) the PRIMARY window n=1..40 with M swept -- with controls at each M")
rng = np.random.default_rng(3)
ns40 = np.arange(1, 41, dtype=float)
P(f"  {'M':>9}{'#lines':>8}{'R2 true':>10}{'r true':>9}   {'ctrl randfreq R2 med/99th':>28}")
for M in (32, 100, 1000, 10000, 100000, 1000000):
    msM, lmM = prime_powers(M)
    OM = line_prediction(40, msM, lmM, M)
    R2t, rt, _, _ = score(ns40, Y[:40], OM)
    R2s = []
    for _ in range(60):
        xs = np.exp(rng.uniform(math.log(2), math.log(M), size=len(msM)))
        Oc = line_prediction(40, xs, lmM, M)
        a, b, _, _ = score(ns40, Y[:40], Oc)
        R2s.append(a)
    R2s = np.array(R2s)
    P(f"  {M:>9}{len(msM):>8}{R2t:>10.4f}{rt:>9.4f}   "
      f"{np.median(R2s):>12.4f} {np.percentile(R2s,99):>12.4f}")

# ---------------------------------------------------------------- (3) spectral, THEIR windows
P("\n" + "="*100)
P("(3) spectral law on THEIR windows (n_lo..8000)")
def spectrum(nsv, gt, omegas):
    v = np.sqrt(nsv); V = v[-1]-v[0]
    w = 1.0/(2*np.sqrt(nsv))
    E = np.exp(-1j*np.outer(np.asarray(omegas, float), v))
    return (2.0/V)*(E*(gt*w)).sum(axis=1)
def detrend_poly(v, y, deg=3):
    X = np.vander(v - v.mean(), deg+1)
    c, *_ = np.linalg.lstsq(X, y, rcond=None)
    return y - X @ c
mlist = [2,3,4,5,7,8,9,11,13]
Lam = {2:math.log(2),4:math.log(2),8:math.log(2),3:math.log(3),9:math.log(3),
       5:math.log(5),7:math.log(7),11:math.log(11),13:math.log(13)}
allpp = [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32]
theirs = {200:[1.041,1.064,0.808,1.006,1.040,1.311,0.772,0.859,0.892]}
for lo in (200, 500, 1000):
    nsv = np.arange(lo, NB+1, dtype=float)
    g = Y[lo-1:NB]/nsv**0.25
    gt = detrend_poly(np.sqrt(nsv), g, 3)
    V = math.sqrt(NB)-math.sqrt(lo); ray = 2*math.pi/V
    oms = [2*math.sqrt(math.log(m)) for m in mlist]
    A = spectrum(nsv, gt, oms)
    ratios, phases, absA, preds = [], [], [], []
    for i, m in enumerate(mlist):
        am = Lam[m]/(math.sqrt(math.pi)*math.sqrt(m)*math.log(m)**0.75)
        ratios.append(abs(A[i])/am); phases.append(
            (np.angle(A[i])-math.pi/4+math.pi) % (2*math.pi) - math.pi)
        absA.append(abs(A[i])); preds.append(am)
    ratios = np.array(ratios); phases = np.array(phases); absA = np.array(absA)
    P(f"\n  n = {lo}..8000   Rayleigh = {ray:.4f}")
    P("    m   |A|      a_m     obs/pred   arg-pi/4   sep/Rayleigh")
    for i, m in enumerate(mlist):
        sep = min(abs(oms[i]-2*math.sqrt(math.log(q))) for q in allpp if q != m)/ray
        P(f"   {m:>3} {absA[i]:8.4f} {preds[i]:8.4f} {ratios[i]:9.3f} {phases[i]:+9.3f} {sep:12.2f}")
    P(f"    MY median obs/pred = {np.median(ratios):.3f}   "
      f"median |arg-pi/4| = {np.median(np.abs(phases)):.3f}   max |arg-pi/4| = "
      f"{np.abs(phases).max():.3f}")
    if lo in theirs:
        P(f"    THEIR per-line: {theirs[lo]}  (median 1.006)")
    rng2 = np.random.default_rng(11)
    band = rng2.uniform(1.70, 4.20, 6000)
    keep = np.array([min(abs(w-2*math.sqrt(math.log(q))) for q in allpp) > 1.5*ray for w in band])
    Ab = np.abs(spectrum(nsv, gt, band[keep]))
    lf = np.abs(spectrum(nsv, gt, np.linspace(0.40, 1.60, 400)))
    A6 = abs(spectrum(nsv, gt, [2*math.sqrt(math.log(6))])[0])
    P(f"    floors: line-free med {np.median(lf):.4f} 99th {np.percentile(lf,99):.4f} | "
      f"random({keep.sum()}) med {np.median(Ab):.4f} 99th {np.percentile(Ab,99):.4f} | "
      f"m=6 {A6:.4f}")
    P(f"    lines above the RANDOM 99th pct ({np.percentile(Ab,99):.4f}): "
      f"{[m for i,m in enumerate(mlist) if absA[i] > np.percentile(Ab,99)]}")
    P(f"    ratio (weakest line)/(random 99th) = {absA.min()/np.percentile(Ab,99):.2f}, "
      f"(m=2)/(random 99th) = {absA[0]/np.percentile(Ab,99):.2f}")
P(f"\n[{time.time()-t0:.0f}s] done")
