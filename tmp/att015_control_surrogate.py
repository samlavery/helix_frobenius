"""ATTEMPT 015, stage 5 -- the zero-side control that fails by MISSING STRUCTURE.

Replace the TRUE zeros by the RIGID surrogate  gamma~_k = theta^{-1}(pi (k-1)),  i.e. the zero
set for which S(t) == 0 identically.  Everything else in the pipeline is byte-identical.
The surrogate has the same smooth density, the same count, the same range -- it differs from
the true set ONLY by the arithmetic fluctuation, which is exactly the structure under test.

PRE-REGISTERED: the surrogate must show NO line at any omega_m = 2 sqrt(log m); every
|A(omega_m)| must fall into the noise floor.  If a line survives the surrogate, the "lines"
measured in stage 4 are an artifact of the density/window and the attempt is void.

Also reported: predicted-vs-measured oscillating part sampled inside the resonant band, and
the obs/pred summary over the first nine prime powers.
"""
import sys, os, math, json, time
import numpy as np
from mpmath import mp, mpf

def P(*a):
    print(*a); sys.stdout.flush()

HERE = os.path.dirname(os.path.abspath(__file__))
NBIG = 8000
src = open(os.path.join(HERE, 'att015_lines.py')).read().split(
    '# ================================================================== main')[0]
_g = {'__file__': os.path.join(HERE, 'att015_lines.py')}; exec(src, _g)
lambda_arch = _g['lambda_arch']; lambda_from_zeros = _g['lambda_from_zeros']
prime_powers = _g['prime_powers']; line_prediction = _g['line_prediction']; score = _g['score']
# (identical to att015_lispectrum.py -- copied rather than exec'd, that file contains the
#  split marker inside a string literal)
def spectrum(ns, gt, omegas):
    v = np.sqrt(ns); V = v[-1]-v[0]
    w = 1.0/(2*np.sqrt(ns))
    E = np.exp(-1j*np.outer(np.asarray(omegas, float), v))
    return (2.0/V)*(E*(gt*w)).sum(axis=1)

def detrend_poly(v, y, deg=3):
    X = np.vander(v - v.mean(), deg+1)
    c, *_ = np.linalg.lstsq(X, y, rcond=None)
    return y - X @ c

def theta_f(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def theta_p(t):
    return 0.5*np.log(t/(2*np.pi)) - 1/(48*t**2) - 21/(5760*t**4)

if __name__ == "__main__":
    P(__doc__); P("="*100)
    g_true = np.load(os.path.join(HERE, 'att015_zeros_to_30000.npy'))
    K = len(g_true)
    y = np.pi*np.arange(0, K, dtype=float)          # theta(gamma~_k) = pi (k-1)
    t = np.maximum(20.0, 2*np.pi*np.exp(1 + y/np.maximum(1.0, y)))   # crude start
    t = np.full(K, 30.0)
    for _ in range(200):                             # Newton on theta(t) = y
        t = np.clip(t - (theta_f(t)-y)/theta_p(t), 17.85, 1e6)
    P(f"  surrogate: {K} rigid zeros, gamma~_1={t[0]:.6f} (true {g_true[0]:.6f}), "
      f"gamma~_K={t[-1]:.4f} (true {g_true[-1]:.4f}),  max|theta(g~)/pi-(k-1)| = "
      f"{np.abs(theta_f(t)/np.pi - np.arange(K)).max():.2e}")

    arch = lambda_arch(NBIG, K=100_000)
    Ytrue = lambda_from_zeros(g_true, NBIG, 0.75761045) - arch
    Ysurr = lambda_from_zeros(t, NBIG, 0.0) - arch     # S == 0 for the surrogate, by definition

    for NLO, tag in ((200, 'TRUE zeros'), (200, 'SURROGATE (S==0)')):
        pass
    ms, lms = prime_powers(64)
    om = 2*np.sqrt(np.log(ms)); a_pred = lms/(math.sqrt(math.pi)*np.sqrt(ms)*np.log(ms)**0.75)
    msall, _ = prime_powers(4000); omall = 2*np.sqrt(np.log(msall))
    NLO = 200
    ns = np.arange(NLO, NBIG+1, dtype=float); v = np.sqrt(ns); V = v[-1]-v[0]
    bin_ = 2*math.pi/V
    rng = np.random.default_rng(7)
    P(f"\n  window n={NLO}..{NBIG},  Rayleigh bin {bin_:.4f} rad")
    P(f"  {'m':>4}{'a_m pred':>11}{'|A| TRUE':>11}{'obs/pred':>10}   {'|A| SURROGATE':>15}"
      f"{'surr/pred':>11}{'surr/floor90':>14}")
    rows = {}
    for name, Yx in (('true', Ytrue), ('surr', Ysurr)):
        gt = detrend_poly(v, Yx[NLO-1:NBIG]/ns**0.25, deg=3)
        rows[name] = (np.abs(spectrum(ns, gt, om)),
                      np.abs(spectrum(ns, gt, rng.uniform(0.40, 1.60, 3000))))
    fl_s = np.percentile(rows['surr'][1], 90)
    ratT, ratS = [], []
    for i, m in enumerate(ms):
        if m > 13: continue
        rt = rows['true'][0][i]/a_pred[i]; rs = rows['surr'][0][i]/a_pred[i]
        ratT.append(rt); ratS.append(rs)
        P(f"  {int(m):>4}{a_pred[i]:>11.4f}{rows['true'][0][i]:>11.4f}{rt:>10.3f}   "
          f"{rows['surr'][0][i]:>15.4f}{rs:>11.3f}{rows['surr'][0][i]/fl_s:>14.2f}")
    P(f"\n  TRUE      obs/pred over the first {len(ratT)} prime powers: median "
      f"{np.median(ratT):.3f}  mean {np.mean(ratT):.3f}  IQR "
      f"[{np.percentile(ratT,25):.3f},{np.percentile(ratT,75):.3f}]")
    P(f"  SURROGATE obs/pred over the same lines:                median "
      f"{np.median(ratS):.3f}  mean {np.mean(ratS):.3f}  max {max(ratS):.3f}")
    P(f"  surrogate noise floor (line-free band): median {np.median(rows['surr'][1]):.4f}  "
      f"90th {fl_s:.4f}  99th {np.percentile(rows['surr'][1],99):.4f}")
    P(f"  every surrogate line inside its own 90th-pct floor? "
      f"{all(rows['surr'][0][i] < fl_s for i in range(len(ms)) if ms[i] <= 13)}")
    P(f"  ratio of TRUE to SURROGATE spectral power at the lines: "
      f"{np.median(np.array(ratT)/np.maximum(np.array(ratS),1e-12)):.1f}x")

    # predicted vs measured, sampled inside the resonant band
    P("\n" + "="*100)
    P("PREDICTED vs MEASURED oscillating part (M=32, ZERO free parameters), sampled.")
    ms32, lm32 = prime_powers(32)
    O32 = line_prediction(NBIG, np.log(ms32), lm32/ms32, math.log(32))
    for lo, hi in ((1, 40), (200, 3000), (200, 8000), (3000, 8000)):
        nsw = np.arange(lo, hi+1, dtype=float)
        R2, r, Yd, Od = score(nsw, Ytrue[lo-1:hi], O32[lo-1:hi])
        P(f"  n=[{lo:>5},{hi:>5}]  R2={R2:>8.4f}  r={r:>7.4f}  rms(Y)={Yd.std():>7.4f}  "
          f"rms(O)={Od.std():>7.4f}  rms(Y-O)={np.std(Yd-Od):>7.4f}")
    P("\n  sample of the resonant band, n = 1000..1020:")
    P(f"  {'n':>6}{'Y_n = lam^arith':>18}{'O_n(M=32)':>14}{'Y-detr':>10}{'O-detr':>10}")
    nsw = np.arange(1000, 1101, dtype=float)
    _, _, Yd, Od = score(nsw, Ytrue[999:1100], O32[999:1100])
    for i in range(0, 21):
        P(f"  {1000+i:>6}{Ytrue[999+i]:>18.6f}{O32[999+i]:>14.6f}{Yd[i]:>10.4f}{Od[i]:>10.4f}")
