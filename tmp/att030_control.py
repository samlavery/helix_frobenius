"""ATTEMPT 030, stage 5 -- GROUND-TRUTH control with an exactly known gamma_1, plus the
noise audit that stage 4's part B needs.

Stage 4 measured the turn-on exponent p = +0.98 (r = 0.999) in gamma_1 over four L-functions
and found n_half = 8.0, 8.5, 8.1, 8.2 times gamma_1 -- a 6% collapse -- against a 2.95x failure
for gamma_1^2.  It also found that the ONE lowest zero, with no fitted parameter, explains
lambda_n^arith below the threshold at R^2 = 0.78-0.98 where the M=32 prime model gives -65.7.

Two things are still missing and both can be supplied exactly.

 (1) NOISE AUDIT for part B.  Is "the lowest zero explains it" discriminating, or would ANY
     slow cosine score 0.97?  Control: replace gamma_1 by c*gamma_1 for c away from 1, and by
     random ordinates in the same range.  The control must fail by MISSING STRUCTURE (wrong
     frequency), which it does by construction -- it cannot fail by extra cancellation.

 (2) OUT-OF-SAMPLE TEST with an exactly known gamma_1.  lambda_n^arith is EXACTLY
     sum_gamma [2 - 2 cos(2 n arctan(1/(2 gamma)))] - lambda_n^arch, so deleting the first K
     zeros produces an object whose lowest ordinate is gamma_{K+1}, known to 10 digits.
        LINEAR law     predicts  n_half = 8.2 * gamma_{K+1}
        RESONANCE law  predicts  n_half = gamma_{K+1}^2 log 2
     For zeta these are  114 / 170 / 203 / 246 / 304 / 389  against  138 / 306 / 434 / 642 /
     979 / 1598  at K = 0,1,2,3,5,8 -- a factor 4 apart by K=8.  PRE-REGISTERED BEFORE THE RUN.

STATED NULL
  N9   the wrong-gamma control also scores R^2 >= 0.5 at [20,40], i.e. part B was vacuous.
  N10  the deletion test's n_half tracks gamma_{K+1}^2 log 2 rather than 8.2 gamma_{K+1}.
"""
import sys, os, math, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from att030_zeta import score, detrend, line_prediction_zeta
from att030_scaling import zero_model, amp_curve, n_half
def P(*a): print(*a); sys.stdout.flush()

if __name__ == "__main__":
    t0 = time.time(); P(__doc__); P("="*104)
    NMAX = 2500
    Y = np.load(os.path.join(HERE, 'att030_Yzeta_r997.npy'))[:NMAX]
    G = np.load(os.path.join(HERE, 'att019_zeros_to20k.npy'))
    O32 = line_prediction_zeta(NMAX, 32)

    P("(1) NOISE AUDIT: single-cosine model at gamma = c * gamma_1, zeta, R^2 vs window")
    P(f"  {'c':>7}{'gamma':>10}" + "".join(f"{'[%d,%d]'%w:>12}"
                                           for w in ((20,40),(40,80),(80,160),(160,320))))
    for c in (0.50, 0.70, 0.85, 0.95, 1.00, 1.05, 1.20, 1.50, 2.00, 3.00):
        g = c*G[0]; ZM = zero_model([g], NMAX); row = f"  {c:>7.2f}{g:>10.4f}"
        for lo, hi in ((20,40),(40,80),(80,160),(160,320)):
            nv = np.arange(lo, hi+1, dtype=float)
            R2, *_ = score(nv, Y[lo-1:hi], ZM[lo-1:hi]); row += f"{R2:>12.4f}"
        P(row)
    rng = np.random.default_rng(305)
    for lo, hi in ((20,40),(80,160)):
        nv = np.arange(lo, hi+1, dtype=float)
        vals = []
        for _ in range(400):
            g = rng.uniform(5.0, 60.0); ZM = zero_model([g], NMAX)
            vals.append(score(nv, Y[lo-1:hi], ZM[lo-1:hi])[0])
        vals = np.array(vals)
        true = score(nv, Y[lo-1:hi], zero_model([G[0]], NMAX)[lo-1:hi])[0]
        P(f"  random gamma in [5,60], 400 draws, window [{lo},{hi}]: median {np.median(vals):+.4f}"
          f"  90th {np.percentile(vals,90):+.4f}  99th {np.percentile(vals,99):+.4f}"
          f"  max {vals.max():+.4f}   |  TRUE gamma_1 {true:+.4f}")

    P("\n(2) OUT-OF-SAMPLE: delete the first K zeta zeros; lowest ordinate becomes gamma_{K+1}")
    P(f"  {'K':>3}{'gamma_K+1':>11}{'pred 8.2*g':>12}{'pred g^2 log2':>15}"
      f"{'n_h(f=.3)':>11}{'n_h(f=.5)':>11}{'n_h/g':>9}{'n_h/g^2':>10}")
    rows = []
    for K in (0, 1, 2, 3, 5, 8, 12):
        Yk = Y - zero_model(G[:K], NMAX) if K else Y.copy()
        g = G[K]
        ns, As = amp_curve(Yk, NMAX, 2.0)
        nh3 = n_half(ns, As, 0.3)[0]; nh5 = n_half(ns, As, 0.5)[0]
        rows.append((K, g, nh3, nh5))
        P(f"  {K:>3}{g:>11.4f}{8.2*g:>12.1f}{g*g*math.log(2):>15.1f}"
          f"{nh3:>11.0f}{nh5:>11.0f}{nh3/g:>9.2f}{nh3/(g*g):>10.4f}")
    x = np.log([r[1] for r in rows]); y = np.log([r[2] for r in rows])
    p_, c_ = np.polyfit(x, y, 1)
    P(f"\n  log-log exponent over the deletion family: p = {p_:+.3f}  "
      f"r = {np.corrcoef(x,y)[0,1]:+.4f}   (LINEAR law p=1, RESONANCE law p=2)")
    v1 = [r[2]/r[1] for r in rows]; v2 = [r[2]/r[1]**2 for r in rows]
    P(f"  spread of n_half/gamma   = {max(v1)/min(v1):.2f}x     "
      f"spread of n_half/gamma^2 = {max(v2)/min(v2):.2f}x")

    P("\n(3) and the same deletion family scored against the PRIME model M=32 "
      "(does deleting zeros move the prime crossing?)")
    P(f"  {'K':>3}{'gamma_K+1':>11}" + "".join(f"{'[%d,%d]'%w:>12}"
      for w in ((40,80),(80,160),(160,320),(320,640))))
    for K in (0, 1, 2, 3, 5, 8, 12):
        Yk = Y - zero_model(G[:K], NMAX) if K else Y.copy()
        row = f"  {K:>3}{G[K]:>11.4f}"
        for lo, hi in ((40,80),(80,160),(160,320),(320,640)):
            nv = np.arange(lo, hi+1, dtype=float)
            R2, *_ = score(nv, Yk[lo-1:hi], O32[lo-1:hi]); row += f"{R2:>12.4f}"
        P(row)
    P(f"\n[{time.time()-t0:.0f}s] stage 5 done")
