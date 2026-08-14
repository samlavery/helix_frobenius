"""ATTEMPT 028 -- STAGE 5.  Locate F's off-line zeros and run the BETA-WEIGHTED Landau sum.

Stage 4 (argument principle, gated by max phase step 0.124 rad and stable under nv doubling):
   F     253 zeros in sigma in [-1,2], t in [10,200];  205 on the line  ->  48 OFF-LINE
   L(f)  254 zeros;  254 on the line  ->  0 off-line     (positive control, clean)

Landau's theorem is about  sum_rho x^rho = x^beta x^{i gamma}, NOT about ordinates.  So:
   a_pred(n) = -Lambda_1(n)/sqrt(n) = (2pi/W) n^{-1/2} sum_{ALL rho} n^{rho}
             = (2pi/W)[ sum_{on-line} n^{i gamma} + sum_{off-line} n^{beta-1/2} n^{i gamma} ].

NULL (pre-registered): adding the off-line zeros with their true beta does NOT restore the
non-prime-power lines -- |obs/pred - 1| stays > 0.5 at n = 6, 12, 18 -- so the ordinate-only
residual measured in stage 3 is not the off-line zeros.
CONTROL: the identical machinery on L(f) must find ZERO off-line zeros and therefore return the
ordinate-only answer unchanged.
"""
import numpy as np, math, sys, time
from math import pi, log, sqrt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_offline import GEngine
from att028_engine import coefficients, vonmangoldt_like, theta_Q

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 200.0
W = T1 - T0
a1, aC, dK, bf = coefficients(6000)
LAMF = vonmangoldt_like(a1, 64)
LAMf = vonmangoldt_like(bf, 64)

engF = GEngine(a1, 0.5, delta=0.012)
engf = GEngine(bf, 0.0, delta=0.012)


def newton(eng, sg, t, iters=60):
    s = complex(sg, t)
    for _ in range(iters):
        sigma, tt = s.real, s.imag
        if not (-1.0 < sigma < 2.0 and 5.0 < tt < 205.0): return None
        e = 1e-5
        f0 = eng.Fval(sigma, tt)
        d = -1j*(eng.Fval(sigma, tt+e) - eng.Fval(sigma, tt-e))/(2*e)
        if abs(d) < 1e-14: return None
        step = f0/d
        if abs(step) > 0.6: step *= 0.6/abs(step)
        s = s - step
        if abs(step) < 1e-13: break
    sigma, tt = s.real, s.imag
    if not (-1.0 < sigma < 2.0 and T0 < tt < T1): return None
    if abs(eng.Fval(sigma, tt)) > 1e-9: return None
    return s


def find_offline(eng, name):
    t0 = time.time()
    roots = []
    for sg in (0.56, 0.65, 0.78, 0.92, 1.06, 1.20, 1.38, 1.60):
        for t in np.arange(T0+0.05, T1, 0.12):
            r = newton(eng, sg, float(t))
            if r is None: continue
            if r.real <= 0.5 + 1e-6: continue
            if not any(abs(r-q) < 1e-7 for q in roots): roots.append(r)
    roots.sort(key=lambda z: z.imag)
    P(f"  {name}: {len(roots)} distinct zeros with Re s > 1/2 found  [{time.time()-t0:.0f}s]")
    return roots


P("locating off-line zeros by 2D Newton (zeros come in pairs beta, 1-beta at the same gamma):")
offF = find_offline(engF, 'F')
offf = find_offline(engf, 'L(f)')
P(f"  F: implies {2*len(offF)} off-line zeros, argument principle said 253-205 = 48 -> "
  f"{'MATCH' if 2*len(offF) == 48 else 'MISMATCH'}")
P(f"  L(f): implies {2*len(offf)} off-line zeros, argument principle said 254-254 = 0 -> "
  f"{'MATCH' if 2*len(offf) == 0 else 'MISMATCH'}")
P("\n  F's off-line zeros (upper half plane, Re > 1/2; each pairs with 1-beta at the same gamma):")
for r in offF:
    P(f"     beta = {r.real:.8f}   gamma = {r.imag:.8f}   beta-1/2 = {r.real-0.5:+.6f}")
np.save('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F.npy',
        np.array([[r.real, r.imag] for r in offF]))

zF = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
zf = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_Lf.npy')
onF = zF[(zF > T0) & (zF < T1)]
onf = zf[(zf > T0) & (zf < T1)]
P(f"\n  totals in the box:  F  on-line {len(onF)} + off-line {2*len(offF)} = "
  f"{len(onF)+2*len(offF)}  (arg principle 253)")

NS = [2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 18, 23, 25, 27, 32, 49]
NOISE = [10, 14, 15, 20, 21, 22, 26, 28, 30, 33, 34, 35, 38, 39, 40, 42, 44, 45, 50]


def report(name, ong, off, LAM):
    P(f"\n{'='*100}\n{name}   on-line {len(ong)}, off-line pairs {len(off)}, W={W:.0f}")
    P(f"  {'n':>4}{'Lam(n)':>10}{'a_pred':>10}{'ordinate-only':>15}{'obs/pred':>10}"
      f"{'BETA-WEIGHTED':>15}{'obs/pred':>10}")
    r1, r2 = [], []
    for n in NS:
        ln = log(n)
        on = np.exp(1j*ong*ln).sum()
        ao = complex(on/(W/(2*pi)))
        ex = sum(n**(r.real-0.5)*np.exp(1j*r.imag*ln)
                 + n**(0.5-r.real)*np.exp(1j*r.imag*ln) for r in off)
        ab = complex((on+ex)/(W/(2*pi)))
        pred = -LAM[n]/sqrt(n)
        if abs(pred) > 1e-9:
            q1, q2 = ao.real/pred, ab.real/pred
            r1.append(q1); r2.append(q2)
            P(f"  {n:>4}{LAM[n]:>10.5f}{pred:>10.5f}{ao.real:>15.5f}{q1:>10.4f}"
              f"{ab.real:>15.5f}{q2:>10.4f}")
        else:
            P(f"  {n:>4}{LAM[n]:>10.5f}{pred:>10.5f}{ao.real:>15.5f}{'--':>10}"
              f"{ab.real:>15.5f}{'--':>10}")
    P(f"  -> median obs/pred:  ordinate-only {np.median(r1):.4f}   "
      f"BETA-WEIGHTED {np.median(r2):.4f}")
    nf1, nf2 = [], []
    for n in NOISE:
        ln = log(n)
        on = np.exp(1j*ong*ln).sum()
        ex = sum(n**(r.real-0.5)*np.exp(1j*r.imag*ln) + n**(0.5-r.real)*np.exp(1j*r.imag*ln)
                 for r in off)
        nf1.append(abs(complex(on/(W/(2*pi))))); nf2.append(abs(complex((on+ex)/(W/(2*pi)))))
    P(f"  -> noise floor over {len(NOISE)} all-silent n: ordinate-only median {np.median(nf1):.4f}"
      f" max {max(nf1):.4f};  beta-weighted median {np.median(nf2):.4f} max {max(nf2):.4f}")
    return np.array(r1), np.array(r2)


rF1, rF2 = report('F = Epstein principal class (NOT an Euler product)', onF, offF, LAMF)
rf1, rf2 = report('L(f) wt-1 newform [Euler product] CONTROL', onf, offf, LAMf)

P("\n" + "="*100)
P("NULL EVALUATION (stage 5)")
idx = {n: i for i, n in enumerate([n for n in NS if abs(LAMF[n]) > 1e-9])}
for n in (6, 12, 18):
    P(f"  n={n:>3}: ordinate-only obs/pred {rF1[idx[n]]:+.4f}   beta-weighted obs/pred "
      f"{rF2[idx[n]]:+.4f}   -> |obs/pred - 1| = {abs(rF2[idx[n]]-1):.4f} "
      f"(null needs > 0.5)")
ok = all(abs(rF2[idx[n]]-1) < 0.5 for n in (6, 12, 18))
P(f"  -> stage-5 NULL {'REJECTED' if ok else 'HOLDS'}")
P(f"  CONTROL L(f): off-line pairs found = {len(offf)} (must be 0); beta-weighted median "
  f"{np.median(rf2):.4f} vs ordinate-only {np.median(rf1):.4f} (must be identical)")
