"""ATTEMPT 028 -- STAGE 7.  Same test, window [10,600] (W = 590) instead of [10,200].

Reason stated before running: the beta-weighted noise floor falls like 1/sqrt(W) while the line
heights are W-independent, so tripling the window should move the shuffle-control separation from
~5 sigma to ~9 sigma and shrink the Gonek error by 3x.  The prediction a_pred(n) = -Lam_1(n)/sqrt(n)
does not change -- there is no fitted parameter anywhere in this test.
"""
import numpy as np, math, sys, time
from math import pi, log, sqrt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_offline import GEngine, winding
from att028_engine import coefficients, vonmangoldt_like, theta_Q

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 600.0
W = T1 - T0
a1, aC, dK, bf = coefficients(6000)
LAMF = vonmangoldt_like(a1, 64)
eng = GEngine(a1, 0.5, delta=0.012)

exp_n = (theta_Q(np.array([T1]))[0] - theta_Q(np.array([T0]))[0])/pi
onF = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_F.npy')
onF = onF[(onF > T0) & (onF < T1)]
t0 = time.time()
N, jump = winding(eng, -1.0, 2.0, T0, T1, 24000, 800)
P(f"argument principle on [{T0},{T1}]: N = {N:.4f}  (theta count {exp_n:.2f}, max phase step "
  f"{jump:.3f} rad)   on-line {len(onF)}   =>  off-line {int(round(N))-len(onF)}  "
  f"({100*(int(round(N))-len(onF))/N:.2f}%)   [{time.time()-t0:.0f}s]")

def newton(s, iters=60):
    for _ in range(iters):
        sg, tt = s.real, s.imag
        if not (-1.0 < sg < 2.0 and 5.0 < tt < T1+5): return None
        e = 1e-5
        f0 = eng.Fval(sg, tt)
        d = -1j*(eng.Fval(sg, tt+e) - eng.Fval(sg, tt-e))/(2*e)
        if abs(d) < 1e-14: return None
        st = f0/d
        if abs(st) > 0.6: st *= 0.6/abs(st)
        s = s - st
        if abs(st) < 1e-13: break
    if not (-1.0 < s.real < 2.0 and T0 < s.imag < T1): return None
    if abs(eng.Fval(s.real, s.imag)) > 1e-9: return None
    return s

t0 = time.time()
roots = [complex(b, g) for b, g in
         np.load('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F.npy')]
for sg in (0.56, 0.65, 0.78, 0.92, 1.06, 1.20, 1.38, 1.60):
    for t in np.arange(200.0, T1, 0.12):
        r = newton(complex(sg, float(t)))
        if r is None or r.real <= 0.5 + 1e-6: continue
        if not any(abs(r-q) < 1e-7 for q in roots): roots.append(r)
roots.sort(key=lambda z: z.imag)
off = np.array([[r.real, r.imag] for r in roots])
P(f"off-line zeros with Re>1/2 located: {len(roots)}  => {2*len(roots)} off-line total"
  f"   [{time.time()-t0:.0f}s]")
P(f"  census closure: on-line {len(onF)} + off-line {2*len(roots)} = {len(onF)+2*len(roots)}"
  f"  vs argument principle {int(round(N))}   "
  f"[{'MATCH' if len(onF)+2*len(roots) == int(round(N)) else 'MISMATCH'}]")
P(f"  beta range {off[:,0].min():.4f} .. {off[:,0].max():.4f}   "
  f"mean beta-1/2 = {np.mean(off[:,0]-0.5):.4f}")
np.save('/Users/samuellavery/work/helix_frobenius/tmp/att028_offline_F600.npy', off)

NS = [2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 18, 23, 25, 27, 32, 49]
NOISE = [10, 14, 15, 20, 21, 22, 26, 28, 30, 33, 34, 35, 38, 39, 40, 42, 44, 45, 50]
def bw(gon, offs, n, weighted=True):
    ln = log(n)
    tot = np.exp(1j*gon*ln).sum()
    if weighted:
        tot += np.sum((n**(offs[:,0]-0.5) + n**(0.5-offs[:,0]))*np.exp(1j*offs[:,1]*ln))
    return complex(tot/(W/(2*pi)))

P(f"\n{'n':>4}{'Lam_1(n)':>10}{'a_pred':>10}{'ordinate-only':>15}{'o/p':>9}"
  f"{'BETA-WEIGHTED':>15}{'o/p':>9}")
r1, r2 = [], []
for n in NS:
    ao, ab = bw(onF, off, n, False), bw(onF, off, n, True)
    pred = -LAMF[n]/sqrt(n)
    if abs(pred) > 1e-9:
        q1, q2 = ao.real/pred, ab.real/pred; r1.append(q1); r2.append(q2)
        P(f"{n:>4}{LAMF[n]:>10.5f}{pred:>10.5f}{ao.real:>15.5f}{q1:>9.4f}{ab.real:>15.5f}{q2:>9.4f}")
    else:
        P(f"{n:>4}{LAMF[n]:>10.5f}{pred:>10.5f}{ao.real:>15.5f}{'--':>9}{ab.real:>15.5f}{'--':>9}")
r1, r2 = np.array(r1), np.array(r2)
P(f"-> median obs/pred: ordinate-only {np.median(r1):.4f}   BETA-WEIGHTED {np.median(r2):.4f}"
  f"   IQR {np.percentile(r2,25):.4f}-{np.percentile(r2,75):.4f}")
nf = [abs(bw(onF, off, n, True)) for n in NOISE]
nf0 = [abs(bw(onF, off, n, False)) for n in NOISE]
P(f"-> noise floor (19 all-silent n): beta-weighted median {np.median(nf):.4f} max {max(nf):.4f};"
  f"  ordinate-only median {np.median(nf0):.4f} max {max(nf0):.4f}")

P("\nSHUFFLE control (same betas, random on-line gammas):")
rng = np.random.default_rng(20260812)
for n in (6, 12, 18, 4, 8):
    pred = -LAMF[n]/sqrt(n)
    v = []
    for _ in range(400):
        gg = rng.choice(onF, size=len(off), replace=False)
        v.append(bw(onF, np.column_stack([off[:,0], gg]), n, True).real/pred)
    v = np.array(v); true = bw(onF, off, n, True).real/pred
    P(f"  n={n:>3}: true {true:+.4f};  shuffled {v.mean():+.4f} +- {v.std():.4f}"
      f"  -> z = {(true-v.mean())/v.std():+.1f} sigma")
