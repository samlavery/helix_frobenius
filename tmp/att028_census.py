"""ATTEMPT 028 -- STAGE 2: zero census for the three D=-23 specimens on t in [10, T1].

PRE-REGISTERED VALIDITY CRITERIA (computed before the run, rule 7):
  V1  engine accuracy at the top of the window: |engine - zeta*L(chi_23)|/|.| < 1e-6 at t = T1.
  V2  grid refinement: the sign-change count must be stable under step -> step/2 -> step/4.
  V3  census vs the theta_Q count.  zeta_K and L(f) are the CONTROLS: both are expected to have
      every zero on the line in this range, so their deficit must be ~0.  F (Epstein principal
      class) is the specimen with genuinely off-line zeros (Davenport-Heilbronn 1936 for h>1),
      so a POSITIVE deficit there is the expected reading, not a bug -- but only if the two
      controls come out clean at the same step.
  V4  zeta_K's zero set must CONTAIN every cached zeta zero in the window (att019_zeros_to20k),
      since zeta_K = zeta * L(chi_-23) exactly.  This is an end-to-end gate on zero-finding.
"""
import numpy as np, mpmath as mp, math, sys, time, os
from math import pi, sqrt, log
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_engine import D, C, coefficients, chi23, Engine, theta_Q, find_zeros

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 1200.0
DELTA = 0.012
STEP = 0.04

a1, aC, dK, bf = coefficients(6000)
t0 = time.time()
engs = {'F': Engine(a1, 0.5, delta=DELTA), 'zetaK': Engine(dK, 1.5, delta=DELTA),
        'Lf': Engine(bf, 0.0, delta=DELTA)}
P(f"engines: delta={DELTA}  n_max={engs['F'].nmax}  V={engs['F'].V:.3f}  M={engs['F'].M}  "
  f"built in {time.time()-t0:.1f}s")
P(f"predicted digit loss at t=T1: {DELTA*T1/math.log(10):.2f}")

# ---------------------------------------------------------------- V1
def LamK_direct(t, dps):
    mp.mp.dps = dps
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    L = mp.mpf(23)**(-s)*sum(chi23(r)*mp.zeta(s, mp.mpf(r)/23) for r in range(1, 23) if chi23(r))
    return (mp.sqrt(23)/(2*mp.pi))**s*mp.gamma(s)*mp.zeta(s)*L
P("\nV1  engine vs independent zeta*L(chi_23):")
v1ok = True
for t in (600.0, 900.0, 1200.0):
    dps = int(0.7*t) + 60
    ref = float(mp.re(LamK_direct(t, dps)*mp.e**(mp.pi*mp.mpf(t)/2)))
    got = engs['zetaK'].lam_scaled(t)
    rel = abs(got-ref)/abs(ref)
    v1ok &= rel < 1e-6
    P(f"    t={t:>7.1f}  engine {got:>20.12g}  direct {ref:>20.12g}  rel {rel:.2e}")
P(f"    V1 {'PASS' if v1ok else 'FAIL'}")

# ---------------------------------------------------------------- V2 / V3
exp_n = (theta_Q(np.array([T1]))[0] - theta_Q(np.array([T0]))[0])/pi
P(f"\ntheta_Q count over [{T0},{T1}] = {exp_n:.2f} zeros per specimen "
  f"(identical Gamma factor and conductor for all three)")

Z = {}
P(f"\nV2/V3  sign-change census (step {STEP}, then refinements):")
for nm, eng in engs.items():
    cache = f'/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_{nm}.npy'
    t0 = time.time()
    counts = []
    for st in (STEP, STEP/2, STEP/4):
        ts = np.arange(T0, T1+st, st)
        vals = np.array([eng.lam_scaled(float(t)) for t in ts])
        idx = np.nonzero(np.signbit(vals[:-1]) != np.signbit(vals[1:]))[0]
        counts.append(len(idx))
        if st == STEP/4:
            from scipy.optimize import brentq
            f = lambda x: eng.lam_scaled(float(x))
            Z[nm] = np.array([brentq(f, ts[i], ts[i+1], xtol=1e-10, rtol=1e-14) for i in idx])
    np.save(cache, Z[nm])
    d = exp_n - counts[-1]
    P(f"  {nm:>6}: counts at step {STEP}/{STEP/2}/{STEP/4} = {counts}   "
      f"final {counts[-1]}   deficit {d:+.2f}  ({100*d/exp_n:+.2f}%)   [{time.time()-t0:.0f}s]")

# ---------------------------------------------------------------- V4
gz = np.load('/Users/samuellavery/work/helix_frobenius/tmp/att019_zeros_to20k.npy')
gz = gz[(gz >= T0) & (gz <= T1)]
zk = Z['zetaK']
miss = 0; worst = 0.0
for g in gz:
    d = np.min(np.abs(zk - g))
    worst = max(worst, d)
    if d > 1e-6: miss += 1
P(f"\nV4  cached zeta zeros in window: {len(gz)}.  Present in the engine's zeta_K set: "
  f"{len(gz)-miss}/{len(gz)}, worst match {worst:.2e}   "
  f"[{'PASS' if miss == 0 else 'FAIL'}]")
P(f"    implied L(chi_-23) zero count = {len(zk)} - {len(gz)} = {len(zk)-len(gz)}")
