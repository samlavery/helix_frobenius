"""ATTEMPT 028 -- STAGE 1: gates on the engine, BEFORE any zero is looked for.

VALIDITY CRITERIA COMPUTED BEFORE RUNNING (rule 7):
  G1  arithmetic: d_K(n) == sum_{d|n} chi_{-23}(d) for all n <= 2000, and a_1 + 2 a_C = d_K.
  G2  Dirichlet-series gate at s = 2 (Re s > 1, no cancellation there):
      (sqrt23/2pi)^2 Gamma(2) sum coef(n) n^{-2}  ==  Lambda(2) from the rotated formula.
  G3  the decisive one: rotated-ray Lambda(1/2+it) in double precision  ==  020's alpha=0
      two-sided incomplete-gamma expansion evaluated in mpmath at dps > 0.7 t + 30.
      PASS = relative agreement < 1e-6 at every t tested.
  G4  Lambda(1/2+it) must be REAL: the engine returns a real by construction, so instead we
      check the imaginary part of the mpmath alpha=0 evaluation is < 1e-25 relative.
If G3 fails the attempt is BROKEN and says so.
"""
import numpy as np, mpmath as mp, math, sys, time
from math import pi, sqrt, log
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_engine import (D, C, LOGQ, coefficients, chi23, vonmangoldt_like, Engine, theta_Q)

def P(*a): print(*a); sys.stdout.flush()

NC = 4000
a1, aC, dK, bf = coefficients(NC)

# ---------------------------------------------------------------- G1
bad = 0
for n in range(1, 2001):
    d = sum(chi23(dd) for dd in range(1, n+1) if n % dd == 0)
    if abs(dK[n] - d) > 1e-9:
        bad += 1
P(f"G1  d_K(n) == sum_{{d|n}} chi_-23(d)  over n<=2000 : mismatches = {bad}   "
  f"[{'PASS' if bad == 0 else 'FAIL'}]")
P(f"    a_1(1..14) = {[int(a1[i]) for i in range(1,15)]}")
P(f"    a_C(1..14) = {[int(aC[i]) for i in range(1,15)]}")
P(f"    d_K(1..14) = {[int(dK[i]) for i in range(1,15)]}")
P(f"    b_f(1..14) = {[int(bf[i]) for i in range(1,15)]}   (weight-1 newform eta(z)eta(23z))")

# ---------------------------------------------------------------- Lambda tables
NL = 64
LamF = vonmangoldt_like(a1, NL)
LamK = vonmangoldt_like(dK, NL)
Lamf = vonmangoldt_like(bf, NL)
def vonm(n):
    m = n
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m % p == 0:
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0

P("\nTHE DISCRIMINATOR TABLE  (Lambda from  coef(n)log n = sum_{d|n} Lam(d) coef(n/d))")
P(f"  {'n':>4}{'a_1':>6}{'Lam_F':>11}{'Lam_zetaK':>11}{'Lam_f':>11}{'zeta Lam':>11}   note")
NSHOW = [2,3,4,5,6,7,8,9,10,11,12,13,16,18,23,24,25,27,29,31,32,36,46,49]
for n in NSHOW:
    note = ""
    if abs(LamF[n]) > 1e-9 and vonm(n) == 0: note = "<-- NON-PRIME-POWER LINE"
    if abs(LamF[n]) < 1e-9 and vonm(n) > 0:  note = "<-- zeta rings, F silent"
    P(f"  {n:>4}{int(a1[n]):>6}{LamF[n]:>11.5f}{LamK[n]:>11.5f}{Lamf[n]:>11.5f}"
      f"{vonm(n):>11.5f}   {note}")
np.save('/Users/samuellavery/work/helix_frobenius/tmp/att028_lam.npy',
        np.vstack([LamF[:NL+1], LamK[:NL+1], Lamf[:NL+1]]))

# ---------------------------------------------------------------- engines
DELTA = 0.025
t0 = time.time()
engF = Engine(a1, 0.5, delta=DELTA, name='F (principal class)')
engK = Engine(dK, 1.5, delta=DELTA, name='zeta_K')
engf = Engine(bf, 0.0, delta=DELTA, name='L(f)')
P(f"\nengines built in {time.time()-t0:.1f}s   "
  f"n_max={engF.nmax}  V={engF.V:.3f}  M={engF.M}  h={engF.h}  alpha=pi/2-{DELTA}")
P(f"    predicted digit loss at t: delta*t/ln10 = {DELTA/math.log(10):.4f} * t"
  f"   (t=600 -> {DELTA*600/math.log(10):.1f} digits)")

# ---------------------------------------------------------------- G2 (s=2)
def lam_gen_rot(eng, coef, s, dps):
    """rotated formula at general s, in mpmath -- for the Re s > 1 gate."""
    mp.mp.dps = dps
    s = mp.mpc(s)
    a = mp.mpf(eng.alpha)
    ea, eb = mp.e**(1j*a), mp.e**(-1j*a)
    tot = mp.mpc(0)
    for n in eng.nz:
        x = mp.mpf(C)*int(n)
        tot += coef[n]*(x**(-s)*mp.gammainc(s, x*ea) + x**(s-1)*mp.gammainc(1-s, x*eb))
    return tot + eng.pc*(eb**(1-s)/(s-1) - ea**s/s)

P("\nG2  Dirichlet-series gate at s = 2  (Re s > 1, cancellation-free region)")
for nm, eng, coef in (('F', engF, a1), ('zeta_K', engK, dK), ('L(f)', engf, bf)):
    mp.mp.dps = 30
    ser = sum(mp.mpf(coef[n])*mp.mpf(n)**(-2) for n in range(1, NC+1) if coef[n])
    lhs = (mp.sqrt(D)/(2*mp.pi))**2*mp.gamma(2)*ser
    rot = lam_gen_rot(eng, coef, mp.mpf(2), 30)
    P(f"    {nm:>7}: series {mp.nstr(lhs,12)}   rotated {mp.nstr(rot,12)}   "
      f"reldiff {float(abs(rot-lhs)/abs(lhs)):.2e}")

# ---------------------------------------------------------------- G3 (the decisive gate)
def lam_alpha0(coef, t, dps, nmax):
    """020's route: alpha = 0 two-sided incomplete gamma, at dps high enough to survive."""
    mp.mp.dps = dps
    s = mp.mpf(0.5) + 1j*mp.mpf(t)
    tot = mp.mpc(0)
    for n in range(1, nmax+1):
        if coef[n] == 0: continue
        x = mp.mpf(C)*n
        tot += coef[n]*(x**(-s)*mp.gammainc(s, x) + x**(s-1)*mp.gammainc(1-s, x))
    return tot

P("\nG3  DECISIVE: rotated double-precision engine  vs  020's alpha=0 route at high dps")
P(f"  {'t':>7}{'dps':>6}{'|Im|/|Re| (mpmath)':>21}{'engine Lam*e^{pi t/2}':>24}"
  f"{'mpmath Lam*e^{pi t/2}':>24}{'rel':>11}")
G3_ok = True
for t, dps, nmx in ((5.0, 60, 260), (15.0, 80, 260), (30.0, 100, 260),
                    (60.0, 140, 300), (100.0, 200, 340)):
    for nm, eng, coef, pcoef in (('F', engF, a1, mp.mpf(1)/2),
                                 ('zeta_K', engK, dK, mp.mpf(3)/2),
                                 ('L(f)', engf, bf, mp.mpf(0))):
        mp.mp.dps = dps
        s = mp.mpf(0.5) + 1j*mp.mpf(t)
        lam = lam_alpha0(coef, t, dps, nmx) + pcoef*(1/(s-1) - 1/s)
        scale = mp.e**(mp.pi*mp.mpf(t)/2)
        ref = float(mp.re(lam)*scale)
        imr = float(abs(mp.im(lam))/abs(mp.re(lam)))
        got = eng.lam_scaled(t)
        rel = abs(got-ref)/max(abs(ref), 1e-300)
        if rel > 1e-6: G3_ok = False
        P(f"  {nm:>7}{t:>7.1f}{dps:>6}{imr:>21.3e}{got:>24.12g}{ref:>24.12g}{rel:>11.2e}")
P(f"  G3 verdict: {'PASS' if G3_ok else 'FAIL -- BROKEN'}   (criterion rel < 1e-6, set before running)")

# ---------------------------------------------------------------- G5 identity F = (K+2f)/3
P("\nG5  identity  F = (zeta_K + 2 L(f))/3  at the level of the computed Hardy functions")
for t in (11.3, 47.9, 133.7, 401.5, 588.2):
    hF, hK, hf = engF.hardy(t), engK.hardy(t), engf.hardy(t)
    P(f"    t={t:>7.1f}  H_F={hF:>14.8f}   (H_K+2H_f)/3={((hK+2*hf)/3):>14.8f}   "
      f"diff {abs(hF-(hK+2*hf)/3):.2e}")

# ---------------------------------------------------------------- timing
t0 = time.time()
for t in np.linspace(10, 600, 200): engF.hardy(float(t))
P(f"\ntiming: {1000*(time.time()-t0)/200:.3f} ms per Hardy evaluation")
