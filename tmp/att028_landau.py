"""ATTEMPT 028 -- STAGE 3: THE TEST.  The adaptive (Landau) variable on a non-Euler-product
L-function whose functional equation, Gamma factor, conductor and zero density are identical to
two Euler-product controls.

PAIRING.  house: the ADAPTIVE (Landau) VARIABLE of attempts 026/027 -- a(n) = (2 pi/W) sum_gamma
n^{i gamma}, calibrated on 22491 zeta zeros to median obs/pred 1.0003 with phase +-1.000 pi, and
carrying the instrument decision that wide windows are an asset and the PHASE is the test
x classical: Landau (1911) / Gonek (1993) plus the class-group decomposition of the Epstein zeta
of a class-number-3 discriminant (Epstein 1903; Potter-Titchmarsh 1935; Davenport-Heilbronn 1936).
MECHANISM.  Landau's contour argument reads off -F'/F on Re s = A > 1 from the ORDINATES of the
zeros.  -F'/F is supported on prime powers if and only if F is an Euler product.  The principal
class of D = -23 gives Z = w*zeta_{K,1} = (w/3)(zeta_K + 2 L(f)), a SUM of two Euler products,
so its Lambda_1 lives on non-prime-powers.  The two summands are the controls: they fail by
MISSING that structure, at matched conductor and matched Gamma factor.

DERIVED NORMALISATION (stated, as required).  Write F(s) = sum a_1(n) n^{-s}, a_1(1) = 1.  The
Epstein zeta is Z_Q = w * F with w = 2 units, but -Z_Q'/Z_Q = -F'/F, so the unit count DROPS OUT
of the prediction entirely.  Z_Q has a simple pole at s = 1; the Landau rectangle is
[1-A, A] x [T0, T1] with T0 = 10 > 1, so the pole is OUTSIDE the contour and contributes NOTHING.
(It would have contributed x/(W/2pi) had the window started at 0 -- 2 pi n / W = 0.14 at n = 27,
not negligible, which is why the window form is the right one.)  Hence, with no free constants,

        a_pred(n) = -Lambda_1(n)/sqrt(n),     Lambda_1 from  a(n) log n = sum_{d|n} Lam(d) a(n/d),

the SAME normalisation zeta obeys to 1.0003.

STATED NULLS, pre-registered before the run.
  NULL-1 (support).  The Epstein zeros show ZETA's / an Euler product's line structure: the
     non-prime-power cells are empty, |a(6)|, |a(12)|, |a(18)| < 0.25 (predicted 1.36-1.46), AND
     the cells where F is silent but zeta rings are occupied, |a(n)| > 0.15 for n in
     {2,3,5,7,11,13}.  Then the adaptive instrument cannot see the Euler product.
  NULL-2 (amplitude).  At the n with Lambda_1(n) != 0, median |obs/pred - 1| > 0.5.
  NULL-3 (phase).  The sums are not negative reals: for the majority of lines with
     Lambda_1(n) > 0, |arg(a)/pi| < 0.75.
  CONTROL FAILURE (invalidates the instrument, not the specimen).  If zeta_K or L(f) -- both
     genuine Euler products -- show |a(n)| > 0.25 at n = 6, 12 or 18, the controls have failed by
     EXTRA structure rather than missing structure and nothing here is readable.
  NOISE FLOOR.  n with Lambda = 0 for all three specimens: 10,14,15,20,21,22,26,28,30,33,34,35,
     38,39,40,42,44,45,50.  Reported as the floor every claimed line must clear.

VALIDITY CRITERION COMPUTED BEFORE THE RUN (rule 7).  Gonek's error for the adaptive variable is
O(sqrt(n) log n loglog n / W).  With W = 1190 this is 0.0171 at n = 27, 0.0122 at n = 18,
0.0069 at n = 6 -- i.e. ~1% of the predicted line heights.  There is no window-ratio constraint.
"""
import numpy as np, math, sys
from math import pi, log, sqrt
sys.path.insert(0, '/Users/samuellavery/work/helix_frobenius/tmp')
from att028_engine import coefficients, vonmangoldt_like

def P(*a): print(*a); sys.stdout.flush()

T0, T1 = 10.0, 1200.0
W = T1 - T0
a1, aC, dK, bf = coefficients(4000)
NL = 64
LAM = {'F': vonmangoldt_like(a1, NL), 'zetaK': vonmangoldt_like(dK, NL),
       'Lf': vonmangoldt_like(bf, NL)}
TITLE = {'F': 'F = Epstein principal class (NOT an Euler product)',
         'zetaK': 'zeta_K = Dedekind of Q(sqrt-23)  [Euler product]  CONTROL',
         'Lf': 'L(f), f = eta(z)eta(23z) wt-1 newform [Euler product] CONTROL'}

NS = [2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 18, 23, 25, 27, 32, 36, 46, 49]
NOISE = [10, 14, 15, 20, 21, 22, 26, 28, 30, 33, 34, 35, 38, 39, 40, 42, 44, 45, 50]

P("VALIDITY (computed before the run):  Gonek error sqrt(n) log n loglog n / W, W = %.0f" % W)
for n in (6, 12, 18, 27):
    P("    n=%2d : %.4f" % (n, sqrt(n)*log(n)*log(log(n))/W))

Z = {k: np.load(f'/Users/samuellavery/work/helix_frobenius/tmp/att028_zeros_{k}.npy')
     for k in ('F', 'zetaK', 'Lf')}

def adaptive(g, n):
    return complex(np.exp(1j*g*log(n)).sum()/(W/(2*pi)))

res = {}
for key in ('F', 'zetaK', 'Lf'):
    g = Z[key]; L = LAM[key]
    P(f"\n{'='*104}\n{key}:  {TITLE[key]}\n  zeros used {len(g)}  t in [{g[0]:.2f},{g[-1]:.2f}]  W={W:.0f}")
    P(f"  {'n':>4}{'Lam(n)':>10}{'a_pred':>10}{'a_meas.Re':>11}{'a_meas.Im':>11}"
      f"{'|a|':>9}{'arg/pi':>9}{'obs/pred':>10}  verdict")
    rats = []; rows = {}
    for n in NS:
        a = adaptive(g, n)
        pred = -L[n]/sqrt(n)
        ph = math.atan2(a.imag, a.real)/pi
        if abs(pred) > 1e-9:
            r = a.real/pred; rats.append(r)
            v = 'line ok' if (abs(r-1) < 0.5 and abs(abs(ph)-1) < 0.25) else 'MISS'
        else:
            r = float('nan')
            v = 'silent ok' if abs(a) < 0.15 else 'PRESENT!'
        rows[n] = (a, pred, r)
        P(f"  {n:>4}{L[n]:>10.5f}{pred:>10.5f}{a.real:>11.5f}{a.imag:>11.5f}"
          f"{abs(a):>9.5f}{ph:>9.4f}{r:>10.4f}  {v}")
    nf = [abs(adaptive(g, n)) for n in NOISE]
    rr = np.array(rats)
    P(f"  -> median obs/pred {np.median(rr):.4f}   IQR {np.percentile(rr,25):.4f}-{np.percentile(rr,75):.4f}"
      f"   n_lines={len(rr)}")
    P(f"  -> NOISE FLOOR over {len(NOISE)} all-silent n: median |a| {np.median(nf):.5f}, "
      f"max {max(nf):.5f}")
    res[key] = (rows, rr, nf)

# ------------------------------------------------------------------ verdict on the nulls
P("\n" + "="*104)
P("NULL EVALUATION")
rowsF = res['F'][0]
cellsA = [6, 12, 18]
cellsB = [2, 3, 5, 7, 11, 13]
mA = max(abs(rowsF[n][0]) for n in cellsA if n in rowsF)
mB = max(abs(rowsF[n][0]) for n in cellsB if n in rowsF)
P(f"  NULL-1 support: max|a| on the NON-PRIME-POWER cells {cellsA} = {mA:.4f} "
  f"(null needs < 0.25);  max|a| on the zeta-rings-F-silent cells {cellsB} = {mB:.4f} "
  f"(null needs > 0.15)")
P(f"     -> NULL-1 {'HOLDS' if (mA < 0.25 and mB > 0.15) else 'REJECTED'}")
med = np.median(res['F'][1])
P(f"  NULL-2 amplitude: median obs/pred on F's lines = {med:.4f}, |median-1| = {abs(med-1):.4f} "
  f"(null needs > 0.5) -> NULL-2 {'HOLDS' if abs(med-1) > 0.5 else 'REJECTED'}")
phs = [abs(math.atan2(rowsF[n][0].imag, rowsF[n][0].real)/pi) for n in NS if abs(rowsF[n][1]) > 1e-9]
frac = np.mean([p > 0.75 for p in phs])
P(f"  NULL-3 phase: fraction of F's lines with |arg/pi| > 0.75 = {frac:.3f}; median |arg/pi| = "
  f"{np.median(phs):.4f} -> NULL-3 {'HOLDS' if frac < 0.5 else 'REJECTED'}")
for c in ('zetaK', 'Lf'):
    m = max(abs(res[c][0][n][0]) for n in cellsA if n in res[c][0])
    P(f"  CONTROL {c}: max|a| on {cellsA} = {m:.4f} (must be < 0.25 -- controls fail by MISSING "
      f"structure) -> {'ok' if m < 0.25 else 'CONTROL FAILURE'}")
