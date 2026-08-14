"""ATTEMPT 026 -- the ADAPTIVE-SCALE tape (Sam's suggestion), i.e. the Landau variable.

THE DEFECT BEING REPAIRED.  The theta-tape unfolds to density 1 via u = theta/pi.  That
necessarily rescales frequencies by 2pi/L(t), so a prime clock sits at tau_n = log n / L(t) and
DRIFTS as L varies across the window.  The cost is the criterion R = U log n log(1+W/T)/L^2,
which has now failed three times today: attempt 010 at low height, attempt 021 at R = 27-121,
and attempt 023 where it manufactured a spurious excess above tau = 1.

ADAPTIVE SCALING.  Let the scale adapt so the structure stays put: use the variable in which
the prime frequencies are FIXED.  In t the phase is gamma log n, so the adaptive-scale spectrum
is simply
        A(n) = sum_{gamma in W} n^{i gamma}
with the line for n at frequency log n at EVERY height.  No unfolding, hence no R at all.

THE LAW, and it is cleaner than the tape's.  Landau (1911) / Gonek (1993):
        sum_{0 < gamma <= T} n^{i gamma} = -(T/2pi) Lambda(n)/sqrt(n) + O(sqrt n log n loglog n)
for n > 1 a prime power, and 0 (to the same error) otherwise.  Over a window [T1,T2],
        A(n) = -(W/2pi) Lambda(n)/sqrt(n) + O(...),      W = T2 - T1,
so the NORMALISED amplitude  A(n)/(W/2pi)  is  -Lambda(n)/sqrt(n)  with NO L, NO U, and an
error that does not grow with T.  Wide windows are now an ASSET: the relative error falls like
1/W.  This is the precise sense in which adaptive scaling beats the fixed unfolding.

PAIRING.  house: the theta-tape line law and its R criterion -- specifically the attempt-011
derivation that the tape law IS Landau/Gonek dressed by the unfolding, with R exactly the
quadratic dephasing introduced by that dressing.  classical: Landau's theorem in Gonek's
uniform form.  MECHANISM: undressing the tape returns the theorem to its native variable,
where the dephasing term R is identically absent -- so the house instrument's known failure
mode is removed by construction rather than by choosing gentler windows.

STATED NULL, pre-registered.  Pooling over the widest available window (gamma in [14, 20000],
22491 zeros, W ~ 2e4) does NOT recover -Lambda(n)/sqrt(n): either the modulus misses, or the
phase is not pi (the sum must be a NEGATIVE REAL), or composites fail to vanish.  Then the
wide-window failure is intrinsic and adaptive scaling buys nothing.
"""
import numpy as np, math, sys, os
from math import log, pi, sqrt

def P(*a): print(*a); sys.stdout.flush()

def vonm(n):
    m = n
    for p in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m % p == 0:
            while m % p == 0: m //= p
            return log(p) if m == 1 else 0.0
    return 0.0

SETS = [('long [14,2e4]','att019_zeros_to20k.npy'), ('T=1e3','att010_zeros_1e+03.npy'),
        ('T=1e5','att010_zeros_1e+05.npy'), ('T=1e7','att010_zeros_1e+07.npy')]

NS = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,19,23,25,27,29,31,32,49]

P("A(n) = sum_gamma n^{i gamma};  normalised  a(n) = A(n)/(W/2pi)  must equal -Lambda(n)/sqrt(n).\n")
for name, f in SETS:
    if not os.path.exists(f): continue
    g = np.load(f); W = g[-1] - g[0]
    P(f"{name}:  {len(g)} zeros, gamma in [{g[0]:.2f}, {g[-1]:.2f}], W = {W:.1f}")
    P(f"  {'n':>4}{'Lam(n)':>9}{'pred -Lam/sqrt n':>18}{'measured Re a':>15}"
      f"{'|Im a|':>9}{'obs/pred':>10}{'phase/pi':>10}")
    ratios = []
    for n in NS:
        A = np.exp(1j*g*log(n)).sum()
        a = A/(W/(2*pi))
        pred = -vonm(n)/sqrt(n)
        r = (a.real/pred) if pred != 0 else float('nan')
        if pred != 0: ratios.append(r)
        ph = math.atan2(a.imag, a.real)/pi if abs(a) > 1e-12 else float('nan')
        P(f"  {n:>4}{vonm(n):>9.4f}{pred:>18.5f}{a.real:>15.5f}{abs(a.imag):>9.5f}"
          f"{r:>10.3f}{ph:>10.3f}")
    rr = np.array(ratios)
    P(f"  -> prime powers: median obs/pred {np.median(rr):.4f}, "
      f"IQR {np.percentile(rr,25):.4f}-{np.percentile(rr,75):.4f}, n={len(rr)}")
    comp = [n for n in NS if vonm(n) == 0]
    cm = [abs(np.exp(1j*g*log(n)).sum()/(W/(2*pi))) for n in comp]
    P(f"  -> composites {comp}: max |a| = {max(cm):.5f}  (must be ~0)\n")

P("THE POINT OF THE EXERCISE -- error vs window, which the tape could not do.")
P("  Gonek's error is O(sqrt n log n loglog n), independent of T, so |obs/pred - 1| must")
P("  FALL like 1/W.  Sub-windows of the long set, same n-set:")
g = np.load('att019_zeros_to20k.npy')
P(f"  {'window':>22}{'#zeros':>8}{'W':>9}{'median obs/pred':>18}{'spread(IQR)':>13}")
for lo, hi in ((14, 200), (14, 1000), (14, 5000), (14, 10000), (14, 20000)):
    sub = g[(g >= lo) & (g <= hi)]
    if len(sub) < 30: continue
    W = sub[-1] - sub[0]
    rs = []
    for n in NS:
        p = vonm(n)
        if p == 0: continue
        a = (np.exp(1j*sub*log(n)).sum()/(W/(2*pi))).real
        rs.append(a/(-p/sqrt(n)))
    rs = np.array(rs)
    P(f"  {f'[{lo},{hi}]':>22}{len(sub):>8}{W:>9.0f}{np.median(rs):>18.4f}"
      f"{np.percentile(rs,75)-np.percentile(rs,25):>13.4f}")

P("\n  CONTRAST: the tape's own criterion on the same widest window would be")
U = 22491; L = 2*log(10000/(2*pi))
P(f"    R(n=2) = U log2 log(1+W/T)/L^2 = {U*log(2)*log(1+19985/14)/L**2:.0f}  -- catastrophic,")
P("    which is exactly why attempts 021 and 023 failed there.  The adaptive variable has no R.")
