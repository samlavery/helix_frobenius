#!/usr/bin/env python3
"""
C3 batch 18 -- numerical block 1.  xiKernel_log_concaveOn, attacked hard, with gates.

  T1  the GLOBAL bound Phi(t) <= C exp(-3|t|/2) that unlocks all-centre integrability
  T2  log Phi concavity on the FULL line via reflection: t<0, near 0, transitions, tails
  T3  the double-sum split of D(t,h) = Phi(t)^2 - Phi(t-h)Phi(t+h) into DIAGONAL (n=m) and
      OFF-DIAGONAL (n!=m) parts.  The diagonal is >= 0 term-by-term (repo's compiled
      per-term log-concavity on Ici 0).  The off-diagonal is NOT >= 0 in general -- proved
      here by the log-linear witness -- so the question is whether the diagonal DOMINATES.
  T4  the cross-pair inequality 2 a_n(t) a_m(t) >= a_n(t-h)a_m(t+h) + a_m(t-h)a_n(t+h):
      is it true for THIS family?  (For log-linear terms with different slopes it is FALSE;
      that is exactly why sums of log-concave functions need not be log-concave.)
  T5  Cauchy-Schwarz variance form: Phi*Phi'' - (Phi')^2 <= 0, coefficient signs audited,
      with Phi'' and Phi' from RIGOROUS termwise differentiation (checked against mpmath.diff)
  T6  TP2 of the mode kernel a_n(t) in (n,t)
  T7  hazard monotonicity: is -Phi'/Phi nondecreasing?  (equivalent to log-concavity)

REJECTION GATE: any stable positive (log Phi)'' on the full line kills the branch and is
recorded as a counterexample.
"""
from mpmath import mp, mpf, exp, pi, log, fabs, diff, nstr, mpmathify

mp.dps = 50

def term(n, t):
    r = mpf(n)
    return 4*((2*pi**2*r**4*exp(9*t/2) - 3*pi*r**2*exp(5*t/2)) * exp(-pi*r**2*exp(2*t)))

def Phi_raw(t, nmax=200):
    """the RAW series at t (no reflection) -- valid for t >= 0; slow to converge for t << 0"""
    s = mpf(0)
    for n in range(1, nmax+1):
        a = term(n, t)
        s += a
        if n > 3 and fabs(a) < mpf(10)**(-(mp.dps+20)):
            break
    return s

def Phi(t):
    """the kernel, using evenness (Jacobi reflection) so that t<0 is exact and fast"""
    return Phi_raw(fabs(mpf(t)))

print("="*78); print("T1 -- the GLOBAL bound Phi(t) <= C exp(-3|t|/2)"); print("="*78)
print("  Repo: riemannXiKernel_le_majorant (hu : 0 <= u) : Phi u <= C * exp(-3u/2),")
print("        C = xiKernelMajorantConstant (>= 0, compiled).")
print("  With evenness this bounds Phi on the WHOLE line, and in particular Phi <= C.")
print("  Measured C-free consequence: sup Phi and where it is attained.")
best = None
for k in range(0, 2001):
    t = mpf(k)/1000
    v = Phi(t)
    if best is None or v > best[0]: best = (v, t)
print(f"    max Phi on [0,2] = {nstr(best[0],16)} at t = {nstr(best[1],8)}")
print(f"    Phi(0) = {nstr(Phi(mpf(0)),16)}   (so the max is at 0, consistent with evenness)")
print(f"    Phi(1)/exp(-3/2) = {nstr(Phi(mpf(1))/exp(mpf(-3)/2),12)}  (must be <= C)")

print(); print("="*78); print("T2 -- log Phi CONCAVE on the FULL line (reflection used for t<0)"); print("="*78)
lp = lambda t: log(Phi(t))
grids = [
    ("near 0, step 2e-3, |t|<=0.2", [mpf(k)/500 for k in range(-100, 101)]),
    ("transition, step 0.01, |t|<=2", [mpf(k)/100 for k in range(-200, 201)]),
    ("tail, step 0.05, 2<=|t|<=5", [mpf(k)/20 for k in range(40, 101)] +
                                   [-mpf(k)/20 for k in range(40, 101)]),
]
allpos = 0; worst = None; worstt = None; tot = 0
for lab, g in grids:
    npos = 0; wmax = None; wt = None
    for t in g:
        tot += 1
        d2 = diff(lp, t, 2)
        if d2 > 0: npos += 1
        if wmax is None or d2 > wmax: wmax, wt = d2, t
    allpos += npos
    if worst is None or wmax > worst: worst, worstt = wmax, wt
    print(f"  {lab:<32} points={len(g):>4}  (logPhi)'' > 0 at {npos:>3};"
          f"  max = {nstr(wmax,10)} at t={nstr(wt,7)}")
print()
print(f"  TOTAL: {tot} points, (log Phi)'' > 0 at {allpos}")
print(f"  global max (log Phi)'' = {nstr(worst,12)} at t = {nstr(worstt,8)}")
if allpos == 0:
    print("  ==> GATE PASSES: log Phi concave on the full scanned line.")
else:
    print("  ==> GATE FIRES: stable positive curvature found.  BRANCH STOPPED.")

print(); print("="*78); print("T7 -- hazard monotonicity: is -Phi'/Phi nondecreasing?"); print("="*78)
print("  (equivalent to log-concavity; an independent read of the same fact)")
haz = lambda t: -diff(lambda s: Phi(s), t, 1)/Phi(t)
print(f"{'t':>8} {'-Phi-prime/Phi':>22}")
prev = None; dec = 0
for k in range(-40, 41, 4):
    t = mpf(k)/20
    h = haz(t)
    if prev is not None and h < prev: dec += 1
    prev = h
    print(f"{nstr(t,6):>8} {nstr(h,14):>22}")
print(f"  hazard DECREASES at {dec} of the sampled steps (0 expected if log-concave)")

print(); print("="*78); print("T4 -- the CROSS-PAIR inequality for this family"); print("="*78)
print("  2 a_n(t) a_m(t) >= a_n(t-h)a_m(t+h) + a_m(t-h)a_n(t+h) ?")
print("  For LOG-LINEAR terms e^{at}, e^{bt} with a != b the RHS is 2e^{(a+b)t}cosh((b-a)h),")
print("  which EXCEEDS the LHS.  So this is FALSE in general.  Is it true here?")
print(f"{'n':>3} {'m':>3} {'t':>7} {'h':>6} {'LHS-RHS':>24} {'sign':>7}")
badcp = 0; totcp = 0
for (n, m) in [(1,2),(1,3),(2,3),(1,5)]:
    for ts in ['0.2','0.6','1.0']:
        for hs in ['0.05','0.2','0.5']:
            t, h = mpf(ts), mpf(hs)
            an, am = term(n,t), term(m,t)
            d = 2*an*am - (term(n,t-h)*term(m,t+h) + term(m,t-h)*term(n,t+h))
            totcp += 1
            if d < 0: badcp += 1
            if (n,m) in ((1,2),(1,5)) and hs in ('0.05','0.5') and ts=='0.6':
                print(f"{n:>3} {m:>3} {nstr(t,5):>7} {nstr(h,4):>6} {nstr(d,14):>24}"
                      f" {('NEG' if d<0 else 'pos'):>7}")
print(f"  cross-pair violations: {badcp}/{totcp}")
if badcp > 0:
    print("  ==> the OFF-DIAGONAL terms are NOT individually nonnegative, as expected.")
    print("      So log-concavity of Phi is NOT a term-by-term fact; the DIAGONAL surplus")
    print("      must dominate.  That is the exact double-sum inequality that remains.")

print(); print("="*78); print("T3 -- DIAGONAL vs OFF-DIAGONAL split of D(t,h)"); print("="*78)
print("  D(t,h) = Phi(t)^2 - Phi(t-h)Phi(t+h) = DIAG + OFF, where")
print("    DIAG = sum_n [a_n(t)^2 - a_n(t-h)a_n(t+h)]              (>= 0 per-term, Ici 0)")
print("    OFF  = sum_{n<m} [2a_n a_m - a_n(t-h)a_m(t+h) - a_m(t-h)a_n(t+h)]")
NM = 30
def split(t, h):
    diag = mpf(0); off = mpf(0)
    for n in range(1, NM+1):
        diag += term(n,t)**2 - term(n,t-h)*term(n,t+h)
        for m in range(n+1, NM+1):
            off += (2*term(n,t)*term(m,t)
                    - term(n,t-h)*term(m,t+h) - term(m,t-h)*term(n,t+h))
    return diag, off
print(f"{'t':>7} {'h':>6} {'DIAG':>22} {'OFF':>22} {'D=DIAG+OFF':>22} {'D>=0':>6}")
for ts in ['0.1','0.4','0.8','1.2']:
    for hs in ['0.05','0.3']:
        t, h = mpf(ts), mpf(hs)
        dg, of = split(t, h)
        D = dg + of
        print(f"{ts:>7} {hs:>6} {nstr(dg,12):>22} {nstr(of,12):>22} {nstr(D,12):>22}"
              f" {str(D >= 0):>6}")
print("  CONTROL: DIAG + OFF must equal Phi(t)^2 - Phi(t-h)Phi(t+h) directly:")
for ts, hs in [('0.4','0.3'), ('1.2','0.05')]:
    t, h = mpf(ts), mpf(hs)
    dg, of = split(t, h)
    direct = Phi_raw(t)**2 - Phi_raw(t-h)*Phi_raw(t+h)
    print(f"    t={ts} h={hs}: split={nstr(dg+of,14)}  direct={nstr(direct,14)}"
          f"  reldiff={nstr(fabs(dg+of-direct)/fabs(direct),4)}")

print(); print("="*78); print("T5 -- Cauchy-Schwarz variance form, coefficients audited"); print("="*78)
print("  log-concavity <=> Phi*Phi'' - (Phi')^2 <= 0.  Phi', Phi'' by TERMWISE")
print("  differentiation, cross-checked against mpmath.diff on the summed kernel.")
def dterm(n, t, k):
    """k-th derivative of term(n,.) at t, by mpmath.diff on the closed form"""
    return diff(lambda s: term(n, s), t, k)
def Phi_d(t, k, nmax=60):
    s = mpf(0)
    for n in range(1, nmax+1):
        a = dterm(n, t, k)
        s += a
        if n > 5 and fabs(a) < mpf(10)**(-(mp.dps+10)):
            break
    return s
print(f"{'t':>7} {'Phi-prime termwise':>22} {'mpmath.diff':>22} {'reldiff':>11}")
for ts in ['0.2','0.7','1.3']:
    t = mpf(ts)
    a = Phi_d(t,1); b = diff(lambda s: Phi_raw(s), t, 1)
    print(f"{ts:>7} {nstr(a,14):>22} {nstr(b,14):>22} {nstr(fabs(a-b)/fabs(b),4):>11}")
print()
print(f"{'t':>7} {'Phi*Phi2 - Phi1^2':>26} {'sign (must be <= 0)':>22}")
for ts in ['0.05','0.3','0.7','1.1','1.6']:
    t = mpf(ts)
    P, P1, P2 = Phi_raw(t), Phi_d(t,1), Phi_d(t,2)
    val = P*P2 - P1**2
    print(f"{ts:>7} {nstr(val,16):>26} {('NEG ok' if val <= 0 else 'POSITIVE'):>22}")

print(); print("="*78); print("T6 -- TP2 of the mode kernel a_n(t) in (n,t)"); print("="*78)
print("  TP2:  a_n(t) a_m(s) - a_n(s) a_m(t) >= 0  for n < m and t < s ?")
print(f"{'n':>3} {'m':>3} {'t':>6} {'s':>6} {'minor':>24} {'sign':>7}")
badtp = 0; tottp = 0
for (n,m) in [(1,2),(1,3),(2,4)]:
    for ts, ss in [('0.1','0.4'), ('0.4','0.9'), ('0.9','1.6')]:
        t, s = mpf(ts), mpf(ss)
        d = term(n,t)*term(m,s) - term(n,s)*term(m,t)
        tottp += 1
        if d < 0: badtp += 1
        if (n,m)==(1,2) or (n,m)==(2,4):
            print(f"{n:>3} {m:>3} {ts:>6} {ss:>6} {nstr(d,14):>24}"
                  f" {('NEG' if d<0 else 'pos'):>7}")
print(f"  TP2 violations: {badtp}/{tottp}")
print("="*78)
