"""ATTEMPT 031, part D -- remove the Monte-Carlo noise: EXACT u-sampled moments, the EXACT
boundary term, and the honest re-statement of part C's badly-chosen criteria.

TWO PRE-REGISTRATION DEFECTS IN PART C, named before the numbers.
 (1) C1 used a RELATIVE deviation with an |sinc| > 0.05 cut.  That is the wrong criterion: the
     derivation predicts an ADDITIVE boundary term of fixed size ~1/(xU), so the relative
     deviation must blow up wherever sinc(x/2) is small -- which is exactly where C1 "failed"
     (x = 6, 7, 8, i.e. |sinc| = 0.047, 0.100, 0.189).  Restated correctly here as an ABSOLUTE
     test against the exactly-derived boundary term.
 (2) C4 said "halve the sample and the residual must double".  The derivation gives a BOUND with
     an oscillating O(1) numerator, not a monotone 1/n law, so "doubling" was never predicted.
     Restated as the bound it actually is.

THE EXACT IDENTITY (all terms, nothing dropped).  With A_k = S_k + 1/2, B_k = S_{k+1} - 1/2,
U = u_n - u_1, Phi(x) = (1/n) sum_k e^{i x S_k}:
   phi_u(x) = (n/U) sinc(x/2) Phi(x)  +  [ e^{i x (S_1 - 1/2)} - e^{i x (S_n + 1/2)} ] / (i x U).
NULL: this fails at better than 1e-12 relative.  (It is an identity; this is a floating-point
and bookkeeping gate on the derivation, stated as such.)

EXACT u-MOMENTS.  E[S_u^m] = (1/((m+1)U)) sum_k ( A_k^{m+1} - B_k^{m+1} ) -- closed form, no
sampling.  With these the cumulant differences kappa_j(u) - kappa_j(zeros) are computed with NO
Monte-Carlo error, so the B_j/j prediction can be tested at the boundary-term level.
NULL: |kappa_j(u) - kappa_j(z) - B_j/j| > 5e-4 for j = 2,4,6,8 (the O(1/n) boundary scale).

AND the decomposition test, pre-registered: if the independent-prime random model supplies the
SMOOTH part of S and the sawtooth supplies the JUMP part, then
    kappa_4(u)  =?  kappa_4(model) + B_4/4 = -0.00176 - 0.00833 = -0.01009,
    kappa_6(u)  =?  kappa_6(model) + B_6/6 = +0.000228 + 0.003968 = +0.004196.
NULL: this composite misses by more than 30%.  (The pure random model missed kappa_4(u) by 6-7x,
so the sawtooth is the bulk of it; the question is what is left over.)
"""
import numpy as np, math, os, sys
from math import pi

def P(*a): print(*a); sys.stdout.flush()
HERE = os.path.dirname(os.path.abspath(__file__))

def theta(t):
    t = np.asarray(t, float)
    return (t/2*np.log(t/(2*pi)) - t/2 - pi/8 + 1/(48*t) + 7/(5760*t**3)
            + 31/(80640*t**5) + 127/(430080*t**7))

SETS = [('T=1e3', 'att010_zeros_1e+03.npy'), ('T=1e4', 'att010_zeros_1e+04.npy'),
        ('T=1e5', 'att010_zeros_1e+05.npy'), ('T=1e6', 'att010_zeros_1e+06.npy'),
        ('T=1e7', 'att010_zeros_1e+07.npy'), ('long[14,2e4]', 'att019_zeros_to20k.npy')]
BERN = {2: 1/12, 3: 0.0, 4: -1/120, 5: 0.0, 6: 1/252, 7: 0.0, 8: -1/240}

def load(f):
    g = np.load(os.path.join(HERE, f)); n = len(g)
    u = theta(g)/pi
    k1 = int(round(u[0]+1.5)); S = (k1+np.arange(n))-1.5-u
    sh = int(round(S.mean())); k1 -= sh; S = (k1+np.arange(n))-1.5-u
    return g, u, S, n

def raw_to_cum(raw, order=8):
    """raw moments m_1..m_order -> cumulants, via the standard recursion."""
    from math import comb
    k = [0.0]*(order+1)
    for nn in range(1, order+1):
        s = raw[nn]
        for i in range(1, nn):
            s -= comb(nn-1, i-1)*k[i]*raw[nn-i]
        k[nn] = s
    return {j: k[j] for j in range(1, order+1)}

P(__doc__)
P("="*100)
P("D1 -- the EXACT identity (boundary term included).  relative error must be ~1e-15.")
P(f"   {'set':>14}" + "".join(f"{'x='+str(x):>12}" for x in (1.0, 3.0, 6.28318, 8.0)))
for name, f in SETS:
    g, u, S, n = load(f)
    U = u[-1]-u[0]
    row = []
    for x in (1.0, 3.0, 2*pi, 8.0):
        A = S[:-1]+0.5; B = S[1:]-0.5
        lhs = (np.exp(1j*x*A)-np.exp(1j*x*B)).sum()/(1j*x*U)
        Phi = np.exp(1j*x*S).mean()
        rhs = (n/U)*(math.sin(x/2)/(x/2))*Phi + (np.exp(1j*x*(S[0]-0.5))-np.exp(1j*x*(S[-1]+0.5)))/(1j*x*U)
        row.append(abs(lhs-rhs)/max(abs(lhs), 1e-300))
    P(f"   {name:>14}" + "".join(f"{r:>12.2e}" for r in row))

P("\nD2 -- ABSOLUTE residual |phi_u - (n/U) sinc(x/2) Phi| against the derived bound 2/(xU)")
P(f"   {'set':>14}{'2/(1*U)':>10}" + "".join(f"{'x='+f'{x:g}':>22}" for x in (1.0, 3.0, 2*pi, 8.0)))
for name, f in SETS:
    g, u, S, n = load(f); U = u[-1]-u[0]
    row = []
    for x in (1.0, 3.0, 2*pi, 8.0):
        A = S[:-1]+0.5; B = S[1:]-0.5
        lhs = (np.exp(1j*x*A)-np.exp(1j*x*B)).sum()/(1j*x*U)
        Phi = np.exp(1j*x*S).mean()
        res = abs(lhs - (n/U)*(math.sin(x/2)/(x/2))*Phi)
        row.append((res, 2/(x*U)))
    P(f"   {name:>14}{2/U:>10.2e}" + "".join(f"{r:>11.2e}/{b:<10.2e}" for r, b in row))
P("   (each cell: residual / bound.  Every residual must be <= its bound.)")

P("\n" + "="*100)
P("D3 -- EXACT u-sampled cumulants (closed-form cell integral, zero Monte-Carlo error)")
P(f"   {'set':>14}" + "".join(f"{'j='+str(j):>12}" for j in range(2, 9)))
EX = {}
for name, f in SETS:
    g, u, S, n = load(f); U = u[-1]-u[0]
    A = S[:-1]+0.5; B = S[1:]-0.5
    raw = [0.0]*9
    for m in range(1, 9):
        raw[m] = float((A**(m+1) - B**(m+1)).sum())/((m+1)*U)
    ku = raw_to_cum(raw, 8)
    rawz = [0.0]*9
    for m in range(1, 9): rawz[m] = float((S**m).mean())
    kz = raw_to_cum(rawz, 8)
    EX[name] = (ku, kz, n)
    P(f"   {name:>14}" + "".join(f"{ku[j]-kz[j]:>12.7f}" for j in range(2, 9)))
P(f"   {'B_j/j (pred)':>14}" + "".join(f"{BERN[j]:>12.7f}" for j in range(2, 9)))
P(f"\n   {'set':>14}" + "".join(f"{'|dev| j='+str(j):>13}" for j in range(2, 9)))
worst = 0.0
for name in EX:
    ku, kz, n = EX[name]
    devs = [abs(ku[j]-kz[j]-BERN[j]) for j in range(2, 9)]
    worst = max(worst, max(devs))
    P(f"   {name:>14}" + "".join(f"{d:>13.2e}" for d in devs))
P(f"\n   D3 WORST absolute deviation from B_j/j over all sets, j=2..8 : {worst:.3e}")
P(f"   (null was > 5e-4)  ==> {'NULL REJECTED, law confirmed' if worst < 5e-4 else 'NULL HOLDS'}")

P("\n" + "="*100)
P("D4 -- random model + sawtooth vs the measured continuous-S cumulants")
K4M, K6M = -0.0017604, 0.0002276
P(f"   {'set':>14}{'k4_u meas':>12}{'model+saw':>12}{'ratio':>8}{'model only':>12}{'ratio':>8}")
for name in EX:
    ku, kz, n = EX[name]
    P(f"   {name:>14}{ku[4]:>12.5f}{K4M+BERN[4]:>12.5f}{(K4M+BERN[4])/ku[4]:>8.3f}"
      f"{K4M:>12.5f}{K4M/ku[4]:>8.3f}")
P(f"   {'':>14}{'k6_u meas':>12}{'model+saw':>12}{'ratio':>8}{'model only':>12}{'ratio':>8}")
for name in EX:
    ku, kz, n = EX[name]
    P(f"   {name:>14}{ku[6]:>12.6f}{K6M+BERN[6]:>12.6f}{(K6M+BERN[6])/ku[6]:>8.3f}"
      f"{K6M:>12.6f}{K6M/ku[6]:>8.3f}")
P("\n   NOTE, so it is not oversold: 'model+sawtooth' and 'model vs at-zeros' are THE SAME")
P("   comparison in two registers -- k4_z = k4_u - B_4/4 exactly -- so the absolute shortfall")
P("   (0.0007..0.0023) is one number, flattering in one register and not in the other.")
