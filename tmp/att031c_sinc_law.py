"""ATTEMPT 031, part C -- the exact law that part B stumbled into, DERIVED and then TESTED
out of sample.

WHAT PART B SHOWED (measured, not predicted).  Comparing the two samplings of S:
    Var_t S(t) - Var_zeros S(gamma) = 0.08297, 0.08333, 0.08329, 0.08336, 0.08334, 0.08218
at the six sets.  1/12 = 0.0833333.  The four NARROW-window sets reproduce it to 4e-5.
And the fourth/sixth cumulants: kappa4_t - kappa4_z = -0.00832,-0.00834,-0.00830,-0.00833,-0.00832
(-1/120 = -0.0083333);  kappa6_t - kappa6_z = +0.003969,+0.003961,+0.003964,+0.003968,+0.003940
(1/252 = 0.0039683).  Those are Bernoulli numbers:  B_2/2, B_4/4, B_6/6.

THE DERIVATION (three lines, no probability).  On the unfolded axis u = theta/pi the counting
fluctuation is EXACTLY piecewise linear of slope -1:  for u in [u_k, u_{k+1}),  S(u) = k - 1 - u.
Its endpoint values are A_k = S_k + 1/2 (at u_k^+) and B_k = S_{k+1} - 1/2 (at u_{k+1}^-), and the
cell length is delta_k = A_k - B_k.  Hence, with U = u_n - u_1,
    <e^{i x S}>_u = (1/U) sum_k int_0^{delta_k} e^{i x (A_k - y)} dy
                  = (1/(i x U)) sum_k [ e^{i x A_k} - e^{i x B_k} ]
                  = (n/U) * ( e^{i x/2} - e^{-i x/2} )/(i x) * <e^{i x S}>_zeros  + O(1/(xU)),
the middle factor telescoping the two sums into one.  So

    ******  phi_u(x)  =  sinc(x/2) * phi_zeros(x),   sinc(z) := sin z / z   ******

i.e. S sampled continuously EQUALS S sampled at the zeros PLUS an independent uniform on
[-1/2, 1/2].  Its cumulant generating function is log(sinh(s/2)/(s/2)) = sum_m B_2m s^2m/(2m (2m)!),
so the cumulants of the added uniform are exactly kappa_2m = B_2m/(2m):
    1/12,  -1/120,  1/252,  -1/240,  1/132, ...
This is Euler-Maclaurin / Abel summation, nothing more.  NO NOVELTY IS CLAIMED: it is the
standard sawtooth identity, and the Bernoulli numbers are its signature.  What it BUYS is below.

WHY IT SETTLES THE ATTEMPT.  sinc(pi m) = 0 for every nonzero integer m.  So
    phi_u(2 pi m) = 0   EXACTLY, for every integer m,
which is why part B measured |phi_t(2 pi)| = 2e-5 .. 8e-5 (pure boundary term) against
|phi_zeros(2 pi)| = 0.060 .. 0.160.  The tau = 1 point mass K(1) -- and the whole pi/m cell
family at every integer m -- sits EXACTLY ON THE ZEROS OF THE SINC KERNEL.  It is invisible to
any continuous-in-t reading of S and is carried entirely by the discreteness of the zero
counting.  Consequently Selberg's central limit theorem, which is a statement about the
t-sampled S, does not govern K(1) directly: the two variances differ by exactly 1/12, and using
the Selberg variance in exp(-4 pi^2 V) mis-states log K by 2 pi^2/12 = pi^2/6 = 1.6449.

======================== PRE-REGISTERED BEFORE RUNNING (out of sample) ========================
Everything above was FITTED to part B's kappa_2, kappa_4, kappa_6.  The following were not
looked at and are predicted by the derivation alone:

 C1  phi_u(x) / phi_zeros(x) = sin(x/2)/(x/2) at x = 0.5, 1, 1.5, ..., 8, and at x = 2 pi.
     phi_u computed EXACTLY (closed-form cell integral, no sampling).
     NULL: relative deviation > 1e-3 at any x where |sinc(x/2)| > 0.05.
 C2  kappa_8,t - kappa_8,z = B_8/8 = -1/240 = -0.00416667   and
     kappa_10 difference = B_10/10 = (5/66)/10 = +0.00757576.
     NULL: relative deviation > 1e-2.
 C3  all ODD cumulant differences vanish.
     NULL: |kappa_3 diff| or |kappa_5 diff| > 1e-3.
 C4  the error is a BOUNDARY term of size O(1/n): halving the sample must DOUBLE the residual.
     NULL: the residual does not scale like 1/n.
 C5  the t-uniform (rather than u-uniform) reading deviates by the Jacobian dt/du = 2 pi/L only,
     so it must fail exactly on the two WIDE-ratio sets (T=1e3, ratio 6.19; long, ratio 1414)
     and hold on the four narrow ones.  This is the pre-registered explanation of why part B's
     t-uniform numbers gave 0.08297 and 0.08218 instead of 1/12.
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

def cums(x, order=10):
    m1 = x.mean(); c = x - m1
    mu = {j: float((c**j).mean()) for j in range(2, order+1)}
    k = {1: float(m1), 2: mu[2], 3: mu[3], 4: mu[4]-3*mu[2]**2, 5: mu[5]-10*mu[3]*mu[2],
         6: mu[6]-15*mu[4]*mu[2]-10*mu[3]**2+30*mu[2]**3,
         7: mu[7]-21*mu[5]*mu[2]-35*mu[4]*mu[3]+210*mu[3]*mu[2]**2,
         8: (mu[8]-28*mu[6]*mu[2]-56*mu[5]*mu[3]-35*mu[4]**2+420*mu[4]*mu[2]**2
             +560*mu[3]**2*mu[2]-630*mu[2]**4)}
    if order >= 10:
        k[9] = (mu[9]-36*mu[7]*mu[2]-84*mu[6]*mu[3]-126*mu[5]*mu[4]+756*mu[5]*mu[2]**2
                + 2520*mu[4]*mu[3]*mu[2]+560*mu[3]**3-7560*mu[3]*mu[2]**3)
        k[10] = (mu[10]-45*mu[8]*mu[2]-120*mu[7]*mu[3]-210*mu[6]*mu[4]+1260*mu[6]*mu[2]**2
                 -126*mu[5]**2+5040*mu[5]*mu[3]*mu[2]+3150*mu[4]**2*mu[2]+4200*mu[4]*mu[3]**2
                 -18900*mu[4]*mu[2]**3-37800*mu[3]**2*mu[2]**2+22680*mu[2]**5)
    return k

def load(f):
    g = np.load(os.path.join(HERE, f)); n = len(g)
    u = theta(g)/pi
    k1 = int(round(u[0]+1.5)); S = (k1+np.arange(n))-1.5-u
    sh = int(round(S.mean())); k1 -= sh; S = (k1+np.arange(n))-1.5-u
    return g, u, S, k1, n

def phi_u_exact(u, S, x):
    """<e^{i x S}>_u computed in closed form on the piecewise-linear cells: no sampling."""
    A = S[:-1] + 0.5            # value at u_k^+
    B = S[1:] - 0.5             # value at u_{k+1}^-
    U = u[-1] - u[0]
    return (np.exp(1j*x*A) - np.exp(1j*x*B)).sum()/(1j*x*U)

def S_u_samples(u, S, M, rng):
    """exact draws of S under the u-uniform measure (piecewise-linear inversion)."""
    v = rng.uniform(u[0], u[-1], M)
    j = np.searchsorted(u, v, side='right') - 1   # cell index into arrays
    return S[j] + 0.5 - (v - u[j])

P(__doc__)
rng = np.random.default_rng(777)
BERN = {2: 1/12, 4: -1/120, 6: 1/252, 8: -1/240, 10: 5/660}

P("="*100)
P("C1 -- phi_u(x) / phi_zeros(x)  vs  sinc(x/2).   phi_u by EXACT cell integration.")
XS = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0, 2*pi, 7.0, 8.0]
worst = 0.0
for name, f in SETS:
    g, u, S, k1, n = load(f)
    row = []
    for x in XS:
        pz = np.exp(1j*x*S).mean()
        pu = phi_u_exact(u, S, x)
        sc = math.sin(x/2)/(x/2)
        pred = sc*pz
        rel = abs(pu-pred)/max(abs(pred), 1e-16)
        if abs(sc) > 0.05: worst = max(worst, rel)
        row.append(rel)
    P(f"   {name:>14} n={n:5d}  max rel dev (|sinc|>0.05) = "
      f"{max(r for r, x in zip(row, XS) if abs(math.sin(x/2)/(x/2)) > 0.05):.3e}")
    P(f"   {'':>14}   per-x: " + " ".join(f"{r:.1e}" for r in row))
P(f"\n   C1 WORST over all sets and all x with |sinc|>0.05 : {worst:.3e}   "
  f"(null was >1e-3)  ==> {'NULL REJECTED' if worst < 1e-3 else 'NULL HOLDS'}")

P("\n   and at the sinc ZERO x = 2 pi (prediction: phi_u = 0 up to the O(1/U) boundary term):")
P(f"   {'set':>14}{'|phi_u(2pi)|':>15}{'|phi_z(2pi)|':>15}{'1/U':>12}{'|phi_u|*U':>12}")
for name, f in SETS:
    g, u, S, k1, n = load(f)
    U = u[-1]-u[0]
    pu = phi_u_exact(u, S, 2*pi); pz = np.exp(2j*pi*S).mean()
    P(f"   {name:>14}{abs(pu):>15.3e}{abs(pz):>15.5f}{1/U:>12.3e}{abs(pu)*U:>12.4f}")

P("\n" + "="*100)
P("C2/C3 -- cumulant differences kappa_j(u-sampled) - kappa_j(at zeros) vs B_j/j")
P(f"   {'set':>14}" + "".join(f"{'j='+str(j):>13}" for j in (2, 3, 4, 5, 6, 7, 8, 10)))
CUM = {}
for name, f in SETS:
    g, u, S, k1, n = load(f)
    Su = S_u_samples(u, S, 6_000_000, rng)
    ku = cums(Su); kz = cums(S)
    CUM[name] = (ku, kz, n)
    P(f"   {name:>14}" + "".join(f"{ku[j]-kz[j]:>13.6f}" for j in (2, 3, 4, 5, 6, 7, 8, 10)))
P(f"   {'B_j/j (pred)':>14}" + "".join(
    f"{BERN.get(j, 0.0):>13.6f}" for j in (2, 3, 4, 5, 6, 7, 8, 10)))
P("   (odd j predicted 0; MC error on the u-sample with 6e6 draws is ~1e-4 for j=2 and grows"
  "\n    steeply with j, so j=10 is reported for shape only.)")
P(f"\n   {'set':>14}{'rel err j=2':>13}{'rel err j=4':>13}{'rel err j=6':>13}{'rel err j=8':>13}")
for name in CUM:
    ku, kz, n = CUM[name]
    P(f"   {name:>14}" + "".join(f"{abs((ku[j]-kz[j])/BERN[j]-1):>13.2e}" for j in (2, 4, 6, 8)))

P("\n" + "="*100)
P("C4 -- is the residual a 1/n boundary term?  halve the sample, the residual must DOUBLE.")
P("   (using the EXACT cell integral at x=1, residual := |phi_u - sinc(1/2) phi_z| * U)")
for name, f in SETS[:5]:
    g, u, S, k1, n = load(f)
    out = []
    for frac in (1.0, 0.5, 0.25):
        m = int(n*frac)
        uu, SS = u[:m], S[:m]
        pu = phi_u_exact(uu, SS, 1.0); pz = np.exp(1j*1.0*SS).mean()
        r = abs(pu - (math.sin(0.5)/0.5)*pz)
        out.append((m, r, r*(uu[-1]-uu[0])))
    P(f"   {name:>14}  " + "   ".join(f"n={m}: res={r:.2e} (res*U={rU:.3f})" for m, r, rU in out))

P("\n" + "="*100)
P("C5 -- t-uniform vs u-uniform: the Jacobian must break the law on WIDE-ratio windows only")
P(f"   {'set':>14}{'hi/lo':>9}{'Var_t - Var_z':>15}{'Var_u - Var_z':>15}{'1/12':>10}")
for name, f in SETS:
    g, u, S, k1, n = load(f)
    tt = np.linspace(g[0], g[-1], 2_000_000)
    N = k1 - 1 + np.searchsorted(g, tt, side='right')
    St = N - theta(tt)/pi - 1.0
    Su = S_u_samples(u, S, 6_000_000, rng)
    P(f"   {name:>14}{g[-1]/g[0]:>9.3f}{St.var()-S.var():>15.6f}{Su.var()-S.var():>15.6f}{1/12:>10.6f}")

P("\n" + "="*100)
P("C6 -- consequence: what the Selberg variance would have given.  log K mis-statement = pi^2/6.")
P(f"   {'set':>14}{'V_zeros':>10}{'V_u':>10}{'V_Selberg lead':>16}{'K meas':>10}{'K from V_u':>12}{'ratio':>9}")
for name, f in SETS:
    g, u, S, k1, n = load(f)
    Tc = float(np.exp(np.log(g).mean()))
    Vz = float(S.var()); Vu = Vz + 1/12
    Vsel = math.log(math.log(Tc))/(2*pi*pi)
    K = n*abs(np.exp(-2j*pi*S).mean())**2
    Kwrong = n*math.exp(-4*pi*pi*Vu)
    P(f"   {name:>14}{Vz:>10.5f}{Vu:>10.5f}{Vsel:>16.5f}{K:>10.3f}{Kwrong:>12.4f}{K/Kwrong:>9.2f}")
P(f"   exp(4 pi^2/12) = exp(pi^2/3) = {math.exp(pi*pi/3):.4f}  -- the exact factor by which using")
P("   the continuous-in-t variance in the Gaussian formula understates K.")
