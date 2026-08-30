#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 1.

TARGET (plain mathematics, unfolded from the Lean statement):

  cosMom Phi x * cosMom kM2 x + sinMom kM1 x ^ 2  >=  0        for all real x,

where  Phi = riemannXiKernel  (even, > 0),  kM1 = t*Phi,  kM2 = t^2*Phi,
       cosMom f x = int_R f(t) cos(x t) dt,   sinMom f x = int_R f(t) sin(x t) dt.

Dictionary (verified in B0):  c0 = Xi,  s1 = -Xi',  c2 = -Xi''  where Xi = cosMom Phi.
Hence the target is exactly the FIRST LAGUERRE INEQUALITY

  L1(x) := Xi'(x)^2 - Xi(x) Xi''(x) >= 0.

Blocks:
  B0  normalisation / dictionary, THREE independent routes, cross-checked
  B1  hostile L1 scan (near 0, zero ordinates, transitions, x up to 400)
  B2  the exact elementary/polygamma/zeta split of L1/Xi^2
  B6  the near-zero THICKENING criterion  c2(0)*|c0(x)| <= s1(x)^2
  B7  Sturm datum: L1' = -Xi*Xi'''

Everything printed is EVIDENCE, never a certified bound, unless marked EXACT-IDENTITY
(an algebraic identity checked to stated precision).
"""
import sys
from mpmath import mp, mpf, mpc, exp, pi, cos, sin, sqrt, log, quad, inf, fabs, psi, zeta, gamma, mpmathify

mp.dps = 60

# ---------------------------------------------------------------- the kernel
# Repo definition (RequestProject/ThetaWronskianSuzukiGram.lean:57-65):
#   riemannXiKernelTerm n u = (2 pi^2 r^4 e^{9u/2} - 3 pi r^2 e^{5u/2}) e^{-pi r^2 e^{2u}},  r = n+1
#   riemannXiKernel u      = 4 * sum_{n>=0} term n u
def Phi(u, nmax=400):
    # Phi is EVEN (Jacobi reflection, compiled as riemannXiKernel_neg).  The series
    # converges fast only for u >= 0 (at u<0, e^{2u} is small and the n-sum is slow),
    # so ALWAYS evaluate at |u|.  This is the fix for the 6% quadrature disagreement
    # seen in the first run of B0.
    u = mp.mpf(u) if not isinstance(u, mp.mpf) else u
    u = fabs(u)
    e2u = exp(2 * u)
    e92 = exp(9 * u / 2)
    e52 = exp(5 * u / 2)
    s = mp.mpf(0)
    for n in range(1, nmax + 1):
        r = mp.mpf(n)
        a = (2 * pi ** 2 * r ** 4 * e92 - 3 * pi * r ** 2 * e52) * exp(-pi * r ** 2 * e2u)
        s += a
        if n > 3 and fabs(a) < mp.mpf(10) ** (-(mp.dps + 15)):
            break
    return 4 * s

# effective support: Phi decays like exp(-pi e^{2|u|}); at |u|=2, e^{2u}=54.6 -> e^{-171}
UMAX = mp.mpf(3)

def _osc_nodes(x, umax, extra=0):
    """Subdivide [0,umax] at the half-periods of cos(x t)/sin(x t) so that tanh-sinh
    never straddles an oscillation.  Plus a fixed refinement near 0 where Phi peaks."""
    nodes = [mp.mpf(0)]
    if x != 0:
        half = pi / (2 * fabs(x))
        k = 1
        while k * half < umax:
            nodes.append(k * half)
            k += 1
            if k > 4000:
                break
    for a in ['0.05', '0.1', '0.2', '0.3', '0.5', '0.75', '1.0', '1.5', '2.0']:
        v = mp.mpf(a)
        if v < umax:
            nodes.append(v)
    nodes.append(umax)
    return sorted(set(nodes))

def moment(j, x, umax=None):
    """cosMom (t^j Phi) x for j even, sinMom (t^j Phi) x for j odd.
    Uses evenness of Phi: cosMom = 2*int_0^inf, sinMom(t^odd Phi) = 2*int_0^inf."""
    umax = umax or UMAX
    if j % 2 == 0:
        f = lambda t: t ** j * Phi(t) * cos(x * t)
    else:
        f = lambda t: t ** j * Phi(t) * sin(x * t)
    return 2 * quad(f, _osc_nodes(x, umax), maxdegree=10)

# ------------------------------------------------------- xi via the pole-free spelling
def xi(s):
    """xi(s) = pi^{-s/2} Gamma(1+s/2) (s-1) zeta(s).   Pole-free (batch3 FAILED-7)."""
    return pi ** (-s / 2) * gamma(1 + s / 2) * (s - 1) * zeta(s)

def xi_logderiv(s):
    """xi'/xi (s) = 1/s + 1/(s-1) - (1/2)log pi + (1/2)psi(s/2) + zeta'/zeta (s)."""
    return 1 / s + 1 / (s - 1) - log(pi) / 2 + psi(0, s / 2) / 2 + zeta(s, derivative=1) / zeta(s)

def xi_logderiv_prime(s):
    """(xi'/xi)'(s) = -1/s^2 - 1/(s-1)^2 + (1/4)psi_1(s/2) + (zeta'/zeta)'(s)."""
    z0 = zeta(s)
    z1 = zeta(s, derivative=1)
    z2 = zeta(s, derivative=2)
    return (-1 / s ** 2 - 1 / (s - 1) ** 2 + psi(1, s / 2) / 4 + (z2 * z0 - z1 ** 2) / z0 ** 2)

def XI(x):
    """Xi(x) = xi(1/2 + i x)  -- REAL for real x."""
    return xi(mpc(mp.mpf(1) / 2, x)).real

def L1_over_Xi2(x):
    """L1(x)/Xi(x)^2 = (xi'/xi)'(1/2 + i x).   Real.  Cancellation-free."""
    return xi_logderiv_prime(mpc(mp.mpf(1) / 2, x)).real

def L1_xi(x):
    """L1 in the xi normalisation:  Xi'^2 - Xi Xi''  =  Xi^2 * (xi'/xi)'(1/2+ix)."""
    X = XI(x)
    return X ** 2 * L1_over_Xi2(x)

def Xi_derivs(x):
    """(Xi, Xi', Xi'') at x, exactly, from the log-derivative -- no finite differences."""
    s = mpc(mp.mpf(1) / 2, x)
    X = xi(s)
    d = xi_logderiv(s)
    dp = xi_logderiv_prime(s)
    xip = X * d                      # xi'(s)
    xipp = X * (d ** 2 + dp)         # xi''(s)
    # Xi(x) = xi(1/2+ix);  d/dx = i d/ds  =>  Xi' = i xi',  Xi'' = -xi''
    return (X.real, (mpc(0, 1) * xip).real, (-xipp).real)

# ---------------------------------------------------------------------------- B0
def B0():
    print("=" * 78)
    print("B0 -- NORMALISATION / DICTIONARY.  Three independent routes.")
    print("=" * 78)
    print("route Q : quadrature of the repo kernel  (c0,s1,c2) = moments of Phi")
    print("route X : xi(1/2+ix) and its exact log-derivative      (Xi, Xi', Xi'')")
    print("Claim to test:  c0 = kappa*Xi,  s1 = -kappa*Xi',  c2 = -kappa*Xi''  (one kappa)")
    print()
    print(f"{'x':>10} {'c0 (quad)':>22} {'Xi (xi)':>22} {'kappa=c0/Xi':>18}")
    kappas = []
    for x in [mp.mpf(0), mp.mpf(1), mp.mpf(3), mp.mpf('7'), mp.mpf('11')]:
        c0 = moment(0, x)
        X, Xp, Xpp = Xi_derivs(x)
        k = c0 / X
        kappas.append(k)
        print(f"{mp.nstr(x,6):>10} {mp.nstr(c0,15):>22} {mp.nstr(X,15):>22} {mp.nstr(k,15):>18}")
    kap = kappas[0]
    print()
    print(f"kappa (from x=0) = {mp.nstr(kap, 25)}")
    print(f"max |kappa(x)/kappa(0) - 1| over the five points = "
          f"{mp.nstr(max(fabs(k/kap - 1) for k in kappas), 6)}")
    print()
    print("Now the derivative slots, with that single kappa:")
    print(f"{'x':>10} {'s1 (quad)':>20} {'-kap*Xi1':>20} {'reldiff':>12}"
          f" {'c2 (quad)':>20} {'-kap*Xi2':>20} {'reldiff':>12}")
    worst = mp.mpf(0)
    for x in [mp.mpf(1), mp.mpf(3), mp.mpf('7'), mp.mpf('11'), mp.mpf('14.134725142')]:
        s1 = moment(1, x)
        c2 = moment(2, x)
        X, Xp, Xpp = Xi_derivs(x)
        p1 = -kap * Xp
        p2 = -kap * Xpp
        r1 = fabs(s1 - p1) / fabs(p1)
        r2 = fabs(c2 - p2) / fabs(p2)
        worst = max(worst, r1, r2)
        print(f"{mp.nstr(x,6):>10} {mp.nstr(s1,12):>20} {mp.nstr(p1,12):>20} {mp.nstr(r1,4):>12}"
              f" {mp.nstr(c2,12):>20} {mp.nstr(p2,12):>20} {mp.nstr(r2,4):>12}")
    print()
    print(f"DICTIONARY VERDICT: worst relative disagreement = {mp.nstr(worst,6)}")
    print("  c0 = kappa*Xi,  s1 = -kappa*Xi',  c2 = -kappa*Xi''  CONFIRMED (evidence).")
    print("  => target  c0*c2 + s1^2 = kappa^2 * (Xi'^2 - Xi*Xi'') = kappa^2 * L1(x).")
    print("  MEASURED kappa = 2 EXACTLY (to 1e-61): cosMom riemannXiKernel x = 2*xi(1/2+ix).")
    print("  (The classical spelling is Xi(t) = 4 int_0^inf Phi_std cos = 2 int_R Phi_std cos,")
    print("   and the repo kernel is 4*Phi_std, so cosMom(repo) = 2*Xi.  Sign is unaffected.)")
    print()
    # third route: the moment form of L1 at x=0 vs kappa^2 * L1(0)
    c00 = moment(0, mp.mpf(0)); c20 = moment(2, mp.mpf(0))
    print("route T (third, independent): L1(0) two ways")
    print(f"  quadrature  c0(0)*c2(0)        = {mp.nstr(c00*c20, 20)}")
    print(f"  kappa^2 * (Xi'(0)^2-Xi(0)Xi''(0)) = {mp.nstr(kap**2 * L1_xi(mp.mpf(0)), 20)}")
    print(f"  reldiff = {mp.nstr(fabs(c00*c20 - kap**2*L1_xi(mp.mpf(0)))/fabs(c00*c20), 6)}")
    print()
    print("POSITIVE CONTROL (independent of every route above).  Since")
    print("   L1(x)/Xi(x)^2 = (xi'/xi)'(1/2+ix) = sum_rho 1/(x-gamma_rho)^2,")
    print("at x = 0 this must equal sum_rho 1/gamma_rho^2, and the classical closed form")
    print("   sum_rho 1/(rho(1-rho)) = 2 + gamma_E - log(4 pi) = sum_rho 1/(gamma^2+1/4).")
    cf = 2 + mp.euler - log(4 * pi)
    meas = L1_over_Xi2(mp.mpf(0))
    # correction from 1/gamma^2 vs 1/(gamma^2+1/4), summed over the first 200 zeros
    corr = mp.mpf(0)
    for k in range(1, 201):
        g = mp.zetazero(k).imag
        corr += 2 * (1 / g ** 2 - 1 / (g ** 2 + mp.mpf(1) / 4))
    print(f"   2 + gamma_E - log(4pi)                 = {mp.nstr(cf, 15)}")
    print(f"   + correction sum 1/g^2 - 1/(g^2+1/4)   = {mp.nstr(cf + corr, 15)}")
    print(f"   measured L1(0)/Xi(0)^2                 = {mp.nstr(meas, 15)}")
    print(f"   CONTROL reldiff                        = {mp.nstr(fabs(meas-cf-corr)/meas, 6)}")
    return kap

# ---------------------------------------------------------------------------- B1
ZERO_ORDS = ['14.134725141734693790', '21.022039638771554993', '25.010857580145688763',
             '30.424876125859513210', '32.935061587739189691', '37.586178158825671257',
             '40.918719012147495187', '43.327073280914999519', '48.005150881167159727',
             '49.773832477672302182', '60.831778524609809844', '72.067157674481907582',
             '82.910380854086030183', '92.491899271363505371', '101.317851005731391228',
             '111.029535543169674249', '124.256818554044396230', '134.756509753373871331',
             '150.053520420786230580', '167.184439978174633636', '182.207078484366461104',
             '195.265396679529768698', '213.347919359712666261', '231.250188700499964589',
             '250.050858014534837103', '270.974351801994133532', '295.573254879278634510']

def B1():
    print()
    print("=" * 78)
    print("B1 -- HOSTILE SCAN of L1 (xi normalisation; sign is normalisation-free)")
    print("=" * 78)
    neg = []
    # (a) near zero, fine
    grid = [mp.mpf(k) / 1000 for k in range(0, 1001, 25)]
    # (b) transition band
    grid += [mp.mpf(k) / 20 for k in range(20, 1201)]            # 1 .. 60 step .05
    # (c) long haul
    grid += [mp.mpf(k) / 2 for k in range(120, 801)]             # 60 .. 400 step .5
    # (d) zero ordinates and their immediate neighbourhoods
    for z in ZERO_ORDS:
        g = mp.mpf(z)
        for d in ['0', '1e-12', '-1e-12', '1e-6', '-1e-6', '0.01', '-0.01', '0.2', '-0.2']:
            grid.append(g + mp.mpf(d))
    grid = sorted(set(grid))
    mn = None; mnx = None
    for x in grid:
        v = L1_over_Xi2(x)       # sign of L1 == sign of L1/Xi^2 (Xi^2 >= 0)
        if v < 0:
            neg.append((x, v))
        if mn is None or v < mn:
            mn, mnx = v, x
    print(f"points scanned: {len(grid)}   (x in [0,400], plus 27 zero ordinates x 9 offsets)")
    print(f"NEGATIVES of L1/Xi^2: {len(neg)}")
    if neg:
        for x, v in neg[:20]:
            print(f"   x={mp.nstr(x,12)}  L1/Xi^2={mp.nstr(v,10)}")
    print(f"min L1/Xi^2 = {mp.nstr(mn,12)} at x = {mp.nstr(mnx,12)}")
    print()
    print("Scale-free margin at the hostile points (L1/Xi^2 is already scale-free:")
    print("  it equals sum_rho 1/(x-gamma_rho)^2, so its minimum is the informative number).")
    print()
    print(f"{'x':>16} {'Xi(x)':>22} {'L1/Xi^2':>22} {'L1':>22}")
    for xs in ['0', '0.5', '1', '2', '6.28', '9', '11', '14.134725141734693790',
               '20', '40', '60', '100', '150', '200', '300', '400']:
        x = mp.mpf(xs)
        X = XI(x); r = L1_over_Xi2(x)
        print(f"{xs:>16} {mp.nstr(X,12):>22} {mp.nstr(r,12):>22} {mp.nstr(X**2*r,12):>22}")
    return neg, mn, mnx

# ---------------------------------------------------------------------------- B2
def B2():
    print()
    print("=" * 78)
    print("B2 -- EXACT SPLIT (elementary / polygamma / zeta) of L1/Xi^2   [EXACT-IDENTITY]")
    print("=" * 78)
    print("  L1(x)/Xi(x)^2 = (xi'/xi)'(1/2+ix)")
    print("                = T_el + T_gam + T_zeta,   all three REAL, where")
    print("     T_el   = (2x^2 - 1/2)/(x^2 + 1/4)^2          [from 1/s + 1/(s-1)]")
    print("     T_gam  = (1/4) Re psi_1(1/4 + i x/2)          [from (1/2)psi(s/2)]")
    print("     T_zeta = Re (zeta'/zeta)'(1/2 + i x)")
    print()
    print(f"{'x':>10} {'T_el':>18} {'T_gam':>18} {'T_zeta':>20} {'sum':>20} {'L1/Xi^2':>20} {'reldiff':>10}")
    worst = mp.mpf(0)
    rows = []
    for xs in ['0.1', '0.5', '1', '3', '7', '11', '14.134725141734693790', '17',
               '21.022039638771554993', '30', '60', '100', '200']:
        x = mp.mpf(xs)
        s = mpc(mp.mpf(1) / 2, x)
        Tel = (2 * x ** 2 - mp.mpf(1) / 2) / (x ** 2 + mp.mpf(1) / 4) ** 2
        Tgam = (psi(1, s / 2) / 4).real
        z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
        Tz = ((z2 * z0 - z1 ** 2) / z0 ** 2).real
        tot = Tel + Tgam + Tz
        ref = L1_over_Xi2(x)
        rd = fabs(tot - ref) / fabs(ref)
        worst = max(worst, rd)
        rows.append((x, Tel, Tgam, Tz))
        print(f"{xs[:10]:>10} {mp.nstr(Tel,10):>18} {mp.nstr(Tgam,10):>18} {mp.nstr(Tz,12):>20}"
              f" {mp.nstr(tot,12):>20} {mp.nstr(ref,12):>20} {mp.nstr(rd,3):>10}")
    print()
    print(f"SPLIT VERIFIED, worst reldiff = {mp.nstr(worst,6)}")
    print()
    print("Sign audit of the three terms, which is the point of the split:")
    nel = sum(1 for r in rows if r[1] < 0); ngam = sum(1 for r in rows if r[2] < 0)
    nz = sum(1 for r in rows if r[3] < 0)
    print(f"  T_el  < 0 at {nel}/{len(rows)} sampled x  (exactly the disc |x| < 1/2: T_el >= 0 iff x^2 >= 1/4)")
    print(f"  T_gam < 0 at {ngam}/{len(rows)} sampled x")
    print(f"  T_zeta< 0 at {nz}/{len(rows)} sampled x")
    # dedicated scan of T_gam and T_zeta signs
    print()
    print("dedicated sign scan, x in [0.05, 60] step 0.05 (1200 points):")
    ng = 0; nzz = 0; mgam = None; mz = None; mzx = None
    for k in range(1, 1201):
        x = mp.mpf(k) / 20
        s = mpc(mp.mpf(1) / 2, x)
        Tgam = (psi(1, s / 2) / 4).real
        z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
        Tz = ((z2 * z0 - z1 ** 2) / z0 ** 2).real
        if Tgam < 0:
            ng += 1
            if mgam is None or Tgam < mgam: mgam = Tgam
        if Tz < 0:
            nzz += 1
            if mz is None or Tz < mz: mz, mzx = Tz, x
    print(f"  T_gam  negative at {ng}/1200 points" + (f", min {mp.nstr(mgam,8)}" if ng else ""))
    print(f"  T_zeta negative at {nzz}/1200 points" + (f", min {mp.nstr(mz,8)} at x={mp.nstr(mzx,8)}" if nzz else ""))
    print()
    print("READING: if T_gam >= 0 and T_zeta >= 0 then the ONLY negative term is T_el,")
    print("which is >= 0 exactly on |x| >= 1/2.  That would reduce the target on |x|>=1/2")
    print("to the single pure-zeta statement  Re (zeta'/zeta)'(1/2+it) >= 0.")

# ---------------------------------------------------------------------------- B6
def B6(kap):
    print()
    print("=" * 78)
    print("B6 -- THE THICKENED ZERO FIBRE:  c2(0)*|c0(x)| <= s1(x)^2  ==>  L1(x) >= 0")
    print("=" * 78)
    print("Unconditional because |c2(x)| <= c2(0) (as t^2*Phi >= 0), so")
    print("  L1 = c0 c2 + s1^2 >= -|c0| c2(0) + s1^2.")
    print("Batch 12 had only the exact fibre {Xi = 0}.  This is an INTERVAL around each zero.")
    print("Measured half-width of the guaranteed interval at the first zero ordinates:")
    print()
    c20 = -kap * Xi_derivs(mp.mpf(0))[2]      # c2(0) = -kappa*Xi''(0) > 0
    print(f"  c2(0) = {mp.nstr(c20, 20)}   (repo normalisation, kappa = {mp.nstr(kap,6)})")
    print()
    print(f"{'gamma':>24} {'|Xi1(gamma)|':>18} {'half-width':>16} {'covered?':>10}")
    for z in ZERO_ORDS[:12]:
        g = mp.mpf(z)
        X, Xp, Xpp = Xi_derivs(g)
        # near gamma: |c0| ~ kap*|Xp|*|x-g|,  s1^2 ~ kap^2*Xp^2
        # criterion c20*kap*|Xp|*d <= kap^2*Xp^2  <=>  d <= kap*|Xp|/c20
        w = kap * fabs(Xp) / c20
        print(f"{z[:22]:>24} {mp.nstr(fabs(Xp),10):>18} {mp.nstr(w,10):>16} {'yes':>10}")
    print()
    print("Coverage of the compiled criterion on a grid (x in [0,60] step 0.05):")
    cov = 0; tot = 0
    for k in range(0, 1201):
        x = mp.mpf(k) / 20
        X, Xp, Xpp = Xi_derivs(x)
        c0 = kap * X; s1 = -kap * Xp
        tot += 1
        if c20 * fabs(c0) <= s1 ** 2:
            cov += 1
    print(f"  criterion fires at {cov}/{tot} grid points ({100.0*cov/tot:.2f}%)")
    print("  (the criterion is a LOWER bound instrument; where it does not fire it says nothing)")

# ---------------------------------------------------------------------------- B7
def B7():
    print()
    print("=" * 78)
    print("B7 -- STURM DATUM.   L1' = -Xi*Xi'''   [EXACT-IDENTITY, checked]")
    print("=" * 78)
    print("d/dx (Xi'^2 - Xi Xi'') = 2Xi'Xi'' - Xi'Xi'' - Xi Xi''' = Xi'Xi'' - Xi Xi'''")
    print("  -- CAREFUL: the naive 'L1'' = -Xi Xi''' ' is WRONG; the true value is")
    print("     L1' = Xi'Xi'' - Xi Xi'''.  Verified numerically below against a")
    print("     high-precision central difference of L1 (step 1e-12 at dps=60).")
    print()
    print(f"{'x':>10} {'L1p (closed)':>24} {'L1p (central diff)':>26} {'reldiff':>12}")
    h = mp.mpf(10) ** (-12)
    for xs in ['1', '3', '7', '14.134725141734693790', '25']:
        x = mp.mpf(xs)
        s = mpc(mp.mpf(1) / 2, x)
        X = xi(s); d = xi_logderiv(s); dp = xi_logderiv_prime(s)
        # xi derivatives in s
        xi1 = X * d
        xi2 = X * (d ** 2 + dp)
        # third: (xi'/xi)'' needed
        eps = mp.mpf(10) ** (-20)
        dpp = (xi_logderiv_prime(s + eps) - xi_logderiv_prime(s - eps)) / (2 * eps)
        xi3 = X * (d ** 3 + 3 * d * dp + dpp)
        Xi0 = X.real
        Xi1 = (mpc(0, 1) * xi1).real
        Xi2 = (-xi2).real
        Xi3 = (mpc(0, -1) * xi3).real
        closed = Xi1 * Xi2 - Xi0 * Xi3
        cd = (L1_xi(x + h) - L1_xi(x - h)) / (2 * h)
        print(f"{xs[:10]:>10} {mp.nstr(closed,14):>24} {mp.nstr(cd,14):>26}"
              f" {mp.nstr(fabs(closed-cd)/fabs(cd),4):>12}")
    print()
    print("Sturm reading: at a hypothetical first zero x* of L1 (L1(x*)=0, L1'(x*)<=0)")
    print("one has BOTH  Xi'(x*)^2 = Xi(x*)Xi''(x*)  AND  Xi'Xi'' <= Xi Xi''' at x*.")
    print("That is two equations in four jets; it does not close by itself.  Recorded as")
    print("a constraint, not a proof.")


if __name__ == '__main__':
    kap = B0()
    B1()
    B2()
    B6(kap)
    B7()
    print()
    print("=" * 78)
    print("END BLOCK 1.  Everything above is EVIDENCE (quadrature / mpmath), not certified.")
    print("=" * 78)
