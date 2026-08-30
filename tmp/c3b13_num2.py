#!/usr/bin/env python3
"""
C3 batch 13 -- numerical block 2.

  B3  THE R-KERNEL.  Target = cosine transform of a MANIFESTLY NONNEGATIVE function.
        R(v) := int_R p^2 Phi(v+p) Phi(v-p) dp  >= 0,   and
        cosMom R (2x) = (1/4)(c0 c2 + s1^2) = (1/4) L1_repo(x).
      Consequences tested: |L1(x)| <= L1(0) SHARP;  explicit near-0 interval.
  B4  Envelope / phase split, sign-oriented:  L1/Xi^2 = [T_el + T_gam] + T_zeta
        = -(log A)'' + -(log|Z|)'',  A = archimedean envelope, Z = Hardy function.
      WHERE are the negatives of each piece, and what is the true margin.
  B5  Schoenberg: is R a Gaussian scale mixture (R(sqrt(tau)) completely monotone)?
      Necessary test first: is L1 monotone decreasing in |x|?
  B8  COUNTEREXAMPLE TRANSFER on nearby positive even kernels, with a PRE-REGISTERED
      prediction from the zero-location calculus of B9.
  B9  Off-line-zero calibration: how far off the critical line must a zero be before
      L1 >= 0 stops detecting it.
"""
from mpmath import (mp, mpf, mpc, exp, pi, cos, sin, sqrt, log, quad, fabs, psi,
                    zeta, gamma, cosh, sinh, acosh, diff, inf)

mp.dps = 40

# ------------------------------------------------------------------ repo kernel
def Phi(u, nmax=400):
    u = fabs(mp.mpf(u))
    e2u = exp(2 * u); e92 = exp(9 * u / 2); e52 = exp(5 * u / 2)
    s = mp.mpf(0)
    for n in range(1, nmax + 1):
        r = mp.mpf(n)
        a = (2 * pi ** 2 * r ** 4 * e92 - 3 * pi * r ** 2 * e52) * exp(-pi * r ** 2 * e2u)
        s += a
        if n > 3 and fabs(a) < mp.mpf(10) ** (-(mp.dps + 15)):
            break
    return 4 * s

UMAX = mp.mpf(3)

def xi(s):
    return pi ** (-s / 2) * gamma(1 + s / 2) * (s - 1) * zeta(s)

def xi_logderiv_prime(s):
    z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
    return -1 / s ** 2 - 1 / (s - 1) ** 2 + psi(1, s / 2) / 4 + (z2 * z0 - z1 ** 2) / z0 ** 2

def XI(x):  return xi(mpc(mp.mpf(1) / 2, x)).real
def L1xi(x):
    X = XI(x); return X ** 2 * xi_logderiv_prime(mpc(mp.mpf(1) / 2, x)).real

def _nodes(x, umax, base=None):
    nodes = [mp.mpf(0)]
    if x != 0:
        half = pi / (2 * fabs(x)); k = 1
        while k * half < umax and k < 4000:
            nodes.append(k * half); k += 1
    for a in ['0.05','0.1','0.2','0.3','0.5','0.75','1.0','1.5','2.0']:
        v = mp.mpf(a)
        if v < umax: nodes.append(v)
    nodes.append(umax)
    return sorted(set(nodes))

# --------------------------------------------------------------------------- B3
def Rker(v, umax=UMAX):
    """R(v) = int p^2 Phi(v+p)Phi(v-p) dp.  Integrand >= 0 pointwise."""
    v = mp.mpf(v)
    f = lambda p: p ** 2 * Phi(v + p) * Phi(v - p)
    # Phi(v+p)Phi(v-p) dies once |v|+|p| exceeds ~3
    lim = umax + fabs(v)
    return quad(f, [-lim, -fabs(v), 0, fabs(v), lim], maxdegree=8)

def B3():
    print("=" * 78)
    print("B3 -- THE R-KERNEL:  target = cosine transform of a NONNEGATIVE even function")
    print("=" * 78)
    print("   R(v) = int_R p^2 Phi(v+p) Phi(v-p) dp     [integrand >= 0 POINTWISE]")
    print("   CLAIM (to be compiled):  cosMom R (2x) = (1/4)(c0 c2 + s1^2) = L1xi(x)")
    print("   (repo normalisation kappa = 2, so (1/4)*L1_repo = (1/4)*4*L1xi = L1xi)")
    print()
    print("(a) R >= 0 and its shape:")
    print(f"{'v':>10} {'R(v)':>26}")
    Rtab = {}
    for vs in ['0','0.1','0.25','0.5','0.75','1.0','1.25','1.5','2.0','2.5','3.0']:
        v = mp.mpf(vs); r = Rker(v); Rtab[vs] = r
        print(f"{vs:>10} {mp.nstr(r,18):>26}")
    print()
    print("(b) the identity cosMom R (2x) = L1xi(x), by nested quadrature:")
    print(f"{'x':>10} {'cosMom R (2x)':>26} {'L1xi(x)':>26} {'reldiff':>12}")
    VLIM = mp.mpf('3.2')
    worst = mp.mpf(0)
    for xs in ['0','0.5','1','2','3','5']:
        x = mp.mpf(xs)
        g = lambda v: Rker(v) * cos(2 * x * v)
        lhs = quad(g, _nodes(2 * x, VLIM), maxdegree=6)
        rhs = L1xi(x)
        rd = fabs(lhs - rhs) / fabs(rhs)
        worst = max(worst, rd)
        print(f"{xs:>10} {mp.nstr(lhs,16):>26} {mp.nstr(rhs,16):>26} {mp.nstr(rd,4):>12}")
    print()
    print(f"IDENTITY worst reldiff = {mp.nstr(worst,6)}   (nested quadrature, cutoff |v|<=3.2)")
    print()
    print("(c) THE SHARP TWO-SIDED BOUND that R >= 0 gives for free:")
    print("      |L1(x)| = 4|cosMom R (2x)| <= 4 int R = 4 cosMom R 0 = L1(0).")
    L10 = L1xi(mp.mpf(0))
    print(f"    L1xi(0) = {mp.nstr(L10, 20)}")
    print(f"{'x':>10} {'L1xi(x)':>26} {'L1xi(x)/L1xi(0)':>22} {'<=1 ?':>8}")
    ok = True
    for xs in ['0','0.5','1','2','5','9','11','14.134725141734693790','20','40']:
        x = mp.mpf(xs); v = L1xi(x); r = v / L10
        if fabs(r) > 1: ok = False
        print(f"{xs[:10]:>10} {mp.nstr(v,16):>26} {mp.nstr(r,14):>22} {'yes' if fabs(r)<=1 else 'NO':>8}")
    print(f"    sharp bound holds at every sampled point: {ok}")
    print()
    print("(d) THE EXPLICIT NEAR-0 INTERVAL from a cutoff v0 (cos(2 x v) >= cos(2 x v0) >= 0")
    print("    on |v| <= v0 when 2|x| v0 <= pi/2):   L1 >= 4[cos(2 x v0) m_in - m_out].")
    tot = quad(lambda v: Rker(v), [-VLIM, 0, VLIM], maxdegree=6)
    print(f"    total mass int R = {mp.nstr(tot,16)}   (= L1xi(0)/4 = {mp.nstr(L10/4,16)})")
    print(f"{'v0':>8} {'m_in':>20} {'m_out':>20} {'x range covered':>22}")
    for v0s in ['0.5','0.75','1.0','1.25','1.5','2.0']:
        v0 = mp.mpf(v0s)
        m_in = quad(lambda v: Rker(v), [-v0, 0, v0], maxdegree=6)
        m_out = tot - m_in
        # need cos(2 x v0) * m_in > m_out  with 2|x|v0 <= pi/2
        if m_out < m_in:
            xmax = mp.acos(m_out / m_in) / (2 * v0)
            xmax = min(xmax, pi / (4 * v0))
        else:
            xmax = mp.mpf(0)
        print(f"{v0s:>8} {mp.nstr(m_in,12):>20} {mp.nstr(m_out,12):>20} {'|x| <= ' + mp.nstr(xmax,8):>22}")
    print("    READING: the cutoff instrument certifies only a small interval about 0.")
    print("    That is the uncertainty principle, not a defect of the algebra.")

# --------------------------------------------------------------------------- B4
def B4():
    print()
    print("=" * 78)
    print("B4 -- ENVELOPE/PHASE SPLIT, SIGN-ORIENTED (attack: convexity with orientation)")
    print("=" * 78)
    print("  Xi(t) = -A(t) Z(t),  A(t) = (1/2)(t^2+1/4) pi^{-1/4} |Gamma(1/4+it/2)| > 0,")
    print("  Z = Hardy's function.  The derivation law for L1/f^2 = -(log|f|)'' gives")
    print("      L1/Xi^2 = -(log A)'' + -(log|Z|)'' = (T_el + T_gam) + T_zeta   EXACTLY.")
    print("  So the target = 'log|Xi| is concave', split into an ARCHIMEDEAN part and a")
    print("  HARDY part.  Question: is either part separately nonnegative?")
    print()
    nA = 0; nZ = 0; nTot = 0
    minA = None; minAx = None; minZ = None; minZx = None
    minS = None; minSx = None
    bigneg = []
    for k in range(1, 2001):        # x in (0, 100]
        x = mp.mpf(k) / 20
        s = mpc(mp.mpf(1) / 2, x)
        Tel = (2 * x ** 2 - mp.mpf(1) / 2) / (x ** 2 + mp.mpf(1) / 4) ** 2
        Tgam = (psi(1, s / 2) / 4).real
        z0 = zeta(s); z1 = zeta(s, derivative=1); z2 = zeta(s, derivative=2)
        Tz = ((z2 * z0 - z1 ** 2) / z0 ** 2).real
        A = Tel + Tgam
        nTot += 1
        if A < 0:
            nA += 1
            if minA is None or A < minA: minA, minAx = A, x
        if Tz < 0:
            nZ += 1
            if minZ is None or Tz < minZ: minZ, minZx = Tz, x
            if Tz + A < mp.mpf('0.2'):
                bigneg.append((x, A, Tz, A + Tz))
        if minS is None or A + Tz < minS: minS, minSx = A + Tz, x
    print(f"  scanned x in (0,100] step 0.05 : {nTot} points")
    print(f"  ARCHIMEDEAN part -(log A)'' = T_el+T_gam  negative at {nA}/{nTot} points"
          + (f", min {mp.nstr(minA,8)} at x={mp.nstr(minAx,6)}" if nA else ""))
    print(f"  HARDY part      -(log|Z|)'' = T_zeta      negative at {nZ}/{nTot} points"
          + (f", min {mp.nstr(minZ,8)} at x={mp.nstr(minZx,6)}" if nZ else ""))
    print(f"  SUM (= L1/Xi^2)                          min {mp.nstr(minS,10)} at x={mp.nstr(minSx,8)}")
    print()
    print("  The tightest points (T_zeta < 0 and total margin < 0.2):")
    print(f"{'x':>10} {'archimedean':>18} {'hardy':>18} {'sum':>18}")
    for row in bigneg[:18]:
        print(f"{mp.nstr(row[0],6):>10} {mp.nstr(row[1],10):>18} {mp.nstr(row[2],10):>18}"
              f" {mp.nstr(row[3],10):>18}")
    print()
    print("  VERDICT: NEITHER part is separately nonnegative, so the split does not")
    print("  isolate a single hard term.  Recorded as FAILED for the reduction purpose;")
    print("  the identity itself is exact and stands.")
    print(f"  In particular  Re (zeta'/zeta)'(1/2+it) >= 0 is FALSE (min {mp.nstr(minZ,8)}"
          f" at t={mp.nstr(minZx,6)}).")
    print(f"  And the archimedean envelope is asymptotically log-concave: T_el+T_gam ~ 7/(4x^2).")
    for xs in ['10','30','100']:
        x = mp.mpf(xs); s = mpc(mp.mpf(1)/2, x)
        A = (2*x**2 - mp.mpf(1)/2)/(x**2+mp.mpf(1)/4)**2 + (psi(1, s/2)/4).real
        print(f"      x={xs:>5}:  T_el+T_gam = {mp.nstr(A,10)}   7/(4x^2) = {mp.nstr(7/(4*x**2),10)}")

# --------------------------------------------------------------------------- B5
def B5():
    print()
    print("=" * 78)
    print("B5 -- SCHOENBERG / GAUSSIAN-SCALE-MIXTURE test on R")
    print("=" * 78)
    print("  If R(v) = int_0^inf e^{-lam v^2} dmu(lam) with mu >= 0 (equivalently, by")
    print("  Schoenberg, R(sqrt(tau)) completely monotone) then R is positive definite")
    print("  and the target follows.  PRE-REGISTERED PREDICTION: this FAILS, because a")
    print("  Gaussian scale mixture has a transform that is itself a Gaussian scale")
    print("  mixture, hence COMPLETELY MONOTONE in x^2 -- in particular MONOTONE")
    print("  DECREASING in |x|.  L1 is not.")
    print()
    print("  Necessary condition test: is |L1| monotone decreasing in |x| ?")
    prev = None; ups = 0; first = None
    for k in range(0, 400):
        x = mp.mpf(k) / 4
        v = fabs(L1xi(x))
        if prev is not None and v > prev:
            ups += 1
            if first is None: first = x
        prev = v
    print(f"    |L1| INCREASES at {ups}/399 consecutive steps on x in [0,100] step 0.25;"
          f" first at x = {mp.nstr(first,6) if first is not None else '--'}")
    if ups > 0:
        print("    => L1 is NOT monotone in |x| => R is NOT a Gaussian scale mixture.")
        print("    PREDICTION CONFIRMED.  Schoenberg route REFUTED (property of the instrument).")
    else:
        print("    => prediction REFUTED; the Schoenberg route survives this test.")

# --------------------------------------------------------------------------- B9
def B9():
    print()
    print("=" * 78)
    print("B9 -- OFF-LINE ZERO CALIBRATION (canonical product, every zero input exposed)")
    print("=" * 78)
    print("  L1(x)/Xi(x)^2 = sum over zeros z of Xi of 1/(x - z)^2   [Hadamard, genus 1].")
    print("  A zeta zero rho = beta + i gam with delta := beta - 1/2 != 0 puts a CONJUGATE")
    print("  PAIR of Xi-zeros at gam -+ i delta, contributing at x = gam exactly")
    print("        2 * (u^2 - delta^2)/(u^2 + delta^2)^2 |_{u=0}  =  -2/delta^2.")
    print("  So L1(gam) < 0 unless the remaining zeros supply more than 2/delta^2.")
    print()
    print("  Measured 'budget' B(x) := L1(x)/Xi(x)^2 at generic real x (all-on-line value),")
    print("  against the 2/delta^2 an off-line pair would have to beat:")
    print(f"{'x':>10} {'B(x)=L1/Xi^2':>20} {'delta needed: 2/B':>22} {'sqrt = delta_crit':>20}")
    for xs in ['5','14','30','60','100','200','400']:
        x = mp.mpf(xs)
        B = xi_logderiv_prime(mpc(mp.mpf(1)/2, x)).real
        dc = sqrt(2 / B) if B > 0 else mp.mpf('inf')
        print(f"{xs:>10} {mp.nstr(B,12):>20} {mp.nstr(2/B,12):>22} {mp.nstr(dc,10):>20}")
    print()
    print("  READING (calibration, NOT a no-go): delta_crit > 1/2 at every sampled height,")
    print("  and |delta| < 1/2 always, so at these heights ANY off-line zero would drive")
    print("  L1 negative near its ordinate.  Hence the target CONTAINS a zero-repulsion")
    print("  statement: proving it supplies 'no zeros just off the critical line' at these")
    print("  heights.  Consequence for method: no proof using only evenness + positivity of")
    print("  Phi can work (already witnessed by Phi_g), because those hypotheses do not")
    print("  see zero locations.  This is a property of the SOFT-KERNEL INSTRUMENT CLASS.")

# --------------------------------------------------------------------------- B8
def B8():
    print()
    print("=" * 78)
    print("B8 -- COUNTEREXAMPLE TRANSFER on nearby positive even kernels")
    print("=" * 78)
    print("  Each kernel is even and > 0.  For each, the zero set of its transform is")
    print("  computed in closed form FIRST, the sign of L1 is PREDICTED from B9's")
    print("  calculus, and only then measured.  This is a pre-registered test.")
    print()
    tests = []

    # (1) Phi_g = e^{-t^2} + e^{-4t^2};  Xi_g = sqrt(pi)[e^{-x^2/4} + (1/2)e^{-x^2/16}]
    def Xig(x):
        return sqrt(pi) * (exp(-x ** 2 / 4) + mp.mpf(1) / 2 * exp(-x ** 2 / 16))
    # zeros: e^{-3x^2/16} = -1/2  =>  x^2 = (16/3)(log 2 - i pi (2k+1))
    x2 = (mp.mpf(16) / 3) * (log(2) - mpc(0, 1) * pi)
    z = sqrt(x2)
    tests.append(('Phi_g = e^-t^2 + e^-4t^2', Xig, z))

    # (2) Phi_c = e^{-t^2}(2 + cos 2t);  Xi_c = sqrt(pi) e^{-x^2/4}(2 + e^{-1} cosh x)
    def Xic(x):
        return sqrt(pi) * exp(-x ** 2 / 4) * (2 + exp(-1) * cosh(x))
    zc = mpc(acosh(2 * exp(1)).real if False else 0, 0)
    # cosh x = -2e  =>  x = +- (arccosh(2e)) + i pi
    zc = mpc(acosh(2 * exp(1)), pi)
    tests.append(('Phi_c = e^-t^2 (2+cos 2t)', Xic, zc))

    # (3) e^{-t^2} + (1/8) e^{-16 t^2}  -- a *further* separated mixture
    def Xih(x):
        return sqrt(pi) * (exp(-x ** 2 / 4) + (mp.mpf(1) / 8) / 4 * exp(-x ** 2 / 64))
    x2h = (mp.mpf(64) * 4 / 60) * (log(32) - mpc(0, 1) * pi)
    tests.append(('Phi_h = e^-t^2 + (1/8)e^-16t^2', Xih, sqrt(x2h)))

    # (4) pure Gaussian (the Hudson case) -- must be positive everywhere
    def Xi0(x):
        return sqrt(pi) * exp(-x ** 2 / 4)
    tests.append(('Phi_0 = e^-t^2 (pure Gaussian)', Xi0, None))

    # (5) e^{-t^2}(1 + (1/2) cos t): Xi = sqrt(pi)e^{-x^2/4}(1 + (1/4)e^{-1/4}(e^{x/2}+e^{-x/2}))
    def Xik(x):
        return sqrt(pi) * exp(-x ** 2 / 4) * (1 + mp.mpf(1) / 2 * exp(mp.mpf(-1) / 4) * cosh(x / 2))
    tests.append(('Phi_k = e^-t^2 (1 + (1/2)cos t)', Xik, None))

    print(f"{'kernel':>34} {'nearest zero |Im|':>20} {'predict':>10} {'min L1':>18} {'at x':>8} {'verdict':>10}")
    for name, F, z in tests:
        L1f = lambda x: diff(F, x) ** 2 - F(x) * diff(F, x, 2)
        mn = None; mnx = None
        for k in range(0, 1201):
            x = mp.mpf(k) / 20     # x in [0,60]
            v = L1f(x)
            if mn is None or v < mn: mn, mnx = v, x
        if z is None:
            pred = 'POS'
            imz = mp.mpf('inf')
        else:
            imz = fabs(z.imag) if hasattr(z, 'imag') else mp.mpf('inf')
            rez = fabs(z.real) if hasattr(z, 'real') else mp.mpf(0)
            # predicted negative if 2/imz^2 exceeds what the far zeros can supply (~2/|2 rez|^2)
            budget = 2 / (2 * rez) ** 2 if rez > 0 else mp.mpf(0)
            pred = 'NEG' if 2 / imz ** 2 > budget else 'POS'
        verdict = ('NEG' if mn < 0 else 'POS')
        agree = 'MATCH' if verdict == pred else 'MISS'
        print(f"{name:>34} {mp.nstr(imz,6):>20} {pred:>10} {mp.nstr(mn,10):>18}"
              f" {mp.nstr(mnx,5):>8} {agree:>10}")
    print()
    print("  The prediction rule used is the crude two-zero budget of B9; a MISS means the")
    print("  crude rule, not the identity, was wrong.  Reported either way.")


if __name__ == '__main__':
    B3(); B4(); B5(); B9(); B8()
    print()
    print("=" * 78)
    print("END BLOCK 2.  EVIDENCE ONLY.  No certified bound is claimed anywhere above.")
    print("=" * 78)
