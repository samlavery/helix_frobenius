"""ADVERSARIAL VERIFICATION of attempt 032.  Written from scratch; shares no code with
att032_*.py.  Recomputes, by an independent route:

  (A) the Davenport-Heilbronn coefficient growth  sum_{n<=x}|Lambda_DH(n)|^2 , /n , max
  (B) the two-moment separation |mu2^DH - mu2^zeta| / mu2^zeta  in units of E_T
  (C) the certificate main term 2 - mu2 for DH and its zero crossing height
  (D) the injection damping constant c and the Poisson control, against an ANALYTIC
      GUE/Montgomery prediction derived here independently
  (E) genuine precision audit of the Lambda_DH recursion (mpmath, not np.longdouble)

Stage V1 first: build DH coefficients from the CLOSED FORM tau = tan(arg(eps_chi)/2), and
verify the functional equation before trusting anything.
"""
import numpy as np, math, sys, time
import mpmath as mp

def P(*a): print(*a); sys.stdout.flush()
TMP = '/Users/samuellavery/work/helix_frobenius/tmp/'
STAGE = sys.argv[1] if len(sys.argv) > 1 else 'all'

# =====================================================================================
# V1.  DH coefficients from an INDEPENDENT closed form, gated by the functional equation.
# =====================================================================================
# chi = quartic character mod 5 with chi(2)=i.  Gauss sum tau(chi) = sum chi(n) e(n/5).
mp.mp.dps = 40
CHI = {1: mp.mpc(1), 2: mp.mpc(0, 1), 3: mp.mpc(0, -1), 4: mp.mpc(-1)}
gauss = sum(CHI[n]*mp.e**(2j*mp.pi*n/5) for n in range(1, 5))
eps = gauss/(1j*mp.sqrt(5))                     # root number of the odd character chi mod 5
TAU = mp.tan(mp.arg(eps)/2)                     # forced by  cbar/c = eps
TAU_ALT = (mp.sqrt(10 - 2*mp.sqrt(5)) - 2)/(mp.sqrt(5) - 1)   # textbook closed form
A5 = [mp.mpf(0), mp.mpf(1), TAU, -TAU, mp.mpf(-1)]            # a_n periodic mod 5


def f_dh(s):
    """f(s) = sum a_n n^{-s} = 5^{-s} sum_{r=1}^4 a_r zeta(s, r/5)."""
    s = mp.mpc(s)
    return mp.power(5, -s)*sum(A5[r]*mp.zeta(s, mp.mpf(r)/5) for r in range(1, 5))


def xi_dh(s):
    """completed:  (5/pi)^{(s+1)/2} Gamma((s+1)/2) f(s)   (odd, conductor 5)."""
    s = mp.mpc(s)
    return mp.power(5/mp.pi, (s+1)/2)*mp.gamma((s+1)/2)*f_dh(s)


def stage_V1():
    P("="*100)
    P("V1  DH coefficients, independent closed form + FUNCTIONAL-EQUATION gate")
    P("="*100)
    P(f"    root number eps(chi)      = {mp.nstr(eps, 15)}   |eps| = {mp.nstr(abs(eps),12)}")
    P(f"    tau = tan(arg eps / 2)    = {mp.nstr(TAU, 20)}")
    P(f"    textbook (sqrt(10-2sqrt5)-2)/(sqrt5-1) = {mp.nstr(TAU_ALT, 20)}")
    P(f"    |difference|              = {mp.nstr(abs(TAU-TAU_ALT), 5)}")
    # their construction, recomputed here for comparison only
    A = (4/math.sqrt(5))*math.sin(2*math.pi/5); B = (4/math.sqrt(5))*math.sin(4*math.pi/5)
    XI = (math.sqrt(A*A+B*B) - A)/B
    P(f"    record's XI (A,B route)   = {XI:.20f}   diff vs mine {abs(float(TAU)-XI):.3e}")
    P("\n    FE gate  xi(s) == xi(1-s):")
    worst = 0.0
    for s in (mp.mpc('0.3', '4.1'), mp.mpc('1.7', '11.3'), mp.mpc('0.5', '30.7'),
              mp.mpc('2.2', '0.9')):
        a, b = xi_dh(s), xi_dh(1-s)
        r = abs(a-b)/abs(a)
        worst = max(worst, float(r))
        P(f"      s = {mp.nstr(s,8):>22}   |xi(s)-xi(1-s)|/|xi| = {mp.nstr(r, 5)}")
    P(f"    worst relative FE defect = {worst:.3e}   {'PASS' if worst < 1e-25 else 'FAIL'}")
    return worst < 1e-25


# =====================================================================================
# V2.  Lambda_f by an INDEPENDENT route: explicit Dirichlet inverse, then convolution.
#      Lambda_f = (a * log) (dirichlet-conv) a^{-1}.   Their route was the in-place
#      subtractive recursion; this one materialises a^{-1} and convolves.
# =====================================================================================
def dirichlet_inverse(a, N):
    """b with (a*b)(n) = [n=1];  b[1]=1, b[n] = -sum_{d|n, d<n} b[d] a[n/d]."""
    b = np.zeros(N+1); b[1] = 1.0
    for d in range(1, N+1):
        bd = b[d]
        if bd != 0.0:
            m = np.arange(2, N//d + 1)
            if len(m):
                b[d*m] -= bd*a[m]
    return b


def lambda_via_inverse(N, a):
    """Lambda_f = (a log) * a^{-1}."""
    b = dirichlet_inverse(a, N)
    al = np.zeros(N+1)
    al[1:] = a[1:]*np.log(np.arange(1, N+1))
    Lam = np.zeros(N+1)
    for d in range(2, N+1):          # d=1 term is a_1 log 1 = 0
        v = al[d]
        if v != 0.0:
            m = np.arange(1, N//d + 1)
            Lam[d*m] += v*b[m]
    return Lam


def a_dh_array(N):
    coef = np.array([0.0, 1.0, float(TAU), -float(TAU), -1.0])
    a = coef[np.arange(N+1) % 5].copy(); a[0] = 0.0
    a[1] = 1.0
    return a


def lambda_vm(N):
    Lam = np.zeros(N+1)
    sieve = np.ones(N+1, bool); sieve[:2] = False
    for p in range(2, int(N**0.5)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    for p in np.nonzero(sieve)[0]:
        q = int(p); lp = math.log(p)
        while q <= N:
            Lam[q] = lp; q *= p
    return Lam


def lambda_mp(N, dps=50):
    """Same recursion in mpmath at dps digits -- a REAL precision audit (np.longdouble is
       IEEE double on arm64, so the record's float64-vs-float128 audit is vacuous)."""
    mp.mp.dps = dps
    coef = [mp.mpf(0), mp.mpf(1), TAU, -TAU, mp.mpf(-1)]
    a = [mp.mpf(0)]*(N+1)
    for n in range(1, N+1):
        a[n] = coef[n % 5]
    acc = [mp.mpf(0)]*(N+1)
    for n in range(1, N+1):
        acc[n] = a[n]*mp.log(n)
    Lam = [mp.mpf(0)]*(N+1)
    for k in range(2, N+1):
        v = acc[k]
        Lam[k] = v
        if v != 0:
            for m in range(2, N//k + 1):
                acc[k*m] -= v*a[m]
    return Lam


def stage_V2():
    P("\n"+"="*100)
    P("V2  Lambda_DH by an independent route (materialised Dirichlet inverse + convolution)")
    P("="*100)
    Nsm = 20000
    a = a_dh_array(Nsm)
    L_inv = lambda_via_inverse(Nsm, a)
    # record's array, for a straight comparison
    LD = np.load(TMP+'att032_lam_DH.npy')
    d = np.abs(L_inv[1:Nsm+1] - LD[1:Nsm+1])
    P(f"    my Lambda_DH (inverse route) vs record's cached array, n<=%d:" % Nsm)
    P(f"      max abs diff {d.max():.3e}   max|Lam| = {np.abs(L_inv).max():.6f}   "
      f"rel {d.max()/np.abs(L_inv[1:Nsm+1]).max():.3e}")
    # genuine precision audit
    Nmp = 4000
    t0 = time.time()
    Lmp = lambda_mp(Nmp, dps=50)
    dd = max(abs(float(Lmp[n]) - L_inv[n]) for n in range(1, Nmp+1))
    peak = max(abs(float(x)) for x in Lmp[1:Nmp+1])
    P(f"\n    GENUINE PRECISION AUDIT (mpmath dps=50 recursion, N={Nmp}, {time.time()-t0:.1f}s):")
    P(f"      max |float64 - mp50| = {dd:.3e}   peak |Lambda| = {peak:.4f}   "
      f"relative {dd/peak:.3e}")
    P(f"      [record's audit used np.longdouble, which on arm64 IS float64: "
      f"itemsize {np.dtype(np.longdouble).itemsize}, eps {np.finfo(np.longdouble).eps:.2e}]")
    # analytic gate: -f'/f at sigma=3, computed by mpmath differentiation (not finite diff)
    mp.mp.dps = 30
    for sg in (3.0, 2.5, 2.0):
        exact = mp.re(-mp.diff(lambda zz: mp.log(f_dh(zz)), mp.mpf(sg)))
        ps = float(np.sum(L_inv[1:Nsm+1]/np.arange(1, Nsm+1)**sg))
        P(f"      sigma={sg}: -f'/f = {mp.nstr(exact,12):>16}   partial sum(2e4) = {ps:.12f}"
          f"   |err| = {abs(float(exact)-ps):.3e}")
    # larger genuine-precision audit
    Nmp2 = 40000
    t0 = time.time()
    Lmp2 = lambda_mp(Nmp2, dps=40)
    a2 = a_dh_array(Nmp2)
    L_inv2 = lambda_via_inverse(Nmp2, a2)
    dd2 = max(abs(float(Lmp2[nn]) - L_inv2[nn]) for nn in range(1, Nmp2+1))
    pk2 = max(abs(float(x)) for x in Lmp2[1:Nmp2+1])
    P(f"\n    mpmath dps=40 audit at N={Nmp2} ({time.time()-t0:.1f}s): max|float64-mp| = {dd2:.3e}"
      f"   peak {pk2:.3f}   relative {dd2/pk2:.3e}")
    return L_inv


# =====================================================================================
# V3.  (A) coefficient growth   (B) separation   (C) certificate crossing
# =====================================================================================
def stage_V3(NMAX=2_600_000):
    P("\n"+"="*100)
    P("V3  (A) coefficient growth, (B) separation in E_T units, (C) certificate crossing")
    P("="*100)
    t0 = time.time()
    a = a_dh_array(NMAX)
    # direct recursion, my own implementation (vectorised over multiples, forward sweep)
    acc = np.zeros(NMAX+1)
    acc[1:] = a[1:]*np.log(np.arange(1, NMAX+1))
    LamD = np.zeros(NMAX+1)
    for k in range(2, NMAX+1):
        v = acc[k]
        LamD[k] = v
        if v != 0.0 and 2*k <= NMAX:
            acc[2*k::k] -= v*a[2:NMAX//k + 1]
    P(f"    Lambda_DH to {NMAX} built in {time.time()-t0:.1f}s")
    LamZ = lambda_vm(NMAX)
    np.save(TMP+'att032_verify_lamDH.npy', LamD)

    n = np.arange(1, NMAX+1); logn = np.log(n)
    sqD = LamD[1:]**2; sqZ = LamZ[1:]**2
    cD = np.cumsum(sqD); cZ = np.cumsum(sqZ)
    cDn = np.cumsum(sqD/n); cZn = np.cumsum(sqZ/n)
    P(f"\n    (A) growth of sum_{{n<=x}}|Lambda|^2  and  sum |Lambda|^2/n")
    P(f"    {'x':>10} {'S2_DH(x)':>14} {'slope_DH':>9} {'S2_z(x)':>14} {'slope_z':>8} "
      f"{'sum|L_DH|^2/n':>14} {'sum|L_z|^2/n':>13} {'log^2x/2':>10}")
    xs = [10**3, 10**4, 10**5, 10**6, NMAX]
    for x in xs:
        # local log-slope over [x/e, x]
        x0 = max(10, int(x/math.e))
        slD = (math.log(cD[x-1]) - math.log(cD[x0-1]))/(math.log(x)-math.log(x0))
        slZ = (math.log(cZ[x-1]) - math.log(cZ[x0-1]))/(math.log(x)-math.log(x0))
        P(f"    {x:>10} {cD[x-1]:14.4e} {slD:9.4f} {cZ[x-1]:14.4e} {slZ:8.4f} "
          f"{cDn[x-1]:14.3f} {cZn[x-1]:13.3f} {math.log(x)**2/2:10.3f}")
    P(f"    max|Lambda_DH| = {np.abs(LamD).max():.2f} at n = {int(np.argmax(np.abs(LamD)))}"
      f"     max|Lambda_zeta| = {LamZ.max():.4f}")
    P(f"    RECORD claims: sum|L_DH|^2/n = 1934.2, max = 5245, zeta 107.52 / 14.77, "
      f"slopes 1.4208/1.4193/1.4933/1.5888/1.6386")

    # ---------------- (B) separation
    def S2(Lam, X, L):
        m = n <= X
        return float(np.sum(Lam[1:][m]**2*np.maximum(L-logn[m], 0.0)/n[m]))
    P(f"\n    (B) mu_2 = l_c/L + 2 S_2/(L^2 l_c);  E_T = 1/L + (l^2+X)log l/(T l) + T^(lam/2-1)")
    P(f"    {'T':>9} {'lam':>4} {'X':>11} {'mu2 zeta':>9} {'mu2 DH':>9} {'primeZ':>8} "
      f"{'primeDH':>9} {'ratio':>7} {'E_T':>8} {'sep/E_T':>8}")
    out = {}
    for T in (1e4, 1e5, 1e6, 1e7):
        for lam in (1.0, 0.7, 0.5):
            l_z = math.log(T/(2*math.pi)); l_d = math.log(5*T/(2*math.pi))
            L = lam*l_z; X = math.exp(L)
            if X > NMAX:
                continue
            az, pz = l_z/L, 2*S2(LamZ, X, L)/(L*L*l_z)
            ad, pd = l_d/L, 2*S2(LamD, X, L)/(L*L*l_d)
            ET = 1/L + (l_z**2+X)*math.log(l_z)/(T*l_z) + T**(lam/2-1)
            sep = abs((ad+pd)-(az+pz))/(az+pz)
            out[(T, lam)] = (sep/ET, ET, az+pz, ad+pd)
            P(f"    {T:9.0e} {lam:4.1f} {X:11.4g} {az+pz:9.4f} {ad+pd:9.4f} {pz:8.4f} "
              f"{pd:9.4f} {pd/pz:7.2f} {ET:8.4f} {sep/ET:8.2f}")
    P(f"    RECORD claims sep/E_T at lam=1: 1.08 / 1.96 / 4.20 / 10.75 ; "
      f"E_T 0.1902/0.1441/0.1175/0.1000")

    # a properly LAMBDA-matched variant: L = lam * l_c of each object
    P(f"\n    (B') SAME but with L matched to EACH object's own l_c (removes the conductor")
    P(f"         artifact in the archimedean part; then arch = 1/lam for both):")
    P(f"    {'T':>9} {'lam':>4} {'mu2 zeta':>9} {'mu2 DH':>9} {'E_T':>8} {'sep/E_T':>8}")
    for T in (1e4, 1e5, 1e6, 1e7):
        for lam in (1.0,):
            l_z = math.log(T/(2*math.pi)); l_d = math.log(5*T/(2*math.pi))
            Lz = lam*l_z; Ld = lam*l_d
            Xz, Xd = math.exp(Lz), math.exp(Ld)
            if max(Xz, Xd) > NMAX:
                P(f"    {T:9.0e} {lam:4.1f}  -- X_DH = {Xd:.3g} exceeds the table --")
                continue
            m2z = l_z/Lz + 2*S2(LamZ, Xz, Lz)/(Lz*Lz*l_z)
            m2d = l_d/Ld + 2*S2(LamD, Xd, Ld)/(Ld*Ld*l_d)
            ET = 1/Lz + (l_z**2+Xz)*math.log(l_z)/(T*l_z) + T**(lam/2-1)
            P(f"    {T:9.0e} {lam:4.1f} {m2z:9.4f} {m2d:9.4f} {ET:8.4f} "
              f"{abs(m2d-m2z)/m2z/ET:8.2f}")

    # ---------------- (C) certificate
    P(f"\n    (C) certificate main term 2 - mu_2   (lam = 1)")
    def mu2(Lam, T, lam, cond):
        l = math.log(T/(2*math.pi)); lc = math.log(cond*T/(2*math.pi))
        L = lam*l; X = math.exp(L)
        return lc/L + 2*S2(Lam, X, L)/(L*L*lc)
    P(f"    {'T':>10} {'2-mu2 zeta':>12} {'2-mu2 DH':>11}")
    for T in (1e4, 3e4, 1e5, 3e5, 1e6, 3e6, 1e7):
        P(f"    {T:10.1e} {2-mu2(LamZ,T,1.0,1.0):12.4f} {2-mu2(LamD,T,1.0,5.0):11.4f}")
    from scipy.optimize import brentq
    r = brentq(lambda lT: 2 - mu2(LamD, 10**lT, 1.0, 5.0), 4.0, 7.0)
    P(f"    crossing at T = 10^{r:.4f} = {10**r:.4e}    RECORD: 1.167e6")
    return LamD, LamZ


# =====================================================================================
# V4.  the injection damping c -- independent implementation + ANALYTIC GUE prediction.
#
#   DERIVED HERE.  Move p of the N zeros from (gamma,0) [a double] to (gamma,+-y).
#   self term      : 2p L^2 [sinh^2(Ly)/(Ly)^2 - 1]                -> (p/N) Delta(y)
#   cross terms    : 4 [Re F(d-iy) - F(d)] = -2 y^2 F''(d) + O(y^4), F(x)=(sin(Lx/2)/(x/2))^2
#   sum_k F''(d_jk) has ZERO mean part (int F'' = 0) and equals the pair-correlation
#   fluctuation  rho int F''(d)(R2(rho d)-1) dd.  With R2-1 = -(sin pi w/pi w)^2 (GUE),
#   F(x) = int g(y) e^{-ixy} dy, g = (L-|y|)_+, and hat{K}(y) = -(1/rho)(1-|y|/l)_+ :
#      rho int F'' K dd = int_{-L}^{L} y^2 (L-|y|)(1-|y|/l)_+ dy =: A
#   giving      c = 1 - (1 + p/N) * 3 A / L^4.
#   For lam = L/l <= 1 :  A = 2L^4 (1/12 - lam/20)  =>  c = 1 - (1+p/N)(1/2 - 3lam/10).
#   For lam > 1 :  A = 2(L l^3/12 - l^4/20).
#   POISSON background: R2 - 1 = 0, so c = 1 exactly.
# =====================================================================================
def c_analytic(lam, pN):
    if lam <= 1:
        A_over_L4 = 2*(1/12 - lam/20)
    else:
        A_over_L4 = 2*(1/(12*lam**3) - 1/(20*lam**4))
    return 1 - (1+pN)*3*A_over_L4


def mu2_cx(rows_g, rows_b, all_g, all_b, L, chunk=300):
    tot = 0.0
    for i in range(0, len(rows_g), chunk):
        x = (rows_g[i:i+chunk][:, None]-all_g[None, :]) - 1j*(rows_b[i:i+chunk][:, None]-all_b[None, :])
        with np.errstate(divide='ignore', invalid='ignore'):
            v = np.where(np.abs(x) < 1e-13, L*L+0j, (np.sin(L*x/2.0)/(x/2.0))**2)
        tot += np.real(v).sum()
    return tot/(L*L*len(rows_g))


def measure_c(z, lam, pN, y, seed, marg=60.0):
    Na = len(z)
    l = math.log(0.5*(z[0]+z[-1])/(2*math.pi)); L = lam*l
    rng = np.random.default_rng(seed)
    npair = int(round(pN*Na))
    idx = rng.choice(Na, size=npair, replace=False)
    pg = z[idx]
    lo, hi = z[0]+marg, z[-1]-marg

    def build(yy):
        ag = np.concatenate([z, pg]); ab = np.zeros(Na+npair)
        ab[Na:] = -yy; ab[idx] = yy
        return ag, ab
    ag0, ab0 = build(0.0)
    mi = (ag0 > lo) & (ag0 < hi)
    Nr = int(mi.sum()); p_in = int(((pg > lo) & (pg < hi)).sum())
    base = mu2_cx(ag0[mi], ab0[mi], ag0, ab0, L)
    ag, ab = build(y)
    m = mu2_cx(ag[mi], ab[mi], ag, ab, L) - base
    u = L*y
    pred = (p_in/Nr)*2*((math.sinh(u)/u)**2 - 1)
    return m/pred, p_in/Nr, L


def stage_V4():
    P("\n"+"="*100)
    P("V4  the injection damping c: independent measurement vs an ANALYTIC GUE prediction")
    P("    c_pred(lam,p/N) = 1 - (1+p/N)*(1/2 - 3 lam/10)   [lam<=1]  -- pure Montgomery F(a)")
    P("="*100)
    P(f"    {'lam':>5} {'T':>8} {'p/N':>7} {'c measured':>11} {'c analytic':>11} {'ratio':>7}")
    for lam in (1.3, 1.0, 0.7, 0.5, 0.3):
        for nm in ('1e+04', '1e+06', '1e+07'):
            z = np.sort(np.load(TMP+f'att010_zeros_{nm}.npy'))
            c, frac, L = measure_c(z, lam, 1/6, 0.005, 32)
            ca = c_analytic(lam, frac)
            P(f"    {lam:5.2f} {nm:>8} {frac:7.4f} {c:11.5f} {ca:11.5f} {c/ca:7.4f}")
    P("\n    POISSON control (analytic prediction: c = 1 exactly, no pair correlation):")
    for nm in ('1e+03', '1e+05', '1e+07'):
        z = np.sort(np.load(TMP+f'att010_zeros_{nm}.npy'))
        rp = np.random.default_rng(7)
        zp = np.sort(z[0] + (z[-1]-z[0])*rp.random(len(z)))
        c, frac, L = measure_c(zp, 1.0, 1/6, 0.005, 32)
        P(f"    POISSON {nm:>8}  c = {c:.5f}   (record: 1.0187 / 1.0072 / 1.0184)")
    P("\n    p/N dependence at lam=1, T=1e6 (analytic says c grows as p/N falls):")
    z = np.sort(np.load(TMP+'att010_zeros_1e+06.npy'))
    for pN in (1/6, 1/20, 1/60):
        c, frac, L = measure_c(z, 1.0, pN, 0.005, 32)
        P(f"      p/N={pN:.4f}  c = {c:.5f}   analytic {c_analytic(1.0, frac):.5f}")


if __name__ == '__main__':
    if STAGE in ('all', 'V1'):
        stage_V1()
    if STAGE in ('all', 'V2'):
        stage_V2()
    if STAGE in ('all', 'V3'):
        stage_V3()
    if STAGE in ('all', 'V4'):
        stage_V4()


# =====================================================================================
# V5.  ATTRIBUTION.  Does DH really have zeros with sigma > 1, and where?
#      (a) abscissa of convergence of  sum Lambda_DH(n) n^{-s}  = sup Re(rho)
#      (b) independent wide-t zero hunt (my own vectorised Euler-Maclaurin Hurwitz)
# =====================================================================================
_B = [1/6, -1/30, 1/42, -1/30, 5/66, -691/2730, 7/6, -3617/510, 43867/798]

def hz(s, a, M):
    """Hurwitz zeta by Euler-Maclaurin, vectorised over complex s. 9 Bernoulli terms."""
    s = np.asarray(s, complex)
    k = np.arange(M)[:, None]
    head = np.sum(np.exp(-s[None, :]*np.log(k + a)), axis=0)
    Ma = M + a
    out = head + Ma**(1-s)/(s-1) + 0.5*Ma**(-s)
    term = s*Ma**(-s-1)
    for j in range(1, len(_B)+1):
        out = out + _B[j-1]/math.factorial(2*j)*term
        term = term*(s+2*j-1)*(s+2*j)/(Ma*Ma)
    return out


def f_vec(s):
    s = np.atleast_1d(np.asarray(s, complex))
    M = int(max(80, 4.0*np.abs(s.imag).max() + 80))
    coef = [0.0, 1.0, float(TAU), -float(TAU), -1.0]
    return 5.0**(-s)*sum(coef[r]*hz(s, r/5.0, M) for r in range(1, 5))


def stage_V5(tmax=600.0, dt=0.01):
    P("\n"+"="*100)
    P("V5  ATTRIBUTION: does f_DH have zeros with sigma > 1?")
    P("="*100)
    LamD = np.load(TMP+'att032_verify_lamDH.npy')
    NM = len(LamD)-1
    nn = np.arange(1, NM+1)
    P("    (a) partial sums of sum Lambda_DH(n) n^{-sigma}  (abscissa = sup Re rho)")
    P(f"    {'sigma':>6} {'n<=1e4':>13} {'n<=1e5':>13} {'n<=1e6':>13} {'n<=2.6e6':>13} "
      f"{'|last-prev|':>12}")
    for sg in (1.05, 1.1, 1.2, 1.3, 1.4, 1.5, 1.7, 2.0):
        ps = np.cumsum(LamD[1:]/nn**sg)
        P(f"    {sg:6.2f} {ps[9999]:13.5f} {ps[99999]:13.5f} {ps[999999]:13.5f} "
          f"{ps[NM-1]:13.5f} {abs(ps[NM-1]-ps[999999]):12.3e}")
    P("    zeta control:")
    LamZ = lambda_vm(200000)
    n2 = np.arange(1, 200001)
    for sg in (1.05, 1.2):
        ps = np.cumsum(LamZ[1:]/n2**sg)
        P(f"    {sg:6.2f} {ps[9999]:13.5f} {ps[99999]:13.5f} {ps[199999]:13.5f}")

    P(f"\n    (b) gate my Euler-Maclaurin f against mpmath:")
    mp.mp.dps = 30
    for z0 in (complex(1.2, 10.0), complex(1.05, 250.0), complex(1.3, 555.5)):
        a = f_vec(z0)[0]; b = complex(f_dh(z0))
        P(f"      s={z0}  EM {a:.10f}  mp {b:.10f}  diff {abs(a-b):.2e}")

    P(f"\n    scanning sigma-lines for deep minima of |f|, t in [0.5, {tmax}], dt={dt}")
    tt = np.arange(0.5, tmax, dt)
    cands = []
    for sg in (1.02, 1.10, 1.20, 1.30):
        vals = np.empty(len(tt))
        B = 20000
        for i in range(0, len(tt), B):
            vals[i:i+B] = np.abs(f_vec(sg + 1j*tt[i:i+B]))
        loc = np.nonzero((vals[1:-1] < vals[:-2]) & (vals[1:-1] < vals[2:]))[0]+1
        deep = loc[vals[loc] < 0.30]
        P(f"      sigma={sg:.2f}: min|f| = {vals.min():.5f} at t={tt[np.argmin(vals)]:.3f};"
          f"  {len(deep)} local minima < 0.30")
        for j in deep:
            cands.append((float(vals[j]), sg, float(tt[j])))
    cands.sort()
    P(f"    {len(cands)} candidate dips; Newton-refining the best 80 in 2D")
    mp.mp.dps = 30
    zeros = []
    for v, sg, t0 in cands[:80]:
        for s0 in (mp.mpc(sg, t0), mp.mpc(sg+0.1, t0), mp.mpc(sg+0.2, t0)):
            try:
                r = mp.findroot(f_dh, s0, tol=mp.mpf('1e-30'))
            except Exception:
                continue
            b, t = float(mp.re(r)), float(mp.im(r))
            if abs(f_dh(r)) < 1e-20 and b > 1.0 and 0 < t < tmax and \
               not any(abs(b-x) < 1e-6 and abs(t-y) < 1e-6 for x, y in zeros):
                zeros.append((b, t))
    zeros.sort(key=lambda q: q[1])
    P(f"\n    {len(zeros)} DISTINCT zeros of f_DH with sigma>1, t in (0,{tmax}):")
    for b, t in zeros[:40]:
        P(f"      beta = {b:.7f}   t = {t:.5f}")
    if zeros:
        bm = max(b for b, _ in zeros)
        P(f"    beta_max on this box = {bm:.6f}  =>  sum|c(n)|^2 ~ x^{{{2*bm-1:.4f}}}, "
          f"delta = {2*bm-2:.4f}")
        P(f"    density: {len(zeros)} zeros in t<{tmax}  ->  ~{len(zeros)/tmax:.4f} per unit t")


if __name__ == '__main__' and STAGE == 'V5':
    stage_V5()


def stage_V6():
    """V6 -- does the -f'/f series actually CONVERGE at sigma=1.05 to the true value?
       If yes, f_DH has no zeros with Re > 1.05 and the 'zeros in sigma>1' attribution
       of the measured coefficient growth is refuted in the measured range."""
    P("\n"+"="*100)
    P("V6  abscissa, decisively:  partial sums vs the TRUE -f'/f, and Psi_f(x) growth")
    P("="*100)
    LamD = np.load(TMP+'att032_verify_lamDH.npy'); NM = len(LamD)-1
    nn = np.arange(1, NM+1)
    mp.mp.dps = 30
    P(f"    {'sigma':>6} {'true -f./f':>15} {'partial sum 2.6e6':>18} {'|err|':>11} "
      f"{'max|ps(x)-limit|, x>1e4':>24}")
    for sg in (1.02, 1.05, 1.1, 1.2, 1.3, 1.5):
        exact = float(mp.re(-mp.diff(lambda zz: mp.log(f_dh(zz)), mp.mpf(sg))))
        ps = np.cumsum(LamD[1:]/nn**sg)
        swing = float(np.max(np.abs(ps[10000:] - exact)))
        P(f"    {sg:6.2f} {exact:15.8f} {ps[NM-1]:18.8f} {abs(ps[NM-1]-exact):11.2e} "
          f"{swing:24.3e}")
    P("    [a zero at beta would make the partial sums swing like x^(beta-sigma):")
    P("     beta=1.32 at sigma=1.05 would swing by x^0.27 = 54 at x=2.6e6.]")

    P(f"\n    Psi_f(x) = sum_{{n<=x}} Lambda_DH(n);  sigma_c = limsup log|Psi|/log x = sup Re rho")
    Ps = np.cumsum(LamD[1:])
    PsZ = np.cumsum(lambda_vm(NM)[1:])
    P(f"    {'x':>10} {'Psi_DH(x)':>15} {'log|Psi_DH|/log x':>18} {'Psi_zeta(x)':>14} "
      f"{'log Psi_z/log x':>16}")
    for x in (10**3, 10**4, 10**5, 10**6, NM):
        P(f"    {x:>10} {Ps[x-1]:15.4f} {math.log(abs(Ps[x-1]))/math.log(x):18.4f} "
          f"{PsZ[x-1]:14.1f} {math.log(PsZ[x-1])/math.log(x):16.4f}")
    P("    running max of log|Psi_DH(x)|/log x over x in [1e4, 2.6e6]:")
    xs = np.arange(10000, NM)
    r = np.log(np.abs(Ps[xs-1]) + 1e-300)/np.log(xs)
    P(f"      max = {r.max():.4f} at x = {int(xs[np.argmax(r)])};  value at end {r[-1]:.4f}")

    P(f"\n    where DOES the l2 growth come from?  sum_{{n<=x}}|Lam|^2 by dyadic block, and")
    P(f"    the largest |Lambda_DH(n)| and their n (are they a sparse set?)")
    sq = LamD[1:]**2
    tot = sq.sum()
    idx = np.argsort(-np.abs(LamD))[:12]
    P(f"      top |Lambda_DH(n)|: " + ", ".join(f"{abs(LamD[i]):.0f}@n={i}" for i in idx))
    cs = np.cumsum(np.sort(sq)[::-1])
    for frac in (0.5, 0.9):
        k = int(np.searchsorted(cs, frac*tot))+1
        P(f"      {frac:.0%} of sum|Lam|^2 sits on the top {k} values of n "
          f"({k/NM:.3e} of all n)")


if __name__ == '__main__' and STAGE == 'V6':
    stage_V6()


def stage_V7():
    """V7 -- (i) concentration of the DH prime-side moment; (ii) two INDEPENDENT float64
       routes at full length; (iii) conditioning of the recursion."""
    P("\n"+"="*100)
    P("V7  is the DH second-moment INPUT carried by a handful of integers?")
    P("="*100)
    LamD = np.load(TMP+'att032_verify_lamDH.npy'); NM = len(LamD)-1
    nn = np.arange(1, NM+1); ln = np.log(nn)
    for T, lam in ((1e6, 1.0), (1e7, 1.0)):
        l = math.log(T/(2*math.pi)); L = lam*l; X = math.exp(L)
        m = nn <= X
        w = LamD[1:][m]**2*np.maximum(L-ln[m], 0.0)/nn[m]
        tot = w.sum()
        srt = np.sort(w)[::-1]
        cs = np.cumsum(srt)
        k50 = int(np.searchsorted(cs, 0.5*tot))+1
        k90 = int(np.searchsorted(cs, 0.9*tot))+1
        top = np.argsort(-w)[:5]
        P(f"    T={T:.0e} lam={lam}: X={X:.4g}, S2_DH = {tot:.2f}; 50% on top {k50} n "
          f"({k50/int(X):.2e} of n<=X), 90% on top {k90}")
        P(f"       top terms n = " + ", ".join(f"{int(nn[m][i])}(w={w[i]:.2f})" for i in top))
        P(f"       removing the single largest term changes S2 by "
          f"{-100*srt[0]/tot:.2f}%, the top 10 by {-100*cs[9]/tot:.2f}%")
    P("\n    same for zeta at T=1e7, lam=1 (control):")
    LamZ = lambda_vm(NM)
    l = math.log(1e7/(2*math.pi)); L = l; X = math.exp(L)
    m = nn <= X
    w = LamZ[1:][m]**2*np.maximum(L-ln[m], 0.0)/nn[m]
    cs = np.cumsum(np.sort(w)[::-1]); tot = w.sum()
    P(f"       S2_zeta = {tot:.2f}; 50% on top {int(np.searchsorted(cs,0.5*tot))+1} n, "
      f"90% on top {int(np.searchsorted(cs,0.9*tot))+1}")

    P("\n"+"="*100)
    P("V7b TWO INDEPENDENT float64 ROUTES AT FULL LENGTH (recursion vs Dirichlet inverse)")
    P("="*100)
    t0 = time.time()
    a = a_dh_array(NM)
    Lam2 = lambda_via_inverse(NM, a)
    d = np.abs(Lam2[1:] - LamD[1:])
    P(f"    built in {time.time()-t0:.1f}s;  max abs diff {d.max():.3e} at n="
      f"{int(np.argmax(d))+1};  peak |Lambda| {np.abs(LamD).max():.2f}")
    P(f"    Lambda at the record's argmax n=2339064: recursion {LamD[2339064]:.9f}  "
      f"inverse-route {Lam2[2339064]:.9f}")
    P(f"    sum|Lam|^2/n by route: {np.sum(LamD[1:]**2/nn):.4f} vs {np.sum(Lam2[1:]**2/nn):.4f}")

    P("\n    CONDITIONING: perturb tau by 1e-13 relative and rerun the recursion")
    tp = float(TAU)*(1+1e-13)
    coef = np.array([0.0, 1.0, tp, -tp, -1.0])
    ap = coef[np.arange(NM+1) % 5].copy(); ap[0] = 0.0; ap[1] = 1.0
    acc = np.zeros(NM+1); acc[1:] = ap[1:]*np.log(np.arange(1, NM+1))
    Lp = np.zeros(NM+1)
    for k in range(2, NM+1):
        v = acc[k]; Lp[k] = v
        if v != 0.0 and 2*k <= NM:
            acc[2*k::k] -= v*ap[2:NM//k+1]
    dd = np.abs(Lp[1:]-LamD[1:])
    P(f"    max |dLambda| from a 1e-13 relative change in tau = {dd.max():.3e} "
      f"(relative to peak {dd.max()/np.abs(LamD).max():.3e})")
    P(f"    => amplification factor ~ {dd.max()/np.abs(LamD).max()/1e-13:.1f}x")


if __name__ == '__main__' and STAGE == 'V7':
    stage_V7()


def stage_V8(tmax=800.0, dt=0.02):
    """V8 -- THE REAL CAUSE of the DH coefficient growth.  Test the hypothesis that
       sum_{n<=x}|Lambda_DH|^2 ~ x^{2 beta_max - 1} with beta_max the largest real part of a
       CRITICAL-STRIP off-line zero (the classical 0.8085...), NOT a zero in sigma>1."""
    P("\n"+"="*100)
    P("V8  beta_max from the critical strip, and the growth exponent it predicts")
    P("="*100)
    mp.mp.dps = 30
    r = mp.findroot(f_dh, mp.mpc('0.808', '85.7'), tol=mp.mpf('1e-30'))
    P(f"    classical off-line DH zero: {mp.nstr(r, 15)}   |f| = {mp.nstr(abs(f_dh(r)),5)}")
    P(f"    depth y = beta - 1/2 = {float(mp.re(r))-0.5:.6f}")
    P(f"    (the record's G4b injection swept y up to 0.3085 -- the same number)")

    P(f"\n    grid hunt for off-line zeros, sigma in [0.52,1.00], t in [0.5,{tmax}]")
    tt = np.arange(0.5, tmax, dt)
    cands = []
    for sg in np.arange(0.55, 1.00, 0.05):
        vals = np.empty(len(tt)); B = 20000
        for i in range(0, len(tt), B):
            vals[i:i+B] = np.abs(f_vec(sg + 1j*tt[i:i+B]))
        loc = np.nonzero((vals[1:-1] < vals[:-2]) & (vals[1:-1] < vals[2:]))[0]+1
        deep = loc[vals[loc] < 0.06]
        for j in deep:
            cands.append((float(vals[j]), float(sg), float(tt[j])))
    cands.sort()
    P(f"    {len(cands)} dips < 0.06; refining")
    zeros = []
    for v, sg, t0 in cands[:400]:
        try:
            rr = mp.findroot(f_dh, mp.mpc(sg, t0), tol=mp.mpf('1e-28'))
        except Exception:
            continue
        b, t = float(mp.re(rr)), float(mp.im(rr))
        if abs(f_dh(rr)) < 1e-18 and 0.5 < b and 0 < t < tmax and \
           not any(abs(b-x) < 1e-6 and abs(t-y) < 1e-6 for x, y in zeros):
            zeros.append((b, t))
    zeros.sort(key=lambda q: -q[0])
    P(f"    {len(zeros)} distinct zeros with beta > 0.5, t < {tmax}.  Deepest 10:")
    for b, t in zeros[:10]:
        P(f"      beta = {b:.7f}  t = {t:.5f}   depth y = {b-0.5:.6f}")
    if zeros:
        bm = zeros[0][0]
        P(f"\n    beta_max = {bm:.6f}  =>  PREDICTED  sum_{{n<=x}}|Lambda|^2 ~ x^{{{2*bm-1:.4f}}}")
        P(f"                            and  sum|Lambda|^2/n ~ x^{{{2*bm-2:.4f}}}")
        P(f"    MEASURED local log-slope at x=2.6e6 : 1.6389   (record 1.6386)")
        P(f"    MEASURED Psi_DH growth exponent      : 0.605 (running max 0.625), "
          f"-> sigma_c should be {bm:.4f}")
        P(f"    the paper's attribution 'zeros in sigma>1' would need beta_max = "
          f"{(1.6389+1)/2:.4f}; the -f'/f series CONVERGES at sigma=1.02, excluding it.")


if __name__ == '__main__' and STAGE == 'V8':
    stage_V8()
