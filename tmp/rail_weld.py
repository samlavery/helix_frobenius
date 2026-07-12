"""Rail-weld defect experiment: Sym^3(Delta) through the Adams-rail decomposition.

THE CLAIM UNDER TEST (calibration case, everything classically known):
  L(Sym^3 Delta) = L(Delta) * L(psi^3 Delta)   (exact Euler identity, Adams pair-rails)
  Rail 1 (c=1): Delta itself, kernel 2x^{11/2}e^{-2pi x}, welds EXACTLY (modularity).
  Rail psi (c=3): coefficients 2cos(3 theta_p)-multiplicative, ONE clock G_C(s+33/2),
      kernel g(x) = 2 x^{33/2} e^{-2pi x}, bank phi_psi(t) = sum lam_psi(n) g(nt).
  Weld defect:  D(t) := phi_psi(1/t) + t*phi_psi(t)      (eps_psi = eps3/eps1 = -1)
  PREDICTION (contour shift across Lambda_psi = Lambda_3/Lambda_1):
      D(t) = sum over nontrivial zeros rho of Lambda(Delta) of  R_rho * t^rho,
      R_rho = Lambda_3(rho) / Lambda_1'(rho),  absolutely convergent (~e^{-pi gamma/2}).
  With both epsilons real and level 1: R_rho real, so
      D(t) = sum_k 2 R_k t^{1/2} cos(gamma_k log t).
  ANNIHILATION: (t phi_1) star_M D = 0 because Lambda_1 vanishes on the defect's
      spectral support -- the mechanism by which the full Sym^3 weld closes.

Non-circular inputs: tau(n) from eta^24 (exact ints), Satake angles from tau(p),
Chebyshev multiplicative coefficients, incomplete-Gamma / K-Bessel quadrature.
No L-function library.
"""

import mpmath as mp
from math import comb

mp.mp.dps = 40

# ---------------------------------------------------------------- tau(n), exact
def tau_list(N):
    """tau(1..N) via Delta = q * prod_{m>=1} (1-q^m)^24, integer arithmetic."""
    c = [0] * N
    c[0] = 1
    for m in range(1, N):
        step = [0] * N
        j = 0
        while m * j < N:
            b = (-1) ** j * comb(24, j)
            for i in range(0, N - m * j):
                if c[i]:
                    step[i + m * j] += b * c[i]
            j += 1
        c = step
    return {n: c[n - 1] for n in range(1, N + 1)}  # tau(n) = coeff of q^{n-1} in prod

NMAX = 1000
TAU = tau_list(NMAX)
assert TAU[2] == -24 and TAU[3] == 252 and TAU[4] == -1472, "eta^24 sanity"

def primes(N):
    s = list(range(N + 1))
    P = []
    for p in range(2, N + 1):
        if s[p] == p:
            P.append(p)
            for q in range(p * p, N + 1, p):
                if s[q] == q:
                    s[q] = p
    return P, s  # smallest-prime-factor table

PRIMES, SPF = primes(NMAX)

# Satake angle: tau(p) = 2 p^{11/2} cos(theta_p)
THETA = {}
for p in PRIMES:
    x = mp.mpf(TAU[p]) / (2 * mp.power(p, mp.mpf(11) / 2))
    assert abs(x) < 1, f"Ramanujan violated at {p}?!"
    THETA[p] = mp.acos(x)

def cheb_lambda(phi, k):
    """U_k(cos phi) = sin((k+1)phi)/sin(phi)."""
    s = mp.sin(phi)
    if abs(s) < mp.mpf(10) ** (-25):
        return mp.mpf(k + 1) * mp.cos(phi) ** k  # phi ~ 0 or pi limit
    return mp.sin((k + 1) * phi) / s

def mult_from_local(local_lambda, N):
    """Multiplicative extension n <= N from prime-power values."""
    lam = {1: mp.mpf(1)}
    for n in range(2, N + 1):
        p = SPF[n]
        k, m = 0, n
        while m % p == 0:
            m //= p
            k += 1
        lam[n] = local_lambda(p, k) * lam[m]
    return lam

# psi^3 rail: angle 3*theta_p, degree 2
LAM_PSI = mult_from_local(lambda p, k: cheb_lambda(3 * THETA[p], k), NMAX)
# Delta rail (unitary): angle theta_p
LAM_1 = mult_from_local(lambda p, k: cheb_lambda(THETA[p], k), NMAX)
# Sym^3 coefficients via degree-4 local recursion (for Lambda_3 values)
def sym3_local(p, k):
    c1, c3 = 2 * mp.cos(THETA[p]), 2 * mp.cos(3 * THETA[p])
    # P(X) = (1 - c1 X + X^2)(1 - c3 X + X^2) = 1 - e1 X + e2 X^2 - e3 X^3 + e4 X^4
    e1 = c1 + c3
    e2 = 2 + c1 * c3
    e3 = c1 + c3
    e4 = mp.mpf(1)
    lam = [mp.mpf(1), e1, e1 * e1 - e2]
    while len(lam) <= k:
        j = len(lam)
        v = e1 * lam[j - 1] - e2 * lam[j - 2] + e3 * lam[j - 3] - (e4 * lam[j - 4] if j >= 4 else 0)
        lam.append(v)
    return lam[k]

LAM_3 = mult_from_local(sym3_local, NMAX)

# sanity: lambda_Sym3(n) = sum_{d | n} ... no simple check; verify Euler identity numerically:
# L_3(s) = L_1(s) * L_psi(s) coefficientwise: lam3 = lam1 * lam_psi (Dirichlet convolution)
def dirichlet_conv_check(n):
    s = mp.mpf(0)
    d = 1
    while d * d <= n:
        if n % d == 0:
            s += LAM_1[d] * LAM_PSI[n // d]
            if d != n // d:
                s += LAM_1[n // d] * LAM_PSI[d]
        d += 1
    return s

for n in (2, 3, 4, 6, 12, 30, 64, 210):
    assert abs(dirichlet_conv_check(n) - LAM_3[n]) < mp.mpf(10) ** (-30), f"Euler split fails at {n}"
print("[ok] Euler identity lam_Sym3 = lam_Delta * lam_psi3 (Dirichlet convolution), machine zero")

# ---------------------------------------------------------------- banks
def phi_psi(t):
    """phi_psi(t) = sum lam_psi(n) * 2 (nt)^{33/2} e^{-2 pi n t}."""
    t = mp.mpf(t)
    s = mp.mpf(0)
    for n in range(1, NMAX + 1):
        x = n * t
        term = 2 * mp.power(x, mp.mpf(33) / 2) * mp.e ** (-2 * mp.pi * x)
        if n > 40 and abs(term) < mp.mpf(10) ** (-45) * (1 + abs(s)):
            break
        s += LAM_PSI[n] * term
    return s

def phi_1(t):
    """Delta rail bank: 2 t^{11/2} sum tau_u(n) (n)^{11/2} ... = sum lam1(n) 2(nt)^{11/2} e^{-2pi nt}."""
    t = mp.mpf(t)
    s = mp.mpf(0)
    for n in range(1, NMAX + 1):
        x = n * t
        term = 2 * mp.power(x, mp.mpf(11) / 2) * mp.e ** (-2 * mp.pi * x)
        if n > 40 and abs(term) < mp.mpf(10) ** (-45) * (1 + abs(s)):
            break
        s += LAM_1[n] * term
    return s

# control: rail-1 welds exactly (modularity of Delta)
ctrl = [abs(phi_1(1 / t) - t * phi_1(t)) / abs(t * phi_1(t)) for t in (mp.mpf(1.3), mp.mpf(2.1))]
print(f"[control] Delta-rail weld defect (should be ~0): {mp.nstr(max(ctrl), 3)}")

def defect(t):
    """D(t) = phi_psi(1/t) + t phi_psi(t)   (eps_psi = -1)."""
    t = mp.mpf(t)
    return phi_psi(1 / t) + t * phi_psi(t)

# ---------------------------------------------------------------- Lambda_1 on the line
def Lambda1(s):
    """Completed L(Delta), unitary: Lambda(s) = sum_n 2 tau_u(n) [E(s,n) + E(1-s,n)],
    E(s,n) = (2 pi)^{-(s+11/2)} n^{-s} Gamma(s+11/2, 2 pi n).  (eps=+1 weld, classical.)"""
    s = mp.mpc(s)

    def E(sv, n):
        return mp.power(2 * mp.pi, -(sv + mp.mpf(11) / 2)) * mp.power(n, -sv) \
            * mp.gammainc(sv + mp.mpf(11) / 2, 2 * mp.pi * n)

    tot = mp.mpc(0)
    for n in range(1, NMAX + 1):
        tu = mp.mpf(TAU[n]) / mp.power(n, mp.mpf(11) / 2)
        if n > 30 and mp.e ** (-2 * mp.pi * n) * 1e40 < mp.mpf(10) ** (-45):
            break
        tot += 2 * tu * (E(s, n) + E(1 - s, n))
    return tot

# reality check on the line
z = Lambda1(mp.mpc(0.5, 11.0))
print(f"[check] Lambda_1(1/2+11i) = {mp.nstr(z, 8)}  (imag part should be ~0)")

def find_zeros(lo, hi, step=0.05):
    zs = []
    g = mp.mpf(lo)
    prev = mp.re(Lambda1(mp.mpc(0.5, g)))
    while g < hi:
        g2 = g + step
        cur = mp.re(Lambda1(mp.mpc(0.5, g2)))
        if prev * cur < 0:
            a, b = g, g2
            for _ in range(80):
                m = (a + b) / 2
                vm = mp.re(Lambda1(mp.mpc(0.5, m)))
                va = mp.re(Lambda1(mp.mpc(0.5, a)))
                if va * vm <= 0:
                    b = m
                else:
                    a = m
            zs.append((a + b) / 2)
        prev, g = cur, g2
    return zs

print("locating zeros of Lambda(Delta) on the line, 8 < gamma < 27 ...")
ZEROS = find_zeros(8, 27)
print("  gamma_k =", [mp.nstr(g, 10) for g in ZEROS])

# ---------------------------------------------------------------- Lambda_3 at the zeros
def Lambda3(s):
    """Completed L(Sym^3 Delta): kernel 8 x^{11} K_11(4 pi sqrt x)  (two-clock Bessel),
    Lambda_3(s) = sum lam3(n) [ H(s,n) - H(1-s,n) ]   (eps_3 = -1, classical),
    H(s,n) = n^{-s} * 16 * int_{sqrt n}^inf v^{2s+21} K_11(4 pi v) dv."""
    s = mp.mpc(s)

    def H(sv, n):
        integ = mp.quad(lambda v: mp.power(v, 2 * sv + 21) * mp.besselk(11, 4 * mp.pi * v),
                        [mp.sqrt(n), mp.sqrt(n) + 2, mp.sqrt(n) + 8, mp.inf])
        return mp.power(n, -sv) * 16 * integ

    tot = mp.mpc(0)
    for n in range(1, 220):
        if n > 25 and mp.e ** (-4 * mp.pi * mp.sqrt(n)) * 1e35 < mp.mpf(10) ** (-40):
            break
        tot += LAM_3[n] * (H(s, n) - H(1 - s, n))
    return tot

# kernel normalization gate: M[g](s) =? Gamma_C(s+11/2) Gamma_C(s+33/2)
def GammaC(s):
    return 2 * mp.power(2 * mp.pi, -s) * mp.gamma(s)

stest = mp.mpc(0.7, 0.3)
Mg = 16 * mp.quad(lambda v: mp.power(v, 2 * stest + 21) * mp.besselk(11, 4 * mp.pi * v),
                  [0, 1, 4, 10, mp.inf])
gate = abs(Mg - GammaC(stest + mp.mpf(11) / 2) * GammaC(stest + mp.mpf(33) / 2)) / abs(Mg)
print(f"[gate] two-clock kernel Mellin vs Gamma_C*Gamma_C: rel err = {mp.nstr(gate, 3)}")

def Lambda1_deriv(gamma):
    h = mp.mpf(10) ** (-8)
    return (Lambda1(mp.mpc(0.5, gamma + h)) - Lambda1(mp.mpc(0.5, gamma - h))) / (2j * h)

print("computing residues R_k = Lambda_3(rho_k)/Lambda_1'(rho_k) ...")
RES = []
for g in ZEROS:
    L3 = Lambda3(mp.mpc(0.5, g))
    L1p = Lambda1_deriv(g)
    R = L3 / L1p
    RES.append(R)
    print(f"  gamma={mp.nstr(g,8)}  Lambda3(rho)={mp.nstr(L3,6)}  Lambda1'(rho)={mp.nstr(L1p,6)}  R={mp.nstr(R,8)}")

# ---------------------------------------------------------------- THE TEST
def D_pred(t):
    t = mp.mpf(t)
    s = mp.mpf(0)
    for g, R in zip(ZEROS, RES):
        s += 2 * mp.re(R * mp.power(t, mp.mpc(0.5, g)))
    return s

print("\n===== defect vs zero-spectrum prediction =====")
print(f"{'t':>6} {'D_measured':>16} {'D_predicted':>16} {'rel.err':>10}")
grid = [mp.mpf(x) / 10 for x in range(10, 41, 3)]
scale = max(abs(defect(t)) for t in grid)
worst = mp.mpf(0)
for t in grid:
    dm, dp = defect(t), D_pred(t)
    err = abs(dm - dp) / scale
    worst = max(worst, err)
    print(f"{mp.nstr(t,3):>6} {mp.nstr(dm,10):>16} {mp.nstr(dp,10):>16} {mp.nstr(err,3):>10}")
print(f"\nWORST relative error over grid (vs max|D| = {mp.nstr(scale,6)}): {mp.nstr(worst, 4)}")
print("expected floor ~ |R at first omitted zero| / |R_1|, geometric in exp(-pi*dgamma/2)")

# ---------------------------------------------------------------- annihilation test
def conv_against_rail1(x):
    """((t phi_1) star_M D)(x) = int_0^inf (x/u) phi_1(x/u) D(u) du/u  -- should be ~ 0."""
    x = mp.mpf(x)
    return mp.quad(lambda u: (x / u) * phi_1(x / u) * defect(u) / u,
                   [mp.mpf('0.03'), mp.mpf('0.3'), 1, 3, 10, mp.mpf(45)])

print("\n===== ledgered-recombination annihilation test =====")
for x in (mp.mpf('0.8'), mp.mpf('1.5')):
    val = conv_against_rail1(x)
    ref = mp.quad(lambda u: abs((x / u) * phi_1(x / u) * defect(u) / u),
                  [mp.mpf('0.03'), mp.mpf('0.3'), 1, 3, 10, mp.mpf(45)])
    print(f"  x={mp.nstr(x,3)}: (t*phi_1) star D = {mp.nstr(val, 6)}   |integrand| mass = {mp.nstr(ref,6)}   ratio = {mp.nstr(abs(val)/ref, 3)}")
print("(ratio ~ 0 means the welded rail annihilates the defect: full Sym^3 weld closes)")
