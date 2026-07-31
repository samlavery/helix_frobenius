#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
symr_pullback_weld.py -- numerics probe B: the Sym^r-pullback weld.

Construction under test (exactly as specified):
  g_z = [[y^1/2, x y^-1/2],[0, y^-1/2]] (maps i -> z), rho_r = Sym^r in the
  basis x^(r-i) y^i scaled by sqrt(C(r,i)) (the basis making Sym^r|SO(2)
  orthogonal).  Gram Q_r(z) = rho_r(g_z) rho_r(g_z)^T (det 1).
  E_r(z,s) = sum_{0 != v in Z^{r+1}} (v^T Q_r(z) v)^{-s}.
  I_r(s)   = int_F P(z) E_r(z,s) dmu,  P(z) = y^12 |Delta(z)|^2.

Instrument validation (V1, V2) is run for BOTH lattice framings:
  (scaled)   lattice Z^{r+1} in the sqrt-binomial basis, Gram Q_f = rho rho^T
             (det 1);
  (monomial) lattice Z^{r+1} in the monomial basis x^(r-i)y^i, Gram
             Q_mon = rho_mon diag(C(r,i)) rho_mon^T  (det = prod C(r,i)).
  These agree at r=1 and differ for r >= 2; both facts are MEASURED below.

PRE-REGISTERED criteria (fixed before any integral is computed; see the
"PRE-REGISTRATION" section written to the results file before the main run):
  r=1 : I_1(s) / [2 zeta(2s) (4pi)^-(s+11) Gamma(s+11) D(s)] constant in s
        to 1e-6 over >= 5 values, Re s in [3,6].
        (D(w) = sum tau(n)^2 n^-(w+11) = zeta(w) L(Sym2,w)/zeta(2w),
         analytic normalization.)
  r=2, r=3 : an identification COUNTS only if I_r(s)/candidate(s) is constant
        in s to 1e-5 over the 6-point s-grid, candidate drawn from the
        pre-registered lists only.  Anything else = measured s-dependence,
        reported as log-derivative gaps.  Post-hoc observations are labelled
        POST-HOC.

Numerical honesty: every truncation is doubled and the shift reported
(lattice cutoff, quadrature, y-cap, Euler p-cutoff).

Output: tmp/symr_pullback_weld_results.txt
"""

import math
import sys
import time

import numpy as np
import mpmath as mp

try:
    import scipy.special as sc
    HAVE_SCIPY = True
except ImportError:
    HAVE_SCIPY = False

PI = math.pi
HERE = "/Users/samuellavery/work/helix_frobenius/tmp"
OUTPATH = HERE + "/symr_pullback_weld_results.txt"
OUT = open(OUTPATH, "w")
T0 = time.time()


def rep(line=""):
    print(line, flush=True)
    OUT.write(line + "\n")
    OUT.flush()


# ----------------------------------------------------------------------------
# Section 0: exact tau(n) for n <= NTAU via eta^24 (pentagonal eta^3, then
# three exact polynomial squarings via Kronecker substitution, base 2^128).
# ----------------------------------------------------------------------------

NTAU = 20000
DIGBITS = 128
DIGB = 1 << DIGBITS
HALF = DIGB >> 1


def poly_sqr_exact(coeffs, nkeep):
    """Exact square of integer polynomial (list of ints), keep nkeep coeffs."""
    n = len(coeffs)
    pos = 0
    neg = 0
    for i in range(n - 1, -1, -1):
        pos <<= DIGBITS
        neg <<= DIGBITS
        c = coeffs[i]
        if c >= 0:
            pos += c
        else:
            neg += -c
    val = pos - neg
    v2 = val * val  # >= 0
    nout = min(2 * n - 1, nkeep)
    nb = (2 * n + 2) * (DIGBITS // 8)
    raw = v2.to_bytes(nb, "little")
    out = []
    carry = 0
    step = DIGBITS // 8
    for k in range(nout):
        d = int.from_bytes(raw[k * step:(k + 1) * step], "little") + carry
        if d >= HALF:
            out.append(d - DIGB)
            carry = 1
        else:
            out.append(d)
            carry = 0
    return out


def tau_list(N):
    """tau(1..N) exact (Python ints), tau[0] unused."""
    e3 = [0] * (N + 1)
    k = 0
    while k * (k + 1) // 2 <= N:
        e3[k * (k + 1) // 2] = (-1) ** k * (2 * k + 1)
        k += 1
    e6 = poly_sqr_exact(e3, N + 1)
    e12 = poly_sqr_exact(e6, N + 1)
    e24 = poly_sqr_exact(e12, N + 1)
    tau = [0] * (N + 1)
    for n in range(1, N + 1):
        tau[n] = e24[n - 1]
    return tau


rep("=" * 78)
rep("Sym^r-pullback weld probe  (numerics probe B)  " + time.strftime("%Y-%m-%d %H:%M"))
rep("=" * 78)
rep("")
rep("[S0] exact tau(n), n <= %d (eta^3 pentagonal -> 3 exact Kronecker squarings)" % NTAU)
TAU = tau_list(NTAU)
_tau_known = {1: 1, 2: -24, 3: 252, 4: -1472, 5: 4830, 6: -6048, 7: -16744,
              10: -115920, 25: -25499225}
ok = all(TAU[n] == v for n, v in _tau_known.items())
# Hecke relations as independent structural validation
ok = ok and TAU[2] * TAU[3] == TAU[6] and TAU[3] * TAU[8] == TAU[24] \
    and TAU[5] ** 2 - 5 ** 11 == TAU[25] \
    and TAU[2] * TAU[16] - 2 ** 11 * TAU[8] == TAU[32] \
    and TAU[7] * TAU[9] == TAU[63]
rep("  tau spot-check (known values + Hecke relations at 6,24,25,32,63): %s"
    % ("PASS" if ok else "FAIL"))
if not ok:
    rep("  ABORT: tau computation wrong");  sys.exit(1)


def sieve_primes(N):
    m = np.ones(N + 1, bool); m[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if m[p]:
            m[p * p::p] = False
    return np.nonzero(m)[0]


PRIMES = sieve_primes(NTAU)
_lam_p = np.array([float(TAU[p]) / p ** 5.5 for p in PRIMES])
deligne_viol = int(np.sum(np.abs(_lam_p) > 2.0))
rep("  Deligne bound |tau(p)| <= 2 p^{11/2} on all %d primes <= %d: violations = %d"
    % (len(PRIMES), NTAU, deligne_viol))
THETA_P = np.arccos(np.clip(_lam_p / 2.0, -1.0, 1.0))
rep("  max |lambda(p)/2| = %.6f  (Satake angles well-defined)" % np.max(np.abs(_lam_p / 2)))
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 1: representations rho_r (monomial and scaled bases)
# ----------------------------------------------------------------------------


def rho_mon(g, r):
    """Sym^r of g=[[a,b],[c,d]] in monomial basis e1^(r-j) e2^j (columns j)."""
    a, b, c, d = g[0][0], g[0][1], g[1][0], g[1][1]
    n = r + 1
    M = np.zeros((n, n))
    for j in range(n):
        p1 = np.array([math.comb(r - j, k) * a ** (r - j - k) * c ** k
                       for k in range(r - j + 1)])
        p2 = np.array([math.comb(j, l) * b ** (j - l) * d ** l
                       for l in range(j + 1)])
        M[:, j] = np.convolve(p1, p2)
    return M


def binom_diag(r):
    return np.array([math.comb(r, i) for i in range(r + 1)], dtype=float)


def rho_scaled(g, r):
    Sd = np.sqrt(binom_diag(r))
    return rho_mon(g, r) / Sd[:, None] * Sd[None, :]


def g_of_z(x, y):
    sy = math.sqrt(y)
    return [[sy, x / sy], [0.0, 1.0 / sy]]


def Q_mon(x, y, r):
    R = rho_mon(g_of_z(x, y), r)
    return (R * binom_diag(r)[None, :]) @ R.T


def Q_scaled(x, y, r):
    R = rho_scaled(g_of_z(x, y), r)
    return R @ R.T


S_MAT = [[0.0, -1.0], [1.0, 0.0]]
T_MAT = [[1.0, 1.0], [0.0, 1.0]]

rep("[S1] representation checks")
for r in (2, 3):
    for nm, gg in (("S", S_MAT), ("T", T_MAT)):
        Mm = rho_mon(gg, r)
        Ms = rho_scaled(gg, r)
        int_m = np.max(np.abs(Mm - np.round(Mm)))
        int_s = np.max(np.abs(Ms - np.round(Ms)))
        rep("  r=%d gamma=%s : rho_MONOMIAL integer-dev %.2e (det %+0.f) | "
            "rho_SCALED integer-dev %.3f" % (r, nm, int_m, np.linalg.det(Mm), int_s))
rep("  -> rho_scaled(T) r=2 matrix:")
for row in rho_scaled(T_MAT, 2):
    rep("       [%s]" % "  ".join("%+.6f" % v for v in row))
th0 = 0.7345
K0 = [[math.cos(th0), -math.sin(th0)], [math.sin(th0), math.cos(th0)]]
for r in (2, 3):
    Rk = rho_scaled(K0, r)
    rep("  r=%d rho_scaled(SO(2), th=%.4f) orthogonality |R R^T - I|_max = %.2e"
        % (r, th0, np.max(np.abs(Rk @ Rk.T - np.eye(r + 1)))))
    rep("  r=%d det Q_scaled(z0) - 1 = %.2e ; det Q_mon(z0) = %.12f (prod C(r,i) = %d)"
        % (r, np.linalg.det(Q_scaled(0.13, 0.91, r)) - 1.0,
           np.linalg.det(Q_mon(0.13, 0.91, r)), int(np.prod(binom_diag(r)))))
rep("")

# ----------------------------------------------------------------------------
# Section 2: lattice enumeration + Epstein zeta via incomplete-gamma formula
# ----------------------------------------------------------------------------


def enumerate_norms(Q, B, want_vecs=False):
    """All 0 != v in Z^n with v^T Q v <= B; returns array of norms (and vecs)."""
    n = Q.shape[0]
    L = np.linalg.cholesky(Q)
    R = L.T  # upper triangular, v^T Q v = ||R v||^2
    V = np.zeros((1, n))
    Tp = np.zeros((1, n))
    rem = np.array([float(B)])
    for i in range(n - 1, -1, -1):
        sq = np.sqrt(np.maximum(rem, 0.0))
        lo = np.ceil((-sq - Tp[:, i]) / R[i, i] - 1e-12).astype(np.int64)
        hi = np.floor((sq - Tp[:, i]) / R[i, i] + 1e-12).astype(np.int64)
        cnt = np.maximum(hi - lo + 1, 0)
        tot = int(cnt.sum())
        if tot == 0:
            return (np.zeros(0), np.zeros((0, n), dtype=np.int64)) if want_vecs else np.zeros(0)
        idx = np.repeat(np.arange(len(rem)), cnt)
        starts = np.concatenate(([0], np.cumsum(cnt)[:-1]))
        offs = np.arange(tot) - np.repeat(starts, cnt)
        vals = (lo[idx] + offs).astype(float)
        yi = R[i, i] * vals + Tp[idx, i]
        V = V[idx]; V[:, i] = vals
        Tp = Tp[idx] + vals[:, None] * R[:, i][None, :]
        rem = rem[idx] - yi ** 2
        keep = rem >= -1e-9
        V, Tp, rem = V[keep], Tp[keep], rem[keep]
    Vi = np.round(V).astype(np.int64)
    N = np.einsum("ij,jk,ik->i", V, Q, V)
    mask = np.any(Vi != 0, axis=1)
    if want_vecs:
        return N[mask], Vi[mask]
    return N[mask]


def upper_gamma(a, x):
    """Gamma(a, x) for scalar real a (any sign, non-integer if a<=0), x array>0."""
    x = np.asarray(x, dtype=float)
    if a > 0:
        return sc.gammaincc(a, x) * math.gamma(a)
    m = math.floor(-a) + 1
    a0 = a + m  # in (0,1]
    assert a0 > 1e-9, "a too close to non-positive integer"
    G = sc.gammaincc(a0, x) * math.gamma(a0)
    ex = np.exp(-x)
    ac = a0
    for _ in range(m):
        ac -= 1.0
        G = (G - x ** ac * ex) / ac
    return G


def epstein(Q, s, B=36.0):
    """E_Q(s) by the incomplete-gamma (Riemann/Terras) representation."""
    n = Q.shape[0]
    det = np.linalg.det(Q)
    Qi = np.linalg.inv(Q); Qi = 0.5 * (Qi + Qi.T)
    N = enumerate_norms(Q, B)
    Ns = enumerate_norms(Qi, B)
    x1 = PI * N
    S1 = float(np.sum(upper_gamma(s, x1) * x1 ** (-s)))
    a = 0.5 * n - s
    x2 = PI * Ns
    S2 = float(np.sum(upper_gamma(a, x2) * x2 ** (-a)))
    lam = S1 + S2 / math.sqrt(det) + 1.0 / (math.sqrt(det) * (s - 0.5 * n)) - 1.0 / s
    return PI ** s / math.gamma(s) * lam


rep("[S2] Epstein machinery validation")
# (a) incomplete gamma vs mpmath
rng = np.random.default_rng(7)
maxrel = 0.0
for a in (-4.4, -3.65, -1.6, -0.9, 0.4, 1.0, 3.1, 5.65):
    xs = 10.0 ** rng.uniform(-3.5, 1.6, 12)
    got = upper_gamma(a, xs)
    for xx, gg in zip(xs, got):
        ref = float(mp.gammainc(a, xx, mp.inf))
        maxrel = max(maxrel, abs(gg - ref) / abs(ref))
rep("  upper_gamma vs mpmath.gammainc over a in [-4.4, 5.65], x in [3e-4, 40]: "
    "max rel err = %.2e" % maxrel)

# (b) enumeration vs brute-force box
z0x, z0y = 0.234, 1.077
for r in (2, 3):
    Q = Q_mon(z0x, z0y, r)
    B = 25.0
    N1 = np.sort(enumerate_norms(Q, B))
    Qi = np.linalg.inv(Q)
    ext = np.sqrt(B * np.diag(Qi)).astype(int) + 2
    grids = np.meshgrid(*[np.arange(-e, e + 1) for e in ext], indexing="ij")
    Vb = np.stack([g.ravel() for g in grids], axis=1).astype(float)
    Nb = np.einsum("ij,jk,ik->i", Vb, Q, Vb)
    Nb = np.sort(Nb[(Nb <= B) & (Nb > 1e-12)])
    same = len(N1) == len(Nb) and np.max(np.abs(N1 - Nb)) < 1e-8
    rep("  r=%d enumeration vs brute box (B=%.0f): %d pts, match=%s" %
        (r, B, len(N1), same))

# (c) Epstein formula vs direct lattice sum at large s
for r, Bdir in ((1, 4000.0), (2, 700.0), (3, 260.0)):
    Q = Q_mon(z0x, z0y, r)
    s_test = 6.1
    Ef = epstein(Q, s_test)
    Nd = enumerate_norms(Q, Bdir)
    Ed = float(np.sum(Nd ** (-s_test)))
    n = r + 1
    Vn = PI ** (n / 2) / math.gamma(n / 2 + 1)
    tail = Vn / math.sqrt(np.linalg.det(Q)) * (n / 2) * Bdir ** (n / 2 - s_test) \
        / (s_test - n / 2)
    rep("  r=%d E(z0,s=6.1): formula=%.12e direct=%.12e  rel diff=%.2e (tail est %.1e)"
        % (r, Ef, Ed, abs(Ef - Ed) / abs(Ef), tail / Ed))
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 3: V1 (SL2(Z)-invariance) and V2 (Poisson self-duality) -- MEASURED
# for both lattice framings.
# ----------------------------------------------------------------------------

rep("[S3] V1: SL2(Z)-invariance of E_r(z,s)  (s=3.3, two z test points)")


def mobius(g, z):
    a, b = g[0]; c, d = g[1]
    return (a * z + b) / (c * z + d)


for r in (2, 3):
    for zx, zy in ((0.13, 0.77), (-0.21, 1.13)):
        z = complex(zx, zy)
        s = 3.3
        for tag, Qfun in (("monomial", Q_mon), ("scaled  ", Q_scaled)):
            Ez = epstein(Qfun(z.real, z.imag, r), s)
            zS = mobius(S_MAT, z); zT = mobius(T_MAT, z)
            ES = epstein(Qfun(zS.real, zS.imag, r), s)
            ET = epstein(Qfun(zT.real, zT.imag, r), s)
            rep("  r=%d z=%+.2f%+.2fi [%s]  relΔ(S)=%.2e  relΔ(T)=%.2e"
                % (r, zx, zy, tag, abs(ES - Ez) / abs(Ez), abs(ET - Ez) / abs(Ez)))
rep("  (r=1 control) both framings coincide:")
z = complex(0.13, 0.77); s = 3.3
E1 = epstein(Q_mon(z.real, z.imag, 1), s)
zS = mobius(S_MAT, z); zT = mobius(T_MAT, z)
rep("  r=1 relΔ(S)=%.2e relΔ(T)=%.2e"
    % (abs(epstein(Q_mon(zS.real, zS.imag, 1), s) - E1) / E1,
       abs(epstein(Q_mon(zT.real, zT.imag, 1), s) - E1) / E1))
rep("")

rep("[S3] V2: Poisson duality of theta_Q(t) = sum exp(-pi t v^T Q v)")


def theta_lat(Q, t, tol=1e-18):
    B = -math.log(tol) / (PI * t)
    N = enumerate_norms(Q, B)
    return 1.0 + float(np.sum(np.exp(-PI * t * N)))


for r in (1, 2, 3):
    n = r + 1
    Qs = Q_scaled(0.234, 1.077, r)
    Qm = Q_mon(0.234, 1.077, r)
    det_m = np.linalg.det(Qm)
    for t in (0.73, 1.41):
        lhs = theta_lat(Qs, 1.0 / t)
        rhs = t ** (n / 2) * theta_lat(Qs, t)
        rep("  r=%d t=%.2f SCALED (det 1):    theta(1/t) vs t^{n/2} theta(t): rel dev %.2e"
            % (r, t, abs(lhs - rhs) / abs(lhs)))
        lhs = theta_lat(Qm, 1.0 / t)
        rhs_self = t ** (n / 2) * theta_lat(Qm, t)
        rhs_dual = t ** (n / 2) / math.sqrt(det_m) * theta_lat(np.linalg.inv(Qm), t)
        rep("  r=%d t=%.2f MONOMIAL (det %g): naive self-dual dev %.2e ; "
            "det^-1/2-twisted dual dev %.2e"
            % (r, t, det_m, abs(lhs - rhs_self) / abs(lhs),
               abs(lhs - rhs_dual) / abs(lhs)))
# structural: dual of scaled Gram is signed-permutation equivalent
for r in (2, 3):
    Qs = Q_scaled(0.234, 1.077, r)
    O = rho_scaled(S_MAT, r)  # rho_scaled(J), J in SO(2): signed permutation
    dev = np.max(np.abs(np.linalg.inv(Qs) - O @ Qs @ O.T))
    rep("  r=%d structural: Q_scaled^-1 = rho_scaled(J) Q_scaled rho_scaled(J)^T, "
        "max dev %.2e (J = signed permutation)" % (r, dev))
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# PRE-REGISTRATION (written before any I_r value is computed)
# ----------------------------------------------------------------------------

SBASE = [3.1, 3.6, 4.1, 4.6, 5.1, 5.6]
DS = 0.05
SALL = SBASE + [s + DS for s in SBASE]

rep("[PRE-REGISTRATION]  (fixed before the main run)")
rep("  s-grid: %s  (+%.2f partners for log-derivatives)" % (SBASE, DS))
rep("  main-run lattice framing: MONOMIAL (the SL2(Z)-invariant one; the")
rep("  integral over F is only well-defined for the invariant object).")
rep("  Notation: Z(w)=zeta(w); G(w)=(4pi)^-w Gamma(w); L2/L3/LD = analytic-")
rep("  normalized L(Sym^2 Delta, w), L(Sym^3 Delta, w), L(Delta, w) via Satake")
rep("  Euler products p <= 1e4; D(w) = Z(w) L2(w)/Z(2w) = sum lam(n)^2 n^-w.")
rep("  r=1 SANITY: I_1(s) = 2 Z(2s) G(s+11) D(s) exactly (classical unfolding);")
rep("    criterion: ratio constant AND equal to 1 to 1e-6 over the 6 s-values.")
CANDS2_TXT = [
    "2A: Z(2s) G(2s+11) D(2s)",
    "2B: Z(2s-1) G(2s+10) D(2s-1)",
    "2C: Z(2s) G(2s+11) L2(2s)",
    "2D: Z(2s-1) G(2s+10) L2(2s-1)",
    "2E: Z(2s) Z(2s-1) G(2s+10) L2(2s-1)",
    "2F: Z(2s-1) G(s+11) (Gamma(s-1/2)/Gamma(s)) L2(2s-1)",
    "2G: Z(2s-1) G(s+11) L2(s)",
    "2H: Z(2s) G(s+11) L2(s+1/2)",
    "2I: measured I_1(s)  (pure rung-1 proportionality)",
    "2J: Z(2s) Z(2s-1) G(2s+11) D(2s)",
]
CANDS3_TXT = [
    "3A: Z(2s) G(2s+11) L3(2s)",
    "3B: Z(2s-1) G(2s+10) L3(2s-1)",
    "3C: Z(2s) G(2s+11) LD(2s) LD(2s-1)",
    "3D: Z(2s-1) G(2s+10) LD(2s-1)^2",
    "3E: Z(2s) Z(2s-2) G(2s+10) L3(2s-1)",
    "3F: Z(2s-1) G(s+11) L3(s+1/2)",
    "3G: Z(2s-2) G(2s+10) D(2s-1)",
    "3H: measured I_1(s)",
    "3I: measured I_2(s)",
    "3J: Z(2s) G(2s+11) D(2s)",
]
rep("  r=2 candidate list (identification iff ratio dev <= 1e-5):")
for c in CANDS2_TXT:
    rep("    " + c)
rep("  r=3 candidate list (identification iff ratio dev <= 1e-5):")
for c in CANDS3_TXT:
    rep("    " + c)
rep("  dev metric: (max R - min R)/|mean R| over the 6 base s-values.")
rep("")

# ----------------------------------------------------------------------------
# Section 4: main run -- build grid, store lattice norms, compute I_r(s)
# ----------------------------------------------------------------------------

NTAU_DELTA = 60
TAU_F = np.array([0.0] + [float(TAU[n]) for n in range(1, NTAU_DELTA + 1)])


def build_grid(nx, ny, ymax):
    xg, wxg = np.polynomial.legendre.leggauss(nx)
    yg, wyg = np.polynomial.legendre.leggauss(ny)
    xs = 0.5 * xg; wxs = 0.5 * wxg
    X, Y, WQ = [], [], []
    for x, wx in zip(xs, wxs):
        y0 = math.sqrt(1.0 - x * x)
        ys = 0.5 * (ymax + y0) + 0.5 * (ymax - y0) * yg
        wys = 0.5 * (ymax - y0) * wyg
        X.extend([x] * ny); Y.extend(ys); WQ.extend(wx * wys)
    X = np.array(X); Y = np.array(Y); WQ = np.array(WQ)
    q = np.exp(2j * PI * (X + 1j * Y))
    Delta = np.zeros(len(X), complex)
    qp = np.ones(len(X), complex)
    for n in range(1, NTAU_DELTA + 1):
        qp = qp * q
        Delta += TAU_F[n] * qp
    W = WQ * Y ** 10 * np.abs(Delta) ** 2
    return X, Y, W


def build_lattice_data(X, Y, B, rmax=3):
    """Per r: concatenated primal/dual norms + node indices."""
    data = {}
    M = len(X)
    for r in range(1, rmax + 1):
        Ns, Nds, i1, i2 = [], [], [], []
        for k in range(M):
            Q = Q_mon(X[k], Y[k], r)
            Qi = np.linalg.inv(Q); Qi = 0.5 * (Qi + Qi.T)
            a = enumerate_norms(Q, B)
            b = enumerate_norms(Qi, B)
            Ns.append(a); Nds.append(b)
            i1.append(np.full(len(a), k, dtype=np.int32))
            i2.append(np.full(len(b), k, dtype=np.int32))
        data[r] = dict(
            N=np.concatenate(Ns), idx1=np.concatenate(i1),
            Nd=np.concatenate(Nds), idx2=np.concatenate(i2),
            det=float(np.prod(binom_diag(r))), M=M)
    return data


def I_of_s(data_r, W, s, n):
    det = data_r["det"]; M = data_r["M"]
    x1 = PI * data_r["N"]
    t1 = upper_gamma(s, x1) * x1 ** (-s)
    S1 = np.bincount(data_r["idx1"], weights=t1, minlength=M)
    a = 0.5 * n - s
    x2 = PI * data_r["Nd"]
    t2 = upper_gamma(a, x2) * x2 ** (-a)
    S2 = np.bincount(data_r["idx2"], weights=t2, minlength=M)
    lam = S1 + S2 / math.sqrt(det) \
        + 1.0 / (math.sqrt(det) * (s - 0.5 * n)) - 1.0 / s
    E = PI ** s / math.gamma(s) * lam
    return float(np.dot(W, E))


def full_run(nx, ny, ymax, B, slist, rmax=3, tag=""):
    X, Y, W = build_grid(nx, ny, ymax)
    data = build_lattice_data(X, Y, B, rmax)
    I = {}
    for r in range(1, rmax + 1):
        for s in slist:
            I[(r, s)] = I_of_s(data[r], W, s, r + 1)
    pet = float(np.sum(W))
    rep("  [grid %s] nx=%d ny=%d ymax=%.0f B=%.0f  nodes=%d  <Delta,Delta>_quad=%.12e"
        % (tag, nx, ny, ymax, B, len(X), pet))
    return I, pet


rep("[S4] MAIN RUN")
I_MAIN, PET = full_run(36, 48, 6.0, 36.0, SALL, tag="primary")
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 5: L-values, candidates, ratio tests
# ----------------------------------------------------------------------------


def zeta(w):
    return float(mp.zeta(w))


def Gfac(w):
    return math.exp(math.lgamma(w) - w * math.log(4 * PI))


def L_sym(m, w, pcut=10000):
    mask = PRIMES <= pcut
    lp = PRIMES[mask].astype(float)
    th = THETA_P[mask]
    x = lp ** (-w)
    logtot = np.zeros(len(lp), complex)
    for j in range(m + 1):
        logtot += np.log(1.0 - np.exp(1j * (m - 2 * j) * th) * x)
    val = complex(np.exp(-np.sum(logtot)))
    assert abs(val.imag) < 1e-8 * abs(val)
    return val.real


def Dser(w, pcut=10000):
    return zeta(w) * L_sym(2, w, pcut) / zeta(2 * w)


# instrument check: D(w) Euler form vs direct exact-tau sum
for w in (4.1, 5.6):
    lam_n = np.array([float(TAU[n]) / n ** 5.5 for n in range(1, NTAU + 1)])
    ns = np.arange(1, NTAU + 1, dtype=float)
    direct = float(np.sum(lam_n ** 2 * ns ** (-w)))
    eul = Dser(w)
    rep("[S5] D(%.1f): direct tau-sum (N=%d) = %.12e ; Euler zL2/z = %.12e ; "
        "rel diff = %.2e" % (w, NTAU, direct, eul, abs(direct - eul) / eul))

rep("")
rep("[S5] r=1 SANITY (instrument certification)")
rows = []
for s in SBASE:
    T1 = 2.0 * zeta(2 * s) * Gfac(s + 11.0) * Dser(s)
    R = I_MAIN[(1, s)] / T1
    rows.append(R)
    rep("  s=%.2f  I_1=%.10e  target=%.10e  ratio=%.10f" % (s, I_MAIN[(1, s)], T1, R))
rows = np.array(rows)
dev1 = (rows.max() - rows.min()) / abs(rows.mean())
rep("  ratio constancy dev = %.3e ; |mean ratio - 1| = %.3e" % (dev1, abs(rows.mean() - 1)))
rep("  r=1 SANITY: %s (criterion: dev <= 1e-6)" % ("PASS" if dev1 <= 1e-6 else "FAIL"))
rep("")


def cand_lists(pcut=10000):
    L2 = lambda w: L_sym(2, w, pcut)
    L3 = lambda w: L_sym(3, w, pcut)
    LD = lambda w: L_sym(1, w, pcut)
    Dw = lambda w: Dser(w, pcut)
    c2 = [
        ("2A", lambda s: zeta(2*s) * Gfac(2*s+11) * Dw(2*s)),
        ("2B", lambda s: zeta(2*s-1) * Gfac(2*s+10) * Dw(2*s-1)),
        ("2C", lambda s: zeta(2*s) * Gfac(2*s+11) * L2(2*s)),
        ("2D", lambda s: zeta(2*s-1) * Gfac(2*s+10) * L2(2*s-1)),
        ("2E", lambda s: zeta(2*s) * zeta(2*s-1) * Gfac(2*s+10) * L2(2*s-1)),
        ("2F", lambda s: zeta(2*s-1) * Gfac(s+11)
                * math.gamma(s-0.5)/math.gamma(s) * L2(2*s-1)),
        ("2G", lambda s: zeta(2*s-1) * Gfac(s+11) * L2(s)),
        ("2H", lambda s: zeta(2*s) * Gfac(s+11) * L2(s+0.5)),
        ("2I", lambda s: I_MAIN[(1, s)]),
        ("2J", lambda s: zeta(2*s) * zeta(2*s-1) * Gfac(2*s+11) * Dw(2*s)),
    ]
    c3 = [
        ("3A", lambda s: zeta(2*s) * Gfac(2*s+11) * L3(2*s)),
        ("3B", lambda s: zeta(2*s-1) * Gfac(2*s+10) * L3(2*s-1)),
        ("3C", lambda s: zeta(2*s) * Gfac(2*s+11) * LD(2*s) * LD(2*s-1)),
        ("3D", lambda s: zeta(2*s-1) * Gfac(2*s+10) * LD(2*s-1)**2),
        ("3E", lambda s: zeta(2*s) * zeta(2*s-2) * Gfac(2*s+10) * L3(2*s-1)),
        ("3F", lambda s: zeta(2*s-1) * Gfac(s+11) * L3(s+0.5)),
        ("3G", lambda s: zeta(2*s-2) * Gfac(2*s+10) * Dw(2*s-1)),
        ("3H", lambda s: I_MAIN[(1, s)]),
        ("3I", lambda s: I_MAIN[(2, s)]),
        ("3J", lambda s: zeta(2*s) * Gfac(2*s+11) * Dw(2*s)),
    ]
    return c2, c3


CANDS2, CANDS3 = cand_lists(10000)


def slope(vals_lo, vals_hi):
    return (np.log(np.abs(vals_hi)) - np.log(np.abs(vals_lo))) / DS


def test_rank(r, cands, thresh=1e-5):
    rep("[S5] r=%d ratio tests against pre-registered candidates" % r)
    Ilo = np.array([I_MAIN[(r, s)] for s in SBASE])
    Ihi = np.array([I_MAIN[(r, s + DS)] for s in SBASE])
    sI = slope(Ilo, Ihi)
    rep("  I_%d(s) at base grid: %s" % (r, "  ".join("%.6e" % v for v in Ilo)))
    rep("  dlog I_%d/ds        : %s" % (r, "  ".join("%+.5f" % v for v in sI)))
    results = []
    for name, f in cands:
        Clo = np.array([f(s) for s in SBASE])
        Chi = np.array([f(s + DS) for s in SBASE])
        R = Ilo / Clo
        dev = (R.max() - R.min()) / abs(R.mean())
        dsl = sI - slope(Clo, Chi)
        results.append((dev, name, R, dsl))
        rep("  cand %s : ratio dev = %.3e ; slope gap (dlogI-dlogC) = [%s]"
            % (name, dev, " ".join("%+.4f" % v for v in dsl)))
    results.sort(key=lambda t: t[0])
    best = results[0]
    hit = best[0] <= thresh
    rep("  BEST: %s with dev = %.3e -> %s" %
        (best[1], best[0], "IDENTIFICATION (pre-registered criterion met)"
         if hit else "NO identification (all candidates fail 1e-5)"))
    if hit:
        rep("  ratio values: %s" % " ".join("%.10e" % v for v in best[2]))
    return best, hit, sI


BEST2, HIT2, SLOPE2 = test_rank(2, CANDS2)
rep("")
BEST3, HIT3, SLOPE3 = test_rank(3, CANDS3)
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 6: truncation / stability battery
# ----------------------------------------------------------------------------

rep("[S6] stability battery (each knob doubled; report max rel shift of I_r)")
SCHK = [3.6, 4.6]
I_B, _ = full_run(36, 48, 6.0, 72.0, SCHK, tag="lattice-B x2")
I_G, PET_G = full_run(48, 64, 6.0, 36.0, SCHK, tag="quadrature x~1.8")
I_Y, _ = full_run(36, 56, 9.0, 36.0, SCHK, tag="ymax 6->9")


def maxshift(Iref, Inew):
    return max(abs(Inew[(r, s)] - Iref[(r, s)]) / abs(Iref[(r, s)])
               for r in (1, 2, 3) for s in SCHK)


rep("  lattice cutoff B 36 -> 72   : max rel shift = %.2e" % maxshift(I_MAIN, I_B))
rep("  quadrature 36x48 -> 48x64   : max rel shift = %.2e" % maxshift(I_MAIN, I_G))
rep("  ymax 6 -> 9                 : max rel shift = %.2e" % maxshift(I_MAIN, I_Y))
rep("  Petersson <Delta,Delta> quad vs refined: rel shift = %.2e" %
    (abs(PET_G - PET) / PET))
# Euler p-cutoff doubling on all candidate values used
c2b, c3b = cand_lists(20000)
mx = 0.0
for (n1, f1), (n2, f2) in list(zip(CANDS2, c2b)) + list(zip(CANDS3, c3b)):
    if n1 in ("2I", "3H", "3I"):
        continue
    for s in SBASE:
        a, b = f1(s), f2(s)
        mx = max(mx, abs(a - b) / abs(a))
rep("  Euler p-cutoff 1e4 -> 2e4 on all candidates: max rel shift = %.2e" % mx)
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 6b: POST-HOC (labelled per protocol; conceived AFTER seeing the
# pre-registered nulls).
#
# (i) TWO invariant transports.  There are two natural SL2(Z)-invariant
# monomial-lattice transports of the Sym^r Gram:
#     framing-1:  Q_mon(z)  = rho_mon(g_z) diag(C(r,i)) rho_mon(g_z)^T
#     framing-2:  Q_dual(z) = D^-1 Q_mon(z) D^-1,  D = diag(C(r,i))
# framing-2 is the task-literal scaled construction transported to the
# monomial lattice.  Structural identity (measured below):
#     rho_mon(k)^T = D^-1 rho_mon(k^-1) D  for k in SO(2)
#  => Q_mon(z)^-1 = rho_mon(J)^T Q_dual(z) rho_mon(J),  rho_mon(J) integer
# unimodular -- i.e. POISSON DUALITY EXCHANGES THE TWO INVARIANT FRAMINGS
# (at the same z), with det factor prod C(r,i); only the non-arithmetic
# scaled frame is Poisson self-fixed.
#
# (ii) Exact degenerate-stratum decomposition holds in FRAMING-2: the
# disc-0 stratum is {e u^r : e in Z\0, u primitive}, and under Q_dual
# N_z(u^r) = (Sym^1 norm)^r exactly, so the stratum subsum of E^(2)_r(z,s)
# is Z(2s) E_1(z, rs)/Z(2rs) and its contribution to I^(2)_r(s) is exactly
#     Pdeg_r(s) = 2 Z(2s) G(rs+11) D(rs)
# via the CERTIFIED r=1 unfolding.  (Under framing-1 the power law FAILS --
# measured below -- so no analogous exact subtraction is available there.)
# ----------------------------------------------------------------------------

rep("[S6b] POST-HOC: two invariant framings + exact stratum decomposition")
rep("  (labelled POST-HOC: framing-2 analysis designed after the primary nulls)")


def Q_dualf(x, y, r):
    Dm = binom_diag(r)
    Q = Q_mon(x, y, r)
    return Q / Dm[:, None] / Dm[None, :]


zpt = (0.234, 1.077)
# (i) structural identities
for r in (2, 3):
    Qm = Q_mon(zpt[0], zpt[1], r)
    Qd = Q_dualf(zpt[0], zpt[1], r)
    U = rho_mon(S_MAT, r)  # rho_mon(J)
    dev = np.max(np.abs(np.linalg.inv(Qm) - U.T @ Qd @ U))
    rep("  r=%d  Q_mon^-1 = rho(J)^T Q_dual rho(J): max dev = %.2e  "
        "(rho(J) integer, det %+0.f); det Q_dual = %.6f (1/prod C = %.6f)"
        % (r, dev, np.linalg.det(U), np.linalg.det(Qd),
           1.0 / np.prod(binom_diag(r))))
    # V1 for framing-2
    z = complex(*zpt); s = 3.3
    Ez = epstein(Qd, s)
    zT = mobius(T_MAT, z); zS = mobius(S_MAT, z)
    rep("  r=%d  framing-2 V1: relΔ(S)=%.2e relΔ(T)=%.2e"
        % (r, abs(epstein(Q_dualf(zS.real, zS.imag, r), s) - Ez) / Ez,
           abs(epstein(Q_dualf(zT.real, zT.imag, r), s) - Ez) / Ez))
# power law under both framings
p, q = 1, 2
nu1 = abs(p * complex(*zpt) + q) ** 2 / zpt[1]
v2 = np.array([p * p, 2 * p * q, q * q], float)
rep("  power law N(u^2) vs (Sym^1 norm)^2 at u=(1,2): framing-1 %.6f vs %.6f"
    " (FAILS); framing-2 %.6f vs %.6f (rel dev %.2e)"
    % (v2 @ Q_mon(zpt[0], zpt[1], 2) @ v2, nu1 ** 2,
       v2 @ Q_dualf(zpt[0], zpt[1], 2) @ v2, nu1 ** 2,
       abs(v2 @ Q_dualf(zpt[0], zpt[1], 2) @ v2 - nu1 ** 2) / nu1 ** 2))

# (ii) pointwise stratum identity under framing-2
spt = 4.6
Bpt = 400.0
for r in (2, 3):
    Qd = Q_dualf(zpt[0], zpt[1], r)
    N, V = enumerate_norms(Qd, Bpt, want_vecs=True)
    if r == 2:
        aa, bb, cc = V.T
        mask = (bb * bb - 4 * aa * cc == 0)
    else:
        aa, bb, cc, dd = V.T
        mask = (bb * bb == 3 * aa * cc) & (cc * cc == 3 * bb * dd) \
            & (bb * cc == 9 * aa * dd)
    direct = float(np.sum(N[mask] ** (-spt)))
    target = zeta(2 * spt) / zeta(2 * r * spt) \
        * epstein(Q_mon(zpt[0], zpt[1], 1), r * spt)
    rep("  r=%d framing-2 pointwise stratum identity (s=%.1f, B=%.0f, %d pts): "
        "direct=%.12e target=%.12e rel diff=%.2e"
        % (r, spt, Bpt, int(mask.sum()), direct, target,
           abs(direct - target) / target))
    # framing-1 control (expected to FAIL the power-law identity)
    Qm = Q_mon(zpt[0], zpt[1], r)
    Nm, Vm = enumerate_norms(Qm, Bpt, want_vecs=True)
    if r == 2:
        aa, bb, cc = Vm.T
        maskm = (bb * bb - 4 * aa * cc == 0)
    else:
        aa, bb, cc, dd = Vm.T
        maskm = (bb * bb == 3 * aa * cc) & (cc * cc == 3 * bb * dd) \
            & (bb * cc == 9 * aa * dd)
    directm = float(np.sum(Nm[maskm] ** (-spt)))
    rep("      (framing-1 control: direct=%.12e, rel diff to power-law target"
        " = %.2e -- the law fails there, as predicted)"
        % (directm, abs(directm - target) / target))

# framing-2 MAIN RUN (grid identical to primary; frozen candidate lists)
rep("  framing-2 main run (same grid/candidates; run AFTER stratum analysis):")
X2, Y2, W2 = build_grid(36, 48, 6.0)
I_D = {}
for r in (2, 3):
    Ns, Nds, i1, i2 = [], [], [], []
    for k in range(len(X2)):
        Q = Q_dualf(X2[k], Y2[k], r)
        Qi = np.linalg.inv(Q); Qi = 0.5 * (Qi + Qi.T)
        a = enumerate_norms(Q, 36.0)
        b = enumerate_norms(Qi, 36.0)
        Ns.append(a); Nds.append(b)
        i1.append(np.full(len(a), k, dtype=np.int32))
        i2.append(np.full(len(b), k, dtype=np.int32))
    dat = dict(N=np.concatenate(Ns), idx1=np.concatenate(i1),
               Nd=np.concatenate(Nds), idx2=np.concatenate(i2),
               det=float(1.0 / np.prod(binom_diag(r))), M=len(X2))
    for s in SALL:
        I_D[(r, s)] = I_of_s(dat, W2, s, r + 1)

for r in (2, 3):
    rep("  I^(2)_%d(s): %s" % (r, "  ".join("%.6e" % I_D[(r, s)] for s in SBASE)))


def Pdeg(r, s, pcut=10000):
    return 2.0 * zeta(2 * s) * Gfac(r * s + 11.0) * Dser(r * s, pcut)


# frozen-candidate ratio tests for framing-2
def test_framing2(r, cands, thresh=1e-5):
    Ilo = np.array([I_D[(r, s)] for s in SBASE])
    Ihi = np.array([I_D[(r, s + DS)] for s in SBASE])
    sI = slope(Ilo, Ihi)
    rep("  framing-2 r=%d dlogI/ds: %s" % (r, "  ".join("%+.5f" % v for v in sI)))
    res = []
    for name, f in cands:
        Clo = np.array([f(s) for s in SBASE])
        R = Ilo / Clo
        dev = (R.max() - R.min()) / abs(R.mean())
        res.append((dev, name, R))
    res.sort(key=lambda t: t[0])
    rep("  framing-2 r=%d BEST frozen candidate: %s dev=%.3e -> %s"
        % (r, res[0][1], res[0][0],
           "IDENTIFICATION" if res[0][0] <= thresh else "null"))
    return res[0]


F2BEST2 = test_framing2(2, CANDS2)
F2BEST3 = test_framing2(3, CANDS3)

REM = {}
rep("  framing-2 remainders R_r(s) = I^(2)_r(s) - Pdeg_r(s)")
rep("    [Pdeg exact for framing-2; R_2 = nondegenerate-orbit sum exactly;")
rep("     R_3 still contains the double-root stratum]")
for r in (2, 3):
    for s in SALL:
        REM[(r, s)] = I_D[(r, s)] - Pdeg(r, s)
    rep("  r=%d:  s, Pdeg/I, R, R/I, cancellation digits lost:" % r)
    for s in SBASE:
        I = I_D[(r, s)]; R = REM[(r, s)]
        rep("    s=%.2f  Pdeg/I=%.6f  R=%.6e  R/I=%.4e  lost=%.1f"
            % (s, Pdeg(r, s) / I, R, R / I, math.log10(max(I / abs(R), 1.0))))
# stability of framing-2 at doubled lattice cutoff
mxs = 0.0
for r in (2, 3):
    for s in (3.6, 4.6):
        Ns, Nds, i1, i2 = [], [], [], []
        for k in range(len(X2)):
            Q = Q_dualf(X2[k], Y2[k], r)
            Qi = np.linalg.inv(Q); Qi = 0.5 * (Qi + Qi.T)
            a = enumerate_norms(Q, 72.0)
            b = enumerate_norms(Qi, 72.0)
            Ns.append(a); Nds.append(b)
            i1.append(np.full(len(a), k, dtype=np.int32))
            i2.append(np.full(len(b), k, dtype=np.int32))
        dat = dict(N=np.concatenate(Ns), idx1=np.concatenate(i1),
                   Nd=np.concatenate(Nds), idx2=np.concatenate(i2),
                   det=float(1.0 / np.prod(binom_diag(r))), M=len(X2))
        v = I_of_s(dat, W2, s, r + 1)
        mxs = max(mxs, abs(v - I_D[(r, s)]) / abs(I_D[(r, s)]))
rep("  framing-2 lattice cutoff B 36 -> 72: max rel shift = %.2e" % mxs)
rep("")


def posthoc_test(r, cands, extra):
    rep("  POST-HOC ratio tests of R_%d against candidates (NOT pre-registered):" % r)
    Rlo = np.array([REM[(r, s)] for s in SBASE])
    Rhi = np.array([REM[(r, s + DS)] for s in SBASE])
    sR = slope(Rlo, Rhi)
    rep("    dlog R_%d/ds : %s" % (r, "  ".join("%+.5f" % v for v in sR)))
    res = []
    for name, f in list(cands) + list(extra):
        Clo = np.array([f(s) for s in SBASE])
        Chi = np.array([f(s + DS) for s in SBASE])
        Rt = Rlo / Clo
        dev = (Rt.max() - Rt.min()) / abs(Rt.mean())
        dsl = sR - slope(Clo, Chi)
        res.append((dev, name, Rt, dsl))
        rep("    cand %s : ratio dev = %.3e ; slope gap = [%s]"
            % (name, dev, " ".join("%+.4f" % v for v in dsl)))
    res.sort(key=lambda t: t[0])
    rep("    POST-HOC BEST for R_%d: %s dev = %.3e%s"
        % (r, res[0][1], res[0][0],
           "  ratios: " + " ".join("%.8e" % v for v in res[0][2])
           if res[0][0] <= 1e-4 else ""))
    return res[0], sR


EXTRA2 = [
    ("X2a Z(2s-1)^2 G(2s+10) D(2s-1)",
     lambda s: zeta(2*s-1)**2 * Gfac(2*s+10) * Dser(2*s-1)),
    ("X2b Z(4s-2) G(2s+10) D(2s-1)",
     lambda s: zeta(4*s-2) * Gfac(2*s+10) * Dser(2*s-1)),
]
EXTRA3 = [
    ("X3a Z(2s-1) G(3s+10) D(3s-1)",
     lambda s: zeta(2*s-1) * Gfac(3*s+10) * Dser(3*s-1)),
    ("X3b Z(2s) Z(2s-1) G(2s+11) D(2s)",
     lambda s: zeta(2*s) * zeta(2*s-1) * Gfac(2*s+11) * Dser(2*s)),
]
PHBEST2, RSLOPE2 = posthoc_test(2, CANDS2[:8], EXTRA2)
PHBEST3, RSLOPE3 = posthoc_test(3, CANDS3[:7], EXTRA3)
rep("  elapsed %.1fs" % (time.time() - T0))
rep("")

# ----------------------------------------------------------------------------
# Section 7: summary
# ----------------------------------------------------------------------------

rep("=" * 78)
rep("[S7] SUMMARY")
rep("  V1 (as stated, scaled basis): rho_scaled(T) is NOT integral for r>=2")
rep("      (sqrt-binomial entries); E_r on the scaled lattice breaks under T.")
rep("      Repaired framing: monomial lattice, Q = rho_mon diag(C(r,i)) rho_mon^T")
rep("      -> exact SL2(Z)-invariance (measured above).")
rep("  V2: exact rank-uniform Poisson SELF-duality holds on the SCALED lattice")
rep("      (det 1; dual Gram = signed-permutation conjugate).  The invariant")
rep("      monomial lattice obeys the det^{-1/2}-twisted duality instead")
rep("      (det = prod C(r,i)).  For r>=2 no single Z^{r+1} framing carries both.")
rep("  r=1 sanity: dev = %.3e, mean ratio-1 = %.3e -> %s" %
    (dev1, abs(rows.mean() - 1), "PASS" if dev1 <= 1e-6 else "FAIL"))
rep("  r=2: best candidate %s dev %.3e -> %s" %
    (BEST2[1], BEST2[0], "IDENTIFICATION" if HIT2 else "NULL vs pre-registered list"))
rep("  r=3: best candidate %s dev %.3e -> %s" %
    (BEST3[1], BEST3[0], "IDENTIFICATION" if HIT3 else "NULL vs pre-registered list"))
rep("")
rep("  POST-HOC two-framing structure: the two invariant transports Q_mon and")
rep("      Q_dual = D^-1 Q_mon D^-1 are EXCHANGED by Poisson duality")
rep("      (Q_mon^-1 = rho(J)^T Q_dual rho(J), rho(J) integer unimodular);")
rep("      only the non-arithmetic scaled frame is Poisson self-fixed.")
rep("  framing-2 frozen-candidate tests: r=2 best %s dev %.3e; r=3 best %s dev %.3e."
    % (F2BEST2[1], F2BEST2[0], F2BEST3[1], F2BEST3[0]))
rep("  POST-HOC stratum decomposition (framing-2, exact):")
rep("      I^(2)_r = 2 Z(2s) G(rs+11) D(rs) + R_r, first term = EXACT disc-0")
rep("      (power-orbit) stratum = rung-1 content at argument rs; best post-hoc")
rep("      match for R_2: %s (dev %.3e); for R_3: %s (dev %.3e)."
    % (PHBEST2[1], PHBEST2[0], PHBEST3[1], PHBEST3[0]))
rep("[POST-HOC / ANALYSIS NOTES]  (not pre-registered; labelled per protocol)")
rep("  - Orbit structure of the invariant lattice: SL2(Z)-orbits on Z^{r+1} are")
rep("    binary quadratic forms (r=2, disc invariant) / binary cubic forms (r=3,")
rep("    Shintani prehomogeneous space).  Definite-disc orbits unfold I_2 into")
rep("    CM-point evaluations of a Poincare-convolved |Delta|^2 y^12; indefinite")
rep("    orbits into closed-geodesic periods.  This predicts a spectral-sum")
rep("    (Katok-Sarnak/Waldspurger-type) object, NOT a finite product of")
rep("    standard L-values -- consistent with the measured verdicts above.")
rep("  - measured dlog I_r/ds tables are printed in [S5] for downstream use.")
rep("")
rep("total elapsed %.1fs" % (time.time() - T0))
OUT.close()
