"""Hejhal's algorithm: our OWN Hecke eigenvalues for a level-1 Maass form.

The previous work (tmp/maass_clocks.py) hit LMFDB's 1000-coefficient cap.  Here we
break the cap by SOLVING for our own Fourier/Hecke coefficients c_n of the level-1
Maass cusp form with KNOWN spectral parameter

    R = 13.779751351890738944   (LMFDB 1.0.1.3.1, EVEN / symmetry cos),

using Hejhal's linear-system algorithm.  Because R is already known to high
precision, this is the WELL-CONDITIONED regime: we do not search for R, we solve
the (over-determined, automorphy-constrained) linear system  V(R,Y) c = b  for the
coefficients at fixed R.

Maass expansion (level 1, even):
    f(z) = sqrt(y) sum_{n>=1} c_n * 2 cos(2 pi n x) * K_{iR}(2 pi n y),   c_1 = 1.
The c_n are the analytic Hecke eigenvalues (a_n); c_1 = 1, c_p the Hecke eigenvalue.

Hejhal machinery (Hejhal 1999; Stromberg; Lowry-Duda's heuristic_hejhal):
  * Horocycle at height Y (< sqrt(3)/2 so every point pulls back nontrivially):
    z_j = X_j + iY,  X_j = (j-1/2)/(2Q),  j = 1..Q  (half horocycle; even symmetry).
  * Pull each z_j back to the fundamental domain: z_j* = gamma_j z_j = X_j* + iY_j*.
  * Automorphy f(z_j) = f(z_j*) turns the truncated (n <= M) Fourier expansion into
    a linear system for c_1..c_M.  Inverting the DFT on the LEFT (the flat horocycle,
    height Y) and inserting the pulled-back expansion on the RIGHT gives, per n<=M,
        c_n sqrt(Y) K_{iR}(2 pi n Y)
          = (2/Q) sum_j [ sqrt(Y_j*) sum_{l<=M} c_l cos(2 pi l X_j*) K_{iR}(2 pi l Y_j*) ]
                        * cos(2 pi n X_j),
    i.e.  (D - V) c = 0 with  D_nn = sqrt(Y) K_{iR}(2 pi n Y).  Fix c_1 = 1, move its
    column to the RHS, drop the n=1 row, solve the M-1 system.

Truncation M(Y): K_{iR}(2 pi n Y) decays super-exponentially once 2 pi n Y > R, so
M ~ (R + 12 R^{1/3}) / (2 pi Y).  To reach coefficients up to index P we need
M >= P, i.e. Y <= (R + 12 R^{1/3}) / (2 pi P).  Larger P => smaller Y => bigger system.

K-Bessel with imaginary order K_{iR}(x) (rescaled by exp(pi R/2) to avoid under/over-
flow) via a vectorized port of Stromberg's double-precision routines:
  * power series (Gil-Segura-Temme / Stromberg besselk_dp_pow) for x < 0.7 R,
  * backward Miller recurrence (Stromberg besselk_dp_rec) for x >= 0.7 R.
Cross-checked against mpmath.besselk(iR, x) to ~1e-13.

VALIDATION GATES (all mandatory before any claim):
  (1) recover LMFDB's rigorous a_n (n <= 1000) to >= 6 digits;
  (2) Hecke multiplicativity residuals <= 1e-8 on fresh primes ABOVE 1000;
  (3) coefficient stability under truncation M / horocycle Y changes.
"""

import math
import sys
import time

import numpy as np
import mpmath

R_DEFAULT = 13.779751351890738944  # LMFDB 1.0.1.3.1, spectral parameter
SYMMETRY = "even"                  # cos expansion (LMFDB symmetry-col 0)

PI = math.pi
TWOPI = 2.0 * math.pi


# ===========================================================================
# K-Bessel  K_{iR}(x) * exp(pi R / 2)    (vectorized, double precision)
#   ported from Fredrik Stromberg / David Lowry-Duda lpkbessel.spyx
# ===========================================================================
def _besselk_pow(R, x, prec=1e-16):
    """Power series (Gil-Segura-Temme).  x, arrays; returns K_iR(x) exp(pi R/2).

    Valid/accurate for small-to-moderate x (x < ~0.7 R).  Vectorized over x.
    """
    x = np.asarray(x, dtype=np.float64)
    Rsq = R * R
    # sigma0 = Im log Gamma(1 + iR)
    lg = mpmath.loggamma(1.0 + 1j * R)
    sigma0 = float(mpmath.im(lg))
    xh = 0.5 * x
    xh2 = xh * xh
    th = R * np.log(xh) - sigma0
    s_th = np.sin(th)
    c_th = np.cos(th)
    tmp_factor = math.sqrt(PI / (R * math.sinh(PI * R)))
    exp_PihR = math.exp(PI * R / 2.0)

    f0 = -tmp_factor * s_th
    r0 = R * tmp_factor * c_th
    r1 = R * tmp_factor / (1.0 + Rsq) * (c_th + R * s_th)

    summa = f0.copy()
    fk1 = f0
    rk1 = r0
    # k = 1 term
    fk = (fk1 + rk1) / (1.0 + Rsq)
    ck = xh2.copy()
    summa = summa + ck * fk
    fk1 = fk
    rk1 = r1
    rk2 = r0
    ck1 = ck
    N_max = 2000
    active = np.ones_like(x, dtype=bool)
    for k in range(2, N_max + 1):
        den = k * k + Rsq
        fk = (k * fk1 + rk1) / den
        rk = ((2.0 * k - 1.0) * rk1 - rk2) / den
        ck = xh2 * ck1 / k
        term = ck * fk
        summa = summa + term
        # convergence when relative term small everywhere
        with np.errstate(divide="ignore", invalid="ignore"):
            rel = np.abs(term / summa * exp_PihR)
        active = rel >= prec
        fk1 = fk
        rk2 = rk1
        rk1 = rk
        ck1 = ck
        if not active.any():
            break
    return summa * exp_PihR


def _besselk_rec_scalar(R, x, prec=1e-14):
    """Backward Miller recurrence for a single x (Stromberg besselk_dp_rec).
    Returns K_iR(x) exp(pi R/2)."""
    p = 0.25 + R * R
    q = 2.0 * (x - 1.0)
    t = 0.0
    k = 1.0
    NMAX = 5000
    n_start = 1
    ef1 = math.log(2.0 * x / PI)
    n = n_start
    nn = 0
    for nn in range(1, NMAX + 1):
        err = abs(t - k)
        if err < prec and n > n_start + 40:
            break
        n = n + 20
        t = k
        y = 1.0
        k = 1.0
        d = 1.0
        tmp = 2.0 * x - R * PI
        if tmp > 1300.0:
            return 0.0
        nr = float(n)
        ef = math.exp((ef1 + tmp) / (2.0 * nr))
        mr_p1 = n + 1
        mr = n
        for m in range(n, 0, -1):
            mr_m1 = m - 1
            y = (mr_m1 + p / mr) / (q + mr_p1 * (2.0 - y))
            k = ef * (d + y * k)
            d = d * ef
            mr_p1 = mr
            mr = mr_m1
        if k == 0.0:
            return 0.0
        k = 1.0 / k
    return k


# vectorized recurrence: run the scalar recurrence but over a numpy array by
# fixing a single (generous) n for the whole batch -- justified because for our
# range x is bounded and a common n suffices; we choose n from the max x.
def _besselk_rec_vec(R, x, prec=1e-14):
    """Vectorized backward recurrence over array x, common iteration depth.
    Returns K_iR(x) exp(pi R/2).  Matches scalar routine to ~1e-13."""
    x = np.asarray(x, dtype=np.float64)
    out = np.zeros_like(x)
    # super-exponential cutoff: 2x - R pi > 1300 -> underflow to 0
    big = (2.0 * x - R * PI) > 1300.0
    small = ~big
    if not small.any():
        return out
    xs = x[small]
    p = 0.25 + R * R
    q = 2.0 * (xs - 1.0)
    ef1 = np.log(2.0 * xs / PI)
    tmp = 2.0 * xs - R * PI
    # iterate n upward until convergence of ALL entries; use previous-iterate diff
    prev = np.full_like(xs, np.inf)
    k_cur = np.ones_like(xs)
    n = 1
    NMAX = 300  # each step adds 20 => up to n ~ 6000, ample
    converged = np.zeros_like(xs, dtype=bool)
    result = np.ones_like(xs)
    for _ in range(NMAX):
        n = n + 20
        nr = float(n)
        ef = np.exp((ef1 + tmp) / (2.0 * nr))
        y = np.ones_like(xs)
        k = np.ones_like(xs)
        d = np.ones_like(xs)
        mr_p1 = float(n + 1)
        mr = float(n)
        for m in range(n, 0, -1):
            mr_m1 = float(m - 1)
            y = (mr_m1 + p / mr) / (q + mr_p1 * (2.0 - y))
            k = ef * (d + y * k)
            d = d * ef
            mr_p1 = mr
            mr = mr_m1
        kval = 1.0 / k
        newconv = (np.abs(kval - result) < prec) & (n > 60)
        result = np.where(converged, result, kval)
        just = newconv & ~converged
        converged = converged | newconv
        if converged.all():
            break
    out[small] = result
    return out


def besselk_iR(R, x):
    """K_iR(x) * exp(pi R/2), vectorized.  Picks power series / recurrence by region."""
    x = np.asarray(x, dtype=np.float64)
    out = np.empty_like(x)
    lo = x < 0.7 * R
    if lo.any():
        out[lo] = _besselk_pow(R, x[lo])
    hi = ~lo
    if hi.any():
        out[hi] = _besselk_rec_vec(R, x[hi])
    return out


# ===========================================================================
# Fundamental-domain pullback for SL(2,Z)
# ===========================================================================
def pullback(x, y):
    """Pull (x + iy) into the standard fundamental domain of SL(2,Z).
    Returns (xstar, ystar).  Vectorized over arrays x, y."""
    x = np.array(x, dtype=np.float64)
    y = np.array(y, dtype=np.float64)
    for _ in range(200):
        # translate x into (-1/2, 1/2]
        shift = np.floor(x + 0.5)
        x = x - shift
        r2 = x * x + y * y
        inv = r2 < 1.0 - 1e-12
        if not inv.any():
            break
        # apply S: z -> -1/z  on the points inside the unit circle
        xi = x[inv]
        yi = y[inv]
        denom = xi * xi + yi * yi
        x[inv] = -xi / denom
        y[inv] = yi / denom
    return x, y


# ===========================================================================
# Hejhal linear system  (D - V) c = 0,  c_1 = 1
# ===========================================================================
def build_system(R, Y, M, Q, symmetry="even", verbose=False):
    """Assemble the Hejhal matrix.  Returns (A, b) for  A c[2..M] = b  with c_1 = 1.

    Even symmetry -> cos; odd -> sin.  The horocycle uses Q points on the half
    horocycle (j-1/2)/(2Q); the factor 2/Q folds in the reflected half.
    """
    trig = np.cos if symmetry == "even" else np.sin
    j = np.arange(1, Q + 1)
    Xj = (j - 0.5) / (2.0 * Q)                 # (Q,)
    Yj = np.full(Q, Y)
    Xs, Ys = pullback(Xj, Yj)                  # pulled-back coords (Q,)

    ns = np.arange(1, M + 1)                    # coefficient indices 1..M

    # K-Bessel at pulled-back heights: Kmat[l-1, jpoint] = K_iR(2 pi l Ys_j) exp(piR/2)
    # argument matrix (M, Q)
    arg = TWOPI * np.outer(ns, Ys)             # (M, Q)
    if verbose:
        print(f"# assembling K-Bessel over {M}x{Q} = {M*Q} args ...", flush=True)
        t0 = time.time()
    Kmat = besselk_iR(R, arg.ravel()).reshape(M, Q)   # (M, Q)
    if verbose:
        print(f"#   K-Bessel done in {time.time()-t0:.1f}s", flush=True)

    # right-hand expansion weights per point j and coefficient l:
    #   W[l, j] = sqrt(Ys_j) * trig(2 pi l Xs_j) * Kmat[l, j]
    trigRHS = trig(TWOPI * np.outer(ns, Xs))   # (M, Q)
    W = np.sqrt(Ys)[None, :] * trigRHS * Kmat  # (M, Q)

    # left DFT test functions: T[n, j] = trig(2 pi n Xj)
    T = trig(TWOPI * np.outer(ns, Xj))         # (M, Q)

    # V[n, l] = (2/Q) sum_j T[n, j] * W[l, j]
    if verbose:
        print("# forming V = (2/Q) T W^T ...", flush=True)
        t0 = time.time()
    V = (2.0 / Q) * (T @ W.T)                   # (M, M)
    if verbose:
        print(f"#   V formed in {time.time()-t0:.1f}s", flush=True)

    # diagonal D_nn = sqrt(Y) K_iR(2 pi n Y)
    Ldiag = np.sqrt(Y) * besselk_iR(R, TWOPI * ns * Y)   # (M,)

    # full system  (D - V) c = 0.  Fix c_1 = 1: move column 0 to RHS, drop row 0.
    Dm = np.diag(Ldiag)
    Mfull = Dm - V                              # (M, M)
    A = Mfull[1:, 1:]                           # (M-1, M-1)
    b = -Mfull[1:, 0]                           # (M-1,)  from c_1 = 1
    return A, b, Ldiag


def solve_coeffs(R, Y, M, Q, symmetry="even", verbose=False):
    """Solve Hejhal system, return c[0..M-1] with c[0]=c_1=1."""
    A, b, _ = build_system(R, Y, M, Q, symmetry=symmetry, verbose=verbose)
    if verbose:
        print(f"# solving {A.shape[0]}x{A.shape[1]} linear system ...", flush=True)
        t0 = time.time()
    c_rest = np.linalg.solve(A, b)
    if verbose:
        print(f"#   solved in {time.time()-t0:.1f}s", flush=True)
    c = np.empty(M)
    c[0] = 1.0
    c[1:] = c_rest
    return c


# ===========================================================================
# MEMORY-LEAN solver exploiting the l-sparsity of V.
#
# The Hejhal matrix V(n,l) = (2/Q) sum_j T(n,j) W(l,j) has W(l,j) nonzero only
# for small l, because W(l,j) carries K_iR(2 pi l Ys_j) and the pulled-back
# heights satisfy Ys_j >= sqrt(3)/2, so the K-Bessel is super-exponentially tiny
# once 2 pi l Ys_j > R.  Empirically ||V[:,l]|| < 1e-14 for l beyond ~8-10, and
# < 1e-300 (true zero) beyond ~L.  Hence (D - V) is DIAGONAL except in its first
# L columns, and the linear system collapses:
#   * rows/cols 1..L couple only c_1..c_L  -> a tiny L x L solve;
#   * for n > L:  D_nn c_n = sum_{l<=L} V(n,l) c_l  -> c_n explicit.
# This is O(M L) time & memory instead of O(M^2)/O(M^3).  We pick L by the point
# where the K-Bessel column at the SMALLEST pulled-back height underflows, with a
# safety pad, and (below) VERIFY the lean solver reproduces the dense solve.
# ===========================================================================
def choose_L(R, Ys, tol=1e-16, pad=6):
    """Smallest L such that K_iR(2 pi l Ys_min) < tol for all l > L (plus pad)."""
    ymin = float(np.min(Ys))
    # K decays super-exponentially once 2 pi l ymin > R; step l up until underflow
    l = 1
    while l < 100000:
        val = besselk_iR(R, np.array([TWOPI * l * ymin]))[0]
        if abs(val) < tol:
            break
        l += 1
    return l + pad


def solve_coeffs_lean(R, Y, M, Q, symmetry="even", L=None, verbose=False):
    """Memory-lean Hejhal solve exploiting V's l-sparsity.  Returns c[0..M-1].

    Identical result to solve_coeffs but O(M L) memory; enables M ~ 10^5+.
    """
    trig = np.cos if symmetry == "even" else np.sin
    j = np.arange(1, Q + 1)
    Xj = (j - 0.5) / (2.0 * Q)
    Yj = np.full(Q, Y)
    Xs, Ys = pullback(Xj, Yj)

    if L is None:
        L = choose_L(R, Ys)
    L = min(L, M)
    if verbose:
        print(f"# lean solve: M={M}, Q={Q}, L(active cols)={L}", flush=True)
        t0 = time.time()

    ns = np.arange(1, M + 1)                    # 1..M
    ls = np.arange(1, L + 1)                    # active coefficient indices 1..L

    # W restricted to l <= L:  Wl[l-1, j] = sqrt(Ys_j) trig(2 pi l Xs_j) K_iR(2 pi l Ys_j)
    argL = TWOPI * np.outer(ls, Ys)            # (L, Q)  -- small
    KL = besselk_iR(R, argL.ravel()).reshape(L, Q)
    Wl = np.sqrt(Ys)[None, :] * trig(TWOPI * np.outer(ls, Xs)) * KL   # (L, Q)

    # Left test functions for ALL n but we only need V(:, l<=L):
    #   V[n, l] = (2/Q) sum_j trig(2 pi n Xj) Wl[l, j]
    # Compute in blocks over n to bound memory (Tblk is blk x Q).  Choose blk so
    # the temporary trig block stays under ~0.5 GB regardless of M, Q.
    Vcols = np.empty((M, L))
    WlT = np.ascontiguousarray(Wl.T)                       # (Q, L)
    blk = max(1, int(6e7 // max(Q, 1)))                    # ~0.5 GB trig block
    for a in range(0, M, blk):
        bnd = min(a + blk, M)
        Tblk = trig(TWOPI * np.outer(ns[a:bnd], Xj))       # (blk, Q)
        Vcols[a:bnd] = (2.0 / Q) * (Tblk @ WlT)            # (blk, L)
    # diagonal D_nn
    Ldiag = np.sqrt(Y) * besselk_iR(R, TWOPI * ns * Y)     # (M,)

    # top-left L x L block of (D - V): A_LL[i,k] = D_i delta - V[i,k], i,k in 1..L
    A_LL = -Vcols[:L, :L].copy()
    A_LL[np.arange(L), np.arange(L)] += Ldiag[:L]
    # fix c_1 = 1: drop row 0, move col 0 to RHS
    Asub = A_LL[1:, 1:]
    bsub = -A_LL[1:, 0]
    cL = np.empty(L)
    cL[0] = 1.0
    cL[1:] = np.linalg.solve(Asub, bsub)

    # explicit back-substitution for n > L:  c_n = (sum_{l<=L} V[n,l] c_l) / D_nn
    c = np.empty(M)
    c[:L] = cL
    rhs = Vcols[L:] @ cL                        # (M-L,)
    c[L:] = rhs / Ldiag[L:]
    if verbose:
        print(f"#   lean solve done in {time.time()-t0:.1f}s "
              f"(peak arrays ~ {(M*L*8)/1e9:.2f} GB)", flush=True)
    return c


# ===========================================================================
# quick self-test of the K-Bessel against mpmath
# ===========================================================================
def _test_bessel():
    R = R_DEFAULT
    xs = np.array([0.3, 1.0, 3.0, 7.0, 10.0, 20.0, 30.0, 50.0])
    got = besselk_iR(R, xs)
    print("K-Bessel cross-check vs mpmath (rescaled by exp(pi R/2)):")
    ok = True
    for x, g in zip(xs, got):
        ref = float(mpmath.re(mpmath.besselk(1j * R, x) * mpmath.e ** (mpmath.pi * R / 2)))
        rel = abs(g - ref) / (abs(ref) + 1e-300)
        flag = "" if rel < 1e-10 else "  <-- MISMATCH"
        if rel >= 1e-10:
            ok = False
        print(f"  x={x:6.2f}  ours={g: .8e}  mpmath={ref: .8e}  rel={rel:.1e}{flag}")
    print("  -> K-Bessel OK" if ok else "  -> K-Bessel PROBLEM")
    return ok


# ===========================================================================
# helpers
# ===========================================================================
def sieve(m):
    s = np.ones(m + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def truncation_Y(R, M):
    """Horocycle height so the truncation index is ~M."""
    return (R + 12.0 * R ** (1.0 / 3.0)) / (TWOPI * M)


def compute_coeffs(R, P, symmetry="even", headroom=1.6, Q_extra=20, verbose=True):
    """Solve for c_1..c_P (trustworthy) by using an oversized bank M = headroom*P.

    Empirically Hecke residuals stay <= 1e-9 for n <= 0.65 M; headroom=1.6 keeps
    P <= 0.625 M with margin.  Returns c[0..M-1] (index n-1 -> c_n) and M.
    """
    M = int(math.ceil(headroom * P))
    Y = truncation_Y(R, M)
    Q = M + Q_extra
    if verbose:
        print(f"# target P={P}, bank M={M}, Y={Y:.6g}, Q={Q}", flush=True)
    t0 = time.time()
    c = solve_coeffs(R, Y, M, Q, symmetry=symmetry, verbose=verbose)
    if verbose:
        print(f"# compute_coeffs total {time.time()-t0:.1f}s", flush=True)
    return c, M, Y, Q


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "bessel":
        _test_bessel()
    else:
        _test_bessel()
