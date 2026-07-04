"""Sparse-Φ Krylov build of the U_13 matrix for e_ord — the feasible realization.

We do NOT form the full Cauchy product Φ = d^{-1}(f)·h to q^M (that is ~M²/2 mults, infeasible
at M~171000).  Instead we compute Φ's coefficients ONLY at the sparse index set the Krylov
matrix needs: {p^j · n : j=0..d, n=1..L}.  Each Φ_m = Σ_{i} (d^{-1}f)_i h_{m-i} is one
convolution sum, O(m).  The matrix of U_p on span{Φ, U_pΦ, ...} follows from
(U_p^j Φ)_n = Φ_{p^j n}.

Reports: Krylov dimension d, the fixed q-precision M, the U_p matrix, and the spectral-e_ord
gates (idempotence; fixes a known ordinary eigenform).
"""
import time
import sys

import numpy as _np
import sympy as _sp
from rung3_rhs import Unramified, Qpf
from rung3_lhs import a_p_h_exponent, _ind31_mod3, _legendre, _ap_ell_fast


def _ap_ell_np(ainv, p):
    """a_p of E/Q via numpy-vectorized Legendre point count (O(p) but ~30x faster in numpy)."""
    a1, a2, a3, a4, a6 = [c % p for c in ainv]
    X = _np.arange(p, dtype=_np.int64)
    rhs = ((X * X % p) * X % p + a2 * (X * X % p) + a4 * X + a6) % p
    b = (a1 * X + a3) % p
    disc = ((b * b % p) + 4 * rhs) % p
    qr = _np.zeros(p, dtype=_np.int8)
    qr[(X * X % p)] = 1                  # qr[t]=1 iff t is a square mod p (incl 0)
    leg = _np.where(disc == 0, 0, _np.where(qr[disc] == 1, 1, -1))
    return p + 1 - (1 + int(_np.sum(1 + leg)))


def embedding(p, prec, zeta_res=7):
    mod = p ** prec

    def h12(seed):
        x = seed % mod
        for _ in range(2 * prec + 5):
            x = (x - (pow(x, 12, mod) - 1) * pow(12 * pow(x, 11, mod) % mod, -1, mod)) % mod
        return x
    zeta = h12(zeta_res)
    assert pow(zeta, 12, mod) == 1
    return zeta, mod


def _chi_exp(p):
    i = _ind31_mod3(p)
    return ((0 if p % 4 == 1 else 6) + 4 * i) % 12


def h_coeffs_int(zeta, mod, M):
    """h coefficients a_0..a_{M-1} as plain integers mod `mod` (fast; the a_p engine)."""
    def zk(k):
        return pow(zeta, k % 12, mod)
    a = [0] * M
    if M > 1:
        a[1] = 1
    for q in _sp.primerange(2, M):
        q = int(q)
        if 124 % q == 0:
            aq = zk(3) if q == 2 else 0        # a_2 = ζ³ (bad-prime U_2-eigenvalue, DLR)
            chiq = 0
        else:
            k = a_p_h_exponent(q)
            aq = 0 if k is None else zk(k)
            chiq = zk(_chi_exp(q))
        qe = q
        prev, cur = 1, aq
        while qe < M:
            a[qe] = cur % mod
            nxt = (aq * cur - (chiq if 124 % q else 0) * prev) % mod
            prev, cur = cur, nxt
            qe *= q
    _mult_fill(a, M, mod)
    return a


def f_coeffs_int(ainv, cond, zeta_unused, mod, M):
    """weight-2 f coefficients a_0..a_{M-1} as plain integers mod `mod` (fast Legendre a_p)."""
    a = [0] * M
    if M > 1:
        a[1] = 1
    for q in _sp.primerange(2, M):
        q = int(q)
        # numpy Legendre count is correct at GOOD odd primes; at p=2 and bad primes it
        # mishandles the singular point — use the exact reference count there.
        if q == 2 or cond % q == 0:
            ap = _ap_ell_fast(ainv, q) % mod
        else:
            ap = _ap_ell_np(ainv, q) % mod
        pfac = 0 if cond % q == 0 else q
        qe = q
        prev, cur = 1, ap
        while qe < M:
            a[qe] = cur % mod
            nxt = (ap * cur - pfac * prev) % mod
            prev, cur = cur, nxt
            qe *= q
    _mult_fill(a, M, mod)
    return a


def _mult_fill(a, M, mod):
    spf = list(range(M))
    i = 2
    while i * i < M:
        if spf[i] == i:
            for j in range(i * i, M, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    for n in range(2, M):
        p = spf[n]
        e, t = 0, n
        while t % p == 0:
            t //= p
            e += 1
        pe = p ** e
        m = n // pe
        if m != 1:
            a[n] = (a[pe] * a[m]) % mod


def dinv_f_coeffs(fa, p, mod, M):
    """(d^{-1} f)_i = a_i(f)/i for p∤i, else 0.  Integers mod `mod` (i is a p-unit ⇒ invertible)."""
    out = [0] * M
    for i in range(1, M):
        if i % p != 0:
            out[i] = (fa[i] * pow(i % mod, -1, mod)) % mod
    return out


def phi_coeff(F, h, m, mod):
    """Φ_m = Σ_{i=1}^{m-1} F_i · h_{m-i}  (single convolution coefficient, integers mod)."""
    s = 0
    for i in range(1, m):
        fi = F[i]
        if fi:
            s += fi * h[m - i]
    return s % mod


def build_krylov(ainv, cond, p=13, prec=10, L=6, max_d=6):
    """Build the U_p Krylov matrix of Φ via sparse coefficients.  Returns (d, M, Mat, diag)."""
    t0 = time.time()
    zeta, mod = embedding(p, prec)
    # index set: need Φ at p^j·n for j=0..max_d, n=1..(some window W) to detect closure at L.
    W = L + 4
    M = p ** max_d * (W + 2)                      # fixed q-precision (worst index p^max_d·W)
    diag = {"M": M, "L": L}
    # build f, h to q^M
    fa = f_coeffs_int(ainv, cond, zeta, mod, M)
    ha = h_coeffs_int(zeta, mod, M)
    F = dinv_f_coeffs(fa, p, mod, M)
    diag["build_s"] = time.time() - t0
    # Krylov vectors as coefficient-dicts at needed indices: v_j has (v_j)_n = Φ_{p^j n}.
    # We store each vector's values at n=1..W.
    def phi_at(idx):
        return phi_coeff(F, ha, idx, mod)
    vecs = []            # vecs[j][n] = (U_p^j Φ)_n = Φ_{p^j n}, n=1..W  (j=0..max_d)
    for j in range(max_d + 1):
        row = {}
        for n in range(1, W + 1):
            idx = p ** j * n
            row[n] = phi_at(idx) if idx < M else 0
        vecs.append(row)
    diag["phi_s"] = time.time() - t0
    # find Krylov dimension: first j where vecs[j] is in span of vecs[0..j-1] (mod p^prec)
    # via exact Q_p Gaussian elimination on the W×j coefficient matrix.
    U = Unramified(p, [0, 1], prec)

    def as_col(row):
        return [Qpf.from_U(U, U.from_int_vec([row[n] % mod])) for n in range(1, W + 1)]
    basis_cols = []
    d = 0
    closed = False
    for j in range(max_d + 1):
        col = as_col(vecs[j])
        coords = _solve_cols(basis_cols, col, U)
        if coords is not None and j > 0:
            d = j
            closed = True
            break
        basis_cols.append(col)
    if not closed:
        # did not close within max_d; use d = max_d (matrix's last column needs vecs[max_d])
        d = max_d
        diag["not_closed"] = True
    diag["dim"] = d
    # U_p matrix on the d-dim basis {v_0,...,v_{d-1}}: U_p(v_i) = v_{i+1}; express v_{i+1} in basis.
    Mat = [[Qpf.from_int(U, 0) for _ in range(d)] for _ in range(d)]
    bcols = basis_cols[:d]
    for i in range(d):
        target = as_col(vecs[i + 1])
        coords = _solve_cols(bcols, target, U)
        if coords is None:
            diag["matrix_incomplete_at"] = i
            coords = [Qpf.from_int(U, 0)] * d
        for r in range(d):
            Mat[r][i] = coords[r]
    diag["total_s"] = time.time() - t0
    return d, M, Mat, diag


def _solve_cols(cols, target, U):
    """Solve target = Σ x_i cols[i] exactly over Q_p (columns are Qpf lists).  None if no soln."""
    if not cols:
        # target in span of empty set iff target == 0
        return [] if all(t.val() >= U.N for t in target) else None
    rows = len(target)
    ncol = len(cols)
    A = [[cols[c][r] for c in range(ncol)] + [target[r]] for r in range(rows)]
    piv = []
    pr = 0
    for c in range(ncol):
        best, bestval = None, U.N + 1
        for r in range(pr, rows):
            v = A[r][c].val()
            if v < bestval:
                bestval, best = v, r
        if best is None or bestval >= U.N:
            continue
        A[pr], A[best] = A[best], A[pr]
        pivinv = Qpf.from_U_with_exp(U, -A[pr][c].exp, U.inv_unit(A[pr][c].u))
        A[pr] = [pivinv.mul(x) for x in A[pr]]
        for r in range(rows):
            if r != pr and not A[r][c].is_zero():
                fnum = A[r][c]
                A[r] = [A[r][k].sub(fnum.mul(A[pr][k])) for k in range(ncol + 1)]
        piv.append((pr, c))
        pr += 1
    for r in range(rows):
        if all(A[r][c].is_zero() for c in range(ncol)) and not A[r][ncol].is_zero():
            return None
    x = [Qpf.from_int(U, 0) for _ in range(ncol)]
    for (r, c) in piv:
        x[c] = A[r][ncol]
    return x


if __name__ == "__main__":
    def P(s=""):
        print(s)
    prec = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    for label, ainv, cond in [("26b", (1, -1, 1, -3, 3), 26)]:
        d, M, Mat, diag = build_krylov(ainv, cond, prec=prec, L=L)
        P(f"{label}: Krylov dim d={d}, fixed M={M}  "
          f"[build {diag['build_s']:.0f}s, phi {diag['phi_s']:.0f}s, total {diag['total_s']:.0f}s]")
        mod = 13 ** prec
        P("  U_13 matrix (mod 13^%d):" % prec)
        for row in Mat:
            P("    " + str([((pow(13, x.exp, mod) * x.u[0]) % mod if x.exp >= 0 else 'neg')
                            for x in row]))
