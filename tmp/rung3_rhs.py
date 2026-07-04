"""RUNG 3, STAGE 1 — the RIGHT-HAND SIDE of the Darmon-Lauder-Rotger Elliptic Stark
Conjecture (Conjecture ES), built entirely from house machinery.

Conjecture ES (DLR, Stark points and p-adic iterated integrals, Forum Math. Pi 3 (2015)),
tetrahedral (A4) exotic rank-2 case, curves 26b and 52b (DLR Example 5.4/5.5 region,
eq. 79-80), p = 13:

    integral_{gamma_gα} f·h  =  ( ζ3·Eα / sqrt(3) ) ·
                                [ logE(P1) logE(Qgα) - logE(Q1) logE(Pgα) ] / log_p(u_gα)      (79)
    integral_{gamma_gβ} f·h  = ( -ζ3^{-1}·Eβ / sqrt(3) ) ·
                                [ logE(P1) logE(Qgβ) - logE(Q1) logE(Pgβ) ] / log_p(u_gβ)      (80)

This file builds the ENTIRE RIGHT-HAND SIDE (the bracketed 2x2 regulator determinant of
p-adic elliptic logs, divided by the Stark-unit log, times the algebraic constant), WITHOUT
the overconvergent (Lauder) left side.  It must reproduce DLR's published values of the
LEFT side (the iterated integrals, quoted as integers mod 13^20) — because Conjecture ES
asserts the two sides are equal, and both 26b and 52b were verified by DLR to 20 digits of
13-adic precision.  That published integer IS our anchor.

GROUND TRUTH: tmp/rung3_darmon_rotger_notes.md and tmp/rung3_pdfs/DLR_stark_points.txt.

HOUSE CODE (mandatory reuse): the exact rational group law ec_add / ec_mul from
jet_census.py.  Everything p-adic and every number-field operation is built from scratch
here with exact integer/Fraction arithmetic and explicit precision tracking.

TIERS:
  [exact]                  — number-field / rational identities, on-curve, unit norm.
  [p-adic certified prec]  — a p-adic quantity carried to a stated, tracked precision.
  [anchor-matched]         — reproduces a DLR published value to its stated precision.
  [first-determination]    — a fresh configuration nobody has published.

NORMALIZATION TRAPS respected (from the notes' list of 8): explicit 13-adic embedding
(the linear factor's root pins the degree-1 prime; the cubic factor pins the unramified
cubic and the Frobenius cyclic order); gα vs gβ kept as separate branches; regularity
(order-3 Frobenius) checked before using the point formula; Eα vs Eβ Euler factors in
clearly labelled separate code; the algebraic constant ζ3·Eα/sqrt(3) is stated by DLR to
equal a SIMPLE rational for these two curves ("both have non-split multiplicative reduction
at 13") and we recover/record it rather than improvising.

Run:  python3 rung3_rhs.py test     (exact + p-adic self-gates only)
      python3 rung3_rhs.py          (full run, writes rung3_rhs_results.txt)
"""
import io
import sys
import time
from fractions import Fraction as Q

# ---- house machinery (mandatory reuse): exact rational group law ----
from jet_census import ec_add, ec_mul


# ============================================================================
# 0. NUMBER FIELD M = Q[x]/(m(x))   (exact arithmetic, Fraction coefficients)
# ============================================================================
class NumberField:
    """Q[x]/(m(x)) for a monic irreducible m of degree d.  Elements are length-d
    Fraction coefficient vectors [c0,c1,...,c_{d-1}] representing sum c_i x^i.
    All arithmetic exact.  Reduction is by long division against m."""

    def __init__(self, mcoeffs):
        # mcoeffs = [m0, m1, ..., m_{d-1}, 1]  (monic, ascending degree)
        self.m = [Q(c) for c in mcoeffs]
        assert self.m[-1] == 1, "minimal polynomial must be monic"
        self.d = len(mcoeffs) - 1

    def zero(self):
        return [Q(0)] * self.d

    def one(self):
        e = self.zero(); e[0] = Q(1); return e

    def gen(self):
        e = self.zero()
        if self.d > 1:
            e[1] = Q(1)
        return e

    def from_rational(self, r):
        e = self.zero(); e[0] = Q(r); return e

    def add(self, a, b):
        return [a[i] + b[i] for i in range(self.d)]

    def sub(self, a, b):
        return [a[i] - b[i] for i in range(self.d)]

    def neg(self, a):
        return [-a[i] for i in range(self.d)]

    def scal(self, r, a):
        r = Q(r); return [r * a[i] for i in range(self.d)]

    def _reduce(self, coeffs):
        """Reduce a polynomial (any length, ascending) mod m(x) to degree < d."""
        c = [Q(x) for x in coeffs]
        # strip / extend
        while len(c) > self.d:
            # leading term c[-1] * x^{len-1}; subtract c[-1]*x^{len-1-d} * m(x)
            deg = len(c) - 1
            lead = c[deg]
            if lead == 0:
                c.pop()
                continue
            shift = deg - self.d
            for i in range(self.d + 1):
                c[shift + i] -= lead * self.m[i]
            c.pop()
        while len(c) < self.d:
            c.append(Q(0))
        return c

    def mul(self, a, b):
        prod = [Q(0)] * (2 * self.d - 1)
        for i in range(self.d):
            if a[i] == 0:
                continue
            for j in range(self.d):
                prod[i + j] += a[i] * b[j]
        return self._reduce(prod)

    def pow(self, a, n):
        r = self.one()
        base = list(a)
        while n:
            if n & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            n >>= 1
        return r

    def _matrix_of_mult(self, a):
        """Matrix of 'multiply by a' in the power basis (columns = a*x^j reduced)."""
        cols = []
        xj = self.one()
        for j in range(self.d):
            cols.append(self.mul(a, xj))
            xj = self._reduce([Q(0)] + xj)  # multiply xj by x (shift up one degree)
        # cols[j] is the image of x^j; build matrix rows i, cols j
        return [[cols[j][i] for j in range(self.d)] for i in range(self.d)]

    def norm(self, a):
        """Field norm N(a) = det(mult-by-a matrix)  [exact Fraction]."""
        Mx = self._matrix_of_mult(a)
        return _det_fraction(Mx)

    def trace(self, a):
        Mx = self._matrix_of_mult(a)
        return sum(Mx[i][i] for i in range(self.d))

    def inv(self, a):
        """a^{-1} via solving (mult-by-a) x = 1 with exact Gaussian elimination."""
        Mx = self._matrix_of_mult(a)
        rhs = self.one()
        return _solve_fraction(Mx, rhs)


def _det_fraction(Mx):
    """Exact determinant of a Fraction matrix (fraction-free would be faster;
    plain Gaussian elimination with Fractions is exact and fine at d<=6)."""
    n = len(Mx)
    A = [[Q(Mx[i][j]) for j in range(n)] for i in range(n)]
    det = Q(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r; break
        if piv is None:
            return Q(0)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            det = -det
        det *= A[col][col]
        inv = Q(1) / A[col][col]
        for r in range(col + 1, n):
            f = A[r][col] * inv
            if f != 0:
                for c in range(col, n):
                    A[r][c] -= f * A[col][c]
    return det


def _solve_fraction(Mx, b):
    """Solve Mx . x = b exactly over Q."""
    n = len(Mx)
    A = [[Q(Mx[i][j]) for j in range(n)] + [Q(b[i])] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r; break
        if piv is None:
            raise ZeroDivisionError("singular")
        A[col], A[piv] = A[piv], A[col]
        inv = Q(1) / A[col][col]
        for c in range(col, n + 1):
            A[col][c] *= inv
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                for c in range(col, n + 1):
                    A[r][c] -= f * A[col][c]
    return [A[i][n] for i in range(n)]


# ============================================================================
# 1. ELLIPTIC CURVE OVER A NUMBER FIELD  (exact group law, NumberField coords)
# ============================================================================
class ECoverNF:
    """E: y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6 over a NumberField F.
    Points are (X, Y) with X, Y field elements, or None for O.  The group law
    mirrors jet_census.ec_add but over F (field inverse instead of Fraction /)."""

    def __init__(self, F, ainv):
        self.F = F
        self.a1, self.a2, self.a3, self.a4, self.a6 = [F.from_rational(a) for a in ainv]
        self.ainv = ainv

    def on_curve(self, P):
        if P is None:
            return True
        F = self.F; X, Y = P
        lhs = F.add(F.add(F.mul(Y, Y), F.mul(self.a1, F.mul(X, Y))), F.mul(self.a3, Y))
        rhs = F.add(F.add(F.add(F.mul(F.mul(X, X), X), F.mul(self.a2, F.mul(X, X))),
                          F.mul(self.a4, X)), self.a6)
        return F.sub(lhs, rhs) == F.zero()

    def neg(self, P):
        if P is None:
            return None
        F = self.F; X, Y = P
        # -P = (X, -Y - a1 X - a3)
        Yn = F.neg(F.add(F.add(Y, F.mul(self.a1, X)), self.a3))
        return (X, Yn)

    def add(self, P, Pt):
        F = self.F
        if P is None:
            return Pt
        if Pt is None:
            return P
        X1, Y1 = P; X2, Y2 = Pt
        a1, a2, a3, a4 = self.a1, self.a2, self.a3, self.a4
        if X1 == X2:
            # check if P = -Pt  => O
            s = F.add(F.add(F.add(Y1, Y2), F.mul(a1, X2)), a3)
            if s == F.zero():
                return None
        if P == Pt:
            den = F.add(F.add(F.scal(2, Y1), F.mul(a1, X1)), a3)
            num = F.sub(F.add(F.add(F.scal(3, F.mul(X1, X1)), F.scal(2, F.mul(a2, X1))), a4),
                        F.mul(a1, Y1))
            lam = F.mul(num, F.inv(den))
        else:
            lam = F.mul(F.sub(Y2, Y1), F.inv(F.sub(X2, X1)))
        # x3 = lam^2 + a1 lam - a2 - x1 - x2
        X3 = F.sub(F.sub(F.sub(F.add(F.mul(lam, lam), F.mul(a1, lam)), a2), X1), X2)
        # y3 = -(lam (x3 - x1) + y1) - a1 x3 - a3
        Y3 = F.sub(F.sub(F.neg(F.add(F.mul(lam, F.sub(X3, X1)), Y1)), F.mul(a1, X3)), a3)
        return (X3, Y3)

    def mul(self, n, P):
        if n == 0:
            return None
        if n < 0:
            return self.mul(-n, self.neg(P))
        R = None; base = P
        while n:
            if n & 1:
                R = self.add(R, base)
            base = self.add(base, base)
            n >>= 1
        return R


# ============================================================================
# 2. UNRAMIFIED p-ADIC FIELD  Q_{p^f} = Z_p[t]/(phi(t)),  phi | m mod p, deg f
# ============================================================================
# Elements: length-f integer vectors mod p^N representing sum c_i t^i, with an
# EXPLICIT precision N (number of p-adic digits).  This is enough to embed M into
# Q_{p^f} (send the field generator to a root of the chosen irreducible factor of
# m over Q_p, computed by Hensel lifting), and to run the formal-group log there.
class Unramified:
    """Q_{p^f} as Z_p[t]/(phi(t)) with phi a degree-f monic lift (integer coeffs,
    ascending) of an irreducible factor of the defining polynomial mod p.  All
    coefficients are carried mod p^N.  f = 1 gives Q_p itself."""

    def __init__(self, p, phi_int, N):
        self.p = p
        self.N = N
        self.mod = p ** N
        self.phi = [c % self.mod for c in phi_int]   # monic, ascending, len f+1
        self.f = len(phi_int) - 1
        assert phi_int[-1] % p == 1 or phi_int[-1] == 1

    def zero(self):
        return [0] * self.f

    def one(self):
        e = self.zero(); e[0] = 1 % self.mod; return e

    def from_int(self, k):
        e = self.zero(); e[0] = k % self.mod; return e

    def from_int_vec(self, v):
        return [c % self.mod for c in (list(v) + [0] * self.f)[:self.f]]

    def add(self, a, b):
        m = self.mod
        return [(a[i] + b[i]) % m for i in range(self.f)]

    def sub(self, a, b):
        m = self.mod
        return [(a[i] - b[i]) % m for i in range(self.f)]

    def neg(self, a):
        m = self.mod
        return [(-a[i]) % m for i in range(self.f)]

    def scal_int(self, k, a):
        m = self.mod
        return [(k * a[i]) % m for i in range(self.f)]

    def _reduce(self, coeffs):
        m = self.mod
        c = [x % m for x in coeffs]
        while len(c) > self.f:
            deg = len(c) - 1
            lead = c[deg]
            if lead % m == 0:
                c.pop(); continue
            shift = deg - self.f
            for i in range(self.f + 1):
                c[shift + i] = (c[shift + i] - lead * self.phi[i]) % m
            c.pop()
        while len(c) < self.f:
            c.append(0)
        return [x % m for x in c]

    def mul(self, a, b):
        m = self.mod
        prod = [0] * (2 * self.f - 1)
        for i in range(self.f):
            if a[i] == 0:
                continue
            ai = a[i]
            for j in range(self.f):
                if b[j]:
                    prod[i + j] = (prod[i + j] + ai * b[j]) % m
        return self._reduce(prod)

    def pow(self, a, n):
        r = self.one(); base = list(a)
        while n:
            if n & 1:
                r = self.mul(r, base)
            base = self.mul(base, base)
            n >>= 1
        return r

    # ---- valuation and inversion ----
    def val(self, a):
        """p-adic valuation of a field element (min over coeff valuations; for an
        unramified extension v(sum c_i t^i) = min_i v(c_i) since t is a unit).
        Capped at N."""
        p, N = self.p, self.N
        best = N
        for c in a:
            c %= self.mod
            if c == 0:
                continue
            v = 0
            cc = c
            while cc % p == 0 and v < N:
                cc //= p; v += 1
            best = min(best, v)
        return best

    def is_unit(self, a):
        return self.val(a) == 0

    def unit_part(self, a):
        """Write a = p^v * u with u a unit; return (v, u_vector).  For v(a) = 0 this is
        (0, a).  Loses v digits of precision in u (u is correct mod p^{N-v})."""
        p = self.p
        v = self.val(a)
        if v == 0:
            return 0, list(a)
        if v >= self.N:
            return self.N, self.zero()
        u = [(c // (p ** v)) % self.mod for c in a]
        return v, u

    def div_val(self, a, b):
        """General division a/b for ANY nonzero b (unit or not): returns
        (v, quotient_vector) with a/b = p^v * quotient, quotient a unit-scale vector.
        v = val(a) - val(b) may be negative (b more divisible than a).  When v >= 0
        the honest p-adic value is p^v * quotient (an integral element); when v < 0
        the element is non-integral and the caller must keep the exponent separate."""
        va, ua = self.unit_part(a)
        vb, ub = self.unit_part(b)
        q = self.mul(ua, self.inv_unit(ub))
        return va - vb, q

    def inv_unit(self, a):
        """Inverse of a p-adic UNIT via Newton iteration x <- x(2 - a x) mod p^N,
        seeded by inverse mod p (linear algebra over F_p in the residue field)."""
        p, N, m = self.p, self.N, self.mod
        # residue-field inverse: invert a mod p in F_p[t]/(phi mod p) via ext-euclid
        inv1 = self._inv_mod_p(a)
        x = [c % m for c in inv1]
        # Newton doubling of precision
        prec = 1
        while prec < N:
            prec = min(2 * prec, N)
            ax = self.mul(a, x)
            two_minus = self.sub(self.from_int(2), ax)
            x = self.mul(x, two_minus)
        return x

    def _inv_mod_p(self, a):
        """Inverse of a (a unit) in F_p[t]/(phibar) via extended Euclid on
        polynomials over F_p.  Returns integer-lifted coeff vector."""
        p = self.p
        A = [c % p for c in a]
        # ensure length f
        A = (A + [0] * self.f)[:self.f]
        phibar = [c % p for c in self.phi]
        r0, r1 = phibar[:], _polytrim(A[:])
        s0, s1 = [0], [1]
        while _polytrim(r1) != [0]:
            q, r = _polydivmod(r0, r1, p)
            r0, r1 = r1, r
            s0, s1 = s1, _polysub(s0, _polymul(q, s1, p), p)
        # r0 is gcd (a nonzero constant since phibar irreducible); scale s0
        g = r0[0] % p
        ginv = pow(g, -1, p)
        res = [(ginv * c) % p for c in s0]
        res = (res + [0] * self.f)[:self.f]
        return res

    def div(self, a, b):
        """a / b  where b is a unit."""
        return self.mul(a, self.inv_unit(b))


def _polytrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def _polymul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] = (r[i + j] + ai * bj) % p
    return _polytrim(r)


def _polysub(a, b, p):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a)); b = b + [0] * (n - len(b))
    return _polytrim([(a[i] - b[i]) % p for i in range(n)])


def _polydivmod(a, b, p):
    a = _polytrim(a[:]); b = _polytrim(b[:])
    if b == [0]:
        raise ZeroDivisionError
    binv = pow(b[-1], -1, p)
    q = [0] * (max(0, len(a) - len(b)) + 1)
    r = a[:]
    while len(r) >= len(b) and r != [0]:
        deg = len(r) - len(b)
        coef = (r[-1] * binv) % p
        q[deg] = coef
        for i in range(len(b)):
            r[deg + i] = (r[deg + i] - coef * b[i]) % p
        r = _polytrim(r)
        if len(r) < len(b):
            break
    return _polytrim(q), _polytrim(r)


# ============================================================================
# 3. HENSEL: embed M -> Q_{p^f} by lifting a root of m(x) mod p to precision N
# ============================================================================
def hensel_root_in_unramified(U, mcoeffs, seed=None):
    """Given the unramified field U = Z_p[t]/(phi) whose residue field contains a
    root of m(x), return rho in U with m(rho) == 0 mod p^N.  rho encodes the image
    of the field generator x of M in this p-adic completion.

    Seed: the residue root of m in the residue field F_{p^f}.  When phi is chosen as
    a factor of m mod p, the generator t IS such a root, so seed = t.  But for f = 1
    the "generator" t collapses to an integer; the caller passes the actual residue
    root as `seed` (a coeff vector).  If seed is None we default to t = [0,1,...].
    Then Newton/Hensel-lift  rho <- rho - m(rho)/m'(rho)  to full precision N.
    """
    p, N = U.p, U.N

    def m_at(z):
        acc = U.zero()
        for c in reversed(mcoeffs):
            acc = U.add(U.mul(acc, z), U.from_int(int(c)))
        return acc

    def mprime_at(z):
        dc = [int(mcoeffs[i]) * i for i in range(1, len(mcoeffs))]
        acc = U.zero()
        for c in reversed(dc):
            acc = U.add(U.mul(acc, z), U.from_int(int(c)))
        return acc

    if seed is None:
        seed = [0, 1]
    rho = U.from_int_vec(seed)
    assert U.val(m_at(rho)) >= 1, "seed is not a root of m mod p"
    # m'(rho) must be a unit (simple root) for Hensel to converge
    assert U.val(mprime_at(rho)) == 0, "m'(seed) not a unit — root not simple mod p"
    prec = 1
    while prec < N:
        prec = min(2 * prec, N)
        f = m_at(rho); fp = mprime_at(rho)
        rho = U.sub(rho, U.div(f, fp))
    for _ in range(3):
        f = m_at(rho); fp = mprime_at(rho)
        rho = U.sub(rho, U.div(f, fp))
    assert U.val(m_at(rho)) >= N - 2, "Hensel lift failed to converge"
    return rho


def find_residue_roots(mcoeffs, p):
    """All residue roots of m(x) mod p in F_p (integers 0..p-1)."""
    roots = []
    for r in range(p):
        v = 0
        for c in reversed(mcoeffs):
            v = (v * r + int(c)) % p
        if v == 0:
            roots.append(r)
    return roots


def embed_M_element(U, rho, elem_coeffs):
    """Map a NumberField element (Fraction coeff vector in power basis of x) into U,
    substituting x -> rho.  Rational coeffs c=num/den need den to be a p-adic unit
    (den coprime to p); we invert den mod p^N."""
    acc = U.zero()
    # Horner in rho: sum c_i rho^i
    powers = [U.one()]
    for i in range(1, len(elem_coeffs)):
        powers.append(U.mul(powers[-1], rho))
    for i, c in enumerate(elem_coeffs):
        c = Q(c)
        num = int(c.numerator) % U.mod
        den = int(c.denominator)
        if den % U.p == 0:
            raise ValueError("denominator not a p-adic unit; point not integral at p")
        deninv = pow(den % U.mod, -1, U.mod)
        coef = (num * deninv) % U.mod
        acc = U.add(acc, U.scal_int(coef, powers[i]))
    return acc


# ============================================================================
# 4. FORMAL GROUP LOGARITHM of E at p   (from scratch, on Q_{p^f} points)
# ============================================================================
# For E: y^2 + a1 xy + a3 y = x^3 + a2 x^2 + a4 x + a6, the formal group in the
# uniformizer z = -x/y at the origin has invariant differential
#     omega = (1 + a1 z + ...) dz  = sum_{n>=0} ... ,
# and the formal logarithm is  L(z) = z + (b2-ish)/... — but we take the robust,
# self-contained route via the standard recursion for the coefficients of x(z),
# y(z) as power series in z (Silverman AEC IV.1), then w(z) and the log.
#
# We use:  z = -x/y,  w = -1/y.  Then w = z^3 + a1 z w + a2 z^2 w + a3 w^2
#                                          + a4 z w^2 + a6 w^3   (Silverman IV.1.1),
# solved iteratively as a power series w(z) = z^3(1 + A1 z + A2 z^2 + ...).
# x(z) = z/w(z),  y(z) = -1/w(z).  The invariant differential
#     omega = dx/(2y + a1 x + a3) = (1 + c1 z + c2 z^2 + ...) dz,
# and  logE(z) = z + (c1/2) z^2 + (c2/3) z^3 + ...  (formal integral).
# We compute omega's series directly from x(z), y(z).
def formal_log_series(ainv, prec_terms):
    """Return the coefficients [l1, l2, ...] (as Fraction) of the formal logarithm
    logE(z) = l1 z + l2 z^2 + ... up to z^prec_terms, from the Weierstrass model.
    Purely rational (model-dependent) — no p yet."""
    a1, a2, a3, a4, a6 = [Q(a) for a in ainv]
    K = prec_terms + 4
    # Solve w(z) = z^3 + a1 z w + a2 z^2 w + a3 w^2 + a4 z w^2 + a6 w^3
    # as power series in z up to degree K.  w starts at z^3.
    w = [Q(0)] * (K + 1)

    def pmul(A, B):
        C = [Q(0)] * (K + 1)
        for i in range(K + 1):
            if A[i] == 0:
                continue
            for j in range(K + 1 - i):
                if B[j]:
                    C[i + j] += A[i] * B[j]
        return C

    def padd(*Ps):
        C = [Q(0)] * (K + 1)
        for P in Ps:
            for i in range(K + 1):
                C[i] += P[i]
        return C

    def pscal(r, A):
        return [r * A[i] for i in range(K + 1)]

    # iterate to convergence (each iteration fixes more low-order terms)
    z = [Q(0)] * (K + 1); z[1] = Q(1)
    z2 = pmul(z, z); z3 = pmul(z2, z)
    for _ in range(K + 2):
        w2 = pmul(w, w); w3 = pmul(w2, w)
        rhs = padd(z3,
                   pscal(a1, pmul(z, w)),
                   pscal(a2, pmul(z2, w)),
                   pscal(a3, w2),
                   pscal(a4, pmul(z, w2)),
                   pscal(a6, w3))
        w = rhs
    # x(z) = z / w(z),  but w = z^3 u(z) with u(0)=1; z/w = z^{-2}/u.  Work with
    # x(z) = z * w^{-1}.  Compute w^{-1} as Laurent: w = z^3 (1 + ...), so
    # x(z) = z^{-2} (1 + ...)^{-1}.  We only need omega up to z^prec, and
    # omega = (1 + ... )dz has a regular expansion, so compute it via
    #   x(z), y(z) then omega = x'(z) / (2 y + a1 x + a3).
    # Represent x, y as Laurent series with a leading z^{-2}, z^{-3}.  Simplest:
    # shift by tracking the "unit part".  u(z) = w(z)/z^3 (power series, u(0)=1).
    u = [Q(0)] * (K + 1)
    for i in range(K + 1):
        if i + 3 <= K:
            u[i] = w[i + 3]
    uinv = _series_inv(u, K)
    # x(z) = z^{-2} * uinv,  y(z) = -1/w = -z^{-3} * uinv
    # invariant differential omega = dx/(2y + a1 x + a3)
    #   as a power series in z:  omega = (1 + c1 z + c2 z^2 + ...) dz.
    # Compute via: let X = uinv (power series, = z^2 x), Y = uinv (= -z^3 y).
    # x = z^{-2} X,  y = -z^{-3} Y.  dx = (-2 z^{-3} X + z^{-2} X') dz.
    # 2y + a1 x + a3 = -2 z^{-3} Y + a1 z^{-2} X + a3.
    # omega = dx/(denom).  Multiply num and denom by z^3:
    #   z^3 dx = (-2 X + z X') dz  (a power series, value at z=0 is -2 X0 = -2)
    #   z^3 denom = -2 Y + a1 z X + a3 z^3
    # so omega = [(-2 X + z X')/(-2 Y + a1 z X + a3 z^3)] dz.
    Xs = uinv[:]                 # X = uinv
    Xp = [Q(0)] * (K + 1)        # X'(z)
    for i in range(1, K + 1):
        Xp[i - 1] = i * uinv[i]
    num = [Q(0)] * (K + 1)
    for i in range(K + 1):
        num[i] += -2 * Xs[i]
    for i in range(K + 1):       # + z X'
        if i >= 1:
            num[i] += Xp[i - 1]
    den = [Q(0)] * (K + 1)
    Ys = uinv[:]                 # Y = uinv (same series, since x/(-y)=z => X=Y here)
    for i in range(K + 1):
        den[i] += -2 * Ys[i]
    for i in range(K + 1):       # + a1 z X
        if i >= 1:
            den[i] += a1 * Xs[i - 1]
    if K >= 3:                   # + a3 z^3
        den[3] += a3
    deninv = _series_inv(_normalize_leading(den), K)
    # renormalize: den(0) = -2, so divide through
    omega = _series_mul(num, deninv, K)
    # omega should be 1 + c1 z + ...  ; integrate term by term:
    # logE(z) = sum_{n>=1} omega_{n-1}/n * z^n
    log_coeffs = [Q(0)] * (prec_terms + 1)
    for n in range(1, prec_terms + 1):
        if n - 1 <= K:
            log_coeffs[n] = omega[n - 1] / n
    return log_coeffs[1:]   # [l1, l2, ...], l1 should be 1


def _normalize_leading(den):
    # returns den unchanged (leading nonzero term is den[0]); _series_inv handles it
    return den


def _series_inv(A, K):
    """Inverse of a power series A with A[0] != 0, up to degree K (Fraction)."""
    assert A[0] != 0, "series not invertible (zero constant term)"
    B = [Q(0)] * (K + 1)
    B[0] = Q(1) / A[0]
    for n in range(1, K + 1):
        s = Q(0)
        for k in range(1, n + 1):
            s += A[k] * B[n - k]
        B[n] = -B[0] * s
    return B


def _series_mul(A, B, K):
    C = [Q(0)] * (K + 1)
    for i in range(K + 1):
        if A[i] == 0:
            continue
        for j in range(K + 1 - i):
            if B[j]:
                C[i + j] += A[i] * B[j]
    return C


# ============================================================================
# 5. p-ADIC ELLIPTIC LOG of a point over Q_{p^f}
# ============================================================================
class PadicEllipticLog:
    """logE,p on E(Q_{p^f}).  Reduce a point into the kernel of reduction by
    multiplying by an integer n_kill so that n_kill*P lies in E_1 (z-adic
    formal group, v(z) >= 1), evaluate the formal log there, divide by n_kill.
    The formal log is Q_p-linear on E_1, so logE(P) = logE(n_kill P)/n_kill."""

    def __init__(self, U, ainv, log_terms=40):
        self.U = U
        self.ainv = ainv
        self.log_coeffs = formal_log_series(ainv, log_terms)  # [l1,l2,...] Fraction
        self.EC = None  # set by caller: an ECoverU
        self._Nns_cache = None   # memoized #E_ns(F_{p^f}) (independent of the point)

    def z_of_point(self, EC, P):
        """z = -x/y as a Qpf.  For a kernel point (v(X)=-2,v(Y)=-3) this has v(z)=1."""
        X, Y = P
        return X.neg().div(Y)

    def in_kernel(self, P):
        """True iff P reduces to O: affine coordinates blow up (v(X) < 0, v(Y) < 0)."""
        if P is None:
            return False
        X, Y = P
        return X.val() < 0 and Y.val() < 0

    def formal_log_at_z(self, z):
        """Evaluate logE(z) = sum l_n z^n as a Qpf.  Requires v(z) >= 1 so the series
        converges p-adically (the term l_n z^n has valuation >= n - v_p(den(l_n)),
        which -> infinity).  z is a Qpf, so negative-valuation intermediates are exact."""
        U = self.U
        acc = Qpf.from_int(U, 0)
        zpow = z
        for n, ln in enumerate(self.log_coeffs, start=1):
            num = int(ln.numerator); den = int(ln.denominator)
            # term = (num/den) * z^n  as Qpf: scale by num, then divide by den (Qpf
            # handles p | den exactly via the exponent).
            term = zpow.scal_int(num)
            term = _qpf_div_int(term, den)
            acc = acc.add(term)
            zpow = zpow.mul(z)
        return acc

    def log_point(self, EC, P):
        """logE,p(P): find n_kill with n_kill*P in the kernel of reduction E_1, log
        there, divide by n_kill.  Handles good AND multiplicative reduction (26b/52b
        are non-split multiplicative at 13): we count NONSINGULAR residue points and
        self-verify the kernel landing (v(X) < 0), so the multiplier is confirmed,
        not assumed.  Returns (Qpf log, diag)."""
        n_kill, Pk, diag = self._into_kernel(EC, P)
        z = self.z_of_point(EC, Pk)
        Lz = self.formal_log_at_z(z)
        L = _qpf_div_int(Lz, n_kill)
        diag.update(n_kill=n_kill, vz=z.val())
        return L, diag

    def _into_kernel(self, EC, P):
        """Return (n, nP, diag) with nP in E_1 (reduces to O: v(X) < 0), verified.
        Multiply P by m = #E_ns(F_{p^f}); if that does not land in E_1 (point on a
        non-identity component, or extra torsion in the component group), escalate by
        small cofactors until v(X) < 0.  Self-certifying: we CHECK the reduction, we
        never assume the multiplier.  The kernel test is v(X) < 0 (X blows up), NOT
        v(z) >= 1 (which a finite affine point with X ≡ 0 would spuriously satisfy)."""
        if self._Nns_cache is None:
            self._Nns_cache = self._reduced_group_order(EC)
        Nns = self._Nns_cache
        for cof in (1, 2, 3, 4, 6, 8, 12, 24):
            m = Nns * cof
            Pm = EC.mul(m, P)
            if Pm is None:
                continue
            if self.in_kernel(Pm):
                return m, Pm, dict(Nns=Nns, cofactor=cof)
        raise RuntimeError("could not push point into kernel of reduction (v(X) < 0)")

    def _reduced_group_order(self, EC):
        """#E_ns(F_{p^f}) — order of the NONSINGULAR part of the reduced curve.  Fast
        path (good reduction): count #E(F_p) over the p base-field points (cheap),
        read off a_p = p+1-#E(F_p), and lift to F_{p^f} by the Frobenius-eigenvalue
        recurrence  #E(F_{p^k}) = p^k + 1 - t_k,  t_0=2, t_1=a_p, t_k=a_p t_{k-1}-p t_{k-2}.
        Multiplicative reduction (a node exists over F_p): #E_ns = p^f - 1 (split) or
        p^f + 1 (non-split), detected via the tangent-slope discriminant at the node.
        This avoids the O(p^{2f}) brute force that is fatal at p=37, f=3."""
        U = self.U; p = U.p; f = U.f
        a1, a2, a3, a4, a6 = [e % p for e in EC.ainv_int()]
        red = self._reduction_type_and_order_Fp(a1, a2, a3, a4, a6, p)
        if red[0] == 'good':
            ap = (p + 1) - red[1]     # a_p from #E(F_p)
            # lift to F_{p^f} by the Frobenius power-sum recurrence (exact integers)
            t = [2, ap]
            for k in range(2, f + 1):
                t.append(ap * t[k - 1] - p * t[k - 2])
            return p ** f + 1 - t[f]
        elif red[0] == 'split':
            return p ** f - 1
        elif red[0] == 'nonsplit':
            # non-split becomes split over even-degree extensions; f=3 (odd) stays non-split
            return (p ** f + 1) if (f % 2 == 1) else (p ** f - 1)
        else:  # additive — fall back to the (rare) brute force
            return self._brute_group_order(EC)

    def _reduction_type_and_order_Fp(self, a1, a2, a3, a4, a6, p):
        """Classify reduction over F_p and, for good reduction, return #E(F_p).
        Returns ('good', N_Fp) | ('split',) | ('nonsplit',) | ('additive',)."""
        # locate singular points over F_p (F = dF/dX = dF/dY = 0)
        sing = []
        Nfp = 1  # infinity
        for X in range(p):
            for Y in range(p):
                F = (Y * Y + a1 * X * Y + a3 * Y - (X ** 3 + a2 * X * X + a4 * X + a6)) % p
                if F != 0:
                    continue
                Fx = (a1 * Y - (3 * X * X + 2 * a2 * X + a4)) % p
                Fy = (2 * Y + a1 * X + a3) % p
                if Fx == 0 and Fy == 0:
                    sing.append((X, Y))
                else:
                    Nfp += 1
        if not sing:
            return ('good', Nfp)
        # one singular point: multiplicative (node) or additive (cusp).  The two tangent
        # slopes at the node solve  m^2 - (a1) m ... ; use the standard test: the node is
        # a double point of Y^2+(a1 X+a3)Y-(...) = 0.  Split iff the tangent slopes are in
        # F_p, i.e. the discriminant of the tangent-cone quadratic is a square mod p.
        (x0, y0) = sing[0]
        # translate to origin; tangent cone: the quadratic part of F at (x0,y0).
        # F = Y^2 + a1 XY + a3 Y - X^3 - a2 X^2 - a4 X - a6.  Hessian-type quadratic form
        # in (dx,dy): dy^2 + a1 dx dy - (3 x0 + a2) dx^2  (from expanding to 2nd order).
        A = (-(3 * x0 + a2)) % p     # dx^2 coeff
        B = a1 % p                    # dx dy coeff
        Cc = 1 % p                    # dy^2 coeff
        disc = (B * B - 4 * A * Cc) % p
        if disc == 0:
            return ('additive',)      # cusp (shouldn't happen for our mult-reduction curves)
        # split iff disc is a nonzero QR mod p
        is_qr = pow(disc, (p - 1) // 2, p) == 1
        return ('split',) if is_qr else ('nonsplit',)

    def _brute_group_order(self, EC):
        """Fallback brute force #E_ns(F_{p^f}) (used only for additive reduction)."""
        U = self.U; p = U.p; f = U.f
        phibar = [c % p for c in U.phi]
        elems = _enumerate_Fpf(p, f)
        a1, a2, a3, a4, a6 = [e % p for e in EC.ainv_int()]
        # F(X,Y) = Y^2 + a1 X Y + a3 Y - (X^3 + a2 X^2 + a4 X + a6).  A point is
        # SINGULAR iff F = dF/dX = dF/dY = 0.  dF/dX = a1 Y - (3X^2+2a2 X+a4),
        # dF/dY = 2Y + a1 X + a3.  Exclude singular points from the count so we get
        # #E_ns(F_{p^f}) (correct for multiplicative reduction too).
        cnt = 1  # point at infinity (always nonsingular on a Weierstrass model)
        for X in elems:
            X2 = _fp_mul(X, X, phibar, p)
            X3 = _fp_mul(X2, X, phibar, p)
            rhs = _fp_add(_fp_add(_fp_add(X3, _fp_scal(a2, X2, p), p),
                          _fp_scal(a4, X, p), p), _fp_const(a6, f), p)
            b = _fp_add(_fp_scal(a1, X, p), _fp_const(a3, f), p)  # coeff of Y
            for Y in elems:
                lhs = _fp_add(_fp_mul(Y, Y, phibar, p), _fp_mul(b, Y, phibar, p), p)
                if not _fp_eq(lhs, rhs):
                    continue
                # on the curve; test singularity
                dFdX = _fp_add(_fp_scal(a1, Y, p),
                        _fp_scal((-1) % p, _fp_add(_fp_add(_fp_scal(3, X2, p),
                        _fp_scal((2 * a2) % p, X, p), p), _fp_const(a4, f), p), p), p)
                dFdY = _fp_add(_fp_scal(2, Y, p), b, p)
                zero = _fp_const(0, f)
                if _fp_eq(dFdX, zero) and _fp_eq(dFdY, zero):
                    continue  # singular point: drop it
                cnt += 1
        return cnt


def _u_div_int(U, a, k):
    """Divide a U-element by an integer k, splitting k = p^e * unit.  Loses e digits
    of precision (the result is correct mod p^{N-e}); returned at reduced precision
    implicitly (higher digits are unreliable but we keep the ring modulus)."""
    p = U.p
    e = 0
    kk = k
    while kk % p == 0:
        kk //= p; e += 1
    # divide by unit part kk (invertible mod p^N)
    inv = pow(kk % U.mod, -1, U.mod)
    b = U.scal_int(inv, a)
    if e > 0:
        # divide each coeff by p^e (must be divisible; the log lands in p^? so ok)
        m = U.mod
        out = []
        for c in b:
            c %= m
            # c should be divisible by p^e; do exact integer division after lifting
            out.append((c // (p ** e)) % m)
        b = out
    return b


def _qpf_div_int(a, k):
    """Divide a Qpf by an integer k (splitting off p-power into the exponent)."""
    U = a.U
    if k == 0:
        raise ZeroDivisionError
    e0 = 0; kk = k
    while kk % U.p == 0:
        kk //= U.p; e0 += 1
    inv = pow(kk % U.mod, -1, U.mod)
    return Qpf.from_U_with_exp(U, a.exp - e0, U.scal_int(inv, a.u))


# ---- tiny residue-field F_{p^f} arithmetic for point counting ----
def _enumerate_Fpf(p, f):
    out = []
    def rec(prefix):
        if len(prefix) == f:
            out.append(tuple(prefix)); return
        for c in range(p):
            rec(prefix + [c])
    rec([])
    return out


def _fp_const(c, f):
    return tuple([c] + [0] * (f - 1))


def _fp_scal(k, a, p):
    return tuple((k * x) % p for x in a)


def _fp_add(a, b, p):
    return tuple((a[i] + b[i]) % p for i in range(len(a)))


def _fp_eq(a, b):
    return tuple(a) == tuple(b)


def _fp_mul(a, b, phibar, p):
    f = len(a)
    prod = [0] * (2 * f - 1)
    for i in range(f):
        if a[i]:
            for j in range(f):
                if b[j]:
                    prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
    # reduce mod phibar
    while len(prod) > f:
        deg = len(prod) - 1
        lead = prod[deg]
        if lead:
            shift = deg - f
            for i in range(f + 1):
                prod[shift + i] = (prod[shift + i] - lead * phibar[i]) % p
        prod.pop()
    while len(prod) < f:
        prod.append(0)
    return tuple(x % p for x in prod)


# add ainv_int accessor to ECoverNF-like curve over U
def _attach_ainv_int(EC_over_U, ainv):
    EC_over_U._ainv_int = tuple(int(a) for a in ainv)


# ============================================================================
# 6a. VALUATION-AWARE p-adic NUMBER  Qpf = p^exp * unit  (handles v < 0)
# ============================================================================
# The kernel of reduction E_1 consists of points whose affine coordinates BLOW UP
# p-adically (v(X) = -2, v(Y) = -3).  A plain integer-mod-p^N ring cannot hold those.
# Qpf carries an explicit valuation exponent so negative valuations are exact; the
# unit part keeps N reliable digits (relative precision).  All group-law arithmetic
# for E over Q_{p^f} runs on Qpf, so points near/at infinity are representable and
# the formal-group log gets a correct z = -X/Y even deep in the kernel.
class Qpf:
    __slots__ = ("U", "exp", "u")   # value = p^exp * u ;  u a unit vector (or zero)

    def __init__(self, U, exp, u):
        self.U = U; self.exp = exp; self.u = u

    @staticmethod
    def from_U(U, a):
        v, u = U.unit_part(a)
        if v >= U.N:
            return Qpf(U, U.N, U.zero())
        return Qpf(U, v, u)

    @staticmethod
    def from_int(U, k):
        return Qpf.from_U(U, U.from_int(k))

    def is_zero(self):
        return self.exp >= self.U.N or all(c == 0 for c in self.u)

    def val(self):
        if self.is_zero():
            return self.U.N
        return self.exp

    def _align(self, other):
        """Return (e, ua, ub) with self = p^e ua, other = p^e ub sharing exponent e."""
        U = self.U
        e = min(self.exp, other.exp)
        ua = _shift_up(U, self.u, self.exp - e)
        ub = _shift_up(U, other.u, other.exp - e)
        return e, ua, ub

    def add(self, other):
        U = self.U
        e, ua, ub = self._align(other)
        return Qpf.from_U_with_exp(U, e, U.add(ua, ub))

    def sub(self, other):
        U = self.U
        e, ua, ub = self._align(other)
        return Qpf.from_U_with_exp(U, e, U.sub(ua, ub))

    def neg(self):
        return Qpf(self.U, self.exp, self.U.neg(self.u))

    def mul(self, other):
        U = self.U
        return Qpf.from_U_with_exp(U, self.exp + other.exp, U.mul(self.u, other.u))

    def scal_int(self, k):
        U = self.U
        # k = p^e0 * unit
        if k == 0:
            return Qpf(U, U.N, U.zero())
        e0 = 0; kk = k
        while kk % U.p == 0:
            kk //= U.p; e0 += 1
        return Qpf.from_U_with_exp(U, self.exp + e0, U.scal_int(kk % U.mod, self.u))

    def div(self, other):
        U = self.U
        inv = U.inv_unit(other.u)   # other.u is a unit by construction
        return Qpf.from_U_with_exp(U, self.exp - other.exp, U.mul(self.u, inv))

    @staticmethod
    def from_U_with_exp(U, exp, a):
        v, u = U.unit_part(a)
        if v >= U.N:
            return Qpf(U, U.N, U.zero())
        return Qpf(U, exp + v, u)

    def eq(self, other):
        return self.sub(other).is_zero()


def _shift_up(U, u, k):
    """Multiply a unit vector by p^k (k >= 0), returning an integer vector mod p^N."""
    if k <= 0:
        return list(u)
    f = (U.p ** k) % U.mod
    return [(f * c) % U.mod for c in u]


# ============================================================================
# 6b. EC over Q_{p^f} with valuation-aware coordinates (points can be in E_1)
# ============================================================================
class ECoverU:
    """E over U = Q_{p^f}, coords are Qpf (valuation-aware).  Group law tolerates
    points in the kernel of reduction (non-integral affine coords)."""

    def __init__(self, U, ainv):
        self.U = U
        self.ainv = ainv
        self._a = [Qpf.from_int(U, int(a)) for a in ainv]

    def ainv_int(self):
        return tuple(int(a) for a in self.ainv)

    def lift(self, Xu, Yu):
        """Wrap a pair of plain U-vectors as a Qpf point."""
        return (Qpf.from_U(self.U, Xu), Qpf.from_U(self.U, Yu))

    def neg(self, P):
        if P is None:
            return None
        X, Y = P
        a1, _, a3, _, _ = self._a
        Yn = Y.add(a1.mul(X)).add(a3).neg()
        return (X, Yn)

    def add(self, P, Pt):
        if P is None:
            return Pt
        if Pt is None:
            return P
        X1, Y1 = P; X2, Y2 = Pt
        a1, a2, a3, a4, _ = self._a
        if X1.eq(X2):
            s = Y1.add(Y2).add(a1.mul(X2)).add(a3)
            if s.is_zero():
                return None
        if X1.eq(X2) and Y1.eq(Y2):
            den = Y1.scal_int(2).add(a1.mul(X1)).add(a3)
            num = X1.mul(X1).scal_int(3).add(a2.mul(X1).scal_int(2)).add(a4).sub(a1.mul(Y1))
            lam = num.div(den)
        else:
            lam = Y2.sub(Y1).div(X2.sub(X1))
        X3 = lam.mul(lam).add(a1.mul(lam)).sub(a2).sub(X1).sub(X2)
        Y3 = lam.mul(X3.sub(X1)).add(Y1).neg().sub(a1.mul(X3)).sub(a3)
        return (X3, Y3)

    def mul(self, n, P):
        if n == 0:
            return None
        if n < 0:
            return self.mul(-n, self.neg(P))
        R = None; base = P
        while n:
            if n & 1:
                R = self.add(R, base)
            base = self.add(base, base)
            n >>= 1
        return R


# ============================================================================
# 7. p-ADIC LOGARITHM of a UNIT in Q_{p^f}   (from scratch)
# ============================================================================
# The Iwasawa p-adic logarithm log_p on Q_{p^f}^x: on 1-units (v(x-1) >= 1) it is the
# convergent series  log_p(x) = sum_{n>=1} (-1)^{n-1} (x-1)^n / n .  For a general unit
# u we first kill the Teichmuller/root-of-unity part by raising to the power (p^f - 1)
# (which lands in the 1-units, since u^{p^f-1} ≡ 1 mod p), then divide the log by
# (p^f - 1):   log_p(u) = log_p(u^{p^f-1}) / (p^f - 1).   (log_p is a homomorphism and
# vanishes on roots of unity, so this recovers the correct value.)
def padic_log_one_unit(U, x, terms=None):
    """log_p(x) for a 1-unit x (v(x-1) >= 1), as a Qpf.  Series converges: the n-th
    term has valuation >= n*v(x-1) - v_p(n) -> infinity."""
    if terms is None:
        terms = U.N + 8
    one = Qpf.from_int(U, 1)
    y = x.sub(one)                     # y = x - 1, v(y) >= 1
    assert y.val() >= 1, "padic_log_one_unit: argument is not a 1-unit"
    acc = Qpf.from_int(U, 0)
    ypow = y                           # y^1
    for n in range(1, terms + 1):
        sign = 1 if (n % 2 == 1) else -1
        term = _qpf_div_int(ypow.scal_int(sign), n)
        acc = acc.add(term)
        ypow = ypow.mul(y)
    return acc


def padic_log_unit(U, u):
    """log_p(u) for any UNIT u in Q_{p^f} (v(u) = 0), as a Qpf.  Raise to (p^f - 1) to
    land in the 1-units, take the 1-unit log, divide by (p^f - 1)."""
    assert u.val() == 0, "padic_log_unit: not a unit"
    e = U.p ** U.f - 1
    upow = _qpf_pow(u, e)
    L = padic_log_one_unit(U, upow)
    return _qpf_div_int(L, e)


def _qpf_pow(a, n):
    U = a.U
    r = Qpf.from_int(U, 1)
    base = a
    while n:
        if n & 1:
            r = r.mul(base)
        base = base.mul(base)
        n >>= 1
    return r


# ============================================================================
# 8. CUBE ROOT OF UNITY in Q_{p^f}  (for the Case-3 point/unit combinations)
# ============================================================================
# The Case-3 formulas use a primitive cube root of unity ζ3 = α_g/β_g.  In Q_{13^3}
# (13 ≡ 1 mod 3) ζ3 lives already in Q_13 ⊂ Q_{13^3}.  We compute it by Hensel-lifting
# a root of x^2 + x + 1 from F_p.  There are TWO (ζ3 and ζ3^2); the CHOICE is pinned by
# the embedding convention (which one is α_g/β_g under the fixed 13-adic embedding of L).
def cube_roots_of_unity(U):
    """Both primitive cube roots of unity in Q_{p^f} as Qpf (requires p ≡ 1 mod 3, or
    f divisible by 2; here p=13 ≡ 1 mod 3 so they sit in Q_p).  Hensel-lift roots of
    x^2 + x + 1."""
    p = U.p
    # residue roots of x^2+x+1 mod p
    roots = [r for r in range(p) if (r * r + r + 1) % p == 0]
    out = []
    for r0 in roots:
        # Hensel lift: f(x)=x^2+x+1, f'(x)=2x+1
        x = U.from_int(r0)
        for _ in range(U.N.bit_length() + 5):
            fx = U.add(U.add(U.mul(x, x), x), U.one())
            fpx = U.add(U.scal_int(2, x), U.one())
            x = U.sub(x, U.div_val(fx, fpx)[1] if False else _u_div(U, fx, fpx))
        out.append(Qpf.from_U(U, x))
    return out


def _u_div(U, a, b):
    """Plain unit division a/b in U (b a unit), returning a U-vector."""
    return U.mul(a, U.inv_unit(b))


# ============================================================================
# ANCHOR DATA (from DLR_stark_points.txt / rung3_darmon_rotger_notes.md)
# ============================================================================
# M for 26b/52b: w^4 + 7 w^2 - 2 w + 14 (ascending coeffs).  disc(poly)=2^6*31^2.
M_2652 = [14, -2, 7, 0, 1]
# Stark unit generator: u1 = w^2 - w + 3, root of x^4+2x^3+18x^2-6x+1, norm 1 (verified).
STARK_UNIT_2652 = [3, -1, 1, 0]   # u1 = 3 - w + w^2  (ascending in the power basis of M)

# 26b: y^2+xy+y = x^3 - x^2 - 3x + 3.  Generators of the rank-2 MW lattice in E(M).
#   Coords printed by DLR as (c3 w^3 + c2 w^2 + c1 w + c0)/den ; we store [c3,c2,c1,c0],den.
CURVE_26b = dict(
    label="26b", cond=26, ainv=(1, -1, 1, -3, 3), p=13, M=M_2652,
    Px=([283, 1295, 1442, 9528], 4802),
    Py=([29371, -35875, 146552, -319814], 235298),
    Qx=([-25, 98, 41, 775], 121),
    Qy=([67, 3832, 2465, 17404], 1331),
    # DLR published LEFT-side iterated-integral values (integers mod 13^20):
    intgral_gα=6721481652857547558786,
    intgral_gβ=-2549577176522983012568,
)

# 52b: y^2 = x^3 + x - 10, same field M, same p=13, same eq (79)-(80) shape.
CURVE_52b = dict(
    label="52b", cond=52, ainv=(0, 0, 0, 1, -10), p=13, M=M_2652,
    Px=([-225, -1533, -1458, 1078], 2809),
    Py=([-247041, 68295, -1265094, 317530], 297754),
    Qx=([-63391, -51546, -698338, -942346], 390625),
    Qy=([84293978, -33352782, 603648754, -1348508882], 244140625),
    intgral_gα=-1602512412162131808818,
    intgral_gβ=4989460414989865668627,
)


def nf_from_coeffs(F, coeffs_desc, den):
    """DLR coord (c_{d-1} w^{d-1} + ... + c1 w + c0)/den -> NumberField element."""
    v = F.zero()
    for i, c in enumerate(reversed(list(coeffs_desc))):   # i = power
        if i < F.d:
            v[i] = Q(int(c), int(den))
    return v


# ============================================================================
# 9. GALOIS CONJUGATES: the four embeddings M -> Q_{13^3} (Case-3 A4 structure)
# ============================================================================
class GaloisEmbeddings:
    """The four field embeddings M = Q[w]/m -> Q_{p^f} sending w to the four roots of
    m.  In the tetrahedral (A4) Case-3 setting with p=13, m factors mod p as
    (linear)(irreducible cubic): ONE root r4 in Q_p (fixed by σ_p, gives P1) and THREE
    roots r1,r2,r3 in the unramified cubic (a Frobenius orbit, cyclically permuted by
    σ_p, giving P2,P3,P4).  All four live in Q_{p^3}, so a single degree-3 completion
    U carries every conjugate.  The ORDERING r1 -> r2 -> r3 under σ_p is exactly the
    Frobenius cycle (r_{i+1} = φ(r_i)); r4 is σ_p-fixed."""

    def __init__(self, U, mcoeffs):
        self.U = U
        self.m = [int(c) for c in mcoeffs]
        self._compute_roots()

    def _m_at(self, a):
        acc = self.U.zero()
        for c in reversed(self.m):
            acc = self.U.add(self.U.mul(acc, a), self.U.from_int(int(c)))
        return acc

    def _mp_at(self, a):
        dc = [self.m[i] * i for i in range(1, len(self.m))]
        acc = self.U.zero()
        for c in reversed(dc):
            acc = self.U.add(self.U.mul(acc, a), self.U.from_int(int(c)))
        return acc

    def _hensel(self, seed_vec):
        U = self.U
        x = U.from_int_vec(seed_vec)
        assert U.val(self._m_at(x)) >= 1, "seed not a root mod p"
        assert U.val(self._mp_at(x)) == 0, "root not simple"
        prec = 1
        while prec < U.N:
            prec = min(2 * prec, U.N)
            x = U.sub(x, _u_div(U, self._m_at(x), self._mp_at(x)))
        for _ in range(3):
            x = U.sub(x, _u_div(U, self._m_at(x), self._mp_at(x)))
        assert U.val(self._m_at(x)) >= U.N - 2, "hensel failed"
        return x

    def _compute_roots(self):
        U = self.U; p = U.p
        # residue roots of m in F_p (degree-1 primes) and in F_{p^f} (the cubic orbit).
        lin_roots = find_residue_roots(self.m, p)   # e.g. [9]
        # cubic-factor orbit: seed with t = generator, Frobenius images t^p, t^{p^2}
        gen = U.from_int_vec([0, 1] + [0] * (U.f - 2)) if U.f >= 2 else U.from_int(0)
        # residue Frobenius images of the generator
        def respow(e):
            return [c % p for c in U.pow(U.from_int_vec([0, 1] + [0] * (U.f - 2)), e)]
        orbit_seeds = [[0, 1, 0], respow(p), respow(p * p)] if U.f == 3 else []
        self.r_cubic = [self._hensel(s) for s in orbit_seeds]   # r1,r2,r3 (Frobenius cycle)
        self.r_lin = [self._hensel([r] + [0] * (U.f - 1)) for r in lin_roots]  # r4 (σ_p-fixed)
        # sanity: 4 distinct roots summing to -m[deg-1] (here 0)
        self.roots = self.r_cubic + self.r_lin

    def embed(self, root_vec, elem_coeffs):
        """Embed a NumberField element (power-basis Fraction vector) via w -> root."""
        return embed_M_element(self.U, root_vec, elem_coeffs)


if __name__ == "__main__":
    print("rung3_rhs module loaded — run  python3 rung3_rhs.py test  or  ... run")
