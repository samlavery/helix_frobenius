"""Build the Katz-basis U_p matrix (Lauder Algorithm 2.1) and GATE it: U_p must close to a
finite matrix on the Katz basis; the spectral projector e_ord = A^{(p-1)p^m} must fix a known
ordinary eigenform and kill a non-ordinary vector.  Only after this gate passes do we apply it
to Φ.  Level N=124, character χ, weight k=1, prime p=13.

Katz basis: for i=0..n, W_i = complementary space in M_{k+i(p-1)}(N,χ) (the new forms not in
E_{p-1}·M_{k+(i-1)(p-1)}); basis element = b / E_{p-1}^i for b ∈ W_i.  U_p acts as a finite
matrix A on this basis.  e_ord = lim U_p^{t!} = A^{(p-1)p^m} (unit-eigenvalue projector).
"""
import time
import sympy as sp
from rung3_katz import eisenstein_pm1, series_inv, series_mul, U_p_series
from rung3_lhs import a_p_h_exponent, _ind31_mod3
from rung3_rhs import Unramified, Qpf
from rung3_krylov import _solve_cols

p = 13
prec = 2               # low precision for the closure gate (agreement-to-precision later)
mod = p ** prec
M = 400                # q-truncation


def h12(s):
    x = s % mod
    for _ in range(2 * prec + 5):
        x = (x - (pow(x, 12, mod) - 1) * pow(12 * pow(x, 11, mod) % mod, -1, mod)) % mod
    return x


zeta = h12(7)


def zk(k):
    return pow(zeta, k % 12, mod)


_g31 = sp.primitive_root(31)
_ind31 = {}
_v = 1
for _e in range(30):
    _ind31[_v % 31] = _e
    _v = _v * _g31 % 31


def chi4(n, e):
    if n % 2 == 0:
        return 0
    return 1 if e == 0 else (1 if n % 4 == 1 else -1)


def chi31(n, e):
    if n % 31 == 0:
        return 0
    return zk(4 * (_ind31[n % 31] * e % 3))


def chi_exp(l):
    i = _ind31_mod3(l)
    return ((0 if l % 4 == 1 else 6) + 4 * i) % 12


def Ek(k, pa, pb, fa, fb):
    """Weight-k Eisenstein series E_k^{ψ,φ}, ψ=chi4^pa·chi31^pb, φ=chi4^fa·chi31^fb."""
    def psi(n):
        return (chi4(n, pa) * chi31(n, pb)) % mod if n % 124 else 0

    def phi(n):
        return (chi4(n, fa) * chi31(n, fb)) % mod if n % 124 else 0
    a = [0] * M
    a[0] = 1
    for n in range(1, M):
        s = 0
        for d in sp.divisors(n):
            s = (s + psi(n // d) * phi(d) * pow(d % mod, k - 1, mod)) % mod
        a[n] = s % mod
    return a


def eisen_span(k):
    """Spanning set of Eisenstein series of weight k, level 124, character χ (all ψφ=χ pairs)."""
    out = []
    for a in [0, 1]:
        for b in [0, 1, 2]:
            c = (1 - b) % 3
            out.append(Ek(k, a, b, (1 - a) % 2, c))
    return out


def _mfill(a):
    spf = list(range(len(a))); i = 2
    while i * i < len(a):
        if spf[i] == i:
            for j in range(i * i, len(a), i):
                if spf[j] == j: spf[j] = i
        i += 1
    for n in range(2, len(a)):
        pp = spf[n]; e, t = 0, n
        while t % pp == 0: t //= pp; e += 1
        pe = pp ** e; m = n // pe
        if m != 1: a[n] = (a[pe] * a[m]) % mod


def weight1_cuspforms():
    """The weight-1 cusp forms h, h' (genuine, all coefficients; a_2=ζ³, a_31=0 placeholder)."""
    def build(conj):
        a = [0] * M; a[1] = 1
        for q in sp.primerange(2, M):
            q = int(q)
            if q == 2:
                aq = zk(3 if not conj else 9); chiq = 0
            elif q == 31:
                aq = 0; chiq = 0
            else:
                k = a_p_h_exponent(q); chiq = zk(chi_exp(q))
                aq = 0 if k is None else (zk(k) * ((-1) ** k if conj else 1)) % mod
            qe = q; pv, cv = 1, aq
            while qe < M:
                a[qe] = cv % mod
                nx = (aq * cv - (chiq if q not in (2, 31) else 0) * pv) % mod
                pv, cv = cv, nx; qe *= q
        _mfill(a)
        return a
    return [build(False), build(True)]


def weight1_eisenstein():
    """Weight-1 Eisenstein series E_1^{ψ,φ}, ψφ=χ.  a_n = Σ_{d|n} ψ(n/d)φ(d); const = combo."""
    return eisen_span(1)


def full_Mk(k, U, cols, cache):
    """A spanning basis of M_k(124,χ) INCLUDING cusp forms, via products of lower-weight forms.
    M_1 = {h, h', wt-1 Eisenstein}; for k≥2, span = {wt-k Eisenstein} ∪ {wt-1 form · wt-(k-1)
    form}, row-reduced.  Products of forms generate the cusp part that Eisenstein-only misses."""
    if k in cache:
        return cache[k]
    if k == 1:
        span = weight1_cuspforms() + weight1_eisenstein()
    else:
        span = list(eisen_span(k))
        w1 = weight1_cuspforms() + weight1_eisenstein()
        lower = full_Mk(k - 1, U, cols, cache)
        for u in w1:
            for lo in lower:
                span.append(series_mul(u, lo, mod, M))
    basis = _cols_reduce(span, U, cols)
    cache[k] = basis
    return basis


def _cols_reduce(vectors, U, cols):
    """Return an independent subset (a basis) of `vectors` at coordinates `cols`."""
    basis = []
    keep = []
    for v in vectors:
        c = [Qpf.from_U(U, U.from_int_vec([v[n] % mod])) for n in cols]
        if _solve_cols([b[1] for b in basis], c, U) is None:
            basis.append((v, c))
            keep.append(v)
    return keep


def main():
    def P(s=""):
        print(s, flush=True)
    t0 = time.time()
    U = Unramified(p, [0, 1], prec)
    cols = list(range(0, 60))
    E12, _ = eisenstein_pm1(p, prec, M)
    E12i = series_inv(E12, mod)

    # n = number of Katz levels for precision m=prec
    n = (p - 1) * (prec + 1) // (p + 1)
    P(f"Katz levels n = {n} (weights 1..{1 + n * (p - 1)}), prec 13^{prec}, q^{M}")

    # classical spaces M_{1+i*12}, i=0..n; complementary spaces W_i
    # W_0 = M_1 = {h, h', weight-1 Eisenstein}; W_i (i>=1) = new forms in M_{1+12i} not in
    # E_12 * M_{1+12(i-1)}.
    prev_space = None
    Wbases = []
    E12ipows = [[1] + [0] * (M - 1)]
    for i in range(1, n + 1):
        E12ipows.append(series_mul(E12ipows[-1], E12, mod, M))

    mk_cache = {}
    for i in range(n + 1):
        wt = 1 + i * (p - 1)
        indep = full_Mk(wt, U, cols, mk_cache)   # FULL M_wt incl. cusp forms (via products)
        # complementary part W_i: forms in M_wt not in E_12 * M_{wt-12}.  For i>=1, remove the
        # E_12-multiples of the previous full space from `indep`.
        if i == 0:
            Wi = indep
        else:
            prevmul = [series_mul(v, E12, mod, M) for v in prev_full]
            combined = _cols_reduce(prevmul + indep, U, cols)
            # the "new" directions are those in combined beyond prevmul's rank
            Wi = [v for v in combined if v not in prevmul]
        Wbases.append(Wi)
        prev_full = indep
        P(f"  weight {wt}: classical(Eisenstein) dim {len(indep)}, complementary W_{i} dim {len(Wi)}")

    # Katz basis: b / E_12^i for b in W_i
    katz = []
    for i, Wi in enumerate(Wbases):
        for b in Wi:
            katz.append(series_mul(b, series_inv(E12ipows[i], mod) if i > 0 else [1] + [0] * (M - 1),
                                   mod, M) if i > 0 else b)
    # simpler: b * E12^{-i}
    katz = []
    E12invpows = [[1] + [0] * (M - 1), E12i]
    for i in range(2, n + 1):
        E12invpows.append(series_mul(E12invpows[-1], E12i, mod, M))
    for i, Wi in enumerate(Wbases):
        for b in Wi:
            katz.append(series_mul(b, E12invpows[i], mod, M))
    D = len(katz)
    P(f"Katz basis dimension D = {D}  [{time.time()-t0:.0f}s]")

    # GATE: does U_p close on the Katz basis?
    kcols = [n for n in range(1, M) if True][:D + 15]
    def col(v):
        return [Qpf.from_U(U, U.from_int_vec([v[nn] % mod])) for nn in kcols]
    katzcols = [col(b) for b in katz]
    inspan = 0
    for b in katz:
        Ub = U_p_series(b, p, M)
        if _solve_cols(katzcols, col(Ub), U) is not None:
            inspan += 1
    P(f"CLOSURE GATE: U_p closes on {inspan}/{D} Katz basis vectors  "
      f"{'[PASS — finite U_p matrix]' if inspan == D else '[FAIL — not U_p-stable]'}  "
      f"[{time.time()-t0:.0f}s]")


if __name__ == "__main__":
    main()
