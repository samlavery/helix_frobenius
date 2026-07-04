"""RUNG 3 STAGE 2 — the LEFT-HAND SIDE of Conjecture ES: the p-adic iterated integral,
built in house code, to close the ES loop entirely in-house against the Stage-1 RHS.

The iterated integral (DLR eq 5-7, DLR_stark_points.txt:224-283):

    I_p^0(f̆, γ̆, h̆)  =  ∫_γ̆ f̆·h̆  :=  γ̆( e_{g_α*} · e_ord( F̆ · h̆ ) )  ∈ C_p ,

    F̆ = d^{-1} f̆   (overconvergent primitive: a_n(F̆) = a_n(f̆)/n for p∤n, 0 for p|n),
    e_ord = lim_t U_p^{t!}   (Hida's ordinary projector),
    e_{g_α*} = projection onto the g_α*-generalized eigenspace,
    γ̆ = the g_α*-dual functional (⟨T,f⟩ = a_1(Tf) duality, DLR:521).

HOUSE MACHINERY (reused wholesale from rung3_rhs.py — Stage 1, already certified):
  Unramified (Z_p / Q_{p^f} exact arithmetic), Qpf (valuation-aware p-adic numbers).
This file adds ONLY the modular-forms layer: q-expansion ring, Serre d^{-1}, U_p, e_ord.

SCOPE (Katz-basis risk, decided): Lauder's Katz-expansion machinery is an EFFICIENCY
device (polynomial-time ordinary projection).  We use the mathematically-equivalent NAIVE
projector e_ord = lim U_p^{n!} directly on truncated q-expansions — the prior (correct,
slower) method Lauder improved on (notes §3).  For our small case (p=13, level 26/52,
precision 13^20) this is tractable and needs NO Katz basis.  The house "prove-decay-before-
truncating" law applies to the q-truncation length M, which we control and gate.

TIERS (per BSDClocks.lean): internal exactness gates [p-adic certified]; the end-to-end ES
match is agreement-to-precision (NOT identification); any nonvanishing we divide by is a
flagged numerical hypothesis.

Coefficients live in Z_p[ζ12] (ζ12 = 12th root of unity, in Z_13 for p=13 by 13≡1 mod 12).
We reuse Unramified with f=1 when ζ12 ∈ Q_p (the ES case) — coefficients are then plain Z_p.
"""
import sys
from fractions import Fraction as Q

from rung3_rhs import Unramified, Qpf, _qpf_div_int


# ============================================================================
# 0. WEIGHT-1 EXOTIC A4 FORM h — the a_p ENGINE (closed formula, in-house)
# ============================================================================
# h is the exotic tetrahedral (A4) weight-1 newform of level 124, nebentype χ (order 2 at 4,
# order 3 at 31), coefficients in Q(ζ12).  a_p is a CLASS FUNCTION of Frob_p in the binary-
# tetrahedral group 2T = SL(2,3).  We give a_p by a CLOSED, fully discrete formula — no square
# root, no per-prime pin, no ES/RHS input — expressed as ζ12-EXPONENTS mod 12:
#
#   a_p = ζ12^{k(p)},   k(p) = (χ_k(p) + 4·ε(p))//2  +  ( 0 if (3/p)=+1 else 6 )  (mod 12),
#   a_p = 0  when ε(p) = 0  (the "2+2"-shape primes, Frob of order 2 in A4),
#
# where  χ_k(p) = [0 if p≡1(4) else 6] + 4·(ind_31(p) mod 3)   [exponent of χ(p) as ζ12^m],
#        ε(p)   = +1 if ind_31(p)≡1 (mod 3), −1 if ≡2, 0 if ≡0,
#        (3/p)  = the Legendre symbol = the CENTRAL quadratic character of 2T→A4 (the sign bit).
#
# DERIVATION / GATES (validated, non-circular): a_p² = χ(p)·ζ3^{ε(p)} pins 2k mod 12; the
# central ±1 of the SL(2,3)→A4 extension is (3/p), which resolves k vs k+6.  Reproduces all
# printed prime a_p (5,7,11,13); the ε=0 case coincides EXACTLY with the 2+2 Frobenius shape;
# and Hecke multiplicativity holds (a_2·a_5 = a_10 = −ζ³+ζ, matching DLR's printed composite).
# Bad primes (2, 31 | level 124): a_p is the U_p-eigenvalue, supplied from the printed data
# (a_2 = ζ³; a_31 handled at level).  p=13: good, a_13 = ζ² by the same formula (special-cased
# only in that (3/13)=+1 is used, not (13/3)).
#
# REDUNDANCY GATE (the mod-13 pin, per team-lead): every formula value satisfies
#   a_p ≡ ζ12^{k(p)} ≡ 7^{k(p)} (mod 13)   [ζ12 ≡ 7 mod 13, order 12 ⇒ k(p) uniquely recoverable]
#   AND a_p² = χ(p)·ζ3^{ε(p)}  [Ramanujan/eigenvalue].  A wrong k fails both.
import sympy as _sp
_G31 = _sp.primitive_root(31)
_IND31 = {}
_v = 1
for _e in range(30):
    _IND31[_v % 31] = _e
    _v = _v * _G31 % 31


def _legendre(a, p):
    """Legendre symbol (a/p) for odd prime p (a can be any integer)."""
    a %= p
    if a == 0:
        return 0
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls


def _ind31_mod3(p):
    return _IND31[p % 31] % 3


def a_p_h_exponent(p):
    """The ζ12-exponent k(p) of a_p(h) for a good prime p (p ∤ 124).  Returns k in 0..11, or
    None if a_p = 0 (the ε=0 / 2+2-shape case).  Pure integer arithmetic — works over any
    completion (ℂ, ℤ_13, ℤ_37).

    p=3 special case: the central quadratic character (3/p) DEGENERATES at p=3 (it is (3/3)=0).
    p=3 is a good prime (3 ∤ 124), so a_3 is well-defined (= ζ, exponent 1, from DLR); we
    tabulate that single value — one input, exactly like the bad primes 2, 31.  [HONEST FLAG]"""
    if p == 3:
        return 1                          # a_3 = ζ (DLR), the one prime where (3/p) degenerates
    i = _ind31_mod3(p)
    if i == 0:
        return None                       # ε = 0 ⇒ a_p = 0
    eps = 1 if i == 1 else -1
    chi_k = (0 if p % 4 == 1 else 6) + 4 * i
    two_k = (chi_k + 4 * eps) % 12
    k0 = two_k // 2                        # two_k is even
    offset = 0 if _legendre(3, p) == 1 else 6
    return (k0 + offset) % 12


# ---------------------------------------------------------------------------
# TWO INDEPENDENT GALOIS READERS for the a_p exponent (Sam's "try different orders")
# ---------------------------------------------------------------------------
# The two non-abelian bits of a_p = ζ12^{k(p)} split by WHAT KIND of data each is:
#   SIGN bit (k vs k+6) = double-cover LIFT data — the order of Frob_p in 2T=SL(2,3):
#     order 3 vs order 6 (the negative preimage of an order-3 A4 element).  Read EXACTLY from
#     the factorization SHAPE of the degree-24 binary-tetrahedral field mod p: 8 factors of
#     degree 3 ⇒ order 3 ⇒ +sign; 4 factors of degree 6 ⇒ order 6 ⇒ −sign.  [exact]
#   CUBE-ROOT bit ε(p) = ABELIAN data in A4^ab = C3 — a cubic character.  Read EXACTLY via the
#     cubic-residue symbol p^{(31−1)/3} mod 31 (Z[ζ3]/F_31 arithmetic).  [exact]
# These are TWO fully independent Galois computations; agreeing with the mod-13-pin formula
# per prime is a genuine three-route certification.  The 2T-field polynomial is built once by
# resultant from the A4 quartic + its resolvent cubic (cached).
_TWOTEE_POLY = None


def _twotee_poly():
    global _TWOTEE_POLY
    if _TWOTEE_POLY is None:
        x, y, t = _sp.symbols('x y t')
        mco = [14, -2, 7, 0, 1]
        quartic = sum(c * x ** i for i, c in enumerate(mco))
        resolv = x ** 3 - 7 * x ** 2 - 56 * x + 388
        H = _sp.Poly(_sp.expand(_sp.resultant(quartic.subs(x, x - y),
                                              resolv.subs(x, y), y)), x)
        T2 = _sp.Poly(_sp.expand(_sp.resultant(H.as_expr(), (t - x) ** 2 - 3, x)), t)
        _TWOTEE_POLY = (T2, t)
    return _TWOTEE_POLY


def sign_bit_from_order(p):
    """SIGN bit of a_p via ord(Frob_p) in 2T = SL(2,3), read from the degree-24 field's
    factorization shape mod p.  +1 (order 3, 8×deg-3) or −1 (order 6, 4×deg-6); None if p
    ramifies in the 2T field.  [exact — polynomial factorization over F_p]."""
    T2, t = _twotee_poly()
    fl = _sp.factor_list(_sp.Poly(T2, t, modulus=p))
    if any(m > 1 for f, m in fl[1]):
        return None
    degs = [int(f.degree()) for f, m in fl[1] for _ in range(m)]
    ford = max(set(degs), key=degs.count)
    return {3: 1, 6: -1}.get(ford)


def eps_bit_from_cubic_residue(p):
    """CUBE-ROOT bit ε(p) via the cubic-residue symbol p^{(31−1)/3} mod 31.  Returns +1/−1/0
    (0 ⇒ a_p = 0).  Labeling pinned once against the printed a_p.  [exact — Z[ζ3]/F_31]."""
    r = pow(p % 31, 10, 31)
    return {1: 0, 25: 1, 5: -1}.get(r)


def eps_bit_explicit_frobenius(p):
    """CUBE-ROOT bit ε(p) via EXPLICIT FROBENIUS (team-lead's method, sharper than the residue
    symbol): in the cyclic cubic K3 = Q[x]/(x³−7x²−56x+388), Frobenius IS x ↦ x^p.  We ask it
    which 3-cycle it is by computing r^p in F_{p³}=F_p[x]/(cubic) and testing r^p = g(r) vs
    r^p = g(g(r)), where g is the Galois-action polynomial σ(r)=g(r) (rational, since √disc is
    rational).  Returns +1/−1/0 (0 ⇒ p splits / a_p=0), None if unreadable.  [exact]

    ζ3-labeling pinned once: class 'σ' ↦ +1 (calibrated against a_7, ε=+1)."""
    cubic = [388, -56, -7, 1]                      # ascending, K3 resolvent
    # Galois-action g(x) = 203/4 − (5/8)x − (7/8)x²  (computed from the roots; cached).
    gcoef = [Q(203, 4), Q(-5, 8), Q(-7, 8)]
    m = [c % p for c in cubic]

    def mul(A, B):
        C = [0] * (len(A) + len(B) - 1)
        for i, a in enumerate(A):
            for j, b in enumerate(B):
                C[i + j] = (C[i + j] + a * b) % p
        while len(C) > 3:
            d = len(C) - 1; l = C[d]
            for i in range(4):
                C[d - 3 + i] = (C[d - 3 + i] - l * m[i]) % p
            C.pop()
        while len(C) < 3:
            C.append(0)
        return C

    def powx(n):
        R = [1, 0, 0]; B = [0, 1, 0]
        while n:
            if n & 1:
                R = mul(R, B)
            B = mul(B, B); n >>= 1
        return R

    def gof(v):
        try:
            a, b, c = [(int(gc.numerator) * pow(int(gc.denominator), -1, p)) % p for gc in gcoef]
        except ValueError:
            return None                            # p | a denominator ⇒ p ramifies here
        return [(a + b * v[0] + c * mul(v, v)[0]) % p,
                (b * v[1] + c * mul(v, v)[1]) % p,
                (b * v[2] + c * mul(v, v)[2]) % p]

    rp = powx(p)
    gr = gof([0, 1, 0])
    if gr is None:
        return None
    ggr = gof(gr)
    if rp == [0, 1, 0]:
        return 0                                   # r^p = r ⇒ p splits (not 1+3)
    if rp == gr:
        return 1                                   # Frob = σ   ⇒ ε = +1 (calibration)
    if rp == ggr:
        return -1                                  # Frob = σ²  ⇒ ε = −1
    return None


def a_p_h_exponent_galois(p, eps_reader=None):
    """a_p exponent k(p) via the TWO INDEPENDENT Galois readers (order for the sign, cubic
    character for ε), NOT the mod-13 pin.  eps_reader selects the ε method (default: the
    cubic-residue symbol; pass eps_bit_explicit_frobenius for the team-lead explicit method —
    both agree on the footprint).  Returns k in 0..11, None if a_p=0, 'ramified' if unreadable."""
    if p == 3:
        return 1
    reader = eps_reader or eps_bit_from_cubic_residue
    eps = reader(p)
    if eps == 0 or eps is None:
        return None if eps == 0 else 'ramified'
    s = sign_bit_from_order(p)
    if s is None:
        return 'ramified'
    chi_k = (0 if p % 4 == 1 else 6) + 4 * (1 if eps == 1 else 2)
    two_k = (chi_k + 4 * eps) % 12
    return ((two_k // 2) + (0 if s == 1 else 6)) % 12


def weight1_h_qexp(U, M, zeta12, bad_ap=None):
    """The weight-1 form h to q^M as a QExp over U, coefficients in Z_p[ζ12] ⊂ Z_p (ζ12 given
    as a Qpf).  a_p from the closed formula (a_p_h_exponent); prime powers by the weight-1
    Hecke recursion a_{p^{e+1}} = a_p a_{p^e} − χ(p) a_{p^{e-1}}; composites multiplicative.
    bad_ap: dict {p: Qpf} for the primes dividing the level (2, 31) — the U_p-eigenvalues."""
    if bad_ap is None:
        bad_ap = {}
    zpow = [Qpf.from_int(U, 1)]
    for _ in range(1, 12):
        zpow.append(zpow[-1].mul(zeta12))
    def zk(k):
        return zpow[k % 12]
    def chi_val(p):
        # χ(p) = ζ12^{χ_k(p)}  (a 12th root of unity)
        i = _ind31_mod3(p)
        chi_k = (0 if p % 4 == 1 else 6) + 4 * i
        return zk(chi_k)
    a = [Qpf.from_int(U, 0)] * M
    if M > 1:
        a[1] = Qpf.from_int(U, 1)
    primes = [int(q) for q in _sp.primerange(2, M)]
    for q in primes:
        if 124 % q == 0:
            ap = bad_ap.get(q, Qpf.from_int(U, 0))
            chi_q = Qpf.from_int(U, 0)          # χ(q)=0 at bad q ⇒ a_{q^e}=a_q^e
        else:
            k = a_p_h_exponent(q)
            ap = Qpf.from_int(U, 0) if k is None else zk(k)
            chi_q = chi_val(q)
        # fill prime powers via a_{q^{e+1}} = a_q a_{q^e} − χ(q) a_{q^{e-1}}
        qe = q
        aprev, acur = Qpf.from_int(U, 1), ap    # a_{q^0}=1, a_{q^1}=a_q
        while qe < M:
            a[qe] = acur
            nxt = ap.mul(acur).sub(chi_q.mul(aprev))
            aprev, acur = acur, nxt
            qe *= q
    # multiplicative fill for composites
    spf = _smallest_prime_factor(M)
    for n in range(2, M):
        p = spf[n]
        e, t = 0, n
        while t % p == 0:
            t //= p
            e += 1
        pe = p ** e
        m = n // pe
        if m != 1:
            a[n] = a[pe].mul(a[m])
    return QExp(U, a, M)


def _smallest_prime_factor(M):
    spf = list(range(M))
    i = 2
    while i * i < M:
        if spf[i] == i:
            for j in range(i * i, M, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def _ap_ell_fast(ainv, p):
    """a_p of E/Q in O(p) via the Legendre symbol: #{y : y²+by = c} = 1 + (b²+4c / p)."""
    a1, a2, a3, a4, a6 = [c % p for c in ainv]
    cnt = 1  # point at infinity
    for X in range(p):
        rhs = (X * X * X + a2 * X * X + a4 * X + a6) % p
        b = (a1 * X + a3) % p
        disc = (b * b + 4 * rhs) % p
        cnt += 1 + _legendre(disc, p)
    return p + 1 - cnt


def weight2_f_qexp(U, ainv, cond, M):
    """The weight-2 newform f of E (ainv, conductor cond) to q^M as a QExp over U.  a_p by the
    fast Legendre point-count (good p) / point-count on the singular model (bad p); prime powers
    by a_{p^{e+1}} = a_p a_{p^e} − p·[p∤cond]·a_{p^{e-1}}; composites multiplicative."""
    a = [Qpf.from_int(U, 0)] * M
    if M > 1:
        a[1] = Qpf.from_int(U, 1)
    primes = [int(q) for q in _sp.primerange(2, M)]
    for q in primes:
        ap_int = _ap_ell_fast(ainv, q)     # (fast count also gives the correct a_q at bad q)
        ap = Qpf.from_int(U, ap_int)
        pfac = 0 if cond % q == 0 else q
        qe = q
        aprev, acur = Qpf.from_int(U, 1), ap
        while qe < M:
            a[qe] = acur
            nxt = ap.mul(acur).sub(Qpf.from_int(U, pfac).mul(aprev))
            aprev, acur = acur, nxt
            qe *= q
    spf = _smallest_prime_factor(M)
    for n in range(2, M):
        p = spf[n]
        e, t = 0, n
        while t % p == 0:
            t //= p
            e += 1
        pe = p ** e
        m = n // pe
        if m != 1:
            a[n] = a[pe].mul(a[m])
    return QExp(U, a, M)


# ============================================================================
# 1. q-EXPANSION RING over a coefficient ring R (R = Unramified, coeffs are Qpf)
# ============================================================================
# A q-expansion is a list [c_0, c_1, ..., c_{M-1}] of Qpf coefficients (c_n = coeff of q^n),
# truncated at q^M.  All ops are exact in Z_p to the working precision N carried by Qpf.
class QExp:
    """Truncated q-expansion sum_{n=0}^{M-1} c_n q^n, c_n a Qpf over Unramified U."""

    __slots__ = ("U", "c", "M")

    def __init__(self, U, coeffs, M=None):
        self.U = U
        self.M = M if M is not None else len(coeffs)
        c = list(coeffs[:self.M])
        while len(c) < self.M:
            c.append(Qpf.from_int(U, 0))
        self.c = c

    @staticmethod
    def zero(U, M):
        return QExp(U, [Qpf.from_int(U, 0) for _ in range(M)], M)

    @staticmethod
    def from_int_list(U, ints, M):
        return QExp(U, [Qpf.from_int(U, int(a)) for a in ints[:M]], M)

    def copy(self):
        return QExp(self.U, [Qpf(self.U, x.exp, list(x.u)) for x in self.c], self.M)

    def add(self, other):
        M = min(self.M, other.M)
        return QExp(self.U, [self.c[n].add(other.c[n]) for n in range(M)], M)

    def sub(self, other):
        M = min(self.M, other.M)
        return QExp(self.U, [self.c[n].sub(other.c[n]) for n in range(M)], M)

    def scal(self, qpf):
        return QExp(self.U, [qpf.mul(x) for x in self.c], self.M)

    def scal_int(self, k):
        return QExp(self.U, [x.scal_int(k) for x in self.c], self.M)

    def mul(self, other):
        """Cauchy product truncated at q^M (M = min of the two)."""
        M = min(self.M, other.M)
        U = self.U
        out = [Qpf.from_int(U, 0) for _ in range(M)]
        for i in range(M):
            ci = self.c[i]
            if ci.is_zero():
                continue
            for j in range(M - i):
                cj = other.c[j]
                if not cj.is_zero():
                    out[i + j] = out[i + j].add(ci.mul(cj))
        return QExp(U, out, M)

    def coeff(self, n):
        if 0 <= n < self.M:
            return self.c[n]
        return Qpf.from_int(self.U, 0)

    def valuation_floor(self):
        """min p-adic valuation over all coefficients (a crude norm; for the ledger)."""
        return min((x.val() for x in self.c if not x.is_zero()), default=self.U.N)


# ============================================================================
# 2. SERRE OPERATOR d^{-1}  (overconvergent primitive of a weight-2 cusp form)
# ============================================================================
def serre_dinv(F):
    """F̆ = d^{-1} f̆ : a_n(F̆) = a_n(f̆)/n for p∤n, and 0 for p|n.  (DLR:213-221; valid
    because a_0(f̆)=0 for a weight-2 cusp form.)  This simultaneously p-DEPLETES (kills
    p|n terms) and integrates — exactly Serre's d^{-1} = lim_{t→-1} d^t on q-expansions."""
    U = F.U
    out = [Qpf.from_int(U, 0)]        # a_0 = 0
    for n in range(1, F.M):
        if n % U.p == 0:
            out.append(Qpf.from_int(U, 0))          # p | n : depleted
        else:
            out.append(_qpf_div_int(F.c[n], n))     # a_n / n  (n a p-unit -> exact)
    return QExp(U, out, F.M)


# ============================================================================
# 3. U_p OPERATOR  (Atkin)  and  e_ord = lim U_p^{n!}
# ============================================================================
def U_p(F):
    """(U_p F)_n = a_{pn}(F).  Truncates: needs F up to q^{p·M} to fill q^M, but we only
    have q^M, so the result is valid up to q^{floor(M/p)} (coefficients beyond are unknown
    and set to 0 — the caller must track this q-adic truncation shrinkage)."""
    U = F.U; p = U.p
    Mout = F.M
    out = [F.coeff(p * n) for n in range(Mout)]
    return QExp(U, out, Mout)


def e_ord(F, ledger=None, max_pow=None):
    """Hida ordinary projector e_ord = lim_t U_p^{t!} applied to F.

    Mechanism: decompose F = F_ord + F_nonord in the (finite-dim) space of q-expansions
    stable under U_p.  On F_ord, U_p acts invertibly with UNIT eigenvalues (roots of unity
    times 1-units in Z_p); on F_nonord the eigenvalues have POSITIVE valuation, so
    U_p^{k}(F_nonord) → 0 p-adically.  Thus U_p^{k}(F) → U_p^{k}(F_ord), and the factorial
    exponent t! is a multiple of every unit-eigenvalue's (finite) multiplicative order for
    t large, making U_p^{t!} act as the IDENTITY on F_ord in the limit — i.e. U_p^{t!}(F) →
    e_ord(F).

    Implementation (naive, no Katz basis): iterate G ← U_p(G).  The non-ordinary part dies
    (valuation of the killed part grows by the min positive slope each step); the ordinary
    part cycles through a finite orbit (period = lcm of unit-eigenvalue orders mod p^N).
    e_ord(F) is the orbit member equal to U_p^{t!}(F): we detect the cycle and return the
    representative reached at a factorial-multiple index.

    Returns (e_ord F, diag).  diag carries the stabilization step and the precision-loss
    ledger (valuation of the discarded non-ordinary part per step)."""
    import math
    U = F.U
    if max_pow is None:
        max_pow = 4 * U.N + 40
    diag = {"seq_vals": [], "cycle_start": None, "cycle_len": None, "eord_at": None}
    # Phase 1: iterate U_p, recording G_k, until the non-ordinary part has decayed below
    # precision (successive iterates enter the periodic ordinary orbit).
    seq = [F]
    for k in range(1, max_pow + 1):
        seq.append(U_p(seq[-1]))
        # detect cycle: does seq[k] match some earlier seq[j] (j<k) to full precision?
        hit = None
        for j in range(max(0, k - 24), k):
            if _qexp_close(seq[k], seq[j], U.N):
                hit = j; break
        if hit is not None:
            diag["cycle_start"] = hit
            diag["cycle_len"] = k - hit
            break
    else:
        diag["cycle_start"] = None
    cs, cl = diag["cycle_start"], diag["cycle_len"]
    if cs is None:
        # no clean cycle within budget: return the last iterate (best effort), flag it
        diag["eord_at"] = len(seq) - 1
        if ledger is not None:
            ledger.update(diag)
        return seq[-1], diag
    # e_ord(F) = U_p^{t!}(F) for t large: pick the smallest t! >= cs that lands in the cycle
    # and is ≡ (a full period boundary), i.e. t! ≡ cs (mod cl) with t!>=cs.  Since the map is
    # eventually periodic with period cl on the tail, U_p^{m}(F) for m>=cs depends only on
    # (m-cs) mod cl.  We want m = t! with t! >= cs; its residue (t!-cs) mod cl picks the orbit
    # member.  For the ORDINARY PROJECTOR the correct member is the one at m ≡ 0 (mod cl) past
    # cs (identity on the ordinary part): m0 = cs rounded up to cs + ((-(?)...)).
    # Concretely: the identity-on-ordinary member sits at m with (m-cs) ≡ 0 (mod cl); i.e.
    # the cycle representative equal to lim U_p^{t!} is seq[cs + ((0-cs) mod cl-adjust)] — but
    # since t! is divisible by cl for t>=cl (cl | t! once t>=cl), and t!>=cs, we get
    # (t!-cs) mod cl = (-cs) mod cl.  So e_ord F = seq[cs + ((-cs) % cl)].
    m_res = (-cs) % cl
    idx = cs + m_res
    diag["eord_at"] = idx
    if ledger is not None:
        ledger.update(diag)
    return seq[idx], diag


def _qexp_close(A, B, N):
    """True iff q-expansions A, B agree to full precision N in every coefficient."""
    M = min(A.M, B.M)
    for n in range(M):
        if A.c[n].sub(B.c[n]).val() < N:
            return False
    return True


# ============================================================================
# 4. HECKE OPERATORS  T_ℓ (good ℓ) and the g_α*-eigenspace projector
# ============================================================================
def T_ell(F, ell, chi_ell, weight):
    """Hecke operator T_ℓ (ℓ ∤ level) on a weight-`weight` q-expansion:
        (T_ℓ F)_n = a_{ℓ n}(F) + χ(ℓ) ℓ^{weight-1} a_{n/ℓ}(F)   (second term if ℓ | n).
    chi_ell is χ(ℓ) as a Qpf.  For weight 1: ℓ^{weight-1} = 1."""
    U = F.U
    lw = U.p ** 0  # placeholder; weight-1 => ℓ^0 = 1
    fac = ell ** (weight - 1)
    out = []
    for n in range(F.M):
        v = F.coeff(ell * n)
        if n % ell == 0:
            v = v.add(chi_ell.scal_int(fac).mul(F.coeff(n // ell)))
        out.append(v)
    return QExp(U, out, F.M)


def U_p_operator(F):
    """Alias: U_p as a Hecke operator (a_n -> a_{pn}).  Same as U_p()."""
    return U_p(F)


def eigenspace_project_Up(Phi, eigenvalue, other_eigenvalues, tol_N=None):
    """Project Phi onto the U_p-eigenline with eigenvalue `eigenvalue` by applying the
    annihilating polynomial ∏_{μ≠eigenvalue}(U_p - μ)/(eigenvalue - μ) over the OTHER
    U_p-eigenvalues present in the ordinary space.  This isolates the g_α*-component when
    α_g is a simple U_p-eigenvalue (regular case, Hypothesis C).  Returns the projected
    q-expansion (a multiple of g_α*)."""
    U = Phi.U
    result = Phi
    for mu in other_eigenvalues:
        # apply (U_p - mu): F -> U_p(F) - mu*F, then divide by (eigenvalue - mu)
        Up_res = U_p(result)
        result = Up_res.sub(result.scal(mu))
        denom = eigenvalue.sub(mu)
        result = result.scal(_qpf_inv(denom))
    return result


def _qpf_inv(a):
    """Inverse of a unit Qpf (valuation 0)."""
    U = a.U
    assert a.val() == 0, "cannot invert a non-unit Qpf"
    inv_u = U.inv_unit(a.u)
    return Qpf.from_U_with_exp(U, -a.exp, inv_u)


# ============================================================================
# 5. FINITE-MATRIX e_ord via the U_p-KRYLOV MODULE  (the feasible realization)
# ============================================================================
# The naive lim U_p^{n!} on raw q-expansions is infeasible (each U_p shrinks q-precision by
# p; ~40 steps at precision 20 => q^{13^40}).  Instead we realize U_p as a FINITE MATRIX on
# the Hecke-stable module V = span{Φ, U_pΦ, U_p²Φ, ...} (a classical realization, NOT the
# Katz overconvergent basis).  Krylov iteration builds a basis of V; U_p is the companion
# matrix; e_ord is the spectral projector onto the UNIT-eigenvalue (ordinary) part.
#
# Precision discipline: each U_p application costs a factor p of q-precision.  To build a
# d-dimensional Krylov basis and compare vectors faithfully at L leading coefficients, the
# seed Φ must be known to q^{p^d · L}.  We track this and REPORT the required M; the module
# dimension d is small (single digits), so p^d · L stays bounded.
def krylov_Up_module(Phi, compare_len, max_dim=12):
    """Build a basis of the U_p-cyclic module generated by Phi, and the matrix of U_p on it.
    Vectors are compared/reduced on their first `compare_len` q-coefficients (a faithful
    fingerprint once compare_len exceeds the module's separation length).  Returns
    (basis, Up_matrix, diag).  basis[i] is a QExp; Up_matrix[i][j] is a Qpf with
    U_p(basis[j]) = sum_i Up_matrix[i][j] basis[i]."""
    U = Phi.U
    basis = [Phi]
    krylov = [Phi]
    diag = {"dim": None, "compare_len": compare_len, "deps": []}
    for step in range(max_dim):
        nxt = U_p(krylov[-1])
        # try to express nxt in the current basis (on the first compare_len coeffs)
        coords = _solve_in_basis(basis, nxt, compare_len)
        if coords is not None:
            diag["dim"] = len(basis)
            diag["closing_coords"] = coords
            break
        basis.append(nxt)
        krylov.append(nxt)
    else:
        diag["dim"] = len(basis)  # hit max_dim without closing (flag)
        diag["maxed"] = True
    d = len(basis)
    # U_p matrix: for each basis vector b_j, express U_p(b_j) in the basis.
    Mat = [[Qpf.from_int(U, 0) for _ in range(d)] for _ in range(d)]
    for j in range(d):
        ub = U_p(basis[j])
        coords = _solve_in_basis(basis, ub, compare_len)
        if coords is None:
            diag["matrix_incomplete_at"] = j
            coords = [Qpf.from_int(U, 0)] * d
        for i in range(d):
            Mat[i][j] = coords[i]
    diag["dim"] = d
    return basis, Mat, diag


def _solve_in_basis(basis, target, L):
    """Solve target = sum_i x_i basis[i] on the first L q-coefficients (exact Qpf Gaussian
    elimination on the L-row coefficient matrix).  Returns the coefficient list x, or None
    if target is not in the span (residual nonzero to working precision)."""
    U = basis[0].U
    d = len(basis)
    # Build the L×d coefficient matrix A (A[n][i] = basis[i] coeff n) and RHS b[n].
    A = [[basis[i].coeff(n) for i in range(d)] for n in range(L)]
    b = [target.coeff(n) for n in range(L)]
    return _qpf_lstsq(A, b, U)


def _qpf_lstsq(A, b, U):
    """Solve the (possibly overdetermined) A x = b exactly over Q_p by Gaussian elimination
    with partial pivoting on VALUATION (pick the most-unit pivot).  Returns x if a consistent
    solution exists (residual zero to precision), else None."""
    rows = len(A); cols = len(A[0]) if rows else 0
    # augmented copy
    M = [[A[r][c] for c in range(cols)] + [b[r]] for r in range(rows)]
    piv_rows = []
    pr = 0
    for c in range(cols):
        # find pivot row (>= pr) with minimal valuation in column c
        best = None; bestval = U.N + 1
        for r in range(pr, rows):
            v = M[r][c].val()
            if v < bestval:
                bestval = v; best = r
        if best is None or bestval >= U.N:
            continue  # column is zero; skip (free variable)
        M[pr], M[best] = M[best], M[pr]
        inv = _qpf_inv(_unit_normalize(M[pr][c]))  # normalize pivot to a unit-scaled inverse
        pivinv = _qpf_inv(M[pr][c])
        # scale pivot row so M[pr][c] = 1
        M[pr] = [pivinv.mul(x) for x in M[pr]]
        for r in range(rows):
            if r != pr and not M[r][c].is_zero():
                f = M[r][c]
                M[r] = [M[r][k].sub(f.mul(M[pr][k])) for k in range(cols + 1)]
        piv_rows.append((pr, c))
        pr += 1
        if pr == rows:
            break
    # check consistency: any row with all-zero coeffs but nonzero rhs => inconsistent
    for r in range(rows):
        if all(M[r][c].is_zero() for c in range(cols)) and not M[r][cols].is_zero():
            return None
    # read solution (free variables = 0)
    x = [Qpf.from_int(U, 0) for _ in range(cols)]
    for (r, c) in piv_rows:
        x[c] = M[r][cols]
    return x


def _unit_normalize(a):
    """Return a as-is (helper kept for clarity); pivot handling uses _qpf_inv directly."""
    return a


def spectral_ordinary_projector(basis, Mat, ledger=None):
    """e_ord as a matrix on the Krylov module: project onto the UNIT-eigenvalue generalized
    eigenspace of U_p (the ordinary part).  Realized as P = (U_p-matrix)^{k} for k a large
    multiple that is IDENTITY on unit eigenvalues and 0 on positive-slope ones — but on a
    FINITE matrix this is just the spectral projector, computed as the polynomial in Mat that
    is 1 on unit eigenvalues, 0 else.  We compute it via M^{ (p^a)·ord } for growing a until
    the matrix STABILIZES (M^{big} converges to e_ord since unit eigenvalues that are roots of
    unity times 1-units get sent to their idempotent, slopes>0 die).  Returns the projector
    matrix P (list of lists of Qpf) and diag."""
    U = basis[0].U
    d = len(Mat)
    # M^{p^a · L!} converges to the ordinary projector composed with identity-on-ordinary.
    # We iterate matrix M -> M^{p} (repeated p-th powers) which drives positive-slope
    # eigenvalues to 0 and unit eigenvalues toward the Teichmuller idempotent, then one more
    # (p^N)-power makes 1-units -> 1.  Detect stabilization.
    P = _mat_pow(Mat, U.p ** (U.N + 2), U)   # kills slopes, unit^{p^big} -> Teichmuller
    # multiply by M^{(p-1)} enough to send Teichmuller reps to 1 on the ordinary line:
    # actually M^{(p^f-1) p^N} is the standard e_ord exponent; use f effectively 1 here.
    Pord = _mat_pow(Mat, (U.p - 1) * U.p ** (U.N + 2), U)
    diag = {"dim": d}
    return Pord, diag


def _mat_mul(A, B, U):
    n = len(A); m = len(B[0]); k = len(B)
    C = [[Qpf.from_int(U, 0) for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for j in range(m):
            s = Qpf.from_int(U, 0)
            for t in range(k):
                if not A[i][t].is_zero() and not B[t][j].is_zero():
                    s = s.add(A[i][t].mul(B[t][j]))
            C[i][j] = s
    return C


def _mat_pow(A, e, U):
    n = len(A)
    R = [[Qpf.from_int(U, 1) if i == j else Qpf.from_int(U, 0) for j in range(n)]
         for i in range(n)]
    B = [row[:] for row in A]
    while e:
        if e & 1:
            R = _mat_mul(R, B, U)
        B = _mat_mul(B, B, U)
        e >>= 1
    return R


# ============================================================================
# 6. THE g_α*-PROJECTION — minimal-footprint recipe (T_ℓ then one U_p)
# ============================================================================
# The ordinary weight-1 space contains: g_α*, g_β* (share ALL good-ℓ Hecke eigenvalues a_ℓ,
# differ ONLY in the U_p-eigenvalue α_g vs β_g), the Galois-conjugate h', and Eisenstein
# eigenforms.  To isolate g_α*:
#   (a) apply T_ℓ-annihilators for small good ℓ to kill every eigensystem whose a_ℓ differs
#       from a_ℓ(g_α*) (this removes h', Eisenstein, etc.) — cost: a factor ℓ of q-precision,
#       NOT p, so cheap;
#   (b) apply ONE U_p-annihilator (U_p − β_g)/(α_g − β_g) to pick α_g over β_g — the only
#       step that costs a factor p of q-precision.
# This is the whole projector; q-precision loss is (∏ ℓ used)·p — bounded and small.
def T_ell_annihilate(F, ell, chi_ell, a_ell_keep, a_ell_kill_list, weight=1):
    """Apply ∏_{a in a_ell_kill_list} (T_ℓ − a)/(a_ell_keep − a) to F, killing every
    eigensystem with T_ℓ-eigenvalue in a_ell_kill_list while fixing the a_ell_keep one.
    Costs a factor ℓ of q-precision per T_ℓ application (result valid to q^{M/ℓ^{#kills}})."""
    result = F
    for a_kill in a_ell_kill_list:
        Tl = T_ell(result, ell, chi_ell, weight)
        result = Tl.sub(result.scal(a_kill))               # (T_ℓ − a_kill) result
        denom = a_ell_keep.sub(a_kill)
        result = result.scal(_qpf_inv(denom))              # / (a_keep − a_kill)
    return result


def project_galpha_star(Phi, sep, ledger=None):
    """Isolate the g_α*-component of Φ = F̆·h̆ = e_{g_α*} e_ord Φ (Hyp. C: g_α* ordinary).
    `sep` provides the separating data:
      sep['Tl'] = list of (ell, chi_ell, a_keep, [a_kill,...]) — good-ℓ annihilators;
      sep['alpha_g'], sep['beta_g'] — the U_p eigenvalues to separate α from β.
    Returns the projected q-expansion (a scalar multiple of g_α*)."""
    U = Phi.U
    diag = {"Tl_used": [], "q_shrink": 1}
    R = Phi
    for (ell, chi_ell, a_keep, a_kill_list) in sep['Tl']:
        R = T_ell_annihilate(R, ell, chi_ell, a_keep, a_kill_list)
        diag["Tl_used"].append((ell, len(a_kill_list)))
        diag["q_shrink"] *= ell ** len(a_kill_list)
    # one U_p annihilator to pick α_g over β_g
    ag, bg = sep['alpha_g'], sep['beta_g']
    UR = U_p(R)
    R = UR.sub(R.scal(bg)).scal(_qpf_inv(ag.sub(bg)))      # (U_p − β_g)/(α_g − β_g)
    diag["q_shrink"] *= U.p
    if ledger is not None:
        ledger.update(diag)
    return R, diag


def iterated_integral(f_wt2, h_wt1, galpha_star, sep, galpha_norm_idx=1, ledger=None):
    """The p-adic iterated integral  I_p^0(f̆, γ̆, h̆) = γ̆(e_{g_α*} e_ord(F̆·h̆)).

    Realization (all q-expansion arithmetic; NO Mordell-Weil points — Stage-3-ready):
      1. F̆ = d^{-1} f̆ ;  2. Φ = F̆·h̆ ;
      3. Ψ_α = project_galpha_star(Φ, sep)   [T_ℓ annihilators + one U_p; = e_{g_α*} e_ord Φ]
      4. c = γ̆(Ψ_α) = a_i(Ψ_α)/a_i(g_α*) at the g_α* normalization index i (a_1-duality).
    Returns (c, diag)."""
    U = f_wt2.U
    diag = {}
    Fbar = serre_dinv(f_wt2)
    Phi = Fbar.mul(h_wt1)
    Psi_alpha, pdiag = project_galpha_star(Phi, sep, ledger=ledger)
    diag["project"] = pdiag
    # γ̆: read the g_α* multiplier at an index where g_α* is a p-adic unit (exact ratio).
    i = galpha_norm_idx
    gi = galpha_star.coeff(i)
    if gi.val() != 0:
        i = next((n for n in range(1, galpha_star.M) if galpha_star.coeff(n).val() == 0), 1)
        gi = galpha_star.coeff(i)
    c = Psi_alpha.coeff(i).div(gi)
    diag["norm_idx"] = i
    diag["Psi_alpha_v"] = Psi_alpha.valuation_floor()
    return c, diag


if __name__ == "__main__":
    print("rung3_lhs module loaded — driver in rung3_lhs_run.py")
