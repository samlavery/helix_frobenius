"""tmp/general_m_mechanism.py -- link-by-link verification of the GENERAL-m
FREEZE-ORDER MECHANISM for cyclic covers y^m = h(x), h = prod_j f_j^{e_j}.

Generalises tmp/freeze_mechanism.py (the mu_3 case y^3 = f g^2) to arbitrary
character order m and arbitrary exponent multiset (e_1,...,e_r).

THEOREM (companion proof: tmp/general_m_mechanism_notes.md).
Fix m >= 2, a prime p = 1 (mod m) so mu_m subset F_p*, chi = chi_m an order-m
character on F_p (chi(0)=0), and an integer a coprime to m (the a-rail).  Let
f_1,...,f_r in F_p[x] be monic, coprime, squarefree, exponents e_j in {1..m-1},
h = prod_j f_j^{e_j}, and C : y^m = h(x) the smooth projective cyclic m-cover.
Let V_a = chi^a-eigenspace of the cover automorphism sigma:(x,y)->(x, zeta_m y)
inside H^1(C_bar, Qlbar); g_a = dim V_a = N_a - 2 with N_a the number of places
(finite branch points + infinity) at which chi^a(h) is genuinely ramified.  Then

    det(Frob_p | V_a) = W_a * p^{g_a/2} * chi^a(C),
    C = prod over finite branch points of leadcoeff(h) there
      = (sign) * prod_i disc(f_i)^{e_i} * prod_{i<j} Res(f_i,f_j)^{e_i+e_j},
    W_a = position-blind root of unity (Hasse-Davenport branch-place sign
          (-1)^{delta_p}, delta_p = sum_{finite branch v}(deg v - 1), times a
          quadratic-Gauss-sum phase when m is even and p = 3 mod 4).

FREEZE INVARIANT.  chi^a kills every perfect-m-th-power factor of C, so
    r := det/(W_a p^{g_a/2}) = chi^a(D_a),
    D_a = prod_i disc(f_i)^{e_i} * prod_{ i<j : m does not divide a(e_i+e_j) } Res(f_i,f_j)^{e_i+e_j}.
A cross-resultant Res(f_i,f_j) DROPS OUT exactly when m | a(e_i+e_j) (the pair is
"balanced"); otherwise it enters D_a with exponent (e_i+e_j) mod m.  For mu_3,
y^3=f g^2 has the single pair e_f+e_g = 1+2 = 3 = 0 (mod 3): the resultant is a
perfect cube and drops -- reproducing D = disc(f)disc(g)^2 with NO resultant.

Links (each verifies one step independently, exact in Z[zeta_m]):
  L0  Gauss base   : g(chi^a) g(chibar^a) = chi^a(-1) p   [Hasse-Davenport base]
  L1  Weil         : det * conj(det) = p^{g_a}            [RH for curves]
  L2  freeze       : r0 := det / p^{g_a/2} is a root of unity  [balanced signature]
  L4  reciprocity  : C = (sign) disc-part * cross-Res part (integer identity);
                     chi^a(Res(f_i,f_j)^{e_i+e_j}) = 1 iff m | a(e_i+e_j)   [heart]
  L5  Gauss part   : W_a := det / chi^a(C) is a position-blind root of unity times
                     p^{g_a/2}  (= p^{g_a/2} for rational-root, no-quad-phase members)
  L3  end-to-end   : det = W_a p^{g_a/2} chi^a(D_a)  EXACT in Z[zeta_m]  [the theorem]

det(Frob_p | V_a) is computed EXACTLY in Z[zeta_m] from the character sums
T_k = sum_{x in F_{p^k}} chi^a(h(x)); power sums s_k = -T_k; Newton -> e_{g_a}.
No L-values, no oracle.

Run:  python3 general_m_mechanism.py
"""
import sys, os, math, cmath
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import weil_scout as WS
import weil_sixfold_count as WSC

x = sp.symbols('x')


# ============================================================================
# exact cyclotomic arithmetic  Z[zeta_m] = Z[t]/Phi_m(t),  power basis 1..t^{d-1}
# element = list[Fraction] of length d = deg Phi_m = phi(m)
# ============================================================================
class Cyclo:
    def __init__(self, m):
        self.m = m
        Phi = sp.Poly(sp.cyclotomic_poly(m, x), x)
        self.d = Phi.degree()
        # Phi_m(t) = t^d + sum c_i t^i ; reduction t^d = -(c_0 + ... + c_{d-1} t^{d-1})
        coeffs = [Fr(int(Phi.coeff_monomial(x**i))) for i in range(self.d + 1)]
        assert coeffs[self.d] == 1
        self.red_td = [-coeffs[i] for i in range(self.d)]      # t^d in power basis
        # table t^k mod Phi for k = 0 .. 2d-2 (needed for multiplication reduce)
        self.tpow = [self._basis(i) for i in range(self.d)]
        cur = list(self.red_td)                                # t^d
        for k in range(self.d, 2 * self.d - 1):
            self.tpow.append(list(cur))
            # cur = t * cur  (shift up, reduce the t^d term)
            top = cur[self.d - 1]
            nxt = [Fr(0)] + cur[:self.d - 1]
            nxt = [nxt[i] + top * self.red_td[i] for i in range(self.d)]
            cur = nxt
        # zeta^t in power basis for t = 0..m-1  (zeta^m = 1)
        self.zpow = []
        for t in range(m):
            # t^t mod Phi_m: reduce x^t
            r = self._reduce_monomial(t)
            self.zpow.append(r)

    def _basis(self, i):
        v = [Fr(0)] * self.d
        v[i] = Fr(1)
        return v

    def _reduce_monomial(self, k):
        """x^k mod Phi_m in power basis (k any nonneg int)."""
        if k < self.d:
            return self._basis(k)
        if k <= 2 * self.d - 2:
            return list(self.tpow[k])
        # general: reduce via repeated squaring style; do it by polynomial division
        q = sp.Poly(x**k, x)
        Phi = sp.Poly(sp.cyclotomic_poly(self.m, x), x)
        rem = q.rem(Phi)
        v = [Fr(0)] * self.d
        for i in range(self.d):
            v[i] = Fr(int(rem.coeff_monomial(x**i)))
        return v

    def zero(self):
        return [Fr(0)] * self.d

    def one(self):
        return self.zpow[0]

    def zeta_pow(self, t):
        """zeta_m^t (t any integer)."""
        return list(self.zpow[t % self.m])

    def add(self, A, B):
        return [A[i] + B[i] for i in range(self.d)]

    def sub(self, A, B):
        return [A[i] - B[i] for i in range(self.d)]

    def smul(self, c, A):
        c = Fr(c)
        return [c * A[i] for i in range(self.d)]

    def mul(self, A, B):
        d = self.d
        raw = [Fr(0)] * (2 * d - 1)
        for i in range(d):
            if A[i] == 0:
                continue
            ai = A[i]
            for j in range(d):
                if B[j]:
                    raw[i + j] += ai * B[j]
        out = [Fr(0)] * d
        for k in range(2 * d - 1):
            if raw[k] == 0:
                continue
            tk = self.tpow[k]
            for i in range(d):
                out[i] += raw[k] * tk[i]
        return out

    def conj(self, A):
        """complex conjugation zeta -> zeta^{-1}."""
        out = self.zero()
        for i in range(self.d):
            if A[i]:
                out = self.add(out, self.smul(A[i], self.zeta_pow(-i)))
        return out

    def is_int(self, A):
        return all(c.denominator == 1 for c in A)

    def as_rational_int(self, A):
        """if A is a rational integer (only constant coord), return it else None."""
        if A[0].denominator == 1 and all(A[i] == 0 for i in range(1, self.d)):
            return int(A[0])
        return None

    def equal(self, A, B):
        return all(A[i] == B[i] for i in range(self.d))

    def to_complex(self, A):
        z = cmath.exp(2j * math.pi / self.m)
        return sum(complex(A[i]) * z**i for i in range(self.d))

    def roots_of_unity(self):
        """all roots of unity in Q(zeta_m): {zeta^t} (m even) and {-zeta^t} (m odd)."""
        out = {}
        for t in range(self.m):
            out[tuple(self.zeta_pow(t))] = (1, t)
            neg = self.smul(-1, self.zeta_pow(t))
            out.setdefault(tuple(neg), (-1, t))
        return out

    def match_root_of_unity(self, A):
        """return (sign, t, order) if A = sign*zeta^t is a root of unity else None."""
        rou = self.roots_of_unity()
        key = tuple(A)
        if key in rou:
            sgn, t = rou[key]
            # order of sign*zeta^t as element of mu_{2m}
            k = 0
            cur = A
            order = None
            for e in range(1, 2 * self.m + 1):
                if self.equal(cur, self.one()):
                    order = e
                    break
                cur = self.mul(cur, A)
            return (sgn, t, order)
        return None


# ============================================================================
# exact character-sum T_k^{(a)} = sum_{x in F_{p^k}} chi^a(h(x)), exact in Z[zeta_m]
# chi(y) = y^{(q-1)/m} in mu_m(F_p); map rho^j -> zeta^j  (rho = prim m-th root in F_p)
# ============================================================================
def rho_index_map(p, m, rho):
    """{ F_p value rho^j : j }  for j = 0..m-1."""
    d = {}
    v = 1
    for j in range(m):
        d[v] = j
        v = (v * rho) % p
    return d


def counts_Tk(p, k, m, h_mod, rho, ridx):
    """return counts n[0..m-1]: n[j] = #{x in F_{p^k} : chi(h(x)) = zeta^j}."""
    F = WSC.GFpk(p, k)
    q = p ** k
    e = (q - 1) // m
    n = [0] * m
    lo, chunk = 0, 1 << 20
    while lo < q:
        hi = min(lo + chunk, q)
        X = F.elements_chunk(lo, hi)
        H = WSC.eval_h_chunk(F, h_mod, X)
        chi = F.powq(H, e)                    # constant polys (mu_m subset F_p) or 0
        vals = chi[:, 0]
        for v in np.unique(vals):
            vv = int(v)
            if vv == 0:
                continue
            n[ridx[vv]] += int(np.count_nonzero(vals == v))
        lo = hi
    return n


def exact_Tk(CY, a, counts):
    """T_k^{(a)} = sum_j n_j zeta^{a j}, exact element of Z[zeta_m]."""
    acc = CY.zero()
    for j, nj in enumerate(counts):
        if nj:
            acc = CY.add(acc, CY.smul(nj, CY.zeta_pow(a * j)))
    return acc


def newton_top(CY, svals, g):
    """e_g (product of eigenvalues) from power sums s_1..s_g via Newton's identities."""
    e = [CY.one()] + [CY.zero()] * g
    for kk in range(1, g + 1):
        acc = CY.zero()
        for i in range(1, kk + 1):
            t = CY.mul(e[kk - i], svals[i])
            if (i - 1) % 2 == 1:
                t = CY.sub(CY.zero(), t)
            acc = CY.add(acc, t)
        e[kk] = CY.smul(Fr(1, kk), acc)
    return e[g]


# ============================================================================
# residue-symbol chi^a(n) in Z[zeta_m] for a rational integer n (coprime to p)
# ============================================================================
def chi_val(CY, a, n_int, p, m, rho, ridx):
    val = pow(n_int % p, (p - 1) // m, p)
    j = ridx[val % p]
    return CY.zeta_pow(a * j)


# ============================================================================
# L0 : general Gauss-sum base identity  g(chi^a) g(chibar^a) = chi^a(-1) p
# ============================================================================
def gauss_sum(p, m, rho, a):
    gamma = WS.primitive_root(p)
    z = cmath.exp(2j * math.pi / m)
    ind = [0] * p
    t = 1
    for kk in range(p - 1):
        ind[t] = kk
        t = (t * gamma) % p
    # chi(gamma) = zeta^{(p-1)/m ... }: chi(t)=zeta^{ index_rho }. Use rho-index:
    ridx = rho_index_map(p, m, rho)
    tot = 0j
    for tt in range(1, p):
        val = pow(tt, (p - 1) // m, p)
        j = ridx[val]
        tot += (z ** ((a * j) % m)) * cmath.exp(2j * math.pi * tt / p)
    return tot


def check_L0(primes, m):
    print(f"  L0  Gauss base (m={m}): g(chi^a) g(chibar^a) = chi^a(-1) p")
    ok = True
    for p in primes:
        if (p - 1) % m:
            continue
        gamma = WS.primitive_root(p)
        rho = pow(gamma, (p - 1) // m, p)
        a = 1
        gc = gauss_sum(p, m, rho, a)
        gcb = gauss_sum(p, m, rho, (-a) % m)
        prod = gc * gcb
        chi_m1 = pow((-1) % p, (p - 1) // m, p)          # chi(-1) as F_p m-th root
        ridx = rho_index_map(p, m, rho)
        sgn_j = ridx[chi_m1]
        pred = cmath.exp(2j * math.pi * (a * sgn_j % m) / m) * p
        good = abs(prod - pred) < 1e-6 * p and abs(abs(gc) ** 2 - p) < 1e-6 * p
        ok = ok and good
        print(f"      p={p:4d}  g g' = {prod.real:+9.3f}{prod.imag:+9.3f}i  "
              f"pred={pred.real:+9.3f}{pred.imag:+9.3f}i  |g|^2={abs(gc)**2:.3f}  "
              f"{'ok' if good else 'FAIL'}")
    return ok


# ============================================================================
# polynomial helpers
# ============================================================================
def sp_poly(coeffs):
    return sp.Poly(list(reversed(coeffs)), x)


def poly_from_roots(roots):
    """monic poly (low->high int coeffs) from a list of integer roots."""
    P = sp.prod([sp.Poly(x - r, x) for r in roots], sp.Poly(1, x))
    d = P.degree()
    return [int(P.coeff_monomial(x**i)) for i in range(d + 1)]


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def h_from_factors(factors):
    """factors = [(coeffs_low2high, exp), ...] -> h coeffs low->high."""
    h = [1]
    for fc, e in factors:
        for _ in range(e):
            h = poly_mul(h, fc)
    return h


# ============================================================================
# L4 : reciprocity integer identity (the heart -- general cross-resultant law)
# ============================================================================
def _abs_res(fi, fj):
    """|Res(f_i, f_j)| -- magnitude only (sign convention irrelevant)."""
    return abs(int(sp.resultant(fi, fj)))


def _signed_res(fi, fj):
    """a FIXED-orientation resultant of f_i, f_j (sympy's value); any consistent
    orientation is fine -- it only shifts the position-blind constant W_a."""
    return int(sp.resultant(fi, fj))


def check_L4(factors, m, a):
    """factors = [(coeffs, e)].  The leading-coefficient reciprocity:
       C := prod over finite branch pts of leadcoeff(h) there.
       Its ABSOLUTE VALUE factors as (this is the exponent law -- the theorem's heart):
         |C| = prod_i disc(f_i)^{e_i} * prod_{i<j} |Res(f_i,f_j)|^{e_i+e_j}.
       The freeze invariant keeps disc(f_i)^{e_i} and every cross-resultant with
       m does not divide a(e_i+e_j); the rest are perfect m-th powers killed by chi^a:
         D_a = prod_i disc(f_i)^{e_i}
               * prod_{ i<j : m does not divide a(e_i+e_j) } Res(f_i,f_j)^{e_i+e_j}.
    Returns the magnitude-checked exponent law and the explicit invariant D_a."""
    polys = [sp_poly(fc) for fc, e in factors]
    exps = [e for fc, e in factors]
    degs = [P.degree() for P in polys]
    r = len(polys)
    # --- |C| directly (product over roots), magnitude only ---
    Cabs = 1
    for i in range(r):
        Cabs *= abs(int(sp.resultant(polys[i].diff(x), polys[i]))) ** exps[i]
        for j in range(r):
            if j != i:
                Cabs *= _abs_res(polys[i], polys[j]) ** exps[j]
    # --- closed-form magnitude ---
    disc_part = 1
    for i in range(r):
        disc_part *= abs(int(sp.discriminant(polys[i]))) ** exps[i]
    abs_res_part = 1
    for i in range(r):
        for j in range(i + 1, r):
            abs_res_part *= _abs_res(polys[i], polys[j]) ** (exps[i] + exps[j])
    exponent_law_ok = (Cabs == disc_part * abs_res_part)
    # --- explicit invariant D_a (signed, fixed orientation) ---
    D_a = 1
    for i in range(r):
        D_a *= int(sp.discriminant(polys[i])) ** exps[i]
    surviving, dropped = [], []
    for i in range(r):
        for j in range(i + 1, r):
            s = exps[i] + exps[j]
            if (a * s) % m == 0:
                dropped.append((i, j, s))
            else:
                D_a *= _signed_res(polys[i], polys[j]) ** s
                surviving.append((i, j, s))
    return dict(Cabs=Cabs, disc_part=disc_part, abs_res_part=abs_res_part,
                exponent_law_ok=exponent_law_ok, D_a=D_a,
                surviving=surviving, dropped=dropped, degs=degs, exps=exps)


# ============================================================================
# genus / ramification bookkeeping for the a-rail
# ============================================================================
def rail_data(factors, m, a):
    exps = [e for fc, e in factors]
    degs = [sp_poly(fc).degree() for fc, e in factors]
    degh = sum(d * e for d, e in zip(degs, exps))
    # finite ramified geometric branch points: those with m | a*e_j are UNramified
    Nfin = sum(d for d, e in zip(degs, exps) if (a * e) % m != 0)
    inf_ram = (a * degh) % m != 0
    N = Nfin + (1 if inf_ram else 0)
    g = N - 2
    return dict(degh=degh, N=N, g=g, inf_ram=inf_ram, exps=exps, degs=degs)


# ============================================================================
# per-member verification
# ============================================================================
def verify_member(name, factors, m, a, primes, out):
    def P(s=""):
        print(s, flush=True); out.append(s)

    CY = Cyclo(m)
    rd = rail_data(factors, m, a)
    g = rd['g']
    hc = h_from_factors(factors)
    L4 = check_L4(factors, m, a)

    P("=" * 78)
    fdesc = ", ".join(f"f{i+1}={fc}^{e}" for i, (fc, e) in enumerate(factors))
    P(f"MEMBER {name}:  y^{m} = h,  {fdesc}   (a-rail a={a})")
    P(f"  deg h={rd['degh']}, inf_ram={rd['inf_ram']}, N_a={rd['N']}, g_a={g}")
    if g < 1:
        P("  [!] g_a < 1 -- nothing to verify"); return None
    if g % 2:
        P(f"  [!] g_a odd ({g}) -> unbalanced; det verified, r not a root of unity (no freeze)")
    P(f"  L4 exponent law:  |C| = prod disc^e * prod|Res|^(e_i+e_j) : "
      f"{L4['exponent_law_ok']}   (|C|={L4['Cabs']})")
    surv = ", ".join(f"Res(f{i+1},f{j+1})^{s}" for i, j, s in L4['surviving']) or "(none)"
    drop = ", ".join(f"Res(f{i+1},f{j+1})^{s}[m|{a}*{s}]" for i, j, s in L4['dropped']) or "(none)"
    P(f"      surviving cross-resultants in D_a: {surv}")
    P(f"      dropped (perfect m-th power, chi^a kills): {drop}")
    P(f"      D_a = {L4['D_a']}")

    P(f"  {'p':>5s} {'det (complex)':>22s} d  L1  {'r=det/p^(g/2)':>14s} L2 ord  "
      f"{'W=det/(p^(g/2)chi(D_a))':>24s}")
    allok = True
    Wvals = []
    for p in primes:
        if (p - 1) % m:
            continue
        bad = False
        polys = [sp_poly(fc) for fc, e in factors]
        for i in range(len(polys)):
            if int(sp.discriminant(polys[i])) % p == 0:
                bad = True
            for j in range(i + 1, len(polys)):
                if int(sp.resultant(polys[i], polys[j])) % p == 0:
                    bad = True
        if bad:
            continue
        gamma = WS.primitive_root(p)
        rho = pow(gamma, (p - 1) // m, p)
        ridx = rho_index_map(p, m, rho)
        h_mod = [c % p for c in hc]
        svals = [CY.zero()]
        for kk in range(1, g + 1):
            cnts = counts_Tk(p, kk, m, h_mod, rho, ridx)
            Tk = exact_Tk(CY, a, cnts)
            svals.append(CY.sub(CY.zero(), Tk))
        det = newton_top(CY, svals, g)
        # L1 Weil: det*conj(det) = p^g  (exact in Z[zeta_m])
        nrm = CY.mul(det, CY.conj(det))
        L1 = (CY.as_rational_int(nrm) == p ** g)
        # delta_p (Hasse-Davenport branch-place sign)
        nfac = nbp = 0
        for fc, e in factors:
            if (a * e) % m == 0:
                continue
            fp_ = sp.Poly([c % p for c in reversed(fc)], x, modulus=p)
            nfac += len(sp.factor_list(fp_)[1]); nbp += sp_poly(fc).degree()
        delta = nbp - nfac
        # L2: r = det / p^{g/2} root of unity  (freeze)
        if g % 2 == 0:
            half = p ** (g // 2)
            r0 = CY.smul(Fr(1, half), det)
            ru = CY.match_root_of_unity(r0)
            L2 = ru is not None
            ordr = ru[2] if ru else None
            r0str = (f"{'-' if ru[0] < 0 else ''}z^{ru[1]}" if ru else "NOT-rou")
            # L3/L5: W = det / (p^{g/2} chi^a(D_a)); should be POSITION-BLIND root of unity
            chiD = chi_val(CY, a, L4['D_a'], p, m, rho, ridx)
            W = CY.smul(Fr(1, half), CY.mul(det, CY.conj(chiD)))
            wru = CY.match_root_of_unity(W)
            Wstr = (f"{'-' if wru[0] < 0 else ''}z^{wru[1]}" if wru else "NOT-rou")
            Wvals.append((tuple(W), delta, p))
        else:
            L2, ordr, r0str, Wstr = "(oddg)", None, "-", "-"
        detc = CY.to_complex(det)
        allok = allok and L1 and (L2 in (True,))
        P(f"  {p:>5d} {detc.real:+11.2f}{detc.imag:+10.2f}i d={delta} {str(L1)[0]}  "
          f"{r0str:>14s} {str(L2)[0]} {str(ordr):>3s}  {Wstr:>24s}")
    # W position-blindness: group by delta_p, W must be constant within each group
    posblind = True
    groups = {}
    for Wt, delta, p in Wvals:
        groups.setdefault(delta, set()).add(Wt)
    for delta, s in groups.items():
        if len(s) > 1:
            posblind = False
    if Wvals:
        gsum = ", ".join(f"delta={d}: |W-values|={len(s)}" for d, s in sorted(groups.items()))
        P(f"  W position-blind within each delta_p group: {posblind}   ({gsum})")
    P(f"  ALL LINKS PASS for {name}: {allok and posblind}")
    P("")
    return allok and posblind


# ============================================================================
# members
# ============================================================================
def R(roots, e):
    return (poly_from_roots(roots), e)


MEMBERS = [
    # (name, factors [(coeffs,e)], m, a, primes)
    # --- mu_4 generic (scout 9.1): roots 0 (e1); 1,3,7 (e2); 5 (e3), g=4.  POSTDICT.
    ("MU4-gen  0^1 (1,3,7)^2 5^3",
     [R([0], 1), R([1, 3, 7], 2), R([5], 3)], 4, 1, [13, 29, 37, 41, 53]),
    # --- mu_4 inert control: exposes Hasse-Davenport sign delta_p at p=3 mod 4
    ("MU4-inert  (x^2+1)^1 (1,3,7)^2 5^3",
     [([1, 0, 1], 1), R([1, 3, 7], 2), R([5], 3)], 4, 1, [13, 29, 37, 41, 53]),
    # --- mu_5 (a=1): cross-resultants enter, one pair drops (e_i+e_j=5), g=2 balanced
    ("MU5   0^1 1^3 3^4",
     [R([0], 1), R([1], 3), R([3], 4)], 5, 1, [11, 31, 41, 61]),
    # --- mu_5 a=2 rail on the SAME cover: the a-general statement
    ("MU5-a2  0^1 1^3 3^4  (rail a=2)",
     [R([0], 1), R([1], 3), R([3], 4)], 5, 2, [11, 31, 41, 61]),
    # --- mu_6: exp-4 (order-3) monodromy + cross-resultants, one pair drops (e=6), g=2
    ("MU6   0^1 1^2 3^4",
     [R([0], 1), R([1], 2), R([3], 4)], 6, 1, [7, 13, 19, 31]),
    # --- mu_6 with ONE quadratic (exp-3 -> chi_6^3=chi_2) monodromy at root 1:
    #     tests the quadratic-Gauss phase in W_a at p = 3 (mod 4)
    ("MU6-quad  0^1 1^3 3^4",
     [R([0], 1), R([1], 3), R([3], 4)], 6, 1, [7, 13, 19, 31, 43]),
]


def main():
    out = []

    def P(s=""):
        print(s, flush=True); out.append(s)

    P("#" * 78)
    P("# GENERAL-m FREEZE-ORDER MECHANISM")
    P("# det(Frob_p | V_a) = W_a p^{g_a/2} chi^a(D_a),  y^m = prod f_j^{e_j}")
    P("# companion: general_m_mechanism_notes.md")
    P("#" * 78)
    P()
    for m, pr in [(4, [13, 29, 37, 41, 53]), (5, [11, 31, 41, 61]), (6, [7, 13, 19, 31])]:
        check_L0(pr, m)
    P()
    results = {}
    for name, factors, m, a, pr in MEMBERS:
        results[name] = verify_member(name, factors, m, a, pr, out)
    P("#" * 78)
    P("SUMMARY: " + ", ".join(f"{k.split()[0]}={v}" for k, v in results.items()))
    P("#" * 78)

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "general_m_mechanism_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(out) + "\n")
    print(f"\n[results -> {path}]", flush=True)


if __name__ == "__main__":
    main()
