"""tmp/freeze_mechanism.py -- link-by-link verification of the FREEZE-ORDER MECHANISM.

THEOREM (companion proof: tmp/freeze_mechanism_notes.md).
Let p = 1 (mod 3), chi = chi_3 the cubic residue character on F_p (chi(0)=0),
f, g in F_p[x] monic, coprime, squarefree, with 3 does not divide deg(f*g^2)
(the infinity-ramified / balanced configuration).  Let C : y^3 = f(x) g(x)^2 be
the smooth projective cyclic cubic cover, V_zeta = W the zeta_3-eigenspace of the
cover automorphism sigma:(x,y)->(x, zeta_3 y) inside H^1(C_bar, Qlbar),
g_W = dim W = deg f + deg g - 1.  Then

        det( Frob_p | V_zeta )  =  (-1)^{delta_p} * p^{g_W/2} * chi_3(D),
        D = disc(f) disc(g)^2,
        delta_p = (deg f + deg g) - #{finite ramified places of f*g over F_p}
                = sum_{finite branch places v} (deg v - 1)   [Hasse-Davenport sign].

The resultant Res(f,g) does NOT enter.  delta_p = 0 whenever every branch point is
RATIONAL over F_p -- in particular for every integer-root member (the whole freeze
campaign) at every good prime -- giving the clean law det = p^{g_W/2} chi_3(D).
delta_p > 0 only at primes where some factor of f or g is inert/higher-degree
(exposed by the f = x^2+1 member below at p = 3 mod 4).  For balanced (Weil-type)
configs g_W is even and r := det/((-1)^{delta_p} p^{g_W/2}) = chi_3(D) in mu_3;
ord(r) = ord chi_3(D) is the freeze-order law (item 27) as a corollary.

Links (each verifies one step of the proof independently):
  L0  Gauss sanity : g(chi) g(chibar) = chi(-1) p = p ;  |g(chi)|^2 = p   [Hasse-Davenport base]
  L1  Weil         : det * conj(det) = p^{g_W}                            [RH for curves, Weil]
  L2  freeze mu_3  : r := det / p^{g_W/2} in {1, w, w^2}                  [balanced signature]
  L3  end-to-end   : det = p^{g_W/2} chi_3(D)  EXACT in Z[w]             [the theorem]
  L4  reciprocity  : prod(leadcoeff of h at finite branch pts)
                     = (-1)^e disc(f) disc(g)^2 Res(f,g)^3  (integer id.);
                     chi_3 kills Res^3 (perfect cube) and the sign (chi_3(-1)=1) [heart]
  L5  Gauss/char   : det / chi_3(D) = p^{g_W/2}  (real, positive, position-independent) [HD collapse]

det( Frob_p | V_zeta ) is computed EXACTLY in Z[w] (w = e^{2pi i/3}) from the cubic
character sums T_k = sum_{x in F_{p^k}} chi_3(h(x)), s_k = -T_k, Newton -> e_{g_W}.
No L-values, no oracle: the character sums are elementary finite-field counts.

Run:  python3 freeze_mechanism.py            (default member/prime set)
"""
import sys, os
from fractions import Fraction as Fr
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import weil_scout as WS
import weil_sixfold_count as WSC

x = sp.symbols('x')

# ----------------------------------------------------------------------------
# exact Z[w] arithmetic:  a + b*w,  w = primitive cube root, w^2 = -1 - w
# ----------------------------------------------------------------------------
ZERO = (Fr(0), Fr(0)); ONE = (Fr(1), Fr(0)); W1 = (Fr(0), Fr(1)); W2 = (Fr(-1), Fr(-1))
MU3 = {ONE: 0, W1: 1, W2: 2}


def zadd(A, B): return (A[0] + B[0], A[1] + B[1])
def zsub(A, B): return (A[0] - B[0], A[1] - B[1])
def zmul(A, B):
    a, b = A; c, d = B
    return (a * c - b * d, a * d + b * c - b * d)
def zconj(A):
    a, b = A
    return (a - b, -b)
def znorm(A):  # (a+bw)(a+bw^2) = a^2 - ab + b^2
    a, b = A
    return a * a - a * b + b * b


def poly_mul(a, b):
    """multiply integer coeff lists (low->high)."""
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def h_from_fg(fc, gc):
    """h = f * g^2 coeffs (low->high), from f,g coeff lists (low->high)."""
    return poly_mul(fc, poly_mul(gc, gc))


def sp_poly(coeffs):
    """sympy Poly in x from integer coeff list (low->high)."""
    return sp.Poly(list(reversed(coeffs)), x)


# ----------------------------------------------------------------------------
# exact cubic-character sum T_k over F_{p^k}, exact in Z[w]
# ----------------------------------------------------------------------------
def exact_Tk(p, k, h_mod, rho):
    """T_k = sum_{x in F_{p^k}} chi_3(h(x)), exact; chi maps rho^j -> w^j (rho in F_p)."""
    F = WSC.GFpk(p, k)
    q = p ** k
    e = (q - 1) // 3
    rpow = {1: 0, rho % p: 1, (rho * rho) % p: 2}
    n = [0, 0, 0]
    lo, chunk = 0, 1 << 20
    while lo < q:
        hi = min(lo + chunk, q)
        X = F.elements_chunk(lo, hi)
        H = WSC.eval_h_chunk(F, h_mod, X)
        chi = F.powq(H, e)
        vals = chi[:, 0]
        for v in np.unique(vals):
            vv = int(v)
            if vv == 0:
                continue
            n[rpow[vv]] += int(np.count_nonzero(vals == v))
        lo = hi
    return (Fr(n[0]) - Fr(n[2]), Fr(n[1]) - Fr(n[2]))  # n0 + n1 w + n2 w^2, w^2=-1-w


def newton_top(svals, g):
    """e_g (elementary symmetric = product of eigenvalues) from power sums s_1..s_g."""
    e = [ONE] + [ZERO] * g
    for kk in range(1, g + 1):
        acc = ZERO
        for i in range(1, kk + 1):
            t = zmul(e[kk - i], svals[i])
            if (i - 1) % 2 == 1:
                t = zsub(ZERO, t)
            acc = zadd(acc, t)
        e[kk] = (acc[0] / kk, acc[1] / kk)
    return e[g]


def chi3_exp(n_int, p, rho):
    """cubic residue symbol exponent j in {0,1,2} with chi(n)=w^j; n coprime to p."""
    val = pow(n_int % p, (p - 1) // 3, p)
    return {1: 0, rho % p: 1, (rho * rho) % p: 2}[val]


def chi3_val(n_int, p, rho):
    return [ONE, W1, W2][chi3_exp(n_int, p, rho)]


# ----------------------------------------------------------------------------
# L0 : Gauss sum sanity (the Hasse-Davenport base identity)
# ----------------------------------------------------------------------------
def gauss_sum(p, rho, conj=False):
    import cmath, math
    gamma = WS.primitive_root(p)
    w = cmath.exp(2j * math.pi / 3)
    # chi(gamma^k) = w^{k mod 3}; build additive char psi(t)=e^{2pi i t/p}
    ind = [0] * p
    a = 1
    for k in range(p - 1):
        ind[a] = k
        a = (a * gamma) % p
    tot = 0j
    for t in range(1, p):
        e = ind[t] % 3
        if conj:
            e = (-e) % 3
        tot += (w ** e) * cmath.exp(2j * math.pi * t / p)
    return tot


def check_L0(primes):
    import math
    print("  L0  Gauss-sum base (Hasse-Davenport): g(chi) g(chibar) = chi(-1) p = p")
    ok = True
    for p in primes:
        if (p - 1) % 3:
            continue
        gamma = WS.primitive_root(p)
        rho = pow(gamma, (p - 1) // 3, p)
        gc = gauss_sum(p, rho, conj=False)
        gcb = gauss_sum(p, rho, conj=True)
        prod = gc * gcb
        absq = abs(gc) ** 2
        good = abs(prod - p) < 1e-6 * p and abs(absq - p) < 1e-6 * p
        ok = ok and good
        print(f"      p={p:4d}  g(chi)g(chibar)={prod.real:+.4f}{prod.imag:+.4f}i "
              f"(=p={p})  |g(chi)|^2={absq:.4f}  {'ok' if good else 'FAIL'}")
    return ok


# ----------------------------------------------------------------------------
# L4 : reciprocity integer identity (the heart -- resultant cancels)
# ----------------------------------------------------------------------------
def check_L4(fc, gc):
    f, g = sp_poly(fc), sp_poly(gc)
    df, dg = f.degree(), g.degree()
    fp, gp = f.diff(x), g.diff(x)
    Rff = int(sp.resultant(f, fp))       # prod_{f-roots} f'  (monic f)
    Rfg = int(sp.resultant(f, g))        # prod_{f-roots} g   = Res(f,g)
    Rgf = int(sp.resultant(g, f))        # prod_{g-roots} f   = Res(g,f)
    Rgg = int(sp.resultant(g, gp))       # prod_{g-roots} g'
    C = Rff * (Rfg ** 2) * Rgf * (Rgg ** 2)   # = prod over finite branch pts of leadcoeff(h)
    discf = int(sp.discriminant(f))
    discg = int(sp.discriminant(g))
    Res = Rfg
    D = discf * discg ** 2
    # closed form:  C = (-1)^{C(df,2)+df*dg} disc(f) disc(g)^2 Res^3
    sign = (-1) ** ((df * (df - 1) // 2) + df * dg)
    predicted = sign * D * Res ** 3
    id_ok = (C == predicted)
    res_cube_ok = True  # Res enters as Res^3, a perfect cube -> chi_3(Res^3)=1
    return dict(df=df, dg=dg, discf=discf, discg=discg, Res=Res, D=D, C=C,
                sign=sign, id_ok=id_ok)


# ----------------------------------------------------------------------------
# main per-member verification
# ----------------------------------------------------------------------------
def verify_member(name, fc, gc, primes, out):
    def P(s=""):
        print(s, flush=True); out.append(s)

    f, g = sp_poly(fc), sp_poly(gc)
    df, dg = f.degree(), g.degree()
    gW = df + dg - 1
    hc = h_from_fg(fc, gc)
    degh = len(hc) - 1
    inf_ram = (degh % 3 != 0)
    coprime = (sp.gcd(f, g) == 1)
    sqfree = (sp.gcd(f, f.diff(x)) == 1) and (sp.gcd(g, g.diff(x)) == 1)
    P("=" * 74)
    P(f"MEMBER {name}: y^3 = f g^2,  f={fc}, g={gc} (coeffs low->high)")
    P(f"  deg f={df}, deg g={dg}, deg h={degh}, genus_W g_W={gW}, "
      f"infinity-ramified={inf_ram}, coprime={coprime}, squarefree={sqfree}")
    if not (inf_ram and coprime and sqfree):
        P("  [!] hypotheses not met -- skipping"); return

    L4 = check_L4(fc, gc)
    P(f"  L4 reciprocity:  C = prod leadcoeff(h) over finite branch pts")
    P(f"      disc(f)={L4['discf']}  disc(g)={L4['discg']}  Res(f,g)={L4['Res']}  "
      f"D=disc(f)disc(g)^2={L4['D']}")
    P(f"      C = {L4['C']}")
    P(f"      (-1)^e disc(f) disc(g)^2 Res^3  matches C : {L4['id_ok']}   "
      f"[Res enters as Res^3 = cube -> chi_3 kills it; sign={L4['sign']}, chi_3(-1)=1]")

    P(f"  {'p':>5s} {'det=e_gW (Z[w])':>22s}  d=delta_HD  "
      f"L1|det|2  L2 mu3  L3 r=chi(D)  L5 char=(-1)^d p^gW/2   "
      f"[r := det/((-1)^delta p^{{gW/2}})]")
    allok = True
    for p in primes:
        if (p - 1) % 3:
            continue
        # good prime: the RADICAL f*g stays squarefree mod p and f,g stay coprime,
        # i.e. disc(f) disc(g) Res(f,g) != 0 mod p.  (h=f g^2 is never squarefree;
        # the branch LOCUS is the distinct roots of f*g.)  D=disc(f)disc(g)^2.
        if L4['discf'] % p == 0 or L4['discg'] % p == 0 or L4['Res'] % p == 0:
            continue
        gamma = WS.primitive_root(p)
        rho = pow(gamma, (p - 1) // 3, p)
        h_mod = [c % p for c in hc]
        svals = [ZERO]
        for k in range(1, gW + 1):
            svals.append(zsub(ZERO, exact_Tk(p, k, h_mod, rho)))
        det = newton_top(svals, gW)                       # e_{g_W} = prod eigenvalues
        # Hasse-Davenport branch-place sign: delta_p = (#branch pts) - (#finite ram places)
        #   = sum over finite ramified places v of (deg v - 1).  A place of degree d gives a
        #   Gauss sum over F_{p^d} = (-1)^{d-1} (Gauss sum over F_p)^d  [Hasse-Davenport].
        #   delta_p = 0 for members with all roots rational over F_p (e.g. integer roots).
        fp_ = sp.Poly([c % p for c in reversed(fc)], x, modulus=p)
        gp_ = sp.Poly([c % p for c in reversed(gc)], x, modulus=p)
        nfac = len(sp.factor_list(fp_)[1]) + len(sp.factor_list(gp_)[1])
        delta = (df + dg) - nfac
        sgn = (-1) ** delta
        # L1 Weil
        L1 = (znorm(det) == Fr(p ** gW))
        # L2 freeze (sign-corrected): r := det / ((-1)^delta p^{g/2}) in mu3
        if gW % 2 == 0:
            half = sgn * p ** (gW // 2)
            r = (Fr(det[0], half), Fr(det[1], half))
            L2 = r in MU3
        else:
            r, L2 = None, "(odd gW)"
        # L3 end-to-end and L5 char part (sign-corrected)
        chiD = chi3_val(L4['D'], p, rho)
        if gW % 2 == 0:
            L3 = (r == chiD)
            charpart = zmul(det, zconj(chiD))             # det * conj(chi(D)) = det/chi(D)
            L5 = (charpart == (Fr(sgn * p ** (gW // 2)), Fr(0)))
        else:
            L3 = "(odd gW: no freeze)"; L5 = "(odd gW)"
        allok = allok and L1 and (L2 is True) and (L3 is True) and (L5 is True)
        detstr = f"{det[0]}{'+' if det[1] >= 0 else ''}{det[1]}w"
        P(f"  {p:>5d} {detstr:>22s} d={delta} {str(L1):>7s} {str(L2):>7s} "
          f"{str(L3):>7s} {str(L5):>7s}")
    P(f"  ALL LINKS PASS for {name}: {allok}")
    P("")
    return allok


MEMBERS = [
    # (name, f coeffs low->high, g coeffs low->high, primes)   [monic]
    ("F4-M1  f=x(x-1), g=(x-2)(x-3)(x-4)",
     [0, -1, 1], [-24, 26, -9, 1], [7, 13, 19, 31, 37, 43]),          # D=16
    ("F4-M2  f=x(x-1), g=(x-2)(x-4)(x-7)",
     [0, -1, 1], [-56, 50, -13, 1], [7, 13, 19, 31, 37, 43]),         # D=810000
    ("F4-M3  f=x(x-3), g=(x-1)(x-2)(x-5)",
     [0, -3, 1], [-10, 17, -8, 1], [7, 13, 19, 31, 37, 43]),          # D=186624
    ("F4-irr  f=x^2+1 (irreducible / roots in ext), g=(x-2)(x-3)(x-4)",
     [1, 0, 1], [-24, 26, -9, 1], [7, 13, 19, 31, 37, 43]),           # general (non-split) roots
    ("S6      f=x(x-1)(x-2)(x-3), g=(x-4)(x-5)(x-6)",
     [0, -6, 11, -6, 1], [-120, 74, -15, 1], [7, 13]),                # sixfold (3,3), D=2304
]


def main():
    out = []

    def P(s=""):
        print(s, flush=True); out.append(s)

    P("#" * 74)
    P("# FREEZE-ORDER MECHANISM : det(Frob_p | V_zeta) = p^{g/2} chi_3(disc(f)disc(g)^2)")
    P("# cyclic cubic covers y^3 = f g^2  (companion: freeze_mechanism_notes.md)")
    P("#" * 74)
    P()
    L0ok = check_L0([7, 13, 19, 31, 37, 43])
    P()
    results = {}
    for name, fc, gc, pr in MEMBERS:
        results[name] = verify_member(name, fc, gc, pr, out)
    P("#" * 74)
    P(f"SUMMARY: L0 Gauss base {'PASS' if L0ok else 'FAIL'}; "
      f"per-member all-links: " + ", ".join(f"{k.split()[0]}={v}" for k, v in results.items()))
    P("#" * 74)

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "freeze_mechanism_results.txt")
    with open(path, "w") as fh:
        fh.write("\n".join(out) + "\n")
    print(f"\n[results -> {path}]", flush=True)


if __name__ == "__main__":
    main()
