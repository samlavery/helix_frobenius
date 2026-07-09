"""HIDA WEIGHT-LIFT — PIECE 2 (DLR Elliptic Stark LHS route): the classical weight-k companion.

GOAL.  Build the classical space carrying the weight-k Hida-family companion G_k of the
tetrahedral (A4) weight-1 form g (level 124, nebentype chi, coeffs in Q(zeta12), p=13), and
LOCATE the ordinary eigenform G_k whose residual (mod 13) Hecke system matches g's.

WHAT THIS FILE ESTABLISHES (all MEASURED via Sage modular symbols; residual target IN-HOUSE):

  * The companion is NOT a level-124 object.  Its nebentype is chi*omega^{k-1} (omega =
    Teichmuller char at 13), which is RAMIFIED at 13 for k != 1 (mod 12).  Hence G_k is a
    13-NEW newform of level 1612 = 124*13, weight k.  (The task's "M_k(Gamma_1(124),...)"
    and the level-124 dimension formula do NOT describe this object; corrected here.)
    dim S_3(Gamma_0(1612), chi*omega^2) = 444 over Q(zeta6) (Sage). Sturm bound ~ 3*2688/12.

  * CONTINUOUS TATE TWIST.  A weight-k form congruent to weight-1 g cannot share g's nebentype
    unless k == 1 (mod p-1) (Serre weight relation).  For 2<=k<=p-1 the companion is a Tate
    twist g (x) omega^t: its residual Galois rep is rho_g (x) omega^t, so
        a_ell(G_k) == a_ell(g) * ell^t   (mod 13),   nebentype = chi*omega^{2t-2}.
    G_k is projectively == g for every t (twisting by a character preserves the A4 projective
    image).  The Hida-family / DLR companion is the specific t; the natural half-twist is
    t = (k-1)/2.  This file scans t and reports where (if anywhere) the g-system lands as a
    genuine common eigenvector across many primes (not a low-prime coincidence).

METHOD.  Modular symbols M_k(Gamma_1(1612)) with the exact nebentype (chi built to match the
in-house hida_family.chi_mod_p; omega = Teichmuller via zeta12->7).  T_ell (ell coprime to
1612) are computed over the character field Q(zeta6) and reduced at the four primes above 13
(zeta12 -> {2,6,7,11}).  Reduction is EXACT for eigenvalues (13-integral matrices => charpoly
reduces), so target_ell present <=> some char-0 form has that residual a_ell.  The companion
= common eigenvector of all T_ell at the g-target; U_13 (= Hecke at 13, 13|level) read on it
gives the ordinary unit residue (the "off unit=1" crux).

NON-CIRCULAR: the residual target a_ell(g) mod 13 comes from the certified in-house a_p engine
(hida_family / rung3_lhs.a_p_h_exponent).  Sage supplies only the modular-symbols geometry of
the *ambient* space and the Hecke matrices; the eigenform is singled out by the in-house target.

Run (needs Sage):   sage -python hida_piece2.py [k] [tmin tmax]
  default k=3, scans t = 0..5 (the six nebentype classes chi*omega^{-2..8}).
"""
import sys, time

from sage.all import (CyclotomicField, DirichletGroup, GF, QQ, ModularSymbols,
                      matrix, identity_matrix, gcd)

sys.path.insert(0, '.')
from rung3_lhs import _IND31, a_p_h_exponent          # certified a_p engine (in-house)
from hida_family import chi_mod_p                       # PIECE 1 residual nebentype

P = 13
NTAME = 124
NLEV = 1612                                             # = 124 * 13
GOOD = [3, 5, 7, 11, 17, 19, 23, 29, 37, 41, 43]        # primes coprime to 1612
PRIM = [2, 6, 7, 11]                                    # zeta12 -> r, the 4 primes above 13


def build_chars():
    """chi (mod 124, matches in-house chi_mod_p) and omega (Teichmuller mod 13), over Q(zeta12)."""
    K = CyclotomicField(12)
    z12 = K.gen()

    def dlog7(n):
        n %= 13
        for e in range(12):
            if pow(7, e, 13) == n:
                return e

    def chi_tgt(n):
        n = int(n) % 124
        if n % 2 == 0 or n % 31 == 0:
            return None
        return z12 ** ((6 * (1 if n % 4 == 3 else 0) + 8 * (_IND31[n % 31] % 3)) % 12)

    G124 = DirichletGroup(124, K)
    chi = next(c for c in G124
               if all(c(n) == chi_tgt(n) for n in range(1, 124) if gcd(n, 124) == 1))
    G13 = DirichletGroup(13, K)
    om = next(c for c in G13 if all(c(n) == z12 ** dlog7(n) for n in range(1, 13)))
    return K, z12, chi, om


def reducer(F):
    def rd(a, r):
        Par = a.parent()
        try:
            c = QQ(a)
            return F(int(c.numerator()) % 13) * F(int(c.denominator()) % 13) ** -1
        except (TypeError, ValueError):
            pass
        m = int(Par._n())
        gred = F(r) ** (12 // m)
        s = F(0)
        for i, c in enumerate(a.list()):
            c = QQ(c)
            s += F(int(c.numerator()) % 13) * F(int(c.denominator()) % 13) ** -1 * gred ** i
        return s
    return rd


def search_twist(k, t, chi, om, z12, rd, F, log=print):
    """Search S_k(Gamma_0(1612), chi*omega^{2t-2}) for the twist g (x) omega^t:
       target a_ell == a_ell(g)*ell^t == z12^{e_ell}*ell^t (residually).  Returns dict."""
    exps = {l: a_p_h_exponent(l) for l in GOOD}
    charr = chi.extend(NLEV) * om.extend(NLEV) ** (2 * t - 2)
    T = time.time()
    M = ModularSymbols(charr, k, sign=1)
    S = M.cuspidal_subspace()
    n = S.dimension()
    log(f"  t={t}: nebentype chi*omega^{2*t-2}, cuspdim={n}, "
        f"field={S.hecke_matrix(3).base_ring()} [{time.time()-T:.0f}s]")
    Tk = {l: S.hecke_matrix(l) for l in GOOD}
    out = {"t": t, "dim": n, "hits": []}
    for r in PRIM:
        V = None
        for l in GOOD:
            e = exps[l]
            tgt = F(0) if e is None else F(pow(r, e, 13)) * F(pow(l, t, 13))
            Tlb = matrix(F, [[rd(Tk[l][i, j], r) for j in range(n)] for i in range(n)])
            ker = (Tlb - tgt * identity_matrix(F, n)).right_kernel()
            V = ker if V is None else V.intersection(ker)
        d = V.dimension()
        log(f"    embedding zeta12->{r}: g(x)omega^{t} eigenspace dim = {d} "
            f"(over {len(GOOD)} primes)")
        if d > 0:
            U = S.hecke_matrix(13)
            Ub = matrix(F, [[rd(U[i, j], r) for j in range(n)] for i in range(n)])
            B = V.basis_matrix()
            piv = B.pivots()
            Bp = B.matrix_from_columns(piv)
            MU = (B * Ub).matrix_from_columns(piv) * Bp.inverse()
            evs = MU.eigenvalues()
            log(f"       >>> CAPTURED. U_13 residues on eigenspace = {evs} "
                f"(unit <=> nonzero; g's 13-roots reduce to {{1, zeta3=9}})")
            out["hits"].append({"r": r, "dim": d, "U13": [int(e) for e in evs]})
    return out


def positive_control(F, log=print):
    """Validate the instrument: the SAME mod-13 T_ell intersection method must recover the
    13-NEW newforms 26a, 26b (13 | 26) in S_2(Gamma_0(26)) from their a_ell.  If it finds them,
    a null in the g-search below is a real absence, not a 13-new reduction artifact."""
    from sage.all import EllipticCurve
    M = ModularSymbols(26, 2, sign=1)
    S = M.cuspidal_subspace()
    n = S.dimension()
    gd = [3, 5, 7, 11, 17, 19, 23]
    ok = True
    for lab in ('26a', '26b'):
        an = EllipticCurve(lab).anlist(60)
        V = None
        for l in gd:
            Tl = S.hecke_matrix(l)
            Tlb = matrix(F, [[F(QQ(Tl[i, j])) for j in range(n)] for i in range(n)])
            ker = (Tlb - F(an[l]) * identity_matrix(F, n)).right_kernel()
            V = ker if V is None else V.intersection(ker)
        d = V.dimension()
        ok = ok and d == 1
        log(f"  [control] {lab} (13-new): common eigenspace dim = {d} "
            f"[{'FOUND' if d == 1 else 'MISSED'}]")
    log(f"  [control] instrument {'VALIDATED (finds 13-new forms)' if ok else 'FAILED'}")
    return ok


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'control':
        positive_control(GF(13))
        return
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    if len(sys.argv) > 3:
        tmin, tmax = int(sys.argv[2]), int(sys.argv[3])
    else:
        tmin, tmax = 0, 5
    K, z12, chi, om = build_chars()
    F = GF(13)
    rd = reducer(F)
    # self-check: chi reduces (zeta12->7) to the in-house residual nebentype
    ok = all(rd(chi(n), 7) == F(chi_mod_p(n)) for n in range(1, 124) if gcd(n, 124) == 1)
    print(f"[self-check] chi (Sage) reduces to hida_family.chi_mod_p: {'PASS' if ok else 'FAIL'}")
    print(f"[target] residual a_ell(g) = zeta12^e, e = "
          f"{ {l: a_p_h_exponent(l) for l in GOOD} }  (zeta12->7)")
    captured = []
    for t in range(tmin, tmax + 1):
        res = search_twist(k, t, chi, om, z12, rd, F)
        if res["hits"]:
            captured.append(res)
    print()
    if captured:
        for c in captured:
            print(f"CAPTURED companion at k={k}, twist t={c['t']} "
                  f"(nebentype chi*omega^{2*c['t']-2}); U_13 residues {c['hits']}")
    else:
        print(f"NO Tate-twist companion g(x)omega^t (t={tmin}..{tmax}) found as a full "
              f"multi-prime common eigenvector at weight k={k} via mod-13 Hecke reduction.")


if __name__ == "__main__":
    main()
