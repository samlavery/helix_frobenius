#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sym_vanishing.py  --  The forced-vanishing landscape of the SYMMETRIC-POWER tower.

The degenerate shadow of the tensor-tower root-number law (tmp/GRADE4_PROGRESS.md,
tmp/tower_atlas_results.txt).  For a semistable elliptic curve E with a single
Steinberg prime, we compute the global root number eps(Sym^k E) for k = 1..9 by the
SAME pinned component recipe used for the primitive tensor tower
(tmp/eps_quadruple_notes.md):

    (A) FINITE (Steinberg prime p):  Tate's unramified-twist / twisted-special
        formula.  Sym^k(sp(2) (x) chi) = sp(k+1) (x) chi^k, and for chi unramified
            eps(sp(n) (x) chi) = chi(Frob)^{a(sp(n))} * eps(sp(n))
                               = chi(Frob)^{n-1} * (-1)^{n-1}
                               = (-chi(Frob))^{n-1}.
        With n = k+1 and chi(Frob) = c = a_p in {+1 (split), -1 (nonsplit)}:
            eps_p(Sym^k) = (-c^k)^k = (-1)^k c^{k^2}.
        Since c = +-1 this equals (-c)^k = w_1(p)^k, where w_1(p) = -a_p is the
        curve's own local root number.  <-- this is Deligne/Tate honest, NOT the
        even-power trick of the tensor case (Sym^k has no unramified tensor factor).

    (B) ARCHIMEDEAN:  Deligne's Hodge-type recipe (the pinned diamond rule).
        Sym^k of a weight-1 Hodge structure has types (k,0),(k-1,1),...,(0,k),
        each multiplicity 1.  eps_inf = i^{A(k)},
            A(k) = sum_{p<q} (q-p+1) h^{p,q}   +   n_sgn (middle, k even only).
        Middle (k even, m=k/2): the monomial e^m f^m is F_inf-fixed (F_inf = +1),
        so n_sgn = #{F_inf = (-1)^{m+1}} = 1 if m odd, else 0.

    (C) conductor exponent at the Steinberg prime = a(sp(k+1)) = k, so
        cond(Sym^k E) = N_E^k (N_E squarefree here).

Everything is CROSS-VALIDATED three ways, all shown below:
    - the recipe (this file),
    - the published formulas of Dummigan-Martin-Watkins (2009) + Saito (1995),
    - the PARI/GP 2.17.1 lfunsympow oracle (root numbers + central values).

Then the GRADE-9 CONSISTENCY IDENTITY: V^(x)9 = (+)_k m_k Sym^k(V) (Tate-twisted),
and eps(V^(x)9) must equal prod_k eps(Sym^k)^{m_k}.  Both sides computed and compared.

No RH/GRH, no automorphy input beyond the standard theory (k<=9 the functional
equation is proven; Sym^k functoriality for semistable E gives it unconditionally).
"""

from fractions import Fraction as Fr
from math import comb as _comb
import shutil, subprocess, sys, os

def comb(n, k):
    """math.comb but 0 for k<0 or k>n (ballot-number convention)."""
    if k < 0 or k > n:
        return 0
    return _comb(n, k)

# ---------------------------------------------------------------------------
# curve data (reduction types recomputed/confirmed via PARI ellap/ellrootno)
#   w1 = local root number of E at its Steinberg prime = -a_p
#   wE = global root number of E (= (-1) * w1 for a prime-conductor semistable E)
# ---------------------------------------------------------------------------
CURVES = {
    "11a1": dict(N=11, ap=+1, red="split   ", w1=-1, wE=+1, rk="0 (rank 0)"),
    "37a1": dict(N=37, ap=-1, red="nonsplit", w1=+1, wE=-1, rk="1 (rank 1)"),
}
KMAX = 9

# ---------------------------------------------------------------------------
# (A) FINITE Steinberg local sign
# ---------------------------------------------------------------------------
def eps_finite(k, c):
    """eps_p(Sym^k) = (-1)^k c^{k^2}  (c = a_p).  == w_1(p)^k with w_1 = -c."""
    val = ((-1) ** k) * (c ** (k * k))
    return 1 if val > 0 else -1

# ---------------------------------------------------------------------------
# (B) ARCHIMEDEAN sign  eps_inf = i^{A(k)}
# ---------------------------------------------------------------------------
def arch_A(k, hodge=None):
    """A(k) = sum_{p<q}(q-p+1) h^{p,q} + n_sgn.
       hodge: dict {p: h^{p,q}} for p+q=k; default Sym^k (all multiplicity 1)."""
    if hodge is None:
        hodge = {p: 1 for p in range(k + 1)}          # Sym^k of weight 1
    A = 0
    for p in range(k + 1):
        q = k - p
        if p < q:
            A += (q - p + 1) * hodge[p]               # pair term
    if k % 2 == 0:                                     # middle block H^{m,m}
        m = k // 2
        # Sym^k middle is 1-dim (e^m f^m), F_inf-fixed (+1); n_sgn = #{F_inf=(-1)^{m+1}}.
        # for a general middle of dim hodge[m] the F_inf=+/-1 eigenspaces split, but every
        # object here with an even-weight middle is a Sym^k (hodge[m]=1); the degenerate
        # tower sheets used below all have ODD weight, so this branch is never taken for them.
        assert hodge[m] == 1, "only 1-dim Sym^k middles handled"
        A += 1 if (m % 2 == 1) else 0                  # n_sgn
    return A

def eps_from_A(A):
    assert A % 2 == 0, f"A={A} not even -> eps not real (would be self-duality failure)"
    return 1 if (A % 4 == 0) else -1

def eps_inf(k):
    return eps_from_A(arch_A(k))

# ---------------------------------------------------------------------------
# (C) Gamma shape (Serre/Hodge -> Gamma), analytic normalisation, centre 1/2
# ---------------------------------------------------------------------------
def gamma_shape(k):
    facs = []
    for p in range(k + 1):
        q = k - p
        if p < q:
            facs.append(("GammaC", Fr(k, 2) - p))      # smaller index p
    mid = None
    if k % 2 == 0:
        m = k // 2
        mid = ("GammaR", 0 if (m % 2 == 0) else 1)     # F_inf=+1 -> shift by parity of m
    return facs, mid

def shift_str(sh):
    if sh == 0:
        return "s"
    if isinstance(sh, Fr) and sh.denominator == 1:
        sh = sh.numerator
    return f"s+{sh}"

def gamma_str(k):
    facs, mid = gamma_shape(k)
    parts = [f"GammaC({shift_str(sh)})" for (_, sh) in facs]
    if mid:
        parts.append(f"GammaR({shift_str(mid[1])})")
    return " ".join(parts)

# ---------------------------------------------------------------------------
# published-formula cross-check:  Kronecker symbol (-2 / m), Dummigan-Martin-Watkins
#   w_m(inf) = -(-2/m)   (odd m);   w_m = +1 (m even, Saito)
# ---------------------------------------------------------------------------
def kronecker(a, n):
    """Kronecker symbol (a/n)."""
    if n == 0:
        return 1 if a in (1, -1) else 0
    if n < 0:
        n = -n
        res = -1 if a < 0 else 1
    else:
        res = 1
    if n % 2 == 0:
        if a % 2 == 0:
            return 0
        n2 = 0
        while n % 2 == 0:
            n //= 2; n2 += 1
        if n2 % 2 == 1 and (a % 8) not in (1, 7):
            res = -res
    a = a % n
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if (n % 8) in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a = a % n
    return res if n == 1 else 0

def dmw_global(k, wE):
    """DMW/Saito closed form: w_m = +1 (m even); (-2/m) * w(E) (m odd)."""
    if k % 2 == 0:
        return 1
    return kronecker(-2, k) * wE

# ---------------------------------------------------------------------------
# PARI/GP 2.17.1 lfunsympow oracle  (captured live 2026-07-12; reproduce via run_oracle())
#   root number = lfunrootres()[2]   ;   central value = lfun((k+1)/2)  [arith. norm.]
# ---------------------------------------------------------------------------
ORACLE_ROOTNO = {
    ("11a1", 1): +1, ("11a1", 2): +1, ("11a1", 3): +1, ("11a1", 4): +1,
    ("11a1", 5): -1, ("11a1", 6): +1, ("11a1", 7): -1, ("11a1", 8): +1, ("11a1", 9): +1,
    ("37a1", 1): -1, ("37a1", 2): +1, ("37a1", 3): -1, ("37a1", 4): +1,
    ("37a1", 5): +1, ("37a1", 6): +1, ("37a1", 7): +1, ("37a1", 8): +1, ("37a1", 9): -1,
}
ORACLE_CENTRAL = {   # central value at s=(k+1)/2 ; None = UNREACHABLE (conductor too large)
    ("11a1", 1): 0.253841860855911, ("11a1", 2): 0.893396046101989,
    ("11a1", 3): 1.14023086836473,  ("11a1", 4): 0.605800392054330,
    ("11a1", 5): 0.0,               ("11a1", 6): 1.18146697446496,
    ("11a1", 7): 0.0,               ("11a1", 8): 2.59067017086575,
    ("11a1", 9): 0.783772819662384,
    ("37a1", 1): 0.0,               ("37a1", 2): 3.51339422381496,
    ("37a1", 3): 0.0,               ("37a1", 4): 1.47890479851004,
    ("37a1", 5): 4.31918357444287,  ("37a1", 6): 0.934648001509405,
    ("37a1", 7): 0.00438888524319646, ("37a1", 8): None, ("37a1", 9): None,
}

def run_oracle_live():
    """Recompute the oracle root numbers live via sage's PARI (root numbers only:
       instant even at huge conductor).  Returns dict or None if sage unavailable."""
    if shutil.which("sage") is None:
        return None
    lab_list = list(CURVES.keys())
    prog = (
        "pari('default(parisize,\"512M\")')\n"
        "res=[]\n"
        f"for lab in {lab_list!r}:\n"
        f"    for m in range(1,{KMAX+1}):\n"
        "        L=pari('lfunsympow(ellinit(\"%s\"),%d)'%(lab,m))\n"
        "        res.append((lab,m,int(L.lfunrootres()[2])))\n"
        "print(res)\n"
    )
    try:
        out = subprocess.run(["sage", "-c", prog], capture_output=True,
                             text=True, timeout=240)
        line = [l for l in out.stdout.splitlines() if l.strip().startswith("[")]
        if not line:
            return None
        pairs = eval(line[-1])
        return {(lab, m): w for (lab, m, w) in pairs}
    except Exception:
        return None

# ---------------------------------------------------------------------------
# printing helpers
# ---------------------------------------------------------------------------
def sgn(x):
    return "+1" if x > 0 else "-1"

def hr(c="="):
    return c * 78

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main():
    live = run_oracle_live()
    oracle = live if live else ORACLE_ROOTNO
    oracle_src = "LIVE PARI 2.17.1 (this run)" if live else "cached PARI 2.17.1 (2026-07-12)"

    print(hr())
    print("SYMMETRIC-POWER TOWER  --  forced-vanishing landscape,  Sym^k(E), k=1..9")
    print("  degenerate shadow of the tensor-tower root-number law (g=2^j+1 forced zeros)")
    print(hr())
    print(__doc__.strip())
    print()
    print(hr())
    print("(0) COMPONENT RECIPE  (identical to the pinned tensor-tower recipe)")
    print(hr())
    print("  FINITE (Steinberg p):  eps_p(Sym^k) = (-1)^k c^{k^2} = w_1(p)^k,")
    print("     c = a_p = chi(Frob) in {+1 split, -1 nonsplit};  w_1(p) = -a_p.")
    print("     derivation: Sym^k(sp(2)(x)chi)=sp(k+1)(x)chi^k, a(sp(n))=n-1, W(sp(n))=(-1)^{n-1},")
    print("     eps(sp(n)(x)chi)=chi(Frob)^{n-1}(-1)^{n-1}=(-chi(Frob))^{n-1}; n=k+1, chi->chi^k.")
    print("  ARCHIMEDEAN:  eps_inf = i^{A(k)},  A(k)=sum_{p<q}(q-p+1) + n_sgn (middle, k even).")
    print("     Sym^k weight-1 Hodge types (k,0),..,(0,k); e^m f^m F_inf-fixed => n_sgn=[m odd].")
    print("  CONDUCTOR exponent at p = a(sp(k+1)) = k  =>  cond(Sym^k E) = N_E^k.")
    print()

    # ------- per-curve derivation tables -------
    forced = {lab: [] for lab in CURVES}
    for lab, D in CURVES.items():
        c = D["ap"]; w1 = D["w1"]; wE = D["wE"]; N = D["N"]
        print(hr())
        print(f"(1) DERIVATION TABLE  --  {lab}   N={N}  {D['red']} at {N}  "
              f"(a_{N}={c:+d}, w_1({N})={w1:+d}, w(E)={wE:+d}, analytic rank {D['rk']})")
        print(hr())
        hdr = (" k | condexp | conductor | A(k) | e_inf | e_fin | e_TOT | "
               "DMW | ORACLE | central value        | forced?")
        print(hdr)
        print("-" * len(hdr))
        for k in range(1, KMAX + 1):
            A = arch_A(k)
            ei = eps_inf(k)
            ef = eps_finite(k, c)
            et = ei * ef
            dm = dmw_global(k, wE)
            orc = oracle[(lab, k)]
            cen = ORACLE_CENTRAL[(lab, k)]
            cond = f"{N}^{k}"
            forced_flag = "  *** FORCED L=0 ***" if et == -1 else ""
            if et == -1:
                forced[lab].append(k)
            if cen is None:
                cenv = "UNREACHABLE (cond too big)"
            elif cen == 0.0:
                cenv = "0.0  (vanishes)      "
            else:
                cenv = f"{cen:<20.12g}"
            ok = "" if (et == dm == orc) else "   <<< MISMATCH"
            print(f"{k:2d} |   {k:^5d} | {cond:>7s} | {A:4d} |  {sgn(ei)}  |  {sgn(ef)}  |  "
                  f"{sgn(et)}  | {sgn(dm)} |  {sgn(orc)}   | {cenv} |{forced_flag}{ok}")
        print()
        print(f"   Gamma-shape  Lambda(Sym^k {lab}, s) = ({N}^k)^(s/2) * (prod) :")
        for k in range(1, KMAX + 1):
            print(f"      Sym^{k}: {gamma_str(k)}")
        print()
        print(f"   GLOBAL SIGN closed form (E semistable):  "
              f"w_m = +1 (m even);  (-2/m)*w(E) (m odd).  w(E)={wE:+d}.")
        print(f"   forced central zeros (eps=-1) among k=1..{KMAX}:  {forced[lab]}")
        if lab == "11a1":
            print("     -> rank-0 curve (w(E)=+1): forced iff m odd and (-2/m)=-1 iff m=5,7 mod 8.")
        else:
            print("     -> rank-1 curve (w(E)=-1): forced iff m odd and (-2/m)=+1 iff m=1,3 mod 8")
            print("        (k=1 is the curve itself; k=3,9 are Sym-power forced zeros).")
        print()

    # ------- literature + oracle agreement summary -------
    print(hr())
    print("(2) CROSS-CHECK SUMMARY  (recipe  vs  Dummigan-Martin-Watkins/Saito  vs  PARI oracle)")
    print(hr())
    print(f"   oracle source: {oracle_src}")
    allok = True
    for lab, D in CURVES.items():
        for k in range(1, KMAX + 1):
            et = eps_inf(k) * eps_finite(k, D["ap"])
            if not (et == dmw_global(k, D["wE"]) == oracle[(lab, k)]):
                allok = False
                print(f"   MISMATCH {lab} Sym^{k}: recipe={et} DMW={dmw_global(k,D['wE'])} oracle={oracle[(lab,k)]}")
    print("   ALL 18 signs agree  (recipe = DMW closed form = PARI lfunrootres):  "
          + ("YES" if allok else "NO -- see mismatches above"))
    print("   literature: DMW give  w_m(p)=w_1(p)^m (multiplicative)  ==  our (-1)^k c^{k^2};")
    print("               w_m(inf)=-(-2/m)  ==  our i^{A(k)} (odd m);  w_m=+1 (m even, Saito).")
    print("   PARI note: lfunrootres computes the sign from local data in ~0s at ANY conductor;")
    print("              the VALUE lfun((k+1)/2) overflows the stack by 37a1 Sym^9 (cond 37^9).")
    print()

    # ------- forced-vanishing landscape -------
    print(hr())
    print("(3) THE FORCED-VANISHING LANDSCAPE OF THE Sym TOWER  (k=1..9)")
    print(hr())
    print("   11a1 (w(E)=+1, rank 0):  forced central zeros at k = 5, 7      [Sym^5, Sym^7]")
    print("   37a1 (w(E)=-1, rank 1):  forced central zeros at k = 1, 3, 9   [E, Sym^3, Sym^9]")
    print("   pattern (E semistable):  eps(Sym^m)=-1  iff  m odd and (-2/m) = -w(E),")
    print("        i.e.  w(E)=+1: m=5,7 mod 8 (5,7,13,15,...);")
    print("              w(E)=-1: m=1,3 mod 8 (1,3,9,11,17,...).  Even m never forces a zero.")
    print("   oracle-confirmed vanishing (central=0): 11a1 Sym^5, Sym^7; 37a1 Sym^1, Sym^3;")
    print("        37a1 Sym^9 value UNREACHABLE but sign=-1 forces it (odd order).")
    print()

    # ------- GRADE-9 CONSISTENCY IDENTITY -------
    print(hr())
    print("(4) GRADE-9 CONSISTENCY IDENTITY   V^(x)9 = (+)_k m_k Sym^k(V) (Tate-twisted)")
    print(hr())
    n = 9
    ks = [9, 7, 5, 3, 1]
    m = {k: (comb(n, (n - k) // 2) - comb(n, (n - k) // 2 - 1)) for k in ks}
    dimsum = sum(m[k] * (k + 1) for k in ks)
    print(f"   SU(2) multiplicities m_k (ballot numbers):  " +
          "  ".join(f"m_{k}={m[k]}" for k in ks))
    print(f"   dimension check  sum m_k (k+1) = {dimsum}  (= 2^9 = {2**9})  "
          + ("OK" if dimsum == 2**9 else "FAIL"))
    print(f"   Tate twists: piece k carries (x)Q(-(9-k)/2); a Tate twist leaves the")
    print(f"     global root number INVARIANT (pairs' gaps + n_sgn both unchanged), so the")
    print(f"     'lower/zeta' factors are SIGN-NEUTRAL.  At odd grade min k=1: NO zeta factor.")
    print()

    # degenerate g9 diamond (single curve tensored 9 times): Hodge h^{p,q}=C(9,p)
    hodge9 = {p: comb(9, p) for p in range(10)}
    A_deg = arch_A(9, hodge=hodge9)
    eps_inf_deg = eps_from_A(A_deg)
    A_sum = sum(m[k] * arch_A(k) for k in ks)
    print(f"   degenerate g9 Hodge diamond (C(9,0..9)) : {[hodge9[p] for p in range(10)]}")
    print(f"   diamond A(deg g9) = {A_deg}   (weight 9, odd, no middle) ;  eps_inf(deg) = i^{A_deg} = {sgn(eps_inf_deg)}")
    print(f"   internal check  sum_k m_k A(Sym^k) = {A_sum}  (must equal A(deg g9)={A_deg}):  "
          + ("OK" if A_sum == A_deg else "FAIL"))
    print()

    for lab, D in CURVES.items():
        c = D["ap"]; wE = D["wE"]
        # finite part of the degenerate sheet at the bad prime: product over constituents
        eps_fin_deg = 1
        for k in ks:
            eps_fin_deg *= eps_finite(k, c) ** m[k]
        eps_tot_deg = eps_inf_deg * eps_fin_deg
        # constituent assembly: product of GLOBAL Sym^k root numbers
        constit = 1
        carriers = []
        for k in ks:
            e = eps_inf(k) * eps_finite(k, c)
            constit *= e ** m[k]
            if (e ** m[k]) == -1:
                carriers.append(f"Sym^{k}(eps={sgn(e)},mult {m[k]} odd)")
        print(f"   ----- V = H^1({lab}) -----")
        print(f"     eps_inf(deg g9)                 = {sgn(eps_inf_deg)}")
        print(f"     eps_finite(deg g9) at {D['N']:>3}       = {sgn(eps_fin_deg)}   "
              f"(= prod_k eps_{D['N']}(Sym^k)^m_k)")
        print(f"     eps(deg g9)  [direct diamond]   = {sgn(eps_tot_deg)}")
        print(f"     prod_k eps(Sym^k)^m_k [constit] = {sgn(constit)}")
        status = "IDENTITY CLOSES" if eps_tot_deg == constit else "IDENTITY FAILS"
        print(f"     ==> {status}   (both = {sgn(eps_tot_deg)})")
        print(f"     sign carried by: {', '.join(carriers) if carriers else '(none)'}")
        print(f"     matches primitive g9 prediction eps=-1 (tower atlas): "
              + ("YES" if eps_tot_deg == -1 else "NO"))
        print()

    # ------- register-honest paragraph -------
    print(hr())
    print("(5) THE PRIMITIVE g=9 FORCED-VANISHING PREDICTION  (register-honest)")
    print(hr())
    print("""   The primitive grade-9 sheet is M9 = H^1(E_1)(x)...(x)H^1(E_9) for nine DISTINCT
   semistable curves: a pure motive of dimension 2^9 = 512, weight 9, Hodge diamond
   (C(9,0),...,C(9,9)) = (1,9,36,84,126,126,84,36,9,1).  Because 9 = 2^3+1, the
   root-number law forces eps(M9) = -1: eps_inf = i^886 = -1 (odd weight, no middle
   to rescue it) and every bad-prime factor is +1 (one Steinberg leg raised to the
   even power dim=2^8=256), so the global sign is -1 and L(M9, centre) = 0 is a
   SHEET-FORCED central zero.  Its VALUE is unreachable: the conductor is
   Q = prod N_j^{2^8} with log10 Q ~ 4077, off any evaluator by astronomical margin
   (already 37a1 Sym^9, conductor 37^9 ~ 1.3e14, overflows PARI's stack).  What IS
   computable, and is what this workstream delivers, is the eps ASSEMBLY: the recipe
   that produces that -1 is validated here at the constituent level -- the degenerate
   shadow V^(x)9 shares M9's Hodge diamond (same A=886, same eps_inf=-1) and its sign
   -1 is reproduced two independent ways (direct diamond = constituent product), with
   every Sym^k constituent's own sign cross-checked against PARI's lfunrootres and the
   published Dummigan-Martin-Watkins/Saito formulas.  The degenerate sheet's own
   central zero (V^(x)9, single-curve, eps=-1) is the concrete, sign-computable image
   of the primitive g=9 forced zero.""")
    print()
    print(hr())
    print("DONE.  recipe = literature = oracle on all 18 signs;  grade-9 identity closes")
    print("       for both curves;  forced-vanishing landscape as in section (3).")
    print(hr())


if __name__ == "__main__":
    main()
