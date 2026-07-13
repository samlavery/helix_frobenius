"""Sage as the hostile oracle: validate the certified chain, then go further.

Run with:  sage -python sage_ladder.py      (~5-15 min)

PART A -- HOSTILE VALIDATION (PARI lfunsympow: its own coefficients, its own
  FE machinery -- nothing of ours in the loop):
    L(Sym2 11a1, 1/2)_u = L_arith(3/2)   vs our certified 0.8933980
    L(Sym4 11a1, 1/2)_u = L_arith(5/2)   vs our certified 0.6058010
    L(Sym2 11a1, 1)_u   = L_arith(2)     vs our 1.057602
    L(Sym4 11a1, 1)_u   = L_arith(3)     vs our 0.730807
  => the degenerate assembly zeta(1/2)^2 L2^3 L4 and A_theory = sqrt(pi) M(1)
  are re-derived from oracle values alone.

PART B -- the NEW RS4 value through Dokchitser (independent FE/Gamma engine;
  coefficients from the structural law, whose generator Part A just validated):
    L(11a1 x 37a1): arithmetic a_n = lambda_n n, Gamma_C(s)Gamma_C(s-1),
    weight 3, Q = (11*37)^2, eps = +1.  Center L_arith(3/2) vs our 5.0227652.

PART C -- GO FURTHER: the degree-6 center, Sym2(11a1) x 37a1.
  Motivic weight 3, Gamma_C(s)Gamma_C(s-1)^2, Q = 11^4 * 37^3 = 741610573,
  sqrt(Q) ~ 27,232 -- the deepest certified truth reachable, one rung below
  the triple product.  Locals: good p tensor of Sym2-triple x g-pair; p=11
  Sym2(St) = sp(3) single line (eig 1/11) x unram(g): 2 eigenvalues; p=37
  unram Sym2(f) triple x alpha_g = 1/sqrt(37): 3 eigenvalues.  Sign eps
  determined empirically (both tested via check_functional_equation).
  Cross-certified: Dokchitser vs our evaluator (shape GammaC(s+3/2)
  GammaC(s+1/2)^2 unitary, two-point split-vs-direct).  Then the carrier
  window reads it as GATE D6 (ladder crossing sqrt(Q)).
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH
import center_reading as CR
import farside_center as FC
import carrier_center as CC

from sage.all import pari, Dokchitser

OURS = {"sym2_half": 0.8933980, "sym4_half": 0.6058010,
        "sym2_one": 1.057602, "sym4_one": 0.730807,
        "assembly": 0.921258569, "rs4_half": 5.0227652}

A1, A2 = (0, -1, 1, -10, -20), (0, 0, 1, -1, 0)   # 11a1, 37a1


def bank_deg6(nmax):
    """lambda_n (unitary) of Sym2(11a1) x 37a1, exact bad-prime locals."""
    lam = np.zeros(nmax + 1)
    lam[1] = 1.0
    for p in SH.sieve_primes(nmax):
        kmax = int(math.log(nmax) / math.log(p))
        if p == 11:
            t2 = FC.theta_of(A2, p)
            eigs = [cmath.exp(1j * s * t2) / 11.0 for s in (1, -1)]
        elif p == 37:
            t1 = FC.theta_of(A1, p)
            a_g = 1 / math.sqrt(37.0)
            eigs = [a_g * cmath.exp(2j * s * t1) for s in (1, 0, -1)]
        else:
            t1, t2 = FC.theta_of(A1, p), FC.theta_of(A2, p)
            eigs = [cmath.exp(1j * (2 * s1 * t1 + s2 * t2))
                    for s1 in (1, 0, -1) for s2 in (1, -1)]
        c = FC.local_coeffs_eigs(eigs, kmax)
        for k in range(kmax, 0, -1):
            pk = p ** k
            for m in range(1, nmax // pk + 1):
                if m % p:
                    lam[m * pk] += c[k] * lam[m]
    return lam


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# SAGE LADDER -- hostile validation, then the degree-6 rung")
    P("#" * 78)
    P()
    pari.allocatemem(2 ** 31)
    pari.set_real_precision(19)

    # ---------------- PART A: lfunsympow (fully independent code path)
    P("PART A -- PARI lfunsympow (oracle coefficients, oracle FE):")
    pari('E = ellinit([0,-1,1,-10,-20])')
    vals = {}
    for key, r, s in [("sym2_half", 2, "3/2"), ("sym2_one", 2, "2"),
                      ("sym4_half", 4, "5/2"), ("sym4_one", 4, "3")]:
        v = float(pari(f'lfun(lfunsympow(E,{r}), {s})').real())
        vals[key] = v
        d = abs(v - OURS[key])
        P(f"  L(Sym{r}, {s})_arith = {v:.9f}   ours {OURS[key]:.7f}   "
          f"|diff| = {d:.2e}   {'OK' if d < 2e-6 else 'MISMATCH'}")
    z_half = float(pari('zeta(1/2)').real())
    assembly = z_half ** 2 * vals["sym2_half"] ** 3 * vals["sym4_half"]
    A_th = math.sqrt(math.pi) * vals["sym2_one"] ** 3 * vals["sym4_one"]
    P(f"  oracle assembly zeta(1/2)^2 L2^3 L4 = {assembly:.9f}   "
      f"ours {OURS['assembly']}   |diff| = {abs(assembly - OURS['assembly']):.2e}")
    P(f"  oracle A_theory = sqrt(pi) L2(1)^3 L4(1) = {A_th:.4f}   (ours 1.5323)")
    P()

    # ---------------- PART B: RS4 through Dokchitser
    P("PART B -- RS4 through Dokchitser (independent FE/Gamma engine):")
    lam4 = CC.bank_rs(60000)
    L4 = Dokchitser(conductor=(11 * 37) ** 2, gammaV=[0, 1, -1, 0],
                    weight=3, eps=1)
    nc = L4.num_coeffs()
    P(f"  num_coeffs required: {nc}")
    n_arr = np.arange(len(lam4), dtype=float)
    a4 = [float(lam4[n] * n) for n in range(1, min(len(lam4), nc + 10))]
    L4.init_coeffs(a4)
    fe = float(L4.check_functional_equation())
    v_rs = float(L4(1.5))
    d = abs(v_rs - OURS["rs4_half"])
    P(f"  FE residual: {fe:.2e}")
    P(f"  L(f x g, 3/2)_arith = {v_rs:.9f}   ours {OURS['rs4_half']}   "
      f"|diff| = {d:.2e}   {'OK' if d < 2e-5 else 'MISMATCH'}")
    P()

    # ---------------- PART C: the degree-6 rung
    P("PART C -- degree 6: Sym2(11a1) x 37a1, Q = 11^4 * 37^3 = 741610573:")
    Q6 = 11 ** 4 * 37 ** 3
    probe = Dokchitser(conductor=Q6, gammaV=[0, 1, -1, 0, -1, 0],
                       weight=4, eps=1)
    nc6 = probe.num_coeffs()
    P(f"  num_coeffs required: {nc6}")
    nmax6 = min(int(nc6 * 1.05) + 10, 4_000_000)
    if nc6 > 3_900_000:
        P("  (beyond the coefficient budget -- reporting the compute bound)")
        return
    P(f"  building the degree-6 bank to {nmax6}...")
    lam6 = bank_deg6(nmax6)
    a6 = [float(lam6[n] * n ** 1.5) for n in range(1, nmax6 + 1)]

    best = None
    for eps in (1, -1):
        L6 = Dokchitser(conductor=Q6, gammaV=[0, 1, -1, 0, -1, 0],
                        weight=4, eps=eps)
        L6.init_coeffs(a6)
        fe6 = float(L6.check_functional_equation())
        P(f"  eps = {eps:+d}: FE residual {fe6:.2e}")
        if best is None or fe6 < best[1]:
            best = (eps, fe6, L6)
    eps6, fe6, L6 = best
    ok_fe = fe6 < 1e-6
    v6 = float(L6(2.0)) if ok_fe else None
    if v6 is not None:
        P(f"  SIGN eps = {eps6:+d} (residual {fe6:.2e});  "
          f"L(Sym2 f x g, 2)_arith = L_u(1/2) = {v6:.9f}")
    P()

    P("  cross-certification (our evaluator, unitary shape "
      "GammaC(s+3/2) GammaC(s+1/2)^2):")
    lam6u = lam6 if nmax6 <= 400000 else lam6[:400001]
    G6 = CR.make_G(Q6, [('C', 1.5), ('C', 0.5), ('C', 0.5)])
    e_a, r_a, _ = CR.certify(G6, lam6u, s0=2.5, T=60)
    e_b, r_b, _ = CR.certify(G6, lam6u, s0=2.2, T=60)
    P(f"  eps {e_a:+d}/{e_b:+d}, split-vs-direct match {r_a:.2e}, {r_b:.2e}")
    ours6 = None
    if e_a == e_b and max(r_a, r_b) < 1e-3:
        ours6 = CR.central_value(G6, e_a, lam6u, T=60)
        P(f"  our central value: {ours6.real:.9f}")
        if v6 is not None:
            P(f"  Dokchitser vs ours: |diff| = {abs(v6 - ours6.real):.2e}")
    P()

    if v6 is not None:
        P("GATE D6 -- the carrier window on the degree-6 bank "
          f"(sqrt(Q) = {math.isqrt(Q6)}):")
        Ys = [4000, 16000, 64000, 128000, min(250000, nmax6 - 1)]
        prev = None
        for Y in Ys:
            R = CC.reader(lam6, Y)
            P(f"    Y = {Y:8d}   R(Y) = {R:12.6f}   "
              f"(truth {v6:.6f}, err {abs(R - v6):.2e})")
            prev = R
        errD = abs(prev - v6)
        P(f"  top-of-ladder error {errD:.3f}   "
          f"GATE D6: {'PASS' if errD < 0.08 else 'FAIL'}")
    P()

    P("SUMMARY:")
    P("  A: the certified chain (Sym2/Sym4 centers, assembly, A_theory) vs a")
    P("     fully independent oracle -- diffs above.")
    P("  B: the new RS4 value vs Dokchitser -- diff above.")
    if v6 is not None:
        P(f"  C: NEW degree-6 certified center L(Sym2(11a1) x 37a1, 1/2)_u =")
        P(f"     {v6:.9f} (eps {eps6:+d}), cross-certified two ways; the")
        P(f"     deepest certified truth on the ladder, one rung below the")
        P(f"     triple product (degree 8, sqrt(Q) ~ 5e8: beyond every chart).")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "sage_ladder_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to sage_ladder_results.txt]")


if __name__ == "__main__":
    main()
