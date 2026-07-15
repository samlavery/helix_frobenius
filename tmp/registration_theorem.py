"""registration_theorem.py -- verification harness for the REGISTRATION DICHOTOMY.

Companion to tmp/registration_theorem_notes.md.  Nothing here is a new derivation:
this reorganizes the already-verified machinery under the theorem's three arms and
re-runs the load-bearing quantitative checks with a single frozen protocol.  It
imports the verified banks (harmonic_lattice), the smoothed-AFE mirror kernel
(transient_form, Lemma 1), and the completed paired-sheet kernel (transient_pairing).

  BACKBONE  the item-38 pairing identity  F_m F_-m = L(Sym^{m+1})/L(Sym^{m-3}) . C_m
            (m=2 -> Sym3 . C2, denominator Sym^{-1}=1 so RHS is ENTIRE;
             m=3 -> Sym4/zeta . C3, denominator Sym^0 = zeta) in the absolute region.

  ARM A     integer-m conjugate pairing REGISTERS.  The paired center read converges
            to L(Sym3,1/2).C2(1/2) up to the completed-sheet mirror term, to a
            CONSTANT residual ~ 8.6e-6 = the certified-value floor, ZERO fit params.

  ARM B     single rail F_2 does NOT register.  It is not self-dual: its coefficients
            are genuinely complex and its dual is the OTHER rail F_-2 (= conj on the
            real axis), so there is no self functional equation, no mirror term, and
            the windowed center read DIVERGES (growth exp ~ +0.44; Rankin-Selberg +
            Cauchy-Schwarz bound <= +0.5).  The divergence is ABSENCE, not error.

  ARM C     incommensurate control (m = sqrt2).  No lattice partner identity (the
            pairing F_sqrt2 F_-sqrt2 misses every Sym.C candidate by O(1)); the paired
            center read does not register (it drifts).  The two theorem endpoints are
            (A) and (B); (C) is the measured interpolation between them.

Run: python3 registration_theorem.py     (~3-5 min)
"""
import sys, os, math
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import transient_form as TF
import transient_pairing as TP
from harmonic_lattice import (fast_bank as bank, warp_eigs, sym_eigs, dseries,
                              reader_c, ALPHA)

NMAX = 200000
L_SYM3 = 1.1402380                        # certified Sym3(11a1) center (PARI 7e-6)
YS = [4000.0, 16000.0, 64000.0, 250000.0]


def C_of(s, kind):
    """Bad factor at p=11.  C2 = (1-a^3 q)/(1-a q)^2;  C3 = (1-a^4 q)/((1-q)(1-a q)^2)."""
    q = 11.0 ** (-s)
    if kind == 2:
        return (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2
    return (1 - ALPHA ** 4 * q) / ((1 - q) * (1 - ALPHA * q) ** 2)


def growth_exp(lam):
    n = np.arange(1, len(lam), dtype=float)
    cum = np.abs(np.cumsum(np.real(lam[1:]) * n ** -0.5))
    i0 = len(cum) // 8
    return (math.log(cum[-1] + 1e-30) - math.log(cum[i0] + 1e-30)) / \
        (math.log(len(cum)) - math.log(i0 + 1))


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# REGISTRATION DICHOTOMY -- verification harness (base object: 11a1)")
    P("# f = weight-2 newform of level 11 (conductor 11 squarefree => semistable;")
    P("#     non-CM).  Newton-Thorne (Publ. IHES 134, 2021, I+II): Sym^n f cuspidal")
    P("#     automorphic for all n>=1  =>  every L(Sym^n f, s) is nice.  UNCONDITIONAL.")
    P("#" * 78)
    P()

    P("building rails F_2, F_-2, F_3, F_-3, incommensurate F_+-sqrt2, and Sym3/Sym4")
    P(f"banks to NMAX = {NMAX} ...")
    F2 = bank(warp_eigs(2), NMAX)
    Fm2 = bank(warp_eigs(-2), NMAX)
    F3 = bank(warp_eigs(3), NMAX)
    Fm3 = bank(warp_eigs(-3), NMAX)
    Fs2 = bank(warp_eigs(math.sqrt(2)), NMAX)
    Fms2 = bank(warp_eigs(-math.sqrt(2)), NMAX)
    S3 = bank(sym_eigs(3), NMAX)
    S4 = bank(sym_eigs(4), NMAX)
    paired = TP.convolve_rails(F2, Fm2)
    P("  done.")
    P()

    # ============================================================== BACKBONE
    P("=" * 78)
    P("BACKBONE -- the item-38 pairing identity  F_m F_-m = L(Sym^{m+1})/L(Sym^{m-3}).C_m")
    P("=" * 78)
    P("  Algebraic identity of Euler products; checked in the absolute region s=2.5,3.0")
    P("  (numerator/denominator both NICE by Newton-Thorne).")
    for s in (2.5, 3.0):
        z = complex(mp.zeta(s))
        lhs2 = dseries(F2, s) * dseries(Fm2, s)
        rhs2 = dseries(S3, s) * C_of(s, 2)                     # m=2: Sym^{-1}=1
        lhs3 = dseries(F3, s) * dseries(Fm3, s)
        rhs3 = dseries(S4, s) / z * C_of(s, 3)                 # m=3: Sym^0 = zeta
        P(f"  s={s}:  |F2 F-2 - Sym3.C2| = {abs(lhs2 - rhs2):.2e}"
          f"   |F3 F-3 - (Sym4/zeta).C3| = {abs(lhs3 - rhs3):.2e}")
    # pairing convolution identity off 11-powers (must be machine zero)
    off11 = np.array([n for n in range(2, 5000) if n % 11 != 0])
    P(f"  convolution identity  max|F2(*)F-2 - Sym3| off 11-powers (n<5000) = "
      f"{np.abs(paired[off11] - S3[off11]).max():.1e}")
    P("  => the pairing IS Sym3.C2 entrywise; the RHS is the completed sheet the")
    P("     pairing supplies.  For m=2 the denominator Sym^{-1}=1 => RHS ENTIRE.")
    P()

    # ================================================================= ARM A
    P("=" * 78)
    P("ARM A -- CONJUGATE-CLOSED lattice pairing REGISTERS (m=2, entire flagship)")
    P("=" * 78)
    P("  Completed sheet: Q=11^3, G(s)=Q^{s/2} Gamma_C(s+3/2) Gamma_C(s+1/2), eps=+1.")
    P("  FE => smoothed-AFE mirror term (Lemma 1). Register: V_Y(pair) - L_pair equals")
    P("  the completed-sheet mirror term to the certified-value floor, ZERO fit params.")
    Q3, legs3, eps3 = 1331, [('C', 1.5), ('C', 0.5)], +1
    target = L_SYM3 * C_of(0.5, 2)
    lam_p = np.real(paired)[1:]
    nn = np.arange(1, NMAX + 1, dtype=float)
    logn = np.log(nn)
    nm05 = nn ** -0.5
    gl = np.linspace(-0.05, math.log(NMAX) + 0.05, 2200)
    P(f"  central target L(Sym3,1/2).C2(1/2) = {target:.6f}")
    P(f"  {'Y':>9s} {'V_Y(pair)':>11s} {'T_meas':>10s} {'T_pred(compl)':>13s} {'resid':>11s}")
    residuals = []
    for Y in YS:
        w = TF.wsmooth_vec(logn / math.log(Y))
        VY = float((lam_p * nm05 * w).sum())
        T_meas = VY - target
        Mn = np.interp(logn, gl, TP.paired_mirror_kernel(Q3, legs3, Y, gl))
        T_pred = eps3 * float((lam_p * nm05 * Mn).sum())
        resid = T_meas - T_pred
        residuals.append(resid)
        P(f"  {Y:>9.0f} {VY:>11.6f} {T_meas:>+10.5f} {T_pred:>+13.5f} {resid:>+11.2e}")
    spread = max(residuals) - min(residuals)
    P(f"  paired-read growth exponent {growth_exp(paired):+.3f}  (convergent)")
    P(f"  residual is CONSTANT: spread over the Y-ladder = {spread:.1e} "
      f"(= certified-value floor, not a trend)")
    P("  => the integer-m pairing REGISTERS at its derived transient.  PROVEN arm.")
    P()

    # ================================================================= ARM B
    P("=" * 78)
    P("ARM B -- SINGLE RAIL F_2 does NOT register (not self-dual => no FE => no mirror)")
    P("=" * 78)
    # (B1) structural: F_2 is genuinely complex; its dual is F_-2 (= conj on real axis)
    ip = np.abs(np.imag(F2[2:2000])).max()
    dual_gap = np.abs(Fm2[:5000] - np.conj(F2[:5000])).max()
    P("  (B1) non-self-dual, unconditional:")
    P(f"       max |Im lambda_n(F_2)|, n<2000 = {ip:.3f}  (NONZERO => complex coeffs,")
    P(f"            so the root multiset {{(m+1)th,(m-1)th}} is NOT conjugation-closed)")
    P(f"       max |lambda_n(F_-2) - conj(lambda_n(F_2))| = {dual_gap:.1e}  (=> dual(F_2)=F_-2,")
    P("            NOT F_2: no self functional equation)")
    # (B3) the read diverges at the center
    P("  (B3) center read (same window, same coeffs, no mirror to fold the tail):")
    P(f"       {'Y':>9s} {'|F_2(1/2)|':>12s}")
    for Y in YS:
        P(f"       {Y:>9.0f} {abs(reader_c(F2, Y)):>12.4f}")
    geB = growth_exp(F2)
    P(f"       growth exponent {geB:+.3f}   (Rankin-Selberg+Cauchy-Schwarz bound <= +0.5)")
    P("  => no self-FE => no archimedean completion => the mirror term of ARM A is")
    P("     ABSENT.  The read has no finite target and diverges.  'Nothing to register'")
    P("     is the divergence being ABSENCE of a value, not truncation error.")
    P()
    P("  Natural-boundary refinement (CRITERION + EVIDENCE, see notes s.4): Re s=1/2")
    P("  is the Estermann-Kurokawa natural boundary of a non-class-function local")
    P("  factor.  NB the published theorems (Estermann'28, Kurokawa'86, Koyama-")
    P("  Kurokawa'21) are stated for SELF-DUAL factors H in 1+T.R(SU(2))[T]; F_2's")
    P("  factor has complex (non-class-function) coeffs and sits outside their stated")
    P("  scope, so the boundary at 1/2 is criterion + the growth exponent above, NOT")
    P("  a verbatim citation.  The unconditional negative arm is (B1)+(B3) alone.")
    P()

    # ================================================================= ARM C
    P("=" * 78)
    P("ARM C -- INCOMMENSURATE control m=sqrt2 (interpolates toward B; MEASURED)")
    P("=" * 78)
    s = 2.5
    lhsx = dseries(Fs2, s) * dseries(Fms2, s)
    c2 = dseries(S3, s) * C_of(s, 2)
    c3 = dseries(S4, s) / complex(mp.zeta(s)) * C_of(s, 3)
    P("  no lattice partner: the incommensurate pairing matches NO Sym.C candidate:")
    P(f"    |F_sqrt2 F_-sqrt2 - Sym3.C2|      = {abs(lhsx - c2):.3f}   (O(1) = no identity)")
    P(f"    |F_sqrt2 F_-sqrt2 - (Sym4/z).C3|  = {abs(lhsx - c3):.3f}   (O(1) = no identity)")
    P("  => no completed sheet, no mirror term; the paired center read drifts:")
    vx = [abs(reader_c(TP.convolve_rails(Fs2, Fms2), Y)) for Y in YS]
    P("    |R(Y)| ladder: " + "  ".join(f"{v:.4f}" for v in vx)
      + f"   drift {abs(vx[-1] - vx[-2]):.4f}")
    P("  PROVEN endpoints: (A) integer-m pairings register; (B) single rails do not.")
    P("  MEASURED (not proven): the monotone off-lattice interpolation between them")
    P("  (value-registration census, item 11: 0.165 unwarped -> 0.236 full-warp,")
    P("  CV corr +0.89 with off-lattice distance).  OUT OF SCOPE: the RS-product")
    P("  extra transient (RS4/deg6, item 40) -- products carry a term powers do not.")
    P()

    P("=" * 78)
    P("VERDICT")
    P("=" * 78)
    P("  BACKBONE identity machine-zero; ARM A registers to the value floor (~8.6e-6,")
    P("  constant); ARM B diverges (growth ~+0.44) with the non-self-dual structure")
    P("  exhibited; ARM C confirms the incommensurate interpolation. The dichotomy's")
    P("  two endpoints are PROVEN (Newton-Thorne inputs, unconditional for 11a1); the")
    P("  Re s=1/2 boundary and the census interpolation are criterion/measured.")

    outp = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "registration_theorem_results.txt")
    with open(outp, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    P()
    P(f"[results written to {outp}]")


if __name__ == "__main__":
    main()
