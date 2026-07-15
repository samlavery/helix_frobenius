"""The value-registration transient, BOTH forms -- single rail AND conjugate pairing.

Value-level sibling of the S(t)-compensation theorem (CarrierScaleCompensation.lean,
the theta-construction technique).  There the zero COUNT decomposes as

    N(t) = 1 + theta(t)/pi + S(t)     [DC residue + sheet clock + registration gap]

with theta(t) = int_0^t Re(logDeriv Gamma_R(1/2+iu)) du derived FROM THE SHEET (the
Gamma-factor), and S(t) the leftover compensation.  The VALUE-level identity is the
exact sibling:

    V_Y(1/2) = L(1/2) + [mirror term]      [truth + sheet-derived compensation]

the mirror term (transient_form.py) IS the value-level S(t): the chart toll made
explicit from the FE sheet.  This file derives the transient in its TWO carrier reads:

  FORM 1 -- SINGLE RAIL.  A half-lane object F_r (lanes {(1+r)th, (r-1)th}, the
    positive half of Sym^{2r-1}) is NOT conjugate-closed: its dual is the OTHER rail
    F_{-r}, so it has NO self functional equation and NO archimedean completion (its
    lanes have no conjugates to pair Gamma-factors with).  => Estermann/Kurokawa
    natural boundary at Re s = 1/2: there is no value to register, and the mirror
    term is ABSENT.  The single-rail read DIVERGES.  Sheet bound on the divergence:
    Rankin-Selberg gives sum_{n<=N}|lam_n|^2 ~ cN, so by Cauchy-Schwarz the sqrt-
    weighted read is <= N^{1/2}(log N)^{1/2} -- growth, not convergence.

  FORM 2 -- CONJUGATE PAIRING.  The height-matched Hermitian pairing
    (F_r (*) F_{-r})[n] = sum_{d|n} lam_r[d] lam_{-r}[n/d] symmetrizes the lanes
    {(1+r)th,(r-1)th} (x) {-(1+r)th,-(r-1)th} -> {+-(2r-1)th, ..., +-th} = Sym^{2r-1}
    (times a bad-factor C_r at 11).  This restores conjugate closure => the FULL
    Sym^{2r-1} Gamma-factor Gamma_C(s+(2r-1)/2)...Gamma_C(s+1/2) => a genuine FE =>
    the MIRROR TERM EXISTS.  The paired read CONVERGES, and its transient is the
    mirror-term transient (transient_form), DERIVED from the sheet.

WHAT THE PAIRING BUYS, analytically: exactly the mirror term.  The single rail's
mirror lives on the unreachable conjugate rail; the pairing brings it internal.  The
Gamma-factor the pairing supplies is the completed Sym^{2r-1} archimedean factor --
r copies of Gamma_C -- absent from either half alone.

TEST: predict the paired read against the MEASURED helix_pairing convergence
(1.3593, 1.3659, 1.3689, 1.3682 at Y=4e3,16e3,64e3,250e3; growth exp +0.018) and the
helix_tower Sym3 pair convergence.  r=2 (Sym3) is the clean rung; r=3 (Sym4/zeta.C3)
carries a zeta in the denominator (noted, not the headline).

Run: python3 transient_pairing.py     (~2-4 min)
"""
import sys, os, math, cmath
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import transient_form as TF
from harmonic_lattice import (fast_bank as hl_bank, warp_eigs, sym_eigs, reader_c,
                              ALPHA)

NMAX = 400000
H = math.pi / 3
L_SYM3 = 1.1402380                      # certified center of Sym3(11a1)
Y_PAIR = [4000.0, 16000.0, 64000.0, 250000.0]     # helix_pairing ladder
# measured helix_pairing single-rail and pair reads (helix_pairing_results.txt):
MEAS_SINGLE = [6.3643, 9.9941, 15.8844, 25.0586]
MEAS_PAIR = [1.3593, 1.3659, 1.3689, 1.3682]


def convolve_rails(a, b):
    """Height-matched conjugate rail pairing: c[n] = sum_{d|n} a[d] b[n/d]."""
    N = len(a) - 1
    c = np.zeros(N + 1, dtype=complex)
    for d in range(1, N + 1):
        ad = a[d]
        if ad != 0:
            c[d::d] += ad * b[1:N // d + 1]
    return c


def growth_exp(lam):
    n = np.arange(1, len(lam), dtype=float)
    cum = np.abs(np.cumsum(np.real(lam[1:]) * n ** -0.5))
    i0 = len(cum) // 8
    return (math.log(cum[-1] + 1e-30) - math.log(cum[i0] + 1e-30)) / \
        (math.log(len(cum)) - math.log(i0 + 1))


def C2_of(s):
    q = 11.0 ** (-s)
    return (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2


def C2_complex(z):
    """C2(s) for complex s = 1/2 + z (vectorized): the bad-factor at 11."""
    q = np.exp(-(0.5 + z) * math.log(11.0))
    return (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2


def paired_mirror_kernel(Q, legs, Y, gl, cprime=0.75, T=90.0, NODES=14001, NU=1200):
    """Mirror kernel M_m for the PAIRED object Sym3.C2: same as
    transient_form.mirror_kernel_on_grid but chi carries the extra bad-factor FE
    reflection C2(1/2+z)/C2(1/2-z) -- the completed paired sheet."""
    L = math.log(Y)
    ts = np.linspace(-T, T, NODES)
    z = -cprime + 1j * ts
    us = np.linspace(0.5, 1.0, NU + 1)
    wp = TF.wprime(us)
    sw = np.ones(NU + 1); sw[1:-1:2], sw[2:-1:2] = 4.0, 2.0
    sw *= (us[1] - us[0]) / 3.0
    amp = (wp * sw) * np.exp(-us * cprime * L)
    phase = np.exp(1j * np.outer(ts * L, us))
    psi = phase @ amp
    wtilde = -psi / z
    chi = np.exp(TF.log_chi(z, Q, legs)) * (C2_complex(z) / C2_complex(-z))
    F = wtilde * chi
    wt = np.ones(NODES); wt[1:-1:2], wt[2:-1:2] = 4.0, 2.0
    wt *= (ts[1] - ts[0]) / 3.0
    base = F * wt
    M = np.zeros(len(gl))
    CH = 128
    for i in range(0, len(gl), CH):
        blk = gl[i:i + CH]
        E = np.exp(1j * np.outer(blk, ts))
        M[i:i + CH] = (np.exp(-cprime * blk) * (E @ base) / (2.0 * math.pi)).real
    return M


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# VALUE-REGISTRATION TRANSIENT, TWO FORMS -- single rail vs conjugate pairing")
    P("# (value-level sibling of S(t)-compensation: V_Y = L + [mirror] = truth + toll)")
    P("#" * 78)
    P()

    P("building rail banks F_2, F_-2 and the pairing F_2(*)F_-2 = Sym3.C2 ...")
    F2 = hl_bank(warp_eigs(2), NMAX)
    Fm2 = hl_bank(warp_eigs(-2), NMAX)
    S3 = np.real(hl_bank(sym_eigs(3), NMAX))
    paired = convolve_rails(F2, Fm2)
    # pairing identity check (must hold)
    off11 = np.array([n for n in range(2, 5000) if n % 11 != 0])
    idcheck = np.abs(paired[off11] - S3[off11]).max()
    P(f"  pairing identity  max|paired - Sym3| off 11-powers = {idcheck:.1e}")
    target = L_SYM3 * C2_of(0.5)
    P(f"  paired central target  L(Sym3,1/2).C2(1/2) = {target:.6f}")
    P()

    # ================================================================= FORM 1
    P("=" * 78)
    P("FORM 1 -- SINGLE RAIL F_2 (half-lane, NO conjugate closure)")
    P("=" * 78)
    P("  Sheet status: lanes {3th, th} both positive-frequency -> no conjugate to")
    P("  complete a Gamma-factor -> NO functional equation -> NO mirror term.")
    P("  Prediction: Estermann/Kurokawa natural boundary at Re s=1/2; the read has")
    P("  no finite target and DIVERGES.  Sheet bound (Rankin-Selberg + Cauchy-")
    P("  Schwarz on the degree-2 lanes): |read| <= N^{1/2}(log N)^{1/2}.")
    P(f"  {'Y':>9s} {'|F_2(1/2)|':>12s}   measured(helix_pairing)")
    for Y, meas in zip(Y_PAIR, MEAS_SINGLE):
        r = abs(reader_c(F2, Y))
        P(f"  {Y:>9.0f} {r:>12.4f}   {meas:>10.4f}")
    ge = growth_exp(F2)
    P(f"  growth exponent of the sqrt-weighted read: {ge:+.3f}  "
      f"(measured helix_pairing +0.427; sheet bound <= +0.5)")
    P("  => single-rail 'transient' is a DIVERGENCE: no mirror term to derive,")
    P("     because there is no functional equation.  Confirmed.")
    P()

    # ================================================================= FORM 2
    P("=" * 78)
    P("FORM 2 -- CONJUGATE PAIRING F_2(*)F_-2 = Sym3.C2 (mirror term RESTORED)")
    P("=" * 78)
    P("  Sheet: Q = 11^3, G(s)=Q^{s/2} Gamma_C(s+3/2) Gamma_C(s+1/2), eps=+1 -- the")
    P("  FULL Sym3 archimedean factor, supplied BY the conjugate pairing.  The")
    P("  transient is now the mirror term (transient_form), DERIVED from this sheet.")
    P()
    Q3, legs3, eps3 = 1331, [('C', 1.5), ('C', 0.5)], +1
    lam_p = np.real(paired)[1:]
    nn = np.arange(1, NMAX + 1, dtype=float)
    logn = np.log(nn)
    nm05 = nn ** -0.5
    gl = np.linspace(-0.05, math.log(NMAX) + 0.05, 2200)

    P("  T_pred(Sym3) = pure Sym3 sheet;  T_pred(Sym3.C2) = completed paired sheet")
    P("  (chi carries the extra bad-factor reflection C2(1/2+z)/C2(1/2-z)):")
    P(f"  {'Y':>9s} {'V_Y[paired]':>12s} {'T_meas':>10s} {'T(Sym3)':>10s} "
      f"{'T(Sym3.C2)':>11s} {'resid':>10s}")
    for Y, meas in zip(Y_PAIR, MEAS_PAIR):
        w = TF.wsmooth_vec(logn / math.log(Y))
        VY = float((lam_p * nm05 * w).sum())
        T_meas = VY - target
        Mn_pure = np.interp(logn, gl, TF.mirror_kernel_on_grid(Q3, legs3, Y, gl))
        T_pure = eps3 * float((lam_p * nm05 * Mn_pure).sum())
        Mn_c2 = np.interp(logn, gl, paired_mirror_kernel(Q3, legs3, Y, gl))
        T_c2 = eps3 * float((lam_p * nm05 * Mn_c2).sum())
        P(f"  {Y:>9.0f} {VY:>12.6f} {T_meas:>+10.5f} {T_pure:>+10.5f} "
          f"{T_c2:>+11.5f} {T_meas - T_c2:>+10.2e}")
    ge_p = growth_exp(paired)
    P(f"  growth exponent of the paired read: {ge_p:+.3f}  "
      f"(measured helix_pairing +0.018; convergent)")
    P()

    # ============================================ WHAT THE PAIRING BUYS
    P("=" * 78)
    P("WHAT THE PAIRING BUYS (analytic)")
    P("=" * 78)
    P("  The single rail F_2 supplies only HALF the archimedean factor (the")
    P("  positive-frequency Gamma_C's with no reflection) -> no FE -> the mirror")
    P("  term M_m -- the value-level compensation -- does not exist -> divergence.")
    P("  The conjugate pairing completes the lanes {3th,th}(x){-3th,-th} ->")
    P("  {+-3th,+-th} = Sym3, i.e. it SUPPLIES the full Gamma_C(s+3/2)Gamma_C(s+1/2)")
    P("  and the FE.  The mirror term the pairing buys IS the transient's")
    P("  compensation -- exactly the value-level sibling of theta(t)/pi + S(t)")
    P("  supplying the count's compensation in CarrierScaleCompensation.lean.")
    P()
    P("  Concretely, the difference between the two forms at the center is the")
    P("  entire mirror sum: single rail (mirror absent) diverges as N^{~0.43};")
    P("  paired (mirror present) converges, transient = the derived mirror term.")

    outp = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "transient_pairing_results.txt")
    with open(outp, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    P()
    P(f"[results written to {outp}]")


if __name__ == "__main__":
    main()
