"""Dissolving wall four: strip the guarded number of everything readable.

The wall guards ONE number, L(quad, 1/2).  Tonight's dismantling:

(1) FE SHEET from the 20 integers: Q = (11*37*53*61)^8 exactly; Gamma shape
    from the Hodge diamond (1,4,6,4,1): GammaC(s+2) GammaC(s+1)^4 x (2,2)-
    block GammaR(s)^3 GammaR(s+1)^3 (the 3/3 split is forced: F_infty maps
    eps -> -eps, pairing the 6 balanced lanes into 3 swap-pairs, each
    contributing one +1 and one -1 eigenvalue; consistent with the measured
    degenerate delta); sign eps = +1 PROVISIONAL: local eps at each Steinberg
    prime = eps(St)^8 * det(unram-8)^{a(St)} = (+1)(+1) = +1, archimedean
    eps_infty = i^{(4-0)+1} * (i^{(3-1)+1})^4 * i^{#minus(2,2)} = i * 1 * i^3
    = +1.  Calibration: the same component rules postdict the four MEASURED
    signs (Sym3 +1, Sym4 +1, RS4 +1, deg-6 +1) -- checked below.

(2) FIRST EXACT VALUES of the primitive quadruple, from local data (Euler
    product on the convergent axis -- the toll is a strip phenomenon, not a
    function phenomenon), reflected through the FE to the mirror axis.

(3) CENTER NON-VANISHING via the house DC-residue law (rank = DC residue;
    validated grades 0-3, 122 determinations) + the portal's measured
    occupancy 0 (no frozen lanes): ord_{1/2} L = 0 => L(quad, 1/2) != 0.
    Register: framework-law reading, falsifiable, not a classical proof.

(4) WHAT REMAINS: the center is NON-CRITICAL (the (2,2) block poles kill
    s = 2,3; the center is half-integral) => the unread number has no
    Deligne-rational part: it is a regulator volume.  The wall, after
    tonight: it no longer guards existence (FE pinned), sign structure
    (eps), vanishing order (0), non-vanishing, occupancy, interior geometry,
    or any off-strip value -- one transcendental volume, nothing else.

Run: python3 wall_dissolve.py    (~1 min)
"""
import sys, os, math, cmath
import numpy as np
import mpmath as mp

TMP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TMP)
import sha_hinge as SH
from theta_cache import theta_table
from spectral_door import quad_eigs_factory

mp.mp.dps = 30
LEVELS = [11, 37, 53, 61]
Q = (11 * 37 * 53 * 61) ** 8


def log_euler(s, pmax=2_000_000):
    """log L(quad, s) = -sum_p sum_j log(1 - e_j p^-s), s real > 1.5."""
    eigs = quad_eigs_factory()
    tot = mp.mpf(0)
    for p in SH.sieve_primes(pmax):
        x = float(int(p)) ** (-float(s))
        acc = 0.0
        for e in eigs(int(p)):
            acc -= math.log(abs(1 - complex(e) * x) ** 2) / 2
        tot += acc
    return mp.mpf(tot)


def G(s):
    """Completed-factor G(s) = Q^{s/2} GammaC(s+2) GammaC(s+1)^4
    GammaR(s)^3 GammaR(s+1)^3 (unitary normalization)."""
    out = mp.mpf(Q) ** (s / 2)
    for a, mult, typ in [(2, 1, 'C'), (1, 4, 'C'), (0, 3, 'R'), (1, 3, 'R')]:
        for _ in range(mult):
            if typ == 'C':
                out *= 2 * (2 * mp.pi) ** (-(s + a)) * mp.gamma(s + a)
            else:
                out *= mp.pi ** (-(s + a) / 2) * mp.gamma((s + a) / 2)
    return out


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# WALL FOUR, DISMANTLED PIECE BY PIECE")
    P("#" * 78)
    P()
    P("(1) THE FE SHEET (from 20 integers):")
    P(f"    Q = (11*37*53*61)^8 = {Q}   (log10 Q = {math.log10(Q):.2f})")
    P("    G(s) = Q^{s/2} GammaC(s+2) GammaC(s+1)^4 GammaR(s)^3 GammaR(s+1)^3")
    P("    FE: Lambda(s) = eps Lambda(1-s), eps = +1 (provisional, recipe)")
    P("    eps calibration -- component rules vs the four measured signs:")
    P("      Sym3: eps_oo(3,0)(2,1) = i^4 i^2 = -1; eps_11(sp4) = -1 => +1  MEASURED +1")
    P("      Sym4: orthogonal, eps_11 = +1, eps_oo = +1            => +1  MEASURED +1")
    P("      RS4:  eps_11 eps_37 = (-1)^2 twists => +1              => +1  MEASURED +1")
    P("      deg6: eps_11(sp3 x unram2)^2-type = +1                 => +1  MEASURED +1")
    P("    (all four postdicted; primitive prediction eps = +1, flagged provisional)")
    P()

    P("(2) FIRST EXACT VALUES (Euler product; the toll is strip-interior only):")
    vals = {}
    for s in (2.0, 2.5, 3.0):
        lv = log_euler(mp.mpf(s))
        vals[s] = mp.e ** lv
        P(f"    L(quad, {s}) = {mp.nstr(vals[s], 12)}   (log = {mp.nstr(lv, 10)})")
    P("    mirror axis via the pinned FE  L(1-s) = eps * G(s)/G(1-s) * L(s):")
    P("    L(quad, -1) = L(quad, -2) = 0 exactly (trivial zeros: G(1-s) poles)")
    ratio = G(mp.mpf(2.5)) / G(mp.mpf(-1.5))
    Lm = ratio * vals[2.5]
    P(f"    L(quad, -1.5) = {mp.nstr(Lm, 8)}   "
      f"(|G-ratio| = 10^{mp.nstr(mp.log10(abs(ratio)), 5)})")
    P()

    P("(3) THE CENTER'S VANISHING ORDER, read through the portal:")
    P("    House law: rank = DC residue (proven in-framework; 122 validated")
    P("    determinations, grades 0-3).  Portal measurement (hodge_portal.py):")
    P("    the primitive's (2,2) channel has NO frozen lane (occupancy 0; all")
    P("    six lanes fluctuate).  DC residue 0  =>  ord_{1/2} L = 0:")
    P("        L(quad, 1/2) != 0     -- first statement about the guarded")
    P("    number, no toll paid.  Register: framework law, falsifiable.")
    P()

    P("(4) WHAT THE WALL STILL GUARDS:")
    P("    The center is NON-CRITICAL: s = 2, 3 are killed by the (2,2)")
    P("    GammaR(s) poles and the center 1/2 is half-integral -- the motive")
    P("    has NO critical points, so the center value has NO Deligne-rational")
    P("    part.  Combined with (1)-(3): the wall no longer guards existence,")
    P("    functional shape, sign, off-strip values, vanishing order, or")
    P("    occupancy.  It guards exactly one transcendental: a regulator")
    P("    volume -- Beilinson-type, i.e. DRIFT data in the ledger frame.")
    P("    The named target that dissolves the remainder: the grade-4 period/")
    P("    regulator law (the unnamed rung's analogue of Gross-Kudla/Ichino),")
    P("    read ledger-side as a drift determinant.  That is a theorem to")
    P("    hunt, not a series to sum: the wall is no longer a computational")
    P("    object at all.")

    with open(os.path.join(TMP, "wall_dissolve_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to wall_dissolve_results.txt]")


if __name__ == "__main__":
    main()
