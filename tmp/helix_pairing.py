"""Putting the half-lane object on the helix: the two-rail pairing readout.

The 1D finding (harmonic_lattice.py): F_2, the half-lane warp of 11a1 (lanes
{e^{3i th}, e^{i th}}), has a natural boundary at Re s = 1/2 -- its scalar
window reading diverges (|F_2|^2 marched 40 -> 384, growth exp +0.43).

The 3D question (ground rule 4): is that boundary a carrier fact or a chart
artifact?  The carrier is a DOUBLE helix: a complex bank rides one rail with
its conjugate bank on the other (the F21 non-self-dual GL(3) precedent: the
scalar readout provably cannot carry it; the multi-rail helix does).  F_2
alone is non-admissible -- its lane set is not conjugate-closed; THAT is the
3D face of the 1D boundary.  The height-matched Hermitian pairing of the two
rails is the Dirichlet convolution

    (F_2 (*) F_-2)[n] = sum_{d|n} lam_2[d] * lam_-2[n/d]

-- phasor at height log d on rail A paired with phasor at height log(n/d) on
rail B, a geometric operation performed BEFORE any chart reads anything.  The
paired bank is conjugate-closed (complete lanes = Sym3 * C2) and its midline
read should land on the certified L(Sym3, 1/2) * C2(1/2) = 1.368286.

Tests:
  P1  bank identity: paired bank == Sym3 bank entrywise off powers of 11
      (at 11-powers the C2 correction), and value-level at s = 2.5
  P2  THE DEMONSTRATION: same phasor data, three reads at 1/2 --
        single rail F_2:        diverges  (the boundary, chart-side)
        rail pair F_2 (*) F_-2: converges to 1.368286  (the helix read)
        mis-pair  F_2 (*) F_-3: diverges  (half-lane residue survives --
                                 the rail-MATCHING law: exact conjugates only)
  P3  cell profiles ("no gaps in all the cells"): growth exponent of the
      paired bank ~ 0 vs +0.4 for single rail and mis-pair
  P4  falsifier symmetry: mis-pair the other way (F_3 (*) F_-2) -- same fail

Honest scope: P1 is an identity (must hold); the measured content is P2/P3/P4
-- the boundary lives in the single-rail scalar chart, not on the carrier.
Value-wall consequence stated in the summary: the quadruple is itself a
two-rail pairing (G * G-bar, G = plus-half of f1 tensor the full triple), so
its carrier representation exists; the pairing read still carries the
quadruple's own transient scale -- the VALUE wall stands.  What the helix
opens is the SPECTRAL door: zeros are local focal events (no sqrt-Q toll,
focal_closure precedent) -- the follow-on experiment.

Run: python3 helix_pairing.py    (~1-2 min)
"""
import sys, os, math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harmonic_lattice import (fast_bank, warp_eigs, sym_eigs, dseries,
                              reader_c, ALPHA)

NMAX = 300000
H = math.pi / 3
L_SYM3 = 1.1402380          # our certified center, PARI-validated to 7e-6


def convolve_rails(a, b):
    """Height-matched rail pairing: c[n] = sum_{d|n} a[d] b[n/d]."""
    N = len(a) - 1
    c = np.zeros(N + 1, dtype=complex)
    for d in range(1, N + 1):
        ad = a[d]
        if ad != 0:
            c[d::d] += ad * b[1:N // d + 1]
    return c


def growth_exp(lam):
    n = np.arange(1, len(lam), dtype=float)
    cum = np.abs(np.cumsum(lam[1:] * n ** -0.5))
    i0 = len(cum) // 8
    return (math.log(cum[-1] + 1e-30) - math.log(cum[i0] + 1e-30)) / \
        (math.log(len(cum)) - math.log(i0 + 1))


def main():
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# HELIX PAIRING -- the half-lane object on the double helix's two rails")
    P("#" * 78)
    P()
    F2 = fast_bank(warp_eigs(2), NMAX)
    Fm2 = fast_bank(warp_eigs(-2), NMAX)
    Fm3 = fast_bank(warp_eigs(-3), NMAX)
    F3 = fast_bank(warp_eigs(3), NMAX)
    S3 = fast_bank(sym_eigs(3), NMAX)
    paired = convolve_rails(F2, Fm2)
    mis_a = convolve_rails(F2, Fm3)
    mis_b = convolve_rails(F3, Fm2)
    P(f"banks + three rail pairings built to {NMAX}")
    P()

    P("P1 -- pairing identity (must hold; conventions check):")
    off11 = np.array([n for n in range(2, 5000) if n % 11 != 0])
    d = np.abs(paired[off11] - S3[off11]).max()
    P(f"  max |paired - Sym3| off 11-powers (n < 5000): {d:.2e}")
    s = 2.5
    q = 11.0 ** (-s)
    C2s = (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2
    P(f"  value at s=2.5: paired {dseries(paired, s).real:.9f}  "
      f"Sym3*C2 {(dseries(S3, s) * C2s).real:.9f}")
    P()

    P("P2 -- three reads of the SAME phasor data at the midline (1/2):")
    q = 11.0 ** -0.5
    C2h = (1 - ALPHA ** 3 * q) / (1 - ALPHA * q) ** 2
    target = L_SYM3 * C2h
    P(f"  target (certified): L(Sym3,1/2)*C2(1/2) = {target:.6f}")
    Ys = (4000, 16000, 64000, 250000)
    for lab, bank, truth in [("single rail F_2", F2, None),
                             ("rail pair F_2(*)F_-2", paired, target),
                             ("mis-pair F_2(*)F_-3", mis_a, None),
                             ("mis-pair F_3(*)F_-2", mis_b, None)]:
        vals = [reader_c(bank, Y) for Y in Ys]
        row = "  ".join(f"{abs(v):9.4f}" for v in vals)
        drift = abs(vals[-1] - vals[-2])
        t = ""
        if truth is not None:
            t = f"   err vs target {abs(vals[-1] - truth):.2e}"
        P(f"  {lab:22s} |R(Y)|: {row}   drift {drift:.4f}{t}")
    P()

    P("P3 -- cell health (growth exponent of the sqrt-weighted primitive):")
    for lab, bank in [("single rail F_2", F2), ("rail pair", paired),
                      ("mis-pair a", mis_a), ("mis-pair b", mis_b)]:
        P(f"  {lab:16s} growth exp {growth_exp(bank):+.3f}")
    P()

    P("READING:")
    P("  If the rail pair converges on the certified target while the single")
    P("  rail and BOTH mis-pairs diverge, the natural boundary is measured to")
    P("  be a single-rail scalar-chart artifact: the carrier pairs conjugate")
    P("  rails height-by-height BEFORE any readout, and only exact conjugate")
    P("  pairing completes the lanes (the rail-matching law).  The value-")
    P("  registration law then lives at pairing level, where it is exact AND")
    P("  readable at the center.  Consequence for grade 4: the quadruple has")
    P("  an explicit two-rail carrier construction (G (*) G-bar); its VALUE")
    P("  keeps its own transient scale (the wall stands), but zeros are local")
    P("  focal events with no sqrt-Q toll -- the spectral door is the next")
    P("  experiment (focal locator on the paired quadruple bank).")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "helix_pairing_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to helix_pairing_results.txt]")


if __name__ == "__main__":
    main()
