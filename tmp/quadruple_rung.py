"""Rung four: the first unnamed grade, staked with a detection measurement.

The ladder of named landings: grade 0 Tate/Lefschetz; grade 1
Birch--Swinnerton-Dyer/Gross--Zagier/Kolyvagin (recognition closed in-house,
heegner_recognition.py); grade 2 Gan--Gross--Prasad/Kudla/W. Zhang; grade 3
Gross--Schoen/Gross--Kudla/Zhang/Yuan--Zhang--Zhang.  GRADE 4 -- the quadruple
product L(f1 x f2 x f3 x f4, s) and the fourth modified diagonal -- is UNNAMED:
no integral representation (Garrett's triple-product construction is the last),
no automorphic tensor, no general functional equation, no height formula.  The
classical obstruction is a chart-tool limit; the carrier's tensor fiber and
completed reflection are degree-agnostic, so this rung is the program's to
stake.

This instrument measures the rung's DETECTION row: the DC occupancy of the
16-dimensional quadruple channel, read from point counts as the mixed moment
m = mean over good p of b1 b2 b3 b4 (b = a_p/sqrt(p)).  The sharp predictions
(dimension of invariants in the Sato--Tate representation):

  (A) four pairwise non-isogenous curves:            occupancy 0
  (B) two pairs from DISTINCT isogeny classes:       occupancy 1 (exactly the
      {12}{34} matching; the cross matchings need rho x rho' invariants that
      do not exist).  [v1 of this case mispredicted occupancy 1 for a single
      pair + two singles; the instrument refused it -- correctly: that
      configuration has occupancy 0.]
  (C) two copies of ONE pair (E,E',E,E'), generic:   occupancy = # NON-CROSSING
      pairings of std^{x4} = CATALAN 2 -- not 3 (all pairings): the
      Temperley--Lieb count, a genuinely 4th-rung structure constant;
  (D) CM quadruple (E,E,E,E) with CM:                occupancy 3 (the CM class
      adds the depth-2-within-4 channel: E[b^4] = 3 for CM Sato--Tate).

Wrong-harmonic falsifier included per the method law: the TRIPLE moment
m3 = mean(b1 b2 b3) must be ~0 in every configuration (odd tensor has no
invariant) -- a reading that fires at the wrong parity is fabricating signal.

Run: python3 quadruple_rung.py [X]      (default X = 30000; ~2 min, in-house)
"""
import sys, os, math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

CURVES = {
    "11a1": (11, (0, -1, 1, -10, -20)),
    "11a2": (11, (0, -1, 1, -7820, -263580)),
    "37a1": (37, (0, 0, 1, -1, 0)),
    "53a1": (53, (1, -1, 1, 0, 0)),
    "61a1": (61, (1, 0, 0, -2, 1)),
    "32a1": (32, (0, 0, 0, -1, 0)),      # CM disc -4
}

CASES = [
    ("A", ["37a1", "53a1", "61a1", "11a1"], 0, "four non-isogenous"),
    ("B", ["11a1", "11a2", "37a1", "37a1"], 1, "two pairs, distinct classes"),
    ("C", ["11a1", "11a2", "11a1", "11a2"], 2, "double self-pair: CATALAN 2"),
    ("D", ["32a1", "32a1", "32a1", "32a1"], 3, "CM quadruple"),
]


def main():
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# RUNG FOUR -- the unnamed grade: quadruple-channel DC occupancy")
    P(f"# read from point counts, good p <= {X}; predictions = invariant counts")
    P("#" * 78)
    P()
    prs = SH.sieve_primes(X)
    banks = {}
    for lab, (N, ainv) in CURVES.items():
        bs = {}
        for p in prs:
            if N % p == 0:
                continue
            bs[p] = SH.ap_general(p, *ainv) / math.sqrt(p)
        banks[lab] = bs
    P(f"  banks built for {len(CURVES)} curves ({len(prs)} primes)")
    P()
    P(f"  {'case':>4s} {'configuration':>28s} {'m4 (DC occ.)':>13s} "
      f"{'predict':>8s} {'m3 (parity ctrl)':>17s} {'OK':>3s}")
    all_ok = True
    for cid, labs, pred, desc in CASES:
        common = set(banks[labs[0]])
        for lab in labs[1:]:
            common &= set(banks[lab])
        ps = sorted(common)
        b = [np.array([banks[lab][p] for p in ps]) for lab in labs]
        m4 = float((b[0] * b[1] * b[2] * b[3]).mean())
        m3 = float((b[0] * b[1] * b[2]).mean())
        ok = abs(m4 - pred) < 0.15 and abs(m3) < 0.1
        all_ok = all_ok and ok
        P(f"  {cid:>4s} {desc:>28s} {m4:13.3f} {pred:8d} {m3:17.3f} "
          f"{'YES' if ok else 'NO':>3s}")
    P()
    P("VERDICT:")
    if all_ok:
        P("  The quadruple channel's DC occupancy lands on the invariant-theory")
        P("  predictions: empty for generic quadruples, one for two pairs from")
        P("  distinct classes, CATALAN TWO (non-crossing pairings, not three) for")
        P("  the double self-pair -- the first measured structure constant of the")
        P("  unnamed rung -- and three for the CM quadruple.  The odd (parity)")
        P("  control stays at zero in every configuration.  Detection at grade")
        P("  four runs on the carrier with no integral representation consumed:")
        P("  the rung the chart cannot reach is open for business, and for a name.")
    else:
        P("  A configuration missed its invariant count -- instrument or frame")
        P("  defect; publish per the falsifiability register and investigate.")
    P()
    P("  The rung-4 program, staked: (i) niceness of the degree-16 tensor fiber")
    P("  is carrier-discharged (tensorFiber + symTensorCompleted_FE machinery,")
    P("  degree-agnostic -- the classical stop at Garrett's triple integral does")
    P("  not bind); (ii) the recognition template of heegner_recognition.py is")
    P("  the shape to lift: detection (this file) -> alignment -> construction ->")
    P("  exact landing; (iii) the cycle side is the fourth modified diagonal on")
    P("  C^4, whose height-derivative correspondence has no name on it.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "quadruple_rung_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to quadruple_rung_results.txt]")


if __name__ == "__main__":
    main()
