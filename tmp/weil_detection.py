"""Exotic (Weil-type) Hodge classes, detected as occupancy excess.

The Hodge program's detection arm, aimed at the open-case SHAPE.  Weil's
mechanism -- the source of the famous open Hodge classes on abelian fourfolds --
is a RATIONAL class assembled from IRRATIONAL cycles: the pieces exist only over
an extension, but a rational combination survives.  This instrument measures
exactly that mechanism on quadruples where truth is known (product calibration):

  take four PAIRWISE NON-ISOGENOUS-over-Q quadratic twists E^(d1)..E^(d4) of one
  curve.  Over Q there are NO isogeny pairings, so the naive Q-ledger (pairing
  count) predicts quadruple DC occupancy 0.  But a_p(E^(d)) = chi_d(p) a_p(E),
  so the quadruple moment carries chi_{d1 d2 d3 d4}:

    prod d_i = square      ->  occupancy = the QBAR count (twists trivialize
                                over extensions; the classes assemble
                                Q-rationally: the WEIL MECHANISM) --
                                = 3 for a CM base (32a1), 2 (CATALAN) for a
                                  non-CM base (37a1);
    prod d_i = non-square  ->  occupancy 0 (character orthogonality).

  The EXCESS of measured occupancy over the Q-pairing count is the exotic
  occupancy -- Hodge classes invisible to the divisor-over-Q bookkeeping,
  detected by the carrier from point counts alone.  On products these exotic
  classes are known algebraic, so this calibrates the detector on known truth;
  the open Weil fourfolds (non-product) are the same reading's named target.

Register: measured; the naive-vs-Qbar interpretation is invariant theory; no
Hodge claim is made or needed.  Run: python3 weil_detection.py [X=20000]
"""
import sys, os, math
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

# base curves: CM (32a1, CM by Q(i)) and non-CM (37a1 short model) --
# twist by d:  y^2 = x^3 - d^2 x   /   y^2 = x^3 - 16 d^2 x + 16 d^3
def cm_twist(d):
    return (0, 0, 0, -d * d, 0)


def noncm_twist(d):
    return (0, 0, 0, -16 * d * d, 16 * d ** 3)


CASES = [
    ("W1", "CM",    [1, 2, 3, 6],  3, "prod=36 sq: Weil assembly (CM)"),
    ("W2", "CM",    [1, 2, 3, 5],  0, "prod=30 nonsq: orthogonality"),
    ("W3", "CM",    [1, 2, 5, 10], 3, "prod=100 sq: Weil assembly (CM)"),
    ("W4", "nonCM", [1, 2, 3, 6],  2, "prod=36 sq: Weil assembly, CATALAN"),
    ("W5", "nonCM", [1, 2, 3, 5],  0, "prod=30 nonsq: orthogonality"),
]


def bank(ainv, badp, X):
    out = {}
    for p in SH.sieve_primes(X):
        if p in badp:
            continue
        out[p] = SH.ap_general(p, *ainv) / math.sqrt(p)
    return out


def main():
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    lines = []

    def P(s=""):
        print(s, flush=True)
        lines.append(s)

    P("#" * 78)
    P("# WEIL DETECTION -- exotic Hodge classes as occupancy EXCESS")
    P(f"# quadruples of pairwise non-isogenous twists; good p <= {X}")
    P("#" * 78)
    P()
    banks = {}
    for kind, tw in [("CM", cm_twist), ("nonCM", noncm_twist)]:
        for d in {d for _, k, ds, _, _ in CASES if k == kind for d in ds}:
            bad = {2} | {p for p in range(2, 40) if
                         all(m % p == 0 for m in [d]) and d % p == 0}
            bad = {p for p in SH.sieve_primes(40) if (2 * d) % p == 0}
            banks[(kind, d)] = bank(tw(d), bad, X)
    P(f"  banks built: {len(banks)} twisted curves, from point counts only")
    P()
    P(f"  {'case':>4s} {'base':>6s} {'twists':>14s} {'Q-pairing':>9s} "
      f"{'measured':>9s} {'QBAR pred':>9s} {'excess':>7s} {'m3':>7s} {'OK':>3s}")
    all_ok = True
    for cid, kind, ds, pred, desc in CASES:
        common = None
        bs = []
        for d in ds:
            b = banks[(kind, d)]
            common = set(b) if common is None else common & set(b)
        ps = sorted(common)
        arrs = [np.array([banks[(kind, d)][p] for p in ps]) for d in ds]
        m4 = float((arrs[0] * arrs[1] * arrs[2] * arrs[3]).mean())
        m3 = float((arrs[0] * arrs[1] * arrs[2]).mean())
        ok = abs(m4 - pred) < 0.15 and abs(m3) < 0.1
        all_ok = all_ok and ok
        excess = m4 - 0.0            # Q-pairing count is 0 for distinct twists
        P(f"  {cid:>4s} {kind:>6s} {str(ds):>14s} {0:9d} {m4:9.3f} {pred:9d} "
          f"{excess:7.3f} {m3:7.3f} {'YES' if ok else 'NO':>3s}")
    P()
    P("VERDICT:")
    if all_ok:
        P("  The Weil mechanism is measured: quadruples with NO Q-isogeny pairing")
        P("  (naive ledger count 0) carry full QBAR occupancy whenever the twist")
        P("  product is a square -- 3 on the CM base, CATALAN 2 on the non-CM")
        P("  base -- and exactly 0 when it is not (orthogonality).  The excess is")
        P("  the exotic occupancy: rational classes assembled from irrational")
        P("  cycles, detected from point counts with no cycle input.  On products")
        P("  this calibrates against known truth; the identical reading aimed at")
        P("  non-product Weil fourfolds is the program's open-case detection arm,")
        P("  feeding Retention/Recognition of the HodgeDial spine.")
    else:
        P("  A configuration missed -- instrument or invariant-count defect;")
        P("  publish per the falsifiability register and investigate.")

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "weil_detection_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P()
    P("[results written to weil_detection_results.txt]")


if __name__ == "__main__":
    main()
