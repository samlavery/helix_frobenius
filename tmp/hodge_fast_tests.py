"""Hodge-program fast tests: what fails and what works, cheaply.

Fast, high-information tests for the companion paper's program
(automorph/hodge_companion.tex), run before investing in the slow instruments.

TEST A -- THE LEDGER-FAILURE SEARCH, v1 (isogeny classes).
  The program's crux (terminus ingredient 1 of the companion paper) is that the
  carrier's retained ledger separates cycle data that the 1D readout cannot.  The
  sharpest cheap adversarial instance is an ISOGENY CLASS of elliptic curves: by
  Faltings, isogenous curves have the IDENTICAL L-function -- the 1D value channel
  provably cannot separate them -- yet their cycle-level data (torsion T, real
  period Omega, Tamagawa numbers c_p) differ curve by curve, redistributing so the
  BSD combination stays fixed (Cassels' isogeny invariance).
  PASS = the retained ledger channels (Omega, T, c_p -- each computed from the
         curve itself, never from L) separate every pair the 1D readout cannot,
         AND the Cassels combination Omega*prod(c_p)/T^2 is equal across the
         class, verified in-house.
  FAIL (program falsifier, register clause (c)) = a pair with ALL retained
         channels equal but different cycle data.
  In-house isogeny certificate: a_p agreement across the class at every good
  p < 400 (point counts only), plus equal bad-prime support.  No table lookup:
  if the curve data were wrong, the certificate fails loudly.

TEST C -- PHANTOM HUNT: run tower_exhaustion_test.py separately (reproduction:
  finite first depth for every accessible class; CM delayed signature 0,!=0).

NOT BUILT (deliberately): a point-count "level-3 Ceresa" moment test.  Point-count
moments read poles (Tate-shaped detection); the Ceresa signal is a central
DERIVATIVE, invisible to divergence statistics.  A fast moment test labeled
"Ceresa" would measure the wrong thing.  The Ceresa landing remains the slow
instrument (Target 7.1).

Run: python3 hodge_fast_tests.py          (~1 min, oracle-free)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sha_hinge as SH

# The 11a isogeny class (conductor 11, rank 0), Cremona models.
CLASS_11A = [
    ("11a1", 11, (0, -1, 1, -10, -20)),
    ("11a2", 11, (0, -1, 1, -7820, -263580)),
    ("11a3", 11, (0, -1, 1, 0, 0)),
]

PMAX = 400


def good_ap_vector(ainv, N, pmax=PMAX):
    prs = SH.sieve_primes(pmax)
    out = {}
    for p in prs:
        if N % p == 0:
            continue
        out[p] = SH.ap_general(p, *ainv)
    return out


def main():
    lines = []

    def P(s=""):
        print(s)
        lines.append(s)

    P("#" * 76)
    P("# HODGE-PROGRAM FAST TESTS -- battery v1 (oracle-free)")
    P("#" * 76)
    P()
    P("TEST A -- ledger-failure search v1: the 11a isogeny class")
    P("-" * 76)

    # --- 1. in-house isogeny certificate: identical a_p at every good p < PMAX
    vecs = {}
    for label, N, ainv in CLASS_11A:
        vecs[label] = good_ap_vector(ainv, N)
    labels = [c[0] for c in CLASS_11A]
    ref = vecs[labels[0]]
    max_dev = 0
    for lab in labels[1:]:
        for p, a in vecs[lab].items():
            max_dev = max(max_dev, abs(a - ref[p]))
    P(f"  [certificate] a_p agreement across class, good p < {PMAX}: "
      f"max |delta a_p| = {max_dev}")
    if max_dev != 0:
        P("  CERTIFICATE FAILED -- curves are not isogenous as entered; abort.")
        sys.exit(1)
    P("  => identical Dirichlet coefficients: the 1D value channel CANNOT")
    P("     separate these curves (same L-function, Faltings).")
    P()

    # --- 2. per-curve retained ledger, all in-house (sha_hinge machinery)
    rows = []
    for label, N, ainv in CLASS_11A:
        row = SH.sha_hinge(label, N, ainv)
        rows.append(row)

    P("  [ledger] per-curve retained channels (computed from the curve, not L):")
    P(f"    {'curve':8s} {'L(1)':>12s} {'Omega':>12s} {'T':>3s} "
      f"{'prod c_p':>9s} {'|Sha| land':>10s}")
    for r in rows:
        P(f"    {r['label']:8s} {r['L1']:12.7f} {r['Omega']:12.7f} "
          f"{r['T']:3d} {r['prodcp']:9d} {r['nearest_sq']:10d}")
    P()

    # --- 3. separation matrix: which channels separate which pairs
    P("  [separation] pairwise, channel by channel:")
    n = len(rows)
    sep_all_pairs = True
    for i in range(n):
        for j in range(i + 1, n):
            a, b = rows[i], rows[j]
            l1_sep = abs(a["L1"] - b["L1"]) / max(abs(a["L1"]), 1e-30) > 1e-6
            om_sep = abs(a["Omega"] - b["Omega"]) / a["Omega"] > 1e-9
            t_sep = a["T"] != b["T"]
            cp_sep = a["prodcp"] != b["prodcp"]
            pair_sep = om_sep or t_sep or cp_sep
            sep_all_pairs = sep_all_pairs and pair_sep
            P(f"    {a['label']} vs {b['label']}:  L(1) separates: {l1_sep};  "
              f"Omega: {om_sep};  T: {t_sep};  c_p: {cp_sep}"
              f"   -> ledger separates: {pair_sep}")
    P()

    # --- 4. Cassels isogeny invariance of the BSD combination, in-house
    P("  [Cassels] Omega * prod(c_p) / T^2 across the class (must coincide):")
    vals = [r["Omega"] * r["prodcp"] / (r["T"] ** 2) for r in rows]
    for r, v in zip(rows, vals):
        P(f"    {r['label']:8s} -> {v:.9f}")
    spread = (max(vals) - min(vals)) / max(vals)
    P(f"    relative spread = {spread:.2e}")
    P()

    # --- 5. verdict
    P("  VERDICT (Test A):")
    ok_sha = all(r["nearest_sq"] == 1 for r in rows)
    ok_cassels = spread < 1e-6
    P(f"    1D readout separates any pair:        NO  (identical a_p, certified)")
    P(f"    retained ledger separates every pair: {'YES' if sep_all_pairs else 'NO'}")
    P(f"    Cassels combination invariant:        "
      f"{'YES' if ok_cassels else 'NO'} (spread {spread:.1e})")
    P(f"    |Sha| landed = 1 on every member:     {'YES' if ok_sha else 'NO'}")
    if sep_all_pairs and ok_cassels and ok_sha:
        P("    => LEDGER-FAILURE SEARCH v1: no failure found.  The retained")
        P("       channels separate exactly what the 1D readout provably cannot,")
        P("       and redistribute in the Cassels-invariant combination.  The")
        P("       program's crux survives its first adversarial instance.")
    else:
        P("    => POTENTIAL LEDGER FAILURE OR INSTRUMENT DEFECT -- publish per")
        P("       the falsifiability register and investigate before proceeding.")
    P()
    P("  Scope, stated exactly: v1 tests GL(2)/Q isogeny classes, where the")
    P("  cycle-data variation is (Omega, T, c_p) at Sha = 1.  The stronger")
    P("  adversarial search -- a pair with equal FULL ledger and different Sha")
    P("  or different Chow/Griffiths data (higher dimension, same zeta) -- is")
    P("  the v2 target and the genuine clause-(c) falsifier hunt.")
    P()

    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "hodge_fast_tests_results.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    P("[results written to hodge_fast_tests_results.txt]")


if __name__ == "__main__":
    main()
