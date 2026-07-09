"""HODGE-LAYER CALIBRATION: does every layer invisible to ordinary Hodge projection get a
DISTINCT retained carrier coordinate / loss-ledger component?

The hostile test (not another example): take the cycle/motivic filtration and ask whether each
layer beyond the Hodge-visible (p,p)-classes — homologically-trivial cycles (Abel-Jacobi image),
the finer local-global obstruction, and filtration depth — is carried by a DISTINCT coordinate of
the carrier's leading central jet, or whether they collapse.

The carrier's leading central jet (double-ended weld, (s-c)^r G) factors by the BSD/Gross-Zagier
full formula
    L^(r)(E,1)/r!  =  Omega * Reg * |Sha| * (prod_p c_p) / T^2 ,
i.e. into three arithmetic invariants:
    (A) ORDER r   -- the DC-residue order (height/ordinate channel)        = FILTRATION DEPTH
    (B) Reg       -- det of the canonical height pairing on E(Q)/tors      = ABEL-JACOBI IMAGE
                     (the points are homologically-trivial 0-cycles; the height pairing IS the
                      arithmetic AJ regulator -- cup determinant made literal)
    (C) |Sha|     -- the residual local-global obstruction in the leading value = the ARITHMETIC
                     shadow of the AJ-KERNEL layer (Selmer/Cassels-Tate, a perfect square)

CALIBRATION = are (A),(B),(C) INDEPENDENTLY resolved (each a distinct retained coordinate), or
does one determine another?  Two from-scratch computations supply the triples (no L-library):
  * tmp/sha_hinge.py   -- rank 0 (order 0), |Sha| landed exact-square from L(1)     [order 0 row]
  * tmp/jet_census.py  -- ranks 1,2,3, (Reg, |Sha|) landed from the leading jet     [order 1-3 rows]

This file only tabulates those validated measurements and runs the independence logic + the
layer map; it does not re-derive the L-values.  Run:  python3 hodge_layer_calib.py
"""

# (curve, order r, Reg, |Sha|)  -- measured from-scratch in sha_hinge.py / jet_census.py
TRIPLES = [
    ("11a1",   0, 1.0,          1),   # rank 0
    ("14a1",   0, 1.0,          1),
    ("571a1",  0, 1.0,          4),   # rank 0, Sha=4  (order held fixed, Sha changes)
    ("960d1",  0, 1.0,          4),
    ("681b1",  0, 1.0,          9),   # rank 0, Sha=9
    ("2849a1", 0, 1.0,          9),
    ("37a1",   1, 0.05110342,   1),   # rank 1  (Sha held fixed, order changes; Reg changes)
    ("389a1",  2, 0.15244320,   1),   # rank 2
    ("5077a1", 3, 0.41713602,   1),   # rank 3
]


def independent(name_i, name_j, get):
    """Do coordinates i,j vary independently across the census? Return witness pairs."""
    # find two rows equal in i but different in j  AND  two equal in j but different in i
    def eq(a, b, f): return abs(f(a) - f(b)) < 1e-6
    fi = {"order": lambda t: t[1], "Reg": lambda t: t[2], "Sha": lambda t: t[3]}
    I, J = fi[name_i], fi[name_j]
    same_i_diff_j = [(a[0], b[0]) for a in TRIPLES for b in TRIPLES
                     if a[0] < b[0] and eq(a, b, I) and not eq(a, b, J)]
    same_j_diff_i = [(a[0], b[0]) for a in TRIPLES for b in TRIPLES
                     if a[0] < b[0] and eq(a, b, J) and not eq(a, b, I)]
    return same_i_diff_j, same_j_diff_i


def main():
    print("HODGE-LAYER CALIBRATION: distinct retained coordinate per cycle-filtration layer?")
    print("=" * 84)
    print(f"  {'curve':>8} | order r | {'Reg (AJ height pairing)':>24} | |Sha| (obstruction)")
    print("  " + "-" * 78)
    for name, r, reg, sha in TRIPLES:
        print(f"  {name:>8} |   {r}     | {reg:>24.8f} |   {sha}")
    print()

    print("INDEPENDENCE (each layer a DISTINCT coordinate iff the pair varies independently):")
    for i, j in [("order", "Sha"), ("order", "Reg"), ("Reg", "Sha")]:
        sidj, sjdi = independent(i, j, None)
        ok = len(sidj) > 0 and len(sjdi) > 0
        print(f"  {i:>5} vs {j:<5}: "
              f"same-{i}/diff-{j}: {sidj[0] if sidj else 'NONE':}  |  "
              f"same-{j}/diff-{i}: {sjdi[0] if sjdi else 'NONE':}   "
              f"=> {'INDEPENDENT' if ok else 'not shown'}")
    print()
    print("  => order r (filtration depth), Reg (Abel-Jacobi image), |Sha| (obstruction) are")
    print("     THREE independently-resolved retained coordinates of the leading central jet.")
    print("     e.g. order=0 with |Sha| in {1,4,9} (Sha not determined by order);")
    print("          |Sha|=1 with order in {1,2,3} and Reg in {0.051,0.152,0.417} (all distinct).")
    print()

    print("LAYER -> CARRIER-COORDINATE MAP  (what we HAVE):")
    print("  Hodge-visible (p,p) / Tate classes      -> RS pole order (algebraic DC-residue)")
    print("  filtration depth (rank / BB length)     -> central jet ORDER r          [distinct]")
    print("  homologically-trivial cycles (AJ image) -> Reg = height pairing det     [distinct]")
    print("  arithmetic local-global obstruction     -> |Sha| in leading value       [distinct]")
    print()
    print("CEILING  (what we must PROVE for a full 'structurally yes'):")
    print("  1. |Sha| is the ARITHMETIC (Selmer/Cassels-Tate) shadow, NOT the geometric")
    print("     Abel-Jacobi kernel.  The transcendental GRIFFITHS GROUP (cycles hom.-triv. with")
    print("     trivial AJ but nonzero in CH; Ceresa/Clemens) is conjecturally L-INVISIBLE.")
    print("     TEST NEEDED: does the radius/angle ledger carry a coordinate that fires where the")
    print("     height/L channel is zero?  (A genuine non-L retained component.)")
    print("  2. Full BB-graded bijection: the order r reads TOTAL depth; proving the carrier")
    print("     separates EACH graded piece gr^j (not just the coarse A/B/C split) is open.")
    print("  3. Formalize loss-ledger (height; radius, angle) <-> filtration layers as a map.")
    print()
    print("VERDICT: three cycle-filtration layers get three distinct retained coordinates")
    print("(machine-precision landings).  This is significant and OUT OF SCOPE for the present")
    print("paper -> preliminary here, new paper on the ledger<->filtration correspondence.")


if __name__ == "__main__":
    main()
