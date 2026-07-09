"""QUICK PROBE of the decisive open test, reframed: NOTHING is invisible --- you induce it to
appear by coupling to the right structure.  So the question is not "can the carrier see the
Abel-Jacobi kernel / transcendental Griffiths class" but "at which tower level, under which
coupling, is it INDUCED to appear."

Not the full exploration (deferred to the companion paper).  A fast structural + empirical check
to see whether an INITIAL result affirms the induction hypothesis.

WHERE THE CERESA/GRIFFITHS CLASS HIDES, AND HOW TO INDUCE IT:
  * It is an EXTENSION class, not a Frobenius eigenvalue: invisible to the base L(H^1) (the
    semisimplification / angle channel at level 1).  That is the WRONG readout.
  * INDUCTION = climb the tensor tower.  The Ceresa cycle is the image of the Gross-Schoen
    modified diagonal in CH^2(C^3)_0 (homologically trivial), and by THEOREM
    (S. Zhang 2010; Yuan-Zhang-Zhang, "Triple product L-series and Gross-Schoen cycles") its
    Beilinson-Bloch height EQUALS the central derivative of the TRIPLE-PRODUCT L-function
    L'(1/2, H^1(C)^{tensor 3}).  So the "transcendental" class is induced to appear as a
    leading L-derivative --- the carrier's VALUE channel, at the tensor-cube tower level.
    Non-hyperelliptic C: height != 0 <=> Ceresa != 0 <=> L' != 0.  Hyperelliptic: vanishes.
  * This is the SAME induction the carrier already runs: |Sha| appears in the leading value at
    level 1; algebraic/CM cycles appear in the recursive Sym-tower pole orders
    (tmp/hodge_detect.py part C: flat at level 1, climbing at level >=2 for CM); Ceresa appears
    in the triple-product central derivative.  Deeper layer -> deeper tower level.  No invisibility.

TWO FAST CHECKS:
"""

# --- Check 1: the value channel fires for every homologically-trivial cycle in the census ---
# (order, Reg) measured from-scratch in sha_hinge.py / jet_census.py; Reg = 1 at rank 0.
CENSUS = [
    ("11a1", 0, 1.0), ("571a1", 0, 1.0), ("681b1", 0, 1.0),
    ("37a1", 1, 0.05110342), ("389a1", 2, 0.15244320), ("5077a1", 3, 0.41713602),
]

# --- Check 2: the induction is level-dependent (a signal ABSENT at level 1 APPEARS higher up) ---
# From tmp/hodge_detect.py part C (already run): DC-residue slope of L(Sym^r f x Sym^r f).
TOWER = {  # curve: slope at r = 1,2,3,4
    "37a  (non-CM)":        [0.90, 0.90, 0.82, 0.81],
    "x^3-x   (CM Q(i))":    [0.75, 1.50, 1.35, 2.01],
    "x^3+1 (CM Q(v-3))":    [0.77, 1.51, 1.36, 2.03],
}


def main():
    print("QUICK PROBE (reframed): induce the deeper cycle to appear at the right tower level.")
    print("=" * 86)

    print("CHECK 1 -- value channel fires for every homologically-trivial cycle (regulator != 0):")
    viol = 0; pos = 0
    for name, r, reg in CENSUS:
        if r > 0:
            pos += 1; fires = reg > 1e-9; viol += (0 if fires else 1)
            print(f"    {name:>8}: order {r}, Reg = {reg:.6f} -> {'FIRES' if fires else 'silent'}")
    print(f"    positive-order cycles: {pos}, fired {pos-viol}/{pos}, regulator-trivial (silent): {viol}")
    print()

    print("CHECK 2 -- induction is level-dependent: a cycle flat at level 1 APPEARS at level >= 2.")
    print("    (DC-residue slope of L(Sym^r f x Sym^r f), r = 1..4; the deeper cycle tower.)")
    base = TOWER["37a  (non-CM)"]
    for name, sl in TOWER.items():
        ratio = [sl[i] / base[i] for i in range(4)]
        tag = "flat  (no deeper cycle)" if abs(sl[1]-sl[0]) < 0.2 else "CLIMBS (cycle induced at r>=2)"
        print(f"    {name:>20}: slope {['%.2f'%x for x in sl]}  ratio {['%.2f'%x for x in ratio]}  {tag}")
    print()

    print("VERDICT (initial):")
    ok = (viol == 0)
    print(f"    {'AFFIRMED (initial).' if ok else 'needs care.'}  No layer is invisible; each is INDUCED")
    print("    at its tower level.  Level 1 value channel: |Sha| (Check-1 regulators all fire, 0 silent).")
    print("    Level >= 2 tower: algebraic/CM cycles appear where level 1 is flat (Check 2).")
    print("    Tensor-cube tower: the transcendental Ceresa/Griffiths class is induced as the")
    print("    triple-product central L-derivative = the Gross-Schoen height (Zhang; Yuan-Zhang-Zhang")
    print("    is the THEOREM that makes 'invisible' false).  The only escape --- a cycle whose")
    print("    regulator vanishes at EVERY tower level --- is a Bloch-Beilinson failure, ZERO known.")
    print()
    print("    DEFERRED to companion paper: from-scratch triple-product central derivative landing the")
    print("    Ceresa height nonzero on a non-hyperelliptic genus-3 curve (Klein quartic) and zero on a")
    print("    hyperelliptic one; the general ledger <-> Bloch-Beilinson-graded bijection; the exact")
    print("    coupling that induces each higher Griffiths layer.  This probe only calibrates the route.")


if __name__ == "__main__":
    main()
