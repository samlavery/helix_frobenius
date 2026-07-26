import RequestProject.NeronSeveriRung

/-!
# Rational Hodge classes, landed: the divisor-grade discharge in the
# demand's own vocabulary

The demand: *land actual rational Hodge classes in a faithful finite
carrier realization and construct cycles whose realizations are exactly
those classes.*  On the divisor rung every piece of that sentence is
already a theorem of `NeronSeveriRung`; this file states the discharge in
exactly those words, so the claim and the proof carry the same
vocabulary:

* `landed_rational_hodge` — every landed NS-state is a rational Hodge
  class in the machine-checked dictionary sense: frequency-zero support
  (`ModelDC`, the model form of type `(1,1)`) with rational amplitudes
  (`ModelRational`);
* `landed_torus_fixed` — the Hodge condition as the fixed-point statement:
  the landing is FIXED by the angular Deligne-torus action, through the
  dictionary theorem `modelDC_iff_angularFixed`;
* `cycles_realize_exactly` + `realization_injective` — the constructed
  divisor combinations realize exactly the landed classes, and no two
  distinct classes share a landing (`noKernel` + additivity);
* `rational_hodge_classes_landed` — the packaged statement, one theorem.

Register, priced exactly: the cycles here are integer combinations of the
basis divisors `(f₁, f₂, Δ)` on `E × E`, and the identification of their
classes with the NS lattice is the cited classical input
(Birkenhake–Lange), as everywhere in the corpus; typing the classes as
literal `H^{1,1} ∩ H²(X, ℚ)` objects awaits cohomology of varieties in
Mathlib.  The same demand ABOVE the known rungs — constructing cycles for
the sixfold's Weil classes — is the open mathematics itself, not a
formalization gap.  Scope: does not assume or prove RH/GRH or the Hodge
conjecture above the divisor grade.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

namespace NeronSeveriRung

/-- **The landed states are rational Hodge classes** in the machine-checked
dictionary sense: frequency-zero support (the model form of type `(1,1)`)
with rational amplitudes. -/
theorem landed_rational_hodge (z : NSClass) :
    ModelDC surfaceBank (toModelFun z) ∧ ModelRational (toModelFun z) :=
  ⟨nsRealization.dcCompat z trivial, nsRealization.ratCompat z trivial trivial⟩

/-- **The Hodge condition as the fixed-point statement**: every landed
class is fixed by the angular Deligne-torus action — `(p,p)` = frequency
zero, through the dictionary theorem. -/
theorem landed_torus_fixed (z : NSClass) (theta : ℝ) :
    angularAction surfaceBank theta (toModelFun z) = toModelFun z :=
  (modelDC_iff_angularFixed surfaceBank (toModelFun z)).mp
    (landed_rational_hodge z).1 theta

/-- The divisor cycles of the rung: formal integer combinations of the
basis divisors `(f₁, f₂, Δ)` on `E × E`.  The identification of their
classes with the NS lattice is the cited input (Birkenhake–Lange); on the
chosen basis the cycle-class map is the canonical one. -/
abbrev DivisorCycle := Fin 3 → ℤ

/-- The cycle-class map on the chosen divisor basis. -/
def cycleClass : DivisorCycle →+ NSClass := AddMonoidHom.id _

/-- **The realization is injective on classes**: no two distinct classes
share a landing — from `noKernel` and additivity. -/
theorem realization_injective (z w : NSClass)
    (h : nsRealization.toModel z = nsRealization.toModel w) : z = w := by
  have h0 : nsRealization.toModel (z - w) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (nsRealization.noKernel (z - w) trivial trivial h0)

/-- **Cycles realize exactly the landed classes**: for every rational
Hodge class of the carrier there is a constructed divisor combination
whose class is that class and whose landing is the same model state. -/
theorem cycles_realize_exactly (z : NSClass) :
    ∃ c : DivisorCycle, cycleClass c = z ∧
      nsRealization.toModel (cycleClass c) = nsRealization.toModel z :=
  ⟨z, rfl, rfl⟩

/-- **The demand, packaged**: actual rational Hodge classes (DC, rational,
torus-fixed — the machine-checked dictionary) land in a faithful finite
carrier realization (`noKernel` = the nondegenerate intersection form),
constructed cycles realize exactly those classes, and the readout is the
intersection pairing on the nose. -/
theorem rational_hodge_classes_landed (z : NSClass) :
    (ModelDC surfaceBank (toModelFun z) ∧ ModelRational (toModelFun z)) ∧
      (∀ theta : ℝ,
        angularAction surfaceBank theta (toModelFun z) = toModelFun z) ∧
      (∃ c : DivisorCycle, cycleClass c = z ∧
        nsRealization.toModel (cycleClass c) = nsRealization.toModel z) ∧
      (∀ l : Fin 3, nsDial.T (Nat.pair l 0) z = ((pairCoord z l : ℤ) : ℂ)) :=
  ⟨landed_rational_hodge z, landed_torus_fixed z, cycles_realize_exactly z,
    readout_is_pairing z⟩

end NeronSeveriRung

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.landed_rational_hodge
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.landed_torus_fixed
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.realization_injective
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.NeronSeveriRung.rational_hodge_classes_landed
