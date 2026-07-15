import Mathlib.RepresentationTheory.FDRep

/-!
# The self-duality obstruction: a frozen non-self-dual class cannot exist

The multi-rail carrier's freeze detector reads an **algebraic (Tate/Hodge) class** as a
copy of the trivial representation inside a fiber — an invariant vector, equivalently a
morphism `𝟙 ⟶ V` from the monoidal unit.  The order-2 exploration (companion notes,
`tmp/order2_freeze.py`, `tmp/sphere_ellipse.py`) hit a hard wall that turned out to be a
theorem, not a numerical failure: **a strictly non-self-dual piece carries no such class.**

The reason is Schur's lemma.  For a simple `V`, a nonzero `𝟙 ⟶ V` would be an isomorphism
(a nonzero morphism between simple objects is invertible), forcing `V ≅ 𝟙`.  So a simple `V`
**not** isomorphic to the unit has `𝟙 ⟶ V = 0`: no Tate/Hodge class.  Since the unit is
self-dual, any non-self-dual simple `V` satisfies `V ≇ 𝟙`, and the obstruction applies —
the detector's refusal to freeze a non-self-dual rail is exactly this vanishing, so the null
was correct (no false positive), and "make a frozen non-self-dual class" is impossible.

`tateClass_zero_of_simple_not_unit` is the machine-checked statement.  It asserts no Hodge
conjecture; it is the exact reason the non-self-dual freeze route is closed.  No `sorry`,
no `axiom`.
-/

open CategoryTheory Module
open scoped MonoidalCategory

namespace CriticalLinePhasor.NonSelfDual

variable {k : Type*} [Field k] [IsAlgClosed k] {G : Type*} [Group G]

/-- **The self-duality obstruction.**  A simple representation `V` not isomorphic to the
trivial (unit) representation carries **no nonzero Tate/Hodge class**: every morphism from
the monoidal unit `𝟙` to `V` is zero.  A "frozen non-self-dual class" is therefore
impossible — the unit is self-dual, so a non-self-dual simple `V` is not `≅ 𝟙` and this
vanishing applies.  Proof: Schur (`FDRep.finrank_hom_simple_simple`) makes the hom space
`0`-dimensional, hence a subsingleton. -/
theorem tateClass_zero_of_simple_not_unit (V : FDRep k G)
    [Simple (𝟙_ (FDRep k G))] [Simple V]
    (hne : ¬ Nonempty (𝟙_ (FDRep k G) ≅ V))
    (f : 𝟙_ (FDRep k G) ⟶ V) : f = 0 := by
  have hz : finrank k (𝟙_ (FDRep k G) ⟶ V) = 0 := by
    rw [FDRep.finrank_hom_simple_simple, if_neg hne]
  have hss : Subsingleton (𝟙_ (FDRep k G) ⟶ V) := finrank_zero_iff.mp hz
  exact Subsingleton.elim f 0

/-- A simple representation of dimension different from one has no trivial constituent.  The
dimension comparison is used only to prove that the two simple representations are non-isomorphic;
the vanishing itself is Schur's lemma in `FDRep`. -/
theorem tateClass_zero_of_simple_finrank_ne_one (V : FDRep k G)
    [Simple (𝟙_ (FDRep k G))] [Simple V]
    (hrank : finrank k V ≠ 1) (f : 𝟙_ (FDRep k G) ⟶ V) : f = 0 := by
  apply tateClass_zero_of_simple_not_unit V
  rintro ⟨i⟩
  apply hrank
  calc
    finrank k V = finrank k (𝟙_ (FDRep k G)) :=
      (FDRep.isoToLinearEquiv i).finrank_eq.symm
    _ = 1 := by simp

end CriticalLinePhasor.NonSelfDual

#print axioms CriticalLinePhasor.NonSelfDual.tateClass_zero_of_simple_not_unit
#print axioms CriticalLinePhasor.NonSelfDual.tateClass_zero_of_simple_finrank_ne_one
