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
conjecture; it is the exact reason the non-self-dual freeze route is closed.
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
    _ = 1 := by
      change finrank k k = 1
      exact finrank_self k

/-- Symmetric-power-sized form: a simple representation of dimension `r+1`, with `r` positive,
has no morphism from the trivial representation. -/
theorem tateClass_zero_of_simple_finrank_succ (V : FDRep k G) (r : ℕ)
    [Simple (𝟙_ (FDRep k G))] [Simple V]
    (hr : finrank k V = r + 1) (hrpos : 1 ≤ r)
    (f : 𝟙_ (FDRep k G) ⟶ V) : f = 0 := by
  apply tateClass_zero_of_simple_finrank_ne_one V
  rw [hr]
  omega

/-! ## General Schur exclusion (the group-representation statement, not a bare finite-rank one)

The exclusion aristotle's objection 5 requires is **not** "smaller dimension ⇒ no embedding" (false
for plain vector spaces).  It is Schur's lemma for the *group action*: a nonzero map between simple
`G`-representations is an isomorphism, so **non-isomorphic** simples have zero Hom.  Dimension enters
only to certify non-isomorphism.  Stated below for arbitrary simple `V W : FDRep k G` — with the
genuine `G`-action — so it applies to any twist / any constituent, not merely the unit. -/

/-- **Schur exclusion, general form.**  For simple `G`-representations `V`, `W` that are **not
isomorphic**, every morphism `V ⟶ W` is zero.  This is Schur's lemma in `FDRep k G`; the group
action is present (`FDRep.finrank_hom_simple_simple`), so it is a representation-theoretic statement,
not a bare linear-algebra dimension count. -/
theorem hom_zero_of_simple_not_iso {V W : FDRep k G} [Simple V] [Simple W]
    (hne : ¬ Nonempty (V ≅ W)) (f : V ⟶ W) : f = 0 := by
  have hz : finrank k (V ⟶ W) = 0 := by rw [FDRep.finrank_hom_simple_simple, if_neg hne]
  exact Subsingleton.elim (h := finrank_zero_iff.mp hz) f 0

/-- Different dimensions ⇒ non-isomorphic representations.  This is the **only** role dimension
plays; it supplies non-isomorphism, never the vanishing directly. -/
theorem not_iso_of_finrank_ne {V W : FDRep k G} (h : finrank k V ≠ finrank k W) :
    ¬ Nonempty (V ≅ W) := by
  rintro ⟨i⟩
  exact h (FDRep.isoToLinearEquiv i).finrank_eq

/-- **The corrected exclusion.**  For simple `G`-representations with `finrank V < finrank W`, every
`V ⟶ W` is zero — because the strict dimension inequality forces non-isomorphism
(`not_iso_of_finrank_ne`) and Schur (`hom_zero_of_simple_not_iso`) then forces the vanishing.  The
vanishing is Schur's lemma with the group action, *not* "dimension alone": exactly the step objection
5 flags, done correctly. -/
theorem hom_zero_of_finrank_lt {V W : FDRep k G} [Simple V] [Simple W]
    (h : finrank k V < finrank k W) (f : V ⟶ W) : f = 0 :=
  hom_zero_of_simple_not_iso (not_iso_of_finrank_ne (Nat.ne_of_lt h)) f

end CriticalLinePhasor.NonSelfDual

#print axioms CriticalLinePhasor.NonSelfDual.tateClass_zero_of_simple_not_unit
#print axioms CriticalLinePhasor.NonSelfDual.tateClass_zero_of_simple_finrank_ne_one
#print axioms CriticalLinePhasor.NonSelfDual.tateClass_zero_of_simple_finrank_succ
#print axioms CriticalLinePhasor.NonSelfDual.hom_zero_of_simple_not_iso
#print axioms CriticalLinePhasor.NonSelfDual.hom_zero_of_finrank_lt
