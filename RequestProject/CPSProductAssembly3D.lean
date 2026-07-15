import RequestProject.CPSConverse3DDensity
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Product assembly for the 3D converse carrier

Finite-coordinate carrier moves are dense in the product topology.  Invariance under every
single-coordinate move therefore composes over finite multiplicative support and extends, by
continuity, to every product move.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- A dependent product move has finite support when it is nontrivial at finitely many
coordinates. -/
def HasFiniteProductSupport
    {ι : Type*} {G : ι → Type*} [∀ i, One (G i)]
    (g : ∀ i, G i) : Prop :=
  Set.Finite {i | g i ≠ 1}

/-- Restrict a product move to a finite set of coordinates. -/
def finiteMulTruncation
    {ι : Type*} {G : ι → Type*} [DecidableEq ι] [∀ i, One (G i)]
    (s : Finset ι) (g : ∀ i, G i) : ∀ i, G i :=
  fun i => if i ∈ s then g i else 1

/-- A finite truncation has finite multiplicative support. -/
theorem finiteMulTruncation_hasFiniteMulSupport
    {ι : Type*} {G : ι → Type*} [DecidableEq ι] [∀ i, One (G i)]
    (s : Finset ι) (g : ∀ i, G i) :
    HasFiniteProductSupport (finiteMulTruncation s g) := by
  rw [HasFiniteProductSupport]
  exact s.finite_toSet.subset (by
    intro i hi
    by_contra his
    have his' : i ∉ s := by simpa using his
    exact hi (by simp [finiteMulTruncation, his']))

/-- Finite truncations converge coordinatewise to the original product move. -/
theorem finiteMulTruncation_tendsto
    {ι : Type*} {G : ι → Type*}
    [DecidableEq ι] [∀ i, One (G i)] [∀ i, TopologicalSpace (G i)]
    (g : ∀ i, G i) :
    Filter.Tendsto (fun s : Finset ι => finiteMulTruncation s g)
      Filter.atTop (nhds g) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with s hs
  have hi : i ∈ s := hs (by simp)
  simp [finiteMulTruncation, hi]

/-- Product moves with finite multiplicative support are dense in the full product topology. -/
theorem dense_hasFiniteMulSupport
    {ι : Type*} {G : ι → Type*}
    [DecidableEq ι] [∀ i, One (G i)] [∀ i, TopologicalSpace (G i)] :
    Dense {g : ∀ i, G i | HasFiniteProductSupport g} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro g
  exact mem_closure_of_tendsto (finiteMulTruncation_tendsto g)
    (Filter.Eventually.of_forall fun s => finiteMulTruncation_hasFiniteMulSupport s g)

/-- Single-coordinate invariance composes to every finite-support product move. -/
theorem readout_invariant_of_single_moves_of_finiteMulSupport
    {ι X : Type*} {G : ι → Type*}
    [DecidableEq ι] [∀ i, Group (G i)] [MulAction (∀ i, G i) X]
    (readout : X → ℂ)
    (hsingle : ∀ (i : ι) (a : G i) (x : X),
      readout (Pi.mulSingle i a • x) = readout x)
    (g : ∀ i, G i) (hg : HasFiniteProductSupport g) (x : X) :
    readout (g • x) = readout x := by
  classical
  have hind : ∀ s : Finset ι, ∀ (g : ∀ i, G i),
      (∀ i, i ∉ s → g i = 1) → ∀ x : X, readout (g • x) = readout x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro g hg x
        have hgone : g = 1 := by
          funext i
          exact hg i (by simp)
        simp [hgone]
    | @insert a s ha ih =>
        intro g hg x
        let tail : ∀ i, G i := Function.update g a 1
        have htail : ∀ i, i ∉ s → tail i = 1 := by
          intro i hi
          by_cases hia : i = a
          · subst i
            simp [tail]
          · rw [show tail i = g i by exact Function.update_of_ne hia 1 g]
            exact hg i (by simp [hia, hi])
        have hdecomp : Pi.mulSingle a (g a) * tail = g := by
          funext i
          by_cases hia : i = a
          · subst i
            simp [tail]
          · change Pi.mulSingle a (g a) i * tail i = g i
            rw [show tail i = g i by exact Function.update_of_ne hia 1 g]
            simp [Pi.mulSingle, hia]
        rw [← hdecomp, mul_smul]
        calc
          readout (Pi.mulSingle a (g a) • tail • x) = readout (tail • x) :=
            hsingle a (g a) (tail • x)
          _ = readout x := ih tail htail x
  change Set.Finite {i | g i ≠ 1} at hg
  apply hind hg.toFinset g
  intro i hi
  have himem : i ∉ {j | g j ≠ 1} := by
    simpa using hi
  by_contra hgi
  exact himem hgi

/-- **Product assembly for the 3D converse.** Continuous readout invariance under each local move
extends to invariance under every move in the full product group. -/
theorem cpsProduct3D_readout_invariant
    {ι X : Type*} {G : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (G i)] [∀ i, Group (G i)]
    [TopologicalSpace X] [MulAction (∀ i, G i) X]
    [ContinuousSMul (∀ i, G i) X]
    (readout : X → ℂ) (hreadout : Continuous readout)
    (hsingle : ∀ (i : ι) (a : G i) (x : X),
      readout (Pi.mulSingle i a • x) = readout x)
    (g : ∀ i, G i) (x : X) :
    readout (g • x) = readout x := by
  apply readout_invariant_of_dense_moves
    {g : ∀ i, G i | HasFiniteProductSupport g}
    dense_hasFiniteMulSupport readout hreadout
  intro a ha y
  exact readout_invariant_of_single_moves_of_finiteMulSupport readout hsingle a ha y

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.finiteMulTruncation_tendsto
#print axioms CriticalLinePhasor.ThreeDConverse.dense_hasFiniteMulSupport
#print axioms CriticalLinePhasor.ThreeDConverse.readout_invariant_of_single_moves_of_finiteMulSupport
#print axioms CriticalLinePhasor.ThreeDConverse.cpsProduct3D_readout_invariant
