import RequestProject.CPSConverse3DReadout
import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite winding-cell form of the CPS basic identity

On a finite helix winding cell, the complete family of additive twists is the discrete Fourier
transform.  Since that transform is a linear equivalence, equality of every twisted readout forces
equality of the original 3D cell.  Applied to a translated cell, the twist identities force the
corresponding winding/transvection invariance.
-/

open scoped ZMod

namespace CriticalLinePhasor.ThreeDConverse

/-- The additive-twist readout of a finite winding cell. -/
noncomputable def additiveTwistReadout
    {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (cell : ZMod N → E) (k : ZMod N) : E :=
  ZMod.dft cell k

/-- The full additive-twist family separates finite winding cells. -/
theorem windingCell_eq_of_all_additiveTwists_eq
    {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]
    {cell₁ cell₂ : ZMod N → E}
    (h : ∀ k : ZMod N,
      additiveTwistReadout cell₁ k = additiveTwistReadout cell₂ k) :
    cell₁ = cell₂ := by
  apply ZMod.dft.injective
  funext k
  exact h k

/-- Equality of every additive twist with the twists of a translated cell forces the cell itself
to be translation invariant. -/
theorem windingCell_translation_invariant_of_twists
    {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (cell : ZMod N → E) (a : ZMod N)
    (h : ∀ k : ZMod N,
      additiveTwistReadout (fun j => cell (j + a)) k =
        additiveTwistReadout cell k) :
    ∀ j : ZMod N, cell (j + a) = cell j := by
  have hfun : (fun j => cell (j + a)) = cell :=
    windingCell_eq_of_all_additiveTwists_eq h
  exact fun j => congrFun hfun j

/-- Vanishing of every twisted residual forces the original finite winding-cell residual to
vanish pointwise. -/
theorem windingCell_zero_of_all_additiveTwists_zero
    {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (residual : ZMod N → E)
    (h : ∀ k : ZMod N, additiveTwistReadout residual k = 0) :
    residual = 0 := by
  apply windingCell_eq_of_all_additiveTwists_eq
  intro k
  rw [h k]
  simp [additiveTwistReadout]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.windingCell_eq_of_all_additiveTwists_eq
#print axioms CriticalLinePhasor.ThreeDConverse.windingCell_translation_invariant_of_twists
#print axioms CriticalLinePhasor.ThreeDConverse.windingCell_zero_of_all_additiveTwists_zero
