import RequestProject.CPSBasicIdentityFinite
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Multi-winding finite-abelian CPS basic identity

The character family of any finite abelian winding cell is a basis of its complex-valued scalar
readouts.  Thus the complete character-twist bank separates multi-coordinate 3D cells, including
cells indexed by products such as `Fin d → ZMod N`.
-/

namespace CriticalLinePhasor.ThreeDConverse

/-- The coordinate of a finite abelian winding cell in the complete additive-character basis. -/
noncomputable def finiteAbelianTwistReadout
    (G : Type*) [AddCommGroup G] [Finite G]
    (cell : G → ℂ) (character : AddChar G ℂ) : ℂ :=
  (AddChar.complexBasis G).repr cell character

/-- The complete multi-winding character family separates finite abelian 3D cells. -/
theorem finiteAbelianCell_eq_of_all_twists_eq
    {G : Type*} [AddCommGroup G] [Finite G]
    {cell₁ cell₂ : G → ℂ}
    (h : ∀ character : AddChar G ℂ,
      finiteAbelianTwistReadout G cell₁ character =
        finiteAbelianTwistReadout G cell₂ character) :
    cell₁ = cell₂ := by
  apply (AddChar.complexBasis G).repr.injective
  ext character
  exact h character

/-- Equality of all character twists of a translated multi-winding cell forces pointwise
translation invariance. -/
theorem finiteAbelianCell_translation_invariant_of_twists
    {G : Type*} [AddCommGroup G] [Finite G]
    (cell : G → ℂ) (a : G)
    (h : ∀ character : AddChar G ℂ,
      finiteAbelianTwistReadout G (fun x => cell (x + a)) character =
        finiteAbelianTwistReadout G cell character) :
    ∀ x : G, cell (x + a) = cell x := by
  have hfun : (fun x => cell (x + a)) = cell :=
    finiteAbelianCell_eq_of_all_twists_eq h
  exact fun x => congrFun hfun x

/-- Vanishing of every character-twisted coordinate kills a multi-winding residual pointwise. -/
theorem finiteAbelianCell_zero_of_all_twists_zero
    {G : Type*} [AddCommGroup G] [Finite G]
    (residual : G → ℂ)
    (h : ∀ character : AddChar G ℂ,
      finiteAbelianTwistReadout G residual character = 0) :
    residual = 0 := by
  apply finiteAbelianCell_eq_of_all_twists_eq
  intro character
  rw [h character]
  simp [finiteAbelianTwistReadout]

/-- Fourier reconstruction of the original multi-winding cell from all twisted coordinates. -/
theorem finiteAbelianCell_character_reconstruction
    (G : Type*) [AddCommGroup G] [Finite G]
    (cell : G → ℂ) :
    ∑ character : AddChar G ℂ,
        finiteAbelianTwistReadout G cell character •
          (character : G → ℂ) = cell := by
  simpa [finiteAbelianTwistReadout] using (AddChar.complexBasis G).sum_repr cell

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.finiteAbelianCell_eq_of_all_twists_eq
#print axioms CriticalLinePhasor.ThreeDConverse.finiteAbelianCell_translation_invariant_of_twists
#print axioms CriticalLinePhasor.ThreeDConverse.finiteAbelianCell_zero_of_all_twists_zero
#print axioms CriticalLinePhasor.ThreeDConverse.finiteAbelianCell_character_reconstruction
