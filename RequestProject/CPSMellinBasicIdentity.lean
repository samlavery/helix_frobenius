import RequestProject.CPSConverse3DDensity
import Mathlib.Analysis.MellinInversion

/-!
# Inverse-Mellin recovery of the CPS reflection identity

The completed functional equation determines the reflected theta readout whenever Mellin inversion
applies.  This supplies the analytic direction needed before finite character separation turns the
twist family into transvection invariance.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

/-- The theta-side reflection associated with weight `k` and scalar `ε`. -/
noncomputable def reflectedTheta (k : ℝ) (ε : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ε • ((x : ℂ) ^ (-k : ℂ) • g (1 / x))

/-- Mellin transform of the reflected theta readout. -/
theorem mellin_reflectedTheta (k : ℝ) (ε : ℂ) (g : ℝ → ℂ) (s : ℂ) :
    mellin (reflectedTheta k ε g) (k - s) = ε • mellin g s := by
  unfold reflectedTheta
  have hinv := mellin_comp_inv g (-s)
  have hweight := mellin_cpow_smul (fun t : ℝ => g t⁻¹) (k - s) (-k : ℂ)
  have hscalar := mellin_const_smul
    (fun t : ℝ => (t : ℂ) ^ (-k : ℂ) • g t⁻¹) (k - s) ε
  rw [show (k : ℂ) - s + (-k : ℂ) = -s by ring, hinv] at hweight
  rw [hweight] at hscalar
  simpa [one_div] using hscalar

/-- Mellin uniqueness on the positive ray, obtained by applying inverse Mellin to both functions. -/
theorem eqOn_pos_of_mellin_eq
    (sigma : ℝ) (f g : ℝ → ℂ)
    (hfConv : MellinConvergent f (sigma : ℂ))
    (hgConv : MellinConvergent g (sigma : ℂ))
    (hfVert : VerticalIntegrable (mellin f) sigma volume)
    (hgVert : VerticalIntegrable (mellin g) sigma volume)
    (hmellin : mellin f = mellin g) :
    ∀ x : ℝ, 0 < x → ContinuousAt f x → ContinuousAt g x → f x = g x := by
  intro x hx hfc hgc
  calc
    f x = mellinInv sigma (mellin f) x :=
      (mellinInv_mellin_eq sigma f hx hfConv hfVert hfc).symm
    _ = mellinInv sigma (mellin g) x := by rw [hmellin]
    _ = g x := mellinInv_mellin_eq sigma g hx hgConv hgVert hgc

/-- A completed Mellin functional equation recovers the pointwise theta reflection on the positive
ray under the standard Mellin-inversion hypotheses. -/
theorem theta_reflection_of_mellin_functionalEquation
    (k sigma : ℝ) (ε : ℂ) (f g : ℝ → ℂ)
    (hFE : ∀ s : ℂ, mellin f (k - s) = ε • mellin g s)
    (hfConv : MellinConvergent f (sigma : ℂ))
    (hrefConv : MellinConvergent (reflectedTheta k ε g) (sigma : ℂ))
    (hfVert : VerticalIntegrable (mellin f) sigma volume)
    (hrefVert : VerticalIntegrable (mellin (reflectedTheta k ε g)) sigma volume) :
    ∀ x : ℝ, 0 < x → ContinuousAt f x →
      ContinuousAt (reflectedTheta k ε g) x →
      f x = reflectedTheta k ε g x := by
  have hmellin : mellin f = mellin (reflectedTheta k ε g) := by
    funext z
    have h₁ := hFE (k - z)
    have h₂ := mellin_reflectedTheta k ε g (k - z)
    rw [show (k : ℂ) - ((k : ℂ) - z) = z by ring] at h₁ h₂
    exact h₁.trans h₂.symm
  exact eqOn_pos_of_mellin_eq sigma f (reflectedTheta k ε g)
    hfConv hrefConv hfVert hrefVert hmellin

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.mellin_reflectedTheta
#print axioms CriticalLinePhasor.ThreeDConverse.eqOn_pos_of_mellin_eq
#print axioms CriticalLinePhasor.ThreeDConverse.theta_reflection_of_mellin_functionalEquation
