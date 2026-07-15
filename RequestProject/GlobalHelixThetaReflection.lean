import RequestProject.GlobalHelixIntertwiner

/-!
# Reciprocal-height reflection as global 3D equivariance

The multiplicative-height chart is onto the positive ray: `x > 0` is represented by the 3D point
with signed height `log x`.  Therefore a theta reciprocal-height law is exactly equivariance under
the global helix/anti-helix involution, not an additional 1D operation.
-/

open Complex Set

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- Every positive multiplicative height is represented by a concrete 3D carrier point. -/
theorem exists_multiplicativeHeight_eq {x : ℝ} (hx : 0 < x) :
    ∃ f : Fiber, multiplicativeHeight f = x := by
  refine ⟨(0, 0, Real.log x), ?_⟩
  simp [multiplicativeHeight, heightEncode, height, Real.exp_log hx]

/-- Reciprocal-height reflection is equivalent to equivariance of the readout under the global
3D double-helix involution. -/
theorem reciprocalHeight_iff_globalHelixInvolution
    (K KDual : ℝ → ℂ) (k : ℝ) (ε : ℂ) :
    (∀ x ∈ Ioi (0 : ℝ),
        K (1 / x) = (ε * (x ^ k : ℝ)) * KDual x) ↔
      (∀ f : Fiber,
        K (multiplicativeHeight (globalHelixInvolution f)) =
          (ε * ((multiplicativeHeight f) ^ k : ℝ)) *
            KDual (multiplicativeHeight f)) := by
  constructor
  · intro h f
    rw [multiplicativeHeight_globalHelixInvolution]
    exact h (multiplicativeHeight f) (multiplicativeHeight_pos f)
  · intro h x hx
    obtain ⟨f, hf⟩ := exists_multiplicativeHeight_eq hx
    have hJ := multiplicativeHeight_globalHelixInvolution f
    rw [hf] at hJ
    simpa [hf, hJ] using h f

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.exists_multiplicativeHeight_eq
#print axioms CriticalLinePhasor.GlobalHelix.reciprocalHeight_iff_globalHelixInvolution
