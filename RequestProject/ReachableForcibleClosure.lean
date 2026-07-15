import RequestProject.CarrierReachability
import RequestProject.ForcibleClosure

/-!
# Reachable forcible cell closure

The complete dual carrier supplies a height with two independent lane directions.  At that height,
the two real correction coordinates close an arbitrary complex cell residual.
-/

open Complex

namespace CriticalLinePhasor

/-- A continuous nonconstant dual-lane phase supplies a stage and two real correction weights closing
any prescribed complex residual. -/
theorem reachable_residual_forcible {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hnc : ¬ ∀ x, φ x = φ 0) (D : ℂ) :
    ∃ y s t : ℝ,
      D + (s • Complex.exp (↑(φ y) * I) + t • Complex.exp (-↑(φ y) * I)) = 0 := by
  obtain ⟨y, hy⟩ := CarrierReachability.reachable_independent_stage hφ hnc
  obtain ⟨s, t, hst⟩ := ForcibleClosure.residual_forcible hy D
  exact ⟨y, s, t, hst⟩

end CriticalLinePhasor

#print axioms CriticalLinePhasor.reachable_residual_forcible
