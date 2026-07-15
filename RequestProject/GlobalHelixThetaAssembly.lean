import RequestProject.GlobalHelixThetaTerms
import RequestProject.CarrierThetaIdentification

/-!
# Full theta assembly on the sheared anti-helix

The reciprocal-height coefficient theta is exactly the sum of the unchanged fixed kernel read on
the index-sheared global anti-helix points.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta

/-- The full reciprocal-height theta is the global anti-helix sum with its exact index ledger. -/
theorem theta_one_div_as_sheared_globalHelix
    (a : ℕ → ℂ) (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    theta a g (1 / x) =
      ∑' n : ℕ, a n * g (multiplicativeHeight (reciprocalThetaTermPoint n x)) := by
  unfold theta
  apply tsum_congr
  intro n
  rw [show ((n + 1 : ℕ) : ℝ) * (1 / x) = ((n + 1 : ℕ) : ℝ) / x by ring]
  rw [kernel_reciprocal_term_as_globalHelix g n hx]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.theta_one_div_as_sheared_globalHelix
