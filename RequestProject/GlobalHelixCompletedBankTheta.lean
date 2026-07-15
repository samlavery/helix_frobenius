import RequestProject.GlobalHelixClockReflection
import RequestProject.GlobalHelixLogReadout

/-!
# Finite completed-bank theta reflection from the global 3D carrier

The finite bank is first read on the centered coordinate of the 3D carrier.  The global involution
then becomes reciprocal multiplicative height, and the self-dual envelope contributes the exact
Riemann--Hecke power.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.StrandExchange

/-- The completed finite bank, read at the centered 3D coordinate, obeys the weld phase supplied by
the global helix/anti-helix exchange. -/
theorem completedBank_centered_globalHelixInvolution
    {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (f : Fiber) :
    (starRingEnd ℂ)
        (completedBank S α ℓ β ℓ₀ (centeredReadout (globalHelixInvolution f))) =
      ((∏ i ∈ S, (-(starRingEnd ℂ) (α i))) * ((starRingEnd ℂ) β) ^ 2) *
        completedBank S α ℓ β ℓ₀ (centeredReadout f) := by
  rw [centeredReadout_globalHelixInvolution_conj]
  exact completedBank_star S α hα ℓ β hβ ℓ₀ (centeredReadout f)

/-- The finite completed-bank logarithmic theta obeys the weighted reflection directly on the
global 3D carrier. -/
theorem completedBankStage_theta_globalHelixInvolution
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ k : ℝ) (n : ℕ) (f : Fiber) :
    completedLogTheta (completedBankStage α ℓ β ℓ₀ n) k
        (multiplicativeHeight (globalHelixInvolution f)) =
      ((starRingEnd ℂ) (completedBankStageExchangeConstant α β n) *
          ((multiplicativeHeight f) ^ k : ℝ)) •
        completedLogThetaDual (completedBankStage α ℓ β ℓ₀ n) k
          (multiplicativeHeight f) := by
  rw [multiplicativeHeight_globalHelixInvolution]
  exact completedBankStage_logTheta_one_div α hα ℓ β hβ ℓ₀ k n
    (multiplicativeHeight_pos f)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.completedBank_centered_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.completedBankStage_theta_globalHelixInvolution
