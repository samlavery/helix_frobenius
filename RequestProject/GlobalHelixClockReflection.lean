import RequestProject.GlobalHelixIntertwiner
import RequestProject.StrandExchange

/-!
# Clock reflection read from the global 3D involution

The global double-helix symmetry is applied before the clock.  Its strip readout is conjugation,
so the existing clock weld and its finite-bank products become direct readouts of the 3D symmetry.
-/

open Complex CriticalLinePhasor.ChiralityHB
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.StrandExchange

/-- A single clock reads the global 3D helix/anti-helix exchange as its weld identity. -/
theorem symClock_globalHelixInvolution {α : ℂ} (hα : ‖α‖ = 1)
    (ℓ : ℝ) (f : Fiber) :
    (starRingEnd ℂ) (symClock α ℓ (stripReadout (globalHelixInvolution f))) =
      -((starRingEnd ℂ) α) * symClock α ℓ (stripReadout f) := by
  rw [stripReadout_globalHelixInvolution_conj]
  exact symClock_star hα ℓ (stripReadout f)

/-- A finite clock bank reads the same global 3D exchange with the product weld phase. -/
theorem bankProduct_globalHelixInvolution
    {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ) (f : Fiber) :
    (starRingEnd ℂ)
        (bankProduct S α ℓ (stripReadout (globalHelixInvolution f))) =
      (∏ i ∈ S, (-(starRingEnd ℂ) (α i))) *
        bankProduct S α ℓ (stripReadout f) := by
  rw [stripReadout_globalHelixInvolution_conj]
  exact bankProduct_star S α hα ℓ (stripReadout f)

/-- The completed finite bank reads the 3D exchange, including the archimedean clock phase. -/
theorem completedBank_globalHelixInvolution
    {ι : Type*} (S : Finset ι) (α : ι → ℂ)
    (hα : ∀ i ∈ S, ‖α i‖ = 1) (ℓ : ι → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) (f : Fiber) :
    (starRingEnd ℂ)
        (completedBank S α ℓ β ℓ₀ (stripReadout (globalHelixInvolution f))) =
      ((∏ i ∈ S, (-(starRingEnd ℂ) (α i))) * ((starRingEnd ℂ) β) ^ 2) *
        completedBank S α ℓ β ℓ₀ (stripReadout f) := by
  rw [stripReadout_globalHelixInvolution_conj]
  exact completedBank_star S α hα ℓ β hβ ℓ₀ (stripReadout f)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.symClock_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.bankProduct_globalHelixInvolution
#print axioms CriticalLinePhasor.GlobalHelix.completedBank_globalHelixInvolution
