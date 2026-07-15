import RequestProject.CarrierThetaStrongFE
import RequestProject.LogReadoutReflection

/-!
# Exact carrier-to-coefficient-theta coupling

This module transports the completed carrier exchange through pointwise primal and dual readout
identifications.  It isolates the remaining construction as equalities of functions on the positive
half-line, while producing exactly the reflection hypothesis consumed by the coefficient-theta
strong functional-equation theorem.
-/

open Complex Set

namespace CriticalLinePhasor.CarrierTheta

open CriticalLinePhasor.StrandExchange

/-- The one-site coefficient bank, used to verify the direct carrier-to-theta realization without
any convergence hypothesis. -/
def carrierDelta : ℕ → ℂ := fun n => if n = 0 then 1 else 0

/-- A one-site coefficient theta is definitionally the supplied carrier kernel. -/
theorem theta_carrierDelta (g : ℝ → ℂ) (x : ℝ) : theta carrierDelta g x = g x := by
  rw [theta, tsum_eq_single 0]
  · simp [carrierDelta]
  · intro n hn
    simp [carrierDelta, hn]

/-- The Dirichlet readout of the one-site bank is the unit function. -/
theorem dirichlet_carrierDelta (s : ℂ) : dirichlet carrierDelta s = 1 := by
  rw [dirichlet, tsum_eq_single 0]
  · simp [carrierDelta]
  · intro n hn
    simp [carrierDelta, hn]

/-- Pointwise primal and dual carrier readout identifications transport the carrier exchange law to
the coefficient-assembled theta pair. -/
theorem coefficientTheta_reflection_of_carrier_coupling
    (E : ℂ → ℂ) (ε : ℂ)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ)
    (a aDual : ℕ → ℂ) (g gDual : ℝ → ℂ)
    (hprimal : ∀ x ∈ Ioi (0 : ℝ), theta a g x = completedLogTheta E k x)
    (hdual : ∀ x ∈ Ioi (0 : ℝ), theta aDual gDual x = completedLogThetaDual E k x) :
    ∀ x ∈ Ioi (0 : ℝ),
      theta a g (1 / x) =
        ((starRingEnd ℂ) ε * (x ^ k : ℝ)) • theta aDual gDual x := by
  intro x hx
  have hxinv : 1 / x ∈ Ioi (0 : ℝ) := by
    simpa only [mem_Ioi] using one_div_pos.mpr hx
  calc
    theta a g (1 / x) = completedLogTheta E k (1 / x) := hprimal _ hxinv
    _ = ((starRingEnd ℂ) ε * (x ^ k : ℝ)) • completedLogThetaDual E k x :=
      completedLogTheta_one_div E ε hE k hx
    _ = ((starRingEnd ℂ) ε * (x ^ k : ℝ)) • theta aDual gDual x := by
      rw [hdual x hx]

/-- The completed logarithmic carrier and its dual are exact coefficient theta banks, with no
pointwise coupling assumptions: the one-site coefficient realizes each kernel directly. -/
theorem carrierDelta_reflection
    (E : ℂ → ℂ) (ε : ℂ)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) :
    ∀ x ∈ Ioi (0 : ℝ),
      theta carrierDelta (completedLogTheta E k) (1 / x) =
        ((starRingEnd ℂ) ε * (x ^ k : ℝ)) •
          theta carrierDelta (completedLogThetaDual E k) x := by
  intro x hx
  rw [theta_carrierDelta, theta_carrierDelta]
  exact completedLogTheta_one_div E ε hE k hx

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.coefficientTheta_reflection_of_carrier_coupling
#print axioms CriticalLinePhasor.CarrierTheta.theta_carrierDelta
#print axioms CriticalLinePhasor.CarrierTheta.dirichlet_carrierDelta
#print axioms CriticalLinePhasor.CarrierTheta.carrierDelta_reflection
