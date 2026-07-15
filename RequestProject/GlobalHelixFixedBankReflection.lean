import RequestProject.GlobalHelixFixedCompletionKernel

/-!
# Fixed completion-bank reflection as a global 3D carrier equality

This file keeps the 3D source primary.  It defines the primal bank directly from coefficient fibers,
defines its transformed dual bank by applying the global involution followed by the exact index
ledger shear, and only then proves that their 1D projections are the two coefficient-theta readouts.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.CarrierTheta

/-- The global 3D bank before applying the helix involution. -/
noncomputable def fixedPrimalBankReadout
    (μ : List ℂ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber a n x) *
      fixedKernelReadout μ (coefficientFiber a n x)

/-- The global 3D dual bank after applying `J` and the exact index-ledger shear. -/
noncomputable def fixedTransformedDualBankReadout
    (μ : List ℂ) (aDual : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (reciprocalCoefficientFiber aDual n x) *
      fixedKernelReadout μ (reciprocalCoefficientFiber aDual n x)

/-- The 1D projection of the primal 3D bank is the fixed-kernel coefficient theta. -/
theorem fixedPrimalBankReadout_eq_theta
    (μ : List ℂ) (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    fixedPrimalBankReadout μ a x = theta a (completionKernel μ) x := by
  unfold fixedPrimalBankReadout theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber, fixedKernelReadout,
    multiplicativeHeight_coefficientFiber a n hx]

/-- When the dual ledger stores conjugate coefficients, the transformed 3D bank projects to the
primal theta at reciprocal external height. -/
theorem fixedTransformedConjugateDualBankReadout_eq_theta_one_div
    (μ : List ℂ) (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    fixedTransformedDualBankReadout μ (fun n => (starRingEnd ℂ) (a n)) x =
      theta a (completionKernel μ) (1 / x) := by
  symm
  exact fixedCompletionTheta_one_div_as_globalHelix μ a hx

/-- The weighted reflected dual bank on the 3D carrier. -/
noncomputable def weightedReflectedDualBankReadout
    (μ : List ℂ) (aDual : ℕ → ℂ) (η : ℂ) (κ : ℝ) (x : ℝ) : ℂ :=
  (η * (x ^ κ : ℝ)) • fixedTransformedDualBankReadout μ aDual x

/-- The 3D odd reflection channel: primal bank minus weighted transformed dual bank. -/
noncomputable def fixedBankOddChannel
    (μ : List ℂ) (a : ℕ → ℂ) (η : ℂ) (κ : ℝ) (x : ℝ) : ℂ :=
  fixedPrimalBankReadout μ a x -
    weightedReflectedDualBankReadout μ (fun n => (starRingEnd ℂ) (a n)) η κ x

/-- Vanishing of the global 3D odd channel is exactly the fixed-kernel theta reflection after the
ledgered 3D-to-1D projection. -/
theorem fixedBankOddChannel_eq_zero_iff_theta_reflection
    (μ : List ℂ) (a : ℕ → ℂ) (η : ℂ) (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    fixedBankOddChannel μ a η κ x = 0 ↔
      theta a (completionKernel μ) x =
        (η * (x ^ κ : ℝ)) • theta a (completionKernel μ) (1 / x) := by
  rw [fixedBankOddChannel, weightedReflectedDualBankReadout,
    fixedPrimalBankReadout_eq_theta μ a hx,
    fixedTransformedConjugateDualBankReadout_eq_theta_one_div μ a hx]
  exact sub_eq_zero

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.fixedPrimalBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.fixedTransformedConjugateDualBankReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.fixedBankOddChannel_eq_zero_iff_theta_reflection
