import RequestProject.XiIntegralIdentification
import RequestProject.XiChannelReceiver

/-!
# The theta integral in the HP receiver chart

The chart is `s = 1/2 + iz`. The compiled identity `F(z) = 2 ξ(s)` gives
`F'(z) = 2i ξ'(s)` and hence the receiver identity `-ξ'/ξ(s) = i F'/F(z)`.
The factor two cancels even at zeros, using Lean's total quotient convention.

Searches before construction:
`rg -n 'xiChannel.*logDeriv|logDeriv.*xiChannel|xiIntegral.*riemannXi|xiIntegral.*logDeriv|cosine.*receiver|receiver.*cosine' RequestProject --glob '*.lean'`
`rg -n 'logDeriv_const_mul|logDeriv_comp|deriv_const_mul|HasDerivAt.*const_mul|logDeriv_apply' .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'`

Expectation-free step: differentiate the established function identity.
Strategy A: `rw [logDeriv_apply]`, then use the product and chain rules.
Strategy B: `rw [logDeriv_comp]`, then cancel the nonzero scalar factor.
Strategy A below also handles the total quotient at zeros directly.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.XiKernelBridge

open CriticalLinePhasor.ThetaWronskianSuzukiGram

theorem xiIntegral_hasDerivAt (z : ℂ) :
    HasDerivAt xiIntegral (2 * (deriv ZD.riemannXi (1 / 2 + Complex.I * z) * Complex.I)) z := by
  have hchart : HasDerivAt (fun w : ℂ => 1 / 2 + Complex.I * w) Complex.I z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul Complex.I).const_add (1 / 2)
  have h := (((ZD.riemannXi_differentiable (1 / 2 + Complex.I * z)).hasDerivAt).comp z
    hchart).const_mul 2
  have heq : xiIntegral = fun w => 2 * ZD.riemannXi (1 / 2 + Complex.I * w) :=
    funext xiIntegral_eq_two_mul_riemannXi
  rw [heq]
  exact h

theorem xiChannel_eq_cosine_logDeriv (z : ℂ) :
    CriticalLinePhasor.XiChannel.xiChannel z = Complex.I * logDeriv xiIntegral z := by
  have halg (a b : ℂ) : -(a / b) = Complex.I * (2 * (a * Complex.I) / (2 * b)) := by
    by_cases hb : b = 0
    · simp [hb]
    · field_simp
      linear_combination -a * Complex.I_sq
  rw [CriticalLinePhasor.XiChannel.xiChannel, logDeriv_apply, logDeriv_apply,
    (xiIntegral_hasDerivAt z).deriv, xiIntegral_eq_two_mul_riemannXi]
  exact halg _ _

theorem cosine_annihilation_of_nontrivialZero {rho : ℂ} (hrho : rho ∈ ZD.NontrivialZeros) :
    ∫ u in Set.Ioi (0 : ℝ), (riemannXiKernel u : ℂ) *
      Complex.cos (xiFrequency rho * u) = 0 := by
  have hz := xiIntegral_half_eq_riemannXi (xiFrequency rho)
  rw [xiFrequency_chart, ZD.riemannXi_eq_zero_of_mem_NontrivialZeros rho hrho] at hz
  simpa [xiIntegral] using hz

end CriticalLinePhasor.XiKernelBridge

#print axioms CriticalLinePhasor.XiKernelBridge.xiIntegral_hasDerivAt
#print axioms CriticalLinePhasor.XiKernelBridge.xiChannel_eq_cosine_logDeriv
#print axioms CriticalLinePhasor.XiKernelBridge.cosine_annihilation_of_nontrivialZero
