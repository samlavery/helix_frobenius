import RequestProject.XiIntegralIdentification
import RequestProject.SeatingStageDoor

/-!
# The explicit theta-stage mass and its limit

Unfolded statement: write F_U(z) = 2 integral_(0,U] K(u) cos(zu) du,
z(s) = -i(s - 1/2), and G_U(s) = F_U(z(s))/2. Then

  Re(G_U'(s)/G_U(s))/(Re(s)-1/2)
    = -Im(F_U'(z(s)) conjugate(F_U(z(s)))) /
        (|F_U(z(s))|^2 Im(z(s))).

The identity uses total division, including at zeros. For nonzero xi(s),
these masses converge to Re(xi'(s)/xi(s))/(Re(s)-1/2). Neither theorem
asserts a sign for that sequence or its limit.

Search commands before construction:
`rg -n 'xiStage.*logDeriv|xiArithmeticStage.*mass|stage_mass_tendsto|xiStage.*norm|div_im_eq_mul_conj_im_div' RequestProject --glob '*.lean'`
`rg -n 'div_re|div_im|normSq_div|normSq_nonneg|logDeriv_apply' .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'`
`rg -n 'theorem.*(mul_div|div_mul|div_div|div_neg|neg_div)' .lake/packages/mathlib/Mathlib/Algebra --glob '*.lean'`
LeanSearch: real part of logarithmic derivative Riemann xi positive critical strip.
Loogle: RiemannHypothesis; integral_mul.

Expectation-free step: cancel the common normalization before taking real parts.
Strategy A: `rw [logDeriv_apply, deriv_xiArithmeticStage, xiArithmeticStage]`.
Strategy B: `apply SeatingLedger.stage_mass_tendsto` for the limit clause.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiKernelBridge

open ThetaWronskianSuzukiGram

theorem xiArithmeticStage_mass_formula (U : ℝ) (s : ℂ) :
    (logDeriv (xiArithmeticStage U) s).re / (s.re - 1 / 2) =
      -(deriv (xiStage U) (xiFrequency s) *
          (starRingEnd ℂ) (xiStage U (xiFrequency s))).im /
        (Complex.normSq (xiStage U (xiFrequency s)) * (xiFrequency s).im) := by
  have halg (a b : ℂ) (t : ℝ) :
      (a * (-Complex.I) / 2 / (b / 2)).re / t =
        -(a * (starRingEnd ℂ) b).im / (Complex.normSq b * -t) := by
    have hquot : a * (-Complex.I) / 2 / (b / 2) = (a / b) * (-Complex.I) := by
      by_cases hb : b = 0
      · simp [hb]
      · field_simp
    rw [hquot]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re,
      Complex.I_im, mul_zero, neg_neg, mul_neg, mul_one, zero_sub,
      Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [logDeriv_apply, deriv_xiArithmeticStage, xiArithmeticStage]
  have him : (xiFrequency s).im = -(s.re - 1 / 2) := by
    simp [xiFrequency, Complex.mul_im, Complex.sub_re]
  rw [him]
  exact halg _ _ _

theorem xiArithmeticStage_mass_tendsto {s : ℂ} (hs : ZD.riemannXi s ≠ 0) :
    Tendsto (fun n : ℕ => (logDeriv (xiArithmeticStage n) s).re /
      (s.re - 1 / 2)) atTop (𝓝 (SeatingLedger.seatMass s)) :=
  SeatingLedger.stage_mass_tendsto hs (xiArithmeticStage_tendsto s)
    (deriv_xiArithmeticStage_tendsto s)

end CriticalLinePhasor.XiKernelBridge

#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_mass_formula
#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_mass_tendsto
