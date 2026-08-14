import RequestProject.MaassRankinIdentity

/-!
# The archimedean factor is positive, so the identity can be divided

`maass_rankinSelberg_identity` reads `Eisenstein pairing = ½·(Dirichlet series)·A(s)`.  To transfer
analytic information from the geometric side to the arithmetic one, `A(s)` has to be nonzero — and
at real exponents that is not an estimate but a positivity statement, which the corpus's
`radialKernel_norm_pos` already supplies past a height.

The integrand `t^{σ-1}‖K(t)‖²` is nonnegative on the whole ray and *strictly* positive on
`(y₁,∞)`, a set of infinite measure, so the integral is positive outright.  No lower bound on the
kernel is needed anywhere — only that it does not vanish identically, which is the normalization.

`archimedeanFactor_ofReal` then identifies the complex factor at a real exponent with this real
integral, so `archimedeanFactor M σ ≠ 0` on `σ > 1` and the identity can be solved for the
Rankin--Selberg series.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex Filter Function UpperHalfPlane ModularGroup
open scoped Real Topology MatrixGroups Pointwise NNReal

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

/-- **The archimedean factor is strictly positive at every real exponent above one.** -/
theorem archimedeanFactorReal_pos (M : GenuineMaassCuspForm3D) {σ : ℝ} (hσ : 1 < σ) :
    0 < archimedeanFactorReal M σ := by
  obtain ⟨y₁, hy₁, hpos⟩ := radialKernel_norm_pos M
  rw [archimedeanFactorReal]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_
    (archimedeanFactorReal_integrableOn M hσ)).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    exact mul_nonneg (Real.rpow_nonneg ht0.le _) (sq_nonneg _)
  · have hsub : Set.Ioi y₁ ⊆
        support (fun t : ℝ => t ^ (σ - 1) * ‖M.radialKernel t‖ ^ 2) ∩ Set.Ioi (0:ℝ) := by
      intro t ht
      have ht1 : y₁ < t := ht
      have ht0 : (0:ℝ) < t := lt_trans (lt_of_lt_of_le zero_lt_one hy₁) ht1
      refine ⟨?_, ht0⟩
      have hk := hpos t ht1.le
      have hval : (0:ℝ) < t ^ (σ - 1) * ‖M.radialKernel t‖ ^ 2 :=
        mul_pos (Real.rpow_pos_of_pos ht0 _) (pow_pos hk 2)
      exact ne_of_gt hval
    calc (0 : ENNReal) < ⊤ := ENNReal.zero_lt_top
      _ = volume (Set.Ioi y₁) := Real.volume_Ioi.symm
      _ ≤ _ := measure_mono hsub

/-- The complex archimedean factor at a real exponent is the real integral. -/
theorem archimedeanFactor_ofReal (M : GenuineMaassCuspForm3D) (σ : ℝ) :
    archimedeanFactor M (σ : ℂ) = ((archimedeanFactorReal M σ : ℝ) : ℂ) := by
  rw [archimedeanFactor, mellin, archimedeanFactorReal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht0.le]
  congr 2
  push_cast
  ring

/-- **The archimedean factor does not vanish** on the real ray above one — so the Rankin--Selberg
identity can be divided by it. -/
theorem archimedeanFactor_ne_zero (M : GenuineMaassCuspForm3D) {σ : ℝ} (hσ : 1 < σ) :
    archimedeanFactor M (σ : ℂ) ≠ 0 := by
  rw [archimedeanFactor_ofReal]
  exact_mod_cast (archimedeanFactorReal_pos M hσ).ne'

end CriticalLinePhasor.ThreeDConverse

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The Rankin--Selberg series, solved for.**  At real exponents the identity determines the
arithmetic series from the Eisenstein pairing, unconditionally. -/
theorem maass_rankinSeries_eq_pairing (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    (∑' n : ℕ, rankinSelbergTerm M (σ : ℂ) n) =
      2 * (∑' q : CosetQ, ∫ z in ModularGroup.fd,
          (maassP M z : ℂ) * (((rep q • z).im : ℝ) : ℂ) ^ (σ : ℂ)
          ∂(volume : Measure ℍ)) / archimedeanFactor M (σ : ℂ) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hσ1 : 1 < σ := by linarith
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hne : archimedeanFactor M (σ : ℂ) ≠ 0 := archimedeanFactor_ne_zero M hσ1
  have hid := maass_rankinSelberg_identity M (s := (σ : ℂ)) (by rw [hre]; exact hσ)
  rw [hid]
  field_simp

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactorReal_pos
#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactor_ofReal
#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactor_ne_zero
#print axioms CriticalLinePhasor.Unfolding.maass_rankinSeries_eq_pairing
