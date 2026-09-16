import RequestProject.FlowDerivFamily
import RequestProject.FlowLambdaLipschitz

/-!
# Reality and `λ`-Lipschitz for the derivative family
-/

open Complex MeasureTheory Filter Topology

namespace CriticalLinePhasor.XiKernel

/-- Schwarz reflection for every order. -/
theorem flowD_conj (k : ℕ) (lam : ℝ) (z : ℂ) :
    flowD k lam ((starRingEnd ℂ) z) = (starRingEnd ℂ) (flowD k lam z) := by
  unfold flowD flowDInt
  rw [← integral_conj]
  conv_rhs => rw [← MeasureTheory.integral_neg_eq_self]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [map_mul, map_pow, Complex.conj_ofReal, Kker_conj, ← Complex.exp_conj, Complex.conj_I,
    map_neg, Complex.ofReal_neg, neg_sq, Kker_even]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

theorem flowD_im_ofReal (k : ℕ) (lam : ℝ) (x : ℝ) : (flowD k lam (x : ℂ)).im = 0 := by
  have h := flowD_conj k lam (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im] at h2
  linarith

theorem norm_flowDInt (k : ℕ) (lam : ℝ) (z : ℂ) (u : ℝ) :
    ‖flowDInt k lam z u‖
      = |u| ^ k * Real.exp (lam * u ^ 2) * ‖Kker u‖ * ‖Complex.exp (I * z * u)‖ := by
  unfold flowDInt
  rw [norm_mul, norm_mul, norm_mul, norm_I_mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Pointwise `λ`-difference bound for the order-`k` integrand, via the order-`(k+2)` bound. -/
theorem flowDInt_lam_diff_bound {k : ℕ} {lam lam' lam₁ B M : ℝ} (hl : lam ≤ lam₁) (hl' : lam' ≤ lam₁)
    (hM : 0 ≤ M) (hB : ∀ v : ℝ, |v| ^ (k + 2) ≤ B * Real.exp |v|)
    (hK : ∀ u : ℝ, ‖Kker u‖ ≤ M * Dabs (1 / 2) (2 * Rc) u) {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a)
    (u : ℝ) :
    ‖flowDInt k lam z u - flowDInt k lam' z u‖
      ≤ |lam - lam'| * ((B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) := by
  have hdiff : |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)|
      ≤ |lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by
    refine (abs_exp_sub_exp_le _ _).trans ?_
    have habs : |lam * u ^ 2 - lam' * u ^ 2| = |lam - lam'| * u ^ 2 := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg u)]
    have hmax : Real.exp (max (lam * u ^ 2) (lam' * u ^ 2)) ≤ Real.exp (lam₁ * u ^ 2) := by
      refine Real.exp_le_exp.mpr (max_le ?_ ?_) <;>
        exact mul_le_mul_of_nonneg_right (by assumption) (sq_nonneg u)
    rw [habs]
    calc |lam - lam'| * u ^ 2 * Real.exp (max (lam * u ^ 2) (lam' * u ^ 2))
        ≤ |lam - lam'| * u ^ 2 * Real.exp (lam₁ * u ^ 2) :=
          mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = |lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)) := by ring
  have hfac : flowDInt k lam z u - flowDInt k lam' z u
      = (I * (u : ℂ)) ^ k * (((Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2) : ℝ)) : ℂ)
          * Kker u * Complex.exp (I * z * u) := by
    unfold flowDInt; push_cast [Complex.ofReal_sub]; ring
  rw [hfac, norm_mul, norm_mul, norm_mul, norm_I_mul_pow, Complex.norm_real, Real.norm_eq_abs]
  have hstep : |u| ^ k * |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)| * ‖Kker u‖
        * ‖Complex.exp (I * z * u)‖
      ≤ |lam - lam'| * (|u| ^ (k + 2) * Real.exp (lam₁ * u ^ 2) * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖) := by
    have h1 : |u| ^ k * |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)|
        ≤ |u| ^ k * (|lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2))) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    have hu2 : |u| ^ k * (|lam - lam'| * (u ^ 2 * Real.exp (lam₁ * u ^ 2)))
        = |lam - lam'| * (|u| ^ (k + 2) * Real.exp (lam₁ * u ^ 2)) := by
      rw [pow_add, ← sq_abs u]; ring
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (h1.trans_eq hu2) (norm_nonneg (Kker u)))
      (norm_nonneg (Complex.exp (I * z * u)))
    calc |u| ^ k * |Real.exp (lam * u ^ 2) - Real.exp (lam' * u ^ 2)| * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖
        ≤ |lam - lam'| * (|u| ^ (k + 2) * Real.exp (lam₁ * u ^ 2)) * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖ := h2
      _ = |lam - lam'| * (|u| ^ (k + 2) * Real.exp (lam₁ * u ^ 2) * ‖Kker u‖
          * ‖Complex.exp (I * z * u)‖) := by ring
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  have hnb := flowD_integrand_bound (k := k + 2) (lam := lam₁) (lam₁ := lam₁) le_rfl hM hB hK hz u
  rwa [norm_flowDInt] at hnb

/-- **`λ`-Lipschitz for `flowD k`, uniformly on `|Im z| ≤ a`.** -/
theorem flowD_lipschitz_lam (k : ℕ) {lam₁ : ℝ} (h1 : lam₁ ≤ 1) (h1' : 0 ≤ lam₁) {a : ℝ}
    (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam lam' : ℝ, 0 ≤ lam → 0 ≤ lam' → lam ≤ lam₁ → lam' ≤ lam₁ →
      ∀ z : ℂ, |z.im| ≤ a → ‖flowD k lam z - flowD k lam' z‖ ≤ |lam - lam'| * C := by
  obtain ⟨M, hM, hK⟩ := Kker_bound
  have hMnn : 0 ≤ M := by
    have := (norm_nonneg (Kker 0)).trans (hK 0)
    have hD : 0 < Dabs (1 / 2) (2 * Rc) 0 := by unfold Dabs Dprof; positivity
    nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ v : ℝ, |v| ^ (k + 2) ≤ B * Real.exp |v| :=
    ⟨(((k + 2).factorial : ℕ) : ℝ), abs_pow_le_factorial_exp (k + 2)⟩
  have hint : Integrable (fun u : ℝ => (B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) :=
    (integrable_Dq h1' h1 (by positivity) (by have := Rc_pos; positivity)).const_mul (B * M)
  refine ⟨∫ u : ℝ, (B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u, ?_, ?_⟩
  · refine integral_nonneg fun u => ?_
    have hBnn : 0 ≤ B := by
      have h0 := hB 1
      simp only [abs_one, one_pow] at h0
      nlinarith [Real.exp_pos (1:ℝ)]
    exact mul_nonneg (by positivity) (Dq_nonneg _ _ _ _)
  · intro lam lam' h0 h0' hl hl' z hz
    unfold flowD
    rw [← integral_sub (integrable_flowD_integrand k h0 (le_trans hl h1) z)
      (integrable_flowD_integrand k h0' (le_trans hl' h1) z)]
    calc ‖∫ u : ℝ, (flowDInt k lam z u - flowDInt k lam' z u)‖
        ≤ ∫ u : ℝ, |lam - lam'| * ((B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u) := by
          refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
          filter_upwards with u
          exact flowDInt_lam_diff_bound hl hl' hMnn hB hK hz u
      _ = |lam - lam'| * ∫ u : ℝ, (B * M) * Dq lam₁ (1 / 2 + (a + 1)) (2 * Rc) u := by
          rw [integral_const_mul]

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.flowD_im_ofReal
#print axioms CriticalLinePhasor.XiKernel.flowD_lipschitz_lam
