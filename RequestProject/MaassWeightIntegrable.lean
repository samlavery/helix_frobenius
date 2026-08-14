import RequestProject.MaassGDecay

/-!
# The Route B weight is integrable over the fundamental domain

The second missing piece of Route B (the first being the averaging itself).  `GDecay`'s docstring
asserts `weight_integrableOn_fd` but the file does not contain it; here it is.

The weight is `wt C₁ y = (1 + C₁y²)·e^{-πy}`, and it is bounded on the **whole** positive ray, not
just on `𝒟`: `e^{-πy} ≤ 1` and `y²·e^{-πy} ≤ 1`, the latter because `y ≤ e^y` gives `y² ≤ e^{2y}`
and `π > 2`.  So `wt C₁ y ≤ 1 + C₁` outright — no property of `𝒟` is used for the bound, only for
the finiteness of the measure it is integrated against (`volume_fd_lt_top`).

Both facts are exact, not estimates: the exponential dominates the polynomial because `2 < π`, and
that comparison is the object's own scale.
-/

open MeasureTheory UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

/-- `y²·e^{-πy} ≤ 1` on the positive ray: `y ≤ e^y` twice, and `π > 2`. -/
lemma sq_mul_exp_neg_pi_le_one {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 * Real.exp (-Real.pi * y) ≤ 1 := by
  have h1 : y ≤ Real.exp y := le_trans (by linarith) (Real.add_one_le_exp y)
  have h2 : y ^ 2 ≤ Real.exp y ^ 2 := pow_le_pow_left₀ hy h1 2
  have h3 : Real.exp y ^ 2 = Real.exp (2 * y) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3] at h2
  have h4 : y ^ 2 * Real.exp (-Real.pi * y) ≤
      Real.exp (2 * y) * Real.exp (-Real.pi * y) :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  rw [← Real.exp_add] at h4
  refine le_trans h4 ?_
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])

/-- The Route B weight is bounded on the whole positive ray. -/
lemma wt_le {C₁ : ℝ} (hC₁ : 0 ≤ C₁) {y : ℝ} (hy : 0 ≤ y) :
    wt C₁ y ≤ 1 + C₁ := by
  have hexp1 : Real.exp (-Real.pi * y) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hsq := sq_mul_exp_neg_pi_le_one hy
  have hexpnn : (0:ℝ) < Real.exp (-Real.pi * y) := Real.exp_pos _
  rw [wt]
  calc (1 + C₁ * y ^ 2) * Real.exp (-Real.pi * y)
      = Real.exp (-Real.pi * y) + C₁ * (y ^ 2 * Real.exp (-Real.pi * y)) := by ring
    _ ≤ 1 + C₁ * 1 := by
        refine add_le_add hexp1 ?_
        exact mul_le_mul_of_nonneg_left hsq hC₁
    _ = 1 + C₁ := by ring

/-- The weight is nonnegative. -/
lemma wt_nonneg {C₁ : ℝ} (hC₁ : 0 ≤ C₁) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ wt C₁ y := by
  rw [wt]
  have : (0:ℝ) ≤ 1 + C₁ * y ^ 2 := by positivity
  positivity

/-- **The Route B weight is integrable over `𝒟`.**  Bounded on the ray, against a finite
measure. -/
theorem weight_integrableOn_fd {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    IntegrableOn (fun z : ℍ => wt C₁ z.im) ModularGroup.fd volume := by
  refine integrableOn_fd_of_bounded (continuous_wt C₁) (C := 1 + C₁) fun z _ => ?_
  have hy : (0:ℝ) ≤ z.im := z.im_pos.le
  rw [Real.norm_of_nonneg (wt_nonneg hC₁ hy)]
  exact wt_le hC₁ hy

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.sq_mul_exp_neg_pi_le_one
#print axioms CriticalLinePhasor.Unfolding.wt_le
#print axioms CriticalLinePhasor.Unfolding.weight_integrableOn_fd
