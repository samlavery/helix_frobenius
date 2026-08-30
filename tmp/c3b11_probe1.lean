import Mathlib
open MeasureTheory

example (f : ℝ → ℝ) : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (-1)
  simp only [smul_eq_mul, neg_one_mul] at h
  norm_num at h
  exact h
