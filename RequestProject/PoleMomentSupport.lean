import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The pole moments are a SUPPORT condition, not a constraint

RH_LEDGER 736 (2026-09-13), verified numerically to five significant figures; this file compiles the
computation it rests on.

Weil's functional in the Bombieri–Connes form is taken on test functions `G` supported in `[-a, a]`
with the two pole moments `P± = ∫ G(u) e^{±u/2} du` vanishing.  That looks like a codimension-two
linear constraint.  It is not: putting `h = e^{-|·|/2} ⋆ G`, one has for `u > a`

  `h(u) = ∫_{-a}^{a} e^{-(u-v)/2} G(v) dv = e^{-u/2} · ∫_{-a}^{a} e^{v/2} G(v) dv = e^{-u/2} · P₊`,

because `u - v > 0` for every `v` in the support.  So `P₊ = 0` says exactly that `h` vanishes to the
right of the support, and symmetrically for `P₋` on the left.  **The constraint is the statement
that `G`'s own resolvent transform is compactly supported.**

* `exp_conv_far_right` — the factorisation above, for `u` to the right of the support;
* `exp_conv_far_left` — its mirror;
* `exp_conv_far_right_eq_zero` / `exp_conv_far_left_eq_zero` — the pole moment vanishes iff the
  transform does, at every point beyond the support.
-/

namespace CriticalLinePhasor.PoleMomentSupport

open MeasureTheory Set

/-- To the RIGHT of the support the kernel factorises: `|u - v| = u - v` there. -/
theorem exp_conv_far_right {a u : ℝ} (hu : a < u) (G : ℝ → ℝ) :
    (∫ v in Icc (-a) a, Real.exp (-|u - v| / 2) * G v)
      = Real.exp (-u / 2) * ∫ v in Icc (-a) a, Real.exp (v / 2) * G v := by
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro v hv
  have hvu : v < u := lt_of_le_of_lt hv.2 hu
  have habs : |u - v| = u - v := abs_of_pos (by linarith)
  have hsplit : Real.exp (-(u - v) / 2) = Real.exp (-u / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add]; ring_nf
  simp only [habs, hsplit, mul_assoc]

/-- To the LEFT of the support, the mirror statement. -/
theorem exp_conv_far_left {a u : ℝ} (hu : u < -a) (G : ℝ → ℝ) :
    (∫ v in Icc (-a) a, Real.exp (-|u - v| / 2) * G v)
      = Real.exp (u / 2) * ∫ v in Icc (-a) a, Real.exp (-v / 2) * G v := by
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro v hv
  have hvu : u < v := lt_of_lt_of_le hu hv.1
  have habs : |u - v| = -(u - v) := abs_of_neg (by linarith)
  have hsplit : Real.exp (- -(u - v) / 2) = Real.exp (u / 2) * Real.exp (-v / 2) := by
    rw [← Real.exp_add]; ring_nf
  simp only [habs, hsplit, mul_assoc]

/-- **`P₊ = 0` exactly when the transform vanishes to the right of the support.** -/
theorem exp_conv_far_right_eq_zero {a u : ℝ} (hu : a < u) (G : ℝ → ℝ) :
    (∫ v in Icc (-a) a, Real.exp (-|u - v| / 2) * G v) = 0
      ↔ (∫ v in Icc (-a) a, Real.exp (v / 2) * G v) = 0 := by
  rw [exp_conv_far_right hu G, mul_eq_zero]
  simp [Real.exp_ne_zero]

/-- **`P₋ = 0` exactly when the transform vanishes to the left of the support.** -/
theorem exp_conv_far_left_eq_zero {a u : ℝ} (hu : u < -a) (G : ℝ → ℝ) :
    (∫ v in Icc (-a) a, Real.exp (-|u - v| / 2) * G v) = 0
      ↔ (∫ v in Icc (-a) a, Real.exp (-v / 2) * G v) = 0 := by
  rw [exp_conv_far_left hu G, mul_eq_zero]
  simp [Real.exp_ne_zero]

end CriticalLinePhasor.PoleMomentSupport

#print axioms CriticalLinePhasor.PoleMomentSupport.exp_conv_far_right
#print axioms CriticalLinePhasor.PoleMomentSupport.exp_conv_far_left
#print axioms CriticalLinePhasor.PoleMomentSupport.exp_conv_far_right_eq_zero
#print axioms CriticalLinePhasor.PoleMomentSupport.exp_conv_far_left_eq_zero
