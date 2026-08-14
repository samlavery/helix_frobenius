import RequestProject.MaassStripIntegrable
import RequestProject.CuspAmplitude

/-!
# The Maass Petersson density decays like `e^{-2πy}` on the fundamental domain

The single input Route B (`GDecay`) needs from the form.  Its `ptwise_bound` consumes
`P_exp_decay_on_fd` — the density's exponential decay on `𝒟` — and everything else in that argument
(the theta tail bound, `cz_ge_on_fd`, the AM-GM saddle) is form-independent.

For a Maass form the decay is already proved: `maassWave_decay_above` gives
`‖u‖ ≤ B·√y·e^{-2πy}`, so `‖u‖² ≤ B²·y·e^{-4πy}`, and `y·e^{-2πy} ≤ 1` on the whole positive ray
(because `y ≤ e^y` and `2π > 1`).  Hence

  **`maassP M z ≤ B²·e^{-2πy}`  on `𝒟`,**

which is the same shape as the holomorphic case and in fact came from a stronger estimate — the
Maass density decays like `e^{-4πy}` before the weight is discarded.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- `y·e^{-2πy} ≤ 1` on the positive ray: the exponential dominates the linear factor. -/
lemma im_mul_exp_neg_le_one {y : ℝ} (hy : 0 ≤ y) :
    y * Real.exp (-(2 * Real.pi * y)) ≤ 1 := by
  have h1 : y ≤ Real.exp y := le_trans (by linarith) (Real.add_one_le_exp y)
  have h2 : y * Real.exp (-(2 * Real.pi * y)) ≤
      Real.exp y * Real.exp (-(2 * Real.pi * y)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rw [← Real.exp_add] at h2
  refine le_trans h2 ?_
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])

/-- **The Maass Petersson density decays exponentially on `𝒟`** — the one form-dependent input of
Route B. -/
theorem maassP_exp_decay_on_fd (M : GenuineMaassCuspForm3D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ModularGroup.fd,
      maassP M z ≤ C * Real.exp (-(2 * Real.pi) * z.im) := by
  have ha : (0:ℝ) < Real.sqrt 3 / 2 := by
    have : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  obtain ⟨B, hB0, hB⟩ := maassWave_decay_above M ha
  refine ⟨B ^ 2, by positivity, fun z hz => ?_⟩
  have hy : Real.sqrt 3 / 2 ≤ z.im := CriticalLinePhasor.HeckeSupBound.fd_im_ge hz
  have hy0 : (0:ℝ) < z.im := z.im_pos
  have hb := hB (z : ℂ).re z.im hy
  rw [← maassWave_eq_coords M z] at hb
  have hsq : maassP M z ≤
      (B * Real.sqrt z.im * Real.exp (-(2 * Real.pi * z.im))) ^ 2 := by
    unfold maassP
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hval : (B * Real.sqrt z.im * Real.exp (-(2 * Real.pi * z.im))) ^ 2 =
      B ^ 2 * (z.im * Real.exp (-(2 * Real.pi * z.im))) *
        Real.exp (-(2 * Real.pi) * z.im) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hy0.le, ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * -(2 * Real.pi * z.im) =
      -(2 * Real.pi * z.im) + -(2 * Real.pi) * z.im by push_cast; ring, Real.exp_add]
    ring
  rw [hval] at hsq
  refine le_trans hsq ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  calc B ^ 2 * (z.im * Real.exp (-(2 * Real.pi * z.im)))
      ≤ B ^ 2 * 1 := mul_le_mul_of_nonneg_left (im_mul_exp_neg_le_one hy0.le) (by positivity)
    _ = B ^ 2 := mul_one _

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.im_mul_exp_neg_le_one
#print axioms CriticalLinePhasor.Unfolding.maassP_exp_decay_on_fd
