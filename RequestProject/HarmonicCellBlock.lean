import RequestProject.ChebyshevCosSum

/-!
# The maximal exact Sato--Tate block sits on the harmonic cell

`satoTate_quadrature` makes the Sato--Tate integral an exact finite node sum, with node weights
`1 − x_i² = sin²θ_i`.  Turning that into an **equal-weight** family — what the corpus's prime
average actually consumes — requires the weight ratios to be rational.

They are, for `n = 1, 2, 3` only.  Measured (`tmp`, this session): the ratios are `1`, `(1,1)`,
`(1,4,1)`, then `(1, 3+2√2, 3+2√2, 1)` at `n = 4` and irrational onwards — which is Niven's theorem
(the only rational cosines of rational multiples of `π` are `0, ±1/2, ±1`).

So the **maximal exact block** is `n = 3`, and its nodes are
`cos(π/6), cos(π/2), cos(5π/6)` with multiplicities `1 : 4 : 1` — six equal-weight angles, all on
the `π/6` harmonic cell.  This file compiles its cancellation:

  **`U_r(cos π/6) + 4·U_r(cos π/2) + U_r(cos 5π/6) = 0`  for `r = 1, 2, 3`.**

Rank `4` genuinely fails (the sum is `6`), exactly as the degree bound `r + 2 < 2n = 6` predicts.

**What this is.**  The first concrete positive control for the cancellation machinery in this
campaign: an explicit finite equal-weight family on which the Sato--Tate character average is
*exactly* zero at every rank it reaches.

**What this is not.**  It is not a witness — it stops at rank `3`, and by Niven no exact rational
block reaches further.  Beyond rank `3` the multiplicities must be rounded, which is where the
remaining asymptotic work lives.  Nothing here concerns any arithmetic family.
-/

open Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.ThreeDConverse

private lemma cos_five_pi_div_six : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := by
  rw [show (5 * Real.pi / 6) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_six]

/-- **The harmonic-cell block cancels every rank it reaches.** -/
theorem harmonicCell_block_cancels {r : ℕ} (hr : 1 ≤ r) (hr3 : r ≤ 3) :
    chebyshevCosSum r (Real.pi / 6)
      + 4 * chebyshevCosSum r (Real.pi / 2)
      + chebyshevCosSum r (5 * Real.pi / 6) = 0 := by
  have h1 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have h2 : Real.cos (2 * (Real.pi / 6)) = 1 / 2 := by
    rw [show (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 by ring, Real.cos_pi_div_three]
  have h3 : Real.cos (3 * (Real.pi / 6)) = 0 := by
    rw [show (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  have k1 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have k2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
  have k3 : Real.cos (3 * (Real.pi / 2)) = 0 := by
    rw [show (3 : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi, k1]
    ring
  have m1 : Real.cos (5 * Real.pi / 6) = -(Real.sqrt 3 / 2) := cos_five_pi_div_six
  have m2 : Real.cos (2 * (5 * Real.pi / 6)) = 1 / 2 := by
    rw [show (2 : ℝ) * (5 * Real.pi / 6) = -(Real.pi / 3) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  have m3 : Real.cos (3 * (5 * Real.pi / 6)) = 0 := by
    rw [show (3 : ℝ) * (5 * Real.pi / 6) = Real.pi / 2 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, k1]
  interval_cases r <;>
    simp only [chebyshevCosSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;>
    push_cast <;>
    norm_num [Real.cos_neg, h1, h2, h3, k1, k2, k3, m1, m2, m3,
      show ((1 : ℝ) - 2 * 0) = 1 by ring] <;>
    ring

/-- The same statement on the Chebyshev side. -/
theorem harmonicCell_block_cancels_U {r : ℕ} (hr : 1 ≤ r) (hr3 : r ≤ 3) :
    (U ℝ (r : ℤ)).eval (Real.cos (Real.pi / 6))
      + 4 * (U ℝ (r : ℤ)).eval (Real.cos (Real.pi / 2))
      + (U ℝ (r : ℤ)).eval (Real.cos (5 * Real.pi / 6)) = 0 := by
  rw [chebyshevU_cos_eq_cosSum, chebyshevU_cos_eq_cosSum, chebyshevU_cos_eq_cosSum]
  exact harmonicCell_block_cancels hr hr3

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.harmonicCell_block_cancels_U
