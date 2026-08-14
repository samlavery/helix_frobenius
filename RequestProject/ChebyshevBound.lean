import RequestProject.ChebyshevCosSum

/-!
# The Chebyshev character is bounded by its rank

The rounding estimate `rounded_average_bound` needs a uniform bound `B` on the values being
averaged.  For the Sato--Tate character that bound is immediate from the cosine-sum identity: a sum
of `r + 1` cosines cannot exceed `r + 1`.

  **`|U_r(cos θ)| ≤ r + 1`.**

No analysis — the identity `chebyshevU_cos_eq_cosSum` already exhibits `U_r(cos θ)` as a sum of
exactly `r + 1` terms of modulus at most one, and the bound is attained at `θ = 0`.

This is the last input the single-block estimate needs: node count `n`, budget `L`, and `B = r+1`.
-/

open Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.ThreeDConverse

/-- **The cosine sum is bounded by its length.** -/
theorem abs_chebyshevCosSum_le (r : ℕ) (θ : ℝ) :
    |chebyshevCosSum r θ| ≤ (r : ℝ) + 1 := by
  calc |chebyshevCosSum r θ|
      ≤ ∑ j ∈ Finset.range (r + 1), |Real.cos (((r : ℝ) - 2 * (j : ℝ)) * θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (r + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => Real.abs_cos_le_one _
    _ = (r : ℝ) + 1 := by simp

/-- **The Chebyshev character is bounded by its rank.**  This is the `B` of the rounding
estimate. -/
theorem abs_chebyshevU_cos_le (r : ℕ) (θ : ℝ) :
    |(U ℝ (r : ℤ)).eval (Real.cos θ)| ≤ (r : ℝ) + 1 := by
  rw [chebyshevU_cos_eq_cosSum]
  exact abs_chebyshevCosSum_le r θ

/-- The bound is attained: at `θ = 0` the character equals `r + 1`. -/
theorem chebyshevU_cos_zero (r : ℕ) :
    (U ℝ (r : ℤ)).eval (Real.cos 0) = (r : ℝ) + 1 := by
  rw [chebyshevU_cos_eq_cosSum, chebyshevCosSum]
  simp

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.abs_chebyshevU_cos_le
