import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rounding exact weights to integer multiplicities

`satoTate_quadrature` makes the Sato--Tate integral an **exact** finite node sum, but with unequal
weights `w_i = sin²θ_i`.  The corpus's prime average is equal-weight, so the weights have to be
realised by repeating node `i` some integer number of times.  By Niven's theorem the ratios are
rational only for `n ≤ 3` (`HarmonicCellBlock`), so beyond rank `3` the multiplicities must be
rounded — and the whole remaining corpus-side gap is the arithmetic of that rounding.

This file compiles its heart.  Given weights `w` summing to `1` with `∑ wᵢ fᵢ = 0` exactly, take
multiplicities `mᵢ = ⌊L·wᵢ⌋`.  Then

* **the numerator barely moves** — `|∑ mᵢ fᵢ| ≤ n·B`, *independently of `L`*, because the exact
  vanishing kills the main term and only the `n` rounding residuals survive, each bounded by `1`;
* **the denominator is nearly `L`** — `L − n ≤ ∑ mᵢ`.

So the rounded equal-weight average is `≤ n·B/(L−n)`: a fixed node count `n` against a
multiplicity budget `L` we are free to grow.  That is the estimate a block construction needs, and
it is where the exactness of the quadrature pays off — an *approximate* quadrature would leave a
main term that no choice of `L` could suppress.

**Scope.**  This is the rounding estimate alone.  Assembling blocks into a single sequence, and
inhabiting the corpus's cancellation structure, are not done here.
-/

open Finset

namespace CriticalLinePhasor.ThreeDConverse

/-- Each rounding residual is bounded by `1`. -/
private lemma abs_floor_sub_le_one (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x - 1 < (⌊x⌋ : ℝ) := Int.sub_one_lt_floor x
  rw [abs_le]
  constructor <;> linarith

/-- **The numerator barely moves.**  Exact vanishing of the weighted sum leaves only the `n`
rounding residuals, so the bound does not grow with the multiplicity budget `L`. -/
theorem rounded_numerator_bound {n : ℕ} (w f : Fin n → ℝ) (L B : ℝ)
    (hzero : ∑ i, w i * f i = 0) (hB : ∀ i, |f i| ≤ B) :
    |∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) * f i| ≤ n * B := by
  have hsplit : ∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) * f i
      = ∑ i, (((⌊L * w i⌋ : ℤ) : ℝ) - L * w i) * f i := by
    have : ∑ i, (((⌊L * w i⌋ : ℤ) : ℝ) - L * w i) * f i
        = (∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) * f i) - L * ∑ i, w i * f i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hzero, mul_zero, sub_zero]
  rw [hsplit]
  calc |∑ i, (((⌊L * w i⌋ : ℤ) : ℝ) - L * w i) * f i|
      ≤ ∑ i, |(((⌊L * w i⌋ : ℤ) : ℝ) - L * w i) * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_floor_sub_le_one _) (hB i) (abs_nonneg _) zero_le_one
    _ = n * B := by simp [mul_comm]

/-- **The denominator is nearly the budget.** -/
theorem rounded_denominator_ge {n : ℕ} (w : Fin n → ℝ) (L : ℝ)
    (hsum : ∑ i, w i = 1) :
    L - n ≤ ∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) := by
  have hlow : ∀ i : Fin n, L * w i - 1 ≤ ((⌊L * w i⌋ : ℤ) : ℝ) := fun i =>
    le_of_lt (Int.sub_one_lt_floor _)
  calc L - n = (∑ i, L * w i) - ∑ _i : Fin n, (1 : ℝ) := by
        rw [← Finset.mul_sum, hsum, mul_one]; simp
    _ = ∑ i, (L * w i - 1) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) := Finset.sum_le_sum fun i _ => hlow i

/-- **The rounded equal-weight average is small.**  With `n` fixed and the budget `L` free, the
average of `f` over the multiset that repeats node `i` exactly `⌊L·wᵢ⌋ ` times is at most
`n·B/(L−n)`. -/
theorem rounded_average_bound {n : ℕ} (w f : Fin n → ℝ) (L B : ℝ)
    (hsum : ∑ i, w i = 1) (hzero : ∑ i, w i * f i = 0) (hB : ∀ i, |f i| ≤ B)
    (hL : (n : ℝ) < L) (hBnn : 0 ≤ B) :
    |∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) * f i| / (∑ i, ((⌊L * w i⌋ : ℤ) : ℝ))
      ≤ n * B / (L - n) := by
  have hden : L - (n : ℝ) ≤ ∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) := rounded_denominator_ge w L hsum
  have hdenpos : (0 : ℝ) < L - n := by linarith
  have hsumpos : (0:ℝ) < ∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) := lt_of_lt_of_le hdenpos hden
  have hnum := rounded_numerator_bound w f L B hzero hB
  have hnB : (0:ℝ) ≤ (n : ℝ) * B := by positivity
  calc |∑ i, ((⌊L * w i⌋ : ℤ) : ℝ) * f i| / (∑ i, ((⌊L * w i⌋ : ℤ) : ℝ))
      ≤ ((n : ℝ) * B) / (∑ i, ((⌊L * w i⌋ : ℤ) : ℝ)) := by
        exact (div_le_div_iff_of_pos_right hsumpos).mpr hnum
    _ ≤ ((n : ℝ) * B) / (L - n) := by
        gcongr

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.rounded_average_bound
