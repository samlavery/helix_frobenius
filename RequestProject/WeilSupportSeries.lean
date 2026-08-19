import Mathlib

/-!
# The Weil support series and its monotone floor

This file proves the elementary series facts behind the support certificate's
"Lemma C".  Everything here is a statement about the concrete real series

`weilB r n = (r²/4) / ((n + 1/4) · ((n + 1/4)² + r²/4))`,  `weilD r = ∑' n, weilB r n`,

indexed by `n : ℕ`.  The four structural facts proved are:

* each term is nonnegative (`weilB_nonneg`);
* each term decreases in the index `n` (`weilB_anti`);
* each term increases in the parameter `r` on `[0, ∞)` (`weilB_mono`);
* the series converges for every `r` (`weilB_summable`),

and the consequence that the sum itself is monotone in `r` on `[0, ∞)`
(`weilD_mono`).  The tail-bracket ingredient `weilB_le_bound` records the
comparison `weilB r n ≤ (r²/4) · ((n + 1/4)³)⁻¹`.

The two shape lemmas `denom_antitone` and `denom_mono_num` isolate the algebra:
writing `x = r²/4` and `y = n + 1/4 > 0`, the term is `x / (y³ + x·y)`, which
decreases when `y` grows and increases when `x` grows.  The second is the
cross-multiplied statement `x₁·(y³ + x₂·y) ≤ x₂·(y³ + x₁·y) ⟺ x₁·y³ ≤ x₂·y³`.

Convergence is by comparison with `16·r²·(n+1)⁻²`: the seat offset gives
`n + 1/4 ≥ (n+1)/4`, so `(n + 1/4)³ ≥ (n+1)³/64`.  The comparison is tight at
`n = 0`, where both sides equal `r²/4`.

Search record used before construction:

* repository: `rg -n "weilB|weilD" RequestProject/`
* Mathlib names checked at source before use: `div_le_div_iff₀`,
  `Summable.tsum_le_tsum`, `Real.summable_one_div_nat_pow`,
  `summable_nat_add_iff`, `Summable.of_nonneg_of_le`
-/

noncomputable section

namespace CriticalLinePhasor.WeilSupportSeries

/-! ## 1. The term and the sum -/

/-- The `n`-th term of the Weil support series at parameter `r`:
`(r²/4) / ((n + 1/4) · ((n + 1/4)² + r²/4))`. -/
def weilB (r : ℝ) (n : ℕ) : ℝ :=
  (r ^ 2 / 4) / (((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + r ^ 2 / 4))

/-- The Weil support sum `weilD r = ∑' n, weilB r n`. -/
def weilD (r : ℝ) : ℝ := ∑' n, weilB r n

/-! ## 2. Positivity of the denominator -/

/-- The denominator of `weilB r n` is strictly positive: the offset `1/4` keeps
`(n : ℝ) + 1/4` away from `0` even at `n = 0`. -/
lemma denom_pos (r : ℝ) (n : ℕ) :
    0 < ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + r ^ 2 / 4) := by
  have hy : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  have hz : (0 : ℝ) < ((n : ℝ) + 1 / 4) ^ 2 + r ^ 2 / 4 := by positivity
  exact mul_pos hy hz

/-! ## 3. The two shape lemmas -/

/-- For `x ≥ 0` the map `y ↦ x / (y · (y² + x))` is antitone on `(0, ∞)`. -/
lemma denom_antitone {x y₁ y₂ : ℝ} (hx : 0 ≤ x) (hy₁ : 0 < y₁) (h : y₁ ≤ y₂) :
    x / (y₂ * (y₂ ^ 2 + x)) ≤ x / (y₁ * (y₁ ^ 2 + x)) := by
  have hy₂ : 0 < y₂ := lt_of_lt_of_le hy₁ h
  have d₁ : 0 < y₁ * (y₁ ^ 2 + x) := by positivity
  have d₂ : 0 < y₂ * (y₂ ^ 2 + x) := by positivity
  have hcube : y₁ ^ 3 ≤ y₂ ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h)
      (by positivity : (0 : ℝ) ≤ y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)]
  have hmono : y₁ * (y₁ ^ 2 + x) ≤ y₂ * (y₂ ^ 2 + x) := by
    nlinarith [hcube, mul_le_mul_of_nonneg_left h hx]
  rw [div_le_div_iff₀ d₂ d₁]
  exact mul_le_mul_of_nonneg_left hmono hx

/-- For `y > 0` the map `x ↦ x / (y · (y² + x))` is monotone on `[0, ∞)`:
cross-multiplying, `x₁ · (y³ + x₂·y) ≤ x₂ · (y³ + x₁·y)` reduces to
`x₁ · y³ ≤ x₂ · y³`. -/
lemma denom_mono_num {x₁ x₂ y : ℝ} (hx₁ : 0 ≤ x₁) (h : x₁ ≤ x₂) (hy : 0 < y) :
    x₁ / (y * (y ^ 2 + x₁)) ≤ x₂ / (y * (y ^ 2 + x₂)) := by
  have hx₂ : 0 ≤ x₂ := le_trans hx₁ h
  have d₁ : 0 < y * (y ^ 2 + x₁) := by positivity
  have d₂ : 0 < y * (y ^ 2 + x₂) := by positivity
  have hcube : x₁ * y ^ 3 ≤ x₂ * y ^ 3 :=
    mul_le_mul_of_nonneg_right h (le_of_lt (pow_pos hy 3))
  rw [div_le_div_iff₀ d₁ d₂]
  nlinarith [hcube]

/-! ## 4. The four term facts -/

/-- Every term of the Weil support series is nonnegative. -/
theorem weilB_nonneg (r : ℝ) (n : ℕ) : 0 ≤ weilB r n := by
  unfold weilB
  exact div_nonneg (by positivity) (le_of_lt (denom_pos r n))

/-- The terms decrease in the index: `weilB r (n+1) ≤ weilB r n`. -/
theorem weilB_anti (r : ℝ) (n : ℕ) : weilB r (n + 1) ≤ weilB r n := by
  have h := denom_antitone (x := r ^ 2 / 4) (y₁ := (n : ℝ) + 1 / 4)
    (y₂ := ((n : ℝ) + 1) + 1 / 4) (by positivity) (by positivity) (by linarith)
  unfold weilB
  push_cast
  exact h

/-- The terms increase in the parameter on `[0, ∞)`. -/
theorem weilB_mono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h : r₁ ≤ r₂) (n : ℕ) :
    weilB r₁ n ≤ weilB r₂ n := by
  unfold weilB
  have hsq : r₁ ^ 2 / 4 ≤ r₂ ^ 2 / 4 := by nlinarith
  exact denom_mono_num (by positivity) hsq (by positivity)

/-- The tail-bracket comparison: dropping the `x·y` part of the denominator
gives `weilB r n ≤ (r²/4) · ((n + 1/4)³)⁻¹`. -/
theorem weilB_le_bound (r : ℝ) (n : ℕ) :
    weilB r n ≤ (r ^ 2 / 4) * (((n : ℝ) + 1 / 4) ^ 3)⁻¹ := by
  have hy : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  have hcube : (0 : ℝ) < ((n : ℝ) + 1 / 4) ^ 3 := by positivity
  have hden : ((n : ℝ) + 1 / 4) ^ 3
      ≤ ((n : ℝ) + 1 / 4) * (((n : ℝ) + 1 / 4) ^ 2 + r ^ 2 / 4) := by
    nlinarith [mul_nonneg hy.le (by positivity : (0 : ℝ) ≤ r ^ 2 / 4)]
  unfold weilB
  rw [← div_eq_mul_inv, div_le_div_iff₀ (denom_pos r n) hcube]
  exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- The Weil support series converges for every parameter. -/
theorem weilB_summable (r : ℝ) : Summable (weilB r) := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    have h : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h
    simpa using h2
  refine Summable.of_nonneg_of_le (fun n => weilB_nonneg r n) (fun n => ?_)
    (hbase.mul_left (16 * r ^ 2))
  have hcube : (0 : ℝ) < ((n : ℝ) + 1 / 4) ^ 3 := by positivity
  have hsq : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have ht : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have key : (r ^ 2 / 4) / (((n : ℝ) + 1 / 4) ^ 3)
      ≤ (16 * r ^ 2) / (((n : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ hcube hsq]
    nlinarith [mul_nonneg (sq_nonneg r)
      (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 3 + 47 / 4 * (n : ℝ) ^ 2 + 5 / 2 * (n : ℝ))]
  calc weilB r n ≤ (r ^ 2 / 4) * (((n : ℝ) + 1 / 4) ^ 3)⁻¹ := weilB_le_bound r n
    _ = (r ^ 2 / 4) / (((n : ℝ) + 1 / 4) ^ 3) := (div_eq_mul_inv _ _).symm
    _ ≤ (16 * r ^ 2) / (((n : ℝ) + 1) ^ 2) := key
    _ = 16 * r ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by rw [mul_one_div]

/-- The Weil support sum is monotone in the parameter on `[0, ∞)`. -/
theorem weilD_mono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h : r₁ ≤ r₂) : weilD r₁ ≤ weilD r₂ :=
  Summable.tsum_le_tsum (fun n => weilB_mono h0 h n) (weilB_summable r₁) (weilB_summable r₂)

end CriticalLinePhasor.WeilSupportSeries
