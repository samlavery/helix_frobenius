import RequestProject.CPSEdgePositivityCore3D

/-!
# The Mertens product bound for tempered self-dual banks

The positivity half of the edge-nonvanishing argument, per prime.  For a
tempered (unit-circle) bank `α : Fin m → ℂ` with real power sums (the
self-dual case — Maass `Sym^r` banks), the 2–1–4–1 combination of
Euler-factor logarithms

`2·(−log ζ-factor) + (−log D-factor) + 4·(−log C-factor twisted)
  + (−log D-factor double-twisted)`

has nonnegative real part: grouping the Taylor series by power, the `n`-th
coefficient is `(aⁿ/n)·2(1 + Sₙ·cₙ)²` with `Sₙ` the real power sum and
`cₙ = (zⁿ).re` — the Mertens square, closed by the trig-free angle-doubling
law `sq_re_of_norm_one`.  Here the `D`-factor is the diagonal
Rankin--Selberg factor with root bank `{αᵢ·αₖ}` — no squared-root bank and
no auxiliary object enters.  No `axiom`, no `sorry`.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

/-- Real power sums package: the bank's `n`-th power sum as a real number. -/
noncomputable def bankPowerSum {m : ℕ} (α : Fin m → ℂ) (n : ℕ) : ℝ :=
  (∑ i, α i ^ n).re

theorem bankPowerSum_eq {m : ℕ} (α : Fin m → ℂ)
    (hreal : ∀ n : ℕ, (∑ i, α i ^ n).im = 0) (n : ℕ) :
    ((bankPowerSum α n : ℝ) : ℂ) = ∑ i, α i ^ n := by
  apply Complex.ext
  · simp [bankPowerSum]
  · simp [hreal n]

/-- **The per-prime Mertens-square positivity.**  For a tempered bank with
real power sums, `0 < a < 1`, and a unit twist `z`, the combined
Euler-factor logarithm has nonnegative real part. -/
theorem re_log_comb_nonneg_bank {m : ℕ} (α : Fin m → ℂ)
    (hα : ∀ i, ‖α i‖ = 1)
    (hreal : ∀ n : ℕ, (∑ i, α i ^ n).im = 0)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 2 * (-Complex.log (1 - (a : ℂ))).re
      + (∑ i, ∑ k, (-Complex.log (1 - (a : ℂ) * (α i * α k)))).re
      + 4 * (∑ i, (-Complex.log (1 - (a : ℂ) * (α i * z)))).re
      + (∑ i, ∑ k, (-Complex.log (1 - (a : ℂ) * (α i * α k * z ^ 2)))).re := by
  -- norms of all the Taylor arguments
  have hnorm0 : ‖(a : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha₀]
    exact ha₁
  have hnormD : ∀ i k : Fin m, ‖(a : ℂ) * (α i * α k)‖ < 1 := by
    intro i k
    rw [norm_mul, norm_mul, hα i, hα k, one_mul, mul_one]
    exact hnorm0
  have hnormC : ∀ i : Fin m, ‖(a : ℂ) * (α i * z)‖ < 1 := by
    intro i
    rw [norm_mul, norm_mul, hα i, hz, one_mul, mul_one]
    exact hnorm0
  have hnormD2 : ∀ i k : Fin m, ‖(a : ℂ) * (α i * α k * z ^ 2)‖ < 1 := by
    intro i k
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hα i, hα k, hz]
    simpa using hnorm0
  -- the four Taylor `HasSum`s (finite sums over the bank indices inside)
  have h0 : HasSum (fun n : ℕ => ((a : ℂ) ^ n / n).re)
      (-Complex.log (1 - (a : ℂ))).re :=
    hasSum_re (hasSum_taylorSeries_neg_log hnorm0)
  have hD : HasSum
      (fun n : ℕ => (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n / n).re)
      ((∑ i, ∑ k, -Complex.log (1 - (a : ℂ) * (α i * α k)))).re := by
    apply hasSum_re
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro k _
    exact hasSum_taylorSeries_neg_log (hnormD i k)
  have hC : HasSum
      (fun n : ℕ => (∑ i, ((a : ℂ) * (α i * z)) ^ n / n).re)
      ((∑ i, -Complex.log (1 - (a : ℂ) * (α i * z)))).re := by
    apply hasSum_re
    apply hasSum_sum
    intro i _
    exact hasSum_taylorSeries_neg_log (hnormC i)
  have hD2 : HasSum
      (fun n : ℕ => (∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n / n).re)
      ((∑ i, ∑ k, -Complex.log (1 - (a : ℂ) * (α i * α k * z ^ 2)))).re := by
    apply hasSum_re
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro k _
    exact hasSum_taylorSeries_neg_log (hnormD2 i k)
  -- combine and bound termwise
  have htotal := ((h0.mul_left 2).add hD).add ((hC.mul_left 4).add hD2)
  rw [show 2 * (-Complex.log (1 - (a : ℂ))).re
      + (∑ i, ∑ k, (-Complex.log (1 - (a : ℂ) * (α i * α k)))).re
      + 4 * (∑ i, (-Complex.log (1 - (a : ℂ) * (α i * z)))).re
      + (∑ i, ∑ k, (-Complex.log (1 - (a : ℂ) * (α i * α k * z ^ 2)))).re
      = 2 * (-Complex.log (1 - (a : ℂ))).re
        + ((∑ i, ∑ k, -Complex.log (1 - (a : ℂ) * (α i * α k)))).re
        + (4 * ((∑ i, -Complex.log (1 - (a : ℂ) * (α i * z)))).re
          + ((∑ i, ∑ k, -Complex.log (1 - (a : ℂ)
              * (α i * α k * z ^ 2)))).re) by
    simp only [Complex.re_sum, Finset.sum_neg_distrib]
    ring]
  rw [← htotal.tsum_eq]
  apply tsum_nonneg
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- the n-th coefficient is the Mertens square
  set S : ℝ := bankPowerSum α n with hS
  set c : ℝ := (z ^ n).re with hc
  have hzn : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hself := bankPowerSum_eq α hreal n
  -- rewrite each finite sum through the power sum
  have hCsum : (∑ i, ((a : ℂ) * (α i * z)) ^ n)
      = (a : ℂ) ^ n * ((S : ℂ) * z ^ n) := by
    rw [hself, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hDsum : (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n)
      = (a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) := by
    rw [hself, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hD2sum : (∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n)
      = (a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) * (z ^ n) ^ 2 := by
    calc ∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n
        = ∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n * (z ^ n) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n) * (z ^ n) ^ 2 := by
          simp_rw [← Finset.sum_mul]
      _ = (a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) * (z ^ n) ^ 2 := by
          rw [hDsum]
  -- real parts of the grouped coefficients
  have hre_a : (((a : ℂ) ^ n / n)).re = a ^ n / n := by
    rw [show ((a : ℂ) ^ n / n) = (((a ^ n / n : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hre_C : ((a : ℂ) ^ n * ((S : ℂ) * z ^ n) / n).re
      = a ^ n * (S * c) / n := by
    rw [show (a : ℂ) ^ n * ((S : ℂ) * z ^ n) / n
        = ((a ^ n * S / n : ℝ) : ℂ) * z ^ n by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [← hc]
    ring
  have hre_D : ((a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) / n).re
      = a ^ n * (S * S) / n := by
    rw [show (a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) / n
        = ((a ^ n * (S * S) / n : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hre_D2 : ((a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) * (z ^ n) ^ 2 / n).re
      = a ^ n * (S * S) * (2 * c ^ 2 - 1) / n := by
    rw [show (a : ℂ) ^ n * ((S : ℂ) * (S : ℂ)) * (z ^ n) ^ 2 / n
        = ((a ^ n * (S * S) / n : ℝ) : ℂ) * (z ^ n) ^ 2 by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [sq_re_of_norm_one hzn, ← hc]
    ring
  -- divide the sums by n and conclude with the square
  have hdivC : (∑ i, ((a : ℂ) * (α i * z)) ^ n / n).re
      = a ^ n * (S * c) / n := by
    rw [← Finset.sum_div, hCsum]
    exact hre_C
  have hdivD : (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n / n).re
      = a ^ n * (S * S) / n := by
    have heq : (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n / n)
        = (∑ i, ∑ k, ((a : ℂ) * (α i * α k)) ^ n) / n := by
      simp_rw [← Finset.sum_div]
    rw [heq, hDsum]
    exact hre_D
  have hdivD2 : (∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n / n).re
      = a ^ n * (S * S) * (2 * c ^ 2 - 1) / n := by
    have heq : (∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n / n)
        = (∑ i, ∑ k, ((a : ℂ) * (α i * α k * z ^ 2)) ^ n) / n := by
      simp_rw [← Finset.sum_div]
    rw [heq, hD2sum]
    exact hre_D2
  rw [hre_a, hdivC, hdivD, hdivD2]
  have han : (0 : ℝ) ≤ a ^ n := pow_nonneg ha₀ n
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (0 : ℝ) ≤ 2 * (1 + S * c) ^ 2 := by positivity
  rw [show 2 * (a ^ n / n) + a ^ n * (S * S) / n
      + (4 * (a ^ n * (S * c) / n)
        + a ^ n * (S * S) * (2 * c ^ 2 - 1) / n)
      = (a ^ n / n) * (2 * (1 + S * c) ^ 2) by field_simp; ring]
  positivity

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.re_log_comb_nonneg_bank
