import RequestProject.MaassCosineOrthogonality

/-!
# Finite-level Parseval in the cosine basis

The next brick of the Maass Rankin--Selberg chain.  `waveForm` expands the even Maass wave in the
real cosine basis `cos(2π(n+1)x)`, so the horizontal energy readout is a Parseval identity for that
basis.  This file proves it at **finite level**, where it is exact and needs no convergence
hypothesis whatsoever — the same strategy `ParsevalExact` uses for the holomorphic case (finite
level first, tail estimate afterwards).

* `finite_cosine_parseval_real` — for real coefficients, `∫₀¹ (∑ rₙ cos(2π(n+1)x))² dx = (∑ rₙ²)/2`;
* `finite_cosine_parseval` — the complex form, obtained by splitting into real and imaginary parts
  (the cosines are real, so the two parts do not interact).

Only the frequencies `n+1 ≥ 1` occur, which is exactly the positivity hypothesis of
`integral_cos_mul_cos`.

Scope: the passage to `tsum` needs the summability supplied by `radialKernel_norm_le_exp` against
the Hecke bound; that is not proven here.
-/

open Real intervalIntegral MeasureTheory Finset

namespace CriticalLinePhasor.MaassParseval

/-- Each cosine mode is interval-integrable against any other on the period. -/
private lemma intervalIntegrable_cos_mul (m n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ => Real.cos (2 * Real.pi * (m : ℝ) * x) *
        Real.cos (2 * Real.pi * (n : ℝ) * x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)))

/-- **Finite-level Parseval, real coefficients.**  Exact, with no convergence hypothesis. -/
theorem finite_cosine_parseval_real (r : ℕ → ℝ) (N : ℕ) :
    (∫ x in (0:ℝ)..1,
      (∑ n ∈ range N, r n * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2) =
      (∑ n ∈ range N, (r n) ^ 2) / 2 := by
  have hexpand : ∀ x : ℝ,
      (∑ n ∈ range N, r n * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2 =
        ∑ n ∈ range N, ∑ m ∈ range N,
          (r n * r m) * (Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) *
            Real.cos (2 * Real.pi * ((m : ℝ) + 1) * x)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [intervalIntegral.integral_congr (g := fun x =>
    ∑ n ∈ range N, ∑ m ∈ range N,
      (r n * r m) * (Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) *
        Real.cos (2 * Real.pi * ((m : ℝ) + 1) * x))) (fun x _ => hexpand x)]
  rw [intervalIntegral.integral_finset_sum]
  · have hinner : ∀ n ∈ range N,
        (∫ x in (0:ℝ)..1, ∑ m ∈ range N,
          (r n * r m) * (Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) *
            Real.cos (2 * Real.pi * ((m : ℝ) + 1) * x))) = (r n) ^ 2 / 2 := by
      intro n hn
      rw [intervalIntegral.integral_finset_sum]
      · have hterm : ∀ m ∈ range N,
            (∫ x in (0:ℝ)..1,
              (r n * r m) * (Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) *
                Real.cos (2 * Real.pi * ((m : ℝ) + 1) * x))) =
              if m = n then (r n) ^ 2 / 2 else 0 := by
          intro m _
          rw [intervalIntegral.integral_const_mul]
          have hcast : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by
            intro k; push_cast; ring
          rw [hcast n, hcast m,
            integral_cos_mul_cos (Nat.succ_pos n) (Nat.succ_pos m)]
          by_cases hmn : m = n
          · subst hmn
            rw [if_pos rfl, if_pos rfl]
            ring
          · rw [if_neg (by omega : ¬ (n + 1 = m + 1)), if_neg hmn]
            ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (range N) n (fun _ => (r n) ^ 2 / 2),
          if_pos hn]
      · intro m _
        apply Continuous.intervalIntegrable
        exact continuous_const.mul
          ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
            (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro m _
    exact continuous_const.mul
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))

/-- **Finite-level Parseval, complex coefficients.**  The cosines are real, so the real and
imaginary parts of the coefficient sequence do not interact and each obeys the real identity.
This is the form the Maass coefficients `aₙ·K((n+1)y)` take. -/
theorem finite_cosine_parseval (c : ℕ → ℂ) (N : ℕ) :
    (∫ x in (0:ℝ)..1,
      ‖∑ n ∈ range N, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2) =
      (∑ n ∈ range N, ‖c n‖ ^ 2) / 2 := by
  have hsplit : ∀ x : ℝ,
      ‖∑ n ∈ range N, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2 =
        (∑ n ∈ range N, (c n).re * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2 +
          (∑ n ∈ range N, (c n).im * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2 := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    congr 1
    · rw [Complex.re_sum]
      rw [← sq]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    · rw [Complex.im_sum]
      rw [← sq]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [intervalIntegral.integral_congr (g := fun x =>
    (∑ n ∈ range N, (c n).re * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2 +
      (∑ n ∈ range N, (c n).im * Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)) ^ 2)
    (fun x _ => hsplit x)]
  rw [intervalIntegral.integral_add]
  · rw [finite_cosine_parseval_real (fun n => (c n).re) N,
      finite_cosine_parseval_real (fun n => (c n).im) N, ← add_div]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply continuous_finsetSum
    intro m _
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply continuous_finsetSum
    intro m _
    exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))

end CriticalLinePhasor.MaassParseval

#print axioms CriticalLinePhasor.MaassParseval.finite_cosine_parseval_real
#print axioms CriticalLinePhasor.MaassParseval.finite_cosine_parseval
