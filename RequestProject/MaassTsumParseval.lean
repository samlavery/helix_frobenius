import RequestProject.MaassFiniteParseval

/-!
# Parseval in the cosine basis, `tsum` form

The tail step of the Maass Rankin--Selberg chain.  `MaassFiniteParseval` gives the identity exactly
at finite level; this file passes to the limit under the single hypothesis that the coefficient
sequence is absolutely summable.

The passage is dominated convergence with a **constant** dominating function: the partial sums are
uniformly bounded by `∑' n, ‖cₙ‖` because every cosine has modulus at most one, so the squares are
bounded by the square of that constant, which is integrable on a bounded interval.  Pointwise
convergence of the partial sums is immediate from absolute summability.

`summable_sq_of_summable_norm` records the elementary fact that absolute summability of `cₙ` gives
summability of `‖cₙ‖²`, which is what the right-hand side needs.

For the Maass application the hypothesis is discharged by `radialKernel_norm_le_exp` against the
polynomial Hecke bound; that discharge is not performed here.
-/

open Real intervalIntegral MeasureTheory Filter Topology Finset

namespace CriticalLinePhasor.MaassParseval

variable {c : ℕ → ℂ}

/-- Absolute summability gives summability of the squared norms. -/
theorem summable_sq_of_summable_norm (hc : Summable fun n => ‖c n‖) :
    Summable fun n => ‖c n‖ ^ 2 := by
  set M : ℝ := ∑' n : ℕ, ‖c n‖ with hM
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hc.mul_left M)
  have hle : ‖c n‖ ≤ M := hc.le_tsum n (fun m _ => norm_nonneg _)
  calc ‖c n‖ ^ 2 = ‖c n‖ * ‖c n‖ := sq _
    _ ≤ M * ‖c n‖ := by gcongr

/-- The cosine series converges absolutely at every point. -/
theorem summable_cosine_series (hc : Summable fun n => ‖c n‖) (x : ℝ) :
    Summable fun n => c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded hc fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖c n‖ * |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| ≤ ‖c n‖ * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = ‖c n‖ := mul_one _

/-- **Parseval in the cosine basis.**  For an absolutely summable coefficient sequence the
horizontal energy readout is half the squared-norm sum. -/
theorem tsum_cosine_parseval (hc : Summable fun n => ‖c n‖) :
    (∫ x in (0:ℝ)..1,
      ‖∑' n : ℕ, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2) =
      (∑' n : ℕ, ‖c n‖ ^ 2) / 2 := by
  set M : ℝ := ∑' n : ℕ, ‖c n‖ with hMdef
  set F : ℕ → ℝ → ℝ := fun N x =>
    ‖∑ n ∈ range N, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2 with hF
  set f : ℝ → ℝ := fun x =>
    ‖∑' n : ℕ, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2 with hf
  -- uniform bound on the partial sums
  have hpartial : ∀ (N : ℕ) (x : ℝ),
      ‖∑ n ∈ range N, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ≤ M := by
    intro N x
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ range N,
        ‖c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ≤ ‖c n‖ := by
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖c n‖ * |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| ≤ ‖c n‖ * 1 := by
            gcongr
            exact Real.abs_cos_le_one _
        _ = ‖c n‖ := mul_one _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    exact hc.sum_le_tsum _ (fun n _ => norm_nonneg _)
  -- pointwise convergence of the partial sums
  have hlim : ∀ x : ℝ, Tendsto (fun N => F N x) atTop (𝓝 (f x)) := by
    intro x
    have hs := (summable_cosine_series hc x).hasSum.tendsto_sum_nat
    exact (hs.norm).pow 2
  -- dominated convergence on the interval
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable (F N) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro N
    apply Continuous.aestronglyMeasurable
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hbound : ∀ N : ℕ,
      ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ‖F N x‖ ≤ M ^ 2 := by
    intro N
    filter_upwards with x
    rw [hF]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤
      ‖∑ n ∈ range N, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2)]
    have h := hpartial N x
    have hnn : (0 : ℝ) ≤ ‖∑ n ∈ range N,
        c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ := norm_nonneg _
    nlinarith [h, hnn]
  have hint : Integrable (fun _ : ℝ => M ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    apply integrable_const
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => M ^ 2) hmeas hint hbound
    (Filter.Eventually.of_forall fun x => hlim x)
  -- identify both sides
  have hleft : ∀ N : ℕ,
      (∫ x in Set.Ioc (0:ℝ) 1, F N x) = (∑ n ∈ range N, ‖c n‖ ^ 2) / 2 := by
    intro N
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact finite_cosine_parseval c N
  have hright : Tendsto (fun N => (∑ n ∈ range N, ‖c n‖ ^ 2) / 2) atTop
      (𝓝 ((∑' n : ℕ, ‖c n‖ ^ 2) / 2)) :=
    ((summable_sq_of_summable_norm hc).hasSum.tendsto_sum_nat).div_const 2
  have hfinal : (∫ x in Set.Ioc (0:ℝ) 1, f x) = (∑' n : ℕ, ‖c n‖ ^ 2) / 2 := by
    refine tendsto_nhds_unique hDCT ?_
    simpa only [hleft] using hright
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hfinal

end CriticalLinePhasor.MaassParseval

#print axioms CriticalLinePhasor.MaassParseval.summable_sq_of_summable_norm
#print axioms CriticalLinePhasor.MaassParseval.tsum_cosine_parseval
