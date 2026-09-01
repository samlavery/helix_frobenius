import RequestProject.MellinDual

/-!
# Carlson mean convergence for the ordered carrier bank

This file proves the unconditional mean half of the ordered-bank convergence problem.
For square-summable coefficients at distinct log frequencies, the normalized vertical
mean square of every finite tail is exactly its coefficient-square mass.  Consequently
the ordered partial readouts are Cauchy in vertical mean square.  The final theorem
specializes this to the eta ordering `n ↦ log (n + 1)` with arbitrary unimodular faces;
its coefficient threshold is exactly `σ > 1/2`.

The result is a mean statement.  It contains no pointwise-convergence or regularity
hypothesis.

Search audit:

```
rg -n -i -S "Carlson|mean.value|meanSquare|square.summable|vertical.*mean" RequestProject
rg -n -S "char_mean_zero|char_mean_one|readout_dual_recovers_sites" RequestProject
rg -n -S "summable_nat_rpow|cauchySeq_iff|tendsto_finsetSum" \
  .lake/packages/mathlib/Mathlib
smart_search.sh "mean square limit finite exponential sum distinct real frequencies"
smart_search.sh "square summable coefficients partial exponential sums converge in vertical mean"
```
-/

open Complex Filter Topology intervalIntegral

noncomputable section

namespace CriticalLinePhasor.CarlsonMean

/-- A finite ordered exponential readout. -/
def orderedReadout (a : ℕ → ℂ) (h : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * Complex.exp (-(Complex.I * h n * t))

/-- The normalized vertical mean square of a complex readout. -/
def verticalMeanSquare (F : ℝ → ℂ) (T : ℝ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, F t * (starRingEnd ℂ) (F t)

/-- Carlson's finite mean-value identity: distinct characters are orthogonal in
the vertical mean. -/
theorem finite_meanSquare_tendsto {ι : Type*} (s : Finset ι) (h : ι → ℝ)
    (a : ι → ℂ) (hinj : Set.InjOn h s) :
    Tendsto (fun T : ℝ => verticalMeanSquare
        (fun t => ∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * t))) T)
      atTop (𝓝 (∑ n ∈ s, (‖a n‖ : ℂ) ^ 2)) := by
  classical
  let F : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * t))
  have hconj : ∀ t : ℝ,
      (starRingEnd ℂ) (F t) =
        ∑ n ∈ s, (starRingEnd ℂ) (a n) * Complex.exp (Complex.I * h n * t) := by
    intro t
    simp only [F, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hmean : ∀ T : ℝ,
      verticalMeanSquare F T =
        ∑ n ∈ s, (starRingEnd ℂ) (a n) *
          ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
            F t * Complex.exp (Complex.I * h n * t)) := by
    intro T
    rw [verticalMeanSquare]
    have hpoint : ∀ t : ℝ,
        F t * (starRingEnd ℂ) (F t) =
          ∑ n ∈ s, (starRingEnd ℂ) (a n) *
            (F t * Complex.exp (Complex.I * h n * t)) := by
      intro t
      rw [hconj t, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
      intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
      ring
    · intro n hn
      exact (Continuous.const_mul
        ((by fun_prop : Continuous fun t : ℝ =>
          F t * Complex.exp (Complex.I * h n * t)))
            ((starRingEnd ℂ) (a n))).intervalIntegrable _ _
  rw [show (fun T : ℝ => verticalMeanSquare F T) = fun T : ℝ =>
      ∑ n ∈ s, (starRingEnd ℂ) (a n) *
        ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
          F t * Complex.exp (Complex.I * h n * t)) by funext T; exact hmean T]
  have hterm : ∀ n ∈ s, Tendsto
      (fun T : ℝ => (starRingEnd ℂ) (a n) *
        ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
          F t * Complex.exp (Complex.I * h n * t)))
      atTop (𝓝 ((‖a n‖ : ℂ) ^ 2)) := by
    intro n hn
    have hextract := CriticalLinePhasor.MellinDual.readout_dual_recovers_sites
      s h a (h n)
    have hfilterSet : s.filter (fun m => h m = h n) = {n} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hm, heq⟩
        exact hinj hm hn heq
      · intro hmn
        subst m
        exact ⟨hn, rfl⟩
    have hfilter : ∑ m ∈ s.filter (fun m => h m = h n), a m = a n := by
      rw [hfilterSet]
      simp
    rw [hfilter] at hextract
    have hmul := hextract.const_mul ((starRingEnd ℂ) (a n))
    simpa [F, Complex.conj_mul'] using hmul
  exact tendsto_finsetSum s hterm

/-- Square-summable ordered coefficients give a Cauchy family in normalized
vertical mean square. -/
theorem orderedReadout_meanSquare_cauchy (a : ℕ → ℂ) (h : ℕ → ℝ)
    (hinj : Function.Injective h) (hsq : Summable fun n => ‖a n‖ ^ 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
      Tendsto (fun T : ℝ => verticalMeanSquare
          (fun t => orderedReadout a h M t - orderedReadout a h N t) T)
        atTop (𝓝 (∑ n ∈ Finset.range M \ Finset.range N, (‖a n‖ : ℂ) ^ 2)) ∧
      ∑ n ∈ Finset.range M \ Finset.range N, ‖a n‖ ^ 2 < ε := by
  intro ε hε
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, ‖a n‖ ^ 2
  have hScauchy : CauchySeq S := hsq.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp hScauchy) ε hε
  refine ⟨N, fun M hMN => ?_⟩
  have hdiff : ∀ t : ℝ,
      orderedReadout a h M t - orderedReadout a h N t =
        ∑ n ∈ Finset.range M \ Finset.range N,
          a n * Complex.exp (-(Complex.I * h n * t)) := by
    intro t
    rw [orderedReadout, orderedReadout]
    have hsub : Finset.range N ⊆ Finset.range M := Finset.range_mono hMN
    have hsplit := Finset.sum_sdiff hsub
      (f := fun n => a n * Complex.exp (-(Complex.I * h n * t)))
    rw [← hsplit]
    exact add_sub_cancel_right _ _
  constructor
  · refine Filter.Tendsto.congr (fun T => ?_)
      (finite_meanSquare_tendsto (Finset.range M \ Finset.range N) h a
        (hinj.injOn))
    congr 1
    funext t
    exact (hdiff t).symm
  · have hdist := hN M hMN
    rw [Real.dist_eq] at hdist
    dsimp [S] at hdist
    have hsub : Finset.range N ⊆ Finset.range M := Finset.range_mono hMN
    have hsplit := Finset.sum_sdiff hsub (f := fun n => ‖a n‖ ^ 2)
    have hnonneg : 0 ≤ ∑ n ∈ Finset.range M \ Finset.range N, ‖a n‖ ^ 2 := by
      positivity
    have hsumdiff :
        (∑ n ∈ Finset.range M, ‖a n‖ ^ 2) -
            ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 =
          ∑ n ∈ Finset.range M \ Finset.range N, ‖a n‖ ^ 2 := by
      rw [← hsplit]
      ring
    rw [hsumdiff] at hdist
    simpa [abs_of_nonneg hnonneg] using hdist

/-- The eta ordering's log frequencies. -/
def etaFrequency (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1)

/-- The eta-ordered coefficient at abscissa `σ`, with an arbitrary unit face. -/
def etaCoefficient (α : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  α n * ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)

theorem etaFrequency_injective : Function.Injective etaFrequency := by
  intro m n hmn
  unfold etaFrequency at hmn
  have hposm : 0 < (m : ℝ) + 1 := by positivity
  have hposn : 0 < (n : ℝ) + 1 := by positivity
  have hcast : (m : ℝ) + 1 = (n : ℝ) + 1 := (Real.strictMonoOn_log.injOn hposm hposn) hmn
  exact_mod_cast (by linarith : (m : ℝ) = n)

theorem etaCoefficient_square_summable (α : ℕ → ℂ) (hα : ∀ n, ‖α n‖ = 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) : Summable fun n => ‖etaCoefficient α σ n‖ ^ 2 := by
  have hpow : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * σ) := by
    have hbase : Summable fun n : ℕ => (n : ℝ) ^ (-2 * σ) := by
      rw [Real.summable_nat_rpow]
      linarith
    simpa using (summable_nat_add_iff 1).mpr hbase
  apply hpow.congr
  intro n
  symm
  rw [etaCoefficient, norm_mul, hα, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    (((n : ℝ) + 1) ^ (-σ)) ^ 2 = (((n : ℝ) + 1) ^ (-σ)) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
    _ = ((n : ℝ) + 1) ^ (-σ * 2) := by
      rw [← Real.rpow_mul (by positivity)]
    _ = ((n : ℝ) + 1) ^ (-2 * σ) := by ring_nf

/-- The unconditional Carlson mean-value brick for the eta-ordered bank at
every abscissa `σ > 1/2`. -/
theorem etaOrdered_meanSquare_cauchy (α : ℕ → ℂ) (hα : ∀ n, ‖α n‖ = 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
      Tendsto (fun T : ℝ => verticalMeanSquare
          (fun t => orderedReadout (etaCoefficient α σ) etaFrequency M t -
            orderedReadout (etaCoefficient α σ) etaFrequency N t) T)
        atTop (𝓝 (∑ n ∈ Finset.range M \ Finset.range N,
          (‖etaCoefficient α σ n‖ : ℂ) ^ 2)) ∧
      ∑ n ∈ Finset.range M \ Finset.range N, ‖etaCoefficient α σ n‖ ^ 2 < ε :=
  orderedReadout_meanSquare_cauchy (etaCoefficient α σ) etaFrequency
    etaFrequency_injective (etaCoefficient_square_summable α hα hσ)

end CriticalLinePhasor.CarlsonMean

#print axioms CriticalLinePhasor.CarlsonMean.finite_meanSquare_tendsto
#print axioms CriticalLinePhasor.CarlsonMean.orderedReadout_meanSquare_cauchy
#print axioms CriticalLinePhasor.CarlsonMean.etaCoefficient_square_summable
#print axioms CriticalLinePhasor.CarlsonMean.etaOrdered_meanSquare_cauchy
