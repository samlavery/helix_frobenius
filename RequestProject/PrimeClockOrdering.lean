import RequestProject.CarrierCarlsonMean
import RequestProject.PrimeClockData

/-!
# Prime-clock teeth and their eta ordering

This file supplies the concrete data consumed by the finite Herglotz banks:

* `PrimeTooth = ℕ × ℕ` records a prime position and a positive power;
* `primeToothLength` is exactly `(k + 1) * log p`;
* `primeToothFace` is unimodular whenever the underlying prime face is;
* `primeToothExhaustion` is an increasing exhaustive family of finite grids;
* `primeToothEtaIndex` identifies every clock length with an eta frequency.

The companion natural ordering `etaPrimePowerSupport` records the same prime-power
support directly inside the eta lattice.

Search audit:

```
rg -n -i -S "primeClock|prime_clock|teeth|tooth|etaOrdering|eta_ordering|exhaustion" \
  RequestProject --glob '*.lean'
rg -n -S "prime_nth_prime|nth_count|count_nth|Prime.pow_inj" \
  .lake/packages/mathlib/Mathlib
rg -n -S "Real.log_pow|Prime.log_pos|product_subset_product|image_mono|range_mono" \
  .lake/packages/mathlib/Mathlib
```
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.PrimeClockOrdering

theorem etaFrequency_primeToothEtaIndex (i : PrimeTooth) :
    CriticalLinePhasor.CarlsonMean.etaFrequency (primeToothEtaIndex i) =
      primeToothLength i := by
  rw [CriticalLinePhasor.CarlsonMean.etaFrequency, primeToothLength]
  have hs : (primeToothEtaIndex i : ℝ) + 1 = (toothNat i : ℕ) := by
    exact_mod_cast primeToothEtaIndex_succ i
  rw [hs, toothNat, Nat.cast_pow, Real.log_pow]

/-- The log-weighted eta coefficients are square summable past `σ = 1/2`. -/
theorem etaLogSquare_summable {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun n : ℕ =>
      Real.log ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-2 * σ) := by
  let ε : ℝ := (2 * σ - 1) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : 2 * ε - 2 * σ < -1 := by dsimp [ε]; linarith
  have hraw : Summable fun n : ℕ => (1 / ε ^ 2) * (n : ℝ) ^ (2 * ε - 2 * σ) :=
    (Real.summable_nat_rpow.mpr hexp).mul_left _
  have hbase : Summable fun n : ℕ =>
      (1 / ε ^ 2) * ((n : ℝ) + 1) ^ (2 * ε - 2 * σ) := by
    simpa using (summable_nat_add_iff 1).mpr hraw
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  · intro n
    let x : ℝ := n + 1
    have hx : 0 < x := by dsimp [x]; positivity
    have hx1 : 1 ≤ x := by dsimp [x]; norm_num
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlog := Real.log_le_rpow_div hx.le hε
    have hsquare : Real.log x ^ 2 ≤ (x ^ ε / ε) ^ 2 := by nlinarith
    have hweight : 0 ≤ x ^ (-2 * σ) := Real.rpow_nonneg hx.le _
    calc
      Real.log ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (-2 * σ)
          = Real.log x ^ 2 * x ^ (-2 * σ) := by rfl
      _ ≤ (x ^ ε / ε) ^ 2 * x ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right hsquare hweight
      _ = (1 / ε ^ 2) * x ^ (2 * ε - 2 * σ) := by
        rw [div_pow]
        have hpow : (x ^ ε) ^ 2 = x ^ (2 * ε) := by
          calc
            (x ^ ε) ^ 2 = (x ^ ε) ^ (2 : ℝ) := by rw [Real.rpow_two]
            _ = x ^ (ε * 2) := by rw [← Real.rpow_mul hx.le]
            _ = x ^ (2 * ε) := by ring_nf
        rw [hpow]
        rw [show x ^ (2 * ε) / ε ^ 2 * x ^ (-2 * σ) =
          (1 / ε ^ 2) * (x ^ (2 * ε) * x ^ (-2 * σ)) by ring]
        rw [← Real.rpow_add hx]
        ring_nf
      _ = (1 / ε ^ 2) * (n + 1 : ℝ) ^ (2 * ε - 2 * σ) := by norm_num [x]
  · exact hbase

/-- The log-weighted coefficient of a prime-power tooth on the line `Re s = σ`. -/
def primeToothCoefficient (α : Nat.Primes → ℂ) (σ : ℝ) (i : PrimeTooth) : ℂ :=
  ((primeToothLength i : ℝ) : ℂ) * primeToothFace α i *
    Complex.ofReal ((toothNat i : ℝ) ^ (-σ))

theorem primeToothCoefficient_square_summable
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun i : PrimeTooth => ‖primeToothCoefficient α σ i‖ ^ 2 := by
  have hbase := (etaLogSquare_summable hσ).comp_injective primeToothEtaIndex_injective
  apply hbase.congr
  intro i
  have htpos : 0 < (toothNat i : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_two (toothNat_two_le i)
  rw [Function.comp_apply, primeToothCoefficient, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeToothLength_pos i),
    primeToothFace_norm α hα, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos htpos _),
    mul_pow, primeToothLength_eq_log_toothNat]
  have hs : (primeToothEtaIndex i : ℝ) + 1 = (toothNat i : ℕ) := by
    exact_mod_cast primeToothEtaIndex_succ i
  rw [hs]
  have hpow : (((toothNat i : ℝ) ^ (-σ)) ^ 2) =
      (toothNat i : ℝ) ^ (-2 * σ) := by
    calc
      ((toothNat i : ℝ) ^ (-σ)) ^ 2 =
          ((toothNat i : ℝ) ^ (-σ)) ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = (toothNat i : ℝ) ^ (-σ * 2) := by
        rw [← Real.rpow_mul (by positivity)]
      _ = (toothNat i : ℝ) ^ (-2 * σ) := by ring_nf
  rw [hpow]

/-- The finite exponential readout of the first prime-power tooth grid. -/
def primeToothReadout (α : Nat.Primes → ℂ) (σ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ primeToothExhaustion N,
    primeToothCoefficient α σ i *
      Complex.exp (-(Complex.I * primeToothLength i * t))

/-- Carlson mean-square Cauchy convergence for the exact log-weighted prime-clock teeth. -/
theorem primeTooth_meanSquare_cauchy
    (α : Nat.Primes → ℂ) (hα : ∀ p, ‖α p‖ = 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ M ≥ N,
      Tendsto (fun T : ℝ => CriticalLinePhasor.CarlsonMean.verticalMeanSquare
          (fun t => primeToothReadout α σ M t - primeToothReadout α σ N t) T)
        atTop (𝓝 (∑ i ∈ primeToothExhaustion M \ primeToothExhaustion N,
          (‖primeToothCoefficient α σ i‖ : ℂ) ^ 2)) ∧
      ∑ i ∈ primeToothExhaustion M \ primeToothExhaustion N,
          ‖primeToothCoefficient α σ i‖ ^ 2 < ε := by
  have hsq := primeToothCoefficient_square_summable α hα hσ
  have hexhaust : Tendsto primeToothExhaustion atTop atTop :=
    primeToothExhaustion_mono.tendsto_atTop_finset fun i =>
      ⟨max i.1 i.2 + 1, mem_primeToothExhaustion i⟩
  have hScauchy : CauchySeq fun N =>
      ∑ i ∈ primeToothExhaustion N, ‖primeToothCoefficient α σ i‖ ^ 2 :=
    (hsq.hasSum.comp hexhaust).cauchySeq
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp hScauchy) ε hε
  refine ⟨N, fun M hMN => ?_⟩
  have hsub : primeToothExhaustion N ⊆ primeToothExhaustion M :=
    primeToothExhaustion_mono hMN
  have hdiff : ∀ t : ℝ,
      primeToothReadout α σ M t - primeToothReadout α σ N t =
        ∑ i ∈ primeToothExhaustion M \ primeToothExhaustion N,
          primeToothCoefficient α σ i *
            Complex.exp (-(Complex.I * primeToothLength i * t)) := by
    intro t
    rw [primeToothReadout, primeToothReadout]
    have hsplit := Finset.sum_sdiff hsub
      (f := fun i => primeToothCoefficient α σ i *
        Complex.exp (-(Complex.I * primeToothLength i * t)))
    rw [← hsplit]
    exact add_sub_cancel_right _ _
  constructor
  · refine Filter.Tendsto.congr (fun T => ?_)
      (CriticalLinePhasor.CarlsonMean.finite_meanSquare_tendsto
        (primeToothExhaustion M \ primeToothExhaustion N)
        primeToothLength (primeToothCoefficient α σ) primeToothLength_injective.injOn)
    congr 1
    funext t
    exact (hdiff t).symm
  · have hdist := hN M hMN
    rw [Real.dist_eq] at hdist
    have hsplit := Finset.sum_sdiff hsub
      (f := fun i => ‖primeToothCoefficient α σ i‖ ^ 2)
    have hnonneg : 0 ≤ ∑ i ∈ primeToothExhaustion M \ primeToothExhaustion N,
        ‖primeToothCoefficient α σ i‖ ^ 2 := by positivity
    have hsumdiff :
        (∑ i ∈ primeToothExhaustion M, ‖primeToothCoefficient α σ i‖ ^ 2) -
            ∑ i ∈ primeToothExhaustion N, ‖primeToothCoefficient α σ i‖ ^ 2 =
          ∑ i ∈ primeToothExhaustion M \ primeToothExhaustion N,
            ‖primeToothCoefficient α σ i‖ ^ 2 := by
      rw [← hsplit]
      ring
    rw [hsumdiff] at hdist
    simpa [abs_of_nonneg hnonneg] using hdist

end CriticalLinePhasor.PrimeClockOrdering

#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothLength_pos
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothFace_norm
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothExhaustion_eventually_mem
#print axioms CriticalLinePhasor.PrimeClockOrdering.etaFrequency_primeToothEtaIndex
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothEtaIndex_injective
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothLength_injective
#print axioms CriticalLinePhasor.PrimeClockOrdering.etaLogSquare_summable
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothCoefficient_square_summable
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeTooth_meanSquare_cauchy
#print axioms CriticalLinePhasor.PrimeClockOrdering.primeToothEtaIndex_mem_support
