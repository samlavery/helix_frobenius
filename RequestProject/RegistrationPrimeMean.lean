import RequestProject.RegistrationScale
import RequestProject.PrimeWarpOscillation

open Set MeasureTheory Filter Topology Asymptotics
open scoped BigOperators

namespace CriticalLinePhasor.ContourArgument

theorem rieszProfile_logScale_eq_logEntryWeight {c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) :
    rieszProfile (logScale c t) (Real.log n) = logEntryWeight c (Real.log n) t := by
  rw [rieszProfile_eq (logScale_pos hc t) (Real.log_natCast_nonneg n)]
  rfl

/-- Each actual prime clock has a uniformly bounded primitive as its Riesz weight grows. -/
theorem growing_prime_clock_integral_bound {c T : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hT : 0 ≤ T) (n : ℕ) :
    |∫ t in (0 : ℝ)..T, rieszProfile (logScale c t) (Real.log n) * strainClock n t| ≤
      2 / Real.log 2 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [strainClock, ArithmeticFunction.vonMangoldt_apply]
    <;> positivity
  · have hn2 : 2 ≤ n := by omega
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogle : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hlogn : 0 < Real.log n := hlog2.trans_le hlogle
    have hentry : c * Real.log 2 ≤ Real.log n := by
      calc c * Real.log 2 ≤ 1 * Real.log 2 := mul_le_mul_of_nonneg_right hc1 hlog2.le
        _ ≤ Real.log n := by simpa using hlogle
    have heq : (fun t => rieszProfile (logScale c t) (Real.log n) * strainClock n t) =
        fun t => strainAmp n * (logEntryWeight c (Real.log n) t * Real.sin (t * Real.log n)) := by
      funext t
      rw [rieszProfile_logScale_eq_logEntryWeight hc]
      unfold strainClock strainAmp
      ring
    rw [heq, intervalIntegral.integral_const_mul, abs_mul]
    calc |strainAmp n| * |∫ t in (0 : ℝ)..T,
          logEntryWeight c (Real.log n) t * Real.sin (t * Real.log n)|
        ≤ 1 * (2 / Real.log n) :=
          mul_le_mul (abs_strainAmp_le_one n)
            (logEntryWeight_sine_integral_bound hc hlogn hentry hT) (abs_nonneg _) zero_le_one
      _ ≤ 2 / Real.log 2 := by
        rw [one_mul]
        exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlogle

/-- The changing head is frozen only as a summation range; every weight still varies with `t`. -/
theorem registryStrain_integral_bound {c T : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hT : 0 ≤ T) :
    |∫ t in (0 : ℝ)..T, registryStrain c t| ≤
      (1 / Real.pi) * (Real.exp (logScale c T) + 1) * (2 / Real.log 2) := by
  let M := ⌊Real.exp (logScale c T)⌋₊
  let term := fun (n : ℕ) (t : ℝ) => rieszProfile (logScale c t) (Real.log n) * strainClock n t
  have hterm (n : ℕ) : Continuous (term n) := by
    have heq : term n = fun t => logEntryWeight c (Real.log n) t * strainClock n t := by
      funext t
      exact congrArg (fun x => x * strainClock n t) (rieszProfile_logScale_eq_logEntryWeight hc n t)
    rw [heq]
    exact (logEntryWeight_continuous hc _).mul (strainClock_continuous n)
  have heq : (∫ t in (0 : ℝ)..T, registryStrain c t) =
      -(1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), ∫ t in (0 : ℝ)..T, term n t := by
    calc (∫ t in (0 : ℝ)..T, registryStrain c t)
        = ∫ t in (0 : ℝ)..T, -(1 / Real.pi) * ∑ n ∈ Finset.range (M + 1), term n t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hT] at ht
          exact rieszStrain_eq_sum_range (logScale_pos hc t)
            (Nat.floor_mono (Real.exp_le_exp.mpr (logScale_mono hc ht.2))) t
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        intro n _
        exact (hterm n).intervalIntegrable 0 T
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  have hsum : |∑ n ∈ Finset.range (M + 1), ∫ t in (0 : ℝ)..T, term n t| ≤
      ((M + 1 : ℕ) : ℝ) * (2 / Real.log 2) := by
    calc |∑ n ∈ Finset.range (M + 1), ∫ t in (0 : ℝ)..T, term n t|
        ≤ ∑ n ∈ Finset.range (M + 1), |∫ t in (0 : ℝ)..T, term n t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (M + 1), (2 / Real.log 2) :=
          Finset.sum_le_sum (fun n _ => growing_prime_clock_integral_bound hc hc1 hT n)
      _ = _ := by simp
  have hM : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (logScale c T) + 1 := by
    dsimp [M]
    push_cast
    linarith [Nat.floor_le (Real.exp_pos (logScale c T)).le]
  calc (1 / Real.pi) * |∑ n ∈ Finset.range (M + 1), ∫ t in (0 : ℝ)..T, term n t|
      ≤ (1 / Real.pi) * (((M + 1 : ℕ) : ℝ) * (2 / Real.log 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1 / Real.pi) * ((Real.exp (logScale c T) + 1) * (2 / Real.log 2)) := by
      gcongr
    _ = _ := by ring

/-- The actual growing prime strain has sublinear running integral for every `0 < c < 1`. -/
theorem registryStrain_integral_isLittleO {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (fun T => ∫ t in (0 : ℝ)..T, registryStrain c t) =o[atTop] (fun T : ℝ => T) := by
  have hpow : (fun T => Real.exp (logScale c T)) =o[atTop] (fun T : ℝ => T) := by
    apply (isLittleO_iff_tendsto' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT hzero
      exact (hT.ne' hzero).elim)).mpr
    refine (tendsto_rpow_neg_atTop (sub_pos.mpr hc1)).congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    rw [show -(1 - c) = c - 1 by ring, Real.rpow_sub (by linarith : 0 < T),
      Real.rpow_one, exp_logScale, max_eq_left hT]
  have hbudget := (hpow.add (isLittleO_const_id_atTop (1 : ℝ))).const_mul_left
    ((1 / Real.pi) * (2 / Real.log 2))
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hbudget.bound hε, eventually_ge_atTop (0 : ℝ)] with T hb hT
  rw [Real.norm_eq_abs]
  calc |∫ t in (0 : ℝ)..T, registryStrain c t|
      ≤ (1 / Real.pi) * (Real.exp (logScale c T) + 1) * (2 / Real.log 2) :=
        registryStrain_integral_bound hc hc1.le hT
    _ = ((1 / Real.pi) * (2 / Real.log 2)) * (Real.exp (logScale c T) + 1) := by ring
    _ ≤ ‖((1 / Real.pi) * (2 / Real.log 2)) * (Real.exp (logScale c T) + 1)‖ :=
      le_abs_self _
    _ ≤ ε * ‖T‖ := hb

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.growing_prime_clock_integral_bound
#print axioms CriticalLinePhasor.ContourArgument.registryStrain_integral_bound
#print axioms CriticalLinePhasor.ContourArgument.registryStrain_integral_isLittleO
