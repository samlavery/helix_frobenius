import Mathlib

open Set MeasureTheory

namespace CriticalLinePhasor

/-- A growing weight in `[0,1]` preserves a uniform primitive bound for a sine clock. -/
theorem growing_weight_sine_integral_bound {a b ω : ℝ} (hab : a ≤ b) (hω : 0 < ω)
    {w w' : ℝ → ℝ}
    (hder : ∀ t ∈ uIcc a b, HasDerivAt w (w' t) t)
    (hint : IntervalIntegrable w' volume a b)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ w' t)
    (hw : ∀ t ∈ Icc a b, 0 ≤ w t ∧ w t ≤ 1) :
    |∫ t in a..b, w t * Real.sin (t * ω)| ≤ 2 / ω := by
  let v : ℝ → ℝ := fun t => -Real.cos (t * ω) / ω
  have hv : ∀ t ∈ uIcc a b, HasDerivAt v (Real.sin (t * ω)) t := by
    intro t _
    simpa [v, hω.ne'] using (((hasDerivAt_id t).mul_const ω).cos.neg.div_const ω)
  have hvc : Continuous v := by dsimp [v]; fun_prop
  have hsin : Continuous (fun t : ℝ => Real.sin (t * ω)) := by fun_prop
  have hvbound (t : ℝ) : |v t| ≤ 1 / ω := by
    dsimp [v]
    rw [abs_div, abs_neg, abs_of_pos hω]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hω.le
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hder hv hint
    (hsin.intervalIntegrable a b)
  have hprimitive : (∫ t in a..b, w' t) = w b - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have herror : |∫ t in a..b, w' t * v t| ≤ (w b - w a) / ω := by
    calc |∫ t in a..b, w' t * v t|
        ≤ ∫ t in a..b, |w' t * v t| := intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in a..b, w' t / ω := by
        apply intervalIntegral.integral_mono_on hab
          (hint.mul_continuousOn hvc.continuousOn).abs (hint.div_const ω)
        intro t ht
        rw [abs_mul, abs_of_nonneg (hpos t ht), div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa using hvbound t) (hpos t ht)
      _ = (w b - w a) / ω := by
        simp only [div_eq_mul_inv]
        rw [intervalIntegral.integral_mul_const, hprimitive]
  have hwa := hw a ⟨le_rfl, hab⟩
  have hwb := hw b ⟨hab, le_rfl⟩
  have hea : |w a * v a| ≤ w a / ω := by
    rw [abs_mul, abs_of_nonneg hwa.1, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa using hvbound a) hwa.1
  have heb : |w b * v b| ≤ w b / ω := by
    rw [abs_mul, abs_of_nonneg hwb.1, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa using hvbound b) hwb.1
  rw [hparts]
  calc |w b * v b - w a * v a - ∫ t in a..b, w' t * v t|
      ≤ |w b * v b - w a * v a| + |∫ t in a..b, w' t * v t| := abs_sub _ _
    _ ≤ (|w b * v b| + |w a * v a|) + |∫ t in a..b, w' t * v t| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (w b / ω + w a / ω) + (w b - w a) / ω := by gcongr
    _ = 2 * w b / ω := by ring
    _ ≤ 2 / ω := div_le_div_of_nonneg_right (by linarith) hω.le

/-- The Riesz weight after a clock has entered the logarithmically growing bank. -/
theorem active_log_weight_sine_integral_bound {a b c ω : ℝ}
    (hab : a ≤ b) (ha : 1 < a) (hc : 0 < c) (hω : 0 < ω)
    (hentry : ω ≤ c * Real.log a) :
    |∫ t in a..b, (1 - ω / (c * Real.log t)) * Real.sin (t * ω)| ≤ 2 / ω := by
  have ht1 : ∀ t ∈ uIcc a b, 1 < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have ht0 : ∀ t ∈ uIcc a b, 0 < t := fun t ht => zero_lt_one.trans (ht1 t ht)
  have hlog : ∀ t ∈ uIcc a b, 0 < Real.log t := fun t ht => Real.log_pos (ht1 t ht)
  let w' : ℝ → ℝ := fun t => ω / (c * t * (Real.log t) ^ 2)
  apply growing_weight_sine_integral_bound hab hω (w' := w')
  · intro t ht
    have hct : c * Real.log t ≠ 0 := mul_ne_zero hc.ne' (hlog t ht).ne'
    have hd := (hasDerivAt_const t ω).div
      ((Real.hasDerivAt_log (ht0 t ht).ne').const_mul c) hct
    have he : w' t = -((0 * (c * Real.log t) - ω * (c * t⁻¹)) /
        (c * Real.log t) ^ 2) := by
      dsimp [w']
      field_simp [hc.ne', (ht0 t ht).ne', (hlog t ht).ne']
      ring
    rw [he]
    exact HasDerivAt.const_sub 1 hd
  · have hlc : ContinuousOn Real.log (uIcc a b) :=
      continuousOn_id.log (fun t ht => (ht0 t ht).ne')
    have hdc : ContinuousOn w' (uIcc a b) :=
      continuousOn_const.div
        ((continuousOn_const.mul continuousOn_id).mul (hlc.pow 2))
        (fun t ht => by
          have := ht0 t ht
          have := hlog t ht
          positivity)
    exact hdc.intervalIntegrable
  · intro t ht
    have ht' : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
    dsimp [w']
    have := ht0 t ht'
    positivity
  · intro t ht
    have ht' : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hden : 0 < c * Real.log t := mul_pos hc (hlog t ht')
    have hentryt : ω ≤ c * Real.log t :=
      hentry.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (zero_lt_one.trans ha) ht.1) hc.le)
    constructor
    · exact sub_nonneg.mpr ((div_le_one hden).mpr hentryt)
    · have := div_nonneg hω.le hden.le
      linarith

/-- The entry profile with a logarithmically growing cutoff, before and after admission. -/
noncomputable def logEntryWeight (c ω t : ℝ) : ℝ :=
  max (1 - ω / (c * Real.log (max t 2))) 0

theorem logEntryWeight_continuous {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    Continuous (logEntryWeight c ω) := by
  have hlog : Continuous (fun t : ℝ => Real.log (max t 2)) :=
    (continuous_id.max continuous_const).log (fun t => by
      change max t 2 ≠ 0
      have := le_max_right t (2 : ℝ)
      linarith)
  have hden : ∀ t : ℝ, c * Real.log (max t 2) ≠ 0 := by
    intro t
    apply mul_ne_zero hc.ne'
    exact (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right t 2))).ne'
  exact (continuous_const.sub (continuous_const.div
    (continuous_const.mul hlog) hden)).max continuous_const

/-- Admission at `exp(ω/c)` contributes no boundary jump to the primitive estimate. -/
theorem logEntryWeight_sine_integral_bound {c ω T : ℝ} (hc : 0 < c) (hω : 0 < ω)
    (hentry : c * Real.log 2 ≤ ω) (hT : 0 ≤ T) :
    |∫ t in (0 : ℝ)..T, logEntryWeight c ω t * Real.sin (t * ω)| ≤ 2 / ω := by
  let a := Real.exp (ω / c)
  have ha2 : 2 ≤ a := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  have ha1 : 1 < a := by linarith
  have ha0 : 0 ≤ a := by linarith
  have halog : c * Real.log a = ω := by
    dsimp [a]
    rw [Real.log_exp]
    field_simp [hc.ne']
  have hwzero : ∀ t : ℝ, t ≤ a → logEntryWeight c ω t = 0 := by
    intro t ht
    have hp : 0 < c * Real.log (max t 2) := mul_pos hc
      (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right t 2)))
    have hh : c * Real.log (max t 2) ≤ ω := by
      rw [← halog]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right t 2))
          (max_le ht ha2)) hc.le
    unfold logEntryWeight
    exact max_eq_right (sub_nonpos.mpr ((one_le_div hp).mpr hh))
  have hwactive : ∀ t : ℝ, a ≤ t →
      logEntryWeight c ω t = 1 - ω / (c * Real.log t) := by
    intro t ht
    have hp : 0 < c * Real.log t := mul_pos hc (Real.log_pos (ha1.trans_le ht))
    have hh : ω ≤ c * Real.log t := by
      rw [← halog]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) ht) hc.le
    unfold logEntryWeight
    rw [max_eq_left (ha2.trans ht)]
    exact max_eq_left (sub_nonneg.mpr ((div_le_one hp).mpr hh))
  have hcont : Continuous (fun t : ℝ => logEntryWeight c ω t * Real.sin (t * ω)) :=
    (logEntryWeight_continuous hc ω).mul (by fun_prop)
  have hzero {B : ℝ} (hB0 : 0 ≤ B) (hBa : B ≤ a) :
      (∫ t in (0 : ℝ)..B, logEntryWeight c ω t * Real.sin (t * ω)) = 0 := by
    calc (∫ t in (0 : ℝ)..B, logEntryWeight c ω t * Real.sin (t * ω))
        = ∫ t in (0 : ℝ)..B, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hB0] at ht
          dsimp only
          rw [hwzero t (ht.2.trans hBa), zero_mul]
      _ = 0 := by simp
  by_cases hTa : T ≤ a
  · rw [hzero hT hTa, abs_zero]
    positivity
  · have haT : a ≤ T := (lt_of_not_ge hTa).le
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a T), hzero ha0 le_rfl,
      zero_add]
    have heq : (∫ t in a..T, logEntryWeight c ω t * Real.sin (t * ω)) =
        ∫ t in a..T, (1 - ω / (c * Real.log t)) * Real.sin (t * ω) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le haT] at ht
      dsimp only
      rw [hwactive t ht.1]
    rw [heq]
    exact active_log_weight_sine_integral_bound haT ha1 hc hω halog.ge

end CriticalLinePhasor

#print axioms CriticalLinePhasor.growing_weight_sine_integral_bound
#print axioms CriticalLinePhasor.active_log_weight_sine_integral_bound
#print axioms CriticalLinePhasor.logEntryWeight_sine_integral_bound
