import RequestProject.DVPWindowCount

/-!
# The θ asymptotic and the textbook Riemann–von Mangoldt formula

`θ(T) = (T/2)·log(T/2π) − T/2 + O(1)`: the clock's exact primitive plus the
integrated Stirling error (`∫ 10/t² ≤ 1`).  Combined with 413 this yields
the classical count `N(T) = (T/2π)·log(T/2π) − T/2π + 1 + O(log T)`.
UNCONDITIONAL.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The Stirling main term's derivative:
`d/dt [(t/2)·log(t/2π) − t/2] = (1/2)·log(t/2π)`. -/
theorem main_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (s/2) * Real.log (s/(2*Real.pi)) - s/2)
      ((1/2) * Real.log (t/(2*Real.pi))) t := by
  have hπ := Real.pi_pos
  have harg : t / (2*Real.pi) ≠ 0 := by positivity
  have hlog : HasDerivAt (fun s : ℝ => Real.log (s/(2*Real.pi)))
      (1/t) t := by
    have hdiv : HasDerivAt (fun s : ℝ => s/(2*Real.pi))
        (1/(2*Real.pi)) t := by
      simpa using (hasDerivAt_id t).div_const (2*Real.pi)
    have hcomp := (Real.hasDerivAt_log harg).comp t hdiv
    have hval : (t/(2*Real.pi))⁻¹ * (1/(2*Real.pi)) = 1/t := by
      field_simp
    rw [← hval]
    exact hcomp
  have hhalf : HasDerivAt (fun s : ℝ => s/2) (1/2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hmul := hhalf.mul hlog
  have hmul' : HasDerivAt (fun s : ℝ => (s/2) * Real.log (s/(2*Real.pi)))
      ((1/2) * Real.log (t/(2*Real.pi)) + (t/2) * (1/t)) t := hmul
  have hsub := hmul'.sub hhalf
  have hval : (1/2) * Real.log (t/(2*Real.pi)) + (t/2) * (1/t) - 1/2
      = (1/2) * Real.log (t/(2*Real.pi)) := by
    field_simp
    ring
  rw [← hval]
  exact hsub

/-- The inverse-square primitive: `d/dt (−10/t) = 10/t²`. -/
theorem inv_sq_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -(10/s)) (10/t^2) t := by
  have h2 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t :=
    hasDerivAt_inv (ne_of_gt ht)
  have h3 := h2.const_mul (10:ℝ)
  have hfun : (fun s : ℝ => (10:ℝ) * s⁻¹) = fun s : ℝ => 10/s := by
    funext s
    rw [← div_eq_mul_inv]
  rw [hfun] at h3
  have h4 := h3.neg
  have hval : -((10:ℝ) * -(t^2)⁻¹) = 10/t^2 := by
    field_simp
  rw [← hval]
  exact h4

/-- **The θ asymptotic**: `|θ(T) − ((T/2)·log(T/2π) − T/2)| ≤ C` for all
`T ≥ 10`, with the constant anchored at `T = 10`. -/
theorem theta_asymptotic :
    ∃ C : ℝ, ∀ T : ℝ, 10 ≤ T →
      |theta T - ((T/2) * Real.log (T/(2*Real.pi)) - T/2)| ≤ C := by
  refine ⟨|theta 10 - ((10/2) * Real.log (10/(2*Real.pi)) - 10/2)| + 1, ?_⟩
  intro T hT
  have hπ := Real.pi_pos
  have hcont_main : ContinuousOn
      (fun t : ℝ => (1/2) * Real.log (t/(2*Real.pi))) (Set.Icc 10 T) := by
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    have h1 : ContinuousAt (fun t : ℝ => t/(2*Real.pi)) t :=
      continuousAt_id.div_const _
    have h2 : ContinuousAt Real.log (t/(2*Real.pi)) :=
      Real.continuousAt_log (by positivity)
    have h3 : ContinuousAt (Real.log ∘ fun t : ℝ => t/(2*Real.pi)) t :=
      ContinuousAt.comp h2 h1
    exact (continuousAt_const.mul h3).continuousWithinAt
  have hθftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := theta) (f' := clockRate) (a := 10) (b := T)
    (fun t _ => theta_hasDerivAt t)
    (continuous_clockRate.intervalIntegrable _ _)
  have hint_main : IntervalIntegrable
      (fun t : ℝ => (1/2) * Real.log (t/(2*Real.pi)))
      MeasureTheory.volume 10 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hcont_main
  have hmftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => (s/2) * Real.log (s/(2*Real.pi)) - s/2)
    (f' := fun t => (1/2) * Real.log (t/(2*Real.pi)))
    (a := 10) (b := T)
    (fun t htm => main_hasDerivAt (by
      rw [Set.uIcc_of_le hT] at htm
      linarith [htm.1]))
    hint_main
  -- the pointwise Stirling error
  have hpt : ∀ t ∈ Set.Icc (10:ℝ) T,
      |clockRate t - (1/2) * Real.log (t/(2*Real.pi))| ≤ 10/t^2 := by
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    have habs : |t| = t := abs_of_pos ht0
    have hmu := mu_stirling_explicit (τ := t) (by rw [habs]; linarith [htm.1])
    rw [habs] at hmu
    have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
    have hkey : clockRate t - (1/2) * Real.log (t/(2*Real.pi))
        = Real.pi * (Zeta23.mu t
            - 1/(2*Real.pi) * Real.log (t/(2*Real.pi))) := by
      rw [hcr]
      field_simp
    rw [hkey, abs_mul, abs_of_pos hπ]
    calc Real.pi * |Zeta23.mu t - 1/(2*Real.pi) * Real.log (t/(2*Real.pi))|
        ≤ Real.pi * ((10/Real.pi)/t^2) :=
          mul_le_mul_of_nonneg_left hmu hπ.le
      _ = 10/t^2 := by field_simp
  -- the integrated error
  have hint_diff : IntervalIntegrable
      (fun t : ℝ => clockRate t - (1/2) * Real.log (t/(2*Real.pi)))
      MeasureTheory.volume 10 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact continuous_clockRate.continuousOn.sub hcont_main
  have hint_sq : IntervalIntegrable (fun t : ℝ => 10/t^2)
      MeasureTheory.volume 10 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    exact (continuousAt_const.div ((continuous_pow 2).continuousAt)
      (by positivity)).continuousWithinAt
  have hsqftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => -(10/s)) (f' := fun t => 10/t^2)
    (a := 10) (b := T)
    (fun t htm => inv_sq_hasDerivAt (by
      rw [Set.uIcc_of_le hT] at htm
      linarith [htm.1]))
    hint_sq
  have hdiff_bound : |∫ t in (10:ℝ)..T,
      (clockRate t - (1/2) * Real.log (t/(2*Real.pi)))| ≤ 1 := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => clockRate t - (1/2) * Real.log (t/(2*Real.pi)))
      (μ := MeasureTheory.volume) hT
    have h2 : (∫ t in (10:ℝ)..T,
        |clockRate t - (1/2) * Real.log (t/(2*Real.pi))|)
        ≤ ∫ t in (10:ℝ)..T, 10/t^2 :=
      intervalIntegral.integral_mono_on hT hint_diff.abs hint_sq hpt
    have h3 : (∫ t in (10:ℝ)..T, 10/t^2 : ℝ) = -(10/T) - -(10/10) := hsqftc
    have h4 : -(10/T) - -(10/10 : ℝ) ≤ 1 := by
      have hpos : (0:ℝ) < 10/T := by positivity
      have heq : -(10/T) - -(10/10 : ℝ) = 1 - 10/T := by
        norm_num
        ring
      linarith [heq.le, heq.ge]
    linarith [h1, h2, h3.le, h3.ge, h4]
  -- assemble
  have hsplit : theta T - ((T/2) * Real.log (T/(2*Real.pi)) - T/2)
      = (theta 10 - ((10/2) * Real.log (10/(2*Real.pi)) - 10/2))
        + ∫ t in (10:ℝ)..T,
            (clockRate t - (1/2) * Real.log (t/(2*Real.pi))) := by
    have hsub := intervalIntegral.integral_sub
      (continuous_clockRate.intervalIntegrable _ _) hint_main
    linarith [hθftc, hmftc, hsub]
  rw [hsplit]
  calc |(theta 10 - ((10/2) * Real.log (10/(2*Real.pi)) - 10/2))
        + ∫ t in (10:ℝ)..T,
            (clockRate t - (1/2) * Real.log (t/(2*Real.pi)))|
      ≤ |theta 10 - ((10/2) * Real.log (10/(2*Real.pi)) - 10/2)|
        + |∫ t in (10:ℝ)..T,
            (clockRate t - (1/2) * Real.log (t/(2*Real.pi)))| :=
        abs_add_le _ _
    _ ≤ |theta 10 - ((10/2) * Real.log (10/(2*Real.pi)) - 10/2)| + 1 := by
        linarith [hdiff_bound]

/-- **The textbook Riemann–von Mangoldt formula**:
`|N(T) − ((T/2π)·log(T/2π) − T/2π) − 1| ≤ 20·log T + C` at good heights. -/
theorem riemann_von_mangoldt_classical :
    ∃ C : ℝ, ∀ T : ℝ, Real.exp 6 ≤ T → ∀ hT : GoodHeight T,
      |(stripZeroCountMult T : ℝ)
        - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi)) - 1|
      ≤ 20 * Real.log T + C := by
  obtain ⟨Cθ, hCθ⟩ := theta_asymptotic
  have hπ := Real.pi_pos
  refine ⟨3 + Cθ/Real.pi, ?_⟩
  intro T h6 hT
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
      have h33 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h66 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h3, Real.exp_pos 3]
  have hrvm := riemann_von_mangoldt h6 hT
  have hθ := hCθ T (by linarith)
  have hθπ : |theta T / Real.pi
      - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi))|
      ≤ Cθ / Real.pi := by
    have hkey : theta T / Real.pi
        - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi))
        = (theta T - ((T/2) * Real.log (T/(2*Real.pi)) - T/2)) / Real.pi := by
      field_simp
    rw [hkey, abs_div, abs_of_pos hπ]
    gcongr
  have htri : |(stripZeroCountMult T : ℝ)
      - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi)) - 1|
      ≤ |(stripZeroCountMult T : ℝ) - theta T / Real.pi - 1|
        + |theta T / Real.pi
            - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi))| := by
    have heq : (stripZeroCountMult T : ℝ)
        - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi)) - 1
        = ((stripZeroCountMult T : ℝ) - theta T / Real.pi - 1)
          + (theta T / Real.pi
              - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi))) := by
      ring
    rw [heq]
    exact abs_add_le _ _
  calc |(stripZeroCountMult T : ℝ)
      - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi)) - 1|
      ≤ |(stripZeroCountMult T : ℝ) - theta T / Real.pi - 1|
        + |theta T / Real.pi
            - ((T/(2*Real.pi)) * Real.log (T/(2*Real.pi)) - T/(2*Real.pi))| :=
        htri
    _ ≤ (20 * Real.log T + 3) + Cθ / Real.pi := by
        linarith [hrvm, hθπ]
    _ = 20 * Real.log T + (3 + Cθ/Real.pi) := by ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.main_hasDerivAt
#print axioms CriticalLinePhasor.DVP.theta_asymptotic
#print axioms CriticalLinePhasor.DVP.riemann_von_mangoldt_classical
end AxiomAudit
