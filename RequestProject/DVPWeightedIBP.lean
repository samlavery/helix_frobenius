import RequestProject.DVPSAllContinuity

/-!
# The weighted IBP identity for the full ledger

Exception-free (419): `S_all` is right-continuous everywhere, so its
primitive has a right-derivative everywhere, and the right-derivative FTC
applies to `G = F·w₀` on the nose:

`∫ₐᵀ S_all·w₀ = F(T)·w₀(T) − ∫ₐᵀ F·w₀′`,  `w₀(t) = (1/2π)·log(t/2π)`.

This is the identity that converts Littlewood's `F = O(log)` into the
`O(log²)` bound on the weighted (clock-measure) ledger.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `S_all` is measurable. -/
theorem sall_measurable : Measurable SAll := by
  have hsplit : SAll = fun s : ℝ =>
      (stripZeroCountMult s : ℝ) - 1 - theta s / Real.pi := by
    funext s
    rw [SAll, Smult]
    have h := stripZeroCountMult_eq_line_add_offLine s
    have hR : (stripZeroCountMult s : ℝ)
        = (zeroEventCountMult s : ℝ) + (offLineStripZeroCountMult s : ℝ) := by
      exact_mod_cast h
    linarith [hR]
  rw [hsplit]
  have h1 : Measurable (fun t : ℝ => (stripZeroCountMult t : ℝ)) :=
    measurable_from_top.comp stripZeroCountMult_mono.measurable
  exact (h1.sub measurable_const).sub
    ((continuous_theta.measurable).div_const _)

/-- The log-weight's derivative: `d/dt log(t/2π) = 1/t`. -/
theorem hasDerivAt_log_over_two_pi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log (s/(2*Real.pi))) (1/t) t := by
  have hπ := Real.pi_pos
  have harg : t / (2*Real.pi) ≠ 0 := by positivity
  have hdiv : HasDerivAt (fun s : ℝ => s/(2*Real.pi))
      (1/(2*Real.pi)) t := by
    simpa using (hasDerivAt_id t).div_const (2*Real.pi)
  have hcomp := (Real.hasDerivAt_log harg).comp t hdiv
  have hval : (t/(2*Real.pi))⁻¹ * (1/(2*Real.pi)) = 1/t := by
    field_simp
  rw [← hval]
  exact hcomp

/-- **The weighted IBP identity** (exception-free):
`∫ₐᵀ S_all(t)·(1/2π)·log(t/2π) dt
  = F(T)·(1/2π)·log(T/2π) − ∫ₐᵀ F(t)·(1/(2πt)) dt`
with `F(u) = ∫ₐᵘ S_all`. -/
theorem sall_weighted_ibp {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ t in a..T, SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi)))
      = (∫ s in a..T, SAll s) * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))
        - ∫ t in a..T, (∫ s in a..t, SAll s) * (1/(2*Real.pi*t)) := by
  have hπ := Real.pi_pos
  set F : ℝ → ℝ := fun u => ∫ s in a..u, SAll s with hFdef
  set w : ℝ → ℝ := fun t => (1/(2*Real.pi)) * Real.log (t/(2*Real.pi))
    with hwdef
  -- continuity of the primitive and the weight
  have hFcont : Continuous F :=
    intervalIntegral.continuous_primitive
      (fun b c => sall_intervalIntegrable b c) a
  have hwcont : ContinuousOn w (Set.Icc a T) := by
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    have h1 : ContinuousAt (fun t : ℝ => t/(2*Real.pi)) t :=
      continuousAt_id.div_const _
    have h2 : ContinuousAt Real.log (t/(2*Real.pi)) :=
      Real.continuousAt_log (by positivity)
    have h3 : ContinuousAt (Real.log ∘ fun t : ℝ => t/(2*Real.pi)) t :=
      ContinuousAt.comp h2 h1
    exact (continuousAt_const.mul h3).continuousWithinAt
  -- the right derivative of G = F·w on the interior
  have hG_deriv : ∀ t ∈ Set.Ioo a T,
      HasDerivWithinAt (fun u => F u * w u)
        (SAll t * w t + F t * ((1/(2*Real.pi)) * (1/t))) (Set.Ioi t) t := by
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    have hFd : HasDerivWithinAt F (SAll t) (Set.Ioi t) t := by
      have h := intervalIntegral.integral_hasDerivWithinAt_right
        (f := SAll) (a := a) (b := t)
        (s := Set.Ici t) (t := Set.Ioi t)
        (sall_intervalIntegrable a t)
        (sall_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter)
        ((sall_continuousWithinAt_right ht0).mono Set.Ioi_subset_Ici_self)
      exact h.mono Set.Ioi_subset_Ici_self
    have hwd : HasDerivWithinAt w ((1/(2*Real.pi)) * (1/t)) (Set.Ioi t) t := by
      have h := (hasDerivAt_log_over_two_pi ht0).const_mul (1/(2*Real.pi))
      exact h.hasDerivWithinAt
    exact hFd.mul hwd
  -- continuity of G on the closed interval
  have hG_cont : ContinuousOn (fun u => F u * w u) (Set.Icc a T) :=
    hFcont.continuousOn.mul hwcont
  -- integrability of the derivative
  have hint1 : IntervalIntegrable
      (fun t => SAll t * w t) MeasureTheory.volume a T := by
    apply IntervalIntegrable.mul_continuousOn (sall_intervalIntegrable a T)
    rw [Set.uIcc_of_le haT]
    exact hwcont
  have hint2 : IntervalIntegrable
      (fun t => F t * ((1/(2*Real.pi)) * (1/t))) MeasureTheory.volume a T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haT]
    apply hFcont.continuousOn.mul
    intro t htm
    have ht0 : (0:ℝ) < t := by linarith [htm.1]
    exact (continuousAt_const.mul
      ((continuousAt_const.div continuousAt_id (ne_of_gt ht0)))).continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => SAll t * w t + F t * ((1/(2*Real.pi)) * (1/t)))
      MeasureTheory.volume a T := hint1.add hint2
  -- the right-derivative FTC
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    haT hG_cont hG_deriv hint
  -- split and rearrange
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  have hFa : F a = 0 := intervalIntegral.integral_same
  rw [hFa, zero_mul, sub_zero] at hftc
  have hval : ∀ t : ℝ, F t * ((1/(2*Real.pi)) * (1/t))
      = F t * (1/(2*Real.pi*t)) := by
    intro t
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0]
      norm_num
    · field_simp
  have hcong : (∫ t in a..T, F t * ((1/(2*Real.pi)) * (1/t)))
      = ∫ t in a..T, F t * (1/(2*Real.pi*t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact hval t
  rw [hcong] at hftc
  linarith [hftc]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sall_measurable
#print axioms CriticalLinePhasor.DVP.hasDerivAt_log_over_two_pi
#print axioms CriticalLinePhasor.DVP.sall_weighted_ibp
end AxiomAudit
