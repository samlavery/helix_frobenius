import RequestProject.DVPWeightedIBP
import RequestProject.DVPLittlewoodTheorem

/-!
# The weighted ledger is `O(log²)`

Substituting Littlewood (411) into the exception-free IBP identity (420):
`|∫₁₀ᵀ S_all·(1/2π)·log(t/2π) dt| ≤ 2C_L·(1 + log(1+T))²` — the ε-chain's
boundary excess in `S_all` form, sublinear in the cell count.
UNCONDITIONAL.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The weighted ledger bound**: the clock-weighted running integral of
the full ledger is `O(log²)`. -/
theorem sall_weighted_log_sq_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 10 ≤ T →
      |∫ t in (10:ℝ)..T,
          SAll t * ((1/(2*Real.pi)) * Real.log (t/(2*Real.pi)))|
        ≤ C * (1 + Real.log (1 + T))^2 := by
  obtain ⟨CL, hCL⟩ := littlewoodBound_holds
  have hCL0 : (0:ℝ) ≤ CL := by
    have h := hCL 0 (le_refl 0)
    rw [intervalIntegral.integral_same] at h
    simpa using h
  have hπ := Real.pi_pos
  have h2π10 : 2 * Real.pi ≤ 10 := by
    nlinarith [Real.pi_lt_d4]
  -- the running-integral bound from base 10
  have hFb : ∀ t : ℝ, 10 ≤ t →
      |∫ s in (10:ℝ)..t, SAll s| ≤ 2*CL*(1 + Real.log (1+t)) := by
    intro t ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (sall_intervalIntegrable 0 10) (sall_intervalIntegrable 10 t)
    have h1 := hCL t (by linarith)
    have h2 := hCL 10 (by norm_num)
    have hlogmono : (1:ℝ) + Real.log (1+10) ≤ 1 + Real.log (1+t) := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 1+10)
        (by linarith : (1:ℝ)+10 ≤ 1+t)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogmono hCL0
    have habs : |∫ s in (10:ℝ)..t, SAll s|
        ≤ |∫ s in (0:ℝ)..t, SAll s| + |∫ s in (0:ℝ)..10, SAll s| := by
      have heq : ∫ s in (10:ℝ)..t, SAll s
          = (∫ s in (0:ℝ)..t, SAll s) - ∫ s in (0:ℝ)..10, SAll s := by
        linarith [hadj]
      rw [heq, sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    linarith [habs, h1, h2, hmul]
  refine ⟨2*CL, by linarith, ?_⟩
  intro T hT
  have hL0 : (0:ℝ) ≤ Real.log (1+T) := Real.log_nonneg (by linarith)
  set L : ℝ := 1 + Real.log (1+T) with hLdef
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef]
    linarith
  -- weight bounds at T
  have hlogT : Real.log (T/(2*Real.pi)) ≤ Real.log (1+T) := by
    apply Real.log_le_log
    · have : (1:ℝ) ≤ T / (2*Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
  have hlogT0 : (0:ℝ) ≤ Real.log (T/(2*Real.pi)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hw0 : (0:ℝ) ≤ (1/(2*Real.pi)) * Real.log (T/(2*Real.pi)) := by
    positivity
  have hwle : (1/(2*Real.pi)) * Real.log (T/(2*Real.pi)) ≤ (1/2) * L := by
    have h1 : (1:ℝ)/(2*Real.pi) ≤ 1/2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_gt_three]
    have h2 : Real.log (T/(2*Real.pi)) ≤ L := by
      rw [hLdef]
      linarith
    calc (1/(2*Real.pi)) * Real.log (T/(2*Real.pi))
        ≤ (1/2) * Real.log (T/(2*Real.pi)) :=
          mul_le_mul_of_nonneg_right h1 hlogT0
      _ ≤ (1/2) * L := by linarith
  -- rewrite by the IBP identity
  rw [sall_weighted_ibp (by norm_num : (0:ℝ) < 10) hT]
  -- term 1
  have hT1 : |(∫ s in (10:ℝ)..T, SAll s)
      * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))|
      ≤ CL * L^2 := by
    rw [abs_mul, abs_of_nonneg hw0]
    have h1 := hFb T hT
    have h2 : |∫ s in (10:ℝ)..T, SAll s| * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))
        ≤ (2*CL*L) * ((1/2) * L) := by
      apply mul_le_mul _ hwle hw0 _
      · rw [hLdef]
        exact h1
      · nlinarith [hL1]
    calc |∫ s in (10:ℝ)..T, SAll s|
          * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))
        ≤ (2*CL*L) * ((1/2) * L) := h2
      _ = CL * L^2 := by ring
  -- term 2
  have hFcont : Continuous (fun u : ℝ => ∫ s in (10:ℝ)..u, SAll s) :=
    intervalIntegral.continuous_primitive
      (fun b c => sall_intervalIntegrable b c) 10
  have hT2 : |∫ t in (10:ℝ)..T,
      (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))|
      ≤ CL * L^2 := by
    have hint_f : IntervalIntegrable
        (fun t : ℝ => (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t)))
        MeasureTheory.volume 10 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      apply hFcont.continuousOn.mul
      intro t htm
      have ht0 : (0:ℝ) < t := by linarith [htm.1]
      exact (continuousAt_const.div
        (continuousAt_const.mul continuousAt_id)
        (ne_of_gt (mul_pos (mul_pos two_pos Real.pi_pos) ht0))).continuousWithinAt
    have hint_g : IntervalIntegrable
        (fun t : ℝ => (2*CL*L) * (1/(2*Real.pi*t)))
        MeasureTheory.volume 10 T := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hT]
      intro t htm
      have ht0 : (0:ℝ) < t := by linarith [htm.1]
      exact (continuousAt_const.mul (continuousAt_const.div
        (continuousAt_const.mul continuousAt_id)
        (ne_of_gt (mul_pos (mul_pos two_pos Real.pi_pos) ht0)))).continuousWithinAt
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun t : ℝ => (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t)))
      (μ := MeasureTheory.volume) hT
    have hmono : (∫ t in (10:ℝ)..T,
        |(∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))|)
        ≤ ∫ t in (10:ℝ)..T, (2*CL*L) * (1/(2*Real.pi*t)) := by
      apply intervalIntegral.integral_mono_on hT hint_f.abs hint_g
      intro t htm
      have ht0 : (0:ℝ) < t := by linarith [htm.1]
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi*t))]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc |∫ s in (10:ℝ)..t, SAll s|
          ≤ 2*CL*(1 + Real.log (1+t)) := hFb t htm.1
        _ ≤ 2*CL*L := by
            rw [hLdef]
            have hlm : Real.log (1+t) ≤ Real.log (1+T) :=
              Real.log_le_log (by linarith) (by linarith [htm.2])
            nlinarith [hCL0]
    -- the explicit weight integral
    have hwftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => (1/(2*Real.pi)) * Real.log t)
      (f' := fun t : ℝ => 1/(2*Real.pi*t))
      (a := 10) (b := T)
      (fun t htm => by
        rw [Set.uIcc_of_le hT] at htm
        have ht0 : (0:ℝ) < t := by linarith [htm.1]
        have h := (Real.hasDerivAt_log (ne_of_gt ht0)).const_mul (1/(2*Real.pi))
        have hval : (1/(2*Real.pi)) * t⁻¹ = 1/(2*Real.pi*t) := by
          field_simp
        rw [← hval]
        exact h)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hT]
        intro t htm
        have ht0 : (0:ℝ) < t := by linarith [htm.1]
        exact (continuousAt_const.div
          (continuousAt_const.mul continuousAt_id)
          (ne_of_gt (mul_pos (mul_pos two_pos Real.pi_pos) ht0))).continuousWithinAt)
    have hwint : (∫ t in (10:ℝ)..T, (1/(2*Real.pi*t)))
        ≤ (1/2) * L := by
      rw [hwftc]
      have hlog10 : (0:ℝ) ≤ Real.log 10 := Real.log_nonneg (by norm_num)
      have hlogTle : Real.log T ≤ L := by
        rw [hLdef]
        have := Real.log_le_log (by linarith : (0:ℝ) < T)
          (by linarith : T ≤ 1 + T)
        linarith
      have h1 : (1:ℝ)/(2*Real.pi) ≤ 1/2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Real.pi_gt_three]
      have hlogT0' : (0:ℝ) ≤ Real.log T :=
        Real.log_nonneg (by linarith)
      have hL0' : (0:ℝ) ≤ L := by linarith
      calc (1/(2*Real.pi)) * Real.log T - (1/(2*Real.pi)) * Real.log 10
          ≤ (1/(2*Real.pi)) * Real.log T := by
            have : (0:ℝ) ≤ (1/(2*Real.pi)) * Real.log 10 := by positivity
            linarith
        _ ≤ (1/2) * Real.log T :=
            mul_le_mul_of_nonneg_right h1 hlogT0'
        _ ≤ (1/2) * L := by linarith
    have hconst : (∫ t in (10:ℝ)..T, (2*CL*L) * (1/(2*Real.pi*t)))
        = (2*CL*L) * ∫ t in (10:ℝ)..T, (1/(2*Real.pi*t)) :=
      intervalIntegral.integral_const_mul _ _
    have hCLL : (0:ℝ) ≤ 2*CL*L := by nlinarith [hCL0, hL1]
    calc |∫ t in (10:ℝ)..T,
        (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))|
        ≤ ∫ t in (10:ℝ)..T,
            |(∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))| := habs
      _ ≤ ∫ t in (10:ℝ)..T, (2*CL*L) * (1/(2*Real.pi*t)) := hmono
      _ = (2*CL*L) * ∫ t in (10:ℝ)..T, (1/(2*Real.pi*t)) := hconst
      _ ≤ (2*CL*L) * ((1/2) * L) :=
          mul_le_mul_of_nonneg_left hwint hCLL
      _ = CL * L^2 := by ring
  -- assemble
  have htri : |(∫ s in (10:ℝ)..T, SAll s)
      * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))
      - ∫ t in (10:ℝ)..T,
          (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))|
      ≤ |(∫ s in (10:ℝ)..T, SAll s)
          * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))|
        + |∫ t in (10:ℝ)..T,
            (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))| := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  calc |(∫ s in (10:ℝ)..T, SAll s)
      * ((1/(2*Real.pi)) * Real.log (T/(2*Real.pi)))
      - ∫ t in (10:ℝ)..T,
          (∫ s in (10:ℝ)..t, SAll s) * (1/(2*Real.pi*t))|
      ≤ CL * L^2 + CL * L^2 := by
        linarith [htri, hT1, hT2]
    _ = 2*CL * L^2 := by ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sall_weighted_log_sq_bound
end AxiomAudit
