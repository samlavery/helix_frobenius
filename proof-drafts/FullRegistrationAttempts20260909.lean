import RequestProject.LittlewoodRegisterDoor

open Complex Filter Topology MeasureTheory Asymptotics
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.rh_of_smultIntegralSublinear
#print axioms CriticalLinePhasor.DVP.littlewood_o_input_holds

-- Strategy A: transfer the existing full-register lower bound through the integral split.
example : RiemannHypothesis := by
  apply rh_of_smultIntegralSublinear
  intro ε hε
  have hsmall := littlewood_o_input_holds.bound hε
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  change ‖∫ t in (0 : ℝ)..T, SAll t‖ ≤ ε * ‖T‖ at hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hT
  have hlower := (abs_le.mp hT).1
  rw [integral_smult_split]
  have hmass : 0 ≤ ∫ t in (0 : ℝ)..T, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hT0 (fun t _ => Nat.cast_nonneg _)
  linarith

-- Strategy C: return to the bank's native/unit warp identity, retaining multiplicities.
example : RiemannHypothesis := by
  apply rh_of_smultIntegralSublinear
  have hregister : ∀ t : ℝ, SAll t = Smult t := by
    intro t
    have hwarp := CriticalLinePhasor.CarrierScale.carrier_scale_compensation_S t
    have hmult := Smult_sub_S t
    change Smult t + (offLineStripZeroCountMult t : ℝ) = Smult t
    linarith only [hwarp, hmult]
  have hsub := littlewood_o_input_holds
  change (fun T => ∫ t in (0 : ℝ)..T, SAll t) =o[atTop] (fun T : ℝ => T) at hsub
  simp only [hregister] at hsub
  intro ε hε
  filter_upwards [hsub.bound hε, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0] at hT
  exact (abs_le.mp hT).1
