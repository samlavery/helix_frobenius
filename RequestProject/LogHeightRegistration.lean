import RequestProject.LittlewoodRegisterDoor

noncomputable section

open Filter Topology MeasureTheory
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump

namespace CriticalLinePhasor.DVP

/-- Integration in the carrier's physical height uses logarithmic measure. -/
theorem integral_logHeight (f : ℝ → ℝ) (a b : ℝ) :
    (∫ Z in Real.exp a..Real.exp b, f (Real.log Z) / Z) =
      ∫ t in a..b, f t := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := a) (b := b) (f := Real.exp) (f' := Real.exp)
    (g := fun Z => f (Real.log Z) / Z)
    Real.continuous_exp.continuousOn
    (fun t _ => Real.hasDerivAt_exp t) (fun t _ => (Real.exp_pos t).le)
  simpa [Function.comp_def, Real.log_exp, Real.exp_ne_zero] using h.symm

/-- The change of variable also preserves integrability of the jump registers. -/
theorem intervalIntegrable_logHeight_iff (f : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun Z => f (Real.log Z) / Z) volume (Real.exp a) (Real.exp b) ↔
      IntervalIntegrable f volume a b := by
  have h := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := a) (b := b) (f := Real.exp) (f' := Real.exp)
    (g := fun Z => f (Real.log Z) / Z)
    Real.continuous_exp.continuousOn
    (fun t _ => Real.hasDerivAt_exp t) (fun t _ => (Real.exp_pos t).le)
  simpa [Function.comp_def, Real.log_exp, Real.exp_ne_zero] using h.symm

/-- The multiplicity register, integrated at physical carrier heights. -/
theorem smult_integral_logHeight (T : ℝ) :
    (∫ Z in (1 : ℝ)..Real.exp T, Smult (Real.log Z) / Z) =
      ∫ t in (0 : ℝ)..T, Smult t := by
  simpa using integral_logHeight Smult 0 T

/-- The complete register retains the off-line contribution under the same substitution. -/
theorem integral_logHeight_register_split (T : ℝ) :
    (∫ Z in (1 : ℝ)..Real.exp T, Smult (Real.log Z) / Z) =
      (∫ Z in (1 : ℝ)..Real.exp T, SAll (Real.log Z) / Z) -
        ∫ Z in (1 : ℝ)..Real.exp T,
          (offLineStripZeroCountMult (Real.log Z) : ℝ) / Z := by
  simpa only [Real.exp_zero] using
    (integral_logHeight Smult 0 T).trans
      ((integral_smult_split T).trans (by
        rw [← Real.exp_zero, integral_logHeight SAll,
          integral_logHeight (fun t => (offLineStripZeroCountMult t : ℝ))]))

/-- Littlewood's actual bound in the physical-height chart. -/
theorem littlewood_logHeight_bound :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      |∫ Z in (1 : ℝ)..Real.exp T, SAll (Real.log Z) / Z| ≤
        C * (1 + Real.log (1 + T)) := by
  obtain ⟨C, hC⟩ := littlewoodBound_holds
  refine ⟨C, fun T hT => ?_⟩
  simpa only [← Real.exp_zero, integral_logHeight] using hC T hT

/-- The resulting lower bound for the multiplicity register, retaining the correction mass. -/
theorem smult_logHeight_lower :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      -(C * (1 + Real.log (1 + T))) -
          (∫ Z in (1 : ℝ)..Real.exp T,
            (offLineStripZeroCountMult (Real.log Z) : ℝ) / Z) ≤
        ∫ Z in (1 : ℝ)..Real.exp T, Smult (Real.log Z) / Z := by
  obtain ⟨C, hC⟩ := littlewood_logHeight_bound
  refine ⟨C, fun T hT => ?_⟩
  rw [integral_logHeight_register_split]
  exact sub_le_sub_right (abs_le.mp (hC T hT)).1 _

end CriticalLinePhasor.DVP

#print axioms CriticalLinePhasor.DVP.integral_logHeight
#print axioms CriticalLinePhasor.DVP.intervalIntegrable_logHeight_iff
#print axioms CriticalLinePhasor.DVP.smult_integral_logHeight
#print axioms CriticalLinePhasor.DVP.integral_logHeight_register_split
#print axioms CriticalLinePhasor.DVP.littlewood_logHeight_bound
#print axioms CriticalLinePhasor.DVP.smult_logHeight_lower
