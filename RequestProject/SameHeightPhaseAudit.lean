import RequestProject.TwoEndedJState
import RequestProject.ThreeDFocalEvent
import RequestProject.CarrierHamiltonian

/-!
The phase link that precedes the requested same-height S/focal test.
The warp in these statements is the existing heat operator, not CarrierScale.S.
No S-dependent focal invariant is asserted or introduced.
-/

noncomputable section

namespace CriticalLinePhasor.SameHeightPhaseAudit

open Complex TwoEndedJState

/-- The focal spin is the eigenvalue of the existing imaginary-time heat operator. -/
theorem focalPhase_eq_warpPhase (t : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin t (n + 1) =
      ((n : ℂ) + 1) ^ (-(Complex.I * (t : ℂ))) := by
  rw [CarrierReadout.heat_eigenvalue_eq_exp]
  unfold LFunctionPhasor.mellinSpin CarrierReadout.logWeight
  congr 1
  push_cast
  ring

/-- The same phase acts on the actual phasor eigenvector of the heat operator. -/
theorem heat_phasor_focalPhase (t : ℝ) (n : ℕ) :
    CarrierReadout.heat (Complex.I * (t : ℂ))
        ⟨CarrierReadout.phasor n, CarrierReadout.phasor_mem_cweightDomain _ n⟩ =
      LFunctionPhasor.mellinSpin t (n + 1) • CarrierReadout.phasor n := by
  rw [CarrierReadout.heat_phasor, focalPhase_eq_warpPhase]

/-- The focal frequency is the logarithm of the normalized wound-site arclength.
This uses the defining winding theorem, rather than assigning identical phase formulas. -/
theorem focalPhase_eq_woundSitePhase (p r : ℝ) (hr : 0 < r) (t : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin t (n + 1) =
      Complex.exp (-(Complex.I * (t : ℂ)) *
        (Real.log (Geometry.arclength p r
          (Geometry.windParameter p r (Geometry.spinAngle (n + 1))) /
            (Real.pi / 3)) : ℂ)) := by
  rw [(Geometry.windParameter_spec p r _ hr (Geometry.spinAngle_nonneg _)).2]
  have hsite : Geometry.spinAngle (n + 1) / (Real.pi / 3) = (n : ℝ) + 1 := by
    unfold Geometry.spinAngle
    rw [mul_div_cancel_right₀ _ (div_ne_zero Real.pi_ne_zero (by norm_num))]
    push_cast
    rfl
  rw [hsite, focalPhase_eq_warpPhase, CarrierReadout.heat_eigenvalue_eq_exp]
  rfl

/-- The already-selected carrier datum retains its amplitude and heat phase at the first end.
There is no free exponent in this statement. -/
theorem selected_endPhasor_eq_heatPhase (t : ℝ) (n : ℕ) :
    endPhasor (chartData ThreeDFocal.carrierAbscissa) t n =
      (-1 : ℂ) ^ n * ((((n : ℝ) + 1) ^ (-ThreeDFocal.carrierAbscissa) : ℝ) : ℂ) *
        ((n : ℂ) + 1) ^ (-(Complex.I * (t : ℂ))) := by
  unfold endPhasor chartData
  rw [focalPhase_eq_warpPhase]

/-- The second end transports the same selected amplitude and reverses the heat time. -/
theorem selected_jEndPhasor_eq_heatPhase (t : ℝ) (n : ℕ) :
    jEndPhasor (chartData ThreeDFocal.carrierAbscissa) t n =
      (-1 : ℂ) ^ n * ((((n : ℝ) + 1) ^ (-ThreeDFocal.carrierAbscissa) : ℝ) : ℂ) *
        ((n : ℂ) + 1) ^ (-(Complex.I * ((-t : ℝ) : ℂ))) := by
  rw [jEndPhasor_eq, focalPhase_eq_warpPhase]
  simp only [chartData, map_pow, map_neg, map_one]

end CriticalLinePhasor.SameHeightPhaseAudit
