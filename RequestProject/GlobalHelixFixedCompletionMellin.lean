import RequestProject.GlobalHelixFixedCompletionKernel
import RequestProject.CarrierThetaIdentification

/-!
# Mellin identification of a fixed archimedean completion clock

The clock is defined on the three-dimensional carrier before any coefficient bank is attached.
Its Mellin transform is Deligne's prescribed complex-place Gamma factor.  Thus the completion
multiplier is read from the fixed geometric clock rather than synthesized from Euler coefficients.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- Absolute Mellin convergence of one fixed archimedean clock in its natural half-plane. -/
theorem gammaClock_mellinConvergent (μ s : ℂ) (hs : 0 < (s + μ).re) :
    MellinConvergent (gammaClock μ) s := by
  have hbase : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s + μ) := by
    rw [MellinConvergent]
    simpa [smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent hs)
  have hscale : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscaled :
      MellinConvergent (fun t : ℝ => (Real.exp (-((2 * Real.pi : ℝ) * t)) : ℂ))
        (s + μ) := by
    simpa only using
      ((MellinConvergent.comp_mul_left hscale).2 hbase)
  have hpow :
      MellinConvergent
        (fun t : ℝ => (t : ℂ) ^ μ * (Real.exp (-((2 * Real.pi : ℝ) * t)) : ℂ)) s := by
    exact (MellinConvergent.cpow_smul (E := ℂ)).2 hscaled
  have hconst := hpow.const_smul (2 : ℂ)
  have hexp : ∀ t : ℝ,
      Complex.exp (-(2 * Real.pi : ℂ) * t) =
        (Real.exp (-((2 * Real.pi : ℝ) * t)) : ℂ) := by
    intro t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold gammaClock
  convert hconst using 1
  funext t
  rw [hexp t]
  simp [smul_eq_mul]
  ring

/-- The fixed Gamma clock has exactly Deligne's complex-place Gamma multiplier. -/
theorem gammaClock_mellin (μ s : ℂ) (hs : 0 < (s + μ).re) :
    mellin (gammaClock μ) s = Complex.Gammaℂ (s + μ) := by
  have hscale : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  unfold mellin gammaClock
  simp only [smul_eq_mul]
  have hint :
      (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) *
          (2 * (t : ℂ) ^ μ * Complex.exp (-(2 * Real.pi : ℂ) * t))) =
        2 * ∫ t : ℝ in Ioi 0,
          (t : ℂ) ^ (s + μ - 1) *
            Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [show (t : ℂ) ^ (s + μ - 1) =
        (t : ℂ) ^ (s - 1) * (t : ℂ) ^ μ by
      rw [show s + μ - 1 = (s - 1) + μ by ring, Complex.cpow_add _ _ ht0]]
    push_cast
    ring
  rw [hint]
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hscale]
  rw [Complex.Gammaℂ_def]
  have hbase : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbase]
  have hpow : ((1 / ((2 * Real.pi : ℝ) : ℂ)) ^ (s + μ)) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (-(s + μ)) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg]
      · exact ne_of_lt Real.pi_pos
      · positivity), ← Complex.cpow_neg]
  rw [hpow]
  ring

/-- The singleton completion kernel is the fixed clock and has the same Mellin multiplier. -/
theorem completionKernel_singleton_hasMellin (μ s : ℂ) (hs : 0 < (s + μ).re) :
    HasMellin (completionKernel [μ]) s (Complex.Gammaℂ (s + μ)) := by
  rw [completionKernel_singleton]
  exact ⟨gammaClock_mellinConvergent μ s hs, gammaClock_mellin μ s hs⟩

/-- A positive geometric height scale carries the square-root conductor. -/
noncomputable def conductorScaledGammaClock (C : ℝ) (μ : ℂ) (x : ℝ) : ℂ :=
  gammaClock μ (x / C)

/-- Read the conductor-scaled fixed clock from the third coordinate of a 3D carrier point. -/
noncomputable def conductorScaledGammaClockReadout (C : ℝ) (μ : ℂ) (f : ConeProjection.Fiber) : ℂ :=
  conductorScaledGammaClock C μ (multiplicativeHeight f)

/-- Conductor scaling preserves Mellin convergence. -/
theorem conductorScaledGammaClock_mellinConvergent
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hs : 0 < (s + μ).re) :
    MellinConvergent (conductorScaledGammaClock C μ) s := by
  have hscale : 0 < C⁻¹ := inv_pos.mpr hC
  have hfun : conductorScaledGammaClock C μ =
      fun x : ℝ => gammaClock μ (C⁻¹ * x) := by
    funext x
    simp [conductorScaledGammaClock, div_eq_inv_mul]
  rw [hfun, MellinConvergent.comp_mul_left hscale]
  exact gammaClock_mellinConvergent μ s hs

/-- Scaling the 3D height by `C` contributes exactly `C^s`; for `C = sqrt N` this is the
classical conductor factor `N^(s/2)`. -/
theorem conductorScaledGammaClock_mellin
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hs : 0 < (s + μ).re) :
    mellin (conductorScaledGammaClock C μ) s =
      (C : ℂ) ^ s * Complex.Gammaℂ (s + μ) := by
  have hscale : 0 < C⁻¹ := inv_pos.mpr hC
  have hfun : conductorScaledGammaClock C μ =
      fun x : ℝ => gammaClock μ (C⁻¹ * x) := by
    funext x
    simp [conductorScaledGammaClock, div_eq_inv_mul]
  rw [hfun, mellin_comp_mul_left (gammaClock μ) s hscale,
    gammaClock_mellin μ s hs]
  simp only [smul_eq_mul]
  have hcast : ((C⁻¹ : ℝ) : ℂ) = (C : ℂ)⁻¹ := by push_cast; rfl
  rw [hcast, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hC.le]
    exact ne_of_lt Real.pi_pos), Complex.cpow_neg, inv_inv]

theorem conductorScaledGammaClock_hasMellin
    (C : ℝ) (hC : 0 < C) (μ s : ℂ) (hs : 0 < (s + μ).re) :
    HasMellin (conductorScaledGammaClock C μ) s
      ((C : ℂ) ^ s * Complex.Gammaℂ (s + μ)) :=
  ⟨conductorScaledGammaClock_mellinConvergent C hC μ s hs,
    conductorScaledGammaClock_mellin C hC μ s hs⟩

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gammaClock_mellinConvergent
#print axioms CriticalLinePhasor.GlobalHelix.gammaClock_mellin
#print axioms CriticalLinePhasor.GlobalHelix.completionKernel_singleton_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledGammaClock_mellinConvergent
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledGammaClock_mellin
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledGammaClock_hasMellin
