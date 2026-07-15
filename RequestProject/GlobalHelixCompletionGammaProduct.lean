import RequestProject.GlobalHelixLogMellinConvolution

/-!
# The complete fixed archimedean Gamma product

Every archimedean clock is fixed before the Euler bank is attached.  Signed-log convolution
assembles the clocks, and the Mellin product theorem identifies the resulting kernel with the full
product of Deligne Gamma factors.  Positive height scaling contributes the conductor factor.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

/-- A nonempty archimedean clock list assembled in native signed-log height. -/
noncomputable def completionKernelLog : List ℂ → ℝ → ℂ
  | [] => fun _ => 0
  | [μ] => gammaClock μ
  | μ :: ν :: rest => logMellinConvolution (gammaClock μ) (completionKernelLog (ν :: rest))

/-- The assembled fixed kernel has the complete product of its prescribed Gamma multipliers. -/
theorem completionKernelLog_hasMellin
    (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (completionKernelLog μs) s
      ((μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  induction μs with
  | nil => exact (hne rfl).elim
  | cons μ tail ih =>
      cases tail with
      | nil =>
          simpa [completionKernelLog] using
            (show HasMellin (gammaClock μ) s (Complex.Gammaℂ (s + μ)) from
              ⟨gammaClock_mellinConvergent μ s (hs μ (by simp)),
                gammaClock_mellin μ s (hs μ (by simp))⟩)
      | cons ν rest =>
          have hμ : HasMellin (gammaClock μ) s (Complex.Gammaℂ (s + μ)) :=
            ⟨gammaClock_mellinConvergent μ s (hs μ (by simp)),
              gammaClock_mellin μ s (hs μ (by simp))⟩
          have htail := ih (by simp) (fun z hz => hs z (by simp [hz]))
          have hconv := logMellinConvolution_hasMellin
            (gammaClock μ) (completionKernelLog (ν :: rest)) s hμ.1 htail.1
          refine ⟨?_, ?_⟩
          · simpa [completionKernelLog] using hconv.1
          · rw [show completionKernelLog (μ :: ν :: rest) =
                logMellinConvolution (gammaClock μ) (completionKernelLog (ν :: rest)) by rfl,
              hconv.2, hμ.2, htail.2]
            simp

/-- Add the square-root conductor as a geometric scale of the assembled clock. -/
noncomputable def conductorScaledCompletionKernelLog
    (C : ℝ) (μs : List ℂ) (x : ℝ) : ℂ :=
  completionKernelLog μs (x / C)

/-- The complete fixed kernel reads `C^s` times the full Gamma product. -/
theorem conductorScaledCompletionKernelLog_hasMellin
    (C : ℝ) (hC : 0 < C) (μs : List ℂ) (hne : μs ≠ []) (s : ℂ)
    (hs : ∀ μ ∈ μs, 0 < (s + μ).re) :
    HasMellin (conductorScaledCompletionKernelLog C μs) s
      ((C : ℂ) ^ s * (μs.map fun μ => Complex.Gammaℂ (s + μ)).prod) := by
  have hbase := completionKernelLog_hasMellin μs hne s hs
  have hscale : 0 < C⁻¹ := inv_pos.mpr hC
  have hfun : conductorScaledCompletionKernelLog C μs =
      fun x : ℝ => completionKernelLog μs (C⁻¹ * x) := by
    funext x
    simp [conductorScaledCompletionKernelLog, div_eq_inv_mul]
  have hconv : MellinConvergent (conductorScaledCompletionKernelLog C μs) s := by
    rw [hfun, MellinConvergent.comp_mul_left hscale]
    exact hbase.1
  refine ⟨hconv, ?_⟩
  rw [hfun, mellin_comp_mul_left (completionKernelLog μs) s hscale, hbase.2]
  simp only [smul_eq_mul]
  have hcast : ((C⁻¹ : ℝ) : ℂ) = (C : ℂ)⁻¹ := by push_cast; rfl
  rw [hcast, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hC.le]
    exact ne_of_lt Real.pi_pos), Complex.cpow_neg, inv_inv]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.completionKernelLog_hasMellin
#print axioms CriticalLinePhasor.GlobalHelix.conductorScaledCompletionKernelLog_hasMellin
