import RequestProject.HelixCancellationProjection
import RequestProject.ZetaZeroDefs

/-!
# What the construction writes (ledger 1266)

The two-ended construction writes a point `s` when its configuration at some physical height `Z` cancels and the
post-cancellation eigenstate projects to `s` (3D → 2D → 1D).

* `written_on_line`: **it writes nothing off the line.** Every written point has real part `½` and is a zero.
* `written_of_on_line`: it writes every zero on the line.
* `written_iff`: it writes exactly the zeros on the line.
* `nontrivialZeros_on_line_of_written`: if every nontrivial zero is written, every nontrivial zero lies on the line.
  The hypothesis is `EveryZeroHasSource` read through this construction.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.HelixWrittenZeros

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.FocalLine
  CriticalLinePhasor.HelixTwoEndedCancellation CriticalLinePhasor.HelixFootMass
  CriticalLinePhasor.HelixCancellationProjection

/-- The construction writes `s`: at some height `Z` the two-ended configuration cancels and the post-cancellation
eigenstate projects to `s`. -/
def Written (s : ℂ) : Prop :=
  ∃ Z hc : ℝ, ∃ hZ : 0 < Z, (twoEndedConfig Z hc).Cancels ∧ chartOf (cancellationEigenstate Z hc hZ) = s

/-- **The construction writes nothing off the line**: every written point is a zero with real part `½`. -/
theorem written_on_line {s : ℂ} (h : Written s) : s.re = 1 / 2 ∧ riemannZeta s = 0 := by
  obtain ⟨Z, hc, hZ, hcan, rfl⟩ := h
  refine ⟨?_, projection_commutes hZ hcan⟩
  rw [eigenstate_chart, HelixCancellationProjection.carrierPointAtHeight_eq]
  simp

/-- The construction writes every zero on the line. -/
theorem written_of_on_line {s : ℂ} (hre : s.re = 1 / 2) (hz : riemannZeta s = 0) : Written s := by
  refine ⟨Real.exp s.im, 0, Real.exp_pos _, ?_, ?_⟩
  · exact (zero_on_chart_line_iff (by rw [hre, carrierAbscissa_eq_half]) 0).mp hz
  · rw [eigenstate_chart, HelixCancellationProjection.carrierPointAtHeight_eq, Real.log_exp]
    apply Complex.ext <;> simp [hre]

/-- **The construction writes exactly the zeros on the line.** -/
theorem written_iff (s : ℂ) : Written s ↔ s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  ⟨written_on_line, fun h => written_of_on_line h.1 h.2⟩

/-- If every nontrivial zero is written by the construction, every nontrivial zero lies on the line. -/
theorem nontrivialZeros_on_line_of_written (h : ∀ ρ ∈ ZD.NontrivialZeros, Written ρ) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 :=
  fun ρ hρ => (written_on_line (h ρ hρ)).1

end CriticalLinePhasor.HelixWrittenZeros

end

#print axioms CriticalLinePhasor.HelixWrittenZeros.written_on_line
#print axioms CriticalLinePhasor.HelixWrittenZeros.written_iff
#print axioms CriticalLinePhasor.HelixWrittenZeros.nontrivialZeros_on_line_of_written
