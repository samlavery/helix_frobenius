import Mathlib

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The real FE-pair expression in the user's `(y,a,d)` coordinates. -/
def fePairContribution (y a d : ℝ) : ℝ :=
  2 * y * ((a ^ 2 - y ^ 2) - d ^ 2) /
    (((a - y) ^ 2 + d ^ 2) * ((a + y) ^ 2 + d ^ 2))

/-- A conjugate quartet is not termwise nonpositive: the resonant FE pair
dominates its conjugate pair at the reflected ordinate in this exact rational test. -/
theorem feQuartet_resonant_countertest :
    0 < fePairContribution (1 / 10) (1 / 4) 0
      + fePairContribution (1 / 10) (1 / 4) (1 / 4) := by
  norm_num [fePairContribution]

/-- At the ordinate of a deep zero, no positive tube-separation parameter can
satisfy the premise used by `seat_channel_off_tubes`. -/
theorem no_positive_tube_separation_at_same_ordinate
    {w ρ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hordinate : ρ.im = w.re) :
    ¬ δ ≤ |ρ.im - w.re| := by
  rw [hordinate]
  simp
  exact hδ

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.feQuartet_resonant_countertest
#print axioms CriticalLinePhasor.DVP.no_positive_tube_separation_at_same_ordinate
end AxiomAudit
