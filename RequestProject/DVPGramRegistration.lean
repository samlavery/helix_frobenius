import RequestProject.DVPGramCells
import RequestProject.ClockChartCellResidue

/-!
# The registration chain instantiated on the harmonized cells

On the compiled π-cells (`exists_gram_cells`, 385) with the explicit rate
floor `1/10`, the clock-chart identification's hypothesis list reduces to
the two register residuals plus Littlewood: mass, boundary accumulation,
and the o(T) input.  Monotonicity, positivity of the base, unboundedness,
and the rate floor are DISCHARGED at the concrete object.
-/

open CriticalLinePhasor.CarrierScale CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.ResidueJump
open Filter Topology

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The identification on the harmonized cells**: there is a concrete
π-cell decomposition on which the global coordinate identification
(`classicalSContour = Smult` at every good height) follows from the two
register residuals and Littlewood alone. -/
theorem gram_registration_reduction :
    ∃ c : ℕ → ℝ, c 0 = 10 ∧ Monotone c
      ∧ (∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
      ∧ (ClockCellMassBounded c →
          BoundaryLogAccumulation c →
          ((fun T => ∫ t in (0:ℝ)..T,
              (Smult t + (offLineStripZeroCountMult t : ℝ)))
            =o[atTop] fun T : ℝ => T) →
          ∀ (T : ℝ) (hT : GoodHeight T), classicalSContour hT = Smult T) := by
  obtain ⟨c, hc0, hmono, hten, hspan, htop⟩ := exists_gram_cells
  refine ⟨c, hc0, hmono, hspan, ?_⟩
  intro hmass hbdry hLittlewood
  have hc0' : (0:ℝ) ≤ c 0 := by
    rw [hc0]
    norm_num
  have hrate : ∀ n, ∀ t ∈ Set.Icc (c n) (c (n + 1)),
      (1/10 : ℝ) ≤ clockRate t := by
    intro n t ht
    exact clockRate_floor (le_trans (hten n) ht.1)
  exact globalCoordinateIdentification_of_clockInputs hmono hc0' htop
    (by norm_num : (0:ℝ) < 1/10) hrate hmass hbdry hLittlewood

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.gram_registration_reduction
end AxiomAudit
