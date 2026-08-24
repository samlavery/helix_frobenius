import RequestProject.DVPLittlewoodTheorem

/-!
# The Riemann–von Mangoldt formula, compiled

`N_all(T) = θ(T)/π + 1 + O(log T)`: the full-strip multiplicity census
equals the clock count up to the explicit Backlund error `20·log T + 3`,
at every good height above `e⁶`.  Pure assembly: the census identity
(att246) + the Backlund bound + the count split.  UNCONDITIONAL.
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **Riemann–von Mangoldt**: `|N_all(T) − θ(T)/π − 1| ≤ 20·log T + 3` at
every good height `T ≥ e⁶`. -/
theorem riemann_von_mangoldt {T : ℝ} (h6 : Real.exp 6 ≤ T)
    (hT : GoodHeight T) :
    |(stripZeroCountMult T : ℝ) - theta T / Real.pi - 1|
      ≤ 20 * Real.log T + 3 := by
  have hback := abs_classicalSContour_le h6 hT
  have hcensus := classicalSContour_eq_Smult_add_offLine hT
  have hsplit := stripZeroCountMult_eq_line_add_offLine T
  have hsplitR : (stripZeroCountMult T : ℝ)
      = (zeroEventCountMult T : ℝ) + (offLineStripZeroCountMult T : ℝ) := by
    exact_mod_cast hsplit
  have hkey : classicalSContour hT
      = (stripZeroCountMult T : ℝ) - theta T / Real.pi - 1 := by
    rw [hcensus]
    unfold Smult
    linarith [hsplitR]
  rw [← hkey]
  exact hback

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.riemann_von_mangoldt
end AxiomAudit
