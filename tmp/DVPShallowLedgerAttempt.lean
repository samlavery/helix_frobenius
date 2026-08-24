import RequestProject.DVPLedgerSuite

open Filter Asymptotics
open CriticalLinePhasor.ContourArgument

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Direct attempt to close the registration defect from the unconditional
Littlewood input. -/
theorem integratedDefect_sublinear_attempt :
    (fun T => ∫ t in (0 : ℝ)..T, (offLineStripZeroCountMult t : ℝ))
      =o[atTop] (fun T : ℝ => T) := by
  exact suite_o_input

end CriticalLinePhasor.DVP
