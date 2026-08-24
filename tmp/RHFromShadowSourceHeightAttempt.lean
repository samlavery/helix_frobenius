import RequestProject.XiCarrierShadow
import RequestProject.RiemannHypothesisBridge

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- Strategy A: reindex an arbitrary analytic zero through its canonical physical height. -/
noncomputable def shadowOfXiZero_sourceHeight (rho : XiZeroIndex) : XiCarrierShadow := by
  let fiber := principalZeroAnalyticFiber3D rho.property
  refine
    { height := fiber.sourceHeight
      height_pos := fiber.sourceHeight_pos
      xi_zero := ?_ }
  exact (ZD.riemannXi_eq_zero_iff rho.val).mpr rho.property

end CriticalLinePhasor.ContourArgument
