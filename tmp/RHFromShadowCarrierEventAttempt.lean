import RequestProject.XiCarrierShadow
import RequestProject.RiemannHypothesisBridge

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- Strategy B: reindex an arbitrary analytic zero through its registered carrier event. -/
noncomputable def shadowOfXiZero_carrierEvent (rho : XiZeroIndex) : XiCarrierShadow := by
  let event := principalZero_focalCancellation_on_carrier rho.property
  refine
    { height := event.analyticFiber.sourceHeight
      height_pos := event.analyticFiber.sourceHeight_pos
      xi_zero := ?_ }
  exact event.focalCancellation

end CriticalLinePhasor.ContourArgument
