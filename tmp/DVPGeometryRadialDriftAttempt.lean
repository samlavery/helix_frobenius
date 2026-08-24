import RequestProject.ZetaZeroNative3DSourceTransfer

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- Geometry-first construction of zero radial drift on every analytic zero mode. -/
theorem xiRadialDriftOperator_eq_zero_of_geometry_attempt :
    xiRadialDriftOperator = 0 := by
  apply xiRadialDriftOperator_eq_zero_iff_all_scaleBalanced.mpr
  intro rho
  let event := principalZero_focalCancellation_on_carrier rho.property
  have hgeometry := event.carrierReadout_scaleBalanced
  apply (carrierScaleBalanced_iff rho.val.re).2
  exact (carrierScaleBalanced_iff
    (carrierPointAtHeight event.analyticFiber.sourceHeight).re).1 hgeometry

end CriticalLinePhasor.ContourArgument
