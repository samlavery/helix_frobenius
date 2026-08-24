import RequestProject.XiCarrierShadow
import RequestProject.RiemannHypothesisBridge

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

/-- Strategy C: turn the registered carrier event into a completed 3D zero at its height. -/
theorem completedThreeDZero_of_registeredXiZero
    (chiOne : DirichletCharacter ℂ 1) (rho : XiZeroIndex) :
    CompletedThreeDZeroAtHeight chiOne
      (principalZeroAnalyticFiber3D rho.property).sourceHeight := by
  let event := principalZero_focalCancellation_on_carrier rho.property
  exact event.focalCancellation

end CriticalLinePhasor.ContourArgument
