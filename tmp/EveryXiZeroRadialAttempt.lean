import RequestProject.XiCarrierShadow
import RequestProject.RadialBoundedness

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

theorem everyXiZero_online_radial_attempt (rho : XiZeroIndex) : rho.val.re = 1 / 2 := by
  let fiber := principalZeroAnalyticFiber3D rho.property
  have hpair := paired_areaNormalizedRadialMagnitude_tendsto_one rho.property
  have hbalanced : CarrierScaleBalanced rho.val.re := by
    apply fiber.carrierScaleBalanced_iff_radialMagnitude.mpr
    exact ⟨1, by norm_num, hpair⟩
  exact (carrierScaleBalanced_iff rho.val.re).1 hbalanced

end CriticalLinePhasor.ContourArgument
