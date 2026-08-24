import RequestProject.XiCarrierShadow
import RequestProject.RadialBoundedness

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.XiChannel

theorem everyXiZero_hasCarrierShadow :
    Function.Surjective XiCarrierShadow.toXiZeroIndex := by
  apply XiCarrierShadow.toXiZeroIndex_surjective_iff.mpr
  intro rho

end CriticalLinePhasor.ContourArgument
