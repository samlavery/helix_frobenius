import RequestProject.XiCarrierShadow

open Complex

noncomputable section

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor
open CriticalLinePhasor.XiChannel

theorem everyXiZero_online_operator_attempt (rho : XiZeroIndex) : rho.val.re = 1 / 2 := by
  have hsym : xiZeroLedgerOperator.IsSymmetric :=
    xiZeroLedgerNoDriftProjection_isSymmetric
  have hpole := xiZeroLedgerOperator_symmetric_imp_poleParam_real hsym rho
  rw [HelixLimit.poleParam_im] at hpole
  linarith

end CriticalLinePhasor.ContourArgument
