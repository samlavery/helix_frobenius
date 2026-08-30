import RequestProject.XiStructureFunction
import RequestProject.JKernelSignLaw
import RequestProject.XiKernelThetaBridge
import RequestProject.SeatScalarCriterion
import RequestProject.DVPSeatRungOne
import RequestProject.DVPSeatRealPart

/-!
Axiom bucket audit for every declaration the C3 / IsHB backward chain consumes.

Bucketing rule for the ledger:
  A  exactly [propext, Classical.choice, Quot.sound]
  B  a named dependency with a transitive discharger
  C  a target / undischarged Prop -- becomes the recursive target
-/

section TargetAndConnector
#print axioms CriticalLinePhasor.XiStructure.rh_of_xiStructure_isHB
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Estar
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Acomp
#print axioms CriticalLinePhasor.XiStructure.xiStructure_Bcomp
#print axioms CriticalLinePhasor.DeBranges.Acomp_zero_im_eq_zero
#print axioms CriticalLinePhasor.DeBranges.norm_eq_imp_im_zero
#print axioms CriticalLinePhasor.DeBranges.hb_lower
end TargetAndConnector

section Seat
#print axioms CriticalLinePhasor.SeatScalar.seat_criterion_iff
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_identity
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_online
#print axioms CriticalLinePhasor.SeatScalar.exists_seat_energy_neg
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_outside_strip
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_depth
#print axioms CriticalLinePhasor.SeatScalar.depth_criterion_iff
#print axioms CriticalLinePhasor.DVP.seat_energy_re_eq
#print axioms CriticalLinePhasor.DVP.xi_logDeriv_one_sub_conj
#print axioms CriticalLinePhasor.DVP.seat_interior_rung_one'
end Seat

section KernelSide
#print axioms CriticalLinePhasor.JKernel.jKernel_pairing_nonpos
#print axioms CriticalLinePhasor.JKernel.jKernel_neg
#print axioms CriticalLinePhasor.JKernel.phiEven_nonneg
#print axioms CriticalLinePhasor.XiKernelBridge.riemannXiKernel_eq_psi_operator
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_pos
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.riemannXiKernel_neg
end KernelSide

section FEsupport
#print axioms CriticalLinePhasor.ContourArgument.riemannXi_conj
#print axioms CriticalLinePhasor.DVP.deriv_xi_conj
#print axioms CriticalLinePhasor.DVP.deriv_xi_one_sub
#print axioms ZD.ZeroCount.riemannXi_one_sub
#print axioms ZD.ZeroCount.riemannXi_zero_of_mem_NontrivialZeros
end FEsupport
