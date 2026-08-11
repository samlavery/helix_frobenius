import RequestProject.Sym2RankinCapstone
import RequestProject.CPSSynthesizedKernelControl

open CriticalLinePhasor

-- file 1
#print axioms CriticalLinePhasor.Sym2Join.symClock_prod_eq_zpow
#print axioms CriticalLinePhasor.Sym2Join.radialLocalEulerCoeff_symClock_eq_sym2Coeff
-- file 2
#print axioms CriticalLinePhasor.Sym2Join.radialGlobal_eq_symrBank
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_sqIndicator
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_rankinSquareNorm
#print axioms CriticalLinePhasor.Sym2Join.isMultiplicative_sym2Bank
#print axioms CriticalLinePhasor.Sym2Join.symrBank_two_eq_sym2Bank
#print axioms CriticalLinePhasor.Sym2Join.radialGlobal_eq_sym2Bank
-- file 3
#print axioms CriticalLinePhasor.Sym2Rankin.radialLocalEulerCoeff_rankinWeight
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Coeff_inv
#print axioms CriticalLinePhasor.Sym2Rankin.rankinBank_prime_pow
#print axioms CriticalLinePhasor.Sym2Rankin.satake_uniform_bound
#print axioms CriticalLinePhasor.Sym2Rankin.rankinSatakePair
#print axioms CriticalLinePhasor.Sym2Rankin.rankinPrimalCoeff_eq
#print axioms CriticalLinePhasor.Sym2Rankin.rankinDualCoeff_eq
-- file 4
#print axioms CriticalLinePhasor.Sym2Rankin.LSeries_rankinBank
#print axioms CriticalLinePhasor.Sym2Rankin.completionKernelLog_pair_continuousOn
#print axioms CriticalLinePhasor.Sym2Rankin.rankin_readout_gammaC
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_primal_line
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_dual_line
#print axioms CriticalLinePhasor.Sym2Rankin.sym2RankinCoupling
#print axioms CriticalLinePhasor.Sym2Rankin.sym2RankinPair
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_selfdual_FE
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_lambda_eq
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_residue
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_entire
-- file 5
#print axioms CriticalLinePhasor.Sym2Rankin.sym2Rankin_lambda_eq'
#print axioms CriticalLinePhasor.Sym2Rankin.sym2_rankin_rung
-- file 6
#print axioms CriticalLinePhasor.GlobalHelix.cpsPrimal3DBankReadout_eq_carrier
#print axioms CriticalLinePhasor.GlobalHelix.cpsPrimal3DBankReadout_independent_of_satake
-- upstream load-bearing
#print axioms CriticalLinePhasor.Unfolding.averagedTheta_inv
#print axioms CriticalLinePhasor.ThreeDConverse.eqOn_pos_of_mellin_eqOn_line
#print axioms CriticalLinePhasor.GlobalHelix.WeakBankThetaProfileCoupling3D.toWeakFEPair
#print axioms CriticalLinePhasor.Sym2Registration.peeledFE
#print axioms CriticalLinePhasor.Sym2Registration.peeled_edge_regularity
#print axioms CriticalLinePhasor.Sym2Wire.sym2_euler_identity

-- statement strength: the exact types
#check @CriticalLinePhasor.Sym2Rankin.sym2_rankin_rung
#check @CriticalLinePhasor.Sym2Rankin.sym2Rankin_selfdual_FE
#check @CriticalLinePhasor.Sym2Wire.HeckeEigenData
#check @CriticalLinePhasor.ThreeDConverse.eqOn_pos_of_mellin_eqOn_line
#check @CriticalLinePhasor.Unfolding.averagedTheta_inv
