import RequestProject.CPSCompletionUnification3D
import RequestProject.RepresentationRankGap
import RequestProject.NonSelfDualObstruction
import RequestProject.DualPairFiber

/-!
# Arithmetic CPS twists on the three-dimensional carrier

This file removes two ambiguities from the polynomial CPS interface.

First, the rank `(r+1)m` local bank is constructed from a rank-two Satake pair and a rank-`m`
twist by the literal symmetric-power tensor monomials.  The local Euler polynomial and the global
Dirichlet coefficients consumed by the carrier are therefore definitionally the arithmetic ones;
there is no second, freely chosen coefficient family to identify afterward.

Second, residual extinction is stated only for equivariant maps.  The target is a simple module
over the representation algebra, and the strict complex-rank inequality is used only after a
nonzero intertwiner would have become surjective.  The companion `FDRep` theorem uses Schur's
lemma to exclude a trivial constituent from a simple representation not isomorphic to the unit.
-/

open Complex Module
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- The literal local roots of `Sym^r(pi) tensor tau`, retaining both arithmetic radii of `pi`. -/
noncomputable def arithmeticCPSTensorRoot
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (p : Nat.Primes) (i : CPSTensorIndex r m) : ℂ :=
  pi.primal p 0 ^ (r - i.1.1) * pi.primal p 1 ^ i.1.1 * tau.primal p i.2

/-- The literal contragredient roots of the same arithmetic tensor. -/
noncomputable def arithmeticCPSDualTensorRoot
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (p : Nat.Primes) (i : CPSTensorIndex r m) : ℂ :=
  pi.dual p 0 ^ (r - i.1.1) * pi.dual p 1 ^ i.1.1 * tau.dual p i.2

theorem arithmeticCPSDualTensorRoot_eq_inv
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (p : Nat.Primes) (i : CPSTensorIndex r m) :
    arithmeticCPSDualTensorRoot r m pi tau p i =
      (arithmeticCPSTensorRoot r m pi tau p i)⁻¹ := by
  simp only [arithmeticCPSDualTensorRoot, arithmeticCPSTensorRoot,
    pi.dual_eq_inv, tau.dual_eq_inv, inv_pow]
  ring

private theorem arithmeticCPSTensorRoot_bound
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (p : Nat.Primes) (i : CPSTensorIndex r m) :
    ‖arithmeticCPSTensorRoot r m pi tau p i‖ ≤
      (p.1 : ℝ) ^ (r * pi.primalExponent + tau.primalExponent) := by
  have hp : 0 ≤ (p.1 : ℝ) := by positivity
  have hj : i.1.1 ≤ r := Nat.le_of_lt_succ i.1.2
  calc
    ‖arithmeticCPSTensorRoot r m pi tau p i‖ =
        ‖pi.primal p 0‖ ^ (r - i.1.1) *
          ‖pi.primal p 1‖ ^ i.1.1 * ‖tau.primal p i.2‖ := by
            simp [arithmeticCPSTensorRoot, norm_pow]
    _ ≤ ((p.1 : ℝ) ^ pi.primalExponent) ^ (r - i.1.1) *
          ((p.1 : ℝ) ^ pi.primalExponent) ^ i.1.1 *
            (p.1 : ℝ) ^ tau.primalExponent := by
          gcongr
          · exact pi.primal_bound p 0
          · exact pi.primal_bound p 1
          · exact tau.primal_bound p i.2
    _ = (p.1 : ℝ) ^ (r * pi.primalExponent + tau.primalExponent) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [← Nat.mul_add, Nat.sub_add_cancel hj, Nat.mul_comm]

private theorem arithmeticCPSDualTensorRoot_bound
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (p : Nat.Primes) (i : CPSTensorIndex r m) :
    ‖arithmeticCPSDualTensorRoot r m pi tau p i‖ ≤
      (p.1 : ℝ) ^ (r * pi.dualExponent + tau.dualExponent) := by
  have hp : 0 ≤ (p.1 : ℝ) := by positivity
  have hj : i.1.1 ≤ r := Nat.le_of_lt_succ i.1.2
  calc
    ‖arithmeticCPSDualTensorRoot r m pi tau p i‖ =
        ‖pi.dual p 0‖ ^ (r - i.1.1) *
          ‖pi.dual p 1‖ ^ i.1.1 * ‖tau.dual p i.2‖ := by
            simp [arithmeticCPSDualTensorRoot, norm_pow]
    _ ≤ ((p.1 : ℝ) ^ pi.dualExponent) ^ (r - i.1.1) *
          ((p.1 : ℝ) ^ pi.dualExponent) ^ i.1.1 *
            (p.1 : ℝ) ^ tau.dualExponent := by
          gcongr
          · exact pi.dual_bound p 0
          · exact pi.dual_bound p 1
          · exact tau.dual_bound p i.2
    _ = (p.1 : ℝ) ^ (r * pi.dualExponent + tau.dualExponent) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [← Nat.mul_add, Nat.sub_add_cancel hj, Nat.mul_comm]

/-- The polynomial CPS datum constructed from the actual rank-two and rank-`m` local roots. -/
noncomputable def arithmeticCPSPolynomialTwist
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) : CPSPolynomialTwist r m where
  primal := arithmeticCPSTensorRoot r m pi tau
  dual := arithmeticCPSDualTensorRoot r m pi tau
  primalExponent := r * pi.primalExponent + tau.primalExponent
  dualExponent := r * pi.dualExponent + tau.dualExponent
  primal_ne_zero := by
    intro p i
    exact mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (pi.primal_ne_zero p 0))
      (pow_ne_zero _ (pi.primal_ne_zero p 1))) (tau.primal_ne_zero p i.2)
  dual_eq_inv := arithmeticCPSDualTensorRoot_eq_inv r m pi tau
  primal_bound := arithmeticCPSTensorRoot_bound r m pi tau
  dual_bound := arithmeticCPSDualTensorRoot_bound r m pi tau

/-- The carrier local numerator is literally the arithmetic twisted Euler numerator. -/
theorem arithmeticCPS_localFactor_identification
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) (p : Nat.Primes) (X : ℂ) :
    DualPairFiber.dualLocalPoly
        ((arithmeticCPSPolynomialTwist r m pi tau).primal p) X =
      DualPairFiber.dualLocalPoly (arithmeticCPSTensorRoot r m pi tau p) X := rfl

/-- The carrier all-place coefficient bank is literally the arithmetic twisted Euler bank. -/
theorem arithmeticCPS_globalCoefficient_identification
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) (n : ℕ) :
    cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau) n =
      unitaryGlobalSatakeCoeff (arithmeticCPSTensorRoot r m pi tau) n := rfl

/-- The same exact identification on the contragredient bank. -/
theorem arithmeticCPS_globalDualCoefficient_identification
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) (n : ℕ) :
    cpsPolynomialDualCoeff (arithmeticCPSPolynomialTwist r m pi tau) n =
      unitaryGlobalSatakeCoeff (arithmeticCPSDualTensorRoot r m pi tau) n := rfl

/-- A single exact passport showing that the local factors and both all-place coefficient banks
of the 3D CPS datum are the literal arithmetic symmetric-power tensor data. -/
structure ArithmeticCPSCoefficientPassport
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) : Prop where
  localFactor : ∀ (p : Nat.Primes) (X : ℂ),
    DualPairFiber.dualLocalPoly
        ((arithmeticCPSPolynomialTwist r m pi tau).primal p) X =
      DualPairFiber.dualLocalPoly (arithmeticCPSTensorRoot r m pi tau p) X
  primalCoefficient : ∀ n : ℕ,
    cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau) n =
      unitaryGlobalSatakeCoeff (arithmeticCPSTensorRoot r m pi tau) n
  dualCoefficient : ∀ n : ℕ,
    cpsPolynomialDualCoeff (arithmeticCPSPolynomialTwist r m pi tau) n =
      unitaryGlobalSatakeCoeff (arithmeticCPSDualTensorRoot r m pi tau) n

/-- The arithmetic CPS coefficient passport is constructed without identification hypotheses. -/
theorem arithmeticCPSCoefficientPassport
    (r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m)) :
    ArithmeticCPSCoefficientPassport r m pi tau := by
  exact ⟨arithmeticCPS_localFactor_identification r m pi tau,
    arithmeticCPS_globalCoefficient_identification r m pi tau,
    arithmeticCPS_globalDualCoefficient_identification r m pi tau⟩

/-- The arithmetic conductor and archimedean parameters of one CPS tensor twist.  The completion
shifts are constructed as all pairwise sums, exactly as for a tensor-product local parameter. -/
structure ArithmeticCPSCompletionData (r m : ℕ) where
  conductor : ℝ
  conductor_pos : 0 < conductor
  symmetricShift : Fin (r + 1) → ℂ
  twistShift : Fin m → ℂ

/-- The tensor-product Deligne shifts, with one entry for every `(j,k)` channel. -/
noncomputable def ArithmeticCPSCompletionData.tensorShifts
    {r m : ℕ} (D : ArithmeticCPSCompletionData r m) : List ℂ :=
  List.ofFn fun i : Fin ((r + 1) * m) =>
    let jk : Fin (r + 1) × Fin m :=
      (Fintype.equivFin (Fin (r + 1) × Fin m)).symm
        (Fin.cast (by simp [Nat.mul_comm]) i)
    D.symmetricShift jk.1 + D.twistShift jk.2

/-- The prescribed CPS completion clock built from the arithmetic conductor and tensor shifts. -/
noncomputable def ArithmeticCPSCompletionData.clock
    {r m : ℕ} (D : ArithmeticCPSCompletionData r m) (hm : 0 < m) : CPSCompletionClock where
  conductor := D.conductor
  conductor_pos := D.conductor_pos
  shifts := D.tensorShifts
  shifts_nonempty := by
    intro h
    have hlen := congrArg List.length h
    simp [tensorShifts, Nat.ne_of_gt hm] at hlen

/-- For the literal arithmetic CPS bank, the primal and dual 3D Mellin projections have the
tensor-product conductor and Gamma shifts supplied by the local parameter data. -/
theorem arithmeticCPSFullCompletion3D_identification
    (r m : ℕ) (hm : 0 < m)
    (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (D : ArithmeticCPSCompletionData r m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    mellin (cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts) point.s =
      cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s ∧
    mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts (1 / x)) point.s =
      cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts point.s := by
  exact cpsPolynomialFullCompletion3D_identification
    (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm) point

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.CPSResidual

variable {A W V : Type*} [Ring A] [Algebra ℂ A]
  [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

/-- A CPS residual channel vanishes as an intertwiner, not as an arbitrary linear map. -/
theorem equivariantResidual_zero
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V]
    [IsSimpleModule A V] (hdim : finrank ℂ W < finrank ℂ V)
    (residue : W →ₗ[A] V) : residue = 0 :=
  RepresentationRankGap.no_nonzero_intertwiner_of_finrank_lt
    (A := A) (W := W) (V := V) inferInstance hdim residue

end CriticalLinePhasor.CPSResidual

#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPSDualTensorRoot_eq_inv
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPSPolynomialTwist
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPS_localFactor_identification
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPS_globalCoefficient_identification
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPSCoefficientPassport
#print axioms CriticalLinePhasor.GlobalHelix.arithmeticCPSFullCompletion3D_identification
#print axioms CriticalLinePhasor.CPSResidual.equivariantResidual_zero
