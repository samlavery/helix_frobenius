import RequestProject.CPSRestrictedTensorConverseCapstone3D
import Mathlib.GroupTheory.DoubleCoset

/-!
# Representation-bound unramified Satake realization

This file strengthens the local root bookkeeping used by the CPS converse carrier.  The roots are
connected to the actual local representation through a compact-fixed spherical vector and finite
double-coset Hecke operators.  Thus Satake compatibility is no longer an equality between two
independently stored root functions.
-/

open scoped BigOperators Pointwise RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-- The `k`th elementary symmetric function of a finite root packet. -/
noncomputable def elementarySatakeCoefficient {d : ℕ} (root : Fin d → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin d))).filter (fun s ↦ s.card = k),
    ∏ j ∈ s, root j

/-- The finite Hecke operator attached to a chosen set of right-coset representatives.  Every
summand is the action of the actual representation. -/
noncomputable def finiteHeckeOperator
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (support : Finset G) : Module.End ℂ V :=
  ∑ g ∈ support, rho g

/-- In the trivial scalar representation a finite Hecke sum is multiplication by the number of
chosen cosets.  This is the concrete restriction missing from metadata-only compatibility. -/
theorem finiteHeckeOperator_trivial_apply
    {G : Type*} [Group G] (support : Finset G) (z : ℂ) :
    finiteHeckeOperator (Representation.trivial ℂ G ℂ) support z = support.card * z := by
  simp [finiteHeckeOperator]

/-- Turn an element of any `SubgroupClass` family into the corresponding bundled subgroup. -/
def subgroupOfSubgroupClass
    {G S : Type*} [Group G] [SetLike S G] [SubgroupClass S G] (H : S) : Subgroup G where
  carrier := H
  one_mem' := one_mem H
  mul_mem' := mul_mem
  inv_mem' := inv_mem

/-- A local unramified representation whose declared root packet is realized by spherical Hecke
operators.  `support_covers` ties each finite operator to an actual compact double coset, while
`hecke_eigen` identifies its eigenvalue with the elementary symmetric polynomial in `root`. -/
structure UnramifiedSatakeRealization3D
    (d : ℕ) {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (compact : Subgroup G) (rho : Representation ℂ G V) (root : Fin d → ℂ) where
  sphericalVector : V
  sphericalVector_ne_zero : sphericalVector ≠ 0
  spherical_fixed : ∀ k : compact, rho k sphericalVector = sphericalVector
  heckeElement : Fin (d + 1) → G
  heckeSupport : Fin (d + 1) → Finset G
  support_covers : ∀ k,
    DoubleCoset.doubleCoset (heckeElement k) compact compact =
      ⋃ g ∈ heckeSupport k, (g : G) • (compact : Set G)
  hecke_eigen : ∀ k,
    finiteHeckeOperator rho (heckeSupport k) sphericalVector =
      elementarySatakeCoefficient root k.1 • sphericalVector

/-- A restricted symmetric-power representation together with representation-bound Satake
realizations at every finite place. -/
structure SatakeRealizedRestrictedSymmetricPowerRepresentation3D
    (r : ℕ) (pi : CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    (compact : ∀ p, S p)
    (Vlocal : Nat.Primes → Type*)
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    (X : Type*) [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X] where
  representation :
    RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X
  local_realization : ∀ p,
    UnramifiedSatakeRealization3D (r + 1) (subgroupOfSubgroupClass (compact p))
      (representation.localRepresentation p) (representation.localSatakeRoot p)

/-- A CPS cuspidal symmetric-power lift whose local Satake packets are realized by the actual
local representations rather than attached as independent metadata. -/
structure SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D
    (r : ℕ) (pi : CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (X Garch P : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    (compact : ∀ p, S p)
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    (U : P → Type*)
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    (Vlocal : Nat.Primes → Type*)
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    (Ares Wres Vres : ℕ → Type*)
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)] where
  lift : ArithmeticSymmetricPowerCuspidalLift3D r pi X Garch P G S compact U Vlocal
    Ares Wres Vres
  local_realization : ∀ p,
    UnramifiedSatakeRealization3D (r + 1) (subgroupOfSubgroupClass (compact p))
      (lift.candidate.representation.localRepresentation p)
      (lift.candidate.representation.localSatakeRoot p)

/-- The reflected-theta CPS constructor preserves a representation-bound Satake realization all
the way to the object-valued cuspidal lift. -/
noncomputable def SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D.ofReflectedThetaSources
    {r : ℕ} {pi : CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    {X Garch P : Type*} {G : Nat.Primes → Type*} {S : Nat.Primes → Type*}
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    {compact : ∀ p, S p}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
    {U : P → Type*}
    [∀ q, MeasurableSpace (U q)] [∀ q, Group (U q)]
    [∀ q, MeasurableMul (U q)] [∀ q, MeasurableInv (U q)]
    {Vlocal : Nat.Primes → Type*}
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    {Ares Wres Vres : ℕ → Type*}
    [∀ m, Ring (Ares m)] [∀ m, Algebra ℂ (Ares m)]
    [∀ m, AddCommGroup (Wres m)] [∀ m, Module ℂ (Wres m)]
    [∀ m, Module (Ares m) (Wres m)] [∀ m, IsScalarTower ℂ (Ares m) (Wres m)]
    [∀ m, AddCommGroup (Vres m)] [∀ m, Module ℂ (Vres m)]
    [∀ m, Module (Ares m) (Vres m)] [∀ m, IsScalarTower ℂ (Ares m) (Vres m)]
    (representation :
      SatakeRealizedRestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X)
    (bank : CPSBankBridge Nat.Primes X Garch P compact U)
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : CriticalLinePhasor.GlobalHelix.ArithmeticCPSCompletionData r m) →
        CriticalLinePhasor.GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : CriticalLinePhasor.GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D r pi X Garch P G S compact U
      Vlocal Ares Wres Vres where
  lift := symmetricPowerFunctoriality3D_ofReflectedThetaSources
    representation.representation bank source residual
  local_realization := representation.local_realization

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.elementarySatakeCoefficient
#print axioms CriticalLinePhasor.ThreeDConverse.finiteHeckeOperator
#print axioms CriticalLinePhasor.ThreeDConverse.finiteHeckeOperator_trivial_apply
#print axioms CriticalLinePhasor.ThreeDConverse.SatakeRealizedArithmeticSymmetricPowerCuspidalLift3D.ofReflectedThetaSources
