import RequestProject.CPSArithmeticStrongSource3D
import RequestProject.CPSLatticeInstance3D
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Restricted-tensor arithmetic CPS converse capstone

This file puts the representation-theoretic and analytic inputs of one arithmetic CPS twist on
one typed object.  Its finite-place group is Mathlib's actual restricted product.  The object
records local representations, their smoothness and admissibility, the irreducibility of both the
local components and the restricted-product representation, and the exact equality between the
local Satake readout and the arithmetic symmetric-power tensor roots.

The residual channel is an equivariant map between modules over a representation algebra.  Its
vanishing is derived from simplicity and the strict rank gap.  The final theorem then assembles
that extinction, the literal arithmetic analytic candidate, and the existing rational-quotient
cuspidal landing for the same restricted-product action.
-/

open Complex Module MeasureTheory
open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-- Smoothness in the nonarchimedean representation-theoretic sense: every vector is fixed by an
open subgroup. -/
def Representation.IsSmoothAtOpenSubgroups
    {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (rho : Representation ℂ G V) : Prop :=
  ∀ v : V, ∃ K : OpenSubgroup G, ∀ k : K, rho k v = v

/-- Admissibility in the nonarchimedean representation-theoretic sense: the fixed vectors of
every open subgroup form a finite-dimensional complex vector space. -/
def Representation.IsAdmissibleAtOpenSubgroups
    {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (rho : Representation ℂ G V) : Prop :=
  ∀ K : OpenSubgroup G,
    Module.Finite ℂ (Representation.invariants (rho.comp K.subtype))

/-- A representation on the archimedean factor times the genuine finite-place restricted
product, together with its local components and exact arithmetic local-root readout. -/
structure RestrictedTensorRepresentation3D
    (r m : ℕ)
    (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    (compact : ∀ p, S p)
    (Vlocal : Nat.Primes → Type*)
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    (X : Type*) [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X] where
  /-- The local representation at a finite place. -/
  localRepresentation : ∀ p, Representation ℂ (G p) (Vlocal p)
  /-- Every local component is irreducible. -/
  local_irreducible : ∀ p, (localRepresentation p).IsIrreducible
  /-- Every local component is smooth. -/
  local_smooth : ∀ p,
    Representation.IsSmoothAtOpenSubgroups (localRepresentation p)
  /-- Every local component is admissible. -/
  local_admissible : ∀ p,
    Representation.IsAdmissibleAtOpenSubgroups (localRepresentation p)
  /-- The local Satake-root readout of the representation. -/
  localSatakeRoot : Nat.Primes → GlobalHelix.CPSTensorIndex r m → ℂ
  /-- Local compatibility is equality with the literal arithmetic tensor root, at every place and
  every tensor channel. -/
  local_compatible : ∀ p i,
    localSatakeRoot p i = GlobalHelix.arithmeticCPSTensorRoot r m pi tau p i
  /-- The global candidate is a representation of the actual archimedean-times-restricted-product
  group on the carrier state space. -/
  restrictedTensor :
    Representation ℂ (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X
  /-- Its linear action is the carrier action consumed by the converse landing. -/
  restrictedTensor_action : ∀ g x, restrictedTensor g x = g • x
  /-- The restricted-tensor candidate is irreducible. -/
  restrictedTensor_irreducible : restrictedTensor.IsIrreducible
  /-- The restricted-tensor candidate is smooth. -/
  restrictedTensor_smooth : Representation.IsSmoothAtOpenSubgroups restrictedTensor
  /-- The restricted-tensor candidate is admissible. -/
  restrictedTensor_admissible : Representation.IsAdmissibleAtOpenSubgroups restrictedTensor

/-- The finite-dimensional parameter residual used by the CPS pole calculation.  The residual is
an intertwiner over the representation algebra, rather than an arbitrary complex-linear map. -/
structure EquivariantCPSResidual3D
    (A W V : Type*) [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] where
  source_finite : FiniteDimensional ℂ W
  target_finite : FiniteDimensional ℂ V
  target_simple : IsSimpleModule A V
  rank_gap : finrank ℂ W < finrank ℂ V
  residue : W →ₗ[A] V

/-- Equivariant residual extinction, derived inside the packaged residual channel. -/
theorem EquivariantCPSResidual3D.residue_eq_zero
    {A W V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    (R : EquivariantCPSResidual3D A W V) : R.residue = 0 := by
  letI := R.source_finite
  letI := R.target_finite
  letI := R.target_simple
  exact CPSResidual.equivariantResidual_zero R.rank_gap R.residue

/-- One arithmetic CPS twist on one restricted-tensor candidate.  No representation-status,
local-identification, analytic, or residual proposition is supplied separately to the capstone:
all belong to this object. -/
structure ArithmeticCPSRestrictedTensorCandidate3D
    (r m : ℕ)
    (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (D : GlobalHelix.ArithmeticCPSCompletionData r m)
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
    (Ares Wres Vres : Type*) [Ring Ares] [Algebra ℂ Ares]
    [AddCommGroup Wres] [Module ℂ Wres] [Module Ares Wres]
    [IsScalarTower ℂ Ares Wres]
    [AddCommGroup Vres] [Module ℂ Vres] [Module Ares Vres]
    [IsScalarTower ℂ Ares Vres] where
  representation :
    RestrictedTensorRepresentation3D r m pi tau Garch G S compact Vlocal X
  bank : CPSBankBridge Nat.Primes X Garch P compact U
  analytic : GlobalHelix.ArithmeticCPSAnalyticCandidate3D r m pi tau D
  residual : EquivariantCPSResidual3D Ares Wres Vres

/-- **Restricted-tensor converse capstone.**  For the one packaged candidate, local arithmetic
compatibility, local/global irreducibility, smooth admissibility, analytic niceness, equivariant
residual extinction, and rational-quotient cuspidal landing hold simultaneously. -/
theorem ArithmeticCPSRestrictedTensorCandidate3D.converseCapstone
    {r m : ℕ}
    {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    {tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)}
    {D : GlobalHelix.ArithmeticCPSCompletionData r m}
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
    {Ares Wres Vres : Type*} [Ring Ares] [Algebra ℂ Ares]
    [AddCommGroup Wres] [Module ℂ Wres] [Module Ares Wres]
    [IsScalarTower ℂ Ares Wres]
    [AddCommGroup Vres] [Module ℂ Vres] [Module Ares Vres]
    [IsScalarTower ℂ Ares Vres]
    (C : ArithmeticCPSRestrictedTensorCandidate3D r m pi tau D X Garch P G S compact U
      Vlocal Ares Wres Vres) :
    (∀ p i, C.representation.localSatakeRoot p i =
      GlobalHelix.arithmeticCPSTensorRoot r m pi tau p i) ∧
    (∀ p, (C.representation.localRepresentation p).IsIrreducible) ∧
    (∀ p, Representation.IsSmoothAtOpenSubgroups
      (C.representation.localRepresentation p)) ∧
    (∀ p, Representation.IsAdmissibleAtOpenSubgroups
      (C.representation.localRepresentation p)) ∧
    C.representation.restrictedTensor.IsIrreducible ∧
    Representation.IsSmoothAtOpenSubgroups C.representation.restrictedTensor ∧
    Representation.IsAdmissibleAtOpenSubgroups C.representation.restrictedTensor ∧
    C.residual.residue = 0 ∧
    Differentiable ℂ C.analytic.primalContinuation ∧
    Differentiable ℂ C.analytic.dualContinuation ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖C.analytic.primalContinuation s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖C.analytic.dualContinuation s‖ ≤ B) ∧
    (∀ s : ℂ, C.analytic.primalContinuation (C.analytic.weight - s) =
      C.analytic.rootNumber • C.analytic.dualContinuation s) ∧
    ((∀ x : X,
      cpsAdelic3D_rationalQuotientReadout compact C.bank.H C.bank.readout
        C.bank.readout_continuous C.bank.tate_archimedean C.bank.tate_finite
        (Quotient.mk'' x) = C.bank.readout x) ∧
      CuspidalAlong3D C.bank.μ
        (quotientUnipotentKernel
          (cpsAdelic3D_rationalQuotientReadout compact C.bank.H C.bank.readout
            C.bank.readout_continuous C.bank.tate_archimedean C.bank.tate_finite)
          C.bank.translate)) := by
  refine ⟨C.representation.local_compatible,
    C.representation.local_irreducible,
    C.representation.local_smooth,
    C.representation.local_admissible,
    C.representation.restrictedTensor_irreducible,
    C.representation.restrictedTensor_smooth,
    C.representation.restrictedTensor_admissible,
    C.residual.residue_eq_zero,
    C.analytic.primal_entire,
    C.analytic.dual_entire,
    C.analytic.primal_boundedOn_verticalStrip,
    C.analytic.dual_boundedOn_verticalStrip,
    C.analytic.functionalEquation,
    C.bank.landing⟩

/-! ## The all-twist converse candidate -/

/-- The literal degree-`r+1` symmetric-power local root of the base rank-two Satake datum. -/
noncomputable def arithmeticSymmetricPowerRoot
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (p : Nat.Primes) (j : Fin (r + 1)) : ℂ :=
  pi.primal p 0 ^ (r - j.1) * pi.primal p 1 ^ j.1

/-- The base degree-`r+1` representation presented on the archimedean factor times the actual
finite-place restricted product.  Unlike the fixed-twist object above, its local root readout is
the symmetric-power candidate itself; twists are attached separately in the all-twist package. -/
structure RestrictedSymmetricPowerRepresentation3D
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
    [Group Garch] [TopologicalSpace Garch]
    [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
    [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
    (compact : ∀ p, S p)
    (Vlocal : Nat.Primes → Type*)
    [∀ p, AddCommGroup (Vlocal p)] [∀ p, Module ℂ (Vlocal p)]
    (X : Type*) [AddCommGroup X] [Module ℂ X]
    [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X] where
  localRepresentation : ∀ p, Representation ℂ (G p) (Vlocal p)
  local_irreducible : ∀ p, (localRepresentation p).IsIrreducible
  local_smooth : ∀ p,
    Representation.IsSmoothAtOpenSubgroups (localRepresentation p)
  local_admissible : ∀ p,
    Representation.IsAdmissibleAtOpenSubgroups (localRepresentation p)
  localSatakeRoot : Nat.Primes → Fin (r + 1) → ℂ
  local_compatible : ∀ p j,
    localSatakeRoot p j = arithmeticSymmetricPowerRoot r pi p j
  restrictedTensor :
    Representation ℂ (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X
  restrictedTensor_action : ∀ g x, restrictedTensor g x = g • x
  restrictedTensor_irreducible : restrictedTensor.IsIrreducible
  restrictedTensor_smooth : Representation.IsSmoothAtOpenSubgroups restrictedTensor
  restrictedTensor_admissible : Representation.IsAdmissibleAtOpenSubgroups restrictedTensor

/-- One base restricted-tensor candidate together with the literal arithmetic analytic candidate
and equivariant residual channel for every twist in the CPS range. -/
structure ArithmeticCPSAllTwistsConverseCandidate3D
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
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
  representation :
    RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X
  bank : CPSBankBridge Nat.Primes X Garch P compact U
  analytic : ∀ (m : ℕ), 1 ≤ m → m < r →
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
    (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
      GlobalHelix.ArithmeticCPSAnalyticCandidate3D r m pi tau D
  residual : ∀ (m : ℕ), 1 ≤ m → m < r →
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)

/-- Construct the complete all-twists converse candidate from the representation-theoretic
carrier, its rational-quotient bank, one literal reflected arithmetic theta source for every CPS
twist, and the equivariant residual channels.  In particular, callers do not supply an already
assembled analytic candidate: each analytic input is constructed from the corresponding
`ArithmeticCPSReflectedThetaSource`, whose one strong pair carries the prescribed primal and dual
banks, their reflection, continuation, strip bounds, and functional equation. -/
noncomputable def ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
      RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X)
    (bank : CPSBankBridge Nat.Primes X Garch P compact U)
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres where
  representation := representation
  bank := bank
  analytic := fun m hm hmr tau D => (source m hm hmr tau D).analyticCandidate
  residual := residual

@[simp] theorem ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources_analytic
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
      RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X)
    (bank : CPSBankBridge Nat.Primes X Garch P compact U)
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m))
    (m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (D : GlobalHelix.ArithmeticCPSCompletionData r m) :
    (ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources
      representation bank source residual).analytic m hm hmr tau D =
        (source m hm hmr tau D).analyticCandidate := rfl

/-- The analytic and residual payload for one member of the universally quantified twist family. -/
def ArithmeticCPSAllTwistsConverseCandidate3D.TwistPayload
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
    (C : ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres)
    (m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (D : GlobalHelix.ArithmeticCPSCompletionData r m) : Prop :=
  let A := C.analytic m hm hmr tau D
  let R := C.residual m hm hmr tau
  GlobalHelix.ArithmeticCPSCoefficientPassport r m pi tau ∧
  R.residue = 0 ∧
  Differentiable ℂ A.primalContinuation ∧
  Differentiable ℂ A.dualContinuation ∧
  (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
    u ≤ s.re → s.re ≤ v → ‖A.primalContinuation s‖ ≤ B) ∧
  (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
    u ≤ s.re → s.re ≤ v → ‖A.dualContinuation s‖ ≤ B) ∧
  (∀ s : ℂ, A.primalContinuation (A.weight - s) =
    A.rootNumber • A.dualContinuation s) ∧
  (∀ point : GlobalHelix.CPSCompletionPoint
      (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau) (D.clock (lt_of_lt_of_le Nat.zero_lt_one hm)),
    A.primalContinuation point.s =
        GlobalHelix.cpsPolynomialFullPrimalCompletedReadout
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts point.s ∧
      A.dualContinuation point.s =
        GlobalHelix.cpsPolynomialFullDualCompletedReadout
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts point.s) ∧
  (∀ x : ℝ, 0 < x →
    GlobalHelix.cpsPolynomialFullPrimal3DBankReadout
        (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
        D.conductor D.tensorShifts (1 / x) =
      (A.rootNumber * (x ^ A.weight : ℝ)) •
        GlobalHelix.cpsPolynomialFullDual3DTransformedReadout
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts (1 / x))

/-- Every twist member of an all-twist candidate supplies its exact arithmetic passport, analytic
niceness, initial Euler identification, native 3D reflection, and a derived zero residual. -/
theorem ArithmeticCPSAllTwistsConverseCandidate3D.twistPayload
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
    (C : ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres)
    (m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (D : GlobalHelix.ArithmeticCPSCompletionData r m) :
    C.TwistPayload m hm hmr tau D := by
  let A := C.analytic m hm hmr tau D
  let R := C.residual m hm hmr tau
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  refine ⟨GlobalHelix.arithmeticCPSCoefficientPassport r m pi tau,
    R.residue_eq_zero,
    A.primal_entire,
    A.dual_entire,
    A.primal_boundedOn_verticalStrip,
    A.dual_boundedOn_verticalStrip,
    A.functionalEquation,
    ?_,
    A.native3DReflection⟩
  intro point
  exact ⟨A.primal_initial hmpos point, A.dual_initial hmpos point⟩

/-- **All-twist restricted-tensor converse capstone.**  The base candidate's exact local roots,
restricted-product representation status, and cuspidal quotient landing are assembled with the
complete analytic and equivariant-residual payload for every twist in the CPS range. -/
theorem ArithmeticCPSAllTwistsConverseCandidate3D.converseCapstone
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
    (C : ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres) :
    (∀ p j, C.representation.localSatakeRoot p j =
      arithmeticSymmetricPowerRoot r pi p j) ∧
    (∀ p, (C.representation.localRepresentation p).IsIrreducible) ∧
    (∀ p, Representation.IsSmoothAtOpenSubgroups
      (C.representation.localRepresentation p)) ∧
    (∀ p, Representation.IsAdmissibleAtOpenSubgroups
      (C.representation.localRepresentation p)) ∧
    C.representation.restrictedTensor.IsIrreducible ∧
    Representation.IsSmoothAtOpenSubgroups C.representation.restrictedTensor ∧
    Representation.IsAdmissibleAtOpenSubgroups C.representation.restrictedTensor ∧
    (∀ g x, C.representation.restrictedTensor g x = g • x) ∧
    ((∀ x : X,
      cpsAdelic3D_rationalQuotientReadout compact C.bank.H C.bank.readout
        C.bank.readout_continuous C.bank.tate_archimedean C.bank.tate_finite
        (Quotient.mk'' x) = C.bank.readout x) ∧
      CuspidalAlong3D C.bank.μ
        (quotientUnipotentKernel
          (cpsAdelic3D_rationalQuotientReadout compact C.bank.H C.bank.readout
            C.bank.readout_continuous C.bank.tate_archimedean C.bank.tate_finite)
          C.bank.translate)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
      (D : GlobalHelix.ArithmeticCPSCompletionData r m),
        C.TwistPayload m hm hmr tau D) := by
  refine ⟨C.representation.local_compatible,
    C.representation.local_irreducible,
    C.representation.local_smooth,
    C.representation.local_admissible,
    C.representation.restrictedTensor_irreducible,
    C.representation.restrictedTensor_smooth,
    C.representation.restrictedTensor_admissible,
    C.representation.restrictedTensor_action,
    C.bank.landing,
    ?_⟩
  intro m hm hmr tau D
  exact C.twistPayload m hm hmr tau D

/-! ## Object-valued symmetric-power landing -/

/-- The object returned by the three-dimensional symmetric-power converse construction.

It retains one restricted-product representation whose local roots are the literal arithmetic
`Sym^r` roots, the rational-quotient cuspidal landing for that same representation, and the complete
analytic CPS payload for every required twist.  Representation compatibility, irreducibility,
smoothness, and admissibility remain fields of `candidate.representation`; they are not copied into
a second object. -/
structure ArithmeticSymmetricPowerCuspidalLift3D
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
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
  candidate : ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
    Ares Wres Vres
  cuspidal : CuspidalAlong3D candidate.bank.μ
    (quotientUnipotentKernel
      (cpsAdelic3D_rationalQuotientReadout compact candidate.bank.H candidate.bank.readout
        candidate.bank.readout_continuous candidate.bank.tate_archimedean
        candidate.bank.tate_finite)
      candidate.bank.translate)
  allTwists : ∀ (m : ℕ) (hm : 1 ≤ m) (hmr : m < r)
    (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m))
    (D : GlobalHelix.ArithmeticCPSCompletionData r m),
      candidate.TwistPayload m hm hmr tau D

/-- Convert the assembled all-twist converse candidate into the first-class cuspidal
symmetric-power lift returned by the three-dimensional model. -/
noncomputable def ArithmeticCPSAllTwistsConverseCandidate3D.cuspidalSymmetricPowerLift
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
    (C : ArithmeticCPSAllTwistsConverseCandidate3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres) :
    ArithmeticSymmetricPowerCuspidalLift3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres where
  candidate := C
  cuspidal := C.bank.landing.2
  allTwists := fun m hm hmr tau D => C.twistPayload m hm hmr tau D

/-- One-step symmetric-power landing from the restricted representation, its arithmetic reflected
theta sources, and its equivariant residual channels.  The result is an object, rather than a
conjunction of properties. -/
noncomputable def symmetricPowerFunctoriality3D_ofReflectedThetaSources
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
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
      RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact Vlocal X)
    (bank : CPSBankBridge Nat.Primes X Garch P compact U)
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    ArithmeticSymmetricPowerCuspidalLift3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres :=
  (ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources
    representation bank source residual).cuspidalSymmetricPowerLift

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.EquivariantCPSResidual3D.residue_eq_zero
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSRestrictedTensorCandidate3D.converseCapstone
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSAllTwistsConverseCandidate3D.ofReflectedThetaSources_analytic
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSAllTwistsConverseCandidate3D.twistPayload
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSAllTwistsConverseCandidate3D.converseCapstone
#print axioms CriticalLinePhasor.ThreeDConverse.ArithmeticCPSAllTwistsConverseCandidate3D.cuspidalSymmetricPowerLift
#print axioms CriticalLinePhasor.ThreeDConverse.symmetricPowerFunctoriality3D_ofReflectedThetaSources
