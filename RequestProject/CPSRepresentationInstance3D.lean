import RequestProject.CPSRestrictedTensorConverseCapstone3D

/-!
# Representation-side existence terms for the CPS capstone

The all-twist converse capstone consumes four families of terms: a restricted-product
representation, a bank bridge, per-twist analytic candidates, and per-twist equivariant residual
channels.  The analytic family is supplied by the theta-profile couplings
(`CPSBankThetaProfileCoupling3D.lean`); this file constructs the remaining, representation-side
terms.

* Reusable bricks: every representation on a simple module is irreducible
  (`Representation.isIrreducible_of_isSimpleModule`); the trivial representation is smooth
  (`Representation.trivial_isSmoothAtOpenSubgroups`); every representation on a
  finite-dimensional space is admissible (`Representation.isAdmissibleAtOpenSubgroups_of_finite`).
* `scalarRestrictedSymmetricPowerRepresentation3D` — the first compiled term of
  `RestrictedSymmetricPowerRepresentation3D`, polymorphic over every archimedean/finite group
  family: the scalar (Hecke-character-shaped) instance, with all irreducibility, smoothness, and
  admissibility fields proven, none supplied.
* `EquivariantCPSResidual3D.ofSchurData` and the concrete `scalarResidualChannel(s)` — the
  residual channels exist whenever the Schur data holds; by `residue_eq_zero` the zero intertwiner
  is the only inhabitant, so this constructor is exhaustive.
* `zeroReadoutBankBridge` — a degenerate witness that the `Nat.Primes`-typed `CPSBankBridge` is
  inhabited: zero readout, every Tate field `rfl`.  The
  finite-model witness is `latticeBridge`; the adelic bridge is the Tate
  formalization boundary.
* `scalarConverseCandidateRankOne` and `scalarRankOneCuspidalLift` — at rank `r = 1` the CPS twist
  range is empty, so the representation and bank terms alone assemble a complete
  `ArithmeticCPSAllTwistsConverseCandidate3D`, and the capstone and object-valued lift fire
  end-to-end on compiled terms.  A structural smoke test of the full capstone chain
  at the representation layer; the arithmetic content of higher ranks enters through the twist
  families.
-/

open Complex Module MeasureTheory
open scoped RestrictedProduct

namespace CriticalLinePhasor.ThreeDConverse

/-! ## Reusable bricks -/

/-- Any representation on a simple module is irreducible: an invariant submodule is in particular
a submodule, and the submodule lattice is already simple. -/
theorem Representation.isIrreducible_of_isSimpleModule
    {A G V : Type*} [Field A] [Group G] [AddCommGroup V] [Module A V]
    (rho : Representation A G V) [IsSimpleModule A V] :
    rho.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation rho) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule A V)
      (congrArg Subrepresentation.toSubmodule h)⟩
  exact { toNontrivial := hnt
          eq_bot_or_eq_top := fun p =>
            (eq_bot_or_eq_top p.toSubmodule).imp
              (fun h => Subrepresentation.toSubmodule_injective h)
              (fun h => Subrepresentation.toSubmodule_injective h) }

/-- The trivial representation is smooth: the whole group is an open subgroup fixing everything. -/
theorem Representation.trivial_isSmoothAtOpenSubgroups
    {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] :
    Representation.IsSmoothAtOpenSubgroups (Representation.trivial ℂ G V) :=
  fun _ => ⟨⊤, fun _ => rfl⟩

/-- Every representation on a finite-dimensional space is admissible: each invariant subspace is a
subspace of a finite-dimensional space. -/
theorem Representation.isAdmissibleAtOpenSubgroups_of_finite
    {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (rho : Representation ℂ G V) :
    Representation.IsAdmissibleAtOpenSubgroups rho :=
  fun _ => inferInstance

/-! ## The scalar restricted-product representation instance -/

section ScalarRepresentation

variable (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
  [Group Garch] [TopologicalSpace Garch]
  [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
  [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
  (compact : ∀ p, S p)

/-- The trivial adelic action on the scalar carrier. -/
@[reducible] noncomputable def scalarAdelicAction :
    MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ :=
  Representation.mulAction
    (Representation.trivial ℂ (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ)

/-- **The first compiled restricted-product representation term.**  The scalar
(Hecke-character-shaped) instance of `RestrictedSymmetricPowerRepresentation3D`, for every rank,
every Satake datum, and every group family: local and global representations are the trivial
character on `ℂ`, and every irreducibility, smoothness, admissibility, and compatibility field is
proven from the bricks above.  Nothing is supplied as a hypothesis. -/
noncomputable def scalarRestrictedSymmetricPowerRepresentation3D
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) :
    letI := scalarAdelicAction Garch G S compact
    RestrictedSymmetricPowerRepresentation3D r pi Garch G S compact (fun _ => ℂ) ℂ := by
  letI := scalarAdelicAction Garch G S compact
  exact {
    localRepresentation := fun p => Representation.trivial ℂ (G p) ℂ
    local_irreducible := fun _ => Representation.isIrreducible_of_isSimpleModule _
    local_smooth := fun _ => Representation.trivial_isSmoothAtOpenSubgroups
    local_admissible := fun _ => Representation.isAdmissibleAtOpenSubgroups_of_finite _
    localSatakeRoot := arithmeticSymmetricPowerRoot r pi
    local_compatible := fun _ _ => rfl
    restrictedTensor := Representation.trivial ℂ _ ℂ
    restrictedTensor_action := fun _ _ => rfl
    restrictedTensor_irreducible := Representation.isIrreducible_of_isSimpleModule _
    restrictedTensor_smooth := Representation.trivial_isSmoothAtOpenSubgroups
    restrictedTensor_admissible := Representation.isAdmissibleAtOpenSubgroups_of_finite _
  }

end ScalarRepresentation

/-! ## Genuine adelic specialization -/

/-- The scalar representation witness specialized to the actual adelic group
`GL (r+1, 𝔸_ℚ)`.  In particular, the finite factor is Mathlib's restricted product of
`GL (r+1, ℚ_p)` with respect to `GL (r+1, ℤ_p)`, and the local/global irreducibility,
smoothness, admissibility, and exact Satake compatibility fields are inherited from the compiled
scalar representation construction above. -/
noncomputable def scalarGenuineAdelicRestrictedRepresentation3D
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    AdelicRestrictedSymmetricPowerRepresentation3D r pi (fun _ ↦ ℂ) ℂ := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun p ↦ PadicGL (r + 1) p)
    (fun p ↦ Subgroup (PadicGL (r + 1) p))
    (fun p ↦ padicIntegralSubgroup (r + 1) p)
  exact scalarRestrictedSymmetricPowerRepresentation3D
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun p ↦ PadicGL (r + 1) p)
    (fun p ↦ Subgroup (PadicGL (r + 1) p))
    (fun p ↦ padicIntegralSubgroup (r + 1) p) r pi

/-! ## The equivariant residual channels -/

/-- The residual channel exists whenever the Schur data holds; by
`EquivariantCPSResidual3D.residue_eq_zero` every inhabitant has zero residue, so the zero
intertwiner is the canonical and exhaustive choice. -/
noncomputable def EquivariantCPSResidual3D.ofSchurData
    (A W V : Type*) [Ring A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [Module A W] [IsScalarTower ℂ A W]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ V] [IsSimpleModule A V]
    (hgap : finrank ℂ W < finrank ℂ V) :
    EquivariantCPSResidual3D A W V :=
  ⟨inferInstance, inferInstance, inferInstance, hgap, 0⟩

/-- The concrete scalar residual channel: zero-dimensional source, one-dimensional simple
target. -/
noncomputable def scalarResidualChannel :
    EquivariantCPSResidual3D ℂ (Fin 0 → ℂ) ℂ :=
  EquivariantCPSResidual3D.ofSchurData ℂ (Fin 0 → ℂ) ℂ (by simp)

/-- The per-twist residual-channel family consumed by the all-twist converse candidate. -/
noncomputable def scalarResidualChannels (r : ℕ) :
    ∀ (m : ℕ), 1 ≤ m → m < r →
      GlobalHelix.PolynomialSatakeDualPair (Fin m) →
        EquivariantCPSResidual3D ℂ (Fin 0 → ℂ) ℂ :=
  fun _ _ _ _ => scalarResidualChannel

/-! ## A degenerate `Nat.Primes` bank bridge -/

/-- The degenerate unipotent channel of the zero-readout bridge. -/
def ZeroChannel : Type := PUnit

instance : CommGroup ZeroChannel := inferInstanceAs (CommGroup PUnit)
instance : MeasurableSpace ZeroChannel := ⊤
instance : MeasurableMul ZeroChannel :=
  ⟨fun _ => measurable_from_top, fun _ => measurable_from_top⟩
instance : MeasurableInv ZeroChannel := ⟨measurable_from_top⟩

section ZeroBridge

variable (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
  [Group Garch] [TopologicalSpace Garch]
  [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
  [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
  (compact : ∀ p, S p)
  (X : Type*) [TopologicalSpace X]
  [MulAction (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]
  [ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) X]

/-- **A degenerate witness that the `Nat.Primes`-typed bank bridge is inhabited.**  The readout is
zero, both Tate fields are `rfl`, the single channel carries the zero measure, and the eigenvalue
condition `2 ≠ 1` holds because the descended readout vanishes identically.  The
finite-model witness is `latticeBridge`; the adelic readout is the Tate
formalization boundary. -/
noncomputable def zeroReadoutBankBridge :
    CPSBankBridge Nat.Primes X Garch PUnit compact (fun _ => ZeroChannel) where
  H := ⊤
  readout := fun _ => 0
  readout_continuous := continuous_const
  tate_archimedean := fun _ _ => rfl
  tate_finite := fun _ _ _ => rfl
  μ := fun _ => 0
  μ_invariant := fun _ => ⟨fun _ => by simp⟩
  translate := fun _ q _ => q
  hintegrable := fun _ _ => integrable_zero_measure
  move := fun _ _ => 1
  eigenvalue := fun _ _ => 2
  heigen := fun p q u => by
    induction q using Quotient.inductionOn' with
    | h x => show (0 : ℂ) = 2 * 0; norm_num
  hnontrivial := fun _ _ => by norm_num

end ZeroBridge

/-- The zero-readout bridge specialized to the actual adelic group, with quotient subgroup
definitionally equal to the diagonal image of `GL n ℚ`.  This is the canonical zero-channel
inhabitant of the genuine adelic bank interface and exposes the rational quotient at the exact
type consumed by `symmetricPowerFunctoriality3D_ofGenuineAdelicProfileCouplings`. -/
noncomputable def zeroReadoutGenuineAdelicBankBridge3D (n : ℕ) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin n) ℝ)
      (fun p ↦ PadicGL n p)
      (fun p ↦ Subgroup (PadicGL n p))
      (fun p ↦ padicIntegralSubgroup n p)
    letI : ContinuousSMul (AdelicGL n) ℂ := ⟨continuous_snd⟩
    GenuineAdelicCPSBankBridge3D n ℂ PUnit (fun _ ↦ ZeroChannel) := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin n) ℝ)
    (fun p ↦ PadicGL n p)
    (fun p ↦ Subgroup (PadicGL n p))
    (fun p ↦ padicIntegralSubgroup n p)
  letI : ContinuousSMul (AdelicGL n) ℂ := ⟨continuous_snd⟩
  exact {
    bridge := {
      H := rationalDiagonalSubgroup n
      readout := fun _ ↦ 0
      readout_continuous := continuous_const
      tate_archimedean := fun _ _ ↦ rfl
      tate_finite := fun _ _ _ ↦ rfl
      μ := fun _ ↦ 0
      μ_invariant := fun _ ↦ ⟨fun _ ↦ by simp⟩
      translate := fun _ q _ ↦ q
      hintegrable := fun _ _ ↦ integrable_zero_measure
      move := fun _ _ ↦ 1
      eigenvalue := fun _ _ ↦ 2
      heigen := fun p q u ↦ by
        induction q using Quotient.inductionOn' with
        | h x => show (0 : ℂ) = 2 * 0; norm_num
      hnontrivial := fun _ _ ↦ by norm_num
    }
    rational_subgroup := rfl
  }

/-! ## The rank-one candidate: the capstone chain fires on compiled terms -/

section RankOne

variable (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
  (Garch : Type*) (G : Nat.Primes → Type*) (S : Nat.Primes → Type*)
  [Group Garch] [TopologicalSpace Garch]
  [∀ p, Group (G p)] [∀ p, TopologicalSpace (G p)]
  [∀ p, SetLike (S p) (G p)] [∀ p, SubgroupClass (S p) (G p)]
  (compact : ∀ p, S p)

/-- At rank one the CPS twist range `1 ≤ m < 1` is empty, so the scalar representation and the
degenerate bridge assemble a complete all-twist converse candidate with no analytic or residual
family supplied.  A structural smoke test that the full candidate type is inhabited and
the capstone chain executes; arithmetic content enters at higher rank through the twist
families. -/
noncomputable def scalarConverseCandidateRankOne :
    letI := scalarAdelicAction Garch G S compact
    letI : ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ :=
      ⟨continuous_snd⟩
    ArithmeticCPSAllTwistsConverseCandidate3D 1 pi ℂ Garch PUnit G S compact
      (fun _ => ZeroChannel) (fun _ => ℂ) (fun _ => ℂ) (fun _ => Fin 0 → ℂ)
      (fun _ => ℂ) := by
  letI := scalarAdelicAction Garch G S compact
  letI : ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ :=
    ⟨continuous_snd⟩
  exact {
    representation := scalarRestrictedSymmetricPowerRepresentation3D Garch G S compact 1 pi
    bank := zeroReadoutBankBridge Garch G S compact ℂ
    analytic := fun _ hm hmr _ _ => absurd hmr (by omega)
    residual := fun _ hm hmr _ => absurd hmr (by omega)
  }

/-- The object-valued cuspidal lift of the rank-one scalar candidate: the capstone chain —
representation status, quotient landing, cuspidality, and the (vacuous) twist payload — fires
end-to-end on compiled terms. -/
noncomputable def scalarRankOneCuspidalLift :
    letI := scalarAdelicAction Garch G S compact
    letI : ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ :=
      ⟨continuous_snd⟩
    ArithmeticSymmetricPowerCuspidalLift3D 1 pi ℂ Garch PUnit G S compact
      (fun _ => ZeroChannel) (fun _ => ℂ) (fun _ => ℂ) (fun _ => Fin 0 → ℂ)
      (fun _ => ℂ) := by
  letI := scalarAdelicAction Garch G S compact
  letI : ContinuousSMul (Garch × (Πʳ p, [G p, (compact p : Set (G p))])) ℂ :=
    ⟨continuous_snd⟩
  exact (scalarConverseCandidateRankOne pi Garch G S compact).cuspidalSymmetricPowerLift

end RankOne

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.Representation.isIrreducible_of_isSimpleModule
#print axioms CriticalLinePhasor.ThreeDConverse.Representation.trivial_isSmoothAtOpenSubgroups
#print axioms CriticalLinePhasor.ThreeDConverse.Representation.isAdmissibleAtOpenSubgroups_of_finite
#print axioms CriticalLinePhasor.ThreeDConverse.scalarRestrictedSymmetricPowerRepresentation3D
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicRestrictedRepresentation3D
#print axioms CriticalLinePhasor.ThreeDConverse.EquivariantCPSResidual3D.ofSchurData
#print axioms CriticalLinePhasor.ThreeDConverse.scalarResidualChannel
#print axioms CriticalLinePhasor.ThreeDConverse.zeroReadoutBankBridge
#print axioms CriticalLinePhasor.ThreeDConverse.zeroReadoutGenuineAdelicBankBridge3D
#print axioms CriticalLinePhasor.ThreeDConverse.scalarConverseCandidateRankOne
#print axioms CriticalLinePhasor.ThreeDConverse.scalarRankOneCuspidalLift
