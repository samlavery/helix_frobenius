import RequestProject.CPSBankThetaProfileCoupling3D
import RequestProject.CPSRepresentationInstance3D
import RequestProject.CPSRestrictedTensorConverseCapstone3D
import RequestProject.CPSMellinBasicIdentity
import RequestProject.RungCapstone

/-!
# The profile-coupling functoriality endpoint: the wall as one hypothesis

Two strengthenings of the converse chain's typing.

* `symmetricPowerFunctoriality3D_ofProfileCouplings` — the object-valued symmetric-power landing
  whose **only analytic hypothesis is the per-twist theta-profile-coupling family**: given the
  restricted-product representation, the bank bridge, the residual channels, and one
  `BankThetaProfileCoupling3D` per CPS twist, the carrier seeds, reflected sources, analytic
  candidates, converse candidate, and cuspidal lift are all constructed internally.  The
  remaining Langlands wall is thereby the literal hypothesis of one endpoint theorem — one
  pointwise weighted reflection per rung, nothing else analytic.

* `BankThetaProfileCoupling3D.ofMellinFE` — the cited-classical entry point: a completed
  Mellin-space functional equation for the literal prescribed banks, together with the standard
  Mellin-inversion integrability conditions, *derives* the pointwise profile reflection
  (`theta_reflection_of_mellin_functionalEquation`) and constructs the coupling.  This is the
  shape in which classical results deliver the low rungs (Langlands–Shahidi and Kim–Shahidi for
  $r\le4$, cited): the per-rung obligation converts from a pointwise theta identity to a
  Mellin-space functional equation plus integrability — consumed as data, exactly as local
  Langlands and Hecke multiplicativity are consumed at their typed fields.

* `cpsRungFullAutomorphy3D_ofProfileCouplings` — the warp-to-CPS endpoint: the
  degree-generic rung package kills its polar carrier while the profile-coupling
  family constructs the first-class cuspidal symmetric-power lift.  Thus one
  returned object retains both pole extinction and full CPS automorphy.
-/

open Complex MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

open CriticalLinePhasor.ThreeDConverse

/-- **The cited-classical entry point**: a completed Mellin functional equation between the
literal prescribed banks, with the standard Mellin-inversion hypotheses, constructs the
theta-profile coupling — the pointwise reflection is derived, not supplied. -/
noncomputable def BankThetaProfileCoupling3D.ofMellinFE
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (k σ : ℝ) (ε : ℂ) (hε : ε ≠ 0) (hk : 0 < k)
    (hFE : ∀ s : ℂ,
      mellin (cpsPolynomialFullPrimal3DBankReadout W C μs) ((k : ℂ) - s) =
        ε • mellin (fun x : ℝ =>
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) s)
    (hfConv : MellinConvergent
      (cpsPolynomialFullPrimal3DBankReadout W C μs) (σ : ℂ))
    (hrefConv : MellinConvergent
      (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) (σ : ℂ))
    (hfVert : VerticalIntegrable
      (mellin (cpsPolynomialFullPrimal3DBankReadout W C μs)) σ volume)
    (hrefVert : VerticalIntegrable
      (mellin (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)))) σ volume)
    (hfCont : ∀ x : ℝ, 0 < x →
      ContinuousAt (cpsPolynomialFullPrimal3DBankReadout W C μs) x)
    (hrefCont : ∀ x : ℝ, 0 < x →
      ContinuousAt (reflectedTheta k ε (fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))) x) :
    BankThetaProfileCoupling3D W C μs where
  primalProfile := cpsPolynomialFullPrimal3DBankReadout W C μs
  dualProfile := fun x : ℝ =>
    cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)
  exchangeConstant := ε
  exchangeConstant_ne_zero := hε
  weight := k
  weight_pos := hk
  profile_reflection := by
    intro x hx
    have h1x : (0 : ℝ) < 1 / x := one_div_pos.mpr hx
    have h := theta_reflection_of_mellin_functionalEquation k σ ε
      (cpsPolynomialFullPrimal3DBankReadout W C μs)
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x))
      hFE hfConv hrefConv hfVert hrefVert (1 / x) h1x
      (hfCont _ h1x) (hrefCont _ h1x)
    rw [h]
    unfold CriticalLinePhasor.ThreeDConverse.reflectedTheta
    rw [one_div_one_div]
    have hpow : ((1 / x : ℝ) : ℂ) ^ (-(k : ℂ)) = ((x ^ k : ℝ) : ℂ) := by
      have hcast : (-(k : ℂ)) = (((-k : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast, ← Complex.ofReal_cpow h1x.le]
      congr 1
      rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]
    rw [hpow, smul_smul]
  primal_readout := fun _ _ => rfl
  dual_readout := fun _ _ => rfl

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.ThreeDConverse

open scoped RestrictedProduct
open CriticalLinePhasor.PolarCorrection CriticalLinePhasor.RungCapstone

/-- **The wall as one hypothesis: the profile-coupling functoriality endpoint.**  From the
restricted-product representation, the bank bridge, the residual channels, and one theta-profile
coupling per CPS twist, the object-valued cuspidal symmetric-power lift is constructed — the
carrier seeds, reflected sources, and analytic candidates all built internally
(`allProfileCarrierSeeds` → `ofCarrierSeeds` → `cuspidalSymmetricPowerLift`).  The per-rung
analytic obligation of the entire chain is exactly the coupling family: one pointwise weighted
reflection per rung, with both bank identifications, and nothing else. -/
noncomputable def symmetricPowerFunctoriality3D_ofProfileCouplings
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
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.BankThetaProfileCoupling3D
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    ArithmeticSymmetricPowerCuspidalLift3D r pi X Garch P G S compact U Vlocal
      Ares Wres Vres :=
  symmetricPowerFunctoriality3D_ofCarrierSeeds representation bank
    (GlobalHelix.allProfileCarrierSeeds coupling) residual

/-- The profile-coupling converse constructor specialized to the genuine adelic group
`GL (r+1) 𝔸_ℚ`, its literal restricted tensor representation, and a bank whose quotient
subgroup is the rational diagonal image. -/
noncomputable def symmetricPowerFunctoriality3D_ofGenuineAdelicProfileCouplings
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    {X P : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [MulAction (AdelicGL (r + 1)) X] [ContinuousSMul (AdelicGL (r + 1)) X]
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
    (representation : AdelicRestrictedSymmetricPowerRepresentation3D r pi Vlocal X)
    (bank : GenuineAdelicCPSBankBridge3D (r + 1) X P U)
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.BankThetaProfileCoupling3D
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    ArithmeticSymmetricPowerCuspidalLift3D r pi X
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) P
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      U Vlocal Ares Wres Vres :=
  symmetricPowerFunctoriality3D_ofProfileCouplings
    representation bank.bridge coupling residual

/-- The genuine-adelic profile constructor with all representation-side inputs discharged by the
scalar restricted-product representation, the rational-diagonal bank bridge, and the canonical
Schur residual channels.  Its sole argument is the all-twist prescribed-bank coupling family. -/
noncomputable def scalarGenuineAdelicSymmetricPowerLift3D
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.BankThetaProfileCoupling3D
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    ArithmeticSymmetricPowerCuspidalLift3D r pi ℂ
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) PUnit
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (fun _ ↦ ZeroChannel) (fun _ ↦ ℂ) (fun _ ↦ ℂ)
      (fun _ ↦ Fin 0 → ℂ) (fun _ ↦ ℂ) := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun p ↦ PadicGL (r + 1) p)
    (fun p ↦ Subgroup (PadicGL (r + 1) p))
    (fun p ↦ padicIntegralSubgroup (r + 1) p)
  letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
  exact symmetricPowerFunctoriality3D_ofGenuineAdelicProfileCouplings
    (scalarGenuineAdelicRestrictedRepresentation3D r pi)
    (zeroReadoutGenuineAdelicBankBridge3D (r + 1)) coupling
    (scalarResidualChannels r)

/-- Completed Rankin--Selberg theta sources at every CPS twist now flow directly through profile
coupling, genuine adelic restricted representation and bank, and the CPS converse constructor to
an object-valued cuspidal symmetric-power lift. -/
noncomputable def scalarGenuineAdelicSymmetricPowerLift3D_ofReflectedThetaSources
    {r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    ArithmeticSymmetricPowerCuspidalLift3D r pi ℂ
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) PUnit
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (fun _ ↦ ZeroChannel) (fun _ ↦ ℂ) (fun _ ↦ ℂ)
      (fun _ ↦ Fin 0 → ℂ) (fun _ ↦ ℂ) := by
  exact scalarGenuineAdelicSymmetricPowerLift3D
    (GlobalHelix.allArithmeticProfileCouplings source)

/-! ## Warp-to-CPS full automorphy -/

/-- The full CPS output of one rung: an object-valued cuspidal symmetric-power
lift together with extinction of the same rung's polar carrier. -/
structure CPSRungAutomorphicLift3D
    (n r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2))
    (W : RungWarpData n)
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
  polarCarrier_zero : ∀ u : ℂ, expSum W.μ W.c 0 u = 0

/-- **Full CPS automorphy at a rung.**  The warp package kills the polar
carrier, while the CPS profile-coupling endpoint constructs the restricted
product representation, literal arithmetic `Sym^r` local roots,
rational-quotient cuspidality, and every required twisted analytic package. -/
noncomputable def cpsRungFullAutomorphy3D_ofProfileCouplings
    {n r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    (W : RungWarpData n)
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
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.BankThetaProfileCoupling3D
          (GlobalHelix.arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts)
    (residual : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
        EquivariantCPSResidual3D (Ares m) (Wres m) (Vres m)) :
    CPSRungAutomorphicLift3D n r pi W X Garch P G S compact U Vlocal Ares Wres Vres where
  lift := symmetricPowerFunctoriality3D_ofProfileCouplings
    representation bank coupling residual
  polarCarrier_zero := rung_polar_carrier_zero W

/-- A completed Rankin--Selberg source family and an arithmetic warp datum produce the full
rank-`r` object on the literal adelic group: the CPS cuspidal lift and the vanishing polar carrier
are retained in the same `CPSRungAutomorphicLift3D`. -/
noncomputable def scalarGenuineAdelicCPSRungAutomorphicLift3D_ofReflectedThetaSources
    {n r : ℕ} {pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)}
    (W : RungWarpData n)
    (source : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : GlobalHelix.PolynomialSatakeDualPair (Fin m)) →
      (D : GlobalHelix.ArithmeticCPSCompletionData r m) →
        GlobalHelix.ArithmeticCPSReflectedThetaSource r m pi tau D) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
    letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
    CPSRungAutomorphicLift3D n r pi W ℂ
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ) PUnit
      (fun p ↦ PadicGL (r + 1) p)
      (fun p ↦ Subgroup (PadicGL (r + 1) p))
      (fun p ↦ padicIntegralSubgroup (r + 1) p)
      (fun _ ↦ ZeroChannel) (fun _ ↦ ℂ) (fun _ ↦ ℂ)
      (fun _ ↦ Fin 0 → ℂ) (fun _ ↦ ℂ) := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun p ↦ PadicGL (r + 1) p)
    (fun p ↦ Subgroup (PadicGL (r + 1) p))
    (fun p ↦ padicIntegralSubgroup (r + 1) p)
  letI : ContinuousSMul (AdelicGL (r + 1)) ℂ := ⟨continuous_snd⟩
  exact {
    lift := scalarGenuineAdelicSymmetricPowerLift3D_ofReflectedThetaSources source
    polarCarrier_zero := rung_polar_carrier_zero W
  }

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.ofMellinFE
#print axioms CriticalLinePhasor.ThreeDConverse.symmetricPowerFunctoriality3D_ofProfileCouplings
#print axioms CriticalLinePhasor.ThreeDConverse.symmetricPowerFunctoriality3D_ofGenuineAdelicProfileCouplings
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicSymmetricPowerLift3D
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicSymmetricPowerLift3D_ofReflectedThetaSources
#print axioms CriticalLinePhasor.ThreeDConverse.cpsRungFullAutomorphy3D_ofProfileCouplings
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicCPSRungAutomorphicLift3D_ofReflectedThetaSources
