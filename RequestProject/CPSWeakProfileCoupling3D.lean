import RequestProject.CPSBankThetaProfileCoupling3D
import RequestProject.RSAveragedThetaProfile3D

/-!
# The weak profile coupling: the r = 2 rung wired into the coupling type

The strong coupling `BankThetaProfileCoupling3D` has no constant-term fields, and every
prescribed bank readout decays rapidly to zero — while the r = 2 profile, the Petersson
average of the general lattice theta, carries the Petersson mass as its DC mode
(`θ̄_f(t) → ‖f‖² ≠ 0`).  Wiring the profile into the strong type would make the readout
identifications unsatisfiable for `f ≠ 0` — the same vacuity that retired
`ArithmeticBankCoupling3D`.  The profile's home is the weak shape (the house already
recorded this): **the bank carries the AC spectrum, the mass is the DC mode, and the
`ζ`-factor pole is the detected DC residue** — rank-is-DC-residue at the r = 2 rung.

This file lands that wiring, helix style:

* `WeakBankThetaProfileCoupling3D` — the constant-term-carrying coupling: two profiles,
  two masses, one *exact* pointwise reflection (masses included — the weld transforms the
  DC mode consistently), and the two readout identifications tying the literal 3D bank
  projections to the mass-subtracted profiles.  Decay classes now match on both sides:
  the bank readout by the rapid Γ-product kernel, the profile tail by the compiled saddle
  bound `e^{-π√(3t/2)}` — the √-exponential class the corrected coupling was designed for.
* interconversion with the strong type: `BankThetaProfileCoupling3D.toWeak` (masses zero)
  and `WeakBankThetaProfileCoupling3D.toStrong` — so the strong per-rung frontier is the
  weak one at extinguished DC.
* `WeakBankThetaProfileCoupling3D.toWeakFEPair` — the Mathlib `WeakFEPair` of the
  profiles, with local integrability and rapid decay *derived* from the compiled bank
  bounds through the identifications.  Mathlib's abstract machinery then returns, for any
  inhabitant: the entire part, the completed functional equation, and the polar structure
  with residues the masses (`toWeakFEPair_functional_equation`, `toWeakFEPair_residue`).
* `rsAveragedProfileCoupling` — **the r = 2 inhabitant modulo its two named inputs**: the
  profiles are the compiled averaged lattice bank `θ̄_f` of a genuine level-one cusp form,
  the reflection is the compiled Epstein weld under the Petersson average
  (`averagedTheta_inv` — carrier-lattice self-duality, no target automorphy), the masses
  are the Petersson mass, and the exchange data is the fingerprint `ε = 1`, `k = 1`.
  The two hypotheses are exactly the named identification-layer frontier of the rung: the
  ζ-peel from `L(f×f)` to the `Sym²` bank and the coefficient identification with the
  literal twisted Satake bank.  They are inputs, stated — not discharged, not hidden.

No classical `Sym²` functional equation (Shimura/Gelbart–Jacquet) is consumed
anywhere — the reflection is the compiled lattice weld.
-/

open Complex Set Filter MeasureTheory
open scoped Topology

namespace CriticalLinePhasor.GlobalHelix

/-- A theta profile pair with constant terms, coupled to a polynomial Satake bank.  The
reflection is exact with the masses *included* (the weld transforms the DC mode
consistently); the readout identifications tie the literal 3D bank projections to the
mass-subtracted profiles — the bank carries the AC spectrum, the mass is the DC mode. -/
structure WeakBankThetaProfileCoupling3D
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) where
  primalProfile : ℝ → ℂ
  dualProfile : ℝ → ℂ
  primalMass : ℂ
  dualMass : ℂ
  exchangeConstant : ℂ
  exchangeConstant_ne_zero : exchangeConstant ≠ 0
  weight : ℝ
  weight_pos : 0 < weight
  profile_reflection : ∀ x : ℝ, 0 < x →
    primalProfile (1 / x) = (exchangeConstant * (x ^ weight : ℝ)) • dualProfile x
  primal_readout : ∀ x : ℝ, 0 < x →
    cpsPolynomialFullPrimal3DBankReadout W C μs x = primalProfile x - primalMass
  dual_readout : ∀ x : ℝ, 0 < x →
    cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) = dualProfile x - dualMass

namespace WeakBankThetaProfileCoupling3D

variable {ι : Type*} [Fintype ι] {W : PolynomialSatakeDualPair ι} {C : ℝ} {μs : List ℂ}

/-- A weak coupling with extinguished DC modes is a strong coupling. -/
noncomputable def toStrong (G : WeakBankThetaProfileCoupling3D W C μs)
    (hp : G.primalMass = 0) (hd : G.dualMass = 0) :
    BankThetaProfileCoupling3D W C μs where
  primalProfile := G.primalProfile
  dualProfile := G.dualProfile
  exchangeConstant := G.exchangeConstant
  exchangeConstant_ne_zero := G.exchangeConstant_ne_zero
  weight := G.weight
  weight_pos := G.weight_pos
  profile_reflection := G.profile_reflection
  primal_readout := fun x hx => by rw [G.primal_readout x hx, hp, sub_zero]
  dual_readout := fun x hx => by rw [G.dual_readout x hx, hd, sub_zero]

end WeakBankThetaProfileCoupling3D

/-- Every strong coupling is a weak coupling with zero masses: the strong per-rung
frontier is the weak one at extinguished DC. -/
noncomputable def BankThetaProfileCoupling3D.toWeak
    {ι : Type*} [Fintype ι] {W : PolynomialSatakeDualPair ι} {C : ℝ} {μs : List ℂ}
    (G : BankThetaProfileCoupling3D W C μs) :
    WeakBankThetaProfileCoupling3D W C μs where
  primalProfile := G.primalProfile
  dualProfile := G.dualProfile
  primalMass := 0
  dualMass := 0
  exchangeConstant := G.exchangeConstant
  exchangeConstant_ne_zero := G.exchangeConstant_ne_zero
  weight := G.weight
  weight_pos := G.weight_pos
  profile_reflection := G.profile_reflection
  primal_readout := fun x hx => by rw [G.primal_readout x hx, sub_zero]
  dual_readout := fun x hx => by rw [G.dual_readout x hx, sub_zero]

namespace WeakBankThetaProfileCoupling3D

variable {ι : Type*} [Fintype ι] {W : PolynomialSatakeDualPair ι} {C : ℝ} {μs : List ℂ}

/-- The primal profile is locally integrable on the ray: it is the (compiled locally
integrable) bank readout plus its constant DC mode. -/
lemma primalProfile_locallyIntegrableOn (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) :
    LocallyIntegrableOn G.primalProfile (Ioi (0 : ℝ)) volume := by
  have hsum : LocallyIntegrableOn
      (fun x : ℝ => cpsPolynomialFullPrimal3DBankReadout W C μs x + G.primalMass)
      (Ioi (0 : ℝ)) volume :=
    (cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn W C hC μs hne).add
      ((locallyIntegrable_const _).locallyIntegrableOn _)
  refine LocallyIntegrableOn.congr ?_ hsum
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [G.primal_readout x hx]
  ring

/-- The dual profile is locally integrable on the ray. -/
lemma dualProfile_locallyIntegrableOn (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) :
    LocallyIntegrableOn G.dualProfile (Ioi (0 : ℝ)) volume := by
  have hsum : LocallyIntegrableOn
      (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) + G.dualMass)
      (Ioi (0 : ℝ)) volume :=
    (cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn W C hC μs hne).add
      ((locallyIntegrable_const _).locallyIntegrableOn _)
  refine LocallyIntegrableOn.congr ?_ hsum
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [G.dual_readout x hx]
  ring

/-- **The Mathlib weak pair of a weak coupling.**  Local integrability and rapid decay of
the profiles are derived from the compiled bank bounds through the readout
identifications; the reflection is the coupling's own.  Mathlib's abstract machinery then
returns the entire part, the completed functional equation, and the polar structure. -/
noncomputable def toWeakFEPair (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) : WeakFEPair ℂ where
  f := G.primalProfile
  g := G.dualProfile
  k := G.weight
  ε := G.exchangeConstant
  f₀ := G.primalMass
  g₀ := G.dualMass
  hf_int := G.primalProfile_locallyIntegrableOn hC hne
  hg_int := G.dualProfile_locallyIntegrableOn hC hne
  hk := G.weight_pos
  hε := G.exchangeConstant_ne_zero
  h_feq := fun x hx => G.profile_reflection x hx
  hf_top := fun r => by
    have heq : (fun x : ℝ => G.primalProfile x - G.primalMass) =ᶠ[atTop]
        cpsPolynomialFullPrimal3DBankReadout W C μs := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [G.primal_readout x hx]
    exact (cpsPolynomialFullPrimal3DBankReadout_rapid W C hC μs r).congr'
      heq.symm Filter.EventuallyEq.rfl
  hg_top := fun r => by
    have heq : (fun x : ℝ => G.dualProfile x - G.dualMass) =ᶠ[atTop]
        (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [G.dual_readout x hx]
    exact (cpsPolynomialFullDual3DReflectedReadout_rapid W C hC μs r).congr'
      heq.symm Filter.EventuallyEq.rfl

/-- **The completed functional equation of the coupled bank**, read off the weak pair:
`Λ(k − s) = ε • Λ^∨(s)` with the coupling's own weight and exchange constant. -/
theorem toWeakFEPair_functional_equation (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) (s : ℂ) :
    (G.toWeakFEPair hC hne).Λ ((G.weight : ℂ) - s) =
      G.exchangeConstant • (G.toWeakFEPair hC hne).symm.Λ s :=
  (G.toWeakFEPair hC hne).functional_equation s

/-- **The DC mode is the detected residue**: the completed transform of the coupled bank
has residue `ε • dualMass` at the weight edge `s = k` — the rank-is-DC-residue law at the
coupling interface. -/
theorem toWeakFEPair_residue (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) :
    Filter.Tendsto (fun s : ℂ => (s - (G.weight : ℂ)) * (G.toWeakFEPair hC hne).Λ s)
      (𝓝[≠] (G.weight : ℂ)) (𝓝 (G.exchangeConstant • G.dualMass)) :=
  (G.toWeakFEPair hC hne).Λ_residue_k

/-- The entire part of the completed transform of the coupled bank. -/
theorem toWeakFEPair_entire (G : WeakBankThetaProfileCoupling3D W C μs)
    (hC : 0 < C) (hne : μs ≠ []) :
    Differentiable ℂ (G.toWeakFEPair hC hne).Λ₀ :=
  (G.toWeakFEPair hC hne).differentiable_Λ₀

end WeakBankThetaProfileCoupling3D

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HeckeSupBound
open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Set
open scoped Real MatrixGroups Topology

variable {k : ℤ}

/-- **The r = 2 rung wired into the weak coupling type, helix style.**  The profiles are
the compiled averaged lattice bank `θ̄_f` of a genuine level-one cusp form; the reflection
is the compiled Epstein weld under the Petersson average (`averagedTheta_inv` —
carrier-lattice self-duality on `ℤ²`, certifier (a), no target automorphy consumed); the
masses are the Petersson mass (the DC mode; its detected residue is the `ζ`-factor pole);
the fingerprint is `ε = 1`, weight `1`.

The two hypotheses are the rung's *named* identification-layer inputs — the ζ-peel from
`L(f×f)` to the `Sym²` bank and the coefficient identification with the literal twisted
Satake bank.  Both sides of each identification decay to zero in the same √-exponential
class (bank: rapid Γ-product kernel; profile tail: compiled saddle bound), so the type is
not vacuous — this is the decay-class match the corrected coupling was designed around. -/
noncomputable def rsAveragedProfileCoupling
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (f : CuspForm 𝒮ℒ k)
    (hprimal : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout W C μs x =
        averagedThetaC k f x - ((peterssonMass k f : ℝ) : ℂ))
    (hdual : ∀ x : ℝ, 0 < x →
      cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) =
        averagedThetaC k f x - ((peterssonMass k f : ℝ) : ℂ)) :
    WeakBankThetaProfileCoupling3D W C μs where
  primalProfile := averagedThetaC k f
  dualProfile := averagedThetaC k f
  primalMass := ((peterssonMass k f : ℝ) : ℂ)
  dualMass := ((peterssonMass k f : ℝ) : ℂ)
  exchangeConstant := 1
  exchangeConstant_ne_zero := one_ne_zero
  weight := 1
  weight_pos := one_pos
  profile_reflection := fun x hx => by
    unfold averagedThetaC
    rw [one_div, averagedTheta_inv f hx, Real.rpow_one]
    push_cast
    ring
  primal_readout := hprimal
  dual_readout := hdual

/-- Fingerprint: the wired r = 2 rung has exchange constant `1`. -/
@[simp] lemma rsAveragedProfileCoupling_exchangeConstant
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (f : CuspForm 𝒮ℒ k) (hprimal) (hdual) :
    (rsAveragedProfileCoupling W C μs f hprimal hdual).exchangeConstant = 1 := rfl

/-- Fingerprint: the wired r = 2 rung has weight `1`. -/
@[simp] lemma rsAveragedProfileCoupling_weight
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (f : CuspForm 𝒮ℒ k) (hprimal) (hdual) :
    (rsAveragedProfileCoupling W C μs f hprimal hdual).weight = 1 := rfl

/-- The DC mode of the wired r = 2 rung is the Petersson mass. -/
@[simp] lemma rsAveragedProfileCoupling_primalMass
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (f : CuspForm 𝒮ℒ k) (hprimal) (hdual) :
    (rsAveragedProfileCoupling W C μs f hprimal hdual).primalMass =
      ((peterssonMass k f : ℝ) : ℂ) := rfl

/-- The dual DC mode of the wired r = 2 rung is also the Petersson mass. -/
@[simp] lemma rsAveragedProfileCoupling_dualMass
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (μs : List ℂ)
    (f : CuspForm 𝒮ℒ k) (hprimal) (hdual) :
    (rsAveragedProfileCoupling W C μs f hprimal hdual).dualMass =
      ((peterssonMass k f : ℝ) : ℂ) := rfl

/-- **The Petersson mass is the detected residue of the wired r = 2 bank**: the completed
transform of the coupled bank has residue `‖f‖²` at the weight edge — the `ζ`-factor pole
of `L(f×f)` read as the DC mode of the averaged lattice bank, at the coupling interface. -/
theorem rsAveragedProfileCoupling_residue
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (C : ℝ) (hC : 0 < C)
    (μs : List ℂ) (hne : μs ≠ []) (f : CuspForm 𝒮ℒ k) (hprimal) (hdual) :
    Filter.Tendsto (fun s : ℂ =>
        (s - 1) * ((rsAveragedProfileCoupling W C μs f hprimal hdual).toWeakFEPair
          hC hne).Λ s)
      (𝓝[≠] 1) (𝓝 ((peterssonMass k f : ℝ) : ℂ)) := by
  have h := (rsAveragedProfileCoupling W C μs f hprimal hdual).toWeakFEPair_residue hC hne
  simpa using h

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.GlobalHelix.WeakBankThetaProfileCoupling3D.toStrong
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.toWeak
#print axioms CriticalLinePhasor.GlobalHelix.WeakBankThetaProfileCoupling3D.toWeakFEPair
#print axioms CriticalLinePhasor.GlobalHelix.WeakBankThetaProfileCoupling3D.toWeakFEPair_functional_equation
#print axioms CriticalLinePhasor.GlobalHelix.WeakBankThetaProfileCoupling3D.toWeakFEPair_residue
#print axioms CriticalLinePhasor.Unfolding.rsAveragedProfileCoupling
#print axioms CriticalLinePhasor.Unfolding.rsAveragedProfileCoupling_residue
