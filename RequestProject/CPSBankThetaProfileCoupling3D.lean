import RequestProject.CPSGenuineGL2StandardRung3D

/-!
# The bank theta-profile coupling: the per-rung obligation as one pointwise reflection

This file re-types the genuine-source coupling of the CPS tower.  The retired shape
(`ArithmeticBankCoupling3D`) demanded that the twisted bank readout equal a weight-`2n` cusp
form's raw vertical value; that type is uninhabitable on genuine data — the tensor completion
kernel has Bessel-type decay `e^{-c√x}` while a modular vertical restriction decays like
`e^{-2πx}`.  The corrected obligation is a **theta profile pair**: two functions on the positive
ray, one pointwise weighted reflection between them, and the two identifications of the literal
bank readouts with those profiles.  Nothing else.

Three constructors discharge everything downstream:

* `BankThetaProfileCoupling3D.toReflectedThetaSource` — the reflected `StrongFEPair` source over
  an arbitrary polynomial Satake bank, with local integrability and rapid decay derived;
* `BankThetaProfileCoupling3D.toCarrierSeed` — the geometric carrier seed of the twist bank: the
  carrier functions are built by de-enveloping the profiles and the conjugation exchange law is
  derived from the pointwise reflection, not supplied;
* `ArithmeticCPSCarrierSeed3D.toProfileCoupling` — the converse: a carrier seed's completed
  logarithmic thetas form a profile pair.  The seed-typed and profile-typed obligations therefore
  interconvert: the per-rung frontier is exactly one pointwise theta reflection.

`allProfileCarrierSeeds` packages per-twist profile couplings into the seed family consumed by
`ArithmeticCPSAllTwistsConverseCandidate3D.ofCarrierSeeds`.  The standard rung of an actual
level-one cusp form (`StandardRungEulerData.toProfileCoupling`) inhabits the type genuinely: its
reflection is the compiled `standardRung_reflection`, derived from the modular slash law.
-/

open Complex Set

namespace CriticalLinePhasor.GlobalHelix

/-- The self-dual envelope is a nonzero complex scalar at every positive height. -/
private theorem envelope_ofReal_ne_zero (k : ℝ) {x : ℝ} (hx : 0 < x) :
    ((CriticalLinePhasor.StrandExchange.selfDualEnvelope k x : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < CriticalLinePhasor.StrandExchange.selfDualEnvelope k x := by
    unfold CriticalLinePhasor.StrandExchange.selfDualEnvelope
    positivity
  exact_mod_cast hpos.ne'

/-- A theta profile pair coupled to a polynomial Satake bank.  The two profiles are independent
functions on the ray; `profile_reflection` is the single analytic obligation of the rung, and the
two readout fields are the identification-layer data tying the literal 3D bank projections to the
profiles.  No carrier function, exchange law, analytic candidate, or strong pair is a field. -/
structure BankThetaProfileCoupling3D
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) where
  primalProfile : ℝ → ℂ
  dualProfile : ℝ → ℂ
  exchangeConstant : ℂ
  exchangeConstant_ne_zero : exchangeConstant ≠ 0
  weight : ℝ
  weight_pos : 0 < weight
  profile_reflection : ∀ x : ℝ, 0 < x →
    primalProfile (1 / x) = (exchangeConstant * (x ^ weight : ℝ)) • dualProfile x
  primal_readout : ∀ x : ℝ, 0 < x →
    cpsPolynomialFullPrimal3DBankReadout W C μs x = primalProfile x
  dual_readout : ∀ x : ℝ, 0 < x →
    cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) = dualProfile x

namespace BankThetaProfileCoupling3D

variable {ι : Type*} [Fintype ι] {W : PolynomialSatakeDualPair ι} {C : ℝ} {μs : List ℂ}

/-- The literal-bank reflection derived from the profile reflection and the two readout
identifications: the banks themselves satisfy the weighted theta functional equation. -/
theorem bank_reflection (G : BankThetaProfileCoupling3D W C μs) :
    ∀ x : ℝ, 0 < x →
      cpsPolynomialFullPrimal3DBankReadout W C μs (1 / x) =
        (G.exchangeConstant * (x ^ G.weight : ℝ)) •
          cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x) := by
  intro x hx
  rw [G.primal_readout (1 / x) (one_div_pos.mpr hx), G.profile_reflection x hx,
    G.dual_readout x hx]

/-- The reflected theta source of an arbitrary polynomial Satake bank, constructed from a theta
profile coupling.  The `StrongFEPair` reflection is `bank_reflection`; local integrability and
rapid decay are derived from the polynomial coefficient bounds and the prescribed clock. -/
noncomputable def toReflectedThetaSource
    (G : BankThetaProfileCoupling3D W C μs) (hC : 0 < C) (hne : μs ≠ []) :
    CriticalLinePhasor.GenuineGL2Carrier.PolynomialBankReflectedThetaSource W C μs where
  pair := {
    toWeakFEPair := {
      f := cpsPolynomialFullPrimal3DBankReadout W C μs
      g := fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)
      k := G.weight
      ε := G.exchangeConstant
      f₀ := 0
      g₀ := 0
      hf_int := cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn W C hC μs hne
      hg_int := cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn W C hC μs hne
      hk := G.weight_pos
      hε := G.exchangeConstant_ne_zero
      h_feq := fun x hx => G.bank_reflection x hx
      hf_top := fun q => by
        simpa using cpsPolynomialFullPrimal3DBankReadout_rapid W C hC μs q
      hg_top := fun q => by
        simpa using cpsPolynomialFullDual3DReflectedReadout_rapid W C hC μs q
    }
    hf₀ := rfl
    hg₀ := rfl
  }
  primal_source := rfl
  dual_source := rfl

end BankThetaProfileCoupling3D

/-- The geometric carrier seed constructed from a theta profile coupling of the twist bank.  The
two carrier functions are the de-enveloped profiles read on the logarithmic coordinate, and the
global conjugation exchange law is **derived** from the pointwise profile reflection and the
envelope inversion — it is not a supplied field. -/
noncomputable def BankThetaProfileCoupling3D.toCarrierSeed
    {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    {tau : PolynomialSatakeDualPair (Fin m)} {D : ArithmeticCPSCompletionData r m}
    (G : BankThetaProfileCoupling3D (arithmeticCPSPolynomialTwist r m pi tau)
      D.conductor D.tensorShifts) :
    ArithmeticCPSCarrierSeed3D r m pi tau D where
  primalCarrier := fun z => G.primalProfile (Real.exp z.im) /
    (CriticalLinePhasor.StrandExchange.selfDualEnvelope G.weight (Real.exp z.im) : ℂ)
  dualCarrier := fun z => G.dualProfile (Real.exp z.im) /
    (CriticalLinePhasor.StrandExchange.selfDualEnvelope G.weight (Real.exp z.im) : ℂ)
  exchangeConstant := G.exchangeConstant
  exchangeConstant_ne_zero := G.exchangeConstant_ne_zero
  weight := G.weight
  weight_pos := G.weight_pos
  carrier_exchange := by
    intro z
    have hx : (0 : ℝ) < Real.exp z.im := Real.exp_pos _
    simp only [Complex.conj_im, Real.exp_neg]
    have hrefl := G.profile_reflection (Real.exp z.im) hx
    rw [one_div] at hrefl
    have henv : CriticalLinePhasor.StrandExchange.selfDualEnvelope G.weight (Real.exp z.im)⁻¹ =
        (Real.exp z.im) ^ G.weight *
          CriticalLinePhasor.StrandExchange.selfDualEnvelope G.weight (Real.exp z.im) := by
      simpa only [one_div] using
        CriticalLinePhasor.StrandExchange.selfDualEnvelope_one_div G.weight hx
    rw [hrefl, henv, smul_eq_mul]
    have hxw : (((Real.exp z.im) ^ G.weight : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hx _).ne'
    have henvne := envelope_ofReal_ne_zero G.weight hx
    push_cast
    field_simp
  primal_carrier := by
    intro x hx
    rw [G.primal_readout x hx]
    simp only [CriticalLinePhasor.StrandExchange.completedLogTheta,
      CriticalLinePhasor.StrandExchange.logTheta,
      CriticalLinePhasor.StrandExchange.logReadout, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]
    rw [Real.exp_log hx]
    have henvne := envelope_ofReal_ne_zero G.weight hx
    field_simp
  dual_carrier := by
    intro x hx
    rw [G.dual_readout x hx]
    simp only [CriticalLinePhasor.StrandExchange.completedLogTheta,
      CriticalLinePhasor.StrandExchange.logTheta,
      CriticalLinePhasor.StrandExchange.logReadout, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]
    rw [Real.exp_log hx]
    have henvne := envelope_ofReal_ne_zero G.weight hx
    field_simp

/-- The converse: every carrier seed yields a theta profile coupling — its completed logarithmic
thetas are the profiles, and the profile reflection is the compiled transport of the conjugation
exchange through the logarithmic readout.  Together with
`BankThetaProfileCoupling3D.toCarrierSeed`, the seed-typed and profile-typed per-rung obligations
interconvert. -/
noncomputable def ArithmeticCPSCarrierSeed3D.toProfileCoupling
    {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    {tau : PolynomialSatakeDualPair (Fin m)} {D : ArithmeticCPSCompletionData r m}
    (G : ArithmeticCPSCarrierSeed3D r m pi tau D) :
    BankThetaProfileCoupling3D (arithmeticCPSPolynomialTwist r m pi tau)
      D.conductor D.tensorShifts where
  primalProfile := CriticalLinePhasor.StrandExchange.completedLogTheta G.primalCarrier G.weight
  dualProfile := CriticalLinePhasor.StrandExchange.completedLogTheta G.dualCarrier G.weight
  exchangeConstant := G.exchangeConstant
  exchangeConstant_ne_zero := G.exchangeConstant_ne_zero
  weight := G.weight
  weight_pos := G.weight_pos
  profile_reflection := fun _ hx =>
    CriticalLinePhasor.StrandExchange.completedLogTheta_pair_one_div
      G.primalCarrier G.dualCarrier G.exchangeConstant G.carrier_exchange G.weight hx
  primal_readout := G.primal_carrier
  dual_readout := G.dual_carrier

/-- Per-twist theta profile couplings assemble into the exact carrier-seed family consumed by
`ArithmeticCPSAllTwistsConverseCandidate3D.ofCarrierSeeds`: supply this family together with the
restricted-product representation, the bank bridge, and the residual channels, and the all-twist
converse candidate follows with no reflected source or analytic candidate supplied anywhere. -/
noncomputable def allProfileCarrierSeeds
    {r : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
      (D : ArithmeticCPSCompletionData r m) →
        BankThetaProfileCoupling3D (arithmeticCPSPolynomialTwist r m pi tau)
          D.conductor D.tensorShifts) :
    ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
      (D : ArithmeticCPSCompletionData r m) →
        ArithmeticCPSCarrierSeed3D r m pi tau D :=
  fun m hm hmr tau D => (coupling m hm hmr tau D).toCarrierSeed

end CriticalLinePhasor.GlobalHelix

namespace CriticalLinePhasor.GenuineGL2Carrier

open CriticalLinePhasor.GlobalHelix

/-- The standard rung of a genuine level-one cusp form inhabits the theta profile coupling: the
profiles are the literal bank readouts, and the reflection is `standardRung_reflection`, derived
from the modular slash law.  This is the non-vacuity certificate of the corrected coupling type. -/
noncomputable def StandardRungEulerData.toProfileCoupling
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    BankThetaProfileCoupling3D pi 1 [standardShift n] where
  primalProfile := cpsPolynomialFullPrimal3DBankReadout pi 1 [standardShift n]
  dualProfile := fun x : ℝ =>
    cpsPolynomialFullDual3DTransformedReadout pi 1 [standardShift n] (1 / x)
  exchangeConstant := Complex.I ^ (2 * n)
  exchangeConstant_ne_zero := pow_ne_zero _ Complex.I_ne_zero
  weight := 1
  weight_pos := one_pos
  profile_reflection := fun x hx => standardRung_reflection data x hx
  primal_readout := fun _ _ => rfl
  dual_readout := fun _ _ => rfl

end CriticalLinePhasor.GenuineGL2Carrier

#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.bank_reflection
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.toReflectedThetaSource
#print axioms CriticalLinePhasor.GlobalHelix.BankThetaProfileCoupling3D.toCarrierSeed
#print axioms CriticalLinePhasor.GlobalHelix.ArithmeticCPSCarrierSeed3D.toProfileCoupling
#print axioms CriticalLinePhasor.GlobalHelix.allProfileCarrierSeeds
#print axioms CriticalLinePhasor.GenuineGL2Carrier.StandardRungEulerData.toProfileCoupling
