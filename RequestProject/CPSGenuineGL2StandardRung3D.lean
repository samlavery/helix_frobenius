import RequestProject.CPSGenuineGL2CarrierSeed3D

/-!
# The genuine GL(2) standard rung: a reflected theta source constructed from a cusp form

This file constructs the first `StrongFEPair` whose two source functions are literal polynomial
Satake 3D bank readouts and whose reflection is derived from the modular slash law of an actual
level-one cusp form — not supplied as a field.

The rung is the *standard* (degree-two) object of a weight-`2n` form, in the det-one
(analytic-normalization) chart: archimedean shift `n - 1/2`, conductor `1`, reflection weight `1`,
exchange constant `I^(2n)`.  The one arithmetic input is `StandardRungEulerData`: the
identification of the bank's multiplicative Euler coefficients with the form's canonical Mathlib
`qExpansion` coefficients (the Hecke-eigenform datum, a cited classical input of the
identification layer), together with the det-one self-duality of the coefficient bank.  Every
analytic field — the q-expansion convergence, the kernel evaluation, the theta identity, the
reflection, local integrability, and rapid decay — is derived, not assumed.
-/

open Complex UpperHalfPlane MatrixGroups

namespace CriticalLinePhasor.GenuineGL2Carrier

open CriticalLinePhasor.HeckeCancellation
open CriticalLinePhasor.GlobalHelix

/-- The det-one archimedean shift of the weight-`2n` standard rung, as a real exponent. -/
noncomputable def standardShiftR (n : ℕ) : ℝ := (n : ℝ) - 2⁻¹

/-- The det-one archimedean shift of the weight-`2n` standard rung. -/
noncomputable def standardShift (n : ℕ) : ℂ := (standardShiftR n : ℂ)

/-- The radial envelope of the standard rung at carrier height `x`. -/
noncomputable def standardEnvelope (n : ℕ) (x : ℝ) : ℂ :=
  ((x ^ standardShiftR n : ℝ) : ℂ)

/-- The arithmetic Euler certificate of the standard rung: the canonical Mathlib q-expansion
coefficients of the cusp form are the det-one-normalized Euler coefficients of the Satake bank,
and the contragredient bank coincides with the primal bank (det-one self-duality).  This is the
identification-layer datum; every analytic conclusion below is derived from it. -/
structure StandardRungEulerData (n : ℕ) (pi : PolynomialSatakeDualPair (Fin 2)) where
  form : CuspForm 𝒮ℒ (2 * n : ℤ)
  n_pos : 0 < n
  coeff_eq : ∀ j : ℕ,
    (UpperHalfPlane.qExpansion 1 ⇑form).coeff (j + 1) =
      2 * cpsPolynomialPrimalCoeff pi j * ((j + 1 : ℕ) : ℂ) ^ standardShift n
  dual_eq : ∀ j : ℕ, cpsPolynomialDualCoeff pi j = cpsPolynomialPrimalCoeff pi j

/-- The level-one q-parameter on the vertical line is the real exponential kernel. -/
private theorem qParam_vert (x : ℝ) (hx : 0 < x) :
    Function.Periodic.qParam 1 ((vert x hx : ℍ) : ℂ) =
      Complex.exp (-(2 * Real.pi : ℂ) * x) := by
  unfold Function.Periodic.qParam
  rw [vert_coe]
  congr 1
  simp only [Complex.ofReal_one, div_one]
  linear_combination (2 * (Real.pi : ℂ) * x) * Complex.I_mul_I

/-- The q-expansion of a level-one cusp form sums on the vertical line, reindexed to start at the
first coefficient: the constant term vanishes by cuspidality. -/
private theorem form_hasSum (n : ℕ) (f : CuspForm 𝒮ℒ (2 * n : ℤ)) (x : ℝ) (hx : 0 < x) :
    HasSum
      (fun j : ℕ => (UpperHalfPlane.qExpansion 1 ⇑f).coeff (j + 1) *
        Complex.exp (-(2 * Real.pi : ℂ) * ((((j + 1 : ℕ) : ℝ) * x : ℝ) : ℂ)))
      (f (vert x hx)) := by
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hsum := UpperHalfPlane.hasSum_qExpansion one_pos hper
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (vert x hx)
  have hcoeff0 : (UpperHalfPlane.qExpansion 1 ⇑f).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL
  -- rewrite the q-power as the exponential kernel
  have hterm : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion 1 ⇑f).coeff m •
          Function.Periodic.qParam 1 ((vert x hx : ℍ) : ℂ) ^ m =
        (UpperHalfPlane.qExpansion 1 ⇑f).coeff m *
          Complex.exp (-(2 * Real.pi : ℂ) * (((m : ℝ) * x : ℝ) : ℂ)) := by
    intro m
    rw [qParam_vert x hx, smul_eq_mul, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [funext hterm] at hsum
  -- drop the vanishing constant term
  have h1 := (hasSum_nat_add_iff' (f := fun m : ℕ =>
      (UpperHalfPlane.qExpansion 1 ⇑f).coeff m *
        Complex.exp (-(2 * Real.pi : ℂ) * (((m : ℝ) * x : ℝ) : ℂ))) 1).mpr hsum
  simp only [Finset.range_one, Finset.sum_singleton, hcoeff0, zero_mul, sub_zero] at h1
  convert h1 using 2 with j

/-- The single archimedean clock at the standard shift, evaluated at a positive height. -/
private theorem gammaClock_standard (n : ℕ) {y : ℝ} (hy : 0 < y) :
    gammaClock (standardShift n) y =
      2 * ((y ^ standardShiftR n : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi : ℂ) * y) := by
  unfold gammaClock standardShift
  rw [← Complex.ofReal_cpow hy.le]

/-- **The theta engine of the standard rung.**  Under the Euler certificate, the completed
coefficient theta of the bank at the single det-one clock is the enveloped vertical value of the
genuine cusp form.  This is the analytic half of the coupling: q-expansion convergence plus exact
kernel evaluation, no reflection consumed. -/
theorem theta_standard_eq
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) (x : ℝ) (hx : 0 < x) :
    CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff pi)
        (conductorScaledCompletionKernelLog 1 [standardShift n]) x =
      standardEnvelope n x * data.form (vert x hx) := by
  unfold CriticalLinePhasor.CarrierTheta.theta
  have hterm : ∀ j : ℕ,
      cpsPolynomialPrimalCoeff pi j *
        conductorScaledCompletionKernelLog 1 [standardShift n] (((j + 1 : ℕ) : ℝ) * x) =
      standardEnvelope n x *
        ((UpperHalfPlane.qExpansion 1 ⇑data.form).coeff (j + 1) *
          Complex.exp (-(2 * Real.pi : ℂ) * ((((j + 1 : ℕ) : ℝ) * x : ℝ) : ℂ))) := by
    intro j
    have hy : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * x := by positivity
    have hker : conductorScaledCompletionKernelLog 1 [standardShift n]
        (((j + 1 : ℕ) : ℝ) * x) =
        gammaClock (standardShift n) (((j + 1 : ℕ) : ℝ) * x) := by
      simp [conductorScaledCompletionKernelLog, completionKernelLog]
    rw [hker, gammaClock_standard n hy, data.coeff_eq j]
    have hsplit : ((((j + 1 : ℕ) : ℝ) * x) ^ standardShiftR n : ℝ) =
        (((j + 1 : ℕ) : ℝ) ^ standardShiftR n) * (x ^ standardShiftR n) :=
      Real.mul_rpow (by positivity) hx.le
    have hcast : ((j + 1 : ℕ) : ℂ) ^ standardShift n =
        ((((j + 1 : ℕ) : ℝ) ^ standardShiftR n : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      norm_cast
    rw [hcast]
    unfold standardEnvelope
    rw [hsplit]
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left, (form_hasSum n data.form x hx).tsum_eq]

/-- The primal 3D bank readout of the standard rung is the enveloped genuine modular value. -/
theorem standardRung_primalReadout_eq
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) (x : ℝ) (hx : 0 < x) :
    cpsPolynomialFullPrimal3DBankReadout pi 1 [standardShift n] x =
      standardEnvelope n x * data.form (vert x hx) := by
  rw [cpsPolynomialFullPrimal3DBankReadout_eq_theta pi 1 [standardShift n] hx]
  exact theta_standard_eq data x hx

/-- The transformed contragredient 3D bank readout of the standard rung is the same enveloped
modular value: det-one self-duality of the coefficient bank. -/
theorem standardRung_dualTransformedReadout_eq
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) (x : ℝ) (hx : 0 < x) :
    cpsPolynomialFullDual3DTransformedReadout pi 1 [standardShift n] (1 / x) =
      standardEnvelope n x * data.form (vert x hx) := by
  rw [cpsPolynomialFullDual3DTransformedReadout_eq_theta_one_div pi 1 [standardShift n]
    (one_div_pos.mpr hx), one_div_one_div]
  have hdual : CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialDualCoeff pi)
      (conductorScaledCompletionKernelLog 1 [standardShift n]) x =
      CriticalLinePhasor.CarrierTheta.theta (cpsPolynomialPrimalCoeff pi)
        (conductorScaledCompletionKernelLog 1 [standardShift n]) x := by
    unfold CriticalLinePhasor.CarrierTheta.theta
    exact tsum_congr fun j => by rw [data.dual_eq j]
  rw [hdual]
  exact theta_standard_eq data x hx

/-- The envelope algebra of the reflection: inversion of the height composes with the modular
weight factor into the weight-one reflection of the analytic chart. -/
private theorem standardEnvelope_inversion (n : ℕ) {x : ℝ} (hx : 0 < x) :
    standardEnvelope n (1 / x) * ((x : ℂ) * Complex.I) ^ (2 * n) =
      Complex.I ^ (2 * n) * ((x ^ (1 : ℝ) : ℝ) : ℂ) * standardEnvelope n x := by
  unfold standardEnvelope
  have hreal : ((1 / x) ^ standardShiftR n : ℝ) * (x ^ (2 * n : ℕ) : ℝ) =
      (x ^ (1 : ℝ) : ℝ) * (x ^ standardShiftR n : ℝ) := by
    rw [one_div, ← Real.rpow_natCast x (2 * n), Real.inv_rpow hx.le,
      ← Real.rpow_neg hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    unfold standardShiftR
    push_cast
    ring
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hcast
  rw [mul_pow]
  linear_combination Complex.I ^ (2 * n) * hcast

/-- **The native reflection of the standard rung, derived from modularity.**  The primal bank
readout at inverted height equals the exchange constant `I^(2n)` times the weight-one factor
times the transformed contragredient readout.  The proof consumes the two engine identities and
Hecke's inversion — the modular slash law on the vertical line — and nothing else: no analytic
candidate, no reflected source, no supplied theta reflection. -/
theorem standardRung_reflection
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) (x : ℝ) (hx : 0 < x) :
    cpsPolynomialFullPrimal3DBankReadout pi 1 [standardShift n] (1 / x) =
      (Complex.I ^ (2 * n) * ((x ^ (1 : ℝ) : ℝ) : ℂ)) •
        cpsPolynomialFullDual3DTransformedReadout pi 1 [standardShift n] (1 / x) := by
  have hxinv : (0 : ℝ) < 1 / x := one_div_pos.mpr hx
  rw [standardRung_primalReadout_eq data (1 / x) hxinv,
    standardRung_dualTransformedReadout_eq data x hx]
  have hvert : data.form (vert (1 / x) hxinv) =
      ((x : ℂ) * Complex.I) ^ (2 * n) * data.form (vert x hx) := by
    have h := hecke_inversion data.form x hx
    have hv : vert (1 / x) hxinv = vert x⁻¹ (inv_pos.mpr hx) := by
      congr 1
      exact one_div x
    rw [hv, h]
    congr 1
  rw [hvert, smul_eq_mul]
  calc standardEnvelope n (1 / x) *
        (((x : ℂ) * Complex.I) ^ (2 * n) * data.form (vert x hx))
      = (standardEnvelope n (1 / x) * ((x : ℂ) * Complex.I) ^ (2 * n)) *
          data.form (vert x hx) := by ring
    _ = (Complex.I ^ (2 * n) * ((x ^ (1 : ℝ) : ℝ) : ℂ) * standardEnvelope n x) *
          data.form (vert x hx) := by rw [standardEnvelope_inversion n hx]
    _ = Complex.I ^ (2 * n) * ((x ^ (1 : ℝ) : ℝ) : ℂ) *
          (standardEnvelope n x * data.form (vert x hx)) := by ring

/-- A reflected theta source over an arbitrary polynomial Satake bank and completion clock: one
`StrongFEPair` whose two functions are literally the bank's primal and transformed contragredient
3D readouts.  `ArithmeticCPSReflectedThetaSource` is the twist-bank instance of this shape. -/
structure PolynomialBankReflectedThetaSource
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (C : ℝ) (μs : List ℂ) where
  pair : StrongFEPair ℂ
  primal_source : pair.f = cpsPolynomialFullPrimal3DBankReadout W C μs
  dual_source : pair.g = fun x : ℝ =>
    cpsPolynomialFullDual3DTransformedReadout W C μs (1 / x)

/-- The general reflected source specializes to the arithmetic CPS twist typing when the bank is
the literal twist bank with its prescribed completion data. -/
noncomputable def PolynomialBankReflectedThetaSource.toArithmeticCPS
    {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    {tau : PolynomialSatakeDualPair (Fin m)}
    {D : ArithmeticCPSCompletionData r m}
    (S : PolynomialBankReflectedThetaSource
      (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts) :
    ArithmeticCPSReflectedThetaSource r m pi tau D :=
  ⟨S.pair, S.primal_source, S.dual_source⟩

/-- **The existence constructor of the standard rung.**  From a genuine level-one cusp form and
its Euler certificate, the complete reflected theta source of the standard bank is constructed:
the reflection is `standardRung_reflection` (derived from the modular slash law), and local
integrability and rapid decay are derived from the polynomial coefficient bounds and the
prescribed clock.  No field of the output is supplied as an analytic hypothesis. -/
noncomputable def StandardRungEulerData.toReflectedThetaSource
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    PolynomialBankReflectedThetaSource pi 1 [standardShift n] where
  pair := {
    toWeakFEPair := {
      f := cpsPolynomialFullPrimal3DBankReadout pi 1 [standardShift n]
      g := fun x : ℝ =>
        cpsPolynomialFullDual3DTransformedReadout pi 1 [standardShift n] (1 / x)
      k := 1
      ε := Complex.I ^ (2 * n)
      f₀ := 0
      g₀ := 0
      hf_int := cpsPolynomialFullPrimal3DBankReadout_locallyIntegrableOn pi 1 one_pos
        [standardShift n] (by simp)
      hg_int := cpsPolynomialFullDual3DReflectedReadout_locallyIntegrableOn pi 1 one_pos
        [standardShift n] (by simp)
      hk := one_pos
      hε := pow_ne_zero _ Complex.I_ne_zero
      h_feq := fun x hx => standardRung_reflection data x hx
      hf_top := fun q => by
        simpa using cpsPolynomialFullPrimal3DBankReadout_rapid pi 1 one_pos
          [standardShift n] q
      hg_top := fun q => by
        simpa using cpsPolynomialFullDual3DReflectedReadout_rapid pi 1 one_pos
          [standardShift n] q
    }
    hf₀ := rfl
    hg₀ := rfl
  }
  primal_source := rfl
  dual_source := rfl

/-- The completed Mellin transform of the constructed standard-rung source is entire. -/
theorem standardRung_completed_entire
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    Differentiable ℂ data.toReflectedThetaSource.pair.Λ :=
  data.toReflectedThetaSource.pair.differentiable_Λ

/-- The weight of the constructed standard-rung pair is one: the analytic-normalization chart. -/
@[simp] theorem toReflectedThetaSource_pair_k
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    data.toReflectedThetaSource.pair.k = 1 := rfl

/-- The root number of the constructed standard-rung pair is the modular exchange constant. -/
@[simp] theorem toReflectedThetaSource_pair_ε
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    data.toReflectedThetaSource.pair.ε = Complex.I ^ (2 * n) := rfl

/-- The constructed standard-rung source satisfies the completed global functional equation with
weight one and root number `I^(2n)`. -/
theorem standardRung_functional_equation
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) (s : ℂ) :
    data.toReflectedThetaSource.pair.Λ (1 - s) =
      Complex.I ^ (2 * n) • data.toReflectedThetaSource.pair.symm.Λ s := by
  have h := data.toReflectedThetaSource.pair.functional_equation s
  rw [toReflectedThetaSource_pair_k, toReflectedThetaSource_pair_ε] at h
  simpa using h

/-! ## Deriving the dual-bank equality from the det-one normalization

The certificate field `dual_eq` is not an independent arithmetic input: for a det-one Satake
pair the dual weight family is the swap of the primal family, and the Euler coefficients are
symmetric functions of the weights.  `StandardRungEulerData.ofDetOne` therefore builds the
certificate from Hecke multiplicativity and the det-one normalization alone — the sole
remaining arithmetic field is `coeff_eq`. -/

/-- The local Euler coefficient is a symmetric function of the weight family: invariant under
reindexing the channel type by any equivalence. -/
theorem radialLocalEulerCoeff_comp_equiv
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (w : ι → ℂ) (n : ℕ) :
    radialLocalEulerCoeff (w ∘ e) n = radialLocalEulerCoeff w n := by
  classical
  unfold CriticalLinePhasor.GlobalHelix.radialLocalEulerCoeff
  refine Finset.sum_nbij' (fun l => Finsupp.equivMapDomain e l)
    (fun l => Finsupp.equivMapDomain e.symm l) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl ⊢
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ i, Finsupp.equivMapDomain e l i = ∑ i, l (e.symm i) := by
          simp [Finsupp.equivMapDomain_apply]
      _ = ∑ i', l i' := Equiv.sum_comp e.symm l
      _ = n := hl.1
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl ⊢
    refine ⟨?_, Finset.subset_univ _⟩
    calc ∑ i', Finsupp.equivMapDomain e.symm l i' = ∑ i', l (e i') := by
          simp [Finsupp.equivMapDomain_apply]
      _ = ∑ i, l i := Equiv.sum_comp e l
      _ = n := hl.1
  · intro l _
    ext i'
    simp [Finsupp.equivMapDomain_apply]
  · intro l _
    ext i
    simp [Finsupp.equivMapDomain_apply]
  · intro l _
    refine Fintype.prod_equiv e
      (fun i' => (w ∘ e) i' ^ l i')
      (fun i => w i ^ Finsupp.equivMapDomain e l i) fun i' => ?_
    simp [Finsupp.equivMapDomain_apply]

/-- The all-place coefficient bank is invariant under channel reindexing at every place. -/
theorem radialGlobalSatakeCoeff_comp_equiv
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (w : Nat.Primes → ι → ℂ) (n : ℕ) :
    radialGlobalSatakeCoeff (fun p => w p ∘ e) n = radialGlobalSatakeCoeff w n := by
  unfold CriticalLinePhasor.GlobalHelix.radialGlobalSatakeCoeff
  exact Finset.prod_congr rfl fun p _ => radialLocalEulerCoeff_comp_equiv e (w _) _

/-- For a det-one rank-two pair the dual weight family is the swap of the primal family. -/
theorem dual_eq_primal_comp_swap
    (pi : PolynomialSatakeDualPair (Fin 2))
    (hdet : ∀ p, pi.primal p 1 = (pi.primal p 0)⁻¹) (p : Nat.Primes) :
    pi.dual p = pi.primal p ∘ Equiv.swap (0 : Fin 2) 1 := by
  funext i
  rw [pi.dual_eq_inv]
  fin_cases i
  · show (pi.primal p 0)⁻¹ = pi.primal p (Equiv.swap (0 : Fin 2) 1 0)
    rw [Equiv.swap_apply_left]
    exact (hdet p).symm
  · show (pi.primal p 1)⁻¹ = pi.primal p (Equiv.swap (0 : Fin 2) 1 1)
    rw [Equiv.swap_apply_right, hdet p, inv_inv]

/-- **The dual-bank equality is derived, not certified**: det-one forces the contragredient
coefficient bank to coincide with the primal bank, by swap-symmetry of the Euler
coefficients. -/
theorem cpsPolynomialDualCoeff_eq_primal_of_detOne
    (pi : PolynomialSatakeDualPair (Fin 2))
    (hdet : ∀ p, pi.primal p 1 = (pi.primal p 0)⁻¹) (j : ℕ) :
    cpsPolynomialDualCoeff pi j = cpsPolynomialPrimalCoeff pi j := by
  unfold CriticalLinePhasor.GlobalHelix.cpsPolynomialDualCoeff
    CriticalLinePhasor.GlobalHelix.cpsPolynomialPrimalCoeff
  have h : pi.dual = fun p => pi.primal p ∘ Equiv.swap (0 : Fin 2) 1 :=
    funext fun p => dual_eq_primal_comp_swap pi hdet p
  rw [h]
  exact radialGlobalSatakeCoeff_comp_equiv (Equiv.swap 0 1) pi.primal j

/-- **The det-one certificate**: the standard-rung Euler certificate built from Hecke
multiplicativity and the det-one Satake normalization alone.  `dual_eq` is derived by
`cpsPolynomialDualCoeff_eq_primal_of_detOne`; the sole remaining arithmetic field is
`coeff_eq` — the cited classical identification-layer input. -/
noncomputable def StandardRungEulerData.ofDetOne
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (form : CuspForm 𝒮ℒ (2 * n : ℤ)) (n_pos : 0 < n)
    (coeff_eq : ∀ j : ℕ,
      (UpperHalfPlane.qExpansion 1 ⇑form).coeff (j + 1) =
        2 * cpsPolynomialPrimalCoeff pi j * ((j + 1 : ℕ) : ℂ) ^ standardShift n)
    (det_one : ∀ p, pi.primal p 1 = (pi.primal p 0)⁻¹) :
    StandardRungEulerData n pi :=
  ⟨form, n_pos, coeff_eq, cpsPolynomialDualCoeff_eq_primal_of_detOne pi det_one⟩

/-! ## The standard-completion identification

The constructed pair's completed transform is the literal standard conductor/Gamma completion
— Mathlib's `Complex.Gammaℂ` at the Deligne shift `n − ½`, conductor one — not the Mellin of a
synthesized kernel.  This closes, at the inhabited rung, the demand that the coupled bank carry
the exact standard completion: the strong pair, the prescribed Γ-clock bank, and the classical
completed Hecke series are one object on the initial half-plane. -/

/-- The standard rung's prescribed completion clock: conductor one, the single Deligne shift
`n − ½` — the literal standard archimedean datum of a weight-`2n` level-one form. -/
noncomputable def standardClock (n : ℕ) : CPSCompletionClock where
  conductor := 1
  conductor_pos := one_pos
  shifts := [standardShift n]
  shifts_nonempty := by simp

/-- **The pair's Λ is the literal standard completed readout**: on the initial half-plane the
completed Mellin transform of the constructed strong pair equals
`1^s · Γ_ℂ(s + (n−½)) · D(s)` — Mathlib's standard `Complex.Gammaℂ` factor at the standard
shift, with the bank's Dirichlet series.  No synthesized kernel occurs: the bank's clock is the
prescribed Γ-clock, and this theorem is the general prescribed-completion identification
instantiated at the inhabited rung. -/
theorem standardRung_Lambda_eq_standardCompletion
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi)
    (point : CPSCompletionPoint pi (standardClock n)) :
    data.toReflectedThetaSource.pair.Λ point.s =
      cpsPolynomialFullPrimalCompletedReadout pi 1 [standardShift n] point.s :=
  (cpsPolynomialFullCompletion3D_identification pi (standardClock n) point).1

/-- The dual completed transform is the same standard completion: det-one self-duality of the
coefficient bank, through the derived `dual_eq`. -/
theorem standardRung_dualLambda_eq_standardCompletion
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi)
    (point : CPSCompletionPoint pi (standardClock n)) :
    data.toReflectedThetaSource.pair.symm.Λ point.s =
      cpsPolynomialFullPrimalCompletedReadout pi 1 [standardShift n] point.s := by
  have h2 := (cpsPolynomialFullCompletion3D_identification pi (standardClock n) point).2
  have hcoeff : CriticalLinePhasor.CarrierTheta.dirichlet
      (cpsPolynomialDualCoeff pi) point.s =
      CriticalLinePhasor.CarrierTheta.dirichlet (cpsPolynomialPrimalCoeff pi) point.s := by
    unfold CriticalLinePhasor.CarrierTheta.dirichlet
    exact tsum_congr fun m => by rw [data.dual_eq m]
  calc data.toReflectedThetaSource.pair.symm.Λ point.s
      = cpsPolynomialFullDualCompletedReadout pi 1 [standardShift n] point.s := h2
    _ = cpsPolynomialFullPrimalCompletedReadout pi 1 [standardShift n] point.s := by
        unfold cpsPolynomialFullDualCompletedReadout cpsPolynomialFullPrimalCompletedReadout
        rw [hcoeff]

/-- **The standard completed Hecke series, explicitly.**  Under the Euler certificate the
pair's Λ is one half of `Γ_ℂ(s + (n−½)) · ∑ a_f(m)·m^{−(s+(n−½))}` — the classical completed
L-series of the actual form, in the shifted variable, read off the same object. -/
theorem standardRung_Lambda_eq_heckeCompletion
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi)
    (point : CPSCompletionPoint pi (standardClock n)) :
    data.toReflectedThetaSource.pair.Λ point.s =
      (1 / 2 : ℂ) * Complex.Gammaℂ (point.s + standardShift n) *
        ∑' m : ℕ, (UpperHalfPlane.qExpansion 1 ⇑data.form).coeff (m + 1) *
          ((m + 1 : ℕ) : ℂ) ^ (-(point.s + standardShift n)) := by
  rw [standardRung_Lambda_eq_standardCompletion data point]
  unfold cpsPolynomialFullPrimalCompletedReadout CriticalLinePhasor.CarrierTheta.dirichlet
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hterm : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion 1 ⇑data.form).coeff (m + 1) *
          ((m + 1 : ℕ) : ℂ) ^ (-(point.s + standardShift n)) =
        2 * (cpsPolynomialPrimalCoeff pi m * ((m + 1 : ℕ) : ℂ) ^ (-point.s)) := by
    intro m
    have hb : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
    rw [data.coeff_eq m]
    calc 2 * cpsPolynomialPrimalCoeff pi m * ((m + 1 : ℕ) : ℂ) ^ standardShift n *
          ((m + 1 : ℕ) : ℂ) ^ (-(point.s + standardShift n))
        = 2 * (cpsPolynomialPrimalCoeff pi m *
            (((m + 1 : ℕ) : ℂ) ^ standardShift n *
              ((m + 1 : ℕ) : ℂ) ^ (-(point.s + standardShift n)))) := by ring
      _ = 2 * (cpsPolynomialPrimalCoeff pi m *
            ((m + 1 : ℕ) : ℂ) ^ (standardShift n + -(point.s + standardShift n))) := by
          rw [Complex.cpow_add _ _ hb]
      _ = 2 * (cpsPolynomialPrimalCoeff pi m * ((m + 1 : ℕ) : ℂ) ^ (-point.s)) := by
          rw [show standardShift n + -(point.s + standardShift n) = -point.s by ring]
  rw [tsum_congr hterm, tsum_mul_left]
  ring

/-- **Hecke's classical theorem for the form, end-to-end on one object.**  For the actual
level-one cusp form of the certificate, the constructed strong pair is simultaneously:
(i) entire, with entire dual; (ii) the classical completed Hecke series
`½·Γ_ℂ(s+n−½)·∑ a_f(m)·m^{−(s+n−½)}` on the initial half-plane; (iii) the same standard
completion on the contragredient leg (det-one self-duality); and (iv) globally reflected with
weight one and root number `i^{2n}`.  The functional equation of the standard completed
automorphic L-function of the genuine form — conductor, Γ-factor, contragredient, and root
number all the standard ones — not of an auxiliary kernel. -/
theorem standardRung_classicalHeckeTheorem
    {n : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (data : StandardRungEulerData n pi) :
    Differentiable ℂ data.toReflectedThetaSource.pair.Λ ∧
    Differentiable ℂ data.toReflectedThetaSource.pair.symm.Λ ∧
    (∀ point : CPSCompletionPoint pi (standardClock n),
      data.toReflectedThetaSource.pair.Λ point.s =
        (1 / 2 : ℂ) * Complex.Gammaℂ (point.s + standardShift n) *
          ∑' m : ℕ, (UpperHalfPlane.qExpansion 1 ⇑data.form).coeff (m + 1) *
            ((m + 1 : ℕ) : ℂ) ^ (-(point.s + standardShift n))) ∧
    (∀ point : CPSCompletionPoint pi (standardClock n),
      data.toReflectedThetaSource.pair.symm.Λ point.s =
        cpsPolynomialFullPrimalCompletedReadout pi 1 [standardShift n] point.s) ∧
    (∀ s : ℂ, data.toReflectedThetaSource.pair.Λ (1 - s) =
      Complex.I ^ (2 * n) • data.toReflectedThetaSource.pair.symm.Λ s) :=
  ⟨standardRung_completed_entire data,
   data.toReflectedThetaSource.pair.symm.differentiable_Λ,
   fun point => standardRung_Lambda_eq_heckeCompletion data point,
   fun point => standardRung_dualLambda_eq_standardCompletion data point,
   fun s => standardRung_functional_equation data s⟩

end CriticalLinePhasor.GenuineGL2Carrier

#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_classicalHeckeTheorem
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_Lambda_eq_standardCompletion
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_dualLambda_eq_standardCompletion
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_Lambda_eq_heckeCompletion
#print axioms CriticalLinePhasor.GenuineGL2Carrier.radialLocalEulerCoeff_comp_equiv
#print axioms CriticalLinePhasor.GenuineGL2Carrier.radialGlobalSatakeCoeff_comp_equiv
#print axioms CriticalLinePhasor.GenuineGL2Carrier.cpsPolynomialDualCoeff_eq_primal_of_detOne
#print axioms CriticalLinePhasor.GenuineGL2Carrier.StandardRungEulerData.ofDetOne
#print axioms CriticalLinePhasor.GenuineGL2Carrier.theta_standard_eq
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_primalReadout_eq
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_dualTransformedReadout_eq
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_reflection
#print axioms CriticalLinePhasor.GenuineGL2Carrier.StandardRungEulerData.toReflectedThetaSource
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_completed_entire
#print axioms CriticalLinePhasor.GenuineGL2Carrier.standardRung_functional_equation
