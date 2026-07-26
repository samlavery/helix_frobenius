import RequestProject.HeckeCancellation
import RequestProject.CPSArithmeticStrongSource3D

/-!
# Genuine GL(2) modular carrier seed

This file constructs the helix exchange from the modular inversion law of an actual level-one cusp
form.  The exchange is therefore not a field of the arithmetic coupling.  The coupling records only
the two literal arithmetic-bank readouts to which that independently constructed modular carrier is
identified.
-/

open Complex UpperHalfPlane MatrixGroups

namespace CriticalLinePhasor.GenuineGL2Carrier

open CriticalLinePhasor.HeckeCancellation
open CriticalLinePhasor.GlobalHelix

/-- The balanced vertical carrier of an actual even-weight level-one modular form. -/
noncomputable def evenWeightVerticalCarrier
    (n : ℕ) {F : Type*} [FunLike F ℍ ℂ] (f : F) (z : ℂ) : ℂ :=
  ((Real.exp z.im : ℝ) : ℂ) ^ n *
    f (vert (Real.exp z.im) (Real.exp_pos z.im))

/-- Modular inversion gives the global helix exchange of the balanced vertical carrier. -/
theorem evenWeightVerticalCarrier_exchange
    (n : ℕ) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F 𝒮ℒ (2 * n : ℤ)]
    (f : F) (z : ℂ) :
    evenWeightVerticalCarrier n f ((starRingEnd ℂ) z) =
      Complex.I ^ (2 * n) * evenWeightVerticalCarrier n f z := by
  let x : ℝ := Real.exp z.im
  have hx : 0 < x := Real.exp_pos _
  simp only [evenWeightVerticalCarrier, conj_im, Real.exp_neg]
  change ((x⁻¹ : ℝ) : ℂ) ^ n * f (vert x⁻¹ (inv_pos.mpr hx)) =
    Complex.I ^ (2 * n) * (((x : ℂ) ^ n) * f (vert x hx))
  rw [hecke_inversion f x hx]
  push_cast
  rw [show ((2 * n : ℤ)) = (2 * n : ℕ) by norm_num, zpow_natCast]
  rw [mul_pow, Nat.mul_comm 2 n]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : (x : ℂ) ^ (n * 2) * (x : ℂ)⁻¹ ^ n = (x : ℂ) ^ n := by
    rw [pow_mul, inv_pow]
    field_simp [hxc]
  rw [show (x : ℂ)⁻¹ ^ n *
      ((x : ℂ) ^ (n * 2) * Complex.I ^ (n * 2) * f (vert x hx)) =
      ((x : ℂ) ^ (n * 2) * (x : ℂ)⁻¹ ^ n) *
        Complex.I ^ (n * 2) * f (vert x hx) by ring, hpow]
  ring

/-!
The carrier used by a completed theta readout must divide out the completion envelope before the
readout multiplies it back in.  Otherwise the purported modular value is changed by an additional
factor `selfDualEnvelope`.  The next carrier performs that normalization exactly.
-/

/-- A genuine modular vertical carrier with the completion envelope removed.  At logarithmic
height `I * log x`, completing this carrier restores exactly `f (i x)`. -/
noncomputable def deEnvelopedVerticalCarrier
    (n : ℕ) {F : Type*} [FunLike F ℍ ℂ] (f : F) (z : ℂ) : ℂ :=
  f (vert (Real.exp z.im) (Real.exp_pos z.im)) /
    (CriticalLinePhasor.StrandExchange.selfDualEnvelope
      ((2 * n : ℕ) : ℝ) (Real.exp z.im) : ℂ)

private theorem selfDualEnvelope_pos_ne_zero (k x : ℝ) (hx : 0 < x) :
    CriticalLinePhasor.StrandExchange.selfDualEnvelope k x ≠ 0 := by
  unfold CriticalLinePhasor.StrandExchange.selfDualEnvelope
  exact mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (Real.exp_ne_zero _)

/-- Exact readout normalization: the completed logarithmic readout of the de-enveloped carrier is
the genuine modular vertical value, with no residual radial factor. -/
theorem completedLogTheta_deEnvelopedVerticalCarrier
    (n : ℕ) {F : Type*} [FunLike F ℍ ℂ]
    (f : F) (x : ℝ) (hx : 0 < x) :
    CriticalLinePhasor.StrandExchange.completedLogTheta
        (deEnvelopedVerticalCarrier n f) ((2 * n : ℕ) : ℝ) x =
      f (vert x hx) := by
  simp only [CriticalLinePhasor.StrandExchange.completedLogTheta,
    CriticalLinePhasor.StrandExchange.logTheta,
    CriticalLinePhasor.StrandExchange.logReadout,
    deEnvelopedVerticalCarrier, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]
  simp only [Real.exp_log hx]
  have henvR := selfDualEnvelope_pos_ne_zero ((2 * n : ℕ) : ℝ) x hx
  have henvC :
      (CriticalLinePhasor.StrandExchange.selfDualEnvelope ((2 * n : ℕ) : ℝ) x : ℂ) ≠ 0 :=
    by exact_mod_cast henvR
  field_simp [henvC]

/-- Modular inversion also gives a constant global helix exchange after de-enveloping: the
`x^(2n)` modular factor cancels the envelope's `x^(2n)` reflection factor. -/
theorem deEnvelopedVerticalCarrier_exchange
    (n : ℕ) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F 𝒮ℒ (2 * n : ℤ)]
    (f : F) (z : ℂ) :
    deEnvelopedVerticalCarrier n f ((starRingEnd ℂ) z) =
      Complex.I ^ (2 * n) * deEnvelopedVerticalCarrier n f z := by
  let x : ℝ := Real.exp z.im
  have hx : 0 < x := Real.exp_pos _
  simp only [deEnvelopedVerticalCarrier, conj_im, Real.exp_neg]
  change
    f (vert x⁻¹ (inv_pos.mpr hx)) /
        (CriticalLinePhasor.StrandExchange.selfDualEnvelope
          ((2 * n : ℕ) : ℝ) x⁻¹ : ℂ) =
      Complex.I ^ (2 * n) *
        (f (vert x hx) /
          (CriticalLinePhasor.StrandExchange.selfDualEnvelope
            ((2 * n : ℕ) : ℝ) x : ℂ))
  rw [hecke_inversion f x hx]
  have henv :
      CriticalLinePhasor.StrandExchange.selfDualEnvelope ((2 * n : ℕ) : ℝ) x⁻¹ =
        x ^ (((2 * n : ℕ) : ℝ)) *
          CriticalLinePhasor.StrandExchange.selfDualEnvelope ((2 * n : ℕ) : ℝ) x := by
    simpa only [one_div] using
      (CriticalLinePhasor.StrandExchange.selfDualEnvelope_one_div
        ((2 * n : ℕ) : ℝ) hx)
  rw [henv]
  push_cast
  rw [show ((2 * n : ℤ)) = (2 * n : ℕ) by norm_num, zpow_natCast]
  have hcast : (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have henvR := selfDualEnvelope_pos_ne_zero ((2 * n : ℕ) : ℝ) x hx
  have henvC :
      (CriticalLinePhasor.StrandExchange.selfDualEnvelope ((2 * n : ℕ) : ℝ) x : ℂ) ≠ 0 :=
    by exact_mod_cast henvR
  field_simp [hxc, henvC]
  push_cast
  ring

/-- **Retired shape — uninhabitable on genuine data; use
`GlobalHelix.BankThetaProfileCoupling3D` (`CPSBankThetaProfileCoupling3D.lean`) instead.**
The readout fields below demand that the twisted bank readout — whose `(r+1)·m ≥ 2`-clock tensor
completion kernel has Bessel-type decay `e^{-c√x}` — equal the raw vertical value of a cusp form,
which decays like `e^{-2πx}`; and the bank's leading coefficient is `1`, so the zero form fails
too.  No instance can exist at any `(r, m)`.  The corrected obligation types the identification
against a theta profile pair; the genuine standard-rung instance is
`StandardRungEulerData.toProfileCoupling` (`CPSGenuineGL2StandardRung3D.lean`).  The modular
exchange remains deliberately absent here: `toCarrierSeed` derives it from the slash law. -/
structure ArithmeticBankCoupling3D
    (n r m : ℕ) (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin m))
    (D : ArithmeticCPSCompletionData r m) where
  form : CuspForm 𝒮ℒ (2 * n : ℤ)
  n_pos : 0 < n
  primal_readout : ∀ (x : ℝ) (hx : 0 < x),
    cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts x =
      form (vert x hx)
  dual_readout : ∀ (x : ℝ) (hx : 0 < x),
    cpsPolynomialFullDual3DTransformedReadout
        (arithmeticCPSPolynomialTwist r m pi tau) D.conductor D.tensorShifts (1 / x) =
      form (vert x hx)

/-- Direct genuine-GL(2)-to-carrier-seed construction.  **Retired with its input type
(`ArithmeticBankCoupling3D`, uninhabitable — see its docstring); the corrected route is
`BankThetaProfileCoupling3D.toCarrierSeed`.**  Its exchange law is the theorem
`deEnvelopedVerticalCarrier_exchange`, while the two source equalities are the literal arithmetic
bank identifications carried by `ArithmeticBankCoupling3D`.  The completion weight is forced to be
the modular weight `2n`; it is not a freely supplied coupling parameter. -/
noncomputable def ArithmeticBankCoupling3D.toCarrierSeed
    {n r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    {tau : PolynomialSatakeDualPair (Fin m)} {D : ArithmeticCPSCompletionData r m}
    (G : ArithmeticBankCoupling3D n r m pi tau D) :
    ArithmeticCPSCarrierSeed3D r m pi tau D where
  primalCarrier := deEnvelopedVerticalCarrier n G.form
  dualCarrier := deEnvelopedVerticalCarrier n G.form
  exchangeConstant := Complex.I ^ (2 * n)
  exchangeConstant_ne_zero := pow_ne_zero _ Complex.I_ne_zero
  carrier_exchange := deEnvelopedVerticalCarrier_exchange n G.form
  weight := ((2 * n : ℕ) : ℝ)
  weight_pos := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) G.n_pos
  primal_carrier := fun x hx =>
    (G.primal_readout x hx).trans
      (completedLogTheta_deEnvelopedVerticalCarrier n G.form x hx).symm
  dual_carrier := fun x hx =>
    (G.dual_readout x hx).trans
      (completedLogTheta_deEnvelopedVerticalCarrier n G.form x hx).symm

/-- Convert a genuine even-weight GL(2) coupling at every CPS twist into the exact carrier-seed
family consumed by the all-twist converse constructor.  **Retired with its input type; the
corrected family bridge is `GlobalHelix.allProfileCarrierSeeds`.** -/
noncomputable def allCarrierSeeds
    {r : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
    (coupling : ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
      (D : ArithmeticCPSCompletionData r m) →
        Σ n : ℕ, ArithmeticBankCoupling3D n r m pi tau D) :
    ∀ (m : ℕ), 1 ≤ m → m < r →
      (tau : PolynomialSatakeDualPair (Fin m)) →
      (D : ArithmeticCPSCompletionData r m) →
        ArithmeticCPSCarrierSeed3D r m pi tau D :=
  fun m hm hmr tau D => (coupling m hm hmr tau D).2.toCarrierSeed

end CriticalLinePhasor.GenuineGL2Carrier

#print axioms CriticalLinePhasor.GenuineGL2Carrier.evenWeightVerticalCarrier_exchange
#print axioms CriticalLinePhasor.GenuineGL2Carrier.completedLogTheta_deEnvelopedVerticalCarrier
#print axioms CriticalLinePhasor.GenuineGL2Carrier.deEnvelopedVerticalCarrier_exchange
#print axioms CriticalLinePhasor.GenuineGL2Carrier.ArithmeticBankCoupling3D.toCarrierSeed
#print axioms CriticalLinePhasor.GenuineGL2Carrier.allCarrierSeeds
