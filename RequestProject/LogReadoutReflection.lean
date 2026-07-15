import RequestProject.GlobalBankLimit

/-!
# The logarithmic readout transports conjugation to inversion

On the carrier's logarithmic coordinate `z(x) = i log x`, the helix conjugation is exactly the
Riemann--Hecke inversion `x ↦ 1/x`.  This file proves that intertwining and transports the completed
finite-bank exchange law to a theta functional equation.  A self-dual rapid envelope supplies the
weight factor `x^k`.
-/

open Complex

namespace CriticalLinePhasor.StrandExchange

/-- The logarithmic carrier coordinate. -/
noncomputable def logReadout (x : ℝ) : ℂ := Complex.I * Real.log x

/-- Inversion of the positive readout coordinate is conjugation of the carrier coordinate. -/
theorem logReadout_one_div (x : ℝ) :
    logReadout (1 / x) = (starRingEnd ℂ) (logReadout x) := by
  unfold logReadout
  rw [one_div, Real.log_inv]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The carrier function read on the logarithmic coordinate. -/
noncomputable def logTheta (E : ℂ → ℂ) (x : ℝ) : ℂ := E (logReadout x)

/-- The dual logarithmic readout. -/
noncomputable def logThetaDual (E : ℂ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (E (logReadout x))

/-- A conjugation exchange law on the carrier becomes an inversion exchange law on its logarithmic
theta readout. -/
theorem logTheta_one_div
    (E : ℂ → ℂ) (ε : ℂ)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (x : ℝ) :
    logTheta E (1 / x) = (starRingEnd ℂ) ε * logThetaDual E x := by
  unfold logTheta logThetaDual
  rw [logReadout_one_div]
  have h := congrArg (starRingEnd ℂ) (hE (logReadout x))
  simpa only [map_mul, starRingEnd_self_apply] using h

/-- A rapid envelope symmetric under logarithmic inversion. -/
noncomputable def selfDualEnvelope (k x : ℝ) : ℝ :=
  x ^ (-k / 2) * Real.exp (-x - x⁻¹)

/-- The self-dual envelope contributes exactly the Riemann--Hecke factor `x^k`. -/
theorem selfDualEnvelope_one_div (k : ℝ) {x : ℝ} (hx : 0 < x) :
    selfDualEnvelope k (1 / x) = x ^ k * selfDualEnvelope k x := by
  have hpow : x⁻¹ ^ (-k / 2) = x ^ k * x ^ (-k / 2) := by
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  have hexp : Real.exp (-x⁻¹ - x) = Real.exp (-x - x⁻¹) := by
    congr 1
    ring
  unfold selfDualEnvelope
  rw [one_div, inv_inv, hpow, hexp]
  ring

/-- The rapidly completed logarithmic theta. -/
noncomputable def completedLogTheta (E : ℂ → ℂ) (k : ℝ) (x : ℝ) : ℂ :=
  (selfDualEnvelope k x : ℂ) * logTheta E x

/-- The dual rapidly completed logarithmic theta. -/
noncomputable def completedLogThetaDual (E : ℂ → ℂ) (k : ℝ) (x : ℝ) : ℂ :=
  (selfDualEnvelope k x : ℂ) * logThetaDual E x

/-- The carrier exchange becomes the precise weighted theta reflection required by `WeakFEPair`. -/
theorem completedLogTheta_one_div
    (E : ℂ → ℂ) (ε : ℂ)
    (hE : ∀ z, (starRingEnd ℂ) (E ((starRingEnd ℂ) z)) = ε * E z)
    (k : ℝ) {x : ℝ} (hx : 0 < x) :
    completedLogTheta E k (1 / x) =
      ((starRingEnd ℂ) ε * (x ^ k : ℝ)) • completedLogThetaDual E k x := by
  unfold completedLogTheta completedLogThetaDual
  rw [selfDualEnvelope_one_div k hx, logTheta_one_div E ε hE x]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- The rapidly completed logarithmic theta is continuous on the positive half-line whenever the
carrier function is continuous. -/
theorem completedLogTheta_continuousOn (E : ℂ → ℂ) (hE : Continuous E) (k : ℝ) :
    ContinuousOn (completedLogTheta E k) (Set.Ioi 0) := by
  intro x hx
  unfold completedLogTheta selfDualEnvelope logTheta logReadout
  have hpow : ContinuousAt (fun y : ℝ => y ^ (-k / 2)) x :=
    Real.continuousAt_rpow_const x _ (Or.inl hx.ne')
  have hinv : ContinuousAt (fun y : ℝ => y⁻¹) x := continuousAt_inv₀ hx.ne'
  have hexp : ContinuousAt (fun y : ℝ => Real.exp (-y - y⁻¹)) x :=
    Real.continuous_exp.continuousAt.comp (continuousAt_id.neg.sub hinv)
  have henv : ContinuousAt (fun y : ℝ => y ^ (-k / 2) * Real.exp (-y - y⁻¹)) x :=
    hpow.mul hexp
  have hlog : ContinuousAt (fun y : ℝ => Complex.I * (Real.log y : ℂ)) x :=
    continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx.ne'))
  exact ((Complex.continuous_ofReal.continuousAt.comp henv).mul
    (hE.continuousAt.comp hlog)).continuousWithinAt

/-- The dual rapidly completed logarithmic theta is continuous on the positive half-line. -/
theorem completedLogThetaDual_continuousOn (E : ℂ → ℂ) (hE : Continuous E) (k : ℝ) :
    ContinuousOn (completedLogThetaDual E k) (Set.Ioi 0) := by
  intro x hx
  unfold completedLogThetaDual selfDualEnvelope logThetaDual logReadout
  have hpow : ContinuousAt (fun y : ℝ => y ^ (-k / 2)) x :=
    Real.continuousAt_rpow_const x _ (Or.inl hx.ne')
  have hinv : ContinuousAt (fun y : ℝ => y⁻¹) x := continuousAt_inv₀ hx.ne'
  have hexp : ContinuousAt (fun y : ℝ => Real.exp (-y - y⁻¹)) x :=
    Real.continuous_exp.continuousAt.comp (continuousAt_id.neg.sub hinv)
  have henv : ContinuousAt (fun y : ℝ => y ^ (-k / 2) * Real.exp (-y - y⁻¹)) x :=
    hpow.mul hexp
  have hlog : ContinuousAt (fun y : ℝ => Complex.I * (Real.log y : ℂ)) x :=
    continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx.ne'))
  exact ((Complex.continuous_ofReal.continuousAt.comp henv).mul
    (Complex.continuous_conj.continuousAt.comp
      (hE.continuousAt.comp hlog))).continuousWithinAt

/-- The finite completed carrier stage satisfies the weighted theta reflection after logarithmic
readout. -/
theorem completedBankStage_logTheta_one_div
    (α : ℕ → ℂ) (hα : ∀ i, ‖α i‖ = 1) (ℓ : ℕ → ℝ)
    (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ k : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    completedLogTheta (completedBankStage α ℓ β ℓ₀ n) k (1 / x) =
      ((starRingEnd ℂ) (completedBankStageExchangeConstant α β n) * (x ^ k : ℝ)) •
        completedLogThetaDual (completedBankStage α ℓ β ℓ₀ n) k x := by
  exact completedLogTheta_one_div _ _
    (completedBankStage_exchange α hα ℓ β hβ ℓ₀ n) k hx

end CriticalLinePhasor.StrandExchange

#print axioms CriticalLinePhasor.StrandExchange.logReadout_one_div
#print axioms CriticalLinePhasor.StrandExchange.logTheta_one_div
#print axioms CriticalLinePhasor.StrandExchange.selfDualEnvelope_one_div
#print axioms CriticalLinePhasor.StrandExchange.completedLogTheta_one_div
#print axioms CriticalLinePhasor.StrandExchange.completedLogTheta_continuousOn
#print axioms CriticalLinePhasor.StrandExchange.completedLogThetaDual_continuousOn
#print axioms CriticalLinePhasor.StrandExchange.completedBankStage_logTheta_one_div
