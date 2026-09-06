import RequestProject.RegistrationCalibration

/-!
# What the growing-bank balance is (ledger 620)

Two exact identities that fix the content of Draft A's balance.

* `registrationDefect_eq_resid_sub`: the "complete signed error" `𝓔_L(a,b)` of the calibrated
  registry — remainder integral plus Fejér boundary term minus bank change — is the increment of
  the residual `N − 1 − ϑ/π − Ŝ_{L(t)}(t)` of the warped clock. Every Riesz-formula term cancels
  against `count_identity`; the balance carries exactly the information of the clock residual.
* `balance_is_partition`: the balance `𝓔 − ΔV` (Draft A's combined expression) equals the increment
  of `N_strip − N_event`, the difference of the two multiplicity censuses, with no reference to the
  explicit formula at all. With `offLine_increment_eq_registrationDefect_sub_native` this is the
  partition `N_strip = N_line + N_off` read at two heights.

Consequently the leaf of Draft A, the integrated bound `∫_0^T N_off = o(T)`, is not an averaged
target: `offLineStripZeroCountMult_eq_zero_of_integral_sublinear` (already compiled) shows it is
`N_off ≡ 0` pointwise, and the balance rewrites that as `N_strip ≡ N_event`. The Riesz-formula
terms enter only through `count_identity`, which determines the clock residual from the primes up
to the Fejér boundary term; the off-line part of that boundary term is the whole unknown.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta)

namespace CriticalLinePhasor.ContourArgument

/-- The complete signed defect is the increment of the warped clock's residual. -/
theorem registrationDefect_eq_resid_sub {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    registrationDefect (logScale c) a b
      = resid (registryStrain c) b - resid (registryStrain c) a := by
  have hid := count_identity (logScale_pos hc a) ha hab
  have hband : (bandCountMult a b : ℝ) + stripZeroCountMult a = stripZeroCountMult b := by
    exact_mod_cast bandCountMult_add hab
  have hq : ∀ t, registryStrain c t = rieszStrain (logScale c t) t := fun t => rfl
  unfold registrationDefect resid
  rw [hq, hq]
  have hdiv : (theta b - theta a) / Real.pi = theta b / Real.pi - theta a / Real.pi := by ring
  linarith

/-- **The balance is the partition of the census.** Draft A's combined expression is the
increment of `N_strip − N_event`; the explicit-formula terms cancel identically. -/
theorem balance_is_partition {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    registrationDefect (logScale c) a b
      - (nativeRegistryResidual (logScale c) b - nativeRegistryResidual (logScale c) a)
      = ((stripZeroCountMult b : ℝ) - ResidueJump.zeroEventCountMult b)
        - ((stripZeroCountMult a : ℝ) - ResidueJump.zeroEventCountMult a) := by
  rw [registrationDefect_eq_resid_sub hc ha hab]
  have hq : ∀ t, registryStrain c t = rieszStrain (logScale c t) t := fun t => rfl
  unfold resid nativeRegistryResidual ResidueJump.Smult
  rw [hq, hq]
  ring

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.registrationDefect_eq_resid_sub
#print axioms CriticalLinePhasor.ContourArgument.balance_is_partition
