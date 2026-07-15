import RequestProject.GlobalHelixTwistedSymmetricPowerFEPair

/-!
# Fixed-completion target signature audit

The all-place fixed-completion reflection cannot be quantified over an arbitrary finite twist type,
arbitrary placewise fiber family, arbitrary exchange constant, and arbitrary reflection weight.  The
empty twist fiber is a legal input to that signature.  Its global Satake coefficient bank is the
unit coefficient at height one and zero elsewhere, so the fixed theta is just the completion kernel.
For the nonzero fixed clock `[0]`, reciprocal heights `2` and `1/2` give distinct readouts.

This file records the counterexample in Lean so later global-reflection declarations must use a
signature that actually encodes the intended global cuspidal data and its completion parameters.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

/-- The unique finite-weight fiber on the empty channel type. -/
noncomputable def emptyWeightFiber : FiniteWeightFiber Empty where
  weight := Empty.elim
  dual := id
  dual_invol := fun i => nomatch i
  unit := fun i => nomatch i
  balanced := fun i => nomatch i
  center_trivial := fun i => nomatch i

/-- An empty local Euler fiber has coefficient one in degree zero and zero above it. -/
theorem localEulerCoeff_empty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (W : FiniteWeightFiber ι) (n : ℕ) :
    localEulerCoeff W n = if n = 0 then 1 else 0 := by
  rw [localEulerCoeff_eq_finsuppAntidiag]
  cases n <;> simp

noncomputable def onePrimePhase : Nat.Primes → ℂ := fun _ => 1

theorem onePrimePhase_norm (p : Nat.Primes) : ‖onePrimePhase p‖ = 1 := by
  simp [onePrimePhase]

noncomputable def emptyTwist : Nat.Primes → FiniteWeightFiber Empty :=
  fun _ => emptyWeightFiber

/-- For the empty twist type, the all-place coefficient bank is exactly `δ₁`. -/
theorem emptySatakeCoeff (n : ℕ) :
    twistedSymmetricPowerSatakeCoeff 0 onePrimePhase onePrimePhase_norm emptyTwist n =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [twistedSymmetricPowerSatakeCoeff_zero]
  · have hn1 : 1 < n + 1 := by omega
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn1
    unfold twistedSymmetricPowerSatakeCoeff
    rw [if_neg hn]
    apply Finset.prod_eq_zero (s := Finset.univ) (i := ⟨p, hp⟩) (Finset.mem_univ _)
    rw [localEulerCoeff_empty]
    have hfac : (n + 1).factorization p ≠ 0 :=
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (by omega) (Nat.dvd_of_mem_primeFactors hp)).ne'
    simp [hfac]

/-- Projection of the empty-fiber 3D bank reads only its fixed kernel. -/
theorem emptySatakeTheta (g : ℝ → ℂ) (x : ℝ) :
    CarrierTheta.theta
      (twistedSymmetricPowerSatakeCoeff 0 onePrimePhase onePrimePhase_norm emptyTwist)
      g x = g x := by
  unfold CarrierTheta.theta
  rw [tsum_eq_single 0]
  · norm_num [emptySatakeCoeff]
  · intro n hn
    simp [emptySatakeCoeff, hn]

/-- The prescribed nonzero fixed clock distinguishes heights `2` and `1/2`. -/
theorem completionKernel_zero_two_ne_half :
    completionKernel [0] 2 ≠ completionKernel [0] (1 / 2) := by
  rw [completionKernel_singleton]
  unfold gammaClock
  norm_num
  ring_nf
  rw [show -((Real.pi : ℂ) * 4) = (((-4 * Real.pi : ℝ) : ℂ)) by
      push_cast
      ring,
    show -(Real.pi : ℂ) = (((-Real.pi : ℝ) : ℂ)) by push_cast; rfl]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast
  simp

/-- Concrete failure of the unrestricted all-place off-weld vanishing statement. -/
theorem fixedOddChannel_counterexample :
    twistedSymmetricPowerFixedBankOddChannel
      [0] 0 onePrimePhase onePrimePhase_norm emptyTwist 1 0 2 ≠ 0 := by
  unfold twistedSymmetricPowerFixedBankOddChannel fixedBankOddChannel
  rw [fixedPrimalBankReadout_eq_theta [0]
      (twistedSymmetricPowerSatakeCoeff 0 onePrimePhase onePrimePhase_norm emptyTwist)
      (by norm_num : (0 : ℝ) < 2),
    weightedReflectedDualBankReadout,
    fixedTransformedConjugateDualBankReadout_eq_theta_one_div [0]
      (twistedSymmetricPowerSatakeCoeff 0 onePrimePhase onePrimePhase_norm emptyTwist)
      (by norm_num : (0 : ℝ) < 2)]
  norm_num [emptySatakeTheta]
  exact sub_ne_zero.mpr completionKernel_zero_two_ne_half

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.emptySatakeCoeff
#print axioms CriticalLinePhasor.GlobalHelix.emptySatakeTheta
#print axioms CriticalLinePhasor.GlobalHelix.completionKernel_zero_two_ne_half
#print axioms CriticalLinePhasor.GlobalHelix.fixedOddChannel_counterexample
