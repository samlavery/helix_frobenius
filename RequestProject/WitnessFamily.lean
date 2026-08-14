import RequestProject.WitnessSequence
import RequestProject.CPSCharacterSatoTate3D
import RequestProject.MajorantDensity

/-!
# The witness as a Satake family

`witness_cancellation` is a statement about a sequence of angles.  The corpus's Sato--Tate
machinery consumes an `ArithmeticSatakePrimeFamily` — a unit-modulus tower value at each prime.
This file packages the one into the other.

The bridge is `Nat.count`, the inverse of `Nat.nth`: the `i`-th prime gets the angle
`witnessAngle i`, realised as the tower value `e^{iθ}`.  Since `witnessAngle` lands in `[0, π]`,
its argument is recovered exactly, so the family's `angle` at the `i`-th prime is `witnessAngle i`
on the nose.

**Scope.**  This is a synthetic family — the angles are constructed, not arithmetic.  It exhibits a
family on which the corpus's Sato--Tate conclusion fires; it says nothing about any `L`-function.
-/

open Filter Complex
open scoped Real Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.SatoTateCarrier3D

/-- The index of a prime in the enumeration `nthPrime`. -/
noncomputable def primeIndex (p : Nat.Primes) : ℕ := Nat.count Nat.Prime p.1

@[simp] theorem primeIndex_nthPrime (i : ℕ) : primeIndex (nthPrime i) = i := by
  rw [primeIndex, nthPrime]
  exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime i

/-- The tower at a prime: the unit-modulus value `e^{iθ}` with `θ` the witness angle. -/
noncomputable def witnessTower (p : Nat.Primes) :
    CriticalLinePhasor.GlobalHelix.ArithmeticSatakeTowerAtPrime where
  value := Complex.exp ((witnessAngle (primeIndex p) : ℝ) * Complex.I)
  value_ne_zero := Complex.exp_ne_zero _
  topSatake := fun r => (Complex.exp ((witnessAngle (primeIndex p) : ℝ) * Complex.I)) ^ r
  bottomSatake := fun r =>
    ((Complex.exp ((witnessAngle (primeIndex p) : ℝ) * Complex.I))⁻¹) ^ r
  topSatake_eq := fun _ => rfl
  bottomSatake_eq := fun _ => rfl
  bound := 1
  topSatake_bound := by
    intro r _
    rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
  bottomSatake_bound := by
    intro r _
    rw [norm_pow, norm_inv, Complex.norm_exp_ofReal_mul_I, inv_one, one_pow]

/-- **The witness family.** -/
noncomputable def witnessFamily : ArithmeticSatakePrimeFamily := ⟨witnessTower⟩

/-- **The family's angle at the `i`-th prime is the witness angle.** -/
theorem witnessFamily_angle (i : ℕ) :
    witnessFamily.angle (nthPrime i) = witnessAngle i := by
  have hval : (witnessFamily.tower (nthPrime i)).value
      = Complex.exp ((witnessAngle (primeIndex (nthPrime i)) : ℝ) * Complex.I) := rfl
  rw [ArithmeticSatakePrimeFamily.angle, hval, primeIndex_nthPrime]
  have hmem : witnessAngle i ∈ Set.Ioc (-Real.pi) Real.pi := by
    obtain ⟨h1, h2⟩ := witnessAngle_mem i
    exact ⟨by linarith [Real.pi_pos], h2⟩
  rw [Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hmem]
  exact abs_of_nonneg (witnessAngle_nonneg i)


/-! ## The machinery fires

Rewriting the corpus's prime average through the character identity turns it into the sequence
average that `witness_cancellation` controls. -/

/-- **The witness family satisfies the per-rank cancellation.** -/
theorem witnessFamily_cancellation :
    ArithmeticSymmetricPowerPrimeCancellation witnessFamily where
  tendsto_zero := by
    intro r hr
    refine (witness_cancellation r hr).congr fun n => ?_
    rw [CriticalLinePhasor.PartialSerre.arithmeticAverage_eq_chebyshev]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval
        (Real.cos (witnessFamily.angle (nthPrime i)))) (n + 1)]
    have hcongr : ∑ i ∈ Finset.range (n + 1),
        (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval
          (Real.cos (witnessFamily.angle (nthPrime i)))
        = ∑ i ∈ Finset.range (n + 1),
          (Polynomial.Chebyshev.U ℝ (r : ℤ)).eval (Real.cos (witnessAngle i)) :=
      Finset.sum_congr rfl fun i _ => by rw [witnessFamily_angle i]
    rw [hcongr]
    push_cast
    ring

/-- **The corpus's Sato--Tate machinery has a firing instance.**  Compare
`maass_satoTate_no_firing_instance`: the cancellation field, which had no inhabitant anywhere in
the corpus, has one. -/
theorem satoTate_cancellation_inhabited :
    Nonempty (ArithmeticSymmetricPowerPrimeCancellation witnessFamily) :=
  ⟨witnessFamily_cancellation⟩


/-- **★ The machinery fires end to end.**  The witness family's Satake angles equidistribute to the
Sato--Tate carrier measure — unconditionally, with no hypotheses.

This is the positive control the corpus lacked.  `maass_satoTate_no_firing_instance` showed that
`ArithmeticSymmetricPowerPrimeCancellation` had no inhabitant anywhere: its only construction ran
through `GenuineMaassCuspForm3D`, which is empty.  Here is an inhabitant, and with it the full
Sato--Tate conclusion on an explicit family.

**What this is not.**  The family is *synthetic*: its angles are built from Gauss--Chebyshev nodes,
not read off any `L`-function.  It shows the reduction is sound and its conclusion attainable; it
says nothing about whether any arithmetic family satisfies the hypothesis. -/
theorem witnessFamily_equidistributes :
    Tendsto (empiricalPrimeCarrierMeasure witnessFamily.angle) atTop
      (nhds carrierProbability) :=
  empiricalPrimeCarrierMeasure_tendsto_of_arithmeticSatakeCancellation witnessFamily
    witnessFamily_cancellation


/-! ## Closing the remaining "no inhabitant" gaps

The structure audit found several Sato--Tate input bundles with no inhabitant anywhere in the
corpus, for the same reason as the cancellation field: their only supply ran through the empty
`GenuineMaassCuspForm3D`.  The witness supplies them all, through the corpus's own converters. -/

/-- `SymmetricPowerCharacterPrimeZeroInput` is inhabited. -/
noncomputable def witnessCharacterZeroInput : SymmetricPowerCharacterPrimeZeroInput :=
  witnessFamily_cancellation.toCharacterPrimeZeroInput

/-- `SymmetricPowerCharacterPrimeAverageInput` is inhabited. -/
noncomputable def witnessCharacterAverageInput : SymmetricPowerCharacterPrimeAverageInput :=
  witnessCharacterZeroInput.toCharacterAverageInput

theorem witnessCharacterZeroInput_angle :
    witnessCharacterZeroInput.angle = witnessFamily.angle := rfl

/-- All three input bundles are inhabited. -/
theorem satoTate_inputs_inhabited :
    Nonempty SymmetricPowerCharacterPrimeZeroInput
      ∧ Nonempty SymmetricPowerCharacterPrimeAverageInput
      ∧ Nonempty (ArithmeticSymmetricPowerPrimeCancellation witnessFamily) :=
  ⟨⟨witnessCharacterZeroInput⟩, ⟨witnessCharacterAverageInput⟩, ⟨witnessFamily_cancellation⟩⟩

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.witnessFamily_angle
#print axioms CriticalLinePhasor.ThreeDConverse.witnessFamily_cancellation
#print axioms CriticalLinePhasor.ThreeDConverse.witnessFamily_equidistributes
#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_inputs_inhabited
