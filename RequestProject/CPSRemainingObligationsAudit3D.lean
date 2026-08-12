import RequestProject.CPSMaassSatoTate3D
import RequestProject.CPSRepresentationInstance3D
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Audit of the remaining Maass CPS endpoint

`MaassEigenData` stores Hecke-style coefficient identities, but no eigenfunction or automorphic
realization.  The divisor function satisfies that interface.  Its chosen Satake parameter is one
at every prime, so its first symmetric-power prime average is constantly two and the cancellation
field required by `CPSAutomorphicPrimeTheorem3D` is false.

This gives a compiled boundary: the automorphic prime theorem cannot be derived from the present
`MaassEigenData` signature alone.  A completed endpoint must consume a type that also identifies
the coefficients with a genuine cuspidal Maass automorphic representation.
-/

open Filter Topology MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate CriticalLinePhasor.SatoTateCarrier3D

/-- The divisor-counting Hecke sequence, regarded as a complex-valued coefficient bank. -/
noncomputable def divisorMaassCoefficient (n : ℕ) : ℂ := n.divisors.card

/-- The divisor-counting sequence satisfies the current `MaassEigenData` interface. -/
noncomputable def divisorMaassEigenData : MaassEigenData where
  lam := divisorMaassCoefficient
  one := by simp [divisorMaassCoefficient]
  coprime_mul := by
    intro m n hmn
    change (((m * n).divisors.card : ℕ) : ℂ) =
      (m.divisors.card : ℂ) * (n.divisors.card : ℂ)
    norm_cast
    exact hmn.card_divisors_mul
  prime_rec := by
    intro p hp j
    have hpcard : p.divisors.card = 2 := by
      rw [hp.divisors]
      exact Finset.card_pair hp.ne_one.symm
    simp [divisorMaassCoefficient, Nat.divisors_prime_pow hp, hpcard]
    ring
  conj_eq := by
    intro n
    simp [divisorMaassCoefficient]
  E₀ := 1
  lam_bound := by
    intro p hp
    have hpcard : p.divisors.card = 2 := by
      rw [hp.divisors]
      exact Finset.card_pair hp.ne_one.symm
    rw [show divisorMaassCoefficient p = 2 by
      simp [divisorMaassCoefficient, hpcard]]
    norm_num
    exact_mod_cast hp.two_le

/-- A nonzero complex number with trace `a + a⁻¹ = 2` is one. -/
private theorem eq_one_of_add_inv_eq_two {a : ℂ} (ha : a ≠ 0) (htrace : a + a⁻¹ = 2) :
    a = 1 := by
  have hsq : (a - 1) * (a - 1) = 0 := by
    calc
      (a - 1) * (a - 1) = a * (a + a⁻¹ - 2) := by
        field_simp [ha]
        ring
      _ = 0 := by rw [htrace]; norm_num
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)

/-- The divisor sequence's chosen Satake parameter is one at every prime. -/
theorem divisorMaassEigenData_satake (p : Nat.Primes) :
    divisorMaassEigenData.satake p = 1 := by
  apply eq_one_of_add_inv_eq_two (divisorMaassEigenData.satake_ne_zero p)
  rw [divisorMaassEigenData.satake_trace]
  have hpcard : p.1.divisors.card = 2 := by
    rw [p.2.divisors]
    exact Finset.card_pair p.2.ne_one.symm
  simp [divisorMaassEigenData, divisorMaassCoefficient, hpcard]

@[simp] theorem divisorMaassSatakeSeed_satake (p : Nat.Primes) :
    (SatakeSeed.ofMaass divisorMaassEigenData).satake p = 1 :=
  divisorMaassEigenData_satake p

/-- The divisor sequence has the constant unit tower ceiling. -/
noncomputable def divisorMaassTowerCeiling : MaassTowerCeiling divisorMaassEigenData where
  C := fun _ => 1
  top := by
    intro p r _
    rw [divisorMaassSatakeSeed_satake, one_pow, norm_one]
  bottom := by
    intro p r _
    rw [divisorMaassSatakeSeed_satake, inv_one, one_pow, norm_one]

/-- Its first symmetric-power prime average is constantly two, independently of the ceiling used
to package the same Satake values. -/
theorem divisorMaass_firstPrimeAverage_ofCeiling
    (hC : MaassTowerCeiling divisorMaassEigenData) (n : ℕ) :
    arithmeticSymmetricPowerPrimeAverage
        (maassSatoTateFamily divisorMaassEigenData hC) 1 n = 2 := by
  unfold arithmeticSymmetricPowerPrimeAverage maassSatoTateFamily maassTower
  simp only [divisorMaassSatakeSeed_satake, symmetricPowerSatakeTrace_one, inv_one,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  norm_num
  field_simp

/-- Consequently no ceiling on this `MaassEigenData` can supply prime cancellation. -/
theorem divisorMaass_no_primeCancellation_ofCeiling
    (hC : MaassTowerCeiling divisorMaassEigenData) :
    ¬ArithmeticSymmetricPowerPrimeCancellation
      (maassSatoTateFamily divisorMaassEigenData hC) := by
  intro h
  have hzero := h.tendsto_zero 1 (by omega)
  have htwo : Tendsto
      (fun n => arithmeticSymmetricPowerPrimeAverage
        (maassSatoTateFamily divisorMaassEigenData hC) 1 n)
      atTop (nhds 2) := by
    simpa only [divisorMaass_firstPrimeAverage_ofCeiling] using tendsto_const_nhds
  have : (2 : ℝ) = 0 := tendsto_nhds_unique htwo hzero
  norm_num at this

/-- The constant-ceiling specialization. -/
theorem divisorMaass_no_primeCancellation :
    ¬ArithmeticSymmetricPowerPrimeCancellation
      (maassSatoTateFamily divisorMaassEigenData divisorMaassTowerCeiling) :=
  divisorMaass_no_primeCancellation_ofCeiling divisorMaassTowerCeiling

/-! ## The scalar adelic representation does not realize its Satake metadata -/

/-- The local representation used by the scalar genuine-adelic constructor acts trivially at
every finite place.  Its separately stored `localSatakeRoot` field therefore cannot serve as the
Satake parameter of this representation without an additional spherical-Hecke compatibility
theorem. -/
theorem scalarGenuineAdelicRestrictedRepresentation3D_local_apply
    (r : ℕ) (pi : PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (g : PadicGL (r + 1) p) (z : ℂ) :
    letI := scalarAdelicAction
      (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
      (fun q ↦ PadicGL (r + 1) q)
      (fun q ↦ Subgroup (PadicGL (r + 1) q))
      (fun q ↦ padicIntegralSubgroup (r + 1) q)
    (scalarGenuineAdelicRestrictedRepresentation3D r pi).localRepresentation p g z = z := by
  letI := scalarAdelicAction
    (Matrix.GeneralLinearGroup (Fin (r + 1)) ℝ)
    (fun q ↦ PadicGL (r + 1) q)
    (fun q ↦ Subgroup (PadicGL (r + 1) q))
    (fun q ↦ padicIntegralSubgroup (r + 1) q)
  rfl

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.divisorMaassEigenData
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicRestrictedRepresentation3D
#print axioms CriticalLinePhasor.ThreeDConverse.zeroReadoutGenuineAdelicBankBridge3D
#print axioms CriticalLinePhasor.ThreeDConverse.divisorMaassEigenData_satake
#print axioms CriticalLinePhasor.ThreeDConverse.divisorMaass_firstPrimeAverage_ofCeiling
#print axioms CriticalLinePhasor.ThreeDConverse.divisorMaass_no_primeCancellation_ofCeiling
#print axioms CriticalLinePhasor.ThreeDConverse.divisorMaass_no_primeCancellation
#print axioms CriticalLinePhasor.ThreeDConverse.scalarGenuineAdelicRestrictedRepresentation3D_local_apply
