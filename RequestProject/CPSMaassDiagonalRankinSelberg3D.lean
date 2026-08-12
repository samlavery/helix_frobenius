import RequestProject.CPSMaassCoefficientSurfaceReality3D
import RequestProject.RSLocalCauchy

/-!
# The genuine diagonal Rankin--Selberg Satake tensor

The coefficientwise square surface is useful for elementary positivity but is not the conventional
diagonal Rankin--Selberg Euler product.  This file constructs the latter with the literal channels
`alpha_i alpha_j^{-1}` and proves its logarithmic prime-power coefficient is a squared norm.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate
open CriticalLinePhasor.SatoTateCarrier3D

/-- The literal diagonal tensor `W tensor W^vee`, with channels `alpha_i alpha_j^{-1}`. -/
noncomputable def diagonalRankinSelbergSatakePair
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) :
    PolynomialSatakeDualPair (ι × ι) where
  primal := fun p ij => W.primal p ij.1 * W.dual p ij.2
  dual := fun p ij => W.dual p ij.1 * W.primal p ij.2
  primalExponent := W.primalExponent + W.dualExponent
  dualExponent := W.dualExponent + W.primalExponent
  primal_ne_zero := by
    intro p ij
    exact mul_ne_zero (W.primal_ne_zero p ij.1) (by
      rw [W.dual_eq_inv]
      exact inv_ne_zero (W.primal_ne_zero p ij.2))
  dual_eq_inv := by
    intro p ij
    rw [W.dual_eq_inv, W.dual_eq_inv, mul_inv_rev, inv_inv]
    ring
  primal_bound := by
    intro p ij
    rw [norm_mul, pow_add]
    exact mul_le_mul (W.primal_bound p ij.1) (W.dual_bound p ij.2)
      (norm_nonneg _) (by positivity)
  dual_bound := by
    intro p ij
    rw [norm_mul, pow_add]
    exact mul_le_mul (W.dual_bound p ij.1) (W.primal_bound p ij.2)
      (norm_nonneg _) (by positivity)

/-- The diagonal tensor power sum factors as the primal trace times the dual trace. -/
theorem diagonalRankinSelberg_powerSum_eq_mul
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (p : Nat.Primes) (k : ℕ) :
    (∑ ij : ι × ι, (diagonalRankinSelbergSatakePair W).primal p ij ^ k) =
      (∑ i : ι, W.primal p i ^ k) * (∑ j : ι, W.dual p j ^ k) := by
  rw [Fintype.sum_prod_type]
  simp_rw [diagonalRankinSelbergSatakePair, mul_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- On the unit circle the diagonal tensor power sum is the real squared norm of the standard
power-sum trace. -/
theorem diagonalRankinSelberg_powerSum_eq_normSq_of_unit
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (hunit : ∀ p i, ‖W.primal p i‖ = 1) (p : Nat.Primes) (k : ℕ) :
    (∑ ij : ι × ι, (diagonalRankinSelbergSatakePair W).primal p ij ^ k) =
      (Complex.normSq (∑ i : ι, W.primal p i ^ k) : ℝ) := by
  rw [diagonalRankinSelberg_powerSum_eq_mul]
  have hdual : (∑ j : ι, W.dual p j ^ k) =
      (starRingEnd ℂ) (∑ i : ι, W.primal p i ^ k) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, W.dual_eq_inv, Complex.inv_eq_conj (hunit p i)]
  rw [hdual, mul_comm, ← Complex.normSq_eq_conj_mul_self]

/-- Every logarithmic prime-power trace of a unitary diagonal Rankin--Selberg tensor is a
nonnegative real. -/
theorem diagonalRankinSelberg_powerSum_nonneg
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι)
    (hunit : ∀ p i, ‖W.primal p i‖ = 1) (p : Nat.Primes) (k : ℕ) :
    0 ≤ ((∑ ij : ι × ι,
      (diagonalRankinSelbergSatakePair W).primal p ij ^ k)).re := by
  rw [diagonalRankinSelberg_powerSum_eq_normSq_of_unit W hunit]
  exact Complex.normSq_nonneg _

/-- The conventional diagonal Satake tensor at the rank-`r` Maass symmetric power. -/
noncomputable def maassStandardDiagonalRankinSelbergPair
    (M : GenuineMaassCuspForm3D) (r : ℕ) :
    PolynomialSatakeDualPair (Fin (r + 1) × Fin (r + 1)) :=
  diagonalRankinSelbergSatakePair
    (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r)

/-- The genuine Maass tower makes every diagonal logarithmic prime-power coefficient
nonnegative. -/
theorem maassStandardDiagonalRankinSelberg_powerSum_nonneg
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r : ℕ) (p : Nat.Primes) (k : ℕ) :
    0 ≤ ((∑ ij : Fin (r + 1) × Fin (r + 1),
      (maassStandardDiagonalRankinSelbergPair M r).primal p ij ^ k)).re := by
  apply diagonalRankinSelberg_powerSum_nonneg
  intro q i
  have ha := maass_temperedness M.eigenData hC q
  simp [symrSatakePairOf, symClockWeight, ha]

/-- The clock parametrization of a Maass Satake root is exactly the arithmetic symmetric-power
root used by the retained completed source. -/
theorem symClockWeight_maass_eq_arithmeticSymmetricPowerRoot
    (M : GenuineMaassCuspForm3D) (r : ℕ) (p : Nat.Primes) (i : Fin (r + 1)) :
    symClockWeight r ((SatakeSeed.ofMaass M.eigenData).satake p) i =
      arithmeticSymmetricPowerRoot r (maassCPSBase M) p i := by
  simp only [arithmeticSymmetricPowerRoot, maassCPSBase_primal_zero,
    maassCPSBase_primal_one, symClockWeight]
  rw [← zpow_natCast, ← zpow_natCast, inv_zpow',
    ← zpow_add₀ ((SatakeSeed.ofMaass M.eigenData).satake_ne_zero p)]
  congr 1
  have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
  push_cast [Nat.cast_sub hi]
  ring

/-- A retained arithmetic symmetric-power prime-power trace is the standard Satake trace. -/
theorem sum_arithmeticSymmetricPowerRoot_pow_eq_trace
    (M : GenuineMaassCuspForm3D) (r : ℕ) (p : Nat.Primes) (k : ℕ) :
    (∑ i : Fin (r + 1), arithmeticSymmetricPowerRoot r (maassCPSBase M) p i ^ k) =
      symmetricPowerSatakeTrace
        ((SatakeSeed.ofMaass M.eigenData).satake p ^ k) r := by
  unfold symmetricPowerSatakeTrace
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [arithmeticSymmetricPowerRoot, maassCPSBase_primal_zero,
    maassCPSBase_primal_one, mul_pow, inv_pow]
  rw [← pow_mul, ← pow_mul, pow_mul', pow_mul']

/-- The diagonal Rankin--Selberg logarithmic coefficient is the Clebsch--Gordan sum of the
standard even symmetric-power logarithmic coefficients. -/
theorem maassStandardDiagonalRankinSelberg_powerSum_eq_evenSymmetricPowers
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData)
    (r : ℕ) (p : Nat.Primes) (k : ℕ) :
    (∑ ij : Fin (r + 1) × Fin (r + 1),
      (maassStandardDiagonalRankinSelbergPair M r).primal p ij ^ k) =
      ∑ j ∈ Finset.range (r + 1),
        ∑ i : Fin (2 * j + 1),
          arithmeticSymmetricPowerRoot (2 * j) (maassCPSBase M) p i ^ k := by
  let α := (SatakeSeed.ofMaass M.eigenData).satake p
  have hα : ‖α‖ = 1 := maass_temperedness M.eigenData hC p
  have hαk : ‖α ^ k‖ = 1 := by simp [hα]
  have hαkne : α ^ k ≠ 0 :=
    pow_ne_zero k ((SatakeSeed.ofMaass M.eigenData).satake_ne_zero p)
  rw [show maassStandardDiagonalRankinSelbergPair M r =
      diagonalRankinSelbergSatakePair
        (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r) from rfl]
  rw [diagonalRankinSelberg_powerSum_eq_normSq_of_unit]
  · rw [show (∑ i : Fin (r + 1),
        (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r).primal p i ^ k) =
        symmetricPowerSatakeTrace (α ^ k) r from by
      rw [← sum_arithmeticSymmetricPowerRoot_pow_eq_trace M r p k]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (symrSatakePairOf (SatakeSeed.ofMaass M.eigenData) r).primal p i =
          symClockWeight r ((SatakeSeed.ofMaass M.eigenData).satake p) i from rfl,
        symClockWeight_maass_eq_arithmeticSymmetricPowerRoot]]
    rw [Complex.normSq_eq_conj_mul_self,
      CriticalLinePhasor.RSPositivity.trace_conj_of_unit hαk r]
    rw [← sq]
    rw [CriticalLinePhasor.RSLocalCauchy.trace_sq_expand hαkne r]
    apply Finset.sum_congr rfl
    intro j _
    rw [sum_arithmeticSymmetricPowerRoot_pow_eq_trace]
  · intro q i
    have hq := maass_temperedness M.eigenData hC q
    simp [symrSatakePairOf, symClockWeight, hq]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.diagonalRankinSelbergSatakePair
#print axioms CriticalLinePhasor.ThreeDConverse.diagonalRankinSelberg_powerSum_eq_normSq_of_unit
#print axioms CriticalLinePhasor.ThreeDConverse.diagonalRankinSelberg_powerSum_nonneg
#print axioms CriticalLinePhasor.ThreeDConverse.maassStandardDiagonalRankinSelberg_powerSum_nonneg
#print axioms CriticalLinePhasor.ThreeDConverse.symClockWeight_maass_eq_arithmeticSymmetricPowerRoot
#print axioms CriticalLinePhasor.ThreeDConverse.sum_arithmeticSymmetricPowerRoot_pow_eq_trace
#print axioms CriticalLinePhasor.ThreeDConverse.maassStandardDiagonalRankinSelberg_powerSum_eq_evenSymmetricPowers
