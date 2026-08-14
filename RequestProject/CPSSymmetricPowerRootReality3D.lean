import RequestProject.CPSMaassSatoTate3D
import RequestProject.CPSEdgePoleTolerantEngine3D

/-!
# Self-duality of the symmetric-power root bank

The edge argument asks the bank for two things: unit roots and **real power sums**
(`norm_bank_product_ge_one`'s `hreal`).  The first is temperedness.  The second is self-duality,
and for a symmetric power it is a statement about the *index* rather than about the arithmetic:
the rank-`r` root at `j` is `a ^ (r - j) * a⁻¹ ^ j`, and on the unit circle conjugation inverts,
so conjugating the root at `j` returns the root at `Fin.rev j`.  The multiset of roots is
therefore stable under conjugation, every power sum equals its own conjugate, and the imaginary
part vanishes.

Nothing here is an estimate and nothing is arithmetic input: it is the reflection `j ↦ r - j` of
the symmetric-power clock, read on the fiber.  Together with `maass_temperedness` it discharges
both bank hypotheses of the Mertens product bound from the tower ceiling alone.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate

/-- Conjugating a unit-modulus symmetric-power root reflects its index: `j ↦ Fin.rev j`. -/
theorem conj_arithmeticSymmetricPowerRoot
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hunit : ‖pi.primal p 0‖ = 1)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹)
    (j : Fin (r + 1)) :
    (starRingEnd ℂ) (arithmeticSymmetricPowerRoot r pi p j) =
      arithmeticSymmetricPowerRoot r pi p (Fin.rev j) := by
  have hne : pi.primal p 0 ≠ 0 := pi.primal_ne_zero p 0
  have hconj : (starRingEnd ℂ) (pi.primal p 0) = (pi.primal p 0)⁻¹ :=
    (Complex.inv_eq_conj hunit).symm
  have hconjinv : (starRingEnd ℂ) ((pi.primal p 0)⁻¹) = pi.primal p 0 := by
    rw [map_inv₀, hconj, inv_inv]
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.2
  have hrev : ((Fin.rev j : Fin (r + 1)) : ℕ) = r - (j : ℕ) := by
    simp [Fin.val_rev]
  simp only [arithmeticSymmetricPowerRoot, hinv, map_mul, map_pow, hconj, hconjinv, hrev]
  rw [Nat.sub_sub_self hj]
  ring

/-- **Real power sums for the symmetric-power bank.**  Conjugation permutes the roots, so every
power sum is its own conjugate. -/
theorem sum_arithmeticSymmetricPowerRoot_pow_im_eq_zero
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hunit : ‖pi.primal p 0‖ = 1)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹)
    (k : ℕ) :
    (∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r pi p j ^ k).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  calc
    (starRingEnd ℂ) (∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r pi p j ^ k) =
        ∑ j : Fin (r + 1),
          arithmeticSymmetricPowerRoot r pi p (Fin.rev j) ^ k := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [map_pow, conj_arithmeticSymmetricPowerRoot r pi p hunit hinv j]
    _ = ∑ j : Fin (r + 1), arithmeticSymmetricPowerRoot r pi p j ^ k :=
      Fintype.sum_equiv (Fin.revPerm) _ _ fun j => rfl

/-! ## Discharge from the tower ceiling -/

/-- The canonical Maass base is inverse-paired at every prime. -/
theorem maassCPSBase_primal_one_eq_inv (M : GenuineMaassCuspForm3D) (p : Nat.Primes) :
    (maassCPSBase M).primal p 1 = ((maassCPSBase M).primal p 0)⁻¹ := by
  rw [maassCPSBase_primal_zero, maassCPSBase_primal_one]

/-- **Both bank hypotheses of the Mertens product bound follow from the tower ceiling.**  Unit
roots are `maass_temperedness`; real power sums are the index reflection above. -/
theorem maass_symmetricPowerRoot_unit_and_real
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ) :
    (∀ (p : Nat.Primes) (j : Fin (r + 1)),
        ‖arithmeticSymmetricPowerRoot r (maassCPSBase M) p j‖ = 1) ∧
      (∀ (p : Nat.Primes) (k : ℕ),
        (∑ j : Fin (r + 1),
          arithmeticSymmetricPowerRoot r (maassCPSBase M) p j ^ k).im = 0) := by
  refine ⟨norm_arithmeticSymmetricPowerRoot_maass M hC r, fun p k => ?_⟩
  refine sum_arithmeticSymmetricPowerRoot_pow_im_eq_zero r (maassCPSBase M) p ?_
    (maassCPSBase_primal_one_eq_inv M p) k
  rw [maassCPSBase_primal_zero]
  exact maass_temperedness M.eigenData hC p

/-- The Mertens product bound, instantiated on the Maass symmetric-power bank of any rank: the
only inputs are the tower ceiling and the index reflection. -/
theorem maass_norm_bank_product_ge_one
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    {sigma : ℝ} (hsigma : 1 < sigma) (y : ℝ) :
    1 ≤ ‖riemannZeta (sigma : ℂ)‖ ^ 2
      * ‖bankEulerReadout
          (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))) (sigma : ℂ)‖
      * ‖bankEulerReadout
          (arithmeticSymmetricPowerRoot r (maassCPSBase M))
          ((sigma : ℂ) + y * I)‖ ^ 4
      * ‖bankEulerReadout
          (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
          ((sigma : ℂ) + 2 * y * I)‖ :=
  norm_bank_product_ge_one _
    (maass_symmetricPowerRoot_unit_and_real M hC r).1
    (maass_symmetricPowerRoot_unit_and_real M hC r).2 hsigma y

/-- **Edge nonvanishing for the Maass symmetric-power continuation, polar companion allowed.**
Given the tower ceiling, the entire rank-`r` continuation identified with the bank Euler readout
on the readout half-plane, and a companion carrying the diagonal Rankin--Selberg readout with at
worst a simple pole, the continuation has no zero at `1 + iy`. -/
theorem maass_edge_nonvanishing
    (M : GenuineMaassCuspForm3D) (hC : MaassTowerCeiling M.eigenData) (r : ℕ)
    {C D : ℂ → ℂ} (hC' : Differentiable ℂ C)
    (hCeq : Set.EqOn C
      (bankEulerReadout (arithmeticSymmetricPowerRoot r (maassCPSBase M)))
      {s : ℂ | 1 < s.re})
    (hDeq : Set.EqOn D
      (bankEulerReadout (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M))))
      {s : ℂ | 1 < s.re})
    {y K K₂ : ℝ}
    (hDpole : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖D (sigma : ℂ)‖ * (sigma - 1) ≤ K)
    (hDtwist : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      ‖D ((sigma : ℂ) + 2 * y * I)‖ ≤ K₂) :
    C (1 + y * I) ≠ 0 :=
  bank_edge_nonvanishing_of_simplePole _
    (maass_symmetricPowerRoot_unit_and_real M hC r).1
    (maass_symmetricPowerRoot_unit_and_real M hC r).2
    hC' hCeq hDeq hDpole hDtwist

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.conj_arithmeticSymmetricPowerRoot
#print axioms CriticalLinePhasor.ThreeDConverse.sum_arithmeticSymmetricPowerRoot_pow_im_eq_zero
#print axioms CriticalLinePhasor.ThreeDConverse.maass_symmetricPowerRoot_unit_and_real
#print axioms CriticalLinePhasor.ThreeDConverse.maass_norm_bank_product_ge_one
#print axioms CriticalLinePhasor.ThreeDConverse.maass_edge_nonvanishing
