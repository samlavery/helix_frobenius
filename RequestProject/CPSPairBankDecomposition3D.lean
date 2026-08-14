import RequestProject.ClebschGordanWindowSum
import RequestProject.CPSSymmetricPowerRootReality3D

/-!
# The pair bank is the disjoint union of the even symmetric-power banks

Normalization plus the window identity.  The rank-`r` root at `i` is `a ^ (r - 2i)` as a `zpow`
once the base pair is inverse-paired, so the pair bank carries exponent `2(r - i - k)` at `(i,k)`
and the block `Sym^{2j}` carries `2(j - l)` at `l ≤ 2j`.  `ClebschGordanWindowSum` says those two
families of exponents agree as multisets against every test function, so any function of the roots
sums the same way on both sides.

Applied to `F u = -log (1 - z u)` this is the local Euler factorization
`pair factor = ∏_{j=0}^{r} Sym^{2j} factor`, whose `j = 0` term is the zeta factor: the pole of the
diagonal Rankin--Selberg readout is exactly the one zeta contributes.

Scope: this file proves the per-prime finite identity.  The primewise assembly to
`bankEulerLog`/`bankEulerReadout`, and the simple-pole bound it yields, are not in this file.
-/

open Complex

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate CriticalLinePhasor.ClebschGordan

/-- **Root normalization.**  For an inverse-paired base, the rank-`r` symmetric-power root is the
integer power `a ^ (r - 2i)`. -/
theorem arithmeticSymmetricPowerRoot_eq_zpow
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹) (i : Fin (r + 1)) :
    arithmeticSymmetricPowerRoot r pi p i =
      (pi.primal p 0) ^ ((r : ℤ) - 2 * (i : ℕ)) := by
  have hne : pi.primal p 0 ≠ 0 := pi.primal_ne_zero p 0
  have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
  rw [arithmeticSymmetricPowerRoot, hinv, ← zpow_natCast (pi.primal p 0) (r - (i : ℕ)),
    ← zpow_natCast ((pi.primal p 0)⁻¹) (i : ℕ), inv_zpow', ← zpow_add₀ hne]
  congr 1
  push_cast [Nat.cast_sub hi]
  ring

/-- The pair bank exponent at `(i,k)` is `2 (r - i - k)`. -/
theorem pairBank_eq_zpow
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹) (ik : Fin (r + 1) × Fin (r + 1)) :
    pairBank (arithmeticSymmetricPowerRoot r pi) p ik =
      (pi.primal p 0) ^ (2 * ((r : ℤ) - (ik.1 : ℕ) - (ik.2 : ℕ))) := by
  have hne : pi.primal p 0 ≠ 0 := pi.primal_ne_zero p 0
  rw [pairBank, arithmeticSymmetricPowerRoot_eq_zpow r pi p hinv ik.1,
    arithmeticSymmetricPowerRoot_eq_zpow r pi p hinv ik.2, ← zpow_add₀ hne]
  congr 1
  ring

/-- The block `Sym^{2j}` exponent at `l` is `2 (j - l)`. -/
theorem evenBlockRoot_eq_zpow
    (j : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹) (l : Fin (2 * j + 1)) :
    arithmeticSymmetricPowerRoot (2 * j) pi p l =
      (pi.primal p 0) ^ (2 * ((j : ℤ) - (l : ℕ))) := by
  rw [arithmeticSymmetricPowerRoot_eq_zpow (2 * j) pi p hinv l]
  congr 1
  push_cast
  ring

/-- **The pair bank decomposes into the even symmetric-power blocks.**  Any function of the local
roots sums identically over the Rankin--Selberg pair bank and over the disjoint union of the banks
`Sym^0, Sym^2, …, Sym^{2r}`. -/
theorem sum_pairBank_eq_sum_evenBlocks
    (r : ℕ) (pi : GlobalHelix.PolynomialSatakeDualPair (Fin 2)) (p : Nat.Primes)
    (hinv : pi.primal p 1 = (pi.primal p 0)⁻¹) (F : ℂ → ℂ) :
    (∑ ik : Fin (r + 1) × Fin (r + 1),
        F (pairBank (arithmeticSymmetricPowerRoot r pi) p ik)) =
      ∑ j ∈ Finset.range (r + 1), ∑ l : Fin (2 * j + 1),
        F (arithmeticSymmetricPowerRoot (2 * j) pi p l) := by
  have hne : pi.primal p 0 ≠ 0 := pi.primal_ne_zero p 0
  have hwindow := pair_sum_eq_block_sum (M := ℂ) r
    (fun u : ℤ => F ((pi.primal p 0) ^ (2 * u)))
  -- rewrite both sides of the window identity into root form
  have hleft :
      (∑ ik : Fin (r + 1) × Fin (r + 1),
          F (pairBank (arithmeticSymmetricPowerRoot r pi) p ik)) =
        ∑ i ∈ Finset.range (r + 1), ∑ k ∈ Finset.range (r + 1),
          F ((pi.primal p 0) ^ (2 * ((r : ℤ) - i - k))) := by
    have hstep : ∀ ik : Fin (r + 1) × Fin (r + 1),
        F (pairBank (arithmeticSymmetricPowerRoot r pi) p ik) =
          F ((pi.primal p 0) ^ (2 * ((r : ℤ) - (ik.1 : ℕ) - (ik.2 : ℕ)))) := by
      intro ik
      rw [pairBank_eq_zpow r pi p hinv]
    rw [Finset.sum_congr rfl (fun ik (_ : ik ∈ Finset.univ) => hstep ik),
      Fintype.sum_prod_type]
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ∑ k : Fin (r + 1),
      F ((pi.primal p 0) ^ (2 * ((r : ℤ) - n - (k : ℕ))))) (r + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range
      (fun m : ℕ => F ((pi.primal p 0) ^ (2 * ((r : ℤ) - i - m)))) (r + 1)
  have hright :
      (∑ j ∈ Finset.range (r + 1), ∑ l : Fin (2 * j + 1),
          F (arithmeticSymmetricPowerRoot (2 * j) pi p l)) =
        ∑ j ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (2 * j + 1),
          F ((pi.primal p 0) ^ (2 * ((j : ℤ) - l))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstep : ∀ l : Fin (2 * j + 1),
        F (arithmeticSymmetricPowerRoot (2 * j) pi p l) =
          F ((pi.primal p 0) ^ (2 * ((j : ℤ) - (l : ℕ)))) := by
      intro l
      rw [evenBlockRoot_eq_zpow j pi p hinv l]
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    exact Fin.sum_univ_eq_sum_range
      (fun m : ℕ => F ((pi.primal p 0) ^ (2 * ((j : ℤ) - m)))) (2 * j + 1)
  rw [hleft, hright]
  simpa using hwindow

/-- The decomposition for the canonical Maass base at every prime. -/
theorem maass_sum_pairBank_eq_sum_evenBlocks
    (M : GenuineMaassCuspForm3D) (r : ℕ) (p : Nat.Primes) (F : ℂ → ℂ) :
    (∑ ik : Fin (r + 1) × Fin (r + 1),
        F (pairBank (arithmeticSymmetricPowerRoot r (maassCPSBase M)) p ik)) =
      ∑ j ∈ Finset.range (r + 1), ∑ l : Fin (2 * j + 1),
        F (arithmeticSymmetricPowerRoot (2 * j) (maassCPSBase M) p l) :=
  sum_pairBank_eq_sum_evenBlocks r (maassCPSBase M) p
    (maassCPSBase_primal_one_eq_inv M p) F

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.arithmeticSymmetricPowerRoot_eq_zpow
#print axioms CriticalLinePhasor.ThreeDConverse.pairBank_eq_zpow
#print axioms CriticalLinePhasor.ThreeDConverse.sum_pairBank_eq_sum_evenBlocks
#print axioms CriticalLinePhasor.ThreeDConverse.maass_sum_pairBank_eq_sum_evenBlocks
