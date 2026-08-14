import RequestProject.MaassRankinLocal

/-!
# The Möbius peel for the Maass coefficients

`(μ ⋆ b)_{p^j} = peeled α_p j`, where `peeled α k = U_k² − U_{k-1}²`.

This is `HeckeMultiplicativityWire.muRankin_prime_pow` with the Maass local data substituted.  The
divisor bookkeeping is form-blind; the only inputs are `maassRankinSquareNorm_prime_pow` and
`maassRankinSquareNorm_one`, both proved in the previous file.

**Provenance.**  Ported by substitution from `muRankin_prime_pow`; the divisor-sum manipulation is
unchanged.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction Complex Finset
open scoped Real ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.ThreeDConverse
open CriticalLinePhasor.Sym2Identification

theorem maass_muRankin_prime_pow (M : GenuineMaassCuspForm3D) (p : Nat.Primes) (j : ℕ) :
    ((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M) (p.1 ^ j) =
      peeled (M.eigenData.satake p) j := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (f := fun d e => (μ : ArithmeticFunction ℂ) d * maassRankinSquareNorm M e),
    Nat.divisors_prime_pow p.2, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ i ∈ Finset.range (j + 1), (p.1 : ℕ) ^ j / p ^ i = p ^ (j - i) := by
    intro i hi
    have hij : i ≤ j := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hij p.2.pos]
  rw [Finset.sum_congr rfl fun i hi => by rw [hdiv i hi]]
  match j with
  | 0 =>
    rw [Finset.sum_range_one]
    simp only [pow_zero, Nat.sub_zero]
    rw [show ((μ : ArithmeticFunction ℂ) 1) = 1 from by simp,
      maassRankinSquareNorm_one M, peeled_zero, one_mul]
  | (j + 1) =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hzero : ∀ i ∈ Finset.range j,
        ((μ : ArithmeticFunction ℂ) (p ^ (i + 1 + 1))) *
          maassRankinSquareNorm M (p ^ (j + 1 - (i + 1 + 1))) = 0 := by
      intro i _
      have hμ0 : ((μ : ArithmeticFunction ℂ) (p ^ (i + 2))) = 0 := by
        rw [show ((μ : ArithmeticFunction ℂ) (p ^ (i + 2)))
            = ((moebius (p ^ (i + 2)) : ℤ) : ℂ) from by simp,
          ArithmeticFunction.moebius_apply_prime_pow p.2 (by omega)]
        simp [show i + 2 ≠ 1 from by omega]
      rw [show i + 1 + 1 = i + 2 from rfl, hμ0, zero_mul]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]
    have hμp : ((μ : ArithmeticFunction ℂ) (p ^ (0 + 1))) = -1 := by
      rw [pow_one,
        show ((μ : ArithmeticFunction ℂ) p) = ((moebius p : ℤ) : ℂ) from by simp,
        ArithmeticFunction.moebius_apply_prime p.2]
      norm_num
    have hμ0 : ((μ : ArithmeticFunction ℂ) (p ^ 0)) = 1 := by
      norm_num
    rw [show j + 1 - 0 = j + 1 from by omega,
      show j + 1 - (0 + 1) = j from by omega,
      hμp, hμ0, one_mul,
      maassRankinSquareNorm_prime_pow M p (j + 1),
      maassRankinSquareNorm_prime_pow M p j, peeled_succ]
    ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_muRankin_prime_pow
