import RequestProject.MaassSym2Wire

/-!
# The Maass square-norm coefficients are squared Chebyshev clock values

The arithmetic half of the Sym² wire, at prime powers.

The holomorphic version (`rankinSquareNorm_prime_pow`) has to carry a `primeScale` factor because
the weight-`k` normalisation puts `p^{k-1}` into the Hecke recursion.  The Maass recursion has no
such factor — `MaassEigenData.prime_rec` is `λ(p^{j+2}) = λ(p)λ(p^{j+1}) − λ(p^j)` on the nose — so
the identity is the clean one:

  **`b_{p^j} = U_j(α_p)²`.**

Two compiled facts supply it: `MaassEigenData.coeff_prime_pow` (`λ(p^j) = U_j(α_p)`, the Chebyshev
clock) and `conj_eq` (the eigenvalues are real, so `‖λ‖² = λ²`).  The reality is what turns a norm
into a square — without it the coefficient would not even be a polynomial in the Satake parameter.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction Complex
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.ThreeDConverse
open CriticalLinePhasor.Sym2Identification

/-- A real complex number's squared norm is its square. -/
lemma ofReal_norm_sq_of_conj_eq {x : ℂ} (hx : (starRingEnd ℂ) x = x) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = x ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, hx, sq]

/-- **The Maass square-norm coefficient at a prime power is the squared Chebyshev clock value.** -/
theorem maassRankinSquareNorm_prime_pow (M : GenuineMaassCuspForm3D) (p : Nat.Primes) (j : ℕ) :
    maassRankinSquareNorm M (p.1 ^ j) =
      seedCoeff (M.eigenData.satake p) j ^ 2 := by
  have hpj : (p.1 : ℕ) ^ j ≠ 0 := pow_ne_zero _ p.2.pos.ne'
  rw [maassRankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg hpj]
  rw [ofReal_norm_sq_of_conj_eq (M.eigenData.conj_eq (p.1 ^ j)),
    M.eigenData.coeff_prime_pow p j]

/-- The coefficient sequence is normalised at one. -/
theorem maassRankinSquareNorm_one (M : GenuineMaassCuspForm3D) :
    maassRankinSquareNorm M 1 = 1 := by
  rw [maassRankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg one_ne_zero]
  rw [ofReal_norm_sq_of_conj_eq (M.eigenData.conj_eq 1), M.eigenData.one, one_pow]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassRankinSquareNorm_prime_pow
#print axioms CriticalLinePhasor.Unfolding.maassRankinSquareNorm_one
