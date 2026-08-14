import RequestProject.ChebyshevCosSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss

/-!
# Exact finite quadrature for Sato--Tate moments

Mathlib's Gauss--Chebyshev rule is **first kind**: equal weights `π/n` at the nodes
`x_i = cos((2i+1)π/(2n))`, exact against the arcsine density `1/√(1−x²)`.  The Sato--Tate density
is `√(1−x²)`, so the two differ by the factor `(1−x²)` — and that factor can simply be absorbed
into the polynomial:

  **`∫_0^π P(cos θ)·sin²θ dθ = sumZeroes n (P·(1 − X²))`   whenever `deg(P·(1−X²)) < 2n`.**

This is exact, finite, and needs no equidistribution theory.  It is the analytic core of a
synthetic Sato--Tate witness: everything downstream of it is rounding arithmetic, because the only
obstruction to an *equal-weight* rule is that the node weights `1 − x_i² = sin²θ_i` are not equal
(that is Bernstein's obstruction, and it is a statement about weights, not about the integral).

The corollary is the exact cancellation block: for `1 ≤ r` and `r + 2 < 2n`,

  **`∑_{i<n} U_r(x_i)·(1 − x_i²) = 0`,**

a finite identity with no error term, valid at every rank the rule resolves.

**Scope.**  This is quadrature for the target measure.  It says nothing about any arithmetic
family, and it does not by itself produce an equal-weight witness.
-/

open Polynomial Polynomial.Chebyshev

namespace CriticalLinePhasor.ThreeDConverse

/-- **Sato--Tate quadrature.**  The `sin²` density is absorbed into the polynomial, after which
Mathlib's first-kind Gauss--Chebyshev rule is exact. -/
theorem satoTate_quadrature {n : ℕ} (hn : n ≠ 0) {P : ℝ[X]}
    (hP : (P * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ)) :
    (∫ θ in (0:ℝ)..Real.pi, P.eval (Real.cos θ) * Real.sin θ ^ 2)
      = sumZeroes n (P * (1 - X ^ 2)) := by
  rw [← integral_eq_sumZeroes hn hP, integral_measureT_eq_integral_cos]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [hsin]

/-- **The exact cancellation block.**  At every rank the rule resolves, the `sin²`-weighted node
sum of the Chebyshev character vanishes identically — no error term. -/
theorem chebyshevU_nodeSum_eq_zero {n r : ℕ} (hn : n ≠ 0) (hr : 1 ≤ r)
    (hdeg : ((U ℝ (r : ℤ)) * (1 - X ^ 2)).degree < 2 * (n : WithBot ℕ)) :
    ∑ i ∈ Finset.range n,
      (U ℝ (r : ℤ)).eval (Real.cos ((2 * (i : ℝ) + 1) / (2 * n) * Real.pi))
        * (1 - Real.cos ((2 * (i : ℝ) + 1) / (2 * n) * Real.pi) ^ 2) = 0 := by
  have hq := satoTate_quadrature hn hdeg
  rw [satoTate_moment_vanishes r hr] at hq
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpin : Real.pi / (n : ℝ) ≠ 0 := div_ne_zero Real.pi_ne_zero hn0
  rw [sumZeroes] at hq
  have hzero : ∑ i ∈ Finset.range n,
      ((U ℝ (r : ℤ)) * (1 - X ^ 2)).eval
        (Real.cos ((2 * (i : ℝ) + 1) / (2 * n) * Real.pi)) = 0 := by
    rcases mul_eq_zero.mp hq.symm with h | h
    · exact absurd h hpin
    · exact h
  rw [← hzero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_quadrature
#print axioms CriticalLinePhasor.ThreeDConverse.chebyshevU_nodeSum_eq_zero
