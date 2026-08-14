import RequestProject.MaassRSFactorization

/-!
# The Sym² L-function as a ratio with understood continuation

Solving the Rankin--Selberg factorization for `L(Sym²u, s)`:

  **`L(Sym²u, s) = ζ(2s)·L(‖λ‖², s) / ζ(s)`**   on `Re s > 2(E₀+2)+1`.

Every factor on the right is now understood at the edge.  `L(‖λ‖², s)` continues past `s = 1` with
a **simple pole** whose residue is a positive multiple of the Petersson norm
(`maass_rankinSeries_continuation`, `maassPetersson_pos`); `ζ(s)` has a simple pole at `s = 1` with
residue `1`; and `ζ(2s)` is holomorphic and nonzero there.  So the quotient extends across `s = 1`
and its value is `ζ(2)` times the numerator's residue — nonzero.

That is the edge statement in the form the tower's non-vanishing interface consumes; carrying out
the residue limit is the remaining step, and is pure Mathlib complex analysis with no arithmetic
left in it.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction LSeries Complex
open scoped Real LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.ThreeDConverse

/-- **The Sym² L-series is the Rankin--Selberg ratio.** -/
theorem maass_sym2_eq_ratio (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) (hs2 : 1 < (2 * s).re) :
    LSeries (⇑(maassSym2Bank M)) s =
      riemannZeta (2 * s) * LSeries (⇑(maassRankinSquareNorm M)) s / riemannZeta s := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hs1 : 1 < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  rw [eq_div_iff hζ]
  rw [maass_rankinSelberg_factorization M hs hs2]
  ring

/-- The numerator's zeta factor is nonzero on the half-plane, so the ratio is genuinely determined
by the square-norm series. -/
theorem maass_sym2_ratio_zeta_ne_zero {s : ℂ} (hs2 : 1 < (2 * s).re) :
    riemannZeta (2 * s) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs2

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_sym2_eq_ratio
#print axioms CriticalLinePhasor.Unfolding.maass_sym2_ratio_zeta_ne_zero
