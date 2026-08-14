import RequestProject.MaassSeriesContinuation
import RequestProject.HeckeMultiplicativityWire

/-!
# The Sym² wire for a Maass form

The Euler factorization the edge argument needs.  `HeckeMultiplicativityWire.sym2_euler_identity`
is stated for holomorphic cusp forms, but its proof is **generic**: the only form-dependent input is
the `L`-series summability of the coefficient sequence.  Everything else — `sqIndicator`,
`LSeries_sqIndicator` (`= ζ(2s)`), `LSeries_convolution'` — is Dirichlet-convolution bookkeeping.

So the identity

  `ζ(2s)·L(μ ⋆ b, s) = L(sqIndicator ⋆ (μ ⋆ b), s)`

holds for the Maass coefficient sequence `b_n = ‖λ_n‖²` as soon as that sequence is `L`-summable,
which `summable_rankinSeries` gives on `Re s > 2(E₀+2)+1`.

Note what is *not* used: no Hecke input at all.  The docstring of the original says as much — the
arithmetic content lives in `sym2Bank_prime_pow`, identifying local factors with Sym²-Satake
traces, which is a separate statement.  This file is the free half.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction LSeries Complex
open scoped Real LSeries.notation ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.Sym2Wire CriticalLinePhasor.ThreeDConverse

/-- The Maass Rankin square-norm coefficient sequence `n ↦ ‖λ_n‖²`. -/
noncomputable def maassRankinSquareNorm (M : GenuineMaassCuspForm3D) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n => ((‖M.eigenData.lam n‖ ^ 2 : ℝ) : ℂ)

/-- The Maass Sym² bank. -/
noncomputable def maassSym2Bank (M : GenuineMaassCuspForm3D) : ArithmeticFunction ℂ :=
  sqIndicator * ((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)

/-- **The Maass square-norm series is `L`-summable** beyond the polynomial abscissa. -/
theorem maassRankinSquareNorm_LSeriesSummable (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    LSeriesSummable (⇑(maassRankinSquareNorm M)) s := by
  refine Summable.of_norm ?_
  rw [← summable_nat_add_iff 1]
  refine (summable_rankinSeries M hs).congr fun n => ?_
  have hn : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  have hpos : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [LSeries.norm_term_eq]
  simp only [hn, if_false]
  rw [maassRankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, hn, if_false]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), rankinCoeff]
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, Real.rpow_neg (by positivity : (0:ℝ) ≤ (n : ℝ) + 1), div_eq_mul_inv]

/-- **The Sym² Euler identity for a Maass form.**  Pure Dirichlet convolution — no Hecke input. -/
theorem maass_sym2_euler_identity (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) (hs2 : 1 < (2 * s).re) :
    riemannZeta (2 * s) *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s =
      LSeries (⇑(maassSym2Bank M)) s := by
  have hμs : LSeriesSummable (⇑(μ : ArithmeticFunction ℂ)) s := by
    have hcoe : (⇑(μ : ArithmeticFunction ℂ) : ℕ → ℂ) = ↗μ := by
      funext n
      simp
    rw [hcoe]
    refine LSeriesSummable_moebius_iff.mpr ?_
    have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
    linarith
  have hb : LSeriesSummable (⇑(maassRankinSquareNorm M)) s :=
    maassRankinSquareNorm_LSeriesSummable M hs
  have hμb : LSeriesSummable (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s := by
    rw [← ArithmeticFunction.coe_mul]
    exact hμs.convolution hb
  have hsq : LSeriesSummable (⇑sqIndicator) s := sqIndicator_LSeriesSummable hs2
  calc riemannZeta (2 * s) *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s
      = LSeries (⇑sqIndicator) s *
          LSeries (⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s := by
        rw [LSeries_sqIndicator hs2]
    _ = LSeries ((⇑sqIndicator) ⍟
          ⇑((μ : ArithmeticFunction ℂ) * maassRankinSquareNorm M)) s :=
        (LSeries_convolution' hsq hμb).symm
    _ = LSeries (⇑(maassSym2Bank M)) s := by
        rw [maassSym2Bank, ArithmeticFunction.coe_mul]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassRankinSquareNorm_LSeriesSummable
#print axioms CriticalLinePhasor.Unfolding.maass_sym2_euler_identity
