import RequestProject.MaassSym2Ratio

/-!
# The Rankin--Selberg series is the `L`-series of the square-norm coefficients

A bookkeeping identification that the residue argument needs and that had not been made.

`maass_rankinSeries_continuation` speaks of `∑'_{n:ℕ} rankinSelbergTerm M s n`, indexed from `0`
with the shift `n ↦ n+1` built into the summand.  `maass_rankinSelberg_factorization` speaks of
`LSeries (maassRankinSquareNorm M) s`, indexed from `1` with the `n = 0` term defined to be zero.
They are the same sum; the reindexing is `tsum_eq_zero_add` and the `n = 0` term vanishes on both
sides for the same reason — there is no zeroth Fourier coefficient.

Making this explicit is what lets the pole of the continuation and the factorization's numerator be
recognised as the same object.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open ArithmeticFunction LSeries Complex
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse CriticalLinePhasor.EpsteinTheta
open UpperHalfPlane ModularGroup

/-- **The two spellings of the Rankin--Selberg series agree.** -/
theorem maass_rankinSeries_eq_LSeries (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < s.re) :
    (∑' n : ℕ, rankinSelbergTerm M s n) = LSeries (⇑(maassRankinSquareNorm M)) s := by
  have hsum : Summable (fun n : ℕ => LSeries.term (⇑(maassRankinSquareNorm M)) s n) :=
    maassRankinSquareNorm_LSeriesSummable M hs
  rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  have hn : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
  rw [LSeries.term_of_ne_zero hn, maassRankinSquareNorm, toArithmeticFunction]
  simp only [ArithmeticFunction.coe_mk, if_neg hn]
  rw [rankinSelbergTerm, Complex.cpow_neg, div_eq_mul_inv]
  congr 2
  push_cast
  ring

/-- **The continuation, in `L`-series form.**  This is the statement the residue argument reads
against `maass_sym2_eq_ratio`: the same `LSeries (maassRankinSquareNorm M)` appears in both, so the
pole located here is the pole of the factorization's numerator. -/
theorem maass_LSeries_continuation (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    (((Real.pi : ℝ) : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ)) *
        (riemannZeta (2 * (σ : ℂ)) *
          (LSeries (⇑(maassRankinSquareNorm M)) (σ : ℂ) * archimedeanFactor M (σ : ℂ))) =
      (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ (σ : ℂ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane))
        - (1 / (σ : ℂ) + 1 / (1 - (σ : ℂ))) * ((maassPetersson M : ℝ) : ℂ) := by
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  rw [← maass_rankinSeries_eq_LSeries M (s := (σ : ℂ)) (by rw [hre]; exact hσ)]
  exact maass_rankinSeries_continuation M hσ

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_rankinSeries_eq_LSeries
#print axioms CriticalLinePhasor.Unfolding.maass_LSeries_continuation
