import RequestProject.MaassSeriesLSeries

/-!
# The residue identity at the edge

The continuation multiplied through by `(σ − 1)`, in the form where the limit at `σ = 1` is read
off with no analysis:

  **`(σ−1)·F(σ)·L(σ) = (σ−1)·E(σ) − ((σ−1)/σ)·P + P`**

with `F` the completed archimedean-times-zeta factor, `L` the square-norm `L`-series, `E` the entire
part, and `P` the Petersson norm.

The whole content is that `−(σ−1)·(1/(1−σ)) = 1` exactly — the second pole's contribution is
*constant*, not merely bounded.  So as `σ → 1` the first two terms vanish for trivial reasons
(a factor `(σ−1)` against a continuous function) and what survives is `P`, which is positive.

That isolates the remaining step to a limit of two manifestly vanishing terms, with the arithmetic
already extracted.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup ArithmeticFunction
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse CriticalLinePhasor.EpsteinTheta

/-- **The residue identity.**  The `s = 1` pole's contribution is the constant `P`. -/
theorem maass_residue_identity (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    ((σ : ℂ) - 1) *
        ((((Real.pi : ℝ) : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ)) *
          (riemannZeta (2 * (σ : ℂ)) *
            (LSeries (⇑(maassRankinSquareNorm M)) (σ : ℂ) *
              archimedeanFactor M (σ : ℂ)))) =
      ((σ : ℂ) - 1) *
          (∫ z in ModularGroup.fd,
            ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ (σ : ℂ)
            ∂(volume : Measure ℍ))
        - (((σ : ℂ) - 1) / (σ : ℂ)) * ((maassPetersson M : ℝ) : ℂ)
        + ((maassPetersson M : ℝ) : ℂ) := by
  have hE : (0:ℝ) ≤ 2 * (M.eigenData.E₀ + 2) := by positivity
  have hσ1 : 1 < σ := by linarith
  have hσ0 : (σ : ℂ) ≠ 0 := by
    simpa using (by linarith : (0:ℝ) < σ).ne'
  have hσne : (1 : ℂ) - (σ : ℂ) ≠ 0 := by
    intro h
    have : (σ : ℂ) = 1 := by linear_combination -h
    have hre : σ = 1 := by exact_mod_cast this
    linarith
  rw [maass_LSeries_continuation M hσ]
  field_simp
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_residue_identity
