import RequestProject.MaassMellinSubstitution
import RequestProject.MaassCoeffPolyBound

/-!
# The Rankin--Selberg Dirichlet series of a Maass form

The object the Mellin substitution produced, established as a genuine convergent Dirichlet series.

`mellin_maass_term` shows the `n`-th Fourier mode contributes `|λₙ|²·(n+1)^{-s}` times a fixed
archimedean factor, so the arithmetic content is the series `∑ₙ |λₙ|²(n+1)^{-s}`.  This file proves
it converges in a half-plane, using the unconditional eigenvalue bound `lam_norm_le`: squaring gives
`|λₙ|² ≤ (n+1)^{2(E₀+2)}`, and a Dirichlet series with polynomially bounded coefficients converges
past the corresponding abscissa.

Its coefficients are **nonnegative** by construction — they are squared norms — which is what makes
the pole of this series at the edge meaningful: it is a Rankin--Selberg square, not a general
Dirichlet series.

Scope: convergence and nonnegativity are proven here.  The continuation, and the identification of
the pole with the Petersson norm, are not.
-/

open Real Filter

namespace CriticalLinePhasor.ThreeDConverse

/-- The Rankin--Selberg Dirichlet coefficients: squared eigenvalue norms, hence nonnegative. -/
noncomputable def rankinCoeff (M : GenuineMaassCuspForm3D) (n : ℕ) : ℝ :=
  ‖M.eigenData.lam (n + 1)‖ ^ 2

theorem rankinCoeff_nonneg (M : GenuineMaassCuspForm3D) (n : ℕ) :
    0 ≤ rankinCoeff M n := by
  unfold rankinCoeff
  positivity

/-- The squared eigenvalue norms are polynomially bounded, with exponent twice that of
`lam_norm_le`. -/
theorem rankinCoeff_le (M : GenuineMaassCuspForm3D) (n : ℕ) :
    rankinCoeff M n ≤ ((n : ℝ) + 1) ^ (2 * (M.eigenData.E₀ + 2)) := by
  have hb := CriticalLinePhasor.GeneralSeed.lam_norm_le M.eigenData (n + 1) (by omega)
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hb
  have hnn : (0 : ℝ) ≤ ‖M.eigenData.lam (n + 1)‖ := norm_nonneg _
  unfold rankinCoeff
  calc ‖M.eigenData.lam (n + 1)‖ ^ 2
      ≤ (((n : ℝ) + 1) ^ (M.eigenData.E₀ + 2)) ^ 2 := by
        apply pow_le_pow_left₀ hnn hb
    _ = ((n : ℝ) + 1) ^ (2 * (M.eigenData.E₀ + 2)) := by
        rw [← pow_mul]
        congr 1
        ring

/-- **The Rankin--Selberg series converges in a half-plane.**  Polynomially bounded nonnegative
coefficients converge past the abscissa set by the eigenvalue exponent. -/
theorem summable_rankinSeries (M : GenuineMaassCuspForm3D) {σ : ℝ}
    (hσ : (2 * (M.eigenData.E₀ + 2) : ℝ) + 1 < σ) :
    Summable fun n : ℕ => rankinCoeff M n * ((n : ℝ) + 1) ^ (-σ) := by
  set A : ℝ := ((2 * (M.eigenData.E₀ + 2) : ℕ) : ℝ) with hA
  have hmaj : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (A - σ) := by
    have hshift : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(σ - A)) := by
      have hp : 1 < σ - A := by
        rw [hA]
        push_cast
        linarith
      have hbase := Real.summable_nat_rpow_inv.mpr hp
      refine (hbase.comp_injective (add_left_injective 1)).congr fun n => ?_
      simp only [Function.comp_apply]
      rw [Real.rpow_neg (by positivity)]
      push_cast
      ring
    refine hshift.congr fun n => ?_
    congr 1
    ring
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (rankinCoeff_nonneg M n) (Real.rpow_nonneg (by positivity) _))
    (fun n => ?_) hmaj
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle := rankinCoeff_le M n
  have hcast : (((n : ℝ) + 1) ^ (2 * (M.eigenData.E₀ + 2))) = ((n : ℝ) + 1) ^ A := by
    rw [hA, ← Real.rpow_natCast ((n : ℝ) + 1) (2 * (M.eigenData.E₀ + 2))]
  rw [hcast] at hle
  calc rankinCoeff M n * ((n : ℝ) + 1) ^ (-σ)
      ≤ ((n : ℝ) + 1) ^ A * ((n : ℝ) + 1) ^ (-σ) := by
        apply mul_le_mul_of_nonneg_right hle (by positivity)
    _ = ((n : ℝ) + 1) ^ (A - σ) := by
        rw [← Real.rpow_add hpos, sub_eq_add_neg]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.rankinCoeff_le
#print axioms CriticalLinePhasor.ThreeDConverse.summable_rankinSeries
