import RequestProject.MaassTsumParseval
import RequestProject.MaassCoeffSummable
import RequestProject.MaassIdentification

/-!
# The horizontal energy readout of a Maass wave

The payoff of the Parseval bricks: the strip-side integrand of the Maass Rankin--Selberg method,
evaluated.

`waveForm a K x y = √y · ∑ₙ aₙ·cos(2π(n+1)x)·K((n+1)y)` is a cosine series in `x` whose coefficients
`cₙ = aₙ·K((n+1)y)` do not depend on `x`, so `tsum_cosine_parseval` applies directly once the terms
are reassociated.  The prefactor contributes `‖√y‖² = y`, giving

  `∫₀¹ ‖u(x+iy)‖² dx = (y/2)·∑ₙ |aₙ|²·‖K((n+1)y)‖²`.

This is the Maass analogue of `ParsevalExact.rankin_energy_exact`, and it is what the unfolded
strip integral of `maass_rs_unfolding` integrates against `y^{s-1}`.

The summability hypothesis is exactly what `summable_maass_coeff_kernel` supplies past an explicit
height, itself discharged from `lam_norm_le`.
-/

open Real intervalIntegral MeasureTheory

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.MaassParseval CriticalLinePhasor.MaassIdentification

/-- **The horizontal energy identity.**  The period integral of the squared Maass wave is half the
squared-coefficient sum, scaled by the height. -/
theorem maass_horizontal_energy (M : GenuineMaassCuspForm3D) {y : ℝ} (hy : 0 < y)
    (hsum : Summable fun n : ℕ =>
      ‖M.eigenData.lam (n + 1) * M.radialKernel (((n : ℝ) + 1) * y)‖) :
    (∫ x in (0:ℝ)..1,
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2) =
      y / 2 * ∑' n : ℕ,
        ‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 := by
  set c : ℕ → ℂ := fun n =>
    M.eigenData.lam (n + 1) * M.radialKernel (((n : ℝ) + 1) * y) with hc
  -- rewrite the wave as `√y` times a cosine series in the reassociated coefficients
  have hwave : ∀ x : ℝ,
      maassWaveCoordinates M.eigenData M.radialKernel x y =
        ((Real.sqrt y : ℝ) : ℂ) *
          ∑' n : ℕ, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) := by
    intro x
    rw [maassWaveCoordinates, waveForm]
    congr 1
    refine tsum_congr fun n => ?_
    rw [hc]
    simp only [maassFourierCoefficient]
    ring
  -- the prefactor contributes `y`
  have hsq : ∀ x : ℝ,
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2 =
        y * ‖∑' n : ℕ, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2 := by
    intro x
    rw [hwave x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg y), mul_pow, Real.sq_sqrt (le_of_lt hy)]
  rw [intervalIntegral.integral_congr (g := fun x =>
    y * ‖∑' n : ℕ, c n * ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ)‖ ^ 2)
    (fun x _ => hsq x)]
  rw [intervalIntegral.integral_const_mul, tsum_cosine_parseval hsum]
  -- identify the coefficient norms
  have hcoeff : ∀ n : ℕ, ‖c n‖ ^ 2 =
      ‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 := by
    intro n
    rw [hc, norm_mul, mul_pow]
  rw [tsum_congr hcoeff]
  ring

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.maass_horizontal_energy
