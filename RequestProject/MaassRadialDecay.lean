import RequestProject.GenuineMaassCuspForm3D

/-!
# Exponential decay of the Maass radial kernel

The summability input for every `tsum`/integral exchange in the Maass Rankin--Selberg chain.

`GenuineMaassCuspForm3D` pins its radial kernel by the modified Bessel equation together with the
normalization `2√y·e^{2πy}·K(y) → 1` (`radial_normalization`), which is the standard leading
asymptotic of `K_{ir}(2πy)`.  That normalization is exactly enough to extract a clean exponential
bound: past some height the normalized quantity has norm at most `2`, so

  `‖K(y)‖ ≤ e^{-2πy}`  for all large `y`,

with no constant to track (the `√y` in the denominator is `≥ 1` in that range and is simply
discarded).  This is the estimate that, against the polynomial Hecke bound on the coefficients,
makes the Fourier--Whittaker series absolutely convergent and lets the strip integral be evaluated
termwise.

Nothing here uses the Bessel ODE itself — only the normalization — so the bound is available for
any kernel with that asymptotic.
-/

open Filter Topology Real

namespace CriticalLinePhasor.ThreeDConverse

/-- **Exponential decay of the radial kernel.**  Past an explicit height the Maass radial kernel is
bounded by `e^{-2πy}`, directly from its normalization. -/
theorem radialKernel_norm_le_exp (M : GenuineMaassCuspForm3D) :
    ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      ‖M.radialKernel y‖ ≤ Real.exp (-(2 * Real.pi * y)) := by
  have hnorm := M.radial_normalization
  have hev : ∀ᶠ y : ℝ in atTop,
      ‖((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) * M.radialKernel y‖ ≤ 2 := by
    have hlt : ‖(1 : ℂ)‖ < 2 := by rw [norm_one]; norm_num
    have hball := hnorm.norm.eventually (eventually_lt_nhds hlt)
    filter_upwards [hball] with y hy
    exact le_of_lt hy
  obtain ⟨y₁, hy₁⟩ := eventually_atTop.mp hev
  refine ⟨max y₁ 1, le_max_right _ _, fun y hy => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyge : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hyge
  have hb := hy₁ y hy1
  -- unpack the norm of the real scalar multiple
  have hsqrt : (1 : ℝ) ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hyge
  have hexp : (0 : ℝ) < Real.exp (2 * Real.pi * y) := Real.exp_pos _
  have hscal : (0 : ℝ) < 2 * Real.sqrt y * Real.exp (2 * Real.pi * y) := by
    have : (0 : ℝ) < Real.sqrt y := lt_of_lt_of_le one_pos hsqrt
    positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscal] at hb
  -- divide through
  have hstep : ‖M.radialKernel y‖ ≤ 2 / (2 * Real.sqrt y * Real.exp (2 * Real.pi * y)) := by
    rw [le_div_iff₀ hscal]
    linarith [hb]
  refine le_trans hstep ?_
  rw [Real.exp_neg]
  rw [div_le_iff₀ hscal]
  have hinv : (Real.exp (2 * Real.pi * y))⁻¹ * (2 * Real.sqrt y * Real.exp (2 * Real.pi * y)) =
      2 * Real.sqrt y := by
    field_simp
  rw [hinv]
  linarith [hsqrt]

/-- **The radial kernel is eventually nonvanishing.**  The other half of the normalization: past
some height the normalized quantity has norm at least `1/2`, so the kernel cannot vanish there.

This is what makes the archimedean Mellin factor `∫ ‖K‖² t^{s-1} dt` strictly positive at real
exponents — the integrand is nonnegative and not almost everywhere zero. -/
theorem radialKernel_norm_pos (M : GenuineMaassCuspForm3D) :
    ∃ y₁ : ℝ, 1 ≤ y₁ ∧ ∀ y : ℝ, y₁ ≤ y → 0 < ‖M.radialKernel y‖ := by
  have hnorm := M.radial_normalization
  have hgt : ‖(1 : ℂ)‖ > 1 / 2 := by rw [norm_one]; norm_num
  have hev : ∀ᶠ y : ℝ in atTop,
      (1 : ℝ) / 2 < ‖((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) *
        M.radialKernel y‖ :=
    hnorm.norm.eventually (eventually_gt_nhds hgt)
  obtain ⟨y₁, hy₁⟩ := eventually_atTop.mp hev
  refine ⟨max y₁ 1, le_max_right _ _, fun y hy => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hb := hy₁ y hy1
  rw [norm_mul] at hb
  by_contra hcon
  push_neg at hcon
  have hzero : ‖M.radialKernel y‖ = 0 := le_antisymm hcon (norm_nonneg _)
  rw [hzero, mul_zero] at hb
  linarith

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.radialKernel_norm_le_exp
#print axioms CriticalLinePhasor.ThreeDConverse.radialKernel_norm_pos
