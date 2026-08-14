import RequestProject.MaassCoeffSummable
import RequestProject.MaassCoeffPolyBound
import RequestProject.MaassIdentification

/-!
# Uniform decay of the Maass wave at the cusp

The `y → ∞` half of the strip-integrability estimate.  `cusp_decay` gives decay for each fixed `x`;
what the integrability argument needs is a bound **uniform in `x`**, which the Fourier--Whittaker
expansion supplies directly once the coefficients and the kernel are both controlled.

Every cosine has modulus at most one, so termwise

  `‖u(x+iy)‖ ≤ √y · ∑ₙ ‖λₙ₊₁‖·‖K((n+1)y)‖ ≤ √y · ∑ₙ (n+1)^{E₀+2}·e^{-2π(n+1)y}`,

and factoring one geometric factor out of the sum leaves `√y·e^{-2πy}` times a constant that is
monotone in the height, hence bounded by its value at the base height.  Both inputs are compiled:
`lam_norm_le` for the coefficients and `radialKernel_norm_le_exp` for the kernel.

This is one of the two ends of the product-side estimate; the `y → 0` end needs boundedness of the
wave on the strip, which is a separate argument from invariance and is not proven here.
-/

open Real Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.MaassIdentification CriticalLinePhasor.GeneralSeed

/-- **Uniform exponential decay of the Maass wave.**  Past an explicit height the wave is bounded by
`√y·e^{-2πy}` times a constant, uniformly in the horizontal coordinate. -/
theorem maassWave_uniform_decay (M : GenuineMaassCuspForm3D) :
    ∃ y₀ B : ℝ, 1 ≤ y₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, y₀ ≤ y →
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ≤
        B * Real.sqrt y * Real.exp (-(2 * Real.pi * y)) := by
  obtain ⟨y₀, hy₀, hdecay⟩ := radialKernel_norm_le_exp M
  set A : ℕ := M.eigenData.E₀ + 2 with hA
  set r₀ : ℝ := Real.exp (-(2 * Real.pi * y₀)) with hr₀
  have hr₀pos : 0 < r₀ := Real.exp_pos _
  have hy₀pos : (0 : ℝ) < y₀ := lt_of_lt_of_le one_pos hy₀
  have hr₀lt : r₀ < 1 := by
    rw [hr₀]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hBsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r₀ ^ n :=
    summable_shifted_pow_mul_geometric hr₀pos hr₀lt A
  set B : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ A * r₀ ^ n with hB
  have hBnonneg : 0 ≤ B := tsum_nonneg fun n => by positivity
  refine ⟨y₀, B, hy₀, hBnonneg, fun x y hy => ?_⟩
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le hy₀pos hy
  set r : ℝ := Real.exp (-(2 * Real.pi * y)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hrle : r ≤ r₀ := by
    rw [hr, hr₀]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  -- termwise bound on the coefficients of the expansion
  have hterm : ∀ n : ℕ,
      ‖maassFourierCoefficient M.eigenData n *
        ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
        M.radialKernel (((n : ℝ) + 1) * y)‖ ≤ ((n : ℝ) + 1) ^ A * r₀ ^ n * r := by
    intro n
    have hge : y₀ ≤ ((n : ℝ) + 1) * y := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      calc y₀ ≤ y := hy
        _ = 1 * y := (one_mul y).symm
        _ ≤ ((n : ℝ) + 1) * y := mul_le_mul_of_nonneg_right hn1 (le_of_lt hypos)
    have hk := hdecay _ hge
    have hlam : ‖M.eigenData.lam (n + 1)‖ ≤ ((n : ℝ) + 1) ^ A := by
      have h := lam_norm_le M.eigenData (n + 1) (by omega)
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rwa [hcast] at h
    have hexp : Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) * y))) = r ^ (n + 1) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcos : |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| ≤ 1 := Real.abs_cos_le_one _
    have hstep : ‖M.eigenData.lam (n + 1)‖ *
        |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| *
        ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ≤
        ((n : ℝ) + 1) ^ A * 1 * r ^ (n + 1) := by
      rw [← hexp] at *
      apply mul_le_mul (mul_le_mul hlam hcos (abs_nonneg _) (by positivity)) hk
        (norm_nonneg _) (by positivity)
    have hmono : r ^ n ≤ r₀ ^ n := pow_le_pow_left₀ (le_of_lt hrpos) hrle n
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ A := by positivity
    refine le_trans hstep ?_
    calc ((n : ℝ) + 1) ^ A * 1 * r ^ (n + 1)
        = (((n : ℝ) + 1) ^ A * r ^ n) * r := by rw [pow_succ]; ring
      _ ≤ (((n : ℝ) + 1) ^ A * r₀ ^ n) * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hnn) hrpos.le
      _ = ((n : ℝ) + 1) ^ A * r₀ ^ n * r := by ring
  -- assemble
  have hsummable : Summable fun n : ℕ =>
      ‖maassFourierCoefficient M.eigenData n *
        ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
        M.radialKernel (((n : ℝ) + 1) * y)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      ((hBsum.mul_right r))
  rw [maassWaveCoordinates, waveForm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg y)]
  calc Real.sqrt y * ‖∑' n : ℕ, maassFourierCoefficient M.eigenData n *
          ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
          M.radialKernel (((n : ℝ) + 1) * y)‖
      ≤ Real.sqrt y * ∑' n : ℕ, ((n : ℝ) + 1) ^ A * r₀ ^ n * r := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg y)
        exact le_trans (norm_tsum_le_tsum_norm hsummable)
          (Summable.tsum_le_tsum hterm hsummable (hBsum.mul_right r))
    _ = B * Real.sqrt y * r := by
        rw [tsum_mul_right, hB]
        ring

/-- **Boundedness transfers from the fundamental domain to all of `ℍ`.**  Every point of the upper
half-plane is `SL(2,ℤ)`-equivalent to a point of `𝒟` (`ModularGroup.exists_smul_mem_fd`), and the
Maass wave is invariant, so a bound on `𝒟` is a bound everywhere — in particular on the strip,
where the `y → 0` end of the integrability estimate needs it.

This reduces the remaining obligation to boundedness on `𝒟`, where `y ≥ √3/2`: past the height of
`maassWave_uniform_decay` the wave is already controlled, so what is left is the compact truncated
region, a continuity fact. -/
theorem maassWave_bounded_of_bounded_on_fd (M : GenuineMaassCuspForm3D) {C : ℝ}
    (hfd : ∀ z ∈ ModularGroup.fd,
      ‖maassWave M.eigenData M.radialKernel z‖ ≤ C) :
    ∀ z : UpperHalfPlane, ‖maassWave M.eigenData M.radialKernel z‖ ≤ C := by
  intro z
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hb := hfd (g • z) hg
  rwa [M.level_one_invariant g z] at hb

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_uniform_decay
#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_bounded_of_bounded_on_fd
