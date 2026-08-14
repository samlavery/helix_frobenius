import RequestProject.MaassWaveDecay
import RequestProject.SupBound

/-!
# The Maass wave is bounded on the whole upper half-plane

The last analytic input of the `r = 2` Rankin--Selberg rung.  `maassWave_uniform_decay` controls
the wave past the height where the Bessel normalization takes over; what the strip-integrability
estimate also needs is control as `y → 0`, and by `maassWave_bounded_of_bounded_on_fd` that reduces
to a bound on the fundamental domain.  This file supplies it, and therefore a global bound.

The one missing ingredient was the *compact* window `[a, y₀]`, where the asymptotic says nothing.
There the kernel is merely continuous — but continuity is exactly what `radial_smooth` gives, and a
continuous function on a compact set is bounded.  Absorbing that bound into the exponential (the
window is compact, so `e^{-2πt}` is bounded below on it) upgrades the decay estimate from "past the
normalization height" to "past *any* positive height, with a constant":

  `∀ a > 0, ∃ C ≥ 1, ∀ t ≥ a, ‖K t‖ ≤ C·e^{-2πt}`.

That single change makes the whole `maassWave_uniform_decay` argument run from `a` instead of `y₀`,
and since `√y·e^{-2πy} ≤ 1` for every `y ≥ 0`, decay above a height *is* boundedness above that
height.  On `𝒟` the height is `√3/2` (`HeckeSupBound.fd_im_ge`), so the wave is bounded there, hence —
by invariance — everywhere.

**Scope.**  This is the `r = 2` rung.  It does not prove Sato--Tate, which needs every rank.
-/

open Real Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.MaassIdentification CriticalLinePhasor.GeneralSeed

/-- **The exponential kernel bound from an arbitrary positive height.**  Below the normalization
height the asymptotic gives nothing, but `radial_smooth` gives continuity and the window is
compact, so the bound survives with a constant. -/
theorem radialKernel_norm_le_exp_of_pos (M : GenuineMaassCuspForm3D) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, a ≤ t →
      ‖M.radialKernel t‖ ≤ C * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨y₀, hy₀, hdecay⟩ := radialKernel_norm_le_exp M
  have hy₀pos : (0 : ℝ) < y₀ := lt_of_lt_of_le one_pos hy₀
  have hcont : ContinuousOn M.radialKernel (Set.Icc a y₀) :=
    ((M.radial_smooth 0).continuousOn).mono (fun t ht => lt_of_lt_of_le ha ht.1)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hE1 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * y₀) := by
    apply Real.one_le_exp
    positivity
  have hmax : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
  have hCbig : (1 : ℝ) ≤ max C₀ 1 * Real.exp (2 * Real.pi * y₀) := by nlinarith
  refine ⟨max C₀ 1 * Real.exp (2 * Real.pi * y₀), hCbig, fun t hat => ?_⟩
  rcases le_or_gt t y₀ with ht | ht
  · have h1 : ‖M.radialKernel t‖ ≤ max C₀ 1 := le_trans (hC₀ t ⟨hat, ht⟩) (le_max_left _ _)
    have hexp : (1 : ℝ) ≤ Real.exp (2 * Real.pi * y₀) * Real.exp (-(2 * Real.pi * t)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [Real.pi_pos]
    calc ‖M.radialKernel t‖ ≤ max C₀ 1 := h1
      _ = max C₀ 1 * 1 := (mul_one _).symm
      _ ≤ max C₀ 1 * (Real.exp (2 * Real.pi * y₀) * Real.exp (-(2 * Real.pi * t))) :=
          mul_le_mul_of_nonneg_left hexp (le_trans zero_le_one hmax)
      _ = max C₀ 1 * Real.exp (2 * Real.pi * y₀) * Real.exp (-(2 * Real.pi * t)) := by ring
  · calc ‖M.radialKernel t‖ ≤ Real.exp (-(2 * Real.pi * t)) := hdecay t ht.le
      _ = 1 * Real.exp (-(2 * Real.pi * t)) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hCbig (Real.exp_pos _).le

/-- **Uniform decay of the Maass wave above an arbitrary positive height.**  The strengthening of
`maassWave_uniform_decay` that removes the dependence on the normalization height. -/
theorem maassWave_decay_above (M : GenuineMaassCuspForm3D) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ, a ≤ y →
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ≤
        B * Real.sqrt y * Real.exp (-(2 * Real.pi * y)) := by
  obtain ⟨C, hC1, hC⟩ := radialKernel_norm_le_exp_of_pos M ha
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  set A : ℕ := M.eigenData.E₀ + 2 with hA
  set r₀ : ℝ := Real.exp (-(2 * Real.pi * a)) with hr₀
  have hr₀pos : 0 < r₀ := Real.exp_pos _
  have hr₀lt : r₀ < 1 := by
    rw [hr₀]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hBsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r₀ ^ n :=
    summable_shifted_pow_mul_geometric hr₀pos hr₀lt A
  set S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ A * r₀ ^ n with hS
  have hSnonneg : 0 ≤ S := tsum_nonneg fun n => by positivity
  refine ⟨C * S, by positivity, fun x y hy => ?_⟩
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le ha hy
  set r : ℝ := Real.exp (-(2 * Real.pi * y)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hrle : r ≤ r₀ := by
    rw [hr, hr₀]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hterm : ∀ n : ℕ,
      ‖maassFourierCoefficient M.eigenData n *
        ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
        M.radialKernel (((n : ℝ) + 1) * y)‖ ≤ C * (((n : ℝ) + 1) ^ A * r₀ ^ n) * r := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hge : a ≤ ((n : ℝ) + 1) * y := by
      calc a ≤ y := hy
        _ = 1 * y := (one_mul y).symm
        _ ≤ ((n : ℝ) + 1) * y := mul_le_mul_of_nonneg_right hn1 hypos.le
    have hexp : Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) * y))) = r ^ (n + 1) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hk : ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ≤ C * r ^ (n + 1) := by
      rw [← hexp]; exact hC _ hge
    have hlam : ‖M.eigenData.lam (n + 1)‖ ≤ ((n : ℝ) + 1) ^ A := by
      have h := lam_norm_le M.eigenData (n + 1) (by omega)
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rwa [hcast] at h
    have hcos : |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| ≤ 1 := Real.abs_cos_le_one _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hstep : ‖M.eigenData.lam (n + 1)‖ *
        |Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x)| *
        ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ≤
        ((n : ℝ) + 1) ^ A * 1 * (C * r ^ (n + 1)) :=
      mul_le_mul (mul_le_mul hlam hcos (abs_nonneg _) (by positivity)) hk
        (norm_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hmono : r ^ n ≤ r₀ ^ n := pow_le_pow_left₀ hrpos.le hrle n
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ A := by positivity
    calc ((n : ℝ) + 1) ^ A * 1 * (C * r ^ (n + 1))
        = C * (((n : ℝ) + 1) ^ A * r ^ n) * r := by rw [pow_succ]; ring
      _ ≤ C * (((n : ℝ) + 1) ^ A * r₀ ^ n) * r :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hnn) hCpos.le)
            hrpos.le
  have hsummable : Summable fun n : ℕ =>
      ‖maassFourierCoefficient M.eigenData n *
        ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
        M.radialKernel (((n : ℝ) + 1) * y)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      (((hBsum.mul_left C)).mul_right r)
  rw [maassWaveCoordinates, waveForm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg y)]
  calc Real.sqrt y * ‖∑' n : ℕ, maassFourierCoefficient M.eigenData n *
          ((Real.cos (2 * Real.pi * ((n : ℝ) + 1) * x) : ℝ) : ℂ) *
          M.radialKernel (((n : ℝ) + 1) * y)‖
      ≤ Real.sqrt y * ∑' n : ℕ, C * (((n : ℝ) + 1) ^ A * r₀ ^ n) * r := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg y)
        exact le_trans (norm_tsum_le_tsum_norm hsummable)
          (Summable.tsum_le_tsum hterm hsummable ((hBsum.mul_left C).mul_right r))
    _ = C * S * Real.sqrt y * r := by
        rw [tsum_mul_right, tsum_mul_left, hS]
        ring

/-- `√y·e^{-2πy} ≤ 1` on the whole positive ray: exponential decay dominates the square root, so a
decay estimate above a height is a *bound* above that height. -/
lemma sqrt_mul_exp_neg_le_one {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y * Real.exp (-(2 * Real.pi * y)) ≤ 1 := by
  have h1 : Real.sqrt y ≤ y + 1 := by
    have hle : y ≤ (y + 1) ^ 2 := by nlinarith
    calc Real.sqrt y ≤ Real.sqrt ((y + 1) ^ 2) := Real.sqrt_le_sqrt hle
      _ = y + 1 := Real.sqrt_sq (by linarith)
  have h2 : Real.sqrt y * Real.exp (-(2 * Real.pi * y)) ≤
      Real.exp y * Real.exp (-(2 * Real.pi * y)) :=
    mul_le_mul_of_nonneg_right (le_trans h1 (Real.add_one_le_exp y)) (Real.exp_pos _).le
  rw [← Real.exp_add] at h2
  refine le_trans h2 ?_
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])

/-- **The Maass wave is bounded above any positive height**, uniformly in the horizontal
coordinate. -/
theorem maassWave_bounded_above (M : GenuineMaassCuspForm3D) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ, a ≤ y →
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := maassWave_decay_above M ha
  refine ⟨B, hB, fun x y hy => ?_⟩
  have hypos : (0 : ℝ) ≤ y := le_trans ha.le hy
  refine le_trans (hbound x y hy) ?_
  calc B * Real.sqrt y * Real.exp (-(2 * Real.pi * y))
      = B * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) := by ring
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left (sqrt_mul_exp_neg_le_one hypos) hB
    _ = B := mul_one B

/-- **The Maass wave is bounded on the fundamental domain.**  On `𝒟` the height is at least
`√3/2` (`HeckeSupBound.fd_im_ge`), which is above zero, so `maassWave_bounded_above` applies. -/
theorem maassWave_bounded_on_fd (M : GenuineMaassCuspForm3D) :
    ∃ C : ℝ, ∀ z ∈ ModularGroup.fd,
      ‖maassWave M.eigenData M.radialKernel z‖ ≤ C := by
  have ha : (0 : ℝ) < Real.sqrt 3 / 2 := by
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  obtain ⟨B, _, hbound⟩ := maassWave_bounded_above M ha
  exact ⟨B, fun z hz => hbound _ _ (CriticalLinePhasor.HeckeSupBound.fd_im_ge hz)⟩

/-- **The Maass wave is bounded on the whole upper half-plane.**  Unconditional: decay at the cusp
supplies the bound on `𝒟`, and level-one invariance spreads it everywhere — in particular over the
strip, where the `y → 0` end of the Rankin--Selberg integrability estimate needs it. -/
theorem maassWave_bounded (M : GenuineMaassCuspForm3D) :
    ∃ C : ℝ, ∀ z : UpperHalfPlane, ‖maassWave M.eigenData M.radialKernel z‖ ≤ C := by
  obtain ⟨C, hC⟩ := maassWave_bounded_on_fd M
  exact ⟨C, maassWave_bounded_of_bounded_on_fd M hC⟩

/-- The Petersson density of a Maass form is bounded on all of `ℍ`. -/
theorem maassP_bounded (M : GenuineMaassCuspForm3D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖maassWave M.eigenData M.radialKernel z‖ ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := maassWave_bounded M
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC ⟨⟨0, 1⟩, by norm_num⟩)
  refine ⟨C ^ 2, by positivity, fun z => ?_⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (hC z) 2

/-- **The Maass wave is continuous on `ℍ`.**  `wave_smooth` gives smoothness of the coordinate
realization on `ℝ × Ioi 0`, and the coordinate map of the upper half-plane lands there.  This is the
joint measurability input of the strip-integrability assembly. -/
theorem continuous_maassWave (M : GenuineMaassCuspForm3D) :
    Continuous (maassWave M.eigenData M.radialKernel) := by
  have hc : ContinuousOn
      (Function.uncurry (maassWaveCoordinates M.eigenData M.radialKernel))
      (Set.univ ×ˢ Set.Ioi (0:ℝ)) := (M.wave_smooth 0).continuousOn
  have hg : Continuous (fun τ : UpperHalfPlane => (((τ : ℂ).re, (τ : ℂ).im) : ℝ × ℝ)) :=
    (Complex.continuous_re.comp UpperHalfPlane.continuous_coe).prodMk
      (Complex.continuous_im.comp UpperHalfPlane.continuous_coe)
  have hmaps : ∀ τ : UpperHalfPlane,
      (((τ : ℂ).re, (τ : ℂ).im) : ℝ × ℝ) ∈ Set.univ ×ˢ Set.Ioi (0:ℝ) :=
    fun τ => ⟨Set.mem_univ _, τ.im_pos⟩
  exact hc.comp_continuous hg hmaps

/-- The Maass Rankin--Selberg integrand is continuous on `ℍ` for every exponent. -/
theorem continuous_maassRsIntegrand (M : GenuineMaassCuspForm3D) (s : ℂ) :
    Continuous (fun z : UpperHalfPlane =>
      ((‖maassWave M.eigenData M.radialKernel z‖ ^ 2 : ℝ) : ℂ) * ((z.im : ℝ) : ℂ) ^ s) :=
  (Complex.continuous_ofReal.comp ((continuous_maassWave M).norm.pow 2)).mul
    (Continuous.cpow (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im)
      continuous_const fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos)

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.continuous_maassWave
#print axioms CriticalLinePhasor.ThreeDConverse.continuous_maassRsIntegrand
#print axioms CriticalLinePhasor.ThreeDConverse.radialKernel_norm_le_exp_of_pos
#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_decay_above
#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_bounded_above
#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_bounded_on_fd
#print axioms CriticalLinePhasor.ThreeDConverse.maassWave_bounded
#print axioms CriticalLinePhasor.ThreeDConverse.maassP_bounded
