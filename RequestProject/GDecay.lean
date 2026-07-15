import RequestProject.DomainIntegrability

/-!
# The averaged tail decays faster than every power

Route B, part one.  The `𝒟`-average of the truncated bank against the Petersson density,
`G(t) = ∫_𝒟 P(z)·truncTheta(z,t) dμ`, decays like `e^{-c√t}` at infinity (`G_isBigO_rpow`,
via `G_norm_le`): the pointwise product is bounded, for `t ≥ 1` on `𝒟`, by a `y`-weight times
`e^{-π√(3t/2)}` (`ptwise_bound`, the `y ∼ √t` saddle materialized by AM-GM from `P`'s
`e^{-2πy}` against the theta tail's `e^{-π cz t}` with `cz ≥ 3/(8y)`), and the `y`-weight is
integrable over `𝒟` (`weight_integrableOn_fd`, bounded × finite measure).  Faster-than-power
decay makes the Mellin transform of `G` entire — the holomorphy the continuation needs.
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter Asymptotics
open scoped Real Topology MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The `y`-weight controlling the average. -/
noncomputable def wt (C₁ : ℝ) (y : ℝ) : ℝ := (1 + C₁ * y ^ 2) * Real.exp (-π * y)

/-- The weight is continuous. -/
lemma continuous_wt (C₁ : ℝ) : Continuous fun z : ℍ => wt C₁ z.im := by
  unfold wt
  fun_prop

/-- **The AM-GM saddle**: `P`'s decay against the theta tail collapses to a `√t` rate.  For
`t ≥ 1` and `y > 0`, `e^{-2πy}·e^{-3πt/(8y)} ≤ e^{-πy}·e^{-π√(3t/2)}`. -/
lemma amgm_saddle {y t : ℝ} (hy : 0 < y) (ht : 1 ≤ t) :
    Real.exp (-2 * π * y) * Real.exp (-(3 * π * t / (8 * y))) ≤
      Real.exp (-π * y) * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- the AM-GM height inequality  √(3t/2) ≤ y + 3t/(8y)
  have hsqrt : Real.sqrt (3 * t / 2) ≤ y + 3 * t / (8 * y) := by
    have hkey : Real.sqrt (3 * t / 2) * (8 * y) ≤ (y + 3 * t / (8 * y)) * (8 * y) := by
      have hrhs : (y + 3 * t / (8 * y)) * (8 * y) = 8 * y ^ 2 + 3 * t := by
        field_simp
      rw [hrhs]
      nlinarith [sq_nonneg (2 * y - Real.sqrt (3 * t / 2)),
        Real.sq_sqrt (show (0:ℝ) ≤ 3 * t / 2 by positivity),
        Real.sqrt_nonneg (3 * t / 2)]
    exact le_of_mul_le_mul_right hkey (by positivity : (0:ℝ) < 8 * y)
  have hmul : π * Real.sqrt (3 * t / 2) ≤ π * (y + 3 * t / (8 * y)) :=
    mul_le_mul_of_nonneg_left hsqrt Real.pi_pos.le
  have hexpand : π * (y + 3 * t / (8 * y)) = π * y + 3 * π * t / (8 * y) := by ring
  rw [hexpand] at hmul
  linarith [hmul]

/-- The saddle exponential decays faster than every power at infinity. -/
lemma exp_sqrt_isBigO (a : ℝ) :
    (fun t : ℝ => Real.exp (-(π * Real.sqrt (3 * t / 2)))) =O[atTop] (· ^ (-a)) := by
  have hb : (fun u : ℝ => Real.exp (-π * u)) =O[atTop] (fun u : ℝ => u ^ (-(2 * a))) :=
    CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow Real.pi_pos (-(2 * a))
  have h32 : Tendsto (fun t : ℝ => 3 * t / 2) atTop atTop :=
    tendsto_atTop_mono' atTop
      (by filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; show t ≤ 3 * t / 2; linarith)
      tendsto_id
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (3 * t / 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp h32
  have hcomp : (fun t : ℝ => Real.exp (-π * Real.sqrt (3 * t / 2))) =O[atTop]
      (fun t : ℝ => (Real.sqrt (3 * t / 2)) ^ (-(2 * a))) := hb.comp_tendsto hsqrt
  have hcong : (fun t : ℝ => Real.exp (-π * Real.sqrt (3 * t / 2))) =
      (fun t : ℝ => Real.exp (-(π * Real.sqrt (3 * t / 2)))) := by
    funext t; congr 1; ring
  rw [hcong] at hcomp
  refine hcomp.trans ?_
  have heq : (fun t : ℝ => (Real.sqrt (3 * t / 2)) ^ (-(2 * a))) =ᶠ[atTop]
      (fun t : ℝ => (3 / 2 : ℝ) ^ (-a) * t ^ (-a)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      show (1/2 : ℝ) * (-(2 * a)) = -a by ring,
      show (3 * t / 2 : ℝ) = (3/2) * t by ring, Real.mul_rpow (by norm_num) ht.le]
  exact heq.trans_isBigO (Asymptotics.isBigO_const_mul_self _ _ _)

/-- **The pointwise saddle bound**: on `𝒟`, for `t ≥ 1`, the Petersson density against the
bank tail is dominated by a `y`-weight times the saddle exponential. -/
lemma ptwise_bound (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ∃ C₁ C₆ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₆ ∧ ∀ z ∈ ModularGroup.fd, ∀ t : ℝ, 1 ≤ t →
      P k f z * (latticeTheta z t - 1) ≤
        C₆ * wt C₁ z.im * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
  obtain ⟨C, hC0, hC⟩ := P_exp_decay_on_fd f hk
  set C₁ : ℝ := 256 * latticeZ / (9 * π ^ 2) with hC₁def
  refine ⟨C₁, C * Real.exp (π / 2),
    by rw [hC₁def]; exact div_nonneg (mul_nonneg (by norm_num) latticeZ_nonneg) (by positivity),
    mul_nonneg hC0 (Real.exp_pos _).le, fun z hz t ht => ?_⟩
  have hy : 0 < z.im := z.im_pos
  have hcz := cz_pos z
  have hczfd := cz_ge_on_fd hz
  have hC1nn : (0 : ℝ) ≤ C₁ := by
    rw [hC₁def]; exact div_nonneg (mul_nonneg (by norm_num) latticeZ_nonneg) (by positivity)
  have hpolynn : (0 : ℝ) ≤ 1 + C₁ * z.im ^ 2 :=
    add_nonneg zero_le_one (mul_nonneg hC1nn (sq_nonneg _))
  have hθnn : 0 ≤ latticeTheta z t - 1 := by
    have := one_le_latticeTheta z (lt_of_lt_of_le one_pos ht); linarith
  have hPnn : 0 ≤ P k f z := P_nonneg f z
  -- step 1: P·(θ-1) ≤ [C e^{-2πy}]·[Kz e^{-π cz t}]
  have hstep1 : P k f z * (latticeTheta z t - 1) ≤
      (C * Real.exp (-(2 * π) * z.im)) * (Kz z * Real.exp (-(π * cz z) * t)) := by
    apply mul_le_mul (hC z hz) (theta_tail_bound z ht) hθnn
    exact mul_nonneg hC0 (Real.exp_pos _).le
  -- step 2: rate bound  e^{-π cz t} ≤ e^{-(3πt/(8y))}
  have hrate : Real.exp (-(π * cz z) * t) ≤ Real.exp (-(3 * π * t / (8 * z.im))) := by
    apply Real.exp_le_exp.mpr
    have h8y : (0 : ℝ) < 8 * z.im := by positivity
    have h3 : (3 : ℝ) ≤ cz z * (8 * z.im) := (div_le_iff₀ h8y).mp hczfd
    rw [neg_mul, neg_le_neg_iff, div_le_iff₀ h8y]
    nlinarith [mul_le_mul_of_nonneg_right h3 (show (0:ℝ) ≤ π * t by positivity),
      Real.pi_pos, ht]
  -- step 3: the coefficient bound  4/(π cz)² ≤ (256/(9π²))·y²
  have hquad : 4 / (π * cz z) ^ 2 ≤ 256 / (9 * π ^ 2) * z.im ^ 2 := by
    have hlow : 3 * π / (8 * z.im) ≤ π * cz z := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left
        ((div_le_iff₀ (show (0:ℝ) < 8 * z.im by positivity)).mp hczfd) Real.pi_pos.le]
    have hsq : (3 * π / (8 * z.im)) ^ 2 ≤ (π * cz z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have h1 : 4 / (π * cz z) ^ 2 ≤ 4 / (3 * π / (8 * z.im)) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  -- Kz bound in y-polynomial form
  have hKz : Kz z ≤ Real.exp (π / 2) * (1 + C₁ * z.im ^ 2) := by
    refine (Kz_le z).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hZ := latticeZ_nonneg
    rw [hC₁def]
    have : 4 / (π * cz z) ^ 2 * latticeZ ≤ 256 / (9 * π ^ 2) * z.im ^ 2 * latticeZ :=
      mul_le_mul_of_nonneg_right hquad hZ
    calc 1 + 4 / (π * cz z) ^ 2 * latticeZ
        ≤ 1 + 256 / (9 * π ^ 2) * z.im ^ 2 * latticeZ := by linarith
      _ = 1 + 256 * latticeZ / (9 * π ^ 2) * z.im ^ 2 := by ring
  -- assemble
  have hcombine : Kz z * Real.exp (-(π * cz z) * t) ≤
      Real.exp (π / 2) * (1 + C₁ * z.im ^ 2) * Real.exp (-(3 * π * t / (8 * z.im))) :=
    mul_le_mul hKz hrate (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le hpolynn)
  calc P k f z * (latticeTheta z t - 1)
      ≤ (C * Real.exp (-(2 * π) * z.im)) * (Kz z * Real.exp (-(π * cz z) * t)) := hstep1
    _ ≤ (C * Real.exp (-(2 * π) * z.im)) *
          (Real.exp (π / 2) * (1 + C₁ * z.im ^ 2) *
            Real.exp (-(3 * π * t / (8 * z.im)))) :=
        mul_le_mul_of_nonneg_left hcombine (by positivity)
    _ = C * Real.exp (π / 2) * (1 + C₁ * z.im ^ 2) *
          (Real.exp (-2 * π * z.im) * Real.exp (-(3 * π * t / (8 * z.im)))) := by
        rw [show -(2 * π) * z.im = -2 * π * z.im by ring]; ring
    _ ≤ C * Real.exp (π / 2) * (1 + C₁ * z.im ^ 2) *
          (Real.exp (-π * z.im) * Real.exp (-(π * Real.sqrt (3 * t / 2)))) := by
        apply mul_le_mul_of_nonneg_left (amgm_saddle hy ht)
        exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) hpolynn
    _ = C * Real.exp (π / 2) * wt C₁ z.im * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
        rw [wt]; ring

end CriticalLinePhasor.Unfolding
