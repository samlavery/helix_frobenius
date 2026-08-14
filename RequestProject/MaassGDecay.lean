import RequestProject.MaassPDecayOnFd
import RequestProject.GDecay

/-!
# Route B's pointwise bound, ported to the Maass density

`GDecay.ptwise_bound` touches the cusp form in exactly two places: the density's exponential decay
on `𝒟` and its nonnegativity.  Both are now available for a Maass form
(`maassP_exp_decay_on_fd`, `maassP_nonneg`), and everything else in the argument — the theta tail
bound, `cz_ge_on_fd`, the `y ~ √t` AM-GM saddle, the `Kz` polynomial bound — never mentions the
form at all.

This is the seventh form-independent transfer in this campaign, and the same pattern each time:
machinery written for holomorphic cusp forms turns out to depend only on the *density*, and the
Maass density satisfies the same interface (here with room to spare, since it decays like
`e^{-4πy}`).

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter Asymptotics
open scoped Real Topology MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.ThreeDConverse

/-- **The Maass pointwise bound of Route B.**  The `y ~ √t` saddle, with the Maass density. -/
theorem maass_ptwise_bound (M : GenuineMaassCuspForm3D) :
    ∃ C₁ C₆ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₆ ∧ ∀ z ∈ ModularGroup.fd, ∀ t : ℝ, 1 ≤ t →
      maassP M z * (latticeTheta z t - 1) ≤
        C₆ * wt C₁ z.im * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
  obtain ⟨C, hC0, hC⟩ := maassP_exp_decay_on_fd M
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
  have hPnn : 0 ≤ maassP M z := maassP_nonneg M z
  -- step 1: P·(θ-1) ≤ [C e^{-2πy}]·[Kz e^{-π cz t}]
  have hstep1 : maassP M z * (latticeTheta z t - 1) ≤
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
  calc maassP M z * (latticeTheta z t - 1)
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

#print axioms CriticalLinePhasor.Unfolding.maass_ptwise_bound
