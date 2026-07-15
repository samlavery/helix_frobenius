import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rectangle argument-principle kernel

Elementary boundary-integral lemmas used by the independent zeta contour count.
-/

open Complex Set MeasureTheory
open scoped Interval Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The positively oriented boundary integral of `f` around the rectangle with southwest
corner `a + ic` and northeast corner `b + id`. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) +
    I * (∫ y in c..d, f (b + y * I)) - I * (∫ y in c..d, f (a + y * I))

/-- Cauchy--Goursat in the boundary-integral normalization used here. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : DifferentiableOn ℂ f (Icc a b ×ℂ Icc c d)) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (a + c * I) (b + d * I) (by simpa [uIcc_of_le hab, uIcc_of_le hcd] using hf))

private theorem inv_cartesian_decomposition (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * I)⁻¹) =
      ((x / (x ^ 2 + y ^ 2) : ℝ) : ℂ) -
        ((y / (x ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
  have hnorm : Complex.normSq ((x : ℂ) + (y : ℂ) * I) = x ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [Complex.inv_def]
  rw [hnorm]
  push_cast
  rw [map_add, conj_ofReal, map_mul, conj_ofReal, conj_I]
  ring

private theorem inv_sub_I_decomposition (r x : ℝ) :
    (((x : ℂ) - (r : ℂ) * I)⁻¹) =
      ((x / (x ^ 2 + r ^ 2) : ℝ) : ℂ) +
        ((r / (x ^ 2 + r ^ 2) : ℝ) : ℂ) * I := by
  rw [show (x : ℂ) - (r : ℂ) * I = (x : ℂ) + (-r : ℝ) * I by push_cast; ring,
    inv_cartesian_decomposition]
  push_cast
  ring_nf

private theorem integral_x_div_sq_add_sq {r : ℝ} (hr : 0 < r) :
    (∫ x in -r..r, x / (x ^ 2 + r ^ 2)) = 0 := by
  let F : ℝ → ℝ := fun x ↦ Real.log (x ^ 2 + r ^ 2) / 2
  have hderiv : ∀ x ∈ uIcc (-r) r, HasDerivAt F (x / (x ^ 2 + r ^ 2)) x := by
    intro x hx
    have hne : x ^ 2 + r ^ 2 ≠ 0 := by positivity
    dsimp [F]
    convert (((hasDerivAt_pow 2 x).add_const (r ^ 2)).log hne).div_const 2 using 1
    all_goals try rfl
    next =>
      simp only [Nat.reduceSubDiff, pow_one]
      ring
  have hcont : Continuous (fun x : ℝ ↦ x / (x ^ 2 + r ^ 2)) :=
    continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp [F]

private theorem integral_r_div_sq_add_sq {r : ℝ} (hr : 0 < r) :
    (∫ x in -r..r, r / (x ^ 2 + r ^ 2)) = Real.pi / 2 := by
  let F : ℝ → ℝ := fun x ↦ Real.arctan (x / r)
  have hderiv : ∀ x ∈ uIcc (-r) r, HasDerivAt F (r / (x ^ 2 + r ^ 2)) x := by
    intro x hx
    have hne : x ^ 2 + r ^ 2 ≠ 0 := by positivity
    dsimp [F]
    convert Real.hasDerivAt_arctan (x / r) |>.comp x (hasDerivAt_id x |>.div_const r) using 1
    all_goals try rfl
    next =>
      change r / (x ^ 2 + r ^ 2) = 1 / (1 + (x / r) ^ 2) * (1 / r)
      field_simp [hr.ne', hne]
      ring
  have hcont : Continuous (fun x : ℝ ↦ r / (x ^ 2 + r ^ 2)) :=
    continuous_const.div (continuous_id.pow 2 |>.add continuous_const) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp [F, hr.ne', Real.arctan_one, Real.arctan_neg]
  ring

private theorem integral_inv_sub_I {r : ℝ} (hr : 0 < r) :
    (∫ x in -r..r, (((x : ℂ) - (r : ℂ) * I)⁻¹)) = (Real.pi / 2 : ℝ) * I := by
  simp_rw [inv_sub_I_decomposition]
  have hden : ∀ x : ℝ, x ^ 2 + r ^ 2 ≠ 0 := fun x ↦ by
    nlinarith [sq_pos_of_pos hr]
  have hcontx : Continuous (fun x : ℝ ↦ x / (x ^ 2 + r ^ 2)) :=
    continuous_id.div (continuous_id.pow 2 |>.add continuous_const) hden
  have hcontr : Continuous (fun x : ℝ ↦ r / (x ^ 2 + r ^ 2)) :=
    continuous_const.div (continuous_id.pow 2 |>.add continuous_const) hden
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, integral_x_div_sq_add_sq hr,
      integral_r_div_sq_add_sq hr]
    simp
  · exact (continuous_ofReal.comp hcontx).intervalIntegrable _ _
  · exact ((continuous_ofReal.comp hcontr).mul continuous_const).intervalIntegrable _ _

private theorem integral_inv_add_I {r : ℝ} (hr : 0 < r) :
    (∫ x in -r..r, (((x : ℂ) + (r : ℂ) * I)⁻¹)) = -(Real.pi / 2 : ℝ) * I := by
  simp_rw [inv_cartesian_decomposition]
  have hden : ∀ x : ℝ, x ^ 2 + r ^ 2 ≠ 0 := fun x ↦ by
    nlinarith [sq_pos_of_pos hr]
  have hcontx : Continuous (fun x : ℝ ↦ x / (x ^ 2 + r ^ 2)) :=
    continuous_id.div (continuous_id.pow 2 |>.add continuous_const) hden
  have hcontr : Continuous (fun x : ℝ ↦ r / (x ^ 2 + r ^ 2)) :=
    continuous_const.div (continuous_id.pow 2 |>.add continuous_const) hden
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, integral_x_div_sq_add_sq hr,
      integral_r_div_sq_add_sq hr]
    simp
  · exact (continuous_ofReal.comp hcontx).intervalIntegrable _ _
  · exact ((continuous_ofReal.comp hcontr).mul continuous_const).intervalIntegrable _ _

private theorem integral_inv_right_I {r : ℝ} (hr : 0 < r) :
    (∫ y in -r..r, (((r : ℂ) + (y : ℂ) * I)⁻¹)) = (Real.pi / 2 : ℝ) := by
  simp_rw [inv_cartesian_decomposition]
  have hden : ∀ y : ℝ, r ^ 2 + y ^ 2 ≠ 0 := fun y ↦ by
    nlinarith [sq_pos_of_pos hr]
  have hcontr : Continuous (fun y : ℝ ↦ r / (r ^ 2 + y ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hden
  have hconty : Continuous (fun y : ℝ ↦ y / (r ^ 2 + y ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hden
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal]
    have hy : (∫ y in -r..r, y / (r ^ 2 + y ^ 2)) = 0 := by
      rw [show (fun y : ℝ ↦ y / (r ^ 2 + y ^ 2)) =
        fun y ↦ y / (y ^ 2 + r ^ 2) by funext y; ring]
      exact integral_x_div_sq_add_sq hr
    have hr' : (∫ y in -r..r, r / (r ^ 2 + y ^ 2)) = Real.pi / 2 := by
      rw [show (fun y : ℝ ↦ r / (r ^ 2 + y ^ 2)) =
        fun y ↦ r / (y ^ 2 + r ^ 2) by funext y; ring]
      exact integral_r_div_sq_add_sq hr
    rw [hy, hr']
    simp
  · exact (continuous_ofReal.comp hcontr).intervalIntegrable _ _
  · exact ((continuous_ofReal.comp hconty).mul continuous_const).intervalIntegrable _ _

private theorem integral_inv_left_I {r : ℝ} (hr : 0 < r) :
    (∫ y in -r..r, (((-r : ℝ) : ℂ) + (y : ℂ) * I)⁻¹) = -(Real.pi / 2 : ℝ) := by
  simp_rw [inv_cartesian_decomposition]
  have hden : ∀ y : ℝ, (-r) ^ 2 + y ^ 2 ≠ 0 := fun y ↦ by
    nlinarith [sq_pos_of_pos hr]
  have hcontr : Continuous (fun y : ℝ ↦ -r / ((-r) ^ 2 + y ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) hden
  have hconty : Continuous (fun y : ℝ ↦ y / ((-r) ^ 2 + y ^ 2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hden
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal]
    have hy : (∫ y in -r..r, y / ((-r) ^ 2 + y ^ 2)) = 0 := by
      rw [show (fun y : ℝ ↦ y / ((-r) ^ 2 + y ^ 2)) =
        fun y ↦ y / (y ^ 2 + r ^ 2) by funext y; ring]
      exact integral_x_div_sq_add_sq hr
    have hr' : (∫ y in -r..r, -r / ((-r) ^ 2 + y ^ 2)) = -(Real.pi / 2) := by
      rw [show (fun y : ℝ ↦ -r / ((-r) ^ 2 + y ^ 2)) =
        fun y ↦ -(r / (y ^ 2 + r ^ 2)) by funext y; ring]
      rw [intervalIntegral.integral_neg, integral_r_div_sq_add_sq hr]
    rw [hy, hr']
    simp
  · exact (continuous_ofReal.comp hcontr).intervalIntegrable _ _
  · exact ((continuous_ofReal.comp hconty).mul continuous_const).intervalIntegrable _ _

/-- The inverse coordinate has boundary integral `2πi` on a centered square. -/
theorem rectangleBoundaryIntegral_inv_centered_square {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹) (-r) r (-r) r =
      2 * Real.pi * I := by
  unfold rectangleBoundaryIntegral
  norm_num only [ofReal_neg]
  rw [show (fun x : ℝ ↦ (↑x + -↑r * I : ℂ)⁻¹) =
    fun x : ℝ ↦ ((x : ℂ) - (r : ℂ) * I)⁻¹ by funext x; ring]
  rw [show (fun y : ℝ ↦ (-↑r + ↑y * I : ℂ)⁻¹) =
    fun y : ℝ ↦ (((-r : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ by funext y; simp]
  rw [integral_inv_sub_I hr, integral_inv_add_I hr,
    integral_inv_right_I hr, integral_inv_left_I hr]
  push_cast
  ring

/-- Translation of the centered-square inverse integral to an arbitrary center. -/
theorem rectangleBoundaryIntegral_inv_square {ρ : ℂ} {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - ρ)⁻¹)
        (ρ.re - r) (ρ.re + r) (ρ.im - r) (ρ.im + r) = 2 * Real.pi * I := by
  have hbottom :
      (∫ x in ρ.re - r..ρ.re + r,
        ((x : ℂ) + ((ρ.im - r : ℝ) : ℂ) * I - ρ)⁻¹) =
      ∫ x in -r..r, ((x : ℂ) - (r : ℂ) * I)⁻¹ := by
    calc
      _ = ∫ x in ρ.re - r..ρ.re + r,
          ((((x - ρ.re : ℝ) : ℂ) - (r : ℂ) * I)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro x hx
            apply congrArg (fun z : ℂ ↦ z⁻¹)
            apply Complex.ext <;> simp
      _ = _ := by
        calc
          _ = ∫ u in (ρ.re - r) - ρ.re..(ρ.re + r) - ρ.re,
              ((u : ℂ) - (r : ℂ) * I)⁻¹ :=
            intervalIntegral.integral_comp_sub_right
              (a := ρ.re - r) (b := ρ.re + r)
              (f := fun u : ℝ ↦ ((u : ℂ) - (r : ℂ) * I)⁻¹) ρ.re
          _ = _ := by congr 1 <;> ring
  have htop :
      (∫ x in ρ.re - r..ρ.re + r,
        ((x : ℂ) + ((ρ.im + r : ℝ) : ℂ) * I - ρ)⁻¹) =
      ∫ x in -r..r, ((x : ℂ) + (r : ℂ) * I)⁻¹ := by
    calc
      _ = ∫ x in ρ.re - r..ρ.re + r,
          ((((x - ρ.re : ℝ) : ℂ) + (r : ℂ) * I)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro x hx
            apply congrArg (fun z : ℂ ↦ z⁻¹)
            apply Complex.ext <;> simp
      _ = _ := by
        calc
          _ = ∫ u in (ρ.re - r) - ρ.re..(ρ.re + r) - ρ.re,
              ((u : ℂ) + (r : ℂ) * I)⁻¹ :=
            intervalIntegral.integral_comp_sub_right
              (a := ρ.re - r) (b := ρ.re + r)
              (f := fun u : ℝ ↦ ((u : ℂ) + (r : ℂ) * I)⁻¹) ρ.re
          _ = _ := by congr 1 <;> ring
  have hright :
      (∫ y in ρ.im - r..ρ.im + r,
        (((ρ.re + r : ℝ) : ℂ) + (y : ℂ) * I - ρ)⁻¹) =
      ∫ y in -r..r, ((r : ℂ) + (y : ℂ) * I)⁻¹ := by
    calc
      _ = ∫ y in ρ.im - r..ρ.im + r,
          (((r : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro y hy
            apply congrArg (fun z : ℂ ↦ z⁻¹)
            apply Complex.ext <;> simp
      _ = _ := by
        calc
          _ = ∫ u in (ρ.im - r) - ρ.im..(ρ.im + r) - ρ.im,
              ((r : ℂ) + (u : ℂ) * I)⁻¹ :=
            intervalIntegral.integral_comp_sub_right
              (a := ρ.im - r) (b := ρ.im + r)
              (f := fun u : ℝ ↦ ((r : ℂ) + (u : ℂ) * I)⁻¹) ρ.im
          _ = _ := by congr 1 <;> ring
  have hleft :
      (∫ y in ρ.im - r..ρ.im + r,
        (((ρ.re - r : ℝ) : ℂ) + (y : ℂ) * I - ρ)⁻¹) =
      ∫ y in -r..r, (((-r : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ := by
    calc
      _ = ∫ y in ρ.im - r..ρ.im + r,
          ((((-r : ℝ) : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro y hy
            apply congrArg (fun z : ℂ ↦ z⁻¹)
            apply Complex.ext <;> simp
      _ = _ := by
        calc
          _ = ∫ u in (ρ.im - r) - ρ.im..(ρ.im + r) - ρ.im,
              (((-r : ℝ) : ℂ) + (u : ℂ) * I)⁻¹ :=
            intervalIntegral.integral_comp_sub_right
              (a := ρ.im - r) (b := ρ.im + r)
              (f := fun u : ℝ ↦ (((-r : ℝ) : ℂ) + (u : ℂ) * I)⁻¹) ρ.im
          _ = _ := by congr 1 <;> ring
  unfold rectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  have hsquare := rectangleBoundaryIntegral_inv_centered_square hr
  unfold rectangleBoundaryIntegral at hsquare
  rw [show (fun x : ℝ ↦ ((x : ℂ) - (r : ℂ) * I)⁻¹) =
    fun x : ℝ ↦ ((x : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ by funext x; push_cast; ring]
  exact hsquare

/-- Additivity when a rectangle is split by a horizontal line. -/
theorem rectangleBoundaryIntegral_horizontal_add (f : ℂ → ℂ) (a b c m d : ℝ)
    (ha : Continuous (fun y : ℝ ↦ f (a + y * I)))
    (hb : Continuous (fun y : ℝ ↦ f (b + y * I))) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral f a b c m + rectangleBoundaryIntegral f a b m d := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hb.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals
      (ha.intervalIntegrable _ _) (ha.intervalIntegrable _ _)]
  ring

/-- Additivity when a rectangle is split by a vertical line. -/
theorem rectangleBoundaryIntegral_vertical_add (f : ℂ → ℂ) (a m b c d : ℝ)
    (hc : Continuous (fun x : ℝ ↦ f (x + c * I)))
    (hd : Continuous (fun x : ℝ ↦ f (x + d * I))) :
    rectangleBoundaryIntegral f a b c d =
      rectangleBoundaryIntegral f a m c d + rectangleBoundaryIntegral f m b c d := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hd.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  ring

private theorem continuous_inv_horizontal {ρ : ℂ} {y₀ : ℝ} (hy : y₀ ≠ ρ.im) :
    Continuous (fun x : ℝ ↦ ((x : ℂ) + (y₀ : ℂ) * I - ρ)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro x hx
  have him := congrArg Complex.im hx
  simp at him
  exact hy (sub_eq_zero.mp him)

private theorem continuous_inv_vertical {ρ : ℂ} {x₀ : ℝ} (hx : x₀ ≠ ρ.re) :
    Continuous (fun y : ℝ ↦ ((x₀ : ℂ) + (y : ℂ) * I - ρ)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro y hy
  have hre := congrArg Complex.re hy
  simp at hre
  exact hx (sub_eq_zero.mp hre)

private theorem differentiableOn_inv_sub_of_re_separated {ρ : ℂ} {a b c d : ℝ}
    (hsep : b < ρ.re ∨ ρ.re < a) :
    DifferentiableOn ℂ (fun z : ℂ ↦ (z - ρ)⁻¹) (Icc a b ×ℂ Icc c d) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.inv (by fun_prop)
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  have hre' : z.re = ρ.re := sub_eq_zero.mp hre
  rcases hsep with hsep | hsep
  · exact (not_le_of_gt hsep) (hre' ▸ hz.1.2)
  · exact (not_le_of_gt hsep) (hre' ▸ hz.1.1)

private theorem differentiableOn_inv_sub_of_im_separated {ρ : ℂ} {a b c d : ℝ}
    (hsep : d < ρ.im ∨ ρ.im < c) :
    DifferentiableOn ℂ (fun z : ℂ ↦ (z - ρ)⁻¹) (Icc a b ×ℂ Icc c d) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.inv (by fun_prop)
  intro hzero
  have him := congrArg Complex.im hzero
  simp at him
  have him' : z.im = ρ.im := sub_eq_zero.mp him
  rcases hsep with hsep | hsep
  · exact (not_le_of_gt hsep) (him' ▸ hz.2.2)
  · exact (not_le_of_gt hsep) (him' ▸ hz.2.1)

/-- A point strictly inside a rectangle contributes exactly `2πi` to the boundary integral
of its inverse coordinate. -/
theorem rectangleBoundaryIntegral_inv_sub_of_mem_interior
    {ρ : ℂ} {a b c d : ℝ}
    (ha : a < ρ.re) (hb : ρ.re < b) (hc : c < ρ.im) (hd : ρ.im < d) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - ρ)⁻¹) a b c d = 2 * Real.pi * I := by
  let r : ℝ := min (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im)) / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hra : a < ρ.re - r := by
    dsimp [r]
    have hmin := min_le_left (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
    have hmin' := min_le_left (ρ.re - a) (b - ρ.re)
    nlinarith
  have hrb : ρ.re + r < b := by
    dsimp [r]
    have hmin := min_le_left (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
    have hmin' := min_le_right (ρ.re - a) (b - ρ.re)
    nlinarith
  have hrc : c < ρ.im - r := by
    dsimp [r]
    have hmin := min_le_right (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
    have hmin' := min_le_left (ρ.im - c) (d - ρ.im)
    nlinarith
  have hrd : ρ.im + r < d := by
    dsimp [r]
    have hmin := min_le_right (min (ρ.re - a) (b - ρ.re)) (min (ρ.im - c) (d - ρ.im))
    have hmin' := min_le_right (ρ.im - c) (d - ρ.im)
    nlinarith
  let f : ℂ → ℂ := fun z ↦ (z - ρ)⁻¹
  have hsplit₁ := rectangleBoundaryIntegral_horizontal_add f a b c (ρ.im - r) d
    (continuous_inv_vertical (ne_of_lt ha)) (continuous_inv_vertical (ne_of_gt hb))
  have hsplit₂ := rectangleBoundaryIntegral_horizontal_add f a b (ρ.im - r) (ρ.im + r) d
    (continuous_inv_vertical (ne_of_lt ha)) (continuous_inv_vertical (ne_of_gt hb))
  have hsplit₃ := rectangleBoundaryIntegral_vertical_add f a (ρ.re - r) b (ρ.im - r) (ρ.im + r)
    (continuous_inv_horizontal (by linarith)) (continuous_inv_horizontal (by linarith))
  have hsplit₄ := rectangleBoundaryIntegral_vertical_add f (ρ.re - r) (ρ.re + r) b
    (ρ.im - r) (ρ.im + r)
    (continuous_inv_horizontal (by linarith)) (continuous_inv_horizontal (by linarith))
  have hbottom : rectangleBoundaryIntegral f a b c (ρ.im - r) = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f a b c (ρ.im - r)
    · linarith
    · linarith
    · exact differentiableOn_inv_sub_of_im_separated (Or.inl (by linarith))
  have htop : rectangleBoundaryIntegral f a b (ρ.im + r) d = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f a b (ρ.im + r) d
    · linarith
    · linarith
    · exact differentiableOn_inv_sub_of_im_separated (Or.inr (by linarith))
  have hleft : rectangleBoundaryIntegral f a (ρ.re - r) (ρ.im - r) (ρ.im + r) = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f a (ρ.re - r)
      (ρ.im - r) (ρ.im + r)
    · linarith
    · linarith
    · exact differentiableOn_inv_sub_of_re_separated (Or.inl (by linarith))
  have hright : rectangleBoundaryIntegral f (ρ.re + r) b (ρ.im - r) (ρ.im + r) = 0 := by
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn f (ρ.re + r) b
      (ρ.im - r) (ρ.im + r)
    · linarith
    · linarith
    · exact differentiableOn_inv_sub_of_re_separated (Or.inr (by linarith))
  have hcenter := rectangleBoundaryIntegral_inv_square (ρ := ρ) hr
  change rectangleBoundaryIntegral f a b c d = 2 * Real.pi * I
  rw [hsplit₁, hbottom, zero_add, hsplit₂, htop, add_zero,
    hsplit₃, hleft, zero_add, hsplit₄, hright, add_zero]
  exact hcenter

/-- An inverse-coordinate pole lying strictly outside a rectangle contributes zero, provided it
does not lie on one of the four supporting boundary lines. -/
theorem rectangleBoundaryIntegral_inv_sub_of_not_mem_interior
    {ρ : ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (ha : ρ.re ≠ a) (hb : ρ.re ≠ b) (hc : ρ.im ≠ c) (hd : ρ.im ≠ d)
    (hout : ¬(a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d)) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - ρ)⁻¹) a b c d = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn _ _ _ _ _ hab hcd
  by_cases har : a < ρ.re
  · by_cases hrb : ρ.re < b
    · by_cases hci : c < ρ.im
      · have hdi : d < ρ.im :=
          lt_of_le_of_ne (not_lt.mp (fun h ↦ hout ⟨har, hrb, hci, h⟩)) hd.symm
        exact differentiableOn_inv_sub_of_im_separated (Or.inl hdi)
      · have hic : ρ.im < c := lt_of_le_of_ne (not_lt.mp hci) hc
        exact differentiableOn_inv_sub_of_im_separated (Or.inr hic)
    · have hbr : b < ρ.re := lt_of_le_of_ne (not_lt.mp hrb) hb.symm
      exact differentiableOn_inv_sub_of_re_separated (Or.inl hbr)
  · have hra : ρ.re < a := lt_of_le_of_ne (not_lt.mp har) ha
    exact differentiableOn_inv_sub_of_re_separated (Or.inr hra)

/-! ## Finite summation of the one-point kernel -/

/-- Boundary integration commutes with a finite sum when every summand is continuous on the
four parametrized sides. -/
theorem rectangleBoundaryIntegral_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ)
    (a b c d : ℝ)
    (hbottom : ∀ i ∈ S, Continuous (fun x : ℝ ↦ F i (x + c * I)))
    (htop : ∀ i ∈ S, Continuous (fun x : ℝ ↦ F i (x + d * I)))
    (hright : ∀ i ∈ S, Continuous (fun y : ℝ ↦ F i (b + y * I)))
    (hleft : ∀ i ∈ S, Continuous (fun y : ℝ ↦ F i (a + y * I))) :
    rectangleBoundaryIntegral (fun z ↦ ∑ i ∈ S, F i z) a b c d =
      ∑ i ∈ S, rectangleBoundaryIntegral (F i) a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_finsetSum (fun i hi ↦ (hbottom i hi).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i hi ↦ (htop i hi).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i hi ↦ (hright i hi).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i hi ↦ (hleft i hi).intervalIntegrable _ _)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A constant complex weight pulls through the rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_const_mul (w : ℂ) (f : ℂ → ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral (fun z ↦ w * f z) a b c d =
      w * rectangleBoundaryIntegral f a b c d := by
  unfold rectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Boundary integration is additive for functions continuous on all four parametrized sides. -/
theorem rectangleBoundaryIntegral_add (f g : ℂ → ℂ) (a b c d : ℝ)
    (hf_bottom : Continuous (fun x : ℝ ↦ f (x + c * I)))
    (hg_bottom : Continuous (fun x : ℝ ↦ g (x + c * I)))
    (hf_top : Continuous (fun x : ℝ ↦ f (x + d * I)))
    (hg_top : Continuous (fun x : ℝ ↦ g (x + d * I)))
    (hf_right : Continuous (fun y : ℝ ↦ f (b + y * I)))
    (hg_right : Continuous (fun y : ℝ ↦ g (b + y * I)))
    (hf_left : Continuous (fun y : ℝ ↦ f (a + y * I)))
    (hg_left : Continuous (fun y : ℝ ↦ g (a + y * I))) :
    rectangleBoundaryIntegral (fun z ↦ f z + g z) a b c d =
      rectangleBoundaryIntegral f a b c d + rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add
      (hf_bottom.intervalIntegrable _ _) (hg_bottom.intervalIntegrable _ _),
    intervalIntegral.integral_add
      (hf_top.intervalIntegrable _ _) (hg_top.intervalIntegrable _ _),
    intervalIntegral.integral_add
      (hf_right.intervalIntegrable _ _) (hg_right.intervalIntegrable _ _),
    intervalIntegral.integral_add
      (hf_left.intervalIntegrable _ _) (hg_left.intervalIntegrable _ _)]
  ring

/-- Additivity with the minimal side-by-side interval-integrability hypotheses. -/
theorem rectangleBoundaryIntegral_add_of_intervalIntegrable (f g : ℂ → ℂ) (a b c d : ℝ)
    (hf_bottom : IntervalIntegrable (fun x : ℝ ↦ f (x + c * I)) volume a b)
    (hg_bottom : IntervalIntegrable (fun x : ℝ ↦ g (x + c * I)) volume a b)
    (hf_top : IntervalIntegrable (fun x : ℝ ↦ f (x + d * I)) volume a b)
    (hg_top : IntervalIntegrable (fun x : ℝ ↦ g (x + d * I)) volume a b)
    (hf_right : IntervalIntegrable (fun y : ℝ ↦ f (b + y * I)) volume c d)
    (hg_right : IntervalIntegrable (fun y : ℝ ↦ g (b + y * I)) volume c d)
    (hf_left : IntervalIntegrable (fun y : ℝ ↦ f (a + y * I)) volume c d)
    (hg_left : IntervalIntegrable (fun y : ℝ ↦ g (a + y * I)) volume c d) :
    rectangleBoundaryIntegral (fun z ↦ f z + g z) a b c d =
      rectangleBoundaryIntegral f a b c d + rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf_bottom hg_bottom,
    intervalIntegral.integral_add hf_top hg_top,
    intervalIntegral.integral_add hf_right hg_right,
    intervalIntegral.integral_add hf_left hg_left]
  ring

/-- **Finite divisor kernel.** Summing the one-point inverse-coordinate kernel over finitely many
interior points, with multiplicity carried by the weights, gives `2πi` times the total weight. -/
theorem rectangleBoundaryIntegral_weighted_divisor
    (S : Finset ℂ) (w : ℂ → ℂ) {a b c d : ℝ}
    (hS : ∀ ρ ∈ S, a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d) :
    rectangleBoundaryIntegral
        (fun z ↦ ∑ ρ ∈ S, w ρ * (z - ρ)⁻¹) a b c d =
      (2 * Real.pi * I) * ∑ ρ ∈ S, w ρ := by
  let F : ℂ → ℂ → ℂ := fun ρ z ↦ w ρ * (z - ρ)⁻¹
  have hbottom : ∀ ρ ∈ S, Continuous (fun x : ℝ ↦ F ρ (x + c * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_horizontal (ne_of_lt (hS ρ hρ).2.2.1))
  have htop : ∀ ρ ∈ S, Continuous (fun x : ℝ ↦ F ρ (x + d * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_horizontal (ne_of_gt (hS ρ hρ).2.2.2))
  have hright : ∀ ρ ∈ S, Continuous (fun y : ℝ ↦ F ρ (b + y * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_vertical (ne_of_gt (hS ρ hρ).2.1))
  have hleft : ∀ ρ ∈ S, Continuous (fun y : ℝ ↦ F ρ (a + y * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_vertical (ne_of_lt (hS ρ hρ).1))
  change rectangleBoundaryIntegral (fun z ↦ ∑ ρ ∈ S, F ρ z) a b c d = _
  rw [rectangleBoundaryIntegral_finset_sum S F a b c d hbottom htop hright hleft]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [show F ρ = fun z ↦ w ρ * (z - ρ)⁻¹ by rfl,
    rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_inv_sub_of_mem_interior
      (hS ρ hρ).1 (hS ρ hρ).2.1 (hS ρ hρ).2.2.1 (hS ρ hρ).2.2.2]
  ring

/-- **Finite divisor kernel with exterior points.** Points strictly inside contribute `2πi`
times their weight; points off the four boundary lines and outside contribute zero. -/
theorem rectangleBoundaryIntegral_weighted_divisor_off_boundary
    (S : Finset ℂ) (w : ℂ → ℂ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hoff : ∀ ρ ∈ S, ρ.re ≠ a ∧ ρ.re ≠ b ∧ ρ.im ≠ c ∧ ρ.im ≠ d) :
    rectangleBoundaryIntegral
        (fun z ↦ ∑ ρ ∈ S, w ρ * (z - ρ)⁻¹) a b c d =
      (2 * Real.pi * I) *
        ∑ ρ ∈ S.filter (fun ρ ↦
          a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d), w ρ := by
  let F : ℂ → ℂ → ℂ := fun ρ z ↦ w ρ * (z - ρ)⁻¹
  have hbottom : ∀ ρ ∈ S, Continuous (fun x : ℝ ↦ F ρ (x + c * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_horizontal (hoff ρ hρ).2.2.1.symm)
  have htop : ∀ ρ ∈ S, Continuous (fun x : ℝ ↦ F ρ (x + d * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_horizontal (hoff ρ hρ).2.2.2.symm)
  have hright : ∀ ρ ∈ S, Continuous (fun y : ℝ ↦ F ρ (b + y * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_vertical (hoff ρ hρ).2.1.symm)
  have hleft : ∀ ρ ∈ S, Continuous (fun y : ℝ ↦ F ρ (a + y * I)) := by
    intro ρ hρ
    exact continuous_const.mul (continuous_inv_vertical (hoff ρ hρ).1.symm)
  change rectangleBoundaryIntegral (fun z ↦ ∑ ρ ∈ S, F ρ z) a b c d = _
  rw [rectangleBoundaryIntegral_finset_sum S F a b c d hbottom htop hright hleft]
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases hin : a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d
  · rw [show F ρ = fun z ↦ w ρ * (z - ρ)⁻¹ by rfl,
      rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_inv_sub_of_mem_interior hin.1 hin.2.1 hin.2.2.1 hin.2.2.2]
    simp [hin]
    ring
  · rw [show F ρ = fun z ↦ w ρ * (z - ρ)⁻¹ by rfl,
      rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_inv_sub_of_not_mem_interior hab hcd
        (hoff ρ hρ).1 (hoff ρ hρ).2.1 (hoff ρ hρ).2.2.1 (hoff ρ hρ).2.2.2 hin,
      mul_zero]
    simp [hin]

/-! ## From a finite divisor product to its logarithmic derivative -/

/-- The finite polynomial carrying prescribed natural multiplicities. -/
def finiteDivisorProduct (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ ρ ∈ S, (z - ρ) ^ m ρ

/-- Off its finite support, the logarithmic derivative of the divisor product is the weighted
sum of inverse coordinates. -/
theorem logDeriv_finiteDivisorProduct (S : Finset ℂ) (m : ℂ → ℕ) {z : ℂ}
    (hz : ∀ ρ ∈ S, z ≠ ρ) :
    logDeriv (finiteDivisorProduct S m) z =
      ∑ ρ ∈ S, (m ρ : ℂ) * (z - ρ)⁻¹ := by
  unfold finiteDivisorProduct
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w : ℂ ↦ w - ρ) (by fun_prop)]
    simp [logDeriv_apply, hz ρ hρ]
  · intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))
  · intro ρ hρ
    fun_prop

/-- A nonvanishing analytic factor contributes zero logarithmic-derivative boundary integral. -/
theorem rectangleBoundaryIntegral_logDeriv_eq_zero
    (g : ℂ → ℂ) {a b c d : ℝ}
    (hg : ∀ z ∈ Icc a b ×ℂ Icc c d, AnalyticAt ℂ g z)
    (hne : ∀ z ∈ Icc a b ×ℂ Icc c d, g z ≠ 0)
    (hab : a ≤ b) (hcd : c ≤ d) :
    rectangleBoundaryIntegral (logDeriv g) a b c d = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn _ _ _ _ _ hab hcd
  intro z hz
  have ha : AnalyticAt ℂ (logDeriv g) z := by
    simpa [logDeriv] using (hg z hz).deriv.div (hg z hz) (hne z hz)
  exact ha.differentiableAt.differentiableWithinAt

/-- Boundary integration of the finite divisor product is exactly the summed kernel. -/
theorem rectangleBoundaryIntegral_logDeriv_finiteDivisorProduct
    (S : Finset ℂ) (m : ℂ → ℕ) {a b c d : ℝ}
    (hS : ∀ ρ ∈ S, a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d) :
    rectangleBoundaryIntegral (logDeriv (finiteDivisorProduct S m)) a b c d =
      (2 * Real.pi * I) * ∑ ρ ∈ S, (m ρ : ℂ) := by
  have hkernel := rectangleBoundaryIntegral_weighted_divisor
    S (fun ρ ↦ (m ρ : ℂ)) hS
  have heq :
      rectangleBoundaryIntegral (logDeriv (finiteDivisorProduct S m)) a b c d =
        rectangleBoundaryIntegral
          (fun z ↦ ∑ ρ ∈ S, (m ρ : ℂ) * (z - ρ)⁻¹) a b c d := by
    have hbottom :
        (∫ x in a..b, logDeriv (finiteDivisorProduct S m) (x + c * I)) =
          ∫ x in a..b, ∑ ρ ∈ S, (m ρ : ℂ) * (x + c * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply logDeriv_finiteDivisorProduct
      intro ρ hρ heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [(hS ρ hρ).2.2.1]
    have htop :
        (∫ x in a..b, logDeriv (finiteDivisorProduct S m) (x + d * I)) =
          ∫ x in a..b, ∑ ρ ∈ S, (m ρ : ℂ) * (x + d * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply logDeriv_finiteDivisorProduct
      intro ρ hρ heq
      have him := congrArg Complex.im heq
      simp at him
      linarith [(hS ρ hρ).2.2.2]
    have hright :
        (∫ y in c..d, logDeriv (finiteDivisorProduct S m) (b + y * I)) =
          ∫ y in c..d, ∑ ρ ∈ S, (m ρ : ℂ) * (b + y * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply logDeriv_finiteDivisorProduct
      intro ρ hρ heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith [(hS ρ hρ).2.1]
    have hleft :
        (∫ y in c..d, logDeriv (finiteDivisorProduct S m) (a + y * I)) =
          ∫ y in c..d, ∑ ρ ∈ S, (m ρ : ℂ) * (a + y * I - ρ)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply logDeriv_finiteDivisorProduct
      intro ρ hρ heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith [(hS ρ hρ).1]
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  rw [heq]
  exact hkernel

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_inv_centered_square
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_inv_square
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_inv_sub_of_mem_interior
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_finset_sum
#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_weighted_divisor
