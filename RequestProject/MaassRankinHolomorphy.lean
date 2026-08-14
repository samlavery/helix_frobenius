import RequestProject.MaassArchimedeanPositivity
import RequestProject.HolomorphicUnderIntegral

/-!
# The Maass Rankin--Selberg integral is holomorphic on its half-plane

First half of the continuation: before the Eisenstein poles can be transferred, the geometric side
has to be a holomorphic function of `s` where it converges.

The corpus's `differentiableAt_integral_of_dominated_holo` is stated for an arbitrary measure
space, so nothing new is needed there.  The only content is the dominating function, and the
harmonic reading makes it immediate: `‖‖u‖²·y^s‖ = ‖u‖²·y^{σ}`, and on a ball of radius `R` about
`s₀` the exponent `σ` ranges over `(σ₀-R, σ₀+R)`.  A power of the height is monotone in the
exponent in one direction above `y = 1` and the other direction below it, so

  `y^σ ≤ y^{σ₀+R} + y^{σ₀-R}`

on the whole ray — the two endpoints of the ball dominate the interior, one at each end of the
strip.  Both are integrable by `maassRsIntegrand_integrableOn_strip` at real exponents, provided
`σ₀ - R > 1`; taking `R = (σ₀-1)/2` arranges that.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Metric
open scoped Real MatrixGroups Pointwise Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- The Petersson density against a real power of the height is strip-integrable above one. -/
lemma maassP_mul_rpow_integrableOn_strip (M : GenuineMaassCuspForm3D) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun z : ℍ => maassP M z * z.im ^ σ) strip (volume : Measure ℍ) := by
  have h := (maassRsIntegrand_integrableOn_strip M (s := (σ : ℂ)) (by simpa using hσ)).norm
  refine h.congr ?_
  filter_upwards with z
  rw [norm_maassRsIntegrand]
  congr 1

/-- A fixed positive base gives an entire exponential. -/
lemma differentiable_const_cpow {a : ℂ} (ha : a ≠ 0) :
    Differentiable ℂ (fun s : ℂ => a ^ s) := by
  have heq : (fun s : ℂ => a ^ s) = fun s : ℂ => Complex.exp (Complex.log a * s) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero ha]
  rw [heq]
  exact Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)

/-- **The Rankin--Selberg integral is holomorphic on `Re s > 1`.** -/
theorem maass_strip_side_differentiableAt (M : GenuineMaassCuspForm3D) {s₀ : ℂ}
    (hs₀ : 1 < s₀.re) :
    DifferentiableAt ℂ
      (fun s => ∫ z in strip, maassRsIntegrand M s z ∂(volume : Measure ℍ)) s₀ := by
  set R : ℝ := (s₀.re - 1) / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hlo : 1 < s₀.re - R := by rw [hR]; linarith
  have hhi : 1 < s₀.re + R := by linarith
  set bound : ℍ → ℝ := fun z =>
    maassP M z * z.im ^ (s₀.re + R) + maassP M z * z.im ^ (s₀.re - R) with hbound
  have hbint : Integrable bound ((volume : Measure ℍ).restrict strip) :=
    (maassP_mul_rpow_integrableOn_strip M hhi).add
      (maassP_mul_rpow_integrableOn_strip M hlo)
  refine differentiableAt_integral_of_dominated_holo
    (fun s z => maassRsIntegrand M s z) bound hRpos ?_ ?_ ?_ hbint
  · exact fun s _ => (continuous_maassRsIntegrand' M s).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    have hne : ((z.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
    exact (((differentiable_const_cpow hne).const_mul
      ((maassP M z : ℝ) : ℂ)).differentiableOn)
  · refine Eventually.of_forall fun z s hs => ?_
    have hy0 : (0:ℝ) < z.im := z.im_pos
    have hdist : ‖s - s₀‖ < R := by
      have := mem_ball.mp hs
      rwa [Complex.dist_eq] at this
    have hre : |s.re - s₀.re| < R := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      simp only [Complex.sub_re] at h1
      linarith
    have hlt : s₀.re - R < s.re ∧ s.re < s₀.re + R := by
      constructor <;> [linarith [neg_lt_of_abs_lt hre]; linarith [lt_of_abs_lt hre]]
    rw [norm_maassRsIntegrand, hbound]
    have hP : 0 ≤ maassP M z := maassP_nonneg M z
    have hpow : z.im ^ s.re ≤ z.im ^ (s₀.re + R) + z.im ^ (s₀.re - R) := by
      rcases le_or_gt 1 z.im with hz | hz
      · have h1 : z.im ^ s.re ≤ z.im ^ (s₀.re + R) :=
          Real.rpow_le_rpow_of_exponent_le hz hlt.2.le
        have h2 : (0:ℝ) ≤ z.im ^ (s₀.re - R) := Real.rpow_nonneg hy0.le _
        linarith
      · have h1 : z.im ^ s.re ≤ z.im ^ (s₀.re - R) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hz.le hlt.1.le
        have h2 : (0:ℝ) ≤ z.im ^ (s₀.re + R) := Real.rpow_nonneg hy0.le _
        linarith
    calc maassP M z * z.im ^ s.re
        ≤ maassP M z * (z.im ^ (s₀.re + R) + z.im ^ (s₀.re - R)) :=
          mul_le_mul_of_nonneg_left hpow hP
      _ = maassP M z * z.im ^ (s₀.re + R) + maassP M z * z.im ^ (s₀.re - R) := by ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_mul_rpow_integrableOn_strip
#print axioms CriticalLinePhasor.Unfolding.maass_strip_side_differentiableAt
