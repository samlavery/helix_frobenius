import RequestProject.DVPTopEdgeLower

/-!
# The top edge's `σ ≥ 2` tail: absolutely bounded by a constant

DC first: `∫ₐᵇ 2^{−x} dx = (2^{−a} − 2^{−b})/log 2` computed EXACTLY, then
the 394 pointwise control `|log‖ζ‖| ≤ 12·2^{−σ}` integrates to
`∫₂^{σ₀} |log‖ζ(x+iT)‖| dx ≤ 6` — uniformly in `σ₀` and in the height.
With 399 (`≥ −800 log T` on `[1/2,2]`) and 392 (`≤ 10 log T`), every piece
of the box's top edge is now two-sided.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The exact primitive: `∫ₐᵇ 2^{−x} dx = (2^{−a} − 2^{−b})/log 2`. -/
theorem integral_two_rpow_neg (a b : ℝ) :
    ∫ x in a..b, (2:ℝ) ^ (-x)
      = ((2:ℝ) ^ (-a) - (2:ℝ) ^ (-b)) / Real.log 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => -(2:ℝ) ^ (-y) / Real.log 2)
        ((2:ℝ) ^ (-x)) x := by
    intro x
    have hexp : ∀ y : ℝ, (2:ℝ) ^ (-y) = Real.exp (Real.log 2 * (-y)) := by
      intro y
      rw [Real.rpow_def_of_pos (by norm_num)]
    have hinner : HasDerivAt (fun y : ℝ => Real.log 2 * (-y))
        (-Real.log 2) x := by
      simpa using (hasDerivAt_id x).neg.const_mul (Real.log 2)
    have hcomp : HasDerivAt (fun y : ℝ => Real.exp (Real.log 2 * (-y)))
        (Real.exp (Real.log 2 * (-x)) * (-Real.log 2)) x :=
      (Real.hasDerivAt_exp _).comp x hinner
    have hdiv : HasDerivAt
        (fun y : ℝ => -(Real.exp (Real.log 2 * (-y))) / Real.log 2)
        (-(Real.exp (Real.log 2 * (-x)) * (-Real.log 2)) / Real.log 2) x :=
      (hcomp.neg).div_const _
    have hval : -(Real.exp (Real.log 2 * (-x)) * (-Real.log 2)) / Real.log 2
        = (2:ℝ) ^ (-x) := by
      rw [← hexp x]
      field_simp
    have hfun : (fun y : ℝ => -(Real.exp (Real.log 2 * (-y))) / Real.log 2)
        = fun y : ℝ => -(2:ℝ) ^ (-y) / Real.log 2 := by
      funext y
      rw [← hexp y]
    rw [hfun, hval] at hdiv
    exact hdiv
  have hint : IntervalIntegrable (fun x : ℝ => (2:ℝ) ^ (-x))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have : (fun x : ℝ => (2:ℝ) ^ (-x))
        = fun x : ℝ => Real.exp (Real.log 2 * (-x)) := by
      funext x
      rw [Real.rpow_def_of_pos (by norm_num)]
    rw [this]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint
  rw [hftc]
  field_simp
  ring

/-- **The tail-edge absolute bound**: `∫₂^{σ₀} |log‖ζ(x+iT)‖| dx ≤ 6`
uniformly in `σ₀ ≥ 2` and `|T| ≥ 2`. -/
theorem zeta_tail_edge_abs_le {T σ₀ : ℝ} (hT : 2 ≤ |T|) (hσ : 2 ≤ σ₀) :
    ∫ x in (2:ℝ)..σ₀,
        |Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)‖| ≤ 6 := by
  have hT0 : T ≠ 0 := by
    intro h
    rw [h] at hT
    simp at hT
    linarith
  -- pointwise: |log‖ζ‖| ≤ 12·2^{−x} on the segment
  have hpt : ∀ x ∈ Set.Icc (2:ℝ) σ₀,
      |Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)‖|
        ≤ 12 * (2:ℝ) ^ (-x) := by
    intro x hx
    have hre : ((x:ℂ) + (T:ℂ) * Complex.I).re = x := by simp
    have him : ((x:ℂ) + (T:ℂ) * Complex.I).im = T := by simp
    have h := abs_log_norm_zeta_edge
      (z := (x:ℂ) + (T:ℂ) * Complex.I) (by rw [hre]; exact hx.1)
    rwa [hre] at h
  -- integrability of the LHS: continuous on the segment
  have hint_lhs : IntervalIntegrable
      (fun x : ℝ => |Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)‖|)
      MeasureTheory.volume 2 σ₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ]
    apply ContinuousOn.abs
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hne1 : (x:ℂ) + (T:ℂ) * Complex.I ≠ 1 := by
        intro h1
        apply hT0
        have := congrArg Complex.im h1
        simpa using this
      have hc' : ContinuousAt
          (riemannZeta ∘ fun τ : ℝ => (τ:ℂ) + (T:ℂ) * Complex.I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc'.continuousWithinAt
    · intro x hx
      apply norm_ne_zero_iff.mpr
      apply riemannZeta_ne_zero_of_one_lt_re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      nlinarith [hx.1]
  have hint_rhs : IntervalIntegrable (fun x : ℝ => 12 * (2:ℝ) ^ (-x))
      MeasureTheory.volume 2 σ₀ := by
    apply Continuous.intervalIntegrable
    have : (fun x : ℝ => (2:ℝ) ^ (-x))
        = fun x : ℝ => Real.exp (Real.log 2 * (-x)) := by
      funext x
      rw [Real.rpow_def_of_pos (by norm_num)]
    have hc : Continuous (fun x : ℝ => (2:ℝ) ^ (-x)) := by
      rw [this]
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    exact continuous_const.mul hc
  have hmono := intervalIntegral.integral_mono_on hσ hint_lhs hint_rhs hpt
  -- the exact majorant integral
  have hmaj : ∫ x in (2:ℝ)..σ₀, 12 * (2:ℝ) ^ (-x)
      = 12 * (((2:ℝ) ^ (-(2:ℝ)) - (2:ℝ) ^ (-σ₀)) / Real.log 2) := by
    rw [intervalIntegral.integral_const_mul, integral_two_rpow_neg]
  have hquarter : (2:ℝ) ^ (-(2:ℝ)) = 1/4 := by
    rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hσ0 : (0:ℝ) < (2:ℝ) ^ (-σ₀) := by positivity
  have hlog2_half : (1/2 : ℝ) ≤ Real.log 2 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have hsq : Real.exp (1/2) ^ (2:ℕ) = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2 : ℝ), hsq]
  have hlog2 : (0:ℝ) < Real.log 2 := by linarith
  calc ∫ x in (2:ℝ)..σ₀,
        |Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)‖|
      ≤ ∫ x in (2:ℝ)..σ₀, 12 * (2:ℝ) ^ (-x) := hmono
    _ = 12 * (((2:ℝ) ^ (-(2:ℝ)) - (2:ℝ) ^ (-σ₀)) / Real.log 2) := hmaj
    _ ≤ 6 := by
        rw [hquarter]
        have h1 : ((1:ℝ)/4 - (2:ℝ) ^ (-σ₀)) / Real.log 2 ≤ 1/2 := by
          rw [div_le_iff₀ hlog2]
          linarith [hσ0, hlog2_half]
        linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.integral_two_rpow_neg
#print axioms CriticalLinePhasor.DVP.zeta_tail_edge_abs_le
end AxiomAudit
