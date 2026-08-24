import RequestProject.DVPLittlewoodEdge
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Littlewood box: the vertical transport of `log‖ζ‖`

The branch-free vertical FTC: on any zero-free vertical segment,
`∫₀ᵀ Im(ζ'/ζ)(u+it) dt = log‖ζ(u)‖ − log‖ζ(u+iT)‖`.  The derivative
`d/dt log‖ζ(u+it)‖ = −Im(ζ'/ζ)` is computed through `‖·‖²` (no logarithm
branch is ever chosen), so the identity applies at EVERY zero-free abscissa —
the form Fubini needs on the box, where `u ≤ 1` segments are zero-free for
a.e. `u`.  Plus the full complex-log edge bound `‖Log ζ‖ ≤ 3·2^{−σ}` (σ ≥ 3),
which controls the right edge's argument as well as its modulus.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The pointwise value identity behind the vertical clock rate:
`(1/2)·(‖w‖²)⁻¹·2⟪w, d·I⟫_ℝ = −Im(d/w)` for `w ≠ 0`. -/
theorem inner_I_div_im {w d : ℂ} (hw : w ≠ 0) :
    (1/2 : ℝ) * ((‖w‖ ^ 2)⁻¹ * (2 * (inner (𝕜 := ℝ) w (d * Complex.I) : ℝ)))
      = -((d / w).im) := by
  have hnsq : Complex.normSq w ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    have h : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  rw [show ‖w‖ ^ 2 = Complex.normSq w from (Complex.normSq_eq_norm_sq _).symm]
  simp only [Complex.inner, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

/-- **The vertical clock rate of `log‖ζ‖`**: at any point off the pole with
`ζ ≠ 0`, `d/dt log‖ζ(u+it)‖ = −Im(ζ'/ζ)(u+it)`.  Branch-free (computed via
`‖·‖²`). -/
theorem hasDerivAt_log_norm_zeta_vertical {u t : ℝ}
    (hs1 : (u:ℂ) + (t:ℂ) * Complex.I ≠ 1)
    (hs0 : riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun τ : ℝ => Real.log ‖riemannZeta ((u:ℂ) + (τ:ℂ) * Complex.I)‖)
      (-((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
          / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im) t := by
  set s : ℂ := (u:ℂ) + (t:ℂ) * Complex.I with hsdef
  set F : ℝ → ℂ := fun τ => riemannZeta ((u:ℂ) + (τ:ℂ) * Complex.I) with hFdef
  set d : ℂ := deriv riemannZeta s with hddef
  have haff : HasDerivAt (fun τ : ℝ => (u:ℂ) + (τ:ℂ) * Complex.I) Complex.I t := by
    have ht : HasDerivAt (fun τ : ℝ => ((τ:ℝ):ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    simpa using (ht.mul_const Complex.I).const_add (u:ℂ)
  have hF : HasDerivAt F (d * Complex.I) t :=
    (differentiableAt_riemannZeta hs1).hasDerivAt.comp t haff
  have hFt0 : F t ≠ 0 := hs0
  have hnorm : (0:ℝ) < ‖F t‖ := norm_pos_iff.mpr hFt0
  have hsqpos : (0:ℝ) < ‖F t‖ ^ 2 := by positivity
  have hsq := hF.norm_sq
  have hlog2 := (Real.hasDerivAt_log (ne_of_gt hsqpos)).comp t hsq
  have hhalf := hlog2.const_mul (1/2 : ℝ)
  have hfun : (fun τ => (1/2 : ℝ) * Real.log (‖F τ‖ ^ 2))
      = fun τ => Real.log ‖F τ‖ := by
    funext τ
    rw [Real.log_pow]
    push_cast
    ring
  simp only [Function.comp_def] at hhalf
  rw [hfun] at hhalf
  exact hhalf.congr_deriv (inner_I_div_im hFt0)

/-- **The vertical FTC for `log‖ζ‖`** on a zero-free segment:
`∫₀ᵀ Im(ζ'/ζ)(u+it) dt = log‖ζ(u+0i)‖ − log‖ζ(u+iT)‖`. -/
theorem vertical_im_logDeriv_integral {u T : ℝ} (hT : 0 ≤ T)
    (hne : ∀ t ∈ Set.Icc (0:ℝ) T,
      riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (h1 : ∀ t ∈ Set.Icc (0:ℝ) T, ((u:ℂ) + (t:ℂ) * Complex.I) ≠ 1) :
    ∫ t in (0:ℝ)..T,
        ((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
          / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im
      = Real.log ‖riemannZeta ((u:ℂ) + ((0:ℝ):ℂ) * Complex.I)‖
        - Real.log ‖riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I)‖ := by
  have haffc : Continuous (fun t : ℝ => (u:ℂ) + (t:ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun x hx => (differentiableAt_riemannZeta hx).differentiableWithinAt
  have hzc : ContinuousOn
      (fun t : ℝ => riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)) (Set.Icc 0 T) := by
    intro t ht
    have hc : ContinuousAt (riemannZeta ∘ fun τ : ℝ => (u:ℂ) + (τ:ℂ) * Complex.I) t :=
      ContinuousAt.comp (differentiableAt_riemannZeta (h1 t ht)).continuousAt
        haffc.continuousAt
    exact hc.continuousWithinAt
  have hdc : ContinuousOn
      (fun t : ℝ => deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
      (Set.Icc 0 T) := by
    intro t ht
    have hana : AnalyticAt ℂ riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I) :=
      hdiffOn.analyticAt (isOpen_ne.mem_nhds (h1 t ht))
    have hc : ContinuousAt
        (deriv riemannZeta ∘ fun τ : ℝ => (u:ℂ) + (τ:ℂ) * Complex.I) t :=
      ContinuousAt.comp hana.deriv.continuousAt haffc.continuousAt
    exact hc.continuousWithinAt
  have hquot : ContinuousOn (fun t : ℝ =>
      (deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
        / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)) (Set.Icc 0 T) :=
    hdc.div hzc hne
  have hint : IntervalIntegrable (fun t : ℝ =>
      -((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
        / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im)
      MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact (Complex.continuous_im.comp_continuousOn hquot).neg
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun τ : ℝ => Real.log ‖riemannZeta ((u:ℂ) + (τ:ℂ) * Complex.I)‖)
        (-((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
            / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im) t := by
    rw [Set.uIcc_of_le hT]
    intro t ht
    exact hasDerivAt_log_norm_zeta_vertical (h1 t ht) (hne t ht)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hftc
  linarith [hftc]

/-- The zero-free hypotheses are automatic for `u > 1` (Euler product). -/
theorem vertical_im_logDeriv_integral_gt_one {u T : ℝ} (hu : 1 < u) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T,
        ((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
          / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im
      = Real.log ‖riemannZeta ((u:ℂ) + ((0:ℝ):ℂ) * Complex.I)‖
        - Real.log ‖riemannZeta ((u:ℂ) + (T:ℂ) * Complex.I)‖ := by
  apply vertical_im_logDeriv_integral hT
  · intro t _
    apply riemannZeta_ne_zero_of_one_lt_re
    simpa using hu
  · intro t _ h
    have hre : ((u:ℂ) + (t:ℂ) * Complex.I).re = 1 := by rw [h]; simp
    simp at hre
    linarith

/-- **The full complex-log edge bound**: `‖Log ζ(z)‖ ≤ 3·2^{−σ}` for
`σ = Re z ≥ 3` — modulus AND argument of the right edge, in one norm. -/
theorem norm_log_zeta_edge {z : ℂ} (hz : 3 ≤ z.re) :
    ‖Complex.log (riemannZeta z)‖ ≤ 3 * (2:ℝ) ^ (-z.re) := by
  have hz1 : 1 < z.re := by linarith
  have hw := zeta_sub_one_norm_le hz1
  have hrp : (0:ℝ) < (2:ℝ) ^ (-z.re) := by positivity
  have h2σ' : (2:ℝ) ^ (1 - z.re) = 2 * (2:ℝ) ^ (-z.re) := by
    rw [show (1 - z.re) = 1 + (-z.re) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
  have hεle : ‖riemannZeta z - 1‖ ≤ 2 * (2:ℝ) ^ (-z.re) := by
    have hfrac : (2:ℝ) ^ (1 - z.re) / (z.re - 1) ≤ (2:ℝ) ^ (-z.re) := by
      rw [h2σ', div_le_iff₀ (by linarith : (0:ℝ) < z.re - 1)]
      nlinarith [hrp]
    linarith [hw]
  have hhalf : ‖riemannZeta z - 1‖ ≤ 1/2 := by
    have hmono : (2:ℝ) ^ (-z.re) ≤ (2:ℝ) ^ (-(3:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h8 : (2:ℝ) ^ (-(3:ℝ)) = 1/8 := by
      rw [show (-(3:ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    have := hmono.trans h8.le
    linarith
  have heq : riemannZeta z = 1 + (riemannZeta z - 1) := by ring
  calc ‖Complex.log (riemannZeta z)‖
      = ‖Complex.log (1 + (riemannZeta z - 1))‖ := by rw [← heq]
    _ ≤ (3/2) * ‖riemannZeta z - 1‖ :=
        Complex.norm_log_one_add_half_le_self hhalf
    _ ≤ (3/2) * (2 * (2:ℝ) ^ (-z.re)) :=
        mul_le_mul_of_nonneg_left hεle (by norm_num)
    _ = 3 * (2:ℝ) ^ (-z.re) := by ring

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.inner_I_div_im
#print axioms CriticalLinePhasor.DVP.hasDerivAt_log_norm_zeta_vertical
#print axioms CriticalLinePhasor.DVP.vertical_im_logDeriv_integral
#print axioms CriticalLinePhasor.DVP.vertical_im_logDeriv_integral_gt_one
#print axioms CriticalLinePhasor.DVP.norm_log_zeta_edge
end AxiomAudit
