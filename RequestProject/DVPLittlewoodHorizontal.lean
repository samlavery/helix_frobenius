import RequestProject.DVPLittlewoodVertical

/-!
# Littlewood box: horizontal transport and log-distance integrals

The general branch-free clock rate `d/dt log‖F t‖ = Re(F'/F t)` for any
differentiable path `F : ℝ → ℂ` off zeros — the vertical case (395) is the
instance `F' = iζ'`, the horizontal case is `F' = ζ'`, and the affine case
`F = s − ρ`, `F' = 1` gives the per-zero log-distance integrals that the
top-edge lower bound consumes against the compiled partial fraction.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The general pointwise value identity:
`(1/2)·(‖w‖²)⁻¹·2⟪w, v⟫_ℝ = Re(v/w)` for `w ≠ 0`. -/
theorem inner_div_re {w v : ℂ} (hw : w ≠ 0) :
    (1/2 : ℝ) * ((‖w‖ ^ 2)⁻¹ * (2 * (inner (𝕜 := ℝ) w v : ℝ)))
      = ((v / w).re) := by
  have hnsq : Complex.normSq w ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    have h : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  rw [show ‖w‖ ^ 2 = Complex.normSq w from (Complex.normSq_eq_norm_sq _).symm]
  simp only [Complex.inner, Complex.div_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  field_simp
  ring

/-- **The general branch-free clock rate**: for any path `F : ℝ → ℂ`
differentiable at `t` with `F t ≠ 0`,
`d/dt log‖F t‖ = Re(F'(t)/F t)`. -/
theorem hasDerivAt_log_norm {F : ℝ → ℂ} {F' : ℂ} {t : ℝ}
    (hF : HasDerivAt F F' t) (h0 : F t ≠ 0) :
    HasDerivAt (fun τ => Real.log ‖F τ‖) ((F' / F t).re) t := by
  have hnorm : (0:ℝ) < ‖F t‖ := norm_pos_iff.mpr h0
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
  exact hhalf.congr_deriv (inner_div_re h0)

/-- The horizontal clock rate for ζ:
`d/dx log‖ζ(x+iT)‖ = Re(ζ'/ζ)(x+iT)` off zeros and the pole. -/
theorem hasDerivAt_log_norm_zeta_horizontal {T x : ℝ}
    (hs1 : (x:ℂ) + (T:ℂ) * Complex.I ≠ 1)
    (hs0 : riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun ξ : ℝ => Real.log ‖riemannZeta ((ξ:ℂ) + (T:ℂ) * Complex.I)‖)
      (((deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I))
        / riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)).re) x := by
  have haff : HasDerivAt (fun ξ : ℝ => (ξ:ℂ) + (T:ℂ) * Complex.I) 1 x := by
    have ht : HasDerivAt (fun ξ : ℝ => ((ξ:ℝ):ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa using ht.add_const ((T:ℂ) * Complex.I)
  have hF : HasDerivAt (fun ξ : ℝ => riemannZeta ((ξ:ℂ) + (T:ℂ) * Complex.I))
      (deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)) x := by
    have h := (differentiableAt_riemannZeta hs1).hasDerivAt.comp x haff
    simpa [Function.comp_def] using h
  exact hasDerivAt_log_norm hF hs0

/-- **The horizontal FTC for `log‖ζ‖`** on a zero-free horizontal segment:
`∫ₐᵇ Re(ζ'/ζ)(x+iT) dx = log‖ζ(b+iT)‖ − log‖ζ(a+iT)‖`. -/
theorem horizontal_re_logDeriv_integral {T a b : ℝ} (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b,
      riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I) ≠ 0)
    (h1 : ∀ x ∈ Set.Icc a b, (x:ℂ) + (T:ℂ) * Complex.I ≠ 1) :
    ∫ x in a..b,
        ((deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I))
          / riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)).re
      = Real.log ‖riemannZeta ((b:ℂ) + (T:ℂ) * Complex.I)‖
        - Real.log ‖riemannZeta ((a:ℂ) + (T:ℂ) * Complex.I)‖ := by
  have haffc : Continuous (fun x : ℝ => (x:ℂ) + (T:ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hzc : ContinuousOn
      (fun x : ℝ => riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)) (Set.Icc a b) := by
    intro x hx
    have hc : ContinuousAt (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (T:ℂ) * Complex.I) x :=
      ContinuousAt.comp (differentiableAt_riemannZeta (h1 x hx)).continuousAt
        haffc.continuousAt
    exact hc.continuousWithinAt
  have hdc : ContinuousOn
      (fun x : ℝ => deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I))
      (Set.Icc a b) := by
    intro x hx
    have hana : AnalyticAt ℂ riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I) :=
      hdiffOn.analyticAt (isOpen_ne.mem_nhds (h1 x hx))
    have hc : ContinuousAt
        (deriv riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (T:ℂ) * Complex.I) x :=
      ContinuousAt.comp hana.deriv.continuousAt haffc.continuousAt
    exact hc.continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ =>
      ((deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I))
        / riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)).re)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact Complex.continuous_re.comp_continuousOn (hdc.div hzc hne)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun ξ : ℝ => Real.log ‖riemannZeta ((ξ:ℂ) + (T:ℂ) * Complex.I)‖)
        (((deriv riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I))
          / riemannZeta ((x:ℂ) + (T:ℂ) * Complex.I)).re) x := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact hasDerivAt_log_norm_zeta_horizontal (h1 x hx) (hne x hx)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **The per-zero log-distance integral**: on a horizontal segment avoiding
`ρ`, `∫ₐᵇ Re(1/(x+iT−ρ)) dx = log|b+iT−ρ| − log|a+iT−ρ|`.  The elementary
integral the partial-fraction lower bound sums over the local zero window. -/
theorem horizontal_log_dist_integral {T a b : ℝ} {ρ : ℂ} (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b, (x:ℂ) + (T:ℂ) * Complex.I - ρ ≠ 0) :
    ∫ x in a..b, ((1 : ℂ) / ((x:ℂ) + (T:ℂ) * Complex.I - ρ)).re
      = Real.log ‖(b:ℂ) + (T:ℂ) * Complex.I - ρ‖
        - Real.log ‖(a:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
  have hFd : ∀ x : ℝ,
      HasDerivAt (fun ξ : ℝ => (ξ:ℂ) + (T:ℂ) * Complex.I - ρ) 1 x := by
    intro x
    have ht : HasDerivAt (fun ξ : ℝ => ((ξ:ℝ):ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa using (ht.add_const ((T:ℂ) * Complex.I)).sub_const ρ
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun ξ : ℝ => Real.log ‖(ξ:ℂ) + (T:ℂ) * Complex.I - ρ‖)
        (((1:ℂ) / ((x:ℂ) + (T:ℂ) * Complex.I - ρ)).re) x := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact hasDerivAt_log_norm (hFd x) (hne x hx)
  have hint : IntervalIntegrable (fun x : ℝ =>
      ((1:ℂ) / ((x:ℂ) + (T:ℂ) * Complex.I - ρ)).re)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have hc : ContinuousOn (fun x : ℝ => (x:ℂ) + (T:ℂ) * Complex.I - ρ)
        (Set.Icc a b) :=
      ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
    exact Complex.continuous_re.comp_continuousOn (continuousOn_const.div hc hne)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.inner_div_re
#print axioms CriticalLinePhasor.DVP.hasDerivAt_log_norm
#print axioms CriticalLinePhasor.DVP.hasDerivAt_log_norm_zeta_horizontal
#print axioms CriticalLinePhasor.DVP.horizontal_re_logDeriv_integral
#print axioms CriticalLinePhasor.DVP.horizontal_log_dist_integral
end AxiomAudit
