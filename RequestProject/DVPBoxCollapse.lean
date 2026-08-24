import RequestProject.DVPBoxFubini

/-!
# The box collapse: double integral → edge log-integrals

The box double integral of `Im(ζ'/ζ)` collapses to the difference of the
two horizontal edge integrals of `log‖ζ‖`: swap (403), then the vertical
FTC (395, generalized off `0`-based intervals) at almost every abscissa —
the bad abscissae are the real parts of the finitely many zeros in the box.
-/

open Metric Complex MeasureTheory Topology Filter
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Zeros of ζ in a pole-free compact are finite (isolation + accumulation). -/
theorem zeta_zeros_finite_in_compact {K : Set ℂ} (hK : IsCompact K)
    (h1 : (1:ℂ) ∉ K) : {z ∈ K | riemannZeta z = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨z₀, hz₀K, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK
    (fun z hz => hz.1)
  have hz₀1 : z₀ ≠ 1 := by
    rintro rfl
    exact h1 hz₀K
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hana : AnalyticAt ℂ riemannZeta z₀ :=
    hdiffOn.analyticAt (isOpen_ne.mem_nhds hz₀1)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, riemannZeta z = 0 := by
    have h := accPt_iff_frequently_nhdsNE.mp hacc
    exact h.mono fun z hz => hz.2
  rcases hana.eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exact zeta_not_eventually_zero hz₀1 hev
  · obtain ⟨z, h1', h2'⟩ := (hfreq.and_eventually hev).exists
    exact h2' h1'

/-- The vertical FTC on a general zero-free segment (395 off `0`-based). -/
theorem vertical_im_logDeriv_integral' {u t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hne : ∀ t ∈ Set.Icc t₀ t₁,
      riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (h1 : ∀ t ∈ Set.Icc t₀ t₁, ((u:ℂ) + (t:ℂ) * Complex.I) ≠ 1) :
    ∫ t in t₀..t₁,
        ((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
          / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im
      = Real.log ‖riemannZeta ((u:ℂ) + (t₀:ℂ) * Complex.I)‖
        - Real.log ‖riemannZeta ((u:ℂ) + (t₁:ℂ) * Complex.I)‖ := by
  have haffc : Continuous (fun t : ℝ => (u:ℂ) + (t:ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hzc : ContinuousOn
      (fun t : ℝ => riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
      (Set.Icc t₀ t₁) := by
    intro t htm
    have hc : ContinuousAt (riemannZeta ∘ fun τ : ℝ => (u:ℂ) + (τ:ℂ) * Complex.I) t :=
      ContinuousAt.comp (differentiableAt_riemannZeta (h1 t htm)).continuousAt
        haffc.continuousAt
    exact hc.continuousWithinAt
  have hdc : ContinuousOn
      (fun t : ℝ => deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
      (Set.Icc t₀ t₁) := by
    intro t htm
    have hana : AnalyticAt ℂ riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I) :=
      hdiffOn.analyticAt (isOpen_ne.mem_nhds (h1 t htm))
    have hc : ContinuousAt
        (deriv riemannZeta ∘ fun τ : ℝ => (u:ℂ) + (τ:ℂ) * Complex.I) t :=
      ContinuousAt.comp hana.deriv.continuousAt haffc.continuousAt
    exact hc.continuousWithinAt
  have hquot : ContinuousOn (fun t : ℝ =>
      (deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
        / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)) (Set.Icc t₀ t₁) :=
    hdc.div hzc hne
  have hint : IntervalIntegrable (fun t : ℝ =>
      -((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
        / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im)
      MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    exact (Complex.continuous_im.comp_continuousOn hquot).neg
  have hderiv : ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun τ : ℝ => Real.log ‖riemannZeta ((u:ℂ) + (τ:ℂ) * Complex.I)‖)
        (-((deriv riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I))
            / riemannZeta ((u:ℂ) + (t:ℂ) * Complex.I)).im) t := by
    rw [Set.uIcc_of_le ht]
    intro t htm
    exact hasDerivAt_log_norm_zeta_vertical (h1 t htm) (hne t htm)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hftc
  linarith [hftc]

/-- **The box collapse**: the double integral of `Im(ζ'/ζ)` over the box
equals the bottom-edge minus top-edge `log‖ζ‖` integrals. -/
theorem box_vertical_collapse {a b t₀ t₁ : ℝ} (hab : a ≤ b) (ht : t₀ ≤ t₁)
    (ht₀ : 0 < t₀) :
    ∫ t in t₀..t₁, (∫ x in a..b,
        ((deriv riemannZeta ((x:ℝ) + (t:ℝ) * Complex.I))
          / riemannZeta ((x:ℝ) + (t:ℝ) * Complex.I)).im)
      = ∫ x in a..b,
          (Real.log ‖riemannZeta ((x:ℝ) + (t₀:ℝ) * Complex.I)‖
            - Real.log ‖riemannZeta ((x:ℝ) + (t₁:ℝ) * Complex.I)‖) := by
  have hbox : IntegrableOn
      (fun z : ℂ => ((deriv riemannZeta z) / riemannZeta z).im)
      (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁)) volume := by
    have h := (zeta_logDeriv_integrableOn_box_of_pos
      (a := a) (b := b) (t₁ := t₁) ht₀).im
    have hld : (fun x : ℂ => RCLike.im (logDeriv riemannZeta x))
        = fun z : ℂ => ((deriv riemannZeta z) / riemannZeta z).im := by
      funext z
      rw [logDeriv_apply]
      rfl
    rwa [hld] at h
  have hswap := box_integral_swap (f := fun z : ℂ =>
    ((deriv riemannZeta z) / riemannZeta z).im) hab ht hbox
  rw [← hswap]
  apply intervalIntegral.integral_congr_ae
  have hzfin : {z ∈ Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁) |
      riemannZeta z = 0}.Finite := by
    apply zeta_zeros_finite_in_compact (isCompact_Icc.reProdIm isCompact_Icc)
    intro hmem
    rw [Complex.mem_reProdIm] at hmem
    have him := hmem.2
    simp only [Complex.one_im, Set.mem_Icc] at him
    linarith [him.1]
  have hbadfin : (Complex.re ''
      {z ∈ Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁) |
        riemannZeta z = 0}).Finite := hzfin.image _
  have hnull := hbadfin.measure_zero volume
  rw [ae_iff]
  apply measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hx
  obtain ⟨hxI, hxne⟩ := hx
  have hxab : x ∈ Set.Icc a b := by
    rw [Set.uIoc_of_le hab] at hxI
    exact ⟨le_of_lt hxI.1, hxI.2⟩
  by_contra hxbad
  apply hxne
  apply vertical_im_logDeriv_integral' ht
  · intro t htm hz0
    apply hxbad
    refine ⟨(x:ℝ) + (t:ℝ) * Complex.I, ⟨?_, hz0⟩, by simp⟩
    rw [Complex.mem_reProdIm]
    constructor
    · simpa using hxab
    · simpa using htm
  · intro t htm h1'
    have him := congrArg Complex.im h1'
    simp at him
    linarith [htm.1]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_zeros_finite_in_compact
#print axioms CriticalLinePhasor.DVP.vertical_im_logDeriv_integral'
#print axioms CriticalLinePhasor.DVP.box_vertical_collapse
end AxiomAudit
