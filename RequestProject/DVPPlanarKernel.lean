import RequestProject.DVPTailEdge
import RequestProject.ResidueJump
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The planar kernel and local integrability of `ζ'/ζ`

The Fubini core of the Littlewood box: `1/‖s−ρ‖` is integrable on planar
balls (`α = 1 < 2 = dim_ℝ ℂ`), and near every point `ρ ≠ 1` — zero or not —
`logDeriv ζ` is integrable on a small ball: at a zero the order-`n`
factorization `ζ = (·−ρ)ⁿ·g` splits `ζ'/ζ = n/(s−ρ) + g'/g` with the second
term locally bounded, so the whole is dominated by the kernel.
-/

open Metric Complex MeasureTheory Topology Filter
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The planar Riesz kernel**: `∫_{B(ρ,ε)} ‖s−ρ‖⁻¹ dA < ∞`. -/
theorem integrableOn_inv_norm_sub (ρ : ℂ) (ε : ℝ) :
    IntegrableOn (fun s : ℂ => ‖s - ρ‖⁻¹) (ball ρ ε) volume := by
  have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h0 : IntegrableOn (fun x : ℂ => ‖x‖⁻¹) (ball 0 ε) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1)
      (f := fun x : ℂ => ‖x‖⁻¹)
    case hd =>
      rw [hfr]
      norm_num
    case hα =>
      rw [hfr]
      norm_num
    case h_decay =>
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Real.rpow_neg (norm_nonneg x), Real.rpow_one]
      exact le_of_eq (one_mul _).symm
    case h_meas =>
      exact measurable_norm.inv.aestronglyMeasurable
  have hmp : MeasurePreserving (fun x : ℂ => ρ + x) volume volume :=
    measurePreserving_add_left volume ρ
  have hpre : ((fun x : ℂ => ρ + x) ⁻¹' ball ρ ε) = ball (0:ℂ) ε := by
    ext x
    simp [mem_ball, dist_eq_norm, add_sub_cancel_left]
  have hmeas_g : AEStronglyMeasurable (fun s : ℂ => ‖s - ρ‖⁻¹)
      (volume.restrict (ball ρ ε)) :=
    ((measurable_id.sub_const ρ).norm.inv).aestronglyMeasurable
  have hmpr := hmp.restrict_preimage
    (measurableSet_ball : MeasurableSet (ball ρ ε))
  rw [hpre] at hmpr
  have hiff := hmpr.integrable_comp hmeas_g
  show Integrable _ _
  rw [← hiff]
  have hcomp : ((fun s : ℂ => ‖s - ρ‖⁻¹) ∘ (fun x : ℂ => ρ + x))
      = fun x : ℂ => ‖x‖⁻¹ := by
    funext x
    simp [add_sub_cancel_left]
  rw [hcomp]
  exact h0

/-- **Local integrability of `ζ'/ζ`** at every point off the pole — through
zeros included: there is a ball around every `ρ ≠ 1` on which
`logDeriv riemannZeta` is integrable. -/
theorem zeta_logDeriv_integrableOn_near (ρ : ℂ) (hρ1 : ρ ≠ 1) :
    ∃ ε > 0, IntegrableOn (logDeriv riemannZeta) (ball ρ ε) volume := by
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hana : AnalyticAt ℂ riemannZeta ρ :=
    hdiffOn.analyticAt (isOpen_ne.mem_nhds hρ1)
  by_cases hz0 : riemannZeta ρ = 0
  · -- a zero: order factorization
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro htop
      exact zeta_not_eventually_zero hρ1 (analyticOrderAt_eq_top.mp htop)
    set n : ℕ := analyticOrderNatAt riemannZeta ρ with hndef
    have hord : analyticOrderAt riemannZeta ρ = (n : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt hord_ne).symm
    obtain ⟨g, hg_ana, hg_ne, hfac⟩ :=
      (hana.analyticOrderAt_eq_natCast).mp hord
    have h1 : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 :=
      hg_ana.continuousAt.eventually_ne hg_ne
    have h2 : ∀ᶠ z in 𝓝 ρ, z ≠ (1:ℂ) := isOpen_ne.mem_nhds hρ1
    have h4 : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ g z := hg_ana.eventually_analyticAt
    have hld_cont : ContinuousAt (fun z => deriv g z / g z) ρ :=
      (hg_ana.deriv.continuousAt).div hg_ana.continuousAt hg_ne
    have h3 : ∀ᶠ z in 𝓝 ρ, ‖deriv g z / g z‖ ≤ ‖deriv g ρ / g ρ‖ + 1 := by
      have hcn : ContinuousAt (fun z => ‖deriv g z / g z‖) ρ := hld_cont.norm
      have hball := Metric.tendsto_nhds.mp hcn 1 one_pos
      filter_upwards [hball] with z hz1
      rw [Real.dist_eq] at hz1
      have := abs_lt.mp hz1
      linarith [this.2]
    obtain ⟨ε, hε0, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (hfac.and (h1.and (h2.and (h3.and h4))))
    refine ⟨ε, hε0, ?_⟩
    set B : ℝ := ‖deriv g ρ / g ρ‖ + 1 with hBdef
    have hB0 : (0:ℝ) ≤ B := by
      rw [hBdef]
      positivity
    set C : ℝ := (n : ℝ) + B * ε with hCdef
    have hker : Integrable (fun s : ℂ => C * ‖s - ρ‖⁻¹)
        (volume.restrict (ball ρ ε)) :=
      (integrableOn_inv_norm_sub ρ ε).const_mul C
    have hmeas : AEStronglyMeasurable (logDeriv riemannZeta)
        (volume.restrict (ball ρ ε)) := by
      have hzc : ContinuousOn riemannZeta (ball ρ ε) := by
        intro s hs
        exact (differentiableAt_riemannZeta
          ((hball s hs).2.2.1)).continuousAt.continuousWithinAt
      have hdc : ContinuousOn (deriv riemannZeta) (ball ρ ε) := by
        intro s hs
        have hana_s : AnalyticAt ℂ riemannZeta s :=
          hdiffOn.analyticAt (isOpen_ne.mem_nhds ((hball s hs).2.2.1))
        exact hana_s.deriv.continuousAt.continuousWithinAt
      have : AEStronglyMeasurable (fun s => deriv riemannZeta s / riemannZeta s)
          (volume.restrict (ball ρ ε)) :=
        ((hdc.aestronglyMeasurable measurableSet_ball).aemeasurable.div
          (hzc.aestronglyMeasurable measurableSet_ball).aemeasurable).aestronglyMeasurable
      have hlog_eq : logDeriv riemannZeta
          = fun s => deriv riemannZeta s / riemannZeta s := by
        funext s
        exact logDeriv_apply _ _
      rw [hlog_eq]
      exact this
    apply Integrable.mono' hker hmeas
    have hne_ae : ∀ᵐ s ∂volume.restrict (ball ρ ε), s ≠ ρ := by
      apply ae_restrict_of_ae
      rw [ae_iff]
      refine measure_mono_null ?_ (measure_singleton ρ)
      intro s hs
      simp only [Set.mem_setOf_eq, not_not] at hs
      simpa using hs
    filter_upwards [ae_restrict_mem measurableSet_ball, hne_ae] with s hs hsne
    have hfacs := (hball s hs).1
    have hg0 := (hball s hs).2.1
    have hB := (hball s hs).2.2.2.1
    have hga := (hball s hs).2.2.2.2
    have hsub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hpow_ne : (s - ρ) ^ n ≠ 0 := pow_ne_zero _ hsub_ne
    -- local congruence to the factorized form
    have hev : riemannZeta =ᶠ[𝓝 s] fun z => (z - ρ) ^ n * g z := by
      filter_upwards [isOpen_ball.mem_nhds hs] with z hz
      simpa [smul_eq_mul] using (hball z hz).1
    rw [logDeriv_congr_nhds hev]
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => (z - ρ) ^ n) s :=
      ((differentiableAt_id.sub_const ρ).pow n)
    have hd2 : DifferentiableAt ℂ g s := hga.differentiableAt
    rw [logDeriv_mul s hpow_ne hg0 hd1 hd2]
    have hlin := logDeriv_sub_pow (u := ρ) (z := s) (k := n) hpow_ne
    calc ‖logDeriv (fun z : ℂ => (z - ρ) ^ n) s + logDeriv g s‖
        ≤ ‖logDeriv (fun z : ℂ => (z - ρ) ^ n) s‖ + ‖logDeriv g s‖ :=
          norm_add_le _ _
      _ ≤ (n : ℝ) * ‖s - ρ‖⁻¹ + B := by
          have h1 : ‖logDeriv (fun z : ℂ => (z - ρ) ^ n) s‖
              = (n : ℝ) * ‖s - ρ‖⁻¹ := by
            rw [hlin, norm_div, Complex.norm_natCast, div_eq_mul_inv]
          have h2 : ‖logDeriv g s‖ ≤ B := by
            have : logDeriv g s = deriv g s / g s := logDeriv_apply _ _
            rw [this]
            exact hB
          linarith [h1.le, h1.ge, h2]
      _ ≤ C * ‖s - ρ‖⁻¹ := by
          have hsρ : ‖s - ρ‖ < ε := by
            have := mem_ball.mp hs
            rwa [dist_eq_norm] at this
          have hsρ0 : (0:ℝ) < ‖s - ρ‖ := norm_pos_iff.mpr hsub_ne
          have hinv : (1:ℝ) ≤ ε * ‖s - ρ‖⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ hsρ0]
            linarith
          have hBB : B ≤ B * ε * ‖s - ρ‖⁻¹ := by
            calc B = B * 1 := (mul_one B).symm
              _ ≤ B * (ε * ‖s - ρ‖⁻¹) :=
                  mul_le_mul_of_nonneg_left hinv hB0
              _ = B * ε * ‖s - ρ‖⁻¹ := by ring
          rw [hCdef]
          have hexp : ((n:ℝ) + B * ε) * ‖s - ρ‖⁻¹
              = (n:ℝ) * ‖s - ρ‖⁻¹ + B * ε * ‖s - ρ‖⁻¹ := by ring
          rw [hexp]
          linarith
  · -- not a zero: `logDeriv ζ` is continuous near ρ
    have h1 : ∀ᶠ s in 𝓝 ρ, riemannZeta s ≠ 0 :=
      hana.continuousAt.eventually_ne hz0
    have h2 : ∀ᶠ s in 𝓝 ρ, s ≠ (1:ℂ) := isOpen_ne.mem_nhds hρ1
    obtain ⟨ε, hε0, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
    refine ⟨ε/2, by linarith, ?_⟩
    have hcont : ContinuousOn (logDeriv riemannZeta) (closedBall ρ (ε/2)) := by
      intro s hs
      have hsball : s ∈ ball ρ ε := by
        have := mem_closedBall.mp hs
        rw [mem_ball]
        linarith
      have hs1 := (hball s hsball).2
      have hs0 := (hball s hsball).1
      have hana_s : AnalyticAt ℂ riemannZeta s :=
        hdiffOn.analyticAt (isOpen_ne.mem_nhds hs1)
      have hc : ContinuousAt (fun z => deriv riemannZeta z / riemannZeta z) s :=
        (hana_s.deriv.continuousAt).div
          (differentiableAt_riemannZeta hs1).continuousAt hs0
      have hlog_eq : logDeriv riemannZeta
          = fun z => deriv riemannZeta z / riemannZeta z := by
        funext z
        exact logDeriv_apply _ _
      rw [hlog_eq]
      exact hc.continuousWithinAt
    exact (hcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.integrableOn_inv_norm_sub
#print axioms CriticalLinePhasor.DVP.zeta_logDeriv_integrableOn_near
end AxiomAudit
