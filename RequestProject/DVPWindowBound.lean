import RequestProject.DVPRightBox
import RequestProject.DVPLittlewood

/-!
# The window bound: `|∫ F| ≤ 12 + 1600·log t₁` for the per-height ledger

Assembly step (iv).  `F t := Im Log ζ(2+it) − ∫_{1/2}^2 Im(ζ'/ζ)(x+it) dx`
is the total-function form of `π·classicalSContour` (407).  Its window
integral splits into the right-edge argument integral (≤ 12, by 408) minus
the main-box collapse (404), whose two horizontal edges are two-sided
bounded (399 below, 392 above) at good heights.
-/

open Metric Complex MeasureTheory Topology Filter Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The two-sided top-edge bound at good heights ≥ e⁴:
`|∫_{1/2}^2 log‖ζ(x+iT)‖ dx| ≤ 800·log T`. -/
theorem top_edge_log_abs_le {T : ℝ} (hg : GoodHeight T)
    (he : Real.exp 4 ≤ T) :
    |∫ x in (1/2 : ℝ)..2, Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * I)‖|
      ≤ 800 * Real.log T := by
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) he
    rwa [Real.log_exp] at this
  have hnz : ∀ x ∈ Set.Icc (1/2 : ℝ) 2,
      riemannZeta ((x:ℂ) + (T:ℂ) * I) ≠ 0 :=
    fun x hx => zeta_top_ne_zero' hg hx
  have hlow := zeta_top_edge_log_lower he hnz
  -- upper: pointwise majorant integrated
  have hup : ∫ x in (1/2 : ℝ)..2,
      Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * I)‖
        ≤ 800 * Real.log T := by
    have hint : IntervalIntegrable
        (fun x : ℝ => Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * I)‖)
        MeasureTheory.volume (1/2) 2 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]
      apply ContinuousOn.log
      · apply ContinuousOn.norm
        intro x hx
        have hne1 : (x:ℂ) + (T:ℂ) * I ≠ 1 := by
          intro h1
          have := congrArg Complex.im h1
          simp at this
          linarith
        have hc : ContinuousAt
            (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (T:ℂ) * I) x :=
          ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
            ((Complex.continuous_ofReal.add continuous_const).continuousAt)
        exact hc.continuousWithinAt
      · intro x hx
        exact norm_ne_zero_iff.mpr (hnz x hx)
    have hpt : ∀ x ∈ Set.Icc (1/2 : ℝ) 2,
        Real.log ‖riemannZeta ((x:ℂ) + (T:ℂ) * I)‖
          ≤ Real.log 24 + (3/4) * Real.log T := by
      intro x hx
      have hre : ((x:ℂ) + (T:ℂ) * I).re = x := by simp
      have him : ((x:ℂ) + (T:ℂ) * I).im = T := by simp
      have h := log_norm_zeta_le (s := (x:ℂ) + (T:ℂ) * I)
        (by rw [him]; rw [abs_of_pos (by linarith)]; linarith)
        (by rw [hre]; linarith [hx.1]) (by rw [hre]; exact hx.2)
      rw [him, abs_of_pos (by linarith : (0:ℝ) < T)] at h
      exact h
    have hmono := intervalIntegral.integral_mono_on
      (by norm_num : (1/2:ℝ) ≤ 2) hint intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hlog24 : Real.log 24 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
        nlinarith [Real.exp_one_gt_d9]
      have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
          * (Real.exp 1 * Real.exp 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [he2, Real.exp_pos 1]
    nlinarith [hL4]
  rw [abs_le]
  constructor
  · linarith [hlow]
  · exact hup

/-- The inner main-box integral is interval-integrable in the height. -/
theorem inner_integral_intervalIntegrable {a b t₀ t₁ : ℝ}
    (hab : a ≤ b) (ht : t₀ ≤ t₁) (ht₀ : 0 < t₀) :
    IntervalIntegrable
      (fun t : ℝ => ∫ x in a..b,
        (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
          riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)
      MeasureTheory.volume t₀ t₁ := by
  -- box-integrability transported to the real product, then the marginal
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
  set e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd with hedef
  have hep : MeasurePreserving e volume (volume.prod volume) :=
    Complex.volume_preserving_equiv_real_prod
  have hpre : ((e : ℂ → ℝ × ℝ) ⁻¹' (Set.Icc a b ×ˢ Set.Icc t₀ t₁))
      = Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁) := by
    ext z
    simp only [hedef, Complex.measurableEquivRealProd, Complex.mem_reProdIm,
      Set.mem_prod, Set.mem_preimage, Set.mem_Icc]
    tauto
  have hS : MeasurableSet (Set.Icc a b ×ˢ Set.Icc t₀ t₁ : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hres := hep.restrict_preimage hS
  rw [hpre] at hres
  set g : ℝ × ℝ → ℝ := fun p =>
    ((deriv riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)) /
      riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)).im with hgdef
  have hge : g ∘ (e : ℂ → ℝ × ℝ)
      = fun z : ℂ => ((deriv riemannZeta z) / riemannZeta z).im := by
    funext z
    show ((deriv riemannZeta ((z.re : ℂ) + (z.im : ℂ) * I)) /
      riemannZeta ((z.re : ℂ) + (z.im : ℂ) * I)).im = _
    rw [Complex.re_add_im]
  have hgmeas : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc t₀ t₁)) := by
    have h1 : AEStronglyMeasurable (g ∘ (e : ℂ → ℝ × ℝ))
        (volume.restrict (Complex.reProdIm (Set.Icc a b) (Set.Icc t₀ t₁))) := by
      rw [hge]
      exact hbox.aestronglyMeasurable
    exact (hres.aestronglyMeasurable_comp_iff e.measurableEmbedding).mp h1
  have hgint : Integrable g
      ((volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc t₀ t₁)) := by
    apply (hres.integrable_comp hgmeas).mp
    rw [hge]
    exact hbox
  rw [← Measure.prod_restrict] at hgint
  have hmarg := hgint.integral_prod_right
  -- convert the marginal's inner set-integral to the interval integral
  have hcong : (fun t : ℝ => ∫ x in Set.Icc a b,
      ((deriv riemannZeta ((x:ℂ) + (t:ℂ) * I)) /
        riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)
      = fun t : ℝ => ∫ x in a..b,
        ((deriv riemannZeta ((x:ℂ) + (t:ℂ) * I)) /
          riemannZeta ((x:ℂ) + (t:ℂ) * I)).im := by
    funext t
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  have : IntegrableOn (fun t : ℝ => ∫ x in Set.Icc a b,
      ((deriv riemannZeta ((x:ℂ) + (t:ℂ) * I)) /
        riemannZeta ((x:ℂ) + (t:ℂ) * I)).im) (Set.Icc t₀ t₁) volume := hmarg
  rwa [hcong] at this

/-- **The window bound** (assembly step iv): over any good-height window
above `e⁴`, the integrated per-height ledger is `≤ 12 + 1600·log t₁`. -/
theorem window_arg_integral_bound {t₀ t₁ : ℝ}
    (h₀ : GoodHeight t₀) (h₁ : GoodHeight t₁)
    (he : Real.exp 4 ≤ t₀) (ht : t₀ ≤ t₁) :
    |∫ t in t₀..t₁,
        ((Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im
          - ∫ x in (1/2 : ℝ)..2,
              (deriv riemannZeta ((x:ℂ) + (t:ℂ) * I) /
                riemannZeta ((x:ℂ) + (t:ℂ) * I)).im)|
      ≤ 12 + 1600 * Real.log t₁ := by
  have hT50 : (50:ℝ) ≤ t₀ := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have h2t₀ : (2:ℝ) ≤ t₀ := by linarith
  -- split
  have hi1 : IntervalIntegrable
      (fun t : ℝ => (Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I))).im)
      MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    intro t htm
    have htne : ((2:ℂ) + (t:ℂ) * I) ≠ 1 := by
      intro h1
      have := congrArg Complex.im h1
      simp at this
      linarith [htm.1]
    have hre : ((2:ℂ) + (t:ℂ) * I).re = 2 := by simp
    have hinner : ContinuousAt (fun t : ℝ => (2:ℂ) + (t:ℂ) * I) t :=
      (continuous_const.add (Complex.continuous_ofReal.mul
        continuous_const)).continuousAt
    have hζ : ContinuousAt riemannZeta ((2:ℂ) + (t:ℂ) * I) :=
      (differentiableAt_riemannZeta htne).continuousAt
    have hlog : ContinuousAt Complex.log (riemannZeta ((2:ℂ) + (t:ℂ) * I)) :=
      continuousAt_clog (zeta_mem_slitPlane_of_two_le (by rw [hre]))
    have hz_at : ContinuousAt
        (riemannZeta ∘ fun t : ℝ => (2:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp hζ hinner
    have hlog_at : ContinuousAt
        (Complex.log ∘ riemannZeta ∘ fun t : ℝ => (2:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp hlog hz_at
    have hcomp : ContinuousAt
        (Complex.im ∘ Complex.log ∘ riemannZeta ∘
          fun t : ℝ => (2:ℂ) + (t:ℂ) * I) t :=
      ContinuousAt.comp Complex.continuous_im.continuousAt hlog_at
    exact hcomp.continuousWithinAt
  have hi2 := inner_integral_intervalIntegrable
    (by norm_num : (1/2:ℝ) ≤ 2) ht (by linarith : (0:ℝ) < t₀)
  rw [intervalIntegral.integral_sub hi1 hi2]
  -- right edge ≤ 12
  have hright := right_edge_arg_integral_bound h2t₀ ht
  -- main box collapse
  have hcollapse := box_vertical_collapse
    (by norm_num : (1/2:ℝ) ≤ 2) ht (by linarith : (0:ℝ) < t₀)
  rw [hcollapse]
  -- split and bound the two horizontal edges
  have hLog₁ : (4:ℝ) ≤ Real.log t₁ := by
    have h1 : Real.exp 4 ≤ t₁ := le_trans he ht
    have := Real.log_le_log (Real.exp_pos 4) h1
    rwa [Real.log_exp] at this
  have hlog_mono : Real.log t₀ ≤ Real.log t₁ :=
    Real.log_le_log (by linarith) ht
  have hedge₀ := top_edge_log_abs_le h₀ he
  have hedge₁ := top_edge_log_abs_le h₁ (le_trans he ht)
  have hint₀ : IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
      MeasureTheory.volume (1/2) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hne1 : (x:ℂ) + (t₀:ℂ) * I ≠ 1 := by
        intro h1
        have := congrArg Complex.im h1
        simp at this
        linarith
      have hc : ContinuousAt
          (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (t₀:ℂ) * I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc.continuousWithinAt
    · intro x hx
      exact norm_ne_zero_iff.mpr (zeta_top_ne_zero' h₀ hx)
  have hint₁ : IntervalIntegrable
      (fun x : ℝ => Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖)
      MeasureTheory.volume (1/2) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      intro x hx
      have hne1 : (x:ℂ) + (t₁:ℂ) * I ≠ 1 := by
        intro h1
        have := congrArg Complex.im h1
        simp at this
        linarith
      have hc : ContinuousAt
          (riemannZeta ∘ fun ξ : ℝ => (ξ:ℂ) + (t₁:ℂ) * I) x :=
        ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
          ((Complex.continuous_ofReal.add continuous_const).continuousAt)
      exact hc.continuousWithinAt
    · intro x hx
      exact norm_ne_zero_iff.mpr (zeta_top_ne_zero' h₁ hx)
  have hsplit : ∫ x in (1/2 : ℝ)..2,
      (Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖
        - Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖)
      = (∫ x in (1/2 : ℝ)..2,
          Real.log ‖riemannZeta ((x:ℂ) + (t₀:ℂ) * I)‖)
        - ∫ x in (1/2 : ℝ)..2,
            Real.log ‖riemannZeta ((x:ℂ) + (t₁:ℂ) * I)‖ :=
    intervalIntegral.integral_sub hint₀ hint₁
  rw [hsplit]
  have habs1 := abs_le.mp hedge₀
  have habs2 := abs_le.mp hedge₁
  have habs3 := abs_le.mp hright
  rw [abs_le]
  constructor <;> nlinarith [hlog_mono, hLog₁]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.top_edge_log_abs_le
#print axioms CriticalLinePhasor.DVP.inner_integral_intervalIntegrable
#print axioms CriticalLinePhasor.DVP.window_arg_integral_bound
end AxiomAudit
