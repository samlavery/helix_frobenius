import RequestProject.DVPRightEdgeLog
import RequestProject.ZetaContourArgument

/-!
# Right-edge principality of the contour lift

On the vertical half of the standard contour the ζ-lift IS the principal
logarithm: both are continuous lifts of the same path through the covering
`exp`, and they agree at the base point (`initialLog = Log ζ(2)`), so
covering-map lift uniqueness (`IsCoveringMap.eqOn_of_comp_eqOn`) forces
them equal on the connected half.  At the corner `2+iT` the 405 bound then
pins `|Im lift| ≤ 2` — the right edge of Littlewood's box never
accumulates argument.
-/

open Metric Complex MeasureTheory Topology Filter
open CriticalLinePhasor.ContourArgument

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `‖ζ(z) − 1‖ ≤ 3/4` for `Re z ≥ 2` (the 405 chain, factored). -/
theorem zeta_sub_one_le_three_quarters {z : ℂ} (hz : 2 ≤ z.re) :
    ‖riemannZeta z - 1‖ ≤ 3/4 := by
  have hw := zeta_sub_one_norm_le (by linarith : 1 < z.re)
  have h1 : (2:ℝ)^(-z.re) ≤ 1/4 := by
    have hmono : (2:ℝ)^(-z.re) ≤ (2:ℝ)^(-(2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2:ℝ)^(-(2:ℝ)) = 1/4 := by
      rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    exact hmono.trans h4.le
  have h2 : (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ 1/2 := by
    have h2σ : (2:ℝ)^(1-z.re) ≤ 1/2 := by
      have hmono : (2:ℝ)^(1-z.re) ≤ (2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have hhalf : (2:ℝ)^(-(1:ℝ)) = 1/2 := by
        rw [show (-(1:ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      exact hmono.trans hhalf.le
    calc (2:ℝ)^(1 - z.re) / (z.re - 1) ≤ (2:ℝ)^(1 - z.re) :=
          div_le_self (by positivity) (by linarith)
      _ ≤ 1/2 := h2σ
  linarith [hw]

/-- `ζ(z)` lies in the slit plane for `Re z ≥ 2` (`Re ζ ≥ 1/4`). -/
theorem zeta_mem_slitPlane_of_two_le {z : ℂ} (hz : 2 ≤ z.re) :
    riemannZeta z ∈ Complex.slitPlane := by
  apply Or.inl
  have h := zeta_sub_one_le_three_quarters hz
  have hre := Complex.abs_re_le_norm (riemannZeta z - 1)
  have hre' : (riemannZeta z - 1).re = (riemannZeta z).re - 1 := by simp
  rw [hre'] at hre
  have := (abs_le.mp hre).1
  linarith

/-- The vertical half of the standard contour has real part `2`. -/
theorem standardContour_re_of_le_half {T : ℝ} {u : unitInterval}
    (hu : (u:ℝ) ≤ 1/2) : (standardContour T u).re = 2 := by
  rw [standardContour, Path.trans_apply, dif_pos hu]
  change (AffineMap.lineMap (2 : ℂ) (upperRight T) ((2 * (u:ℝ) : ℝ))).re = 2
  rw [AffineMap.lineMap_apply_module]
  simp [upperRight]
  ring

/-- **Right-edge principality**: on the vertical half of the contour, the
ζ-lift is the principal logarithm of ζ. -/
theorem contourLogLift_eq_log_on_half {T : ℝ} (hT : GoodHeight T)
    {u : unitInterval} (hu : (u:ℝ) ≤ 1/2) :
    contourLogLift hT u
      = Complex.log (riemannZeta (standardContour T u)) := by
  set uhalf : unitInterval := ⟨1/2, by constructor <;> norm_num⟩ with huhalf
  set s : Set unitInterval := Set.Icc 0 uhalf with hsdef
  have hs_pre : IsPreconnected s := isPreconnected_Icc
  have hmem : ∀ v : unitInterval, v ∈ s → (v:ℝ) ≤ 1/2 := by
    intro v hv
    exact hv.2
  have hre2 : ∀ v : unitInterval, v ∈ s → (standardContour T v).re = 2 :=
    fun v hv => standardContour_re_of_le_half (hmem v hv)
  have hzne : ∀ v : unitInterval, v ∈ s →
      riemannZeta (standardContour T v) ≠ 0 := by
    intro v hv
    apply riemannZeta_ne_zero_of_one_le_re
    rw [hre2 v hv]
    norm_num
  have hone : ∀ v : unitInterval, v ∈ s → standardContour T v ≠ 1 := by
    intro v hv h1
    have := congrArg Complex.re h1
    rw [hre2 v hv] at this
    simp at this
  have hslit : ∀ v : unitInterval, v ∈ s →
      riemannZeta (standardContour T v) ∈ Complex.slitPlane := by
    intro v hv
    exact zeta_mem_slitPlane_of_two_le (by rw [hre2 v hv])
  have hg₂cont : ContinuousOn
      (fun v : unitInterval =>
        Complex.log (riemannZeta (standardContour T v))) s := by
    intro v hv
    have hc : ContinuousAt
        (Complex.log ∘ riemannZeta ∘ (standardContour T : unitInterval → ℂ)) v := by
      apply ContinuousAt.comp
      · exact continuousAt_clog (hslit v hv)
      · apply ContinuousAt.comp
        · exact (differentiableAt_riemannZeta (hone v hv)).continuousAt
        · exact (standardContour T).continuous.continuousAt
    exact hc.continuousWithinAt
  have heq := Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hs_pre
    ((contourLogLift hT).continuous.continuousOn) hg₂cont
    (by
      intro v hv
      apply Subtype.ext
      show Complex.exp (contourLogLift hT v)
        = Complex.exp (Complex.log (riemannZeta (standardContour T v)))
      rw [exp_contourLogLift, Complex.exp_log (hzne v hv)])
    (a := 0)
    (by
      constructor
      · exact le_refl 0
      · show ((0:unitInterval):ℝ) ≤ ((uhalf:unitInterval):ℝ)
        norm_num [huhalf])
    (by
      rw [contourLogLift_zero]
      have h0 : standardContour T 0 = 2 := (standardContour T).source
      rw [h0]
      rw [riemannZeta_two]
      have hcast : ((Real.pi:ℂ) ^ 2 / 6) = (((Real.pi ^ 2 / 6 : ℝ)):ℂ) := by
        push_cast
        ring
      rw [hcast, ← Complex.ofReal_log (by positivity)]
      rfl)
  apply heq
  exact ⟨bot_le, by exact_mod_cast hu⟩

/-- The corner value: the lift at `2+iT` is the principal log, hence its
imaginary part is at most `2` in absolute value. -/
theorem abs_im_contourLogLift_half {T : ℝ} (hT : GoodHeight T) :
    |(contourLogLift hT ⟨1/2, by constructor <;> norm_num⟩).im| ≤ 2 := by
  rw [contourLogLift_eq_log_on_half hT (by norm_num)]
  have hcorner : standardContour T (⟨1/2, by constructor <;> norm_num⟩ : unitInterval)
      = upperRight T := by
    rw [standardContour, Path.trans_apply, dif_pos (by norm_num)]
    norm_num
  rw [hcorner]
  have h := norm_log_zeta_ge_two (z := upperRight T)
    (by simp [upperRight])
  calc |(Complex.log (riemannZeta (upperRight T))).im|
      ≤ ‖Complex.log (riemannZeta (upperRight T))‖ :=
        Complex.abs_im_le_norm _
    _ ≤ 2 := h

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zeta_sub_one_le_three_quarters
#print axioms CriticalLinePhasor.DVP.zeta_mem_slitPlane_of_two_le
#print axioms CriticalLinePhasor.DVP.standardContour_re_of_le_half
#print axioms CriticalLinePhasor.DVP.contourLogLift_eq_log_on_half
#print axioms CriticalLinePhasor.DVP.abs_im_contourLogLift_half
end AxiomAudit
