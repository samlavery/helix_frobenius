import RequestProject.DVPLiftPrincipal

/-!
# The top-edge ζ-lift transport (the last identity brick)

The ζ-analogue of the compiled ξ-side `xiTopLift` FTC: reparametrize the
ζ-lift along the top edge by the abscissa, exponentiate to `ζ(x+iT)`
(`exp_contourLogLift` + the contour-point computation), and apply the lift
FTC.  Combined with 406's principality this expresses
`π·classicalSContour(T) = Im Log ζ(2+iT) − ∫_{1/2}^2 Im(ζ'/ζ)(x+iT) dx`
— the per-height identity the Littlewood integral consumes.
-/

open Metric Complex MeasureTheory Topology Filter Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The ζ-lift extended to the real parameter line. -/
def zetaContourLogReal {T : ℝ} (hT : GoodHeight T) : C(ℝ, ℂ) :=
  ContinuousMap.IccExtendCM (contourLogLift hT)

/-- The ζ-lift along the top edge, parametrized by the abscissa. -/
def zetaTopLift {T : ℝ} (hT : GoodHeight T) (x : ℝ) : ℂ :=
  zetaContourLogReal hT ((7 / 2 - x) / 3)

theorem continuous_zetaTopLift {T : ℝ} (hT : GoodHeight T) :
    Continuous (zetaTopLift hT) := by
  unfold zetaTopLift zetaContourLogReal
  fun_prop

/-- The top-edge contour point at parameter `(7/2−x)/3` is `x + iT`. -/
theorem standardContour_top_apply {T x : ℝ} (hx : x ∈ Icc (1/2 : ℝ) 2)
    {hu : (7 / 2 - x) / 3 ∈ Icc (0:ℝ) 1} :
    standardContour T ⟨(7 / 2 - x) / 3, hu⟩ = (x : ℂ) + (T : ℂ) * I := by
  have huhalf : 1 / 2 ≤ (7 / 2 - x) / 3 := by
    have := hx.2
    linarith
  rw [standardContour, Path.trans_apply]
  split_ifs with hbranch
  · have hle : ((7 / 2 - x) / 3 : ℝ) ≤ 1 / 2 := by simpa using hbranch
    have hueq : ((7 / 2 - x) / 3 : ℝ) = 1 / 2 := le_antisymm hle huhalf
    have hxeq : x = 2 := by linarith
    subst hxeq
    change AffineMap.lineMap (2 : ℂ) (upperRight T) _ = _
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext <;> simp [upperRight] <;> ring
  · change AffineMap.lineMap (upperRight T) (line T) _ = _
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext <;> simp [upperRight, line, lineC] <;> ring

/-- The top-edge lift exponentiates to `ζ(x+iT)`. -/
theorem exp_zetaTopLift {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Icc (1/2 : ℝ) 2) :
    Complex.exp (zetaTopLift hT x)
      = riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
  have hu : ((7 / 2 - x) / 3 : ℝ) ∈ Icc (0:ℝ) 1 := by
    constructor
    · linarith [hx.2]
    · linarith [hx.1]
  rw [zetaTopLift, zetaContourLogReal, ContinuousMap.IccExtendCM_of_mem hu,
    exp_contourLogLift, standardContour_top_apply hx]

/-- ζ is nonvanishing along the top edge (it is `exp` of the lift). -/
theorem zeta_top_ne_zero' {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Icc (1/2 : ℝ) 2) :
    riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  rw [← exp_zetaTopLift hT hx]
  exact Complex.exp_ne_zero _

/-- The horizontal derivative of ζ along the top edge. -/
theorem hasDerivAt_zeta_top {T : ℝ} (hT : GoodHeight T) (x : ℝ) :
    HasDerivAt (fun ξ : ℝ => riemannZeta ((ξ : ℂ) + (T : ℂ) * I))
      (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I)) x := by
  have hne1 : (x : ℂ) + (T : ℂ) * I ≠ 1 := by
    intro h1
    have := congrArg Complex.im h1
    simp at this
    exact hT.1.ne' this
  have haff : HasDerivAt (fun ξ : ℝ => (ξ : ℂ) + (T : ℂ) * I) 1 x := by
    have ht : HasDerivAt (fun ξ : ℝ => ((ξ:ℝ):ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    simpa using ht.add_const ((T : ℂ) * I)
  have h := (differentiableAt_riemannZeta hne1).hasDerivAt.comp x haff
  simpa [Function.comp_def] using h

/-- The top-edge log-derivative is interval-integrable at good heights. -/
theorem intervalIntegrable_zeta_top_logDeriv {T : ℝ} (hT : GoodHeight T) :
    IntervalIntegrable
      (fun x : ℝ => deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
        riemannZeta ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume (1/2) 2 := by
  have haff : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) := by fun_prop
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)]
  have hdiffOn : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hdc : ContinuousOn
      (fun x : ℝ => deriv riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Icc (1/2 : ℝ) 2) := by
    intro x hx
    have hne1 : (x : ℂ) + (T : ℂ) * I ≠ 1 := by
      intro h1
      have := congrArg Complex.im h1
      simp at this
      exact hT.1.ne' this
    have hana : AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) :=
      hdiffOn.analyticAt (isOpen_ne.mem_nhds hne1)
    have hc : ContinuousAt
        (deriv riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (T : ℂ) * I) x :=
      ContinuousAt.comp hana.deriv.continuousAt haff.continuousAt
    exact hc.continuousWithinAt
  have hzc : ContinuousOn
      (fun x : ℝ => riemannZeta ((x : ℂ) + (T : ℂ) * I))
      (Icc (1/2 : ℝ) 2) := by
    intro x hx
    have hne1 : (x : ℂ) + (T : ℂ) * I ≠ 1 := by
      intro h1
      have := congrArg Complex.im h1
      simp at this
      exact hT.1.ne' this
    have hc : ContinuousAt
        (riemannZeta ∘ fun ξ : ℝ => (ξ : ℂ) + (T : ℂ) * I) x :=
      ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
        haff.continuousAt
    exact hc.continuousWithinAt
  exact hdc.div hzc (fun x hx => zeta_top_ne_zero' hT hx)

/-- **The top-edge transport**: the log-derivative integral along the top
edge equals the lift increment from the corner to the endpoint. -/
theorem zeta_top_logDeriv_integral_eq_lift_sub {T : ℝ} (hT : GoodHeight T) :
    (∫ x in (1/2 : ℝ)..2,
        deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
          riemannZeta ((x : ℂ) + (T : ℂ) * I))
      = zetaTopLift hT 2 - zetaTopLift hT (1/2) := by
  exact intervalIntegral_logDeriv_eq_lift_sub_of_le
    (by norm_num : (1/2 : ℝ) ≤ 2)
    (continuous_zetaTopLift hT)
    (fun x hx => exp_zetaTopLift hT hx)
    (fun x _ => hasDerivAt_zeta_top hT x)
    (intervalIntegrable_zeta_top_logDeriv hT)

/-- The endpoints of the top-edge lift are the contour-lift values. -/
theorem zetaTopLift_two {T : ℝ} (hT : GoodHeight T) :
    zetaTopLift hT 2
      = contourLogLift hT ⟨1/2, by constructor <;> norm_num⟩ := by
  rw [zetaTopLift, zetaContourLogReal]
  have h : ((7/2 - 2)/3 : ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  rw [ContinuousMap.IccExtendCM_of_mem h]
  congr 1
  ext
  norm_num

theorem zetaTopLift_half {T : ℝ} (hT : GoodHeight T) :
    zetaTopLift hT (1/2) = contourLogLift hT 1 := by
  rw [zetaTopLift, zetaContourLogReal]
  have h : ((7/2 - 1/2)/3 : ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  rw [ContinuousMap.IccExtendCM_of_mem h]
  congr 1
  ext
  norm_num

/-- **The per-height Littlewood identity**: at every good height,
`π·S_contour(T) = Im Log ζ(2+iT) − ∫_{1/2}^2 Im(ζ'/ζ)(x+iT) dx`. -/
theorem classicalSContour_eq_log_sub_integral {T : ℝ} (hT : GoodHeight T) :
    Real.pi * classicalSContour hT
      = (Complex.log (riemannZeta ((2:ℂ) + (T:ℂ) * I))).im
        - ∫ x in (1/2 : ℝ)..2,
            (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
              riemannZeta ((x : ℂ) + (T : ℂ) * I)).im := by
  have htrans := zeta_top_logDeriv_integral_eq_lift_sub hT
  rw [zetaTopLift_two hT, zetaTopLift_half hT] at htrans
  have hlift1 : contourLogLift hT 1
      = contourLogLift hT ⟨1/2, by constructor <;> norm_num⟩
        - ∫ x in (1/2 : ℝ)..2,
            deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
              riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
    rw [htrans]
    ring
  have hprin := contourLogLift_eq_log_on_half hT
    (u := ⟨1/2, by constructor <;> norm_num⟩) (le_refl _)
  have hcorner : standardContour T (⟨1/2, by constructor <;> norm_num⟩ : unitInterval)
      = (2:ℂ) + (T:ℂ) * I := by
    rw [standardContour, Path.trans_apply, dif_pos (by norm_num)]
    change AffineMap.lineMap (2 : ℂ) (upperRight T) _ = _
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext <;> simp [upperRight] <;> ring
  rw [hcorner] at hprin
  have him := congrArg Complex.im hlift1
  rw [hprin] at him
  rw [Complex.sub_im] at him
  have hswap : (∫ x in (1/2 : ℝ)..2,
        deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
          riemannZeta ((x : ℂ) + (T : ℂ) * I)).im
      = ∫ x in (1/2 : ℝ)..2,
          (deriv riemannZeta ((x : ℂ) + (T : ℂ) * I) /
            riemannZeta ((x : ℂ) + (T : ℂ) * I)).im :=
    (intervalIntegral.intervalIntegral_im
      (intervalIntegrable_zeta_top_logDeriv hT)).symm
  rw [hswap] at him
  rw [classicalSContour]
  field_simp
  linarith [him]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.standardContour_top_apply
#print axioms CriticalLinePhasor.DVP.exp_zetaTopLift
#print axioms CriticalLinePhasor.DVP.zeta_top_logDeriv_integral_eq_lift_sub
#print axioms CriticalLinePhasor.DVP.classicalSContour_eq_log_sub_integral
end AxiomAudit
