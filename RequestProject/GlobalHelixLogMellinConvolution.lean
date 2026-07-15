import RequestProject.GlobalHelixFixedCompletionMellin
import Mathlib.Analysis.Convolution

/-!
# Multiplicative Mellin convolution in signed-log height

The global carrier stores positive multiplicative height as a signed logarithm.  In that native
coordinate, multiplicative convolution is ordinary additive convolution.  Mathlib's convolution
integral theorem therefore gives the Mellin product law directly.
-/

open Real Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

theorem rexpNeg_image_univ : (Real.exp ∘ Neg.neg) '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ,
    Real.range_exp]

theorem rexpNeg_injOn_univ : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)

theorem rexpNeg_hasDerivWithinAt :
    ∀ x ∈ Set.univ,
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

theorem rexpNeg_mellinIntegrand (x : ℝ) (s : ℂ) (z : ℂ) :
    Real.exp (-x) • Complex.exp (-(x : ℂ)) ^ (s - 1) • z =
      Complex.exp (-s * (x : ℂ)) • z := by
  have hcoef : (Real.exp (-x) : ℂ) * Complex.exp (-(x : ℂ)) ^ (s - 1) =
      Complex.exp (-s * (x : ℂ)) := by
    rw [Complex.ofReal_exp]
    push_cast
    nth_rewrite 1 [← Complex.cpow_one (Complex.exp (-(x : ℂ)))]
    rw [← Complex.cpow_add _ _ (Complex.exp_ne_zero _),
      Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
    ring_nf
  simpa [smul_eq_mul, ← mul_assoc] using congrArg (fun c : ℂ => c * z) hcoef

theorem mellin_eq_negLogIntegral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, Complex.exp (-s * u) * f (Real.exp (-u)) := by
  calc
    mellin f s =
        ∫ u : ℝ, Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin, ← rexpNeg_image_univ,
        integral_image_eq_integral_abs_deriv_smul
          MeasurableSet.univ rexpNeg_hasDerivWithinAt rexpNeg_injOn_univ]
      simp only [Measure.restrict_univ, Function.comp_apply, abs_neg,
        abs_of_pos (Real.exp_pos _)]
      apply integral_congr_ae
      filter_upwards with u
      simpa [smul_eq_mul, mul_assoc] using
        rexpNeg_mellinIntegrand u s (f (Real.exp (-u)))
    _ = ∫ u : ℝ, Complex.exp (-s * u) * f (Real.exp (-u)) := by
      simp only [smul_eq_mul]

theorem mellinConvergent_iff_negLogIntegrable (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔
      Integrable (fun u : ℝ => Complex.exp (-s * u) * f (Real.exp (-u))) := by
  rw [MellinConvergent, ← rexpNeg_image_univ,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexpNeg_hasDerivWithinAt rexpNeg_injOn_univ]
  simp only [IntegrableOn, Measure.restrict_univ, Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply integrable_congr
  filter_upwards with u
  simpa [smul_eq_mul, mul_assoc] using
    rexpNeg_mellinIntegrand u s (f (Real.exp (-u)))

/-- Multiplicative convolution defined in the carrier's signed-log height coordinate. -/
noncomputable def logMellinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then
    MeasureTheory.convolution
      (fun u : ℝ => f (Real.exp (-u)))
      (fun u : ℝ => g (Real.exp (-u)))
      (ContinuousLinearMap.mul ℂ ℂ) (μ := MeasureTheory.volume) (-Real.log x)
  else 0

theorem logMellinConvolution_rexpNeg (f g : ℝ → ℂ) (u : ℝ) :
    logMellinConvolution f g (Real.exp (-u)) =
      MeasureTheory.convolution
        (fun v : ℝ => f (Real.exp (-v)))
        (fun v : ℝ => g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) (μ := MeasureTheory.volume) u := by
  simp [logMellinConvolution, Real.exp_pos, Real.log_exp]

theorem weighted_logMellinConvolution_eq_convolution
    (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    Complex.exp (-s * u) * logMellinConvolution f g (Real.exp (-u)) =
      MeasureTheory.convolution
        (fun v : ℝ => Complex.exp (-s * v) * f (Real.exp (-v)))
        (fun v : ℝ => Complex.exp (-s * v) * g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) (μ := MeasureTheory.volume) u := by
  rw [logMellinConvolution_rexpNeg]
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  have he : Complex.exp (-s * u) =
      Complex.exp (-s * v) * Complex.exp (-s * (u - v)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ac_rfl

/-- Mellin transform turns signed-log multiplicative convolution into multiplication. -/
theorem logMellinConvolution_hasMellin
    (f g : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (logMellinConvolution f g) s (mellin f s * mellin g s) := by
  let F : ℝ → ℂ := fun u => Complex.exp (-s * u) * f (Real.exp (-u))
  let G : ℝ → ℂ := fun u => Complex.exp (-s * u) * g (Real.exp (-u))
  have hF : Integrable F := (mellinConvergent_iff_negLogIntegrable f s).mp hf
  have hG : Integrable G := (mellinConvergent_iff_negLogIntegrable g s).mp hg
  have hconv : Integrable
      (MeasureTheory.convolution F G (ContinuousLinearMap.mul ℂ ℂ)) :=
    hF.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hG
  have hmc : MellinConvergent (logMellinConvolution f g) s := by
    rw [mellinConvergent_iff_negLogIntegrable]
    convert hconv using 1
    funext u
    exact weighted_logMellinConvolution_eq_convolution f g s u
  refine ⟨hmc, ?_⟩
  rw [mellin_eq_negLogIntegral]
  simp_rw [weighted_logMellinConvolution_eq_convolution f g s]
  rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hF hG]
  change (∫ u, F u) * (∫ u, G u) = _
  rw [← mellin_eq_negLogIntegral f s, ← mellin_eq_negLogIntegral g s]

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.mellin_eq_negLogIntegral
#print axioms CriticalLinePhasor.GlobalHelix.mellinConvergent_iff_negLogIntegrable
#print axioms CriticalLinePhasor.GlobalHelix.logMellinConvolution_hasMellin
