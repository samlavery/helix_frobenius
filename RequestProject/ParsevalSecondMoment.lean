import RequestProject.HeckeCoeffBound
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Parseval second moment: Rankin's average bound from pure modularity

For a level-one cusp form `f` of weight `k`, the horizontal Fourier coefficients at height `y`
satisfy the second-moment bound

  `∑' i, ‖c_i(y)‖² ≤ M · y^{-k}`,

by Parseval on the unit interval (`tsum_sq_fourierCoeffOn`) against the compiled pointwise bound
`|f(x+iy)|² ≤ M·y^{-k}` (`hecke_pointwise`).  Since the horizontal Fourier coefficients are the
exponentially-weighted `q`-coefficients (`c_n(y) = a_n e^{-2πny}`, the coefficient-integral
identification), this is Rankin's average bound — the second-moment input of the `r = 2`
pair-dilation estimate — obtained with no Eisenstein continuation, no Rankin–Selberg unfolding,
and no tower input: modularity in, moment bound out.  No RH/GRH.
-/

open UpperHalfPlane Complex Filter MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The horizontal restriction of a form at height `y` is continuous. -/
lemma horizontal_continuous (f : CuspForm 𝒮ℒ k) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) := by
  apply (CuspFormClass.holo f).continuous.comp
  apply continuous_induced_rng.mpr
  show Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
  fun_prop

/-- **The Parseval second moment.**  The horizontal Fourier coefficients of a level-one cusp
form at height `y` have total square mass at most `M·y^{-k}` — Rankin's average bound, from
Parseval against the compiled pointwise bound. -/
theorem parseval_second_moment (f : CuspForm 𝒮ℒ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, ∀ hy : 0 < y,
      ∑' i : ℤ, ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1)
          (fun x : ℝ => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)) i‖ ^ 2
        ≤ M * y ^ (-k) := by
  obtain ⟨M, hM⟩ := hecke_pointwise f
  have hMnn : 0 ≤ M := hecke_pointwise_const_nonneg f hM
  refine ⟨M, hMnn, fun y hy => ?_⟩
  set g : ℝ → ℂ := fun x => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) with hg_def
  have hgc : Continuous g := horizontal_continuous f hy
  -- the pointwise square bound along the horizontal line
  have hgb : ∀ x : ℝ, ‖g x‖ ^ 2 ≤ M * y ^ (-k) := by
    intro x
    have h := hM (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)
    rw [Complex.normSq_eq_norm_sq] at h
    have himz : (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by
      simp [UpperHalfPlane.im]
    rwa [himz] at h
  -- membership in L² on the unit interval
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Ioc]
  have hL2 : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply MemLp.of_bound hgc.aestronglyMeasurable (Real.sqrt (M * y ^ (-k)))
    apply Filter.Eventually.of_forall
    intro x
    calc ‖g x‖ = Real.sqrt (‖g x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (M * y ^ (-k)) := Real.sqrt_le_sqrt (hgb x)
  -- Parseval + the integral bound
  rw [tsum_sq_fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) hL2]
  have hint : (∫ x in (0:ℝ)..1, ‖g x‖ ^ 2) ≤ M * y ^ (-k) := by
    calc (∫ x in (0:ℝ)..1, ‖g x‖ ^ 2) ≤ ∫ _x in (0:ℝ)..1, M * y ^ (-k) := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · exact (hgc.norm.pow 2).intervalIntegrable 0 1
          · exact intervalIntegrable_const
          · intro x _
            exact hgb x
      _ = M * y ^ (-k) := by simp
  calc ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖g x‖ ^ 2
      = ∫ x in (0:ℝ)..1, ‖g x‖ ^ 2 := by norm_num
    _ ≤ M * y ^ (-k) := hint

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.parseval_second_moment
