import RequestProject.ArgumentPrincipleRectangle

/-!
# Contour shift with residues — the Perron shift step, from compiled rectangle primitives

The Perron argument passes from the meromorphic continuation of a Dirichlet series to a summatory
bound by **shifting a vertical contour past the pole line and collecting the residue**.  That shift
is often cited as "not in Mathlib"; it is not a gap here — it assembles directly from two compiled
rectangle facts:

* Cauchy–Goursat vanishing on a holomorphic rectangle
  (`rectangleBoundaryIntegral_eq_zero_of_differentiableOn`), and
* the inverse-kernel residue `∮ ∑_ρ w_ρ/(z-ρ) = 2πi·∑_ρ w_ρ`
  (`rectangleBoundaryIntegral_weighted_divisor`),

glued by boundary-integral additivity.  The result, `rectangleBoundaryIntegral_holo_add_residues`,
is the residue theorem for finitely many simple poles inside a rectangle: it is exactly the
contour-shift identity used in Perron's method (the difference of the two vertical legs, plus the
horizontal legs, equals `2πi` times the enclosed residues).

This isolates the genuinely-cited remainder of the symmetric-power cancellation to the **Perron
summation identity** alone (the sharp-cutoff ↔ contour-integral representation of the partial sum);
the contour shift, the residue, the meromorphic continuation, the functional equation, the pole
structure, and the entire-part holomorphy (`RSEntireHolo.rs_entirePart_differentiable`) are all
compiled.  No RH/GRH.
-/

open Complex Set MeasureTheory
open scoped Interval Real

namespace CriticalLinePhasor.ContourArgument

/-- **Residue theorem for simple poles in a rectangle = the Perron contour shift.**
If `g` is holomorphic on the closed rectangle `[a,b] × [c,d]` and `ρ ∈ S` are finitely many points
strictly interior with residues `w ρ`, then the boundary integral of `g + ∑_ρ w_ρ/(·-ρ)` equals
`2πi·∑_ρ w_ρ`.  Assembled from the compiled Cauchy–Goursat vanishing and inverse-kernel residue —
the contour-shift step of Perron's method, discharged from in-tree machinery. -/
theorem rectangleBoundaryIntegral_holo_add_residues
    (g : ℂ → ℂ) (S : Finset ℂ) (w : ℂ → ℂ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hg : DifferentiableOn ℂ g (Icc a b ×ℂ Icc c d))
    (hS : ∀ ρ ∈ S, a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d) :
    rectangleBoundaryIntegral (fun z => g z + ∑ ρ ∈ S, w ρ * (z - ρ)⁻¹) a b c d
      = (2 * Real.pi * I) * ∑ ρ ∈ S, w ρ := by
  have hgc : ContinuousOn g (Icc a b ×ℂ Icc c d) := hg.continuousOn
  -- `g` restricted to a horizontal edge at height `t ∈ [c,d]` is interval-integrable
  have hgH : ∀ t : ℝ, c ≤ t → t ≤ d →
      IntervalIntegrable (fun x : ℝ => g (↑x + ↑t * I)) volume a b := by
    intro t htc htd
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    refine hgc.comp (by fun_prop : Continuous fun x : ℝ => (↑x + ↑t * I : ℂ)).continuousOn ?_
    intro x hx
    rw [mem_reProdIm]
    refine ⟨by simpa using hx, ?_⟩
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, mem_Icc]
    exact ⟨htc, htd⟩
  -- `g` restricted to a vertical edge at abscissa `s ∈ [a,b]` is interval-integrable
  have hgV : ∀ s : ℝ, a ≤ s → s ≤ b →
      IntervalIntegrable (fun y : ℝ => g (↑s + ↑y * I)) volume c d := by
    intro s hsa hsb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    refine hgc.comp (by fun_prop : Continuous fun y : ℝ => (↑s + ↑y * I : ℂ)).continuousOn ?_
    intro y hy
    rw [mem_reProdIm]
    refine ⟨?_, by simpa using hy⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, mem_Icc]
    exact ⟨hsa, hsb⟩
  -- the residue kernel restricted to a horizontal edge off the poles is continuous
  have hrH : ∀ t : ℝ, (∀ ρ ∈ S, t ≠ ρ.im) →
      Continuous (fun x : ℝ => ∑ ρ ∈ S, w ρ * ((↑x + ↑t * I) - ρ)⁻¹) := by
    intro t ht
    refine continuous_finset_sum S (fun ρ hρ => continuous_const.mul
      (Continuous.inv₀ (by fun_prop) (fun x hx0 => ht ρ hρ ?_)))
    have him := congrArg Complex.im (sub_eq_zero.mp hx0)
    simpa using him
  -- the residue kernel restricted to a vertical edge off the poles is continuous
  have hrV : ∀ s : ℝ, (∀ ρ ∈ S, s ≠ ρ.re) →
      Continuous (fun y : ℝ => ∑ ρ ∈ S, w ρ * ((↑s + ↑y * I) - ρ)⁻¹) := by
    intro s hs
    refine continuous_finset_sum S (fun ρ hρ => continuous_const.mul
      (Continuous.inv₀ (by fun_prop) (fun y hy0 => hs ρ hρ ?_)))
    have hre := congrArg Complex.re (sub_eq_zero.mp hy0)
    simpa using hre
  rw [rectangleBoundaryIntegral_add_of_intervalIntegrable g
        (fun z => ∑ ρ ∈ S, w ρ * (z - ρ)⁻¹) a b c d
      (hgH c le_rfl hcd)
      ((hrH c (fun ρ hρ => ne_of_lt (hS ρ hρ).2.2.1)).intervalIntegrable a b)
      (hgH d hcd le_rfl)
      ((hrH d (fun ρ hρ => ne_of_gt (hS ρ hρ).2.2.2)).intervalIntegrable a b)
      (hgV b hab le_rfl)
      ((hrV b (fun ρ hρ => ne_of_gt (hS ρ hρ).2.1)).intervalIntegrable c d)
      (hgV a le_rfl hab)
      ((hrV a (fun ρ hρ => ne_of_lt (hS ρ hρ).1)).intervalIntegrable c d),
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn g a b c d hab hcd hg, zero_add]
  exact rectangleBoundaryIntegral_weighted_divisor S w hS

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.rectangleBoundaryIntegral_holo_add_residues
