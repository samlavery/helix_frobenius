import RequestProject.FlowLamAnti

/-!
# At a double zero the section is nonnegative nearby

If `xiR λ₀` has `xiR = 0`, `∂xiR = 0` and `∂²xiR = c > 0` at `x₀`, then `∂²xiR > 0` on a neighbourhood
(continuity), so `∂xiR` is strictly increasing there and vanishes at `x₀`; hence `xiR λ₀` decreases to
the left of `x₀` and increases to the right, so `xiR λ₀ ≥ xiR λ₀ x₀ = 0` nearby.  Convexity, no Taylor
remainder needed.
-/

open Complex Filter Topology Set

namespace CriticalLinePhasor.XiKernel

theorem differentiable_deriv_flowStage {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Differentiable ℂ (deriv (flowStage lam)) := by
  have hA : AnalyticOnNhd ℂ (flowStage lam) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_flowStage h0 h1)
  exact fun z => ((hA z (Set.mem_univ z)).deriv).differentiableAt

theorem hasDerivAt_xiR_fst {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    HasDerivAt (xiR lam) ((deriv (flowStage lam) (x : ℂ)).re) x :=
  ((differentiable_flowStage h0 h1 ((x : ℝ) : ℂ)).hasDerivAt).real_of_complex

theorem deriv_xiR_eq {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    deriv (xiR lam) = fun y : ℝ => (deriv (flowStage lam) (y : ℂ)).re :=
  funext fun y => (hasDerivAt_xiR_fst h0 h1 y).deriv

theorem hasDerivAt_deriv_xiR {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    HasDerivAt (deriv (xiR lam)) ((deriv (deriv (flowStage lam)) (x : ℂ)).re) x := by
  rw [deriv_xiR_eq h0 h1]
  exact ((differentiable_deriv_flowStage h0 h1 ((x : ℝ) : ℂ)).hasDerivAt).real_of_complex

theorem deriv2_xiR_eq {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (x : ℝ) :
    deriv (deriv (xiR lam)) x = (deriv (deriv (flowStage lam)) (x : ℂ)).re :=
  (hasDerivAt_deriv_xiR h0 h1 x).deriv

/-- **A double zero with positive curvature is a local minimum with value `0`.** -/
theorem xiR_nonneg_near {lam₀ : ℝ} (h0 : 0 ≤ lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hval : xiR lam₀ x₀ = 0) (hd : deriv (xiR lam₀) x₀ = 0)
    (hc : 0 < (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, |x - x₀| ≤ ρ → 0 ≤ xiR lam₀ x := by
  have hd2 : Differentiable ℂ (deriv (deriv (flowStage lam₀))) := by
    have hA2 : AnalyticOnNhd ℂ (deriv (flowStage lam₀)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_deriv_flowStage h0 h1)
    exact fun z => ((hA2 z (Set.mem_univ z)).deriv).differentiableAt
  have hcont : Continuous (fun y : ℝ => (deriv (deriv (flowStage lam₀)) (y : ℂ)).re) :=
    Complex.continuous_re.comp (hd2.continuous.comp Complex.continuous_ofReal)
  have hpos : ∀ᶠ y : ℝ in 𝓝 x₀, 0 < (deriv (deriv (flowStage lam₀)) ((y : ℝ) : ℂ)).re :=
    (hcont.tendsto x₀).eventually (eventually_gt_nhds hc)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff.mp hpos
  have hxiDiff : Differentiable ℝ (xiR lam₀) := fun y =>
    (hasDerivAt_xiR_fst h0 h1 y).differentiableAt
  refine ⟨ρ₀ / 2, by positivity, ?_⟩
  intro x hx
  have hmemD : ∀ y ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2), dist y x₀ < ρ₀ := by
    intro y hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have hderiv2 : ∀ y ∈ interior (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)),
      0 < deriv (deriv (xiR lam₀)) y := by
    intro y hy
    rw [interior_Icc] at hy
    rw [deriv2_xiR_eq h0 h1]
    exact hball (hmemD y ⟨hy.1.le, hy.2.le⟩)
  have hcontD : ContinuousOn (deriv (xiR lam₀)) (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)) := fun y _ =>
    ((hasDerivAt_deriv_xiR h0 h1 y).continuousAt).continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)) hcontD hderiv2
  have hxD : x ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by
    obtain ⟨h1', h2'⟩ := abs_le.mp hx
    constructor <;> [linarith; linarith]
  have hx₀D : x₀ ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by constructor <;> linarith
  rcases le_total x x₀ with hle | hle
  · have hsub : Icc x x₀ ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hxD.1 hx₀D.2
    have hnp : ∀ y ∈ interior (Icc x x₀), deriv (xiR lam₀) y ≤ 0 := by
      intro y hy
      rw [interior_Icc] at hy
      have := hmono (hsub ⟨hy.1.le, hy.2.le⟩) hx₀D hy.2
      rw [hd] at this
      linarith
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc x x₀)
      (hxiDiff.continuous.continuousOn) (hxiDiff.differentiableOn) hnp
    have := hanti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [hval] at this
    linarith
  · have hsub : Icc x₀ x ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hx₀D.1 hxD.2
    have hnn : ∀ y ∈ interior (Icc x₀ x), 0 ≤ deriv (xiR lam₀) y := by
      intro y hy
      rw [interior_Icc] at hy
      have := hmono hx₀D (hsub ⟨hy.1.le, hy.2.le⟩) hy.1
      rw [hd] at this
      linarith
    have hmon := monotoneOn_of_deriv_nonneg (convex_Icc x₀ x)
      (hxiDiff.continuous.continuousOn) (hxiDiff.differentiableOn) hnn
    have := hmon (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [hval] at this
    linarith

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.xiR_nonneg_near
