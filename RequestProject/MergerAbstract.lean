import Mathlib

/-!
# The merger argument's two analysis lemmas, in abstract form

Neither step of the merger argument mentions the flow.  Both are statements about a real function of
two variables whose `s`-derivative is `j`:

* `deriv_neg_on_rect` — if `j s₀ x₀ < 0`, `j` is Lipschitz in `s` uniformly in `x`, and `j s₀` is
  continuous, then `j ≤ j s₀ x₀ / 2 < 0` on a rectangle around `(s₀, x₀)`;
* `lt_of_lt_of_deriv_neg` — on such a rectangle `s ↦ G s x` is strictly antitone, so descending in `s`
  strictly raises `G`;
* `nonneg_near_of_deriv2_pos` — a real function with `f = f' = 0` and `f'' > 0` at `x₀`, with `f''`
  continuous, is `≥ 0` near `x₀`.

Stating them here, free of `flowStage`, is what allows the same argument to be re-run on the
derivatives `∂_z^kΞ_λ` when the order of a zero exceeds two.
-/

open Filter Topology Set

namespace CriticalLinePhasor.Merger

/-- The `s`-derivative stays negative on a rectangle. -/
theorem deriv_neg_on_rect {j : ℝ → ℝ → ℝ} {s₀ x₀ C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ s s' x : ℝ, |j s x - j s' x| ≤ |s - s'| * C)
    (hcont : Continuous (j s₀)) (hneg : j s₀ x₀ < 0) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ s : ℝ, |s - s₀| ≤ δ → ∀ x : ℝ, |x - x₀| ≤ r → j s x ≤ j s₀ x₀ / 2 := by
  set c : ℝ := -(j s₀ x₀) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hxcont : ∀ᶠ x in 𝓝 x₀, |j s₀ x - j s₀ x₀| < c / 4 :=
    (hcont.tendsto x₀).eventually
      (eventually_abs_sub_lt (j s₀ x₀) (by positivity : (0:ℝ) < c / 4))
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp hxcont
  refine ⟨r / 2, c / (4 * (C + 1)), by positivity, by positivity, ?_⟩
  intro s hs x hx
  have hx' : |j s₀ x - j s₀ x₀| < c / 4 := by
    refine hr ?_
    rw [Real.dist_eq]
    calc |x - x₀| ≤ r / 2 := hx
      _ < r := by linarith
  have hs' : |j s x - j s₀ x| ≤ |s - s₀| * C := hlip s s₀ x
  have hCbd : |s - s₀| * C ≤ c / 4 := by
    have h1 : |s - s₀| * C ≤ (c / (4 * (C + 1))) * C := mul_le_mul_of_nonneg_right hs hC
    have hCp : (0:ℝ) < 4 * (C + 1) := by linarith
    have hnn : (0:ℝ) ≤ c / (4 * (C + 1)) := div_nonneg hcpos.le hCp.le
    have key : c / 4 - (c / (4 * (C + 1))) * C = c / (4 * (C + 1)) := by field_simp; ring
    linarith
  have a1 : j s x - j s₀ x ≤ |j s x - j s₀ x| := le_abs_self _
  have a2 : j s₀ x - j s₀ x₀ ≤ |j s₀ x - j s₀ x₀| := le_abs_self _
  linarith [hcdef]

/-- Descending in `s` strictly raises `G`, wherever the `s`-derivative is negative. -/
theorem lt_of_lt_of_deriv_neg {G j : ℝ → ℝ → ℝ} {s₀ δ x : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ s ∈ Icc (s₀ - δ) s₀, HasDerivAt (fun t : ℝ => G t x) (j s x) s)
    (hneg : ∀ s ∈ Icc (s₀ - δ) s₀, j s x < 0) :
    ∀ s ∈ Ico (s₀ - δ) s₀, G s₀ x < G s x := by
  intro s hs
  have hcontD : ContinuousOn (fun t : ℝ => G t x) (Icc (s₀ - δ) s₀) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hnegD : ∀ t ∈ interior (Icc (s₀ - δ) s₀), deriv (fun u : ℝ => G u x) t < 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have htD : t ∈ Icc (s₀ - δ) s₀ := ⟨ht.1.le, ht.2.le⟩
    rw [(hderiv t htD).deriv]
    exact hneg t htD
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontD hnegD
  exact hanti ⟨hs.1, le_of_lt hs.2⟩ ⟨by linarith, le_rfl⟩ hs.2

/-- A real function with a double zero of positive curvature is `≥ 0` nearby. -/
theorem nonneg_near_of_deriv2_pos {f f' f'' : ℝ → ℝ} {x₀ : ℝ}
    (hd1 : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hcont : Continuous f'') (h0 : f x₀ = 0) (h1 : f' x₀ = 0) (h2 : 0 < f'' x₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, |x - x₀| ≤ ρ → 0 ≤ f x := by
  have hpos : ∀ᶠ y in 𝓝 x₀, 0 < f'' y := (hcont.tendsto x₀).eventually (eventually_gt_nhds h2)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff.mp hpos
  refine ⟨ρ₀ / 2, by positivity, ?_⟩
  intro x hx
  have hmemD : ∀ y ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2), dist y x₀ < ρ₀ := by
    intro y hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have hderiv2 : ∀ y ∈ interior (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)), 0 < deriv f' y := by
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd2 y).deriv]
    exact hball (hmemD y ⟨hy.1.le, hy.2.le⟩)
  have hcontD : ContinuousOn f' (Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2)) := fun y _ =>
    ((hd2 y).continuousAt).continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcontD hderiv2
  have hfDiff : Differentiable ℝ f := fun y => (hd1 y).differentiableAt
  have hxD : x ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by
    obtain ⟨ha, hb⟩ := abs_le.mp hx; constructor <;> [linarith; linarith]
  have hx₀D : x₀ ∈ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := by constructor <;> linarith
  have hderivf : deriv f = f' := funext fun y => (hd1 y).deriv
  rcases le_total x x₀ with hle | hle
  · have hsub : Icc x x₀ ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hxD.1 hx₀D.2
    have hnp : ∀ y ∈ interior (Icc x x₀), deriv f y ≤ 0 := by
      intro y hy
      rw [interior_Icc] at hy
      have := hmono (hsub ⟨hy.1.le, hy.2.le⟩) hx₀D hy.2
      rw [hderivf, h1] at *
      linarith
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc x x₀)
      (hfDiff.continuous.continuousOn) (hfDiff.differentiableOn) hnp
    have := hanti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [h0] at this; linarith
  · have hsub : Icc x₀ x ⊆ Icc (x₀ - ρ₀ / 2) (x₀ + ρ₀ / 2) := Icc_subset_Icc hx₀D.1 hxD.2
    have hnn : ∀ y ∈ interior (Icc x₀ x), 0 ≤ deriv f y := by
      intro y hy
      rw [interior_Icc] at hy
      have := hmono hx₀D (hsub ⟨hy.1.le, hy.2.le⟩) hy.1
      rw [hderivf, h1] at *
      linarith
    have hmon := monotoneOn_of_deriv_nonneg (convex_Icc x₀ x)
      (hfDiff.continuous.continuousOn) (hfDiff.differentiableOn) hnn
    have := hmon (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    rw [h0] at this; linarith

end CriticalLinePhasor.Merger

#print axioms CriticalLinePhasor.Merger.deriv_neg_on_rect
#print axioms CriticalLinePhasor.Merger.lt_of_lt_of_deriv_neg
#print axioms CriticalLinePhasor.Merger.nonneg_near_of_deriv2_pos
