import RequestProject.FlowRealSection

/-!
# Descending in the warp parameter strictly increases the section at a would-be double zero

If `∂_x²Ξ_{λ₀}(x₀) = c > 0`, then `∂_λ xiR = jR` is `≤ −c/2` on a whole rectangle around `(λ₀, x₀)`
(continuity in `x` plus the uniform Lipschitz bound in `λ`).  Hence `s ↦ xiR s x` is strictly
ANTITONE there, so `xiR λ x > xiR λ₀ x` for every `λ < λ₀` in the rectangle — no integration needed.
-/

open Complex Filter Topology Set

namespace CriticalLinePhasor.XiKernel

/-- The `λ`-derivative is uniformly negative on a rectangle around `(λ₀, x₀)`. -/
theorem jR_neg_on_rect {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ ≤ 1) {x₀ : ℝ}
    (hc : 0 < (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ s ∈ Icc (lam₀ - δ) lam₀, ∀ x : ℝ, |x - x₀| ≤ r →
        jR s x ≤ -((deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) / 2 := by
  set c : ℝ := (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re with hcdef
  have hj0 : jR lam₀ x₀ = -c := jR_eq_neg_deriv2 h0.le h1 x₀
  -- continuity in `x`
  have hcont := continuous_jR_snd h0.le h1
  have hxcont : ∀ᶠ x in 𝓝 x₀, |jR lam₀ x - jR lam₀ x₀| < c / 4 := by
    have := (hcont.tendsto x₀).eventually
      (eventually_abs_sub_lt (jR lam₀ x₀) (by positivity : (0:ℝ) < c / 4))
    exact this
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp hxcont
  -- Lipschitz in `λ`
  obtain ⟨C, hC, hlip⟩ := jR_lipschitz h1 h0.le
  set δ : ℝ := min (lam₀ / 2) (c / (4 * (C + 1))) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδlt : δ < lam₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨r / 2, δ, by positivity, hδpos, hδlt, ?_⟩
  intro s hs x hx
  have hs0 : 0 ≤ s := by
    have := hs.1
    have : lam₀ - δ ≤ s := this
    linarith [hδlt]
  have hsl : s ≤ lam₀ := hs.2
  -- the `x`-step
  have hx' : |jR lam₀ x - jR lam₀ x₀| < c / 4 := by
    refine hr ?_
    rw [Real.dist_eq]
    calc |x - x₀| ≤ r / 2 := hx
      _ < r := by linarith
  -- the `λ`-step
  have hs' : |jR s x - jR lam₀ x| ≤ |s - lam₀| * C :=
    hlip s lam₀ hs0 h0.le hsl le_rfl x
  have hsd : |s - lam₀| ≤ δ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [hs.1]
  have hCbd : |s - lam₀| * C ≤ c / 4 := by
    have h1' : |s - lam₀| * C ≤ δ * C := mul_le_mul_of_nonneg_right hsd hC
    have h2' : δ * C ≤ (c / (4 * (C + 1))) * C := by
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) hC
    have h3' : (c / (4 * (C + 1))) * C ≤ c / 4 := by
      have hCp : (0:ℝ) < 4 * (C + 1) := by linarith
      have hnn : (0:ℝ) ≤ c / (4 * (C + 1)) := div_nonneg hc.le hCp.le
      have key : c / 4 - (c / (4 * (C + 1))) * C = c / (4 * (C + 1)) := by
        field_simp
        ring
      linarith
    linarith
  -- combine
  have : jR s x ≤ jR lam₀ x₀ + c / 4 + c / 4 := by
    have a1 : jR s x - jR lam₀ x ≤ |jR s x - jR lam₀ x| := le_abs_self _
    have a2 : jR lam₀ x - jR lam₀ x₀ ≤ |jR lam₀ x - jR lam₀ x₀| := le_abs_self _
    linarith
  rw [hj0] at this
  linarith

/-- **Descending in `λ` strictly raises the section**, on the rectangle where `jR < 0`. -/
theorem xiR_lt_of_lam_lt {lam₀ : ℝ} (h0 : 0 < lam₀) (h1 : lam₀ < 1) {x₀ : ℝ}
    (hc : 0 < (deriv (deriv (flowStage lam₀)) (x₀ : ℂ)).re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ δ < lam₀ ∧
      ∀ x : ℝ, |x - x₀| ≤ r → ∀ lam ∈ Ico (lam₀ - δ) lam₀, xiR lam₀ x < xiR lam x := by
  obtain ⟨r, δ, hr, hδ, hδl, hrect⟩ := jR_neg_on_rect h0 h1.le hc
  refine ⟨r, δ, hr, hδ, hδl, ?_⟩
  intro x hx lam hlam
  set D : Set ℝ := Icc (lam₀ - δ) lam₀ with hD
  set lam₁ : ℝ := (lam₀ + 1) / 2 with hl1
  have hl1lt : lam₀ < lam₁ := by rw [hl1]; linarith
  have hl1le : lam₁ ≤ 1 := by rw [hl1]; linarith
  have hderiv : ∀ s ∈ D, HasDerivAt (fun t : ℝ => xiR t x) (jR s x) s := by
    intro s hs
    have hs0 : 0 ≤ s := by have := hs.1; linarith
    exact hasDerivAt_xiR_lam hs0 (lt_of_le_of_lt hs.2 hl1lt) hl1le x
  have hcontD : ContinuousOn (fun t : ℝ => xiR t x) D := fun s hs =>
    ((hderiv s hs).continuousAt).continuousWithinAt
  have hnegD : ∀ s ∈ interior D, deriv (fun t : ℝ => xiR t x) s < 0 := by
    intro s hs
    rw [hD, interior_Icc] at hs
    have hsD : s ∈ D := ⟨hs.1.le, hs.2.le⟩
    rw [(hderiv s hsD).deriv]
    have := hrect s hsD x hx
    linarith
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontD hnegD
  exact hanti ⟨hlam.1, le_of_lt hlam.2⟩ ⟨by linarith [hδ], le_rfl⟩ hlam.2

end CriticalLinePhasor.XiKernel

#print axioms CriticalLinePhasor.XiKernel.jR_neg_on_rect
#print axioms CriticalLinePhasor.XiKernel.xiR_lt_of_lam_lt
