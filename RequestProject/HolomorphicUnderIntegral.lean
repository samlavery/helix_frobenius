import Mathlib

/-!
# Holomorphy of a parametric integral from a locally-uniform integrable bound

The reusable analytic core of `RSPoleStructure`'s gap (i): if, for a.e. `a`, the family
`s ↦ F s a` is holomorphic on a ball and dominated there by an integrable `bound a`, then the
parametric integral `s ↦ ∫ a, F s a` is holomorphic.

The point is that **only a bound on `F` itself is needed** — not on its derivative.  The derivative
bound the standard parametric-integral lemma
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) requires is manufactured internally by a
**Cauchy estimate** (`norm_cderiv_le`, `cderiv_eq_deriv`): on a slightly smaller ball the derivative
is bounded by `2/r · bound a`.  The measurability of the (formula-free) derivative
`a ↦ deriv (F · a) s₀` is obtained as a **difference-quotient limit** (`HasDerivAt.tendsto_slope`,
`aestronglyMeasurable_of_tendsto_ae`), so no closed form for the derivative is assumed — which is
exactly why it applies to the abstract completed-`L` entire part `Λ₀`, unlike Mathlib's Mellin
proof (whose derivative `t^{s-1}·log t` is explicit).

This is the input `RSPoleStructure.lean` names as "(i) holomorphy of
`s ↦ ∫_𝒟 P·Λ₀_z(s) dμ`"; the note there that it is "not in Mathlib" is discharged here.

No `axiom`, no `sorry`.
-/

open MeasureTheory Complex Metric Filter Topology Set

/-- **Holomorphy of a parametric integral from pointwise holomorphy and an integrable dominating
bound on `F` (no derivative bound needed).**  If for a.e. `a` the map `s ↦ F s a` is holomorphic on
`ball s₀ R` and bounded there by the integrable `bound a`, then `s ↦ ∫ a, F s a ∂μ` is
differentiable (holomorphic) at `s₀`. -/
theorem differentiableAt_integral_of_dominated_holo
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℂ → α → ℂ) (bound : α → ℝ) {s₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hFmeas : ∀ s ∈ ball s₀ R, AEStronglyMeasurable (F s) μ)
    (hFholo : ∀ᵐ a ∂μ, DifferentiableOn ℂ (fun s => F s a) (ball s₀ R))
    (hFbound : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ R, ‖F s a‖ ≤ bound a)
    (hbound_int : Integrable bound μ) :
    DifferentiableAt ℂ (fun s => ∫ a, F s a ∂μ) s₀ := by
  set r : ℝ := R / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; exact half_pos hR
  set G : ℂ → α → ℂ := fun s a => deriv (fun s => F s a) s with hG_def
  have hballr : ball s₀ r ∈ 𝓝 s₀ := ball_mem_nhds _ hr
  have hs₀R : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) μ := by
    filter_upwards [ball_mem_nhds s₀ hR] with s hs using hFmeas s hs
  have hF_int : Integrable (F s₀) μ := by
    refine hbound_int.mono' (hFmeas s₀ hs₀R) ?_
    filter_upwards [hFbound] with a ha using ha s₀ hs₀R
  set c : ℕ → ℂ := fun n => ((r / 2) / (n + 1) : ℝ) with hc_def
  have hcpos : ∀ n : ℕ, 0 < ((r / 2) / (n + 1) : ℝ) :=
    fun n => div_pos (half_pos hr) (by positivity)
  have hcmem : ∀ n, s₀ + c n ∈ ball s₀ R := by
    intro n
    have hlt : ‖c n‖ < R := by
      simp only [hc_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcpos n).le]
      have h1 : (r / 2) / ((n : ℝ) + 1) ≤ r / 2 :=
        div_le_self (half_pos hr).le (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have h2 : r / 2 < R := by rw [hr_def]; linarith
      linarith
    rw [mem_ball, dist_eq, show s₀ + c n - s₀ = c n by ring]
    exact hlt
  have hcne : ∀ n, s₀ + c n ≠ s₀ := by
    intro n h
    have hc0 : c n = 0 := by linear_combination h
    simp only [hc_def] at hc0
    exact (hcpos n).ne' (Complex.ofReal_eq_zero.mp hc0)
  have hc_tendsto0 : Tendsto c atTop (𝓝 (0 : ℂ)) := by
    have hg : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => ((r / 2) / ((n : ℝ) + 1))) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hg
    have h1 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h0
    rw [Complex.ofReal_zero] at h1
    exact h1
  have hctendsto : Tendsto (fun n => s₀ + c n) atTop (𝓝[≠] s₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · simpa using tendsto_const_nhds.add hc_tendsto0
    · simp only [mem_compl_iff, mem_singleton_iff]; exact hcne n
  have hG_meas : AEStronglyMeasurable (G s₀) μ := by
    have hseq : ∀ n : ℕ, AEStronglyMeasurable
        (fun a => slope (fun s => F s a) s₀ (s₀ + c n)) μ := by
      intro n
      have he : (fun a => slope (fun s => F s a) s₀ (s₀ + c n))
          = fun a => (F (s₀ + c n) a - F s₀ a) * (c n)⁻¹ := by
        funext a
        rw [slope_def_field, show (s₀ + c n) - s₀ = c n by ring, div_eq_mul_inv]
      rw [he]
      exact ((hFmeas _ (hcmem n)).sub (hFmeas s₀ hs₀R)).mul_const _
    have htend : ∀ᵐ a ∂μ, Tendsto (fun n => slope (fun s => F s a) s₀ (s₀ + c n))
        atTop (𝓝 (G s₀ a)) := by
      filter_upwards [hFholo] with a ha
      have hda : HasDerivAt (fun s => F s a) (G s₀ a) s₀ :=
        (ha.differentiableAt (isOpen_ball.mem_nhds hs₀R)).hasDerivAt
      exact hda.tendsto_slope.comp hctendsto
    exact aestronglyMeasurable_of_tendsto_ae atTop hseq htend
  have h_bound : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ r, ‖G s a‖ ≤ (2 / r) * bound a := by
    filter_upwards [hFholo, hFbound] with a ha hb
    intro s hs
    have hsub : closedBall s (r / 2) ⊆ ball s₀ R := by
      intro w hw
      rw [mem_closedBall] at hw; rw [mem_ball] at hs ⊢
      calc dist w s₀ ≤ dist w s + dist s s₀ := dist_triangle w s s₀
        _ ≤ r / 2 + r := by linarith [hw, hs.le]
        _ < R := by rw [hr_def]; linarith
    have hcd : cderiv (r / 2) (fun s => F s a) s = deriv (fun s => F s a) s :=
      cderiv_eq_deriv isOpen_ball ha (by positivity) hsub
    have hsphere : ∀ w ∈ sphere s (r / 2), ‖F w a‖ ≤ bound a :=
      fun w hw => hb w (hsub (sphere_subset_closedBall hw))
    have hcderiv := norm_cderiv_le (f := fun s => F s a) (z := s) (r := r / 2)
      (M := bound a) (by positivity) hsphere
    rw [hcd] at hcderiv
    calc ‖G s a‖ = ‖deriv (fun s => F s a) s‖ := rfl
      _ ≤ bound a / (r / 2) := hcderiv
      _ = (2 / r) * bound a := by ring
  have h_diff : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ r, HasDerivAt (fun s => F s a) (G s a) s := by
    filter_upwards [hFholo] with a ha
    intro s hs
    have hsR : s ∈ ball s₀ R := ball_subset_ball (by rw [hr_def]; linarith) hs
    exact (ha.differentiableAt (isOpen_ball.mem_nhds hsR)).hasDerivAt
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hballr hF_meas hF_int hG_meas h_bound (hbound_int.const_mul (2 / r)) h_diff
  exact main.2.differentiableAt

#print axioms differentiableAt_integral_of_dominated_holo
