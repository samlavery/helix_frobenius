import Mathlib
import RequestProject.PerronReduction
import RequestProject.ArgumentPrincipleRectangle

/-!
# Track W1 — strip contours for a decaying entire test function (ledger 534)

The boundary of the vertical strip `a ≤ Re s ≤ b`, oriented as the limit of the positively
oriented rectangles `[a,b] × [−T,T]` (`rectangleBoundaryIntegral`): the right line upward, the
left line downward.

* `lineIntegral F σ = ∫ t, F(σ + it)`, `stripBoundary F a b = i·lineIntegral F b − i·lineIntegral F a`.
* `integrable_line_of_decay` — power decay `‖F(σ+it)‖ ≤ C/(1+|t|)^k`, `k ≥ 2`, makes the line
  integrands integrable (dominated by `C/(1+t²)`).
* `horizontal_tendsto_zero` — the horizontal segments vanish as `T → ∞`.
* `rectangle_tendsto_stripBoundary` — the rectangle boundary integrals converge to the strip
  boundary integral.
* `stripBoundary_eq_zero` — **strip Cauchy**: an entire decaying `F` has zero strip boundary.
* `stripBoundary_div_sub_eq` — **strip residue**: `∮_strip F(s)/(s−ρ) = 2πi F(ρ)` for `a < Re ρ < b`,
  from the compiled rectangle residue theorem (`rectangleBoundaryIntegral_holo_add_residues`) with
  the removable-singularity quotient `dslope F ρ` (Mathlib `differentiableOn_dslope`).

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The integral of `F` along the vertical line `Re s = σ`, upward. -/
def lineIntegral (F : ℂ → ℂ) (σ : ℝ) : ℂ := ∫ t : ℝ, F (σ + t * I)

/-- The boundary integral of the strip `a ≤ Re s ≤ b`, positively oriented: right line up, left
line down. -/
def stripBoundary (F : ℂ → ℂ) (a b : ℝ) : ℂ := I * lineIntegral F b - I * lineIntegral F a

/-- Power decay on a vertical line. -/
def LineDecay (F : ℂ → ℂ) (σ : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ C / (1 + |t|) ^ k

theorem one_add_abs_pow_ge {t : ℝ} {k : ℕ} (hk : 2 ≤ k) : 1 + t ^ 2 ≤ (1 + |t|) ^ k := by
  have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h2 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ k := pow_le_pow_right₀ h1 hk
  have h3 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith [abs_nonneg t]
  linarith

/-- Decay of order `k ≥ 2` is dominated by `C/(1+t²)`. -/
theorem lineDecay_le_inv_one_add_sq {F : ℂ → ℂ} {σ C : ℝ} {k : ℕ} (hk : 2 ≤ k) (hC : 0 ≤ C)
    (h : LineDecay F σ C k) (t : ℝ) : ‖F (σ + t * I)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  have h1 := h t
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hpow : 0 < (1 + |t|) ^ k := by positivity
  calc ‖F (σ + t * I)‖ ≤ C / (1 + |t|) ^ k := h1
    _ ≤ C / (1 + t ^ 2) := by
        apply div_le_div_of_nonneg_left hC hpos (one_add_abs_pow_ge hk)
    _ = C * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- A continuous line integrand with power decay of order `≥ 2` is integrable. -/
theorem integrable_line_of_decay {F : ℂ → ℂ} (hF : Continuous F) {σ C : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hC : 0 ≤ C) (h : LineDecay F σ C k) : Integrable (fun t : ℝ => F (σ + t * I)) := by
  have hg : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hg ?_ ?_
  · exact (hF.comp (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (lineDecay_le_inv_one_add_sq hk hC h)

/-- `C(b−a)/(1+T)^k → 0` for `k ≥ 1`. -/
theorem tendsto_const_div_one_add_pow {c : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun T : ℝ => c / (1 + T) ^ k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => 1 + T) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have h2 : Tendsto (fun T : ℝ => (1 + T) ^ k) atTop atTop :=
    (tendsto_pow_atTop (by omega : k ≠ 0)).comp h1
  exact tendsto_const_nhds.div_atTop h2

/-- The horizontal segment integrals vanish as `T → ∞` under uniform power decay on the strip. -/
theorem horizontal_tendsto_zero {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 1 ≤ k) (hab : a ≤ b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    Tendsto (fun T : ℝ => ∫ x in a..b, F (x + T * I)) atTop (𝓝 0) := by
  have hbound : ∀ T : ℝ, 0 ≤ T →
      ‖∫ x in a..b, F (x + T * I)‖ ≤ C / (1 + T) ^ k * (b - a) := by
    intro T hT
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + T * I)) (C := C / (1 + T) ^ k) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    · intro x hx
      have hx' : x ∈ Icc a b := by
        rw [uIoc_of_le hab] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have := hdec x hx' T
      rwa [abs_of_nonneg hT] at this
  have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ k * (b - a)) atTop (𝓝 0) := by
    have := (tendsto_const_div_one_add_pow (c := C) hk).mul_const (b - a)
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hbound T hT

/-- The horizontal segment at height `−T` also vanishes. -/
theorem horizontal_neg_tendsto_zero {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 1 ≤ k) (hab : a ≤ b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    Tendsto (fun T : ℝ => ∫ x in a..b, F (x + (-T : ℝ) * I)) atTop (𝓝 0) := by
  have hdec' : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k := hdec
  have hbound : ∀ T : ℝ, 0 ≤ T →
      ‖∫ x in a..b, F (x + (-T : ℝ) * I)‖ ≤ C / (1 + T) ^ k * (b - a) := by
    intro T hT
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + (-T : ℝ) * I)) (C := C / (1 + T) ^ k) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    · intro x hx
      have hx' : x ∈ Icc a b := by
        rw [uIoc_of_le hab] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have := hdec' x hx' (-T)
      rwa [abs_neg, abs_of_nonneg hT] at this
  have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ k * (b - a)) atTop (𝓝 0) := by
    have := (tendsto_const_div_one_add_pow (c := C) hk).mul_const (b - a)
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hbound T hT

/-- The rectangle boundary integrals `[a,b] × [−T,T]` converge to the strip boundary integral. -/
theorem rectangle_tendsto_stripBoundary {F : ℂ → ℂ} {a b : ℝ}
    (hia : Integrable (fun t : ℝ => F (a + t * I)))
    (hib : Integrable (fun t : ℝ => F (b + t * I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + (-T : ℝ) * I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => rectangleBoundaryIntegral F a b (-T) T) atTop
      (𝓝 (stripBoundary F a b)) := by
  have hva : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (a + y * I)) atTop (𝓝 (lineIntegral F a)) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (b + y * I)) atTop (𝓝 (lineIntegral F b)) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h := ((hbot.sub htop).add (hvb.const_mul I)).sub (hva.const_mul I)
  have hfun : (fun T : ℝ => rectangleBoundaryIntegral F a b (-T) T)
      = fun T : ℝ => (∫ x in a..b, F (x + (-T : ℝ) * I)) - (∫ x in a..b, F (x + T * I))
          + I * (∫ y in (-T)..T, F (b + y * I)) - I * (∫ y in (-T)..T, F (a + y * I)) := by
    funext T
    unfold rectangleBoundaryIntegral
    push_cast
    ring_nf
  rw [hfun]
  unfold stripBoundary
  simpa using h

/-- **Strip Cauchy**: an entire function with uniform power decay (order `≥ 2`) on the strip has
zero strip boundary integral. -/
theorem stripBoundary_eq_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hC : 0 ≤ C) (hab : a ≤ b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    stripBoundary F a b = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hia : Integrable (fun t : ℝ => F (a + t * I)) :=
    integrable_line_of_decay hF.continuous hk hC (fun t => hdec a ⟨le_refl a, hab⟩ t)
  have hib : Integrable (fun t : ℝ => F (b + t * I)) :=
    integrable_line_of_decay hF.continuous hk hC (fun t => hdec b ⟨hab, le_refl b⟩ t)
  have hlim := rectangle_tendsto_stripBoundary hia hib (horizontal_tendsto_zero hk1 hab hdec)
    (horizontal_neg_tendsto_zero hk1 hab hdec)
  have hzero : ∀ T : ℝ, 0 ≤ T → rectangleBoundaryIntegral F a b (-T) T = 0 := by
    intro T hT
    exact rectangleBoundaryIntegral_eq_zero_of_differentiableOn F a b (-T) T hab
      (by linarith) hF.differentiableOn
  have hconst : Tendsto (fun T : ℝ => rectangleBoundaryIntegral F a b (-T) T) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hzero T hT).symm
  exact tendsto_nhds_unique hlim hconst

/-- Two functions agreeing on the boundary of a rectangle have the same boundary integral. -/
theorem rectangleBoundaryIntegral_congr_boundary {f g : ℂ → ℂ} {a b c d : ℝ}
    (h : ∀ z : ℂ, (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) → f z = g z) :
    rectangleBoundaryIntegral f a b c d = rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  have h1 : ∫ x in a..b, f (x + c * I) = ∫ x in a..b, g (x + c * I) :=
    intervalIntegral.integral_congr (fun x _ => h _ (Or.inr (Or.inr (Or.inl (by simp)))))
  have h2 : ∫ x in a..b, f (x + d * I) = ∫ x in a..b, g (x + d * I) :=
    intervalIntegral.integral_congr (fun x _ => h _ (Or.inr (Or.inr (Or.inr (by simp)))))
  have h3 : ∫ y in c..d, f (b + y * I) = ∫ y in c..d, g (b + y * I) :=
    intervalIntegral.integral_congr (fun y _ => h _ (Or.inr (Or.inl (by simp))))
  have h4 : ∫ y in c..d, f (a + y * I) = ∫ y in c..d, g (a + y * I) :=
    intervalIntegral.integral_congr (fun y _ => h _ (Or.inl (by simp)))
  rw [h1, h2, h3, h4]

/-- **Rectangle residue for an entire `F`**: for `ρ` interior, `∮_rect F(z)/(z−ρ) = 2πi F(ρ)`. -/
theorem rectangleBoundaryIntegral_div_sub {F : ℂ → ℂ} (hF : Differentiable ℂ F) {ρ : ℂ}
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hρ : a < ρ.re ∧ ρ.re < b ∧ c < ρ.im ∧ ρ.im < d) :
    rectangleBoundaryIntegral (fun z => F z * (z - ρ)⁻¹) a b c d = 2 * Real.pi * I * F ρ := by
  have hg : DifferentiableOn ℂ (dslope F ρ) (Icc a b ×ℂ Icc c d) := by
    have h := (differentiableOn_dslope (f := F) (s := (univ : Set ℂ)) (c := ρ) univ_mem).mpr
      hF.differentiableOn
    exact h.mono (subset_univ _)
  have hres := rectangleBoundaryIntegral_holo_add_residues (dslope F ρ) {ρ} (fun _ => F ρ)
    hab hcd hg (by
      intro ρ' hρ'
      rw [Finset.mem_singleton] at hρ'
      rw [hρ']
      exact hρ)
  rw [Finset.sum_singleton] at hres
  have hcongr : rectangleBoundaryIntegral (fun z => F z * (z - ρ)⁻¹) a b c d
      = rectangleBoundaryIntegral (fun z => dslope F ρ z + F ρ * (z - ρ)⁻¹) a b c d := by
    apply rectangleBoundaryIntegral_congr_boundary
    intro z hz
    have hne : z ≠ ρ := by
      intro h
      rw [h] at hz
      rcases hz with h | h | h | h <;> linarith [hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2]
    rw [dslope_of_ne F hne, slope_def_field]
    have hne' : z - ρ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  rw [hcongr]
  have hsum : (fun z => dslope F ρ z + F ρ * (z - ρ)⁻¹)
      = fun z => dslope F ρ z + ∑ ρ' ∈ ({ρ} : Finset ℂ), (fun _ => F ρ) ρ' * (z - ρ')⁻¹ := by
    funext z
    rw [Finset.sum_singleton]
  rw [hsum, hres]

/-- **Strip residue**: for an entire `F` with uniform power decay (order `≥ 2`) on the strip and
`a < Re ρ < b`, `∮_strip F(s)/(s−ρ) = 2πi F(ρ)`. -/
theorem stripBoundary_div_sub_eq {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hC : 0 ≤ C) (hab : a ≤ b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {ρ : ℂ} (hρa : a < ρ.re) (hρb : ρ.re < b) :
    stripBoundary (fun s => F s * (s - ρ)⁻¹) a b = 2 * Real.pi * I * F ρ := by
  have hk1 : 1 ≤ k := by omega
  set δ : ℝ := min (ρ.re - a) (b - ρ.re) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  -- the kernel is bounded on the two lines
  have hker : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ, ‖((σ : ℂ) + t * I - ρ)⁻¹‖ ≤ δ⁻¹ := by
    intro σ hσ t
    rw [norm_inv]
    apply inv_anti₀ hδ0
    have hre : |((σ : ℂ) + t * I - ρ).re| ≤ ‖(σ : ℂ) + t * I - ρ‖ := Complex.abs_re_le_norm _
    have hre' : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
    rw [hre'] at hre
    rcases hσ with h | h
    · calc δ ≤ ρ.re - a := min_le_left _ _
        _ = |σ - ρ.re| := by rw [h, abs_sub_comm, abs_of_pos (by linarith)]
        _ ≤ _ := hre
    · calc δ ≤ b - ρ.re := min_le_right _ _
        _ = |σ - ρ.re| := by rw [h, abs_of_pos (by linarith)]
        _ ≤ _ := hre
  -- integrability on the lines: decay of `F` times the bounded kernel
  have hint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - ρ)⁻¹) := by
    intro σ hσ
    have hσab : σ ∈ Icc a b := by
      rcases hσ with rfl | rfl
      · exact ⟨le_refl _, hab⟩
      · exact ⟨hab, le_refl _⟩
    have hg : Integrable (fun t : ℝ => (C * δ⁻¹) * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    refine Integrable.mono' hg ?_ ?_
    · have hcont : Continuous (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - ρ)⁻¹) := by
        refine (hF.continuous.comp (by fun_prop)).mul (Continuous.inv₀ (by fun_prop) ?_)
        intro t h0
        have hre0 := congrArg Complex.re h0
        simp at hre0
        rcases hσ with h | h <;> linarith
      exact hcont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t => ?_)
      rw [norm_mul]
      have h1 := lineDecay_le_inv_one_add_sq hk hC (fun t => hdec σ hσab t) t
      have h2 := hker σ hσ t
      calc ‖F (σ + t * I)‖ * ‖((σ : ℂ) + t * I - ρ)⁻¹‖
          ≤ (C * (1 + t ^ 2)⁻¹) * δ⁻¹ :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (C * δ⁻¹) * (1 + t ^ 2)⁻¹ := by ring
  -- horizontal segments: for `|T| ≥ |Im ρ| + 1` the kernel is bounded by `1`
  have hhor : ∀ x ∈ Icc a b, ∀ T : ℝ, |ρ.im| + 1 ≤ |T| →
      ‖F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹‖ ≤ C / (1 + |T|) ^ k := by
    intro x hx T hT
    rw [norm_mul]
    have hkerT : ‖((x : ℂ) + T * I - ρ)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have him : |((x : ℂ) + T * I - ρ).im| ≤ ‖(x : ℂ) + T * I - ρ‖ := Complex.abs_im_le_norm _
      have him' : ((x : ℂ) + T * I - ρ).im = T - ρ.im := by simp
      rw [him'] at him
      have : 1 ≤ |T - ρ.im| := by
        have := abs_sub_abs_le_abs_sub T ρ.im
        linarith
      linarith
    calc ‖F (x + T * I)‖ * ‖((x : ℂ) + T * I - ρ)⁻¹‖
        ≤ (C / (1 + |T|) ^ k) * 1 := mul_le_mul (hdec x hx T) hkerT (norm_nonneg _) (by positivity)
      _ = C / (1 + |T|) ^ k := mul_one _
  have htop : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹) atTop
      (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ k * (b - a)) atTop (𝓝 0) := by
      have := (tendsto_const_div_one_add_pow (c := C) hk1).mul_const (b - a)
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg ρ.im]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹)
      (C := C / (1 + T) ^ k) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    · intro x hx
      have hx' : x ∈ Icc a b := by
        rw [uIoc_of_le hab] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have := hhor x hx' T (by rw [abs_of_nonneg hT0]; exact hT)
      rwa [abs_of_nonneg hT0] at this
  have hbot : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + (-T : ℝ) * I)
      * ((x : ℂ) + (-T : ℝ) * I - ρ)⁻¹) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ k * (b - a)) atTop (𝓝 0) := by
      have := (tendsto_const_div_one_add_pow (c := C) hk1).mul_const (b - a)
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg ρ.im]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + (-T : ℝ) * I) * ((x : ℂ) + (-T : ℝ) * I - ρ)⁻¹)
      (C := C / (1 + T) ^ k) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    · intro x hx
      have hx' : x ∈ Icc a b := by
        rw [uIoc_of_le hab] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have := hhor x hx' (-T) (by rw [abs_neg, abs_of_nonneg hT0]; exact hT)
      rwa [abs_neg, abs_of_nonneg hT0] at this
  have hlim := rectangle_tendsto_stripBoundary (F := fun s => F s * (s - ρ)⁻¹)
    (hint a (Or.inl rfl)) (hint b (Or.inr rfl)) htop hbot
  have hconst : Tendsto (fun T : ℝ => rectangleBoundaryIntegral (fun s => F s * (s - ρ)⁻¹) a b (-T) T)
      atTop (𝓝 (2 * Real.pi * I * F ρ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg ρ.im]
    symm
    apply rectangleBoundaryIntegral_div_sub hF hab (by linarith)
    refine ⟨hρa, hρb, ?_, ?_⟩
    · have := neg_abs_le ρ.im
      linarith
    · have := le_abs_self ρ.im
      linarith
  exact tendsto_nhds_unique hlim hconst

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_eq_zero
#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_div_sub_eq
