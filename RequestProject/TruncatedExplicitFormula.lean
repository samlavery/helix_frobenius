import Mathlib
import RequestProject.WeilExplicitFormula
import RequestProject.HilbertPolyaResolventTrace

/-!
# The truncated explicit formula at a growth front (ledger 563)

The prime bank grown to the front `x = e^L` (weight exactly `1` for `n ≤ x`, a `C²` cubic B-spline
taper to `0` at `n = x⁴`), read at an arbitrary chart point `s₀` off the zero set, is EXACTLY the
zero comb read through the kernel `K(w) = (x^{4w} − 3x^{3w} + 3x^{2w} − x^{w})/(w⁴ L³)`:

  `ξ′/ξ(s₀) + Σ'_ρ m_ρ K(ρ − s₀)
     = (1/2π)[∫ K(b+it−s₀) E(b+it) dt + ∫ K(a+it−s₀) E(1−a−it) dt] − Σ_n W_x(n) Λ(n) n^{−s₀}`,

`E = weilArch` the Archimedean part of `ξ′/ξ`, `a < 0 < 1 < b`, `a < Re s₀ < b`. The pole of `E` at
`s = 1` inside the strip carries the END term `K(1 − s₀)`; the zero sum converges absolutely
(`K` decays at order 4).

Route: Track W's strip machinery (`WeilStripContour`, `WeilZeroSide`, `WeilPrimeSide`) with two
changes. (i) The kernel has a simple pole at the evaluation point `s₀`: it is `G(s − s₀)/(s − s₀)`
with `G(w) = e^{Lw}((e^{Lw} − 1)/(Lw))³` entire, `G(0) = 1`, of decay order 3 on every strip, and
the per-zero strip residue is computed by partial fractions against `G`. (ii) The prime side is
the Fourier inversion of the explicit profile `W(v) = [(4L−v)₊³ − 3(3L−v)₊³ + 3(2L−v)₊³ − (L−v)₊³]/(6L³)`
(right line) and of its reflection (left line, where it vanishes at `−log n`).

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real FourierTransform

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The kernel -/

/-- `(e^{Lw} − 1)/(Lw)`, extended by `1` at `w = 0`. -/
def expRatio (L : ℝ) (w : ℂ) : ℂ := dslope (fun w : ℂ => Complex.exp (L * w)) 0 w / L

theorem expRatio_of_ne (L : ℝ) {w : ℂ} (hw : w ≠ 0) :
    expRatio L w = (Complex.exp (L * w) - 1) / (L * w) := by
  unfold expRatio
  rw [dslope_of_ne _ hw, slope_def_field]
  simp only [mul_zero, Complex.exp_zero, sub_zero]
  rw [div_div, mul_comm w (L : ℂ)]

theorem expRatio_zero {L : ℝ} (hL : L ≠ 0) : expRatio L 0 = 1 := by
  unfold expRatio
  rw [dslope_same]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have h : HasDerivAt (fun w : ℂ => Complex.exp (L * w)) (Complex.exp (L * 0) * (L * 1)) 0 :=
    (Complex.hasDerivAt_exp _).comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ))
  rw [h.deriv]
  simp [hL']

theorem expRatio_differentiable (L : ℝ) : Differentiable ℂ (expRatio L) := by
  have h : Differentiable ℂ (dslope (fun w : ℂ => Complex.exp (L * w)) 0) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (f := fun w : ℂ => Complex.exp (L * w)) (s := univ) (c := 0)
      univ_mem).mpr (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (L * w)).differentiableOn
  unfold expRatio
  exact h.div_const _

/-- The entire factor `G(w) = e^{Lw}·((e^{Lw} − 1)/(Lw))³`, `G(0) = 1`. -/
def cubicG (L : ℝ) (w : ℂ) : ℂ := Complex.exp (L * w) * expRatio L w ^ 3

theorem cubicG_differentiable (L : ℝ) : Differentiable ℂ (cubicG L) := by
  unfold cubicG
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (L * w)).mul
    ((expRatio_differentiable L).pow 3)

theorem cubicG_zero {L : ℝ} (hL : L ≠ 0) : cubicG L 0 = 1 := by
  simp [cubicG, expRatio_zero hL]

/-- The kernel `K(w) = G(w)/w = (e^{4Lw} − 3e^{3Lw} + 3e^{2Lw} − e^{Lw})/(w⁴L³)`. -/
def cubicKernel (L : ℝ) (w : ℂ) : ℂ := cubicG L w / w

theorem cubicKernel_eq {L : ℝ} (hL : L ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    cubicKernel L w = (Complex.exp (4 * L * w) - 3 * Complex.exp (3 * L * w)
      + 3 * Complex.exp (2 * L * w) - Complex.exp (L * w)) / (w ^ 4 * L ^ 3) := by
  unfold cubicKernel cubicG
  rw [expRatio_of_ne L hw]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have h4 : Complex.exp (4 * L * w) = Complex.exp (L * w) ^ 4 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Complex.exp (3 * L * w) = Complex.exp (L * w) ^ 3 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Complex.exp (2 * L * w) = Complex.exp (L * w) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h4, h3, h2]
  field_simp
  ring

/-- `G` decays at order 3 on every half-plane `Re w ≤ b'`. -/
theorem cubicG_bound {L : ℝ} (hL : 0 < L) {b' : ℝ} (hb' : 0 ≤ b') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ b' → ‖cubicG L w‖ ≤ C / (1 + |w.im|) ^ 3 := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (cubicG_differentiable L).continuous.continuousOn
  set E : ℝ := Real.exp (L * b') with hE
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
  set C : ℝ := max (8 * max M 0) (8 * E * ((E + 1) / L) ^ 3) with hC
  refine ⟨C, by positivity, fun w hw => ?_⟩
  have hpos : 0 < (1 + |w.im|) ^ 3 := by positivity
  by_cases h1 : ‖w‖ ≤ 1
  · have hMw : ‖cubicG L w‖ ≤ max M 0 :=
      le_trans (hM w (by simpa using h1)) (le_max_left _ _)
    have him : |w.im| ≤ 1 := le_trans (Complex.abs_im_le_norm w) h1
    have h8 : (1 + |w.im|) ^ 3 ≤ 8 := by
      have : 1 + |w.im| ≤ 2 := by linarith
      calc (1 + |w.im|) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 8 := by norm_num
    rw [le_div_iff₀ hpos]
    calc ‖cubicG L w‖ * (1 + |w.im|) ^ 3 ≤ max M 0 * 8 :=
          mul_le_mul hMw h8 (by positivity) (le_max_right _ _)
      _ = 8 * max M 0 := by ring
      _ ≤ C := le_max_left _ _
  · have h1 : 1 < ‖w‖ := not_le.mp h1
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    have hexp : ‖Complex.exp (L * w)‖ ≤ E := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (L * w : ℂ).re = L * w.re := by simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hw hL.le
    have hratio : ‖expRatio L w‖ ≤ (E + 1) / (L * ‖w‖) := by
      rw [expRatio_of_ne L hw0, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hL]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc ‖Complex.exp (L * w) - 1‖ ≤ ‖Complex.exp (L * w)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ E + 1 := by rw [norm_one]; linarith
    have hnorm : (1 + |w.im|) ≤ 2 * ‖w‖ := by
      have := Complex.abs_im_le_norm w
      linarith
    have hG : ‖cubicG L w‖ ≤ E * ((E + 1) / (L * ‖w‖)) ^ 3 := by
      unfold cubicG
      rw [norm_mul, norm_pow]
      exact mul_le_mul hexp (pow_le_pow_left₀ (norm_nonneg _) hratio 3) (by positivity)
        (by positivity)
    have hw3 : (1 + |w.im|) ^ 3 ≤ 8 * ‖w‖ ^ 3 := by
      calc (1 + |w.im|) ^ 3 ≤ (2 * ‖w‖) ^ 3 := pow_le_pow_left₀ (by positivity) hnorm 3
        _ = 8 * ‖w‖ ^ 3 := by ring
    rw [le_div_iff₀ hpos]
    have hwpos : 0 < ‖w‖ := by linarith
    calc ‖cubicG L w‖ * (1 + |w.im|) ^ 3
        ≤ (E * ((E + 1) / (L * ‖w‖)) ^ 3) * (8 * ‖w‖ ^ 3) :=
          mul_le_mul hG hw3 (by positivity) (by positivity)
      _ = 8 * E * ((E + 1) / L) ^ 3 := by field_simp
      _ ≤ C := le_max_right _ _

/-- Uniform decay of `s ↦ G(s − s₀)` of order 3 on the strip `a ≤ Re s ≤ b` (`Re s₀ < b`). -/
theorem cubicG_strip_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (_hab : a ≤ b) {s₀ : ℂ}
    (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ T : ℝ,
      ‖cubicG L (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 3 := by
  obtain ⟨C₀, hC₀, hbound⟩ := cubicG_bound hL (b' := b - s₀.re) (by linarith)
  refine ⟨C₀ * (1 + |s₀.im|) ^ 3, by positivity, fun x hx T => ?_⟩
  have hre : ((x : ℂ) + T * I - s₀).re ≤ b - s₀.re := by
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_zero]
    linarith [hx.2]
  have him : ((x : ℂ) + T * I - s₀).im = T - s₀.im := by simp
  have h := hbound _ hre
  rw [him] at h
  have hkey : 1 + |T| ≤ (1 + |s₀.im|) * (1 + |T - s₀.im|) := by
    have h1 := abs_sub_abs_le_abs_sub T s₀.im
    nlinarith [abs_nonneg s₀.im, abs_nonneg (T - s₀.im)]
  have hpos1 : 0 < (1 + |T - s₀.im|) ^ 3 := by positivity
  have hpos2 : 0 < (1 + |T|) ^ 3 := by positivity
  calc ‖cubicG L ((x : ℂ) + T * I - s₀)‖ ≤ C₀ / (1 + |T - s₀.im|) ^ 3 := h
    _ ≤ C₀ * (1 + |s₀.im|) ^ 3 / (1 + |T|) ^ 3 := by
        rw [div_le_div_iff₀ hpos1 hpos2]
        calc C₀ * (1 + |T|) ^ 3 ≤ C₀ * ((1 + |s₀.im|) * (1 + |T - s₀.im|)) ^ 3 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkey 3) hC₀
          _ = C₀ * (1 + |s₀.im|) ^ 3 * (1 + |T - s₀.im|) ^ 3 := by ring

/-- The kernel `s ↦ K(s − s₀)` decays at order 4 on the two lines `Re s ∈ {a, b}`
(`a < Re s₀ < b`). -/
theorem cubicKernel_line_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {s₀ : ℂ}
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, (σ = a ∨ σ = b) →
      LineDecay (fun s => cubicKernel L (s - s₀)) σ C 4 := by
  obtain ⟨C₀, hC₀, hbound⟩ := cubicG_strip_decay hL hab hs₀b
  set η : ℝ := min (s₀.re - a) (b - s₀.re) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  refine ⟨C₀ * ((1 + |s₀.im|) / η + 1), by positivity, fun σ hσ t => ?_⟩
  have hσab : σ ∈ Icc a b := by
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hG := hbound σ hσab t
  have hden : η ≤ ‖(σ : ℂ) + t * I - s₀‖ := by
    have hre : |((σ : ℂ) + t * I - s₀).re| ≤ ‖(σ : ℂ) + t * I - s₀‖ := Complex.abs_re_le_norm _
    have hre' : ((σ : ℂ) + t * I - s₀).re = σ - s₀.re := by simp
    rw [hre'] at hre
    rcases hσ with h | h
    · calc η ≤ s₀.re - a := min_le_left _ _
        _ = |σ - s₀.re| := by rw [h, abs_sub_comm, abs_of_pos (by linarith)]
        _ ≤ _ := hre
    · calc η ≤ b - s₀.re := min_le_right _ _
        _ = |σ - s₀.re| := by rw [h, abs_of_pos (by linarith)]
        _ ≤ _ := hre
  have hkey : 1 + |t| ≤ ((1 + |s₀.im|) / η + 1) * ‖(σ : ℂ) + t * I - s₀‖ := by
    have hden2 : |t - s₀.im| ≤ ‖(σ : ℂ) + t * I - s₀‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I - s₀)
      simpa using this
    have h1 := abs_sub_abs_le_abs_sub t s₀.im
    have h2 : (1 + |s₀.im|) ≤ (1 + |s₀.im|) / η * ‖(σ : ℂ) + t * I - s₀‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hη0]
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    nlinarith
  have hD0 : 0 < ‖(σ : ℂ) + t * I - s₀‖ := lt_of_lt_of_le hη0 hden
  show ‖cubicKernel L ((σ : ℂ) + t * I - s₀)‖ ≤ _
  unfold cubicKernel
  rw [norm_div]
  have hpos4 : 0 < (1 + |t|) ^ 4 := by positivity
  calc ‖cubicG L ((σ : ℂ) + t * I - s₀)‖ / ‖(σ : ℂ) + t * I - s₀‖
      ≤ (C₀ / (1 + |t|) ^ 3) / ‖(σ : ℂ) + t * I - s₀‖ := div_le_div_of_nonneg_right hG hD0.le
    _ ≤ C₀ * ((1 + |s₀.im|) / η + 1) / (1 + |t|) ^ 4 := by
        rw [div_div, div_le_div_iff₀ (by positivity) hpos4]
        have h4 : (1 + |t|) ^ 4 = (1 + |t|) ^ 3 * (1 + |t|) := by ring
        rw [h4]
        calc C₀ * ((1 + |t|) ^ 3 * (1 + |t|))
            ≤ C₀ * ((1 + |t|) ^ 3 * (((1 + |s₀.im|) / η + 1) * ‖(σ : ℂ) + t * I - s₀‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey (by positivity)) hC₀
          _ = C₀ * ((1 + |s₀.im|) / η + 1) * ((1 + |t|) ^ 3 * ‖(σ : ℂ) + t * I - s₀‖) := by
              ring

theorem cubicKernel_line_continuous (L : ℝ) {σ : ℝ} {s₀ : ℂ} (h : σ ≠ s₀.re) :
    Continuous (fun t : ℝ => cubicKernel L ((σ : ℂ) + t * I - s₀)) := by
  unfold cubicKernel
  refine ((cubicG_differentiable L).continuous.comp (by fun_prop)).div (by fun_prop) ?_
  intro t h0
  have := congrArg Complex.re h0
  simp at this
  exact h (by linarith)

/-! ## 2. The cubic ramp and its Laplace transform -/

theorem tendsto_pow_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun u : ℝ => u ^ k * Real.exp (-(c * u))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul ((c ^ k)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr' (Eventually.of_forall fun u => ?_)
  simp only [Function.comp, id]
  have hck : c ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- `u ↦ u³ e^{−wu}` is integrable on `(0, ∞)` for `Re w > 0`. -/
theorem cube_mul_exp_integrableOn {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ 3 * Complex.exp (-(w * u))) (Ioi 0) := by
  have hreal : IntegrableOn (fun u : ℝ => u ^ (3 : ℝ) * Real.exp (-w.re * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hw
  have hcont : Continuous (fun u : ℝ => (u : ℂ) ^ 3 * Complex.exp (-(w * u))) := by fun_prop
  refine Integrable.mono' hreal hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu
  have e3 : u ^ (3 : ℝ) = u ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : u ^ (1 : ℝ) = u := Real.rpow_one u
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_exp,
    e3, e1]
  have : (-(w * u) : ℂ).re = -w.re * u := by simp
  rw [this]

/-- `∫₀^∞ u³ e^{−wu} du = 6/w⁴` for `Re w > 0`. -/
theorem integral_cube_mul_exp_neg {w : ℂ} (hw : 0 < w.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ 3 * Complex.exp (-(w * u)) = 6 / w ^ 4 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  set Φ : ℂ → ℂ := fun z =>
    -(Complex.exp (-(w * z)) * (z ^ 3 / w + 3 * z ^ 2 / w ^ 2 + 6 * z / w ^ 3 + 6 / w ^ 4)) with hΦ
  have hΦd : ∀ z : ℂ, HasDerivAt Φ (z ^ 3 * Complex.exp (-(w * z))) z := by
    intro z
    have he : HasDerivAt (fun z : ℂ => Complex.exp (-(w * z))) (Complex.exp (-(w * z)) * (-(w * 1))) z :=
      (Complex.hasDerivAt_exp _).comp z (((hasDerivAt_id z).const_mul w).neg)
    have hp : HasDerivAt (fun z : ℂ => z ^ 3 / w + 3 * z ^ 2 / w ^ 2 + 6 * z / w ^ 3 + 6 / w ^ 4)
        (((3 : ℕ) : ℂ) * z ^ (3 - 1) / w + 3 * (((2 : ℕ) : ℂ) * z ^ (2 - 1)) / w ^ 2
          + 6 * 1 / w ^ 3) z := by
      have h3 := (hasDerivAt_pow 3 z).div_const w
      have h2 := ((hasDerivAt_pow 2 z).const_mul (3 : ℂ)).div_const (w ^ 2)
      have h1 := ((hasDerivAt_id z).const_mul (6 : ℂ)).div_const (w ^ 3)
      exact ((h3.add h2).add h1).add_const (6 / w ^ 4)
    have hd := (he.mul hp).neg
    refine hd.congr_deriv ?_
    push_cast
    norm_num
    field_simp
    ring
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => Φ u)
      ((u : ℂ) ^ 3 * Complex.exp (-(w * u))) u :=
    fun u _ => (hΦd (u : ℂ)).comp_ofReal
  have hlim : Tendsto (fun u : ℝ => Φ u) atTop (𝓝 0) := by
    set A : ℝ := ‖w‖ with hA
    have hA0 : 0 < A := norm_pos_iff.mpr hw0
    have hg : Tendsto (fun u : ℝ => (u ^ 3 * Real.exp (-(w.re * u))) / A
        + 3 * (u ^ 2 * Real.exp (-(w.re * u))) / A ^ 2
        + 6 * (u ^ 1 * Real.exp (-(w.re * u))) / A ^ 3
        + 6 * (u ^ 0 * Real.exp (-(w.re * u))) / A ^ 4) atTop (𝓝 0) := by
      have h3 := (tendsto_pow_mul_exp_neg_mul hw 3).div_const A
      have h2 := ((tendsto_pow_mul_exp_neg_mul hw 2).const_mul 3).div_const (A ^ 2)
      have h1 := ((tendsto_pow_mul_exp_neg_mul hw 1).const_mul 6).div_const (A ^ 3)
      have h0 := ((tendsto_pow_mul_exp_neg_mul hw 0).const_mul 6).div_const (A ^ 4)
      have := ((h3.add h2).add h1).add h0
      simpa using this
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [hΦ]
    simp only [norm_neg, norm_mul, Complex.norm_exp]
    have hre : (-(w * (u : ℂ))).re = -(w.re * u) := by simp
    rw [hre]
    have hbound : ‖(u : ℂ) ^ 3 / w + 3 * (u : ℂ) ^ 2 / w ^ 2 + 6 * (u : ℂ) / w ^ 3 + 6 / w ^ 4‖
        ≤ u ^ 3 / A + 3 * u ^ 2 / A ^ 2 + 6 * u ^ 1 / A ^ 3 + 6 * u ^ 0 / A ^ 4 := by
      have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      calc ‖(u : ℂ) ^ 3 / w + 3 * (u : ℂ) ^ 2 / w ^ 2 + 6 * (u : ℂ) / w ^ 3 + 6 / w ^ 4‖
          ≤ ‖(u : ℂ) ^ 3 / w + 3 * (u : ℂ) ^ 2 / w ^ 2 + 6 * (u : ℂ) / w ^ 3‖ + ‖(6 : ℂ) / w ^ 4‖ :=
            norm_add_le _ _
        _ ≤ ‖(u : ℂ) ^ 3 / w + 3 * (u : ℂ) ^ 2 / w ^ 2‖ + ‖6 * (u : ℂ) / w ^ 3‖ + ‖(6 : ℂ) / w ^ 4‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ ‖(u : ℂ) ^ 3 / w‖ + ‖3 * (u : ℂ) ^ 2 / w ^ 2‖ + ‖6 * (u : ℂ) / w ^ 3‖ + ‖(6 : ℂ) / w ^ 4‖ := by
            gcongr; exact norm_add_le _ _
        _ = u ^ 3 / A + 3 * u ^ 2 / A ^ 2 + 6 * u ^ 1 / A ^ 3 + 6 * u ^ 0 / A ^ 4 := by
            simp only [norm_div, norm_mul, norm_pow, hn, hA]
            norm_num
    calc Real.exp (-(w.re * u)) * ‖(u : ℂ) ^ 3 / w + 3 * (u : ℂ) ^ 2 / w ^ 2 + 6 * (u : ℂ) / w ^ 3 + 6 / w ^ 4‖
        ≤ Real.exp (-(w.re * u)) * (u ^ 3 / A + 3 * u ^ 2 / A ^ 2 + 6 * u ^ 1 / A ^ 3 + 6 * u ^ 0 / A ^ 4) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = (u ^ 3 * Real.exp (-(w.re * u))) / A + 3 * (u ^ 2 * Real.exp (-(w.re * u))) / A ^ 2
          + 6 * (u ^ 1 * Real.exp (-(w.re * u))) / A ^ 3
          + 6 * (u ^ 0 * Real.exp (-(w.re * u))) / A ^ 4 := by ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (cube_mul_exp_integrableOn hw) hlim
  rw [h, hΦ]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, zero_add, one_mul, neg_neg, zero_sub]

/-- The right cubic ramp `(c − v)₊³`. -/
def rampR (c v : ℝ) : ℝ := max (c - v) 0 ^ 3

/-- The left cubic ramp `(v − c)₊³`. -/
def rampL (c v : ℝ) : ℝ := max (v - c) 0 ^ 3

theorem rampR_continuous (c : ℝ) : Continuous (rampR c) := by
  unfold rampR; fun_prop

theorem rampL_continuous (c : ℝ) : Continuous (rampL c) := by
  unfold rampL; fun_prop

theorem rampR_eq_of_le {c v : ℝ} (h : v ≤ c) : rampR c v = (c - v) ^ 3 := by
  unfold rampR; rw [max_eq_left (by linarith)]

theorem rampR_eq_zero_of_ge {c v : ℝ} (h : c ≤ v) : rampR c v = 0 := by
  unfold rampR; rw [max_eq_right (by linarith)]; ring

theorem rampL_eq_zero_of_le {c v : ℝ} (h : v ≤ c) : rampL c v = 0 := by
  unfold rampL; rw [max_eq_right (by linarith)]; ring

theorem rampL_neg (c v : ℝ) : rampL c (-v) = rampR (-c) v := by
  unfold rampL rampR
  congr 2
  ring

/-- `v ↦ (c−v)₊³ e^{wv}` is integrable for `Re w > 0`. -/
theorem rampR_mul_exp_integrable {w : ℂ} (hw : 0 < w.re) (c : ℝ) :
    Integrable (fun v : ℝ => (rampR c v : ℂ) * Complex.exp (w * v)) := by
  have hbase : Integrable (fun u : ℝ => ((max u 0 : ℝ) : ℂ) ^ 3 * Complex.exp (-(w * u))) := by
    have hI := cube_mul_exp_integrableOn hw
    have h2 : IntegrableOn (fun u : ℝ => ((max u 0 : ℝ) : ℂ) ^ 3 * Complex.exp (-(w * u)))
        (Ioi 0) := by
      refine hI.congr_fun (fun u hu => ?_) measurableSet_Ioi
      have : max u 0 = u := max_eq_left (le_of_lt hu)
      simp [this]
    exact h2.integrable_of_forall_notMem_eq_zero (fun u hu => by
      have : u ≤ 0 := not_lt.mp hu
      simp [max_eq_right this])
  have h := (hbase.comp_sub_left c).const_mul (Complex.exp (w * c))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [rampR]
  push_cast
  have hexp : Complex.exp (w * c) * Complex.exp (-(w * ((c : ℂ) - v))) = Complex.exp (w * v) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc Complex.exp (w * c) * (((max (c - v) 0 : ℝ) : ℂ) ^ 3 * Complex.exp (-(w * ((c : ℂ) - v))))
      = ((max (c - v) 0 : ℝ) : ℂ) ^ 3
          * (Complex.exp (w * c) * Complex.exp (-(w * ((c : ℂ) - v)))) := by
        ring
    _ = _ := by rw [hexp]

/-- **The right ramp's transform**: `∫ (c−v)₊³ e^{wv} dv = 6 e^{wc}/w⁴` for `Re w > 0`. -/
theorem rampR_laplace {w : ℂ} (hw : 0 < w.re) (c : ℝ) :
    ∫ v : ℝ, (rampR c v : ℂ) * Complex.exp (w * v) = 6 * Complex.exp (w * c) / w ^ 4 := by
  rw [← integral_sub_left_eq_self (fun v : ℝ => (rampR c v : ℂ) * Complex.exp (w * v)) volume c]
  have hfun : (fun u : ℝ => (rampR c (c - u) : ℂ) * Complex.exp (w * ((c - u : ℝ) : ℂ)))
      = fun u : ℝ => Complex.exp (w * c) * (((max u 0 : ℝ) : ℂ) ^ 3 * Complex.exp (-(w * u))) := by
    funext u
    simp only [rampR, sub_sub_cancel]
    push_cast
    have hexp : Complex.exp (w * ((c : ℂ) - u)) = Complex.exp (w * c) * Complex.exp (-(w * u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hexp]
    ring
  rw [hfun, integral_const_mul]
  have hres : ∫ u : ℝ, ((max u 0 : ℝ) : ℂ) ^ 3 * Complex.exp (-(w * u))
      = ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ 3 * Complex.exp (-(w * u)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun u hu => by
      have : u ≤ 0 := not_lt.mp hu
      simp [max_eq_right this])]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
      have : max u 0 = u := max_eq_left (le_of_lt hu)
      simp [this])
  rw [hres, integral_cube_mul_exp_neg hw]
  ring

/-- **The left ramp's transform**: `∫ (v−c)₊³ e^{wv} dv = 6 e^{wc}/w⁴` for `Re w < 0`. -/
theorem rampL_laplace {w : ℂ} (hw : w.re < 0) (c : ℝ) :
    ∫ v : ℝ, (rampL c v : ℂ) * Complex.exp (w * v) = 6 * Complex.exp (w * c) / w ^ 4 := by
  have hw' : 0 < (-w).re := by simp; linarith
  have h := rampR_laplace hw' (-c)
  rw [← integral_neg_eq_self (fun v : ℝ => (rampL c v : ℂ) * Complex.exp (w * v)) volume]
  have hfun : (fun v : ℝ => (rampL c (-v) : ℂ) * Complex.exp (w * ((-v : ℝ) : ℂ)))
      = fun v : ℝ => (rampR (-c) v : ℂ) * Complex.exp ((-w) * v) := by
    funext v
    rw [rampL_neg]
    congr 1
    congr 1
    push_cast
    ring
  rw [hfun, h]
  have e1 : (-w) * ((-c : ℝ) : ℂ) = w * c := by push_cast; ring
  have e2 : (-w) ^ 4 = w ^ 4 := by ring
  rw [e1, e2]

theorem rampL_mul_exp_integrable {w : ℂ} (hw : w.re < 0) (c : ℝ) :
    Integrable (fun v : ℝ => (rampL c v : ℂ) * Complex.exp (w * v)) := by
  have hw' : 0 < (-w).re := by simp; linarith
  have h := (rampR_mul_exp_integrable hw' (-c)).comp_neg
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [← rampL_neg, neg_neg]
  congr 1
  congr 1
  push_cast
  ring

/-! ## 3. The cubic B-spline profile -/

/-- The cubic B-spline weight: `1` for `v ≤ L`, `0` for `v ≥ 4L`, `C²` in between. -/
def cubicProfile (L v : ℝ) : ℝ :=
  (rampR (4 * L) v - 3 * rampR (3 * L) v + 3 * rampR (2 * L) v - rampR L v) / (6 * L ^ 3)

/-- The reflected profile (supported on `v ≥ L`), the kernel's transform left of the pole. -/
def cubicProfileLeft (L v : ℝ) : ℝ :=
  (rampL (4 * L) v - 3 * rampL (3 * L) v + 3 * rampL (2 * L) v - rampL L v) / (6 * L ^ 3)

theorem cubicProfile_continuous (L : ℝ) : Continuous (cubicProfile L) := by
  unfold cubicProfile
  have := rampR_continuous
  fun_prop

theorem cubicProfileLeft_continuous (L : ℝ) : Continuous (cubicProfileLeft L) := by
  unfold cubicProfileLeft
  have := rampL_continuous
  fun_prop

/-- **Sharp front**: the weight is exactly `1` up to the front. -/
theorem cubicProfile_eq_one {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : v ≤ L) : cubicProfile L v = 1 := by
  unfold cubicProfile
  rw [rampR_eq_of_le (by linarith), rampR_eq_of_le (by linarith), rampR_eq_of_le (by linarith),
    rampR_eq_of_le hv]
  have hL0 : L ≠ 0 := hL.ne'
  field_simp
  ring

theorem cubicProfile_eq_zero {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : 4 * L ≤ v) :
    cubicProfile L v = 0 := by
  unfold cubicProfile
  rw [rampR_eq_zero_of_ge hv, rampR_eq_zero_of_ge (by linarith), rampR_eq_zero_of_ge (by linarith),
    rampR_eq_zero_of_ge (by linarith)]
  simp

theorem cubicProfileLeft_eq_zero {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : v ≤ L) :
    cubicProfileLeft L v = 0 := by
  unfold cubicProfileLeft
  rw [rampL_eq_zero_of_le (by linarith), rampL_eq_zero_of_le (by linarith),
    rampL_eq_zero_of_le (by linarith), rampL_eq_zero_of_le hv]
  simp

theorem cubicProfile_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun v : ℝ => (cubicProfile L v : ℂ) * Complex.exp (w * v)) := by
  have i4 := rampR_mul_exp_integrable hw (4 * L)
  have i3 := (rampR_mul_exp_integrable hw (3 * L)).const_mul (3 : ℂ)
  have i2 := (rampR_mul_exp_integrable hw (2 * L)).const_mul (3 : ℂ)
  have i1 := rampR_mul_exp_integrable hw L
  have h := (((i4.sub i3).add i2).sub i1).const_mul (1 / (6 * (L : ℂ) ^ 3))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [cubicProfile, Pi.sub_apply, Pi.add_apply]
  push_cast
  ring

theorem cubicProfileLeft_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : w.re < 0) :
    Integrable (fun v : ℝ => (cubicProfileLeft L v : ℂ) * Complex.exp (w * v)) := by
  have i4 := rampL_mul_exp_integrable hw (4 * L)
  have i3 := (rampL_mul_exp_integrable hw (3 * L)).const_mul (3 : ℂ)
  have i2 := (rampL_mul_exp_integrable hw (2 * L)).const_mul (3 : ℂ)
  have i1 := rampL_mul_exp_integrable hw L
  have h := (((i4.sub i3).add i2).sub i1).const_mul (1 / (6 * (L : ℂ) ^ 3))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [cubicProfileLeft, Pi.sub_apply, Pi.add_apply]
  push_cast
  ring

/-- **The kernel is the Laplace transform of the profile** right of the pole. -/
theorem cubicKernel_eq_laplace_right {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    cubicKernel L w = ∫ v : ℝ, (cubicProfile L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i4 := rampR_mul_exp_integrable hw (4 * L)
  have i3 := (rampR_mul_exp_integrable hw (3 * L)).const_mul (3 : ℂ)
  have i2 := (rampR_mul_exp_integrable hw (2 * L)).const_mul (3 : ℂ)
  have i1 := rampR_mul_exp_integrable hw L
  have hfun : (fun v : ℝ => (cubicProfile L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (6 * (L : ℂ) ^ 3)) *
          ((((rampR (4 * L) v : ℂ) * Complex.exp (w * v)
            - 3 * ((rampR (3 * L) v : ℂ) * Complex.exp (w * v)))
            + 3 * ((rampR (2 * L) v : ℂ) * Complex.exp (w * v)))
            - (rampR L v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [cubicProfile]
    push_cast
    ring
  have j3 : Integrable (fun v : ℝ => (rampR (4 * L) v : ℂ) * Complex.exp (w * v)
      - 3 * ((rampR (3 * L) v : ℂ) * Complex.exp (w * v))) := i4.sub i3
  have j2 : Integrable (fun v : ℝ => (rampR (4 * L) v : ℂ) * Complex.exp (w * v)
      - 3 * ((rampR (3 * L) v : ℂ) * Complex.exp (w * v))
      + 3 * ((rampR (2 * L) v : ℂ) * Complex.exp (w * v))) := j3.add i2
  rw [hfun, integral_const_mul, integral_sub j2 i1, integral_add j3 i2,
    integral_sub i4 i3, integral_const_mul, integral_const_mul, rampR_laplace hw, rampR_laplace hw,
    rampR_laplace hw, rampR_laplace hw, cubicKernel_eq hL0 hw0]
  have e4 : Complex.exp (w * ((4 * L : ℝ) : ℂ)) = Complex.exp (4 * L * w) := by
    congr 1; push_cast; ring
  have e3 : Complex.exp (w * ((3 * L : ℝ) : ℂ)) = Complex.exp (3 * L * w) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (w * ((2 * L : ℝ) : ℂ)) = Complex.exp (2 * L * w) := by
    congr 1; push_cast; ring
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  rw [e4, e3, e2, e1]
  field_simp

/-- **The kernel is the Laplace transform of the reflected profile** left of the pole. -/
theorem cubicKernel_eq_laplace_left {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w.re < 0) :
    cubicKernel L w = ∫ v : ℝ, (cubicProfileLeft L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i4 := rampL_mul_exp_integrable hw (4 * L)
  have i3 := (rampL_mul_exp_integrable hw (3 * L)).const_mul (3 : ℂ)
  have i2 := (rampL_mul_exp_integrable hw (2 * L)).const_mul (3 : ℂ)
  have i1 := rampL_mul_exp_integrable hw L
  have hfun : (fun v : ℝ => (cubicProfileLeft L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (6 * (L : ℂ) ^ 3)) *
          ((((rampL (4 * L) v : ℂ) * Complex.exp (w * v)
            - 3 * ((rampL (3 * L) v : ℂ) * Complex.exp (w * v)))
            + 3 * ((rampL (2 * L) v : ℂ) * Complex.exp (w * v)))
            - (rampL L v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [cubicProfileLeft]
    push_cast
    ring
  have j3 : Integrable (fun v : ℝ => (rampL (4 * L) v : ℂ) * Complex.exp (w * v)
      - 3 * ((rampL (3 * L) v : ℂ) * Complex.exp (w * v))) := i4.sub i3
  have j2 : Integrable (fun v : ℝ => (rampL (4 * L) v : ℂ) * Complex.exp (w * v)
      - 3 * ((rampL (3 * L) v : ℂ) * Complex.exp (w * v))
      + 3 * ((rampL (2 * L) v : ℂ) * Complex.exp (w * v))) := j3.add i2
  rw [hfun, integral_const_mul, integral_sub j2 i1, integral_add j3 i2,
    integral_sub i4 i3, integral_const_mul, integral_const_mul, rampL_laplace hw, rampL_laplace hw,
    rampL_laplace hw, rampL_laplace hw, cubicKernel_eq hL0 hw0]
  have e4 : Complex.exp (w * ((4 * L : ℝ) : ℂ)) = Complex.exp (4 * L * w) := by
    congr 1; push_cast; ring
  have e3 : Complex.exp (w * ((3 * L : ℝ) : ℂ)) = Complex.exp (3 * L * w) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (w * ((2 * L : ℝ) : ℂ)) = Complex.exp (2 * L * w) := by
    congr 1; push_cast; ring
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  rw [e4, e3, e2, e1]
  field_simp

/-! ## 4. Fourier inversion on a line -/

/-- A line integrand that is continuous in `t` with power decay of order `≥ 2` is integrable
(no continuity of `F` off the line is needed). -/
theorem integrable_line_of_decay' {F : ℂ → ℂ} {σ C : ℝ} {k : ℕ}
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hk : 2 ≤ k) (hC : 0 ≤ C)
    (h : LineDecay F σ C k) : Integrable (fun t : ℝ => F (σ + t * I)) := by
  have hg : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hg hF.aestronglyMeasurable ?_
  exact Eventually.of_forall (lineDecay_le_inv_one_add_sq hk hC h)

/-- **Line inversion**: if `Φ(t) = ∫ φ(v) e^{itv} dv` with `φ` continuous and integrable and `Φ`
integrable, then `∫ Φ(t) e^{−ity} dt = 2π φ(y)`. -/
theorem line_transform_inversion {φ : ℝ → ℂ} (hφc : Continuous φ) (hφi : Integrable φ)
    {Φ : ℝ → ℂ} (hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v))
    (hΦi : Integrable Φ) (y : ℝ) :
    ∫ t : ℝ, Φ t * Complex.exp (-(I * t * y)) = 2 * π * φ y := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
  have hinv : ∀ t : ℝ, Φ t = 𝓕⁻ φ (t / (2 * π)) := by
    intro t
    rw [hΦ t, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext v
    rw [smul_eq_mul, mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp
  have hFφ : Integrable (𝓕 φ) := by
    have h2π : (-(2 * π) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 2 * π := by positivity
      linarith
    have h : Integrable (fun w : ℝ => Φ ((-(2 * π)) * w)) := hΦi.comp_mul_left' h2π
    refine h.congr (Eventually.of_forall fun w => ?_)
    show Φ ((-(2 * π)) * w) = 𝓕 φ w
    rw [hinv, Real.fourierInv_eq_fourier_neg]
    field_simp
  set G : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((-2 * π * x * y : ℝ) : ℂ) * I) • 𝓕⁻ φ x with hG
  have h1 : ∀ t : ℝ, Φ t * Complex.exp (-(I * t * y)) = G ((2 * π)⁻¹ * t) := by
    intro t
    rw [hG]
    simp only [smul_eq_mul]
    rw [hinv, mul_comm]
    congr 1
    · congr 1
      push_cast
      field_simp
    · rw [div_eq_inv_mul]
  have h2 : ∫ t : ℝ, G ((2 * π)⁻¹ * t) = |((2 * π)⁻¹)⁻¹| • ∫ x : ℝ, G x :=
    Measure.integral_comp_mul_left G ((2 * π)⁻¹)
  have h3 : ∫ x : ℝ, G x = φ y := by
    rw [hG]
    have hf : 𝓕 (𝓕⁻ φ) y = φ y := hφi.fourier_fourierInv_eq hFφ hφc.continuousAt
    rw [← hf, Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ => Φ t * Complex.exp (-(I * t * y))) = fun t : ℝ => G ((2 * π)⁻¹ * t) :=
    funext h1
  rw [hfun, h2, h3, inv_inv, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  ring

/-! ## 5. The prime side -/

/-- The right prime line: `∫ K(b+it−s₀) term_n(b+it) dt = 2π · W(log n) · Λ(n) n^{−s₀}`. -/
theorem cubicKernel_prime_line_right {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {b : ℝ} (hb : s₀.re < b)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => cubicKernel L (s - s₀)) b C 4) (n : ℕ) :
    ∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n
      = 2 * π * ((cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set w₀ : ℂ := (b : ℂ) - s₀ with hw₀
  have hw₀re : 0 < w₀.re := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (cubicProfile L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (cubicProfile_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := cubicProfile_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => cubicKernel L ((b : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : (0 : ℝ) < ((b : ℂ) + t * I - s₀).re := by simp; linarith
    show cubicKernel L ((b : ℂ) + t * I - s₀) = _
    rw [cubicKernel_eq_laplace_right hL hw]
    congr 1
    funext v
    rw [hφ]
    show (cubicProfile L v : ℂ) * Complex.exp (((b : ℂ) + t * I - s₀) * v)
      = (cubicProfile L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => cubicKernel L (s - s₀))
      (cubicKernel_line_continuous L (by linarith : b ≠ s₀.re)) (by norm_num) hC hdec
  have hfun : (fun t : ℝ => cubicKernel L ((b : ℂ) + t * I - s₀)
        * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
          * (Φ t * Complex.exp (-(I * t * Real.log n))) := by
    funext t
    rw [term_line_eq b t hn, hΦdef]
    ring
  rw [hfun, integral_const_mul, line_transform_inversion hφc hφi hΦ hΦi (Real.log n)]
  rw [hφ]
  show (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
      * (2 * π * ((cubicProfile L (Real.log n) : ℂ) * Complex.exp (w₀ * Real.log n)))
    = 2 * π * ((cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n)
  have hexp : Complex.exp (w₀ * Real.log n) = (n : ℂ) ^ w₀ := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 1
    ring
  have hpow : (((n : ℝ) ^ (-b) : ℝ) : ℂ) * (n : ℂ) ^ w₀ = (n : ℂ) ^ (-s₀) := by
    rw [Complex.ofReal_cpow hnr.le, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hn0]
    congr 1
    rw [hw₀]
    push_cast
    ring
  have hts : LSeries.term vonMangoldtC s₀ n
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s₀) := by
    rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, Complex.cpow_neg]
  rw [hts, hexp]
  linear_combination
    (2 * (π : ℂ) * (cubicProfile L (Real.log n) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      * hpow

/-- The left prime line vanishes: the reflected profile is supported above the front. -/
theorem cubicKernel_prime_line_left {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => cubicKernel L (s - s₀)) a C 4) (n : ℕ) :
    ∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀)
      * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (cubicProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (cubicProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := cubicProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => cubicKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show cubicKernel L ((a : ℂ) + t * I - s₀) = _
    rw [cubicKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (cubicProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (cubicProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => cubicKernel L (s - s₀))
      (cubicKernel_line_continuous L (by linarith : a ≠ s₀.re)) (by norm_num) hC hdec
  have hrefl : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)) = (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    push_cast
    ring
  have hfun : (fun t : ℝ => cubicKernel L ((a : ℂ) + t * I - s₀)
        * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          * (((n : ℝ) ^ (-(1 - a)) : ℝ) : ℂ))
          * (Φ t * Complex.exp (-(I * t * ((-Real.log n : ℝ) : ℂ)))) := by
    funext t
    rw [hrefl t, term_line_eq (1 - a) (-t) hn, hΦdef]
    have : Complex.exp (-(I * ((-t : ℝ) : ℂ) * Real.log n))
        = Complex.exp (-(I * t * ((-Real.log n : ℝ) : ℂ))) := by
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [hfun, integral_const_mul, line_transform_inversion hφc hφi hΦ hΦi (-Real.log n)]
  rw [hφ]
  show (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-(1 - a)) : ℝ) : ℂ))
      * (2 * π * ((cubicProfileLeft L (-Real.log n) : ℂ) * Complex.exp (w₀ * ((-Real.log n : ℝ) : ℂ))))
    = 0
  rw [cubicProfileLeft_eq_zero hL (by linarith : -Real.log n ≤ L)]
  simp

/-! ## 6. Line-only versions of the exchange lemmas, via the line extension -/

/-- The line extension `s ↦ F(σ + i·Im s)`: constant along horizontals, equal to `F` on the line. -/
def lineExt (F : ℂ → ℂ) (σ : ℝ) (s : ℂ) : ℂ := F (σ + s.im * I)

theorem lineExt_continuous {F : ℂ → ℂ} {σ : ℝ} (hF : Continuous (fun t : ℝ => F (σ + t * I))) :
    Continuous (lineExt F σ) := by
  unfold lineExt
  exact hF.comp Complex.continuous_im

theorem lineExt_strip_decay {F : ℂ → ℂ} {σ C : ℝ} {k : ℕ} (hdec : LineDecay F σ C k) (a b : ℝ) :
    ∀ x ∈ Icc a b, ∀ T : ℝ, ‖lineExt F σ (x + T * I)‖ ≤ C / (1 + |T|) ^ k := by
  intro x _ T
  unfold lineExt
  have : ((x : ℂ) + T * I).im = T := by simp
  rw [this]
  exact hdec T

theorem hadamardLineTerm_lineExt (F : ℂ → ℂ) (σ : ℝ) (ρ : Zero) :
    hadamardLineTerm (lineExt F σ) σ ρ = hadamardLineTerm F σ ρ := by
  funext t
  unfold hadamardLineTerm lineExt
  simp

theorem hadamardLineTerm_integrable_line {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k)
    (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b)
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hdec : LineDecay F σ C k) (ρ : Zero) :
    Integrable (hadamardLineTerm F σ ρ) := by
  have h := hadamardLineTerm_integrable (lineExt_continuous hF) hk hC ha hb
    (lineExt_strip_decay hdec a b) hσ ρ
  rwa [hadamardLineTerm_lineExt] at h

theorem summable_hadamardLineTerm_integral_norm_line {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b)
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hdec : LineDecay F σ C k) :
    Summable (fun ρ : Zero => ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖) := by
  have h := summable_hadamardLineTerm_integral_norm (lineExt_continuous hF) hk hC ha hb
    (lineExt_strip_decay hdec a b) hσ
  simpa only [hadamardLineTerm_lineExt] using h

theorem lineIntegral_hadamard_exchange_line {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b)
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hdec : LineDecay F σ C k) :
    ∫ t : ℝ, ∑' ρ : Zero, hadamardLineTerm F σ ρ t
      = ∑' ρ : Zero, ∫ t : ℝ, hadamardLineTerm F σ ρ t := by
  have h := lineIntegral_hadamard_exchange (lineExt_continuous hF) hk hC ha hb
    (lineExt_strip_decay hdec a b) hσ
  simpa only [hadamardLineTerm_lineExt] using h

theorem summable_hadamardLineTerm_integral_line {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b)
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hdec : LineDecay F σ C k) :
    Summable (fun ρ : Zero => ∫ t : ℝ, hadamardLineTerm F σ ρ t) := by
  have h := summable_hadamardLineTerm_integral (lineExt_continuous hF) hk hC ha hb
    (lineExt_strip_decay hdec a b) hσ
  simpa only [hadamardLineTerm_lineExt] using h

/-- `F·ξ′/ξ` is integrable on a line where `F` is continuous with decay `≥ 4`. -/
theorem line_mul_logDeriv_xi_integrable' {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k)
    (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b)
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hdec : LineDecay F σ C k) :
    Integrable (fun t : ℝ => F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I)) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  have hintF : Integrable (fun t : ℝ => F (σ + t * I)) := integrable_line_of_decay' hF hk2 hC hdec
  have hpt : ∀ t : ℝ, F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I)
      = A * F (σ + t * I) + ∑' ρ : Zero, hadamardLineTerm F σ ρ t := by
    intro t
    rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
    unfold hadamardLineTerm hadamardTerm
    rw [mul_add, ← tsum_mul_left]
    congr 1
    ring
  have hfun : (fun t : ℝ => F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I))
      = fun t : ℝ => A * F (σ + t * I) + ∑' ρ : Zero, hadamardLineTerm F σ ρ t := funext hpt
  rw [hfun]
  exact (hintF.const_mul A).add (integrable_tsum_of_summable_integral_norm
    (fun ρ => hadamardLineTerm_integrable_line hk hC ha hb hσ hF hdec ρ)
    (summable_hadamardLineTerm_integral_norm_line hk hC ha hb hσ hF hdec))

/-! ## 7. Strip-boundary algebra -/

theorem stripBoundary_congr {F G : ℂ → ℂ} {a b : ℝ}
    (h : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ, F (σ + t * I) = G (σ + t * I)) :
    stripBoundary F a b = stripBoundary G a b := by
  unfold stripBoundary lineIntegral
  have hb' : (fun t : ℝ => F (b + t * I)) = fun t : ℝ => G (b + t * I) := funext (h b (Or.inr rfl))
  have ha' : (fun t : ℝ => F (a + t * I)) = fun t : ℝ => G (a + t * I) := funext (h a (Or.inl rfl))
  rw [hb', ha']

theorem stripBoundary_add {F G : ℂ → ℂ} {a b : ℝ}
    (hFa : Integrable (fun t : ℝ => F (a + t * I))) (hFb : Integrable (fun t : ℝ => F (b + t * I)))
    (hGa : Integrable (fun t : ℝ => G (a + t * I)))
    (hGb : Integrable (fun t : ℝ => G (b + t * I))) :
    stripBoundary (fun s => F s + G s) a b = stripBoundary F a b + stripBoundary G a b := by
  unfold stripBoundary lineIntegral
  beta_reduce
  rw [integral_add hFb hGb, integral_add hFa hGa]
  ring

theorem stripBoundary_sub {F G : ℂ → ℂ} {a b : ℝ}
    (hFa : Integrable (fun t : ℝ => F (a + t * I))) (hFb : Integrable (fun t : ℝ => F (b + t * I)))
    (hGa : Integrable (fun t : ℝ => G (a + t * I)))
    (hGb : Integrable (fun t : ℝ => G (b + t * I))) :
    stripBoundary (fun s => F s - G s) a b = stripBoundary F a b - stripBoundary G a b := by
  unfold stripBoundary lineIntegral
  beta_reduce
  rw [integral_sub hFb hGb, integral_sub hFa hGa]
  ring

theorem stripBoundary_const_mul (c : ℂ) (F : ℂ → ℂ) (a b : ℝ) :
    stripBoundary (fun s => c * F s) a b = c * stripBoundary F a b := by
  unfold stripBoundary lineIntegral
  beta_reduce
  rw [integral_const_mul, integral_const_mul]
  ring

/-- Decay `≥ 2` times a bounded resolvent factor is integrable on a line off the pole. -/
theorem integrable_line_mul_inv_sub {F : ℂ → ℂ} (hF : Continuous F) {σ C : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hC : 0 ≤ C) (hdec : LineDecay F σ C k) {p : ℂ} (hp : σ ≠ p.re) :
    Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) := by
  have hint : Integrable (fun t : ℝ => F (σ + t * I)) := integrable_line_of_decay hF hk hC hdec
  have hne : ∀ t : ℝ, (σ : ℂ) + t * I - p ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact hp (by linarith)
  have hcont : Continuous (fun t : ℝ => ((σ : ℂ) + t * I - p)⁻¹) :=
    Continuous.inv₀ (by fun_prop) hne
  have hδ : 0 < |σ - p.re| := abs_pos.mpr (sub_ne_zero.mpr hp)
  refine hint.mul_bdd hcont.aestronglyMeasurable (c := |σ - p.re|⁻¹)
    (Eventually.of_forall fun t => ?_)
  rw [norm_inv]
  apply inv_anti₀ hδ
  have h1 : |((σ : ℂ) + t * I - p).re| ≤ ‖(σ : ℂ) + t * I - p‖ := Complex.abs_re_le_norm _
  have h2 : ((σ : ℂ) + t * I - p).re = σ - p.re := by simp
  rw [h2] at h1
  exact h1

/-! ## 8. The zero side with the pole inside the strip -/

/-- **Per-zero strip residue with the pole**: for a zero `ρ ≠ s₀`,
`∮_strip K(s−s₀)·(1/(s−ρ) + 1/ρ) = 2πi [hadamardTerm ρ s₀ + K(ρ − s₀)]`. -/
theorem stripBoundary_cubicKernel_hadamardTerm {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρs : ρ ≠ s₀) :
    stripBoundary (fun s => cubicKernel L (s - s₀) * hadamardTerm ρ s) a b
      = 2 * Real.pi * I * (hadamardTerm ρ s₀ + cubicKernel L (ρ - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdec⟩ := cubicG_strip_decay hL hab hs₀b
  set G : ℂ → ℂ := fun s => cubicG L (s - s₀) with hGdef
  have hGd : Differentiable ℂ G :=
    (cubicG_differentiable L).comp (differentiable_id.sub_const s₀)
  have hdecG : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I)‖ ≤ C / (1 + |T|) ^ 3 := hdec
  have hρ0 : ρ ≠ 0 := zero_ne_zero hρ
  have hρa : a < ρ.re := by linarith [hρ.1]
  have hρb : ρ.re < b := by linarith [hρ.2.1]
  have h1 : stripBoundary (fun s => G s * (s - s₀)⁻¹) a b = 2 * Real.pi * I * G s₀ :=
    stripBoundary_div_sub_eq hGd (by norm_num) hC hab hdecG hs₀a hs₀b
  have h2 : stripBoundary (fun s => G s * (s - ρ)⁻¹) a b = 2 * Real.pi * I * G ρ :=
    stripBoundary_div_sub_eq hGd (by norm_num) hC hab hdecG hρa hρb
  have hne3 : s₀ - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρs)
  have hpt : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ,
      cubicKernel L ((σ : ℂ) + t * I - s₀) * hadamardTerm ρ ((σ : ℂ) + t * I)
        = (1 / (s₀ - ρ)) * (G ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - s₀)⁻¹
            - G ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - ρ)⁻¹)
          + (1 / ρ) * (G ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - s₀)⁻¹) := by
    intro σ hσ t
    have hne1 : (σ : ℂ) + t * I - s₀ ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      rcases hσ with rfl | rfl <;> linarith
    have hne2 : (σ : ℂ) + t * I - ρ ≠ 0 := sub_ne_zero.mpr (line_ne_zero_point ha hb hσ t hρ)
    simp only [cubicKernel, hadamardTerm, hGdef]
    field_simp
    ring
  have hσab : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ∈ Icc a b := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hint : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ p : ℂ, (p = s₀ ∨ p = ρ) →
      Integrable (fun t : ℝ => G (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) := by
    intro σ hσ p hp
    have hdecσ : LineDecay G σ C 3 := fun t => hdecG σ (hσab σ hσ) t
    have hp' : σ ≠ p.re := by
      rcases hσ with rfl | rfl <;> rcases hp with rfl | rfl <;> linarith
    exact integrable_line_mul_inv_sub hGd.continuous (by norm_num) hC hdecσ hp'
  have hFa : Integrable (fun t : ℝ => (1 / (s₀ - ρ)) * (G (a + t * I) * ((a : ℂ) + t * I - s₀)⁻¹
      - G (a + t * I) * ((a : ℂ) + t * I - ρ)⁻¹)) :=
    ((hint a (Or.inl rfl) s₀ (Or.inl rfl)).sub (hint a (Or.inl rfl) ρ (Or.inr rfl))).const_mul _
  have hFb : Integrable (fun t : ℝ => (1 / (s₀ - ρ)) * (G (b + t * I) * ((b : ℂ) + t * I - s₀)⁻¹
      - G (b + t * I) * ((b : ℂ) + t * I - ρ)⁻¹)) :=
    ((hint b (Or.inr rfl) s₀ (Or.inl rfl)).sub (hint b (Or.inr rfl) ρ (Or.inr rfl))).const_mul _
  have hGa : Integrable (fun t : ℝ => (1 / ρ) * (G (a + t * I) * ((a : ℂ) + t * I - s₀)⁻¹)) :=
    (hint a (Or.inl rfl) s₀ (Or.inl rfl)).const_mul _
  have hGb : Integrable (fun t : ℝ => (1 / ρ) * (G (b + t * I) * ((b : ℂ) + t * I - s₀)⁻¹)) :=
    (hint b (Or.inr rfl) s₀ (Or.inl rfl)).const_mul _
  have e1 := stripBoundary_add
    (F := fun s => (1 / (s₀ - ρ)) * (G s * (s - s₀)⁻¹ - G s * (s - ρ)⁻¹))
    (G := fun s => (1 / ρ) * (G s * (s - s₀)⁻¹)) hFa hFb hGa hGb
  have e2 := stripBoundary_sub (F := fun s => G s * (s - s₀)⁻¹) (G := fun s => G s * (s - ρ)⁻¹)
    (hint a (Or.inl rfl) s₀ (Or.inl rfl)) (hint b (Or.inr rfl) s₀ (Or.inl rfl))
    (hint a (Or.inl rfl) ρ (Or.inr rfl)) (hint b (Or.inr rfl) ρ (Or.inr rfl))
  rw [stripBoundary_congr (G := fun s => (1 / (s₀ - ρ)) * (G s * (s - s₀)⁻¹ - G s * (s - ρ)⁻¹)
      + (1 / ρ) * (G s * (s - s₀)⁻¹)) hpt,
    e1, stripBoundary_const_mul, stripBoundary_const_mul, e2, h1, h2]
  have hG0 : G s₀ = 1 := by
    show cubicG L (s₀ - s₀) = 1
    rw [sub_self]
    exact cubicG_zero hL.ne'
  have hGρ : G ρ = cubicG L (ρ - s₀) := rfl
  rw [hG0, hGρ]
  have hρs' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hρs
  unfold cubicKernel hadamardTerm
  field_simp
  ring

/-- The strip integral of the kernel alone is the residue of its pole: `2πi`. -/
theorem stripBoundary_cubicKernel {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    stripBoundary (fun s => cubicKernel L (s - s₀)) a b = 2 * Real.pi * I := by
  obtain ⟨C, hC, hdec⟩ := cubicG_strip_decay hL hab hs₀b
  have hGd : Differentiable ℂ (fun s => cubicG L (s - s₀)) :=
    (cubicG_differentiable L).comp (differentiable_id.sub_const s₀)
  have h := stripBoundary_div_sub_eq hGd (by norm_num : 2 ≤ 3) hC hab hdec hs₀a hs₀b
  have hF : (fun s => cubicKernel L (s - s₀)) = fun s => cubicG L (s - s₀) * (s - s₀)⁻¹ := by
    funext s
    simp only [cubicKernel, div_eq_mul_inv]
  rw [hF, h, sub_self, cubicG_zero hL.ne', mul_one]

/-- **The zero side with a simple pole of residue one at `s₀`, general form.** For `F` continuous
on the two lines with decay of order 4 there, whose per-zero strip residues are
`2πi (hadamardTerm ρ s₀ + F ρ)` and whose own strip integral is `2πi`,
`∮_strip F·ξ′/ξ = 2πi (ξ′/ξ(s₀) + Σ'_ρ m_ρ F(ρ))`, and the zero sum is summable. -/
theorem stripBoundary_pole_mul_logDeriv_xi {F : ℂ → ℂ} {s₀ : ℂ} (hs₀ : s₀ ∉ ZD.NontrivialZeros)
    {a b C : ℝ} (ha : a < 0) (hb : 1 < b) (hC : 0 ≤ C)
    (hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => F (σ + t * I)))
    (hdec : ∀ σ : ℝ, (σ = a ∨ σ = b) → LineDecay F σ C 4)
    (hres : ∀ ρ ∈ ZD.NontrivialZeros, stripBoundary (fun s => F s * hadamardTerm ρ s) a b
      = 2 * Real.pi * I * (hadamardTerm ρ s₀ + F ρ))
    (hpole : stripBoundary F a b = 2 * Real.pi * I) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) ∧
    stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (logDeriv ZD.riemannXi s₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  have hintF : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => F (σ + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hFc σ hσ) (by norm_num) hC (hdec σ hσ)
  -- each line integral decomposes into the constant part and the exchanged zero sum
  have hline : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      lineIntegral (fun s => F s * logDeriv ZD.riemannXi s) σ
        = A * lineIntegral F σ + ∑' ρ : Zero, ∫ t : ℝ, hadamardLineTerm F σ ρ t := by
    intro σ hσ
    unfold lineIntegral
    have hpt : ∀ t : ℝ, F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I)
        = A * F (σ + t * I) + ∑' ρ : Zero, hadamardLineTerm F σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * F (σ + t * I) + ∑' ρ : Zero, hadamardLineTerm F σ ρ t := funext hpt
    rw [hfun, integral_add ((hintF σ hσ).const_mul A)
      (integrable_tsum_of_summable_integral_norm
        (fun ρ => hadamardLineTerm_integrable_line (le_refl 4) hC ha hb hσ (hFc σ hσ) (hdec σ hσ) ρ)
        (summable_hadamardLineTerm_integral_norm_line (le_refl 4) hC ha hb hσ (hFc σ hσ)
          (hdec σ hσ))),
      integral_const_mul,
      lineIntegral_hadamard_exchange_line (le_refl 4) hC ha hb hσ (hFc σ hσ) (hdec σ hσ)]
  -- per zero: the two line integrals combine to the strip residue
  have hper : ∀ ρ : Zero,
      I * (∫ t : ℝ, hadamardLineTerm F b ρ t) - I * (∫ t : ℝ, hadamardLineTerm F a ρ t)
        = 2 * Real.pi * I * ((ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val s₀ + F ρ.val)) := by
    intro ρ
    have h := hres ρ.val ρ.property
    unfold stripBoundary lineIntegral at h
    have hb' : ∫ t : ℝ, hadamardLineTerm F b ρ t
        = (ZD.xiOrderNat ρ.val : ℂ) * ∫ t : ℝ, F (b + t * I) * hadamardTerm ρ.val (b + t * I) := by
      rw [← integral_const_mul]
      congr 1
      funext t
      unfold hadamardLineTerm
      ring
    have ha' : ∫ t : ℝ, hadamardLineTerm F a ρ t
        = (ZD.xiOrderNat ρ.val : ℂ) * ∫ t : ℝ, F (a + t * I) * hadamardTerm ρ.val (a + t * I) := by
      rw [← integral_const_mul]
      congr 1
      funext t
      unfold hadamardLineTerm
      ring
    beta_reduce at h
    linear_combination I * hb' - I * ha' + (ZD.xiOrderNat ρ.val : ℂ) * h
  have hsumb := summable_hadamardLineTerm_integral_line (le_refl 4) hC ha hb
    (Or.inr rfl : b = a ∨ b = b) (hFc b (Or.inr rfl)) (hdec b (Or.inr rfl))
  have hsuma := summable_hadamardLineTerm_integral_line (le_refl 4) hC ha hb
    (Or.inl rfl : a = a ∨ a = b) (hFc a (Or.inl rfl)) (hdec a (Or.inl rfl))
  have hsumH : Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s₀) :=
    CriticalLinePhasor.HilbertPolya.summable_hadamard_term hs₀
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hsumTot : Summable (fun ρ : Zero =>
      (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val s₀ + F ρ.val)) := by
    have hs : Summable (fun ρ : Zero =>
        2 * Real.pi * I * ((ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val s₀ + F ρ.val))) :=
      ((hsumb.mul_left I).sub (hsuma.mul_left I)).congr hper
    refine (hs.mul_left (2 * Real.pi * I)⁻¹).congr (fun ρ => ?_)
    field_simp
  have hsumK : Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) := by
    refine (hsumTot.sub hsumH).congr (fun ρ => ?_)
    ring
  refine ⟨hsumK, ?_⟩
  have hcomb : stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = A * stripBoundary F a b
        + ∑' ρ : Zero, (I * (∫ t : ℝ, hadamardLineTerm F b ρ t)
            - I * (∫ t : ℝ, hadamardLineTerm F a ρ t)) := by
    unfold stripBoundary
    rw [hline b (Or.inr rfl), hline a (Or.inl rfl),
      (hsumb.mul_left I).tsum_sub (hsuma.mul_left I), tsum_mul_left, tsum_mul_left]
    ring
  rw [hcomb, hpole, tsum_congr hper, tsum_mul_left]
  have hsplit : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val s₀ + F ρ.val)
      = (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s₀)
        + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val := by
    rw [← hsumH.tsum_add hsumK]
    congr 1
    funext ρ
    ring
  have hξ : logDeriv ZD.riemannXi s₀
      = A + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s₀ := by
    rw [logDeriv_apply, hA s₀ hs₀]
    rfl
  rw [hsplit, hξ]
  ring

/-- The zero side for the cubic kernel with its pole at `s₀`. -/
theorem stripBoundary_cubicKernel_mul_logDeriv_xi {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)) ∧
    stripBoundary (fun s => cubicKernel L (s - s₀) * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (logDeriv ZD.riemannXi s₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := cubicKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => cubicKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply cubicKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  exact stripBoundary_pole_mul_logDeriv_xi (F := fun s => cubicKernel L (s - s₀)) hs₀ ha hb hC
    hFc hdecl
    (fun ρ hρ => stripBoundary_cubicKernel_hadamardTerm hL ha hb hs₀a hs₀b hρ
      (fun h => hs₀ (h ▸ hρ)))
    (stripBoundary_cubicKernel hL hab hs₀a hs₀b)

/-! ## 9. The truncated explicit formula -/

/-- **The truncated explicit formula at the growth front `x = e^L`, cubic B-spline taper.**
For `s₀` off the zero set with `a < Re s₀ < b` (`a < 0 < 1 < b`):

  `ξ′/ξ(s₀) + Σ'_ρ m_ρ K(ρ − s₀)
     = (1/2π)[∫ K(b+it−s₀) E(b+it) dt + ∫ K(a+it−s₀) E(1−a−it) dt]
       − Σ_n W(log n) · Λ(n) n^{−s₀}`,

with `K = cubicKernel L`, `W = cubicProfile L` (exactly `1` for `n ≤ x`, `0` for `n ≥ x⁴`),
`E = weilArch`. The pole of `E` at `s = 1` inside the strip carries the END term `K(1 − s₀)`. -/
theorem truncated_explicit_formula_cubic {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀)
      = (1 / (2 * π)) * ((∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := cubicKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => cubicKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply cubicKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hFint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => cubicKernel L ((σ : ℂ) + t * I - s₀)) :=
    fun σ hσ => integrable_line_of_decay' (F := fun s => cubicKernel L (s - s₀)) (hFc σ hσ)
      (by norm_num) hC (hdecl σ hσ)
  obtain ⟨-, hzero⟩ := stripBoundary_cubicKernel_mul_logDeriv_xi hL hs₀ ha hb hs₀a hs₀b
  -- the right line
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hLb : lineIntegral (fun s => cubicKernel L (s - s₀) * logDeriv ZD.riemannXi s) b
      = (∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
        - 2 * π * ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (b + t * I)
        = cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
          - cubicKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) := by
      intro t
      rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        cubicKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hFint b (Or.inr rfl)) hθb hreb hb
    have hAint : Integrable (fun t : ℝ =>
        cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)) := by
      have h := (line_mul_logDeriv_xi_integrable' (F := fun s => cubicKernel L (s - s₀))
        (le_refl 4) hC ha hb (Or.inr rfl) (hFc b (Or.inr rfl)) (hdecl b (Or.inr rfl))).add hLint
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.add_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => cubicKernel L ((b : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (b + t * I))
        = fun t : ℝ => cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
            - cubicKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) :=
      funext hpt
    rw [hfun, integral_sub hAint hLint,
      lseries_line_exchange (hFint b (Or.inr rfl)) hθb hreb hb,
      tsum_congr (cubicKernel_prime_line_right hL hs₀b hC (hdecl b (Or.inr rfl))), tsum_mul_left]
  -- the left line
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hLa : lineIntegral (fun s => cubicKernel L (s - s₀) * logDeriv ZD.riemannXi s) a
      = -(∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (a + t * I)
        = -(cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
          + cubicKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := by
      intro t
      rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        cubicKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hFint a (Or.inl rfl)) hθa hrea h1a
    have hAint : Integrable (fun t : ℝ =>
        cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
      have h := hLint.sub (line_mul_logDeriv_xi_integrable' (F := fun s => cubicKernel L (s - s₀))
        (le_refl 4) hC ha hb (Or.inl rfl) (hFc a (Or.inl rfl)) (hdecl a (Or.inl rfl)))
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => cubicKernel L ((a : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (a + t * I))
        = fun t : ℝ => -(cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
            + cubicKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) :=
      funext hpt
    have hAint' : Integrable (fun t : ℝ =>
        -(cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))) := hAint.neg
    rw [hfun, integral_add hAint' hLint, integral_neg,
      lseries_line_exchange (hFint a (Or.inl rfl)) hθa hrea h1a,
      tsum_congr (cubicKernel_prime_line_left hL hs₀a hC (hdecl a (Or.inl rfl))), tsum_zero,
      add_zero]
  -- assemble
  unfold stripBoundary at hzero
  rw [hLb, hLa] at hzero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * cubicKernel L (ρ.val - s₀) with hS
  set X := logDeriv ZD.riemannXi s₀ with hX
  set Ab := ∫ t : ℝ, cubicKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I) with hAb
  set Aa := ∫ t : ℝ, cubicKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))
    with hAa
  set P := ∑' n : ℕ, (cubicProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n with hP
  have h2πS : 2 * (π : ℂ) * (X + S) = (Ab + Aa) - 2 * π * P := by
    linear_combination I * hzero + (2 * π * (X + S) - Ab - Aa + 2 * π * P) * Complex.I_sq
  have hS' : X + S = (Ab + Aa) / (2 * π) - P := by
    rw [eq_sub_iff_add_eq, eq_div_iff h2π]
    linear_combination h2πS
  rw [hS']
  ring

/-- The front is sharp: the weight is exactly `1` for `n ≤ e^L`. -/
theorem cubicProfile_log_eq_one {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n)
    (hx : (n : ℝ) ≤ Real.exp L) : cubicProfile L (Real.log n) = 1 := by
  apply cubicProfile_eq_one hL
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log n ≤ Real.log (Real.exp L) := Real.log_le_log hnr hx
    _ = L := Real.log_exp L

/-- The taper ends: the weight is exactly `0` for `n ≥ e^{4L}`. -/
theorem cubicProfile_log_eq_zero {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hx : Real.exp (4 * L) ≤ n) : cubicProfile L (Real.log n) = 0 := by
  apply cubicProfile_eq_zero hL
  have hpos : (0 : ℝ) < Real.exp (4 * L) := Real.exp_pos _
  calc 4 * L = Real.log (Real.exp (4 * L)) := (Real.log_exp _).symm
    _ ≤ Real.log n := Real.log_le_log hpos hx

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.truncated_explicit_formula_cubic
#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_pole_mul_logDeriv_xi
#print axioms CriticalLinePhasor.ContourArgument.cubicKernel_prime_line_right
