import Mathlib
import RequestProject.TruncatedFormulaEnds

/-!
# The truncated explicit formula for the Riesz window — the Hilbert finite stage (ledger 568)

Ledger 567 (Bochner): every taper with a plateau at a front `x > 1` has a signed on-line kernel, so
its finite-stage marriage measure is Krein by a universal shape constant. The route around is to
remove the plateau: the RIESZ window `w(n) = (1 − log n/log x)₊`, no phasor ever fully grown. Its
kernel is `K_R(w) = (x^w − 1)/(L w²) = expRatio(L, w)/w`, and on the line
`Re K_R(iu) = (1 − cos Lu)/(L u²) ≥ 0` — the Fejér kernel. Under RH the finite-stage density is a
POSITIVE measure at every front; an off-line pair enters with amplitude `x^{δ}` and a phase, so
`RH ⟺ D_{R,x}(t) ≥ 0 for all x > 1, t` (the density-register form of Weil positivity on the Fejér
class). This file compiles the identity for that window:

  `Σ_n (1 − log n/L)₊ Λ(n) n^{−s₀} = −ζ′/ζ(s₀) + K_R(1−s₀) + K_R(−s₀) − Σ′_ρ m_ρ K_R(ρ−s₀) + R_clock(s₀)`.

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real FourierTransform

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The Riesz kernel: `G = expRatio` -/

/-- `K_R(w) = expRatio(L,w)/w = (e^{Lw} − 1)/(L w²)`. -/
def rieszKernel (L : ℝ) (w : ℂ) : ℂ := expRatio L w / w

theorem rieszKernel_eq {L : ℝ} (hL : L ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    rieszKernel L w = (Complex.exp (L * w) - 1) / (w ^ 2 * L) := by
  unfold rieszKernel
  rw [expRatio_of_ne L hw]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  field_simp

/-- `expRatio` decays at order 1 on every half-plane `Re w ≤ b'`. -/
theorem expRatio_bound {L : ℝ} (hL : 0 < L) {b' : ℝ} (hb' : 0 ≤ b') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ b' → ‖expRatio L w‖ ≤ C / (1 + |w.im|) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (expRatio_differentiable L).continuous.continuousOn
  set E : ℝ := Real.exp (L * b') with hE
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
  set C : ℝ := max (2 * max M 0) (2 * ((E + 1) / L)) with hC
  refine ⟨C, by positivity, fun w hw => ?_⟩
  have hpos : 0 < 1 + |w.im| := by positivity
  by_cases h1 : ‖w‖ ≤ 1
  · have hMw : ‖expRatio L w‖ ≤ max M 0 :=
      le_trans (hM w (by simpa using h1)) (le_max_left _ _)
    have him : |w.im| ≤ 1 := le_trans (Complex.abs_im_le_norm w) h1
    rw [le_div_iff₀ hpos]
    calc ‖expRatio L w‖ * (1 + |w.im|) ≤ max M 0 * 2 :=
          mul_le_mul hMw (by linarith) (by positivity) (le_max_right _ _)
      _ = 2 * max M 0 := by ring
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
    rw [le_div_iff₀ hpos]
    have hwpos : 0 < ‖w‖ := by linarith
    calc ‖expRatio L w‖ * (1 + |w.im|) ≤ ((E + 1) / (L * ‖w‖)) * (2 * ‖w‖) :=
          mul_le_mul hratio hnorm (by positivity) (by positivity)
      _ = 2 * ((E + 1) / L) := by field_simp
      _ ≤ C := le_max_right _ _

theorem rieszG_strip_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (_hab : a ≤ b) {s₀ : ℂ}
    (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ T : ℝ,
      ‖expRatio L (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 1 := by
  obtain ⟨C₀, hC₀, hbound⟩ := expRatio_bound hL (b' := b - s₀.re) (by linarith)
  refine ⟨C₀ * (1 + |s₀.im|), by positivity, fun x hx T => ?_⟩
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
  have hpos1 : 0 < 1 + |T - s₀.im| := by positivity
  have hpos2 : 0 < 1 + |T| := by positivity
  rw [pow_one]
  calc ‖expRatio L ((x : ℂ) + T * I - s₀)‖ ≤ C₀ / (1 + |T - s₀.im|) := h
    _ ≤ C₀ * (1 + |s₀.im|) / (1 + |T|) := by
        rw [div_le_div_iff₀ hpos1 hpos2]
        calc C₀ * (1 + |T|) ≤ C₀ * ((1 + |s₀.im|) * (1 + |T - s₀.im|)) :=
              mul_le_mul_of_nonneg_left hkey hC₀
          _ = C₀ * (1 + |s₀.im|) * (1 + |T - s₀.im|) := by ring

theorem rieszKernel_line_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {s₀ : ℂ}
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, (σ = a ∨ σ = b) →
      LineDecay (fun s => rieszKernel L (s - s₀)) σ C 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := rieszG_strip_decay hL hab hs₀b
  set η : ℝ := min (s₀.re - a) (b - s₀.re) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  refine ⟨C₀ * ((1 + |s₀.im|) / η + 1), by positivity, fun σ hσ t => ?_⟩
  have hσab : σ ∈ Icc a b := by
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hG := hbound σ hσab t
  rw [pow_one] at hG
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
  show ‖rieszKernel L ((σ : ℂ) + t * I - s₀)‖ ≤ _
  unfold rieszKernel
  rw [norm_div]
  have hpos2 : 0 < (1 + |t|) ^ 2 := by positivity
  calc ‖expRatio L ((σ : ℂ) + t * I - s₀)‖ / ‖(σ : ℂ) + t * I - s₀‖
      ≤ (C₀ / (1 + |t|)) / ‖(σ : ℂ) + t * I - s₀‖ := div_le_div_of_nonneg_right hG hD0.le
    _ ≤ C₀ * ((1 + |s₀.im|) / η + 1) / (1 + |t|) ^ 2 := by
        rw [div_div, div_le_div_iff₀ (by positivity) hpos2]
        have h2 : (1 + |t|) ^ 2 = (1 + |t|) * (1 + |t|) := by ring
        rw [h2]
        calc C₀ * ((1 + |t|) * (1 + |t|))
            ≤ C₀ * ((1 + |t|) * (((1 + |s₀.im|) / η + 1) * ‖(σ : ℂ) + t * I - s₀‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey (by positivity)) hC₀
          _ = C₀ * ((1 + |s₀.im|) / η + 1) * ((1 + |t|) * ‖(σ : ℂ) + t * I - s₀‖) := by
              ring

theorem rieszKernel_line_continuous (L : ℝ) {σ : ℝ} {s₀ : ℂ} (h : σ ≠ s₀.re) :
    Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)) := by
  unfold rieszKernel
  refine ((expRatio_differentiable L).continuous.comp (by fun_prop)).div (by fun_prop) ?_
  intro t h0
  have := congrArg Complex.re h0
  simp at this
  exact h (by linarith)

/-! ## 2. Per-zero residue with the pole, and the pole alone -/

theorem stripBoundary_rieszKernel_hadamardTerm {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρs : ρ ≠ s₀) :
    stripBoundary (fun s => rieszKernel L (s - s₀) * hadamardTerm ρ s) a b
      = 2 * Real.pi * I * (hadamardTerm ρ s₀ + rieszKernel L (ρ - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdec⟩ := rieszG_strip_decay hL hab hs₀b
  set G : ℂ → ℂ := fun s => expRatio L (s - s₀) with hGdef
  have hGd : Differentiable ℂ G :=
    (expRatio_differentiable L).comp (differentiable_id.sub_const s₀)
  have hdecG : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖G (x + T * I)‖ ≤ C / (1 + |T|) ^ 1 := hdec
  have hρ0 : ρ ≠ 0 := zero_ne_zero hρ
  have hρa : a < ρ.re := by linarith [hρ.1]
  have hρb : ρ.re < b := by linarith [hρ.2.1]
  have h1 : stripBoundary (fun s => G s * (s - s₀)⁻¹) a b = 2 * Real.pi * I * G s₀ :=
    stripBoundary_div_sub_eq₁ hGd hC hab hdecG hs₀a hs₀b
  have h2 : stripBoundary (fun s => G s * (s - ρ)⁻¹) a b = 2 * Real.pi * I * G ρ :=
    stripBoundary_div_sub_eq₁ hGd hC hab hdecG hρa hρb
  have hne3 : s₀ - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρs)
  have hpt : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ,
      rieszKernel L ((σ : ℂ) + t * I - s₀) * hadamardTerm ρ ((σ : ℂ) + t * I)
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
    simp only [rieszKernel, hadamardTerm, hGdef]
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
    have hdecσ : LineDecay G σ C 1 := fun t => hdecG σ (hσab σ hσ) t
    have hp' : σ ≠ p.re := by
      rcases hσ with rfl | rfl <;> rcases hp with rfl | rfl <;> linarith
    exact integrable_line_mul_inv_sub₁ (hGd.continuous.comp (by fun_prop)) hC hdecσ hp'
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
    show expRatio L (s₀ - s₀) = 1
    rw [sub_self]
    exact expRatio_zero hL.ne'
  have hGρ : G ρ = expRatio L (ρ - s₀) := rfl
  rw [hG0, hGρ]
  have hρs' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hρs
  unfold rieszKernel hadamardTerm
  field_simp
  ring

theorem stripBoundary_rieszKernel {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    stripBoundary (fun s => rieszKernel L (s - s₀)) a b = 2 * Real.pi * I := by
  obtain ⟨C, hC, hdec⟩ := rieszG_strip_decay hL hab hs₀b
  have hGd : Differentiable ℂ (fun s => expRatio L (s - s₀)) :=
    (expRatio_differentiable L).comp (differentiable_id.sub_const s₀)
  have h := stripBoundary_div_sub_eq₁ hGd hC hab hdec hs₀a hs₀b
  have hF : (fun s => rieszKernel L (s - s₀)) = fun s => expRatio L (s - s₀) * (s - s₀)⁻¹ := by
    funext s
    simp only [rieszKernel, div_eq_mul_inv]
  rw [hF, h, sub_self, expRatio_zero hL.ne', mul_one]

/-- The zero side for the Riesz kernel with its pole at `s₀`. -/
theorem stripBoundary_rieszKernel_mul_logDeriv_xi {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀)) ∧
    stripBoundary (fun s => rieszKernel L (s - s₀) * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (logDeriv ZD.riemannXi s₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := rieszKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  exact stripBoundary_pole_mul_logDeriv_xi₂ (F := fun s => rieszKernel L (s - s₀)) hs₀ ha hb hC
    hFc hdecl
    (fun ρ hρ => stripBoundary_rieszKernel_hadamardTerm hL ha hb hs₀a hs₀b hρ
      (fun h => hs₀ (h ▸ hρ)))
    (stripBoundary_rieszKernel hL hab hs₀a hs₀b)

/-! ## 3. The Riesz window and the prime side -/

/-- The Riesz window in the log variable: `1` for `v ≤ 0`, `(L − v)/L` on `[0, L]`, `0` beyond —
no plateau above `n = 1`. -/
def rieszProfile (L v : ℝ) : ℝ := (rampR1 L v - rampR1 0 v) / L

/-- The reflected profile, supported on `v ≥ 0` (vanishing at `v ≤ 0`, so the left prime line is `0`). -/
def rieszProfileLeft (L v : ℝ) : ℝ := (rampL1 L v - rampL1 0 v) / L

theorem rieszProfile_continuous (L : ℝ) : Continuous (rieszProfile L) := by
  unfold rieszProfile
  have := rampR1_continuous
  fun_prop

theorem rieszProfileLeft_continuous (L : ℝ) : Continuous (rieszProfileLeft L) := by
  unfold rieszProfileLeft
  have := rampL1_continuous
  fun_prop

/-- On the bank, `n ≥ 1`: the weight is `(1 − log n/L)₊`. -/
theorem rieszProfile_eq {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : 0 ≤ v) :
    rieszProfile L v = max (1 - v / L) 0 := by
  unfold rieszProfile rampR1
  rw [zero_sub, max_eq_right (by linarith : -v ≤ 0), sub_zero]
  have hL0 : L ≠ 0 := hL.ne'
  rcases le_or_gt v L with h | h
  · rw [max_eq_left (by linarith : 0 ≤ L - v), max_eq_left (by rw [sub_nonneg, div_le_one hL]; exact h)]
    field_simp
  · rw [max_eq_right (by linarith : L - v ≤ 0), max_eq_right (by rw [sub_nonpos, one_le_div hL]; exact h.le)]
    simp

theorem rieszProfileLeft_eq_zero {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : v ≤ 0) :
    rieszProfileLeft L v = 0 := by
  unfold rieszProfileLeft
  rw [rampL1_eq_zero_of_le (by linarith), rampL1_eq_zero_of_le hv]
  simp

theorem rieszProfile_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun v : ℝ => (rieszProfile L v : ℂ) * Complex.exp (w * v)) := by
  have i2 := rampR1_mul_exp_integrable hw L
  have i1 := rampR1_mul_exp_integrable hw 0
  have h := (i2.sub i1).const_mul (1 / (L : ℂ))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [rieszProfile, Pi.sub_apply]
  push_cast
  ring

theorem rieszProfileLeft_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : w.re < 0) :
    Integrable (fun v : ℝ => (rieszProfileLeft L v : ℂ) * Complex.exp (w * v)) := by
  have i2 := rampL1_mul_exp_integrable hw L
  have i1 := rampL1_mul_exp_integrable hw 0
  have h := (i2.sub i1).const_mul (1 / (L : ℂ))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [rieszProfileLeft, Pi.sub_apply]
  push_cast
  ring

theorem rieszKernel_eq_laplace_right {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    rieszKernel L w = ∫ v : ℝ, (rieszProfile L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i2 := rampR1_mul_exp_integrable hw L
  have i1 := rampR1_mul_exp_integrable hw 0
  have hfun : (fun v : ℝ => (rieszProfile L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (L : ℂ)) * ((rampR1 L v : ℂ) * Complex.exp (w * v)
          - (rampR1 0 v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [rieszProfile]
    push_cast
    ring
  rw [hfun, integral_const_mul, integral_sub i2 i1, rampR1_laplace hw, rampR1_laplace hw,
    rieszKernel_eq hL0 hw0]
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  have e0 : Complex.exp (w * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [e1, e0]
  field_simp

theorem rieszKernel_eq_laplace_left {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w.re < 0) :
    rieszKernel L w = ∫ v : ℝ, (rieszProfileLeft L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i2 := rampL1_mul_exp_integrable hw L
  have i1 := rampL1_mul_exp_integrable hw 0
  have hfun : (fun v : ℝ => (rieszProfileLeft L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (L : ℂ)) * ((rampL1 L v : ℂ) * Complex.exp (w * v)
          - (rampL1 0 v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [rieszProfileLeft]
    push_cast
    ring
  rw [hfun, integral_const_mul, integral_sub i2 i1, rampL1_laplace hw, rampL1_laplace hw,
    rieszKernel_eq hL0 hw0]
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  have e0 : Complex.exp (w * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [e1, e0]
  field_simp

theorem rieszKernel_prime_line_right {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {b : ℝ} (hb : s₀.re < b)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => rieszKernel L (s - s₀)) b C 2) (n : ℕ) :
    ∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n
      = 2 * π * ((rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set w₀ : ℂ := (b : ℂ) - s₀ with hw₀
  have hw₀re : 0 < w₀.re := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (rieszProfile L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (rieszProfile_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := rieszProfile_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => rieszKernel L ((b : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : (0 : ℝ) < ((b : ℂ) + t * I - s₀).re := by simp; linarith
    show rieszKernel L ((b : ℂ) + t * I - s₀) = _
    rw [rieszKernel_eq_laplace_right hL hw]
    congr 1
    funext v
    rw [hφ]
    show (rieszProfile L v : ℂ) * Complex.exp (((b : ℂ) + t * I - s₀) * v)
      = (rieszProfile L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => rieszKernel L (s - s₀))
      (rieszKernel_line_continuous L (by linarith : b ≠ s₀.re)) (le_refl 2) hC hdec
  have hfun : (fun t : ℝ => rieszKernel L ((b : ℂ) + t * I - s₀)
        * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
          * (Φ t * Complex.exp (-(I * t * Real.log n))) := by
    funext t
    rw [term_line_eq b t hn, hΦdef]
    ring
  rw [hfun, integral_const_mul, line_transform_inversion hφc hφi hΦ hΦi (Real.log n)]
  rw [hφ]
  show (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
      * (2 * π * ((rieszProfile L (Real.log n) : ℂ) * Complex.exp (w₀ * Real.log n)))
    = 2 * π * ((rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n)
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
    (2 * (π : ℂ) * (rieszProfile L (Real.log n) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      * hpow

theorem rieszKernel_prime_line_left {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => rieszKernel L (s - s₀)) a C 2) (n : ℕ) :
    ∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀)
      * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (rieszProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (rieszProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := rieszProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => rieszKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show rieszKernel L ((a : ℂ) + t * I - s₀) = _
    rw [rieszKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (rieszProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (rieszProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => rieszKernel L (s - s₀))
      (rieszKernel_line_continuous L (by linarith : a ≠ s₀.re)) (le_refl 2) hC hdec
  have hrefl : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)) = (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    push_cast
    ring
  have hfun : (fun t : ℝ => rieszKernel L ((a : ℂ) + t * I - s₀)
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
      * (2 * π * ((rieszProfileLeft L (-Real.log n) : ℂ)
          * Complex.exp (w₀ * ((-Real.log n : ℝ) : ℂ))))
    = 0
  rw [rieszProfileLeft_eq_zero hL (by linarith : -Real.log n ≤ 0)]
  simp

/-! ## 4. The truncated formula for the Riesz window -/

theorem truncated_explicit_formula_riesz {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀)
      = (1 / (2 * π)) * ((∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := rieszKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hFint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)) :=
    fun σ hσ => integrable_line_of_decay' (F := fun s => rieszKernel L (s - s₀)) (hFc σ hσ)
      (le_refl 2) hC (hdecl σ hσ)
  obtain ⟨-, hzero⟩ := stripBoundary_rieszKernel_mul_logDeriv_xi hL hs₀ ha hb hs₀a hs₀b
  have hlineInt : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)
        * logDeriv ZD.riemannXi (σ + t * I)) := by
    intro σ hσ
    obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
    have hpt : ∀ t : ℝ, rieszKernel L ((σ : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (σ + t * I)
        = A * rieszKernel L ((σ : ℂ) + t * I - s₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => rieszKernel L (s - s₀)) σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * rieszKernel L ((σ : ℂ) + t * I - s₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => rieszKernel L (s - s₀)) σ ρ t := funext hpt
    rw [hfun]
    exact ((hFint σ hσ).const_mul A).add (integrable_tsum_of_summable_integral_norm
      (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hFc σ hσ) (hdecl σ hσ) ρ)
      (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdecl σ hσ)))
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hLb : lineIntegral (fun s => rieszKernel L (s - s₀) * logDeriv ZD.riemannXi s) b
      = (∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
        - 2 * π * ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (b + t * I)
        = rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
          - rieszKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) := by
      intro t
      rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        rieszKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hFint b (Or.inr rfl)) hθb hreb hb
    have hAint : Integrable (fun t : ℝ =>
        rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)) := by
      have h := (hlineInt b (Or.inr rfl)).add hLint
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.add_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((b : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (b + t * I))
        = fun t : ℝ => rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
            - rieszKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) :=
      funext hpt
    rw [hfun, integral_sub hAint hLint,
      lseries_line_exchange (hFint b (Or.inr rfl)) hθb hreb hb,
      tsum_congr (rieszKernel_prime_line_right hL hs₀b hC (hdecl b (Or.inr rfl))), tsum_mul_left]
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hLa : lineIntegral (fun s => rieszKernel L (s - s₀) * logDeriv ZD.riemannXi s) a
      = -(∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (a + t * I)
        = -(rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
          + rieszKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := by
      intro t
      rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        rieszKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hFint a (Or.inl rfl)) hθa hrea h1a
    have hAint : Integrable (fun t : ℝ =>
        rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
      have h := hLint.sub (hlineInt a (Or.inl rfl))
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((a : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (a + t * I))
        = fun t : ℝ => -(rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
            + rieszKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) :=
      funext hpt
    have hAint' : Integrable (fun t : ℝ =>
        -(rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))) := hAint.neg
    rw [hfun, integral_add hAint' hLint, integral_neg,
      lseries_line_exchange (hFint a (Or.inl rfl)) hθa hrea h1a,
      tsum_congr (rieszKernel_prime_line_left hL hs₀a hC (hdecl a (Or.inl rfl))), tsum_zero,
      add_zero]
  unfold stripBoundary at hzero
  rw [hLb, hLa] at hzero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀) with hS
  set X := logDeriv ZD.riemannXi s₀ with hX
  set Ab := ∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I) with hAb
  set Aa := ∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))
    with hAa
  set P := ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n with hP
  have h2πS : 2 * (π : ℂ) * (X + S) = (Ab + Aa) - 2 * π * P := by
    linear_combination I * hzero + (2 * π * (X + S) - Ab - Aa + 2 * π * P) * Complex.I_sq
  have hS' : X + S = (Ab + Aa) / (2 * π) - P := by
    rw [eq_sub_iff_add_eq, eq_div_iff h2π]
    linear_combination h2πS
  rw [hS']
  ring

/-! ## 5. Ends extracted and the classical form -/

theorem rieszKernel_left_line_integral {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => rieszKernel L (s - s₀)) a C 2) :
    ∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) = 0 := by
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (rieszProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (rieszProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := rieszProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => rieszKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show rieszKernel L ((a : ℂ) + t * I - s₀) = _
    rw [rieszKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (rieszProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (rieszProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => rieszKernel L (s - s₀))
      (rieszKernel_line_continuous L (by linarith : a ≠ s₀.re)) (le_refl 2) hC hdec
  have h := line_transform_inversion hφc hφi hΦ hΦi 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h
  rw [hΦdef] at h
  rw [h, hφ]
  simp only [rieszProfileLeft_eq_zero hL (le_refl (0 : ℝ)), Complex.ofReal_zero, zero_mul,
    mul_zero]

theorem truncated_explicit_formula_riesz_ends {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (h0 : s₀ ≠ 0) (h1 : s₀ ≠ 1) {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀)
      = (weilEnds s₀ + rieszKernel L (1 - s₀) + rieszKernel L (-s₀))
        + (1 / (2 * π)) * ((∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
          + (∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  have hmain := truncated_explicit_formula_riesz hL hs₀ ha hb hs₀a hs₀b
  obtain ⟨C, hC, hdecl⟩ := rieszKernel_line_decay hL hab hs₀a hs₀b
  obtain ⟨C₀, hC₀, hdecG⟩ := rieszG_strip_decay hL hab hs₀b
  set K : ℂ → ℂ := fun s => rieszKernel L (s - s₀) with hKdef
  have hK : ∀ s, K s = expRatio L (s - s₀) / (s - s₀) := fun s => rfl
  have hKc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => K ((σ : ℂ) + t * I)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hKint : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => K ((σ : ℂ) + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hKc σ hσ) (le_refl 2) hC (hdecl σ hσ)
  have hlineInt : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I)) := by
    intro σ hσ
    obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
    have hpt : ∀ t : ℝ, K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I)
        = A * K ((σ : ℂ) + t * I) + ∑' ρ : Zero, hadamardLineTerm K σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => K ((σ : ℂ) + t * I) * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * K ((σ : ℂ) + t * I) + ∑' ρ : Zero, hadamardLineTerm K σ ρ t :=
      funext hpt
    rw [hfun]
    exact ((hKint σ hσ).const_mul A).add (integrable_tsum_of_summable_integral_norm
      (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hKc σ hσ) (hdecl σ hσ) ρ)
      (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdecl σ hσ)))
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hAb : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * weilArch ((b : ℂ) + t * I)) := by
    have hLint : Integrable (fun t : ℝ => K ((b : ℂ) + t * I) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hKint b (Or.inr rfl)) hθb hreb hb
    have h := (hlineInt b (Or.inr rfl)).add hLint
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply]
    rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
    ring
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hAa : Integrable (fun t : ℝ => K ((a : ℂ) + t * I) * weilArch (1 - ((a : ℂ) + t * I))) := by
    have hLint : Integrable (fun t : ℝ =>
        K ((a : ℂ) + t * I) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hKint a (Or.inl rfl)) hθa hrea h1a
    have h := hLint.sub (hlineInt a (Or.inl rfl))
    refine h.congr (Eventually.of_forall (fun t => ?_))
    simp only [Pi.sub_apply]
    rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
    ring
  have hleft : ∫ t : ℝ, K ((a : ℂ) + t * I) = 0 :=
    rieszKernel_left_line_integral hL hs₀a hC (hdecl a (Or.inl rfl))
  have hends := archLines_ends (expRatio_differentiable L) (expRatio_zero hL.ne') hC₀ hC ha hb
    hdecG hs₀a hs₀b h0 h1 K hK hKc hdecl hAb hAa hleft
  have hK0 : K 0 = rieszKernel L (-s₀) := by rw [hKdef]; simp
  have hK1 : K 1 = rieszKernel L (1 - s₀) := rfl
  rw [hK0, hK1] at hends
  simp only [hKdef] at hends
  rw [hmain, hends]
  have h2π : (1 / (2 * (π : ℂ))) * (2 * π) = 1 := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  linear_combination (weilEnds s₀ + rieszKernel L (-s₀) + rieszKernel L (1 - s₀)) * h2π

/-- **The Riesz-window identity in classical form.** -/
theorem riesz_identity_classical {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) (hre : 0 < s₀.re) (h1 : s₀ ≠ 1) (hz : riemannZeta s₀ ≠ 0)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n
      = -logDeriv riemannZeta s₀ + rieszKernel L (1 - s₀) + rieszKernel L (-s₀)
        - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - s₀)
        + ((1 / (2 * π)) * ((∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - s₀) * weilClock ((b : ℂ) + t * I))
            + (∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - s₀) * weilClock (1 - ((a : ℂ) + t * I))))
          - weilClock s₀) := by
  have h0 : s₀ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hends := truncated_explicit_formula_riesz_ends hL hs₀ h0 h1 ha hb hs₀a hs₀b
  have hsplice := CriticalLinePhasor.SeatingLedger.logDeriv_riemannXi_splice hre h1 hz
  have hξ : logDeriv ZD.riemannXi s₀ = weilEnds s₀ + weilClock s₀ + logDeriv riemannZeta s₀ := by
    rw [hsplice]; unfold weilEnds weilClock; ring
  rw [hξ] at hends
  linear_combination hends

/-- **The Fejér kernel on the line**: for an on-line zero the Riesz comb term has nonnegative real
part, `Re K_R(iu) = (1 − cos Lu)/(L u²) ≥ 0`. -/
theorem rieszKernel_re_on_line_nonneg {L : ℝ} (hL : 0 < L) (u : ℝ) :
    0 ≤ (rieszKernel L (u * I)).re := by
  by_cases hu : u = 0
  · subst hu
    simp [rieszKernel]
  have hw : (u : ℂ) * I ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hu (by exact_mod_cast h')
    · exact I_ne_zero h'
  rw [rieszKernel_eq hL.ne' hw]
  have hsq : ((u : ℂ) * I) ^ 2 = -((u : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [hsq]
  have hden : (-((u : ℂ) ^ 2) * L) ≠ 0 := by
    have : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    simp [*]
  have e : (Complex.exp (L * ((u : ℂ) * I)) - 1) / (-((u : ℂ) ^ 2) * L)
      = ((1 - Complex.exp ((L * u : ℝ) * I)) / ((u ^ 2 * L : ℝ) : ℂ)) := by
    have : (L : ℂ) * ((u : ℂ) * I) = ((L * u : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]
    push_cast
    field_simp
    ring
  rw [e, Complex.div_ofReal_re]
  have hpos : 0 < u ^ 2 * L := by positivity
  apply div_nonneg _ hpos.le
  rw [sub_re, one_re, Complex.exp_ofReal_mul_I_re]
  linarith [Real.cos_le_one (L * u)]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.truncated_explicit_formula_riesz
#print axioms CriticalLinePhasor.ContourArgument.riesz_identity_classical
#print axioms CriticalLinePhasor.ContourArgument.rieszKernel_re_on_line_nonneg
