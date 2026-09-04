import Mathlib
import RequestProject.RieszTruncatedFormula

/-!
# The Riesz truncated formula AT A ZERO: multiplicity read from primes (ledger 584)

At `s₀ = ρ₀` a nontrivial zero, the kernel's pole meets the zero's pole. The compiled formula
(`truncated_explicit_formula_riesz`) needs `s₀ ∉ zeros`; here the identity is extended to the zero
itself. The only new residue is the DOUBLE pole: with `G(w) = expRatio L w` (entire, `G(0) = 1`),

  `∮ G(s−ρ₀)/(s−ρ₀)² ds = 2πi·G′(0)`,

obtained by writing `G(s−ρ₀)/(s−ρ₀)² = dslope G ρ₀ (s)/(s−ρ₀) + (s−ρ₀)⁻²`: the first term is the
compiled simple-pole residue of an entire, decaying quotient, the second integrates to `0` along each
vertical line (fundamental theorem of calculus with the antiderivative `i·(s−ρ₀)⁻¹`).

Consequences (§3–§4): the per-zero residue at the evaluation zero itself is
`∮ K_R·hadamardTerm ρ₀ = 2πi(1/ρ₀ + G′(0))`, and the truncated explicit formula at `ρ₀` reads

  `xiFinitePart ρ₀ + Σ'_{ρ} m_ρ K_R(ρ − ρ₀) + m_{ρ₀}·G′(0) = (1/2π)(lines) − Σ_n W(log n) Λ(n) n^{−ρ₀}`,

where `xiFinitePart ρ₀ = A + Σ'_ρ m_ρ (1/(ρ₀−ρ) + 1/ρ)` is the finite part of `ξ′/ξ` at the zero
(the Hadamard constant plus the sum with the self-term read as `1/ρ₀`), and the `ρ = ρ₀` entry of
the kernel sum is `K_R(0) = 0` in Lean's total division. Since `G′(0) = L/2`, THE MULTIPLICITY
`m_{ρ₀}` IS READ BY THE FRONT: `m_{ρ₀}·L/2 = (prime side) − xiFinitePart ρ₀ − Σ_{ρ≠ρ₀} m_ρ K_R(ρ−ρ₀)`.
Measured (`tmp/att584_multiplicity_readout.py`): `(2π/L)·D_{R,x}(γ) = 1.00` to `1%` at the first
13 zeros for `x = 10³…10⁵`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real FourierTransform

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Vertical-line facts for the double pole -/

theorem line_sub_ne_zero {σ : ℝ} {p : ℂ} (hp : σ ≠ p.re) (t : ℝ) :
    (σ : ℂ) + t * I - p ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hp (by linarith)

/-- `‖(σ + it − p)⁻¹‖ ≤ C/(1+|t|)` on a vertical line off the pole. -/
theorem inv_line_bound {σ : ℝ} {p : ℂ} (hp : σ ≠ p.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖((σ : ℂ) + t * I - p)⁻¹‖ ≤ C / (1 + |t|) := by
  set δ : ℝ := |σ - p.re| with hδ
  have hδ0 : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hp)
  refine ⟨max ((2 + 2 * |p.im|) / δ) 2, by positivity, fun t => ?_⟩
  have hpos : 0 < 1 + |t| := by positivity
  set z : ℂ := (σ : ℂ) + t * I - p with hz
  have hzre : z.re = σ - p.re := by simp [hz]
  have hzim : z.im = t - p.im := by simp [hz]
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (line_sub_ne_zero hp t)
  have hre : δ ≤ ‖z‖ := by rw [hδ, ← hzre]; exact Complex.abs_re_le_norm z
  have him : |t - p.im| ≤ ‖z‖ := by rw [← hzim]; exact Complex.abs_im_le_norm z
  have key : 1 + |t| ≤ max ((2 + 2 * |p.im|) / δ) 2 * ‖z‖ := by
    by_cases hT : |t| ≤ 2 * |p.im| + 1
    · calc 1 + |t| ≤ 2 + 2 * |p.im| := by linarith
        _ = ((2 + 2 * |p.im|) / δ) * δ := by field_simp
        _ ≤ ((2 + 2 * |p.im|) / δ) * ‖z‖ := by gcongr
        _ ≤ max ((2 + 2 * |p.im|) / δ) 2 * ‖z‖ := by gcongr; exact le_max_left _ _
    · have hT' : 2 * |p.im| + 1 < |t| := not_le.mp hT
      have h1 : |t| - |p.im| ≤ |t - p.im| := abs_sub_abs_le_abs_sub t p.im
      calc 1 + |t| ≤ 2 * |t - p.im| := by linarith
        _ ≤ 2 * ‖z‖ := by gcongr
        _ ≤ max ((2 + 2 * |p.im|) / δ) 2 * ‖z‖ := by gcongr; exact le_max_right _ _
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hz0 hpos]
  linarith

theorem integrable_inv_sq_line {σ : ℝ} {p : ℂ} (hp : σ ≠ p.re) :
    Integrable (fun t : ℝ => ((σ : ℂ) + t * I - p)⁻¹ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := inv_line_bound hp
  have hcont : Continuous (fun t : ℝ => ((σ : ℂ) + t * I - p)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (line_sub_ne_zero hp)
  have h := integrable_line_mul_inv_sub₁ (F := fun s => (s - p)⁻¹) (σ := σ) hcont hC
    (fun t => by simpa using hb t) hp
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp [sq]

/-- Along a vertical line off the pole, `∫ (σ + it − p)⁻² dt = 0`. -/
theorem lineIntegral_inv_sq {σ : ℝ} {p : ℂ} (hp : σ ≠ p.re) :
    ∫ t : ℝ, ((σ : ℂ) + t * I - p)⁻¹ ^ 2 = 0 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => I * ((σ : ℂ) + t * I - p)⁻¹)
      (((σ : ℂ) + t * I - p)⁻¹ ^ 2) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h1 : HasDerivAt (fun t : ℝ => (σ : ℂ) + t * I - p) I t := by
      have := ((h0.mul_const I).const_add (σ : ℂ)).sub_const p
      simpa using this
    have hne := line_sub_ne_zero hp t
    have h2 := (h1.inv hne).const_mul I
    refine h2.congr_deriv ?_
    field_simp
    rw [Complex.I_sq]
    ring
  obtain ⟨C, hC, hb⟩ := inv_line_bound hp
  have hlimTop : Tendsto (fun t : ℝ => C / (1 + |t|)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_abs_atTop_atTop)
  have hlimBot : Tendsto (fun t : ℝ => C / (1 + |t|)) atBot (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_abs_atBot_atTop)
  have hnorm : ∀ t : ℝ, ‖I * ((σ : ℂ) + t * I - p)⁻¹‖ ≤ C / (1 + |t|) := by
    intro t
    rw [norm_mul, Complex.norm_I, one_mul]
    exact hb t
  have htop : Tendsto (fun t : ℝ => I * ((σ : ℂ) + t * I - p)⁻¹) atTop (𝓝 0) :=
    squeeze_zero_norm hnorm hlimTop
  have hbot : Tendsto (fun t : ℝ => I * ((σ : ℂ) + t * I - p)⁻¹) atBot (𝓝 0) :=
    squeeze_zero_norm hnorm hlimBot
  have := integral_of_hasDerivAt_of_tendsto hderiv (integrable_inv_sq_line hp) hbot htop
  rw [this, sub_zero]

theorem stripBoundary_inv_sq {a b : ℝ} {p : ℂ} (hpa : a < p.re) (hpb : p.re < b) :
    stripBoundary (fun s => (s - p)⁻¹ ^ 2) a b = 0 := by
  unfold stripBoundary lineIntegral
  rw [lineIntegral_inv_sq (ne_of_lt hpb).symm, lineIntegral_inv_sq (ne_of_lt hpa)]
  simp

/-! ## 2. The double-pole strip residue -/

/-- **The double pole.** For `G` entire with `G p = 1` and a decaying difference quotient,
`∮ G(s)/(s−p)² = 2πi·G′(p)`. -/
theorem stripBoundary_div_sq_eq {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a b C : ℝ} (hC : 0 ≤ C)
    (hab : a ≤ b) {p : ℂ} (hG1 : G p = 1)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖dslope G p (x + T * I)‖ ≤ C / (1 + |T|) ^ 1)
    (hpa : a < p.re) (hpb : p.re < b) :
    stripBoundary (fun s => G s * (s - p)⁻¹ ^ 2) a b = 2 * Real.pi * I * deriv G p := by
  have hD : Differentiable ℂ (dslope G p) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (f := G) (s := univ) (c := p) univ_mem).mpr
      hG.differentiableOn
  have h1 := stripBoundary_div_sub_eq₁ hD hC hab hdec hpa hpb
  rw [dslope_same] at h1
  have h2 := stripBoundary_inv_sq hpa hpb
  have hσab : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ∈ Icc a b := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hσp : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ≠ p.re := by
    intro σ hσ
    rcases hσ with rfl | rfl <;> linarith
  have hint1 : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => dslope G p (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) := by
    intro σ hσ
    exact integrable_line_mul_inv_sub₁ (hD.continuous.comp (by fun_prop)) hC
      (fun t => hdec σ (hσab σ hσ) t) (hσp σ hσ)
  have hint2 : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => ((σ : ℂ) + t * I - p)⁻¹ ^ 2) :=
    fun σ hσ => integrable_inv_sq_line (hσp σ hσ)
  have hpt : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ,
      G (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹ ^ 2
        = dslope G p (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹ + ((σ : ℂ) + t * I - p)⁻¹ ^ 2 := by
    intro σ hσ t
    have hne := line_sub_ne_zero (hσp σ hσ) t
    have hne' : (σ : ℂ) + t * I ≠ p := sub_ne_zero.mp hne
    rw [dslope_of_ne _ hne', slope_def_field, hG1]
    field_simp
    ring
  rw [stripBoundary_congr (G := fun s => dslope G p s * (s - p)⁻¹ + (s - p)⁻¹ ^ 2) hpt,
    stripBoundary_add (hint1 a (Or.inl rfl)) (hint1 b (Or.inr rfl)) (hint2 a (Or.inl rfl))
      (hint2 b (Or.inr rfl)), h1, h2, add_zero]

/-- The difference quotient of `G = expRatio L (· − ρ₀)` at `ρ₀` decays at order 1 on the strip. -/
theorem dslope_expRatio_strip_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ₀ : ℂ}
    (hρa : a < ρ₀.re) (hρb : ρ₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ T : ℝ,
      ‖dslope (fun s => expRatio L (s - ρ₀)) ρ₀ (x + T * I)‖ ≤ C / (1 + |T|) ^ 1 := by
  set G : ℂ → ℂ := fun s => expRatio L (s - ρ₀) with hGdef
  have hGd : Differentiable ℂ G :=
    (expRatio_differentiable L).comp (differentiable_id.sub_const ρ₀)
  have hD : Differentiable ℂ (dslope G ρ₀) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (f := G) (s := univ) (c := ρ₀) univ_mem).mpr
      hGd.differentiableOn
  obtain ⟨C₀, hC₀, hG⟩ := expRatio_bound hL (b' := b - ρ₀.re) (by linarith)
  set R : ℝ := (b - a) + 1 with hR
  obtain ⟨M, hM⟩ := (isCompact_closedBall ρ₀ R).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  set C : ℝ := max (max M 0 * (2 + |ρ₀.im|)) (2 * (C₀ + 1) * (1 + |ρ₀.im|)) with hC
  refine ⟨C, by positivity, fun x hx T => ?_⟩
  rw [pow_one]
  have hpos : 0 < 1 + |T| := by positivity
  set s : ℂ := x + T * I with hs
  have hsre : (s - ρ₀).re = x - ρ₀.re := by simp [hs]
  have hsim : (s - ρ₀).im = T - ρ₀.im := by simp [hs]
  by_cases hnear : |T - ρ₀.im| ≤ 1
  · have hsball : s ∈ Metric.closedBall ρ₀ R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hre : |(s - ρ₀).re| ≤ b - a := by
        rw [hsre, abs_le]; constructor <;> linarith [hx.1, hx.2]
      have him : |(s - ρ₀).im| ≤ 1 := by rw [hsim]; exact hnear
      calc ‖s - ρ₀‖ ≤ |(s - ρ₀).re| + |(s - ρ₀).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ (b - a) + 1 := add_le_add hre him
    have hMs : ‖dslope G ρ₀ s‖ ≤ max M 0 := le_trans (hM s hsball) (le_max_left _ _)
    have hT : 1 + |T| ≤ 2 + |ρ₀.im| := by
      have := abs_sub_abs_le_abs_sub T ρ₀.im
      linarith
    rw [le_div_iff₀ hpos]
    calc ‖dslope G ρ₀ s‖ * (1 + |T|) ≤ max M 0 * (2 + |ρ₀.im|) :=
          mul_le_mul hMs hT hpos.le (le_max_right _ _)
      _ ≤ C := le_max_left _ _
  · have hfar : 1 < |T - ρ₀.im| := not_le.mp hnear
    have hne : s ≠ ρ₀ := by
      intro h
      have : (s - ρ₀).im = 0 := by rw [h, sub_self]; simp
      rw [hsim] at this
      rw [this] at hfar
      simp at hfar
      linarith
    rw [dslope_of_ne _ hne, slope_def_field]
    have hGs : ‖G s‖ ≤ C₀ := by
      have h := hG (s - ρ₀) (by rw [hsre]; linarith [hx.2])
      calc ‖G s‖ = ‖expRatio L (s - ρ₀)‖ := rfl
        _ ≤ C₀ / (1 + |(s - ρ₀).im|) := h
        _ ≤ C₀ := div_le_self hC₀ (by linarith [abs_nonneg (s - ρ₀).im])
    have hG0 : ‖G ρ₀‖ = 1 := by
      show ‖expRatio L (ρ₀ - ρ₀)‖ = 1
      rw [sub_self, expRatio_zero hL.ne', norm_one]
    have hden : |T - ρ₀.im| ≤ ‖s - ρ₀‖ := by
      rw [← hsim]; exact Complex.abs_im_le_norm (s - ρ₀)
    have h1 : ‖(G s - G ρ₀) / (s - ρ₀)‖ ≤ (C₀ + 1) / |T - ρ₀.im| := by
      rw [norm_div]
      apply div_le_div₀ (by positivity) ?_ (by linarith) hden
      calc ‖G s - G ρ₀‖ ≤ ‖G s‖ + ‖G ρ₀‖ := norm_sub_le _ _
        _ ≤ C₀ + 1 := by rw [hG0]; linarith
    have hT : 1 + |T| ≤ 2 * (1 + |ρ₀.im|) * |T - ρ₀.im| := by
      have h1' := abs_sub_abs_le_abs_sub T ρ₀.im
      have h2' : 0 ≤ |ρ₀.im| := abs_nonneg _
      nlinarith [abs_nonneg (T - ρ₀.im)]
    have hden0 : 0 < |T - ρ₀.im| := by linarith
    rw [le_div_iff₀ hpos]
    calc ‖(G s - G ρ₀) / (s - ρ₀)‖ * (1 + |T|)
        ≤ ((C₀ + 1) / |T - ρ₀.im|) * (2 * (1 + |ρ₀.im|) * |T - ρ₀.im|) :=
          mul_le_mul h1 hT hpos.le (by positivity)
      _ = 2 * (C₀ + 1) * (1 + |ρ₀.im|) := by field_simp
      _ ≤ C := le_max_right _ _

/-! ## 3. The self residue of the Riesz kernel at its own zero -/

/-- `∮ K_R(s−ρ₀)·hadamardTerm ρ₀ s = 2πi(1/ρ₀ + G′(0))`, `G = expRatio L`. -/
theorem stripBoundary_rieszKernel_hadamardTerm_self {L : ℝ} (hL : 0 < L) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    stripBoundary (fun s => rieszKernel L (s - ρ₀) * hadamardTerm ρ₀ s) a b
      = 2 * Real.pi * I * (1 / ρ₀ + deriv (expRatio L) 0) := by
  have hab : a ≤ b := by linarith
  have hρa : a < ρ₀.re := by linarith [hρ₀.1]
  have hρb : ρ₀.re < b := by linarith [hρ₀.2.1]
  have hρ0 : ρ₀ ≠ 0 := zero_ne_zero hρ₀
  set G : ℂ → ℂ := fun s => expRatio L (s - ρ₀) with hGdef
  have hGd : Differentiable ℂ G :=
    (expRatio_differentiable L).comp (differentiable_id.sub_const ρ₀)
  have hG1 : G ρ₀ = 1 := by
    show expRatio L (ρ₀ - ρ₀) = 1
    rw [sub_self, expRatio_zero hL.ne']
  obtain ⟨C, hC, hdec⟩ := dslope_expRatio_strip_decay hL hab hρa hρb
  have hdouble := stripBoundary_div_sq_eq hGd hC hab hG1 hdec hρa hρb
  have hsingle := stripBoundary_rieszKernel hL hab hρa hρb
  have hσp : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ≠ ρ₀.re := by
    intro σ hσ
    rcases hσ with rfl | rfl <;> linarith
  have hpt : ∀ σ : ℝ, (σ = a ∨ σ = b) → ∀ t : ℝ,
      rieszKernel L ((σ : ℂ) + t * I - ρ₀) * hadamardTerm ρ₀ ((σ : ℂ) + t * I)
        = G ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - ρ₀)⁻¹ ^ 2
          + (1 / ρ₀) * rieszKernel L ((σ : ℂ) + t * I - ρ₀) := by
    intro σ hσ t
    have hne := line_sub_ne_zero (hσp σ hσ) t
    simp only [rieszKernel, hadamardTerm, hGdef]
    field_simp
  obtain ⟨C₂, hC₂, hdecK⟩ := rieszKernel_line_decay hL hab hρa hρb
  have hKc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hKint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => (1 / ρ₀) * rieszKernel L ((σ : ℂ) + t * I - ρ₀)) :=
    fun σ hσ => (integrable_line_of_decay' (F := fun s => rieszKernel L (s - ρ₀)) (hKc σ hσ)
      (le_refl 2) hC₂ (hdecK σ hσ)).const_mul _
  obtain ⟨C₀, hC₀, hGb⟩ := expRatio_bound hL (b' := b - ρ₀.re) (by linarith)
  have hGint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => G ((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - ρ₀)⁻¹ ^ 2) := by
    intro σ hσ
    have hσb : σ ≤ b := by rcases hσ with rfl | rfl <;> linarith
    have hbdd : ∀ t : ℝ, ‖G ((σ : ℂ) + t * I)‖ ≤ C₀ := by
      intro t
      have h := hGb ((σ : ℂ) + t * I - ρ₀) (by simp; linarith)
      calc ‖G ((σ : ℂ) + t * I)‖ = ‖expRatio L ((σ : ℂ) + t * I - ρ₀)‖ := rfl
        _ ≤ C₀ / (1 + |((σ : ℂ) + t * I - ρ₀).im|) := h
        _ ≤ C₀ := div_le_self hC₀ (by linarith [abs_nonneg ((σ : ℂ) + t * I - ρ₀).im])
    have hmeas : AEStronglyMeasurable (fun t : ℝ => G ((σ : ℂ) + t * I)) volume :=
      (hGd.continuous.comp (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + t * I))).aestronglyMeasurable
    exact (integrable_inv_sq_line (hσp σ hσ)).bdd_mul hmeas (Eventually.of_forall hbdd)
  rw [stripBoundary_congr
      (G := fun s => G s * (s - ρ₀)⁻¹ ^ 2 + (1 / ρ₀) * rieszKernel L (s - ρ₀)) hpt,
    stripBoundary_add (hGint a (Or.inl rfl)) (hGint b (Or.inr rfl)) (hKint a (Or.inl rfl))
      (hKint b (Or.inr rfl)), hdouble, stripBoundary_const_mul, hsingle]
  have hdG : deriv G ρ₀ = deriv (expRatio L) 0 := by
    rw [hGdef, deriv_comp_sub_const, sub_self]
  rw [hdG]
  ring

/-! ## 4. The finite part of `ξ′/ξ` and the pole theorem at a zero -/

/-- The Hadamard partial-fraction sum converges at EVERY `s` (at a zero the self-term is read as
`1/ρ`): the tail bound never used `s ∉ zeros`. -/
theorem summable_hadamard_term_any (s : ℂ) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s) := by
  have hg : Summable (fun ρ : Zero =>
      (2 * ‖s‖) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge (2 * ‖s‖ + 2)] with ρ hbig
  have hρ0 : ρ.val ≠ 0 := CriticalLinePhasor.HilbertPolya.ne_zero_of_mem_nontrivialZeros ρ.2
  have hnorms : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  have hsρ : s - ρ.val ≠ 0 := by
    intro h
    have : ρ.val = s := (sub_eq_zero.mp h).symm
    rw [this] at hbig
    linarith
  have hid : hadamardTerm ρ.val s = s / ((s - ρ.val) * ρ.val) := by
    unfold hadamardTerm
    field_simp
    ring
  have hnormρ : (0 : ℝ) < ‖ρ.val‖ := by
    have : (0 : ℝ) ≤ 2 * ‖s‖ := by positivity
    linarith
  have hlow : ‖ρ.val‖ / 2 ≤ ‖s - ρ.val‖ := by
    have h1 : ‖ρ.val‖ - ‖s‖ ≤ ‖s - ρ.val‖ := by
      calc ‖ρ.val‖ - ‖s‖ ≤ ‖ρ.val - s‖ := norm_sub_norm_le _ _
        _ = ‖s - ρ.val‖ := norm_sub_rev _ _
    linarith
  have hsub0 : (0 : ℝ) < ‖s - ρ.val‖ := by
    have : (0 : ℝ) < ‖ρ.val‖ / 2 := by linarith
    linarith
  calc ‖(ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s‖
      = (ZD.xiOrderNat ρ.val : ℝ) * (‖s‖ / (‖s - ρ.val‖ * ‖ρ.val‖)) := by
        rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ) * (‖s‖ / (‖ρ.val‖ ^ 2 / 2)) := by
        have hXY : ‖ρ.val‖ ^ 2 / 2 ≤ ‖s - ρ.val‖ * ‖ρ.val‖ := by nlinarith
        gcongr
    _ = (2 * ‖s‖) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        field_simp

/-- The Hadamard constant of `ξ′/ξ`. -/
def xiHadamardConst : ℂ := Classical.choose ZD.xi_logDeriv_partial_fraction

theorem xiHadamardConst_spec : ∀ s : ℂ, s ∉ ZD.NontrivialZeros →
    deriv ZD.riemannXi s / ZD.riemannXi s
      = xiHadamardConst + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) :=
  Classical.choose_spec ZD.xi_logDeriv_partial_fraction

/-- **The finite part of `ξ′/ξ`**: `A + Σ'_ρ m_ρ (1/(s−ρ) + 1/ρ)`, which equals `ξ′/ξ(s)` off the
zeros and, at a zero `ρ₀`, is the finite part of the Laurent expansion (the self-term reads `1/ρ₀`). -/
def xiFinitePart (s : ℂ) : ℂ :=
  xiHadamardConst + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val s

theorem xiFinitePart_eq_logDeriv {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) :
    xiFinitePart s = logDeriv ZD.riemannXi s := by
  rw [logDeriv_apply, xiHadamardConst_spec s hs]
  rfl

/-- **The pole theorem AT A ZERO.** Like `stripBoundary_pole_mul_logDeriv_xi₂`, with the evaluation
point a zero `ρ₀`: the self-term's residue is `1/ρ₀ + c` (`c` the kernel's regular value), and the
conclusion carries `xiFinitePart ρ₀ + m_{ρ₀}·c` in place of `logDeriv ξ s₀`. -/
theorem stripBoundary_pole_mul_logDeriv_xi_at_zero {F : ℂ → ℂ} {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros) {c : ℂ} {a b C : ℝ} (ha : a < 0) (hb : 1 < b) (hC : 0 ≤ C)
    (hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => F (σ + t * I)))
    (hdec : ∀ σ : ℝ, (σ = a ∨ σ = b) → LineDecay F σ C 2)
    (hF0 : F ρ₀ = 0)
    (hres : ∀ ρ ∈ ZD.NontrivialZeros, ρ ≠ ρ₀ →
      stripBoundary (fun s => F s * hadamardTerm ρ s) a b
        = 2 * Real.pi * I * (hadamardTerm ρ ρ₀ + F ρ))
    (hself : stripBoundary (fun s => F s * hadamardTerm ρ₀ s) a b
        = 2 * Real.pi * I * (1 / ρ₀ + c))
    (hpole : stripBoundary F a b = 2 * Real.pi * I) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) ∧
    stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (xiFinitePart ρ₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val
          + (ZD.xiOrderNat ρ₀ : ℂ) * c) := by
  have hA := xiHadamardConst_spec
  set A : ℂ := xiHadamardConst with hAdef
  set z₀ : Zero := ⟨ρ₀, hρ₀⟩ with hz₀
  have hintF : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => F (σ + t * I)) :=
    fun σ hσ => integrable_line_of_decay' (hFc σ hσ) (le_refl 2) hC (hdec σ hσ)
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
        (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hFc σ hσ) (hdec σ hσ) ρ)
        (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdec σ hσ))),
      integral_const_mul, lin_lineIntegral_hadamard_exchange hC ha hb hσ (hFc σ hσ) (hdec σ hσ)]
  set v : Zero → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val ρ₀ + F ρ.val)
      + (if ρ = z₀ then (ZD.xiOrderNat ρ₀ : ℂ) * c else 0) with hv
  have hper : ∀ ρ : Zero,
      I * (∫ t : ℝ, hadamardLineTerm F b ρ t) - I * (∫ t : ℝ, hadamardLineTerm F a ρ t)
        = 2 * Real.pi * I * v ρ := by
    intro ρ
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
    by_cases hρeq : ρ = z₀
    · have hval : ρ.val = ρ₀ := by rw [hρeq]
      have hv' : v ρ = (ZD.xiOrderNat ρ₀ : ℂ) * (1 / ρ₀ + c) := by
        simp only [hv, if_pos hρeq, hval, hF0, hadamardTerm, sub_self, div_zero, zero_add, add_zero]
        ring
      rw [hv']
      have h := hself
      unfold stripBoundary lineIntegral at h
      beta_reduce at h
      rw [hval] at hb' ha'
      linear_combination I * hb' - I * ha' + (ZD.xiOrderNat ρ₀ : ℂ) * h
    · have hne : ρ.val ≠ ρ₀ := fun h => hρeq (Subtype.ext h)
      have h := hres ρ.val ρ.property hne
      unfold stripBoundary lineIntegral at h
      beta_reduce at h
      have hv' : v ρ = (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val ρ₀ + F ρ.val) := by
        simp only [hv, if_neg hρeq, add_zero]
      rw [hv']
      linear_combination I * hb' - I * ha' + (ZD.xiOrderNat ρ.val : ℂ) * h
  have hsumb := lin_summable_hadamardLineTerm_integral hC ha hb
    (Or.inr rfl : b = a ∨ b = b) (hdec b (Or.inr rfl))
  have hsuma := lin_summable_hadamardLineTerm_integral hC ha hb
    (Or.inl rfl : a = a ∨ a = b) (hdec a (Or.inl rfl))
  have hsumH : Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val ρ₀) :=
    summable_hadamard_term_any ρ₀
  have hsumIf : Summable (fun ρ : Zero => if ρ = z₀ then (ZD.xiOrderNat ρ₀ : ℂ) * c else 0) :=
    (hasSum_ite_eq z₀ _).summable
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) I_ne_zero
  have hsumV : Summable v := by
    have hs : Summable (fun ρ : Zero => 2 * Real.pi * I * v ρ) :=
      ((hsumb.mul_left I).sub (hsuma.mul_left I)).congr hper
    refine (hs.mul_left (2 * Real.pi * I)⁻¹).congr (fun ρ => ?_)
    field_simp
  have hsumTot : Summable (fun ρ : Zero =>
      (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val ρ₀ + F ρ.val)) := by
    refine (hsumV.sub hsumIf).congr (fun ρ => ?_)
    simp only [hv, Pi.sub_apply]
    ring
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
  have hsplitV : ∑' ρ : Zero, v ρ
      = (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val ρ₀ + F ρ.val))
        + (ZD.xiOrderNat ρ₀ : ℂ) * c := by
    have hite : ∑' ρ : Zero, (if ρ = z₀ then (ZD.xiOrderNat ρ₀ : ℂ) * c else 0)
        = (ZD.xiOrderNat ρ₀ : ℂ) * c := by
      simpa using tsum_ite_eq z₀ (fun _ : Zero => (ZD.xiOrderNat ρ₀ : ℂ) * c)
    rw [← hite, ← hsumTot.tsum_add hsumIf]
  have hsplit : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * (hadamardTerm ρ.val ρ₀ + F ρ.val)
      = (∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val ρ₀)
        + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val := by
    rw [← hsumH.tsum_add hsumK]
    congr 1
    funext ρ
    ring
  rw [hsplitV, hsplit]
  unfold xiFinitePart
  ring

/-! ## 5. The Riesz kernel at a zero and the identity -/

theorem rieszKernel_self_zero (L : ℝ) : rieszKernel L 0 = 0 := by
  simp [rieszKernel]

/-- The zero side for the Riesz kernel with its pole AT a zero `ρ₀`. -/
theorem stripBoundary_rieszKernel_mul_logDeriv_xi_at_zero {L : ℝ} (hL : 0 < L) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - ρ₀)) ∧
    stripBoundary (fun s => rieszKernel L (s - ρ₀) * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (xiFinitePart ρ₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - ρ₀)
          + (ZD.xiOrderNat ρ₀ : ℂ) * deriv (expRatio L) 0) := by
  have hab : a ≤ b := by linarith
  have hρa : a < ρ₀.re := by linarith [hρ₀.1]
  have hρb : ρ₀.re < b := by linarith [hρ₀.2.1]
  obtain ⟨C, hC, hdecl⟩ := rieszKernel_line_decay hL hab hρa hρb
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  exact stripBoundary_pole_mul_logDeriv_xi_at_zero (F := fun s => rieszKernel L (s - ρ₀)) hρ₀
    ha hb hC hFc hdecl (by simp [rieszKernel_self_zero])
    (fun ρ hρ hne => stripBoundary_rieszKernel_hadamardTerm hL ha hb hρa hρb hρ hne)
    (stripBoundary_rieszKernel_hadamardTerm_self hL hρ₀ ha hb)
    (stripBoundary_rieszKernel hL hab hρa hρb)

/-- **The truncated explicit formula AT A ZERO (Riesz window).** For a nontrivial zero `ρ₀` and every
front `x = e^L`: the finite part of `ξ′/ξ` at `ρ₀`, plus the kernel sum over the other zeros, plus
`m_{ρ₀}·G′(0)` (the multiplicity times the kernel's regular value at its pole), equals the
Archimedean lines minus the Riesz-windowed prime sum at `ρ₀`. -/
theorem truncated_explicit_formula_riesz_at_zero {L : ℝ} (hL : 0 < L) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    xiFinitePart ρ₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - ρ₀)
        + (ZD.xiOrderNat ρ₀ : ℂ) * deriv (expRatio L) 0
      = (1 / (2 * π)) * ((∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC ρ₀ n := by
  have hab : a ≤ b := by linarith
  have hs₀a : a < ρ₀.re := by linarith [hρ₀.1]
  have hs₀b : ρ₀.re < b := by linarith [hρ₀.2.1]
  obtain ⟨C, hC, hdecl⟩ := rieszKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)) := by
    intro σ hσ
    apply rieszKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hFint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)) :=
    fun σ hσ => integrable_line_of_decay' (F := fun s => rieszKernel L (s - ρ₀)) (hFc σ hσ)
      (le_refl 2) hC (hdecl σ hσ)
  obtain ⟨-, hzero⟩ := stripBoundary_rieszKernel_mul_logDeriv_xi_at_zero hL hρ₀ ha hb
  have hlineInt : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)
        * logDeriv ZD.riemannXi (σ + t * I)) := by
    intro σ hσ
    obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
    have hpt : ∀ t : ℝ, rieszKernel L ((σ : ℂ) + t * I - ρ₀) * logDeriv ZD.riemannXi (σ + t * I)
        = A * rieszKernel L ((σ : ℂ) + t * I - ρ₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => rieszKernel L (s - ρ₀)) σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((σ : ℂ) + t * I - ρ₀)
          * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * rieszKernel L ((σ : ℂ) + t * I - ρ₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => rieszKernel L (s - ρ₀)) σ ρ t := funext hpt
    rw [hfun]
    exact ((hFint σ hσ).const_mul A).add (integrable_tsum_of_summable_integral_norm
      (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hFc σ hσ) (hdecl σ hσ) ρ)
      (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdecl σ hσ)))
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hLb : lineIntegral (fun s => rieszKernel L (s - ρ₀) * logDeriv ZD.riemannXi s) b
      = (∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch ((b : ℂ) + t * I))
        - 2 * π * ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC ρ₀ n := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, rieszKernel L ((b : ℂ) + t * I - ρ₀) * logDeriv ZD.riemannXi (b + t * I)
        = rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch (b + t * I)
          - rieszKernel L ((b : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (b + t * I) := by
      intro t
      rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        rieszKernel L ((b : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hFint b (Or.inr rfl)) hθb hreb hb
    have hAint : Integrable (fun t : ℝ =>
        rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch (b + t * I)) := by
      have h := (hlineInt b (Or.inr rfl)).add hLint
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.add_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((b : ℂ) + t * I - ρ₀)
          * logDeriv ZD.riemannXi (b + t * I))
        = fun t : ℝ => rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch (b + t * I)
            - rieszKernel L ((b : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (b + t * I) :=
      funext hpt
    rw [hfun, integral_sub hAint hLint,
      lseries_line_exchange (hFint b (Or.inr rfl)) hθb hreb hb,
      tsum_congr (rieszKernel_prime_line_right hL hs₀b hC (hdecl b (Or.inr rfl))), tsum_mul_left]
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hLa : lineIntegral (fun s => rieszKernel L (s - ρ₀) * logDeriv ZD.riemannXi s) a
      = -(∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, rieszKernel L ((a : ℂ) + t * I - ρ₀) * logDeriv ZD.riemannXi (a + t * I)
        = -(rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I)))
          + rieszKernel L ((a : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := by
      intro t
      rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        rieszKernel L ((a : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hFint a (Or.inl rfl)) hθa hrea h1a
    have hAint : Integrable (fun t : ℝ =>
        rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
      have h := hLint.sub (hlineInt a (Or.inl rfl))
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => rieszKernel L ((a : ℂ) + t * I - ρ₀)
          * logDeriv ZD.riemannXi (a + t * I))
        = fun t : ℝ => -(rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I)))
            + rieszKernel L ((a : ℂ) + t * I - ρ₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) :=
      funext hpt
    have hAint' : Integrable (fun t : ℝ =>
        -(rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I)))) := hAint.neg
    rw [hfun, integral_add hAint' hLint, integral_neg,
      lseries_line_exchange (hFint a (Or.inl rfl)) hθa hrea h1a,
      tsum_congr (rieszKernel_prime_line_left hL hs₀a hC (hdecl a (Or.inl rfl))), tsum_zero,
      add_zero]
  unfold stripBoundary at hzero
  rw [hLb, hLa] at hzero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - ρ₀) with hS
  set X := xiFinitePart ρ₀ + S + (ZD.xiOrderNat ρ₀ : ℂ) * deriv (expRatio L) 0 with hX
  set Ab := ∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch ((b : ℂ) + t * I) with hAb
  set Aa := ∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I))
    with hAa
  set P := ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC ρ₀ n with hP
  have h2πS : 2 * (π : ℂ) * X = (Ab + Aa) - 2 * π * P := by
    linear_combination I * hzero + (2 * π * X - Ab - Aa + 2 * π * P) * Complex.I_sq
  have hS' : X = (Ab + Aa) / (2 * π) - P := by
    rw [eq_sub_iff_add_eq, eq_div_iff h2π]
    linear_combination h2πS
  rw [hS']
  ring

/-! ## 6. `G′(0) = L/2` and the multiplicity readout -/

/-- `expRatio L` has derivative `L/2` at `0`: `(e^{Lw} − 1)/(Lw) = 1 + Lw/2 + O(w²)`. -/
theorem hasDerivAt_expRatio_zero {L : ℝ} (hL : 0 < L) :
    HasDerivAt (expRatio L) ((L : ℂ) / 2) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have key : ∀ w : ℂ, w ≠ 0 → ‖(L : ℂ) * w‖ ≤ 1 →
      ‖slope (expRatio L) 0 w - (L : ℂ) / 2‖ ≤ (2 / 9) * L ^ 2 * ‖w‖ := by
    intro w hw hLw
    rw [slope_def_field, expRatio_of_ne L hw, expRatio_zero hL.ne', sub_zero]
    have hid : ((Complex.exp (L * w) - 1) / (L * w) - 1) / w - (L : ℂ) / 2
        = (Complex.exp (L * w) - ∑ m ∈ Finset.range 3, (L * w) ^ m / (m.factorial : ℂ))
            / ((L : ℂ) * w ^ 2) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      field_simp
      ring
    rw [hid, norm_div]
    have hb := Complex.exp_bound hLw (by norm_num : 0 < 3)
    have hden : ‖(L : ℂ) * w ^ 2‖ = L * ‖w‖ ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    have hnum : ‖(L : ℂ) * w‖ ^ 3 = L ^ 3 * ‖w‖ ^ 3 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, mul_pow]
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [hden, div_le_iff₀ (by positivity)]
    calc ‖Complex.exp (L * w) - ∑ m ∈ Finset.range 3, (L * w) ^ m / (m.factorial : ℂ)‖
        ≤ ‖(L : ℂ) * w‖ ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) := hb
      _ = (2 / 9) * L ^ 2 * ‖w‖ * (L * ‖w‖ ^ 2) := by
          rw [hnum]
          simp only [Nat.factorial, Nat.succ_eq_add_one]
          push_cast
          ring
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖slope (expRatio L) 0 w - (L : ℂ) / 2‖ ≤ (2 / 9) * L ^ 2 * ‖w‖ := by
    have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖(L : ℂ) * w‖ ≤ 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      have hcont : Continuous (fun w : ℂ => ‖(L : ℂ) * w‖) := by fun_prop
      have : ∀ᶠ w in 𝓝 (0 : ℂ), ‖(L : ℂ) * w‖ < 1 := by
        apply (hcont.tendsto 0).eventually (gt_mem_nhds _)
        simp
      exact this.mono (fun w hw => hw.le)
    filter_upwards [h1, h2] with w hw hLw
    exact key w hw hLw
  have hlim : Tendsto (fun w : ℂ => (2 / 9) * L ^ 2 * ‖w‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun w : ℂ => (2 / 9) * L ^ 2 * ‖w‖) (𝓝 (0 : ℂ)) (𝓝 ((2 / 9) * L ^ 2 * ‖(0 : ℂ)‖)) :=
      (continuous_norm.tendsto 0).const_mul _
    simp only [norm_zero, mul_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hev hlim

theorem deriv_expRatio_zero {L : ℝ} (hL : 0 < L) : deriv (expRatio L) 0 = (L : ℂ) / 2 :=
  (hasDerivAt_expRatio_zero hL).deriv

/-- **THE MULTIPLICITY READOUT.** At a nontrivial zero `ρ₀` and front `x = e^L`:
`m_{ρ₀} · L/2 = (1/2π)(Archimedean lines) − Σ_n W(log n) Λ(n) n^{−ρ₀} − xiFinitePart ρ₀ − Σ'_{ρ} m_ρ K_R(ρ−ρ₀)`.
The multiplicity of the zero is read by the Riesz front from the prime side, the finite part of
`ξ′/ξ`, and the other zeros' Fejér-kernel contributions. -/
theorem multiplicity_readout {L : ℝ} (hL : 0 < L) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    (ZD.xiOrderNat ρ₀ : ℂ) * ((L : ℂ) / 2)
      = (1 / (2 * π)) * ((∫ t : ℝ, rieszKernel L ((b : ℂ) + t * I - ρ₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, rieszKernel L ((a : ℂ) + t * I - ρ₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (rieszProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC ρ₀ n
        - xiFinitePart ρ₀
        - ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * rieszKernel L (ρ.val - ρ₀) := by
  have h := truncated_explicit_formula_riesz_at_zero hL hρ₀ ha hb
  rw [deriv_expRatio_zero hL] at h
  linear_combination h

#print axioms stripBoundary_div_sq_eq
#print axioms stripBoundary_rieszKernel_hadamardTerm_self
#print axioms stripBoundary_pole_mul_logDeriv_xi_at_zero
#print axioms truncated_explicit_formula_riesz_at_zero
#print axioms deriv_expRatio_zero
#print axioms multiplicity_readout

end CriticalLinePhasor.ContourArgument
