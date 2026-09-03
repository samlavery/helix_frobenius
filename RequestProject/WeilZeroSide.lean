import Mathlib
import RequestProject.WeilStripContour
import RequestProject.XiPartialFraction
import RequestProject.XiOrderSummable
import RequestProject.StExplicitBridge

/-!
# Track W3/W4 — the zero side of the explicit formula (ledger 534)

For an entire test function `F` with power decay of order `≥ 4` on the strip `a ≤ Re s ≤ b`
(`a < 0`, `1 < b`), the strip boundary integral of `F · ξ′/ξ` is `2πi Σ_ρ m_ρ F(ρ)`.

Route: the compiled Hadamard partial fraction `ξ′/ξ = A + Σ_ρ m_ρ (1/(s−ρ) + 1/ρ)`
(`ZD.xi_logDeriv_partial_fraction`) is integrated TERMWISE against `F` around the strip. Each
term gives `m_ρ · 2πi F(ρ)` (strip residue, `stripBoundary_div_sub_eq`) plus `m_ρ/ρ` times the
strip Cauchy integral of `F`, which is zero; the constant `A` integrates to zero the same way. The
exchange of `Σ_ρ` and the line integrals is dominated by
`‖F(s)‖·‖s‖/(‖s−ρ‖‖ρ‖) ≤ K/‖ρ‖² · (1+t²)⁻¹`, summable by the compiled
`ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`. No bound on `ξ′/ξ` at large height is used.

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## A whole-line `L¹` lemma: a tsum with summable norm integrals is integrable -/

theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF_int : ∀ i, Integrable (F i)) (hF_sum : Summable fun i => ∫ t : ℝ, ‖F i t‖) :
    Integrable (fun t : ℝ => ∑' i, F i t) := by
  let fL1 : ι → Lp ℂ 1 (volume : Measure ℝ) := fun i => (hF_int i).toL1 (F i)
  have hnormL1 : Summable fun i => ‖fL1 i‖ := by
    have heq : (fun i => ‖fL1 i‖) = fun i => ∫ t : ℝ, ‖F i t‖ := by
      funext i
      exact L1.norm_of_fun_eq_integral_norm (hF_int i)
    rw [heq]
    exact hF_sum
  have henorm : ∑' i, ‖fL1 i‖ₑ ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hnormL1
  have hcoeEach : ∀ᵐ x, ∀ i, fL1 i x = F i x := by
    rw [ae_all_iff]
    intro i
    exact (hF_int i).coeFn_toL1
  have hcoeSum : (fun x => (∑' i, fL1 i) x) =ᵐ[volume] fun x => ∑' i, F i x := by
    filter_upwards [Lp.coeFn_tsum henorm, hcoeEach] with x hxsum hxeach
    rw [hxsum]
    exact tsum_congr (fun i => hxeach i)
  exact (L1.integrable_coeFn (∑' i, fL1 i)).congr hcoeSum

/-! ## The Hadamard term and its size on the lines -/

/-- The resolvent term of the Hadamard partial fraction at the zero `ρ`. -/
def hadamardTerm (ρ s : ℂ) : ℂ := 1 / (s - ρ) + 1 / ρ

theorem hadamardTerm_eq {ρ s : ℂ} (hs : s ≠ ρ) (hρ : ρ ≠ 0) :
    hadamardTerm ρ s = s / ((s - ρ) * ρ) := by
  unfold hadamardTerm
  have h1 : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

theorem norm_hadamardTerm {ρ s : ℂ} (hs : s ≠ ρ) (hρ : ρ ≠ 0) :
    ‖hadamardTerm ρ s‖ = ‖s‖ / (‖s - ρ‖ * ‖ρ‖) := by
  rw [hadamardTerm_eq hs hρ, norm_div, norm_mul]

/-- The majorant constant: `4 C M / η`, `M = max |a| |b|`, `η = min (min (−a) (b−1)) 1`. -/
def weilK (a b C : ℝ) : ℝ := 4 * C * max |a| |b| / min (min (-a) (b - 1)) 1

theorem weilK_nonneg {a b C : ℝ} (ha : a < 0) (hb : 1 < b) (hC : 0 ≤ C) : 0 ≤ weilK a b C := by
  unfold weilK
  have hη : 0 < min (min (-a) (b - 1)) 1 := lt_min (lt_min (by linarith) (by linarith)) one_pos
  have hM : 0 ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  positivity

theorem line_not_zero {a b σ : ℝ} (ha : a < 0) (hb : 1 < b) (hσ : σ = a ∨ σ = b) (t : ℝ) :
    ((σ : ℂ) + t * I) ∉ ZD.NontrivialZeros := by
  intro h
  obtain ⟨h1, h2, -⟩ := h
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero, sub_zero, mul_one,
    add_zero] at h1 h2
  rcases hσ with rfl | rfl <;> linarith

theorem line_ne_zero_point {a b σ : ℝ} (ha : a < 0) (hb : 1 < b) (hσ : σ = a ∨ σ = b) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : ((σ : ℂ) + t * I) ≠ ρ := by
  intro h
  exact line_not_zero ha hb hσ t (h ▸ hρ)

theorem zero_ne_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : ρ ≠ 0 := by
  obtain ⟨h1, -, -⟩ := hρ
  intro h
  rw [h, zero_re] at h1
  exact lt_irrefl _ h1

/-- **The pointwise majorant on a line**: for decay of order `≥ 4`,
`‖F(s) · (1/(s−ρ) + 1/ρ)‖ ≤ K/‖ρ‖² · (1+t²)⁻¹`, `s = σ + it`, `σ ∈ {a, b}`. -/
theorem weil_pointwise_bound {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (t : ℝ) :
    ‖F (σ + t * I) * hadamardTerm ρ (σ + t * I)‖
      ≤ weilK a b C / ‖ρ‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
  have hsρ : ((σ : ℂ) + t * I) ≠ ρ := line_ne_zero_point ha hb hσ t hρ
  have hρne : ρ ≠ 0 := zero_ne_zero hρ
  obtain ⟨hρ0, hρ1, -⟩ := hρ
  set η : ℝ := min (min (-a) (b - 1)) 1 with hη
  set M : ℝ := max |a| |b| with hM
  have hη0 : 0 < η := lt_min (lt_min (by linarith) (by linarith)) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ |b| := by rw [abs_of_pos (by linarith)]; linarith
    exact le_trans this (le_max_right _ _)
  have hσM : |σ| ≤ M := by
    rcases hσ with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hσab : σ ∈ Icc a b := by
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, by linarith⟩
    · exact ⟨by linarith, le_refl _⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  set γ : ℝ := ρ.im with hγ
  set u : ℝ := 1 + |t| with hu
  set v : ℝ := 1 + |t - γ| with hv
  set g : ℝ := 1 + |γ| with hg
  have hu1 : 1 ≤ u := by rw [hu]; linarith [abs_nonneg t]
  have hv1 : 1 ≤ v := by rw [hv]; linarith [abs_nonneg (t - γ)]
  have hg1 : 1 ≤ g := by rw [hg]; linarith [abs_nonneg γ]
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hR0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hD0 : 0 < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
  -- (i) decay of order 4
  have hF : ‖F s‖ ≤ C / u ^ 4 := by
    have h1 := hdec σ hσab t
    have h2 : u ^ 4 ≤ u ^ k := pow_le_pow_right₀ hu1 hk
    calc ‖F s‖ ≤ C / u ^ k := h1
      _ ≤ C / u ^ 4 := div_le_div_of_nonneg_left hC (by positivity) h2
  -- (ii) size of `s`
  have hS : ‖s‖ ≤ M * u := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |σ| + |t| := by simp [hs]
      _ ≤ M + M * |t| := by nlinarith [abs_nonneg t]
      _ = M * u := by rw [hu]; ring
  -- (iii) distance to the zero
  have hre_gap : η ≤ |σ - ρ.re| := by
    rcases hσ with h | h
    · rw [h]
      calc η ≤ min (-a) (b - 1) := min_le_left _ _
        _ ≤ -a := min_le_left _ _
        _ ≤ |a - ρ.re| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [h]
      calc η ≤ min (-a) (b - 1) := min_le_left _ _
        _ ≤ b - 1 := min_le_right _ _
        _ ≤ |b - ρ.re| := by rw [abs_of_pos (by linarith)]; linarith
  have hD : η / 2 * v ≤ ‖s - ρ‖ := by
    have h1 : |σ - ρ.re| ≤ ‖s - ρ‖ := by
      have := Complex.abs_re_le_norm (s - ρ)
      simpa [hs] using this
    have h2 : |t - γ| ≤ ‖s - ρ‖ := by
      have := Complex.abs_im_le_norm (s - ρ)
      simpa [hs, hγ] using this
    have h3 : η * |t - γ| ≤ |t - γ| := by nlinarith [abs_nonneg (t - γ)]
    rw [hv]
    nlinarith
  -- (iv) size of the zero
  have hR : ‖ρ‖ ≤ g := by
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ g := by rw [hg, abs_of_pos hρ0]; linarith
  -- (v) the product inequality `1/(uv) ≤ 2/g`
  have huv : u⁻¹ * v⁻¹ ≤ 2 / g := by
    have htri : |γ| ≤ |t| + |t - γ| := by
      have := abs_sub t (t - γ)
      rwa [sub_sub_cancel] at this
    rw [← mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hg0]
    rw [hu, hv, hg]
    nlinarith [abs_nonneg t, abs_nonneg (t - γ), abs_nonneg γ]
  have hu2 : u⁻¹ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
    rw [inv_pow]
    apply inv_anti₀ (by positivity)
    rw [hu]
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith [abs_nonneg t]
  -- assemble
  rw [norm_mul, norm_hadamardTerm hsρ hρne]
  have hstep1 : ‖F s‖ * (‖s‖ / (‖s - ρ‖ * ‖ρ‖))
      ≤ (C / u ^ 4) * ((M * u) / ((η / 2 * v) * ‖ρ‖)) := by
    have hden : (η / 2 * v) * ‖ρ‖ ≤ ‖s - ρ‖ * ‖ρ‖ := by
      exact mul_le_mul_of_nonneg_right hD hR0.le
    have hden0 : 0 < (η / 2 * v) * ‖ρ‖ := by positivity
    have hfrac : ‖s‖ / (‖s - ρ‖ * ‖ρ‖) ≤ (M * u) / ((η / 2 * v) * ‖ρ‖) := by
      apply div_le_div₀ (by positivity) hS hden0 hden
    exact mul_le_mul hF hfrac (by positivity) (by positivity)
  have hstep2 : (C / u ^ 4) * ((M * u) / ((η / 2 * v) * ‖ρ‖))
      = (2 * C * M / η) * (u⁻¹ ^ 2 * (u⁻¹ * v⁻¹) * ‖ρ‖⁻¹) := by
    field_simp
  have hstep3 : u⁻¹ ^ 2 * (u⁻¹ * v⁻¹) * ‖ρ‖⁻¹ ≤ (1 + t ^ 2)⁻¹ * (2 / ‖ρ‖) * ‖ρ‖⁻¹ := by
    have h2 : 2 / g ≤ 2 / ‖ρ‖ := div_le_div_of_nonneg_left (by norm_num) hR0 hR
    have huv' : u⁻¹ * v⁻¹ ≤ 2 / ‖ρ‖ := huv.trans h2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hu2 huv' (by positivity) (by positivity)
  have hstep4 : (2 * C * M / η) * ((1 + t ^ 2)⁻¹ * (2 / ‖ρ‖) * ‖ρ‖⁻¹)
      = weilK a b C / ‖ρ‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
    unfold weilK
    rw [← hη, ← hM]
    field_simp
    ring
  calc ‖F s‖ * (‖s‖ / (‖s - ρ‖ * ‖ρ‖))
      ≤ (C / u ^ 4) * ((M * u) / ((η / 2 * v) * ‖ρ‖)) := hstep1
    _ = (2 * C * M / η) * (u⁻¹ ^ 2 * (u⁻¹ * v⁻¹) * ‖ρ‖⁻¹) := hstep2
    _ ≤ (2 * C * M / η) * ((1 + t ^ 2)⁻¹ * (2 / ‖ρ‖) * ‖ρ‖⁻¹) := by
        apply mul_le_mul_of_nonneg_left hstep3
        have : 0 ≤ 2 * C * M := by positivity
        positivity
    _ = weilK a b C / ‖ρ‖ ^ 2 * (1 + t ^ 2)⁻¹ := hstep4

/-! ## The weighted line terms, their integrability and summability -/

/-- The zero subtype. -/
abbrev Zero := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-- The `ρ`-term of `F · (partial fraction)` on the line `Re s = σ`. -/
def hadamardLineTerm (F : ℂ → ℂ) (σ : ℝ) (ρ : Zero) (t : ℝ) : ℂ :=
  F (σ + t * I) * ((ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val (σ + t * I))

theorem hadamardLineTerm_norm_le {F : ℂ → ℂ} {a b C : ℝ} {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) (ρ : Zero) (t : ℝ) :
    ‖hadamardLineTerm F σ ρ t‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2)) * (1 + t ^ 2)⁻¹ := by
  unfold hadamardLineTerm
  have h := weil_pointwise_bound hk hC ha hb hdec hσ ρ.property t
  have hm : ‖((ZD.xiOrderNat ρ.val : ℕ) : ℂ)‖ = (ZD.xiOrderNat ρ.val : ℝ) := by
    rw [Complex.norm_natCast]
  calc ‖F (σ + t * I) * ((ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val (σ + t * I))‖
      = (ZD.xiOrderNat ρ.val : ℝ) * ‖F (σ + t * I) * hadamardTerm ρ.val (σ + t * I)‖ := by
        rw [norm_mul, norm_mul, hm, norm_mul]
        ring
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2)) * (1 + t ^ 2)⁻¹ := by ring

theorem hadamardLineTerm_continuous {F : ℂ → ℂ} (hF : Continuous F) {a b : ℝ} (ha : a < 0)
    (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (ρ : Zero) :
    Continuous (hadamardLineTerm F σ ρ) := by
  unfold hadamardLineTerm hadamardTerm
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  refine (hF.comp hline).mul (continuous_const.mul (Continuous.add ?_ continuous_const))
  refine Continuous.div continuous_const (hline.sub continuous_const) ?_
  intro t
  exact sub_ne_zero.mpr (line_ne_zero_point ha hb hσ t ρ.property)

theorem hadamardLineTerm_integrable {F : ℂ → ℂ} (hF : Continuous F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) (ρ : Zero) : Integrable (hadamardLineTerm F σ ρ) := by
  have hg : Integrable (fun t : ℝ =>
      ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg (hadamardLineTerm_continuous hF ha hb hσ ρ).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (hadamardLineTerm_norm_le hk hC ha hb hdec hσ ρ)

theorem hadamardLineTerm_integral_norm_le {F : ℂ → ℂ} (_hF : Continuous F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) (ρ : Zero) :
    ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2))
          * ∫ t : ℝ, (1 + t ^ 2)⁻¹ := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (integrable_inv_one_add_sq.const_mul _)
  exact Filter.Eventually.of_forall (hadamardLineTerm_norm_le hk hC ha hb hdec hσ ρ)

theorem summable_hadamardLineTerm_integral_norm {F : ℂ → ℂ} (hF : Continuous F) {a b C : ℝ}
    {k : ℕ} (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) :
    Summable (fun ρ : Zero => ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖) := by
  have hmaj : Summable (fun ρ : Zero =>
      ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖ ^ 2)) * ∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
    have h := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros
    have h2 := (h.mul_left (weilK a b C)).mul_right (∫ t : ℝ, (1 + t ^ 2)⁻¹)
    refine h2.congr (fun ρ => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg (fun t => norm_nonneg _)) ?_ hmaj
  intro ρ
  exact hadamardLineTerm_integral_norm_le hF hk hC ha hb hdec hσ ρ

/-- **The exchange on a line**: `∫ Σ_ρ = Σ_ρ ∫` for the weighted Hadamard terms. -/
theorem lineIntegral_hadamard_exchange {F : ℂ → ℂ} (hF : Continuous F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) :
    ∫ t : ℝ, ∑' ρ : Zero, hadamardLineTerm F σ ρ t
      = ∑' ρ : Zero, ∫ t : ℝ, hadamardLineTerm F σ ρ t :=
  (integral_tsum_of_summable_integral_norm
    (fun ρ => hadamardLineTerm_integrable hF hk hC ha hb hdec hσ ρ)
    (summable_hadamardLineTerm_integral_norm hF hk hC ha hb hdec hσ)).symm

theorem summable_hadamardLineTerm_integral {F : ℂ → ℂ} (hF : Continuous F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) :
    Summable (fun ρ : Zero => ∫ t : ℝ, hadamardLineTerm F σ ρ t) := by
  refine Summable.of_norm_bounded (summable_hadamardLineTerm_integral_norm hF hk hC ha hb hdec hσ)
    (fun ρ => ?_)
  exact norm_integral_le_integral_norm _

/-! ## The zero side -/

/-- The per-zero strip identity: `∮_strip F·(1/(s−ρ)+1/ρ) = 2πi F(ρ)`. -/
theorem stripBoundary_hadamardTerm {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    stripBoundary (fun s => F s * hadamardTerm ρ s) a b = 2 * Real.pi * I * F ρ := by
  have hab : a ≤ b := by linarith
  have hk2 : 2 ≤ k := by omega
  have hρa : a < ρ.re := by linarith [hρ.1]
  have hρb : ρ.re < b := by linarith [hρ.2.1]
  have hσab : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ∈ Icc a b := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hintF : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => F (σ + t * I)) :=
    fun σ hσ => integrable_line_of_decay hF.continuous hk2 hC (fun t => hdec σ (hσab σ hσ) t)
  have hintH : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => F (σ + t * I) * hadamardTerm ρ (σ + t * I)) := by
    intro σ hσ
    have hg : Integrable (fun t : ℝ => weilK a b C / ‖ρ‖ ^ 2 * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    refine Integrable.mono' hg ?_
      (Filter.Eventually.of_forall (weil_pointwise_bound hk hC ha hb hdec hσ hρ))
    have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
    unfold hadamardTerm
    refine ((hF.continuous.comp hline).mul
      (Continuous.add ?_ continuous_const)).aestronglyMeasurable
    refine Continuous.div continuous_const (hline.sub continuous_const) ?_
    intro t
    exact sub_ne_zero.mpr (line_ne_zero_point ha hb hσ t hρ)
  have hintK : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - ρ)⁻¹) := by
    intro σ hσ
    have h2 : Integrable (fun t : ℝ => F (σ + t * I) * (1 / ρ)) := (hintF σ hσ).mul_const _
    refine ((hintH σ hσ).sub h2).congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hadamardTerm, Pi.sub_apply]
    ring
  have hsplit : stripBoundary (fun s => F s * hadamardTerm ρ s) a b
      = stripBoundary (fun s => F s * (s - ρ)⁻¹) a b + (1 / ρ) * stripBoundary F a b := by
    unfold stripBoundary lineIntegral
    have hb' : ∫ t : ℝ, F (b + t * I) * hadamardTerm ρ (b + t * I)
        = (∫ t : ℝ, F (b + t * I) * ((b : ℂ) + t * I - ρ)⁻¹)
          + (1 / ρ) * ∫ t : ℝ, F (b + t * I) := by
      rw [← integral_const_mul, ← integral_add (hintK b (Or.inr rfl))
        ((hintF b (Or.inr rfl)).const_mul _)]
      congr 1
      funext t
      simp only [hadamardTerm]
      ring
    have ha' : ∫ t : ℝ, F (a + t * I) * hadamardTerm ρ (a + t * I)
        = (∫ t : ℝ, F (a + t * I) * ((a : ℂ) + t * I - ρ)⁻¹)
          + (1 / ρ) * ∫ t : ℝ, F (a + t * I) := by
      rw [← integral_const_mul, ← integral_add (hintK a (Or.inl rfl))
        ((hintF a (Or.inl rfl)).const_mul _)]
      congr 1
      funext t
      simp only [hadamardTerm]
      ring
    rw [hb', ha']
    ring
  rw [hsplit, stripBoundary_div_sub_eq hF hk2 hC hab hdec hρa hρb,
    stripBoundary_eq_zero hF hk2 hC hab hdec]
  ring

/-- The line integrand `F · ξ′/ξ` is integrable on the two lines (used by the assembly to split
the Archimedean and prime parts). -/
theorem line_mul_logDeriv_xi_integrable {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) :
    Integrable (fun t : ℝ => F (σ + t * I) * logDeriv ZD.riemannXi (σ + t * I)) := by
  have hab : a ≤ b := by linarith
  have hk2 : 2 ≤ k := by omega
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  have hσab : σ ∈ Icc a b := by
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hintF : Integrable (fun t : ℝ => F (σ + t * I)) :=
    integrable_line_of_decay hF.continuous hk2 hC (fun t => hdec σ hσab t)
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
    (fun ρ => hadamardLineTerm_integrable hF.continuous hk hC ha hb hdec hσ ρ)
    (summable_hadamardLineTerm_integral_norm hF.continuous hk hC ha hb hdec hσ))

/-- **The zero side of the explicit formula.** For an entire `F` with power decay of order
`≥ 4` on the strip `a ≤ Re s ≤ b` (`a < 0 < 1 < b`),
`∮_strip F(s)·ξ′/ξ(s) ds = 2πi Σ_ρ m_ρ F(ρ)` (sum over the nontrivial zeros with multiplicity). -/
theorem stripBoundary_mul_logDeriv_xi {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ} {k : ℕ}
    (hk : 4 ≤ k) (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ k) :
    stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val := by
  have hab : a ≤ b := by linarith
  have hk2 : 2 ≤ k := by omega
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  have hσab : ∀ σ : ℝ, (σ = a ∨ σ = b) → σ ∈ Icc a b := by
    intro σ hσ
    rcases hσ with rfl | rfl
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
  have hintF : ∀ σ : ℝ, (σ = a ∨ σ = b) → Integrable (fun t : ℝ => F (σ + t * I)) :=
    fun σ hσ => integrable_line_of_decay hF.continuous hk2 hC (fun t => hdec σ (hσab σ hσ) t)
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
        (fun ρ => hadamardLineTerm_integrable hF.continuous hk hC ha hb hdec hσ ρ)
        (summable_hadamardLineTerm_integral_norm hF.continuous hk hC ha hb hdec hσ)),
      integral_const_mul, lineIntegral_hadamard_exchange hF.continuous hk hC ha hb hdec hσ]
  -- per zero: the two line integrals combine to the strip residue
  have hper : ∀ ρ : Zero,
      I * (∫ t : ℝ, hadamardLineTerm F b ρ t) - I * (∫ t : ℝ, hadamardLineTerm F a ρ t)
        = 2 * Real.pi * I * ((ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) := by
    intro ρ
    have h := stripBoundary_hadamardTerm hF hk hC ha hb hdec ρ.property
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
  -- assemble
  have hsumb := summable_hadamardLineTerm_integral hF.continuous hk hC ha hb hdec
    (Or.inr rfl : b = a ∨ b = b)
  have hsuma := summable_hadamardLineTerm_integral hF.continuous hk hC ha hb hdec
    (Or.inl rfl : a = a ∨ a = b)
  have hzero : stripBoundary F a b = 0 := stripBoundary_eq_zero hF hk2 hC hab hdec
  have hcomb : stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = A * stripBoundary F a b
        + ∑' ρ : Zero, (I * (∫ t : ℝ, hadamardLineTerm F b ρ t)
            - I * (∫ t : ℝ, hadamardLineTerm F a ρ t)) := by
    unfold stripBoundary
    rw [hline b (Or.inr rfl), hline a (Or.inl rfl),
      (hsumb.mul_left I).tsum_sub (hsuma.mul_left I), tsum_mul_left, tsum_mul_left]
    ring
  rw [hcomb, hzero, mul_zero, zero_add, tsum_congr hper, tsum_mul_left]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_hadamardTerm
#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_mul_logDeriv_xi

