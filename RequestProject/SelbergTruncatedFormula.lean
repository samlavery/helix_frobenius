import Mathlib
import RequestProject.TruncatedExplicitFormula

/-!
# The truncated explicit formula, Selberg's linear taper (ledger 564)

The same identity as `truncated_explicit_formula_cubic` for Selberg's weight `Λ_x`
(Titchmarsh 14.20): weight exactly `1` for `n ≤ x = e^L`, `log(x²/n)/log x` for `x ≤ n ≤ x²`,
`0` beyond — the object measured in att554d/560. Kernel `K(w) = (x^{2w} − x^w)/(w² L)`.

The kernel decays only at order 2 on the lines, so the exchange `Σ_ρ ↔ ∫` needs two inputs the
cubic instance did not: (i) the log-weighted zero sum `Σ_ρ m_ρ (1 + log(1+|ρ|))/|ρ|² < ∞`, from the
compiled multiplicity-weighted count `Σ_{|ρ|≤R} m_ρ ≤ C R log R` by dyadic shells; (ii) the
elementary bound `∫ dt/((1+|t|)(1+|t−γ|)) ≤ 12(1 + log(1+|γ|))/(1+|γ|)`. The entire factor
`G = K·w` decays only at order 1, so the strip residue lemma is re-proved at that order.

No `sorry`, no `axiom`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real FourierTransform

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. The log-weighted zero sum -/

/-- The dyadic shell index of a zero: `2^k ≤ ‖ρ‖ < 2^{k+1}` when `‖ρ‖ ≥ 1`. -/
def shellIdx (ρ : Zero) : ℕ := Nat.log 2 ⌊‖ρ.val‖⌋₊

theorem shellIdx_bounds {ρ : Zero} (h : 1 ≤ ‖ρ.val‖) :
    (2 : ℝ) ^ shellIdx ρ ≤ ‖ρ.val‖ ∧ ‖ρ.val‖ < 2 ^ (shellIdx ρ + 1) := by
  have hn1 : 1 ≤ ⌊‖ρ.val‖⌋₊ := Nat.le_floor (by exact_mod_cast h)
  have h1 : 2 ^ Nat.log 2 ⌊‖ρ.val‖⌋₊ ≤ ⌊‖ρ.val‖⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h2 : ⌊‖ρ.val‖⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊‖ρ.val‖⌋₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hfl : (⌊‖ρ.val‖⌋₊ : ℝ) ≤ ‖ρ.val‖ := Nat.floor_le (norm_nonneg _)
  have hfl2 : ‖ρ.val‖ < ⌊‖ρ.val‖⌋₊ + 1 := Nat.lt_floor_add_one _
  unfold shellIdx
  constructor
  · calc (2 : ℝ) ^ Nat.log 2 ⌊‖ρ.val‖⌋₊ = ((2 ^ Nat.log 2 ⌊‖ρ.val‖⌋₊ : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊‖ρ.val‖⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ _ := hfl
  · calc ‖ρ.val‖ < ⌊‖ρ.val‖⌋₊ + 1 := hfl2
      _ ≤ ((2 ^ (Nat.log 2 ⌊‖ρ.val‖⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = _ := by push_cast; rfl

/-- On the shell `k`, the log weight is at most `(k+3)/4^k`. -/
theorem logWeight_le_shell {ρ : Zero} (h : 1 ≤ ‖ρ.val‖) :
    (1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ ^ 2 ≤ (shellIdx ρ + 3) / 4 ^ shellIdx ρ := by
  obtain ⟨h1, h2⟩ := shellIdx_bounds h
  set k := shellIdx ρ with hk
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hnum : 1 + Real.log (1 + ‖ρ.val‖) ≤ k + 3 := by
    have hl1 : Real.log (1 + ‖ρ.val‖) ≤ Real.log ((2 : ℝ) ^ (k + 2)) := by
      apply Real.log_le_log (by positivity)
      have e : (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      rw [e]
      linarith
    have hl2 : Real.log ((2 : ℝ) ^ (k + 2)) = (k + 2) * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have hl3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hden : (4 : ℝ) ^ k ≤ ‖ρ.val‖ ^ 2 := by
    have e : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ hpos.le h1 2
  have hpos4 : (0 : ℝ) < 4 ^ k := by positivity
  calc (1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ ^ 2 ≤ (k + 3) / ‖ρ.val‖ ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (k + 3) / 4 ^ k := div_le_div_of_nonneg_left (by positivity) hpos4 hden

/-- **Log-weighted summability over the zeros**: `Σ_ρ m_ρ (1 + log(1+|ρ|))/|ρ|² < ∞`, from the
compiled multiplicity-weighted count by dyadic shells. -/
theorem summable_logWeight_nontrivialZeros :
    Summable (fun ρ : Zero =>
      (ZD.xiOrderNat ρ.val : ℝ) * ((1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ ^ 2)) := by
  obtain ⟨C, hC, R₀, _hR₀, hcount⟩ := ZD.xi_weighted_zero_count_disk_bound
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℕ, max R₀ 1 ≤ (2 : ℝ) ^ K := by
    rcases pow_unbounded_of_one_lt (max R₀ 1) (by norm_num : (1 : ℝ) < 2) with ⟨K, hK⟩
    exact ⟨K, hK.le⟩
  have hK₀R : R₀ ≤ 2 ^ K₀ := le_trans (le_max_left _ _) hK₀
  have hK₀1 : (1 : ℝ) ≤ 2 ^ K₀ := le_trans (le_max_right _ _) hK₀
  set f : Zero → ℝ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℝ) * ((1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ ^ 2) with hf
  have hlog0 : ∀ z : ℂ, 0 ≤ Real.log (1 + ‖z‖) :=
    fun z => Real.log_nonneg (by linarith [norm_nonneg z])
  have hf0 : ∀ ρ, 0 ≤ f ρ := by
    intro ρ
    have := hlog0 ρ.val
    rw [hf]
    positivity
  -- the low part: zeros in the closed ball of radius `2^K₀`, a finite set
  set Low : Finset ℂ :=
    (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite ((2 : ℝ) ^ K₀)).toFinset with hLow
  set fC : ℂ → ℝ := fun z => (ZD.xiOrderNat z : ℝ) * ((1 + Real.log (1 + ‖z‖)) / ‖z‖ ^ 2) with hfC
  set M_low : ℝ := ∑ z ∈ Low, fC z with hM
  -- the shell majorant
  set b : ℕ → ℝ := fun k => 2 * C * Real.log 2 * ((k + 1) * (k + 3)) / 2 ^ k with hb
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    rw [hb]
    positivity
  have hbsum : Summable b := by
    have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have h0 : Summable (fun k : ℕ => (k : ℝ) ^ 0 * (1 / 2 : ℝ) ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 0 (by norm_num)
    have h := ((h2.add (h1.mul_left 4)).add (h0.mul_left 3)).mul_left (2 * C * Real.log 2)
    refine h.congr (fun k => ?_)
    rw [hb]
    simp only [one_div_pow, pow_one, pow_zero]
    field_simp
    ring
  refine summable_of_sum_le hf0 (c := M_low + ∑' k, b k) (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.val‖ < 2 ^ K₀)]
  have hlow : ∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2 ^ K₀), f ρ ≤ M_low := by
    rw [hM]
    have himg : ∑ ρ ∈ u.filter (fun ρ => ‖ρ.val‖ < 2 ^ K₀), f ρ
        = ∑ z ∈ (u.filter (fun ρ => ‖ρ.val‖ < 2 ^ K₀)).image Subtype.val, fC z := by
      rw [Finset.sum_image (fun x _ y _ h => Subtype.val_injective h)]
    rw [himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
      simp only [Finset.mem_filter] at hρ
      rw [hLow, Set.Finite.mem_toFinset]
      refine ⟨ρ.property, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hρ.2.le
    · intro z _ _
      have := hlog0 z
      rw [hfC]
      positivity
  have hhigh : ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.val‖ < 2 ^ K₀), f ρ ≤ ∑' k, b k := by
    set v := u.filter (fun ρ => ¬ ‖ρ.val‖ < 2 ^ K₀) with hv
    rw [← Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem shellIdx hρ) f]
    have hshell : ∀ k ∈ v.image shellIdx,
        ∑ ρ ∈ v.filter (fun ρ => shellIdx ρ = k), f ρ ≤ b k := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨ρ₀, hρ₀, hρ₀k⟩
      have hρ₀v : ¬ ‖ρ₀.val‖ < 2 ^ K₀ := (Finset.mem_filter.mp hρ₀).2
      have hρ₀1 : 1 ≤ ‖ρ₀.val‖ := le_trans hK₀1 (not_lt.mp hρ₀v)
      have hKk : (2 : ℝ) ^ K₀ ≤ 2 ^ (k + 1) := by
        rw [← hρ₀k]
        exact le_trans (not_lt.mp hρ₀v) (shellIdx_bounds hρ₀1).2.le
      have hR : R₀ ≤ 2 ^ (k + 1) := le_trans hK₀R hKk
      set S := v.filter (fun ρ => shellIdx ρ = k) with hS
      have hS1 : ∀ ρ ∈ S, 1 ≤ ‖ρ.val‖ := by
        intro ρ hρ
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2
        exact le_trans hK₀1 (not_lt.mp this)
      have hSk : ∀ ρ ∈ S, shellIdx ρ = k := fun ρ hρ => (Finset.mem_filter.mp hρ).2
      have hSle : ∀ ρ ∈ S, ‖ρ.val‖ ≤ 2 ^ (k + 1) := by
        intro ρ hρ
        have := (shellIdx_bounds (hS1 ρ hρ)).2
        rw [hSk ρ hρ] at this
        exact this.le
      have hcnt := hcount (2 ^ (k + 1)) hR S hSle
      have hel : ∀ ρ ∈ S, f ρ ≤ (ZD.xiOrderNat ρ.val : ℝ) * ((k + 3) / 4 ^ k) := by
        intro ρ hρ
        rw [hf]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := logWeight_le_shell (hS1 ρ hρ)
        rw [hSk ρ hρ] at this
        exact this
      calc ∑ ρ ∈ S, f ρ ≤ ∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) * ((k + 3) / 4 ^ k) :=
            Finset.sum_le_sum hel
        _ = ((k + 3) / 4 ^ k) * ∑ ρ ∈ S, (ZD.xiOrderNat ρ.val : ℝ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun ρ _ => by ring)
        _ ≤ ((k + 3) / 4 ^ k) * (C * 2 ^ (k + 1) * Real.log ((2 : ℝ) ^ (k + 1))) :=
            mul_le_mul_of_nonneg_left hcnt (by positivity)
        _ = b k := by
            rw [hb, Real.log_pow]
            push_cast
            have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
            rw [h4]
            field_simp
            ring
    calc ∑ k ∈ v.image shellIdx, ∑ ρ ∈ v.filter (fun ρ => shellIdx ρ = k), f ρ
        ≤ ∑ k ∈ v.image shellIdx, b k := Finset.sum_le_sum hshell
      _ ≤ ∑' k, b k := hbsum.sum_le_tsum _ (fun k _ => hb0 k)
  linarith

/-! ## 2. The one `t`-integral -/

theorem integral_inv_one_add_abs {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (-R)..R, (1 + |t|)⁻¹ = 2 * Real.log (1 + R) := by
  have hcont : Continuous (fun t : ℝ => (1 + |t|)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => (1 + |t|)⁻¹) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-R) 0) (hint 0 R)]
  have hright : ∫ t in (0 : ℝ)..R, (1 + |t|)⁻¹ = Real.log (1 + R) := by
    have hc : ∫ t in (0 : ℝ)..R, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..R, (1 + t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hR] at ht
      show (1 + |t|)⁻¹ = (1 + t)⁻¹
      rw [abs_of_nonneg ht.1]
    rw [hc]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) R,
        HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹) t := by
      intro t ht
      rw [uIcc_of_le hR] at ht
      have h1 : (1 + t) ≠ 0 := by linarith [ht.1]
      have h := ((hasDerivAt_id' t).const_add 1).log h1
      refine h.congr_deriv ?_
      rw [one_div]
    have hii : IntervalIntegrable (fun t : ℝ => (1 + t)⁻¹) volume 0 R := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      rw [uIcc_of_le hR] at ht
      linarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    simp
  have hleft : ∫ t in (-R)..(0 : ℝ), (1 + |t|)⁻¹ = Real.log (1 + R) := by
    have hc : ∫ t in (-R)..(0 : ℝ), (1 + |t|)⁻¹ = ∫ t in (-R)..(0 : ℝ), (1 - t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      show (1 + |t|)⁻¹ = (1 - t)⁻¹
      rw [abs_of_nonpos ht.2, ← sub_eq_add_neg]
    rw [hc]
    have hderiv : ∀ t ∈ uIcc (-R) (0 : ℝ),
        HasDerivAt (fun t : ℝ => -Real.log (1 - t)) ((1 - t)⁻¹) t := by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      have h1 : (1 - t) ≠ 0 := by linarith [ht.2]
      have h := (((hasDerivAt_id' t).const_sub 1).log h1).neg
      refine h.congr_deriv ?_
      field_simp
    have hii : IntervalIntegrable (fun t : ℝ => (1 - t)⁻¹) volume (-R) 0 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      linarith [ht.2]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii]
    simp
  rw [hleft, hright]
  ring

/-- Pointwise: for `t ≥ 2(1+|γ|)`, `1/((1+|t|)(1+|t−γ|)) ≤ 2/(1+t)²`. -/
theorem inv_mul_inv_le_far {γ t : ℝ} (ht : 2 * (1 + |γ|) ≤ t) :
    ((1 + |t|) * (1 + |t - γ|))⁻¹ ≤ 2 * ((1 + t)⁻¹) ^ 2 := by
  have hg := abs_nonneg γ
  have ht0 : 0 ≤ t := by linarith
  have h1 : |t| = t := abs_of_nonneg ht0
  have h2 : t - |γ| ≤ |t - γ| := by
    have := abs_sub_abs_le_abs_sub t γ
    rw [h1] at this
    exact this
  have h3 : (1 + t) / 2 ≤ 1 + |t - γ| := by linarith
  rw [h1, inv_pow, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + t)
  nlinarith

theorem far_majorant_integrableOn (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => 2 * ((1 + t)⁻¹) ^ 2) (Ioi R) := by
  have hg : Integrable (fun t : ℝ => 2 * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  have hmeas : Measurable (fun t : ℝ => 2 * ((1 + t)⁻¹) ^ 2) := by fun_prop
  refine hg.integrableOn.mono' hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun t ht => ?_
  have ht0 : 0 ≤ t := le_trans hR (le_of_lt ht)
  have h1 : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow]
  gcongr

theorem integral_far_le {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in Ioi R, 2 * ((1 + t)⁻¹) ^ 2 = 2 / (1 + R) := by
  have hd : ∀ t ∈ Ici R, HasDerivAt (fun t : ℝ => -2 * (1 + t)⁻¹) (2 * ((1 + t)⁻¹) ^ 2) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by
      have : R ≤ t := ht
      linarith
    have h := (((hasDerivAt_id' t).const_add 1).inv h1).const_mul (-2)
    refine h.congr_deriv ?_
    rw [inv_pow]
    field_simp
  have hlim : Tendsto (fun t : ℝ => -2 * (1 + t)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left _ 1 tendsto_id)).const_mul (-2 : ℝ)
    simpa [Function.comp_def] using h
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (far_majorant_integrableOn R hR) hlim]
  field_simp
  ring

/-- The `t`-integrand is integrable: `f ≤ (2 + 4γ²)/(1+t²)`. -/
theorem integrable_inv_mul_inv (γ : ℝ) :
    Integrable (fun t : ℝ => ((1 + |t|) * (1 + |t - γ|))⁻¹) := by
  set g := |γ| with hg
  have hfc : Continuous (fun t : ℝ => ((1 + |t|) * (1 + |t - γ|))⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hmaj : Integrable (fun t : ℝ => (2 + 4 * g ^ 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' hfc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ((1 + |t|) * (1 + |t - γ|))⁻¹ ≤ (2 + 4 * g ^ 2) * (1 + t ^ 2)⁻¹
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have htri := abs_sub_abs_le_abs_sub t γ
  have hprod1 : 1 ≤ (1 + |t|) * (1 + |t - γ|) :=
    one_le_mul_of_one_le_of_one_le (by linarith [abs_nonneg t]) (by linarith [abs_nonneg (t - γ)])
  rcases le_or_gt |t| (2 * g) with h | h
  · have hsq : |t| ^ 2 ≤ (2 * g) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) h 2
    nlinarith [abs_nonneg t, abs_nonneg (t - γ)]
  · have h2 : |t| / 2 ≤ |t - γ| := by rw [hg] at h; linarith
    have hprod2 : (1 + |t|) * (1 + |t| / 2) ≤ (1 + |t|) * (1 + |t - γ|) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [abs_nonneg t, abs_nonneg (t - γ)]

/-- **The `t`-integral bound**:
`∫ dt/((1+|t|)(1+|t−γ|)) ≤ 12 (1 + log(1+|γ|))/(1+|γ|)`. -/
theorem integral_inv_mul_inv_le (γ : ℝ) :
    ∫ t : ℝ, ((1 + |t|) * (1 + |t - γ|))⁻¹ ≤ 12 * (1 + Real.log (1 + |γ|)) / (1 + |γ|) := by
  set g := |γ| with hg
  have hg0 : 0 ≤ g := abs_nonneg γ
  set R : ℝ := 2 * (1 + g) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set f : ℝ → ℝ := fun t => ((1 + |t|) * (1 + |t - γ|))⁻¹ with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => by rw [hf]; positivity
  have hfc : Continuous f := by
    rw [hf]; exact Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hfi : Integrable f := integrable_inv_mul_inv γ
  -- split the line: `Iic (−R) ∪ Ioc (−R) R ∪ Ioi R`
  have hsplit : ∫ t, f t = (∫ t in Iic (-R), f t) + (∫ t in Ioc (-R) R, f t)
      + ∫ t in Ioi R, f t := by
    have h1 := integral_add_compl (measurableSet_Iic (a := -R)) hfi
    rw [Set.compl_Iic] at h1
    have h2 : ∫ t in Ioi (-R), f t = (∫ t in Ioc (-R) R, f t) + ∫ t in Ioi R, f t := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : -R ≤ R)]
      exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hfi.integrableOn hfi.integrableOn
    rw [← h1, h2]
    ring
  -- (P1) the right tail
  have hP1 : ∫ t in Ioi R, f t ≤ 2 / (1 + R) := by
    rw [← integral_far_le hR0]
    apply setIntegral_mono_on hfi.integrableOn (far_majorant_integrableOn R hR0) measurableSet_Ioi
    intro t ht
    exact inv_mul_inv_le_far (γ := γ) (le_of_lt ht)
  -- (P2) the left tail, by reflection
  have hP2 : ∫ t in Iic (-R), f t ≤ 2 / (1 + R) := by
    have hrefl : ∫ t in Iic (-R), f t = ∫ t in Ioi R, f (-t) := by
      have := integral_comp_neg_Iic (-R) (fun t => f (-t))
      simp only [neg_neg] at this
      rw [← this]
    rw [hrefl, ← integral_far_le hR0]
    have hfi' : IntegrableOn (fun t => f (-t)) (Ioi R) := by
      have := hfi.comp_neg
      exact this.integrableOn
    apply setIntegral_mono_on hfi' (far_majorant_integrableOn R hR0) measurableSet_Ioi
    intro t ht
    have ht' : 2 * (1 + |(-γ)|) ≤ t := by rw [abs_neg]; exact le_of_lt ht
    have := inv_mul_inv_le_far (γ := -γ) ht'
    rw [hf]
    show ((1 + |-t|) * (1 + |-t - γ|))⁻¹ ≤ 2 * ((1 + t)⁻¹) ^ 2
    rw [abs_neg, show -t - γ = -(t - -γ) by ring, abs_neg]
    exact this
  -- (P3) the middle: `1/(uv) ≤ (1/u + 1/v)/(2+g)`
  have hP3 : ∫ t in Ioc (-R) R, f t
      ≤ (1 / (2 + g)) * (2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g))) := by
    rw [← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    have hpt : ∀ t ∈ Icc (-R) R, f t ≤ (1 / (2 + g)) * ((1 + |t|)⁻¹ + (1 + |t - γ|)⁻¹) := by
      intro t _
      rw [hf]
      show ((1 + |t|) * (1 + |t - γ|))⁻¹ ≤ (1 / (2 + g)) * ((1 + |t|)⁻¹ + (1 + |t - γ|)⁻¹)
      have hu : 0 < 1 + |t| := by positivity
      have hv : 0 < 1 + |t - γ| := by positivity
      have hsum : 2 + g ≤ (1 + |t|) + (1 + |t - γ|) := by
        have := abs_sub_abs_le_abs_sub t γ
        have h2 : |γ| - |t| ≤ |t - γ| := by
          have := abs_sub_abs_le_abs_sub γ t
          rw [abs_sub_comm] at this
          exact this
        rw [hg]
        linarith [abs_nonneg t]
      have key : (1 : ℝ) ≤ (1 / (2 + g)) * ((1 + |t - γ|) + (1 + |t|)) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        linarith
      calc ((1 + |t|) * (1 + |t - γ|))⁻¹ = 1 * ((1 + |t|) * (1 + |t - γ|))⁻¹ := by ring
        _ ≤ ((1 / (2 + g)) * ((1 + |t - γ|) + (1 + |t|))) * ((1 + |t|) * (1 + |t - γ|))⁻¹ :=
            mul_le_mul_of_nonneg_right key (by positivity)
        _ = (1 / (2 + g)) * ((1 + |t|)⁻¹ + (1 + |t - γ|)⁻¹) := by
            field_simp
    have hii1 : IntervalIntegrable (fun t : ℝ => (1 + |t|)⁻¹) volume (-R) R :=
      (Continuous.inv₀ (by fun_prop) (fun t => by positivity)).intervalIntegrable _ _
    have hii2 : IntervalIntegrable (fun t : ℝ => (1 + |t - γ|)⁻¹) volume (-R) R :=
      (Continuous.inv₀ (by fun_prop) (fun t => by positivity)).intervalIntegrable _ _
    have hmid2 : ∫ t in (-R)..R, (1 + |t - γ|)⁻¹ ≤ 2 * Real.log (1 + (R + g)) := by
      rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => (1 + |u|)⁻¹) γ,
        ← integral_inv_one_add_abs (by positivity : (0 : ℝ) ≤ R + g)]
      have hγ1 := le_abs_self γ
      have hγ2 := neg_abs_le γ
      apply intervalIntegral.integral_mono_interval (by rw [hg]; linarith)
        (by linarith) (by rw [hg]; linarith)
        (Eventually.of_forall fun t => by
          show (0 : ℝ) ≤ (1 + |t|)⁻¹
          positivity)
        ((Continuous.inv₀ (by fun_prop) (fun t => by positivity)).intervalIntegrable _ _)
    calc ∫ t in (-R)..R, f t
        ≤ ∫ t in (-R)..R, (1 / (2 + g)) * ((1 + |t|)⁻¹ + (1 + |t - γ|)⁻¹) :=
          intervalIntegral.integral_mono_on (by linarith) (hfc.intervalIntegrable _ _)
            ((hii1.add hii2).const_mul _) hpt
      _ = (1 / (2 + g)) * ((∫ t in (-R)..R, (1 + |t|)⁻¹) + ∫ t in (-R)..R, (1 + |t - γ|)⁻¹) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hii1 hii2]
      _ ≤ (1 / (2 + g)) * (2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [integral_inv_one_add_abs hR0]
          linarith
  -- assemble
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlogR : Real.log (1 + R) ≤ Real.log 3 + Real.log (1 + g) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hR]; nlinarith
  have hlogRg : Real.log (1 + (R + g)) ≤ Real.log 3 + Real.log (1 + g) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hR]; nlinarith
  have hlg0 : 0 ≤ Real.log (1 + g) := Real.log_nonneg (by linarith)
  have hmid : (1 / (2 + g)) * (2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g)))
      ≤ (4 * Real.log 3 + 4 * Real.log (1 + g)) / (1 + g) := by
    have h1 : (1 : ℝ) / (2 + g) ≤ 1 / (1 + g) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    have h2 : 2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g))
        ≤ 4 * Real.log 3 + 4 * Real.log (1 + g) := by linarith
    have h3 : 0 ≤ 2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g)) := by
      have : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
      have : 0 ≤ Real.log (1 + (R + g)) := Real.log_nonneg (by linarith)
      linarith
    calc (1 / (2 + g)) * (2 * Real.log (1 + R) + 2 * Real.log (1 + (R + g)))
        ≤ (1 / (1 + g)) * (4 * Real.log 3 + 4 * Real.log (1 + g)) :=
          mul_le_mul h1 h2 h3 (by positivity)
      _ = (4 * Real.log 3 + 4 * Real.log (1 + g)) / (1 + g) := by ring
  have htail : 2 / (1 + R) + 2 / (1 + R) ≤ 2 / (1 + g) := by
    rw [hR, ← add_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htot : (4 * Real.log 3 + 4 * Real.log (1 + g)) / (1 + g) + 2 / (1 + g)
      ≤ 12 * (1 + Real.log (1 + g)) / (1 + g) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  rw [hsplit]
  linarith

/-! ## 3. Selberg's kernel -/

/-- The entire factor `G₁(w) = e^{Lw}(e^{Lw} − 1)/(Lw)`, `G₁(0) = 1`, decay 1. -/
def linG (L : ℝ) (w : ℂ) : ℂ := Complex.exp (L * w) * expRatio L w

theorem linG_differentiable (L : ℝ) : Differentiable ℂ (linG L) := by
  unfold linG
  exact (by fun_prop : Differentiable ℂ fun w : ℂ => Complex.exp (L * w)).mul
    (expRatio_differentiable L)

theorem linG_zero {L : ℝ} (hL : L ≠ 0) : linG L 0 = 1 := by
  simp [linG, expRatio_zero hL]

/-- Selberg's kernel `K₁(w) = G₁(w)/w = (e^{2Lw} − e^{Lw})/(w² L)`. -/
def linKernel (L : ℝ) (w : ℂ) : ℂ := linG L w / w

theorem linKernel_eq {L : ℝ} (hL : L ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    linKernel L w = (Complex.exp (2 * L * w) - Complex.exp (L * w)) / (w ^ 2 * L) := by
  unfold linKernel linG
  rw [expRatio_of_ne L hw]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have h2 : Complex.exp (2 * L * w) = Complex.exp (L * w) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  field_simp

/-- `G₁` decays at order 1 on every half-plane `Re w ≤ b'`. -/
theorem linG_bound {L : ℝ} (hL : 0 < L) {b' : ℝ} (hb' : 0 ≤ b') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ≤ b' → ‖linG L w‖ ≤ C / (1 + |w.im|) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (linG_differentiable L).continuous.continuousOn
  set E : ℝ := Real.exp (L * b') with hE
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
  set C : ℝ := max (2 * max M 0) (2 * E * ((E + 1) / L)) with hC
  refine ⟨C, by positivity, fun w hw => ?_⟩
  have hpos : 0 < 1 + |w.im| := by positivity
  by_cases h1 : ‖w‖ ≤ 1
  · have hMw : ‖linG L w‖ ≤ max M 0 :=
      le_trans (hM w (by simpa using h1)) (le_max_left _ _)
    have him : |w.im| ≤ 1 := le_trans (Complex.abs_im_le_norm w) h1
    rw [le_div_iff₀ hpos]
    calc ‖linG L w‖ * (1 + |w.im|) ≤ max M 0 * 2 :=
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
    have hG : ‖linG L w‖ ≤ E * ((E + 1) / (L * ‖w‖)) := by
      unfold linG
      rw [norm_mul]
      exact mul_le_mul hexp hratio (by positivity) (by positivity)
    rw [le_div_iff₀ hpos]
    have hwpos : 0 < ‖w‖ := by linarith
    calc ‖linG L w‖ * (1 + |w.im|) ≤ (E * ((E + 1) / (L * ‖w‖))) * (2 * ‖w‖) :=
          mul_le_mul hG hnorm (by positivity) (by positivity)
      _ = 2 * E * ((E + 1) / L) := by field_simp
      _ ≤ C := le_max_right _ _

/-- Uniform decay of order 1 of `s ↦ G₁(s − s₀)` on the strip `a ≤ Re s ≤ b` (`Re s₀ < b`). -/
theorem linG_strip_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (_hab : a ≤ b) {s₀ : ℂ}
    (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, ∀ T : ℝ,
      ‖linG L (x + T * I - s₀)‖ ≤ C / (1 + |T|) ^ 1 := by
  obtain ⟨C₀, hC₀, hbound⟩ := linG_bound hL (b' := b - s₀.re) (by linarith)
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
  calc ‖linG L ((x : ℂ) + T * I - s₀)‖ ≤ C₀ / (1 + |T - s₀.im|) := h
    _ ≤ C₀ * (1 + |s₀.im|) / (1 + |T|) := by
        rw [div_le_div_iff₀ hpos1 hpos2]
        calc C₀ * (1 + |T|) ≤ C₀ * ((1 + |s₀.im|) * (1 + |T - s₀.im|)) :=
              mul_le_mul_of_nonneg_left hkey hC₀
          _ = C₀ * (1 + |s₀.im|) * (1 + |T - s₀.im|) := by ring

/-- `K₁(s − s₀)` decays at order 2 on the two lines `Re s ∈ {a, b}` (`a < Re s₀ < b`). -/
theorem linKernel_line_decay {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {s₀ : ℂ}
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, (σ = a ∨ σ = b) →
      LineDecay (fun s => linKernel L (s - s₀)) σ C 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := linG_strip_decay hL hab hs₀b
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
  show ‖linKernel L ((σ : ℂ) + t * I - s₀)‖ ≤ _
  unfold linKernel
  rw [norm_div]
  have hpos2 : 0 < (1 + |t|) ^ 2 := by positivity
  calc ‖linG L ((σ : ℂ) + t * I - s₀)‖ / ‖(σ : ℂ) + t * I - s₀‖
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

theorem linKernel_line_continuous (L : ℝ) {σ : ℝ} {s₀ : ℂ} (h : σ ≠ s₀.re) :
    Continuous (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)) := by
  unfold linKernel
  refine ((linG_differentiable L).continuous.comp (by fun_prop)).div (by fun_prop) ?_
  intro t h0
  have := congrArg Complex.re h0
  simp at this
  exact h (by linarith)

/-! ## 4. The strip residue at decay order 1 -/

/-- Decay of order 1 times the resolvent factor is integrable on a line off the pole (with a
pole-dependent constant). -/
theorem integrable_line_mul_inv_sub₁ {F : ℂ → ℂ} {σ C : ℝ}
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) (hC : 0 ≤ C) (hdec : LineDecay F σ C 1)
    {p : ℂ} (hp : σ ≠ p.re) :
    Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) := by
  set δ : ℝ := |σ - p.re| with hδ
  have hδ0 : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hp)
  set κ : ℝ := min (1 / 2) (δ / (1 + (2 * |p.im| + 1) ^ 2)) with hκ
  have hκ0 : 0 < κ := lt_min (by norm_num) (by positivity)
  have hne : ∀ t : ℝ, (σ : ℂ) + t * I - p ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact hp (by linarith)
  have hcont : Continuous (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - p)⁻¹) :=
    hF.mul (Continuous.inv₀ (by fun_prop) hne)
  have hg : Integrable (fun t : ℝ => (C / κ) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hFt : ‖F (σ + t * I)‖ ≤ C / (1 + |t|) := by
    have := hdec t
    rwa [pow_one] at this
  have hD1 : δ ≤ ‖(σ : ℂ) + t * I - p‖ := by
    have hre : |((σ : ℂ) + t * I - p).re| ≤ ‖(σ : ℂ) + t * I - p‖ := Complex.abs_re_le_norm _
    have hre' : ((σ : ℂ) + t * I - p).re = σ - p.re := by simp
    rw [hre'] at hre
    exact hre
  have hD2 : |t - p.im| ≤ ‖(σ : ℂ) + t * I - p‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + t * I - p)
    simpa using this
  have hD0 : 0 < ‖(σ : ℂ) + t * I - p‖ := lt_of_lt_of_le hδ0 hD1
  have hkey : κ * (1 + t ^ 2) ≤ (1 + |t|) * ‖(σ : ℂ) + t * I - p‖ := by
    rcases le_or_gt |t| (2 * |p.im| + 1) with h | h
    · have hκ2 : κ ≤ δ / (1 + (2 * |p.im| + 1) ^ 2) := min_le_right _ _
      have hsq : t ^ 2 ≤ (2 * |p.im| + 1) ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) h 2
      have hpos : (0 : ℝ) < 1 + (2 * |p.im| + 1) ^ 2 := by positivity
      calc κ * (1 + t ^ 2) ≤ (δ / (1 + (2 * |p.im| + 1) ^ 2)) * (1 + (2 * |p.im| + 1) ^ 2) :=
            mul_le_mul hκ2 (by linarith) (by positivity) (by positivity)
        _ = δ := by field_simp
        _ ≤ 1 * ‖(σ : ℂ) + t * I - p‖ := by rw [one_mul]; exact hD1
        _ ≤ (1 + |t|) * ‖(σ : ℂ) + t * I - p‖ :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) hD0.le
    · have hκ1 : κ ≤ 1 / 2 := min_le_left _ _
      have h1 : (1 + |t|) / 2 ≤ |t - p.im| := by
        have := abs_sub_abs_le_abs_sub t p.im
        linarith
      have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        rw [← sq_abs t]; nlinarith [abs_nonneg t]
      calc κ * (1 + t ^ 2) ≤ (1 / 2) * (1 + |t|) ^ 2 :=
            mul_le_mul hκ1 hsq (by positivity) (by norm_num)
        _ = (1 + |t|) * ((1 + |t|) / 2) := by ring
        _ ≤ (1 + |t|) * ‖(σ : ℂ) + t * I - p‖ :=
            mul_le_mul_of_nonneg_left (le_trans h1 hD2) (by positivity)
  rw [norm_mul, norm_inv]
  have hpos1 : (1 + |t|) ≠ 0 := by positivity
  have hD0' : ‖(σ : ℂ) + t * I - p‖ ≠ 0 := hD0.ne'
  calc ‖F (σ + t * I)‖ * ‖(σ : ℂ) + t * I - p‖⁻¹
      ≤ (C / (1 + |t|)) * ‖(σ : ℂ) + t * I - p‖⁻¹ :=
        mul_le_mul_of_nonneg_right hFt (by positivity)
    _ = C / ((1 + |t|) * ‖(σ : ℂ) + t * I - p‖) := by field_simp
    _ ≤ C / (κ * (1 + t ^ 2)) := div_le_div_of_nonneg_left hC (by positivity) hkey
    _ = (C / κ) * (1 + t ^ 2)⁻¹ := by
        rw [div_mul_eq_div_div, div_eq_mul_inv (C / κ)]

/-- **Strip residue at decay order 1**: for an entire `F` with `‖F(x+iT)‖ ≤ C/(1+|T|)` on the
strip and `a < Re ρ < b`, `∮_strip F(s)/(s−ρ) = 2πi F(ρ)`. -/
theorem stripBoundary_div_sub_eq₁ {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a b C : ℝ}
    (hC : 0 ≤ C) (hab : a ≤ b)
    (hdec : ∀ x ∈ Icc a b, ∀ T : ℝ, ‖F (x + T * I)‖ ≤ C / (1 + |T|) ^ 1)
    {ρ : ℂ} (hρa : a < ρ.re) (hρb : ρ.re < b) :
    stripBoundary (fun s => F s * (s - ρ)⁻¹) a b = 2 * Real.pi * I * F ρ := by
  have hint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => F (σ + t * I) * ((σ : ℂ) + t * I - ρ)⁻¹) := by
    intro σ hσ
    have hσab : σ ∈ Icc a b := by
      rcases hσ with rfl | rfl
      · exact ⟨le_refl _, hab⟩
      · exact ⟨hab, le_refl _⟩
    have hp : σ ≠ ρ.re := by rcases hσ with rfl | rfl <;> linarith
    exact integrable_line_mul_inv_sub₁ (hF.continuous.comp (by fun_prop)) hC
      (fun t => hdec σ hσab t) hp
  have hhor : ∀ x ∈ Icc a b, ∀ T : ℝ, |ρ.im| + 1 ≤ |T| →
      ‖F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹‖ ≤ C / (1 + |T|) ^ 1 := by
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
        ≤ (C / (1 + |T|) ^ 1) * 1 :=
          mul_le_mul (hdec x hx T) hkerT (norm_nonneg _) (by positivity)
      _ = C / (1 + |T|) ^ 1 := mul_one _
  have htop : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹) atTop
      (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ 1 * (b - a)) atTop (𝓝 0) := by
      have := (tendsto_const_div_one_add_pow (c := C) (le_refl 1)).mul_const (b - a)
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg ρ.im]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + T * I) * ((x : ℂ) + T * I - ρ)⁻¹)
      (C := C / (1 + T) ^ 1) ?_
    · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
    · intro x hx
      have hx' : x ∈ Icc a b := by
        rw [uIoc_of_le hab] at hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      have := hhor x hx' T (by rw [abs_of_nonneg hT0]; exact hT)
      rwa [abs_of_nonneg hT0] at this
  have hbot : Tendsto (fun T : ℝ => ∫ x in a..b, F (x + (-T : ℝ) * I)
      * ((x : ℂ) + (-T : ℝ) * I - ρ)⁻¹) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ => C / (1 + T) ^ 1 * (b - a)) atTop (𝓝 0) := by
      have := (tendsto_const_div_one_add_pow (c := C) (le_refl 1)).mul_const (b - a)
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    have hT0 : 0 ≤ T := by linarith [abs_nonneg ρ.im]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x : ℝ => F (x + (-T : ℝ) * I) * ((x : ℂ) + (-T : ℝ) * I - ρ)⁻¹)
      (C := C / (1 + T) ^ 1) ?_
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

/-! ## 5. Per-zero residue with the pole, Selberg kernel -/

theorem stripBoundary_linKernel_hadamardTerm {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hρs : ρ ≠ s₀) :
    stripBoundary (fun s => linKernel L (s - s₀) * hadamardTerm ρ s) a b
      = 2 * Real.pi * I * (hadamardTerm ρ s₀ + linKernel L (ρ - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdec⟩ := linG_strip_decay hL hab hs₀b
  set G : ℂ → ℂ := fun s => linG L (s - s₀) with hGdef
  have hGd : Differentiable ℂ G :=
    (linG_differentiable L).comp (differentiable_id.sub_const s₀)
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
      linKernel L ((σ : ℂ) + t * I - s₀) * hadamardTerm ρ ((σ : ℂ) + t * I)
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
    simp only [linKernel, hadamardTerm, hGdef]
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
    show linG L (s₀ - s₀) = 1
    rw [sub_self]
    exact linG_zero hL.ne'
  have hGρ : G ρ = linG L (ρ - s₀) := rfl
  rw [hG0, hGρ]
  have hρs' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hρs
  unfold linKernel hadamardTerm
  field_simp
  ring

/-- The strip integral of Selberg's kernel alone is the residue of its pole: `2πi`. -/
theorem stripBoundary_linKernel {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hs₀a : a < s₀.re) (hs₀b : s₀.re < b) :
    stripBoundary (fun s => linKernel L (s - s₀)) a b = 2 * Real.pi * I := by
  obtain ⟨C, hC, hdec⟩ := linG_strip_decay hL hab hs₀b
  have hGd : Differentiable ℂ (fun s => linG L (s - s₀)) :=
    (linG_differentiable L).comp (differentiable_id.sub_const s₀)
  have h := stripBoundary_div_sub_eq₁ hGd hC hab hdec hs₀a hs₀b
  have hF : (fun s => linKernel L (s - s₀)) = fun s => linG L (s - s₀) * (s - s₀)⁻¹ := by
    funext s
    simp only [linKernel, div_eq_mul_inv]
  rw [hF, h, sub_self, linG_zero hL.ne', mul_one]

/-! ## 6. The exchange at kernel decay 2 -/

/-- Pointwise on a line, for a kernel of decay 2:
`‖F·(1/(s−ρ)+1/ρ)‖ ≤ (weilK/‖ρ‖) · ((1+|t|)(1+|t−γ|))⁻¹`. -/
theorem lin_pointwise_bound {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b)
    {σ : ℝ} (hσ : σ = a ∨ σ = b) (hdec : LineDecay F σ C 2) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (t : ℝ) :
    ‖F (σ + t * I) * hadamardTerm ρ (σ + t * I)‖
      ≤ (weilK a b C / ‖ρ‖) * ((1 + |t|) * (1 + |t - ρ.im|))⁻¹ := by
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
  set s : ℂ := (σ : ℂ) + t * I with hs
  set γ : ℝ := ρ.im with hγ
  set u : ℝ := 1 + |t| with hu
  set v : ℝ := 1 + |t - γ| with hv
  have hu1 : 1 ≤ u := by rw [hu]; linarith [abs_nonneg t]
  have hv1 : 1 ≤ v := by rw [hv]; linarith [abs_nonneg (t - γ)]
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hR0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hD0 : 0 < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
  have hF : ‖F s‖ ≤ C / u ^ 2 := hdec t
  have hS : ‖s‖ ≤ M * u := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |σ| + |t| := by simp [hs]
      _ ≤ M + M * |t| := by nlinarith [abs_nonneg t]
      _ = M * u := by rw [hu]; ring
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
  rw [norm_mul, norm_hadamardTerm hsρ hρne]
  have hstep1 : ‖F s‖ * (‖s‖ / (‖s - ρ‖ * ‖ρ‖))
      ≤ (C / u ^ 2) * ((M * u) / ((η / 2 * v) * ‖ρ‖)) := by
    have hden : (η / 2 * v) * ‖ρ‖ ≤ ‖s - ρ‖ * ‖ρ‖ := mul_le_mul_of_nonneg_right hD hR0.le
    have hden0 : 0 < (η / 2 * v) * ‖ρ‖ := by positivity
    have hfrac : ‖s‖ / (‖s - ρ‖ * ‖ρ‖) ≤ (M * u) / ((η / 2 * v) * ‖ρ‖) :=
      div_le_div₀ (by positivity) hS hden0 hden
    exact mul_le_mul hF hfrac (by positivity) (by positivity)
  have hstep2 : (C / u ^ 2) * ((M * u) / ((η / 2 * v) * ‖ρ‖))
      = (2 * C * M / η) * (1 / ‖ρ‖) * (u * v)⁻¹ := by
    field_simp
  have hK : 2 * C * M / η ≤ weilK a b C := by
    unfold weilK
    rw [← hη, ← hM]
    apply div_le_div_of_nonneg_right _ hη0.le
    nlinarith [mul_nonneg hC (le_trans zero_le_one hM1)]
  calc ‖F s‖ * (‖s‖ / (‖s - ρ‖ * ‖ρ‖))
      ≤ (C / u ^ 2) * ((M * u) / ((η / 2 * v) * ‖ρ‖)) := hstep1
    _ = (2 * C * M / η) * (1 / ‖ρ‖) * (u * v)⁻¹ := hstep2
    _ ≤ weilK a b C * (1 / ‖ρ‖) * (u * v)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (by positivity)
    _ = (weilK a b C / ‖ρ‖) * (u * v)⁻¹ := by ring

theorem hadamardLineTerm_continuous' {F : ℂ → ℂ} {σ : ℝ}
    (hF : Continuous (fun t : ℝ => F (σ + t * I))) {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hσ : σ = a ∨ σ = b) (ρ : Zero) : Continuous (hadamardLineTerm F σ ρ) := by
  unfold hadamardLineTerm hadamardTerm
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  refine hF.mul (continuous_const.mul (Continuous.add ?_ continuous_const))
  refine Continuous.div continuous_const (hline.sub continuous_const) ?_
  intro t
  exact sub_ne_zero.mpr (line_ne_zero_point ha hb hσ t ρ.property)

theorem lin_hadamardLineTerm_norm_le {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0)
    (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hdec : LineDecay F σ C 2) (ρ : Zero) (t : ℝ) :
    ‖hadamardLineTerm F σ ρ t‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
          * ((1 + |t|) * (1 + |t - ρ.val.im|))⁻¹ := by
  unfold hadamardLineTerm
  have h := lin_pointwise_bound hC ha hb hσ hdec ρ.property t
  have hm : ‖((ZD.xiOrderNat ρ.val : ℕ) : ℂ)‖ = (ZD.xiOrderNat ρ.val : ℝ) := by
    rw [Complex.norm_natCast]
  calc ‖F (σ + t * I) * ((ZD.xiOrderNat ρ.val : ℂ) * hadamardTerm ρ.val (σ + t * I))‖
      = (ZD.xiOrderNat ρ.val : ℝ) * ‖F (σ + t * I) * hadamardTerm ρ.val (σ + t * I)‖ := by
        rw [norm_mul, norm_mul, hm, norm_mul]
        ring
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ)
          * ((weilK a b C / ‖ρ.val‖) * ((1 + |t|) * (1 + |t - ρ.val.im|))⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem lin_hadamardLineTerm_integrable {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0)
    (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hF : Continuous (fun t : ℝ => F (σ + t * I)))
    (hdec : LineDecay F σ C 2) (ρ : Zero) : Integrable (hadamardLineTerm F σ ρ) := by
  have hg : Integrable (fun t : ℝ => ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
      * ((1 + |t|) * (1 + |t - ρ.val.im|))⁻¹) :=
    (integrable_inv_mul_inv ρ.val.im).const_mul _
  refine Integrable.mono' hg (hadamardLineTerm_continuous' hF ha hb hσ ρ).aestronglyMeasurable ?_
  exact Eventually.of_forall (lin_hadamardLineTerm_norm_le hC ha hb hσ hdec ρ)

theorem lin_hadamardLineTerm_integral_norm_le {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hdec : LineDecay F σ C 2)
    (ρ : Zero) :
    ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖
      ≤ ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
          * (12 * (1 + Real.log (1 + |ρ.val.im|)) / (1 + |ρ.val.im|)) := by
  calc ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖
      ≤ ∫ t : ℝ, ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
          * ((1 + |t|) * (1 + |t - ρ.val.im|))⁻¹ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          ((integrable_inv_mul_inv _).const_mul _)
        exact Eventually.of_forall (lin_hadamardLineTerm_norm_le hC ha hb hσ hdec ρ)
    _ = ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
          * ∫ t : ℝ, ((1 + |t|) * (1 + |t - ρ.val.im|))⁻¹ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_inv_mul_inv_le _)
          (by have := weilK_nonneg ha hb hC; positivity)

/-- The majorant `m_ρ (weilK/|ρ|) · 12(1+log(1+|γ|))/(1+|γ|)` is summable over the zeros. -/
theorem lin_majorant_summable {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0) (hb : 1 < b) :
    Summable (fun ρ : Zero => ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
      * (12 * (1 + Real.log (1 + |ρ.val.im|)) / (1 + |ρ.val.im|))) := by
  have hK := weilK_nonneg ha hb hC
  have hmaj := (summable_logWeight_nontrivialZeros).mul_left (12 * weilK a b C)
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hmaj
  · have : 0 ≤ Real.log (1 + |ρ.val.im|) :=
      Real.log_nonneg (by linarith [abs_nonneg ρ.val.im])
    positivity
  · obtain ⟨hρ0, hρ1, -⟩ := ρ.property
    have hR0 : 0 < ‖ρ.val‖ := norm_pos_iff.mpr (zero_ne_zero ρ.property)
    have hRγ : ‖ρ.val‖ ≤ 1 + |ρ.val.im| := by
      calc ‖ρ.val‖ ≤ |ρ.val.re| + |ρ.val.im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1 + |ρ.val.im| := by rw [abs_of_pos hρ0]; linarith
    have hγR : |ρ.val.im| ≤ ‖ρ.val‖ := Complex.abs_im_le_norm _
    have hlog : Real.log (1 + |ρ.val.im|) ≤ Real.log (1 + ‖ρ.val‖) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (1 + |ρ.val.im|) :=
      Real.log_nonneg (by linarith [abs_nonneg ρ.val.im])
    have hlog0' : 0 ≤ Real.log (1 + ‖ρ.val‖) := Real.log_nonneg (by linarith)
    have h1 : (1 + Real.log (1 + |ρ.val.im|)) / (1 + |ρ.val.im|)
        ≤ (1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ :=
      div_le_div₀ (by positivity) (by linarith) hR0 hRγ
    have hm0 : (0 : ℝ) ≤ ZD.xiOrderNat ρ.val := by positivity
    calc ((ZD.xiOrderNat ρ.val : ℝ) * (weilK a b C / ‖ρ.val‖))
          * (12 * (1 + Real.log (1 + |ρ.val.im|)) / (1 + |ρ.val.im|))
        = (12 * weilK a b C * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖)
            * ((1 + Real.log (1 + |ρ.val.im|)) / (1 + |ρ.val.im|)) := by ring
      _ ≤ (12 * weilK a b C * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖)
            * ((1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 12 * weilK a b C
            * ((ZD.xiOrderNat ρ.val : ℝ) * ((1 + Real.log (1 + ‖ρ.val‖)) / ‖ρ.val‖ ^ 2)) := by
          field_simp

theorem lin_summable_hadamardLineTerm_integral_norm {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hdec : LineDecay F σ C 2) :
    Summable (fun ρ : Zero => ∫ t : ℝ, ‖hadamardLineTerm F σ ρ t‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun ρ => lin_hadamardLineTerm_integral_norm_le hC ha hb hσ hdec ρ)
    (lin_majorant_summable hC ha hb)

theorem lin_lineIntegral_hadamard_exchange {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C) (ha : a < 0)
    (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hF : Continuous (fun t : ℝ => F (σ + t * I)))
    (hdec : LineDecay F σ C 2) :
    ∫ t : ℝ, ∑' ρ : Zero, hadamardLineTerm F σ ρ t
      = ∑' ρ : Zero, ∫ t : ℝ, hadamardLineTerm F σ ρ t :=
  (integral_tsum_of_summable_integral_norm
    (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ hF hdec ρ)
    (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ hdec)).symm

theorem lin_summable_hadamardLineTerm_integral {F : ℂ → ℂ} {a b C : ℝ} (hC : 0 ≤ C)
    (ha : a < 0) (hb : 1 < b) {σ : ℝ} (hσ : σ = a ∨ σ = b) (hdec : LineDecay F σ C 2) :
    Summable (fun ρ : Zero => ∫ t : ℝ, hadamardLineTerm F σ ρ t) :=
  Summable.of_norm_bounded (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ hdec)
    (fun _ => norm_integral_le_integral_norm _)

/-! ## 7. The zero side at kernel decay 2 -/

/-- **The zero side with a simple pole of residue one at `s₀`, kernel decay 2.** -/
theorem stripBoundary_pole_mul_logDeriv_xi₂ {F : ℂ → ℂ} {s₀ : ℂ} (hs₀ : s₀ ∉ ZD.NontrivialZeros)
    {a b C : ℝ} (ha : a < 0) (hb : 1 < b) (hC : 0 ≤ C)
    (hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) → Continuous (fun t : ℝ => F (σ + t * I)))
    (hdec : ∀ σ : ℝ, (σ = a ∨ σ = b) → LineDecay F σ C 2)
    (hres : ∀ ρ ∈ ZD.NontrivialZeros, stripBoundary (fun s => F s * hadamardTerm ρ s) a b
      = 2 * Real.pi * I * (hadamardTerm ρ s₀ + F ρ))
    (hpole : stripBoundary F a b = 2 * Real.pi * I) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) ∧
    stripBoundary (fun s => F s * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (logDeriv ZD.riemannXi s₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * F ρ.val) := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
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
  have hsumb := lin_summable_hadamardLineTerm_integral hC ha hb
    (Or.inr rfl : b = a ∨ b = b) (hdec b (Or.inr rfl))
  have hsuma := lin_summable_hadamardLineTerm_integral hC ha hb
    (Or.inl rfl : a = a ∨ a = b) (hdec a (Or.inl rfl))
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

/-- The zero side for Selberg's kernel with its pole at `s₀`. -/
theorem stripBoundary_linKernel_mul_logDeriv_xi {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀)) ∧
    stripBoundary (fun s => linKernel L (s - s₀) * logDeriv ZD.riemannXi s) a b
      = 2 * Real.pi * I * (logDeriv ZD.riemannXi s₀
          + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀)) := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := linKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply linKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  exact stripBoundary_pole_mul_logDeriv_xi₂ (F := fun s => linKernel L (s - s₀)) hs₀ ha hb hC
    hFc hdecl
    (fun ρ hρ => stripBoundary_linKernel_hadamardTerm hL ha hb hs₀a hs₀b hρ
      (fun h => hs₀ (h ▸ hρ)))
    (stripBoundary_linKernel hL hab hs₀a hs₀b)

/-! ## 8. The prime side: Selberg's weight -/

/-- The right linear ramp `(c − v)₊`. -/
def rampR1 (c v : ℝ) : ℝ := max (c - v) 0

/-- The left linear ramp `(v − c)₊`. -/
def rampL1 (c v : ℝ) : ℝ := max (v - c) 0

theorem rampR1_continuous (c : ℝ) : Continuous (rampR1 c) := by
  unfold rampR1; fun_prop

theorem rampL1_continuous (c : ℝ) : Continuous (rampL1 c) := by
  unfold rampL1; fun_prop

theorem rampR1_eq_of_le {c v : ℝ} (h : v ≤ c) : rampR1 c v = c - v := by
  unfold rampR1; rw [max_eq_left (by linarith)]

theorem rampR1_eq_zero_of_ge {c v : ℝ} (h : c ≤ v) : rampR1 c v = 0 := by
  unfold rampR1; rw [max_eq_right (by linarith)]

theorem rampL1_eq_zero_of_le {c v : ℝ} (h : v ≤ c) : rampL1 c v = 0 := by
  unfold rampL1; rw [max_eq_right (by linarith)]

theorem rampL1_neg (c v : ℝ) : rampL1 c (-v) = rampR1 (-c) v := by
  unfold rampL1 rampR1
  congr 1
  ring

/-- `u ↦ u e^{−wu}` is integrable on `(0, ∞)` for `Re w > 0`. -/
theorem lin_mul_exp_integrableOn {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-(w * u))) (Ioi 0) := by
  have hreal : IntegrableOn (fun u : ℝ => u ^ (1 : ℝ) * Real.exp (-w.re * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hw
  have hcont : Continuous (fun u : ℝ => (u : ℂ) * Complex.exp (-(w * u))) := by fun_prop
  refine Integrable.mono' hreal hcont.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu
  have e1 : u ^ (1 : ℝ) = u := Real.rpow_one u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_exp, e1]
  have : (-(w * u) : ℂ).re = -w.re * u := by simp
  rw [this]

/-- `∫₀^∞ u e^{−wu} du = 1/w²` for `Re w > 0`. -/
theorem integral_lin_mul_exp_neg {w : ℂ} (hw : 0 < w.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) * Complex.exp (-(w * u)) = 1 / w ^ 2 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  set Φ : ℂ → ℂ := fun z => -(Complex.exp (-(w * z)) * (z / w + 1 / w ^ 2)) with hΦ
  have hΦd : ∀ z : ℂ, HasDerivAt Φ (z * Complex.exp (-(w * z))) z := by
    intro z
    have he : HasDerivAt (fun z : ℂ => Complex.exp (-(w * z)))
        (Complex.exp (-(w * z)) * (-(w * 1))) z :=
      (Complex.hasDerivAt_exp _).comp z (((hasDerivAt_id z).const_mul w).neg)
    have hp : HasDerivAt (fun z : ℂ => z / w + 1 / w ^ 2) (1 / w) z :=
      ((hasDerivAt_id z).div_const w).add_const (1 / w ^ 2)
    have hd := (he.mul hp).neg
    refine hd.congr_deriv ?_
    field_simp
    ring
  have hderiv : ∀ u ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ => Φ u)
      ((u : ℂ) * Complex.exp (-(w * u))) u :=
    fun u _ => (hΦd (u : ℂ)).comp_ofReal
  have hlim : Tendsto (fun u : ℝ => Φ u) atTop (𝓝 0) := by
    set A : ℝ := ‖w‖ with hA
    have hA0 : 0 < A := norm_pos_iff.mpr hw0
    have hg : Tendsto (fun u : ℝ => (u ^ 1 * Real.exp (-(w.re * u))) / A
        + (u ^ 0 * Real.exp (-(w.re * u))) / A ^ 2) atTop (𝓝 0) := by
      have h1 := (tendsto_pow_mul_exp_neg_mul hw 1).div_const A
      have h0 := (tendsto_pow_mul_exp_neg_mul hw 0).div_const (A ^ 2)
      have := h1.add h0
      simpa using this
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [hΦ]
    simp only [norm_neg, norm_mul, Complex.norm_exp]
    have hre : (-(w * (u : ℂ))).re = -(w.re * u) := by simp
    rw [hre]
    have hn : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    have hbound : ‖(u : ℂ) / w + 1 / w ^ 2‖ ≤ u ^ 1 / A + u ^ 0 / A ^ 2 := by
      calc ‖(u : ℂ) / w + 1 / w ^ 2‖ ≤ ‖(u : ℂ) / w‖ + ‖(1 : ℂ) / w ^ 2‖ := norm_add_le _ _
        _ = u ^ 1 / A + u ^ 0 / A ^ 2 := by
            simp only [norm_div, norm_pow, hn, hA, norm_one]
            ring
    calc Real.exp (-(w.re * u)) * ‖(u : ℂ) / w + 1 / w ^ 2‖
        ≤ Real.exp (-(w.re * u)) * (u ^ 1 / A + u ^ 0 / A ^ 2) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = (u ^ 1 * Real.exp (-(w.re * u))) / A + (u ^ 0 * Real.exp (-(w.re * u))) / A ^ 2 := by
          ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (lin_mul_exp_integrableOn hw) hlim
  rw [h, hΦ]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_div, zero_add,
    one_mul, neg_neg, zero_sub]

theorem rampR1_mul_exp_integrable {w : ℂ} (hw : 0 < w.re) (c : ℝ) :
    Integrable (fun v : ℝ => (rampR1 c v : ℂ) * Complex.exp (w * v)) := by
  have hbase : Integrable (fun u : ℝ => ((max u 0 : ℝ) : ℂ) * Complex.exp (-(w * u))) := by
    have hI := lin_mul_exp_integrableOn hw
    have h2 : IntegrableOn (fun u : ℝ => ((max u 0 : ℝ) : ℂ) * Complex.exp (-(w * u)))
        (Ioi 0) := by
      refine hI.congr_fun (fun u hu => ?_) measurableSet_Ioi
      have : max u 0 = u := max_eq_left (le_of_lt hu)
      simp [this]
    exact h2.integrable_of_forall_notMem_eq_zero (fun u hu => by
      have : u ≤ 0 := not_lt.mp hu
      simp [max_eq_right this])
  have h := (hbase.comp_sub_left c).const_mul (Complex.exp (w * c))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [rampR1]
  push_cast
  have hexp : Complex.exp (w * c) * Complex.exp (-(w * ((c : ℂ) - v))) = Complex.exp (w * v) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc Complex.exp (w * c) * (((max (c - v) 0 : ℝ) : ℂ) * Complex.exp (-(w * ((c : ℂ) - v))))
      = ((max (c - v) 0 : ℝ) : ℂ)
          * (Complex.exp (w * c) * Complex.exp (-(w * ((c : ℂ) - v)))) := by
        ring
    _ = _ := by rw [hexp]

/-- **The right linear ramp's transform**: `∫ (c−v)₊ e^{wv} dv = e^{wc}/w²` for `Re w > 0`. -/
theorem rampR1_laplace {w : ℂ} (hw : 0 < w.re) (c : ℝ) :
    ∫ v : ℝ, (rampR1 c v : ℂ) * Complex.exp (w * v) = Complex.exp (w * c) / w ^ 2 := by
  rw [← integral_sub_left_eq_self (fun v : ℝ => (rampR1 c v : ℂ) * Complex.exp (w * v)) volume c]
  have hfun : (fun u : ℝ => (rampR1 c (c - u) : ℂ) * Complex.exp (w * ((c - u : ℝ) : ℂ)))
      = fun u : ℝ => Complex.exp (w * c) * (((max u 0 : ℝ) : ℂ) * Complex.exp (-(w * u))) := by
    funext u
    simp only [rampR1, sub_sub_cancel]
    push_cast
    have hexp : Complex.exp (w * ((c : ℂ) - u)) = Complex.exp (w * c) * Complex.exp (-(w * u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hexp]
    ring
  rw [hfun, integral_const_mul]
  have hres : ∫ u : ℝ, ((max u 0 : ℝ) : ℂ) * Complex.exp (-(w * u))
      = ∫ u in Ioi (0 : ℝ), (u : ℂ) * Complex.exp (-(w * u)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun u hu => by
      have : u ≤ 0 := not_lt.mp hu
      simp [max_eq_right this])]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
      have : max u 0 = u := max_eq_left (le_of_lt hu)
      simp [this])
  rw [hres, integral_lin_mul_exp_neg hw]
  ring

/-- **The left linear ramp's transform**: `∫ (v−c)₊ e^{wv} dv = e^{wc}/w²` for `Re w < 0`. -/
theorem rampL1_laplace {w : ℂ} (hw : w.re < 0) (c : ℝ) :
    ∫ v : ℝ, (rampL1 c v : ℂ) * Complex.exp (w * v) = Complex.exp (w * c) / w ^ 2 := by
  have hw' : 0 < (-w).re := by simp; linarith
  have h := rampR1_laplace hw' (-c)
  rw [← integral_neg_eq_self (fun v : ℝ => (rampL1 c v : ℂ) * Complex.exp (w * v)) volume]
  have hfun : (fun v : ℝ => (rampL1 c (-v) : ℂ) * Complex.exp (w * ((-v : ℝ) : ℂ)))
      = fun v : ℝ => (rampR1 (-c) v : ℂ) * Complex.exp ((-w) * v) := by
    funext v
    rw [rampL1_neg]
    congr 1
    congr 1
    push_cast
    ring
  rw [hfun, h]
  have e1 : (-w) * ((-c : ℝ) : ℂ) = w * c := by push_cast; ring
  have e2 : (-w) ^ 2 = w ^ 2 := by ring
  rw [e1, e2]

theorem rampL1_mul_exp_integrable {w : ℂ} (hw : w.re < 0) (c : ℝ) :
    Integrable (fun v : ℝ => (rampL1 c v : ℂ) * Complex.exp (w * v)) := by
  have hw' : 0 < (-w).re := by simp; linarith
  have h := (rampR1_mul_exp_integrable hw' (-c)).comp_neg
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [← rampL1_neg, neg_neg]
  congr 1
  congr 1
  push_cast
  ring

/-- **Selberg's weight `Λ_x`** in the log variable: `1` for `v ≤ L`, `(2L − v)/L` on `[L, 2L]`,
`0` beyond. -/
def linProfile (L v : ℝ) : ℝ := (rampR1 (2 * L) v - rampR1 L v) / L

/-- The reflected profile (supported on `v ≥ L`), the kernel's transform left of the pole. -/
def linProfileLeft (L v : ℝ) : ℝ := (rampL1 (2 * L) v - rampL1 L v) / L

theorem linProfile_continuous (L : ℝ) : Continuous (linProfile L) := by
  unfold linProfile
  have := rampR1_continuous
  fun_prop

theorem linProfileLeft_continuous (L : ℝ) : Continuous (linProfileLeft L) := by
  unfold linProfileLeft
  have := rampL1_continuous
  fun_prop

/-- **Sharp front**: the weight is exactly `1` up to the front. -/
theorem linProfile_eq_one {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : v ≤ L) : linProfile L v = 1 := by
  unfold linProfile
  rw [rampR1_eq_of_le (by linarith), rampR1_eq_of_le hv]
  have hL0 : L ≠ 0 := hL.ne'
  field_simp
  ring

/-- **The taper**: `(2L − v)/L = log(x²/n)/log x` on `[L, 2L]`. -/
theorem linProfile_eq_taper {L : ℝ} (_hL : 0 < L) {v : ℝ} (hv1 : L ≤ v) (hv2 : v ≤ 2 * L) :
    linProfile L v = (2 * L - v) / L := by
  unfold linProfile
  rw [rampR1_eq_of_le hv2, rampR1_eq_zero_of_ge hv1]
  ring

theorem linProfile_eq_zero {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : 2 * L ≤ v) :
    linProfile L v = 0 := by
  unfold linProfile
  rw [rampR1_eq_zero_of_ge hv, rampR1_eq_zero_of_ge (by linarith)]
  simp

theorem linProfileLeft_eq_zero {L : ℝ} (hL : 0 < L) {v : ℝ} (hv : v ≤ L) :
    linProfileLeft L v = 0 := by
  unfold linProfileLeft
  rw [rampL1_eq_zero_of_le (by linarith), rampL1_eq_zero_of_le hv]
  simp

theorem linProfile_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun v : ℝ => (linProfile L v : ℂ) * Complex.exp (w * v)) := by
  have i2 := rampR1_mul_exp_integrable hw (2 * L)
  have i1 := rampR1_mul_exp_integrable hw L
  have h := (i2.sub i1).const_mul (1 / (L : ℂ))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [linProfile, Pi.sub_apply]
  push_cast
  ring

theorem linProfileLeft_mul_exp_integrable {L : ℝ} {w : ℂ} (hw : w.re < 0) :
    Integrable (fun v : ℝ => (linProfileLeft L v : ℂ) * Complex.exp (w * v)) := by
  have i2 := rampL1_mul_exp_integrable hw (2 * L)
  have i1 := rampL1_mul_exp_integrable hw L
  have h := (i2.sub i1).const_mul (1 / (L : ℂ))
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [linProfileLeft, Pi.sub_apply]
  push_cast
  ring

/-- **Selberg's kernel is the Laplace transform of `Λ_x`** right of the pole. -/
theorem linKernel_eq_laplace_right {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    linKernel L w = ∫ v : ℝ, (linProfile L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i2 := rampR1_mul_exp_integrable hw (2 * L)
  have i1 := rampR1_mul_exp_integrable hw L
  have hfun : (fun v : ℝ => (linProfile L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (L : ℂ)) * ((rampR1 (2 * L) v : ℂ) * Complex.exp (w * v)
          - (rampR1 L v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [linProfile]
    push_cast
    ring
  rw [hfun, integral_const_mul, integral_sub i2 i1, rampR1_laplace hw, rampR1_laplace hw,
    linKernel_eq hL0 hw0]
  have e2 : Complex.exp (w * ((2 * L : ℝ) : ℂ)) = Complex.exp (2 * L * w) := by
    congr 1; push_cast; ring
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  rw [e2, e1]
  field_simp

/-- **Selberg's kernel is the Laplace transform of the reflected profile** left of the pole. -/
theorem linKernel_eq_laplace_left {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : w.re < 0) :
    linKernel L w = ∫ v : ℝ, (linProfileLeft L v : ℂ) * Complex.exp (w * v) := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hL0 : L ≠ 0 := hL.ne'
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0
  have i2 := rampL1_mul_exp_integrable hw (2 * L)
  have i1 := rampL1_mul_exp_integrable hw L
  have hfun : (fun v : ℝ => (linProfileLeft L v : ℂ) * Complex.exp (w * v))
      = fun v : ℝ => (1 / (L : ℂ)) * ((rampL1 (2 * L) v : ℂ) * Complex.exp (w * v)
          - (rampL1 L v : ℂ) * Complex.exp (w * v)) := by
    funext v
    simp only [linProfileLeft]
    push_cast
    ring
  rw [hfun, integral_const_mul, integral_sub i2 i1, rampL1_laplace hw, rampL1_laplace hw,
    linKernel_eq hL0 hw0]
  have e2 : Complex.exp (w * ((2 * L : ℝ) : ℂ)) = Complex.exp (2 * L * w) := by
    congr 1; push_cast; ring
  have e1 : Complex.exp (w * (L : ℂ)) = Complex.exp (L * w) := by
    congr 1; ring
  rw [e2, e1]
  field_simp

/-- The right prime line: `∫ K₁(b+it−s₀) term_n(b+it) dt = 2π · Λ_x(n) · Λ(n) n^{−s₀}`. -/
theorem linKernel_prime_line_right {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {b : ℝ} (hb : s₀.re < b)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => linKernel L (s - s₀)) b C 2) (n : ℕ) :
    ∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n
      = 2 * π * ((linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set w₀ : ℂ := (b : ℂ) - s₀ with hw₀
  have hw₀re : 0 < w₀.re := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (linProfile L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (linProfile_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := linProfile_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => linKernel L ((b : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : (0 : ℝ) < ((b : ℂ) + t * I - s₀).re := by simp; linarith
    show linKernel L ((b : ℂ) + t * I - s₀) = _
    rw [linKernel_eq_laplace_right hL hw]
    congr 1
    funext v
    rw [hφ]
    show (linProfile L v : ℂ) * Complex.exp (((b : ℂ) + t * I - s₀) * v)
      = (linProfile L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => linKernel L (s - s₀))
      (linKernel_line_continuous L (by linarith : b ≠ s₀.re)) (le_refl 2) hC hdec
  have hfun : (fun t : ℝ => linKernel L ((b : ℂ) + t * I - s₀)
        * LSeries.term vonMangoldtC ((b : ℂ) + t * I) n)
      = fun t : ℝ => (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
          * (Φ t * Complex.exp (-(I * t * Real.log n))) := by
    funext t
    rw [term_line_eq b t hn, hΦdef]
    ring
  rw [hfun, integral_const_mul, line_transform_inversion hφc hφi hΦ hΦi (Real.log n)]
  rw [hφ]
  show (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((n : ℝ) ^ (-b) : ℝ) : ℂ))
      * (2 * π * ((linProfile L (Real.log n) : ℂ) * Complex.exp (w₀ * Real.log n)))
    = 2 * π * ((linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n)
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
    (2 * (π : ℂ) * (linProfile L (Real.log n) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      * hpow

/-- The left prime line vanishes: the reflected profile is supported above the front. -/
theorem linKernel_prime_line_left {L : ℝ} (hL : 0 < L) {s₀ : ℂ} {a : ℝ} (ha : a < s₀.re)
    {C : ℝ} (hC : 0 ≤ C) (hdec : LineDecay (fun s => linKernel L (s - s₀)) a C 2) (n : ℕ) :
    ∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀)
      * LSeries.term vonMangoldtC (1 - ((a : ℂ) + t * I)) n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set w₀ : ℂ := (a : ℂ) - s₀ with hw₀
  have hw₀re : w₀.re < 0 := by rw [hw₀]; simp; linarith
  set φ : ℝ → ℂ := fun v => (linProfileLeft L v : ℂ) * Complex.exp (w₀ * v) with hφ
  have hφc : Continuous φ := by
    rw [hφ]
    exact (Complex.continuous_ofReal.comp (linProfileLeft_continuous L)).mul (by fun_prop)
  have hφi : Integrable φ := linProfileLeft_mul_exp_integrable hw₀re
  set Φ : ℝ → ℂ := fun t => linKernel L ((a : ℂ) + t * I - s₀) with hΦdef
  have hΦ : ∀ t : ℝ, Φ t = ∫ v : ℝ, φ v * Complex.exp (I * t * v) := by
    intro t
    rw [hΦdef]
    have hw : ((a : ℂ) + t * I - s₀).re < 0 := by simp; linarith
    show linKernel L ((a : ℂ) + t * I - s₀) = _
    rw [linKernel_eq_laplace_left hL hw]
    congr 1
    funext v
    rw [hφ]
    show (linProfileLeft L v : ℂ) * Complex.exp (((a : ℂ) + t * I - s₀) * v)
      = (linProfileLeft L v : ℂ) * Complex.exp (w₀ * v) * Complex.exp (I * t * v)
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    rw [hw₀]
    ring
  have hΦi : Integrable Φ :=
    integrable_line_of_decay' (F := fun s => linKernel L (s - s₀))
      (linKernel_line_continuous L (by linarith : a ≠ s₀.re)) (le_refl 2) hC hdec
  have hrefl : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)) = (((1 - a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    push_cast
    ring
  have hfun : (fun t : ℝ => linKernel L ((a : ℂ) + t * I - s₀)
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
      * (2 * π * ((linProfileLeft L (-Real.log n) : ℂ)
          * Complex.exp (w₀ * ((-Real.log n : ℝ) : ℂ))))
    = 0
  rw [linProfileLeft_eq_zero hL (by linarith : -Real.log n ≤ L)]
  simp

/-! ## 9. The truncated explicit formula, Selberg's taper -/

/-- **The truncated explicit formula at the growth front `x = e^L`, Selberg's linear taper.**
For `s₀` off the zero set with `a < Re s₀ < b` (`a < 0 < 1 < b`):

  `ξ′/ξ(s₀) + Σ'_ρ m_ρ K₁(ρ − s₀)
     = (1/2π)[∫ K₁(b+it−s₀) E(b+it) dt + ∫ K₁(a+it−s₀) E(1−a−it) dt]
       − Σ_n Λ_x(n) · Λ(n) n^{−s₀}`,

with `K₁(w) = (x^{2w} − x^{w})/(w² L)`, `Λ_x(n) = linProfile L (log n)` (exactly `1` for `n ≤ x`,
`log(x²/n)/log x` for `x ≤ n ≤ x²`, `0` beyond), `E = weilArch`. The pole of `E` at `s = 1`
inside the strip carries the END term `K₁(1 − s₀) = (x^{2(1−s₀)} − x^{1−s₀})/((1−s₀)² L)`. -/
theorem truncated_explicit_formula_selberg {L : ℝ} (hL : 0 < L) {s₀ : ℂ}
    (hs₀ : s₀ ∉ ZD.NontrivialZeros) {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hs₀a : a < s₀.re)
    (hs₀b : s₀.re < b) :
    logDeriv ZD.riemannXi s₀ + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀)
      = (1 / (2 * π)) * ((∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
          + (∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, (linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
  have hab : a ≤ b := by linarith
  obtain ⟨C, hC, hdecl⟩ := linKernel_line_decay hL hab hs₀a hs₀b
  have hFc : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Continuous (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)) := by
    intro σ hσ
    apply linKernel_line_continuous
    rcases hσ with rfl | rfl <;> linarith
  have hFint : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)) :=
    fun σ hσ => integrable_line_of_decay' (F := fun s => linKernel L (s - s₀)) (hFc σ hσ)
      (le_refl 2) hC (hdecl σ hσ)
  obtain ⟨-, hzero⟩ := stripBoundary_linKernel_mul_logDeriv_xi hL hs₀ ha hb hs₀a hs₀b
  have hlineInt : ∀ σ : ℝ, (σ = a ∨ σ = b) →
      Integrable (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)
        * logDeriv ZD.riemannXi (σ + t * I)) := by
    intro σ hσ
    obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
    have hpt : ∀ t : ℝ, linKernel L ((σ : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (σ + t * I)
        = A * linKernel L ((σ : ℂ) + t * I - s₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => linKernel L (s - s₀)) σ ρ t := by
      intro t
      rw [logDeriv_apply, hA _ (line_not_zero ha hb hσ t)]
      unfold hadamardLineTerm hadamardTerm
      rw [mul_add, ← tsum_mul_left]
      congr 1
      ring
    have hfun : (fun t : ℝ => linKernel L ((σ : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (σ + t * I))
        = fun t : ℝ => A * linKernel L ((σ : ℂ) + t * I - s₀)
          + ∑' ρ : Zero, hadamardLineTerm (fun s => linKernel L (s - s₀)) σ ρ t := funext hpt
    rw [hfun]
    exact ((hFint σ hσ).const_mul A).add (integrable_tsum_of_summable_integral_norm
      (fun ρ => lin_hadamardLineTerm_integrable hC ha hb hσ (hFc σ hσ) (hdecl σ hσ) ρ)
      (lin_summable_hadamardLineTerm_integral_norm hC ha hb hσ (hdecl σ hσ)))
  -- the right line
  have hθb : Continuous (fun t : ℝ => (b : ℂ) + t * I) := by fun_prop
  have hreb : ∀ t : ℝ, ((b : ℂ) + t * I).re = b := by intro t; simp
  have hLb : lineIntegral (fun s => linKernel L (s - s₀) * logDeriv ZD.riemannXi s) b
      = (∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I))
        - 2 * π * ∑' n : ℕ, (linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (b + t * I)
        = linKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
          - linKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) := by
      intro t
      rw [logDeriv_xi_eq_arch_sub_lseries (by rw [hreb]; exact hb)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        linKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I)) :=
      lseries_line_integrable (hFint b (Or.inr rfl)) hθb hreb hb
    have hAint : Integrable (fun t : ℝ =>
        linKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)) := by
      have h := (hlineInt b (Or.inr rfl)).add hLint
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.add_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => linKernel L ((b : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (b + t * I))
        = fun t : ℝ => linKernel L ((b : ℂ) + t * I - s₀) * weilArch (b + t * I)
            - linKernel L ((b : ℂ) + t * I - s₀) * LSeries vonMangoldtC (b + t * I) :=
      funext hpt
    rw [hfun, integral_sub hAint hLint,
      lseries_line_exchange (hFint b (Or.inr rfl)) hθb hreb hb,
      tsum_congr (linKernel_prime_line_right hL hs₀b hC (hdecl b (Or.inr rfl))), tsum_mul_left]
  -- the left line
  have hθa : Continuous (fun t : ℝ => 1 - ((a : ℂ) + t * I)) := by fun_prop
  have hrea : ∀ t : ℝ, (1 - ((a : ℂ) + t * I)).re = 1 - a := by intro t; simp
  have h1a : 1 < 1 - a := by linarith
  have hLa : lineIntegral (fun s => linKernel L (s - s₀) * logDeriv ZD.riemannXi s) a
      = -(∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
    unfold lineIntegral
    beta_reduce
    have hpt : ∀ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * logDeriv ZD.riemannXi (a + t * I)
        = -(linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
          + linKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) := by
      intro t
      rw [logDeriv_xi_reflect, logDeriv_xi_eq_arch_sub_lseries (by rw [hrea]; exact h1a)]
      ring
    have hLint : Integrable (fun t : ℝ =>
        linKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I))) :=
      lseries_line_integrable (hFint a (Or.inl rfl)) hθa hrea h1a
    have hAint : Integrable (fun t : ℝ =>
        linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))) := by
      have h := hLint.sub (hlineInt a (Or.inl rfl))
      refine h.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      rw [hpt t]
      ring
    have hfun : (fun t : ℝ => linKernel L ((a : ℂ) + t * I - s₀)
          * logDeriv ZD.riemannXi (a + t * I))
        = fun t : ℝ => -(linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))
            + linKernel L ((a : ℂ) + t * I - s₀) * LSeries vonMangoldtC (1 - ((a : ℂ) + t * I)) :=
      funext hpt
    have hAint' : Integrable (fun t : ℝ =>
        -(linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I)))) := hAint.neg
    rw [hfun, integral_add hAint' hLint, integral_neg,
      lseries_line_exchange (hFint a (Or.inl rfl)) hθa hrea h1a,
      tsum_congr (linKernel_prime_line_left hL hs₀a hC (hdecl a (Or.inl rfl))), tsum_zero,
      add_zero]
  -- assemble
  unfold stripBoundary at hzero
  rw [hLb, hLa] at hzero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set S := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * linKernel L (ρ.val - s₀) with hS
  set X := logDeriv ZD.riemannXi s₀ with hX
  set Ab := ∫ t : ℝ, linKernel L ((b : ℂ) + t * I - s₀) * weilArch ((b : ℂ) + t * I) with hAb
  set Aa := ∫ t : ℝ, linKernel L ((a : ℂ) + t * I - s₀) * weilArch (1 - ((a : ℂ) + t * I))
    with hAa
  set P := ∑' n : ℕ, (linProfile L (Real.log n) : ℂ) * LSeries.term vonMangoldtC s₀ n with hP
  have h2πS : 2 * (π : ℂ) * (X + S) = (Ab + Aa) - 2 * π * P := by
    linear_combination I * hzero + (2 * π * (X + S) - Ab - Aa + 2 * π * P) * Complex.I_sq
  have hS' : X + S = (Ab + Aa) / (2 * π) - P := by
    rw [eq_sub_iff_add_eq, eq_div_iff h2π]
    linear_combination h2πS
  rw [hS']
  ring

/-- The front is sharp: `Λ_x(n) = 1` exactly for `n ≤ x = e^L`. -/
theorem linProfile_log_eq_one {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n)
    (hx : (n : ℝ) ≤ Real.exp L) : linProfile L (Real.log n) = 1 := by
  apply linProfile_eq_one hL
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.log n ≤ Real.log (Real.exp L) := Real.log_le_log hnr hx
    _ = L := Real.log_exp L

/-- The taper ends: `Λ_x(n) = 0` exactly for `n ≥ x² = e^{2L}`. -/
theorem linProfile_log_eq_zero {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hx : Real.exp (2 * L) ≤ n) : linProfile L (Real.log n) = 0 := by
  apply linProfile_eq_zero hL
  have hpos : (0 : ℝ) < Real.exp (2 * L) := Real.exp_pos _
  calc 2 * L = Real.log (Real.exp (2 * L)) := (Real.log_exp _).symm
    _ ≤ Real.log n := Real.log_le_log hpos hx

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.truncated_explicit_formula_selberg
#print axioms CriticalLinePhasor.ContourArgument.summable_logWeight_nontrivialZeros
#print axioms CriticalLinePhasor.ContourArgument.integral_inv_mul_inv_le
#print axioms CriticalLinePhasor.ContourArgument.stripBoundary_div_sub_eq₁
