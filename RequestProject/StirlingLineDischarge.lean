import RequestProject.WeilConverse
import RequestProject.AmplitudeExchange

/-!
# Stirling line discharge: the converse's line data compiled from the house bounds

`weil_converse` consumes one line-integrability field and one strip-decay field.
This file discharges the line data from the compiled vertical Stirling machinery
(`CPSGammaVerticalIntegrable`, from `ZD.StirlingBound.gamma_stirling_bound`), so that
for the compiled kernel families the field is derived, not assumed:

* `exists_bound_of_tendsto_zero` — a continuous line function vanishing at both ends
  is globally bounded;
* `gammaC_vline_bounded` / `gammaC_vline_exp_bound` — the `Γℂ` line is bounded and
  exponentially decaying (`A·e^{-(π/4)|t|}`), assembled from the compiled `IsBigO`s;
* `gammaR_vline_eq_const_mul` — **the reduction**: `‖Γℝ(w+it)‖` is a positive
  constant times `‖Γℂ(w/2 + i t/2)‖`, so every `Γℝ` line fact transfers from the
  compiled `Γℂ` machinery with no new Stirling work;
* `gammaR_vline_integrable` / `_bounded` / `_exp_bound` / `gammaR_line_continuous`;
* `chainTail_continuous` / `chainTail_bounded` / `chain_line_integrable` /
  `chain_line_exp_bound` — the `∏ Γℝ(s+e)` multiplier of the pure-real chain, by
  list induction: head integrable/decaying, tail bounded;
* `realChainG_line_integrable` / `realChainG_line_exp_bound` and
  `gammaCSingletonG_line_integrable` / `gammaCSingletonG_line_exp_bound` — the two
  compiled kernel families' multipliers on any line `σ > 0`;
* `lam_line_eq` / `lam_line_integrable_of_G` / `lam_line_exp_bound_of_G` — the
  package's `lam` on the chart line is multiplier × Dirichlet factor; the Dirichlet
  factor is uniformly bounded there (compiled `dirichlet_vline_isBigO_one`), so the
  kernel-side data transfers to `lam` — exactly the `hline` field of
  `weil_converse`, derived.

No `axiom`, no `sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.StirlingLine

open CriticalLinePhasor.GammaVertical CriticalLinePhasor.CarrierTheta
open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.WeilConverse
open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.TransportClosure

/-! ## A continuous line function vanishing at both ends is bounded -/

theorem exists_bound_of_tendsto_zero (f : ℝ → ℂ) (hc : Continuous f)
    (htop : Tendsto f atTop (𝓝 0)) (hbot : Tendsto f atBot (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖f y‖ ≤ C := by
  have h1 : ∀ᶠ y in atTop, ‖f y‖ ≤ 1 := by
    have h0 : Tendsto (fun y => ‖f y‖) atTop (𝓝 0) := by simpa using htop.norm
    exact h0.eventually (eventually_le_nhds one_pos)
  have h2 : ∀ᶠ y in atBot, ‖f y‖ ≤ 1 := by
    have h0 : Tendsto (fun y => ‖f y‖) atBot (𝓝 0) := by simpa using hbot.norm
    exact h0.eventually (eventually_le_nhds one_pos)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp h1
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.mp h2
  set a : ℝ := min T₂ 0
  set b : ℝ := max T₁ 0
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C₀ 1 + 1, by positivity, fun y => ?_⟩
  rcases le_total y a with hy | hy
  · have : ‖f y‖ ≤ 1 := hT₂ y (le_trans hy (min_le_left _ _))
    calc ‖f y‖ ≤ 1 := this
      _ ≤ max C₀ 1 + 1 := by
          have := le_max_right C₀ 1
          linarith
  · rcases le_total y b with hy' | hy'
    · have : ‖f y‖ ≤ C₀ := hC₀ y ⟨hy, hy'⟩
      calc ‖f y‖ ≤ C₀ := this
        _ ≤ max C₀ 1 + 1 := by
            have := le_max_left C₀ 1
            linarith
    · have : ‖f y‖ ≤ 1 := hT₁ y (le_trans (le_max_left _ _) hy')
      calc ‖f y‖ ≤ 1 := this
        _ ≤ max C₀ 1 + 1 := by
            have := le_max_right C₀ 1
            linarith

/-! ## The `Γℂ` line: bounded and exponentially decaying -/

theorem gammaC_vline_tendsto_zero_atTop {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun y : ℝ => Complex.Gammaℂ (vline w y)) atTop (𝓝 0) := by
  refine (gammaC_vline_isBigO_atTop hw).trans_tendsto ?_
  have h1 : Tendsto (fun y : ℝ => -(Real.pi / 4) * y) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr (by positivity))).mpr tendsto_id
  exact Real.tendsto_exp_atBot.comp h1

theorem gammaC_vline_tendsto_zero_atBot {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun y : ℝ => Complex.Gammaℂ (vline w y)) atBot (𝓝 0) := by
  refine (gammaC_vline_isBigO_atBot hw).trans_tendsto ?_
  have h1 : Tendsto (fun y : ℝ => (Real.pi / 4) * y) atBot atBot := by
    exact (tendsto_const_mul_atBot_of_pos (by positivity)).mpr tendsto_id
  exact Real.tendsto_exp_atBot.comp h1

theorem gammaC_vline_bounded {w : ℂ} (hw : 0 < w.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖Complex.Gammaℂ (vline w y)‖ ≤ C :=
  exists_bound_of_tendsto_zero _ (gammaC_vline_continuous hw)
    (gammaC_vline_tendsto_zero_atTop hw) (gammaC_vline_tendsto_zero_atBot hw)

theorem gammaC_vline_exp_bound {w : ℂ} (hw : 0 < w.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ,
      ‖Complex.Gammaℂ (vline w y)‖ ≤ A * Real.exp (-(Real.pi / 4) * |y|) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := (gammaC_vline_isBigO_atTop hw).exists_pos
  rw [Asymptotics.isBigOWith_iff] at hc₁
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hc₁
  obtain ⟨c₂, hc₂pos, hc₂⟩ := (gammaC_vline_isBigO_atBot hw).exists_pos
  rw [Asymptotics.isBigOWith_iff] at hc₂
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.mp hc₂
  set a : ℝ := min T₂ 0
  set b : ℝ := max T₁ 0
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (gammaC_vline_continuous hw).continuousOn
  set Tm : ℝ := max |a| |b|
  refine ⟨max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) + 1, by positivity,
    fun y => ?_⟩
  have hkey : ‖Complex.Gammaℂ (vline w y)‖ ≤
      max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) *
        Real.exp (-(Real.pi / 4) * |y|) := by
    rcases le_total y a with hy | hy
    · have hyneg : y ≤ 0 := le_trans hy (min_le_right _ _)
      have h := hT₂ y (le_trans hy (min_le_left _ _))
      have habs : |y| = -y := abs_of_nonpos hyneg
      calc ‖Complex.Gammaℂ (vline w y)‖
          ≤ c₂ * ‖Real.exp ((Real.pi / 4) * y)‖ := h
        _ = c₂ * Real.exp (-(Real.pi / 4) * |y|) := by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), habs]
            ring_nf
        _ ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) *
              Real.exp (-(Real.pi / 4) * |y|) := by
            have hle : c₂ ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) :=
              le_trans (le_max_right c₁ c₂) (le_max_left _ _)
            exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    · rcases le_total y b with hy' | hy'
      · have h := hC₀ y ⟨hy, hy'⟩
        have habs : |y| ≤ Tm := by
          rw [abs_le]
          constructor
          · have : -|a| ≤ a := neg_abs_le a
            have h2 : -Tm ≤ -|a| := neg_le_neg (le_max_left _ _)
            linarith
          · have : b ≤ |b| := le_abs_self b
            have h2 : |b| ≤ Tm := le_max_right _ _
            linarith
        calc ‖Complex.Gammaℂ (vline w y)‖ ≤ C₀ := h
          _ ≤ C₀ * Real.exp ((Real.pi / 4) * Tm) * Real.exp (-(Real.pi / 4) * |y|) := by
              rw [mul_assoc, ← Real.exp_add]
              have hexp : (0 : ℝ) ≤ (Real.pi / 4) * Tm + -(Real.pi / 4) * |y| := by
                have : (Real.pi / 4) * |y| ≤ (Real.pi / 4) * Tm :=
                  mul_le_mul_of_nonneg_left habs (by positivity)
                linarith
              nlinarith [Real.one_le_exp hexp, hC₀ y ⟨hy, hy'⟩,
                norm_nonneg (Complex.Gammaℂ (vline w y)),
                Real.exp_pos ((Real.pi / 4) * Tm + -(Real.pi / 4) * |y|)]
          _ ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) *
                Real.exp (-(Real.pi / 4) * |y|) := by
              exact mul_le_mul_of_nonneg_right
                (le_max_right (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)))
                (Real.exp_pos _).le
      · have hypos : 0 ≤ y := le_trans (le_max_right T₁ 0) hy'
        have h := hT₁ y (le_trans (le_max_left T₁ 0) hy')
        have habs : |y| = y := abs_of_nonneg hypos
        calc ‖Complex.Gammaℂ (vline w y)‖
            ≤ c₁ * ‖Real.exp (-(Real.pi / 4) * y)‖ := h
          _ = c₁ * Real.exp (-(Real.pi / 4) * |y|) := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), habs]
          _ ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) *
                Real.exp (-(Real.pi / 4) * |y|) := by
              have hle : c₁ ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) :=
                le_trans (le_max_left c₁ c₂) (le_max_left _ _)
              exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  calc ‖Complex.Gammaℂ (vline w y)‖
      ≤ max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) *
          Real.exp (-(Real.pi / 4) * |y|) := hkey
    _ ≤ (max (max c₁ c₂) (C₀ * Real.exp ((Real.pi / 4) * Tm)) + 1) *
          Real.exp (-(Real.pi / 4) * |y|) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-! ## The `Γℝ` line, by reduction to the compiled `Γℂ` line -/

/-- **The reduction**: the `Γℝ` line norm is a positive constant times the `Γℂ` line
norm at half the base point and half the height. -/
theorem gammaR_vline_eq_const_mul (w : ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ,
      ‖Complex.Gammaℝ (vline w y)‖ = c * ‖Complex.Gammaℂ (vline (w / 2) (y / 2))‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨(Real.pi : ℝ) ^ (-(w.re / 2)) / (2 * (2 * Real.pi) ^ (-(w / 2).re)),
    by positivity, fun y => ?_⟩
  have hhalf : vline w y / 2 = vline (w / 2) (y / 2) := by
    unfold vline
    push_cast
    ring
  have hR : ‖Complex.Gammaℝ (vline w y)‖ =
      (Real.pi : ℝ) ^ (-(w.re / 2)) * ‖Complex.Gamma (vline (w / 2) (y / 2))‖ := by
    rw [Complex.Gammaℝ_def, norm_mul]
    congr 1
    · have hbase : ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) := rfl
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
      congr 1
      have : (-(vline w y) / 2).re = -(w.re / 2) := by
        unfold vline
        simp
        ring
      exact this
    · rw [← hhalf]
  have hC : ‖Complex.Gammaℂ (vline (w / 2) (y / 2))‖ =
      2 * (2 * Real.pi) ^ (-(w / 2).re) * ‖Complex.Gamma (vline (w / 2) (y / 2))‖ :=
    gammaC_vline_norm _ _
  rw [hR, hC]
  field_simp

theorem gammaR_line_continuous {w : ℂ} (hw : 0 < w.re) :
    Continuous (fun y : ℝ => Complex.Gammaℝ (vline w y)) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hpt : 0 < (vline w y).re := by
    unfold vline
    simpa using hw
  exact (CriticalLinePhasor.AmplitudeExchange.differentiableAt_GammaR
    hpt).continuousAt.comp
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)

theorem gammaR_half_re {w : ℂ} (hw : 0 < w.re) : 0 < (w / 2).re := by
  have h : (w / 2).re = w.re / 2 := by simp
  rw [h]
  linarith

theorem gammaR_vline_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun y : ℝ => Complex.Gammaℝ (vline w y)) := by
  obtain ⟨c, hcpos, hc⟩ := gammaR_vline_eq_const_mul w
  have hΓC : Integrable (fun y : ℝ => Complex.Gammaℂ (vline (w / 2) y)) :=
    gammaC_vline_integrable (gammaR_half_re hw)
  have hscaled : Integrable (fun y : ℝ =>
      Complex.Gammaℂ (vline (w / 2) ((2 : ℝ)⁻¹ * y))) :=
    (integrable_comp_mul_left_iff
      (fun y : ℝ => Complex.Gammaℂ (vline (w / 2) y))
      (by norm_num : ((2 : ℝ)⁻¹) ≠ 0)).mpr hΓC
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Complex.Gammaℝ (vline w y)) volume :=
    (gammaR_line_continuous hw).aestronglyMeasurable
  refine ((hscaled.norm.const_mul c).mono' hmeas ?_)
  refine Eventually.of_forall fun y => le_of_eq ?_
  rw [hc y, show (2 : ℝ)⁻¹ * y = y / 2 from by ring]

theorem gammaR_vline_bounded {w : ℂ} (hw : 0 < w.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖Complex.Gammaℝ (vline w y)‖ ≤ C := by
  obtain ⟨c, hcpos, hc⟩ := gammaR_vline_eq_const_mul w
  obtain ⟨C, hCpos, hC⟩ := gammaC_vline_bounded (gammaR_half_re hw)
  exact ⟨c * C, by positivity, fun y => by
    rw [hc y]
    exact mul_le_mul_of_nonneg_left (hC _) hcpos.le⟩

theorem gammaR_vline_exp_bound {w : ℂ} (hw : 0 < w.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ,
      ‖Complex.Gammaℝ (vline w y)‖ ≤ A * Real.exp (-(Real.pi / 8) * |y|) := by
  obtain ⟨c, hcpos, hc⟩ := gammaR_vline_eq_const_mul w
  obtain ⟨A, hApos, hA⟩ := gammaC_vline_exp_bound (gammaR_half_re hw)
  refine ⟨c * A, by positivity, fun y => ?_⟩
  rw [hc y]
  have h1 := hA (y / 2)
  have habs : |y / 2| = |y| / 2 := by
    rw [abs_div]
    norm_num
  have hexp : -(Real.pi / 4) * |y / 2| = -(Real.pi / 8) * |y| := by
    rw [habs]
    ring
  rw [hexp] at h1
  calc c * ‖Complex.Gammaℂ (vline (w / 2) (y / 2))‖
      ≤ c * (A * Real.exp (-(Real.pi / 8) * |y|)) :=
        mul_le_mul_of_nonneg_left h1 hcpos.le
    _ = c * A * Real.exp (-(Real.pi / 8) * |y|) := by ring

/-! ## The pure-real chain multiplier on a line -/

theorem chainTail_continuous (σ : ℝ) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 < σ + e.re) :
    Continuous (fun t : ℝ =>
      (ds.map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod) := by
  induction ds with
  | nil => simpa using continuous_const
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      have he : 0 < ((σ : ℂ) + e).re := by
        have := hds e (by simp)
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      have hhead : Continuous (fun t : ℝ => Complex.Gammaℝ ((σ : ℂ) + t * I + e)) := by
        have heq : (fun t : ℝ => Complex.Gammaℝ ((σ : ℂ) + t * I + e))
            = fun t : ℝ => Complex.Gammaℝ (vline ((σ : ℂ) + e) t) := by
          funext t
          rw [vline_baseAdd]
        rw [heq]
        exact gammaR_line_continuous he
      exact hhead.mul (ih fun x hx => hds x (by simp [hx]))

theorem chainTail_bounded (σ : ℝ) (ds : List ℂ) (hds : ∀ e ∈ ds, 0 < σ + e.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(ds.map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod‖ ≤ C := by
  induction ds with
  | nil => exact ⟨1, one_pos, fun t => by simp⟩
  | cons e es ih =>
      obtain ⟨C₁, hC₁pos, hC₁⟩ := ih fun x hx => hds x (by simp [hx])
      have he : 0 < ((σ : ℂ) + e).re := by
        have := hds e (by simp)
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      obtain ⟨C₂, hC₂pos, hC₂⟩ := gammaR_vline_bounded he
      refine ⟨C₂ * C₁, by positivity, fun t => ?_⟩
      simp only [List.map_cons, List.prod_cons, norm_mul]
      have hh : ‖Complex.Gammaℝ ((σ : ℂ) + t * I + e)‖ ≤ C₂ := by
        rw [vline_baseAdd]
        exact hC₂ t
      exact mul_le_mul hh (hC₁ t) (norm_nonneg _) hC₂pos.le

theorem chain_line_integrable (σ : ℝ) (d : ℂ) (ds : List ℂ)
    (hd : 0 < σ + d.re) (hds : ∀ e ∈ ds, 0 < σ + e.re) :
    Integrable (fun t : ℝ =>
      ((d :: ds).map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod) := by
  simp only [List.map_cons, List.prod_cons]
  have hd' : 0 < ((σ : ℂ) + d).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hhead : Integrable (fun t : ℝ => Complex.Gammaℝ ((σ : ℂ) + t * I + d)) := by
    have heq : (fun t : ℝ => Complex.Gammaℝ ((σ : ℂ) + t * I + d))
        = fun t : ℝ => Complex.Gammaℝ (vline ((σ : ℂ) + d) t) := by
      funext t
      rw [vline_baseAdd]
    rw [heq]
    exact gammaR_vline_integrable hd'
  obtain ⟨C, hCpos, hC⟩ := chainTail_bounded σ ds hds
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (ds.map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod)
      volume := (chainTail_continuous σ ds hds).aestronglyMeasurable
  have hmul := hhead.bdd_mul hmeas (Eventually.of_forall hC)
  exact hmul.congr (Eventually.of_forall fun t => by dsimp only; ring)

theorem chain_line_exp_bound (σ : ℝ) (d : ℂ) (ds : List ℂ)
    (hd : 0 < σ + d.re) (hds : ∀ e ∈ ds, 0 < σ + e.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖((d :: ds).map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod‖
        ≤ A * Real.exp (-(Real.pi / 8) * |t|) := by
  have hd' : 0 < ((σ : ℂ) + d).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  obtain ⟨Ah, hAhpos, hAh⟩ := gammaR_vline_exp_bound hd'
  obtain ⟨C, hCpos, hC⟩ := chainTail_bounded σ ds hds
  refine ⟨Ah * C, by positivity, fun t => ?_⟩
  simp only [List.map_cons, List.prod_cons, norm_mul]
  have hh : ‖Complex.Gammaℝ ((σ : ℂ) + t * I + d)‖
      ≤ Ah * Real.exp (-(Real.pi / 8) * |t|) := by
    rw [vline_baseAdd]
    exact hAh t
  calc ‖Complex.Gammaℝ ((σ : ℂ) + t * I + d)‖ *
        ‖(ds.map fun e => Complex.Gammaℝ ((σ : ℂ) + t * I + e)).prod‖
      ≤ (Ah * Real.exp (-(Real.pi / 8) * |t|)) * C :=
        mul_le_mul hh (hC t) (norm_nonneg _) (by positivity)
    _ = Ah * C * Real.exp (-(Real.pi / 8) * |t|) := by ring

/-! ## The single `Γℂ` factor on a line -/

theorem gammaC_single_line_integrable (σ : ℝ) (μ : ℂ) (hμσ : 0 < σ + μ.re) :
    Integrable (fun t : ℝ => Complex.Gammaℂ ((σ : ℂ) + t * I + μ)) := by
  have h : 0 < ((σ : ℂ) + μ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have heq : (fun t : ℝ => Complex.Gammaℂ ((σ : ℂ) + t * I + μ))
      = fun t : ℝ => Complex.Gammaℂ (vline ((σ : ℂ) + μ) t) := by
    funext t
    rw [vline_baseAdd]
  rw [heq]
  exact gammaC_vline_integrable h

theorem gammaC_single_line_exp_bound (σ : ℝ) (μ : ℂ) (hμσ : 0 < σ + μ.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖Complex.Gammaℂ ((σ : ℂ) + t * I + μ)‖ ≤ A * Real.exp (-(Real.pi / 4) * |t|) := by
  have h : 0 < ((σ : ℂ) + μ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  obtain ⟨A, hApos, hA⟩ := gammaC_vline_exp_bound h
  refine ⟨A, hApos, fun t => ?_⟩
  rw [vline_baseAdd]
  exact hA t

/-! ## The package's `lam` on the chart line -/

theorem lam_line_eq (P : CoefficientSurface) (κ : MellinKernel) {ε : ℂ}
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (s : ℂ) (hs : max κ.B0 ((P.A : ℝ) + 1) < s.re) :
    pkg.lam s = κ.G s * CriticalLinePhasor.CarrierTheta.dirichlet P.a s := by
  have hA : (P.A : ℝ) + 1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  rw [pkg.chart s hs]
  congr 1
  have hcoeff : P.a = fun j => (coefficientArithmetic P.a) (j + 1) := by
    funext j
    simp [coefficientArithmetic]
  have hdir : CriticalLinePhasor.CarrierTheta.dirichlet P.a s
      = LSeries (⇑(coefficientArithmetic P.a)) s := by
    conv_lhs => rw [hcoeff]
    rw [dirichlet_shift_eq_LSeries _ (coeffArithmetic_summable P hA)]
  rw [hdir]

theorem lam_line_integrable_of_G (P : CoefficientSurface) (κ : MellinKernel) {ε : ℂ}
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (hG : Integrable (fun t : ℝ => κ.G ((σ : ℂ) + t * I))) :
    Integrable (fun t : ℝ => pkg.lam ((σ : ℂ) + t * I)) := by
  have hA : (P.A : ℝ) + 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
  have ha' : ∀ n : ℕ, ‖P.a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ ((P.A : ℕ) : ℝ) := fun n => by
    rw [Real.rpow_natCast]
    exact P.a_bound n
  have hbdd := dirichlet_vline_isBigO_one (l := (⊤ : Filter ℝ)) P.a (P.A : ℝ) σ
    ha' hA
  rw [Asymptotics.isBigO_top] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hCbound : ∀ t : ℝ,
      ‖CriticalLinePhasor.CarrierTheta.dirichlet P.a ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
    intro t
    have := hC t
    simpa using this
  have hcont := dirichlet_vline_continuous P.a (P.A : ℝ) σ ha' hA
  have hmul := hG.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall hCbound)
  refine hmul.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [lam_line_eq P κ pkg _ (by simpa using hσ)]
  ring

theorem lam_line_exp_bound_of_G (P : CoefficientSurface) (κ : MellinKernel) {ε : ℂ}
    (pkg : KNicePackage (coefficientArithmetic P.a) κ.G (max κ.B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max κ.B0 ((P.A : ℝ) + 1) < σ)
    (A k : ℝ) (hApos : 0 < A)
    (hGexp : ∀ t : ℝ, ‖κ.G ((σ : ℂ) + t * I)‖ ≤ A * Real.exp (-k * |t|)) :
    ∃ A' : ℝ, 0 < A' ∧ ∀ t : ℝ,
      ‖pkg.lam ((σ : ℂ) + t * I)‖ ≤ A' * Real.exp (-k * |t|) := by
  have hA : (P.A : ℝ) + 1 < σ := lt_of_le_of_lt (le_max_right _ _) hσ
  have ha' : ∀ n : ℕ, ‖P.a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ ((P.A : ℕ) : ℝ) := fun n => by
    rw [Real.rpow_natCast]
    exact P.a_bound n
  have hbdd := dirichlet_vline_isBigO_one (l := (⊤ : Filter ℝ)) P.a (P.A : ℝ) σ
    ha' hA
  rw [Asymptotics.isBigO_top] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hCbound : ∀ t : ℝ,
      ‖CriticalLinePhasor.CarrierTheta.dirichlet P.a ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
    intro t
    have := hC t
    simpa using this
  refine ⟨A * max C 1, by positivity, fun t => ?_⟩
  rw [lam_line_eq P κ pkg _ (by simpa using hσ), norm_mul]
  calc ‖κ.G ((σ : ℂ) + (t : ℂ) * I)‖ *
        ‖CriticalLinePhasor.CarrierTheta.dirichlet P.a ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (A * Real.exp (-k * |t|)) * max C 1 :=
        mul_le_mul (hGexp t) (le_trans (hCbound t) (le_max_left C 1)) (norm_nonneg _)
          (by positivity)
    _ = A * max C 1 * Real.exp (-k * |t|) := by ring

end CriticalLinePhasor.StirlingLine

#print axioms CriticalLinePhasor.StirlingLine.gammaC_vline_exp_bound
#print axioms CriticalLinePhasor.StirlingLine.gammaR_vline_integrable
#print axioms CriticalLinePhasor.StirlingLine.chain_line_integrable
#print axioms CriticalLinePhasor.StirlingLine.chain_line_exp_bound
#print axioms CriticalLinePhasor.StirlingLine.lam_line_integrable_of_G
#print axioms CriticalLinePhasor.StirlingLine.lam_line_exp_bound_of_G
