import RequestProject.GrownFiberDoor

/-!
# The two-ended grown fiber: helix and anti-helix, and T2c on it (ledger 703)

`twoEnded Z s = finiteFiber Z s + χ_η(s) · finiteFiber Z (1 − s)`: the carrier's grown fiber read from both ends,
`χ_η` the conduction-corrected functional-equation factor of `η` in Mathlib's normalisation.  On the open strip the
two ends converge (`finiteFiber_tendstoLocallyUniformlyOn` at `s` and at `1 − s`), so `twoEnded (Z n) → 2η`
locally uniformly on the strip (`twoEnded_tendstoLocallyUniformlyOn`).

**The clause `TwoEndedClean`** — at every head, in every box of the strip, every event of the balanced fiber lies on
the axis: one clean cancellation per carrier height, at finite head (measured 2026-09-10, `tmp/att703`: ten events in
the box `[0.2, 0.8] × [10, 50]` at heads 25 to 1000, all on the axis, all sign changes of the grown Hardy function).
**`rh_of_twoEndedClean`** — the clause forces the Riemann Hypothesis (Hurwitz on a ball around an off-axis zero).
-/

open Complex Filter Topology Set
open CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.BankNoTransient

namespace CriticalLinePhasor.GrownFiber

/-- The open strip `0 < Re s < 1`. -/
def strip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

theorem isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem convex_strip : Convex ℝ strip := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)

theorem strip_subset_rightHalf : strip ⊆ {s : ℂ | 0 < s.re} := fun s hs => hs.1

theorem one_sub_mem_strip {s : ℂ} (hs : s ∈ strip) : 1 - s ∈ strip := by
  obtain ⟨h0, h1⟩ := hs
  constructor <;> simp <;> linarith

theorem ne_one_of_mem_strip {s : ℂ} (hs : s ∈ strip) : s ≠ 1 := by
  intro h; have := hs.2; rw [h] at this; simp at this

theorem ne_zero_of_mem_strip {s : ℂ} (hs : s ∈ strip) : s ≠ 0 := by
  intro h; have := hs.1; rw [h] at this; simp at this

/-- `2^s ≠ 1` off the imaginary axis. -/
theorem two_cpow_ne_one {s : ℂ} (hs : s.re ≠ 0) : (2 : ℂ) ^ s ≠ 1 := by
  intro h
  have hn := congrArg norm h
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hn
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) h1; linarith
  · have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) h1; linarith

/-- The functional-equation factor of `ζ` in Mathlib's normalisation: `ζ(1 − s) = A(s) ζ(s)`. -/
noncomputable def feFactor (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)

theorem feFactor_ne_zero {s : ℂ} (hs : s ∈ strip) : feFactor s ≠ 0 := by
  unfold feFactor
  have hΓ : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    have h0 := hs.1
    simp at this
    linarith
  have hcos : Complex.cos (Real.pi * s / 2) ≠ 0 := by
    intro h
    rw [Complex.cos_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hs' : s = 2 * (k : ℂ) + 1 := by
      have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by linear_combination 2 * hk
      exact mul_left_cancel₀ hπ h2
    have hre := congrArg Complex.re hs'
    simp at hre
    have h0 := hs.1; have h1 := hs.2
    have hk1 : (k : ℝ) < 0 := by linarith
    have hk2 : k < 0 := by exact_mod_cast hk1
    have hk3 : k ≤ -1 := by omega
    have hk4 : (k : ℝ) ≤ -1 := by exact_mod_cast hk3
    linarith
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push_neg
    intro h; exfalso
    have := congrArg Complex.re h
    simp at this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hcos

theorem feFactor_continuousOn : ContinuousOn feFactor strip := by
  unfold feFactor
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply ContinuousOn.mul continuousOn_const
      apply Continuous.continuousOn
      apply continuous_const.cpow continuous_neg
      intro _
      rw [Complex.mem_slitPlane_iff]; left; simp; linarith [Real.pi_pos]
    · intro s hs
      apply ContinuousAt.continuousWithinAt
      apply (Complex.differentiableAt_Gamma s _).continuousAt
      intro m hm
      have := congrArg Complex.re hm
      have h0 := hs.1
      simp at this
      linarith
  · exact (Complex.continuous_cos.comp (by fun_prop)).continuousOn

theorem feFactor_differentiableOn : DifferentiableOn ℂ feFactor strip := by
  unfold feFactor
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hΓ : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s (fun m hm => by
    have := congrArg Complex.re hm; have h0 := hs.1; simp at this; linarith)
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (2 * (Real.pi : ℂ)) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hbase)
  have hcos : DifferentiableAt ℂ (fun s : ℂ => Complex.cos (Real.pi * s / 2)) s := by fun_prop
  exact (((differentiableAt_const _).mul hpow).mul hΓ).mul hcos

/-- `η(1 − s) = (1 − 2^s) A(s) ζ(s)` on the strip. -/
theorem eta_one_sub_eq {s : ℂ} (hs : s ∈ strip) :
    etaTailLimit (1 - s) = (1 - (2 : ℂ) ^ s) * feFactor s * riemannZeta s := by
  have h1s : 1 - s ∈ strip := one_sub_mem_strip hs
  rw [etaTailLimit_eq_etaProduct h1s.1 (ne_one_of_mem_strip h1s)]
  rw [show (1 : ℂ) - (1 - s) = s by ring]
  rw [riemannZeta_one_sub (fun n hn => by
      have := congrArg Complex.re hn; have h0 := hs.1; simp at this; linarith)
    (ne_one_of_mem_strip hs)]
  unfold feFactor
  ring

/-- `χ_η(s) = (1 − 2^{1−s}) / ((1 − 2^s) A(s))`: the factor with `η(s) = χ_η(s) η(1 − s)`. -/
noncomputable def chiEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) / ((1 - (2 : ℂ) ^ s) * feFactor s)

theorem chiEta_continuousOn : ContinuousOn chiEta strip := by
  unfold chiEta
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    exact continuous_const.sub (continuous_const.cpow (continuous_const.sub continuous_id)
      (fun _ => by rw [Complex.mem_slitPlane_iff]; left; norm_num))
  · apply ContinuousOn.mul _ feFactor_continuousOn
    apply Continuous.continuousOn
    exact continuous_const.sub (continuous_const.cpow continuous_id
      (fun _ => by rw [Complex.mem_slitPlane_iff]; left; norm_num))
  · intro s hs
    exact mul_ne_zero (sub_ne_zero.mpr (two_cpow_ne_one hs.1.ne').symm) (feFactor_ne_zero hs)

theorem chiEta_differentiableOn : DifferentiableOn ℂ chiEta strip := by
  unfold chiEta
  apply DifferentiableOn.div
  · exact ((differentiable_const _).sub
      (((differentiable_const _).sub differentiable_id).const_cpow (Or.inl two_ne_zero))).differentiableOn
  · exact (((differentiable_const _).sub (differentiable_id.const_cpow (Or.inl two_ne_zero))).differentiableOn).mul
      feFactor_differentiableOn
  · intro s hs
    exact mul_ne_zero (sub_ne_zero.mpr (two_cpow_ne_one hs.1.ne').symm) (feFactor_ne_zero hs)

/-- **The two-ended identity:** `χ_η(s) η(1 − s) = η(s)` on the strip. -/
theorem chiEta_mul_eta_one_sub {s : ℂ} (hs : s ∈ strip) : chiEta s * etaTailLimit (1 - s) = etaTailLimit s := by
  rw [eta_one_sub_eq hs, etaTailLimit_eq_etaProduct hs.1 (ne_one_of_mem_strip hs)]
  unfold chiEta
  have h1 : (1 - (2 : ℂ) ^ s) ≠ 0 := sub_ne_zero.mpr (two_cpow_ne_one hs.1.ne').symm
  have h2 := feFactor_ne_zero hs
  field_simp

/-! ### The two-ended grown fiber -/

/-- `twoEnded Z s = F_Z(s) + χ_η(s) F_Z(1 − s)`: the grown fiber read from both ends. -/
noncomputable def twoEnded (Z : ℝ) (s : ℂ) : ℂ := finiteFiber Z s + chiEta s * finiteFiber Z (1 - s)

/-- The two-ended limit, `η(s) + χ_η(s) η(1 − s) = 2η(s)` on the strip. -/
noncomputable def twoEndedLimit (s : ℂ) : ℂ := etaTailLimit s + chiEta s * etaTailLimit (1 - s)

theorem twoEndedLimit_eq {s : ℂ} (hs : s ∈ strip) :
    twoEndedLimit s = 2 * ((1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) := by
  unfold twoEndedLimit
  rw [chiEta_mul_eta_one_sub hs, etaTailLimit_eq_etaProduct hs.1 (ne_one_of_mem_strip hs)]
  ring

/-- Locally uniform limits on an open set: sums. -/
theorem tendstoLocallyUniformlyOn_add' {U : Set ℂ} (hU : IsOpen U) {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn F f atTop U) (hG : TendstoLocallyUniformlyOn G g atTop U) :
    TendstoLocallyUniformlyOn (fun n z => F n z + G n z) (fun z => f z + g z) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hF hG ⊢
  intro K hK hKc
  exact (hF K hK hKc).add (hG K hK hKc)

/-- Locally uniform limits on an open set: multiplication by a continuous function. -/
theorem tendstoLocallyUniformlyOn_mul_left' {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : ContinuousOn g U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : TendstoLocallyUniformlyOn F f atTop U) :
    TendstoLocallyUniformlyOn (fun n z => g z * F n z) (fun z => g z * f z) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hF ⊢
  intro K hK hKc
  obtain ⟨M₀, hM₀⟩ := (hKc.image_of_continuousOn (hg.mono hK)).isBounded.exists_norm_le
  set M : ℝ := max M₀ 0 with hMdef
  have hM : ∀ y ∈ g '' K, ‖y‖ ≤ M := fun y hy => (hM₀ y hy).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hFK := Metric.tendstoUniformlyOn_iff.mp (hF K hK hKc)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hFK (ε / (M + 1)) (by positivity)] with n hn z hz
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hgz : ‖g z‖ ≤ M := hM (g z) (mem_image_of_mem g hz)
  have h1 := hn z hz
  rw [dist_eq_norm] at h1
  calc ‖g z‖ * ‖f z - F n z‖ ≤ M * (ε / (M + 1)) := mul_le_mul hgz h1.le (norm_nonneg _) hM0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **The two-ended grown fiber converges locally uniformly on the strip to `2η`.** -/
theorem twoEnded_tendstoLocallyUniformlyOn (Z : ℕ → ℝ) (hZ : Tendsto Z atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => twoEnded (Z n)) twoEndedLimit atTop strip := by
  have h1 : TendstoLocallyUniformlyOn (fun n => finiteFiber (Z n)) etaTailLimit atTop strip :=
    (finiteFiber_tendstoLocallyUniformlyOn Z hZ).mono strip_subset_rightHalf
  have h2 : TendstoLocallyUniformlyOn (fun n => (finiteFiber (Z n)) ∘ (fun s : ℂ => 1 - s))
      (etaTailLimit ∘ (fun s : ℂ => 1 - s)) atTop strip :=
    h1.comp (fun s : ℂ => 1 - s) (fun s hs => one_sub_mem_strip hs) (by fun_prop)
  have h3 := tendstoLocallyUniformlyOn_mul_left' isOpen_strip chiEta_continuousOn h2
  exact tendstoLocallyUniformlyOn_add' isOpen_strip h1 h3

/-! ### The clause and the door -/

/-- **One clean cancellation per carrier height, at every head:** in every box of the strip, every event of the
balanced fiber lies on the axis. -/
def TwoEndedClean (Z : ℕ → ℝ) : Prop :=
  ∀ T : ℝ, ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ strip → |s.im| ≤ T → s.re ≠ 1 / 2 → twoEnded (Z n) s ≠ 0

/-- The two-ended limit is not identically zero near any point of the strip. -/
theorem twoEndedLimit_not_eqOn_zero_ball {ρ : ℂ} (hρ : ρ ∈ strip) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball ρ r ⊆ strip) : ∃ z ∈ Metric.ball ρ r, twoEndedLimit z ≠ 0 := by
  by_contra hall
  push Not at hall
  have hζ : ∀ z ∈ Metric.ball ρ r, riemannZeta z = 0 := by
    intro z hz
    have hzs := hball hz
    have h := hall z hz
    rw [twoEndedLimit_eq hzs] at h
    rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · exact (mul_eq_zero.mp h).resolve_left (conduction_ne_zero hzs.2)
  have hana : AnalyticOnNhd ℂ riemannZeta strip := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_strip
    intro z hz
    exact (differentiableAt_riemannZeta (ne_one_of_mem_strip hz)).differentiableWithinAt
  have hev : riemannZeta =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [Metric.ball_mem_nhds ρ hr] with z hz
    exact hζ z hz
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero convex_strip.isPreconnected hρ hev
  have h34 : (3 / 4 : ℂ) ∈ strip := by constructor <;> norm_num
  exact riemannZeta_three_quarters_ne_zero (hzero h34)

/-- **The door: one clean cancellation per carrier height at every head forces the Riemann Hypothesis.** -/
theorem rh_of_twoEndedClean (Z : ℕ → ℝ) (hZ : Tendsto Z atTop atTop) (h : TwoEndedClean Z) :
    RiemannHypothesis := by
  apply DoubleCoshProgram.RiemannHypothesis_of_no_offline
  intro ρ hρ
  by_contra hne
  have hstrip : ρ ∈ strip := ⟨hρ.1, hρ.2.1⟩
  -- the limit vanishes at ρ
  have hL : twoEndedLimit ρ = 0 := by
    rw [twoEndedLimit_eq hstrip, hρ.2.2]; ring
  -- a ball around ρ inside the strip, off the axis, below height `|Im ρ| + 1`
  set d : ℝ := |ρ.re - 1 / 2| with hd
  have hdpos : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp isOpen_strip ρ hstrip
  set r : ℝ := min (min r₁ d) 1 / 2 with hr
  have hrpos : 0 < r := by positivity
  have hr1 : r < r₁ := by
    have : min (min r₁ d) 1 ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hrd : r < d := by
    have : min (min r₁ d) 1 ≤ d := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hr1' : r < 1 := by
    have : min (min r₁ d) 1 ≤ 1 := min_le_right _ _
    linarith
  have hball : Metric.ball ρ r ⊆ strip := (Metric.ball_subset_ball hr1.le).trans hball₁
  have hoff : ∀ z ∈ Metric.ball ρ r, z.re ≠ 1 / 2 := by
    intro z hz h12
    have hdist := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hdist
    have h1 : |(z - ρ).re| ≤ ‖z - ρ‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, h12] at h1
    have : |ρ.re - 1 / 2| = |(1 / 2 : ℝ) - ρ.re| := abs_sub_comm _ _
    linarith
  have hheight : ∀ z ∈ Metric.ball ρ r, |z.im| ≤ |ρ.im| + 1 := by
    intro z hz
    have hdist := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hdist
    have h1 : |(z - ρ).im| ≤ ‖z - ρ‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have := abs_sub_abs_le_abs_sub z.im ρ.im
    linarith
  obtain ⟨n₀, hn₀⟩ := (h (|ρ.im| + 1)).exists_forall_of_atTop
  set F : ℕ → ℂ → ℂ := fun k => twoEnded (Z (k + n₀)) with hF
  have hconv : TendstoLocallyUniformlyOn F twoEndedLimit atTop (Metric.ball ρ r) := by
    have h1 := (twoEnded_tendstoLocallyUniformlyOn Z hZ).mono hball
    intro u hu x hx
    obtain ⟨t, ht, hev⟩ := h1 u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat n₀).eventually hev⟩
  have hFne : ∀ k, ∀ z ∈ Metric.ball ρ r, F k z ≠ 0 := fun k z hz =>
    hn₀ (k + n₀) (by omega) z (hball hz) (hheight z hz) (hoff z hz)
  have hFdiff : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball ρ r) := by
    intro k
    apply DifferentiableOn.add (finiteFiber_entire _).differentiableOn
    exact (chiEta_differentiableOn.mono hball).mul
      (((finiteFiber_entire _).comp ((differentiable_const _).sub differentiable_id)).differentiableOn)
  have hne := CriticalLinePhasor.Hurwitz.ne_zero_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
    (convex_ball ρ r).isPreconnected hFdiff hFne hconv
    (twoEndedLimit_not_eqOn_zero_ball hstrip hrpos hball) ρ (Metric.mem_ball_self hrpos)
  exact hne hL

end CriticalLinePhasor.GrownFiber

#print axioms CriticalLinePhasor.GrownFiber.chiEta_mul_eta_one_sub
#print axioms CriticalLinePhasor.GrownFiber.twoEnded_tendstoLocallyUniformlyOn
#print axioms CriticalLinePhasor.GrownFiber.rh_of_twoEndedClean
