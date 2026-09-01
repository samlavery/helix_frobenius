import Mathlib

/-!
# Transient rigidity: Dirichlet readouts have no decaying sector

The Phase-B σ>1 exclusion brick, in the register the att569 diagnostic
identified.  A carrier readout on a vertical line is an absolutely
convergent exponential sum over the log-lattice frequencies
`t ↦ Σ' aₙ e^{−it·log(n+1)}`.  Compiled here:

* `coeff_eq_zero_of_tendsto_zero` — if the readout tends to `0` along the
  line, EVERY coefficient vanishes.  Mechanism: Cesàro character averaging
  extracts `aₘ` at the explicit rate `2M/(cₘT)` (frequency separation
  `cₘ = log((m+2)/(m+1))`), while decay forces the same average to `0`.
* `readout_eq_zero_of_tendsto_zero` — hence the readout is identically `0`.

Consequence for the C₁ audit (att569): a single-quadruple surgery adds a
TRANSIENT — a decaying, somewhere-nonzero component — to the σ-line
readout; by this brick no absolutely convergent Dirichlet readout can
absorb it.  The finite-power/transient dichotomy is now a theorem on the
σ>1 side; the transport of transient-freeness into the channel is
Phase B's single item.

No `sorry`, no `axiom`.
-/

open Complex Filter MeasureTheory Topology

noncomputable section

namespace CriticalLinePhasor.TransientRigidity

/-- The log-lattice frequency of mode `n`. -/
def freq (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1)

/-- The carrier readout on a vertical line. -/
def readout (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a n * Complex.exp (-(Complex.I * t * freq n))

theorem exp_I_mul_norm (t x : ℝ) :
    ‖Complex.exp (Complex.I * t * x)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (t : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem exp_neg_I_mul_norm (t x : ℝ) :
    ‖Complex.exp (-(Complex.I * t * x))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(Complex.I * (t : ℂ) * (x : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

theorem readout_term_norm (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖a n * Complex.exp (-(Complex.I * t * freq n))‖ = ‖a n‖ := by
  rw [norm_mul, exp_neg_I_mul_norm, mul_one]

theorem readout_norm_le (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (t : ℝ) :
    ‖readout a t‖ ≤ ∑' n, ‖a n‖ := by
  have hs : Summable
      (fun n : ℕ => ‖a n * Complex.exp (-(Complex.I * t * freq n))‖) :=
    ha.congr (fun n => (readout_term_norm a n t).symm)
  calc ‖readout a t‖
      ≤ ∑' n, ‖a n * Complex.exp (-(Complex.I * t * freq n))‖ :=
        norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖a n‖ := tsum_congr (fun n => readout_term_norm a n t)

theorem readout_continuous (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) :
    Continuous (readout a) := by
  apply continuous_tsum
  · intro n
    apply continuous_const.mul
    apply Complex.continuous_exp.comp
    exact ((continuous_const.mul Complex.continuous_ofReal).mul
      continuous_const).neg
  · exact ha
  · intro n t
    exact le_of_eq (readout_term_norm a n t)

/-- **Frequency separation**: every other mode sits at log-distance at least
`log((m+2)/(m+1))` from mode `m`. -/
theorem freq_separation (m : ℕ) :
    ∀ n : ℕ, n ≠ m →
      Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) ≤ |freq m - freq n| := by
  intro n hn
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hsep : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
      = Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hnm : (n : ℝ) + 1 ≤ (m : ℝ) := by
      have h : n + 1 ≤ m := hlt
      exact_mod_cast h
    have hm0 : (0:ℝ) < (m : ℝ) := lt_of_lt_of_le hn1 hnm
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (m : ℝ) :=
      Real.log_le_log hn1 hnm
    have h2 : Real.log (m : ℝ) + Real.log ((m : ℝ) + 2)
        ≤ 2 * Real.log ((m : ℝ) + 1) := by
      have hprod : (m : ℝ) * ((m : ℝ) + 2) ≤ ((m : ℝ) + 1)^2 := by nlinarith
      have h3 : Real.log ((m : ℝ) * ((m : ℝ) + 2))
          ≤ Real.log (((m : ℝ) + 1)^2) :=
        Real.log_le_log (by positivity) hprod
      rw [Real.log_mul (ne_of_gt hm0) (by positivity), Real.log_pow] at h3
      push_cast at h3
      linarith
    have habs : |freq m - freq n| = freq m - freq n := by
      apply abs_of_nonneg
      unfold freq
      have h := Real.log_le_log hn1 (by linarith : (n:ℝ)+1 ≤ (m:ℝ)+1)
      linarith
    rw [habs, hsep]
    unfold freq
    linarith
  · have hnm : (m : ℝ) + 2 ≤ (n : ℝ) + 1 := by
      have h : m + 1 ≤ n := hgt
      have h2 : m + 2 ≤ n + 1 := by omega
      exact_mod_cast h2
    have h1 : Real.log ((m : ℝ) + 2) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) hnm
    have habs : |freq m - freq n| = freq n - freq m := by
      rw [abs_sub_comm]
      apply abs_of_nonneg
      unfold freq
      have h := Real.log_le_log hm1 (by linarith : (m:ℝ)+1 ≤ (n:ℝ)+1)
      linarith
    rw [habs, hsep]
    unfold freq
    linarith

/-- Diagonal character integral. -/
theorem char_integral_diag (m : ℕ) (T : ℝ) :
    (∫ t in (0:ℝ)..T,
        Complex.exp (Complex.I * t * ((freq m - freq m : ℝ) : ℂ)))
      = (T : ℂ) := by
  have h : ∀ t : ℝ,
      Complex.exp (Complex.I * t * ((freq m - freq m : ℝ) : ℂ)) = 1 := by
    intro t
    simp
  rw [intervalIntegral.integral_congr (fun t _ => h t),
    intervalIntegral.integral_const]
  simp

/-- Off-diagonal character integral: bounded by `2/|Δfreq|`, uniformly in
the window length. -/
theorem char_integral_offdiag_norm {m n : ℕ} (hmn : freq m - freq n ≠ 0)
    (T : ℝ) :
    ‖∫ t in (0:ℝ)..T,
        Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖
      ≤ 2 / |freq m - freq n| := by
  set ω : ℝ := freq m - freq n with hω
  have hc : (Complex.I * (ω:ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hmn)
  have hfun : ∀ t : ℝ, Complex.exp (Complex.I * t * (ω:ℂ))
      = Complex.exp ((Complex.I * (ω:ℂ)) * t) := by
    intro t
    congr 1
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hfun t),
    integral_exp_mul_complex hc]
  have hnorm1 : ‖Complex.exp (Complex.I * (ω:ℂ) * (T:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (Complex.I * (ω:ℂ) * (T:ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h, Real.exp_zero]
  have hnorm0 : ‖Complex.exp (Complex.I * (ω:ℂ) * ((0:ℝ):ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have h : (Complex.I * (ω:ℂ) * ((0:ℝ):ℂ)).re = 0 := by
      simp
    rw [h, Real.exp_zero]
  have hcnorm : ‖Complex.I * (ω:ℂ)‖ = |ω| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have hnum : ‖Complex.exp (Complex.I * (ω:ℂ) * (T:ℂ))
      - Complex.exp (Complex.I * (ω:ℂ) * ((0:ℝ):ℂ))‖ ≤ 2 := by
    calc ‖Complex.exp (Complex.I * (ω:ℂ) * (T:ℂ))
          - Complex.exp (Complex.I * (ω:ℂ) * ((0:ℝ):ℂ))‖
        ≤ ‖Complex.exp (Complex.I * (ω:ℂ) * (T:ℂ))‖
          + ‖Complex.exp (Complex.I * (ω:ℂ) * ((0:ℝ):ℂ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [hnorm1, hnorm0]; norm_num
  rw [norm_div, hcnorm]
  have hω0 : 0 < |ω| := abs_pos.mpr hmn
  gcongr

/-- The interchange: the windowed character average of the readout is the
sum of per-mode character integrals. -/
theorem readout_char_integral (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖)
    (m : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0:ℝ)..T, readout a t * Complex.exp (Complex.I * t * freq m))
      = ∑' n : ℕ, a n *
          ∫ t in (0:ℝ)..T,
            Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ)) := by
  have hpt : ∀ t : ℝ, readout a t * Complex.exp (Complex.I * t * freq m)
      = ∑' n : ℕ,
          a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ)) := by
    intro t
    unfold readout
    rw [← tsum_mul_right]
    congr 1
    funext n
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hchar : ∀ n (t : ℝ),
      ‖a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖
        = ‖a n‖ := by
    intro n t
    rw [norm_mul, exp_I_mul_norm, mul_one]
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ =>
        a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ)))
      (MeasureTheory.volume.restrict (Set.Ioc 0 T)) := by
    intro n
    apply Continuous.aestronglyMeasurable
    apply continuous_const.mul
    apply Complex.continuous_exp.comp
    exact (continuous_const.mul Complex.continuous_ofReal).mul continuous_const
  have hlin : ∀ n : ℕ, (∫⁻ t in Set.Ioc (0:ℝ) T,
        ‖a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖ₑ
        ∂MeasureTheory.volume)
      = ‖a n‖ₑ * ENNReal.ofReal T := by
    intro n
    have h1 : (fun t : ℝ =>
        ‖a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖ₑ)
        = fun _ : ℝ => ‖a n‖ₑ := by
      funext t
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hchar n t]
    rw [h1, MeasureTheory.lintegral_const,
      MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    rw [sub_zero]
  have hlint : (∑' n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) T,
        ‖a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖ₑ
        ∂MeasureTheory.volume) ≠ ⊤ := by
    have h1 : (∑' n : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) T,
        ‖a n * Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ))‖ₑ
        ∂MeasureTheory.volume)
        = (∑' n : ℕ, ‖a n‖ₑ) * ENNReal.ofReal T := by
      rw [← ENNReal.tsum_mul_right]
      congr 1
      funext n
      exact hlin n
    rw [h1]
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    have h2 : (∑' n : ℕ, ‖a n‖ₑ) = ENNReal.ofReal (∑' n, ‖a n‖) := by
      simp only [← ofReal_norm_eq_enorm]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) ha).symm
    rw [h2]
    exact ENNReal.ofReal_ne_top
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_of_le hT.le,
    MeasureTheory.integral_tsum hmeas hlint]
  apply tsum_congr
  intro n
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact (intervalIntegral.integral_of_le hT.le).symm

/-- **The Cesàro character average approaches `aₘ` at explicit rate
`2M/(cₘT)`.** -/
theorem avg_close (a : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (m : ℕ)
    {T : ℝ} (hT : 1 ≤ T) :
    ‖(∫ t in (0:ℝ)..T,
        readout a t * Complex.exp (Complex.I * t * freq m)) / (T:ℂ) - a m‖
      ≤ 2 * (∑' n, ‖a n‖)
        / (Real.log (((m:ℝ)+2)/((m:ℝ)+1)) * T) := by
  set cm : ℝ := Real.log (((m:ℝ)+2)/((m:ℝ)+1)) with hcm
  have hcm0 : 0 < cm := by
    rw [hcm]
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le one_pos hT
  set F : ℕ → ℂ := fun n => a n *
      ∫ t in (0:ℝ)..T,
        Complex.exp (Complex.I * t * ((freq m - freq n : ℝ) : ℂ)) with hF
  have hFbound : ∀ n : ℕ, n ≠ m → ‖F n‖ ≤ (2/cm) * ‖a n‖ := by
    intro n hn
    have hsep := freq_separation m n hn
    have hne : freq m - freq n ≠ 0 := by
      intro h
      rw [h, abs_zero] at hsep
      linarith
    have h1 := char_integral_offdiag_norm hne T
    have h2 : 2 / |freq m - freq n| ≤ 2 / cm := by
      gcongr
    rw [hF]
    calc ‖a n * _‖ = ‖a n‖ * ‖_‖ := norm_mul _ _
      _ ≤ ‖a n‖ * (2/cm) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (norm_nonneg _)
      _ = (2/cm) * ‖a n‖ := by ring
  have hFsum : Summable F := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (g := fun n => ‖F n‖)
      (f := fun n => (2/cm + T) * ‖a n‖) ?_ (ha.mul_left _)
    intro n
    rcases eq_or_ne n m with rfl | hn
    · rw [hF]
      calc ‖a n * _‖ = ‖a n‖ * ‖_‖ := norm_mul _ _
        _ ≤ ‖a n‖ * T := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [char_integral_diag]
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
        _ ≤ (2/cm + T) * ‖a n‖ := by
            have : (0:ℝ) ≤ 2/cm := by positivity
            nlinarith [norm_nonneg (a n)]
    · calc ‖F n‖ ≤ (2/cm) * ‖a n‖ := hFbound n hn
        _ ≤ (2/cm + T) * ‖a n‖ := by
            nlinarith [norm_nonneg (a n), hT0]
  rw [readout_char_integral a ha m hT0]
  rw [hFsum.tsum_eq_add_tsum_ite m]
  have hFm : F m = a m * (T:ℂ) := by
    rw [hF]
    show a m * (∫ t in (0:ℝ)..T,
        Complex.exp (Complex.I * t * ((freq m - freq m : ℝ) : ℂ)))
      = a m * (T:ℂ)
    rw [char_integral_diag]
  rw [hFm]
  have hTC : (T:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hT0
  have hsimp : (a m * (T:ℂ)
        + ∑' n, if n = m then 0 else F n) / (T:ℂ) - a m
      = (∑' n, if n = m then 0 else F n) / (T:ℂ) := by
    field_simp [hTC]
    ring
  rw [hsimp]
  have hRnorm : Summable (fun n : ℕ => ‖if n = m then 0 else F n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      (ha.mul_left (2/cm))
    intro n
    rcases eq_or_ne n m with rfl | hn
    · rw [if_pos rfl, norm_zero]
      positivity
    · rw [if_neg hn]
      exact hFbound n hn
  have hR : ‖∑' n : ℕ, if n = m then 0 else F n‖
      ≤ (2/cm) * (∑' n, ‖a n‖) := by
    calc ‖∑' n : ℕ, if n = m then 0 else F n‖
        ≤ ∑' n : ℕ, ‖if n = m then 0 else F n‖ :=
          norm_tsum_le_tsum_norm hRnorm
      _ ≤ ∑' n : ℕ, (2/cm) * ‖a n‖ := by
          apply hRnorm.tsum_le_tsum ?_ (ha.mul_left (2/cm))
          intro n
          rcases eq_or_ne n m with rfl | hn
          · rw [if_pos rfl, norm_zero]
            positivity
          · rw [if_neg hn]
            exact hFbound n hn
      _ = (2/cm) * (∑' n, ‖a n‖) := tsum_mul_left
  rw [norm_div]
  have hTnorm : ‖(T:ℂ)‖ = T := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  rw [hTnorm]
  calc ‖∑' n : ℕ, if n = m then 0 else F n‖ / T
      ≤ ((2/cm) * (∑' n, ‖a n‖)) / T := by gcongr
    _ = 2 * (∑' n, ‖a n‖) / (cm * T) := by
        field_simp

/-- Cesàro averages of a bounded nonnegative decaying function vanish. -/
theorem cesaro_avg_tendsto_zero {h : ℝ → ℝ} {M : ℝ} (hcont : Continuous h)
    (hnn : ∀ t, 0 ≤ h t) (hM : ∀ t, h t ≤ M)
    (hdec : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in (0:ℝ)..T, h t) / T) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  have hM0 : (0:ℝ) ≤ M := le_trans (hnn 0) (hM 0)
  have hev : ∀ᶠ t in atTop, h t < ε/2 :=
    hdec.eventually_lt_const (by linarith)
  obtain ⟨T₀, hT₀⟩ := hev.exists_forall_of_atTop
  set T₁ : ℝ := max T₀ 0 with hT₁def
  have hT₁0 : (0:ℝ) ≤ T₁ := le_max_right _ _
  filter_upwards [eventually_ge_atTop
    (max (T₁ + 1) (2*(T₁*M + 1)/ε))] with T hT
  have hTa : T₁ + 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTb : 2*(T₁*M + 1)/ε ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0:ℝ) < T := by linarith
  have hTb' : 2*(T₁*M + 1) ≤ ε * T := by
    rw [div_le_iff₀ hε] at hTb
    linarith
  have hint1 : IntervalIntegrable h MeasureTheory.volume 0 T₁ :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable h MeasureTheory.volume T₁ T :=
    hcont.intervalIntegrable _ _
  have hsplit : (∫ t in (0:ℝ)..T, h t)
      = (∫ t in (0:ℝ)..T₁, h t) + ∫ t in T₁..T, h t :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hb1 : (∫ t in (0:ℝ)..T₁, h t) ≤ T₁ * M := by
    calc (∫ t in (0:ℝ)..T₁, h t) ≤ ∫ _t in (0:ℝ)..T₁, M :=
        intervalIntegral.integral_mono_on hT₁0 hint1
          intervalIntegrable_const (fun t _ => hM t)
      _ = T₁ * M := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hb2 : (∫ t in T₁..T, h t) ≤ (T - T₁) * (ε/2) := by
    have hmono : (∫ t in T₁..T, h t) ≤ ∫ _t in T₁..T, (ε/2 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith : T₁ ≤ T) hint2
        intervalIntegrable_const
      intro t ht
      exact le_of_lt (hT₀ t (le_trans (le_max_left T₀ 0) ht.1))
    have hconst : (∫ _t in T₁..T, (ε/2 : ℝ)) = (T - T₁) * (ε/2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    linarith [hmono, hconst.le, hconst.ge]
  have hpos : 0 ≤ (∫ t in (0:ℝ)..T, h t) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hnn t)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hpos, abs_of_pos hT0,
    div_lt_iff₀ hT0]
  have hstep : (∫ t in (0:ℝ)..T, h t) ≤ T₁*M + (T - T₁)*(ε/2) := by
    rw [hsplit]
    linarith [hb1, hb2]
  have hT₁ε : (0:ℝ) ≤ T₁ * ε := mul_nonneg hT₁0 hε.le
  nlinarith [hstep, hTb', hT₁ε]

/-- **Transient rigidity**: an absolutely convergent log-lattice readout
that tends to `0` along the line has every coefficient zero. -/
theorem coeff_eq_zero_of_tendsto_zero (a : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖)
    (hdecay : Tendsto (readout a) atTop (𝓝 0)) (m : ℕ) : a m = 0 := by
  set A : ℝ → ℂ := fun T =>
    (∫ t in (0:ℝ)..T, readout a t * Complex.exp (Complex.I * t * freq m))
      / (T:ℂ) with hA
  set L : ℝ := Real.log (((m:ℝ)+2)/((m:ℝ)+1)) with hL
  have hcm0 : 0 < L := by
    rw [hL]
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith
  clear_value L
  have h1 : Tendsto A atTop (𝓝 (a m)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg0 : Tendsto (fun T : ℝ => (2 * (∑' n, ‖a n‖) / L) * T⁻¹)
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 (0:ℝ)) :=
        tendsto_inv_atTop_zero
      have h2 := hbase.const_mul (2 * (∑' n, ‖a n‖) / L)
      rwa [mul_zero] at h2
    have hev : ∀ᶠ T in atTop,
        ‖‖A T - a m‖‖ ≤ (2 * (∑' n, ‖a n‖) / L) * T⁻¹ := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      have hT0 : (0:ℝ) < T := lt_of_lt_of_le one_pos hT
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h := avg_close a ha m hT
      rw [← hL] at h
      calc ‖A T - a m‖ ≤ 2 * (∑' n, ‖a n‖) / (L * T) := h
        _ = (2 * (∑' n, ‖a n‖) / L) * T⁻¹ := by
            field_simp
    exact squeeze_zero_norm' hev hg0
  have h2 : Tendsto A atTop (𝓝 0) := by
    have hces := cesaro_avg_tendsto_zero
      (h := fun t => ‖readout a t‖) (M := ∑' n, ‖a n‖)
      ((readout_continuous a ha).norm) (fun t => norm_nonneg _)
      (readout_norm_le a ha) (by simpa using hdecay.norm)
    apply squeeze_zero_norm' ?_ hces
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [hA]
    simp only
    rw [norm_div]
    have hTnorm : ‖(T:ℂ)‖ = T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    rw [hTnorm]
    have hle : ‖∫ t in (0:ℝ)..T,
        readout a t * Complex.exp (Complex.I * t * freq m)‖
        ≤ ∫ t in (0:ℝ)..T, ‖readout a t‖ := by
      calc ‖∫ t in (0:ℝ)..T,
            readout a t * Complex.exp (Complex.I * t * freq m)‖
          ≤ ∫ t in (0:ℝ)..T,
              ‖readout a t * Complex.exp (Complex.I * t * freq m)‖ := by
            apply intervalIntegral.norm_integral_le_integral_norm hT.le
        _ = ∫ t in (0:ℝ)..T, ‖readout a t‖ := by
            apply intervalIntegral.integral_congr
            intro t _
            show ‖readout a t * Complex.exp (Complex.I * t * freq m)‖
              = ‖readout a t‖
            rw [norm_mul, exp_I_mul_norm, mul_one]
    gcongr
  exact tendsto_nhds_unique h1 h2

/-- **The rigidity corollary**: the decaying readout is identically zero —
no absolutely convergent Dirichlet readout has a transient sector. -/
theorem readout_eq_zero_of_tendsto_zero (a : ℕ → ℂ)
    (ha : Summable fun n => ‖a n‖)
    (hdecay : Tendsto (readout a) atTop (𝓝 0)) (t : ℝ) :
    readout a t = 0 := by
  unfold readout
  have h := coeff_eq_zero_of_tendsto_zero a ha hdecay
  simp only [h, zero_mul, tsum_zero]

/-- The log-derivative trace of a finite zero/pole packet on a vertical
line — the general surgery transient (`Q′/Q(σ₀+it)` for a Blaschke-type
census-preserving surgery). -/
def packetTrace {k l : ℕ} (zs : Fin k → ℂ) (ps : Fin l → ℂ)
    (σ0 t : ℝ) : ℂ :=
  (∑ i, (((σ0:ℂ) + Complex.I * t) - zs i)⁻¹)
    - ∑ j, (((σ0:ℂ) + Complex.I * t) - ps j)⁻¹

theorem line_point_im (σ0 : ℝ) (z : ℂ) (t : ℝ) :
    ((((σ0:ℂ) + Complex.I * t) - z)).im = t - z.im := by
  simp

/-- Each surgery term decays along the line. -/
theorem inv_line_tendsto_zero (σ0 : ℝ) (z : ℂ) :
    Tendsto (fun t : ℝ => (((σ0:ℂ) + Complex.I * t) - z)⁻¹)
      atTop (𝓝 0) := by
  have htend : Tendsto (fun t : ℝ => (t - z.im)⁻¹) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ _ tendsto_id
  apply squeeze_zero_norm' ?_ htend
  filter_upwards [eventually_ge_atTop (z.im + 1)] with t ht
  have him : ((((σ0:ℂ) + Complex.I * t) - z)).im = t - z.im :=
    line_point_im σ0 z t
  have h1 : |t - z.im| ≤ ‖(((σ0:ℂ) + Complex.I * t) - z)‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : (0:ℝ) < t - z.im := by linarith
  rw [norm_inv]
  have h3 : |t - z.im| = t - z.im := abs_of_pos h2
  rw [h3] at h1
  gcongr

/-- The whole packet trace decays along the line: surgeries are pure
transients. -/
theorem packetTrace_tendsto_zero {k l : ℕ} (zs : Fin k → ℂ)
    (ps : Fin l → ℂ) (σ0 : ℝ) :
    Tendsto (packetTrace zs ps σ0) atTop (𝓝 0) := by
  unfold packetTrace
  have h1 : Tendsto
      (fun t : ℝ => ∑ i, (((σ0:ℂ) + Complex.I * t) - zs i)⁻¹)
      atTop (𝓝 (∑ _i : Fin k, (0:ℂ))) :=
    tendsto_finset_sum _ (fun i _ => inv_line_tendsto_zero σ0 (zs i))
  have h2 : Tendsto
      (fun t : ℝ => ∑ j, (((σ0:ℂ) + Complex.I * t) - ps j)⁻¹)
      atTop (𝓝 (∑ _j : Fin l, (0:ℂ))) :=
    tendsto_finset_sum _ (fun j _ => inv_line_tendsto_zero σ0 (ps j))
  have h3 := h1.sub h2
  simpa using h3

/-- **The surgery exclusion**: no absolutely convergent carrier readout can
differ from another by a nonvanishing zero/pole surgery — the transient
sector of the Dirichlet class is empty, so every census-preserving Blaschke
deformation exits the class at the moment it exists.  The formal σ>1
C₁-exclusion of the Phase-B map. -/
theorem no_readout_realization_of_packet {k l : ℕ}
    (zs : Fin k → ℂ) (ps : Fin l → ℂ) (σ0 : ℝ)
    (hne : ∃ t : ℝ, packetTrace zs ps σ0 t ≠ 0)
    (b c : ℕ → ℂ) (hb : Summable fun n => ‖b n‖)
    (hc : Summable fun n => ‖c n‖)
    (hrep : ∀ t : ℝ, readout b t = readout c t + packetTrace zs ps σ0 t) :
    False := by
  have hbc : Summable fun n => ‖b n - c n‖ := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_sub_le (b n) (c n)) (hb.add hc)
  have hsub : ∀ t : ℝ, readout (fun n => b n - c n) t
      = readout b t - readout c t := by
    intro t
    unfold readout
    have hbv : Summable
        (fun n : ℕ => b n * Complex.exp (-(Complex.I * t * freq n))) :=
      Summable.of_norm (hb.congr (fun n => (readout_term_norm b n t).symm))
    have hcv : Summable
        (fun n : ℕ => c n * Complex.exp (-(Complex.I * t * freq n))) :=
      Summable.of_norm (hc.congr (fun n => (readout_term_norm c n t).symm))
    rw [← hbv.tsum_sub hcv]
    apply tsum_congr
    intro n
    ring
  have heq : ∀ t : ℝ, readout (fun n => b n - c n) t
      = packetTrace zs ps σ0 t := by
    intro t
    rw [hsub t, hrep t]
    ring
  have hdec : Tendsto (readout (fun n => b n - c n)) atTop (𝓝 0) :=
    (packetTrace_tendsto_zero zs ps σ0).congr (fun t => (heq t).symm)
  obtain ⟨t₀, ht₀⟩ := hne
  apply ht₀
  rw [← heq t₀]
  exact readout_eq_zero_of_tendsto_zero _ hbc hdec t₀

/-- **A genuine pair surgery is somewhere nonvanishing**: moving one zero
anywhere (`z₀ ≠ p₀`) produces a nonzero trace at some line point — so by
`no_readout_realization_of_packet` it can never be absorbed by the
Dirichlet class. -/
theorem pair_packetTrace_ne_zero (σ0 : ℝ) {z₀ p₀ : ℂ} (hzp : z₀ ≠ p₀) :
    ∃ t : ℝ, packetTrace (fun _ : Fin 1 => z₀) (fun _ : Fin 1 => p₀)
      σ0 t ≠ 0 := by
  refine ⟨max z₀.im p₀.im + 1, ?_⟩
  set w : ℂ := (σ0:ℂ) + Complex.I * ((max z₀.im p₀.im + 1 : ℝ) : ℂ) with hw
  have hwim : w.im = max z₀.im p₀.im + 1 := by
    rw [hw]
    simp
  have hwz : w ≠ z₀ := by
    intro h
    have h2 := congrArg Complex.im h
    rw [hwim] at h2
    have := le_max_left z₀.im p₀.im
    linarith [h2.symm.le]
  have hwp : w ≠ p₀ := by
    intro h
    have h2 := congrArg Complex.im h
    rw [hwim] at h2
    have := le_max_right z₀.im p₀.im
    linarith [h2.symm.le]
  unfold packetTrace
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  show (w - z₀)⁻¹ - (w - p₀)⁻¹ ≠ 0
  intro h
  rw [sub_eq_zero] at h
  have h2 : w - z₀ = w - p₀ := inv_inj.mp h
  apply hzp
  linear_combination -h2

end CriticalLinePhasor.TransientRigidity

#print axioms CriticalLinePhasor.TransientRigidity.freq_separation
#print axioms CriticalLinePhasor.TransientRigidity.avg_close
#print axioms CriticalLinePhasor.TransientRigidity.cesaro_avg_tendsto_zero
#print axioms CriticalLinePhasor.TransientRigidity.coeff_eq_zero_of_tendsto_zero
#print axioms CriticalLinePhasor.TransientRigidity.readout_eq_zero_of_tendsto_zero
