import RequestProject.DVPRvM

/-!
# The unit-window zero count: `N(T+1) − N(T) ≤ 41·log(T+2) + 6`

The third classical pillar, assembled from RvM (413): the clock-rate upper
bound integrates to the θ-increment, RvM at two good straddling heights
converts increments of the count to increments of the clock, and good-height
density (410) removes all goodness hypotheses from the final statement.
UNCONDITIONAL.  (This is also the `K`-supply of the seat channel.)
-/

open Complex
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The clock-rate upper bound: `clockRate t ≤ (1/2)·log t` for `t ≥ 20`. -/
theorem clockRate_upper {t : ℝ} (ht : 20 ≤ t) :
    clockRate t ≤ (1/2) * Real.log t := by
  have ht0 : (0:ℝ) < t := by linarith
  have habs : |t| = t := abs_of_pos ht0
  have hmu := mu_stirling_explicit (τ := t) (by rw [habs]; linarith)
  rw [habs] at hmu
  have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
  have hup := (abs_le.mp hmu).2
  have hπ := Real.pi_pos
  -- log(t/2π) ≤ log t − 1  (since 2π ≥ e)
  have h2πe : Real.exp 1 ≤ 2 * Real.pi := by
    nlinarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hlogdiv : Real.log (t / (2 * Real.pi)) ≤ Real.log t - 1 := by
    rw [Real.log_div (by linarith) (by positivity)]
    have : (1:ℝ) ≤ Real.log (2 * Real.pi) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      exact h2πe
    linarith
  -- error term
  have herr : (10 / Real.pi) / t^2 ≤ 1 / (2 * Real.pi) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have ht2 : (400:ℝ) ≤ t^2 := by nlinarith [ht]
    nlinarith [mul_le_mul_of_nonneg_left ht2 hπ.le]
  -- assemble
  have hmu_up : Zeta23.mu t
      ≤ (1 / (2 * Real.pi)) * (Real.log t - 1) + 1 / (2 * Real.pi) := by
    have h1 : (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
        ≤ (1 / (2 * Real.pi)) * (Real.log t - 1) :=
      mul_le_mul_of_nonneg_left hlogdiv (by positivity)
    linarith [hup, herr, h1]
  rw [hcr]
  calc Real.pi * Zeta23.mu t
      ≤ Real.pi * ((1 / (2 * Real.pi)) * (Real.log t - 1) + 1 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hmu_up hπ.le
    _ = (1/2) * Real.log t := by
        field_simp
        ring

/-- The θ-increment upper bound. -/
theorem theta_increment_upper {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (ht : T₁ ≤ T₂) :
    theta T₂ - theta T₁ ≤ (T₂ - T₁) * ((1/2) * Real.log T₂) := by
  have hderiv : ∀ t ∈ Set.uIcc T₁ T₂,
      HasDerivAt theta (clockRate t) t := fun t _ => theta_hasDerivAt t
  have hint : IntervalIntegrable clockRate MeasureTheory.volume T₁ T₂ :=
    continuous_clockRate.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hup : (∫ t in T₁..T₂, clockRate t)
      ≤ ∫ _t in T₁..T₂, ((1/2) * Real.log T₂ : ℝ) := by
    apply intervalIntegral.integral_mono_on ht hint intervalIntegrable_const
    intro t htm
    calc clockRate t ≤ (1/2) * Real.log t :=
          clockRate_upper (by linarith [htm.1])
      _ ≤ (1/2) * Real.log T₂ := by
          have : Real.log t ≤ Real.log T₂ :=
            Real.log_le_log (by linarith [htm.1]) htm.2
          linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hup
  linarith [hftc, hup]

/-- The strip census is monotone. -/
theorem stripZeroCountMult_mono : Monotone (fun T => stripZeroCountMult T) := by
  intro a b hab
  show stripZeroCountMult a ≤ stripZeroCountMult b
  rw [stripZeroCountMult_eq_line_add_offLine,
    stripZeroCountMult_eq_line_add_offLine]
  exact Nat.add_le_add (zeroEventCountMult_mono hab)
    (offLineStripZeroCountMult_mono hab)

/-- The window count at good endpoints: RvM at both ends. -/
theorem zero_count_window {T₁ T₂ : ℝ} (h6 : Real.exp 6 ≤ T₁)
    (h1 : GoodHeight T₁) (h2 : GoodHeight T₂) (ht : T₁ ≤ T₂) :
    (stripZeroCountMult T₂ : ℝ) - stripZeroCountMult T₁
      ≤ (theta T₂ - theta T₁) / Real.pi + 40 * Real.log T₂ + 6 := by
  have hrvm1 := riemann_von_mangoldt h6 h1
  have hrvm2 := riemann_von_mangoldt (le_trans h6 ht) h2
  have hlog : Real.log T₁ ≤ Real.log T₂ :=
    Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 6) h6) ht
  have ha1 := (abs_le.mp hrvm1).1
  have ha2 := (abs_le.mp hrvm2).2
  have hπ := Real.pi_pos
  have hdiv : (theta T₂ / Real.pi - theta T₁ / Real.pi)
      = (theta T₂ - theta T₁) / Real.pi := by ring
  linarith [ha1, ha2, hdiv.le, hdiv.ge]

/-- **The unit-window zero count**, hypothesis-free above `e⁶+1`:
`N(T+1) − N(T) ≤ 41·log(T+2) + 6`. -/
theorem zero_count_unit_window {T : ℝ} (hT : Real.exp 6 + 1 ≤ T) :
    (stripZeroCountMult (T + 1) : ℝ) - stripZeroCountMult T
      ≤ 41 * Real.log (T + 2) + 6 := by
  have he6 : (403:ℝ) ≤ Real.exp 6 := by
    have h3 : (20.08:ℝ) ≤ Real.exp 3 := by
      have h33 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h6 : Real.exp 6 = Real.exp 3 * Real.exp 3 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h3, Real.exp_pos 3]
  obtain ⟨T₁, hT₁l, hT₁u, hg₁⟩ :=
    exists_goodHeight_between (a := T - 1) (by linarith)
  obtain ⟨T₂, hT₂l, hT₂u, hg₂⟩ :=
    exists_goodHeight_between (a := T + 1) (by linarith)
  have hmono1 : stripZeroCountMult T₁ ≤ stripZeroCountMult T :=
    stripZeroCountMult_mono (by linarith : T₁ ≤ T)
  have hmono2 : stripZeroCountMult (T + 1) ≤ stripZeroCountMult T₂ :=
    stripZeroCountMult_mono (le_of_lt hT₂l)
  have h6T₁ : Real.exp 6 ≤ T₁ := by linarith
  have hT₁₂ : T₁ ≤ T₂ := by linarith
  have hwin := zero_count_window h6T₁ hg₁ hg₂ hT₁₂
  have hθ := theta_increment_upper (T₁ := T₁) (T₂ := T₂)
    (by linarith) hT₁₂
  have hπ3 := Real.pi_gt_three
  have hπ := Real.pi_pos
  have hlogT₂ : Real.log T₂ ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlognn : (0:ℝ) ≤ Real.log (T + 2) := by
    apply Real.log_nonneg
    linarith
  have hθπ : (theta T₂ - theta T₁) / Real.pi
      ≤ (1/2) * Real.log (T + 2) := by
    have hlen : T₂ - T₁ ≤ 3 := by linarith
    have hlog2 : Real.log T₂ ≤ Real.log (T + 2) := hlogT₂
    have hlogpos : (0:ℝ) ≤ Real.log T₂ := by
      apply Real.log_nonneg
      linarith
    have h1 : theta T₂ - theta T₁ ≤ 3 * ((1/2) * Real.log (T + 2)) := by
      calc theta T₂ - theta T₁ ≤ (T₂ - T₁) * ((1/2) * Real.log T₂) := hθ
        _ ≤ 3 * ((1/2) * Real.log T₂) := by nlinarith
        _ ≤ 3 * ((1/2) * Real.log (T + 2)) := by linarith
    rw [div_le_iff₀ hπ]
    nlinarith [h1, hlognn]
  have hcast1 : (stripZeroCountMult T₁ : ℝ) ≤ (stripZeroCountMult T : ℝ) := by
    exact_mod_cast hmono1
  have hcast2 : (stripZeroCountMult (T + 1) : ℝ)
      ≤ (stripZeroCountMult T₂ : ℝ) := by
    exact_mod_cast hmono2
  have hlogchain : 40 * Real.log T₂ ≤ 40 * Real.log (T + 2) := by linarith
  calc (stripZeroCountMult (T + 1) : ℝ) - stripZeroCountMult T
      ≤ (stripZeroCountMult T₂ : ℝ) - stripZeroCountMult T₁ := by
        linarith [hcast1, hcast2]
    _ ≤ (theta T₂ - theta T₁) / Real.pi + 40 * Real.log T₂ + 6 := hwin
    _ ≤ (1/2) * Real.log (T + 2) + 40 * Real.log (T + 2) + 6 := by
        linarith [hθπ, hlogchain]
    _ ≤ 41 * Real.log (T + 2) + 6 := by linarith [hlognn]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.clockRate_upper
#print axioms CriticalLinePhasor.DVP.theta_increment_upper
#print axioms CriticalLinePhasor.DVP.stripZeroCountMult_mono
#print axioms CriticalLinePhasor.DVP.zero_count_window
#print axioms CriticalLinePhasor.DVP.zero_count_unit_window
end AxiomAudit
