import RequestProject.DVPThetaEnclosure

/-!
# The harmonized cell decomposition exists (register-native scaffold)

The clock chart's π-cells — `θ(c (n+1)) − θ(c n) = π` exactly — are
constructed unconditionally: the clock rate has the explicit floor `1/10`
from `t = 10` on (our own explicit Stirling), θ is monotone and unbounded
there, and IVT plus choice builds the decomposition.  This is the scaffold
`clockCellMassBounded_of_uniform` consumes.
-/

open CriticalLinePhasor.CarrierScale Filter Topology

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The explicit clock-rate floor**: `clockRate t ≥ 1/10` for `t ≥ 10`. -/
theorem clockRate_floor {t : ℝ} (ht : 10 ≤ t) : 1/10 ≤ clockRate t := by
  have hπ := Real.pi_pos
  have ht0 : (0:ℝ) < t := by linarith
  have habs : |t| = t := abs_of_pos ht0
  have hmu := mu_stirling_explicit (τ := t) (by rw [habs]; linarith)
  rw [habs] at hmu
  have hcr := CriticalLinePhasor.CarrierScale.clockRate_eq_pi_mul_mu t
  -- log(3/2) ≥ 2/5 via fifth powers
  have hexp25 : Real.exp (2/5) ≤ 3/2 := by
    by_contra hc
    push_neg at hc
    have h5 : Real.exp (2/5) ^ (5:ℕ) = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have he2 : Real.exp 2 ≤ 7.59 := by
      have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have hpow : (3/2:ℝ)^(5:ℕ) < Real.exp (2/5) ^ (5:ℕ) := by
      apply pow_lt_pow_left₀ hc (by norm_num)
      norm_num
    rw [h5] at hpow
    norm_num at hpow
    linarith
  have hmain : (2:ℝ)/5 ≤ Real.log (t / (2 * Real.pi)) := by
    have harg : (3:ℝ)/2 ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d4]
    calc (2:ℝ)/5 ≤ Real.log (3/2) := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          exact hexp25
      _ ≤ Real.log (t / (2 * Real.pi)) :=
          Real.log_le_log (by norm_num) harg
  have herr : (10 / Real.pi) / t^2 ≤ 1/(10 * Real.pi) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have ht2 : (100:ℝ) ≤ t^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht2 hπ.le]
  have hlow := (abs_le.mp hmu).1
  have hmu_low : (1:ℝ)/(10 * Real.pi) ≤ Zeta23.mu t := by
    have hmain2 : (1:ℝ)/(5 * Real.pi)
        ≤ (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) := by
      calc (1:ℝ)/(5 * Real.pi) = (1/(2 * Real.pi)) * (2/5) := by
            field_simp
        _ ≤ (1/(2 * Real.pi)) * Real.log (t / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hmain (by positivity)
    have hhalf : (1:ℝ)/(5 * Real.pi) = 2 * (1/(10 * Real.pi)) := by
      field_simp
      ring
    linarith [hlow, herr, hmain2]
  rw [hcr]
  calc (1:ℝ)/10 = Real.pi * (1/(10 * Real.pi)) := by
        field_simp
    _ ≤ Real.pi * Zeta23.mu t :=
        mul_le_mul_of_nonneg_left hmu_low hπ.le

/-- θ is continuous. -/
theorem continuous_theta : Continuous theta := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (theta_hasDerivAt t).continuousAt

/-- The θ increment over any interval in `[10, ∞)` dominates length/10. -/
theorem theta_increment_floor {a b : ℝ} (ha : 10 ≤ a) (hab : a ≤ b) :
    (b - a)/10 ≤ theta b - theta a := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt theta (clockRate t) t := fun t _ => theta_hasDerivAt t
  have hint : IntervalIntegrable clockRate MeasureTheory.volume a b :=
    continuous_clockRate.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlow : (b - a)/10 ≤ ∫ t in a..b, clockRate t := by
    have hconst : (b - a)/10 = ∫ _ : ℝ in a..b, (1/10 : ℝ) := by
      rw [intervalIntegral.integral_const]
      simp
      ring
    rw [hconst]
    apply intervalIntegral.integral_mono_on hab
      intervalIntegrable_const hint
    intro t ht
    exact clockRate_floor (by linarith [ht.1])
  linarith [hftc, hlow]

/-- θ is monotone on `[10, ∞)`. -/
theorem theta_mono_ten {a b : ℝ} (ha : 10 ≤ a) (hab : a ≤ b) :
    theta a ≤ theta b := by
  have := theta_increment_floor ha hab
  linarith

/-- One harmonized step: from any `a ≥ 10` there is `b ≥ a` with
`θ(b) − θ(a) = π` exactly. -/
theorem exists_gram_step {a : ℝ} (ha : 10 ≤ a) :
    ∃ b : ℝ, a ≤ b ∧ theta b - theta a = Real.pi := by
  have hπ := Real.pi_pos
  have hbig : Real.pi ≤ theta (a + 10 * Real.pi) - theta a := by
    have := theta_increment_floor ha
      (by linarith : a ≤ a + 10 * Real.pi)
    have hlen : (a + 10 * Real.pi - a)/10 = Real.pi := by
      ring
    linarith [this, hlen.symm.le]
  have hcont : ContinuousOn (fun t => theta t - theta a)
      (Set.Icc a (a + 10 * Real.pi)) :=
    (continuous_theta.sub continuous_const).continuousOn
  have hmem : Real.pi ∈ Set.Icc (theta a - theta a)
      (theta (a + 10 * Real.pi) - theta a) := by
    constructor
    · simp
      linarith
    · exact hbig
  obtain ⟨b, hb_mem, hb⟩ := intermediate_value_Icc
    (by linarith : a ≤ a + 10 * Real.pi) hcont hmem
  exact ⟨b, hb_mem.1, hb⟩

/-- **The harmonized (Gram-type) cell decomposition exists**: monotone from
`10`, θ-increment exactly `π` per cell, unbounded. -/
theorem exists_gram_cells :
    ∃ c : ℕ → ℝ, c 0 = 10 ∧ Monotone c ∧ (∀ n, 10 ≤ c n)
      ∧ (∀ n, theta (c (n + 1)) - theta (c n) = Real.pi)
      ∧ Tendsto c atTop atTop := by
  have hπ := Real.pi_pos
  -- the recursion in the subtype
  let step : {x : ℝ // 10 ≤ x} → {x : ℝ // 10 ≤ x} := fun a =>
    ⟨Classical.choose (exists_gram_step a.2),
     le_trans a.2 (Classical.choose_spec (exists_gram_step a.2)).1⟩
  let c' : ℕ → {x : ℝ // 10 ≤ x} := fun n =>
    Nat.rec ⟨10, le_refl 10⟩ (fun _ a => step a) n
  set c : ℕ → ℝ := fun n => (c' n).1 with hc
  have hstep_le : ∀ n, c n ≤ c (n + 1) := fun n =>
    (Classical.choose_spec (exists_gram_step (c' n).2)).1
  have hstep_theta : ∀ n, theta (c (n + 1)) - theta (c n) = Real.pi :=
    fun n => (Classical.choose_spec (exists_gram_step (c' n).2)).2
  have hmono : Monotone c := monotone_nat_of_le_succ hstep_le
  have hten : ∀ n, 10 ≤ c n := fun n => (c' n).2
  have hc0 : c 0 = 10 := rfl
  -- θ along the cells
  have htheta_n : ∀ n, theta (c n) = theta 10 + n * Real.pi := by
    intro n
    induction n with
    | zero => simp [hc0]
    | succ k ih =>
      have := hstep_theta k
      push_cast
      push_cast at ih
      linarith
  -- unbounded
  have htop : Tendsto c atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    rcases le_or_gt M 10 with hM | hM
    · exact ⟨0, fun n _ => le_trans hM (hten n)⟩
    · -- if c n ≤ M for all large n then θ(c n) ≤ θ(M), contradicting linear growth
      by_contra hcon
      push_neg at hcon
      have hbdd : ∀ n : ℕ, ∃ m ≥ n, c m < M := by
        intro n
        obtain ⟨m, hm, hcm⟩ := hcon n
        exact ⟨m, hm, hcm⟩
      have hbdd_all : ∀ n : ℕ, c n < M := by
        intro n
        obtain ⟨m, hmn, hcm⟩ := hbdd n
        exact lt_of_le_of_lt (hmono hmn) hcm
      have hθbdd : ∀ n : ℕ, theta 10 + n * Real.pi ≤ theta M := by
        intro n
        rw [← htheta_n n]
        exact theta_mono_ten (hten n) (le_of_lt (hbdd_all n))
      -- take n large
      obtain ⟨n, hn⟩ := exists_nat_gt ((theta M - theta 10) / Real.pi)
      have := hθbdd n
      rw [div_lt_iff₀ hπ] at hn
      linarith
  exact ⟨c, hc0, hmono, hten, hstep_theta, htop⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.clockRate_floor
#print axioms CriticalLinePhasor.DVP.theta_increment_floor
#print axioms CriticalLinePhasor.DVP.exists_gram_step
#print axioms CriticalLinePhasor.DVP.exists_gram_cells
end AxiomAudit
