import RequestProject.RegistrationMaster
import RequestProject.FejerTail

/-!
# Flux conservation, the run identity, and the near/far split of the boundary term (ledger 612)

* **`boundaryTerm_add`**: the boundary term is additive over adjacent gaps — the flux of a run of gaps
  is the flux through its two ends. So `boundaryTerm L a b = Φ(b) − Φ(a)` for a registration
  potential `Φ` (the sharp count minus the Fejér-smoothed count), and the count over a run of `k`
  station gaps of the fixed-scale clock is `k` plus the remainder plus the boundary term of the
  whole run (**`run_count`**): the net defect over any run is an end effect, not a sum of per-gap
  defects.
* **`boundaryTerm_split`**: at any distance `D > 0`, the boundary term is the near part (the count
  minus the weights of the zeros within `D` of the gap, finitely many) minus the weights of the far
  zeros. An on-line zero at distance `dist > 0` from the gap has weight at most
  `(2(b − a)/(πL)) / dist²` (**`gapWeight_le_of_far`**), and the far second moment
  `Σ' m_ρ / max(dist, D)²` is summable (**`summable_far_moment`**).
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-! ## 1. Summability and additivity of the weights -/

theorem rieszKernel_re_integrableOn_Ioc {L : ℝ} (hL : 0 < L) {ρ : ℂ} (hρ : ρ.re ≤ 1) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => (rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re) (Ioc a b) := by
  obtain ⟨M, hM⟩ := rieszKernel_re_bound_fixed hL ρ hρ
  apply Measure.integrableOn_of_bounded (M := M)
  · simp
  · exact (rieszKernel_re_measurable L ρ).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hM t)

theorem rieszKernel_re_intervalIntegrable {L : ℝ} (hL : 0 < L) {ρ : ℂ} (hρ : ρ.re ≤ 1) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re) volume a b :=
  ⟨rieszKernel_re_integrableOn_Ioc hL hρ a b, rieszKernel_re_integrableOn_Ioc hL hρ b a⟩

/-- Gap weights add over adjacent gaps. -/
theorem gapWeight_add {L : ℝ} (hL : 0 < L) (a b c : ℝ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    gapWeight L a b ρ + gapWeight L b c ρ = gapWeight L a c ρ := by
  unfold gapWeight
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
    (rieszKernel_re_intervalIntegrable hL hρ a b) (rieszKernel_re_intervalIntegrable hL hρ b c)]

theorem summable_weights {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a b ρ.val) := by
  refine Summable.of_norm_bounded ((summable_integral_norm_weight hL hab).mul_left (1 / Real.pi)) ?_
  intro ρ
  have h : (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a b ρ.val
      = (1 / Real.pi) * ∫ t in Ioc a b,
          (ZD.xiOrderNat ρ.val : ℝ) * (rieszKernel L (ρ.val - (1 / 2 + (t : ℂ) * I))).re := by
    unfold gapWeight
    rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    ring
  rw [h, norm_mul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.pi)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

theorem bandCountMult_add3 {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    bandCountMult a b + bandCountMult b c = bandCountMult a c := by
  have h1 := bandCountMult_add hab
  have h2 := bandCountMult_add hbc
  have h3 := bandCountMult_add (hab.trans hbc)
  omega

/-- **Flux conservation: the boundary term is additive over adjacent gaps.** -/
theorem boundaryTerm_add {L : ℝ} (hL : 0 < L) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    boundaryTerm L a b + boundaryTerm L b c = boundaryTerm L a c := by
  unfold boundaryTerm
  have h := bandCountMult_add3 hab hbc
  have hs1 := summable_weights hL hab
  have hs2 := summable_weights hL hbc
  have hsum : ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a c ρ.val
      = ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L a b ρ.val
        + ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * gapWeight L b c ρ.val := by
    rw [← hs1.tsum_add hs2]
    refine tsum_congr (fun ρ => ?_)
    rw [← mul_add, gapWeight_add hL a b c ρ.2.2.1.le]
  rw [hsum, ← h]
  push_cast
  ring

/-! ## 2. The run identity -/

/-- **Over `k` consecutive station gaps of the fixed-scale clock the count is `k` plus the
integrated remainder plus the boundary term of the whole run.** -/
theorem run_count {L : ℝ} (hL : 0 < L) {B : ℝ} (hB : ∀ t, |rieszStrain L t| ≤ B)
    {n : ℕ} (hn : regClock (rieszStrain L) 10 < stationLevel n) (k : ℕ) :
    (bandCountMult (station (rieszStrain L) n) (station (rieszStrain L) (n + k)) : ℝ)
      = k + (1 / Real.pi) * (∫ t in station (rieszStrain L) n..station (rieszStrain L) (n + k),
            rieszRemainder L t)
        + boundaryTerm L (station (rieszStrain L) n) (station (rieszStrain L) (n + k)) := by
  have hs := rieszStrain_continuous L
  have hnk : regClock (rieszStrain L) 10 < stationLevel (n + k) :=
    lt_of_lt_of_le hn (stationLevel_mono (by omega))
  obtain ⟨ha10, hGa⟩ := station_spec hs hB hn
  obtain ⟨hb10, hGb⟩ := station_spec hs hB hnk
  have hab : station (rieszStrain L) n ≤ station (rieszStrain L) (n + k) := by
    have hm := (station_strictMono hs hB hn).monotone (Nat.zero_le k)
    simpa using hm
  have hid := count_identity hL (by linarith : (0:ℝ) < station (rieszStrain L) n) hab
  unfold regClock stationLevel at hGa hGb
  rw [hid]
  push_cast at hGb
  have : (theta (station (rieszStrain L) (n + k)) - theta (station (rieszStrain L) n)) / Real.pi
      = theta (station (rieszStrain L) (n + k)) / Real.pi
        - theta (station (rieszStrain L) n) / Real.pi := by ring
  linarith

/-! ## 3. Near and far zeros -/

/-- The distance from an ordinate to the interval `[a, b]`. -/
noncomputable def gapDist (a b γ : ℝ) : ℝ := max (a - γ) (max (γ - b) 0)

theorem gapDist_nonneg (a b γ : ℝ) : 0 ≤ gapDist a b γ :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem gapDist_le_left {a b γ : ℝ} : a - γ ≤ gapDist a b γ := le_max_left _ _
theorem gapDist_le_right {a b γ : ℝ} : γ - b ≤ gapDist a b γ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- A zero at positive distance from the gap lies outside it, on one side. -/
theorem gapDist_pos_cases {a b γ : ℝ} (h : 0 < gapDist a b γ) : γ < a ∨ b < γ := by
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  unfold gapDist at h
  have : max (a - γ) (max (γ - b) 0) ≤ 0 :=
    max_le (by linarith) (max_le (by linarith) le_rfl)
  linarith

theorem gapDist_eq_of_left {a b γ : ℝ} (hab : a ≤ b) (h : γ < a) : gapDist a b γ = a - γ := by
  unfold gapDist
  apply max_eq_left
  apply max_le <;> linarith

theorem gapDist_eq_of_right {a b γ : ℝ} (hab : a ≤ b) (h : b < γ) : gapDist a b γ = γ - b := by
  unfold gapDist
  rw [max_eq_right (by apply le_max_of_le_left; linarith), max_eq_left (by linarith)]

/-- The near zeros are finitely many. -/
theorem near_finite (a b D : ℝ) : {ρ : Zero | gapDist a b ρ.val.im < D}.Finite := by
  set R : ℝ := |a| + |b| + |D| + 1
  apply Set.Finite.subset
    ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite R).preimage Subtype.val_injective.injOn)
  intro ρ hρ
  simp only [Set.mem_ofPred_eq] at hρ
  show ρ.val ∈ ZD.NontrivialZeros ∩ Metric.closedBall (0 : ℂ) R
  refine ⟨ρ.2, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre0 : 0 ≤ ρ.val.re := ρ.2.1.le
  have hre1 : ρ.val.re ≤ 1 := ρ.2.2.1.le
  have h1 : a - ρ.val.im < D := lt_of_le_of_lt gapDist_le_left hρ
  have h2 : ρ.val.im - b < D := lt_of_le_of_lt gapDist_le_right hρ
  have him : |ρ.val.im| ≤ |a| + |b| + |D| := by
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg D, le_abs_self a,
      neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self D, neg_abs_le D]
  calc ‖ρ.val‖ ≤ |ρ.val.re| + |ρ.val.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 + (|a| + |b| + |D|) := by
        apply add_le_add _ him
        rw [abs_of_nonneg hre0]; exact hre1
    _ = R := by ring

/-- **The near/far split of the boundary term.** -/
theorem boundaryTerm_split {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) (D : ℝ) :
    boundaryTerm L a b
      = ((bandCountMult a b : ℝ)
          - ∑' ρ : {ρ : Zero | gapDist a b ρ.val.im < D},
              (ZD.xiOrderNat ρ.val.val : ℝ) * gapWeight L a b ρ.val.val)
        - ∑' ρ : ↑({ρ : Zero | gapDist a b ρ.val.im < D}ᶜ),
              (ZD.xiOrderNat ρ.val.val : ℝ) * gapWeight L a b ρ.val.val := by
  unfold boundaryTerm
  rw [← (summable_weights hL hab).tsum_subtype_add_tsum_subtype_compl
    {ρ : Zero | gapDist a b ρ.val.im < D}]
  ring

/-! ## 4. The far part for on-line zeros -/

/-- Outside zero to the left, second-moment form. -/
theorem gapWeight_le_of_left_sq {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (ha : ρ.im < a) :
    gapWeight L a b ρ ≤ (2 * (b - a) / (π * L)) * (1 / (a - ρ.im) ^ 2) := by
  rw [gapWeight_eq_fejer hL a b hρ]
  have hπ := Real.pi_pos
  have hpt : ∀ t ∈ Set.Icc a b, fejer L (ρ.im - t) ≤ 2 / (L * (a - ρ.im) ^ 2) := by
    intro t ht
    have hne : ρ.im - t ≠ 0 := by linarith [ht.1]
    calc fejer L (ρ.im - t) ≤ 2 / (L * (ρ.im - t) ^ 2) := fejer_le hL hne
      _ ≤ 2 / (L * (a - ρ.im) ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hL.le
          rw [show (ρ.im - t) ^ 2 = (t - ρ.im) ^ 2 by ring]
          apply pow_le_pow_left₀ (by linarith) (by linarith [ht.1])
  have hmono := intervalIntegral.integral_mono_on hab
    ((fejer_integrable hL).comp_sub_left ρ.im).intervalIntegrable
    intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  calc (1 / π) * ∫ t in a..b, fejer L (ρ.im - t)
      ≤ (1 / π) * ((b - a) * (2 / (L * (a - ρ.im) ^ 2))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (2 * (b - a) / (π * L)) * (1 / (a - ρ.im) ^ 2) := by
        have : a - ρ.im ≠ 0 := by linarith
        field_simp

/-- An on-line zero at positive distance from the gap: `w ≤ (2(b − a)/(πL)) / dist²`. -/
theorem gapWeight_le_of_far {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) (hfar : 0 < gapDist a b ρ.im) :
    gapWeight L a b ρ ≤ (2 * (b - a) / (π * L)) * (1 / gapDist a b ρ.im ^ 2) := by
  rcases gapDist_pos_cases hfar with h | h
  · rw [gapDist_eq_of_left hab h]; exact gapWeight_le_of_left_sq hL hab hρ h
  · rw [gapDist_eq_of_right hab h]; exact gapWeight_le_of_right_sq hL hab hρ h

/-- The far second moment `Σ' m_ρ / max(dist, D)²` is summable. -/
theorem summable_far_moment {a b D : ℝ} (hD : 0 < D) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℝ) / max (gapDist a b ρ.val.im) D ^ 2) := by
  set R : ℝ := 2 * (|a| + |b| + 1)
  have hg : Summable (fun ρ : Zero => 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left 4
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [CriticalLinePhasor.StBridge.eventually_cofinite_norm_ge R] with ρ hρR
  have hre0 : 0 ≤ ρ.val.re := ρ.2.1.le
  have hre1 : ρ.val.re ≤ 1 := ρ.2.2.1.le
  -- `dist ≥ |γ| − (|a| + |b|) ≥ ‖ρ‖/2`
  have hnorm : ‖ρ.val‖ ≤ 1 + |ρ.val.im| := by
    calc ‖ρ.val‖ ≤ |ρ.val.re| + |ρ.val.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |ρ.val.im| := by rw [abs_of_nonneg hre0]; linarith
  have hdist : ‖ρ.val‖ / 2 ≤ gapDist a b ρ.val.im := by
    rcases le_or_gt 0 ρ.val.im with hγ | hγ
    · rw [abs_of_nonneg hγ] at hnorm
      have := gapDist_le_right (a := a) (b := b) (γ := ρ.val.im)
      nlinarith [le_abs_self b, abs_nonneg a]
    · rw [abs_of_neg hγ] at hnorm
      have := gapDist_le_left (a := a) (b := b) (γ := ρ.val.im)
      nlinarith [neg_abs_le a, abs_nonneg b]
  have hmax : ‖ρ.val‖ / 2 ≤ max (gapDist a b ρ.val.im) D := hdist.trans (le_max_left _ _)
  have hpos : 0 < ‖ρ.val‖ := by
    have : (0:ℝ) < R := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have hsq : (‖ρ.val‖ / 2) ^ 2 ≤ max (gapDist a b ρ.val.im) D ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmax 2
  calc (ZD.xiOrderNat ρ.val : ℝ)
      = 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) * (‖ρ.val‖ / 2) ^ 2 := by
        field_simp
        ring
    _ ≤ 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) * max (gapDist a b ρ.val.im) D ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.boundaryTerm_add
#print axioms CriticalLinePhasor.ContourArgument.run_count
#print axioms CriticalLinePhasor.ContourArgument.boundaryTerm_split
