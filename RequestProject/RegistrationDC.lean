import RequestProject.RegistrationStations
import RequestProject.DVPBacklund
import RequestProject.DVPThetaIncrement
import RequestProject.ClockRateStirling

/-!
# The DC of the residual law, unconditional (ledger 602)

The residual at a station is `R(t_n) = N(t_n) − n + ½` exactly (601). Its DC is its size: at every
station above `e⁶ + 1`,

  `|R(t_n)| ≤ C · (log(t_n + 1) + 1)`      (`resid_station_abs_le`)

unconditionally — from the argument principle at a good height within one unit of the station
(`stripZeroCountMult_eq_S`, `exists_goodHeight_between`), Backlund's compiled bound
`|S(T)| ≤ 20 log T + 3` (`abs_classicalSContour_le`), the station equation, and the Stirling-grade
clock-rate bound. Consequently the one-per-gap law holds ON AVERAGE: over any run of stations the
net registration defect `(N(t_M) − N(t_{n₀})) − (M − n₀)` is `O(log t_M)` (`net_defect_le`).

What remains for the residual law itself is the AC: the pointwise fluctuation `|R(t_n) − R(t_{n₀})|
< 1`, against this `O(log t)` envelope.
-/

open Complex Finset Filter Topology Set
open CriticalLinePhasor.CarrierScale (theta clockRate continuous_clockRate)

namespace CriticalLinePhasor.ContourArgument

/-- **The argument principle at a good height:** `N(T) = S(T) + 1 + ϑ(T)/π`. -/
theorem stripZeroCountMult_eq_S {T : ℝ} (hT : GoodHeight T) :
    (stripZeroCountMult T : ℝ) = classicalSContour hT + 1 + theta T / Real.pi := by
  have h1 := contourWindingIndex_add_one_eq_stripZeroCountMult hT
  have h2 := classicalSContour_eq_winding_sub_clock hT
  have h1' : ((contourWindingIndex hT : ℤ) : ℝ) + 1 = (stripZeroCountMult T : ℝ) := by
    exact_mod_cast h1
  linarith

/-- The clock moves by at most `|A'| + ½ log(b + 1)` over a unit step above `10`. -/
theorem theta_step_le {A' : ℝ} (hA : ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + (1 / 2) * Real.log t)
    {a b : ℝ} (ha : 10 ≤ a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    theta b - theta a ≤ |A'| + (1 / 2) * Real.log (b + 1) := by
  rw [CriticalLinePhasor.ResidueJump.theta_sub_theta]
  have hlog : 0 ≤ Real.log (b + 1) := Real.log_nonneg (by linarith)
  have hbound : ∀ u ∈ Icc a b, clockRate u ≤ |A'| + (1 / 2) * Real.log (b + 1) := by
    intro u hu
    have h2 : (2:ℝ) ≤ u := by linarith [hu.1]
    have hu1 : Real.log u ≤ Real.log (b + 1) :=
      Real.log_le_log (by linarith) (by linarith [hu.2])
    linarith [hA u h2, le_abs_self A']
  have h : ∫ u in a..b, clockRate u ≤ ∫ u in a..b, (|A'| + (1 / 2) * Real.log (b + 1)) :=
    intervalIntegral.integral_mono_on hab (continuous_clockRate.intervalIntegrable _ _)
      intervalIntegrable_const hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have hK : 0 ≤ |A'| + (1 / 2) * Real.log (b + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show b - a ≤ 1 by linarith) hK]

/-- **The DC of the residual law with its explicit constant:** `|R(t_n)| ≤ (24 + |A'| + B)(log(t_n+1)+1)`
at every station above `e⁶ + 1`, for any `A'` with `clockRate t ≤ A' + ½ log t` on `t ≥ 2`. -/
theorem resid_station_abs_le' {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) {A' : ℝ}
    (hA : ∀ t : ℝ, 2 ≤ t → clockRate t ≤ A' + (1 / 2) * Real.log t)
    {n : ℕ} (hn : regClock strain 10 < stationLevel n) (ht : Real.exp 6 + 1 ≤ station strain n) :
    |resid strain (station strain n)| ≤ (24 + |A'| + B) * (Real.log (station strain n + 1) + 1) := by
  set t := station strain n with htdef
  obtain ⟨h10, hG⟩ := station_spec hs hB hn
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hπ := Real.pi_pos
  have hπ1 : 1 / Real.pi ≤ 1 := by
    rw [div_le_one hπ]; linarith [Real.pi_gt_three]
  have hlog0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith [Real.exp_pos 6])
  have hlogt : Real.log t ≤ Real.log (t + 1) := Real.log_le_log (by linarith [Real.exp_pos 6]) (by linarith)
  have he6 : 0 < Real.exp 6 := Real.exp_pos 6
  have he6' : (16:ℝ) ≤ Real.exp 6 := by
    rw [show (6:ℝ) = 3 + 3 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (3:ℝ)]
  -- the station equation: ϑ(t)/π = n − 3/2 − Ŝ(t)
  have hθ : theta t / Real.pi = (n : ℝ) - 3 / 2 - strain t := by
    unfold regClock stationLevel at hG; linarith
  have hst := abs_le.1 (hB t)
  rw [resid_station hs hB hn]
  rw [abs_le]
  constructor
  · -- lower bound via a good height in (t − 1, t)
    obtain ⟨T, hT1, hT2, hgood⟩ := CriticalLinePhasor.DVP.exists_goodHeight_between
      (show (0:ℝ) < t - 1 by linarith)
    have hNle : (stripZeroCountMult T : ℝ) ≤ stripZeroCountMult t := by
      exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg (stripZeroFinset_mono (by linarith))
        (fun _ _ _ => Nat.zero_le _)
    have hS := CriticalLinePhasor.DVP.abs_classicalSContour_le (by linarith) hgood
    have hN := stripZeroCountMult_eq_S hgood
    have hstep := theta_step_le hA (show 10 ≤ T by linarith) (show T ≤ t by linarith)
      (show t ≤ T + 1 by linarith)
    have hlogT : Real.log T ≤ Real.log (t + 1) := Real.log_le_log (by linarith) (by linarith)
    have hSlow : -(20 * Real.log T + 3) ≤ classicalSContour hgood := (abs_le.1 hS).1
    -- θ(T)/π ≥ θ(t)/π − (|A'| + ½ log(t+1))/π ≥ θ(t)/π − (|A'| + ½ log(t+1))
    have hθT : theta t / Real.pi - (|A'| + (1 / 2) * Real.log (t + 1)) ≤ theta T / Real.pi := by
      have h1 : theta t - (|A'| + (1 / 2) * Real.log (t + 1)) ≤ theta T := by linarith
      have h2 : (theta t - (|A'| + (1 / 2) * Real.log (t + 1))) / Real.pi ≤ theta T / Real.pi :=
        div_le_div_of_nonneg_right h1 hπ.le
      have h3 : (|A'| + (1 / 2) * Real.log (t + 1)) / Real.pi ≤ |A'| + (1 / 2) * Real.log (t + 1) := by
        rw [div_le_iff₀ hπ]; nlinarith [abs_nonneg A', Real.pi_gt_three]
      have h4 : (theta t - (|A'| + (1 / 2) * Real.log (t + 1))) / Real.pi
          = theta t / Real.pi - (|A'| + (1 / 2) * Real.log (t + 1)) / Real.pi := by ring
      linarith
    nlinarith [hlog0, abs_nonneg A']
  · -- upper bound via a good height in (t, t + 1)
    obtain ⟨T, hT1, hT2, hgood⟩ := CriticalLinePhasor.DVP.exists_goodHeight_between
      (show (0:ℝ) < t by linarith)
    have hNle : (stripZeroCountMult t : ℝ) ≤ stripZeroCountMult T := by
      exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg (stripZeroFinset_mono hT1.le)
        (fun _ _ _ => Nat.zero_le _)
    have hS := CriticalLinePhasor.DVP.abs_classicalSContour_le (by linarith) hgood
    have hN := stripZeroCountMult_eq_S hgood
    have hstep := theta_step_le hA h10 hT1.le (show T ≤ t + 1 by linarith)
    have hlogT : Real.log T ≤ Real.log (t + 1) := Real.log_le_log (by linarith) (by linarith)
    have hSup : classicalSContour hgood ≤ 20 * Real.log T + 3 := (abs_le.1 hS).2
    have hθT : theta T / Real.pi ≤ theta t / Real.pi + (|A'| + (1 / 2) * Real.log (T + 1)) := by
      have h1 : theta T ≤ theta t + (|A'| + (1 / 2) * Real.log (T + 1)) := by linarith
      have h2 : theta T / Real.pi ≤ (theta t + (|A'| + (1 / 2) * Real.log (T + 1))) / Real.pi :=
        div_le_div_of_nonneg_right h1 hπ.le
      have h3 : (|A'| + (1 / 2) * Real.log (T + 1)) / Real.pi ≤ |A'| + (1 / 2) * Real.log (T + 1) := by
        rw [div_le_iff₀ hπ]
        have : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
        nlinarith [abs_nonneg A', Real.pi_gt_three]
      have h4 : (theta t + (|A'| + (1 / 2) * Real.log (T + 1))) / Real.pi
          = theta t / Real.pi + (|A'| + (1 / 2) * Real.log (T + 1)) / Real.pi := by ring
      linarith
    have hlogT1 : Real.log (T + 1) ≤ Real.log (t + 2) := Real.log_le_log (by linarith) (by linarith)
    have hlogt2 : Real.log (t + 2) ≤ Real.log (t + 1) + 1 := by
      have : Real.log (t + 2) - Real.log (t + 1) = Real.log ((t + 2) / (t + 1)) := by
        rw [Real.log_div (by linarith) (by linarith)]
      have h2 : Real.log ((t + 2) / (t + 1)) ≤ (t + 2) / (t + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : (t + 2) / (t + 1) - 1 ≤ 1 := by
        rw [div_sub_one (by linarith), div_le_one (by linarith)]; linarith
      linarith
    nlinarith [hlog0, abs_nonneg A']

/-- **The DC of the residual law: `|R(t_n)| = O(log t_n)` at every station, unconditionally.** -/
theorem resid_station_abs_le {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain)
    (hB : ∀ t, |strain t| ≤ B) :
    ∃ C : ℝ, ∀ n : ℕ, regClock strain 10 < stationLevel n →
      Real.exp 6 + 1 ≤ station strain n →
      |resid strain (station strain n)| ≤ C * (Real.log (station strain n + 1) + 1) := by
  obtain ⟨A', hA⟩ := CriticalLinePhasor.CarrierScale.clockRate_log_bound_half
  exact ⟨24 + |A'| + B, fun n hn ht => resid_station_abs_le' hs hB hA hn ht⟩

/-- **The one-per-gap law holds on average, unconditionally**: over any run of stations the net
registration defect is `O(log t_M)`. -/
theorem net_defect_le {strain : ℝ → ℝ} {B : ℝ} (hs : Continuous strain) (hB : ∀ t, |strain t| ≤ B) :
    ∃ C : ℝ, ∀ n₀ M : ℕ, regClock strain 10 < stationLevel n₀ → n₀ ≤ M →
      Real.exp 6 + 1 ≤ station strain n₀ →
      |((stripZeroCountMult (station strain M) : ℝ) - stripZeroCountMult (station strain n₀))
          - ((M : ℝ) - n₀)|
        ≤ C * (Real.log (station strain M + 1) + 1) := by
  obtain ⟨C, hC⟩ := resid_station_abs_le hs hB
  refine ⟨2 * |C|, ?_⟩
  intro n₀ M hn₀ hM ht₀
  have hnM : regClock strain 10 < stationLevel M := lt_of_lt_of_le hn₀ (stationLevel_mono hM)
  have hmono : station strain n₀ ≤ station strain M := by
    have := (station_strictMono hs hB hn₀).monotone (Nat.zero_le (M - n₀))
    simp only [add_zero] at this
    rwa [show n₀ + (M - n₀) = M by omega] at this
  have htM : Real.exp 6 + 1 ≤ station strain M := le_trans ht₀ hmono
  have h1 := hC n₀ hn₀ ht₀
  have h2 := hC M hnM htM
  rw [resid_station hs hB hn₀] at h1
  rw [resid_station hs hB hnM] at h2
  have hlog : Real.log (station strain n₀ + 1) ≤ Real.log (station strain M + 1) :=
    Real.log_le_log (by linarith [Real.exp_pos 6]) (by linarith)
  have hlog0 : 0 ≤ Real.log (station strain M + 1) :=
    Real.log_nonneg (by linarith [Real.exp_pos 6])
  have hCle : C ≤ |C| := le_abs_self C
  have hCnn : 0 ≤ |C| := abs_nonneg C
  have hlog0' : 0 ≤ Real.log (station strain n₀ + 1) :=
    Real.log_nonneg (by linarith [Real.exp_pos 6])
  have e1 : C * (Real.log (station strain n₀ + 1) + 1) ≤ |C| * (Real.log (station strain M + 1) + 1) :=
    calc C * (Real.log (station strain n₀ + 1) + 1)
        ≤ |C| * (Real.log (station strain n₀ + 1) + 1) :=
          mul_le_mul_of_nonneg_right hCle (by linarith)
      _ ≤ |C| * (Real.log (station strain M + 1) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hCnn
  have e2 : C * (Real.log (station strain M + 1) + 1) ≤ |C| * (Real.log (station strain M + 1) + 1) :=
    mul_le_mul_of_nonneg_right hCle (by linarith)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.stripZeroCountMult_eq_S
#print axioms CriticalLinePhasor.ContourArgument.resid_station_abs_le'
#print axioms CriticalLinePhasor.ContourArgument.resid_station_abs_le
#print axioms CriticalLinePhasor.ContourArgument.net_defect_le
