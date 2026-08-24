import RequestProject.ClockRateStirling
import RequestProject.ZetaContourArgument
import RequestProject.DVPBacklund

/-!
# The θ-increment lower bound

The last analytic brick of the RvM lower-density chain: the clock
`θ(t) = ∫₀ᵗ clockRate` grows at least at the Stirling rate.  Everything is
retrieval: `clockRate = π·μ` (compiled), `mu_stirling` two-sided with the
constant existential (Zeta23 path dependency, compiled), and
`theta_hasDerivAt` (compiled).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.CarrierScale

/-- The clock rate's Stirling FLOOR: `½·log(t/2π) − C₀/t² ≤ clockRate t`
for `t ≥ 1`, the mirror of the compiled ceiling. -/
theorem clockRate_ge_half_log :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ t : ℝ, 1 ≤ t →
      (1/2) * Real.log (t/(2*Real.pi)) - C₀/t^2 ≤ clockRate t := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  have hπ := Real.pi_pos
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have h0 := abs_nonneg
      (Zeta23.mu 1 - (1 / (2 * Real.pi)) * Real.log (|(1 : ℝ)| / (2 * Real.pi)))
    simp only [one_pow, div_one] at h
    linarith
  refine ⟨Real.pi * C, by positivity, fun t ht => ?_⟩
  have ht0 : (0:ℝ) < t := by linarith
  have habs : (1:ℝ) ≤ |t| := by rw [abs_of_pos ht0]; exact ht
  have hmu : (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) - C / t^2
      ≤ Zeta23.mu t := by
    have h := (abs_le.mp (hC t habs)).1
    rw [abs_of_pos ht0] at h
    linarith
  calc (1/2) * Real.log (t/(2*Real.pi)) - (Real.pi * C)/t^2
      = Real.pi * ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
        - C / t^2) := by
        field_simp
    _ ≤ Real.pi * Zeta23.mu t :=
        mul_le_mul_of_nonneg_left hmu hπ.le
    _ = clockRate t := (clockRate_eq_pi_mul_mu t).symm

/-- **The θ-increment lower bound**: for `1 ≤ T` and `0 ≤ Δ`,
`θ(T+Δ) − θ(T) ≥ Δ·(½·log(T/2π) − C₀/T²)`. -/
theorem theta_increment_ge :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ T Δ : ℝ, 1 ≤ T → 0 ≤ Δ →
      Δ * ((1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2)
        ≤ theta (T + Δ) - theta T := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := clockRate_ge_half_log
  refine ⟨C₀, hC₀0, fun T Δ hT hΔ => ?_⟩
  have hT0 : (0:ℝ) < T := by linarith
  -- the increment is the integral of the rate
  have hint : theta (T + Δ) - theta T
      = ∫ u in T..(T + Δ), clockRate u := by
    rw [theta, theta]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := 0) (b := T) (c := T + Δ)
      (continuous_clockRate.intervalIntegrable 0 T)
      (continuous_clockRate.intervalIntegrable T (T + Δ))]
    ring
  rw [hint]
  -- the rate is bounded below on the window by its value-shape at T
  have hrate : ∀ u ∈ Set.uIcc T (T + Δ),
      (1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2 ≤ clockRate u := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    have hu1 : 1 ≤ u := by linarith [hu.1]
    have hu0 : (0:ℝ) < u := by linarith
    calc (1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2
        ≤ (1/2) * Real.log (u/(2*Real.pi)) - C₀/u^2 := by
          have hlog : Real.log (T/(2*Real.pi)) ≤ Real.log (u/(2*Real.pi)) := by
            apply Real.log_le_log (by positivity)
            apply div_le_div_of_nonneg_right _ (by positivity)
            linarith [hu.1]
          have hCdiv : C₀/u^2 ≤ C₀/T^2 := by
            apply div_le_div_of_nonneg_left hC₀0 (by positivity)
            nlinarith [hu.1]
          linarith
      _ ≤ clockRate u := hC₀ u hu1
  calc Δ * ((1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2)
      = ∫ _ in T..(T + Δ),
          ((1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ ∫ u in T..(T + Δ), clockRate u := by
        apply intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const
          (continuous_clockRate.intervalIntegrable _ _)
        intro u hu
        apply hrate
        rw [Set.uIcc_of_le (by linarith)]
        exact hu

open CriticalLinePhasor.ContourArgument in
/-- Good heights exist in every unit interval above `0`: the bad heights
(zero ordinates) in a bounded window are finite. -/
theorem exists_goodHeight_between {a : ℝ} (ha : 0 < a) :
    ∃ T : ℝ, a < T ∧ T < a + 1 ∧ GoodHeight T := by
  have hfin : {t : ℝ | ∃ ρ ∈ ZD.NontrivialZeros, ρ.im = t}
      ∩ Set.Ioo a (a+1) |>.Finite := by
    apply Set.Finite.subset
      ((ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (a + 2)).image
        Complex.im)
    rintro t ⟨⟨ρ, hρ, hρt⟩, htIoo⟩
    refine ⟨ρ, ⟨hρ, ?_⟩, hρt⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + (a + 1) := by
          apply add_le_add
          · rw [abs_of_pos hρ.1]
            exact le_of_lt hρ.2.1
          · rw [hρt, abs_of_pos (by linarith [htIoo.1])]
            linarith [htIoo.2]
      _ ≤ a + 2 := by linarith
  have hIoo : (Set.Ioo a (a+1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨T, hT⟩ := (hIoo.diff hfin).nonempty
  rw [Set.mem_diff] at hT
  obtain ⟨hTIoo, hTbad⟩ := hT
  refine ⟨T, hTIoo.1, hTIoo.2, ⟨by linarith [hTIoo.1], ?_⟩⟩
  intro ρ hρ hρT
  apply hTbad
  exact ⟨⟨ρ, hρ, hρT⟩, hTIoo⟩

open CriticalLinePhasor.ContourArgument in
/-- The census count in real form: `N(T) = S(T) + θ(T)/π + 1`. -/
theorem stripCount_real_eq {T : ℝ} (hT : GoodHeight T) :
    (stripZeroCountMult T : ℝ)
      = classicalSContour hT + theta T / Real.pi + 1 := by
  have h1 := contourWindingIndex_add_one_eq_stripZeroCountMult hT
  have h2 := classicalSContour_eq_winding_sub_clock hT
  have h1' : ((contourWindingIndex hT : ℝ)) + 1 = (stripZeroCountMult T : ℝ) := by
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) h1
  linarith

set_option maxHeartbeats 3200000 in
open CriticalLinePhasor.ContourArgument in
/-- **THE LOWER DENSITY**: above an explicit threshold, every height has a
zero of ζ within `300` — the RvM chain assembled: census algebra + the
S-bound + the θ-increment. -/
theorem exists_zero_near_height :
    ∃ T₀ : ℝ, ∀ a : ℝ, T₀ ≤ a →
      ∃ ρ ∈ ZD.NontrivialZeros, 0 < ρ.im ∧ |ρ.im - a| ≤ 300 := by
  obtain ⟨C₀, hC₀0, hθ⟩ := theta_increment_ge
  refine ⟨max (Real.exp 18 + 151) (297 * C₀ + 152), fun a ha => ?_⟩
  have haE : Real.exp 18 + 151 ≤ a := le_trans (le_max_left _ _) ha
  have haC : 297 * C₀ + 152 ≤ a := le_trans (le_max_right _ _) ha
  have hE18 : (400:ℝ) ≤ Real.exp 18 := by
    have h6 : Real.exp 6 ≤ Real.exp 18 := Real.exp_le_exp.mpr (by norm_num)
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h6' : Real.exp 6 = (Real.exp 1 * Real.exp 1)
        * (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) := by
      rw [show (6:ℝ) = 1+1+(1+1)+(1+1) by norm_num]
      simp only [Real.exp_add]
    nlinarith [he2, Real.exp_pos 1]
  -- the two good heights
  obtain ⟨T, hTl, hTu, hT⟩ := exists_goodHeight_between
    (a := a - 150) (by linarith)
  obtain ⟨T', hTl', hTu', hT'⟩ := exists_goodHeight_between
    (a := a + 148) (by linarith)
  have hTT' : T < T' := by linarith
  have hΔl : (297:ℝ) ≤ T' - T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hTbig : Real.exp 18 ≤ T := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hT'pos : (0:ℝ) < T' := by linarith
  have hL18 : (18:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 18) hTbig
    rwa [Real.log_exp] at this
  have hLpos : (0:ℝ) < Real.log T := by linarith
  -- the S bounds
  have hTe6 : Real.exp 6 ≤ T := by
    have : Real.exp 6 ≤ Real.exp 18 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hT'e6 : Real.exp 6 ≤ T' := by linarith
  have hS := abs_classicalSContour_le hTe6 hT
  have hS' := abs_classicalSContour_le hT'e6 hT'
  -- log T' ≤ log T + 1
  have hlogT' : Real.log T' ≤ Real.log T + 1 := by
    have h1 : T' ≤ T + 300 := by linarith
    have h2 : Real.log T' ≤ Real.log (T + 300) :=
      Real.log_le_log hT'pos h1
    have h3 : Real.log (T + 300) = Real.log T + Real.log (1 + 300/T) := by
      rw [← Real.log_mul hTpos.ne' (by positivity)]
      congr 1
      field_simp
    have h4 : Real.log (1 + 300/T) ≤ 300/T :=
      le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
    have h5 : (300:ℝ)/T ≤ 1 := by
      rw [div_le_one hTpos]
      linarith
    linarith
  -- the θ increment
  have hθinc := hθ T (T' - T) hT1 (by linarith)
  rw [show T + (T' - T) = T' by ring] at hθinc
  -- the count difference is positive
  have hcount : (stripZeroCountMult T : ℝ) < (stripZeroCountMult T' : ℝ) := by
    rw [stripCount_real_eq hT, stripCount_real_eq hT']
    have hπ := Real.pi_pos
    have hπ315 : Real.pi < 3.15 := by
      have := Real.pi_lt_d4
      linarith
    -- suffices: θ' − θ > π·(S − S')
    have hkey : theta T' - theta T
        > Real.pi * (classicalSContour hT - classicalSContour hT') := by
      have hlog2π : Real.log (2*Real.pi) ≤ 2 := by
        have h1 : 2*Real.pi ≤ Real.exp 2 := by
          have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
            nlinarith [Real.exp_one_gt_d9]
          have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [← Real.exp_add]
            norm_num
          nlinarith
        calc Real.log (2*Real.pi) ≤ Real.log (Real.exp 2) :=
            Real.log_le_log (by positivity) h1
          _ = 2 := Real.log_exp 2
      have hlogsplit : Real.log (T/(2*Real.pi))
          = Real.log T - Real.log (2*Real.pi) := by
        rw [Real.log_div hTpos.ne' (by positivity)]
      have hC₀T : 297 * (C₀/T^2) ≤ 1 := by
        rcases eq_or_lt_of_le hC₀0 with h0 | hpos
        · rw [← h0]
          norm_num
        · have hTC : 297 * C₀ + 1 ≤ T := by linarith
          have hT2 : 297 * C₀ ≤ T := by linarith
          rw [show 297 * (C₀/T^2) = (297*C₀)/T^2 by ring]
          rw [div_le_one (by positivity)]
          nlinarith
      have hSb := abs_le.mp hS
      have hS'b := abs_le.mp hS'
      calc theta T' - theta T
          ≥ 297 * ((1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2) := by
            have h297 : (297:ℝ) ≤ T' - T := hΔl
            have hbr : (0:ℝ) ≤ (1/2) * Real.log (T/(2*Real.pi)) - C₀/T^2 := by
              rw [hlogsplit]
              nlinarith
            nlinarith [hθinc, mul_le_mul_of_nonneg_right h297 hbr]
        _ = 148.5 * Real.log T - 148.5 * Real.log (2*Real.pi)
            - 297 * (C₀/T^2) := by
            rw [hlogsplit]
            ring
        _ > Real.pi * (classicalSContour hT - classicalSContour hT') := by
            have hle : Real.pi * (classicalSContour hT - classicalSContour hT')
                ≤ 3.15 * ((20 * Real.log T + 3) + (20 * Real.log T' + 3)) := by
              have h1 : classicalSContour hT - classicalSContour hT'
                  ≤ (20 * Real.log T + 3) + (20 * Real.log T' + 3) := by
                linarith [hSb.2, hS'b.1]
              have h2 : (0:ℝ) ≤ (20 * Real.log T + 3)
                  + (20 * Real.log T' + 3) := by
                have : (0:ℝ) ≤ Real.log T' := by
                  have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T')
                  linarith
                nlinarith
              nlinarith
            have h3 : 3.15 * ((20 * Real.log T + 3) + (20 * Real.log T' + 3))
                ≤ 126 * Real.log T + 3.15 * (20 * (Real.log T + 1) + 6)
                  - 63 * Real.log T + 63 * Real.log T := by
              nlinarith [hlogT']
            nlinarith [hlogT', hlog2π, hC₀T, hL18]
    have hdiv : classicalSContour hT - classicalSContour hT'
        < (theta T' - theta T) / Real.pi := by
      rw [lt_div_iff₀ hπ]
      nlinarith [hkey]
    have hsplit : (theta T' - theta T) / Real.pi
        = theta T' / Real.pi - theta T / Real.pi := by
      ring
    rw [hsplit] at hdiv
    linarith
  -- from the count gap to an actual zero
  have hltN : stripZeroCountMult T < stripZeroCountMult T' := by
    exact_mod_cast hcount
  have hsub : stripZeroFinset T ⊆ stripZeroFinset T' := by
    intro ρ hρ
    rw [stripZeroFinset, Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 (le_of_lt hTT')⟩
  have hdiff_pos : (stripZeroFinset T' \ stripZeroFinset T).Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty] at hno
    have hsum := Finset.sum_sdiff (f := fun ρ => ZD.xiOrderNat ρ) hsub
    rw [hno, Finset.sum_empty, zero_add] at hsum
    rw [stripZeroCountMult, stripZeroCountMult] at hltN
    omega
  obtain ⟨ρ, hρmem⟩ := hdiff_pos
  rw [Finset.mem_sdiff] at hρmem
  obtain ⟨hρT', hρnT⟩ := hρmem
  rw [stripZeroFinset, Set.Finite.mem_toFinset] at hρT'
  have hρim : T < ρ.im := by
    by_contra hc
    push_neg at hc
    apply hρnT
    rw [stripZeroFinset, Set.Finite.mem_toFinset]
    exact ⟨hρT'.1, hρT'.2.1, hc⟩
  refine ⟨ρ, hρT'.1, hρT'.2.1, ?_⟩
  have him' : ρ.im ≤ T' := hρT'.2.2
  rw [abs_le]
  constructor <;> linarith

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.clockRate_ge_half_log
#print axioms CriticalLinePhasor.DVP.theta_increment_ge
#print axioms CriticalLinePhasor.DVP.exists_goodHeight_between
#print axioms CriticalLinePhasor.DVP.stripCount_real_eq
#print axioms CriticalLinePhasor.DVP.exists_zero_near_height
end AxiomAudit
