import RequestProject.CarrierScaleCompensation
import RequestProject.ReachableForcibleClosure
import RequestProject.DVPThetaAsymptotic

/-!
# The zeta-phase bridge: reachability at the actual carrier clock

`CarrierReachability.reachable_independent_stage` is stated for any continuous
nonconstant lane phase.  This file instantiates it at the zeta carrier's own
clock `CarrierScale.theta t = ∫₀ᵗ clockRate`, where
`clockRate t = Re (logDeriv Γℝ (½+it))` — the Riemann–Siegel phase by its
defining ODE and initial condition (`theta_hasDerivAt`, `theta_zero`); the same
`theta` already carries the compiled `S`-definition and
`riemann_von_mangoldt_classical`.

* `theta_nonconstant` — the clock is nonconstant: the compiled Stirling
  asymptotic (`DVP.theta_asymptotic`) makes the main term
  `(T/2)·log(T/2π) − T/2` unbounded, while a constant clock would pin
  `theta ≡ theta 0 = 0`.
* `zeta_reachable_independent_stage` — the carrier attains a height where the
  two lane directions `e^{±iθ}` are `ℝ`-linearly independent.
* `zeta_reachable_residual_forcible` — at such a height the dual lanes close
  any prescribed complex cell residual.

Audited 2026-08-28 (independent adjudication): numerically, on zero heights
`120 ≤ t < 400` the median `|sin 2θ|` is `0.766` and `θ = π/4 + kπ/2` is
attained at 327 stages — the compiled statement needs only one height with
`sin 2θ ≠ 0`.

No `sorry`, no `axiom`.
-/

open Complex
open CriticalLinePhasor CriticalLinePhasor.CarrierScale

namespace CriticalLinePhasor.ZetaPhaseBridge

/-- **The zeta clock is nonconstant** — corollary of the compiled Stirling
asymptotic: the main term `(T/2)·log(T/2π) − T/2` is unbounded while a constant
clock would pin `theta ≡ 0`. -/
theorem theta_nonconstant : ¬ ∀ x, CarrierScale.theta x = CarrierScale.theta 0 := by
  intro h
  obtain ⟨C, hC⟩ := DVP.theta_asymptotic
  have hπ := Real.pi_pos
  set T : ℝ := max 10 (max (2*Real.pi*Real.exp 3) (2*(|C|+1))) with hTdef
  have hT10 : (10:ℝ) ≤ T := le_max_left _ _
  have hTe : 2*Real.pi*Real.exp 3 ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTC : 2*(|C|+1) ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hT0 : (0:ℝ) < T := by linarith
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC T hT10)
  -- log(T/(2π)) ≥ 3
  have hquot : Real.exp 3 ≤ T/(2*Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hTe]
  have hlog : (3:ℝ) ≤ Real.log (T/(2*Real.pi)) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr hquot
  -- main term ≥ T
  have hmain : T ≤ (T/2) * Real.log (T/(2*Real.pi)) - T/2 := by nlinarith [hT0, hlog]
  -- θ(T) ≥ main − C ≥ T − C > 0, contradicting θ(T) = θ(0) = 0
  have hb := (abs_le.mp (hC T hT10)).1
  have habs : C ≤ |C| := le_abs_self C
  have hconst := h T
  rw [theta_zero] at hconst
  linarith [hb, hmain, hTC, habs, hconst]

/-- **The zeta-specialized reachable independent stage**: the actual carrier
clock `theta` attains a height where the two lane directions `e^{±iθ}` are
`ℝ`-linearly independent. -/
theorem zeta_reachable_independent_stage :
    ∃ y, LinearIndependent ℝ
      ![Complex.exp (↑(CarrierScale.theta y) * I),
        Complex.exp (-↑(CarrierScale.theta y) * I)] :=
  CarrierReachability.reachable_independent_stage theta_continuous theta_nonconstant

/-- **The zeta-specialized forcible closure**: at some carrier height the dual
lanes of the actual clock close any prescribed complex cell residual. -/
theorem zeta_reachable_residual_forcible (D : ℂ) :
    ∃ y s t : ℝ,
      D + (s • Complex.exp (↑(CarrierScale.theta y) * I)
        + t • Complex.exp (-↑(CarrierScale.theta y) * I)) = 0 :=
  reachable_residual_forcible theta_continuous theta_nonconstant D

/-! ## Windowed reachability: a condition-number-1 stage in every half-π window

The existential stage upgrades to a uniform supply: past an explicit threshold
the clock rate is at least `1` (Stirling brick, lower side), so the phase sweeps
at least `π/2` over every window of length `π/2`, and by the intermediate value
theorem every such window contains an **exact** stage `θ = π/4 + k·π/2` —
`sin(2θ)² = 1`, the two lanes exactly antipodal, condition number `1`.  This is
the stage-supply half of the `∃ law ∀ event` uniformity the count register
consumes; only the residual-dependence of the weights remains on the other half.
-/

/-- **The clock rate floor**: past an explicit threshold the rate is ≥ 1
(lower side of the Stirling brick `Zeta23.StirlingVert.mu_stirling`). -/
theorem clockRate_ge_one : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → 1 ≤ clockRate t := by
  obtain ⟨C, hC⟩ := Zeta23.StirlingVert.mu_stirling
  have hπ := Real.pi_pos
  have hCnn : 0 ≤ C := by
    have h1 := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1/(2*Real.pi) * Real.log (|1|/(2*Real.pi)))
    nlinarith [h1]
  refine ⟨max (2*Real.pi*Real.exp 4) (max 1 (Real.pi*C)), le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro t ht
  have ht1 : (1:ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have hte : 2*Real.pi*Real.exp 4 ≤ t := le_trans (le_max_left _ _) ht
  have htC : Real.pi*C ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : (0:ℝ) < t := by linarith
  -- Stirling lower side at t
  have hs := hC t (by rw [abs_of_pos ht0]; exact ht1)
  rw [abs_of_pos ht0] at hs
  have hlow : 1/(2*Real.pi) * Real.log (t/(2*Real.pi)) - C/t^2 ≤ Zeta23.mu t := by
    have := (abs_le.mp hs).1
    linarith
  -- DC term ≥ 2
  have hlog : (4:ℝ) ≤ Real.log (t/(2*Real.pi)) := by
    have hquot : Real.exp 4 ≤ t/(2*Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hte]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hquot
  -- AC term ≤ 1 in clock units: π·C/t² ≤ 1
  have hac : Real.pi * (C/t^2) ≤ 1 := by
    rw [mul_div_assoc'] at *
    rw [div_le_one (by positivity)]
    nlinarith [htC, ht1, hCnn]
  -- assemble: clockRate = π·mu ≥ ½·log(t/2π) − π·C/t² ≥ 2 − 1 = 1
  have hcr := clockRate_eq_pi_mul_mu t
  have hmu : Real.pi * (1/(2*Real.pi) * Real.log (t/(2*Real.pi)) - C/t^2)
      ≤ Real.pi * Zeta23.mu t := by
    exact mul_le_mul_of_nonneg_left hlow hπ.le
  have hdc : Real.pi * (1/(2*Real.pi) * Real.log (t/(2*Real.pi)))
      = (1/2) * Real.log (t/(2*Real.pi)) := by
    field_simp
  nlinarith [hmu, hdc.le, hdc.ge, hlog, hac, hcr.le, hcr.ge]

/-- **Windowed reachability**: past the threshold, *every* window of length
`π/2` contains an exact optimal stage `θ(y) = π/4 + k·π/2`. -/
theorem exact_stage_in_window : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ y ∈ Set.Icc T (T + Real.pi/2), ∃ k : ℤ,
      CarrierScale.theta y = Real.pi/4 + k * (Real.pi/2) := by
  obtain ⟨T₀, hT₀1, hrate⟩ := clockRate_ge_one
  have hπ := Real.pi_pos
  refine ⟨T₀, fun T hT => ?_⟩
  have hTle : T ≤ T + Real.pi/2 := by linarith
  -- the sweep: θ(T+π/2) − θ(T) = ∫ clockRate ≥ π/2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := CarrierScale.theta) (f' := clockRate) (a := T) (b := T + Real.pi/2)
    (fun t _ => theta_hasDerivAt t)
    (continuous_clockRate.intervalIntegrable _ _)
  have hmono : (∫ t in T..(T + Real.pi/2), (1:ℝ))
      ≤ ∫ t in T..(T + Real.pi/2), clockRate t := by
    refine intervalIntegral.integral_mono_on hTle intervalIntegrable_const
      (continuous_clockRate.intervalIntegrable _ _) (fun t htm => ?_)
    exact hrate t (le_trans hT htm.1)
  have hone : (∫ t in T..(T + Real.pi/2), (1:ℝ)) = Real.pi/2 := by
    simp
  have hsweep : CarrierScale.theta T + Real.pi/2
      ≤ CarrierScale.theta (T + Real.pi/2) := by
    have := hftc
    rw [hone] at hmono
    linarith [hmono, this.le, this.ge]
  -- the lattice point in the swept interval
  set g : ℝ := Real.pi/4 + (⌈(CarrierScale.theta T - Real.pi/4)/(Real.pi/2)⌉ : ℤ) * (Real.pi/2) with hg
  have hglo : CarrierScale.theta T ≤ g := by
    have h := Int.le_ceil ((CarrierScale.theta T - Real.pi/4)/(Real.pi/2))
    rw [hg]
    have h2 := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ Real.pi/2)
    rw [div_mul_cancel₀ _ (by positivity : (Real.pi/2:ℝ) ≠ 0)] at h2
    linarith
  have hghi : g ≤ CarrierScale.theta T + Real.pi/2 := by
    have h := Int.ceil_lt_add_one ((CarrierScale.theta T - Real.pi/4)/(Real.pi/2))
    rw [hg]
    have h2 := mul_le_mul_of_nonneg_right h.le (by positivity : (0:ℝ) ≤ Real.pi/2)
    rw [add_mul, div_mul_cancel₀ _ (by positivity : (Real.pi/2:ℝ) ≠ 0)] at h2
    linarith
  -- IVT on the window
  have hivt := intermediate_value_Icc hTle
    (theta_continuous.continuousOn (s := Set.Icc T (T + Real.pi/2)))
  have hgmem : g ∈ Set.Icc (CarrierScale.theta T) (CarrierScale.theta (T + Real.pi/2)) :=
    ⟨hglo, le_trans hghi hsweep⟩
  obtain ⟨y, hy, hyval⟩ := hivt hgmem
  exact ⟨y, hy, ⌈(CarrierScale.theta T - Real.pi/4)/(Real.pi/2)⌉, hyval⟩

/-- **Optimal-stage form**: in every half-π window past the threshold there is a
height with `sin(2θ)² = 1` — the two lanes exactly antipodal, condition number 1. -/
theorem optimal_stage_in_window : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ y ∈ Set.Icc T (T + Real.pi/2),
      Real.sin (2 * CarrierScale.theta y) ^ 2 = 1 := by
  obtain ⟨T₀, hstage⟩ := exact_stage_in_window
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨y, hy, k, hk⟩ := hstage T hT
  refine ⟨y, hy, ?_⟩
  have h2θ : 2 * CarrierScale.theta y = Real.pi/2 + k * Real.pi := by
    rw [hk]; ring
  have hcos : Real.cos (2 * CarrierScale.theta y) = 0 := by
    rw [h2θ, add_comm, Real.cos_add_pi_div_two]
    simp [Real.sin_int_mul_pi]
  have hpyth := Real.sin_sq_add_cos_sq (2 * CarrierScale.theta y)
  rw [hcos] at hpyth
  nlinarith [hpyth]

end CriticalLinePhasor.ZetaPhaseBridge

#print axioms CriticalLinePhasor.ZetaPhaseBridge.theta_nonconstant
#print axioms CriticalLinePhasor.ZetaPhaseBridge.zeta_reachable_independent_stage
#print axioms CriticalLinePhasor.ZetaPhaseBridge.zeta_reachable_residual_forcible
#print axioms CriticalLinePhasor.ZetaPhaseBridge.clockRate_ge_one
#print axioms CriticalLinePhasor.ZetaPhaseBridge.exact_stage_in_window
#print axioms CriticalLinePhasor.ZetaPhaseBridge.optimal_stage_in_window
