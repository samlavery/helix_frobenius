import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import RequestProject.CarrierScaleCompensation

/-!
# The Borel–Carathéodory derivative estimate and the clock-rate reduction

The Tier-2 clock brick (`hclock`: the Γ-clock rate is bounded by the chart logarithm) glues from
the compiled Γ-modulus ladder through a Borel–Carathéodory derivative estimate.  This file
supplies the estimate and the reduction:

* `bc_deriv_bound` (proven): if `g` is differentiable on `ball z₀ R` and
  `Re (g z − g z₀) ≤ M` there, then `‖deriv g z₀‖ ≤ 4M/R` — Mathlib's
  `Complex.borelCaratheodory_zero` composed with Cauchy's derivative estimate
  (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) on the half-radius circle.
* `deriv_branchLog_eq_logDeriv` (proven): on a ball where `exp ∘ g = Γℝ`, the branch derivative
  is the logarithmic derivative of `Γℝ`.
* `clockRate_le_of_stripLog` (proven): given a holomorphic branch logarithm of `Γℝ` on the
  quarter-ball at `line t` whose real oscillation is at most `M`, the clock rate is at most
  `16·M`.

The two remaining inputs are named with compiled anchors: the branch-log existence on the ball
(`Mathlib.Analysis.Complex.BranchLogRoot`, the ball being simply connected and `Γℝ` nonvanishing
on `0 < Re`), and the strip modulus bound `M = O(log t)` from the Stirling ladder
(`StirlingBound.lean`: `stirling_at_half`, `norm_Gamma_step`).  Discharging them yields `hclock`
and, with `carrierJensenBound_of_clockBound`, the chart form of the clock target.  Nothing here
assumes or proves RH/GRH.
-/

open Metric Complex

namespace CriticalLinePhasor.CarrierScale

/-- **The Borel–Carathéodory derivative estimate.**  A holomorphic function whose real part
oscillates by at most `M` on a ball has derivative at most `4M/R` at the center. -/
theorem bc_deriv_bound {g : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hre : ∀ z ∈ ball z₀ R, (g z - g z₀).re ≤ M) :
    ‖deriv g z₀‖ ≤ 4 * M / R := by
  set f : ℂ → ℂ := fun w => g (z₀ + w) - g z₀ with hf_def
  have hmaps : ∀ w ∈ ball (0 : ℂ) R, z₀ + w ∈ ball z₀ R := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.mp hw
  have hfd : DifferentiableOn ℂ f (ball (0 : ℂ) R) := by
    apply DifferentiableOn.sub_const
    exact hg.comp ((differentiable_id.const_add z₀).differentiableOn) hmaps
  have hfre : Set.MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ M} := by
    intro w hw
    exact hre (z₀ + w) (hmaps w hw)
  have hf0 : f 0 = 0 := by simp [hf_def]
  -- Borel–Carathéodory on the half-radius sphere
  have hsphere : ∀ w ∈ sphere (0 : ℂ) (R / 2), ‖f w‖ ≤ 2 * M := by
    intro w hw
    have hwn : ‖w‖ = R / 2 := mem_sphere_zero_iff_norm.mp hw
    have hwball : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, hwn]
      linarith
    have hbc := Complex.borelCaratheodory_zero hM hfd hfre hR hwball hf0
    rw [hwn] at hbc
    calc ‖f w‖ ≤ 2 * M * (R / 2) / (R - R / 2) := hbc
      _ = 2 * M := by field_simp; ring
  -- Cauchy derivative estimate on the half-radius ball
  have hhalf : (0 : ℝ) < R / 2 := by linarith
  have hcl : DiffContOnCl ℂ f (ball (0 : ℂ) (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) (ne_of_gt hhalf)]
    exact hfd.mono (closedBall_subset_ball (by linarith))
  have hcauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hcl hsphere
  -- transport the derivative back to `g` at `z₀`
  have hderiv : deriv f 0 = deriv g z₀ := by
    rw [hf_def]
    have h1 : deriv (fun w => g (z₀ + w) - g z₀) 0 = deriv (fun w => g (z₀ + w)) 0 :=
      deriv_sub_const _
    rw [h1, deriv_comp_const_add, add_zero]
  rw [hderiv] at hcauchy
  calc ‖deriv g z₀‖ ≤ 2 * M / (R / 2) := hcauchy
    _ = 4 * M / R := by field_simp; ring

/-- On a ball where `exp ∘ g = Γℝ`, the branch derivative equals the logarithmic derivative. -/
theorem deriv_branchLog_eq_logDeriv {g : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hΓ : Gammaℝ z₀ ≠ 0)
    (hg : DifferentiableOn ℂ g (ball z₀ R))
    (hexp : ∀ z ∈ ball z₀ R, Complex.exp (g z) = Gammaℝ z)
    (hΓd : DifferentiableAt ℂ Gammaℝ z₀) :
    deriv g z₀ = logDeriv Gammaℝ z₀ := by
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hgd : DifferentiableAt ℂ g z₀ :=
    hg.differentiableAt (isOpen_ball.mem_nhds hz₀)
  have heq : (fun z => Complex.exp (g z)) =ᶠ[nhds z₀] Gammaℝ :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀) hexp
  have hd1 : HasDerivAt (fun z => Complex.exp (g z))
      (Complex.exp (g z₀) * deriv g z₀) z₀ :=
    (Complex.hasDerivAt_exp (g z₀)).comp z₀ hgd.hasDerivAt
  have hd2 : HasDerivAt Gammaℝ (Complex.exp (g z₀) * deriv g z₀) z₀ :=
    hd1.congr_of_eventuallyEq heq.symm
  have hΓval : Complex.exp (g z₀) = Gammaℝ z₀ := hexp z₀ hz₀
  rw [logDeriv, Pi.div_apply, hd2.deriv, hΓval]
  field_simp

/-- **The clock-rate reduction.**  A holomorphic branch logarithm of `Γℝ` on the quarter-ball at
`line t` with real oscillation at most `M` bounds the clock rate by `16·M`.  The remaining
inputs — branch existence and the strip Stirling bound `M = O(log t)` — are anchored in
`Mathlib.Analysis.Complex.BranchLogRoot` and `StirlingBound.lean`. -/
theorem clockRate_le_of_stripLog (t : ℝ) {M : ℝ} (hM : 0 < M)
    (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (ball (line t) (1 / 4)))
    (hexp : ∀ z ∈ ball (line t) (1 / 4), Complex.exp (g z) = Gammaℝ z)
    (hΓd : DifferentiableAt ℂ Gammaℝ (line t))
    (hstrip : ∀ z ∈ ball (line t) (1 / 4), (g z - g (line t)).re ≤ M) :
    clockRate t ≤ 16 * M := by
  have hbc := bc_deriv_bound (z₀ := line t) (R := 1 / 4) (by norm_num) hM hg hstrip
  have hid := deriv_branchLog_eq_logDeriv (z₀ := line t) (R := 1 / 4) (by norm_num)
    (gauge_ne_zero t) hg hexp hΓd
  have hnorm : ‖logDeriv Gammaℝ (line t)‖ ≤ 16 * M := by
    rw [← hid]
    calc ‖deriv g (line t)‖ ≤ 4 * M / (1 / 4) := hbc
      _ = 16 * M := by ring
  calc clockRate t = (logDeriv Gammaℝ (line t)).re := rfl
    _ ≤ ‖logDeriv Gammaℝ (line t)‖ := Complex.re_le_norm _
    _ ≤ 16 * M := hnorm

end CriticalLinePhasor.CarrierScale

#print axioms CriticalLinePhasor.CarrierScale.bc_deriv_bound
#print axioms CriticalLinePhasor.CarrierScale.deriv_branchLog_eq_logDeriv
#print axioms CriticalLinePhasor.CarrierScale.clockRate_le_of_stripLog
