import RequestProject.DVPLittlewoodHorizontal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Littlewood box: the log-distance integrals

`∫ₐᵇ log|x−β| dx` computed EXACTLY (Mathlib's junk-value `log 0 = 0` absorbs
the singularity — `integral_log` is unconditional), and bounded below by `−2`
UNIFORMLY in the window and in `β`.  DC first: the common mode is the exact
primitive `g(c) = c·log c − c`; the estimate is only on `g`'s range
(`g ≥ −1` on `[0,∞)`, odd extension).  This is the per-zero supply for the
top-edge lower bound: each zero in the local window costs at least `−2`, and
the compiled `13L` count caps the total at `O(log T)`.
-/

open intervalIntegral

noncomputable section

namespace CriticalLinePhasor.DVP

/-- `g(c) = c·log c − c ≥ −1` on `[0,∞)` (global minimum at `c = 1`). -/
theorem mul_log_sub_self_ge {c : ℝ} (hc : 0 ≤ c) :
    -1 ≤ c * Real.log c - c := by
  rcases eq_or_lt_of_le hc with h0 | h0
  · rw [← h0]
    simp
  · have hinv : Real.log c⁻¹ ≤ c⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hinv
    have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt h0)
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h0)
    nlinarith [hmul, hcc]

/-- `g(c) = c·log c − c ≤ 0` on `[0, e]`. -/
theorem mul_log_sub_self_nonpos {c : ℝ} (hc0 : 0 ≤ c)
    (hce : c ≤ Real.exp 1) : c * Real.log c - c ≤ 0 := by
  rcases eq_or_lt_of_le hc0 with h0 | h0
  · rw [← h0]
    simp
  · have hlog : Real.log c ≤ 1 := by
      calc Real.log c ≤ Real.log (Real.exp 1) := Real.log_le_log h0 hce
        _ = 1 := Real.log_exp 1
    nlinarith [mul_le_mul_of_nonneg_left hlog (le_of_lt h0)]

/-- **The primitive-difference floor**: `g(v) − g(w) ≥ −2` for every real
`w ≤ v`, where `g(c) = c·log c − c` — no window-length restriction. -/
theorem mul_log_sub_diff_ge {w v : ℝ} (hwv : w ≤ v) :
    -2 ≤ (v * Real.log v - v) - (w * Real.log w - w) := by
  have hodd : ∀ x : ℝ, (-x) * Real.log (-x) - (-x) = -(x * Real.log x - x) := by
    intro x
    rw [Real.log_neg_eq_log]
    ring
  have hP : ∀ {w' v' : ℝ}, 0 ≤ w' → w' ≤ v' →
      -2 ≤ (v' * Real.log v' - v') - (w' * Real.log w' - w') := by
    intro w' v' hw0 hwv'
    rcases le_or_gt w' (Real.exp 1) with hwe | hwe
    · have hA := mul_log_sub_self_ge (le_trans hw0 hwv')
      have hB := mul_log_sub_self_nonpos hw0 hwe
      linarith
    · have hw0' : (0:ℝ) < w' := lt_trans (Real.exp_pos 1) hwe
      have hv0 : (0:ℝ) < v' := lt_of_lt_of_le hw0' hwv'
      have hlogw : 1 ≤ Real.log w' := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt hwe)
      have hlogvw : Real.log w' ≤ Real.log v' := Real.log_le_log hw0' hwv'
      have h1 : v' * Real.log w' ≤ v' * Real.log v' :=
        mul_le_mul_of_nonneg_left hlogvw (le_of_lt hv0)
      nlinarith [h1, mul_nonneg (sub_nonneg.2 hwv') (sub_nonneg.2 hlogw)]
  rcases le_or_gt 0 w with hw0 | hw0
  · exact hP hw0 hwv
  · rcases le_or_gt 0 v with hv0 | hv0
    · have hgw : w * Real.log w - w = -((-w) * Real.log (-w) - (-w)) := by
        have h := hodd (-w)
        simp only [neg_neg] at h
        linarith [h]
      have hA1 := mul_log_sub_self_ge (le_of_lt (neg_pos.mpr hw0))
      have hA2 := mul_log_sub_self_ge hv0
      linarith
    · have hgv : v * Real.log v - v = -((-v) * Real.log (-v) - (-v)) := by
        have h := hodd (-v)
        simp only [neg_neg] at h
        linarith [h]
      have hgw : w * Real.log w - w = -((-w) * Real.log (-w) - (-w)) := by
        have h := hodd (-w)
        simp only [neg_neg] at h
        linarith [h]
      have h := hP (le_of_lt (neg_pos.mpr hv0)) (by linarith : -v ≤ -w)
      linarith

/-- **The exact log-distance integral**, unconditional in `a`, `b`, `β`:
`∫ₐᵇ log|x−β| dx = g(b−β) − g(a−β)` with `g(c) = c·log c − c`. -/
theorem integral_log_abs_sub (a b β : ℝ) :
    ∫ x in a..b, Real.log |x - β|
      = (b - β) * Real.log (b - β) - (a - β) * Real.log (a - β) - b + a := by
  have h1 : (fun x : ℝ => Real.log |x - β|) = fun x : ℝ => Real.log (x - β) := by
    funext x
    exact Real.log_abs _
  rw [h1, intervalIntegral.integral_comp_sub_right (fun s => Real.log s) β,
    integral_log]
  ring

/-- **The universal log-distance floor**: `∫ₐᵇ log|x−β| dx ≥ −2` for every
window `a ≤ b` and every center `β` — the per-zero cost of the top edge. -/
theorem integral_log_abs_sub_lower {a b : ℝ} (hab : a ≤ b) (β : ℝ) :
    -2 ≤ ∫ x in a..b, Real.log |x - β| := by
  rw [integral_log_abs_sub]
  have h := mul_log_sub_diff_ge (w := a - β) (v := b - β) (by linarith)
  linarith

/-- The log-distance integrand is interval-integrable (shift of `log`,
composed with `|·|`). -/
theorem intervalIntegrable_log_abs_sub (a b β : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log |x - β|)
      MeasureTheory.volume a b := by
  have h1 : (fun x : ℝ => Real.log |x - β|) = fun x : ℝ => Real.log (x - β) := by
    funext x
    exact Real.log_abs _
  rw [h1]
  have h := (intervalIntegrable_log' (a := a - β) (b := b - β)).comp_sub_right β
  simpa using h

/-- **The complex log-distance floor**: `∫ₐᵇ log‖u+iT−ρ‖ du ≥ −2` for every
window `a ≤ b`, every height `T`, every center `ρ` — the horizontal distance
minorizes the complex one a.e. (the single junk point `u = Re ρ` has measure
zero), and through the center's own height the norm IS the real distance. -/
theorem integral_log_norm_dist_lower {a b : ℝ} (hab : a ≤ b) (T : ℝ) (ρ : ℂ) :
    -2 ≤ ∫ u in a..b, Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
  rcases eq_or_ne T ρ.im with hT | hT
  · have hcong : Set.EqOn
        (fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
        (fun u : ℝ => Real.log |u - ρ.re|) (Set.uIcc a b) := by
      intro u _
      have hz : (u:ℂ) + (T:ℂ) * Complex.I - ρ = ((u - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hT]
      show Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ = Real.log |u - ρ.re|
      rw [hz, Complex.norm_real, Real.norm_eq_abs]
    rw [intervalIntegral.integral_congr hcong]
    exact integral_log_abs_sub_lower hab ρ.re
  · have hne : ∀ u : ℝ, (u:ℂ) + (T:ℂ) * Complex.I - ρ ≠ 0 := by
      intro u h
      apply hT
      have him := congrArg Complex.im h
      simp at him
      linarith [him]
    have hcont : ContinuousOn
        (fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
        (Set.uIcc a b) := by
      apply ContinuousOn.log
      · exact (((Complex.continuous_ofReal.add continuous_const).sub
          continuous_const).norm).continuousOn
      · intro u _
        exact norm_ne_zero_iff.mpr (hne u)
    have hint : IntervalIntegrable
        (fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖)
        MeasureTheory.volume a b :=
      hcont.intervalIntegrable
    have hintr := intervalIntegrable_log_abs_sub a b ρ.re
    have hae : (fun u : ℝ => Real.log |u - ρ.re|)
        ≤ᵐ[MeasureTheory.volume]
        fun u : ℝ => Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
      show ∀ᵐ u ∂MeasureTheory.volume,
        Real.log |u - ρ.re| ≤ Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_
        (MeasureTheory.measure_singleton ρ.re)
      intro u hu
      simp only [Set.mem_setOf_eq, not_le] at hu
      simp only [Set.mem_singleton_iff]
      by_contra hub
      have habs : (0:ℝ) < |u - ρ.re| := by
        rw [abs_pos, sub_ne_zero]
        exact hub
      have hre : ((u:ℂ) + (T:ℂ) * Complex.I - ρ).re = u - ρ.re := by simp
      have hle : |u - ρ.re| ≤ ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := by
        calc |u - ρ.re| = |((u:ℂ) + (T:ℂ) * Complex.I - ρ).re| := by rw [hre]
          _ ≤ ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ := Complex.abs_re_le_norm _
      have hlog := Real.log_le_log habs hle
      linarith
    calc (-2 : ℝ) ≤ ∫ u in a..b, Real.log |u - ρ.re| :=
        integral_log_abs_sub_lower hab ρ.re
      _ ≤ ∫ u in a..b, Real.log ‖(u:ℂ) + (T:ℂ) * Complex.I - ρ‖ :=
        intervalIntegral.integral_mono_ae hab hintr hint hae

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.mul_log_sub_self_ge
#print axioms CriticalLinePhasor.DVP.mul_log_sub_self_nonpos
#print axioms CriticalLinePhasor.DVP.mul_log_sub_diff_ge
#print axioms CriticalLinePhasor.DVP.integral_log_abs_sub
#print axioms CriticalLinePhasor.DVP.integral_log_abs_sub_lower
#print axioms CriticalLinePhasor.DVP.intervalIntegrable_log_abs_sub
#print axioms CriticalLinePhasor.DVP.integral_log_norm_dist_lower
end AxiomAudit
