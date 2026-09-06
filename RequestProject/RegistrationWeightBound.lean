import RequestProject.RegistrationBoundary
import RequestProject.FejerMass

/-!
# On-line gap weights lie in `[0, 1]` (ledger 610)

For an on-line zero `ρ = ½ + iγ` the gap weight `w_ρ(a, b) = (1/π) ∫_a^b Re K_L(ρ − ½ − it) dt` is the
Fejér mass of the gap, `(1/π) ∫_a^b F_L(γ − t) dt` with `F_L(u) = (1 − cos Lu)/(L u²)`. It is
nonnegative (609) and, by the total mass `∫_ℝ F_L = π` (`integral_fejer`), at most one. Hence every
on-line term of the boundary sum `Σ'_ρ m_ρ (1_gap(ρ) − w_ρ)` is a number in `[−1, 1]`: a zero inside the
gap contributes `m_ρ (1 − w_ρ) ≥ 0`, a zero outside contributes `−m_ρ w_ρ ≤ 0`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Interval Real

namespace CriticalLinePhasor.ContourArgument

theorem fejer_nonneg {L : ℝ} (hL : 0 < L) (u : ℝ) : 0 ≤ fejer L u := by
  unfold fejer
  apply div_nonneg
  · linarith [Real.cos_le_one (L * u)]
  · positivity

/-- `fejer L (2πw) = (triHat L w).re / 2`, everywhere (both vanish at `w = 0`). -/
theorem fejer_scaled_eq {L : ℝ} (hL : 0 < L) (w : ℝ) :
    fejer L (2 * π * w) = (1 / 2) * (triHat L w).re := by
  unfold fejer triHat
  rw [Complex.ofReal_re]
  by_cases hw : w = 0
  · subst hw; simp
  · have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    rw [show L * (2 * π * w) = 2 * π * L * w by ring]
    field_simp

theorem fejer_integrable {L : ℝ} (hL : 0 < L) : Integrable (fejer L) := by
  have h : Integrable (fun w : ℝ => fejer L (2 * π * w)) := by
    have := ((triHat_integrable hL).re).const_mul (1 / 2)
    refine this.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [RCLike.re_to_complex]
    exact (fejer_scaled_eq hL w).symm
  exact (integrable_comp_mul_left_iff (fejer L) (by positivity : (2 * π : ℝ) ≠ 0)).1 h

/-- On the line the kernel's real part is the Fejér kernel, off the single point `u = 0`. -/
theorem rieszKernel_re_line_eq_fejer {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : u ≠ 0) :
    (rieszKernel L (u * I)).re = fejer L u := by
  rw [rieszKernel_re_line_eq hL hu]
  unfold fejer
  ring

/-- **On-line gap weights are at most one.** -/
theorem gapWeight_le_one_of_online {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) : gapWeight L a b ρ ≤ 1 := by
  unfold gapWeight
  have hπ := Real.pi_pos
  -- the integrand is `fejer L (ρ.im − t)` off the single height `t = ρ.im`
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      (rieszKernel L (ρ - (1 / 2 + (t : ℂ) * I))).re = fejer L (ρ.im - t) := by
    have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ ρ.im := by
      rw [MeasureTheory.ae_iff]
      simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [h0] with t ht _
    rw [online_shift hρ t, rieszKernel_re_line_eq_fejer hL (sub_ne_zero.2 (Ne.symm ht))]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_of_le hab]
  have hint : Integrable (fun t : ℝ => fejer L (ρ.im - t)) := (fejer_integrable hL).comp_sub_left ρ.im
  have hle : ∫ t in Ioc a b, fejer L (ρ.im - t) ≤ ∫ t, fejer L (ρ.im - t) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall (fun t => fejer_nonneg hL _))
  rw [integral_sub_left_eq_self (fejer L) volume ρ.im, integral_fejer hL] at hle
  calc (1 / π) * ∫ t in Ioc a b, fejer L (ρ.im - t) ≤ (1 / π) * π :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := by field_simp

/-- On-line gap weights lie in `[0, 1]`. -/
theorem gapWeight_mem_Icc_of_online {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) : gapWeight L a b ρ ∈ Icc (0 : ℝ) 1 :=
  ⟨gapWeight_nonneg_of_online hL hab hρ, gapWeight_le_one_of_online hL hab hρ⟩

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.fejer_integrable
#print axioms CriticalLinePhasor.ContourArgument.gapWeight_le_one_of_online
#print axioms CriticalLinePhasor.ContourArgument.gapWeight_mem_Icc_of_online
