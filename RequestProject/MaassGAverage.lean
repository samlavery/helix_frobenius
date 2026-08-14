import RequestProject.MaassWeightIntegrable
import RequestProject.TruncatedMellin

/-!
# The `𝒟`-average of the truncated bank against the Maass density

Route B's averaging step.  `G(t) = ∫_𝒟 ‖u‖²·truncTheta(z,t) dμ` inherits the pointwise saddle bound
of `maass_ptwise_bound` uniformly, because the `y`-weight it leaves behind is integrable over `𝒟`
(`weight_integrableOn_fd`).

The point of averaging *before* transforming is that no uniformity in `z` is ever required: the
`z`-dependence is integrated away against a finite measure, and what survives is a single function
of `t` with the saddle rate `e^{-π√(3t/2)}` — faster than every power, which is exactly the
hypothesis that makes the Mellin transform entire.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- The truncated bank's norm is bounded by the untruncated tail past height one. -/
lemma norm_truncTheta_le (z : ℍ) {t : ℝ} (ht : 1 ≤ t) :
    ‖truncTheta z t‖ ≤ latticeTheta z t - 1 := by
  have hone := one_le_latticeTheta z (lt_of_lt_of_le one_pos ht)
  rcases eq_or_lt_of_le ht with h | h
  · rw [truncTheta, Set.indicator_of_notMem (by simp [← h]), norm_zero]
    linarith
  · rw [truncTheta, Set.indicator_of_mem (Set.mem_Ioi.mpr h), latticeThetaC, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]

/-- **The `𝒟`-average of the truncated bank against the Maass Petersson density.** -/
noncomputable def maassG (M : GenuineMaassCuspForm3D) (t : ℝ) : ℂ :=
  ∫ z in ModularGroup.fd, ((maassP M z : ℝ) : ℂ) * truncTheta z t ∂(volume : Measure ℍ)

/-- **The average carries the saddle rate.**  For `t ≥ 1` the average is bounded by a constant
times `e^{-π√(3t/2)}` — faster than every power. -/
theorem maassG_norm_le (M : GenuineMaassCuspForm3D) :
    ∃ C₇ : ℝ, 0 ≤ C₇ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖maassG M t‖ ≤ C₇ * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2))) := by
  obtain ⟨C₁, C₆, hC₁, hC₆, hpt⟩ := maass_ptwise_bound M
  set W : ℝ := ∫ z in ModularGroup.fd, wt C₁ z.im ∂(volume : Measure ℍ) with hW
  have hWnn : 0 ≤ W := by
    rw [hW]
    refine setIntegral_nonneg measurableSet_fd fun z _ => ?_
    exact wt_nonneg hC₁ z.im_pos.le
  refine ⟨C₆ * W, mul_nonneg hC₆ hWnn, fun t ht => ?_⟩
  have hEnn : (0:ℝ) ≤ Real.exp (-(Real.pi * Real.sqrt (3 * t / 2))) := (Real.exp_pos _).le
  -- pointwise bound on the integrand
  have hptw : ∀ z ∈ ModularGroup.fd,
      ‖((maassP M z : ℝ) : ℂ) * truncTheta z t‖ ≤
        (C₆ * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2)))) * wt C₁ z.im := by
    intro z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (maassP_nonneg M z)]
    have h1 : maassP M z * ‖truncTheta z t‖ ≤ maassP M z * (latticeTheta z t - 1) :=
      mul_le_mul_of_nonneg_left (norm_truncTheta_le z ht) (maassP_nonneg M z)
    refine le_trans h1 (le_trans (hpt z hz t ht) (le_of_eq ?_))
    ring
  -- integrate
  have hmaj : IntegrableOn
      (fun z : ℍ => (C₆ * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2)))) * wt C₁ z.im)
      ModularGroup.fd volume := (weight_integrableOn_fd hC₁).const_mul _
  calc ‖maassG M t‖ ≤ ∫ z in ModularGroup.fd,
        ‖((maassP M z : ℝ) : ℂ) * truncTheta z t‖ ∂(volume : Measure ℍ) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z in ModularGroup.fd,
        (C₆ * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2)))) * wt C₁ z.im
          ∂(volume : Measure ℍ) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj ?_
        filter_upwards [ae_restrict_mem measurableSet_fd] with z hz
        exact hptw z hz
    _ = C₆ * W * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2))) := by
        rw [MeasureTheory.integral_const_mul, ← hW]
        ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.norm_truncTheta_le
#print axioms CriticalLinePhasor.Unfolding.maassG_norm_le
