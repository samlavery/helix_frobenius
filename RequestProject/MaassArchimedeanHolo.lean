import RequestProject.MaassResidueIdentity

/-!
# Holomorphy of the archimedean factor

Named as a gap last stretch, and closed here: `archimedeanFactor M` is not merely convergent on
`Re s > 1`, it is **holomorphic** there.

Mathlib's `mellin_differentiableAt_of_isBigO_rpow` has *exactly* the hypotheses of
`mellinConvergent_of_isBigO_rpow` — locally integrable on the ray, `O(t^{-a})` at the cusp with
`Re s < a`, `O(t^{-b})` at the boundary with `b < Re s`.  So the proof of
`archimedeanFactor_mellinConvergent` transfers unchanged with the conclusion swapped: the same two
bounds that make the integral converge make it depend holomorphically on the exponent.

That is not an accident of the API.  Both facts come from the same dominating estimate, and the
boundary exponent `b = 1` is again the derived bound `‖K(t)‖² ≤ C/t` — the `n = 0` Fourier mode.

**Scope.**  `r = 2`.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane Filter Asymptotics
open scoped Real Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

theorem archimedeanFactor_differentiableAt (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) :
    DifferentiableAt ℂ (mellin fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) s := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := radialKernel_sq_le_div M
  obtain ⟨C₁, hC₁1, hC₁⟩ := radialKernel_norm_le_exp_of_pos M (a := 1) one_pos
  have hKcont : ContinuousOn M.radialKernel (Set.Ioi (0:ℝ)) := (M.radial_smooth 0).continuousOn
  have hpi : (0:ℝ) < 4 * Real.pi := by positivity
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := (1:ℝ)) ?_ ?_ (by linarith) ?_ hs
  · exact ((Complex.continuous_ofReal.comp_continuousOn
      (hKcont.norm.pow 2))).locallyIntegrableOn measurableSet_Ioi
  · -- cusp end: exponentially small
    have hOexp : (fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-(4 * Real.pi) * t)) := by
      rw [isBigO_iff]
      refine ⟨C₁ ^ 2, ?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have hb := hC₁ t ht
      have hsq : ‖M.radialKernel t‖ ^ 2 ≤ (C₁ * Real.exp (-(2 * Real.pi * t))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      refine le_trans hsq (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    exact hOexp.trans
      (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow hpi (-(s.re + 1)))
  · -- boundary end: the derived `C/t` bound
    rw [isBigO_iff]
    refine ⟨C₀, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.rpow_neg_one]
    rw [← div_eq_mul_inv]
    exact hC₀ t ht0

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactor_differentiableAt
