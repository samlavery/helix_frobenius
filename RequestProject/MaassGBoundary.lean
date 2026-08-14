import RequestProject.MaassGDecayRate

/-!
# The averaged tail vanishes below height one

The boundary end of Route B's Mellin transform, and it is not an estimate at all.

`truncTheta` is the indicator of `(1,∞)`, so for `t ≤ 1` the integrand of `maassG` is identically
zero and the average vanishes outright.  Consequently `maassG` is `O(t^{-b})` at the boundary for
*every* `b` — vacuously, because the function is zero there.

Together with `maassG_isBigO_rpow` (faster than every power at the cusp) this is two-sided
faster-than-power control with no half-plane restriction on either side: the truncation supplies
the boundary end by construction, and the saddle supplies the cusp end.  That is the shape that
makes a Mellin transform entire rather than merely convergent on a strip.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Asymptotics
open scoped Real MatrixGroups Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.ThreeDConverse

/-- **The truncated bank vanishes at or below height one.** -/
lemma truncTheta_eq_zero_of_le_one (z : ℍ) {t : ℝ} (ht : t ≤ 1) : truncTheta z t = 0 := by
  rw [truncTheta, Set.indicator_of_notMem]
  simp only [Set.mem_Ioi, not_lt]
  exact ht

/-- **The average vanishes at or below height one** — by construction, not by estimate. -/
theorem maassG_eq_zero_of_le_one (M : GenuineMaassCuspForm3D) {t : ℝ} (ht : t ≤ 1) :
    maassG M t = 0 := by
  rw [maassG]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z _ => ?_
  rw [truncTheta_eq_zero_of_le_one z ht, mul_zero]

/-- **The boundary end is vacuous**: the average is `O(t^{-b})` near zero for every `b`, because it
is identically zero there. -/
theorem maassG_isBigO_boundary (M : GenuineMaassCuspForm3D) (b : ℝ) :
    (fun t : ℝ => maassG M t) =O[𝓝[>] (0:ℝ)] (· ^ (-b)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  rw [maassG_eq_zero_of_le_one M ht.2.le, norm_zero]
  positivity

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.truncTheta_eq_zero_of_le_one
#print axioms CriticalLinePhasor.Unfolding.maassG_eq_zero_of_le_one
#print axioms CriticalLinePhasor.Unfolding.maassG_isBigO_boundary
