import RequestProject.MaassGAverage

/-!
# The averaged tail decays faster than every power

The last step of Route B for the Maass case.  `maassG_norm_le` bounds the average by a constant
times the saddle exponential; `exp_sqrt_isBigO` (already in `GDecay`) says that exponential is
`O(t^{-a})` for **every** `a`.  Composing gives

  **`maassG M =O[atTop] (· ^ (-a))` for every `a : ℝ`.**

Faster-than-power decay at the cusp end is exactly the hypothesis that makes a Mellin transform
entire in the corresponding direction, so this is the holomorphy input the continuation needs — and
it was obtained without any uniformity in `z`, because the averaging was done first.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Asymptotics
open scoped Real MatrixGroups Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The averaged Maass tail decays faster than every power.** -/
theorem maassG_isBigO_rpow (M : GenuineMaassCuspForm3D) (a : ℝ) :
    (fun t : ℝ => maassG M t) =O[atTop] (· ^ (-a)) := by
  obtain ⟨C₇, hC₇, hbd⟩ := maassG_norm_le M
  have hstep : (fun t : ℝ => maassG M t) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi * Real.sqrt (3 * t / 2)))) := by
    rw [isBigO_iff]
    refine ⟨C₇, ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hbd t ht
  exact hstep.trans (exp_sqrt_isBigO a)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassG_isBigO_rpow
