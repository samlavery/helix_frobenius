import RequestProject.MaassGBoundary

/-!
# The averaged tail's global bound

`maassG_norm_le` bounds the average past height one; `maassG_eq_zero_of_le_one` says it vanishes
below.  The two combine into a single bound valid on the **whole** positive ray, with no case
split left for consumers:

  **`‖G(t)‖ ≤ C₇·e^{-π√(3t/2)}`  for every `t > 0`.**

Below the cut the left side is zero, so the inequality is free there; above it, it is the saddle
bound.  The truncation is what makes the two regimes join without a constant adjustment — the same
observation as `maassG_isBigO_boundary`, in quantitative form.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.

**Not proved here.**  Measurability of `t ↦ maassG M t`.  That needs *joint* measurability of
`(z,t) ↦ ‖u(z)‖²·truncTheta(z,t)`, and the corpus has only per-`z` continuity in `t`
(`continuousOn_latticeTheta`).  It is the one remaining obstacle to feeding
`mellinConvergent_of_isBigO_rpow`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.ThreeDConverse

/-- **The saddle bound holds on the whole positive ray.** -/
theorem maassG_norm_le_global (M : GenuineMaassCuspForm3D) :
    ∃ C₇ : ℝ, 0 ≤ C₇ ∧ ∀ t : ℝ, 0 < t →
      ‖maassG M t‖ ≤ C₇ * Real.exp (-(Real.pi * Real.sqrt (3 * t / 2))) := by
  obtain ⟨C₇, hC₇, hbd⟩ := maassG_norm_le M
  refine ⟨C₇, hC₇, fun t ht => ?_⟩
  rcases le_or_gt 1 t with h | h
  · exact hbd t h
  · rw [maassG_eq_zero_of_le_one M h.le, norm_zero]
    positivity

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassG_norm_le_global
