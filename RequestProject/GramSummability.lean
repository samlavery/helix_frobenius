import RequestProject.LatticeThetaTermMellin

/-!
# Summability of the Gram form's negative powers

The arithmetic hypothesis of the lattice-theta interchange.  The `p`-th integrated norm in
`mellin_latticeTheta_term` is `Γ(σ)·(π·gram z p)^{-σ}`, so the interchange needs

  `∑_{p ≠ 0} (gram z p)^{-σ} < ∞`   for `σ > 1`.

That is not a new estimate: `gram z p = ‖cz+d‖²/y` (`gram_eq_norm_sq_div`), so the sum is
`y^σ·∑‖cz+d‖^{-2σ}` — precisely the Eisenstein convergence already imported from Mathlib's lattice
bounds.  The threshold is again `σ > 1`, for the third time in this chain and for the same reason:
`2σ > 2` is the two-dimensional lattice's own convergence condition.
-/

open Complex MeasureTheory UpperHalfPlane
open scoped Real

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- **Negative powers of the Gram form are summable over nonzero lattice points** for `σ > 1`. -/
theorem summable_gram_rpow_nz (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : {p : ℤ × ℤ // ¬(p.1 = 0 ∧ p.2 = 0)} => (gram z p.1) ^ (-σ) := by
  have hy : (0:ℝ) < z.im := z.im_pos
  -- the Eisenstein majorant, transported to `ℤ × ℤ`
  have hbase : Summable fun p : ℤ × ℤ =>
      z.im ^ σ * ‖(p.1 : ℂ) * (z : ℂ) + (p.2 : ℂ)‖ ^ (-(2 * σ)) := by
    rw [← (finTwoArrowEquiv ℤ).summable_iff]
    exact summable_eisenstein_real z hσ
  refine (hbase.subtype _).congr fun p => ?_
  simp only [Function.comp_apply]
  have hu : (0:ℝ) < ‖(p.1.1 : ℂ) * (z : ℂ) + (p.1.2 : ℂ)‖ := norm_pos_of_ne_zero z p.2
  rw [gram_eq_norm_sq_div, Real.div_rpow (by positivity) hy.le,
    show ((‖(p.1.1 : ℂ) * (z : ℂ) + (p.1.2 : ℂ)‖ ^ 2 : ℝ)) =
      ‖(p.1.1 : ℂ) * (z : ℂ) + (p.1.2 : ℂ)‖ ^ (2 : ℝ) by
        rw [← Real.rpow_natCast _ 2]; norm_num,
    ← Real.rpow_mul hu.le, Real.rpow_neg hy.le, div_eq_mul_inv, inv_inv,
    show (2 : ℝ) * -σ = -(2 * σ) by ring]
  ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.summable_gram_rpow_nz
