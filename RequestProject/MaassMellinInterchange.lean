import Mathlib

/-!
# Interchanging the Mellin transform with a series

The joining step of the Maass Rankin--Selberg chain.  `maass_horizontal_energy` presents the strip
integrand as a series over Fourier modes, and `mellin_maass_term` evaluates the Mellin transform of
each mode.  To conclude that the Mellin transform of the strip integrand is the Rankin--Selberg
Dirichlet series times the archimedean factor, the transform has to pass through the sum.

The scalar `t^{s-1}` moves inside the series for free — `tsum_mul_left` holds unconditionally in a
division ring — so the only real content is Mathlib's
`integral_tsum_of_summable_integral_norm`, which needs each term integrable and the integrated
norms summable.

Stated for an arbitrary countable family, so it is reusable and carries no Maass-specific content.
-/

open MeasureTheory Set

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

/-- **The Mellin transform commutes with an absolutely convergent series.**  The weight moves inside
the sum for free; the interchange itself is dominated convergence. -/
theorem mellin_tsum {F : ℕ → ℝ → ℂ} {s : ℂ}
    (hint : ∀ n, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • F n t) (Ioi (0:ℝ)))
    (hsum : Summable fun n => ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ (s - 1) • F n t‖) :
    mellin (fun t => ∑' n, F n t) s = ∑' n, mellin (F n) s := by
  have hmove : ∀ t : ℝ,
      (t : ℂ) ^ (s - 1) • (∑' n, F n t) = ∑' n, (t : ℂ) ^ (s - 1) • F n t := by
    intro t
    simp only [smul_eq_mul]
    exact (tsum_mul_left).symm
  rw [mellin]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hmove t)]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  rfl

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.mellin_tsum
