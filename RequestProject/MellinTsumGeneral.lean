import RequestProject.GramSummability

/-!
# The Mellin–series interchange at an arbitrary countable index

`MaassMellinInterchange.mellin_tsum` is stated for `ℕ`-indexed families, which is what the
Fourier–Whittaker expansion needs.  The lattice theta is indexed by nonzero pairs, so the same
statement is needed at an arbitrary countable index.

The proof is unchanged — the weight `t^{s-1}` moves inside for free (`tsum_mul_left` holds
unconditionally in a division ring), and the interchange is Mathlib's
`integral_tsum_of_summable_integral_norm`, which is already stated for a countable index.  Only the
`ℕ` in the earlier statement was special.
-/

open MeasureTheory Set

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

/-- **The Mellin transform commutes with an absolutely convergent series**, at any countable
index. -/
theorem mellin_tsum_countable {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {s : ℂ}
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

#print axioms CriticalLinePhasor.ThreeDConverse.mellin_tsum_countable
