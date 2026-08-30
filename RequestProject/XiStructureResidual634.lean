import RequestProject.XiStructureSeatBridge
import RequestProject.DVPLadder1269o2

/-!
# Xi-structure domination through height 634

The compiled Hardy ladder `DVP.seat_channel_to_634` gives seat positivity at anchors
with `|Re w| ≤ 634`.  The chart dictionary transports this to Xi-structure domination.
Together with the existing interior rung, this isolates the remaining shallow channel.
-/

open Complex ComplexConjugate
open CriticalLinePhasor.DeBranges

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

/-- Xi-structure domination throughout the bounded Xi-chart ordinate band supplied by the
Hardy ladder.  Under `z = i(s - 1/2)`, this is `|Im s| ≤ 634`, not a strip condition on
`Re s`. -/
theorem xiStructure_dominates_of_low634 {z : ℂ} (hz : 0 < z.im)
    (hlow : |z.re| ≤ 634) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  refine dominates_of_seat_nonneg hz (fun hw hw' him => ?_)
  refine seat_channel_to_634 hw hw' him ?_
  rwa [Complex.neg_re, abs_neg]

/-- Numerical comparison used to connect the 634 ladder to the interior rung. -/
theorem exp_four_le_55 : Real.exp 4 ≤ 55 := by
  have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    linarith [Real.exp_one_lt_d9]
  nlinarith [h1, h2]

/-- Half-plane domination is equivalent to domination on the shallow channel above
height 634; the bounded ordinate band and the deep channel are discharged by compiled
theorems. -/
theorem xiStructure_dominates_residual_iff_634 : ∃ c : ℝ, 0 < c ∧
    ((∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)
      ↔ (∀ z : ℂ, 0 < z.im → 634 < |z.re| →
            z.im < 1 / 2 - c / Real.log (|z.re| + 1 / 2) →
            ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)) := by
  obtain ⟨c, hc, hrung⟩ := xiStructure_dominates_interior_rung
  refine ⟨c, hc, ?_, ?_⟩
  · intro h z hz _ _
    exact h z hz
  · intro h z hz
    by_cases hlow : |z.re| ≤ 634
    · exact xiStructure_dominates_of_low634 hz hlow
    · push Not at hlow
      have hge : Real.exp 4 + 2 ≤ |z.re| := by
        have := exp_four_le_55
        linarith
      by_cases hdeep : 1 / 2 - c / Real.log (|z.re| + 1 / 2) ≤ z.im
      · exact hrung z hz hge hdeep
      · push Not at hdeep
        exact h z hz hlow hdeep

/-- The zero-location target is equivalent to domination on the shallow channel above
height 634. -/
theorem rh_iff_shallow_channel_dominates_634 : ∃ c : ℝ, 0 < c ∧
    ((∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ (∀ z : ℂ, 0 < z.im → 634 < |z.re| →
            z.im < 1 / 2 - c / Real.log (|z.re| + 1 / 2) →
            ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)) := by
  obtain ⟨c, hc, hiff⟩ := xiStructure_dominates_residual_iff_634
  exact ⟨c, hc, rh_iff_xiStructure_dominates.trans hiff⟩

end CriticalLinePhasor.XiStructure

section AxiomAudit
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_of_low634
#print axioms CriticalLinePhasor.XiStructure.exp_four_le_55
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_residual_iff_634
#print axioms CriticalLinePhasor.XiStructure.rh_iff_shallow_channel_dominates_634
end AxiomAudit
