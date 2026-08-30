import RequestProject.XiStructureSeatBridge
import RequestProject.DVPLadder1269o2

/-!
# C3 batch 3, attack A3 — the residual seat, sharpened from `e⁴+2 ≈ 56.6` to `634`

`DVP.seat_channel_to_634` (Hardy ladder to `|γ| ≤ 1269/2`) is an unconditional seat
positivity at every anchor of height `|Re w| ≤ 634`.  Transporting it through the
`w = −z` chart dictionary of `XiStructureSeatBridge` replaces A1's low strip
(`|Re z| < e⁴ + 2`) by an eleven-fold wider one, and shrinks the residual channel
accordingly.

Nothing here is new analysis: it is the *same* transport as A1 fed by the longer
compiled ladder.  What it buys is that the residual region is now
`|Re z| > 634`, `0 < Im z < ½ − c/log(|Re z| + ½)`.
-/

open Complex ComplexConjugate
open CriticalLinePhasor.DeBranges

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

/-- **UNCONDITIONAL DOMINATION UP TO HEIGHT 634.** -/
theorem xiStructure_dominates_of_low634 {z : ℂ} (hz : 0 < z.im)
    (hlow : |z.re| ≤ 634) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  refine dominates_of_seat_nonneg hz (fun hw hw' him => ?_)
  refine seat_channel_to_634 hw hw' him ?_
  rwa [Complex.neg_re, abs_neg]

/-- `e⁴ ≤ 55`, as in `DVPExhaustion58`. -/
theorem exp_four_le_55 : Real.exp 4 ≤ 55 := by
  have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    linarith [Real.exp_one_lt_d9]
  nlinarith [h1, h2]

/-- **THE SHARPENED EXACT RESIDUAL.**  Half-plane domination is equivalent to
domination on the shallow channel ABOVE HEIGHT 634. -/
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

/-- **RH ⟺ the shallow channel above height 634.** -/
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
