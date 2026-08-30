import RequestProject.XiStructureSeatBridge
import RequestProject.DVPLadder

/-!
# C3 batch 3, attack A1 — the low-height strip, and the EXACT residual

Two things:

* `xiStructure_dominates_of_low` — **unconditional** Hermite–Biehler domination at
  every chart point of height `|Re z| < e⁴ + 2`.  Supplied by `DVP.conjunct_one`
  (the thirteen-station Hardy ladder) through the window law: a window zero of a
  low anchor has ordinate `< e⁴ + 5/2`, hence lies on the line, hence has depth `0`,
  hence cannot be deeper than the anchor.  The deep window is empty and the seat
  energy is a sum of nonnegative terms.

* `xiStructure_dominates_residual_iff` — the target half-plane domination is
  **equivalent** to domination on the shallow high channel alone.  Low height is
  A1's first half; high-and-deep is `xiStructure_dominates_interior_rung`.

Combined: `rh_iff_shallow_channel_dominates`.
-/

open Complex ComplexConjugate
open CriticalLinePhasor.DeBranges

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DVP CriticalLinePhasor.SeatScalar
open CriticalLinePhasor.HilbertPolya

/-- **Seat positivity at low anchors, unconditional.**  From `DVP.conjunct_one`. -/
theorem seat_energy_nonneg_of_low {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hlow : |w.re| < Real.exp 4 + 2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hwindow := seat_energy_ge_window hw hw' him
  have hempty : IsEmpty {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} := by
    constructor
    rintro ⟨⟨ρ, hρ⟩, hnear, hdeep⟩
    simp only at hnear hdeep
    have hγlow : |ρ.im| < Real.exp 4 + 5 / 2 := by
      have h1 := abs_sub_abs_le_abs_sub ρ.im w.re
      linarith [hnear, h1]
    have hre := conjunct_one ρ hρ hγlow
    rw [hre] at hdeep
    simp only [sub_self, abs_zero] at hdeep
    exact absurd hdeep (not_lt.mpr (abs_nonneg _))
  have hzero : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)) = 0 := tsum_empty
  rw [hzero] at hwindow
  simpa using hwindow

/-- **UNCONDITIONAL DOMINATION IN THE LOW STRIP.** -/
theorem xiStructure_dominates_of_low {z : ℂ} (hz : 0 < z.im)
    (hlow : |z.re| < Real.exp 4 + 2) :
    ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖ := by
  refine dominates_of_seat_nonneg hz (fun hw hw' him => ?_)
  refine seat_energy_nonneg_of_low hw hw' him ?_
  rwa [Complex.neg_re, abs_neg]

/-- **THE EXACT RESIDUAL.**  Half-plane domination ⟺ shallow-high-channel domination. -/
theorem xiStructure_dominates_residual_iff : ∃ c : ℝ, 0 < c ∧
    ((∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)
      ↔ (∀ z : ℂ, 0 < z.im → Real.exp 4 + 2 ≤ |z.re| →
            z.im < 1 / 2 - c / Real.log (|z.re| + 1 / 2) →
            ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)) := by
  obtain ⟨c, hc, hrung⟩ := xiStructure_dominates_interior_rung
  refine ⟨c, hc, ?_, ?_⟩
  · intro h z hz _ _
    exact h z hz
  · intro h z hz
    by_cases hlow : |z.re| < Real.exp 4 + 2
    · exact xiStructure_dominates_of_low hz hlow
    · push Not at hlow
      by_cases hdeep : 1 / 2 - c / Real.log (|z.re| + 1 / 2) ≤ z.im
      · exact hrung z hz hlow hdeep
      · push Not at hdeep
        exact h z hz hlow hdeep

/-- **RH ⟺ the shallow channel.**  The whole of RH now sits on the single region
`|Re z| ≥ e⁴ + 2`, `0 < Im z < ½ − c/log(|Re z| + ½)`. -/
theorem rh_iff_shallow_channel_dominates : ∃ c : ℝ, 0 < c ∧
    ((∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ (∀ z : ℂ, 0 < z.im → Real.exp 4 + 2 ≤ |z.re| →
            z.im < 1 / 2 - c / Real.log (|z.re| + 1 / 2) →
            ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖)) := by
  obtain ⟨c, hc, hiff⟩ := xiStructure_dominates_residual_iff
  exact ⟨c, hc, rh_iff_xiStructure_dominates.trans hiff⟩

end CriticalLinePhasor.XiStructure

section AxiomAudit
#print axioms CriticalLinePhasor.XiStructure.seat_energy_nonneg_of_low
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_of_low
#print axioms CriticalLinePhasor.XiStructure.xiStructure_dominates_residual_iff
#print axioms CriticalLinePhasor.XiStructure.rh_iff_shallow_channel_dominates
end AxiomAudit
