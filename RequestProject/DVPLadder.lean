import RequestProject.DVPStation11
import RequestProject.DVPStation18
import RequestProject.DVPStation23
import RequestProject.DVPStation28
import RequestProject.DVPStation32
import RequestProject.DVPStation35
import RequestProject.DVPStation39
import RequestProject.DVPStation42
import RequestProject.DVPStation46
import RequestProject.DVPStation49
import RequestProject.DVPStation52
import RequestProject.DVPStation55
import RequestProject.DVPStation58
import RequestProject.DVPSeatRungOne

/-!
# The Hardy ladder, assembled — conjunct 1 discharged

Thirteen certified station signs alternate, so `LadderData` holds; with
the compiled census `N_all(58) = 12` the exhaustion forces **every
nontrivial zero of ordinate `|γ| ≤ 58` onto the critical line** — in
particular the finite conjunct of `seat_criterion_split_iff`
(`|γ| < e⁴ + 5/2`), UNCONDITIONALLY.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The thirteen station heights. -/
def ladderT (i : Fin 13) : ℝ :=
  if i.val = 0 then 11 else if i.val = 1 then 18 else if i.val = 2 then 23
  else if i.val = 3 then 28 else if i.val = 4 then 32
  else if i.val = 5 then 35 else if i.val = 6 then 39
  else if i.val = 7 then 42 else if i.val = 8 then 46
  else if i.val = 9 then 49 else if i.val = 10 then 52
  else if i.val = 11 then 55 else 58

/-- **The ladder is inhabited.** -/
theorem ladderData_holds : LadderData := by
  refine ⟨ladderT, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladderT]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladderT]
  · intro i
    fin_cases i <;>
      · norm_num [ladderT]
        first
        | exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
        | exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
        | exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
        | exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
        | exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
        | exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 58` is on the line.** -/
theorem online_below_58 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 58 → ρ.re = 1/2 :=
  online_below_58_of_ladder ladderData_holds

/-- **CONJUNCT 1 of the seat split, unconditional**: every zero of
ordinate `|γ| < e⁴ + 5/2` lies on the critical line. -/
theorem conjunct_one :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| < Real.exp 4 + 5/2 → ρ.re = 1/2 :=
  conjunct_one_of_ladder ladderData_holds

/-- **The seat criterion, finite conjunct absorbed**: with conjunct 1 a
theorem, the split collapses — RH is EQUIVALENT to the shallow channel
alone. -/
theorem seat_criterion_channel_iff : ∃ c : ℝ, 0 < c ∧
    ((∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ ∀ w : ℂ, ((1/2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
          ((1/2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
          (w - (starRingEnd ℂ) w ≠ 0) →
          Real.exp 4 + 2 ≤ |w.re| →
          |w.im| < 1/2 - c / Real.log (|w.re| + 1/2) →
          0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val - w)⁻¹ *
                  (CriticalLinePhasor.HilbertPolya.spectralCoord ρ.val
                    - (starRingEnd ℂ) w)⁻¹)).re) := by
  obtain ⟨c, hc, hiff⟩ := seat_criterion_split_iff
  refine ⟨c, hc, ?_⟩
  rw [hiff]
  constructor
  · rintro ⟨_, h2⟩
    exact h2
  · intro h2
    exact ⟨conjunct_one, h2⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladderData_holds
#print axioms CriticalLinePhasor.DVP.online_below_58
#print axioms CriticalLinePhasor.DVP.conjunct_one
#print axioms CriticalLinePhasor.DVP.seat_criterion_channel_iff
end AxiomAudit
