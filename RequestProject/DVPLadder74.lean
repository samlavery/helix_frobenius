import RequestProject.DVPLadder63
import RequestProject.DVPExhaustion74
import RequestProject.DVPStation66
import RequestProject.DVPStation68
import RequestProject.DVPStation71
import RequestProject.DVPStation74

/-!
# Rung-74: on-line to 74, channel to 73.5
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The nineteen station heights. -/
def ladder74T (i : Fin 19) : ℝ :=
  if i.val = 0 then 11 else if i.val = 1 then 18 else if i.val = 2 then 23
  else if i.val = 3 then 28 else if i.val = 4 then 32
  else if i.val = 5 then 35 else if i.val = 6 then 39
  else if i.val = 7 then 42 else if i.val = 8 then 46
  else if i.val = 9 then 49 else if i.val = 10 then 52
  else if i.val = 11 then 55 else if i.val = 12 then 58
  else if i.val = 13 then 60 else if i.val = 14 then 62
  else if i.val = 15 then 66 else if i.val = 16 then 68
  else if i.val = 17 then 71 else 74

set_option maxHeartbeats 3200000 in
/-- **The 19-station ladder is inhabited.** -/
theorem ladder74Data_holds : LadderData74 := by
  refine ⟨ladder74T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder74T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder74T]
  · intro i
    fin_cases i
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder74T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 74` is on the line.** -/
theorem online_below_74 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 74 → ρ.re = 1/2 :=
  online_below_74_of_ladder ladder74Data_holds

/-- **The channel to height 73.5, unconditional.** -/
theorem seat_channel_to_73_5 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 147/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 74) online_below_74 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder74Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_74
#print axioms CriticalLinePhasor.DVP.seat_channel_to_73_5
end AxiomAudit
