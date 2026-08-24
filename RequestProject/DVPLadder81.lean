import RequestProject.DVPLadder74
import RequestProject.DVPExhaustion81
import RequestProject.DVPStation76
import RequestProject.DVPStation78
import RequestProject.DVPStation80

/-!
# Rung-81: on-line to 81, channel to 80.5
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The twenty-two station heights. -/
def ladder81T (i : Fin 22) : ℝ :=
  if i.val = 0 then 11
  else if i.val = 1 then 18
  else if i.val = 2 then 23
  else if i.val = 3 then 28
  else if i.val = 4 then 32
  else if i.val = 5 then 35
  else if i.val = 6 then 39
  else if i.val = 7 then 42
  else if i.val = 8 then 46
  else if i.val = 9 then 49
  else if i.val = 10 then 52
  else if i.val = 11 then 55
  else if i.val = 12 then 58
  else if i.val = 13 then 60
  else if i.val = 14 then 62
  else if i.val = 15 then 66
  else if i.val = 16 then 68
  else if i.val = 17 then 71
  else if i.val = 18 then 74
  else if i.val = 19 then 76
  else if i.val = 20 then 78
  else 80

set_option maxHeartbeats 3200000 in
/-- **The 22-station ladder is inhabited.** -/
theorem ladder81Data_holds : LadderData81 := by
  refine ⟨ladder81T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder81T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder81T]
  · intro i
    fin_cases i
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_74_sign station_76_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_pos_of_neg station_76_sign station_78_sign
    · norm_num [ladder81T]
      exact_mod_cast mul_neg_of_neg_of_pos station_78_sign station_80_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 81` is on the line.** -/
theorem online_below_81 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 81 → ρ.re = 1/2 :=
  online_below_81_of_ladder ladder81Data_holds

/-- **The channel to height 80.5, unconditional.** -/
theorem seat_channel_to_80_5 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 161/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 81) online_below_81 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder81Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_81
#print axioms CriticalLinePhasor.DVP.seat_channel_to_80_5
end AxiomAudit
