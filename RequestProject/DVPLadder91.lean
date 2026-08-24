import RequestProject.DVPLadder81
import RequestProject.DVPExhaustion91
import RequestProject.DVPStation84
import RequestProject.DVPStation86
import RequestProject.DVPStation88
import RequestProject.DVPStation90

/-!
# Rung-91: on-line to 91, channel to 90.5
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The twenty-six station heights. -/
def ladder91T (i : Fin 26) : ℝ :=
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
  else if i.val = 21 then 80
  else if i.val = 22 then 84
  else if i.val = 23 then 86
  else if i.val = 24 then 88
  else 90

set_option maxHeartbeats 6400000 in
/-- **The 26-station ladder is inhabited.** -/
theorem ladder91Data_holds : LadderData91 := by
  refine ⟨ladder91T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder91T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder91T]
  · intro i
    fin_cases i
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_74_sign station_76_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_76_sign station_78_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_78_sign station_80_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_80_sign station_84_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_84_sign station_86_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_pos_of_neg station_86_sign station_88_sign
    · norm_num [ladder91T]
      exact_mod_cast mul_neg_of_neg_of_pos station_88_sign station_90_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 91` is on the line.** -/
theorem online_below_91 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 91 → ρ.re = 1/2 :=
  online_below_91_of_ladder ladder91Data_holds

/-- **The channel to height 90.5, unconditional.** -/
theorem seat_channel_to_90_5 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 181/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 91) online_below_91 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder91Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_91
#print axioms CriticalLinePhasor.DVP.seat_channel_to_90_5
end AxiomAudit
