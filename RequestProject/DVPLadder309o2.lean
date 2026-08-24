import RequestProject.DVPLadder289o2
import RequestProject.DVPExhaustion309o2
import RequestProject.DVPStation147
import RequestProject.DVPStation149
import RequestProject.DVPStation301o2
import RequestProject.DVPStation152
import RequestProject.DVPStation154

/-!
# Rung-154.5: on-line to 309/2, channel to 154
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The fifty-six station heights (four half-integer). -/
def ladder309o2T (i : Fin 56) : ℝ :=
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
  else if i.val = 25 then 90
  else if i.val = 26 then 93
  else if i.val = 27 then 95
  else if i.val = 28 then 97
  else if i.val = 29 then 100
  else if i.val = 30 then 102
  else if i.val = 31 then 105
  else if i.val = 32 then 106
  else if i.val = 33 then 108
  else if i.val = 34 then 223/2
  else if i.val = 35 then 113
  else if i.val = 36 then 115
  else if i.val = 37 then 118
  else if i.val = 38 then 120
  else if i.val = 39 then 122
  else if i.val = 40 then 247/2
  else if i.val = 41 then 125
  else if i.val = 42 then 128
  else if i.val = 43 then 130
  else if i.val = 44 then 132
  else if i.val = 45 then 134
  else if i.val = 46 then 136
  else if i.val = 47 then 139
  else if i.val = 48 then 281/2
  else if i.val = 49 then 142
  else if i.val = 50 then 144
  else if i.val = 51 then 147
  else if i.val = 52 then 149
  else if i.val = 53 then 301/2
  else if i.val = 54 then 152
  else 154

set_option maxHeartbeats 25600000 in
/-- **The 56-station ladder is inhabited.** -/
theorem ladder309o2Data_holds : LadderData309o2 := by
  refine ⟨ladder309o2T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder309o2T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder309o2T]
  · intro i
    fin_cases i
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_74_sign station_76_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_76_sign station_78_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_78_sign station_80_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_80_sign station_84_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_84_sign station_86_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_86_sign station_88_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_88_sign station_90_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_90_sign station_93_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_93_sign station_95_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_95_sign station_97_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_97_sign station_100_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_100_sign station_102_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_102_sign station_105_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_105_sign station_106_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_106_sign station_108_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_108_sign station_223o2_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_223o2_sign station_113_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_113_sign station_115_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_115_sign station_118_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_118_sign station_120_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_120_sign station_122_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_122_sign station_247o2_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_247o2_sign station_125_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_125_sign station_128_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_128_sign station_130_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_130_sign station_132_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_132_sign station_134_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_134_sign station_136_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_136_sign station_139_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_139_sign station_281o2_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_281o2_sign station_142_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_142_sign station_144_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_144_sign station_147_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_147_sign station_149_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_149_sign station_301o2_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_301o2_sign station_152_sign
    · norm_num [ladder309o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_152_sign station_154_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 309/2` is on the line.** -/
theorem online_below_309o2 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 309/2 → ρ.re = 1/2 :=
  online_below_309o2_of_ladder ladder309o2Data_holds

/-- **The channel to height 154, unconditional.** -/
theorem seat_channel_to_154 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 154) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 309/2) online_below_309o2 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder309o2Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_309o2
#print axioms CriticalLinePhasor.DVP.seat_channel_to_154
end AxiomAudit
