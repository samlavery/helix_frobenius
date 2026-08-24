import RequestProject.DVPLadder435o2
import RequestProject.DVPExhaustion471o2
import RequestProject.DVPStation220
import RequestProject.DVPStation221
import RequestProject.DVPStation223
import RequestProject.DVPStation449o2
import RequestProject.DVPStation226
import RequestProject.DVPStation228
import RequestProject.DVPStation230
import RequestProject.DVPStation463o2
import RequestProject.DVPStation233
import RequestProject.DVPStation235

/-!
# Rung-235.5: on-line to 471/2, channel to 235
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The one hundred station heights. -/
def ladder471o2T (i : Fin 100) : ℝ :=
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
  else if i.val = 55 then 154
  else if i.val = 56 then 157
  else if i.val = 57 then 158
  else if i.val = 58 then 160
  else if i.val = 59 then 162
  else if i.val = 60 then 164
  else if i.val = 61 then 166
  else if i.val = 62 then 168
  else if i.val = 63 then 339/2
  else if i.val = 64 then 172
  else if i.val = 65 then 174
  else if i.val = 66 then 176
  else if i.val = 67 then 177
  else if i.val = 68 then 179
  else if i.val = 69 then 181
  else if i.val = 70 then 183
  else if i.val = 71 then 741/4
  else if i.val = 72 then 186
  else if i.val = 73 then 188
  else if i.val = 74 then 191
  else if i.val = 75 then 385/2
  else if i.val = 76 then 194
  else if i.val = 77 then 196
  else if i.val = 78 then 395/2
  else if i.val = 79 then 199
  else if i.val = 80 then 202
  else if i.val = 81 then 203
  else if i.val = 82 then 205
  else if i.val = 83 then 207
  else if i.val = 84 then 209
  else if i.val = 85 then 211
  else if i.val = 86 then 212
  else if i.val = 87 then 214
  else if i.val = 88 then 215
  else if i.val = 89 then 217
  else if i.val = 90 then 220
  else if i.val = 91 then 221
  else if i.val = 92 then 223
  else if i.val = 93 then 449/2
  else if i.val = 94 then 226
  else if i.val = 95 then 228
  else if i.val = 96 then 230
  else if i.val = 97 then 463/2
  else if i.val = 98 then 233
  else 235

set_option maxHeartbeats 51200000 in
/-- **The 100-station ladder is inhabited.** -/
theorem ladder471o2Data_holds : LadderData471o2 := by
  refine ⟨ladder471o2T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder471o2T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder471o2T]
  · intro i
    fin_cases i
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_74_sign station_76_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_76_sign station_78_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_78_sign station_80_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_80_sign station_84_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_84_sign station_86_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_86_sign station_88_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_88_sign station_90_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_90_sign station_93_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_93_sign station_95_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_95_sign station_97_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_97_sign station_100_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_100_sign station_102_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_102_sign station_105_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_105_sign station_106_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_106_sign station_108_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_108_sign station_223o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_223o2_sign station_113_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_113_sign station_115_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_115_sign station_118_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_118_sign station_120_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_120_sign station_122_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_122_sign station_247o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_247o2_sign station_125_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_125_sign station_128_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_128_sign station_130_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_130_sign station_132_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_132_sign station_134_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_134_sign station_136_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_136_sign station_139_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_139_sign station_281o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_281o2_sign station_142_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_142_sign station_144_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_144_sign station_147_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_147_sign station_149_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_149_sign station_301o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_301o2_sign station_152_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_152_sign station_154_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_154_sign station_157_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_157_sign station_158_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_158_sign station_160_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_160_sign station_162_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_162_sign station_164_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_164_sign station_166_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_166_sign station_168_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_168_sign station_339o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_339o2_sign station_172_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_172_sign station_174_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_174_sign station_176_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_176_sign station_177_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_177_sign station_179_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_179_sign station_181_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_181_sign station_183_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_183_sign station_741o4_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_741o4_sign station_186_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_186_sign station_188_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_188_sign station_191_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_191_sign station_385o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_385o2_sign station_194_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_194_sign station_196_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_196_sign station_395o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_395o2_sign station_199_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_199_sign station_202_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_202_sign station_203_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_203_sign station_205_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_205_sign station_207_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_207_sign station_209_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_209_sign station_211_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_211_sign station_212_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_212_sign station_214_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_214_sign station_215_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_215_sign station_217_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_217_sign station_220_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_220_sign station_221_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_221_sign station_223_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_223_sign station_449o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_449o2_sign station_226_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_226_sign station_228_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_228_sign station_230_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_230_sign station_463o2_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_463o2_sign station_233_sign
    · norm_num [ladder471o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_233_sign station_235_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 471/2` is on the line.** -/
theorem online_below_471o2 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 471/2 → ρ.re = 1/2 :=
  online_below_471o2_of_ladder ladder471o2Data_holds

/-- **The channel to height 235, unconditional.** -/
theorem seat_channel_to_235 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 235) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 471/2) online_below_471o2 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder471o2Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_471o2
#print axioms CriticalLinePhasor.DVP.seat_channel_to_235
end AxiomAudit
