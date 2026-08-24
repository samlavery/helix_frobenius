import RequestProject.DVPLadder
import RequestProject.DVPExhaustion63
import RequestProject.DVPStation60
import RequestProject.DVPStation62
import RequestProject.DVPChannelBase

/-!
# Rung-63: the extended ladder — on-line to 63, channel to 62.5

Two new certified stations (60 (+), 62 (−)) extend the Hardy ladder to
fifteen; with the census `N_all(63) = 14` every zero of ordinate
`|γ| ≤ 63` is on the line, and the compiled transfer extends the
unconditional channel to height `62.5`.
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The fifteen station heights. -/
def ladder63T (i : Fin 15) : ℝ :=
  if i.val = 0 then 11 else if i.val = 1 then 18 else if i.val = 2 then 23
  else if i.val = 3 then 28 else if i.val = 4 then 32
  else if i.val = 5 then 35 else if i.val = 6 then 39
  else if i.val = 7 then 42 else if i.val = 8 then 46
  else if i.val = 9 then 49 else if i.val = 10 then 52
  else if i.val = 11 then 55 else if i.val = 12 then 58
  else if i.val = 13 then 60 else 62

/-- **The extended ladder is inhabited.** -/
theorem ladder63Data_holds : LadderData63 := by
  refine ⟨ladder63T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder63T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder63T]
  · intro i
    fin_cases i <;>
      · norm_num [ladder63T]
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
        | exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
        | exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 63` is on the line.** -/
theorem online_below_63 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 63 → ρ.re = 1/2 :=
  online_below_63_of_ladder ladder63Data_holds

/-- **The channel to height 62.5, unconditional** — rung-63 through the
compiled transfer. -/
theorem seat_channel_to_62_5 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 125/2) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 63) online_below_63 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder63Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_63
#print axioms CriticalLinePhasor.DVP.seat_channel_to_62_5
end AxiomAudit
