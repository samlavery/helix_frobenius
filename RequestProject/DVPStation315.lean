import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 315` (rung-335.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT315 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((315 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((393/31250 : ℚ) : ℝ))

theorem st315_c1 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393/125000) (δ := 1/1000000000) (ψ := 393/31250) 315 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t1 : ((999821/1000000 : ℚ) : ℝ) ≤ stT315 1 := by
  have hc : ((999821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999821/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((999821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c2 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-11913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1978387/5000000) (δ := 317/20000000) (ψ := 393/31250) 315 35
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t2 : ((-21236184971/2500000000000 : ℚ) : ℝ) ≤ stT315 2 := by
  have hc : ((-12013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21236184971/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-12013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c3 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((889251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187727/10000000) (δ := 15807/1000000000) (ψ := 393/31250) 315 55
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t3 : ((2566757538401/5000000000000 : ℚ) : ℝ) ≤ stT315 3 := by
  have hc : ((889151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2566757538401/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((889151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c4 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1565179/2000000) (δ := 7903/500000000) (ψ := 393/31250) 315 69
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t4 : ((-5000186000037/10000000000000 : ℚ) : ℝ) ≤ stT315 4 := by
  have hc : ((-1000037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5000186000037/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-1000037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c5 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-79141/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4944079/10000000) (δ := 15783/1000000000) (ψ := 393/31250) 315 81
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t5 : ((-44252344737/250000000000 : ℚ) : ℝ) ≤ stT315 5 := by
  have hc : ((-79161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44252344737/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-79161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c6 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((458023/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2737567/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 90
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t6 : ((934731202443/5000000000000 : ℚ) : ℝ) ≤ stT315 6 := by
  have hc : ((457923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((934731202443/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((457923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c7 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-235809/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7007597/10000000) (δ := 3161/200000000) (ψ := 393/31250) 315 98
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t7 : ((-89136879893/250000000000 : ℚ) : ℝ) ≤ stT315 7 := by
  have hc : ((-117917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89136879893/250000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-117917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c8 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((2639/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3900601/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 104
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t8 : ((4620941631/1250000000000 : ℚ) : ℝ) ≤ stT315 8 := by
  have hc : ((1307/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4620941631/1250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((1307/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c9 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((285623/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1203467/5000000) (δ := 15891/1000000000) (ψ := 393/31250) 315 110
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t9 : ((951909904809/5000000000000 : ℚ) : ℝ) ≤ stT315 9 := by
  have hc : ((285573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((951909904809/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((285573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c10 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-459317/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6838511/10000000) (δ := 493/31250000) (ψ := 393/31250) 315 115
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t10 : ((-726323079013/2500000000000 : ℚ) : ℝ) ≤ stT315 10 := by
  have hc : ((-459367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-726323079013/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-459367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c11 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((11331/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3355477/10000000) (δ := 99/6250000) (ψ := 393/31250) 315 120
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t11 : ((17074584919/250000000000 : ℚ) : ℝ) ≤ stT315 11 := by
  have hc : ((5663/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17074584919/250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((5663/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c12 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-88863/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3331431/5000000) (δ := 497/31250000) (ψ := 393/31250) 315 125
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t12 : ((-8017322203/31250000000 : ℚ) : ℝ) ≤ stT315 12 := by
  have hc : ((-88873/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8017322203/31250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-88873/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c13 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-424381/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -201909/312500) (δ := 1991/125000000) (ψ := 393/31250) 315 129
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t13 : ((-1177159802931/5000000000000 : ℚ) : ℝ) ≤ stT315 13 := by
  have hc : ((-424431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1177159802931/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-424431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c14 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-332763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149221/312500) (δ := 15849/1000000000) (ψ := 393/31250) 315 132
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t14 : ((-889613981019/10000000000000 : ℚ) : ℝ) ≤ stT315 14 := by
  have hc : ((-332863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-889613981019/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-332863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c15 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((80759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3724873/10000000) (δ := 637/40000000) (ψ := 393/31250) 315 136
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t15 : ((52065142523/2500000000000 : ℚ) : ℝ) ≤ stT315 15 := by
  have hc : ((80659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52065142523/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((80659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c16 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12347/5000000) (δ := 497/31250000) (ψ := 393/31250) 315 139
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t16 : ((999851/4000000 : ℚ) : ℝ) ≤ stT315 16 := by
  have hc : ((999851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999851/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((999851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c17 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((971973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 593289/10000000) (δ := 7891/500000000) (ψ := 393/31250) 315 142
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t17 : ((589284502947/2500000000000 : ℚ) : ℝ) ≤ stT315 17 := by
  have hc : ((971873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((589284502947/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((971873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c18 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((410583/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1518361/10000000) (δ := 793/50000000) (ψ := 393/31250) 315 145
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t18 : ((483817656363/2500000000000 : ℚ) : ℝ) ≤ stT315 18 := by
  have hc : ((410533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483817656363/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((410533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c19 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-754529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6064331/10000000) (δ := 15939/1000000000) (ψ := 393/31250) 315 148
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t19 : ((-865619078691/5000000000000 : ℚ) : ℝ) ≤ stT315 19 := by
  have hc : ((-754629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-865619078691/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-754629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c20 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((394487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2913217/10000000) (δ := 7939/500000000) (ψ := 393/31250) 315 150
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t20 : ((881875755929/10000000000000 : ℚ) : ℝ) ≤ stT315 20 := by
  have hc : ((394387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881875755929/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((394387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c21 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-42353/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5788391/10000000) (δ := 15903/1000000000) (ψ := 393/31250) 315 153
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t21 : ((-369741863223/2500000000000 : ℚ) : ℝ) ≤ stT315 21 := by
  have hc : ((-169437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369741863223/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-169437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c22 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((974137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569817/10000000) (δ := 7907/500000000) (ψ := 393/31250) 315 155
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t22 : ((2076653702259/10000000000000 : ℚ) : ℝ) ≤ stT315 22 := by
  have hc : ((974037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2076653702259/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((974037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c23 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((44359/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3020049/10000000) (δ := 15829/1000000000) (ψ := 393/31250) 315 157
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t23 : ((23117209599/312500000000 : ℚ) : ℝ) ≤ stT315 23 := by
  have hc : ((88693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23117209599/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((88693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c24 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-114807/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5119807/10000000) (δ := 793/50000000) (ψ := 393/31250) 315 159
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t24 : ((-7324996917/78125000000 : ℚ) : ℝ) ≤ stT315 24 := by
  have hc : ((-7177/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7324996917/78125000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-7177/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c25 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-69591/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2925603/5000000) (δ := 15857/1000000000) (ψ := 393/31250) 315 161
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t25 : ((-139202069601/1000000000000 : ℚ) : ℝ) ≤ stT315 25 := by
  have hc : ((-69601/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139202069601/1000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-69601/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c26 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-529351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266079/500000) (δ := 15931/1000000000) (ψ := 393/31250) 315 163
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t26 : ((-519169591031/5000000000000 : ℚ) : ℝ) ≤ stT315 26 := by
  have hc : ((-529451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519169591031/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-529451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c27 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((2401/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181307/500000) (δ := 15817/1000000000) (ψ := 393/31250) 315 165
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t27 : ((9233751/400000000 : ℚ) : ℝ) ≤ stT315 27 := by
  have hc : ((2399/20000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9233751/400000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((2399/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c28 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((14731/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849777/10000000) (δ := 15903/1000000000) (ψ := 393/31250) 315 167
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t28 : ((222688120281/1250000000000 : ℚ) : ℝ) ≤ stT315 28 := by
  have hc : ((235671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222688120281/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((235671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c29 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((24229/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11727/40000) (δ := 3183/200000000) (ψ := 393/31250) 315 169
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t29 : ((179922033123/2500000000000 : ℚ) : ℝ) ≤ stT315 29 := by
  have hc : ((96891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179922033123/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((96891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c30 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-996681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3825123/5000000) (δ := 7937/500000000) (ψ := 393/31250) 315 171
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t30 : ((-909932468251/5000000000000 : ℚ) : ℝ) ≤ stT315 30 := by
  have hc : ((-996781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-909932468251/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-996781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c31 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((552417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2463837/10000000) (δ := 15867/1000000000) (ψ := 393/31250) 315 172
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t31 : ((991990604801/10000000000000 : ℚ) : ℝ) ≤ stT315 31 := by
  have hc : ((552317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((991990604801/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((552317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c32 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-9199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -987497/2500000) (δ := 1969/125000000) (ψ := 393/31250) 315 174
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t32 : ((-16438465333/10000000000000 : ℚ) : ℝ) ≤ stT315 32 := by
  have hc : ((-9299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16438465333/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-9299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c33 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-256189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1143671/2500000) (δ := 7929/500000000) (ψ := 393/31250) 315 175
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t33 : ((-446141996553/10000000000000 : ℚ) : ℝ) ≤ stT315 33 := by
  have hc : ((-256289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446141996553/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-256289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c34 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((117877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -666401/2000000) (δ := 31/1953125) (ψ := 393/31250) 315 177
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t34 : ((40414307519/1000000000000 : ℚ) : ℝ) ≤ stT315 34 := by
  have hc : ((117827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40414307519/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((117827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c35 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((13923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 473461/1250000) (δ := 15879/1000000000) (ψ := 393/31250) 315 178
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t35 : ((2936487573/312500000000 : ℚ) : ℝ) ≤ stT315 35 := by
  have hc : ((6949/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2936487573/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((6949/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c36 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-570131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088731/2000000) (δ := 7897/500000000) (ψ := 393/31250) 315 180
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t36 : ((-950385190077/10000000000000 : ℚ) : ℝ) ≤ stT315 36 := by
  have hc : ((-570231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-950385190077/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-570231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c37 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((492789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212547/5000000) (δ := 7901/500000000) (ψ := 393/31250) 315 181
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t37 : ((810057495871/5000000000000 : ℚ) : ℝ) ≤ stT315 37 := by
  have hc : ((492739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810057495871/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((492739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c38 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-656779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2859169/5000000) (δ := 3179/200000000) (ψ := 393/31250) 315 182
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t38 : ((-213119793397/2000000000000 : ℚ) : ℝ) ≤ stT315 38 := by
  have hc : ((-656879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213119793397/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-656879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c39 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-12551/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2620941/5000000) (δ := 789/50000000) (ψ := 393/31250) 315 184
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t39 : ((-20101693587/250000000000 : ℚ) : ℝ) ≤ stT315 39 := by
  have hc : ((-25107/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20101693587/250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-25107/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c40 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((919169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506039/5000000) (δ := 15873/1000000000) (ψ := 393/31250) 315 185
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t40 : ((726587460261/5000000000000 : ℚ) : ℝ) ≤ stT315 40 := by
  have hc : ((919069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((726587460261/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((919069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c41 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((9247/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1362691/5000000) (δ := 15937/1000000000) (ψ := 393/31250) 315 186
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t41 : ((2887651713/40000000000 : ℚ) : ℝ) ≤ stT315 41 := by
  have hc : ((1849/4000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2887651713/40000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((1849/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c42 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-367923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2997139/5000000) (δ := 15859/1000000000) (ψ := 393/31250) 315 187
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t42 : ((-283897425041/2500000000000 : ℚ) : ℝ) ≤ stT315 42 := by
  have hc : ((-367973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283897425041/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-367973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c43 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-926783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344569/500000) (δ := 3189/200000000) (ψ := 393/31250) 315 189
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t43 : ((-706741799319/5000000000000 : ℚ) : ℝ) ≤ stT315 43 := by
  have hc : ((-926883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706741799319/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-926883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c44 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-112649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -561889/1250000) (δ := 15937/1000000000) (ψ := 393/31250) 315 190
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t44 : ((-169900166343/5000000000000 : ℚ) : ℝ) ≤ stT315 44 := by
  have hc : ((-112699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169900166343/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-112699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c45 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((538367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501149/2000000) (δ := 1583/100000000) (ψ := 393/31250) 315 191
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t45 : ((802400537837/10000000000000 : ℚ) : ℝ) ≤ stT315 45 := by
  have hc : ((538267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((802400537837/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((538267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c46 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((116893/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226331/2500000) (δ := 397/25000000) (ψ := 393/31250) 315 192
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t46 : ((344661659859/2500000000000 : ℚ) : ℝ) ≤ stT315 46 := by
  have hc : ((233761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344661659859/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((233761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c47 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((991669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80731/2500000) (δ := 15887/1000000000) (ψ := 393/31250) 315 193
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t47 : ((1446351130281/10000000000000 : ℚ) : ℝ) ≤ stT315 47 := by
  have hc : ((991569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1446351130281/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((991569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c48 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((444003/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1194513/10000000) (δ := 7897/500000000) (ψ := 393/31250) 315 194
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t48 : ((5126325291/40000000000 : ℚ) : ℝ) ≤ stT315 48 := by
  have hc : ((443953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5126325291/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((443953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c49 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((771457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172417/1000000) (δ := 7951/500000000) (ψ := 393/31250) 315 195
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t49 : ((1101938240847/10000000000000 : ℚ) : ℝ) ≤ stT315 49 := by
  have hc : ((771357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1101938240847/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((771357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c50 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((717657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1925911/10000000) (δ := 7947/500000000) (ψ := 393/31250) 315 196
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t50 : ((1014778437641/10000000000000 : ℚ) : ℝ) ≤ stT315 50 := by
  have hc : ((717557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1014778437641/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((717557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c51 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((1497/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113281/625000) (δ := 3979/250000000) (ψ := 393/31250) 315 197
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t51 : ((65498097/625000000 : ℚ) : ℝ) ≤ stT315 51 := by
  have hc : ((1871/2500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65498097/625000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((1871/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c52 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((848043/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698143/5000000) (δ := 789/50000000) (ψ := 393/31250) 315 198
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t52 : ((4703539821/40000000000 : ℚ) : ℝ) ≤ stT315 52 := by
  have hc : ((847943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4703539821/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((847943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c53 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((481143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34439/500000) (δ := 15873/1000000000) (ψ := 393/31250) 315 199
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t53 : ((132166350053/1000000000000 : ℚ) : ℝ) ≤ stT315 53 := by
  have hc : ((481093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132166350053/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((481093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c54 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((992849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149577/5000000) (δ := 15837/1000000000) (ψ := 393/31250) 315 200
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t54 : ((1350959643423/10000000000000 : ℚ) : ℝ) ≤ stT315 54 := by
  have hc : ((992749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1350959643423/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((992749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c55 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((812201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557201/10000000) (δ := 3169/200000000) (ψ := 393/31250) 315 201
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t55 : ((1095036176299/10000000000000 : ℚ) : ℝ) ≤ stT315 55 := by
  have hc : ((812101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1095036176299/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((812101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c56 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((334013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -768899/2500000) (δ := 15851/1000000000) (ψ := 393/31250) 315 202
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t56 : ((223104972689/5000000000000 : ℚ) : ℝ) ≤ stT315 56 := by
  have hc : ((333913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223104972689/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((333913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c57 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-359053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1211281/2500000) (δ := 15759/1000000000) (ψ := 393/31250) 315 203
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t57 : ((-475710000549/10000000000000 : ℚ) : ℝ) ≤ stT315 57 := by
  have hc : ((-359153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475710000549/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-359153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c58 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-921537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1371409/2000000) (δ := 15837/1000000000) (ψ := 393/31250) 315 204
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t58 : ((-242033857481/2000000000000 : ℚ) : ℝ) ≤ stT315 58 := by
  have hc : ((-921637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242033857481/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-921637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c59 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-438869/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1320959/2000000) (δ := 15837/1000000000) (ψ := 393/31250) 315 204
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t59 : ((-57142425691/500000000000 : ℚ) : ℝ) ≤ stT315 59 := by
  have hc : ((-438919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57142425691/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-438919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c60 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-513/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4132423/10000000) (δ := 1583/100000000) (ψ := 393/31250) 315 205
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t60 : ((-1060939691/100000000000 : ℚ) : ℝ) ≤ stT315 60 := by
  have hc : ((-4109/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060939691/100000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-4109/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c61 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((26199/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360321/2500000) (δ := 397/25000000) (ψ := 393/31250) 315 206
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t61 : ((16770180041/156250000000 : ℚ) : ℝ) ≤ stT315 61 := by
  have hc : ((209567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16770180041/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((209567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c62 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((33357/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45673/312500) (δ := 3163/200000000) (ψ := 393/31250) 315 207
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t62 : ((42358343353/400000000000 : ℚ) : ℝ) ≤ stT315 62 := by
  have hc : ((33353/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42358343353/400000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((33353/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c63 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-127031/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142787/312500) (δ := 3159/200000000) (ψ := 393/31250) 315 208
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t63 : ((-80053532221/2500000000000 : ℚ) : ℝ) ≤ stT315 63 := by
  have hc : ((-127081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80053532221/2500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-127081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c64 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999963/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3916301/5000000) (δ := 247/15625000) (ψ := 393/31250) 315 208
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t64 : ((-1250079750063/10000000000000 : ℚ) : ℝ) ≤ stT315 64 := by
  have hc : ((-1000063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1250079750063/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-1000063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c65 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-162163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1083549/2500000) (δ := 15901/1000000000) (ψ := 393/31250) 315 209
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t65 : ((-50315646881/2500000000000 : ℚ) : ℝ) ≤ stT315 65 := by
  have hc : ((-162263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50315646881/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-162263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c66 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((966453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 649389/10000000) (δ := 7947/500000000) (ψ := 393/31250) 315 210
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t66 : ((594748718321/5000000000000 : ℚ) : ℝ) ≤ stT315 66 := by
  have hc : ((966353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594748718321/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((966353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c67 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((280491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -804057/2500000) (δ := 15887/1000000000) (ψ := 393/31250) 315 211
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t67 : ((171276001177/5000000000000 : ℚ) : ℝ) ≤ stT315 67 := by
  have hc : ((280391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171276001177/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((280391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c68 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-971653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72573/100000) (δ := 15879/1000000000) (ψ := 393/31250) 315 212
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t68 : ((-1178424456287/10000000000000 : ℚ) : ℝ) ≤ stT315 68 := by
  have hc : ((-971753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1178424456287/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-971753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c69 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-124581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847851/2000000) (δ := 15879/1000000000) (ψ := 393/31250) 315 212
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t69 : ((-150098343979/10000000000000 : ℚ) : ℝ) ≤ stT315 69 := by
  have hc : ((-124681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150098343979/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-124681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c70 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((499243/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137607/10000000) (δ := 31/1953125) (ψ := 393/31250) 315 213
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t70 : ((149162362751/1250000000000 : ℚ) : ℝ) ≤ stT315 70 := by
  have hc : ((499193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149162362751/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((499193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c71 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-58967/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4675197/10000000) (δ := 7969/500000000) (ψ := 393/31250) 315 214
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t71 : ((-35002354917/1000000000000 : ℚ) : ℝ) ≤ stT315 71 := by
  have hc : ((-58987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35002354917/1000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-58987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c72 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-41097/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3169507/5000000) (δ := 7919/500000000) (ψ := 393/31250) 315 214
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t72 : ((-1513725007/15625000000 : ℚ) : ℝ) ≤ stT315 72 := by
  have hc : ((-20551/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1513725007/15625000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-20551/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c73 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((206713/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 746637/5000000) (δ := 7929/500000000) (ψ := 393/31250) 315 215
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t73 : ((7559684649/78125000000 : ℚ) : ℝ) ≤ stT315 73 := by
  have hc : ((12918/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7559684649/78125000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((12918/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c74 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((169857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3500279/10000000) (δ := 1969/125000000) (ψ := 393/31250) 315 216
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t74 : ((49334609583/2500000000000 : ℚ) : ℝ) ≤ stT315 74 := by
  have hc : ((169757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49334609583/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((169757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c75 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-475641/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1767603/2500000) (δ := 15851/1000000000) (ψ := 393/31250) 315 216
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t75 : ((-549280873391/5000000000000 : ℚ) : ℝ) ≤ stT315 75 := by
  have hc : ((-475691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549280873391/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-475691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c76 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((753637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448261/2500000) (δ := 15759/1000000000) (ψ := 393/31250) 315 217
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t76 : ((432182857443/5000000000000 : ℚ) : ℝ) ≤ stT315 76 := by
  have hc : ((753537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432182857443/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((753537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c77 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((122233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3620641/10000000) (δ := 249/15625000) (ψ := 393/31250) 315 218
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t77 : ((27836675493/2000000000000 : ℚ) : ℝ) ≤ stT315 77 := by
  have hc : ((122133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27836675493/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((122133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c78 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-173037/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6540787/10000000) (δ := 15767/1000000000) (ψ := 393/31250) 315 218
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t78 : ((-97974316923/1000000000000 : ℚ) : ℝ) ≤ stT315 78 := by
  have hc : ((-173057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97974316923/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-173057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c79 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((470383/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432393/5000000) (δ := 15829/1000000000) (ψ := 393/31250) 315 219
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t79 : ((529165543971/5000000000000 : ℚ) : ℝ) ≤ stT315 79 := by
  have hc : ((470333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529165543971/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((470333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c80 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-9831/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1234343/2500000) (δ := 15781/1000000000) (ψ := 393/31250) 315 220
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t80 : ((-10994187339/250000000000 : ℚ) : ℝ) ≤ stT315 80 := by
  have hc : ((-19667/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10994187339/250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-19667/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c81 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-11223/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4845347/10000000) (δ := 15881/1000000000) (ψ := 393/31250) 315 220
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t81 : ((-12473482201/312500000000 : ℚ) : ℝ) ≤ stT315 81 := by
  have hc : ((-89809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12473482201/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-89809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c82 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((887011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1199913/10000000) (δ := 3163/200000000) (ψ := 393/31250) 315 221
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t82 : ((195885824193/2000000000000 : ℚ) : ℝ) ≤ stT315 82 := by
  have hc : ((886911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195885824193/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((886911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c83 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-12259/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3681137/5000000) (δ := 3977/250000000) (ψ := 393/31250) 315 222
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t83 : ((-53829510363/500000000000 : ℚ) : ℝ) ≤ stT315 83 := by
  have hc : ((-49041/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53829510363/500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-49041/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c84 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((676661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 413789/2000000) (δ := 6339/200000000) (ψ := 393/31250) 315 222
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t84 : ((738188264929/10000000000000 : ℚ) : ℝ) ≤ stT315 84 := by
  have hc : ((676561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((738188264929/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((676561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c85 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-39079/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4319389/10000000) (δ := 15903/1000000000) (ψ := 393/31250) 315 223
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t85 : ((-662722983/39062500000 : ℚ) : ℝ) ≤ stT315 85 := by
  have hc : ((-2444/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662722983/39062500000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-2444/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c86 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-376197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4891211/10000000) (δ := 15903/1000000000) (ψ := 393/31250) 315 223
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t86 : ((-50721448927/1250000000000 : ℚ) : ℝ) ≤ stT315 86 := by
  have hc : ((-376297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50721448927/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-376297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c87 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((96801/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53517/312500) (δ := 15793/1000000000) (ψ := 393/31250) 315 224
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t87 : ((12971014039/156250000000 : ℚ) : ℝ) ≤ stT315 87 := by
  have hc : ((193577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12971014039/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((193577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c88 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-974443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7287557/10000000) (δ := 15893/1000000000) (ψ := 393/31250) 315 224
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t88 : ((-259716684043/2500000000000 : ℚ) : ℝ) ≤ stT315 88 := by
  have hc : ((-974543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259716684043/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-974543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c89 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((981781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9559/200000) (δ := 7943/500000000) (ψ := 393/31250) 315 225
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t89 : ((1040578914957/10000000000000 : ℚ) : ℝ) ≤ stT315 89 := by
  have hc : ((981681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1040578914957/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((981681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c90 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-168469/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6431039/10000000) (δ := 989/62500000) (ψ := 393/31250) 315 226
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t90 : ((-177603075477/2000000000000 : ℚ) : ℝ) ≤ stT315 90 := by
  have hc : ((-168489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177603075477/2000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-168489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c91 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((615097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1135359/5000000) (δ := 3953/125000000) (ψ := 393/31250) 315 226
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t91 : ((161172878787/2500000000000 : ℚ) : ℝ) ≤ stT315 91 := by
  have hc : ((614997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161172878787/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((614997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c92 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-11051/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4830619/10000000) (δ := 31/1953125) (ψ := 393/31250) 315 227
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t92 : ((-92197858109/2500000000000 : ℚ) : ℝ) ≤ stT315 92 := by
  have hc : ((-88433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92197858109/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-88433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c93 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((19491/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736593/2000000) (δ := 3943/250000000) (ψ := 393/31250) 315 227
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t93 : ((20190472921/2000000000000 : ℚ) : ℝ) ≤ stT315 93 := by
  have hc : ((19471/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20190472921/2000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((19471/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c94 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((32363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3602449/10000000) (δ := 7969/500000000) (ψ := 393/31250) 315 228
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t94 : ((16677046149/1250000000000 : ℚ) : ℝ) ≤ stT315 94 := by
  have hc : ((16169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16677046149/1250000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((16169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c95 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-316071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365477/5000000) (δ := 3173/200000000) (ψ := 393/31250) 315 228
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t95 : ((-324384806409/10000000000000 : ℚ) : ℝ) ≤ stT315 95 := by
  have hc : ((-316171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324384806409/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-316171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c96 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((230203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136543/500000) (δ := 7923/500000000) (ψ := 393/31250) 315 229
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t96 : ((11744937743/250000000000 : ℚ) : ℝ) ≤ stT315 96 := by
  have hc : ((230153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11744937743/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((230153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c97 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-35349/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085969/2000000) (δ := 7923/500000000) (ψ := 393/31250) 315 229
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t97 : ((-143591388087/2500000000000 : ℚ) : ℝ) ≤ stT315 97 := by
  have hc : ((-141421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143591388087/2500000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-141421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c98 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((159201/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17609/80000) (δ := 317/20000000) (ψ := 393/31250) 315 230
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t98 : ((2512374293/39062500000 : ℚ) : ℝ) ≤ stT315 98 := by
  have hc : ((19897/31250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2512374293/39062500000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((19897/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c99 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-21227/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 579389/1000000) (δ := 317/20000000) (ψ := 393/31250) 315 230
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t99 : ((-85348329479/1250000000000 : ℚ) : ℝ) ≤ stT315 99 := by
  have hc : ((-169841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85348329479/1250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-169841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c100 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((696861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -999731/5000000) (δ := 15843/1000000000) (ψ := 393/31250) 315 231
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t100 : ((696760303239/10000000000000 : ℚ) : ℝ) ≤ stT315 100 := by
  have hc : ((696761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((696760303239/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((696761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c101 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-691667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2918239/5000000) (δ := 15843/1000000000) (ψ := 393/31250) 315 231
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t101 : ((-344167226073/5000000000000 : ℚ) : ℝ) ≤ stT315 101 := by
  have hc : ((-691767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344167226073/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-691767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c102 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((331821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2112799/10000000) (δ := 3959/250000000) (ψ := 393/31250) 315 232
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t102 : ((328502060337/5000000000000 : ℚ) : ℝ) ≤ stT315 102 := by
  have hc : ((331771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328502060337/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((331771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c103 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-610947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557013/1000000) (δ := 15767/1000000000) (ψ := 393/31250) 315 232
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t103 : ((-60208294051/1000000000000 : ℚ) : ℝ) ≤ stT315 103 := by
  have hc : ((-611047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60208294051/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-611047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c104 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((132619/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2529087/10000000) (δ := 7887/500000000) (ψ := 393/31250) 315 233
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t104 : ((3250475613/62500000000 : ℚ) : ℝ) ≤ stT315 104 := by
  have hc : ((66297/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3250475613/62500000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((66297/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c105 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-418653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2503447/5000000) (δ := 15829/1000000000) (ψ := 393/31250) 315 233
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t105 : ((-408661471453/10000000000000 : ℚ) : ℝ) ≤ stT315 105 := by
  have hc : ((-418753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408661471453/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-418753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c106 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((136331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3236593/10000000) (δ := 15821/1000000000) (ψ := 393/31250) 315 234
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t106 : ((26473538217/1000000000000 : ℚ) : ℝ) ≤ stT315 106 := by
  have hc : ((136281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26473538217/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((136281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c107 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-46111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33263/80000) (δ := 7941/500000000) (ψ := 393/31250) 315 234
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t107 : ((-44625546657/5000000000000 : ℚ) : ℝ) ≤ stT315 107 := by
  have hc : ((-46161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44625546657/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-46161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c108 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-118703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4224449/10000000) (δ := 7957/500000000) (ψ := 393/31250) 315 235
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t108 : ((-114318305553/10000000000000 : ℚ) : ℝ) ≤ stT315 108 := by
  have hc : ((-118803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114318305553/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-118803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c109 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((34979/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379203/1250000) (δ := 15789/1000000000) (ψ := 393/31250) 315 235
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t109 : ((16747108697/500000000000 : ℚ) : ℝ) ≤ stT315 109 := by
  have hc : ((34969/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16747108697/500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((34969/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c110 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-291413/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42832/78125) (δ := 15907/1000000000) (ψ := 393/31250) 315 236
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t110 : ((-277899186369/5000000000000 : ℚ) : ℝ) ≤ stT315 110 := by
  have hc : ((-291463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277899186369/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-291463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c111 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((197847/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1644301/10000000) (δ := 1987/125000000) (ψ := 393/31250) 315 236
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t111 : ((93882068027/1250000000000 : ℚ) : ℝ) ≤ stT315 111 := by
  have hc : ((98911/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93882068027/1250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((98911/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c112 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-471171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700089/1000000) (δ := 15803/1000000000) (ψ := 393/31250) 315 237
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t112 : ((-27828898597/312500000000 : ℚ) : ℝ) ≤ stT315 112 := by
  have hc : ((-471221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27828898597/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-471221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c113 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -803/10000000) (δ := 159/10000000) (ψ := 393/31250) 315 237
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t113 : ((117578241/1250000000 : ℚ) : ℝ) ≤ stT315 113 := by
  have hc : ((9999/10000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117578241/1250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((9999/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c114 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-933561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1387509/2000000) (δ := 15803/1000000000) (ψ := 393/31250) 315 237
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t114 : ((-437226910673/5000000000000 : ℚ) : ℝ) ≤ stT315 114 := by
  have hc : ((-933661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437226910673/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-933661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c115 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((45429/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189263/1000000) (δ := 15893/1000000000) (ψ := 393/31250) 315 238
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t115 : ((21178448033/312500000000 : ℚ) : ℝ) ≤ stT315 115 := by
  have hc : ((181691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21178448033/312500000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((181691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c116 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-194443/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 985109/2000000) (δ := 15893/1000000000) (ψ := 393/31250) 315 238
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t116 : ((-180582277161/5000000000000 : ℚ) : ℝ) ≤ stT315 116 := by
  have hc : ((-194493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180582277161/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-194493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c117 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-4783/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160907/400000) (δ := 15917/1000000000) (ψ := 393/31250) 315 239
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t117 : ((-8866889091/2500000000000 : ℚ) : ℝ) ≤ stT315 117 := by
  have hc : ((-9591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8866889091/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-9591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c118 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((29909/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2679501/10000000) (δ := 15817/1000000000) (ψ := 393/31250) 315 239
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t118 : ((55055388357/1250000000000 : ℚ) : ℝ) ≤ stT315 118 := by
  have hc : ((119611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55055388357/1250000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((119611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c119 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-831813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6382907/10000000) (δ := 637/40000000) (ψ := 393/31250) 315 240
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t119 : ((-762613815187/10000000000000 : ℚ) : ℝ) ≤ stT315 119 := by
  have hc : ((-831913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-762613815187/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-831913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c120 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((99657/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207129/10000000) (δ := 633/40000000) (ψ := 393/31250) 315 240
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t120 : ((9096475689/100000000000 : ℚ) : ℝ) ≤ stT315 120 := by
  have hc : ((99647/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9096475689/100000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((99647/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c121 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-36111/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3371217/5000000) (δ := 633/40000000) (ψ := 393/31250) 315 240
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t121 : ((-6566364293/80000000000 : ℚ) : ℝ) ≤ stT315 121 := by
  have hc : ((-7223/8000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6566364293/80000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-7223/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c122 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((545673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2484011/10000000) (δ := 15871/1000000000) (ψ := 393/31250) 315 241
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t122 : ((493938334561/10000000000000 : ℚ) : ℝ) ≤ stT315 122 := by
  have hc : ((545573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493938334561/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((545573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c123 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-7039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 986147/2500000) (δ := 15771/1000000000) (ψ := 393/31250) 315 241
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t123 : ((-643702213/1000000000000 : ℚ) : ℝ) ≤ stT315 123 := by
  have hc : ((-7139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643702213/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-7139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c124 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-34457/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538683/1000000) (δ := 15839/1000000000) (ψ := 393/31250) 315 242
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t124 : ((-123795716031/2500000000000 : ℚ) : ℝ) ≤ stT315 124 := by
  have hc : ((-137853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123795716031/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-137853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c125 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((930357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 938527/10000000) (δ := 1983/125000000) (ψ := 393/31250) 315 242
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t125 : ((832046977739/10000000000000 : ℚ) : ℝ) ≤ stT315 125 := by
  have hc : ((930257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832046977739/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((930257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c126 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-3023/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1442697/2000000) (δ := 15839/1000000000) (ψ := 393/31250) 315 242
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t126 : ((-43094102883/500000000000 : ℚ) : ℝ) ≤ stT315 126 := by
  have hc : ((-48373/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43094102883/500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-48373/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c127 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((153893/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567303/2500000) (δ := 7923/500000000) (ψ := 393/31250) 315 243
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t127 : ((8533480813/156250000000 : ℚ) : ℝ) ≤ stT315 127 := by
  have hc : ((38467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8533480813/156250000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((38467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c128 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((7873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976827/2500000) (δ := 7923/500000000) (ψ := 393/31250) 315 243
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t128 : ((6870422559/10000000000000 : ℚ) : ℝ) ≤ stT315 128 := by
  have hc : ((7773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6870422559/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((7773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c129 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-642743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5672173/10000000) (δ := 15753/1000000000) (ψ := 393/31250) 315 244
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t129 : ((-565991762193/10000000000000 : ℚ) : ℝ) ≤ stT315 129 := by
  have hc : ((-642843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-565991762193/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-642843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c130 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((493327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204451/5000000) (δ := 15753/1000000000) (ψ := 393/31250) 315 244
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t130 : ((216316269533/2500000000000 : ℚ) : ℝ) ≤ stT315 130 := by
  have hc : ((493277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216316269533/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((493277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c131 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-845007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1610859/2500000) (δ := 15853/1000000000) (ψ := 393/31250) 315 244
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t131 : ((-147674842287/2000000000000 : ℚ) : ℝ) ≤ stT315 131 := by
  have hc : ((-845107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147674842287/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-845107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c132 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((103/400 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655181/2000000) (δ := 197/12500000) (ψ := 393/31250) 315 245
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t132 : ((280047339/12500000000 : ℚ) : ℝ) ≤ stT315 132 := by
  have hc : ((1287/5000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280047339/12500000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((1287/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c133 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((120687/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 533503/2000000) (δ := 197/12500000) (ψ := 393/31250) 315 245
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t133 : ((52313553079/1250000000000 : ℚ) : ℝ) ≤ stT315 133 := by
  have hc : ((60331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52313553079/1250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((60331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c134 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-959671/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7141561/10000000) (δ := 7917/250000000) (ψ := 393/31250) 315 246
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t134 : ((-829116413999/10000000000000 : ℚ) : ℝ) ≤ stT315 134 := by
  have hc : ((-959771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-829116413999/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-959771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c135 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((435241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -643269/5000000) (δ := 3967/250000000) (ψ := 393/31250) 315 246
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t135 : ((187276178221/2500000000000 : ℚ) : ℝ) ≤ stT315 135 := by
  have hc : ((435191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187276178221/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((435191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c136 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-118521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452529/1000000) (δ := 3187/200000000) (ψ := 393/31250) 315 246
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t136 : ((-101673802503/5000000000000 : ℚ) : ℝ) ≤ stT315 136 := by
  have hc : ((-118571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101673802503/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-118571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c137 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-560137/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5413369/10000000) (δ := 631/40000000) (ψ := 393/31250) 315 247
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t137 : ((-239321481423/5000000000000 : ℚ) : ℝ) ≤ stT315 137 := by
  have hc : ((-560237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239321481423/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-560237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c138 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((992129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156941/5000000) (δ := 3957/250000000) (ψ := 393/31250) 315 247
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t138 : ((105558829803/1250000000000 : ℚ) : ℝ) ≤ stT315 138 := by
  have hc : ((992029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105558829803/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((992029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c139 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-368679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1499967/2500000) (δ := 1991/125000000) (ψ := 393/31250) 315 247
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t139 : ((-312751881781/5000000000000 : ℚ) : ℝ) ≤ stT315 139 := by
  have hc : ((-368729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312751881781/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-368729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c140 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-54337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4062901/10000000) (δ := 7891/500000000) (ψ := 393/31250) 315 248
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t140 : ((-9201540547/2000000000000 : ℚ) : ℝ) ≤ stT315 140 := by
  have hc : ((-54437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9201540547/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-54437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c141 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((407861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1542051/10000000) (δ := 15921/1000000000) (ψ := 393/31250) 315 248
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t141 : ((343438441461/5000000000000 : ℚ) : ℝ) ≤ stT315 141 := by
  have hc : ((407811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343438441461/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((407811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c142 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-238937/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7107471/10000000) (δ := 15921/1000000000) (ψ := 393/31250) 315 248
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t142 : ((-50133152271/625000000000 : ℚ) : ℝ) ≤ stT315 142 := by
  have hc : ((-119481/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50133152271/625000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-119481/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c143 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((66913/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -768533/2500000) (δ := 7907/500000000) (ψ := 393/31250) 315 249
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t143 : ((27969368053/1000000000000 : ℚ) : ℝ) ≤ stT315 143 := by
  have hc : ((66893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27969368053/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((66893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c144 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((284521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2413641/10000000) (δ := 15889/1000000000) (ψ := 393/31250) 315 249
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t144 : ((237059071843/5000000000000 : ℚ) : ℝ) ≤ stT315 144 := by
  have hc : ((284471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237059071843/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((284471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c145 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7844429/10000000) (δ := 15807/1000000000) (ψ := 393/31250) 315 250
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t145 : ((-166106446463/2000000000000 : ℚ) : ℝ) ≤ stT315 145 := by
  have hc : ((-1000093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166106446463/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-1000093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c146 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((562981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121601/500000) (δ := 3949/250000000) (ψ := 393/31250) 315 250
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t146 : ((93168626001/2000000000000 : ℚ) : ℝ) ≤ stT315 146 := by
  have hc : ((562881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93168626001/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((562881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c147 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((383373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183961/625000) (δ := 15807/1000000000) (ψ := 393/31250) 315 250
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t147 : ((158059102289/5000000000000 : ℚ) : ℝ) ≤ stT315 147 := by
  have hc : ((383273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158059102289/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((383273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c148 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-985353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7425573/10000000) (δ := 497/31250000) (ψ := 393/31250) 315 251
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t148 : ((-162007487747/2000000000000 : ℚ) : ℝ) ≤ stT315 148 := by
  have hc : ((-985453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162007487747/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-985453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c149 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((660743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212247/1000000) (δ := 15899/1000000000) (ψ := 393/31250) 315 251
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t149 : ((541219225533/10000000000000 : ℚ) : ℝ) ≤ stT315 149 := by
  have hc : ((660643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541219225533/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((660643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c150 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((153853/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3145039/10000000) (δ := 15799/1000000000) (ψ := 393/31250) 315 251
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t150 : ((7848720893/312500000000 : ℚ) : ℝ) ≤ stT315 150 := by
  have hc : ((153803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7848720893/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((153803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c151 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-978141/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3665151/5000000) (δ := 3973/250000000) (ψ := 393/31250) 315 252
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t151 : ((-796081765149/10000000000000 : ℚ) : ℝ) ≤ stT315 151 := by
  have hc : ((-978241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-796081765149/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-978241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c152 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((328901/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8529/40000) (δ := 15911/1000000000) (ψ := 393/31250) 315 252
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t152 : ((266733348057/5000000000000 : ℚ) : ℝ) ≤ stT315 152 := by
  have hc : ((328851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266733348057/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((328851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c153 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((35051/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1515851/5000000) (δ := 987/62500000) (ψ := 393/31250) 315 252
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t153 : ((7082241633/250000000000 : ℚ) : ℝ) ≤ stT315 153 := by
  have hc : ((35041/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7082241633/250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((35041/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c154 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-496209/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509187/2000000) (δ := 3157/200000000) (ψ := 393/31250) 315 253
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t154 : ((-399896916157/5000000000000 : ℚ) : ℝ) ≤ stT315 154 := by
  have hc : ((-496259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399896916157/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-496259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c155 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((17419/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2448841/10000000) (δ := 7909/500000000) (ψ := 393/31250) 315 253
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t155 : ((111910093613/2500000000000 : ℚ) : ℝ) ≤ stT315 155 := by
  have hc : ((139327/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111910093613/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((139327/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c156 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((250433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2615493/10000000) (δ := 7959/500000000) (ψ := 393/31250) 315 253
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t156 : ((313229133/7812500000 : ℚ) : ℝ) ≤ stT315 156 := by
  have hc : ((250383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313229133/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((250383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c157 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-99659/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382373/500000) (δ := 3157/200000000) (ψ := 393/31250) 315 253
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t157 : ((-79544533203/1000000000000 : ℚ) : ℝ) ≤ stT315 157 := by
  have hc : ((-99669/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79544533203/1000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-99669/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c158 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((67939/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -765127/2500000) (δ := 633/40000000) (ψ := 393/31250) 315 254
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t158 : ((54033435883/2000000000000 : ℚ) : ℝ) ≤ stT315 158 := by
  have hc : ((67919/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54033435883/2000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((67919/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c159 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((722631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907987/10000000) (δ := 633/40000000) (ψ := 393/31250) 315 254
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t159 : ((573003932081/10000000000000 : ℚ) : ℝ) ≤ stT315 159 := by
  have hc : ((722531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((573003932081/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((722531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c160 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-919703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6845297/10000000) (δ := 633/40000000) (ψ := 393/31250) 315 254
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t160 : ((-72716865771/1000000000000 : ℚ) : ℝ) ≤ stT315 160 := by
  have hc : ((-919803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72716865771/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-919803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c161 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-11663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -989037/2500000) (δ := 15871/1000000000) (ψ := 393/31250) 315 255
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t161 : ((-9270549693/10000000000000 : ℚ) : ℝ) ≤ stT315 161 := by
  have hc : ((-11763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9270549693/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-11763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c162 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((933041/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230013/2500000) (δ := 15871/1000000000) (ψ := 393/31250) 315 255
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t162 : ((366493743617/5000000000000 : ℚ) : ℝ) ≤ stT315 162 := by
  have hc : ((932941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366493743617/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((932941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c163 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-671109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5766249/10000000) (δ := 3983/250000000) (ψ := 393/31250) 315 255
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t163 : ((-525731832549/10000000000000 : ℚ) : ℝ) ≤ stT315 163 := by
  have hc : ((-671209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-525731832549/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-671209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c164 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-230573/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5125207/10000000) (δ := 15839/1000000000) (ψ := 393/31250) 315 256
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t164 : ((-180086351387/5000000000000 : ℚ) : ℝ) ≤ stT315 164 := by
  have hc : ((-230623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180086351387/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-230623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c165 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((7927/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67599/2000000) (δ := 1983/125000000) (ψ := 393/31250) 315 256
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t165 : ((15426327119/200000000000 : ℚ) : ℝ) ≤ stT315 165 := by
  have hc : ((39631/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15426327119/200000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((39631/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c166 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-49013/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4420317/10000000) (δ := 15939/1000000000) (ψ := 393/31250) 315 256
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t166 : ((-19030446369/1250000000000 : ℚ) : ℝ) ≤ stT315 166 := by
  have hc : ((-24519/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19030446369/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-24519/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c167 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-434293/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6557843/10000000) (δ := 3939/250000000) (ψ := 393/31250) 315 257
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t167 : ((-5251641213/78125000000 : ℚ) : ℝ) ≤ stT315 167 := by
  have hc : ((-434343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5251641213/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-434343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c168 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((736743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1856389/10000000) (δ := 15847/1000000000) (ψ := 393/31250) 315 257
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t168 : ((142082965197/2500000000000 : ℚ) : ℝ) ≤ stT315 168 := by
  have hc : ((736643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142082965197/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((736643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c169 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((26841/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1408633/5000000) (δ := 15847/1000000000) (ψ := 393/31250) 315 257
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t169 : ((8256837897/250000000000 : ℚ) : ℝ) ≤ stT315 169 := by
  have hc : ((107339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8256837897/250000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((107339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c170 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-987813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93291/125000) (δ := 15947/1000000000) (ψ := 393/31250) 315 257
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t170 : ((-151538938809/2000000000000 : ℚ) : ℝ) ≤ stT315 170 := by
  have hc : ((-987913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151538938809/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-987913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c171 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((60069/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1812959/5000000) (δ := 15949/1000000000) (ψ := 393/31250) 315 258
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t171 : ((45897669661/5000000000000 : ℚ) : ℝ) ≤ stT315 171 := by
  have hc : ((60019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45897669661/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((60019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c172 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((231571/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241479/2500000) (δ := 15849/1000000000) (ψ := 393/31250) 315 258
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t172 : ((22068996579/312500000000 : ℚ) : ℝ) ≤ stT315 172 := by
  have hc : ((115773/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22068996579/312500000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((115773/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c173 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-598523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1382783/2500000) (δ := 15949/1000000000) (ψ := 393/31250) 315 258
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t173 : ((-227562343089/5000000000000 : ℚ) : ℝ) ≤ stT315 173 := by
  have hc : ((-598623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227562343089/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-598623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c174 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-126437/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5637917/10000000) (δ := 15761/1000000000) (ψ := 393/31250) 315 259
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t174 : ((-95866925243/2000000000000 : ℚ) : ℝ) ≤ stT315 174 := by
  have hc : ((-126457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95866925243/2000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-126457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c175 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((900449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1124991/10000000) (δ := 7921/500000000) (ψ := 393/31250) 315 259
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t175 : ((85074877359/1250000000000 : ℚ) : ℝ) ≤ stT315 175 := by
  have hc : ((900349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85074877359/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((900349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c176 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((112003/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420273/1250000) (δ := 7921/500000000) (ψ := 393/31250) 315 259
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t176 : ((42193854217/2500000000000 : ℚ) : ℝ) ≤ stT315 176 := by
  have hc : ((111953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42193854217/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((111953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c177 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-124991/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3912001/5000000) (δ := 15861/1000000000) (ψ := 393/31250) 315 259
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t177 : ((-187917011529/2500000000000 : ℚ) : ℝ) ≤ stT315 177 := by
  have hc : ((-250007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187917011529/2500000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-250007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c178 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((47671/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215459/625000) (δ := 1971/125000000) (ψ := 393/31250) 315 260
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t178 : ((17856077013/1250000000000 : ℚ) : ℝ) ≤ stT315 178 := by
  have hc : ((23823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17856077013/1250000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((23823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c179 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((926503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 964467/10000000) (δ := 3167/200000000) (ψ := 393/31250) 315 260
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t179 : ((138485205261/2000000000000 : ℚ) : ℝ) ≤ stT315 179 := by
  have hc : ((926403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138485205261/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((926403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c180 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-539511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535163/1000000) (δ := 3967/250000000) (ψ := 393/31250) 315 260
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t180 : ((-100550574129/2500000000000 : ℚ) : ℝ) ≤ stT315 180 := by
  have hc : ((-539611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100550574129/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-539611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c181 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-147123/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2996713/5000000) (δ := 631/40000000) (ψ := 393/31250) 315 261
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t181 : ((-21874131237/400000000000 : ℚ) : ℝ) ≤ stT315 181 := by
  have hc : ((-147143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21874131237/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-147143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c182 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((788859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206827/1250000) (δ := 631/40000000) (ψ := 393/31250) 315 261
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t182 : ((584666819991/10000000000000 : ℚ) : ℝ) ≤ stT315 182 := by
  have hc : ((788759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584666819991/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((788759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c183 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((485207/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266049/1000000) (δ := 3957/250000000) (ψ := 393/31250) 315 261
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t183 : ((358601281647/10000000000000 : ℚ) : ℝ) ≤ stT315 183 := by
  have hc : ((485107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358601281647/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((485107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c184 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-116953/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139041/200000) (δ := 3957/250000000) (ψ := 393/31250) 315 261
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t184 : ((-17245627251/250000000000 : ℚ) : ℝ) ≤ stT315 184 := by
  have hc : ((-233931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17245627251/250000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-233931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c185 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-222363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140237/312500) (δ := 15883/1000000000) (ψ := 393/31250) 315 262
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t185 : ((-32711626909/2000000000000 : ℚ) : ℝ) ≤ stT315 185 := by
  have hc : ((-222463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32711626909/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-222463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c186 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((497653/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242329/10000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 262
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t186 : ((72971987141/1000000000000 : ℚ) : ℝ) ≤ stT315 186 := by
  have hc : ((497603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72971987141/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((497603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c187 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-213/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1990123/5000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 262
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t187 : ((-78246211/50000000000 : ℚ) : ℝ) ≤ stT315 187 := by
  have hc : ((-107/5000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78246211/50000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-107/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c188 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-495749/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117621/156250) (δ := 15813/1000000000) (ψ := 393/31250) 315 263
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t188 : ((-14463944227/200000000000 : ℚ) : ℝ) ≤ stT315 188 := by
  have hc : ((-495799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14463944227/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-495799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c189 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((228761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1674989/5000000) (δ := 15913/1000000000) (ψ := 393/31250) 315 263
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t189 : ((5197693191/312500000000 : ℚ) : ℝ) ≤ stT315 189 := by
  have hc : ((228661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5197693191/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((228661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c190 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((948521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40283/500000) (δ := 1579/100000000) (ψ := 393/31250) 315 263
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t190 : ((172014168349/2500000000000 : ℚ) : ℝ) ≤ stT315 190 := by
  have hc : ((948421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172014168349/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((948421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c191 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-78809/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2469781/5000000) (δ := 15913/1000000000) (ψ := 393/31250) 315 263
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t191 : ((-2281547747/80000000000 : ℚ) : ℝ) ≤ stT315 191 := by
  have hc : ((-78829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2281547747/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-78829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c192 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-221849/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331231/2000000) (δ := 7953/500000000) (ψ := 393/31250) 315 264
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t192 : ((-10007737707/156250000000 : ℚ) : ℝ) ≤ stT315 192 := by
  have hc : ((-110937/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10007737707/156250000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-110937/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c193 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((259079/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10261/40000) (δ := 7953/500000000) (ψ := 393/31250) 315 264
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t193 : ((37290591927/1000000000000 : ℚ) : ℝ) ≤ stT315 193 := by
  have hc : ((259029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37290591927/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((259029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c194 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((824307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30091/200000) (δ := 7953/500000000) (ψ := 393/31250) 315 264
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t194 : ((295873004653/5000000000000 : ℚ) : ℝ) ≤ stT315 194 := by
  have hc : ((824207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295873004653/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((824207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c195 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-151409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5553403/10000000) (δ := 15797/1000000000) (ψ := 393/31250) 315 264
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t195 : ((-10844415891/250000000000 : ℚ) : ℝ) ≤ stT315 195 := by
  have hc : ((-75717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10844415891/250000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-75717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c196 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-770593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6126419/10000000) (δ := 3951/250000000) (ψ := 393/31250) 315 265
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t196 : ((-275247610099/5000000000000 : ℚ) : ℝ) ≤ stT315 196 := by
  have hc : ((-770693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275247610099/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-770693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c197 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((330929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2118753/10000000) (δ := 15799/1000000000) (ψ := 393/31250) 315 265
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t197 : ((23574136113/500000000000 : ℚ) : ℝ) ≤ stT315 197 := by
  have hc : ((330879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23574136113/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((330879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c198 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((733433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467149/2500000) (δ := 3951/250000000) (ψ := 393/31250) 315 265
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t198 : ((521157029777/10000000000000 : ℚ) : ℝ) ≤ stT315 198 := by
  have hc : ((733333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521157029777/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((733333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c199 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-691489/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5835863/10000000) (δ := 15899/1000000000) (ψ := 393/31250) 315 265
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t199 : ((-245127496749/5000000000000 : ℚ) : ℝ) ≤ stT315 199 := by
  have hc : ((-691589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245127496749/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-691589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c200 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-716733/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481189/2500000) (δ := 15811/1000000000) (ψ := 393/31250) 315 266
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t200 : ((-506877632131/10000000000000 : ℚ) : ℝ) ≤ stT315 200 := by
  have hc : ((-716833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506877632131/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-716833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c201 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((697561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1997021/10000000) (δ := 15811/1000000000) (ψ := 393/31250) 315 266
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t201 : ((98390125809/2000000000000 : ℚ) : ℝ) ≤ stT315 201 := by
  have hc : ((697461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98390125809/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((697461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c202 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((721769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382221/2000000) (δ := 987/62500000) (ψ := 393/31250) 315 266
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t202 : ((507764143393/10000000000000 : ℚ) : ℝ) ≤ stT315 202 := by
  have hc : ((721669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507764143393/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((721669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c203 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-681061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 362501/625000) (δ := 3973/250000000) (ψ := 393/31250) 315 266
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t203 : ((-478081702943/10000000000000 : ℚ) : ℝ) ≤ stT315 203 := by
  have hc : ((-681161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478081702943/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-681161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c204 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-747621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509543/2500000) (δ := 3157/200000000) (ψ := 393/31250) 315 267
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t204 : ((-523510128661/10000000000000 : ℚ) : ℝ) ≤ stT315 204 := by
  have hc : ((-747721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523510128661/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-747721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c205 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((641059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2187297/10000000) (δ := 3157/200000000) (ψ := 393/31250) 315 267
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t205 : ((44766499437/1000000000000 : ℚ) : ℝ) ≤ stT315 205 := by
  have hc : ((640959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44766499437/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((640959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c206 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((791257/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411209/2500000) (δ := 7959/500000000) (ψ := 393/31250) 315 267
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t206 : ((551225190081/10000000000000 : ℚ) : ℝ) ≤ stT315 206 := by
  have hc : ((791157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((551225190081/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((791157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c207 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-574961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5458383/10000000) (δ := 3157/200000000) (ψ := 393/31250) 315 267
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t207 : ((-399695572989/10000000000000 : ℚ) : ℝ) ≤ stT315 207 := by
  have hc : ((-575061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399695572989/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-575061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c208 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-42367/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6454381/10000000) (δ := 7963/500000000) (ψ := 393/31250) 315 268
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t208 : ((-57382281/976562500 : ℚ) : ℝ) ≤ stT315 208 := by
  have hc : ((-10593/12500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57382281/976562500 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-10593/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c209 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((479291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1338687/5000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 268
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t209 : ((165731561687/5000000000000 : ℚ) : ℝ) ≤ stT315 209 := by
  have hc : ((479191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165731561687/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((479191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c210 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((453931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338/3125) (δ := 7913/500000000) (ψ := 393/31250) 315 268
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t210 : ((62641478453/1000000000000 : ℚ) : ℝ) ≤ stT315 210 := by
  have hc : ((453881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62641478453/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((453881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c211 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-175333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4822697/10000000) (δ := 15877/1000000000) (ψ := 393/31250) 315 268
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t211 : ((-120738743307/5000000000000 : ℚ) : ℝ) ≤ stT315 211 := by
  have hc : ((-175383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120738743307/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-175383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c212 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-38477/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7161887/10000000) (δ := 15833/1000000000) (ψ := 393/31250) 315 269
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t212 : ((-26428866243/400000000000 : ℚ) : ℝ) ≤ stT315 212 := by
  have hc : ((-38481/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26428866243/400000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-38481/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c213 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((187287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3455991/10000000) (δ := 1577/100000000) (ψ := 393/31250) 315 269
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t213 : ((32064571539/2500000000000 : ℚ) : ℝ) ≤ stT315 213 := by
  have hc : ((187187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32064571539/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((187187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c214 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((248919/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11629/500000) (δ := 1587/100000000) (ψ := 393/31250) 315 269
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t214 : ((17014020499/250000000000 : ℚ) : ℝ) ≤ stT315 214 := by
  have hc : ((124447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17014020499/250000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((124447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c215 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((4617/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780781/2000000) (δ := 1587/100000000) (ψ := 393/31250) 315 269
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t215 : ((1557333299/2500000000000 : ℚ) : ℝ) ≤ stT315 215 := by
  have hc : ((4567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1557333299/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((4567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c216 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-99301/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377911/500000) (δ := 1587/100000000) (ψ := 393/31250) 315 269
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t216 : ((-33786297377/500000000000 : ℚ) : ℝ) ≤ stT315 216 := by
  have hc : ((-99311/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33786297377/500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-99311/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c217 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-116007/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4512359/10000000) (δ := 99/6250000) (ψ := 393/31250) 315 270
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t217 : ((-15756942833/1000000000000 : ℚ) : ℝ) ≤ stT315 217 := by
  have hc : ((-116057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15756942833/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-116057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c218 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((187413/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89167/1000000) (δ := 797/50000000) (ψ := 393/31250) 315 270
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t218 : ((25383693601/400000000000 : ℚ) : ℝ) ≤ stT315 218 := by
  have hc : ((187393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25383693601/400000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((187393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c219 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((466919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2712481/10000000) (δ := 99/6250000) (ψ := 393/31250) 315 270
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t219 : ((315446870603/10000000000000 : ℚ) : ℝ) ≤ stT315 219 := by
  have hc : ((466819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315446870603/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((466819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c220 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-12703/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6300173/10000000) (δ := 15863/1000000000) (ψ := 393/31250) 315 270
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t220 : ((-685233283/12500000000 : ℚ) : ℝ) ≤ stT315 220 := by
  have hc : ((-203273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685233283/12500000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-203273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c221 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-691621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36477/62500) (δ := 3939/250000000) (ψ := 393/31250) 315 271
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t221 : ((-465302040233/10000000000000 : ℚ) : ℝ) ≤ stT315 221 := by
  have hc : ((-691721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465302040233/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-691721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c222 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((305913/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142567/625000) (δ := 15947/1000000000) (ψ := 393/31250) 315 271
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t222 : ((51320446907/1250000000000 : ℚ) : ℝ) ≤ stT315 222 := by
  have hc : ((305863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51320446907/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((305863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c223 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((109499/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314567/2500000) (δ := 15947/1000000000) (ψ := 393/31250) 315 271
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t223 : ((146635050477/2500000000000 : ℚ) : ℝ) ≤ stT315 223 := by
  have hc : ((218973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146635050477/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((218973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c224 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-83823/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4781779/10000000) (δ := 15847/1000000000) (ψ := 393/31250) 315 271
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t224 : ((-3501461037/156250000000 : ℚ) : ℝ) ≤ stT315 224 := by
  have hc : ((-10481/31250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3501461037/156250000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-10481/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c225 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-123107/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483669/2000000) (δ := 15949/1000000000) (ψ := 393/31250) 315 272
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t225 : ((-164159415413/2500000000000 : ℚ) : ℝ) ≤ stT315 225 := by
  have hc : ((-246239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164159415413/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-246239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c226 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490767/1250000) (δ := 15827/500000000) (ψ := 393/31250) 315 272
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t226 : ((8048799/500000000000 : ℚ) : ℝ) ≤ stT315 226 := by
  have hc : ((121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8048799/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c227 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((196779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89857/2000000) (δ := 15949/1000000000) (ψ := 393/31250) 315 272
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t227 : ((130593473757/2000000000000 : ℚ) : ℝ) ≤ stT315 227 := by
  have hc : ((196759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130593473757/2000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((196759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c228 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((178893/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12049/40000) (δ := 15949/1000000000) (ψ := 393/31250) 315 272
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t228 : ((59220819119/2500000000000 : ℚ) : ℝ) ≤ stT315 228 := by
  have hc : ((178843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59220819119/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((178843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c229 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-848249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1291733/2000000) (δ := 15949/1000000000) (ψ := 393/31250) 315 272
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t229 : ((-560605137831/10000000000000 : ℚ) : ℝ) ≤ stT315 229 := by
  have hc : ((-848349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560605137831/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-848349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c230 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-42893/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1454481/2500000) (δ := 7881/500000000) (ψ := 393/31250) 315 273
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t230 : ((-113147801457/2500000000000 : ℚ) : ℝ) ≤ stT315 230 := by
  have hc : ((-171597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113147801457/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-171597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c231 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((11461/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1200717/5000000) (δ := 7881/500000000) (ψ := 393/31250) 315 273
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t231 : ((7539460509/200000000000 : ℚ) : ℝ) ≤ stT315 231 := by
  have hc : ((11459/20000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7539460509/200000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((11459/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c232 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((460511/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1000251/10000000) (δ := 7881/500000000) (ψ := 393/31250) 315 273
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t232 : ((75576845313/1250000000000 : ℚ) : ℝ) ≤ stT315 232 := by
  have hc : ((460461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75576845313/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((460461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c233 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-183111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4387367/10000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 273
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t233 : ((-60012778371/5000000000000 : ℚ) : ℝ) ≤ stT315 233 := by
  have hc : ((-183211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60012778371/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-183211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c234 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7759993/10000000) (δ := 15941/1000000000) (ψ := 393/31250) 315 273
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t234 : ((-653324191353/10000000000000 : ℚ) : ℝ) ≤ stT315 234 := by
  have hc : ((-999393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653324191353/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-999393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c235 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-262011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -917951/2000000) (δ := 7917/500000000) (ψ := 393/31250) 315 274
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t235 : ((-170982606519/10000000000000 : ℚ) : ℝ) ≤ stT315 235 := by
  have hc : ((-262111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170982606519/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-262111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c236 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((219597/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -622897/5000000) (δ := 7967/500000000) (ψ := 393/31250) 315 274
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t236 : ((558316703/9765625000 : ℚ) : ℝ) ≤ stT315 236 := by
  have hc : ((54893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558316703/9765625000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((54893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c237 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((672217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2083993/10000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 274
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t237 : ((436586367573/10000000000000 : ℚ) : ℝ) ≤ stT315 237 := by
  have hc : ((672117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436586367573/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((672117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c238 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-27781/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5399761/10000000) (δ := 7967/500000000) (ψ := 393/31250) 315 274
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t238 : ((-2251374543/62500000000 : ℚ) : ℝ) ≤ stT315 238 := by
  have hc : ((-13893/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2251374543/62500000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-13893/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c239 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-943063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7006293/10000000) (δ := 493/31250000) (ψ := 393/31250) 315 275
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t239 : ((-610082157061/10000000000000 : ℚ) : ℝ) ≤ stT315 239 := by
  have hc : ((-943163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610082157061/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-943163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c240 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((83433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1859083/5000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 275
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t240 : ((53791201501/10000000000000 : ℚ) : ℝ) ≤ stT315 240 := by
  have hc : ((83333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53791201501/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((83333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c241 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((984289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -443741/10000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 275
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t241 : ((158492812371/2500000000000 : ℚ) : ℝ) ≤ stT315 241 := by
  have hc : ((984189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158492812371/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((984189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c242 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((214751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2817139/10000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 275
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t242 : ((17251869453/625000000000 : ℚ) : ℝ) ≤ stT315 242 := by
  have hc : ((214701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17251869453/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((214701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c243 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-754587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6064553/10000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 275
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t243 : ((-484132465187/10000000000000 : ℚ) : ℝ) ≤ stT315 243 := by
  have hc : ((-754687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484132465187/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-754687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c244 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-209407/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1281861/2000000) (δ := 15783/1000000000) (ψ := 393/31250) 315 276
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t244 : ((-3351880623/62500000000 : ℚ) : ℝ) ≤ stT315 244 := by
  have hc : ((-26179/31250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3351880623/62500000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-26179/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c245 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((291131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3188469/10000000) (δ := 31683/1000000000) (ψ := 393/31250) 315 276
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t245 : ((46483180289/2500000000000 : ℚ) : ℝ) ≤ stT315 245 := by
  have hc : ((291031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46483180289/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((291031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c246 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((99997/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9647/5000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 276
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t246 : ((7968663939/125000000000 : ℚ) : ℝ) ≤ stT315 246 := by
  have hc : ((99987/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7968663939/125000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((99987/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c247 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((281337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401753/1250000) (δ := 15883/1000000000) (ψ := 393/31250) 315 276
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t247 : ((44736650827/2500000000000 : ℚ) : ℝ) ≤ stT315 247 := by
  have hc : ((281237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44736650827/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((281237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c248 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-834673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6395839/10000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 276
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t248 : ((-530081689773/10000000000000 : ℚ) : ℝ) ≤ stT315 248 := by
  have hc : ((-834773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530081689773/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-834773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c249 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-19371/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3071573/5000000) (δ := 15813/1000000000) (ψ := 393/31250) 315 277
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t249 : ((-982197703/20000000000 : ℚ) : ℝ) ≤ stT315 249 := by
  have hc : ((-38747/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-982197703/20000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-38747/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c250 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((183643/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2986767/10000000) (δ := 1579/100000000) (ψ := 393/31250) 315 277
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t250 : ((23222862163/1000000000000 : ℚ) : ℝ) ≤ stT315 250 := by
  have hc : ((183593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23222862163/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((183593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c251 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((99803/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156933/10000000) (δ := 1579/100000000) (ψ := 393/31250) 315 277
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t251 : ((31494371421/500000000000 : ℚ) : ℝ) ≤ stT315 251 := by
  have hc : ((99793/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31494371421/500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((99793/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c252 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((252779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205507/625000) (δ := 1589/100000000) (ψ := 393/31250) 315 277
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t252 : ((7958630463/500000000000 : ℚ) : ℝ) ≤ stT315 252 := by
  have hc : ((252679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7958630463/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((252679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c253 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-209277/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6406927/10000000) (δ := 1589/100000000) (ψ := 393/31250) 315 277
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t253 : ((-13158712089/250000000000 : ℚ) : ℝ) ≤ stT315 253 := by
  have hc : ((-104651/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13158712089/250000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-104651/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c254 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-787663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6194507/10000000) (δ := 7953/500000000) (ψ := 393/31250) 315 278
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t254 : ((-1930807113/39062500000 : ℚ) : ℝ) ≤ stT315 254 := by
  have hc : ((-787763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1930807113/39062500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-787763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c255 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((324727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3100183/10000000) (δ := 7903/500000000) (ψ := 393/31250) 315 278
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t255 : ((12705576153/625000000000 : ℚ) : ℝ) ≤ stT315 255 := by
  have hc : ((324627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12705576153/625000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((324627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c256 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((499987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17987/10000000) (δ := 7953/500000000) (ψ := 393/31250) 315 278
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t256 : ((499937/8000000 : ℚ) : ℝ) ≤ stT315 256 := by
  have hc : ((499937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499937/8000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((499937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c257 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((171417/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3052161/10000000) (δ := 15797/1000000000) (ψ := 393/31250) 315 278
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t257 : ((53447824997/2500000000000 : ℚ) : ℝ) ≤ stT315 257 := by
  have hc : ((171367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53447824997/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((171367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c258 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-383249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6110417/10000000) (δ := 7903/500000000) (ψ := 393/31250) 315 278
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t258 : ((-238631608327/5000000000000 : ℚ) : ℝ) ≤ stT315 258 := by
  have hc : ((-383299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238631608327/5000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-383299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c259 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-433623/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3275551/5000000) (δ := 3181/200000000) (ψ := 393/31250) 315 279
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t259 : ((-26947139201/500000000000 : ℚ) : ℝ) ≤ stT315 259 := by
  have hc : ((-433673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26947139201/500000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-433673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c260 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((81751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439549/1250000) (δ := 3181/200000000) (ψ := 393/31250) 315 279
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t260 : ((50668754273/5000000000000 : ℚ) : ℝ) ≤ stT315 260 := by
  have hc : ((81701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50668754273/5000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((81701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c261 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((980593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493337/10000000) (δ := 3181/200000000) (ψ := 393/31250) 315 279
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t261 : ((75863684889/1250000000000 : ℚ) : ℝ) ≤ stT315 261 := by
  have hc : ((980493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75863684889/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((980493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c262 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((267091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2518141/10000000) (δ := 23699/500000000) (ψ := 393/31250) 315 279
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t262 : ((82489231941/2500000000000 : ℚ) : ℝ) ≤ stT315 262 := by
  have hc : ((267041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82489231941/2500000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((267041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c263 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-594347/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5518123/10000000) (δ := 3181/200000000) (ψ := 393/31250) 315 279
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t263 : ((-366552070269/10000000000000 : ℚ) : ℝ) ≤ stT315 263 := by
  have hc : ((-594447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366552070269/10000000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-594447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c264 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-966103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7201199/10000000) (δ := 11853/250000000) (ψ := 393/31250) 315 280
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t264 : ((-297328682987/5000000000000 : ℚ) : ℝ) ≤ stT315 264 := by
  have hc : ((-966203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297328682987/5000000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-966203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c265 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-29621/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2111949/5000000) (δ := 3953/250000000) (ψ := 393/31250) 315 280
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t265 : ((-1138213701/156250000000 : ℚ) : ℝ) ≤ stT315 265 := by
  have hc : ((-14823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1138213701/156250000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-14823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c266 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((876087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257779/10000000) (δ := 1989/125000000) (ψ := 393/31250) 315 280
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t266 : ((537101793193/10000000000000 : ℚ) : ℝ) ≤ stT315 266 := by
  have hc : ((875987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537101793193/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((875987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c267 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((778287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1697157/10000000) (δ := 3953/250000000) (ψ := 393/31250) 315 280
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t267 : ((47624266213/1000000000000 : ℚ) : ℝ) ≤ stT315 267 := by
  have hc : ((778187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47624266213/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((778187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c268 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-281763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160267/2500000) (δ := 15791/1000000000) (ψ := 393/31250) 315 280
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t268 : ((-5380482807/312500000000 : ℚ) : ℝ) ≤ stT315 268 := by
  have hc : ((-281863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5380482807/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-281863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c269 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-993737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7574033/10000000) (δ := 15791/1000000000) (ψ := 393/31250) 315 280
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t269 : ((-605953351107/10000000000000 : ℚ) : ℝ) ≤ stT315 269 := by
  have hc : ((-993837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605953351107/10000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-993837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c270 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-491609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5211833/10000000) (δ := 3971/250000000) (ψ := 393/31250) 315 281
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t270 : ((-299244754929/10000000000000 : ℚ) : ℝ) ≤ stT315 270 := by
  have hc : ((-491709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299244754929/10000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-491709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c271 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((605653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575131/2500000) (δ := 1973/125000000) (ψ := 393/31250) 315 281
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t271 : ((11495212599/312500000000 : ℚ) : ℝ) ≤ stT315 271 := by
  have hc : ((605553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11495212599/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((605553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c272 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((485669/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149999/2500000) (δ := 1973/125000000) (ψ := 393/31250) 315 281
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t272 : ((294449738841/5000000000000 : ℚ) : ℝ) ≤ stT315 272 := by
  have hc : ((485619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294449738841/5000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((485619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c273 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((173953/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697977/2000000) (δ := 15819/1000000000) (ψ := 393/31250) 315 281
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t273 : ((105220529631/10000000000000 : ℚ) : ℝ) ≤ stT315 273 := by
  have hc : ((173853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105220529631/10000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((173853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c274 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-41439/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63693/100000) (δ := 15819/1000000000) (ψ := 393/31250) 315 281
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t274 : ((-6259318403/125000000000 : ℚ) : ℝ) ≤ stT315 274 := by
  have hc : ((-10361/12500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6259318403/125000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-10361/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c275 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-106327/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161747/250000) (δ := 15877/1000000000) (ψ := 393/31250) 315 282
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t275 : ((-128250328617/2500000000000 : ℚ) : ℝ) ≤ stT315 275 := by
  have hc : ((-212679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128250328617/2500000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-212679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c276 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((125897/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -902853/2500000) (δ := 7913/500000000) (ψ := 393/31250) 315 282
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t276 : ((75720862413/10000000000000 : ℚ) : ℝ) ≤ stT315 276 := by
  have hc : ((125797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75720862413/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((125797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c277 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((190751/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763261/10000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 282
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t277 : ((114599004771/2000000000000 : ℚ) : ℝ) ≤ stT315 277 := by
  have hc : ((190731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114599004771/2000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((190731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c278 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((675001/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1037287/5000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 282
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t278 : ((5059732797/125000000000 : ℚ) : ℝ) ≤ stT315 278 := by
  have hc : ((674901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5059732797/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((674901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c279 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-76051/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225543/2500000) (δ := 7963/500000000) (ψ := 393/31250) 315 282
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t279 : ((-9108513327/400000000000 : ℚ) : ℝ) ≤ stT315 279 := by
  have hc : ((-76071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9108513327/400000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-76071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c280 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-998559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 964971/1250000) (δ := 7913/500000000) (ψ := 393/31250) 315 282
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t280 : ((-119362719657/2000000000000 : ℚ) : ℝ) ≤ stT315 280 := by
  have hc : ((-998659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119362719657/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-998659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c281 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-480747/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2590379/5000000) (δ := 1577/100000000) (ψ := 393/31250) 315 283
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t281 : ((-5736985557/200000000000 : ℚ) : ℝ) ≤ stT315 281 := by
  have hc : ((-480847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5736985557/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-480847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c282 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((289499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383243/10000000) (δ := 1577/100000000) (ψ := 393/31250) 315 283
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t282 : ((172364274459/5000000000000 : ℚ) : ℝ) ≤ stT315 282 := by
  have hc : ((289449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172364274459/5000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((289449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c283 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((986949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8087/200000) (δ := 15933/1000000000) (ψ := 393/31250) 315 283
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t283 : ((293310272931/5000000000000 : ℚ) : ℝ) ≤ stT315 283 := by
  have hc : ((986849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293310272931/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((986849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c284 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((146769/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3182177/10000000) (δ := 1577/100000000) (ψ := 393/31250) 315 283
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t284 : ((8706158741/500000000000 : ℚ) : ℝ) ≤ stT315 284 := by
  have hc : ((146719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8706158741/500000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((146719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c285 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-361891/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5950161/10000000) (δ := 15833/1000000000) (ψ := 393/31250) 315 283
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t285 : ((-214395389409/5000000000000 : ℚ) : ℝ) ≤ stT315 285 := by
  have hc : ((-361941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214395389409/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-361941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c286 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-188429/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3499713/5000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 284
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t286 : ((-111432343537/2000000000000 : ℚ) : ℝ) ≤ stT315 286 := by
  have hc : ((-188449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111432343537/2000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-188449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c287 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-8071/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265671/625000) (δ := 15841/1000000000) (ψ := 393/31250) 315 284
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t287 : ((-9535710569/1250000000000 : ℚ) : ℝ) ≤ stT315 287 := by
  have hc : ((-32309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9535710569/1250000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-32309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c288 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((164539/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755827/5000000) (δ := 7931/500000000) (ψ := 393/31250) 315 284
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t288 : ((19388728669/400000000000 : ℚ) : ℝ) ≤ stT315 288 := by
  have hc : ((164519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19388728669/400000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((164519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c289 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((883651/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217979/10000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 284
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t289 : ((103947124497/2000000000000 : ℚ) : ℝ) ≤ stT315 289 := by
  have hc : ((883551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103947124497/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((883551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c290 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-9/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12307/31250) (δ := 7881/500000000) (ψ := 393/31250) 315 284
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t290 : ((-13506083/50000000000 : ℚ) : ℝ) ≤ stT315 290 := by
  have hc : ((-23/5000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13506083/50000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-23/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c291 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-443041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6649051/10000000) (δ := 7931/500000000) (ψ := 393/31250) 315 284
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t291 : ((-259744818201/5000000000000 : ℚ) : ℝ) ≤ stT315 291 := by
  have hc : ((-443091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259744818201/5000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-443091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c292 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-103261/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3178657/5000000) (δ := 3987/250000000) (ψ := 393/31250) 315 285
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t292 : ((-60436271841/1250000000000 : ℚ) : ℝ) ≤ stT315 292 := by
  have hc : ((-206547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60436271841/1250000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-206547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c293 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((104601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3665009/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 285
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t293 : ((30525055603/5000000000000 : ℚ) : ℝ) ≤ stT315 293 := by
  have hc : ((104501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30525055603/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((104501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c294 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((923853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490959/5000000) (δ := 1981/125000000) (ψ := 393/31250) 315 285
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t294 : ((538742910883/10000000000000 : ℚ) : ℝ) ≤ stT315 294 := by
  have hc : ((923753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538742910883/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((923753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c295 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((24361/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1692117/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 285
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t295 : ((56726762793/1250000000000 : ℚ) : ℝ) ≤ stT315 295 := by
  have hc : ((194863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56726762793/1250000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((194863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c296 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-34239/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 544637/1250000) (δ := 3987/250000000) (ψ := 393/31250) 315 285
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t296 : ((-19912666901/2000000000000 : ℚ) : ℝ) ≤ stT315 296 := by
  have hc : ((-34259/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19912666901/2000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-34259/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c297 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-235991/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7013097/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 285
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t297 : ((-8559400509/156250000000 : ℚ) : ℝ) ≤ stT315 297 := by
  have hc : ((-14751/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8559400509/156250000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-14751/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c298 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-93773/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6047843/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 286
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t298 : ((-21731413347/500000000000 : ℚ) : ℝ) ≤ stT315 298 := by
  have hc : ((-187571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21731413347/500000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-187571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c299 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((205467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3409639/10000000) (δ := 3151/200000000) (ψ := 393/31250) 315 286
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t299 : ((59383305619/5000000000000 : ℚ) : ℝ) ≤ stT315 299 := by
  have hc : ((205367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59383305619/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((205367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c300 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((95169/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156051/2000000) (δ := 3171/200000000) (ψ := 393/31250) 315 286
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t300 : ((1098800973/20000000000 : ℚ) : ℝ) ≤ stT315 300 := by
  have hc : ((95159/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1098800973/20000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((95159/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c301 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((11579/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1840387/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 286
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t301 : ((10676990721/250000000000 : ℚ) : ℝ) ≤ stT315 301 := by
  have hc : ((185239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10676990721/250000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((185239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c302 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-208607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4452367/10000000) (δ := 1981/125000000) (ψ := 393/31250) 315 286
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t302 : ((-30024380313/2500000000000 : ℚ) : ℝ) ≤ stT315 302 := by
  have hc : ((-208707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30024380313/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-208707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c303 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-18989/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1411137/2000000) (δ := 3171/200000000) (ψ := 393/31250) 315 286
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t303 : ((-2182008927/40000000000 : ℚ) : ℝ) ≤ stT315 303 := by
  have hc : ((-18991/20000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2182008927/40000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-18991/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c304 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-150549/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1211509/2000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 287
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t304 : ((-4317867213/100000000000 : ℚ) : ℝ) ≤ stT315 304 := by
  have hc : ((-150569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4317867213/100000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-150569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c305 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((181231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694279/2000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 287
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t305 : ((51857624169/5000000000000 : ℚ) : ℝ) ≤ stT315 305 := by
  have hc : ((181131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51857624169/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((181131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c306 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((936797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111699/1250000) (δ := 7931/500000000) (ψ := 393/31250) 315 287
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t306 : ((535473143717/10000000000000 : ℚ) : ℝ) ≤ stT315 306 := by
  have hc : ((936697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535473143717/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((936697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c307 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((783647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335141/2000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 287
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t307 : ((44719377931/1000000000000 : ℚ) : ℝ) ≤ stT315 307 := by
  have hc : ((783547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44719377931/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((783547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c308 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-123549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847331/2000000) (δ := 15841/1000000000) (ψ := 393/31250) 315 287
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t308 : ((-70455571147/10000000000000 : ℚ) : ℝ) ≤ stT315 308 := by
  have hc : ((-123649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70455571147/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-123649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c309 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-182137/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848667/1250000) (δ := 15941/1000000000) (ψ := 393/31250) 315 287
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t309 : ((-103625656317/2000000000000 : ℚ) : ℝ) ≤ stT315 309 := by
  have hc : ((-182157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103625656317/2000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-182157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c310 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-414939/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3187107/5000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 288
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t310 : ((-117848991209/2500000000000 : ℚ) : ℝ) ≤ stT315 310 := by
  have hc : ((-414989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117848991209/2500000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-414989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c311 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((4453/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3837913/10000000) (δ := 15769/1000000000) (ψ := 393/31250) 315 288
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t311 : ((5035944407/2500000000000 : ℚ) : ℝ) ≤ stT315 311 := by
  have hc : ((8881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5035944407/2500000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((8881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c312 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((865849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309881/10000000) (δ := 7967/500000000) (ψ := 393/31250) 315 288
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t312 : ((245066703681/5000000000000 : ℚ) : ℝ) ≤ stT315 312 := by
  have hc : ((865749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245066703681/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((865749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c313 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((885119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210119/10000000) (δ := 7967/500000000) (ψ := 393/31250) 315 288
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t313 : ((500241944427/10000000000000 : ℚ) : ℝ) ≤ stT315 313 := by
  have hc : ((885019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((500241944427/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((885019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c314 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((8187/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3722087/10000000) (δ := 15769/1000000000) (ψ := 393/31250) 315 288
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t314 : ((1153635691/250000000000 : ℚ) : ℝ) ≤ stT315 314 := by
  have hc : ((8177/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1153635691/250000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((8177/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c315 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-397693/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6226101/10000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 288
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t315 : ((-224103122691/5000000000000 : ℚ) : ℝ) ≤ stT315 315 := by
  have hc : ((-397743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224103122691/5000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-397743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c316 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-188061/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6985803/10000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 289
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t316 : ((-6612739879/125000000000 : ℚ) : ℝ) ≤ stT315 316 := by
  have hc : ((-188081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6612739879/125000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-188081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c317 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-45261/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140553/312500) (δ := 3969/250000000) (ψ := 393/31250) 315 289
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t317 : ((-3179043167/250000000000 : ℚ) : ℝ) ≤ stT315 317 := by
  have hc : ((-45281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3179043167/250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-45281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c318 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((691701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1008693/5000000) (δ := 3969/250000000) (ψ := 393/31250) 315 289
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t318 : ((96957618993/2500000000000 : ℚ) : ℝ) ≤ stT315 318 := by
  have hc : ((691601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96957618993/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((691601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c319 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((983469/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227603/5000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 289
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t319 : ((137645109037/2500000000000 : ℚ) : ℝ) ≤ stT315 319 := by
  have hc : ((983369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137645109037/2500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((983369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c320 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((19601/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729981/2500000) (δ := 3969/250000000) (ψ := 393/31250) 315 289
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t320 : ((342327423/15625000000 : ℚ) : ℝ) ≤ stT315 320 := by
  have hc : ((4899/12500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342327423/15625000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((4899/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c321 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-274027/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5377081/10000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 289
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t321 : ((-76487490621/2500000000000 : ℚ) : ℝ) ≤ stT315 321 := by
  have hc : ((-274077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76487490621/2500000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-274077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c322 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-49997/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7826521/10000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 289
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t322 : ((-13932532279/250000000000 : ℚ) : ℝ) ≤ stT315 322 := by
  have hc : ((-25001/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13932532279/250000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-25001/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c323 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-113757/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2719781/5000000) (δ := 1973/125000000) (ψ := 393/31250) 315 290
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t323 : ((-12661445891/400000000000 : ℚ) : ℝ) ≤ stT315 323 := by
  have hc : ((-113777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12661445891/400000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-113777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c324 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((360403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502621/5000000) (δ := 1973/125000000) (ψ := 393/31250) 315 290
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t324 : ((40033626633/2000000000000 : ℚ) : ℝ) ≤ stT315 324 := by
  have hc : ((360303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40033626633/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((360303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c325 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((243337/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -289241/5000000) (δ := 1973/125000000) (ψ := 393/31250) 315 290
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t325 : ((84353229/1562500000 : ℚ) : ℝ) ≤ stT315 325 := by
  have hc : ((15207/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84353229/1562500000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((15207/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c326 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((29637/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14727/80000) (δ := 15919/1000000000) (ψ := 393/31250) 315 290
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t326 : ((2051522223/50000000000 : ℚ) : ℝ) ≤ stT315 326 := by
  have hc : ((29633/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2051522223/50000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((29633/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c327 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-129967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425283/1000000) (δ := 15919/1000000000) (ψ := 393/31250) 315 290
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t327 : ((-35963655567/5000000000000 : ℚ) : ℝ) ≤ stT315 327 := by
  have hc : ((-130067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35963655567/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-130067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c328 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-887637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3328731/5000000) (δ := 3971/250000000) (ψ := 393/31250) 315 290
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t328 : ((-245085543223/5000000000000 : ℚ) : ℝ) ≤ stT315 328 := by
  have hc : ((-887737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245085543223/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-887737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c329 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-55429/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6653273/10000000) (δ := 3953/250000000) (ψ := 393/31250) 315 291
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t329 : ((-61124902319/1250000000000 : ℚ) : ℝ) ≤ stT315 329 := by
  have hc : ((-221741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61124902319/1250000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-221741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c330 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-67057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4263289/10000000) (δ := 15791/1000000000) (ψ := 393/31250) 315 291
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t330 : ((-18470597787/2500000000000 : ℚ) : ℝ) ≤ stT315 330 := by
  have hc : ((-67107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18470597787/2500000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-67107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c331 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((365087/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37611/200000) (δ := 15891/1000000000) (ψ := 393/31250) 315 291
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t331 : ((200642222013/5000000000000 : ℚ) : ℝ) ≤ stT315 331 := by
  have hc : ((365037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200642222013/5000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((365037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c332 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((49023/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 247511/5000000) (δ := 3953/250000000) (ψ := 393/31250) 315 291
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t332 : ((13451053889/250000000000 : ℚ) : ℝ) ≤ stT315 332 := by
  have hc : ((24509/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13451053889/250000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((24509/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c333 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((103177/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715857/2500000) (δ := 1989/125000000) (ψ := 393/31250) 315 291
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t333 : ((883232553/39062500000 : ℚ) : ℝ) ≤ stT315 333 := by
  have hc : ((6447/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((883232553/39062500000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((6447/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c334 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-496101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5224747/10000000) (δ := 3953/250000000) (ψ := 393/31250) 315 291
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t334 : ((-33938659797/1250000000000 : ℚ) : ℝ) ≤ stT315 334 := by
  have hc : ((-496201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33938659797/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-496201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c335 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-993959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7579057/10000000) (δ := 3953/250000000) (ψ := 393/31250) 315 291
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t335 : ((-543113081181/10000000000000 : ℚ) : ℝ) ≤ stT315 335 := by
  have hc : ((-994059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543113081181/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-994059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c336 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-675673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445421/2500000) (δ := 3181/200000000) (ψ := 393/31250) 315 292
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t336 : ((-73732916257/2000000000000 : ℚ) : ℝ) ≤ stT315 336 := by
  have hc : ((-675773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73732916257/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-675773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c337 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((193021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3441391/10000000) (δ := 7899/500000000) (ψ := 393/31250) 315 292
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t337 : ((52545314007/5000000000000 : ℚ) : ℝ) ≤ stT315 337 := by
  have hc : ((192921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52545314007/5000000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((192921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c338 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((451683/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108107/10000000) (δ := 7949/500000000) (ψ := 393/31250) 315 292
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t338 : ((30706979303/625000000000 : ℚ) : ℝ) ≤ stT315 338 := by
  have hc : ((451633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30706979303/625000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((451633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c339 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((883571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304601/2500000) (δ := 7899/500000000) (ψ := 393/31250) 315 292
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t339 : ((767736299/16000000000 : ℚ) : ℝ) ≤ stT315 339 := by
  have hc : ((883471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((767736299/16000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((883471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c340 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((6199/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707597/2000000) (δ := 3161/200000000) (ψ := 393/31250) 315 292
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t340 : ((335970957/40000000000 : ℚ) : ℝ) ≤ stT315 340 := by
  have hc : ((1239/8000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335970957/40000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((1239/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c341 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-695769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1170143/2000000) (δ := 3161/200000000) (ψ := 393/31250) 315 292
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t341 : ((-376834635439/10000000000000 : ℚ) : ℝ) ≤ stT315 341 := by
  have hc : ((-695869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376834635439/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-695869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c342 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-39707/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1887803/2500000) (δ := 7899/500000000) (ψ := 393/31250) 315 293
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t342 : ((-21473286429/400000000000 : ℚ) : ℝ) ≤ stT315 342 := by
  have hc : ((-39711/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21473286429/400000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-39711/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c343 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-505519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312987/2500000) (δ := 3161/200000000) (ψ := 393/31250) 315 293
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t343 : ((-5460179581/200000000000 : ℚ) : ℝ) ≤ stT315 343 := by
  have hc : ((-505619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5460179581/200000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-505619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c344 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((188727/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1479689/5000000) (δ := 3161/200000000) (ψ := 393/31250) 315 293
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t344 : ((101727657351/5000000000000 : ℚ) : ℝ) ≤ stT315 344 := by
  have hc : ((188677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101727657351/5000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((188677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c345 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((963939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673423/10000000) (δ := 3161/200000000) (ψ := 393/31250) 315 293
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t345 : ((518912604659/10000000000000 : ℚ) : ℝ) ≤ stT315 345 := by
  have hc : ((963839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518912604659/10000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((963839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c346 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((800699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 802919/5000000) (δ := 7899/500000000) (ψ := 393/31250) 315 293
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t346 : ((430404424197/10000000000000 : ℚ) : ℝ) ≤ stT315 346 := by
  have hc : ((800599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430404424197/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((800599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c347 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((1937/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3878563/10000000) (δ := 7899/500000000) (ψ := 393/31250) 315 293
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t347 : ((258616889/250000000000 : ℚ) : ℝ) ≤ stT315 347 := by
  have hc : ((1927/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258616889/250000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((1927/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c348 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-387623/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 384047/625000) (δ := 3161/200000000) (ψ := 393/31250) 315 293
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t348 : ((-207814825361/5000000000000 : ℚ) : ℝ) ≤ stT315 348 := by
  have hc : ((-387673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207814825361/5000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-387673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c349 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-487927/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182587/250000) (δ := 3953/250000000) (ψ := 393/31250) 315 294
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t349 : ((-32651029047/625000000000 : ℚ) : ℝ) ≤ stT315 349 := by
  have hc : ((-487977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32651029047/625000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-487977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c350 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-434351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1010057/2000000) (δ := 3953/250000000) (ψ := 393/31250) 315 294
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t350 : ((-232224051873/10000000000000 : ℚ) : ℝ) ≤ stT315 350 := by
  have hc : ((-434451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232224051873/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-434451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c351 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((434433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2803469/10000000) (δ := 15791/1000000000) (ψ := 393/31250) 315 294
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t351 : ((181116861/7812500000 : ℚ) : ℝ) ≤ stT315 351 := by
  have hc : ((434333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181116861/7812500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((434333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c352 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((48737/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56311/1000000) (δ := 3953/250000000) (ψ := 393/31250) 315 294
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t352 : ((6493551183/125000000000 : ℚ) : ℝ) ≤ stT315 352 := by
  have hc : ((12183/12500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6493551183/125000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((12183/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c353 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((784827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1670949/10000000) (δ := 1989/125000000) (ψ := 393/31250) 315 294
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t353 : ((208833903421/5000000000000 : ℚ) : ℝ) ≤ stT315 353 := by
  have hc : ((784727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208833903421/5000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((784727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c354 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((11313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3898707/10000000) (δ := 15891/1000000000) (ψ := 393/31250) 315 294
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t354 : ((2979821111/5000000000000 : ℚ) : ℝ) ≤ stT315 354 := by
  have hc : ((11213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2979821111/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((11213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c355 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-48061/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6120087/10000000) (δ := 15891/1000000000) (ψ := 393/31250) 315 294
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t355 : ((-20409162081/500000000000 : ℚ) : ℝ) ≤ stT315 355 := by
  have hc : ((-192269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20409162081/500000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-192269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c356 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-490761/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3686319/5000000) (δ := 15919/1000000000) (ψ := 393/31250) 315 295
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t356 : ((-260129339189/5000000000000 : ℚ) : ℝ) ≤ stT315 356 := by
  have hc : ((-490811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260129339189/5000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-490811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c357 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-237377/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5163701/10000000) (δ := 1973/125000000) (ψ := 393/31250) 315 295
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t357 : ((-125659901739/5000000000000 : ℚ) : ℝ) ≤ stT315 357 := by
  have hc : ((-237427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125659901739/5000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-237427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c358 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((47111/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1480453/5000000) (δ := 1973/125000000) (ψ := 393/31250) 315 295
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t358 : ((12446155413/625000000000 : ℚ) : ℝ) ≤ stT315 358 := by
  have hc : ((94197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12446155413/625000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((94197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c359 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((238409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -764253/10000000) (δ := 15919/1000000000) (ψ := 393/31250) 315 295
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t359 : ((7863379321/156250000000 : ℚ) : ℝ) ≤ stT315 359 := by
  have hc : ((14899/15625 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7863379321/156250000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((14899/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c360 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((841613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285267/2000000) (δ := 3971/250000000) (ψ := 393/31250) 315 295
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t360 : ((221758030299/5000000000000 : ℚ) : ℝ) ≤ stT315 360 := by
  have hc : ((841513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221758030299/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((841513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c361 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((126147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1805391/5000000) (δ := 15919/1000000000) (ψ := 393/31250) 315 295
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t361 : ((13268085361/2000000000000 : ℚ) : ℝ) ≤ stT315 361 := by
  have hc : ((126047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13268085361/2000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((126047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c362 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-677899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5789243/10000000) (δ := 15819/1000000000) (ψ := 393/31250) 315 295
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t362 : ((-356348816411/10000000000000 : ℚ) : ℝ) ≤ stT315 362 := by
  have hc : ((-677999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356348816411/10000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-677999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c363 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7746323/10000000) (δ := 493/31250000) (ψ := 393/31250) 315 296
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t363 : ((-8194217773/156250000000 : ℚ) : ℝ) ≤ stT315 363 := by
  have hc : ((-999173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8194217773/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-999173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c364 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-614039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -557991/1000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 296
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t364 : ((-321896657877/10000000000000 : ℚ) : ℝ) ≤ stT315 364 := by
  have hc : ((-614139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321896657877/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-614139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c365 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((201643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -854851/2500000) (δ := 15827/1000000000) (ψ := 393/31250) 315 296
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t365 : ((105492241689/10000000000000 : ℚ) : ℝ) ≤ stT315 365 := by
  have hc : ((201543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105492241689/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((201543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c366 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((109341/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316201/2500000) (δ := 15827/1000000000) (ψ := 393/31250) 315 296
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t366 : ((28573440789/625000000000 : ℚ) : ℝ) ≤ stT315 366 := by
  have hc : ((218657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28573440789/625000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((218657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c367 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((938147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88389/1000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 296
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t367 : ((97931168753/2000000000000 : ℚ) : ℝ) ≤ stT315 367 := by
  have hc : ((938047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97931168753/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((938047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c368 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((176181/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756689/2500000) (δ := 15827/1000000000) (ψ := 393/31250) 315 296
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t368 : ((45907312233/2500000000000 : ℚ) : ℝ) ≤ stT315 368 := by
  have hc : ((176131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45907312233/2500000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((176131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c369 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-474787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032759/2000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 296
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t369 : ((-12360833723/500000000000 : ℚ) : ℝ) ≤ stT315 369 := by
  have hc : ((-474887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12360833723/500000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-474887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c370 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-195023/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1459017/2000000) (δ := 15927/1000000000) (ψ := 393/31250) 315 296
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t370 : ((-25349543667/500000000000 : ℚ) : ℝ) ≤ stT315 370 := by
  have hc : ((-195043/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25349543667/500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-195043/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c371 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-810011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785927/1250000) (δ := 7917/500000000) (ψ := 393/31250) 315 297
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t371 : ((-16823575137/400000000000 : ℚ) : ℝ) ≤ stT315 371 := by
  have hc : ((-810111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16823575137/400000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-810111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c372 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-19221/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520953/1250000) (δ := 15869/1000000000) (ψ := 393/31250) 315 297
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t372 : ((-2493999179/500000000000 : ℚ) : ℝ) ≤ stT315 372 := by
  have hc : ((-19241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2493999179/500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-19241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c373 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((681197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2053501/10000000) (δ := 7917/500000000) (ψ := 393/31250) 315 297
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t373 : ((17632920233/500000000000 : ℚ) : ℝ) ≤ stT315 373 := by
  have hc : ((681097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17632920233/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((681097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c374 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999759/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54873/10000000) (δ := 7967/500000000) (ψ := 393/31250) 315 297
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t374 : ((516910673333/10000000000000 : ℚ) : ℝ) ≤ stT315 374 := by
  have hc : ((999659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516910673333/10000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((999659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c375 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((65009/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078867/5000000) (δ := 7917/500000000) (ψ := 393/31250) 315 297
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t375 : ((33565288603/1000000000000 : ℚ) : ℝ) ≤ stT315 375 := by
  have hc : ((64999/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33565288603/1000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((64999/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c376 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-65399/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170197/400000) (δ := 15769/1000000000) (ψ := 393/31250) 315 297
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t376 : ((-33752769239/5000000000000 : ℚ) : ℝ) ≤ stT315 376 := by
  have hc : ((-65449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33752769239/5000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-65449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c377 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-25739/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253861/400000) (δ := 15769/1000000000) (ψ := 393/31250) 315 297
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t377 : ((-106063115299/2500000000000 : ℚ) : ℝ) ≤ stT315 377 := by
  have hc : ((-205937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106063115299/2500000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-205937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c378 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-486667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7275351/10000000) (δ := 7931/500000000) (ψ := 393/31250) 315 298
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t378 : ((-50068091073/1000000000000 : ℚ) : ℝ) ≤ stT315 378 := by
  have hc : ((-486717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50068091073/1000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-486717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c379 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-485629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5194697/10000000) (δ := 7881/500000000) (ψ := 393/31250) 315 298
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t379 : ((-124751236257/5000000000000 : ℚ) : ℝ) ≤ stT315 379 := by
  have hc : ((-485729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124751236257/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-485729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c380 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((317359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1559817/5000000) (δ := 15941/1000000000) (ψ := 393/31250) 315 298
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t380 : ((162750377151/10000000000000 : ℚ) : ℝ) ≤ stT315 380 := by
  have hc : ((317259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162750377151/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((317259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c381 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((14267/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525003/5000000) (δ := 7931/500000000) (ψ := 393/31250) 315 298
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t381 : ((23386872361/500000000000 : ℚ) : ℝ) ≤ stT315 381 := by
  have hc : ((228247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23386872361/500000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((228247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c382 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((114853/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253567/2500000) (δ := 7881/500000000) (ψ := 393/31250) 315 298
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t382 : ((29378726391/625000000000 : ℚ) : ℝ) ≤ stT315 382 := by
  have hc : ((229681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29378726391/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((229681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c383 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((334981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3073029/10000000) (δ := 7931/500000000) (ψ := 393/31250) 315 298
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t383 : ((167105619/9765625000 : ℚ) : ℝ) ≤ stT315 383 := by
  have hc : ((334881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167105619/9765625000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((334881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c384 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-46161/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2563257/5000000) (δ := 7931/500000000) (ψ := 393/31250) 315 298
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t384 : ((-23561569181/1000000000000 : ℚ) : ℝ) ≤ stT315 384 := by
  have hc : ((-46171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23561569181/1000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-46171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c385 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-963307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1793661/2500000) (δ := 7931/500000000) (ψ := 393/31250) 315 298
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t385 : ((-30687403171/625000000000 : ℚ) : ℝ) ≤ stT315 385 := by
  have hc : ((-963407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30687403171/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-963407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c386 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-854933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405659/625000) (δ := 3151/200000000) (ψ := 393/31250) 315 299
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t386 : ((-435200681571/10000000000000 : ℚ) : ℝ) ≤ stT315 386 := by
  have hc : ((-855033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435200681571/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-855033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c387 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-26109/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890609/2000000) (δ := 1981/125000000) (ψ := 393/31250) 315 299
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t387 : ((-26556631947/2500000000000 : ℚ) : ℝ) ≤ stT315 387 := by
  have hc : ((-52243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26556631947/2500000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-52243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c388 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((566703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302593/1250000) (δ := 3151/200000000) (ψ := 393/31250) 315 299
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t388 : ((287649044819/10000000000000 : ℚ) : ℝ) ≤ stT315 388 := by
  have hc : ((566603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287649044819/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((566603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c389 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((123453/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393719/10000000) (δ := 3151/200000000) (ψ := 393/31250) 315 299
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t389 : ((6258680231/125000000000 : ℚ) : ℝ) ≤ stT315 389 := by
  have hc : ((246881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6258680231/125000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((246881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c390 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((795331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628109/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 299
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t390 : ((402680326239/10000000000000 : ℚ) : ℝ) ≤ stT315 390 := by
  have hc : ((795231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402680326239/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((795231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c391 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((112661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3644739/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 299
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t391 : ((56924461481/10000000000000 : ℚ) : ℝ) ≤ stT315 391 := by
  have hc : ((112561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56924461481/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((112561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c392 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-12757/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181/320) (δ := 1981/125000000) (ψ := 393/31250) 315 299
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t392 : ((-6444277443/200000000000 : ℚ) : ℝ) ≤ stT315 392 := by
  have hc : ((-12759/20000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6444277443/200000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-12759/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c393 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-997073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3831321/5000000) (δ := 3171/200000000) (ψ := 393/31250) 315 299
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t393 : ((-251503982541/5000000000000 : ℚ) : ℝ) ≤ stT315 393 := by
  have hc : ((-997173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251503982541/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-997173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c394 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-37459/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6044047/10000000) (δ := 3171/200000000) (ψ := 393/31250) 315 300
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t394 : ((-2359262619/62500000000 : ℚ) : ℝ) ≤ stT315 394 := by
  have hc : ((-4683/6250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2359262619/62500000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-4683/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c395 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-24171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011973/2500000) (δ := 3171/200000000) (ψ := 393/31250) 315 300
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t395 : ((-2437383451/1000000000000 : ℚ) : ℝ) ≤ stT315 395 := by
  have hc : ((-24221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2437383451/1000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-24221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c396 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((34013/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2056699/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 300
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t396 : ((1068102009/31250000000 : ℚ) : ℝ) ≤ stT315 396 := by
  have hc : ((4251/6250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1068102009/31250000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((4251/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c397 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2207/312500) (δ := 3987/250000000) (ψ := 393/31250) 315 300
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t397 : ((100326911877/2000000000000 : ℚ) : ℝ) ≤ stT315 397 := by
  have hc : ((999501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100326911877/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((999501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c398 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((721917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1910569/10000000) (δ := 3151/200000000) (ψ := 393/31250) 315 300
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t398 : ((180906829259/5000000000000 : ℚ) : ℝ) ≤ stT315 398 := by
  have hc : ((721817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180906829259/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((721817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c399 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((16107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3886721/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 300
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t399 : ((4006760191/5000000000000 : ℚ) : ℝ) ≤ stT315 399 := by
  have hc : ((16007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4006760191/5000000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((16007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c400 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-348917/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5857913/10000000) (δ := 3171/200000000) (ψ := 393/31250) 315 300
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t400 : ((-174483848967/5000000000000 : ℚ) : ℝ) ≤ stT315 400 := by
  have hc : ((-348967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174483848967/5000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-348967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c401 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7824221/10000000) (δ := 3987/250000000) (ψ := 393/31250) 315 300
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t401 : ((-499391481933/10000000000000 : ℚ) : ℝ) ≤ stT315 401 := by
  have hc : ((-1000029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499391481933/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-1000029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c402 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-358037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2961197/5000000) (δ := 15863/1000000000) (ψ := 393/31250) 315 301
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t402 : ((-35719536337/1000000000000 : ℚ) : ℝ) ≤ stT315 402 := by
  have hc : ((-358087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35719536337/1000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-358087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c403 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-15543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3965851/10000000) (δ := 797/50000000) (ψ := 393/31250) 315 301
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t403 : ((-974042681/1250000000000 : ℚ) : ℝ) ≤ stT315 403 := by
  have hc : ((-15643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-974042681/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-15643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c404 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((43289/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2014189/10000000) (δ := 15863/1000000000) (ψ := 393/31250) 315 301
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t404 : ((43067894429/1250000000000 : ℚ) : ℝ) ≤ stT315 404 := by
  have hc : ((173131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43067894429/1250000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((173131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c405 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16833/2500000) (δ := 99/6250000) (ψ := 393/31250) 315 301
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t405 : ((496672933911/10000000000000 : ℚ) : ℝ) ≤ stT315 405 := by
  have hc : ((999537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496672933911/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((999537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c406 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((146353/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 937361/5000000) (δ := 15763/1000000000) (ψ := 393/31250) 315 301
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t406 : ((72623750903/2000000000000 : ℚ) : ℝ) ≤ stT315 406 := by
  have hc : ((146333/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72623750903/2000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((146333/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c407 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((45991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952993/2500000) (δ := 15763/1000000000) (ψ := 393/31250) 315 301
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t407 : ((22747296771/10000000000000 : ℚ) : ℝ) ≤ stT315 407 := by
  have hc : ((45891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22747296771/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((45891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c408 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-664633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5744497/10000000) (δ := 15763/1000000000) (ψ := 393/31250) 315 301
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t408 : ((-164546012621/5000000000000 : ℚ) : ℝ) ≤ stT315 408 := by
  have hc : ((-664733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164546012621/5000000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-664733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c409 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-12467/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7672297/10000000) (δ := 15763/1000000000) (ψ := 393/31250) 315 301
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t409 : ((-24660652437/500000000000 : ℚ) : ℝ) ≤ stT315 409 := by
  have hc : ((-49873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24660652437/500000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-49873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c410 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-47941/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6112591/10000000) (δ := 1587/100000000) (ψ := 393/31250) 315 302
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t410 : ((-18943574897/500000000000 : ℚ) : ℝ) ≤ stT315 410 := by
  have hc : ((-191789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18943574897/500000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-191789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c411 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-53333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4194163/10000000) (δ := 15933/1000000000) (ψ := 393/31250) 315 302
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t411 : ((-1645744507/312500000000 : ℚ) : ℝ) ≤ stT315 411 := by
  have hc : ((-53383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1645744507/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-53383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c412 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((30601/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2280459/10000000) (δ := 15833/1000000000) (ψ := 393/31250) 315 302
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t412 : ((471048367/15625000000 : ℚ) : ℝ) ≤ stT315 412 := by
  have hc : ((7649/12500 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471048367/15625000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((7649/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c413 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((197797/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371401/10000000) (δ := 1587/100000000) (ψ := 393/31250) 315 302
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t413 : ((97319535059/2000000000000 : ℚ) : ℝ) ≤ stT315 413 := by
  have hc : ((197777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97319535059/2000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((197777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c414 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((81779/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1533089/10000000) (δ := 1587/100000000) (ψ := 393/31250) 315 302
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t414 : ((40187255737/1000000000000 : ℚ) : ℝ) ≤ stT315 414 := by
  have hc : ((81769/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40187255737/1000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((81769/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c415 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((196309/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3433011/10000000) (δ := 15833/1000000000) (ψ := 393/31250) 315 302
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t415 : ((150492303/15625000000 : ℚ) : ℝ) ≤ stT315 415 := by
  have hc : ((196209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150492303/15625000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((196209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c416 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-4253/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5328287/10000000) (δ := 15933/1000000000) (ψ := 393/31250) 315 302
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t416 : ((-10427999279/400000000000 : ℚ) : ℝ) ≤ stT315 416 := by
  have hc : ((-21269/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10427999279/400000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-21269/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c417 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-241981/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288763/400000) (δ := 1577/100000000) (ψ := 393/31250) 315 302
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t417 : ((-59255532109/1250000000000 : ℚ) : ℝ) ≤ stT315 417 := by
  have hc : ((-121003/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59255532109/1250000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-121003/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c418 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-877331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650667/2500000) (δ := 15877/1000000000) (ψ := 393/31250) 315 303
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t418 : ((-107291385249/2500000000000 : ℚ) : ℝ) ≤ stT315 418 := by
  have hc : ((-877431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107291385249/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-877431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c419 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-312267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4720937/10000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 303
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t419 : ((-38150318811/2500000000000 : ℚ) : ℝ) ≤ stT315 419 := by
  have hc : ((-312367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38150318811/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-312367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c420 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((83977/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -568739/2000000) (δ := 7963/500000000) (ψ := 393/31250) 315 303
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t420 : ((819336363/40000000000 : ℚ) : ℝ) ≤ stT315 420 := by
  have hc : ((83957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819336363/40000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((83957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c421 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((37021/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -970941/10000000) (δ := 7913/500000000) (ψ := 393/31250) 315 303
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t421 : ((1804097529/40000000000 : ℚ) : ℝ) ≤ stT315 421 := by
  have hc : ((37017/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1804097529/40000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((37017/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c422 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((468131/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897403/10000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 303
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t422 : ((28482260769/625000000000 : ℚ) : ℝ) ≤ stT315 422 := by
  have hc : ((468081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28482260769/625000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((468081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c423 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((224789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1380629/5000000) (δ := 15777/1000000000) (ψ := 393/31250) 315 303
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t423 : ((13658962203/625000000000 : ℚ) : ℝ) ≤ stT315 423 := by
  have hc : ((224739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13658962203/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((224739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c424 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-17123/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2310391/5000000) (δ := 15877/1000000000) (ψ := 393/31250) 315 303
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t424 : ((-33274801431/2500000000000 : ℚ) : ℝ) ≤ stT315 424 := by
  have hc : ((-68517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33274801431/2500000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-68517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c425 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-851879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1295179/2000000) (δ := 7963/500000000) (ψ := 393/31250) 315 303
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t425 : ((-25829447343/625000000000 : ℚ) : ℝ) ≤ stT315 425 := by
  have hc : ((-851979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25829447343/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-851979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c426 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-491089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476257/2000000) (δ := 3971/250000000) (ψ := 393/31250) 315 304
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t426 : ((-118978913889/2500000000000 : ℚ) : ℝ) ≤ stT315 426 := by
  have hc : ((-491139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118978913889/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-491139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c427 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-599709/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2767417/5000000) (δ := 1973/125000000) (ψ := 393/31250) 315 304
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t427 : ((-145133984303/5000000000000 : ℚ) : ℝ) ≤ stT315 427 := by
  have hc : ((-599809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145133984303/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-599809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c428 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((46771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3692793/10000000) (δ := 15819/1000000000) (ψ := 393/31250) 315 304
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t428 : ((2822929541/625000000000 : ℚ) : ℝ) ≤ stT315 428 := by
  have hc : ((46721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2822929541/625000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((46721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c429 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((737139/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74197/400000) (δ := 3971/250000000) (ψ := 393/31250) 315 304
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t429 : ((88961344339/2500000000000 : ℚ) : ℝ) ≤ stT315 429 := by
  have hc : ((737039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88961344339/2500000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((737039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c430 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((999963/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21389/10000000) (δ := 1973/125000000) (ψ := 393/31250) 315 304
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t430 : ((241087966423/5000000000000 : ℚ) : ℝ) ≤ stT315 430 := by
  have hc : ((999863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241087966423/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((999863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c431 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((749741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 225977/1250000) (δ := 1973/125000000) (ψ := 393/31250) 315 304
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t431 : ((361089325803/10000000000000 : ℚ) : ℝ) ≤ stT315 431 := by
  have hc : ((749641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361089325803/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((749641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c432 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((58693/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3632847/10000000) (δ := 15819/1000000000) (ψ := 393/31250) 315 304
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t432 : ((225716907/40000000000 : ℚ) : ℝ) ≤ stT315 432 := by
  have hc : ((58643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225716907/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((58643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c433 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-573429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1090741/2000000) (δ := 3971/250000000) (ψ := 393/31250) 315 304
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t433 : ((-27562083153/1000000000000 : ℚ) : ℝ) ≤ stT315 433 := by
  have hc : ((-573529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27562083153/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-573529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c434 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-97287/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727031/1000000) (δ := 3971/250000000) (ψ := 393/31250) 315 304
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t434 : ((-2919007297/62500000000 : ℚ) : ℝ) ≤ stT315 434 := by
  have hc : ((-97297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2919007297/62500000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-97297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c435 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-110203/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3312611/5000000) (δ := 15891/1000000000) (ψ := 393/31250) 315 305
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t435 : ((-13211091123/312500000000 : ℚ) : ℝ) ≤ stT315 435 := by
  have hc : ((-220431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13211091123/312500000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-220431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c436 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-174259/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -963393/2000000) (δ := 3953/250000000) (ψ := 393/31250) 315 305
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t436 : ((-41739510213/2500000000000 : ℚ) : ℝ) ≤ stT315 436 := by
  have hc : ((-174309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41739510213/2500000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-174309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c437 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((357551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3012881/10000000) (δ := 15791/1000000000) (ψ := 393/31250) 315 305
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t437 : ((42747922541/2500000000000 : ℚ) : ℝ) ≤ stT315 437 := by
  have hc : ((357451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42747922541/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((357451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c438 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((110577/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -606407/5000000) (δ := 1989/125000000) (ψ := 393/31250) 315 305
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t438 : ((52829708261/1250000000000 : ℚ) : ℝ) ≤ stT315 438 := by
  have hc : ((221129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52829708261/1250000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((221129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c439 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((243231/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14577/250000) (δ := 3953/250000000) (ψ := 393/31250) 315 305
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t439 : ((58037828619/1250000000000 : ℚ) : ℝ) ≤ stT315 439 := by
  have hc : ((121603/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58037828619/1250000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((121603/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c440 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((290861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2374879/10000000) (δ := 15791/1000000000) (ψ := 393/31250) 315 305
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t440 : ((138638618841/5000000000000 : ℚ) : ℝ) ≤ stT315 440 := by
  have hc : ((290811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138638618841/5000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((290811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c441 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-94097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4162583/10000000) (δ := 15891/1000000000) (ψ := 393/31250) 315 305
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t441 : ((-44855763627/10000000000000 : ℚ) : ℝ) ≤ stT315 441 := by
  have hc : ((-94197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44855763627/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-94197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c442 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-722707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594627/1000000) (δ := 3953/250000000) (ψ := 393/31250) 315 305
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t442 : ((-85951148791/2500000000000 : ℚ) : ℝ) ≤ stT315 442 := by
  have hc : ((-722807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85951148791/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-722807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c443 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-998689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7725941/10000000) (δ := 1989/125000000) (ψ := 393/31250) 315 305
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t443 : ((-94907927147/2000000000000 : ℚ) : ℝ) ≤ stT315 443 := by
  have hc : ((-998789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94907927147/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-998789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c444 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-790577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6206367/10000000) (δ := 3161/200000000) (ψ := 393/31250) 315 306
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t444 : ((-375238699983/10000000000000 : ℚ) : ℝ) ≤ stT315 444 := by
  have hc : ((-790677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375238699983/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-790677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c445 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-100851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554341/1250000) (δ := 7899/500000000) (ψ := 393/31250) 315 306
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t445 : ((-23915857723/2500000000000 : ℚ) : ℝ) ≤ stT315 445 := by
  have hc : ((-100901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23915857723/2500000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-100901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c446 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((482919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2667027/10000000) (δ := 3161/200000000) (ψ := 393/31250) 315 306
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t446 : ((228621073147/10000000000000 : ℚ) : ℝ) ≤ stT315 446 := by
  have hc : ((482819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228621073147/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((482819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c447 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((37417/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451671/5000000) (δ := 3161/200000000) (ψ := 393/31250) 315 306
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t447 : ((17695712979/400000000000 : ℚ) : ℝ) ≤ stT315 447 := by
  have hc : ((37413/40000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17695712979/400000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((37413/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c448 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((941887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214121/2500000) (δ := 3181/200000000) (ψ := 393/31250) 315 306
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t448 : ((88990395417/2000000000000 : ℚ) : ℝ) ≤ stT315 448 := by
  have hc : ((941787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88990395417/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((941787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c449 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((501973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1306147/5000000) (δ := 3181/200000000) (ψ := 393/31250) 315 306
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t449 : ((236848423017/10000000000000 : ℚ) : ℝ) ≤ stT315 449 := by
  have hc : ((501873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236848423017/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((501873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c450 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-43503/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2182123/5000000) (δ := 7949/500000000) (ψ := 393/31250) 315 306
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t450 : ((-512982921/62500000000 : ℚ) : ℝ) ≤ stT315 450 := by
  have hc : ((-5441/31250 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512982921/62500000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-5441/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c451 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-766991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3056169/5000000) (δ := 3161/200000000) (ψ := 393/31250) 315 306
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t451 : ((-180604672131/5000000000000 : ℚ) : ℝ) ≤ stT315 451 := by
  have hc : ((-767091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180604672131/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-767091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c452 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785147/1000000) (δ := 7903/500000000) (ψ := 393/31250) 315 307
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t452 : ((-470407565739/10000000000000 : ℚ) : ℝ) ≤ stT315 452 := by
  have hc : ((-1000099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470407565739/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-1000099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c453 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-47917/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1222219/2000000) (δ := 7903/500000000) (ψ := 393/31250) 315 307
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t453 : ((-90065230813/2500000000000 : ℚ) : ℝ) ≤ stT315 453 := by
  have hc : ((-191693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90065230813/2500000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-191693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c454 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-178111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2187329/5000000) (δ := 15897/1000000000) (ψ := 393/31250) 315 307
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t454 : ((-20909674841/2500000000000 : ℚ) : ℝ) ≤ stT315 454 := by
  have hc : ((-178211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20909674841/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-178211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c455 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((491689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2641921/10000000) (δ := 7953/500000000) (ψ := 393/31250) 315 307
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t455 : ((230460364323/10000000000000 : ℚ) : ℝ) ≤ stT315 455 := by
  have hc : ((491589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230460364323/10000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((491589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c456 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((467023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228261/2500000) (δ := 15797/1000000000) (ψ := 393/31250) 315 307
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t456 : ((54669930029/1250000000000 : ℚ) : ℝ) ≤ stT315 456 := by
  have hc : ((466973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54669930029/1250000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((466973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c457 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((473859/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32479/400000) (δ := 7903/500000000) (ψ := 393/31250) 315 307
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t457 : ((11081918701/250000000000 : ℚ) : ℝ) ≤ stT315 457 := by
  have hc : ((473809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11081918701/250000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((473809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c458 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((529049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 633323/2500000) (δ := 15897/1000000000) (ψ := 393/31250) 315 307
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t458 : ((247161470281/10000000000000 : ℚ) : ℝ) ≤ stT315 458 := by
  have hc : ((528949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247161470281/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((528949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c459 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-25841/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4250909/10000000) (δ := 7953/500000000) (ψ := 393/31250) 315 307
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t459 : ((-12070906221/2000000000000 : ℚ) : ℝ) ≤ stT315 459 := by
  have hc : ((-25861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12070906221/2000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-25861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c460 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-363887/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2982333/5000000) (δ := 15797/1000000000) (ψ := 393/31250) 315 307
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t460 : ((-169686718061/5000000000000 : ℚ) : ℝ) ≤ stT315 460 := by
  have hc : ((-363937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169686718061/5000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-363937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c461 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-997433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7674801/10000000) (δ := 15797/1000000000) (ψ := 393/31250) 315 307
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t461 : ((-464598002151/10000000000000 : ℚ) : ℝ) ≤ stT315 461 := by
  have hc : ((-997533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464598002151/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-997533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c462 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-819149/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6326807/10000000) (δ := 15813/1000000000) (ψ := 393/31250) 315 308
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t462 : ((-381149862507/10000000000000 : ℚ) : ℝ) ≤ stT315 462 := by
  have hc : ((-819249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381149862507/10000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-819249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c463 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-55047/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184963/400000) (δ := 1589/100000000) (ψ := 393/31250) 315 308
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t463 : ((-1279591879/100000000000 : ℚ) : ℝ) ≤ stT315 463 := by
  have hc : ((-55067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1279591879/100000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-55067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c464 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((48767/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2925043/10000000) (δ := 15913/1000000000) (ψ := 393/31250) 315 308
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t464 : ((22633691571/1250000000000 : ℚ) : ℝ) ≤ stT315 464 := by
  have hc : ((97509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22633691571/1250000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((97509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c465 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((881459/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245927/2000000) (δ := 1589/100000000) (ψ := 393/31250) 315 308
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t465 : ((204359829971/5000000000000 : ℚ) : ℝ) ≤ stT315 465 := by
  have hc : ((881359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204359829971/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((881359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c466 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((122871/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462073/10000000) (δ := 15813/1000000000) (ψ := 393/31250) 315 308
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t466 : ((113826188797/2500000000000 : ℚ) : ℝ) ≤ stT315 466 := by
  have hc : ((245717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113826188797/2500000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((245717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c467 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((65239/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1075079/5000000) (δ := 15813/1000000000) (ψ := 393/31250) 315 308
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t467 : ((3773041047/125000000000 : ℚ) : ℝ) ≤ stT315 467 := by
  have hc : ((65229/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3773041047/125000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((65229/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c468 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((1847/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191731/500000) (δ := 1589/100000000) (ψ := 393/31250) 315 308
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t468 : ((1702929/1000000000 : ℚ) : ℝ) ≤ stT315 468 := by
  have hc : ((921/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1702929/1000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((921/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c469 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-118703/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5515539/10000000) (δ := 1579/100000000) (ψ := 393/31250) 315 308
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t469 : ((-27410647517/1000000000000 : ℚ) : ℝ) ≤ stT315 469 := by
  have hc : ((-118723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27410647517/1000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-118723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c470 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-482617/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438567/2000000) (δ := 1589/100000000) (ψ := 393/31250) 315 308
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t470 : ((-111318938211/2500000000000 : ℚ) : ℝ) ≤ stT315 470 := by
  have hc : ((-482667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111318938211/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-482667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c471 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-459543/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54731/80000) (δ := 199/12500000) (ψ := 393/31250) 315 309
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t471 : ((-26471178021/625000000000 : ℚ) : ℝ) ≤ stT315 471 := by
  have hc : ((-459593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26471178021/625000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-459593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c472 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-23869/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5171167/10000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 309
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t472 : ((-10731363/488281250 : ℚ) : ℝ) ≤ stT315 472 := by
  have hc : ((-11937/25000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10731363/488281250 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-11937/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c473 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((2628/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1752251/5000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 309
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t473 : ((96610877/12500000000 : ℚ) : ℝ) ≤ stT315 473 := by
  have hc : ((42023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96610877/12500000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((42023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c474 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((74081/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -920651/5000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 309
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t474 : ((6804384273/200000000000 : ℚ) : ℝ) ≤ stT315 474 := by
  have hc : ((74071/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6804384273/200000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((74071/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c475 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((498681/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36329/2000000) (δ := 199/12500000) (ψ := 393/31250) 315 309
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t475 : ((228787360361/5000000000000 : ℚ) : ℝ) ≤ stT315 475 := by
  have hc : ((498631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228787360361/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((498631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c476 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((831059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1474467/10000000) (δ := 15783/1000000000) (ψ := 393/31250) 315 309
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t476 : ((380869226691/10000000000000 : ℚ) : ℝ) ≤ stT315 476 := by
  have hc : ((830959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380869226691/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((830959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c477 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((314519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 625423/2000000) (δ := 199/12500000) (ψ := 393/31250) 315 309
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t477 : ((35990599673/2500000000000 : ℚ) : ℝ) ≤ stT315 477 := by
  have hc : ((314419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35990599673/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((314419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c478 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-66651/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 597047/1250000) (δ := 791/50000000) (ψ := 393/31250) 315 309
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t478 : ((-3049464869/200000000000 : ℚ) : ℝ) ≤ stT315 478 := by
  have hc : ((-66671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3049464869/200000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-66671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c479 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-840411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6422093/10000000) (δ := 15883/1000000000) (ψ := 393/31250) 315 309
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t479 : ((-24002472627/625000000000 : ℚ) : ℝ) ≤ stT315 479 := by
  have hc : ((-840511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24002472627/625000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-840511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c480 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-996457/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382173/500000) (δ := 493/31250000) (ψ := 393/31250) 315 310
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t480 : ((-113716122713/2500000000000 : ℚ) : ℝ) ≤ stT315 480 := by
  have hc : ((-996557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113716122713/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-996557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c481 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-369317/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3002297/5000000) (δ := 3969/250000000) (ψ := 393/31250) 315 310
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t481 : ((-168416946687/5000000000000 : ℚ) : ℝ) ≤ stT315 481 := by
  have hc : ((-369367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168416946687/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-369367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c482 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-87949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873807/2000000) (δ := 493/31250000) (ψ := 393/31250) 315 310
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t482 : ((-626288883/78125000000 : ℚ) : ℝ) ≤ stT315 482 := by
  have hc : ((-87999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626288883/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-87999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c483 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((91649/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2736941/10000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 310
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t483 : ((8338513887/400000000000 : ℚ) : ℝ) ≤ stT315 483 := by
  have hc : ((91629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8338513887/400000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((91629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c484 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((903357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221631/2000000) (δ := 493/31250000) (ψ := 393/31250) 315 310
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t484 : ((82114190613/2000000000000 : ℚ) : ℝ) ≤ stT315 484 := by
  have hc : ((903257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82114190613/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((903257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c485 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((978679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258583/5000000) (δ := 3969/250000000) (ψ := 393/31250) 315 310
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t485 : ((111087309501/2500000000000 : ℚ) : ℝ) ≤ stT315 485 := by
  have hc : ((978579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111087309501/2500000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((978579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c486 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((655687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2139259/10000000) (δ := 15827/1000000000) (ψ := 393/31250) 315 310
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t486 : ((297380163483/10000000000000 : ℚ) : ℝ) ≤ stT315 486 := by
  have hc : ((655587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297380163483/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((655587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c487 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((67559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 751593/2000000) (δ := 493/31250000) (ψ := 393/31250) 315 310
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t487 : ((30568573637/10000000000000 : ℚ) : ℝ) ≤ stT315 487 := by
  have hc : ((67459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30568573637/10000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((67459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c488 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-54681/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1343341/2500000) (δ := 15827/1000000000) (ψ := 393/31250) 315 310
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t488 : ((-24757467189/1000000000000 : ℚ) : ℝ) ≤ stT315 488 := by
  have hc : ((-54691/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24757467189/1000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-54691/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c489 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-940247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218293/312500) (δ := 3969/250000000) (ψ := 393/31250) 315 310
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t489 : ((-53154994869/1250000000000 : ℚ) : ℝ) ≤ stT315 489 := by
  have hc : ((-940347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53154994869/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-940347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c490 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-95649/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7113803/10000000) (δ := 7917/500000000) (ψ := 393/31250) 315 311
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t490 : ((-21607167943/500000000000 : ℚ) : ℝ) ≤ stT315 490 := by
  have hc : ((-95659/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21607167943/500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-95659/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c491 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-118233/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -688531/1250000) (δ := 7917/500000000) (ψ := 393/31250) 315 311
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t491 : ((-26683434691/1000000000000 : ℚ) : ℝ) ≤ stT315 491 := by
  have hc : ((-118253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26683434691/1000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-118253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c492 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((2099/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3906001/10000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 311
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t492 : ((233757429/625000000000 : ℚ) : ℝ) ≤ stT315 492 := by
  have hc : ((1037/125000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233757429/625000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((1037/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c493 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((603571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2307061/10000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 311
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t493 : ((271789458567/10000000000000 : ℚ) : ℝ) ≤ stT315 493 := by
  have hc : ((603471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271789458567/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((603471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c494 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((4799/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711271/10000000) (δ := 15869/1000000000) (ψ := 393/31250) 315 311
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t494 : ((4317891837/100000000000 : ℚ) : ℝ) ≤ stT315 494 := by
  have hc : ((9597/10000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4317891837/100000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((9597/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c495 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((469259/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220303/2500000) (δ := 7917/500000000) (ψ := 393/31250) 315 311
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t495 : ((105446746197/2500000000000 : ℚ) : ℝ) ≤ stT315 495 := by
  have hc : ((469209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105446746197/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((469209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c496 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((550179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154409/625000) (δ := 15869/1000000000) (ψ := 393/31250) 315 311
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t496 : ((246992622027/10000000000000 : ℚ) : ℝ) ≤ stT315 496 := by
  have hc : ((550079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246992622027/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((550079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c497 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-162/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 507081/1250000) (δ := 15769/1000000000) (ψ := 393/31250) 315 311
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t497 : ((-582457757/250000000000 : ℚ) : ℝ) ≤ stT315 497 := by
  have hc : ((-2597/50000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-582457757/250000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-2597/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c498 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-632683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5639523/10000000) (δ := 15769/1000000000) (ψ := 393/31250) 315 311
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t498 : ((-283557022913/10000000000000 : ℚ) : ℝ) ≤ stT315 498 := by
  have hc : ((-632783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283557022913/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-632783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c499 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-483971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451203/625000) (δ := 15769/1000000000) (ψ := 393/31250) 315 311
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t499 : ((-108338904451/2500000000000 : ℚ) : ℝ) ≤ stT315 499 := by
  have hc : ((-484021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108338904451/2500000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-484021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_c500 :
    |Real.cos (((315 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-92987/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345607/500000) (δ := 7921/500000000) (ψ := 393/31250) 315 312
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st315_t500 : ((-20794780179/500000000000 : ℚ) : ℝ) ≤ stT315 500 := by
  have hc : ((-92997/100000 : ℚ) : ℝ)
      ≤ Real.cos (((315 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((393/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st315_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20794780179/500000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-92997/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st315_p1 : ((999821/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT315 (i+1) := by
  rw [Finset.sum_range_one]
  exact st315_t1

theorem st315_p2 : ((2478316315029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT315 (i+1))
      = (∑ i ∈ Finset.range 1, stT315 (i+1)) + stT315 2 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 1
    simpa using h
  have hprev := st315_p1
  have hstep := st315_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p3 : ((7523390168459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT315 (i+1))
      = (∑ i ∈ Finset.range 2, stT315 (i+1)) + stT315 3 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 2
    simpa using h
  have hprev := st315_p2
  have hstep := st315_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p4 : ((10046594336881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT315 (i+1))
      = (∑ i ∈ Finset.range 3, stT315 (i+1)) + stT315 4 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 3
    simpa using h
  have hprev := st315_p3
  have hstep := st315_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p5 : ((8276500547401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT315 (i+1))
      = (∑ i ∈ Finset.range 4, stT315 (i+1)) + stT315 5 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 4
    simpa using h
  have hprev := st315_p4
  have hstep := st315_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p6 : ((10145962952287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT315 (i+1))
      = (∑ i ∈ Finset.range 5, stT315 (i+1)) + stT315 6 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 5
    simpa using h
  have hprev := st315_p5
  have hstep := st315_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p7 : ((6580487756567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT315 (i+1))
      = (∑ i ∈ Finset.range 6, stT315 (i+1)) + stT315 7 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 6
    simpa using h
  have hprev := st315_p6
  have hstep := st315_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p8 : ((1323491057923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT315 (i+1))
      = (∑ i ∈ Finset.range 7, stT315 (i+1)) + stT315 8 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 7
    simpa using h
  have hprev := st315_p7
  have hstep := st315_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p9 : ((8521275099233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT315 (i+1))
      = (∑ i ∈ Finset.range 8, stT315 (i+1)) + stT315 9 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 8
    simpa using h
  have hprev := st315_p8
  have hstep := st315_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p10 : ((5615982783181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT315 (i+1))
      = (∑ i ∈ Finset.range 9, stT315 (i+1)) + stT315 10 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 9
    simpa using h
  have hprev := st315_p9
  have hstep := st315_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p11 : ((6298966179941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT315 (i+1))
      = (∑ i ∈ Finset.range 10, stT315 (i+1)) + stT315 11 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 10
    simpa using h
  have hprev := st315_p10
  have hstep := st315_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p12 : ((3733423074981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT315 (i+1))
      = (∑ i ∈ Finset.range 11, stT315 (i+1)) + stT315 12 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 11
    simpa using h
  have hprev := st315_p11
  have hstep := st315_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p13 : ((1379103469119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT315 (i+1))
      = (∑ i ∈ Finset.range 12, stT315 (i+1)) + stT315 13 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 12
    simpa using h
  have hprev := st315_p12
  have hstep := st315_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p14 : ((4894894881/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT315 (i+1))
      = (∑ i ∈ Finset.range 13, stT315 (i+1)) + stT315 14 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 13
    simpa using h
  have hprev := st315_p13
  have hstep := st315_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p15 : ((43609378637/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT315 (i+1))
      = (∑ i ∈ Finset.range 14, stT315 (i+1)) + stT315 15 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 14
    simpa using h
  have hprev := st315_p14
  have hstep := st315_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p16 : ((199836097387/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT315 (i+1))
      = (∑ i ∈ Finset.range 15, stT315 (i+1)) + stT315 16 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 15
    simpa using h
  have hprev := st315_p15
  have hstep := st315_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p17 : ((277725778499/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT315 (i+1))
      = (∑ i ∈ Finset.range 16, stT315 (i+1)) + stT315 17 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 16
    simpa using h
  have hprev := st315_p16
  have hstep := st315_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p18 : ((936223274429/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT315 (i+1))
      = (∑ i ∈ Finset.range 17, stT315 (i+1)) + stT315 18 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 17
    simpa using h
  have hprev := st315_p17
  have hstep := st315_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p19 : ((115170960761/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT315 (i+1))
      = (∑ i ∈ Finset.range 18, stT315 (i+1)) + stT315 19 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 18
    simpa using h
  have hprev := st315_p18
  have hstep := st315_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p20 : ((6640423793979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT315 (i+1))
      = (∑ i ∈ Finset.range 19, stT315 (i+1)) + stT315 20 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 19
    simpa using h
  have hprev := st315_p19
  have hstep := st315_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p21 : ((5161456341087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT315 (i+1))
      = (∑ i ∈ Finset.range 20, stT315 (i+1)) + stT315 21 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 20
    simpa using h
  have hprev := st315_p20
  have hstep := st315_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p22 : ((3619055021673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT315 (i+1))
      = (∑ i ∈ Finset.range 21, stT315 (i+1)) + stT315 22 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 21
    simpa using h
  have hprev := st315_p21
  have hstep := st315_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p23 : ((3988930375257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT315 (i+1))
      = (∑ i ∈ Finset.range 22, stT315 (i+1)) + stT315 23 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 22
    simpa using h
  have hprev := st315_p22
  have hstep := st315_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p24 : ((3520130572569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT315 (i+1))
      = (∑ i ∈ Finset.range 23, stT315 (i+1)) + stT315 24 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 23
    simpa using h
  have hprev := st315_p23
  have hstep := st315_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p25 : ((706030056141/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT315 (i+1))
      = (∑ i ∈ Finset.range 24, stT315 (i+1)) + stT315 25 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 24
    simpa using h
  have hprev := st315_p24
  have hstep := st315_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p26 : ((2304950633533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT315 (i+1))
      = (∑ i ∈ Finset.range 25, stT315 (i+1)) + stT315 26 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 25
    simpa using h
  have hprev := st315_p25
  have hstep := st315_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p27 : ((2420372521033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT315 (i+1))
      = (∑ i ∈ Finset.range 26, stT315 (i+1)) + stT315 27 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 26
    simpa using h
  have hprev := st315_p26
  have hstep := st315_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p28 : ((3311125002157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT315 (i+1))
      = (∑ i ∈ Finset.range 27, stT315 (i+1)) + stT315 28 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 27
    simpa using h
  have hprev := st315_p27
  have hstep := st315_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p29 : ((3670969068403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT315 (i+1))
      = (∑ i ∈ Finset.range 28, stT315 (i+1)) + stT315 29 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 28
    simpa using h
  have hprev := st315_p28
  have hstep := st315_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p30 : ((345129575019/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT315 (i+1))
      = (∑ i ∈ Finset.range 29, stT315 (i+1)) + stT315 30 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 29
    simpa using h
  have hprev := st315_p29
  have hstep := st315_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p31 : ((1302812761021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT315 (i+1))
      = (∑ i ∈ Finset.range 30, stT315 (i+1)) + stT315 31 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 30
    simpa using h
  have hprev := st315_p30
  have hstep := st315_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p32 : ((1624406334943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT315 (i+1))
      = (∑ i ∈ Finset.range 31, stT315 (i+1)) + stT315 32 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 31
    simpa using h
  have hprev := st315_p31
  have hstep := st315_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p33 : ((6051483343219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT315 (i+1))
      = (∑ i ∈ Finset.range 32, stT315 (i+1)) + stT315 33 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 32
    simpa using h
  have hprev := st315_p32
  have hstep := st315_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p34 : ((6455626418409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT315 (i+1))
      = (∑ i ∈ Finset.range 33, stT315 (i+1)) + stT315 34 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 33
    simpa using h
  have hprev := st315_p33
  have hstep := st315_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p35 : ((1309918804149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT315 (i+1))
      = (∑ i ∈ Finset.range 34, stT315 (i+1)) + stT315 35 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 34
    simpa using h
  have hprev := st315_p34
  have hstep := st315_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p36 : ((1399802207667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT315 (i+1))
      = (∑ i ∈ Finset.range 35, stT315 (i+1)) + stT315 36 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 35
    simpa using h
  have hprev := st315_p35
  have hstep := st315_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p37 : ((721932382241/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT315 (i+1))
      = (∑ i ∈ Finset.range 36, stT315 (i+1)) + stT315 37 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 36
    simpa using h
  have hprev := st315_p36
  have hstep := st315_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p38 : ((246148994217/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT315 (i+1))
      = (∑ i ∈ Finset.range 37, stT315 (i+1)) + stT315 38 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 37
    simpa using h
  have hprev := st315_p37
  have hstep := st315_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p39 : ((1069931422389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT315 (i+1))
      = (∑ i ∈ Finset.range 38, stT315 (i+1)) + stT315 39 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 38
    simpa using h
  have hprev := st315_p38
  have hstep := st315_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p40 : ((6802832032467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT315 (i+1))
      = (∑ i ∈ Finset.range 39, stT315 (i+1)) + stT315 40 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 39
    simpa using h
  have hprev := st315_p39
  have hstep := st315_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p41 : ((7524744960717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT315 (i+1))
      = (∑ i ∈ Finset.range 40, stT315 (i+1)) + stT315 41 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 40
    simpa using h
  have hprev := st315_p40
  have hstep := st315_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p42 : ((6389155260553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT315 (i+1))
      = (∑ i ∈ Finset.range 41, stT315 (i+1)) + stT315 42 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 41
    simpa using h
  have hprev := st315_p41
  have hstep := st315_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p43 : ((995134332383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT315 (i+1))
      = (∑ i ∈ Finset.range 42, stT315 (i+1)) + stT315 43 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 42
    simpa using h
  have hprev := st315_p42
  have hstep := st315_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p44 : ((4635871329229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT315 (i+1))
      = (∑ i ∈ Finset.range 43, stT315 (i+1)) + stT315 44 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 43
    simpa using h
  have hprev := st315_p43
  have hstep := st315_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p45 : ((2719135933533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT315 (i+1))
      = (∑ i ∈ Finset.range 44, stT315 (i+1)) + stT315 45 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 44
    simpa using h
  have hprev := st315_p44
  have hstep := st315_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p46 : ((3408459253251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT315 (i+1))
      = (∑ i ∈ Finset.range 45, stT315 (i+1)) + stT315 46 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 45
    simpa using h
  have hprev := st315_p45
  have hstep := st315_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p47 : ((8263269636783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT315 (i+1))
      = (∑ i ∈ Finset.range 46, stT315 (i+1)) + stT315 47 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 46
    simpa using h
  have hprev := st315_p46
  have hstep := st315_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p48 : ((9544850959533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT315 (i+1))
      = (∑ i ∈ Finset.range 47, stT315 (i+1)) + stT315 48 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 47
    simpa using h
  have hprev := st315_p47
  have hstep := st315_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p49 : ((532339460019/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT315 (i+1))
      = (∑ i ∈ Finset.range 48, stT315 (i+1)) + stT315 49 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 48
    simpa using h
  have hprev := st315_p48
  have hstep := st315_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p50 : ((11661567638021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT315 (i+1))
      = (∑ i ∈ Finset.range 49, stT315 (i+1)) + stT315 50 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 49
    simpa using h
  have hprev := st315_p49
  have hstep := st315_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p51 : ((12709537190021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT315 (i+1))
      = (∑ i ∈ Finset.range 50, stT315 (i+1)) + stT315 51 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 50
    simpa using h
  have hprev := st315_p50
  have hstep := st315_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p52 : ((13885422145271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT315 (i+1))
      = (∑ i ∈ Finset.range 51, stT315 (i+1)) + stT315 52 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 51
    simpa using h
  have hprev := st315_p51
  have hstep := st315_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p53 : ((15207085645801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT315 (i+1))
      = (∑ i ∈ Finset.range 52, stT315 (i+1)) + stT315 53 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 52
    simpa using h
  have hprev := st315_p52
  have hstep := st315_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p54 : ((2069755661153/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT315 (i+1))
      = (∑ i ∈ Finset.range 53, stT315 (i+1)) + stT315 54 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 53
    simpa using h
  have hprev := st315_p53
  have hstep := st315_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p55 : ((17653081465523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT315 (i+1))
      = (∑ i ∈ Finset.range 54, stT315 (i+1)) + stT315 55 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 54
    simpa using h
  have hprev := st315_p54
  have hstep := st315_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p56 : ((18099291410901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT315 (i+1))
      = (∑ i ∈ Finset.range 55, stT315 (i+1)) + stT315 56 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 55
    simpa using h
  have hprev := st315_p55
  have hstep := st315_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p57 : ((1101473838147/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT315 (i+1))
      = (∑ i ∈ Finset.range 56, stT315 (i+1)) + stT315 57 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 56
    simpa using h
  have hprev := st315_p56
  have hstep := st315_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p58 : ((16413412122947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT315 (i+1))
      = (∑ i ∈ Finset.range 57, stT315 (i+1)) + stT315 58 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 57
    simpa using h
  have hprev := st315_p57
  have hstep := st315_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p59 : ((15270563609127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT315 (i+1))
      = (∑ i ∈ Finset.range 58, stT315 (i+1)) + stT315 59 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 58
    simpa using h
  have hprev := st315_p58
  have hstep := st315_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p60 : ((15164469640027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT315 (i+1))
      = (∑ i ∈ Finset.range 59, stT315 (i+1)) + stT315 60 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 59
    simpa using h
  have hprev := st315_p59
  have hstep := st315_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p61 : ((16237761162651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT315 (i+1))
      = (∑ i ∈ Finset.range 60, stT315 (i+1)) + stT315 61 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 60
    simpa using h
  have hprev := st315_p60
  have hstep := st315_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p62 : ((4324179936619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT315 (i+1))
      = (∑ i ∈ Finset.range 61, stT315 (i+1)) + stT315 62 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 61
    simpa using h
  have hprev := st315_p61
  have hstep := st315_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p63 : ((2122063202199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT315 (i+1))
      = (∑ i ∈ Finset.range 62, stT315 (i+1)) + stT315 63 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 62
    simpa using h
  have hprev := st315_p62
  have hstep := st315_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p64 : ((15726425867529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT315 (i+1))
      = (∑ i ∈ Finset.range 63, stT315 (i+1)) + stT315 64 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 63
    simpa using h
  have hprev := st315_p63
  have hstep := st315_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p65 : ((3105032656001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT315 (i+1))
      = (∑ i ∈ Finset.range 64, stT315 (i+1)) + stT315 65 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 64
    simpa using h
  have hprev := st315_p64
  have hstep := st315_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p66 : ((16714660716647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT315 (i+1))
      = (∑ i ∈ Finset.range 65, stT315 (i+1)) + stT315 66 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 65
    simpa using h
  have hprev := st315_p65
  have hstep := st315_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p67 : ((17057212719001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT315 (i+1))
      = (∑ i ∈ Finset.range 66, stT315 (i+1)) + stT315 67 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 66
    simpa using h
  have hprev := st315_p66
  have hstep := st315_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p68 : ((7939394131357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT315 (i+1))
      = (∑ i ∈ Finset.range 67, stT315 (i+1)) + stT315 68 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 67
    simpa using h
  have hprev := st315_p67
  have hstep := st315_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p69 : ((3145737983747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT315 (i+1))
      = (∑ i ∈ Finset.range 68, stT315 (i+1)) + stT315 69 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 68
    simpa using h
  have hprev := st315_p68
  have hstep := st315_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p70 : ((16921988820743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT315 (i+1))
      = (∑ i ∈ Finset.range 69, stT315 (i+1)) + stT315 70 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 69
    simpa using h
  have hprev := st315_p69
  have hstep := st315_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p71 : ((16571965271573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT315 (i+1))
      = (∑ i ∈ Finset.range 70, stT315 (i+1)) + stT315 71 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 70
    simpa using h
  have hprev := st315_p70
  have hstep := st315_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p72 : ((15603181267093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT315 (i+1))
      = (∑ i ∈ Finset.range 71, stT315 (i+1)) + stT315 72 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 71
    simpa using h
  have hprev := st315_p71
  have hstep := st315_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p73 : ((3314164180433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT315 (i+1))
      = (∑ i ∈ Finset.range 72, stT315 (i+1)) + stT315 73 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 72
    simpa using h
  have hprev := st315_p72
  have hstep := st315_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p74 : ((16768159340497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT315 (i+1))
      = (∑ i ∈ Finset.range 73, stT315 (i+1)) + stT315 74 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 73
    simpa using h
  have hprev := st315_p73
  have hstep := st315_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p75 : ((3133919518743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT315 (i+1))
      = (∑ i ∈ Finset.range 74, stT315 (i+1)) + stT315 75 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 74
    simpa using h
  have hprev := st315_p74
  have hstep := st315_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p76 : ((16533963308601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT315 (i+1))
      = (∑ i ∈ Finset.range 75, stT315 (i+1)) + stT315 76 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 75
    simpa using h
  have hprev := st315_p75
  have hstep := st315_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p77 : ((8336573343033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT315 (i+1))
      = (∑ i ∈ Finset.range 76, stT315 (i+1)) + stT315 77 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 76
    simpa using h
  have hprev := st315_p76
  have hstep := st315_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p78 : ((3923350879209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT315 (i+1))
      = (∑ i ∈ Finset.range 77, stT315 (i+1)) + stT315 78 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 77
    simpa using h
  have hprev := st315_p77
  have hstep := st315_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p79 : ((8375867302389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT315 (i+1))
      = (∑ i ∈ Finset.range 78, stT315 (i+1)) + stT315 79 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 78
    simpa using h
  have hprev := st315_p78
  have hstep := st315_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p80 : ((8155983555609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT315 (i+1))
      = (∑ i ∈ Finset.range 79, stT315 (i+1)) + stT315 80 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 79
    simpa using h
  have hprev := st315_p79
  have hstep := st315_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p81 : ((7956407840393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT315 (i+1))
      = (∑ i ∈ Finset.range 80, stT315 (i+1)) + stT315 81 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 80
    simpa using h
  have hprev := st315_p80
  have hstep := st315_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p82 : ((16892244801751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT315 (i+1))
      = (∑ i ∈ Finset.range 81, stT315 (i+1)) + stT315 82 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 81
    simpa using h
  have hprev := st315_p81
  have hstep := st315_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p83 : ((15815654594491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT315 (i+1))
      = (∑ i ∈ Finset.range 82, stT315 (i+1)) + stT315 83 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 82
    simpa using h
  have hprev := st315_p82
  have hstep := st315_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p84 : ((827692142971/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT315 (i+1))
      = (∑ i ∈ Finset.range 83, stT315 (i+1)) + stT315 84 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 83
    simpa using h
  have hprev := st315_p83
  have hstep := st315_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p85 : ((4096046443943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT315 (i+1))
      = (∑ i ∈ Finset.range 84, stT315 (i+1)) + stT315 85 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 84
    simpa using h
  have hprev := st315_p84
  have hstep := st315_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p86 : ((3994603546089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT315 (i+1))
      = (∑ i ∈ Finset.range 85, stT315 (i+1)) + stT315 86 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 85
    simpa using h
  have hprev := st315_p85
  have hstep := st315_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p87 : ((4202139770713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT315 (i+1))
      = (∑ i ∈ Finset.range 86, stT315 (i+1)) + stT315 87 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 86
    simpa using h
  have hprev := st315_p86
  have hstep := st315_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p88 : ((394242308667/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT315 (i+1))
      = (∑ i ∈ Finset.range 87, stT315 (i+1)) + stT315 88 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 87
    simpa using h
  have hprev := st315_p87
  have hstep := st315_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p89 : ((16810271261637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT315 (i+1))
      = (∑ i ∈ Finset.range 88, stT315 (i+1)) + stT315 89 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 88
    simpa using h
  have hprev := st315_p88
  have hstep := st315_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p90 : ((3980563971063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT315 (i+1))
      = (∑ i ∈ Finset.range 89, stT315 (i+1)) + stT315 90 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 89
    simpa using h
  have hprev := st315_p89
  have hstep := st315_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p91 : ((82834736997/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT315 (i+1))
      = (∑ i ∈ Finset.range 90, stT315 (i+1)) + stT315 91 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 90
    simpa using h
  have hprev := st315_p90
  have hstep := st315_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p92 : ((4049538991741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT315 (i+1))
      = (∑ i ∈ Finset.range 91, stT315 (i+1)) + stT315 92 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 91
    simpa using h
  have hprev := st315_p91
  have hstep := st315_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p93 : ((16299108331569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT315 (i+1))
      = (∑ i ∈ Finset.range 92, stT315 (i+1)) + stT315 93 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 92
    simpa using h
  have hprev := st315_p92
  have hstep := st315_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p94 : ((16432524700761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT315 (i+1))
      = (∑ i ∈ Finset.range 93, stT315 (i+1)) + stT315 94 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 93
    simpa using h
  have hprev := st315_p93
  have hstep := st315_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p95 : ((1006758743397/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT315 (i+1))
      = (∑ i ∈ Finset.range 94, stT315 (i+1)) + stT315 95 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 94
    simpa using h
  have hprev := st315_p94
  have hstep := st315_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p96 : ((2072242175509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT315 (i+1))
      = (∑ i ∈ Finset.range 95, stT315 (i+1)) + stT315 96 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 95
    simpa using h
  have hprev := st315_p95
  have hstep := st315_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p97 : ((4000892962931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT315 (i+1))
      = (∑ i ∈ Finset.range 96, stT315 (i+1)) + stT315 97 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 96
    simpa using h
  have hprev := st315_p96
  have hstep := st315_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p98 : ((4161684917683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT315 (i+1))
      = (∑ i ∈ Finset.range 97, stT315 (i+1)) + stT315 98 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 97
    simpa using h
  have hprev := st315_p97
  have hstep := st315_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p99 : ((159639530349/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT315 (i+1))
      = (∑ i ∈ Finset.range 98, stT315 (i+1)) + stT315 99 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 98
    simpa using h
  have hprev := st315_p98
  have hstep := st315_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p100 : ((16660713338139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT315 (i+1))
      = (∑ i ∈ Finset.range 99, stT315 (i+1)) + stT315 100 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 99
    simpa using h
  have hprev := st315_p99
  have hstep := st315_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p101 : ((15972378885993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT315 (i+1))
      = (∑ i ∈ Finset.range 100, stT315 (i+1)) + stT315 101 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 100
    simpa using h
  have hprev := st315_p100
  have hstep := st315_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p102 : ((16629383006667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT315 (i+1))
      = (∑ i ∈ Finset.range 101, stT315 (i+1)) + stT315 102 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 101
    simpa using h
  have hprev := st315_p101
  have hstep := st315_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p103 : ((16027300066157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT315 (i+1))
      = (∑ i ∈ Finset.range 102, stT315 (i+1)) + stT315 103 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 102
    simpa using h
  have hprev := st315_p102
  have hstep := st315_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p104 : ((16547376164237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT315 (i+1))
      = (∑ i ∈ Finset.range 103, stT315 (i+1)) + stT315 104 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 103
    simpa using h
  have hprev := st315_p103
  have hstep := st315_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p105 : ((1008669668299/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT315 (i+1))
      = (∑ i ∈ Finset.range 104, stT315 (i+1)) + stT315 105 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 104
    simpa using h
  have hprev := st315_p104
  have hstep := st315_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p106 : ((8201725037477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT315 (i+1))
      = (∑ i ∈ Finset.range 105, stT315 (i+1)) + stT315 106 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 105
    simpa using h
  have hprev := st315_p105
  have hstep := st315_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p107 : ((407854974541/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT315 (i+1))
      = (∑ i ∈ Finset.range 106, stT315 (i+1)) + stT315 107 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 106
    simpa using h
  have hprev := st315_p106
  have hstep := st315_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p108 : ((16199880676087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT315 (i+1))
      = (∑ i ∈ Finset.range 107, stT315 (i+1)) + stT315 108 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 107
    simpa using h
  have hprev := st315_p107
  have hstep := st315_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p109 : ((16534822850027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT315 (i+1))
      = (∑ i ∈ Finset.range 108, stT315 (i+1)) + stT315 109 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 108
    simpa using h
  have hprev := st315_p108
  have hstep := st315_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p110 : ((15979024477289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT315 (i+1))
      = (∑ i ∈ Finset.range 109, stT315 (i+1)) + stT315 110 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 109
    simpa using h
  have hprev := st315_p109
  have hstep := st315_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p111 : ((3346016204301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT315 (i+1))
      = (∑ i ∈ Finset.range 110, stT315 (i+1)) + stT315 111 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 110
    simpa using h
  have hprev := st315_p110
  have hstep := st315_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p112 : ((15839556266401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT315 (i+1))
      = (∑ i ∈ Finset.range 111, stT315 (i+1)) + stT315 112 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 111
    simpa using h
  have hprev := st315_p111
  have hstep := st315_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p113 : ((16780182194401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT315 (i+1))
      = (∑ i ∈ Finset.range 112, stT315 (i+1)) + stT315 113 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 112
    simpa using h
  have hprev := st315_p112
  have hstep := st315_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p114 : ((3181145674611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT315 (i+1))
      = (∑ i ∈ Finset.range 113, stT315 (i+1)) + stT315 114 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 113
    simpa using h
  have hprev := st315_p113
  have hstep := st315_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p115 : ((16583438710111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT315 (i+1))
      = (∑ i ∈ Finset.range 114, stT315 (i+1)) + stT315 115 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 114
    simpa using h
  have hprev := st315_p114
  have hstep := st315_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p116 : ((16222274155789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT315 (i+1))
      = (∑ i ∈ Finset.range 115, stT315 (i+1)) + stT315 116 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 115
    simpa using h
  have hprev := st315_p115
  have hstep := st315_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p117 : ((647472263977/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT315 (i+1))
      = (∑ i ∈ Finset.range 116, stT315 (i+1)) + stT315 117 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 116
    simpa using h
  have hprev := st315_p116
  have hstep := st315_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p118 : ((16627249706281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT315 (i+1))
      = (∑ i ∈ Finset.range 117, stT315 (i+1)) + stT315 118 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 117
    simpa using h
  have hprev := st315_p117
  have hstep := st315_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p119 : ((7932317945547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT315 (i+1))
      = (∑ i ∈ Finset.range 118, stT315 (i+1)) + stT315 119 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 118
    simpa using h
  have hprev := st315_p118
  have hstep := st315_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p120 : ((8387141729997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT315 (i+1))
      = (∑ i ∈ Finset.range 119, stT315 (i+1)) + stT315 120 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 119
    simpa using h
  have hprev := st315_p119
  have hstep := st315_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p121 : ((15953487923369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT315 (i+1))
      = (∑ i ∈ Finset.range 120, stT315 (i+1)) + stT315 121 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 120
    simpa using h
  have hprev := st315_p120
  have hstep := st315_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p122 : ((1644742625793/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT315 (i+1))
      = (∑ i ∈ Finset.range 121, stT315 (i+1)) + stT315 122 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 121
    simpa using h
  have hprev := st315_p121
  have hstep := st315_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p123 : ((82204946179/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT315 (i+1))
      = (∑ i ∈ Finset.range 122, stT315 (i+1)) + stT315 123 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 122
    simpa using h
  have hprev := st315_p122
  have hstep := st315_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p124 : ((3986451592919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT315 (i+1))
      = (∑ i ∈ Finset.range 123, stT315 (i+1)) + stT315 124 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 123
    simpa using h
  have hprev := st315_p123
  have hstep := st315_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p125 : ((3355570669883/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT315 (i+1))
      = (∑ i ∈ Finset.range 124, stT315 (i+1)) + stT315 125 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 124
    simpa using h
  have hprev := st315_p124
  have hstep := st315_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p126 : ((3183194258351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT315 (i+1))
      = (∑ i ∈ Finset.range 125, stT315 (i+1)) + stT315 126 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 125
    simpa using h
  have hprev := st315_p125
  have hstep := st315_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p127 : ((16462114063787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT315 (i+1))
      = (∑ i ∈ Finset.range 126, stT315 (i+1)) + stT315 127 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 126
    simpa using h
  have hprev := st315_p126
  have hstep := st315_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p128 : ((8234492243173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT315 (i+1))
      = (∑ i ∈ Finset.range 127, stT315 (i+1)) + stT315 128 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 127
    simpa using h
  have hprev := st315_p127
  have hstep := st315_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p129 : ((15902992724153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT315 (i+1))
      = (∑ i ∈ Finset.range 128, stT315 (i+1)) + stT315 129 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 128
    simpa using h
  have hprev := st315_p128
  have hstep := st315_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p130 : ((3353651560457/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT315 (i+1))
      = (∑ i ∈ Finset.range 129, stT315 (i+1)) + stT315 130 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 129
    simpa using h
  have hprev := st315_p129
  have hstep := st315_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p131 : ((320597671817/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT315 (i+1))
      = (∑ i ∈ Finset.range 130, stT315 (i+1)) + stT315 131 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 130
    simpa using h
  have hprev := st315_p130
  have hstep := st315_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p132 : ((325078429241/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT315 (i+1))
      = (∑ i ∈ Finset.range 131, stT315 (i+1)) + stT315 132 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 131
    simpa using h
  have hprev := st315_p131
  have hstep := st315_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p133 : ((8336214943341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT315 (i+1))
      = (∑ i ∈ Finset.range 132, stT315 (i+1)) + stT315 133 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 132
    simpa using h
  have hprev := st315_p132
  have hstep := st315_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p134 : ((15843313472683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT315 (i+1))
      = (∑ i ∈ Finset.range 133, stT315 (i+1)) + stT315 134 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 133
    simpa using h
  have hprev := st315_p133
  have hstep := st315_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p135 : ((16592418185567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT315 (i+1))
      = (∑ i ∈ Finset.range 134, stT315 (i+1)) + stT315 135 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 134
    simpa using h
  have hprev := st315_p134
  have hstep := st315_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p136 : ((16389070580561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT315 (i+1))
      = (∑ i ∈ Finset.range 135, stT315 (i+1)) + stT315 136 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 135
    simpa using h
  have hprev := st315_p135
  have hstep := st315_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p137 : ((3182085523543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT315 (i+1))
      = (∑ i ∈ Finset.range 136, stT315 (i+1)) + stT315 137 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 136
    simpa using h
  have hprev := st315_p136
  have hstep := st315_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p138 : ((16754898256139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT315 (i+1))
      = (∑ i ∈ Finset.range 137, stT315 (i+1)) + stT315 138 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 137
    simpa using h
  have hprev := st315_p137
  have hstep := st315_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p139 : ((16129394492577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT315 (i+1))
      = (∑ i ∈ Finset.range 138, stT315 (i+1)) + stT315 139 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 138
    simpa using h
  have hprev := st315_p138
  have hstep := st315_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p140 : ((8041693394921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT315 (i+1))
      = (∑ i ∈ Finset.range 139, stT315 (i+1)) + stT315 140 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 139
    simpa using h
  have hprev := st315_p139
  have hstep := st315_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p141 : ((4192565918191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT315 (i+1))
      = (∑ i ∈ Finset.range 140, stT315 (i+1)) + stT315 141 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 140
    simpa using h
  have hprev := st315_p140
  have hstep := st315_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p142 : ((3992033309107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT315 (i+1))
      = (∑ i ∈ Finset.range 141, stT315 (i+1)) + stT315 142 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 141
    simpa using h
  have hprev := st315_p141
  have hstep := st315_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p143 : ((8123913458479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT315 (i+1))
      = (∑ i ∈ Finset.range 142, stT315 (i+1)) + stT315 143 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 142
    simpa using h
  have hprev := st315_p142
  have hstep := st315_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p144 : ((4180486265161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT315 (i+1))
      = (∑ i ∈ Finset.range 143, stT315 (i+1)) + stT315 144 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 143
    simpa using h
  have hprev := st315_p143
  have hstep := st315_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p145 : ((15891412828329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT315 (i+1))
      = (∑ i ∈ Finset.range 144, stT315 (i+1)) + stT315 145 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 144
    simpa using h
  have hprev := st315_p144
  have hstep := st315_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p146 : ((8178627979167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT315 (i+1))
      = (∑ i ∈ Finset.range 145, stT315 (i+1)) + stT315 146 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 145
    simpa using h
  have hprev := st315_p145
  have hstep := st315_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p147 : ((521042942591/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT315 (i+1))
      = (∑ i ∈ Finset.range 146, stT315 (i+1)) + stT315 147 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 146
    simpa using h
  have hprev := st315_p146
  have hstep := st315_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p148 : ((15863336724177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT315 (i+1))
      = (∑ i ∈ Finset.range 147, stT315 (i+1)) + stT315 148 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 147
    simpa using h
  have hprev := st315_p147
  have hstep := st315_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p149 : ((1640455594971/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT315 (i+1))
      = (∑ i ∈ Finset.range 148, stT315 (i+1)) + stT315 149 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 148
    simpa using h
  have hprev := st315_p148
  have hstep := st315_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p150 : ((8327857509143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT315 (i+1))
      = (∑ i ∈ Finset.range 149, stT315 (i+1)) + stT315 150 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 149
    simpa using h
  have hprev := st315_p149
  have hstep := st315_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p151 : ((15859633253137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT315 (i+1))
      = (∑ i ∈ Finset.range 150, stT315 (i+1)) + stT315 151 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 150
    simpa using h
  have hprev := st315_p150
  have hstep := st315_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p152 : ((16393099949251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT315 (i+1))
      = (∑ i ∈ Finset.range 151, stT315 (i+1)) + stT315 152 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 151
    simpa using h
  have hprev := st315_p151
  have hstep := st315_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p153 : ((16676389614571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT315 (i+1))
      = (∑ i ∈ Finset.range 152, stT315 (i+1)) + stT315 153 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 152
    simpa using h
  have hprev := st315_p152
  have hstep := st315_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p154 : ((15876595782257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT315 (i+1))
      = (∑ i ∈ Finset.range 153, stT315 (i+1)) + stT315 154 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 153
    simpa using h
  have hprev := st315_p153
  have hstep := st315_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p155 : ((16324236156709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT315 (i+1))
      = (∑ i ∈ Finset.range 154, stT315 (i+1)) + stT315 155 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 154
    simpa using h
  have hprev := st315_p154
  have hstep := st315_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p156 : ((16725169446949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT315 (i+1))
      = (∑ i ∈ Finset.range 155, stT315 (i+1)) + stT315 156 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 155
    simpa using h
  have hprev := st315_p155
  have hstep := st315_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p157 : ((15929724114919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT315 (i+1))
      = (∑ i ∈ Finset.range 156, stT315 (i+1)) + stT315 157 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 156
    simpa using h
  have hprev := st315_p156
  have hstep := st315_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p158 : ((8099945647167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT315 (i+1))
      = (∑ i ∈ Finset.range 157, stT315 (i+1)) + stT315 158 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 157
    simpa using h
  have hprev := st315_p157
  have hstep := st315_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p159 : ((3354579045283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT315 (i+1))
      = (∑ i ∈ Finset.range 158, stT315 (i+1)) + stT315 159 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 158
    simpa using h
  have hprev := st315_p158
  have hstep := st315_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p160 : ((3209145313741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT315 (i+1))
      = (∑ i ∈ Finset.range 159, stT315 (i+1)) + stT315 160 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 159
    simpa using h
  have hprev := st315_p159
  have hstep := st315_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p161 : ((4009114004753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT315 (i+1))
      = (∑ i ∈ Finset.range 160, stT315 (i+1)) + stT315 161 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 160
    simpa using h
  have hprev := st315_p160
  have hstep := st315_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p162 : ((8384721753123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT315 (i+1))
      = (∑ i ∈ Finset.range 161, stT315 (i+1)) + stT315 162 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 161
    simpa using h
  have hprev := st315_p161
  have hstep := st315_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p163 : ((16243711673697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT315 (i+1))
      = (∑ i ∈ Finset.range 162, stT315 (i+1)) + stT315 163 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 162
    simpa using h
  have hprev := st315_p162
  have hstep := st315_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p164 : ((15883538970923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT315 (i+1))
      = (∑ i ∈ Finset.range 163, stT315 (i+1)) + stT315 164 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 163
    simpa using h
  have hprev := st315_p163
  have hstep := st315_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p165 : ((16654855326873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT315 (i+1))
      = (∑ i ∈ Finset.range 164, stT315 (i+1)) + stT315 165 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 164
    simpa using h
  have hprev := st315_p164
  have hstep := st315_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p166 : ((16502611755921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT315 (i+1))
      = (∑ i ∈ Finset.range 165, stT315 (i+1)) + stT315 166 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 165
    simpa using h
  have hprev := st315_p165
  have hstep := st315_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p167 : ((15830401680657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT315 (i+1))
      = (∑ i ∈ Finset.range 166, stT315 (i+1)) + stT315 167 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 166
    simpa using h
  have hprev := st315_p166
  have hstep := st315_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p168 : ((3279746708289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT315 (i+1))
      = (∑ i ∈ Finset.range 167, stT315 (i+1)) + stT315 168 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 167
    simpa using h
  have hprev := st315_p167
  have hstep := st315_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p169 : ((669160282293/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT315 (i+1))
      = (∑ i ∈ Finset.range 168, stT315 (i+1)) + stT315 169 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 168
    simpa using h
  have hprev := st315_p168
  have hstep := st315_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p170 : ((199641404541/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT315 (i+1))
      = (∑ i ∈ Finset.range 169, stT315 (i+1)) + stT315 170 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 169
    simpa using h
  have hprev := st315_p169
  have hstep := st315_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p171 : ((8031553851301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT315 (i+1))
      = (∑ i ∈ Finset.range 170, stT315 (i+1)) + stT315 171 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 170
    simpa using h
  have hprev := st315_p170
  have hstep := st315_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p172 : ((1676931559313/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT315 (i+1))
      = (∑ i ∈ Finset.range 171, stT315 (i+1)) + stT315 172 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 171
    simpa using h
  have hprev := st315_p171
  have hstep := st315_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p173 : ((2039273863369/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT315 (i+1))
      = (∑ i ∈ Finset.range 172, stT315 (i+1)) + stT315 173 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 172
    simpa using h
  have hprev := st315_p172
  have hstep := st315_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p174 : ((15834856280737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT315 (i+1))
      = (∑ i ∈ Finset.range 173, stT315 (i+1)) + stT315 174 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 173
    simpa using h
  have hprev := st315_p173
  have hstep := st315_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p175 : ((16515455299609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT315 (i+1))
      = (∑ i ∈ Finset.range 174, stT315 (i+1)) + stT315 175 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 174
    simpa using h
  have hprev := st315_p174
  have hstep := st315_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p176 : ((16684230716477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT315 (i+1))
      = (∑ i ∈ Finset.range 175, stT315 (i+1)) + stT315 176 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 175
    simpa using h
  have hprev := st315_p175
  have hstep := st315_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p177 : ((15932562670361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT315 (i+1))
      = (∑ i ∈ Finset.range 176, stT315 (i+1)) + stT315 177 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 176
    simpa using h
  have hprev := st315_p176
  have hstep := st315_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p178 : ((3215082257293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT315 (i+1))
      = (∑ i ∈ Finset.range 177, stT315 (i+1)) + stT315 178 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 177
    simpa using h
  have hprev := st315_p177
  have hstep := st315_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p179 : ((1676783731277/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT315 (i+1))
      = (∑ i ∈ Finset.range 178, stT315 (i+1)) + stT315 179 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 178
    simpa using h
  have hprev := st315_p178
  have hstep := st315_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p180 : ((8182817508127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT315 (i+1))
      = (∑ i ∈ Finset.range 179, stT315 (i+1)) + stT315 180 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 179
    simpa using h
  have hprev := st315_p179
  have hstep := st315_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p181 : ((15818781735329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT315 (i+1))
      = (∑ i ∈ Finset.range 180, stT315 (i+1)) + stT315 181 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 180
    simpa using h
  have hprev := st315_p180
  have hstep := st315_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p182 : ((410086213883/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT315 (i+1))
      = (∑ i ∈ Finset.range 181, stT315 (i+1)) + stT315 182 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 181
    simpa using h
  have hprev := st315_p181
  have hstep := st315_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p183 : ((16762049836967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT315 (i+1))
      = (∑ i ∈ Finset.range 182, stT315 (i+1)) + stT315 183 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 182
    simpa using h
  have hprev := st315_p182
  have hstep := st315_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p184 : ((16072224746927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT315 (i+1))
      = (∑ i ∈ Finset.range 183, stT315 (i+1)) + stT315 184 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 183
    simpa using h
  have hprev := st315_p183
  have hstep := st315_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p185 : ((7954333306191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT315 (i+1))
      = (∑ i ∈ Finset.range 184, stT315 (i+1)) + stT315 185 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 184
    simpa using h
  have hprev := st315_p184
  have hstep := st315_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p186 : ((1039899155237/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT315 (i+1))
      = (∑ i ∈ Finset.range 185, stT315 (i+1)) + stT315 186 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 185
    simpa using h
  have hprev := st315_p185
  have hstep := st315_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p187 : ((2077842155199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT315 (i+1))
      = (∑ i ∈ Finset.range 186, stT315 (i+1)) + stT315 187 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 186
    simpa using h
  have hprev := st315_p186
  have hstep := st315_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p188 : ((7949770015121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT315 (i+1))
      = (∑ i ∈ Finset.range 187, stT315 (i+1)) + stT315 188 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 187
    simpa using h
  have hprev := st315_p187
  have hstep := st315_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p189 : ((8032933106177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT315 (i+1))
      = (∑ i ∈ Finset.range 188, stT315 (i+1)) + stT315 189 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 188
    simpa using h
  have hprev := st315_p188
  have hstep := st315_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p190 : ((67015691543/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT315 (i+1))
      = (∑ i ∈ Finset.range 189, stT315 (i+1)) + stT315 190 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 189
    simpa using h
  have hprev := st315_p189
  have hstep := st315_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p191 : ((131749835339/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT315 (i+1))
      = (∑ i ∈ Finset.range 190, stT315 (i+1)) + stT315 191 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 190
    simpa using h
  have hprev := st315_p190
  have hstep := st315_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p192 : ((15828234204127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT315 (i+1))
      = (∑ i ∈ Finset.range 191, stT315 (i+1)) + stT315 192 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 191
    simpa using h
  have hprev := st315_p191
  have hstep := st315_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p193 : ((16201140123397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT315 (i+1))
      = (∑ i ∈ Finset.range 192, stT315 (i+1)) + stT315 193 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 192
    simpa using h
  have hprev := st315_p192
  have hstep := st315_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p194 : ((16792886132703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT315 (i+1))
      = (∑ i ∈ Finset.range 193, stT315 (i+1)) + stT315 194 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 193
    simpa using h
  have hprev := st315_p193
  have hstep := st315_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p195 : ((16359109497063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT315 (i+1))
      = (∑ i ∈ Finset.range 194, stT315 (i+1)) + stT315 195 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 194
    simpa using h
  have hprev := st315_p194
  have hstep := st315_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p196 : ((3161722855373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT315 (i+1))
      = (∑ i ∈ Finset.range 195, stT315 (i+1)) + stT315 196 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 195
    simpa using h
  have hprev := st315_p195
  have hstep := st315_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p197 : ((130240775993/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT315 (i+1))
      = (∑ i ∈ Finset.range 196, stT315 (i+1)) + stT315 197 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 196
    simpa using h
  have hprev := st315_p196
  have hstep := st315_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p198 : ((8400627014451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT315 (i+1))
      = (∑ i ∈ Finset.range 197, stT315 (i+1)) + stT315 198 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 197
    simpa using h
  have hprev := st315_p197
  have hstep := st315_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p199 : ((4077749758851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT315 (i+1))
      = (∑ i ∈ Finset.range 198, stT315 (i+1)) + stT315 199 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 198
    simpa using h
  have hprev := st315_p198
  have hstep := st315_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p200 : ((15804121403273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT315 (i+1))
      = (∑ i ∈ Finset.range 199, stT315 (i+1)) + stT315 200 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 199
    simpa using h
  have hprev := st315_p199
  have hstep := st315_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p201 : ((8148036016159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT315 (i+1))
      = (∑ i ∈ Finset.range 200, stT315 (i+1)) + stT315 201 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 200
    simpa using h
  have hprev := st315_p200
  have hstep := st315_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p202 : ((16803836175711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT315 (i+1))
      = (∑ i ∈ Finset.range 201, stT315 (i+1)) + stT315 202 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 201
    simpa using h
  have hprev := st315_p201
  have hstep := st315_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p203 : ((255089913637/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT315 (i+1))
      = (∑ i ∈ Finset.range 202, stT315 (i+1)) + stT315 203 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 202
    simpa using h
  have hprev := st315_p202
  have hstep := st315_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p204 : ((15802244344107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT315 (i+1))
      = (∑ i ∈ Finset.range 203, stT315 (i+1)) + stT315 204 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 203
    simpa using h
  have hprev := st315_p203
  have hstep := st315_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p205 : ((16249909338477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT315 (i+1))
      = (∑ i ∈ Finset.range 204, stT315 (i+1)) + stT315 205 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 204
    simpa using h
  have hprev := st315_p204
  have hstep := st315_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p206 : ((8400567264279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT315 (i+1))
      = (∑ i ∈ Finset.range 205, stT315 (i+1)) + stT315 206 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 205
    simpa using h
  have hprev := st315_p205
  have hstep := st315_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p207 : ((16401438955569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT315 (i+1))
      = (∑ i ∈ Finset.range 206, stT315 (i+1)) + stT315 207 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 206
    simpa using h
  have hprev := st315_p206
  have hstep := st315_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p208 : ((15813844398129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT315 (i+1))
      = (∑ i ∈ Finset.range 207, stT315 (i+1)) + stT315 208 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 207
    simpa using h
  have hprev := st315_p207
  have hstep := st315_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p209 : ((16145307521503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT315 (i+1))
      = (∑ i ∈ Finset.range 208, stT315 (i+1)) + stT315 209 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 208
    simpa using h
  have hprev := st315_p208
  have hstep := st315_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p210 : ((16771722306033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT315 (i+1))
      = (∑ i ∈ Finset.range 209, stT315 (i+1)) + stT315 210 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 209
    simpa using h
  have hprev := st315_p209
  have hstep := st315_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p211 : ((16530244819419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT315 (i+1))
      = (∑ i ∈ Finset.range 210, stT315 (i+1)) + stT315 211 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 210
    simpa using h
  have hprev := st315_p210
  have hstep := st315_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p212 : ((991845197709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT315 (i+1))
      = (∑ i ∈ Finset.range 211, stT315 (i+1)) + stT315 212 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 211
    simpa using h
  have hprev := st315_p211
  have hstep := st315_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p213 : ((31995562899/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT315 (i+1))
      = (∑ i ∈ Finset.range 212, stT315 (i+1)) + stT315 213 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 212
    simpa using h
  have hprev := st315_p212
  have hstep := st315_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p214 : ((833917113473/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT315 (i+1))
      = (∑ i ∈ Finset.range 213, stT315 (i+1)) + stT315 214 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 213
    simpa using h
  have hprev := st315_p213
  have hstep := st315_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p215 : ((521392862583/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT315 (i+1))
      = (∑ i ∈ Finset.range 214, stT315 (i+1)) + stT315 215 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 214
    simpa using h
  have hprev := st315_p214
  have hstep := st315_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p216 : ((4002211413779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT315 (i+1))
      = (∑ i ∈ Finset.range 215, stT315 (i+1)) + stT315 216 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 215
    simpa using h
  have hprev := st315_p215
  have hstep := st315_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p217 : ((7925638113393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT315 (i+1))
      = (∑ i ∈ Finset.range 216, stT315 (i+1)) + stT315 217 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 216
    simpa using h
  have hprev := st315_p216
  have hstep := st315_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p218 : ((16485868566811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT315 (i+1))
      = (∑ i ∈ Finset.range 217, stT315 (i+1)) + stT315 218 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 217
    simpa using h
  have hprev := st315_p217
  have hstep := st315_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p219 : ((8400657718707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT315 (i+1))
      = (∑ i ∈ Finset.range 218, stT315 (i+1)) + stT315 219 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 218
    simpa using h
  have hprev := st315_p218
  have hstep := st315_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p220 : ((8126564405507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT315 (i+1))
      = (∑ i ∈ Finset.range 219, stT315 (i+1)) + stT315 220 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 219
    simpa using h
  have hprev := st315_p219
  have hstep := st315_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p221 : ((15787826770781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT315 (i+1))
      = (∑ i ∈ Finset.range 220, stT315 (i+1)) + stT315 221 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 220
    simpa using h
  have hprev := st315_p220
  have hstep := st315_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p222 : ((16198390346037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT315 (i+1))
      = (∑ i ∈ Finset.range 221, stT315 (i+1)) + stT315 222 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 221
    simpa using h
  have hprev := st315_p221
  have hstep := st315_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p223 : ((3356986109589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT315 (i+1))
      = (∑ i ∈ Finset.range 222, stT315 (i+1)) + stT315 223 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 222
    simpa using h
  have hprev := st315_p222
  have hstep := st315_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p224 : ((16560837041577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT315 (i+1))
      = (∑ i ∈ Finset.range 223, stT315 (i+1)) + stT315 224 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 223
    simpa using h
  have hprev := st315_p223
  have hstep := st315_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p225 : ((636167975197/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT315 (i+1))
      = (∑ i ∈ Finset.range 224, stT315 (i+1)) + stT315 225 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 224
    simpa using h
  have hprev := st315_p224
  have hstep := st315_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p226 : ((3180872071181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT315 (i+1))
      = (∑ i ∈ Finset.range 225, stT315 (i+1)) + stT315 226 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 225
    simpa using h
  have hprev := st315_p225
  have hstep := st315_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p227 : ((1655732772469/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT315 (i+1))
      = (∑ i ∈ Finset.range 226, stT315 (i+1)) + stT315 227 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 226
    simpa using h
  have hprev := st315_p226
  have hstep := st315_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p228 : ((8397105500583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT315 (i+1))
      = (∑ i ∈ Finset.range 227, stT315 (i+1)) + stT315 228 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 227
    simpa using h
  have hprev := st315_p227
  have hstep := st315_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p229 : ((3246721172667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT315 (i+1))
      = (∑ i ∈ Finset.range 228, stT315 (i+1)) + stT315 229 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 228
    simpa using h
  have hprev := st315_p228
  have hstep := st315_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p230 : ((15781014657507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT315 (i+1))
      = (∑ i ∈ Finset.range 229, stT315 (i+1)) + stT315 230 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 229
    simpa using h
  have hprev := st315_p229
  have hstep := st315_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p231 : ((16157987682957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT315 (i+1))
      = (∑ i ∈ Finset.range 230, stT315 (i+1)) + stT315 231 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 230
    simpa using h
  have hprev := st315_p230
  have hstep := st315_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p232 : ((16762602445461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT315 (i+1))
      = (∑ i ∈ Finset.range 231, stT315 (i+1)) + stT315 232 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 231
    simpa using h
  have hprev := st315_p231
  have hstep := st315_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p233 : ((16642576888719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT315 (i+1))
      = (∑ i ∈ Finset.range 232, stT315 (i+1)) + stT315 233 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 232
    simpa using h
  have hprev := st315_p232
  have hstep := st315_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p234 : ((7994626348683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT315 (i+1))
      = (∑ i ∈ Finset.range 233, stT315 (i+1)) + stT315 234 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 233
    simpa using h
  have hprev := st315_p233
  have hstep := st315_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p235 : ((15818270090847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT315 (i+1))
      = (∑ i ∈ Finset.range 234, stT315 (i+1)) + stT315 235 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 234
    simpa using h
  have hprev := st315_p234
  have hstep := st315_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p236 : ((16389986394719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT315 (i+1))
      = (∑ i ∈ Finset.range 235, stT315 (i+1)) + stT315 236 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 235
    simpa using h
  have hprev := st315_p235
  have hstep := st315_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p237 : ((4206643190573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT315 (i+1))
      = (∑ i ∈ Finset.range 236, stT315 (i+1)) + stT315 237 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 236
    simpa using h
  have hprev := st315_p236
  have hstep := st315_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p238 : ((4116588208853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT315 (i+1))
      = (∑ i ∈ Finset.range 237, stT315 (i+1)) + stT315 238 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 237
    simpa using h
  have hprev := st315_p237
  have hstep := st315_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p239 : ((15856270678351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT315 (i+1))
      = (∑ i ∈ Finset.range 238, stT315 (i+1)) + stT315 239 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 238
    simpa using h
  have hprev := st315_p238
  have hstep := st315_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p240 : ((3977515469963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT315 (i+1))
      = (∑ i ∈ Finset.range 239, stT315 (i+1)) + stT315 240 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 239
    simpa using h
  have hprev := st315_p239
  have hstep := st315_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p241 : ((2068004141167/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT315 (i+1))
      = (∑ i ∈ Finset.range 240, stT315 (i+1)) + stT315 241 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 240
    simpa using h
  have hprev := st315_p240
  have hstep := st315_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p242 : ((2102507880073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT315 (i+1))
      = (∑ i ∈ Finset.range 241, stT315 (i+1)) + stT315 242 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 241
    simpa using h
  have hprev := st315_p241
  have hstep := st315_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p243 : ((16335930575397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT315 (i+1))
      = (∑ i ∈ Finset.range 242, stT315 (i+1)) + stT315 243 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 242
    simpa using h
  have hprev := st315_p242
  have hstep := st315_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p244 : ((15799629675717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT315 (i+1))
      = (∑ i ∈ Finset.range 243, stT315 (i+1)) + stT315 244 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 243
    simpa using h
  have hprev := st315_p243
  have hstep := st315_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p245 : ((15985562396873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT315 (i+1))
      = (∑ i ∈ Finset.range 244, stT315 (i+1)) + stT315 245 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 244
    simpa using h
  have hprev := st315_p244
  have hstep := st315_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p246 : ((16623055511993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT315 (i+1))
      = (∑ i ∈ Finset.range 245, stT315 (i+1)) + stT315 246 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 245
    simpa using h
  have hprev := st315_p245
  have hstep := st315_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p247 : ((16802002115301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT315 (i+1))
      = (∑ i ∈ Finset.range 246, stT315 (i+1)) + stT315 247 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 246
    simpa using h
  have hprev := st315_p246
  have hstep := st315_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p248 : ((2033990053191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT315 (i+1))
      = (∑ i ∈ Finset.range 247, stT315 (i+1)) + stT315 248 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 247
    simpa using h
  have hprev := st315_p247
  have hstep := st315_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p249 : ((3945205393507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT315 (i+1))
      = (∑ i ∈ Finset.range 248, stT315 (i+1)) + stT315 249 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 248
    simpa using h
  have hprev := st315_p248
  have hstep := st315_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p250 : ((8006525097829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT315 (i+1))
      = (∑ i ∈ Finset.range 249, stT315 (i+1)) + stT315 250 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 249
    simpa using h
  have hprev := st315_p249
  have hstep := st315_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p251 : ((8321468812039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT315 (i+1))
      = (∑ i ∈ Finset.range 250, stT315 (i+1)) + stT315 251 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 250
    simpa using h
  have hprev := st315_p250
  have hstep := st315_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p252 : ((8401055116669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT315 (i+1))
      = (∑ i ∈ Finset.range 251, stT315 (i+1)) + stT315 252 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 251
    simpa using h
  have hprev := st315_p251
  have hstep := st315_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p253 : ((8137880874889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT315 (i+1))
      = (∑ i ∈ Finset.range 252, stT315 (i+1)) + stT315 253 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 252
    simpa using h
  have hprev := st315_p252
  have hstep := st315_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p254 : ((315629502577/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT315 (i+1))
      = (∑ i ∈ Finset.range 253, stT315 (i+1)) + stT315 254 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 253
    simpa using h
  have hprev := st315_p253
  have hstep := st315_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p255 : ((7992382173649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT315 (i+1))
      = (∑ i ∈ Finset.range 254, stT315 (i+1)) + stT315 255 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 254
    simpa using h
  have hprev := st315_p254
  have hstep := st315_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p256 : ((8304842798649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT315 (i+1))
      = (∑ i ∈ Finset.range 255, stT315 (i+1)) + stT315 256 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 255
    simpa using h
  have hprev := st315_p255
  have hstep := st315_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p257 : ((8411738448643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT315 (i+1))
      = (∑ i ∈ Finset.range 256, stT315 (i+1)) + stT315 257 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 256
    simpa using h
  have hprev := st315_p256
  have hstep := st315_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p258 : ((2043276710079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT315 (i+1))
      = (∑ i ∈ Finset.range 257, stT315 (i+1)) + stT315 258 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 257
    simpa using h
  have hprev := st315_p257
  have hstep := st315_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p259 : ((3951817724153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT315 (i+1))
      = (∑ i ∈ Finset.range 258, stT315 (i+1)) + stT315 259 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 258
    simpa using h
  have hprev := st315_p258
  have hstep := st315_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p260 : ((7954304202579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT315 (i+1))
      = (∑ i ∈ Finset.range 259, stT315 (i+1)) + stT315 260 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 259
    simpa using h
  have hprev := st315_p259
  have hstep := st315_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p261 : ((1651551788427/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT315 (i+1))
      = (∑ i ∈ Finset.range 260, stT315 (i+1)) + stT315 261 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 260
    simpa using h
  have hprev := st315_p260
  have hstep := st315_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p262 : ((8422737406017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT315 (i+1))
      = (∑ i ∈ Finset.range 261, stT315 (i+1)) + stT315 262 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 261
    simpa using h
  have hprev := st315_p261
  have hstep := st315_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p263 : ((3295784548353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT315 (i+1))
      = (∑ i ∈ Finset.range 262, stT315 (i+1)) + stT315 263 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 262
    simpa using h
  have hprev := st315_p262
  have hstep := st315_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p264 : ((15884265375791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT315 (i+1))
      = (∑ i ∈ Finset.range 263, stT315 (i+1)) + stT315 264 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 263
    simpa using h
  have hprev := st315_p263
  have hstep := st315_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p265 : ((15811419698927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT315 (i+1))
      = (∑ i ∈ Finset.range 264, stT315 (i+1)) + stT315 265 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 264
    simpa using h
  have hprev := st315_p264
  have hstep := st315_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p266 : ((408713037303/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT315 (i+1))
      = (∑ i ∈ Finset.range 265, stT315 (i+1)) + stT315 266 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 265
    simpa using h
  have hprev := st315_p265
  have hstep := st315_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p267 : ((67299056617/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT315 (i+1))
      = (∑ i ∈ Finset.range 266, stT315 (i+1)) + stT315 267 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 266
    simpa using h
  have hprev := st315_p266
  have hstep := st315_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p268 : ((8326294352213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT315 (i+1))
      = (∑ i ∈ Finset.range 267, stT315 (i+1)) + stT315 268 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 267
    simpa using h
  have hprev := st315_p267
  have hstep := st315_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p269 : ((16046635353319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT315 (i+1))
      = (∑ i ∈ Finset.range 268, stT315 (i+1)) + stT315 269 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 268
    simpa using h
  have hprev := st315_p268
  have hstep := st315_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p270 : ((1574739059839/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT315 (i+1))
      = (∑ i ∈ Finset.range 269, stT315 (i+1)) + stT315 270 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 269
    simpa using h
  have hprev := st315_p269
  have hstep := st315_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p271 : ((8057618700779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT315 (i+1))
      = (∑ i ∈ Finset.range 270, stT315 (i+1)) + stT315 271 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 270
    simpa using h
  have hprev := st315_p270
  have hstep := st315_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p272 : ((417603421981/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT315 (i+1))
      = (∑ i ∈ Finset.range 271, stT315 (i+1)) + stT315 272 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 271
    simpa using h
  have hprev := st315_p271
  have hstep := st315_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p273 : ((16809357408871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT315 (i+1))
      = (∑ i ∈ Finset.range 272, stT315 (i+1)) + stT315 273 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 272
    simpa using h
  have hprev := st315_p272
  have hstep := st315_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p274 : ((16308611936631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT315 (i+1))
      = (∑ i ∈ Finset.range 273, stT315 (i+1)) + stT315 274 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 273
    simpa using h
  have hprev := st315_p273
  have hstep := st315_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p275 : ((15795610622163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT315 (i+1))
      = (∑ i ∈ Finset.range 274, stT315 (i+1)) + stT315 275 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 274
    simpa using h
  have hprev := st315_p274
  have hstep := st315_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p276 : ((495979108893/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT315 (i+1))
      = (∑ i ∈ Finset.range 275, stT315 (i+1)) + stT315 276 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 275
    simpa using h
  have hprev := st315_p275
  have hstep := st315_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p277 : ((16444326508431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT315 (i+1))
      = (∑ i ∈ Finset.range 276, stT315 (i+1)) + stT315 277 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 276
    simpa using h
  have hprev := st315_p276
  have hstep := st315_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p278 : ((16849105132191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT315 (i+1))
      = (∑ i ∈ Finset.range 277, stT315 (i+1)) + stT315 278 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 277
    simpa using h
  have hprev := st315_p277
  have hstep := st315_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p279 : ((2077674037377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT315 (i+1))
      = (∑ i ∈ Finset.range 278, stT315 (i+1)) + stT315 279 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 278
    simpa using h
  have hprev := st315_p278
  have hstep := st315_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p280 : ((16024578700731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT315 (i+1))
      = (∑ i ∈ Finset.range 279, stT315 (i+1)) + stT315 280 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 279
    simpa using h
  have hprev := st315_p279
  have hstep := st315_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p281 : ((15737729422881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT315 (i+1))
      = (∑ i ∈ Finset.range 280, stT315 (i+1)) + stT315 281 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 280
    simpa using h
  have hprev := st315_p280
  have hstep := st315_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p282 : ((16082457971799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT315 (i+1))
      = (∑ i ∈ Finset.range 281, stT315 (i+1)) + stT315 282 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 281
    simpa using h
  have hprev := st315_p281
  have hstep := st315_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p283 : ((16669078517661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT315 (i+1))
      = (∑ i ∈ Finset.range 282, stT315 (i+1)) + stT315 283 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 282
    simpa using h
  have hprev := st315_p282
  have hstep := st315_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p284 : ((16843201692481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT315 (i+1))
      = (∑ i ∈ Finset.range 283, stT315 (i+1)) + stT315 284 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 283
    simpa using h
  have hprev := st315_p283
  have hstep := st315_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p285 : ((16414410913663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT315 (i+1))
      = (∑ i ∈ Finset.range 284, stT315 (i+1)) + stT315 285 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 284
    simpa using h
  have hprev := st315_p284
  have hstep := st315_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p286 : ((7928624597989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT315 (i+1))
      = (∑ i ∈ Finset.range 285, stT315 (i+1)) + stT315 286 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 285
    simpa using h
  have hprev := st315_p285
  have hstep := st315_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p287 : ((7890481755713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT315 (i+1))
      = (∑ i ∈ Finset.range 286, stT315 (i+1)) + stT315 287 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 286
    simpa using h
  have hprev := st315_p286
  have hstep := st315_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p288 : ((16265681728151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT315 (i+1))
      = (∑ i ∈ Finset.range 287, stT315 (i+1)) + stT315 288 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 287
    simpa using h
  have hprev := st315_p287
  have hstep := st315_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p289 : ((4196354337659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT315 (i+1))
      = (∑ i ∈ Finset.range 288, stT315 (i+1)) + stT315 289 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 288
    simpa using h
  have hprev := st315_p288
  have hstep := st315_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p290 : ((4195679033509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT315 (i+1))
      = (∑ i ∈ Finset.range 289, stT315 (i+1)) + stT315 290 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 289
    simpa using h
  have hprev := st315_p289
  have hstep := st315_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p291 : ((8131613248817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT315 (i+1))
      = (∑ i ∈ Finset.range 290, stT315 (i+1)) + stT315 291 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 290
    simpa using h
  have hprev := st315_p290
  have hstep := st315_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p292 : ((7889868161453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT315 (i+1))
      = (∑ i ∈ Finset.range 291, stT315 (i+1)) + stT315 292 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 291
    simpa using h
  have hprev := st315_p291
  have hstep := st315_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p293 : ((247512288033/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT315 (i+1))
      = (∑ i ∈ Finset.range 292, stT315 (i+1)) + stT315 293 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 292
    simpa using h
  have hprev := st315_p292
  have hstep := st315_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p294 : ((3275905868999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT315 (i+1))
      = (∑ i ∈ Finset.range 293, stT315 (i+1)) + stT315 294 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 293
    simpa using h
  have hprev := st315_p293
  have hstep := st315_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p295 : ((16833343447339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT315 (i+1))
      = (∑ i ∈ Finset.range 294, stT315 (i+1)) + stT315 295 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 294
    simpa using h
  have hprev := st315_p294
  have hstep := st315_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p296 : ((8366890056417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT315 (i+1))
      = (∑ i ∈ Finset.range 295, stT315 (i+1)) + stT315 296 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 295
    simpa using h
  have hprev := st315_p295
  have hstep := st315_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p297 : ((8092989240129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT315 (i+1))
      = (∑ i ∈ Finset.range 296, stT315 (i+1)) + stT315 297 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 296
    simpa using h
  have hprev := st315_p296
  have hstep := st315_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p298 : ((7875675106659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT315 (i+1))
      = (∑ i ∈ Finset.range 297, stT315 (i+1)) + stT315 298 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 297
    simpa using h
  have hprev := st315_p297
  have hstep := st315_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p299 : ((3967529206139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT315 (i+1))
      = (∑ i ∈ Finset.range 298, stT315 (i+1)) + stT315 299 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 298
    simpa using h
  have hprev := st315_p298
  have hstep := st315_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p300 : ((1026219831941/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT315 (i+1))
      = (∑ i ∈ Finset.range 299, stT315 (i+1)) + stT315 300 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 299
    simpa using h
  have hprev := st315_p299
  have hstep := st315_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p301 : ((2105824617487/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT315 (i+1))
      = (∑ i ∈ Finset.range 300, stT315 (i+1)) + stT315 301 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 300
    simpa using h
  have hprev := st315_p300
  have hstep := st315_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p302 : ((4181624854661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT315 (i+1))
      = (∑ i ∈ Finset.range 301, stT315 (i+1)) + stT315 302 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 301
    simpa using h
  have hprev := st315_p301
  have hstep := st315_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p303 : ((8090498593447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT315 (i+1))
      = (∑ i ∈ Finset.range 302, stT315 (i+1)) + stT315 303 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 302
    simpa using h
  have hprev := st315_p302
  have hstep := st315_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p304 : ((7874605232797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT315 (i+1))
      = (∑ i ∈ Finset.range 303, stT315 (i+1)) + stT315 304 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 303
    simpa using h
  have hprev := st315_p303
  have hstep := st315_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p305 : ((3963231428483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT315 (i+1))
      = (∑ i ∈ Finset.range 304, stT315 (i+1)) + stT315 305 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 304
    simpa using h
  have hprev := st315_p304
  have hstep := st315_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p306 : ((16388398857649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT315 (i+1))
      = (∑ i ∈ Finset.range 305, stT315 (i+1)) + stT315 306 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 305
    simpa using h
  have hprev := st315_p305
  have hstep := st315_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p307 : ((16835592636959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT315 (i+1))
      = (∑ i ∈ Finset.range 306, stT315 (i+1)) + stT315 307 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 306
    simpa using h
  have hprev := st315_p306
  have hstep := st315_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p308 : ((4191284266453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT315 (i+1))
      = (∑ i ∈ Finset.range 307, stT315 (i+1)) + stT315 308 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 307
    simpa using h
  have hprev := st315_p307
  have hstep := st315_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p309 : ((16247008784227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT315 (i+1))
      = (∑ i ∈ Finset.range 308, stT315 (i+1)) + stT315 309 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 308
    simpa using h
  have hprev := st315_p308
  have hstep := st315_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p310 : ((15775612819391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT315 (i+1))
      = (∑ i ∈ Finset.range 309, stT315 (i+1)) + stT315 310 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 309
    simpa using h
  have hprev := st315_p309
  have hstep := st315_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p311 : ((15795756597019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT315 (i+1))
      = (∑ i ∈ Finset.range 310, stT315 (i+1)) + stT315 311 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 310
    simpa using h
  have hprev := st315_p310
  have hstep := st315_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p312 : ((16285890004381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT315 (i+1))
      = (∑ i ∈ Finset.range 311, stT315 (i+1)) + stT315 312 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 311
    simpa using h
  have hprev := st315_p311
  have hstep := st315_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p313 : ((2098266493601/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT315 (i+1))
      = (∑ i ∈ Finset.range 312, stT315 (i+1)) + stT315 313 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 312
    simpa using h
  have hprev := st315_p312
  have hstep := st315_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p314 : ((263004334007/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT315 (i+1))
      = (∑ i ∈ Finset.range 313, stT315 (i+1)) + stT315 314 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 313
    simpa using h
  have hprev := st315_p313
  have hstep := st315_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p315 : ((8192035565533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT315 (i+1))
      = (∑ i ∈ Finset.range 314, stT315 (i+1)) + stT315 315 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 314
    simpa using h
  have hprev := st315_p314
  have hstep := st315_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p316 : ((7927525970373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT315 (i+1))
      = (∑ i ∈ Finset.range 315, stT315 (i+1)) + stT315 316 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 315
    simpa using h
  have hprev := st315_p315
  have hstep := st315_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p317 : ((7863945107033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT315 (i+1))
      = (∑ i ∈ Finset.range 316, stT315 (i+1)) + stT315 317 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 316
    simpa using h
  have hprev := st315_p316
  have hstep := st315_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p318 : ((8057860345019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT315 (i+1))
      = (∑ i ∈ Finset.range 317, stT315 (i+1)) + stT315 318 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 317
    simpa using h
  have hprev := st315_p317
  have hstep := st315_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p319 : ((8333150563093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT315 (i+1))
      = (∑ i ∈ Finset.range 318, stT315 (i+1)) + stT315 319 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 318
    simpa using h
  have hprev := st315_p318
  have hstep := st315_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p320 : ((8442695338453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT315 (i+1))
      = (∑ i ∈ Finset.range 319, stT315 (i+1)) + stT315 320 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 319
    simpa using h
  have hprev := st315_p319
  have hstep := st315_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p321 : ((8289720357211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT315 (i+1))
      = (∑ i ∈ Finset.range 320, stT315 (i+1)) + stT315 321 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 320
    simpa using h
  have hprev := st315_p320
  have hstep := st315_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p322 : ((8011069711631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT315 (i+1))
      = (∑ i ∈ Finset.range 321, stT315 (i+1)) + stT315 322 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 321
    simpa using h
  have hprev := st315_p321
  have hstep := st315_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p323 : ((15705603275987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT315 (i+1))
      = (∑ i ∈ Finset.range 322, stT315 (i+1)) + stT315 323 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 322
    simpa using h
  have hprev := st315_p322
  have hstep := st315_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p324 : ((62131919567/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT315 (i+1))
      = (∑ i ∈ Finset.range 323, stT315 (i+1)) + stT315 324 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 323
    simpa using h
  have hprev := st315_p323
  have hstep := st315_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p325 : ((16060187573/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT315 (i+1))
      = (∑ i ∈ Finset.range 324, stT315 (i+1)) + stT315 325 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 324
    simpa using h
  have hprev := st315_p324
  have hstep := st315_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p326 : ((2106992064919/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT315 (i+1))
      = (∑ i ∈ Finset.range 325, stT315 (i+1)) + stT315 326 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 325
    simpa using h
  have hprev := st315_p325
  have hstep := st315_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p327 : ((8392004604109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT315 (i+1))
      = (∑ i ∈ Finset.range 326, stT315 (i+1)) + stT315 327 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 326
    simpa using h
  have hprev := st315_p326
  have hstep := st315_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p328 : ((4073459530443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT315 (i+1))
      = (∑ i ∈ Finset.range 327, stT315 (i+1)) + stT315 328 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 327
    simpa using h
  have hprev := st315_p327
  have hstep := st315_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p329 : ((790241945161/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT315 (i+1))
      = (∑ i ∈ Finset.range 328, stT315 (i+1)) + stT315 329 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 328
    simpa using h
  have hprev := st315_p328
  have hstep := st315_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p330 : ((1966369564009/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT315 (i+1))
      = (∑ i ∈ Finset.range 329, stT315 (i+1)) + stT315 330 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 329
    simpa using h
  have hprev := st315_p329
  have hstep := st315_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p331 : ((8066120478049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT315 (i+1))
      = (∑ i ∈ Finset.range 330, stT315 (i+1)) + stT315 331 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 330
    simpa using h
  have hprev := st315_p330
  have hstep := st315_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p332 : ((8335141555829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT315 (i+1))
      = (∑ i ∈ Finset.range 331, stT315 (i+1)) + stT315 332 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 331
    simpa using h
  have hprev := st315_p331
  have hstep := st315_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p333 : ((8448195322613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT315 (i+1))
      = (∑ i ∈ Finset.range 332, stT315 (i+1)) + stT315 333 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 332
    simpa using h
  have hprev := st315_p332
  have hstep := st315_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p334 : ((332497627337/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT315 (i+1))
      = (∑ i ∈ Finset.range 333, stT315 (i+1)) + stT315 334 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 333
    simpa using h
  have hprev := st315_p333
  have hstep := st315_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p335 : ((16081768285669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT315 (i+1))
      = (∑ i ∈ Finset.range 334, stT315 (i+1)) + stT315 335 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 334
    simpa using h
  have hprev := st315_p334
  have hstep := st315_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p336 : ((245517245381/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT315 (i+1))
      = (∑ i ∈ Finset.range 335, stT315 (i+1)) + stT315 336 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 335
    simpa using h
  have hprev := st315_p335
  have hstep := st315_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p337 : ((7909097166199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT315 (i+1))
      = (∑ i ∈ Finset.range 336, stT315 (i+1)) + stT315 337 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 336
    simpa using h
  have hprev := st315_p336
  have hstep := st315_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p338 : ((8154753000623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT315 (i+1))
      = (∑ i ∈ Finset.range 337, stT315 (i+1)) + stT315 338 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 337
    simpa using h
  have hprev := st315_p337
  have hstep := st315_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p339 : ((16789341188121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT315 (i+1))
      = (∑ i ∈ Finset.range 338, stT315 (i+1)) + stT315 339 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 338
    simpa using h
  have hprev := st315_p338
  have hstep := st315_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p340 : ((16873333927371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT315 (i+1))
      = (∑ i ∈ Finset.range 339, stT315 (i+1)) + stT315 340 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 339
    simpa using h
  have hprev := st315_p339
  have hstep := st315_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p341 : ((4124124822983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT315 (i+1))
      = (∑ i ∈ Finset.range 340, stT315 (i+1)) + stT315 341 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 340
    simpa using h
  have hprev := st315_p340
  have hstep := st315_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p342 : ((15959667131207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT315 (i+1))
      = (∑ i ∈ Finset.range 341, stT315 (i+1)) + stT315 342 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 341
    simpa using h
  have hprev := st315_p341
  have hstep := st315_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p343 : ((15686658152157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT315 (i+1))
      = (∑ i ∈ Finset.range 342, stT315 (i+1)) + stT315 343 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 342
    simpa using h
  have hprev := st315_p342
  have hstep := st315_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p344 : ((15890113466859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT315 (i+1))
      = (∑ i ∈ Finset.range 343, stT315 (i+1)) + stT315 344 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 343
    simpa using h
  have hprev := st315_p343
  have hstep := st315_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p345 : ((8204513035759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT315 (i+1))
      = (∑ i ∈ Finset.range 344, stT315 (i+1)) + stT315 345 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 344
    simpa using h
  have hprev := st315_p344
  have hstep := st315_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p346 : ((3367886099143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT315 (i+1))
      = (∑ i ∈ Finset.range 345, stT315 (i+1)) + stT315 346 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 345
    simpa using h
  have hprev := st315_p345
  have hstep := st315_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p347 : ((673991006851/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT315 (i+1))
      = (∑ i ∈ Finset.range 346, stT315 (i+1)) + stT315 347 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 346
    simpa using h
  have hprev := st315_p346
  have hstep := st315_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p348 : ((16434145520553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT315 (i+1))
      = (∑ i ∈ Finset.range 347, stT315 (i+1)) + stT315 348 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 347
    simpa using h
  have hprev := st315_p347
  have hstep := st315_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p349 : ((15911729055801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT315 (i+1))
      = (∑ i ∈ Finset.range 348, stT315 (i+1)) + stT315 349 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 348
    simpa using h
  have hprev := st315_p348
  have hstep := st315_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p350 : ((1959938125491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT315 (i+1))
      = (∑ i ∈ Finset.range 349, stT315 (i+1)) + stT315 350 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 349
    simpa using h
  have hprev := st315_p349
  have hstep := st315_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p351 : ((1988916823251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT315 (i+1))
      = (∑ i ∈ Finset.range 350, stT315 (i+1)) + stT315 351 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 350
    simpa using h
  have hprev := st315_p350
  have hstep := st315_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p352 : ((2053852335081/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT315 (i+1))
      = (∑ i ∈ Finset.range 351, stT315 (i+1)) + stT315 352 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 351
    simpa using h
  have hprev := st315_p351
  have hstep := st315_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p353 : ((1684848648749/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT315 (i+1))
      = (∑ i ∈ Finset.range 352, stT315 (i+1)) + stT315 353 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 352
    simpa using h
  have hprev := st315_p352
  have hstep := st315_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p354 : ((1053402883107/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT315 (i+1))
      = (∑ i ∈ Finset.range 353, stT315 (i+1)) + stT315 354 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 353
    simpa using h
  have hprev := st315_p353
  have hstep := st315_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p355 : ((4111565722023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT315 (i+1))
      = (∑ i ∈ Finset.range 354, stT315 (i+1)) + stT315 355 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 354
    simpa using h
  have hprev := st315_p354
  have hstep := st315_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p356 : ((7963002104857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT315 (i+1))
      = (∑ i ∈ Finset.range 355, stT315 (i+1)) + stT315 356 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 355
    simpa using h
  have hprev := st315_p355
  have hstep := st315_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p357 : ((3918671101559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT315 (i+1))
      = (∑ i ∈ Finset.range 356, stT315 (i+1)) + stT315 357 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 356
    simpa using h
  have hprev := st315_p356
  have hstep := st315_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p358 : ((3968455723211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT315 (i+1))
      = (∑ i ∈ Finset.range 357, stT315 (i+1)) + stT315 358 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 357
    simpa using h
  have hprev := st315_p357
  have hstep := st315_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p359 : ((4094269792347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT315 (i+1))
      = (∑ i ∈ Finset.range 358, stT315 (i+1)) + stT315 359 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 358
    simpa using h
  have hprev := st315_p358
  have hstep := st315_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p360 : ((8410297614993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT315 (i+1))
      = (∑ i ∈ Finset.range 359, stT315 (i+1)) + stT315 360 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 359
    simpa using h
  have hprev := st315_p359
  have hstep := st315_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p361 : ((16886935656791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT315 (i+1))
      = (∑ i ∈ Finset.range 360, stT315 (i+1)) + stT315 361 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 360
    simpa using h
  have hprev := st315_p360
  have hstep := st315_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p362 : ((826529342019/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT315 (i+1))
      = (∑ i ∈ Finset.range 361, stT315 (i+1)) + stT315 362 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 361
    simpa using h
  have hprev := st315_p361
  have hstep := st315_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p363 : ((4001539225727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT315 (i+1))
      = (∑ i ∈ Finset.range 362, stT315 (i+1)) + stT315 363 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 362
    simpa using h
  have hprev := st315_p362
  have hstep := st315_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p364 : ((15684260245031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT315 (i+1))
      = (∑ i ∈ Finset.range 363, stT315 (i+1)) + stT315 364 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 363
    simpa using h
  have hprev := st315_p363
  have hstep := st315_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p365 : ((49342976521/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT315 (i+1))
      = (∑ i ∈ Finset.range 364, stT315 (i+1)) + stT315 365 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 364
    simpa using h
  have hprev := st315_p364
  have hstep := st315_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p366 : ((1015432971209/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT315 (i+1))
      = (∑ i ∈ Finset.range 365, stT315 (i+1)) + stT315 366 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 365
    simpa using h
  have hprev := st315_p365
  have hstep := st315_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p367 : ((16736583383109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT315 (i+1))
      = (∑ i ∈ Finset.range 366, stT315 (i+1)) + stT315 367 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 366
    simpa using h
  have hprev := st315_p366
  have hstep := st315_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p368 : ((16920212632041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT315 (i+1))
      = (∑ i ∈ Finset.range 367, stT315 (i+1)) + stT315 368 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 367
    simpa using h
  have hprev := st315_p367
  have hstep := st315_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p369 : ((16672995957581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT315 (i+1))
      = (∑ i ∈ Finset.range 368, stT315 (i+1)) + stT315 369 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 368
    simpa using h
  have hprev := st315_p368
  have hstep := st315_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p370 : ((16166005084241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT315 (i+1))
      = (∑ i ∈ Finset.range 369, stT315 (i+1)) + stT315 370 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 369
    simpa using h
  have hprev := st315_p369
  have hstep := st315_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p371 : ((1968176963227/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT315 (i+1))
      = (∑ i ∈ Finset.range 370, stT315 (i+1)) + stT315 371 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 370
    simpa using h
  have hprev := st315_p370
  have hstep := st315_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p372 : ((3923883930559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT315 (i+1))
      = (∑ i ∈ Finset.range 371, stT315 (i+1)) + stT315 372 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 371
    simpa using h
  have hprev := st315_p371
  have hstep := st315_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p373 : ((1003012132931/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT315 (i+1))
      = (∑ i ∈ Finset.range 372, stT315 (i+1)) + stT315 373 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 372
    simpa using h
  have hprev := st315_p372
  have hstep := st315_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p374 : ((16565104800229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT315 (i+1))
      = (∑ i ∈ Finset.range 373, stT315 (i+1)) + stT315 374 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 373
    simpa using h
  have hprev := st315_p373
  have hstep := st315_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p375 : ((16900757686259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT315 (i+1))
      = (∑ i ∈ Finset.range 374, stT315 (i+1)) + stT315 375 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 374
    simpa using h
  have hprev := st315_p374
  have hstep := st315_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p376 : ((16833252147781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT315 (i+1))
      = (∑ i ∈ Finset.range 375, stT315 (i+1)) + stT315 376 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 375
    simpa using h
  have hprev := st315_p375
  have hstep := st315_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p377 : ((3281799937317/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT315 (i+1))
      = (∑ i ∈ Finset.range 376, stT315 (i+1)) + stT315 377 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 376
    simpa using h
  have hprev := st315_p376
  have hstep := st315_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p378 : ((3181663755171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT315 (i+1))
      = (∑ i ∈ Finset.range 377, stT315 (i+1)) + stT315 378 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 377
    simpa using h
  have hprev := st315_p377
  have hstep := st315_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p379 : ((15658816303341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT315 (i+1))
      = (∑ i ∈ Finset.range 378, stT315 (i+1)) + stT315 379 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 378
    simpa using h
  have hprev := st315_p378
  have hstep := st315_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p380 : ((3955391670123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT315 (i+1))
      = (∑ i ∈ Finset.range 379, stT315 (i+1)) + stT315 380 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 379
    simpa using h
  have hprev := st315_p379
  have hstep := st315_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p381 : ((509040753991/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT315 (i+1))
      = (∑ i ∈ Finset.range 380, stT315 (i+1)) + stT315 381 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 380
    simpa using h
  have hprev := st315_p380
  have hstep := st315_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p382 : ((1047460234373/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT315 (i+1))
      = (∑ i ∈ Finset.range 381, stT315 (i+1)) + stT315 382 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 381
    simpa using h
  have hprev := st315_p381
  have hstep := st315_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p383 : ((1058154993989/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT315 (i+1))
      = (∑ i ∈ Finset.range 382, stT315 (i+1)) + stT315 383 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 382
    simpa using h
  have hprev := st315_p382
  have hstep := st315_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p384 : ((8347432106007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT315 (i+1))
      = (∑ i ∈ Finset.range 383, stT315 (i+1)) + stT315 384 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 383
    simpa using h
  have hprev := st315_p383
  have hstep := st315_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p385 : ((8101932880639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT315 (i+1))
      = (∑ i ∈ Finset.range 384, stT315 (i+1)) + stT315 385 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 384
    simpa using h
  have hprev := st315_p384
  have hstep := st315_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p386 : ((15768665079707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT315 (i+1))
      = (∑ i ∈ Finset.range 385, stT315 (i+1)) + stT315 386 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 385
    simpa using h
  have hprev := st315_p385
  have hstep := st315_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p387 : ((15662438551919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT315 (i+1))
      = (∑ i ∈ Finset.range 386, stT315 (i+1)) + stT315 387 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 386
    simpa using h
  have hprev := st315_p386
  have hstep := st315_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p388 : ((7975043798369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT315 (i+1))
      = (∑ i ∈ Finset.range 387, stT315 (i+1)) + stT315 388 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 387
    simpa using h
  have hprev := st315_p387
  have hstep := st315_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p389 : ((8225391007609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT315 (i+1))
      = (∑ i ∈ Finset.range 388, stT315 (i+1)) + stT315 389 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 388
    simpa using h
  have hprev := st315_p388
  have hstep := st315_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p390 : ((16853462341457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT315 (i+1))
      = (∑ i ∈ Finset.range 389, stT315 (i+1)) + stT315 390 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 389
    simpa using h
  have hprev := st315_p389
  have hstep := st315_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p391 : ((8455193401469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT315 (i+1))
      = (∑ i ∈ Finset.range 390, stT315 (i+1)) + stT315 391 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 390
    simpa using h
  have hprev := st315_p390
  have hstep := st315_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p392 : ((4147043232697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT315 (i+1))
      = (∑ i ∈ Finset.range 391, stT315 (i+1)) + stT315 392 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 391
    simpa using h
  have hprev := st315_p391
  have hstep := st315_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p393 : ((8042582482853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT315 (i+1))
      = (∑ i ∈ Finset.range 392, stT315 (i+1)) + stT315 393 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 392
    simpa using h
  have hprev := st315_p392
  have hstep := st315_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p394 : ((7853841473333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT315 (i+1))
      = (∑ i ∈ Finset.range 393, stT315 (i+1)) + stT315 394 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 393
    simpa using h
  have hprev := st315_p393
  have hstep := st315_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p395 : ((3920827278039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT315 (i+1))
      = (∑ i ∈ Finset.range 394, stT315 (i+1)) + stT315 395 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 394
    simpa using h
  have hprev := st315_p394
  have hstep := st315_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p396 : ((4006275438759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT315 (i+1))
      = (∑ i ∈ Finset.range 395, stT315 (i+1)) + stT315 396 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 395
    simpa using h
  have hprev := st315_p395
  have hstep := st315_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p397 : ((16526736314421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT315 (i+1))
      = (∑ i ∈ Finset.range 396, stT315 (i+1)) + stT315 397 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 396
    simpa using h
  have hprev := st315_p396
  have hstep := st315_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p398 : ((16888549972939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT315 (i+1))
      = (∑ i ∈ Finset.range 397, stT315 (i+1)) + stT315 398 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 397
    simpa using h
  have hprev := st315_p397
  have hstep := st315_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p399 : ((16896563493321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT315 (i+1))
      = (∑ i ∈ Finset.range 398, stT315 (i+1)) + stT315 399 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 398
    simpa using h
  have hprev := st315_p398
  have hstep := st315_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p400 : ((16547595795387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT315 (i+1))
      = (∑ i ∈ Finset.range 399, stT315 (i+1)) + stT315 400 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 399
    simpa using h
  have hprev := st315_p399
  have hstep := st315_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p401 : ((8024102156727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT315 (i+1))
      = (∑ i ∈ Finset.range 400, stT315 (i+1)) + stT315 401 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 400
    simpa using h
  have hprev := st315_p400
  have hstep := st315_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p402 : ((3922752237521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT315 (i+1))
      = (∑ i ∈ Finset.range 401, stT315 (i+1)) + stT315 402 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 401
    simpa using h
  have hprev := st315_p401
  have hstep := st315_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p403 : ((3920804152159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT315 (i+1))
      = (∑ i ∈ Finset.range 402, stT315 (i+1)) + stT315 403 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 402
    simpa using h
  have hprev := st315_p402
  have hstep := st315_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p404 : ((4006939941017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT315 (i+1))
      = (∑ i ∈ Finset.range 403, stT315 (i+1)) + stT315 404 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 403
    simpa using h
  have hprev := st315_p403
  have hstep := st315_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p405 : ((16524432697979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT315 (i+1))
      = (∑ i ∈ Finset.range 404, stT315 (i+1)) + stT315 405 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 404
    simpa using h
  have hprev := st315_p404
  have hstep := st315_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p406 : ((8443775726247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT315 (i+1))
      = (∑ i ∈ Finset.range 405, stT315 (i+1)) + stT315 406 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 405
    simpa using h
  have hprev := st315_p405
  have hstep := st315_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p407 : ((3382059749853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT315 (i+1))
      = (∑ i ∈ Finset.range 406, stT315 (i+1)) + stT315 407 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 406
    simpa using h
  have hprev := st315_p406
  have hstep := st315_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p408 : ((16581206724023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT315 (i+1))
      = (∑ i ∈ Finset.range 407, stT315 (i+1)) + stT315 408 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 407
    simpa using h
  have hprev := st315_p407
  have hstep := st315_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p409 : ((16087993675283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT315 (i+1))
      = (∑ i ∈ Finset.range 408, stT315 (i+1)) + stT315 409 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 408
    simpa using h
  have hprev := st315_p408
  have hstep := st315_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p410 : ((15709122177343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT315 (i+1))
      = (∑ i ∈ Finset.range 409, stT315 (i+1)) + stT315 410 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 409
    simpa using h
  have hprev := st315_p409
  have hstep := st315_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p411 : ((15656458353119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT315 (i+1))
      = (∑ i ∈ Finset.range 410, stT315 (i+1)) + stT315 411 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 410
    simpa using h
  have hprev := st315_p410
  have hstep := st315_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p412 : ((15957929307999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT315 (i+1))
      = (∑ i ∈ Finset.range 411, stT315 (i+1)) + stT315 412 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 411
    simpa using h
  have hprev := st315_p411
  have hstep := st315_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p413 : ((8222263491647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT315 (i+1))
      = (∑ i ∈ Finset.range 412, stT315 (i+1)) + stT315 413 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 412
    simpa using h
  have hprev := st315_p412
  have hstep := st315_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p414 : ((2105799942583/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT315 (i+1))
      = (∑ i ∈ Finset.range 413, stT315 (i+1)) + stT315 414 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 413
    simpa using h
  have hprev := st315_p413
  have hstep := st315_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p415 : ((2117839326823/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT315 (i+1))
      = (∑ i ∈ Finset.range 414, stT315 (i+1)) + stT315 415 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 414
    simpa using h
  have hprev := st315_p414
  have hstep := st315_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p416 : ((16682014632609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT315 (i+1))
      = (∑ i ∈ Finset.range 415, stT315 (i+1)) + stT315 416 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 415
    simpa using h
  have hprev := st315_p415
  have hstep := st315_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p417 : ((16207970375737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT315 (i+1))
      = (∑ i ∈ Finset.range 416, stT315 (i+1)) + stT315 417 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 416
    simpa using h
  have hprev := st315_p416
  have hstep := st315_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p418 : ((15778804834741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT315 (i+1))
      = (∑ i ∈ Finset.range 417, stT315 (i+1)) + stT315 418 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 417
    simpa using h
  have hprev := st315_p417
  have hstep := st315_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p419 : ((15626203559497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT315 (i+1))
      = (∑ i ∈ Finset.range 418, stT315 (i+1)) + stT315 419 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 418
    simpa using h
  have hprev := st315_p418
  have hstep := st315_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p420 : ((15831037650247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT315 (i+1))
      = (∑ i ∈ Finset.range 419, stT315 (i+1)) + stT315 420 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 419
    simpa using h
  have hprev := st315_p419
  have hstep := st315_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p421 : ((16282062032497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT315 (i+1))
      = (∑ i ∈ Finset.range 420, stT315 (i+1)) + stT315 421 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 420
    simpa using h
  have hprev := st315_p420
  have hstep := st315_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p422 : ((16737778204801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT315 (i+1))
      = (∑ i ∈ Finset.range 421, stT315 (i+1)) + stT315 422 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 421
    simpa using h
  have hprev := st315_p421
  have hstep := st315_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p423 : ((16956321600049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT315 (i+1))
      = (∑ i ∈ Finset.range 422, stT315 (i+1)) + stT315 423 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 422
    simpa using h
  have hprev := st315_p422
  have hstep := st315_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p424 : ((672928895773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT315 (i+1))
      = (∑ i ∈ Finset.range 423, stT315 (i+1)) + stT315 424 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 423
    simpa using h
  have hprev := st315_p423
  have hstep := st315_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p425 : ((16409951236837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT315 (i+1))
      = (∑ i ∈ Finset.range 424, stT315 (i+1)) + stT315 425 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 424
    simpa using h
  have hprev := st315_p424
  have hstep := st315_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p426 : ((15934035581281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT315 (i+1))
      = (∑ i ∈ Finset.range 425, stT315 (i+1)) + stT315 426 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 425
    simpa using h
  have hprev := st315_p425
  have hstep := st315_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p427 : ((625750704507/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT315 (i+1))
      = (∑ i ∈ Finset.range 426, stT315 (i+1)) + stT315 427 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 426
    simpa using h
  have hprev := st315_p426
  have hstep := st315_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p428 : ((15688934485331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT315 (i+1))
      = (∑ i ∈ Finset.range 427, stT315 (i+1)) + stT315 428 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 427
    simpa using h
  have hprev := st315_p427
  have hstep := st315_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p429 : ((16044779862687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT315 (i+1))
      = (∑ i ∈ Finset.range 428, stT315 (i+1)) + stT315 429 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 428
    simpa using h
  have hprev := st315_p428
  have hstep := st315_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p430 : ((16526955795533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT315 (i+1))
      = (∑ i ∈ Finset.range 429, stT315 (i+1)) + stT315 430 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 429
    simpa using h
  have hprev := st315_p429
  have hstep := st315_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p431 : ((2111005640167/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT315 (i+1))
      = (∑ i ∈ Finset.range 430, stT315 (i+1)) + stT315 431 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 430
    simpa using h
  have hprev := st315_p430
  have hstep := st315_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p432 : ((8472237174043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT315 (i+1))
      = (∑ i ∈ Finset.range 431, stT315 (i+1)) + stT315 432 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 431
    simpa using h
  have hprev := st315_p431
  have hstep := st315_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p433 : ((4167213379139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT315 (i+1))
      = (∑ i ∈ Finset.range 432, stT315 (i+1)) + stT315 433 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 432
    simpa using h
  have hprev := st315_p432
  have hstep := st315_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p434 : ((4050453087259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT315 (i+1))
      = (∑ i ∈ Finset.range 433, stT315 (i+1)) + stT315 434 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 433
    simpa using h
  have hprev := st315_p433
  have hstep := st315_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p435 : ((157790574331/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT315 (i+1))
      = (∑ i ∈ Finset.range 434, stT315 (i+1)) + stT315 435 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 434
    simpa using h
  have hprev := st315_p434
  have hstep := st315_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p436 : ((1951512424031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT315 (i+1))
      = (∑ i ∈ Finset.range 435, stT315 (i+1)) + stT315 436 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 435
    simpa using h
  have hprev := st315_p435
  have hstep := st315_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p437 : ((3945772770603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT315 (i+1))
      = (∑ i ∈ Finset.range 436, stT315 (i+1)) + stT315 437 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 436
    simpa using h
  have hprev := st315_p436
  have hstep := st315_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p438 : ((32411457497/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT315 (i+1))
      = (∑ i ∈ Finset.range 437, stT315 (i+1)) + stT315 438 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 437
    simpa using h
  have hprev := st315_p437
  have hstep := st315_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p439 : ((4167507844363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT315 (i+1))
      = (∑ i ∈ Finset.range 438, stT315 (i+1)) + stT315 439 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 438
    simpa using h
  have hprev := st315_p438
  have hstep := st315_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p440 : ((8473654307567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT315 (i+1))
      = (∑ i ∈ Finset.range 439, stT315 (i+1)) + stT315 440 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 439
    simpa using h
  have hprev := st315_p439
  have hstep := st315_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p441 : ((16902452851507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT315 (i+1))
      = (∑ i ∈ Finset.range 440, stT315 (i+1)) + stT315 441 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 440
    simpa using h
  have hprev := st315_p440
  have hstep := st315_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p442 : ((16558648256343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT315 (i+1))
      = (∑ i ∈ Finset.range 441, stT315 (i+1)) + stT315 442 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 441
    simpa using h
  have hprev := st315_p441
  have hstep := st315_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p443 : ((251314197197/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT315 (i+1))
      = (∑ i ∈ Finset.range 442, stT315 (i+1)) + stT315 443 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 442
    simpa using h
  have hprev := st315_p442
  have hstep := st315_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p444 : ((25134191873/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT315 (i+1))
      = (∑ i ∈ Finset.range 443, stT315 (i+1)) + stT315 444 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 443
    simpa using h
  have hprev := st315_p443
  have hstep := st315_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p445 : ((15613206489733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT315 (i+1))
      = (∑ i ∈ Finset.range 444, stT315 (i+1)) + stT315 445 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 444
    simpa using h
  have hprev := st315_p444
  have hstep := st315_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p446 : ((24752855567/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT315 (i+1))
      = (∑ i ∈ Finset.range 445, stT315 (i+1)) + stT315 446 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 445
    simpa using h
  have hprev := st315_p445
  have hstep := st315_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p447 : ((3256844077471/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT315 (i+1))
      = (∑ i ∈ Finset.range 446, stT315 (i+1)) + stT315 447 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 446
    simpa using h
  have hprev := st315_p446
  have hstep := st315_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p448 : ((418229309111/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT315 (i+1))
      = (∑ i ∈ Finset.range 447, stT315 (i+1)) + stT315 448 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 447
    simpa using h
  have hprev := st315_p447
  have hstep := st315_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p449 : ((16966020787457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT315 (i+1))
      = (∑ i ∈ Finset.range 448, stT315 (i+1)) + stT315 449 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 448
    simpa using h
  have hprev := st315_p448
  have hstep := st315_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p450 : ((16883943520097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT315 (i+1))
      = (∑ i ∈ Finset.range 449, stT315 (i+1)) + stT315 450 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 449
    simpa using h
  have hprev := st315_p449
  have hstep := st315_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p451 : ((3304546835167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT315 (i+1))
      = (∑ i ∈ Finset.range 450, stT315 (i+1)) + stT315 451 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 450
    simpa using h
  have hprev := st315_p450
  have hstep := st315_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p452 : ((1003270413131/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT315 (i+1))
      = (∑ i ∈ Finset.range 451, stT315 (i+1)) + stT315 452 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 451
    simpa using h
  have hprev := st315_p451
  have hstep := st315_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p453 : ((3923016421711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT315 (i+1))
      = (∑ i ∈ Finset.range 452, stT315 (i+1)) + stT315 453 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 452
    simpa using h
  have hprev := st315_p452
  have hstep := st315_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p454 : ((390210674687/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT315 (i+1))
      = (∑ i ∈ Finset.range 453, stT315 (i+1)) + stT315 454 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 453
    simpa using h
  have hprev := st315_p453
  have hstep := st315_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p455 : ((15838887351803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT315 (i+1))
      = (∑ i ∈ Finset.range 454, stT315 (i+1)) + stT315 455 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 454
    simpa using h
  have hprev := st315_p454
  have hstep := st315_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p456 : ((3255249358407/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT315 (i+1))
      = (∑ i ∈ Finset.range 455, stT315 (i+1)) + stT315 456 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 455
    simpa using h
  have hprev := st315_p455
  have hstep := st315_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p457 : ((668780941603/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT315 (i+1))
      = (∑ i ∈ Finset.range 456, stT315 (i+1)) + stT315 457 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 456
    simpa using h
  have hprev := st315_p456
  have hstep := st315_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p458 : ((4241671252589/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT315 (i+1))
      = (∑ i ∈ Finset.range 457, stT315 (i+1)) + stT315 458 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 457
    simpa using h
  have hprev := st315_p457
  have hstep := st315_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p459 : ((16906330479251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT315 (i+1))
      = (∑ i ∈ Finset.range 458, stT315 (i+1)) + stT315 459 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 458
    simpa using h
  have hprev := st315_p458
  have hstep := st315_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p460 : ((16566957043129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT315 (i+1))
      = (∑ i ∈ Finset.range 459, stT315 (i+1)) + stT315 460 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 459
    simpa using h
  have hprev := st315_p459
  have hstep := st315_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p461 : ((8051179520489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT315 (i+1))
      = (∑ i ∈ Finset.range 460, stT315 (i+1)) + stT315 461 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 460
    simpa using h
  have hprev := st315_p460
  have hstep := st315_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p462 : ((15721209178471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT315 (i+1))
      = (∑ i ∈ Finset.range 461, stT315 (i+1)) + stT315 462 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 461
    simpa using h
  have hprev := st315_p461
  have hstep := st315_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p463 : ((15593249990571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT315 (i+1))
      = (∑ i ∈ Finset.range 462, stT315 (i+1)) + stT315 463 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 462
    simpa using h
  have hprev := st315_p462
  have hstep := st315_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p464 : ((15774319523139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT315 (i+1))
      = (∑ i ∈ Finset.range 463, stT315 (i+1)) + stT315 464 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 463
    simpa using h
  have hprev := st315_p463
  have hstep := st315_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p465 : ((16183039183081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT315 (i+1))
      = (∑ i ∈ Finset.range 464, stT315 (i+1)) + stT315 465 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 464
    simpa using h
  have hprev := st315_p464
  have hstep := st315_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p466 : ((16638343938269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT315 (i+1))
      = (∑ i ∈ Finset.range 465, stT315 (i+1)) + stT315 466 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 465
    simpa using h
  have hprev := st315_p465
  have hstep := st315_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p467 : ((16940187222029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT315 (i+1))
      = (∑ i ∈ Finset.range 466, stT315 (i+1)) + stT315 467 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 466
    simpa using h
  have hprev := st315_p466
  have hstep := st315_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p468 : ((16957216512029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT315 (i+1))
      = (∑ i ∈ Finset.range 467, stT315 (i+1)) + stT315 468 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 467
    simpa using h
  have hprev := st315_p467
  have hstep := st315_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p469 : ((16683110036859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT315 (i+1))
      = (∑ i ∈ Finset.range 468, stT315 (i+1)) + stT315 469 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 468
    simpa using h
  have hprev := st315_p468
  have hstep := st315_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p470 : ((3247566856803/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT315 (i+1))
      = (∑ i ∈ Finset.range 469, stT315 (i+1)) + stT315 470 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 469
    simpa using h
  have hprev := st315_p469
  have hstep := st315_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p471 : ((15814295435679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT315 (i+1))
      = (∑ i ∈ Finset.range 470, stT315 (i+1)) + stT315 471 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 470
    simpa using h
  have hprev := st315_p470
  have hstep := st315_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p472 : ((15594517121439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT315 (i+1))
      = (∑ i ∈ Finset.range 471, stT315 (i+1)) + stT315 472 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 471
    simpa using h
  have hprev := st315_p471
  have hstep := st315_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p473 : ((15671805823039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT315 (i+1))
      = (∑ i ∈ Finset.range 472, stT315 (i+1)) + stT315 473 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 472
    simpa using h
  have hprev := st315_p472
  have hstep := st315_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p474 : ((16012025036689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT315 (i+1))
      = (∑ i ∈ Finset.range 473, stT315 (i+1)) + stT315 474 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 473
    simpa using h
  have hprev := st315_p473
  have hstep := st315_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p475 : ((16469599757411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT315 (i+1))
      = (∑ i ∈ Finset.range 474, stT315 (i+1)) + stT315 475 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 474
    simpa using h
  have hprev := st315_p474
  have hstep := st315_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p476 : ((8425234492051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT315 (i+1))
      = (∑ i ∈ Finset.range 475, stT315 (i+1)) + stT315 476 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 475
    simpa using h
  have hprev := st315_p475
  have hstep := st315_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p477 : ((8497215691397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT315 (i+1))
      = (∑ i ∈ Finset.range 476, stT315 (i+1)) + stT315 477 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 476
    simpa using h
  have hprev := st315_p476
  have hstep := st315_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p478 : ((1052622383709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT315 (i+1))
      = (∑ i ∈ Finset.range 477, stT315 (i+1)) + stT315 478 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 477
    simpa using h
  have hprev := st315_p477
  have hstep := st315_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p479 : ((514309955541/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT315 (i+1))
      = (∑ i ∈ Finset.range 478, stT315 (i+1)) + stT315 479 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 478
    simpa using h
  have hprev := st315_p478
  have hstep := st315_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p480 : ((800152704323/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT315 (i+1))
      = (∑ i ∈ Finset.range 479, stT315 (i+1)) + stT315 480 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 479
    simpa using h
  have hprev := st315_p479
  have hstep := st315_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p481 : ((7833110096543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT315 (i+1))
      = (∑ i ∈ Finset.range 480, stT315 (i+1)) + stT315 481 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 480
    simpa using h
  have hprev := st315_p480
  have hstep := st315_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p482 : ((7793027608031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT315 (i+1))
      = (∑ i ∈ Finset.range 481, stT315 (i+1)) + stT315 482 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 481
    simpa using h
  have hprev := st315_p481
  have hstep := st315_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p483 : ((15794518063237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT315 (i+1))
      = (∑ i ∈ Finset.range 482, stT315 (i+1)) + stT315 483 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 482
    simpa using h
  have hprev := st315_p482
  have hstep := st315_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p484 : ((8102544508151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT315 (i+1))
      = (∑ i ∈ Finset.range 483, stT315 (i+1)) + stT315 484 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 483
    simpa using h
  have hprev := st315_p483
  have hstep := st315_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p485 : ((8324719127153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT315 (i+1))
      = (∑ i ∈ Finset.range 484, stT315 (i+1)) + stT315 485 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 484
    simpa using h
  have hprev := st315_p484
  have hstep := st315_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p486 : ((16946818417789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT315 (i+1))
      = (∑ i ∈ Finset.range 485, stT315 (i+1)) + stT315 486 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 485
    simpa using h
  have hprev := st315_p485
  have hstep := st315_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p487 : ((8488693495713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT315 (i+1))
      = (∑ i ∈ Finset.range 486, stT315 (i+1)) + stT315 487 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 486
    simpa using h
  have hprev := st315_p486
  have hstep := st315_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p488 : ((1045613269971/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT315 (i+1))
      = (∑ i ∈ Finset.range 487, stT315 (i+1)) + stT315 488 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 487
    simpa using h
  have hprev := st315_p487
  have hstep := st315_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p489 : ((2038071545073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT315 (i+1))
      = (∑ i ∈ Finset.range 488, stT315 (i+1)) + stT315 489 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 488
    simpa using h
  have hprev := st315_p488
  have hstep := st315_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p490 : ((3968107250431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT315 (i+1))
      = (∑ i ∈ Finset.range 489, stT315 (i+1)) + stT315 490 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 489
    simpa using h
  have hprev := st315_p489
  have hstep := st315_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p491 : ((7802797327407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT315 (i+1))
      = (∑ i ∈ Finset.range 490, stT315 (i+1)) + stT315 491 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 490
    simpa using h
  have hprev := st315_p490
  have hstep := st315_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p492 : ((7804667386839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT315 (i+1))
      = (∑ i ∈ Finset.range 491, stT315 (i+1)) + stT315 492 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 491
    simpa using h
  have hprev := st315_p491
  have hstep := st315_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p493 : ((3176224846449/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT315 (i+1))
      = (∑ i ∈ Finset.range 492, stT315 (i+1)) + stT315 493 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 492
    simpa using h
  have hprev := st315_p492
  have hstep := st315_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p494 : ((3262582683189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT315 (i+1))
      = (∑ i ∈ Finset.range 493, stT315 (i+1)) + stT315 494 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 493
    simpa using h
  have hprev := st315_p493
  have hstep := st315_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p495 : ((16734700400733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT315 (i+1))
      = (∑ i ∈ Finset.range 494, stT315 (i+1)) + stT315 495 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 494
    simpa using h
  have hprev := st315_p494
  have hstep := st315_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p496 : ((424542325569/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT315 (i+1))
      = (∑ i ∈ Finset.range 495, stT315 (i+1)) + stT315 496 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 495
    simpa using h
  have hprev := st315_p495
  have hstep := st315_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p497 : ((105989966953/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT315 (i+1))
      = (∑ i ∈ Finset.range 496, stT315 (i+1)) + stT315 497 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 496
    simpa using h
  have hprev := st315_p496
  have hstep := st315_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p498 : ((16674837689567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT315 (i+1))
      = (∑ i ∈ Finset.range 497, stT315 (i+1)) + stT315 498 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 497
    simpa using h
  have hprev := st315_p497
  have hstep := st315_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p499 : ((16241482071763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT315 (i+1))
      = (∑ i ∈ Finset.range 498, stT315 (i+1)) + stT315 499 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 498
    simpa using h
  have hprev := st315_p498
  have hstep := st315_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_p500 : ((15825586468183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT315 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT315 (i+1))
      = (∑ i ∈ Finset.range 499, stT315 (i+1)) + stT315 500 := by
    have h := Finset.sum_range_succ (fun i => stT315 (i+1)) 499
    simpa using h
  have hprev := st315_p499
  have hstep := st315_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st315_s500 :
    |Real.sin (((315 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((393/31250 : ℚ) : ℝ))
      - ((-22993/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -345607/500000) (δ := 7921/500000000) (ψ := 393/31250) 315 312
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 315`** (evaluated boundary). -/
theorem station_315_sign : 0 < hardyG ((((315:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 315 500 (by norm_num) (by norm_num)
    ((393/31250 : ℚ) : ℝ)
  have hchain := st315_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT315 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((315 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((393/31250 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st315_c500
  have hsinb := abs_le.mp st315_s500
  have hbdy_lo : ((10403793738273/396901000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((315 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((393/31250 : ℚ) : ℝ))) / 2
          - ((((315:ℕ)):ℝ))
            * Real.sin (((315 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((393/31250 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((315:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((315:ℝ) * Real.log (500:ℝ) - ((393/31250 : ℚ) : ℝ))) / 2
        - ((315:ℝ)) * Real.sin ((315:ℝ) * Real.log (500:ℝ) - ((393/31250 : ℚ) : ℝ))
        ≥ ((23263621/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((315:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((23263621/200000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((23263621/200000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((23263621/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((315:ℕ)):ℝ))+1) * (((((315:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((5784294721303/7500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((15825586468183/10000000000000 : ℚ) : ℝ) + ((10403793738273/396901000000000 : ℚ) : ℝ)
      - ((5784294721303/7500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((393/31250 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((315:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((393/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((315:ℕ)):ℝ)))).re
      - Real.sin ((393/31250 : ℚ) : ℝ)
        * (riemannZeta (line ((((315:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((315:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((315:ℕ)):ℝ))
      = (((((315:ℕ)):ℝ)) * (Real.log ((((315:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((315:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_315
  have hl30 : ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30:ℝ)
      ∧ Real.log (30:ℝ) ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := log_br_30
    norm_num at h ⊢
    exact h
  have hl2 : ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2:ℝ)
      ∧ Real.log (2:ℝ) ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := log_br_2
    norm_num at h ⊢
    exact h
  have hlπ := log_pi_enclosure
  have hπ6l := Real.pi_gt_d6
  have hπ6u := Real.pi_lt_d6
  have hθb := abs_le.mp hθ30
  have hincb := abs_le.mp hinc
  have hθwin : |(((393/31250 : ℚ) : ℝ) + ((73:ℤ)) * (2*Real.pi)) - theta ((((315:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((315:ℕ)):ℝ)))
    (φ := ((393/31250 : ℚ) : ℝ) + ((73:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((393/31250 : ℚ)) : ℝ) 73).1,
    (cos_sin_shift (((393/31250 : ℚ)) : ℝ) 73).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_315_sign
end AxiomAudit
